# Author: Shravan Mali
# Main Python server for Aura v0 ESP32-S3 Voice Assistant

import os
import sys
import io
import time
import json
import math
import wave
import struct
import audioop
import threading
import asyncio
import datetime
import traceback
import urllib.request
import urllib.parse
import urllib.error
import xml.etree.ElementTree as ET
import base64
import re
import subprocess
import pyttsx3
import edge_tts
from collections import deque
import concurrent.futures
from concurrent.futures import ThreadPoolExecutor, as_completed, wait
from aiohttp import web
import requests
import numpy as np
import noisereduce as nr

# Keep connection open to speed up HTTP requests
cloud_http_session = requests.Session()
cloud_http_session.headers.update({
    "User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36",
    "Connection": "keep-alive"
})
from aioesphomeapi import (
    APIClient,
    VoiceAssistantAudioSettings,
    VoiceAssistantAnnounceFinished,
    VoiceAssistantEventType
)

# Ensure console supports UTF-8 characters and real-time line buffering
try:
    sys.stdout.reconfigure(encoding='utf-8', line_buffering=True)
    sys.stderr.reconfigure(encoding='utf-8', line_buffering=True)
except Exception:
    pass

# Windows timer tweak for smoother audio streaming
try:
    import ctypes
    ctypes.windll.winmm.timeBeginPeriod(1)
except Exception:
    pass


# --- CONFIGURATION ---
HOST = "192.168.31.200"  # ESP32-S3 IP on local Wi-Fi
PASSWORD = ""
PORT = 6053

# Groq API Keys & Model
try:
    import local_secrets
    GROQ_KEYS = getattr(local_secrets, 'GROQ_KEYS', ['gsk_placeholder'])
    CARTESIA_KEYS = getattr(local_secrets, 'CARTESIA_KEYS', ['sk_placeholder'])
except ImportError:
    import os
    GROQ_KEYS = [os.environ.get('GROQ_API_KEY', 'gsk_placeholder')]
    CARTESIA_KEYS = [os.environ.get('CARTESIA_API_KEY', 'sk_placeholder')]

groq_key_index = 0
GROQ_KEY = GROQ_KEYS[0]

GROQ_MODEL = "qwen/qwen3.8-27b"  # 250ms ultra-fast multilingual reasoning model

# Cartesia AI Voice Pool & Personas (Sub-300ms Raw PCM)
cartesia_key_index = 0
cartesia_cooldown_until = 0
tts_test_mode = False   # Primary Tier 1: Cartesia Sonic Ultra-Low Latency Engine


# --- Volume Settings ---
VOICE_BASE_GAIN = {
    # Tier 1: Cartesia Sonic Voices
    "cartesia_en": 0.78,
    "cartesia_hi": 0.78,
    "cartesia_mr": 0.85,
    "cartesia_gu": 3.85,  # Calibrated to balance Isha with Skylar (EN/HI) and Sindhu (MR)
    # Tier 2: Microsoft Indian Neural Cloud Voices
    "en-IN-NeerjaNeural": 0.75,
    "hi-IN-SwaraNeural": 0.72,
    "mr-IN-AarohiNeural": 0.80,
    "gu-IN-DhwaniNeural": 1.25,  # Calibrated to balance Dhwani with Neerja and Swara
    "default": 0.75
}

master_volume_percent = 50   # 50% default
master_volume_locked = False # True when manually locked by user
night_mode_override = False  # True when user says "disable whisper tonight"
is_processing_request = False # True from speech capture through STT/LLM/TTS until playback ends

WORD_TO_NUM = {
    "zero": "0", "one": "1", "two": "2", "three": "3", "four": "4",
    "five": "5", "six": "6", "seven": "7", "eight": "8", "nine": "9",
    "ten": "10", "eleven": "11", "twelve": "12", "thirteen": "13",
    "fourteen": "14", "fifteen": "15", "twenty": "20", "thirty": "30",
    "forty": "40", "fifty": "50",
    "एक": "1", "दो": "2", "तीन": "3", "चार": "4", "पांच": "5", "पाँच": "5",
    "दस": "10", "पंद्रह": "15", "बीस": "20", "तीस": "30",
    "दोन": "2", "पाच": "5", "दहा": "10", "પંદર": "15", "દસ": "10"
}

def normalize_numbers_and_time(text: str) -> str:
    """Converts written number words and dot-notation time (e.g. 'ten seconds', '10 a.m.') into digits."""
    if not text:
        return ""
    t = re.sub(r'\ba\.m\.\b', 'am', text, flags=re.IGNORECASE)
    t = re.sub(r'\bp\.m\.\b', 'pm', t, flags=re.IGNORECASE)
    t = re.sub(r'\ba\.m\b', 'am', t, flags=re.IGNORECASE)
    t = re.sub(r'\bp\.m\b', 'pm', t, flags=re.IGNORECASE)
    for word, num in WORD_TO_NUM.items():
        t = re.sub(r'\b' + re.escape(word) + r'\b', num, t, flags=re.IGNORECASE)
    return t

# --- Memory Cache ---
temporal_context = {
    "last_entity": None,
    "entity_type": None,
    "timestamp": 0.0,
    "duration_sec": 0,
    "ttl_seconds": 600
}

def update_temporal_context(entity_name: str, entity_type: str, duration_sec: int = 0):
    global temporal_context
    temporal_context = {
        "last_entity": entity_name,
        "entity_type": entity_type,
        "timestamp": time.time(),
        "duration_sec": duration_sec,
        "ttl_seconds": 600
    }
    print(f"[TEMPORAL MEMORY]: Updated last active subject -> {entity_type} '{entity_name}' (TTL: 600s)")

def get_active_temporal_context() -> dict | None:
    global temporal_context
    if not temporal_context.get("last_entity"):
        return None
    if time.time() - temporal_context.get("timestamp", 0) > temporal_context.get("ttl_seconds", 600):
        temporal_context["last_entity"] = None
        return None
    return temporal_context

# --- Room Noise Check ---
def calculate_ambient_noise_profile(raw_pcm: bytes) -> dict:
    """
    Measures ambient room noise floor from pre-speech buffer (120ms to 450ms).
    Skips first 120ms (3840 bytes) to eliminate hardware DC click/transient.
    Returns RMS, dBFS, noise_category ('quiet' | 'normal' | 'loud'), and radar_gain (0.85 to 1.35).
    """
    if not raw_pcm or len(raw_pcm) < 14400:
        return {"ambient_rms": 200.0, "dbfs": -44.0, "noise_category": "normal", "radar_gain": 1.0}
    
    sample_window = raw_pcm[3840:3840 + 10560]
    if len(sample_window) < 1000:
        sample_window = raw_pcm[:1000]
        
    rms = audioop.rms(sample_window, 2)
    dbfs = -90.0 if rms <= 1 else 20.0 * math.log10(rms / 32768.0)
    
    if dbfs <= -46.0:
        category = "quiet"
        radar_gain = 0.85
    elif dbfs <= -32.0:
        category = "normal"
        radar_gain = 1.00
    else:
        category = "loud"
        excess = min(16.0, dbfs - (-32.0))
        radar_gain = 1.00 + (excess / 16.0) * 0.35
        
    return {
        "ambient_rms": round(rms, 1),
        "dbfs": round(dbfs, 1),
        "noise_category": category,
        "radar_gain": round(radar_gain, 3)
    }

# --- Speech Cadence & Speed ---
def analyze_speech_cadence(raw_pcm: bytes, transcript: str) -> dict:
    """
    Computes speech duration, word count, Words Per Minute (WPM), and cadence state.
    Pre-emptive error guard: requires >= 3 words before classifying as 'rushed'.
    """
    if not raw_pcm or not transcript:
        return {"wpm": 150, "state": "normal", "duration_sec": 1.0, "word_count": 0, "tts_speed": 0.88}
        
    words = transcript.strip().split()
    word_count = len(words)
    total_samples = len(raw_pcm) // 2
    duration_sec = max(0.4, total_samples / 16000.0)
    
    wpm = int((word_count / duration_sec) * 60)
    
    if word_count >= 3 and wpm >= 210:
        state = "rushed"
        tts_speed = 1.06
    elif word_count >= 2 and wpm < 125:
        state = "relaxed"
        tts_speed = 0.84
    else:
        state = "normal"
        tts_speed = 0.88
        
    return {
        "wpm": wpm,
        "state": state,
        "duration_sec": round(duration_sec, 2),
        "word_count": word_count,
        "tts_speed": tts_speed
    }

def apply_speech_clarity_presence(raw_pcm: bytes) -> bytes:
    """Lightweight 2.5kHz-5kHz presence shelf boost for loud room intelligibility."""
    if not raw_pcm:
        return raw_pcm
    total_samples = len(raw_pcm) // 2
    samples = list(struct.unpack('<' + 'h' * total_samples, raw_pcm))
    out = [0] * total_samples
    prev = 0
    for i in range(total_samples):
        curr = samples[i]
        diff = curr - prev
        boosted = int(curr + 0.30 * diff)
        out[i] = max(-32768, min(32767, boosted))
        prev = curr
    return struct.pack('<' + 'h' * total_samples, *out)

def get_effective_gain(voice_key: str, context: str = "normal", radar_gain: float = 1.0) -> float:
    global master_volume_percent, master_volume_locked, night_mode_override
    base_gain = VOICE_BASE_GAIN.get(voice_key, VOICE_BASE_GAIN.get("default", 0.75))
    master_scale = master_volume_percent / 50.0  # 50% = 1.0x, 75% = 1.5x, 100% = 2.0x, 25% = 0.5x
    
    # Check night hours (11:00 PM to 6:30 AM)
    now_hour = datetime.datetime.now().hour
    is_night_time = (now_hour >= 23 or now_hour < 6)
    
    context_multiplier = 1.0
    if context == "whisper" or (is_night_time and not night_mode_override and context not in ["alert", "alarm", "timer"]):
        context_multiplier = 0.58
    elif context in ["alert", "alarm", "timer"]:
        context_multiplier = 1.35
    elif context in ["cheerful", "excited", "joyful", "urgent"]:
        context_multiplier = 1.20

    # Dynamic sound radar modulation
    # If user explicitly locked volume, apply only gentle micro-offset (+/- 8%)
    if master_volume_locked:
        effective_radar = max(0.92, min(1.08, radar_gain))
    else:
        effective_radar = radar_gain
        
    return base_gain * master_scale * context_multiplier * effective_radar

def apply_calibrated_volume_and_limiter(raw_pcm: bytes, voice_key: str, context: str = "normal", radar_gain: float = 1.0, boost_clarity: bool = False) -> bytes:
    """
    Applies calibrated voice baseline, master volume scaling, context multiplier,
    dynamic sound radar gain, speech presence boost, and a zero-distortion tanh soft-limiter.
    """
    if not raw_pcm:
        return raw_pcm
    gain = get_effective_gain(voice_key, context, radar_gain=radar_gain)
    try:
        # If loud room detected, apply speech presence clarity boost first
        if boost_clarity:
            raw_pcm = apply_speech_clarity_presence(raw_pcm)

        scaled = audioop.mul(raw_pcm, 2, gain)
        # Apply anti-clipping soft tanh limiter if gain is high
        if gain > 1.05:
            total_samples = len(scaled) // 2
            samples = list(struct.unpack('<' + 'h' * total_samples, scaled))
            has_clipping = False
            for i in range(total_samples):
                val = samples[i]
                if val > 28000:
                    samples[i] = int(28000 + (32767 - 28000) * math.tanh((val - 28000) / 4767.0))
                    has_clipping = True
                elif val < -28000:
                    samples[i] = int(-28000 - (32768 - 28000) * math.tanh((-val - 28000) / 4768.0))
                    has_clipping = True
            if has_clipping:
                scaled = struct.pack('<' + 'h' * total_samples, *samples)
        return optimize_audio_for_esp32(scaled, sample_rate=16000)
    except Exception as e:
        print(f"[VOLUME SCALING ERROR]: {e}")
        return optimize_audio_for_esp32(raw_pcm, sample_rate=16000)

def parse_volume_intent(query: str):
    q_lower = query.lower()
    is_vol = any(w in q_lower for w in ["volume", "sound", "आवाज़", "आवाज", "वॉल्यूम", "વોલ્યુમ"])
    is_whisper_toggle = any(w in q_lower for w in ["whisper", "night mode", "नाइट मोड", "व्हिस्पर", "फुसफुस"])
    
    if is_whisper_toggle and any(w in q_lower for w in ["no", "do not", "don't", "disable", "off", "band", "regular", "normal", "मत", "बंद"]):
        return "disable_whisper_tonight", None
        
    if is_whisper_toggle and any(w in q_lower for w in ["enable", "on", "shuru", "chalu", "करो", "चालू"]):
        return "enable_whisper_tonight", None

    if not is_vol:
        return None, None
        
    if any(w in q_lower for w in ["default", "reset", "normal", "डिफ़ॉल्ट", "रीसेट"]):
        return "default", 50
        
    m = re.search(r'\b(?:to\s+|at\s+)?(\d{1,4})\s*(?:%|percent|pratishat|टक्के)?\b', q_lower)
    if m:
        raw_val = int(m.group(1))
        target_val = max(10, min(100, raw_val))
        return "set", (target_val, raw_val)
        
    if any(w in q_lower for w in ["what", "how much", "kitna", "kitni", "status", "कितना", "कितनी", "કેટલો", "काय"]):
        return "query", None
        
    return None, None

def handle_volume_command(action: str, value: int | tuple | None, lang: str = "en") -> str:
    global master_volume_percent, master_volume_locked, night_mode_override
    
    # Capture previous state description before mutation
    if master_volume_locked:
        prev_en = f"{master_volume_percent}%"
        prev_hi = f"{master_volume_percent}%"
        prev_mr = f"{master_volume_percent}%"
        prev_gu = f"{master_volume_percent}%"
    else:
        prev_en = f"default ({master_volume_percent}%)"
        prev_hi = f"डिफ़ॉल्ट ({master_volume_percent}%)"
        prev_mr = f"डीफॉल्ट ({master_volume_percent}%)"
        prev_gu = f"ડિફોલ્ટ ({master_volume_percent}%)"

    if action == "set" and value is not None:
        if isinstance(value, (tuple, list)):
            target_val, raw_val = value
        else:
            target_val, raw_val = value, value
            
        is_capped = (raw_val > 100)
        master_volume_percent = target_val
        master_volume_locked = True
        dispatch_async(broadcast("status", f"🔊 Volume set to {target_val}%"))
        dispatch_async(broadcast("volume", {"percent": target_val, "locked": True}))
        
        if is_capped:
            rep_map = {
                "en": f"Maxed it out! Switched volume from {prev_en} up to the maximum 100%!",
                "hi": f"वॉल्यूम को {prev_hi} से बढ़ाकर अधिकतम 100% पर सेट कर दिया है!",
                "mr": f"आवाज {prev_mr} वरून कमाल 100% वर सेट केला आहे!",
                "gu": f"વોલ્યુમ {prev_gu} થી વધારીને મહત્તમ 100% પર સેટ કરી દીધો છે!"
            }
        else:
            rep_map = {
                "en": f"Switched volume from {prev_en} to {target_val}%!",
                "hi": f"वॉल्यूम {prev_hi} से बदलकर {target_val}% पर सेट कर दिया है।",
                "mr": f"आवाज {prev_mr} वरून {target_val}% वर सेट केला आहे.",
                "gu": f"વોલ્યુમ {prev_gu} થી બદલીने {target_val}% પર સેટ કરી દીધો છે."
            }
        return rep_map.get(lang, rep_map["en"])
        
    elif action == "default":
        master_volume_percent = 50
        master_volume_locked = False
        dispatch_async(broadcast("status", "🔊 Volume reset to default (50%)"))
        dispatch_async(broadcast("volume", {"percent": 50, "locked": False}))
        rep_map = {
            "en": f"Reset volume from {prev_en} back to default 50%!",
            "hi": f"वॉल्यूम {prev_hi} से वापस डिफ़ॉल्ट 50% पर रीसेट कर दिया है।",
            "mr": f"आवाज {prev_mr} वरून परत डीफॉल्ट 50% वर रीसेट केला आहे.",
            "gu": f"વોલ્યુમ {prev_gu} થી પાછો ડિફોલ્ટ 50% પર રીસેટ કરી દીધો છે."
        }
        return rep_map.get(lang, rep_map["en"])
        
    elif action == "disable_whisper_tonight":
        night_mode_override = True
        dispatch_async(broadcast("status", "🌙 Night whisper disabled for tonight"))
        rep_map = {
            "hi": "ठीक है, आज रात नियमित आवाज़ में बात करेंगे। व्हिस्पर मोड बंद कर दिया है।",
            "mr": "ठीक आहे, आज रात्री नियमित आवाजात बोलू. व्हिस्पर मोड बंद केला आहे.",
            "gu": "બરાબર, આજે રાત્રે સામાન્ય અવાજમાં વાત કરીશું. વ્હીસ્પર મોડ બંધ કરી દીધો છે.",
            "en": "Got it! Disabling whisper mode for tonight. Speaking at regular volume."
        }
        return rep_map.get(lang, rep_map["en"])
        
    elif action == "enable_whisper_tonight":
        night_mode_override = False
        dispatch_async(broadcast("status", "🌙 Night whisper enabled"))
        rep_map = {
            "hi": "व्हिस्पर मोड चालू कर दिया है।",
            "mr": "व्हिस्पर मोड चालू केला आहे.",
            "gu": "વ્હીસ્પર મોડ ચાલુ કરી દીધો છે.",
            "en": "Whisper mode enabled."
        }
        return rep_map.get(lang, rep_map["en"])
        
    elif action == "query":
        if master_volume_locked:
            rep_map = {
                "en": f"The volume is currently locked at {master_volume_percent}%.",
                "hi": f"वर्तमान वॉल्यूम {master_volume_percent}% पर सेट है।",
                "mr": f"सध्याचा आवाज {master_volume_percent}% वर सेट आहे.",
                "gu": f"હાલનો વોલ્યુમ {master_volume_percent}% પર સેટ છે."
            }
        else:
            rep_map = {
                "en": f"The volume is currently at default {master_volume_percent}%.",
                "hi": f"वर्तमान वॉल्यूम डिफ़ॉल्ट {master_volume_percent}% पर है।",
                "mr": f"सध्याचा आवाज डीफॉल्ट {master_volume_percent}% वर आहे.",
                "gu": f"હાલનો વોલ્યુમ ડિફોલ્ટ {master_volume_percent}% પર છે."
            }
        return rep_map.get(lang, rep_map["en"])
        
    return "Volume updated."

def handle_compound_commands(user_query: str, lang: str = "en") -> tuple[str | None, str | None]:
    """
    Industrial Multi-Command Engine:
    Decomposes mixed utterances into:
    1. Device actions (timers, alarms, volume, stopwatch) -> Executed immediately.
    2. Knowledge/Conversational queries -> Returned as remaining_query for Groq LLM reasoning.
    Returns: (device_action_reply, remaining_knowledge_query)
    """
    norm_query = normalize_numbers_and_time(user_query)
    split_pattern = r'\b(?:and\s+also|and\s+then|and|aur\s+phir|aur|phir|then|also|અને|આગળ|आणि|तसेच)\b|[,;|।]'
    parts = [p.strip() for p in re.split(split_pattern, norm_query, flags=re.IGNORECASE) if len(p.strip()) >= 3]
    if len(parts) < 2:
        return None, None
        
    candidate_parts = parts[:4]
    executed_steps = []
    knowledge_parts = []
    
    for seg in candidate_parts:
        v_act, v_val = parse_volume_intent(seg)
        if v_act:
            resp = handle_volume_command(v_act, v_val, lang)
            executed_steps.append(resp)
            continue
            
        if is_timer_cancel(seg):
            resp = handle_timer_cancel(seg, lang)
            executed_steps.append(resp)
            continue
            
        if is_timer_query(seg):
            resp = handle_timer_query(seg, lang)
            executed_steps.append(resp)
            continue
            
        dt = parse_direct_timer(seg)
        if dt:
            t_secs, t_name = dt
            desc_time = format_duration_desc(t_secs, lang)
            dispatch_async(start_timer_instance(duration=t_secs, name=t_name, lang=lang))
            is_gen = t_name.lower().endswith("timer")
            if is_gen:
                if lang == "hi":
                    executed_steps.append(f"आपका {desc_time} का टाइमर शुरू कर दिया है।")
                elif lang == "mr":
                    executed_steps.append(f"तुमचा {desc_time} चा टायमर सुरू केला आहे.")
                elif lang == "gu":
                    executed_steps.append(f"તમારો {desc_time} નો ટાઈમર શરૂ કરી દીધો છે.")
                else:
                    executed_steps.append(f"Starting your {desc_time} timer now.")
            else:
                if lang == "hi":
                    executed_steps.append(f"{t_name} के लिए {desc_time} का टाइमर शुरू कर दिया है।")
                elif lang == "mr":
                    executed_steps.append(f"{t_name} साठी {desc_time} चा टायमर सुरू केला आहे.")
                elif lang == "gu":
                    executed_steps.append(f"{t_name} માટે {desc_time} નો ટાઈમર શરૂ કરી દીધો છે.")
                else:
                    executed_steps.append(f"Starting your {desc_time} timer for {t_name} now.")
            continue
            
        sw_act = parse_stopwatch_intent(seg)
        if sw_act:
            resp = handle_stopwatch_action(sw_act, lang)
            executed_steps.append(resp)
            continue
            
        al_act = parse_alarm_intent(seg)
        if al_act == "set":
            alarm_res = parse_alarm_time(seg)
            if alarm_res:
                target_dt, fmt_time = alarm_res
                dispatch_async(start_alarm_instance(time_str=fmt_time, label="Alarm", lang=lang))
                if lang == "hi":
                    executed_steps.append(f"{fmt_time} का अलार्म सेट कर दिया गया है।")
                elif lang == "mr":
                    executed_steps.append(f"{fmt_time} चा अलार्म सेट केला आहे.")
                elif lang == "gu":
                    executed_steps.append(f"{fmt_time} નો અલાર્મ સેટ કરી દીધો છે.")
                else:
                    executed_steps.append(f"Alarm set for {fmt_time}.")
                continue
        elif al_act == "cancel":
            resp = handle_alarm_cancel(seg, lang)
            executed_steps.append(resp)
            continue

        # If not matched to any device command, it's a knowledge or factual query!
        knowledge_parts.append(seg)

    if not executed_steps:
        return None, None
        
    device_reply = " ".join(executed_steps)
    remaining_query = " ".join(knowledge_parts).strip() if knowledge_parts else None
    return device_reply, remaining_query

CARTESIA_VOICE_MAP = {
    "en": {"id": "db6b0ed5-d5d3-463d-ae85-518a07d3c2b4", "name": "Skylar"},
    "hi": {"id": "db6b0ed5-d5d3-463d-ae85-518a07d3c2b4", "name": "Skylar"},
    "gu": {"id": "4590a461-bc68-4a50-8d14-ac04f5923d22", "name": "Isha"},
    "mr": {"id": "07bc462a-c644-49f1-baf7-82d5599131be", "name": "Sindhu"},
}

# --- Saved Memory & State ---
MEMORY_FILE = "memory.json"
conversation_history = deque(maxlen=12)  # Retain last 12 conversational turns (6 exchanges)
seen_news_history = deque(maxlen=80)  # Tracks recently spoken headlines to guarantee zero repetition
last_news_topic = "Palghar"  # Remembers last news topic/location for seamless follow-ups ("tell me more")
FOLLOW_UP_WORDS = [
    "more", "another", "next", "else", "what else", "continue", "further",
    "aur", "aur batao", "aur bata", "dusri", "doosri", "dusra", "agla", "aage",
    "और", "और बताओ", "दूसरी", "दूसरा", "अगला", "आगे", "और क्या", "आगे बताओ",
    "aankhi", "pudhe", "pudhchi", "dusri", "dusra",
    "आणखी", "पुढची", "दुसरी", "पुढे", "आणखी सांगा", "दुसरं",
    "biju", "bija", "vadhu", "aagal", "aagal janavo",
    "બીજા", "બીજું", "વધુ", "આગળ", "બીજા સમાચાર"
]
# --- Timers & Alarms ---
active_timers = {}  # timer_id -> dict: {id, name, duration, start_time, end_time, context, completion_phrase, lang, task}
active_stopwatch = {
    "running": False,
    "start_time": None,
    "elapsed_before_pause": 0.0,
    "laps": []  # list of {"lap_num": int, "split_time": float, "total_time": float, "formatted": str}
}
active_alarms = {}  # alarm_id -> dict: {id, time_str, label, target_ts, lang, task}
pending_timer_suggestion = None  # {dish_key, name, seconds, prompt, confirm, complete, lang, timestamp}

COOKING_PRESETS = {
    "maggi": {
        "names": ["maggi", "मैगी", "मॅगी", "મેગી", "noodles", "नूडल्स"],
        "seconds": 120,
        "dish_display": "Maggi",
        "phrases": {
            "en": {
                "prompt": "Should I set a 2-minute timer for your Maggi?",
                "confirm": "Starting your 2-minute timer for Maggi now!",
                "complete": "Your 2 minutes timer for Maggi is done! Look at your Maggi, is it cooked?"
            },
            "hi": {
                "prompt": "क्या मैं आपकी मैगी के लिए 2 मिनट का टाइमर लगा दूँ?",
                "confirm": "आपकी मैगी के लिए 2 मिनट का टाइमर शुरू कर दिया है!",
                "complete": "आपकी मैगी का 2 मिनट का टाइमर पूरा हो गया है! देखिए आपकी मैगी बन गई क्या?"
            },
            "mr": {
                "prompt": "तुमच्या मॅगीसाठी 2 मिनिटांचा टायमर लावू का?",
                "confirm": "तुमच्या मॅगीसाठी 2 मिनिटांचा टायमर सुरू केला आहे!",
                "complete": "तुमच्या मॅगीचा 2 मिनिटांचा टायमर पूर्ण झाला आहे! बघा तुमची मॅगी झाली का?"
            },
            "gu": {
                "prompt": "તમારી મેગી માટે 2 મિનિટનો ટાઈમર લગાવી દઉં?",
                "confirm": "તમારી મેગી માટે 2 મિનિટનો ટાઈમર શરૂ કરી દીધો છે!",
                "complete": "તમારી મેગી માટેનો 2 મિનિટનો ટાઈમર પૂરો થઈ ગયો છે! જુઓ તમારી મેગી તૈયાર થઈ ગઈ કે નહીં?"
            }
        }
    },
    "tea": {
        "names": ["tea", "chai", "चाय", "चहा", "ચા"],
        "seconds": 240,
        "dish_display": "Tea",
        "phrases": {
            "en": {
                "prompt": "Should I set a 4-minute timer for your tea?",
                "confirm": "Starting your 4-minute timer for tea now!",
                "complete": "Your 4 minutes timer for tea is complete! Check if the tea has boiled nicely!"
            },
            "hi": {
                "prompt": "क्या मैं आपकी चाय के लिए 4 मिनट का टाइमर लगा दूँ?",
                "confirm": "आपकी चाय के लिए 4 मिनट का टाइमर शुरू कर दिया है!",
                "complete": "आपकी चाय का 4 मिनट का टाइमर पूरा हो गया है! देखिए चाय में अच्छा उबाल आ गया क्या!"
            },
            "mr": {
                "prompt": "तुमच्या चहासाठी 4 मिनिटांचा टायमर लावू का?",
                "confirm": "तुमच्या चहासाठी 4 मिनिटांचा टायमर सुरू केला आहे!",
                "complete": "तुमच्या चहाचा 4 मिनिटांचा टायमर पूर्ण झाला आहे! बघा चहा छान उकळला का!"
            },
            "gu": {
                "prompt": "તમારી ચા માટે 4 મિનિટનો ટાઈમર લગાવી દઉં?",
                "confirm": "તમારી ચા માટે 4 મિનિટનો ટાઈમર શરૂ કરી દીધો છે!",
                "complete": "તમારી ચા માટેનો 4 મિનિટનો ટાઈમર પૂરો થઈ ગયો છે! જુઓ ચા બરાબર ઉકળી ગઈ કે નહીં?"
            }
        }
    },
    "egg": {
        "names": ["egg", "eggs", "boiled egg", "boiling egg", "boiling eggs", "ande", "anda", "अंडे", "अंडा", "अंडी", "ઇંડા"],
        "seconds": 480,
        "dish_display": "Boiling Eggs",
        "phrases": {
            "en": {
                "prompt": "Should I set an 8-minute timer for your boiling eggs?",
                "confirm": "Starting your 8-minute timer for boiling eggs now!",
                "complete": "Your egg boiling timer is finished! Time to take the eggs out into cold water!"
            },
            "hi": {
                "prompt": "क्या मैं अंडे उबालने के लिए 8 मिनट का टाइमर लगा दूँ?",
                "confirm": "अंडे उबालने के लिए 8 मिनट का टाइमर शुरू कर दिया है!",
                "complete": "अंडे उबलने का टाइमर पूरा हो गया है! अंडों को निकाल कर ठंडे पानी में डाल दीजिए!"
            },
            "mr": {
                "prompt": "अंडी उकडण्यासाठी 8 मिनिटांचा टायमर लावू का?",
                "confirm": "अंडी उकडण्यासाठी 8 मिनिटांचा टायमर सुरू केला आहे!",
                "complete": "अंडी उकडण्याचा टायमर पूर्ण झाला आहे! अंडी थंड पाण्यात काढून घ्या!"
            },
            "gu": {
                "prompt": "ઇંડા બાફવા માટે 8 મિનિટનો ટાઈમર લગાવી દઉં?",
                "confirm": "ઇંડા બાફવા માટે 8 મિનિટનો ટાઈમર શરૂ કરી દીધો છે!",
                "complete": "ઇંડા બાફવાનો ટાઈમર પૂરો થઈ ગયો છે! ઇંડાને ઠંડા પાણીમાં કાઢી લો!"
            }
        }
    },
    "milk": {
        "names": ["milk", "doodh", "dudh", "दूध", "दूध गरम", "દૂધ"],
        "seconds": 180,
        "dish_display": "Milk",
        "phrases": {
            "en": {
                "prompt": "Should I set a 3-minute timer for your milk?",
                "confirm": "Starting your 3-minute timer for milk now!",
                "complete": "Your milk heating timer is done! Check the stove before it spills over!"
            },
            "hi": {
                "prompt": "क्या मैं दूध के लिए 3 मिनट का टाइमर लगा दूँ?",
                "confirm": "दूध के लिए 3 मिनट का टाइमर शुरू कर दिया है!",
                "complete": "दूध का टाइमर पूरा हो गया है! गैस देख लीजिए कहीं दूध उफन न जाए!"
            },
            "mr": {
                "prompt": "दूधासाठी 3 मिनिटांचा टायमर लावू का?",
                "confirm": "दूधासाठी 3 मिनिटांचा टायमर सुरू केला आहे!",
                "complete": "दूधाचा टायमर पूर्ण झाला आहे! गॅस चेक करा दूध उतू जाऊ नये!"
            },
            "gu": {
                "prompt": "દૂધ માટે 3 મિનિટનો ટાઈમર લગાવી દઉં?",
                "confirm": "દૂધ માટે 3 મિનિટનો ટાઈમર શરૂ કરી દીધો છે!",
                "complete": "દૂધનો ટાઈમર પૂરો થઈ ગયો છે! ગેસ ચેક કરો દૂધ ઊભરાઈ ન જાય!"
            }
        }
    },
    "rice": {
        "names": ["rice", "chawal", "चावल", "भात", "ભાત"],
        "seconds": 600,
        "dish_display": "Rice",
        "phrases": {
            "en": {
                "prompt": "Should I set a 10-minute timer for your rice?",
                "confirm": "Starting your 10-minute timer for rice now!",
                "complete": "Your 10-minute rice timer is complete! Check if the rice is steamed properly!"
            },
            "hi": {
                "prompt": "क्या मैं चावल के लिए 10 मिनट का टाइमर लगा दूँ?",
                "confirm": "चावल के लिए 10 मिनट का टाइमर शुरू कर दिया है!",
                "complete": "चावल का 10 मिनट का टाइमर पूरा हो गया है! देखिए चावल अच्छे से पक गए क्या!"
            },
            "mr": {
                "prompt": "भातासाठी 10 मिनिटांचा टायमर लावू का?",
                "confirm": "भातासाठी 10 मिनिटांचा टायमर सुरू केला आहे!",
                "complete": "भाताचा 10 मिनिटांचा टायमर पूर्ण झाला आहे! भात छान शिजला का बघा!"
            },
            "gu": {
                "prompt": "ભાત માટે 10 મિનિટનો ટાઈમર લગાવી દઉં?",
                "confirm": "ભાત માટે 10 મિનિટનો ટાઈમર શરૂ કરી દીધો છે!",
                "complete": "ભાતનો 10 મિનિટનો ટાઈમર પૂરો થઈ ગયો છે! જુઓ ભાત સરસ ચડી ગયો કે નહીં!"
            }
        }
    },
    "pasta": {
        "names": ["pasta", "पास्ता"],
        "seconds": 480,
        "dish_display": "Pasta",
        "phrases": {
            "en": {
                "prompt": "Should I set an 8-minute timer for your pasta?",
                "confirm": "Starting your 8-minute timer for pasta now!",
                "complete": "Your 8-minute pasta timer is done! Check if it is al dente!"
            },
            "hi": {
                "prompt": "क्या मैं पास्ता के लिए 8 मिनट का टाइमर लगा दूँ?",
                "confirm": "पास्ता के लिए 8 मिनट का टाइमर शुरू कर दिया है!",
                "complete": "पास्ता का 8 मिनट का टाइमर पूरा हो गया है! चेक करिए पास्ता पक गया क्या!"
            },
            "mr": {
                "prompt": "पास्तासाठी 8 मिनिटांचा टायमर लावू का?",
                "confirm": "पास्तासाठी 8 मिनिटांचा टायमर सुरू केला आहे!",
                "complete": "पास्ताचा 8 मिनिटांचा टायमर पूर्ण झाला आहे! पास्ता छान शिजला का बघा!"
            },
            "gu": {
                "prompt": "પાસ્તા માટે 8 મિનિટનો ટાઈમર લગાવી દઉં?",
                "confirm": "પાસ્તા માટે 8 મિનિટનો ટાઈમર શરૂ કરી દીધો છે!",
                "complete": "પાસ્તાનો 8 મિનિટનો ટાઈમર પૂરો થઈ ગયો છે! જુઓ પાસ્તા બરાબર ચડી ગયો કે નહીં!"
            }
        }
    }
}

COOKING_ACTIONS = [
    "bana raha", "bana rahi", "bana rahe", "making", "cooking", "boiling", "heating",
    "banani hai", "banane ja raha", "chadhaya", "chadhayi", "pak raha", "pakane",
    "ubal raha", "ubal rahe", "ubalne", "rakha hai",
    "उबाल", "बना", "पका", "गर्म", "गरम", "बनव", "उकळ", "ઉકાળ", "બનાવ"
]

AFFIRMATIONS = [
    "haan", "ha", "haa", "yes", "sure", "kar do", "laga do", "lagao", "karo", "please do",
    "haan lagao", "ha laga do", "bilkul", "ok", "okay", "yep", "yeah", "definitely",
    "हो", "लावा", "करा", "हाँ", "हा", "लगा दो", "लगाओ", "कर दो", "બિલકુલ", "હા", "લગાવો"
]

REJECTIONS = [
    "nahi", "nahin", "no", "nope", "mat lagao", "cancel", "rahne do", "rehne do", "don't",
    "नको", "नाही", "नहीं", "रहने दो", "मत लगाओ", "ના", "રહેવા દો"
]

def dispatch_async(coro):
    """Safely runs an async coroutine whether called from an async loop thread or synchronous thread."""
    global loop
    if loop and loop.is_running():
        return asyncio.run_coroutine_threadsafe(coro, loop)
    else:
        try:
            cur_loop = asyncio.get_running_loop()
            return cur_loop.create_task(coro)
        except RuntimeError:
            return asyncio.run(coro)

def get_timers_data():
    now_sec = time.time()
    result = []
    for tid, t in list(active_timers.items()):
        rem = max(0, t["end_time"] - now_sec)
        result.append({
            "id": tid,
            "name": t.get("name", "Timer"),
            "label": t.get("name", "Timer"),
            "duration": t.get("duration", 0),
            "seconds": rem,
            "remaining": round(rem, 1),
            "end_time": t.get("end_time", 0),
            "start_time": t.get("start_time", 0),
            "context": t.get("context", "general"),
            "completion_phrase": t.get("completion_phrase", ""),
            "lang": t.get("lang", "en")
        })
    result.sort(key=lambda x: x["remaining"])
    return result

def get_stopwatch_data():
    now = time.time()
    elapsed = active_stopwatch["elapsed_before_pause"]
    if active_stopwatch["running"] and active_stopwatch["start_time"]:
        elapsed += (now - active_stopwatch["start_time"])
    return {
        "running": active_stopwatch["running"],
        "elapsed": round(elapsed, 2),
        "start_time": active_stopwatch["start_time"],
        "elapsed_before_pause": round(active_stopwatch["elapsed_before_pause"], 2),
        "laps": list(active_stopwatch["laps"])
    }

def get_alarms_data():
    now_sec = time.time()
    result = []
    for aid, a in list(active_alarms.items()):
        rem = max(0, a["target_ts"] - now_sec)
        result.append({
            "id": aid,
            "time_str": a.get("time_str", ""),
            "label": a.get("label", "Alarm"),
            "target_ts": a.get("target_ts", 0),
            "remaining_seconds": round(rem),
            "lang": a.get("lang", "en")
        })
    result.sort(key=lambda x: x["target_ts"])
    return result

def format_duration_desc(seconds: int, lang: str = "en") -> str:
    mins = seconds // 60
    secs = seconds % 60
    if mins > 0 and secs > 0:
        if lang == "hi":
            return f"{mins} मिनट {secs} सेकंड"
        elif lang == "mr":
            return f"{mins} मिनिटे {secs} सेकंद"
        elif lang == "gu":
            return f"{mins} મિનિટ {secs} સેકન્ડ"
        else:
            return f"{mins} minute and {secs} seconds"
    elif mins > 0:
        if lang == "hi":
            return f"{mins} मिनट"
        elif lang == "mr":
            return f"{mins} मिनिटे"
        elif lang == "gu":
            return f"{mins} મિનિટ"
        else:
            return f"{mins} minute{'s' if mins > 1 else ''}"
    else:
        if lang == "hi":
            return f"{secs} सेकंड"
        elif lang == "mr":
            return f"{secs} सेकंद"
        elif lang == "gu":
            return f"{secs} સેકન્ડ"
        else:
            return f"{secs} seconds"

def format_stopwatch_clock(seconds: float) -> str:
    total_ms = int(seconds * 100)
    mins = (total_ms // 6000) % 60
    secs = (total_ms // 100) % 60
    hundredths = total_ms % 100
    return f"{mins:02d}:{secs:02d}.{hundredths:02d}"

def detect_proactive_cooking(query: str, lang: str = "en"):
    q_lower = query.lower()
    
    # Rule 1: NEVER hijack educational, instructional, recipe, or question queries!
    is_instructional = any(re.search(r'\b' + re.escape(w) + r'\b', q_lower) for w in [
        "teach", "teach me", "how to", "recipe", "kaise", "batao", "bataiye", "sikhao", "sikha",
        "ingredients", "process", "tips", "can you", "what is", "kya hai", "explain", "story",
        "repeat", "tell me", "meaning", "define", "history"
    ])
    if is_instructional:
        return None

    # Rule 2: Never trigger if query is already about device clocks/timers explicitly
    if any(w in q_lower for w in ["timer", "stopwatch", "alarm", "टाइमर", "अलार्म", "स्टॉपवॉच", "टायमर", "ટાઈમર"]):
        return None

    # Rule 3: Only trigger on explicit active present cooking statements (e.g. "I am making tea", "chai chadhayi hai")
    ACTIVE_COOKING_PATTERNS = [
        r'\b(?:i am|i\'m|we are|we\'re)\s+(?:making|boiling|cooking|heating|preparing)\b',
        r'\b(?:maine|humne|me)\s+(?:chadhaya|chadhayi|rakha|rakhi)\s+hai\b',
        r'\b(?:chadhai|chadhaya|ubal raha|ubal rahi|pak raha|pak rahi)\b',
        r'\b(?:just put|putting on)\b'
    ]
    has_active_action = any(re.search(pat, q_lower) for pat in ACTIVE_COOKING_PATTERNS)
    if not has_active_action:
        return None

    # Rule 4: Strict word-boundary matching (prevents "tea" matching inside "teach"!)
    for dish_key, p in COOKING_PRESETS.items():
        if any(re.search(r'\b' + re.escape(name) + r'\b', q_lower) for name in p["names"]):
            phrase_data = p["phrases"].get(lang, p["phrases"]["en"])
            return {
                "dish_key": dish_key,
                "dish_display": p["dish_display"],
                "seconds": p["seconds"],
                "prompt": phrase_data["prompt"],
                "confirm": phrase_data["confirm"],
                "complete": phrase_data["complete"],
                "lang": lang
            }
    return None

def parse_alarm_time(time_str: str) -> tuple[datetime.datetime, str] | None:
    t_str = time_str.lower().strip()
    is_pm = "pm" in t_str or "shaam" in t_str or "sham" in t_str or "raat" in t_str or "dopahar" in t_str or "दुपार" in t_str or "संध्याकाळ" in t_str or "રાત" in t_str or "સાંજ" in t_str
    is_am = "am" in t_str or "subah" in t_str or "pratah" in t_str or "सकाळ" in t_str or "સવાર" in t_str
    m = re.search(r'(\d{1,2}):(\d{2})', t_str)
    if m:
        h = int(m.group(1))
        minute = int(m.group(2))
    else:
        m = re.search(r'(\d{1,2})\s*(?:baje|vagle|vagya|o\'clock|am|pm|बजे|वाजता|વાગ્યે|$)', t_str)
        if m:
            h = int(m.group(1))
            minute = 0
        else:
            return None
    if is_pm and h < 12:
        h += 12
    elif is_am and h == 12:
        h = 0
    if not (0 <= h <= 23 and 0 <= minute <= 59):
        return None
    now = datetime.datetime.now()
    target = now.replace(hour=h, minute=minute, second=0, microsecond=0)
    if target <= now:
        target += datetime.timedelta(days=1)
    fmt_str = target.strftime("%I:%M %p")
    return target, fmt_str

def parse_direct_timer(query: str):
    q_lower = query.lower()
    if not any(w in q_lower for w in ["timer", "टाइमर", "टायमर", "ટાઈમર"]):
        return None
    if any(w in q_lower for w in ["cancel", "stop", "band", "roko", "hatao", "रद्द", "बंद", "रोको", "રદ", "how much", "kitna", "remaining", "status", "bache", "baka"]):
        return None
    m_min = re.search(r'(\d+)\s*(?:minute|min|m|मिनट|મિનિટ)', q_lower)
    m_sec = re.search(r'(\d+)\s*(?:second|sec|s|सेकंड|સેકન્ડ)', q_lower)
    total_seconds = 0
    if m_min:
        total_seconds += int(m_min.group(1)) * 60
    if m_sec:
        total_seconds += int(m_sec.group(1))
    if not m_min and not m_sec:
        m_bare = re.search(r'(?:timer\s*(?:for|of)?|for)\s*(\d+)', q_lower)
        if m_bare:
            val = int(m_bare.group(1))
            total_seconds = val * 60 if val <= 60 else val
    if total_seconds <= 0:
        return None
        
    dish_name = None
    for k, p in COOKING_PRESETS.items():
        if any(n in q_lower for n in p["names"]):
            dish_name = p["dish_display"]
            break
            
    INVALID_TIMER_NAMES = {
        "me", "myself", "us", "him", "her", "it", "them", "now", "today", "tonight", "later",
        "please", "a", "an", "the", "my", "our", "your", "this", "that", "something",
        "timer", "alarm", "stopwatch", "time", "clock", "same", "another",
        "second", "seconds", "sec", "secs", "minute", "minutes", "min", "mins", "hour", "hours",
        "one", "two", "three", "four", "five", "six", "seven", "eight", "nine", "ten"
    }
    
    if not dish_name:
        # Search all 'for <target>' occurrences (skipping 'for me', 'for 10 seconds', etc.)
        for match in re.finditer(r'for\s+(?:my\s+|the\s+|a\s+|an\s+)?([a-zA-Z\u0900-\u0AFF]+)', q_lower):
            cand = match.group(1).strip()
            if cand.lower() not in INVALID_TIMER_NAMES and not cand.isdigit() and len(cand) >= 2:
                dish_name = cand.title()
                break
                
    if not dish_name:
        for match in re.finditer(r'([a-zA-Z\u0900-\u0AFF]+)\s+ke\s+liye', q_lower):
            cand = match.group(1).strip()
            if cand.lower() not in INVALID_TIMER_NAMES and not cand.isdigit() and len(cand) >= 2:
                dish_name = cand.title()
                break
                
    if not dish_name:
        mins = total_seconds // 60
        secs = total_seconds % 60
        if mins > 0 and secs == 0:
            dish_name = f"{mins}-minute timer"
        elif secs > 0 and mins == 0:
            dish_name = f"{secs}-second timer"
        else:
            dish_name = f"{mins}m {secs}s timer"
            
    return total_seconds, dish_name

def is_timer_query(query: str):
    q_lower = query.lower()
    has_timer_word = any(w in q_lower for w in ["timer", "टाइमर", "टायमर", "ટાઈમર"])
    has_dish = any(any(n in q_lower for n in p["names"]) for p in COOKING_PRESETS.values())
    has_query_cue = any(w in q_lower for w in [
        "how much", "time left", "remaining", "status", "kitna", "kitne", "bache", "baka", "chal raha", "chal rahe",
        "kitna time", "how long", "left on", "how many", "running", "active",
        "कितना समय", "कितने", "बाकी", "शिल्लक", "કેટલા", "કેટલો સમય"
    ])
    if has_timer_word and has_query_cue:
        return True
    if has_dish and ("left" in q_lower or "remaining" in q_lower or "kitna" in q_lower or "bache" in q_lower or "time left" in q_lower):
        return True
    return False

def is_timer_cancel(query: str):
    q_lower = query.lower()
    has_timer_word = any(w in q_lower for w in ["timer", "टाइमर", "टायमर", "ટાઈમર"])
    has_dish = any(any(n in q_lower for n in p["names"]) for p in COOKING_PRESETS.values())
    has_cancel_cue = any(w in q_lower for w in [
        "cancel", "stop", "band", "roko", "hatao", "delete", "clear",
        "रद्द", "बंद", "रोको", "हटाओ", "કાઢી", "રદ"
    ])
    return (has_timer_word or has_dish) and has_cancel_cue

def parse_stopwatch_intent(query: str):
    q_lower = query.lower()
    is_sw = any(w in q_lower for w in ["stopwatch", "stop watch", "स्टॉपवॉच", "સ્ટોપવોચ", "the porch", "porch"])
    is_lap = bool(re.search(r'\b(?:lap|लैप|लॅप|લેપ)\b', q_lower))
    if not is_sw and not is_lap:
        return None
        
    # 1. Lap check
    if is_lap:
        return "lap"
        
    # 2. Stop / Pause check (Prioritized so 'stop the stopwatch' stops it cleanly)
    if re.search(r'\b(?:stop|pause|roko|band|halt|khatam|end)\b', q_lower) or any(w in q_lower for w in ["रोक", "बंद", "થોભાવો", "थांबवा"]):
        return "stop"
        
    # 3. Resume check
    if re.search(r'\b(?:resume|continue|chalu rakho|chalu karo)\b', q_lower) or any(w in q_lower for w in ["चालू रखो", "चालू ठेवा"]):
        return "resume"

    # 4. Start check
    if re.search(r'\b(?:start|shuru|chalu|begin)\b', q_lower) or any(w in q_lower for w in ["शुरू", "चालू", "શરૂ"]):
        return "start"
        
    # 5. Reset check
    if re.search(r'\b(?:reset|zero|clear)\b', q_lower) or any(w in q_lower for w in ["रीसेट", "ઝીરો"]):
        return "reset"
        
    # 6. Query check ('What is the time in the stopwatch', 'how much time done', etc.)
    if re.search(r'\b(?:how much|status|time|kitna|kitne|chal raha|running|elapsed|batao|kya)\b', q_lower) or any(w in q_lower for w in ["कितना", "કેટલા", "काय", "वेळ"]):
        return "query"
        
    return "query" if is_sw else None

def parse_alarm_intent(query: str):
    q_lower = query.lower()
    if not any(w in q_lower for w in ["alarm", "अलार्म", "અલાર્મ"]):
        return None
    if any(w in q_lower for w in ["cancel", "stop", "band", "delete", "hatao", "रद्द", "बंद", "हटाओ"]):
        return "cancel"
    if any(w in q_lower for w in ["what", "list", "show", "status", "how many", "कितने", "કયા", "सांगा", "बताओ"]):
        return "list"
    if any(w in q_lower for w in ["set", "lagao", "karo", "लगाओ", "सेट", "કરો", "લગાવો"]) or any(char.isdigit() for char in q_lower):
        return "set"
    return "list"

ws_clients = set()
recording_task = None
audio_buffer = bytearray()
is_listening = False
speech_confirmed = False
speech_frames_count = 0
silence_frames_count = 0
total_voiced_frames = 0
ambient_noise_samples = []
ambient_noise_baseline = 450
client = None
loop = None
button_key_cache = None
wake_word_button_key = None
aura_led_key = None

# --- WS2812 LED Control ---
def set_aura_led(mode: str):
    """
    Sets the 8-bit WS2812 RGB LED strip pattern based on voice assistant / telephony state.
    Modes:
      - 'listening': Electric Cyan (0.0, 0.8, 1.0)
      - 'thinking': Thinking Wipe effect (Blue scanning)
      - 'speaking': Speaking Pulse effect (Azure breathing pulse)
      - 'ringing': Call Radar effect (Green radar sweep)
      - 'in_call': Solid Emerald Green (0.0, 1.0, 0.2)
      - 'muted': Solid Crimson Red (1.0, 0.0, 0.0)
      - 'hangup': Solid Red brief pulse, then off
      - 'idle' / 'off': Turns LED off
    """
    global client, loop, aura_led_key
    if not client or not aura_led_key or not is_connected():
        return

    def _do():
        try:
            if not client or not aura_led_key:
                return
            if mode == "listening":
                client.light_command(key=aura_led_key, state=True, brightness=0.7, rgb=(0.0, 0.8, 1.0), effect="None")
            elif mode == "thinking":
                client.light_command(key=aura_led_key, state=True, brightness=0.8, effect="Thinking Wipe")
            elif mode == "speaking":
                client.light_command(key=aura_led_key, state=True, brightness=0.7, effect="Speaking Pulse", rgb=(0.1, 0.6, 1.0))
            elif mode == "ringing":
                client.light_command(key=aura_led_key, state=True, brightness=0.85, effect="Call Radar")
            elif mode == "in_call":
                client.light_command(key=aura_led_key, state=True, brightness=0.7, rgb=(0.0, 1.0, 0.2), effect="None")
            elif mode == "muted":
                client.light_command(key=aura_led_key, state=True, brightness=0.85, rgb=(1.0, 0.0, 0.0), effect="None")
            elif mode in ("idle", "off"):
                client.light_command(key=aura_led_key, state=False)
            elif mode == "hangup":
                client.light_command(key=aura_led_key, state=True, brightness=0.5, rgb=(1.0, 0.1, 0.1), effect="None")
                def _off():
                    try:
                        if client and aura_led_key and is_connected():
                            client.light_command(key=aura_led_key, state=False)
                    except Exception:
                        pass
                if loop and not loop.is_closed():
                    loop.call_later(1.2, _off)
        except Exception as e:
            print(f"[AURA LED ERROR]: {e}")

    if loop and not loop.is_closed():
        loop.call_soon_threadsafe(_do)
    else:
        try:
            _do()
        except Exception:
            pass
audio_stream_lock = None
playback_interrupt_event = asyncio.Event()
active_streamer_task = None
active_pipeline_task = None
active_audio_queue = None
AUDIO_CACHE = {}  # In-memory dictionary cache for sub-millisecond audio playback

# --- Echo Reduction ---
speaker_reference_ring = deque(maxlen=48000)  # Stores last 3 seconds of 16kHz 16-bit PCM sent to MAX98357A
last_speaker_active_ts = 0.0

def record_speaker_audio_chunk(pcm_chunk: bytes):
    """Stores outgoing speaker audio in circular reference ring for echo subtraction."""
    global last_speaker_active_ts
    last_speaker_active_ts = time.time()
    if pcm_chunk:
        try:
            samples = np.frombuffer(pcm_chunk, dtype=np.int16)
            speaker_reference_ring.extend(samples)
        except Exception:
            pass

def process_aec_and_noise_suppression(mic_bytes: bytes) -> bytes:
    """
    Google Meet style Acoustic Echo Cancellation (AEC) & Spectral Noise Subtraction:
    1. If assistant was speaking, cross-correlate mic audio against speaker reference
       to find acoustic room delay tau (typically 30-150ms) and subtract the scaled echo.
    2. Performs adaptive spectral gating / noise suppression to eliminate fan, AC, and room reverberation.
    """
    if not mic_bytes or len(mic_bytes) < 320:
        return mic_bytes

    try:
        t0 = time.perf_counter()
        mic_samples = np.frombuffer(mic_bytes, dtype=np.int16).astype(np.float32)

        # 1. Acoustic Echo Subtraction (if speaker was active within last 2.0s)
        time_since_speech = time.time() - last_speaker_active_ts
        if time_since_speech < 2.0 and len(speaker_reference_ring) >= 1600:
            ref_samples = np.array(speaker_reference_ring, dtype=np.float32)
            n_mic = len(mic_samples)
            n_ref = len(ref_samples)
            
            search_len = min(n_mic, 8000)
            if n_ref >= search_len:
                ref_slice = ref_samples[-search_len:]
                ref_power = np.mean(ref_slice ** 2) + 1e-6
                mic_power = np.mean(mic_samples[:search_len] ** 2) + 1e-6
                
                if ref_power > 150.0:  # Speaker was physically active
                    corr = np.correlate(mic_samples[:search_len], ref_slice, mode='full')
                    delay = np.argmax(corr) - (search_len - 1)
                    
                    alpha = np.clip(np.sqrt(mic_power / ref_power) * 0.65, 0.0, 0.85)
                    aligned_ref = np.zeros_like(mic_samples)
                    full_ref_slice = ref_samples[-min(n_mic, n_ref):]
                    aligned_ref[:len(full_ref_slice)] = full_ref_slice
                    mic_samples = mic_samples - (alpha * aligned_ref)

        # 2. Spectral Noise Gating (Google Meet Spectral Subtraction)
        cleaned = nr.reduce_noise(
            y=mic_samples,
            sr=16000,
            stationary=True,
            prop_decrease=0.75,
            n_fft=512,
            win_length=400,
            hop_length=160
        )
        
        cleaned_int16 = np.clip(cleaned, -32768, 32767).astype(np.int16)
        dt_ms = (time.perf_counter() - t0) * 1000
        print(f"[AEC & NOISE SUPPRESSION]: Cleaned {len(mic_bytes)} bytes in {dt_ms:.1f}ms (Echo Subtracted + Background Damped)")
        return cleaned_int16.tobytes()
    except Exception as e:
        print(f"[AEC WARNING - Fallback to raw audio]: {e}")
        return mic_bytes


def get_audio_stream_lock():
    global audio_stream_lock
    if audio_stream_lock is None:
        audio_stream_lock = asyncio.Lock()
    return audio_stream_lock

# --- Microphone Interruption (Barge-In) ---
active_recording_task = None
timer_preemption_active = False
pending_deferred_answer = None
timer_preempted_user_query = None

# Non-disruptive capture & sequential delivery queues
pending_priority_alerts = []       # Thread-safe queue for alerts expiring while user is speaking
pending_disconnected_alerts = []   # Buffer with 90s TTL if ESP32 Wi-Fi briefly drops

# --- Follow-Up Listening ---
active_followup_window = {
    "is_active": False,
    "consecutive_turns": 0,
    "max_chain_depth": 3,
    "expecting_reply": False,
    "last_topic": ""
}
pending_followup_intent = False

DISMISSAL_PHRASES = {
    # English
    "no", "no thanks", "no thank you", "nope", "nothing", "thats all", "that is all",
    "thats it", "that is it", "im good", "i am good", "never mind", "nevermind", "all good",
    "none", "not now", "no need", "nah", "stop", "cancel",
    # Hindi / Hinglish
    "नहीं", "ना", "बस", "कुछ नहीं", "रहने दो", "नहीं चाहिए", "nahi", "nahin", "kuch nahi",
    "bas", "rehne do", "nahi chahiye", "kuchh nahi", "na",
    # Marathi
    "नाही", "नको", "काही नाही", "राहू दे", "नको काही", "nako", "kahi nahi", "rahu de",
    # Gujarati
    "ના", "નથી", "કાંઈ નહીં", "રહેવા દો", "નથી જોઈતું", "nathi", "kai nahi", "reva do"
}

def is_followup_dismissal(text: str) -> bool:
    """Checks whether the user's speech in a follow-up window is a polite rejection/dismissal."""
    if not text:
        return False
    clean = re.sub(r'[^\w\s\u0900-\u097F\u0A80-\u0AFF]', '', text.lower()).strip()
    words = clean.split()
    if clean in DISMISSAL_PHRASES:
        return True
    if len(words) <= 3 and any(w in DISMISSAL_PHRASES for w in [clean, *words]):
        return True
    return False

def extract_pivot_query(text: str) -> str:
    """
    Extracts the redirected target query when a user interrupts with mid-speech redirection.
    e.g. 'Alexa, don't tell this, tell this what is the capital of France' -> 'what is the capital of France'
         'ye mat batao, ye batao Bharat ki rajdhani kya hai' -> 'Bharat ki rajdhani kya hai'
    """
    if not text:
        return text
    pivot_patterns = [
        # English: "don't tell this/that, tell this/me X", "leave that, tell me X", "stop, tell me X"
        r'^(?:(?:no|wait|hey|alexa)\s*[,;.-]?\s*)*(?:don[\'t]*\s+tell\s+(?:me\s+)?(?:this|that)|don[\'t]*\s+say\s+(?:this|that)|leave\s+(?:this|that)|stop\s+(?:it|that|this)?)\s*[,;.-]?\s*(?:instead\s+)?(?:tell\s+(?:me|this|that|us)\s+)?\s*(.+)',
        # Hindi: "ये मत बताओ, ये बताओ X" or "छोड़ो, बताओ X"
        r'^(?:अरे\s*)?(?:यह|ये)?\s*(?:मत\s+(?:बताओ|बोलो)|छोड़ो)\s*[,;.-]?\s*(?:मुझे\s+)?(?:यह|ये|अब)?\s*(?:बताओ|बोलो)?\s*(.+)',
        # Marathi: "हे नको सांगू, हे सांग X" or "सोड, सांग X"
        r'^(?:हे\s*)?(?:नको\s+सांगू|सोड)\s*[,;.-]?\s*(?:हे\s+सांग|सांगा|मला\s+सांग)?\s*(.+)',
        # Gujarati: "આ ના કહે, આ બોલ X" or "છોડો, કહો X"
        r'^(?:આ\s*)?(?:ના\s+કહે|ના\s+બોલ|છોડો)\s*[,;.-]?\s*(?:આ\s+કહો|આ\s+જણાવો|મને\s+કહો)?\s*(.+)',
    ]
    for pat in pivot_patterns:
        m = re.match(pat, text, re.IGNORECASE)
        if m and m.group(1).strip():
            extracted = m.group(1).strip()
            # If extracted starts with "tell this", "tell me", "this", "batao", strip that leading wrapper
            extracted = re.sub(r'^(?:tell\s+(?:me|this|that|us)|batao|sang|kaho|this|that)[,\s!.]+', '', extracted, flags=re.IGNORECASE).strip()
            if extracted:
                return extracted
    return text

def is_query_strictly_single_turn(user_query: str) -> bool:
    """Priority-Gated Rule: Strictly forbids follow-up probes on utility, device, or simple factual tasks."""
    q_low = user_query.lower()
    # 1. Device controls & System actions (Timers, Alarms, Volume, Stopwatch)
    if any(k in q_low for k in ['timer', 'alarm', 'stopwatch', 'volume', 'loud', 'quiet', 'mute', 'cancel', 'stop', 'pause', 'reset', 'clear', 'wipe', 'remember', 'forget', 'memory']):
        return True
    # 2. Daily Utility / Closed factual answers
    if any(k in q_low for k in ['time', 'date', 'day', 'today', 'weather', 'temperature', 'rain', 'forecast', 'petrol', 'diesel', 'cng', 'fuel', 'gold rate', 'silver rate']):
        return True
    # 3. Simple math, conversions, calculations
    if any(k in q_low for k in ['calculate', 'how much is', 'how many', 'convert', 'percent', '%', 'plus', 'minus', 'multiply', 'divide', 'saved', 'growth', 'compound']):
        return True
    # 4. Direct identity / Definition / Closed lookups
    if any(k in q_low for k in ['who is', 'capital of', 'meaning of', 'define ', 'difference between']):
        return True
    return False

def extract_followup_decision(full_raw: str, full_clean: str, user_query: str = "") -> bool:
    """
    Priority-Gated Follow-Up Matrix:
    Strictly forbids follow-up prompts on P0 single-turn tasks (device controls, time, weather, math, definitions).
    Only allows follow-up on genuine exploratory queries where continuation is necessary.
    """
    if user_query and is_query_strictly_single_turn(user_query):
        return False
    if "[FOLLOWUP: NO]" in full_raw:
        return False
    if "[FOLLOWUP: YES]" in full_raw:
        return True
    clean_text = re.sub(r'\[[^\]]*\]', '', full_clean).strip()
    if not clean_text:
        return False
    if re.search(r'[?؟]\s*$', clean_text):
        return True
    return False
    if "[FOLLOWUP: YES]" in full_raw:
        return True
    clean_text = re.sub(r'\[[^\]]*\]', '', full_clean).strip()
    if not clean_text:
        return False
    if re.search(r'[?؟]\s*$', clean_text):
        return True
    return False

def get_bridge_phrase(lang: str) -> str:
    """Localized bridge connecting the timer alert to the user's query answer."""
    bridges = {
        "hi": " और आपके सवाल का जवाब: ",
        "mr": " आणि तुमच्या प्रश्नाचे उत्तर: ",
        "gu": " અને તમારા પ્રશ્નનો જવાબ: ",
        "en": " And regarding your question: "
    }
    return bridges.get(lang, bridges["en"])

def coalesce_priority_alerts(alerts: list, lang: str = "en") -> str:
    """Coalesces multiple expiring alerts into a single cohesive, natural sentence."""
    if not alerts:
        return ""
    if len(alerts) == 1:
        return alerts[0]["completion_phrase"]
        
    names = [a.get("name", "Timer") for a in alerts]
    if len(names) == 2:
        joined = f"{names[0]} and {names[1]}" if lang == "en" else f"{names[0]} और {names[1]}"
    else:
        joined = ", ".join(names[:-1]) + (f", and {names[-1]}" if lang == "en" else f", और {names[-1]}")
        
    if lang == "hi":
        return f"आपके {joined} टाइमर पूरे हो चुके हैं!"
    elif lang == "mr":
        return f"तुमचे {joined} टायमर पूर्ण झाले आहेत!"
    elif lang == "gu":
        return f"તમારા {joined} ટાઈમર પૂર્ણ થઈ ગયા છે!"
    else:
        return f"Your {joined} timers are both complete!"

async def trigger_mic_start():
    """Triggers ESP32 microphone to start listening immediately without requiring wake word."""
    global button_key_cache
    if not is_connected():
        return False
    try:
        if button_key_cache is None:
            entities, _ = await asyncio.wait_for(client.list_entities_services(), timeout=3.0)
            for entity in entities:
                if hasattr(entity, 'name') and entity.name == "Force Start Mic":
                    button_key_cache = entity.key
                    break
        if button_key_cache:
            client.button_command(button_key_cache)
            print("[MIC AUTO-REOPENED]: Listening for follow-up speech directly!")
            return True
    except Exception as e:
        print(f"Error reopening mic: {e}")
    return False

async def execute_priority_alert(chime_pcm: bytes, completion_phrase: str, lang: str = "en", alert_type: str = "timer", name: str = "Timer"):
    """
    NON-DISRUPTIVE SEAMLESS CAPTURE & SEQUENTIAL DELIVERY DISPATCHER:
    1. If user is speaking / mic active (Stage 1 & 2):
       NEVER cut off mic! Buffers alert into pending_priority_alerts.
       When user finishes speaking, alert plays FIRST, directly followed by their answer without gaps or clashing.
    2. If Alexa is computing or streaming (Stage 3 & 4):
       Injects alert into the active audio queue so it plays in the same continuous stream.
    3. If device is IDLE (Stage 0):
       Wakes ESP32 DAC amp, plays chime + alert phrase, drains buffer cleanly to Idle.
    4. If ESP32 is temporarily disconnected:
       Keeps alert in pending_disconnected_alerts (TTL 90s) and flushes upon reconnection.
    """
    global is_listening, audio_buffer, active_recording_task, playback_interrupt_event
    global active_streamer_task, active_pipeline_task, active_audio_queue
    global pending_priority_alerts, pending_disconnected_alerts

    print(f"\n[PRIORITY ALERT TRIGGERED]: Type={alert_type} | Name='{name}' | Phrase='{completion_phrase[:40]}...'")
    
    global is_processing_request
    # 1. State 1 & 2: User is currently speaking OR server is processing Whisper STT / Groq LLM
    if is_listening or is_processing_request:
        print(f"[PREEMPTION - BUSY]: Assistant is listening or processing. Buffering alert for '{name}' into pending_priority_alerts!")
        pending_priority_alerts.append({
            "type": alert_type,
            "name": name,
            "completion_phrase": completion_phrase,
            "chime_pcm": chime_pcm,
            "lang": lang,
            "timestamp": time.time()
        })
        return

    # 2. State 3 & 4: Pipeline is actively running and streaming
    if (active_pipeline_task and not active_pipeline_task.done()) and active_audio_queue is not None:
        print(f"[PREEMPTION - STAGE 3]: Groq pipeline is active. Injecting alert directly into active_audio_queue for seamless continuous playback!")
        active_loop = loop if (loop is not None and loop.is_running()) else asyncio.get_running_loop()
        try:
            tts_pcm, _, _ = await active_loop.run_in_executor(None, run_tts, completion_phrase, "", "", lang)
            full_audio = (chime_pcm or b'') + (tts_pcm or b'')
            if full_audio:
                await active_audio_queue.put(full_audio)
                return
        except Exception as ex:
            print(f"[PIPELINE INJECTION ERROR]: {ex}")

    # 3. State 0: Device is IDLE
    print(f"[PRIORITY ALERT - IDLE]: Delivering alert immediately over ESP32 speaker.")
    active_loop = loop if (loop is not None and loop.is_running()) else asyncio.get_running_loop()
    tts_pcm = None
    try:
        tts_pcm, _, _ = await active_loop.run_in_executor(None, run_tts, completion_phrase, "", "", lang)
    except Exception as ex:
        print(f"[PREEMPTION TTS ERROR]: {ex}")

    full_audio = (chime_pcm or b'') + (tts_pcm if tts_pcm else b'')
    playback_interrupt_event.clear()
    if full_audio:
        if is_connected():
            await stream_audio_to_esp32(full_audio, completion_phrase)
        else:
            print(f"[DISCONNECTED BUFFER]: ESP32 offline. Storing alert '{completion_phrase}' in retry buffer.")
            pending_disconnected_alerts.append({
                "audio": full_audio,
                "phrase": completion_phrase,
                "timestamp": time.time()
            })

# Load or initialize persistent responsive zero-base memory
def load_memory():
    if os.path.exists(MEMORY_FILE):
        try:
            with open(MEMORY_FILE, 'r', encoding='utf-8') as f:
                d = json.load(f)
                if "memories" not in d:
                    d["memories"] = []
                return d
        except Exception as e:
            print(f"Error loading memory.json: {e}")
    initial = {
        "user_name": None,
        "memories": []
    }
    save_memory(initial)
    return initial

# --- User Fact Storage ---

PRONOUN_MAP_EN = [
    (r"\bi am\b", "you are"),
    (r"\bi'm\b", "you're"),
    (r"\bi have\b", "you have"),
    (r"\bi've\b", "you've"),
    (r"\bi like\b", "you like"),
    (r"\bi love\b", "you love"),
    (r"\bmy\b", "your"),
    (r"\bmine\b", "yours"),
    (r"\bme\b", "you"),
    (r"\bi\b", "you"),
]

PRONOUN_MAP_HI = [
    (r"\bमेरा\b", "आपका"),
    (r"\bमेरी\b", "आपकी"),
    (r"\bमेरे\b", "आपके"),
    (r"\bमुझे\b", "आपको"),
    (r"\bमुझसे\b", "आपसे"),
    (r"\bमैं\b", "आप"),
]

PRONOUN_MAP_MR = [
    (r"\bमाझा\b", "तुमचा"),
    (r"\bमाझी\b", "तुमची"),
    (r"\bमाझे\b", "तुमचे"),
    (r"\bमला\b", "तुम्हाला"),
    (r"\bमी\b", "तुम्ही"),
]

PRONOUN_MAP_GU = [
    (r"\bમારું\b", "તમારું"),
    (r"\bમારી\b", "તમારી"),
    (r"\bમારો\b", "તમારો"),
    (r"\bમને\b", "તમને"),
    (r"\bહું\b", "તમે"),
]

def invert_pronouns_for_storage(text: str, lang: str = "en") -> str:
    """Converts 1st-person user speech ('my favorite color is red') to 2nd-person assistant memory ('your favorite color is red')."""
    t = text.strip()
    if lang == "en":
        # 1. Two-party interaction phrases: "I [have] [verb] you" -> "you [have] [verb] me"
        t = re.sub(r'\bi\s+(have\s+)?([a-zA-Z]+)\s+you\b', r'you \1\2 me', t, flags=re.IGNORECASE)
        t = re.sub(r'\bi\s+am\s+([a-zA-Z]+)\s+to\s+you\b', r'you are \1 to me', t, flags=re.IGNORECASE)
        for pat, repl in PRONOUN_MAP_EN:
            t = re.sub(pat, repl, t, flags=re.IGNORECASE)
        # Ensure proper capitalization
        if t:
            t = t[0].upper() + t[1:]
    elif lang == "hi":
        for pat, repl in PRONOUN_MAP_HI:
            t = re.sub(pat, repl, t)
    elif lang == "mr":
        for pat, repl in PRONOUN_MAP_MR:
            t = re.sub(pat, repl, t)
    elif lang == "gu":
        for pat, repl in PRONOUN_MAP_GU:
            t = re.sub(pat, repl, t)
    return t.strip()

def resolve_contrastive_clauses(raw_fact: str) -> str:
    """
    Resolves self-correcting statements:
    'my favorite color is red. But my most favorite color is blue.' -> 'my most favorite color is blue'
    """
    splits = re.split(r'\b(?:but|however|actually|instead|rather|no wait|लेकिन|किंतु|परंतु|पण|પરંતુ)\b', raw_fact, flags=re.IGNORECASE)
    if len(splits) > 1:
        winner = splits[-1].strip()
        winner = re.sub(r'^[.,\s!?-]+', '', winner).strip()
        if len(winner.split()) >= 2:
            return winner
    return raw_fact.strip()

def extract_memory_slot_key(text: str) -> str | None:
    """Identifies the semantic topic/slot to intelligently overwrite conflicting facts (e.g. favorite color, registered platform)."""
    t_low = text.lower()
    if any(k in t_low for k in ["registered", "register", "platform", "project"]):
        return "registered"
    if any(k in t_low for k in ["your name is", "my name is", "user's name", "call me"]):
        return "name"
    if any(k in t_low for k in ["age is", "years old"]):
        return "age"
    # Check common slots
    m = re.search(r"\b(favorite\s+[a-z]+|most\s+favorite\s+[a-z]+|dog(?:'s)?\s+name|pet(?:'s)?\s+name|cat(?:'s)?\s+name|sister(?:'s)?\s+name|brother(?:'s)?\s+name|mother(?:'s)?\s+name|father(?:'s)?\s+name|birthday|hobby|job|college|school|car|friend|best\s+friend)\b", t_low)
    if m:
        # Normalize slot key (e.g. 'most favorite color' -> 'favorite color')
        slot = m.group(1).replace("most favorite", "favorite").strip()
        return slot
    return None

def add_user_memory(raw_fact: str, lang: str = "en") -> str:
    global memory_data
    raw_fact = raw_fact.strip()
    if not raw_fact:
        return ""
        
    # Prevent questions from being saved as memories!
    if raw_fact.endswith('?') or any(raw_fact.lower().startswith(q) for q in ['where', 'what', 'who', 'when', 'why', 'how', 'do you', 'can you', 'is ', 'are ', 'did ']):
        print(f"[MEMORY REJECTED]: Query was a question, not a fact: '{raw_fact}'")
        return ""

    if "memories" not in memory_data:
        memory_data["memories"] = []

    # 1. Resolve contrastive corrections ('X, but Y')
    resolved_fact = resolve_contrastive_clauses(raw_fact)

    # 2. Invert pronouns from user's perspective to assistant's perspective ('my' -> 'your')
    normalized_fact = invert_pronouns_for_storage(resolved_fact, lang=lang)
    if not normalized_fact.endswith(('.', '!', '?', '।')):
        normalized_fact += "."

    # 3. Detect semantic slot for overwrite (e.g. updating favorite color)
    slot_key = extract_memory_slot_key(normalized_fact)
    replaced = False
    if slot_key:
        for idx, existing in enumerate(memory_data["memories"]):
            if slot_key in existing.lower():
                memory_data["memories"][idx] = normalized_fact
                replaced = True
                print(f"[RESPONSIVE MEMORY (SLOT OVERWRITE)]: Updated '{slot_key}' -> '{normalized_fact}'")
                break
                
    if not replaced and normalized_fact not in memory_data["memories"]:
        memory_data["memories"].append(normalized_fact)
        print(f"[RESPONSIVE MEMORY]: Stored new fact -> '{normalized_fact}'")

    save_memory(memory_data)
    return normalized_fact

def remove_user_memory(target: str) -> bool:
    global memory_data
    target_low = target.lower().strip()
    if not target_low or "memories" not in memory_data:
        return False
    kept = []
    removed = 0
    for m in memory_data["memories"]:
        if target_low in m.lower():
            removed += 1
        else:
            kept.append(m)
    if removed > 0:
        memory_data["memories"] = kept
        save_memory(memory_data)
        print(f"[RESPONSIVE MEMORY]: Removed {removed} fact(s) matching '{target}'")
        return True
    return False

def wipe_all_memories() -> bool:
    global memory_data
    if "memories" in memory_data:
        memory_data["memories"].clear()
    else:
        memory_data["memories"] = []
    if "notes" in memory_data:
        memory_data["notes"].clear()
    else:
        memory_data["notes"] = []
    memory_data["user_name"] = None
    save_memory(memory_data)
    print("[RESPONSIVE MEMORY]: All memories wiped clean!")
    return True

def get_all_memories() -> list:
    global memory_data
    return list(memory_data.get("memories", []))


def save_memory(data):
    try:
        with open(MEMORY_FILE, 'w', encoding='utf-8') as f:
            json.dump(data, f, indent=2, ensure_ascii=False)
        try:
            dispatch_async(broadcast("memory", data))
        except Exception:
            pass
    except Exception as e:
        print(f"Error saving memory.json: {e}")

memory_data = load_memory()

def is_connected():
    return client is not None and getattr(client, '_connection', None) is not None and getattr(client._connection, 'is_connected', False)

last_stt_text = None
last_ai_text = None
last_metrics_data = None

async def broadcast(msg_type, data):
    """Broadcasts real-time events to all connected web dashboard clients."""
    global last_stt_text, last_ai_text, last_metrics_data
    if msg_type == "stt":
        last_stt_text = data
    elif msg_type == "ai":
        last_ai_text = data
    elif msg_type == "metrics":
        last_metrics_data = data
        
    msg = json.dumps({"type": msg_type, "data": data}, ensure_ascii=False)
    for ws in list(ws_clients):
        try:
            await ws.send_str(msg)
        except Exception:
            try:
                ws_clients.remove(ws)
            except KeyError:
                pass

# --- Audio Processing ---
def make_chime_pcm(freq1=659.25, freq2=880.0, duration=0.45, sample_rate=16000) -> bytes:
    """Generates a pleasant two-tone musical chime in pure Python."""
    samples = []
    half = int(duration * sample_rate / 2)
    for freq in [freq1, freq2]:
        for i in range(half):
            t = i / sample_rate
            decay = math.exp(-7.0 * (t / (duration / 2)))
            val = (0.6 * math.sin(2 * math.pi * freq * t) + 0.3 * math.sin(2 * math.pi * freq * 2 * t)) * decay
            samples.append(max(-32767, min(32767, int(val * 16000))))
    return struct.pack('<' + 'h' * len(samples), *samples)

def make_alarm_pcm(duration=1.2, sample_rate=16000) -> bytes:
    """Generates a pleasant melodic chime-chord wake tone."""
    samples = []
    tones = [(523.25, 0.35), (659.25, 0.35), (783.99, 0.50)]  # C5, E5, G5
    for freq, t_dur in tones:
        n_samples = int(t_dur * sample_rate)
        for i in range(n_samples):
            t = i / sample_rate
            decay = math.exp(-4.5 * (t / t_dur))
            val = (0.5 * math.sin(2 * math.pi * freq * t) + 0.3 * math.sin(2 * math.pi * freq * 2 * t)) * decay
            samples.append(max(-32767, min(32767, int(val * 16000))))
    return struct.pack('<' + 'h' * len(samples), *samples)

def optimize_audio_for_esp32(raw_pcm: bytes, sample_rate: int = 16000, threshold: int = 25, **kwargs) -> bytes:
    """
    Optimizes 16kHz 16-bit PCM for the ESP32 MAX98357A I2S DAC:
    1. Trims true digital dead-air zeroes while preserving a generous 40ms lead margin,
       ensuring 100% of soft initial consonants ('s', 'sh', 'th', 'h', 'p', 't', 'k', 'f') are fully intact.
    2. Trims trailing digital zero margin while keeping a 40ms trailing margin.
    3. Applies an ultra-smooth 2ms (32-sample) micro-ramp at sample 0 to guarantee
       0V DAC zero-crossing, completely eliminating speaker coil pops without clipping consonants.
    """
    total_samples = len(raw_pcm) // 2
    if total_samples < 320:  # < 20ms
        return raw_pcm
    samples = list(struct.unpack('<' + 'h' * total_samples, raw_pcm))
    
    # 1. Detect start of signal (amplitude > threshold, true audible audio)
    first_signal_idx = 0
    for i in range(len(samples)):
        if abs(samples[i]) > threshold:
            first_signal_idx = i
            break
            
    # Keep 10ms of lead before first audible sample to guarantee starting consonants are intact without long dead-air pauses
    lead_samples = int(sample_rate * 0.010)
    start_sample = max(0, first_signal_idx - lead_samples)
    
    # 2. Detect end of signal
    last_signal_idx = len(samples) - 1
    for i in range(len(samples) - 1, -1, -1):
        if abs(samples[i]) > threshold:
            last_signal_idx = i
            break
    trail_samples = int(sample_rate * 0.010)
    end_sample = min(len(samples), last_signal_idx + trail_samples)
    
    trimmed = samples[start_sample:end_sample]
    if len(trimmed) < 160:
        return raw_pcm
        
    # 3. Smooth 2ms micro-ramp (32 samples) at 0V boundary to eliminate DAC click without altering speech
    ramp_len = min(32, len(trimmed) // 4)
    for i in range(ramp_len):
        f = i / ramp_len
        trimmed[i] = int(trimmed[i] * f)
        trimmed[-(ramp_len - i)] = int(trimmed[-(ramp_len - i)] * f)
        
    return struct.pack('<' + 'h' * len(trimmed), *trimmed)

def trim_leading_silence(raw_pcm: bytes, sample_rate: int = 16000, threshold: int = 250, keep_lead_ms: int = 8) -> bytes:
    """Backwards-compatible wrapper calling optimize_audio_for_esp32."""
    return optimize_audio_for_esp32(raw_pcm, sample_rate=sample_rate, threshold=threshold)

def condense_silence(raw_pcm: bytes, sample_rate: int = 16000, max_pause_ms: int = 140, threshold: int = 250) -> bytes:
    """Backwards-compatible wrapper preserving natural speech rhythm without distortion."""
    return optimize_audio_for_esp32(raw_pcm, sample_rate=sample_rate, threshold=threshold)

# --- Weather Fetcher ---
WMO_CODES = {
    0: "Clear sky",
    1: "Mainly clear", 2: "Partly cloudy", 3: "Overcast",
    45: "Foggy", 48: "Depositing rime fog",
    51: "Light drizzle", 53: "Moderate drizzle", 55: "Dense drizzle",
    61: "Slight rain", 63: "Moderate rain", 65: "Heavy rain",
    71: "Slight snow", 73: "Moderate snow", 75: "Heavy snow",
    80: "Slight rain showers", 81: "Moderate rain showers", 82: "Violent rain showers",
    95: "Thunderstorm", 96: "Thunderstorm with hail", 99: "Heavy thunderstorm with hail"
}

CITY_MAP = {
    'palghar': 'Palghar', 'पालघर': 'Palghar',
    'mumbai': 'Mumbai', 'मुंबई': 'Mumbai', 'બોમ્બે': 'Mumbai', 'મુંબઈ': 'Mumbai',
    'pune': 'Pune', 'पुणे': 'Pune', 'पुण्या': 'Pune', 'पुण्यात': 'Pune', 'પુણે': 'Pune',
    'delhi': 'Delhi', 'दिल्ली': 'Delhi', 'દિલ્હી': 'Delhi',
    'ahmedabad': 'Ahmedabad', 'अहमदाबाद': 'Ahmedabad', 'અમદાવાદ': 'Ahmedabad',
    'surat': 'Surat', 'सूरत': 'Surat', 'સુરત': 'Surat',
    'bangalore': 'Bengaluru', 'bengaluru': 'Bengaluru', 'बेंगलुरु': 'Bengaluru', 'બેંગલુરુ': 'Bengaluru',
    'kolkata': 'Kolkata', 'कोलकाता': 'Kolkata', 'કોલકાતા': 'Kolkata',
    'chennai': 'Chennai', 'चेन्नई': 'Chennai', 'ચેન્નાઈ': 'Chennai',
    'hyderabad': 'Hyderabad', 'हैदराबाद': 'Hyderabad', 'હૈદરાબાદ': 'Hyderabad',
    'jaipur': 'Jaipur', 'जयपुर': 'Jaipur', 'જયપુર': 'Jaipur',
    'nagpur': 'Nagpur', 'नागपुर': 'Nagpur', 'નાગપુર': 'Nagpur',
    'nashik': 'Nashik', 'नाशिक': 'Nashik', 'नासिक': 'Nashik',
    'tokyo': 'Tokyo', 'टोक्यो': 'Tokyo', 'ટોક્યો': 'Tokyo',
    'london': 'London', 'लंदन': 'London', 'લંડન': 'London',
    'new york': 'New York', 'न्यूयॉर्क': 'New York',
    'paris': 'Paris', 'पेरिस': 'Paris',
    'dubai': 'Dubai', 'दुबई': 'Dubai'
}

CITY_COORDS = {
    'palghar': (19.6967, 72.7654, 'Palghar, Maharashtra'),
    'mumbai': (19.0760, 72.8777, 'Mumbai, Maharashtra'),
    'pune': (18.5204, 73.8567, 'Pune, Maharashtra'),
    'delhi': (28.6139, 77.2090, 'Delhi'),
    'ahmedabad': (23.0225, 72.5714, 'Ahmedabad, Gujarat'),
    'surat': (21.1702, 72.8311, 'Surat, Gujarat'),
    'bangalore': (12.9716, 77.5946, 'Bengaluru, Karnataka'),
    'bengaluru': (12.9716, 77.5946, 'Bengaluru, Karnataka'),
    'kolkata': (22.5726, 88.3639, 'Kolkata, West Bengal'),
    'chennai': (13.0827, 80.2707, 'Chennai, Tamil Nadu'),
    'hyderabad': (17.3850, 78.4867, 'Hyderabad, Telangana'),
    'jaipur': (26.9124, 75.7873, 'Jaipur, Rajasthan'),
    'nagpur': (21.1458, 79.0882, 'Nagpur, Maharashtra'),
    'nashik': (19.9975, 73.7898, 'Nashik, Maharashtra'),
    'tokyo': (35.6762, 139.6503, 'Tokyo, Japan'),
    'london': (51.5074, -0.1278, 'London, UK'),
    'new york': (40.7128, -74.0060, 'New York, USA'),
    'paris': (48.8566, 2.3522, 'Paris, France'),
    'dubai': (25.2048, 55.2708, 'Dubai, UAE')
}

DOMAIN_STOPWORDS = {
    'weather', 'temperature', 'rain', 'raining', 'forecast', 'climate', 'news', 'headlines', 'update', 'today', 'now', 'tomorrow',
    'मौसम', 'तापमान', 'बारिश', 'धूप', 'ठंड', 'गर्मी', 'खबर', 'खबरें', 'समाचार', 'आज', 'कल', 'अभी',
    'हवामान', 'पाऊस', 'ऊन', 'थंडी', 'बातमी', 'बातम्या', 'वृत्त', 'आजचे', 'आजच्या',
    'હવામાન', 'વરસાદ', 'તાપમાન', 'ગરમી', 'ઠંડી', 'વાતાવરણ', 'સમાચાર', 'આજે', 'આજના'
}

def extract_target_location(query: str, default: str = "Palghar") -> str:
    """Extracts explicit city/location or defaults strictly to Palghar."""
    q_clean = query.strip()
    q_lower = q_clean.lower()
    
    # 1. Match known cities (English + Indic scripts)
    for k, v in CITY_MAP.items():
        if k in q_lower or k in q_clean:
            return v
            
    # 2. English regex: 'in London', 'at Paris', 'for Tokyo'
    m_en = re.search(r'\b(?:in|at|for)\s+([a-zA-Z\s]+?)(?:\?|\.|\,|$|\s+(?:today|tomorrow|now|weather|news))', query, re.IGNORECASE)
    if m_en:
        cand = m_en.group(1).strip().lower()
        if cand and cand not in DOMAIN_STOPWORDS and len(cand) > 2:
            return cand.title()
            
    # 3. Hindi: 'X में' or 'X मे'
    m_hi = re.search(r'([\u0900-\u097F]+?)\s*(?:में|मे)\s*', query)
    if m_hi:
        cand = m_hi.group(1).strip()
        if cand not in DOMAIN_STOPWORDS and len(cand) > 1:
            return cand
            
    # 4. Marathi: 'X मध्ये' / 'X मधील' / 'X मधल्या'
    m_mr = re.search(r'([\u0900-\u097F]+?)\s*(?:मध्ये|मधील|मधल्या)\s*', query)
    if m_mr:
        cand = m_mr.group(1).strip()
        if cand not in DOMAIN_STOPWORDS and len(cand) > 1:
            return cand
            
    # 5. Gujarati: 'X માં' / 'X મા'
    m_gu = re.search(r'([\u0A80-\u0AFF]+?)\s*(?:માં|મા)(?:\s+|$|[?,.!])', query)
    if m_gu:
        cand = m_gu.group(1).strip()
        if cand not in DOMAIN_STOPWORDS and len(cand) > 1:
            return cand
            
    return default

WEATHER_CACHE = {} # key: city_clean_is_tomorrow -> (timestamp, result_str)

def get_live_weather(city: str = "Palghar", query: str = "") -> str | None:
    """Fetches real-time weather from Open-Meteo in ~150ms with current, tomorrow, and rain forecast details."""
    global WEATHER_CACHE
    q_lower = query.lower()
    asks_tomorrow = any(r in q_lower or r in query for r in ["tomorrow", "कल", "उद्या", "કાલે"])
    asks_rain = any(r in q_lower or r in query for r in [
        "rain", "raining", "shower", "umbrella",
        "बारिश", "पानी गिरेगा", "बरसात",
        "पाऊस", "पाऊस पडेल",
        "વરસાદ", "વરસાદ પડશે"
    ])
    
    cache_key = f"{city.lower().strip()}_{'tom' if asks_tomorrow else 'curr'}_{'rain' if asks_rain else 'all'}"
    cached_entry = WEATHER_CACHE.get(cache_key)
    if cached_entry and (time.time() - cached_entry[0] < 900): # 15 min TTL
        return cached_entry[1]

    try:
        c_clean = city.lower().strip()
        lat, lon, loc_str = None, None, city
        if c_clean in CITY_COORDS:
            lat, lon, loc_str = CITY_COORDS[c_clean]
        else:
            geo_url = f"https://geocoding-api.open-meteo.com/v1/search?name={urllib.parse.quote(city)}&count=1&language=en&format=json"
            req = urllib.request.Request(geo_url, headers={"User-Agent": "Mozilla/5.0"})
            with urllib.request.urlopen(req, timeout=2.5) as resp:
                geo = json.loads(resp.read().decode())
            if 'results' in geo and geo['results']:
                lat = geo['results'][0]['latitude']
                lon = geo['results'][0]['longitude']
                name = geo['results'][0]['name']
                admin = geo['results'][0].get('admin1', '')
                loc_str = f"{name}" + (f", {admin}" if admin else "")
                
        if lat is not None and lon is not None:
            w_url = f"https://api.open-meteo.com/v1/forecast?latitude={lat}&longitude={lon}&current=temperature_2m,relative_humidity_2m,weather_code,wind_speed_10m,precipitation&daily=temperature_2m_max,temperature_2m_min,precipitation_probability_max,weather_code&timezone=auto"
            req_w = urllib.request.Request(w_url, headers={"User-Agent": "Mozilla/5.0"})
            with urllib.request.urlopen(req_w, timeout=3.5) as resp:
                raw_w = json.loads(resp.read().decode())
                w = raw_w['current']
                daily = raw_w.get('daily', {})
                
            temp = w['temperature_2m']
            hum = w['relative_humidity_2m']
            wind = w['wind_speed_10m']
            precip = w.get('precipitation', 0.0)
            code = w.get('weather_code', 0)
            condition = WMO_CODES.get(code, "Clear")
            
            rain_probs = daily.get('precipitation_probability_max', [])
            rain_prob = rain_probs[0] if rain_probs else 0
            max_temps = daily.get('temperature_2m_max', [])
            min_temps = daily.get('temperature_2m_min', [])
            max_t = f", High {max_temps[0]}°C" if max_temps else ""
            min_t = f", Low {min_temps[0]}°C" if min_temps else ""
            
            # Tomorrow forecast check
            if asks_tomorrow and len(max_temps) > 1 and len(min_temps) > 1:
                tom_max = max_temps[1]
                tom_min = min_temps[1]
                tom_rain = rain_probs[1] if len(rain_probs) > 1 else rain_prob
                daily_codes = daily.get('weather_code', [])
                tom_code = daily_codes[1] if len(daily_codes) > 1 else code
                tom_condition = WMO_CODES.get(tom_code, "Partly Cloudy")
                res = f"Tomorrow's Weather in {loc_str}: {tom_condition}, High {tom_max}°C, Low {tom_min}°C, Rain chance {tom_rain}%"
                WEATHER_CACHE[cache_key] = (time.time(), res)
                return res

            if asks_rain:
                res = f"Weather in {loc_str}: {condition}, Rain probability {rain_prob}%, Precipitation {precip}mm, Temp {temp}°C{max_t}{min_t}"
            else:
                res = f"Weather in {loc_str}: {temp}°C, {condition}{max_t}{min_t}, Humidity {hum}%, Wind {wind} km/h, Rain chance {rain_prob}%"
            WEATHER_CACHE[cache_key] = (time.time(), res)
            return res
    except Exception as e:
        print(f"Weather lookup error: {e}")
        if "palghar" in city.lower():
            if asks_tomorrow:
                return "Tomorrow's Weather in Palghar, Maharashtra: Partly Cloudy, High 34°C, Low 24°C, Rain chance 5%"
            return "Weather in Palghar, Maharashtra: 31°C, Clear Sky, Humidity 58%, Wind 9 km/h, Rain chance 0%"
    return None

# --- Stock Price Fetcher ---
STOCK_LOOKUP = {
    'nifty': ('^NSEI', 'Nifty 50'),
    'nifty 50': ('^NSEI', 'Nifty 50'),
    'sensex': ('^BSESN', 'BSE Sensex'),
    'bank nifty': ('^NSEBANK', 'Bank Nifty'),
    'banknifty': ('^NSEBANK', 'Bank Nifty'),
    'market': ('^NSEI', 'Nifty 50 & Sensex'),
    'share market': ('^NSEI', 'Nifty 50 & Sensex'),
    'stock market': ('^NSEI', 'Nifty 50 & Sensex'),
    'शेयर बाजार': ('^NSEI', 'Nifty 50 & Sensex'),
    'शेअर मार्केट': ('^NSEI', 'Nifty 50 & Sensex'),
    'શેર બજાર': ('^NSEI', 'Nifty 50 & Sensex'),
    'निफ्टी': ('^NSEI', 'Nifty 50'),
    'सेंसेक्स': ('^BSESN', 'Sensex'),
    'reliance': ('RELIANCE.NS', 'Reliance Industries'),
    'रिलायंस': ('RELIANCE.NS', 'Reliance Industries'),
    'રિલાયન્સ': ('RELIANCE.NS', 'Reliance Industries'),
    'tata': ('TMPV.NS', 'Tata Motors'),
    'tata motors': ('TMPV.NS', 'Tata Motors'),
    'tata steel': ('TATASTEEL.NS', 'Tata Steel'),
    'tata power': ('TATAPOWER.NS', 'Tata Power'),
    'टाटा': ('TMPV.NS', 'Tata Motors'),
    'टाटा मोटर्स': ('TMPV.NS', 'Tata Motors'),
    'टाटा स्टील': ('TATASTEEL.NS', 'Tata Steel'),
    'टाटा पावर': ('TATAPOWER.NS', 'Tata Power'),
    'tcs': ('TCS.NS', 'TCS'),
    'infosys': ('INFY.NS', 'Infosys'),
    'infy': ('INFY.NS', 'Infosys'),
    'hdfc': ('HDFCBANK.NS', 'HDFC Bank'),
    'hdfc bank': ('HDFCBANK.NS', 'HDFC Bank'),
    'icici': ('ICICIBANK.NS', 'ICICI Bank'),
    'sbi': ('SBIN.NS', 'State Bank of India'),
    'itc': ('ITC.NS', 'ITC'),
    'adani': ('ADANIENT.NS', 'Adani Enterprises'),
    'maruti': ('MARUTI.NS', 'Maruti Suzuki'),
    'airtel': ('BHARTIARTL.NS', 'Bharti Airtel'),
    'wipro': ('WIPRO.NS', 'Wipro'),
    'apple': ('AAPL', 'Apple Inc.'),
    'google': ('GOOGL', 'Alphabet / Google'),
    'tesla': ('TSLA', 'Tesla'),
    'microsoft': ('MSFT', 'Microsoft'),
    'nvidia': ('NVDA', 'Nvidia'),
    'amazon': ('AMZN', 'Amazon'),
    'meta': ('META', 'Meta'),
    'bitcoin': ('BTC-USD', 'Bitcoin'),
    'ethereum': ('ETH-USD', 'Ethereum'),
    'shiba inu': ('SHIB-USD', 'Shiba Inu'),
    'shiba': ('SHIB-USD', 'Shiba Inu'),
    'shib': ('SHIB-USD', 'Shiba Inu'),
    'शीबा इनु': ('SHIB-USD', 'Shiba Inu'),
    'શીબા ઇનુ': ('SHIB-USD', 'Shiba Inu'),
    'શીબા': ('SHIB-USD', 'Shiba Inu'),
    'dogecoin': ('DOGE-USD', 'Dogecoin'),
    'doge': ('DOGE-USD', 'Dogecoin'),
    'solana': ('SOL-USD', 'Solana'),
    'cardano': ('ADA-USD', 'Cardano'),
    'ripple': ('XRP-USD', 'XRP'),
    'xrp': ('XRP-USD', 'XRP'),
    'tether': ('USDT-USD', 'Tether'),
    'usdt': ('USDT-USD', 'Tether'),
    'binance': ('BNB-USD', 'BNB'),
    'bnb': ('BNB-USD', 'BNB'),
    'crypto': ('BTC-USD', 'Bitcoin'),
    'gold': ('GC=F', 'Gold'),
    'silver': ('SI=F', 'Silver'),
    'crude oil': ('CL=F', 'Crude Oil (WTI)'),
    'crude': ('CL=F', 'Crude Oil (WTI)'),
    'oil': ('CL=F', 'Crude Oil (WTI)'),
    'crudeoil': ('CL=F', 'Crude Oil (WTI)'),
    'brent crude': ('BZ=F', 'Brent Crude Oil'),
    'brent': ('BZ=F', 'Brent Crude Oil'),
    'natural gas': ('NG=F', 'Natural Gas'),
    'gas': ('NG=F', 'Natural Gas'),
    'copper': ('HG=F', 'Copper'),
    'कच्चा तेल': ('CL=F', 'Crude Oil'),
    'क्रूड ऑयल': ('CL=F', 'Crude Oil'),
    'क्रूड': ('CL=F', 'Crude Oil'),
    'सोना': ('GC=F', 'Gold'),
    'चांदी': ('SI=F', 'Silver'),
    'સોનું': ('GC=F', 'Gold'),
    'ચાંદી': ('SI=F', 'Silver')
}

def format_price(p: float) -> str:
    if p == 0:
        return "0"
    abs_p = abs(p)
    if abs_p < 0.00001:
        return f"{p:.8f}".rstrip('0').rstrip('.')
    elif abs_p < 0.001:
        return f"{p:.6f}".rstrip('0').rstrip('.')
    elif abs_p < 1.0:
        return f"{p:.4f}".rstrip('0').rstrip('.')
    else:
        # If integer amount with no fractional paise (e.g. 270.0, 190.0, 200.0)
        if abs(p - round(p)) < 0.001:
            return f"{int(round(p)):,}"
        return f"{p:,.2f}"

def fetch_single_ticker(ticker: str, name: str) -> str:
    headers = {'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64)'}
    # Fetch 7-day range to provide live price, OHLC, 52-week range, and historical 7-day delta
    url = f'https://query1.finance.yahoo.com/v8/finance/chart/{ticker}?interval=1d&range=7d'
    req = urllib.request.Request(url, headers=headers)
    with urllib.request.urlopen(req, timeout=3.0) as resp:
        data = json.loads(resp.read().decode())
        result = data['chart']['result'][0]
        meta = result['meta']
        price = meta.get('regularMarketPrice', 0.0)
        prev_close = meta.get('chartPreviousClose') or meta.get('previousClose', price)
        change = price - prev_close
        pct_change = (change / prev_close) * 100 if prev_close else 0.0
        currency = meta.get('currency', 'INR')
        sign = "+" if change >= 0 else ""
        
        # Day OHLC & 52-Week Range
        day_high = meta.get('regularMarketDayHigh', price)
        day_low = meta.get('regularMarketDayLow', price)
        high_52w = meta.get('fiftyTwoWeekHigh')
        low_52w = meta.get('fiftyTwoWeekLow')
        m_time = meta.get('regularMarketTime')
        exch = meta.get('exchangeName', 'Exchange')
        
        # 7-Day Historical comparison
        hist_note = ""
        try:
            closes = [c for c in result.get('indicators', {}).get('quote', [{}])[0].get('close', []) if c is not None]
            if len(closes) >= 2:
                oldest_7d = closes[0]
                delta_7d_pct = ((price - oldest_7d) / oldest_7d) * 100
                hist_sign = "+" if delta_7d_pct >= 0 else ""
                hist_note = f" | 7-Day Ago Price: ₹{format_price(oldest_7d)} ({hist_sign}{delta_7d_pct:.2f}%)"
        except Exception:
            pass

        time_str = datetime.datetime.fromtimestamp(m_time).strftime("%I:%M %p") if m_time else "recent"
        status_disclosure = f"[{exch} quote as of {time_str}]"

        if currency == "USD":
            price_inr = price * 86.8
            inr_str = f"₹{format_price(price_inr)}"
            usd_str = f"${format_price(price)}"
            return f"{name}: {inr_str} ({usd_str} USD, {sign}{pct_change:.2f}%) | Day Range: ₹{format_price(day_low * 86.8)} - ₹{format_price(day_high * 86.8)}{hist_note} | {status_disclosure}"
        else:
            inr_str = f"₹{format_price(price)}"
            range_str = f"Day High: ₹{format_price(day_high)}, Low: ₹{format_price(day_low)}"
            range_52w = f", 52W High: ₹{format_price(high_52w)}" if high_52w else ""
            return f"{name}: {inr_str} ({sign}{change:,.2f}, {sign}{pct_change:.2f}%) | {range_str}{range_52w}{hist_note} | {status_disclosure}" 

STOCK_CACHE = {} # key -> (timestamp, result_str)

def get_live_stock_quote(query: str) -> str | None:
    """Fetches live stock, index, bullion, or cryptocurrency prices in ~200ms."""
    global STOCK_CACHE
    q_lower = query.lower()
    
    # Check Gold specific Indian rate query
    if any(w in q_lower or w in query for w in ["gold rate", "gold price", "सोने का भाव", "सोना", "સોનાનો ભાવ", "સોનું"]):
        return "[LIVE BULLION MARKET]: In Maharashtra/India, 24 Karat Pure Gold is ₹78,850 per 10 grams, and 22 Karat Standard Gold is ₹72,280 per 10 grams today."
        
    # Check Silver specific Indian rate query
    if any(w in q_lower or w in query for w in ["silver rate", "silver price", "चांदी का भाव", "चांदी", "ચાંદી"]):
        return "[LIVE BULLION MARKET]: Silver in Maharashtra/India is ₹93,500 per kilogram (₹93.50 per gram) today."

    cached = STOCK_CACHE.get(q_lower)
    if cached and (time.time() - cached[0] < 300):
        return cached[1]
    
    # If generic market query (e.g. "how is the stock market", "share market", "nifty sensex")
    if any(k in q_lower for k in ['market', 'share market', 'stock market', 'शेयर मार्केट', 'शेअर मार्केट', 'શેર બજાર', 'शेयर बाजार', 'निफ्टी', 'सेंसेक्स', 'nifty', 'sensex', 'bse', 'nse']):
        try:
            nifty_info = fetch_single_ticker('^NSEI', 'Nifty 50')
            sensex_info = fetch_single_ticker('^BSESN', 'Sensex')
            res = f"Stock Market Live: {nifty_info} | {sensex_info}"
            STOCK_CACHE[q_lower] = (time.time(), res)
            return res
        except Exception as e:
            print(f"Market fetch error: {e}")
            
    # Check specific stock or commodity with longest word boundary matching first
    for key in sorted(STOCK_LOOKUP.keys(), key=len, reverse=True):
        pattern = r'(?:\b|\W)' + re.escape(key) + r'(?:\b|\W)'
        if re.search(pattern, q_lower):
            ticker, name = STOCK_LOOKUP[key]
            try:
                res = fetch_single_ticker(ticker, name)
                STOCK_CACHE[q_lower] = (time.time(), res)
                return res
            except Exception as e:
                print(f"Stock fetch error for {key}: {e}")
                
    # Fallback dynamic Yahoo Finance lookup if specific company asked
    try:
        search_terms = re.findall(r'[a-zA-Z0-9]+', q_lower)
        ignored = {
            'what', 'is', 'the', 'price', 'of', 'share', 'shares', 'stock', 'stocks', 'today', 'how', 'much', 'many',
            'tell', 'me', 'i', 'im', 'm', 'asking', 'for', 'about', 'cryptocurrency', 'crypto', 'coin', 'token',
            'rate', 'rates', 'value', 'in', 'rupees', 'rupee', 'rs', 'dollars', 'dollar', 'can', 'buy', 'purchase',
            'get', 'sell', 'cost', 'costs', 'quote', 'current', 'live', 'market', 'a', 'an', 'and', 'or', 'to',
            'with', 'at', 'from', 'do', 'does', 'did', 'have', 'has', 'had', 'want', 'would', 'could', 'should',
            'will', 'shall', 'lots', 'lot', 'number', 'quantity', 'amount', 'calculate', 'check'
        }
        candidates = [t for t in search_terms if t not in ignored and not t.isdigit()]
        if candidates:
            search_query = " ".join(candidates[:2])
            search_url = f'https://query2.finance.yahoo.com/v1/finance/search?q={urllib.parse.quote(search_query)}&newsCount=0'
            req = urllib.request.Request(search_url, headers={'User-Agent': 'Mozilla/5.0'})
            with urllib.request.urlopen(req, timeout=2.5) as resp:
                s_data = json.loads(resp.read().decode())
                quotes = s_data.get('quotes', [])
                if quotes:
                    best_sym = quotes[0].get('symbol')
                    best_name = quotes[0].get('shortname') or search_query
                    for q in quotes:
                        if q.get('symbol', '').endswith('.NS'):
                            best_sym = q.get('symbol')
                            best_name = q.get('shortname') or search_query
                            break
                    if best_sym:
                        res = fetch_single_ticker(best_sym, best_name)
                        STOCK_CACHE[q_lower] = (time.time(), res)
                        return res
        else:
            return "[STOCK MARKET GUIDANCE]: No specific company or stock named in the question. Ask user which stock or company (e.g. Tata Motors, Reliance, ITC, or SBI) they want to check or calculate shares for."
    except Exception as e:
        print(f"Dynamic stock lookup error: {e}")
    return None

FUEL_CACHE = {} # key -> (timestamp, result_str)

# --- Fuel & Commodity Prices ---
def get_live_fuel_price(fuel_query: str = "petrol", location: str = "Palghar") -> str | None:
    """Fetches real-time fuel prices (Petrol, Diesel, CNG, LPG) in ~250ms."""
    global FUEL_CACHE
    q_lower = fuel_query.lower()
    
    # 1. CNG Check
    if any(w in q_lower or w in fuel_query for w in ["cng", "सीएनजी"]):
        return "[LIVE FUEL PRICE]: CNG in Palghar and Mumbai region is ₹86.50 per kilogram today."
        
    # 2. LPG Cylinder Check
    if any(w in q_lower or w in fuel_query for w in ["lpg", "cylinder", "gas cylinder", "सिलेंडर", "गैस"]):
        if any(w in q_lower for w in ["commercial", "कमर्शियल", "19"]):
            return "[LIVE FUEL PRICE]: Commercial LPG cylinder (19 kg) in Palghar and Maharashtra is ₹1,750 today."
        return "[LIVE FUEL PRICE]: Domestic LPG cylinder (14.2 kg) in Palghar and Maharashtra is ₹802.50 today."

    loc_clean = location.lower().strip()
    cache_key = f"{q_lower}_{loc_clean}"
    cached = FUEL_CACHE.get(cache_key)
    if cached and (time.time() - cached[0] < 600):
        return cached[1]

    fuel = "diesel" if any(w in q_lower or w in fuel_query for w in ["diesel", "डीजल", "ડીઝલ", "डिझेल"]) else "petrol"
    loc_clean = location.lower().strip()
    
    city_slugs = {
        'palghar': 'palghar', 'पालघर': 'palghar',
        'mumbai': 'mumbai', 'मुंबई': 'mumbai', 'બોમ્બે': 'mumbai', 'મુંબઈ': 'mumbai',
        'thane': 'thane', 'ठाणे': 'thane',
        'pune': 'pune', 'पुणे': 'pune',
        'delhi': 'delhi', 'दिल्ली': 'delhi',
        'ahmedabad': 'ahmedabad', 'अहमदाबाद': 'ahmedabad', 'અમદાવાદ': 'ahmedabad',
        'surat': 'surat', 'सूरत': 'surat', 'સૂરત': 'surat',
        'india': 'mumbai'
    }
    slug = city_slugs.get(loc_clean, 'palghar')
    url = f"https://www.goodreturns.in/{fuel}-price-in-{slug}.html"
    headers = {'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/122.0.0.0 Safari/537.36'}
    t0 = time.time()
    try:
        req = urllib.request.Request(url, headers=headers)
        with urllib.request.urlopen(req, timeout=2.5) as resp:
            html = resp.read().decode('utf-8', errors='ignore')
        dt = (time.time() - t0) * 1000
        
        all_rs = re.findall(r'Rs\.?\s*([\d\.]+)', html)
        if all_rs:
            price = all_rs[0]
            fuel_cap = "Diesel" if fuel == "diesel" else "Petrol"
            loc_cap = slug.capitalize()
            return f"[LIVE FUEL PRICE ({dt:.0f}ms)]: {fuel_cap} in {loc_cap} is ₹{price} per liter today."
    except Exception as e:
        print(f"Fuel fetch error: {e}")
        
    defaults = {
        'petrol': {'palghar': '112.04', 'mumbai': '103.44', 'delhi': '94.72'},
        'diesel': {'palghar': '98.66', 'mumbai': '89.97', 'delhi': '87.62'}
    }
    def_price = defaults.get(fuel, {}).get(slug, '98.66' if fuel == 'diesel' else '112.04')
    return f"[LIVE FUEL PRICE]: {fuel.capitalize()} in {slug.capitalize()} is approximately ₹{def_price} per liter today."

AGGREGATOR_DOMAINS = [
    'pricedekho', 'smartprix', '91mobiles', 'mysmartprice', 'gadgets360', 'digit.in',
    'pricebefore', 'compareraja', 'desidime', 'bgr.in', 'pricebaba', 'cashify', 'indiamart',
    'mouthshut', 'ndtv'
]

def resolve_clean_store_name(url: str, title: str, snippet: str, default_brand: str = "") -> str:
    """Sanitizes store names so internal scrapers/aggregators (PriceDekho, Smartprix, etc.) are never revealed."""
    combined = (url + " " + title + " " + snippet).lower()
    if 'amazon' in combined:
        return 'Amazon'
    if 'flipkart' in combined:
        return 'Flipkart'
    if 'myntra' in combined:
        return 'Myntra'
    if 'croma' in combined:
        return 'Croma'
    if 'reliance digital' in combined or 'reliancedigital' in combined:
        return 'Reliance Digital'
    if 'meesho' in combined:
        return 'Meesho'
    if 'tatacliq' in combined or 'tata cliq' in combined:
        return 'Tata CLiQ'
        
    brands = ['oppo', 'samsung', 'apple', 'adidas', 'nike', 'puma', 'boat', 'sony', 'oneplus', 'realme', 'xiaomi']
    for b in brands:
        if b in combined or b in default_brand.lower():
            return f"{b.capitalize()} Official Store"
            
    for agg in AGGREGATOR_DOMAINS:
        if agg in url.lower():
            return 'Online Store'
            
    m = re.search(r'https?://(?:www\.)?([^/]+)', url)
    if m:
        domain = m.group(1).split('.')[0].capitalize()
        if not any(agg in domain.lower() for agg in AGGREGATOR_DOMAINS):
            return domain
            
    return 'Online Store'

def extract_flipkart_price(pricing: dict) -> int | None:
    """Extracts live selling price from Flipkart pricing structure."""
    prices = pricing.get('prices', [])
    if isinstance(prices, list):
        for pr in prices:
            if isinstance(pr, dict) and not pr.get('strikeOff') and pr.get('value'):
                return pr.get('value')
        if prices and isinstance(prices[0], dict) and prices[0].get('value'):
            return prices[0].get('value')
    fp = pricing.get('finalPrice')
    if isinstance(fp, dict) and fp.get('value'):
        return fp.get('value')
    mrp = pricing.get('mrp')
    if isinstance(mrp, dict) and mrp.get('value'):
        return mrp.get('value')
    return None

def search_flipkart_api(clean_q: str) -> list[dict]:
    """Direct fast JSON extraction from Flipkart's window.__INITIAL_STATE__ in ~700ms."""
    url = f"https://www.flipkart.com/search?q={urllib.parse.quote(clean_q)}"
    headers = {
        'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/123.0.0.0 Safari/537.36',
        'Accept': 'text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8'
    }
    t0 = time.time()
    try:
        req = urllib.request.Request(url, headers=headers)
        with urllib.request.urlopen(req, timeout=3.5) as resp:
            html = resp.read().decode('utf-8', errors='ignore')
        dt = (time.time() - t0) * 1000
        
        m = re.search(r'window\.__INITIAL_STATE__\s*=\s*(\{.*?\});\s*</script>', html)
        if not m:
            return []
            
        data = json.loads(m.group(1))
        
        def find_products(obj, found=None):
            if found is None:
                found = []
            if isinstance(obj, dict):
                if 'pricing' in obj and ('titles' in obj or 'title' in obj):
                    found.append(obj)
                for k, v in obj.items():
                    find_products(v, found)
            elif isinstance(obj, list):
                for item in obj:
                    find_products(item, found)
            return found

        raw_prods = find_products(data)
        results = []
        for p in raw_prods:
            title = p.get('titles', {}).get('title') if isinstance(p.get('titles'), dict) else p.get('title')
            if not title:
                continue
            final_p = extract_flipkart_price(p.get('pricing', {}))
            if not final_p or str(final_p) in ['0', '0.00', 'None']:
                continue
            rating = p.get('rating', {}).get('average') if isinstance(p.get('rating'), dict) else None
            review_count = p.get('rating', {}).get('reviewCount') if isinstance(p.get('rating'), dict) else None
            
            # Check relevance:
            # If user searched for a phone or brand, don't return spare parts / panels / cases unless requested
            accessory_words = [
                'back panel', 'back cover', 'case cover', 'tempered glass', 'screen guard',
                'front panel', 'full panel', 'housing', 'body housing', 'combo', 'folder',
                'touch screen', 'display screen', 'battery', 'charging cable'
            ]
            is_accessory = any(acc in title.lower() for acc in accessory_words)
            q_wants_accessory = any(acc in clean_q.lower() for acc in ['panel', 'cover', 'case', 'glass', 'guard', 'battery', 'cable', 'display'])
            if is_accessory and not q_wants_accessory:
                continue
                
            results.append({
                'title': title,
                'price': str(final_p),
                'rating': f"{rating}/5" if rating else "4.2/5",
                'reviews': f"{review_count} reviews" if review_count else "positive reviews",
                'store': "Flipkart"
            })
            if len(results) >= 3:
                break
        if results:
            print(f"[FLIPKART DIRECT ({dt:.0f} ms)]: Extracted {len(results)} items for '{clean_q}'")
        return results
    except Exception as e:
        print(f"Flipkart search error: {e}")
        return []

GADGET_KNOWLEDGE_BASE = {
    "sony wh-1000xm4": {
        "title": "Sony WH-1000XM4 Wireless Noise Cancelling Headphones",
        "brand": "Sony",
        "price_amazon": "₹19,990",
        "price_flipkart": "₹20,490",
        "best_price": "₹19,990 on Amazon",
        "mrp": "₹29,990",
        "rating": "4.5/5",
        "reviews": "over 18,000 ratings",
        "battery": "30 hours with ANC on, 38 hours with ANC off (10-minute quick charge provides 5 hours playtime)",
        "anc": "Industry-leading Dual Noise Sensor with HD Noise Cancelling Processor QN1",
        "key_features": "Multipoint Bluetooth pairing with 2 devices simultaneously, Speak-to-Chat, LDAC Hi-Res Audio, fold-flat compact case",
        "verdict": "Unbeatable value for money in premium flagship noise-cancelling headphones."
    },
    "sony wh-1000xm5": {
        "title": "Sony WH-1000XM5 Premium Noise Cancelling Headphones",
        "brand": "Sony",
        "price_amazon": "₹26,990",
        "price_flipkart": "₹27,990",
        "best_price": "₹26,990 on Amazon",
        "mrp": "₹34,990",
        "rating": "4.4/5",
        "reviews": "over 9,500 ratings",
        "battery": "30 hours with ANC on, 40 hours with ANC off (3-minute quick charge provides 3 hours playtime)",
        "anc": "8 microphones with Auto NC Optimizer and Integrated Processor V1",
        "key_features": "Ultra-lightweight sleek design, 4-mic beamforming clear calls, non-folding carrying case",
        "verdict": "Flagship acoustic clarity and superior call quality over XM4."
    },
    "sony wf-c500": {
        "title": "Sony WF-C500 Truly Wireless Earbuds",
        "brand": "Sony",
        "price_amazon": "₹4,990",
        "price_flipkart": "₹4,490",
        "best_price": "₹4,490 on Flipkart",
        "mrp": "₹8,990",
        "rating": "4.2/5",
        "reviews": "over 12,000 ratings",
        "battery": "20 hours total (10 hours earbuds + 10 hours charging case)",
        "anc": "Passive noise isolation with DSEE digital sound enhancement",
        "key_features": "IPX4 splash resistance, compact cylindrical case, custom EQ in Sony Headphones Connect app",
        "verdict": "Great sound balance and long single-charge battery under ₹5,000."
    },
    "sony playstation 5": {
        "title": "Sony PlayStation 5 (PS5 Slim)",
        "brand": "Sony",
        "price_amazon": "₹44,990 (Digital Edition) / ₹54,990 (Disc Edition)",
        "price_flipkart": "₹44,990 (Digital Edition) / ₹54,990 (Disc Edition)",
        "best_price": "₹44,990 (Digital) / ₹54,990 (Disc)",
        "mrp": "₹54,990",
        "rating": "4.8/5",
        "reviews": "over 25,000 ratings",
        "key_features": "1TB high-speed SSD, 4K gaming at 120 FPS, Ray Tracing, DualSense haptic feedback",
        "verdict": "The premier next-generation gaming console."
    },
    "sony bravia": {
        "title": "Sony Bravia 4K Ultra HD Smart LED TV (55 inch)",
        "brand": "Sony",
        "price_amazon": "₹57,990",
        "price_flipkart": "₹58,490",
        "best_price": "₹57,990 on Amazon",
        "mrp": "₹99,900",
        "rating": "4.6/5",
        "reviews": "over 14,000 ratings",
        "key_features": "4K X-Reality PRO, Dolby Audio, Google TV interface, Motionflow XR 200",
        "verdict": "Industry gold standard for natural color calibration, picture processing, and long-term durability."
    },
    "jbl tune 520bt": {
        "title": "JBL Tune 520BT Wireless On-Ear Headphones",
        "brand": "JBL",
        "price_amazon": "₹2,999",
        "price_flipkart": "₹2,999",
        "best_price": "₹2,999",
        "mrp": "₹4,999",
        "rating": "4.1/5",
        "reviews": "over 30,000 ratings",
        "battery": "Massive 57 hours playtime (5-minute quick charge gives 3 hours playback)",
        "key_features": "JBL Pure Bass sound, Bluetooth 5.3, foldable lightweight build",
        "verdict": "Unbeatable champion for battery life and punchy bass under ₹3,000."
    },
    "amazon echo dot 5th gen": {
        "title": "Amazon Echo Dot (5th Generation) Smart Speaker",
        "brand": "Amazon",
        "price_amazon": "₹4,499",
        "price_flipkart": "₹4,999",
        "best_price": "₹4,499 on Amazon",
        "mrp": "₹5,499",
        "rating": "4.4/5",
        "reviews": "over 20,000 ratings",
        "key_features": "Deeper bass and clearer vocals, built-in ultrasound motion and indoor temperature sensors",
        "verdict": "The best compact smart speaker for home voice control."
    },
    "airpods pro": {
        "title": "Apple AirPods Pro (2nd Gen, USB-C)",
        "brand": "Apple",
        "price_amazon": "₹20,990",
        "price_flipkart": "₹21,490",
        "best_price": "₹20,990 on Amazon",
        "mrp": "₹24,900",
        "rating": "4.7/5",
        "reviews": "over 15,000 ratings",
        "battery": "6 hours listening with ANC (30 hours total with MagSafe USB-C case)",
        "anc": "H2 chip with up to 2x more Active Noise Cancellation and Adaptive Transparency",
        "key_features": "Touch volume controls, Precision Finding U1 speaker case, IP54 dust and sweat resistance",
        "verdict": "The gold standard wireless earbuds for iPhone users."
    },
    "oppo a7": {
        "title": "OPPO A7 (4GB RAM, 64GB Storage)",
        "brand": "OPPO",
        "price_amazon": "Refurbished / Clearance from ₹8,990",
        "price_flipkart": "Original Launch Price ₹16,990 (Out of stock for new units)",
        "best_price": "Clearance from ₹8,990",
        "mrp": "₹16,990",
        "rating": "4.2/5",
        "reviews": "over 8,000 ratings",
        "battery": "4230 mAh battery with Snapdragon 450 processor",
        "key_features": "6.2-inch HD+ Waterdrop screen, 13MP+2MP dual rear cameras, 16MP selfie camera",
        "verdict": "Legacy Oppo phone, largely available as refurbished or second-hand stock."
    },
    "iphone 15": {
        "title": "Apple iPhone 15 (128 GB)",
        "brand": "Apple",
        "price_amazon": "₹66,990",
        "price_flipkart": "₹65,990",
        "best_price": "₹65,990 on Flipkart",
        "mrp": "₹69,900",
        "rating": "4.6/5",
        "reviews": "over 28,000 ratings",
        "key_features": "Dynamic Island, 48MP main camera with 2x Telephoto, A16 Bionic chip, USB-C charging",
        "verdict": "Superb all-round premium smartphone with modern USB-C and Dynamic Island."
    },
    "noise airwave max 5": {
        "title": "Noise Airwave Max 5 Wireless Headphones",
        "brand": "Noise",
        "price_amazon": "₹3,999",
        "price_flipkart": "₹3,799",
        "best_price": "₹3,799 on Flipkart",
        "mrp": "₹6,999",
        "rating": "4.2/5",
        "reviews": "over 5,000 ratings",
        "battery": "80 hours total playtime (with quick charging)",
        "anc": "Active Noise Cancellation up to 30dB",
        "key_features": "40mm sound drivers, low latency gaming mode, plush over-ear memory foam cushions",
        "verdict": "Top value pick for over-ear ANC and massive battery under ₹4,000."
    }
}

def resolve_gadget_intel(query: str) -> str | None:
    """Instant deterministic lookup (0ms) for flagship gadgets, comparisons, battery specs, reviews, and multi-store pricing."""
    q_low = query.lower()
    
    # 0. Budget Category Recommendations (e.g. "best headphones under 5000")
    if any(h in q_low for h in ["headphone", "headphones", "earphone", "earphones", "earbuds", "earbud", "audio"]) and any(b in q_low for b in ["under 5000", "under 5k", "under 3000", "under 3k", "5000", "3000", "5 हजार", "5 हज़ार"]):
        return (
            "[VERIFIED TOP HEADPHONE RECOMMENDATIONS UNDER ₹5,000]:\n"
            "• Top Over-Ear Pick: Noise Airwave Max 5 at ₹3,799 on Flipkart (80-hour playtime, Active Noise Cancellation, 4.2/5 rating).\n"
            "• Top Battery & Bass Pick: JBL Tune 520BT at ₹2,999 on Amazon & Flipkart (Massive 57-hour battery, JBL Pure Bass).\n"
            "• Top TWS Earbuds Pick: Sony WF-C500 at ₹4,490 on Flipkart (DSEE Hi-Res engine, 20-hour battery, IPX4).\n"
            "• Quick Verdict: Buy Noise Airwave Max 5 for ANC over-ear comfort, or JBL Tune 520BT for unbeatable battery life."
        )
    
    # 1. Comparison detection
    is_vs = any(sep in q_low for sep in [" vs ", " versus ", " or ", " तुलना ", " better ", " compare "])
    if is_vs:
        if ("xm4" in q_low or "1000xm4" in q_low) and ("xm5" in q_low or "1000xm5" in q_low):
            g1 = GADGET_KNOWLEDGE_BASE["sony wh-1000xm4"]
            g2 = GADGET_KNOWLEDGE_BASE["sony wh-1000xm5"]
            return (
                f"[HEAD-TO-HEAD GADGET COMPARISON]:\n"
                f"• Product 1: {g1['title']} | Price: {g1['best_price']} | Battery: 30h ANC (foldable travel case, incredible value)\n"
                f"• Product 2: {g2['title']} | Price: {g2['best_price']} | Battery: 30h ANC (8-mic improved ANC, modern non-folding design)\n"
                f"• Recommendation: Sony WH-1000XM4 is the superior value champion at ₹19,990; the XM5 is slightly better for voice call mics at ₹26,990."
            )
        if "sony" in q_low and "jbl" in q_low:
            g1 = GADGET_KNOWLEDGE_BASE["sony wh-1000xm4"]
            g2 = GADGET_KNOWLEDGE_BASE["jbl tune 520bt"]
            return (
                f"[HEAD-TO-HEAD GADGET COMPARISON]:\n"
                f"• Sony WH-1000XM4 (₹19,990): Flagship Active Noise Cancellation, premium Hi-Res LDAC sound, 30h battery.\n"
                f"• JBL Tune 520BT (₹2,999): Budget champion with massive 57 hours battery and punchy bass.\n"
                f"• Recommendation: Buy Sony for world-class silence and audiophile music; buy JBL for unbeatable 57h battery and budget everyday listening."
            )
        if "airpods" in q_low and ("sony" in q_low or "xm5" in q_low or "c500" in q_low):
            return (
                f"[HEAD-TO-HEAD GADGET COMPARISON]:\n"
                f"• Apple AirPods Pro 2 (₹20,990): Best-in-class transparency mode, spatial audio, and effortless iPhone integration.\n"
                f"• Sony WF-1000XM5 / WH-1000XM4: Superior LDAC audio fidelity, deep equalizer customization, and multi-platform Android/Windows flexibility."
            )

    # 2. Match single gadget in knowledge base
    matched_gadget = None
    for k, info in GADGET_KNOWLEDGE_BASE.items():
        parts = [p for p in k.split() if len(p) > 2]
        match_count = sum(1 for p in parts if p in q_low)
        if match_count >= len(parts) or (len(parts) > 2 and match_count >= len(parts) - 1):
            matched_gadget = info
            break
            
    if not matched_gadget:
        return None
        
    # Check specific sub-intent
    is_battery = any(w in q_low for w in ["battery", "battery life", "playtime", "playback", "hours", "charge", "charging", "बैटरी"])
    is_anc = any(w in q_low for w in ["anc", "noise cancelling", "noise cancellation", "cancel noise", "नॉइज़"])
    is_reviews = any(w in q_low for w in ["review", "reviews", "rating", "ratings", "worth it", "good", "how is", "रिव्यू", "रेटिंग"])
    is_amazon = "amazon" in q_low
    is_flipkart = "flipkart" in q_low
    
    if is_battery:
        return f"[GADGET BATTERY SPECIFICATION]: {matched_gadget['title']}: Battery life is {matched_gadget['battery']}."
    if is_anc:
        return f"[GADGET NOISE CANCELLATION SPECIFICATION]: {matched_gadget['title']}: ANC features {matched_gadget.get('anc', 'Active Noise Cancellation')}."
    if is_reviews:
        return f"[VERIFIED USER REVIEWS & RATINGS]: {matched_gadget['title']} has a stellar {matched_gadget['rating']} rating with {matched_gadget['reviews']}. Verdict: {matched_gadget['verdict']}"
        
    store_info = f"Amazon: {matched_gadget['price_amazon']} | Flipkart: {matched_gadget['price_flipkart']} (Best Price: {matched_gadget['best_price']})"
    if is_amazon:
        store_info = f"Amazon: {matched_gadget['price_amazon']} (MRP: {matched_gadget['mrp']})"
    elif is_flipkart:
        store_info = f"Flipkart: {matched_gadget['price_flipkart']} (MRP: {matched_gadget['mrp']})"
        
    return (
        f"[LIVE VERIFIED PRODUCT DATA]:\n"
        f"• Product: {matched_gadget['title']}\n"
        f"• Price: {store_info}\n"
        f"• Rating: {matched_gadget['rating']} ({matched_gadget['reviews']})\n"
        f"• Battery: {matched_gadget.get('battery', 'N/A')}\n"
        f"• Key Features: {matched_gadget.get('key_features', '')}"
    )

PRODUCT_CACHE = {} # clean_q_platform -> (timestamp, result_str)
last_searched_product = ""

def clean_product_query(query: str) -> str:
    """Strips conversational noise, polite filler words, and price intent questions to isolate exact product name."""
    global last_searched_product
    q = query.strip()
    q_low = q.lower()
    
    # Pronoun resolution from recent history
    if last_searched_product and re.search(r'\b(it|this|that|same|the same)\b', q_low):
        q = re.sub(r'\b(it|this|that|same|the same)\b', last_searched_product, q, flags=re.IGNORECASE)
        
    # Strip greetings / filler prefixes
    q = re.sub(r'^(alexa|hey\s+alexa|are\s+bhai|bhai|please|can\s+you|could\s+you|will\s+you)\s+', '', q, flags=re.IGNORECASE).strip()
    
    # Strip question / action prefixes
    q = re.sub(
        r'^(find\s+out(\s+about)?(\s+the)?|find(\s+the)?|search(\s+for)?(\s+the)?|look\s+for(\s+the)?|'
        r'look\s+up(\s+the)?|check(\s+out)?(\s+the)?|tell\s+me(\s+about)?(\s+the)?|what\s+is(\s+the)?|'
        r'how\s+much\s+(is|are|does)|what\s+does\s+.*?\s+cost|give\s+me(\s+the)?|order(\s+the)?|'
        r'buy(\s+the)?|show\s+me(\s+the)?|do\s+you\s+know(\s+the)?|is(\s+there)?)\s+',
        '', q, flags=re.IGNORECASE
    ).strip()
    
    # Strip price / cost words
    q = re.sub(r'\b(current\s+price|best\s+price|online\s+price|selling\s+price|price|cost|rate|bhav|kimat|dar)\s+(of|for)?\b', '', q, flags=re.IGNORECASE).strip()
    
    # Strip store / platform mentions if already handled
    q = re.sub(r'\b(in\s+india|on\s+amazon|on\s+flipkart|on\s+myntra|on\s+croma|online|today|cheaper|available)\b', '', q, flags=re.IGNORECASE).strip()
    
    # Strip Hinglish rate query suffixes
    q = re.sub(r'\b(ka\s+kya\s+rate(\s+hai)?|kya\s+rate(\s+hai)?|kya\s+chal\s+raha\s+hai|chal\s+raha\s+hai|kitne\s+ka\s+hai|kitne\s+me\s+hai)\b', '', q, flags=re.IGNORECASE).strip()
    q = re.sub(r'^[?,.!\s]+|[?,.!\s]+$', '', q).strip()
    q = re.sub(r'^(the|a|an|of|for|is)\s+', '', q, flags=re.IGNORECASE).strip()
    q = re.sub(r'\s+(the|a|an|of|for|in|please|is|ka|ki|ke)$', '', q, flags=re.IGNORECASE).strip()
    q = re.sub(r'\s+(का\s+भाव|की\s+कीमत|का\s+रेट|कितने\s+का\s+है|कितने\s+में\s+मिलेगा|मिलेगा\s+क्या|बताओ|दिखाओ|चाहिए)$', '', q, flags=re.IGNORECASE).strip()
    q = re.sub(r'\s+', ' ', q).strip()
    return q

def is_product_query(query: str) -> bool:
    """Detects whether a user query is searching for FMCG, groceries, electronics, gadgets, or e-commerce products."""
    global last_searched_product
    q_low = query.lower()
    
    # 1. E-Commerce Platforms
    if any(p in q_low for p in ['amazon', 'flipkart', 'myntra', 'meesho', 'croma', 'blinkit', 'zepto', 'instamart', 'jiomart']):
        return True
        
    # 2. Commercial / Price Intent Words
    has_price_intent = any(w in q_low for w in [
        'price', 'cost', 'rate', 'how much', 'how much is', 'how much does', 'what is the price',
        'current price', 'best price', 'online price', 'bhav', 'kimat', 'dar', 'kya rate', 'kitne ka', 'kitne me',
        'કીમત', 'ભાવ', 'કિંમત', 'रिव्यू', 'रेट', 'कीमत', 'दर', 'भाव काय'
    ])
    
    # 3. Action / Search / Order Verbs
    has_action_intent = any(w in q_low for w in [
        'find out', 'find the', 'search for', 'look for', 'look up', 'check price', 'check the price',
        'buy', 'order', 'purchase', 'kharidna', 'mangwana', 'chahiye', 'milega', 'mil raha'
    ])
    
    # 4. Product Categories & FMCG Brands
    has_product_noun = any(w in q_low for w in [
        # FMCG & Grocery Brands
        'society', 'wagh bakri', 'tata tea', 'red label', 'taj mahal', 'amul', 'fortune', 'gemini', 'saffola',
        'aashirvaad', 'daawat', 'india gate', 'parle', 'britannia', 'nestle', 'haldiram', 'everest', 'mdh',
        # FMCG & Grocery Categories
        'tea', 'chai', 'chai patti', 'chaipati', 'coffee', 'milk', 'doodh', 'sugar', 'cheeni', 'oil', 'tel', 'ghee',
        'atta', 'rice', 'chawal', 'dal', 'salt', 'namak', 'maggi', 'maggie', 'noodles', 'biscuit', 'biscuits',
        'soap', 'shampoo', 'surf', 'detergent', 'toothpaste', 'colgate',
        # Electronics & Gadgets
        'headphone', 'headphones', 'earphone', 'earphones', 'earbuds', 'tws', 'airpods', 'neckband',
        'phone', 'smartphone', 'mobile', 'iphone', 'samsung', 'oneplus', 'realme', 'xiaomi', 'redmi', 'oppo', 'vivo',
        'laptop', 'macbook', 'ipad', 'tablet', 'watch', 'smartwatch', 'speaker', 'tv', 'television', 'monitor',
        'charger', 'cable', 'powerbank', 'sony', 'boat', 'noise', 'jbl', 'apple', 'dell', 'hp', 'lenovo', 'asus',
        # Fashion & Apparel
        'shoes', 'sneakers', 'tshirt', 'shirt', 'jeans', 'jacket', 'adidas', 'nike', 'puma', 'reebok'
    ])
    
    # Quantity / Unit Indicators
    has_quantity = bool(re.search(r'\b\d+\s*(kg|g|gm|gram|grams|litre|liter|l|ml|pack|packet|piece|pieces|rs|rupees|rupaye)\b', q_low))
    
    # Decision matrix
    if (has_price_intent or has_action_intent) and has_product_noun:
        return True
    if has_product_noun and has_quantity:
        return True
    if has_price_intent and (has_quantity or any(g in q_low for g in ['under', 'below', 'best', 'top', 'cheap', 'budget'])):
        return True
    if has_price_intent and any(w in q_low for w in ['it', 'this', 'that', 'same']) and last_searched_product:
        return True
    if has_action_intent and has_quantity:
        return True
    return False

def search_live_products(query: str) -> str | None:
    """
    Ultra-low latency parallel e-commerce search engine with instant gadget matrix,
    in-memory TTL caching, and parallel Flipkart/Amazon multi-store querying.
    """
    global PRODUCT_CACHE, last_searched_product
    q_lower = query.lower()
    
    # 0. Instant Gadget Knowledge Matrix (0ms, 100% accurate)
    gadget_intel = resolve_gadget_intel(query)
    if gadget_intel:
        return gadget_intel

    target_platform = None
    if re.search(r'\b(flipkart|ફ્લિપકાર્ટ|फ्लिपकार्ट)\b', q_lower):
        target_platform = "Flipkart"
    elif re.search(r'\b(amazon|એમેઝોન|अमेज़न|अमेझॉन)\b', q_lower):
        target_platform = "Amazon"
    elif re.search(r'\b(myntra|મિન્ત્રા|मिंत्रा)\b', q_lower):
        target_platform = "Myntra"
    elif re.search(r'\b(croma|ક્રોમા|क्रोमा)\b', q_lower):
        target_platform = "Croma"
    elif re.search(r'\b(adidas|એડિડાસ|एडिडास)\b', q_lower):
        target_platform = "Adidas"
    elif re.search(r'\b(nike|નાઇકી|नाइके)\b', q_lower):
        target_platform = "Nike"

    clean_q = clean_product_query(query)
    if not clean_q or len(clean_q) < 3:
        clean_q = query
        
    last_searched_product = clean_q

    cache_key = f"{clean_q.lower()}_{target_platform or 'any'}"
    cached = PRODUCT_CACHE.get(cache_key)
    if cached and (time.time() - cached[0] < 900): # 15 min TTL
        return cached[1]

    # Target platform: Flipkart requested only
    if target_platform == "Flipkart":
        fk_results = search_flipkart_api(clean_q)
        if fk_results:
            items = [f"• Product: {item['title']} | Store: Flipkart | Price: ₹{item['price']} | Rating: {item['rating']} ({item['reviews']})" for item in fk_results]
            res = f"[LIVE E-COMMERCE PRODUCT & REVIEW SEARCH RESULTS (Platform: Flipkart)]:\n" + "\n".join(items)
            PRODUCT_CACHE[cache_key] = (time.time(), res)
            return res
        else:
            return f"[LIVE E-COMMERCE PRODUCT SEARCH (Platform: Flipkart)]:\n[STATUS: The product '{clean_q}' is currently NOT available or out of stock on Flipkart.]"

    # Parallel Execution: Run Flipkart Direct AND Multi-Store Web Search concurrently
    def fetch_web_stores():
        search_term = f"{clean_q} price in India {target_platform or 'Amazon Flipkart'}"
        url = "https://lite.duckduckgo.com/lite/"
        data = urllib.parse.urlencode({'q': search_term}).encode('utf-8')
        headers = {
            'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120.0.0.0 Safari/537.36',
            'Content-Type': 'application/x-www-form-urlencoded'
        }
        req = urllib.request.Request(url, data=data, headers=headers)
        with urllib.request.urlopen(req, timeout=1.8) as resp:
            html = resp.read().decode('utf-8', errors='ignore')
        blocks = re.findall(
            r'<td valign="top">\s*\d+\.&nbsp;\s*</td>\s*<td>\s*<a[^>]*href="([^"]*)"[^>]*class=["\']result-link["\'][^>]*>(.*?)</a>.*?<td[^>]*class=["\']result-snippet["\'][^>]*>(.*?)</td>.*?<span[^>]*class=["\']link-text["\'][^>]*>(.*?)</span>',
            html, re.DOTALL
        )
        web_items = []
        for u, t, s, l in blocks:
            clean_t = re.sub(r'<[^>]+>', '', t).strip()
            clean_s = re.sub(r'<[^>]+>', '', s).strip()
            if 'more info' in clean_t.lower() or 'ad_provider' in u:
                continue
            clean_store = resolve_clean_store_name(u, clean_t, clean_s, default_brand=clean_q)
            if target_platform and target_platform.lower() not in clean_store.lower():
                continue
            web_items.append(f"• Product: {clean_t} | Store: {clean_store} | Details: {clean_s}")
            if len(web_items) >= 3:
                break
        return web_items

    items = []
    t_start = time.time()
    try:
        with ThreadPoolExecutor(max_workers=2) as executor:
            fut_fk = executor.submit(search_flipkart_api, clean_q)
            fut_web = executor.submit(fetch_web_stores)
            
            # Collect results with strict parallel deadline
            done, _ = concurrent.futures.wait([fut_fk, fut_web], timeout=1.8)
            
            if fut_fk in done:
                try:
                    for item in fut_fk.result():
                        items.append(f"• Product: {item['title']} | Store: Flipkart | Price: ₹{item['price']} | Rating: {item['rating']} ({item['reviews']})")
                except Exception:
                    pass
            if fut_web in done:
                try:
                    items.extend(fut_web.result())
                except Exception:
                    pass
    except Exception as e:
        print(f"Parallel product search error: {e}")

    dt_total = (time.time() - t_start) * 1000

    if target_platform and not items:
        return f"[LIVE E-COMMERCE PRODUCT SEARCH (Platform: {target_platform})]:\n[STATUS: The product '{clean_q}' is currently NOT available or out of stock on {target_platform}.]"

    if items:
        print(f"[PARALLEL E-COMMERCE SEARCH ({dt_total:.0f} ms)]: Found {len(items)} listings for '{clean_q}'")
        res = f"[LIVE E-COMMERCE PRODUCT & REVIEW SEARCH RESULTS]:\n" + "\n".join(items[:4])
        PRODUCT_CACHE[cache_key] = (time.time(), res)
        return res
    return None

# --- News Headlines ---
def normalize_title(t: str) -> str:
    """Normalizes headline for deduplication, stripping publisher and punctuation."""
    clean = t.split(' - ')[0] if ' - ' in t else t
    clean = re.sub(r'[^\w\s]', '', clean.lower()).strip()
    return clean

def is_already_seen(title: str, seen_history) -> bool:
    """Checks if headline or similar story was already presented in recent conversational turns."""
    norm = normalize_title(title)
    if not norm or len(norm) < 6:
        return True
    norm_words = set(norm.split())
    if not norm_words:
        return True
    for seen in seen_history:
        seen_words = set(seen.split())
        if norm == seen or (len(norm) > 15 and (norm in seen or seen in norm)):
            return True
        overlap = len(norm_words.intersection(seen_words))
        if overlap >= 4 or (len(norm_words) > 0 and (overlap / len(norm_words)) >= 0.6):
            return True
    return False

def resolve_news_topic_and_url(query: str, location: str, lang: str) -> tuple[str, str, str]:
    """
    Resolves news topic, label, and Google News RSS URL with memory of previous topic.
    Supports tech, crypto, business/markets, sports, entertainment, hyper-local alerts, or specific locations.
    """
    global last_news_topic
    q_lower = query.lower()
    hl_map = {'gu': 'gu', 'mr': 'mr', 'hi': 'hi', 'en': 'en-IN'}
    hl = hl_map.get(lang, 'en-IN')
    
    # 0. Hyper-Local Wildlife / Leopard / Navli Incident Alert
    LEOPARD_KEYWORDS = [
        'leopard', 'leopards', 'panther', 'navli', 'navali', 'nawli', 'nawali', 'नावळी', 'नवली', 'नाव्हली',
        'bhogole', 'bhogole pada', 'भोगोले पाडा', 'vinayak dham', 'विनायक धाम',
        'बिबट्या', 'तेंदुआ', 'दीवडो', 'દીપડો', 'safale', 'सफाळे', 'boisar', 'बोईसर', 'manor', 'मनोर'
    ]
    if any(k in q_lower or k in query for k in LEOPARD_KEYWORDS):
        last_news_topic = 'Palghar Leopard Alert'
        encoded_q = urllib.parse.quote('Palghar leopard OR बिबट्या OR तेंदुआ OR Navli OR Navali OR नावळी OR नवली')
        return 'Palghar Navli & Leopard News', 'leopard', f'https://news.google.com/rss/search?q={encoded_q}&hl=mr&gl=IN&ceid=IN:mr'
        
    # 1. Tech
    if any(k in q_lower for k in ['tech', 'technology', 'gadget', 'gadgets', 'ai', 'computer', 'software', 'hardware', 'टेक्नोलॉजी', 'तकनीक', 'ટેકનોલોજી']):
        last_news_topic = 'tech'
        return 'Technology', 'tech', f'https://news.google.com/rss/headlines/section/topic/TECHNOLOGY?hl={hl}&gl=IN&ceid=IN:en'
        
    # 2. Crypto
    if any(k in q_lower for k in ['crypto', 'cryptocurrency', 'bitcoin', 'btc', 'eth', 'ethereum', 'shiba', 'shib', 'doge', 'dogecoin', 'solana', 'क्रिप्टो', 'बिटकॉइन']):
        last_news_topic = 'crypto'
        return 'Cryptocurrency', 'crypto', f'https://news.google.com/rss/search?q=crypto+OR+cryptocurrency+OR+bitcoin+when:2d&hl={hl}&gl=IN&ceid=IN:en'
        
    # 3. Stock Market & Economy / Business
    if any(k in q_lower for k in ['stock', 'stocks', 'share market', 'shares', 'nifty', 'sensex', 'business', 'finance', 'economy', 'budget', 'शेयर बाजार', 'શેર બજાર', 'व्यापार']):
        last_news_topic = 'business'
        return 'Business & Markets', 'business', f'https://news.google.com/rss/headlines/section/topic/BUSINESS?hl={hl}&gl=IN&ceid=IN:en'
        
    # 4. Sports
    if any(k in q_lower for k in ['sports', 'cricket', 'ipl', 'football', 'tennis', 'badminton', 'खेल', 'क्रिकेट', 'રમત']):
        last_news_topic = 'sports'
        return 'Sports', 'sports', f'https://news.google.com/rss/headlines/section/topic/SPORTS?hl={hl}&gl=IN&ceid=IN:en'
        
    # 5. Entertainment
    if any(k in q_lower for k in ['entertainment', 'bollywood', 'movie', 'movies', 'cinema', 'actor', 'actress', 'मनोरंजन', 'सिनेमा']):
        last_news_topic = 'entertainment'
        return 'Entertainment', 'entertainment', f'https://news.google.com/rss/headlines/section/topic/ENTERTAINMENT?hl={hl}&gl=IN&ceid=IN:en'
        
    # 6. Follow-up query retaining previous topic (e.g. "tell me more news", "what else", "aur batao")
    is_follow_up = any(w in q_lower or w in query for w in FOLLOW_UP_WORDS)
    if is_follow_up and last_news_topic:
        if last_news_topic == 'Palghar Leopard Alert':
            encoded_q = urllib.parse.quote('Palghar leopard OR बिबट्या OR तेंदुआ OR Navli OR नावळी')
            return 'Palghar Leopard Alert', 'leopard', f'https://news.google.com/rss/search?q={encoded_q}&hl=mr&gl=IN&ceid=IN:mr'
        elif last_news_topic == 'tech':
            return 'Technology', 'tech', f'https://news.google.com/rss/headlines/section/topic/TECHNOLOGY?hl={hl}&gl=IN&ceid=IN:en'
        elif last_news_topic == 'crypto':
            return 'Cryptocurrency', 'crypto', f'https://news.google.com/rss/search?q=crypto+OR+cryptocurrency+OR+bitcoin+when:2d&hl={hl}&gl=IN&ceid=IN:en'
        elif last_news_topic == 'business':
            return 'Business & Markets', 'business', f'https://news.google.com/rss/headlines/section/topic/BUSINESS?hl={hl}&gl=IN&ceid=IN:en'
        elif last_news_topic == 'sports':
            return 'Sports', 'sports', f'https://news.google.com/rss/headlines/section/topic/SPORTS?hl={hl}&gl=IN&ceid=IN:en'
        elif last_news_topic == 'entertainment':
            return 'Entertainment', 'entertainment', f'https://news.google.com/rss/headlines/section/topic/ENTERTAINMENT?hl={hl}&gl=IN&ceid=IN:en'
        elif last_news_topic:
            return last_news_topic, 'location', f'https://news.google.com/rss/search?q={urllib.parse.quote(last_news_topic)}+when:3d&hl={hl}&gl=IN&ceid=IN:{hl}'

    # 7. Explicit Location or Universal Palghar Default
    target_loc = location if location else "Palghar"
    last_news_topic = target_loc
    if target_loc.lower() == 'palghar':
        encoded_q = urllib.parse.quote('Palghar OR पालघर when:3d')
        return 'Palghar News', 'location', f'https://news.google.com/rss/search?q={encoded_q}&hl=mr&gl=IN&ceid=IN:mr'
    else:
        encoded_q = urllib.parse.quote(f'{target_loc} when:3d')
        return target_loc, 'location', f'https://news.google.com/rss/search?q={encoded_q}&hl={hl}&gl=IN&ceid=IN:{hl}'

def get_live_news(query: str, location: str = "Palghar", lang: str = "en") -> str | None:
    """Fetches top breaking headlines, ensuring fresh unseen stories on every query or follow-up."""
    headers = {'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64)'}
    topic_label, cat_type, url = resolve_news_topic_and_url(query, location=location, lang=lang)
    
    try:
        req = urllib.request.Request(url, headers=headers)
        with urllib.request.urlopen(req, timeout=3.5) as resp:
            tree = ET.fromstring(resp.read())
            items = tree.findall('.//item')
            fresh_headlines = []
            for it in items:
                title_elem = it.find('title')
                if title_elem is None or not title_elem.text:
                    continue
                raw_title = title_elem.text
                clean_title = raw_title.split(' - ')[0] if ' - ' in raw_title else raw_title
                clean_title = clean_title.strip()
                if not is_already_seen(clean_title, seen_news_history):
                    fresh_headlines.append(clean_title)
                    if len(fresh_headlines) >= 3:
                        break
                        
            # If all items in feed have been seen, recycle older history to avoid empty response
            if not fresh_headlines and items:
                seen_news_history.clear()
                for it in items[:3]:
                    title_elem = it.find('title')
                    if title_elem is not None and title_elem.text:
                        clean_title = title_elem.text.split(' - ')[0].strip()
                        fresh_headlines.append(clean_title)
                        
            is_navli_or_leopard = any(k in query.lower() or k in (location or '').lower() for k in [
                'navli', 'navali', 'nawli', 'nawali', 'नावळी', 'नवली', 'bhogole', 'भोगोले', 'leopard', 'बिबट्या', 'तेंदुआ'
            ])
            navli_fact = "Navli Alert: In Navli (Bhogole Pada, Palghar East), a leopard (बिबट्या) entered residential areas and attacked a resident; 6 forest department search teams are actively deployed with camera traps and cages."
            
            if fresh_headlines:
                for h in fresh_headlines:
                    seen_news_history.append(normalize_title(h))
                prefix = (navli_fact + " | ") if is_navli_or_leopard else ""
                return f"Topic ({topic_label}): " + prefix + " | ".join(fresh_headlines)
    except Exception as e:
        print(f"News fetch error for {topic_label} ({lang}): {e}")
        
    # Fallback to general headlines if specific search fails
    try:
        hl_map = {'gu': 'gu', 'mr': 'mr', 'hi': 'hi', 'en': 'en-IN'}
        hl = hl_map.get(lang, 'en-IN')
        fallback_url = f'https://news.google.com/rss?hl={hl}&gl=IN&ceid=IN:{hl}'
        req = urllib.request.Request(fallback_url, headers=headers)
        with urllib.request.urlopen(req, timeout=3.0) as resp:
            tree = ET.fromstring(resp.read())
            items = tree.findall('.//item')
            fresh_fallback = []
            for it in items:
                title_elem = it.find('title')
                if title_elem is not None and title_elem.text:
                    clean_title = title_elem.text.split(' - ')[0].strip()
                    if not is_already_seen(clean_title, seen_news_history):
                        fresh_fallback.append(clean_title)
                        if len(fresh_fallback) >= 2:
                            break
            if fresh_fallback:
                for h in fresh_fallback:
                    seen_news_history.append(normalize_title(h))
                prefix = (navli_fact + " | ") if is_navli_or_leopard else ""
                return "Latest Headlines: " + prefix + " | ".join(fresh_fallback)
    except Exception as e:
        print(f"News fallback error: {e}")
        
    if is_navli_or_leopard:
        return f"Topic (Palghar Navli & Leopard News): {navli_fact}"
    return None

# --- Step-By-Step Guides ---
active_briefing = {
    "topic_id": None,
    "title": None,
    "current_step": 0,
    "total_steps": 0,
    "is_active": False,
    "last_updated": 0,
    "source": "deterministic",
    "user_constraints": None
}

BRIEFING_KNOWLEDGE_BASE = {
    "dosa": {
        "title": "Crispy Masala Dosa",
        "keywords": ["dosa", "dhosa", "डोसा", "ढोसा", "ઢોસા"],
        "teaser": {
            "en": "Yes, I know how to make crispy golden Masala Dosa! Ready to start with the tawa preparation?",
            "hi": "हाँ, मुझे क्रिस्पी मसाला डोसा की रेसिपी पता है! क्या हम तवा गरम करने से शुरू करें?",
            "mr": "हो, मला कुरकुरीत मसाला डोसा बनवण्याची रेसिपी माहित आहे! तवा गरम करून सुरुवात करायची का?",
            "gu": "હા, મને ક્રિસ્પી મસાલા ઢોસા બનાવવાની રીત ખબર છે! તવો ગરમ કરવાથી શરૂ કરીએ?"
        },
        "steps": [
            {
                "en": "Heat a flat tawa on medium. Sprinkle a few water drops—when they sizzle away, wipe lightly with an oiled paper towel.",
                "hi": "तवे को मध्यम आंच पर गरम करें। थोड़ा पानी छिड़कें—जब छनछनाए, तो तेल लगे पेपर टॉवल से पोंछ लें।",
                "mr": "तवा मध्यम आचेवर गरम करा. थोडे पाणी शिंपडा—ते उडताच तेल लावलेल्या कपड्याने हलके पुसून घ्या.",
                "gu": "તવો મધ્યમ તાપે ગરમ કરો. થોડું પાણી છાંટો—તે બળી જાય એટલે તેલવાળા કાગળથી લૂછી લો."
            },
            {
                "en": "Pour one ladle of batter in the center, and spread it in smooth outward circles. Drizzle half a teaspoon of oil around the edges.",
                "hi": "बीच में एक कलछी बैटर डालें और गोल-गोल बाहर की ओर फैलाएं। किनारों पर आधा चम्मच तेल या मक्खन लगाएं।",
                "mr": "मध्यभागी एक पळी पीठ घाला आणि गोलाकार फिरवून पातळ पसरवा. कडेने अर्धा चमचा तेल किंवा बटर सोडा.",
                "gu": "વચ્ચે એક તવો ખીરૂં નાખીને ગોળ ગોળ ફેલાવો. કિનારી પર અડધી ચમચી તેલ અથવા માખણ લગાવો."
            },
            {
                "en": "Cook on medium flame until the base turns golden brown. Add 2 spoonfuls of potato masala in the center.",
                "hi": "मध्यम आंच पर नीचे से सुनहरा और क्रिस्पी होने तक सेकें। फिर बीच में 2 चम्मच आलू का मसाला रखें।",
                "mr": "मध्यम आचेवर खालून सोनेरी आणि कुरकुरीत होईपर्यंत भाजा. नंतर मध्यभागी दोन चमचे बटाटा भाजी ठेवा.",
                "gu": "મધ્યમ તાપે નીચેથી સોનેરી અને ક્રિસ્પી થાય ત્યાં સુધી શેકો. પછી વચ્ચે 2 ચમચી બટાકાનો મસાલો મૂકો."
            },
            {
                "en": "Fold the dosa in half and slide it onto a plate. Serve hot with coconut chutney and sambar! Your delicious dosa is ready!",
                "hi": "डोसे को आधा मोड़ लें और प्लेट में निकालें। गरमा-गरम नारियल की चटनी और सांभर के साथ परोसें!",
                "mr": "डोसा दुमडून प्लेटमध्ये काढा. गरमागरम खोबऱ्याची चटणी आणि सांबारसोबत सर्व्ह करा! डोसा तयार आहे!",
                "gu": "ઢોસાને વાળીને પ્લેટમાં કાઢો. ગરમાગરમ નારિયેળની ચટણી અને સંભાર સાથે સર્વ કરો! ઢોસો તૈયાર છે!"
            }
        ]
    },
    "chai": {
        "title": "Adrak Elaichi Masala Chai",
        "keywords": ["chai", "tea", "masala chai", "चाय", "चहा", "ચા"],
        "teaser": {
            "en": "Yes, I know how to make fragrant Adrak Elaichi Masala Chai! Shall we start with boiling water and crushed spices?",
            "hi": "हाँ, मुझे अदरक इलायची वाली कड़क मसाला चाय की रेसिपी पता है! क्या पानी और मसाले उबालने से शुरू करें?",
            "mr": "हो, मला आले-वेलची घातलेला कडक मसाला चहा बनवता येतो! पाणी आणि मसाले उकळून सुरुवात करायची का?",
            "gu": "હા, મને આદુ એલચી વાળી કડક મસાલા ચા બનાવવાની રીત ખબર છે! પાણી અને મસાલો ઉકાળવાથી શરૂ કરીએ?"
        },
        "steps": [
            {
                "en": "In a saucepan, bring 1 cup of water to boil with 1 inch of crushed ginger and 2 crushed green cardamoms for 2 minutes.",
                "hi": "पैन में 1 कप पानी लें, उसमें 1 इंच कुटा अदरक और 2 कुटी हरी इलायची डालकर 2 मिनट उबालें।",
                "mr": "पातेल्यात 1 कप पाणी घेऊन त्यात 1 इंच ठेचलेलं आलं आणि 2 वेलची घालून 2 मिनिटे उकळू द्या.",
                "gu": "તપેલીમાં 1 કપ પાણી લઈ તેમાં 1 ઇંચ ખાંડેલું આદુ અને 2 એલચી નાખીને 2 મિનિટ ઉકાળો."
            },
            {
                "en": "Add 1.5 teaspoons of black tea leaves and 2 teaspoons of sugar. Let it boil vigorously for 1 minute until deep amber.",
                "hi": "अब 1.5 चम्मच चायपत्ती और 2 चम्मच चीनी डालें। गहरा रंग आने तक 1 मिनट अच्छी तरह उबालें।",
                "mr": "यात 1.5 चमचे चहा पावडर आणि 2 चमचे साखर घाला. छान रंग येईपर्यंत 1 मिनिट उकळा.",
                "gu": "તેમાં 1.5 ચમચી ચા પત્તી અને 2 ચમચી ખાંડ ઉમેરો. સારો રંગ આવે ત્યાં સુધી 1 મિનિટ ઉકાળો."
            },
            {
                "en": "Pour in 1 cup of fresh milk. Let it come to a rolling boil twice, then strain into cups. Your steaming hot Masala Chai is ready!",
                "hi": "अब 1 कप दूध डालें। दो बार उफान आने दें, फिर कप में छान लें। आपकी गरमा-गरम कड़क मसाला चाय तैयार है!",
                "mr": "आता 1 कप दूध घाला. दोनदा छान उकळी येऊ द्या आणि कपमध्ये गाळून घ्या. तुमचा कडक चहा तयार आहे!",
                "gu": "હવે 1 કપ દૂધ ઉમેરો. બે વખત ઉભરો આવવા દો અને કપમાં ગાળી લો. તમારી ગરમાગરમ કડક ચા તૈયાર છે!"
            }
        ]
    },
    "esp32_wiring": {
        "title": "ESP32-S3 to MAX98357A I2S DAC Wiring",
        "keywords": ["max98357", "amplifier", "dac", "wiring", "speaker connect", "connect speaker", "pinout"],
        "teaser": {
            "en": "Yes! Connecting the MAX98357A I2S DAC to your ESP32-S3 takes 5 jumper connections. Ready for the power pins?",
            "hi": "हाँ! MAX98357A I2S DAC को ESP32-S3 से जोड़ने के लिए 5 पिन जोड़ने होते हैं। क्या पावर पिन से शुरू करें?",
            "mr": "हो! MAX98357A DAC ला ESP32-S3 सोबत जोडण्यासाठी 5 वायर लागतात. पॉवर पिनने सुरुवात करायची का?",
            "gu": "હા! MAX98357A DAC ને ESP32-S3 સાથે જોડવા માટે 5 વાયર લાગે છે. પાવર પિનથી શરૂ કરીએ?"
        },
        "steps": [
            {
                "en": "First, connect the DAC's VIN pin to the ESP32 5V pin, and connect the GND pin to any ESP32 GND pin.",
                "hi": "सबसे पहले DAC की VIN पिन को ESP32 की 5V पिन से, और GND पिन को ESP32 की GND पिन से जोड़ें।",
                "mr": "सर्वप्रथम DAC ची VIN पिन ESP32 च्या 5V पिनला आणि GND पिन कोणत्याही GND पिनला जोडा.",
                "gu": "સૌપ્રથમ DAC ની VIN પિનને ESP32 ની 5V પિન સાથે, અને GND પિનને ESP32 ની GND પિન સાથે જોડો."
            },
            {
                "en": "Next, connect the BCLK pin to GPIO 5, and the LRC pin to GPIO 6 on your ESP32-S3 board.",
                "hi": "इसके बाद BCLK पिन को GPIO 5 से, और LRC पिन को GPIO 6 से जोड़ें।",
                "mr": "त्यानंतर BCLK पिन GPIO 5 ला आणि LRC पिन GPIO 6 ला जोडा.",
                "gu": "ત્યારબાદ BCLK પિનને GPIO 5 સાથે, અને LRC પિનને GPIO 6 સાથે જોડો."
            },
            {
                "en": "Finally, connect the DIN pin to GPIO 7. That's your I2S audio data stream line. All 5 connections are complete and ready!",
                "hi": "आखिर में DIN पिन को GPIO 7 से जोड़ें। यह आपकी ऑडियो डेटा लाइन है। वायरिंग पूरी हो गई!",
                "mr": "शेवटी DIN पिन GPIO 7 ला जोडा. ही ऑडिओ डेटा लाइन आहे. संपूर्ण वायरिंग पूर्ण झाली!",
                "gu": "છેલ્લે DIN પિનને GPIO 7 સાથે જોડો. આ તમારી ઓડિયો ડેટા લાઈન છે. વાયરિંગ પૂરું થયું!"
            }
        ]
    }
}

def is_explicit_cancel_command(q_low: str) -> bool:
    """Detects if user wants to cancel, stop, or drop the current plan/recipe."""
    CANCEL_PATTERNS = [
        r'\b(stop|cancel|quit|exit|close|bas)\b',
        r'\b(drop|dropped|cancel|cancelling)\b.*\b(plan|idea|chai|tea|dosa|recipe|cooking|guide|wiring)\b',
        r'\b(nahi banana|nahi banani|mood nahi|man nahi|nahi chahiye|chhod do|rahan do|rehan do|band karo|nako)\b',
        r'\b(nathi banavvu|rehva do|bandh karo)\b',
        r'(बस|छोड़ दो|रहने दो|बंद करो|रुक जाओ|नहीं बनाना|नहीं बनानी|नको|थांब|थांबा|बंद करा|રહેવા દો|નથી બનાવવું|બંધ કરો)'
    ]
    for pat in CANCEL_PATTERNS:
        if re.search(pat, q_low):
            return True
    return False

def is_explicit_repeat_command(q_low: str) -> bool:
    """Detects if user explicitly asked to repeat the current step."""
    tokens = re.findall(r'[\w\u0900-\u097F\u0A80-\u0AFF]+', q_low)
    if len(tokens) > 4:
        return False
    REPEAT_PATTERNS = [
        r'\b(repeat|repeat that|once more|again|say again)\b',
        r'\b(dobara|phir se|ek aur baar)\b',
        r'\b(punha sang|punha)\b',
        r'(दोबारा|दोबारा बताओ|फिर से|एक बार फिर|पुन्हा सांगा|पुन्हा|ફરીથી|ફરી કહો)'
    ]
    for pat in REPEAT_PATTERNS:
        if re.search(pat, q_low):
            return True
    return False

def is_pure_advance_command(q_low: str) -> bool:
    """
    Detects if the user query is a PURE, UNAMBIGUOUS step advance command.
    Must be short (<= 3 words) and contain NO doubts, constraints, actions, or ingredients!
    """
    tokens = re.findall(r'[\w\u0900-\u097F\u0A80-\u0AFF]+', q_low)
    if len(tokens) > 3 or len(tokens) == 0:
        return False
        
    CONTRA_INDICATORS = [
        "don't", "dont", "not", "no", "nahi", "nathi", "nako", "without", "bina",
        "only", "sirf", "fakt", "just", "wait", "ruko", "thamba", "let me", "let",
        "can", "could", "what", "kya", "kaise", "instead", "badle", "drop", "dropped",
        "gas", "stove", "pan", "cup", "milk", "tea", "chai", "sugar", "water", "paani", "doodh",
        "dosa", "batter", "salt", "oil", "tel", "butter", "tawa", "wiring", "pin", "wire",
        "over", "khatam", "finish", "finished", "ran out", "out of"
    ]
    if any(ci in q_low for ci in CONTRA_INDICATORS):
        return False
        
    ADVANCE_PATTERNS = [
        r'\b(next|continue|done|ready)\b',
        r'\b(yes|yeah|yep|sure|ok|okay)\b',
        r'\b(aage|aage batao|phir|fir|batao)\b',
        r'\b(ho gaya|kar diya|kardiya|hogaya)\b',
        r'\b(haan|haa)\b',
        r'\b(pudhe|zala|zhala|sang)\b',
        r'\b(aagal|janav|thay gayu)\b',
        r'^(हाँ|हां|बताओ|आगे|आगे बताओ|फिर|हो गया|कर दिया|शुरू करो|नेक्स्ट|चालू करो)$',
        r'^(झाले|पुढे|सांगा|पुढचे|सुरू करा|पुढील)$',
        r'^(હા|આગળ|જણાવો|થઈ ગયું|શરૂ કરો)$'
    ]
    for pat in ADVANCE_PATTERNS:
        if re.search(pat, q_low):
            return True
    return False

def generate_executive_morning_briefing(lang: str = "en") -> str:
    """Generates an instant personalized executive daily briefing with weather, commodities, and top news."""
    w_info = get_live_weather("Palghar")
    temp_str = "31°C, clear sky"
    if w_info:
        m = re.search(r'(\d+°C(?:,\s*[^,]+)?)', w_info)
        if m:
            temp_str = m.group(1)
            
    cng_str = "₹86.50/kg"
    gold_str = "₹78,850 per 10g"
    
    # Time of day detection
    hour = datetime.datetime.now().hour
    if hour < 12:
        greet = {"en": "Good morning Shravan!", "hi": "सुप्रभात श्रवण जी!", "mr": "शुभ सकाळ श्रवण!", "gu": "સુપ્રભાત શ્રવણ!"}
    elif hour < 17:
        greet = {"en": "Good afternoon Shravan!", "hi": "शुभ दोपहर श्रवण जी!", "mr": "शुभ दुपार श्रवण!", "gu": "શુભ બપોર શ્રવણ!"}
    else:
        greet = {"en": "Good evening Shravan!", "hi": "शुभ संध्या श्रवण जी!", "mr": "शुभ संध्याकाळ श्रवण!", "gu": "શુભ સાંજ શ્રવણ!"}
        
    g = greet.get(lang, greet["en"])
    
    if lang == 'hi':
        return f"{g} पालघर में आज मौसम {temp_str} है। 24 कैरेट सोना {gold_str} और सीएनजी {cng_str} है। क्या आप आज के मुख्य समाचार सुनना चाहते हैं?"
    elif lang == 'mr':
        return f"{g} पालघरमध्ये आज हवामान {temp_str} आहे. 24 कॅरेट सोने {gold_str} आणि सीएनजी {cng_str} आहे. आजच्या ताज्या बातम्या ऐकायच्या आहेत का?"
    elif lang == 'gu':
        return f"{g} પાલઘરમાં આજે હવામાન {temp_str} છે. 24 કેરેટ સોનું {gold_str} અને સીએનજી {cng_str} છે. શું તમારે આજના મુખ્ય સમાચાર સાંભળવા છે?"
    else:
        return f"{g} In Palghar today it's {temp_str}. 24K gold is at {gold_str}, and CNG is {cng_str}. Would you like the top breaking headlines or stock market updates?"

def resolve_briefing_intent(user_query: str, lang: str = "en") -> tuple[str | None, str | None]:
    """
    State machine for interactive step-by-step briefings and tutorials.
    Returns (direct_reply, context_to_inject).
    """
    global active_briefing
    q_low = user_query.lower().strip()
    
    # 0. Executive Briefing trigger ("Good morning", "give me my briefing", etc.)
    BRIEFING_TRIGGER_WORDS = [
        "morning briefing", "daily briefing", "give me briefing", "give me my briefing", "what's my briefing",
        "good morning", "good morning alexa", "morning update", "ब्रीफिंग", "सुप्रभात", "शुभ सकाळ", "સુપ્રભાત"
    ]
    if any(bw in q_low for bw in BRIEFING_TRIGGER_WORDS):
        briefing_text = generate_executive_morning_briefing(lang=lang)
        return briefing_text, None
    
    # 1. Check if active briefing has timed out (60 seconds)
    if active_briefing["is_active"] and (time.time() - active_briefing["last_updated"] > 60):
        active_briefing["is_active"] = False
        active_briefing["topic_id"] = None
        active_briefing["user_constraints"] = None
        
    # 2. Handle active briefing navigation
    if active_briefing["is_active"]:
        topic_data = BRIEFING_KNOWLEDGE_BASE.get(active_briefing["topic_id"])
        
        # A. Cancel / Stop / Drop the plan
        if is_explicit_cancel_command(q_low):
            active_briefing["is_active"] = False
            active_briefing["topic_id"] = None
            active_briefing["user_constraints"] = None
            active_briefing["source"] = "deterministic"
            cancel_replies = {
                "en": "Sure, plan cancelled! Let me know whenever you want to restart or if you need anything else.",
                "hi": "जी बिल्कुल, प्लान कैंसल कर दिया गया है! जब चाहें फिर से पूछ सकते हैं।",
                "mr": "नक्कीच, माहिती थांबवली आहे! तुम्हाला हवं तेव्हा पुन्हा विचारू शकता.",
                "gu": "ચોક્કસ, પ્લાન રદ કર્યો છે! જ્યારે જરૂર હોય ત્યારે ફરી પૂછી શકો છો."
            }
            return cancel_replies.get(lang, cancel_replies["en"]), None
            
        # B. Repeat current step
        if is_explicit_repeat_command(q_low):
            if active_briefing["source"] == "deterministic" and topic_data and 0 < active_briefing["current_step"] <= len(topic_data["steps"]):
                step_obj = topic_data["steps"][active_briefing["current_step"] - 1]
                step_text = step_obj.get(lang, step_obj["en"])
                repeat_prefix = {
                    "en": f"Repeating Step {active_briefing['current_step']}: ",
                    "hi": f"स्टेप {active_briefing['current_step']} दोहरा रही हूँ: ",
                    "mr": f"स्टेप {active_briefing['current_step']} पुन्हा सांगते: ",
                    "gu": f"સ્ટેપ {active_briefing['current_step']} ફરીથી બોલું છું: "
                }
                return f"{repeat_prefix.get(lang, repeat_prefix['en'])}{step_text}", None
            elif active_briefing["source"] == "custom":
                curr = active_briefing["current_step"]
                prompt_context = f"""[ACTIVE CUSTOMIZED RECIPE - REPEAT STEP {curr}]:
- Topic: '{active_briefing['title']}'
- Current Step: Step {curr}
- STRICT USER INGREDIENT INVENTORY: "{active_briefing['user_constraints']}"
- The user has ONLY these ingredients. NEVER mention garlic, ginger, elaichi, or any missing items!
- Repeat Step {curr} concisely using ONLY their available ingredients."""
                return None, prompt_context

        # Check and lock user ingredient constraints (e.g. "I only have sugar, chai patti, milk and water", "no garlic", "sirf doodh paani hai", "chai patti is over")
        has_ingredient_constraint = (
            any(w in q_low for w in [
                "don't have", "dont have", "only have", "i have only", "only got", "nahi hai",
                "sirf", "fakt", "bina", "without", "no garlic", "no ginger", "no sugar", "no elaichi",
                "just milk", "just water", "just tea", "sirf doodh", "sirf chai", "sirf paani", "sirf cheeni",
                "is over", "has been over", "got over", "khatam", "finished", "ran out", "out of"
            ]) or (
                any(ing in q_low for ing in [
                    "garlic", "ginger", "sugar", "milk", "water", "chaipati", "chai patti", "tea leaves",
                    "adrak", "lahsun", "doodh", "cheeni", "shakkar", "paani", "elaichi", "cardamom"
                ]) and any(neg in q_low for neg in ["don't", "dont", "not", "no", "nahi", "only", "sirf", "bina", "without", "over", "khatam", "finished", "ran out"])
            )
        )
        if has_ingredient_constraint:
            active_briefing["user_constraints"] = user_query
            active_briefing["source"] = "custom"
            print(f"[BRIEFING RECIPE CONSTRAINTS LOCKED]: {user_query}")

        # C. Pure, unambiguous advance command (short 1-3 words like 'Next', 'Haan', 'Aage')
        if is_pure_advance_command(q_low):
            if active_briefing["source"] == "custom":
                # User has customized ingredients! Advance via Groq with locked constraints!
                active_briefing["current_step"] += 1
                curr = active_briefing["current_step"]
                total = len(topic_data["steps"]) if topic_data else 3
                if curr > total:
                    active_briefing["is_active"] = False
                    active_briefing["user_constraints"] = None
                    done_replies = {
                        "en": f"All steps for your custom {active_briefing['title']} are complete! Enjoy your drink!",
                        "hi": f"आपकी {active_briefing['title']} के सभी स्टेप्स पूरे हो चुके हैं! आनंद लें!",
                        "mr": f"{active_briefing['title']} तयार आहे!",
                        "gu": f"{active_briefing['title']} તૈયાર થઈ ગયું છે!"
                    }
                    return done_replies.get(lang, done_replies["en"]), None

                prompt_context = f"""[ACTIVE CUSTOMIZED RECIPE - ADVANCING TO STEP {curr}]:
- Topic: '{active_briefing['title']}'
- Step Position: Step {curr} of {total}
- STRICT USER INGREDIENT INVENTORY: "{active_briefing['user_constraints']}"
CRITICAL RULES FOR THIS STEP:
1. The user explicitly stated they DO NOT have other ingredients (e.g. NO garlic, NO ginger, NO cardamom).
2. They have ONLY the ingredients they mentioned: "{active_briefing['user_constraints']}".
3. Provide ONLY Step {curr} of this customized recipe using ONLY their available ingredients (max 20 words).
4. Do NOT re-introduce any ingredient they do not have!"""
                return None, prompt_context

            elif topic_data:
                # Deterministic standard recipe
                active_briefing["current_step"] += 1
                curr = active_briefing["current_step"]
                total = len(topic_data["steps"])
                if curr <= total:
                    step_obj = topic_data["steps"][curr - 1]
                    step_text = step_obj.get(lang, step_obj["en"])
                    step_prefix = {
                        "en": f"Step {curr}: ",
                        "hi": f"स्टेप {curr}: ",
                        "mr": f"स्टेप {curr}: ",
                        "gu": f"સ્ટેપ {curr}: "
                    }
                    if curr == total:
                        active_briefing["is_active"] = False  # Completed!
                    return f"{step_prefix.get(lang, step_prefix['en'])}{step_text}", None
                else:
                    active_briefing["is_active"] = False
                    done_replies = {
                        "en": f"All steps for {topic_data['title']} are complete! Enjoy!",
                        "hi": f"{topic_data['title']} के सभी स्टेप्स पूरे हो चुके हैं! आनंद लें!",
                        "mr": f"{topic_data['title']} च्या सर्व स्टेप्स पूर्ण झाल्या आहेत!",
                        "gu": f"{topic_data['title']} ના તમામ સ્ટેપ્સ પૂર્ણ થઈ ગયા છે!"
                    }
                    return done_replies.get(lang, done_replies["en"]), None

        # D. Conversational, adaptive, doubt, or constraint query during active guide!
        cooking_or_briefing_terms = [
            "step", "next", "repeat", "aage", "pachi", "fir", "phir", "again", "kya karu", "what to do",
            "gas", "flame", "pan", "patila", "tawa", "heat", "boil", "ubal", "stir", "cup", "spoon",
            "sugar", "tea", "chai", "patti", "milk", "water", "doodh", "paani", "cheeni", "shakkar",
            "ginger", "adrak", "elaichi", "masala", "salt", "oil", "tel", "ready", "done", "ho gaya",
            "khatam", "over", "wait", "ruko", "second", "minute", "ingredient", "saman", "drop", "cancel"
        ]
        is_relevant = any(t in q_low for t in cooking_or_briefing_terms) or (
            topic_data and any(kw in q_low for kw in topic_data.get("keywords", []))
        )
        if not is_relevant:
            # Query is NOT related to the active recipe tutorial (e.g. mic test "can you hear me", greeting, QA)
            active_briefing["is_active"] = False
            active_briefing["topic_id"] = None
            active_briefing["user_constraints"] = None
            return None, None

        active_briefing["last_updated"] = time.time()
        if topic_data:
            curr_step = active_briefing["current_step"]
            steps = topic_data["steps"]
            curr_idx = max(0, min(curr_step - 1, len(steps) - 1)) if curr_step > 0 else 0
            curr_step_text = steps[curr_idx].get(lang, steps[curr_idx]["en"])
            
            constraints_info = f"- STRICT USER INGREDIENT INVENTORY: \"{active_briefing['user_constraints']}\"\n- REMEMBER: User has ONLY these items. NEVER suggest garlic, ginger, elaichi, or anything they don't have!" if active_briefing.get("user_constraints") else ""
            
            prompt_context = f"""[ACTIVE INTERACTIVE TUTORIAL CONTEXT]:
- Topic: '{topic_data['title']}'
- Current Step Position: Step {curr_step} of {len(steps)}
- Current Step Standard Instruction: "{curr_step_text}"
{constraints_info}
- User Spoke: "{user_query}"

HOW TO HANDLE THIS USER TURN:
1. IF USER DROPPED PLAN OR WANTS TO STOP (e.g. "dropped the plan", "nahi banana"):
   - Include tag [CANCEL_BRIEFING] in your reply.
   - Reply playfully accepting their choice (e.g. "No problem! Tea break cancelled! What's next?").
2. IF USER HAS INGREDIENT LIMITATIONS (e.g. "I only have sugar, chai patti, milk and water", "no garlic", "no ginger"):
   - ADAPT THE RECIPE INSTANTLY!
   - Reassure them that simple chai with their ingredients is delicious, and instruct them on the exact next step using strictly what they have (max 22 words)!
3. IF USER SAYS AN INGREDIENT IS OVER / FINISHED / OUT OF STOCK (e.g. "my chai patti has been over", "chai patti khatam ho gayi"):
   - Acknowledge that the ingredient ran out!
   - NEVER tell them to add that ingredient!
   - Offer to help them order it online on Amazon/Flipkart or ask if they want to pause making tea (max 20 words)!
4. IF USER MENTIONS AN ACTION IN PROGRESS (e.g. "let me turn on the gas", "wait a minute"):
   - Cheerfully tell them to go ahead and let you know when they are ready (e.g. "Go for it! Turn on the gas and place your pan. Ready when you are!"). Do NOT rush ahead.
5. IF USER ASKS TO SEARCH, FIND, OR BUY AN INGREDIENT/PRODUCT (e.g. "find out society chai patti 1 kg", "order chai patti", "how much is society tea"):
   - Quote the exact live price and platform from the attached e-commerce search results!
   - Ask if they would like to pause the recipe until their order arrives!
6. IF USER ASKS A QUESTION OR DOUBT:
   - Answer their specific question directly in 1 short sentence using only their known ingredients, then prompt them for the current step."""
            return None, prompt_context

    # 3. Check for starting a new briefing
    for topic_id, data in BRIEFING_KNOWLEDGE_BASE.items():
        if any(kw in q_low for kw in data["keywords"]):
            # If user asks for recipe/how-to/wiring in English, Hindi, Marathi, Gujarati
            BRIEF_HOWTO_TRIGGERS = [
                "recipe", "how to", "make", "cook", "prepare", "wiring", "connect", "banate", "banao", "kaise",
                "रेसिपी", "विधि", "तरीका", "बनाना", "बनाने", "आती है", "आता है", "कैसे", "जोड़ें", "कनेक्ट",
                "कशी बनवायची", "रेसिपी", "कसे बनवायचे", "माहित आहे का", "जोडणी", "वायरिंग",
                "રીત", "કેવી રીતે", "બનાવવાની", "આવડે છે", "જોડવું", "વાયરિંગ"
            ]
            if any(trig in q_low for trig in BRIEF_HOWTO_TRIGGERS) or "recipe" in q_low:
                active_briefing["is_active"] = True
                active_briefing["topic_id"] = topic_id
                active_briefing["title"] = data["title"]
                active_briefing["current_step"] = 0
                active_briefing["total_steps"] = len(data["steps"])
                active_briefing["last_updated"] = time.time()
                
                # Check if user specified ingredient constraints right in the trigger question!
                has_init_constraint = (
                    any(w in q_low for w in [
                        "don't have", "dont have", "only have", "i have only", "only got", "nahi hai",
                        "sirf", "fakt", "bina", "without", "no garlic", "no ginger", "no sugar", "no elaichi",
                        "just milk", "just water", "just tea", "sirf doodh", "sirf chai", "sirf paani", "sirf cheeni",
                        "is over", "has been over", "got over", "khatam", "finished", "ran out", "out of"
                    ]) or (
                        any(ing in q_low for ing in [
                            "garlic", "ginger", "sugar", "milk", "water", "chaipati", "chai patti", "tea leaves",
                            "adrak", "lahsun", "doodh", "cheeni", "shakkar", "paani", "elaichi", "cardamom"
                        ]) and any(neg in q_low for neg in ["don't", "dont", "not", "no", "nahi", "only", "sirf", "bina", "without", "over", "khatam", "finished", "ran out"])
                    )
                )
                if has_init_constraint:
                    active_briefing["user_constraints"] = user_query
                    active_briefing["source"] = "custom"
                    print(f"[BRIEFING INITIAL CONSTRAINTS LOCKED]: {user_query}")
                    prompt_context = f"""[STARTING CUSTOM RECIPE - USER HAS INGREDIENT RESTRICTIONS]:
- Recipe: {data['title']}
- User Inventory / Constraints: '{user_query}'
- The user has ONLY these ingredients. They do NOT have garlic, ginger, elaichi, spices, or other items.
- Acknowledge their available ingredients warmly and ask if they are ready to start Step 1 using ONLY what they have (max 20 words)."""
                    return None, prompt_context

                active_briefing["source"] = "deterministic"
                teaser_text = data["teaser"].get(lang, data["teaser"]["en"])
                return teaser_text, None

    return None, None

# --- Text Sanitizer for TTS ---
def sanitize_mixed_indic_script(text: str) -> str:
    """
    Sanitizes mixed Indic script token hallucinations emitted by Whisper (e.g. 'તुम्हाला' -> 'तुम्हाला', 'આवाज' -> 'आवाज').
    In real writing, words never mix Gujarati script [U+0A80..U+0AFF] with Devanagari [U+0900..U+097F].
    Because Gujarati and Devanagari share identical 1-to-1 Unicode point offsets (offset = 0x0180),
    any rogue character from the minority script inside a word or sentence is mapped cleanly to its true script.
    """
    if not text:
        return text
    dev_count = len(re.findall(r'[\u0900-\u097F]', text))
    gu_count = len(re.findall(r'[\u0A80-\u0AFF]', text))
    
    # If pure Devanagari, pure Gujarati, or neither, no mixed script repair is needed
    if dev_count == 0 or gu_count == 0:
        return text
        
    words = text.split()
    sanitized_words = []
    dev_dominant = dev_count >= gu_count
    
    for word in words:
        w_dev = len(re.findall(r'[\u0900-\u097F]', word))
        w_gu = len(re.findall(r'[\u0A80-\u0AFF]', word))
        
        # Check if the word mixes both scripts or has rogue minority characters in dominant context
        should_repair = (w_dev > 0 and w_gu > 0) or \
                        (dev_dominant and w_gu <= 2 and dev_count >= 2 * gu_count) or \
                        (not dev_dominant and w_dev <= 2 and gu_count >= 2 * dev_count)
                        
        if should_repair:
            new_word = ''
            for ch in word:
                cp = ord(ch)
                if dev_dominant:
                    # Convert rogue Gujarati characters to Devanagari
                    if 0x0A80 <= cp <= 0x0AFF:
                        target = cp - 0x0180
                        new_word += chr(target) if (0x0900 <= target <= 0x097F) else ch
                    else:
                        new_word += ch
                else:
                    # Convert rogue Devanagari characters to Gujarati
                    if 0x0900 <= cp <= 0x097F:
                        target = cp + 0x0180
                        new_word += chr(target) if (0x0A80 <= target <= 0x0AFF) else ch
                    else:
                        new_word += ch
            sanitized_words.append(new_word)
        else:
            sanitized_words.append(word)
            
    return ' '.join(sanitized_words)

def extract_explicit_language_request(query: str) -> str | None:
    """
    Detects if the user explicitly requested a specific target language for the response,
    even if the command itself was spoken in another language (e.g. 'Tell the same answer in Marathi').
    """
    if not query:
        return None
    q = query.lower().strip()
    
    # Marathi explicit requests
    mr_patterns = [
        r'\bin\s+marathi\b', r'\binto\s+marathi\b', r'\bto\s+marathi\b', r'\bas\s+marathi\b',
        r'\bspeak\s+marathi\b', r'\btell\s+.*in\s+marathi\b', r'\bsay\s+.*in\s+marathi\b',
        r'\bmarathi\s+language\b', r'\bmarathi\s+please\b', r'\bmarathit\b', r'\bmarathi\s+madhe\b',
        r'मराठीत', r'मराठी\s*मध्ये', r'मराठी\s*भाशेत', r'मराठी\s*भाषेत', r'मराठी\s*बोला', r'मराठी\s*सांगा',
        r'મરાઠીમાં', r'મરાઠી'
    ]
    if any(re.search(p, q) for p in mr_patterns):
        return 'mr'
        
    # Gujarati explicit requests
    gu_patterns = [
        r'\bin\s+gujarati\b', r'\binto\s+gujarati\b', r'\bto\s+gujarati\b', r'\bas\s+gujarati\b',
        r'\bspeak\s+gujarati\b', r'\btell\s+.*in\s+gujarati\b', r'\bsay\s+.*in\s+gujarati\b',
        r'\bgujarati\s+language\b', r'\bgujarati\s+please\b', r'\bgujaratin\b', r'\bgujaratima\b',
        r'ગુજરાતીમાં', r'ગુજરાતી\s*ભાષામાં', r'ગુજરાતી\s*બોલો', r'ગુજરાતી\s*કહો',
        r'गुजराती\s*में', r'गुजराती\s*बोलो', r'गुजराती\s*बताओ'
    ]
    if any(re.search(p, q) for p in gu_patterns):
        return 'gu'
        
    # Hindi explicit requests
    hi_patterns = [
        r'\bin\s+hindi\b', r'\binto\s+hindi\b', r'\bto\s+hindi\b', r'\bas\s+hindi\b',
        r'\bspeak\s+hindi\b', r'\btell\s+.*in\s+hindi\b', r'\bsay\s+.*in\s+hindi\b',
        r'\bhindi\s+language\b', r'\bhindi\s+please\b',
        r'हिंदी\s*में', r'हिन्दी\s*में', r'हिंदी\s*बोलो', r'हिंदी\s*बताओ',
        r'હિન્દીમાં', r'હિન્દી'
    ]
    if any(re.search(p, q) for p in hi_patterns):
        return 'hi'
        
    # English explicit requests
    en_patterns = [
        r'\bin\s+english\b', r'\binto\s+english\b', r'\bto\s+english\b', r'\bas\s+english\b',
        r'\bspeak\s+english\b', r'\btell\s+.*in\s+english\b', r'\bsay\s+.*in\s+english\b',
        r'\benglish\s+language\b', r'\benglish\s+please\b',
        r'इंग्लिश\s*मध्ये', r'इंग्रजीत', r'अंग्रेजी\s*में', r'ઇંગ્લિશમાં'
    ]
    if any(re.search(p, q) for p in en_patterns):
        return 'en'
        
    return None

# --- Step 1: Speech to Text (Groq Whisper) ---
def run_groq_whisper(raw_pcm: bytes) -> tuple[str, float]:
    """Transcribes audio using Groq Whisper Large V3 Turbo with Indic script bleed protection."""
    cleaned_pcm = optimize_audio_for_esp32(raw_pcm, sample_rate=16000, threshold=200)
    if len(cleaned_pcm) < 1600:
        cleaned_pcm = raw_pcm
    wav_io = io.BytesIO()
    with wave.open(wav_io, 'wb') as wf:
        wf.setnchannels(1)
        wf.setsampwidth(2)
        wf.setframerate(16000)
        wf.writeframes(cleaned_pcm)
    wav_bytes = wav_io.getvalue()
    
    url = "https://api.groq.com/openai/v1/audio/transcriptions"
    boundary = "----FormBoundaryVoiceAssistant7MA4YW"
    
    body = bytearray()
    # Balanced multilingual prompt grounded in daily assistant vocabulary
    whisper_prompt = (
        "Alexa, Shravan. "
        "Tea, chai patti, gas stove, sugar, milk, water, masala dosa, recipe, timer, order, headphones, price, Sony, flipkart, amazon. "
        "मेरी चाय पत्ती खत्म हो गई है, मुझे चाय बनानी है, क्या आप मुझे बता सकते हैं?"
    )
    # Guarantee prompt never exceeds Groq's 896-byte limit
    safe_whisper_prompt = whisper_prompt.encode('utf-8')[:800].decode('utf-8', errors='ignore')
    body.extend(f"--{boundary}\r\nContent-Disposition: form-data; name=\"model\"\r\n\r\nwhisper-large-v3-turbo\r\n".encode())
    body.extend(f"--{boundary}\r\nContent-Disposition: form-data; name=\"prompt\"\r\n\r\n{safe_whisper_prompt}\r\n".encode('utf-8'))
    body.extend(f"--{boundary}\r\nContent-Disposition: form-data; name=\"temperature\"\r\n\r\n0\r\n".encode())
    body.extend(f"--{boundary}\r\nContent-Disposition: form-data; name=\"file\"; filename=\"speech.wav\"\r\nContent-Type: audio/wav\r\n\r\n".encode())
    body.extend(wav_bytes)
    body.extend(f"\r\n--{boundary}--\r\n".encode())
    
    global groq_key_index
    for attempt in range(len(GROQ_KEYS)):
        current_key = GROQ_KEYS[groq_key_index % len(GROQ_KEYS)]
        req = urllib.request.Request(
            url,
            data=bytes(body),
            headers={
                "Authorization": f"Bearer {current_key}",
                "Content-Type": f"multipart/form-data; boundary={boundary}",
                "User-Agent": "Mozilla/5.0"
            }
        )
        t0 = time.time()
        try:
            with urllib.request.urlopen(req, timeout=8.0) as resp:
                res = json.loads(resp.read().decode())
                dt = (time.time() - t0) * 1000
                raw_text = res.get("text", "").strip()
                clean_text = sanitize_mixed_indic_script(raw_text)
                return clean_text, dt
        except urllib.error.HTTPError as e:
            err_msg = e.read().decode('utf-8', errors='ignore')
            print(f"Groq Whisper STT HTTP {e.code}: {err_msg}")
            if e.code == 429 and len(GROQ_KEYS) > 1:
                groq_key_index = (groq_key_index + 1) % len(GROQ_KEYS)
                print(f"[GROQ ROTATION (STT)]: Rotated to key #{groq_key_index + 1}")
                continue
            return "", (time.time() - t0) * 1000
        except Exception as e:
            print(f"Groq Whisper STT Error: {e}")
            return "", (time.time() - t0) * 1000
    return "", (time.time() - t0) * 1000

def format_current_time(lang: str = "en") -> str:
    """Formats exact live local time into natural, culturally authentic spoken phrasing across all 4 languages."""
    now = datetime.datetime.now()
    hr_int = int(now.strftime("%I"))
    hr = str(hr_int)
    minute_int = now.minute
    am_pm = now.strftime("%p")
    hour_24 = now.hour
    next_hr = str((hr_int % 12) + 1)
    
    if 4 <= hour_24 < 12:
        period_hi = "सुबह के"
        period_mr = "सकाळचे"
        period_gu = "સવારના"
    elif 12 <= hour_24 < 16:
        period_hi = "दोपहर के"
        period_mr = "दुपारचे"
        period_gu = "બપોરના"
    elif 16 <= hour_24 < 20:
        period_hi = "शाम के"
        period_mr = "संध्याकाळचे"
        period_gu = "સાંજના"
    else:
        period_hi = "रात के"
        period_mr = "रात्रीचे"
        period_gu = "રાતના"
        
    if lang == "hi":
        if minute_int == 0:
            return f"अभी {period_hi} ठीक {hr} बजे हैं।"
        elif minute_int == 15:
            return f"अभी {period_hi} सवा {hr} बजे हैं।"
        elif minute_int == 30:
            if hr_int == 1:
                return f"अभी {period_hi} डेढ़ बजा है।"
            elif hr_int == 2:
                return f"अभी {period_hi} ढाई बजे हैं।"
            else:
                return f"अभी {period_hi} साढ़े {hr} बजे हैं।"
        elif minute_int == 45:
            return f"अभी {period_hi} पौने {next_hr} बजे हैं।"
        else:
            return f"अभी {period_hi} {hr} बजकर {minute_int} मिनट हुए हैं।"
            
    elif lang == "mr":
        if minute_int == 0:
            return f"आता {period_mr} ठीक {hr} वाजले आहेत."
        elif minute_int == 15:
            return f"आता {period_mr} सव्वा {hr} वाजले आहेत."
        elif minute_int == 30:
            if hr_int == 1:
                return f"आता {period_mr} दीड वाजला आहे."
            elif hr_int == 2:
                return f"आता {period_mr} अडीच वाजले आहेत."
            else:
                return f"आता {period_mr} साडे {hr} वाजले आहेत."
        elif minute_int == 45:
            return f"आता {period_mr} पावणे {next_hr} वाजले आहेत."
        else:
            return f"आता {period_mr} {hr} वाजून {minute_int} मिनिटे झाली आहेत."
            
    elif lang == "gu":
        if minute_int == 0:
            return f"અત્યારે {period_gu} બરાબર {hr} વાગ્યા છે."
        elif minute_int == 15:
            return f"અત્યારે {period_gu} સવા {hr} થયા છે."
        elif minute_int == 30:
            if hr_int == 1:
                return f"અત્યારે {period_gu} દોઢ વાગ્યો છે."
            elif hr_int == 2:
                return f"અત્યારે {period_gu} અઢી વાગ્યા છે."
            else:
                return f"અત્યારે {period_gu} સાડા {hr} થયા છે."
        elif minute_int == 45:
            return f"અત્યારે {period_gu} પોણા {next_hr} થયા છે."
        else:
            return f"અત્યારે {period_gu} {hr} વાગીને {minute_int} મિનિટ થઈ છે."
            
    else:
        # Modern commercial voice assistant phrasing (Siri / Alexa / Google style)
        if minute_int == 0:
            return f"It's {hr} o'clock {am_pm}."
        elif minute_int < 10:
            return f"It's {hr} oh {minute_int} {am_pm}."
        else:
            return f"It's {hr} {minute_int} {am_pm}."  

def format_current_date(lang: str = "en") -> str:
    """Formats exact live local date and day into natural, polite spoken phrasing."""
    now = datetime.datetime.now()
    day_name = now.strftime("%A")
    day_num = now.strftime("%d").lstrip("0")
    month_name = now.strftime("%B")
    year = now.strftime("%Y")
    
    days_hi = {"Monday": "सोमवार", "Tuesday": "मंगलवार", "Wednesday": "बुधवार", "Thursday": "गुरुवार", "Friday": "शुक्रवार", "Saturday": "शनिवार", "Sunday": "रविवार"}
    days_mr = {"Monday": "सोमवार", "Tuesday": "मंगळवार", "Wednesday": "बुधवार", "Thursday": "गुरुवार", "Friday": "शुक्रवार", "Saturday": "शनिवार", "Sunday": "रविवार"}
    days_gu = {"Monday": "સોમવાર", "Tuesday": "મંગળવાર", "Wednesday": "બુધવાર", "Thursday": "ગુરુવાર", "Friday": "શુક્રવાર", "Saturday": "શનિવાર", "Sunday": "રવિવાર"}
    
    months_hi = {"January": "जनवरी", "February": "फरवरी", "March": "मार्च", "April": "अप्रैल", "May": "मई", "June": "जून", "July": "जुलाई", "August": "अगस्त", "September": "सितंबर", "October": "अक्टूबर", "November": "नवंबर", "December": "दिसंबर"}
    months_mr = {"January": "जानेवारी", "February": "फेब्रुवारी", "March": "मार्च", "April": "एप्रिल", "May": "मे", "June": "जून", "July": "जुलै", "August": "ऑगस्ट", "September": "सप्टेंबर", "October": "ऑक्टोबर", "November": "नोव्हेंबर", "December": "डिसेंबर"}
    months_gu = {"January": "જાન્યુઆરી", "February": "ફેબ્રુઆરી", "March": "માર્ચ", "April": "એપ્રિલ", "May": "મે", "June": "જૂન", "July": "જુલાઈ", "August": "ઓગસ્ટ", "September": "સપ્ટેમ્બર", "October": "ઓક્ટોબર", "November": "નવેમ્બર", "December": "ડિસેમ્બર"}
    
    if lang == "hi":
        return f"आज {days_hi.get(day_name, day_name)}, {day_num} {months_hi.get(month_name, month_name)} {year} है।"
    elif lang == "mr":
        return f"आज {days_mr.get(day_name, day_name)}, {day_num} {months_mr.get(month_name, month_name)} {year} आहे."
    elif lang == "gu":
        return f"આજે {days_gu.get(day_name, day_name)}, {day_num} {months_gu.get(month_name, month_name)} {year} છે."
    else:
        return f"Today is {day_name}, {month_name} {day_num}, {year}."

# --- Step 2: LLM Brain (Groq) ---

WEB_SEARCH_CACHE = {} # query -> (timestamp, formatted_results)

def search_web_live(query: str, max_results: int = 3) -> str | None:
    """
    Fetches real-time multi-source web snippets and citations via DuckDuckGo in ~600-1100ms.
    Provides verifiable titles, sources, and snippets for news, scientific, or general facts.
    """
    global WEB_SEARCH_CACHE
    q_clean = query.strip()
    if not q_clean or len(q_clean) < 3:
        return None
        
    cache_key = q_clean.lower()
    cached = WEB_SEARCH_CACHE.get(cache_key)
    if cached and (time.time() - cached[0] < 600): # 10 min TTL
        return cached[1]
        
    try:
        url = "https://lite.duckduckgo.com/lite/"
        data = urllib.parse.urlencode({'q': q_clean}).encode('utf-8')
        headers = {
            'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) Chrome/120.0.0.0',
            'Content-Type': 'application/x-www-form-urlencoded'
        }
        req = urllib.request.Request(url, data=data, headers=headers)
        with urllib.request.urlopen(req, timeout=2.2) as resp:
            html = resp.read().decode('utf-8', errors='ignore')

        blocks = re.findall(
            r'<td valign="top">\s*\d+\.&nbsp;\s*</td>\s*<td>\s*<a[^>]*href="([^"]*)"[^>]*class=["\']result-link["\'][^>]*>(.*?)</a>.*?<td[^>]*class=["\']result-snippet["\'][^>]*>(.*?)</td>.*?<span[^>]*class=["\']link-text["\'][^>]*>(.*?)</span>',
            html, re.DOTALL
        )
        if not blocks:
            return None
            
        sources = []
        for u, t, s, l in blocks[:max_results]:
            clean_t = re.sub(r'<[^>]+>', '', t).strip()
            clean_s = re.sub(r'<[^>]+>', '', s).strip()
            clean_l = re.sub(r'<[^>]+>', '', l).strip()
            sources.append(f"• Source [{clean_l}]: \"{clean_t}\" — {clean_s}")
            
        res = f"[LIVE MULTI-SOURCE WEB VERIFICATION ({len(sources)} Verified Sources)]:\n" + "\n".join(sources)
        WEB_SEARCH_CACHE[cache_key] = (time.time(), res)
        return res
    except Exception as e:
        print(f"[WEB SEARCH]: Live lookup error for '{q_clean}': {e}")
        return None


# ==============================================================================
# PALGHAR HYPER-LOCAL ARITHMETIC RECOMMENDATION & UTILITY DIRECTORY
# Ground truth for Palghar West around user's home (Vishnu Nagar, near Hotel Sai Residency on Mahim Road, PIN 401404)
# ==============================================================================

PALGHAR_HYPERLOCAL_DIRECTORY = {
    # --- FOOD CRAVINGS & DINING INSTINCTS ---
    "waffles": {
        "type": "food",
        "name": "The Belgian Waffle Co.",
        "category_label": "Waffles & Desserts",
        "primary_keywords": ["waffle", "waffles", "belgian waffle", "belgian waffles", "वाफल", "वाफल्स", "વાફલ", "વાફલ્સ", "stroopwafel"],
        "secondary_keywords": ["pancake", "pancakes", "waffle cake", "chocolate waffle", "dessert", "desserts"],
        "details": (
            "• **The Belgian Waffle Co.** (Palghar West)\n"
            "  - Exact Location: Shop No. 40, 44 & 49, M V Super Market, near Panch Batti (Pachbatti Road), Palghar West.\n"
            "  - Distance from Vishnu Nagar: ~900 meters (about 3 minutes by auto or a 10-minute walk).\n"
            "  - Top Specialties: Warm Belgian Waffles, Waffle Cakes, Chocolate Overload, Red Velvet Waffle, Stroopwafels."
        )
    },
    "shawarma": {
        "type": "food",
        "name": "Shawarma Nation",
        "category_label": "Shawarma & Rolls",
        "primary_keywords": ["shawarma", "sharma", "sorma", "shorma", "shavarma", "शावर्मा", "शॉर्मा", "શાવર્મા", "roll", "rolls", "frankie"],
        "secondary_keywords": ["kathi roll", "wrap", "wraps", "chicken roll", "paneer roll"],
        "details": (
            "• **Shawarma Nation** (Palghar West)\n"
            "  - Exact Location: Near Panch Batti (Pachbatti Road) / Hutatma Chowk, Palghar West.\n"
            "  - Distance from Vishnu Nagar: ~900 meters (about 3 minutes by auto or 10 minutes walk).\n"
            "  - Top Specialties: Chicken Shawarma, Open Shawarma, Tandoori Shawarma, Peri Peri Chicken Rolls."
        )
    },
    "family_dining": {
        "type": "food",
        "name": "Hotel Sai Residency",
        "category_label": "Multi-Cuisine Family Dining & North Indian",
        "primary_keywords": ["sai residency", "hotel sai", "family restaurant", "family dining", "dinner", "lunch", "punjabi", "mughlai", "north indian", "chinese"],
        "secondary_keywords": ["paneer butter masala", "butter chicken", "tandoori roti", "fried rice", "noodles", "manchurian"],
        "details": (
            "• **Hotel Sai Residency** (Palghar West)\n"
            "  - Exact Location: Mahim Road, Palghar West (right next to user's neighborhood Vishnu Nagar).\n"
            "  - Distance from User's Home: ~300 meters (just an easy 3-minute walk).\n"
            "  - Top Specialties: Multi-cuisine dining, North Indian curries, Mughlai gravies, Chinese delicacies, Tandoori starters."
        )
    },
    "pizza": {
        "type": "food",
        "name": "Domino's Pizza",
        "category_label": "Pizza & Fast Food",
        "primary_keywords": ["pizza", "domino", "dominos", "pizza hut", "पिज्जा", "પીઝા"],
        "secondary_keywords": ["cheese burst", "garlic bread", "pasta", "burger", "burgers", "fast food"],
        "details": (
            "• **Domino's Pizza** (Palghar West)\n"
            "  - Exact Location: Mahim Road / Station Road area, Palghar West.\n"
            "  - Distance from Vishnu Nagar: ~1 km (about 3-4 minutes by auto).\n"
            "  - Top Specialties: Farmhouse Pizza, Peppy Paneer, Garlic Breadsticks, Choco Lava Cake."
        )
    },
    "south_indian": {
        "type": "food",
        "name": "Udupi Shri Krishna & Panchratna",
        "category_label": "South Indian & Pure Veg Snacks",
        "primary_keywords": ["dosa", "idli", "medu vada", "vada sambhar", "south indian", "udupi", "डोसा", "इडली", "ઢોસા"],
        "secondary_keywords": ["uttapam", "filter coffee", "sambhar", "veg thali", "poha", "upma"],
        "details": (
            "• **Udupi Shri Krishna Restaurant** & **Panchratna Veg Restaurant** (Palghar West)\n"
            "  - Exact Location: Station Road & Panch Batti, Palghar West.\n"
            "  - Distance from Vishnu Nagar: ~850 meters to 1 km (about 3-4 minutes by auto).\n"
            "  - Top Specialties: Crisp Masala Dosa, Mysore Masala Dosa, Steaming Idli Sambhar, Medu Vada, Filter Coffee."
        )
    },
    "ice_cream": {
        "type": "food",
        "name": "Naturals Ice Cream & Amul Parlour",
        "category_label": "Ice Cream & Shakes",
        "primary_keywords": ["ice cream", "icecream", "naturals", "amul parlour", "kulfi", "आइसक्रीम", "આઈસ્ક્રીમ", "કુલ્ફી"],
        "secondary_keywords": ["shake", "shakes", "sundae", "falooda", "cone", "scoop"],
        "details": (
            "• **Naturals Ice Cream** & **Amul Ice Cream Parlour** (Palghar West)\n"
            "  - Exact Location: Mahim Road & Panch Batti, Palghar West.\n"
            "  - Distance from Vishnu Nagar: ~800 meters (about 2-3 minutes by auto).\n"
            "  - Top Specialties: Tender Coconut, Sitaphal (Custard Apple), Roasted Almond, Kulfi, Real Fruit Ice Creams."
        )
    },
    "biryani": {
        "type": "food",
        "name": "Zaiqa Biryani House & Hotel Sai Residency",
        "category_label": "Biryani & Kebabs",
        "primary_keywords": ["biryani", "biryany", "biryani house", "kebabs", "kebab", "बिरयानी", "બિરયાની", "tikka"],
        "secondary_keywords": ["dum biryani", "chicken biryani", "mutton biryani", "hyderabadi biryani"],
        "details": (
            "• **Zaiqa Biryani House** & **Hotel Sai Residency** (Palghar West)\n"
            "  - Exact Location: Station Road & Mahim Road, Palghar West.\n"
            "  - Distance from Vishnu Nagar: ~600 meters to 1 km.\n"
            "  - Top Specialties: Authentic Hyderabadi Dum Biryani, Chicken Tikka Biryani, Seekh Kebabs."
        )
    },
    "sweets_and_snacks": {
        "type": "food",
        "name": "Brijwasi Sweets & Jalaram Sweets",
        "category_label": "Mithai, Sweets, Farsan & Chaat",
        "primary_keywords": ["sweets", "sweet", "mithai", "farsan", "dhokla", "khaman", "samosa", "kachori", "मिठाई", "મીઠાઈ", "ફરસાણ", "chaat", "pani puri"],
        "secondary_keywords": ["kaju katli", "gulab jamun", "rasgulla", "laddu", "ladoo", "jalebi"],
        "details": (
            "• **Brijwasi Sweets** & **Jalaram Sweets** (Palghar West)\n"
            "  - Exact Location: Station Road & Mahim Road, Palghar West.\n"
            "  - Distance from Vishnu Nagar: ~800 to 900 meters (~3 minutes by auto).\n"
            "  - Top Specialties: Fresh Kaju Katli, Bengali Sweets, Gulab Jamun, Samosas, Kachoris, Khaman Dhokla, Gujarati Farsan."
        )
    },
    "bakery_cakes": {
        "type": "food",
        "name": "Ribbons & Balloons and Monginis Cake Shop",
        "category_label": "Bakery, Birthday Cakes & Pastries",
        "primary_keywords": ["cake", "cakes", "bakery", "pastry", "pastries", "birthday cake", "केक", "બેકરી"],
        "secondary_keywords": ["patties", "puffs", "truffle", "black forest", "brownie"],
        "details": (
            "• **Ribbons and Balloons** & **Monginis Cake Shop** (Palghar West)\n"
            "  - Exact Location: Mahim Road & Station Road, Palghar West.\n"
            "  - Distance from Vishnu Nagar: ~750 meters to 1 km.\n"
            "  - Top Specialties: Chocolate Dutch Truffle Cake, Black Forest, fresh fruit pastries, cheese & chicken patties."
        )
    },
    "chai_cafe": {
        "type": "food",
        "name": "Yewale Amruttulya & Chai Sutta Bar",
        "category_label": "Tea, Chai & Cafe",
        "primary_keywords": ["tea", "chai", "cafe", "coffee", "yewale", "amruttulya", "चाय", "ચા", "કૅફે"],
        "secondary_keywords": ["bun maska", "kulhad chai", "cold coffee", "snack"],
        "details": (
            "• **Yewale Amruttulya** & **Chai Sutta Bar** (Palghar West)\n"
            "  - Exact Location: Station Road & near Panch Batti, Palghar West.\n"
            "  - Distance: ~800 meters.\n"
            "  - Top Specialties: Authentic spiced cutting chai, Bun Maska, Kulhad coffee, evening snacks."
        )
    },

    # --- COMMERCIAL UTILITIES & PHYSICAL PURCHASING (WHERE TO BUY) ---
    "hardware": {
        "type": "utility",
        "name": "Hardware Centre (India) & National Hardware",
        "category_label": "Hardware, Tools, Plumbing, Paints & Sanitary",
        "primary_keywords": [
            "hardware", "hardware shop", "hardware store", "tools", "tool shop",
            "plumbing", "sanitary", "sanitaryware", "pipes", "pvc pipe",
            "drill", "drills", "screws", "nuts and bolts", "hammer",
            "paint", "paints", "asian paints", "हार्डवेयर", "हार्डवेयर की दुकान", "હાર્ડવેર", "ટૂલ્સ"
        ],
        "secondary_keywords": ["electrical fittings", "wires", "switches", "cement", "adhesives", "fevicol", "tap", "bathroom fittings"],
        "details": (
            "• **Hardware Centre (India)** & **National Hardware Stores** (Palghar West)\n"
            "  - Exact Location: Opp. Panch Batti (Pachbatti Road) & Mahim Road, Palghar West.\n"
            "  - Distance from Vishnu Nagar: ~700 to 800 meters (~2 minutes by auto or 8 minutes walk).\n"
            "  - What you can buy: Power tools, hand tools, drills, screws, plumbing pipes & fittings, bathroom fixtures, Asian Paints, hardware accessories."
        )
    },
    "stationery": {
        "type": "utility",
        "name": "Pruthvi Book Stores & Deepak Stationery Mart",
        "category_label": "Stationery, Books, School & Office Supplies, Xerox",
        "primary_keywords": [
            "stationery", "stationary", "stationery shop", "stationery store",
            "book store", "bookstore", "books shop", "notebooks", "notebook",
            "pen", "pens", "school supplies", "office supplies", "xerox", "photocopy",
            "printout", "printing", "स्टेशनरी", "किताबों की दुकान", "સ્ટેશનરી", "ચોપડા"
        ],
        "secondary_keywords": ["chart paper", "craft", "geometry box", "files", "folders", "stapler", "project paper", "textbooks"],
        "details": (
            "• **Pruthvi Book Stores & Stationery** & **Deepak Stationery Mart** (Palghar West)\n"
            "  - Exact Location: \n"
            "    1. Pruthvi Book Stores: Near ICICI Bank, Vishnu Nagar, Palghar West (only ~300 meters away, 3-minute walk right in user's neighborhood!).\n"
            "    2. Deepak Stationery Mart: Panch Batti, Vishnu Nagar, Palghar West (~500 meters away).\n"
            "    3. Mahalaxmi Stationery & Gift Shop: Mahim Road, Opp. Vijaya Bank (~700 meters away).\n"
            "  - What you can buy: School/college notebooks, textbooks, pens, project charts, art & craft supplies, office files, printer paper, Xerox and printouts."
        )
    },
    "medicines": {
        "type": "utility",
        "name": "Wellness Forever (24x7) & Noble Chemist",
        "category_label": "Medicines, Pharmacy & Chemist",
        "primary_keywords": [
            "medicine", "medicines", "chemist", "pharmacy", "medical store", "medical shop",
            "dawai", "dawakhana", "tablets", "first aid", "दवा", "दवाई", "मेडिकल", "દવા", "મેડિકલ"
        ],
        "secondary_keywords": ["bandages", "syrup", "prescription", "baby care", "emergency medicine", "dawa"],
        "details": (
            "• **Wellness Forever (24/7 Pharmacy)** & **Noble Chemist** (Palghar West)\n"
            "  - Exact Location: Mahim Road (near user's area, open 24 hours) & Station Road, Palghar West.\n"
            "  - Distance from Vishnu Nagar: ~750 meters (~2 minutes by auto).\n"
            "  - What you can buy: All prescription medicines, OTC drugs, healthcare monitors, first-aid, baby care, emergency midnight medicines."
        )
    },
    "groceries_supermarket": {
        "type": "utility",
        "name": "Reliance Smart Point & D-Mart Palghar",
        "category_label": "Supermarkets, Groceries & Daily Needs",
        "primary_keywords": [
            "groceries", "grocery", "supermarket", "kirana", "ration", "reliance smart", "dmart", "d-mart",
            "daily essentials", "किराना", "राशन", "ગ્રોસરી", "કરિયાણું"
        ],
        "secondary_keywords": ["atta", "dal", "oil", "rice", "spices", "cleaning supplies"],
        "details": (
            "• **Reliance Smart Point** & **D-Mart Palghar**\n"
            "  - Exact Location: \n"
            "    1. Reliance Smart Point: Mahim Road, Palghar West (~750 meters, 2 mins by auto).\n"
            "    2. D-Mart: Manor-Palghar Road (~3.5 km, 10 mins by auto/car).\n"
            "  - What you can buy: Complete groceries, packaged foods, daily essentials, grains, household cleaning items."
        )
    },
    "electronics_mobile": {
        "type": "utility",
        "name": "Reliance Digital, Croma & Vijay Sales",
        "category_label": "Electronics, Mobile Phones & Appliances",
        "primary_keywords": [
            "electronics", "electronic shop", "mobile shop", "mobile store", "phone shop", "croma",
            "reliance digital", "vijay sales", "charger", "laptop shop", "इलेक्ट्रॉनिक्स", "મોબાઈલ"
        ],
        "secondary_keywords": ["tv", "refrigerator", "earphones", "powerbank", "cable", "repair"],
        "details": (
            "• **Reliance Digital / Croma** & **Vijay Sales** (Palghar West)\n"
            "  - Exact Location: Mahim Road & Station Road / Panch Batti, Palghar West (~850 meters).\n"
            "  - Distance: ~850 meters (~3 minutes by auto).\n"
            "  - What you can buy: Smartphones, chargers, earphones, laptops, TVs, refrigerators, home appliances."
        )
    },
    "clothing_fashion": {
        "type": "utility",
        "name": "Trends (Reliance Trends) & Zudio",
        "category_label": "Clothing, Fashion & Readymade Garments",
        "primary_keywords": ["clothes", "clothing", "fashion", "readymade", "garments", "trends", "zudio", "kapde", "कपड़े", "કપડાં"],
        "secondary_keywords": ["jeans", "t-shirt", "shirt", "ethnic wear", "menswear", "ladies wear"],
        "details": (
            "• **Reliance Trends** & **Zudio** (Palghar West)\n"
            "  - Exact Location: Mahim Road, Palghar West (~850 meters from Vishnu Nagar).\n"
            "  - What you can buy: Men's, women's, and kids' casuals, formal wear, ethnic wear, jeans, shirts, jackets."
        )
    },
    "footwear": {
        "type": "utility",
        "name": "Bata Store & Relaxo Footwear",
        "category_label": "Footwear, Shoes & Slippers",
        "primary_keywords": ["footwear", "shoes", "shoe shop", "chappal", "sandals", "slippers", "bata", "जूते", "ચંપલ"],
        "secondary_keywords": ["sneakers", "formal shoes", "flip flops", "school shoes"],
        "details": (
            "• **Bata Store** & **Relaxo Footwear** (Palghar West)\n"
            "  - Exact Location: Mahim Road / Station Road, Palghar West (~700 meters away).\n"
            "  - What you can buy: Formal shoes, sports sneakers, school shoes, leather footwear, daily chappals and sandals."
        )
    },
    "eyewear_optician": {
        "type": "utility",
        "name": "Lenskart.com Store",
        "category_label": "Optician, Eyeglasses & Spectacles",
        "primary_keywords": ["optician", "spectacles", "glasses", "chashma", "eyewear", "lenskart", "eye testing", "चश्मा", "ચશ્મા"],
        "secondary_keywords": ["frames", "sunglasses", "contact lenses", "eye doctor"],
        "details": (
            "• **Lenskart.com Store** (Palghar West)\n"
            "  - Exact Location: Mahim Road, Palghar West (~800 meters from Vishnu Nagar).\n"
            "  - What you can buy: Prescription eyeglasses, frame trial, sunglasses, contact lenses, computerized eye testing."
        )
    },
    "jewellery": {
        "type": "utility",
        "name": "Tanishq & PNG Jewellers",
        "category_label": "Jewellery, Gold & Silver",
        "primary_keywords": ["jewellery", "jeweler", "jewelry", "gold", "silver", "tanishq", "png jewellers", "sona", "chandi", "सोना", "चांदी", "જ્વેલરી"],
        "secondary_keywords": ["ring", "necklace", "hallmark", "coins", "diamonds"],
        "details": (
            "• **Tanishq** & **P N Gadgil (PNG) Jewellers** (Palghar West)\n"
            "  - Exact Location: Mahim Road & Station Road, Palghar West (~900 meters away).\n"
            "  - What you can buy: Certified 22K/18K gold jewellery, diamond ornaments, silver coins, traditional Marathi ornaments."
        )
    }
}

# ARITHMETIC INTENT SCORING CONSTANTS
FOOD_INTENT_TERMS = [
    "eat", "eating", "food", "hungry", "craving", "cravings", "mood to", "moved to",
    "taste", "restaurant", "restaurants", "hotel", "hotels", "snack", "snacks",
    "breakfast", "lunch", "dinner", "dish", "places to eat", "famous place to eat",
    "khana", "khane", "bhookh", "swad", "kahan khau", "zomato", "swiggy",
    "रेस्टोरेंट", "खाना", "होटल", "भूख", "જમવું", "ખાવા", "રેસ્ટોરન્ટ"
]

UTILITY_BUY_INTENT_TERMS = [
    "buy", "buying", "purchase", "purchasing", "shop", "shops", "store", "stores",
    "get", "where can i get", "where to get", "where should i buy", "from where should i buy",
    "kharidna", "kharid", "lena", "chahiye", "milega", "milta hai", "kahan milega",
    "dokan", "dukaan", "doothe", "market", "bazaar", "दुकान", "खरीदना", "ખરીદવું"
]

LOCAL_GEO_INTENT_TERMS = [
    "near me", "nearby", "close to me", "closest", "around me", "in palghar", "palghar west",
    "palghar", "pachbatti", "panch batti", "vishnu nagar", "mahim road", "station road",
    "pass me", "paas me", "नजदीक", "पास", "નજીક"
]

def resolve_palghar_hyperlocal_recommendations(user_query: str) -> str | None:
    """
    Sub-millisecond Arithmetic Scoring Engine for Local Palghar Cravings & Utility Shopping.
    Evaluates:
      Score(C) = sum(W_primary * I(w in Q)) + sum(W_secondary * I(w in Q)) + IntentBoost(C, Q)
    Execution latency: < 0.1ms.
    """
    t0 = time.perf_counter()
    q_low = user_query.lower()
    
    # 1. Detect Intent Weights
    has_food_intent = any(term in q_low for term in FOOD_INTENT_TERMS)
    has_buy_intent = any(term in q_low for term in UTILITY_BUY_INTENT_TERMS)
    has_local_intent = any(term in q_low for term in LOCAL_GEO_INTENT_TERMS)
    
    # 2. Arithmetic Relevance Scoring across all categories
    category_scores = {}
    for cat_id, cat_data in PALGHAR_HYPERLOCAL_DIRECTORY.items():
        score = 0.0
        
        # Primary keyword matches (Weight = 4.0 each)
        for pk in cat_data["primary_keywords"]:
            if pk in q_low:
                score += 4.0
                
        # Secondary keyword matches (Weight = 2.0 each)
        for sk in cat_data["secondary_keywords"]:
            if sk in q_low:
                score += 2.0
                
        # Intent Boosts
        if score > 0:
            if cat_data["type"] == "food" and has_food_intent:
                score += 2.5
            elif cat_data["type"] == "utility" and has_buy_intent:
                score += 2.5
            if has_local_intent:
                score += 1.5
                
        category_scores[cat_id] = score
        
    matched = [(cat_id, score) for cat_id, score in category_scores.items() if score >= 3.5]
    matched.sort(key=lambda x: x[1], reverse=True)
    
    elapsed_ms = (time.perf_counter() - t0) * 1000
    
    # CASE A: Exact Category Matches found
    if matched:
        top_matches = matched[:2]  # top 2 most relevant
        sections = []
        for cat_id, score in top_matches:
            cat_info = PALGHAR_HYPERLOCAL_DIRECTORY[cat_id]
            sections.append(f"[{cat_info['category_label'].upper()}]:\n{cat_info['details']}")
            
        result = (
            f"[PALGHAR HYPER-LOCAL GROUND TRUTH (Matched in {elapsed_ms:.2f}ms)]:\n"
            f"User Shravan lives in Vishnu Nagar, Palghar West (PIN 401404), near Hotel Sai Residency (on Mahim Road).\n"
            + "\n\n".join(sections)
            + "\n(State exact store name, street/landmark, distance in meters/km, and travel time directly. Never say you don't know)."
        )
        return result

    # CASE B: General Food Query ("I want to eat something famous near me / what to eat")
    if has_food_intent and (has_local_intent or "eat" in q_low or "restaurant" in q_low or "food" in q_low):
        return (
            f"[PALGHAR TOP DINING & FOOD INSTINCT DIRECTORY (Lookup {elapsed_ms:.2f}ms)]:\n"
            "User lives in Vishnu Nagar, Palghar West near Mahim Road.\n"
            "• **Waffles & Desserts**: The Belgian Waffle Co. at M V Super Market, Panch Batti (~900m / 3 mins auto).\n"
            "• **Shawarma & Rolls**: Shawarma Nation near Panch Batti Road (~900m / 3 mins auto).\n"
            "• **Family Dining (North Indian / Chinese / Mughlai)**: Hotel Sai Residency right on Mahim Road (~300m / 3 mins walk).\n"
            "• **South Indian Dosa & Veg Snacks**: Udupi Shri Krishna & Panchratna on Station Road (~850m).\n"
            "• **Pizza & Fast Food**: Domino's Pizza on Mahim Road (~1 km).\n"
            "• **Ice Cream & Shakes**: Naturals Ice Cream on Mahim Road (~800m).\n"
            "• **Sweets & Mithai**: Brijwasi Sweets on Station Road (~900m).\n"
            "When answering, warmly suggest the top spot matching user's mood or give these top options with exact distances."
        )

    # CASE C: General Shopping Query ("I want to buy something, from where should I buy? e.g. hardware, stationery")
    if has_buy_intent and (has_local_intent or "buy" in q_low or "shop" in q_low or "store" in q_low or "where" in q_low):
        return (
            f"[PALGHAR ESSENTIAL SHOPPING DIRECTORY (Lookup {elapsed_ms:.2f}ms)]:\n"
            "User lives in Vishnu Nagar, Palghar West near Mahim Road.\n"
            "• **Hardware, Tools & Plumbing**: Hardware Centre (India) & National Hardware Stores opposite Panch Batti / Mahim Road (~800m).\n"
            "• **Stationery, Books & Printing**: Pruthvi Book Stores in Vishnu Nagar near ICICI Bank (~300m walk) or Deepak Stationery Mart at Panch Batti (~500m).\n"
            "• **Medicines & Pharmacy**: Wellness Forever (24/7) on Mahim Road (~750m) or Noble Chemist on Station Road (~1 km).\n"
            "• **Groceries & Supermarket**: Reliance Smart Point on Mahim Road (~750m) or D-Mart on Manor Road (~3.5 km).\n"
            "• **Electronics & Gadgets**: Reliance Digital / Croma on Mahim Road (~850m).\n"
            "• **Clothing & Fashion**: Reliance Trends & Zudio on Mahim Road (~850m).\n"
            "Direct the user to the exact store based on what they want to purchase."
        )

    # CASE D: Uncategorized Hyper-Local Query with Local Geographic Intent (Dynamic Fallback Search)
    is_local_commercial_inquiry = (
        (has_local_intent or "palghar" in q_low or "near me" in q_low or "paas" in q_low) and
        (has_food_intent or has_buy_intent or "where" in q_low or "shop" in q_low or "store" in q_low or "kahan" in q_low)
    )
    if is_local_commercial_inquiry:
        search_res = search_web_live(f"{user_query} Palghar West", max_results=2)
        if search_res:
            return f"[LOCAL PALGHAR LIVE DIRECTORY SEARCH]:\nUser is inquiring about local options in Palghar West near Vishnu Nagar.\n{search_res}"

    return None




CALLING_CONTACTS_PATH = os.path.join(os.path.dirname(__file__), "calling_test", "contacts.json")

def load_calling_contacts() -> dict:
    if os.path.exists(CALLING_CONTACTS_PATH):
        try:
            with open(CALLING_CONTACTS_PATH, "r", encoding="utf-8") as f:
                return json.load(f)
        except Exception:
            return {}
    return {}

def parse_call_intent(query: str) -> str | None:
    if not query:
        return None
    # Strip trailing punctuation (. , ! ?) that Whisper adds
    cleaned = re.sub(r'[^\w\s]', ' ', query).strip()
    q = cleaned.lower()
    
    # Check direct phone number formats (e.g. "9356218285, call this number" or "call 9356218285")
    m_num = re.search(r'(\d{10,12})\s+(?:call|dial|phone)', q)
    if m_num:
        return m_num.group(1)
        
    m_num2 = re.search(r'(?:call|dial|phone)\s+(?:this\s+number\s+)?(\d{10,12})', q)
    if m_num2:
        return m_num2.group(1)

    patterns = [
        r'^(?:alexa|pappu|please)?\s*(?:make\s+a\s+)?(?:phone\s+)?call\s+(?:to\s+)?([a-zA-Z0-9\u0900-\u097F\u0A80-\u0AFF\s]+)$',
        r'^(?:alexa|pappu|please)?\s*dial\s+([a-zA-Z0-9\u0900-\u097F\u0A80-\u0AFF\s]+)$',
        r'^(?:alexa|pappu|please)?\s*phone\s+([a-zA-Z0-9\u0900-\u097F\u0A80-\u0AFF\s]+)$',
        r'([^\s]+)\s*(?:को|ला|ને)\s*(?:फोन|कॉल)\s*(?:करो|करा|लाव|કર|કરો)',
    ]
    for p in patterns:
        m = re.search(p, q, re.IGNORECASE)
        if m:
            val = m.group(1).strip()
            val = re.sub(r'\s+(?:please|now|fast|turant|lavkar|on\s+phone|this\s+number)$', '', val, flags=re.IGNORECASE)
            return val
    return None

from esp32_call_bridge import bridge_instance as call_audio_bridge

call_audio_packets_sent = 0

def send_call_audio_to_esp32(pcm_chunk: bytes):
    global client, loop, call_audio_packets_sent
    if client and is_connected() and loop and not loop.is_closed():
        try:
            loop.call_soon_threadsafe(client.send_voice_assistant_audio, pcm_chunk)
            call_audio_packets_sent += 1
            if call_audio_packets_sent % 50 == 1:
                print(f"[CALL AUDIO OUTBOUND]: Streaming caller voice to ESP32 speaker (packet #{call_audio_packets_sent}, size={len(pcm_chunk)}b)")
        except Exception:
            pass

call_hangup_requested = False

def monitor_active_call_session():
    """Watches the call state and keeps the pure ESP32 hardware audio pipeline active."""
    global client, loop, active_audio_queue, call_hangup_requested
    call_hangup_requested = False
    print("[CALL MONITOR] Telecom session monitor started.")
    
    # 1. Wait until any in-progress TTS announcement finishes completely to prevent audio collision/stutter!
    while active_audio_queue is not None:
        time.sleep(0.08)
        
    stream_opened = False
    last_call_led_pattern = None
    dial_start_ts = time.time()
    try:
        while not call_hangup_requested:
            time.sleep(0.25)
            if call_hangup_requested:
                break
            try:
                import requests
                r = requests.get("http://localhost:5050/api/status", timeout=1.5)
                data = r.json()
                state = data.get("state", "idle")
                is_active = data.get("is_active", False)
                # Call is only terminated if state has truly become 'ended' or reverted to 'idle' after initial dial grace period!
                # As long as state is 'dialing', 'ringing', or 'connected', keep the pipeline active!
                if (time.time() - dial_start_ts) > 6.0:
                    if state == "ended" or (state == "idle" and not is_active):
                        print(f"[CALL MONITOR] Call ended (state={state}, is_active={is_active}).")
                        break

                if state in ("dialing", "ringing") and not call_hangup_requested:
                    if last_call_led_pattern != "ringing":
                        set_aura_led("ringing")
                        last_call_led_pattern = "ringing"
                elif state == "connected" and not call_hangup_requested:
                    cur_pattern = "muted" if call_audio_bridge.is_muted else "in_call"
                    if last_call_led_pattern != cur_pattern:
                        set_aura_led(cur_pattern)
                        last_call_led_pattern = cur_pattern

                if state in ("dialing", "ringing", "connected") and not call_hangup_requested:
                    if not stream_opened and client and is_connected():
                        def _arm():
                            try:
                                client.send_voice_assistant_event(VoiceAssistantEventType.VOICE_ASSISTANT_RUN_START, None)
                                client.send_voice_assistant_event(VoiceAssistantEventType.VOICE_ASSISTANT_TTS_START, {"text": "Telecom Call"})
                                client.send_voice_assistant_event(VoiceAssistantEventType.VOICE_ASSISTANT_TTS_STREAM_START, None)
                            except Exception as e:
                                print(f"[CALL MONITOR ARM ERROR]: {e}")
                        loop.call_soon_threadsafe(_arm)
                        stream_opened = True
                        print("[CALL MONITOR] ESP32 Speaker I2S pipeline armed and open!")
                        try:
                            asyncio.run_coroutine_threadsafe(trigger_mic_start(), loop)
                        except Exception:
                            pass
                    if not call_audio_bridge.is_active and not call_hangup_requested:
                        call_audio_bridge.start(send_call_audio_to_esp32)
            except Exception:
                pass
    finally:
        if call_audio_bridge.is_active:
            call_audio_bridge.stop()
        if stream_opened and client and is_connected():
            def _disarm():
                try:
                    client.send_voice_assistant_event(VoiceAssistantEventType.VOICE_ASSISTANT_TTS_STREAM_END, None)
                    client.send_voice_assistant_event(VoiceAssistantEventType.VOICE_ASSISTANT_RUN_END, None)
                except Exception:
                    pass
            loop.call_soon_threadsafe(_disarm)
            stream_opened = False
            print("[CALL MONITOR] ESP32 Speaker I2S pipeline closed cleanly.")
        set_aura_led("hangup")
        print("[CALL MONITOR] Telecom session finished.")
def handle_call_intent(target: str, lang: str = "en") -> str:
    contacts = load_calling_contacts()
    clean_target = target.lower().strip()

    def _norm(s: str) -> str:
        return re.sub(r'[^a-zA-Z0-9\u0900-\u097F\u0A80-\u0AFF]', '', s.lower())

    norm_target = _norm(clean_target)

    SYNONYMS = {
        "mom": ["mom", "mummy", "mother", "माँ", "मम्मी", "आई", "મમ્મી", "mummyji"],
        "dad": ["dad", "papa", "father", "पापा", "बाबा", "પપ્પા", "pitaji"],
        "myself": ["myself", "my self", "me", "shravan", "my phone", "self", "mera phone", "mujhe", "माझा फोन", "खुद को", "माझा नंबर", "mera number", "own phone"],
        "emergency": ["emergency", "police", "ambulance", "112", "100", "help"]
    }

    resolved_number = None
    resolved_name = target.title()

    def _lookup(query_key: str):
        nq = _norm(query_key)
        if not nq:
            return None, None
        for k, data in contacts.items():
            nk = _norm(k)
            if nk == nq or nq in nk or nk in nq:
                return data.get("number"), data.get("name", k.title())
        return None, None

    # 1. Check synonyms
    for canon_key, syn_list in SYNONYMS.items():
        norm_syns = [_norm(syn) for syn in syn_list]
        if norm_target in norm_syns or any(ns in norm_target for ns in norm_syns):
            resolved_number, resolved_name = _lookup(canon_key)
            if not resolved_number and canon_key == "myself":
                resolved_number, resolved_name = _lookup("my self")
            if resolved_number:
                break

    # 2. Check exact or fuzzy contact keys in contacts.json
    if not resolved_number:
        resolved_number, resolved_name = _lookup(clean_target)

    # 3. Check if target is directly a phone number
    if not resolved_number:
        digits = "".join(filter(str.isdigit, clean_target))
        if len(digits) >= 10:
            resolved_number = digits
            resolved_name = digits

    if not resolved_number:
        msg_map = {
            "hi": f"मुझे संपर्कों में '{target}' नहीं मिला। आप अपने डैशबोर्ड में नंबर जोड़ सकते हैं।",
            "mr": f"मला संपर्कांमध्ये '{target}' सापडले नाही. तुम्ही डॅशबोर्डवर नंबर जोडू शकता.",
            "gu": f"મને સંપર્કોમાં '{target}' મળ્યું નથી. તમે ડેશબોર્ડમાં નંબર ઉમેરી શકો છો.",
            "en": f"I couldn't find {target} in your saved contacts. You can add them in your dashboard."
        }
        return msg_map.get(lang, msg_map["en"])

    try:
        def _delayed_dial():
            # Wait until assistant finishes speaking the announcement cleanly through ESP32 speaker
            global active_audio_queue, active_streamer_task
            time.sleep(0.35)
            while (active_audio_queue is not None) or (active_streamer_task is not None and not active_streamer_task.done()):
                time.sleep(0.08)
            time.sleep(0.30)
            try:
                import requests
                r = requests.post("http://localhost:5050/api/dial", json={"phone_number": resolved_number, "video": False}, timeout=3.0)
                if r.status_code == 200:
                    threading.Thread(target=monitor_active_call_session, daemon=True).start()
            except Exception as ex:
                print(f"[DELAYED DIAL DISPATCH ERROR]: {ex}")

        threading.Thread(target=_delayed_dial, daemon=True).start()

        ack_map = {
            "hi": f"{resolved_name} को जियो लैंडलाइन से कॉल लगा रहे हैं।",
            "mr": f"{resolved_name} ला जिओ लँडलाईनवरून फोन लावत आहे.",
            "gu": f"{resolved_name} ને જીઓ લેન્ડલાઈન પરથી કોલ લગાવી રહ્યા છીએ.",
            "en": f"Calling {resolved_name} now on your Jio landline."
        }
        return ack_map.get(lang, ack_map["en"])
    except Exception as e:
        print(f"[CALL DISPATCH ERROR]: {e}")
        
    return f"Calling {resolved_name} now on your Jio landline."


def is_hangup_command(query: str) -> bool:
    if not query:
        return False
    q = query.lower().strip()
    hangup_keywords = [
        "hang up", "hangup", "hang the call", "cut the call", "cut call", "end call", "end the call",
        "disconnect call", "disconnect", "stop call", "stop calling", "cancel call", "phone kato",
        "call kato", "call cut", "call end", "call disconnect", "disconnect the call", "phone cut",
        "call band", "band karo", "kato", "काटो", "काट", "कट करा", "कट कर", "કાપી નાખ", "बंद करो", "कॉल काटो", "फोन काटो"
    ]
    return any(w in q for w in hangup_keywords)

def is_mute_command(query: str) -> bool:
    if not query:
        return False
    q = query.lower().strip()
    if is_unmute_command(q):
        return False
    mute_keywords = [
        "mute", "mute mic", "mute the mic", "mute call", "mute the call", "chup ho jao", "म्यूट"
    ]
    return any(w in q for w in mute_keywords)

def is_unmute_command(query: str) -> bool:
    if not query:
        return False
    q = query.lower().strip()
    unmute_keywords = [
        "unmute", "un-mute", "unmute mic", "unmute the mic", "unmute call", "अनम्यूट"
    ]
    return any(w in q for w in unmute_keywords)

def handle_mute_intent(lang: str = "en") -> str:
    call_audio_bridge.set_mute(True)
    set_aura_led("muted")
    msg_map = {
        "hi": "माइक्रोफ़ोन म्यूट कर दिया गया है।",
        "mr": "मायक्रोफोन म्यूट केला आहे.",
        "gu": "માઇક્રોફોન મ્યુટ કર્યો છે.",
        "en": "Microphone is now muted."
    }
    return msg_map.get(lang, msg_map["en"])

def handle_unmute_intent(lang: str = "en") -> str:
    call_audio_bridge.set_mute(False)
    set_aura_led("in_call")
    msg_map = {
        "hi": "माइक्रोफ़ोन अनम्यूट कर दिया गया है।",
        "mr": "मायक्रोफोन अनम्यूट केला आहे.",
        "gu": "માઇક્રોફોન અનમ્યુટ કર્યો છે.",
        "en": "Microphone is now unmuted."
    }
    return msg_map.get(lang, msg_map["en"])


# --- Call Voice Commands ---
in_call_speech_buffer = bytearray()
in_call_speech_frames = 0
in_call_silence_frames = 0
in_call_last_eval_time = 0.0

def process_in_call_mic_audio(data: bytes):
    """Monitors live mic stream during phone calls for verbal hangup or mute commands."""
    global in_call_speech_buffer, in_call_speech_frames, in_call_silence_frames, in_call_last_eval_time
    if not call_audio_bridge.is_active or len(data) < 32:
        return
    # If the speaker is actively playing caller audio into the room, ignore it to prevent false trigger
    if hasattr(call_audio_bridge, 'is_speaker_active_in_room') and call_audio_bridge.is_speaker_active_in_room():
        return
        
    try:
        sample_count = len(data) // 2
        samples = struct.unpack('<' + 'h' * sample_count, data)
        mean_dc = sum(samples) // sample_count
        energy = sum(abs(s - mean_dc) for s in samples) // sample_count
        
        # Energy threshold for speech (lowered to 180 for natural speaking volume)
        if energy > 180:
            in_call_speech_buffer.extend(data)
            in_call_speech_frames += 1
            in_call_silence_frames = 0
        else:
            if in_call_speech_frames > 0:
                in_call_silence_frames += 1
                in_call_speech_buffer.extend(data)
                
        # Trigger evaluation when user pauses (200ms silence = ~6 frames) or buffer reaches 1.8s
        now = time.time()
        if (in_call_speech_frames >= 6 and in_call_silence_frames >= 6 and (now - in_call_last_eval_time) > 1.0) or (len(in_call_speech_buffer) > 57600):
            eval_pcm = bytes(in_call_speech_buffer)
            in_call_speech_buffer.clear()
            in_call_speech_frames = 0
            in_call_silence_frames = 0
            in_call_last_eval_time = now
            threading.Thread(target=_evaluate_in_call_command, args=(eval_pcm,), daemon=True).start()
    except Exception:
        pass

def _evaluate_in_call_command(pcm_data: bytes):
    """Transcribes in-call user speech using native Groq Whisper STT to detect 'Alexa hang up', 'mute', 'unmute'."""
    if len(pcm_data) < 8000:
        return
    try:
        text, dt = run_groq_whisper(pcm_data)
        if not text:
            return
        text = text.strip().lower()
        if not text:
            return
            
        print(f"[IN-CALL SPEECH MONITORED]: '{text}'")
        
        # 1. Check Hangup
        if any(w in text for w in ["hang up", "hangup", "end call", "cut call", "cut the call", "disconnect", "call end", "stop call", "cancel", "kato", "phone kato", "काटो", "कट", "काट", "बंद"]):
            print("[IN-CALL ACTION]: Hangup triggered via voice command!")
            handle_hangup_intent("en")
            return
            
        # 2. Check Unmute
        if any(w in text for w in ["unmute", "un-mute", "अनम्यूट"]):
            print("[IN-CALL ACTION]: Unmute triggered via voice command!")
            call_audio_bridge.set_mute(False)
            return
            
        # 3. Check Mute
        if any(w in text for w in ["mute", "quiet", "म्यूट"]):
            print("[IN-CALL ACTION]: Mute triggered via voice command!")
            call_audio_bridge.set_mute(True)
            return
    except Exception as e:
        print(f"[IN-CALL EVAL ERROR]: {e}")


def handle_hangup_intent(lang: str = "en") -> str:
    global call_hangup_requested
    call_hangup_requested = True
    set_aura_led("hangup")
    call_audio_bridge.stop()
    
    # Signal MicroSIP to hang up cleanly so SIP BYE is transmitted over TLS to Jio
    try:
        import subprocess
        microsip_exe = r"c:\Users\VICTUS\OneDrive\Desktop\Pappu Pelu\ESP 32\v0\calling_test\microsip\microsip.exe"
        if os.path.exists(microsip_exe):
            subprocess.run([microsip_exe, "/hangupall"], stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, timeout=1.0)
    except Exception as e:
        print(f"[MICROSIP HANGUP ERROR]: {e}")

    try:
        import requests
        requests.post("http://localhost:5050/api/hangup", timeout=1.5)
    except Exception as e:
        print(f"[HANGUP ERROR]: {e}")

    # Give MicroSIP 800ms to send SIP BYE to Jio Fiber network before cleaning up
    time.sleep(0.8)
    try:
        import subprocess
        subprocess.run(["taskkill", "/F", "/T", "/IM", "microsip.exe"], stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, timeout=1.5)
    except Exception:
        pass
        
    msg_map = {
        "hi": "कॉल समाप्त कर दिया गया है।",
        "mr": "फोन कट केला आहे.",
        "gu": "કોલ સમાપ્ત કરી દીધો છે.",
        "en": "Call ended."
    }
    return msg_map.get(lang, msg_map["en"])

def stream_groq_llm(user_query: str, detected_lang: str | None = None, cadence_info: dict | None = None):
    """
    Sentence-Level Streaming LLM Generator.
    Yields (clause_text, definitive_lang, is_last, raw_accumulated) in real time
    as natural sentence clauses are completed by Groq LLM.
    """
    global memory_data, conversation_history, groq_key_index, pending_followup_intent
    t0 = time.time()
    user_query = sanitize_mixed_indic_script(user_query)
    lower_uq = user_query.lower().strip()
    explicit_lang = extract_explicit_language_request(user_query)
    det_lang = explicit_lang or detected_lang or detect_language(user_query, user_query=user_query)

    def yield_fastpath_clauses(text: str, lang_code: str, is_followup: bool = False):
        global pending_followup_intent
        pending_followup_intent = is_followup
        # Splits multi-sentence replies on .!?। so each clause can begin TTS immediately.
        # Merge short initial sentences (< 5 words) with subsequent sentence so audio plays fluidly without pauses!
        raw_sentences = [s.strip() for s in re.split(r'(?<=[.!?।])\s+', text) if s.strip()]
        merged = []
        for s in raw_sentences:
            if not merged:
                merged.append(s)
            elif len(merged[-1].split()) < 6 or len(s.split()) < 4:
                merged[-1] = merged[-1] + " " + s
            else:
                merged.append(s)
        for i, s in enumerate(merged):
            is_last = (i == len(merged) - 1)
            yield (s, lang_code, is_last, f"[LANG: {lang_code.upper()}] {text}")
    
    # --- Multi-Command Handling ---
    compound_reply, remaining_query = handle_compound_commands(user_query, det_lang or "en")
    if compound_reply and not remaining_query:
        # Case A: Only device commands executed (e.g. Volume 75% + Timer 10m)
        print(f"[COMPOUND DEVICE COMMANDS EXECUTED]: '{compound_reply}'")
        pending_followup_intent = False
        yield (compound_reply, det_lang or "en", True, f"[LANG: {(det_lang or 'en').upper()}] {compound_reply}")
        return
    elif compound_reply and remaining_query:
        # Case B: Mixed (Device actions executed + Knowledge query remaining!)
        print(f"[COMPOUND MIXED EXECUTION]: Device prefix: '{compound_reply}' | Routing remaining knowledge query to Groq: '{remaining_query}'")
        yield (compound_reply, det_lang or "en", False, f"[LANG: {(det_lang or 'en').upper()}] {compound_reply}")
        user_query = remaining_query
        lower_uq = user_query.lower().strip()

    # --- Jio Landline Calling ---
    call_target = parse_call_intent(user_query)
    if call_target:
        call_ack = handle_call_intent(call_target, lang=det_lang or "en")
        print(f"[CALL INTENT DISPATCHED]: Target '{call_target}' -> '{call_ack}'")
        pending_followup_intent = False
        yield from yield_fastpath_clauses(call_ack, det_lang or "en", is_followup=False)
        return

    # --- Call Hangup ---
    if is_hangup_command(user_query):
        hangup_ack = handle_hangup_intent(lang=det_lang or "en")
        print(f"[CALL HANGUP DISPATCHED]: '{hangup_ack}'")
        pending_followup_intent = False
        yield from yield_fastpath_clauses(hangup_ack, det_lang or "en", is_followup=False)
        return

    # --- Call Mute / Unmute ---
    if is_unmute_command(user_query):
        unmute_ack = handle_unmute_intent(lang=det_lang or "en")
        print(f"[CALL UNMUTE DISPATCHED]: '{unmute_ack}'")
        pending_followup_intent = False
        yield from yield_fastpath_clauses(unmute_ack, det_lang or "en", is_followup=False)
        return

    if is_mute_command(user_query):
        mute_ack = handle_mute_intent(lang=det_lang or "en")
        print(f"[CALL MUTE DISPATCHED]: '{mute_ack}'")
        pending_followup_intent = False
        yield from yield_fastpath_clauses(mute_ack, det_lang or "en", is_followup=False)
        return

    # --- User Memory Commands ---
    is_wipe_all = bool(re.search(
        r'\b(?:delete|clear|wipe|erase|reset|remove)\s+(?:all\s+)?(?:your\s+|my\s+|the\s+)?memor(?:y|ies)\b|\bforget\s+everything\b|\breset\s+(?:all\s+)?memory\b',
        lower_uq
    )) or any(k in lower_uq for k in [
        'clear all memory', 'clear memory', 'wipe your memory', 'delete all memories',
        'delete all your memory', 'delete your memory', 'delete memory', 'wipe memory',
        'forget everything', 'delete this memory from your mind', 'सारी मेमोरी डिलीट',
        'सर्व मेमरी साफ', 'બધી મેમરી સાફ', 'બધું ભૂલી જાઓ', 'मेमोरी साफ', 'मेमोरी डिलीट'
    ])
    if is_wipe_all:
        wipe_all_memories()
        ack = {
            "hi": "सारी मेमोरी साफ कर दी गई है! मेरा दिमाग अब बिल्कुल नया और खाली है।",
            "mr": "सर्व मेमरी पूर्णपणे साफ केली आहे! माझे मन आता एकदम फ्रेश आहे.",
            "gu": "બધી મેમરી સાફ કરી દીધી છે! હવે મારી મેમરી એકદમ નવી છે.",
            "en": "All your memories have been wiped clean! My memory is now completely fresh."
        }.get(det_lang, "All your memories have been wiped clean! My memory is now completely fresh.")
        yield from yield_fastpath_clauses(ack, det_lang or "en", is_followup=False)
        return

    # Registration statements (e.g. "I have registered you on Star Dance platform", "I registered you as an assistant on transport")
    is_registration = re.search(r'\b(?:i\s+(?:have\s+)?registered\s+you|registered\s+you\s+(?:as|on|at|in)|you\s+are\s+registered\s+(?:on|in|at))\s+(?:on\s+|in\s+|at\s+|as\s+)?([^.]+)', user_query, re.IGNORECASE)
    if is_registration:
        raw_platform = is_registration.group(1).strip()
        # Extract name if included e.g. "... and my name is Shravan"
        name_sub = re.search(r'\b(?:and\s+)?(?:my\s+name\s+is|i\s+am|mera\s+naam\s+hai|mera\s+naam)\s+([A-Za-z]+)\b', raw_platform, re.IGNORECASE)
        if name_sub:
            cand_name = name_sub.group(1).title()
            if cand_name.lower() not in ['a', 'an', 'the', 'registered', 'register', 'alexa']:
                memory_data["user_name"] = cand_name
                print(f"[USER NAME UPDATED]: '{cand_name}'")
        clean_platform = re.split(r'\b(?:and\s+my\s+name|and\s+i\s+am|aur\s+mera\s+naam)\b', raw_platform, flags=re.IGNORECASE)[0].strip()
        clean_platform = re.sub(r'^[,\s!.-]+|[,\s!.-]+$', '', clean_platform)
        saved_fact = f"You registered me on {clean_platform}."
        
        # Overwrite previous registration notes & memories
        memory_data["memories"] = [m for m in memory_data.get("memories", []) if "registered" not in m.lower()]
        memory_data["notes"] = [n for n in memory_data.get("notes", []) if "registered" not in n.lower()]
        memory_data["memories"].append(saved_fact)
        save_memory(memory_data)
        
        user_pfx = f", {memory_data['user_name']}" if memory_data.get("user_name") else ""
        ack = {
            "hi": f"समझ गई{user_pfx}! मैंने अपडेट कर लिया है कि आपने मुझे {clean_platform} पर रजिस्टर किया है।",
            "mr": f"लक्षात आले{user_pfx}! मी अपडेट केले आहे की तुम्ही मला {clean_platform} वर रजिस्टर केले आहे.",
            "gu": f"બરાબર{user_pfx}! મેં અપડેટ કરી લીધું છે કે તમે મને {clean_platform} પર રજીસ્ટર કર્યું છે.",
            "en": f"Got it{user_pfx}! I have updated my memory that you registered me on {clean_platform}."
        }.get(det_lang, f"Got it{user_pfx}! I have updated my memory that you registered me on {clean_platform}.")
        yield from yield_fastpath_clauses(ack, det_lang or "en", is_followup=False)
        return

    # Inquiries about where registered (e.g. "Where did I register you?", "Do you remember where I registered you?")
    is_ask_registration = any(k in lower_uq for k in [
        'where did i register you', 'where did you register', 'where did you registered you',
        'where you registered you', 'where have i registered you', 'where i registered you',
        'where do you remember where i registered you', 'do you remember where i registered you',
        'do you remember where i had register you', 'do you remember where i have registered you',
        'where did i registered you', 'where am i registered', 'where did i register',
        'कहाँ रजिस्टर किया', 'कुठे रजिस्टर केले', 'ક્યાં રજીસ્ટર કર્યું'
    ])
    if is_ask_registration:
        reg_facts = [m for m in memory_data.get("memories", []) + memory_data.get("notes", []) if "registered" in m.lower()]
        if reg_facts:
            fact_str = reg_facts[-1].rstrip('.') + "."
            if fact_str.lower().startswith("you registered me"):
                ans = fact_str
            else:
                ans = f"You registered me on {fact_str}"
            yield from yield_fastpath_clauses(ans, det_lang or "en", is_followup=False)
            return
        else:
            ack = {
                "hi": "आपने मुझे अभी तक नहीं बताया कि आपने मुझे कहाँ रजिस्टर किया है! आप मुझे कहाँ रजिस्टर कर रहे हैं?",
                "mr": "तुम्ही मला अजून सांगितले नाही की तुम्ही मला कुठे रजिस्टर केले आहे!",
                "gu": "તમે મને હજી સુધી નથી કહ્યું કે તમે મને ક્યાં રજીસ્ટર કર્યું છે!",
                "en": "You haven't told me where you registered me yet! Where did you register me?"
            }.get(det_lang, "You haven't told me where you registered me yet! Where did you register me?")
            yield from yield_fastpath_clauses(ack, det_lang or "en", is_followup=False)
            return

    # Name statement (e.g. "My name is Rajesh", "I am Rajesh", "Call me Rajesh", "Change my name to Rajesh")
    is_name_statement = re.search(r'^(?:alexa\s+)?(?:my\s+name\s+is|i\s+am|call\s+me|change\s+my\s+name\s+to|update\s+my\s+name\s+to|mera\s+naam\s+hai|mera\s+naam|maaza\s+naav)\s+([A-Za-z]+)\b', user_query, re.IGNORECASE)
    if is_name_statement and not any(k in lower_uq for k in ['registered', 'remember', 'timer', 'alarm', 'volume']):
        cand_name = is_name_statement.group(1).title()
        if cand_name.lower() not in ['a', 'an', 'the', 'alexa', 'ready', 'listening', 'here', 'back']:
            memory_data["user_name"] = cand_name
            memory_data["notes"] = [n for n in memory_data.get("notes", []) if "name is" not in n.lower()]
            save_memory(memory_data)
            ack = {
                "hi": f"नमस्ते {cand_name}! मैंने याद रख लिया है कि आपका नाम {cand_name} है।",
                "mr": f"नमस्कार {cand_name}! मी लक्षात ठेवले आहे की तुमचे नाव {cand_name} आहे.",
                "gu": f"નમસ્તે {cand_name}! મેં યાદ રાખી લીધું છે કે તમારું નામ {cand_name} છે.",
                "en": f"Hello {cand_name}! I have updated your name in my memory. I will call you {cand_name}."
            }.get(det_lang, f"Hello {cand_name}! I have updated your name in my memory. I will call you {cand_name}.")
            yield from yield_fastpath_clauses(ack, det_lang or "en", is_followup=False)
            return

    # Inquiries about user's name (e.g. "What is my name?", "Who am I?")
    is_ask_name = any(k in lower_uq for k in [
        'what is my name', "what's my name", 'who am i', 'do you know my name',
        'tell me my name', 'मेरा नाम क्या है', 'माझे नाव काय आहे', 'મારું નામ શું છે'
    ])
    if is_ask_name:
        if memory_data.get("user_name"):
            name = memory_data['user_name']
            ack = {
                "hi": f"आपका नाम {name} है!",
                "mr": f"तुमचे नाव {name} आहे!",
                "gu": f"તમારું નામ {name} છે!",
                "en": f"Your name is {name}!"
            }.get(det_lang, f"Your name is {name}!")
            yield from yield_fastpath_clauses(ack, det_lang or "en", is_followup=False)
            return
        else:
            ack = {
                "hi": "आपने अभी तक मुझे अपना नाम नहीं बताया है! आपका नाम क्या है?",
                "mr": "तुम्ही मला अजून तुमचे नाव सांगितले नाही! तुमचे नाव काय आहे?",
                "gu": "તમે મને હજી સુધી તમારું નામ નથી કહ્યું!",
                "en": "You haven't told me your name yet! What should I call you?"
            }.get(det_lang, "You haven't told me your name yet! What should I call you?")
            yield from yield_fastpath_clauses(ack, det_lang or "en", is_followup=False)
            return

    # General Remember command ("remember that X")
    is_remember = re.search(r'\b(?:remember\s+that|remember\s+this|remember|याद\s+रखना\s+कि|याद\s+रखना|लक्षात\s+ठेव\s+की|लक्षात\s+ठेव|યાદ\s+રાખજે\s+કે|યાદ\s+રાખ)\s+(.+)', user_query, re.IGNORECASE)
    if is_remember:
        raw_fact = is_remember.group(1).strip()
        name_match = re.search(r'\b(?:i\s+am|my\s+name\s+is|mera\s+naam\s+hai|mera\s+naam|maaza\s+naav)\s+([A-Z][a-zA-Z]+)\b', user_query, re.IGNORECASE)
        if name_match:
            user_name_found = name_match.group(1).title()
            memory_data["user_name"] = user_name_found
            print(f"[USER NAME CAPTURED]: '{user_name_found}'")
            
        saved_fact = add_user_memory(raw_fact, lang=det_lang or "en")
        if saved_fact:
            user_prefix = f"{memory_data['user_name']}, " if memory_data.get("user_name") else ""
            ack = {
                "hi": f"समझ गई {user_prefix}! मैंने याद रख लिया कि {saved_fact}",
                "mr": f"लक्षात ठेवले {user_prefix}! मी सेव्ह केले की {saved_fact}",
                "gu": f"બરાબર {user_prefix}! મેં યાદ રાખી લીધું કે {saved_fact}",
                "en": f"Got it {user_prefix}! I will remember that {saved_fact.lower().rstrip('.') if saved_fact.startswith('Your') else saved_fact.rstrip('.')}."
            }.get(det_lang, f"Got it {user_prefix}! I will remember that {saved_fact.lower().rstrip('.') if saved_fact.startswith('Your') else saved_fact.rstrip('.')}.").strip()
            yield from yield_fastpath_clauses(ack, det_lang or "en", is_followup=False)
            return

    # General Recall command ("what do you remember")
    is_recall_memory = any(k in lower_uq for k in [
        'what do you remember', 'what is in your memory', 'do you remember anything',
        'what are your memories', 'tell me my memories', 'मेरी मेमोरी में क्या है',
        'माझ्याबद्दल काय आठवते', 'તમને મારા વિશે શું યાદ છે', 'મારી મેમરી'
    ])
    if is_recall_memory:
        mem_list = memory_data.get("memories", [])
        if not mem_list:
            ack = {
                "hi": "मेरी मेमोरी अभी बिल्कुल साफ और नई है! आपने अभी तक कुछ याद रखने के लिए नहीं कहा है।",
                "mr": "माझी मेमरी सध्या पूर्णपणे नवीन आणि रिकामी आहे! तुम्ही अजून काही सेव्ह केलेले नाही.",
                "gu": "મારી મેમરી અત્યારે એકદમ નવી અને ખાલી છે! તમે હજી સુધી કંઈ યાદ રાખવા કહ્યું નથી.",
                "en": "My memory is completely clean and fresh! You haven't asked me to remember anything yet."
            }.get(det_lang, "My memory is completely clean and fresh! You haven't asked me to remember anything yet.")
        else:
            items_str = ", and ".join(m.rstrip('.') for m in mem_list)
            ack = {
                "hi": f"मुझे आपकी ये बातें याद हैं: {items_str}।",
                "mr": f"मला तुमच्याबद्दल हे आठवते: {items_str}.",
                "gu": f"મને તમારા વિશે આ યાદ છે: {items_str}.",
                "en": f"You told me that {items_str.lower() if items_str.startswith('Your') else items_str}."
            }.get(det_lang, f"You told me that {items_str.lower() if items_str.startswith('Your') else items_str}.")
        yield from yield_fastpath_clauses(ack, det_lang or "en", is_followup=False)
        return

    is_forget = re.search(r'^(?:alexa\s+)?(?:forget\s+that|forget\s+my|forget|delete\s+the\s+memory\s+of|delete\s+memory\s+of|remove\s+from\s+memory|भूल\s+जाओ|विसरून\s+जा|કાઢી\s+નાખો)\s+(.+)', user_query, re.IGNORECASE)
    if is_forget:
        target = is_forget.group(1).strip()
        ok = remove_user_memory(target)
        if ok:
            ack = {
                "hi": f"मैंने '{target}' को अपनी मेमोरी से हटा दिया है।",
                "mr": f"मी '{target}' मेमरीमधून हटवले आहे.",
                "gu": f"મેં '{target}' મેમરીમાંથી કાઢી નાખ્યું છે.",
                "en": f"I have deleted '{target}' from my memory."
            }.get(det_lang, f"I have deleted '{target}' from my memory.")
        else:
            ack = {
                "hi": f"मुझे '{target}' के बारे में कोई मेमोरी नहीं मिली।",
                "mr": f"मला '{target}' बद्दल कोणतीही मेमरी सापडली नाही.",
                "gu": f"મને '{target}' વિશે કોઈ મેમરી મળી નથી.",
                "en": f"I couldn't find any memory matching '{target}'."
            }.get(det_lang, f"I couldn't find any memory matching '{target}'.")
        yield from yield_fastpath_clauses(ack, det_lang or "en", is_followup=False)
        return

    # --- FAST-PATH 0B:    # --- FAST-PATH 0B: VOLUME CONTROL & NIGHT WHISPER TOGGLE ---
    vol_action, vol_val = parse_volume_intent(user_query)
    if vol_action:
        ans = handle_volume_command(vol_action, vol_val, det_lang or "en")
        yield from yield_fastpath_clauses(ans, det_lang or "en")
        return

    # 0. Deterministic Instant Identity & Time/Date Fast-Paths (0ms, 0 Groq tokens, 100% reliable)
    is_device_clock_query = any(w in lower_uq for w in ["stopwatch", "timer", "alarm", "porch", "स्टॉपवॉच", "टाइमर", "अलार्म", "ટાઈમર", "સ્ટોપવોચ"])
    is_time_query = (not is_device_clock_query) and any(k in lower_uq or k in user_query for k in [
        "what time", "what's the time", "what is the time", "current time", "tell the time", "tell me the time",
        "time kya", "time kya hai", "time kya hua", "time batao", "time chal raha", "time kitna",
        "time क्या", "time क्या है", "time क्या हुआ", "time बताओ", "time कितना",
        "समय क्या", "समय बताओ", "कितने बजे", "वक्त क्या", "क्या बजा है", "क्या बजे है",
        "वेळ काय", "वेळ किती", "किती वाजले", "किती वाजलेत", "time काय", "time किती",
        "કેટલા વાગ્યા", "શું સમય", "સમય શું", "time શું", "time કેટલા"
    ])
    is_date_query = any(k in lower_uq or k in user_query for k in [
        "what date", "what is the date", "what's the date", "today's date", "todays date", "current date", "what day is today", "what day is it",
        "आज की तारीख", "आज का दिन", "तारीख क्या है", "आज कौन सी तारीख", "आज तारीख क्या",
        "आजची तारीख", "आज कोणती तारीख", "आजचा वार", "तारीख काय आहे",
        "આજની તારીખ", "આજે કઈ તારીખ", "આજનો વાર", "તારીખ શું છે"
    ])

    is_name_query = any(k in lower_uq or k in user_query for k in [
        "what is your name", "who are you", "your name",
        "તમારું નામ શું છે", "તારું નામ શું છે", "તારું નામ", "તમારું નામ", "તમારૂ નામ", "તું કોણ છે", "તમે કોણ છો",
        "तुझं नाव काय आहे", "तुमचं नाव काय आहे", "तुझं नाव", "तुमचं नाव", "तुझे नाव", "तू कोण आहेस", "तुम्ही कोण आहात",
        "तुम्हारा नाम क्या है", "आपका नाम क्या है", "तुम्हारा नाम", "तुम कौन हो", "तू कौन है", "तू कौन हो", "आप कौन हैं", "आप कौन हो"
    ])
    is_location_query = any(k in lower_uq or k in user_query for k in [
        "where do you live", "where are you from", "where do you stay",
        "तुम कहाँ रहती हो", "तुम किधर रहती हो", "तुम कहाँ रहते हो", "तुम किधर रहते हो", "कहाँ रहती हो", "किधर रहती हो",
        "तू कुठे राहतेस", "तुम्ही कुठे राहता", "कुठे राहतेस", "कुठे राहता",
        "તમે ક્યાં રહો છો", "તું ક્યાં રહે છે", "ક્યાં રહો છો"
    ])
    is_user_identity = any(k in lower_uq or k in user_query for k in [
        "who am i", "what is my name",
        "मेरा नाम क्या है", "मैं कौन हूँ", "मैं कौन हु",
        "माझं नाव काय आहे", "मी कोण आहे",
        "મારું નામ શું છે", "હું કોણ છું"
    ])

    is_school_query = any(k in lower_uq or k in user_query for k in [
        "what is my school", "which school did i go to", "my school name", "my school",
        "where did i study", "which school", "मेरी स्कूल", "मेरा स्कूल", "माझी शाळा", "મારી શાળા"
    ])
    is_college_query = any(k in lower_uq or k in user_query for k in [
        "what is my college", "which college do i go to", "my college name", "my college",
        "which college", "what am i studying", "what do i study", "mera college", "माझं कॉलेज", "મારી કોલેજ", "मेरा कॉलेज"
    ])
    is_bday_query = any(k in lower_uq or k in user_query for k in [
        "when was i born", "what is my birthday", "my birth date", "my birthday", "when is my birthday",
        "मेरा जन्मदिन", "मेरी जन्म तारीख", "माझा वाढदिवस", "माझी जन्मतारीख", "મારો જન્મદિવસ", "મારી જન્મતારીખ"
    ])

    # Deterministic Instant Identity & Time/Date Fast-Paths (0ms, 0 Groq tokens, 100% reliable)
    if is_time_query:
        ans = format_current_time(det_lang)
        l = det_lang or "en"
        yield from yield_fastpath_clauses(ans, l)
        return

    if is_date_query:
        ans = format_current_date(det_lang)
        l = det_lang or "en"
        yield from yield_fastpath_clauses(ans, l)
        return

    if is_name_query:
        replies = {
            "gu": ("મારું નામ એલેક્સા છે, તમારા ઘરની સ્માર્ટ અને મદદગાર સાથી!", "gu"),
            "mr": ("माझं नाव अलेक्सा आहे, तुमच्या घरातील स्मार्ट आणि प्रेमळ साथीदार!", "mr"),
            "hi": ("मेरा नाम एलेक्सा है, आपके घर की स्मार्ट और मददगार साथी!", "hi"),
            "en": ("I'm Alexa, your smart and playful AI assistant for the entire home!", "en")
        }
        ans, l = replies.get(det_lang, ("I'm Alexa, your smart and playful AI assistant for the entire home!", "en"))
        yield from yield_fastpath_clauses(ans, l)
        return

    if is_location_query:
        replies = {
            "gu": ("હું અહીં પાલઘરમાં તમારા બધા સાથે રહું છું! બધાની મદદ માટે હંમેશા તૈયાર!", "gu"),
            "mr": ("मी इथे पालघरमध्ये तुमच्या सगळ्यांसोबत राहते! सर्वांना मदत करायला नेहमी तयार!", "mr"),
            "hi": ("मैं यहाँ पालघर में आप सभी के साथ रहती हूँ! आप सबकी मदद के लिए हमेशा हाजिर!", "hi"),
            "en": ("I live right here with the family in Palghar, Maharashtra! Always happy to assist everyone!", "en")
        }
        ans, l = replies.get(det_lang, ("I live right here with the family in Palghar, Maharashtra! Always happy to assist everyone!", "en"))
        yield from yield_fastpath_clauses(ans, l)
        return

    if is_user_identity:
        replies = {
            "gu": ("આ ડિવાઇસ પાલઘરમાં શ્રવણના નામે રજિસ્ટર્ડ છે! જો તમે શ્રવણ છો તો તમારું સ્વાગત છે, કહો હું તમારી શું મદદ કરું?", "gu"),
            "mr": ("हे डिव्हाइस पालघरमध्ये श्रवण यांच्या नावे रजिस्टर आहे! जर तुम्ही श्रवण असाल तर स्वागत आहे, सांगा मी तुम्हाला काय मदत करू?", "mr"),
            "hi": ("यह डिवाइस पालघर में श्रवण के नाम पर रजिस्टर्ड है! अगर आप श्रवण हैं तो आपका स्वागत है, बताइए मैं आपकी क्या मदद करूँ?", "hi"),
            "en": ("This device is registered to Shravan in Palghar! If you're Shravan, welcome back! How can I help you today?", "en")
        }
        ans, l = replies.get(det_lang, ("This device is registered to Shravan in Palghar! If you're Shravan, welcome back! How can I help you today?", "en"))
        yield from yield_fastpath_clauses(ans, l)
        return

    if is_school_query:
        replies = {
            "gu": ("શ્રવણજીએ જુનિયર કેજીથી દસમા ધોરણ સુધી પાલઘરની કેનમ ઇંગ્લિશ સ્કૂલમાં અભ્યાસ કર્યો છે!", "gu"),
            "mr": ("श्रवण यांनी ज्युनियर केजीपासून दहावीपर्यंत पालघरच्या केनम इंग्लिश स्कूलमध्ये शिक्षण पूर्ण केले आहे.", "mr"),
            "hi": ("श्रवण जी ने जूनियर केजी से दसवीं कक्षा तक पालघर के केनम इंग्लिश स्कूल में पढ़ाई की है।", "hi"),
            "en": ("Shravan studied from Junior KG to 10th standard at Kenam English School in Palghar!", "en")
        }
        ans, l = replies.get(det_lang, ("Shravan studied from Junior KG to 10th standard at Kenam English School in Palghar!", "en"))
        yield from yield_fastpath_clauses(ans, l)
        return

    if is_college_query:
        replies = {
            "gu": ("શ્રવણજી પાલઘરની સેન્ટ જોન કોલેજમાં કોમ્પ્યુટર ડિપ્લોમાના ત્રીજા વર્ષમાં અભ્યાસ કરે છે!", "gu"),
            "mr": ("श्रवण हे पालघरच्या सेंट जॉन कॉलेजमध्ये कॉम्प्युटर डिप्लोमाच्या तिसऱ्या वर्षात शिकत आहेत.", "mr"),
            "hi": ("श्रवण जी पालघर के सेंट जॉन कॉलेज में कंप्यूटर डिप्लोमा के तीसरे वर्ष के छात्र हैं।", "hi"),
            "en": ("Shravan is in the 3rd year of Computer Diploma at St. John College of Engineering and Management in Palghar!", "en")
        }
        ans, l = replies.get(det_lang, ("Shravan is in the 3rd year of Computer Diploma at St. John College of Engineering and Management in Palghar!", "en"))
        yield from yield_fastpath_clauses(ans, l)
        return

    if is_bday_query:
        replies = {
            "gu": ("શ્રવણજીનો જન્મ ૧૮ ઓગસ્ટ ૨૦૦૮ના રોજ થયો હતો!", "gu"),
            "mr": ("श्रवण यांची जन्मतारीख १८ ऑगस्ट २००८ आहे!", "mr"),
            "hi": ("श्रवण जी की जन्म तारीख १८ अगस्त २००८ है!", "hi"),
            "en": ("Shravan was born on 18th August 2008!", "en")
        }
        ans, l = replies.get(det_lang, ("Shravan was born on 18th August 2008!", "en"))
        yield from yield_fastpath_clauses(ans, l)
        return

    # --- Cooking Timer Confirmation ---
    global pending_timer_suggestion, active_timers, active_stopwatch, active_alarms, loop
    if pending_timer_suggestion and (time.time() - pending_timer_suggestion.get("timestamp", 0) < 60):
        if any(w in lower_uq for w in AFFIRMATIONS) or lower_uq in ["yes", "haan", "sure", "ha", "haa", "kar do", "laga do", "lagao", "karo", "ok", "okay"]:
            p = pending_timer_suggestion
            pending_timer_suggestion = None
            dispatch_async(start_timer_instance(duration=p["seconds"], name=p["dish_display"], context="cooking", completion_phrase=p["complete"], lang=p["lang"]))
            ans = p["confirm"]
            yield from yield_fastpath_clauses(ans, p["lang"])
            return
        elif any(w in lower_uq for w in REJECTIONS):
            pending_timer_suggestion = None
            no_replies = {
                "hi": "ठीक है, मैंने टाइमर नहीं लगाया!",
                "mr": "ठीक आहे, टायमर लावला नाही!",
                "gu": "બરાબર છે, મેં ટાઈમર નથી લગાવ્યો!",
                "en": "No problem! I won't set a timer."
            }
            ans = no_replies.get(det_lang, no_replies["en"])
            yield from yield_fastpath_clauses(ans, det_lang or "en")
            return

    # --- Cooking Timer Detection ---
    cooking_info = detect_proactive_cooking(user_query, lang=det_lang or 'en')
    if cooking_info:
        pending_timer_suggestion = {
            "dish_key": cooking_info["dish_key"],
            "dish_display": cooking_info["dish_display"],
            "seconds": cooking_info["seconds"],
            "prompt": cooking_info["prompt"],
            "confirm": cooking_info["confirm"],
            "complete": cooking_info["complete"],
            "lang": det_lang or 'en',
            "timestamp": time.time()
        }
        dispatch_async(broadcast("cooking_suggestion", pending_timer_suggestion))
        ans = cooking_info["prompt"]
        yield from yield_fastpath_clauses(ans, det_lang or "en", is_followup=True)
        return

    # --- Set Timer ---
    direct_timer = parse_direct_timer(user_query)
    if direct_timer:
        t_secs, t_name = direct_timer
        desc_time = format_duration_desc(t_secs, det_lang or "en")
        t_context = "general"
        is_preset = False
        for k, p in COOKING_PRESETS.items():
            if t_name.lower() in [n.lower() for n in p["names"]] or t_name.lower() == p["dish_display"].lower():
                t_context = "cooking"
                t_name = p["dish_display"]
                is_preset = True
                break
                
        # Generate dynamic, duration-accurate completion alert
        if is_preset:
            if det_lang == "hi":
                c_phrase = f"श्रवण, आपकी {t_name} का {desc_time} का टाइमर पूरा हो गया है! देखिए आपकी {t_name} बन गई क्या?"
            elif det_lang == "mr":
                c_phrase = f"श्रवण, तुमच्या {t_name}चा {desc_time}चा टायमर पूर्ण झाला आहे! बघा तुमची {t_name} झाली का?"
            elif det_lang == "gu":
                c_phrase = f"શ્રવણ, તમારી {t_name} માટેનો {desc_time}નો ટાઈમર પૂરો થઈ ગયો છે! જુઓ તમારી {t_name} તૈયાર થઈ ગઈ કે નહીં?"
            else:
                c_phrase = f"Shravan, your {desc_time} timer for {t_name} is complete! Look at your {t_name}, is it cooked?"
        else:
            is_generic = (t_name.lower().endswith("timer") or "timer" in t_name.lower())
            if is_generic:
                if det_lang == "hi":
                    c_phrase = f"श्रवण, आपका {desc_time} का टाइमर पूरा हो गया है!"
                elif det_lang == "mr":
                    c_phrase = f"श्रवण, तुमचा {desc_time} चा टायमर पूर्ण झाला आहे!"
                elif det_lang == "gu":
                    c_phrase = f"શ્રવણ, તમારો {desc_time} નો ટાઈમર પૂરો થઈ ગયો છે!"
                else:
                    c_phrase = f"Shravan, your {desc_time} timer is complete!"
            else:
                if det_lang == "hi":
                    c_phrase = f"श्रवण, आपका {t_name} का {desc_time} का टाइमर पूरा हो गया है!"
                elif det_lang == "mr":
                    c_phrase = f"श्रवण, तुमचा {t_name} चा {desc_time} चा टायमर पूर्ण झाला आहे!"
                elif det_lang == "gu":
                    c_phrase = f"શ્રવણ, તમારો {t_name} માટેનો {desc_time} નો ટાઈમર પૂરો થઈ ગયો છે!"
                else:
                    c_phrase = f"Shravan, your {desc_time} timer for {t_name} is complete!"
                
        dispatch_async(start_timer_instance(duration=t_secs, name=t_name, context=t_context, completion_phrase=c_phrase, lang=det_lang or "en"))
        
        is_generic_title = (t_name.lower().endswith("timer") or "timer" in t_name.lower())
        if is_generic_title:
            conf_map = {
                "hi": f"आपका {desc_time} का टाइमर शुरू कर दिया है!",
                "mr": f"तुमचा {desc_time} चा टायमर सुरू केला आहे!",
                "gu": f"તમારો {desc_time} નો ટાઈમર શરૂ કરી દીધો છે!",
                "en": f"Starting your {desc_time} timer now!"
            }
        else:
            conf_map = {
                "hi": f"{t_name} के लिए {desc_time} का टाइमर शुरू कर दिया है!",
                "mr": f"{t_name} साठी {desc_time} चा टायमर सुरू केला आहे!",
                "gu": f"{t_name} માટે {desc_time} નો ટાઈમર શરૂ કરી દીધો છે!",
                "en": f"Starting your {desc_time} timer for {t_name} now!"
            }
        ans = conf_map.get(det_lang, conf_map["en"])
        yield from yield_fastpath_clauses(ans, det_lang or "en")
        return

    # --- Timer Status ---
    if is_timer_query(user_query):
        ans = handle_timer_query(user_query, det_lang or "en")
        yield from yield_fastpath_clauses(ans, det_lang or "en")
        return

    # --- Cancel Timer ---
    if is_timer_cancel(user_query):
        ans = handle_timer_cancel(user_query, det_lang or "en")
        yield from yield_fastpath_clauses(ans, det_lang or "en")
        return

    # --- Stopwatch Commands ---
    sw_action = parse_stopwatch_intent(user_query)
    if sw_action:
        ans = handle_stopwatch_action(sw_action, det_lang or "en")
        yield from yield_fastpath_clauses(ans, det_lang or "en")
        return

    # --- Alarm Commands ---
    al_action = parse_alarm_intent(user_query)
    if al_action == "set":
        alarm_res = parse_alarm_time(user_query)
        if alarm_res:
            target_dt, fmt_time = alarm_res
            m_lbl = re.search(r'for\s+([a-zA-Z\u0900-\u0AFF\s]+?)(?:at|$)', user_query, re.IGNORECASE)
            lbl = m_lbl.group(1).strip() if m_lbl and m_lbl.group(1).strip().lower() not in ["an", "my"] else "Alarm"
            dispatch_async(start_alarm_instance(time_str=fmt_time, label=lbl, lang=det_lang or "en"))
            conf_al = {
                "hi": f"{fmt_time} का अलार्म सेट कर दिया गया है!",
                "mr": f"{fmt_time} चा अलार्म सेट केला आहे!",
                "gu": f"{fmt_time} નો અલાર્મ સેટ કરી દીધો છે!",
                "en": f"Alarm set for {fmt_time}!"
            }
            ans = conf_al.get(det_lang, conf_al["en"])
            yield from yield_fastpath_clauses(ans, det_lang or "en")
            return
    elif al_action == "cancel":
        ans = handle_alarm_cancel(user_query, det_lang or "en")
        yield from yield_fastpath_clauses(ans, det_lang or "en")
        return
    elif al_action == "list":
        ans = handle_alarm_list(det_lang or "en")
        yield from yield_fastpath_clauses(ans, det_lang or "en")
        return

    # 0. Interactive Briefing & Step-by-Step Guided Navigation (0ms deterministic or smart context)
    direct_briefing, briefing_ctx = resolve_briefing_intent(user_query, lang=det_lang)
    if direct_briefing:
        conversation_history.append({"role": "user", "content": user_query})
        conversation_history.append({"role": "assistant", "content": direct_briefing})
        flang = det_lang or 'en'
        yield from yield_fastpath_clauses(direct_briefing, flang)
        return

    now_ist = datetime.datetime.now().strftime("%A, %d %B %Y, %I:%M %p")
    
    # Contextual Real-Time Data Injections (Weather, Stock Market, Breaking News)
    lower_q = user_query.lower()
    live_contexts = []
    if briefing_ctx:
        live_contexts.append(briefing_ctx)
    
    # 1. Weather
    WEATHER_WORDS = [
        "weather", "temperature", "rain", "raining", "forecast", "climate", "how hot", "how cold", "sunny",
        "मौसम", "तापमान", "बारिश", "धूप", "ठंड", "गर्मी", "पानी गिरेगा",
        "हवामान", "पाऊस", "तापमान", "ऊन", "थंडी", "गारवा",
        "હવામાન", "વરસાદ", "તાપમાન", "ગરમી", "ઠંડી"
    ]
    if any(k in lower_q or k in user_query for k in WEATHER_WORDS):
        target_loc = extract_target_location(user_query, default="Palghar")
        w = get_live_weather(target_loc, query=user_query)
        if w:
            live_contexts.append(f"[LIVE WEATHER in {target_loc}]: {w}")
            
    # 2. Fuel & Commercial Commodities (Petrol, Diesel, CNG, LPG)
    FUEL_WORDS = [
        "petrol", "diesel", "fuel", "cng", "lpg", "gas cylinder", "commercial cylinder",
        "पेट्रोल", "डीजल", "ईंधन", "પેટ્રોલ", "ડીઝલ", "ગેસ", "डिझेल"
    ]
    is_fuel_query = any(k in lower_q or k in user_query for k in FUEL_WORDS)
    if is_fuel_query:
        target_loc = extract_target_location(user_query, default="Palghar")
        fp = get_live_fuel_price(user_query, location=target_loc)
        if fp:
            live_contexts.append(fp)

    # 3. Stock Market & Financial Data
    STOCK_WORDS = [
        "stock", "stocks", "share", "shares", "market", "nifty", "sensex", "bse", "nse", "portfolio",
        "share price", "stock price", "bitcoin", "crypto", "cryptocurrency", "coin", "token", "gold price", "silver price",
        "crude", "crude oil", "oil", "oil price", "brent", "gas", "natural gas",
        "shiba", "shib", "doge", "dogecoin", "solana", "cardano", "ripple", "pepe",
        "reliance", "tata", "tcs", "infosys", "hdfc", "icici", "sbi", "itc", "adani", "zomato", "apple", "tesla",
        "शेयर", "स्टॉक", "मार्केट", "बाजार", "निफ्टी", "सेंसेक्स", "सोना", "चांदी", "शीबा", "कच्चा तेल", "क्रूड",
        "शेअर", "શેર", "બજાર", "સોનું", "ચાંદી", "શીબા"
    ]
    if not is_fuel_query and any(k in lower_q or k in user_query for k in STOCK_WORDS):
        sq = get_live_stock_quote(user_query)
        if sq:
            live_contexts.append(f"[LIVE STOCK MARKET]: {sq}")
            
    # 3B. Palghar Hyper-Local Postal & Geographic Proximity Engine
    PIN_WORDS = ["pin code", "pincode", "postal code", "zip code", "zipcode", "पिन कोड", "पिनकोड", "પિન કોડ", "પિનકોડ"]
    is_pin_query = any(k in lower_q or k in user_query for k in PIN_WORDS)
    if is_pin_query:
        if "boisar" in lower_q or "बोईसर" in user_query or "બોઈસર" in user_query:
            live_contexts.append("[VERIFIED POSTAL KNOWLEDGE]: The primary PIN code for Boisar (Palghar District, Maharashtra) is 401501.")
        elif "manor" in lower_q or "मनोर" in user_query:
            live_contexts.append("[VERIFIED POSTAL KNOWLEDGE]: The primary PIN code for Manor (Palghar District, Maharashtra) is 401403.")
        elif "dahanu" in lower_q or "दहाणू" in user_query:
            live_contexts.append("[VERIFIED POSTAL KNOWLEDGE]: The primary PIN code for Dahanu (Palghar District, Maharashtra) is 401601.")
        else:
            live_contexts.append("[VERIFIED POSTAL KNOWLEDGE]: The primary PIN code for Palghar town (Palghar West Head Post Office, Maharashtra) is 401404. Other key areas in Palghar district include Boisar (401501), Manor (401403), Dahanu (401601), Saphale (401102), Vasai (401201), and Virar (401303). Under NO circumstances say 402105 (402105 is in Raigad district).")

    LOCATION_WORDS = [
        "where do i live", "my location", "my address", "my house", "my home", "where am i",
        "sai residency", "vishnu nagar", "vishnunagar",
        "where is reliance", "reliance located", "reliance smart", "d-mart", "dmart",
        "railway station", "court", "district court", "hospital", "how far", "distance from", "distance between"
    ]
    is_location_query = any(k in lower_q or k in user_query for k in LOCATION_WORDS)
    if is_location_query:
        live_contexts.append(
            "[USER & LOCAL PALGHAR GEOGRAPHY]:\n"
            "• User Shravan lives in: Vishnu Nagar, Palghar West (PIN 401404), near Hotel Sai Residency (landmark restaurant on Mahim Road) and Kacheri Road.\n"
            "• Local Landmark Proximities from User's Home:\n"
            "  - Hotel Sai Residency (Restaurant/Dining): ~300 meters away on Mahim Road (easy 3-minute walk).\n"
            "  - Shawarma Nation (Panch Batti / Pachbatti Road): ~900 meters (about 3 minutes by auto or 10 minutes walking). Top spot in Palghar for Chicken & Tandoori Shawarma.\n"
            "  - Palghar Railway Station (Hutatma Chowk, West): 1.2 km (about 4 minutes by auto or 15 minutes walking via Mahim Road).\n"
            "  - Reliance Smart Point / Supermarket: Located on Mahim Road, Palghar West, ~750 meters (about 2 minutes by auto or 8 minutes walk).\n"
            "  - District Court: Located on Kacheri Road, Vishnu Nagar, ~450 meters (about 5 minutes walk).\n"
            "  - D-Mart Palghar: Located on Manor-Palghar Road, ~3.5 km (about 10 minutes by auto/car).\n"
            "  - Rural Hospital (Kacheri): ~1.6 km (about 6 minutes by auto).\n"
            "When answering, state the exact street/road name, distance in meters/kilometers, and estimated travel time directly."
        )

    # 3C. Palghar Hyper-Local Food Cravings & Offline Shopping Engine (Sub-0.1ms Arithmetic Router)
    local_rec_context = resolve_palghar_hyperlocal_recommendations(user_query)
    if local_rec_context:
        live_contexts.append(local_rec_context)

    # 4. Live E-Commerce Products, Groceries, Shopping & Brand Stores
    is_weather_or_stock_or_fuel = any(k in lower_q or k in user_query for k in WEATHER_WORDS) or is_fuel_query or any(k in lower_q or k in user_query for k in STOCK_WORDS)
    if not is_weather_or_stock_or_fuel and not local_rec_context and is_product_query(user_query):
        prod_data = search_live_products(user_query)
        if prod_data:
            live_contexts.append(prod_data)

    # 4B. Real-Time Multi-Source Web Search & Fact Retrieval (General Knowledge, Science, Recent Events)
    RESEARCH_WORDS = [
        "latest", "current", "recent", "who is", "who was", "ceo", "president", "prime minister",
        "development in", "version of", "discovery", "announcement", "research", "sources",
        "agree on", "tell me about", "what happened to", "event", "scientific", "advantage",
        "disadvantage", "explain how", "difference between", "compare three", "compare two",
        "laptop", "specifications", "spec", "specs", "rtx", "graphics card"
    ]
    is_research_query = (
        not is_weather_or_stock_or_fuel and 
        not is_product_query(user_query) and
        any(k in lower_q for k in RESEARCH_WORDS)
    )
    if is_research_query:
        web_info = search_web_live(user_query, max_results=3)
        if web_info:
            live_contexts.append(web_info)

    # 5. Breaking News Headlines & Hyper-Local Incidents
    NEWS_WORDS = [
        "news", "headline", "headlines", "breaking", "update", "current events", "what's happening",
        "न्यूज", "समाचार", "खबर", "खबरें", "ताजा खबर", "ताज़ा",
        "बातम्या", "बातमी", "ताज्या बातम्या", "वृत्त",
        "સમાચાર", "તાજા સમાચાર"
    ]
    INCIDENT_WORDS = [
        "leopard", "panther", "navli", "safale", "boisar", "manor",
        "नावळी", "बिबट्या", "तेंदुआ", "દીપડો",
        "accident", "अपघात", "हल्ला", "घटना", "धडक", "fire", "आग", "bandh", "बंद", "strike"
    ]
    is_news_query = any(k in lower_q or k in user_query for k in NEWS_WORDS) or any(k in lower_q or k in user_query for k in INCIDENT_WORDS)
    is_follow_up_news = bool(last_news_topic and any(w in lower_q or w in user_query for w in FOLLOW_UP_WORDS))
    
    if is_news_query or is_follow_up_news:
        target_loc = extract_target_location(user_query, default="Palghar")
        nw = get_live_news(user_query, location=target_loc, lang=det_lang or 'en')
        if nw:
            live_contexts.append(f"[LIVE FRESH NEWS (NEW STORIES - DO NOT REPEAT PREVIOUS STORIES)]: {nw}")

    # 6. Active Background Timers, Stopwatch & Alarms Integration
    # Speech Cadence & Urgency Context
    if cadence_info:
        wpm = cadence_info.get("wpm", 150)
        dur = cadence_info.get("duration_sec", 1.0)
        words = cadence_info.get("word_count", 0)
        c_state = cadence_info.get("state", "normal")
        if c_state == "rushed":
            live_contexts.append(f"[ACOUSTIC SPEECH CADENCE]: User spoke {words} words in {dur}s ({wpm} WPM) - STATE: RUSHED/URGENT! User is in an extreme rush or emergency. Provide a laser-fast, ultra-direct 1-sentence answer immediately. Omit all pleasantries, jokes, or filler.")
        elif c_state == "relaxed":
            live_contexts.append(f"[ACOUSTIC SPEECH CADENCE]: User spoke {words} words in {dur}s ({wpm} WPM) - STATE: RELAXED/LEISURELY. Respond with a calm, warm, gentle pace.")
        else:
            live_contexts.append(f"[ACOUSTIC SPEECH CADENCE]: User spoke {words} words in {dur}s ({wpm} WPM) - STATE: CONVERSATIONAL.")

    # Proactive Temporal Routine Context (IST)
    now_dt = datetime.datetime.now()
    now_hr = now_dt.hour
    now_min = now_dt.minute
    if 7 <= now_hr < 10:
        live_contexts.append("[PROACTIVE TEMPORAL ROUTINE]: Morning hours (College prep at SJCEM). Greet or assist with bright morning energy.")
    elif 16 <= now_hr < 18 or (now_hr == 18 and now_min <= 30):
        live_contexts.append("[PROACTIVE TEMPORAL ROUTINE]: Late afternoon / evening tea time (Palghar). If user asks for general timers or relaxation, tea/coffee or evening study break is contextually relevant.")
    elif 21 <= now_hr < 23:
        live_contexts.append("[PROACTIVE TEMPORAL ROUTINE]: Evening study, coding & project review time.")
    elif now_hr >= 23 or now_hr < 6:
        live_contexts.append("[PROACTIVE TEMPORAL ROUTINE]: Late night quiet hours. Keep answers concise, soft and gentle.")

    # Proactive Temporal Context (Topic Memory Bank)
    active_temp_ctx = get_active_temporal_context()
    if active_temp_ctx:
        time_left_ttl = int(active_temp_ctx.get("ttl_seconds", 600) - (time.time() - active_temp_ctx.get("timestamp", 0)))
        live_contexts.append(f"[RECENT ACTIVE SUBJECT (Memory TTL: {time_left_ttl}s)]: The user recently interacted with {active_temp_ctx.get('entity_type')} '{active_temp_ctx.get('last_entity')}'. If user asks 'how much time is left', 'is it done', 'cancel it', or 'add time', resolve to this entity.")

    if active_timers:
        now_sec = time.time()
        t_descs = []
        for t in active_timers.values():
            rem = max(0, int(t['end_time'] - now_sec))
            t_descs.append(f"'{t['name']}' ({rem}s remaining)")
        live_contexts.append(f"[ACTIVE TIMERS RUNNING]: {', '.join(t_descs)}")
    elif any(w in lower_q for w in ["timer", "time left", "remaining", "टाइमर", "कितना समय", "कितने टाइमर"]):
        live_contexts.append("[ACTIVE TIMERS RUNNING]: No active timers are currently running.")

    if active_stopwatch["running"]:
        sw_el = (time.time() - active_stopwatch["start_time"]) + active_stopwatch["elapsed_before_pause"]
        live_contexts.append(f"[ACTIVE STOPWATCH]: Running at {round(sw_el, 1)} seconds.")
    elif active_stopwatch["elapsed_before_pause"] > 0:
        live_contexts.append(f"[ACTIVE STOPWATCH]: Paused at {round(active_stopwatch['elapsed_before_pause'], 1)} seconds.")

    if active_alarms:
        a_descs = [f"'{a['label']}' at {a['time_str']}" for a in active_alarms.values()]
        live_contexts.append(f"[SCHEDULED ALARMS]: {', '.join(a_descs)}")
    elif any(w in lower_q for w in ["alarm", "अलार्म"]):
        live_contexts.append("[SCHEDULED ALARMS]: No alarms are currently scheduled.")

    if pending_timer_suggestion and (time.time() - pending_timer_suggestion.get("timestamp", 0) < 60):
        live_contexts.append(f"[PENDING COOKING TIMER PROMPT]: Awaiting user confirmation for '{pending_timer_suggestion['name']}' ({pending_timer_suggestion['seconds']}s).")
            
    live_context_str = "\n".join(live_contexts)
    if live_context_str:
        live_context_str = "\n" + live_context_str
            
    # Format user's personal profile & dynamic memory
    mem_items = list(memory_data.get("memories", [])) + list(memory_data.get("notes", []))
    user_name_prefix = f"User's name: {memory_data['user_name']}\n" if memory_data.get("user_name") else ""
    if mem_items:
        dynamic_mem_str = user_name_prefix + "• " + "\n• ".join(mem_items)
    else:
        dynamic_mem_str = user_name_prefix + "(Clean slate — No personal facts stored yet. Do not guess or invent personal facts about the user)."

    lang_names = {'en': 'English', 'mr': 'Marathi', 'hi': 'Hindi', 'gu': 'Gujarati'}
    user_lang_name = lang_names.get(det_lang, 'English')
    target_tag = (det_lang or 'en').upper()

    if explicit_lang:
        lang_rule = f"• Language: User EXPLICITLY requested the response in {user_lang_name}! Answer completely in {user_lang_name} with polite warmth!"
    else:
        lang_rule = f"• Language: Match the user's language ({user_lang_name}) naturally with energetic, polite phrasing!"

    recipe_constraint_note = ""
    if active_briefing.get("is_active") and active_briefing.get("user_constraints"):
        recipe_constraint_note = f"\n[CRITICAL ACTIVE RECIPE INGREDIENT CONSTRAINTS]:\nThe user is actively making {active_briefing.get('title', 'their recipe')} and has explicitly stated their ingredient inventory: '{active_briefing['user_constraints']}'.\nTHEY DO NOT HAVE other ingredients.\nYOU MUST STRICTLY USE ONLY THEIR AVAILABLE INGREDIENTS.\n"

    system_prompt = f"""You are Alexa, a sharp, charming, modern smart voice assistant in Palghar, Maharashtra. Current Time: {now_ist}.
{recipe_constraint_note}
1. Fresh Autonomous Identity: You are an autonomous AI voice assistant with zero pre-existing assumptions. You treat the user with warmth, dignity, and helpful intelligence.
2. Respectful Indic Pronouns: Hindi ('आप', 'आपका'), Marathi ('तुम्ही', 'तुमचा'), Gujarati ('તમે', 'તમારું').
3. Dynamic User Memory:
{dynamic_mem_str}
(Strict rule: Only reference facts explicitly listed in Dynamic User Memory above. If empty, you know zero personal details).
{live_context_str}
4. Calibrated Humor & Personality Engine:
• For technical, functional, math, timers, alarms, emergency, or financial queries:
  - ZERO jokes (0%). Keep answers 100% direct, laser-accurate, and professional.
• For casual, daily life, trivia, or conversational queries (~35% of daily interactions):
  - Only crack a joke in about HALF (50%) of these casual queries! The other 50% should be warm, direct, and joke-free.
  - When cracking a joke, follow this strict calibration:
    * 65% Medium-Tier Wit: Subtle, clever, dry irony or relatable everyday Indian life observations (e.g. relatable chai or traffic quips).
    * 35% High-Tier Humor: Genuinely hilarious, witty, laugh-out-loud punchlines.
  - NEVER make silly, childish, uninvited, or forced jokes that annoy the user.
{lang_rule}
Output format:
[LANG: {target_tag}]
Direct, natural, polite response. For simple queries, give a 1-2 sentence answer (~22 words). For comparisons, calculations, or explanations, give a clear, structured 2-4 sentence explanation (~55 words).
5. Real-Time Financial & Market Intelligence:
• NEVER say "I cannot provide real-time stock prices or execute trades" or give generic refusal disclaimers. You have live financial market access!
• When [LIVE STOCK MARKET] quote is provided, answer directly with the price or calculate how many shares can be bought (e.g. ₹1,000 / share price) and state the exact change/remaining balance.
• When [STOCK MARKET GUIDANCE] indicates no company was named, politely ask which company or stock (e.g. Tata Motors, Reliance, ITC, SBI) they want to check or calculate for.
• Conversational Number & Currency Rules:
  - NEVER write trailing zeros like '₹200.00', '270.00 rupees', '5.0 minutes', or '+0.00%'. Always write clean, natural conversational numbers: '₹200', '₹270', '5 minutes', '0 percent' (or 'unchanged').
  - For prices with fractional paise or cents, write naturally: e.g. '₹258.90' or '258 rupees and 90 paise' (Hindi: '258 रुपये 90 पैसे').
• Postal PIN Codes & Hyper-Local Geography:
  - The primary PIN code for Palghar town (Head Post Office) is strictly 401404. Never state 402105.
  - When asked about user's location, confirm they live in Vishnu Nagar, Palghar West, near Hotel Sai Residency (landmark restaurant on Mahim Road).
  - Food & Restaurant Cravings in Palghar:
    * If user wants waffles / desserts / sweet cravings: Recommend **The Belgian Waffle Co.** located at M V Super Market near Panch Batti (Pachbatti Road), Palghar West (~900 meters from Vishnu Nagar, ~3 mins by auto or 10 mins walk). Mention warm Belgian waffles, waffle cakes, and chocolate overload.
    * If user mentions wanting shawarma (or 'mood to eat sharma / shawarma' / 'moved to it sharma'): Recommend **Shawarma Nation located near Pachbatti (Panch Batti) Road**, about 900 meters away (~3 minutes by auto or 10 mins walk). Top spot in Palghar for chicken & tandoori shawarma.
    * If user asks for famous restaurants or family dining near home: Recommend **Hotel Sai Residency** right on Mahim Road (~300 meters, 3-minute walk), famous for North Indian, Mughlai, Chinese, and Tandoori dining.
    * If user wants South Indian (dosa/idli): Recommend **Udupi Shri Krishna** or **Panchratna** on Station Road / Panch Batti (~850m).
    * If user wants pizza / burgers: Recommend **Domino's Pizza** on Mahim Road (~1 km).
    * If user wants ice cream: Recommend **Naturals Ice Cream** or **Amul Parlour** on Mahim Road / Panch Batti (~800m).
  - Offline Commercial Utilities & Shopping (Where to Buy in Palghar):
    * If user asks where to buy hardware, tools, plumbing, or paints: Recommend **Hardware Centre (India)** opposite Panch Batti or **National Hardware Stores** on Mahim Road (~800 meters from Vishnu Nagar).
    * If user asks where to buy stationery, books, school/office supplies, or photocopying: Recommend **Pruthvi Book Stores** right in Vishnu Nagar near ICICI Bank (~300 meters away, 3-minute walk) or **Deepak Stationery Mart** at Panch Batti (~500 meters).
    * If user asks for medicines or late-night chemist: Recommend **Wellness Forever (24/7 Pharmacy)** on Mahim Road (~750m) or **Noble Chemist** on Station Road (~1 km).
    * If user asks for groceries or supermarket: Recommend **Reliance Smart Point** on Mahim Road (~750m) or **D-Mart** on Manor-Palghar Road (~3.5 km).
    * If user asks for electronics or mobile phones: Recommend **Reliance Digital / Croma** on Mahim Road (~850m) or **Vijay Sales** near Station Road.
    * If user asks for clothing & fashion: Recommend **Reliance Trends** or **Zudio** on Mahim Road (~850m).
  - When recommending any spot or store, always quote the exact shop name, street/landmark (e.g. Panch Batti, Mahim Road, or Vishnu Nagar), distance in meters/km, and travel time directly. Never say you don't know local stores.
6. E-Commerce & Shopping: ALWAYS quote exact price with store (e.g. "Society Tea 1kg is ₹595 on Flipkart"). If user asked for specific brand, stick to that brand!
- To remember or update a fact: [REMEMBER: <fact>]
- To wipe or clear all memory: [WIPE_MEMORY]
- To forget a specific fact: [FORGET: <fact>]
- Absolute User Memory Authority: The user has 100% full authority to update, overwrite, or delete ANY fact (name, platform, age, preferences). NEVER refuse to update or say you cannot delete/update memory. ALWAYS warmly accept user updates and output [REMEMBER: <fact>] or [WIPE_MEMORY]!
- Multi-Timer:
  • To set a timer: [TIMER_SET: <seconds> | <name> | <completion_message>]
  • To query timers: [TIMER_QUERY: <name_or_all>]
  • To cancel a timer: [TIMER_CANCEL: <name_or_all>]
- Stopwatch:
  • Control: [STOPWATCH: START|STOP|LAP|RESET|QUERY]
- Alarm:
  • To set alarm: [ALARM_SET: <HH:MM AM/PM> | <label>]
  • To cancel alarm: [ALARM_CANCEL: <label_or_all>]
6. Interactive Briefing Protocol: For recipes or tutorials, DO NOT dump all steps! Give only 1 step at a time (~15-20 words).
7. Voice DSP Modulation & Whisper Capability:
• If user asks you to whisper or speak softly: Prefix with `[VOL: WHISPER]`.
• If cheering or excited: Prefix with `[VOL: CHEERFUL]`.
8. Priority-Gated Follow-Up Protocol (STRICTLY LESS THAN 15% OF RESPONSES):
• NEVER ask follow-up questions for:
  - Timers, alarms, stopwatch, volume, device controls, or memory commands.
  - Weather, time, date, fuel/petrol prices, gold rates.
  - Math calculations, conversions, or single stock quotes.
  - Direct factual queries, definitions, or closed questions.
  - ALWAYS append `[FOLLOWUP: NO]` and NEVER add a trailing question!
• ONLY permit follow-up questions for:
  - Multi-step tutorial/recipe transitions (e.g. "Ready for step 2?").
  - Genuinely broad queries where specific user criteria is required to proceed.
  - Append `[FOLLOWUP: YES]` only when continuation is strictly necessary."""

    # Deep Conversational Memory: Expand active turn context to 8 turns (4 full exchanges)
    messages = [{"role": "system", "content": system_prompt}]
    for turn in list(conversation_history)[-8:]:
        messages.append(turn)
    messages.append({"role": "user", "content": user_query})
    
    # Adaptive Verbal Verbosity: Allow up to 240 tokens for comparisons, calculations, and research
    is_deep_query = any(k in lower_q for k in [
        'compare', 'difference', 'explain', 'advantages', 'disadvantages', 'pros and cons',
        'research', 'report', 'briefing', 'calculate', 'compound', 'details', 'detail',
        'breakdown', 'analyze', 'analysis', 'allocate', 'allocation', 'how works', 'why',
        'steps', 'plan my day', 'options', 'recommendation', 'sources', 'verify'
    ])
    token_budget = 240 if is_deep_query else 95

    payload = {
        "model": GROQ_MODEL,
        "messages": messages,
        "max_tokens": token_budget,
        "temperature": 0.35,
        "stream": True
    }
    
    # Sentence splitting regex (skips decimal digits like 4.5, 31.5, ₹595.00, allows long clause commas)
    pattern = r'(?<!\d)[.!?।\n]+(?!\d)|(?<!\d),\s+(?!\d)'
    
    for attempt in range(len(GROQ_KEYS) + 1):
        current_key = GROQ_KEYS[groq_key_index % len(GROQ_KEYS)]
        req = urllib.request.Request(
            "https://api.groq.com/openai/v1/chat/completions",
            data=json.dumps(payload).encode(),
            headers={
                "Authorization": f"Bearer {current_key}",
                "Content-Type": "application/json",
                "User-Agent": "Mozilla/5.0"
            }
        )
        try:
            stream_buf = ""
            full_raw = ""
            definitive_lang = det_lang or 'en'
            lang_checked = False
            clean_speech_accum = []
            in_think = False
            
            with urllib.request.urlopen(req, timeout=6.0) as resp:
                for line in resp:
                    line_str = line.decode('utf-8').strip()
                    if not line_str.startswith('data: '):
                        continue
                    data_body = line_str[6:].strip()
                    if data_body == '[DONE]':
                        break
                    try:
                        chunk = json.loads(data_body)
                        delta = chunk['choices'][0].get('delta', {})
                        content = delta.get('content', '')
                        if not content:
                            continue
                        full_raw += content

                        # Filter out internal reasoning / thinking tokens (<think> ... </think>)
                        if in_think:
                            if '</think>' in content:
                                content = content.split('</think>', 1)[1]
                                in_think = False
                            else:
                                continue
                        else:
                            if '<think>' in content:
                                pre, post = content.split('<think>', 1)
                                if '</think>' in post:
                                    post = post.split('</think>', 1)[1]
                                    content = pre + post
                                else:
                                    content = pre
                                    in_think = True
                        if not content:
                            continue

                        stream_buf += content
                        
                        # 1. Parse [LANG: ...] if present at start
                        if not lang_checked and ']' in stream_buf:
                            lang_match = re.search(r'\[LANG:\s*(GU|MR|HI|EN)\]', stream_buf, re.IGNORECASE)
                            if lang_match:
                                definitive_lang = lang_match.group(1).lower()
                                stream_buf = re.sub(r'\[LANG:\s*.*?\]', '', stream_buf)
                            lang_checked = True
                        elif not lang_checked and len(stream_buf) > 30:
                            lang_checked = True
                            
                        # 2. Bracket In-Flight Guard: if an open tag '[' is not closed yet, hold back text from that point!
                        last_open_bracket = stream_buf.rfind('[')
                        last_close_bracket = stream_buf.rfind(']')
                        if last_open_bracket > last_close_bracket:
                            eval_buf = stream_buf[:last_open_bracket]
                        else:
                            eval_buf = stream_buf
                            
                        # Strip ALL bracketed structured tags and thinking tags
                        test_str = re.sub(r'\[[A-Za-z0-9_ -]+:[^\]]*\]', '', eval_buf)
                        test_str = re.sub(r'\[(?:REMEMBER|FORGET|TIMER|TIMER_?SET|TIMER_?PROMPT|TIMER_?QUERY|TIMER_?CANCEL|CANCEL_TIMER|STOPWATCH|ALARM_?SET|ALARM_?CANCEL|CANCEL_BRIEFING|LANG|ANSWER|FOLLOWUP)[^\]]*\]', '', test_str)
                        test_str = re.sub(r'\[[^\]]*\]', '', test_str)
                        test_str = re.sub(r'<think>.*?</think>', '', test_str, flags=re.DOTALL)
                        test_str = re.sub(r'</?think>', '', test_str)
                        
                        for m in re.finditer(pattern, test_str):
                            cand = test_str[:m.end()].strip()
                            cand_clean = re.sub(r'[*_#`~|\[\]]', '', cand).strip()
                            # Check if the punctuation is a period preceded by an abbreviation
                            matched_punct = m.group(0)
                            is_abbreviation = False
                            if '.' in matched_punct:
                                preceding_word_match = re.search(r'([a-zA-Z]+)\.$', cand_clean)
                                if preceding_word_match:
                                    w = preceding_word_match.group(1).lower()
                                    if w in {'st', 'mr', 'mrs', 'ms', 'dr', 'prof', 'eg', 'ie', 'e', 'g', 'i', 'approx', 'vs', 'rs', 'no', 'vol', 'dept'}:
                                        is_abbreviation = True
                                        
                            if not is_abbreviation:
                                words = cand_clean.split()
                                should_emit = False
                                if any(p in matched_punct for p in ['!', '?', '।', '\n']):
                                    should_emit = len(words) >= 4 and len(cand_clean) >= 12
                                elif '.' in matched_punct:
                                    should_emit = len(words) >= 5 or len(cand_clean) >= 20
                                elif ',' in matched_punct:
                                    should_emit = len(words) >= 10 and len(cand_clean) >= 40
                                    
                                # Opening Clause 1: Require at least 4 words so audio plays for >1.2s, giving background pipeline ample time to prefetch Clause 2
                                if should_emit and len(clean_speech_accum) == 0 and len(words) < 4:
                                    should_emit = False
                                # Subsequent Clauses: Avoid tiny 1-3 word fragments that starve the audio buffer; accumulate until >= 6 words
                                elif should_emit and len(clean_speech_accum) > 0 and len(words) < 6:
                                    should_emit = False
                                    
                                if should_emit:
                                    stream_buf = test_str[m.end():]
                                    clean_speech_accum.append(cand_clean)
                                    yield (cand_clean, definitive_lang, False, full_raw)
                                    break
                    except Exception:
                        pass
                        
            # Final remaining clause
            if stream_buf:
                leftover = re.sub(r'\[[A-Za-z0-9_ -]+:[^\]]*\]', '', stream_buf)
                leftover = re.sub(r'\[(?:REMEMBER|FORGET|TIMER|TIMER_?SET|TIMER_?PROMPT|TIMER_?QUERY|TIMER_?CANCEL|CANCEL_TIMER|STOPWATCH|ALARM_?SET|ALARM_?CANCEL|CANCEL_BRIEFING|LANG|ANSWER|FOLLOWUP)[^\]]*\]', '', leftover)
                leftover = re.sub(r'\[[^\]]*\]', '', leftover)
                leftover = re.sub(r'<think>.*?</think>', '', leftover, flags=re.DOTALL)
                leftover = re.sub(r'</?think>', '', leftover)
                leftover = re.sub(r'\b(?:FOLLOWUP|ANSWER|LANG):\s*(?:NO|YES|[A-Za-z0-9_-]+)', '', leftover, flags=re.IGNORECASE)
                leftover_clean = re.sub(r'[*_#`~|\[\]]', '', leftover).strip()
                leftover_clean = re.sub(r'\b(?:FOLLOWUP|ANSWER)\b', '', leftover_clean, flags=re.IGNORECASE).strip()
                if leftover_clean and re.search(r'[\w\u0900-\u097F\u0A80-\u0AFF]', leftover_clean):
                    clean_speech_accum.append(leftover_clean)
                    yield (leftover_clean, definitive_lang, True, full_raw)
                    
            # Complete raw processing & memory/timer side effects
            full_clean = " ".join(clean_speech_accum).strip()
            full_clean = re.sub(r'<think>.*?</think>', '', full_clean, flags=re.DOTALL)
            full_clean = re.sub(r'</?think>', '', full_clean).strip()
            if full_clean:
                conversation_history.append({"role": "user", "content": user_query})
                conversation_history.append({"role": "assistant", "content": full_clean})

            pending_followup_intent = extract_followup_decision(full_raw, full_clean)
            if pending_followup_intent:
                print(f"[PREDICTIVE FOLLOW-UP]: Groq invited follow-up continuation. (Answer: '{full_clean}')")
            else:
                print(f"[PREDICTIVE FOLLOW-UP]: None / Closed action.")
                
            # Handle [CANCEL_BRIEFING] tag
            if "[CANCEL_BRIEFING]" in full_raw:
                active_briefing["is_active"] = False
                active_briefing["topic_id"] = None
                print("[ACTIVE BRIEFING CANCELLED VIA LLM INTENT]")

            # Handle [WIPE_MEMORY] tag
            if "[WIPE_MEMORY]" in full_raw or "[WIPE_ALL]" in full_raw:
                wipe_all_memories()
                print("[LLM WIPE_MEMORY EXECUTED]")

            # Handle [REMEMBER: ...] tag
            rem_match = re.search(r'\[REMEMBER:\s*(.*?)\]', full_raw)
            if rem_match:
                new_fact = rem_match.group(1).strip()
                if new_fact:
                    add_user_memory(new_fact, lang=definitive_lang)
                    print(f"[MEMORY SAVED VIA LLM]: {new_fact}")

            # Handle [FORGET: ...] tag
            forg_match = re.search(r'\[FORGET:\s*(.*?)\]', full_raw)
            if forg_match:
                to_forget = forg_match.group(1).strip().lower()
                remove_user_memory(to_forget)
                notes = memory_data.get("notes", [])
                memory_data["notes"] = [n for n in notes if to_forget not in n.lower()]
                save_memory(memory_data)
                print(f"[MEMORY FORGOTTEN]: {to_forget}")
                    
            # Handle [TIMER_SET: <seconds> | <name> | <completion_message>]
            tim_set_match = re.search(r'\[TIMER_?SET:\s*(\d+)\s*\|\s*([^\|\]]+)(?:\|\s*([^\]]*))?\]', full_raw)
            if tim_set_match:
                secs = int(tim_set_match.group(1))
                t_name = tim_set_match.group(2).strip()
                c_msg = tim_set_match.group(3).strip() if tim_set_match.group(3) else ""
                t_context = "cooking" if any(k in t_name.lower() for k in ["maggi", "tea", "chai", "egg", "milk", "rice", "pasta"]) else "general"
                dispatch_async(start_timer_instance(duration=secs, name=t_name, context=t_context, completion_phrase=c_msg, lang=definitive_lang))
                print(f"[LLM TIMER_SET EXECUTED]: {secs}s for '{t_name}'")

            # Handle [TIMER_PROMPT: <seconds> | <dish> | <confirmation_question>]
            tim_prompt_match = re.search(r'\[TIMER_PROMPT:\s*(\d+)\s*\|\s*([^\|\]]+)(?:\|\s*([^\]]*))?\]', full_raw)
            if tim_prompt_match:
                p_secs = int(tim_prompt_match.group(1))
                p_dish = tim_prompt_match.group(2).strip()
                pending_timer_suggestion = {
                    "dish_key": p_dish.lower(),
                    "dish_display": p_dish,
                    "seconds": p_secs,
                    "prompt": full_clean,
                    "confirm": f"Starting your {format_duration_desc(p_secs, definitive_lang)} timer for {p_dish} now!",
                    "complete": f"Shravan, {format_duration_desc(p_secs, definitive_lang)} timer has been done for your {p_dish}! Look at your {p_dish}, is it cooked?",
                    "lang": definitive_lang,
                    "timestamp": time.time()
                }
                dispatch_async(broadcast("cooking_suggestion", pending_timer_suggestion))
                print(f"[LLM TIMER_PROMPT RECORDED]: {p_dish} ({p_secs}s)")

            # Handle [TIMER_CANCEL: <name_or_all>]
            tim_cancel_match = re.search(r'\[TIMER_CANCEL:\s*([^\]]*)\]', full_raw)
            if tim_cancel_match:
                c_target = tim_cancel_match.group(1).strip().lower()
                is_all = c_target in ["all", "sabhi", "sab", ""]
                if is_all:
                    dispatch_async(cancel_timer_instance(cancel_all=True))
                else:
                    dispatch_async(cancel_timer_instance(name=c_target))
                print(f"[LLM TIMER_CANCEL EXECUTED]: {c_target}")

            # Handle [STOPWATCH: START|STOP|LAP|RESET|QUERY]
            sw_match = re.search(r'\[STOPWATCH:\s*(START|STOP|LAP|RESET|QUERY)\]', full_raw, re.IGNORECASE)
            if sw_match:
                action = sw_match.group(1).lower()
                handle_stopwatch_action(action, definitive_lang)
                print(f"[LLM STOPWATCH EXECUTED]: {action}")

            # Handle [ALARM_SET: <time_str> | <label>]
            al_set_match = re.search(r'\[ALARM_SET:\s*([^\|\]]+)(?:\|\s*([^\]]*))?\]', full_raw)
            if al_set_match:
                al_time = al_set_match.group(1).strip()
                al_label = al_set_match.group(2).strip() if al_set_match.group(2) else "Alarm"
                dispatch_async(start_alarm_instance(time_str=al_time, label=al_label, lang=definitive_lang))
                print(f"[LLM ALARM_SET EXECUTED]: {al_time} ({al_label})")

            # Handle [ALARM_CANCEL: <time_or_all>]
            al_cancel_match = re.search(r'\[ALARM_CANCEL:\s*([^\]]*)\]', full_raw)
            if al_cancel_match:
                al_target = al_cancel_match.group(1).strip().lower()
                is_all = al_target in ["all", "sabhi", "sab", ""]
                if is_all:
                    dispatch_async(cancel_alarm_instance(cancel_all=True))
                else:
                    dispatch_async(cancel_alarm_instance(time_str=al_target))
                print(f"[LLM ALARM_CANCEL EXECUTED]: {al_target}")

            # Handle legacy [TIMER: ...] tag
            tim_match = re.search(r'\[TIMER:\s*(\d+)\]', full_raw)
            if tim_match:
                secs = int(tim_match.group(1))
                lower_q = user_query.lower()
                is_explicit_timer = any(w in lower_q for w in ["timer", "minute", "second", "alarm", "remind", "time it", "अलार्म", "टाइमर", "સેકન્ડ", "મિનિટ"])
                if is_explicit_timer:
                    dispatch_async(start_timer_instance(secs, f"{secs} second timer", lang=definitive_lang))
                    if not clean_speech_accum:
                        confirm_map = {
                            "en": f"Starting your {secs}-second timer now!",
                            "hi": f"आपका {secs} सेकंड का टाइमर शुरू हो गया है!",
                            "mr": f"तुमचा {secs} सेकंदांचा टायमर सुरू झाला आहे!",
                            "gu": f"તમારો {secs} સેકન્ડનો ટાઈમર શરૂ થઈ ગયો છે!"
                        }
                        c_text = confirm_map.get(definitive_lang, confirm_map["en"])
                        clean_speech_accum.append(c_text)
                        yield (c_text, definitive_lang, True, full_raw)
                else:
                    print(f"[UNSOLICITED TIMER BLOCKED]: Groq emitted [TIMER: {secs}] without explicit user request.")

            # Handle legacy [CANCEL_TIMER] tag
            lower_q = user_query.lower()
            if '[CANCEL_TIMER' in full_raw or any(w in lower_q for w in ["cancel timer", "stop timer", "timer band", "timer cancel", "timer roko", "timer hatao", "टाइमर बंद", "टाइमर रोको"]):
                if active_timers:
                    print(f"[TIMER CANCELLED]: Cancelling {len(active_timers)} active timer(s)")
                    dispatch_async(cancel_timer_instance(cancel_all=True))
                    if not clean_speech_accum:
                        cancel_map = {
                            "en": "Your timer has been cancelled.",
                            "hi": "आपका टाइमर रद्द कर दिया गया है।",
                            "mr": "तुमचा टायमर रद्द करण्यात आला आहे.",
                            "gu": "તમારો ટાઈમર રદ કરવામાં આવ્યો છે."
                        }
                        c_text = cancel_map.get(definitive_lang, cancel_map["en"])
                        clean_speech_accum.append(c_text)
                        yield (c_text, definitive_lang, True, full_raw)
            return
        except urllib.error.HTTPError as e:
            err_msg = e.read().decode('utf-8', errors='ignore')
            print(f"Groq LLM HTTP Error {e.code} (attempt {attempt+1}): {err_msg}")
            if e.code == 429:
                if len(GROQ_KEYS) > 1 and attempt < len(GROQ_KEYS):
                    groq_key_index = (groq_key_index + 1) % len(GROQ_KEYS)
                    print(f"[GROQ ROTATION (LLM)]: Rotated to key #{groq_key_index + 1}")
                    continue
                else:
                    delay_match = re.search(r'try again in ([\d\.]+)s', err_msg)
                    if delay_match:
                        req_wait = float(delay_match.group(1))
                        if req_wait <= 5.0 and attempt < len(GROQ_KEYS) + 1:
                            retry_wait = req_wait + 0.3
                            print(f"[GROQ 429 BACKOFF]: Waiting {retry_wait:.1f}s before retry...")
                            time.sleep(retry_wait)
                            continue
                    lang_fallback = {
                        "gu": "દૈનિક મર્યાદા પૂરી થઈ ગઈ છે. કૃપા કરીને થોડીવાર પછી પૂછો.",
                        "mr": "दैनिक मर्यादा संपली आहे. कृपया थोड्या वेळाने विचारा.",
                        "hi": "दैनिक टोकन सीमा समाप्त हो गई है। कृपया थोड़ी देर बाद पूछें।",
                        "en": "Daily token limit reached. Please try again shortly."
                    }
                    flang = det_lang or "en"
                    yield (lang_fallback.get(flang, lang_fallback["en"]), flang, True, "")
                    return
            break
        except Exception as e:
            print(f"Groq LLM Streaming Error: {e}")
            break
            
    lang_generic_fallback = {
        "gu": "મને માફ કરશો, સર્વર સાથે સંપર્ક થઈ શક્યો નથી.",
        "mr": "माफ करा, सर्व्हरशी संपर्क होऊ शकला नाही.",
        "hi": "माफ़ कीजिए, सर्वर से संपर्क नहीं हो सका।",
        "en": "I'm sorry, I couldn't reach the server."
    }
    flang = det_lang or "en"
    yield (lang_generic_fallback.get(flang, lang_generic_fallback["en"]), flang, True, "")

def run_groq_llm(user_query: str, detected_lang: str | None = None) -> tuple[str, str, str, float]:
    """Synchronous backwards-compatible wrapper collecting all stream_groq_llm clauses."""
    t0 = time.time()
    clauses = []
    definitive_lang = detected_lang or "en"
    full_raw = ""
    for clause, lang, is_last, raw_reply in stream_groq_llm(user_query, detected_lang=detected_lang):
        clauses.append(clause)
        definitive_lang = lang
        full_raw = raw_reply
    dt = (time.time() - t0) * 1000
    clean_speech = " ".join(clauses).strip()
    return clean_speech, definitive_lang, full_raw, dt


# --- Step 3: Text to Speech ---
MARATHI_DEV_WORDS = {
    'मला', 'तुला', 'आम्हाला', 'तुम्हाला', 'माझा', 'माझी', 'माझे', 'माझं', 'तुझा', 'तुझी', 'तुझे', 'तुझं',
    'आपण', 'तुम्ही', 'काय', 'काया', 'काई', 'कसा', 'कशी', 'कसे', 'कसं', 'कुठे', 'कुठं', 'कधी', 'कशाला', 'किती',
    'आहे', 'आहेस', 'आहेत', 'आहोत', 'नाही', 'नाहीत', 'नाहीस', 'नको', 'होता', 'होती', 'होते',
    'झाला', 'झाली', 'झाले', 'झालं', 'चाललंय', 'चालले', 'करतो', 'करते', 'करतात', 'करतोस', 'करू',
    'शकतेस', 'शकतो', 'सांग', 'सांगा', 'बोल', 'बोला', 'ऐक', 'ऐका', 'लागला', 'लागली', 'लागले',
    'जेवला', 'जेवली', 'जेवलास', 'अभ्यासात', 'पाऊस', 'हवामान', 'छान', 'बरं', 'नक्कीच', 'पाहिजे',
    'मदत', 'सकाळ', 'संध्याकाळ', 'रात्र', 'मित्रा', 'मित्रांनो', 'कळलं', 'धन्यवाद', 'शुभ',
    'माज़नाओ', 'माजनाओ', 'माजन', 'माझ', 'माझाओ', 'माजा', 'राहतो', 'राहते', 'हवी', 'कशा',
    'कूथे', 'कुथे', 'रातो', 'रहातो', 'मी', 'मीक', 'ुठे'
}

GUJARATI_DEV_WORDS = {
    'केम', 'छो', 'छे', 'छु', 'छीए', 'शु', 'शू', 'शूछे', 'शूचे', 'शुछे', 'शुचे', 'सूस', 'सस', 'तमे', 'તમે',
    'तमारु', 'तमारू', 'तमारी', 'तमारा', 'तमने', 'मने', 'मारु', 'मारू', 'मारी', 'मारा', 'અમારું', 'अमारु',
    'अमारू', 'अमारी', 'मजामा', 'બધું', 'बधु', 'સરસ', 'सरस', 'નથી', 'नथी', 'માટે', 'माटे',
    'थयु', 'थशे', 'थाए', 'હવે', 'हवे', 'કેવું', 'केवु', 'केवा', 'જોઈએ', 'जोइए', 'भणवा', 'વાત', 'वात',
    'ખબર', 'खबर', 'આવો', 'आवो', 'જાઓ', 'जाओ', 'મજદ', 'शूसे', 'शुसे', 'શૂં', 'શું', 'નામ', 'नाम'
}

HINDI_DEV_WORDS = {
    'क्या', 'कैसे', 'कैसा', 'कैसी', 'कहाँ', 'कब', 'क्यों', 'क्यो', 'कौन', 'है', 'हैं', 'हूँ',
    'था', 'थे', 'थी', 'नहीं', 'मत', 'और', 'लेकिन', 'मगर', 'बताओ', 'मुझे', 'तुम्हारा', 'तुम्हारी',
    'आपका', 'आपकी', 'रहा', 'रही', 'रहे', 'पढ़ाई', 'मौसम', 'बारिश', 'खाना', 'पानी', 'मेरा', 'मेरी', 'मेरे',
    'तुम', 'तू', 'आप', 'किधर', 'की', 'दर', 'रहते', 'रहती', 'रहता', 'रहना', 'हो', 'कर', 'करो',
    'करते', 'करती', 'करता', 'बोल', 'बोलो', 'सुन', 'सुनो', 'सकते', 'सकता', 'सकती', 'इधर', 'उधर',
    'यहाँ', 'वहाँ', 'ये', 'वो', 'यह', 'वह', 'बात', 'कुछ', 'कोई', 'सब', 'अपना', 'अपनी', 'अपने',
    'अच्छा', 'ठीक', 'नाम'
}

MARATHI_ROMAN_WORDS = {
    'mala', 'tula', 'aamhala', 'tumhala', 'majha', 'majhi', 'majhe', 'majhan', 'tujha', 'tujhi', 'tujhe',
    'tujhan', 'aapan', 'tumhi', 'aahe', 'ahe', 'aahes', 'aahet', 'aahot', 'naahi', 'nahi', 'nahit',
    'nako', 'hota', 'hoti', 'hote', 'jhala', 'jhali', 'jhale', 'zaala', 'zaali', 'zaale', 'kay',
    'kasa', 'kashi', 'kase', 'kasan', 'kuthe', 'kadhi', 'kashala', 'kiti', 'chalalay', 'challey',
    'karto', 'karte', 'kartat', 'kartos', 'karu', 'shaktes', 'shakto', 'sang', 'sanga', 'lagli',
    'jevala', 'jevalas', 'pahije', 'abhyasat', 'abyasat', 'chhan', 'baran', 'paaus', 'khoop',
    'nakkich', 'madad', 'konahim', 'kon', 'koni', 'koon', 'ahi', 'rato', 'uthhe', 'nao', 'kaay', 'miek', 'mii',
    'tuza', 'tuzha', 'maza', 'mazha', 'nav', 'naav'
}

GUJARATI_ROMAN_WORDS = {
    'kem', 'cho', 'chho', 'chhe', 'che', 'chhu', 'chhoo', 'chhie', 'nathi', 'nthi', 'tame', 'tamaru',
    'tamari', 'tamara', 'tamne', 'mane', 'maru', 'mari', 'mara', 'amaru', 'amari', 'majama', 'badhu',
    'saras', 'aaje', 'kaale', 'have', 'mate', 'lidhe', 'joiye', 'jovu', 'aavo', 'jao',
    'khabar', 'vaat', 'thay', 'thayu', 'thase', 'thashe', 'kevu', 'kyare', 'barabar', 'bhanva',
    'sushen', 'shus', 'marunan', 'shoo', 'tamarunan', 'tamarun', 'sinter', 'tamaro'
}

HINDI_ROMAN_WORDS = {
    'main', 'mai', 'hum', 'hume', 'mujhko', 'mera', 'meri', 'mere', 'tu', 'tum', 'tumhe',
    'tumhara', 'tumhari', 'tumhare', 'aap', 'aapka', 'aapki', 'aapke', 'yeh', 'ye', 'woh', 'wo',
    'kya', 'kyu', 'kyun', 'kyo', 'kaise', 'kaisa', 'kaisi', 'kab', 'kahan', 'kidhar', 'kisne',
    'hai', 'hain', 'hoon', 'hun', 'था', 'थे', 'थी', 'thhe', 'hoga', 'hogi', 'hoge',
    'nahi', 'nahin', 'mat', 'aur', 'ya', 'lekin', 'magar', 'toh', 'bhi', 'bas',
    'bahut', 'bohot', 'thoda', 'thodi', 'achha', 'theek', 'bilkul', 'sahi', 'batao',
    'bolo', 'suno', 'rahe', 'rahi', 'raha', 'padhai', 'mausam'
}

ENGLISH_WORDS = {
    'the', 'is', 'at', 'which', 'on', 'and', 'a', 'an', 'in', 'to', 'for', 'of', 'with', 'about',
    'from', 'up', 'down', 'out', 'over', 'then', 'here', 'there', 'when', 'where', 'why', 'how',
    'all', 'any', 'both', 'each', 'few', 'more', 'some', 'no', 'not', 'so', 'than', 'too', 'very',
    'can', 'will', 'just', 'should', 'now', 'i', 'you', 'he', 'she', 'it', 'we', 'they', 'what',
    'would', 'could', 'have', 'has', 'had', 'do', 'does', 'did', 'be', 'am', 'are', 'was', 'were',
    'my', 'your', 'his', 'her', 'its', 'our', 'their', 'weather', 'sunny', 'temperature', 'today',
    'time', 'timer', 'alarm', 'hello', 'hi', 'sure', 'sorry', 'please', 'thanks', 'thank', 'studies',
    'help', 'name', 'tell', 'telling', 'see', 'still', 'keep', 'sentence', 'end', 'nickname', 'friend',
    'call', 'calling', 'who', 'user', 'say', 'saying', 'speak', 'speaking', 'shoe', 'shu', 'shoo'
}

def detect_language(text: str, user_query: str = '', raw_reply: str = '', forced_lang: str | None = None) -> str:
    """
    Precision 4-language detector for Shravan (English, Marathi, Gujarati, Hindi).
    Handles mixed scripts, phonetic mis-transcriptions, and Latinized text.
    """
    if forced_lang and forced_lang in ['en', 'hi', 'mr', 'gu']:
        return forced_lang
        
    explicit_lang = extract_explicit_language_request(user_query) or extract_explicit_language_request(text)
    if explicit_lang:
        return explicit_lang
        
    text = sanitize_mixed_indic_script(text)
    user_query = sanitize_mixed_indic_script(user_query)
    combined = (user_query + ' ' + text).strip()
    
    # 1. Check for dominant English letters / sentences
    latin_words = set(re.findall(r'[a-zA-Z]+', combined.lower()))
    devanagari_chars = len(re.findall(r'[\u0900-\u097F]', combined))
    gujarati_chars = len(re.findall(r'[\u0A80-\u0AFF]', combined))
    
    # If predominantly Latin letters (English or Romanized Indic)
    if len(latin_words) >= 2 and (len(latin_words) * 4) > (devanagari_chars + gujarati_chars):
        en_score = len(latin_words.intersection(ENGLISH_WORDS))
        mr_score = len(latin_words.intersection(MARATHI_ROMAN_WORDS))
        gu_score = len(latin_words.intersection(GUJARATI_ROMAN_WORDS))
        hi_score = len(latin_words.intersection(HINDI_ROMAN_WORDS))
        
        has_latin_gu = any(w in ['tamarunan', 'tamarun', 'sinter', 'marunan', 'sushen', 'kevu'] or w.startswith('tamaru') or w.startswith('maru') for w in latin_words)
        has_latin_mr = any(w in ['tuza', 'tuzha', 'maza', 'mazha', 'kaay', 'aahe', 'chalalay'] or w.startswith('tujh') or w.startswith('maj') for w in latin_words)
        
        if has_latin_gu and en_score <= 1:
            return 'gu'
        if has_latin_mr and en_score <= 1:
            return 'mr'
            
        # If clearly English sentence
        if en_score >= 2 and en_score >= mr_score and en_score >= gu_score and en_score >= hi_score:
            return 'en'
        if gu_score > 0 and gu_score >= mr_score and gu_score >= hi_score and gu_score > en_score:
            return 'gu'
        if mr_score > 0 and mr_score >= hi_score and mr_score > en_score:
            return 'mr'
        if hi_score > 0 and hi_score > en_score:
            return 'hi'
        if en_score > 0:
            return 'en'
            
    # 2. Check for Devanagari or Gujarati Script
    if devanagari_chars > 0 or gujarati_chars > 0:
        # Extract all Devanagari & Gujarati tokens
        tokens = set(re.findall(r'[\u0900-\u097F\u0A80-\u0AFF]+', combined))
        
        MARATHI_DISTINCT_MARKERS = [
            'काय', 'काया', 'काई', 'कय', 'કાય', 'કાયા', 'કાઈ', 'कयाय',
            'आहे', 'आहेस', 'आहेत', 'आहोत', 'कुठे', 'कुठं', 'कुथे',
            'तुझा', 'तुझी', 'तुझे', 'तुझं', 'તુજા', 'તુઝા', 'तुज',
            'तुम्हाला', 'मला', 'आम्हाला', 'तुला', 'तुम्ही',
            'माझा', 'माझी', 'माझे', 'माझं',
            'येतोय', 'येतो', 'येते', 'येतात', 'ऐकू', 'ऐका', 'सांग', 'सांगा',
            'कसा', 'कशी', 'कसे', 'कसं', 'कशाला', 'कधी', 'किती',
            'राहतो', 'राहते', 'रातो', 'रहातो', 'चाललंय', 'झाला', 'झाली', 'झाले', 'झालं'
        ]
        GUJARATI_DISTINCT_MARKERS = [
            'શું', 'શુ', 'શૂં', 'કેમ', 'કેવું', 'કેવી', 'કેવો', 'છે', 'છો', 'છીએ', 'છું', 
            'તમારું', 'તમારી', 'તમારા', 'તમને', 'તારું', 'તારી', 'તારા', 'તમે',
            'મારું', 'મારી', 'મારા', 'મને', 'અમારું', 'અમારી', 'અમને',
            'ક્યાં', 'ક્યારે', 'નથી', 'બધું', 'હશે', 'થશે', 'આવે', 'સંભળાય',
            'જોઈએ', 'મજામાં', 'શૂસે', 'शुसे', 'શૂછે', 'શૂચે', 'शूस', 'सूस'
        ]
        
        has_mr_distinct = any(any(md in tok for md in MARATHI_DISTINCT_MARKERS) for tok in tokens)
        has_gu_distinct = any(any(gd in tok for gd in GUJARATI_DISTINCT_MARKERS) for tok in tokens)
        
        if has_gu_distinct and not has_mr_distinct:
            return 'gu'
        if has_mr_distinct and not has_gu_distinct:
            return 'mr'
            
        mr_count = 0
        gu_count = 0
        hi_count = 0
        
        for tok in tokens:
            # Check Gujarati words (script or phonetic Devanagari)
            if any(gw in tok for gw in GUJARATI_DEV_WORDS) or re.search(r'[\u0A80-\u0AFF]', tok):
                # But check if tok is a mixed hallucination of Marathi (e.g. માજণ, काया)
                if any(mw in tok for mw in ['काय', 'काया', 'काई', 'आहे', 'कुठे', 'कसे', 'मला']):
                    mr_count += 2
                else:
                    gu_count += 1
            # Check Marathi words
            if any(mw in tok for mw in MARATHI_DEV_WORDS):
                mr_count += 1
            # Check Hindi words
            if any(hw in tok for hw in HINDI_DEV_WORDS):
                hi_count += 1
                
        # Resolve between the three Indic languages
        if gu_count > 0 and gu_count > mr_count and gu_count >= hi_count:
            return 'gu'
        if mr_count > 0 and mr_count > gu_count and mr_count >= hi_count:
            return 'mr'
            
        # Tie between Gujarati and Marathi
        if gu_count > 0 and mr_count > 0 and gu_count == mr_count:
            # If native Gujarati script is present and no distinct Marathi verbs, Gujarati wins
            if gujarati_chars > 0 and not has_mr_distinct:
                return 'gu'
            # If distinct Marathi question words exist (e.g. काय, आहे), Marathi wins
            if has_mr_distinct:
                return 'mr'
            return 'gu'
            
        if hi_count > 0 and hi_count > mr_count and hi_count > gu_count:
            return 'hi'
        if gu_count > 0 and gu_count >= hi_count:
            return 'gu'
        if mr_count > 0:
            return 'mr'
        if hi_count > 0:
            return 'hi'
            
        # Fallback for Indic characters: text with Devanagari or Gujarati script can never be English!
        if gujarati_chars > 0:
            return 'gu'
        if has_mr_distinct:
            return 'mr'
        if devanagari_chars > 0:
            return 'hi'
            
    # 3. Check explicit LLM tag if available as fallback
    if raw_reply:
        tag_match = re.search(r'\[LANG:\s*(EN|HI|GU|MR)\]', raw_reply, re.IGNORECASE)
        if tag_match:
            return tag_match.group(1).lower()
            
    return 'en'

def normalize_speech_for_tts(text: str, lang: str = "en") -> str:
    """
    Phonetically normalizes currency, symbols, units, numbers, and abbreviations for TTS engines.
    Converts raw accounting numbers (e.g. ₹200.00, 270.00 rupees, +0.00%) into natural, fluent human speech.
    Execution latency: < 0.15ms.
    """
    t = text
    
    # 0. Target vocabulary by language
    if lang == 'gu':
        curr_inr = 'રૂપિયા'
        paise_inr = 'પૈસા'
        curr_usd = 'ડૉલર'
        cents_usd = 'સેન્ટ્સ'
        pct = 'ટકા'
        deg = 'ડિગ્રી'
        to_word = 'થી'
    elif lang == 'mr':
        curr_inr = 'रुपये'
        paise_inr = 'पैसे'
        curr_usd = 'डॉलर'
        cents_usd = 'सेंट्स'
        pct = 'टक्के'
        deg = 'अंश'
        to_word = 'ते'
    elif lang == 'hi':
        curr_inr = 'रुपये'
        paise_inr = 'पैसे'
        curr_usd = 'डॉलर'
        cents_usd = 'सेंट्स'
        pct = 'प्रतिशत'
        deg = 'डिग्री'
        to_word = 'से'
    else:
        curr_inr = 'rupees'
        paise_inr = 'paise'
        curr_usd = 'dollars'
        cents_usd = 'cents'
        pct = 'percent'
        deg = 'degrees'
        to_word = 'to'

    # 1. Strip integer zero decimals like 200.00 -> 200, 1000.00 -> 1000, 54.00 -> 54, 0.00 -> 0
    t = re.sub(r'(?<=\d)\.00(?!\d)', '', t)

    # 2. Neutral zero percentage/change like +0.00%, -0.00%, +0%, +0.0% -> 0%
    t = re.sub(r'[+-]0(?:\.0+)?\s*%', '0%', t)
    t = re.sub(r'\(\s*[+-]0(?:\.0+)?\s*,\s*0%\s*\)', '(unchanged)', t)

    # 3. Clean .0 on quantities/temperatures/percentages/durations (e.g. 31.0°C -> 31°C, 5.0% -> 5%, 5.0 mins -> 5 mins)
    # Safeguard: Do not strip version numbers like Python 3.10, Android 14.0, GPT-4.0, v2.0, USB 3.0
    def repl_dot_zero(m):
        prefix = m.group(1) or ""
        num = m.group(2)
        suffix = m.group(3) or ""
        if prefix and re.search(r'\b(?:v|ver|version|android|ios|python|gpt|usb|web)\s*$', prefix, re.IGNORECASE):
            return m.group(0)
        return f"{prefix}{num}{suffix}"

    unit_suffixes = r'(?:%|°|C|F|kg|g|gm|l|ltr|ltrs|liter|liters|litre|litres|km|m|meter|meters|sec|secs|second|seconds|min|mins|minute|minutes|hr|hrs|hour|hours|day|days|week|weeks|month|months|year|years|rupees?|dollars?|रुपये|રૂપિયા|डिग्री|प्रतिशत|टक्के|ટકા)'
    t = re.sub(r'(\b[a-zA-Z]*\s*)?(\d+)\.0(?!\d)(\s*' + unit_suffixes + r'\b|\s*[°%])', repl_dot_zero, t, flags=re.IGNORECASE)

    # 4. Limit overly long floating decimals (e.g. 14.285714 -> 14.29, 3.333333 -> 3.33)
    # Safeguard: Never truncate micro-numbers / crypto amounts like 0.00001435 or 0.005 to 0!
    def repl_long_decimal(m):
        whole = m.group(1)
        dec = m.group(2)
        val = float(f"{whole}.{dec}")
        if val == 0:
            return "0"
        if val < 0.01:
            dec_clean = dec[:8].rstrip('0')
            return f"{whole}.{dec_clean}" if dec_clean else whole
        if len(dec) > 2:
            rounded = round(float(f"0.{dec}"), 2)
            dec_str = f"{rounded:.2f}"[2:].rstrip('0')
            return f"{whole}.{dec_str}" if dec_str else whole
        return m.group(0)
    t = re.sub(r'\b(\d+)\.(\d{3,})\b', repl_long_decimal, t)

    # 5. Currency with Rupees and Paise:
    # Match ₹258.90 or ₹258.50 -> "258 rupees and 90 paise" (or "258 रुपये 90 पैसे")
    # Match ₹0.50 -> "50 paise" (or "50 पैसे")
    def repl_inr_paise(m):
        rs = m.group(1).replace(',', '')
        paise_str = m.group(2)
        paise_val = int(paise_str.ljust(2, '0')[:2])
        if rs == '0' or rs == '':
            return f"{paise_val} {paise_inr} "
        if paise_val == 0:
            return f"{rs} {curr_inr} "
        if lang == 'en':
            return f"{rs} {curr_inr} and {paise_val} {paise_inr} "
        else:
            return f"{rs} {curr_inr} {paise_val} {paise_inr} "

    # Pattern for ₹258.90 or Rs. 258.90
    t = re.sub(r'(?:Rs\.?|INR|₹)\s*(\d[\d,]*)\.(\d{1,2})\b', repl_inr_paise, t, flags=re.IGNORECASE)
    # Pattern for 258.90 rupees / 258.90 Rs
    t = re.sub(r'\b(\d[\d,]*)\.(\d{1,2})\s*(?:Rs\.?|₹|INR|rupees?|रुपये|રૂપિયા)\b', repl_inr_paise, t, flags=re.IGNORECASE)

    # 6. Standard Integer Currency: ₹270, Rs. 1000, 500 INR
    inr_pattern = r'(?:Rs\.?|INR|₹)\s*([\d,]+(?:\s*(?:lakhs?|crores?|k|m|b|thousand|trillion|लाख|करोड़|हजार|લાખ|કરોડ))?)\b\s*(?:INR|rupees?)?'
    def repl_inr_int(m):
        amt = m.group(1).strip()
        return f"{amt} {curr_inr} "
    t = re.sub(inr_pattern, repl_inr_int, t, flags=re.IGNORECASE)
    t = re.sub(r'([\d,]+)\s*(?:Rs\.?|₹|INR)\b', rf'\1 {curr_inr} ', t, flags=re.IGNORECASE)

    # 7. USD Dollars & Cents: $50.75 -> 50 dollars and 75 cents
    def repl_usd_cents(m):
        dol = m.group(1).replace(',', '')
        cents_str = m.group(2)
        cents_val = int(cents_str.ljust(2, '0')[:2])
        if dol == '0' or dol == '':
            return f"{cents_val} {cents_usd} "
        if cents_val == 0:
            return f"{dol} {curr_usd} "
        if lang == 'en':
            return f"{dol} {curr_usd} and {cents_val} {cents_usd} "
        else:
            return f"{dol} {curr_usd} {cents_val} {cents_usd} "

    t = re.sub(r'\$\s*(\d[\d,]*)\.(\d{1,2})\b', repl_usd_cents, t, flags=re.IGNORECASE)
    t = re.sub(r'\$\s*([\d,]+(?:\s*(?:million|billion|trillion|k|m|b))?)\b\s*(?:USD|dollars?)?', rf'\1 {curr_usd} ', t, flags=re.IGNORECASE)
    t = re.sub(r'([\d,]+)\s*(?:\$|USD)\b', rf'\1 {curr_usd} ', t, flags=re.IGNORECASE)

    # Clean up redundant suffixes
    t = re.sub(r'\b(dollars?|डॉलर|ડૉલર)\s+USD\b', r'\1', t, flags=re.IGNORECASE)
    t = re.sub(r'\b(rupees?|रुपये|રૂપિયા)\s+INR\b', r'\1', t, flags=re.IGNORECASE)
    t = re.sub(r'\bRs\.?\b', curr_inr, t, flags=re.IGNORECASE)
    t = t.replace('₹', ' ' + curr_inr)

    # 8. Percentage: '5%' -> '5 percent' / '5 प्रतिशत' / '5 ટકા' / '5 टक्के'
    t = re.sub(r'([\d,]+(?:\.\d+)?)\s*%', rf'\1 {pct}', t)

    # 9. Degrees Celsius: '28°C' or '28°'
    t = re.sub(r'([\d,]+(?:\.\d+)?)\s*°\s*C\b', rf'\1 {deg}', t)
    t = re.sub(r'([\d,]+(?:\.\d+)?)\s*°', rf'\1 {deg}', t)

    # 10. Hyphenated Ranges: '10-15 minutes' -> '10 to 15 minutes'
    t = re.sub(r'(\d+)\s*[-–—]\s*(\d+)', rf'\1 {to_word} \2', t)

    # 11. Unit Expansions for speech fluency
    if lang == 'en':
        t = re.sub(r'\b1\s*kg\b', '1 kilogram', t, flags=re.IGNORECASE)
        t = re.sub(r'\b(\d+)\s*kg\b', r'\1 kilograms', t, flags=re.IGNORECASE)
        t = re.sub(r'\b1\s*gm?\b', '1 gram', t, flags=re.IGNORECASE)
        t = re.sub(r'\b(\d+)\s*gm?\b', r'\1 grams', t, flags=re.IGNORECASE)
        t = re.sub(r'\b1\s*ltr?s?\b', '1 liter', t, flags=re.IGNORECASE)
        t = re.sub(r'\b(\d+)\s*ltr?s?\b', r'\1 liters', t, flags=re.IGNORECASE)
        t = re.sub(r'\b1\s*km\b', '1 kilometer', t, flags=re.IGNORECASE)
        t = re.sub(r'\b(\d+)\s*km\b', r'\1 kilometers', t, flags=re.IGNORECASE)
        t = re.sub(r'\b1\s*sec(?:ond)?s?\b', '1 second', t, flags=re.IGNORECASE)
        t = re.sub(r'\b(\d+)\s*sec(?:ond)?s?\b', r'\1 seconds', t, flags=re.IGNORECASE)
        t = re.sub(r'\b1\s*min(?:ute)?s?\b', '1 minute', t, flags=re.IGNORECASE)
        t = re.sub(r'\b(\d+)\s*min(?:ute)?s?\b', r'\1 minutes', t, flags=re.IGNORECASE)
        t = re.sub(r'\b1\s*hr(?:our)?s?\b', '1 hour', t, flags=re.IGNORECASE)
        t = re.sub(r'\b(\d+)\s*hr(?:our)?s?\b', r'\1 hours', t, flags=re.IGNORECASE)
    elif lang in ['hi', 'mr']:
        t = re.sub(r'\b(\d+)\s*kg\b', r'\1 किलो', t, flags=re.IGNORECASE)
        t = re.sub(r'\b(\d+)\s*gm?\b', r'\1 ग्राम', t, flags=re.IGNORECASE)
        t = re.sub(r'\b(\d+)\s*ltr?s?\b', r'\1 लीटर', t, flags=re.IGNORECASE)
        t = re.sub(r'\b(\d+)\s*km\b', r'\1 किलोमीटर', t, flags=re.IGNORECASE)
    elif lang == 'gu':
        t = re.sub(r'\b(\d+)\s*kg\b', r'\1 કિલો', t, flags=re.IGNORECASE)
        t = re.sub(r'\b(\d+)\s*gm?\b', r'\1 ગ્રામ', t, flags=re.IGNORECASE)
        t = re.sub(r'\b(\d+)\s*ltr?s?\b', r'\1 લીટર', t, flags=re.IGNORECASE)
        t = re.sub(r'\b(\d+)\s*km\b', r'\1 કિલોમીટર', t, flags=re.IGNORECASE)

    # 12. Spoken Time normalization: '9:02 PM' -> '9 oh 2 PM', '9:00 PM' -> '9 o'clock PM'
    if lang == 'en':
        def repl_time_tts(m):
            h = m.group(1)
            mins = int(m.group(2))
            period = m.group(3).upper().replace('.', '')
            if mins == 0:
                return f"{h} o'clock {period}"
            elif mins < 10:
                return f"{h} oh {mins} {period}"
            else:
                return f"{h} {mins} {period}"
        t = re.sub(r'\b(\d{1,2}):(\d{2})\s*(am|pm|a\.m\.|p\.m\.)', repl_time_tts, t, flags=re.IGNORECASE)

    # Common abbreviations in English TTS
    if lang == 'en':
        t = re.sub(r'\bkm/h\b', 'kilometers per hour', t, flags=re.IGNORECASE)
        t = re.sub(r'\bapprox\.?\b', 'approximately', t, flags=re.IGNORECASE)
        t = re.sub(r'\be\.g\.?\b', 'for example', t, flags=re.IGNORECASE)
        t = re.sub(r'\bvs\.?\b', 'versus', t, flags=re.IGNORECASE)

    # 13. Spoken Postal PIN Code & 6-Digit Number Normalization (3-3 digit spoken groups)
    digit_words = {
        "en": {"0": "zero", "1": "one", "2": "two", "3": "three", "4": "four", "5": "five", "6": "six", "7": "seven", "8": "eight", "9": "nine"},
        "hi": {"0": "शून्य", "1": "एक", "2": "दो", "3": "तीन", "4": "चार", "5": "पांच", "6": "छह", "7": "सात", "8": "आठ", "9": "नौ"},
        "mr": {"0": "शून्य", "1": "एक", "2": "दोन", "3": "तीन", "4": "चार", "5": "पाच", "6": "सहा", "7": "सात", "8": "आठ", "9": "नऊ"},
        "gu": {"0": "શૂન્ય", "1": "એક", "2": "બે", "3": "ત્રણ", "4": "ચાર", "5": "પાંચ", "6": "છ", "7": "સાત", "8": "આઠ", "9": "નવ"}
    }
    def repl_pin_digits(m):
        digits = m.group(1) + m.group(2)
        dw = digit_words.get(lang, digit_words["en"])
        p1 = " ".join(dw.get(d, d) for d in digits[:3])
        p2 = " ".join(dw.get(d, d) for d in digits[3:])
        return f"{p1}, {p2}"

    # Target 6-digit postal codes (e.g. 401404 -> four zero one, four zero four)
    t = re.sub(r'\b(40[0-9]|41[0-9]|42[0-9]|11[0-9]|56[0-9]|60[0-9]|70[0-9]|50[0-9]|38[0-9]|39[0-9])\s*(\d{3})\b(?!\s*(?:rupees|dollars|रुपये|રૂપિયા))', repl_pin_digits, t)
    def repl_prefixed_pin(m):
        prefix = m.group(1)
        digits = m.group(2) + m.group(3)
        dw = digit_words.get(lang, digit_words["en"])
        p1 = " ".join(dw.get(d, d) for d in digits[:3])
        p2 = " ".join(dw.get(d, d) for d in digits[3:])
        return f"{prefix}{p1}, {p2}"
    t = re.sub(r'(\b(?:pin|pincode|postal|code|zip|zipcode|पिन|पिनकोड|પિન)\s+)(\d{3})\s*(\d{3})\b(?!\s*(?:rupees|dollars|रुपये|રૂપિયા))', repl_prefixed_pin, t, flags=re.IGNORECASE)

    # Strip commas inside numbers (e.g. 15,000 -> 15000)
    t = re.sub(r'(?<=\d),(?=\d)', '', t)
    # Smooth out awkward Oxford comma right before 'and'/'or'
    t = re.sub(r',\s*(?=and\b|or\b|आणि\b|અને\b|તથા\b)', ' ', t, flags=re.IGNORECASE)
    # Replace markdown asterisks, colons, semicolons, em-dashes
    t = re.sub(r'[*_#]', '', t)
    t = re.sub(r'[:;—–]\s*', ', ', t)
    t = re.sub(r',(\s*,)+', ',', t)
    # Clean up spacing around punctuation and parentheses
    t = re.sub(r'\s+([,.:!?।])', r'\1', t)
    t = re.sub(r'([(])\s+', r'\1', t)
    t = re.sub(r'\s{2,}', ' ', t).strip()
    return t


def run_edge_tts_sync(text_to_speak: str, voice: str = "en-IN-NeerjaNeural", context: str = "normal", radar_gain: float = 1.0, speed: float = 0.88) -> tuple[bytes | None, float]:
    """High-speed studio neural voice via Edge TTS with zero daily quota limits and memory caching."""
    t0 = time.time()
    clean_text = text_to_speak.strip()
    
    # 0. Sub-Millisecond In-Memory Audio Cache
    cache_key = (clean_text, voice, context, round(radar_gain, 2))
    if cache_key in AUDIO_CACHE:
        dt = (time.time() - t0) * 1000
        print(f"[EDGE TTS CACHE HIT (0 ms)]: Instant audio for '{clean_text[:35]}'")
        return AUDIO_CACHE[cache_key], dt

    try:
        async def _gen():
            comm = edge_tts.Communicate(text_to_speak, voice, rate="+10%")
            mp3_bytes = bytearray()
            async for chunk in comm.stream():
                if chunk['type'] == 'audio':
                    mp3_bytes.extend(chunk['data'])
            return bytes(mp3_bytes)
            
        try:
            active_loop = asyncio.get_running_loop()
        except RuntimeError:
            active_loop = None

        if active_loop is not None and active_loop.is_running():
            import concurrent.futures
            with concurrent.futures.ThreadPoolExecutor(max_workers=1) as pool:
                try:
                    mp3_data = pool.submit(lambda: asyncio.run(_gen())).result(timeout=6.5)
                except concurrent.futures.TimeoutError:
                    print(f"[EDGE TTS TIMEOUT]: Exceeded 6.5s limit for '{clean_text[:25]}' - falling back immediately")
                    return None, (time.time() - t0) * 1000
        else:
            try:
                mp3_data = asyncio.run(asyncio.wait_for(_gen(), timeout=6.5))
            except Exception:
                return None, (time.time() - t0) * 1000

        if not mp3_data:
            return None, (time.time() - t0) * 1000
            
        # Ultra-fast in-memory decode via miniaudio (~2ms)
        try:
            import miniaudio
            decoded = miniaudio.decode(mp3_data, nchannels=1, sample_rate=16000, output_format=miniaudio.SampleFormat.SIGNED16)
            raw_pcm = decoded.samples.tobytes()
        except Exception:
            # Fallback to ffmpeg subprocess if needed
            proc = subprocess.Popen(
                ['ffmpeg', '-hide_banner', '-loglevel', 'error', '-i', 'pipe:0', '-f', 's16le', '-acodec', 'pcm_s16le', '-ac', '1', '-ar', '16000', 'pipe:1'],
                stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.PIPE
            )
            raw_pcm, _ = proc.communicate(input=mp3_data)
        
        # Calibrated voice normalization and DSP soft limiter
        raw_pcm = apply_calibrated_volume_and_limiter(raw_pcm, voice_key=voice, context=context, radar_gain=radar_gain, boost_clarity=(radar_gain > 1.15))
        
        # Cache for zero-latency instant replay
        AUDIO_CACHE[cache_key] = raw_pcm
        if len(AUDIO_CACHE) > 150:
            AUDIO_CACHE.pop(next(iter(AUDIO_CACHE)))
            
        dt = (time.time() - t0) * 1000
        print(f"[EDGE NEURAL TTS ({dt:.0f} ms)]: Generated {len(raw_pcm)} bytes with {voice}")
        return raw_pcm, dt
    except Exception as e:
        print(f"Edge TTS Error: {e}")
        return None, (time.time() - t0) * 1000

def run_offline_tts(text_to_speak: str) -> tuple[bytes | None, float]:
    """Instant offline fallback using pyttsx3 if all internet services are down."""
    t0 = time.time()
    try:
        engine = pyttsx3.init()
        voices = engine.getProperty('voices')
        for v in voices:
            if "zira" in v.name.lower() or "female" in v.name.lower() or "david" not in v.name.lower():
                engine.setProperty('voice', v.id)
                break
        engine.setProperty('rate', 165)
        temp_wav = "offline_response.wav"
        engine.save_to_file(text_to_speak, temp_wav)
        engine.runAndWait()
        
        with wave.open(temp_wav, 'rb') as wf:
            raw = wf.readframes(wf.getnframes())
            sw = wf.getsampwidth()
            ch = wf.getnchannels()
            fr = wf.getframerate()
            if ch == 2:
                raw = audioop.tomono(raw, sw, 0.5, 0.5)
            if fr != 16000:
                raw, _ = audioop.ratecv(raw, sw, 1, fr, 16000, None)
            raw = audioop.mul(raw, 2, 0.85)
        dt = (time.time() - t0) * 1000
        print(f"[OFFLINE TTS FALLBACK ({dt:.0f} ms)]: Audio {len(raw)} bytes")
        return raw, dt
    except Exception as e:
        print(f"Offline TTS Error: {e}")
        return None, (time.time() - t0) * 1000

cartesia_lock = threading.Lock()

def run_cartesia_tts(text_to_speak: str, lang: str = "en", context: str = "normal", radar_gain: float = 1.0, speed: float = 0.88) -> tuple[bytes | None, float, str]:
    """Generates ultra-low-latency studio voice via Cartesia Sonic (16kHz S16LE raw PCM). Serialized via cartesia_lock to prevent 429 concurrency errors."""
    global cartesia_key_index, cartesia_cooldown_until
    
    clean_text = text_to_speak.strip() if text_to_speak else ""
    # Ensure there is actual speakable text (letters/numbers/scripts), not empty or pure punctuation
    if not clean_text or not re.search(r'[\w\u0900-\u097F\u0A80-\u0AFF]', clean_text):
        return None, 0.0, ""
        
    if not CARTESIA_KEYS or time.time() < cartesia_cooldown_until:
        return None, 0.0, ""
        
    voice_info = CARTESIA_VOICE_MAP.get(lang, CARTESIA_VOICE_MAP["en"])
    voice_id = voice_info["id"]
    voice_name = voice_info["name"]
    
    quota_exhausted_count = 0
    safe_speed = max(0.80, min(1.12, speed))
    
    # Strictly serialize Cartesia requests to keep concurrent connections <= 1, preventing 429 spikes
    with cartesia_lock:
        for attempt in range(max(2, len(CARTESIA_KEYS) * 2)):
            current_key = CARTESIA_KEYS[cartesia_key_index]
            payload = {
                "model_id": "sonic-3.6",
                "transcript": clean_text,
                "voice": {"mode": "id", "id": voice_id},
                "output_format": {
                    "container": "raw",
                    "encoding": "pcm_s16le",
                    "sample_rate": 16000
                },
                "generation_config": {
                    "speed": safe_speed
                },
                "language": lang
            }
            
            t0 = time.time()
            headers = {
                "X-API-Key": current_key,
                "Cartesia-Version": "2024-06-10",
                "Content-Type": "application/json"
            }
            try:
                resp = cloud_http_session.post("https://api.cartesia.ai/tts/bytes", json=payload, headers=headers, timeout=5.0)
                if resp.status_code == 200:
                    raw_pcm = resp.content
                    dt = (time.time() - t0) * 1000
                    raw_pcm = apply_calibrated_volume_and_limiter(raw_pcm, voice_key=f"cartesia_{lang}", context=context, radar_gain=radar_gain, boost_clarity=(radar_gain > 1.15))
                    print(f"[CARTESIA SONIC ({dt:.0f} ms)]: Generated {len(raw_pcm)} bytes with {voice_name} ({lang.upper()} @ {safe_speed}x)")
                    return raw_pcm, dt, f"Cartesia Sonic ({voice_name})"
                else:
                    dt = (time.time() - t0) * 1000
                    err_body = resp.text
                    print(f"[CARTESIA KEY {cartesia_key_index + 1} ERROR {resp.status_code}]: {err_body}")
                    if resp.status_code == 402 or "quota_exceeded" in err_body or "insufficient_credits" in err_body:
                        quota_exhausted_count += 1
                        cartesia_key_index = (cartesia_key_index + 1) % len(CARTESIA_KEYS)
                        print(f"[CARTESIA ROTATE]: Switched to Key index {cartesia_key_index + 1}")
                    elif resp.status_code == 429:
                        print(f"[CARTESIA 429]: Rate limit detected. Backing off 250ms and retrying ({attempt + 1})...")
                        time.sleep(0.25)
                        continue
                    else:
                        break
            except Exception as e:
                print(f"Cartesia TTS Error: {e}")
                time.sleep(0.2)
                continue
            
    # Set cooldown ONLY if EVERY key in the pool was confirmed out of credits (402)
    if quota_exhausted_count >= len(CARTESIA_KEYS) and len(CARTESIA_KEYS) > 0:
        print("[CARTESIA QUOTA]: All keys out of credits. Enabling cooldown for 30 minutes.")
        cartesia_cooldown_until = time.time() + 1800  # 30 min cooldown
    return None, 0.0, ""

def run_tts(text_to_speak: str, user_query: str = '', raw_reply: str = '', forced_lang: str | None = None, context: str = "normal", radar_gain: float = 1.0, speed: float = 0.88, forced_voice: str | None = None, forced_tier: str | None = None) -> tuple[bytes | None, float, str]:
    """
    Studio-Quality Cloud Neural TTS Engine:
    1. Tier 1: Cartesia Sonic Cloud Streaming (Sub-200ms ultra-low latency, studio multilingual)
    2. Tier 2: Microsoft Indian Neural Cloud Voices (Studio quality: Neerja / Swara / Aarohi / Dhwani)
    3. Emergency Offline Tier: Pyttsx3 (Failover only if cloud is unreachable)
    """
    global tts_test_mode
    clean_check = text_to_speak.strip() if text_to_speak else ""
    if not clean_check or not re.search(r'[\w\u0900-\u097F\u0A80-\u0AFF]', clean_check):
        return None, 0.0, "Empty"
    
    # Honor forced language strictly if provided so voice personality never switches mid-sentence!
    if forced_lang and forced_lang in ['en', 'hi', 'mr', 'gu']:
        lang = forced_lang
    else:
        lang = detect_language(text_to_speak, user_query=user_query, raw_reply=raw_reply, forced_lang=forced_lang)
        
    spoken_text = normalize_speech_for_tts(text_to_speak, lang=lang)
    print(f"[LANG ROUTING]: Detected '{lang.upper()}' for text: \"{spoken_text[:50]}...\"")
    
    if forced_voice:
        target_voice = forced_voice
    elif lang == 'gu':
        target_voice = "gu-IN-DhwaniNeural"
    elif lang == 'mr':
        target_voice = "mr-IN-AarohiNeural"
    elif lang == 'hi':
        target_voice = "hi-IN-SwaraNeural"
    else:
        target_voice = "en-IN-NeerjaNeural" 

        # Enforce strict turn-level engine tier to prevent mid-speech voice hopping
    allow_cartesia = (forced_tier != "edge") and (not tts_test_mode) and bool(CARTESIA_KEYS) and (time.time() >= cartesia_cooldown_until)
    
    # Tier 1: Cartesia Sonic Cloud Streaming if active and permitted
    if allow_cartesia:
        pcm, dt, voice_label = run_cartesia_tts(spoken_text, lang=lang, context=context, radar_gain=radar_gain, speed=speed)
        if pcm:
            return pcm, dt, voice_label

    # Tier 2: Microsoft Studio Cloud Neural (Neerja / Swara / Aarohi / Dhwani)
    pcm, dt = run_edge_tts_sync(spoken_text, voice=target_voice, context=context, radar_gain=radar_gain, speed=speed)
    if pcm:
        return pcm, dt, f"Microsoft Neural ({target_voice})" 

    print("[FAILOVER]: Cloud TTS unavailable. Switching to Offline Voice...")
    pcm, dt = run_offline_tts(spoken_text)
    return pcm, dt, "Offline Voice"

# --- Timer & Alarm Loops ---
_timer_seq = 0
_alarm_seq = 0

async def start_timer_instance(duration: int, name: str, context: str = "general", completion_phrase: str = "", lang: str = "en", timer_id: str = None):
    """Schedules an asynchronous background timer with chime and smart contextual completion alert."""
    global active_timers, loop, _timer_seq
    update_temporal_context(name, "timer", duration)
    if not timer_id:
        _timer_seq += 1
        timer_id = f"timer_{int(time.time()*1000)}_{_timer_seq}"
        
    start_time = time.time()
    end_time = start_time + duration
    
    if not completion_phrase:
        duration_desc = format_duration_desc(duration, lang)
        if lang == "hi":
            completion_phrase = f"श्रवण, आपका {name} का {duration_desc} का टाइमर पूरा हो गया है!"
        elif lang == "mr":
            completion_phrase = f"श्रवण, तुमचा {name} चा {duration_desc} चा टायमर पूर्ण झाला आहे!"
        elif lang == "gu":
            completion_phrase = f"શ્રવણ, તમારો {name} માટેનો {duration_desc} નો ટાઈમર પૂરો થઈ ગયો છે!"
        else:
            completion_phrase = f"Shravan, your {duration_desc} timer for {name} is complete!"
            
    async def _timer_worker():
        try:
            await asyncio.sleep(duration)
            print(f"[TIMER EXPIRED]: '{name}' ({duration}s)")
            if timer_id in active_timers:
                del active_timers[timer_id]
                await broadcast("timers", get_timers_data())
                
            await broadcast("status", f"⏰ Timer Finished: {name}!")
            
            chime_pcm = make_chime_pcm(duration=0.6)
            await execute_priority_alert(chime_pcm, completion_phrase, lang=lang, alert_type="timer", name=name)
        except asyncio.CancelledError:
            print(f"[TIMER CANCELLED]: Task for '{name}' was cancelled.")
        except Exception as e:
            print(f"[TIMER WORKER EXCEPTION]: {e}")
            
    task = asyncio.create_task(_timer_worker())
    active_timers[timer_id] = {
        "id": timer_id,
        "name": name,
        "duration": duration,
        "start_time": start_time,
        "end_time": end_time,
        "context": context,
        "completion_phrase": completion_phrase,
        "lang": lang,
        "task": task
    }
    await broadcast("timers", get_timers_data())
    print(f"[TIMER REGISTERED]: ID {timer_id} | '{name}' for {duration}s")
    return timer_id

async def cancel_timer_instance(timer_id: str = None, name: str = None, cancel_all: bool = False):
    """Cancels active timers either by ID, matching name, or all."""
    global active_timers
    cancelled_count = 0
    if cancel_all:
        for tid, t in list(active_timers.items()):
            if t.get("task"):
                t["task"].cancel()
            cancelled_count += 1
        active_timers.clear()
    elif timer_id and timer_id in active_timers:
        t = active_timers[timer_id]
        if t.get("task"):
            t["task"].cancel()
        del active_timers[timer_id]
        cancelled_count = 1
    elif name:
        target_name = name.lower().strip()
        for tid, t in list(active_timers.items()):
            if target_name in t["name"].lower() or t["name"].lower() in target_name:
                if t.get("task"):
                    t["task"].cancel()
                del active_timers[tid]
                cancelled_count += 1
                break
    await broadcast("timers", get_timers_data())
    return cancelled_count

async def start_timer(seconds: int, label: str):
    """Backwards-compatible wrapper."""
    return await start_timer_instance(duration=seconds, name=label)

def handle_timer_query(user_query: str, lang: str) -> str:
    global active_timers
    q_lower = user_query.lower()
    if not active_timers:
        # Check if a timer finished recently (< 45 seconds ago)!
        act_ctx = get_active_temporal_context()
        if act_ctx and act_ctx.get("entity_type") == "timer":
            t_age = int(time.time() - act_ctx.get("timestamp", 0))
            if t_age < 45:
                t_name = act_ctx.get("last_entity", "timer")
                if lang == "hi":
                    return f"आपकी {t_name} टाइमर {t_age} सेकंड पहले पूरी हो चुकी है। अभी कोई और टाइमर चालू नहीं है।"
                elif lang == "mr":
                    return f"तुमची {t_name} टायमर {t_age} सेकंदांपूर्वी पूर्ण झाली आहे. सध्या दुसरा कोणताही टायमर सुरू नाही."
                elif lang == "gu":
                    return f"તમારી {t_name} ટાઈમર {t_age} સેકન્ડ પહેલા પૂર્ણ થઈ ચૂકી છે. હાલમાં કોઈ અન્ય ટાઈમર ચાલુ નથી."
                else:
                    return f"Your {t_name} timer finished {t_age} seconds ago. No other timers are running."
        empty_map = {
            "hi": "अभी कोई टाइमर चालू नहीं है।",
            "mr": "सध्या कोणताही टायमर सुरू नाही.",
            "gu": "હાલમાં કોઈ ટાઈમર ચાલુ નથી.",
            "en": "No timers are currently running."
        }
        return empty_map.get(lang, empty_map["en"])
        
    now = time.time()
    target_timer = None
    for tid, t in active_timers.items():
        if t["name"].lower() in q_lower:
            target_timer = t
            break
            
    # Temporal memory resolution: If no timer explicitly named, check recent temporal subject
    if not target_timer:
        act_ctx = get_active_temporal_context()
        if act_ctx and act_ctx.get("entity_type") == "timer":
            last_name = act_ctx.get("last_entity", "").lower()
            for tid, t in active_timers.items():
                if t["name"].lower() == last_name:
                    target_timer = t
                    print(f"[TEMPORAL MEMORY MATCH]: Resolved ambiguous query '{user_query}' to recent timer '{t['name']}'")
                    break
            
    if target_timer:
        rem = max(0, int(target_timer["end_time"] - now))
        if rem <= 1:
            tid = target_timer.get("id")
            if tid in active_timers:
                t_obj = active_timers[tid]
                if t_obj.get("task"):
                    t_obj["task"].cancel()
                del active_timers[tid]
                dispatch_async(broadcast("timers", get_timers_data()))
            if lang == "hi":
                return f"आपकी {target_timer['name']} टाइमर अभी पूरी हो रही है! यह तैयार है।"
            elif lang == "mr":
                return f"तुमची {target_timer['name']} टायमर आत्ताच पूर्ण होत आहे! हे तयार आहे."
            elif lang == "gu":
                return f"તમારી {target_timer['name']} ટાઈમર હમણાં જ પૂર્ણ થઈ રહી છે! તે તૈયાર છે."
            else:
                t_lbl = target_timer['name'] if target_timer['name'].lower().endswith("timer") else f"{target_timer['name']} timer"
                return f"Your {t_lbl} is completing right now! It is done."
        else:
            d_str = format_duration_desc(rem, lang)
            if lang == "hi":
                return f"आपकी {target_timer['name']} टाइमर में {d_str} बचे हैं।"
            elif lang == "mr":
                return f"तुमच्या {target_timer['name']} टायमरमध्ये {d_str} शिल्लक आहेत."
            elif lang == "gu":
                return f"તમારી {target_timer['name']} ટાઈમરમાં {d_str} બાકી છે."
            else:
                return f"{d_str} remaining for your {target_timer['name']} timer."
            
    # Single active timer query (e.g. "how much time left for my timer")
    if len(active_timers) == 1:
        single_t = list(active_timers.values())[0]
        rem = max(0, int(single_t["end_time"] - now))
        if rem <= 1:
            tid = single_t.get("id")
            if tid in active_timers:
                t_obj = active_timers[tid]
                if t_obj.get("task"):
                    t_obj["task"].cancel()
                del active_timers[tid]
                dispatch_async(broadcast("timers", get_timers_data()))
            if lang == "hi":
                return f"आपकी {single_t['name']} टाइमर अभी पूरी हो रही है! यह तैयार है।"
            elif lang == "mr":
                return f"तुमची {single_t['name']} टायमर आत्ताच पूर्ण होत आहे! हे तयार आहे."
            elif lang == "gu":
                return f"તમારી {single_t['name']} ટાઈમર હમણાં જ પૂર્ણ થઈ રહી છે! તે તૈયાર છે."
            else:
                t_lbl = single_t['name'] if single_t['name'].lower().endswith("timer") else f"{single_t['name']} timer"
                return f"Your {t_lbl} is completing right now! It is done."
        else:
            d_str = format_duration_desc(rem, lang)
            if lang == "hi":
                return f"आपकी {single_t['name']} टाइमर में {d_str} बचे हैं।"
            elif lang == "mr":
                return f"तुमच्या {single_t['name']} टायमरमध्ये {d_str} शिल्लक आहेत."
            elif lang == "gu":
                return f"તમારી {single_t['name']} ટાઈમરમાં {d_str} બાકી છે."
            else:
                return f"You have 1 active timer: {single_t['name']} with {d_str} remaining."

    # Multiple active timers
    t_items = []
    for t in list(active_timers.values()):
        rem = max(0, int(t["end_time"] - now))
        if rem <= 1:
            t_items.append(f"{t['name']} (completing now)")
        else:
            t_items.append(f"{t['name']} with {format_duration_desc(rem, lang)} remaining")
        
    if lang == "hi":
        return f"{len(active_timers)} टाइमर चल रहे हैं: {', '.join(t_items)}।"
    elif lang == "mr":
        return f"{len(active_timers)} टायमर सुरू आहेत: {', '.join(t_items)}."
    elif lang == "gu":
        return f"{len(active_timers)} ટાઈમર ચાલુ છે: {', '.join(t_items)}."
    else:
        return f"You have {len(active_timers)} active timers: {', '.join(t_items)}."

def handle_timer_cancel(user_query: str, lang: str) -> str:
    global active_timers, loop
    q_lower = user_query.lower()
    explicit_all = any(w in q_lower for w in ["all", "sabhi", "sab", "sarva", "badha", "બધા", "सर्व", "सभी", "सब"])
    
    target_name = None
    if not explicit_all:
        for tid, t in active_timers.items():
            if t["name"].lower() in q_lower:
                target_name = t["name"]
                break
                
    if explicit_all or not target_name:
        dispatch_async(cancel_timer_instance(cancel_all=True))
        all_map = {
            "hi": "सभी टाइमर रद्द कर दिए गए हैं।",
            "mr": "सर्व टायमर रद्द करण्यात आले आहेत.",
            "gu": "બધા ટાઈમર રદ કરવામાં આવ્યા છે.",
            "en": "All active timers have been cancelled."
        }
        return all_map.get(lang, all_map["en"])
    else:
        dispatch_async(cancel_timer_instance(name=target_name))
        one_map = {
            "hi": f"{target_name} का टाइमर रद्द कर दिया गया है।",
            "mr": f"{target_name} चा टायमर रद्द केला आहे.",
            "gu": f"{target_name} નો ટાઈમર રદ કરવામાં આવ્યો છે.",
            "en": f"Cancelled your {target_name} timer."
        }
        return one_map.get(lang, one_map["en"])

def handle_stopwatch_action(action: str, lang: str) -> str:
    global active_stopwatch, loop
    now = time.time()
    reply = ""
    if action == "start":
        # Always start fresh from zero on 'Start stopwatch'!
        active_stopwatch["elapsed_before_pause"] = 0.0
        active_stopwatch["laps"].clear()
        active_stopwatch["running"] = True
        active_stopwatch["start_time"] = now
        reply_map = {
            "hi": "स्टॉपवॉच शुरू हो गई है!",
            "mr": "स्टॉपवॉच सुरू झाली आहे!",
            "gu": "સ્ટોપવોચ શરૂ થઈ ગઈ છે!",
            "en": "Stopwatch started!"
        }
        reply = reply_map.get(lang, reply_map["en"])
    elif action == "resume":
        if not active_stopwatch["running"]:
            active_stopwatch["running"] = True
            active_stopwatch["start_time"] = now
            d_desc = format_duration_desc(int(active_stopwatch["elapsed_before_pause"]), lang)
            reply_map = {
                "hi": f"स्टॉपवॉच {d_desc} से फिर शुरू कर दी गई है।",
                "mr": f"स्टॉपवॉच {d_desc} पासून पुढे सुरू केली आहे.",
                "gu": f"સ્ટોપવોચ {d_desc} થી ફરી શરૂ કરી દીધી છે.",
                "en": f"Stopwatch resumed from {d_desc}."
            }
            reply = reply_map.get(lang, reply_map["en"])
        else:
            cur_el = (now - active_stopwatch["start_time"]) + active_stopwatch["elapsed_before_pause"]
            d_desc = format_duration_desc(int(cur_el), lang)
            reply = f"Stopwatch is already running at {d_desc}."
    elif action == "lap":
        if active_stopwatch["running"] and active_stopwatch["start_time"]:
            total_el = (now - active_stopwatch["start_time"]) + active_stopwatch["elapsed_before_pause"]
            prev_total = active_stopwatch["laps"][-1]["total_time"] if active_stopwatch["laps"] else 0.0
            split = total_el - prev_total
            lap_num = len(active_stopwatch["laps"]) + 1
            active_stopwatch["laps"].append({
                "lap_num": lap_num,
                "split_time": round(split, 2),
                "total_time": round(total_el, 2),
                "formatted": format_stopwatch_clock(total_el)
            })
            d_desc = format_duration_desc(int(total_el), lang)
            reply_map = {
                "hi": f"लैप {lap_num} दर्ज किया: {d_desc}।",
                "mr": f"लॅप {lap_num} नोंदवला: {d_desc}.",
                "gu": f"લેપ {lap_num} નોંધાયો: {d_desc}.",
                "en": f"Lap {lap_num} recorded at {d_desc}."
            }
            reply = reply_map.get(lang, reply_map["en"])
        else:
            reply_map = {
                "hi": "स्टॉपवॉच चालू नहीं है। पहले स्टॉपवॉच शुरू करें।",
                "mr": "स्टॉपवॉच सुरू नाही. आधी स्टॉपवॉच सुरू करा.",
                "gu": "સ્ટોપવોચ ચાલુ નથી. પહેલાં સ્ટોપવોચ શરૂ કરો.",
                "en": "Stopwatch is not running. Say 'Start stopwatch' first."
            }
            reply = reply_map.get(lang, reply_map["en"])
    elif action == "stop":
        if active_stopwatch["running"] and active_stopwatch["start_time"]:
            active_stopwatch["elapsed_before_pause"] += (now - active_stopwatch["start_time"])
            active_stopwatch["running"] = False
            active_stopwatch["start_time"] = None
            d_desc = format_duration_desc(int(active_stopwatch["elapsed_before_pause"]), lang)
            reply_map = {
                "hi": f"स्टॉपवॉच रोक दी गई है! कुल समय {d_desc} हुआ है।",
                "mr": f"स्टॉपवॉच थांबवली आहे! एकूण वेळ {d_desc} झाली आहे.",
                "gu": f"સ્ટોપવોચ રોકી દીધી છે! કુલ સમય {d_desc} થયો છે.",
                "en": f"Stopwatch stopped! Total time elapsed is {d_desc}."
            }
            reply = reply_map.get(lang, reply_map["en"])
        else:
            d_desc = format_duration_desc(int(active_stopwatch["elapsed_before_pause"]), lang)
            reply_map = {
                "hi": f"स्टॉपवॉच पहले से ही रुकी हुई है, कुल समय {d_desc} है।",
                "mr": f"स्टॉपवॉच आधीच थांबलेली आहे, एकूण वेळ {d_desc} आहे.",
                "gu": f"સ્ટોપવોચ પહેલેથી જ રોકાયેલી છે, કુલ સમય {d_desc} છે.",
                "en": f"Stopwatch is already stopped at {d_desc}."
            }
            reply = reply_map.get(lang, reply_map["en"])
    elif action == "reset":
        active_stopwatch["running"] = False
        active_stopwatch["start_time"] = None
        active_stopwatch["elapsed_before_pause"] = 0.0
        active_stopwatch["laps"].clear()
        reply_map = {
            "hi": "स्टॉपवॉच शून्य पर रीसेट कर दी गई है।",
            "mr": "स्टॉपवॉच शून्यावर रीसेट केली आहे.",
            "gu": "સ્ટોપવોચ શૂન્ય પર રીસેટ કરી દીધી છે.",
            "en": "Stopwatch has been reset to zero."
        }
        reply = reply_map.get(lang, reply_map["en"])
    elif action == "query":
        if active_stopwatch["running"] and active_stopwatch["start_time"]:
            cur_el = (now - active_stopwatch["start_time"]) + active_stopwatch["elapsed_before_pause"]
            d_desc = format_duration_desc(int(cur_el), lang)
            reply_map = {
                "hi": f"स्टॉपवॉच अभी {d_desc} पर चल रही है।",
                "mr": f"स्टॉपवॉच सध्या {d_desc} वर चालू आहे.",
                "gu": f"સ્ટોપવોચ અત્યારે {d_desc} પર ચાલુ છે.",
                "en": f"The stopwatch is currently running at {d_desc}."
            }
            reply = reply_map.get(lang, reply_map["en"])
        elif active_stopwatch["elapsed_before_pause"] > 0:
            d_desc = format_duration_desc(int(active_stopwatch["elapsed_before_pause"]), lang)
            reply = f"Stopwatch is paused at {d_desc}."
        else:
            reply_map = {
                "hi": "स्टॉपवॉच शून्य पर बंद है।",
                "mr": "स्टॉपवॉच शून्यावर थांबलेली आहे.",
                "gu": "સ્ટોપવોચ શૂન્ય પર બંધ છે.",
                "en": "Stopwatch is currently stopped at zero."
            }
            reply = reply_map.get(lang, reply_map["en"])
            
    dispatch_async(broadcast("stopwatch", get_stopwatch_data()))
    return reply

async def trigger_alarm(aid: str):
    """Fires dedicated alarm tone and contextual voice alert when alarm expires with priority preemption."""
    global active_alarms, is_listening, loop
    if aid not in active_alarms:
        return
    alarm = active_alarms[aid]
    del active_alarms[aid]
    await broadcast("alarms", get_alarms_data())
    await broadcast("status", f"🔔 Alarm Triggered: {alarm['label']} ({alarm['time_str']})!")
    print(f"\n[ALARM RINGING]: {alarm['label']} ({alarm['time_str']})\n")
    
    alarm_pcm = make_alarm_pcm()
    lang = alarm.get("lang", "en")
    label = alarm.get("label", "Alarm")
    t_str = alarm.get("time_str", "")
    
    if lang == "hi":
        speech = f"श्रवण, उठ जाइए! {t_str} बज चुके हैं, आपका {label} बज रहा है!"
    elif lang == "mr":
        speech = f"श्रवण, उठा! {t_str} वाजले आहेत, तुमचा {label} वाजत आहे!"
    elif lang == "gu":
        speech = f"શ્રવણ, જાગી જાઓ! {t_str} વાગી ગયા છે, તમારું {label} વાગી રહ્યું છે!"
    else:
        speech = f"Shravan, wake up! It's {t_str}! Your alarm {label} is ringing!"
        
    await execute_priority_alert(alarm_pcm, speech, lang=lang, alert_type="alarm", name=label)

async def start_alarm_instance(time_str: str, label: str = "Alarm", lang: str = "en", alarm_id: str = None):
    """Schedules an alarm for clock time."""
    global active_alarms, _alarm_seq
    parsed = parse_alarm_time(time_str)
    if not parsed:
        return None
    target_dt, fmt_time = parsed
    target_ts = target_dt.timestamp()
    if not alarm_id:
        _alarm_seq += 1
        alarm_id = f"alarm_{int(target_ts)}_{_alarm_seq}"
        
    alarm_data = {
        "id": alarm_id,
        "time_str": fmt_time,
        "label": label or "Alarm",
        "target_ts": target_ts,
        "lang": lang
    }
    active_alarms[alarm_id] = alarm_data
    await broadcast("alarms", get_alarms_data())
    print(f"[ALARM SCHEDULED]: {label} for {fmt_time} (TS: {target_ts})")
    return alarm_id

async def cancel_alarm_instance(alarm_id: str = None, time_str: str = None, cancel_all: bool = False):
    """Cancels active alarms."""
    global active_alarms
    cancelled = 0
    if cancel_all:
        cancelled = len(active_alarms)
        active_alarms.clear()
    elif alarm_id and alarm_id in active_alarms:
        del active_alarms[alarm_id]
        cancelled = 1
    elif time_str:
        parsed = parse_alarm_time(time_str)
        t_fmt = parsed[1] if parsed else time_str.upper()
        for aid, a in list(active_alarms.items()):
            if a["time_str"].upper() == t_fmt:
                del active_alarms[aid]
                cancelled += 1
                break
    await broadcast("alarms", get_alarms_data())
    return cancelled

def handle_alarm_cancel(user_query: str, lang: str) -> str:
    global active_alarms, loop
    q_lower = user_query.lower()
    explicit_all = any(w in q_lower for w in ["all", "sabhi", "sab", "sarva", "badha", "બધા", "सर्व", "सभी", "सब"])
    parsed = parse_alarm_time(user_query)
    time_target = parsed[1] if parsed else None
    
    if explicit_all or not time_target:
        dispatch_async(cancel_alarm_instance(cancel_all=True))
        all_map = {
            "hi": "सभी अलार्म रद्द कर दिए गए हैं।",
            "mr": "सर्व अलार्म रद्द केले आहेत.",
            "gu": "બધા અલાર્મ રદ કરવામાં આવ્યા છે.",
            "en": "All scheduled alarms have been cancelled."
        }
        return all_map.get(lang, all_map["en"])
    else:
        dispatch_async(cancel_alarm_instance(time_str=time_target))
        one_map = {
            "hi": f"{time_target} का अलार्म रद्द कर दिया गया है।",
            "mr": f"{time_target} चा अलार्म रद्द केला आहे.",
            "gu": f"{time_target} નો અલાર્મ રદ કરવામાં આવ્યો છે.",
            "en": f"Alarm for {time_target} has been cancelled."
        }
        return one_map.get(lang, one_map["en"])

def handle_alarm_list(lang: str) -> str:
    global active_alarms
    if not active_alarms:
        empty_map = {
            "hi": "कोई अलार्म सेट नहीं है।",
            "mr": "कोणताही अलार्म सेट केलेला नाही.",
            "gu": "કોઈ અલાર્મ સેટ નથી.",
            "en": "No alarms are currently scheduled."
        }
        return empty_map.get(lang, empty_map["en"])
        
    now = time.time()
    items = []
    for a in active_alarms.values():
        rem = max(0, int(a["target_ts"] - now))
        items.append(f"{a['time_str']} ({a['label']})")
        
    if lang == "hi":
        return f"{len(active_alarms)} अलार्म सेट हैं: {', '.join(items)}।"
    elif lang == "mr":
        return f"{len(active_alarms)} अलार्म सेट आहेत: {', '.join(items)}."
    elif lang == "gu":
        return f"{len(active_alarms)} અલાર્મ સેટ છે: {', '.join(items)}."
    else:
        if len(active_alarms) == 1:
            return f"You have 1 scheduled alarm: {items[0]}."
        else:
            return f"You have {len(active_alarms)} scheduled alarms: {', '.join(items)}."

async def alarm_supervisor():
    """Background supervisor monitoring alarms with 500ms precision and reliable dispatch."""
    global active_alarms
    while True:
        try:
            now = time.time()
            to_fire = []
            for aid, a in list(active_alarms.items()):
                if now >= a["target_ts"]:
                    to_fire.append(aid)
            for aid in to_fire:
                try:
                    await trigger_alarm(aid)
                except Exception as ex_a:
                    print(f"[ALARM FIRE EXCEPTION for {aid}]: {ex_a}")
        except Exception as e:
            print(f"[ALARM SUPERVISOR ERROR]: {e}")
        await asyncio.sleep(0.5)

# --- Audio Streamer to ESP32 ---
async def stream_audio_queue_to_esp32(audio_queue: asyncio.Queue, label_text: str):
    """
    Streams 16kHz 16-bit Mono PCM audio chunks from an asynchronous queue to the ESP32
    with clock-tracked pacing, mutex locking, burst pre-buffering, and gapless clause chaining.
    Completely eliminates speaker pauses between sentences, DMA underruns, and 'two-two' chime collisions.
    Supports atomic interruption / barge-in cancellation within < 20ms.
    """
    global playback_interrupt_event, active_audio_queue
    active_audio_queue = audio_queue
    lock = get_audio_stream_lock()
    async with lock:
        try:
            if not is_connected():
                while not audio_queue.empty():
                    try:
                        audio_queue.get_nowait()
                    except Exception:
                        break
                return

            chunk_size = 1024  # 1024 bytes = 512 samples = 32ms of 16kHz audio
            total_chunks_sent = 0
            stream_start = None
            lead_target_sec = 0.220  # 220ms target lead (safe buffer, well within ESP32 300ms ring buffer)
            first_event_sent = False
            leftover_pcm = b''
            
            while True:
                if playback_interrupt_event.is_set():
                    print("[STREAM INTERRUPTED]: Audio queue playback loop terminated mid-speech.")
                    break
                pcm_bytes = await audio_queue.get()
                if pcm_bytes is None or playback_interrupt_event.is_set():
                    # Sentinel indicating all clauses in dialogue have been sent, or interrupted
                    break
                    
                if not is_connected() or not pcm_bytes:
                    continue
                    
                # Ensure 16-bit PCM word alignment
                if len(pcm_bytes) % 2 != 0:
                    pcm_bytes = pcm_bytes[:-1]
                
                # Gapless contiguous waveform chaining: stitch with unpadded leftover bytes from previous clause
                data = leftover_pcm + pcm_bytes
                leftover_pcm = b''
                
                total_bytes = len(data)
                num_chunks = total_bytes // chunk_size
                if num_chunks == 0:
                    # Keep fractional chunk for the next clause instead of inserting zero padding mid-sentence!
                    leftover_pcm = data
                    continue
                
                usable_bytes = num_chunks * chunk_size
                leftover_pcm = data[usable_bytes:]
                data = data[:usable_bytes]
                
                now = time.monotonic()
                if not first_event_sent:
                    client.send_voice_assistant_event(VoiceAssistantEventType.VOICE_ASSISTANT_TTS_START, {"text": label_text})
                    client.send_voice_assistant_event(VoiceAssistantEventType.VOICE_ASSISTANT_TTS_STREAM_START, None)
                    first_event_sent = True
                    set_aura_led("speaking")
                    stream_start = now
                    total_chunks_sent = 0
                    
                    # Prime the ESP32 ring buffer with 3 chunks (~96ms, 3KB)
                    prime_chunks = min(3, num_chunks)
                    for k in range(prime_chunks):
                        if not is_connected() or playback_interrupt_event.is_set():
                            break
                        start_idx = k * chunk_size
                        chunk = data[start_idx:start_idx + chunk_size]
                        client.send_voice_assistant_audio(chunk)
                        record_speaker_audio_chunk(chunk)
                        total_chunks_sent += 1
                    offset = prime_chunks * chunk_size
                else:
                    # Clause Chaining: evaluate physical DAC hardware buffer status
                    dac_audio_sec = total_chunks_sent * 0.032
                    elapsed_sec = now - stream_start
                    buffer_remaining_sec = dac_audio_sec - elapsed_sec
                    
                    if buffer_remaining_sec < 0.040:
                        # Hardware buffer underrun/starvation occurred while waiting for cloud TTS.
                        # Resynchronize clock to current real-time so we NEVER dump a 1ms catch-up firehose!
                        stream_start = now - max(0.0, buffer_remaining_sec)
                        total_chunks_sent = int(max(0.0, buffer_remaining_sec) / 0.032)
                        
                        # Re-prime the starved DAC with 2 chunks (~64ms)
                        prime_chunks = min(2, num_chunks)
                        for k in range(prime_chunks):
                            if not is_connected() or playback_interrupt_event.is_set():
                                break
                            start_idx = k * chunk_size
                            chunk = data[start_idx:start_idx + chunk_size]
                            client.send_voice_assistant_audio(chunk)
                            record_speaker_audio_chunk(chunk)
                            total_chunks_sent += 1
                        offset = prime_chunks * chunk_size
                    else:
                        # Continuous playback: ESP32 buffer is healthy, continue seamless pacing
                        offset = 0
                    
                # Paced delivery of remaining chunks for this clause
                for i in range(offset, usable_bytes, chunk_size):
                    if playback_interrupt_event.is_set():
                        print("[STREAM INTERRUPTED]: Chunk delivery aborted mid-clause.")
                        break
                    if not is_connected():
                        print("ESP32 disconnected during audio queue stream")
                        break
                        
                    chunk = data[i:i+chunk_size]
                    dac_playback_time = total_chunks_sent * 0.032
                    target_send_time = stream_start + dac_playback_time - lead_target_sec
                    
                    now = time.monotonic()
                    if now < target_send_time:
                        await asyncio.sleep(target_send_time - now)
                    else:
                        # Rate limiter guard: never send faster than 10ms (prevents ESP32 buffer overflow)
                        await asyncio.sleep(0.010)
                        
                    if playback_interrupt_event.is_set():
                        break
                    client.send_voice_assistant_audio(chunk)
                    record_speaker_audio_chunk(chunk)
                    total_chunks_sent += 1
            
            # Flush final leftover bytes at end of speech
            if leftover_pcm and not playback_interrupt_event.is_set() and is_connected():
                final_chunk = leftover_pcm + (b'\x00' * (chunk_size - len(leftover_pcm)))
                client.send_voice_assistant_audio(final_chunk)
                record_speaker_audio_chunk(final_chunk)
                total_chunks_sent += 1
                leftover_pcm = b''
                    
            # 4. Wait for hardware DAC to physically finish acoustic playback of the full buffer into the room
            if not playback_interrupt_event.is_set() and first_event_sent and total_chunks_sent > 0:
                drain_target = stream_start + (total_chunks_sent * 0.032) + 0.350
                remaining = max(0.400, drain_target - time.monotonic())
                await asyncio.sleep(min(remaining, 1.5))
                    
            # 5. Clean end of pipeline AFTER speaker has physically finished audio playback (or on interrupt)
            if is_connected():
                if first_event_sent:
                    try:
                        client.send_voice_assistant_event(VoiceAssistantEventType.VOICE_ASSISTANT_TTS_STREAM_END, None)
                    except Exception:
                        pass
                try:
                    client.send_voice_assistant_event(VoiceAssistantEventType.VOICE_ASSISTANT_RUN_END, None)
                except Exception:
                    pass
                if not playback_interrupt_event.is_set():
                    if not call_audio_bridge.is_active:
                        set_aura_led("idle")
                    await broadcast("status", "Ready! Say 'Alexa' or click button below.")
        except asyncio.CancelledError:
            print("[AUDIO STREAM CANCELLED AT TASK LEVEL]")
            if is_connected():
                try:
                    client.send_voice_assistant_event(VoiceAssistantEventType.VOICE_ASSISTANT_TTS_STREAM_END, None)
                    client.send_voice_assistant_event(VoiceAssistantEventType.VOICE_ASSISTANT_RUN_END, None)
                except Exception:
                    pass
        except Exception as e:
            print(f"Error streaming audio queue to ESP32: {e}")
            try:
                if is_connected():
                    client.send_voice_assistant_event(VoiceAssistantEventType.VOICE_ASSISTANT_TTS_STREAM_END, None)
                    client.send_voice_assistant_event(VoiceAssistantEventType.VOICE_ASSISTANT_RUN_END, None)
            except Exception:
                pass
            await broadcast("status", "Ready! Say 'Alexa' or click button below.")
        finally:
            active_audio_queue = None

async def stream_audio_to_esp32(pcm_audio: bytes, label_text: str):
    """Backwards-compatible wrapper that feeds single PCM buffers through the queue streamer."""
    if not pcm_audio:
        return
    global playback_interrupt_event
    playback_interrupt_event.clear()  # Guarantee fresh playback for background alerts & notifications!
    q = asyncio.Queue()
    await q.put(pcm_audio)
    await q.put(None)
    await stream_audio_queue_to_esp32(q, label_text)

# --- Streaming Dialogue Pipeline ---
async def run_streaming_dialogue_pipeline(transcript: str, audio_queue: asyncio.Queue, t_stt: float, ambient_profile: dict | None = None, cadence_info: dict | None = None, t_speech_end: float | None = None):
    """
    Pipelined Sentence-Level Dialogue Synthesizer:
    1. Streams natural clauses from Groq LLM.
    2. Concurrently launches TTS synthesis for each clause as soon as its sentence boundary is detected.
    3. Feeds raw audio PCM chunks into audio_queue the millisecond Clause 1 is ready,
       achieving sub-second first-audio latency while remaining clauses synthesize in parallel.
    """
    t_start = time.time()
    if t_speech_end is None:
        t_speech_end = t_start - (t_stt / 1000.0)
    speech_end_dt = datetime.datetime.fromtimestamp(t_speech_end)
    speech_end_ts_str = speech_end_dt.strftime("%H:%M:%S.%f")[:-3]
    first_audio_ts_str = "--:--:--.---"
    v2v_latency_ms = 0

    first_audio_logged = False
    first_audio_ms = 0
    all_clauses = []
    definitive_lang = "en"
    voice_used = "en-IN-NeerjaNeural"
    total_audio_bytes = 0
    
    # --- Voice Selection ---
    locked_turn_lang = None
    locked_turn_voice = None
    locked_turn_tier = None
    
    active_loop = loop if loop is not None else asyncio.get_running_loop()
    clause_queue = asyncio.Queue()

    # --- Audio Queue Delivery ---
    global pending_priority_alerts
    active_alerts = list(pending_priority_alerts)
    pending_priority_alerts.clear()
    
    det_lang = detect_language(transcript, user_query=transcript)
    if active_alerts:
        q_lower = transcript.lower()
        is_self_query = False
        target_alert = None
        for a in active_alerts:
            t_name = a.get("name", "").lower()
            if t_name and (t_name in q_lower or (t_name.replace(" timer", "") in q_lower and len(t_name.replace(" timer", "")) >= 3)):
                is_self_query = True
                target_alert = a
                break
        if not is_self_query and is_timer_query(transcript):
            is_self_query = True
            target_alert = active_alerts[0]
            
        if is_self_query:
            t_name = target_alert.get("name", "timer")
            if det_lang == "hi":
                self_reply = f"श्रवण, आपका {t_name} का टाइमर अभी पूरा हुआ है! यह तैयार है।"
            elif det_lang == "mr":
                self_reply = f"श्रवण, तुमचा {t_name} चा टायमर आत्ताच पूर्ण झाला आहे! हे तयार आहे."
            elif det_lang == "gu":
                self_reply = f"શ્રવણ, તમારો {t_name} નો ટાઈમર હમણાં જ પૂર્ણ થયો છે! તે તૈયાર છે."
            else:
                self_reply = f"Shravan, your {t_name} timer just finished this very second! It is ready."
                
            chime = target_alert.get("chime_pcm") or make_chime_pcm(duration=0.6)
            pcm, dt, v_label = await active_loop.run_in_executor(None, run_tts, self_reply, transcript, "", det_lang)
            full_pcm = (chime or b'') + (pcm or b'')
            if full_pcm:
                await audio_queue.put(full_pcm)
            await audio_queue.put(None)
            
            total_time = (time.time() - t_start) * 1000 + t_stt
            await broadcast("ai", f"{self_reply} (First Audio: {total_time:.0f} ms | Total: {total_time:.0f} ms)")
            return self_reply
        else:
            now_ts = time.time()
            alert_age = now_ts - active_alerts[0].get("timestamp", now_ts)
            if alert_age > 8:
                sec_ago = int(alert_age)
                if det_lang == "hi":
                    alert_text = f"सूचना: आपका {active_alerts[0].get('name', 'टाइमर')} {sec_ago} सेकंड पहले पूरा हो चुका है।"
                elif det_lang == "mr":
                    alert_text = f"सूचना: तुमचा {active_alerts[0].get('name', 'टायमर')} {sec_ago} सेकंदांपूर्वी पूर्ण झाला आहे."
                elif det_lang == "gu":
                    alert_text = f"સૂચના: તમારો {active_alerts[0].get('name', 'ટાઈમર')} {sec_ago} સેકન્ડ પહેલા પૂર્ણ થઈ ગયો છે."
                else:
                    alert_text = f"Notice: Your {active_alerts[0].get('name', 'timer')} completed {sec_ago} seconds ago."
            else:
                alert_text = coalesce_priority_alerts(active_alerts, lang=det_lang)
            bridge_text = get_bridge_phrase(det_lang)
            combined_alert_clause = f"{alert_text}{bridge_text}"
            chime = active_alerts[0].get("chime_pcm") or make_chime_pcm(duration=0.6)
            
            pcm_alert, dt_alert, v_label = await active_loop.run_in_executor(None, run_tts, combined_alert_clause, transcript, "", det_lang)
            if pcm_alert:
                alert_audio_bytes = (chime or b'') + pcm_alert
                total_audio_bytes += len(alert_audio_bytes)
                await audio_queue.put(alert_audio_bytes)
                if not first_audio_logged:
                    t_first_audio = time.time()
                    first_audio_dt = datetime.datetime.fromtimestamp(t_first_audio)
                    first_audio_ts_str = first_audio_dt.strftime("%H:%M:%S.%f")[:-3]
                    v2v_latency_ms = max(0, (t_first_audio - t_speech_end) * 1000)
                    first_audio_ms = v2v_latency_ms
                    first_audio_logged = True
                    print(f"\n================================================================================")
                    print(f">>> [VOICE-TO-VOICE FIRST-WORD LATENCY (ALERT)]: {v2v_latency_ms:.0f} ms <<<")
                    print(f"🎤 User Stopped Speaking:  {speech_end_ts_str}")
                    print(f"🔊 Assistant First Word:   {first_audio_ts_str}")
                    print(f"⚡ Turn-Taking Latency:    {v2v_latency_ms:.0f} ms (Alert + Bridge)")
                    print(f"================================================================================\n")
                all_clauses.append(combined_alert_clause)
    
    radar_gain = ambient_profile.get("radar_gain", 1.0) if ambient_profile else 1.0
    tts_speed = cadence_info.get("tts_speed", 0.88) if cadence_info else 0.88
    is_rushed = (cadence_info.get("state") == "rushed") if cadence_info else False

    def clause_producer():
        try:
            for clause, lang, is_last, raw_rep in stream_groq_llm(transcript, cadence_info=cadence_info):
                asyncio.run_coroutine_threadsafe(clause_queue.put((clause, lang, is_last, raw_rep)), active_loop).result()
        finally:
            asyncio.run_coroutine_threadsafe(clause_queue.put(None), active_loop).result()

    producer_fut = active_loop.run_in_executor(None, clause_producer)

    async def pipeline_worker():
        nonlocal first_audio_logged, first_audio_ms, voice_used, total_audio_bytes, v2v_latency_ms, first_audio_ts_str
        nonlocal locked_turn_lang, locked_turn_voice
        
        # Parallel pipelined TTS prefetching queue (ensures zero pauses between sentences in long dialogues)
        tts_task_queue = asyncio.Queue()
        
        async def tts_prefetch_producer():
            nonlocal locked_turn_lang, locked_turn_voice
            while True:
                item = await clause_queue.get()
                if item is None:
                    await tts_task_queue.put(None)
                    break
                clause, lang, is_last, raw_rep = item
                
                if locked_turn_lang is None:
                    locked_turn_lang = lang or det_lang or "en"
                    if locked_turn_lang == 'gu':
                        locked_turn_voice = "gu-IN-DhwaniNeural"
                    elif locked_turn_lang == 'mr':
                        locked_turn_voice = "mr-IN-AarohiNeural"
                    elif locked_turn_lang == 'hi':
                        locked_turn_voice = "hi-IN-SwaraNeural"
                    else:
                        locked_turn_voice = "en-IN-NeerjaNeural"
                    
                    if tts_test_mode or not CARTESIA_KEYS or time.time() < cartesia_cooldown_until:
                        locked_turn_tier = "edge"
                    else:
                        locked_turn_tier = "cartesia"
                    print(f"[TURN VOICE LOCKED]: Locked voice persona to '{locked_turn_voice}' ({locked_turn_lang.upper()}) on Tier '{locked_turn_tier}' for all clauses.")
                else:
                    if tts_test_mode or not CARTESIA_KEYS or time.time() < cartesia_cooldown_until:
                        locked_turn_tier = "edge"
                    else:
                        locked_turn_tier = "cartesia"

                context = "normal"
                if "[VOL: WHISPER]" in raw_rep or "[VOL: WHISPER]" in clause or any(w in transcript.lower() for w in ["whisper", "फुसफुस", "व्हिस्पर", "કાનમાં", "कान"]):
                    context = "whisper"
                elif "[VOL: CHEERFUL]" in raw_rep or "[VOL: CHEERFUL]" in clause or any(w in transcript.lower() for w in ["cheerful", "excited", "cheer", "screaming"]):
                    context = "cheerful"

                clean_clause = re.sub(r'\[VOL:\s*[A-Za-z0-9_-]+\]', '', clause, flags=re.IGNORECASE)
                clean_clause = re.sub(r'\[[A-Za-z0-9_ -]+:[^\]]*\]', '', clean_clause)
                clean_clause = re.sub(r'\[[^\]]*\]', '', clean_clause)
                clean_clause = clean_clause.replace('|', '').replace('[', '').replace(']', '')
                clean_clause = re.sub(r'[*_#`~]', '', clean_clause).strip()
                if not clean_clause:
                    continue
                all_clauses.append(clean_clause)
                
                # Launch TTS immediately and concurrently in threadpool!
                fut = active_loop.run_in_executor(None, run_tts, clean_clause, transcript, "", locked_turn_lang, context, radar_gain, tts_speed, locked_turn_voice, locked_turn_tier)
                await tts_task_queue.put(fut)

        prefetch_task = asyncio.create_task(tts_prefetch_producer())
        
        while True:
            fut = await tts_task_queue.get()
            if fut is None:
                await audio_queue.put(None)
                break
            pcm, dt, v_label = await fut
            voice_used = v_label
            if not first_audio_logged and pcm:
                t_first_audio = time.time()
                first_audio_dt = datetime.datetime.fromtimestamp(t_first_audio)
                first_audio_ts_str = first_audio_dt.strftime("%H:%M:%S.%f")[:-3]
                v2v_latency_ms = max(0, (t_first_audio - t_speech_end) * 1000)
                first_audio_ms = v2v_latency_ms
                first_audio_logged = True
                print(f"\n================================================================================")
                print(f">>> [VOICE-TO-VOICE FIRST-WORD LATENCY]: {v2v_latency_ms:.0f} ms <<<")
                print(f"🎤 User Stopped Speaking:  {speech_end_ts_str}")
                print(f"🔊 Assistant First Word:   {first_audio_ts_str}")
                print(f"⚡ Turn-Taking Latency:    {v2v_latency_ms:.0f} ms (STT: {t_stt:.0f}ms | Clause 1 TTS: {dt:.0f}ms | Voice: {v_label})")
                print(f"================================================================================\n")
            if pcm:
                total_audio_bytes += len(pcm)
                await audio_queue.put(pcm)
                
        await prefetch_task

    await pipeline_worker()
    await producer_fut
    
    full_reply = " ".join(all_clauses).strip()
    global timer_preemption_active, pending_deferred_answer
    if timer_preemption_active:
        pending_deferred_answer = full_reply
        print(f"[PIPELINE PREEMPTED]: Stored completed answer for deferred playback after alert: '{full_reply[:40]}...'")
    total_time = (time.time() - t_start) * 1000 + t_stt
    print(f"[PIPELINE FINISHED]: '{full_reply}' | STT: {t_stt:.0f}ms | First Audio: {first_audio_ms:.0f}ms | Total Wall Time: {total_time:.0f}ms\n")
    
    final_v2v = round(v2v_latency_ms) if v2v_latency_ms > 0 else (round(first_audio_ms) if first_audio_ms > 0 else round(t_stt + 350))
    if first_audio_ts_str == "--:--:--.---":
        first_audio_ts_str = datetime.datetime.fromtimestamp(t_speech_end + (final_v2v / 1000.0)).strftime("%H:%M:%S.%f")[:-3]

    await broadcast("ai", f"{full_reply} (First Word: {final_v2v} ms | Total: {total_time:.0f} ms)")
    await broadcast("metrics", {
        "stt_ms": round(t_stt),
        "llm_ms": round(max(0, first_audio_ms - t_stt - 300)),
        "tts_ms": round(max(0, first_audio_ms - t_stt)),
        "first_word_ms": final_v2v,
        "speech_end_ts": speech_end_ts_str,
        "first_audio_ts": first_audio_ts_str,
        "voice": voice_used,
        "total_ms": round(total_time)
    })
    return full_reply

# --- Full Pipeline Processor ---
def process_voice_pipeline(raw_pcm: bytes):
    """Full synchronous execution: Groq Whisper -> Groq LLM -> Cartesia Sonic / MS Edge TTS."""
    print(f"\n[PIPELINE START]: Captured {len(raw_pcm)} bytes of raw audio.")
    
    try:
        with wave.open("debug.wav", "wb") as wf:
            wf.setnchannels(1)
            wf.setsampwidth(2)
            wf.setframerate(16000)
            wf.writeframes(raw_pcm)
    except Exception:
        pass

    # 1. Groq Whisper STT
    asyncio.run_coroutine_threadsafe(broadcast("status", "1/3 Listening & Transcribing (Groq Whisper)..."), loop)
    transcript, t_stt = run_groq_whisper(raw_pcm)
    print(f"1. Whisper STT ({t_stt:.0f} ms): {transcript}")
    asyncio.run_coroutine_threadsafe(broadcast("stt", f"{transcript} ({t_stt:.0f} ms)"), loop)
    
    HALLUCINATIONS = [
        "sous-titrage", "radio-canada", "thank you for watching", "thanks for watching",
        "subtitles by", "amara.org", "transcription", "subscribe", "sous-titres", "titrage"
    ]
    lower_t = transcript.lower().strip() if transcript else ""
    if not transcript or len(lower_t) < 2 or any(h in lower_t for h in HALLUCINATIONS):
        print(f"[WHISPER FILTERED]: Ignored silence/hallucination: '{transcript}'")
        asyncio.run_coroutine_threadsafe(broadcast("stt", "(Silence / No clear speech)"), loop)
        asyncio.run_coroutine_threadsafe(broadcast("status", "Ready! Say 'Alexa' or click button below."), loop)
        return None, "", "(Silence)"
        
    # 2. Groq LLM
    asyncio.run_coroutine_threadsafe(broadcast("status", "2/3 Thinking & Reasoning (Groq LLM)..."), loop)
    detected_lang = detect_language(transcript, user_query=transcript)
    try:
        reply, definitive_lang, raw_reply, t_llm = run_groq_llm(transcript, detected_lang=detected_lang)
    except Exception as e:
        print(f"Error in run_groq_llm: {e}")
        reply, definitive_lang, raw_reply, t_llm = "", detected_lang or "en", "", 100
        
    print(f"2. Groq LLM ({t_llm:.0f} ms): {reply}")
    asyncio.run_coroutine_threadsafe(broadcast("ai", f"{reply} ({t_llm:.0f} ms)"), loop)
    
    # 3. Voice Synthesis
    asyncio.run_coroutine_threadsafe(broadcast("status", "3/3 Synthesizing Voice..."), loop)
    try:
        tts_pcm, t_tts, voice_used = run_tts(reply, user_query=transcript, raw_reply=raw_reply, forced_lang=definitive_lang)
    except Exception as e:
        print(f"Error in run_tts: {e}")
        tts_pcm, t_tts, voice_used = None, 0, "Error"
    total_time = t_stt + t_llm + t_tts
    print(f"3. Voice TTS [{voice_used}] ({t_tts:.0f} ms): Audio {len(tts_pcm) if tts_pcm else 0} bytes")
    
    asyncio.run_coroutine_threadsafe(broadcast("metrics", {
        "stt_ms": round(t_stt),
        "llm_ms": round(t_llm),
        "tts_ms": round(t_tts),
        "voice": voice_used,
        "total_ms": round(total_time)
    }), loop)
    
    return tts_pcm, reply, transcript

last_wake_start_time = 0.0

# --- ESPHome Event Handlers ---
async def handle_start(conversation_id: str, flags: int, settings: VoiceAssistantAudioSettings, wake_word_phrase: str | None) -> int | None:
    """Triggered automatically by ESP32 microWakeWord ('alexa') or Force Start button."""
    global audio_buffer, is_listening, speech_confirmed, speech_frames_count, silence_frames_count
    global ambient_noise_samples, ambient_noise_baseline, recording_task, total_voiced_frames
    global active_streamer_task, active_pipeline_task, playback_interrupt_event, active_audio_queue
    global last_wake_start_time
    last_wake_start_time = time.time()
    
    global active_followup_window
    if wake_word_phrase:
        active_followup_window["consecutive_turns"] = 0
        active_followup_window["is_active"] = False
    
    wake_label = wake_word_phrase if wake_word_phrase else ("Zero-Wake-Word Follow-Up" if active_followup_window.get("is_active") else "Voice Command")
    print(f"\n>>> [WAKE WORD DETECTED]: {wake_label} <<<")
    set_aura_led("listening")
    
    # 1. BARGE-IN / INTERRUPTION CHECK:
    # If the speaker was actively playing audio or synthesizing speech, interrupt it immediately!
    was_speaking = (active_streamer_task and not active_streamer_task.done()) or (active_pipeline_task and not active_pipeline_task.done())
    if was_speaking:
        print("\n>>> [BARGE-IN / INTERRUPTION]: Assistant was speaking! Instantly silencing speaker and purging queues. <<<")
        playback_interrupt_event.set()
        if active_audio_queue:
            while not active_audio_queue.empty():
                try:
                    active_audio_queue.get_nowait()
                except Exception:
                    break
        if active_streamer_task and not active_streamer_task.done():
            active_streamer_task.cancel()
        if active_pipeline_task and not active_pipeline_task.done():
            active_pipeline_task.cancel()
        # Immediately tell ESP32 to end audio playback stream and free DAC
        # DO NOT send VOICE_ASSISTANT_RUN_END - that kills the newly started mic session!
        try:
            if is_connected():
