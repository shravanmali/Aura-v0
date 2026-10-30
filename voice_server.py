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
