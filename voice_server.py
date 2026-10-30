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
