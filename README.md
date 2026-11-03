# Aura (Version 0) - ESP32-S3 Voice Assistant & Landline

Hi, I'm Shravan Mali. I'm a student builder and this is Aura v0: a fast DIY smart speaker and VoIP landline that I built on my desk using an ESP32-S3 and five basic hardware modules.

Standard DIY voice assistants usually feel sluggish and take 3 to 5 seconds to reply. My goal was to make something that talks back in under one second, looks cool with an LED ring, and can even place real phone calls through my home Wi-Fi router.

---

## What Aura Does

- **Sub-Second Voice Chat**: Listens for the wake word, sends audio to my computer over Wi-Fi, and speaks back in under 800ms.
- **On-Device Wake Word**: Runs an on-device "Alexa" wake word detector right on the ESP32-S3 silicon so it doesn't stream audio 24/7.
- **Wi-Fi Phone Calls**: Connects to my home JioFiber broadband router via SIP (MicroSIP) so I can say "Alexa, call Mom" or "Alexa, call myself" and talk hands-free through the speaker and microphone.
- **Visual Feedback**: An 8-pixel WS2812 RGB LED ring changes colors depending on what Aura is doing (listening, thinking, speaking, or in a call).
- **Interruption (Barge-In)**: If Aura is speaking and you talk over it, the microphone detects your voice and stops playback immediately.
- **Desk Memory & Timers**: Remembers facts you tell it (like where you put your keys or what ingredients you have in the kitchen) and runs cooking timers.

---

## Bench Demos & Video Proof

Here are short videos of the actual hardware running live on my desk:

- **Video 1: Fast Voice Query (Weather & Bitcoin)**  
  ▶️ [Watch on YouTube Shorts](https://youtube.com/shorts/PmZ0z8Imm-w)  
  *Testing wake word response time, weather lookup, and live crypto price.*

- **Video 2: Live ESP32 VoIP Phone Call ("Alexa, Call Myself")**  
  ▶️ [Watch on YouTube Shorts](https://youtube.com/shorts/HGMN75dKRuE)  
  *Making an actual phone call using my home JioFiber SIP connection through the ESP32 speaker and mic.*

- **Video 3: Long Term Memory Recall ("Registered on Stardance")**  
  ▶️ [Watch on YouTube Shorts](https://youtu.be/rkv8eTRfRxI)  
  *Asking Aura to remember my name and registration on Stardance, then querying it back.*

---

## Working Features Tested on My Bench

- `✅` On-device wake word detection running on ESP32-S3 via ESPHome `micro_wake_word`
- `✅` Dual separate I2S buses so the mic and speaker don't crash the ESP32 FreeRTOS watchdog
- `✅` Sub-second voice pipeline using Groq Whisper, fast LLMs, and Cartesia/Edge-TTS
- `✅` 8-pixel WS2812B addressable LED ring showing states (idle, listening, thinking, speaking)
- `✅` Landline calling through home router SIP server using MicroSIP audio loopback
- `✅` Microphone ducking so the speaker sound doesn't loop back into the microphone
- `✅` Local cooking timers, stopwatch, and ingredient-aware recipe guidance
- `✅` Web dashboard on port 8080 showing live conversation state and timers

---

## Hardware Parts (5 Core Components)

Everything is currently wired on a breadboard on my desk (see [`BOM.csv`](BOM.csv) for parts and suppliers):

1. **ESP32-S3 DevKitC-1** (N16R8 with 16MB Flash and 8MB Octal PSRAM)
2. **INMP441 MEMS Microphone Module** (I2S digital input)
3. **MAX98357A Mono Amplifier Module** (I2S Class-D DAC)
4. **4Ω 3W Full-Range Speaker**
5. **WS2812B 8-Pixel RGB LED Ring**
6. Breadboard, jumper wires, and USB-C cable for power/flashing.

---

## Wiring & Pinout

