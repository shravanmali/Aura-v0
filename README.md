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

| Component | Pin Label | ESP32-S3 GPIO | Notes |
| :--- | :--- | :--- | :--- |
| **INMP441 Mic** | VDD | 3.3V | Logic power |
| | GND | GND | Ground |
| | SD | GPIO 17 | I2S Data In |
| | WS / LRCLK | GPIO 15 | Word Select clock |
| | SCK / BCLK | GPIO 16 | Bit Clock |
| | L/R | GND | Set to Left channel |
| **MAX98357A Amp** | VIN | 5V | Power for 3W output |
| | GND | GND | Ground |
| | DIN | GPIO 7 | I2S Data Out |
| | LRC / LRCLK | GPIO 6 | Word Select clock |
| | BCLK | GPIO 5 | Bit Clock |
| | GAIN | GND | 9dB gain setting |
| | SD_MODE | Not connected | Auto mono mix |
| **WS2812 LED Ring**| 5V / VDD | 5V | Power |
| | GND | GND | Ground |
| | DIN | GPIO 4 | RMT control pin |

> **Wiring tip from my desk testing:** Keep the mic wires away from the speaker wires. Early on I had electrical hum because the microphone lines were running directly next to the 5V speaker power wire. Putting them on opposite sides of the breadboard fixed the noise!

---

## LED Ring Colors

| State | LED Color | Meaning |
| :--- | :--- | :--- |
| **Idle** | Off | Waiting for wake word |
| **Listening** | Bright Cyan | Wake word detected, listening to you |
| **Thinking** | Blue Scan | Groq processing speech and generating reply |
| **Speaking** | Purple Pulse | Audio playing through the 3W speaker |
| **Call Ringing**| Amber Scan | Calling phone number via SIP |
| **In Call** | Green Solid | Phone call active |

---

## How to Set Up and Run

### 1. Set Up Python Environment
You need Python 3.10 or newer:

```bash
# Clone the repository
git clone https://github.com/shravanmali/aura-esp32-voice-assistant.git
cd aura-esp32-voice-assistant

# Create and activate virtual environment
python -m venv venv
# On Windows Powershell:
.\venv\Scripts\Activate.ps1
# On Linux/macOS:
source venv/bin/activate

# Install required packages
pip install aioesphomeapi aiohttp requests numpy soundfile edge-tts pyttsx3 flask
```

### 2. Configure Credentials
Copy the example files and fill in your details:

```bash
# Wi-Fi credentials for the ESP32
cp secrets.example.yaml secrets.yaml

# API keys for Groq and Cartesia
cp local_secrets.example.py local_secrets.py

# Optional: VoIP contacts and SIP setup
cp calling_test/contacts.example.json calling_test/contacts.json
cp calling_test/jio_config.example.json calling_test/jio_config.json
```

### 3. Flash the ESP32-S3
Connect your ESP32-S3 board with a USB-C cable:

```bash
# Flash via USB (change COM3 to your port)
esphome run voice_assistant.yaml --device COM3
```

Once flashed, the ESP32 connects to your Wi-Fi router. Future updates can be flashed wirelessly over the air (OTA).

### 4. Start the Voice Server
With your virtual environment active, run:

```bash
python voice_server.py
```

The server connects to the ESP32 at `192.168.31.200:6053` and opens a local web interface at `http://localhost:8080`. Say **"Alexa"** near the microphone and speak your question!

### 5. Optional: Run the VoIP Calling Bridge
If you want to test phone calls through your home broadband SIP line:
1. Download and install [MicroSIP](https://www.microsip.org/).
2. Run the calling bridge:
   ```bash
   cd calling_test
   python app.py
   ```
3. Open `http://localhost:5050` in your browser to test dialing numbers.

---

## Problems I Faced and How I Fixed Them

1. **50Hz Hum and Mic Buzzing:** The INMP441 was picking up electrical hum from the breadboard power rail. I added a software high-pass filter at 85Hz in Python and physically separated the microphone wires from the 5V speaker line.
2. **Watchdog Crashes on the ESP32:** Initially, both the mic and DAC shared the same I2S clock lines. When Wi-Fi packets slowed down during audio playback, the ESP32 would trigger a FreeRTOS watchdog reset. I solved this by splitting them into two completely separate I2S buses: `i2s_in` (GPIO 15, 16, 17) and `i2s_out` (GPIO 5, 6, 7).
3. **Response Delays:** Standard local models took 3-4 seconds to respond. Offloading to Groq Whisper and streaming neural TTS cut total response time to under a second.

---

## License

MIT License. Built by Shravan Mali with lots of late-night soldering and testing.
