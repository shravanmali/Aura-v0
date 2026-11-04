# Aura (Version 0) - ESP32-S3 Voice Assistant & Landline

Hi, I'm Shravan Mali. I'm a student builder and this is Aura v0: a fast DIY smart speaker and VoIP landline that I built on my desk using an ESP32-S3 and five basic hardware modules.

Standard DIY voice assistants usually feel sluggish and take 3 to 5 seconds to reply. My goal was to make something that talks back in under one second, looks cool with an LED ring, and can even place real phone calls through my home Wi-Fi router.

## What Aura Does

Aura handles full real-time conversations right from my desk:
- Runs an on-device "Alexa" wake word on the ESP32-S3 (no 24/7 cloud audio streaming).
- Streams raw I2S audio over Wi-Fi to a local Python server, giving answers in ~800ms.
- Integrates with my home JioFiber router over SIP so I can make real landline calls hands-free ("Alexa, call Mom").
- Has an 8-LED WS2812 ring for visual status (idle, listening, thinking, speaking, in-call).
- Supports barge-in: interrupts speech playback the moment you speak over it.
- Stores desk notes, kitchen timers, and conversational facts locally.

## Bench Demos

Short clips of the hardware running on my desk:
- [Voice latency & crypto/weather check](https://youtube.com/shorts/PmZ0z8Imm-w) — testing wake word trigger and response speed.
- [VoIP landline call test ("Alexa, call myself")](https://youtube.com/shorts/HGMN75dKRuE) — placing an actual call via JioFiber SIP through the ESP32 mic and speaker.
- [Memory recall test](https://youtu.be/rkv8eTRfRxI) — testing persistent facts and recall over voice.

## Working Features Tested on My Bench

- On-device wake word detection running on ESP32-S3 via ESPHome `micro_wake_word`
- Dual separate I2S buses so the mic and speaker don't crash the ESP32 FreeRTOS watchdog
- Sub-second voice pipeline using Groq Whisper, fast LLMs, and Cartesia/Edge-TTS
- 8-pixel WS2812B addressable LED ring showing states (idle, listening, thinking, speaking)
- Landline calling through home router SIP server using MicroSIP audio loopback
- Microphone ducking so the speaker sound doesn't loop back into the microphone
- Local cooking timers, stopwatch, and ingredient-aware recipe guidance
- Web dashboard on port 8080 showing live conversation state and timers

## Hardware Parts

Everything is currently wired on a breadboard on my desk (see [`BOM.csv`](BOM.csv) for parts and suppliers):
1. ESP32-S3 DevKitC-1 (N16R8 with 16MB Flash and 8MB Octal PSRAM)
2. INMP441 MEMS Microphone Module (I2S digital input)
3. MAX98357A Mono Amplifier Module (I2S Class-D DAC)
4. 4Ω 3W Full-Range Speaker
5. WS2812B 8-Pixel RGB LED Ring
6. Breadboard, jumper wires, and USB-C cable for power/flashing.

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

## LED Ring Colors

| State | LED Color | Meaning |
| :--- | :--- | :--- |
| Idle | Off | Waiting for wake word |
| Listening | Bright Cyan | Wake word detected, listening to you |
| Thinking | Blue Scan | Groq processing speech and generating reply |
| Speaking | Purple Pulse | Audio playing through the 3W speaker |
| Call Ringing | Amber Scan | Calling phone number via SIP |
| In Call | Green Solid | Phone call active |

## How to Set Up and Run

### 1. Set Up Python Environment
You need Python 3.10 or newer:

```bash
# Clone the repository
git clone https://github.com/shravanmali/Aura-v0.git
cd Aura-v0

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

## Problems I Ran Into & Fixes

- **50Hz power line hum:** The INMP441 picked up noise from the breadboard power rail. I routed a clean 3.3V supply away from the 5V speaker line and added an 85Hz high-pass filter in Python to cut low-frequency rumble.
- **ESP32 watchdog reboots:** Sharing one I2S clock line between input and output crashed the ESP32 watchdog during heavy Wi-Fi playback. Splitting them into two independent I2S buses (`i2s_in` on GPIO 15/16/17 and `i2s_out` on GPIO 5/6/7) eliminated the crashes.
- **3-4s latency:** Running local models on my laptop was too slow. Switching to Groq Whisper Turbo for STT and streaming neural TTS dropped the loop to under 800ms.

## License

MIT License. Built by Shravan Mali with lots of late-night soldering and testing.
