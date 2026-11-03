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
