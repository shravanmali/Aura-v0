# Aura v0 Build Story

**By Shravan Mali**

This is the story of how I built Aura Version 0 on my desk using an ESP32-S3 and five basic hardware modules.

---

## The Spark

I wanted to build my own smart speaker from scratch on a breadboard. Most DIY assistants rely on a Raspberry Pi or feel really slow, with 3 to 5 second pauses before answering simple questions. I wanted to see how far I could push a humble microcontroller like the ESP32-S3 to make it respond fast, look alive with RGB LEDs, and even place phone calls through my home Wi-Fi landline.

---

## The 5 Hardware Parts

I kept the hardware minimal and clean:

1. **ESP32-S3 DevKitC-1** (N16R8, 16MB Flash, 8MB PSRAM)
2. **INMP441 MEMS Microphone Module** (I2S digital mic)
3. **MAX98357A Mono Amplifier Module** (I2S Class-D DAC)
4. **4Ω 3W Speaker**
5. **WS2812B 8-Pixel RGB LED Ring**

Along with standard jumper wires, a breadboard, and a USB cable.

---

## Real Problems and Late-Night Fixes

### 1. The 50Hz Power Line Hum
When I first plugged the INMP441 microphone into the breadboard, every single recording was ruined by a loud buzzing noise. It was a combination of 50Hz mains hum and the microphone power line picking up noise from the speaker's 5V rail.

**Fix:**
- I rewired the breadboard so the microphone received clean 3.3V power, physically separated from the 5V speaker line.
- In software, I wrote a quick 85Hz high-pass filter in Python to strip out any remaining low-frequency rumble before sending audio to speech-to-text.

### 2. ESP32 Crashing (Watchdog Resets)
Early on, I tried using one I2S bus for both microphone input and speaker output. During playback, if Wi-Fi packets jittered or delayed, the ESP32 CPU would lock up in the audio loop and trigger the FreeRTOS watchdog timer, causing the whole board to reboot.

**Fix:**
- I configured two completely separate I2S hardware buses in `voice_assistant.yaml`:
  - `i2s_in` on GPIO 15, 16, 17 strictly for the microphone.
  - `i2s_out` on GPIO 5, 6, 7 strictly for the speaker DAC.
- This stopped the lockups completely. The ESP32 can now stream audio in both directions at the same time without crashing.

### 3. Sluggish Responses (3-5 Second Delays)
Local speech-to-text models on my computer were taking 2 to 3 seconds just to transcribe the audio. By the time the LLM answered and TTS converted it to audio, 5 seconds had passed.

**Fix:**
- I connected the backend to Groq's Whisper Turbo API for fast speech recognition (~250ms), paired with fast neural TTS voices (Cartesia and Edge-TTS).
- This brought the total turnaround time down to around 800ms, making conversations feel natural.

### 4. Acoustic Feedback During Phone Calls
When testing phone calls with MicroSIP through my home JioFiber router, the speaker output was loud enough that the INMP441 microphone would pick it up and echo it back into the caller's ear.

**Fix:**
- I added software ducking: whenever the speaker is playing incoming caller audio, the microphone gain is dialed down so it doesn't feed back. As soon as the caller pauses, the mic opens back up.

---

## What Works Today

- `✅` Real-time on-device wake word ("Alexa") on ESP32-S3.
- `✅` Fast voice conversation loop (sub-800ms response time).
- `✅` 8-pixel RGB LED ring animations for listening, thinking, and speaking.
- `✅` Voice-activated phone calls through my home Wi-Fi landline via SIP.
- `✅` Microphone barge-in: interrupts speech playback if you speak up.
- `✅` Simple conversation memory for kitchen ingredients and cooking timers.

---

## What's Next (Aura v1)

Now that Version 0 is fully tested on a breadboard, my next step for Version 1 is to design a custom PCB carrier in KiCad so I can replace all the messy jumper wires and mount everything onto a mobile robot chassis.
