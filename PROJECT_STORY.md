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
