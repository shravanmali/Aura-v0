# Wi-Fi Landline Calling Testbed

Hi, I'm Shravan Mali. This is a small test helper I wrote to test dialing phone numbers through my home JioFiber broadband SIP connection from my computer.

---

## How to Test

1. **Start the Calling Server**:
   ```bash
   cd calling_test
   python app.py
   ```
2. **Open in Browser**:
   Go to [http://localhost:5050](http://localhost:5050).
3. **Dial a Number**:
   - Type in the destination number (e.g. `+91 9876543210`).
   - Click **Call / Ring**.
   - The web page shows the SIP protocol steps (`INVITE`, `100 Trying`, `180 Ringing`).
   - Click **Hang Up** when done.
