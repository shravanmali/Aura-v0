# JioFiber SIP Calling Testbed

Small Flask helper to test VoIP dialing through my home JioFiber router before tying it into the voice assistant.

## Quick Start

```bash
cd calling_test
python app.py
```

Then open `http://localhost:5050` in your browser.

- Type in a phone number (e.g. `+91 9876543210`).
- Click **Call / Ring** to initiate the SIP handshake (`INVITE`, `100 Trying`, `180 Ringing`).
- Click **Hang Up** when done to send the `BYE` packet.
