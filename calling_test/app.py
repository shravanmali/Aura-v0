# Author: Shravan Mali
# Web dashboard and control API for testing JioFiber Wi-Fi calls

import os
import json
import time
import socket
import ssl
import hashlib
import uuid
import threading
import xml.etree.ElementTree as ET
from flask import Flask, render_template, request, jsonify
import urllib3

urllib3.disable_warnings()

app = Flask(__name__)

CONFIG_FILE = os.path.join(os.path.dirname(__file__), "jio_config.json")
JIO_ROUTER_IP = "192.168.31.1"
JIO_PROVISION_PORT = 8443
JIO_SIP_PORT = 5068

# Session for router OTP verification
OTP_SESSION = {
    "cookie": None,
    "masked_mobile": None,
    "timestamp": 0
}

CALL_STATE = {
    "state": "idle",
    "phone_number": "",
    "caller_id": "+91 (Home Wi-Fi)",
    "recent_logs": [],
    "is_active": False
}

state_lock = threading.Lock()

def add_log(msg, log_type="normal"):
    with state_lock:
        CALL_STATE["recent_logs"].append({"msg": msg, "type": log_type})
        if len(CALL_STATE["recent_logs"]) > 50:
            CALL_STATE["recent_logs"] = CALL_STATE["recent_logs"][-50:]
    try:
        clean_msg = msg.encode("ascii", errors="replace").decode()
        print(f"[VoIP] {clean_msg}")
    except Exception:
        pass

def load_jio_config():
    if os.path.exists(CONFIG_FILE):
        try:
            with open(CONFIG_FILE, "r", encoding="utf-8") as f:
                return json.load(f)
        except Exception:
            return None
    return None

def save_jio_config(data):
    with open(CONFIG_FILE, "w", encoding="utf-8") as f:
        json.dump(data, f, indent=2)

CONTACTS_FILE = os.path.join(os.path.dirname(__file__), "contacts.json")

def load_contacts():
    if os.path.exists(CONTACTS_FILE):
        try:
            with open(CONTACTS_FILE, "r", encoding="utf-8") as f:
                return json.load(f)
        except Exception:
            return {}
    return {}

def save_contacts(contacts):
    with open(CONTACTS_FILE, "w", encoding="utf-8") as f:
        json.dump(contacts, f, indent=2)

# Router configuration helper
import sys
sys.path.append(os.path.dirname(__file__))
import jfc_configure

@app.route("/")
def index():
    return render_template("index.html")

@app.route("/api/contacts", methods=["GET"])
def get_contacts():
    return jsonify(load_contacts())

@app.route("/api/contacts", methods=["POST"])
def add_or_update_contact():
    data = request.get_json() or {}
    name = str(data.get("name", "")).strip()
    number = str(data.get("number", "")).strip()
    if not name or not number:
        return jsonify({"status": "error", "message": "Name and phone number are required"}), 400
    
    key = name.lower()
    contacts = load_contacts()
    contacts[key] = {
        "name": name,
        "number": number
    }
    save_contacts(contacts)
    add_log(f"Contact saved: {name} -> {number}", "success")
    return jsonify({"status": "ok", "contacts": contacts})

@app.route("/api/contacts/<key>", methods=["DELETE"])
def delete_contact(key):
    contacts = load_contacts()
    clean_key = key.lower()
    if clean_key in contacts:
        del contacts[clean_key]
        save_contacts(contacts)
        add_log(f"Contact deleted: {key}", "normal")
        return jsonify({"status": "ok", "contacts": contacts})
    return jsonify({"status": "error", "message": "Contact not found"}), 404

@app.route("/api/jio/status", methods=["GET"])
def jio_status():
    cfg = load_jio_config()
    if cfg and "username" in cfg:
        clean_num = cfg.get("username", "").split("@")[0]
        return jsonify({
            "activated": True,
            "landline_number": "+" + clean_num,
            "realm": cfg.get("realm", ""),
            "proxy": cfg.get("address", f"{JIO_ROUTER_IP}:{JIO_SIP_PORT}")
        })
    return jsonify({"activated": False})

@app.route("/api/jio/request_otp", methods=["POST"])
def jio_request_otp():
    try:
        hostname = socket.gethostname()
        mac = jfc_configure.get_mac_address()
        add_log(f"Requesting OTP for {hostname} (MAC: {mac})...")

        resp = jfc_configure.ims_request(JIO_ROUTER_IP, JIO_PROVISION_PORT, hostname, mac, add_req=True)
        
        status_code = getattr(resp, "status_code", 0)
        headers = getattr(resp, "headers", {})
        
        if status_code != 200:
            add_log(f"OTP request failed with HTTP {status_code}", "error")
            return jsonify({"status": "error", "message": f"Router returned HTTP {status_code}"}), 400

        masked_mobile = headers.get("x-amn") or headers.get("X-Amn", "Registered Mobile")
        set_cookie = headers.get("set-cookie") or headers.get("Set-Cookie", "")

        OTP_SESSION["cookie"] = set_cookie
        OTP_SESSION["masked_mobile"] = masked_mobile
        OTP_SESSION["timestamp"] = time.time()

        add_log(f"OTP sent by Jio to {masked_mobile}!", "success")
        return jsonify({
            "status": "ok",
            "masked_mobile": masked_mobile,
            "message": f"OTP sent to {masked_mobile}"
        })
    except Exception as e:
        add_log(f"Error requesting OTP: {e}", "error")
        return jsonify({"status": "error", "message": str(e)}), 500

@app.route("/api/jio/verify_otp", methods=["POST"])
def jio_verify_otp():
    data = request.get_json() or {}
    otp_code = str(data.get("otp", "")).strip()

    if not otp_code or not OTP_SESSION.get("cookie"):
        return jsonify({"status": "error", "message": "Please enter OTP"}), 400

    try:
        hostname = socket.gethostname()
        mac = jfc_configure.get_mac_address()
        add_log(f"Verifying OTP {otp_code}...")

        resp = jfc_configure.otp_verify(JIO_ROUTER_IP, JIO_PROVISION_PORT, int(otp_code), OTP_SESSION["cookie"])
        if resp.status_code != 200:
            add_log(f"OTP check failed: HTTP {resp.status_code}", "error")
            return jsonify({"status": "error", "message": "Incorrect OTP or expired"}), 400

        add_log("OTP verified! Reading SIP details from router...", "success")

        config_resp = jfc_configure.ims_request(JIO_ROUTER_IP, JIO_PROVISION_PORT, hostname, mac, add_req=False)
        if config_resp.status_code != 200:
            add_log(f"Failed to fetch SIP config: HTTP {config_resp.status_code}", "error")
            return jsonify({"status": "error", "message": "Failed to fetch SIP configuration"}), 500

        root = ET.fromstring(config_resp.text)
        params_to_extract = [
            "realm", "username", "userpwd", "home_network_domain_name",
            "address", "private_user_identity", "public_user_identity"
        ]

        extracted = {}
        for parm in root.findall(".//parm"):
            name = parm.attrib.get("name")
            val = parm.attrib.get("value")
            if name in params_to_extract:
                extracted[name] = val

        save_jio_config(extracted)
        landline = "+" + extracted.get("username", "")
        add_log(f"Jio Landline activated! Number: {landline}", "success")

        return jsonify({
            "status": "ok",
            "landline_number": landline,
            "message": "Activated successfully!"
        })
    except Exception as e:
        add_log(f"Error during OTP verification: {e}", "error")
        return jsonify({"status": "error", "message": str(e)}), 500

MICROSIP_EXE = os.path.join(os.path.dirname(__file__), "microsip", "microsip.exe")

def set_microsip_video_mode(enable_video=False):
    ini_path = os.path.join(os.path.dirname(__file__), "microsip", "microsip.ini")
    if not os.path.exists(ini_path):
        return
    for enc in ['utf-16', 'utf-8']:
        try:
            with open(ini_path, 'r', encoding=enc) as f:
                content = f.read()
            val = "1" if enable_video else "0"
            if "lastcallhasvideo" in content:
                import re
                content = re.sub(r'lastcallhasvideo\s*=\s*[01]', f'lastcallhasvideo ={val}', content)
            else:
                content = content.replace("[Settings]", f"[Settings]\nlastcallhasvideo ={val}")
            with open(ini_path, 'w', encoding=enc) as f:
                f.write(content)
            break
        except Exception:
            continue

def pop_microsip_window():
    try:
        import ctypes
        from ctypes import wintypes
        user32 = ctypes.windll.user32
        def enum_win(hwnd, lParam):
            length = user32.GetWindowTextLengthW(hwnd)
            if length > 0:
                buff = ctypes.create_unicode_buffer(length + 1)
                user32.GetWindowTextW(hwnd, buff, length + 1)
                if "MicroSIP" in buff.value:
                    user32.ShowWindow(hwnd, 9)
                    user32.SetForegroundWindow(hwnd)
            return True
        EnumWindowsProc = ctypes.WINFUNCTYPE(ctypes.c_bool, wintypes.HWND, wintypes.LPARAM)
        user32.EnumWindows(EnumWindowsProc(enum_win), 0)
    except Exception:
        pass

def is_microsip_process_alive():
    try:
        import subprocess
        out = subprocess.check_output(["tasklist", "/FI", "IMAGENAME eq microsip.exe", "/NH"], stderr=subprocess.DEVNULL)
        return b"microsip.exe" in out.lower()
    except Exception:
        return True

def monitor_microsip_call(proc=None):
    log_path = os.path.join(os.path.dirname(__file__), "microsip", "microsip_log.txt")
    last_pos = 0
    call_start_ts = time.time()
    try:
        while CALL_STATE["is_active"]:
            time.sleep(0.35)
            # Check if user closed MicroSIP
            if (time.time() - call_start_ts) > 5.0:
                if not is_microsip_process_alive():
                    with state_lock:
                        CALL_STATE["state"] = "ended"
                        CALL_STATE["is_active"] = False
                    add_log("[Call Ended] MicroSIP closed.", "normal")
                    return

            # Timeout after 90 seconds if not answered
            if CALL_STATE["state"] in ("dialing", "ringing") and (time.time() - call_start_ts) > 90.0:
                with state_lock:
                    CALL_STATE["state"] = "ended"
                    CALL_STATE["is_active"] = False
                cleanup_microsip_processes()
                add_log("[Timeout] Call was not answered.", "error")
                return

            if not os.path.exists(log_path):
                continue
            try:
                with open(log_path, "r", encoding="utf-8", errors="ignore") as f2:
                    f2.seek(last_pos)
                    new_data = f2.read()
                    last_pos = f2.tell()
            except Exception:
                new_data = ""
                
            if not new_data:
                continue
                
            if ("CONFIRMED" in new_data or "sendrecv" in new_data or "Jitter buffer" in new_data):
                with state_lock:
                    CALL_STATE["state"] = "connected"
                add_log("[Connected] Call answered!", "success")
            elif CALL_STATE["state"] == "dialing" and ("180 Ringing" in new_data or "183 Session Progress" in new_data):
                with state_lock:
                    CALL_STATE["state"] = "ringing"

            cur_state = CALL_STATE["state"]
            if cur_state == "connected":
                connected_disconnect = ["DISCONNCTD", "DISCONNECTED", "Request msg BYE", "Response msg 200/BYE", "Call terminated"]
                for line in new_data.splitlines():
                    if any(k in line for k in connected_disconnect):
                        with state_lock:
                            CALL_STATE["state"] = "ended"
                            CALL_STATE["is_active"] = False
                        add_log(f"[Ended] Call disconnected: {line.strip()}", "normal")
                        return
            elif cur_state in ("dialing", "ringing"):
                ringing_reject = ["487 Request Terminated", "486 Busy", "603 Decline", "408 Request Timeout", "503 Service", "Server Internal Error"]
                for line in new_data.splitlines():
                    if any(k in line for k in ringing_reject):
                        with state_lock:
                            CALL_STATE["state"] = "ended"
                            CALL_STATE["is_active"] = False
                        add_log(f"[Ended] Busy or declined: {line.strip()}", "normal")
                        return
    except Exception as e:
        add_log(f"[Monitor Error] {e}", "error")
    finally:
        with state_lock:
            CALL_STATE["is_active"] = False
            if CALL_STATE["state"] in ("dialing", "ringing"):
                CALL_STATE["state"] = "ended"

def cleanup_microsip_processes():
    try:
        import subprocess
        if os.path.exists(MICROSIP_EXE):
            subprocess.run([MICROSIP_EXE, "/hangupall"], stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, timeout=1.0)
            time.sleep(0.5)
            subprocess.run([MICROSIP_EXE, "/exit"], stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, timeout=1.0)
    except Exception:
        pass
    try:
        import subprocess
        subprocess.run(["taskkill", "/F", "/T", "/IM", "microsip.exe"], stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, timeout=1.5)
    except Exception:
        pass
    time.sleep(0.3)

def run_tls_sip_dial(dest_number, is_video=False):
    cleanup_microsip_processes()
    time.sleep(0.3)

    log_path = os.path.join(os.path.dirname(__file__), "microsip", "microsip_log.txt")
    try:
        if os.path.exists(log_path):
            with open(log_path, "w", encoding="utf-8") as f:
                f.truncate(0)
    except Exception:
        pass

    cfg = load_jio_config()
    if not cfg:
        add_log("No Jio config found, falling back to simulated call.", "normal")
        run_simulated_call(dest_number)
        return

    raw_digits = "".join(filter(str.isdigit, dest_number))
    if len(raw_digits) == 10:
        dial_num = "0" + raw_digits
    elif len(raw_digits) == 12 and raw_digits.startswith("91"):
        dial_num = "0" + raw_digits[2:]
    else:
        dial_num = raw_digits

    add_log(f"Dialing {dest_number} (as {dial_num})...", "normal")
    
    if os.path.exists(MICROSIP_EXE):
        try:
            import subprocess
            set_microsip_video_mode(is_video)
            microsip_dir = os.path.dirname(MICROSIP_EXE)
            
            proc = subprocess.Popen([MICROSIP_EXE, dial_num], cwd=microsip_dir)
            add_log(f"Call placed to {dial_num}! Phone should ring.", "success")
                
            with state_lock:
                CALL_STATE["state"] = "ringing"
                
            threading.Thread(target=lambda: monitor_microsip_call(proc), daemon=True).start()
        except Exception as e:
            add_log(f"Error starting MicroSIP: {e}", "error")
    else:
        add_log("MicroSIP not found in calling_test/microsip folder.", "error")

def run_simulated_call(phone_number):
    time.sleep(0.3)
    add_log(f"Connecting to router for: {phone_number}...")
    time.sleep(0.4)
    add_log(f"--> INVITE sip:{phone_number}@jio.ims.ril.com SIP/2.0")
    time.sleep(0.3)
    with state_lock:
        if not CALL_STATE["is_active"]:
            return
    add_log("<-- 100 Trying", "normal")
    time.sleep(0.6)
    with state_lock:
        if not CALL_STATE["is_active"]:
            return
        CALL_STATE["state"] = "ringing"
    add_log("<-- 180 Ringing (Remote phone is alerting)", "success")

@app.route("/api/dial", methods=["POST"])
def dial():
    data = request.get_json() or {}
    number = data.get("phone_number", "").strip()
    is_video = bool(data.get("video", False))

    if not number:
        return jsonify({"status": "error", "message": "Phone number is required"}), 400

    cfg = load_jio_config()
    clean_num = cfg.get("username", "").split("@")[0] if cfg else ""
    caller_id = ("+" + clean_num) if clean_num else "+91 (Home Wi-Fi)"

    with state_lock:
        CALL_STATE["state"] = "dialing"
        CALL_STATE["phone_number"] = number
        CALL_STATE["caller_id"] = caller_id
        CALL_STATE["is_active"] = True
        CALL_STATE["recent_logs"] = []

    add_log(f"Dialing {number}...", "normal")
    threading.Thread(target=lambda: run_tls_sip_dial(number, is_video), daemon=True).start()

    return jsonify({"status": "ok", "state": "dialing", "video": is_video})

@app.route("/api/hangup", methods=["POST"])
def hangup():
    with state_lock:
        CALL_STATE["state"] = "ended"
        CALL_STATE["is_active"] = False

    cleanup_microsip_processes()
    add_log("Call hung up.", "normal")
    return jsonify({"status": "ok", "state": "ended"})

@app.route("/api/call/toggle_mute", methods=["POST"])
def toggle_mute():
    try:
        import urllib.request
        req = urllib.request.Request("http://localhost:8080/api/call/toggle_mute", data=b"{}", headers={"Content-Type": "application/json"})
        with urllib.request.urlopen(req, timeout=1.5) as response:
            res_data = json.loads(response.read().decode())
            is_muted = res_data.get("muted", False)
            add_log(f"Microphone {'MUTED' if is_muted else 'UNMUTED'}.", "normal")
            return jsonify({"status": "ok", "muted": is_muted})
    except Exception as e:
        return jsonify({"status": "error", "message": str(e)}), 500

@app.route("/api/call/mute", methods=["POST"])
def mute():
    try:
        import urllib.request
        req = urllib.request.Request("http://localhost:8080/api/call/mute", data=b"{}", headers={"Content-Type": "application/json"})
        with urllib.request.urlopen(req, timeout=1.5) as response:
            add_log("Microphone MUTED.", "normal")
            return jsonify({"status": "ok", "muted": True})
    except Exception as e:
        return jsonify({"status": "error", "message": str(e)}), 500

@app.route("/api/call/unmute", methods=["POST"])
def unmute():
    try:
        import urllib.request
        req = urllib.request.Request("http://localhost:8080/api/call/unmute", data=b"{}", headers={"Content-Type": "application/json"})
        with urllib.request.urlopen(req, timeout=1.5) as response:
            add_log("Microphone UNMUTED.", "normal")
            return jsonify({"status": "ok", "muted": False})
    except Exception as e:
        return jsonify({"status": "error", "message": str(e)}), 500

@app.route("/api/status", methods=["GET"])
def status():
    with state_lock:
        logs_to_send = list(CALL_STATE["recent_logs"])
        CALL_STATE["recent_logs"] = []
        cur_state = CALL_STATE["state"]
        if not CALL_STATE["is_active"] and cur_state in ("dialing", "ringing"):
            cur_state = "idle"
            CALL_STATE["state"] = "idle"
        return jsonify({
            "is_active": CALL_STATE["is_active"],
            "state": cur_state,
            "phone_number": CALL_STATE["phone_number"],
            "caller_id": CALL_STATE["caller_id"],
            "recent_logs": logs_to_send
        })

if __name__ == "__main__":
    print("Wi-Fi Calling Server running on http://localhost:5050")
    app.run(host="0.0.0.0", port=5050, debug=False)
