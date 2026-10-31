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
