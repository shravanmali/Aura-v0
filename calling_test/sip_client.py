# Author: Shravan Mali
# Simple SIP UDP test client for local Wi-Fi calling tests

import socket
import uuid
import time
import threading

class SimpleSIPClient:
    def __init__(self, local_ip="0.0.0.0", local_port=5060, gateway_ip="192.168.29.1", gateway_port=5060):
        self.local_ip = local_ip
        self.local_port = local_port
        self.gateway_ip = gateway_ip
        self.gateway_port = gateway_port
        self.sock = None
        self.call_id = None
        self.tag = None
        self.branch = None
        self.active_call = False
        self.running = False
        self.log_callback = None

    def log(self, message):
        print(f"[SIP] {message}")
        if self.log_callback:
            self.log_callback(message)

    def start_listener(self):
        try:
            self.sock = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
            self.sock.settimeout(1.0)
            self.sock.bind((self.local_ip, self.local_port))
            self.running = True
            threading.Thread(target=self._listen_loop, daemon=True).start()
            self.log(f"SIP listener started on {self.local_ip}:{self.local_port}")
            return True
        except Exception as e:
            self.log(f"Port {self.local_port} busy ({e}), trying random port instead.")
            try:
                self.sock = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
                self.sock.settimeout(1.0)
                self.sock.bind(("0.0.0.0", 0))
                self.local_port = self.sock.getsockname()[1]
                self.running = True
                threading.Thread(target=self._listen_loop, daemon=True).start()
                self.log(f"SIP listener started on port {self.local_port}")
                return True
            except Exception as e2:
                self.log(f"Could not open UDP socket: {e2}")
                return False

    def _listen_loop(self):
        while self.running:
            try:
                data, addr = self.sock.recvfrom(4096)
                msg = data.decode('utf-8', errors='ignore')
                first_line = msg.split('\r\n')[0] if '\r\n' in msg else msg
                self.log(f"<-- From {addr[0]}: {first_line}")
                self._handle_response(msg)
            except socket.timeout:
                continue
            except Exception as e:
                if self.running:
                    self.log(f"Socket error: {e}")
                break

    def _handle_response(self, msg):
        lines = msg.split('\r\n')
        status_line = lines[0] if lines else ""
        if "100 Trying" in status_line:
            self.log("Gateway received request (100 Trying)")
        elif "180 Ringing" in status_line:
            self.log("Phone is ringing! (180 Ringing)")
        elif "200 OK" in status_line:
            self.log("Call answered (200 OK)")
        elif "401 Unauthorized" in status_line or "407 Proxy Authentication" in status_line:
            self.log("Router requested IMS authentication")
        elif "486 Busy Here" in status_line:
            self.log("Recipient is busy")
        elif "487 Request Terminated" in status_line:
            self.log("Call cancelled")

    def dial(self, from_number, to_number, host_ip=None):
        if not self.sock:
            self.start_listener()

        if host_ip is None:
            try:
                s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
                s.connect((self.gateway_ip, 80))
                host_ip = s.getsockname()[0]
                s.close()
            except Exception:
                host_ip = "192.168.31.72"

        self.call_id = f"{uuid.uuid4().hex}@{host_ip}"
        self.tag = uuid.uuid4().hex[:8]
        self.branch = f"z9hG4bK{uuid.uuid4().hex[:12]}"
        self.active_call = True

        sip_invite = (
            f"INVITE sip:{to_number}@{self.gateway_ip}:{self.gateway_port} SIP/2.0\r\n"
            f"Via: SIP/2.0/UDP {host_ip}:{self.local_port};branch={self.branch};rport\r\n"
            f"Max-Forwards: 70\r\n"
            f"From: <sip:{from_number}@{self.gateway_ip}>;tag={self.tag}\r\n"
            f"To: <sip:{to_number}@{self.gateway_ip}>\r\n"
            f"Call-ID: {self.call_id}\r\n"
            f"CSeq: 1 INVITE\r\n"
            f"Contact: <sip:{from_number}@{host_ip}:{self.local_port}>\r\n"
            f"User-Agent: JioFiber-VoiceTest/1.0\r\n"
            f"Allow: INVITE, ACK, CANCEL, OPTIONS, BYE\r\n"
            f"Content-Type: application/sdp\r\n"
            f"Content-Length: 0\r\n\r\n"
        )

        self.log(f"--> Sending SIP INVITE to {to_number}...")
        try:
            self.sock.sendto(sip_invite.encode('utf-8'), (self.gateway_ip, self.gateway_port))
            return True, self.call_id
        except Exception as e:
            self.log(f"Error sending INVITE: {e}")
            return False, str(e)

    def cancel(self, from_number, to_number, host_ip="192.168.31.72"):
        if not self.active_call or not self.call_id:
            return False

        sip_cancel = (
            f"CANCEL sip:{to_number}@{self.gateway_ip}:{self.gateway_port} SIP/2.0\r\n"
            f"Via: SIP/2.0/UDP {host_ip}:{self.local_port};branch={self.branch}\r\n"
            f"Max-Forwards: 70\r\n"
            f"From: <sip:{from_number}@{self.gateway_ip}>;tag={self.tag}\r\n"
            f"To: <sip:{to_number}@{self.gateway_ip}>\r\n"
            f"Call-ID: {self.call_id}\r\n"
            f"CSeq: 1 CANCEL\r\n"
            f"Content-Length: 0\r\n\r\n"
        )

        self.log("--> Sending SIP CANCEL to hang up...")
        try:
            self.sock.sendto(sip_cancel.encode('utf-8'), (self.gateway_ip, self.gateway_port))
            self.active_call = False
            return True
        except Exception as e:
            self.log(f"Error sending CANCEL: {e}")
            return False

    def close(self):
        self.running = False
        if self.sock:
            try:
                self.sock.close()
            except Exception:
                pass
            self.sock = None
