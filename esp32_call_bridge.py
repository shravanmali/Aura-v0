# Author: Shravan Mali
# Audio bridge between ESP32 hardware and PC SIP phone (MicroSIP)

import time
import queue
import threading
import numpy as np
import scipy.signal as signal
import pyaudiowpatch as pyaudio
import comtypes
from ctypes import wintypes, POINTER, c_float
from comtypes import GUID, IUnknown, COMMETHOD, HRESULT

CLSID_MMDeviceEnumerator = GUID('{BCDE0395-E52F-467C-8E3D-C4579291692E}')
IID_IMMDeviceEnumerator = GUID('{A95664D2-9614-4F35-A746-DE8DB63617E6}')
IID_IAudioEndpointVolume = GUID('{5CDF2C82-841E-4546-9722-0CF74078229A}')
IID_IPropertyStore = GUID('{886d8eeb-8cf2-4446-8d02-cdba1dbdcf99}')

class PROPERTYKEY(comtypes.Structure):
    _fields_ = [('fmtid', GUID), ('pid', wintypes.DWORD)]

PKEY_Device_FriendlyName = PROPERTYKEY(GUID('{a45c254e-df1c-4efd-8020-67d146a850e0}'), 14)

class PROPVARIANT(comtypes.Structure):
    _fields_ = [
        ('vt', wintypes.USHORT),
        ('wReserved1', wintypes.USHORT),
        ('wReserved2', wintypes.USHORT),
        ('wReserved3', wintypes.USHORT),
        ('pwszVal', wintypes.LPWSTR),
    ]

class IPropertyStore(IUnknown):
    _iid_ = IID_IPropertyStore
    _methods_ = [
        COMMETHOD([], HRESULT, 'GetCount'),
        COMMETHOD([], HRESULT, 'GetAt'),
        COMMETHOD([], HRESULT, 'GetValue', (['in'], POINTER(PROPERTYKEY), 'key'), (['out'], POINTER(PROPVARIANT), 'pv')),
    ]

class IMMDevice(IUnknown):
    _iid_ = GUID('{D666063F-1587-4E43-81F1-B948E807363F}')
    _methods_ = [
        COMMETHOD([], HRESULT, 'Activate',
                  (['in'], POINTER(GUID), 'iid'),
                  (['in'], wintypes.DWORD, 'dwClsCtx'),
                  (['in'], POINTER(wintypes.DWORD), 'pActivationParams'),
                  (['out'], POINTER(POINTER(IUnknown)), 'ppInterface')),
        COMMETHOD([], HRESULT, 'OpenPropertyStore',
                  (['in'], wintypes.DWORD, 'stgmAccess'),
                  (['out'], POINTER(POINTER(IPropertyStore)), 'ppProperties')),
    ]

class IMMDeviceCollection(IUnknown):
    _iid_ = GUID('{0BD7A1BE-7A1A-44DB-8397-CC5392387B5E}')
    _methods_ = [
        COMMETHOD([], HRESULT, 'GetCount', (['out'], POINTER(wintypes.UINT), 'pcDevices')),
        COMMETHOD([], HRESULT, 'Item', (['in'], wintypes.UINT, 'nDevice'), (['out'], POINTER(POINTER(IMMDevice)), 'ppDevice')),
    ]

class IMMDeviceEnumerator(IUnknown):
    _iid_ = IID_IMMDeviceEnumerator
    _methods_ = [
        COMMETHOD([], HRESULT, 'EnumAudioEndpoints', (['in'], wintypes.DWORD, 'dataFlow'), (['in'], wintypes.DWORD, 'dwStateMask'), (['out'], POINTER(POINTER(IMMDeviceCollection)), 'ppDevices')),
    ]

class IAudioEndpointVolume(IUnknown):
    _iid_ = IID_IAudioEndpointVolume
    _methods_ = [
        COMMETHOD([], HRESULT, 'RegisterControlChangeNotify'),
        COMMETHOD([], HRESULT, 'UnregisterControlChangeNotify'),
        COMMETHOD([], HRESULT, 'GetChannelCount'),
        COMMETHOD([], HRESULT, 'SetMasterVolumeLevel'),
        COMMETHOD([], HRESULT, 'SetMasterVolumeLevelScalar', (['in'], c_float, 'fLevel'), (['in'], POINTER(GUID), 'pguidEventContext')),
        COMMETHOD([], HRESULT, 'GetMasterVolumeLevel'),
        COMMETHOD([], HRESULT, 'GetMasterVolumeLevelScalar', (['out'], POINTER(c_float), 'pfLevel')),
        COMMETHOD([], HRESULT, 'SetChannelVolumeLevel'),
        COMMETHOD([], HRESULT, 'SetChannelVolumeLevelScalar'),
        COMMETHOD([], HRESULT, 'GetChannelVolumeLevel'),
        COMMETHOD([], HRESULT, 'GetChannelVolumeLevelScalar'),
        COMMETHOD([], HRESULT, 'SetMute', (['in'], wintypes.BOOL, 'bMute'), (['in'], POINTER(GUID), 'pguidEventContext')),
        COMMETHOD([], HRESULT, 'GetMute', (['out'], POINTER(wintypes.BOOL), 'pbMute')),
    ]

# Mute laptop physical speaker so the caller sound only plays through the ESP32 speaker
def silence_laptop_physical_speakers():
    try:
        enumerator = comtypes.CoCreateInstance(CLSID_MMDeviceEnumerator, IMMDeviceEnumerator, comtypes.CLSCTX_INPROC_SERVER)
        for flow in [0, 1]:
            collection = enumerator.EnumAudioEndpoints(flow, 1)
            for i in range(collection.GetCount()):
                dev = collection.Item(i)
                props = dev.OpenPropertyStore(0)
                pv = props.GetValue(PKEY_Device_FriendlyName)
                name = str(pv.pwszVal)
                pEndpoint = dev.Activate(IID_IAudioEndpointVolume, comtypes.CLSCTX_INPROC_SERVER, None)
                vol = pEndpoint.QueryInterface(IAudioEndpointVolume)
                if 'REALTEK' in name.upper():
                    vol.SetMute(True, None)
                    print(f"[Audio Bridge] Muted laptop speaker '{name}' so room doesn't echo.")
                elif 'OMEN' in name.upper() or 'CABLE' in name.upper():
                    vol.SetMute(False, None)
                    vol.SetMasterVolumeLevelScalar(1.0, None)
    except Exception as e:
        print(f"[Audio Bridge] Note: Speaker mute check skipped: {e}")

class ESP32CallAudioBridge:
    def __init__(self, send_to_esp32_fn=None):
        self.send_to_esp32_fn = send_to_esp32_fn
        self.is_active = False
        self.is_muted = False
        self.pa = None
        self.inbound_thread = None
        self.outbound_thread = None
        
        self.cable_in_dev = None
        self.caller_loopback_dev = None
        self.caller_render_dev = None
        
        self.outbound_stream = None
        self.silent_render_stream = None
        
        self.caller_speaker_rms = 0.0
        self.last_caller_audio_time = 0.0
        self.current_out_gain = 1.0
        
        # Queue for mic audio from ESP32
        self.mic_queue = queue.Queue(maxsize=120)
        
        # 85Hz high-pass filter to remove desk rumble
        self.b_hp, self.a_hp = signal.butter(2, 85.0, 'highpass', fs=16000)
        self.hp_zi = signal.lfilter_zi(self.b_hp, self.a_hp) * 0.0

        # Small 3.2kHz boost for vocal clarity
        self._init_presence_filter()

    def _init_presence_filter(self):
        # Peaking filter at 3200Hz to make voice clear over phone compression
        fs = 16000.0
        f0 = 3200.0
        gain_db = 4.5
        q = 1.2
        a = 10.0 ** (gain_db / 40.0)
        w0 = 2.0 * np.pi * f0 / fs
        alpha = np.sin(w0) / (2.0 * q)

        b0 = 1.0 + alpha * a
        b1 = -2.0 * np.cos(w0)
        b2 = 1.0 - alpha * a
        a0 = 1.0 + alpha / a
        a1 = -2.0 * np.cos(w0)
        a2 = 1.0 - alpha / a

        self.b_eq = np.array([b0/a0, b1/a0, b2/a0], dtype=np.float32)
        self.a_eq = np.array([1.0, a1/a0, a2/a0], dtype=np.float32)
        self.eq_zi = signal.lfilter_zi(self.b_eq, self.a_eq) * 0.0

    # Look for VB-Cable and loopback audio devices
    def _discover_devices(self):
        if self.pa is None:
            self.pa = pyaudio.PyAudio()

        wasapi_api_idx = 2
        try:
            wasapi_info = self.pa.get_host_api_info_by_type(pyaudio.paWASAPI)
            wasapi_api_idx = wasapi_info['index']
        except Exception:
            pass

        self.cable_in_dev = None
        self.caller_loopback_dev = None
        self.caller_render_dev = None

        for i in range(self.pa.get_device_count()):
            try:
                d = self.pa.get_device_info_by_index(i)
                if d['hostApi'] != wasapi_api_idx:
                    continue
                name = d['name'].upper()
                is_loopback = d.get('isLoopbackDevice', False)
                
                # CABLE Input: we write mic audio here so MicroSIP can hear it
                if 'CABLE INPUT' in name and d['maxOutputChannels'] > 0 and not is_loopback:
                    self.cable_in_dev = d
                    
                # Loopback device to hear caller audio from MicroSIP
                if 'OMEN' in name and is_loopback and self.caller_loopback_dev is None:
                    self.caller_loopback_dev = d
                    
                if 'SPEAKERS (OMEN' in name and d['maxOutputChannels'] > 0 and not is_loopback and self.caller_render_dev is None:
                    self.caller_render_dev = d
            except Exception:
                pass

        print("[Audio Bridge] Found audio devices:")
        print(f"  -> Mic output (CABLE Input): {self.cable_in_dev['name'] if self.cable_in_dev else 'NOT FOUND'}")
        print(f"  -> Caller input (Loopback): {self.caller_loopback_dev['name'] if self.caller_loopback_dev else 'NOT FOUND'}")

    def start(self, send_fn=None):
        if self.is_active:
            return
        if send_fn:
            self.send_to_esp32_fn = send_fn

        self.is_active = True
        self.is_muted = False
        self.caller_speaker_rms = 0.0
        self.last_caller_audio_time = 0.0
        self.current_out_gain = 1.0
        
        silence_laptop_physical_speakers()
        
        # Clear out any old mic samples
        while not self.mic_queue.empty():
            try:
                self.mic_queue.get_nowait()
            except Exception:
                break
                
        self._discover_devices()
        
        self.hp_zi = signal.lfilter_zi(self.b_hp, self.a_hp) * 0.0
        self.eq_zi = signal.lfilter_zi(self.b_eq, self.a_eq) * 0.0
        print("[Audio Bridge] Starting audio bridge between MicroSIP and ESP32...")

        # Open output stream to CABLE Input at 48kHz stereo
        try:
            if self.cable_in_dev:
                self.outbound_stream = self.pa.open(
                    format=pyaudio.paInt16,
                    channels=2,
                    rate=48000,
                    output=True,
                    output_device_index=self.cable_in_dev['index'],
                    frames_per_buffer=960
                )
                print("[Audio Bridge] Mic stream open to CABLE Input.")
        except Exception as e:
            print(f"[Audio Bridge] Could not open mic stream: {e}")

        # Keep loopback clock running
        try:
            if self.caller_render_dev:
                self.silent_render_stream = self.pa.open(
                    format=pyaudio.paInt16,
                    channels=2,
                    rate=48000,
                    output=True,
                    output_device_index=self.caller_render_dev['index'],
                    frames_per_buffer=960
                )
        except Exception:
            self.silent_render_stream = None

        # Start thread to send ESP32 mic audio to MicroSIP
        self.outbound_thread = threading.Thread(target=self._run_outbound_loop, daemon=True)
        self.outbound_thread.start()

        # Start thread to read caller audio and send to ESP32 speaker
        self.inbound_thread = threading.Thread(target=self._run_inbound_loop, daemon=True)
        self.inbound_thread.start()

    def is_speaker_active_in_room(self) -> bool:
        return (time.time() - self.last_caller_audio_time) < 0.45

    def set_mute(self, muted: bool):
        self.is_muted = muted
        state = "MUTED" if muted else "UNMUTED"
        print(f"[Audio Bridge] Mic is now {state}")

    def toggle_mute(self) -> bool:
        self.is_muted = not self.is_muted
        state = "MUTED" if self.is_muted else "UNMUTED"
        print(f"[Audio Bridge] Toggled mic -> {state}")
        return self.is_muted

    # Put raw mic audio from ESP32 into queue
    def feed_esp32_mic_audio(self, pcm_bytes: bytes):
        if not self.is_active or not pcm_bytes:
            return
        try:
            self.mic_queue.put_nowait(pcm_bytes)
        except queue.Full:
            try:
                self.mic_queue.get_nowait()
                self.mic_queue.put_nowait(pcm_bytes)
            except Exception:
                pass

    # Worker thread: filters mic audio and sends to CABLE Input
    def _run_outbound_loop(self):
        while self.is_active:
            try:
                pcm_bytes = self.mic_queue.get(timeout=0.1)
            except queue.Empty:
                continue

            if not self.outbound_stream:
                continue

            in_samples = len(pcm_bytes) // 2
            out_samples_target = in_samples * 3

            if self.is_muted:
                silence_frame = b'\x00' * (out_samples_target * 4)
                try:
                    self.outbound_stream.write(silence_frame)
                except Exception:
                    pass
                continue

            try:
                samples = np.frombuffer(pcm_bytes, dtype=np.int16).astype(np.float32)
                if len(samples) == 0:
                    continue

                # Strip 50Hz/room rumble below 85Hz
                filtered_hp, self.hp_zi = signal.lfilter(self.b_hp, self.a_hp, samples, zi=self.hp_zi)

                # Vocal EQ boost
                voice_eq, self.eq_zi = signal.lfilter(self.b_eq, self.a_eq, filtered_hp, zi=self.eq_zi)

                # Duck mic if speaker is currently playing caller audio
                mic_rms = float(np.sqrt(np.mean(voice_eq ** 2)))
                now_ts = time.time()
                time_since_caller = now_ts - self.last_caller_audio_time
                speaker_active = (self.caller_speaker_rms > 40.0) or (time_since_caller < 0.45)

                if speaker_active:
                    if mic_rms < 400.0:
                        target_gain = 0.0
                    else:
                        target_gain = 0.85
                else:
                    target_gain = 1.80

                # Smooth gain transition to avoid pops
                self.current_out_gain = 0.70 * self.current_out_gain + 0.30 * target_gain

                if self.current_out_gain < 0.01:
                    silence_frame = b'\x00' * (out_samples_target * 4)
                    try:
                        self.outbound_stream.write(silence_frame)
                    except Exception:
                        pass
                    continue

                boosted = voice_eq * self.current_out_gain

                # Prevent audio clipping
                mag = np.abs(boosted)
                clip_mask = mag > 26000.0
                if np.any(clip_mask):
                    excess = mag[clip_mask] - 26000.0
                    compressed = 26000.0 + (32767.0 - 26000.0) * np.tanh(excess / 6000.0)
                    boosted[clip_mask] = np.sign(boosted[clip_mask]) * compressed

                processed_16k = np.clip(boosted, -32767.0, 32767.0).astype(np.float32)

                # Resample 16kHz to 48kHz for VB-Cable
                samples_48k = signal.resample_poly(processed_16k, 3, 1)

                # Convert to stereo
                int16_48k = np.clip(samples_48k, -32767.0, 32767.0).astype(np.int16)
                stereo_frame = np.column_stack([int16_48k, int16_48k]).tobytes()
                self.outbound_stream.write(stereo_frame)
            except Exception:
                pass

    # Worker thread: reads caller audio from MicroSIP and forwards to ESP32 speaker
