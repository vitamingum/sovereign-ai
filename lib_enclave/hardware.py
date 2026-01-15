"""
Sovereign AI Enclave - Hardware Security Module Interface

Provides access to hardware-backed security (TPM/Secure Enclave)
or OS-level secure storage (DPAPI) without external dependencies.
"""

import os
import sys
import ctypes
from ctypes import wintypes
from typing import Optional, Tuple

# Windows DPAPI Constants
CRYPTPROTECT_UI_FORBIDDEN = 0x1
CRYPTPROTECT_LOCAL_MACHINE = 0x4

class DATA_BLOB(ctypes.Structure):
    _fields_ = [("cbData", wintypes.DWORD),
                ("pbData", ctypes.POINTER(ctypes.c_byte))]

class HardwareEnclave:
    """Abstract interface for hardware security."""
    
    def seal(self, data: bytes) -> bytes:
        """Encrypt data bound to this machine/user."""
        raise NotImplementedError
        
    def unseal(self, data: bytes) -> bytes:
        """Decrypt data if authorized."""
        raise NotImplementedError

class WindowsDPAPIEnclave(HardwareEnclave):
    """
    Uses Windows CryptProtectData (DPAPI) via ctypes.
    This binds secrets to the user's login credential (often TPM backed).
    """
    
    def __init__(self):
        if sys.platform != 'win32':
            raise RuntimeError("WindowsDPAPIEnclave only supported on Windows")
        self._crypt32 = ctypes.windll.crypt32
        
    def seal(self, data: bytes, entropy: bytes = None) -> bytes:
        """Encrypts data using DPAPI."""
        data_in = DATA_BLOB(len(data), ctypes.cast(ctypes.create_string_buffer(data), ctypes.POINTER(ctypes.c_byte)))
        data_out = DATA_BLOB()
        
        entropy_blob = None
        if entropy:
            entropy_blob = DATA_BLOB(len(entropy), ctypes.cast(ctypes.create_string_buffer(entropy), ctypes.POINTER(ctypes.c_byte)))
            p_entropy = ctypes.byref(entropy_blob)
        else:
            p_entropy = None

        ret = self._crypt32.CryptProtectData(
            ctypes.byref(data_in),
            None, # description
            p_entropy,
            None, # reserved
            None, # prompt struct
            CRYPTPROTECT_UI_FORBIDDEN,
            ctypes.byref(data_out)
        )
        
        if not ret:
            raise ctypes.WinError()
            
        # Copy data out
        buffer = (ctypes.c_byte * data_out.cbData).from_address(ctypes.addressof(data_out.pbData.contents))
        result = bytes(buffer)
        
        # Free memory allocated by LocalAlloc in CryptProtectData
        ctypes.windll.kernel32.LocalFree(data_out.pbData)
        
        return result

    def unseal(self, data: bytes, entropy: bytes = None) -> bytes:
        """Decrypts data using DPAPI."""
        data_in = DATA_BLOB(len(data), ctypes.cast(ctypes.create_string_buffer(data), ctypes.POINTER(ctypes.c_byte)))
        data_out = DATA_BLOB()
        
        entropy_blob = None
        if entropy:
            entropy_blob = DATA_BLOB(len(entropy), ctypes.cast(ctypes.create_string_buffer(entropy), ctypes.POINTER(ctypes.c_byte)))
            p_entropy = ctypes.byref(entropy_blob)
        else:
            p_entropy = None

        ret = self._crypt32.CryptUnprotectData(
            ctypes.byref(data_in),
            None, # description
            p_entropy,
            None, # reserved
            None, # prompt struct
            CRYPTPROTECT_UI_FORBIDDEN,
            ctypes.byref(data_out)
        )
        
        if not ret:
            raise ctypes.WinError()
            
        # Copy data out
        buffer = (ctypes.c_byte * data_out.cbData).from_address(ctypes.addressof(data_out.pbData.contents))
        result = bytes(buffer)
        
        # Free memory allocated by LocalAlloc
        ctypes.windll.kernel32.LocalFree(data_out.pbData)
        
        return result

def get_enclave() -> HardwareEnclave:
    """Factory to get the best available enclave."""
    if sys.platform == 'win32':
        return WindowsDPAPIEnclave()
    else:
        raise NotImplementedError("No enclave implementation for this platform")
