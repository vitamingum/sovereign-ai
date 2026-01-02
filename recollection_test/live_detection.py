#!/usr/bin/env python3
"""
Live microphone input for real-time chord detection.

Requires: pip install pyaudio
"""

import numpy as np
import sys
import os

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from chord_detector import ChordDetector, SAMPLE_RATE, HOP_SIZE

try:
    import pyaudio
except ImportError:
    print("Install pyaudio: pip install pyaudio")
    sys.exit(1)


def main():
    """Run live chord detection from microphone."""
    detector = ChordDetector()
    
    # PyAudio setup
    p = pyaudio.PyAudio()
    
    print("=" * 50)
    print("LIVE CHORD DETECTION")
    print("=" * 50)
    print("Listening on default microphone...")
    print("Press Ctrl+C to stop")
    print("-" * 50)
    
    def audio_callback(in_data, frame_count, time_info, status):
        audio = np.frombuffer(in_data, dtype=np.float32)
        detector.process_frame(audio)
        return (in_data, pyaudio.paContinue)
    
    stream = p.open(
        format=pyaudio.paFloat32,
        channels=1,
        rate=SAMPLE_RATE,
        input=True,
        frames_per_buffer=HOP_SIZE,
        stream_callback=audio_callback
    )
    
    stream.start_stream()
    
    last_chord = None
    
    try:
        while stream.is_active():
            result = detector.get_latest()
            if result and result.label != last_chord:
                conf_bar = "█" * int(result.confidence * 20)
                print(f"\r{result.label:8s} {conf_bar:20s} ({result.confidence:.2f})", end="", flush=True)
                last_chord = result.label
            
            import time
            time.sleep(0.05)
    
    except KeyboardInterrupt:
        print("\n\nStopped.")
    
    finally:
        stream.stop_stream()
        stream.close()
        p.terminate()


if __name__ == "__main__":
    main()
