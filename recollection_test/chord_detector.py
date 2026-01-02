#!/usr/bin/env python3
"""
Real-time Chord Detection System

Pipeline: Raw Audio → STFT → Chroma → Template Matching → HMM Smoothing → Label

Supports:
- Live microphone input
- Audio file analysis
- Real-time streaming with confidence scores
"""

import numpy as np
from dataclasses import dataclass
from typing import Optional, List, Tuple
from collections import deque
import threading
import time

# Audio processing constants
SAMPLE_RATE = 44100
HOP_SIZE = 2048
WINDOW_SIZE = 4096
N_CHROMA = 12

# Note names for display
NOTE_NAMES = ['C', 'C#', 'D', 'D#', 'E', 'F', 'F#', 'G', 'G#', 'A', 'A#', 'B']

# Chord templates (binary patterns relative to root)
CHORD_TEMPLATES = {
    'maj': [1, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0],  # Root, M3, P5
    'min': [1, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0],  # Root, m3, P5
    'dim': [1, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0],  # Root, m3, d5
    'aug': [1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0],  # Root, M3, A5
    'maj7': [1, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 1], # Root, M3, P5, M7
    'min7': [1, 0, 0, 1, 0, 0, 0, 1, 0, 0, 1, 0], # Root, m3, P5, m7
    'dom7': [1, 0, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0], # Root, M3, P5, m7
    'sus4': [1, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0], # Root, P4, P5
    'sus2': [1, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0], # Root, M2, P5
}


@dataclass
class ChordResult:
    """Result of chord detection for a single frame."""
    root: str
    quality: str
    confidence: float
    timestamp: float
    chroma_vector: np.ndarray
    
    @property
    def label(self) -> str:
        return f"{self.root}{self.quality}"
    
    def __str__(self) -> str:
        return f"{self.label} ({self.confidence:.2f})"


class ChromaExtractor:
    """Extract chroma features from audio using STFT."""
    
    def __init__(self, sample_rate: int = SAMPLE_RATE, 
                 window_size: int = WINDOW_SIZE,
                 hop_size: int = HOP_SIZE):
        self.sample_rate = sample_rate
        self.window_size = window_size
        self.hop_size = hop_size
        
        # Precompute frequency bins to chroma mapping
        self._init_chroma_filter()
    
    def _init_chroma_filter(self):
        """Initialize the frequency-to-chroma filter bank."""
        n_fft = self.window_size
        freqs = np.fft.rfftfreq(n_fft, 1.0 / self.sample_rate)
        
        # Map frequencies to chroma bins (A4 = 440Hz reference)
        # Chroma = (12 * log2(f/440) + 69) mod 12
        self.chroma_filter = np.zeros((N_CHROMA, len(freqs)))
        
        for i, freq in enumerate(freqs):
            if freq > 20:  # Skip DC and very low frequencies
                # Convert frequency to MIDI note number
                midi = 12 * np.log2(freq / 440.0) + 69
                chroma_bin = int(round(midi)) % 12
                
                # Gaussian weighting around the bin center
                for c in range(N_CHROMA):
                    dist = min(abs(c - chroma_bin), 12 - abs(c - chroma_bin))
                    self.chroma_filter[c, i] = np.exp(-dist**2 / 0.5)
        
        # Normalize each chroma bin
        row_sums = self.chroma_filter.sum(axis=1, keepdims=True)
        row_sums[row_sums == 0] = 1
        self.chroma_filter /= row_sums
    
    def extract(self, audio: np.ndarray) -> np.ndarray:
        """
        Extract chroma features from audio buffer.
        
        Args:
            audio: Audio samples (mono, float32, normalized to [-1, 1])
            
        Returns:
            Chroma vector (12,) normalized to sum to 1
        """
        # Apply Hanning window
        if len(audio) < self.window_size:
            audio = np.pad(audio, (0, self.window_size - len(audio)))
        
        windowed = audio[:self.window_size] * np.hanning(self.window_size)
        
        # Compute magnitude spectrum
        spectrum = np.abs(np.fft.rfft(windowed))
        
        # Apply chroma filter
        chroma = self.chroma_filter @ spectrum
        
        # Normalize
        total = chroma.sum()
        if total > 0:
            chroma /= total
        
        return chroma


class ChordMatcher:
    """Match chroma vectors to chord templates."""
    
    def __init__(self):
        # Precompute normalized templates for all roots
        self.templates = {}
        for quality, pattern in CHORD_TEMPLATES.items():
            pattern = np.array(pattern, dtype=float)
            pattern /= pattern.sum()
            
            for root_idx in range(12):
                root_name = NOTE_NAMES[root_idx]
                # Rotate pattern to root
                rotated = np.roll(pattern, root_idx)
                self.templates[f"{root_name}{quality}"] = rotated
    
    def match(self, chroma: np.ndarray) -> List[Tuple[str, float]]:
        """
        Match chroma vector against all chord templates.
        
        Args:
            chroma: Normalized chroma vector (12,)
            
        Returns:
            List of (chord_label, similarity) tuples, sorted by similarity
        """
        scores = []
        for label, template in self.templates.items():
            # Cosine similarity
            similarity = np.dot(chroma, template)
            scores.append((label, similarity))
        
        scores.sort(key=lambda x: x[1], reverse=True)
        return scores


class HMMSmoother:
    """
    Hidden Markov Model for temporal smoothing of chord predictions.
    
    Uses chord transition probabilities to reduce spurious detections.
    """
    
    def __init__(self, chord_labels: List[str], smoothing_window: int = 5):
        self.chord_labels = chord_labels
        self.n_chords = len(chord_labels)
        self.smoothing_window = smoothing_window
        
        # Initialize transition matrix (favor staying in same chord)
        self.transition_matrix = np.full((self.n_chords, self.n_chords), 0.01)
        np.fill_diagonal(self.transition_matrix, 0.7)
        
        # Add musical relationships (circle of fifths transitions more likely)
        for i, label in enumerate(chord_labels):
            root_idx = NOTE_NAMES.index(label[:-3] if len(label) > 3 else label[:-2] if len(label) > 2 else label)
            fifth_idx = (root_idx + 7) % 12
            fourth_idx = (root_idx + 5) % 12
            
            # Find chords with fifth/fourth as root
            for j, other in enumerate(chord_labels):
                other_root = NOTE_NAMES.index(other[:-3] if len(other) > 3 else other[:-2] if len(other) > 2 else other)
                if other_root == fifth_idx or other_root == fourth_idx:
                    self.transition_matrix[i, j] = 0.15
        
        # Normalize rows
        self.transition_matrix /= self.transition_matrix.sum(axis=1, keepdims=True)
        
        # Recent observations buffer
        self.observations = deque(maxlen=smoothing_window)
        self.prev_state = None
    
    def smooth(self, observation_scores: List[Tuple[str, float]]) -> Tuple[str, float]:
        """
        Apply HMM smoothing to observation scores.
        
        Args:
            observation_scores: List of (chord_label, score) from matcher
            
        Returns:
            (smoothed_chord_label, confidence)
        """
        # Convert to probability distribution
        obs_probs = np.zeros(self.n_chords)
        for label, score in observation_scores:
            if label in self.chord_labels:
                idx = self.chord_labels.index(label)
                obs_probs[idx] = score
        
        # Normalize
        total = obs_probs.sum()
        if total > 0:
            obs_probs /= total
        
        self.observations.append(obs_probs)
        
        # Viterbi-style smoothing with recent history
        if self.prev_state is not None:
            # Prior from transition
            prior = self.transition_matrix[self.prev_state]
        else:
            prior = np.ones(self.n_chords) / self.n_chords
        
        # Combine with observation
        posterior = prior * obs_probs
        total = posterior.sum()
        if total > 0:
            posterior /= total
        
        # Select best chord
        best_idx = np.argmax(posterior)
        self.prev_state = best_idx
        
        return self.chord_labels[best_idx], posterior[best_idx]


class ChordDetector:
    """
    Main chord detection class combining all components.
    
    Usage:
        detector = ChordDetector()
        
        # From audio buffer
        result = detector.detect(audio_samples)
        
        # Streaming mode
        detector.start_stream()
        # ... audio callbacks feed detector.process_frame() ...
        detector.stop_stream()
    """
    
    def __init__(self, sample_rate: int = SAMPLE_RATE):
        self.sample_rate = sample_rate
        self.chroma_extractor = ChromaExtractor(sample_rate)
        self.matcher = ChordMatcher()
        
        # Build chord label list for HMM
        all_labels = []
        for quality in CHORD_TEMPLATES.keys():
            for root in NOTE_NAMES:
                all_labels.append(f"{root}{quality}")
        
        self.smoother = HMMSmoother(all_labels)
        
        # Streaming state
        self._streaming = False
        self._stream_thread = None
        self._audio_buffer = deque(maxlen=WINDOW_SIZE)
        self._results = deque(maxlen=100)
        self._lock = threading.Lock()
    
    def detect(self, audio: np.ndarray, timestamp: float = 0.0) -> ChordResult:
        """
        Detect chord from audio buffer.
        
        Args:
            audio: Audio samples (mono, float32)
            timestamp: Timestamp for this frame
            
        Returns:
            ChordResult with detected chord and confidence
        """
        # Extract chroma
        chroma = self.chroma_extractor.extract(audio)
        
        # Match against templates
        matches = self.matcher.match(chroma)
        
        # Apply HMM smoothing
        label, confidence = self.smoother.smooth(matches)
        
        # Parse label into root and quality
        for quality in sorted(CHORD_TEMPLATES.keys(), key=len, reverse=True):
            if label.endswith(quality):
                root = label[:-len(quality)]
                break
        else:
            root = label
            quality = 'maj'
        
        return ChordResult(
            root=root,
            quality=quality,
            confidence=confidence,
            timestamp=timestamp,
            chroma_vector=chroma
        )
    
    def process_frame(self, samples: np.ndarray):
        """Add samples to buffer and process if ready."""
        with self._lock:
            self._audio_buffer.extend(samples)
            
            if len(self._audio_buffer) >= WINDOW_SIZE:
                audio = np.array(list(self._audio_buffer))
                timestamp = time.time()
                result = self.detect(audio, timestamp)
                self._results.append(result)
    
    def get_latest(self) -> Optional[ChordResult]:
        """Get most recent detection result."""
        with self._lock:
            return self._results[-1] if self._results else None
    
    def start_stream(self, audio_callback=None):
        """Start streaming detection mode."""
        self._streaming = True
        if audio_callback:
            self._stream_thread = threading.Thread(
                target=self._stream_loop, 
                args=(audio_callback,)
            )
            self._stream_thread.start()
    
    def stop_stream(self):
        """Stop streaming detection mode."""
        self._streaming = False
        if self._stream_thread:
            self._stream_thread.join()
            self._stream_thread = None
    
    def _stream_loop(self, audio_callback):
        """Internal streaming loop."""
        while self._streaming:
            try:
                samples = audio_callback()
                if samples is not None:
                    self.process_frame(samples)
            except Exception as e:
                print(f"Stream error: {e}")
            time.sleep(HOP_SIZE / self.sample_rate)


def analyze_file(filepath: str, detector: ChordDetector = None) -> List[ChordResult]:
    """
    Analyze an audio file and return chord detections.
    
    Args:
        filepath: Path to audio file (WAV, MP3, etc.)
        detector: Optional pre-configured detector
        
    Returns:
        List of ChordResults with timestamps
    """
    try:
        import soundfile as sf
    except ImportError:
        raise ImportError("Install soundfile: pip install soundfile")
    
    # Load audio
    audio, sr = sf.read(filepath)
    
    # Convert to mono if stereo
    if len(audio.shape) > 1:
        audio = audio.mean(axis=1)
    
    # Resample if needed
    if sr != SAMPLE_RATE:
        # Simple resampling (for production, use librosa.resample)
        ratio = SAMPLE_RATE / sr
        new_length = int(len(audio) * ratio)
        indices = np.linspace(0, len(audio) - 1, new_length)
        audio = np.interp(indices, np.arange(len(audio)), audio)
    
    if detector is None:
        detector = ChordDetector()
    
    results = []
    hop = HOP_SIZE
    
    for i in range(0, len(audio) - WINDOW_SIZE, hop):
        frame = audio[i:i + WINDOW_SIZE]
        timestamp = i / SAMPLE_RATE
        result = detector.detect(frame, timestamp)
        results.append(result)
    
    return results


def print_chord_timeline(results: List[ChordResult], min_duration: float = 0.5):
    """Print chord changes with timestamps."""
    if not results:
        print("No chords detected")
        return
    
    current_chord = None
    start_time = 0
    
    for result in results:
        if result.label != current_chord:
            if current_chord is not None:
                duration = result.timestamp - start_time
                if duration >= min_duration:
                    print(f"{start_time:6.2f}s - {result.timestamp:6.2f}s: {current_chord}")
            current_chord = result.label
            start_time = result.timestamp
    
    # Print last chord
    if current_chord and results:
        print(f"{start_time:6.2f}s - {results[-1].timestamp:6.2f}s: {current_chord}")


if __name__ == "__main__":
    import sys
    
    if len(sys.argv) > 1:
        filepath = sys.argv[1]
        print(f"Analyzing: {filepath}")
        print("-" * 40)
        
        try:
            results = analyze_file(filepath)
            print_chord_timeline(results)
            
            print("-" * 40)
            print(f"Total frames: {len(results)}")
            if results:
                avg_conf = sum(r.confidence for r in results) / len(results)
                print(f"Average confidence: {avg_conf:.2f}")
        except Exception as e:
            print(f"Error: {e}")
    else:
        print("Real-time Chord Detection System")
        print("Usage: python chord_detector.py <audio_file>")
        print("\nSupported formats: WAV, MP3, FLAC, OGG (requires soundfile)")
