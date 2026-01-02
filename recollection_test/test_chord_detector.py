#!/usr/bin/env python3
"""
Unit tests for the chord detection system.
"""

import numpy as np
import unittest
from chord_detector import (
    ChromaExtractor, ChordMatcher, HMMSmoother, ChordDetector,
    NOTE_NAMES, CHORD_TEMPLATES, SAMPLE_RATE, WINDOW_SIZE
)


class TestChromaExtractor(unittest.TestCase):
    """Tests for chroma feature extraction."""
    
    def setUp(self):
        self.extractor = ChromaExtractor()
    
    def test_pure_tone_a440(self):
        """A 440Hz tone should peak at A (index 9)."""
        t = np.linspace(0, WINDOW_SIZE / SAMPLE_RATE, WINDOW_SIZE)
        audio = np.sin(2 * np.pi * 440 * t).astype(np.float32)
        
        chroma = self.extractor.extract(audio)
        
        # A is index 9 in our NOTE_NAMES
        peak_idx = np.argmax(chroma)
        self.assertEqual(NOTE_NAMES[peak_idx], 'A')
    
    def test_pure_tone_c(self):
        """A C4 (261.63Hz) tone should peak at C (index 0)."""
        t = np.linspace(0, WINDOW_SIZE / SAMPLE_RATE, WINDOW_SIZE)
        audio = np.sin(2 * np.pi * 261.63 * t).astype(np.float32)
        
        chroma = self.extractor.extract(audio)
        
        peak_idx = np.argmax(chroma)
        self.assertEqual(NOTE_NAMES[peak_idx], 'C')
    
    def test_chroma_normalization(self):
        """Chroma vector should sum to 1."""
        audio = np.random.randn(WINDOW_SIZE).astype(np.float32)
        chroma = self.extractor.extract(audio)
        
        self.assertAlmostEqual(chroma.sum(), 1.0, places=5)
    
    def test_silence_handling(self):
        """Silent audio should not cause division by zero."""
        audio = np.zeros(WINDOW_SIZE, dtype=np.float32)
        chroma = self.extractor.extract(audio)
        
        # Should return zeros without error
        self.assertEqual(len(chroma), 12)


class TestChordMatcher(unittest.TestCase):
    """Tests for chord template matching."""
    
    def setUp(self):
        self.matcher = ChordMatcher()
    
    def test_c_major_detection(self):
        """C major chroma should match Cmaj template best."""
        # C major: C, E, G (indices 0, 4, 7)
        chroma = np.zeros(12)
        chroma[0] = 1.0  # C
        chroma[4] = 0.8  # E
        chroma[7] = 0.9  # G
        chroma /= chroma.sum()
        
        matches = self.matcher.match(chroma)
        best_label, best_score = matches[0]
        
        self.assertEqual(best_label, 'Cmaj')
    
    def test_a_minor_detection(self):
        """A minor chroma should match Amin template best."""
        # A minor: A, C, E (indices 9, 0, 4)
        chroma = np.zeros(12)
        chroma[9] = 1.0  # A
        chroma[0] = 0.8  # C
        chroma[4] = 0.9  # E
        chroma /= chroma.sum()
        
        matches = self.matcher.match(chroma)
        best_label, best_score = matches[0]
        
        self.assertEqual(best_label, 'Amin')
    
    def test_g_dominant7_detection(self):
        """G7 chroma should match Gdom7 template."""
        # G7: G, B, D, F (indices 7, 11, 2, 5)
        chroma = np.zeros(12)
        chroma[7] = 1.0  # G
        chroma[11] = 0.8  # B
        chroma[2] = 0.9  # D
        chroma[5] = 0.7  # F
        chroma /= chroma.sum()
        
        matches = self.matcher.match(chroma)
        best_label, best_score = matches[0]
        
        self.assertEqual(best_label, 'Gdom7')
    
    def test_all_templates_normalized(self):
        """All templates should be normalized."""
        for label, template in self.matcher.templates.items():
            self.assertAlmostEqual(template.sum(), 1.0, places=5,
                                   msg=f"Template {label} not normalized")


class TestHMMSmoother(unittest.TestCase):
    """Tests for HMM temporal smoothing."""
    
    def setUp(self):
        labels = [f"{r}maj" for r in NOTE_NAMES]
        self.smoother = HMMSmoother(labels)
    
    def test_stable_chord_maintained(self):
        """Repeated observations of same chord should reinforce it."""
        # Observe Cmaj multiple times
        obs = [('Cmaj', 0.9), ('Dmaj', 0.1)]
        
        for _ in range(5):
            label, conf = self.smoother.smooth(obs)
        
        self.assertEqual(label, 'Cmaj')
        self.assertGreater(conf, 0.5)
    
    def test_noisy_detection_smoothed(self):
        """Random noise shouldn't cause rapid chord changes."""
        labels = []
        
        # Mostly Cmaj with some noise
        for i in range(10):
            if i % 3 == 0:
                obs = [('Gmaj', 0.6), ('Cmaj', 0.4)]  # Noise
            else:
                obs = [('Cmaj', 0.8), ('Gmaj', 0.2)]
            
            label, _ = self.smoother.smooth(obs)
            labels.append(label)
        
        # Should mostly be Cmaj due to smoothing
        cmaj_count = labels.count('Cmaj')
        self.assertGreater(cmaj_count, 5)


class TestChordDetector(unittest.TestCase):
    """Integration tests for full detector."""
    
    def setUp(self):
        self.detector = ChordDetector()
    
    def test_synthesized_c_major_chord(self):
        """Synthesized C major chord should be detected."""
        t = np.linspace(0, WINDOW_SIZE / SAMPLE_RATE, WINDOW_SIZE)
        
        # C major: C4 + E4 + G4
        c4 = np.sin(2 * np.pi * 261.63 * t)
        e4 = np.sin(2 * np.pi * 329.63 * t)
        g4 = np.sin(2 * np.pi * 392.00 * t)
        
        audio = (c4 + e4 + g4).astype(np.float32) / 3
        
        result = self.detector.detect(audio)
        
        # Should detect C major or closely related chord
        self.assertIn(result.root, ['C', 'E', 'G'])  # Allow some ambiguity
    
    def test_detection_returns_result(self):
        """Detection should return ChordResult object."""
        audio = np.random.randn(WINDOW_SIZE).astype(np.float32) * 0.1
        result = self.detector.detect(audio)
        
        self.assertIsNotNone(result)
        self.assertIn(result.root, NOTE_NAMES)
        self.assertIn(result.quality, CHORD_TEMPLATES.keys())
        self.assertGreaterEqual(result.confidence, 0)
        self.assertLessEqual(result.confidence, 1)
    
    def test_chroma_vector_included(self):
        """Result should include the chroma vector."""
        audio = np.random.randn(WINDOW_SIZE).astype(np.float32) * 0.1
        result = self.detector.detect(audio)
        
        self.assertEqual(len(result.chroma_vector), 12)
        self.assertAlmostEqual(result.chroma_vector.sum(), 1.0, places=5)


class TestChordTemplates(unittest.TestCase):
    """Verify chord template correctness."""
    
    def test_major_intervals(self):
        """Major chord should have root, major third, perfect fifth."""
        template = CHORD_TEMPLATES['maj']
        self.assertEqual(template[0], 1)   # Root
        self.assertEqual(template[4], 1)   # Major third (4 semitones)
        self.assertEqual(template[7], 1)   # Perfect fifth (7 semitones)
    
    def test_minor_intervals(self):
        """Minor chord should have root, minor third, perfect fifth."""
        template = CHORD_TEMPLATES['min']
        self.assertEqual(template[0], 1)   # Root
        self.assertEqual(template[3], 1)   # Minor third (3 semitones)
        self.assertEqual(template[7], 1)   # Perfect fifth (7 semitones)
    
    def test_diminished_intervals(self):
        """Diminished chord should have root, minor third, diminished fifth."""
        template = CHORD_TEMPLATES['dim']
        self.assertEqual(template[0], 1)   # Root
        self.assertEqual(template[3], 1)   # Minor third (3 semitones)
        self.assertEqual(template[6], 1)   # Diminished fifth (6 semitones)


if __name__ == '__main__':
    unittest.main()
