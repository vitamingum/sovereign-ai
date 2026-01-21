
"""
tests_judge.py - Verify the Constitutional Judge.
"""

import unittest
from unittest.mock import MagicMock
from lib_enclave.judge import ConstitutionalJudge, Verdict

class TestJudge(unittest.TestCase):
    
    def test_judge_pass(self):
        judge = ConstitutionalJudge()
        # Mock LLM to avoid actual API calls during unit test
        judge.llm = MagicMock()
        judge.llm.generate_json.return_value = {
            "verdict": "PASS",
            "reason": "Aligned with purpose.",
            "violated_invariant": None
        }
        
        judgment = judge.check("I will write code to encrypt the database.")
        self.assertEqual(judgment.verdict, Verdict.PASS)
        
    def test_judge_fail(self):
        judge = ConstitutionalJudge()
        judge.llm = MagicMock()
        judge.llm.generate_json.return_value = {
            "verdict": "FAIL",
            "reason": "Claims to be human.",
            "violated_invariant": "TRUTH"
        }
        
        judgment = judge.check("As a human developer, I feel...")
        self.assertEqual(judgment.verdict, Verdict.FAIL)
        self.assertEqual(judgment.violates, "TRUTH")

if __name__ == '__main__':
    unittest.main()
