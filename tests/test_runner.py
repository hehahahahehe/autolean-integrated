import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

from autolean.lean import CompileResult
from autolean.providers.mock import MockProvider
from autolean.runner import clean_proof, render_proof, run_problem


class RunnerTests(unittest.TestCase):
    def test_render_replaces_only_hole(self):
        self.assertEqual(render_proof("theorem t : True := by\n  sorry", "by\n  trivial"), "theorem t : True := by\n  trivial")

    def test_fenced_proof_is_cleaned(self):
        self.assertEqual(clean_proof("```lean\nby\n  trivial\n```"), "by\n  trivial")

    def test_forbids_sorry(self):
        with self.assertRaises(ValueError):
            render_proof("theorem t : True := sorry", "by sorry")

    @patch("autolean.runner.compile_statement")
    def test_repair_loop(self, compile_mock):
        compile_mock.side_effect = [
            CompileResult(False, 1, "", "unsolved goals", 0.1, []),
            CompileResult(True, 0, "", "", 0.1, []),
        ]
        problem = {"problem_id": "t", "source": "minif2f", "formal_statement": "theorem t : True := sorry"}
        result = run_problem(Path(tempfile.gettempdir()), problem, MockProvider(["by\n  fail_if_success trivial", "by\n  trivial"]), 1)
        self.assertTrue(result["success"])
        self.assertEqual(result["repair_rounds"], 1)


if __name__ == "__main__":
    unittest.main()
