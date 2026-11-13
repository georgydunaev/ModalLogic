#!/usr/bin/env python3
"""Unit tests for bisimulations, maximal bisimulation fixed points, quotients, and modal invariance."""

import os
import sys
import unittest

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
if ROOT not in sys.path:
    sys.path.insert(0, ROOT)

from modallogic.syntax import parse_formula
from modallogic.semantics import KripkeFrame, KripkeModel
from modallogic.bisimulation import (
    is_bisimulation,
    compute_maximal_bisimulation,
    are_bisimilar,
    bisimulation_quotient,
    verify_modal_invariance,
)


class TestModalLogicBisimulation(unittest.TestCase):
    def setUp(self):
        # Model 1: 2 worlds: w0 -> w1 (p true at w1)
        f1 = KripkeFrame(worlds=["w0", "w1"], relation=[("w0", "w1")])
        self.m1 = KripkeModel(f1, {"p": ["w1"]})

        # Model 2: 3 worlds: u0 -> u1, u0 -> u2 (p true at u1 and u2)
        # u1 and u2 are duplicates, so u0 should be bisimilar to w0
        f2 = KripkeFrame(worlds=["u0", "u1", "u2"], relation=[("u0", "u1"), ("u0", "u2")])
        self.m2 = KripkeModel(f2, {"p": ["u1", "u2"]})

    def test_bisimulation_relation_check(self):
        rel = {("w0", "u0"), ("w1", "u1"), ("w1", "u2")}
        ok, reason = is_bisimulation(self.m1, self.m2, rel)
        self.assertTrue(ok, f"Expected bisimulation, but failed with: {reason}")

        # Invalid relation: pairing w1 (where p holds) with u0 (where p does not hold)
        bad_rel = {("w1", "u0")}
        bad_ok, _ = is_bisimulation(self.m1, self.m2, bad_rel)
        self.assertFalse(bad_ok)

    def test_maximal_bisimulation_computation(self):
        max_bisim = compute_maximal_bisimulation(self.m1, self.m2)
        self.assertIn(("w0", "u0"), max_bisim)
        self.assertIn(("w1", "u1"), max_bisim)
        self.assertIn(("w1", "u2"), max_bisim)
        self.assertNotIn(("w0", "u1"), max_bisim)

        self.assertTrue(are_bisimilar(self.m1, "w0", self.m2, "u0"))
        self.assertTrue(are_bisimilar(self.m1, "w1", self.m2, "u1"))
        self.assertFalse(are_bisimilar(self.m1, "w0", self.m2, "u1"))

    def test_bisimulation_quotient(self):
        # In model 2, u1 and u2 are bisimilar. The quotient should collapse them to 2 worlds!
        quotient = bisimulation_quotient(self.m2)
        self.assertEqual(len(quotient.worlds), 2)

    def test_modal_invariance(self):
        max_bisim = compute_maximal_bisimulation(self.m1, self.m2)
        test_formulas = [
            parse_formula("p"),
            parse_formula("~p"),
            parse_formula("[]p"),
            parse_formula("<>p"),
            parse_formula("[](p -> <>p)"),
            parse_formula("<>[]p"),
            parse_formula("p | ~p"),
        ]
        ok, reason = verify_modal_invariance(self.m1, self.m2, max_bisim, test_formulas)
        self.assertTrue(ok, f"Modal invariance violation: {reason}")


if __name__ == "__main__":
    unittest.main()
