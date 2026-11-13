#!/usr/bin/env python3
"""Unit tests for modal axiom schemas, modal systems, and frame correspondence."""

import os
import sys
import unittest

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
if ROOT not in sys.path:
    sys.path.insert(0, ROOT)

from modallogic.syntax import parse_formula, Box, Atom, Implies
from modallogic.semantics import KripkeFrame, is_frame_valid
from modallogic.axioms import (
    STANDARD_AXIOMS,
    SYSTEMS,
    axiom_k,
    axiom_t,
    axiom_4,
    axiom_b,
    axiom_d,
    axiom_5,
    axiom_gl,
    axiom_grz,
    axiom_c4,
    axiom_cd,
)


class TestModalLogicAxioms(unittest.TestCase):
    def test_standard_axioms_structure(self):
        self.assertIn("K", STANDARD_AXIOMS)
        self.assertIn("T", STANDARD_AXIOMS)
        self.assertIn("4", STANDARD_AXIOMS)
        self.assertIn("B", STANDARD_AXIOMS)
        self.assertIn("D", STANDARD_AXIOMS)
        self.assertIn("5", STANDARD_AXIOMS)
        self.assertIn("GL", STANDARD_AXIOMS)
        self.assertIn("Grz", STANDARD_AXIOMS)
        self.assertIn("C4", STANDARD_AXIOMS)
        self.assertIn("CD", STANDARD_AXIOMS)

    def test_modal_systems_verification(self):
        s4_sys = SYSTEMS["S4"]
        s5_sys = SYSTEMS["S5"]
        gl_sys = SYSTEMS["GL"]
        kd_sys = SYSTEMS["KD"]

        # Preorder frame (reflexive + transitive)
        f_preorder = KripkeFrame(
            worlds=["w0", "w1"],
            relation=[("w0", "w0"), ("w1", "w1"), ("w0", "w1")],
        )
        self.assertTrue(s4_sys.verify_frame(f_preorder))
        self.assertFalse(s5_sys.verify_frame(f_preorder))  # Not symmetric

        # Equivalence frame (reflexive + transitive + symmetric)
        f_equiv = f_preorder.symmetric_closure()
        self.assertTrue(s5_sys.verify_frame(f_equiv))

        # Serial frame
        f_serial = KripkeFrame(worlds=["w0", "w1"], relation=[("w0", "w1"), ("w1", "w0")])
        self.assertTrue(kd_sys.verify_frame(f_serial))

        # Dead-end world fails seriality
        f_deadend = KripkeFrame(worlds=["w0", "w1"], relation=[("w0", "w1")])
        self.assertFalse(kd_sys.verify_frame(f_deadend))

        # GL frame (transitive and irreflexive / acyclic)
        f_gl = KripkeFrame(
            worlds=["w0", "w1", "w2"],
            relation=[("w0", "w1"), ("w1", "w2"), ("w0", "w2")],
        )
        self.assertTrue(gl_sys.verify_frame(f_gl))

    def test_axiom_d_on_serial_frame(self):
        # D: []p -> <>p holds if and only if frame is serial
        f_serial = KripkeFrame(worlds=["w0", "w1"], relation=[("w0", "w1"), ("w1", "w0")])
        valid, _, _ = is_frame_valid(f_serial, axiom_d())
        self.assertTrue(valid)

        f_non_serial = KripkeFrame(worlds=["w0"], relation=[])
        valid_fail, _, _ = is_frame_valid(f_non_serial, axiom_d())
        self.assertFalse(valid_fail)

    def test_axiom_5_on_euclidean_frame(self):
        # 5: <>p -> []<>p holds on euclidean frames
        f_eucl = KripkeFrame(
            worlds=["w0", "w1"],
            relation=[("w0", "w0"), ("w0", "w1"), ("w1", "w0"), ("w1", "w1")],
        )
        valid, _, _ = is_frame_valid(f_eucl, axiom_5())
        self.assertTrue(valid)

    def test_axiom_gl_on_finite_transitive_acyclic_frame(self):
        # Gödel-Löb axiom []( []p -> p ) -> []p
        f_gl = KripkeFrame(
            worlds=["w0", "w1"],
            relation=[("w0", "w1")],
        )
        valid, _, _ = is_frame_valid(f_gl, axiom_gl())
        self.assertTrue(valid)

        # On reflexive frame (cycle w0 -> w0), GL must fail
        f_refl = KripkeFrame(worlds=["w0"], relation=[("w0", "w0")])
        valid_fail, _, _ = is_frame_valid(f_refl, axiom_gl())
        self.assertFalse(valid_fail)

    def test_determinism_axiom_cd(self):
        # CD: <>p -> []p holds if each world has at most 1 successor (functional)
        f_func = KripkeFrame(worlds=["w0", "w1"], relation=[("w0", "w1")])
        valid, _, _ = is_frame_valid(f_func, axiom_cd())
        self.assertTrue(valid)

        # Branching frame with 2 successors fails CD
        f_branch = KripkeFrame(worlds=["w0", "w1", "w2"], relation=[("w0", "w1"), ("w0", "w2")])
        valid_fail, _, _ = is_frame_valid(f_branch, axiom_cd())
        self.assertFalse(valid_fail)


if __name__ == "__main__":
    unittest.main()
