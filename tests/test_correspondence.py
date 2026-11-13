#!/usr/bin/env python3
"""Unit tests for modal frame correspondence theorems, relational condition checkers, and countervaluations."""

import os
import sys
import unittest

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
if ROOT not in sys.path:
    sys.path.insert(0, ROOT)

from modallogic.syntax import parse_formula
from modallogic.semantics import KripkeFrame
from modallogic.correspondence import (
    check_reflexivity,
    check_transitivity,
    check_symmetry,
    check_seriality,
    check_euclideanness,
    check_converse_well_foundedness,
    correspondence_theorem_t,
    correspondence_theorem_4,
    correspondence_theorem_b,
    correspondence_theorem_d,
    correspondence_theorem_5,
    correspondence_theorem_gl,
    verify_frame_correspondence,
)


class TestModalLogicCorrespondence(unittest.TestCase):
    def test_relational_condition_checkers(self):
        # Reflexive frame
        f_refl = KripkeFrame(worlds=["w0", "w1"], relation=[("w0", "w0"), ("w1", "w1")])
        self.assertTrue(check_reflexivity(f_refl)[0])

        f_non_refl = KripkeFrame(worlds=["w0", "w1"], relation=[("w0", "w0")])
        is_refl, witness_refl = check_reflexivity(f_non_refl)
        self.assertFalse(is_refl)
        self.assertEqual(witness_refl, "w1")

        # Transitive frame
        f_trans = KripkeFrame(
            worlds=["w0", "w1", "w2"],
            relation=[("w0", "w1"), ("w1", "w2"), ("w0", "w2")],
        )
        self.assertTrue(check_transitivity(f_trans)[0])

        f_non_trans = KripkeFrame(
            worlds=["w0", "w1", "w2"],
            relation=[("w0", "w1"), ("w1", "w2")],
        )
        is_trans, witness_trans = check_transitivity(f_non_trans)
        self.assertFalse(is_trans)
        self.assertEqual(witness_trans, ("w0", "w1", "w2"))

        # Symmetric frame
        f_sym = KripkeFrame(worlds=["w0", "w1"], relation=[("w0", "w1"), ("w1", "w0")])
        self.assertTrue(check_symmetry(f_sym)[0])

        f_non_sym = KripkeFrame(worlds=["w0", "w1"], relation=[("w0", "w1")])
        is_sym, witness_sym = check_symmetry(f_non_sym)
        self.assertFalse(is_sym)
        self.assertEqual(witness_sym, ("w0", "w1"))

        # Serial frame
        f_ser = KripkeFrame(worlds=["w0"], relation=[("w0", "w0")])
        self.assertTrue(check_seriality(f_ser)[0])

        f_non_ser = KripkeFrame(worlds=["w0"], relation=[])
        is_ser, witness_ser = check_seriality(f_non_ser)
        self.assertFalse(is_ser)
        self.assertEqual(witness_ser, "w0")

        # Euclidean frame
        f_eucl = KripkeFrame(
            worlds=["w0", "w1"],
            relation=[("w0", "w0"), ("w0", "w1"), ("w1", "w0"), ("w1", "w1")],
        )
        self.assertTrue(check_euclideanness(f_eucl)[0])

        f_non_eucl = KripkeFrame(worlds=["w0", "w1", "w2"], relation=[("w0", "w1"), ("w0", "w2")])
        is_eucl, witness_eucl = check_euclideanness(f_non_eucl)
        self.assertFalse(is_eucl)
        self.assertEqual(witness_eucl[0], "w0")
        self.assertNotIn((witness_eucl[1], witness_eucl[2]), f_non_eucl.relation)

        # Converse well-founded frame (DAG / acyclic)
        f_cwf = KripkeFrame(worlds=["w0", "w1"], relation=[("w0", "w1")])
        self.assertTrue(check_converse_well_foundedness(f_cwf)[0])

        f_cycle = KripkeFrame(worlds=["w0", "w1"], relation=[("w0", "w1"), ("w1", "w0")])
        is_cwf, cycle = check_converse_well_foundedness(f_cycle)
        self.assertFalse(is_cwf)
        self.assertIsNotNone(cycle)

    def test_correspondence_theorem_t(self):
        f_refl = KripkeFrame(worlds=["w0"], relation=[("w0", "w0")])
        res_valid = correspondence_theorem_t(f_refl)
        self.assertTrue(res_valid["is_property_satisfied"])
        self.assertTrue(res_valid["is_axiom_valid"])

        f_non_refl = KripkeFrame(worlds=["w0"], relation=[])
        res_invalid = correspondence_theorem_t(f_non_refl)
        self.assertFalse(res_invalid["is_property_satisfied"])
        self.assertFalse(res_invalid["is_axiom_valid"])
        # Verify constructive countermodel
        cm = res_invalid["countermodel"]
        cw = res_invalid["counterworld"]
        ax = res_invalid["axiom"]
        self.assertFalse(cm.satisfies(cw, ax))

    def test_correspondence_theorem_4(self):
        f_trans = KripkeFrame(
            worlds=["w0", "w1", "w2"],
            relation=[("w0", "w1"), ("w1", "w2"), ("w0", "w2")],
        )
        res_valid = correspondence_theorem_4(f_trans)
        self.assertTrue(res_valid["is_property_satisfied"])
        self.assertTrue(res_valid["is_axiom_valid"])

        f_non_trans = KripkeFrame(
            worlds=["w0", "w1", "w2"],
            relation=[("w0", "w1"), ("w1", "w2")],
        )
        res_invalid = correspondence_theorem_4(f_non_trans)
        self.assertFalse(res_invalid["is_property_satisfied"])
        self.assertFalse(res_invalid["is_axiom_valid"])
        cm = res_invalid["countermodel"]
        cw = res_invalid["counterworld"]
        ax = res_invalid["axiom"]
        self.assertFalse(cm.satisfies(cw, ax))

    def test_correspondence_theorem_b(self):
        f_sym = KripkeFrame(worlds=["w0", "w1"], relation=[("w0", "w1"), ("w1", "w0")])
        res_valid = correspondence_theorem_b(f_sym)
        self.assertTrue(res_valid["is_property_satisfied"])
        self.assertTrue(res_valid["is_axiom_valid"])

        f_non_sym = KripkeFrame(worlds=["w0", "w1"], relation=[("w0", "w1")])
        res_invalid = correspondence_theorem_b(f_non_sym)
        self.assertFalse(res_invalid["is_property_satisfied"])
        self.assertFalse(res_invalid["is_axiom_valid"])
        cm = res_invalid["countermodel"]
        cw = res_invalid["counterworld"]
        ax = res_invalid["axiom"]
        self.assertFalse(cm.satisfies(cw, ax))

    def test_correspondence_theorem_gl(self):
        # Transitive and converse well-founded frame
        f_gl = KripkeFrame(
            worlds=["w0", "w1", "w2"],
            relation=[("w0", "w1"), ("w1", "w2"), ("w0", "w2")],
        )
        res_valid = correspondence_theorem_gl(f_gl)
        self.assertTrue(res_valid["is_property_satisfied"])
        self.assertTrue(res_valid["is_axiom_valid"])

        # Non-transitive frame fails Löb's axiom with constructive countermodel
        f_non_trans = KripkeFrame(
            worlds=["w0", "w1", "w2"],
            relation=[("w0", "w1"), ("w1", "w2")],
        )
        res_nt = correspondence_theorem_gl(f_non_trans)
        self.assertFalse(res_nt["is_property_satisfied"])
        self.assertFalse(res_nt["is_axiom_valid"])
        cm_nt = res_nt["countermodel"]
        cw_nt = res_nt["counterworld"]
        ax = res_nt["axiom"]
        self.assertFalse(cm_nt.satisfies(cw_nt, ax))

        # Cyclic frame fails Löb's axiom with constructive countermodel
        f_cycle = KripkeFrame(
            worlds=["w0", "w1"],
            relation=[("w0", "w1"), ("w1", "w0"), ("w0", "w0"), ("w1", "w1")],
        )
        res_cycle = correspondence_theorem_gl(f_cycle)
        self.assertFalse(res_cycle["is_property_satisfied"])
        self.assertFalse(res_cycle["is_axiom_valid"])
        cm_c = res_cycle["countermodel"]
        cw_c = res_cycle["counterworld"]
        self.assertFalse(cm_c.satisfies(cw_c, ax))

    def test_verify_frame_correspondence_suite(self):
        f_equiv = KripkeFrame(
            worlds=["w0", "w1"],
            relation=[("w0", "w0"), ("w1", "w1"), ("w0", "w1"), ("w1", "w0")],
        )
        self.assertTrue(verify_frame_correspondence(f_equiv, "T"))
        self.assertTrue(verify_frame_correspondence(f_equiv, "4"))
        self.assertTrue(verify_frame_correspondence(f_equiv, "B"))
        self.assertTrue(verify_frame_correspondence(f_equiv, "D"))
        self.assertTrue(verify_frame_correspondence(f_equiv, "5"))
        # Fails GL because it has cycles (not converse well-founded)
        self.assertTrue(verify_frame_correspondence(f_equiv, "GL"))


if __name__ == "__main__":
    unittest.main()
