#!/usr/bin/env python3
"""Unit tests for Kripke semantics, frame conditions, closures, and model checking."""

import os
import sys
import unittest

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
if ROOT not in sys.path:
    sys.path.insert(0, ROOT)

from modallogic.syntax import parse_formula, Atom, Box, Implies
from modallogic.semantics import KripkeFrame, KripkeModel, is_frame_valid
from modallogic.axioms import axiom_k, axiom_t, axiom_4, axiom_b, axiom_d, axiom_5, axiom_gl


class TestModalLogicSemantics(unittest.TestCase):
    def test_frame_properties_classification(self):
        # 1. Reflexive frame
        f_refl = KripkeFrame(worlds=["w0", "w1"], relation=[("w0", "w0"), ("w1", "w1"), ("w0", "w1")])
        self.assertTrue(f_refl.is_reflexive())
        self.assertFalse(f_refl.is_irreflexive())
        self.assertTrue(f_refl.is_serial())

        # 2. Symmetric frame
        f_sym = KripkeFrame(worlds=["w0", "w1"], relation=[("w0", "w1"), ("w1", "w0")])
        self.assertTrue(f_sym.is_symmetric())
        self.assertFalse(f_sym.is_reflexive())

        # 3. Transitive frame
        f_trans = KripkeFrame(
            worlds=["w0", "w1", "w2"],
            relation=[("w0", "w1"), ("w1", "w2"), ("w0", "w2")],
        )
        self.assertTrue(f_trans.is_transitive())

        # Intransitive frame
        f_not_trans = KripkeFrame(
            worlds=["w0", "w1", "w2"],
            relation=[("w0", "w1"), ("w1", "w2")],
        )
        self.assertFalse(f_not_trans.is_transitive())

        # 4. Euclidean frame: w R u and w R v implies u R v
        f_eucl = KripkeFrame(
            worlds=["w0", "w1", "w2"],
            relation=[
                ("w0", "w1"),
                ("w0", "w2"),
                ("w1", "w1"),
                ("w1", "w2"),
                ("w2", "w1"),
                ("w2", "w2"),
            ],
        )
        self.assertTrue(f_eucl.is_euclidean())

        # 5. Confluent (Church-Rosser / directed) frame
        f_confl = KripkeFrame(
            worlds=["w0", "w1", "w2", "w3"],
            relation=[("w0", "w1"), ("w0", "w2"), ("w1", "w3"), ("w2", "w3"), ("w3", "w3")],
        )
        self.assertTrue(f_confl.is_confluent())

        # 6. GL Frame (transitive and acyclic)
        f_gl = KripkeFrame(
            worlds=["w0", "w1", "w2"],
            relation=[("w0", "w1"), ("w1", "w2"), ("w0", "w2")],
        )
        self.assertTrue(f_gl.is_gl_frame())

        # Non-GL due to cycle
        f_cycle = KripkeFrame(
            worlds=["w0", "w1"],
            relation=[("w0", "w1"), ("w1", "w0"), ("w0", "w0"), ("w1", "w1")],
        )
        self.assertFalse(f_cycle.is_gl_frame())

    def test_frame_closures(self):
        frame = KripkeFrame(worlds=["w0", "w1", "w2"], relation=[("w0", "w1"), ("w1", "w2")])
        self.assertFalse(frame.is_reflexive())
        self.assertFalse(frame.is_transitive())
        self.assertFalse(frame.is_symmetric())

        r_clos = frame.reflexive_closure()
        self.assertTrue(r_clos.is_reflexive())
        self.assertIn(("w0", "w0"), r_clos.relation)

        t_clos = frame.transitive_closure()
        self.assertTrue(t_clos.is_transitive())
        self.assertIn(("w0", "w2"), t_clos.relation)

        s_clos = frame.symmetric_closure()
        self.assertTrue(s_clos.is_symmetric())
        self.assertIn(("w1", "w0"), s_clos.relation)

        eq_clos = frame.equivalence_closure()
        self.assertTrue(eq_clos.is_s5_frame())

    def test_kripke_model_evaluation(self):
        frame = KripkeFrame(worlds=["w0", "w1"], relation=[("w0", "w1")])
        model = KripkeModel(frame, {"p": ["w1"], "q": ["w0", "w1"]})

        p = parse_formula("p")
        q = parse_formula("q")
        self.assertFalse(model.satisfies("w0", p))
        self.assertTrue(model.satisfies("w1", p))
        self.assertTrue(model.satisfies("w0", q))

        box_p = parse_formula("[]p")
        self.assertTrue(model.satisfies("w0", box_p))
        self.assertTrue(model.satisfies("w1", box_p))  # w1 has no successors (vacuously true)

        dia_p = parse_formula("<>p")
        self.assertTrue(model.satisfies("w0", dia_p))
        self.assertFalse(model.satisfies("w1", dia_p))

        self.assertEqual(model.truth_set(q), {"w0", "w1"})
        self.assertTrue(model.is_globally_true(q))

    def test_frame_validity_correspondence(self):
        # Axiom K is valid on ANY frame
        frame_any = KripkeFrame(worlds=["w0", "w1"], relation=[("w0", "w1")])
        valid_k, _, _ = is_frame_valid(frame_any, axiom_k())
        self.assertTrue(valid_k)

        # Axiom T valid on reflexive frame, invalid on irreflexive frame
        frame_refl = KripkeFrame(worlds=["w0"], relation=[("w0", "w0")])
        valid_t, _, _ = is_frame_valid(frame_refl, axiom_t())
        self.assertTrue(valid_t)

        frame_irref = KripkeFrame(worlds=["w0"], relation=[])
        valid_t_fail, countermodel, counterworld = is_frame_valid(frame_irref, axiom_t())
        self.assertFalse(valid_t_fail)
        self.assertIsNotNone(countermodel)

        # Axiom 4 valid on transitive frame, invalid on intransitive frame
        frame_trans = KripkeFrame(
            worlds=["w0", "w1", "w2"],
            relation=[("w0", "w1"), ("w1", "w2"), ("w0", "w2")],
        )
        valid_4, _, _ = is_frame_valid(frame_trans, axiom_4())
        self.assertTrue(valid_4)

        frame_not_trans = KripkeFrame(
            worlds=["w0", "w1", "w2"],
            relation=[("w0", "w1"), ("w1", "w2")],
        )
        valid_4_fail, _, _ = is_frame_valid(frame_not_trans, axiom_4())
        self.assertFalse(valid_4_fail)

        # Axiom B valid on symmetric frame, invalid on non-symmetric frame
        frame_sym = KripkeFrame(worlds=["w0", "w1"], relation=[("w0", "w1"), ("w1", "w0")])
        valid_b, _, _ = is_frame_valid(frame_sym, axiom_b())
        self.assertTrue(valid_b)

        frame_asym = KripkeFrame(worlds=["w0", "w1"], relation=[("w0", "w1")])
        valid_b_fail, _, _ = is_frame_valid(frame_asym, axiom_b())
        self.assertFalse(valid_b_fail)


if __name__ == "__main__":
    unittest.main()
