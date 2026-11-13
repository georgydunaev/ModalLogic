#!/usr/bin/env python3
"""Unit tests for Gödel-Löb Provability Logic (GL), frame conditions, and fixed-point algorithms."""

import os
import sys
import unittest

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
if ROOT not in sys.path:
    sys.path.insert(0, ROOT)

from modallogic.syntax import parse_formula, Box, Atom, Not, Bottom, Top, Implies, Iff
from modallogic.semantics import KripkeFrame, KripkeModel, is_frame_valid
from modallogic.provability import (
    axiom_gl,
    axiom_4,
    godel_second_incompleteness,
    is_transitive,
    is_converse_well_founded,
    is_gl_frame,
    gl_depth,
    gl_frame_height,
    substitute,
    is_modalized,
    simplify_constants,
    compute_fixed_point,
)
from modallogic.tableau import TableauSolver


class TestProvabilityLogicGL(unittest.TestCase):
    def test_gl_axioms_and_theorems_structure(self):
        gl = axiom_gl("p")
        self.assertIsInstance(gl, Implies)
        self.assertIn("p", gl.atoms())

        a4 = axiom_4("p")
        self.assertIsInstance(a4, Implies)

        g2 = godel_second_incompleteness()
        self.assertIsInstance(g2, Implies)

    def test_gl_frame_conditions_and_depth(self):
        # Strict linear order: w0 -> w1 -> w2 and w0 -> w2
        f_gl = KripkeFrame(
            worlds=["w0", "w1", "w2"],
            relation=[("w0", "w1"), ("w1", "w2"), ("w0", "w2")],
        )
        self.assertTrue(is_transitive(f_gl))
        self.assertTrue(is_converse_well_founded(f_gl))
        self.assertTrue(is_gl_frame(f_gl))

        # Check converse well-founded ranks:
        # w2 is a dead-end => rank 0
        # w1 sees w2 => rank 1
        # w0 sees w1 and w2 => rank 2
        self.assertEqual(gl_depth(f_gl, "w2"), 0)
        self.assertEqual(gl_depth(f_gl, "w1"), 1)
        self.assertEqual(gl_depth(f_gl, "w0"), 2)
        self.assertEqual(gl_frame_height(f_gl), 2)

        # Reflexive frame contains cycle w0 -> w0, hence NOT converse well-founded
        f_refl = KripkeFrame(worlds=["w0"], relation=[("w0", "w0")])
        self.assertFalse(is_converse_well_founded(f_refl))
        self.assertFalse(is_gl_frame(f_refl))
        with self.assertRaises(ValueError):
            gl_depth(f_refl, "w0")

    def test_is_modalized_checker(self):
        self.assertTrue(is_modalized(parse_formula("[]p"), "p"))
        self.assertTrue(is_modalized(parse_formula("<>p"), "p"))
        self.assertTrue(is_modalized(parse_formula("[](p -> q)"), "p"))
        self.assertTrue(is_modalized(parse_formula("[]p & []~p"), "p"))
        self.assertTrue(is_modalized(parse_formula("q -> r"), "p"))  # p does not occur

        # Non-modalized occurrences
        self.assertFalse(is_modalized(parse_formula("p"), "p"))
        self.assertFalse(is_modalized(parse_formula("p -> []p"), "p"))
        self.assertFalse(is_modalized(parse_formula("[]p & p"), "p"))

    def test_de_jongh_sambin_fixed_points(self):
        solver = TableauSolver(system="GL")

        # 1. Gödel Consistency sentence: A(p) = ~[]p
        # Fixed point H is ~[]BOT
        a_goedel = parse_formula("~[]p")
        h_goedel = compute_fixed_point(a_goedel, "p")
        # In GL, H <-> A(H) is valid
        equiv_goedel = Iff(h_goedel, substitute(a_goedel, "p", h_goedel))
        res_goedel = solver.check_validity(equiv_goedel)
        self.assertTrue(res_goedel.is_valid, "Gödel fixed point equivalence must be valid in GL")

        # 2. Henkin sentence: A(p) = []p
        # Fixed point H is TOP
        a_henkin = parse_formula("[]p")
        h_henkin = compute_fixed_point(a_henkin, "p")
        self.assertEqual(h_henkin, Top())
        equiv_henkin = Iff(h_henkin, substitute(a_henkin, "p", h_henkin))
        res_henkin = solver.check_validity(equiv_henkin)
        self.assertTrue(res_henkin.is_valid, "Henkin fixed point equivalence must be valid in GL")

        # 3. Refutable sentence: A(p) = []~p
        # Fixed point H is []BOT
        a_refute = parse_formula("[]~p")
        h_refute = compute_fixed_point(a_refute, "p")
        equiv_refute = Iff(h_refute, substitute(a_refute, "p", h_refute))
        res_refute = solver.check_validity(equiv_refute)
        self.assertTrue(res_refute.is_valid, "Refutable fixed point equivalence must be valid in GL")

        # 4. Implication sentence: A(p) = [](p -> q)
        a_impl = parse_formula("[](p -> q)")
        h_impl = compute_fixed_point(a_impl, "p")
        equiv_impl = Iff(h_impl, substitute(a_impl, "p", h_impl))
        res_impl = solver.check_validity(equiv_impl)
        self.assertTrue(res_impl.is_valid, "Implication fixed point equivalence must be valid in GL")

        # 5. Non-modalized formula raises ValueError
        with self.assertRaises(ValueError):
            compute_fixed_point(parse_formula("p & []p"), "p")

    def test_gl_tableau_decision_procedure(self):
        solver = TableauSolver(system="GL")

        # Löb's axiom is valid in GL
        res_gl = solver.check_validity(axiom_gl("p"))
        self.assertTrue(res_gl.is_valid)

        # Transitivity Axiom 4 ([]p -> [][]p) is a theorem in GL
        res_4 = solver.check_validity(axiom_4("p"))
        self.assertTrue(res_4.is_valid)

        # Gödel's Second Incompleteness Theorem (~[]BOT -> ~[]~[]BOT) is valid in GL
        res_g2 = solver.check_validity(godel_second_incompleteness())
        self.assertTrue(res_g2.is_valid)

        # Axiom T ([]p -> p) is NOT valid in GL
        res_t = solver.check_validity(parse_formula("[]p -> p"))
        self.assertFalse(res_t.is_valid)
        self.assertTrue(res_t.verify_countermodel(parse_formula("[]p -> p")))
        # Extracted frame must be transitive and converse well-founded (GL frame)
        self.assertTrue(res_t.countermodel.frame.is_gl_frame())

        # Consistency cannot be proven: []BOT is NOT valid in GL
        res_bot = solver.check_validity(parse_formula("[]BOT"))
        self.assertFalse(res_bot.is_valid)
        self.assertTrue(res_bot.verify_countermodel(parse_formula("[]BOT")))
        self.assertTrue(res_bot.countermodel.frame.is_gl_frame())


if __name__ == "__main__":
    unittest.main()
