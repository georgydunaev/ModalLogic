#!/usr/bin/env python3
"""Unit tests for labeled semantic tableau solver and countermodel extraction."""

import os
import sys
import unittest

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
if ROOT not in sys.path:
    sys.path.insert(0, ROOT)

from modallogic.syntax import parse_formula
from modallogic.tableau import TableauSolver


class TestModalLogicTableau(unittest.TestCase):
    def test_propositional_theorems(self):
        solver = TableauSolver(system="K")
        tautologies = [
            "p | ~p",
            "p -> (q -> p)",
            "(p -> q) -> (~q -> ~p)",
            "(p & (p -> q)) -> q",
            "~(p & ~p)",
        ]
        for s in tautologies:
            phi = parse_formula(s)
            res = solver.check_validity(phi)
            self.assertTrue(res.is_valid, f"Expected propositional theorem: {s}")

    def test_system_k_validity_and_countermodels(self):
        solver_k = TableauSolver(system="K")

        # Axiom K
        res_k = solver_k.check_validity(parse_formula("[](p -> q) -> ([]p -> []q)"))
        self.assertTrue(res_k.is_valid)

        # Distribution of Box over conjunction
        res_box_and = solver_k.check_validity(parse_formula("[](p & q) <-> ([]p & []q)"))
        self.assertTrue(res_box_and.is_valid)

        # Distribution of Dia over disjunction
        res_dia_or = solver_k.check_validity(parse_formula("<>(p | q) <-> (<>p | <>q)"))
        self.assertTrue(res_dia_or.is_valid)

        # Axiom T is NOT valid in K
        res_t_in_k = solver_k.check_validity(parse_formula("[]p -> p"))
        self.assertFalse(res_t_in_k.is_valid)
        self.assertIsNotNone(res_t_in_k.countermodel)
        # Verify the countermodel actually falsifies the formula
        cm = res_t_in_k.countermodel
        cw = res_t_in_k.counterworld
        self.assertFalse(cm.satisfies(cw, parse_formula("[]p -> p")))

    def test_system_t_validity_and_countermodels(self):
        solver_t = TableauSolver(system="T")

        # Axiom T is valid in T
        res_t = solver_t.check_validity(parse_formula("[]p -> p"))
        self.assertTrue(res_t.is_valid)

        # Dual p -> <>p is valid in T
        res_dual_t = solver_t.check_validity(parse_formula("p -> <>p"))
        self.assertTrue(res_dual_t.is_valid)

        # Axiom 4 ([]p -> [][]p) is NOT valid in T
        res_4_in_t = solver_t.check_validity(parse_formula("[]p -> [][]p"))
        self.assertFalse(res_4_in_t.is_valid)
        self.assertIsNotNone(res_4_in_t.countermodel)

    def test_system_s4_validity_and_countermodels(self):
        solver_s4 = TableauSolver(system="S4")

        # Axiom 4 is valid in S4
        res_4 = solver_s4.check_validity(parse_formula("[]p -> [][]p"))
        self.assertTrue(res_4.is_valid)

        # Axiom T is also valid in S4
        res_t = solver_s4.check_validity(parse_formula("[]p -> p"))
        self.assertTrue(res_t.is_valid)

        # Axiom 5 (<>p -> []<>p) is NOT valid in S4
        res_5_in_s4 = solver_s4.check_validity(parse_formula("<>p -> []<>p"))
        self.assertFalse(res_5_in_s4.is_valid)
        self.assertIsNotNone(res_5_in_s4.countermodel)

    def test_system_s5_validity(self):
        solver_s5 = TableauSolver(system="S5")

        # Axiom 5 is valid in S5
        res_5 = solver_s5.check_validity(parse_formula("<>p -> []<>p"))
        self.assertTrue(res_5.is_valid)

        # Brouwerian axiom (B): p -> []<>p is valid in S5
        res_b = solver_s5.check_validity(parse_formula("p -> []<>p"))
        self.assertTrue(res_b.is_valid)

        # Modal collapse of double modalities: <>[]p -> []p
        res_collapse = solver_s5.check_validity(parse_formula("[]<>p <-> <>p"))
        self.assertTrue(res_collapse.is_valid)


if __name__ == "__main__":
    unittest.main()
