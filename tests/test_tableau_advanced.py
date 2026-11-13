#!/usr/bin/env python3
"""Unit tests for advanced semantic tableau decision procedures, proof trees, and countermodels."""

import os
import sys
import unittest

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
if ROOT not in sys.path:
    sys.path.insert(0, ROOT)

from modallogic.syntax import parse_formula
from modallogic.tableau import TableauSolver, TableauResult, TableauProofNode


class TestTableauAdvanced(unittest.TestCase):
    def test_constructive_proof_tree_generation(self):
        solver = TableauSolver(system="K")
        phi = parse_formula("[](p & q) -> ([]p & []q)")
        res = solver.check_validity(phi)

        self.assertTrue(res.is_valid)
        self.assertIsNotNone(res.proof_tree)
        self.assertIsInstance(res.proof_tree, TableauProofNode)
        self.assertTrue(res.proof_tree.closed)

        # Check formatted proof text
        proof_str = res.format_proof()
        self.assertIn("[Node", proof_str)
        self.assertIn("CLOSED", proof_str)

    def test_system_k_countermodel_verification(self):
        solver = TableauSolver(system="K")
        # Axiom T is invalid in K
        phi = parse_formula("[]p -> p")
        res = solver.check_validity(phi)
        self.assertFalse(res.is_valid)
        self.assertTrue(res.verify_countermodel(phi))
        self.assertFalse(res.countermodel.satisfies(res.counterworld, phi))

    def test_system_t_countermodel_verification(self):
        solver = TableauSolver(system="T")
        # Axiom 4 is invalid in T
        phi = parse_formula("[]p -> [][]p")
        res = solver.check_validity(phi)
        self.assertFalse(res.is_valid)
        self.assertTrue(res.verify_countermodel(phi))
        # Frame must be reflexive
        self.assertTrue(res.countermodel.frame.is_reflexive())

    def test_system_s4_countermodel_verification(self):
        solver = TableauSolver(system="S4")
        # Axiom 5 (<>p -> []<>p) is invalid in S4
        phi = parse_formula("<>p -> []<>p")
        res = solver.check_validity(phi)
        self.assertFalse(res.is_valid)
        self.assertTrue(res.verify_countermodel(phi))
        # Frame must be S4 (reflexive and transitive)
        self.assertTrue(res.countermodel.frame.is_s4_frame())

    def test_system_s5_countermodel_verification(self):
        solver = TableauSolver(system="S5")
        # Contingent formula p is invalid in S5
        phi = parse_formula("[]p | []~p")
        res = solver.check_validity(phi)
        self.assertFalse(res.is_valid)
        self.assertTrue(res.verify_countermodel(phi))
        # Frame must be an equivalence relation
        self.assertTrue(res.countermodel.frame.is_s5_frame())

    def test_system_gl_countermodel_verification(self):
        solver = TableauSolver(system="GL")
        # Reflexivity ([]p -> p) fails in GL
        phi = parse_formula("[]p -> p")
        res = solver.check_validity(phi)
        self.assertFalse(res.is_valid)
        self.assertTrue(res.verify_countermodel(phi))
        # Frame must be a GL frame (transitive and converse well-founded)
        self.assertTrue(res.countermodel.frame.is_gl_frame())


if __name__ == "__main__":
    unittest.main()
