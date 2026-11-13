#!/usr/bin/env python3
"""Unit tests for standardized modal box and diamond distribution tactics, canonical models, and proof rules."""

import os
import sys
import unittest

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
if ROOT not in sys.path:
    sys.path.insert(0, ROOT)

from modallogic.syntax import parse_formula, Box, Dia, And, Or, Atom, Implies, Iff, Top
from modallogic.tableau import TableauSolver
from modallogic.tactics import (
    distribute_box_and,
    distribute_dia_or,
    factor_box_and,
    factor_dia_or,
    normalize_modal_distributions,
    box_and_distribution_schema,
    dia_or_distribution_schema,
    k_implication_distribution_schema,
    dia_implication_distribution_schema,
    s4_deduction_schema,
    s5_modal_collapse_schema,
    gl_provability_schema,
    ModalDeduction,
    prove_box_and_distribution,
    prove_dia_or_distribution,
    prove_s4_preorder_theorems,
    prove_s5_modal_collapse,
    prove_gl_transitivity,
)
from modallogic.canonical import (
    SubformulaClosure,
    CanonicalModel,
    construct_canonical_model,
    compute_subformulas,
)


class TestTacticsAndCanonicalModels(unittest.TestCase):
    def test_box_and_distribution_tactics(self):
        f = parse_formula("[](p & q)")
        dist = distribute_box_and(f)
        self.assertEqual(dist, parse_formula("[]p & []q"))

        # Factor back
        factored = factor_box_and(dist)
        self.assertEqual(factored, f)

        # Nested distribution
        f_nested = parse_formula("[](p & (q & r))")
        dist_nested = distribute_box_and(f_nested)
        self.assertEqual(dist_nested, parse_formula("[]p & ([]q & []r)"))

    def test_dia_or_distribution_tactics(self):
        f = parse_formula("<>(p | q)")
        dist = distribute_dia_or(f)
        self.assertEqual(dist, parse_formula("<>p | <>q"))

        # Factor back
        factored = factor_dia_or(dist)
        self.assertEqual(factored, f)

        # Nested distribution
        f_nested = parse_formula("<>(p | (q | r))")
        dist_nested = distribute_dia_or(f_nested)
        self.assertEqual(dist_nested, parse_formula("<>p | (<>q | <>r)"))

    def test_normalize_modal_distributions(self):
        complex_formula = parse_formula("[](p & q) -> <>(r | s)")
        normalized = normalize_modal_distributions(complex_formula)
        expected = parse_formula("([]p & []q) -> (<>r | <>s)")
        self.assertEqual(normalized, expected)

    def test_distribution_theorems_validity(self):
        # Axiom schemas must be valid in base system K
        solver_k = TableauSolver(system="K")

        th_box_and = box_and_distribution_schema()
        self.assertTrue(solver_k.check_validity(th_box_and).is_valid)

        th_dia_or = dia_or_distribution_schema()
        self.assertTrue(solver_k.check_validity(th_dia_or).is_valid)

        th_k = k_implication_distribution_schema()
        self.assertTrue(solver_k.check_validity(th_k).is_valid)

        th_dia_impl = dia_implication_distribution_schema()
        self.assertTrue(solver_k.check_validity(th_dia_impl).is_valid)

    def test_system_specific_deduction_schemas(self):
        solver_s4 = TableauSolver(system="S4")
        th_s4 = s4_deduction_schema()
        self.assertTrue(solver_s4.check_validity(th_s4).is_valid)

        solver_s5 = TableauSolver(system="S5")
        th_s5 = s5_modal_collapse_schema()
        self.assertTrue(solver_s5.check_validity(th_s5).is_valid)

        solver_gl = TableauSolver(system="GL")
        th_gl = gl_provability_schema()
        self.assertTrue(solver_gl.check_validity(th_gl).is_valid)

    def test_standardized_proof_deductions(self):
        # 1. Box conjunction distribution deduction
        ded_box = prove_box_and_distribution("K")
        self.assertTrue(ded_box.verify())
        self.assertIsNotNone(ded_box.conclusion)
        formatted_box = ded_box.format_proof()
        self.assertIn("Deduction for Box Conjunction Distribution", formatted_box)

        # 2. Diamond disjunction distribution deduction
        ded_dia = prove_dia_or_distribution("K")
        self.assertTrue(ded_dia.verify())

        # 3. S4 preorder deduction
        ded_s4 = prove_s4_preorder_theorems()
        self.assertTrue(ded_s4.verify())

        # 4. S5 modal collapse deduction
        ded_s5 = prove_s5_modal_collapse()
        self.assertTrue(ded_s5.verify())

        # 5. GL transitivity theorem deduction
        ded_gl = prove_gl_transitivity()
        self.assertTrue(ded_gl.verify())

    def test_subformula_closure(self):
        phi = parse_formula("[](p -> q)")
        closure = SubformulaClosure([phi])
        self.assertIn(phi, closure)
        self.assertIn(parse_formula("p -> q"), closure)
        self.assertIn(Atom("p"), closure)
        self.assertIn(Atom("q"), closure)
        self.assertIn(Top(), closure)

    def test_canonical_model_construction_and_evaluation_k(self):
        phi = parse_formula("p & q")
        model = construct_canonical_model([phi], system="K")
        self.assertIsInstance(model, CanonicalModel)
        self.assertGreater(len(model.worlds), 0)

        # Check Truth Lemma
        truth_rep = model.verify_truth_lemma()
        self.assertTrue(truth_rep["truth_lemma_holds"])

    def test_canonical_model_s4_frame_properties(self):
        phi = parse_formula("[]p -> p")
        model_s4 = construct_canonical_model([phi], system="S4")
        rep_s4 = model_s4.verify_frame_conditions()
        self.assertTrue(rep_s4["is_valid"])
        self.assertTrue(rep_s4["reflexive"])
        self.assertTrue(rep_s4["transitive"])

    def test_canonical_model_s5_frame_properties(self):
        phi = parse_formula("<>p -> []<>p")
        model_s5 = construct_canonical_model([phi], system="S5")
        rep_s5 = model_s5.verify_frame_conditions()
        self.assertTrue(rep_s5["is_valid"])
        self.assertTrue(rep_s5["reflexive"])
        self.assertTrue(rep_s5["transitive"])
        self.assertTrue(rep_s5["symmetric"])

    def test_canonical_model_gl_frame_properties(self):
        phi = parse_formula("[]( []p -> p ) -> []p")
        model_gl = construct_canonical_model([phi], system="GL")
        rep_gl = model_gl.verify_frame_conditions()
        self.assertTrue(rep_gl["is_valid"])
        self.assertTrue(rep_gl["transitive"])
        self.assertTrue(rep_gl["converse_well_founded"])


if __name__ == "__main__":
    unittest.main()
