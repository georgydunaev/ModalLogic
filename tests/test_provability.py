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
    is_irreflexive,
    is_converse_well_founded,
    is_gl_frame,
    verify_gl_frame_condition,
    gl_depth,
    gl_frame_height,
    substitute,
    is_modalized,
    simplify_constants,
    compute_fixed_point,
    GLHilbertStep,
    GLHilbertProof,
    gl_hilbert_axioms,
    gl_derive_axiom_4,
    GLSequent,
    GLSequentNode,
    GLDecisionResult,
    GLDecisionProcedure,
    prove_gl,
    check_gl_validity,
    PASentence,
    PAAtom,
    PAEquation,
    PATrue,
    PAFalse,
    PANot,
    PAAnd,
    PAOr,
    PAImplies,
    PAIff,
    PAProvability,
    PAConsistency,
    ArithmeticalRealization,
    solovay_translation,
    solovay_derivability_conditions,
    solovay_goedel_second_incompleteness,
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

    def test_gl_hilbert_system_and_axiom_4_deduction(self):
        axioms = gl_hilbert_axioms("p", "q")
        self.assertIn("K", axioms)
        self.assertIn("LOB", axioms)

        # Verified derivation of Axiom 4 from Löb's axiom
        proof = gl_derive_axiom_4("p")
        self.assertEqual(len(proof.steps), 22)
        self.assertTrue(proof.verify(), "Hilbert proof must be formally verified")
        self.assertEqual(proof.conclusion, axiom_4("p"))

        # String representation covers steps
        proof_str = str(proof)
        self.assertIn("GL Derivation of Transitivity Axiom 4", proof_str)
        self.assertIn("22.", proof_str)

        # Test verification failure on corrupted proof step
        corrupt_proof = gl_derive_axiom_4("p")
        corrupt_proof.steps[0].formula = Atom("unprovable_atom")
        self.assertFalse(corrupt_proof.verify())

    def test_gl_frame_condition_diagnostics(self):
        # 1. Transitive, irreflexive, converse well-founded frame
        f_gl = KripkeFrame(
            worlds=["w0", "w1", "w2"],
            relation=[("w0", "w1"), ("w1", "w2"), ("w0", "w2")],
        )
        self.assertTrue(is_irreflexive(f_gl))
        self.assertTrue(is_transitive(f_gl))
        self.assertTrue(is_converse_well_founded(f_gl))
        is_gl, diags = verify_gl_frame_condition(f_gl)
        self.assertTrue(is_gl)
        self.assertEqual(len(diags), 0)

        # 2. Reflexive violation
        f_refl = KripkeFrame(worlds=["w0"], relation=[("w0", "w0")])
        self.assertFalse(is_irreflexive(f_refl))
        is_gl_refl, diags_refl = verify_gl_frame_condition(f_refl)
        self.assertFalse(is_gl_refl)
        self.assertTrue(any("Irreflexivity failure" in d for d in diags_refl))

        # 3. Transitivity violation
        f_nontrans = KripkeFrame(
            worlds=["w0", "w1", "w2"],
            relation=[("w0", "w1"), ("w1", "w2")],
        )
        self.assertFalse(is_transitive(f_nontrans))
        is_gl_trans, diags_trans = verify_gl_frame_condition(f_nontrans)
        self.assertFalse(is_gl_trans)
        self.assertTrue(any("Transitivity failure" in d for d in diags_trans))

        # 4. Cycle violation (e.g. 2-cycle)
        f_cycle = KripkeFrame(
            worlds=["w0", "w1"],
            relation=[("w0", "w1"), ("w1", "w0")],
        )
        self.assertFalse(is_converse_well_founded(f_cycle))
        is_gl_cyc, diags_cyc = verify_gl_frame_condition(f_cycle)
        self.assertFalse(is_gl_cyc)
        self.assertTrue(any("Converse well-foundedness failure" in d or "Transitivity failure" in d for d in diags_cyc))

    def test_terminating_sequent_decision_procedure_theorems(self):
        # 1. Löb's Axiom
        res_lob = prove_gl(axiom_gl("p"))
        self.assertTrue(res_lob.is_valid)
        self.assertIsNotNone(res_lob.proof_tree)
        self.assertTrue(res_lob.proof_tree.is_closed)

        # 2. Transitivity Axiom 4
        res_4 = prove_gl(axiom_4("p"))
        self.assertTrue(res_4.is_valid)

        # 3. Axiom K
        res_k = prove_gl(parse_formula("[](p -> q) -> ([]p -> []q)"))
        self.assertTrue(res_k.is_valid)

        # 4. Gödel's Second Incompleteness Theorem
        res_g2 = prove_gl(godel_second_incompleteness())
        self.assertTrue(res_g2.is_valid)

        # 5. Compound GL theorem: []p -> []([]q -> p)
        res_comp = prove_gl(parse_formula("[]p -> []([]q -> p)"))
        self.assertTrue(res_comp.is_valid)

        # 6. Distribution of box over conjunction
        res_and = check_gl_validity(parse_formula("[](p & q) <-> ([]p & []q)"))
        self.assertTrue(res_and.is_valid)

        # 7. Propositional tautology under modalities
        res_taut = check_gl_validity(parse_formula("[](p | ~p)"))
        self.assertTrue(res_taut.is_valid)

    def test_terminating_sequent_decision_procedure_countermodels(self):
        # 1. Axiom T ([]p -> p) fails in GL
        res_t = prove_gl(parse_formula("[]p -> p"))
        self.assertFalse(res_t.is_valid)
        self.assertIsNotNone(res_t.countermodel)
        self.assertTrue(res_t.verify_countermodel())
        self.assertTrue(res_t.countermodel.frame.is_gl_frame())
        self.assertTrue(res_t.countermodel.frame.is_irreflexive())

        # 2. Consistency theorem failure ([]BOT is unprovable)
        res_bot = prove_gl(parse_formula("[]BOT"))
        self.assertFalse(res_bot.is_valid)
        self.assertTrue(res_bot.verify_countermodel())
        self.assertTrue(res_bot.countermodel.frame.is_gl_frame())

        # 3. Symmetry Axiom B (p -> []<>p) fails in GL
        res_b = prove_gl(parse_formula("p -> []<>p"))
        self.assertFalse(res_b.is_valid)
        self.assertTrue(res_b.verify_countermodel())
        self.assertTrue(res_b.countermodel.frame.is_gl_frame())

        # 4. Euclidean Axiom 5 (<>p -> []<>p) fails in GL
        res_5 = prove_gl(parse_formula("<>p -> []<>p"))
        self.assertFalse(res_5.is_valid)
        self.assertTrue(res_5.verify_countermodel())
        self.assertTrue(res_5.countermodel.frame.is_gl_frame())

        # 5. Propositional non-theorem: p
        res_atom = prove_gl(Atom("p"))
        self.assertFalse(res_atom.is_valid)
        self.assertTrue(res_atom.verify_countermodel())

        # 6. Branching non-theorem: p | q -> p & q
        res_branch = prove_gl(parse_formula("(p | q) -> (p & q)"))
        self.assertFalse(res_branch.is_valid)
        self.assertTrue(res_branch.verify_countermodel())

        # 7. Modalized loop formula termination: []p <-> p
        res_loop = prove_gl(parse_formula("[]p <-> p"))
        self.assertFalse(res_loop.is_valid)
        self.assertTrue(res_loop.verify_countermodel())
        self.assertTrue(res_loop.countermodel.frame.is_gl_frame())

    def test_solovay_arithmetical_realization(self):
        # 1. Base translation of propositional and modal formulas
        f = parse_formula("[](p -> q) -> ([]p -> []q)")
        pa_f = solovay_translation(f)
        self.assertIsInstance(pa_f, PAImplies)
        self.assertIsInstance(pa_f.left, PAProvability)
        self.assertIsInstance(pa_f.right.left, PAProvability)
        self.assertIn("Prov_PA", str(pa_f))

        # 2. Constants translation
        f_const = parse_formula("TOP & ~BOT")
        pa_const = solovay_translation(f_const)
        self.assertIsInstance(pa_const, PAAnd)
        self.assertEqual(str(pa_const.left), "(0 = 0)")
        self.assertEqual(str(pa_const.right.inner), "(0 = 1)")

        # 3. Custom arithmetical realization mapping
        custom_realizer = ArithmeticalRealization(
            {
                "p": PAEquation("x", "0"),
                "q": PAEquation("y", "1"),
            }
        )
        pa_custom = solovay_translation(parse_formula("[]p -> q"), custom_realizer)
        self.assertEqual(str(pa_custom), "(Prov_PA([(x = 0)]) -> (y = 1))")

        # 4. Derivability conditions in PA
        d_conds = solovay_derivability_conditions()
        self.assertIn("D1", d_conds)
        self.assertIn("D2", d_conds)
        self.assertIn("D3", d_conds)
        self.assertIn("LOB", d_conds)
        self.assertIsInstance(d_conds["D1"], PAProvability)
        self.assertIsInstance(d_conds["LOB"], PAImplies)

        # 5. Gödel's Second Incompleteness Theorem under Solovay realization
        pa_g2 = solovay_goedel_second_incompleteness()
        self.assertIsInstance(pa_g2, PAImplies)
        self.assertEqual(str(pa_g2), "(~Prov_PA([(0 = 1)]) -> ~Prov_PA([~Prov_PA([(0 = 1)])]))")

        # 6. Consistency predicate representation
        consis_default = PAConsistency()
        self.assertEqual(str(consis_default), "Consis_PA")
        prov_equiv = consis_default.to_provability()
        self.assertIsInstance(prov_equiv, PANot)
        self.assertEqual(str(prov_equiv), "~Prov_PA([(0 = 1)])")

        consis_custom = PAConsistency(PAAtom("Theory"))
        self.assertEqual(str(consis_custom), "Consis_PA(Theory)")


if __name__ == "__main__":
    unittest.main()
