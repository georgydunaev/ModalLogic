#!/usr/bin/env python3
"""Unit tests for first-order standard translation (ST_x) and frame correspondence."""

import os
import sys
import unittest

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
if ROOT not in sys.path:
    sys.path.insert(0, ROOT)

from modallogic.syntax import (
    Formula,
    Atom,
    Top,
    Bottom,
    Not,
    And,
    Or,
    Implies,
    Iff,
    Box,
    Dia,
    parse_formula,
)
from modallogic.semantics import KripkeFrame, KripkeModel
from modallogic.fo_translation import (
    FOFormula,
    FOTop,
    FOBottom,
    Predicate,
    Relation,
    Equality,
    FONot,
    FOAnd,
    FOOr,
    FOImplies,
    FOIff,
    Forall,
    Exists,
    standard_translation,
    ST_x,
    st,
    evaluate_fo,
    fo_reflexive_condition,
    fo_symmetric_condition,
    fo_transitive_condition,
    fo_euclidean_condition,
    fo_serial_condition,
    fo_functional_condition,
    fo_confluent_condition,
)
from modallogic.correspondence import (
    check_functionality,
    check_partial_functionality,
    correspondence_theorem_cd,
    verify_frame_correspondence,
    is_positive,
    is_negative,
    is_sahlqvist_antecedent,
    is_sahlqvist,
    is_sahlqvist_formula,
    SahlqvistRecognizer,
    CANONICAL_FRAME_CONDITIONS,
    match_axiom_frame_condition,
    get_canonical_frame_condition,
)
from modallogic.frames import FunctionalFrame, CDFrame, FrameProperty
from modallogic.axioms import (
    axiom_t,
    axiom_b,
    axiom_4,
    axiom_5,
    axiom_d,
    axiom_cd,
    axiom_c4,
    axiom_gl,
    axiom_grz,
)


class TestFirstOrderTranslationAST(unittest.TestCase):
    """Test AST node construction, variable binding, complexity, and string formatting."""

    def test_fo_constants(self):
        top = FOTop()
        bot = FOBottom()
        self.assertEqual(top.free_variables(), set())
        self.assertEqual(bot.free_variables(), set())
        self.assertEqual(top.complexity(), 1)
        self.assertEqual(str(top), "TOP")
        self.assertEqual(str(bot), "BOTTOM")
        self.assertEqual(top.to_latex(), r"\top")
        self.assertEqual(bot.to_latex(), r"\bot")

    def test_fo_predicates_and_relations(self):
        p_x = Predicate("P", "x")
        r_xy = Relation("R", "x", "y")
        eq_yz = Equality("y", "z")

        self.assertEqual(p_x.free_variables(), {"x"})
        self.assertEqual(p_x.bound_variables(), set())
        self.assertEqual(r_xy.free_variables(), {"x", "y"})
        self.assertEqual(eq_yz.free_variables(), {"y", "z"})

        self.assertEqual(str(p_x), "P(x)")
        self.assertEqual(str(r_xy), "R(x, y)")
        self.assertEqual(str(eq_yz), "y = z")

    def test_fo_connectives_and_quantifiers(self):
        p_x = Predicate("P", "x")
        q_y = Predicate("Q", "y")
        r_xy = Relation("R", "x", "y")

        neg = FONot(p_x)
        self.assertEqual(neg.free_variables(), {"x"})
        self.assertEqual(str(neg), "~P(x)")

        conj = FOAnd(r_xy, q_y)
        self.assertEqual(conj.free_variables(), {"x", "y"})
        self.assertEqual(conj.to_string("standard"), "(R(x, y) /\\ Q(y))")
        self.assertEqual(conj.to_string("compact"), "(R(x, y) & Q(y))")

        disj = FOOr(p_x, q_y)
        self.assertEqual(disj.free_variables(), {"x", "y"})

        impl = FOImplies(r_xy, q_y)
        self.assertEqual(impl.free_variables(), {"x", "y"})
        self.assertEqual(impl.to_string("words"), "(R(x, y) implies Q(y))")

        quant_all = Forall("y", impl)
        self.assertEqual(quant_all.free_variables(), {"x"})
        self.assertEqual(quant_all.bound_variables(), {"y"})
        self.assertEqual(str(quant_all), "forall y. (R(x, y) -> Q(y))")

        quant_ex = Exists("y", conj)
        self.assertEqual(quant_ex.free_variables(), {"x"})
        self.assertEqual(quant_ex.bound_variables(), {"y"})
        self.assertEqual(str(quant_ex), "exists y. (R(x, y) /\\ Q(y))")

    def test_fo_operator_overloading(self):
        p = Predicate("P", "x")
        q = Predicate("Q", "x")
        and_node = p & q
        or_node = p | q
        not_node = ~p
        impl_node = p >> q

        self.assertIsInstance(and_node, FOAnd)
        self.assertIsInstance(or_node, FOOr)
        self.assertIsInstance(not_node, FONot)
        self.assertIsInstance(impl_node, FOImplies)


class TestStandardTranslationRules(unittest.TestCase):
    """Test van Benthem's Standard Translation ST_x from modal logic into FO^2."""

    def test_atomic_and_boolean_translation(self):
        p = Atom("p")
        st_p = standard_translation(p, "x")
        self.assertEqual(st_p, Predicate("P", "x"))
        self.assertEqual(st_p.free_variables(), {"x"})

        top_f = Top()
        self.assertIsInstance(standard_translation(top_f, "x"), FOTop)

        bot_f = Bottom()
        self.assertIsInstance(standard_translation(bot_f, "x"), FOBottom)

        not_p = Not(p)
        self.assertEqual(standard_translation(not_p, "x"), FONot(Predicate("P", "x")))

        and_pq = And(Atom("p"), Atom("q"))
        self.assertEqual(
            standard_translation(and_pq, "x"),
            FOAnd(Predicate("P", "x"), Predicate("Q", "x")),
        )

        or_pq = Or(Atom("p"), Atom("q"))
        self.assertEqual(
            standard_translation(or_pq, "x"),
            FOOr(Predicate("P", "x"), Predicate("Q", "x")),
        )

        impl_pq = Implies(Atom("p"), Atom("q"))
        self.assertEqual(
            standard_translation(impl_pq, "x"),
            FOImplies(Predicate("P", "x"), Predicate("Q", "x")),
        )

    def test_modal_operators_translation(self):
        # ST_x([]p) = forall y. (R(x, y) -> P(y))
        box_p = Box(Atom("p"))
        st_box = standard_translation(box_p, "x")
        expected_box = Forall("y", FOImplies(Relation("R", "x", "y"), Predicate("P", "y")))
        self.assertEqual(st_box, expected_box)
        self.assertEqual(st_box.free_variables(), {"x"})
        self.assertEqual(st_box.bound_variables(), {"y"})

        # ST_x(<>p) = exists y. (R(x, y) /\ P(y))
        dia_p = Dia(Atom("p"))
        st_dia = standard_translation(dia_p, "x")
        expected_dia = Exists("y", FOAnd(Relation("R", "x", "y"), Predicate("P", "y")))
        self.assertEqual(st_dia, expected_dia)
        self.assertEqual(st_dia.free_variables(), {"x"})
        self.assertEqual(st_dia.bound_variables(), {"y"})

    def test_two_variable_reutilization_nested_modalities(self):
        # ST_x([][]p): outer binds y, inner binds x -> strictly within FO^2
        box_box_p = Box(Box(Atom("p")))
        st_bb = standard_translation(box_box_p, "x")
        self.assertIsInstance(st_bb, Forall)
        self.assertEqual(st_bb.var, "y")
        inner_forall = st_bb.body.right  # type: ignore
        self.assertIsInstance(inner_forall, Forall)
        self.assertEqual(inner_forall.var, "x")
        self.assertEqual(inner_forall.body.right, Predicate("P", "x"))  # type: ignore
        # Total variables used is exactly {x, y}
        self.assertEqual(st_bb.variables(), {"x", "y"})

        # Aliases ST_x and st
        self.assertEqual(ST_x(box_p_formula := Box(Atom("p"))), standard_translation(box_p_formula))
        self.assertEqual(st(box_p_formula), standard_translation(box_p_formula))

    def test_custom_relation_and_initial_variable(self):
        p = Atom("p")
        st_custom = standard_translation(Box(p), var="w", rel_name="R1")
        self.assertIsInstance(st_custom, Forall)
        self.assertEqual(st_custom.var, "u")
        self.assertEqual(st_custom.body.left, Relation("R1", "w", "u"))  # type: ignore


class TestSemanticValidationAgainstKripkeModels(unittest.TestCase):
    """Validate van Benthem's theorem: (M, w) |= phi iff M |= ST_x(phi)[x |-> w]."""

    def setUp(self):
        # Construct diverse test frames and models
        # Frame 1: Linear chain w0 -> w1 -> w2
        self.f_chain = KripkeFrame(
            worlds=["w0", "w1", "w2"],
            relation=[("w0", "w1"), ("w1", "w2")],
        )
        self.m_chain = KripkeModel(
            self.f_chain,
            {"p": {"w1", "w2"}, "q": {"w2"}},
        )

        # Frame 2: Fork w0 -> w1, w0 -> w2, with reflexivity at w1
        self.f_fork = KripkeFrame(
            worlds=["w0", "w1", "w2"],
            relation=[("w0", "w1"), ("w0", "w2"), ("w1", "w1")],
        )
        self.m_fork = KripkeModel(
            self.f_fork,
            {"p": {"w1"}, "q": {"w1", "w2"}},
        )

        # Frame 3: Directed cycle w0 -> w1 -> w0
        self.f_cycle = KripkeFrame(
            worlds=["w0", "w1"],
            relation=[("w0", "w1"), ("w1", "w0")],
        )
        self.m_cycle = KripkeModel(
            self.f_cycle,
            {"p": {"w0"}},
        )

    def _verify_equivalence(self, model: KripkeModel, formula_str: str):
        phi = parse_formula(formula_str)
        st_phi = standard_translation(phi, "x")
        for w in model.frame.worlds:
            kripke_val = model.satisfies(w, phi)
            fo_val = evaluate_fo(st_phi, model, {"x": w})
            self.assertEqual(
                kripke_val,
                fo_val,
                f"Mismatch for {formula_str!r} at world {w!r}: Kripke={kripke_val}, FO={fo_val}",
            )

    def test_semantic_equivalence_chain_model(self):
        formulas = [
            "p",
            "q",
            "~p",
            "p & q",
            "p | q",
            "p -> q",
            "[]p",
            "<>p",
            "[]q",
            "<>q",
            "[][]p",
            "<><>q",
            "[](p -> q)",
            "[](p -> q) -> ([]p -> []q)",
        ]
        for f_str in formulas:
            self._verify_equivalence(self.m_chain, f_str)

    def test_semantic_equivalence_fork_model(self):
        formulas = [
            "p",
            "q",
            "[]p",
            "<>p",
            "[]q",
            "<>q",
            "[]p -> p",
            "p -> []<>p",
            "<>p -> []p",
            "[]p -> <>p",
        ]
        for f_str in formulas:
            self._verify_equivalence(self.m_fork, f_str)

    def test_semantic_equivalence_cycle_model(self):
        formulas = [
            "p",
            "~p",
            "[]p",
            "<>p",
            "[][]p",
            "<><>p",
            "[]<>p",
            "<>[]p",
            "[]p -> [][]p",
        ]
        for f_str in formulas:
            self._verify_equivalence(self.m_cycle, f_str)


class TestCanonicalFOFrameConditions(unittest.TestCase):
    """Test evaluation of canonical first-order frame conditions."""

    def test_reflexive_condition(self):
        fo_cond = fo_reflexive_condition()
        f_refl = KripkeFrame(worlds=["w0", "w1"], relation=[("w0", "w0"), ("w1", "w1")])
        f_non_refl = KripkeFrame(worlds=["w0", "w1"], relation=[("w0", "w0")])

        m_refl = KripkeModel(f_refl, {})
        m_non_refl = KripkeModel(f_non_refl, {})

        self.assertTrue(fo_cond.evaluate(m_refl, {}))
        self.assertFalse(fo_cond.evaluate(m_non_refl, {}))

    def test_symmetric_condition(self):
        fo_cond = fo_symmetric_condition()
        f_sym = KripkeFrame(worlds=["w0", "w1"], relation=[("w0", "w1"), ("w1", "w0")])
        f_non_sym = KripkeFrame(worlds=["w0", "w1"], relation=[("w0", "w1")])

        m_sym = KripkeModel(f_sym, {})
        m_non_sym = KripkeModel(f_non_sym, {})

        self.assertTrue(fo_cond.evaluate(m_sym, {}))
        self.assertFalse(fo_cond.evaluate(m_non_sym, {}))

    def test_transitive_condition(self):
        fo_cond = fo_transitive_condition()
        f_trans = KripkeFrame(
            worlds=["w0", "w1", "w2"],
            relation=[("w0", "w1"), ("w1", "w2"), ("w0", "w2")],
        )
        f_non_trans = KripkeFrame(
            worlds=["w0", "w1", "w2"],
            relation=[("w0", "w1"), ("w1", "w2")],
        )

        m_trans = KripkeModel(f_trans, {})
        m_non_trans = KripkeModel(f_non_trans, {})

        self.assertTrue(fo_cond.evaluate(m_trans, {}))
        self.assertFalse(fo_cond.evaluate(m_non_trans, {}))

    def test_functional_condition(self):
        fo_cond = fo_functional_condition()
        f_func = KripkeFrame(worlds=["w0", "w1"], relation=[("w0", "w1"), ("w1", "w1")])
        f_non_func = KripkeFrame(worlds=["w0", "w1", "w2"], relation=[("w0", "w1"), ("w0", "w2")])

        m_func = KripkeModel(f_func, {})
        m_non_func = KripkeModel(f_non_func, {})

        self.assertTrue(fo_cond.evaluate(m_func, {}))
        self.assertFalse(fo_cond.evaluate(m_non_func, {}))

    def test_serial_condition(self):
        fo_cond = fo_serial_condition()
        f_ser = KripkeFrame(worlds=["w0"], relation=[("w0", "w0")])
        f_non_ser = KripkeFrame(worlds=["w0"], relation=[])

        m_ser = KripkeModel(f_ser, {})
        m_non_ser = KripkeModel(f_non_ser, {})

        self.assertTrue(fo_cond.evaluate(m_ser, {}))
        self.assertFalse(fo_cond.evaluate(m_non_ser, {}))


class TestSahlqvistRecognizerAndCorrespondence(unittest.TestCase):
    """Test automated Sahlqvist formula recognizer and frame correspondence matching."""

    def test_polarity_analysis(self):
        # Positive formulas
        self.assertTrue(is_positive(Atom("p")))
        self.assertTrue(is_positive(Box(Atom("p"))))
        self.assertTrue(is_positive(Dia(Atom("p"))))
        self.assertTrue(is_positive(Not(Not(Atom("p")))))
        self.assertTrue(is_positive(Implies(Not(Atom("p")), Atom("q"))))

        # Negative formulas
        self.assertTrue(is_negative(Not(Atom("p"))))
        self.assertTrue(is_negative(Box(Not(Atom("p")))))
        self.assertTrue(is_negative(Dia(Not(Atom("p")))))
        self.assertTrue(is_negative(Implies(Atom("p"), Bottom())))

    def test_sahlqvist_antecedent_recognition(self):
        # Negative formulas are Sahlqvist antecedents
        self.assertTrue(is_sahlqvist_antecedent(Not(Atom("p"))))

        # Box^k(p) are Sahlqvist antecedents
        self.assertTrue(is_sahlqvist_antecedent(Atom("p")))
        self.assertTrue(is_sahlqvist_antecedent(Box(Atom("p"))))
        self.assertTrue(is_sahlqvist_antecedent(Box(Box(Atom("p")))))

        # Operations And, Or, Dia on Sahlqvist antecedents
        self.assertTrue(is_sahlqvist_antecedent(And(Box(Atom("p")), Box(Atom("q")))))
        self.assertTrue(is_sahlqvist_antecedent(Dia(Box(Atom("p")))))
        self.assertTrue(is_sahlqvist_antecedent(Or(Atom("p"), Not(Atom("q")))))

        # Non-Sahlqvist antecedents: Box over Dia, Box over implication
        self.assertFalse(is_sahlqvist_antecedent(Box(Dia(Atom("p")))))
        self.assertFalse(is_sahlqvist_antecedent(Box(Implies(Box(Atom("p")), Atom("p")))))

    def test_sahlqvist_classical_axioms_recognition(self):
        # All classical axioms (T, B, 4, 5, D, CD, C4) must be recognized as Sahlqvist
        classical_axioms = {
            "T": axiom_t(),
            "B": axiom_b(),
            "4": axiom_4(),
            "5": axiom_5(),
            "D": axiom_d(),
            "CD": axiom_cd(),
            "C4": axiom_c4(),
        }

        for name, ax in classical_axioms.items():
            self.assertTrue(
                is_sahlqvist(ax),
                f"Axiom {name} must be recognized as Sahlqvist formula",
            )
            analysis = SahlqvistRecognizer.analyze(ax)
            self.assertTrue(analysis["is_sahlqvist"])
            self.assertTrue(analysis["corresponds_to_first_order"])

    def test_non_sahlqvist_axioms_rejection(self):
        # Löb's Axiom GL, Grzegorczyk Grz, and McKinsey formula must be rejected
        gl = axiom_gl()
        grz = axiom_grz()
        mckinsey = parse_formula("[]<>p -> <>[]p")

        self.assertFalse(is_sahlqvist(gl), "Axiom GL is not Sahlqvist")
        self.assertFalse(is_sahlqvist(grz), "Axiom Grz is not Sahlqvist")
        self.assertFalse(is_sahlqvist(mckinsey), "McKinsey formula is not Sahlqvist")

        analysis_gl = SahlqvistRecognizer.analyze(gl)
        self.assertFalse(analysis_gl["is_sahlqvist"])
        self.assertFalse(analysis_gl["corresponds_to_first_order"])

    def test_canonical_frame_condition_matcher(self):
        # Match by axiom name
        for ax_name in ["T", "B", "4", "5", "D", "CD", "C4"]:
            entry = match_axiom_frame_condition(ax_name)
            self.assertIsNotNone(entry)
            self.assertEqual(entry["axiom_name"], ax_name)
            self.assertIn("property", entry)
            self.assertIn("fo_condition", entry)
            self.assertIn("fo_ast", entry)
            self.assertTrue(entry["is_sahlqvist"])

        # Match by formula AST (modulo variable renaming)
        entry_t = match_axiom_frame_condition(axiom_t("q"))
        self.assertIsNotNone(entry_t)
        self.assertEqual(entry_t["axiom_name"], "T")

        entry_cd = match_axiom_frame_condition(axiom_cd("psi"))
        self.assertIsNotNone(entry_cd)
        self.assertEqual(entry_cd["axiom_name"], "CD")
        self.assertEqual(entry_cd["property"], "functional")

    def test_axiom_cd_correspondence_and_functionality(self):
        # Functional frame: at most 1 successor
        f_func = KripkeFrame(worlds=["w0", "w1"], relation=[("w0", "w1"), ("w1", "w1")])
        is_func, wit_func = check_functionality(f_func)
        self.assertTrue(is_func)
        self.assertIsNone(wit_func)

        res_cd = correspondence_theorem_cd(f_func)
        self.assertTrue(res_cd["is_property_satisfied"])
        self.assertTrue(res_cd["is_axiom_valid"])
        self.assertTrue(verify_frame_correspondence(f_func, "CD"))

        # Non-functional frame: w0 sees w1 and w2
        f_non_func = KripkeFrame(
            worlds=["w0", "w1", "w2"],
            relation=[("w0", "w1"), ("w0", "w2")],
        )
        is_func2, wit_non_func = check_functionality(f_non_func)
        self.assertFalse(is_func2)
        self.assertEqual(wit_non_func[0], "w0")

        res_cd_invalid = correspondence_theorem_cd(f_non_func)
        self.assertFalse(res_cd_invalid["is_property_satisfied"])
        self.assertFalse(res_cd_invalid["is_axiom_valid"])
        # Verify constructive countermodel falsifies <>p -> []p at w0
        cm = res_cd_invalid["countermodel"]
        cw = res_cd_invalid["counterworld"]
        ax = res_cd_invalid["axiom"]
        self.assertFalse(cm.satisfies(cw, ax))
        self.assertTrue(verify_frame_correspondence(f_non_func, "CD"))

    def test_functional_frame_class_integration(self):
        f = CDFrame(worlds=["w0", "w1"], relation=[("w0", "w1"), ("w1", "w1")])
        self.assertTrue(f.is_functional())
        self.assertTrue(f.is_valid_frame())


if __name__ == "__main__":
    unittest.main()
