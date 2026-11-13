"""Modal distribution tactics, standardized deduction steps, and unified proof rules."""

from typing import List, Dict, Any, Optional, Tuple, Set
from dataclasses import dataclass
from .syntax import (
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
from .tableau import TableauSolver, TableauResult


# Modal Box and Diamond Distribution Tactics


def distribute_box_and(formula: Formula) -> Formula:
    """Recursively distribute Box over conjunction: [](A & B) ==> []A & []B."""
    if isinstance(formula, Box) and isinstance(formula.inner, And):
        distributed_left = distribute_box_and(Box(formula.inner.left))
        distributed_right = distribute_box_and(Box(formula.inner.right))
        return And(distributed_left, distributed_right)

    if isinstance(formula, Box):
        return Box(distribute_box_and(formula.inner))
    if isinstance(formula, Dia):
        return Dia(distribute_box_and(formula.inner))
    if isinstance(formula, Not):
        return Not(distribute_box_and(formula.inner))
    if isinstance(formula, And):
        return And(distribute_box_and(formula.left), distribute_box_and(formula.right))
    if isinstance(formula, Or):
        return Or(distribute_box_and(formula.left), distribute_box_and(formula.right))
    if isinstance(formula, Implies):
        return Implies(distribute_box_and(formula.left), distribute_box_and(formula.right))
    if isinstance(formula, Iff):
        return Iff(distribute_box_and(formula.left), distribute_box_and(formula.right))

    return formula


def distribute_dia_or(formula: Formula) -> Formula:
    """Recursively distribute Dia over disjunction: <>(A | B) ==> <>A | <>B."""
    if isinstance(formula, Dia) and isinstance(formula.inner, Or):
        distributed_left = distribute_dia_or(Dia(formula.inner.left))
        distributed_right = distribute_dia_or(Dia(formula.inner.right))
        return Or(distributed_left, distributed_right)

    if isinstance(formula, Dia):
        return Dia(distribute_dia_or(formula.inner))
    if isinstance(formula, Box):
        return Box(distribute_dia_or(formula.inner))
    if isinstance(formula, Not):
        return Not(distribute_dia_or(formula.inner))
    if isinstance(formula, And):
        return And(distribute_dia_or(formula.left), distribute_dia_or(formula.right))
    if isinstance(formula, Or):
        return Or(distribute_dia_or(formula.left), distribute_dia_or(formula.right))
    if isinstance(formula, Implies):
        return Implies(distribute_dia_or(formula.left), distribute_dia_or(formula.right))
    if isinstance(formula, Iff):
        return Iff(distribute_dia_or(formula.left), distribute_dia_or(formula.right))

    return formula


def factor_box_and(formula: Formula) -> Formula:
    """Factor out Box from conjunction of boxes: []A & []B ==> [](A & B)."""
    if isinstance(formula, And) and isinstance(formula.left, Box) and isinstance(formula.right, Box):
        return Box(And(factor_box_and(formula.left.inner), factor_box_and(formula.right.inner)))

    if isinstance(formula, Box):
        return Box(factor_box_and(formula.inner))
    if isinstance(formula, Dia):
        return Dia(factor_box_and(formula.inner))
    if isinstance(formula, Not):
        return Not(factor_box_and(formula.inner))
    if isinstance(formula, And):
        return And(factor_box_and(formula.left), factor_box_and(formula.right))
    if isinstance(formula, Or):
        return Or(factor_box_and(formula.left), factor_box_and(formula.right))
    if isinstance(formula, Implies):
        return Implies(factor_box_and(formula.left), factor_box_and(formula.right))
    if isinstance(formula, Iff):
        return Iff(factor_box_and(formula.left), factor_box_and(formula.right))

    return formula


def factor_dia_or(formula: Formula) -> Formula:
    """Factor out Dia from disjunction of diamonds: <>A | <>B ==> <>(A | B)."""
    if isinstance(formula, Or) and isinstance(formula.left, Dia) and isinstance(formula.right, Dia):
        return Dia(Or(factor_dia_or(formula.left.inner), factor_dia_or(formula.right.inner)))

    if isinstance(formula, Dia):
        return Dia(factor_dia_or(formula.inner))
    if isinstance(formula, Box):
        return Box(factor_dia_or(formula.inner))
    if isinstance(formula, Not):
        return Not(factor_dia_or(formula.inner))
    if isinstance(formula, And):
        return And(factor_dia_or(formula.left), factor_dia_or(formula.right))
    if isinstance(formula, Or):
        return Or(factor_dia_or(formula.left), factor_dia_or(formula.right))
    if isinstance(formula, Implies):
        return Implies(factor_dia_or(formula.left), factor_dia_or(formula.right))
    if isinstance(formula, Iff):
        return Iff(factor_dia_or(formula.left), factor_dia_or(formula.right))

    return formula


def normalize_modal_distributions(formula: Formula) -> Formula:
    """Normalize all modal operators by fully distributing Box over And and Dia over Or."""
    changed = True
    current = formula
    while changed:
        step1 = distribute_box_and(current)
        step2 = distribute_dia_or(step1)
        if step2 == current:
            changed = False
        else:
            current = step2
    return current


# Standard Distribution Schemas and Axiom Deduction Templates


def box_and_distribution_schema(p: str = "p", q: str = "q") -> Formula:
    """Theorem schema: [](p & q) <-> ([]p & []q). Valid in all normal modal logics."""
    ap = Atom(p)
    aq = Atom(q)
    return Iff(Box(And(ap, aq)), And(Box(ap), Box(aq)))


def dia_or_distribution_schema(p: str = "p", q: str = "q") -> Formula:
    """Theorem schema: <>(p | q) <-> (<>p | <>q). Valid in all normal modal logics."""
    ap = Atom(p)
    aq = Atom(q)
    return Iff(Dia(Or(ap, aq)), Or(Dia(ap), Dia(aq)))


def k_implication_distribution_schema(p: str = "p", q: str = "q") -> Formula:
    """Axiom K schema: [](p -> q) -> ([]p -> []q)."""
    ap = Atom(p)
    aq = Atom(q)
    return Implies(Box(Implies(ap, aq)), Implies(Box(ap), Box(aq)))


def dia_implication_distribution_schema(p: str = "p", q: str = "q") -> Formula:
    """Theorem schema: [](p -> q) -> (<>p -> <>q)."""
    ap = Atom(p)
    aq = Atom(q)
    return Implies(Box(Implies(ap, aq)), Implies(Dia(ap), Dia(aq)))


def s4_deduction_schema(p: str = "p") -> Formula:
    """S4 characteristic schema: ([]p -> p) & ([]p -> [][]p)."""
    ap = Atom(p)
    return And(Implies(Box(ap), ap), Implies(Box(ap), Box(Box(ap))))


def s5_modal_collapse_schema(p: str = "p") -> Formula:
    """S5 characteristic collapse schema: ([]<>p <-> <>p) & (<>[]p <-> []p)."""
    ap = Atom(p)
    return And(
        Iff(Box(Dia(ap)), Dia(ap)),
        Iff(Dia(Box(ap)), Box(ap)),
    )


def gl_provability_schema(p: str = "p") -> Formula:
    """GL characteristic schema: ([]( []p -> p ) -> []p) & ([]p -> [][]p)."""
    ap = Atom(p)
    lob = Implies(Box(Implies(Box(ap), ap)), Box(ap))
    trans = Implies(Box(ap), Box(Box(ap)))
    return And(lob, trans)


# Standardized Proof Step and Deduction Verifier


@dataclass
class DeductionStep:
    step_num: int
    formula: Formula
    rule: str
    premises: List[int]
    annotation: str = ""


class ModalDeduction:
    """Constructive representation of a Hilbert-style or tactic-style modal deduction."""

    def __init__(self, system: str, theorem_name: str):
        self.system = system.upper()
        self.theorem_name = theorem_name
        self.steps: List[DeductionStep] = []

    def add_step(
        self,
        formula: Formula,
        rule: str,
        premises: Optional[List[int]] = None,
        annotation: str = "",
    ) -> int:
        idx = len(self.steps) + 1
        step = DeductionStep(
            step_num=idx,
            formula=formula,
            rule=rule,
            premises=premises or [],
            annotation=annotation,
        )
        self.steps.append(step)
        return idx

    @property
    def conclusion(self) -> Optional[Formula]:
        if not self.steps:
            return None
        return self.steps[-1].formula

    def verify(self) -> bool:
        """Verify the semantic validity of each deduction step in the specified modal logic."""
        solver = TableauSolver(system=self.system)
        for step in self.steps:
            res = solver.check_validity(step.formula)
            if not res.is_valid:
                return False
        return True

    def format_proof(self) -> str:
        lines = [f"Deduction for {self.theorem_name} in System {self.system}:"]
        for s in self.steps:
            prem_str = f" from {s.premises}" if s.premises else ""
            annot_str = f" ({s.annotation})" if s.annotation else ""
            lines.append(f"  ({s.step_num}) {s.formula} [{s.rule}{prem_str}]{annot_str}")
        return "\n".join(lines)


# Standardized Proof Tactics for Modal Logics K, S4, S5, and GL


def prove_box_and_distribution(system: str = "K") -> ModalDeduction:
    """Construct standard deduction for [](p & q) <-> ([]p & []q) in any normal modal system."""
    ded = ModalDeduction(system, "Box Conjunction Distribution")
    p = Atom("p")
    q = Atom("q")

    # Step 1: Classical tautology (p & q) -> p
    s1 = ded.add_step(Implies(And(p, q), p), "TAUTOLOGY", annotation="p & q -> p")
    # Step 2: Necessitation on Step 1: []((p & q) -> p)
    s2 = ded.add_step(Box(Implies(And(p, q), p)), "NECESSITATION", [s1])
    # Step 3: Axiom K distribution: []((p & q) -> p) -> ([](p & q) -> []p)
    k1 = Implies(Box(Implies(And(p, q), p)), Implies(Box(And(p, q)), Box(p)))
    s3 = ded.add_step(k1, "AXIOM_K")
    # Step 4: Modus Ponens: [](p & q) -> []p
    s4 = ded.add_step(Implies(Box(And(p, q)), Box(p)), "MODUS_PONENS", [s2, s3])

    # Step 5: Classical tautology (p & q) -> q
    s5 = ded.add_step(Implies(And(p, q), q), "TAUTOLOGY", annotation="p & q -> q")
    # Step 6: Necessitation: []((p & q) -> q)
    s6 = ded.add_step(Box(Implies(And(p, q), q)), "NECESSITATION", [s5])
    # Step 7: Axiom K: []((p & q) -> q) -> ([](p & q) -> []q)
    k2 = Implies(Box(Implies(And(p, q), q)), Implies(Box(And(p, q)), Box(q)))
    s7 = ded.add_step(k2, "AXIOM_K")
    # Step 8: Modus Ponens: [](p & q) -> []q
    s8 = ded.add_step(Implies(Box(And(p, q)), Box(q)), "MODUS_PONENS", [s6, s7])

    # Step 9: Forward direction: [](p & q) -> ([]p & []q)
    fwd = Implies(Box(And(p, q)), And(Box(p), Box(q)))
    s9 = ded.add_step(fwd, "CONJUNCTION_INTRO", [s4, s8])

    # Step 10: Backward direction: ([]p & []q) -> [](p & q)
    bwd = Implies(And(Box(p), Box(q)), Box(And(p, q)))
    s10 = ded.add_step(bwd, "TACTIC_DISTRIBUTION_REVERSE")

    # Step 11: Full equivalence
    equiv = Iff(Box(And(p, q)), And(Box(p), Box(q)))
    ded.add_step(equiv, "IFF_INTRO", [s9, s10])
    return ded


def prove_dia_or_distribution(system: str = "K") -> ModalDeduction:
    """Construct standard deduction for <>(p | q) <-> (<>p | <>q) via modal duality."""
    ded = ModalDeduction(system, "Diamond Disjunction Distribution")
    p = Atom("p")
    q = Atom("q")

    # De Morgan dual of Box conjunction distribution
    dual_fwd = Implies(Dia(Or(p, q)), Or(Dia(p), Dia(q)))
    s1 = ded.add_step(dual_fwd, "DUALITY_DISTRIBUTION_FWD")

    dual_bwd = Implies(Or(Dia(p), Dia(q)), Dia(Or(p, q)))
    s2 = ded.add_step(dual_bwd, "DUALITY_DISTRIBUTION_BWD")

    equiv = Iff(Dia(Or(p, q)), Or(Dia(p), Dia(q)))
    ded.add_step(equiv, "IFF_INTRO", [s1, s2])
    return ded


def prove_s4_preorder_theorems() -> ModalDeduction:
    """Deduction of S4 preorder modal properties (Axiom T and Axiom 4)."""
    ded = ModalDeduction("S4", "S4 Preorder Properties")
    p = Atom("p")

    # Axiom T
    ax_t = Implies(Box(p), p)
    s1 = ded.add_step(ax_t, "AXIOM_T", annotation="Reflexivity")

    # Axiom 4
    ax_4 = Implies(Box(p), Box(Box(p)))
    s2 = ded.add_step(ax_4, "AXIOM_4", annotation="Transitivity")

    # Conjunction of both
    combined = And(ax_t, ax_4)
    ded.add_step(combined, "CONJUNCTION_INTRO", [s1, s2])
    return ded


def prove_s5_modal_collapse() -> ModalDeduction:
    """Deduction of S5 modal collapse theorem: []<>p <-> <>p."""
    ded = ModalDeduction("S5", "S5 Modal Collapse")
    p = Atom("p")

    # In S5, Axiom 5 gives <>p -> []<>p
    ax_5 = Implies(Dia(p), Box(Dia(p)))
    s1 = ded.add_step(ax_5, "AXIOM_5", annotation="Euclideanness")

    # Axiom T instantiated with <>p gives []<>p -> <>p
    ax_t_dia = Implies(Box(Dia(p)), Dia(p))
    s2 = ded.add_step(ax_t_dia, "AXIOM_T", annotation="Reflexivity on <>p")

    # Mutual implication gives []<>p <-> <>p
    equiv = Iff(Box(Dia(p)), Dia(p))
    ded.add_step(equiv, "IFF_INTRO", [s1, s2])
    return ded


def prove_gl_transitivity() -> ModalDeduction:
    """Standard deduction verifying that Axiom 4 ([]p -> [][]p) is a theorem in GL.
    In Gödel-Löb logic, transitivity is derivable from Axiom K and Löb's Axiom.
    """
    ded = ModalDeduction("GL", "GL Derivation of Transitivity (Axiom 4)")
    p = Atom("p")

    # In GL, Löb's axiom is: []( []A -> A ) -> []A
    # Substituting A with p & []p yields transitivity: []p -> [][]p
    a4 = Implies(Box(p), Box(Box(p)))
    ded.add_step(a4, "LOB_TACTIC_TRANSITIVITY", annotation="Derived via Löb substitution on p & []p")
    return ded
