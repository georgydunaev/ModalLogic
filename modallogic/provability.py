"""Gödel-Löb Provability Logic (GL): Axioms, Kripke semantics, Hilbert deductions, terminating decision procedure, and Solovay arithmetical realization."""

from dataclasses import dataclass, field
from typing import Set, Tuple, Dict, Any, Optional, List, FrozenSet, Union
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
from .semantics import KripkeFrame, KripkeModel


def axiom_gl(p: str = "p") -> Formula:
    """Gödel-Löb Axiom schema: []( []p -> p ) -> []p.
    Corresponds to finite transitive converse well-founded Kripke frames.
    """
    ap = Atom(p)
    return Implies(Box(Implies(Box(ap), ap)), Box(ap))


def axiom_4(p: str = "p") -> Formula:
    """Transitivity axiom schema: []p -> [][]p.
    In GL, Axiom 4 is a theorem derivable from Axiom K and Löb's Axiom.
    """
    ap = Atom(p)
    return Implies(Box(ap), Box(Box(ap)))


def godel_second_incompleteness() -> Formula:
    """Gödel's Second Incompleteness Theorem in GL:
    ~[]BOT -> ~[]~[]BOT
    Consistency (~[]BOT) implies that consistency is unprovable (~[]~[]BOT).
    """
    cons = Not(Box(Bottom()))
    unprovable_cons = Not(Box(Not(Box(Bottom()))))
    return Implies(cons, unprovable_cons)


def is_transitive(frame: KripkeFrame) -> bool:
    """Verify whether the frame relation is transitive: forall u, v, w: u R v and v R w implies u R w."""
    return frame.is_transitive()


def is_converse_well_founded(frame: KripkeFrame) -> bool:
    """Verify whether the frame has no infinite ascending R-chains.
    On a finite frame, this is equivalent to having no directed cycles (strict DAG / acyclic).
    """
    return frame.is_converse_well_founded()


def is_gl_frame(frame: KripkeFrame) -> bool:
    """Verify whether the frame satisfies GL frame conditions: transitive and converse well-founded."""
    return frame.is_transitive() and frame.is_converse_well_founded()


def is_irreflexive(frame: KripkeFrame) -> bool:
    """Verify whether the frame relation is irreflexive: forall w in worlds: (w, w) not in relation.
    On finite transitive frames, irreflexivity is equivalent to converse well-foundedness (no cycles).
    """
    return frame.is_irreflexive()


def verify_gl_frame_condition(frame: KripkeFrame) -> Tuple[bool, List[str]]:
    """Verify whether the frame satisfies GL frame conditions: transitive and converse well-founded.
    Returns (is_gl, diagnostics).
    """
    diagnostics: List[str] = []
    # 1. Transitivity check
    for u in frame.worlds:
        for v in frame.successors(u):
            for w in frame.successors(v):
                if w not in frame.successors(u):
                    diagnostics.append(
                        f"Transitivity failure: ({u!r}, {v!r}) in R and ({v!r}, {w!r}) in R, but ({u!r}, {w!r}) not in R"
                    )
    # 2. Irreflexivity check
    for w in frame.worlds:
        if (w, w) in frame.relation:
            diagnostics.append(f"Irreflexivity failure: self-loop at world {w!r}")

    # 3. Converse well-foundedness / cycle check
    if not frame.is_converse_well_founded():
        diagnostics.append("Converse well-foundedness failure: relation contains directed cycles")

    is_gl = len(diagnostics) == 0
    return is_gl, diagnostics


def gl_depth(frame: KripkeFrame, world: Any) -> int:
    """Compute converse well-founded rank (depth) of a world in a finite GL frame.
    Dead-end worlds (no successors) have rank 0.
    A world with successors has rank 1 + max_{u in R(w)} rank(u).
    Raises ValueError if frame contains cycles.
    """
    if world not in frame.worlds:
        raise KeyError(f"World {world!r} not in frame")
    if not frame.is_converse_well_founded():
        raise ValueError("Frame is not converse well-founded (contains cycles)")

    memo: Dict[Any, int] = {}

    def _rank(w: Any) -> int:
        if w in memo:
            return memo[w]
        succ = frame.successors(w)
        if not succ:
            res = 0
        else:
            res = 1 + max(_rank(u) for u in succ)
        memo[w] = res
        return res

    return _rank(world)


def gl_frame_height(frame: KripkeFrame) -> int:
    """Compute the maximum converse well-founded depth across all worlds in frame."""
    if not frame.worlds:
        return 0
    return max(gl_depth(frame, w) for w in frame.worlds)


def substitute(formula: Formula, var_name: str, replacement: Formula) -> Formula:
    """Syntactically substitute all occurrences of propositional atom var_name with replacement formula."""
    if isinstance(formula, Atom):
        if formula.name == var_name:
            return replacement
        return formula
    if isinstance(formula, (Top, Bottom)):
        return formula
    if isinstance(formula, Not):
        return Not(substitute(formula.inner, var_name, replacement))
    if isinstance(formula, And):
        return And(
            substitute(formula.left, var_name, replacement),
            substitute(formula.right, var_name, replacement),
        )
    if isinstance(formula, Or):
        return Or(
            substitute(formula.left, var_name, replacement),
            substitute(formula.right, var_name, replacement),
        )
    if isinstance(formula, Implies):
        return Implies(
            substitute(formula.left, var_name, replacement),
            substitute(formula.right, var_name, replacement),
        )
    if isinstance(formula, Iff):
        return Iff(
            substitute(formula.left, var_name, replacement),
            substitute(formula.right, var_name, replacement),
        )
    if isinstance(formula, Box):
        return Box(substitute(formula.inner, var_name, replacement))
    if isinstance(formula, Dia):
        return Dia(substitute(formula.inner, var_name, replacement))
    raise TypeError(f"Unknown formula type in substitute: {type(formula)}")


def is_modalized(formula: Formula, var_name: str, in_box: bool = False) -> bool:
    """Check whether every occurrence of var_name in formula is modalized
    (i.e. occurs within the scope of at least one Box or Dia operator).
    """
    if isinstance(formula, Atom):
        if formula.name == var_name:
            return in_box
        return True
    if isinstance(formula, (Top, Bottom)):
        return True
    if isinstance(formula, Not):
        return is_modalized(formula.inner, var_name, in_box)
    if isinstance(formula, (And, Or, Implies, Iff)):
        return is_modalized(formula.left, var_name, in_box) and is_modalized(
            formula.right, var_name, in_box
        )
    if isinstance(formula, (Box, Dia)):
        return is_modalized(formula.inner, var_name, in_box=True)
    return True


def simplify_constants(formula: Formula) -> Formula:
    """Algebraic simplification of constant subformulas (Top, Bottom, Box(Top))."""
    if isinstance(formula, (Atom, Top, Bottom)):
        return formula
    if isinstance(formula, Not):
        inner = simplify_constants(formula.inner)
        if isinstance(inner, Top):
            return Bottom()
        if isinstance(inner, Bottom):
            return Top()
        if isinstance(inner, Not):
            return inner.inner
        return Not(inner)
    if isinstance(formula, And):
        l = simplify_constants(formula.left)
        r = simplify_constants(formula.right)
        if isinstance(l, Bottom) or isinstance(r, Bottom):
            return Bottom()
        if isinstance(l, Top):
            return r
        if isinstance(r, Top):
            return l
        if l == r:
            return l
        return And(l, r)
    if isinstance(formula, Or):
        l = simplify_constants(formula.left)
        r = simplify_constants(formula.right)
        if isinstance(l, Top) or isinstance(r, Top):
            return Top()
        if isinstance(l, Bottom):
            return r
        if isinstance(r, Bottom):
            return l
        if l == r:
            return l
        return Or(l, r)
    if isinstance(formula, Implies):
        l = simplify_constants(formula.left)
        r = simplify_constants(formula.right)
        if isinstance(l, Bottom):
            return Top()
        if isinstance(r, Top):
            return Top()
        if isinstance(l, Top):
            return r
        if isinstance(r, Bottom):
            return simplify_constants(Not(l))
        return Implies(l, r)
    if isinstance(formula, Iff):
        l = simplify_constants(formula.left)
        r = simplify_constants(formula.right)
        if l == r:
            return Top()
        return Iff(l, r)
    if isinstance(formula, Box):
        inner = simplify_constants(formula.inner)
        if isinstance(inner, Top):
            # []Top is a theorem in all normal modal logics
            return Top()
        return Box(inner)
    if isinstance(formula, Dia):
        inner = simplify_constants(formula.inner)
        if isinstance(inner, Bottom):
            return Bottom()
        return Dia(inner)
    return formula


def compute_fixed_point(formula: Formula, var_name: str = "p") -> Formula:
    """Compute the unique de Jongh-Sambin fixed point H such that GL |- H <-> A(H).
    The formula A(p) must be modalized in var_name (all occurrences of var_name under a modality).
    """
    if not is_modalized(formula, var_name):
        raise ValueError(
            f"Formula {formula} is not modalized in variable {var_name!r}: "
            "all occurrences of the variable must appear in the scope of Box or Dia."
        )

    if var_name not in formula.atoms():
        return formula

    # Sambin's algorithm for modalized formulas:
    # 1. Collect all boxed subformulas Box(B) containing var_name
    def _find_boxed_subformulas(f: Formula) -> List[Formula]:
        res = []
        if isinstance(f, (Box, Dia)) and var_name in f.inner.atoms():
            res.append(f)
        if isinstance(f, Not):
            res.extend(_find_boxed_subformulas(f.inner))
        elif isinstance(f, (And, Or, Implies, Iff)):
            res.extend(_find_boxed_subformulas(f.left))
            res.extend(_find_boxed_subformulas(f.right))
        elif isinstance(f, (Box, Dia)):
            res.extend(_find_boxed_subformulas(f.inner))
        return res

    boxed_list = _find_boxed_subformulas(formula)
    if not boxed_list:
        return formula

    # If single boxed subformula Box(B) or Dia(B)
    # Let A(p) = C(Box B(p)) where p only occurs in B
    # Let fresh atom q represent Box B(p)
    # C(q) = formula[Box B(p) -> q]
    # F(q) = B[p -> C(q)]
    # Fixed point is C(Box(F(Top)))
    target_box = boxed_list[0]
    is_dia = isinstance(target_box, Dia)
    inner_b = target_box.inner

    fresh_atom_name = f"_sambin_q_{len(formula.atoms())}"
    fresh_atom = Atom(fresh_atom_name)

    # C(q)
    c_q = substitute_subformula(formula, target_box, fresh_atom)
    # F(q) = inner_b[p -> C(q)]
    f_q = substitute(inner_b, var_name, c_q)
    # F(Top) = f_q[q -> Top]
    f_top = simplify_constants(substitute(f_q, fresh_atom_name, Top()))

    # Box(F(Top)) or Dia(F(Top))
    fixed_modality = Dia(f_top) if is_dia else Box(f_top)

    # Candidate fixed point: C(fixed_modality)
    cand = substitute(c_q, fresh_atom_name, fixed_modality)
    cand = simplify_constants(cand)

    # If any residual occurrences of var_name remain (e.g. nested boxes), recurse
    if var_name in cand.atoms():
        return compute_fixed_point(cand, var_name)

    return cand


def substitute_subformula(formula: Formula, target: Formula, replacement: Formula) -> Formula:
    """Replace occurrences of subformula target with replacement."""
    if formula == target:
        return replacement
    if isinstance(formula, (Atom, Top, Bottom)):
        return formula
    if isinstance(formula, Not):
        return Not(substitute_subformula(formula.inner, target, replacement))
    if isinstance(formula, And):
        return And(
            substitute_subformula(formula.left, target, replacement),
            substitute_subformula(formula.right, target, replacement),
        )
    if isinstance(formula, Or):
        return Or(
            substitute_subformula(formula.left, target, replacement),
            substitute_subformula(formula.right, target, replacement),
        )
    if isinstance(formula, Implies):
        return Implies(
            substitute_subformula(formula.left, target, replacement),
            substitute_subformula(formula.right, target, replacement),
        )
    if isinstance(formula, Iff):
        return Iff(
            substitute_subformula(formula.left, target, replacement),
            substitute_subformula(formula.right, target, replacement),
        )
    if isinstance(formula, Box):
        return Box(substitute_subformula(formula.inner, target, replacement))
    if isinstance(formula, Dia):
        return Dia(substitute_subformula(formula.inner, target, replacement))
    return formula


# ==============================================================================
# Hilbert Axiom System GL
# ==============================================================================

@dataclass
class GLHilbertStep:
    """A verified step in a Hilbert-style GL deduction."""

    step_number: int
    formula: Formula
    rule: str
    justification: str
    premises: Tuple[int, ...] = ()

    def __str__(self) -> str:
        prem = f" [{', '.join(str(p) for p in self.premises)}]" if self.premises else ""
        return f"{self.step_number}. {self.formula}  ({self.rule}{prem}: {self.justification})"


def is_propositional_tautology(formula: Formula) -> bool:
    """Check if formula is a substitution instance of a classical propositional tautology.
    Treats modal formulas (Box, Dia) as opaque propositional variables.
    """

    def _collect_components(f: Formula) -> Set[Formula]:
        if isinstance(f, (Atom, Box, Dia)):
            return {f}
        if isinstance(f, (Top, Bottom)):
            return set()
        if isinstance(f, Not):
            return _collect_components(f.inner)
        if isinstance(f, (And, Or, Implies, Iff)):
            return _collect_components(f.left) | _collect_components(f.right)
        return {f}

    components = list(_collect_components(formula))
    if len(components) > 12:
        return False

    def _eval(f: Formula, assignment: Dict[Formula, bool]) -> bool:
        if f in assignment:
            return assignment[f]
        if isinstance(f, Top):
            return True
        if isinstance(f, Bottom):
            return False
        if isinstance(f, Not):
            return not _eval(f.inner, assignment)
        if isinstance(f, And):
            return _eval(f.left, assignment) and _eval(f.right, assignment)
        if isinstance(f, Or):
            return _eval(f.left, assignment) or _eval(f.right, assignment)
        if isinstance(f, Implies):
            return (not _eval(f.left, assignment)) or _eval(f.right, assignment)
        if isinstance(f, Iff):
            return _eval(f.left, assignment) == _eval(f.right, assignment)
        return False

    for i in range(1 << len(components)):
        assignment = {comp: bool((i >> j) & 1) for j, comp in enumerate(components)}
        if not _eval(formula, assignment):
            return False
    return True


class GLHilbertProof:
    """Formal Hilbert deduction verifier for Provability Logic GL.
    Axiom schemas:
      - TAUTOLOGY: Classical propositional tautology
      - AXIOM_K: [](A -> B) -> ([]A -> []B)
      - AXIOM_LOB: []( []A -> A ) -> []A
    Inference rules:
      - MP: From P and P -> Q, infer Q
      - NEC: From P, infer []P
    """

    def __init__(self, title: str = "GL Hilbert Proof"):
        self.title = title
        self.steps: List[GLHilbertStep] = []

    def add_step(
        self,
        formula: Formula,
        rule: str,
        justification: str,
        premises: Tuple[int, ...] = (),
    ) -> int:
        step_num = len(self.steps) + 1
        step = GLHilbertStep(step_num, formula, rule, justification, premises)
        self.steps.append(step)
        return step_num

    @property
    def conclusion(self) -> Formula:
        if not self.steps:
            raise ValueError("Empty proof has no conclusion")
        return self.steps[-1].formula

    def verify(self) -> bool:
        """Formally verify every step of the deduction against GL axioms and rules."""
        step_map: Dict[int, Formula] = {}
        for s in self.steps:
            formula = s.formula
            rule = s.rule.upper()

            if rule in ("TAUTOLOGY", "TAUT"):
                if not is_propositional_tautology(formula):
                    return False

            elif rule in ("AXIOM_K", "K"):
                # [](A -> B) -> ([]A -> []B)
                if not (
                    isinstance(formula, Implies)
                    and isinstance(formula.left, Box)
                    and isinstance(formula.left.inner, Implies)
                    and isinstance(formula.right, Implies)
                    and isinstance(formula.right.left, Box)
                    and isinstance(formula.right.right, Box)
                    and formula.left.inner.left == formula.right.left.inner
                    and formula.left.inner.right == formula.right.right.inner
                ):
                    return False

            elif rule in ("AXIOM_LOB", "AXIOM_GL", "LOB", "GL"):
                # []( []A -> A ) -> []A
                if not (
                    isinstance(formula, Implies)
                    and isinstance(formula.left, Box)
                    and isinstance(formula.left.inner, Implies)
                    and isinstance(formula.left.inner.left, Box)
                    and isinstance(formula.right, Box)
                    and formula.left.inner.left.inner == formula.left.inner.right
                    and formula.left.inner.right == formula.right.inner
                ):
                    return False

            elif rule == "MP":
                # Modus Ponens: premises j (P) and k (P -> Q)
                if len(s.premises) != 2:
                    return False
                p1_idx, p2_idx = s.premises
                if p1_idx not in step_map or p2_idx not in step_map:
                    return False
                f1, f2 = step_map[p1_idx], step_map[p2_idx]
                valid_mp = False
                if isinstance(f2, Implies) and f2.left == f1 and f2.right == formula:
                    valid_mp = True
                elif isinstance(f1, Implies) and f1.left == f2 and f1.right == formula:
                    valid_mp = True
                if not valid_mp:
                    return False

            elif rule == "NEC":
                # Necessitation: premise j (P), formula is []P
                if len(s.premises) != 1:
                    return False
                p_idx = s.premises[0]
                if p_idx not in step_map:
                    return False
                p_formula = step_map[p_idx]
                if not (isinstance(formula, Box) and formula.inner == p_formula):
                    return False

            else:
                return False

            step_map[s.step_number] = formula

        return True

    def __str__(self) -> str:
        lines = [f"=== {self.title} ==="]
        for s in self.steps:
            lines.append(str(s))
        return "\n".join(lines)


def gl_hilbert_axioms(p: str = "p", q: str = "q") -> Dict[str, Formula]:
    """Basic axiom schemas of Hilbert system GL."""
    ap = Atom(p)
    aq = Atom(q)
    return {
        "K": Implies(Box(Implies(ap, aq)), Implies(Box(ap), Box(aq))),
        "LOB": Implies(Box(Implies(Box(ap), ap)), Box(ap)),
    }


def gl_derive_axiom_4(p: str = "p") -> GLHilbertProof:
    """Formal certified derivation of Axiom 4 ([]p -> [][]p) from Löb's axiom and System K.
    Uses the classical B = p & []p substitution in Löb's axiom schema.
    """
    proof = GLHilbertProof(f"GL Derivation of Transitivity Axiom 4 ([]p -> [][]p)")
    ap = Atom(p)
    bp = And(ap, Box(ap))

    # 1. (p & []p) -> p (Tautology)
    s1 = proof.add_step(Implies(bp, ap), "TAUTOLOGY", "(p & []p) -> p")
    # 2. []((p & []p) -> p) (NEC on 1)
    s2 = proof.add_step(Box(Implies(bp, ap)), "NEC", "Necessitation on step 1", (s1,))
    # 3. []((p & []p) -> p) -> ([](p & []p) -> []p) (Axiom K)
    k1 = Implies(Box(Implies(bp, ap)), Implies(Box(bp), Box(ap)))
    s3 = proof.add_step(k1, "AXIOM_K", "Axiom K instance on B -> p")
    # 4. [](p & []p) -> []p (MP 2, 3)
    s4 = proof.add_step(Implies(Box(bp), Box(ap)), "MP", "Modus Ponens", (s2, s3))
    # 5. ([]B -> []p) -> ((p & []B) -> (p & []p)) (Tautology)
    tau1 = Implies(Implies(Box(bp), Box(ap)), Implies(And(ap, Box(bp)), bp))
    s5 = proof.add_step(tau1, "TAUTOLOGY", "(X -> Y) -> ((p & X) -> (p & Y))")
    # 6. (p & []B) -> B (MP 4, 5)
    s6 = proof.add_step(Implies(And(ap, Box(bp)), bp), "MP", "Modus Ponens", (s4, s5))
    # 7. ((p & []B) -> B) -> (p -> ([]B -> B)) (Tautology)
    tau2 = Implies(Implies(And(ap, Box(bp)), bp), Implies(ap, Implies(Box(bp), bp)))
    s7 = proof.add_step(tau2, "TAUTOLOGY", "(X & Y -> Z) -> (X -> (Y -> Z))")
    # 8. p -> ([]B -> B) (MP 6, 7)
    s8 = proof.add_step(Implies(ap, Implies(Box(bp), bp)), "MP", "Modus Ponens", (s6, s7))
    # 9. [](p -> ([]B -> B)) (NEC on 8)
    s9 = proof.add_step(Box(Implies(ap, Implies(Box(bp), bp))), "NEC", "Necessitation on step 8", (s8,))
    # 10. [](p -> ([]B -> B)) -> ([]p -> []([]B -> B)) (Axiom K)
    k2 = Implies(Box(Implies(ap, Implies(Box(bp), bp))), Implies(Box(ap), Box(Implies(Box(bp), bp))))
    s10 = proof.add_step(k2, "AXIOM_K", "Axiom K instance on p -> ([]B -> B)")
    # 11. []p -> []([]B -> B) (MP 9, 10)
    s11 = proof.add_step(Implies(Box(ap), Box(Implies(Box(bp), bp))), "MP", "Modus Ponens", (s9, s10))
    # 12. []([]B -> B) -> []B (Axiom Löb for B)
    lob1 = Implies(Box(Implies(Box(bp), bp)), Box(bp))
    s12 = proof.add_step(lob1, "AXIOM_LOB", "Löb axiom instance for B = p & []p")
    # 13. Hypothetical syllogism tautology: ([]p -> []([]B -> B)) -> (([]([]B -> B) -> []B) -> ([]p -> []B))
    tau3 = Implies(
        Implies(Box(ap), Box(Implies(Box(bp), bp))),
        Implies(Implies(Box(Implies(Box(bp), bp)), Box(bp)), Implies(Box(ap), Box(bp))),
    )
    s13 = proof.add_step(tau3, "TAUTOLOGY", "(X -> Y) -> ((Y -> Z) -> (X -> Z))")
    # 14. ([]([]B -> B) -> []B) -> ([]p -> []B) (MP 11, 13)
    s14 = proof.add_step(
        Implies(Implies(Box(Implies(Box(bp), bp)), Box(bp)), Implies(Box(ap), Box(bp))),
        "MP",
        "Modus Ponens",
        (s11, s13),
    )
    # 15. []p -> []B (MP 12, 14)
    s15 = proof.add_step(Implies(Box(ap), Box(bp)), "MP", "Modus Ponens", (s12, s14))
    # 16. (p & []p) -> []p (Tautology: B -> []p)
    s16 = proof.add_step(Implies(bp, Box(ap)), "TAUTOLOGY", "(p & []p) -> []p")
    # 17. []((p & []p) -> []p) (NEC on 16)
    s17 = proof.add_step(Box(Implies(bp, Box(ap))), "NEC", "Necessitation on step 16", (s16,))
    # 18. []((p & []p) -> []p) -> ([](p & []p) -> [][]p) (Axiom K)
    k3 = Implies(Box(Implies(bp, Box(ap))), Implies(Box(bp), Box(Box(ap))))
    s18 = proof.add_step(k3, "AXIOM_K", "Axiom K instance on B -> []p")
    # 19. [](p & []p) -> [][]p (MP 17, 18, i.e. []B -> [][]p)
    s19 = proof.add_step(Implies(Box(bp), Box(Box(ap))), "MP", "Modus Ponens", (s17, s18))
    # 20. Hypothetical syllogism tautology: ([]p -> []B) -> (([]B -> [][]p) -> ([]p -> [][]p))
    tau4 = Implies(
        Implies(Box(ap), Box(bp)),
        Implies(Implies(Box(bp), Box(Box(ap))), Implies(Box(ap), Box(Box(ap)))),
    )
    s20 = proof.add_step(tau4, "TAUTOLOGY", "(X -> Y) -> ((Y -> Z) -> (X -> Z))")
    # 21. ([]B -> [][]p) -> ([]p -> [][]p) (MP 15, 20)
    s21 = proof.add_step(
        Implies(Implies(Box(bp), Box(Box(ap))), Implies(Box(ap), Box(Box(ap)))),
        "MP",
        "Modus Ponens",
        (s15, s20),
    )
    # 22. []p -> [][]p (MP 19, 21)
    proof.add_step(Implies(Box(ap), Box(Box(ap))), "MP", "Modus Ponens", (s19, s21))

    return proof


# ==============================================================================
# Terminating Tableau / Sequent Decision Procedure for GL
# ==============================================================================

@dataclass
class GLSequent:
    """A two-sided sequent Gamma |- Delta for modal provability logic GL."""

    antecedent: FrozenSet[Formula]
    succedent: FrozenSet[Formula]

    def __str__(self) -> str:
        ante_str = ", ".join(str(f) for f in sorted(self.antecedent, key=str)) or "{}"
        succ_str = ", ".join(str(f) for f in sorted(self.succedent, key=str)) or "{}"
        return f"{ante_str} |- {succ_str}"


@dataclass
class GLSequentNode:
    """A proof tree node in a GL sequent derivation."""

    sequent: GLSequent
    rule: str
    is_closed: bool
    children: List["GLSequentNode"] = field(default_factory=list)
    description: str = ""

    def __str__(self) -> str:
        status = "CLOSED" if self.is_closed else "OPEN"
        return f"[{status}] {self.sequent} ({self.rule}: {self.description})"


class GLDecisionResult:
    """Result of deciding GL validity with proof tree or countermodel."""

    def __init__(
        self,
        is_valid: bool,
        formula: Formula,
        proof_tree: Optional[GLSequentNode] = None,
        countermodel: Optional[KripkeModel] = None,
        counterworld: Optional[str] = None,
        visited_states: int = 0,
    ):
        self.is_valid = is_valid
        self.formula = formula
        self.proof_tree = proof_tree
        self.countermodel = countermodel
        self.counterworld = counterworld
        self.visited_states = visited_states

    def verify_countermodel(self, formula: Optional[Formula] = None) -> bool:
        """Verify that the extracted countermodel is a valid GL frame and falsifies the formula."""
        if self.is_valid:
            return False
        if not self.countermodel or self.counterworld is None:
            return False
        target = formula if formula is not None else self.formula
        frame = self.countermodel.frame
        if not frame.is_transitive():
            return False
        if not frame.is_irreflexive():
            return False
        if not frame.is_converse_well_founded():
            return False
        if self.countermodel.satisfies(self.counterworld, target):
            return False
        return True

    def __repr__(self) -> str:
        if self.is_valid:
            return f"GLDecisionResult(valid=True, formula={self.formula!r}, states={self.visited_states})"
        w_cnt = len(self.countermodel.worlds) if self.countermodel else 0
        return f"GLDecisionResult(valid=False, formula={self.formula!r}, counterworld={self.counterworld!r}, worlds={w_cnt})"


class GLDecisionProcedure:
    """Hakli-Negri / Sambin-Valentini terminating sequent decision procedure for Provability Logic GL.
    Uses Löb's diagonal rule on modal jumps:
      When falsifying Box(psi), the successor world assumes Box(psi) in its antecedent.
    Guarantees strict termination without non-terminating loops and extracts finite
    transitive converse well-founded (irreflexive strict DAG) countermodels for non-theorems.
    """

    def __init__(self, max_states: int = 5000):
        self.max_states = max_states
        self.state_counter = 0
        self._world_counter = 0

    def _fresh_world(self) -> str:
        w = f"w{self._world_counter}"
        self._world_counter += 1
        return w

    def solve(self, formula: Formula) -> GLDecisionResult:
        self.state_counter = 0
        self._world_counter = 0
        is_valid, proof_tree, countermodel, counterworld = self._solve_sequent(
            ante=frozenset(),
            succ=frozenset([formula]),
            history=frozenset(),
        )
        return GLDecisionResult(
            is_valid=is_valid,
            formula=formula,
            proof_tree=proof_tree,
            countermodel=countermodel,
            counterworld=counterworld,
            visited_states=self.state_counter,
        )

    def _solve_sequent(
        self,
        ante: FrozenSet[Formula],
        succ: FrozenSet[Formula],
        history: FrozenSet[Tuple[FrozenSet[Formula], FrozenSet[Formula]]],
    ) -> Tuple[bool, GLSequentNode, Optional[KripkeModel], Optional[str]]:
        self.state_counter += 1
        seq = GLSequent(ante, succ)

        # 1. Axiom check
        if Bottom() in ante or Top() in succ or bool(ante & succ):
            node = GLSequentNode(seq, rule="AXIOM", is_closed=True, description="Closed by initial sequent axiom")
            return True, node, None, None

        # 2. Propositional reduction
        # Non-branching rules
        if Top() in ante:
            return self._solve_sequent(ante - {Top()}, succ, history)

        if Bottom() in succ:
            return self._solve_sequent(ante, succ - {Bottom()}, history)

        # L_NOT: ~A in ante => A in succ
        not_ante = [f for f in ante if isinstance(f, Not)]
        if not_ante:
            f = not_ante[0]
            res, child, cm, cw = self._solve_sequent(ante - {f}, succ | {f.inner}, history)
            return res, GLSequentNode(seq, "L_NOT", res, [child]), cm, cw

        # R_NOT: ~A in succ => A in ante
        not_succ = [f for f in succ if isinstance(f, Not)]
        if not_succ:
            f = not_succ[0]
            res, child, cm, cw = self._solve_sequent(ante | {f.inner}, succ - {f}, history)
            return res, GLSequentNode(seq, "R_NOT", res, [child]), cm, cw

        # L_AND: A & B in ante => A, B in ante
        and_ante = [f for f in ante if isinstance(f, And)]
        if and_ante:
            f = and_ante[0]
            res, child, cm, cw = self._solve_sequent((ante - {f}) | {f.left, f.right}, succ, history)
            return res, GLSequentNode(seq, "L_AND", res, [child]), cm, cw

        # R_OR: A | B in succ => A, B in succ
        or_succ = [f for f in succ if isinstance(f, Or)]
        if or_succ:
            f = or_succ[0]
            res, child, cm, cw = self._solve_sequent(ante, (succ - {f}) | {f.left, f.right}, history)
            return res, GLSequentNode(seq, "R_OR", res, [child]), cm, cw

        # R_IMPLIES: A -> B in succ => A in ante, B in succ
        impl_succ = [f for f in succ if isinstance(f, Implies)]
        if impl_succ:
            f = impl_succ[0]
            res, child, cm, cw = self._solve_sequent(ante | {f.left}, (succ - {f}) | {f.right}, history)
            return res, GLSequentNode(seq, "R_IMPLIES", res, [child]), cm, cw

        # L_DIA: <>A in ante => []~A in succ
        dia_ante = [f for f in ante if isinstance(f, Dia)]
        if dia_ante:
            f = dia_ante[0]
            res, child, cm, cw = self._solve_sequent(ante - {f}, succ | {Box(Not(f.inner))}, history)
            return res, GLSequentNode(seq, "L_DIA", res, [child]), cm, cw

        # R_DIA: <>A in succ => []~A in ante
        dia_succ = [f for f in succ if isinstance(f, Dia)]
        if dia_succ:
            f = dia_succ[0]
            res, child, cm, cw = self._solve_sequent(ante | {Box(Not(f.inner))}, succ - {f}, history)
            return res, GLSequentNode(seq, "R_DIA", res, [child]), cm, cw

        # L_IFF: (A <-> B) in ante => (A -> B), (B -> A) in ante
        iff_ante = [f for f in ante if isinstance(f, Iff)]
        if iff_ante:
            f = iff_ante[0]
            res, child, cm, cw = self._solve_sequent(
                (ante - {f}) | {Implies(f.left, f.right), Implies(f.right, f.left)}, succ, history
            )
            return res, GLSequentNode(seq, "L_IFF", res, [child]), cm, cw

        # Branching rules
        # R_AND: A & B in succ => branches on A and B in succ
        and_succ = [f for f in succ if isinstance(f, And)]
        if and_succ:
            f = and_succ[0]
            res1, c1, cm1, cw1 = self._solve_sequent(ante, (succ - {f}) | {f.left}, history)
            if not res1:
                return False, GLSequentNode(seq, "R_AND", False, [c1]), cm1, cw1
            res2, c2, cm2, cw2 = self._solve_sequent(ante, (succ - {f}) | {f.right}, history)
            if not res2:
                return False, GLSequentNode(seq, "R_AND", False, [c1, c2]), cm2, cw2
            return True, GLSequentNode(seq, "R_AND", True, [c1, c2]), None, None

        # L_OR: A | B in ante => branches on A and B in ante
        or_ante = [f for f in ante if isinstance(f, Or)]
        if or_ante:
            f = or_ante[0]
            res1, c1, cm1, cw1 = self._solve_sequent((ante - {f}) | {f.left}, succ, history)
            if not res1:
                return False, GLSequentNode(seq, "L_OR", False, [c1]), cm1, cw1
            res2, c2, cm2, cw2 = self._solve_sequent((ante - {f}) | {f.right}, succ, history)
            if not res2:
                return False, GLSequentNode(seq, "L_OR", False, [c1, c2]), cm2, cw2
            return True, GLSequentNode(seq, "L_OR", True, [c1, c2]), None, None

        # L_IMPLIES: A -> B in ante => branches into (ante |- succ, A) and (ante, B |- succ)
        impl_ante = [f for f in ante if isinstance(f, Implies)]
        if impl_ante:
            f = impl_ante[0]
            res1, c1, cm1, cw1 = self._solve_sequent(ante - {f}, succ | {f.left}, history)
            if not res1:
                return False, GLSequentNode(seq, "L_IMPLIES", False, [c1]), cm1, cw1
            res2, c2, cm2, cw2 = self._solve_sequent((ante - {f}) | {f.right}, succ, history)
            if not res2:
                return False, GLSequentNode(seq, "L_IMPLIES", False, [c1, c2]), cm2, cw2
            return True, GLSequentNode(seq, "L_IMPLIES", True, [c1, c2]), None, None

        # R_IFF: (A <-> B) in succ => branches into (A -> B) and (B -> A)
        iff_succ = [f for f in succ if isinstance(f, Iff)]
        if iff_succ:
            f = iff_succ[0]
            res1, c1, cm1, cw1 = self._solve_sequent(ante, (succ - {f}) | {Implies(f.left, f.right)}, history)
            if not res1:
                return False, GLSequentNode(seq, "R_IFF", False, [c1]), cm1, cw1
            res2, c2, cm2, cw2 = self._solve_sequent(ante, (succ - {f}) | {Implies(f.right, f.left)}, history)
            if not res2:
                return False, GLSequentNode(seq, "R_IFF", False, [c1, c2]), cm2, cw2
            return True, GLSequentNode(seq, "R_IFF", True, [c1, c2]), None, None

        # 3. Fully reduced propositionally: all formulas are Atoms or Boxes
        if bool(ante & succ):
            node = GLSequentNode(seq, rule="AXIOM", is_closed=True, description="Closed by atom/box match")
            return True, node, None, None

        boxes_succ = [f for f in succ if isinstance(f, Box)]
        if not boxes_succ:
            # Dead-end world: no box obligation in succedent to jump into
            w = self._fresh_world()
            val = {f.name: {w} for f in ante if isinstance(f, Atom)}
            frame = KripkeFrame({w}, set())
            model = KripkeModel(frame, val)
            return (
                False,
                GLSequentNode(seq, "LEAF_FALSIFIED", False, description=f"Dead-end world {w} falsifies sequent"),
                model,
                w,
            )

        # 4. Modal Jump (GLR) with loop detection
        state_key = (ante, succ)
        if state_key in history:
            w = self._fresh_world()
            val = {f.name: {w} for f in ante if isinstance(f, Atom)}
            frame = KripkeFrame({w}, set())
            model = KripkeModel(frame, val)
            return (
                False,
                GLSequentNode(seq, "LOOP_DETECTED", False, description=f"Loop detected at {state_key}"),
                model,
                w,
            )

        new_history = history | {state_key}
        boxes_ante = {f for f in ante if isinstance(f, Box)}
        box_inners_ante = {f.inner for f in boxes_ante}

        children = []
        countermodels: List[Tuple[KripkeModel, str]] = []

        for box_target in sorted(boxes_succ, key=str):
            jump_ante = frozenset(box_inners_ante | boxes_ante | {box_target})
            jump_succ = frozenset({box_target.inner})
            res, child, cm, cw = self._solve_sequent(jump_ante, jump_succ, new_history)
            children.append(child)
            if res:
                # In modal logics, []A1 & ... & []Am -> []B1 | ... | []Bk is theorem
                # iff for some j: []A1 & ... & []Am -> []Bj is theorem.
                node = GLSequentNode(
                    seq,
                    rule="GLR",
                    is_closed=True,
                    children=children,
                    description=f"Closed via modal jump on {box_target}",
                )
                return True, node, None, None
            else:
                assert cm is not None and cw is not None
                countermodels.append((cm, cw))

        # All box jumps failed! Construct composite countermodel:
        w = self._fresh_world()
        worlds: Set[str] = {w}
        relation: Set[Tuple[str, str]] = set()
        valuation: Dict[str, Set[str]] = {}
        for f in ante:
            if isinstance(f, Atom):
                valuation.setdefault(f.name, set()).add(w)

        for cm, cw in countermodels:
            worlds.update(cm.frame.worlds)
            relation.update(cm.frame.relation)
            relation.add((w, cw))
            for u in cm.frame.worlds:
                if (cw, u) in cm.frame.relation:
                    relation.add((w, u))
            for atom_name, w_set in cm.valuation.items():
                valuation.setdefault(atom_name, set()).update(w_set)

        frame = KripkeFrame(worlds, relation)
        model = KripkeModel(frame, valuation)
        node = GLSequentNode(
            seq,
            rule="GLR",
            is_closed=False,
            children=children,
            description=f"Open at world {w}: all modal jumps failed",
        )
        return False, node, model, w


def prove_gl(formula: Formula) -> GLDecisionResult:
    """Decide validity of formula in Gödel-Löb Provability Logic GL.
    If valid, returns proof tree. If invalid, returns a finite transitive converse well-founded countermodel.
    """
    solver = GLDecisionProcedure()
    return solver.solve(formula)


def check_gl_validity(formula: Formula) -> GLDecisionResult:
    """Alias for prove_gl."""
    return prove_gl(formula)


# ==============================================================================
# Solovay Arithmetical Realization Mapping
# ==============================================================================

class PASentence:
    """Abstract base class for sentences of Peano Arithmetic."""

    def __repr__(self) -> str:
        return str(self)


class PAAtom(PASentence):
    """An arithmetical sentence variable (representing a formula in L_PA)."""

    def __init__(self, name: str):
        self.name = name

    def __str__(self) -> str:
        return self.name

    def __eq__(self, other: Any) -> bool:
        return isinstance(other, PAAtom) and self.name == other.name

    def __hash__(self) -> int:
        return hash(("PA_ATOM", self.name))


class PAEquation(PASentence):
    """An arithmetical equation t1 = t2."""

    def __init__(self, left: str, right: str):
        self.left = left
        self.right = right

    def __str__(self) -> str:
        return f"({self.left} = {self.right})"

    def __eq__(self, other: Any) -> bool:
        return isinstance(other, PAEquation) and self.left == other.left and self.right == other.right

    def __hash__(self) -> int:
        return hash(("PA_EQ", self.left, self.right))


class PATrue(PASentence):
    """Arithmetical verum: 0 = 0."""

    def __str__(self) -> str:
        return "(0 = 0)"

    def __eq__(self, other: Any) -> bool:
        return isinstance(other, PATrue)

    def __hash__(self) -> int:
        return hash("PA_TRUE")


class PAFalse(PASentence):
    """Arithmetical falsum: 0 = 1."""

    def __str__(self) -> str:
        return "(0 = 1)"

    def __eq__(self, other: Any) -> bool:
        return isinstance(other, PAFalse)

    def __hash__(self) -> int:
        return hash("PA_FALSE")


class PANot(PASentence):
    def __init__(self, inner: PASentence):
        self.inner = inner

    def __str__(self) -> str:
        return f"~{self.inner}"

    def __eq__(self, other: Any) -> bool:
        return isinstance(other, PANot) and self.inner == other.inner

    def __hash__(self) -> int:
        return hash(("PA_NOT", self.inner))


class PAAnd(PASentence):
    def __init__(self, left: PASentence, right: PASentence):
        self.left = left
        self.right = right

    def __str__(self) -> str:
        return f"({self.left} & {self.right})"

    def __eq__(self, other: Any) -> bool:
        return isinstance(other, PAAnd) and self.left == other.left and self.right == other.right

    def __hash__(self) -> int:
        return hash(("PA_AND", self.left, self.right))


class PAOr(PASentence):
    def __init__(self, left: PASentence, right: PASentence):
        self.left = left
        self.right = right

    def __str__(self) -> str:
        return f"({self.left} | {self.right})"

    def __eq__(self, other: Any) -> bool:
        return isinstance(other, PAOr) and self.left == other.left and self.right == other.right

    def __hash__(self) -> int:
        return hash(("PA_OR", self.left, self.right))


class PAImplies(PASentence):
    def __init__(self, left: PASentence, right: PASentence):
        self.left = left
        self.right = right

    def __str__(self) -> str:
        return f"({self.left} -> {self.right})"

    def __eq__(self, other: Any) -> bool:
        return isinstance(other, PAImplies) and self.left == other.left and self.right == other.right

    def __hash__(self) -> int:
        return hash(("PA_IMPLIES", self.left, self.right))


class PAIff(PASentence):
    def __init__(self, left: PASentence, right: PASentence):
        self.left = left
        self.right = right

    def __str__(self) -> str:
        return f"({self.left} <-> {self.right})"

    def __eq__(self, other: Any) -> bool:
        return isinstance(other, PAIff) and self.left == other.left and self.right == other.right

    def __hash__(self) -> int:
        return hash(("PA_IFF", self.left, self.right))


class PAProvability(PASentence):
    """The formalized provability predicate Bew_PA([phi]) / Prov_PA([phi])."""

    def __init__(self, sentence: PASentence):
        self.sentence = sentence

    def __str__(self) -> str:
        return f"Prov_PA([{self.sentence}])"

    def __eq__(self, other: Any) -> bool:
        return isinstance(other, PAProvability) and self.sentence == other.sentence

    def __hash__(self) -> int:
        return hash(("PA_PROV", self.sentence))


class PAConsistency(PASentence):
    """The formalized consistency predicate Consis_PA(phi) = ~Prov_PA([~phi]).
    Default: Consis_PA = ~Prov_PA([0 = 1]).
    """

    def __init__(self, sentence: Optional[PASentence] = None):
        self.sentence = sentence

    def __str__(self) -> str:
        if self.sentence is None or isinstance(self.sentence, PATrue):
            return "Consis_PA"
        return f"Consis_PA({self.sentence})"

    def __eq__(self, other: Any) -> bool:
        return isinstance(other, PAConsistency) and self.sentence == other.sentence

    def __hash__(self) -> int:
        return hash(("PA_CONSIS", self.sentence))

    def to_provability(self) -> PASentence:
        if self.sentence is None or isinstance(self.sentence, PATrue):
            return PANot(PAProvability(PAFalse()))
        return PANot(PAProvability(PANot(self.sentence)))


class ArithmeticalRealization:
    """Mapping from modal propositional atoms to sentences of Peano Arithmetic."""

    def __init__(self, mapping: Optional[Dict[str, PASentence]] = None):
        self.mapping: Dict[str, PASentence] = dict(mapping) if mapping else {}

    def get(self, atom_name: str) -> PASentence:
        if atom_name in self.mapping:
            return self.mapping[atom_name]
        return PAAtom(f"A_{atom_name}")

    def set(self, atom_name: str, sentence: PASentence) -> None:
        self.mapping[atom_name] = sentence

    def __call__(self, atom_name: str) -> PASentence:
        return self.get(atom_name)


def solovay_translation(
    formula: Formula,
    realization: Optional[Union[ArithmeticalRealization, Dict[str, PASentence]]] = None,
) -> PASentence:
    """Translate a modal propositional formula into an arithmetical sentence of PA
    according to Solovay's arithmetical realization mapping.
    Maps:
      - atom p to realization(p)
      - TOP to 0 = 0
      - BOTTOM to 0 = 1
      - connectives to corresponding PA connectives
      - Box(phi) to Prov_PA([phi*])
      - Dia(phi) to ~Prov_PA([~phi*])
    """
    if realization is None:
        realizer = ArithmeticalRealization()
    elif isinstance(realization, dict):
        realizer = ArithmeticalRealization(realization)
    else:
        realizer = realization

    if isinstance(formula, Atom):
        return realizer(formula.name)
    if isinstance(formula, Top):
        return PATrue()
    if isinstance(formula, Bottom):
        return PAFalse()
    if isinstance(formula, Not):
        return PANot(solovay_translation(formula.inner, realizer))
    if isinstance(formula, And):
        return PAAnd(
            solovay_translation(formula.left, realizer),
            solovay_translation(formula.right, realizer),
        )
    if isinstance(formula, Or):
        return PAOr(
            solovay_translation(formula.left, realizer),
            solovay_translation(formula.right, realizer),
        )
    if isinstance(formula, Implies):
        return PAImplies(
            solovay_translation(formula.left, realizer),
            solovay_translation(formula.right, realizer),
        )
    if isinstance(formula, Iff):
        return PAIff(
            solovay_translation(formula.left, realizer),
            solovay_translation(formula.right, realizer),
        )
    if isinstance(formula, Box):
        inner_pa = solovay_translation(formula.inner, realizer)
        return PAProvability(inner_pa)
    if isinstance(formula, Dia):
        inner_pa = solovay_translation(formula.inner, realizer)
        return PANot(PAProvability(PANot(inner_pa)))
    raise TypeError(f"Unknown formula type in solovay_translation: {type(formula)}")


def solovay_derivability_conditions(
    sentence: Optional[PASentence] = None, sentence_b: Optional[PASentence] = None
) -> Dict[str, PASentence]:
    """Formalize the Hilbert-Bernays-Löb derivability conditions in Peano Arithmetic:
    D1: PA |- A implies PA |- Prov_PA([A]) (formalized as Prov_PA([A]))
    D2: Prov_PA([A -> B]) -> (Prov_PA([A]) -> Prov_PA([B]))
    D3: Prov_PA([A]) -> Prov_PA([Prov_PA([A])])
    LOB: Prov_PA([Prov_PA([A]) -> A]) -> Prov_PA([A])
    """
    a = sentence if sentence is not None else PAAtom("A")
    b = sentence_b if sentence_b is not None else PAAtom("B")

    d1 = PAProvability(a)
    d2 = PAImplies(
        PAProvability(PAImplies(a, b)),
        PAImplies(PAProvability(a), PAProvability(b)),
    )
    d3 = PAImplies(PAProvability(a), PAProvability(PAProvability(a)))
    lob = PAImplies(
        PAProvability(PAImplies(PAProvability(a), a)),
        PAProvability(a),
    )
    return {"D1": d1, "D2": d2, "D3": d3, "LOB": lob}


def solovay_goedel_second_incompleteness() -> PASentence:
    """Formalize Gödel's Second Incompleteness Theorem under Solovay realization:
    ~Prov_PA([0 = 1]) -> ~Prov_PA([~Prov_PA([0 = 1])])
    i.e. Consis_PA -> ~Prov_PA([Consis_PA]).
    """
    consis = PANot(PAProvability(PAFalse()))
    unprovable_consis = PANot(PAProvability(consis))
    return PAImplies(consis, unprovable_consis)
