"""Gödel-Löb Provability Logic (GL): Axioms, Kripke semantics, and fixed-point algorithms."""

from typing import Set, Tuple, Dict, Any, Optional, List
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
