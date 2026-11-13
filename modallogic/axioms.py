"""Canonical modal axioms, systems, and correspondence conditions."""

from typing import Dict, Any, List
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
from .semantics import KripkeFrame


def axiom_k(p: str = "p", q: str = "q") -> Formula:
    """Axiom K: [](p -> q) -> ([]p -> []q). Holds on every Kripke frame."""
    ap = Atom(p)
    aq = Atom(q)
    return Implies(
        Box(Implies(ap, aq)),
        Implies(Box(ap), Box(aq)),
    )


def axiom_t(p: str = "p") -> Formula:
    """Axiom T: []p -> p. Corresponds to reflexivity."""
    ap = Atom(p)
    return Implies(Box(ap), ap)


def axiom_4(p: str = "p") -> Formula:
    """Axiom 4: []p -> [][]p. Corresponds to transitivity."""
    ap = Atom(p)
    return Implies(Box(ap), Box(Box(ap)))


def axiom_b(p: str = "p") -> Formula:
    """Axiom B: p -> []<>p. Corresponds to symmetry."""
    ap = Atom(p)
    return Implies(ap, Box(Dia(ap)))


def axiom_d(p: str = "p") -> Formula:
    """Axiom D: []p -> <>p. Corresponds to seriality."""
    ap = Atom(p)
    return Implies(Box(ap), Dia(ap))


def axiom_5(p: str = "p") -> Formula:
    """Axiom 5: <>p -> []<>p. Corresponds to euclideanness."""
    ap = Atom(p)
    return Implies(Dia(ap), Box(Dia(ap)))


def axiom_gl(p: str = "p") -> Formula:
    """Gödel-Löb Axiom GL: []( []p -> p ) -> []p.
    Corresponds to transitive and converse well-founded frames.
    """
    ap = Atom(p)
    return Implies(Box(Implies(Box(ap), ap)), Box(ap))


def axiom_grz(p: str = "p") -> Formula:
    """Grzegorczyk Axiom Grz: []( [](p -> []p) -> p ) -> p.
    Corresponds to reflexive, transitive, converse well-founded (partially ordered) frames.
    """
    ap = Atom(p)
    inner = Implies(Box(Implies(ap, Box(ap))), ap)
    return Implies(Box(inner), ap)


def axiom_c4(p: str = "p") -> Formula:
    """Lemmon confluence / Church-Rosser axiom: <>[]p -> []<>p.
    Corresponds to directed / confluent frames.
    """
    ap = Atom(p)
    return Implies(Dia(Box(ap)), Box(Dia(ap)))


def axiom_cd(p: str = "p") -> Formula:
    """Determinism / functionality axiom: <>p -> []p.
    Corresponds to partial functionality: at most one successor.
    """
    ap = Atom(p)
    return Implies(Dia(ap), Box(ap))


STANDARD_AXIOMS: Dict[str, Formula] = {
    "K": axiom_k(),
    "T": axiom_t(),
    "4": axiom_4(),
    "B": axiom_b(),
    "D": axiom_d(),
    "5": axiom_5(),
    "GL": axiom_gl(),
    "Grz": axiom_grz(),
    "C4": axiom_c4(),
    "CD": axiom_cd(),
}


class ModalSystem:
    """Specification of a modal logic system by its characteristic axioms and frame condition."""

    def __init__(self, name: str, axioms: List[str], description: str):
        self.name = name
        self.axioms = axioms
        self.description = description

    def verify_frame(self, frame: KripkeFrame) -> bool:
        """Verify whether the frame satisfies the frame properties required by this modal system."""
        if self.name == "K":
            return True
        if self.name == "KD":
            return frame.is_serial()
        if self.name in ("T", "KT"):
            return frame.is_reflexive()
        if self.name == "KB":
            return frame.is_symmetric()
        if self.name == "K4":
            return frame.is_transitive()
        if self.name == "K45":
            return frame.is_transitive() and frame.is_euclidean()
        if self.name == "KD45":
            return frame.is_serial() and frame.is_transitive() and frame.is_euclidean()
        if self.name == "S4":
            return frame.is_s4_frame()
        if self.name == "S5":
            return frame.is_s5_frame()
        if self.name == "GL":
            return frame.is_gl_frame()
        raise ValueError(f"Unknown modal system: {self.name}")


SYSTEMS: Dict[str, ModalSystem] = {
    "K": ModalSystem("K", ["K"], "Basic normal modal logic (arbitrary frames)"),
    "KD": ModalSystem("KD", ["K", "D"], "Deontic modal logic (serial frames)"),
    "T": ModalSystem("T", ["K", "T"], "Reflexive modal logic (reflexive frames)"),
    "KB": ModalSystem("KB", ["K", "B"], "Brouwerian modal logic (symmetric frames)"),
    "K4": ModalSystem("K4", ["K", "4"], "Transitive modal logic (transitive frames)"),
    "K45": ModalSystem("K45", ["K", "4", "5"], "Transitive euclidean modal logic"),
    "KD45": ModalSystem("KD45", ["K", "D", "4", "5"], "Doxastic modal logic of belief"),
    "S4": ModalSystem("S4", ["K", "T", "4"], "Epistemic/intuitionistic logic (preorders)"),
    "S5": ModalSystem("S5", ["K", "T", "4", "5"], "Logic of universal modality (equivalence frames)"),
    "GL": ModalSystem("GL", ["K", "GL"], "Gödel-Löb provability logic (transitive converse well-founded)"),
}
