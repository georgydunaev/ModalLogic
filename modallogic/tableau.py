"""Semantic tableau calculus and countermodel extraction for modal logics K, T, S4, and S5."""

from typing import Set, Tuple, List, Dict, Optional, Any, FrozenSet
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
from .semantics import KripkeFrame, KripkeModel


@dataclass(frozen=True)
class SignedFormula:
    sign: bool  # True for T(phi), False for F(phi)
    world: str
    formula: Formula

    def __repr__(self) -> str:
        s = "T" if self.sign else "F"
        return f"{s}({self.formula}, {self.world})"


class TableauResult:
    """Result of running the tableau decision procedure."""

    def __init__(
        self,
        is_valid: bool,
        system: str,
        countermodel: Optional[KripkeModel] = None,
        counterworld: Optional[str] = None,
        proof_steps: int = 0,
    ):
        self.is_valid = is_valid
        self.system = system
        self.countermodel = countermodel
        self.counterworld = counterworld
        self.proof_steps = proof_steps

    def __repr__(self) -> str:
        if self.is_valid:
            return f"TableauResult(valid=True, system={self.system!r}, steps={self.proof_steps})"
        return (
            f"TableauResult(valid=False, system={self.system!r}, "
            f"counterworld={self.counterworld!r}, worlds={len(self.countermodel.worlds)})"
        )


class TableauBranch:
    """Single branch in a semantic tableau proof tree."""

    def __init__(
        self,
        signed_formulas: Optional[Set[SignedFormula]] = None,
        relation: Optional[Set[Tuple[str, str]]] = None,
        worlds: Optional[Set[str]] = None,
    ):
        self.signed_formulas: Set[SignedFormula] = (
            set(signed_formulas) if signed_formulas else set()
        )
        self.relation: Set[Tuple[str, str]] = set(relation) if relation else set()
        self.worlds: Set[str] = set(worlds) if worlds else set()
        self.processed: Set[SignedFormula] = set()

    def copy(self) -> "TableauBranch":
        b = TableauBranch(self.signed_formulas, self.relation, self.worlds)
        b.processed = set(self.processed)
        return b

    def add_world(self, w: str) -> None:
        self.worlds.add(w)

    def add_edge(self, u: str, v: str) -> None:
        self.worlds.add(u)
        self.worlds.add(v)
        self.relation.add((u, v))

    def add_formula(self, sf: SignedFormula) -> None:
        self.signed_formulas.add(sf)
        self.worlds.add(sf.world)

    def is_closed(self) -> bool:
        """Check if branch contains an explicit contradiction."""
        true_atoms: Dict[str, Set[Formula]] = {}
        false_atoms: Dict[str, Set[Formula]] = {}

        for sf in self.signed_formulas:
            w = sf.world
            phi = sf.formula
            if sf.sign:
                if isinstance(phi, Bottom):
                    return True
                true_atoms.setdefault(w, set()).add(phi)
                if phi in false_atoms.get(w, set()):
                    return True
            else:
                if isinstance(phi, Top):
                    return True
                false_atoms.setdefault(w, set()).add(phi)
                if phi in true_atoms.get(w, set()):
                    return True

        return False


class TableauSolver:
    """Automated tableau theorem prover and countermodel generator for modal propositional logics."""

    def __init__(self, system: str = "K", max_steps: int = 1000):
        system = system.upper()
        if system not in ("K", "T", "KT", "S4", "S5"):
            raise ValueError(f"Unsupported modal system for tableau: {system}")
        if system == "KT":
            system = "T"
        self.system = system
        self.max_steps = max_steps
        self.world_counter = 0

    def _fresh_world(self, prefix: str = "w") -> str:
        self.world_counter += 1
        return f"{prefix}_{self.world_counter}"

    def check_validity(self, formula: Formula) -> TableauResult:
        """Determine whether formula is valid in the specified modal logic system."""
        self.world_counter = 0
        root_world = "w0"

        # Search for a countermodel: test whether F(formula, root_world) can be satisfied
        root_sf = SignedFormula(sign=False, world=root_world, formula=formula)
        initial_branch = TableauBranch()
        initial_branch.add_world(root_world)
        initial_branch.add_formula(root_sf)

        if self.system in ("T", "S4", "S5"):
            initial_branch.add_edge(root_world, root_world)

        steps = [0]
        countermodel_branch = self._expand(initial_branch, steps)

        if countermodel_branch is None:
            # All branches closed => formula is valid
            return TableauResult(is_valid=True, system=self.system, proof_steps=steps[0])

        # An open, fully-saturated branch was found => extract countermodel
        model = self._extract_countermodel(countermodel_branch)
        return TableauResult(
            is_valid=False,
            system=self.system,
            countermodel=model,
            counterworld=root_world,
            proof_steps=steps[0],
        )

    def _extract_countermodel(self, branch: TableauBranch) -> KripkeModel:
        """Build KripkeModel from an open, saturated tableau branch."""
        worlds = set(branch.worlds)
        relation = set(branch.relation)

        # Apply closure conditions for the modal system
        if self.system in ("T", "S4", "S5"):
            for w in worlds:
                relation.add((w, w))
        if self.system in ("S4", "S5"):
            # Transitive closure
            changed = True
            while changed:
                changed = False
                to_add = set()
                for u, v in relation:
                    for w in worlds:
                        if (v, w) in relation and (u, w) not in relation:
                            to_add.add((u, w))
                if to_add:
                    relation.update(to_add)
                    changed = True
        if self.system == "S5":
            # Universal / equivalence closure: all worlds can see all worlds
            for u in worlds:
                for v in worlds:
                    relation.add((u, v))

        # Atomic valuations
        valuation: Dict[str, Set[str]] = {}
        for sf in branch.signed_formulas:
            if sf.sign and isinstance(sf.formula, Atom):
                valuation.setdefault(sf.formula.name, set()).add(sf.world)

        frame = KripkeFrame(worlds, relation)
        return KripkeModel(frame, valuation)

    def _world_label_set(self, branch: TableauBranch, w: str) -> FrozenSet[Tuple[bool, Formula]]:
        return frozenset((sf.sign, sf.formula) for sf in branch.signed_formulas if sf.world == w)

    def _expand(self, branch: TableauBranch, steps: List[int]) -> Optional[TableauBranch]:
        """Expand branch recursively. Returns an open saturated branch if satisfiable, or None if closed."""
        steps[0] += 1
        if steps[0] > self.max_steps:
            # Safety timeout against infinite loops
            return branch

        if branch.is_closed():
            return None

        # 1. Apply propositional linear rules (Top, Bottom, Not, True And, False Or, False Implies)
        linear_candidate = None
        for sf in branch.signed_formulas:
            if sf in branch.processed:
                continue
            phi = sf.formula
            sign = sf.sign
            if isinstance(phi, (Top, Bottom, Atom)):
                branch.processed.add(sf)
                continue
            if isinstance(phi, Not):
                linear_candidate = sf
                break
            if sign and isinstance(phi, And):
                linear_candidate = sf
                break
            if not sign and isinstance(phi, Or):
                linear_candidate = sf
                break
            if not sign and isinstance(phi, Implies):
                linear_candidate = sf
                break

        if linear_candidate:
            branch.processed.add(linear_candidate)
            w = linear_candidate.world
            phi = linear_candidate.formula
            sign = linear_candidate.sign

            if isinstance(phi, Not):
                branch.add_formula(SignedFormula(not sign, w, phi.inner))
            elif sign and isinstance(phi, And):
                branch.add_formula(SignedFormula(True, w, phi.left))
                branch.add_formula(SignedFormula(True, w, phi.right))
            elif not sign and isinstance(phi, Or):
                branch.add_formula(SignedFormula(False, w, phi.left))
                branch.add_formula(SignedFormula(False, w, phi.right))
            elif not sign and isinstance(phi, Implies):
                branch.add_formula(SignedFormula(True, w, phi.left))
                branch.add_formula(SignedFormula(False, w, phi.right))

            return self._expand(branch, steps)

        # 2. Apply propositional branching rules (False And, True Or, True Implies, Iff)
        branching_candidate = None
        for sf in branch.signed_formulas:
            if sf in branch.processed:
                continue
            phi = sf.formula
            sign = sf.sign
            if not sign and isinstance(phi, And):
                branching_candidate = sf
                break
            if sign and isinstance(phi, Or):
                branching_candidate = sf
                break
            if sign and isinstance(phi, Implies):
                branching_candidate = sf
                break
            if isinstance(phi, Iff):
                branching_candidate = sf
                break

        if branching_candidate:
            branch.processed.add(branching_candidate)
            w = branching_candidate.world
            phi = branching_candidate.formula
            sign = branching_candidate.sign

            if not sign and isinstance(phi, And):
                # F(A & B) branches into F(A) | F(B)
                b1 = branch.copy()
                b1.add_formula(SignedFormula(False, w, phi.left))
                res = self._expand(b1, steps)
                if res is not None:
                    return res
                b2 = branch.copy()
                b2.add_formula(SignedFormula(False, w, phi.right))
                return self._expand(b2, steps)

            if sign and isinstance(phi, Or):
                # T(A | B) branches into T(A) | T(B)
                b1 = branch.copy()
                b1.add_formula(SignedFormula(True, w, phi.left))
                res = self._expand(b1, steps)
                if res is not None:
                    return res
                b2 = branch.copy()
                b2.add_formula(SignedFormula(True, w, phi.right))
                return self._expand(b2, steps)

            if sign and isinstance(phi, Implies):
                # T(A -> B) branches into F(A) | T(B)
                b1 = branch.copy()
                b1.add_formula(SignedFormula(False, w, phi.left))
                res = self._expand(b1, steps)
                if res is not None:
                    return res
                b2 = branch.copy()
                b2.add_formula(SignedFormula(True, w, phi.right))
                return self._expand(b2, steps)

            if isinstance(phi, Iff):
                if sign:
                    # T(A <-> B) branches into {T(A), T(B)} | {F(A), F(B)}
                    b1 = branch.copy()
                    b1.add_formula(SignedFormula(True, w, phi.left))
                    b1.add_formula(SignedFormula(True, w, phi.right))
                    res = self._expand(b1, steps)
                    if res is not None:
                        return res
                    b2 = branch.copy()
                    b2.add_formula(SignedFormula(False, w, phi.left))
                    b2.add_formula(SignedFormula(False, w, phi.right))
                    return self._expand(b2, steps)
                else:
                    # F(A <-> B) branches into {T(A), F(B)} | {F(A), T(B)}
                    b1 = branch.copy()
                    b1.add_formula(SignedFormula(True, w, phi.left))
                    b1.add_formula(SignedFormula(False, w, phi.right))
                    res = self._expand(b1, steps)
                    if res is not None:
                        return res
                    b2 = branch.copy()
                    b2.add_formula(SignedFormula(False, w, phi.left))
                    b2.add_formula(SignedFormula(True, w, phi.right))
                    return self._expand(b2, steps)

        # 3. Apply modal Universal propagation (T Box, F Dia) along accessibility
        propagated_any = False
        for sf in list(branch.signed_formulas):
            phi = sf.formula
            sign = sf.sign
            w = sf.world

            # For S5, relation is universal across all worlds in branch
            targets = (
                branch.worlds
                if self.system == "S5"
                else {v for (u, v) in branch.relation if u == w}
            )

            if self.system in ("T", "S4") and w not in targets:
                targets = targets | {w}

            if sign and isinstance(phi, Box):
                for v in targets:
                    target_sf = SignedFormula(True, v, phi.inner)
                    if target_sf not in branch.signed_formulas:
                        branch.add_formula(target_sf)
                        propagated_any = True
                    if self.system == "S4":
                        box_sf = SignedFormula(True, v, phi)
                        if box_sf not in branch.signed_formulas:
                            branch.add_formula(box_sf)
                            propagated_any = True

            if not sign and isinstance(phi, Dia):
                for v in targets:
                    target_sf = SignedFormula(False, v, phi.inner)
                    if target_sf not in branch.signed_formulas:
                        branch.add_formula(target_sf)
                        propagated_any = True
                    if self.system == "S4":
                        dia_sf = SignedFormula(False, v, phi)
                        if dia_sf not in branch.signed_formulas:
                            branch.add_formula(dia_sf)
                            propagated_any = True

        if propagated_any:
            return self._expand(branch, steps)

        # 4. Apply modal Existential generation (F Box, T Dia) creating a fresh world
        existential_candidate = None
        for sf in branch.signed_formulas:
            if sf in branch.processed:
                continue
            phi = sf.formula
            sign = sf.sign
            if (not sign and isinstance(phi, Box)) or (sign and isinstance(phi, Dia)):
                existential_candidate = sf
                break

        if existential_candidate:
            branch.processed.add(existential_candidate)
            w = existential_candidate.world
            phi = existential_candidate.formula
            sign = existential_candidate.sign

            inner = phi.inner
            target_sign = False if not sign else True

            # In S4, check for loop blocking: if w already has a successor with matching label
            if self.system == "S4":
                # Check if there is an existing successor that already has target_sign, inner
                already_satisfied = any(
                    SignedFormula(target_sign, v, inner) in branch.signed_formulas
                    for (u, v) in branch.relation
                    if u == w
                )
                if already_satisfied:
                    return self._expand(branch, steps)

            fresh = self._fresh_world()
            branch.add_world(fresh)
            branch.add_edge(w, fresh)
            branch.add_formula(SignedFormula(target_sign, fresh, inner))

            if self.system in ("T", "S4", "S5"):
                branch.add_edge(fresh, fresh)

            return self._expand(branch, steps)

        # No rules apply and branch is not closed => Saturated open branch found!
        return branch
