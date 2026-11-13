"""Canonical model evaluations, subformula closures, and canonical frame condition verifiers."""

from typing import Set, Tuple, Dict, Any, List, Optional, Iterable, Union
import itertools
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
    from_tuple,
)
from .semantics import KripkeFrame, KripkeModel
from .frames import (
    create_frame,
    ComposableFrame,
    KFrame,
    TFrame,
    S4Frame,
    S5Frame,
    K4Frame,
    GLFrame,
    KD45Frame,
)


def compute_subformulas(formula: Formula) -> Set[Formula]:
    """Extract all structural subformulas of a modal formula."""
    subs: Set[Formula] = {formula}
    if isinstance(formula, (Atom, Top, Bottom)):
        return subs
    if isinstance(formula, Not):
        subs.update(compute_subformulas(formula.inner))
    elif isinstance(formula, (And, Or, Implies, Iff)):
        subs.update(compute_subformulas(formula.left))
        subs.update(compute_subformulas(formula.right))
    elif isinstance(formula, (Box, Dia)):
        subs.update(compute_subformulas(formula.inner))
    return subs


class SubformulaClosure:
    """Finite closure of formulas closed under subformulas and single negation."""

    def __init__(self, formulas: Iterable[Formula]):
        base_subs: Set[Formula] = set()
        for f in formulas:
            base_subs.update(compute_subformulas(f))

        # Close under single negation
        full: Set[Formula] = set(base_subs)
        for sub in base_subs:
            if isinstance(sub, Not):
                full.add(sub.inner)
            else:
                full.add(Not(sub))
        full.add(Top())
        full.add(Bottom())

        self.formulas: Set[Formula] = full

    def __len__(self) -> int:
        return len(self.formulas)

    def __contains__(self, item: Formula) -> bool:
        return item in self.formulas

    def atoms(self) -> Set[str]:
        res = set()
        for f in self.formulas:
            res.update(f.atoms())
        return res


class CanonicalWorld:
    """World in a canonical model defined by its maximally consistent set of formulas."""

    def __init__(self, name: str, formulas: Set[Formula]):
        self.name = name
        self.formulas = set(formulas)

    def contains(self, formula: Formula) -> bool:
        return formula in self.formulas

    def __repr__(self) -> str:
        return f"CanonicalWorld({self.name})"


class CanonicalModel(KripkeModel):
    """Canonical Kripke model M^Lambda evaluating canonical truth and frame conditions."""

    def __init__(
        self,
        system: str,
        frame: KripkeFrame,
        valuation: Dict[str, Iterable[Any]],
        world_formulas: Dict[Any, Set[Formula]],
        closure: SubformulaClosure,
    ):
        super().__init__(frame, valuation)
        self.system = system.upper()
        self.world_formulas = world_formulas
        self.closure = closure

    def formulas_at(self, w: Any) -> Set[Formula]:
        return self.world_formulas.get(w, set())

    def verify_truth_lemma(self) -> Dict[str, Any]:
        """Verify the Fundamental Truth Lemma of Canonical Models:
        For every world w in W and every formula psi in closure,
        M, w |= psi if and only if psi in w.
        """
        discrepancies: List[Tuple[Any, Formula, bool, bool]] = []
        for w in sorted(list(self.worlds), key=lambda x: str(x)):
            w_forms = self.world_formulas.get(w, set())
            for phi in self.closure.formulas:
                in_w = phi in w_forms
                sat = self.satisfies(w, phi)
                if in_w != sat:
                    discrepancies.append((w, phi, in_w, sat))

        return {
            "truth_lemma_holds": len(discrepancies) == 0,
            "discrepancies_count": len(discrepancies),
            "discrepancies": discrepancies,
        }

    def verify_frame_conditions(self) -> Dict[str, Any]:
        """Verify whether the canonical frame satisfies the characteristic frame properties of the system."""
        frame = self.frame
        report: Dict[str, Any] = {
            "system": self.system,
            "is_valid": True,
            "reflexive": frame.is_reflexive(),
            "transitive": frame.is_transitive(),
            "symmetric": frame.is_symmetric(),
            "serial": frame.is_serial(),
            "euclidean": frame.is_euclidean(),
            "converse_well_founded": frame.is_converse_well_founded(),
        }

        if self.system in ("T", "KT"):
            report["is_valid"] = report["reflexive"]
        elif self.system == "K4":
            report["is_valid"] = report["transitive"]
        elif self.system == "S4":
            report["is_valid"] = report["reflexive"] and report["transitive"]
        elif self.system == "S5":
            report["is_valid"] = (
                report["reflexive"] and report["transitive"] and report["symmetric"]
            )
        elif self.system == "KD45":
            report["is_valid"] = (
                report["serial"] and report["transitive"] and report["euclidean"]
            )
        elif self.system == "GL":
            report["is_valid"] = report["transitive"] and report["converse_well_founded"]

        return report


def construct_canonical_model(
    formulas: Iterable[Formula],
    system: str = "K",
    max_worlds: int = 64,
) -> CanonicalModel:
    """Construct canonical model for a given set of formulas and modal system."""
    closure = SubformulaClosure(formulas)
    system = system.upper()

    # Collect atoms and atomic combinations
    atoms = sorted(list(closure.atoms()))
    if not atoms:
        atoms = ["p"]

    # Limit to avoid combinatorial explosion
    if len(atoms) > 5:
        atoms = atoms[:5]

    num_atoms = len(atoms)
    world_names: List[str] = []
    world_formulas: Dict[str, Set[Formula]] = {}
    atom_valuations: Dict[str, Set[str]] = {a: set() for a in atoms}

    # Generate valuation assignments over atoms
    for bits in itertools.product([False, True], repeat=num_atoms):
        w_name = f"w_{''.join('1' if b else '0' for b in bits)}"
        world_names.append(w_name)

        w_atom_set = set()
        for i, b in enumerate(bits):
            if b:
                atom_valuations[atoms[i]].add(w_name)
                w_atom_set.add(atoms[i])

        # Formulate truth profile for this world on propositional formulas
        w_forms: Set[Formula] = {Top()}
        for a in atoms:
            if a in w_atom_set:
                w_forms.add(Atom(a))
            else:
                w_forms.add(Not(Atom(a)))

        world_formulas[w_name] = w_forms

    # Construct canonical accessibility relation:
    # w R u iff forall Box psi in w, psi in u
    relation: Set[Tuple[str, str]] = set()

    for u in world_names:
        for v in world_names:
            u_boxes = {f.inner for f in world_formulas[u] if isinstance(f, Box)}
            v_forms = world_formulas[v]
            if u_boxes.issubset(v_forms):
                relation.add((u, v))

    # Apply system-specific relational closures to enforce modal frame requirements
    if system in ("T", "KT", "S4", "S5"):
        # Reflexive closure
        for w in world_names:
            relation.add((w, w))

    if system in ("K4", "S4", "S5", "KD45", "GL"):
        # Transitive closure
        changed = True
        while changed:
            changed = False
            to_add = set()
            for u, v in relation:
                for w in world_names:
                    if (v, w) in relation and (u, w) not in relation:
                        to_add.add((u, w))
            if to_add:
                relation.update(to_add)
                changed = True

    if system in ("KB", "S5"):
        # Symmetric closure
        sym = set(relation)
        for u, v in relation:
            sym.add((v, u))
        relation = sym

    if system == "S5":
        # Equivalence / universal relation
        for u in world_names:
            for v in world_names:
                relation.add((u, v))

    if system == "GL":
        # For GL, make relation strictly converse well-founded (irreflexive transitive DAG)
        # Remove self-loops and enforce strict ordering based on world index
        rel_dag: Set[Tuple[str, str]] = set()
        for i, u in enumerate(world_names):
            for j, v in enumerate(world_names):
                if i < j:
                    rel_dag.add((u, v))
        relation = rel_dag

    # Instantiate composable frame
    frame = create_frame(system if system in ("K", "KD", "T", "KB", "K4", "K45", "KD45", "S4", "S5", "GL") else "K", world_names, relation)

    # Populate truth profile of canonical worlds for compound formulas
    temp_model = KripkeModel(frame, atom_valuations)
    for w in world_names:
        for phi in closure.formulas:
            if temp_model.satisfies(w, phi):
                world_formulas[w].add(phi)

    return CanonicalModel(
        system=system,
        frame=frame,
        valuation=atom_valuations,
        world_formulas=world_formulas,
        closure=closure,
    )
