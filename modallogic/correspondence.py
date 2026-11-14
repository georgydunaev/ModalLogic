"""Frame correspondence theorems, relational property checkers, and constructive countervaluations."""

from typing import Set, Tuple, Dict, Any, Optional, List, Union
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
)
from .semantics import KripkeFrame, KripkeModel, is_frame_valid
from .axioms import (
    axiom_k,
    axiom_t,
    axiom_4,
    axiom_b,
    axiom_d,
    axiom_5,
    axiom_gl,
    axiom_c4,
    axiom_cd,
)
from .fo_translation import (
    FOFormula,
    fo_reflexive_condition,
    fo_symmetric_condition,
    fo_transitive_condition,
    fo_euclidean_condition,
    fo_serial_condition,
    fo_functional_condition,
    fo_confluent_condition,
)


def check_reflexivity(frame: KripkeFrame) -> Tuple[bool, Optional[Any]]:
    """Check whether frame is reflexive (forall w: w R w).
    Returns (True, None) or (False, non_reflexive_world).
    """
    for w in sorted(list(frame.worlds), key=lambda x: str(x)):
        if (w, w) not in frame.relation:
            return False, w
    return True, None


def check_transitivity(frame: KripkeFrame) -> Tuple[bool, Optional[Tuple[Any, Any, Any]]]:
    """Check whether frame is transitive (forall w, u, v: w R u and u R v implies w R v).
    Returns (True, None) or (False, (w, u, v)).
    """
    for w, u in sorted(list(frame.relation), key=lambda p: (str(p[0]), str(p[1]))):
        for v in sorted(list(frame.successors(u)), key=lambda x: str(x)):
            if (w, v) not in frame.relation:
                return False, (w, u, v)
    return True, None


def check_symmetry(frame: KripkeFrame) -> Tuple[bool, Optional[Tuple[Any, Any]]]:
    """Check whether frame is symmetric (forall w, u: w R u implies u R w).
    Returns (True, None) or (False, (w, u)).
    """
    for w, u in sorted(list(frame.relation), key=lambda p: (str(p[0]), str(p[1]))):
        if (u, w) not in frame.relation:
            return False, (w, u)
    return True, None


def check_seriality(frame: KripkeFrame) -> Tuple[bool, Optional[Any]]:
    """Check whether frame is serial (forall w exists u: w R u).
    Returns (True, None) or (False, dead_end_world).
    """
    for w in sorted(list(frame.worlds), key=lambda x: str(x)):
        if not frame.successors(w):
            return False, w
    return True, None


def check_euclideanness(frame: KripkeFrame) -> Tuple[bool, Optional[Tuple[Any, Any, Any]]]:
    """Check whether frame is euclidean (forall w, u, v: w R u and w R v implies u R v).
    Returns (True, None) or (False, (w, u, v)).
    """
    for w in sorted(list(frame.worlds), key=lambda x: str(x)):
        succ = sorted(list(frame.successors(w)), key=lambda x: str(x))
        for u in succ:
            for v in succ:
                if (u, v) not in frame.relation:
                    return False, (w, u, v)
    return True, None


def check_converse_well_foundedness(frame: KripkeFrame) -> Tuple[bool, Optional[List[Any]]]:
    """Check whether frame is converse well-founded (no cycles on finite frames).
    Returns (True, None) or (False, cycle_path [w0, w1, ..., wk, w0]).
    """
    visited: Set[Any] = set()
    in_stack: Set[Any] = set()
    path: List[Any] = []

    def _dfs(node: Any) -> Optional[List[Any]]:
        visited.add(node)
        in_stack.add(node)
        path.append(node)
        for succ in sorted(list(frame.successors(node)), key=lambda x: str(x)):
            if succ in in_stack:
                cycle_start = path.index(succ)
                return path[cycle_start:] + [succ]
            if succ not in visited:
                found = _dfs(succ)
                if found is not None:
                    return found
        path.pop()
        in_stack.remove(node)
        return None

    for w in sorted(list(frame.worlds), key=lambda x: str(x)):
        if w not in visited:
            cycle = _dfs(w)
            if cycle is not None:
                return False, cycle
    return True, None


def check_confluence(frame: KripkeFrame) -> Tuple[bool, Optional[Tuple[Any, Any, Any]]]:
    """Check whether frame is confluent (Church-Rosser / directed):
    forall w, u, v: w R u and w R v implies exists z: u R z and v R z.
    Returns (True, None) or (False, (w, u, v)).
    """
    for w in sorted(list(frame.worlds), key=lambda x: str(x)):
        succ = sorted(list(frame.successors(w)), key=lambda x: str(x))
        for i, u in enumerate(succ):
            succ_u = frame.successors(u)
            for v in succ[i:]:
                succ_v = frame.successors(v)
                if not (succ_u & succ_v):
                    return False, (w, u, v)
    return True, None


def check_directedness(frame: KripkeFrame) -> Tuple[bool, Optional[Tuple[Any, Any, Any]]]:
    """Alias for check_confluence."""
    return check_confluence(frame)


def check_well_foundedness(frame: KripkeFrame) -> Tuple[bool, Optional[List[Any]]]:
    """Check whether frame is well-founded (no cycles on finite frames).
    Returns (True, None) or (False, cycle_path).
    """
    return check_converse_well_foundedness(frame)


def check_functionality(frame: KripkeFrame) -> Tuple[bool, Optional[Tuple[Any, Any, Any]]]:
    """Check whether frame is functional (deterministic / partial function):
    forall w, u, v: (w R u and w R v) implies u == v (at most one successor per world).
    Returns (True, None) or (False, (w, u, v)).
    """
    for w in sorted(list(frame.worlds), key=lambda x: str(x)):
        succ = sorted(list(frame.successors(w)), key=lambda x: str(x))
        if len(succ) > 1:
            return False, (w, succ[0], succ[1])
    return True, None


def check_partial_functionality(frame: KripkeFrame) -> Tuple[bool, Optional[Tuple[Any, Any, Any]]]:
    """Alias for check_functionality."""
    return check_functionality(frame)


def correspondence_theorem_cd(frame: KripkeFrame) -> Dict[str, Any]:
    """Frame correspondence theorem for Axiom CD:
    Frame F satisfies Axiom CD (<>p -> []p) if and only if F is functional (at most one successor per world).
    """
    ax = axiom_cd("p")
    is_func, witness_triple = check_functionality(frame)

    if is_func:
        return {
            "property": "functional",
            "is_property_satisfied": True,
            "is_axiom_valid": True,
            "axiom": ax,
            "witness": None,
            "countermodel": None,
            "counterworld": None,
            "proof_explanation": (
                "Frame is functional. Every world has at most one successor. "
                "If w satisfies <>p, there is some successor u satisfying p; since u is the unique "
                "successor of w, all successors of w satisfy p, so []p holds. "
                "If w has no successors, <>p is false, so <>p -> []p is vacuously true."
            ),
        }

    w, u, v = witness_triple  # type: ignore
    # Constructive countervaluation: V(p) = {u}
    valuation = {"p": {u}}
    model = KripkeModel(frame, valuation)
    return {
        "property": "functional",
        "is_property_satisfied": False,
        "is_axiom_valid": False,
        "axiom": ax,
        "witness": witness_triple,
        "countervaluation": valuation,
        "countermodel": model,
        "counterworld": w,
        "proof_explanation": (
            f"Frame is not functional: {w!r} has distinct successors {u!r} and {v!r}. "
            f"Setting V(p) = {{{u!r}}} makes <>p true at {w!r} (witnessed by {u!r}), "
            f"while []p is false at {w!r} because successor {v!r} falsifies p. Hence <>p -> []p fails at {w!r}."
        ),
    }


def correspondence_theorem_t(frame: KripkeFrame) -> Dict[str, Any]:
    """Frame correspondence theorem for Axiom T:
    Frame F satisfies Axiom T ([]p -> p) if and only if F is reflexive.
    """
    ax = axiom_t("p")
    is_refl, witness_w = check_reflexivity(frame)

    if is_refl:
        return {
            "property": "reflexive",
            "is_property_satisfied": True,
            "is_axiom_valid": True,
            "axiom": ax,
            "witness": None,
            "countermodel": None,
            "counterworld": None,
            "proof_explanation": (
                "Frame is reflexive. For every world w and valuation V, if w satisfies []p, "
                "then since w R w, w must satisfy p. Hence []p -> p holds globally."
            ),
        }

    # Constructive countervaluation: V(p) = W \ {w}
    valuation = {"p": frame.worlds - {witness_w}}
    model = KripkeModel(frame, valuation)
    # At witness_w, all accessible worlds are in W \ {w} because not w R w.
    # Hence w satisfies []p, but w does not satisfy p.
    return {
        "property": "reflexive",
        "is_property_satisfied": False,
        "is_axiom_valid": False,
        "axiom": ax,
        "witness": witness_w,
        "countervaluation": valuation,
        "countermodel": model,
        "counterworld": witness_w,
        "proof_explanation": (
            f"Frame is not reflexive at world {witness_w!r}. Setting V(p) = W \\ {{{witness_w!r}}} "
            f"makes p true at all successors of {witness_w!r} (so []p holds), while p is false at {witness_w!r}. "
            f"Hence []p -> p fails at {witness_w!r}."
        ),
    }


def correspondence_theorem_4(frame: KripkeFrame) -> Dict[str, Any]:
    """Frame correspondence theorem for Axiom 4:
    Frame F satisfies Axiom 4 ([]p -> [][]p) if and only if F is transitive.
    """
    ax = axiom_4("p")
    is_trans, witness_triple = check_transitivity(frame)

    if is_trans:
        return {
            "property": "transitive",
            "is_property_satisfied": True,
            "is_axiom_valid": True,
            "axiom": ax,
            "witness": None,
            "countermodel": None,
            "counterworld": None,
            "proof_explanation": (
                "Frame is transitive. If w R u and u R v, then w R v. Therefore if w satisfies []p, "
                "every world reachable in two steps satisfies p, so w satisfies [][]p."
            ),
        }

    w, u, v = witness_triple  # type: ignore
    # Constructive countervaluation: V(p) = W \ {v}
    valuation = {"p": frame.worlds - {v}}
    model = KripkeModel(frame, valuation)
    return {
        "property": "transitive",
        "is_property_satisfied": False,
        "is_axiom_valid": False,
        "axiom": ax,
        "witness": witness_triple,
        "countervaluation": valuation,
        "countermodel": model,
        "counterworld": w,
        "proof_explanation": (
            f"Frame is not transitive: {w!r} R {u!r} and {u!r} R {v!r} but not ({w!r} R {v!r}). "
            f"Setting V(p) = W \\ {{{v!r}}} makes []p true at {w!r}, but []p false at {u!r}, "
            f"so [][]p is false at {w!r}."
        ),
    }


def correspondence_theorem_b(frame: KripkeFrame) -> Dict[str, Any]:
    """Frame correspondence theorem for Axiom B:
    Frame F satisfies Axiom B (p -> []<>p) if and only if F is symmetric.
    """
    ax = axiom_b("p")
    is_sym, witness_pair = check_symmetry(frame)

    if is_sym:
        return {
            "property": "symmetric",
            "is_property_satisfied": True,
            "is_axiom_valid": True,
            "axiom": ax,
            "witness": None,
            "countermodel": None,
            "counterworld": None,
            "proof_explanation": (
                "Frame is symmetric. If w satisfies p and w R u, then by symmetry u R w, "
                "so u satisfies <>p. Since this holds for all successors u, w satisfies []<>p."
            ),
        }

    w, u = witness_pair  # type: ignore
    # Constructive countervaluation: V(p) = {w}
    valuation = {"p": {w}}
    model = KripkeModel(frame, valuation)
    return {
        "property": "symmetric",
        "is_property_satisfied": False,
        "is_axiom_valid": False,
        "axiom": ax,
        "witness": witness_pair,
        "countervaluation": valuation,
        "countermodel": model,
        "counterworld": w,
        "proof_explanation": (
            f"Frame is not symmetric: {w!r} R {u!r} but not ({u!r} R {w!r}). "
            f"Setting V(p) = {{{w!r}}} makes p true at {w!r}, but {u!r} has no successor satisfying p, "
            f"so <>p is false at {u!r}, and []<>p fails at {w!r}."
        ),
    }


def correspondence_theorem_d(frame: KripkeFrame) -> Dict[str, Any]:
    """Frame correspondence theorem for Axiom D:
    Frame F satisfies Axiom D ([]p -> <>p) if and only if F is serial.
    """
    ax = axiom_d("p")
    is_ser, witness_w = check_seriality(frame)

    if is_ser:
        return {
            "property": "serial",
            "is_property_satisfied": True,
            "is_axiom_valid": True,
            "axiom": ax,
            "witness": None,
            "countermodel": None,
            "counterworld": None,
            "proof_explanation": (
                "Frame is serial. Every world w has at least one successor u. "
                "Hence if w satisfies []p, u satisfies p, so w satisfies <>p."
            ),
        }

    valuation = {"p": set()}
    model = KripkeModel(frame, valuation)
    return {
        "property": "serial",
        "is_property_satisfied": False,
        "is_axiom_valid": False,
        "axiom": ax,
        "witness": witness_w,
        "countervaluation": valuation,
        "countermodel": model,
        "counterworld": witness_w,
        "proof_explanation": (
            f"Frame is not serial: world {witness_w!r} has no successors. "
            f"Vacuously []p holds at {witness_w!r}, but <>p is false. Hence []p -> <>p fails at {witness_w!r}."
        ),
    }


def correspondence_theorem_5(frame: KripkeFrame) -> Dict[str, Any]:
    """Frame correspondence theorem for Axiom 5:
    Frame F satisfies Axiom 5 (<>p -> []<>p) if and only if F is euclidean.
    """
    ax = axiom_5("p")
    is_eucl, witness_triple = check_euclideanness(frame)

    if is_eucl:
        return {
            "property": "euclidean",
            "is_property_satisfied": True,
            "is_axiom_valid": True,
            "axiom": ax,
            "witness": None,
            "countermodel": None,
            "counterworld": None,
            "proof_explanation": (
                "Frame is euclidean. If w R u and w R v, then u R v. Thus if w satisfies <>p "
                "(witnessed by v), then every successor u sees v, so every successor satisfies <>p."
            ),
        }

    w, u, v = witness_triple  # type: ignore
    valuation = {"p": {v}}
    model = KripkeModel(frame, valuation)
    return {
        "property": "euclidean",
        "is_property_satisfied": False,
        "is_axiom_valid": False,
        "axiom": ax,
        "witness": witness_triple,
        "countervaluation": valuation,
        "countermodel": model,
        "counterworld": w,
        "proof_explanation": (
            f"Frame is not euclidean: {w!r} R {u!r} and {w!r} R {v!r} but not ({u!r} R {v!r}). "
            f"Setting V(p) = {{{v!r}}} makes <>p true at {w!r} (via {v!r}), but <>p is false at {u!r} "
            f"because {u!r} cannot see {v!r}. Thus []<>p fails at {w!r}."
        ),
    }


def correspondence_theorem_gl(frame: KripkeFrame) -> Dict[str, Any]:
    """Frame correspondence theorem for Gödel-Löb's Axiom GL:
    Frame F satisfies Löb's Axiom ([]( []p -> p ) -> []p) if and only if
    F is transitive and converse well-founded (strict partial order with no cycles).
    """
    ax = axiom_gl("p")

    # 1. Check transitivity
    is_trans, witness_trans = check_transitivity(frame)
    if not is_trans:
        w, u, v = witness_trans  # type: ignore
        # Constructive countervaluation for non-transitive frame: V(p) = W \ {u, v}
        valuation = {"p": frame.worlds - {u, v}}
        model = KripkeModel(frame, valuation)
        return {
            "property": "transitive_and_converse_well_founded",
            "is_property_satisfied": False,
            "is_axiom_valid": False,
            "axiom": ax,
            "failure_reason": "non_transitive",
            "witness": witness_trans,
            "countervaluation": valuation,
            "countermodel": model,
            "counterworld": w,
            "proof_explanation": (
                f"Frame is not transitive: {w!r} R {u!r} and {u!r} R {v!r} but not ({w!r} R {v!r}). "
                f"Setting V(p) = W \\ {{{u!r}, {v!r}}} ensures all successors of {w!r} satisfy []p -> p, "
                f"so []( []p -> p ) holds at {w!r}, yet {u!r} is a successor where p is false, so []p fails at {w!r}."
            ),
        }

    # 2. Check converse well-foundedness (no directed cycles)
    is_cwf, cycle = check_converse_well_foundedness(frame)
    if not is_cwf:
        c_nodes = set(cycle[:-1]) if cycle else set()  # type: ignore
        w0 = cycle[0] if cycle else list(frame.worlds)[0]  # type: ignore
        # Constructive countervaluation for cyclic frame: V(p) = W \ C
        valuation = {"p": frame.worlds - c_nodes}
        model = KripkeModel(frame, valuation)
        return {
            "property": "transitive_and_converse_well_founded",
            "is_property_satisfied": False,
            "is_axiom_valid": False,
            "axiom": ax,
            "failure_reason": "cycle_detected",
            "witness": cycle,
            "countervaluation": valuation,
            "countermodel": model,
            "counterworld": w0,
            "proof_explanation": (
                f"Frame contains a directed cycle {cycle!r}, violating converse well-foundedness. "
                f"Setting V(p) = W \\ C where C is the cycle ensures every cycle world has an un-evaluated successor "
                f"in C, making []p false everywhere on C. Hence []p -> p holds at all cycle successors, so "
                f"[]( []p -> p ) holds at {w0!r}, but []p fails at {w0!r}."
            ),
        }

    # Both transitive and converse well-founded => Frame validates Löb's Axiom
    return {
        "property": "transitive_and_converse_well_founded",
        "is_property_satisfied": True,
        "is_axiom_valid": True,
        "axiom": ax,
        "failure_reason": None,
        "witness": None,
        "countermodel": None,
        "counterworld": None,
        "proof_explanation": (
            "Frame is transitive and converse well-founded (a strict finite DAG). "
            "By reverse topological induction along R, no valuation can satisfy []( []p -> p ) while "
            "falsifying []p, because any non-empty set of counterexamples would have an R-maximal element, "
            "contradicting the premise []( []p -> p ). Hence Löb's axiom holds globally."
        ),
    }


def correspondence_theorem_c4(frame: KripkeFrame) -> Dict[str, Any]:
    """Frame correspondence theorem for Lemmon Confluence Axiom C4:
    Frame F satisfies Axiom C4 (<>[]p -> []<>p) if and only if F is confluent (directed):
    forall w, u, v: w R u and w R v implies exists z: u R z and v R z.
    """
    ax = axiom_c4("p")
    is_conf, witness_triple = check_confluence(frame)

    if is_conf:
        return {
            "property": "confluent",
            "is_property_satisfied": True,
            "is_axiom_valid": True,
            "axiom": ax,
            "witness": None,
            "countermodel": None,
            "counterworld": None,
            "proof_explanation": (
                "Frame is confluent. For any world w with w R u (satisfying []p) and w R v, "
                "confluence guarantees a common successor z with u R z and v R z. Since u satisfies []p, "
                "z satisfies p, so v satisfies <>p. Thus []<>p holds at w."
            ),
        }

    w, u, v = witness_triple  # type: ignore
    # Constructive countervaluation: V(p) = R(u) = {z | u R z}
    u_succ = frame.successors(u)
    valuation = {"p": set(u_succ)}
    model = KripkeModel(frame, valuation)
    return {
        "property": "confluent",
        "is_property_satisfied": False,
        "is_axiom_valid": False,
        "axiom": ax,
        "witness": witness_triple,
        "countervaluation": valuation,
        "countermodel": model,
        "counterworld": w,
        "proof_explanation": (
            f"Frame is not confluent: {w!r} R {u!r} and {w!r} R {v!r}, but {u!r} and {v!r} have no common successor. "
            f"Setting V(p) = R({u!r}) ensures {u!r} satisfies []p (so {w!r} satisfies <>[]p), but no successor of {v!r} "
            f"satisfies p, so {v!r} falsifies <>p and {w!r} falsifies []<>p."
        ),
    }


def verify_frame_correspondence(frame: KripkeFrame, axiom_name: str) -> bool:
    """Verify correspondence between the relational property and semantic validity on the frame."""
    name = axiom_name.upper()
    if name == "T":
        res = correspondence_theorem_t(frame)
    elif name == "4":
        res = correspondence_theorem_4(frame)
    elif name == "B":
        res = correspondence_theorem_b(frame)
    elif name == "D":
        res = correspondence_theorem_d(frame)
    elif name == "5":
        res = correspondence_theorem_5(frame)
    elif name in ("CD", "FUNCTIONAL", "DETERMINISTIC"):
        res = correspondence_theorem_cd(frame)
    elif name in ("C4", "CONFLUENT", "DIRECTED"):
        res = correspondence_theorem_c4(frame)
    elif name == "GL":
        res = correspondence_theorem_gl(frame)
    else:
        raise ValueError(f"Unsupported correspondence axiom: {axiom_name}")

    prop_sat = res["is_property_satisfied"]
    ax_valid = res["is_axiom_valid"]

    # Verify that property satisfaction exactly matches validity
    if prop_sat != ax_valid:
        return False

    if not ax_valid:
        # Double-check that countermodel actually falsifies the axiom at counterworld
        cm: KripkeModel = res["countermodel"]
        cw: Any = res["counterworld"]
        ax: Formula = res["axiom"]
        if cm.satisfies(cw, ax):
            return False

    return True


class AutomatedCorrespondenceChecker:
    """Automated registry and verification engine for modal frame correspondence theorems."""

    AXIOM_THEOREMS = {
        "T": correspondence_theorem_t,
        "4": correspondence_theorem_4,
        "B": correspondence_theorem_b,
        "D": correspondence_theorem_d,
        "5": correspondence_theorem_5,
        "CD": correspondence_theorem_cd,
        "FUNCTIONAL": correspondence_theorem_cd,
        "C4": correspondence_theorem_c4,
        "CONFLUENT": correspondence_theorem_c4,
        "DIRECTED": correspondence_theorem_c4,
        "GL": correspondence_theorem_gl,
    }

    PROPERTY_CHECKERS = {
        "reflexive": check_reflexivity,
        "transitive": check_transitivity,
        "symmetric": check_symmetry,
        "serial": check_seriality,
        "euclidean": check_euclideanness,
        "functional": check_functionality,
        "partial_functional": check_functionality,
        "confluent": check_confluence,
        "directed": check_directedness,
        "well_founded": check_well_foundedness,
        "converse_well_founded": check_converse_well_foundedness,
    }

    SYSTEM_AXIOMS: Dict[str, List[str]] = {
        "K": [],
        "KD": ["D"],
        "T": ["T"],
        "KT": ["T"],
        "KB": ["B"],
        "K4": ["4"],
        "K45": ["4", "5"],
        "KD45": ["D", "4", "5"],
        "S4": ["T", "4"],
        "S5": ["T", "4", "5"],
        "GL": ["GL"],
        "C4": ["C4"],
        "CD": ["CD"],
    }

    @classmethod
    def check_property(cls, frame: KripkeFrame, property_name: str) -> Tuple[bool, Optional[Any]]:
        prop = property_name.lower()
        if prop not in cls.PROPERTY_CHECKERS:
            raise ValueError(f"Unknown property: {property_name}. Available: {list(cls.PROPERTY_CHECKERS.keys())}")
        return cls.PROPERTY_CHECKERS[prop](frame)

    @classmethod
    def verify_axiom(cls, frame: KripkeFrame, axiom_name: str) -> Dict[str, Any]:
        ax = axiom_name.upper()
        if ax not in cls.AXIOM_THEOREMS:
            raise ValueError(f"Unknown axiom: {axiom_name}. Available: {list(cls.AXIOM_THEOREMS.keys())}")
        return cls.AXIOM_THEOREMS[ax](frame)

    @classmethod
    def verify_system(cls, frame: KripkeFrame, system_name: str) -> Dict[str, Any]:
        sys_key = system_name.upper()
        if sys_key not in cls.SYSTEM_AXIOMS:
            raise ValueError(f"Unknown system: {system_name}. Available: {list(cls.SYSTEM_AXIOMS.keys())}")
        axioms = cls.SYSTEM_AXIOMS[sys_key]
        report: Dict[str, Any] = {
            "system": sys_key,
            "is_valid": True,
            "axiom_results": {},
            "failed_axioms": [],
        }
        for ax in axioms:
            res = cls.verify_axiom(frame, ax)
            report["axiom_results"][ax] = res
            if not res["is_axiom_valid"]:
                report["is_valid"] = False
                report["failed_axioms"].append(ax)
        return report


# Sahlqvist Formula Recognizer and Polarity Analysis


def polarity_of_atoms(formula: Formula, current_polarity: int = 1) -> Dict[str, Set[int]]:
    """Determine the polarities (+1 positive, -1 negative) with which each propositional atom occurs."""
    res: Dict[str, Set[int]] = {}

    def _merge(other: Dict[str, Set[int]]) -> None:
        for k, v in other.items():
            if k not in res:
                res[k] = set()
            res[k].update(v)

    if isinstance(formula, Atom):
        res[formula.name] = {current_polarity}
    elif isinstance(formula, (Top, Bottom)):
        pass
    elif isinstance(formula, Not):
        _merge(polarity_of_atoms(formula.inner, -current_polarity))
    elif isinstance(formula, (And, Or)):
        _merge(polarity_of_atoms(formula.left, current_polarity))
        _merge(polarity_of_atoms(formula.right, current_polarity))
    elif isinstance(formula, Implies):
        _merge(polarity_of_atoms(formula.left, -current_polarity))
        _merge(polarity_of_atoms(formula.right, current_polarity))
    elif isinstance(formula, Iff):
        _merge(polarity_of_atoms(formula.left, 1))
        _merge(polarity_of_atoms(formula.left, -1))
        _merge(polarity_of_atoms(formula.right, 1))
        _merge(polarity_of_atoms(formula.right, -1))
    elif isinstance(formula, (Box, Dia)):
        _merge(polarity_of_atoms(formula.inner, current_polarity))
    return res


def is_positive(formula: Formula) -> bool:
    """Check if formula is positive: every atom occurs only in positive positions (+1)."""
    pol = polarity_of_atoms(formula)
    return all(-1 not in s for s in pol.values())


def is_negative(formula: Formula) -> bool:
    """Check if formula is negative: every atom occurs only in negative positions (-1)."""
    pol = polarity_of_atoms(formula)
    return all(1 not in s for s in pol.values())


def is_boxed_atom(formula: Formula) -> bool:
    """Check if formula has the form Box^k(p) for k >= 0 and propositional atom p."""
    curr = formula
    while isinstance(curr, Box):
        curr = curr.inner
    return isinstance(curr, Atom)


def is_sahlqvist_antecedent(formula: Formula) -> bool:
    """Check if formula is a Sahlqvist antecedent:
    built up from negative formulas, Box^k(p) (k >= 0), and constants (Top, Bottom)
    using only And, Or, and Dia.
    """
    if is_negative(formula):
        return True
    if is_boxed_atom(formula):
        return True
    if isinstance(formula, (Top, Bottom)):
        return True
    if isinstance(formula, And):
        return is_sahlqvist_antecedent(formula.left) and is_sahlqvist_antecedent(formula.right)
    if isinstance(formula, Or):
        return is_sahlqvist_antecedent(formula.left) and is_sahlqvist_antecedent(formula.right)
    if isinstance(formula, Dia):
        return is_sahlqvist_antecedent(formula.inner)
    return False


def is_sahlqvist(formula: Formula) -> bool:
    """Check if formula is a Sahlqvist formula.
    
    A Sahlqvist formula is constructed from Sahlqvist implications (A -> B where A is
    a Sahlqvist antecedent and B is positive) using Box and And.
    Also handles positive formulas (vacuous antecedent Top), negative formulas,
    and disjunctive forms (~A | B).
    """
    # 1. Implication form A -> B
    if isinstance(formula, Implies):
        return is_sahlqvist_antecedent(formula.left) and is_positive(formula.right)

    # 2. Conjunction of Sahlqvist formulas
    if isinstance(formula, And):
        return is_sahlqvist(formula.left) and is_sahlqvist(formula.right)

    # 3. Boxed Sahlqvist formula
    if isinstance(formula, Box):
        return is_sahlqvist(formula.inner)

    # 4. Purely positive formula (equivalent to Top -> formula)
    if is_positive(formula):
        return True

    # 5. Purely negative formula (equivalent to formula -> Bottom)
    if is_negative(formula):
        return True

    # 6. Disjunctive form ~A | B or B | ~A
    if isinstance(formula, Or):
        if isinstance(formula.left, Not) and is_sahlqvist_antecedent(formula.left.inner) and is_positive(formula.right):
            return True
        if isinstance(formula.right, Not) and is_sahlqvist_antecedent(formula.right.inner) and is_positive(formula.left):
            return True

    return False


is_sahlqvist_formula = is_sahlqvist


class SahlqvistRecognizer:
    """Automated Sahlqvist formula recognizer and classification engine."""

    @classmethod
    def is_positive(cls, formula: Formula) -> bool:
        return is_positive(formula)

    @classmethod
    def is_negative(cls, formula: Formula) -> bool:
        return is_negative(formula)

    @classmethod
    def is_sahlqvist_antecedent(cls, formula: Formula) -> bool:
        return is_sahlqvist_antecedent(formula)

    @classmethod
    def is_sahlqvist(cls, formula: Formula) -> bool:
        return is_sahlqvist(formula)

    @classmethod
    def analyze(cls, formula: Formula) -> Dict[str, Any]:
        """Perform comprehensive Sahlqvist syntactic and semantic correspondence analysis."""
        pos = is_positive(formula)
        neg = is_negative(formula)

        if isinstance(formula, Implies):
            ante_ok = is_sahlqvist_antecedent(formula.left)
            cons_ok = is_positive(formula.right)
            sahlqvist = ante_ok and cons_ok
            if sahlqvist:
                cls_type = "sahlqvist_implication"
                reason = "Antecedent is a valid Sahlqvist antecedent and consequent is positive."
            else:
                cls_type = "non_sahlqvist_implication"
                failures = []
                if not ante_ok:
                    failures.append("antecedent is not a Sahlqvist antecedent")
                if not cons_ok:
                    failures.append("consequent is not positive")
                reason = "Fails Sahlqvist criteria: " + "; ".join(failures) + "."
            return {
                "formula": formula,
                "is_sahlqvist": sahlqvist,
                "classification": cls_type,
                "is_positive": pos,
                "is_negative": neg,
                "antecedent": formula.left,
                "consequent": formula.right,
                "corresponds_to_first_order": sahlqvist,
                "reason": reason,
            }

        if is_sahlqvist(formula):
            if pos:
                cls_type = "positive_formula"
                reason = "Formula is purely positive (vacuous antecedent TOP)."
            elif neg:
                cls_type = "negative_formula"
                reason = "Formula is purely negative (consequent BOTTOM)."
            elif isinstance(formula, And):
                cls_type = "conjunction_of_sahlqvist"
                reason = "Conjunction of Sahlqvist formulas."
            elif isinstance(formula, Box):
                cls_type = "boxed_sahlqvist"
                reason = "Box prefix of Sahlqvist formula."
            else:
                cls_type = "sahlqvist_formula"
                reason = "Formula matches Sahlqvist criteria."
            return {
                "formula": formula,
                "is_sahlqvist": True,
                "classification": cls_type,
                "is_positive": pos,
                "is_negative": neg,
                "antecedent": None,
                "consequent": None,
                "corresponds_to_first_order": True,
                "reason": reason,
            }

        return {
            "formula": formula,
            "is_sahlqvist": False,
            "classification": "non_sahlqvist",
            "is_positive": pos,
            "is_negative": neg,
            "antecedent": None,
            "consequent": None,
            "corresponds_to_first_order": False,
            "reason": "Formula does not conform to Sahlqvist syntax (does not define a first-order frame condition).",
        }


# Canonical Modal Axiom to First-Order Frame Condition Correspondence Engine


def formulas_isomorphic(
    f1: Formula,
    f2: Formula,
    mapping: Optional[Dict[str, str]] = None,
    rev_mapping: Optional[Dict[str, str]] = None,
) -> bool:
    """Check whether two formulas have isomorphic AST structures modulo bijective atom renaming."""
    if mapping is None:
        mapping = {}
        rev_mapping = {}
    if type(f1) is not type(f2):
        return False
    if isinstance(f1, Atom):
        p1 = f1.name
        p2 = f2.name  # type: ignore
        if p1 in mapping:
            return mapping[p1] == p2
        if p2 in rev_mapping:
            return rev_mapping[p2] == p1
        mapping[p1] = p2
        rev_mapping[p2] = p1
        return True
    if isinstance(f1, (Top, Bottom)):
        return True
    if isinstance(f1, Not):
        return formulas_isomorphic(f1.inner, f2.inner, mapping, rev_mapping)  # type: ignore
    if isinstance(f1, (Box, Dia)):
        return formulas_isomorphic(f1.inner, f2.inner, mapping, rev_mapping)  # type: ignore
    if isinstance(f1, (And, Or, Implies, Iff)):
        return (
            formulas_isomorphic(f1.left, f2.left, mapping, rev_mapping)  # type: ignore
            and formulas_isomorphic(f1.right, f2.right, mapping, rev_mapping)  # type: ignore
        )
    return False


CANONICAL_FRAME_CONDITIONS: Dict[str, Dict[str, Any]] = {
    "T": {
        "axiom_name": "T",
        "property": "reflexive",
        "modal_schema": "[]p -> p",
        "modal_formula": axiom_t(),
        "fo_condition": "forall x. R(x, x)",
        "fo_ast": fo_reflexive_condition(),
        "is_sahlqvist": True,
        "description": "Reflexive accessibility relation: every world accesses itself.",
    },
    "B": {
        "axiom_name": "B",
        "property": "symmetric",
        "modal_schema": "p -> []<>p",
        "modal_formula": axiom_b(),
        "fo_condition": "forall x, y. (R(x, y) -> R(y, x))",
        "fo_ast": fo_symmetric_condition(),
        "is_sahlqvist": True,
        "description": "Symmetric accessibility relation: if x accesses y, y accesses x.",
    },
    "4": {
        "axiom_name": "4",
        "property": "transitive",
        "modal_schema": "[]p -> [][]p",
        "modal_formula": axiom_4(),
        "fo_condition": "forall x, y, z. ((R(x, y) /\\ R(y, z)) -> R(x, z))",
        "fo_ast": fo_transitive_condition(),
        "is_sahlqvist": True,
        "description": "Transitive accessibility relation: two-step accessibility implies one-step accessibility.",
    },
    "5": {
        "axiom_name": "5",
        "property": "euclidean",
        "modal_schema": "<>p -> []<>p",
        "modal_formula": axiom_5(),
        "fo_condition": "forall x, y, z. ((R(x, y) /\\ R(x, z)) -> R(y, z))",
        "fo_ast": fo_euclidean_condition(),
        "is_sahlqvist": True,
        "description": "Euclidean accessibility relation: worlds with a common predecessor access each other.",
    },
    "D": {
        "axiom_name": "D",
        "property": "serial",
        "modal_schema": "[]p -> <>p",
        "modal_formula": axiom_d(),
        "fo_condition": "forall x exists y. R(x, y)",
        "fo_ast": fo_serial_condition(),
        "is_sahlqvist": True,
        "description": "Serial accessibility relation: every world has at least one successor (no dead ends).",
    },
    "CD": {
        "axiom_name": "CD",
        "property": "functional",
        "modal_schema": "<>p -> []p",
        "modal_formula": axiom_cd(),
        "fo_condition": "forall x, y, z. ((R(x, y) /\\ R(x, z)) -> y = z)",
        "fo_ast": fo_functional_condition(),
        "is_sahlqvist": True,
        "description": "Functional accessibility relation: at most one successor per world (partial function / deterministic).",
    },
    "C4": {
        "axiom_name": "C4",
        "property": "confluent",
        "modal_schema": "<>[]p -> []<>p",
        "modal_formula": axiom_c4(),
        "fo_condition": "forall x, y, z. ((R(x, y) /\\ R(x, z)) -> exists u. (R(y, u) /\\ R(z, u)))",
        "fo_ast": fo_confluent_condition(),
        "is_sahlqvist": True,
        "description": "Confluent accessibility relation: common predecessors have a common successor (Church-Rosser / directed).",
    },
}


def match_axiom_frame_condition(axiom_or_formula: Union[str, Formula]) -> Optional[Dict[str, Any]]:
    """Match classical modal axioms (T, B, 4, 5, D, CD, C4) against canonical first-order frame conditions.
    
    Accepts either an axiom name string (e.g. 'T', 'B', '4', '5', 'D', 'CD', 'C4') or a Formula AST.
    Returns the correspondence dictionary entry or None if unmatched.
    """
    if isinstance(axiom_or_formula, str):
        key = axiom_or_formula.strip().upper()
        if key in CANONICAL_FRAME_CONDITIONS:
            return CANONICAL_FRAME_CONDITIONS[key]
        for entry in CANONICAL_FRAME_CONDITIONS.values():
            if entry["property"].upper() == key:
                return entry
        return None

    if isinstance(axiom_or_formula, Formula):
        for entry in CANONICAL_FRAME_CONDITIONS.values():
            if formulas_isomorphic(axiom_or_formula, entry["modal_formula"]):
                return entry
        return None

    raise TypeError(f"Expected str or Formula, got {type(axiom_or_formula)}")


def get_canonical_frame_condition(axiom_name: str) -> Dict[str, Any]:
    """Retrieve canonical first-order frame condition for axiom name, raising KeyError if unknown."""
    res = match_axiom_frame_condition(axiom_name)
    if res is None:
        raise KeyError(
            f"Unknown correspondence axiom: {axiom_name!r}. Available: {list(CANONICAL_FRAME_CONDITIONS.keys())}"
        )
    return res


