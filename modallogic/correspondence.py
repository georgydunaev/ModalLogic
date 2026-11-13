"""Frame correspondence theorems, relational property checkers, and constructive countervaluations."""

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

