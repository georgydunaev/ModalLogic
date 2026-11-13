"""Bisimulation verifier, maximal bisimulation fixed-point calculator, and quotient models."""

from typing import Set, Tuple, Any, Optional, List, Dict
from collections import defaultdict
from .syntax import Formula
from .semantics import KripkeModel, KripkeFrame


def is_bisimulation(
    model1: KripkeModel,
    model2: KripkeModel,
    relation: Set[Tuple[Any, Any]],
) -> Tuple[bool, Optional[str]]:
    """Check whether a given relation Z subset W1 x W2 is a bisimulation.

    Returns (True, None) if Z is a bisimulation, or (False, reason) if violated.
    """
    all_atoms = set(model1.valuation.keys()) | set(model2.valuation.keys())

    for w1, w2 in relation:
        if w1 not in model1.worlds:
            return False, f"World {w1!r} in relation does not exist in model 1"
        if w2 not in model2.worlds:
            return False, f"World {w2!r} in relation does not exist in model 2"

        # 1. Atomic agreement
        for p in all_atoms:
            in1 = w1 in model1.valuation.get(p, set())
            in2 = w2 in model2.valuation.get(p, set())
            if in1 != in2:
                return (
                    False,
                    f"Atomic valuation mismatch on atom {p!r} for pair ({w1!r}, {w2!r}): "
                    f"model1={in1}, model2={in2}",
                )

        # 2. Forth condition: forall u1 with w1 R1 u1, exists u2 with w2 R2 u2 and (u1, u2) in Z
        for u1 in model1.frame.successors(w1):
            matched = any((u1, u2) in relation for u2 in model2.frame.successors(w2))
            if not matched:
                return (
                    False,
                    f"Forth condition failed: from ({w1!r}, {w2!r}), step {w1!r} R1 {u1!r} "
                    f"has no Z-matching successor in model2",
                )

        # 3. Back condition: forall u2 with w2 R2 u2, exists u1 with w1 R1 u1 and (u1, u2) in Z
        for u2 in model2.frame.successors(w2):
            matched = any((u1, u2) in relation for u1 in model1.frame.successors(w1))
            if not matched:
                return (
                    False,
                    f"Back condition failed: from ({w1!r}, {w2!r}), step {w2!r} R2 {u2!r} "
                    f"has no Z-matching successor in model1",
                )

    return True, None


def compute_maximal_bisimulation(
    model1: KripkeModel,
    model2: KripkeModel,
) -> Set[Tuple[Any, Any]]:
    """Compute the maximal bisimulation relation between two finite Kripke models.

    Uses iterative greatest fixed-point refinement starting from all pairs
    agreeing on atomic propositions.
    """
    all_atoms = set(model1.valuation.keys()) | set(model2.valuation.keys())

    # Step 0: Initial relation Z0 consists of all pairs with identical atomic valuations
    current_z: Set[Tuple[Any, Any]] = set()
    for w1 in model1.worlds:
        for w2 in model2.worlds:
            agrees = True
            for p in all_atoms:
                in1 = w1 in model1.valuation.get(p, set())
                in2 = w2 in model2.valuation.get(p, set())
                if in1 != in2:
                    agrees = False
                    break
            if agrees:
                current_z.add((w1, w2))

    # Refinement loop
    while True:
        next_z: Set[Tuple[Any, Any]] = set()
        for w1, w2 in current_z:
            # Forth
            forth_ok = True
            for u1 in model1.frame.successors(w1):
                if not any((u1, u2) in current_z for u2 in model2.frame.successors(w2)):
                    forth_ok = False
                    break
            if not forth_ok:
                continue

            # Back
            back_ok = True
            for u2 in model2.frame.successors(w2):
                if not any((u1, u2) in current_z for u1 in model1.frame.successors(w1)):
                    back_ok = False
                    break
            if not back_ok:
                continue

            next_z.add((w1, w2))

        if next_z == current_z:
            break
        current_z = next_z

    return current_z


def are_bisimilar(model1: KripkeModel, w1: Any, model2: KripkeModel, w2: Any) -> bool:
    """Check if world w1 in model1 is bisimilar to world w2 in model2."""
    max_bisim = compute_maximal_bisimulation(model1, model2)
    return (w1, w2) in max_bisim


def bisimulation_quotient(model: KripkeModel) -> KripkeModel:
    """Compute the minimal bisimilar quotient model of a finite Kripke model."""
    auto_bisim = compute_maximal_bisimulation(model, model)

    # Compute equivalence classes of worlds under auto_bisim
    visited = set()
    classes: List[Set[Any]] = []
    class_map: Dict[Any, int] = {}

    for w in sorted(list(model.worlds), key=lambda x: str(x)):
        if w not in visited:
            eq_class = {u for u in model.worlds if (w, u) in auto_bisim}
            class_id = len(classes)
            classes.append(eq_class)
            for u in eq_class:
                visited.add(u)
                class_map[u] = class_id

    quotient_worlds = {f"q{i}" for i in range(len(classes))}
    quotient_relation: Set[Tuple[str, str]] = set()

    for i, eq_i in enumerate(classes):
        for j, eq_j in enumerate(classes):
            # There is a relation q_i -> q_j iff exists w in eq_i and u in eq_j such that w R u
            connected = any(
                u in model.frame.successors(w)
                for w in eq_i
                for u in eq_j
            )
            if connected:
                quotient_relation.add((f"q{i}", f"q{j}"))

    quotient_valuation: Dict[str, Set[str]] = defaultdict(set)
    for p, ws in model.valuation.items():
        for i, eq_i in enumerate(classes):
            # By bisimulation, all worlds in eq_i agree on atom p
            rep = next(iter(eq_i))
            if rep in ws:
                quotient_valuation[p].add(f"q{i}")

    quotient_frame = KripkeFrame(quotient_worlds, quotient_relation)
    return KripkeModel(quotient_frame, dict(quotient_valuation))


def verify_modal_invariance(
    model1: KripkeModel,
    model2: KripkeModel,
    bisim: Set[Tuple[Any, Any]],
    formulas: List[Formula],
) -> Tuple[bool, Optional[str]]:
    """Verify the Hennessy-Milner modal invariance theorem on a set of test formulas:
    For all (w1, w2) in bisim: model1, w1 |= phi <=> model2, w2 |= phi.
    """
    for phi in formulas:
        for w1, w2 in bisim:
            sat1 = model1.satisfies(w1, phi)
            sat2 = model2.satisfies(w2, phi)
            if sat1 != sat2:
                return (
                    False,
                    f"Modal invariance failed for formula {phi!r} on pair ({w1!r}, {w2!r}): "
                    f"model1={sat1}, model2={sat2}",
                )
    return True, None
