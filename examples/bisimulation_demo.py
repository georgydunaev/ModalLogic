#!/usr/bin/env python3
"""Example demonstration of bisimulations and quotient models."""

import os
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
if ROOT not in sys.path:
    sys.path.insert(0, ROOT)

from modallogic.syntax import parse_formula
from modallogic.semantics import KripkeFrame, KripkeModel
from modallogic.bisimulation import (
    compute_maximal_bisimulation,
    bisimulation_quotient,
    verify_modal_invariance,
)


def main():
    print("=== ModalLogic: Bisimulation & Model Minimization ===")

    # Model 1: 2 worlds: w0 -> w1
    f1 = KripkeFrame(worlds=["w0", "w1"], relation=[("w0", "w1")])
    m1 = KripkeModel(f1, {"p": ["w1"]})

    # Model 2: 3 worlds: u0 -> u1, u0 -> u2 (u1 and u2 have identical valuations)
    f2 = KripkeFrame(worlds=["u0", "u1", "u2"], relation=[("u0", "u1"), ("u0", "u2")])
    m2 = KripkeModel(f2, {"p": ["u1", "u2"]})

    bisim = compute_maximal_bisimulation(m1, m2)
    print(f"Maximal Bisimulation pairs: {sorted(list(bisim))}")

    # Verify modal invariance for sample formulas
    formulas = [
        parse_formula("p"),
        parse_formula("[]p"),
        parse_formula("<>p"),
        parse_formula("[](p -> p)"),
    ]
    ok, err = verify_modal_invariance(m1, m2, bisim, formulas)
    print(f"Hennessy-Milner modal invariance preserved: {ok}")

    # Compute quotient model of m2
    quot = bisimulation_quotient(m2)
    print(f"Original model 2 worlds: {len(m2.worlds)} worlds")
    print(f"Minimized quotient model worlds: {len(quot.worlds)} worlds ({quot.worlds})")


if __name__ == "__main__":
    main()
