#!/usr/bin/env python3
"""Example demonstration of automated tableau theorem proving and countermodel extraction."""

import os
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
if ROOT not in sys.path:
    sys.path.insert(0, ROOT)

from modallogic.syntax import parse_formula
from modallogic.tableau import TableauSolver


def main():
    print("=== ModalLogic: Automated Labeled Tableau Theorem Prover ===")

    test_cases = [
        ("[](p -> q) -> ([]p -> []q)", "K"),
        ("[]p -> p", "K"),
        ("[]p -> p", "T"),
        ("[]p -> [][]p", "T"),
        ("[]p -> [][]p", "S4"),
        ("<>p -> []<>p", "S4"),
        ("<>p -> []<>p", "S5"),
    ]

    for formula_str, system in test_cases:
        phi = parse_formula(formula_str)
        solver = TableauSolver(system=system)
        result = solver.check_validity(phi)

        if result.is_valid:
            print(f"System {system}: [VALID] {formula_str} (proof closed in {result.proof_steps} steps)")
        else:
            cm = result.countermodel
            cw = result.counterworld
            print(
                f"System {system}: [REFUTED] {formula_str} "
                f"(countermodel with {len(cm.worlds)} worlds, falsified at {cw})"
            )


if __name__ == "__main__":
    main()
