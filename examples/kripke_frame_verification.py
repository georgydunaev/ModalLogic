#!/usr/bin/env python3
"""Example demonstration of Kripke frame verification and correspondence."""

import os
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
if ROOT not in sys.path:
    sys.path.insert(0, ROOT)

from modallogic.syntax import parse_formula
from modallogic.semantics import KripkeFrame, KripkeModel, is_frame_valid
from modallogic.axioms import axiom_k, axiom_t, axiom_4, axiom_b, axiom_5, axiom_d, axiom_gl


def main():
    print("=== ModalLogic: Kripke Frame Properties & Semantic Verification ===")

    # 1. Define a Kripke frame with 3 worlds
    frame = KripkeFrame(
        worlds=["w0", "w1", "w2"],
        relation=[("w0", "w1"), ("w1", "w2"), ("w0", "w2"), ("w0", "w0"), ("w1", "w1"), ("w2", "w2")],
    )

    print(f"Worlds: {frame.worlds}")
    print(f"Relation: {frame.relation}")
    print(f"Reflexive: {frame.is_reflexive()}")
    print(f"Transitive: {frame.is_transitive()}")
    print(f"Symmetric: {frame.is_symmetric()}")
    print(f"S4 Preorder: {frame.is_s4_frame()}")
    print(f"S5 Equivalence: {frame.is_s5_frame()}")

    # 2. Check Axiom T ([]p -> p) validity on reflexive frame
    valid_t, _, _ = is_frame_valid(frame, axiom_t())
    print(f"Axiom T valid on frame: {valid_t}")

    # 3. Check Axiom 4 ([]p -> [][]p) validity on transitive frame
    valid_4, _, _ = is_frame_valid(frame, axiom_4())
    print(f"Axiom 4 valid on frame: {valid_4}")

    # 4. Check Axiom B (p -> []<>p) validity (should fail since not symmetric)
    valid_b, countermodel, counterworld = is_frame_valid(frame, axiom_b())
    print(f"Axiom B valid on frame: {valid_b}")
    if not valid_b:
        print(f"  Refutation at world: {counterworld}")
        print(f"  Countermodel valuation: {countermodel.valuation}")


if __name__ == "__main__":
    main()
