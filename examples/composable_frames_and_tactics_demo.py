#!/usr/bin/env python3
"""Demonstration of composable Kripke frame classes, automated correspondence checkers, distribution tactics, and canonical models."""

import os
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
if ROOT not in sys.path:
    sys.path.insert(0, ROOT)

from modallogic.syntax import parse_formula
from modallogic.frames import (
    S4Frame,
    S5Frame,
    GLFrame,
    KD45Frame,
    ConfluentFrame,
    create_frame,
)
from modallogic.correspondence import (
    AutomatedCorrespondenceChecker,
    correspondence_theorem_c4,
    verify_frame_correspondence,
)
from modallogic.tactics import (
    distribute_box_and,
    distribute_dia_or,
    normalize_modal_distributions,
    prove_box_and_distribution,
    prove_gl_transitivity,
    prove_s5_modal_collapse,
)
from modallogic.canonical import construct_canonical_model


def main():
    print("=== ModalLogic: Composable Frames and Distribution Tactics Demo ===")

    # 1. Composable S4 frame instantiation and validation
    print("\n[1] Composable S4 Frame Verification:")
    s4_frame = S4Frame(
        worlds=["w0", "w1"],
        relation=[("w0", "w0"), ("w1", "w1"), ("w0", "w1")],
        validate=True,
    )
    print(f"S4 Frame worlds: {s4_frame.worlds}")
    print(f"Validation report: {s4_frame.validation_report()}")

    # 2. Automated correspondence check
    print("\n[2] Automated Correspondence Engine:")
    corr_report = AutomatedCorrespondenceChecker.verify_system(s4_frame, "S4")
    print(f"System S4 verification: valid={corr_report['is_valid']}")

    # 3. Lemmon Confluence (C4) Correspondence Check
    print("\n[3] Confluent Frame & Axiom C4 Correspondence:")
    conf_frame = ConfluentFrame(
        worlds=["w0", "w1", "w2", "w3"],
        relation=[("w0", "w1"), ("w0", "w2"), ("w1", "w3"), ("w2", "w3"), ("w3", "w3")],
        validate=True,
    )
    c4_res = correspondence_theorem_c4(conf_frame)
    print(f"Axiom C4 validity on confluent frame: {c4_res['is_axiom_valid']}")

    # 4. Standardized Modal Distribution Tactics
    print("\n[4] Distribution Tactics:")
    raw_formula = parse_formula("[](p & q) -> <>(r | s)")
    norm_formula = normalize_modal_distributions(raw_formula)
    print(f"Original:   {raw_formula}")
    print(f"Normalized: {norm_formula}")

    # 5. Standardized Proof Deductions
    print("\n[5] Unified Deductions across Modal Logics:")
    box_ded = prove_box_and_distribution("K")
    print(f"Box-And Distribution verified in K: {box_ded.verify()}")

    gl_ded = prove_gl_transitivity()
    print(f"GL Transitivity (Axiom 4) verified in GL: {gl_ded.verify()}")

    s5_ded = prove_s5_modal_collapse()
    print(f"S5 Modal Collapse verified in S5: {s5_ded.verify()}")

    # 6. Canonical Model Truth Lemma and Frame Validation
    print("\n[6] Canonical Model Evaluation:")
    canon_s4 = construct_canonical_model([parse_formula("[]p -> p")], system="S4")
    truth_lemma = canon_s4.verify_truth_lemma()
    print(f"Canonical Truth Lemma holds: {truth_lemma['truth_lemma_holds']}")
    frame_conds = canon_s4.verify_frame_conditions()
    print(f"Canonical S4 Frame Conditions: {frame_conds}")


if __name__ == "__main__":
    main()
