# Project Overview: `ModalLogic`

## 1. Purpose and Scope

`ModalLogic` is a formal verification and automated reasoning library for normal, provability, and multi-agent epistemic modal logics (`K`, `KD`, `T`, `KB`, `K4`, `K45`, `KD45`, `S4`, `S5`, `GL`, `S5_n`, and Public Announcement Logic `PAL`). It provides relational Kripke frame semantics, Sahlqvist correspondence verification, van Benthem's Standard Translation into two-variable first-order logic (`FO^2`), canonical model construction, bisimulation partition refinement, Gödel-Löb provability fixed points, and labeled semantic tableau decision procedures with countermodel extraction.

---

## 2. Repository Architecture

### Layer 1: Syntax, Axioms, and First-Order Translation
- [syntax.py](file:///botworkspace/ModalLogic/modallogic/syntax.py): Propositional, modal (`Box`, `Dia`), multi-agent epistemic (`Knows`, `CommonKnowledge`, `DistributedKnowledge`), and dynamic (`PublicAnnouncement`) AST classes, Negation Normal Form (`to_nnf`), LaTeX export (`to_latex`), and recursive descent parser (`parse_formula`).
- [axioms.py](file:///botworkspace/ModalLogic/modallogic/axioms.py) and [tactics.py](file:///botworkspace/ModalLogic/modallogic/tactics.py): Standard modal axiom schemas (`K`, `T`, `4`, `B`, `D`, `5`, `GL`, `Grz`, `C4`, `CD`), Hilbert-style deduction verifier (`ModalDeduction`), and modal distribution normalization tactics.
- [fo_translation.py](file:///botworkspace/ModalLogic/modallogic/fo_translation.py): Van Benthem's Standard Translation (`standard_translation` / `ST_x`), first-order Kripke evaluator (`evaluate_fo`), and first-order frame property definitions.

### Layer 2: Kripke Frame Semantics, Correspondence, and Bisimulations
- [semantics.py](file:///botworkspace/ModalLogic/modallogic/semantics.py) and [frames.py](file:///botworkspace/ModalLogic/modallogic/frames.py): Single-agent (`KripkeFrame`, `KripkeModel`) and multi-agent (`MultiAgentKripkeFrame`, `MultiAgentKripkeModel`) relational models, composable frame mixins (`ReflexiveFrameMixin`, `TransitiveFrameMixin`, `SymmetricFrameMixin`, `EuclideanFrameMixin`, `ConverseWellFoundedFrameMixin`), and dynamic public announcement restriction.
- [correspondence.py](file:///botworkspace/ModalLogic/modallogic/correspondence.py): Constructive frame correspondence verifiers for `T`, `4`, `B`, `D`, `5`, `CD`, and `GL`, together with the syntactic `SahlqvistRecognizer`.
- [bisimulation.py](file:///botworkspace/ModalLogic/modallogic/bisimulation.py) and [canonical.py](file:///botworkspace/ModalLogic/modallogic/canonical.py): Zig/Zag bisimulation verification, maximal bisimulation refinement, Hennessy-Milner invariance checks, and canonical model filtration (`construct_canonical_model`).

### Layer 3: Decision Procedures and Provability Logic (`GL`)
- [tableau.py](file:///botworkspace/ModalLogic/modallogic/tableau.py): Labeled semantic tableau theorem prover (`TableauSolver`) for `K`, `T`, `S4`, `S5`, `GL`, and multi-agent `S5_n` with Plaza's `PAL` reduction (`reduce_public_announcement`), constructive proof tree generation, and finite countermodel extraction.
- [provability.py](file:///botworkspace/ModalLogic/modallogic/provability.py): Gödel-Löb provability logic `GL`, Hilbert derivation of Axiom 4 from Löb's Axiom (`gl_derive_axiom_4`), Gödel's Second Incompleteness schema, the de Jongh-Sambin modal fixed-point algorithm (`compute_fixed_point`), and Solovay arithmetic realization checks.

---

## 3. Verification Commands

```bash
# Run the complete unit test suite across all modal, provability, and epistemic modules:
PYTHONPATH=/botworkspace/ModalLogic python3 -m unittest discover -s /botworkspace/ModalLogic/tests -p 'test_*.py'
```

See [THEOREM_INDEX.md](file:///botworkspace/ModalLogic/THEOREM_INDEX.md) and [DOCS.md](file:///botworkspace/ModalLogic/DOCS.md) for the complete theorem inventory and technical documentation.
