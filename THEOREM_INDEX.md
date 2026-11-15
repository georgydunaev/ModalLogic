# Theorem and Formalization Inventory (`ModalLogic`)

This document catalogs all formal modal axiom schemas, frame correspondence theorems, Sahlqvist recognition procedures, Gödel-Löb provability theorems, van Benthem first-order translations, bisimulation invariance theorems, and multi-agent epistemic logic theorems implemented and verified in the `ModalLogic` repository.

---

## 1. Modal Axiom Schemas and Deductive Systems (`modallogic/axioms.py`, `modallogic/tactics.py`)

| Axiom / Theorem | Formula Schema | Frame Condition | Module |
|-----------------|----------------|-----------------|--------|
| `axiom_k` | `[](p -> q) -> ([]p -> []q)` | All relational Kripke frames | `modallogic/axioms.py` |
| `axiom_t` | `[]p -> p` | Reflexivity: `forall w, w R w` | `modallogic/axioms.py` |
| `axiom_4` | `[]p -> [][]p` | Transitivity: `w R u and u R v implies w R v` | `modallogic/axioms.py` |
| `axiom_b` | `p -> []<>p` | Symmetry: `w R u implies u R w` | `modallogic/axioms.py` |
| `axiom_d` | `[]p -> <>p` | Seriality: `forall w, exists u, w R u` | `modallogic/axioms.py` |
| `axiom_5` | `<>p -> []<>p` | Euclideanness: `w R u and w R v implies u R v` | `modallogic/axioms.py` |
| `axiom_gl` | `[]([]p -> p) -> []p` | Transitive and converse well-founded (Löb) | `modallogic/axioms.py` |
| `axiom_grz` | `[]([](p -> []p) -> p) -> p` | Reflexive, transitive, converse well-founded (Grzegorczyk) | `modallogic/axioms.py` |
| `axiom_c4` | `<>[]p -> []<>p` | Confluence / Church-Rosser (`is_confluent`) | `modallogic/axioms.py` |
| `axiom_cd` | `<>p -> []p` | Partial functionality (`is_functional`) | `modallogic/axioms.py` |
| `prove_box_and_distribution` | `[](p & q) <-> ([]p & []q)` | Valid in all normal modal logics (`K`) | `modallogic/tactics.py` |
| `prove_dia_or_distribution` | `<>(p | q) <-> (<>p | <>q)` | Valid in all normal modal logics (`K`) | `modallogic/tactics.py` |
| `prove_s4_preorder_theorems` | `[][]p <-> []p`, `<><>p <-> <>p` | S4 idempotence of Box and Diamond | `modallogic/tactics.py` |
| `prove_s5_modal_collapse` | `<>[]p -> []p`, `<>p -> []<>p` | S5 modal collapse theorems | `modallogic/tactics.py` |
| `prove_gl_transitivity` | `[]p -> [][]p` | Formal derivation of Axiom 4 from Löb's Axiom in `GL` | `modallogic/tactics.py` |

---

## 2. Frame Correspondence and Sahlqvist Theory (`modallogic/correspondence.py`)

| Theorem / Verifier | Mathematical Statement | Module |
|--------------------|------------------------|--------|
| `correspondence_theorem_t` | `F |= []p -> p` iff `R` is reflexive | `modallogic/correspondence.py` |
| `correspondence_theorem_4` | `F |= []p -> [][]p` iff `R` is transitive | `modallogic/correspondence.py` |
| `correspondence_theorem_b` | `F |= p -> []<>p` iff `R` is symmetric | `modallogic/correspondence.py` |
| `correspondence_theorem_d` | `F |= []p -> <>p` iff `R` is serial | `modallogic/correspondence.py` |
| `correspondence_theorem_5` | `F |= <>p -> []<>p` iff `R` is euclidean | `modallogic/correspondence.py` |
| `correspondence_theorem_cd` | `F |= <>p -> []p` iff `R` is partially functional | `modallogic/correspondence.py` |
| `correspondence_theorem_gl` | On finite frames, `F |= []([]p -> p) -> []p` iff `R` is transitive and irreflexive/acyclic | `modallogic/correspondence.py` |
| `is_sahlqvist` / `SahlqvistRecognizer` | Syntactic Sahlqvist antecedent/consequent polarity decomposition | `modallogic/correspondence.py` |

---

## 3. Gödel-Löb Provability Logic (`GL`) and Arithmetic Completeness (`modallogic/provability.py`)

| Theorem / Algorithm | Mathematical Statement | Module |
|---------------------|------------------------|--------|
| `gl_derive_axiom_4` | Constructive Hilbert-style proof of `[]p -> [][]p` in `GL` | `modallogic/provability.py` |
| `godel_second_incompleteness` | `~([]BOTTOM) -> ~[](~([]BOTTOM))` derived in `GL` | `modallogic/provability.py` |
| `compute_fixed_point` | De Jongh-Sambin theorem: explicit modal fixed point `psi` with `GL |- (p <-> A(p)) <-> (p <-> psi)` for modalized `p` in `A(p)` | `modallogic/provability.py` |
| `GLDecisionProcedure` / `prove_gl` | Terminating sequent/tableau decision procedure for `GL` with loop-free strict DAG countermodels | `modallogic/provability.py` |
| `ArithmeticRealization` / `verify_solovay_soundness` | Arithmetical interpretation mapping `[]phi` to `Prov_PA(phi)` | `modallogic/provability.py` |

---

## 4. Standard First-Order Translation and Canonical Models (`modallogic/fo_translation.py`, `modallogic/canonical.py`)

| Theorem / Function | Mathematical Statement | Module |
|--------------------|------------------------|--------|
| `standard_translation` (`ST_x`) | Van Benthem translation from modal formulas into two-variable first-order logic `FO^2` | `modallogic/fo_translation.py` |
| `evaluate_fo` | Equivalence theorem: `M, w |= phi` iff `M, [x -> w] |= ST_x(phi)` | `modallogic/fo_translation.py` |
| `fo_reflexive`, `fo_symmetric`, `fo_transitive`, `fo_euclidean`, `fo_serial`, `fo_functional`, `fo_confluent` | First-order frame condition definitions and evaluators | `modallogic/fo_translation.py` |
| `construct_canonical_model` | Filtration / canonical model construction over `SubformulaClosure` for `K`, `T`, `K4`, `S4`, `S5`, `GL` | `modallogic/canonical.py` |
| `CanonicalModel.verify_truth_lemma` | Truth Lemma verification: `M^c, w |= psi` iff `psi in w` | `modallogic/canonical.py` |

---

## 5. Bisimulation, Tableau Decision Engine, and Multi-Agent Epistemic Logic

| Component / Theorem | Mathematical Statement | Module |
|---------------------|------------------------|--------|
| `is_bisimulation`, `compute_largest_bisimulation` | Zig, Zag, and Atomic Harmony verification and maximal bisimulation partition refinement | `modallogic/bisimulation.py` |
| `verify_modal_invariance` | Hennessy-Milner invariance: bisimilar worlds satisfy identical modal formulas | `modallogic/bisimulation.py` |
| `TableauSolver.check_validity` | Sound and complete semantic tableau decision procedure for `K`, `T`, `S4`, `S5`, `GL`, and `S5_n` | `modallogic/tableau.py` |
| `reduce_public_announcement` | Jan Plaza's (1989) completeness reduction axioms for Public Announcement Logic (`PAL`) | `modallogic/tableau.py` |
| `Knows`, `CommonKnowledge`, `DistributedKnowledge`, `PublicAnnouncement` | Multi-agent $S5_n$ epistemic syntax and dynamic model restriction $M|_{\varphi}$ | `modallogic/syntax.py`, `modallogic/semantics.py` |
| `build_muddy_children_model` | Formal $S5_n$ epistemic verification of the $n$-agent Muddy Children puzzle | `tests/test_epistemic_logic.py` |
