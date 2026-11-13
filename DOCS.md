# ModalLogic Technical Documentation

This document catalogs the mathematical foundations, system definitions, theorems, and software APIs implemented in the `ModalLogic` repository.

## Table of Contents

1. Mathematical Foundations and Definitions
2. Modal Axiom Schemas and Frame Correspondence
3. Modal Systems Overview
4. Software Architecture and API Reference
5. Bisimulation and Invariance Theorems
6. Semantic Tableaux Decision Procedures
7. Verification and Testing

---

## 1. Mathematical Foundations and Definitions

### 1.1 Modal Syntax

The language of propositional modal logic is defined inductively over a countably infinite set of propositional variables `Var`:
- Every `p in Var` is a formula.
- Truth constants `TOP` (verum) and `BOTTOM` (falsum) are formulas.
- If `phi` is a formula, then `~phi` (negation), `[]phi` (necessity / box), and `<>phi` (possibility / diamond) are formulas.
- If `phi` and `psi` are formulas, then `phi & psi` (conjunction), `phi | psi` (disjunction), `phi -> psi` (implication), and `phi <-> psi` (equivalence) are formulas.

Duality: `<>phi` is semantically equivalent to `~[]~phi`.

### 1.2 Relational Kripke Frames

A Kripke frame is a pair `F = (W, R)` where:
- `W` is a non-empty set of possible worlds.
- `R subset W x W` is a binary accessibility relation on `W`.

For any world `w in W`:
- `R(w) = {u in W | (w, u) in R}` denotes the set of successors accessible from `w`.
- `R^{-1}(w) = {u in W | (u, w) in R}` denotes the set of predecessors.

### 1.3 Kripke Models and Truth Evaluation

A Kripke model is a triple `M = (W, R, V)` where:
- `(W, R)` is a Kripke frame.
- `V: Var -> Powerset(W)` is a valuation function mapping each propositional variable to the set of worlds where it is true.

The satisfaction relation `M, w |= phi` is defined inductively:
- `M, w |= p` iff `w in V(p)`.
- `M, w |= TOP` always.
- `M, w |= BOTTOM` never.
- `M, w |= ~phi` iff not `(M, w |= phi)`.
- `M, w |= phi & psi` iff `(M, w |= phi)` and `(M, w |= psi)`.
- `M, w |= phi | psi` iff `(M, w |= phi)` or `(M, w |= psi)`.
- `M, w |= phi -> psi` iff `(M, w |= phi)` implies `(M, w |= psi)`.
- `M, w |= phi <-> psi` iff `(M, w |= phi)` iff `(M, w |= psi)`.
- `M, w |= []phi` iff for all `u in W` with `(w, u) in R`, `M, u |= phi`.
- `M, w |= <>phi` iff there exists `u in W` with `(w, u) in R` such that `M, u |= phi`.

---

## 2. Modal Axiom Schemas and Frame Correspondence

The gold standard of modal correspondence (Goldblatt-Thomason, van Benthem) relates modal formulas to first-order frame conditions:

| Axiom Name | Formula Schema | Frame Property | First-Order Condition |
|------------|----------------|----------------|-----------------------|
| K | `[](p -> q) -> ([]p -> []q)` | All frames | None (valid on all relational frames) |
| T | `[]p -> p` | Reflexivity | `forall w: w R w` |
| 4 | `[]p -> [][]p` | Transitivity | `forall w, u, v: (w R u and u R v) implies w R v` |
| B | `p -> []<>p` | Symmetry | `forall w, u: w R u implies u R w` |
| D | `[]p -> <>p` | Seriality | `forall w: exists u: w R u` |
| 5 | `<>p -> []<>p` | Euclideanness | `forall w, u, v: (w R u and w R v) implies u R v` |
| GL | `[]( []p -> p ) -> []p` | Strict well-founded | Transitive and converse well-founded |
| Grz | `[]( [](p -> []p) -> p ) -> p` | Preorder well-founded | Reflexive, transitive, converse well-founded |
| C4 | `<>[]p -> []<>p` | Confluence | `forall w, u, v: (w R u and w R v) implies exists z: (u R z and v R z)` |
| CD | `<>p -> []p` | Partial functionality | `forall w, u, v: (w R u and w R v) implies u = v` |

---

## 3. Modal Systems Overview

Standard modal deductive systems are classified by their axiom sets:

- **K**: Base normal modal logic (Axiom K + Necessitation rule).
- **KD**: Deontic logic of obligation (K + Axiom D). Models must be serial.
- **T (KT)**: Reflexive modal logic (K + Axiom T).
- **K4**: Transitive modal logic (K + Axiom 4).
- **KB**: Symmetric modal logic (K + Axiom B).
- **K45**: Transitive and euclidean modal logic.
- **KD45**: Doxastic logic of belief (K + D + 4 + 5). Serial, transitive, euclidean.
- **S4**: Preorder modal logic (K + T + 4). Reflexive and transitive.
- **S5**: Universal modality (K + T + 4 + 5). Equivalence relation frames.
- **GL**: Gödel-Löb provability logic (K + GL). Transitive converse-well-founded frames.

---

## 4. Software Architecture and API Reference

The `modallogic` Python package provides the following modular structure:

### 4.1 Syntax (`modallogic.syntax`)
- `Formula`: Base abstract class for formulas.
- `Atom`, `Top`, `Bottom`, `Not`, `And`, `Or`, `Implies`, `Iff`, `Box`, `Dia`: Concrete AST nodes.
- `parse_formula(s: str) -> Formula`: Recursive descent parser with standard operator precedence.
- `from_tuple(t: tuple) -> Formula`: Deserializer from compact tuple notation.
- `Formula.to_nnf() -> Formula`: Normalization to Negation Normal Form.

### 4.2 Semantics (`modallogic.semantics`)
- `KripkeFrame(worlds, relation, valuation=None)`:
  - Methods: `successors(w)`, `predecessors(w)`.
  - Properties: `is_reflexive()`, `is_serial()`, `is_transitive()`, `is_symmetric()`, `is_euclidean()`, `is_confluent()`, `is_gl_frame()`, `is_s4_frame()`, `is_s5_frame()`.
  - Closures: `reflexive_closure()`, `transitive_closure()`, `symmetric_closure()`, `equivalence_closure()`.
- `KripkeModel(frame, valuation)`:
  - `satisfies(w, formula) -> bool`: Model checking.
  - `truth_set(formula) -> Set`: Worlds where formula holds.
  - `is_globally_true(formula) -> bool`: Global validity in model.
- `is_frame_valid(frame, formula) -> (bool, model, world)`: Exhaustive finite frame validity checker and countermodel generator.

### 4.3 Axioms and Systems (`modallogic.axioms`)
- Factory functions for standard axioms: `axiom_k()`, `axiom_t()`, `axiom_4()`, `axiom_b()`, `axiom_d()`, `axiom_5()`, `axiom_gl()`, `axiom_grz()`, `axiom_c4()`, `axiom_cd()`.
- Registry of standard systems: `SYSTEMS["K"]`, `SYSTEMS["S4"]`, `SYSTEMS["S5"]`, etc.

### 4.4 Bisimulation Engine (`modallogic.bisimulation`)
- `is_bisimulation(model1, model2, relation)`: Verifies atomic harmony, forth, and back conditions.
- `compute_maximal_bisimulation(model1, model2)`: Relational fixed-point refinement.
- `bisimulation_quotient(model)`: Constructs the minimal quotient model modulo bisimilarity.
- `verify_modal_invariance(model1, model2, bisim, formulas)`: Automated check of the Hennessy-Milner theorem.

### 4.5 Tableau Solver (`modallogic.tableau`)
- `TableauSolver(system="K"|"T"|"S4"|"S5"|"GL")`: Automated decision procedure.
- `check_validity(formula) -> TableauResult`: Returns `is_valid=True` with constructive proof tree (`proof_tree`) and step count, or `is_valid=False` with an extracted finite Kripke countermodel satisfying system frame conditions.
- `TableauResult.format_proof() -> str`: Human-readable derivation tree or countermodel summary.
- `TableauResult.verify_countermodel(formula) -> bool`: Automated check that countermodel falsifies formula at counterworld and satisfies frame conditions.

### 4.6 Provability Logic GL (`modallogic.provability`)
- `axiom_gl()`, `axiom_4()`, `godel_second_incompleteness()`: GL axiom schemas and theorems.
- `is_transitive(frame)`, `is_converse_well_founded(frame)`, `is_gl_frame(frame)`: Frame condition verification.
- `gl_depth(frame, world) -> int`, `gl_frame_height(frame) -> int`: Converse well-founded rank and height.
- `is_modalized(formula, var_name) -> bool`: Verifies that variable occurrences are boxed or diamonded.
- `compute_fixed_point(formula, var_name) -> Formula`: De Jongh-Sambin fixed point calculation yielding unique `H` such that `GL |- H <-> A(H)`.

### 4.7 Frame Correspondence (`modallogic.correspondence`)
- Property checkers with failure witnesses: `check_reflexivity`, `check_transitivity`, `check_symmetry`, `check_seriality`, `check_euclideanness`, `check_converse_well_foundedness`.
- Constructive correspondence theorems: `correspondence_theorem_t`, `correspondence_theorem_4`, `correspondence_theorem_b`, `correspondence_theorem_d`, `correspondence_theorem_5`, `correspondence_theorem_gl`.
- `verify_frame_correspondence(frame, axiom_name)`: Validates equivalence between structural relational condition and modal axiom satisfaction.

---

## 5. Bisimulation and Invariance Theorems

### Theorem (Hennessy-Milner Invariance)
Let `M1 = (W1, R1, V1)` and `M2 = (W2, R2, V2)` be image-finite Kripke models. If `(w1, w2) in Z` for some bisimulation `Z`, then for every modal formula `phi`:
`M1, w1 |= phi` if and only if `M2, w2 |= phi`.

This theorem is verified experimentally in `tests/test_bisimulation.py` and `examples/bisimulation_demo.py`.

---

## 6. Semantic Tableaux Decision Procedures

The labeled semantic tableau calculus tests the validity of a formula `phi` by searching for a countermodel satisfying `F(phi, w0)`:
1. Linear propositional rules reduce compound formulas.
2. Branching rules create search branches for disjunctive constructs.
3. Modal propagation rules transfer box requirements to existing accessible worlds.
4. Modal existential rules create new witness worlds for falsified boxes and verified diamonds.
5. If all branches encounter an explicit clash `T(psi, w)` and `F(psi, w)`, the formula is valid.
6. If an open branch reaches saturation, an explicit finite countermodel is extracted.

---

## 7. Verification and Testing

Execute the complete test suite:
```bash
python3 -m unittest discover -s /botworkspace/ModalLogic/tests -p 'test_*.py'
```
