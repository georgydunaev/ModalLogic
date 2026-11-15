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
- Property checkers with failure witnesses: `check_reflexivity`, `check_transitivity`, `check_symmetry`, `check_seriality`, `check_euclideanness`, `check_confluence`, `check_directedness`, `check_well_foundedness`, `check_converse_well_foundedness`.
- Constructive correspondence theorems: `correspondence_theorem_t`, `correspondence_theorem_4`, `correspondence_theorem_b`, `correspondence_theorem_d`, `correspondence_theorem_5`, `correspondence_theorem_c4`, `correspondence_theorem_gl`.
- `verify_frame_correspondence(frame, axiom_name)`: Validates equivalence between structural relational condition and modal axiom satisfaction.
- `AutomatedCorrespondenceChecker`: Automated verification of individual relational properties, modal axioms, and multi-axiom modal logic systems (S4, S5, K4, KD45, GL).

### 4.8 Composable Frame Classes (`modallogic.frames`)
- Relational property mixins:
  - `ReflexiveFrameMixin`: Enforces `forall w, w R w`.
  - `TransitiveFrameMixin`: Enforces `forall w, u, v: w R u and u R v implies w R v`.
  - `SymmetricFrameMixin`: Enforces `forall w, u: w R u implies u R w`.
  - `SerialFrameMixin`: Enforces `forall w, exists u: w R u`.
  - `EuclideanFrameMixin`: Enforces `forall w, u, v: w R u and w R v implies u R v`.
  - `ConfluentFrameMixin` / `DirectedFrameMixin`: Enforces Church-Rosser confluence: `forall w, u, v: w R u and w R v implies exists z: u R z and v R z`.
  - `ConverseWellFoundedFrameMixin`: Enforces cycle-free finite DAGs for provability logic.
  - `WellFoundedFrameMixin`: Enforces cycle-free finite orders.
- Concrete composable frame classes:
  - `KFrame`: Unrestricted relational frame.
  - `KDFrame`: Serial frame for deontic logic.
  - `TFrame` / `KTFrame`: Reflexive frame.
  - `KBFrame`: Symmetric frame for Brouwerian logic.
  - `K4Frame`: Transitive frame.
  - `K45Frame`: Transitive euclidean frame.
  - `KD45Frame`: Serial transitive euclidean frame for belief logic.
  - `S4Frame`: Reflexive transitive preorder frame.
  - `S5Frame`: Reflexive symmetric transitive euclidean equivalence frame.
  - `GLFrame`: Transitive converse well-founded frame for provability logic.
  - `ConfluentFrame` / `DirectedFrame`: Confluent frame for Lemmon confluence (C4).
- Methods:
  - `frame.validation_report() -> Dict`: Detailed report of satisfied and violated properties.
  - `frame.validate()`: Enforces property satisfaction, raising `ValueError` on failure.
  - `create_frame(system_name, worlds, relation, ...)`: Dynamic factory instantiating the corresponding composable frame class.

### 4.9 Modal Distribution Tactics and Proof Rules (`modallogic.tactics`)
- Distribution Tactics:
  - `distribute_box_and(formula)`: Rewrites `[](A & B)` into `[]A & []B`.
  - `distribute_dia_or(formula)`: Rewrites `<>(A | B)` into `<>A | <>B`.
  - `factor_box_and(formula)`: Rewrites `[]A & []B` into `[](A & B)`.
  - `factor_dia_or(formula)`: Rewrites `<>A | <>B` into `<>(A | B)`.
  - `normalize_modal_distributions(formula)`: Applies recursive distribution transformations across the full AST.
- Distribution Schemas:
  - `box_and_distribution_schema()`: `[](p & q) <-> ([]p & []q)`.
  - `dia_or_distribution_schema()`: `<>(p | q) <-> (<>p | <>q)`.
  - `k_implication_distribution_schema()`: `[](p -> q) -> ([]p -> []q)`.
  - `dia_implication_distribution_schema()`: `[](p -> q) -> (<>p -> <>q)`.
  - `s4_deduction_schema()`, `s5_modal_collapse_schema()`, `gl_provability_schema()`.
- Standardized Proof Rules and Deduction Engine:
  - `DeductionStep`: Individual verified proof step with rule annotation and premises.
  - `ModalDeduction`: Hilbert-style and tactic-style derivation verifier across modal logics.
  - Unified proof generators:
    - `prove_box_and_distribution(system)`: Derivation of Box distribution over conjunction.
    - `prove_dia_or_distribution(system)`: Derivation of Diamond distribution over disjunction via duality.
    - `prove_s4_preorder_theorems()`: Derivation of preorder reflexivity and transitivity.
    - `prove_s5_modal_collapse()`: Derivation of modal collapse in S5.
    - `prove_gl_transitivity()`: Derivation of transitivity (Axiom 4) in GL from Löb's axiom.

### 4.10 Canonical Model Evaluations (`modallogic.canonical`)
- `compute_subformulas(formula)`: Extracts all subformulas.
- `SubformulaClosure(formulas)`: Subformula closure closed under single negation, verum, and falsum.
- `CanonicalWorld`: World representation for maximally consistent sets.
- `CanonicalModel`: Canonical model evaluating truth sets, Truth Lemma consistency, and frame conditions.
- `construct_canonical_model(formulas, system)`: Constructs canonical models for K, T, K4, S4, S5, and GL with relational closures.
- `model.verify_truth_lemma() -> Dict`: Checks `M, w |= psi iff psi in w`.
- `model.verify_frame_conditions() -> Dict`: Validates that canonical frame satisfies system conditions (e.g. S4 preorder, S5 equivalence relation, GL strict DAG).

### 4.11 First-Order Standard Translation (`modallogic.fo_translation`)
- `FOFormula`: Base class for classical first-order logic formulas.
  - Subclasses: `FOTop`, `FOBottom`, `Predicate(name, var)`, `Relation(name, var1, var2)`, `Equality(var1, var2)`, `FONot(sub)`, `FOAnd(left, right)`, `FOOr(left, right)`, `FOImplies(left, right)`, `FOIff(left, right)`, `Forall(var, body)`, `Exists(var, body)`.
- `standard_translation(formula, var='x')` (also `ST_x`, `st`): Computes van Benthem's Standard Translation mapping a modal formula into the two-variable fragment FO^2.
  - Alternates variables `x` and `y` at modal quantifier depth:
    - `ST_x(p) = P(x)`
    - `ST_x(~phi) = ~ST_x(phi)`
    - `ST_x([]phi) = forall y (R(x, y) -> ST_y(phi))`
    - `ST_x(<>phi) = exists y (R(x, y) & ST_y(phi))`
- `evaluate_fo(fo_formula, model, assignment) -> bool`: Direct semantic truth evaluation of first-order formulas on relational Kripke models.
  - Formally proves van Benthem's embedding theorem: `M, w |= phi iff M, [x -> w] |= ST_x(phi)`.
- Canonical first-order frame conditions:
  - `fo_reflexive()`, `fo_symmetric()`, `fo_transitive()`, `fo_euclidean()`, `fo_serial()`, `fo_functional()`, `fo_confluent()`.

### 4.12 Sahlqvist Recognizer and Frame Correspondence (`modallogic.correspondence`)
- Sahlqvist recognizer:
  - `polarity_of_atoms(formula)`: Computes the set of polarities (`+1` or `-1`) for all atom occurrences.
  - `is_positive(formula)` / `is_negative(formula)`: Checks whether a formula is purely positive/negative.
  - `is_sahlqvist(formula)` (and `is_sahlqvist_formula(formula)`): Determines if an implication `phi -> psi` is a Sahlqvist formula (where `psi` is positive and `phi` is a Sahlqvist antecedent composed from negative formulas, boxed atoms, and diamonds).
  - `SahlqvistRecognizer`: Structured class providing detailed analysis and decomposition of Sahlqvist formulas.
- Canonical frame condition matching:
  - `CANONICAL_FRAME_CONDITIONS`: Dictionary mapping standard modal axioms (T, B, 4, 5, D, CD, C4) to their first-order relational frame conditions.
  - `match_axiom_frame_condition(formula)`: Recognizes canonical axiom shapes modulo renaming and associates them with corresponding first-order conditions.
  - `get_canonical_frame_condition(axiom_name)`: Retrieves the FO condition for a known axiom name.
- Axiom CD (Partial Functionality) correspondence:
  - `check_functionality(frame)` / `check_partial_functionality(frame)`: Verifies `forall w, u, v: (w R u and w R v) -> u = v`.
  - `correspondence_theorem_cd(frame)`: Constructive correspondence proof between Axiom CD `<>p -> []p` and partial functionality.

### 4.13 Multi-Agent Epistemic Logic and Dynamic Public Announcements (`modallogic.syntax`, `modallogic.semantics`, `modallogic.tableau`)
- Epistemic and Dynamic AST Nodes:
  - `Knows(agent_id, formula)`: Individual knowledge $K_i \varphi$ evaluated over agent accessibility relation $R_i$.
  - `CommonKnowledge(agent_group, formula)`: Group common knowledge $C_G \varphi$ evaluated over the transitive closure $\left(\bigcup_{i \in G} R_i\right)^+$.
  - `DistributedKnowledge(agent_group, formula)`: Group distributed knowledge $D_G \varphi$ evaluated over the intersection $\bigcap_{i \in G} R_i$.
  - `PublicAnnouncement(announcement, target_formula)`: Dynamic public announcement $[\varphi]\psi$ evaluated on the restricted model $M|_{\varphi}$.
- Multi-Agent Kripke Semantics:
  - `MultiAgentKripkeFrame(worlds, relations, enforce_s5=False)`: Stores agent-indexed relations $R_i$, validates S5 equivalence properties per agent, and computes common and distributed accessibility closures.
  - `MultiAgentKripkeModel(frame, valuation)`: Evaluates multi-agent epistemic formulas and produces updated models under `public_announcement(announcement)`.
- Plaza Reduction and Epistemic Tableau Proving:
  - `reduce_public_announcement(formula)`: Applies Jan Plaza's (1989) reduction axioms to translate PAL formulas into epistemic logic.
  - `TableauSolver`: Supports multi-agent $S5_n$ epistemic propagation and fresh world generation for `Knows`, `CommonKnowledge`, `DistributedKnowledge`, and `PublicAnnouncement`.

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

## 7. Philosophical, Epistemic, Deontic, and Temporal Foundations

Modal logic provides a unified relational semantics across philosophy, computer science, and mathematical foundations:
1. **Alethic Modal Logic (`K`, `T`, `S4`, `S5`)**: Models metaphysical necessity (`[]phi` holds in all possible worlds) and possibility (`<>phi` holds in at least one possible world).
2. **Epistemic and Doxastic Logic (`S5_n`, `KD45`)**:
   - Knowledge (`S5`) satisfies veridicality (`K_i p -> p`), positive introspection (`K_i p -> K_i K_i p`), and negative introspection (`~K_i p -> K_i ~K_i p`).
   - Belief (`KD45`) drops veridicality in favor of consistency/seriality (`B_i p -> ~B_i ~p`).
   - Dynamic Epistemic Logic (`PAL`) models information update by restricting possible worlds to those satisfying a public announcement (`[phi] psi`).
3. **Deontic Logic (`KD`)**: Models normative obligation (`O p`) and permission (`P p`) over serial frames where every world has at least one ideal deontic alternative.
4. **Temporal Logic (`K4`, `S4`, Linear/Branching Frames)**: Interprets `[]phi` as "always in the future" and `<>phi` as "eventually in the future" over transitive, dense (`C4`), or confluent (`G`) time flows.
5. **Provability Logic (`GL`)**: Interprets `[]phi` as arithmetic provability $\text{Prov}_{PA}(\ulcorner \varphi \urcorner)$ in Peano Arithmetic, governed by Löb's Theorem (`[]([]p -> p) -> []p`) and Solovay's arithmetical completeness theorem over finite transitive converse well-founded trees.

---

## 8. Verification and Testing

Execute the complete test suite:
```bash
python3 -m unittest discover -s /botworkspace/ModalLogic/tests -p 'test_*.py'
```
