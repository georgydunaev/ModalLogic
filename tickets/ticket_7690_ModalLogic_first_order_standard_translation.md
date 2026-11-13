# [MODALLOGIC] Ticket 7690: Standard First-Order Translation and Correspondence Theory Engine

**Repository:** `ModalLogic`
**Status:** `OPEN`
**Milestone:** `Phase 2: First-Order Embedding and Frame Correspondence`
**Priority:** `MEDIUM`

## Objective
Implement van Benthem's Standard Translation (ST_x) from basic and multi-modal propositional modal logic into classical first-order logic with unary predicates (P(x)) and binary relation symbols (R(x, y)), along with automated frame condition correspondence verification.

## Technical Requirements
1. **Standard Translation (`modallogic/fo_translation.py`)**:
   - Recursive translation mapping modal formula phi and world variable x to first-order formula ST_x(phi) using two bound variables x and y.
   - Translation rules:
     * ST_x(p) = P(x)
     * ST_x(~phi) = ~ST_x(phi)
     * ST_x(phi /\ psi) = ST_x(phi) /\ ST_x(psi)
     * ST_x(Box phi) = forall y. (R(x, y) implies ST_y(phi))
     * ST_x(Diamond phi) = exists y. (R(x, y) /\ ST_y(phi))
2. **Frame Property Matcher (`modallogic/correspondence.py`)**:
   - Match classical modal axioms (T, B, 4, 5, D, CD) against their canonical first-order frame conditions (reflexive, symmetric, transitive, Euclidean, serial, functional).
   - Automated Sahlqvist formula recognizer identifying modal formulas that correspond to first-order frame conditions.
3. **Verification**:
   - Unit tests in `tests/test_fo_translation.py` validating translation semantics against Kripke model evaluations.

## Acceptance Criteria
- Full test pass in `tests/test_fo_translation.py`.
- Integration into CLI and documentation in `DOCS.md`.
- Pure ASCII formatting with zero emojis and zero arrows.
