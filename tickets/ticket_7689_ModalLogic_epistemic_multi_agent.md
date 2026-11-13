# [MODALLOGIC] Ticket 7689: Multi-Agent Epistemic Logic with Public Announcement and Common Knowledge

**Repository:** `ModalLogic`
**Status:** `OPEN`
**Milestone:** `Phase 2: Multi-Agent Epistemic Semantics and Solvers`
**Priority:** `HIGH`

## Objective
Extend the `modallogic` Python package with full support for multi-agent epistemic logic (S5_n), common knowledge operators (C_G), distributed knowledge operators (D_G), and dynamic public announcements ([phi] psi).

## Technical Requirements
1. **Syntax Extensions (`modallogic/syntax.py`)**:
   - Add AST nodes: `Knows(agent_id, formula)`, `CommonKnowledge(agent_group, formula)`, `DistributedKnowledge(agent_group, formula)`, and `PublicAnnouncement(announcement, target_formula)`.
   - String representations, LaTeX export, and recursive subformula analyzers.
2. **Kripke Semantics for Multi-Agent Models (`modallogic/semantics.py`)**:
   - Support multiple accessibility relations R_i for each agent i in AgentSet.
   - Enforce equivalence relation properties (reflexivity, transitivity, symmetry) per agent for S5 epistemic logic.
   - Implement evaluation of Common Knowledge via transitive closure of the union of group accessibility relations.
   - Implement Public Announcement model update by restricting model domains to worlds satisfying the announcement.
3. **Tableau Solver Support (`modallogic/tableau.py`)**:
   - Extend tableau rules to branch and expand over agent-indexed accessibility relations.
4. **Verification**:
   - Comprehensive test suite in `tests/test_epistemic_logic.py` verifying classical puzzles (e.g. Muddy Children puzzle, Wise Men puzzle).

## Acceptance Criteria
- Unit tests verify correct resolution of Muddy Children puzzle with up to 4 agents.
- 100 percent pass rate across existing and new test suites.
- Pure ASCII formatting with zero emojis and zero arrows.
