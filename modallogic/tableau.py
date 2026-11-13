"""Semantic tableau calculus, constructive proof generation, and countermodel extraction for modal logics K, T, S4, S5, and GL."""

from typing import Set, Tuple, List, Dict, Optional, Any, FrozenSet
from dataclasses import dataclass
from .syntax import (
    Formula,
    Atom,
    Top,
    Bottom,
    Not,
    And,
    Or,
    Implies,
    Iff,
    Box,
    Dia,
    parse_formula,
)
from .semantics import KripkeFrame, KripkeModel


@dataclass(frozen=True)
class SignedFormula:
    sign: bool  # True for T(phi), False for F(phi)
    world: str
    formula: Formula

    def __repr__(self) -> str:
        s = "T" if self.sign else "F"
        return f"{s}({self.formula}, {self.world})"


class TableauProofNode:
    """Node in a constructive semantic tableau proof tree."""

    def __init__(
        self,
        node_id: int,
        rule: str,
        description: str,
        signed_formula: Optional[SignedFormula] = None,
        children: Optional[List["TableauProofNode"]] = None,
        closed: bool = False,
        closing_pair: Optional[Tuple[SignedFormula, Optional[SignedFormula]]] = None,
    ):
        self.node_id = node_id
        self.rule = rule
        self.description = description
        self.signed_formula = signed_formula
        self.children: List["TableauProofNode"] = children or []
        self.closed = closed
        self.closing_pair = closing_pair

    def format_tree(self, indent: int = 0) -> str:
        pad = "  " * indent
        prefix = f"{pad}[Node {self.node_id}] {self.rule}: {self.description}"
        if self.closed and not self.children:
            if self.closing_pair:
                p1, p2 = self.closing_pair
                if p2 is not None:
                    prefix += f" [CLOSED by contradiction: {p1} vs {p2}]"
                else:
                    prefix += f" [CLOSED by constant: {p1}]"
            else:
                prefix += " [CLOSED]"
        lines = [prefix]
        for c in self.children:
            lines.append(c.format_tree(indent + 1))
        return "\n".join(lines)

    def __repr__(self) -> str:
        return f"TableauProofNode(id={self.node_id}, rule={self.rule!r}, closed={self.closed})"


class TableauResult:
    """Result of running the tableau decision procedure."""

    def __init__(
        self,
        is_valid: bool,
        system: str,
        countermodel: Optional[KripkeModel] = None,
        counterworld: Optional[str] = None,
        proof_steps: int = 0,
        proof_tree: Optional[TableauProofNode] = None,
        proof_trace: Optional[List[str]] = None,
    ):
        self.is_valid = is_valid
        self.system = system
        self.countermodel = countermodel
        self.counterworld = counterworld
        self.proof_steps = proof_steps
        self.proof_tree = proof_tree
        self.proof_trace: List[str] = proof_trace or []

    def format_proof(self) -> str:
        """Render constructive proof tree or countermodel description as text."""
        if not self.is_valid:
            w_count = len(self.countermodel.worlds) if self.countermodel else 0
            return (
                f"Formula is INVALID in system {self.system}.\n"
                f"Extracted finite countermodel with {w_count} worlds at root {self.counterworld!r}."
            )
        if self.proof_tree is not None:
            return self.proof_tree.format_tree()
        return f"Formula is VALID in system {self.system} (closed in {self.proof_steps} steps)."

    def verify_countermodel(self, formula: Formula) -> bool:
        """Verify that the countermodel satisfies the system frame condition and falsifies formula at counterworld."""
        if self.is_valid:
            return True
        if self.countermodel is None or self.counterworld is None:
            return False
        if self.countermodel.satisfies(self.counterworld, formula):
            return False

        frame = self.countermodel.frame
        if self.system == "K":
            return True
        if self.system in ("T", "KT"):
            return frame.is_reflexive()
        if self.system == "S4":
            return frame.is_s4_frame()
        if self.system == "S5":
            return frame.is_s5_frame()
        if self.system == "GL":
            return frame.is_gl_frame()
        return True

    def __repr__(self) -> str:
        if self.is_valid:
            return f"TableauResult(valid=True, system={self.system!r}, steps={self.proof_steps})"
        w_count = len(self.countermodel.worlds) if self.countermodel else 0
        return (
            f"TableauResult(valid=False, system={self.system!r}, "
            f"counterworld={self.counterworld!r}, worlds={w_count})"
        )


class TableauBranch:
    """Single branch in a semantic tableau proof tree."""

    def __init__(
        self,
        signed_formulas: Optional[Set[SignedFormula]] = None,
        relation: Optional[Set[Tuple[str, str]]] = None,
        worlds: Optional[Set[str]] = None,
    ):
        self.signed_formulas: Set[SignedFormula] = (
            set(signed_formulas) if signed_formulas else set()
        )
        self.relation: Set[Tuple[str, str]] = set(relation) if relation else set()
        self.worlds: Set[str] = set(worlds) if worlds else set()
        self.processed: Set[SignedFormula] = set()

    def copy(self) -> "TableauBranch":
        b = TableauBranch(self.signed_formulas, self.relation, self.worlds)
        b.processed = set(self.processed)
        return b

    def add_world(self, w: str) -> None:
        self.worlds.add(w)

    def add_edge(self, u: str, v: str) -> None:
        self.worlds.add(u)
        self.worlds.add(v)
        self.relation.add((u, v))

    def add_formula(self, sf: SignedFormula) -> None:
        self.signed_formulas.add(sf)
        self.worlds.add(sf.world)

    def is_closed(self) -> bool:
        """Check if branch contains an explicit contradiction."""
        return self.find_closing_pair() is not None

    def find_closing_pair(self) -> Optional[Tuple[SignedFormula, Optional[SignedFormula]]]:
        """Find the pair of signed formulas causing branch closure, or None if open."""
        true_map: Dict[str, Dict[Formula, SignedFormula]] = {}
        false_map: Dict[str, Dict[Formula, SignedFormula]] = {}

        for sf in self.signed_formulas:
            w = sf.world
            phi = sf.formula
            if sf.sign:
                if isinstance(phi, Bottom):
                    return (sf, None)
                true_map.setdefault(w, {})[phi] = sf
                if phi in false_map.get(w, {}):
                    return (sf, false_map[w][phi])
            else:
                if isinstance(phi, Top):
                    return (sf, None)
                false_map.setdefault(w, {})[phi] = sf
                if phi in true_map.get(w, {}):
                    return (true_map[w][phi], sf)

        return None


class TableauSolver:
    """Automated tableau theorem prover and countermodel generator for modal propositional logics."""

    def __init__(self, system: str = "K", max_steps: int = 1500):
        system = system.upper()
        if system not in ("K", "T", "KT", "S4", "S5", "GL"):
            raise ValueError(f"Unsupported modal system for tableau: {system}")
        if system == "KT":
            system = "T"
        self.system = system
        self.max_steps = max_steps
        self.world_counter = 0
        self.node_counter = 0

    def _fresh_world(self, prefix: str = "w") -> str:
        self.world_counter += 1
        return f"{prefix}_{self.world_counter}"

    def _next_node_id(self) -> int:
        self.node_counter += 1
        return self.node_counter

    def check_validity(self, formula: Formula) -> TableauResult:
        """Determine whether formula is valid in the specified modal logic system."""
        self.world_counter = 0
        self.node_counter = 0
        root_world = "w0"

        # Search for a countermodel: test whether F(formula, root_world) can be satisfied
        root_sf = SignedFormula(sign=False, world=root_world, formula=formula)
        initial_branch = TableauBranch()
        initial_branch.add_world(root_world)
        initial_branch.add_formula(root_sf)

        if self.system in ("T", "S4", "S5"):
            initial_branch.add_edge(root_world, root_world)

        steps = [0]
        trace: List[str] = [f"Initial formula signed False at root {root_world}: {formula}"]
        countermodel_branch, proof_tree = self._expand(initial_branch, steps, trace)

        if countermodel_branch is None:
            # All branches closed => formula is constructively valid
            root_proof = TableauProofNode(
                node_id=0,
                rule="ROOT",
                description=f"Proving validity of {formula} in system {self.system}",
                signed_formula=root_sf,
                children=[proof_tree] if proof_tree else [],
                closed=True,
            )
            return TableauResult(
                is_valid=True,
                system=self.system,
                proof_steps=steps[0],
                proof_tree=root_proof,
                proof_trace=trace,
            )

        # An open, fully-saturated branch was found => extract countermodel
        model = self._extract_countermodel(countermodel_branch)
        return TableauResult(
            is_valid=False,
            system=self.system,
            countermodel=model,
            counterworld=root_world,
            proof_steps=steps[0],
            proof_trace=trace,
        )

    def _extract_countermodel(self, branch: TableauBranch) -> KripkeModel:
        """Build KripkeModel from an open, saturated tableau branch."""
        worlds = set(branch.worlds)
        relation = set(branch.relation)

        # Apply closure conditions for the modal system
        if self.system in ("T", "S4", "S5"):
            for w in worlds:
                relation.add((w, w))
        if self.system in ("S4", "S5", "GL"):
            # Transitive closure
            changed = True
            while changed:
                changed = False
                to_add = set()
                for u, v in relation:
                    for w in worlds:
                        if (v, w) in relation and (u, w) not in relation:
                            to_add.add((u, w))
                if to_add:
                    relation.update(to_add)
                    changed = True
        if self.system == "S5":
            # Universal / equivalence closure: all worlds can see all worlds
            for u in worlds:
                for v in worlds:
                    relation.add((u, v))

        # Atomic valuations: atoms signed True hold at respective worlds
        valuation: Dict[str, Set[str]] = {}
        for sf in branch.signed_formulas:
            if sf.sign and isinstance(sf.formula, Atom):
                valuation.setdefault(sf.formula.name, set()).add(sf.world)

        frame = KripkeFrame(worlds, relation)
        return KripkeModel(frame, valuation)

    def _expand(
        self, branch: TableauBranch, steps: List[int], trace: List[str]
    ) -> Tuple[Optional[TableauBranch], Optional[TableauProofNode]]:
        """Expand branch recursively.
        Returns (countermodel_branch, proof_node):
        - If satisfiable / open: (open_saturated_branch, None)
        - If closed / valid: (None, proof_tree_node)
        """
        steps[0] += 1
        if steps[0] > self.max_steps:
            # Safety timeout against infinite loops: treat as open
            return branch, None

        closing_pair = branch.find_closing_pair()
        if closing_pair is not None:
            node = TableauProofNode(
                node_id=self._next_node_id(),
                rule="CLOSURE",
                description="Contradiction detected on branch",
                closed=True,
                closing_pair=closing_pair,
            )
            return None, node

        # 1. Apply propositional linear rules (Top, Bottom, Not, True And, False Or, False Implies)
        linear_candidate = None
        for sf in branch.signed_formulas:
            if sf in branch.processed:
                continue
            phi = sf.formula
            sign = sf.sign
            if isinstance(phi, (Top, Bottom, Atom)):
                branch.processed.add(sf)
                continue
            if isinstance(phi, Not):
                linear_candidate = sf
                break
            if sign and isinstance(phi, And):
                linear_candidate = sf
                break
            if not sign and isinstance(phi, Or):
                linear_candidate = sf
                break
            if not sign and isinstance(phi, Implies):
                linear_candidate = sf
                break

        if linear_candidate:
            branch.processed.add(linear_candidate)
            w = linear_candidate.world
            phi = linear_candidate.formula
            sign = linear_candidate.sign

            rule_name = ""
            desc = ""
            if isinstance(phi, Not):
                branch.add_formula(SignedFormula(not sign, w, phi.inner))
                rule_name = "NOT"
                desc = f"{'T' if sign else 'F'}(~) on {w}"
            elif sign and isinstance(phi, And):
                branch.add_formula(SignedFormula(True, w, phi.left))
                branch.add_formula(SignedFormula(True, w, phi.right))
                rule_name = "AND_TRUE"
                desc = f"T(&) on {w}"
            elif not sign and isinstance(phi, Or):
                branch.add_formula(SignedFormula(False, w, phi.left))
                branch.add_formula(SignedFormula(False, w, phi.right))
                rule_name = "OR_FALSE"
                desc = f"F(|) on {w}"
            elif not sign and isinstance(phi, Implies):
                branch.add_formula(SignedFormula(True, w, phi.left))
                branch.add_formula(SignedFormula(False, w, phi.right))
                rule_name = "IMPL_FALSE"
                desc = f"F(->) on {w}"

            res_branch, child_proof = self._expand(branch, steps, trace)
            if res_branch is not None:
                return res_branch, None

            node = TableauProofNode(
                node_id=self._next_node_id(),
                rule=rule_name,
                description=desc,
                signed_formula=linear_candidate,
                children=[child_proof] if child_proof else [],
                closed=True,
            )
            return None, node

        # 2. Apply propositional branching rules (False And, True Or, True Implies, Iff)
        branching_candidate = None
        for sf in branch.signed_formulas:
            if sf in branch.processed:
                continue
            phi = sf.formula
            sign = sf.sign
            if not sign and isinstance(phi, And):
                branching_candidate = sf
                break
            if sign and isinstance(phi, Or):
                branching_candidate = sf
                break
            if sign and isinstance(phi, Implies):
                branching_candidate = sf
                break
            if isinstance(phi, Iff):
                branching_candidate = sf
                break

        if branching_candidate:
            branch.processed.add(branching_candidate)
            w = branching_candidate.world
            phi = branching_candidate.formula
            sign = branching_candidate.sign

            if not sign and isinstance(phi, And):
                # F(A & B) branches into F(A) | F(B)
                b1 = branch.copy()
                b1.add_formula(SignedFormula(False, w, phi.left))
                res1, proof1 = self._expand(b1, steps, trace)
                if res1 is not None:
                    return res1, None

                b2 = branch.copy()
                b2.add_formula(SignedFormula(False, w, phi.right))
                res2, proof2 = self._expand(b2, steps, trace)
                if res2 is not None:
                    return res2, None

                node = TableauProofNode(
                    node_id=self._next_node_id(),
                    rule="AND_FALSE",
                    description=f"F(&) branch on {w}",
                    signed_formula=branching_candidate,
                    children=[proof1, proof2],
                    closed=True,
                )
                return None, node

            if sign and isinstance(phi, Or):
                # T(A | B) branches into T(A) | T(B)
                b1 = branch.copy()
                b1.add_formula(SignedFormula(True, w, phi.left))
                res1, proof1 = self._expand(b1, steps, trace)
                if res1 is not None:
                    return res1, None

                b2 = branch.copy()
                b2.add_formula(SignedFormula(True, w, phi.right))
                res2, proof2 = self._expand(b2, steps, trace)
                if res2 is not None:
                    return res2, None

                node = TableauProofNode(
                    node_id=self._next_node_id(),
                    rule="OR_TRUE",
                    description=f"T(|) branch on {w}",
                    signed_formula=branching_candidate,
                    children=[proof1, proof2],
                    closed=True,
                )
                return None, node

            if sign and isinstance(phi, Implies):
                # T(A -> B) branches into F(A) | T(B)
                b1 = branch.copy()
                b1.add_formula(SignedFormula(False, w, phi.left))
                res1, proof1 = self._expand(b1, steps, trace)
                if res1 is not None:
                    return res1, None

                b2 = branch.copy()
                b2.add_formula(SignedFormula(True, w, phi.right))
                res2, proof2 = self._expand(b2, steps, trace)
                if res2 is not None:
                    return res2, None

                node = TableauProofNode(
                    node_id=self._next_node_id(),
                    rule="IMPL_TRUE",
                    description=f"T(->) branch on {w}",
                    signed_formula=branching_candidate,
                    children=[proof1, proof2],
                    closed=True,
                )
                return None, node

            if isinstance(phi, Iff):
                if sign:
                    # T(A <-> B) branches into {T(A), T(B)} | {F(A), F(B)}
                    b1 = branch.copy()
                    b1.add_formula(SignedFormula(True, w, phi.left))
                    b1.add_formula(SignedFormula(True, w, phi.right))
                    res1, proof1 = self._expand(b1, steps, trace)
                    if res1 is not None:
                        return res1, None

                    b2 = branch.copy()
                    b2.add_formula(SignedFormula(False, w, phi.left))
                    b2.add_formula(SignedFormula(False, w, phi.right))
                    res2, proof2 = self._expand(b2, steps, trace)
                    if res2 is not None:
                        return res2, None

                    node = TableauProofNode(
                        node_id=self._next_node_id(),
                        rule="IFF_TRUE",
                        description=f"T(<->) branch on {w}",
                        signed_formula=branching_candidate,
                        children=[proof1, proof2],
                        closed=True,
                    )
                    return None, node
                else:
                    # F(A <-> B) branches into {T(A), F(B)} | {F(A), T(B)}
                    b1 = branch.copy()
                    b1.add_formula(SignedFormula(True, w, phi.left))
                    b1.add_formula(SignedFormula(False, w, phi.right))
                    res1, proof1 = self._expand(b1, steps, trace)
                    if res1 is not None:
                        return res1, None

                    b2 = branch.copy()
                    b2.add_formula(SignedFormula(False, w, phi.left))
                    b2.add_formula(SignedFormula(True, w, phi.right))
                    res2, proof2 = self._expand(b2, steps, trace)
                    if res2 is not None:
                        return res2, None

                    node = TableauProofNode(
                        node_id=self._next_node_id(),
                        rule="IFF_FALSE",
                        description=f"F(<->) branch on {w}",
                        signed_formula=branching_candidate,
                        children=[proof1, proof2],
                        closed=True,
                    )
                    return None, node

        # 3. Apply modal Universal propagation (T Box, F Dia) along accessibility
        propagated_any = False
        for sf in list(branch.signed_formulas):
            phi = sf.formula
            sign = sf.sign
            w = sf.world

            # For S5, relation is universal across all worlds in branch
            targets = (
                branch.worlds
                if self.system == "S5"
                else {v for (u, v) in branch.relation if u == w}
            )

            if self.system in ("T", "S4") and w not in targets:
                targets = targets | {w}

            if sign and isinstance(phi, Box):
                for v in targets:
                    target_sf = SignedFormula(True, v, phi.inner)
                    if target_sf not in branch.signed_formulas:
                        branch.add_formula(target_sf)
                        propagated_any = True
                    if self.system in ("S4", "GL"):
                        # Transitive propagation of Box
                        box_sf = SignedFormula(True, v, phi)
                        if box_sf not in branch.signed_formulas:
                            branch.add_formula(box_sf)
                            propagated_any = True

            if not sign and isinstance(phi, Dia):
                for v in targets:
                    target_sf = SignedFormula(False, v, phi.inner)
                    if target_sf not in branch.signed_formulas:
                        branch.add_formula(target_sf)
                        propagated_any = True
                    if self.system in ("S4", "GL"):
                        dia_sf = SignedFormula(False, v, phi)
                        if dia_sf not in branch.signed_formulas:
                            branch.add_formula(dia_sf)
                            propagated_any = True

        if propagated_any:
            res_branch, child_proof = self._expand(branch, steps, trace)
            if res_branch is not None:
                return res_branch, None
            node = TableauProofNode(
                node_id=self._next_node_id(),
                rule="MODAL_PROPAGATE",
                description="Universal modal propagation along accessibility",
                children=[child_proof] if child_proof else [],
                closed=True,
            )
            return None, node

        # 4. Apply modal Existential generation (F Box, T Dia) creating a fresh world
        existential_candidate = None
        for sf in branch.signed_formulas:
            if sf in branch.processed:
                continue
            phi = sf.formula
            sign = sf.sign
            if (not sign and isinstance(phi, Box)) or (sign and isinstance(phi, Dia)):
                existential_candidate = sf
                break

        if existential_candidate:
            branch.processed.add(existential_candidate)
            w = existential_candidate.world
            phi = existential_candidate.formula
            sign = existential_candidate.sign

            inner = phi.inner
            target_sign = False if not sign else True

            # In S4, check for loop blocking
            if self.system == "S4":
                already_satisfied = any(
                    SignedFormula(target_sign, v, inner) in branch.signed_formulas
                    for (u, v) in branch.relation
                    if u == w
                )
                if already_satisfied:
                    return self._expand(branch, steps, trace)

            fresh = self._fresh_world()
            branch.add_world(fresh)
            branch.add_edge(w, fresh)
            branch.add_formula(SignedFormula(target_sign, fresh, inner))

            # GL specific modal rule: Löb's diagonal formula
            if self.system == "GL":
                if not sign and isinstance(phi, Box):
                    # For F(Box phi, w), add T(Box phi, fresh) (diagonal formula)
                    branch.add_formula(SignedFormula(True, fresh, phi))
                elif sign and isinstance(phi, Dia):
                    # For T(Dia phi, w), equivalent to F(Box ~phi)
                    branch.add_formula(SignedFormula(False, fresh, phi))

                # Transitive copy: all T(Box psi, w) propagate to fresh
                for sf_w in list(branch.signed_formulas):
                    if sf_w.world == w and sf_w.sign and isinstance(sf_w.formula, Box):
                        branch.add_formula(SignedFormula(True, fresh, sf_w.formula))
                        branch.add_formula(SignedFormula(True, fresh, sf_w.formula.inner))

            if self.system in ("T", "S4", "S5"):
                branch.add_edge(fresh, fresh)

            res_branch, child_proof = self._expand(branch, steps, trace)
            if res_branch is not None:
                return res_branch, None

            rule_label = "MODAL_GL_STEP" if self.system == "GL" else "MODAL_STEP"
            node = TableauProofNode(
                node_id=self._next_node_id(),
                rule=rule_label,
                description=f"Generated fresh world {fresh} accessible from {w}",
                signed_formula=existential_candidate,
                children=[child_proof] if child_proof else [],
                closed=True,
            )
            return None, node

        # No rules apply and branch is not closed => Saturated open branch found!
        return branch, None
