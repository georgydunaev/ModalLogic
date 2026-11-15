"""Relational Kripke semantics, frame condition verifiers, and finite model checking."""

from typing import Set, Tuple, Dict, Any, Iterable, Optional, Union
import itertools
from collections import deque
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
    Knows,
    CommonKnowledge,
    DistributedKnowledge,
    PublicAnnouncement,
    from_tuple,
)


class KripkeFrame:
    """Relational Kripke frame (W, R) representing possible worlds and accessibility."""

    def __init__(
        self,
        worlds: Iterable[Any],
        relation: Iterable[Tuple[Any, Any]],
        valuation: Optional[Dict[str, Iterable[Any]]] = None,
    ):
        self.worlds: Set[Any] = set(worlds)
        self.relation: Set[Tuple[Any, Any]] = set(relation)
        # Validate that relations only connect declared worlds
        for u, v in self.relation:
            if u not in self.worlds or v not in self.worlds:
                raise ValueError(f"Relation pair ({u!r}, {v!r}) references undeclared world")

        # Optional legacy valuation embedded directly on frame
        self._valuation: Optional[Dict[str, Set[Any]]] = None
        if valuation is not None:
            self._valuation = {p: set(ws) & self.worlds for p, ws in valuation.items()}

    @property
    def valuation(self) -> Dict[str, Set[Any]]:
        if self._valuation is None:
            return {}
        return self._valuation

    def successors(self, w: Any) -> Set[Any]:
        """Return the set of accessible worlds {u | w R u}."""
        if w not in self.worlds:
            raise KeyError(f"World {w!r} not in frame worlds")
        return {u for (v, u) in self.relation if v == w}

    def predecessors(self, w: Any) -> Set[Any]:
        """Return the set of worlds {u | u R w}."""
        if w not in self.worlds:
            raise KeyError(f"World {w!r} not in frame worlds")
        return {u for (u, v) in self.relation if v == w}

    # Frame properties
    def is_reflexive(self) -> bool:
        """Axiom T condition: forall w, w R w."""
        return all((w, w) in self.relation for w in self.worlds)

    def is_irreflexive(self) -> bool:
        """Forall w, not (w R w)."""
        return all((w, w) not in self.relation for w in self.worlds)

    def is_serial(self) -> bool:
        """Axiom D condition: forall w, exists u such that w R u."""
        return all(len(self.successors(w)) > 0 for w in self.worlds)

    def is_transitive(self) -> bool:
        """Axiom 4 condition: forall w, u, v, w R u and u R v implies w R v."""
        for w, u in self.relation:
            for v in self.successors(u):
                if (w, v) not in self.relation:
                    return False
        return True

    def is_symmetric(self) -> bool:
        """Axiom B condition: forall w, u, w R u implies u R w."""
        return all((u, w) in self.relation for (w, u) in self.relation)

    def is_antisymmetric(self) -> bool:
        """Forall w, u, w R u and u R w implies w == u."""
        for w, u in self.relation:
            if w != u and (u, w) in self.relation:
                return False
        return True

    def is_euclidean(self) -> bool:
        """Axiom 5 condition: forall w, u, v, w R u and w R v implies u R v."""
        for w in self.worlds:
            succ = list(self.successors(w))
            for u in succ:
                for v in succ:
                    if (u, v) not in self.relation:
                        return False
        return True

    def is_functional(self) -> bool:
        """Axiom CD condition: at most one successor per world (forall w, u, v: w R u and w R v implies u == v)."""
        for w in self.worlds:
            if len(self.successors(w)) > 1:
                return False
        return True

    def is_confluent(self) -> bool:
        """Church-Rosser / Lemmon confluence condition:
        forall w, u, v: w R u and w R v implies exists z: u R z and v R z.
        """
        for w in self.worlds:
            succ = list(self.successors(w))
            for i, u in enumerate(succ):
                succ_u = self.successors(u)
                for v in succ[i:]:
                    succ_v = self.successors(v)
                    if not (succ_u & succ_v):
                        return False
        return True

    def is_directed(self) -> bool:
        """Alias for is_confluent (directed frame)."""
        return self.is_confluent()

    def is_dense(self) -> bool:
        """Density condition (Axiom C4): forall w, u: w R u implies exists v: w R v and v R u."""
        for w, u in self.relation:
            if not (self.successors(w) & self.predecessors(u)):
                return False
        return True

    def is_well_founded(self) -> bool:
        """A finite relation is well-founded iff it contains no cycles."""
        return self.is_converse_well_founded()

    def is_converse_well_founded(self) -> bool:
        """On a finite frame with transitive relation, converse well-founded
        is equivalent to having no cycles (strict DAG / irreflexive partial order).
        """
        # Detect cycles using Tarjan/DFS
        visited = set()
        in_stack = set()

        def has_cycle(node: Any) -> bool:
            visited.add(node)
            in_stack.add(node)
            for succ in self.successors(node):
                if succ in in_stack:
                    return True
                if succ not in visited:
                    if has_cycle(succ):
                        return True
            in_stack.remove(node)
            return False

        for w in self.worlds:
            if w not in visited:
                if has_cycle(w):
                    return False
        return True

    def is_gl_frame(self) -> bool:
        """Frame condition for Gödel-Löb logic GL: transitive and converse well-founded."""
        return self.is_transitive() and self.is_converse_well_founded()

    def is_s4_frame(self) -> bool:
        """S4 preorder: reflexive and transitive."""
        return self.is_reflexive() and self.is_transitive()

    def is_s5_frame(self) -> bool:
        """S5 equivalence relation: reflexive, symmetric, and transitive."""
        return self.is_reflexive() and self.is_symmetric() and self.is_transitive()

    # Relational closures
    def reflexive_closure(self) -> "KripkeFrame":
        rel = set(self.relation)
        for w in self.worlds:
            rel.add((w, w))
        return KripkeFrame(self.worlds, rel, self._valuation)

    def symmetric_closure(self) -> "KripkeFrame":
        rel = set(self.relation)
        for u, v in self.relation:
            rel.add((v, u))
        return KripkeFrame(self.worlds, rel, self._valuation)

    def transitive_closure(self) -> "KripkeFrame":
        rel = set(self.relation)
        changed = True
        while changed:
            changed = False
            to_add = set()
            for u, v in rel:
                for w in self.worlds:
                    if (v, w) in rel and (u, w) not in rel:
                        to_add.add((u, w))
            if to_add:
                rel.update(to_add)
                changed = True
        return KripkeFrame(self.worlds, rel, self._valuation)

    def equivalence_closure(self) -> "KripkeFrame":
        return self.reflexive_closure().symmetric_closure().transitive_closure()

    # Backward compatibility with legacy KripkeFrame.eval
    def eval(self, w: Any, formula: Union[Formula, Tuple[Any, ...]]) -> bool:
        if self._valuation is None:
            raise ValueError("KripkeFrame has no valuation. Use KripkeModel for evaluation.")
        return KripkeModel(self, self._valuation).satisfies(w, formula)


class KripkeModel:
    """Kripke model M = (W, R, V) consisting of a frame and valuation function."""

    def __init__(self, frame: KripkeFrame, valuation: Dict[str, Iterable[Any]]):
        self.frame = frame
        self.valuation: Dict[str, Set[Any]] = {
            p: set(ws) & frame.worlds for p, ws in valuation.items()
        }

    @property
    def worlds(self) -> Set[Any]:
        return self.frame.worlds

    @property
    def relation(self) -> Set[Tuple[Any, Any]]:
        return self.frame.relation

    def satisfies(self, w: Any, formula: Union[Formula, Tuple[Any, ...]]) -> bool:
        """Check whether world w satisfies the formula (M, w |= phi)."""
        if isinstance(formula, tuple):
            formula = from_tuple(formula)

        if w not in self.worlds:
            raise KeyError(f"World {w!r} not in model")

        if isinstance(formula, Atom):
            return w in self.valuation.get(formula.name, set())
        if isinstance(formula, Top):
            return True
        if isinstance(formula, Bottom):
            return False
        if isinstance(formula, Not):
            return not self.satisfies(w, formula.inner)
        if isinstance(formula, And):
            return self.satisfies(w, formula.left) and self.satisfies(w, formula.right)
        if isinstance(formula, Or):
            return self.satisfies(w, formula.left) or self.satisfies(w, formula.right)
        if isinstance(formula, Implies):
            return (not self.satisfies(w, formula.left)) or self.satisfies(w, formula.right)
        if isinstance(formula, Iff):
            return self.satisfies(w, formula.left) == self.satisfies(w, formula.right)
        if isinstance(formula, Box):
            return all(self.satisfies(u, formula.inner) for u in self.frame.successors(w))
        if isinstance(formula, Dia):
            return any(self.satisfies(u, formula.inner) for u in self.frame.successors(w))
        if isinstance(formula, Knows):
            return all(self.satisfies(u, formula.formula) for u in self.frame.successors(w))
        if isinstance(formula, CommonKnowledge):
            tc_frame = self.frame.transitive_closure()
            return all(self.satisfies(u, formula.formula) for u in tc_frame.successors(w))
        if isinstance(formula, DistributedKnowledge):
            return all(self.satisfies(u, formula.formula) for u in self.frame.successors(w))
        if isinstance(formula, PublicAnnouncement):
            if not self.satisfies(w, formula.announcement):
                return True
            updated = self.public_announcement(formula.announcement)
            return updated.satisfies(w, formula.target_formula)
        raise TypeError(f"Unknown formula type: {type(formula)}")

    def public_announcement(self, announcement: Formula) -> "KripkeModel":
        """Restrict model to worlds satisfying announcement."""
        surviving = self.truth_set(announcement)
        restricted_rel = {
            (u, v) for (u, v) in self.frame.relation if u in surviving and v in surviving
        }
        restricted_val = {p: ws & surviving for p, ws in self.valuation.items()}
        return KripkeModel(KripkeFrame(surviving, restricted_rel), restricted_val)

    def eval(self, w: Any, formula: Union[Formula, Tuple[Any, ...]]) -> bool:
        """Alias for satisfies."""
        return self.satisfies(w, formula)

    def truth_set(self, formula: Union[Formula, Tuple[Any, ...]]) -> Set[Any]:
        """Compute the set of all worlds in the model satisfying the formula: ||phi||_M."""
        return {w for w in self.worlds if self.satisfies(w, formula)}

    def is_globally_true(self, formula: Union[Formula, Tuple[Any, ...]]) -> bool:
        """Check whether formula holds at every world in this model."""
        return len(self.truth_set(formula)) == len(self.worlds)


def is_frame_valid(
    frame: KripkeFrame,
    formula: Union[Formula, Tuple[Any, ...]],
    max_valuations: int = 4096,
) -> Tuple[bool, Optional[KripkeModel], Optional[Any]]:
    """Check whether a formula is valid on a finite frame (F |= phi).

    Returns (is_valid, countermodel, counterworld).
    If valid: (True, None, None).
    If invalid: (False, countermodel, counterworld).
    """
    if isinstance(formula, tuple):
        formula = from_tuple(formula)

    atoms = sorted(list(formula.atoms()))
    worlds_list = sorted(list(frame.worlds), key=lambda x: str(x))
    num_worlds = len(worlds_list)
    num_atoms = len(atoms)

    total_valuations = 2 ** (num_worlds * num_atoms)
    if total_valuations > max_valuations:
        raise ValueError(
            f"Too many valuations ({total_valuations} > {max_valuations}) for exhaustive check. "
            f"Frame has {num_worlds} worlds and formula has {num_atoms} atoms."
        )

    # Enumerate all subset valuations
    # Each atom p can be assigned any subset of worlds (2^|W| choices per atom)
    world_subsets = []
    for r in range(num_worlds + 1):
        for comb in itertools.combinations(worlds_list, r):
            world_subsets.append(set(comb))

    for val_tuple in itertools.product(world_subsets, repeat=num_atoms):
        valuation = {atom: val_tuple[i] for i, atom in enumerate(atoms)}
        model = KripkeModel(frame, valuation)
        for w in frame.worlds:
            if not model.satisfies(w, formula):
                return False, model, w

    return True, None, None


class MultiAgentKripkeFrame:
    """Multi-agent Kripke frame (W, {R_i}_{i in Agents}) for epistemic logic S5_n."""

    def __init__(
        self,
        worlds: Iterable[Any],
        relations: Dict[str, Iterable[Tuple[Any, Any]]],
        enforce_s5: bool = False,
    ):
        self.worlds: Set[Any] = set(worlds)
        self.relations: Dict[str, Set[Tuple[Any, Any]]] = {}
        for agent, rel in relations.items():
            agent_str = str(agent)
            rel_set = set(rel)
            for u, v in rel_set:
                if u not in self.worlds or v not in self.worlds:
                    raise ValueError(
                        f"Relation pair ({u!r}, {v!r}) for agent {agent_str!r} references undeclared world"
                    )
            if enforce_s5:
                single_frame = KripkeFrame(self.worlds, rel_set).equivalence_closure()
                self.relations[agent_str] = single_frame.relation
            else:
                self.relations[agent_str] = rel_set

    @property
    def agents(self) -> Set[str]:
        return set(self.relations.keys())

    def agent_frame(self, agent_id: str) -> KripkeFrame:
        """Return the single-agent KripkeFrame for agent_id."""
        if agent_id not in self.relations:
            raise KeyError(f"Unknown agent {agent_id!r}")
        return KripkeFrame(self.worlds, self.relations[agent_id])

    def successors(self, agent_id: str, w: Any) -> Set[Any]:
        """Return worlds epistemically accessible to agent_id from world w."""
        if w not in self.worlds:
            raise KeyError(f"World {w!r} not in frame worlds")
        rel = self.relations.get(str(agent_id), set())
        return {u for (v, u) in rel if v == w}

    def group_common_successors(self, agent_group: Iterable[str], w: Any) -> Set[Any]:
        """Return worlds reachable from w via transitive closure of union_{i in G} R_i."""
        if w not in self.worlds:
            raise KeyError(f"World {w!r} not in frame worlds")
        group_agents = [str(a) for a in agent_group]
        union_rel: Set[Tuple[Any, Any]] = set()
        for a in group_agents:
            union_rel |= self.relations.get(a, set())

        # Compute reachable worlds via BFS over non-empty paths in union_rel
        visited: Set[Any] = set()
        queue: deque = deque()
        for v, u in union_rel:
            if v == w and u not in visited:
                visited.add(u)
                queue.append(u)
        while queue:
            curr = queue.popleft()
            for v, u in union_rel:
                if v == curr and u not in visited:
                    visited.add(u)
                    queue.append(u)
        return visited

    def group_distributed_successors(self, agent_group: Iterable[str], w: Any) -> Set[Any]:
        """Return worlds reachable from w via intersection_{i in G} R_i."""
        if w not in self.worlds:
            raise KeyError(f"World {w!r} not in frame worlds")
        group_agents = [str(a) for a in agent_group]
        if not group_agents:
            return set(self.worlds)
        common = set(self.successors(group_agents[0], w))
        for a in group_agents[1:]:
            common &= self.successors(a, w)
        return common

    def is_s5_for_agent(self, agent_id: str) -> bool:
        """Check whether agent_id's relation is an S5 equivalence relation."""
        return self.agent_frame(agent_id).is_s5_frame()

    def is_s5_multi_agent(self) -> bool:
        """Check whether all agents have S5 equivalence relations."""
        return all(self.is_s5_for_agent(a) for a in self.relations)


class MultiAgentKripkeModel:
    """Multi-agent epistemic model M = (W, {R_i}_{i in Agents}, V)."""

    def __init__(
        self,
        frame: MultiAgentKripkeFrame,
        valuation: Dict[str, Iterable[Any]],
    ):
        self.frame = frame
        self.valuation: Dict[str, Set[Any]] = {
            p: set(ws) & frame.worlds for p, ws in valuation.items()
        }

    @property
    def worlds(self) -> Set[Any]:
        return self.frame.worlds

    @property
    def agents(self) -> Set[str]:
        return self.frame.agents

    def satisfies(self, w: Any, formula: Union[Formula, Tuple[Any, ...]]) -> bool:
        """Evaluate multi-agent epistemic and dynamic public announcement formulas at world w."""
        if isinstance(formula, tuple):
            formula = from_tuple(formula)

        if w not in self.worlds:
            raise KeyError(f"World {w!r} not in model")

        if isinstance(formula, Atom):
            return w in self.valuation.get(formula.name, set())
        if isinstance(formula, Top):
            return True
        if isinstance(formula, Bottom):
            return False
        if isinstance(formula, Not):
            return not self.satisfies(w, formula.inner)
        if isinstance(formula, And):
            return self.satisfies(w, formula.left) and self.satisfies(w, formula.right)
        if isinstance(formula, Or):
            return self.satisfies(w, formula.left) or self.satisfies(w, formula.right)
        if isinstance(formula, Implies):
            return (not self.satisfies(w, formula.left)) or self.satisfies(w, formula.right)
        if isinstance(formula, Iff):
            return self.satisfies(w, formula.left) == self.satisfies(w, formula.right)
        if isinstance(formula, Knows):
            return all(
                self.satisfies(u, formula.formula)
                for u in self.frame.successors(formula.agent_id, w)
            )
        if isinstance(formula, CommonKnowledge):
            return all(
                self.satisfies(u, formula.formula)
                for u in self.frame.group_common_successors(formula.agent_group, w)
            )
        if isinstance(formula, DistributedKnowledge):
            return all(
                self.satisfies(u, formula.formula)
                for u in self.frame.group_distributed_successors(formula.agent_group, w)
            )
        if isinstance(formula, PublicAnnouncement):
            # Dynamic semantics: M, w |= [phi] psi iff (M, w |= phi implies M|phi, w |= psi)
            if not self.satisfies(w, formula.announcement):
                return True
            updated_model = self.public_announcement(formula.announcement)
            return updated_model.satisfies(w, formula.target_formula)
        if isinstance(formula, Box):
            # Default to intersection/first agent if single-modality Box used
            all_succ = set()
            for a in self.frame.agents:
                all_succ |= self.frame.successors(a, w)
            return all(self.satisfies(u, formula.inner) for u in all_succ)
        if isinstance(formula, Dia):
            all_succ = set()
            for a in self.frame.agents:
                all_succ |= self.frame.successors(a, w)
            return any(self.satisfies(u, formula.inner) for u in all_succ)
        raise TypeError(f"Unknown formula type: {type(formula)}")

    def truth_set(self, formula: Union[Formula, Tuple[Any, ...]]) -> Set[Any]:
        """Return set of worlds in M satisfying formula."""
        return {w for w in self.worlds if self.satisfies(w, formula)}

    def is_globally_true(self, formula: Union[Formula, Tuple[Any, ...]]) -> bool:
        """Return True iff formula holds at all worlds in M."""
        return len(self.truth_set(formula)) == len(self.worlds)

    def public_announcement(self, announcement: Formula) -> "MultiAgentKripkeModel":
        """Return the updated epistemic model M|announcement restricted to worlds satisfying announcement."""
        surviving_worlds = self.truth_set(announcement)
        restricted_relations: Dict[str, Set[Tuple[Any, Any]]] = {}
        for agent, rel in self.frame.relations.items():
            restricted_relations[agent] = {
                (u, v) for (u, v) in rel if u in surviving_worlds and v in surviving_worlds
            }
        restricted_valuation: Dict[str, Set[Any]] = {
            p: ws & surviving_worlds for p, ws in self.valuation.items()
        }
        new_frame = MultiAgentKripkeFrame(
            surviving_worlds, restricted_relations, enforce_s5=False
        )
        return MultiAgentKripkeModel(new_frame, restricted_valuation)

