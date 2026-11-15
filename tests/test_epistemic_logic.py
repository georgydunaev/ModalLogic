"""Unit tests for Multi-Agent Epistemic Logic S5_n, Common Knowledge, Distributed Knowledge, and Public Announcements."""

import unittest
import itertools
from modallogic.syntax import (
    Atom,
    Top,
    Bottom,
    Not,
    And,
    Or,
    Implies,
    Iff,
    Knows,
    CommonKnowledge,
    DistributedKnowledge,
    PublicAnnouncement,
    from_tuple,
)
from modallogic.semantics import (
    MultiAgentKripkeFrame,
    MultiAgentKripkeModel,
)
from modallogic.tableau import TableauSolver, reduce_public_announcement


def build_muddy_children_model(num_agents: int) -> MultiAgentKripkeModel:
    """Construct the canonical S5_n epistemic Kripke model for the Muddy Children puzzle with n agents.

    Worlds are n-tuples of bits (b_1, ..., b_n) in {0, 1}^n where b_i = 1 iff child i has a muddy forehead.
    Agent i can see all other children's foreheads except their own, so (w, u) in R_i iff w[j] == u[j] for all j != i.
    """
    agents = [str(i) for i in range(1, num_agents + 1)]
    worlds = list(itertools.product([0, 1], repeat=num_agents))
    relations = {a: set() for a in agents}

    for w in worlds:
        for u in worlds:
            for idx, a in enumerate(agents):
                if all(w[j] == u[j] for j in range(num_agents) if j != idx):
                    relations[a].add((w, u))

    valuation = {}
    for idx, a in enumerate(agents):
        valuation[f"m{a}"] = {w for w in worlds if w[idx] == 1}

    frame = MultiAgentKripkeFrame(worlds, relations, enforce_s5=True)
    return MultiAgentKripkeModel(frame, valuation)


class TestMultiAgentEpistemicLogic(unittest.TestCase):
    """Test suite for Ticket 7689: Multi-Agent Epistemic Logic and Dynamic Public Announcements."""

    def test_ast_nodes_and_tuple_roundtrip(self) -> None:
        p = Atom("p")
        q = Atom("q")
        k1 = Knows("1", p)
        cg = CommonKnowledge(["2", "1"], Implies(p, q))
        dg = DistributedKnowledge(["1", "2"], And(p, q))
        pa = PublicAnnouncement(p, k1)

        for f in (k1, cg, dg, pa):
            self.assertEqual(from_tuple(f.to_tuple()), f)
            self.assertGreaterEqual(f.complexity(), 2)
            self.assertIn(p, f.subformulas())
            self.assertTrue(len(f.to_latex()) > 0)
            self.assertEqual(f.to_nnf().atoms(), f.atoms())

    def test_s5_multi_agent_equivalence_relations(self) -> None:
        model = build_muddy_children_model(3)
        self.assertTrue(model.frame.is_s5_multi_agent())
        for a in ("1", "2", "3"):
            self.assertTrue(model.frame.is_s5_for_agent(a))

    def test_muddy_children_puzzle_up_to_4_agents(self) -> None:
        """Verify Muddy Children puzzle for n in {2, 3, 4} agents with k muddy children."""
        for n in (2, 3, 4):
            model = build_muddy_children_model(n)
            agents = [str(i) for i in range(1, n + 1)]
            muddy_atoms = [Atom(f"m{a}") for a in agents]

            # Public announcement 0 (Father): "At least one of you has a muddy forehead"
            at_least_one = muddy_atoms[0]
            for ma in muddy_atoms[1:]:
                at_least_one = Or(at_least_one, ma)

            # Suppose all n children are muddy: actual world w_all = (1, 1, ..., 1)
            w_all = tuple(1 for _ in range(n))

            # Before father's announcement, it is NOT common knowledge that at least one is muddy
            ck_at_least_one = CommonKnowledge(agents, at_least_one)
            self.assertFalse(model.satisfies(w_all, ck_at_least_one))

            # After father announces at_least_one, it becomes common knowledge!
            m_step = model.public_announcement(at_least_one)
            self.assertTrue(m_step.satisfies(w_all, ck_at_least_one))

            # Formula stating whether agent i knows their own status (Knows_i m_i | Knows_i ~m_i)
            def knows_own(agent_id: str):
                ma = Atom(f"m{agent_id}")
                return Or(Knows(agent_id, ma), Knows(agent_id, Not(ma)))

            nobody_knows = And(Not(knows_own("1")), Not(knows_own("2")))
            for a in agents[2:]:
                nobody_knows = And(nobody_knows, Not(knows_own(a)))

            # For rounds 1 .. n-1: no child knows their status yet at w_all, and they announce nobody_knows
            for _round in range(1, n):
                for a in agents:
                    self.assertFalse(m_step.satisfies(w_all, knows_own(a)))
                m_step = m_step.public_announcement(nobody_knows)

            # After n-1 announcements of "nobody knows", every muddy child now knows they are muddy!
            for a in agents:
                self.assertTrue(m_step.satisfies(w_all, Knows(a, Atom(f"m{a}"))))
            self.assertTrue(
                m_step.satisfies(w_all, CommonKnowledge(agents, Atom("m1")))
            )

    def test_distributed_knowledge_and_public_announcement_operator(self) -> None:
        # Agent 1 knows p, Agent 2 knows (p -> q). Neither knows q alone, but D_{1,2}(q) holds!
        worlds = ["w0", "w1", "w2", "w3"]
        # w0: p, q; w1: p, ~q; w2: ~p, q; w3: ~p, ~q
        # Agent 1 distinguishes p vs ~p: partitions {w0, w1}, {w2, w3}
        # Agent 2 distinguishes (p -> q) vs (p & ~q): partitions {w0, w2, w3}, {w1}
        r1 = {
            ("w0", "w0"), ("w0", "w1"), ("w1", "w0"), ("w1", "w1"),
            ("w2", "w2"), ("w2", "w3"), ("w3", "w2"), ("w3", "w3"),
        }
        r2 = {
            ("w0", "w0"), ("w0", "w2"), ("w0", "w3"),
            ("w2", "w0"), ("w2", "w2"), ("w2", "w3"),
            ("w3", "w0"), ("w3", "w2"), ("w3", "w3"),
            ("w1", "w1"),
        }
        val = {"p": {"w0", "w1"}, "q": {"w0", "w2"}}
        frame = MultiAgentKripkeFrame(worlds, {"1": r1, "2": r2}, enforce_s5=True)
        model = MultiAgentKripkeModel(frame, val)

        p = Atom("p")
        q = Atom("q")
        self.assertTrue(model.satisfies("w0", Knows("1", p)))
        self.assertTrue(model.satisfies("w0", Knows("2", Implies(p, q))))
        self.assertFalse(model.satisfies("w0", Knows("1", q)))
        self.assertFalse(model.satisfies("w0", Knows("2", q)))
        self.assertTrue(model.satisfies("w0", DistributedKnowledge(["1", "2"], q)))

        # If Agent 1 publicly announces p, then Agent 2 comes to know q: [p] K_2(q)
        pa_formula = PublicAnnouncement(p, Knows("2", q))
        self.assertTrue(model.satisfies("w0", pa_formula))

    def test_epistemic_tableau_solver(self) -> None:
        p = Atom("p")
        q = Atom("q")
        solver_s5 = TableauSolver(system="S5")

        # 1. Epistemic K distribution: K_1(p -> q) -> (K_1(p) -> K_1(q))
        f_dist = Implies(Knows("1", Implies(p, q)), Implies(Knows("1", p), Knows("1", q)))
        self.assertTrue(solver_s5.check_validity(f_dist).is_valid)

        # 2. Epistemic Veridicality (T): K_1(p) -> p
        f_verid = Implies(Knows("1", p), p)
        self.assertTrue(solver_s5.check_validity(f_verid).is_valid)

        # 3. Positive Introspection (4): K_1(p) -> K_1(K_1(p))
        f_pos = Implies(Knows("1", p), Knows("1", Knows("1", p)))
        self.assertTrue(solver_s5.check_validity(f_pos).is_valid)

        # 4. Negative Introspection (5): ~K_1(p) -> K_1(~K_1(p))
        f_neg = Implies(Not(Knows("1", p)), Knows("1", Not(Knows("1", p))))
        self.assertTrue(solver_s5.check_validity(f_neg).is_valid)

        # 5. Distributed knowledge subsumes individual knowledge: K_1(p) -> D_{1,2}(p)
        f_dk = Implies(Knows("1", p), DistributedKnowledge(["1", "2"], p))
        self.assertTrue(solver_s5.check_validity(f_dk).is_valid)

        # 6. Public announcement reduction validity: [p] K_1(p) is valid for atomic p
        f_pal = PublicAnnouncement(p, Knows("1", p))
        self.assertTrue(solver_s5.check_validity(f_pal).is_valid)


if __name__ == "__main__":
    unittest.main()
