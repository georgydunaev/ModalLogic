#!/usr/bin/env python3
"""Kripke frame evaluator and structural tests for ModalLogic."""

import os
import unittest

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))


class KripkeFrame:
    """Finite Kripke model (W, R, V) for normal modal logics K, T, S4, S5."""

    def __init__(self, worlds, relation, valuation):
        self.worlds = set(worlds)
        self.relation = set(relation)
        self.valuation = {p: set(ws) for p, ws in valuation.items()}

    def successors(self, w):
        return {u for (v, u) in self.relation if v == w}

    def eval(self, w, formula):
        kind = formula[0]
        if kind == "ATOM":
            return w in self.valuation.get(formula[1], set())
        if kind == "NOT":
            return not self.eval(w, formula[1])
        if kind == "IMPL":
            return (not self.eval(w, formula[1])) or self.eval(w, formula[2])
        if kind == "BOX":
            return all(self.eval(u, formula[1]) for u in self.successors(w))
        if kind == "DIA":
            return any(self.eval(u, formula[1]) for u in self.successors(w))
        raise ValueError(f"Unknown formula kind: {kind}")


class TestModalLogic(unittest.TestCase):
    def test_k_axiom_distribution(self):
        # Axiom K: [](p -> q) -> ([]p -> []q) holds at every world of any frame
        frame = KripkeFrame(
            worlds=["w0", "w1"],
            relation=[("w0", "w1")],
            valuation={"p": ["w1"], "q": ["w1"]},
        )
        p = ("ATOM", "p")
        q = ("ATOM", "q")
        k_axiom = ("IMPL", ("BOX", ("IMPL", p, q)), ("IMPL", ("BOX", p), ("BOX", q)))
        for w in frame.worlds:
            self.assertTrue(frame.eval(w, k_axiom))

    def test_t_axiom_on_reflexive_frame(self):
        # Axiom T: []p -> p holds on reflexive frames
        frame = KripkeFrame(
            worlds=["w0"],
            relation=[("w0", "w0")],
            valuation={"p": ["w0"]},
        )
        p = ("ATOM", "p")
        t_axiom = ("IMPL", ("BOX", p), p)
        self.assertTrue(frame.eval("w0", t_axiom))

    def test_docs_and_examples_exist(self):
        for rel in ("README.md", "DOCS.md", "examples/basic_modal_logic_example.md"):
            self.assertTrue(os.path.isfile(os.path.join(ROOT, rel)))


if __name__ == "__main__":
    unittest.main()
