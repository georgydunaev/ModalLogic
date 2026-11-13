#!/usr/bin/env python3
"""Unit tests for modal logic syntax AST, recursive descent parser, and NNF."""

import os
import sys
import unittest

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
if ROOT not in sys.path:
    sys.path.insert(0, ROOT)

from modallogic.syntax import (
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
    from_tuple,
)


class TestModalLogicSyntax(unittest.TestCase):
    def test_ast_construction_and_atoms(self):
        phi = Implies(Box(And(Atom("p"), Atom("q"))), Dia(Or(Atom("p"), Atom("r"))))
        self.assertEqual(phi.atoms(), {"p", "q", "r"})
        self.assertGreater(phi.complexity(), 5)
        self.assertIn(Atom("p"), phi.subformulas())
        self.assertIn(Box(And(Atom("p"), Atom("q"))), phi.subformulas())

    def test_constants_and_atoms(self):
        top = Top()
        bot = Bottom()
        p = Atom("p")
        self.assertEqual(top.atoms(), set())
        self.assertEqual(bot.atoms(), set())
        self.assertEqual(str(top), "TOP")
        self.assertEqual(str(bot), "BOTTOM")
        self.assertEqual(str(p), "p")

    def test_tuple_conversion_roundtrip(self):
        phi = Implies(Box(Atom("p")), Dia(Atom("q")))
        raw_tuple = phi.to_tuple()
        self.assertEqual(raw_tuple, ("IMPL", ("BOX", ("ATOM", "p")), ("DIA", ("ATOM", "q"))))
        reconstructed = from_tuple(raw_tuple)
        self.assertEqual(phi, reconstructed)

    def test_parser_basic(self):
        f1 = parse_formula("p -> q")
        self.assertEqual(f1, Implies(Atom("p"), Atom("q")))

        f2 = parse_formula("[]p -> p")
        self.assertEqual(f2, Implies(Box(Atom("p")), Atom("p")))

        f3 = parse_formula("<>p & ~q")
        self.assertEqual(f3, And(Dia(Atom("p")), Not(Atom("q"))))

        f4 = parse_formula("p <-> q")
        self.assertEqual(f4, Iff(Atom("p"), Atom("q")))

    def test_parser_precedence_and_associativity(self):
        # Implication is right-associative: p -> q -> r == p -> (q -> r)
        f = parse_formula("p -> q -> r")
        expected = Implies(Atom("p"), Implies(Atom("q"), Atom("r")))
        self.assertEqual(f, expected)

        # Precedence: & binds tighter than |, which binds tighter than ->
        f2 = parse_formula("p & q | r -> s")
        expected2 = Implies(Or(And(Atom("p"), Atom("q")), Atom("r")), Atom("s"))
        self.assertEqual(f2, expected2)

        # Modalities bind tightly
        f3 = parse_formula("[]p & <>q")
        self.assertEqual(f3, And(Box(Atom("p")), Dia(Atom("q"))))

        # Nested modalities
        f4 = parse_formula("[][]p -> <>[]q")
        self.assertEqual(f4, Implies(Box(Box(Atom("p"))), Dia(Box(Atom("q")))))

    def test_parser_constants(self):
        f1 = parse_formula("TOP -> true")
        self.assertEqual(f1, Implies(Top(), Top()))
        f2 = parse_formula("BOT | false")
        self.assertEqual(f2, Or(Bottom(), Bottom()))

    def test_parser_syntax_errors(self):
        with self.assertRaises(ValueError):
            parse_formula("p ->")
        with self.assertRaises(ValueError):
            parse_formula("(p & q")
        with self.assertRaises(ValueError):
            parse_formula("& p")

    def test_negation_normal_form(self):
        # ~(p & q) => ~p | ~q
        f1 = Not(And(Atom("p"), Atom("q"))).to_nnf()
        self.assertEqual(f1, Or(Not(Atom("p")), Not(Atom("q"))))

        # ~(p | q) => ~p & ~q
        f2 = Not(Or(Atom("p"), Atom("q"))).to_nnf()
        self.assertEqual(f2, And(Not(Atom("p")), Not(Atom("q"))))

        # ~[]p => <>~p
        f3 = Not(Box(Atom("p"))).to_nnf()
        self.assertEqual(f3, Dia(Not(Atom("p"))))

        # ~<>p => []~p
        f4 = Not(Dia(Atom("p"))).to_nnf()
        self.assertEqual(f4, Box(Not(Atom("p"))))

        # ~~p => p
        f5 = Not(Not(Atom("p"))).to_nnf()
        self.assertEqual(f5, Atom("p"))

        # ~(p -> q) => p & ~q
        f6 = Not(Implies(Atom("p"), Atom("q"))).to_nnf()
        self.assertEqual(f6, And(Atom("p"), Not(Atom("q"))))


if __name__ == "__main__":
    unittest.main()
