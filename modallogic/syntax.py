"""Modal logic syntax AST, recursive descent parser, and normalization."""

from abc import ABC, abstractmethod
from typing import Set, Tuple, Any, List
import re


class Formula(ABC):
    """Abstract base class for modal logic formulas."""

    @abstractmethod
    def atoms(self) -> Set[str]:
        """Return the set of propositional atoms appearing in this formula."""
        pass

    @abstractmethod
    def subformulas(self) -> Set["Formula"]:
        """Return all subformulas of this formula."""
        pass

    @abstractmethod
    def complexity(self) -> int:
        """Return the number of logical connectives and atoms."""
        pass

    @abstractmethod
    def to_tuple(self) -> Tuple[Any, ...]:
        """Convert to legacy/compact tuple format."""
        pass

    @abstractmethod
    def to_nnf(self) -> "Formula":
        """Convert formula to Negation Normal Form."""
        pass

    def to_latex(self) -> str:
        """Export formula to LaTeX notation."""
        return str(self)

    def __repr__(self) -> str:
        return self.__str__()


class Atom(Formula):
    def __init__(self, name: str):
        if not isinstance(name, str) or not name:
            raise ValueError("Atom name must be a non-empty string")
        self.name = name

    def atoms(self) -> Set[str]:
        return {self.name}

    def subformulas(self) -> Set[Formula]:
        return {self}

    def complexity(self) -> int:
        return 1

    def to_tuple(self) -> Tuple[Any, ...]:
        return ("ATOM", self.name)

    def to_nnf(self) -> Formula:
        return self

    def __eq__(self, other: Any) -> bool:
        return isinstance(other, Atom) and self.name == other.name

    def __hash__(self) -> int:
        return hash(("ATOM", self.name))

    def __str__(self) -> str:
        return self.name


class Top(Formula):
    def atoms(self) -> Set[str]:
        return set()

    def subformulas(self) -> Set[Formula]:
        return {self}

    def complexity(self) -> int:
        return 1

    def to_tuple(self) -> Tuple[Any, ...]:
        return ("TOP",)

    def to_nnf(self) -> Formula:
        return self

    def __eq__(self, other: Any) -> bool:
        return isinstance(other, Top)

    def __hash__(self) -> int:
        return hash("TOP")

    def __str__(self) -> str:
        return "TOP"


class Bottom(Formula):
    def atoms(self) -> Set[str]:
        return set()

    def subformulas(self) -> Set[Formula]:
        return {self}

    def complexity(self) -> int:
        return 1

    def to_tuple(self) -> Tuple[Any, ...]:
        return ("BOTTOM",)

    def to_nnf(self) -> Formula:
        return self

    def __eq__(self, other: Any) -> bool:
        return isinstance(other, Bottom)

    def __hash__(self) -> int:
        return hash("BOTTOM")

    def __str__(self) -> str:
        return "BOTTOM"


class Not(Formula):
    def __init__(self, inner: Formula):
        if not isinstance(inner, Formula):
            raise TypeError("Inner element must be a Formula")
        self.inner = inner

    def atoms(self) -> Set[str]:
        return self.inner.atoms()

    def subformulas(self) -> Set[Formula]:
        return {self} | self.inner.subformulas()

    def complexity(self) -> int:
        return 1 + self.inner.complexity()

    def to_tuple(self) -> Tuple[Any, ...]:
        return ("NOT", self.inner.to_tuple())

    def to_nnf(self) -> Formula:
        if isinstance(self.inner, Atom):
            return self
        if isinstance(self.inner, Top):
            return Bottom()
        if isinstance(self.inner, Bottom):
            return Top()
        if isinstance(self.inner, Not):
            return self.inner.inner.to_nnf()
        if isinstance(self.inner, And):
            # ~(A & B) = ~A | ~B
            return Or(Not(self.inner.left).to_nnf(), Not(self.inner.right).to_nnf())
        if isinstance(self.inner, Or):
            # ~(A | B) = ~A & ~B
            return And(Not(self.inner.left).to_nnf(), Not(self.inner.right).to_nnf())
        if isinstance(self.inner, Implies):
            # ~(A -> B) = A & ~B
            return And(self.inner.left.to_nnf(), Not(self.inner.right).to_nnf())
        if isinstance(self.inner, Iff):
            # ~(A <-> B) = (A & ~B) | (~A & B)
            a = self.inner.left
            b = self.inner.right
            return Or(
                And(a.to_nnf(), Not(b).to_nnf()),
                And(Not(a).to_nnf(), b.to_nnf()),
            )
        if isinstance(self.inner, Box):
            # ~[]A = <>~A
            return Dia(Not(self.inner.inner).to_nnf())
        if isinstance(self.inner, Dia):
            # ~<>A = []~A
            return Box(Not(self.inner.inner).to_nnf())
        if isinstance(self.inner, (Knows, CommonKnowledge, DistributedKnowledge, PublicAnnouncement)):
            return Not(self.inner.to_nnf())
        raise TypeError(f"Unsupported formula type in Not: {type(self.inner)}")

    def __eq__(self, other: Any) -> bool:
        return isinstance(other, Not) and self.inner == other.inner

    def __hash__(self) -> int:
        return hash(("NOT", self.inner))

    def __str__(self) -> str:
        if isinstance(self.inner, (Atom, Top, Bottom)):
            return f"~{self.inner}"
        return f"~({self.inner})"


class And(Formula):
    def __init__(self, left: Formula, right: Formula):
        if not isinstance(left, Formula) or not isinstance(right, Formula):
            raise TypeError("Operands must be Formula instances")
        self.left = left
        self.right = right

    def atoms(self) -> Set[str]:
        return self.left.atoms() | self.right.atoms()

    def subformulas(self) -> Set[Formula]:
        return {self} | self.left.subformulas() | self.right.subformulas()

    def complexity(self) -> int:
        return 1 + self.left.complexity() + self.right.complexity()

    def to_tuple(self) -> Tuple[Any, ...]:
        return ("AND", self.left.to_tuple(), self.right.to_tuple())

    def to_nnf(self) -> Formula:
        return And(self.left.to_nnf(), self.right.to_nnf())

    def __eq__(self, other: Any) -> bool:
        return isinstance(other, And) and self.left == other.left and self.right == other.right

    def __hash__(self) -> int:
        return hash(("AND", self.left, self.right))

    def __str__(self) -> str:
        l_str = str(self.left)
        r_str = str(self.right)
        if isinstance(self.left, (Or, Implies, Iff)):
            l_str = f"({l_str})"
        if isinstance(self.right, (Or, Implies, Iff)):
            r_str = f"({r_str})"
        return f"{l_str} & {r_str}"


class Or(Formula):
    def __init__(self, left: Formula, right: Formula):
        if not isinstance(left, Formula) or not isinstance(right, Formula):
            raise TypeError("Operands must be Formula instances")
        self.left = left
        self.right = right

    def atoms(self) -> Set[str]:
        return self.left.atoms() | self.right.atoms()

    def subformulas(self) -> Set[Formula]:
        return {self} | self.left.subformulas() | self.right.subformulas()

    def complexity(self) -> int:
        return 1 + self.left.complexity() + self.right.complexity()

    def to_tuple(self) -> Tuple[Any, ...]:
        return ("OR", self.left.to_tuple(), self.right.to_tuple())

    def to_nnf(self) -> Formula:
        return Or(self.left.to_nnf(), self.right.to_nnf())

    def __eq__(self, other: Any) -> bool:
        return isinstance(other, Or) and self.left == other.left and self.right == other.right

    def __hash__(self) -> int:
        return hash(("OR", self.left, self.right))

    def __str__(self) -> str:
        l_str = str(self.left)
        r_str = str(self.right)
        if isinstance(self.left, (Implies, Iff)):
            l_str = f"({l_str})"
        if isinstance(self.right, (Implies, Iff)):
            r_str = f"({r_str})"
        return f"{l_str} | {r_str}"


class Implies(Formula):
    def __init__(self, left: Formula, right: Formula):
        if not isinstance(left, Formula) or not isinstance(right, Formula):
            raise TypeError("Operands must be Formula instances")
        self.left = left
        self.right = right

    def atoms(self) -> Set[str]:
        return self.left.atoms() | self.right.atoms()

    def subformulas(self) -> Set[Formula]:
        return {self} | self.left.subformulas() | self.right.subformulas()

    def complexity(self) -> int:
        return 1 + self.left.complexity() + self.right.complexity()

    def to_tuple(self) -> Tuple[Any, ...]:
        return ("IMPL", self.left.to_tuple(), self.right.to_tuple())

    def to_nnf(self) -> Formula:
        # A -> B is ~A | B
        return Or(Not(self.left).to_nnf(), self.right.to_nnf())

    def __eq__(self, other: Any) -> bool:
        return isinstance(other, Implies) and self.left == other.left and self.right == other.right

    def __hash__(self) -> int:
        return hash(("IMPL", self.left, self.right))

    def __str__(self) -> str:
        l_str = str(self.left)
        r_str = str(self.right)
        if isinstance(self.left, (Implies, Iff)):
            l_str = f"({l_str})"
        return f"{l_str} -> {r_str}"


class Iff(Formula):
    def __init__(self, left: Formula, right: Formula):
        if not isinstance(left, Formula) or not isinstance(right, Formula):
            raise TypeError("Operands must be Formula instances")
        self.left = left
        self.right = right

    def atoms(self) -> Set[str]:
        return self.left.atoms() | self.right.atoms()

    def subformulas(self) -> Set[Formula]:
        return {self} | self.left.subformulas() | self.right.subformulas()

    def complexity(self) -> int:
        return 1 + self.left.complexity() + self.right.complexity()

    def to_tuple(self) -> Tuple[Any, ...]:
        return ("IFF", self.left.to_tuple(), self.right.to_tuple())

    def to_nnf(self) -> Formula:
        # (A -> B) & (B -> A) = (~A | B) & (~B | A)
        return And(
            Or(Not(self.left).to_nnf(), self.right.to_nnf()),
            Or(Not(self.right).to_nnf(), self.left.to_nnf()),
        )

    def __eq__(self, other: Any) -> bool:
        return isinstance(other, Iff) and self.left == other.left and self.right == other.right

    def __hash__(self) -> int:
        return hash(("IFF", self.left, self.right))

    def __str__(self) -> str:
        return f"({self.left} <-> {self.right})"


class Box(Formula):
    def __init__(self, inner: Formula):
        if not isinstance(inner, Formula):
            raise TypeError("Inner element must be a Formula")
        self.inner = inner

    def atoms(self) -> Set[str]:
        return self.inner.atoms()

    def subformulas(self) -> Set[Formula]:
        return {self} | self.inner.subformulas()

    def complexity(self) -> int:
        return 1 + self.inner.complexity()

    def to_tuple(self) -> Tuple[Any, ...]:
        return ("BOX", self.inner.to_tuple())

    def to_nnf(self) -> Formula:
        return Box(self.inner.to_nnf())

    def __eq__(self, other: Any) -> bool:
        return isinstance(other, Box) and self.inner == other.inner

    def __hash__(self) -> int:
        return hash(("BOX", self.inner))

    def __str__(self) -> str:
        if isinstance(self.inner, (Atom, Top, Bottom, Box, Dia)):
            return f"[]{self.inner}"
        return f"[]({self.inner})"


class Dia(Formula):
    def __init__(self, inner: Formula):
        if not isinstance(inner, Formula):
            raise TypeError("Inner element must be a Formula")
        self.inner = inner

    def atoms(self) -> Set[str]:
        return self.inner.atoms()

    def subformulas(self) -> Set[Formula]:
        return {self} | self.inner.subformulas()

    def complexity(self) -> int:
        return 1 + self.inner.complexity()

    def to_tuple(self) -> Tuple[Any, ...]:
        return ("DIA", self.inner.to_tuple())

    def to_nnf(self) -> Formula:
        return Dia(self.inner.to_nnf())

    def __eq__(self, other: Any) -> bool:
        return isinstance(other, Dia) and self.inner == other.inner

    def __hash__(self) -> int:
        return hash(("DIA", self.inner))

    def __str__(self) -> str:
        if isinstance(self.inner, (Atom, Top, Bottom, Box, Dia)):
            return f"<>{self.inner}"
        return f"<>({self.inner})"


class Knows(Formula):
    """Multi-agent epistemic operator K_i(phi): agent i knows phi."""

    def __init__(self, agent_id: str, formula: Formula):
        if not isinstance(agent_id, str) or not agent_id:
            raise ValueError("Agent ID must be a non-empty string")
        if not isinstance(formula, Formula):
            raise TypeError("Inner element must be a Formula")
        self.agent_id = agent_id
        self.formula = formula
        self.inner = formula

    def atoms(self) -> Set[str]:
        return self.formula.atoms()

    def subformulas(self) -> Set[Formula]:
        return {self} | self.formula.subformulas()

    def complexity(self) -> int:
        return 1 + self.formula.complexity()

    def to_tuple(self) -> Tuple[Any, ...]:
        return ("KNOWS", self.agent_id, self.formula.to_tuple())

    def to_nnf(self) -> Formula:
        return Knows(self.agent_id, self.formula.to_nnf())

    def to_latex(self) -> str:
        return f"K_{{{self.agent_id}}}({self.formula.to_latex()})"

    def __eq__(self, other: Any) -> bool:
        return (
            isinstance(other, Knows)
            and self.agent_id == other.agent_id
            and self.formula == other.formula
        )

    def __hash__(self) -> int:
        return hash(("KNOWS", self.agent_id, self.formula))

    def __str__(self) -> str:
        if isinstance(self.formula, (Atom, Top, Bottom)):
            return f"K_{self.agent_id} {self.formula}"
        return f"K_{self.agent_id}({self.formula})"


class CommonKnowledge(Formula):
    """Group common knowledge operator C_G(phi): everyone in group G knows phi recursively."""

    def __init__(self, agent_group: Any, formula: Formula):
        group_tuple = tuple(sorted(str(a) for a in agent_group))
        if not group_tuple:
            raise ValueError("Agent group must be non-empty")
        if not isinstance(formula, Formula):
            raise TypeError("Inner element must be a Formula")
        self.agent_group: Tuple[str, ...] = group_tuple
        self.formula = formula
        self.inner = formula

    def atoms(self) -> Set[str]:
        return self.formula.atoms()

    def subformulas(self) -> Set[Formula]:
        return {self} | self.formula.subformulas()

    def complexity(self) -> int:
        return 1 + self.formula.complexity()

    def to_tuple(self) -> Tuple[Any, ...]:
        return ("COMMON_KNOWLEDGE", self.agent_group, self.formula.to_tuple())

    def to_nnf(self) -> Formula:
        return CommonKnowledge(self.agent_group, self.formula.to_nnf())

    def to_latex(self) -> str:
        grp = ",".join(self.agent_group)
        return f"C_{{{grp}}}({self.formula.to_latex()})"

    def __eq__(self, other: Any) -> bool:
        return (
            isinstance(other, CommonKnowledge)
            and self.agent_group == other.agent_group
            and self.formula == other.formula
        )

    def __hash__(self) -> int:
        return hash(("COMMON_KNOWLEDGE", self.agent_group, self.formula))

    def __str__(self) -> str:
        grp = ",".join(self.agent_group)
        return f"C_{{{grp}}}({self.formula})"


class DistributedKnowledge(Formula):
    """Group distributed knowledge operator D_G(phi): combined knowledge of group G implies phi."""

    def __init__(self, agent_group: Any, formula: Formula):
        group_tuple = tuple(sorted(str(a) for a in agent_group))
        if not group_tuple:
            raise ValueError("Agent group must be non-empty")
        if not isinstance(formula, Formula):
            raise TypeError("Inner element must be a Formula")
        self.agent_group: Tuple[str, ...] = group_tuple
        self.formula = formula
        self.inner = formula

    def atoms(self) -> Set[str]:
        return self.formula.atoms()

    def subformulas(self) -> Set[Formula]:
        return {self} | self.formula.subformulas()

    def complexity(self) -> int:
        return 1 + self.formula.complexity()

    def to_tuple(self) -> Tuple[Any, ...]:
        return ("DISTRIBUTED_KNOWLEDGE", self.agent_group, self.formula.to_tuple())

    def to_nnf(self) -> Formula:
        return DistributedKnowledge(self.agent_group, self.formula.to_nnf())

    def to_latex(self) -> str:
        grp = ",".join(self.agent_group)
        return f"D_{{{grp}}}({self.formula.to_latex()})"

    def __eq__(self, other: Any) -> bool:
        return (
            isinstance(other, DistributedKnowledge)
            and self.agent_group == other.agent_group
            and self.formula == other.formula
        )

    def __hash__(self) -> int:
        return hash(("DISTRIBUTED_KNOWLEDGE", self.agent_group, self.formula))

    def __str__(self) -> str:
        grp = ",".join(self.agent_group)
        return f"D_{{{grp}}}({self.formula})"


class PublicAnnouncement(Formula):
    """Dynamic epistemic public announcement operator [announcement] target_formula."""

    def __init__(self, announcement: Formula, target_formula: Formula):
        if not isinstance(announcement, Formula) or not isinstance(target_formula, Formula):
            raise TypeError("Both announcement and target_formula must be Formula instances")
        self.announcement = announcement
        self.target_formula = target_formula

    def atoms(self) -> Set[str]:
        return self.announcement.atoms() | self.target_formula.atoms()

    def subformulas(self) -> Set[Formula]:
        return {self} | self.announcement.subformulas() | self.target_formula.subformulas()

    def complexity(self) -> int:
        return 1 + self.announcement.complexity() + self.target_formula.complexity()

    def to_tuple(self) -> Tuple[Any, ...]:
        return (
            "PUBLIC_ANNOUNCEMENT",
            self.announcement.to_tuple(),
            self.target_formula.to_tuple(),
        )

    def to_nnf(self) -> Formula:
        return PublicAnnouncement(self.announcement.to_nnf(), self.target_formula.to_nnf())

    def to_latex(self) -> str:
        return f"[{self.announcement.to_latex!}]{self.target_formula.to_latex()}" if False else f"[{self.announcement.to_latex()}]{self.target_formula.to_latex()}"

    def __eq__(self, other: Any) -> bool:
        return (
            isinstance(other, PublicAnnouncement)
            and self.announcement == other.announcement
            and self.target_formula == other.target_formula
        )

    def __hash__(self) -> int:
        return hash(("PUBLIC_ANNOUNCEMENT", self.announcement, self.target_formula))

    def __str__(self) -> str:
        return f"[{self.announcement}] {self.target_formula}"


def from_tuple(raw: Tuple[Any, ...]) -> Formula:
    """Convert tuple representation to Formula AST."""
    if not isinstance(raw, tuple) or len(raw) == 0:
        raise ValueError(f"Invalid formula tuple: {raw}")
    kind = raw[0]
    if kind == "ATOM":
        return Atom(raw[1])
    if kind == "TOP":
        return Top()
    if kind == "BOTTOM":
        return Bottom()
    if kind == "NOT":
        return Not(from_tuple(raw[1]))
    if kind == "AND":
        return And(from_tuple(raw[1]), from_tuple(raw[2]))
    if kind == "OR":
        return Or(from_tuple(raw[1]), from_tuple(raw[2]))
    if kind == "IMPL":
        return Implies(from_tuple(raw[1]), from_tuple(raw[2]))
    if kind == "IFF":
        return Iff(from_tuple(raw[1]), from_tuple(raw[2]))
    if kind == "BOX":
        return Box(from_tuple(raw[1]))
    if kind == "DIA":
        return Dia(from_tuple(raw[1]))
    if kind == "KNOWS":
        return Knows(raw[1], from_tuple(raw[2]))
    if kind == "COMMON_KNOWLEDGE":
        return CommonKnowledge(raw[1], from_tuple(raw[2]))
    if kind == "DISTRIBUTED_KNOWLEDGE":
        return DistributedKnowledge(raw[1], from_tuple(raw[2]))
    if kind == "PUBLIC_ANNOUNCEMENT":
        return PublicAnnouncement(from_tuple(raw[1]), from_tuple(raw[2]))
    raise ValueError(f"Unknown formula kind: {kind}")


class Parser:
    """Tokenizer and recursive descent parser for modal propositional logic formulas."""

    TOKEN_REGEX = re.compile(
        r"""
        \s*(?:
            (<->|<=>)              | # IFF (1)
            (->|=>)                | # IMPL (2)
            (\[\]|\[\s*\])         | # BOX (3)
            (<>|<\s*>)             | # DIA (4)
            (&&|&|/\\)             | # AND (5)
            (\|\||\||\\/)          | # OR  (6)
            (~|!|NOT|not)          | # NOT (7)
            (\()                   | # LPAREN (8)
            (\))                   | # RPAREN (9)
            (TOP|TRUE|true|1|\\top)| # TOP (10)
            (BOT|BOTTOM|false|0|\\bot) | # BOTTOM (11)
            ([a-zA-Z_][a-zA-Z0-9_]*) # IDENTIFIER (12)
        )
        """,
        re.VERBOSE,
    )

    def __init__(self, text: str):
        self.tokens: List[Tuple[str, str]] = []
        pos = 0
        text_len = len(text)
        while pos < text_len:
            match = self.TOKEN_REGEX.match(text, pos)
            if not match:
                remaining = text[pos:].strip()
                if not remaining:
                    break
                raise ValueError(f"Syntax error near: {text[pos:pos+15]!r}")
            pos = match.end()
            for group_idx, kind in enumerate(
                [
                    "IFF",
                    "IMPL",
                    "BOX",
                    "DIA",
                    "AND",
                    "OR",
                    "NOT",
                    "LPAREN",
                    "RPAREN",
                    "TOP",
                    "BOTTOM",
                    "ATOM",
                ],
                start=1,
            ):
                val = match.group(group_idx)
                if val is not None:
                    self.tokens.append((kind, val))
                    break
        self.tokens.append(("EOF", ""))
        self.cursor = 0

    def peek(self) -> Tuple[str, str]:
        return self.tokens[self.cursor]

    def advance(self) -> Tuple[str, str]:
        tok = self.tokens[self.cursor]
        if self.cursor < len(self.tokens) - 1:
            self.cursor += 1
        return tok

    def match(self, kind: str) -> bool:
        if self.peek()[0] == kind:
            self.advance()
            return True
        return False

    def expect(self, kind: str) -> Tuple[str, str]:
        tok = self.peek()
        if tok[0] != kind:
            raise ValueError(f"Expected {kind}, but found {tok[0]} ({tok[1]!r})")
        return self.advance()

    def parse(self) -> Formula:
        res = self.parse_equivalence()
        if self.peek()[0] != "EOF":
            tok = self.peek()
            raise ValueError(f"Unexpected trailing token: {tok[0]} ({tok[1]!r})")
        return res

    def parse_equivalence(self) -> Formula:
        expr = self.parse_implication()
        while self.match("IFF"):
            right = self.parse_implication()
            expr = Iff(expr, right)
        return expr

    def parse_implication(self) -> Formula:
        # Implication is right-associative: A -> B -> C is A -> (B -> C)
        expr = self.parse_or()
        if self.match("IMPL"):
            right = self.parse_implication()
            return Implies(expr, right)
        return expr

    def parse_or(self) -> Formula:
        expr = self.parse_and()
        while self.match("OR"):
            right = self.parse_and()
            expr = Or(expr, right)
        return expr

    def parse_and(self) -> Formula:
        expr = self.parse_unary()
        while self.match("AND"):
            right = self.parse_unary()
            expr = And(expr, right)
        return expr

    def parse_unary(self) -> Formula:
        tok = self.peek()
        if self.match("NOT"):
            return Not(self.parse_unary())
        if self.match("BOX"):
            return Box(self.parse_unary())
        if self.match("DIA"):
            return Dia(self.parse_unary())
        return self.parse_primary()

    def parse_primary(self) -> Formula:
        tok = self.peek()
        if self.match("LPAREN"):
            expr = self.parse_equivalence()
            self.expect("RPAREN")
            return expr
        if self.match("TOP"):
            return Top()
        if self.match("BOTTOM"):
            return Bottom()
        if self.match("ATOM"):
            return Atom(tok[1])
        raise ValueError(f"Unexpected token in expression: {tok[0]} ({tok[1]!r})")


def parse_formula(s: str) -> Formula:
    """Parse a modal logic string into a Formula AST."""
    return Parser(s).parse()
