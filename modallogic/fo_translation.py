"""First-order standard translation (ST_x) from modal logic into classical first-order logic.

Implements van Benthem's Standard Translation mapping propositional modal logic
into the two-variable fragment of classical first-order logic (FO^2) with
unary predicates P(x) for atoms and binary relation symbols R(x, y).
"""

from abc import ABC, abstractmethod
from typing import Set, Dict, Any, Optional, Tuple
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
)
from .semantics import KripkeModel, KripkeFrame


class FOFormula(ABC):
    """Abstract base class for first-order formulas."""

    @abstractmethod
    def free_variables(self) -> Set[str]:
        """Return the set of free variable names in this formula."""
        pass

    @abstractmethod
    def bound_variables(self) -> Set[str]:
        """Return the set of bound variable names in this formula."""
        pass

    def variables(self) -> Set[str]:
        """Return all variables appearing in this formula."""
        return self.free_variables() | self.bound_variables()

    @abstractmethod
    def complexity(self) -> int:
        """Return the syntactic complexity (count of operators and atomic terms)."""
        pass

    @abstractmethod
    def subformulas(self) -> Set["FOFormula"]:
        """Return the set of all syntactic subformulas."""
        pass

    @abstractmethod
    def evaluate(self, model: KripkeModel, env: Dict[str, Any]) -> bool:
        """Evaluate formula truth on a Kripke model under variable assignment env."""
        pass

    @abstractmethod
    def to_string(self, style: str = "standard") -> str:
        """Format as string.
        
        Styles:
          - 'standard': uses /\\, \\/, ->, <->, ~, forall, exists
          - 'compact': uses &, |, ->, <->, ~, forall, exists
          - 'words': uses /\\, \\/, implies, iff, ~, forall, exists
        """
        pass

    @abstractmethod
    def to_latex(self) -> str:
        """Return LaTeX string representation."""
        pass

    def __and__(self, other: "FOFormula") -> "FOFormula":
        return FOAnd(self, other)

    def __or__(self, other: "FOFormula") -> "FOFormula":
        return FOOr(self, other)

    def __invert__(self) -> "FOFormula":
        return FONot(self)

    def __rshift__(self, other: "FOFormula") -> "FOFormula":
        return FOImplies(self, other)

    def __repr__(self) -> str:
        return self.to_string("standard")

    def __str__(self) -> str:
        return self.to_string("standard")


class FOTop(FOFormula):
    """First-order constant True / TOP."""

    def free_variables(self) -> Set[str]:
        return set()

    def bound_variables(self) -> Set[str]:
        return set()

    def complexity(self) -> int:
        return 1

    def subformulas(self) -> Set[FOFormula]:
        return {self}

    def evaluate(self, model: KripkeModel, env: Dict[str, Any]) -> bool:
        return True

    def to_string(self, style: str = "standard") -> str:
        return "TOP"

    def to_latex(self) -> str:
        return r"\top"

    def __eq__(self, other: Any) -> bool:
        return isinstance(other, FOTop)

    def __hash__(self) -> int:
        return hash("FO_TOP")


class FOBottom(FOFormula):
    """First-order constant False / BOTTOM."""

    def free_variables(self) -> Set[str]:
        return set()

    def bound_variables(self) -> Set[str]:
        return set()

    def complexity(self) -> int:
        return 1

    def subformulas(self) -> Set[FOFormula]:
        return {self}

    def evaluate(self, model: KripkeModel, env: Dict[str, Any]) -> bool:
        return False

    def to_string(self, style: str = "standard") -> str:
        return "BOTTOM"

    def to_latex(self) -> str:
        return r"\bot"

    def __eq__(self, other: Any) -> bool:
        return isinstance(other, FOBottom)

    def __hash__(self) -> int:
        return hash("FO_BOTTOM")


class Predicate(FOFormula):
    """Unary predicate symbol P(x) representing propositional atom p at world x."""

    def __init__(self, name: str, var: str):
        if not isinstance(name, str) or not name:
            raise ValueError("Predicate name must be non-empty string")
        if not isinstance(var, str) or not var:
            raise ValueError("Variable must be non-empty string")
        self.name = name
        self.var = var

    def free_variables(self) -> Set[str]:
        return {self.var}

    def bound_variables(self) -> Set[str]:
        return set()

    def complexity(self) -> int:
        return 1

    def subformulas(self) -> Set[FOFormula]:
        return {self}

    def evaluate(self, model: KripkeModel, env: Dict[str, Any]) -> bool:
        if self.var not in env:
            raise KeyError(f"Variable {self.var!r} unassigned in environment {env}")
        world = env[self.var]
        # Match predicate against valuation keys
        val = None
        if self.name in model.valuation:
            val = model.valuation[self.name]
        elif self.name.lower() in model.valuation:
            val = model.valuation[self.name.lower()]
        elif self.name.upper() in model.valuation:
            val = model.valuation[self.name.upper()]
        else:
            val = set()
        return world in val

    def to_string(self, style: str = "standard") -> str:
        return f"{self.name}({self.var})"

    def to_latex(self) -> str:
        return f"{self.name}({self.var})"

    def __eq__(self, other: Any) -> bool:
        return isinstance(other, Predicate) and self.name == other.name and self.var == other.var

    def __hash__(self) -> int:
        return hash(("PRED", self.name, self.var))


class Relation(FOFormula):
    """Binary relation symbol R(x, y) representing accessibility between worlds."""

    def __init__(self, rel_name: str, arg1: str, arg2: str):
        if not isinstance(rel_name, str) or not rel_name:
            raise ValueError("Relation name must be non-empty string")
        if not isinstance(arg1, str) or not arg1 or not isinstance(arg2, str) or not arg2:
            raise ValueError("Arguments must be non-empty strings")
        self.rel_name = rel_name
        self.arg1 = arg1
        self.arg2 = arg2

    def free_variables(self) -> Set[str]:
        return {self.arg1, self.arg2}

    def bound_variables(self) -> Set[str]:
        return set()

    def complexity(self) -> int:
        return 1

    def subformulas(self) -> Set[FOFormula]:
        return {self}

    def evaluate(self, model: KripkeModel, env: Dict[str, Any]) -> bool:
        if self.arg1 not in env:
            raise KeyError(f"Variable {self.arg1!r} unassigned in environment {env}")
        if self.arg2 not in env:
            raise KeyError(f"Variable {self.arg2!r} unassigned in environment {env}")
        w1 = env[self.arg1]
        w2 = env[self.arg2]
        return (w1, w2) in model.frame.relation

    def to_string(self, style: str = "standard") -> str:
        return f"{self.rel_name}({self.arg1}, {self.arg2})"

    def to_latex(self) -> str:
        return f"{self.rel_name}({self.arg1}, {self.arg2})"

    def __eq__(self, other: Any) -> bool:
        return (
            isinstance(other, Relation)
            and self.rel_name == other.rel_name
            and self.arg1 == other.arg1
            and self.arg2 == other.arg2
        )

    def __hash__(self) -> int:
        return hash(("REL", self.rel_name, self.arg1, self.arg2))


class Equality(FOFormula):
    """First-order equality atom x = y."""

    def __init__(self, arg1: str, arg2: str):
        if not isinstance(arg1, str) or not arg1 or not isinstance(arg2, str) or not arg2:
            raise ValueError("Arguments must be non-empty strings")
        self.arg1 = arg1
        self.arg2 = arg2

    def free_variables(self) -> Set[str]:
        return {self.arg1, self.arg2}

    def bound_variables(self) -> Set[str]:
        return set()

    def complexity(self) -> int:
        return 1

    def subformulas(self) -> Set[FOFormula]:
        return {self}

    def evaluate(self, model: KripkeModel, env: Dict[str, Any]) -> bool:
        if self.arg1 not in env:
            raise KeyError(f"Variable {self.arg1!r} unassigned in environment {env}")
        if self.arg2 not in env:
            raise KeyError(f"Variable {self.arg2!r} unassigned in environment {env}")
        return env[self.arg1] == env[self.arg2]

    def to_string(self, style: str = "standard") -> str:
        return f"{self.arg1} = {self.arg2}"

    def to_latex(self) -> str:
        return f"{self.arg1} = {self.arg2}"

    def __eq__(self, other: Any) -> bool:
        return isinstance(other, Equality) and self.arg1 == other.arg1 and self.arg2 == other.arg2

    def __hash__(self) -> int:
        return hash(("EQ", self.arg1, self.arg2))


class FONot(FOFormula):
    """First-order negation ~phi."""

    def __init__(self, inner: FOFormula):
        if not isinstance(inner, FOFormula):
            raise TypeError("inner must be an FOFormula instance")
        self.inner = inner

    def free_variables(self) -> Set[str]:
        return self.inner.free_variables()

    def bound_variables(self) -> Set[str]:
        return self.inner.bound_variables()

    def complexity(self) -> int:
        return 1 + self.inner.complexity()

    def subformulas(self) -> Set[FOFormula]:
        return {self} | self.inner.subformulas()

    def evaluate(self, model: KripkeModel, env: Dict[str, Any]) -> bool:
        return not self.inner.evaluate(model, env)

    def to_string(self, style: str = "standard") -> str:
        inner_s = self.inner.to_string(style)
        if isinstance(self.inner, (Predicate, Relation, Equality, FOTop, FOBottom)):
            return f"~{inner_s}"
        return f"~({inner_s})"

    def to_latex(self) -> str:
        inner_l = self.inner.to_latex()
        if isinstance(self.inner, (Predicate, Relation, Equality, FOTop, FOBottom)):
            return rf"\neg {inner_l}"
        return rf"\neg ({inner_l})"

    def __eq__(self, other: Any) -> bool:
        return isinstance(other, FONot) and self.inner == other.inner

    def __hash__(self) -> int:
        return hash(("FO_NOT", self.inner))


class FOAnd(FOFormula):
    """First-order conjunction phi /\\ psi."""

    def __init__(self, left: FOFormula, right: FOFormula):
        if not isinstance(left, FOFormula) or not isinstance(right, FOFormula):
            raise TypeError("Operands must be FOFormula instances")
        self.left = left
        self.right = right

    def free_variables(self) -> Set[str]:
        return self.left.free_variables() | self.right.free_variables()

    def bound_variables(self) -> Set[str]:
        return self.left.bound_variables() | self.right.bound_variables()

    def complexity(self) -> int:
        return 1 + self.left.complexity() + self.right.complexity()

    def subformulas(self) -> Set[FOFormula]:
        return {self} | self.left.subformulas() | self.right.subformulas()

    def evaluate(self, model: KripkeModel, env: Dict[str, Any]) -> bool:
        return self.left.evaluate(model, env) and self.right.evaluate(model, env)

    def to_string(self, style: str = "standard") -> str:
        conn = " & " if style == "compact" else " /\\ "
        return f"({self.left.to_string(style)}{conn}{self.right.to_string(style)})"

    def to_latex(self) -> str:
        return rf"({self.left.to_latex()} \land {self.right.to_latex()})"

    def __eq__(self, other: Any) -> bool:
        return isinstance(other, FOAnd) and self.left == other.left and self.right == other.right

    def __hash__(self) -> int:
        return hash(("FO_AND", self.left, self.right))


class FOOr(FOFormula):
    """First-order disjunction phi \\/ psi."""

    def __init__(self, left: FOFormula, right: FOFormula):
        if not isinstance(left, FOFormula) or not isinstance(right, FOFormula):
            raise TypeError("Operands must be FOFormula instances")
        self.left = left
        self.right = right

    def free_variables(self) -> Set[str]:
        return self.left.free_variables() | self.right.free_variables()

    def bound_variables(self) -> Set[str]:
        return self.left.bound_variables() | self.right.bound_variables()

    def complexity(self) -> int:
        return 1 + self.left.complexity() + self.right.complexity()

    def subformulas(self) -> Set[FOFormula]:
        return {self} | self.left.subformulas() | self.right.subformulas()

    def evaluate(self, model: KripkeModel, env: Dict[str, Any]) -> bool:
        return self.left.evaluate(model, env) or self.right.evaluate(model, env)

    def to_string(self, style: str = "standard") -> str:
        conn = " | " if style == "compact" else " \\/ "
        return f"({self.left.to_string(style)}{conn}{self.right.to_string(style)})"

    def to_latex(self) -> str:
        return rf"({self.left.to_latex()} \lor {self.right.to_latex()})"

    def __eq__(self, other: Any) -> bool:
        return isinstance(other, FOOr) and self.left == other.left and self.right == other.right

    def __hash__(self) -> int:
        return hash(("FO_OR", self.left, self.right))


class FOImplies(FOFormula):
    """First-order implication phi -> psi."""

    def __init__(self, left: FOFormula, right: FOFormula):
        if not isinstance(left, FOFormula) or not isinstance(right, FOFormula):
            raise TypeError("Operands must be FOFormula instances")
        self.left = left
        self.right = right

    def free_variables(self) -> Set[str]:
        return self.left.free_variables() | self.right.free_variables()

    def bound_variables(self) -> Set[str]:
        return self.left.bound_variables() | self.right.bound_variables()

    def complexity(self) -> int:
        return 1 + self.left.complexity() + self.right.complexity()

    def subformulas(self) -> Set[FOFormula]:
        return {self} | self.left.subformulas() | self.right.subformulas()

    def evaluate(self, model: KripkeModel, env: Dict[str, Any]) -> bool:
        return (not self.left.evaluate(model, env)) or self.right.evaluate(model, env)

    def to_string(self, style: str = "standard") -> str:
        conn = " implies " if style == "words" else " -> "
        return f"({self.left.to_string(style)}{conn}{self.right.to_string(style)})"

    def to_latex(self) -> str:
        return rf"({self.left.to_latex()} \to {self.right.to_latex()})"

    def __eq__(self, other: Any) -> bool:
        return isinstance(other, FOImplies) and self.left == other.left and self.right == other.right

    def __hash__(self) -> int:
        return hash(("FO_IMPL", self.left, self.right))


class FOIff(FOFormula):
    """First-order equivalence phi <-> psi."""

    def __init__(self, left: FOFormula, right: FOFormula):
        if not isinstance(left, FOFormula) or not isinstance(right, FOFormula):
            raise TypeError("Operands must be FOFormula instances")
        self.left = left
        self.right = right

    def free_variables(self) -> Set[str]:
        return self.left.free_variables() | self.right.free_variables()

    def bound_variables(self) -> Set[str]:
        return self.left.bound_variables() | self.right.bound_variables()

    def complexity(self) -> int:
        return 1 + self.left.complexity() + self.right.complexity()

    def subformulas(self) -> Set[FOFormula]:
        return {self} | self.left.subformulas() | self.right.subformulas()

    def evaluate(self, model: KripkeModel, env: Dict[str, Any]) -> bool:
        return self.left.evaluate(model, env) == self.right.evaluate(model, env)

    def to_string(self, style: str = "standard") -> str:
        conn = " iff " if style == "words" else " <-> "
        return f"({self.left.to_string(style)}{conn}{self.right.to_string(style)})"

    def to_latex(self) -> str:
        return rf"({self.left.to_latex()} \leftrightarrow {self.right.to_latex()})"

    def __eq__(self, other: Any) -> bool:
        return isinstance(other, FOIff) and self.left == other.left and self.right == other.right

    def __hash__(self) -> int:
        return hash(("FO_IFF", self.left, self.right))


class Forall(FOFormula):
    """Universal quantification: forall var. (body)."""

    def __init__(self, var: str, body: FOFormula):
        if not isinstance(var, str) or not var:
            raise ValueError("Bound variable must be non-empty string")
        if not isinstance(body, FOFormula):
            raise TypeError("body must be an FOFormula instance")
        self.var = var
        self.body = body

    def free_variables(self) -> Set[str]:
        return self.body.free_variables() - {self.var}

    def bound_variables(self) -> Set[str]:
        return self.body.bound_variables() | {self.var}

    def complexity(self) -> int:
        return 1 + self.body.complexity()

    def subformulas(self) -> Set[FOFormula]:
        return {self} | self.body.subformulas()

    def evaluate(self, model: KripkeModel, env: Dict[str, Any]) -> bool:
        for w in sorted(list(model.frame.worlds), key=lambda x: str(x)):
            new_env = dict(env)
            new_env[self.var] = w
            if not self.body.evaluate(model, new_env):
                return False
        return True

    def to_string(self, style: str = "standard") -> str:
        body_s = self.body.to_string(style)
        return f"forall {self.var}. {body_s}"

    def to_latex(self) -> str:
        return rf"\forall {self.var}. ({self.body.to_latex()})"

    def __eq__(self, other: Any) -> bool:
        return isinstance(other, Forall) and self.var == other.var and self.body == other.body

    def __hash__(self) -> int:
        return hash(("FORALL", self.var, self.body))


class Exists(FOFormula):
    """Existential quantification: exists var. (body)."""

    def __init__(self, var: str, body: FOFormula):
        if not isinstance(var, str) or not var:
            raise ValueError("Bound variable must be non-empty string")
        if not isinstance(body, FOFormula):
            raise TypeError("body must be an FOFormula instance")
        self.var = var
        self.body = body

    def free_variables(self) -> Set[str]:
        return self.body.free_variables() - {self.var}

    def bound_variables(self) -> Set[str]:
        return self.body.bound_variables() | {self.var}

    def complexity(self) -> int:
        return 1 + self.body.complexity()

    def subformulas(self) -> Set[FOFormula]:
        return {self} | self.body.subformulas()

    def evaluate(self, model: KripkeModel, env: Dict[str, Any]) -> bool:
        for w in sorted(list(model.frame.worlds), key=lambda x: str(x)):
            new_env = dict(env)
            new_env[self.var] = w
            if self.body.evaluate(model, new_env):
                return True
        return False

    def to_string(self, style: str = "standard") -> str:
        body_s = self.body.to_string(style)
        return f"exists {self.var}. {body_s}"

    def to_latex(self) -> str:
        return rf"\exists {self.var}. ({self.body.to_latex()})"

    def __eq__(self, other: Any) -> bool:
        return isinstance(other, Exists) and self.var == other.var and self.body == other.body

    def __hash__(self) -> int:
        return hash(("EXISTS", self.var, self.body))


def _alternate_var(curr: str, alt: Optional[str] = None) -> str:
    """Return the alternate variable name to preserve two-variable FO^2 embedding."""
    if alt is not None:
        return alt
    if curr == "x":
        return "y"
    if curr == "y":
        return "x"
    if curr == "w":
        return "u"
    if curr == "u":
        return "w"
    return "y"


def standard_translation(
    formula: Formula,
    var: str = "x",
    alt_var: Optional[str] = None,
    rel_name: str = "R",
) -> FOFormula:
    """Translate modal formula phi into first-order formula ST_x(phi) under van Benthem's translation.
    
    Uses two bound variables x and y alternating at modal quantifiers:
      - ST_x(p) = P(x)
      - ST_x(TOP) = TOP
      - ST_x(BOTTOM) = BOTTOM
      - ST_x(~phi) = ~ST_x(phi)
      - ST_x(phi /\\ psi) = ST_x(phi) /\\ ST_x(psi)
      - ST_x(phi \\/ psi) = ST_x(phi) \\/ ST_x(psi)
      - ST_x(phi -> psi) = ST_x(phi) -> ST_x(psi)
      - ST_x(phi <-> psi) = ST_x(phi) <-> ST_x(psi)
      - ST_x([]phi) = forall y. (R(x, y) -> ST_y(phi))
      - ST_x(<>phi) = exists y. (R(x, y) /\\ ST_y(phi))
    """
    if isinstance(formula, Atom):
        pred_name = formula.name.upper() if len(formula.name) == 1 else formula.name
        return Predicate(pred_name, var)

    if isinstance(formula, Top):
        return FOTop()

    if isinstance(formula, Bottom):
        return FOBottom()

    if isinstance(formula, Not):
        return FONot(standard_translation(formula.inner, var, alt_var, rel_name))

    if isinstance(formula, And):
        return FOAnd(
            standard_translation(formula.left, var, alt_var, rel_name),
            standard_translation(formula.right, var, alt_var, rel_name),
        )

    if isinstance(formula, Or):
        return FOOr(
            standard_translation(formula.left, var, alt_var, rel_name),
            standard_translation(formula.right, var, alt_var, rel_name),
        )

    if isinstance(formula, Implies):
        return FOImplies(
            standard_translation(formula.left, var, alt_var, rel_name),
            standard_translation(formula.right, var, alt_var, rel_name),
        )

    if isinstance(formula, Iff):
        return FOIff(
            standard_translation(formula.left, var, alt_var, rel_name),
            standard_translation(formula.right, var, alt_var, rel_name),
        )

    if isinstance(formula, Box):
        next_v = _alternate_var(var, alt_var)
        inner_tr = standard_translation(formula.inner, next_v, var, rel_name)
        guard = Relation(rel_name, var, next_v)
        return Forall(next_v, FOImplies(guard, inner_tr))

    if isinstance(formula, Dia):
        next_v = _alternate_var(var, alt_var)
        inner_tr = standard_translation(formula.inner, next_v, var, rel_name)
        guard = Relation(rel_name, var, next_v)
        return Exists(next_v, FOAnd(guard, inner_tr))

    raise TypeError(f"Unsupported formula AST node for standard translation: {type(formula)}")


# Canonical naming aliases
ST_x = standard_translation
st = standard_translation


def evaluate_fo(formula: FOFormula, model: KripkeModel, env: Optional[Dict[str, Any]] = None) -> bool:
    """Evaluate a first-order formula on a Kripke model under environment mapping."""
    return formula.evaluate(model, env or {})


# First-order canonical frame conditions
def fo_reflexive_condition(rel_name: str = "R", var: str = "x") -> FOFormula:
    """Canonical first-order condition for reflexivity: forall x. R(x, x)."""
    return Forall(var, Relation(rel_name, var, var))


def fo_symmetric_condition(rel_name: str = "R", x: str = "x", y: str = "y") -> FOFormula:
    """Canonical first-order condition for symmetry: forall x, y. (R(x, y) -> R(y, x))."""
    return Forall(x, Forall(y, FOImplies(Relation(rel_name, x, y), Relation(rel_name, y, x))))


def fo_transitive_condition(rel_name: str = "R", x: str = "x", y: str = "y", z: str = "z") -> FOFormula:
    """Canonical first-order condition for transitivity: forall x, y, z. ((R(x, y) /\\ R(y, z)) -> R(x, z))."""
    ante = FOAnd(Relation(rel_name, x, y), Relation(rel_name, y, z))
    cons = Relation(rel_name, x, z)
    return Forall(x, Forall(y, Forall(z, FOImplies(ante, cons))))


def fo_euclidean_condition(rel_name: str = "R", x: str = "x", y: str = "y", z: str = "z") -> FOFormula:
    """Canonical first-order condition for euclideanness: forall x, y, z. ((R(x, y) /\\ R(x, z)) -> R(y, z))."""
    ante = FOAnd(Relation(rel_name, x, y), Relation(rel_name, x, z))
    cons = Relation(rel_name, y, z)
    return Forall(x, Forall(y, Forall(z, FOImplies(ante, cons))))


def fo_serial_condition(rel_name: str = "R", x: str = "x", y: str = "y") -> FOFormula:
    """Canonical first-order condition for seriality: forall x exists y. R(x, y)."""
    return Forall(x, Exists(y, Relation(rel_name, x, y)))


def fo_functional_condition(rel_name: str = "R", x: str = "x", y: str = "y", z: str = "z") -> FOFormula:
    """Canonical first-order condition for functionality (partial functionality / at most one successor):
    forall x, y, z. ((R(x, y) /\\ R(x, z)) -> y = z).
    """
    ante = FOAnd(Relation(rel_name, x, y), Relation(rel_name, x, z))
    cons = Equality(y, z)
    return Forall(x, Forall(y, Forall(z, FOImplies(ante, cons))))


def fo_confluent_condition(rel_name: str = "R", x: str = "x", y: str = "y", z: str = "z", u: str = "u") -> FOFormula:
    """Canonical first-order condition for confluence (Church-Rosser):
    forall x, y, z. ((R(x, y) /\\ R(x, z)) -> exists u. (R(y, u) /\\ R(z, u))).
    """
    ante = FOAnd(Relation(rel_name, x, y), Relation(rel_name, x, z))
    cons = Exists(u, FOAnd(Relation(rel_name, y, u), Relation(rel_name, z, u)))
    return Forall(x, Forall(y, Forall(z, FOImplies(ante, cons))))
