# Basic Modal Logic Example

This example demonstrates the core concepts of modal logic, including necessity and possibility operators, Kripke semantics, and theorem checking.

## Theoretical Overview

Modal propositional logic extends classical propositional logic with two dual modal operators:
- **Necessity Operator ([] or Box)**: Represents that a proposition is true in all accessible possible worlds.
- **Possibility Operator (<> or Dia)**: Represents that a proposition is true in at least one accessible possible world.
- **Duality**: `<>phi` is logically equivalent to `~[]~phi`, and `[]phi` is equivalent to `~<>~phi`.

## Formal Representation in ModalLogic

Formulas can be parsed directly from standard strings:

```python
from modallogic.syntax import parse_formula

# Necessity statement
f1 = parse_formula("[]p")

# Distribution axiom K
k_axiom = parse_formula("[](p -> q) -> ([]p -> []q)")

# Reflexivity axiom T
t_axiom = parse_formula("[]p -> p")
```

## Relational Evaluation on Kripke Models

A Kripke model consists of a tuple `M = (W, R, V)`:
- `W`: Set of possible worlds.
- `R`: Binary accessibility relation on `W`.
- `V`: Valuation assigning propositional variables to subsets of `W`.

```python
from modallogic.semantics import KripkeFrame, KripkeModel

# Frame with two worlds where w0 accesses w1
frame = KripkeFrame(worlds=["w0", "w1"], relation=[("w0", "w1")])

# Valuation: p is true at w1
model = KripkeModel(frame, valuation={"p": ["w1"]})

# w0 can only see w1, and p holds at w1, hence []p is True at w0
print(model.satisfies("w0", parse_formula("[]p")))  # True

# But p does not hold at w0, so []p -> p is False at w0
print(model.satisfies("w0", parse_formula("[]p -> p")))  # False
```

## Automated Theorem Proving with Semantic Tableaux

To verify whether a formula is valid in a given modal system or extract an explicit countermodel:

```python
from modallogic.tableau import TableauSolver

solver_k = TableauSolver(system="K")
res = solver_k.check_validity(parse_formula("[](p -> q) -> ([]p -> []q)"))
print(f"Valid in K: {res.is_valid}")  # True

# Axiom T is invalid in K, but valid in T
print(f"Axiom T valid in K: {solver_k.check_validity(parse_formula('[]p -> p')).is_valid}")  # False

solver_t = TableauSolver(system="T")
print(f"Axiom T valid in T: {solver_t.check_validity(parse_formula('[]p -> p')).is_valid}")  # True
```

## Interactive Executable Demos

Run the following scripts in `examples/`:
- `python3 examples/kripke_frame_verification.py`: Frame condition validation.
- `python3 examples/bisimulation_demo.py`: Maximal bisimulation calculation and quotient models.
- `python3 examples/tableau_prover_demo.py`: Automated modal tableau prover and countermodel extraction.
