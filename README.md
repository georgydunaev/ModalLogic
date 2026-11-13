# ModalLogic

ModalLogic is a rigorous Python library and verification suite for propositional modal logics, relational Kripke semantics, correspondence theory, bisimulations, and automated semantic tableau theorem proving.

## Features

- **Formal Syntax AST & Parser**: Full recursive descent parser supporting standard notation (`[]`, `<>`, `~`, `&`, `|`, `->`, `<->`, `TOP`, `BOTTOM`) with precedence handling, AST manipulation, and Negation Normal Form (NNF) transformation.
- **Relational Kripke Semantics**: Representation of Kripke frames `(W, R)` and models `(W, R, V)` with truth evaluation, truth set computation, and model checking.
- **Frame Property Verification**: Sound checking of reflexivity, irreflexivity, transitivity, symmetry, antisymmetry, seriality, euclideanness, confluence (Church-Rosser), and converse well-foundedness (Gödel-Löb / GL frames).
- **Frame Closures**: Reflexive, transitive, symmetric, and equivalence closures.
- **Modal Axiom Suite**: Standard canonical axioms (K, T, 4, B, D, 5, GL, Grz, C4, CD) and modal systems (K, KD, T, KB, K4, K45, KD45, S4, S5, GL).
- **Finite Frame Validity & Countermodel Extraction**: Exhaustive valuation enumeration for finite frames to check validity or extract concrete refutations.
- **Bisimulation Engine**: Verification of bisimulations, maximal bisimulation calculation via greatest fixed-point relational refinement, quotient model construction, and Hennessy-Milner modal invariance verification.
- **Automated Semantic Tableau Solver**: Decision procedure for modal logics K, T, S4, and S5 with automated branch saturation, clash detection, and finite countermodel extraction from open branches.

## Directory Structure

```text
ModalLogic/
├── DOCS.md                    Technical documentation and theorem reference
├── README.md                  Project overview and quickstart
├── modallogic/                Core Python library
│   ├── __init__.py            Public API exports
│   ├── syntax.py              Formula AST, recursive descent parser, NNF
│   ├── semantics.py           Kripke frames, models, frame properties, closures
│   ├── axioms.py              Modal axioms, systems, and correspondence
│   ├── bisimulation.py        Bisimulation checker, fixed point, quotients
│   └── tableau.py             Labeled tableau decision procedure
├── examples/                  Self-contained runnable demonstrations
│   ├── basic_modal_logic_example.md
│   ├── kripke_frame_verification.py
│   ├── bisimulation_demo.py
│   └── tableau_prover_demo.py
├── tests/                     Unit test suite
│   ├── test_modal_logic.py    Legacy and regression tests
│   ├── test_syntax.py         Syntax, parser, AST tests
│   ├── test_semantics.py      Kripke semantics and frame properties
│   ├── test_axioms.py         Axiom schemas and correspondence
│   ├── test_bisimulation.py   Bisimulations and modal invariance
│   └── test_tableau.py        Tableau prover and countermodel extraction
└── tickets/                   Task tracking tickets
```

## Quick Start

### Parsing and Evaluating Formulas

```python
from modallogic.syntax import parse_formula
from modallogic.semantics import KripkeFrame, KripkeModel

# Parse a modal formula
phi = parse_formula("[]p -> p")

# Construct a Kripke frame with two worlds
frame = KripkeFrame(worlds=["w0", "w1"], relation=[("w0", "w1")])

# Define valuation
model = KripkeModel(frame, valuation={"p": ["w1"]})

# Evaluate truth at world w0
print(model.satisfies("w0", phi))  # False: []p holds but p does not hold at w0
```

### Automated Tableau Theorem Proving

```python
from modallogic.syntax import parse_formula
from modallogic.tableau import TableauSolver

solver_k = TableauSolver(system="K")
res_k = solver_k.check_validity(parse_formula("[](p -> q) -> ([]p -> []q)"))
print(res_k.is_valid)  # True

# Axiom T fails in K, but succeeds in T
res_t_in_k = solver_k.check_validity(parse_formula("[]p -> p"))
print(res_t_in_k.is_valid)  # False: countermodel extracted

solver_t = TableauSolver(system="T")
res_t = solver_t.check_validity(parse_formula("[]p -> p"))
print(res_t.is_valid)  # True
```

## Running the Test Suite

Run all unit tests:
```bash
python3 -m unittest discover -s tests -p 'test_*.py'
```

## License

This project is licensed under the MIT License.
