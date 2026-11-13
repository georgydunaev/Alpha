# Alpha — Foundational Coq Proof Script and Logic Engine

## Overview
`Alpha` contains foundational formal developments exploring lambda calculus with explicit shift operators, variable actions, well-founded termination metrics, and inductive alpha-equivalence.

- Original proof script: [`00.v`](file:///botworkspace/Alpha/00.v) (Georgy Dunaev, 2018).
- Modernized Coq 8.20+ / Rocq formalization: [`alpha_core.v`](file:///botworkspace/Alpha/alpha_core.v).
- Executable Python Logic Engine: [`alpha_engine/`](file:///botworkspace/Alpha/alpha_engine/).
- Architectural & Mathematical Documentation: [`DOCS.md`](file:///botworkspace/Alpha/DOCS.md).

## Key Components

1. **Syntax (`term`)**:
   - `atom(v)`: Variable atoms.
   - `appl(M, N)`: Function application.
   - `lamb(x, M)`: Binder abstractions.
   - `shft(M)`: Explicit scope shift.

2. **Actions (`func`)**:
   - `varp(y, x)`: Variable replacement/renaming.
   - `subs(F, x)`: Scope-protecting substitution.

3. **Termination Guarantee (`lenf + lent`)**:
   - Recursion over `act` is proven well-founded via custom measure metric `lenf(f) + lent(t)`.
   - All 5 obligations are proved mechanically in `alpha_core.v` through decomposed, reusable modular lemmas using `lia`.
   - Explicit type annotations are standardized across all theory definitions, lemmas, and inductive constructors.

4. **Alpha-Equivalence (`alp`)**:
   - Inductive relation covering reflexivity, symmetry, transitivity, congruence rules, and axiom `axi`.
   - Verified executable normalization in `alpha_engine.terms.is_alpha_equivalent`.

## Running Verification Tests

```bash
python3 -m unittest discover -s tests -p "test_*.py" -v
```
