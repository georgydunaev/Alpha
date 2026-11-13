# [ALPHA] Ticket 7425 — Alpha: Standardize Term Naming Conventions and Type Annotations

**Repository:** `Alpha`  
**Status:** `RESOLVED`  
**Created:** `2026-10-27T22:48:44Z`  
**Resolved:** `2026-11-13T23:25:00Z`  

## Task Description
Ensure consistent identifier naming across theory files and make implicit type annotations explicit for maintainability.

## Execution Guidelines
1. Work autonomously in `Alpha/`.
2. Ensure existing tests continue to pass.
3. For math and foundations repos, keep modifications cosmetic, clean, and adhere to sound formal reasoning.
4. Run tests with local test runner before concluding.

## Resolution Summary
1. Standardized variable and term naming conventions across `alpha_core.v`:
   - Variable identifiers: `x`, `y`, `v : var`.
   - Term identifiers: `M`, `N`, `M1`, `M2`, `M3 : term`.
   - Action function identifiers: `f`, `F : func`.
2. Made all implicit type annotations explicit across all definitions, hypotheses, inductive constructors, lemmas, and theorems:
   - Hypotheses: `Hypothesis deq_spec : forall (x : var) (y : var), deq x y = true <-> x = y`.
   - Measure lemmas: Every quantifier explicitly annotated with `(x : var)`, `(M : term)`, `(N : term)`, `(f : func)`, or `(F : func)`.
   - Inductive relation `alp`: All constructors explicitly type-annotated (`(M : term)`, `(M1 : term)`, `(M2 : term)`, `(x : var)`, etc.).
   - Congruence and equivalence theorems: Standardized explicit binder typing across all proofs.
3. Standardized Python type annotations in `alpha_engine/terms.py`:
   - Explicit `-> None` return type annotations on all constructor initializers.
   - Explicit type declarations on class instance attributes.
   - Tuple return types annotated as `Tuple[Any, ...]`.
4. Extended `CoqVerifier` in `alpha_engine/syntax_verifier.py`:
   - Added `check_explicit_type_annotations` method to ensure all `forall` quantifiers in lemmas and theorems possess explicit type signatures.
   - Added `find_lemmas` method for structured verification of theory definitions.
5. Added automated validation in `tests/test_alpha.py` verifying full explicit type annotation compliance and clean Coq compilation via `coqc`.
