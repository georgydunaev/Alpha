# Project Overview: Alpha-Equivalence, Explicit Shifts, and Confluence (`Alpha`)

## Purpose and Mathematical Foundations

`Alpha` is a formal verification and executable logic engine project exploring the untyped lambda calculus equipped with explicit scope shift operators (`shft`), variable actions (`varp` and `subs`), measure-based well-founded recursion (`lenf + lent`), capture-avoiding substitution, parallel beta-reduction, and the Church-Rosser confluence theorem.

## Repository Architecture

### 1. Coq / Rocq Formalizations
- [00.v](file:///botworkspace/Alpha/00.v): Original 2018 Coq development by Georgy Dunaev introducing inductive `term` (`atom`, `appl`, `lamb`, `shft`), action `func` (`varp`, `subs`), recursive action `act` with measure `lenf f + lent t`, and inductive alpha-equivalence `alp`.
- [alpha_core.v](file:///botworkspace/Alpha/alpha_core.v): Coq 8.20+ modernized theory with decomposed measure obligations (`act_measure_lamb_subs`, `act_measure_appl_l`, `act_measure_appl_r`, `act_measure_shft_subs`), variable action identity (`act_varp_id`), and shift involution (`act_subs_shft`).
- [alpha_subst.v](file:///botworkspace/Alpha/alpha_subst.v): Formalization of free variable sets (`fv`), freshness predicates (`fresh`), capture-avoiding substitution (`subst`), alpha-equivalence reflexivity/symmetry/transitivity (`alpha_equiv`), and single-step/multi-step beta-reduction (`beta_step`, `beta_star`).
- [alpha_confluence.v](file:///botworkspace/Alpha/alpha_confluence.v): Tait-Martin-Lof parallel beta-reduction (`par_beta`), complete development (`complete_dev`), the strip lemma (`par_beta_strip`), the diamond property (`par_beta_diamond`), and the Church-Rosser confluence theorem (`church_rosser`).

### 2. Executable Python Logic Engine (`alpha_engine/`)
- [alpha_engine/terms.py](file:///botworkspace/Alpha/alpha_engine/terms.py): AST data structures (`Term`, `Atom`, `Appl`, `Lamb`, `Shft`, `Func`, `Varp`, `Subs`), termination metrics (`lent`, `lenf`), recursive action (`act`), De Bruijn canonicalization (`to_canonical`), and DAG term representation (`TermGraph`).
- [alpha_engine/substitution.py](file:///botworkspace/Alpha/alpha_engine/substitution.py): Free variable computation (`fv`), deterministic fresh variable generation (`fresh`), capture-avoiding substitution (`subst`), and leftmost-outermost beta-reduction (`beta_step`, `beta_reduce`).
- [alpha_engine/reduction.py](file:///botworkspace/Alpha/alpha_engine/reduction.py): Parallel beta-reduction (`parallel_reduce_step`, `all_parallel_reducts`), diamond property verifier (`check_par_beta_diamond`), eta-reduction (`eta_step`, `eta_reduce`), beta-eta normalization (`beta_eta_reduce`), and Church-Rosser confluence verifier (`check_church_rosser`).
- [alpha_engine/syntax_verifier.py](file:///botworkspace/Alpha/alpha_engine/syntax_verifier.py): Coq script structural verifier ensuring zero `Admitted` or `Abort` commands across all `.v` files.

### 3. Documentation and Verification Suite
- [README.md](file:///botworkspace/Alpha/README.md) and [DOCS.md](file:///botworkspace/Alpha/DOCS.md): Architectural specification, formal grammar, and theorem catalog.
- [tests/test_alpha.py](file:///botworkspace/Alpha/tests/test_alpha.py), [tests/test_substitution.py](file:///botworkspace/Alpha/tests/test_substitution.py), and [tests/test_confluence.py](file:///botworkspace/Alpha/tests/test_confluence.py): Unit tests validating the Coq proof scripts, measure invariants, capture-avoiding substitution, and Church-Rosser confluence.

## Verification Command

```bash
python3 -m unittest discover -s /botworkspace/Alpha/tests -p "test_*.py"
```
