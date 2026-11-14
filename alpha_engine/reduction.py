"""
Church-Rosser Confluence, Parallel Beta Reduction, and Beta-Eta Normalization for Alpha.
Implements Takahashi complete development, Tait-Martin-Loef parallel reduction,
diamond property verification, eta reduction, and unique normal forms matching alpha_confluence.v.
"""

from __future__ import annotations
from typing import Any, List, Optional, Set, Tuple

from alpha_engine.terms import (
    Term,
    Atom,
    Appl,
    Lamb,
    Shft,
    free_vars,
    all_vars,
    fresh_var,
    is_alpha_equivalent,
)
from alpha_engine.substitution import (
    fv,
    fresh,
    rename,
    subst,
    alpha_equiv,
    beta_step,
    beta_reduce,
)


def parallel_reduce_step(t: Term) -> Term:
    """
    Computes Takahashi complete development of term t (denoted t^*).
    Simultaneously contracts all available beta-redexes in t in a single parallel step.
    Corresponds to Coq Fixpoint cd in alpha_confluence.v.
    """
    if isinstance(t, Atom):
        return Atom(t.var)

    elif isinstance(t, Appl):
        # If this is a beta-redex, contract it after recursively reducing components
        if isinstance(t.left, Lamb):
            var = t.left.var
            reduced_body = parallel_reduce_step(t.left.body)
            reduced_arg = parallel_reduce_step(t.right)
            return subst(var, reduced_arg, reduced_body)
        else:
            return Appl(parallel_reduce_step(t.left), parallel_reduce_step(t.right))

    elif isinstance(t, Lamb):
        return Lamb(t.var, parallel_reduce_step(t.body))

    elif isinstance(t, Shft):
        return Shft(parallel_reduce_step(t.term))

    else:
        raise TypeError(f"Unknown term type: {type(t)}")


def all_parallel_reducts(t: Term) -> List[Term]:
    """
    Enumerates all possible terms reachable from t in one parallel reduction step.
    Allows contracting any subset of disjoint beta-redexes (including none, all, or partial).
    Corresponds to inductive relation par_beta in alpha_confluence.v.
    """
    if isinstance(t, Atom):
        return [Atom(t.var)]

    elif isinstance(t, Lamb):
        body_reducts = all_parallel_reducts(t.body)
        return [Lamb(t.var, b) for b in body_reducts]

    elif isinstance(t, Shft):
        term_reducts = all_parallel_reducts(t.term)
        return [Shft(s) for s in term_reducts]

    elif isinstance(t, Appl):
        left_reducts = all_parallel_reducts(t.left)
        right_reducts = all_parallel_reducts(t.right)

        results: List[Term] = []

        # Structural application rule: pbeta_appl
        for l in left_reducts:
            for r in right_reducts:
                results.append(Appl(l, r))

        # Beta redex contraction rule: pbeta_beta
        if isinstance(t.left, Lamb):
            var = t.left.var
            body_reducts = all_parallel_reducts(t.left.body)
            for b in body_reducts:
                for r in right_reducts:
                    results.append(subst(var, r, b))

        # Deduplicate modulo alpha-equivalence
        unique: List[Term] = []
        for cand in results:
            if not any(alpha_equiv(cand, u) for u in unique):
                unique.append(cand)
        return unique

    else:
        raise TypeError(f"Unknown term type: {type(t)}")


def is_par_beta(M: Term, N: Term) -> bool:
    """
    Checks if N is reachable from M in a single parallel beta reduction step.
    Corresponds to Prop par_beta M N in alpha_confluence.v.
    """
    reducts = all_parallel_reducts(M)
    return any(alpha_equiv(N, r) for r in reducts)


def check_par_beta_diamond(
    M: Term,
) -> Tuple[bool, Term, List[Tuple[Term, Term, Optional[Term]]]]:
    """
    Validates the diamond property for parallel reduction on term M.
    For all pairs of parallel reducts (M1, M2), checks that there exists a common join M'
    such that par_beta M1 M' and par_beta M2 M'.
    By Takahashi's triangle lemma, Takahashi complete development M^* serves as
    the canonical common join.
    Returns (all_joined, cd_M, join_witnesses).
    """
    reducts = all_parallel_reducts(M)
    cd_M = parallel_reduce_step(M)

    # First verify Takahashi triangle property: for all M_i in reducts, par_beta M_i cd_M
    for r in reducts:
        if not is_par_beta(r, cd_M):
            return False, cd_M, []

    # Verify diamond joinability for all pairs (M1, M2)
    witnesses: List[Tuple[Term, Term, Optional[Term]]] = []
    all_joined = True

    for i, M1 in enumerate(reducts):
        for j in range(i, len(reducts)):
            M2 = reducts[j]
            # cd_M is known to join M1 and M2
            witnesses.append((M1, M2, cd_M))

    return all_joined, cd_M, witnesses


def parallel_reduce(t: Term, max_steps: int = 100) -> Tuple[Term, int]:
    """
    Iteratively evaluates Takahashi parallel reduction steps until normal form or step limit.
    Returns (normal_form_term, steps_taken).
    """
    curr = t
    steps = 0
    while steps < max_steps:
        next_t = parallel_reduce_step(curr)
        if alpha_equiv(curr, next_t):
            break
        curr = next_t
        steps += 1
    return curr, steps


def eta_step(t: Term) -> Tuple[bool, Term]:
    """
    Performs one step of standard eta-reduction (leftmost-outermost).
    Contracts (lambda x. M x) to M when x is not free in M.
    Corresponds to Coq Inductive eta_step in alpha_confluence.v.
    Returns (True, reduced_term) if an eta-redex was reduced, or (False, t) if none.
    """
    if isinstance(t, Lamb):
        x = t.var
        body = t.body

        # Check for eta-redex: (lambda x. M x) with fresh x M
        if isinstance(body, Appl) and isinstance(body.right, Atom):
            if body.right.var == x and fresh(x, body.left):
                return True, body.left

        # Try reducing inside lambda body
        has_reduced, new_body = eta_step(body)
        if has_reduced:
            return True, Lamb(x, new_body)

        return False, t

    elif isinstance(t, Appl):
        has_reduced, new_left = eta_step(t.left)
        if has_reduced:
            return True, Appl(new_left, t.right)

        has_reduced, new_right = eta_step(t.right)
        if has_reduced:
            return True, Appl(t.left, new_right)

        return False, t

    elif isinstance(t, Shft):
        has_reduced, new_term = eta_step(t.term)
        if has_reduced:
            return True, Shft(new_term)
        return False, t

    elif isinstance(t, Atom):
        return False, t

    else:
        raise TypeError(f"Unknown term type: {type(t)}")


def eta_reduce(t: Term, max_steps: int = 100) -> Tuple[Term, int]:
    """
    Iteratively evaluates eta-reduction steps until eta-normal form or step limit.
    Returns (eta_normal_form, steps_taken).
    """
    curr = t
    steps = 0
    while steps < max_steps:
        has_reduced, next_t = eta_step(curr)
        if not has_reduced:
            break
        curr = next_t
        steps += 1
    return curr, steps


def beta_eta_step(t: Term) -> Tuple[bool, Term]:
    """
    Performs one step of combined beta-eta reduction (leftmost-outermost).
    Prefers beta-reduction; falls back to eta-reduction if no beta-redex is active.
    Corresponds to Coq Inductive beta_eta_step in alpha_confluence.v.
    """
    has_beta, next_beta = beta_step(t)
    if has_beta:
        return True, next_beta

    has_eta, next_eta = eta_step(t)
    if has_eta:
        return True, next_eta

    return False, t


def beta_eta_reduce(t: Term, max_steps: int = 100) -> Tuple[Term, int]:
    """
    Iteratively evaluates combined beta-eta reduction steps until beta-eta normal form.
    Returns (beta_eta_normal_form, steps_taken).
    """
    curr = t
    steps = 0
    while steps < max_steps:
        has_reduced, next_t = beta_eta_step(curr)
        if not has_reduced:
            break
        curr = next_t
        steps += 1
    return curr, steps


def is_beta_normal(t: Term) -> bool:
    """
    Returns True if term t is in beta-normal form (contains no beta-redexes).
    """
    return not beta_step(t)[0]


def is_eta_normal(t: Term) -> bool:
    """
    Returns True if term t is in eta-normal form (contains no eta-redexes).
    """
    return not eta_step(t)[0]


def is_beta_eta_normal(t: Term) -> bool:
    """
    Returns True if term t is in both beta and eta normal form.
    """
    return is_beta_normal(t) and is_eta_normal(t)


def check_church_rosser(
    M: Term,
) -> Tuple[bool, Term, Term, Optional[Term]]:
    """
    Validates Church-Rosser confluence for term M:
    Reduces M along standard leftmost-outermost beta reduction and Takahashi parallel reduction,
    verifying that both paths converge to alpha-equivalent normal forms.
    Returns (is_confluent, beta_nf, par_nf, common_nf).
    """
    beta_nf, _ = beta_reduce(M)
    par_nf, _ = parallel_reduce(M)

    is_confluent = alpha_equiv(beta_nf, par_nf)
    common_nf = beta_nf if is_confluent else None
    return is_confluent, beta_nf, par_nf, common_nf
