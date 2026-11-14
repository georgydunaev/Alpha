"""
Capture-Avoiding Substitution, Freshness Relations, and Beta-Reduction for Alpha.
Implements capture-avoiding nominal substitution matching alpha_subst.v.
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


def fv(t: Term) -> List[Any]:
    """
    Computes ordered list of free variables in term t.
    Corresponds to Coq Fixpoint fv in alpha_subst.v.
    """
    if isinstance(t, Atom):
        return [t.var]
    elif isinstance(t, Appl):
        res: List[Any] = []
        for v in fv(t.left):
            if v not in res:
                res.append(v)
        for v in fv(t.right):
            if v not in res:
                res.append(v)
        return res
    elif isinstance(t, Lamb):
        return [v for v in fv(t.body) if v != t.var]
    elif isinstance(t, Shft):
        return fv(t.term)
    else:
        raise TypeError(f"Unknown term type: {type(t)}")


def fresh(x: Any, t: Term) -> bool:
    """
    Freshness predicate: returns True if x does not occur free in t.
    Corresponds to Coq Definition fresh in alpha_subst.v.
    """
    return x not in fv(t)


def rename(y: Any, z: Any, t: Term) -> Term:
    """
    Renames free occurrences of variable y to z in term t.
    Corresponds to Coq Fixpoint rename in alpha_subst.v.
    """
    if isinstance(t, Atom):
        return Atom(z) if t.var == y else Atom(t.var)
    elif isinstance(t, Appl):
        return Appl(rename(y, z, t.left), rename(y, z, t.right))
    elif isinstance(t, Lamb):
        if t.var == y:
            # Bound variable y shadows target y
            return Lamb(t.var, t.body)
        else:
            return Lamb(t.var, rename(y, z, t.body))
    elif isinstance(t, Shft):
        return Shft(rename(y, z, t.term))
    else:
        raise TypeError(f"Unknown term type: {type(t)}")


def subst(x: Any, N: Term, M: Term) -> Term:
    """
    Capture-avoiding substitution: substitutes term N for free occurrences of variable x in term M.
    When a lambda binder would capture a free variable of N, automatically generates
    a fresh variable and renames the bound variable prior to substitution.
    Corresponds to Coq subst in alpha_subst.v.
    """
    if isinstance(M, Atom):
        return N if M.var == x else Atom(M.var)

    elif isinstance(M, Appl):
        return Appl(subst(x, N, M.left), subst(x, N, M.right))

    elif isinstance(M, Shft):
        return Shft(subst(x, N, M.term))

    elif isinstance(M, Lamb):
        y = M.var
        if y == x:
            # Variable x is shadowed by binder y; no substitution in body
            return Lamb(y, M.body)

        # y != x
        if not (x in fv(M.body)):
            # x does not occur free in body; no substitution needed
            return Lamb(y, M.body)

        fv_N = set(fv(N))
        if y not in fv_N:
            # Safe: binder y does not occur free in N
            return Lamb(y, subst(x, N, M.body))
        else:
            # Capture hazard: binder y occurs free in N!
            # Generate fresh variable z not in all_vars(M.body) U fv_N U {x, y}
            used = set(all_vars(M.body)) | fv_N | {x, y}
            z = fresh_var(used, base=str(y))
            renamed_body = rename(y, z, M.body)
            return Lamb(z, subst(x, N, renamed_body))

    else:
        raise TypeError(f"Unknown term type: {type(M)}")


def alpha_equiv(M1: Term, M2: Term) -> bool:
    """
    Checks alpha-equivalence (alp) between two terms.
    Corresponds to inductive alp relation in alpha_core.v and alpha_subst.v.
    """
    return is_alpha_equivalent(M1, M2)


def beta_step(t: Term) -> Tuple[bool, Term]:
    """
    Performs one step of standard beta-reduction (leftmost-outermost).
    Returns (True, reduced_term) if a redex was reduced, or (False, t) if in normal form.
    """
    if isinstance(t, Appl):
        # Check if this application is a beta-redex: ((\x. body) arg)
        if isinstance(t.left, Lamb):
            var = t.left.var
            body = t.left.body
            arg = t.right
            reduced = subst(var, arg, body)
            return True, reduced

        # Try reducing function position first
        has_reduced, new_left = beta_step(t.left)
        if has_reduced:
            return True, Appl(new_left, t.right)

        # Try reducing argument position
        has_reduced, new_right = beta_step(t.right)
        if has_reduced:
            return True, Appl(t.left, new_right)

        return False, t

    elif isinstance(t, Lamb):
        has_reduced, new_body = beta_step(t.body)
        if has_reduced:
            return True, Lamb(t.var, new_body)
        return False, t

    elif isinstance(t, Shft):
        has_reduced, new_term = beta_step(t.term)
        if has_reduced:
            return True, Shft(new_term)
        return False, t

    elif isinstance(t, Atom):
        return False, t

    else:
        raise TypeError(f"Unknown term type: {type(t)}")


def beta_reduce(t: Term, max_steps: int = 100) -> Tuple[Term, int]:
    """
    Iteratively evaluates beta-reduction steps until normal form or step limit.
    Returns (normal_form_term, steps_taken).
    """
    curr = t
    steps = 0
    while steps < max_steps:
        has_reduced, next_t = beta_step(curr)
        if not has_reduced:
            break
        curr = next_t
        steps += 1
    return curr, steps
