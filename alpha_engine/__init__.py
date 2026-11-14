"""
Alpha Logic Engine: Formal Lambda Calculus with Explicit Shifts, Actions, and Alpha-Equivalence.
"""

from .terms import (
    Term,
    Atom,
    Appl,
    Lamb,
    Shft,
    Func,
    Varp,
    Subs,
    lent,
    lenf,
    act,
    free_vars,
    all_vars,
    to_canonical,
    is_alpha_equivalent,
    TermGraph,
)

from .substitution import (
    fv,
    fresh,
    rename,
    subst,
    alpha_equiv,
    beta_step,
    beta_reduce,
)

__all__ = [
    "Term",
    "Atom",
    "Appl",
    "Lamb",
    "Shft",
    "Func",
    "Varp",
    "Subs",
    "lent",
    "lenf",
    "act",
    "free_vars",
    "all_vars",
    "to_canonical",
    "is_alpha_equivalent",
    "TermGraph",
    "fv",
    "fresh",
    "rename",
    "subst",
    "alpha_equiv",
    "beta_step",
    "beta_reduce",
]
