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
]
