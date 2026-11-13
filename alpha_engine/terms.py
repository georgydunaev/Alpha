"""
Core Term Structure, Action Function, and Alpha-Equivalence Logic Engine for Alpha.
Directly models the formal definitions in 00.v and alpha_core.v.
"""

from __future__ import annotations
from typing import Any, Callable, Dict, List, Optional, Set, Tuple


class Term:
    """Abstract base class for all Alpha terms."""

    def __repr__(self) -> str:
        return self.to_string()

    def to_string(self) -> str:
        raise NotImplementedError


class Atom(Term):
    """Atomic variable term."""

    def __init__(self, var: Any) -> None:
        self.var: Any = var

    def to_string(self) -> str:
        return str(self.var)

    def __eq__(self, other: object) -> bool:
        return isinstance(other, Atom) and self.var == other.var

    def __hash__(self) -> int:
        return hash(("atom", self.var))


class Appl(Term):
    """Application term: (M N)."""

    def __init__(self, left: Term, right: Term) -> None:
        self.left: Term = left
        self.right: Term = right

    def to_string(self) -> str:
        return f"({self.left.to_string()} {self.right.to_string()})"

    def __eq__(self, other: object) -> bool:
        return (
            isinstance(other, Appl)
            and self.left == other.left
            and self.right == other.right
        )

    def __hash__(self) -> int:
        return hash(("appl", self.left, self.right))


class Lamb(Term):
    """Lambda abstraction term: (lamb x M)."""

    def __init__(self, var: Any, body: Term) -> None:
        self.var: Any = var
        self.body: Term = body

    def to_string(self) -> str:
        return f"(\\ {self.var} . {self.body.to_string()})"

    def __eq__(self, other: object) -> bool:
        return (
            isinstance(other, Lamb)
            and self.var == other.var
            and self.body == other.body
        )

    def __hash__(self) -> int:
        return hash(("lamb", self.var, self.body))


class Shft(Term):
    """Explicit shift operator on terms: (shft M)."""

    def __init__(self, term: Term) -> None:
        self.term: Term = term

    def to_string(self) -> str:
        return f"^( {self.term.to_string()} )"

    def __eq__(self, other: object) -> bool:
        return isinstance(other, Shft) and self.term == other.term

    def __hash__(self) -> int:
        return hash(("shft", self.term))


class Func:
    """Abstract base class for substitution / action functions."""

    def to_string(self) -> str:
        raise NotImplementedError

    def __repr__(self) -> str:
        return self.to_string()


class Varp(Func):
    """Variable permutation / renaming: varp y x means rename x to y."""

    def __init__(self, y: Any, x: Any) -> None:
        self.y: Any = y
        self.x: Any = x

    def to_string(self) -> str:
        return f"[{self.y}/{self.x}]"

    def __eq__(self, other: object) -> bool:
        return isinstance(other, Varp) and self.y == other.y and self.x == other.x

    def __hash__(self) -> int:
        return hash(("varp", self.y, self.x))


class Subs(Func):
    """Scope abstraction: subs F x protects bound variable x."""

    def __init__(self, func: Func, x: Any) -> None:
        self.func: Func = func
        self.x: Any = x

    def to_string(self) -> str:
        return f"({self.func.to_string()})_{self.x}"

    def __eq__(self, other: object) -> bool:
        return isinstance(other, Subs) and self.func == other.func and self.x == other.x

    def __hash__(self) -> int:
        return hash(("subs", self.func, self.x))


def lent(t: Term) -> int:
    """
    Term measure matching Coq Fixpoint lent in 00.v:
    atom x => 0
    appl M N => max(lent M, lent N) + 1
    lamb x M => lent M + 2
    shft M => lent M + 1
    """
    if isinstance(t, Atom):
        return 0
    elif isinstance(t, Appl):
        return max(lent(t.left), lent(t.right)) + 1
    elif isinstance(t, Lamb):
        return lent(t.body) + 2
    elif isinstance(t, Shft):
        return lent(t.term) + 1
    else:
        raise TypeError(f"Unknown term type: {type(t)}")


def lenf(f: Func) -> int:
    """
    Function measure matching Coq Fixpoint lenf in 00.v:
    varp y x => 0
    subs F x => lenf F + 1
    """
    if isinstance(f, Varp):
        return 0
    elif isinstance(f, Subs):
        return lenf(f.func) + 1
    else:
        raise TypeError(f"Unknown func type: {type(f)}")


def measure(f: Func, t: Term) -> int:
    """Combined measure (lenf f) + (lent t)."""
    return lenf(f) + lent(t)


def act(
    f: Func,
    t: Term,
    deq: Optional[Callable[[Any, Any], bool]] = None,
    verify_measure: bool = True,
) -> Term:
    """
    Executes substitution / action function f on term t.
    Corresponds to Program Fixpoint act in alpha_core.v with well-founded measure verification.
    """
    if deq is None:
        deq = lambda a, b: a == b

    curr_meas = measure(f, t)

    def _rec_act(sub_f: Func, sub_t: Term) -> Term:
        if verify_measure:
            sub_meas = measure(sub_f, sub_t)
            if sub_meas >= curr_meas:
                raise ValueError(
                    f"Measure obligation violated: sub_meas {sub_meas} >= curr_meas {curr_meas}"
                )
        return act(sub_f, sub_t, deq=deq, verify_measure=verify_measure)

    if isinstance(t, Atom):
        v = t.var
        if isinstance(f, Varp):
            if deq(v, f.x):
                return Atom(f.y)
            else:
                return Atom(v)
        elif isinstance(f, Subs):
            if deq(v, f.x):
                return Atom(v)
            else:
                return Shft(_rec_act(f.func, Atom(v)))
        else:
            raise TypeError(f"Unknown func type: {type(f)}")

    elif isinstance(t, Appl):
        new_left = _rec_act(f, t.left)
        new_right = _rec_act(f, t.right)
        return Appl(new_left, new_right)

    elif isinstance(t, Lamb):
        x = t.var
        sub_func = Subs(f, x)
        new_body = _rec_act(sub_func, t.body)
        return Lamb(x, new_body)

    elif isinstance(t, Shft):
        new_term = _rec_act(f, t.term)
        return Shft(new_term)

    else:
        raise TypeError(f"Unknown term type: {type(t)}")


def free_vars(t: Term) -> Set[Any]:
    """Returns the set of free variables in term t."""
    if isinstance(t, Atom):
        return {t.var}
    elif isinstance(t, Appl):
        return free_vars(t.left) | free_vars(t.right)
    elif isinstance(t, Lamb):
        return free_vars(t.body) - {t.var}
    elif isinstance(t, Shft):
        return free_vars(t.term)
    else:
        raise TypeError(f"Unknown term type: {type(t)}")


def all_vars(t: Term) -> Set[Any]:
    """Returns the set of all variables (bound and free) in term t."""
    if isinstance(t, Atom):
        return {t.var}
    elif isinstance(t, Appl):
        return all_vars(t.left) | all_vars(t.right)
    elif isinstance(t, Lamb):
        return {t.var} | all_vars(t.body)
    elif isinstance(t, Shft):
        return all_vars(t.term)
    else:
        raise TypeError(f"Unknown term type: {type(t)}")


def fresh_var(used: Set[Any], base: str = "z") -> str:
    """Generates a fresh variable identifier not in used set."""
    idx = 0
    candidate = base
    while candidate in used:
        idx += 1
        candidate = f"{base}_{idx}"
    return candidate


def to_canonical(
    t: Term,
    binding_env: Optional[Dict[Any, int]] = None,
    depth: int = 0,
) -> Tuple[Any, ...]:
    """
    Converts term to a canonical de Bruijn-indexed structural representation.
    Two terms are alpha-equivalent if and only if their canonical representations match.
    """
    if binding_env is None:
        binding_env = {}

    if isinstance(t, Atom):
        if t.var in binding_env:
            # Bound variable: use de Bruijn index (distance to binder)
            return ("bound", depth - 1 - binding_env[t.var])
        else:
            # Free variable: retain variable identity
            return ("free", t.var)

    elif isinstance(t, Appl):
        return (
            "appl",
            to_canonical(t.left, binding_env, depth),
            to_canonical(t.right, binding_env, depth),
        )

    elif isinstance(t, Lamb):
        new_env = dict(binding_env)
        new_env[t.var] = depth
        return ("lamb", to_canonical(t.body, new_env, depth + 1))

    elif isinstance(t, Shft):
        return ("shft", to_canonical(t.term, binding_env, depth))

    else:
        raise TypeError(f"Unknown term type: {type(t)}")


def is_alpha_equivalent(t1: Term, t2: Term) -> bool:
    """
    Computes alpha-equivalence (alp) between two terms.
    Sound and complete with respect to the Coq inductive definition in 00.v / alpha_core.v.
    """
    return to_canonical(t1) == to_canonical(t2)


class TermGraph:
    """
    Directed logic graph representation of a lambda term with explicit binding arcs.
    Nodes: Syntax operators (Appl, Lamb, Shft) and variable occurrences (Atom).
    Edges: Child hierarchy and binding back-arcs from variable usages to binder nodes.
    """

    def __init__(self, root: Term) -> None:
        self.root: Term = root
        self.nodes: List[Dict[str, Any]] = []
        self.edges: List[Tuple[int, int, str]] = []  # (source, target, edge_type)
        self._build_graph(root, None, {})

    def _build_graph(
        self,
        t: Term,
        parent_id: Optional[int],
        binder_env: Dict[Any, int],
    ) -> int:
        node_id = len(self.nodes)
        if isinstance(t, Atom):
            is_bound = t.var in binder_env
            binder_id = binder_env.get(t.var, None)
            self.nodes.append(
                {
                    "id": node_id,
                    "kind": "atom",
                    "var": t.var,
                    "is_bound": is_bound,
                    "binder_id": binder_id,
                }
            )
            if parent_id is not None:
                self.edges.append((parent_id, node_id, "child"))
            if is_bound and binder_id is not None:
                self.edges.append((node_id, binder_id, "binding"))
            return node_id

        elif isinstance(t, Appl):
            self.nodes.append({"id": node_id, "kind": "appl"})
            if parent_id is not None:
                self.edges.append((parent_id, node_id, "child"))
            left_id = self._build_graph(t.left, node_id, binder_env)
            right_id = self._build_graph(t.right, node_id, binder_env)
            return node_id

        elif isinstance(t, Lamb):
            self.nodes.append({"id": node_id, "kind": "lamb", "bound_var": t.var})
            if parent_id is not None:
                self.edges.append((parent_id, node_id, "child"))
            new_env = dict(binder_env)
            new_env[t.var] = node_id
            self._build_graph(t.body, node_id, new_env)
            return node_id

        elif isinstance(t, Shft):
            self.nodes.append({"id": node_id, "kind": "shft"})
            if parent_id is not None:
                self.edges.append((parent_id, node_id, "child"))
            self._build_graph(t.term, node_id, binder_env)
            return node_id

        else:
            raise TypeError(f"Unknown term type: {type(t)}")

    def node_count(self) -> int:
        return len(self.nodes)

    def edge_count(self) -> int:
        return len(self.edges)

    def binding_edges(self) -> List[Tuple[int, int]]:
        return [(src, tgt) for (src, tgt, kind) in self.edges if kind == "binding"]
