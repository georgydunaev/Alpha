#!/usr/bin/env python3
"""
Verification Tests for Alpha Church-Rosser Confluence and Beta-Eta Normalization.
Validates Coq proofs in alpha_confluence.v, Takahashi complete development,
Tait-Martin-Loef parallel reduction, diamond property verification,
Church-Rosser joinability, unique normal forms, and eta contraction.
"""

import os
import sys
import unittest

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
if ROOT not in sys.path:
    sys.path.insert(0, ROOT)

from alpha_engine.terms import (
    Term,
    Atom,
    Appl,
    Lamb,
    Shft,
    is_alpha_equivalent,
)
from alpha_engine.substitution import (
    fv,
    fresh,
    subst,
    alpha_equiv,
    beta_step,
    beta_reduce,
)
from alpha_engine.reduction import (
    parallel_reduce_step,
    all_parallel_reducts,
    is_par_beta,
    check_par_beta_diamond,
    parallel_reduce,
    eta_step,
    eta_reduce,
    beta_eta_step,
    beta_eta_reduce,
    is_beta_normal,
    is_eta_normal,
    is_beta_eta_normal,
    check_church_rosser,
)
from alpha_engine.syntax_verifier import CoqVerifier


class TestCoqConfluenceFile(unittest.TestCase):
    """Verifies existence, formatting, syntax balance, and compilation of alpha_confluence.v."""

    def setUp(self):
        self.vfile = os.path.join(ROOT, "alpha_confluence.v")
        self.assertTrue(
            os.path.isfile(self.vfile),
            f"alpha_confluence.v must exist at {self.vfile}",
        )
        self.verifier = CoqVerifier(self.vfile)

    def test_balanced_comments_and_sections(self):
        self.assertTrue(
            self.verifier.check_balanced_comments(),
            "alpha_confluence.v comments must be balanced",
        )
        is_ok, errs = self.verifier.check_balanced_sections()
        self.assertTrue(is_ok, f"alpha_confluence.v section mismatch: {errs}")

    def test_no_deprecated_tactics(self):
        deprecated = self.verifier.find_deprecated_tactics()
        self.assertEqual(
            deprecated,
            [],
            f"alpha_confluence.v must not use deprecated tactics: {deprecated}",
        )

    def test_coqc_clean_compilation(self):
        ok, msg = self.verifier.verify_with_compiler()
        self.assertTrue(ok, f"alpha_confluence.v coqc compilation failed: {msg}")

    def test_no_admitted_proofs(self):
        self.assertNotIn(
            "Admitted.",
            self.verifier.content,
            "alpha_confluence.v must contain 0 Admitted proofs",
        )

    def test_explicit_type_annotations(self):
        annot_ok, annot_errs = self.verifier.check_explicit_type_annotations()
        self.assertTrue(
            annot_ok,
            f"Implicit or unannotated binders found in alpha_confluence.v: {annot_errs}",
        )

    def test_required_modular_lemmas_present(self):
        lemmas = self.verifier.find_lemmas()
        expected = [
            "deq_refl",
            "deq_eq",
            "deq_neq",
            "subst_atom_same",
            "subst_atom_diff",
            "subst_appl",
            "subst_lamb_same",
            "subst_lamb_diff",
            "subst_shft",
            "subst_fresh",
            "subst_id",
            "alp_refl",
            "alp_symm",
            "alp_trans",
            "beta_step_to_star",
            "beta_star_trans",
            "beta_star_appl",
            "beta_star_lamb",
            "beta_star_shft",
            "par_beta_refl",
            "par_beta_subst_right",
            "par_beta_star_trans",
            "beta_step_to_par_beta",
            "beta_star_to_par_beta_star",
            "par_beta_to_beta_star",
            "par_beta_star_to_beta_star",
            "takahashi_triangle",
            "par_beta_confluence",
            "par_beta_diamond",
            "strip_lemma",
            "par_beta_star_confluence",
            "church_rosser",
            "unique_normal_forms",
            "eta_step_to_star",
            "eta_star_trans",
        ]
        for lem in expected:
            self.assertIn(
                lem,
                lemmas,
                f"Required lemma or theorem '{lem}' must be defined in alpha_confluence.v",
            )


class TestParallelReduction(unittest.TestCase):
    """Verifies Takahashi complete development and Tait-Martin-Loef parallel reduction."""

    def test_parallel_reduce_step_atom(self):
        x = Atom("x")
        self.assertEqual(parallel_reduce_step(x), x)

    def test_parallel_reduce_step_single_redex(self):
        # (lambda x. x) y reduces in one step to y
        id_fn = Lamb("x", Atom("x"))
        redex = Appl(id_fn, Atom("y"))
        reduct = parallel_reduce_step(redex)
        self.assertEqual(reduct, Atom("y"))

    def test_parallel_reduce_step_multiple_simultaneous_redexes(self):
        # (lambda x. x) ((lambda y. y) z)
        # Sequential beta requires 2 steps.
        # Parallel beta contracts both redexes simultaneously in 1 step to z.
        id_x = Lamb("x", Atom("x"))
        id_y = Lamb("y", Atom("y"))
        inner = Appl(id_y, Atom("z"))
        outer = Appl(id_x, inner)

        step1 = parallel_reduce_step(outer)
        self.assertEqual(step1, Atom("z"))

    def test_all_parallel_reducts_and_membership(self):
        # (lambda x. x) ((lambda y. a) z)
        # Permissible parallel reducts are:
        # 1. Complete contraction: a
        # 2. Left contracted, right intact: (lambda y. a) z
        # 3. Left intact, right contracted: (lambda x. x) a
        # 4. Identity (0 contracted): (lambda x. x) ((lambda y. a) z)
        id_x = Lamb("x", Atom("x"))
        const_a = Lamb("y", Atom("a"))
        inner = Appl(const_a, Atom("z"))
        outer = Appl(id_x, inner)

        reducts = all_parallel_reducts(outer)
        self.assertEqual(len(reducts), 4)

        for r in reducts:
            self.assertTrue(
                is_par_beta(outer, r),
                f"Reduct {r} must satisfy is_par_beta relation with source {outer}",
            )

        # Check membership of all 4 expected reducts up to alpha-equivalence
        expected = [
            Atom("a"),
            Appl(const_a, Atom("z")),
            Appl(id_x, Atom("a")),
            outer,
        ]
        for exp in expected:
            found = any(alpha_equiv(exp, r) for r in reducts)
            self.assertTrue(found, f"Expected parallel reduct {exp} not found in {reducts}")

    def test_is_par_beta_negative(self):
        # (lambda x. x) y cannot reduce to unrelated term w in parallel reduction
        redex = Appl(Lamb("x", Atom("x")), Atom("y"))
        self.assertFalse(is_par_beta(redex, Atom("w")))

    def test_parallel_reduce_iterative(self):
        # ((lambda x. lambda y. x) a) b reduces to a
        k_comb = Lamb("x", Lamb("y", Atom("x")))
        app1 = Appl(k_comb, Atom("a"))
        app2 = Appl(app1, Atom("b"))

        nf, steps = parallel_reduce(app2)
        self.assertTrue(alpha_equiv(nf, Atom("a")))
        self.assertTrue(steps <= 2)


class TestDiamondPropertyAndConfluence(unittest.TestCase):
    """Verifies Takahashi triangle, diamond property, and Church-Rosser confluence."""

    def test_takahashi_triangle_joinability(self):
        # For any term M and any parallel reducts N1, N2 of M,
        # Takahashi complete development cd(M) must satisfy:
        # par_beta N1 (cd M) and par_beta N2 (cd M).
        id_x = Lamb("x", Atom("x"))
        id_y = Lamb("y", Atom("y"))
        M = Appl(id_x, Appl(id_y, Atom("z")))

        cd_M = parallel_reduce_step(M)
        reducts = all_parallel_reducts(M)

        for N in reducts:
            self.assertTrue(
                is_par_beta(N, cd_M),
                f"Takahashi triangle failed: {N} does not parallel-reduce to cd(M) = {cd_M}",
            )

    def test_par_beta_diamond_checker(self):
        id_x = Lamb("x", Atom("x"))
        id_y = Lamb("y", Atom("y"))
        M = Appl(id_x, Appl(id_y, Atom("z")))

        has_diamond, join, witnesses = check_par_beta_diamond(M)
        self.assertTrue(has_diamond)
        self.assertTrue(len(witnesses) > 0)
        self.assertIsNotNone(join)
        self.assertTrue(alpha_equiv(join, Atom("z")))

    def test_church_rosser_divergent_reduction_paths(self):
        # Term: (lambda x. lambda y. y) ((lambda z. z) a) ((lambda w. w) b)
        # Leftmost-outermost reduces outer redex first, discarding ((lambda z. z) a).
        # Parallel reduction contracts inner redexes simultaneously with outer redex.
        # Both paths must converge to b.
        k_second = Lamb("x", Lamb("y", Atom("y")))
        arg1 = Appl(Lamb("z", Atom("z")), Atom("a"))
        arg2 = Appl(Lamb("w", Atom("w")), Atom("b"))
        term = Appl(Appl(k_second, arg1), arg2)

        is_confluent, beta_nf, par_nf, common_nf = check_church_rosser(term)
        self.assertTrue(is_confluent)
        self.assertTrue(alpha_equiv(beta_nf, Atom("b")))
        self.assertTrue(alpha_equiv(par_nf, Atom("b")))
        self.assertIsNotNone(common_nf)
        self.assertTrue(alpha_equiv(common_nf, Atom("b")))

    def test_unique_normal_forms_up_to_alpha(self):
        # Two reductions of ((lambda x. lambda y. x y) f) z
        # One with variable renaming during substitution, both must yield (f z).
        term = Appl(Appl(Lamb("x", Lamb("y", Appl(Atom("x"), Atom("y")))), Atom("f")), Atom("z"))
        nf1, _ = beta_reduce(term)
        nf2, _ = parallel_reduce(term)

        expected = Appl(Atom("f"), Atom("z"))
        self.assertTrue(alpha_equiv(nf1, expected))
        self.assertTrue(alpha_equiv(nf2, expected))
        self.assertTrue(alpha_equiv(nf1, nf2))


class TestEtaReductionAndBetaEtaNormalization(unittest.TestCase):
    """Verifies eta contraction, eta normal forms, and combined beta-eta normalization."""

    def test_eta_step_success(self):
        # (lambda x. f x) reduces to f because x is fresh in f
        term = Lamb("x", Appl(Atom("f"), Atom("x")))
        has_reduced, reduct = eta_step(term)
        self.assertTrue(has_reduced)
        self.assertEqual(reduct, Atom("f"))

    def test_eta_step_negative_when_variable_occurs_free(self):
        # (lambda x. x x) cannot eta-reduce because x occurs free in left branch
        term = Lamb("x", Appl(Atom("x"), Atom("x")))
        has_reduced, reduct = eta_step(term)
        self.assertFalse(has_reduced)
        self.assertEqual(reduct, term)

    def test_eta_step_negative_when_not_variable(self):
        # (lambda x. f (g x)) cannot eta-reduce at root because argument is (g x), not x
        term = Lamb("x", Appl(Atom("f"), Appl(Atom("g"), Atom("x"))))
        # Inner expression does not have eta-redex at top
        has_reduced, _ = eta_step(term)
        self.assertFalse(has_reduced)

    def test_eta_reduce_multistep(self):
        # (lambda x. lambda y. f x y) eta-reduces in 2 steps to f:
        # Step 1: (lambda x. (lambda y. (f x) y)) reduces to (lambda x. f x)
        # Step 2: (lambda x. f x) reduces to f
        inner = Lamb("y", Appl(Appl(Atom("f"), Atom("x")), Atom("y")))
        outer = Lamb("x", inner)

        nf, steps = eta_reduce(outer)
        self.assertEqual(nf, Atom("f"))
        self.assertEqual(steps, 2)

    def test_beta_eta_step_and_reduce(self):
        # ((lambda x. lambda y. x y) z)
        # Beta step: lambda y. z y
        # Eta step: z
        term = Appl(Lamb("x", Lamb("y", Appl(Atom("x"), Atom("y")))), Atom("z"))

        # Step 1 is beta
        has_step1, t1 = beta_eta_step(term)
        self.assertTrue(has_step1)
        self.assertTrue(alpha_equiv(t1, Lamb("y", Appl(Atom("z"), Atom("y")))))

        # Step 2 is eta
        has_step2, t2 = beta_eta_step(t1)
        self.assertTrue(has_step2)
        self.assertEqual(t2, Atom("z"))

        # Full normalization
        final_nf, total_steps = beta_eta_reduce(term)
        self.assertEqual(final_nf, Atom("z"))
        self.assertEqual(total_steps, 2)

    def test_is_normal_predicates(self):
        term_beta_redex = Appl(Lamb("x", Atom("x")), Atom("y"))
        term_eta_redex = Lamb("x", Appl(Atom("f"), Atom("x")))
        term_both_redex = Appl(Lamb("z", Lamb("x", Appl(Atom("f"), Atom("x")))), Atom("a"))
        term_nf = Atom("x")

        self.assertFalse(is_beta_normal(term_beta_redex))
        self.assertTrue(is_eta_normal(term_beta_redex))
        self.assertFalse(is_beta_eta_normal(term_beta_redex))

        self.assertTrue(is_beta_normal(term_eta_redex))
        self.assertFalse(is_eta_normal(term_eta_redex))
        self.assertFalse(is_beta_eta_normal(term_eta_redex))

        self.assertFalse(is_beta_normal(term_both_redex))
        self.assertFalse(is_beta_eta_normal(term_both_redex))

        self.assertTrue(is_beta_normal(term_nf))
        self.assertTrue(is_eta_normal(term_nf))
        self.assertTrue(is_beta_eta_normal(term_nf))


if __name__ == "__main__":
    unittest.main()
