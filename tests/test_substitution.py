#!/usr/bin/env python3
"""
Verification Tests for Alpha Capture-Avoiding Substitution and Freshness.
Validates Coq proofs in alpha_subst.v, free variable analysis, freshness relations,
capture-avoiding substitution, alpha-equivalence preservation, and beta-reduction.
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
    rename,
    subst,
    alpha_equiv,
    beta_step,
    beta_reduce,
)
from alpha_engine.syntax_verifier import CoqVerifier


class TestCoqSubstitutionFile(unittest.TestCase):
    """Verifies existence, formatting, syntax balance, and compilation of alpha_subst.v."""

    def setUp(self):
        self.vfile = os.path.join(ROOT, "alpha_subst.v")
        self.assertTrue(os.path.isfile(self.vfile), f"alpha_subst.v must exist at {self.vfile}")
        self.verifier = CoqVerifier(self.vfile)

    def test_balanced_comments_and_sections(self):
        self.assertTrue(
            self.verifier.check_balanced_comments(),
            "alpha_subst.v comments must be balanced",
        )
        is_ok, errs = self.verifier.check_balanced_sections()
        self.assertTrue(is_ok, f"alpha_subst.v section mismatch: {errs}")

    def test_no_deprecated_tactics(self):
        deprecated = self.verifier.find_deprecated_tactics()
        self.assertEqual(
            deprecated,
            [],
            f"alpha_subst.v must not use deprecated tactics: {deprecated}",
        )

    def test_coqc_clean_compilation(self):
        ok, msg = self.verifier.verify_with_compiler()
        self.assertTrue(ok, f"alpha_subst.v coqc compilation failed: {msg}")

    def test_no_admitted_proofs(self):
        self.assertNotIn(
            "Admitted.",
            self.verifier.content,
            "alpha_subst.v must contain 0 Admitted proofs",
        )

    def test_explicit_type_annotations(self):
        annot_ok, annot_errs = self.verifier.check_explicit_type_annotations()
        self.assertTrue(
            annot_ok,
            f"Implicit or unannotated binders found in alpha_subst.v: {annot_errs}",
        )

    def test_required_modular_lemmas_present(self):
        lemmas = self.verifier.find_lemmas()
        expected = [
            "fresh_atom",
            "fresh_appl",
            "fresh_shft",
            "fresh_lamb_self",
            "fresh_lamb_diff",
            "lent_rename",
            "subst_atom_same",
            "subst_atom_diff",
            "subst_appl",
            "subst_shft",
            "subst_lamb_self",
            "subst_lamb_diff",
            "subst_fresh",
            "subst_id",
            "alp_refl",
            "alp_symm",
            "alp_trans",
            "alp_app_cong",
            "alp_lam_cong",
            "alp_shf_cong",
            "alp_axi",
            "alp_subst_cong",
            "alp_core_to_alp",
            "alp_core_preservation",
        ]
        for lem in expected:
            self.assertIn(
                lem,
                lemmas,
                f"Required lemma or theorem '{lem}' must be defined in alpha_subst.v",
            )


class TestFreeVariablesAndFreshness(unittest.TestCase):
    """Verifies free variable calculation (fv) and freshness predicate (fresh)."""

    def test_fv_atom(self):
        x = Atom("x")
        self.assertEqual(fv(x), ["x"])
        self.assertFalse(fresh("x", x))
        self.assertTrue(fresh("y", x))

    def test_fv_appl(self):
        app = Appl(Atom("x"), Atom("y"))
        self.assertEqual(fv(app), ["x", "y"])
        self.assertFalse(fresh("x", app))
        self.assertFalse(fresh("y", app))
        self.assertTrue(fresh("z", app))

    def test_fv_lamb_bound(self):
        lam = Lamb("x", Atom("x"))
        self.assertEqual(fv(lam), [])
        self.assertTrue(fresh("x", lam))

    def test_fv_lamb_nested(self):
        # \x. (x y) -> free: y
        lam = Lamb("x", Appl(Atom("x"), Atom("y")))
        self.assertEqual(fv(lam), ["y"])
        self.assertTrue(fresh("x", lam))
        self.assertFalse(fresh("y", lam))

    def test_fv_shft(self):
        sh = Shft(Atom("x"))
        self.assertEqual(fv(sh), ["x"])
        self.assertFalse(fresh("x", sh))
        self.assertTrue(fresh("y", sh))


class TestRenaming(unittest.TestCase):
    """Verifies variable renaming function."""

    def test_rename_atom(self):
        x = Atom("x")
        self.assertEqual(rename("x", "z", x), Atom("z"))
        self.assertEqual(rename("y", "z", x), Atom("x"))

    def test_rename_appl(self):
        app = Appl(Atom("x"), Atom("y"))
        self.assertEqual(rename("x", "z", app), Appl(Atom("z"), Atom("y")))

    def test_rename_lamb_shadowed(self):
        # In \x. x, renaming x to z does nothing because x is shadowed by binder
        lam = Lamb("x", Atom("x"))
        self.assertEqual(rename("x", "z", lam), Lamb("x", Atom("x")))

    def test_rename_lamb_body(self):
        # In \w. x, renaming x to z renames free occurrence in body
        lam = Lamb("w", Atom("x"))
        self.assertEqual(rename("x", "z", lam), Lamb("w", Atom("z")))


class TestCaptureAvoidingSubstitution(unittest.TestCase):
    """Verifies capture-avoiding substitution and required formal lemmas."""

    def test_subst_atom_same(self):
        x = Atom("x")
        n = Atom("n")
        self.assertEqual(subst("x", n, x), n)

    def test_subst_atom_diff(self):
        y = Atom("y")
        n = Atom("n")
        self.assertEqual(subst("x", n, y), y)

    def test_subst_fresh_lemma(self):
        # fresh x M -> subst x N M = M
        m = Lamb("y", Appl(Atom("y"), Atom("z")))
        n = Atom("w")
        self.assertTrue(fresh("x", m))
        self.assertEqual(subst("x", n, m), m)

    def test_subst_id_lemma(self):
        # subst x (atom x) M = M
        terms = [
            Atom("x"),
            Atom("y"),
            Appl(Atom("x"), Atom("y")),
            Lamb("x", Atom("x")),
            Lamb("y", Appl(Atom("x"), Atom("y"))),
            Shft(Atom("x")),
        ]
        for m in terms:
            self.assertEqual(subst("x", Atom("x"), m), m)

    def test_subst_shadowed_in_lambda(self):
        # \x. x with x := n remains \x. x
        lam = Lamb("x", Atom("x"))
        self.assertEqual(subst("x", Atom("n"), lam), lam)

    def test_subst_capture_avoidance(self):
        # Classic capture hazard:
        # M = \y. x, substituting x := y
        # Naive substitution yields \y. y (captured free variable y!)
        # Capture-avoiding substitution renames y to fresh y_1: \y_1. y
        m = Lamb("y", Atom("x"))
        n = Atom("y")
        result = subst("x", n, m)

        self.assertIsInstance(result, Lamb)
        # Binder variable must NOT be y
        self.assertNotEqual(result.var, "y")
        # Free variables of result must be {"y"}
        self.assertEqual(set(fv(result)), {"y"})
        # Result must be alpha-equivalent to \z. y
        expected = Lamb("z", Atom("y"))
        self.assertTrue(alpha_equiv(result, expected))

    def test_subst_nested_capture_avoidance(self):
        # M = \y. \z. (x y), substitute x := (y z)
        # Both y and z occur in N, so both binders must be renamed if needed
        m = Lamb("y", Lamb("z", Appl(Atom("x"), Atom("y"))))
        n = Appl(Atom("y"), Atom("z"))
        result = subst("x", n, m)

        # Free variables in result must be {"y", "z"}
        self.assertEqual(set(fv(result)), {"y", "z"})
        # Result must be alpha-equivalent to \a. \b. ((y z) a)
        a = Atom("a")
        b = Atom("b")
        ref = Lamb("a", Lamb("b", Appl(Appl(Atom("y"), Atom("z")), a)))
        self.assertTrue(alpha_equiv(result, ref))


class TestAlphaEquivalencePreservation(unittest.TestCase):
    """Verifies that alpha-equivalence is preserved under substitution: alp M1 M2 -> alp (subst x N M1) (subst x N M2)."""

    def test_alp_preservation_identity(self):
        m1 = Lamb("x", Atom("x"))
        m2 = Lamb("y", Atom("y"))
        self.assertTrue(alpha_equiv(m1, m2))

        n = Appl(Atom("a"), Atom("b"))
        sub1 = subst("w", n, m1)
        sub2 = subst("w", n, m2)
        self.assertTrue(alpha_equiv(sub1, sub2))

    def test_alp_preservation_free_variable_substitution(self):
        m1 = Lamb("a", Appl(Atom("x"), Atom("a")))
        m2 = Lamb("b", Appl(Atom("x"), Atom("b")))
        self.assertTrue(alpha_equiv(m1, m2))

        n = Lamb("z", Atom("z"))
        sub1 = subst("x", n, m1)
        sub2 = subst("x", n, m2)
        self.assertTrue(alpha_equiv(sub1, sub2))

    def test_alp_preservation_with_capture_hazard(self):
        # Both M1 and M2 are alpha-equivalent, and substituting N triggers renaming
        m1 = Lamb("y", Appl(Atom("x"), Atom("y")))
        m2 = Lamb("z", Appl(Atom("x"), Atom("z")))
        self.assertTrue(alpha_equiv(m1, m2))

        # Substitute x := y (which clashes with binder of m1)
        n = Atom("y")
        sub1 = subst("x", n, m1)
        sub2 = subst("x", n, m2)
        self.assertTrue(alpha_equiv(sub1, sub2))


class TestBetaReduction(unittest.TestCase):
    """Verifies beta-reduction steps and normalization."""

    def test_beta_step_identity(self):
        # ((\x. x) y) -> y
        redex = Appl(Lamb("x", Atom("x")), Atom("y"))
        has_reduced, result = beta_step(redex)
        self.assertTrue(has_reduced)
        self.assertEqual(result, Atom("y"))

    def test_beta_step_k_combinator(self):
        # ((\x. \y. x) a) -> \y. a
        k = Lamb("x", Lamb("y", Atom("x")))
        app1 = Appl(k, Atom("a"))
        has_reduced, res1 = beta_step(app1)
        self.assertTrue(has_reduced)
        self.assertTrue(alpha_equiv(res1, Lamb("y", Atom("a"))))

        # ((\y. a) b) -> a
        app2 = Appl(res1, Atom("b"))
        has_reduced2, res2 = beta_step(app2)
        self.assertTrue(has_reduced2)
        self.assertEqual(res2, Atom("a"))

    def test_beta_reduce_full(self):
        # ((\x. \y. x) a b) reduces to a in 2 steps
        k = Lamb("x", Lamb("y", Atom("x")))
        term = Appl(Appl(k, Atom("a")), Atom("b"))
        norm, steps = beta_reduce(term)
        self.assertEqual(steps, 2)
        self.assertEqual(norm, Atom("a"))

    def test_beta_step_capture_avoiding(self):
        # ((\x. \y. x) y) -> \y_1. y
        # The argument y must NOT be captured by the inner \y
        k = Lamb("x", Lamb("y", Atom("x")))
        term = Appl(k, Atom("y"))
        has_reduced, result = beta_step(term)
        self.assertTrue(has_reduced)
        self.assertIsInstance(result, Lamb)
        self.assertNotEqual(result.var, "y")
        self.assertEqual(set(fv(result)), {"y"})
        self.assertTrue(alpha_equiv(result, Lamb("z", Atom("y"))))

    def test_normal_form_no_reduction(self):
        atom = Atom("x")
        has_reduced, res = beta_step(atom)
        self.assertFalse(has_reduced)
        self.assertEqual(res, atom)


if __name__ == "__main__":
    unittest.main()
