#!/usr/bin/env python3
"""
Comprehensive Verification Tests for Alpha.
Validates Coq proofs, term measures, substitution action evaluation,
alpha-equivalence logic, and graph representations.
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
    Varp,
    Subs,
    lent,
    lenf,
    measure,
    act,
    free_vars,
    all_vars,
    to_canonical,
    is_alpha_equivalent,
    TermGraph,
)
from alpha_engine.syntax_verifier import CoqVerifier


class TestAlphaCoqFiles(unittest.TestCase):
    """Verifies existence, formatting, and structural health of Coq scripts."""

    def test_original_coq_file_preserved(self):
        vfile = os.path.join(ROOT, "00.v")
        self.assertTrue(os.path.isfile(vfile))
        self.assertGreater(os.path.getsize(vfile), 0)

        verifier = CoqVerifier(vfile)
        self.assertTrue(verifier.check_balanced_comments(), "00.v comments should be balanced")
        is_ok, errs = verifier.check_balanced_sections()
        self.assertTrue(is_ok, f"00.v section mismatch: {errs}")

    def test_modernized_coq_file(self):
        vfile = os.path.join(ROOT, "alpha_core.v")
        self.assertTrue(os.path.isfile(vfile))
        self.assertGreater(os.path.getsize(vfile), 0)

        verifier = CoqVerifier(vfile)
        self.assertTrue(verifier.check_balanced_comments(), "alpha_core.v comments should be balanced")
        is_ok, errs = verifier.check_balanced_sections()
        self.assertTrue(is_ok, f"alpha_core.v section mismatch: {errs}")

        # Check that alpha_core.v uses Lia and has no deprecated omega
        deprecated = verifier.find_deprecated_tactics()
        self.assertEqual(deprecated, [], f"alpha_core.v must not use deprecated tactics: {deprecated}")

        # Ensure all obligations are closed with Defined/Qed
        obligations = verifier.find_obligations()
        self.assertEqual(len(obligations), 5, "alpha_core.v should have exactly 5 obligations for act")
        for ob in obligations:
            self.assertNotIn("Admitted.", ob, "alpha_core.v obligations must be fully proven, never admitted")

        # Verify clean Coq compilation with coqc
        ok, msg = verifier.verify_with_compiler()
        self.assertTrue(ok, f"alpha_core.v coqc compilation failed: {msg}")

        # Verify explicit type annotations across all lemmas and theorems
        annot_ok, annot_errs = verifier.check_explicit_type_annotations()
        self.assertTrue(annot_ok, f"Implicit or unannotated binders found in alpha_core.v: {annot_errs}")

        # Verify modular lemma decomposition
        lemmas = verifier.find_lemmas()
        expected_lemmas = [
            "lent_atom",
            "lent_appl_left",
            "lent_appl_right",
            "lent_shft",
            "lent_lamb",
            "lenf_varp",
            "lenf_subs",
            "measure_atom_subs",
            "measure_appl_left",
            "measure_appl_right",
            "measure_lamb_subs",
            "measure_shft",
            "alp_refl",
            "alp_symm",
            "alp_trans",
            "alp_app_cong",
            "alp_lam_cong",
            "alp_shf_cong",
            "alp_appl_left_cong",
            "alp_appl_right_cong",
            "alp_axi",
            "alp_symm_iff",
        ]
        for lem in expected_lemmas:
            self.assertIn(lem, lemmas, f"Modular lemma '{lem}' must be defined in alpha_core.v")


class TestAlphaMeasures(unittest.TestCase):
    """Verifies term and function length measures and termination bounds."""

    def test_lent_measure(self):
        x = Atom("x")
        y = Atom("y")
        self.assertEqual(lent(x), 0)
        self.assertEqual(lent(y), 0)

        app = Appl(x, y)
        self.assertEqual(lent(app), 1)

        lam = Lamb("x", x)
        self.assertEqual(lent(lam), 2)  # lent(x) + 2 = 2

        sh = Shft(x)
        self.assertEqual(lent(sh), 1)  # lent(x) + 1 = 1

        nested = Lamb("x", Appl(x, Lamb("y", y)))
        # lent(y) = 0
        # lent(Lamb("y", y)) = 2
        # lent(Appl(x, ...)) = max(0, 2) + 1 = 3
        # lent(Lamb("x", ...)) = 3 + 2 = 5
        self.assertEqual(lent(nested), 5)

    def test_lenf_measure(self):
        v = Varp("y", "x")
        self.assertEqual(lenf(v), 0)

        s1 = Subs(v, "z")
        self.assertEqual(lenf(s1), 1)

        s2 = Subs(s1, "w")
        self.assertEqual(lenf(s2), 2)

    def test_measure_decrease_for_act_branches(self):
        """Verifies strict measure decrease corresponding to the 5 obligations in Coq."""
        x = Atom("x")
        y = Atom("y")
        f = Subs(Varp("b", "a"), "w")

        # Obligation 1: atom with subs
        meas_parent = measure(f, x)
        meas_rec = measure(f.func, x)
        self.assertLess(meas_rec, meas_parent)

        # Obligation 2 & 3: appl
        app = Appl(x, y)
        meas_parent = measure(f, app)
        self.assertLess(measure(f, x), meas_parent)
        self.assertLess(measure(f, y), meas_parent)

        # Obligation 4: lamb
        lam = Lamb("x", y)
        meas_parent = measure(f, lam)
        meas_rec = measure(Subs(f, "x"), y)
        self.assertLess(meas_rec, meas_parent)

        # Obligation 5: shft
        sh = Shft(x)
        meas_parent = measure(f, sh)
        meas_rec = measure(f.func, x)
        self.assertLess(meas_rec, meas_parent)

    def test_modular_measure_lemmas_semantics(self):
        """Validates semantic properties modeled by Coq modular lemmas."""
        m = Atom("m")
        # lent_shft: lent(M) < lent(shft M)
        self.assertLess(lent(m), lent(Shft(m)))
        # lent_lamb: lent(M) < lent(lamb x M)
        self.assertLess(lent(m), lent(Lamb("x", m)))
        # lenf_subs: lenf(F) < lenf(subs F x)
        f = Varp("y", "x")
        self.assertLess(lenf(f), lenf(Subs(f, "z")))
        # lenf_varp: lenf(varp x y) = 0
        self.assertEqual(lenf(Varp("a", "b")), 0)


class TestAlphaActionEvaluation(unittest.TestCase):
    """Verifies substitution / action reduction semantics."""

    def test_varp_atom_replacement(self):
        x = Atom("x")
        z = Atom("z")
        f = Varp("y", "x")
        self.assertEqual(act(f, x), Atom("y"))
        self.assertEqual(act(f, z), Atom("z"))

    def test_varp_appl(self):
        t = Appl(Atom("x"), Atom("z"))
        f = Varp("y", "x")
        expected = Appl(Atom("y"), Atom("z"))
        self.assertEqual(act(f, t), expected)

    def test_varp_lamb_bound_protection(self):
        # \x. x with [y/x] should protect bound x: \x. x
        t = Lamb("x", Atom("x"))
        f = Varp("y", "x")
        self.assertEqual(act(f, t), Lamb("x", Atom("x")))

    def test_varp_lamb_free_renaming(self):
        # \z. x with [y/x]: entering binder z wraps substituted free variable in shft: \z. ^(y)
        t = Lamb("z", Atom("x"))
        f = Varp("y", "x")
        self.assertEqual(act(f, t), Lamb("z", Shft(Atom("y"))))

    def test_shft_action(self):
        t = Shft(Atom("x"))
        f = Varp("y", "x")
        self.assertEqual(act(f, t), Shft(Atom("y")))


class TestAlphaEquivalence(unittest.TestCase):
    """Verifies alpha-equivalence (alp) relation."""

    def test_reflexivity(self):
        t1 = Atom("x")
        t2 = Appl(Atom("a"), Atom("b"))
        t3 = Lamb("x", Appl(Atom("x"), Atom("x")))
        t4 = Shft(Lamb("y", Atom("y")))
        for term in [t1, t2, t3, t4]:
            self.assertTrue(is_alpha_equivalent(term, term))

    def test_single_binder_alpha_renaming(self):
        # \x. x ~ \y. y
        t1 = Lamb("x", Atom("x"))
        t2 = Lamb("y", Atom("y"))
        self.assertTrue(is_alpha_equivalent(t1, t2))
        self.assertTrue(is_alpha_equivalent(t2, t1))

    def test_nested_binder_alpha_renaming(self):
        # \x. \y. (x y) ~ \a. \b. (a b)
        t1 = Lamb("x", Lamb("y", Appl(Atom("x"), Atom("y"))))
        t2 = Lamb("a", Lamb("b", Appl(Atom("a"), Atom("b"))))
        self.assertTrue(is_alpha_equivalent(t1, t2))

    def test_negative_different_structure(self):
        # \x. \y. (x y) !~ \x. \y. (y x)
        t1 = Lamb("x", Lamb("y", Appl(Atom("x"), Atom("y"))))
        t2 = Lamb("x", Lamb("y", Appl(Atom("y"), Atom("x"))))
        self.assertFalse(is_alpha_equivalent(t1, t2))

    def test_negative_free_variable_mismatch(self):
        # \x. (x y) !~ \x. (x z) when y != z
        t1 = Lamb("x", Appl(Atom("x"), Atom("y")))
        t2 = Lamb("x", Appl(Atom("x"), Atom("z")))
        self.assertFalse(is_alpha_equivalent(t1, t2))

    def test_free_and_all_variables(self):
        t = Lamb("x", Appl(Atom("x"), Atom("y")))
        self.assertEqual(free_vars(t), {"y"})
        self.assertEqual(all_vars(t), {"x", "y"})

    def test_congruence_and_symmetry_theorems(self):
        """Validates congruence and symmetry properties matching Coq theorems."""
        m1 = Lamb("x", Atom("x"))
        m2 = Lamb("y", Atom("y"))
        n1 = Atom("a")
        n2 = Atom("a")
        # alp_symm_iff: alp M1 M2 <-> alp M2 M1
        self.assertEqual(is_alpha_equivalent(m1, m2), is_alpha_equivalent(m2, m1))
        # alp_appl_left_cong: alp M1 M2 -> alp (appl M1 N) (appl M2 N)
        self.assertTrue(is_alpha_equivalent(Appl(m1, n1), Appl(m2, n1)))
        # alp_appl_right_cong: alp N1 N2 -> alp (appl M N1) (appl M N2)
        self.assertTrue(is_alpha_equivalent(Appl(m1, n1), Appl(m1, n2)))
        # alp_shf_cong: alp M1 M2 -> alp (shft M1) (shft M2)
        self.assertTrue(is_alpha_equivalent(Shft(m1), Shft(m2)))


class TestAlphaTermGraph(unittest.TestCase):
    """Verifies graph generation and binding back-arcs."""

    def test_graph_binding_arcs(self):
        # \x. (x x)
        t = Lamb("x", Appl(Atom("x"), Atom("x")))
        g = TermGraph(t)
        self.assertEqual(g.node_count(), 4)  # Lamb, Appl, Atom(x), Atom(x)
        bindings = g.binding_edges()
        self.assertEqual(len(bindings), 2)  # both x occurrences bind to Lamb (node 0)
        for src, tgt in bindings:
            self.assertEqual(tgt, 0)


class TestEnvironmentSanity(unittest.TestCase):
    """Verifies compliance with workspace rules (no emojis, no arrows)."""

    def test_no_emojis_or_arrows_in_alpha_repo(self):
        # Disallow arrow entities and unicode arrows in repo files
        forbidden_arrows = [
            chr(0x2192),  # right arrow
            chr(0x2190),  # left arrow
            chr(0x2193),  # down arrow
            chr(0x2191),  # up arrow
            "&" + "rarr;",
            "&" + "larr;",
            "&" + "darr;",
            "&" + "uarr;",
        ]
        text_extensions = (".py", ".v", ".md", ".txt")

        for root, _, files in os.walk(ROOT):
            if ".git" in root or "__pycache__" in root:
                continue
            for fname in files:
                fpath = os.path.join(root, fname)
                if fpath == os.path.abspath(__file__):
                    continue
                if any(fname.endswith(ext) for ext in text_extensions):
                    with open(fpath, "r", encoding="utf-8", errors="ignore") as f:
                        content = f.read()

                    # Check forbidden arrows
                    for arrow in forbidden_arrows:
                        self.assertNotIn(
                            arrow,
                            content,
                            f"Forbidden arrow '{arrow}' found in {fpath}",
                        )

                    # Check emojis (broad unicode ranges for emojis)
                    for char in content:
                        cp = ord(char)
                        is_emoji = (
                            (0x1F600 <= cp <= 0x1F64F)  # emoticons
                            or (0x1F300 <= cp <= 0x1F5FF)  # misc symbols
                            or (0x1F680 <= cp <= 0x1F6FF)  # transport
                            or (0x1F1E0 <= cp <= 0x1F1FF)  # flags
                            or (0x1F900 <= cp <= 0x1F9FF)  # supplemental
                            or (0x2600 <= cp <= 0x26FF and cp != 0x2605)  # misc symbols (excluding ★)
                        )
                        self.assertFalse(
                            is_emoji,
                            f"Emoji character U+{cp:04X} ('{char}') found in {fpath}",
                        )


if __name__ == "__main__":
    unittest.main()
