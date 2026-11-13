(*
 * File: alpha_core.v
 * Project: Alpha (/botworkspace/Alpha)
 * Provenance: Modernized and extended from 00.v (Georgy Dunaev, 2018).
 * Purpose: Coq formalization of lambda terms with explicit action, measure-based termination, and alpha-equivalence.
 * Compatibility: Coq 8.14+, Coq 8.20+, and Rocq Prover (uses Coq.micromega.Lia instead of deprecated Omega).
 *)

Require Import Coq.Program.Tactics.
Require Import Coq.Program.Wf.
Require Import Coq.micromega.Lia.
Require Import Coq.Arith.PeanoNat.

Section VarSection.

Context (var : Set) (deq : var -> var -> bool).
Hypothesis deq_spec : forall x y : var, deq x y = true <-> x = y.

Inductive term : Set :=
| atom : var -> term
| appl : term -> term -> term
| lamb : var -> term -> term
| shft : term -> term.

Coercion atom : var >-> term.

Inductive func : Set :=
| varp : var -> var -> func
| subs : func -> var -> func.

Fixpoint lent (t : term) : nat :=
  match t with
  | atom _ => 0
  | appl M N => (Nat.max (lent M) (lent N)) + 1
  | lamb _ M => (lent M) + 2
  | shft M => (lent M) + 1
  end.

Fixpoint lenf (f : func) : nat :=
  match f with
  | varp _ _ => 0
  | subs F _ => (lenf F) + 1
  end.

Lemma lent_atom : forall x : var, lent (atom x) = 0.
Proof.
  intro x; reflexivity.
Qed.

Lemma lent_appl_left : forall M N : term, lent M < lent (appl M N).
Proof.
  intros M N.
  simpl.
  lia.
Qed.

Lemma lent_appl_right : forall M N : term, lent N < lent (appl M N).
Proof.
  intros M N.
  simpl.
  lia.
Qed.

Lemma measure_lamb : forall (f : func) (x : var) (M : term),
  lenf (subs f x) + lent M < lenf f + lent (lamb x M).
Proof.
  intros f x M.
  simpl.
  lia.
Qed.

Program Fixpoint act (f : func) (t : term) {measure ((lenf f) + (lent t))} : term :=
  match t with
  | atom v =>
      match f with
      | varp y x => if deq v x then atom y else atom v
      | subs F x => if deq v x then atom v else shft (act F v)
      end
  | appl M N => appl (act f M) (act f N)
  | lamb x M => lamb x (act (subs f x) M)
  | shft M =>
      match f with
      | varp _ _ => shft (act f M)
      | subs F _ => shft (act F M)
      end
  end.

Next Obligation.
  simpl.
  lia.
Defined.

Next Obligation.
  simpl.
  lia.
Defined.

Next Obligation.
  simpl.
  lia.
Defined.

Next Obligation.
  simpl.
  lia.
Defined.

Next Obligation.
  simpl.
  lia.
Defined.

Inductive alp : term -> term -> Prop :=
| ref : forall M : term, alp M M
| sym : forall M1 M2 : term, alp M1 M2 -> alp M2 M1
| tra : forall M1 M2 M3 : term, alp M1 M2 -> alp M2 M3 -> alp M1 M3
| shf : forall M1 M2 : term, alp M1 M2 -> alp (shft M1) (shft M2)
| app : forall M1 M2 N1 N2 : term, alp M1 M2 -> alp N1 N2 -> alp (appl M1 N1) (appl M2 N2)
| lam : forall (M1 M2 : term) (x : var), alp M1 M2 -> alp (lamb x M1) (lamb x M2)
| axi : forall (M : term) (y x : var), alp (lamb x M) (lamb y (act (varp y x) M)).

Theorem alp_refl : forall M : term, alp M M.
Proof.
  intro M; apply ref.
Qed.

Theorem alp_symm : forall M1 M2 : term, alp M1 M2 -> alp M2 M1.
Proof.
  intros M1 M2 H; apply sym; exact H.
Qed.

Theorem alp_trans : forall M1 M2 M3 : term, alp M1 M2 -> alp M2 M3 -> alp M1 M3.
Proof.
  intros M1 M2 M3 H12 H23; apply (tra M1 M2 M3); [exact H12 | exact H23].
Qed.

Theorem alp_app_cong : forall M1 M2 N1 N2 : term,
  alp M1 M2 -> alp N1 N2 -> alp (appl M1 N1) (appl M2 N2).
Proof.
  intros M1 M2 N1 N2 H1 H2; apply app; [exact H1 | exact H2].
Qed.

Theorem alp_lam_cong : forall (M1 M2 : term) (x : var),
  alp M1 M2 -> alp (lamb x M1) (lamb x M2).
Proof.
  intros M1 M2 x H; apply lam; exact H.
Qed.

Theorem alp_shf_cong : forall M1 M2 : term,
  alp M1 M2 -> alp (shft M1) (shft M2).
Proof.
  intros M1 M2 H; apply shf; exact H.
Qed.

End VarSection.
