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
Hypothesis deq_spec : forall (x : var) (y : var), deq x y = true <-> x = y.

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

(* Modular measure and length lemmas *)

Lemma lent_atom : forall (x : var), lent (atom x) = 0.
Proof.
  intro x.
  reflexivity.
Qed.

Lemma lent_appl_left : forall (M : term) (N : term), lent M < lent (appl M N).
Proof.
  intros M N.
  simpl.
  lia.
Qed.

Lemma lent_appl_right : forall (M : term) (N : term), lent N < lent (appl M N).
Proof.
  intros M N.
  simpl.
  lia.
Qed.

Lemma lent_shft : forall (M : term), lent M < lent (shft M).
Proof.
  intro M.
  simpl.
  lia.
Qed.

Lemma lent_lamb : forall (x : var) (M : term), lent M < lent (lamb x M).
Proof.
  intros x M.
  simpl.
  lia.
Qed.

Lemma lenf_varp : forall (x : var) (y : var), lenf (varp x y) = 0.
Proof.
  intros x y.
  reflexivity.
Qed.

Lemma lenf_subs : forall (F : func) (x : var), lenf F < lenf (subs F x).
Proof.
  intros F x.
  simpl.
  lia.
Qed.

Lemma measure_atom_subs : forall (F : func) (x : var) (v : var),
  lenf F + 0 < lenf (subs F x) + lent (atom v).
Proof.
  intros F x v.
  simpl.
  lia.
Qed.

Lemma measure_appl_left : forall (f : func) (M : term) (N : term),
  lenf f + lent M < lenf f + lent (appl M N).
Proof.
  intros f M N.
  simpl.
  lia.
Qed.

Lemma measure_appl_right : forall (f : func) (M : term) (N : term),
  lenf f + lent N < lenf f + lent (appl M N).
Proof.
  intros f M N.
  simpl.
  lia.
Qed.

Lemma measure_lamb_subs : forall (f : func) (x : var) (M : term),
  lenf (subs f x) + lent M < lenf f + lent (lamb x M).
Proof.
  intros f x M.
  simpl.
  lia.
Qed.

Lemma measure_shft : forall (f : func) (M : term),
  lenf f + lent M < lenf f + lent (shft M).
Proof.
  intros f M.
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
  | shft M => shft (act f M)
  end.

Next Obligation.
  apply (measure_atom_subs F x v).
Defined.

Next Obligation.
  apply (measure_appl_left f M N).
Defined.

Next Obligation.
  apply (measure_appl_right f M N).
Defined.

Next Obligation.
  apply (measure_lamb_subs f x M).
Defined.

Next Obligation.
  apply (measure_shft f M).
Defined.

Inductive alp : term -> term -> Prop :=
| ref : forall (M : term), alp M M
| sym : forall (M1 : term) (M2 : term), alp M1 M2 -> alp M2 M1
| tra : forall (M1 : term) (M2 : term) (M3 : term), alp M1 M2 -> alp M2 M3 -> alp M1 M3
| shf : forall (M1 : term) (M2 : term), alp M1 M2 -> alp (shft M1) (shft M2)
| app : forall (M1 : term) (M2 : term) (N1 : term) (N2 : term),
    alp M1 M2 -> alp N1 N2 -> alp (appl M1 N1) (appl M2 N2)
| lam : forall (M1 : term) (M2 : term) (x : var),
    alp M1 M2 -> alp (lamb x M1) (lamb x M2)
| axi : forall (M : term) (y : var) (x : var),
    alp (lamb x M) (lamb y (act (varp y x) M)).

Theorem alp_refl : forall (M : term), alp M M.
Proof.
  intro M.
  apply ref.
Qed.

Theorem alp_symm : forall (M1 : term) (M2 : term), alp M1 M2 -> alp M2 M1.
Proof.
  intros M1 M2 H.
  apply sym.
  exact H.
Qed.

Theorem alp_trans : forall (M1 : term) (M2 : term) (M3 : term),
  alp M1 M2 -> alp M2 M3 -> alp M1 M3.
Proof.
  intros M1 M2 M3 H12 H23.
  apply (tra M1 M2 M3); [exact H12 | exact H23].
Qed.

Theorem alp_app_cong : forall (M1 : term) (M2 : term) (N1 : term) (N2 : term),
  alp M1 M2 -> alp N1 N2 -> alp (appl M1 N1) (appl M2 N2).
Proof.
  intros M1 M2 N1 N2 H1 H2.
  apply app; [exact H1 | exact H2].
Qed.

Theorem alp_lam_cong : forall (M1 : term) (M2 : term) (x : var),
  alp M1 M2 -> alp (lamb x M1) (lamb x M2).
Proof.
  intros M1 M2 x H.
  apply lam.
  exact H.
Qed.

Theorem alp_shf_cong : forall (M1 : term) (M2 : term),
  alp M1 M2 -> alp (shft M1) (shft M2).
Proof.
  intros M1 M2 H.
  apply shf.
  exact H.
Qed.

Theorem alp_appl_left_cong : forall (M1 : term) (M2 : term) (N : term),
  alp M1 M2 -> alp (appl M1 N) (appl M2 N).
Proof.
  intros M1 M2 N H.
  apply app; [exact H | apply ref].
Qed.

Theorem alp_appl_right_cong : forall (M : term) (N1 : term) (N2 : term),
  alp N1 N2 -> alp (appl M N1) (appl M N2).
Proof.
  intros M N1 N2 H.
  apply app; [apply ref | exact H].
Qed.

Theorem alp_axi : forall (M : term) (y : var) (x : var),
  alp (lamb x M) (lamb y (act (varp y x) M)).
Proof.
  intros M y x.
  apply axi.
Qed.

Theorem alp_symm_iff : forall (M1 : term) (M2 : term),
  alp M1 M2 <-> alp M2 M1.
Proof.
  intros M1 M2.
  split; intro H; apply sym; exact H.
Qed.

End VarSection.
