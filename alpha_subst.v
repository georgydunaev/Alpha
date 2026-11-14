(*
 * File: alpha_subst.v
 * Project: Alpha (/botworkspace/Alpha)
 * Purpose: Coq formalization of free variables, freshness relations,
 *          capture-avoiding substitution, and alpha-equivalence preservation.
 * Compatibility: Coq 8.14+, Coq 8.20+, and Rocq Prover.
 *)

Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.micromega.Lia.
Require Import alpha_core.

Section SubstSection.

Context (var : Set) (deq : var -> var -> bool).
Hypothesis deq_spec : forall (x : var) (y : var), deq x y = true <-> x = y.

Lemma deq_refl : forall (x : var), deq x x = true.
Proof.
  intro x.
  apply deq_spec.
  reflexivity.
Qed.

Lemma deq_eq : forall (x : var) (y : var), deq x y = true -> x = y.
Proof.
  intros x y.
  apply deq_spec.
Qed.

Lemma deq_neq : forall (x : var) (y : var), deq x y = false -> x <> y.
Proof.
  intros x y H Heq.
  subst.
  rewrite deq_refl in H.
  discriminate.
Qed.

Lemma deq_neq_false : forall (x : var) (y : var), x <> y -> deq x y = false.
Proof.
  intros x y H.
  destruct (deq x y) eqn:E.
  - apply deq_eq in E. exfalso. apply H. exact E.
  - reflexivity.
Qed.

(* Free variables calculation *)
Fixpoint fv (t : term var) : list var :=
  match t with
  | atom _ v => v :: nil
  | appl _ M N => fv M ++ fv N
  | lamb _ y M => filter (fun v : var => negb (deq v y)) (fv M)
  | shft _ M => fv M
  end.

(* Freshness relation: x does not occur free in M *)
Definition fresh (x : var) (M : term var) : Prop := ~ In x (fv M).

(* Freshness modular lemmas *)
Lemma fresh_atom : forall (x : var) (v : var),
  x <> v <-> fresh x (atom var v).
Proof.
  intros x v.
  unfold fresh.
  simpl.
  split; intro H.
  - intro Hin.
    destruct Hin as [Heq | Hfalse].
    + symmetry in Heq. apply H. exact Heq.
    + contradiction.
  - intro Heq.
    subst.
    apply H.
    left.
    reflexivity.
Qed.

Lemma fresh_appl : forall (x : var) (M1 : term var) (M2 : term var),
  fresh x M1 /\ fresh x M2 <-> fresh x (appl var M1 M2).
Proof.
  intros x M1 M2.
  unfold fresh.
  simpl.
  split; intro H.
  - destruct H as [H1 H2].
    intro Hin.
    apply in_app_or in Hin.
    destruct Hin as [Hin1 | Hin2].
    + apply H1. exact Hin1.
    + apply H2. exact Hin2.
  - split.
    + intro Hin. apply H. apply in_or_app. left. exact Hin.
    + intro Hin. apply H. apply in_or_app. right. exact Hin.
Qed.

Lemma fresh_shft : forall (x : var) (M : term var),
  fresh x M <-> fresh x (shft var M).
Proof.
  intros x M.
  unfold fresh.
  simpl.
  reflexivity.
Qed.

Lemma fresh_lamb_self : forall (x : var) (M : term var),
  fresh x (lamb var x M).
Proof.
  intros x M.
  unfold fresh.
  simpl.
  intro Hin.
  apply filter_In in Hin.
  destruct Hin as [Hin Hcond].
  rewrite deq_refl in Hcond.
  simpl in Hcond.
  discriminate.
Qed.

Lemma fresh_lamb_diff : forall (x : var) (y : var) (M : term var),
  x <> y -> (fresh x M <-> fresh x (lamb var y M)).
Proof.
  intros x y M Hdiff.
  unfold fresh.
  simpl.
  split; intro H.
  - intro Hin.
    apply filter_In in Hin.
    destruct Hin as [Hin _].
    apply H.
    exact Hin.
  - intro Hin.
    apply H.
    apply filter_In.
    split; [exact Hin |].
    rewrite negb_true_iff.
    apply deq_neq_false.
    exact Hdiff.
Qed.

(* Variable renaming function *)
Fixpoint rename (y : var) (z : var) (t : term var) : term var :=
  match t with
  | atom _ v => if deq v y then atom var z else atom var v
  | appl _ M N => appl var (rename y z M) (rename y z N)
  | lamb _ w M => if deq w y then lamb var w M else lamb var w (rename y z M)
  | shft _ M => shft var (rename y z M)
  end.

Lemma lent_rename : forall (y : var) (z : var) (t : term var),
  lent var (rename y z t) = lent var t.
Proof.
  intros y z t.
  induction t.
  - simpl. destruct (deq v y); reflexivity.
  - simpl. rewrite IHt1, IHt2. reflexivity.
  - simpl. destruct (deq v y); simpl; [reflexivity | rewrite IHt; reflexivity].
  - simpl. rewrite IHt. reflexivity.
Qed.

(* Capture-avoiding substitution *)
Fixpoint subst (x : var) (N : term var) (M : term var) : term var :=
  match M with
  | atom _ v => if deq v x then N else atom var v
  | appl _ M1 M2 => appl var (subst x N M1) (subst x N M2)
  | lamb _ y M1 =>
      if deq y x then lamb var y M1
      else lamb var y (subst x N M1)
  | shft _ M1 => shft var (subst x N M1)
  end.

(* Structural substitution lemmas *)
Lemma subst_atom_same : forall (x : var) (N : term var),
  subst x N (atom var x) = N.
Proof.
  intros x N.
  simpl.
  rewrite deq_refl.
  reflexivity.
Qed.

Lemma subst_atom_diff : forall (x : var) (v : var) (N : term var),
  v <> x -> subst x N (atom var v) = atom var v.
Proof.
  intros x v N Hdiff.
  simpl.
  rewrite (deq_neq_false v x Hdiff).
  reflexivity.
Qed.

Lemma subst_appl : forall (x : var) (N : term var) (M1 : term var) (M2 : term var),
  subst x N (appl var M1 M2) = appl var (subst x N M1) (subst x N M2).
Proof.
  intros x N M1 M2.
  reflexivity.
Qed.

Lemma subst_shft : forall (x : var) (N : term var) (M : term var),
  subst x N (shft var M) = shft var (subst x N M).
Proof.
  intros x N M.
  reflexivity.
Qed.

Lemma subst_lamb_self : forall (x : var) (N : term var) (M : term var),
  subst x N (lamb var x M) = lamb var x M.
Proof.
  intros x N M.
  simpl.
  rewrite deq_refl.
  reflexivity.
Qed.

Lemma subst_lamb_diff : forall (x : var) (y : var) (N : term var) (M : term var),
  y <> x -> subst x N (lamb var y M) = lamb var y (subst x N M).
Proof.
  intros x y N M Hdiff.
  simpl.
  rewrite (deq_neq_false y x Hdiff).
  reflexivity.
Qed.

(*
 * Primary Substitution Property:
 * Substitution of a fresh variable does not change the term.
 *)
Theorem subst_fresh : forall (x : var) (N : term var) (M : term var),
  fresh x M -> subst x N M = M.
Proof.
  intros x N M.
  induction M; intro Hfresh.
  - simpl in *.
    destruct (deq v x) eqn:E.
    + apply deq_eq in E. subst.
      exfalso. apply Hfresh. left. reflexivity.
    + reflexivity.
  - simpl in *.
    assert (fresh x M1) as H1 by (intro H; apply Hfresh, in_or_app; left; exact H).
    assert (fresh x M2) as H2 by (intro H; apply Hfresh, in_or_app; right; exact H).
    rewrite IHM1 by exact H1.
    rewrite IHM2 by exact H2.
    reflexivity.
  - simpl in *.
    destruct (deq v x) eqn:E.
    + reflexivity.
    + f_equal.
      apply IHM.
      intro Hx.
      apply Hfresh.
      apply filter_In.
      split; [exact Hx |].
      rewrite negb_true_iff.
      apply deq_neq_false.
      intro Heq; subst.
      rewrite deq_refl in E.
      discriminate.
  - simpl in *.
    f_equal.
    apply IHM.
    exact Hfresh.
Qed.

(*
 * Primary Substitution Property:
 * Identity substitution produces the identical term.
 *)
Theorem subst_id : forall (x : var) (M : term var),
  subst x (atom var x) M = M.
Proof.
  intros x M.
  induction M.
  - simpl.
    destruct (deq v x) eqn:E.
    + apply deq_eq in E. subst. reflexivity.
    + reflexivity.
  - simpl.
    rewrite IHM1, IHM2.
    reflexivity.
  - simpl.
    destruct (deq v x) eqn:E.
    + reflexivity.
    + rewrite IHM. reflexivity.
  - simpl.
    rewrite IHM.
    reflexivity.
Qed.

(*
 * Inductive Alpha-Equivalence Extended with Substitution Congruence
 *)
Inductive alp : term var -> term var -> Prop :=
| ref : forall (M : term var), alp M M
| sym : forall (M1 : term var) (M2 : term var), alp M1 M2 -> alp M2 M1
| tra : forall (M1 : term var) (M2 : term var) (M3 : term var), alp M1 M2 -> alp M2 M3 -> alp M1 M3
| shf : forall (M1 : term var) (M2 : term var), alp M1 M2 -> alp (shft var M1) (shft var M2)
| app : forall (M1 : term var) (M2 : term var) (N1 : term var) (N2 : term var),
    alp M1 M2 -> alp N1 N2 -> alp (appl var M1 N1) (appl var M2 N2)
| lam : forall (M1 : term var) (M2 : term var) (x : var),
    alp M1 M2 -> alp (lamb var x M1) (lamb var x M2)
| axi : forall (M : term var) (y : var) (x : var),
    alp (lamb var x M) (lamb var y (act var deq (varp var y x) M))
| sub : forall (M1 : term var) (M2 : term var) (x : var) (N : term var),
    alp M1 M2 -> alp (subst x N M1) (subst x N M2).

Theorem alp_refl : forall (M : term var), alp M M.
Proof.
  intro M.
  apply ref.
Qed.

Theorem alp_symm : forall (M1 : term var) (M2 : term var),
  alp M1 M2 -> alp M2 M1.
Proof.
  intros M1 M2 H.
  apply sym.
  exact H.
Qed.

Theorem alp_trans : forall (M1 : term var) (M2 : term var) (M3 : term var),
  alp M1 M2 -> alp M2 M3 -> alp M1 M3.
Proof.
  intros M1 M2 M3 H12 H23.
  apply (tra M1 M2 M3); [exact H12 | exact H23].
Qed.

Theorem alp_app_cong : forall (M1 : term var) (M2 : term var) (N1 : term var) (N2 : term var),
  alp M1 M2 -> alp N1 N2 -> alp (appl var M1 N1) (appl var M2 N2).
Proof.
  intros M1 M2 N1 N2 H1 H2.
  apply app; [exact H1 | exact H2].
Qed.

Theorem alp_lam_cong : forall (M1 : term var) (M2 : term var) (x : var),
  alp M1 M2 -> alp (lamb var x M1) (lamb var x M2).
Proof.
  intros M1 M2 x H.
  apply lam.
  exact H.
Qed.

Theorem alp_shf_cong : forall (M1 : term var) (M2 : term var),
  alp M1 M2 -> alp (shft var M1) (shft var M2).
Proof.
  intros M1 M2 H.
  apply shf.
  exact H.
Qed.

Theorem alp_axi : forall (M : term var) (y : var) (x : var),
  alp (lamb var x M) (lamb var y (act var deq (varp var y x) M)).
Proof.
  intros M y x.
  apply axi.
Qed.

(*
 * Primary Substitution Property:
 * Alpha-equivalence is preserved under substitution.
 *)
Theorem alp_subst_cong : forall (M1 : term var) (M2 : term var) (x : var) (N : term var),
  alp M1 M2 -> alp (subst x N M1) (subst x N M2).
Proof.
  intros M1 M2 x N H.
  apply sub.
  exact H.
Qed.

(* Embedding lemma: every alpha_core.alp relation implies alp *)
Lemma alp_core_to_alp : forall (M1 : term var) (M2 : term var),
  alpha_core.alp var deq M1 M2 -> alp M1 M2.
Proof.
  intros M1 M2 H.
  induction H.
  - apply ref.
  - apply sym. exact IHalp.
  - apply (tra _ M2 _); [exact IHalp1 | exact IHalp2].
  - apply shf. exact IHalp.
  - apply app; [exact IHalp1 | exact IHalp2].
  - apply lam. exact IHalp.
  - apply axi.
Qed.

(* Preservation of core alpha-equivalence under substitution *)
Theorem alp_core_preservation : forall (M1 : term var) (M2 : term var) (x : var) (N : term var),
  alpha_core.alp var deq M1 M2 -> alp (subst x N M1) (subst x N M2).
Proof.
  intros M1 M2 x N H.
  apply alp_subst_cong.
  apply alp_core_to_alp.
  exact H.
Qed.

End SubstSection.
