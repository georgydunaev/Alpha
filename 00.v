(*Definition var := nat.*)
Require Import Coq.Program.Tactics.
Require Import Coq.Program.Wf.
Require Import Omega.
Require Import Psatz. (* lia *)

Section var.
Context (var:Set) (deq:var->var->bool).
Inductive term :=
| atom :> var -> term
| appl : term -> term -> term
| lamb : var -> term -> term
| shft : term -> term
.

Inductive func :=
| varp : var -> var -> func
| subs : func -> var -> func
.

Fixpoint lent (t:term) : nat :=
match t with
 | atom x => 0
 | appl x x0 => (max (lent x) (lent x0))+1
 | lamb x x0 => (lent x0)+2
 | shft x => (lent x)+1
end
.

Fixpoint lenf (f:func) : nat :=
match f with
 | varp x x0 => 0
 | subs x x0 => (lenf x)+1
end
.

Fixpoint act (f:func) (t:term) {struct t} : term.
destruct t as [v|M N|x M|M].
+ destruct f as [y x|F x].
  - exact (if (deq v x) then y else (shft v)). (* {yx}(x)=y *)
  - exact (if (deq v x) then v else (shft (act F v))). (* F_x(x)=x *)
+ exact (appl (act f M) (act f N)).
+ exact (lamb x (act (subs f x) M)).
+ destruct f as [y x|F x].
  - exact (shft M).
  - exact (shft (act F M)).
Show Proof.
Abort.

Program Fixpoint act (t : term) (f : func) {measure ((lenf f)+(lent t))} : term :=
   match t with
   | atom v =>
       match f with
       | varp y x => if deq v x then atom y else shft x
       | subs F x => if deq v x then atom v else shft (act v F)
       end
   | appl M N => appl (act M f) (act N f)
   | lamb x M => lamb x (act M (subs f x))
   | shft M =>
       match f with
       | varp _ _ => shft M
       | subs F _ => shft (act M F)
       end
   end
(*with actx (t : term) (f : func) {struct t} :=true*)
.

Next Obligation.
simpl. omega.
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
simpl. omega.
Defined.
Next Obligation.
simpl.
omega.
Defined.

Inductive alp : term -> term -> Prop :=
| ref : forall M, alp M M
| sym : forall M1 M2, alp M1 M2 -> alp M2 M1
| tra : forall M1 M2 M3, alp M1 M2 -> alp M2 M3 -> alp M1 M3
| shf : forall M1 M2, alp M1 M2 -> alp (shft M1) (shft M2)
| app : forall M1 M2 N1 N2, alp M1 M2 -> alp N1 N2 -> 
          alp (appl M1 N1) (appl M2 N2)
| lam : forall M1 M2 x, alp M1 M2 -> alp (lamb x M1 ) (lamb x M2)
| axi : forall M y x, alp (lamb x M ) (lamb y (act M (varp y x)) )
.


End var.
(*
Context (x y:var) (H: deq x y = false).
Compute (act (lamb x (lamb y x)) (varp y x)).
*)
Definition x:=0.
Definition y:=1.
(*Compute (act (lamb x (lamb y x)) (varp y x)).*)
(* DO NOT RUN IT:
Check (lamb nat y (atom _ x)).
Compute (act _ _ (lamb _ x (lamb _ y (atom _ x))) 
).
(varp nat y x)
*)

