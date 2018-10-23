(*Definition var := nat.*)
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
(*Defined.*)
Abort.
