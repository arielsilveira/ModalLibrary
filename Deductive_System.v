Require Import Modal_Library List.


(**** HILBERT SYSTEM (axiomatic method) ****)

Inductive axiom : Set :=
    | ax1 : formulaModal -> formulaModal -> axiom
    | ax2 : formulaModal -> formulaModal -> formulaModal -> axiom
    | ax3 : formulaModal -> formulaModal -> axiom
    | K   : formulaModal -> formulaModal -> axiom
.

Fixpoint instantiate (a:axiom) : formulaModal :=
    match a with
    | ax1 p1 p2       => p1 .-> (p2 .-> p1)
    | ax2 p1 p2 p3    => (p1 .-> (p2 .-> p3)) .-> ((p1 .-> p2) .-> (p1 .-> p3))
    | ax3 p1 p2       => (.~ p2 .-> .~ p1) .-> (p1 .-> p2)
    | K   p1 p2       => .[] (p1 .-> p2) .-> (.[] p1 .-> .[] p2)
    end.

(* Tentar entender isso *)
Inductive deduction : theory -> formulaModal -> Set :=
    | Prem : forall (t:theory) (f:formulaModal) (i:nat), (nth_error t i = Some f) -> deduction t f
    | Ax   : forall (t:theory) (f:formulaModal) (a:axiom), (instantiate a = f) -> deduction t f
    | Mp   : forall (t:theory) (f g:formulaModal) (d1:deduction t (f .-> g)) (d2:deduction t f), deduction t g
    | Nec  : forall (t:theory) (f g:formulaModal) (d1:deduction t f) , deduction t (.[] f)
.



Definition th1 := (#0 :: #0 .-> #1 :: nil). 
Definition ded1 := (Prem th1        #0 0 eq_refl).
Definition ded2 := (Prem th1 (#0.->#1) 1 eq_refl).
Definition ded3 := (Mp   th1 #0 #1 ded2 ded1).
Check ded3.
Definition ded4 := (Ax th1 (#1 .-> #2 .-> #1) (ax1 #1 #2) eq_refl).
Definition ded5 := (Prem th1        #0 0 eq_refl).
Definition ded6 := (Nec th1  #0).
Check ded6.