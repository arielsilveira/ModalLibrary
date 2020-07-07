Require Import Modal_Library List.

(**** HILBERT SYSTEM (axiomatic method) ****)

Inductive axiom : Set :=
    | ax1 : formulaModal -> formulaModal -> axiom
    | ax2 : formulaModal -> formulaModal -> formulaModal -> axiom
    | ax3 : formulaModal -> formulaModal -> axiom
    | K   : formulaModal -> formulaModal -> axiom
.

Inductive axiom_frame : Set :=
    | T         : formulaModal -> axiom_frame
    | D         : formulaModal -> axiom_frame
    | Quatro    : formulaModal -> axiom_frame
    | Cinco     : formulaModal -> axiom_frame
    | B         : formulaModal -> axiom_frame
.

Fixpoint instantiate (a:axiom) : formulaModal :=
    match a with
    | ax1 p1 p2       => p1 .-> (p2 .-> p1)
    | ax2 p1 p2 p3    => (p1 .-> (p2 .-> p3)) .-> ((p1 .-> p2) .-> (p1 .-> p3))
    | ax3 p1 p2       => (.~ p2 .-> .~ p1) .-> (p1 .-> p2)
    | K   p1 p2       => .[] (p1 .-> p2) .-> (.[] p1 .-> .[] p2)
    end.

(* Fazer para o B, 4, 5, D,  *)
Fixpoint instantiate_frame (a: axiom_frame) : formulaModal :=
    match a with
    | D         p => .[] p .-> .<> p
    | T         p => .[] p .-> p
    | Quatro    p => .[] p .-> .[].[] p
    | Cinco     p => .<> p .-> .[].<> p
    | B         p => p .-> .[].<> p
    end. 

(* Tentar entender isso *)
Inductive deduction : theory -> formulaModal -> Set :=
    | Prem : forall (t:theory) (f:formulaModal) (i:nat), (nth_error t i = Some f) -> deduction t f
    | Ax   : forall (t:theory) (f:formulaModal) (a:axiom), (instantiate a = f) -> deduction t f
    | Ax_Frame : forall (t:theory) (f: formulaModal) (a:axiom_frame), (instantiate_frame a = f) -> deduction t f
    | Mp   : forall (t:theory) (f g:formulaModal) (d1:deduction t (f .-> g)) (d2:deduction t f), deduction t g
    | Nec  : forall (t:theory) (f:formulaModal) (d1:deduction t f) , deduction t (.[] f)
.

Definition Exemplo_2 := (.[](#0 .-> #1) :: .[](#1 .-> #2) :: nil).
Definition ded1 := (Prem Exemplo_2 (.[](#0 .-> #1)) 0 eq_refl).
Definition ded2 := (Prem Exemplo_2 (.[](#1 .-> #2)) 1 eq_refl).
Definition ded3 := (Ax Exemplo_2 (((#0 .-> (#1 .-> #2)) .-> ((#0 .-> #1) .-> (#0 .-> #2))) .-> ((#1 .-> #2) .-> ((#0 .-> (#1 .-> #2)) .-> ((#0 .-> #1) .-> (#0 .-> #2))))) (ax1 ((#0 .-> (#1 .-> #2)) .-> ((#0 .-> #1) .-> (#0 .-> #2))) (#1 .-> #2)) eq_refl).
Definition ded4 := (Ax Exemplo_2 ((#0 .-> (#1 .-> #2)) .-> ((#0 .-> #1) .-> (#0 .-> #2))) (ax2 #0 #1 #2) eq_refl).
Definition ded5 := (Mp Exemplo_2 (((#0 .-> (#1 .-> #2)) .-> ((#0 .-> #1) .-> (#0 .-> #2)))) (((#1 .-> #2) .-> ((#0 .-> (#1 .-> #2)) .-> ((#0 .-> #1) .-> (#0 .-> #2))))) ded3 ded4 ).
Definition ded6 := (Ax Exemplo_2 (((#1 .-> #2) .-> ((#0 .-> (#1 .-> #2)) .-> ((#0 .-> #1) .-> (#0 .-> #2)))) .-> (((#1 .-> #2) .-> (#0 .-> (#1 .-> #2))) .-> ((#1 .-> #2) .-> ((#0 .-> #1) .-> (#0 .-> #2))))) (ax2 (#1 .-> #2) (#0 .-> (#1 .-> #2)) ((#0 .-> #1) .-> (#0 .-> #2))) eq_refl).
Definition ded7 := (Mp Exemplo_2 (((#1 .-> #2) .-> ((#0 .-> (#1 .-> #2)) .-> ((#0 .-> #1) .-> (#0 .-> #2)))))   ((((#1 .-> #2) .-> (#0 .-> (#1 .-> #2))) .-> ((#1 .-> #2) .-> ((#0 .-> #1) .-> (#0 .-> #2))))) ded6 ded5).
Definition ded8 := (Ax Exemplo_2 ((#1 .-> #2) .-> (#0 .-> (#1 .-> #2))) (ax1 (#1 .-> #2) #0) eq_refl).
Definition ded9 := (Mp Exemplo_2 ((#1 .-> #2) .-> (#0 .-> (#1 .-> #2))) ((#1 .-> #2) .-> ((#0 .-> #1) .-> (#0 .-> #2))) ded7 ded8).
Definition ded10 := (Ax_Frame Exemplo_2 (.[](#1 .-> #2) .-> (#1 .-> #2)) (T (#1 .-> #2)) eq_refl).
Definition ded11 := (Mp Exemplo_2 (.[](#1 .-> #2)) ((#1 .-> #2)) ded10 ded2).
Definition ded12 := (Ax_Frame Exemplo_2 (.[](#0 .-> #1) .-> (#0 .-> #1)) (T (#0 .-> #1)) eq_refl).
Definition ded13 := (Mp Exemplo_2 (.[](#0 .-> #1)) ((#0 .-> #1)) ded12 ded1).
Definition ded14 := (Mp Exemplo_2 ((#1 .-> #2)) ((#0 .-> #1) .-> (#0 .-> #2)) ded9 ded11).
Definition ded15 := (Mp Exemplo_2 ((#0 .-> #1)) ((#0 .-> #2)) ded14 ded13).
Definition ded16 := (Nec Exemplo_2 ((#0 .-> #2)) ded15).


Check ded16.
