Require Import Modal_Library List.

(**** HILBERT SYSTEM (axiomatic method) ****)

Inductive axiom : Set :=
    | ax1 : formulaModal -> formulaModal -> axiom
    | ax2 : formulaModal -> formulaModal -> formulaModal -> axiom
    | ax3 : formulaModal -> formulaModal -> axiom
    | K   : formulaModal -> formulaModal -> axiom
.

Inductive axiom_T : Set :=
    | T : formulaModal -> axiom_T
.

Inductive axiom_D : Set :=
    | D : formulaModal -> axiom_D
.

Inductive axiom_Quatro : Set :=
    | Quatro : formulaModal -> axiom_Quatro
.

Inductive axiom_Cinco : Set :=
    | Cinco : formulaModal -> axiom_Cinco
.

Inductive axiom_B : Set :=
    | B : formulaModal -> axiom_B
.

Fixpoint instantiate (a:axiom) : formulaModal :=
    match a with
    | ax1 p1 p2       => p1 .-> (p2 .-> p1)
    | ax2 p1 p2 p3    => (p1 .-> (p2 .-> p3)) .-> ((p1 .-> p2) .-> (p1 .-> p3))
    | ax3 p1 p2       => (.~ p2 .-> .~ p1) .-> (p1 .-> p2)
    | K   p1 p2       => .[] (p1 .-> p2) .-> (.[] p1 .-> .[] p2)
    end.


Fixpoint instantiate_D (a: axiom_D) : formulaModal :=
    match a with
    | D         p => .[] p .-> .<> p
end. 

Fixpoint instantiate_T (a: axiom_T) : formulaModal :=
    match a with
    | T         p => .[] p .-> p
end. 

Fixpoint instantiate_Quatro (a: axiom_Quatro) : formulaModal :=
    match a with
    | Quatro    p => .[] p .-> .[].[] p
end. 

Fixpoint instantiate_Cinco (a: axiom_Cinco) : formulaModal :=
    match a with
    | Cinco     p => .<> p .-> .[].<> p
end. 

Fixpoint instantiate_B (a: axiom_B) : formulaModal :=
    match a with
    | B         p => p .-> .[].<> p
end. 


Inductive deduction : theory -> formulaModal -> Set :=
    | Prem      : forall (t:theory) (f:formulaModal) (i:nat), (nth_error t i = Some f) -> deduction t f
    | Ax        : forall (t:theory) (f:formulaModal) (a:axiom), (instantiate a = f) -> deduction t f
    | Ax_D      : forall (t:theory) (f: formulaModal) (a:axiom_D), (instantiate_D a = f) -> deduction t f
    | Ax_Quatro : forall (t:theory) (f: formulaModal) (a:axiom_Quatro), (instantiate_Quatro a = f) -> deduction t f
    | Ax_Cinco  : forall (t:theory) (f: formulaModal) (a:axiom_Cinco), (instantiate_Cinco a = f) -> deduction t f
    | Ax_B      : forall (t:theory) (f: formulaModal) (a:axiom_B), (instantiate_B a = f) -> deduction t f
    | Mp        : forall (t:theory) (f g:formulaModal) (d1:deduction t (f .-> g)) (d2:deduction t f), deduction t g
    | Nec       : forall (t:theory) (f:formulaModal) (d1:deduction t f) , deduction t (.[] f)
.

Inductive deduction_T : theory -> formulaModal -> Set :=
    | Prem      : forall (t:theory) (f:formulaModal) (i:nat), (nth_error t i = Some f) -> deduction_T t f
    | Ax_T      : forall (t:theory) (f: formulaModal) (a:axiom_T), (instantiate_T a = f) -> deduction_T t f
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
Definition ded10 := (Ax_T Exemplo_2 (.[](#1 .-> #2) .-> (#1 .-> #2)) (T (#1 .-> #2)) eq_refl).
Definition ded11 := (Mp Exemplo_2 (.[](#1 .-> #2)) ((#1 .-> #2)) ded10 ded2).
Definition ded12 := (Ax_T Exemplo_2 (.[](#0 .-> #1) .-> (#0 .-> #1)) (T (#0 .-> #1)) eq_refl).
Definition ded13 := (Mp Exemplo_2 (.[](#0 .-> #1)) ((#0 .-> #1)) ded12 ded1).
Definition ded14 := (Mp Exemplo_2 ((#1 .-> #2)) ((#0 .-> #1) .-> (#0 .-> #2)) ded9 ded11).
Definition ded15 := (Mp Exemplo_2 ((#0 .-> #1)) ((#0 .-> #2)) ded14 ded13).
Definition ded16 := (Nec Exemplo_2 ((#0 .-> #2)) ded15).


Check ded16.
