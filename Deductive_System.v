Require Import Modal_Library List.

(**** HILBERT SYSTEM (axiomatic method) ****)

Inductive axiom : Set :=
    | ax1 : modalFormula -> modalFormula -> axiom
    | ax2 : modalFormula -> modalFormula -> modalFormula -> axiom
    | ax3 : modalFormula -> modalFormula -> axiom
    | K   : modalFormula -> modalFormula -> axiom
.

Inductive axiom_T : Set :=
    | T : modalFormula -> axiom_T
.

Inductive axiom_D : Set :=
    | D : modalFormula -> axiom_D
.

Inductive axiom_Quatro : Set :=
    | Quatro : modalFormula -> axiom_Quatro
.

Inductive axiom_Cinco : Set :=
    | Cinco : modalFormula -> axiom_Cinco
.

Inductive axiom_B : Set :=
    | B : modalFormula -> axiom_B
.

Fixpoint instantiate (a : axiom) : modalFormula :=
    match a with
    | ax1  φ   ψ         => φ .-> (ψ .-> φ)
    | ax2  φ   ψ   Ɣ     => (φ .-> (ψ .-> Ɣ)) .-> ((φ .-> ψ) .-> (φ .-> Ɣ))
    | ax3  φ   ψ         => (.~ ψ .-> .~ φ) .-> (φ .-> ψ)
    | K    φ   ψ         => .[] (φ .-> ψ) .-> (.[] φ .-> .[] ψ)
    end.


Fixpoint instantiate_D (a: axiom_D) : modalFormula :=
    match a with
    | D         φ => .[] φ .-> .<> φ
end. 

Fixpoint instantiate_T (a: axiom_T) : modalFormula :=
    match a with
    | T         φ => .[] φ .-> φ
end. 

Fixpoint instantiate_Quatro (a: axiom_Quatro) : modalFormula :=
    match a with
    | Quatro    φ => .[] φ .-> .[].[] φ
end. 

Fixpoint instantiate_Cinco (a: axiom_Cinco) : modalFormula :=
    match a with
    | Cinco     φ => .<> φ .-> .[].<> φ
end. 

Fixpoint instantiate_B (a: axiom_B) : modalFormula :=
    match a with
    | B         φ => φ .-> .[].<> φ
end. 


Inductive deduction : theory -> modalFormula -> Set :=
    | Prem      : forall (t:theory) (f:modalFormula) (i:nat), (nth_error t i = Some f) -> deduction t f
    | Ax        : forall (t:theory) (f:modalFormula) (a:axiom), (instantiate a = f) -> deduction t f
    | Ax_T      : forall (t:theory) (f: modalFormula) (a:axiom_T), (instantiate_T a = f) -> deduction t f
    | Ax_D      : forall (t:theory) (f: modalFormula) (a:axiom_D), (instantiate_D a = f) -> deduction t f
    | Ax_Quatro : forall (t:theory) (f: modalFormula) (a:axiom_Quatro), (instantiate_Quatro a = f) -> deduction t f
    | Ax_Cinco  : forall (t:theory) (f: modalFormula) (a:axiom_Cinco), (instantiate_Cinco a = f) -> deduction t f
    | Ax_B      : forall (t:theory) (f: modalFormula) (a:axiom_B), (instantiate_B a = f) -> deduction t f
    | Mp        : forall (t:theory) (f g:modalFormula) (d1:deduction t (f .-> g)) (d2:deduction t f), deduction t g
    | Nec       : forall (t:theory) (f:modalFormula) (d1:deduction t f) , deduction t (.[] f)
.

(* Inductive deduction_T : theory -> modalFormula -> Set :=
    | Prem      : forall (t:theory) (f:modalFormula) (i:nat), (nth_error t i = Some f) -> deduction_T t f
    | Ax_T      : forall (t:theory) (f: modalFormula) (a:axiom_T), (instantiate_T a = f) -> deduction_T t f
. *)


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
