Require Import Modal_Library List.

(**** HILBERT SYSTEM (axiomatic method) ****)

Inductive axiom : Set :=
    | ax1 : modalFormula -> modalFormula -> axiom
    | ax2 : modalFormula -> modalFormula -> modalFormula -> axiom
    | ax3 : modalFormula -> modalFormula -> axiom
    | ax4 : modalFormula -> modalFormula -> axiom
    | ax5 : modalFormula -> modalFormula -> axiom
    | ax6 : modalFormula -> modalFormula -> axiom
    | ax7 : modalFormula -> modalFormula -> axiom
    | ax8 : modalFormula -> modalFormula -> axiom
    | ax9 : modalFormula -> modalFormula -> modalFormula -> axiom
    | ax10 : modalFormula -> modalFormula -> axiom
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
    | ax1    φ   ψ       => φ .-> (ψ .-> φ)
    | ax2    φ   ψ   Ɣ   => (φ .-> (ψ .-> Ɣ)) .-> ((φ .-> ψ) .-> (φ .-> Ɣ))
    | ax3    φ   ψ       => (.~ ψ .-> .~ φ) .-> (φ .-> ψ)
    | ax4    φ   ψ       => φ .-> (ψ .-> (φ .\/ ψ))
    | ax5    φ   ψ       => (φ ./\ ψ) .-> φ
    | ax6    φ   ψ       => (φ ./\ ψ) .-> ψ
    | ax7    φ   ψ       => φ .-> (φ .\/ ψ)
    | ax8    φ   ψ       => ψ .-> (φ .\/ ψ)
    | ax9    φ   ψ   Ɣ   => (φ .-> Ɣ) .-> ((ψ .-> Ɣ) .-> ((φ .\/ ψ) .-> Ɣ))
    | ax10   φ   ψ       => .~ .~ φ .-> φ
    | K      φ   ψ       => .[] (φ .-> ψ) .-> (.[] φ .-> .[] ψ)
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
    | Prem      : forall (t:theory) (f:   modalFormula) (i:nat), (nth_error t i = Some f) -> deduction t f
    | Ax        : forall (t:theory) (f:   modalFormula) (a:axiom), (instantiate a = f) -> deduction t f
    | Mp        : forall (t:theory) (f g: modalFormula) (d1:deduction t (f .-> g)) (d2:deduction t f), deduction t g
    | Nec       : forall (t:theory) (f:   modalFormula) (d1:deduction t f), deduction t (.[] f)
.

Inductive deduction_T : theory -> modalFormula -> Set :=
    | Prem_T      : forall (t:theory) (f:   modalFormula) (i:nat), (nth_error t i = Some f) -> deduction_T t f
    | _Ax_T       : forall (t:theory) (f:   modalFormula) (a:axiom), (instantiate a = f) -> deduction_T t f
    | Ax_T        : forall (t:theory) (f:   modalFormula) (a:axiom_T), (instantiate_T a = f) -> deduction_T t f
    | Mp_T        : forall (t:theory) (f g: modalFormula) (d1:deduction_T t (f .-> g)) (d2:deduction_T t f), deduction_T t g
    | Nec_T       : forall (t:theory) (f:   modalFormula) (d1:deduction_T t f), deduction_T t (.[] f)
.


Inductive deduction_D : theory -> modalFormula -> Set :=
    | Prem_D      : forall (t:theory) (f:   modalFormula) (i:nat), deduction_D t f -> deduction_D t f
    | _Ax_D       : forall (t:theory) (f:   modalFormula) (a:axiom), (instantiate a = f) -> deduction_D t f
    | Ax_D        : forall (t:theory) (f:   modalFormula) (a:axiom_D), (instantiate_D a = f) -> deduction_D t f
    | Mp_D        : forall (t:theory) (f g: modalFormula) (d1:deduction_D t (f .-> g)) (d2:deduction_D t f), deduction_D t g
    | Nec_D       : forall (t:theory) (f:   modalFormula) (d1:deduction_D t f), deduction_D t (.[] f)
.


Inductive deduction_Quatro : theory -> modalFormula -> Set :=
    | Prem_Quatro      : forall (t:theory) (f:   modalFormula) (i:nat), deduction_Quatro t f -> deduction_Quatro t f
    | _Ax_Quatro       : forall (t:theory) (f:   modalFormula) (a:axiom), (instantiate a = f) -> deduction_Quatro t f
    | Ax_Quatro        : forall (t:theory) (f:   modalFormula) (a:axiom_Quatro), (instantiate_Quatro a = f) -> deduction_Quatro t f
    | Mp_Quatro        : forall (t:theory) (f g: modalFormula) (d1:deduction_Quatro t (f .-> g)) (d2:deduction_Quatro t f), deduction_Quatro t g
    | Nec_Quatro       : forall (t:theory) (f:   modalFormula) (d1:deduction_Quatro t f), deduction_Quatro t (.[] f)
.


Inductive deduction_Cinco : theory -> modalFormula -> Set :=
    | Prem_Cinco      : forall (t:theory) (f:   modalFormula) (i:nat), deduction_Cinco t f -> deduction_Cinco t f
    | _Ax_Cinco       : forall (t:theory) (f:   modalFormula) (a:axiom), (instantiate a = f) -> deduction_Cinco t f
    | Ax_Cinco        : forall (t:theory) (f:   modalFormula) (a:axiom_Cinco), (instantiate_Cinco a = f) -> deduction_Cinco t f
    | Mp_Cinco        : forall (t:theory) (f g: modalFormula) (d1:deduction_Cinco t (f .-> g)) (d2:deduction_Cinco t f), deduction_Cinco t g
    | Nec_Cinco       : forall (t:theory) (f:   modalFormula) (d1:deduction_Cinco t f), deduction_Cinco t (.[] f)
.

Inductive deduction_S45 : theory -> modalFormula -> Set :=
    | Prem_S45      : forall (t:theory) (f:   modalFormula) (i:nat), deduction_S45 t f -> deduction_S45 t f
    | _Ax_S45       : forall (t:theory) (f:   modalFormula) (a:axiom), (instantiate a = f) -> deduction_S45 t f
    | Ax_S4         : forall (t:theory) (f:   modalFormula) (a:axiom_Quatro), (instantiate_Quatro a = f) -> deduction_S45 t f
    | Ax_S5         : forall (t:theory) (f:   modalFormula) (a:axiom_Cinco), (instantiate_Cinco a = f) -> deduction_S45 t f
    | Mp_S45        : forall (t:theory) (f g: modalFormula) (d1:deduction_S45 t (f .-> g)) (d2:deduction_S45 t f), deduction_S45 t g
    | Nec_S45       : forall (t:theory) (f:   modalFormula) (d1:deduction_S45 t f), deduction_S45 t (.[] f)
.


Inductive deduction_B : theory -> modalFormula -> Set :=
    | Prem_B      : forall (t:theory) (f:   modalFormula) (i:nat), deduction_B t f -> deduction_B t f
    | _Ax_B       : forall (t:theory) (f:   modalFormula) (a:axiom), (instantiate a = f) -> deduction_B t f
    | Ax_B        : forall (t:theory) (f:   modalFormula) (a:axiom_B), (instantiate_B a = f) -> deduction_B t f
    | Mp_B        : forall (t:theory) (f g: modalFormula) (d1:deduction_B t (f .-> g)) (d2:deduction_B t f), deduction_B t g
    | Nec_B       : forall (t:theory) (f:   modalFormula) (d1:deduction_B t f), deduction_B t (.[] f)
.

Definition Exemplo_2 := (.[](#0 .-> #1) :: .[](#1 .-> #2) :: nil).
Definition ded1 := (Prem_T Exemplo_2 (.[](#0 .-> #1)) 0 eq_refl).
Definition ded2 := (Prem_T Exemplo_2 (.[](#1 .-> #2)) 1 eq_refl).
Definition ded3 := (_Ax_T Exemplo_2 (((#0 .-> (#1 .-> #2)) .-> ((#0 .-> #1) .-> (#0 .-> #2))) .-> ((#1 .-> #2) .-> ((#0 .-> (#1 .-> #2)) .-> ((#0 .-> #1) .-> (#0 .-> #2))))) (ax1 ((#0 .-> (#1 .-> #2)) .-> ((#0 .-> #1) .-> (#0 .-> #2))) (#1 .-> #2)) eq_refl).
Definition ded4 := (_Ax_T Exemplo_2 ((#0 .-> (#1 .-> #2)) .-> ((#0 .-> #1) .-> (#0 .-> #2))) (ax2 #0 #1 #2) eq_refl).
Definition ded5 := (Mp_T Exemplo_2 (((#0 .-> (#1 .-> #2)) .-> ((#0 .-> #1) .-> (#0 .-> #2)))) (((#1 .-> #2) .-> ((#0 .-> (#1 .-> #2)) .-> ((#0 .-> #1) .-> (#0 .-> #2))))) ded3 ded4 ).
Definition ded6 := (_Ax_T Exemplo_2 (((#1 .-> #2) .-> ((#0 .-> (#1 .-> #2)) .-> ((#0 .-> #1) .-> (#0 .-> #2)))) .-> (((#1 .-> #2) .-> (#0 .-> (#1 .-> #2))) .-> ((#1 .-> #2) .-> ((#0 .-> #1) .-> (#0 .-> #2))))) (ax2 (#1 .-> #2) (#0 .-> (#1 .-> #2)) ((#0 .-> #1) .-> (#0 .-> #2))) eq_refl).
Definition ded7 := (Mp_T Exemplo_2 (((#1 .-> #2) .-> ((#0 .-> (#1 .-> #2)) .-> ((#0 .-> #1) .-> (#0 .-> #2)))))   ((((#1 .-> #2) .-> (#0 .-> (#1 .-> #2))) .-> ((#1 .-> #2) .-> ((#0 .-> #1) .-> (#0 .-> #2))))) ded6 ded5).
Definition ded8 := (_Ax_T Exemplo_2 ((#1 .-> #2) .-> (#0 .-> (#1 .-> #2))) (ax1 (#1 .-> #2) #0) eq_refl).
Definition ded9 := (Mp_T Exemplo_2 ((#1 .-> #2) .-> (#0 .-> (#1 .-> #2))) ((#1 .-> #2) .-> ((#0 .-> #1) .-> (#0 .-> #2))) ded7 ded8).
Definition ded10 := (Ax_T Exemplo_2 (.[](#1 .-> #2) .-> (#1 .-> #2)) (T (#1 .-> #2)) eq_refl).
Definition ded11 := (Mp_T Exemplo_2 (.[](#1 .-> #2)) ((#1 .-> #2)) ded10 ded2).
Definition ded12 := (Ax_T Exemplo_2 (.[](#0 .-> #1) .-> (#0 .-> #1)) (T (#0 .-> #1)) eq_refl).
Definition ded13 := (Mp_T Exemplo_2 (.[](#0 .-> #1)) ((#0 .-> #1)) ded12 ded1).
Definition ded14 := (Mp_T Exemplo_2 ((#1 .-> #2)) ((#0 .-> #1) .-> (#0 .-> #2)) ded9 ded11).
Definition ded15 := (Mp_T Exemplo_2 ((#0 .-> #1)) ((#0 .-> #2)) ded14 ded13).
Definition ded16 := (Nec_T Exemplo_2 ((#0 .-> #2)) ded15).


Check ded16.
