Require Import Modal_Library List Classical.

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


Inductive deduction : theory -> modalFormula -> Prop :=
    | Prem      : forall (t:theory) (f:   modalFormula) (i:nat), (nth_error t i = Some f) -> deduction t f
    | Ax        : forall (t:theory) (f:   modalFormula) (a:axiom), (instantiate a = f) -> deduction t f
    | Mp        : forall (t:theory) (f g: modalFormula) (d1:deduction t (f .-> g)) (d2:deduction t f), deduction t g
    | Nec       : forall (t:theory) (f:   modalFormula) (d1:deduction t f), deduction t (.[] f)
.

Inductive deduction_T : theory -> modalFormula -> Prop :=
    | Prem_T      : forall (t:theory) (f:   modalFormula) (i:nat), (nth_error t i = Some f) -> deduction_T t f
    | _Ax_T       : forall (t:theory) (f:   modalFormula) (a:axiom), (instantiate a = f) -> deduction_T t f
    | Ax_T        : forall (t:theory) (f:   modalFormula) (a:axiom_T), (instantiate_T a = f) -> deduction_T t f
    | Mp_T        : forall (t:theory) (f g: modalFormula) (d1:deduction_T t (f .-> g)) (d2:deduction_T t f), deduction_T t g
    | Nec_T       : forall (t:theory) (f:   modalFormula) (d1:deduction_T t f), deduction_T t (.[] f)
.

Inductive deduction_D : theory -> modalFormula -> Prop :=
    | Prem_D      : forall (t:theory) (f:   modalFormula) (i:nat),  (nth_error t i = Some f) -> deduction_D t f
    | _Ax_D       : forall (t:theory) (f:   modalFormula) (a:axiom), (instantiate a = f) -> deduction_D t f
    | Ax_D        : forall (t:theory) (f:   modalFormula) (a:axiom_D), (instantiate_D a = f) -> deduction_D t f
    | Mp_D        : forall (t:theory) (f g: modalFormula) (d1:deduction_D t (f .-> g)) (d2:deduction_D t f), deduction_D t g
    | Nec_D       : forall (t:theory) (f:   modalFormula) (d1:deduction_D t f), deduction_D t (.[] f)
.


Inductive deduction_Quatro : theory -> modalFormula -> Prop :=
    | Prem_Quatro      : forall (t:theory) (f:   modalFormula) (i:nat),  (nth_error t i = Some f) -> deduction_Quatro t f
    | _Ax_Quatro       : forall (t:theory) (f:   modalFormula) (a:axiom), (instantiate a = f) -> deduction_Quatro t f
    | Ax_Quatro        : forall (t:theory) (f:   modalFormula) (a:axiom_Quatro), (instantiate_Quatro a = f) -> deduction_Quatro t f
    | Mp_Quatro        : forall (t:theory) (f g: modalFormula) (d1:deduction_Quatro t (f .-> g)) (d2:deduction_Quatro t f), deduction_Quatro t g
    | Nec_Quatro       : forall (t:theory) (f:   modalFormula) (d1:deduction_Quatro t f), deduction_Quatro t (.[] f)
.


Inductive deduction_Cinco : theory -> modalFormula -> Prop :=
    | Prem_Cinco      : forall (t:theory) (f:   modalFormula) (i:nat),  (nth_error t i = Some f) -> deduction_Cinco t f
    | _Ax_Cinco       : forall (t:theory) (f:   modalFormula) (a:axiom), (instantiate a = f) -> deduction_Cinco t f
    | Ax_Cinco        : forall (t:theory) (f:   modalFormula) (a:axiom_Cinco), (instantiate_Cinco a = f) -> deduction_Cinco t f
    | Mp_Cinco        : forall (t:theory) (f g: modalFormula) (d1:deduction_Cinco t (f .-> g)) (d2:deduction_Cinco t f), deduction_Cinco t g
    | Nec_Cinco       : forall (t:theory) (f:   modalFormula) (d1:deduction_Cinco t f), deduction_Cinco t (.[] f)
.

Inductive deduction_S45 : theory -> modalFormula -> Prop :=
    | Prem_S45      : forall (t:theory) (f:   modalFormula) (i:nat),  (nth_error t i = Some f) -> deduction_S45 t f
    | _Ax_S45       : forall (t:theory) (f:   modalFormula) (a:axiom), (instantiate a = f) -> deduction_S45 t f
    | Ax_S4         : forall (t:theory) (f:   modalFormula) (a:axiom_Quatro), (instantiate_Quatro a = f) -> deduction_S45 t f
    | Ax_S5         : forall (t:theory) (f:   modalFormula) (a:axiom_Cinco), (instantiate_Cinco a = f) -> deduction_S45 t f
    | Mp_S45        : forall (t:theory) (f g: modalFormula) (d1:deduction_S45 t (f .-> g)) (d2:deduction_S45 t f), deduction_S45 t g
    | Nec_S45       : forall (t:theory) (f:   modalFormula) (d1:deduction_S45 t f), deduction_S45 t (.[] f)
.

Inductive deduction_B : theory -> modalFormula -> Prop :=
    | Prem_B      : forall (t:theory) (f:   modalFormula) (i:nat),  (nth_error t i = Some f) -> deduction_B t f
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


(* Notations and Theorems *)

(* Conversar com Paulo exists d, d:deduction *)
Notation "G |-- A" := (deduction G A) 
    (at level 110, no associativity).


Compute (Exemplo_2 |-- (#1)).

Lemma derive_self :
    forall (a:modalFormula) (G:theory), 
    ( G |-- (a .-> a)).
Proof.
    intros.
    apply Mp with (f:= a.-> a .-> a).
    apply Mp with (f:= a .-> (a .-> a) .-> a).
    apply Ax with (a:= (ax2 a (a .-> a) a)). simpl. auto.
    apply Ax with (a:= (ax1 a (a .-> a))). simpl. auto.
    apply Ax with (a:= (ax1 a a)). simpl. auto.
Qed.

Lemma derive_refl : 
    forall (Gamma: theory) (phi: modalFormula),
    (phi :: Gamma) |-- phi.
Proof.
    intros.
    apply Prem with (i:=0).
    simpl.
    auto.
Qed.

(* Tem algo errado nesse Fixpoint, foi tirado do artigo da proposicional *)
(* 
Fixpoint addTheory (x a:modalFormula) (G:theory)
            (d1: deduction G a) : (deduction (x::G) a)  :=
match d1 with 
    | Prem _ f i d   => Prem (x::G) f (S i) d
    | Ax _ f a d     => Ax   (x::G) f a d
    | Mp _ f g d1 d2 => Mp   (x::G) f g (addTheory x (f .-> g) G d1) (addTheory x f G d2)
    | Nec _ f d1     => Nec  (x::G) f (addTheory x f G d1) 
end.  *)

Lemma derive_weakening_left :
    forall (H G: theory) (phi:modalFormula), 
    ( G |-- phi) -> ((H ++ G) |-- phi).
Proof.
Admitted.

Theorem deduction_theorem_hilbert :
    forall (Gamma: theory) (phi psi :modalFormula), 
    ((phi::Gamma) |-- psi) -> (Gamma |--(phi .-> psi)). 

Proof.
    intros. induction H.
        - subst. pose (Hip:= Prem Gamma (phi .-> f) i).
        apply Hip. induction i. clear Hip; simpl in *. auto. 
                    
Admitted.

Theorem deduction_theorem :
    forall (Gamma : theory) (phi psi: modalFormula),
    ((phi::Gamma) |-- psi) -> (Gamma |-- phi .-> psi) .
Proof.
Admitted.

Theorem derive_modus_ponens:
    forall (phi psi: modalFormula) (Gamma: theory),
    (phi::Gamma |-- psi) ->
    (Gamma |-- phi) ->
    (Gamma |-- psi).
Proof.
    intros. induction H0.
        - inversion H. subst.
            + subst. apply Prem with (i:=i0). 
                induction Gamma. simpl in *. inversion H. simpl in *. 
Admitted.

Theorem derive_double_neg:
    forall (Gamma: theory) (phi: modalFormula),
    (Gamma |-- phi) <-> (Gamma |-- .~ .~ phi) .
Proof.
Admitted.
