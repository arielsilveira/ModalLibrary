Require Import Modal_Library Tactics Logic List Classical FSetInterface.
Module Import WSfun.
Definition Consistency (Γ : theory) : Prop := 
    forall (M : Model) (φ : modalFormula), 
        ~ (M '' Γ |- φ ./\ .~ φ).

Print Consistency.

Definition Maximal_Consistency (Γ : theory) : Prop :=
    forall (φ : modalFormula), 
        (In φ Γ \/ In (.~φ) Γ) /\ Consistency Γ.

Print Maximal_Consistency.

(* Verificar direito isso = Paulo *)
Definition subset (Γ Δ : theory) : Prop :=
    forall (φ : modalFormula), In φ Γ -> In φ Δ.

Notation "A ⊆ B" := (subset A B)
    (at level 70, no associativity) : type_scope.

Lemma lema_1 :
    forall (Δ Γ : theory),
        ((Consistency Δ) /\ (subset Γ Δ)) -> Consistency Γ.
Proof.
    - unfold Consistency;
        unfold subset.
        unfold entails;
        unfold validate_model.
        intros. 
        unfold not in *.
        intros.
        destruct H as (?, H2). 
        apply H with (M:=M) (φ:=φ).
        split.
            + 

           
Admitted.

Lemma Lindenbaum:
    exists (Γ Δ : theory),
        Consistency Γ -> (Maximal_Consistency Δ /\ subset Γ Δ).
Proof.
    unfold Maximal_Consistency.    
    unfold Consistency.
    unfold subset.
    (* exists Γ. *)
    
    
    intros.
Admitted.

Lemma lema_3:
    forall (Δ Ⲧ: theory),
        Maximal_Consistency Δ -> Consistency Δ /\ (Consistency (Δ++Ⲧ) -> subset Ⲧ Δ).
Proof.
Admitted.

(* Trocar o lambda *)
Definition canonical_world (W : theory) : Prop :=
    forall (Ω : theory),
        (Maximal_Consistency W /\ subset Ω W) -> Maximal_Consistency Ω .

Definition canonical_relation (R : list (theory * theory)) (Γ Γ' : theory) : Prop := 
    forall (φ : modalFormula)  ,
        ((In (Γ, Γ') R) -> (In φ Γ' -> In (.<> φ) Γ)) .

Definition canonical_valuation (W : theory) : Prop :=
    forall (φ : modalFormula), exists (Γ : theory),
        (In φ Γ) -> subset Γ W.

Definition canonical_model (W : theory) (R : list (theory * theory)) : Prop :=
    forall (Γ Γ' : theory),
        (canonical_world W) /\
        (subset Γ W /\ subset Γ' W) /\
        canonical_relation R Γ Γ'  /\
        canonical_valuation W
        .

Lemma lema_4: 
    forall (W Γ Γ' : theory) (R : list (theory * theory)) (φ : modalFormula),
        (canonical_relation R Γ Γ') -> ((In (.[] φ) Γ) -> (In φ Γ')).
Proof.
    unfold canonical_relation;
    simpl. intros.
    
    
    
    
Admitted.


(* Definir um modelo canônico *)

(* Lemma lema_5 - Rever *)

(* Lemma lema_6 - Rever *)
