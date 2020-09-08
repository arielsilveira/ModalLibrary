Require Import Modal_Library   List Classical FSetInterface Utf8 MSetInterface.
(* Logic *)
Definition Consistency (Γ : theory) : Prop := 
    forall (M : Model) (φ : modalFormula), 
        ~ (M '' Γ |- φ ./\ .~ φ).

Print Consistency.

Definition Maximal_Consistency (Γ : theory) : Prop :=
    forall (φ : modalFormula), 
        (In φ Γ \/ In (.~φ) Γ) /\ Consistency Γ.

Print Maximal_Consistency.

(* Interpretação intuicionista de subconjunto *)
Definition subset (Γ Δ : theory) : Prop :=
    forall (φ : modalFormula), In φ Γ -> In φ Δ.


Notation "A ⊆ B" := (subset A B)
    (at level 70, no associativity) : type_scope.

(* Lemma t: 
    forall (G D : theory) (φ: modalFormula),
    (~ (Consistency G) /\ subset G D) -> ~ Consistency D.
Proof.
    intros; destruct H as (?, ?).
    unfold Consistency in *; unfold not in *.
    intros. apply H. intros.
    edestruct H1 with (M:=M) (φ:=φ0).
    eapply H0.
    (* unfold entails in *. intros. *)
    apply H2.
    destruct H1 with (w:=w).
    
Qed. *)


Lemma t2:
  forall (Δ Γ : theory) (M: Model) (phi : modalFormula),
  (M '' Γ++Δ |- phi) /\ subset Γ Δ -> (M '' Δ |- phi).
Proof.
  intros.
  unfold entails in *. (*split.*)
  intros.
  destruct H. apply H.
  edestruct classic.
    + exact H2.
          
Admitted.


Lemma t:
  forall (Δ Γ : theory) (M: Model) (phi : modalFormula),
    ((M '' Γ |- phi) /\ (subset Γ Δ)) -> (M '' Δ |- phi).
Proof.
  - intros. destruct H as (?, ?).
  apply monotonicity with (ẟ:=Δ) in H .
  (* apply t2 in H; eauto. *)
Admitted.


Lemma lema_1 :
    forall (Δ Γ : theory),
    ((Consistency Δ) /\ (subset Γ Δ)) -> Consistency Γ.
Proof.
    - intros.
        (* unfold not in *. intros. *)
        destruct H as (?, Subset).
        edestruct classic.
            + exact H0.
            + unfold Consistency in *. intros. unfold not in *.
              intros; eapply H with M φ.
              unfold entails in *. 
              unfold validate_model in *.
              intros. 
              
              destruct H1 with w.         
            assert(Hip: forall phi: modalFormula, In phi Γ -> In phi Δ -> subset Γ Δ).
              { eauto. }
            
            unfold Consistency in *.
                unfold not in *. 
Admitted.
                
Section Lindebaum.

Variable P: nat -> modalFormula.
Variable Γ: theory.

Inductive Lindebaum_set: nat -> theory -> Prop :=
  | Lindebaum_zero:
    Lindebaum_set 0 Γ
  | Lindebaum_succ1:
    forall n Δ,
    Lindebaum_set n Δ ->
    Consistency (P n :: Δ) ->
    Lindebaum_set (S n) (P n :: Δ)
  | Lindebaum_succ2:
    forall n Δ,
    Lindebaum_set n Δ ->
    ~Consistency (P n :: Δ) ->
    Lindebaum_set (S n) Δ.

Lemma construct_set:
  forall n,
  exists Δ, Lindebaum_set n Δ.
Proof.
  intros.
  induction n.
  - exists Γ.
    constructor.
  - destruct IHn as (Δ, ?H).
    edestruct classic with (Consistency (P n :: Δ)).
    + eexists.
      apply Lindebaum_succ1; eauto.
    + eexists.
      apply Lindebaum_succ2; eauto.
Qed.

Lemma Lindebaum_subset:
  forall n Δ,
  Lindebaum_set n Δ -> subset Γ Δ.
Proof.
  intros.
  induction n.
  - inversion_clear H.
    unfold subset; auto.
  - inversion_clear H.
    + 
      
      admit.
    + auto.
Admitted.

End Lindebaum.

Lemma Lindenbaum:
    forall (Γ : theory),
    Consistency Γ -> 
    exists (Δ : theory), 
    (Maximal_Consistency Δ /\ subset Γ Δ).
Proof.
    
Admitted.

Lemma lema_3:
    forall (Δ Ⲧ: theory),
    Maximal_Consistency Δ -> Consistency Δ /\ (Consistency (Δ++Ⲧ) -> subset Ⲧ Δ).
Proof.
Admitted.






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
