Require Import Modal_Library Deductive_System List ClassicalFacts Classical FSetInterface Utf8 MSetInterface.

Definition Consistency (A: axiom -> Prop) (Γ : theory) : Prop := 
  forall (φ : modalFormula),
  ~ (A; Γ |-- φ ./\ .~φ).

Definition Maximal_Consistency (A: axiom -> Prop) (Γ : theory) : Prop :=
  forall (φ: modalFormula),
  (In φ Γ \/ In .~ φ Γ) /\  (Consistency A Γ).


(* Interpretação intuicionista de subconjunto *)


Notation "A ⊆ B" := (subset A B)
    (at level 70, no associativity) : type_scope.


Lemma lema_1 :
  forall A Δ Γ,
  (Consistency A Δ /\ subset Γ Δ) -> 
  Consistency A Γ.
Proof.
  intros.
  destruct H.
  unfold Consistency, not in *; intros.
  eapply H;
  eapply derive_weak.
  exact H0.
  exact H1.
Qed.

Section Lindebaum.

Variable P: nat -> modalFormula.
Variable Γ: theory.

Inductive Lindebaum_set (A: axiom -> Prop): nat -> theory -> Prop :=
  | Lindebaum_zero:
    Lindebaum_set A 0 Γ
  | Lindebaum_succ1:
    forall n Δ,
    Lindebaum_set A n Δ ->
    Consistency A (P n :: Δ) ->
    Lindebaum_set A (S n) (P n :: Δ)
  | Lindebaum_succ2:
    forall n Δ,
    Lindebaum_set A n Δ ->
    ~Consistency A (P n :: Δ) ->
    Lindebaum_set A (S n) Δ.

Lemma construct_set:
  forall (A: axiom -> Prop) n,
  exists Δ, Lindebaum_set A n Δ.
Proof.
  intros.
  induction n.
  - exists Γ.
    constructor.
  - destruct IHn as (Δ, ?H).
    edestruct classic with (Consistency A (P n :: Δ)).
    + eexists.
      apply Lindebaum_succ1; eauto.
    + eexists.
      apply Lindebaum_succ2; eauto.
Qed.

Lemma Lindebaum_subset:
  forall A n Δ,
  Lindebaum_set A n Δ -> subset Γ Δ.
Proof.
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

Lemma lema_4: 
    forall (W Γ Γ' : theory) (R : list (theory * theory)) (φ : modalFormula),
        (canonical_relation R Γ Γ') -> ((In (.[] φ) Γ) -> (In φ Γ')).
Proof.
Admitted.
