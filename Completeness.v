Require Import Modal_Library Deductive_System List ClassicalFacts Classical FSetInterface Utf8 MSetInterface.

Definition Consistency (A: axiom -> Prop) (Γ : theory) : Prop := 
  forall (φ : modalFormula),
  ~ (A; Γ |-- φ ./\ .~φ).

Definition Maximal_Consistency (A: axiom -> Prop) (Γ : theory) : Prop :=
  forall (φ: modalFormula),
  ~(In φ Γ /\  In .~ φ Γ) /\ Consistency A Γ.

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

Inductive Lindenbaum_set (A: axiom -> Prop): nat -> theory -> Prop :=
  | Lindenbaum_zero:
    Lindenbaum_set A 0 Γ
  | Lindenbaum_succ1:
    forall n Δ,
    Lindenbaum_set A n Δ ->
    Consistency A (P n :: Δ) ->
    Lindenbaum_set A (S n) (P n :: Δ)
  | Lindenbaum_succ2:
    forall n Δ,
    Lindenbaum_set A n Δ ->
    ~Consistency A (P n :: Δ) ->
    Lindenbaum_set A (S n) Δ.

Lemma construct_set:
  forall A n,
  exists Δ, 
  Lindenbaum_set A n Δ.
Proof.
  intros; induction n.
  - exists Γ.
    constructor.
  - destruct IHn as (Δ, ?H). 
    edestruct classic with (Consistency A (P n :: Δ)).
    + eexists.
      apply Lindenbaum_succ1; eauto.
    + eexists.
      apply Lindenbaum_succ2; eauto.
Qed.

Lemma Lindenbaum_subset:
  forall A n Δ,
  Lindenbaum_set A n Δ -> 
  subset Γ Δ.
Proof.
  unfold subset; intros.
  induction H.
  - assumption.
  - intuition.
  - assumption.
Qed.

Lemma lema_3:
  forall A Gamma Delta n,
  Lindenbaum_set A n Delta /\
  subset Gamma Delta ->
  Lindenbaum_set A n Gamma.
Proof.
  admit.  
Admitted.


Lemma lema_9:
  forall A Δ n phi,
  Lindenbaum_set A n Δ ->
  (Consistency A (phi::Δ) ->
  In phi Δ).
Proof.
  admit.
Admitted.
 
End Lindebaum.



Lemma Lindenbaum:
  forall A (Γ : theory),
  Consistency A Γ -> 
  exists (Δ : theory), 
  (Maximal_Consistency A Δ /\ subset Γ Δ).
Proof.
  intros. exists Γ. split.
  - unfold Maximal_Consistency; intros.
    split.
    + admit.
    + assumption.
  - admit. 
Admitted.