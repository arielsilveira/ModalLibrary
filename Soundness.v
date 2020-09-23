Require Import Modal_Library Classical List Deductive_System.

(* p -> (q -> p) *)
Lemma Hilbert_Axiom_1_soundness:
  forall M w φ ψ,
  M ' w ||- φ .-> (ψ .-> φ).
Proof.
  simpl; intros.
  assumption.
Qed.

(* (p -> (q -> r)) -> ((p -> q) -> (p -> r)) *)
Lemma Hilbert_Axiom_2_soundness:
  forall M w φ ψ Ɣ,
  M ' w ||- (φ .-> (ψ .-> Ɣ)) .-> ((φ .-> ψ) .-> (φ .-> Ɣ)).
Proof.
  simpl; intros.
  apply H.
  - auto.
  - apply H0; auto.
Qed.

(* (~ q -> ~ p) -> (p -> q) *)
Lemma Hilbert_Axiom_3_soundness:
  forall M w φ ψ,
  M ' w ||- (.~ ψ .-> .~ φ) .-> (φ .-> ψ).
Proof.
  simpl; intros.
  pose (classic (M ' w ||- ψ)) as Hip.
  destruct Hip.
  - auto.
  - apply H in H1.
    contradiction.
Qed.

(* p -> (q -> (p /\ q)) *)
Lemma Hilbert_Axiom_4_soundness: 
  forall M w φ ψ,
  M ' w ||- φ .-> (ψ .-> (φ ./\ ψ)).
Proof.
  simpl; intros.
  split; auto.
Qed.

(* (p /\ q) -> p *)
Lemma Hilbert_Axiom_5_soundness: 
  forall M w φ ψ,
  M ' w ||- (φ ./\ ψ) .-> φ.
Proof.
  simpl; intros.
  destruct H as [Hip1 Hip2].
  assumption.
Qed.

(* (p /\ q) -> q *)
Lemma Hilbert_Axiom_6_soundness: 
  forall M w φ ψ,
  M ' w ||- (φ ./\ ψ) .-> ψ.
Proof.
  simpl; intros.
  destruct H as [Hip1 Hip2].
  assumption.
Qed.

(* p -> (p \/ q) *)
Lemma Hilbert_Axiom_7_soundness: 
  forall M w φ ψ,
  M ' w ||- (φ .-> (φ .\/ ψ)).
Proof.
  simpl; intros.
  left.
  assumption.
Qed.

(* q -> (p \/ q) *)
Lemma Hilbert_Axiom_8_soundness: 
  forall M w φ ψ,
  M ' w ||- (ψ .-> (φ .\/ ψ)).
Proof.
  simpl; intros.
  right.
  assumption.
Qed.

(* (p -> r) -> (q -> r) -> (p \/ q) -> r *)
Lemma Hilbert_Axiom_9_soundness: 
  forall M w φ ψ Ɣ,
  M ' w ||- (φ .-> Ɣ) .-> (ψ .-> Ɣ) .-> (φ .\/ ψ) .-> Ɣ.
Proof.
  simpl; intros.
  destruct H1.
  - apply H.
    assumption.
  - apply H0.
    assumption.
Qed.

(* ~~p -> p *)
Lemma Hilbert_Axiom_10_soundness: 
  forall M w φ,
  M ' w ||- .~.~φ .-> φ.
Proof.
  simpl; intros.
  apply NNPP in H.
  assumption.
Qed.

(* <>(p \/ q) -> (<>p \/ <>q) *)
Lemma Axiom_Possibility_soundness:
  forall M w φ ψ,
  M ' w ||- .<> (φ .\/ ψ) .-> (.<> φ .\/ .<> ψ).
Proof.
  simpl; intros.
  destruct H as [ w' [ Hip1 [ Hip2 | Hip3 ] ]].
  - left; exists w'; split.
    + assumption.
    + assumption.
  - right; exists w'; split.
    + assumption.
    + assumption.
Qed.

(* [](p -> q) -> ([]p -> []q) *)
Lemma Axiom_K_soundness:
  forall M w φ ψ,
  M ' w ||- .[](φ .-> ψ) .-> (.[]φ .-> .[]ψ).
Proof.
  simpl; intros.
  apply H.
  - assumption.
  - apply H0.
    assumption.
Qed.

(* φ ∈ Γ -> Γ ||= φ  *)
Lemma case_two :
  forall Γ φ,
  In φ Γ -> 
  Γ ||= φ.
Proof.
  unfold entails_modal, validate_model; intros.
  apply exact_deduction with Γ.
  - assumption.
  - assumption.
Qed.

(* a /\ (a -> b) -> b *)
Lemma Modus_Ponens_soundness:
  forall M w φ ψ,
  ((M ' w ||- φ) /\ 
  (M ' w ||- φ .-> ψ)) -> 
  (M ' w ||- ψ).
Proof.
  simpl; intros.
  destruct H.
  apply H0; auto.
Qed.

Lemma Necessitation_soundness:
  forall M φ,
  (M |= φ) -> 
  (M |= .[]φ).
Proof.
  unfold validate_model; simpl; intros.
  apply H.
Qed.

Theorem soundness:
  forall (G: theory) (φ: modalFormula),
  (K; G |-- φ) -> 
  (G ||= φ).
Proof.
  induction 1.
  - intros M ?H.
    apply exact_deduction with t.
    + apply nth_error_In with i.
      assumption.
    + assumption.
  - destruct H; destruct H0; simpl.
    + intros M ?H w.
      apply Hilbert_Axiom_1_soundness.
    + intros M ?H w.
      apply Hilbert_Axiom_2_soundness.
    + intros M ?H w.
      apply Hilbert_Axiom_3_soundness.
    + intros M ?H w.
      apply Hilbert_Axiom_4_soundness.
    + intros M ?H w.
      apply Hilbert_Axiom_5_soundness.
    + intros M ?H w.
      apply Hilbert_Axiom_6_soundness.
    + intros M ?H w.
      apply Hilbert_Axiom_7_soundness.
    + intros M ?H w.
      apply Hilbert_Axiom_8_soundness.
    + intros M ?H w.
      apply Hilbert_Axiom_9_soundness.
    + intros M ?H w.
      apply Hilbert_Axiom_10_soundness.
    + intros M ?H w.
      apply Axiom_K_soundness.
    + intros M ?H w.
      apply Axiom_Possibility_soundness.
  - intros M ?H w.
    apply Modus_Ponens_soundness with f.
    split.
    + apply IHdeduction2.
      assumption.
    + apply IHdeduction1.
      assumption.
  - intros M ?H w.
    apply Necessitation_soundness.
    apply IHdeduction.
    assumption.
Qed.

Corollary soundness2:
  forall M G w φ, 
  theoryModal M G -> 
  (K; G |-- φ) -> M ' w ||- φ.
Proof.
  intros.
  eapply soundness.
  - eassumption.
  - assumption.
Qed.