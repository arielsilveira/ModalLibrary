(*  Introduction

    Name: Ariel Agne da Silveira

    Advisor: Karina Girardi Roggia
    Co-Advisor: Paulo Torrens

    Minion: Miguel

    <Modal Logic Library>

    Description:
*)
Require Import Arith List ListSet Notations Utf8 Classical.

Inductive modalFormula : Set :=
    | Lit          : nat -> modalFormula
    | Neg          : modalFormula -> modalFormula
    | Box          : modalFormula -> modalFormula
    | Dia          : modalFormula -> modalFormula
    | And          : modalFormula -> modalFormula -> modalFormula
    | Or           : modalFormula -> modalFormula -> modalFormula
    | Implies      : modalFormula -> modalFormula -> modalFormula 
.

(* Calcula o tamanho de uma fórmula modal *)
Fixpoint modalSize (f:modalFormula) : nat :=
    match f with 
    | Lit      x     => 1
    | Neg      p1    => 1 + (modalSize p1)
    | Box      p1    => 1 + (modalSize p1)
    | Dia      p1    => 1 + (modalSize p1)
    | And      p1 p2 => 1 + (modalSize p1) + (modalSize p2)
    | Or       p1 p2 => 1 + (modalSize p1) + (modalSize p2)
    | Implies  p1 p2 => 1 + (modalSize p1) + (modalSize p2)
end.

Fixpoint literals (f:modalFormula) : set nat :=
    match f with 
    | Lit      x     => set_add eq_nat_dec x (empty_set nat)
    | Dia      p1    => literals p1
    | Box      p1    => literals p1
    | Neg      p1    => literals p1
    | And      p1 p2 => set_union eq_nat_dec (literals p1) (literals p2)
    | Or       p1 p2 => set_union eq_nat_dec (literals p1) (literals p2)
    | Implies  p1 p2 => set_union eq_nat_dec (literals p1) (literals p2) 
end.

(* -- New notation -- *)
Notation " φ .-> ψ "  := (Implies φ ψ) (at level 13, right associativity).
Notation " φ .\/ ψ "  := (Or φ ψ)      (at level 12, left associativity).
Notation " φ ./\ ψ "   := (And φ ψ)     (at level 11, left associativity).
Notation " .~ φ "     := (Neg φ)       (at level 9, right associativity).
Notation " .[] φ "    := (Box φ)       (at level 9, right associativity).
Notation " .<> φ "    := (Dia φ)       (at level 9, right associativity).
Notation " # φ "      := (Lit φ)       (at level 1, no associativity).


Notation " ☐ φ" := (.[] φ)
    (at level 1, φ at level 200, right associativity): type_scope.

Notation " ◇ φ" := (.<> φ)
    (at level 1, φ at level 200, right associativity): type_scope.

Notation " φ → ψ" := (φ .-> ψ)
    (at level 99, ψ at level 200, right associativity) : type_scope.


Notation " X ∈ Y " := (In X Y)
    (at level 250, no associativity) : type_scope.

Notation "[ ]" := nil.
Notation "x :: l" := (cons x l)
                     (at level 60, right associativity).
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).


Record Frame : Type :={
    W : Set;
    R : W -> W -> Prop;
}.

Record Model : Type := {
    F : Frame; 
    v : nat -> (W F) -> Prop; 
}.


Check Build_Frame.
Check Build_Model.


Fixpoint fun_validation (M: Model) (w: W (F M)) (φ: modalFormula): Prop :=
  match φ with
  | Lit     x      => v M x w 
  | Box     ψ      => forall w': W (F M), R (F M) w w' -> fun_validation M w' ψ
  | Dia     ψ      => exists w': W (F M), R (F M) w w' /\ fun_validation M w' ψ
  | Neg     ψ      => ~fun_validation M w ψ
  | And     ψ  Ɣ   => fun_validation M w ψ /\ fun_validation M w Ɣ
  | Or      ψ  Ɣ   => fun_validation M w ψ \/ fun_validation M w Ɣ
  | Implies ψ  Ɣ   => fun_validation M w ψ -> fun_validation M w Ɣ
  end.

(* World Satisfaziblity *)
Notation "M ' w ||- φ" := (fun_validation M w φ)
  (at level 110, only parsing, right associativity).
Notation "M ☯ w ╟ φ  " := (fun_validation M w φ)
  (at level 110, only printing, right associativity).

(* Model satisfazibility *)
Definition validate_model (M: Model) (φ: modalFormula): Prop :=
  forall w: W (F M), fun_validation M w φ.

Notation "M |= φ" := (validate_model M φ)
  (at level 110, only parsing, right associativity).
Notation "M ╞ φ " := (validate_model M φ)
  (at level 110, only printing, right associativity).

(******  Finite theories and entailment ******)

Definition theory := list modalFormula.

Fixpoint theoryModal (M: Model) (Γ: theory): Prop :=
  match Γ with
  | nil => True
  | h :: t => (validate_model M h) /\ (theoryModal M t)
  end.

Definition entails (M: Model) (Γ: theory) (φ: modalFormula): Prop :=
  theoryModal M Γ -> validate_model M φ.

Notation "M '' Γ |- φ" := (entails M Γ φ)
  (at level 110, only parsing, no associativity).
Notation "M ♥ Γ ├ φ  " := (entails M Γ φ)
  (at level 110, only printing, no associativity).

Notation "⊤" := True.
Notation "⊥" := False.

(***** structural properties of deduction ****)

(* If a formula belongs in a theory, it's valid. *)
Theorem exact_deduction:
  forall Γ φ,
  In φ Γ ->
  forall M,
  M '' Γ |- φ.
Proof.
  intros.
  induction Γ.
  - inversion H.
  - simpl in H.
    destruct H.
    + destruct H.
      unfold entails; intros.
      destruct H; auto.
    + unfold entails; intro.
      apply IHΓ; auto.
      destruct H0; auto.
Qed.

(* reflexivity *)
Theorem reflexive_deduction:
  forall (M: Model) (Γ: theory) (φ: modalFormula),
  M '' φ::Γ |- φ.
Proof.
  intros.
  apply exact_deduction.
  constructor; auto.
Qed.

Lemma theoryModal_union:
  forall (M: Model) (Γ ẟ: theory),
  theoryModal M (Γ ++ ẟ) -> (theoryModal M Γ /\ theoryModal M ẟ).
Proof.
    intros.
    induction Γ.
    - simpl in *.
      split; tauto.
    - simpl in *.
      apply and_assoc.
      destruct H as [left right]; split.
      + assumption.
      + apply IHΓ.
        assumption.
Qed.

(* prova bottom-up *)
Theorem  transitive_deduction_bu:
  forall (M: Model) (Γ ẟ: theory) (φ ψ Ɣ: modalFormula),
  (M '' φ::Γ |- ψ) /\ (M '' ψ::ẟ |- Ɣ) -> (M '' φ::Γ++ẟ |- Ɣ).
Proof.
  intros.
  unfold entails in *.
  destruct H as [H1 H2].
  intros; apply H2.
  simpl in *; destruct H as [left right].
  apply theoryModal_union in right; destruct right as [ModalG ModalD].
  tauto.
Qed.

Theorem exchange: forall (M : Model) (Γ : theory) (φ ψ Ɣ : modalFormula),
  (M '' φ::ψ::Γ |- Ɣ) -> (M '' ψ::φ::Γ |- Ɣ).
Proof.
  intros.
  unfold entails in *; intros.
  apply H; simpl in *.
  split.
  - destruct H0 as [H0 [H1 H2]]; apply H1.
  - split.
    + destruct H0 as [H0 [H1 H2]].
      assumption.
    + destruct H0 as [H0 [H1 H2]].
      assumption.
Qed.

Inductive transpose {T}: list T -> list T -> Prop :=
  | tranpose_head:
    forall a b tail,
    transpose (a :: b :: tail) (b :: a :: tail)
  | transpose_tail:
    forall a tail1 tail2,
    transpose tail1 tail2 -> transpose (a :: tail1) (a :: tail2)
  | transpose_refl:
    forall x,
    transpose x x
  | transpose_trans:
    forall a b c,
    transpose a b -> transpose b c -> transpose a c
  | transpose_sym:
    forall a b,
    transpose a b -> transpose b a.

Lemma transpose_in:
  forall {T} xs ys,
  transpose xs ys ->
  forall x: T,
  In x xs <-> In x ys.
Proof.
  induction 1; intros.
  - split; intros.
    + destruct H.
      * destruct H; intuition.
      * destruct H; try intuition.
        destruct H; intuition.
    + destruct H.
      * destruct H; intuition.
      * destruct H; try intuition.
        destruct H; intuition.
  - split; intros.
    + destruct H0.
      * destruct H0.
        left; auto.
      * right; apply IHtranspose.
        assumption.
    + destruct H0.
      * destruct H0.
        left; auto.
      * right; apply IHtranspose.
        assumption.
  - intuition.
  - split; intros.
    + apply IHtranspose2.
      apply IHtranspose1.
      assumption.
    + apply IHtranspose1.
      apply IHtranspose2.
      assumption.
  - split; intros.
    + apply IHtranspose; auto.
    + apply IHtranspose; auto.
Qed.

Theorem tranpose_deduction:
  forall (M: Model) (Γ ẟ: theory) (φ: modalFormula),
  transpose Γ ẟ ->
  (M '' Γ |- φ) <-> (M '' ẟ |- φ).
Proof.
  induction 1.
  - split; intros.
    + apply exchange.
      assumption.
    + apply exchange.
      assumption.
  - clear H.
    split; intros.
    + unfold entails in *; intros.
      destruct H0.
      edestruct IHtranspose as [H2 _].
      apply H2; intros.
      * apply H.
        split; auto.
      * auto.
    + unfold entails in *; intros.
      destruct H0.
      edestruct IHtranspose as [_ H2].
      apply H2; intros.
      * apply H.
        split; auto.
      * auto.
  - intuition.
  - split; intros.
    + apply IHtranspose2.
      apply IHtranspose1.
      assumption.
    + apply IHtranspose1.
      apply IHtranspose2.
      assumption.
  - split; intros.
    + apply IHtranspose; auto.
    + apply IHtranspose; auto.
Qed.

Theorem idempotence:
  forall (M : Model) (Γ : theory) (φ ψ : modalFormula),
  (M '' φ::φ::Γ |- ψ) -> (M '' φ::Γ |- ψ).
Proof.
  intros.
  unfold entails in *; intros.
  apply H; simpl in *.
  split; destruct H0.
  - apply H0.
  - split.
    + apply H0.
    + apply H1.
Qed.

Theorem monotonicity:
  forall (M: Model) (Γ ẟ: theory) (φ: modalFormula),
  (M '' Γ |- φ) -> (M '' Γ++ẟ |- φ).
Proof.
  intros.
  unfold entails in *; intros.
  apply H.
  apply theoryModal_union with (ẟ := ẟ).
  apply H0.
Qed.

(* Reflexividade *)
Definition reflexivity_frame (F: Frame): Prop :=
  forall w, R F w w.

(* Transitividade *)
Definition transitivity_frame (F: Frame): Prop :=
  forall w w' w'': W F,
  (R F w w' /\ R F w' w'') -> R F w w''.

(* Simetria *)
Definition simmetry_frame (F: Frame): Prop :=
  forall w w',
  R F w w' -> R F w' w.

(* Euclidiana *)
Definition euclidian_frame (F: Frame): Prop :=
  forall w w' w'',
  (R F w w' /\ R F w w'') -> R F w' w''.

(* Serial *)
Definition serial_frame (F: Frame): Prop :=
  forall w,
  exists w', R F w w'.

(* Funcional *)
Definition functional_frame (F: Frame) : Prop :=
  forall w w' w'',
  (R F w w' /\ R F w w'') -> w' = w''.

(* Densa*)
Definition dense_frame (F: Frame) : Prop :=
  forall w w',
  exists w'',
  R F w w' -> (R F w w'' /\ R F w' w'').

(* Convergente *)
Definition convergente_frame (F: Frame): Prop :=
  forall w x y,
  exists z,
  (R F w x /\ R F w y) -> (R F x z /\ R F y z).

(* Equivalencia lógica *)

Definition entails_modal (Γ: theory) (φ: modalFormula): Prop :=
  forall M: Model,
  theoryModal M Γ -> validate_model M φ.

Notation "Γ ||= φ" := (entails_modal Γ φ)
  (at level 110, no associativity).

Definition equivalence (φ ψ: modalFormula) : Prop := 
  ([φ] ||= ψ ) /\ ([ψ] ||= φ).

Notation "φ =|= ψ" := (equivalence φ ψ)
  (at level 110, only parsing, no associativity).

Notation "φ ≡ ψ " := (φ =|= ψ)
  (at level 110, only printing, no associativity).
