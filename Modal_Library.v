(*  Introduction

    Name: Ariel Agne da Silveira

    Advisor: Karina Girardi Roggia
    Co-Advisor: Paulo Torrens

    Minion: Miguel

    <Modal Logic Library>

    Description:
*)
(* Biblitoeca não utilizada: Nat Logic Classical_Prop  Tactics Relation_Definitions*)
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
    R : list (W * W);
}.

Record Model : Type := {
    F : Frame; 
    v : (W F) -> nat -> Prop; (* Conversar sobre isso *)
}.

Check Build_Frame.
Check Build_Model.

(* Fixpoint verification {M : Model} (v: list (nat * list (W (F M)))) (w: (W (F M))) (p : nat) : Prop :=
    match v with
    | [] => False
    | h :: t => ((verification t w p) \/ (p = fst h /\ In w (snd h)))
    end. *)

Fixpoint fun_validation (M : Model) (w : (W (F M))) (φ : modalFormula) : Prop :=
    match φ with
    | Lit      x     => (v M) w x
    (* | Lit      x     => verification (v M) w x  *)
    | Box      ψ     => forall w': (W (F M)), In (w, w') (R (F M)) -> fun_validation M w' ψ
    | Dia      ψ     => exists w': (W (F M)), In (w, w') (R (F M)) /\ fun_validation M w' ψ
    | Neg      ψ     => ~ fun_validation M w ψ
    | And      ψ  Ɣ  => fun_validation M w ψ /\ fun_validation M w Ɣ
    | Or       ψ  Ɣ  => fun_validation M w ψ \/ fun_validation M w Ɣ
    | Implies  ψ  Ɣ  => fun_validation M w ψ -> fun_validation M w Ɣ
    end.

    (* World Satisfaziblity *)
Notation "M ' w ||- φ" := (fun_validation M w φ) (at level 110, right associativity).
Notation "M ☯ w ╟ φ  " := (fun_validation M w φ) (at level 110, right associativity).

(* Model satisfazibility *)
Definition validate_model (M : Model) (φ : modalFormula) : Prop :=
    forall w: (W (F M)), fun_validation M w φ.

Notation "M |= φ" := (validate_model M φ) (at level 110, right associativity).
Notation "M ╞ φ " := (validate_model M φ) (at level 110, right associativity).

(******  Finite theories and entailment ******)

Definition theory := list modalFormula.

Fixpoint theoryModal (M : Model) (Γ : theory) : Prop :=
    match Γ with
    | nil => True
    | h :: t => (validate_model M h) /\ (theoryModal M t)
    end.

Definition entails (M : Model) (Γ : theory) (φ : modalFormula) : Prop :=
    (theoryModal M Γ) -> validate_model M φ.

Notation "M '' Γ |- φ" := (entails M Γ φ) (at level 110, no associativity).
Notation "M ♥ Γ ├ φ  " := (entails M Γ φ) (at level 110, no associativity).

Notation "⊤" := True.
Notation "⊥" := False.


(***** structural properties of deduction ****)

(* reflexivity *)
Theorem  reflexive_deduction:
   forall (M : Model) (Γ : theory) (φ : modalFormula) ,
      (M '' φ::Γ |- φ).
Proof.
    - intros.
        unfold entails.
        intros.
        destruct H.
        apply H.
Qed.
        
Lemma theoryModal_union: forall (M:Model) (Γ ẟ:theory),
  (theoryModal M (Γ++ẟ)) -> ((theoryModal M Γ) /\ (theoryModal M ẟ)).
Proof.
    intros.
    induction Γ.
        - simpl in *. split. tauto. apply H.
        - simpl in *. apply and_assoc. destruct H as [left  right]. split.
            + apply left.
            + apply IHΓ. apply right.
Qed.

(* prova bottom-up *)
Theorem  transitive_deduction_bu:
   forall (M:Model) (Γ ẟ:theory) (φ ψ Ɣ:modalFormula) ,
      (M '' φ::Γ |- ψ) /\ (M '' ψ::ẟ |- Ɣ) -> (M '' φ::Γ++ẟ |- Ɣ).
Proof.
    - intros. 
        unfold entails in *. 
        destruct H as [H1 H2]. 
        intros; apply H2.
        simpl in *; destruct H as [left right]. 
        apply theoryModal_union in right; destruct right as [ModalG ModalD]. 
        split.
        + apply H1.
            * split.
                -- apply left.
                -- apply ModalG. 
        + apply ModalD.
Qed.

Theorem exchange: forall (M : Model) (Γ : theory) (φ ψ Ɣ : modalFormula),
  (M '' φ::ψ::Γ |- Ɣ) -> (M '' ψ::φ::Γ |- Ɣ).
Proof.
    - intros. 
        unfold entails in *; 
        intros;
        apply H.
        simpl in *;
        split.
        + destruct H0 as [H0 [H1 H2]]; apply H1.
        + split.
            * destruct H0 as [H0 [H1 H2]]. apply H0.
            * destruct H0 as [H0 [H1 H2]]. apply H2.
Qed.
                
Theorem idempotence:
    forall (M : Model) (Γ : theory) (φ ψ : modalFormula),
        (M '' φ::φ::Γ |- ψ) -> (M '' φ::Γ |- ψ).
Proof.
    - intros.
        unfold entails in *.
        intros.
        apply H.
        simpl in *.
        split; destruct H0.
        + apply H0.
        + split. 
            * apply H0. 
            * apply H1.
Qed.


Theorem monotonicity: forall (M : Model) (Γ ẟ : theory) (φ : modalFormula),
    (M '' Γ |- φ) -> (M '' Γ++ẟ |- φ).
Proof.
    - intros.
        unfold entails in *.
        intros. apply H.
        apply theoryModal_union with (ẟ:=ẟ).
        apply H0.
Qed.

    (* Reflexividade *)
Definition reflexivity_frame (F: Frame) : Prop :=
    forall w, In (w, w) (R F).
    
    (* Transitividade *)
Definition transitivity_frame (F: Frame) : Prop :=
    forall w w' w'' : (W F), (In (w, w') (R F) /\ In (w', w'') (R F)) -> In (w, w'') (R F).


    (* Simetria *)
Definition simmetry_frame (F: Frame) : Prop :=
    forall w w', In (w, w') (R F) -> In (w', w) (R F).


    (* Euclidiana *)
Definition euclidian_frame (F: Frame) : Prop :=
    forall w w' w'', In (w, w') (R F) /\ In (w, w'') (R F) -> In (w', w'') (R F).


    (* Serial *)
Definition serial_frame (F: Frame) : Prop :=
    forall w, exists w', In (w, w') (R F).


    (* Funcional *)
Definition functional_frame (F: Frame) : Prop :=
    forall w w' w'', (In (w, w') (R F) /\ In (w, w'') (R F)) -> w' = w''.


    (* Densa*)
Definition dense_frame (F: Frame) : Prop :=
    forall w w', exists w'', In (w, w') (R F) -> (In (w, w'') (R F) /\ In (w', w'') (R F)).


    (* Convergente *)
Definition convergente_frame (F: Frame) : Prop :=
    forall w x y, exists z,  In (w, x) (R F) /\ In (w, y) (R F) -> (In (x, z) (R F) /\ In (y, z) (R F)).


(* Equivalencia lógica *)

Definition entails_modal (Γ : theory) (φ : modalFormula) : Prop :=
    forall M: Model, (theoryModal M Γ) -> validate_model M φ.

Notation "Γ ||= φ" := (entails_modal Γ φ) (at level 110, no associativity).

Definition equivalence (φ ψ : modalFormula) : Prop := 
    ( φ::nil ||= ψ ) /\ (ψ::nil ||= φ).

Notation "φ =|= ψ" := (equivalence φ ψ) (at level 110, no associativity).

Notation "φ ≡ ψ " := (φ =|= ψ) (at level 110, no associativity).



Fixpoint toImplic (φ : modalFormula) : modalFormula :=
match φ with
  | # x     => # x
  | .~  ψ    => .~ (toImplic ψ)
  | .[] ψ   => .[] (toImplic ψ)
  | .<> ψ   => .~ .[] .~ (toImplic ψ)
  | ψ ./\ Ɣ => .~ ( (toImplic ψ) .-> .~ (toImplic Ɣ) ) 
  | ψ .\/ Ɣ => (.~ (toImplic ψ) .-> (toImplic Ɣ) ) 
  | ψ .-> Ɣ => (toImplic ψ) .-> (toImplic Ɣ)
end.



Theorem toImplic_equiv : forall (f : modalFormula), f =|= (toImplic f).
Proof.
    split.
    - unfold entails_modal.
        intros. simpl in *;
        destruct H as (?, _);
        unfold validate_model in *.
        intros;
        
        admit. 
    - unfold entails_modal;
        simpl; intros. destruct H as (?, _).
        unfold validate_model in *.
        intros.
         
        
    (* intros.
    split.
        - unfold entails_teste;
            unfold validate_model in *;
            simpl in *;
            unfold validate_model in *.
            intros;
            destruct H0 as (?, _).
            pose (X := H).
            edestruct classic.
                + exact H1.
                + 
            admit.
        - intros; unfold entails_teste in *.
            simpl in *;
            unfold validate_model in *.
            intros.
            destruct H0 as (?, _). 
            
            destruct H0.
            destruct classic with (M ' w ||- f).
            auto. 
            apply H0. *)

    Admitted.






(* ;-; *)