(*  Introduction

    Name: Ariel Agne da Silveira

    Advisor: Karina Girardi Roggia

    Minion: Miguel

    Agradecimentos: Torrens <3

    <Modal Logic Library>
    Description:
*)

Require Import Arith List ListSet Classical Logic Nat Notations Utf8 Tactics Relation_Definitions Classical_Prop.

Inductive formulaModal : Set :=
    | Lit          : nat -> formulaModal
    | Neg          : formulaModal -> formulaModal
    | Box          : formulaModal -> formulaModal
    | Dia          : formulaModal -> formulaModal
    | And          : formulaModal -> formulaModal -> formulaModal
    | Or           : formulaModal -> formulaModal -> formulaModal
    | Implies      : formulaModal -> formulaModal -> formulaModal 
.

(* Calcula o tamanho de uma fórmula com base na lógica modal *)
Fixpoint sizeModal (f:formulaModal) : nat :=
    match f with 
    | Lit      x     => 1
    | Neg      p1    => 1 + (sizeModal p1)
    | Box      p1    => 1 + (sizeModal p1)
    | Dia      p1    => 1 + (sizeModal p1)
    | And      p1 p2 => 1 + (sizeModal p1) + (sizeModal p2)
    | Or       p1 p2 => 1 + (sizeModal p1) + (sizeModal p2)
    | Implies  p1 p2 => 1 + (sizeModal p1) + (sizeModal p2)
end.

Fixpoint literals (f:formulaModal) : set nat :=
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
Notation " X .-> Y "  := (Implies X Y) (at level 13, right associativity).
Notation " X .\/ Y "  := (Or X Y)      (at level 12, left associativity).
Notation " X ./\ Y"   := (And X Y)     (at level 11, left associativity).
Notation " .~ X "     := (Neg X)       (at level 9, right associativity).
Notation " .[] X "    := (Box X)       (at level 9, right associativity).
Notation " .<> X "    := (Dia X)       (at level 9, right associativity).
Notation " # X "      := (Lit X)       (at level 1, no associativity).

Notation " ☐ A" := (.[] A)
    (at level 1, A at level 200, right associativity): type_scope.

Notation " ◇ A" := (.<> A)
    (at level 1, A at level 200, right associativity): type_scope.

Notation " A → B" := (A .-> B)
    (at level 99, B at level 200, right associativity) : type_scope.

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
    F : Frame; (*Frame de um modelo*)
    v : list (nat * list (W F));
}.

Fixpoint verification {M : Model} (v: list (nat * list (W (F M)))) (w: (W (F M))) (p : nat) : Prop :=
    match v with
    | [] => False
    | h :: t => ((verification t w p) \/ (In p [(fst h)] /\ In w (snd h))) -> True
    end.

Fixpoint fun_validation (M : Model) (w : (W (F M))) (p : formulaModal) : Prop :=
    match p with
    | Lit       x    => verification (v M) w x 
    | Box      p1    => forall w': (W (F M)), In (w, w') (R (F M)) -> fun_validation M w' p1
    | Dia      p1    => exists w': (W (F M)), In (w, w') (R (F M)) /\ fun_validation M w' p1
    | Neg      p1    => ~ fun_validation M w p1
    | And      p1 p2 => fun_validation M w p1 /\ fun_validation M w p2
    | Or       p1 p2 => fun_validation M w p1 \/ fun_validation M w p2
    | Implies  p1 p2 => fun_validation M w p1 -> fun_validation M w p2 
    end.

    (* World Satisfaziblity *)
Notation "M ' w ||- B" := (fun_validation M w B) (at level 110, right associativity).
Notation "M ☯ w ╟ B" := (fun_validation M w B) (at level 110, right associativity).

(* Model satisfazibility *)
Definition validate_model (M : Model) (p : formulaModal) : Prop :=
    forall w: (W (F M)), fun_validation M w p.

Notation "M |= B" := (validate_model M B) (at level 110, right associativity).
Notation "M ╞ B" := (validate_model M B) (at level 110, right associativity).

(******  Finite theories and entailment ******)

Definition theory := list formulaModal.

Fixpoint theoryModal (M : Model) (Gamma : theory) : Prop :=
    match Gamma with
    | nil => True
    | h :: t => (validate_model M h) /\ (theoryModal M t)
    end.

Definition entails (M : Model) (A : theory) (B : formulaModal) : Prop :=
    (theoryModal M A) -> validate_model M B.

Notation "M '' A |- B" := (entails M A B) (at level 110, no associativity).
Notation "M ♥ A ├ B" := (entails M A B) (at level 110, no associativity).

Notation "⊤" := True.
Notation "⊥" := False.


(***** structural properties of deduction ****)
(* Γ ٭*)
(* reflexivity *)
Theorem  reflexive_deduction:
   forall (M: Model) (Gamma: theory) (A: formulaModal) ,
      (M '' A::Gamma |- A).
Proof.
    intros.
    unfold entails.
    intros.
    destruct H.
    apply H.
Qed.
        
Lemma theoryModal_union: forall (M:Model) (Gamma Delta:theory),
  (theoryModal M (Gamma++Delta)) -> ((theoryModal M Gamma) /\ (theoryModal M Delta)).
Proof.
    intros.
    induction Gamma.
        - simpl in *. split. tauto. apply H.
        - simpl in *. apply and_assoc. destruct H as [left  right]. split.
            + apply left.
            + apply IHGamma. apply right.
Qed.
         

(* prova bottom-up *)
Theorem  transitive_deduction_bu:
   forall (M:Model) (Gamma Delta:theory) (A B C:formulaModal) ,
      (M '' A::Gamma |- B) /\ (M '' B::Delta |- C) -> (M '' A::Gamma++Delta |- C).
Proof.
    intros. 
    unfold entails in *. 
    destruct H as [H1 H2]. 
    intros; apply H2.
    simpl in *; destruct H as [left right]. 
    apply theoryModal_union in right; destruct right as [ModalG ModalD]. split.
        - apply H1.
            + split.
                * apply left.
                * apply ModalG. 
        - apply ModalD.
Qed.

Theorem exchange: forall (M: Model) (Gamma:theory) (A B C:formulaModal),
  (M '' A::B::Gamma |- C) -> (M '' B::A::Gamma |- C).
Proof.
    intros. 
    unfold entails in *; 
    intros;
    apply H.
    simpl in *;
    split.
        - destruct H0 as [H0 [H1 H2]]; apply H1.
        - split.
            destruct H0 as [H0 [H1 H2]]. apply H0.
            destruct H0 as [H0 [H1 H2]]. apply H2.
Qed.
                
Theorem idempotence:
    forall (M: Model) (Gamma:theory) (A B:formulaModal),
        (M '' A::A::Gamma |- B) -> (M '' A::Gamma |- B).
Proof.
    intros.
    unfold entails in *.
    intros.
    apply H.
    simpl in *.
    split; destruct H0. apply H0.
    split. apply H0. apply H1.
Qed.


Theorem monotonicity: forall (M:Model) (Gamma Delta: theory) (A: formulaModal),
    (M '' Gamma |- A) -> (M '' Gamma++Delta |- A).
Proof.
    intros.
    unfold entails in *.
    intros. apply H.
    apply theoryModal_union with (Delta:=Delta).
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

Definition entails_teste (A : theory) (B : formulaModal) : Prop :=
    forall M: Model, (theoryModal M A) -> validate_model M B.

Notation "A ||= B" := (entails_teste A B) (at level 110, no associativity).

Definition equivalence (f g:formulaModal) : Prop := 
    ( f::nil ||= g ) <-> (g::nil ||= f).

Notation "A =|= B" := (equivalence A B) (at level 110, no associativity).

Notation "A ≡ B " := (A =|= B) (at level 110, no associativity).



Fixpoint toImplic (f: formulaModal) : formulaModal :=
match f with
  | # x     => # x
  | .~ a    => .~ (toImplic a)
  | .[] a   => .[] (toImplic a)
  | .<> a   => .<> (toImplic a)
  | a ./\ b => .~ (.~ (toImplic a) .-> (toImplic b) ) 
  | a .\/ b => .~ (.~ (toImplic a) .-> (toImplic b) ) 
  | a .-> b => (toImplic a) .-> (toImplic b)
end.



Theorem toImplic_equiv : forall (f:formulaModal), f =|= (toImplic f).
Proof.
    intros.
    split.
        - unfold entails_teste.
            unfold validate_model in *.
            intros.
            simpl in *.
            unfold validate_model in *.
            destruct H0.
    Admitted.



(***************** DEDUCTIVE SYSTEMS *************************)




(* ;-; *)