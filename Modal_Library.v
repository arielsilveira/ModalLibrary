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

Check Build_Model.

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

(* Ver esse ponto para baixo *)
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
        
(* transitivity *)

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
    
Theorem validacao_frame_reflexivo_ida:
    forall (M: Model) (Ψ: formulaModal),
    (~(M |= .[] Ψ .-> Ψ) -> ~(reflexivity_frame (F M))). 
Proof.
    intros.
    unfold not in *.
    unfold reflexivity_frame.
    unfold validate_model in *. 
    simpl in *. auto.
Qed.


Theorem validacao_frame_reflexivo_volta:
    forall (M: Model) (Ψ: formulaModal),
    (~ (reflexivity_frame (F M)) -> ~ (M |= .[] Ψ .-> Ψ)).
Proof. 
    unfold not.
    unfold reflexivity_frame in *.
    unfold validate_model in *.
    intros.
    apply H.
    intros.
    simpl in *.
    assert (forall w:W (F M), (In (w, w) (R (F M))) \/ ~(In (w, w) (R (F M)))).
    intros. apply classic.
    destruct H1 with (w:=w).
        apply H2.
    
    Admitted.

(* Theorem validacao_frame_reflexivo_ida:
    forall (M: Model) (Ψ: formulaModal),
    ((reflexivity_frame (F M)) -> (M |= .[] Ψ .-> Ψ)). 
Proof.
    unfold validate_model.
    unfold reflexivity_frame in *. 
    simpl in *.
    intuition.
Qed. *)

Theorem validacao_frame_reflexivo_volta_2: 
    forall (M: Model) (Ψ: formulaModal),
    ~((M |= .[] Ψ .-> Ψ) -> (reflexivity_frame (F M))). 
Proof.
    intros.
    unfold not.
    unfold validate_model in *.
    unfold reflexivity_frame.
    simpl in *.
    intros.
    assert (forall w:W (F M), (In (w, w) (R (F M))) \/ ~(In (w, w) (R (F M)))).
    intros. apply classic.
    (* destruct H0. with (W:=w'). *)
    

Admitted.

(* Transitividade *)
Definition transitivity_frame (F: Frame) : Prop :=
    forall w w' w'' : (W F), (In (w, w') (R F) /\ In (w', w'') (R F)) -> In (w, w'') (R F).
    

(* Prova da relação transitiva de ida*)
Theorem validacao_frame_transitivo_ida: 
    forall (M: Model) (p: formulaModal),
    ((transitivity_frame (F M)) -> (M |= .[]p .-> .[].[]p)).
Proof.
    intros.
    unfold validate_model.
    simpl.
    intros.
    unfold transitivity_frame in *.
    apply H0.
    apply H  with (w:=w) (w':=w') (w'':=w'0).
    split. apply H1. apply H2. 
Qed.

(* Prova da relação transitiva de volta *)
Theorem validacao_frame_transitivo_volta: 
    forall (M: Model) (p: formulaModal),
    ((M |= .[]p .-> .[].[]p) -> (transitivity_frame (F M))).
Proof.
Admitted.

(* Simetria *)
Definition simmetry_frame (F: Frame) : Prop :=
    forall w w', In (w, w') (R F) -> In (w', w) (R F).

    Theorem validacao_frame_simetria_ida: 
    forall (M: Model) (p:formulaModal),
    (simmetry_frame (F M)) -> (M |= p .-> .[] .<> p).
Proof.
    intros.
    unfold validate_model.
    simpl in *.
    intros.
    exists w.
    apply and_comm.
    split.
    apply H0.
    unfold simmetry_frame in *.
    apply H. apply H1.
Qed.

Theorem validacao_frame_simetria_volta: 
    forall (M: Model) (p:formulaModal),
    ((M |= p .-> .[] .<> p) -> (simmetry_frame (F M))).
Proof.
Admitted.

(* Euclidiana *)
Definition euclidian_frame (F: Frame) : Prop :=
    forall w w' w'', In (w, w') (R F) /\ In (w, w'') (R F) -> In (w', w'') (R F).

Theorem validacao_frame_eucliadiana_ida: 
    forall (M: Model) (p: formulaModal),
    (euclidian_frame (F M)) -> (M |= .<> p .-> .[] .<> p).
Proof.
    intros.
    unfold euclidian_frame in *.
    unfold validate_model.
    simpl in *.
    intros.
    destruct H0 as [x [Hip1 Hip2]].
    exists x.
    split.
    apply H with (w:=w) (w':=w') (w'':=x).
    split. auto. auto. auto.
Qed.


Theorem validacao_frame_eucliadiana_volta: 
    forall (M: Model) (p: formulaModal),
    (((M |= .<> p .-> .[] .<> p) -> (euclidian_frame (F M)) )).
Proof.
Admitted.


(* Serial *)
Definition serial_frame (F: Frame) : Prop :=
    forall w, exists w', In (w, w') (R F).

Theorem validacao_frame_serial_ida: 
    forall (M: Model) (p: formulaModal),
    (serial_frame (F M)) -> (M |= .[] p .-> .<> p).
Proof.
    unfold validate_model.
    unfold serial_frame in *.   
    simpl in *.
    intros.
    destruct H with (w:=w).
    exists x. split. auto.
    apply H0 in H1. apply H1.
Qed.

Theorem validacao_frame_serial_volta: 
    forall (M: Model) (p: formulaModal),
    ((M |= .[] p .-> .<> p) -> (serial_frame (F M))).
Proof.   
Admitted.


(* Funcional *)
Definition functional_frame (F: Frame) : Prop :=
    forall w w' w'', (In (w, w') (R F) /\ In (w, w'') (R F)) -> w' = w''.

Theorem validacao_frame_funcional_ida:
    forall (M:Model) (p:formulaModal),
    (functional_frame (F M)) -> (M |= .<> p .-> .[] p).
Proof.
    intros; 
    unfold validate_model; 
    unfold functional_frame in *.
    simpl in *.
    intros w H0 w1 H1.
    destruct H0 as [w' [H0 H2]].
    destruct H with (w:=w) (w':=w1) (w'':=w').
    split. apply H1. apply H0. apply H2.
Qed.

Theorem validacao_frame_funcional_volta:
    forall (M:Model) (p:formulaModal),
     (M |= .<> p .-> .[] p) -> (functional_frame (F M)).
Proof.
Admitted.

(* Densa*)
Definition dense_frame (F: Frame) : Prop :=
    forall w w', exists w'', In (w, w') (R F) -> (In (w, w'') (R F) /\ In (w', w'') (R F)).


Theorem validacao_frame_densa_ida:
    forall (M: Model) (p: formulaModal),
    (dense_frame (F M)) -> (M |= .[] .[] p .-> .[] p).
Proof.
    unfold validate_model;
    unfold dense_frame;
    simpl in *.
    intros. 
    apply H0 with (w':=w').
    auto.
    induction H with (w:=w') (w':=w').
        



Admitted.


Theorem validacao_frame_densa_volta:
    forall (M: Model) (p: formulaModal),
    (dense_frame (F M)) -> (M |= .[] .[] p .-> .[] p).
Proof.
Admitted.

(* Convergente *)
Definition convergente_frame (F: Frame) : Prop :=
    forall w x y, exists z,  In (w, x) (R F) /\ In (w, y) (R F) -> (In (x, z) (R F) /\ In (y, z) (R F)).

    Theorem validacao_frame_convergente_ida:
    forall (M: Model) (p: formulaModal),
    (convergente_frame (F M)) -> (M |= .<> .[] p .-> .[] .<> p).
Proof.
    unfold convergente_frame.
    unfold validate_model.
    simpl in *.
    intros.
    destruct H0 as [x [Hip1 Hip2]].
    destruct H with (w:=w) (x:=x) (y:=w').
    destruct H0. auto.
    exists x0.
    split; auto.
Qed.

Theorem validacao_frame_convergente_volta:
    forall (M: Model) (p: formulaModal),
    (M |= .<> .[] p .-> .[] .<> p) -> (convergente_frame (F M)).
Proof.
Admitted.

(* Equivalencia lógica *)


Definition entails_teste (A : theory) (B : formulaModal) : Prop :=
    forall M: Model, (theoryModal M A) -> validate_model M B.

Notation "A ||= B" := (entails_teste A B) (at level 110, no associativity).

(* Criar outra definição sem o modelo *)
Definition equivalence (f g:formulaModal) : Prop := 
    ( f::nil ||= g ) <-> (g::nil ||= f).

Notation "A =|= B" := (equivalence A B) (at level 110, no associativity).

Notation "A ≡ B " := (A =|= B) (at level 110, no associativity).

Theorem implies_to_or_modal : 
    forall (a b: formulaModal),
        (a .-> b)  =|=  (.~ a) .\/ b .
Proof.
    intros.
    split.
        - intros. 
            unfold entails_teste in *. 
            intros. 
            simpl in *.
            destruct H0. 
            unfold validate_model in *. 
            simpl in *.
            intro w.
            apply or_to_imply. apply H0.
        - intros.
            unfold entails_teste in *. 
            intros. 
            simpl in *.
            destruct H0. 
            unfold validate_model in *.
            intros.
            simpl in *.
            apply imply_to_or. auto. 
Qed.

Theorem double_neg_modal :
    forall (a : formulaModal),
    (.~ .~ a) =|= a.
Proof.
    intros.
    split.
        - unfold entails_teste.
            simpl in *.
            unfold validate_model.    
            intros.
            destruct H0.
            simpl in *.
            intro.
            


        unfold validate_model in *.
            destruct H0. 
            intro.
            apply exfalso. contradiction. 
        
Admitted.

Theorem and_to_or_modal: 
    forall (a b: formulaModal),
    ((a ./\ b) =|= .~ (.~ a .\/ .~ b)).
Proof.
Admitted.

Theorem iff_to_or_modal:
    forall (a b: formulaModal),
    (a .<-> b) =|= ((a .-> b) ./\ (b .-> a)).
Proof.
Admitted.

Theorem diamond_to_box_modal:
    forall (a : formulaModal),
    (.<> a) =|= .~ .[] .~ a.
Proof.
Admitted.


(* ;-; *)