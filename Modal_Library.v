(*  Introduction

    Name: Ariel Agne da Silveira

    Advisor: Karina Girardi Roggia

    Minion: Miguel

    Agradecimentos: Torrens <3

    <Modal Logic Library>
    Description:
*)

Require Import Arith List ListSet Classical Logic Nat Notations Utf8 Tactics Relation_Definitions.

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
Notation "M ☯ A ├ B" := (entails M A B) (at level 110, no associativity).

Notation "⊤" := True.
Notation "⊥" := False.


(***** structural properties of deduction ****)
(* Γ *)
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
    forall (M: Model) (p: formulaModal),
    ((reflexivity_frame (F M)) -> (M |= .[] p .-> p)). 
Proof.
    unfold validate_model.
    unfold reflexivity_frame in *. 
    simpl in *.
    intuition.
Qed.

Theorem validacao_frame_reflexivo_volta:
    forall (M: Model) (p: formulaModal),
    ((M |= .[] p .-> p) -> (reflexivity_frame (F M))). 
Proof.
    unfold reflexivity_frame;
    unfold validate_model in *.
    simpl in *.
    intros.
    Admitted.

Theorem validacao_frame_reflexivo_ida_volta:
    forall (M: Model) (p: formulaModal),
    ((reflexivity_frame (F M)) <-> (M |= .[] p .-> p)). 
Proof.
    intros.
    split.
    apply validacao_frame_reflexivo_ida.
    apply validacao_frame_reflexivo_volta.
Qed.

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

(* Prova da relação transitiva de volta*)
Theorem validacao_frame_transitivo_volta: 
    forall (M: Model) (p: formulaModal),
    ((M |= .[]p .-> .[].[]p) -> (transitivity_frame (F M))).
Proof.
    unfold validate_model.
    unfold transitivity_frame.
    intros.
    simpl in *.
    destruct H0 as [H0 H1].
    simpl in *.
    Admitted.
             

(* 
    FIM DA ATUALIZAÇÃO DO CODIGO

*)

(* Simetria *)
Definition simmetry_frame (F: Frame) : Prop :=
    forall w w': World, (In w (W F) /\ In w' (W F)) -> (relacao (R F) w w' -> relacao (R F) w' w).

Theorem validacao_frame_simetria: 
    forall (M: Model) (p:formulaModal),
    (simmetry_frame (F M)) -> (M |= p .-> .[] .<> p).
Proof.
    intros.
    unfold validate_model.
    intros.
    simpl.
    intros.
    exists w0.
    split.
    unfold simmetry_frame in *.
    apply H with (w:=w0) (w':=w').
    apply relacao_pertinencia_mundos. apply H2. apply H2.
    apply H1.
Qed.

(* Euclidiana *)
Definition euclidian_frame (F: Frame) : Prop :=
    forall w w' w'', (In w (W F) /\ In w' (W F) /\ In w'' (W F)) -> ((relacao (R F) w w' /\ relacao (R F) w w'') -> relacao (R F) w' w'').

Theorem validacao_frame_eucliadiana: 
    forall (M: Model) (p: formulaModal),
    (euclidian_frame (F M)) -> (M |= .<> p .-> .[] .<> p).
Proof.
    intros.
    unfold validate_model.
    simpl.
    intros w H0 H1 w' H2.
    (* split. *)
    unfold euclidian_frame in *.
    destruct H1 as [w'' [H1 H3]].
    exists w''.
    split.
    apply H with (w:=w) (w':=w') (w'':=w'').
    split. apply H0.
    apply relacao_pertinencia_mundos in H2. apply relacao_pertinencia_mundos in H1.
    split; destruct H2; auto.
    destruct H1; auto.
    split; eauto. apply H3.
Qed.

(* Serial *)
Definition serial_frame (F: Frame) : Prop :=
    forall w: World, exists w': World, 
        (In w (W F) /\ In w' (W F)) -> (relacao (R F) w w').

Theorem validacao_frame_serial: 
    forall (M: Model) (p: formulaModal),
    (serial_frame (F M)) -> (M |= .[] p .-> .<> p).
Proof.
    intros.
    unfold validate_model.
    unfold serial_frame in *.
    simpl;
    intros w H0 H1;
    destruct H with (w:=w).
    exists x;
    split.
    apply H2;
    split. apply H0.
    
    

Admitted.


(* Funcional *)
Definition functional_frame (F: Frame) : Prop :=
    forall w w' w'' : World, (In w (W F) /\ In w' (W F) /\ In w'' (W F)) -> ((relacao (R F) w w' /\ relacao (R F) w w'') -> w' = w'').

Theorem validacao_frame_funcional:
    forall (M:Model) (p:formulaModal),
    (functional_frame (F M)) -> (M |= .<> p .-> .[] p).
Proof.
    intros.
    unfold validate_model.
    simpl.
    intros.
    destruct H1 as [w [H1 H3]].
    unfold functional_frame in *.
    destruct H with (w:=w0) (w':=w) (w'':=w').
    split. apply H0.
    apply relacao_pertinencia_mundos in H1 as Hip1.
    apply relacao_pertinencia_mundos in H2 as Hip2.
    destruct Hip1. destruct Hip2.
    split. apply H5. apply H7.
    split. apply H1. apply H2. apply H3.
Qed.


(* Densa*)
Definition dense_frame (F: Frame) : Prop :=
    forall w w': World, exists w'' : World, (In w (W F) /\ In w' (W F) /\ In w'' (W F)) -> (relacao (R F) w w' -> (relacao (R F) w w'' /\ relacao (R F) w'' w')).


Theorem validacao_frame_densa:
    forall (M: Model) (p: formulaModal),
    (dense_frame (F M)) -> (M |= .[] .[] p .-> .[] p).
Proof.
    intros.
    unfold validate_model.
    unfold dense_frame in *.
    simpl in *.
    intros.
    apply H1 with (w':=w') (w'0:=w').
    apply H2.
    destruct H with (w:=w0) (w':=w') as [w Hip].
    apply Hip in H2.
    destruct Hip.
    split; auto.
    destruct H2.
    apply relacao_pertinencia_mundos in H3 as Hip. destruct Hip.
    split; auto.
    destruct H2.
    apply relacao_pertinencia_mundos in H3. destruct H3.
    
    apply H1. destruct H1 with (w':=w') (w'0:=w').
Admitted.

(* Convergente *)
Definition convergente_frame (F: Frame) : Prop :=
    forall w x y: World, exists z: World,  (In w (W F) /\ In x (W F) /\ In y (W F) -> (relacao (R F) w x /\ relacao (R F) w y) -> (relacao (R F) x z /\ relacao (R F) y z /\ In z (W F))).


Theorem validacao_frame_convergente:
    forall (M: Model) (p: formulaModal),
    (convergente_frame (F M)) -> (M |= .<> .[] p .-> .[] .<> p).
Proof.
    intros.
    unfold validate_model.
    unfold convergente_frame in *.
    simpl in *.
    intros.
    destruct H1.
    destruct H1 as [Hip1 Hip2].
    destruct H with (w:=w0) (x:=x) (y:=w').
    destruct H1.
    split. apply H0.
    apply relacao_pertinencia_mundos in H2 as Hip3. destruct Hip3.
    apply relacao_pertinencia_mundos in Hip1 as Hip4. destruct Hip4.
    split; auto.
    split; auto.
    exists x0.
    split. destruct H3; auto.
    apply Hip2 with (w':=x0). apply H1.
Qed.



(* Equivalencia lógica *)




Definition equivalence (M: Model) (f g:formulaModal) : Prop := 
    ( M '' f::nil |- g ) <-> (M '' g::nil |- f).

Notation "M |= A =|= B" := (equivalence M A B) (at level 110, no associativity).

Notation "M |= A ≡ B " := (M |= A =|= B) (at level 110, no associativity).

Theorem implies_to_or_modal : 
    forall (M: Model) (w: World) (a b: formulaModal),
        (M |= (a .-> b)  =|=  (.~ a) .\/ b) .
Proof.
    intros.
    unfold equivalence;
    induction M;
    split.
        - intros. unfold entails in *. intros; simpl in *.
            unfold validate_model in *. inversion H0. 
            intros. split. apply H1. simpl in *. intros.
            destruct H1. 
        
        simpl in *. 
            apply H0 in H.
            
    intros.
    simpl in *. destruct H0. 
    unfold validate_model.
Admitted.




(* ;-; *)