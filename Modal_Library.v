(*  Introduction

    Name: Ariel Agne da Silveira

    Advisor: Karina Girardi Roggia

    Minion: Miguel

    Agradecimentos: Torrens <3

    <Modal Logic Library>
    Description:
*)

Require Import Arith List ListSet Classical Logic Nat Notations Utf8 Tactics.

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

Inductive World : Set :=
    | w : nat -> World
.


Inductive Relation : Set :=
    | r : World -> World -> Relation
.

(* -- New notation -- *)
Notation " X .-> Y "  := (Implies X Y) (at level 13, right associativity).
Notation " X .\/ Y "  := (Or X Y)      (at level 12, left associativity).
Notation " X ./\ Y"   := (And X Y)     (at level 11, left associativity).
Notation " .~ X "     := (Neg X)       (at level 10, right associativity).
Notation " .[] X "    := (Box X)       (at level 10, right associativity).
Notation " .<> X "    := (Dia X)       (at level 10, right associativity).
Notation " # X "      := (Lit X)       (at level 1, no associativity).

Notation " ☐ A" := (.[] A)
    (at level 1, A at level 200, right associativity): type_scope.

Notation " ◇ A" := (.<> A)
    (at level 1, A at level 200, right associativity): type_scope.

Notation " A → B" := (A .-> B)
    (at level 99, B at level 200, right associativity) : type_scope.

Notation "w # X" := (w X) (at level 1, no associativity).
Notation "x .R y" := (r x y) (at level 1, no associativity).

Notation "[ ]" := nil.
Notation "x :: l" := (cons x l)
                     (at level 60, right associativity).
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).


Fixpoint eqb_World (x x' : World): bool :=
    match x with
    | w n => match x' with 
                | w n' => if  n =? n' then true else false
            end
end.

Fixpoint In_World (x: World) (l: list World): bool :=
    match l with
    | nil => false
    | h :: t => if eqb_World x h then true
                else In_World x t
end.

Fixpoint All_In_World (l : list World) (l' : list World) : bool :=
    match l with
  | nil  => true
  | h::t => if In_World h l' then All_In_World t l'
            else false
end.

Fixpoint remove_invalidate (Worlds : list World) (Relations : list (World * World)) : list (World * World) :=
    match Relations with
    | nil => nil 
    | h :: t => if andb (In_World (fst h) Worlds) (In_World (snd h) Worlds) 
                then [(fst h, snd h)] ++ remove_invalidate Worlds t
                else remove_invalidate Worlds t
end.

Fixpoint pair_to_relation (l : list (World * World)) : list Relation :=
    match l with
    | nil => nil
    | h :: t => (r (fst h) (snd h)) :: pair_to_relation t
end.

Definition validate_relation (Worlds : list World) (lw : list (World * World)) : list Relation := 
    pair_to_relation (remove_invalidate Worlds lw).

(* formula válida em algum mundo, 
    verifica se os mundos existem, 
    se sim, 
    concatena
*)
Fixpoint validate_formula (Worlds : list World) (Formulas : list (formulaModal * list World)) : 
         list (formulaModal * list World) :=
  match Formulas with
    | nil   => nil
    | h::t  => match snd h with 
                   | nil => validate_formula Worlds t 
                   | h'::t' => if All_In_World (snd h) Worlds then  [h] ++ validate_formula Worlds t
                               else validate_formula Worlds t
               end
  end.

Record Frame : Type := frame_kripke{
    W : list World; (*Recebe uma lista de mundos*)
    R : list Relation; (*Recebe uma lista de pares ordenados*)
}.

Record Model : Type := model_kripke{
    F : Frame; (*Frame de um modelo*)
    v: list (nat * (list World));
}.


Definition frame (w: list World) (r: list (World * World)) : Frame :=
    frame_kripke w (validate_relation w r).

Definition model (f: Frame) (v: list (nat * (list World))) : Model :=
    model_kripke f v.


Fixpoint verification (val: list (nat * (list World))) (w : World) (p: nat) : Prop :=
    match val with
    | [] => False
    | h :: t => if andb (eqb p (fst h)) (In_World w (snd h)) then True
                else verification t w p
    end.

Definition fst_world (pair_w: Relation) : World :=
    match pair_w with
    | r x y => x
    end.

Definition snd_world (pair_w: Relation) : World :=
    match pair_w with
    | r x y => y
    end.

Fixpoint relacao (r: list Relation) (w w' : World) : Prop :=
    match r with
    | [] => False
    | h :: t => if andb (eqb_World (fst_world h) w) (eqb_World (snd_world h) w') then True
                else relacao t w w'
    end.

    (* World Satisfaziblity *)
Fixpoint fun_validation (M : Model) (w : World) (p : formulaModal) : Prop :=
    match p with
    | Lit      x     => verification (v M) w x
    | Box      p1    => forall w': World, relacao (R (F M)) w w' -> fun_validation M w' p1
    | Dia      p1    => exists w': World, relacao (R (F M)) w w' /\ fun_validation M w' p1
    | Neg      p1    => ~ fun_validation M w p1
    | And      p1 p2 => fun_validation M w p1 /\ fun_validation M w p2
    | Or       p1 p2 => fun_validation M w p1 \/ fun_validation M w p2
    | Implies  p1 p2 => fun_validation M w p1 -> fun_validation M w p2 
    end.

Notation "M ' w ||- B" := (fun_validation M w B) (at level 110, right associativity).

    (* Model satisfazibility *)
Definition validate_model (M : Model) (p : formulaModal) : Prop :=
    forall w: World,  In w (W (F M)) -> fun_validation M w p.

Notation "M |= B" := (validate_model M B) (at level 110, right associativity).

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

(***** structural properties of deduction ****)


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

(* Representação de diferentes Frames *)


Lemma relacao_pertinencia_mundos: 
    forall (M: Model) (w w': World) , 
        relacao (R (F M)) w w' -> (In w (W (F M)) /\ In w' (W (F M))).
Proof.
    intros.
    split.
Admitted.


(* Reflexividade *)
Definition reflexivity_frame (F: Frame) : Prop :=
    forall w: World, (In w (W F)) -> relacao (R F) w w.


Theorem validacao_frame_reflexivo:
    forall (M: Model) (p: formulaModal),
    ((reflexivity_frame (F M)) -> (M |= .[] p .-> p)). 
Proof.
    intros.
    unfold validate_model.
    intros.
    unfold reflexivity_frame in *. simpl in *.
    intros. 
    apply H1 with (w':=w0).
    apply H with (w:=w0).
    apply H0.
Qed.


(* Transitividade *)
Definition transitivity_frame (F: Frame) : Prop :=
    forall w w' w'' : World, (In w (W F) /\ In w' (W F) /\ In w'' (W F)) -> ((relacao (R F) w w' /\ relacao (R F) w' w'') -> relacao (R F) w w'').
    


Theorem validacao_frame_transitivo: 
    forall (M: Model) (p: formulaModal),
    ((transitivity_frame (F M)) -> (M |= .[]p .-> .[].[]p)).
Proof.
    intros.
    unfold validate_model.
    simpl.
    intros w H0 H1 w' H2 w'' H3.
    unfold transitivity_frame in *.
    apply H1.
    apply H  with (w:=w) (w':=w') (w'':=w'').
    split. apply H0. 
    apply relacao_pertinencia_mundos in H3 as J.
    apply J.
    split.
    apply H2. apply H3.  
Qed.
             
    
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
    intros w H0 H1.
    (* assert (w':World). apply w. *)
    destruct H with (w:=w).
    exists x.
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
    (* apply relacao_pertinencia_mundos. *)
    apply relacao_pertinencia_mundos in H1 as Hip1.
    apply relacao_pertinencia_mundos in H2 as Hip2.
    destruct Hip1. destruct Hip2.
    split. apply H5. apply H7.
    split. apply H1. apply H2. apply H3.
Qed.


(* Densa DEFINIÇÃO ERRADA*)
Definition dense_frame (F: Frame) : Prop :=
    forall w w' w'' : World, (In w (W F) /\ In w' (W F) /\ In w'' (W F)) -> (relacao (R F) w w' -> (relacao (R F) w w'' /\ relacao (R F) w' w'')).


Theorem validacao_frame_densa:
    forall (M: Model) (p: formulaModal),
    (dense_frame (F M)) -> (M |= .[] .[] p .-> .[] p).
Proof.
    intros.
    unfold validate_model.
    simpl in *.
    unfold dense_frame in *.
    intros.
    apply H1 with (w':=w0) (w'0:=w').

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
    intros. induction M.
    split.
        - simpl in *.

Admitted.



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