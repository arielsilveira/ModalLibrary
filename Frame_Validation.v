Require Import Modal_Library Classical Logic Arith List ListSet Classical Logic Nat Notations Utf8 Tactics Relation_Definitions Classical_Prop.


(* Prova de validação do Frame Reflexivo *)

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

(* Theorem validacao_frame_reflexivo_volta:
    forall (M: Model) (Ψ: formulaModal),
    ~  ((M |= .[] Ψ .-> Ψ) -> (reflexivity_frame (F M))). *)



Theorem validacao_frame_reflexivo_volta:
    forall (M: Model) (Ψ: formulaModal),
    (~ (reflexivity_frame (F M)) -> ~ (M |= .[] Ψ .-> Ψ)).
Proof.
  intros.
  unfold reflexivity_frame in H.
  unfold validate_model; simpl.
  intro; apply H; clear H; intro.
  destruct classic with (forall w, In (pair w w) (R (F M))).
  - apply H.
  - exfalso.
  
Admitted.







    intros.
    pose (classic (M ' w ||- Ψ)) as Hip.
    destruct Hip. admit.
    destruct H1. apply H0. intros.
    pose (classic (M ' w' ||- Ψ)) as Hip.
    destruct Hip. auto. 
    apply H0. intros.
    apply H1 in H0.
 
Admitted.


(* Prova de validação do Frame Transitivo *)

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


Theorem validacao_frame_transitivo_volta: 
    forall (M: Model) (p: formulaModal),
    (M |= .[]p .-> .[].[]p) -> (transitivity_frame (F M)).
Proof.
    unfold transitivity_frame.
    unfold validate_model.
    simpl in *.
    intros.
    destruct H0.
    apply H with (w:=w) (w':=w') (w'0:=w'') in H1.
    apply H with (w:=w) (w':=w') (w'0:=w'') in H0.

    
Admitted.

(* Prova de validação do Frame Simétrico *)

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

(* Prova de validação do Frame Euclidiano *)

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
    intros.
    unfold euclidian_frame.
    intros. unfold validate_model in *. simpl in *.
    destruct H with (w:=w) (w':=w').
Admitted.


(* Prova de validação do Frame Serial *)

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


(* Prova de validação do Frame Funcional *)
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


(* Prova de validação do Frame Denso *)
Theorem validacao_frame_densa_ida:
    forall (M: Model) (p: formulaModal),
    (dense_frame (F M) ->  (M |= .[] .[] p .-> .[] p)).
Proof.
    unfold validate_model;
    unfold dense_frame;
    simpl in *;
    intros.
    destruct H with (w:=w) (w':=w'). 
    apply H2 in H1.
    destruct H1;
    apply H0 with (w':=x).
        - auto.
        - apply H0 in H3 as Hip. 
    Admitted.


Theorem validacao_frame_densa_volta:
    forall (M: Model) (p: formulaModal),
    ((M |= .[] .[] p .-> .[] p) -> dense_frame (F M)).
Proof.
    unfold validate_model;
    unfold dense_frame;
    simpl in *;
    intros. 
    exists w. intros. 
    apply H with (w':=w') in H0 .
        - admit.
        - intros. apply H with (w:=w'0). 
            + intros. apply H in H4. auto.
                intros. admit.
            + auto.   
Admitted.


(* Prova de validação do Frame Convergente *)

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
     (* ~(convergente_frame (F M) -> ~(M |= .<> .[] p .-> .[] .<> p)). *)
     ~ ((M |= .<> .[] p .-> .[] .<> p) -> convergente_frame (F M)).
Proof.
    unfold validate_model.
    simpl in *.
    unfold convergente_frame.
    unfold not.
    intros. 
Admitted.