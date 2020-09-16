Require Import Modal_Library Classical          .
(* Nat Arith Classical_Prop Logic Utf8 ListSetLogic Notations Classical List Relation_Definitions*)

(* Prova de validação do Frame Reflexivo *)

Theorem validacao_frame_reflexivo_ida:
	forall M Ψ,
	reflexivity_frame (F M) ->
	(M |= .[] Ψ .-> Ψ).
Proof.
	intros;
	unfold validate_model in *;
	simpl in *; intuition.
Qed.

Theorem validacao_frame_reflexivo_volta:
	forall M Ψ,
	~ reflexivity_frame (F M) ->
	~ (M |= .[] Ψ .-> Ψ).
Proof.
	intros;
	unfold reflexivity_frame, not, validate_model in *;
	simpl in H.
	intros.
	apply H.	
Admitted.


(* Prova de validação do Frame Transitivo *)

Theorem validacao_frame_transitivo_ida: 
    forall (M : Model) (φ : modalFormula),
    ((transitivity_frame (F M)) -> (M |= .[]φ .-> .[].[]φ)).
Proof. 
    - intros.
        unfold validate_model.
        simpl.
        intros.
        unfold transitivity_frame in *.
        apply H0.
        apply H  with (w:=w) (w':=w') (w'':=w'0).
        split. 
            + apply H1. 
            + apply H2. 
Qed.


Theorem validacao_frame_transitivo_volta: 
    forall (M: Model) (φ : modalFormula),
    (M |= .[]φ .-> .[].[]φ) -> (transitivity_frame (F M)).
Proof.
Admitted.

(* Prova de validação do Frame Simétrico *)

Theorem validacao_frame_simetria_ida: 
    forall (M : Model) (φ : modalFormula),
    (simmetry_frame (F M)) -> (M |= φ .-> .[] .<> φ).
Proof.
    - intros.
        unfold validate_model.
        simpl in *.
        intros.
        exists w.
        apply and_comm.
        split.
        + apply H0.
        + unfold simmetry_frame in *.
            apply H. apply H1.
Qed.

Theorem validacao_frame_simetria_volta: 
    forall (M : Model) (φ :modalFormula),
    ((M |= φ .-> .[] .<> φ) -> (simmetry_frame (F M))).
Proof.    
Admitted.

(* Prova de validação do Frame Euclidiano *)

Theorem validacao_frame_eucliadiana_ida: 
    forall (M : Model) (φ : modalFormula),
    (euclidian_frame (F M)) -> (M |= .<> φ .-> .[] .<> φ).
Proof.
    - intros.
        unfold euclidian_frame in *.
        unfold validate_model.
        simpl in *.
        intros.
        destruct H0 as [x [Hip1 Hip2]].
        exists x.
        split.
        + apply H with (w:=w) (w':=w') (w'':=x).
            split. 
                * auto. 
                * auto. 
        + auto.
Qed.


Theorem validacao_frame_eucliadiana_volta: 
    forall (M : Model) (φ : modalFormula),
    (((M |= .<> φ .-> .[] .<> φ) -> (euclidian_frame (F M)) )).
Proof.
Admitted.


(* Prova de validação do Frame Serial *)

Theorem validacao_frame_serial_ida: 
    forall (M: Model) (φ: modalFormula),
    (serial_frame (F M)) -> (M |= .[] φ .-> .<> φ).
Proof.
    - unfold validate_model.
        unfold serial_frame in *.   
        simpl in *.
        intros.
        destruct H with (w:=w).
        exists x. 
        split. 
            + auto.
            + apply H0 in H1. apply H1.
Qed.

Theorem validacao_frame_serial_volta: 
    forall (M : Model) (φ : modalFormula),
    ((M |= .[] φ .-> .<> φ) -> (serial_frame (F M))).
Proof.   
Admitted.


(* Prova de validação do Frame Funcional *)
Theorem validacao_frame_funcional_ida:
    forall (M : Model) (φ : modalFormula),
    (functional_frame (F M)) -> (M |= .<> φ .-> .[] φ).
Proof.
    - intros; 
        unfold validate_model; 
        unfold functional_frame in *.
        simpl in *.
        intros w H0 w1 H1.
        destruct H0 as [w' [H0 H2]].
        destruct H with (w:=w) (w':=w1) (w'':=w').
            + split. 
                * apply H1. 
                * apply H0. 
            + apply H2.
Qed.

Theorem validacao_frame_funcional_volta:
    forall (M : Model) (φ : modalFormula),
     (M |= .<> φ .-> .[] φ) -> (functional_frame (F M)).
Proof.
Admitted.


(* Prova de validação do Frame Denso *)
Theorem validacao_frame_densa_ida:
    forall (M : Model) (φ : modalFormula),
    (dense_frame (F M) ->  (M |= .[] .[] φ .-> .[] φ)).
Proof.
Admitted.


Theorem validacao_frame_densa_volta:
    forall (M: Model) (φ: modalFormula),
    ((M |= .[] .[] φ .-> .[] φ) -> dense_frame (F M)).
Proof.
Admitted.


(* Prova de validação do Frame Convergente *)

Theorem validacao_frame_convergente_ida:
    forall (M: Model) (p: modalFormula),
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
    forall (M: Model) (p: modalFormula),
     (* ~(convergente_frame (F M) -> ~(M |= .<> .[] p .-> .[] .<> p)). *)
     ~ ((M |= .<> .[] p .-> .[] .<> p) -> convergente_frame (F M)).
Proof.
Admitted.