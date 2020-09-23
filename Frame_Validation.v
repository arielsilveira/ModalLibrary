Require Import Modal_Library Classical.

Theorem validation_frame_reflexivo_ida:
	forall M Ψ,
	reflexivity_frame (F M) ->
	(M |= .[] Ψ .-> Ψ).
Proof.
	intros;
	unfold validate_model in *;
	simpl in *; intuition.
Qed.

Theorem validation_frame_reflexivo_volta:
  forall M Ψ,
  (M |= .[] Ψ .-> Ψ) -> 
  reflexivity_frame (F M).
Proof.
Admitted.


Theorem validation_frame_transitivo_ida: 
  forall M φ,
  transitivity_frame (F M) -> 
  (M |= .[]φ .-> .[].[]φ).
Proof. 
  unfold validate_model, transitivity_frame.
  simpl; intros.
  apply H0.
  eapply H; split. 
  - apply H1. 
  - assumption. 
Qed.


Theorem validation_frame_transitivo_volta: 
  forall M φ,
  (M |= .[]φ .-> .[].[]φ) -> 
  transitivity_frame (F M).
Proof.
Admitted.

Theorem validation_frame_simetria_ida: 
  forall M φ,
  simmetry_frame (F M) -> 
  (M |= φ .-> .[] .<> φ).
Proof.
  unfold validate_model, simmetry_frame.
  simpl in *; intros; exists w.
  apply and_comm; split.
  - apply H0.
  - eauto.
Qed.

Theorem validation_frame_simetria_volta: 
  forall M φ,
  (M |= φ .-> .[] .<> φ) -> 
  simmetry_frame (F M).
Proof.    
Admitted.

Theorem validation_frame_eucliadiana_ida: 
  forall M φ,
  euclidian_frame (F M) -> 
  (M |= .<> φ .-> .[] .<> φ).
Proof.
  unfold euclidian_frame, validate_model.
  simpl in *; intros.
  edestruct H0.
  exists x; split.
  - eapply H; split. 
    * apply H1. 
    * intuition. 
  - intuition.
Qed.

Theorem validation_frame_eucliadiana_volta: 
  forall M φ,
  (M |= .<> φ .-> .[] .<> φ) -> 
  euclidian_frame (F M).
Proof.
Admitted.

Theorem validation_frame_serial_ida: 
  forall M φ,
  serial_frame (F M) -> 
  (M |= .[] φ .-> .<> φ).
Proof.
  unfold validate_model, serial_frame.   
  simpl in *; intros.
  edestruct H.
  exists x; split. 
  - apply H1.
  - eauto.
Qed.

Theorem validation_frame_serial_volta: 
  forall M φ,
  (M |= .[] φ .-> .<> φ) -> 
  serial_frame (F M).
Proof.   
Admitted.


Theorem validation_frame_funcional_ida:
  forall M φ,
  functional_frame (F M) -> 
  (M |= .<> φ .-> .[] φ).
Proof.
  intros; unfold validate_model; 
  unfold functional_frame in *.
  intros w H0 w1 H1.
  edestruct H0.
  edestruct H with (w:=w) (w':=w1) (w'':=x).
  - split. 
    + apply H1. 
    + intuition. 
  - intuition.
Qed.

Theorem validation_frame_funcional_volta:
  forall M φ,
  (M |= .<> φ .-> .[] φ) -> 
  functional_frame (F M).
Proof.
Admitted.


Theorem validation_frame_densa_ida:
  forall M φ,
  dense_frame (F M) -> 
  (M |= .[] .[] φ .-> .[] φ).
Proof.
Admitted.


Theorem validation_frame_densa_volta:
  forall M φ,
  (M |= .[] .[] φ .-> .[] φ) -> 
  dense_frame (F M).
Proof.
Admitted.

Theorem validation_frame_convergente_ida:
  forall M φ,
  convergente_frame (F M) -> 
  (M |= .<> .[] φ .-> .[] .<> φ).
Proof.
  unfold convergente_frame, validate_model.
  simpl in *; intros.
  edestruct H0.
  destruct H with (w:=w) (x:=x) (y:=w').
  destruct H0; auto.
  exists x0.
  split; intuition.
Qed.

Theorem validation_frame_convergente_volta:
  forall (M: Model) (φ: modalFormula),
  (M |= .<> .[] φ .-> .[] .<> φ) -> 
  convergente_frame (F M).
Proof.
Admitted.
