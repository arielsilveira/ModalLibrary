Require Import Modal_Library Classical List Utf8.


(* p -> (q -> p) *)
Theorem Hilbert_Axiom_1:
    forall (M: Model) (w: W (F M)) (φ ψ: modalFormula),
        (M ' w ||- (φ .-> (ψ .-> φ))).
Proof.
    - intros.
        simpl in *.
        intros. 
        apply H.
Qed.


(* (p -> (q -> r)) -> ((p -> q) -> (p -> r)) *)
Theorem Hilbert_Axiom_2:
    forall (M: Model) (w: W (F M)) (φ ψ Ɣ: modalFormula),
        (M ' w ||- (φ .-> (ψ .-> Ɣ)) .-> ((φ .-> ψ) .-> (φ .-> Ɣ))).
Proof.
    - simpl.
        intros.
        apply H. 
            + auto.
            + apply H0. auto.
Qed.


(* (~ q -> ~ p) -> (p -> q) *)
Theorem Hilbert_Axiom_3:
    forall (M: Model) (w: W (F M)) (φ ψ: modalFormula),
        (M ' w ||- (.~ ψ .-> .~ φ) .-> (φ .-> ψ)).
Proof.
    - simpl.
        intros.
        pose (classic (M ' w ||- ψ)) as Hip.
        destruct Hip. 
            + auto. 
            + apply H in H1. contradiction.
Qed.


Theorem Hilbert_Axiom_4: 
    forall (M: Model) (w: W (F M)) (φ ψ: modalFormula),
        (M ' w ||- (φ .-> (ψ .-> (φ ./\ ψ)))).
Proof.
    - simpl.
        intros.
        split;
        auto. 
Qed.

Theorem Hilbert_Axiom_5: 
    forall (M: Model) (w: W (F M)) (φ ψ: modalFormula),
        (M ' w ||- (φ ./\ ψ) .-> φ).
Proof.
    - simpl.
        intros.
        destruct H as [Hip1 Hip2].
            + apply Hip1.
Qed.

Theorem Hilbert_Axiom_6: 
    forall (M: Model) (w: W (F M)) (φ ψ: modalFormula),
        (M ' w ||- (φ ./\ ψ) .-> ψ) .
Proof.
    - simpl.
        intros.
        destruct H as [Hip1 Hip2].
            + apply Hip2. 
Qed.

Theorem Hilbert_Axiom_7: 
    forall (M: Model) (w: W (F M)) (φ ψ: modalFormula),
        (M ' w ||- (φ .-> (φ .\/ ψ))).
Proof.
    - simpl.
        intros.
        left.
        apply H.
Qed.

Theorem Hilbert_Axiom_8: 
    forall (M: Model) (w: W (F M)) (φ ψ: modalFormula),
        (M ' w ||- (ψ .-> (φ .\/ ψ))).
Proof.
    - simpl.
        intros.
        right.
        apply H.
Qed.

Theorem Hilbert_Axiom_9: 
    forall (M: Model) (w: W (F M)) (φ ψ Ɣ: modalFormula),
        (M ' w ||- (φ .-> Ɣ) .-> (ψ .-> Ɣ) .-> (φ .\/ ψ) .-> Ɣ).
Proof.
    - simpl.
        intros.
        destruct H1. 
            + apply H.
                apply H1.
            + apply H0.
                apply H1.
Qed.    

Theorem Hilbert_Axiom_10: 
    forall (M: Model) (w: W (F M)) (φ: modalFormula),
        (M ' w ||- .~.~φ .-> φ).
Proof.
    - simpl.
        intros.
        apply NNPP in H.
        apply H.
Qed.

(* <>(p \/ q) -> (<>p \/ <>q) *)
Theorem Axiom_Possibility:
    forall (M: Model) (w: W (F M)) (φ ψ : modalFormula),
        (M ' w ||- .<> (φ .\/ ψ) .-> (.<> φ .\/ .<> ψ)) .
Proof.
    - simpl.
        intros.
        destruct H as [w' [Hip1 [Hip2 | Hip3] ]].
            + left; exists w'; split.
                * auto.
                * auto.
            + right; exists w'; split.
                * auto.
                * auto.
Qed.
    
(* [](p -> q) -> ([]p -> []q) *)
Theorem Axiom_K:
    forall (M: Model) (w: W (F M)) (φ ψ : modalFormula),
        (M ' w ||- .[](φ .-> ψ) .-> (.[]φ .-> .[]ψ)) .
Proof.
    - simpl in *.
        intros. apply H. 
        + apply H1. 
        + apply H0. auto.
Qed.

Theorem caso_2 :
    forall (G : theory) (phi: modalFormula),
        (In phi G) -> G ||= phi.
Proof.
    - unfold entails_modal;
        unfold validate_model.
        intros. 
Admitted.

(* a /\ a->b -> b *)
Theorem Modus_Ponens:
    forall (M: Model) (w: W (F M)) (φ ψ: modalFormula),
        ((M ' w ||- φ) /\ (M ' w ||- φ .-> ψ)) -> (M ' w ||- ψ).
Proof.
    - simpl in *.
        intros.
        destruct H.
        apply H0. auto.
Qed.


Theorem Necessitation:
    forall (M: Model) (φ: modalFormula),
        (M |= φ) -> (M |= .[]φ).
Proof.
    - unfold validate_model.
        simpl in *.
        intros.
        apply H.
Qed.