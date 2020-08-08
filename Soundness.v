Require Import Modal_Library Classical.


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
        (M |= φ) -> (M |=.[]φ).
Proof.
    - unfold validate_model.
        simpl in *.
        intros.
        apply H.
Qed.