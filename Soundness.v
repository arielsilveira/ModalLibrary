Require Import Modal_Library Classical.


(* p -> (q -> p) *)
Theorem Hilbert_Axiom_1:
    forall (M: Model) (w: W (F M)) (p q: formulaModal),
        (M ' w ||- (p .-> (q .-> p))).
Proof.
    intros.
    simpl in *.
    intros. apply H.
Qed.


(* (p -> (q -> r)) -> ((p -> q) -> (p -> r)) *)
Theorem Hilbert_Axiom_2:
    forall (M: Model) (w: W (F M)) (p q r: formulaModal),
        (M ' w ||- (p .-> (q .-> r)) .-> ((p .-> q) .-> (p .-> r))).
Proof.
    simpl.
    intros.
    apply H. auto.
    apply H0. auto.
Qed.


(* (~ q -> ~ p) -> (p -> q) *)
Theorem Hilbert_Axiom_3:
    forall (M: Model) (w: W (F M)) (p q: formulaModal),
        (M ' w ||- (.~ q .-> .~ p) .-> (p .-> q)).
Proof.
    simpl.
    intros.
    pose (classic (M ' w ||- q)) as Hip.
    destruct Hip. auto. 
    apply H in H1. contradiction.
Qed.


(* [](p -> q) -> ([]p -> []q) *)
Theorem Axiom_K:
    forall (M: Model) (w: W (F M)) (p q : formulaModal),
    (M ' w ||- .[](p .-> q) .-> (.[]p .-> .[]q)) .
Proof.
    simpl in *.
    intros. apply H. apply H1. apply H0. auto.
Qed.

(* a /\ a->b -> b *)
Theorem Modus_Ponens:
    forall (M: Model) (w: W (F M)) (p q: formulaModal),
    ((M ' w ||- p) /\ (M ' w ||- p .-> q)) -> (M ' w ||- q).
Proof.
    simpl in *.
    intros.
    destruct H.
    apply H0. auto.
Qed.


Theorem Necessitation:
    forall (M: Model) (p: formulaModal),
        (M |= p) -> (M |=.[]p).
Proof.
    unfold validate_model.
    simpl in *.
    intros.
    apply H.
Qed.