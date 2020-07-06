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
    destruct Hip. auto. apply H in H1. contradiction.
Qed.


(* [](p /\ q) -> ([]p /\ []q) *)
Theorem Axiom_K:
    forall (M: Model) (w: W (F M)) (p q : formulaModal),
    (M ' w ||- .[](p ./\ q) .-> (.[]p ./\ .[]q)) .
Proof.
    intros.
    simpl in *.
    split.
    intros. destruct H with (w':=w'). apply H0. apply H1.
    intros. destruct H with (w':=w'). apply H0. apply H2.
Qed.

