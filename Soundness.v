Require Import Modal_Library.

Theorem Hilbert_Axiom_1:
    forall (M: Model) (w: W (F M)) (p q: formulaModal),
        (M ' w ||- p .-> (q .-> p)).
Proof.
Admitted.


Theorem Hilbert_Axiom_2:
    forall (M: Model) (w: W (F M)) (p q r: formulaModal),
        (M ' w ||- (p .-> (q .-> r)) .-> ((p .-> q) .-> (p .-> r))).
Proof.
Admitted.



Theorem Hilbert_Axiom_3:
    forall (M: Model) (w: W (F M)) (p q: formulaModal),
        (M ' w ||- (.~ q .-> .~ p) .-> (p .-> q)).
Proof.
Admitted.

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

