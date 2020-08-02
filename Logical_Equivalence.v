Require Import Modal_Library Classical.

(* Implicação <-> Negação e Disjunção *)
Theorem implies_to_or_modal : 
    forall (a b: formulaModal),
        (a .-> b)  =|=  (.~ a) .\/ b .
Proof.
    intros.
    split.
        - intros. 
            unfold entails_teste in *. 
            intros. 
            simpl in *.
            destruct H0. 
            unfold validate_model in *. 
            simpl in *.
            intro w.
            apply or_to_imply. apply H0.
        - intros.
            unfold entails_teste in *. 
            intros. 
            simpl in *.
            destruct H0. 
            unfold validate_model in *.
            intros.
            simpl in *.
            apply imply_to_or. auto. 
Qed.

(* Dupla Negação *)
Theorem double_neg_modal :
    forall (a : formulaModal),
    (.~ .~ a) =|= a.
Proof.
    intros.
    split.
        - unfold entails_teste.
            simpl in *.
            unfold validate_model.    
            intros.
            destruct H0.
            simpl in *.
            intro.
            pose (classic (M ' w ||-.~.~ a)) as Hip.
            destruct Hip. simpl in *. auto. auto.
        - unfold entails_teste.
            simpl in *.
            unfold validate_model.    
            intros.
            simpl in *.
            destruct H0.
            apply NNPP. apply H0.
Qed.

(* Conjunção <-> Negação e Implicação  *)
Theorem and_to_implies_modal: 
    forall (a b: formulaModal),
    ((a ./\ b) =|= .~ (a .-> .~ b)).
Proof.
    intros.
    split.
        - unfold entails_teste.
            unfold validate_model in *.
            simpl in *.
            intros.
            unfold validate_model in *.
            simpl in *.
            split.
            destruct H0.
                *  pose (classic (M ' w ||- a)) as Hip. 
                    destruct Hip; 
                    auto.
                    assert ((M ' w ||- .~ a) \/ (M ' w ||- .~ b)).
                    left. auto.
                    simpl in *.
                    destruct H0 with (w:=w).
                    intro. contradiction.
                * pose (classic (M ' w ||- b)) as Hip. 
                destruct Hip; 
                auto. 
                assert ((M ' w ||- .~ a) \/ (M ' w ||-.~  b)).
                right. 
                auto. 
                simpl in *.
                destruct H0.
                destruct H0 with (w:=w).
                intro. auto. 
        - unfold entails_teste.
            simpl in *.
            intros.
            unfold validate_model in *.
            intros. 
            simpl in *.
            destruct H0.
            destruct H0 with (w:=w).
            intro.
            destruct H4. auto. auto.
Qed.

(* Diamante <-> Caixa *)
Theorem diamond_to_box_modal:
    forall (a : formulaModal),
    .<> a =|= .~ .[] .~ a.
Proof.
    (* intros. *)
    split.
        - (* We don't need no stinking hypothesis. *)
        intros; clear H.
        unfold entails_teste, validate_model in *.
        simpl in *; intros.
        destruct H as (?, _).
        unfold validate_model in H; simpl in H.
        pose (X := H w).
        (* Either it exists, or it doesn't, right? *)
        edestruct classic.
            + exact H0.
            + exfalso.
                apply X; intros; intro.
                apply H0.
                exists w'; auto.
        - intros. unfold entails_teste in *.
            simpl in *.
            unfold validate_model in *.
            simpl in *. 
            unfold not in *.
            intros.
            destruct H0.
            destruct H with (M:=M) (w:=w).
            split. intros.
            destruct H0 with (w:=w) as [w' [H4 H5]].
            destruct H1 with (w':=w'). auto. auto.
            auto.
            apply H1 with (w':=x). destruct H3 as [H3 H4]; auto. 
            destruct H3 as [H3 H4]; auto.
Qed.