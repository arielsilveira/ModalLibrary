Require Import Modal_Library.

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
    intros.
    split.
        - unfold entails_teste.
            simpl in *.
            unfold validate_model.
            simpl in *. 
            intros.
            unfold not in *.
            destruct H0. destruct H0 with (w:=w).
            intros.
            apply H with (M:=M) (w:=w).
            apply and_comm; split; auto.
            intros. exists w'. apply and_comm.
            split; auto.
            
Admitted.