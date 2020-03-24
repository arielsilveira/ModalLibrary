(* Arquivo para criar testes. *)
Require Import Modal_Library.

(* Construçao de fórmulas *)
Definition form1 := .[] #0 .\/ #1.
Definition form2 := #1 .-> .~ .[] #2 .-> #0 .\/ .[](.<> #1 .\/ #2).
Definition form3 := .~.~ #0 .-> #1.

(* Definição do Mundos e Relações *)
Definition world_in_model := [w 0; w 1;w 2; w 3; w 4]. 
Definition relation_world :=  [ (w 1, w 9); (w 0, w 1); (w 1, w 1);
                                (w 1, w 2); (w 2, w 0); (w 2, w 3);
                                (w 3, w 1); (w 3, w 3); (w 3, w 4)
                              ].

(* Valida as relações entre mundos *)
Definition rel := validate_relation world_in_model relation_world.

(* Declaração do Frame *)
Definition F := frame world_in_model rel.

Check F.
Compute (W F).
Compute (R F).
(* Definition a  := frame world relation_world. *)

(* Talvez seja útil *)
(* Inicio dos exemplos de Relação *)
(* Example ex1: Relation [1; 2; 3] 2 3.
Proof.
  apply r.
    - simpl. auto.
    - simpl. auto.
Qed.

Example ex2: ~Relation [1; 2; 3] 1 5.
Proof.
  unfold not. intros. inversion H. inversion H1. discriminate H4. inversion H4. 
  discriminate H5. inversion H5. discriminate H6. inversion H6.
Qed.

Example ex3: Relation [1;2;3] 2 5 -> False.
Proof.
  intros. inversion H. inversion H1. discriminate H4. inversion H4. 
  discriminate H5. inversion H5. discriminate H6. inversion H6.
Qed. *)


