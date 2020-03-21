Require Import Modal_Library.
(* Arquivo para criar testes. *)

(* Construçao de fórmulas *)
Definition form1 := .[] #0 .\/ #1.
Definition form2 := #1 .-> .~ .[] #2 .-> #0 .\/ .[](.<> #1 .\/ #2).
Definition form3 := .~.~ #0 .-> #1.

(* Definição de Modelo *)
(* Definition world := [0;1;2;3;4]. Precisa ver se é necessário isso
Definition relation_world := [(0,1);(1,1);(1,2);(2,0);(2,3);(3,1);(3,3);(3,4)]. *)

Definition world_in_model := [w 0; w 1;w 2; w 3; w 4]. (*Precisa ver se é necessário isso*)
Definition relation_world := [(w 1, w 9);(w 0,w 1);(w 1,w 1);(w 1,w 2);(w 2,w 0);(w 2,w 3);(w 3, w 1);(w 3,w 3);(w 3, w 4)].

Definition rel := validate_relation world_in_model relation_world.
(* Compute relacionamento world_in_model relation_world. *)


Definition construction_frame := frame world_in_model rel.

Check construction_frame.
Compute (W construction_frame).
Compute (R construction_frame).
(* Definition a  := frame world relation_world. *)


(* Inicio dos exemplos de Relação *)
Example ex1: Relation [1; 2; 3] 2 3.
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
Qed.


