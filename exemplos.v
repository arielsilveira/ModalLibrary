Require Import Modal_Library.
(* Arquivo para criar testes. *)

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