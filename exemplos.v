(*File to create tests. *)
Require Import Modal_Library Deductive_System.

(* Page proof: 22 *)
Lemma Example:
  T; (.[](#0 .-> #1):: .[](#1 .-> #2):: nil) |-- .[](#0 .-> #2) .
Proof.
  (* Line: 16 *)
  apply Nec.
  (* Line: 15 *)
  apply Mp with (f:=(#0 .-> #1)).
    (* Line: 14 *)
  - apply Mp with (f:=(#1 .-> #2)).
      (* Line: 9 *)
    + apply Mp with (f:=((#1 .-> #2) .-> ((#0 .-> (#1 .-> #2))))).
        (* Line: 7 *)
      * apply Mp with (f:=(#1 .-> #2) .-> ((#0 .-> (#1 .-> #2)) .-> (#0 .-> #1) .-> (#0 .-> #2)) ).
          (* Line: 6 *)
        -- apply Ax with (a:=ax2 (#1 .-> #2) (#0 .-> (#1 .-> #2)) ((#0 .-> #1) .-> (#0 .-> #2))).
          ++ constructor. constructor.
          ++ reflexivity.
        (* Line: 5 *)
        -- apply Mp with (f:=(#0 .-> (#1 .-> #2)) .-> ((#0 .-> #1) .-> (#0 .-> #2))).
          (* Line: 3 *)
          ++ apply Ax with (a:= ax1 ((#0 .-> (#1 .-> #2)) .-> ((#0 .-> #1) .-> (#0 .-> #2))) (#1 .-> #2)).
            ** constructor. constructor.
            ** reflexivity.   
          (* Line: 4 *)
          ++ apply Ax with (a:= ax2 #0 #1 #2).
            ** constructor; constructor.
            ** reflexivity.
        (* Line: 8 *)
      * apply Ax with (a:=ax1 (#1 .-> #2) #0).
        -- constructor; constructor.
        -- reflexivity.
      (* Line: 11 *)
    + apply Mp with (f:=.[](#1 .-> #2)).
      * apply Ax with (a:= axT (#1 .-> #2)).
        -- constructor; constructor.
        -- reflexivity.
        (* Line: 2 *)
      * apply Prem with (i:=1).
        reflexivity.
    (* Line: 13 *)
  - apply Mp with (f:=.[](#0 .-> #1)).
      (* Line: 12 *)
    + apply Ax with (a:= axT (#0 .-> #1)).
      * constructor; constructor.
      * reflexivity.
      (* Line: 1 *)
    + apply Prem with (i:=0).
      reflexivity.
Qed.
 