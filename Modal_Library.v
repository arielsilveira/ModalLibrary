Require Import Propositional_Library.

(*Rever o model checking para saber se não vai dar conflito
com o inductive da Propositional_Library*)

Inductive formula_Modal : Set :=
    | Lit          : nat -> formula_Modal
    | Neg          : formula_Modal -> formula_Modal
    | Box          : formula_Modal -> formula_Modal
    | Dia          : formula_Modal -> formula_Modal
    | And          : formula_Modal -> formula_Modal -> formula_Modal
    | Or           : formula_Modal -> formula_Modal -> formula_Modal
    | Implies      : formula_Modal -> formula_Modal -> formula_Modal 
    | formula_Prop : formula
.

Notation " X .-> Y "  := (Implies X Y) (at level 13, right associativity).
Notation " X .\/ Y "  := (Or X Y)      (at level 12, left associativity).
Notation " X ./\ Y"   := (And X Y)     (at level 11, left associativity).
Notation " .~ X "     := (Neg X)       (at level 10, right associativity).
Notation " .[] X "    := (Box X)       (at level 'x', right associativity).
Notation " .<> X "    := (Dia X)       (at level 'x', right associativity).
Notation " # X "      := (Lit X)       (at level 1, no associativity).

(* Calcula o tamanho de uma fórmula com base na lógica modal *)
Fixpoint size (f:formula_Modal) : nat :=
    match f with 
    | Lit      x     => 1
    | Neg      p1    => 1 + (size p1)
    | Box      p1    => 1 + (size p1)
    | Dia      p1    => 1 + (size p1)
    | And      p1 p2 => 1 + (size p1) + (size p2)
    | Or       p1 p2 => 1 + (size p1) + (size p2)
    | Implies  p1 p2 => 1 + (size p1) + (size p2)
    end.

Definition ex1_modal := .<> #0 .\/ #1.
Definition ex2_modal := #1 .-> .[] .~ #2 .-> .<> #0 .\/ (#1 .\/ #2).
Definition ex3_modal := .~.~ .<> #0 .-> .[] #1.
    
Check size ex1.
Compute size ex1.