(* Biblioteca construída com o enfoque de 
auxiliar o ensino sobre lógica proposicional clássica
a partir da pesquisa realizada por Karina && Machado *)
Require Import Propositional_Library.

(*Rever o model checking para saber se não vai dar conflito
com o inductive da Propositional_Library*)

Inductive formula_Modal : Set :=
    | Lit_Modal          : nat -> formula_Modal
    | Neg_Modal          : formula_Modal -> formula_Modal
    | Box          : formula_Modal -> formula_Modal
    | Dia          : formula_Modal -> formula_Modal
    | And_Modal          : formula_Modal -> formula_Modal -> formula_Modal
    | Or_Modal           : formula_Modal -> formula_Modal -> formula_Modal
    | Implies_Modal      : formula_Modal -> formula_Modal -> formula_Modal 
    (* | formula_Prop : formula *)
.
(* Tentar ver como colocar se uma fórmula é modal ou proposicional *)
(* Ver a precedencia dos operadores unários *)
Notation " X .-> Y "  := (Implies_Modal X Y) (at level 13, right associativity).
Notation " X .\/ Y "  := (Or_Modal X Y)      (at level 12, left associativity).
Notation " X ./\ Y"   := (And_Modal X Y)     (at level 11, left associativity).
Notation " .~ X "     := (Neg_Modal X)       (at level 10, right associativity).
Notation " .[] X "    := (Box X)             (at level 10, right associativity).
Notation " .<> X "    := (Dia X)             (at level 10, right associativity).
Notation " # X "      := (Lit_Modal X)       (at level 1, no associativity).

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

(* Começar a construção de um modelo *)
(* Começar o desenvolvimento de mundos *)
(* Rever as anotações criadas pela Kaqui *)
(* Uma proposição vai ter uma lista de mundos *)
(* Ver como funciona a construção do Ltac *)
(* Saber como construir uma fórmula modal *)
(* Modelar os diferentes sistemas (K, B, D, T, 4, 5...) *)
(* Diferentes propriedades de cada um modelo, dessa forma
será visto cada uma das restrições. Página 29 *)
(* Provar cada metapropriedade do capítulo 2.4 *)
(* Regras: De Morgan, Necessitação e Axiomas *)