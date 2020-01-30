(*  Name: Ariel Agne da Silveira

    <Modal Logic Library>

*)

Require Import Arith List ListSet Classical.

Inductive formula : Set :=
    | Lit          : nat -> formula
    | Neg          : formula -> formula
    | Box          : formula -> formula
    | Dia          : formula -> formula
    | And          : formula -> formula -> formula
    | Or           : formula -> formula -> formula
    | Implies      : formula -> formula -> formula 
.

(* Tentar ver como colocar se uma fórmula é modal ou proposicional *)
(* Ver a precedencia dos operadores unários *)
Notation " X .-> Y "  := (Implies X Y) (at level 13, right associativity).
Notation " X .\/ Y "  := (Or X Y)      (at level 12, left associativity).
Notation " X ./\ Y"   := (And X Y)     (at level 11, left associativity).
Notation " .~ X "     := (Neg X)       (at level 10, right associativity).
Notation " .[] X "    := (Box X)       (at level 10, right associativity).
Notation " .<> X "    := (Dia X)       (at level 10, right associativity).
Notation " # X "      := (Lit X)       (at level 1, no associativity).

(* Calcula o tamanho de uma fórmula com base na lógica modal *)
Fixpoint size (f:formula) : nat :=
    match f with
    | Lit      x     => 1
    | Neg      p1    => 1 + (size p1)
    | Box      p1    => 1 + (size p1)
    | Dia      p1    => 1 + (size p1)
    | And      p1 p2 => 1 + (size p1) + (size p2)
    | Or       p1 p2 => 1 + (size p1) + (size p2)
    | Implies  p1 p2 => 1 + (size p1) + (size p2)
    end.

Definition ex1 := .<> #0 .\/ #1.
Definition ex2 := #1 .-> .[] .~ #2 .-> .<> #0 .\/ (#1 .\/ #2).
Definition ex3 := .~.~ .<> #0 .-> .[] #1.
    
Check size ex1.
Compute size ex3.

Ltac prop_world p w := 
(* Comando Compute para ver se esta funcionando o Ltac *)
(* https://github.com/coq/coq/wiki/Ltac *)
(* https://coq.inria.fr/refman/proof-engine/ltac.html#grammar-token-cpattern *)

(* Ideia: prop_world formula [world_1; world_2;...;world_n]*)
(* 
    P -> 2^w
    p0 -> []
    p1 -> [w2, w4]
    p2 -> [w1, w3]

    Construir o Ltac para gravar cada proposição 
     presente em um mundo


*)
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