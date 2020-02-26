(*  Name: Ariel Agne da Silveira

    <Modal Logic Library>

*)

Require Import Arith List ListSet Classical.

Inductive formulaModal : Set :=
    | Lit          : nat -> formulaModal
    | Neg          : formulaModal -> formulaModal
    | Box          : formulaModal -> formulaModal
    | Dia          : formulaModal -> formulaModal
    | And          : formulaModal -> formulaModal -> formulaModal
    | Or           : formulaModal -> formulaModal -> formulaModal
    | Implies      : formulaModal -> formulaModal -> formulaModal 
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
Fixpoint sizeModal (f:formulaModal) : nat :=
    match f with 
    | Lit      x     => 1
    | Neg      p1    => 1 + (sizeModal p1)
    | Box      p1    => 1 + (sizeModal p1)
    | Dia      p1    => 1 + (sizeModal p1)
    | And      p1 p2 => 1 + (sizeModal p1) + (sizeModal p2)
    | Or       p1 p2 => 1 + (sizeModal p1) + (sizeModal p2)
    | Implies  p1 p2 => 1 + (sizeModal p1) + (sizeModal p2)
end.

Definition ex1 := #0 .\/ #1.
Definition ex2 := #1 .-> .~ #2 .-> #0 .\/ (#1 .\/ #2).
Definition ex3 := .~.~ #0 .-> #1.
    
(* Definition list_world : list nat := 3 :: 2 :: nil. *)

Check sizeModal ex1.
Compute sizeModal ex3.

Fixpoint literals (f:formulaModal) : set nat :=
match f with 
| Lit      x     => set_add eq_nat_dec x (empty_set nat)
| Dia      p1    => literals p1
| Box      p1    => literals p1
| Neg      p1    => literals p1
| And      p1 p2 => set_union eq_nat_dec (literals p1) (literals p2)
| Or       p1 p2 => set_union eq_nat_dec (literals p1) (literals p2)
| Implies  p1 p2 => set_union eq_nat_dec (literals p1) (literals p2) 
end.

Fixpoint valuation (p: nat -> bool) (f:formulaModal) : bool :=
match f with
| Lit     x        => p x
| Box     x1       => [] (valuation p x1)
| Dia     x1       => .<> (valuation p x1)
| Neg     x1       => negb (valuation p x1)
| And     x1 x2    => (valuation p x1) && (valuation p x2)
| Or      x1 x2    => (valuation p x1) || (valuation p x2)
| Implies x1 x2    => (negb (valuation p x1)) || (valuation p x2)
end.

Check literals ex2.
(* 

(* Example of basic literal valuation *)

Fixpoint evenb (x:nat) : bool :=
match x with
  | O   => true
  | S x => negb (evenb x)
end.

Check   valuation evenb ex1.
Compute valuation evenb ex1.

(* Inductive World := natlist. *)
(* Definition world : natlist. *)
(* Inductive Model : Type :=
    | w : natlist
    | R : w -> w -> Prop. *)

(* Theorem verify_world : (l : natlist )
    (r : Acessibility) (w : l) (p : formula), 
    w |= p.
Proof.
Qed.

 *)
(* Ltac prop_world p w :=  *)
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

(* Theorem test : 1 <> 2. *)
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