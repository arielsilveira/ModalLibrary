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

Notation "[ ]" := nil.
Notation "x :: l" := (cons x l)
                     (at level 60, right associativity).
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).


Definition world := [0;1;2;3;4].
Definition relation_world := [(0,1);(1,1);(1,2);(2,0);(2,3);(3,1);(3,3);(3,4)].

Fixpoint eqb (n m : nat) : bool :=
  match n with
  | O => match m with
         | O => true
         | S m' => false
         end
  | S n' => match m with
            | O => false
            | S m' => eqb n' m'
            end
  end.

(* Search world relation with all worlds on lists *)
Fixpoint world_relations_list_worlds (w : nat) (R : list (nat * nat)) : list nat :=
match R with
    | nil => nil
    | h :: t => if eqb (fst h) w then (snd h) :: (world_relations_list_worlds w t) else (world_relations_list_worlds w t)
end.

(* Search all worlds relations with all worlds on lists *)
Fixpoint list_worlds_relations_list_worlds (w : list nat) (R : list (nat * nat)) : list (list nat) :=
    match w with
    | nil => nil
    | h :: t => (world_relations_list_worlds h R) :: (list_worlds_relations_list_worlds t R)
    end.

(* Return a list with all relations, where each position is a list of relation *)
Compute list_worlds_relations_list_worlds world relation_world.

Definition lista_prop : list nat := [ ].
Compute lista_prop.

(* Rever essa parte para saber como deixar um vetor de pair com uma lista em snd *)
(* [(prop, [worlds]);(prop, [worlds]);(prop, [worlds]);(prop, [worlds])] *)

Definition prop_world (phi : formulaModal) (w : list nat) : list (formulaModal * list nat) :=
lista_prop ++ [pair phi w].

Compute prop_world (#1 ./\ #2) [1;2;3;4].
Check lista_prop.

(*Fixpoint valuation (p: nat -> bool) (f:formulaModal) : bool :=
match f with
| Lit     x        => p x
| Box     x1       => .[] (valuation p x1) //REVER ESTE TRECHO PARA ANÁLISE DE MUNDOS POSSÍVEIS
| Dia     x1       => .<> (valuation p x1)  //REVER ESTE TRECHO PARA ANÁLISE DE MUNDOS POSSÍVEIS
| Neg     x1       => negb (valuation p x1)
| And     x1 x2    => (valuation p x1) && (valuation p x2)
| Or      x1 x2    => (valuation p x1) || (valuation p x2)
| Implies x1 x2    => (negb (valuation p x1)) || (valuation p x2)
end.
*)

(* Example of basic literal valuation *)

(* Fixpoint evenb (x:nat) : bool :=
match x with
  | O   => true
  | S x => negb (evenb x)
end.

Check   valuation evenb ex1.
Compute valuation evenb ex1. *)

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
(* Definition prop_world (phi : formulaModal) (w : list nat) -> list (nat * list nat) :=
match  p [phi :: w].  *)
(* Comando Compute para ver se esta funcionando o Ltac *)
(* https://github.com/coq/coq/wiki/Ltac *)
(* https://coq.inria.fr/refman/proof-engine/ltac.html#grammar-token-cpattern *)
Definition Ideia  prop_worlphi (f : formulaModal) (w : list nat) -> list (nat * list nat) :=
[phi :: w].mula [world_1; world_2;...;world_n]*)
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