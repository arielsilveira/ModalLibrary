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

(* Check sizeModal ex1.
Compute sizeModal ex3. *)

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

(* Exemplo de teste *)

Definition world := [0;1;2;3;4].
Definition relation_world := [(0,1);(1,1);(1,2);(2,0);(2,3);(3,1);(3,3);(3,4)].

Definition x := list_worlds_relations_list_worlds world relation_world.
Compute x.

Definition lista_prop : list nat := [ ].
Compute lista_prop.

(* Fim do exemplo de teste *)


(* Anotações importantes para próximo uso *)
(* 
    Dar uma olhada em argumentos implícitos, passar como parâmetro e salvá-las
    Construir um Definition que recebe esse argumento, tal como vetor vazio,
    desta forma, concateno o retorno da lista com este argumento. Como por exemplo
    [] ++ (funcao mundos relações)


    [(prop, [worlds]);(prop, [worlds]);(prop, [worlds]);(prop, [worlds])]
*)


(* Rever essa parte para saber como deixar um vetor de pair com uma lista em snd *)
Definition prop_world (phi : formulaModal) (w : list nat) : list (formulaModal * list nat) :=
lista_prop ++ [pair phi w].

Compute prop_world (#1 ./\ #2) [1;2;3;4].
Check lista_prop.


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
