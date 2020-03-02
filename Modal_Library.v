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

(* 
    Constroi uma nova notação para listas
*)
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

(* 
    Recebe um mundo e o conjunto de relações como parâmetro
    Retorna uma lista de mundos que há uma relação. 
*)
Fixpoint world_relations_list_worlds (w : nat) (R : list (nat * nat)) : list nat :=
match R with
    | nil => nil
    | h :: t => if eqb (fst h) w then (snd h) :: (world_relations_list_worlds w t) 
                else (world_relations_list_worlds w t)
end.

(* 
    Recebe o conjunto total de mundos
    Retorna o uma lista onde cada posição da lista é uma lista
        de todos os mundos que a posição relaciona
    *)
Fixpoint list_worlds_relations_list_worlds (w : list nat) (R : list (nat * nat)) : list (list nat) :=
    match w with
    | nil => nil
    | h :: t => (world_relations_list_worlds h R) :: (list_worlds_relations_list_worlds t R)
    end.


(* 
    Verifica se o mundo está contido na lista da proposição
    Recebe uma lista de mundos e um mundo qualquer
    Retorna um valor booleano referente o mundo estiver contido ou não
*)

Fixpoint verify_world (worlds : list nat) (world : nat) : bool :=
match worlds with
    | nil => false
    | h :: t => if eqb h world then true
                else verify_world t world
end.

(* 
    Verifica se uma proposição é valida em um mundo
    Recebe uma lista de pares onde:
        [(proposição, [mundos que possuem a proposição]); ...],
        um mundo qualquer e uma proposição.
    
    Retorna um valor booleano, caso a proposição seja verdadeira
        no mundo passado pelo parâmetro.
*)
Fixpoint verify_prop (worlds : list (nat * list nat)) (world : nat) (f : nat) : bool :=
match worlds with
    | nil => false
    | h :: t => if eqb (fst h) f then verify_world (snd h) world
                else verify_prop t world f
end.

(* Compute 0 |= # 1 ./\ # 2. *)

(* ----------------------- *)
(* Init - Exemplo de teste *)

Definition ex1 := #0 .\/ #1.
Definition ex2 := #1 .-> .~ #2 .-> #0 .\/ (#1 .\/ #2).
Definition ex3 := .~.~ #0 .-> #1.

Definition world := [0;1;2;3;4]. (*Precisa ver se é necessário isso*)
Definition relation_world := [(0,1);(1,1);(1,2);(2,0);(2,3);(3,1);(3,3);(3,4)].
Definition prop_in_world := [(0,[0;1]); (1, [0;1;2;3;4])].

(* Definition x := list_worlds_relations_list_worlds world relation_world. *)
Definition x := world_relations_list_worlds 1 relation_world.
Compute x.
Compute prop_in_world.
Check literals.
Compute literals ex1.
Compute verify_prop prop_in_world 2 0.

Definition lista_prop : list nat := [ ].
Compute lista_prop.

(* End - Exemplo de teste *)
(* ---------------------- *)


(* Rever essa parte para saber como deixar um vetor de pair com uma lista em snd *)
(* Definition prop_world (phi : formulaModal) (w : list nat) : list (formulaModal * list nat) :=
lista_prop ++ [pair phi w].

Compute prop_world (#1 ./\ #2) [1;2;3;4].
Check lista_prop.
*)
