(*  Name: Ariel Agne da Silveira

    <Modal Logic Library>

*)

Require Import Arith List ListSet Classical Logic.

(* Parameter A : Type.
Parameter le : A -> Prop. 
Infix "≤" := le : order_scope.
*)

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

Inductive World : Set :=
    | w : nat -> World
.
(* 
Inductive Relation : Set :=
    | r : World -> World -> Relation
. *)

Check [w 0; w 1; w 4].
(* Check r (w 1) (w 2). *)

Notation "w # X" := (w X) (at level 1, no associativity).

Compute (w 3).

(* Notation "w # X R w # Y" := (r (w X) (w Y)) (at level 111, no associativity). *)

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



Inductive Relation (Worlds : list nat): nat -> nat -> Prop :=
| r:
    forall world_x world_y,
    In world_x Worlds -> In world_y Worlds -> Relation Worlds world_x world_y.
    
(* http://adam.chlipala.net/cpdt/html/Match.html *)

Definition W := list nat.

Definition acessibility_relation (w: list nat) (x: nat * nat) : Prop := 
 Relation w (fst x) (snd x).

Inductive Vazio : Prop.

Fixpoint verify (w: nat) (W: list nat) : Prop :=
match W with
    | [] => Vazio
    | h :: t => if eqb h w then True
                else verify w t 
end.


(* Record Mode : Type :={
    W : list nat;
    x : nat;
    y : nat;
    R : Relation W x x;
}. *)


(* Check Mode {W: [1;2;3]} {x: 1} {y: 2} {R: W x y}. *)

(* Definition R := (W * W). *)

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

(* 
    Interessante ._.
    Preciso ver isso melhor
    Mas serve para definir a caixa e diamante receberam proposições
        e defini-las como prova.
    É uma sintaxe de extensão e interpretação de escopo
    URL: https://coq.inria.fr/refman/user-extensions/syntax-extensions.html
*)
Inductive caixa (A : Prop) : Prop :=
    c : A -> .[] A
where ".[] A" := (caixa A) : type_scope.

Inductive diamante (A : Prop) : Prop :=
    d : A -> .<> A
where ".<> A" := (diamante A) : type_scope.


Fixpoint formulaSAT (v: nat -> Prop) (A:formulaModal) : Prop :=
match A with
| Lit     x        => v x
| Neg     x1       => ~ (formulaSAT v x1)
| Box     x1       => .[] (formulaSAT v x1)
| Dia     x1       => .<> (formulaSAT v x1)
| And     x1 x2    => (formulaSAT v x1) /\ (formulaSAT v x2)
| Or      x1 x2    => (formulaSAT v x1) \/ (formulaSAT v x2)
| Implies x1 x2    => ~ (formulaSAT v x1) \/ (formulaSAT v x2)
end.

(* Example of basic literal valuation *)

Fixpoint evenP (x:nat) : Prop :=
match x with
  | O   => True
  | S x => not (evenP x)
end.

(* Rever essa parte para saber como deixar um vetor de pair com uma lista em snd *)
(* Definition prop_world (phi : formulaModal) (w : list nat) : list (formulaModal * list nat) :=
lista_prop ++ [pair phi w].

Compute prop_world (#1 ./\ #2) [1;2;3;4].
Check lista_prop.
*)
