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


Inductive Relation : Prop :=
    | r : World -> World -> Relation
.


Notation "w # X" := (w X) (at level 1, no associativity).
Notation "x $ y" := (r x y) (at level 1, no associativity).

(* Definition verify_relation (W : World) (R : Relation) : Prop := forall . *)

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

Notation "x && y" := (andb x y).
Notation "x =? y" := (eqb x y) (at level 70).

Fixpoint eqb_World (x x' : World): bool :=
  match x with
    | w n => match x' with 
              | w n' => if eqb n n' then true else false
            end
  end.

Fixpoint In_World (x: World) (l: list World): bool :=
  match l with
    | nil => false
    | h :: t => if eqb_World x h then true
                else In_World x t
  end.

Fixpoint teste (Worlds : list World) (Relations : list (World * World)) : list (World * World) :=
match Relations with
    | nil => nil 
    | h :: t => if (In_World (fst h) Worlds) && (In_World (snd h) Worlds) 
                          then ((fst h, snd h) :: nil) ++ teste Worlds t
                          else teste Worlds t
end.

Fixpoint pair_to_relation (l : list (World * World)) : list Relation :=
  match l with
    | nil => nil
    | h :: t => (r (fst h) (snd h)) :: pair_to_relation t
  end.

Definition validate_relation (Worlds : list World) (lw : list (World * World)) : list Relation := 
pair_to_relation (teste Worlds lw).


Record Frame : Type := frame{
    W : list World; (*Recebe uma lista de mundos*)
    R : (validate_relation W Relation)->list Relation; (*Recebe uma lista de pares ordenados*)
}.

Record Model : Type :={
    F : Frame; (*Frame de um modelo*)
    v : formulaModal -> World -> bool; (*Precisa ser visto como vai ser feito*)
}.

(* The end *)