(*  
    Name: Ariel Agne da Silveira

    Advisor: Karina Girardi Roggia

    Minion: Miguel

    <Modal Logic Library>
    Description:
*)

Require Import Arith List ListSet Classical Logic Nat Notations.

Inductive formulaModal : Set :=
    | Lit          : nat -> formulaModal
    | Neg          : formulaModal -> formulaModal
    | Box          : formulaModal -> formulaModal
    | Dia          : formulaModal -> formulaModal
    | And          : formulaModal -> formulaModal -> formulaModal
    | Or           : formulaModal -> formulaModal -> formulaModal
    | Implies      : formulaModal -> formulaModal -> formulaModal 
.

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

Inductive World : Set :=
    | w : nat -> World
.


Inductive Relation : Set :=
    | r : World -> World -> Relation
.

(* -- New notation -- *)
Notation " X .-> Y "  := (Implies X Y) (at level 13, right associativity).
Notation " X .\/ Y "  := (Or X Y)      (at level 12, left associativity).
Notation " X ./\ Y"   := (And X Y)     (at level 11, left associativity).
Notation " .~ X "     := (Neg X)       (at level 10, right associativity).
Notation " .[] X "    := (Box X)       (at level 10, right associativity).
Notation " .<> X "    := (Dia X)       (at level 10, right associativity).
Notation " # X "      := (Lit X)       (at level 1, no associativity).

Notation "w # X" := (w X) (at level 1, no associativity).
Notation "x .R y" := (r x y) (at level 1, no associativity).

Notation "[ ]" := nil.
Notation "x :: l" := (cons x l)
                     (at level 60, right associativity).
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).


Fixpoint eqb_World (x x' : World): bool :=
    match x with
    | w n => match x' with 
                | w n' => if  n =? n' then true else false
            end
end.

Fixpoint In_World (x: World) (l: list World): bool :=
    match l with
    | nil => false
    | h :: t => if eqb_World x h then true
                else In_World x t
end.

Fixpoint All_In_World (l : list World) (l' : list World) : bool :=
match l with
  | nil  => true
  | h::t => if In_World h l' then All_In_World t l'
            else false
end.

Fixpoint remove_invalidate (Worlds : list World) (Relations : list (World * World)) : list (World * World) :=
    match Relations with
    | nil => nil 
    | h :: t => if andb (In_World (fst h) Worlds) (In_World (snd h) Worlds) 
                then [(fst h, snd h)] ++ remove_invalidate Worlds t
                else remove_invalidate Worlds t
end.

Fixpoint pair_to_relation (l : list (World * World)) : list Relation :=
    match l with
    | nil => nil
    | h :: t => (r (fst h) (snd h)) :: pair_to_relation t
end.

Definition validate_relation (Worlds : list World) (lw : list (World * World)) : list Relation := 
    pair_to_relation (remove_invalidate Worlds lw).

Fixpoint validate_formula (Worlds : list World) (Formulas : list (formulaModal * list World)) : 
         list (formulaModal * list World) :=
  match Formulas with
    | nil   => nil
    | h::t  => match snd h with 
                   | nil => validate_formula Worlds t 
                   | h'::t' => if All_In_World (snd h) Worlds then  [h] ++ validate_formula Worlds t
                               else validate_formula Worlds t
                   (*^^^ formula válida em algum mundo, verifica se os mundos existem, se sim, concatena*)
               end
  end.

Record Frame : Type := frame{
    W : list World; (*Recebe uma lista de mundos*)
    R : list Relation; (*Recebe uma lista de pares ordenados*)
}.

Record Model : Type := model{
    F : Frame; (*Frame de um modelo*)
    v : nat -> World; (*Precisa ser visto como vai ser feito*)
}.




(*  *)
(* The end *)