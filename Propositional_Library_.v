Require Import Arith List ListSet Classical.  (* include natural numbers *)

(* prover online  https://prover-pca.cs.ru.nl/new/# *)

(******  SYNTAX OF FORMULAS ******)

Inductive formula : Set :=
 | Lit     : nat -> formula 
 | Neg     : formula -> formula
 | And     : formula -> formula -> formula
 | Or      : formula -> formula -> formula
 | Implies : formula -> formula -> formula
.

Check (Or (Lit 0) (Lit 1)).
Check (Implies (Lit 1) (Implies (Neg (Lit 2)) (Or (Lit 0) (Or (Lit 1) (Lit 2))))).
Check (Implies (Neg (Neg (Lit 0))) (Lit 1)).


(******* BETTER NOTATATION TO WRITE FORMULAS ********)

Notation " X .-> Y "  := (Implies X Y) (at level 13, right associativity).
Notation " X .\/ Y "  := (Or X Y)      (at level 12, left associativity).
Notation " X ./\ Y"   := (And X Y)     (at level 11, left associativity).
Notation " .~ X "     := (Neg X)       (at level 9, right associativity).
Notation " # X "      := (Lit X)       (at level 1, no associativity).


Check #0 .\/ #1.
Check #1 .-> .~ #2 .-> #0 .\/ (#1 .\/ #2).
Check .~.~ #0 .-> #1.


(****** DEFINITIONS: NAMING TERMS *******)

Definition ex1 := #0 .\/ #1.
Definition ex2 := #1 .-> .~ #2 .-> #0 .\/ (#1 .\/ #2).
Definition ex3 := .~.~ #0 .-> #1.


(* Defining recursive functions on formulas: size *)

Fixpoint size (f:formula) : nat :=
match f with 
| Lit      x     => 1
| Neg      p1    => 1 + (size p1)
| And      p1 p2 => 1 + (size p1) + (size p2)
| Or       p1 p2 => 1 + (size p1) + (size p2)
| Implies  p1 p2 => 1 + (size p1) + (size p2)
end.

Check size ex1.
Compute size ex1.


(* Using ListSet library to have finite sets  

 type: set nat.
 
  ops: empty_set nat, 
       set_add eq_nat_dec, 
       set_remove eq_nat_dec,
       set_union eq_nat_dec, 
       set_mem eq_nat_dec.

We need to pass the type "nat" and also a proof that equality on natural numbers is decidable
"eq_nat_dec". 

*)

Fixpoint literals (f:formula) : set nat :=
match f with 
| Lit      x     => set_add eq_nat_dec x (empty_set nat)
| Neg      p1    => literals p1
| And      p1 p2 => set_union eq_nat_dec (literals p1) (literals p2)
| Or       p1 p2 => set_union eq_nat_dec (literals p1) (literals p2)
| Implies  p1 p2 => set_union eq_nat_dec (literals p1) (literals p2) 
end.


Check literals ex2.
Compute literals ex2.


(******  TRUTH TABLE SEMANTICS -- with booleans ******)

(* Semantics of propositional logic is a function that evaluates a formula based on
   a valuation for literals and truth tables for logical operations *)

Fixpoint valuation (p: nat -> bool) (f:formula) : bool :=
match f with
| Lit     x        => p x
| Neg     x1       => negb (valuation p x1)
| And     x1 x2    => (valuation p x1) && (valuation p x2)
| Or      x1 x2    => (valuation p x1) || (valuation p x2)
| Implies x1 x2    => (negb (valuation p x1)) || (valuation p x2)
end.

(* Example of basic literal valuation *)

Fixpoint evenb (x:nat) : bool :=
match x with
  | O   => true
  | S x => negb (evenb x)
end.

Check   valuation evenb ex1.
Compute valuation evenb ex1.



(******  TRUTH TABLE SEMANTICS -- with propositions ******)

Fixpoint formulaSAT (v: nat -> Prop) (A:formula) : Prop :=
match A with
| Lit     x        => v x
| Neg     x1       => ~ (formulaSAT v x1)
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

Check   formulaSAT evenP ex1.
Compute formulaSAT evenP ex1.



(******  Finite theories and entailment ******)

Definition theory := list formula.

Fixpoint theorySAT (v:nat -> Prop) (Gamma:theory) : Prop :=
match Gamma with
  | nil      => True
  | cons h t => (formulaSAT v h) /\ (theorySAT v t)
end.

Definition entails (Gamma:theory) (A:formula) : Prop := 
forall (v: nat -> Prop), theorySAT v Gamma -> formulaSAT v A.

Notation " A |= B " := (entails A B) (at level 110, no associativity).

(***** structural properties of deduction ****)


(* reflexivity *)

Theorem  reflexive_deduction:
   forall (Gamma:theory) (A:formula) ,
      (A::Gamma |= A).
Proof.
  intros. 
  unfold entails. 
  intros. 
  unfold theorySAT in H. 
  destruct H as [left right].
  apply left.
Qed.



(* transitivity *)
Lemma theorySAT_union: forall (v: nat -> Prop) (Gamma Delta:theory),
  (theorySAT v (Gamma++Delta)) -> ((theorySAT v Gamma) /\ (theorySAT v Delta)).
Proof.
  intros. 
  induction Gamma.
    + simpl in *. split. auto. apply H.
    + simpl in *. apply and_assoc. destruct H as [left right]. split.
      - apply left.
      - apply IHGamma. apply right.
Qed.

(* prova bottom-up *)
Theorem  transitive_deduction_bu:
   forall (Gamma Delta:theory) (A B C:formula) ,
      (A::Gamma |= B) /\ (B::Delta |= C) -> (A::Gamma++Delta |= C).
Proof.
  intros. 
  unfold entails in *. 
  destruct H as [H1 H2]. 
  intros. apply H2. 
  simpl in *. destruct H as [left right]. 
  apply theorySAT_union in right. destruct right as [SatG SatD]. split.
  - apply H1. split. apply left. apply SatG.
  - apply SatD.
Qed.


(* prova top-down *)
Theorem  transitive_deduction_td:
   forall (Gamma Delta:theory) (A B C:formula) ,
      (A::Gamma |= B) /\ (B::Delta |= C) -> (A::Gamma++Delta |= C).
Proof.
  intros. 
  unfold entails in *. 
  destruct H as [H1 H2]. 
  intros. 
  simpl in H.
    destruct H as [left right].
    pose right as x. apply theorySAT_union in x.
    destruct x as [x1 x2].
    assert ( theorySAT v (A::Gamma)). simpl. split. assumption. assumption.
    pose H as y. apply H1 in y.
    assert ( theorySAT v (B::Delta)). simpl. split. assumption. assumption. 
    pose H0 as z.
    apply H2 in z.
    assumption.
Qed.

(*********Machado's code*********)

Lemma theorySAT_union1: 

     forall (p : nat -> Prop) (t u:theory), 
        (theorySAT p (t++u)) -> ((theorySAT p t) /\ (theorySAT p u)).
Proof.
induction t.
  * intros. simpl in H. split. constructor 1. auto. 
  * intros. simpl in H. destruct H. simpl. apply IHt in H0.
    destruct H0.  split. split. auto. auto. auto.
Qed. 


Lemma theorySAT_union2: 

forall (p : nat -> Prop) (t u:theory), 
         (theorySAT p t) -> (theorySAT p u) -> (theorySAT p (t++u)).

Proof.
induction t.
 * intros. simpl. auto. 
 * intros. simpl in H. destruct H. simpl. split. auto. 
   apply IHt. auto. auto. 
Qed. 


Theorem  transitive_deduction_Machado:
   forall (p: nat -> Prop) (t u:theory) (a b c:formula) ,
      (a::t |= b) -> (b::u |= c) -> (a::t++u |= c).
Proof. 
intros. unfold entails. intros. 
inversion H1. apply theorySAT_union1 in H3.
destruct H3. apply H0. simpl. split.
apply H. simpl. split. auto. auto. auto.  
Qed. 






(* exchange *)

Theorem exchange: forall (Gamma:theory) (A B C:formula),
  (A::B::Gamma |= C) -> (B::A::Gamma |= C).
Proof.
  unfold entails in *. intros. apply H. simpl. simpl in H0.
  destruct H0 as [satB [satA satGamma]]. split.
  apply satA. split. apply satB. apply satGamma.
Qed.


Theorem exchange_Machado: 
   forall (p: nat -> Prop) (t:theory) (a:formula) (b:formula) (c:formula),
      (a::b::t |= c) -> (b::a::t |= c).
Proof.
intros. 
unfold entails in *.
intros.
simpl in H0.
destruct H0.
destruct H1.
apply H.
simpl.
auto. 
Qed.



(* idempotence *)

Theorem idempotence:
   forall (Gamma:theory) (A B:formula),
      (A::A::Gamma |= B) -> (A::Gamma |= B).
Proof.
  intros. unfold entails in *. intros.
  apply H. simpl in *. destruct H0 as [satA satGamma]. (*auto.*)
  split. apply satA. split. apply satA. apply satGamma.
Qed.


Theorem idempotence_Machado:
   forall (p: nat -> Prop) (t:theory) (a:formula) (b:formula),
      (a::a::t |= b) -> (a::t |= b).
Proof. 
intros. 
unfold entails in *.
intros. 
apply H.
simpl in H0.
destruct H0.
simpl.
auto. 
Qed. 


(* monotonicity *)

Theorem monotonicity: forall (Gamma Delta: theory) (A: formula),
  (Gamma |= A) -> (Gamma++Delta |= A).
Proof.
  intros. unfold entails in *. intros. apply H. 
  apply theorySAT_union with (Delta:=Delta). apply H0.
Qed.









Theorem  monotonicity_Machado:
   forall (t u:theory) (a:formula) ,
      (t |= a) -> (t++u |= a).
Proof.
induction t.
 * intros. simpl in *. unfold entails. intros.  apply H. constructor 1.
 * intros. simpl in *. unfold entails. intros. apply H. simpl in H0. destruct H0.
   simpl. split. auto. apply theorySAT_union1 in H1. destruct H1. auto. 
Qed.


(******  Deduction theorems (semantic) *******) 

Theorem deduction1 : 

  forall (p: nat -> Prop) (t:theory) (a:formula) (b:formula), 
         (a::t |= b) -> (t |= a .-> b).
Proof.
intros p t a b.
unfold entails.
intros.
assert ((formulaSAT p a) \/ ~(formulaSAT p a)). apply classic.
destruct H1.
  simpl. right. apply H. simpl. auto.
  simpl. left. auto.
Qed.      
 
Theorem deduction2 : 

  forall (p: nat -> Prop) (t:theory) (a:formula) (b:formula), 
      (t |= a .-> b) -> (a::t |= b).

Proof.
intros p t a b.
unfold entails.
intros. 
simpl in H0. destruct H0.
assert (formulaSAT p (a .-> b)). apply H. auto. simpl in H2.
destruct H2. contradiction. auto.
Qed.

Theorem deduction_thm :      
  forall (p: nat -> Prop) (t:theory) (a:formula) (b:formula), 
         (a::t |= b) <-> (t |= a .-> b).
Proof.
intros.
split.
intros. apply deduction1. auto. auto.
intros. apply deduction2. auto. auto.
Qed.     




(***************** EQUIVALENCES  *************************)

Definition equivalence (f g:formula) : Prop := ( f::nil |= g ) <-> (g::nil |= f).

Notation " A =|= B " := (equivalence A B) (at level 110, no associativity).


Theorem equiv_refl : forall (f:formula), f =|= f.
Proof. 
Admitted.

Theorem equiv_sym : forall (f g:formula), (f =|= g) -> (g =|= f).
Proof. 
Admitted.

Theorem equiv_trans : forall (f g h:formula), (f =|= g) -> (g =|= h) -> (f =|= h).
Proof. 
Admitted.



Theorem implies_to_or : forall (a b: formula),   a .-> b  =|=  (.~ a) .\/ b .
Proof.
intros.
split.
  - intros. unfold entails in *. intros. simpl in H0. destruct H0.
    destruct H0. simpl. left. auto. simpl. right. auto.
  - intros. unfold entails in *. intros. simpl. simpl in H0.
    destruct H0. destruct H0. left. auto. right. auto.
Qed.

Theorem elim_double_negation : forall (a: formula),   .~ .~ a  =|=  a.
Proof.
intros.
split.
  - intros. unfold entails in *. intros. simpl in H0. destruct H0.
      simpl. intro. contradiction. 
  - intros. unfold entails in *. intros. simpl in H0. destruct H0.
    assert (formulaSAT v a \/ ~formulaSAT v a). apply classic.
    destruct H2. 
       * auto.
       * contradiction. Admitted.
(* Qed.  *)

Theorem and_to_implies : forall (a b: formula),   a ./\ b  =|=  .~ (a .-> .~ b).
Proof.
intros.
split.
  - intros. unfold entails in *. intros. simpl in H0. destruct H0.
    simpl. split.
       * pose (classic (formulaSAT v a)) as H2.   
         destruct H2. auto. assert (~ formulaSAT v a \/ ~ formulaSAT v b). right. auto. contradiction.
       * pose (classic (formulaSAT v b)) as H2.
         destruct H2. auto. assert (~ formulaSAT v a \/ ~ formulaSAT v b). left. auto. contradiction.
  - intros. unfold entails in *. intros. simpl. simpl in H0.
    destruct H0. destruct H0. intro. destruct H3. contradiction. contradiction.
Qed.



Fixpoint toImplic (f: formula) : formula :=
match f with
  | # x     => # x
  | .~ a    => .~ (toImplic a)
  | a ./\ b => .~ (.~ (toImplic a) .-> (toImplic b) ) 
  | a .\/ b => .~ (.~ (toImplic a) .-> (toImplic b) ) 
  | a .-> b => (toImplic a) .-> (toImplic b)
end.

Theorem toImplic_equiv : forall (f:formula), f =|= (toImplic f).
Proof.
induction f.
Admitted. 

(***************** DEDUCTIVE SYSTEMS *************************)

(**** HILBERT SYSTEM (axiomatic method) ****)

Inductive axiom : Set :=
| ax1 : formula -> formula -> axiom               (* A -> (B -> A) *)
| ax2 : formula -> formula -> formula -> axiom    (* (A -> B -> C) -> (A->B) -> (A -> C) *)
| ax3 : formula -> formula -> axiom               (* (A -> B) -> (A -> ~B) -> ~A *)
| ax4 : formula -> formula -> axiom               (* (A -> B -> A /\ B *)
| ax5 : formula -> formula -> axiom               (* (A /\ B) -> A *)
| ax6 : formula -> formula -> axiom               (* (A /\ B) -> B *)
| ax7 : formula -> formula -> axiom               (* A -> A \/ B *)
| ax8 : formula -> formula -> axiom               (* B -> A \/ B *)
| ax9 : formula -> formula -> formula -> axiom    (* (A -> C) -> (B -> C) -> A \/ B -> C *)
| ax10 : formula -> axiom                         (* ~~A -> A *)
. 

Fixpoint instantiate (a:axiom) : formula :=
match a with
| ax1  p1 p2    => p1 .-> (p2 .-> p1)
| ax2  p1 p2 p3 => (p1 .-> p2 .-> p3) .-> (p1 .-> p2) .-> (p1 .-> p3)
| ax3  p1 p2    => (p1 .-> p2) .-> (p1 .-> .~ p2) .-> .~ p1
| ax4  p1 p2    => p1 .-> p2 .-> p1 ./\ p2
| ax5  p1 p2    => p1 ./\ p2 .-> p1
| ax6  p1 p2    => p1 ./\ p2 .-> p2
| ax7  p1 p2    => p1 .-> p1 .\/ p2
| ax8  p1 p2    => p2 .-> p1 .\/ p2
| ax9  p1 p2 p3 => (p1 .-> p3) .-> (p2 .-> p3) .-> p1 .\/ p2 .-> p3
| ax10 p1       => .~ .~ p1 .-> p1
end.

Check ax1 ex1 ex2.
Check instantiate (ax1 ex1 ex2).
Compute instantiate (ax1 ex1 ex2).

Inductive deduction : theory -> formula -> Set :=
| Prem : forall (t:theory) (f:formula) (i:nat), (nth_error t i = Some f) -> deduction t f
| Ax   : forall (t:theory) (f:formula) (a:axiom), (instantiate a = f) -> deduction t f
| Mp   : forall (t:theory) (f g:formula) (d1:deduction t (f .-> g)) (d2:deduction t f), deduction t g
.


Definition th1 := (#0 :: #0 .-> #1 :: nil). 
Definition ded1 := (Prem th1        #0 0 eq_refl).
Definition ded2 := (Prem th1 (#0.->#1) 1 eq_refl).
Definition ded3 := (Mp   th1 #0 #1 ded2 ded1).
Check ded3.
Definition ded4 := (Ax th1 (#1 .-> #2 .-> #1) (ax1 #1 #2) eq_refl).
Definition ded5 := (Mp th1  #1 (#2 .-> #1) ded4 ded3).
Check ded5.

