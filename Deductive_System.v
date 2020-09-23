Require Import Modal_Library List Classical Logic.

(**** HILBERT SYSTEM (axiomatic method) ****)
Inductive axiom : Set :=
  | ax1   : modalFormula -> modalFormula -> axiom
  | ax2   : modalFormula -> modalFormula -> modalFormula -> axiom
  | ax3   : modalFormula -> modalFormula -> axiom
  | ax4   : modalFormula -> modalFormula -> axiom
  | ax5   : modalFormula -> modalFormula -> axiom
  | ax6   : modalFormula -> modalFormula -> axiom
  | ax7   : modalFormula -> modalFormula -> axiom
  | ax8   : modalFormula -> modalFormula -> axiom
  | ax9   : modalFormula -> modalFormula -> modalFormula -> axiom
  | ax10  : modalFormula -> modalFormula -> axiom
  | axK   : modalFormula -> modalFormula -> axiom
  | axPos : modalFormula -> modalFormula -> axiom
  | axT   : modalFormula -> axiom
  | axB   : modalFormula -> axiom
  | axK4  : modalFormula -> axiom
  | axD   : modalFormula -> axiom
  | axK5  : modalFormula -> axiom.

Definition instantiate (a: axiom): modalFormula :=
  match a with
  | ax1    φ   ψ       => φ .-> (ψ .-> φ)
  | ax2    φ   ψ   Ɣ   => (φ .-> (ψ .-> Ɣ)) .-> ((φ .-> ψ) .-> (φ .-> Ɣ))
  | ax3    φ   ψ       => (.~ ψ .-> .~ φ) .-> (φ .-> ψ)
  | ax4    φ   ψ       => φ .-> (ψ .-> (φ ./\ ψ))
  | ax5    φ   ψ       => (φ ./\ ψ) .-> φ
  | ax6    φ   ψ       => (φ ./\ ψ) .-> ψ
  | ax7    φ   ψ       => φ .-> (φ .\/ ψ)
  | ax8    φ   ψ       => ψ .-> (φ .\/ ψ)
  | ax9    φ   ψ   Ɣ   => (φ .-> Ɣ) .-> ((ψ .-> Ɣ) .-> ((φ .\/ ψ) .-> Ɣ))
  | ax10   φ   ψ       => .~ .~ φ .-> φ
  | axK    φ   ψ       => .[] (φ .-> ψ) .-> (.[] φ .-> .[] ψ)
  | axPos  φ   ψ       => .<> (φ .\/ ψ) .-> (.<> φ .\/ .<> ψ)
  | axT    φ           => .[]φ .-> φ
  | axB    φ           => φ .-> .[] .<> φ
  | axK4   φ           => .[] φ .-> .[] .[] φ
  | axD    φ           => .[] φ .-> .<> φ 
  | axK5   φ           => .<> φ .-> .[] .<> φ 
  end.

Inductive deduction (A: axiom -> Prop): theory -> modalFormula -> Prop :=
  (* Premise. *)
  | Prem: forall (t: theory)
                 (f: modalFormula)
                 (i: nat),
          (nth_error t i = Some f) -> deduction A t f
  (* Axiom. *)
  | Ax: forall (t: theory)
               (a: axiom)
               (f: modalFormula),
        A a -> instantiate a = f -> deduction A t f
  (* Modus Ponens. *)
  | Mp: forall (t: theory)
               (f g: modalFormula)
               (d1: deduction A t (f .-> g))
               (d2: deduction A t f),
        deduction A t g
  (* Generalization. *)
  | Nec: forall (t: theory)
                (f: modalFormula)
                (d1: deduction A t f),
         deduction A t (.[] f).

Inductive K: axiom -> Prop :=
  | K_ax1: forall φ ψ, K (ax1 φ ψ)
  | K_ax2: forall φ ψ Ɣ, K (ax2 φ ψ Ɣ)
  | K_ax3: forall φ ψ, K (ax3 φ ψ)
  | K_ax4: forall φ ψ, K (ax4 φ ψ)
  | K_ax5: forall φ ψ, K (ax5 φ ψ)
  | K_ax6: forall φ ψ, K (ax6 φ ψ)
  | K_ax7: forall φ ψ, K (ax7 φ ψ)
  | K_ax8: forall φ ψ, K (ax8 φ ψ)
  | K_ax9: forall φ ψ Ɣ, K (ax9 φ ψ Ɣ)
  | K_ax10: forall φ ψ, K (ax10 φ ψ)
  | K_axK: forall φ ψ, K (axK φ ψ)
  | K_axPos: forall φ ψ, K (axPos φ ψ).

(* Reflexive *)
Inductive T: axiom -> Prop :=
  | T_K: forall φ, K φ -> T φ
  | T_axT: forall φ , T (axT φ).

(* Reflexive and Symmetry *)
Inductive B: axiom -> Prop :=
  | B_T: forall φ, T φ -> B φ
  | B_axB: forall φ , B (axB φ).

(* Transitive *)
Inductive K4: axiom -> Prop :=
  | K4_K: forall φ, K φ -> K4 φ
  | K4_axK4: forall φ , K4 (axK4 φ).

(* Serial *)
Inductive D: axiom -> Prop :=
  | D_K: forall φ, K φ -> D φ
  | D_axD: forall φ , D (axD φ).

(* Euclidean *)
Inductive K5: axiom -> Prop :=
  | K5_K: forall φ, K φ -> K5 φ
  | K5_axK5: forall φ , K5 (axK5 φ).

(* Reflexive and Transitive*)
Inductive S4: axiom -> Prop :=
  | S4_T: forall φ, T φ -> S4 φ
  | S4_axK4: forall φ , S4 (axK4 φ).

(* Symmetry and S4 *)
Inductive S5: axiom -> Prop :=
  | S5_B: forall φ, B φ -> S5 φ
  | S5_S4: forall φ , S4 φ -> S5 φ.

(* Reflexive and Euclidean *)
Inductive S5_2: axiom -> Prop :=
  | S5_2_T: forall φ, T φ -> S5_2 φ
  | S5_2_K5: forall φ , K5 φ -> S5_2 φ.


(* Notations and Theorems *)

(* Coercion T_K: K >-> T. *)

Notation "A ; G |-- p" := (deduction A G p) 
    (at level 110, no associativity).

Lemma derive_identity:
  forall Γ φ, 
  K; Γ |-- φ .-> φ.
Proof.
  intros.
  apply Mp with (f := φ.-> φ .-> φ).
  - apply Mp with (f := φ .-> (φ .-> φ) .-> φ).
    + apply Ax with (a := (ax2 φ (φ .-> φ) φ)).
      * constructor.
      * reflexivity.
    + apply Ax with (a := (ax1 φ (φ .-> φ))).
      * constructor.
      * reflexivity.
  - apply Ax with (a := (ax1 φ φ)).
    + constructor.
    + reflexivity.
Qed.

Lemma derive_refl : 
  forall A Γ φ,
  A; φ :: Γ |-- φ.
Proof.
  intros.
  apply Prem with (i := 0).
  reflexivity.
Qed.


Definition subset (Γ Δ : theory) : Prop :=
  forall φ, 
  In φ Γ -> 
  In φ Δ.

Notation "A ⊆ B" := (subset A B)
  (at level 70, only printing, no associativity) : type_scope.


Lemma derive_In:
  forall A Γ φ ,
  In φ Γ ->
  A; Γ |-- φ.
Proof.
  intros; eapply In_nth_error in H.
  destruct H.
  apply Prem with (i:=x).
  assumption.
Qed.

Lemma derive_weak: 
  forall Γ ẟ,
  subset Γ ẟ ->
  forall A φ,
  (A; Γ |-- φ) -> 
  (A; ẟ |-- φ).
Proof.
  intros.
  induction H0.
  - eapply derive_In; apply H. 
    eapply nth_error_In. 
    exact H0.
  - apply Ax with (a:= a). 
    + assumption.
    + assumption.
  - eapply Mp;
     eauto.
  - apply Nec; 
    intuition.
Qed.

Lemma derive_monotonicity :
  forall ẟ Γ φ, 
  (K; Γ |-- φ) -> 
  (K; ẟ ++ Γ |-- φ).
Proof.
  intros.
  apply derive_weak with Γ.
  - unfold subset. intros. 
    induction ẟ.
    + simpl; assumption.
    + simpl in *; right; assumption.
  - assumption.
Qed.

Require Import Equality.

Lemma derive_modus_ponens:
  forall Γ φ ψ,
  (K; φ::Γ |-- ψ) ->
  (K; Γ |-- φ) ->
  (K; Γ |-- ψ).
Proof.
  intros; dependent induction H.
  - apply nth_error_In in H. 
    destruct H.
    + destruct H.
      assumption.
    + apply derive_In.
      assumption.  
  - apply Ax with (a:=a).
    + assumption.
    + reflexivity.
  - eapply Mp.
    + eapply IHdeduction1. 
      * eauto.
      * assumption. 
    + eapply IHdeduction2. 
      * eauto.
      * assumption. 
  - apply Nec.
    + eapply IHdeduction. 
      * eauto.
      * assumption. 
Qed.
