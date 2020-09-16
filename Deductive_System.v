Require Import Modal_Library List Classical Logic.

(**** HILBERT SYSTEM (axiomatic method) ****)
Inductive axiom : Set :=
  | ax1 : modalFormula -> modalFormula -> axiom
  | ax2 : modalFormula -> modalFormula -> modalFormula -> axiom
  | ax3 : modalFormula -> modalFormula -> axiom
  | ax4 : modalFormula -> modalFormula -> axiom
  | ax5 : modalFormula -> modalFormula -> axiom
  | ax6 : modalFormula -> modalFormula -> axiom
  | ax7 : modalFormula -> modalFormula -> axiom
  | ax8 : modalFormula -> modalFormula -> axiom
  | ax9 : modalFormula -> modalFormula -> modalFormula -> axiom
  | ax10: modalFormula -> modalFormula -> axiom
  | axK : modalFormula -> modalFormula -> axiom
  | axT : modalFormula -> axiom
  | axB : modalFormula -> axiom
  | axK4: modalFormula -> axiom
  | axD : modalFormula -> axiom
  | axK5: modalFormula -> axiom.

Definition instantiate (a: axiom): modalFormula :=
  match a with
  | ax1  φ   ψ       => φ .-> (ψ .-> φ)
  | ax2  φ   ψ   Ɣ   => (φ .-> (ψ .-> Ɣ)) .-> ((φ .-> ψ) .-> (φ .-> Ɣ))
  | ax3  φ   ψ       => (.~ ψ .-> .~ φ) .-> (φ .-> ψ)
  | ax4  φ   ψ       => φ .-> (ψ .-> (φ ./\ ψ))
  | ax5  φ   ψ       => (φ ./\ ψ) .-> φ
  | ax6  φ   ψ       => (φ ./\ ψ) .-> ψ
  | ax7  φ   ψ       => φ .-> (φ .\/ ψ)
  | ax8  φ   ψ       => ψ .-> (φ .\/ ψ)
  | ax9  φ   ψ   Ɣ   => (φ .-> Ɣ) .-> ((ψ .-> Ɣ) .-> ((φ .\/ ψ) .-> Ɣ))
  | ax10 φ   ψ       => .~ .~ φ .-> φ
  | axK  φ   ψ       => .[] (φ .-> ψ) .-> (.[] φ .-> .[] ψ)
  | axT  φ           => φ .-> .[]φ
  | axB  φ           => φ .-> .[] .<> φ
  | axK4 φ           => .[] φ .-> .[] .[] φ
  | axD  φ           => .[] φ .-> .<> φ 
  | axK5 φ           => .<> φ .-> .[] .<> φ 
  end.

Inductive deduction (A: axiom -> Prop): theory -> modalFormula -> Prop :=
  (* Premissa. *)
  | Prem: forall (t: theory)
                 (f: modalFormula)
                 (i: nat),
          (nth_error t i = Some f) -> deduction A t f
  (* Axioma. *)
  | Ax: forall (t: theory)
               (a: axiom)
               (f: modalFormula),
        A a -> instantiate a = f -> deduction A t f
  (* Modus poenens. *)
  | Mp: forall (t: theory)
               (f g: modalFormula)
               (d1: deduction A t (f .-> g))
               (d2: deduction A t f),
        deduction A t g
  (* Necessitação. *)
  | Nec: forall (t: theory)
                (f: modalFormula)
                (d1: deduction A t f),
         deduction A t (.[] f).

Inductive K: axiom -> Prop :=
  | K_ax1: forall p q, K (ax1 p q)
  | K_ax2: forall p q r, K (ax2 p q r)
  | K_ax3: forall p q, K (ax3 p q)
  | K_ax4: forall p q, K (ax4 p q)
  | K_ax5: forall p q, K (ax5 p q)
  | K_ax6: forall p q, K (ax6 p q)
  | K_ax7: forall p q, K (ax7 p q)
  | K_ax8: forall p q, K (ax8 p q)
  | K_ax9: forall p q r, K (ax9 p q r)
  | K_ax10: forall p q, K (ax10 p q)
  | K_axK: forall p q, K (axK p q).

(* Reflexive *)
Inductive T: axiom -> Prop :=
  | T_K: forall a, K a -> T a
  | T_axT: forall p , T (axT p).

(* Reflexive and Symmetry *)
Inductive B: axiom -> Prop :=
  | B_T: forall a, T a -> B a
  | B_axT: forall p , B (axB p).

(* Transitive *)
Inductive K4: axiom -> Prop :=
  | K4_K: forall a, K a -> K4 a
  | K4_axK4: forall p , K4 (axK4 p).

(* Serial *)
Inductive D: axiom -> Prop :=
  | D_K: forall a, K a -> D a
  | D_axD: forall p , D (axD p).

(* Euclidean *)
Inductive K5: axiom -> Prop :=
  | K5_K: forall a, K a -> K5 a
  | K5_axK5: forall p , K5 (axK5 p).


(* Reflexive and Transitive*)
Inductive S4: axiom -> Prop :=
  | S4_T: forall a, T a -> S4 a
  | S4_axK4: forall p , S4 (axK4 p).

(* Symmetry and S4 *)
Inductive S5: axiom -> Prop :=
  | S5_B: forall a, B a -> S5 a
  | S5_S4: forall a , S4 a -> S5 a.

(* Reflexive and Euclidean *)
Inductive S5_2: axiom -> Prop :=
  | S5_2_T: forall a, T a -> S5_2 a
  | S5_2_K5: forall a , K5 a -> S5_2 a.


(* Notations and Theorems *)

Coercion T_K: K >-> T.

Notation "A ; G |-- p" := (deduction A G p) 
    (at level 110, no associativity).

Lemma derive_identity:
  forall (a: modalFormula) (G: theory), 
  K; G |-- a .-> a.
Proof.
  intros.
  apply Mp with (f := a.-> a .-> a).
  - apply Mp with (f := a .-> (a .-> a) .-> a).
    + apply Ax with (a := (ax2 a (a .-> a) a)).
      * constructor.
      * reflexivity.
    + apply Ax with (a := (ax1 a (a .-> a))).
      * constructor.
      * reflexivity.
  - apply Ax with (a := (ax1 a a)).
    + constructor.
    + reflexivity.
Qed.

Lemma derive_refl : 
  forall (A: axiom -> Prop) (Gamma: theory) (phi: modalFormula),
  A; phi :: Gamma |-- phi.
Proof.
  intros.
  apply Prem with (i := 0).
  reflexivity.
Qed.


Definition subset (Γ Δ : theory) : Prop :=
    forall (φ : modalFormula), In φ Γ -> In φ Δ.


Lemma derive_In:
  forall A G phi ,
  In phi G ->
  A; G |-- phi.
Proof.
  intros; eapply In_nth_error in H.
  destruct H.
  apply Prem with (i:=x).
  assumption.
Qed.

Lemma derive_weak: 
  forall G D,
  subset G D ->
  forall A p,
  (A; G |-- p) -> (A; D |-- p).
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
  forall A (H G: theory) (phi:modalFormula), 
  (A; G |-- phi) -> (A; (H ++ G) |-- phi).
Proof.
  intros.
  apply derive_weak with G.
  - unfold subset. intros. 
    induction H.
    + simpl; assumption.
    + simpl in *; right; assumption.
  - assumption.
Qed.

Theorem derive_modus_ponens:
  forall (phi psi: modalFormula) (Gamma: theory),
  (K; phi::Gamma |-- psi) ->
  (K; Gamma |-- phi) ->
  (K; Gamma |-- psi).
Proof.
  intros; inversion H. 
  admit. 
Admitted.


