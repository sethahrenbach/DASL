Add LoadPath "/Users/sethahrenbach/DASL".
Require Import DASL.

(* This is heavily inspired by Paulien de Wind's M.Sc. Thesis: "Modal Logic in Coq", University of Amsterdam, 2001.
 *)
Inductive var : Set := p : nat -> var.

Record frame : Type := {
  W : Set;
  Rk : DASL.Agents -> W -> W -> Prop;
  Rb : DASL.Agents -> W -> W -> Prop
}.

Check frame.

Check Build_frame.

Record model : Type := {
  F : frame;
  Val : (W F) -> Atoms -> Prop;
  Agents: DASL.Agents
}.


Fixpoint satisfies (M : model) (x : (W (F M))) (phi : prop) {struct phi} : Prop :=
  match phi with
  | _|_ => False
  | (atm atom) => (Val M x atom)
  | (imp phi1 phi2) => (satisfies M x phi1) -> (satisfies M x phi2)
  | (negp phi') => (~ (satisfies M x phi'))
  | (K a phi') => (forall y : (W (F M)), (Rk (F M) a x y) -> (satisfies M y phi'))
  | (B a phi') => (forall y : (W (F M)), (Rb (F M) a x y) -> (satisfies M y phi'))
  end.

Notation "M x |== phi" := (satisfies M x phi) (at level 80).

Definition Model_satisfies (M : model) (phi : prop) := forall (w : (W (F M))),
  satisfies M w phi .

Notation "M |= phi" := (Model_satisfies M phi) (at level 80).

Definition Frame_validity (F : frame) (phi : prop) := forall (Val : (W F) -> Atoms -> Prop) (Ags : DASL.Agents),
  (Model_satisfies (Build_model F Val Ags) phi).

Notation "F ||= phi" := (Frame_validity F phi) (at level 80).

Definition valid (phi : prop) := forall (F : frame),
  (Frame_validity F phi).

Definition reflexive_Rk_frame (F : frame) : Prop := 
  forall (w : (W F)) (ags : DASL.Agents), (Rk F ags w w).

Definition reflexive_Rb_frame (F : frame) : Prop := 
  forall (w : (W F)) (ags : DASL.Agents), (Rb F ags w w).

Lemma K_is_refl : forall (phi : prop) (F : frame) (a : DASL.Agents),
  (reflexive_Rk_frame F) ->
  F ||= ((K a phi) ==> phi).
Proof.
  intros.
  unfold reflexive_Rk_frame in H.
  unfold Frame_validity. 
    intros.
    unfold Model_satisfies. 
      intros. pose proof H w; clear H. pose proof H0 a; clear H0.
      unfold satisfies.
        intros. pose proof H0 w; clear H0. simpl in H1. pose proof H1 H; clear H1.
        auto.
Qed.






