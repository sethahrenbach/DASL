Add LoadPath "/Users/sethahrenbach/DASL".
Require Import DASL.

Definition negb (b:bool) : bool := 
  match b with
  | true => false
  | false => true
  end.

Definition andb (b1:bool) (b2:bool) : bool := 
  match b1 with 
  | true => b2 
  | false => false
  end.

Definition orb (b1:bool) (b2:bool) : bool := 
  match b1 with 
  | true => true
  | false => b2
  end.

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

Definition serial_Rb_frame (F : frame) : Prop := 
  forall (w : (W F)) (ags : DASL.Agents), 
    exists (y : (W F)), (Rb F ags w y).

Definition euclidean_Rb_frame (F : frame) : Prop :=
  forall (w x y : (W F)) (ags : DASL.Agents),
    (Rb F ags w x) ->
    (Rb F ags w y) ->
    (Rb F ags x y).

Definition Rb_subset_Rk (F : frame) : Prop :=
  forall (w x : (W F)) (a : DASL.Agents),
  (Rb F a w x) ->
  (Rk F a w x).

Definition Rb_subset_Rb_compose_Rk (F : frame) : Prop :=
  forall (w x y : (W F)) (a :  DASL.Agents),
  (Rb F a w x) ->
  (Rk F a x y) ->
  (Rb F a w y).

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

Lemma B_is_serial : forall (phi : prop) (F : frame) (a : DASL.Agents),
  (serial_Rb_frame F) ->
  F ||= ((B a phi) ==> NOT (B a (NOT phi))).
Proof.
  intros.
  unfold serial_Rb_frame in H.
  unfold Frame_validity. 
    intros.
    unfold Model_satisfies. 
      intros. pose proof H w; clear H. pose proof H0 a; clear H0.
      unfold satisfies.
        destruct H.
        intros. pose proof H0 x; clear H0. simpl in H1. pose proof H1 H; clear H1. simpl. unfold not.
        intros.
        pose proof H1 x H; clear H1. pose proof H2 H0. assumption.
Qed.

Lemma B_is_euclidean : forall (phi : prop) (F : frame) (a : DASL.Agents),
  (euclidean_Rb_frame F) ->
  F ||= (NOT (B a phi) ==> B a (NOT (B a phi))).
Proof.
  intros; unfold euclidean_Rb_frame in H; 
    unfold Frame_validity; 
      intros; unfold Model_satisfies;
          intros; unfold satisfies; unfold NOT; unfold not; 
            intros; contradiction H0;
              intro x; intros; pose proof H2 x; clear H2;
                pose proof H w; clear H; pose proof H2 y; clear H2; pose proof H x; clear H;
                pose proof H2 a H1; clear H2; pose proof H H3; clear H; pose proof H4 H2; assumption.
Qed.

Lemma KB_is_Rb_subset_Rk : forall (phi : prop) (F : frame) (a : DASL.Agents),
  (Rb_subset_Rk F) ->
  F ||= (K a phi ==> B a phi).
Proof.
  intros; unfold Rb_subset_Rk in H;
    unfold Frame_validity;
      intros; unfold Model_satisfies;
        intros; unfold satisfies; intro H0; intro x;
          pose proof H0 x; clear H0; intro;
          pose proof H w x a H0; clear H;
          pose proof H1 H2; clear H1; assumption.
Qed.

Lemma B_BK_is_Rb_subset_Rb_compose_Rk : forall (phi : prop) (F : frame) (a : DASL.Agents),
  (Rb_subset_Rb_compose_Rk F) ->
  F ||= (B a phi ==> B a (K a phi)).
Proof.
  unfold Rb_subset_Rb_compose_Rk; intros;
  unfold Frame_validity; intros; unfold Model_satisfies; intros; unfold satisfies;
  intro H0; intro x; intro H1; intro y;
    pose proof H w x y a H1; clear H; intro H3;
    pose proof H2 H3; clear H2;
    pose proof H0 y H; clear H0;
    assumption.
Qed.

Lemma Hilbert_K_Frame_Valid : forall (p q : prop) (F : frame) (a : DASL.Agents),
  F ||= (p ==> q ==> p).
Proof.
  intros p q F a.
  repeat (try unfold Frame_validity; intros; try unfold Model_satisfies; intros; try unfold satisfies; intros; assumption).
Qed.

Lemma Hilbert_S_Frame_Valid : forall (p q r : prop) (F : frame) (a : DASL.Agents),
  F ||= ((p==>q==>r)==>(p==>q)==>(p==>r)).
Proof.
  intros p q r F a.
  
  repeat (try unfold Frame_validity; 
              intros; try unfold Model_satisfies; 
              intros; try unfold satisfies;  
              intros; try pose proof H H1; clear H; 
                      try pose proof H0 H1; clear H0; 
                      try pose proof H2 H; 
          assumption).
Qed.

Axiom base_double_negation : forall p,
  not (not p) = p.

Lemma Classic_NOTNOT_Frame_Valid : forall (p : prop) (F : frame) (a : DASL.Agents),
  F ||= ((NOT (NOT p)) ==> p).
Proof.
  intros p F a.
   repeat (try unfold Frame_validity; 
              intros; try unfold Model_satisfies; 
              intros; try unfold satisfies;  
              intros; try unfold NOT in H; 
                      try rewrite base_double_negation in H; 
                      try assumption).
Qed.
