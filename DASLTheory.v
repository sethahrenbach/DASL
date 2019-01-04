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

Lemma MP_Frame_Valid : forall (p q : prop) (F : frame) (a : DASL.Agents),
  F ||= (p ==> q) ->
  F ||= p ->
  F ||= q.
Proof.
  intros p q F a.
  unfold Frame_validity.
  unfold Model_satisfies.
  unfold satisfies.
  intros.
  pose proof H Val0 Ags; clear H.
  pose proof H0 Val0 Ags; clear H0.
  pose proof H w; clear H.
  pose proof H1 w H0; clear H1. assumption.
Qed.

Lemma K_Nec_Frame_Valid : forall (p : prop) (F : frame) (a : DASL.Agents),
  F ||= p ->
  F ||= K a p.
Proof.
  intros p F a.
  unfold Frame_validity; unfold Model_satisfies; unfold satisfies; intros.
  pose proof H Val0 Ags y; clear H. assumption.
Qed.

Lemma K_K_Frame_Valid : forall (p q : prop) (F : frame) (a : DASL.Agents),
  F ||= (K a p ==> K a (p ==> q) ==> K a q).
Proof.
  intros p q F a.
  unfold Frame_validity; unfold Model_satisfies; unfold satisfies. intros.
  pose proof H0 y H1; clear H0.
  pose proof H y H1; clear H. pose proof H2 H0; assumption.
Qed.

Lemma B_K_Frame_Valid : forall (p q : prop) (F : frame) (a : DASL.Agents),
  F ||= (B a p ==> B a (p ==> q) ==> B a q).
Proof.
  intros p q F a.
  unfold Frame_validity; unfold Model_satisfies; unfold satisfies. intros.
  pose proof H0 y H1; clear H0.
  pose proof H y H1; clear H. pose proof H2 H0; assumption.
Qed.

Definition DASL_Frame (F : frame) : Prop :=
  reflexive_Rk_frame F /\
  serial_Rb_frame F /\
  euclidean_Rb_frame F /\
  Rb_subset_Rk F /\
  Rb_subset_Rb_compose_Rk F.
 

Theorem DASL_Soundness : forall (phi : prop) (F : frame) (a : DASL.Agents),
  DASL_Frame F ->
  |-- phi ->
  F ||= phi.
Proof.
   intros phi F.
    unfold DASL_Frame.
    intros. destruct H; destruct H1; destruct H2; destruct H3. 
    induction H0.
    apply Hilbert_K_Frame_Valid; assumption.
    apply Hilbert_S_Frame_Valid; assumption.  
    apply Classic_NOTNOT_Frame_Valid; assumption.
    eapply MP_Frame_Valid; eassumption.
    apply K_Nec_Frame_Valid; assumption.
    apply K_K_Frame_Valid; assumption.
    apply K_is_refl; assumption.
    apply B_K_Frame_Valid; assumption.
    apply B_is_serial; assumption.
    apply B_is_euclidean; assumption.
    apply KB_is_Rb_subset_Rk; assumption.
    apply B_BK_is_Rb_subset_Rb_compose_Rk; assumption.
Qed.

(* Definition simple_prop (p : prop) : Prop :=
  match p with
  | (imp phi1 phi2) => False
  | _ => True
  end.

Fixpoint boxed (p : prop) : Prop :=
  simple_prop p \/
  match p with
  | (negp p') => simple_prop p'
  | (K a p') => boxed p'
  | (B a p') => boxed p'
  | (imp phi1 phi2) => False
  | _ => True
  end. *)

(* 
Fixpoint positive_formula (phi : prop) : Prop :=
  match phi with
  | _|_ => False
  | (atm atom) => True
  | (imp phi1 phi2) => (not (positive_formula phi1) /\ positive_formula phi2)
  | (negp phi') => not (positive_formula phi')
  | (K a phi') => (positive_formula phi')
  | (B a phi') => (positive_formula phi')
  end. *)

(* Fixpoint sahlqvist_antecedent (phi : prop) : Prop :=
  match phi with  
  | _|_ => True
  | (atm atom) => True
  | (imp phi1 phi2) => ((sahlqvist_antecedent phi1) /\ (positive_formula phi1) /\
                       not (positive_formula phi2) /\ (sahlqvist_antecedent phi2))
  | (negp phi') => (sahlqvist_antecedent phi')
  | (K a phi') => (boxed phi')
  | (B a phi') => (boxed phi')
  end.   *)

(* Definition sahlqvist_equivalent (phi : prop) : Prop :=
  exists (phi2 : prop),
  forall (F : frame) (a : DASL.Agents),
    F ||= (phi <=> phi2) ->
    sahlqvist_formula phi2 ->
    sahlqvist_formula phi. *)
Inductive Var : Set :=
  | P : nat -> Var.

Inductive formula : Type :=
  | FVar : Var -> prop -> formula
  | FProp : prop -> formula
  | FImp : formula -> formula -> formula
  | FNeg : formula -> formula
  | FK : DASL.Agents -> formula -> formula
  | FB : DASL.Agents -> formula -> formula.

Notation "\ p" := (FNeg p) (at level 70, right associativity).
Infix "=f=>" := FImp (right associativity, at level 85).
Infix "[. for .]" := FVar (at level 70).

Definition FOr (a b : formula) := (FNeg a) =f=> b.
Infix "a ||| b" := (FOr a b) (at level 75).
Definition FAnd (a b : formula) := \ (FOr (FNeg a) (FNeg b)).
Infix "a /.\ b" := (FAnd a b) (at level 70).
 
Fixpoint formulate (p : prop) (n : nat) : formula :=
  match p with
  | _|_ => FVar (P n) _|_
  | atm A => FVar (P n) (atm A)
  | imp p1 p2 => FImp (formulate p1 n) (formulate p2 (S n))
  | negp p' => FNeg (formulate p' n)
  | K a p' => FK a (formulate p' n)
  | B a p' => FB a (formulate p' n)
  end.

Definition basic_formula (phi : formula) : Prop :=
  match phi with
  | FVar n p => True
  | FProp p => True
  | _ => False
  end.

Fixpoint negative_formula (phi : formula) : Prop :=
  match phi with
  | FVar v p => False
  | FProp p => False
  | FImp phi1 phi2 => (not (negative_formula phi1) \/ negative_formula phi2)
  | FNeg phi' => not (negative_formula phi')
  | FK a phi' => negative_formula phi'
  | FB a phi' => negative_formula phi'
  end.

Definition positive_formula (phi : formula) : Prop :=
  not (negative_formula phi).

Fixpoint boxed_formula (phi : formula) : Prop :=
  match phi with
  | FVar v p => True
  | FProp p => True
  | FImp phi1 phi2 => False
  | FNeg phi' => False
  | FK a phi' => boxed_formula phi'
  | FB a phi' => boxed_formula phi'
  end.


Fixpoint sahlqvist_antecedent (phi : formula) : Prop :=
  match phi with
  | FVar v p => True
  | FProp p => True
  | FImp phi1 phi2 => (negative_formula (FNeg phi1) \/ boxed_formula phi1) 
                   /\ (negative_formula phi2 \/ boxed_formula phi2)
  | FNeg phi' => not (sahlqvist_antecedent phi')
  | FK a phi' => boxed_formula phi'
  | FB a phi' => boxed_formula phi'
  end.

Fixpoint sahlqvist_formula (phi : formula) : Prop :=
  match phi with
  | FProp phi'=> True
  | FVar v phi' => True
  | FImp phi1 phi2 => (sahlqvist_antecedent phi1) /\ (positive_formula phi2)
  | FNeg phi' => sahlqvist_antecedent phi'
  | FK a phi' => boxed_formula phi'
  | FB a phi' => boxed_formula phi'
  end.
  

(* Fixpoint sahlqvist_formula (phi : prop) {struct phi} : Prop :=
  match phi with
  | _|_ => True
  | (atm atom) => True
  | (negp p') => sahlqvist_formula p'
  | (imp p1 p2) => (sahlqvist_antecedent p1) /\ (positive_formula p2)
  | (K a p') => sahlqvist_formula p'
  | (B a p') => sahlqvist_formula p'
  end.
 *)
Lemma K_T_is_sahlqvist : forall (phi : prop) (a : DASL.Agents),
  sahlqvist_formula (FK a (FProp phi) =f=> (FProp phi)).
Proof.
  intros. 
  unfold sahlqvist_formula. split.
  unfold sahlqvist_antecedent. unfold boxed_formula. auto.
  unfold positive_formula; auto.
Qed.

Lemma B_Serial_is_sahlqvist : forall (phi : prop) (a : DASL.Agents),
  sahlqvist_formula (FB a (FProp phi) =f=> \ (FB a (\ FProp phi))).
Proof.
  intros; unfold sahlqvist_formula; split.
  unfold sahlqvist_antecedent. unfold boxed_formula; auto.
  all: try (match goal with [|- ?predicate (?p : formula)] => unfold predicate end; intuition).
Qed.

Lemma B_5_is_sahlqvist : forall (phi : prop) (a : DASL.Agents),
  sahlqvist_formula (\ (FB a (\ FB a (FProp phi))) =f=> (FB a (FProp phi))).
Proof.
intros.
unfold sahlqvist_formula. split.
  unfold sahlqvist_antecedent. unfold boxed_formula. intuition.
  unfold positive_formula. unfold not. unfold negative_formula. intuition.
Qed.

Example Lob_not_sahlqvist : forall (phi : prop) (a : DASL.Agents),
  ~ sahlqvist_formula (FK a (FK a (FProp phi) =f=> (FProp phi)) =f=> FK a (FProp phi)).
Proof.
intros. unfold not. unfold sahlqvist_formula.
  unfold sahlqvist_antecedent. unfold negative_formula. unfold boxed_formula. simpl.
  unfold positive_formula. unfold negative_formula. intuition.
Qed.

Lemma K_B_is_sahlqvist : forall (phi : prop) (a : DASL.Agents),
  sahlqvist_formula (FK a (FProp phi) =f=> FB a (FProp phi)).
Proof.
  intros.
  repeat (match goal with [|- ?predicate (?p : formula)] => unfold predicate end; try intuition).
Qed.

Lemma B_BK_is_sahlqvist : forall (phi : prop) (a : DASL.Agents),
  sahlqvist_formula (FB a (FProp phi) =f=> FB a (FK a (FProp phi))).
Proof.
  intros.
  repeat (match goal with [|- ?predicate (?p : formula)] => unfold predicate end; try intuition).
Qed.

Lemma Hilbert_K_is_sahlqvist : forall (phi psi : prop) (a : DASL.Agents),
  sahlqvist_formula ((FAnd (FProp phi) (FProp psi)) =f=> FProp phi).
Proof.
  intros.
  unfold sahlqvist_formula. split. unfold FAnd. unfold FOr. unfold sahlqvist_antecedent; auto.
  unfold negative_formula. unfold boxed_formula. intuition.
  unfold positive_formula. unfold negative_formula. unfold not. intuition.
Qed. 


(* ((p&q)==>r)
    & p)
    ==>q))
   &p)
   ==>r) 
    
*)
Lemma Hilbert_S_is_sahlqvist : forall (p q r : prop),
  sahlqvist_formula ((FAnd ((FAnd ((FAnd (FProp p) (FProp q)) =f=> FProp r)
                             (FProp p)) 
                             =f=> FProp q)
                           (FProp p)) =f=> FProp r).
Proof.
intros.
unfold sahlqvist_formula; try unfold boxed_formula.
split; unfold positive_formula; intuition.
unfold FAnd; unfold FOr. unfold sahlqvist_antecedent.
unfold not.
unfold boxed_formula. unfold negative_formula. unfold not. intuition.
Qed.

Example McKinsey_not_sahlqvist : forall (phi : prop) (a : DASL.Agents),
  ~ sahlqvist_formula (FK a (FNeg (FK a (FNeg (FProp phi)))) =f=> FNeg (FK a (FNeg (FK a (FProp phi))))).
Proof.
intros. unfold sahlqvist_formula. unfold not. intros. destruct H. unfold sahlqvist_antecedent in H.
unfold boxed_formula in H; auto.
Qed.

Lemma Classic_NOTNOT_is_sahlqvist : forall (p : prop),
  sahlqvist_formula (FNeg (FNeg (FProp p)) =f=> (FProp p)).
Proof.
intros.
unfold sahlqvist_formula; split; repeat (match goal with [|- ?predicate (?p : formula)] => unfold predicate end; try intuition).
Qed.

Theorem DASL_Completeness : forall (phi : prop) (F : frame) (a : DASL.Agents),
  DASL_Frame F ->
  F ||= phi ->
  |-- phi.
Proof.
  intros phi F a. intros.
  
  