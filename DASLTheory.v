Add LoadPath "/Users/sethahrenbach/DASL".
Require Import DASL List.

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

Hint Resolve K_is_refl.

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

Hint Resolve B_is_serial.

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

Hint Resolve B_is_euclidean.

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

Hint Resolve KB_is_Rb_subset_Rk.

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

Hint Resolve B_BK_is_Rb_subset_Rb_compose_Rk.

Lemma Hilbert_K_Frame_Valid : forall (p q : prop) (F : frame) (a : DASL.Agents),
  F ||= (p ==> q ==> p).
Proof.
  intros p q F a.
  repeat (try unfold Frame_validity; intros; try unfold Model_satisfies; intros; try unfold satisfies; intros; assumption).
Qed.

Hint Resolve Hilbert_K_Frame_Valid.

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

Hint Resolve Hilbert_S_Frame_Valid.

Axiom base_double_negation : forall p,
  not (not p) = p.

Hint Resolve base_double_negation.

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

Hint Resolve Classic_NOTNOT_Frame_Valid.

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

Hint Resolve MP_Frame_Valid.

Lemma K_Nec_Frame_Valid : forall (p : prop) (F : frame) (a : DASL.Agents),
  F ||= p ->
  F ||= K a p.
Proof.
  intros p F a.
  unfold Frame_validity; unfold Model_satisfies; unfold satisfies; intros.
  pose proof H Val0 Ags y; clear H. assumption.
Qed.

Hint Resolve K_Nec_Frame_Valid.

Lemma K_K_Frame_Valid : forall (p q : prop) (F : frame) (a : DASL.Agents),
  F ||= (K a p ==> K a (p ==> q) ==> K a q).
Proof.
  intros p q F a.
  unfold Frame_validity; unfold Model_satisfies; unfold satisfies. intros.
  pose proof H0 y H1; clear H0.
  pose proof H y H1; clear H. pose proof H2 H0; assumption.
Qed.

Hint Resolve K_K_Frame_Valid.

Lemma B_K_Frame_Valid : forall (p q : prop) (F : frame) (a : DASL.Agents),
  F ||= (B a p ==> B a (p ==> q) ==> B a q).
Proof.
  intros p q F a.
  unfold Frame_validity; unfold Model_satisfies; unfold satisfies. intros.
  pose proof H0 y H1; clear H0.
  pose proof H y H1; clear H. pose proof H2 H0; assumption.
Qed.

Hint Resolve B_K_Frame_Valid.

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
    induction H0; eauto.  
Qed. 

Inductive formula : Type :=
  | FProp : prop -> formula
  | FAnd : formula -> formula -> formula
  | FOr : formula -> formula -> formula
  | FImp : formula -> formula -> formula
  | FNeg : formula -> formula
  | FK : DASL.Agents -> formula -> formula
  | FB : DASL.Agents -> formula -> formula.

Notation "\ p" := (FNeg p) (at level 70, right associativity).
Infix "=f=>" := FImp (right associativity, at level 85).

Infix "|||" := FOr (right associativity, at level 75).

Infix "&&&" := FAnd (right associativity, at level 75).

Fixpoint normal_form (phi : formula) : formula :=
  match phi with
  | FProp phi'=> FProp phi'
  | FAnd phi1 phi2 => FAnd (normal_form phi1) (normal_form phi2)
  | FOr phi1 phi2 => FOr (normal_form phi1) (normal_form phi2)
  | FImp phi1 phi2 => FOr (FNeg (normal_form phi1)) (normal_form phi2)
  | FNeg phi' => FNeg (normal_form phi')
  | FK a phi' => FK a (normal_form phi')
  | FB a phi' => FB a (normal_form phi')
  end.

Definition basic_formula (phi : formula) : Prop :=
  match phi with
  | FProp p => True
  | _ => False
  end.

Fixpoint negative_formula (phi : formula) : Prop :=
  match phi with
  | FProp p => False
  | FAnd phi1 phi2 => (negative_formula phi1) /\ (negative_formula phi2)
  | FOr phi1 phi2 => (negative_formula phi1) /\ (negative_formula phi2)
  | FImp phi1 phi2 => (negative_formula phi1) /\ (negative_formula phi2)
  | FNeg phi' => not (negative_formula phi')
  | FK a phi' => negative_formula phi'
  | FB a phi' => negative_formula phi'
  end.

Fixpoint positive_formula (phi : formula) : Prop :=
  match phi with
  | FProp p => True
  | FAnd phi1 phi2 => (positive_formula phi1) /\ (positive_formula phi2)
  | FOr phi1 phi2 => (positive_formula phi1) /\ (positive_formula phi2)
  | FImp phi1 phi2 => (positive_formula phi1) /\ (positive_formula phi2)
  | FNeg phi' => not (positive_formula phi')
  | FK a phi' => positive_formula phi'
  | FB a phi' => positive_formula phi'
  end.

Fixpoint boxed_formula (phi : formula) : Prop :=
  match phi with
  | FProp p => True
  | FAnd phi1 phi2 => False
  | FOr phi1 phi2 => False
  | FImp phi1 phi2 => False
  | FNeg phi' => False
  | FK a phi' => boxed_formula phi'
  | FB a phi' => boxed_formula phi'
  end.

Fixpoint s_a_component (phi : formula) : Prop :=
  match phi with
  | FProp p => True
  | FAnd phi1 phi2 => (s_a_component phi1) /\ (s_a_component phi2)
  | FOr phi1 phi2 => (s_a_component phi1) /\ (s_a_component phi2)
  | FImp phi1 phi2 => not (s_a_component phi1) /\ (s_a_component phi2)
  | FNeg phi' => match phi' with
                 | FProp p => True
                 | FAnd p1 p2 => positive_formula p1 /\ positive_formula p2
                 | FOr p1 p2 => positive_formula p1 /\ positive_formula p2
                 | FImp p1 p2 => negative_formula p1 /\ positive_formula p2
                 | FNeg p' => s_a_component p'
                 | FK a p' => not (s_a_component p')
                 | FB a p' => not (s_a_component p')
                 end
  | FK a phi' => boxed_formula phi'
  | FB a phi' => boxed_formula phi'
  end.

Fixpoint sahlqvist_antecedent (phi : formula) : Prop :=
  s_a_component (normal_form phi).

Definition sahlqvist_implication (phi psi : formula) : Prop :=
  sahlqvist_antecedent (phi) /\ positive_formula (psi).

Fixpoint prop_in_formula (phi : prop) (psi : formula) : Prop :=
  match psi with
    | FProp psi' => phi = psi'
    | FAnd psi1 psi2 => (prop_in_formula phi psi1) \/ (prop_in_formula phi psi2)
    | FOr psi1 psi2 => (prop_in_formula phi psi1) \/ (prop_in_formula phi psi2)
    | FImp psi1 psi2 => (prop_in_formula phi psi1) \/ (prop_in_formula phi psi2)
    | FNeg psi' => (prop_in_formula phi psi')
    | FK a psi' => (prop_in_formula phi psi')
    | FB a psi' => (prop_in_formula phi psi')
  end.

Fixpoint share_prop_letter (phi psi : formula) {struct phi} : Prop :=
  match phi with
    | FProp phi' => match psi with
                      | FProp psi' => phi' = psi'
                      | FAnd psi1 psi2 => (prop_in_formula phi' psi1) \/ (prop_in_formula phi' psi2)
                      | FOr psi1 psi2 => (prop_in_formula phi' psi1) \/ (prop_in_formula phi' psi2)
                      | FImp psi1 psi2 => (prop_in_formula phi' psi1) \/ (prop_in_formula phi' psi2)
                      | FNeg psi' => (prop_in_formula phi' psi')
                      | FK a psi' => (prop_in_formula phi' psi')
                      | FB a psi' => (prop_in_formula phi' psi')
                    end
    | FAnd phi1 phi2 => (share_prop_letter phi1 psi) \/ (share_prop_letter phi2 psi)
    | FOr phi1 phi2 => (share_prop_letter phi1 psi) \/ (share_prop_letter phi2 psi)
    | FImp phi1 phi2 => (share_prop_letter phi1 psi) \/ (share_prop_letter phi2 psi)
    | FNeg phi' => (share_prop_letter phi' psi)
    | FK a phi' => (share_prop_letter phi' psi)
    | FB a phi' => (share_prop_letter phi' psi)
  end.

Fixpoint sahlqvist_formula (phi : formula) : Prop :=
  match phi with
    | FProp phi'=> True
    | FAnd phi1 phi2 => (sahlqvist_formula phi1) /\ (sahlqvist_formula phi2)
    | FOr phi1 phi2 => not (share_prop_letter phi1 phi2) /\ (sahlqvist_formula phi1) /\ (sahlqvist_formula phi2)
    | FImp phi1 phi2 => (sahlqvist_implication phi1 phi2)
    | FNeg phi' => False
    | FK a phi' => sahlqvist_formula phi'
    | FB a phi' => sahlqvist_formula phi'
  end.


Lemma sahlqvist_antecedent_p_and_q : forall (p q : prop),
  sahlqvist_antecedent (FAnd (FProp p) (FProp q)).
Proof.
  intros. simpl; auto.
Qed.  
  
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
  intros. simpl. unfold sahlqvist_implication; split; unfold positive_formula; simpl; intuition. 
Qed.

Hint Resolve K_T_is_sahlqvist.

Ltac sahlqvist_reduce := simpl; try (unfold sahlqvist_implication; split);
  try (unfold positive_formula; simpl; intuition);
  try (unfold sahlqvist_antecedent; simpl; intuition; unfold normal_form).
  

Ltac not_sahlqvist := try (unfold sahlqvist_formula; unfold sahlqvist_implication; simpl; intuition).

Lemma B_Serial_is_sahlqvist : forall (phi : prop) (a : DASL.Agents),
  sahlqvist_formula (FB a (FProp phi) =f=> \ (FB a (\ FProp phi))).
Proof.
  intros; sahlqvist_reduce.
Qed.

Hint Resolve B_Serial_is_sahlqvist.

Lemma B_5_is_sahlqvist : forall (phi : prop) (a : DASL.Agents),
  sahlqvist_formula (\ (FB a (\ FB a (FProp phi))) =f=> (FB a (FProp phi))).
Proof.
intros; sahlqvist_reduce. 
Qed.

Hint Resolve B_5_is_sahlqvist.

Example Lob_not_sahlqvist : forall (phi : prop) (a : DASL.Agents),
  ~ sahlqvist_formula (FK a (FK a (FProp phi) =f=> (FProp phi)) =f=> FK a (FProp phi)).
Proof.
intros. unfold not. not_sahlqvist. 
Qed.

Lemma K_B_is_sahlqvist : forall (phi : prop) (a : DASL.Agents),
  sahlqvist_formula (FK a (FProp phi) =f=> FB a (FProp phi)).
Proof.
  intros; sahlqvist_reduce.
Qed.

Hint Resolve K_B_is_sahlqvist.

Lemma B_BK_is_sahlqvist : forall (phi : prop) (a : DASL.Agents),
  sahlqvist_formula (FB a (FProp phi) =f=> FB a (FK a (FProp phi))).
Proof.
  intros; sahlqvist_reduce.
Qed.

Hint Resolve B_BK_is_sahlqvist.

(* Lemma Hilbert_K_is_sahlqvist : forall (p q : prop) (a : DASL.Agents),
  sahlqvist_formula (normal_form ((FProp p) =f=> (FProp q) =f=> (FProp p))).
Proof.
  intros. simpl; auto.
Qed.

Hint Resolve Hilbert_K_is_sahlqvist. 

Lemma Hilbert_S_is_sahlqvist : forall (p q r : prop),
  sahlqvist_formula (normal_form (((FProp p) =f=> (FProp q) =f=> (FProp r)) =f=>
                    ((FProp p) =f=> (FProp q)) =f=>
                    ((FProp p) =f=> (FProp r)))).
Proof.
intros. simpl; auto. 
Qed. 

Hint Resolve Hilbert_S_is_sahlqvist. *)

Example McKinsey_not_sahlqvist : forall (phi : prop) (a : DASL.Agents),
  ~ sahlqvist_formula (FK a (FNeg (FK a (FNeg (FProp phi)))) =f=> FNeg (FK a (FNeg (FK a (FProp phi))))).
Proof.
intros; not_sahlqvist.  
Qed.

Lemma Classic_NOTNOT_is_sahlqvist : forall (p : prop),
  sahlqvist_formula (FNeg (FNeg (FProp p)) =f=> (FProp p)).
Proof.
intros; sahlqvist_reduce. 
Qed.

Hint Resolve Classic_NOTNOT_is_sahlqvist.

Example Church_Rosser_is_sahlqvist : forall (phi : prop) (a : DASL.Agents),
  sahlqvist_formula (\ (FK a (\ (FK a (FProp phi)))) =f=> (FK a (\ (FK a (\ (FProp phi)))))).
Proof.
  intros; sahlqvist_reduce.
Qed.

Example Brouwer_is_sahlqvist : forall (phi : prop) (a : DASL.Agents),
  sahlqvist_formula ((FProp phi) =f=> \ (FK a (\ (FK a (FProp phi))))).
Proof.
  intros; sahlqvist_reduce.
Qed.

Example Brouwer_is_not_sahlqvist : forall (phi : prop) (a : DASL.Agents),
  ~ ( sahlqvist_formula ((FProp phi) =f=> \ (FK a (\ (FK a (FProp phi))))) ).
Proof.
intros; not_sahlqvist. Abort.

Example Very_simple_Blackburn: forall (p : prop) (a : DASL.Agents),
  sahlqvist_formula (((FProp p) &&& (\ (FK a (\ (\ (FK a (\ (FProp p)))))))) =f=>
    (\ (FK a (\ (FProp p))))).
Proof.
intros; sahlqvist_reduce. 
Qed.

Example sahlqvist_Blackburn_example_1 : forall (phi : prop) (a : DASL.Agents),
  sahlqvist_formula (FK a ((FProp phi) =f=> (\ (FK a (\ (FProp phi)))))).
Proof.
  intros; sahlqvist_reduce. 
Qed.

Fixpoint form_to_prop (phi : formula) : prop :=
  match phi with
  | FProp phi' => phi'
  | FAnd phi1 phi2 => (form_to_prop phi1) & (form_to_prop phi2)
  | FOr phi1 phi2 => (form_to_prop phi1) V (form_to_prop phi2)
  | FImp phi1 phi2 => (form_to_prop phi1) ==> (form_to_prop phi2)
  | FNeg phi' => ! (form_to_prop phi')
  | FK a phi' => K a (form_to_prop phi')
  | FB a phi' => B a (form_to_prop phi')
  end.

Fixpoint prop_to_form (phi : prop) : formula :=
  match phi with
  | _|_ => FProp (_|_)
  | (atm atom) => FProp (atm atom)
  | (imp phi1 phi2) => (prop_to_form phi1) =f=> (prop_to_form phi2)
  | (negp phi') => FNeg (prop_to_form phi')
  | (K a phi') => FK a (prop_to_form phi')
  | (B a phi') => FB a (prop_to_form phi')
  end.


Inductive Ftheorem : formula -> Prop :=
   |FHilbert_K: forall p q : prop, Ftheorem ((FProp p) =f=> (FProp q) =f=> (FProp p))
   |FHilbert_S: forall p q r : prop, Ftheorem (((FProp p)=f=>(FProp q)=f=>(FProp r))=f=>((FProp p)=f=>(FProp q))=f=>((FProp p)=f=>(FProp r)))
   |FClassic_NOTNOT : forall p : prop, Ftheorem ((\ (\ (FProp p))) =f=> (FProp p))
   |FMP : forall p q : prop, Ftheorem ((FProp p) =f=> (FProp q)) -> Ftheorem (FProp p) -> Ftheorem (FProp q)
   |FK_Nec : forall (a : DASL.Agents) (p : prop), Ftheorem (FProp p) -> Ftheorem (FK a (FProp p))
   |FK_K : forall (a : DASL.Agents) (p q : prop), Ftheorem (FK a (FProp p) =f=> FK a ((FProp p) =f=> (FProp q)) =f=> FK a (FProp q))
   |FK_T : forall (a : DASL.Agents) (p : prop), Ftheorem (FK a (FProp p) =f=> (FProp p))
   |FB_K : forall (a : DASL.Agents) (p q : prop), Ftheorem (FB a (FProp p) =f=> FB a ((FProp p) =f=> (FProp q)) =f=> FB a (FProp q))
   |FB_Serial : forall (a : DASL.Agents) (p : prop), Ftheorem (FB a (FProp p) =f=> \ (FB a (\ (FProp p))))
   |FB_5 : forall (a : DASL.Agents) (p : prop), Ftheorem (\ (FB a (FProp p)) =f=> FB a (\ (FB a (FProp p))))
   |FK_B : forall (a : DASL.Agents) (p : prop), Ftheorem (FK a (FProp p) =f=> FB a (FProp p))
   |FB_BK : forall (a : DASL.Agents) (p : prop), Ftheorem (FB a (FProp p) =f=> FB a (FK a (FProp p))).

Notation "|f-" := Ftheorem (at level 80).
Check Build_frame.
Check frame.


Definition DASL_Axioms (p q r : prop) (a : DASL.Agents) := 
(FK a (FProp p) =f=> FK a ((FProp p) =f=> (FProp q)) =f=> FK a (FProp q))
:: (FK a (FProp p) =f=> (FProp p))
:: (FB a (FProp p) =f=> FB a ((FProp p) =f=> (FProp q)) =f=> FB a (FProp q))
:: (FB a (FProp p) =f=> \ (FB a (\ (FProp p))))
:: (\ (FB a (\ (FB a (FProp p)))) =f=> FB a (FProp p))
:: (FK a (FProp p) =f=> FB a (FProp p))
:: (FB a (FProp p) =f=> FB a (FK a (FProp p)))
:: nil.


Fixpoint Complete_via_Sahlqvist (l : list formula) : Prop :=  
  match l with
  | nil => True
  | (l' :: els) => sahlqvist_formula (l') /\ Complete_via_Sahlqvist (els)
  end.


Axiom sahlqvist_is_canonical : forall (phi : prop),
  sahlqvist_formula (prop_to_form phi) ->
  (forall F: frame,
    F ||= phi ->
    |-- phi).

Ltac sahlqvist_complete_list :=
  match goal with [ |- ?P1 (?P2 _ _ _ _) ] => unfold P2; repeat (constructor; auto; sahlqvist_reduce) end.

Theorem DASL_Axioms_Complete : forall (p q r : prop) (a : DASL.Agents),
  Complete_via_Sahlqvist (DASL_Axioms p q r a).
Proof.
intros; sahlqvist_complete_list.
Qed.

Lemma schema_to_prop_completeness : forall (phi : formula),
  |f- phi ->
  |-- form_to_prop phi.
Proof.
intros.
induction H; simpl; try constructor.
simpl in IHFtheorem1.
simpl in IHFtheorem2. pose proof MP p q IHFtheorem1; auto.
simpl in IHFtheorem; auto.
Qed.

Theorem DASL_Completeness : forall (phi : formula) (F : frame) (val: (W F) -> Atoms -> Prop) (a : DASL.Agents),
  DASL_Frame F ->  
  F ||= (form_to_prop) phi ->
  |f- phi.
Proof. Abort.