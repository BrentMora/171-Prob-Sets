From LF Require Export Tactics.

Definition plus_claim : Prop := 2 + 2 = 4.
Check plus_claim : Prop.

Theorem plus_claim_is_true :
  plus_claim.
Proof. reflexivity. Qed.

Definition is_three (n : nat) : Prop :=
  n = 3.

Definition injective {A B} (f : A -> B) : Prop := forall x y : A, f x = f y -> x = y.

Lemma succ_inj : injective S.
Proof.
  unfold injective. intros. injection H. intros. apply H0.
Qed.

Example and_example : 3 + 4 = 7 /\ 2 * 2 = 4.
Proof.
  split.
  - (* 3 + 4 = 7 *) reflexivity.
  - (* 2 * 2 = 4 *) reflexivity.
Qed.

Example and_example' : 3 + 4 = 7 /\ 2 * 2 = 4.
Proof.
  apply conj.
  - (* 3 + 4 = 7 *) reflexivity.
  - (* 2 + 2 = 4 *) reflexivity.
Qed.

Example plus_is_O : forall n m : nat, n + m = 0 -> n = 0 /\ m = 0.
Proof. 
  intros. split.
  - destruct m eqn : Hm.
    + rewrite add_0_r in H. rewrite H. reflexivity.
    + destruct n eqn : Hn.
      -- reflexivity.
      -- rewrite <- plus_n_Sm in H. discriminate H.
  - destruct m eqn : Hm.
    + reflexivity.
    + destruct n eqn : Hn.
      -- discriminate H.
      -- rewrite <- plus_n_Sm in H. discriminate H.
Qed.

Lemma and_example2 :
  forall n m : nat, n = 0 /\ m = 0 -> n + m = 0.
Proof.
  intros. destruct H. rewrite H. rewrite H0. reflexivity.
Qed. 

Lemma and_example3 :
  forall n m : nat, n + m = 0 -> n * m = 0.
Proof.
  intros. apply plus_is_O in H. destruct H. rewrite H0. rewrite mul_0_r. reflexivity.
Qed.

Lemma proj1 : forall P Q : Prop,
  P /\ Q -> P.
Proof.
  intros P Q HPQ.
  destruct HPQ as [HP _].
  apply HP. 
Qed.

Lemma proj2 : forall P Q : Prop,
  P /\ Q -> Q.
Proof.
  intros P Q HPQ.
  destruct HPQ as [_ HQ].
  apply HQ. 
Qed.

Theorem and_commut : forall P Q : Prop,
  P /\ Q -> Q /\ P.
Proof.
  intros P Q [HP HQ].
  split.
    - (* left *) apply HQ.
    - (* right *) apply HP. 
Qed.

Theorem and_assoc : forall P Q R : Prop,
  P /\ (Q /\ R) -> (P /\ Q) /\ R.
Proof.
  intros. destruct H. destruct H0.
  split. split. apply H. apply H0. apply H1.
Qed.

Lemma factor_is_O:
  forall n m : nat, n = 0 \/ m = 0 -> n * m = 0.
Proof.
  intros. destruct H.
  - rewrite H. reflexivity.
  - rewrite H. rewrite mul_0_r. reflexivity.
Qed.

Lemma or_intro_l : forall A B : Prop, A -> A \/ B.
Proof.
  intros. left. apply H.
Qed.

Lemma zero_or_succ :
  forall n : nat, n = 0 \/ n = S (pred n).
Proof.
  intros. destruct n eqn : Hn.
  - left. reflexivity.
  - right. simpl. reflexivity.
Qed.

Lemma mult_is_O :
  forall n m, n * m = 0 -> n = 0 \/ m = 0.
Proof.
  intros. destruct n eqn : Hn.
  - left. reflexivity.
  - simpl in H. destruct m eqn : Hm.
    + right. reflexivity.
    + simpl in H. discriminate H.
Qed.

Theorem or_commut : forall P Q : Prop,
  P \/ Q -> Q \/ P.
Proof.
  intros. destruct H.
  - right. apply H.
  - left. apply H.
Qed.    

Definition not (P : Prop) := P -> False.
Check not : Prop -> Prop.
Notation "~ x" := (not x) : type_scope.

Theorem ex_falso_quodlibet : forall (P : Prop),
  False -> P.
Proof.
  intros P contra.
  destruct contra.
Qed.

Theorem not_implies_our_not : forall (P:Prop),
  ~ P -> (forall (Q : Prop), P -> Q).
Proof.
  intros. unfold not in H. apply H in H0. destruct H0.
Qed.

Notation "x <> y" := (~ (x = y)) : type_scope.

Theorem zero_not_one : 0 <> 1.
Proof.
  unfold not. intros. discriminate H.
Qed.

Theorem not_False :
  ~ False.
Proof.
  unfold not. intros. destruct H.
Qed.

Theorem contradiction_implies_anything : forall P Q : Prop,
  (P /\ ~ P) -> Q.
Proof.
  intros. destruct H. unfold not in H0. apply H0 in H. destruct H.
Qed. 

Theorem double_neg : forall P : Prop,
  P -> ~ ~ P.
Proof.
  intros. unfold not. intros. apply H0 in H. destruct H.
Qed.

Theorem contrapositive : forall (P Q : Prop),
  (P -> Q) -> ( ~ Q ->  ~P).
Proof.
  intros. unfold not. intros. apply H in H1. unfold not in H0.
  apply H0 in H1. destruct H1.
Qed.

Theorem not_both_true_and_false : forall P : Prop,
  ~ (P /\ ~ P).
Proof.
  intros. unfold not. intros. destruct H. apply H0 in H. destruct H.
Qed.

Theorem de_morgan_not_or : forall (P Q : Prop),
    ~ (P \/ Q) -> ~ P /\ ~ Q.
Proof.
  intros. split.
  - unfold not. intros. unfold not in H. destruct H. left. apply H0.
  - unfold not. intros. unfold not in H. destruct H. right. apply H0.
Qed.

Lemma not_S_pred_n : ~ (forall n : nat, S (pred n) = n).
Proof.
  unfold not. intros. specialize H with (n := 0). discriminate H.
Qed.

Theorem not_true_is_false : forall b : bool,
  b <> true -> b = false.
Proof.
  intros. unfold not in H. destruct b eqn : Hb.
  - apply ex_falso_quodlibet. apply H. reflexivity.
  - reflexivity.
Qed.

Lemma True_is_true : True.
Proof. reflexivity. Qed.

Definition disc_fn (n : nat) : Prop :=
  match n with
  | O => True
  | S _ => False
  end.

Theorem disc_example : forall n, ~ (O = S n).
Proof.
  intros. unfold not. intros.
  assert (disc_fn 0). {simpl. apply I. }
  rewrite H in H0. simpl in H0. apply H0.
Qed.

Definition listdisc_fn (X : Type) (l : list X) : Prop :=
  match l with
  | [] => True
  | h :: _ => False
  end.

Theorem nil_is_not_cons : forall X (x : X) (xs : list X), ~ (nil = x :: xs).
Proof.
  intros. unfold not. intros.
  assert (listdisc_fn X []). {simpl. apply I. }
  rewrite H in H0. simpl in H0. apply H0.
Qed.

Print "<->".

Theorem iff_sym : forall P Q : Prop,
  (P <-> Q) -> (Q <-> P).
Proof.
  intros. split. destruct H. apply H0. apply H.
Qed.

Lemma not_true_iff_false : forall b,
  b <> true <-> b = false.
Proof.
  intros. split.
  - intros. apply not_true_is_false in H. apply H.
  - intros. unfold not. intros. rewrite H0 in H. discriminate H.
Qed.

Lemma apply_iff_example1 :
  forall P Q R : Prop, (P <-> Q) -> (Q -> R) -> (P -> R).
Proof.
  intros. apply H0. apply H. apply H1.
Qed.

Lemma apply_iff_example2 :
  forall P Q R : Prop, (P <-> Q) -> (P -> R) -> (Q -> R).
Proof.
  intros. apply H0. apply H. apply H1.
Qed.

Theorem iff_refl : forall P : Prop,
  P <-> P.
Proof.
  intros. split.
  - intros. apply H.
  - intros. apply H.
Qed.

Theorem iff_trans : forall P Q R : Prop,
  (P <-> Q) -> (Q <-> R) -> (P <-> R).
Proof.
  intros. split.
  - intros. apply H0. apply H. apply H1.
  - intros. apply H. apply H0. apply H1.
Qed.    

Theorem or_distributes_over_and : forall P Q R : Prop,
  P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R).
Proof.
  intros. split.
  - intros. split.
    + destruct H. left. apply H. right. destruct H. apply H.
    + destruct H. left. apply H. right. destruct H. apply H0.
  - intros. destruct H. destruct H.
    + left. apply H.
    + destruct H0.
      -- left. apply H0.
      -- right. split. apply H. apply H0.
Qed.

Lemma mul_eq_0 : forall n m, n * m = 0 <-> n = 0 \/ m = 0.
Proof.
  intros. split.
  - intros. apply mult_is_O. apply H.
  - intros. apply factor_is_O in H. apply H.
Qed.   

Theorem or_assoc :
  forall P Q R : Prop, P \/ (Q \/ R) <-> (P \/ Q) \/ R.
Proof.
  intros. split.
  - intros. destruct H. left. left. apply H. destruct H. left. right. apply H. right. apply H.
  - intros. destruct H. destruct H. left. apply H. right. left. apply H. right. right. apply H.
Qed.

Lemma mul_eq_0_ternary :
  forall n m p, n * m * p = 0 <-> n = 0 \/ m = 0 \/ p = 0.
Proof.
  intros. rewrite or_assoc. rewrite <- mul_eq_0. rewrite <- mul_eq_0.
  reflexivity.
Qed.

Definition Even x := exists n : nat, x = double n.

Lemma four_is_Even : Even 4.
Proof. unfold Even. exists 2. reflexivity. Qed.

Theorem exists_example_2 : forall n,
  (exists m, n = 4 + m) ->
  (exists o, n = 2 + o).
Proof.
  intros. destruct H. rewrite H. exists (2 + x). reflexivity.
Qed.

Theorem dist_not_exists : forall (X : Type) (P : X -> Prop),
  (forall x, P x) -> ~ (exists x, ~ P x).
Proof.
  intros. unfold not. intros. destruct H0. apply H0. apply H.
Qed.

Theorem dist_exists_or : forall (X : Type) (P Q : X -> Prop),
  (exists x, P x \/ Q x) <-> (exists x, P x) \/ (exists x, Q x).
Proof.
  intros. split.
  - intros. destruct H. destruct H.
    + left. exists x. apply H.
    + right. exists x. apply H.
  - intros. destruct H.
    + destruct H. exists x. left. apply H.
    + destruct H. exists x. right. apply H.
Qed.

Theorem leb_plus_exists : forall n m, n <=? m = true -> exists x, m = n + x.
Proof.
  intros. apply sub_add_leb in H. symmetry in H. exists (m - n).
  rewrite add_comm. apply H.
Qed.

Fixpoint In {A : Type} (x : A) (l : list A) : Prop :=
  match l with
  | [] => False
  | h :: t => h = x \/ In x t
  end.

Example In_example_1 : In 4 [1; 2; 3; 4; 5].
Proof.
  simpl. right. right. right. left. reflexivity.
Qed.

Example In_example_2 :
  forall n, In n [2; 4] ->
  exists n', n = 2 * n'.
Proof.
  intros. simpl in H. destruct H.
  - rewrite <- H. exists 1. reflexivity.
  - destruct H.
    + rewrite <- H. exists 2. reflexivity.
    + destruct H.
Qed.

Theorem In_map :
  forall (A B : Type) (f : A -> B) (l : list A) (x : A),
         In x l -> In (f x) (map f l).
Proof.
  intros. induction l.
  - simpl in H. destruct H.
  - simpl in H. destruct H.
    + simpl. left. rewrite H. reflexivity.
    + simpl. apply IHl in H. right. apply H.
Qed.

Theorem In_map_iff :
  forall (A B : Type) (f : A -> B) (l : list A) (y : B),
         In y (map f l) <->
         exists x, f x = y /\ In x l.
Proof.
  intros. split.
  - induction l.
    + intros. simpl in H. destruct H.
    + intros. simpl in H. destruct H.
      -- exists x. split. apply H. simpl. left. reflexivity.
      -- apply IHl in H. destruct H. destruct H. exists x0. split. apply H. simpl. right. apply H0.
  - intros. destruct H. destruct H. induction l.
    + destruct H0.
    + simpl. simpl in H0. destruct H0.
      -- rewrite <- H0 in H. left. apply H.
      -- apply IHl in H0. right. apply H0.
Qed.

Theorem In_app_iff : forall A l l' (a : A),
  In a (l ++ l') <-> In a l \/ In a l'.
Proof.
  intros A l. induction l.
  - split.
    + intros. simpl in H. right. apply H.
    + intros. destruct H. simpl in H. destruct H. simpl. apply H.
  - split.
    + intros. simpl in H. destruct H.
      -- left. simpl. left. apply H.
      -- apply IHl in H. destruct H.
        ++ left. simpl. right. apply H.
        ++ right. apply H.
    + intros. destruct H.
      -- simpl. simpl in H. destruct H.
        ++ left. apply H.
        ++ right. simpl. rewrite IHl. left. apply H.
      -- simpl. right. rewrite IHl. right. apply H.
Qed.

Fixpoint All {T : Type} (P : T -> Prop) (l : list T) : Prop :=
  match l with
  | [] => True
  | h :: t => (P h) /\ All P t
  end.

Theorem All_In :
  forall T (P : T -> Prop) (l : list T),
    (forall x, In x l -> P x) <-> All P l.
Proof.
  intros. split.
  - intros. induction l.
    + simpl. apply I.
    + simpl. split.
      -- apply H. simpl. left. reflexivity.
      -- apply IHl. intros. apply H. simpl. right. apply H0.
  - intros. induction l.
    + simpl in H0. destruct H0.
    + simpl in H0. simpl in H. destruct H. destruct H0.
      -- rewrite H0 in H. apply H.
      -- apply IHl.
        +++ apply H1.
        +++ apply H0.
Qed.

Definition combine_odd_even (Podd Peven : nat -> Prop) : nat -> Prop :=
  fun n => ((odd n = true) /\ Podd n) \/ ((odd n = false) /\ Peven n).

Theorem combine_odd_even_intro :
  forall (Podd Peven : nat -> Prop) (n : nat),
    (odd n = true -> Podd n) ->
    (odd n = false -> Peven n) ->
    combine_odd_even Podd Peven n.
Proof.
  intros. destruct (odd n) eqn : Hn.
  - unfold combine_odd_even. left. split.
    + apply Hn.
    + assert (true = true). {reflexivity. }
      -- apply H in H1. apply H1.
  - unfold combine_odd_even. right. split.
    + apply Hn.
    + assert (false = false). {reflexivity. }
      -- apply H0 in H1. apply H1.
Qed.

Theorem combine_odd_even_elim_odd :
  forall (Podd Peven : nat -> Prop) (n : nat),
    combine_odd_even Podd Peven n ->
    odd n = true ->
    Podd n.
Proof.
  intros. unfold combine_odd_even in H. destruct H.
  - destruct H. apply H1.
  - destruct H. rewrite H0 in H. discriminate H.
Qed.

Theorem combine_odd_even_elim_even :
  forall (Podd Peven : nat -> Prop) (n : nat),
    combine_odd_even Podd Peven n ->
    odd n = false ->
    Peven n.
Proof.
  intros. unfold combine_odd_even in H. destruct H.
  - destruct H. rewrite H0 in H. discriminate H.
  - destruct H. apply H1.
Qed.

Lemma add_comm3 :
  forall x y z, x + (y + z) = (z + y) + x.
Proof.
  intros x y z.
  rewrite (add_comm x (y + z)).
  rewrite (add_comm y z).
  reflexivity.
Qed.

Theorem in_not_nil :
  forall A (x : A) (l : list A), In x l -> l <> [].
Proof.
  intros. unfold not. intros. rewrite H0 in H. simpl in H. destruct H.
Qed.

Lemma in_not_nil_42_take4 :
  forall l : list nat, In 42 l -> l <> [].
Proof.
  intros l H.
  apply (in_not_nil nat 42).
  apply H.
Qed.

Lemma in_not_nil_42_take5 :
  forall l : list nat, In 42 l -> l <> [].
Proof.
  intros l H.
  apply (in_not_nil _ _ _ H).
Qed.

Example lemma_application_ex :
  forall {n : nat} {ns : list nat},
    In n (map (fun m => m * 0) ns) ->
    n = 0.
Proof.
  intros n ns H.
  destruct (proj1 _ _ (In_map_iff _ _ _ _ _) H)
           as [m [Hm _]].
  rewrite mul_0_r in Hm. rewrite <- Hm. reflexivity.
Qed.

Lemma even_double : forall k, even (double k) = true.
Proof.
  intros. induction k.
  - reflexivity.
  - simpl. apply IHk.
Qed.

Lemma even_double_conv_lemma : forall (X : Type) (P : X -> bool) (x : X), negb (P x) = true -> P x = false.
Proof.
  intros. destruct (P x).
  - discriminate H.
  - reflexivity.
Qed.   

Lemma even_double_conv_lemma2 : forall (X : Type) (P : X -> bool) (x : X), negb (P x) = false -> P x = true.
Proof.
  intros. destruct (P x).
  - reflexivity.
  - discriminate H.
Qed.   

Lemma even_double_conv : forall n, exists k,
  n = if even n then double k else S (double k).
Proof.
  intros. induction n.
  - simpl. exists 0. reflexivity.
  - destruct (even (S n)) eqn : Hn.
    + rewrite even_S in Hn.
      assert (even n = false). {apply even_double_conv_lemma in Hn. apply Hn. }
      rewrite H in IHn. destruct IHn. exists (S x).
      rewrite H0. simpl. reflexivity.
    + rewrite even_S in Hn.
      assert (even n = true). {apply even_double_conv_lemma2 in Hn. apply Hn. }
      rewrite H in IHn. destruct IHn. exists x.
      rewrite H0. reflexivity.  
Qed.

Theorem even_bool_prop : forall n,
  even n = true <-> Even n.
Proof.
  intros. induction n.
  - split.
    + intros. unfold Even. exists 0. reflexivity.
    + reflexivity.
  - split.
    + intros. unfold Even.
      destruct (even_double_conv n). 
      rewrite even_S in H.
      apply even_double_conv_lemma in H.
      rewrite H in H0.
      exists (S x). rewrite H0. reflexivity.
    + intros. unfold Even in H. destruct H. rewrite H.
      apply even_double.
Qed.

Theorem eqb_eq : forall n1 n2 : nat,
  n1 =? n2 = true <-> n1 = n2.
Proof.
  intros n1 n2. split.
  - apply eqb_true.
  - intros H. rewrite H. rewrite eqb_refl. reflexivity.
Qed.

Example even_1000'' : Even 1000.
Proof. apply even_bool_prop. reflexivity. Qed.

Example not_even_1001' : ~ (Even 1001).
Proof.
  unfold not.
  intros. 
  apply even_bool_prop in H.
  simpl in H.
  discriminate H.
Qed.

Lemma plus_eqb_example : forall n m p : nat,
  n =? m = true -> n + p =? m + p = true.
Proof.
  intros.
  rewrite eqb_eq in H.
  rewrite eqb_eq.
  rewrite H.
  reflexivity.
Qed.

Theorem andb_true_iff : forall b1 b2 : bool,
  b1 && b2 = true <-> b1 = true /\ b2 = true.
Proof.
  intros. split.
  - intros. split.
    + unfold "&&" in H. destruct b1 eqn : Hb.
      -- reflexivity.
      -- discriminate H.
    + unfold "&&" in H. destruct b1 eqn : Hb.
      -- apply H.
      -- discriminate H.
  - intros. destruct H. rewrite H. rewrite H0.
    reflexivity.
Qed.

Theorem orb_true_iff : forall b1 b2,
  b1 || b2 = true <-> b1 = true \/ b2 = true.
Proof.
  intros. split.
  - intros. unfold "||" in H. destruct b1 eqn : Hb.
    + left. reflexivity.
    + right. apply H.
  - intros. destruct H.
    + unfold "||". destruct b1 eqn : Hb.
      -- reflexivity.
      -- discriminate H.
    + unfold "||". destruct b1 eqn : Hb.
      -- reflexivity.
      -- rewrite H. reflexivity.
Qed.

Theorem eqb_neq : forall x y : nat,
  x =? y = false <-> x <> y.
Proof.
  intros. split.
  - intros. unfold "<>". intros. rewrite H0 in H.
    rewrite eqb_refl in H. discriminate H.
  - intros. apply not_true_iff_false.
    unfold "<>". intros. apply eqb_true in H0. rewrite H0 in H.
    unfold "<>" in H. 
    assert (y = y). {reflexivity. }
    apply H in H1. destruct H1.
Qed.

Fixpoint eqb_list {A : Type} (eqb : A -> A -> bool)
                  (l1 l2 : list A) : bool :=
  match l1, l2 with
  | [], [] => true
  | [], _ => false
  | _, [] => false
  | h1 :: t1, h2 :: t2 => (eqb h1 h2) && eqb_list eqb t1 t2
  end.

Theorem eqb_list_true_iff :
  forall A (eqb : A -> A -> bool),
    (forall a1 a2, eqb a1 a2 = true <-> a1 = a2) ->
    forall l1 l2, eqb_list eqb l1 l2 = true <-> l1 = l2.
Proof.
  intros. split.
  - intros. generalize dependent l2. induction l1.
    + intros. induction l2.
      -- intros. reflexivity.
      -- intros. simpl in H0. discriminate H0.
    + intros. induction l2.
      -- intros. simpl in H0. discriminate H0.
      -- intros. simpl in H0. apply andb_true_iff in H0. destruct H0. apply H in H0. apply IHl1 in H1. rewrite H1. rewrite H0. reflexivity.
  - intros. rewrite H0. generalize dependent l2. induction l1.
    + intros. induction l2.
      -- reflexivity.
      -- intros. rewrite <- H0. reflexivity.  
    + intros. induction l2.
      -- intros. reflexivity.
      -- intros. simpl. apply andb_true_iff. split.
        ++ apply H. reflexivity.
        ++ apply IHl1. injection H0. intros. apply H1.
Qed.     

Fixpoint forallb {X : Type} (test : X -> bool) (l : list X) : bool :=
  match l with
  | [] => true
  | h :: t => match (test h) with
              | false => false
              | true => forallb test t
              end
  end.

Lemma forallb_true_iff_lemma : forall X test (l : list X) (x : X),
  forallb test (x :: l) = true -> test x = true.
Proof.
  intros. destruct (test x) eqn : Hx.
  - reflexivity.
  - unfold forallb in H. rewrite Hx in H. discriminate H.
Qed.

Lemma forallb_true_iff_lemma2 : forall X test (l : list X) (x : X),
  forallb test (x :: l) = true -> forallb test l = true.
Proof.
  intros. destruct (forallb test l) eqn : Hl.
  - reflexivity.
  - destruct l eqn : Hll.
    + simpl in Hl. discriminate Hl.
    + destruct (test x) in H.
      -- rewrite <- Hll in H. rewrite <- Hll in Hl. apply not_true_iff_false in Hl. unfold not in Hl. rewrite <- H in Hl. apply forallb_true_iff_lemma in H. simpl in Hl. rewrite H in Hl.
      apply ex_falso_quodlibet. apply Hl. reflexivity.
      -- rewrite <- Hll in H. rewrite <- Hll in Hl. 
      apply not_true_iff_false in Hl. unfold not in Hl. simpl in H.
      destruct (test x) in H.
        ++ apply Hl in H. destruct H.
        ++ destruct H. reflexivity.      
Qed.  

Lemma forallb_true_iff_lemma3 : forall X test (l : list X) (x : X),
  forallb test l = true /\ test x = true -> forallb test (x :: l) = true.
Proof.
  intros. destruct H. unfold forallb. rewrite H0. apply H.
Qed. 

Theorem forallb_true_iff : forall X test (l : list X) (x : X),
  forallb test l = true <-> All (fun x => test x = true) l.
Proof.
  intros. split.
  - intros. induction l.
    + simpl. apply I.
    + simpl. split.
      -- apply forallb_true_iff_lemma in H. apply H.
      -- apply IHl. apply forallb_true_iff_lemma2 in H. apply H.
  - intros. induction l.
    + simpl. reflexivity.
    + destruct H. apply IHl in H0. apply forallb_true_iff_lemma3.
    split. apply H0. apply H.
Qed.

Axiom functional_extensionality : forall {X Y: Type}
                                    {f g : X -> Y},
  (forall (x : X), f x = g x) -> f = g.
  
Fixpoint rev_append {X} (l1 l2 : list X) : list X :=
  match l1 with
  | [] => l2
  | x :: l1' => rev_append l1' (x :: l2)
  end.

Definition tr_rev {X} (l : list X) : list X :=
  rev_append l [].

Lemma tr_rev_correct_lemma : forall (X : Type) (l1 l2 : list X),
  rev_append l1 l2 = rev_append l1 [ ] ++ l2.
Proof.
  intros. generalize dependent l2. induction l1.
  - reflexivity.
  - induction l2.
    + simpl. rewrite app_nil_r. reflexivity. 
    + simpl. simpl in IHl2. rewrite IHl1. 
      replace (rev_append l1 [x]) with (rev_append l1 [] ++ [x]).
      rewrite <- app_assoc. reflexivity.
      rewrite <- IHl1. reflexivity.
Qed.

Lemma tr_rev_correct_lemma2 : forall (X : Type) (l : list X) (x : X), rev_append (x :: l) [ ] = rev_append l [ ] ++ [x].
Proof.
  intros. simpl. apply tr_rev_correct_lemma.
Qed. 

Theorem tr_rev_correct : forall X, @tr_rev X = @rev X.
Proof.
  intros. apply functional_extensionality.
  intros. induction x.
  - reflexivity.
  - simpl. rewrite <- IHx. unfold tr_rev. apply tr_rev_correct_lemma2.
Qed.

Definition excluded_middle := forall P : Prop,
  P \/ ~ P.

Theorem restricted_excluded_middle : forall P b,
  (P <-> b = true) -> P \/ ~ P.
Proof.
  intros. destruct b eqn : Hb.
  - left. apply H. reflexivity.
  - right. unfold not. intros. apply H in H0. discriminate H0.   
Qed.

Theorem restricted_excluded_middle_eq : forall (n m : nat),
  n = m \/ n <> m.
Proof.
  intros n m.
  apply (restricted_excluded_middle (n = m) (n =? m)).
  symmetry.
  apply eqb_eq.
Qed.

Theorem de_morgan_1 : forall (P Q : Prop),
    ~ P /\ ~ Q -> ~ (P \/ Q).
Proof.
  intros. destruct H. unfold not. intros. unfold not in H0. unfold not in H. destruct H1.
  - apply H in H1. destruct H1.
  - apply H0 in H1. destruct H1.      
Qed.       

Theorem de_morgan_2 : forall (P Q : Prop),
     (P \/ Q) -> ~ (~ P /\ ~ Q).
Proof.
  intros. destruct H.
  - unfold not. intros. destruct H0. apply H0 in H. destruct H.
  - unfold not. intros. destruct H0. apply H1 in H. destruct H.    
Qed.

Theorem de_morgan_3 : forall (P Q : Prop),
    ~ P /\ ~ Q <-> ~ (P \/ Q).
Proof.
  intros. split. apply de_morgan_1. apply de_morgan_not_or.
Qed. 

Theorem de_morgan_4_classical : forall (P Q : Prop),
     ~ (~ P /\ Q) -> (P \/ ~ Q). 
Proof.
Admitted.

Theorem excluded_middle_irrefutable_classical : forall (P : Prop),
  ~ ~ (P \/ ~ P).
Proof.
  intros. apply double_neg. apply de_morgan_4_classical. unfold not. intros. destruct H. apply H in H0. destruct H0.
Qed.

Theorem excluded_middle_irrefutable : forall (P : Prop),
  ~ ~ (P \/ ~ P).
Proof.
  unfold not. intros. apply H. right. intros. apply H. left. apply H0.  
Qed.

Theorem not_exists_dist :
  excluded_middle ->
  forall (X : Type) (P : X -> Prop),
    ~ (exists x, ~ P x) -> (forall x, P x).
Proof.
  intros. unfold excluded_middle in H. specialize H with (P := P x).
  destruct H.
  - apply H.
  - unfold not in H. unfold not in H0. apply ex_falso_quodlibet.
    apply H0. exists x. intros. apply H in H1. destruct H1.
Qed.     


  

    


      
      



