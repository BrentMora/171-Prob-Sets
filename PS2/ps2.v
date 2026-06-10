(*Problem Set 10, total of 10 pts.*)
(*You need to make and import Maps.v / Imp.v / Hoare.v*)

Set Warnings "-notation-overridden".
From LF Require Import Maps.
From LF Require Export Imp.
From LF Require Export Hoare.
From Stdlib Require Import Bool.
From Stdlib Require Import Arith.
From Stdlib Require Import EqNat.
From Stdlib Require Import PeanoNat. Import Nat.
From Stdlib Require Import Lia.

(*1pt. *)
Example one : 
  {{ Y = 3 }}
    X := 3
  {{ Y = X }}.
Proof.
  eapply hoare_consequence_pre.
  - apply hoare_asgn.
  - assertion_auto''.
Qed.

(*1pt. *)
Example two : 
  {{ Y = X + 1 }}
    X := X + 1
  {{ Y = X }}.
Proof.
  eapply hoare_consequence_pre.
  - apply hoare_asgn.
  - assertion_auto''.
Qed.

(*1pt. *)
Example three : 
  {{ Y > 0 }}
  X := Y + 3
  {{ X > 3 }}.
Proof.
  eapply hoare_consequence_pre.
  - apply hoare_asgn.
  - assertion_auto''.
Qed.

(*1pt. *)
Example four : 
  {{ X = 5 }}
  X := X + 1
  {{ X > 0 }}.
Proof.
  eapply hoare_consequence_pre.
  - apply hoare_asgn.
  - assertion_auto''.
Qed.

(*1pt. *)
Example five : 
  {{ X > 2 }}
  X := X + 1;
  X := X + 2
  {{ X > 5 }}.
Proof.
  eapply hoare_seq with (Q := {{ X > 3 }}).
  - eapply hoare_consequence_pre.
    + apply hoare_asgn.
    + assertion_auto''.
  - eapply hoare_consequence_pre.
    + apply hoare_asgn.
    + assertion_auto''.
Qed.

(*1pt. *)
Axiom axone: forall X a (st : state), ((st X > a) /\ (st X <=? a) = true) -> False.

(*You may use Axiom axone. *)
Example six :
  {{ X > 2 }}
  if X > 2 then Y := 1 else Y := 0 end
  {{ Y = 1}}.
Proof.
  apply hoare_if.
  - eapply hoare_consequence_pre.
    + apply hoare_asgn.
    + assertion_auto''.
  - apply hoare_pre_false.
    intros st [H1 H2].
    unfold bassertion in H2. simpl in H2.
    destruct (st X <=? 2) eqn:Heq.
    + exact (axone X 2 st (conj H1 Heq)).
    + apply H2. reflexivity.
Qed.

(*1pt. *)
Example seven :
  {{ X >= 0 }}
  while X > 0 do X := X - 1 end
  {{ X = 0 }}.
Proof.
  eapply hoare_consequence_post.
  - apply hoare_while.
    eapply hoare_consequence_pre.
    + apply hoare_asgn.
    + unfold "->>", assertion_sub, t_update, bassertion.
      intros st [H1 H2]. simpl in *.
      destruct (st X <=? 0) eqn:Heq.
      * apply leb_le in Heq. lia.
      * apply Nat.leb_gt in Heq. lia.
  - unfold "->>". intros st [H1 H2].
    unfold bassertion in H2. simpl in H2.
    destruct (negb (st X <=? 0)) eqn:Heq.
    + exfalso. apply H2. reflexivity.
    + apply negb_false_iff in Heq.
      apply leb_le in Heq.
      unfold Aexp_of_nat. simpl.
      lia.
Qed.

(*1pt. *)
Example eight :
  {{ True }}
  X := 0;
  Y := 0;
  while (~ (X = Z)) do
    X := X + 1;
    Y := Y + ((2 * X)-1)
  end
  {{ Y = Z * Z }}.
Proof.
  eapply hoare_seq with (Q := {{ X = 0 }}).
  eapply hoare_seq with (Q := {{ Y = X * X }}).
  - eapply hoare_consequence_post.
    + apply hoare_while.
      eapply hoare_seq.
      * apply hoare_asgn.
      * eapply hoare_consequence_pre.
        -- apply hoare_asgn.
        -- unfold "->>", assertion_sub, t_update, bassertion.
           intros st [H _]. simpl in *.
           rewrite H.
           destruct (st X); lia.
    + unfold "->>". intros st [H1 H2].
      unfold bassertion in H2. simpl in H2.
      destruct (st X =? st Z) eqn:Heq.
      * apply eqb_eq in Heq.
        simpl. rewrite <- Heq. apply H1.
      * exfalso. apply H2. reflexivity.
  - eapply hoare_consequence_pre.
    + apply hoare_asgn.
    + unfold "->>", assertion_sub, t_update, bassertion.
      intros st H. simpl in *. lia.
  - eapply hoare_consequence_pre.
    + apply hoare_asgn.
    + unfold "->>". intros st H. simpl. reflexivity.
Qed.

(*1pt. *)
Example nine :
  {{ Z > 0 }}
  X := 1;
  Y := X * (X + 1);
  while (~ (X = Z)) do
    X := X + 1;
    Y := Y + (2 * X)
  end
  {{ Y = Z * (Z + 1)}}.
Proof.
  eapply hoare_seq with (Q := {{ X = 1 }}).
  eapply hoare_seq with (Q := {{ Y = X * (X + 1) }}).
  - eapply hoare_consequence_post.
    + apply hoare_while.
      eapply hoare_seq.
      * apply hoare_asgn.
      * eapply hoare_consequence_pre.
        -- apply hoare_asgn.
        -- unfold "->>", assertion_sub, t_update, bassertion.
           intros st [H _]. simpl in *.
           rewrite H.
           destruct (st X); lia.
    + unfold "->>". intros st [H1 H2].
      unfold bassertion in H2. simpl in H2.
      destruct (st X =? st Z) eqn:Heq.
      * apply eqb_eq in Heq.
        simpl. rewrite <- Heq. apply H1.
      * exfalso. apply H2. reflexivity.
  - eapply hoare_consequence_pre.
    + apply hoare_asgn.
    + unfold "->>", assertion_sub, t_update, bassertion.
      intros st H. simpl in *. lia.
  - eapply hoare_consequence_pre.
    + apply hoare_asgn.
    + unfold "->>". intros st H. simpl. reflexivity.
Qed.

(*1pt. *)
Example ten :
  {{ Z > 0 }}
  X := 1;
  Y := 0;
  while (~((X - 1) = Z)) do
    Y := Y + (2 * X);
    X := X + 1
  end
  {{ Y = Z * (Z + 1)}}.
Proof.
  eapply hoare_seq with (Q := {{ X = 1 /\ Z > 0 }}).
  eapply hoare_seq with (Q := {{ Y = (X - 1) * X /\ Z > 0 }}).
  - eapply hoare_consequence_post.
    + apply hoare_while.
      eapply hoare_seq.
      * apply hoare_asgn.
      * eapply hoare_consequence_pre.
        -- apply hoare_asgn.
        -- unfold "->>", assertion_sub, t_update, bassertion.
           intros st [[H HZ] _]. simpl in *.
           destruct (st X) eqn:HX.
           ++ simpl in H. lia.
           ++ simpl in H.
              replace (S n + 1 - 1) with (S n) by lia.
              split. lia. lia.
    + unfold "->>". intros st [[H1 HZ] H2].
      unfold bassertion in H2. simpl in H2.
      unfold Aexp_of_nat, Aexp_of_aexp in *.
      simpl in *.
      destruct (st X - 1 =? st Z) eqn:Heq.
      * apply eqb_eq in Heq.
        destruct (st X) eqn:HX.
        -- lia.
        -- rewrite H1. simpl in Heq. lia.
      * exfalso. apply H2. reflexivity.
  - eapply hoare_consequence_pre.
    + apply hoare_asgn.
    + unfold "->>", assertion_sub, t_update.
      intros st [HX HZ]. simpl in *.
      split.
      * rewrite HX. simpl. lia.
      * apply HZ.
  - eapply hoare_consequence_pre.
    + apply hoare_asgn.
    + unfold "->>", assertion_sub, t_update.
      intros st HZ. simpl in *.
      split.
      * reflexivity.
      * apply HZ.
Qed.