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
  - (* true branch: X > 2 holds, so Y := 1 establishes Y = 1 *)
    eapply hoare_consequence_pre.
    + apply hoare_asgn.
    + assertion_auto''.
  - (* false branch: precondition X > 2 /\ ~(X > 2) is contradictory *)
    apply hoare_pre_false.
    intros st [H1 H2]. simpl in H2.
    destruct (st X <=? 2) eqn:Heq.
    + exact (axone X 2 st (conj H1 Heq)).
    + apply H2. rewrite Heq. reflexivity.
Qed.

(*1pt. *)
Example seven :
  {{ X >= 0 }}
  while X > 0 do X := X - 1 end
  {{ X = 0 }}.
Proof.
  (* Invariant: X >= 0 (trivially true for nat; maintained since X-1 >= 0 in nat) *)
  eapply hoare_consequence_post.
  - apply hoare_while.
    eapply hoare_consequence_pre.
    + apply hoare_asgn.
    + assertion_auto''.
  - (* Postcondition: X >= 0 /\ ~(X > 0) implies X = 0.
       BGt X 0 evaluates to negb (X <=? 0), so ~(BGt X 0 = true)
       means negb (X <=? 0) is false, i.e. X <=? 0 = true, i.e. X = 0. *)
    unfold "->>". intros st [H1 H2]. simpl in H2.
    destruct (st X <=? 0) eqn:Heq.
    + apply leb_le in Heq. lia.
    + exfalso. apply H2. rewrite Heq. reflexivity.
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
  (* Loop invariant: Y = X * X.
     Each iteration increments X by 1 and adds (2*X - 1) to Y,
     preserving Y = X^2 since (k+1)^2 = k^2 + (2(k+1) - 1). *)
  eapply hoare_seq with (Q := {{ X = 0 }}).
  eapply hoare_seq with (Q := {{ Y = X * X }}).
  - eapply hoare_consequence_post.
    + apply hoare_while.
      (* body: X := X+1 ; Y := Y + (2*X - 1), invariant Y = X*X *)
      eapply hoare_seq.
      * apply hoare_asgn.
      * eapply hoare_consequence_pre.
        -- apply hoare_asgn.
        -- (* Y = X*X /\ cond ->> (Y+(2*X-1) = X*X)[X |-> X+1]
               i.e. Y + (2*(X+1)-1) = (X+1)^2, which follows from Y = X^2 *)
           unfold "->>", assertion_sub, t_update, bassertion.
           intros st [H _]. simpl in *. nlinarith.
    + (* postcondition: Y = X*X /\ X = Z  =>  Y = Z*Z *)
      unfold "->>". intros st [H1 H2]. simpl in H2.
      destruct (st X =? st Z) eqn:Heq.
      * apply eqb_eq in Heq. lia.
      * exfalso. apply H2. rewrite Heq. reflexivity.
  - (* {{ X = 0 }} Y := 0 {{ Y = X * X }}
       WP: (Y = X*X)[Y|->0] = (0 = X*X), and X = 0 implies 0 = 0*0 *)
    eapply hoare_consequence_pre.
    + apply hoare_asgn.
    + assertion_auto''.
  - (* {{ True }} X := 0 {{ X = 0 }}
       WP: (X=0)[X|->0] = (0=0), trivially true *)
    eapply hoare_consequence_pre.
    + apply hoare_asgn.
    + assertion_auto''.
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
  (* Loop invariant: Y = X * (X + 1).
     Each iteration increments X by 1 and adds 2*(X+1) to Y,
     preserving Y = X*(X+1) since (k+1)*(k+2) = k*(k+1) + 2*(k+1). *)
  eapply hoare_seq with (Q := {{ X = 1 }}).
  eapply hoare_seq with (Q := {{ Y = X * (X + 1) }}).
  - eapply hoare_consequence_post.
    + apply hoare_while.
      (* body: X := X+1 ; Y := Y + 2*X, invariant Y = X*(X+1) *)
      eapply hoare_seq.
      * apply hoare_asgn.
      * eapply hoare_consequence_pre.
        -- apply hoare_asgn.
        -- (* Y = X*(X+1) /\ cond ->> (Y+2*X = X*(X+1))[X |-> X+1]
               i.e. Y + 2*(X+1) = (X+1)*(X+2), follows from Y = X*(X+1) *)
           unfold "->>", assertion_sub, t_update, bassertion.
           intros st [H _]. simpl in *. nlinarith.
    + (* postcondition: Y = X*(X+1) /\ X = Z  =>  Y = Z*(Z+1) *)
      unfold "->>". intros st [H1 H2]. simpl in H2.
      destruct (st X =? st Z) eqn:Heq.
      * apply eqb_eq in Heq. lia.
      * exfalso. apply H2. rewrite Heq. reflexivity.
  - (* {{ X = 1 }} Y := X*(X+1) {{ Y = X*(X+1) }}
       WP: (Y=X*(X+1))[Y|->X*(X+1)] = X*(X+1)=X*(X+1), trivially true *)
    eapply hoare_consequence_pre.
    + apply hoare_asgn.
    + assertion_auto''.
  - (* {{ Z > 0 }} X := 1 {{ X = 1 }}
       WP: (X=1)[X|->1] = (1=1), trivially true *)
    eapply hoare_consequence_pre.
    + apply hoare_asgn.
    + assertion_auto''.
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
  (* Loop invariant: Y + X = X * X  (equivalently, Y = X*(X-1) without nat subtraction).
     After k iterations starting from X=1, Y=0: X=k+1, Y=k*(k+1),
     so Y + X = k*(k+1) + (k+1) = (k+1)^2 = X*X. Loop exits when X-1 = Z,
     i.e. X = Z+1, at which point Y = Z*(Z+1). *)
  eapply hoare_seq with (Q := {{ X = 1 }}).
  eapply hoare_seq with (Q := {{ Y + X = X * X }}).
  - eapply hoare_consequence_post.
    + apply hoare_while.
      (* body: Y := Y + 2*X ; X := X+1, invariant Y + X = X*X *)
      eapply hoare_seq.
      * apply hoare_asgn.
      * eapply hoare_consequence_pre.
        -- apply hoare_asgn.
        -- (* Y+X = X*X /\ cond ->> ((Y+(X+1) = (X+1)*(X+1))[Y |-> Y+2*X])
               i.e. Y + 3*X + 1 = (X+1)^2, which follows from Y+X = X*X *)
           unfold "->>", assertion_sub, t_update, bassertion.
           intros st [H _]. simpl in *. nlinarith.
    + (* postcondition: Y+X = X*X /\ (X-1) = Z  =>  Y = Z*(Z+1).
         Case X=0: Z=0, Y=0, goal trivial. Case X=S n: n=Z, nlinarith. *)
      unfold "->>". intros st [H1 H2]. simpl in H2.
      destruct (st X - 1 =? st Z) eqn:Heq.
      * apply eqb_eq in Heq.
        destruct (st X) as [| n].
        -- simpl in Heq. lia.
        -- simpl in Heq. nlinarith [H1, Heq].
      * exfalso. apply H2. rewrite Heq. reflexivity.
  - (* {{ X = 1 }} Y := 0 {{ Y + X = X * X }}
       WP: (Y+X=X*X)[Y|->0] = (X=X*X), and X=1 implies 1=1*1 *)
    eapply hoare_consequence_pre.
    + apply hoare_asgn.
    + assertion_auto''.
  - (* {{ Z > 0 }} X := 1 {{ X = 1 }}
       WP: (X=1)[X|->1] = (1=1), trivially true *)
    eapply hoare_consequence_pre.
    + apply hoare_asgn.
    + assertion_auto''.
Qed.