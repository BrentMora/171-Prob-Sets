Set Warnings "-notation-overridden".
From LF Require Import Maps.
From LF Require Export Imp.
From Stdlib Require Import Bool.
From Stdlib Require Import Arith.
From Stdlib Require Import EqNat.
From Stdlib Require Import PeanoNat. Import Nat.
From Stdlib Require Import Lia.

Definition Assertion := state -> Prop.

Module ExAssertions.
Definition assertion1 : Assertion := fun st => st X <= st Y.
Definition assertion2 : Assertion :=
  fun st => st X = 3 \/ st X <= st Y.
Definition assertion3 : Assertion :=
  fun st => st Z * st Z <= st X /\
            ~ (((S (st Z)) * (S (st Z))) <= st X).
Definition assertion4 : Assertion :=
  fun st => st Z = max (st X) (st Y).
(* FILL IN HERE *)
End ExAssertions.

Definition Aexp : Type := state -> nat.

Definition assert_of_Prop (P : Prop) : Assertion := fun _ => P.
Definition Aexp_of_nat (n : nat) : Aexp := fun _ => n.

Definition Aexp_of_aexp (a : aexp) : Aexp := fun st => aeval st a.

Coercion assert_of_Prop : Sortclass >-> Assertion.
Coercion Aexp_of_nat : nat >-> Aexp.
Coercion Aexp_of_aexp : aexp >-> Aexp.

Arguments assert_of_Prop /.
Arguments Aexp_of_nat /.
Arguments Aexp_of_aexp /.

Declare Custom Entry assn. (* The grammar for Hoare logic Assertions *)
Declare Scope assertion_scope.
Bind Scope assertion_scope with Assertion.
Bind Scope assertion_scope with Aexp.
Delimit Scope assertion_scope with assertion.

Notation "# f x .. y" := (fun st => (.. (f ((x:Aexp) st)) .. ((y:Aexp) st)))
                  (in custom assn at level 2,
                  f constr at level 0, x custom assn at level 1,
                  y custom assn at level 1) : assertion_scope.

Notation "P -> Q" := (fun st => (P:Assertion) st -> (Q:Assertion) st) (in custom assn at level 99, right associativity) : assertion_scope.
Notation "P <-> Q" := (fun st => (P:Assertion) st <-> (Q:Assertion) st) (in custom assn at level 95) : assertion_scope.

Notation "P \/ Q" := (fun st => (P:Assertion) st \/ (Q:Assertion) st) (in custom assn at level 85, right associativity) : assertion_scope.
Notation "P /\ Q" := (fun st => (P:Assertion) st /\ (Q:Assertion) st) (in custom assn at level 80, right associativity) : assertion_scope.
Notation "~ P" := (fun st => ~ ((P:Assertion) st)) (in custom assn at level 75, right associativity) : assertion_scope.
Notation "a = b" := (fun st => (a:Aexp) st = (b:Aexp) st) (in custom assn at level 70) : assertion_scope.
Notation "a <> b" := (fun st => (a:Aexp) <> (b:Aexp) st) (in custom assn at level 70) : assertion_scope.
Notation "a <= b" := (fun st => (a:Aexp) st <= (b:Aexp) st) (in custom assn at level 70) : assertion_scope.
Notation "a < b" := (fun st => (a:Aexp) st < (b:Aexp) st) (in custom assn at level 70) : assertion_scope.
Notation "a >= b" := (fun st => (a:Aexp) st >= (b:Aexp) st) (in custom assn at level 70) : assertion_scope.
Notation "a > b" := (fun st => (a:Aexp) st > (b:Aexp) st) (in custom assn at level 70) : assertion_scope.
Notation "'True'" := True.
Notation "'True'" := (fun st => True) (in custom assn at level 0) : assertion_scope.
Notation "'False'" := False.
Notation "'False'" := (fun st => False) (in custom assn at level 0) : assertion_scope.

Notation "a + b" := (fun st => (a:Aexp) st + (b:Aexp) st) (in custom assn at level 50, left associativity) : assertion_scope.
Notation "a - b" := (fun st => (a:Aexp) st - (b:Aexp) st) (in custom assn at level 50, left associativity) : assertion_scope.
Notation "a * b" := (fun st => (a:Aexp) st * (b:Aexp) st) (in custom assn at level 40, left associativity) : assertion_scope.

Notation "( x )" := x (in custom assn at level 0, x at level 99) : assertion_scope.

Notation "$ f" := f (in custom assn at level 0, f constr at level 0) : assertion_scope.
Notation "x" := (x%assertion) (in custom assn at level 0, x constr at level 0) : assertion_scope.

Declare Scope hoare_spec_scope.
Open Scope hoare_spec_scope.

Notation "{{ e }}" := e (at level 2, e custom assn at level 99) : assertion_scope.
Open Scope assertion_scope.

Module  ExamplePrettyAssertions.
Definition assertion1 : Assertion := {{ X = 3 }}.
Definition assertion2 : Assertion := {{ True }}.
Definition assertion3 : Assertion := {{ False }}.
Definition assertion4 : Assertion := {{ True \/ False }}.
Definition assertion5 : Assertion := {{ X <= Y }}.
Definition assertion6 : Assertion := {{ X = 3 \/ X <= Y }}.
Definition assertion7 : Assertion := {{ Z = (#max X Y) }}.
Definition assertion8 : Assertion := {{ Z * Z <= X
                                        /\  ~ (((#S Z) * (#S Z)) <= X) }}.
Definition assertion9 : Assertion := {{#add X Y > #max Y X }}.
End ExamplePrettyAssertions.

Definition assert_implies (P Q : Assertion) : Prop :=
  forall st, P st -> Q st.

Notation "P ->> Q" := (assert_implies P Q)
                        (at level 80) : hoare_spec_scope.

Notation "P <<->> Q" := (P ->> Q /\ Q ->> P)
                          (at level 80) : hoare_spec_scope.

Definition valid_hoare_triple
           (P : Assertion) (c : com) (Q : Assertion) : Prop :=
  forall st st',
     st =[ c ]=> st' ->
     P st  ->
     Q st'.

Notation "{{ P }} c {{ Q }}" :=
  (valid_hoare_triple P c Q)
    (at level 2, P custom assn at level 99, c custom com at level 99,
     Q custom assn at level 99)
    : hoare_spec_scope.

Theorem hoare_post_true : forall (P Q : Assertion) c,
  (forall st, Q st) ->
  {{P}} c {{Q}}.
Proof.
  intros. unfold valid_hoare_triple. intros.
  specialize H with (st := st'). apply H.
Qed.

Theorem hoare_pre_false : forall (P Q : Assertion) c,
  (forall st, ~ (P st)) -> {{P}} c {{Q}}.
Proof.
  intros. unfold valid_hoare_triple. intros.
  specialize H with (st := st). unfold not in H.
  apply H in H1. destruct H1.
Qed.

Theorem hoare_skip : forall P, {{P}} skip {{P}}.
Proof.
  intros. unfold valid_hoare_triple. intros.
  inversion H. subst. apply H0.
Qed.

Theorem hoare_seq : forall P Q R c1 c2,
     {{Q}} c2 {{R}} ->
     {{P}} c1 {{Q}} ->
     {{P}} c1; c2 {{R}}.
Proof.
  intros. 
  unfold valid_hoare_triple in H. 
  unfold valid_hoare_triple in H0.
  unfold valid_hoare_triple.
  intros.
  inversion H1.
  apply H0 in H5.
  - apply H in H8.
    + apply H8.
    + apply H5.
  - apply H2.
Qed.

Definition assertion_sub X (a:aexp) (P:Assertion) : Assertion :=
  fun (st : state) =>
    (P%_assertion) (X !-> ((a:Aexp) st); st).

Notation "P [ X |-> a ]" := (assertion_sub X a P)
                              (in custom assn at level 10, left associativity,
                               P custom assn, X global, a custom com)
                          : assertion_scope.

Example equivalent_assertion1 :
  {{ (X <= 5) [X |-> 3] }} <<->> {{ 3 <= 5 }}.
Proof.
  unfold valid_hoare_triple. split.
  - unfold assert_implies. intros. simpl in H. unfold assertion_sub in H. apply H.
  - unfold assert_implies. intros. simpl in H. unfold assertion_sub. simpl. apply H.
Qed.  

Example equivalent_assertion2 :
  {{ (X <= 5) [X |-> X + 1] }} <<->> {{ (X + 1) <= 5 }}.
Proof.
  split.
  - unfold assert_implies. intros. unfold assertion_sub in H. simpl in H. apply H.
  - unfold assert_implies. intros. apply H.
Qed.

Theorem hoare_asgn : forall Q X (a:aexp),
  {{Q [X |-> a]}} X := a {{Q}}.
Proof.
  intros. unfold valid_hoare_triple. intros.
  unfold assertion_sub in H0. simpl in H0. inversion H.
  subst. apply H0.
Qed.

Example assertion_sub_example :
  {{(X < 5) [X |-> X + 1]}}
    X := X + 1
  {{X < 5}}.
Proof.
  apply hoare_asgn.
Qed.

Example hoare_asgn_examples1 :
  exists P, {{ P }} X := 2 * X {{ X <= 10 }}.
Proof.
  exists ({{(X <= 10) [X |-> 2 * X]}}).
  apply hoare_asgn.
Qed.

Example hoare_asgn_examples2 :
  exists P,
    {{ P }}
      X := 3
    {{ 0 <= X /\ X <= 5 }}.
Proof.
  exists ({{(0 <= X /\ X <= 5)[X |-> 3]}}).
  apply hoare_asgn.
Qed.

Theorem hoare_consequence_pre : forall (P P' Q : Assertion) c,
  {{P'}} c {{Q}} ->
  P ->> P' ->
  {{P}} c {{Q}}.
Proof.
  intros. unfold assert_implies in H0.
  unfold valid_hoare_triple in *.
  intros.
  apply H in H1.
  - apply H1.
  - apply H0 in H2. apply H2.
Qed.

Theorem hoare_consequence_post : forall (P Q Q' : Assertion) c,
  {{P}} c {{Q'}} ->
  Q' ->> Q ->
  {{P}} c {{Q}}.
Proof.
  intros. unfold valid_hoare_triple in *.
  unfold assert_implies in *.
  intros.
  apply H in H1.
  - specialize H0 with (st := st'). apply H0. apply H1.
  - apply H2.
Qed.

Example hoare_asgn_example1 :
  {{True}} X := 1 {{X = 1}}.
Proof.
  eapply hoare_consequence_pre.
  - apply hoare_asgn.
  - unfold "->>". intros. simpl. unfold assertion_sub.
    simpl. unfold t_update. reflexivity.
Qed.

Example assertion_sub_example2 :
  {{X < 4}}
    X := X + 1
  {{X < 5}}.
Proof.
  eapply hoare_consequence_pre.
  - apply hoare_asgn.
  - unfold "->>". intros. simpl. unfold assertion_sub.
    simpl. unfold t_update. simpl. simpl in H. lia.
Qed.

Theorem hoare_consequence : forall (P P' Q Q' : Assertion) c,
  {{P'}} c {{Q'}} ->
  P ->> P' ->
  Q' ->> Q ->
  {{P}} c {{Q}}.
Proof.
  intros P P' Q Q' c Htriple Hpre Hpost.
  apply hoare_consequence_pre with (P' := P').
  - apply hoare_consequence_post with (Q' := Q'); assumption.
  - assumption.
Qed.

Ltac assertion_auto :=
  try auto;  (* as in example 1, above *)
  try (unfold "->>", assertion_sub, t_update;
       intros; simpl in *; lia). (* as in example 2 *)

Example assertion_sub_example2'' :
  {{X < 4}}
    X := X + 1
  {{X < 5}}.
Proof.
  eapply hoare_consequence_pre.
  - apply hoare_asgn.
  - assertion_auto.
Qed.

Example hoare_asgn_example1''':
  {{True}} X := 1 {{X = 1}}.
Proof.
  eapply hoare_consequence_pre.
  - apply hoare_asgn.
  - assertion_auto.
Qed.

Example assertion_sub_ex1' :
  {{ X <= 5 }}
    X := 2 * X
  {{ X <= 10 }}.
Proof.
  eapply hoare_consequence_pre.
  - apply hoare_asgn.
  - assertion_auto.
Qed.

Example assertion_sub_ex2' :
  {{ 0 <= 3 /\ 3 <= 5 }}
    X := 3
  {{ 0 <= X /\ X <= 5 }}.
Proof.
  eapply hoare_consequence_pre.
  - apply hoare_asgn.
  - assertion_auto.
Qed.

Example hoare_asgn_example3 : forall (a:aexp) (n:nat),
  {{a = n}}
    X := a;
    skip
  {{X = n}}.
Proof.
  intros. eapply hoare_seq.
  - apply hoare_skip.
  - eapply hoare_consequence_pre.
    + apply hoare_asgn.
    + unfold "->>". intros. simpl. unfold assertion_sub.
      simpl. unfold t_update. simpl. simpl in H. apply H.
Qed.

Example hoare_asgn_example4 :
  {{ True }}
    X := 1;
    Y := 2
  {{ X = 1 /\ Y = 2 }}.
Proof.
  eapply hoare_seq with (Q := {{ X = 1 }}).
  - eapply hoare_consequence_pre.
    + apply hoare_asgn.
    + unfold "->>". intros. simpl. unfold assertion_sub.
      simpl. simpl in H. split.
      -- unfold t_update. simpl. apply H.
      -- unfold t_update. simpl. reflexivity.
  - eapply hoare_consequence_pre.
    + apply hoare_asgn.
    + unfold "->>". intros. simpl. unfold assertion_sub.
      simpl. unfold t_update. simpl. reflexivity.
Qed.

Definition swap_program : com :=
  <{  Z := X;
      X := Y;
      Y := Z
  }>.

Theorem swap_exercise :
  {{X <= Y}}
    swap_program
  {{Y <= X}}.
Proof.
  unfold swap_program.
  eapply hoare_seq with (Q := {{Z <= Y}}).
  - eapply hoare_seq.
    + apply hoare_asgn.
    + simpl. unfold assertion_sub. simpl. unfold t_update.
      simpl. eapply hoare_consequence_pre.
        --  apply hoare_asgn.
        --  unfold "->>". intros. simpl. unfold assertion_sub.
            simpl. unfold t_update. simpl. apply H.
  - eapply hoare_consequence_pre.
    + apply hoare_asgn.
    + unfold "->>". intros. simpl. unfold assertion_sub.
      simpl. unfold t_update. simpl. apply H.
Qed.  

Definition bassertion b : Assertion :=
  fun st => (beval st b = true).
Coercion bassertion : bexp >-> Assertion.
Arguments bassertion /.

Lemma bexp_eval_false : forall b st,
  beval st b = false -> ~ ((bassertion b) st).
Proof.
  intros. unfold not. simpl. intros. rewrite H0 in H.
  discriminate H.
Qed.

Theorem hoare_if : forall P Q (b:bexp) c1 c2,
  {{ P /\ b }} c1 {{Q}} ->
  {{ P /\ ~ b}} c2 {{Q}} ->
  {{P}} if b then c1 else c2 end {{Q}}.
Proof.
  intros. unfold valid_hoare_triple. intros.
  inversion H1.
  - unfold valid_hoare_triple in H.
    unfold valid_hoare_triple in H0.
    specialize H with (st := st) (st' := st').
    apply H in H9.
    + apply H9.
    + split. apply H2. simpl. apply H8.
  - unfold valid_hoare_triple in H.
    unfold valid_hoare_triple in H0.
    specialize H0 with (st := st) (st' := st'). 
    apply H0 in H9.
    + apply H9.
    + split. apply H2. simpl. apply bexp_eval_false in H8.
      apply H8.
Qed.

Example if_example :
  {{True}}
    if (X = 0)
      then Y := 2
      else Y := X + 1
    end
  {{X <= Y}}.
Proof.
  apply hoare_if.
  - eapply hoare_consequence_pre.
    + apply hoare_asgn.
    + unfold "->>". intros. unfold assertion_sub.
      destruct H. simpl. unfold t_update.
      simpl. simpl in H0. apply eqb_eq in H0.
      rewrite H0. lia.
  - eapply hoare_consequence_pre.
    + apply hoare_asgn.
    + unfold "->>". intros. unfold assertion_sub.
      destruct H. simpl in H0. unfold t_update.
      simpl. lia.
Qed.

Ltac assertion_auto' :=
  unfold "->>", assertion_sub, t_update, bassertion;
  intros; simpl in *;
  try rewrite -> eqb_eq in *; (* for equalities *)
  auto; try lia.

Example if_example'' :
  {{True}}
    if X = 0
      then Y := 2
      else Y := X + 1
    end
  {{X <= Y}}.
Proof.
  apply hoare_if.
  - eapply hoare_consequence_pre.
    + apply hoare_asgn.
    + assertion_auto'.
  - eapply hoare_consequence_pre.
    + apply hoare_asgn.
    + assertion_auto'.
Qed.

Example if_example''' :
  {{True}}
    if X = 0
      then Y := 2
      else Y := X + 1
    end
  {{X <= Y}}.
Proof.
  apply hoare_if; eapply hoare_consequence_pre;
    try apply hoare_asgn; try assertion_auto'.
Qed.

Ltac assertion_auto'' :=
  unfold "->>", assertion_sub, t_update, bassertion;
  intros; simpl in *;
  try rewrite -> eqb_eq in *;
  try rewrite -> leb_le in *;  (* for inequalities *)
  auto; try lia.

Theorem if_minus_plus :
  {{True}}
    if (X <= Y)
      then Z := Y - X
      else Y := X + Z
    end
  {{Y = X + Z}}.
Proof.
  apply hoare_if.
  - eapply hoare_consequence_pre.
    + apply hoare_asgn.
    + assertion_auto''.
  - eapply hoare_consequence_pre.
    + apply hoare_asgn.
    + assertion_auto''.
Qed.

Module If1.

Inductive com : Type :=
  | CSkip : com
  | CAsgn : string -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com
  | CIf1 : bexp -> com -> com.

Notation "'if1' x 'then' y 'end'" :=
         (CIf1 x y)
             (in custom com at level 0, x custom com at level 99).
Notation "'skip'"  := CSkip
  (in custom com at level 0) : com_scope.
Notation "x := y"  := (CAsgn x y)
  (in custom com at level 0, x constr at level 0, y at level 85, no associativity,
    format "x  :=  y") : com_scope.
Notation "x ; y" := (CSeq x y)
  (in custom com at level 90,
    right associativity,
    format "'[v' x ; '/' y ']'") : com_scope.
Notation "'if' x 'then' y 'else' z 'end'" := (CIf x y z)
  (in custom com at level 89, x at level 99, y at level 99, z at level 99,
    format "'[v' 'if'  x  'then' '/  ' y '/' 'else' '/  ' z '/' 'end' ']'") : com_scope.
Notation "'while' x 'do' y 'end'" := (CWhile x y)
  (in custom com at level 89, x at level 99, y at level 99,
    format "'[v' 'while'  x  'do' '/  ' y '/' 'end' ']'") : com_scope.

Reserved Notation
         "st0 '=[' c ']=>' st1 '/' s"
         (at level 40, c custom com at level 99,
          st0 constr, st1 constr at next level,
          format "'[hv' st0  =[ '/  ' '[' c ']' '/' ]=>  st1 / s ']'").

Inductive ceval : com -> state -> state -> Prop :=
  | E_Skip : forall st,
      st =[ skip ]=> st
  | E_Asgn  : forall st a1 n x,
      aeval st a1 = n ->
      st =[ x := a1 ]=> (x !-> n ; st)
  | E_Seq : forall c1 c2 st st' st'',
      st  =[ c1 ]=> st'  ->
      st' =[ c2 ]=> st'' ->
      st  =[ c1 ; c2 ]=> st''
  | E_IfTrue : forall st st' b c1 c2,
      beval st b = true ->
      st =[ c1 ]=> st' ->
      st =[ if b then c1 else c2 end ]=> st'
  | E_IfFalse : forall st st' b c1 c2,
      beval st b = false ->
      st =[ c2 ]=> st' ->
      st =[ if b then c1 else c2 end ]=> st'
  | E_WhileFalse : forall b st c,
      beval st b = false ->
      st =[ while b do c end ]=> st
  | E_WhileTrue : forall st st' st'' b c,
      beval st b = true ->
      st  =[ c ]=> st' ->
      st' =[ while b do c end ]=> st'' ->
      st  =[ while b do c end ]=> st''
  | E_If1True : forall st st' b c1,
      beval st b = true ->
      st =[ c1 ]=> st' ->
      st =[ if1 b then c1 end ]=> st'
  | E_If1False : forall st b c1,
      beval st b = false ->
      st =[ if1 b then c1 end ]=> st

where "st '=[' c ']=>' st'" := (ceval c st st').

Hint Constructors ceval : core.

Example if1true_test :
  empty_st =[ if1 X = 0 then X := 1 end ]=> (X !-> 1).
Proof. eauto. Qed.

Example if1false_test :
  (X !-> 2) =[ if1 X = 0 then X := 1 end ]=> (X !-> 2).
Proof. eauto. Qed.

Definition valid_hoare_triple
           (P : Assertion) (c : com) (Q : Assertion) : Prop :=
  forall st st',
       st =[ c ]=> st' ->
       P st  ->
       Q st'.

Hint Unfold valid_hoare_triple : core.

Notation "{{ P }} c {{ Q }}" :=
  (valid_hoare_triple P c Q)
    (at level 2, P custom assn at level 99, c custom com at level 99, Q custom assn at level 99)
    : hoare_spec_scope.

Theorem hoare_consequence_pre : forall (P P' Q : Assertion) c,
  {{P'}} c {{Q}} ->
  P ->> P' ->
  {{P}} c {{Q}}.
Proof.
  eauto.
Qed.

Theorem hoare_asgn : forall Q X a,
  {{Q [X |-> a]}} (X := a) {{Q}}.
Proof.
  intros Q X a st st' Heval HQ.
  inversion Heval; subst.
  auto.
Qed.

Theorem hoare_if1 : forall P Q (b : bexp) c1,
  {{ P /\ b }} c1 {{Q}} ->
  {{ P /\ ~b }} skip {{Q}} ->
  {{P}} if1 b then c1 end {{Q}}.
Proof.
  intros. unfold valid_hoare_triple. intros.
  unfold valid_hoare_triple in H.
  unfold valid_hoare_triple in H0.
  inversion H1.
  - apply H in H8.
    + apply H8.
    + split.
      -- apply H2.
      -- simpl. apply H5.
  - subst. apply H0 with (st := st').
    + apply E_Skip.
    + split.
      -- apply H2.
      -- simpl. apply bexp_eval_false in H7. apply H7.
Qed.

Lemma lemma1: forall b, negb b <> true -> b = true.
Proof.
  intros. destruct b. reflexivity. simpl in H.
  contradiction.
Qed.

Lemma hoare_if1_good :
  {{ X + Y = Z }}
    if1 Y <> 0 then
      X := X + Y
    end
  {{ X = Z }}.
Proof.
  intros. apply hoare_if1.
  - eapply hoare_consequence_pre.
    + apply hoare_asgn.
    + assertion_auto''.
  - unfold valid_hoare_triple.
    intros. destruct H0.
    simpl. simpl in *. inversion H.
    subst. apply lemma1 in H1. apply eqb_eq in H1.
    rewrite H1 in H0. lia.
Qed.
    
End If1.

Theorem hoare_while : forall P (b:bexp) c,
  {{P /\ b}} c {{P}} ->
  {{P}} while b do c end {{P /\ ~ b}}.
Proof.
  intros. unfold valid_hoare_triple in *. intros.
  remember <{while b do c end}> as og eqn : Horig.
  induction H0.
  - inversion Horig.
  - inversion Horig.
  - inversion Horig.
  - inversion Horig.
  - inversion Horig.
  - inversion Horig. subst. split. apply H1. 
    apply bexp_eval_false in H0. apply H0.
  - inversion Horig. subst. eauto.
Qed.

Example while_example :
  {{X <= 3}}
    while (X <= 2) do
      X := X + 1
    end
  {{X = 3}}.
Proof.
  eapply hoare_consequence_post.
  - apply hoare_while. eapply hoare_consequence_pre.
    + apply hoare_asgn.
    + assertion_auto''.
  - assertion_auto''.
Qed.

Example while_example2:
  {{X <= Z /\ Z > 0}}
    while (X <= Z - 1) do
      X := X + 1
    end;
    X := 2 * X
  {{X = 2 * Z}}.
Proof.
  apply hoare_seq with (Q := {{X = Z}}). 
  - eapply hoare_consequence_pre. apply hoare_asgn.
    assertion_auto''.
  - eapply hoare_consequence_post.
    + apply hoare_while. eapply hoare_consequence_pre.
      -- apply hoare_asgn.
      -- assertion_auto''.
    + assertion_auto''.
Qed.       

Theorem always_loop_hoare : forall Q,
  {{True}} while true do skip end {{Q}}.
Proof.
  intros Q.
  eapply hoare_consequence_post.
  - apply hoare_while. apply hoare_post_true. auto.
  - simpl. intros st [Hinv Hguard]. congruence.
Qed.
  