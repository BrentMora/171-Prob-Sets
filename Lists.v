From LF Require Export Induction.

Module NatList.

Inductive natprod : Type :=
  | pair (n1 n2 : nat).

Check (pair 3 5) : natprod.

Definition fst (p : natprod) : nat :=
  match p with
  | pair x y => x
  end.

Definition snd (p : natprod) : nat :=
  match p with
  | pair x y => y
  end.

Notation "( x , y )" := (pair x y).

Definition swap_pair (p : natprod) : natprod :=
  match p with
  | (x,y) => (y,x)
  end.

Theorem surjective_pairing' : forall (n m : nat),
  (n,m) = (fst (n,m), snd (n,m)).
Proof.
  intros. reflexivity. 
Qed.

Theorem surjective_pairing : forall (p : natprod),
  p = (fst p, snd p).
Proof.
  intros. destruct p. simpl. reflexivity.
Qed.

Theorem snd_fst_is_swap : forall (p : natprod),
  (snd p, fst p) = swap_pair p.
Proof.
  intros. destruct p. reflexivity.
Qed.

Theorem fst_swap_is_snd : forall (p : natprod),
  fst (swap_pair p) = snd p.
Proof.
  intros. destruct p. reflexivity.
Qed.

Inductive natlist : Type :=
  | nil
  | cons (n : nat) (l : natlist).

Notation "x :: l" := (cons x l)
                     (at level 60, right associativity).
Notation "[]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

Fixpoint repeat (n count : nat) : natlist :=
  match count with
  | O => []
  | S count' => n :: (repeat n count')
  end.

Fixpoint length (l : natlist) : nat :=
  match l with
  | [] => O
  | h :: t => S (length t)
  end.

Fixpoint app (l1 l2 : natlist) : natlist :=
  match l1 with
  | [] => l2
  | h :: t => h :: (app t l2)
  end.

Notation "x ++ y" := (app x y)
                     (right associativity, at level 60).
Example test_app1: [1;2;3] ++ [4;5] = [1;2;3;4;5].
Proof. reflexivity. Qed.
Example test_app2: nil ++ [4;5] = [4;5].
Proof. reflexivity. Qed.
Example test_app3: [1;2;3] ++ nil = [1;2;3].
Proof. reflexivity. Qed.

Definition hd (default : nat) (l : natlist) : nat :=
  match l with
  | [] => default
  | h :: t => h
  end.

Definition tl (l : natlist) : natlist :=
  match l with
  | [] => []
  | h :: t => t
  end.

Fixpoint nonzeros (l : natlist) : natlist :=
  match l with
  | [] => []
  | h :: t => match h with
              | O => nonzeros t
              | _ => h :: (nonzeros t)
              end
  end.

Example test_nonzeros: nonzeros [0;1;0;2;3;0;0] = [1;2;3].
Proof. reflexivity. Qed.

Fixpoint oddmembers (l : natlist) : natlist :=
  match l with
  | [] => []
  | h :: t => match (odd h) with
              | true => h :: (oddmembers t)
              | false => oddmembers t
              end
  end.

Example test_oddmembers : oddmembers [0;1;0;2;3;0;0] = [1;3].
Proof. reflexivity. Qed.

Definition countoddmembers (l : natlist) : nat :=
  length (oddmembers l).

Example test_countoddmembers1 : countoddmembers [1;0;3;1;4;5] = 4.
Proof. reflexivity. Qed.
Example test_countoddmembers2 : countoddmembers [0;2;4] = 0.
Proof. reflexivity. Qed.
Example test_countoddmembers3 : countoddmembers nil = 0.
Proof. reflexivity. Qed.

Fixpoint alternate (l1 l2 : natlist) : natlist :=
  match l1, l2 with
  | [], [] => []
  | [], _ => l2
  | _, [] => l1
  | h1 :: t1, h2 :: t2 => [h1;h2] ++ (alternate t1 t2)
  end.

Example test_alternate1: alternate [1;2;3] [4;5;6] = [1;4;2;5;3;6].
Proof. reflexivity. Qed.
Example test_alternate2: alternate [1] [4;5;6] = [1;4;5;6].
Proof. reflexivity. Qed.
Example test_alternate3: alternate [1;2;3] [4] = [1;4;2;3].
Proof. reflexivity. Qed.
Example test_alternate4: alternate [] [20;30] = [20;30].
Proof. reflexivity. Qed.

Definition bag := natlist.

Fixpoint count (v : nat) (s : bag) : nat :=
  match s with
  | [] => O
  | h :: t => match (eqb h v) with
              | true => S (count v t)
              | false => (count v t)
              end
  end.

Example test_count1: count 1 [1;2;3;1;4;1] = 3.
Proof. reflexivity. Qed.
Example test_count2: count 6 [1;2;3;1;4;1] = 0.
Proof. reflexivity. Qed.

Definition sum : bag -> bag -> bag := app.

Example test_sum1: count 1 (sum [1;2;3] [1;4;1]) = 3.
Proof. reflexivity. Qed.

Definition add (v : nat) (s : bag) : bag := sum [v] s.

Example test_add1: count 1 (add 1 [1;4;1]) = 3.
Proof. reflexivity. Qed.
Example test_add2: count 5 (add 1 [1;4;1]) = 0.
Proof. reflexivity. Qed.

Fixpoint member (v : nat) (s : bag) : bool :=
  match s with
  | [] => false
  | h :: t => match (eqb h v) with
              | true => true
              | false => member v t
              end
  end.

Example test_member1: member 1 [1;4;1] = true.
Proof. reflexivity. Qed.
Example test_member2: member 2 [1;4;1] = false.
Proof. reflexivity. Qed.

Fixpoint remove_one (v : nat) (s : bag) : bag :=
  match s with
  | [] => []
  | h :: t => match (eqb h v) with
              | true => t
              | false => h :: (remove_one v t)
              end
  end.

Example test_remove_one1 : count 5 (remove_one 5 [2;1;5;4;1]) = 0.
Proof. reflexivity. Qed.
Example test_remove_one2 : count 5 (remove_one 5 [2;1;4;1]) = 0.
Proof. reflexivity. Qed.
Example test_remove_one3 : count 4 (remove_one 5 [2;1;4;5;1;4]) = 2.
Proof. reflexivity. Qed.
Example test_remove_one4 : count 5 (remove_one 5 [2;1;5;4;5;1;4]) = 1.
Proof. reflexivity. Qed.

Fixpoint remove_all (v : nat) (s : bag) : bag :=
  match s with
  | [] => []
  | h :: t => match (eqb h v) with
              | true => (remove_all v t)
              | false => h :: (remove_all v t)
              end
  end.

Example test_remove_all1: count 5 (remove_all 5 [2;1;5;4;1]) = 0.
Proof. reflexivity. Qed.
Example test_remove_all2: count 5 (remove_all 5 [2;1;4;1]) = 0.
Proof. reflexivity. Qed.
Example test_remove_all3: count 4 (remove_all 5 [2;1;4;5;1;4]) = 2.
Proof. reflexivity. Qed.
Example test_remove_all4: count 5 (remove_all 5 [2;1;5;4;5;1;4;5;1;4]) = 0.
Proof. simpl. reflexivity. Qed.

Fixpoint included (s1 : bag) (s2 : bag) : bool :=
  match s1, s2 with
  | [], [] => true
  | [], _ => true
  | _, [] => false
  | h1 :: t1, s2 => match (member h1 s2) with
                    | true => included t1 (remove_one h1 s2)
                    | false => false
                    end
  end.

Example test_included1: included [1;2] [2;1;4;1] = true.
Proof. simpl. reflexivity. Qed.
Example test_included2: included [1;2;2] [2;1;4;1] = false.
Proof. simpl. reflexivity. Qed.


Theorem add_inc_count : forall (v : nat) (s : bag), count v (add v s) = S (count v s). 
Proof.
  intros. simpl. rewrite eqb_refl. reflexivity.
Qed.

Theorem nil_app : forall l : natlist, [] ++ l = l.
Proof.
  intros. reflexivity.
Qed.

Theorem tl_length_pred : forall l : 
  natlist, pred (length l) = length (tl l).
Proof.
  intros. destruct l. reflexivity. reflexivity.
Qed.

Theorem app_assoc : forall l1 l2 l3 : natlist, 
  (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
Proof.
  intros. induction l1 as [| h t1 IHl'].
  - reflexivity.
  - simpl. rewrite IHl'.  reflexivity.
Qed.  

Theorem repeat_double_firsttry : forall c n: nat,
  repeat n c ++ repeat n c = repeat n (c + c).
Proof.
  intros c. induction c as [| c' IHc'].
  - (* c = 0 *)
    intros n. simpl. reflexivity.
  - (* c = S c' *)
    intros n. simpl.
    (*  Now we seem to be stuck.  The IH cannot be used to
        rewrite repeat n (c' + S c'): it only works
        for repeat n (c' + c'). If the IH were more liberal here
        (e.g., if it worked for an arbitrary second summand),
        the proof would go through. *)
Abort.

Theorem repeat_plus: forall c1 c2 n: nat,
    repeat n c1 ++ repeat n c2 = repeat n (c1 + c2).
Proof.
  intros c1 c2 n.
  induction c1 as [| c1' IHc1'].
  - simpl. reflexivity.
  - simpl.
    rewrite <- IHc1'.
    reflexivity.
  Qed.

Theorem repeat_double_secondtry : forall c n: nat,
  repeat n c ++ repeat n c = repeat n (c + c).
Proof.
  intros c. induction c as [| c' IHc'].
  - intros n. simpl. reflexivity.
  - intros n. rewrite repeat_plus. reflexivity.
Qed. 

Fixpoint rev (l : natlist) : natlist :=
  match l with
  | [] => []
  | h :: t => (rev t) ++ [h]
  end.

Example test_rev1: rev [1;2;3] = [3;2;1].
Proof. reflexivity. Qed.
Example test_rev2: rev nil = nil.
Proof. reflexivity. Qed.

Theorem rev_length_firsttry : forall l : natlist,
  length (rev l) = length l.
Proof.
  intros l. induction l as [| n l' IHl'].
  - (* l = nil *)
    reflexivity.
  - (* l = n :: l' *)
    (* This is the tricky case.  Let's begin as usual
       by simplifying. *)
    simpl.
    (* Now we seem to be stuck: the goal is an equality
       involving ++, but we don't have any useful equations
       in either the immediate context or in the global
       environment!  We can make a little progress by using
       the IH to rewrite the goal... *)
    rewrite <- IHl'.
    (* ... but now we can't go any further. *)
Abort.

Theorem app_rev_length_S_firsttry: forall l n,
  length (rev l ++ [n]) = S (length (rev l)).
Proof.
  intros l. induction l as [| m l' IHl'].
  - (* l =  *)
    intros n. simpl. reflexivity.
  - (* l = m:: l' *)
    intros n. simpl.
    (* IHl' not applicable. *)
Abort.

Theorem app_length_S: forall l n,
  length (l ++ [n]) = S (length l).
Proof.
  intros l. induction l as [| m l' IHl'].
  - intros n. reflexivity.
  - intros n. simpl. rewrite IHl'. reflexivity.
Qed.

Theorem rev_length : forall l : natlist,
  length (rev l) = length l.
Proof.
  intros l. induction l as [| m l' IHl'].
  - reflexivity.
  - simpl. rewrite app_length_S. rewrite <- IHl'. reflexivity.
Qed.

Theorem app_length : forall l1 l2 : natlist,
  length (l1 ++ l2) = (length l1) + (length l2).
Proof.
  intros l1. induction l1 as [|m1 l1' IHl'].
  - intros l2. reflexivity.
  - intros l2. simpl. rewrite IHl'. reflexivity.
Qed.

Theorem app_nil_r : forall l : natlist, l ++ [] = l.
Proof.
  induction l as [|m l' IHl'].
  - reflexivity.
  - simpl. rewrite IHl'. reflexivity.
Qed.

Theorem rev_app_distr: forall l1 l2 : natlist,
  rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
  intros l1. induction l1 as [|m1 l1' IHl1'].
  - intros l2. simpl. rewrite app_nil_r. reflexivity. 
  - intros l2. simpl. rewrite IHl1'. rewrite app_assoc. reflexivity.
Qed.

Theorem rev_involutive : forall l : natlist, rev (rev l) = l.
Proof.
  intros. induction l as [|m l' IHl'].
  - reflexivity.
  - simpl. rewrite rev_app_distr. rewrite IHl'. reflexivity.
Qed.

Theorem app_assoc4 : forall l1 l2 l3 l4 : natlist,
  l1 ++ (l2 ++ (l3 ++ l4)) = ((l1 ++ l2) ++ l3) ++ l4.
Proof.
  intros. rewrite app_assoc. rewrite app_assoc. reflexivity.
Qed.    

Lemma nonzeros_app : forall l1 l2 : natlist,
  nonzeros (l1 ++ l2) = (nonzeros l1) ++ (nonzeros l2).
Proof.
  intros l1. induction l1 as [|m1 l1' IHl1'].
  - intros l2. reflexivity.
  - intros l2. simpl. rewrite IHl1'. destruct m1.
    + reflexivity.
    + simpl. reflexivity.
Qed.

Fixpoint eqblist (l1 l2 : natlist) : bool :=
  match l1, l2 with
  | [], [] => true
  | _, [] => false
  | [], _ => false
  | h1 :: t1, h2 :: t2 => match (eqb h1 h2) with
                          | true => eqblist t1 t2
                          | false => false
                          end
  end.

Example test_eqblist1 : (eqblist nil nil = true).
Proof. reflexivity. Qed.
Example test_eqblist2 : eqblist [1;2;3] [1;2;3] = true.
Proof. reflexivity. Qed.
Example test_eqblist3 : eqblist [1;2;3] [1;2;4] = false.
Proof. reflexivity. Qed.
Theorem eqblist_refl : forall l : natlist, true = eqblist l l.

Proof.
  intros. induction l as [|m' l' IHl'].
  - reflexivity.
  - simpl. rewrite eqb_refl. rewrite IHl'. reflexivity.
Qed.  

Theorem count_member_nonzero : forall (s : bag),
  1 <=? (count 1 (1 :: s)) = true.
Proof.
  intros. induction s as [|m s' IHs'].
  - reflexivity.
  - reflexivity.
Qed.

Theorem leb_n_Sn : forall n, n <=? (S n) = true.
Proof.
  intros. induction n as [|n' IHn'].
  - reflexivity.
  - simpl. rewrite IHn'. reflexivity.
Qed.

Search ( _ =? 0).

Theorem remove_does_not_increase_count : forall (s : bag),
  (count 0 (remove_one 0 s)) <=? (count 0 s) = true.
Proof.
  intros. induction s as [|m s' IHs'].
  - reflexivity.
  - simpl. destruct m.
    + rewrite eqb_refl. rewrite leb_n_Sn. reflexivity.
    + rewrite S_neqb_0. simpl. rewrite IHs'. reflexivity.
Qed.

Theorem bag_count_sum : forall (v : nat) (s : bag), count v (sum [v] s) = S (count v s).
Proof.
  intros. simpl. rewrite eqb_refl. reflexivity.
Qed.

Theorem involution_injective : forall (f : nat -> nat),
    (forall n : nat, n = f (f n)) -> (forall n1 n2 : nat, f n1 = f n2 -> n1 = n2).
Proof.
  intros f H0. destruct n1.
  - intros n2 H1. rewrite H0. rewrite <- H1. rewrite <- H0. reflexivity.
  - intros n2 H1. rewrite H0. rewrite <- H1. rewrite <- H0. reflexivity.
Qed.

Theorem rev_injective : forall (l1 l2 : natlist), rev l1 = rev l2 -> l1 = l2.
Proof.
  intros l1. intros l2 H. rewrite <- rev_involutive. rewrite <- H. rewrite rev_involutive.
  reflexivity.
Qed.

Inductive natoption : Type :=
  | Some (n : nat)
  | None.

Fixpoint nth_error (l : natlist) (n : nat) : natoption :=
  match l with
  | nil => None
  | a :: l' => match n with
               | O => Some a
               | S n' => nth_error l' n'
               end
  end.

Definition option_elim (d : nat) (o : natoption) : nat :=
  match o with
  | Some n' => n'
  | None => d
  end.

Definition hd_error (l : natlist) : natoption :=
  match l with
  | [] => None
  | h :: t => Some h
  end.

Example test_hd_error1 : hd_error [] = None.
Proof. reflexivity. Qed.
Example test_hd_error2 : hd_error [1] = Some 1.
Proof. reflexivity. Qed.
Example test_hd_error3 : hd_error [5;6] = Some 5.
Proof. reflexivity. Qed.

Theorem option_elim_hd : forall (l : natlist) (default : nat),
  hd default l = option_elim default (hd_error l).
Proof.
  intros. destruct l.
  - reflexivity.
  - reflexivity.
Qed.    

End NatList.

Inductive id : Type :=
  | Id (n : nat).

Definition eqb_id (x1 x2 : id) :=
  match x1, x2 with
  | Id n1, Id n2 => n1 =? n2
  end.

Theorem eqb_id_refl : forall x : id, eqb_id x x = true.
Proof.
  intros. destruct x. destruct n.
  - reflexivity.
  - simpl. rewrite eqb_refl. reflexivity.
Qed.

Module PartialMap.
Export NatList.

Inductive partial_map : Type :=
  | empty
  | record (i : id) (v : nat) (m : partial_map).

Definition update (d : partial_map)
                  (x : id) (value : nat)
                  : partial_map :=
  record x value d.

Fixpoint find (x : id) (d : partial_map) : natoption :=
  match d with
  | empty => None
  | record y v d' => if eqb_id x y
                     then Some v
                     else find x d'
  end.

Theorem update_eq :
  forall (d : partial_map) (x : id) (v: nat),
    find x (update d x v) = Some v.
Proof.
  - intros. simpl. rewrite eqb_id_refl. reflexivity.
Qed.

Theorem update_neq :
  forall (d : partial_map) (x y : id) (o: nat),
    eqb_id x y = false -> find x (update d y o) = find x d.
Proof.
  -intros. simpl. rewrite H. reflexivity.
Qed.   

End PartialMap.