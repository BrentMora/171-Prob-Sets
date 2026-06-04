(*
INSTRUCTIONS

Place this file (ps_blanks.v) inside a folder containing the
solution codes Basics.v, Lists.v, Logic.v.

Afterwards, make and compile Basics.v, Lists.v, Logic.v,
so that you can import functions / theorems defined there.
*)

From LF Require Export Basics.
From LF Require Export Lists.
From LF Require Export Logic.

(* ################################################################# *)

(*
1. (6pts TOTAL). CIRCUIT VERIFICATION. This is the first part 
of this problem set where you'll verify some very simple circuits.
*)

(*
HINT 1: If a goal has a function name that cannot be simplified, 
try using the tactic 'unfold'.
*)

Inductive signal : Type :=
  | ON
  | OFF.

(*
1.a (2pts). Define the following logic gates:
*)

Definition not_gate (s : signal) : signal :=
(*write your answer here*)

Definition or_gate (s1 s2 : signal) : signal :=
(*write your answer here*)

Definition and_gate (s1 s2 : signal) : signal :=
(*write your answer here*)

Definition xor_gate (s1 s2 : signal) : signal :=
(*write your answer here*)

Definition xnor_gate (s1 s2 : signal) : signal :=
(*write your answer here*)

Definition nor_gate (s1 s2 : signal) : signal :=
(*write your answer here*)

Definition nand_gate (s1 s2 : signal) : signal :=
(*write your answer here*)


(*
1.b (1pt). Take a look at this circuit image:
https://drive.google.com/file/d/1u_Vk0XN7dsdWT9Ecr9y0h6x4zHOohROZ/view?usp=sharing
Implement the circuit as a function mygate. You may use the gates 
you defined in 1.a.
*)

Definition mygate (s1 s2 s3 s4 : signal) : signal :=
(*write your answer here*)


(*
1.c (1pt). Prove the following Theorem c1 which states that if the incoming
signal has s1 = ON, then your mygate circuit from 1.b automatically outputs ON.
*)

Theorem c1 : forall s1 s2 s3 s4 : signal,
  s1 = ON -> mygate s1 s2 s3 s4 = ON.
(*write your answer here*)


(*
1.d (1pt). Take a look at this circuit image.
https://drive.google.com/file/d/1cVFAFCeAz2S-2Cq9okMgSw-CjC5KXD6w/view?usp=sharing
Implement the circuit as a function mygate2.
*)

Definition mygate2 (s1 s2 : signal) : signal :=
(*write your answer here*)


(*
1.e (1pt). Using the proposition equalgates defined below, 
prove that mygate2 is an equivalent circuit to xnor_gate by showing that 
both circuits output the same signal for any input. This is Theorem c2.
*)

Definition equalgates (g1 g2 : signal -> signal -> signal) : Prop := 
forall (s1 s2 : signal), g1 s1 s2 = g2 s1 s2.

Theorem c2 : equalgates mygate2 xnor_gate. 
(*write your answer here*)


(* ################################################################# *)

(*
HINT 1: If a goal has a function name that cannot be simplified, 
try using the tactic 'unfold'.

HINT 2: If a hypothesis has a false equality, try using the tactic
'discriminate' on the hypothesis.

HINT 3: If a goal is in the form of a conjunction, you need to prove both
sides of the conjunction, so try using the tactic 'split'.
*)

(*
2. (8pts TOTAL). GAME THEORY. For this part, you will verify some instances of
a full information 2 player game.
*)

Inductive player : Type :=
  | p1
  | p2.

Inductive action : Type :=
  | betray
  | silent.

Inductive strategy : Type :=
  actionpair (a1 : action) (a2 : action).

(*
2.a (1pt). Take a look at this image.
https://drive.google.com/file/d/1n9TZn3jVXd1-33Y9uODFNWwobwc77nXc/view?usp=sharing
Each cell of the table contains a tuple where the first coordinate
refers to the utility gained by player 1 if player 1 acts according to the
row's action. The second coordinate refers to the utility gained by player 2
if player 2 acts according to the column's action.

For instance, under row P1 BETRAY and column P2 BETRAY, we have the tuple
(5,5), which indicates that if P1 betrays and P2 betrays, then both gain utility
5. On the other hand, under row P1 BETRAY and column P2 SILENT, we have the
tuple (3,0) which indicates that if P1 betrays and P2 stays silent, then P2
gains nothing but P1 gains a utility of 3.

Implement the utility function as utility1 below, where utility1 takes in
2 inputs. The first input is a player datatype, and the second is a 
strategy datatype, where both player and strategy are defined for you above.
Given a player p and a strategy s, utility1 should output a nat corresponding to
the table shown in the image link.
*)

Definition utility1 (p : player) (s : strategy) : nat :=
(*write your answer here*)


(*
2.b (1pt). A dominant strategy is a strategy which gives a higher (or equal) utility 
for both players compared to all other strategies. Prove the Theorem gt1
below which states that given utility1, BETRAY BETRAY is a dominant strategy.
*)

Definition dominant_strategy (s : strategy) (u : player -> strategy -> nat): Prop := 
forall (p : player) (s' : strategy), (u p s' <=? u p s) = true.

Theorem gt1 : dominant_strategy (actionpair betray betray) utility1.
(*write your answer here*)


(*
2.c (1pt). Take a look at this image.
https://drive.google.com/file/d/1PaZ55zVCLbMcD_MoBW-QhLkYUnTQ1ieG/view?usp=sharing
Implement the utility function described in the image as the function
utility2 below.
*)

Definition utility2 (p : player) (s : strategy) : nat :=
(*write your answer here*)


(*
2.d (1pt). Given a player p and a strategy s, implement the function
get_action which fetches the action of player p under strategy s.
*)

Definition get_action (p : player) (s : strategy) :=
(*write your answer here*)


(*
2.e (1pt). An equilibrium strategy is a strategy in which each player is
better off sticking to the current strategy - under the assumption
that the other player's action remains fixed. 

Research prisonner's dilemma for more information about an equilibrium strategy.

This notion is defined below as the proposition equilibrium. 
Prove that the actionpair BETRAY BETRAY is an equilibrium given utility2 via Theorem gt2.
*)

Definition equilibrium (s : strategy) (u : player -> strategy -> nat) : Prop := 
forall (s' : strategy), 
(get_action p2 s = get_action p2 s' -> (u p1 s' <=? u p1 s) = true) 
/\
(get_action p1 s = get_action p1 s' -> (u p2 s' <=? u p2 s) = true).

Theorem gt2 : equilibrium (actionpair betray betray) utility2.
(*write your answer here*)


(*
2.f (1pt). Given the proposition equilibrium defined above, write its negation
as the proposition not_equilibrium below.
*)

Definition not_equilibrium (s : strategy) (u : player -> strategy -> nat) : Prop :=
(*write your answer here*) 
exists (s' : strategy), 
(get_action p2 s = get_action p2 s' -> (u p1 s' <=? u p1 s) = false) 
\/
(get_action p1 s = get_action p1 s' -> (u p2 s' <=? u p2 s) = false).

(*
2.g (1pt). Prove Theorem gt3 which states that the strategy SILENT SILENT
is not an equilibrium given utility2.
*)

Theorem gt3 : not_equilibrium (actionpair silent silent) utility2.
(*write your answer here*)


(*
2.h (1pt). Prove Theorem gt4 below which states that if a strategy is
dominant, then it is an equilibrium, i.e. dominance of a strategy
is a sufficient condition for being an equilibrium.
*)

Theorem gt4 : forall (s : strategy) (u : player -> strategy -> nat), 
dominant_strategy s u -> equilibrium s u.
(*write your answer here*)
    

(* ################################################################# *)

(*
3. (2pts TOTAL). NATURAL NUMBERS. We'll prove here some results 
regarding our favorite natural numbers.
*)

(*
3.a (1pt). Prove this simple Theorem.
*)

Theorem num0 : forall (n : nat), (even n = even (S n)) -> False.
(*write your answer here*)


(*
3.b (1pt). Assuming Axiom axone, prove Theorem num1 below which states
that any natural number is either even or not even (i.e. odd).
*)

Axiom axone : forall (n : nat), ((even n = true) -> False) -> (even (S n) = true).

Theorem num1 : forall (n : nat), (even n = true) \/ ((even n = true) -> False).
(*write your answer here*)


(* ################################################################# *)

(*
4. (5pts TOTAL). LOGIC: Let's do some logic !
*)

(*
4.1 (1pt). Prove the Theorem logic1 below which is a tautology.
*)

Theorem logic1 : forall (A B : Prop), (A /\ B -> False) -> A -> (B -> False).
(*write your answer here*)


(*
4.2 (1pt). Prove the Theorem logic2 below which is another tautology.
*)

Theorem logic2 : forall (A B : Prop), (A /\ B -> False) <-> (A -> (B -> False)).
(*write your answer here*)


(*
4.3 (1pt). Assuming Axiom axtwo, prove the Theorem logic3 below.
We need Axiom axtwo because logic3 cannot be proven under constructivist
assumptions.
*)

Axiom axtwo : forall (A B : Prop), ((A -> False) -> B) -> ((B -> False) -> A).  

Theorem logic3 : forall (A B C D : Prop),
  (((A -> C) /\ ((B -> False) -> D)) /\ ((C /\ D) -> False)) -> (A -> C) /\ (C -> B).
(*write your answer here*)


(*
4.4 (1pt). State the law of the excluded middle as a proposition.
*)

Definition excluded_middle : Prop := 
(*write your answer here*)

(*
4.5 (1pt). Assuming excluded_middle, prove the other direction of
De Morgan's Law, which also cannot be proven using constructivist assumptions.
*)

Theorem logic4 : forall (P Q : Prop), 
  excluded_middle -> (P -> False) /\ (Q -> False) -> ((P \/ Q) -> False).
(*write your answer here*)


(* ################################################################# *)

(*
5. (7pts TOTAL). Computer Assisted Education Tool (CAET). 
Here we'll verify a (very) simple computer system that has the following specs:

Users are student / teacher / admin.
Files are lesson / quiz / grade / userdata.
Disk are disk_a / disk_b / disk_c.
Privilege are read / write.

If a file is lesson or quiz, it is stored in disk_a.
If a file is grade, it is stored in disk_b.
If a file is userdata, it is stored in disk_c.

If a user is a student, read privilege is granted to disk_a.
If a user is a teacher, read / write privilege is granted to disk_a and disk_b,
but only read privilege to disk_c.
If a user is an admin, read / write privilege is granted to disk_c, but only
read privilege to all other disks.
*)

(*
5.a (1pt). Implement the following data types following the specs above.
*)

Inductive user : Type :=
(*write your answer here*)

Inductive file : Type :=
(*write your answer here*)

Inductive disk : Type :=
(*write your answer here*)

Inductive privilege : Type :=
(*write your answer here*)

(*
5.b (1pt). Define the function check_disk such that given an input file,
outputs the disk in which the file is stored (following specs above).
*)

Definition check_disk (f : file) : disk :=
(*write your answer here*)


(*
5.c (1pt). Define the function check_access such that given inputs
user, file and privilege, returns true if the specs above are followed
and false otherwise. For instance, the input: student grade write should return false, 
while the input student lesson read should return true.
*)

Definition check_access (u : user) (f : file) (p : privilege) : bool :=
(*write your answer here*)


(*
5.c (1pt). Define the proposition access, which is True if the
user has the right privilege for a file, and False o.w.
*)

Definition access (u : user) (f : file) (p : privilege) : Prop :=
(*write your answer here*)


(*
5.d (1pt). Prove Theorem caet1 which states that if a user is a teacher,
then the teacher does not have write privilege to userdata files.
*)

Theorem caet1 : forall u, u = teacher -> ((access u userdata write) -> False).
(*write your answer here*)


(*
5.d (1pt). Prove Theorem caet2 which states that if a user is an admin, then
he is given read / write privileges on userdata files.
*)

Theorem caet2 : forall (u : user) (p : privilege), u = admin -> access u userdata p.
(*write your answer here*)


(*
5.e (1pt). Prove Theorem caet3 which states that if a file is either a quiz
or a lesson, and if the user has write privileges on both files, then
the user is necessarily a teacher.
*)

Theorem caet3 : forall u f, ((f = quiz) \/ (f = lesson)) -> 
(access u lesson write /\ access u quiz write) -> u = teacher.
(*write your answer here*)


(*
5.f (1pt). Prove Theorem caet4 which states that a student user has read access
to lesson / quiz, but no write access.
*)

Theorem caet4 : forall u, u = student -> access u lesson read /\ 
access u quiz read /\ (access u lesson write -> False) /\ (access u quiz write -> False).
(*write your answer here*)


(*
5.g (1pt). Prove Theorem caet5 which states that an admin user has
read access to all files.
*)

Theorem caet5 : forall u f, u = admin -> access u f read.
(*write your answer here*)


(*
6. (7pts TOTAL). PERCEPTRON. For data science fans, here we'll verify the simplest
neural net, which is the perceptron. 

Let's define a perceptron as a list of natural numbers (i.e. the list are our weights). 
An input to our perceptron is another list of natural numbers.

Let's assume that our data consists of two classes: class1 and class2.
*)

Definition perceptron := list nat.
Definition input := list nat.
Inductive class : Type :=
  | class1
  | class2.

(*
6.a (1pt). Define the function inference below, where if we set our
perceptron as the vector w, and our input as the vector i
then:

inference(p,i) = (w^T)(i)

or that inference is the dot product of our perceptron with the
input.
*) 

Fixpoint inference (p : perceptron) (i : input) : nat :=
(*write your answer here*)


(*
6.b (1pt). Define the function classify such that given an input 
number x, and a threshold number thresh, if x is less than or equal to thresh
then classify outputs class1. Otherwise, it outputs class2.
*)

Definition classify (x : nat) (thresh : nat) : class :=
(*write your answer here*)


(*
6.c (1pt). Define the function reducesum which sums up all the elements
of an input list.
*)

Fixpoint reducesum (i : input) : nat :=
(*write your answer here*)


(*
6.d (1pt). Define the function getclass which fetches the true class of
an input vector, whereby given an input list i and a natural
number border, the function getclass sums up all the elements of i.
If the sum is less than or equal to border, then getclass outputs class1.
Otherwise, it outputs class2.

Note that if getclass is well-defined, then our data is linearly separable.

From our definition, if getclass i = class1, then we assume that i is truly under
class1.
*)

Definition getclass (i : input) (border : nat) : class :=
(*write your answer here*)


(*
6.e (1pt). Define the proposition correct, which is TRUE if 
the perceptron correctly classifies a given input i, given a fixed thresh and border.
*)

Definition correct (p : perceptron) (thresh : nat) (border : nat) (i : input) : Prop :=
(*write your answer here*)


(*
6.f (1pt). Define the proposition trained, which is TRUE if 
the perceptron correctly classifies any input i, given a fixed thresh and border.
*)

Definition trained (p : perceptron) (thresh border : nat): Prop :=
(*write your answer here*)


(*
6.g (1pt). Prove the Theorem per1, which states that if our data consists only
of two datapoints, namely [1;1;1] and [5;5;5] along with a border of 10,
then a perceptron with weights [3;3;3] and a threshold of 10 can be considered
to satisfy the trained proposition.
*)

Theorem per1 : 
  forall p thresh border, (border = 10) -> (forall (i : input), i = [1;1;1] \/ i = [5;5;5]) -> (p = [3;3;3]) -> (thresh = 10) -> trained p thresh border.
(*write your answer here*)


(*
7. (8pts TOTAL). PEANO AXIOMS. For math fans, we'll prove that nat is a model of the Peano Axioms.
*)

(*
7.a (1pt). Take a look at this image.
https://drive.google.com/file/d/1nL0RIihlToPA1drWiuiPUuFLHZs9qPHo/view?usp=sharing
Interpret /\ in the image as 'for all'. Write down the Peano Axioms 2-5. 
As examples, Peano Axioms 1,6,7,8 are provided.
*)

Definition peanoax1 (X : Type) (o : X) (f : X -> X) : Prop :=
  forall (x : X), (f x = o) -> False.

Definition peanoax2 (X : Type) (f : X -> X) : Prop :=
(*write your answer here*)

Definition peanoax3 (X : Type) (p : X -> X -> X) (z : X) (f : X -> X) : Prop :=
(*write your answer here*)

Definition peanoax4 (X : Type) (p : X -> X -> X) (f : X -> X) : Prop :=
(*write your answer here*)

Definition peanoax5 (X : Type) (m : X -> X -> X) (z : X) : Prop := 
(*write your answer here*)

Definition peanoax6 (X : Type) (m : X -> X -> X) (p : X -> X -> X) (z : X) (f : X -> X) : Prop := 
  forall (x y : X), m x (f y) = p (m x y) x.

Definition peanoax7 (X : Type) (l : X -> X -> Prop) (p : X -> X -> X) : Prop := 
  forall (x y : X), l x y <-> exists (n : X), (y = p x n).

Definition peanoax8 (X : Type) (o : X) (f : X -> X) : Prop :=
  forall (x : X) (P : X -> Prop), ((P o) /\ (forall x : X, P x -> P (f x))) -> forall x, P x.


(*
7.b (1pt). Define the proposition isapeanomodel which is TRUE if the inputs satisfy
each of the Peano Axioms.
*)

Definition isapeanomodel (X : Type) (o : X) (z : X) (f : X -> X) (p : X -> X -> X) (m : X -> X -> X) (l : X -> X -> Prop) : Prop :=
(*write your answer here*) 


(*
7.c (3pts). Prove the following Theorems natpax1-natpax8 which state that nat given 
O, S, plus, minus, and le as interpretations for the Peano symbols, 
satisfies each of the Peano Axioms 1-8. You may use built-in theorems of Rocq for nat.
HINT: You may use 'Search' to check existing Rocq theorems.
*)

Theorem natpax1 : peanoax1 nat O S.
(*write your answer here*)


Theorem natpax2 : peanoax2 nat S.
(*write your answer here*)


Theorem natpax3 : peanoax3 nat plus (S O) S.
(*write your answer here*)


Theorem natpax4 : peanoax4 nat plus S.
(*write your answer here*)


Theorem natpax5 : peanoax5 nat mult (S O).
(*write your answer here*)


Theorem natpax6 : peanoax6 nat mult plus (S O) S.
(*write your answer here*)


Theorem natpax7 : peanoax7 nat le plus.
(*write your answer here*)


Theorem natpax8 : peanoax8 nat O S.
(*write your answer here*)


(*
7.d (1pt). Prove Theorem natisapeanomodel which states that nat is a model of the Peano Axioms.
*)

Theorem natisapeanomodel : isapeanomodel nat O (S O) S plus mult le .
      

(*
7.e (1pt). The Axiom groupaxone is one of the axioms of Group Theory. Define the proposition
notgroupaxone which is the negation of groupaxone.
*)

Definition groupaxone (X : Type) (o : X) (p : X -> X -> X) : Prop := 
forall (x : X), exists (y : X), p x y = o.

Definition notgroupaxone (X : Type) (o : X) (p : X -> X -> X) : Prop := 
(*write your answer here*)


(*
7.f (1pt). Prove Theorem natisnotagroup which states that nat fails to satisfy Axiom groupaxone,
so that nat is not a model of Group Theory.
*)

Theorem natisnotagroup : notgroupaxone nat O plus.



(* ################################################################# *)



