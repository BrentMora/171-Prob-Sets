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
Admitted.

(*1pt. *)
Example two : 
  {{ Y = X + 1 }}
    X := X + 1
  {{ Y = X }}.
Proof.
Admitted.

(*1pt. *)
Example three : 
  {{ Y > 0 }}
  X := Y + 3
  {{ X > 3 }}.
Proof.
Admitted.

(*1pt. *)
Example four : 
  {{ X = 5 }}
  X := X + 1
  {{ X > 0 }}.
Proof.
Admitted.

(*1pt. *)
Example five : 
  {{ X > 2 }}
  X := X + 1;
  X := X + 2
  {{ X > 5 }}.
Proof.
Admitted.

(*1pt. *)
Axiom axone: forall X a (st : state), ((st X > a) /\ (st X <=? a) = true) -> False.

(*You may use Axiom axone. *)
Example six :
  {{ X > 2 }}
  if X > 2 then Y := 1 else Y := 0 end
  {{ Y = 1}}.
Proof.
Admitted. 

(*1pt. *)
Example seven :
  {{ X >= 0 }}
  while X > 0 do X := X - 1 end
  {{ X = 0 }}.
Proof.
Admitted.

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
Admitted.     

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
Admitted.

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
Admitted.