From Coq Require Import Reals.
From Interval Require Import Tactic.

Goal forall x, (2 <= IZR x -> 1 <= sqrt (IZR x))%R.
Proof.
intros.
interval.
Qed.
