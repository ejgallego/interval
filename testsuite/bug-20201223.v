From Coq Require Import Reals.
From Interval Require Import Tactic.

Goal forall x, (IZR (1 + 1) <= IZR x -> 1 <= sqrt (IZR x))%R.
Proof.
intros.
interval.
Qed.
