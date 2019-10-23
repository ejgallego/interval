Require Import Reals.
Require Import Interval.Tactic.

Goal forall x, (1 <= x)%R -> (0 < x)%R.
Proof.
intros.
interval.
Qed.

Goal forall x, (1 <= x)%R -> (x <= x * x)%R.
Proof.
intros.
apply Rminus_le.
interval with (i_bisect_diff x).
Qed.

Goal forall x, (2 <= x)%R -> (x < x * x)%R.
Proof.
intros.
apply Rminus_lt.
interval with (i_bisect_diff x).
Qed.

Goal forall x, (-1 <= x)%R -> (x < 1 + powerRZ x 3)%R.
Proof.
intros.
apply Rminus_lt.
interval with (i_bisect_diff x).
Qed.
