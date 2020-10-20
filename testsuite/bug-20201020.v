Require Import Reals.
Require Import Interval.Tactic.

Goal forall x, (1 < x)%R -> (2 > Rabs x)%R -> (2 <= x + 1 <= 3)%R.
Proof.
intros x H1 H2.
interval.
Qed.
