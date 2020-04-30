Require Import Reals Interval.Tactic.

Goal forall x : R,
  (Rabs (x - x) <= 1/5)%R.
Proof.
intros x.
interval with (i_autodiff x).
Qed.
