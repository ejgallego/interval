Require Import Reals Interval.Tactic.

Goal forall x, (-1 / 3 <= x - x <= 1 / 7)%R.
Proof.
intros x.
interval with (i_autodiff x, i_prec 10).
Qed.
