From Coq Require Import Reals.
From Interval Require Import Tactic.

Open Scope R_scope.

Goal forall x y, -1/2 <= x <= 1/2 -> -1/2 <= y <= 1/2 ->
  Rabs (exp (x + y) / (exp x * exp y) - 1) <= 1/10.
Proof.
intros x y Hx Hy.
interval with (i_autodiff x, i_bisect y, i_bisect x).
Qed.
