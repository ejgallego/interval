From Coq Require Import Reals.
From Interval Require Import Tactic.

Open Scope R_scope.

Goal forall x, 1 <= x -> sin (x - 1) / (x - 3/4) <= 7/10.
Proof.
intros.
interval with (i_bisect x, i_autodiff x).
Qed.
