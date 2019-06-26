Require Import Reals.
Require Import Interval.Tactic.
Local Open Scope R_scope.

Goal forall x : R, exp x >= 0.
intros; interval.
Qed.
