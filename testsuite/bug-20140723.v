Require Import Reals.
Require Import Interval.Tactic.

Goal True.
interval_intro PI lower.
interval_intro (PI/2)%R upper.
exact I.
Qed.
