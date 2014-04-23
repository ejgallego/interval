Require Import Reals Interval_tactic.

Local Open Scope R_scope.

(* Define a bound "b" a bit less than PI/2 *)
Notation b := (157 / 100) (only parsing).

Goal forall x : R, Rabs x <= b ->  0 <= sin (Rabs x).
intros x Hx.
(* BEGIN bookkeeping *)
interval_intro b upper as Hr.
apply Rle_trans with (2 := Hr) in Hx.
(* END bookkeeping *)

interval_intro (sin (Rabs x)) lower
  with (i_bisect_taylor x 0, i_depth 1, i_prec 32) as test.
(* test : -1 * / 4294967296 <= sin (Rabs x) *)
clear test.

interval with (i_depth 0, i_prec 0).
Qed.
