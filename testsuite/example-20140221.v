Require Import Reals.
Require Import Interval_tactic.

Local Open Scope R_scope.

(*
Example taken from:
John Harrison, Verifying the Accuracy of Polynomial Approximations in HOL.
In TPHOLs, pages 137-152, 1997.
*)

Goal
  forall x : R,
    (-10831/1000000 <= x /\ x <= 10831/1000000) ->
    Rabs ((exp x - 1) - (x + (8388676/2^24) * x^2 + (11184876/2^26) * x^3))
    <= (23/27) / (2^33).
Proof.
intros x H.
(*
(* Erik: the following 2 lines are required only for i_bisect_diff *)
interval_intro (23 / 27 / 2 ^ 33) lower as H0.
apply Rle_trans with (2 := H0); clear H0.
Time interval with (i_bisect_diff x, i_prec 50, i_depth 16). (* 31 s *)
*)
Time interval with (i_bisect_taylor x 3, i_prec 50). (* 0.48 s *)
Qed.

(* The timings above were obtained using Coq 8.4pl6 *)
