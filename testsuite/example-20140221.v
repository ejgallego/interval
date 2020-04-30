Require Import Reals.
Require Import Interval.Tactic.

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
Time interval with (i_bisect x, i_autodiff x, i_prec 50, i_depth 16). (* 22 s *)
*)
Time interval with (i_bisect x, i_taylor x, i_degree 3, i_prec 50). (* 0.12 s *)
Qed.

(* The timings above were obtained using Coq 8.9.1 *)
