Require Import Reals.
Require Import Interval_tactic.

Local Open Scope R_scope.

(*
Example taken from:
John Harrison, Verifying the Accuracy of Polynomial Approximations in HOL.
In TPHOLs, pages 137-152, 1997.
*)

Notation claim :=
  ( forall x : R,
    (-10831/1000000 <= x /\ x <= 10831/1000000) ->
    Rabs ((exp x - 1) - (x + (8388676/2^24) * x^2 + (11184876/2^26) * x^3))
    <= ((23/27) / (2^33)) )
  (only parsing).

Goal claim.
intros x [_x x_].
interval_intro (-10831/1000000) lower as H1.
interval_intro (10831/1000000) upper as H2.
apply Rle_trans with (1 := H1) in _x; clear H1.
apply Rle_trans with (2 := H2) in x_; clear H2.
(* Erik: the following line should be optional *)
pose proof (conj _x x_) as Hx; clear _x x_.
(* Erik: the following 2 lines are required only for i_bisect_diff *)
interval_intro (23 / 27 / 2 ^ 33) lower as H0.
apply Rle_trans with (2 := H0); clear H0.

Time interval with (i_bisect_taylor x 3, i_prec 50).
(* Finished transaction in 0. secs (0.382009u,0.002368s) *)

(* Undo.
Time interval with (i_bisect_diff x, i_prec 50, i_depth 16).
(* Finished transaction in 49. secs (48.178082u,0.047943s) *)
*)

Qed.
