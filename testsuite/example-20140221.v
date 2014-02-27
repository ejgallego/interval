Require Import Reals.
Require Import Interval_tactic.
Require Import Interval_missing. (* for Z2R_IZR, pow_powerRZ *)

(*
Example taken from:
John Harrison, Verifying the Accuracy of Polynomial Approximations in HOL.
In TPHOLs, pages 137-152, 1997.
*)

Notation claim :=
  (forall x : R,
    (-10831/1000000 <= x /\ x <= 10831/1000000) ->
    Rabs ((exp x - 1) - (x + (8388676/2^24) * x^2 + (11184876/2^26) * x^3))
    <= ((23/27) / (2^33)))%R
  (only parsing).

Goal claim.
intros x H.
interval_intro (10831/1000000)%R upper.
interval_intro (-10831/1000000)%R lower.
generalize (conj (Rle_trans _ _ _ H1 (proj1 H)) (Rle_trans _ _ _ (proj2 H) H0)).
clear; intros H.

Time interval_intro (exp x - 1)%R with (i_bisect_taylor x 2).
clear H0.

Time interval with (i_bisect_taylor x 3, i_prec 50, i_depth 7).
(* No more subgoals. *)
(* Finished transaction in 0. secs (0.593962u,0.003918s) *)
Qed.

(*
Goal claim.
intros x H.
interval_intro (23 / 27 / 2 ^ 33)%R lower.
apply Rle_trans with (2 := H0); clear H0.
interval_intro (10831/1000000)%R upper.
interval_intro (-10831/1000000)%R lower.
generalize (conj (Rle_trans _ _ _ H1 (proj1 H)) (Rle_trans _ _ _ (proj2 H) H0)).
clear; intros H.

Time interval with (i_bisect_diff x, i_prec 50, i_depth 16).
(* No more subgoals. *)
(* Finished transaction in 33. secs (32.86976u,0.007909s) *)
Qed.
*)
