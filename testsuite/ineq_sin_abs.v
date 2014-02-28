Require Import Reals Interval_tactic.

Require Import Fcore_Raux. (* for Rabs_le_inv *)

Local Open Scope R_scope.

(* Define a bound "b" a bit less than PI/2 *)
Notation b := (157 / 100) (only parsing).

Goal forall x : R, Rabs x <= b ->  sin (Rabs x) >= 0.
intros x Hx.
(* BEGIN bookkeeping *)
rewrite <-Ropp_0, <-(Ropp_involutive (sin _)).
apply Ropp_le_ge_contravar.
apply Rabs_le_inv in Hx.
(* rewrite <-Ropp_div in Hx. *)
interval_intro b upper as Hr.
interval_intro (-b) lower as Hl.
generalize (conj (Rle_trans _ _ _ Hl (proj1 Hx)) (Rle_trans _ _ _ (proj2 Hx) Hr)).
clear; intros Hx.
(* END bookkeeping *)
Time interval with (i_bisect_taylor x 0, i_depth 1).
Qed.
