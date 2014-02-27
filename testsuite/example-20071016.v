Require Import Reals.
Require Import Interval_tactic.

Goal
  forall x, (-1 <= x <= 1)%R ->
  (sqrt (1 - x) <= 3/2)%R.
Proof.
  intros.
  interval.
Qed.

Goal
  forall x, (-1 <= x <= 1)%R ->
  (sqrt (1 - x) <= 141422/100000)%R.
Proof.
  intros.
  interval.
Qed.

Goal
  forall x, (-1 <= x <= 1)%R ->
  (sqrt (1 - x) <= 141422/100000)%R.
Proof.
  intros.
  interval_intro (sqrt (1 - x)) upper as H'.
  apply Rle_trans with (1 := H').
  interval.
Qed.

Goal
  forall x, (3/2 <= x <= 2)%R ->
  forall y, (1 <= y <= 33/32)%R ->
  (Rabs (sqrt(1 + x/sqrt(x+y)) - 144/1000*x - 118/100) <= 71/32768)%R.
Proof.
  intros.
  interval with (i_prec 19, i_bisect x).
Qed.

Goal
  forall x, (1/2 <= x <= 2)%R ->
  (Rabs (sqrt x - (((((122 / 7397 * x + (-1733) / 13547) * x
                   + 529 / 1274) * x + (-767) / 999) * x
                   + 407 / 334) * x + 227 / 925))
    <= 5/65536)%R.
Proof.
  intros.
  interval with (i_bisect_diff x).
Qed.
