From Coq Require Import Reals.
From Flocq Require Import Core.
From Interval Require Import Tactic.

Goal forall x, (IZR (1 + 1) <= IZR x -> 1 <= sqrt (IZR x))%R.
Proof.
intros.
interval.
Qed.

Goal forall prec,
  (0 <= bpow radix2 (1 - prec) <= 1 / 32 ->
  12 / 25 <= (2 - bpow radix2 (1 - prec)) / (2 * (2 + bpow radix2 (1 - prec))))%R.
Proof.
intros.
interval.
Qed.
