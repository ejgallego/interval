Require Import Reals.
Require Import Psatz.
Require Import Ssreflect.ssreflect.
Require Import Interval_missing.

Lemma INR_Z2R i : INR i = Z2R (Z.of_nat i).
Proof. by rewrite INR_IZR_INZ -Z2R_IZR. Qed.

Theorem Rneq_lt r1 r2 : r1 <> r2 -> (r1 < r2 \/ r2 < r1)%R.
Proof. by move=>H; elim: (Rtotal_order r1 r2) => [|[|]]; [left|done|right]. Qed.

(** Define a shorter name *)
Notation Rmult_neq0 := Rmult_integral_contrapositive_currified.

(** Lemma to be used with [field_simplify] and [ring] *)
Lemma Rdiv_eq_reg a b c d :
  (a * d = b * c -> b <> 0%R -> d <> 0%R -> a / b = c / d)%R.
Proof.
intros Heq Hb Hd.
apply (Rmult_eq_reg_r (b * d)).
field_simplify; trivial.
now rewrite Heq.
now apply Rmult_neq0.
Qed.
