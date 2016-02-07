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

Section MinMax.
Lemma Rmin_refl x1 : Rmin x1 x1 = x1. (* !!! *)
Proof.
rewrite /Rmin.
case: (Rle_dec x1 x1); lra.
Qed.

Lemma Rmax_refl x1 : Rmax x1 x1 = x1. (* !!! *)
Proof.
rewrite /Rmax.
case: (Rle_dec x1 x1); lra.
Qed.

Local Open Scope R_scope.

Lemma Rmin_leq x1 x2 : x1 <= x2 -> Rmin x1 x2 = x1.
Proof.
move => H12.
rewrite /Rmin.
case: (Rle_dec x1 x2); lra.
Qed.

Lemma Rmax_leq x1 x2 : x1 <= x2 -> Rmax x1 x2 = x2.
Proof.
move => H12.
rewrite /Rmax.
case: (Rle_dec x1 x2); lra.
Qed.

Lemma Rmin_lt x1 x2 : x1 < x2 -> Rmin x1 x2 = x1.
move => H12.
rewrite /Rmin.
case: (Rle_dec x1 x2); lra.
Qed.

Lemma Rmax_lt x1 x2 : x1 < x2 -> Rmax x1 x2 = x2.
Proof.
move => H12.
rewrite /Rmax.
case: (Rle_dec x1 x2); lra.
Qed.

Lemma Rmin_swap x1 x2 : Rmin x1 x2 = Rmin x2 x1.
Proof.
rewrite /Rmin.
case: (Rle_dec x1 x2); case: (Rle_dec x2 x1); lra.
Qed.

Lemma Rmax_swap x1 x2 : Rmax x1 x2 = Rmax x2 x1.
Proof.
rewrite /Rmax.
case: (Rle_dec x1 x2); case: (Rle_dec x2 x1); lra.
Qed.

End MinMax.
