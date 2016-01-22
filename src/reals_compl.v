Require Import Reals.
Require Import ssreflect.
Require Import Psatz .

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
