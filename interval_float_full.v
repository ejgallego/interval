Require Import Reals.
Require Import xreal.
Require Import definitions.
Require Import float_sig.
Require Import interval.
Require Import interval_float.
Require Import transcend.

Module FloatIntervalFull (F : FloatOps with Definition even_radix := true) <: IntervalOps.

Module T := TranscendentalFloatFast F.
Module I := FloatInterval F.

(* assumption |xi| <= pi *)
Definition cos prec xi :=
  match I.abs xi with
  | Ibnd xl xu => I.bnd (I.lower (T.cos_fast prec xu)) (I.upper (T.cos_fast prec xl))
  | Inan => Inan
  end.

Axiom cos_correct : forall prec, I.extension Xcos (cos prec).

(* assumption |xi| <= pi/2 *)
Definition sin prec xi :=
  match xi with
  | Ibnd xl xu => I.bnd (I.lower (T.sin_fast prec xl)) (I.upper (T.sin_fast prec xu))
  | Inan => Inan
  end.

Axiom sin_correct : forall prec, I.extension Xsin (sin prec).

(* assumption |xi| <= pi/2 *)
Definition tan prec xi :=
  match xi with
  | Ibnd xl xu => I.bnd (I.lower (T.tan_fast prec xl)) (I.upper (T.tan_fast prec xu))
  | Inan => Inan
  end.

Axiom tan_correct : forall prec, I.extension Xtan (tan prec).

Definition atan prec xi :=
  match xi with
  | Ibnd xl xu => Ibnd (I.lower (T.atan_fast prec xl)) (I.upper (T.atan_fast prec xu))
  | Inan => Inan
  end.

Axiom atan_correct : forall prec, I.extension Xatan (atan prec).

Definition bound_type := I.bound_type.
Definition convert_bound := I.convert_bound.
Definition type := I.type.
Definition convert := I.convert.
Definition nai := I.nai.
Definition bnd := I.bnd.
Definition bnd_correct := I.bnd_correct.
Definition nai_correct := I.nai_correct.
Definition subset := I.subset.
Definition subset_correct := I.subset_correct.
Definition overlap := I.overlap.
Definition join := I.join.
Definition meet := I.meet.
Definition sign_large := I.sign_large.
Definition midpoint := I.midpoint.
Definition midpoint_correct := I.midpoint_correct.
Definition precision := I.precision.
Definition neg := I.neg.
Definition abs := I.abs.
Definition inv := I.inv.
Definition sqr := I.sqr.
Definition sqrt := I.sqrt.
Definition add := I.add.
Definition sub := I.sub.
Definition mul := I.mul.
Definition div := I.div.
Definition neg_correct := I.neg_correct.
Definition abs_correct := I.abs_correct.
Definition inv_correct := I.inv_correct.
Definition sqr_correct := I.sqr_correct.
Definition sqrt_correct := I.sqrt_correct.
Definition add_correct := I.add_correct.
Definition sub_correct := I.sub_correct.
Definition mul_correct := I.mul_correct.
Definition div_correct := I.div_correct.
Definition bounded := I.bounded.
Definition lower_bounded := I.lower_bounded.
Definition upper_bounded := I.upper_bounded.
Definition lower_extent := I.lower_extent.
Definition upper_extent := I.upper_extent.
Definition whole := I.whole.
Definition lower := I.lower.
Definition upper := I.upper.
Definition fromZ := I.fromZ.
Definition extension := I.extension.
Definition extension_2 := I.extension_2.

End FloatIntervalFull.