(**
This file is part of the Coq.Interval library for proving bounds of
real-valued expressions in Coq: http://coq-interval.gforge.inria.fr/

Copyright (C) 2007-2015, Inria

This library is governed by the CeCILL-C license under French law and
abiding by the rules of distribution of free software. You can use,
modify and/or redistribute the library under the terms of the CeCILL-C
license as circulated by CEA, CNRS and Inria at the following URL:
http://www.cecill.info/

As a counterpart to the access to the source code and rights to copy,
modify and redistribute granted by the license, users are provided
only with a limited warranty and the library's author, the holder of
the economic rights, and the successive licensors have only limited
liability. See the COPYING file for more details.
*)

Require Import Reals.
Require Import Interval_xreal.
Require Import Interval_definitions.
Require Import Interval_float_sig.
Require Import Interval_generic.
Require Import Interval_generic_proof.

Module FloatExt (F : FloatOps).

Definition le x y :=
  match F.cmp x y with
  | Xlt | Xeq => true
  | Xgt | Xund => false
  end.

Lemma le_correct :
  forall x y,
  le x y = true ->
  match F.toX x, F.toX y with
  | Xreal xr, Xreal yr => (xr <= yr)%R
  | _, _ => False
  end.
Proof.
intros x y.
unfold le.
rewrite F.cmp_correct, Fcmp_correct, !F.toF_correct.
destruct F.toX as [|xr]. easy.
destruct F.toX as [|yr]. easy.
simpl.
now case Fcore_Raux.Rcompare_spec ; auto with real.
Qed.

Definition lt x y :=
  match F.cmp x y with
  | Xlt  => true
  | _ => false
  end.

Lemma lt_correct :
  forall x y,
  lt x y = true ->
  match F.toX x, F.toX y with
  | Xreal xr, Xreal yr => (xr < yr)%R
  | _, _ => False
  end.
Proof.
intros x y.
unfold lt.
rewrite F.cmp_correct, Fcmp_correct, !F.toF_correct.
destruct F.toX as [|xr]. easy.
destruct F.toX as [|yr]. easy.
simpl.
now case Fcore_Raux.Rcompare_spec.
Qed.

End FloatExt.
