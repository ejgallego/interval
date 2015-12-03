(**
This file is part of the CoqApprox formalization of rigorous
polynomial approximation in Coq:
http://tamadi.gforge.inria.fr/CoqApprox/

Copyright (c) 2010-2014, ENS de Lyon and Inria.

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

Require Import ZArith.
Require Import Reals.
Require Import Interval_interval.
Require Import Interval_xreal.
Require Import Interval_definitions.
Require Import Interval_specific_ops.
Require Import Interval_float_sig.
Require Import Interval_interval_float.
Require Import Interval_interval_float_full.
Require Import Ssreflect.ssreflect Ssreflect.ssrfun Ssreflect.ssrbool Ssreflect.eqtype Ssreflect.ssrnat Ssreflect.seq.
Require Import coeff_inst.
Require Import poly_datatypes.
Require Import taylor_poly.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Type IntPolyOps (I : IntervalOps).
Module Int := FullInt I.
Include PolyOps Int.
End IntPolyOps.

Module Type IntMonomPolyOps (I : IntervalOps).
Module Int := FullInt I.
Include PowDivMonomPolyOps Int.
End IntMonomPolyOps.

Module Type LinkIntR
  (I : IntervalOps) (Import Pol : IntPolyOps I)
  (PolR : PolyOps FullR).

Definition contains_pointwise_until fi fx n : Prop :=
  forall k, k < n ->
  contains (I.convert (Pol.tnth fi k)) (Xreal (PolR.tnth fx k)).
Definition contains_pointwise fi fx : Prop :=
  Pol.tsize fi = PolR.tsize fx /\
  contains_pointwise_until fi fx (Pol.tsize fi).

Parameter link_tmul_trunc :
  forall u fi gi fx gx,
  contains_pointwise fi fx ->
  contains_pointwise gi gx ->
  forall n : nat, n < tsize fi -> n < tsize gi ->
  contains_pointwise_until (tmul_trunc u n fi gi)
  (PolR.tmul_trunc tt n fx gx) n.+1.

Parameter link_tmul_tail :
  forall u fi gi fx gx,
  contains_pointwise fi fx ->
  contains_pointwise gi gx ->
  forall n : nat,
  contains_pointwise_until (tmul_tail u n fi gi) (PolR.tmul_tail tt n fx gx)
  ((tsize fi).-1 + (tsize gi).-1 - n).

End LinkIntR.

Module RigPolyApproxInt (I : IntervalOps) (P : IntPolyOps I).
Include RigPolyApprox I P.Int P.
End RigPolyApproxInt.

Module Type FloatPolyOps (F : FloatOps with Definition even_radix := true).
Module Fl := MaskBaseF F.
Include PolyOps Fl.
End FloatPolyOps.

Module Type FloatMonomPolyOps (F : FloatOps with Definition even_radix := true).
Module Fl := MaskBaseF F.
Include MonomPolyOps Fl.
End FloatMonomPolyOps.
