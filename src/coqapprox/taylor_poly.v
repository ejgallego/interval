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

Require Import BinPos.
Require Import Flocq.Core.Fcore_Raux.
Require Import Interval_xreal.
Require Import Interval_generic Interval_interval.
Require Import Interval_definitions.
Require Import Interval_specific_ops.
Require Import Interval_float_sig.
Require Import Interval_interval_float.
Require Import Interval_interval_float_full.
Require Import Ssreflect.ssreflect Ssreflect.ssrfun Ssreflect.ssrbool Ssreflect.eqtype Ssreflect.ssrnat Ssreflect.seq Ssreflect.fintype MathComp.bigop.
Require Import poly_datatypes basic_rec.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module TaylorRec (Import C : FullOps).

Section PrecIsPropagated.
Variable u : U.

Definition cst_rec (x : C.T) (n : nat) := C.tcst C.tzero x.

Definition var_rec (a b : C.T) (n : nat) := C.tcst (C.tcst C.tzero a) b.

Definition inv_rec (x : T) (a : T) (n : nat) : T := tdiv u a (topp x).

Definition exp_rec (a : T) (n : nat) : T := tdiv u a (tnat n).

Definition sin_rec (a b : T) (n : nat) : T :=
  tdiv u (topp a) (tmul u (tnat n) (tnat n.-1)).

Definition cos_rec (a b : T) (n : nat) : T :=
  tdiv u (topp a) (tmul u (tnat n) (tnat n.-1)).

Definition pow_aux_rec (p : Z) (x : T) (_ : T) (n : nat)
  := if Z.ltb p Z0 || Z.geb p (Z.of_nat n) then
        C.tpower_int u x (p - Z.of_nat n)%Z
     else C.tcst C.tzero x.

(* Erik: These notations could be used globally *)
Local Notation "i + j" := (tadd u i j).
Local Notation "i - j" := (tsub u i j).
Local Notation "i * j" := (tmul u i j).
Local Notation "i / j" := (tdiv u i j).

Definition sqrt_rec (x : T) (a : T) (n : nat) :=
  let nn := tnat n in
  let n1 := tnat n.-1 in
  let one := tnat 1 in
  let two := tnat 2 in
  (one - two * n1) * a / (two * x * nn).

Definition invsqrt_rec (x : T) (a : T) (n : nat) :=
  let nn := tnat n in
  let n1 := tnat n.-1 in
  let one := tnat 1 in
  let two := tnat 2 in
  topp (one + two * n1) * a / (two * x * nn).

(*
Definition ln_rec (x : T) (a b : T) (n : nat) :=
  let nn := tnat n in
  let n1 := tnat n.-1 in
  let n2 := tnat n.-2 in
  topp (n1 * b) / (nn * x).

Definition Deriv_atan J := tinv u (tnat 1 + (tsqr u J)).

(* (2*loc0+2*a*loc1-(loc0+2*a*loc1)*(i1+1))/((1+a^2)*(i1+1)) *)
Definition atan_rec (x0 : T) (a b : T) (np2 : nat) :=
  let n := tnat (np2.-2) in
  let one := tnat 1 in
  let two := tnat 2 in
(*(two*loc0+two*a*loc1-(loc0+two*a*loc1)*(nn))/((one+a*a)*(nn)). (*OLD*)*)
topp ((n*a+two*b*x0*n+two*b*x0) / (n+n*(tsqr u x0)+two+two*(tsqr u x0))).
(* topp ((nn*u+two*v*a*nn+two*v*a)/((one+(tsqr a))*(nn+two)). (*TESTER*)*)

Definition Deriv_asin (x : T) := (tinvsqrt u (tnat 1 - tsqr u x)).

(* -(u(n+1)*(n+1)*(1+2*n)*z0+n^2*u(n))/((n+1)*(n+2)*z0^2-(n+1)*(n+2)) *)
Definition asin_rec (x : T) (a b : T) (n : nat) :=
  let nn := tnat n in
  let n1 := tnat n.-1 in
  let n2 := tnat n.-2 in
  let one := tnat 1 in
  let two := tnat 2 in
  (b*(n1)*(one+two*n2)*x+n2*n2*a)/((n1)*(nn)*(one-tsqr u x)).

Definition Deriv_acos x := (* Eval unfold Deriv_asin in *)
  topp (Deriv_asin x).

Definition acos_rec := asin_rec. (* acos & asin satisfy the same diffeq *)
*)

End PrecIsPropagated.
End TaylorRec.

Module Type TaylorPolyOps (C : FullOps) (P : PolyOps C).

Parameter T_cst : C.T -> C.T -> nat -> P.T.
(** Note that in addition to the Taylor expansion point that is
the 2nd parameter of T_cst, the first one is the value of
the constant itself. *)

Parameter T_var : C.T -> nat -> P.T.

Parameter T_inv : P.U -> C.T -> nat -> P.T.

Parameter T_exp : P.U -> C.T -> nat -> P.T.

Parameter T_sin : P.U -> C.T -> nat -> P.T.

Parameter T_cos : P.U -> C.T -> nat -> P.T.

Parameter T_sqrt : P.U -> C.T -> nat -> P.T.

Parameter T_invsqrt : P.U -> C.T -> nat -> P.T.

(*
Parameter T_ln : P.U -> C.T -> nat -> P.T.
Parameter T_atan : P.U -> C.T -> nat -> P.T.
Parameter T_asin : P.U -> C.T -> nat -> P.T.
Parameter T_acos : P.U -> C.T -> nat -> P.T.
*)
End TaylorPolyOps.

Module TaylorPoly (C : FullOps) (P : PowDivMonomPolyOps C) <: TaylorPolyOps C P.
(** Needs functions defining the recurrences, as well as trec1, trec2. *)
Module Rec := TaylorRec C.
Import P C Rec.

Definition T_cst c (x : C.T) := trec1 cst_rec (tcst c x).

Definition T_var x := trec2 var_rec x (tcst C.tone x).

Section PrecIsPropagated.
Variable u : P.U.

Definition T_inv x := trec1 (inv_rec u x) (tinv u x).

Definition T_exp x := trec1 (exp_rec u) (texp u x).

Definition T_sin x := trec2 (sin_rec u) (tsin u x) (tcos u x).

Definition T_cos x := trec2 (cos_rec u) (tcos u x) (C.topp (tsin u x)).

Definition T_sqrt x := trec1 (sqrt_rec u x) (tsqrt u x).

Definition T_invsqrt x := trec1 (invsqrt_rec u x) (tinvsqrt u x).

Definition T_power_int (p : Z) x (n : nat) :=
  P.tdotmuldiv u (falling_seq p n) (fact_seq n)
               (trec1 (pow_aux_rec u p x) (tpower_int u x p) n).

Definition T_ln x n :=
  let lg := tln u x in
  let y := C.tcst x lg in
  P.tpolyCons lg
  (if n is n'.+1 then
     let p1 := (-1)%Z in
     P.tdotmuldiv u (falling_seq p1 n') (behead (fact_seq n))
                  (trec1 (pow_aux_rec u p1 y) (tpower_int u y p1) n')
   else P.tpolyNil).

(*
Definition T_ln x := trec2 (ln_rec u x) (tln u x) (tinv u x).
Definition T_atan x := trec2 (atan_rec u x) (tatan u x) (Deriv_atan u x).
Definition T_asin x := trec2 (asin_rec u x) (tasin u x) (Deriv_asin u x).
Definition T_acos x := trec2 (acos_rec u x) (tacos u x) (Deriv_acos u x).
*)
End PrecIsPropagated.
End TaylorPoly.
