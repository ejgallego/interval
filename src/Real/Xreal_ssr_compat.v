(**
This file is part of the CoqApprox formalization of rigorous
polynomial approximation in Coq:
http://tamadi.gforge.inria.fr/CoqApprox/

Copyright (C) 2010-2012, ENS de Lyon.
Copyright (C) 2010-2016, Inria.
Copyright (C) 2014-2016, IRIT.

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

From Coq Require Import Reals Psatz.
From mathcomp.ssreflect Require Import ssreflect ssrbool ssrnat bigop.

Require Import Aux.
Require Import Xreal.
Require Import Rstruct.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Delimit Scope ring_scope with Ri.
Delimit Scope XR_scope with XR.

Local Open Scope XR_scope.

Notation "x + y" := (Xadd x y) : XR_scope.
Notation "x - y" := (Xsub x y) : XR_scope.
Notation " - y" := (Xneg y) : XR_scope.
Notation "x * y" := (Xmul x y) : XR_scope.
Notation "x / y" := (Xdiv x y) : XR_scope.

Lemma sum_f_to_big n (f : nat -> R) :
  sum_f_R0 f n = \big[Rplus/0%R]_(0 <= i < n.+1) f i.
Proof.
elim: n =>[|n IHn]; first by rewrite big_nat_recl // big_mkord big_ord0 Rplus_0_r.
by rewrite big_nat_recr //= IHn.
Qed.
