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
Require Import NaryFunctions.
Require Import mathcomp.ssreflect.ssreflect mathcomp.ssreflect.ssrfun mathcomp.ssreflect.ssrbool mathcomp.ssreflect.eqtype mathcomp.ssreflect.ssrnat mathcomp.ssreflect.seq mathcomp.ssreflect.fintype mathcomp.ssreflect.tuple.
Require Import seq_compl.

(** This theory extends [NaryFunctions] (from Coq's standard library),
relying on an SSReflect formalization style. *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Arguments nprod_to_list [A n] _.
Arguments nuncurry [A B n] _ _.
Arguments ncurry [A B n] _.
Arguments napply_discard _ [B] _ _.

Definition Ttoseq := nprod_to_list.

Section NaryTuple.

Variables (n : nat) (T : Type).

Lemma size_Tuple (t : T ^ n) : size (Ttoseq t) = n.
Proof. by elim: n t =>[//|n' IHn] t; case: t =>[t1 t2] /=; rewrite IHn. Qed.

End NaryTuple.

(** Close section to generalize w.r.t. [n]. *)

Section NaryTuple1.

Variables (n : nat) (T : Type).

Implicit Type t : T ^ n.

Lemma Tnth_default t : 'I_n -> T.
Proof. by rewrite -(size_Tuple t); case: (Ttoseq t)=>[|//] []. Qed.

Definition Tnth t i := nth (Tnth_default t i) (Ttoseq t) i.

End NaryTuple1.

Definition cons_Tuple n T : T -> T ^ n -> T ^ n.+1 := @pair T (T ^ n).
