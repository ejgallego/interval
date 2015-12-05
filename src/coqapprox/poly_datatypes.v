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
Require Import NaryFunctions.
Require Import Flocq.Core.Fcore.
Require Import Interval_interval.
Require Import Interval_xreal.
Require Import Interval_definitions.
Require Import Interval_specific_ops.
Require Import Interval_float_sig.
Require Import Interval_interval_float.
Require Import Interval_interval_float_full.
Require Import Ssreflect.ssreflect Ssreflect.ssrfun Ssreflect.ssrbool Ssreflect.eqtype Ssreflect.ssrnat Ssreflect.seq Ssreflect.fintype MathComp.bigop.
Require Import nary_tuple.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Type BaseOps.
Parameter U : Type.
Parameter T : Type.

Parameter Inline tzero : T.
Parameter Inline tone : T.
Parameter Inline topp : T -> T.
Parameter Inline tadd : U -> T -> T -> T.
Parameter Inline tsub : U -> T -> T -> T.
Parameter Inline tmul : U -> T -> T -> T.
End BaseOps.

(* REM: We may use the new notation features of Coq 8.4 w.r.t. modules.

Delimit Scope base_scope with B.
Module Nota (Import A : BaseOps).
Infix "+" := tadd : base_scope.
Infix "*" := tmul : base_scope.
Infix "-" := tsub : base_scope.
Notation "- x" := (topp x) : base_scope.
Notation "1" := tone : base_scope.
Notation "0" := tzero : base_scope.
End Nota.
*)

Module Type SliceMaskBaseOps (Import A : BaseOps).
Parameter Inline tcst : T -> T -> T. (** the first argument is the constant *)
Parameter Inline tnat : nat -> T.
Parameter Inline tfromZ : Z -> T.
End SliceMaskBaseOps.

Module Type SlicePowDivOps (Import A : BaseOps).
Parameter Inline tpower_int : U -> T -> Z -> T.
Parameter Inline tsqr : U -> T -> T.
Parameter Inline tinv : U -> T -> T.
Parameter Inline tdiv : U -> T -> T -> T.
End SlicePowDivOps.

(* Local Notation tpow prec x n := (tpower_int prec x (Z_of_nat n)). *)

Module Type SliceFullOps (Import A : BaseOps).
Parameter Inline tsqrt : U -> T -> T.
Parameter Inline tinvsqrt : U -> T -> T.
Parameter Inline texp : U -> T -> T.
Parameter Inline tsin : U -> T -> T.
Parameter Inline tcos : U -> T -> T.
Parameter Inline tln : U -> T -> T.
Parameter Inline tatan : U -> T -> T.
Parameter Inline ttan : U -> T -> T.
(*
Parameter Inline tasin : U -> T -> T.
Parameter Inline tacos : U -> T -> T.
*)
End SliceFullOps.

Module Type MaskBaseOps := BaseOps <+ SliceMaskBaseOps.
Module Type PowDivOps := MaskBaseOps <+ SlicePowDivOps.
Module Type FullOps := PowDivOps <+ SliceFullOps.

Module Type BaseOps0 := BaseOps with Definition U := unit.
Module Type MaskBaseOps0 := MaskBaseOps with Definition U := unit.
Module Type PowDivOps0 := PowDivOps with Definition U := unit.
Module Type FullOps0 := FullOps with Definition U := unit.

Module Type SliceExactBaseOps (Import A : BaseOps0).
(* Parameter big_distrr_spec :
  forall n F a, n <> 0 -> tmul tt a (\big[tadd tt/tzero]_(i < n) F i) =
  \big[tadd tt/tzero]_(i < n) tmul tt a (F i). *)
Parameter tadd_zerol : left_id tzero (tadd tt).
Parameter tadd_zeror : right_id tzero (tadd tt).
Parameter tadd_comm : commutative (tadd tt).
Parameter tadd_assoc : associative (tadd tt).
Parameter tmul_onel : left_id tone (tmul tt).
Parameter tmul_oner : right_id tone (tmul tt).
Parameter tmul_comm : commutative (tmul tt).
Parameter tmul_assoc : associative (tmul tt).
Parameter tmul_distrl : left_distributive (tmul tt) (tadd tt).
Parameter tmul_distrr : right_distributive (tmul tt) (tadd tt).
Parameter tmul_zerol : left_zero tzero (tmul tt).
Parameter tmul_zeror : right_zero tzero (tmul tt).
End SliceExactBaseOps.

(*
Module Type SliceStdZOps (Import A : BaseOps).
Parameter tfromZ : Z -> T.
End SliceStdZOps.
Module Type BaseStdZOps := BaseOps <+ SliceStdZOps.
Module Type BaseStdZOps0 := BaseStdZOps with Definition U := unit.
*)

Module Type SliceExactMaskBaseOps (Import A : MaskBaseOps0).
(*
Parameter mask_add_l :
  forall a b x, tcst (tadd tt a b) x = tadd tt (tcst a x) b.
Parameter mask_add_r :
  forall a b x, tcst (tadd tt a b) x = tadd tt a (tcst b x).
Parameter mask_mul_l :
  forall a b x, tcst (tmul tt a b) x = tmul tt (tcst a x) b.
Parameter mask_mul_r :
  forall a b x, tcst (tmul tt a b) x = tmul tt a (tcst b x).
Parameter mask0mul_l :
  forall x, tmul tt tzero x = tcst tzero x.
Parameter mask0mul_r :
  forall x, tmul tt x tzero = tcst tzero x.
Parameter mask_idemp :
  forall a x, tcst (tcst a x) x = tcst a x.
Parameter mask_comm :
  (* useless, but just in case *)
  forall a x y, tcst (tcst a x) y = tcst (tcst a y) x.
*)
Parameter cstE : forall c x, tcst c x = c.
End SliceExactMaskBaseOps.

Module Type SliceExactPowDivOps (Import A : PowDivOps0).
Local Notation tpow prec x n := (tpower_int prec x (Z_of_nat n)).
Parameter tpow_0 : forall x, tpow tt x 0 = tone.
Parameter tpow_S : forall x n, tpow tt x n.+1 = tmul tt x (tpow tt x n).
Parameter tpow_opp :
  forall x n, x <> tzero -> tpower_int tt x (-n) = tinv tt (tpower_int tt x n).
End SliceExactPowDivOps.

Module Type ExactFullOps :=
 FullOps0 <+ SliceExactBaseOps <+ SliceExactMaskBaseOps <+ SliceExactPowDivOps.

Module Type PolyOps (C : BaseOps) <: BaseOps.
Include Type BaseOps with Definition U := C.U. (* simplifying assumption *)
Parameter tmul_trunc : U -> nat -> T -> T -> T.
Parameter tmul_tail : U -> nat -> T -> T -> T.
Parameter tlift : nat -> T -> T.
(** [tlift j pol] represents [pol * X^j] if [pol] is in the monomial basis *)
Parameter ttail : nat -> T -> T.
(* Parameter tpolyX : T. (Subsumed by [tpolyNil] and [tpolyCons].) *)
Parameter tpolyNil : T.
Parameter tpolyCons : C.T -> T -> T.
Parameter teval : U -> T -> C.T -> C.T.
(* REMARK: we could add a [degree] field, but in our particular
context (Taylor modesl with seq-based polynomials), we especially
focus on sizes. *)
Parameter tnth : T -> nat -> C.T.
Parameter tsize : T -> nat.

Parameter trec1 : (C.T -> nat -> C.T) -> C.T -> nat -> T.
Parameter trec1_spec0 :
  forall (F : C.T -> nat -> C.T) F0 n,
  tnth (trec1 F F0 n) 0 = F0.
Parameter trec1_spec :
  forall (F : C.T -> nat -> C.T) F0 p k, k < p ->
  tnth (trec1 F F0 p) k.+1 = F (tnth (trec1 F F0 k) k) k.+1.

Parameter trec2 : (C.T -> C.T -> nat -> C.T) -> C.T -> C.T -> nat -> T.
Parameter trec2_spec0 :
  forall (F : C.T -> C.T -> nat -> C.T) F0 F1 n,
  tnth (trec2 F F0 F1 n) 0 = F0.
Parameter trec2_spec1 :
  forall (F : C.T -> C.T -> nat -> C.T) F0 F1 n,
  tnth (trec2 F F0 F1 n.+1) 1 = F1.
Parameter trec2_spec :
  forall (F : C.T -> C.T -> nat -> C.T) F0 F1 p k, k.+1 < p ->
  tnth (trec2 F F0 F1 p) k.+2 =
  F (tnth (trec2 F F0 F1 k) k) (tnth (trec2 F F0 F1 k.+1) k.+1) k.+2.

Parameter trecN :
  forall N : nat, C.T ^ N -> C.T ^^ N --> (nat -> C.T) -> nat -> T.
Parameter trecN_spec0 :
  forall (N : nat) (L0 : C.T ^ N) (F : C.T ^^ N --> (nat -> C.T)) (n k : nat)
  (d : C.T),
  k <= n -> k < N -> tnth (trecN L0 F n) k = nth d (Ttoseq L0) k.

Parameter tgrec1 :
  forall A : Type,
  (A -> nat -> A) ->
  (A -> nat -> C.T) -> A -> seq C.T -> nat -> T.

Parameter tsize_grec1 :
  forall (A : Type)
  (F : A -> nat -> A) (G : A -> nat -> C.T) (q : A) (s : seq C.T) (n : nat),
  tsize (tgrec1 F G q s n) = n.+1.

Parameter tlastN : C.T -> forall N : nat, T -> C.T ^ N.
Parameter tlastN_spec :
  forall (d := C.tzero) N (p : T) (i : 'I_N),
  Tnth (tlastN d N p) i = tnth p (tsize p - N + val i).

Parameter trecN_spec :
  forall (N : nat) (L0 : C.T ^ N) (F : C.T ^^ N --> (nat -> C.T)) (n k : nat)
         (d : C.T),
  k <= n -> k >= N ->
  tnth (trecN L0 F n) k =
  (nuncurry F) (tlastN d N (trecN L0 F k.-1)) k.
Parameter tsize_trecN :
  forall (N : nat) (L0 : C.T ^ N) (F : C.T ^^ N --> (nat -> C.T)) (n k : nat)
         (d : C.T),
  tsize (trecN L0 F n) = n.+1.

Parameter tfold : forall V : Type, (C.T -> V -> V) -> V -> T -> V.
Parameter tset_nth : T -> nat -> C.T -> T.
(* Erik: We do not define
[Parameter tmap : forall f : C.T -> C.T, T -> T.]
as its specification would require [f C.tzero = C.tzero],
which does not hold in general.
Yet we can use a foldr-based mapping instead. *)
Parameter tsize_trec1 : forall F x n, tsize (trec1 F x n) = n.+1.
Parameter tsize_trec2 : forall F x y n, tsize (trec2 F x y n) = n.+1.
Parameter tsize_mul_trunc : forall u n p q, tsize (tmul_trunc u n p q) = n.+1.
Parameter tsize_mul_tail :
  forall u n p q, tsize (tmul_tail u n p q) = ((tsize p).-1 + (tsize q).-1 - n).
(* Beyond this size lemma, [tmul_tail] will be specified in rpa_inst.LinkIntX *)
Parameter tsize_tadd :
  forall u p1 p2,
  tsize (tadd u p1 p2) = maxn (tsize p1) (tsize p2).
Parameter tnth_tadd :
  forall u p1 p2 k, k < minn (tsize p1) (tsize p2) ->
  tnth (tadd u p1 p2) k = C.tadd u (tnth p1 k) (tnth p2 k).
Parameter tsize_sub :
  forall u p1 p2,
  tsize (tsub u p1 p2) = maxn (tsize p1) (tsize p2).
Parameter tnth_sub :
  forall u p1 p2 k, k < minn (tsize p1) (tsize p2) ->
  tnth (tsub u p1 p2) k = C.tsub u (tnth p1 k) (tnth p2 k).
Parameter tsize_opp :
  forall p1,
  tsize (topp p1) = tsize p1.
Parameter tnth_opp :
  forall p1 k, k < tsize p1 ->
  tnth (topp p1) k = C.topp (tnth p1 k).
Parameter tsize_polyCons : forall a p, tsize (tpolyCons a p) = (tsize p).+1.
Parameter tnth_polyCons : forall a p k, k <= tsize p ->
  tnth (tpolyCons a p) k = if k is k'.+1 then tnth p k' else a.
Parameter tnth_polyNil : forall n, tnth tpolyNil n = C.tzero.
Parameter tnth_out : forall p n, tsize p <= n -> tnth p n = C.tzero.
(** Note that we explicitely choose a default value here *)
Parameter tsize_polyNil : tsize tpolyNil = 0.
Parameter tsize_set_nth : forall p n val,
  tsize (tset_nth p n val) = maxn n.+1 (tsize p).
(* i.e., tsize (tset_nth p n val) = maxn n.+1 (tsize p) = tsize p. *)
Parameter tnth_set_nth : forall p n val k,
  tnth (tset_nth p n val) k = if k == n then val else tnth p k.
Parameter tfold_polyNil : forall U f iv, @tfold U f iv tpolyNil = iv.
Parameter tfold_polyCons : forall U f iv c p,
  @tfold U f iv (tpolyCons c p) = f c (@tfold U f iv p).
Parameter tpoly_ind : forall (f : T -> Type),
  f tpolyNil ->
  (forall a p, f p -> f (tpolyCons a p)) ->
  forall p, f p.
Parameter tsize_tail :
  forall p k, tsize (ttail k p) = tsize p - k.
Parameter tnth_tail :
  forall p n k,
  tnth (ttail k p) n = tnth p (k + n).
Parameter tderiv : U -> T -> T.
(* Parameter tderiv_correct : ... *)
End PolyOps.

Module Type SliceMonomPolyOps (C : MaskBaseOps) (Import A : PolyOps C).
(** Horner evaluation of polynomial in monomial basis *)
Parameter teval_polyCons :
  forall u c p x,
  teval u (tpolyCons c p) x =
  C.tadd u (C.tmul u (teval u p x) x) c.
Parameter teval_polyNil :
  forall u x, teval u tpolyNil x = C.tcst C.tzero x.
End SliceMonomPolyOps.

Module Type MonomPolyOps (C : MaskBaseOps) := PolyOps C <+ SliceMonomPolyOps C.

Module Type SlicePowDivPolyOps (C : PowDivOps) (Import A : PolyOps C).
Parameter tmul_mixed : U -> C.T -> T -> T.
Parameter tdiv_mixed_r : U -> T -> C.T -> T.
Parameter tdotmuldiv : U -> seq Z -> seq Z -> T -> T.
Parameter tsize_dotmuldiv :
  forall n u a b p, tsize p = n -> size a = n -> size b = n ->
  tsize (tdotmuldiv u a b p) = n.
Parameter tnth_dotmuldiv :
  (* FIXME: Replace this spec with a parameter in rpa_inst.LinkIntX *)
  forall u a b p n, n < tsize (tdotmuldiv u a b p) ->
  tnth (tdotmuldiv u a b p) n =
  C.tmul u (C.tdiv u (C.tfromZ (nth 1%Z a n))
                     (C.tfromZ (nth 1%Z b n)))
         (tnth p n).
End SlicePowDivPolyOps.

Module Type PowDivMonomPolyOps (C : PowDivOps) :=
   MonomPolyOps C <+ SlicePowDivPolyOps C.

Module Type SliceExactMonomPolyOps
  (C : PowDivOps0)
  (Import A : PolyOps C)
  (B : SliceMonomPolyOps C A).

Local Notation Ctpow prec x n := (C.tpower_int prec x (Z_of_nat n)).

Parameter is_horner :
 forall p x, teval tt p x =
  \big[C.tadd tt/C.tzero]_(i < tsize p)
  C.tmul tt (tnth p i) (Ctpow tt x i).

Parameter tmul_trunc_nth:
forall p1 p2 n k,
 k < n.+1 ->
 tnth (tmul_trunc tt n p1 p2) k =
  \big[C.tadd tt/C.tzero]_(i < k.+1) C.tmul tt (tnth p1 i) (tnth p2 (k -i)).

Parameter tmul_tail_nth:
forall p1 p2 n k,
 k < ((tsize p1).-1 + (tsize p2).-1 - n) ->
 tnth (tmul_tail tt n p1 p2) k =
(* \big[C.tadd/C.tzero]_(i < n - k)
   C.tmul tt (tnth p1 (i + k)) (tnth p2 (n - i)). *)
 \big[C.tadd tt/C.tzero]_(i < (k+n.+1).+1)
   C.tmul tt (tnth p1 i) (tnth p2 ((k + n.+1) - i)).

End SliceExactMonomPolyOps.

(** Note that the implementations of the previous signature will rely
on the choice of a particular polynomial basis, especially for the
multiplication and polynomial evaluation. *)

Module Type ExactMonomPolyOps (C : PowDivOps0)
  := PolyOps C
  <+ SliceMonomPolyOps C <+ SlicePowDivPolyOps C <+ SliceExactMonomPolyOps C.

Module RigPolyApprox (I : IntervalOps) (C : BaseOps) (Pol : PolyOps C).

(** Rigorous Polynomial Approximation structure *)
Structure rpa : Type := RPA {
  approx : Pol.T;
  error : I.type
}.

End RigPolyApprox.
