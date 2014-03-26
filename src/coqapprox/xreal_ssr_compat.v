(**
This file is part of the CoqApprox formalization of rigorous
polynomial approximation in Coq:
http://tamadi.gforge.inria.fr/CoqApprox/

Copyright (c) 2010-2013, ENS de Lyon and Inria.

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
Require Import Psatz.
Require Import taylor_thm.
Require Import Interval_missing.
Require Import Interval_xreal.
Require Import Interval_xreal_derive.
Require Import Interval_interval.
Require Import Interval_generic_proof.
Require Import Rstruct.
Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
Require Import div fintype finfun path bigop.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Delimit Scope ring_scope with Ri.
Delimit Scope R_scope with Re.
Delimit Scope XR_scope with XR.

Local Open Scope XR_scope.

Notation "x + y" := (Xadd x y) : XR_scope.
Notation "x - y" := (Xsub x y) : XR_scope.
Notation " - y" := (Xneg y) : XR_scope.
Notation "x * y" := (Xmul x y) : XR_scope.
Notation "x / y" := (Xdiv x y) : XR_scope.

Definition Xpow x n := Xpower_int x (Z_of_nat n).

Notation "x ^ n" := (Xpow x n) : XR_scope.

Arguments Xpow x n : simpl nomatch.

(* Erik: Xpow_iter, Xpow_idem, Xpow_Xreal, Xpow_Xnan may be removed
  in favor of fun x n => Xpower_int x (Z_of_nat n), cf. FullXR.tpow *)

Implicit Types n k : nat.
Implicit Type r : R.
Implicit Types x y : ExtendedR.
Implicit Type X : interval.

Definition Xpow_iter x n := iter_nat n _ (Xmul x) (Xmask (Xreal 1) x).

(* "Transitional result" (may be removed in a later version) *)
Lemma Xpow_idem x n : Xpow x n = Xpow_iter x n.
Proof.
elim: n =>[//|n IHn].
rewrite /Xpow_iter /= -/(Xpow_iter x n) -IHn.
case: {IHn} x =>//= r.
(* and similarly to the proof of FullXR.tpow_S *)
case: n =>// n.
by congr Xreal; rewrite tech_pow_Rmult; congr pow; rewrite Pos2Nat.inj_succ.
Qed.

Lemma Xpow_Xreal r n : Xpow_iter (Xreal r) n = Xreal (pow r n).
Proof.
by elim: n=>// n; rewrite /Xpow_iter => /= ->.
Qed.

Lemma Xpow_Xnan n : Xpow_iter Xnan n = Xnan.
Proof. by case: n. Qed.

Lemma Xmul_Xreal a b : Xreal a * Xreal b = Xreal (a * b).
Proof. by []. Qed.

Lemma zeroF r : (r <> 0)%Re -> is_zero r = false.
Proof.
rewrite /is_zero /Req_bool; case E: (Rcompare r 0) =>//.
by rewrite (Rcompare_Eq_inv _ _ E).
Qed.

Lemma zeroT r : (r = 0)%Re -> is_zero r = true.
Proof. by move ->; rewrite is_zero_correct_zero. Qed.

Lemma fact_zeroF i : is_zero (INR (fact i)) = false.
Proof. by apply: zeroF=> Hri; apply: (fact_neq_0 i); apply: INR_eq. Qed.

Lemma XReq_EM_T : forall r1 r2:ExtendedR, {r1 = r2} + {r1 <> r2}.
Proof.
case=>[|r1] []; [left|move=> ?; right|right|move=> r2] =>//.
case: (Req_EM_T r1 r2); first by move ->; left.
by move=> Hr; right=> HX; apply: Hr; case: HX.
Qed.

Definition eqX x1 x2 : bool :=
  match XReq_EM_T x1 x2 with
    | left _ => true
    | right _ => false
  end.

Lemma eqXP : Equality.axiom eqX.
Proof.
move=> x1 x2; apply: (iffP idP) => [|<-].
  by rewrite /eqX; case: XReq_EM_T.
by rewrite /eqX; case: XReq_EM_T.
Qed.

Canonical Structure Xreal_eqMixin := EqMixin eqXP.
Canonical Structure Xreal_eqType := Eval hnf in
  EqType ExtendedR Xreal_eqMixin.

Lemma Xreal_irrelevance (x y : ExtendedR) (E E' : x = y) : E = E'.
Proof. exact: eq_irrelevance. Qed.

Lemma XaddA : associative Xadd.
Proof. by move=> *; rewrite Xadd_assoc. Qed.

Lemma XaddC : commutative Xadd.
Proof. by move=> *; rewrite Xadd_comm. Qed.

Lemma Xadd0 : left_id (Xreal 0%Re) Xadd.
Proof. by case=> // r; rewrite /= Rplus_0_l. Qed.

Lemma X0add : right_id (Xreal 0%Re) Xadd.
Proof. by case=> // r; rewrite /= Rplus_0_r. Qed.

Lemma XmulA : associative Xmul.
Proof. by move=> *; rewrite Xmul_assoc. Qed.

Lemma Xmul0 : left_id (Xreal 1%Re) Xmul.
Proof. by case=> // r; rewrite /= Rmult_1_l. Qed.

Lemma X0mul : right_id (Xreal 1%Re) Xmul.
Proof. by case=> // r; rewrite /= Rmult_1_r. Qed.

Lemma left_distr_Xmul_Xadd : left_distributive Xmul Xadd.
Proof. by case=> [|rx]; case=> [|ry]; case=> [|rz] //=; congr Xreal; ring. Qed.

Lemma right_distr_Rmult_Rplus : right_distributive Xmul Xadd.
Proof. by case=> [|rx]; case=> [|ry]; case=> [|rz] //=; congr Xreal; ring. Qed.

Lemma XmulC : commutative Xmul.
Proof. by move=> *; rewrite Xmul_comm. Qed.

Import Monoid.
Canonical Xadd_monoid := Law XaddA Xadd0 X0add.
Canonical Xadd_comoid := ComLaw XaddC.

Canonical Xmul_monoid := Law XmulA Xmul0 X0mul.
Canonical Xmul_comoid := ComLaw XmulC.

Lemma ordinal1 : all_equal_to (ord0 : 'I_1).
Proof. by case=> m Hm; apply: ord_inj; apply/eqP; rewrite -leqn0. Qed.

Local Open Scope XR_scope.

Lemma Xderive_pt_Xpow n (f : ExtendedR -> ExtendedR) (f' x : ExtendedR) :
  Xderive_pt f x f' ->
  Xderive_pt (fun x0 : ExtendedR => (f x0) ^ n) x
 ((Xreal (INR n)) * (f x) ^ n.-1 * f').
Proof.
move=> Hf; xtotal.
  by move: X0; rewrite Xpow_idem Xpow_Xreal.
move=> v.
apply (derivable_pt_lim_eq_locally
  (Ranalysis1.comp ((fun n r => pow r n) n) (proj_fun v f))).
  apply: locally_true_imp (derivable_imp_defined_any _ _ _ _ X Hf).
  move=> x [w Hw].
  by rewrite /Ranalysis1.comp /proj_fun Hw Xpow_idem Xpow_Xreal.
apply: derivable_pt_lim_comp=>//; rewrite /proj_fun X.
have Heq : (r1 ^ Peano.pred n = r4)%Re.
  by rewrite Xpow_idem Xpow_Xreal in X2; case: X2 =><-.
by rewrite -Heq; apply: (derivable_pt_lim_pow r1 n).
Qed.

Lemma Xderive_pt_mulXmask r x :
  Xderive_pt
  (fun x0 => ((Xreal r) * Xmask (Xreal 1) x0)%XR) x
  (Xmask (Xreal 0) x).
Proof.
case Cx: x => [|rx] //.
rewrite /Xderive_pt /(Xmask (Xreal 0)) /= => v.
by rewrite /proj_fun /=; apply: derivable_pt_lim_const.
Qed.

(* Erik: This lemma should not be used, put all lemmas in Xreal form instead *)
Lemma not_Xnan_Xreal_fun T F :
  (forall i : T, F i <> Xnan) ->
  exists g, forall i : T, F i = Xreal (g i).
Proof.
move=> HF.
exists (fun (i : T) => match (F i) with | Xnan => R0 | Xreal ri => ri end).
move=> i.
by case: (F i) (HF i).
Qed.

Lemma bigXadd_Xreal_proj n (F : 'I_n -> ExtendedR) :
  (forall i, F i <> Xnan) ->
  \big[Xadd/Xreal 0]_(i < n) F i =
  Xreal (\big[Rplus/R0]_(i < n) proj_val (F i)).
Proof.
elim: n F =>[|n IHn] F HF; first by rewrite 2!big_ord0.
rewrite 2!big_ord_recr IHn //=.
suff->: F ord_max = Xreal (proj_val (F ord_max)) by [].
case E: (F ord_max) HF =>//.
by move/(_ ord_max); rewrite E.
Qed.

Lemma bigXadd_Xnan n (F : 'I_n -> ExtendedR) :
  \big[Xadd/Xreal 0]_(i < n) F i = Xnan ->
  exists i, F i = Xnan.
Proof.
elim: n F; first by move=>F; rewrite big_ord0.
move=> n IHn F; rewrite big_ord_recr /=.
case E: (\big[Xadd/Xreal 0]_(i < n) F (widen_ord (leqnSn n) i)) =>[|br] /=.
  elim: (IHn _ E) => i Hi _.
  by exists (widen_ord (leqnSn n) i).
case EF: (F ord_max) =>[|cr] =>// _.
by exists ord_max.
Qed.

Lemma bigXadd_Xnan_i n (F : 'I_n -> ExtendedR) i :
  F i = Xnan -> \big[Xadd/Xreal 0]_(i < n) F i = Xnan.
Proof. by rewrite (bigD1 i)=> // ->. Qed.

Lemma bigXadd_Xreal n (F : 'I_n -> ExtendedR) sx:
  \big[Xadd/Xreal 0]_(i < n) F i = Xreal sx ->
  forall i, exists gi, F i = Xreal (gi).
Proof.
move=> Hxreal i; case Cf: (F i) Hxreal => [|ri].
  by rewrite (bigXadd_Xnan_i Cf).
by exists ri.
Qed.

Lemma bigXadd_Xreal1 n (F : 'I_n -> ExtendedR) r :
  \big[Xadd/Xreal 0]_(i < n) F i = Xreal r ->
  exists g : 'I_n -> R, forall i, F i = Xreal (g i).
Proof.
move=> Hxreal; apply: not_Xnan_Xreal_fun => i.
case C: (F i) Hxreal =>//.
by rewrite (bigXadd_Xnan_i C).
Qed.

Lemma bigXadd_Xreal_i n (g : 'I_n -> R) :
  \big[Xadd/Xreal 0]_(i < n) Xreal (g i) =
  Xreal (\big[Rplus/R0]_(i < n) g i).
Proof.
elim: n g =>[g|n IHn g]; first by rewrite 2!big_ord0.
by rewrite 2!big_ord_recr IHn.
Qed.

Lemma sum_f_to_big n (f : nat -> R) :
  sum_f_R0 f n = \big[Rplus/R0]_(i < n.+1) f i.
Proof.
elim: n =>[|n IHn]; first by rewrite big_ord_recl big_ord0 Rplus_0_r.
by rewrite big_ord_recr /= IHn.
Qed.

Lemma big_Xmul_Xadd_distr n (f : 'I_n -> ExtendedR) r :
  ((\big[Xadd/Xreal 0]_(i < n) f i) * (Xreal r)
  = \big[Xadd/Xreal 0]_(i < n) (f i * (Xreal r)))%XR.
Proof.
elim: n f =>[f| n IHn f]; first by rewrite !big_ord0 /= Rmult_0_l.
by rewrite !big_ord_recl -(IHn _) Xmul_Xadd_distr_r.
Qed.

Lemma contains_Xnan (X : interval) :
  contains X Xnan -> X = Interval_interval.Inan.
Proof. by case: X. Qed.

Lemma Xsub_Xadd_distr (a b c : ExtendedR) : (a - (b + c) = a - b - c)%XR.
Proof. by case: a; case: b; case: c =>// a b c /=; congr Xreal; ring. Qed.

Lemma Xinv_1 : Xinv (Xreal 1%Re)= Xreal 1%Re.
Proof. by rewrite /= zeroF ?Rinv_1 //; apply: R1_neq_R0. Qed.

Section NDerive.
Variable XD : nat -> ExtendedR -> ExtendedR.
Variable X : interval.
Variable n : nat.
Let dom r := contains X (Xreal r).
Let Hdom : connected dom. Proof (contains_connected _).

Hypothesis Hder : forall n, Xderive (XD n) (XD (S n)).

Hypothesis Hdif : forall r k, (k <= n.+1)%N -> dom r -> XD k (Xreal r) <> Xnan.

Hypothesis XD0_Xnan : XD 0%N Xnan = Xnan.

Lemma XD_Xnan_propagate x (k m : nat) :
  (k <= m)%N -> XD k x = Xnan -> XD m x = Xnan.
Proof.
move=> Hkm Hk; elim: m Hkm =>[Hk0 | m IHm].
 by move: Hk0 Hk; rewrite leqn0; move/eqP ->.
case: (leqP k m) =>[Hkm _| Hkm H1].
  move:(IHm Hkm) (Hder m x); rewrite /Xderive_pt => {IHm} {Hk}.
  case: x => [|x].
    by case: (XD m.+1 (Xnan)).
  case: (XD m.+1 (Xreal x)) =>//.
  by case: (XD m (Xreal x)).
suff->: m.+1 = k by [].
 by apply: anti_leq; apply/andP.
Qed.

Lemma XD_Xreal k r :
  (k <= n.+1)%N -> dom r ->
  XD k (Xreal r) = Xreal (proj_val (XD k (Xreal r))).
Proof.
by move=> Hk Hx; case E: (XD k (Xreal r)) =>[|//]; case: (Hdif Hk Hx).
Qed.

Theorem Rneq_lt r1 r2 : r1 <> r2 -> (r1 < r2 \/ r2 < r1)%Re.
Proof. by move=> H; elim: (Rtotal_order r1 r2)=>[a|[b|c]];[left|done|right]. Qed.

Lemma Xderive_propagate (f f' : ExtendedR -> ExtendedR) x :
  Xderive f f' -> f x = Xnan -> f' x = Xnan.
Proof.
rewrite /Xderive /Xderive_pt.
move/(_ x); case: x => [|r]; first by case: (f' Xnan).
by move=> H Hnan; move: H; rewrite Hnan; case: (f' (Xreal r)).
Qed.

Lemma Xderive_propagate' (f f' : ExtendedR -> ExtendedR) :
  Xderive f f' -> f' Xnan = Xnan.
Proof. by rewrite /Xderive /Xderive_pt; move/(_ Xnan); case: (f' Xnan). Qed.

Lemma bigXadd_bigRplus (r s : R) :
  dom r ->
  let xi0 := Xreal r in
  \big[Xadd/Xreal 0]_(i < n.+1)
    ((XD i xi0) / Xreal (INR (fact i)) * Xreal s ^ i)%XR =
  Xreal (\big[Rplus/R0]_(i < n.+1)
    (proj_val (XD i xi0) / (INR (fact i)) * s ^ i)%Re).
Proof.
move=> Hxi0 xi0.
elim/big_ind2: _ =>[//|x1 x2 y1 y2 Hx Hy|i _]; [by rewrite Hx // Hy|].
rewrite XD_Xreal //; last by apply: ltnW; case: i.
rewrite [Xdiv _ _]/= zeroF; last exact: INR_fact_neq_0.
by rewrite Xpow_idem Xpow_Xreal.
Qed.

Lemma Xsub_Xreal_l x y :
  Xsub x y <> Xnan -> x = Xreal (proj_val x).
Proof. by case: x. Qed.

Lemma Xsub_Xreal_r x y :
  Xsub x y <> Xnan -> y = Xreal (proj_val y).
Proof. by case: x; case: y. Qed.

Lemma Xsub_Xnan_r x :
  Xsub x Xnan = Xnan.
Proof. by case: x. Qed.

Theorem XTaylor_Lagrange x0 x :
  contains X x0 ->
  contains X x ->
  exists xi : R,
  contains X (Xreal xi) /\
  (XD 0 x - (\big[Xadd/Xreal 0]_(i < n.+1)
    (XD i x0 / Xreal (INR (fact i)) * (x - x0)^i)))%XR =
  (XD n.+1 (Xreal xi) / Xreal (INR (fact n.+1)) * (x - x0) ^ n.+1)%XR /\
  (contains (Interval_interval.Ibnd x x0) (Xreal xi) \/
   contains (Interval_interval.Ibnd x0 x) (Xreal xi)).
Proof.
move=> Hx0 Hx.
case: x0 Hx0.
  case: X =>[|//] HX.
  exists R0; split=>//; split.
    rewrite !Xsub_Xnan_r Xmul_comm.
    by rewrite big_ord_recr /= Xmul_comm Xadd_comm Xsub_Xnan_r.
  case: x Hx => [|x]; first by left.
  by case: (Rcompare_spec x R0)=> /=; auto with real.
case: x Hx.
  case:X =>// HX.
  exists R0; split =>//; rewrite XD0_Xnan; split; first by rewrite Xmul_comm.
  by case: (Rcompare_spec r R0)=> /=; auto with real.
move=> rx Hrx rx0 Hrx0; case (Req_dec rx0 rx)=> [->|Hneq].
  exists rx; split =>//=; split;[| auto with real].
  rewrite Rminus_diag_eq // pow_ne_zero; last by rewrite SuccNat2Pos.id_succ.
  rewrite bigXadd_bigRplus // XD_Xreal // [in RHS]XD_Xreal //=.
  change (_ + _)%coq_nat with (fact n.+1).
  rewrite fact_zeroF /= Rmult_0_r big_ord_recl big1 /=.
    by congr Xreal; field.
  by move=>i _; rewrite Rmult_0_l Rmult_0_r.
have Hlim rx1 rx2 : (rx1 < rx2)%Re -> dom rx1 -> dom rx2 ->
  forall (k : nat) (r1 : R), (k <= n)%coq_nat ->
  (fun r2 : R => rx1 <= r2 <= rx2)%Re r1 ->
  derivable_pt_lim
  ((fun (n : nat) (r : R) => proj_val (XD n (Xreal r))) k) r1
  ((fun (n : nat) (r : R) => proj_val (XD n (Xreal r))) (S k) r1).
  move=> Hrx12 Hdom1 Hdom2 k y Hk Hy.
  have Hdy: (dom y) by move: Hdom; rewrite /connected; move/(_ rx1 rx2); apply.
  have Hderk := Hder k (Xreal y).
  case E: (XD (S k) (Xreal y)) Hk.
    move/leP; rewrite -ltnS=> Hk.
    by case (@Hdif y (S k) Hk Hdy).
  rewrite /Xderive_pt E in Hderk. move => Hk.
  destruct (XD k (Xreal y))=>//.
  exact: Hderk.
destruct (total_order_T rx0 rx) as [[H1|H2]|H3]; last 2 first.
    by case: Hneq.
  have H0 : (rx <= rx0 <= rx0)%Re by auto with real.
  have H : (rx <= rx <= rx0)%Re by auto with real.
  case: (Cor_Taylor_Lagrange rx rx0 n (fun n r => proj_val (XD n (Xreal r)))
    (Hlim _ _ (Rgt_lt _ _ H3) Hrx Hrx0) rx0 rx H0 H) => [c [Hc Hc1]].
  exists c.
  have Hdc : dom c.
    move: Hdom; rewrite /connected; move/(_ rx rx0); apply=>//.
    by case: (Hc1 Hneq)=> [J|K]; auto with real; psatzl R.
  split=>//; split; last by case:(Hc1 Hneq);rewrite /=; [right|left]; intuition.
  rewrite XD_Xreal //.
  rewrite sum_f_to_big in Hc.
  rewrite bigXadd_bigRplus// XD_Xreal// [in RHS]XD_Xreal//= SuccNat2Pos.id_succ.
  by change (_ + _)%coq_nat with (fact n.+1); rewrite fact_zeroF Hc.
have H0 : (rx0 <= rx0 <= rx)%Re by auto with real.
have H : (rx0 <= rx <= rx)%Re by auto with real.
case: (Cor_Taylor_Lagrange rx0 rx n (fun n r => proj_val (XD n (Xreal r)))
  (Hlim _ _ (Rgt_lt _ _ H1) Hrx0 Hrx) rx0 rx H0 H) => [c [Hc Hc1]].
exists c.
have Hdc : dom c.
  move: Hdom; rewrite /connected; move/(_ rx0 rx); apply=>//.
  by case: (Hc1 Hneq)=> [J|K]; auto with real; psatzl R.
split=>//; split; last by case:(Hc1 Hneq);rewrite /=; [right|left]; intuition.
rewrite sum_f_to_big in Hc.
rewrite XD_Xreal // bigXadd_bigRplus // XD_Xreal // [in RHS]XD_Xreal //=.
rewrite SuccNat2Pos.id_succ.
by change (_ + _)%coq_nat with (fact n.+1); rewrite fact_zeroF Hc.
Qed.

End NDerive.
