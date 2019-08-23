(**
This file is part of the Coq.Interval library for proving bounds of
real-valued expressions in Coq: http://coq-interval.gforge.inria.fr/

Copyright (C) 2007-2016, Inria

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
From Flocq Require Import Digits.

Require Import Stdlib.
Require Import Xreal.
Require Import Basic.
Require Import Sig.
Require Import Interval.
Require Import Float.

Module TranscendentalFloatFast (F : FloatOps with Definition even_radix := true).

Module I := FloatInterval F.
Module J := IntervalBasicExt I.
Module F' := FloatExt F.

CoInductive hidden_constant : Type :=
  | HConst : I.type -> hidden_constant.

CoInductive constants : Type :=
  | Consts: hidden_constant -> constants -> constants.

Fixpoint constant_getter_aux n cst :=
  match n, cst with
  | O, Consts (HConst xi) _ => xi
  | S p, Consts _ c => constant_getter_aux p c
  end.

Definition constant_getter cst prec :=
  let nb := Z.abs_nat (Z.pred (fst (Zdiv.Zdiv_eucl_POS (F.prec prec + 30)%positive 31%Z))) in
  constant_getter_aux nb cst.

CoFixpoint hidden_constant_generator gen n :=
  HConst (gen (F.PtoP (n * 31)%positive)).

CoFixpoint constant_generator_aux gen n :=
  Consts (hidden_constant_generator gen n) (constant_generator_aux gen (Pos.succ n)).

Definition constant_generator gen :=
  constant_generator_aux gen 1.

Definition Z2nat x :=
  match x with
  | Zpos p => nat_of_P p
  | _ => O
  end.

Definition Z2P x :=
  match x with
  | Zpos p => p
  | _ => xH
  end.

Definition c1 := F.fromZ 1.
Definition c2 := F.fromZ 2.
Definition c3 := F.fromZ 3.
Definition i1 := I.fromZ 1.
Definition i2 := I.fromZ 2.
Definition i3 := I.fromZ 3.
Definition i4 := I.fromZ 4.
Definition i6 := I.fromZ 6.
Definition s1 := F.ZtoS 1.
Definition sm1 := F.ZtoS (-1).
Definition sm8 := F.ZtoS (-8).
Definition c1_2 := F.scale2 c1 sm1.

Ltac bound_tac :=
  unfold Xround, Xbind ;
  match goal with
  | |- (round ?r rnd_DN ?p ?v <= ?v)%R =>
    apply (proj1 (proj2 (Generic_fmt.round_DN_pt F.radix (FLX.FLX_exp (Zpos p)) v)))
  | |- (?v <= round ?r rnd_UP ?p ?v)%R =>
    apply (proj1 (proj2 (Generic_fmt.round_UP_pt F.radix (FLX.FLX_exp (Zpos p)) v)))
  | |- (round ?r rnd_DN ?p ?v <= ?w)%R =>
    apply Rle_trans with (1 := proj1 (proj2 (Generic_fmt.round_DN_pt F.radix (FLX.FLX_exp (Zpos p)) v)))
  | |- (?w <= round ?r rnd_UP ?p ?v)%R =>
    apply Rle_trans with (2 := proj1 (proj2 (Generic_fmt.round_UP_pt F.radix (FLX.FLX_exp (Zpos p)) v)))
  end.

Notation toR := F.toR (only parsing).

(* 0 <= inputs *)
Fixpoint atan_fast0_aux prec thre powi sqri divi (nb : nat) { struct nb } :=
  let npwi := I.mul prec powi sqri in
  let vali := I.div prec npwi divi in
  match F'.cmp (I.upper vali) thre, nb with
  | Xlt, _
  | _, O => I.bnd F.zero (I.upper vali)
  | _, S n =>
    I.sub prec vali
      (atan_fast0_aux prec thre npwi sqri (I.add prec divi i2) n)
  end.

(* -1/2 <= input <= 1/2 *)
Definition atan_fast0 prec xi :=
  let x2i := I.sqr prec xi in
  let p := F.prec prec in
  let thre := F.scale c1 (F.ZtoS (Zneg p)) in
  let rem := atan_fast0_aux prec thre i1 x2i i3 (nat_of_P p) in
  I.mul prec (I.sub prec i1 rem) xi.

Definition pi4_gen prec :=
  let s2 := F.ZtoS 2 in
  I.sub prec
   (I.scale2 (atan_fast0 prec (I.inv prec (I.fromZ 5))) s2)
   (atan_fast0 prec (I.inv prec (I.fromZ 239))).

Definition pi4_seq := constant_generator pi4_gen.
Definition pi4 := constant_getter pi4_seq.

Definition atan_fastP prec x :=
  let xi := I.bnd x x in
  if F'.lt c1_2 x then
    let prec := F.incr_prec prec 2 in
    let pi4i := pi4 prec in
    if F'.lt c2 x then
      I.sub prec
       (I.scale2 pi4i s1)
       (atan_fast0 prec (I.div prec i1 xi))
    else
      let xm1i := I.sub prec xi i1 in
      let xp1i := I.add prec xi i1 in
      I.add prec pi4i
       (atan_fast0 prec (I.div prec xm1i xp1i))
  else
    atan_fast0 (F.incr_prec prec 1) xi.

Definition atan_fast prec x :=
  match F'.cmp x F.zero with
  | Xeq => I.bnd F.zero F.zero
  | Xlt => I.neg (atan_fastP prec (F.neg x))
  | Xgt => atan_fastP prec x
  | Xund => I.nai
  end.

Lemma atan_fast0_correct :
  forall prec xi x,
  (Rabs x <= /2)%R ->
  contains (I.convert xi) (Xreal x) ->
  contains (I.convert (atan_fast0 prec xi)) (Xreal (atan x)).
Proof.
intros prec xi x Bx Ix.
unfold atan_fast0.
rewrite atan_atanc, Rmult_comm.
apply J.mul_correct with (2 := Ix).
replace (atanc x) with (1 - (1 - atanc x))%R by ring.
apply J.sub_correct.
  apply I.fromZ_correct.
pose (Ai := fun x => sum_f_R0 (fun n : nat => ((-1) ^ n / INR (2 * n + 1) * x ^ (2 * n))%R)).
assert (Hexit : forall k powi divi,
    contains (I.convert powi) (Xreal (x ^ (2 * k))) ->
    contains (I.convert divi) (Xreal (INR (2 * (k + 1) + 1))) ->
    contains (I.convert (I.bnd F.zero (I.upper (I.div prec (I.mul prec powi (I.sqr prec xi)) divi))))
      (Xreal ((-1) ^ (k + 1) * (atanc x - Ai x k)))).
  intros k powi divi Hpow Hdiv.
  rewrite I.bnd_correct.
  rewrite F.zero_correct, I.upper_correct.
  assert (A: (0 <= (-1) ^ (k + 1) * (atanc x - Ai x k) <= x ^ (2 * (k + 1)) / INR (2 * (k + 1) + 1))%R).
    replace (Ai x k) with (sum_f_R0 (tg_alt (fun n => / INR (2 * n + 1) * x ^ (2 * n))%R) k).
    unfold Rdiv.
    rewrite (Rmult_comm (x ^ _)).
    replace (k + 1) with (S k) by ring.
    apply alternated_series_ineq'.
    apply Un_decreasing_atanc.
    lra.
    apply Un_cv_atanc.
    lra.
    unfold atanc.
    case Ratan.in_int ; intros Hx.
    case atanc_exists ; simpl projT1 ; intros l C.
    exact C.
    elim Hx.
    apply Rabs_le_inv.
    lra.
    apply sum_eq.
    intros n _.
    unfold tg_alt.
    apply sym_eq, Rmult_assoc.
  apply (conj (proj1 A)).
  assert (Hx2 := J.sqr_correct prec _ _ Ix).
  assert (H1 := J.mul_correct prec _ _ _ _ Hpow Hx2).
  assert (H2 := J.div_correct prec _ _ _ _ H1 Hdiv).
  destruct (I.convert (I.div _ _ _)) as [|l [|u]] ; try easy.
  simpl.
  apply Rle_trans with (1 := proj2 A).
  apply Rle_trans with (2 := proj2 H2).
  apply Req_le.
  apply Rmult_eq_compat_r.
  replace (2 * (k + 1)) with (2 * k + 2) by ring.
  now rewrite pow_add, <- Rsqr_pow2.
generalize (F.scale c1 (F.ZtoS (Z.neg (F.prec prec)))) (Pos.to_nat (F.prec prec)).
intros thre n.
replace 1%R with (Ai x 0) by (unfold Ai ; simpl ; field).
generalize (I.fromZ_correct 1) (I.fromZ_correct 3).
fold i1 i3.
generalize i1 i3.
intros powi divi.
change 1%R with (pow x (2 * 0)).
change 3%Z with (Z.of_nat (2 * (0 + 1) + 1)).
rewrite <- INR_IZR_INZ.
replace (Ai x 0%nat - atanc x)%R with ((-1) * 1 * (atanc x - Ai x 0%nat))%R by ring.
change (-1 * 1)%R with (pow (-1) (0 + 1)).
rewrite <- (minus_diag n) at 2 4 7 9.
generalize (le_refl n).
generalize n at 1 4 6 7 9 11.
intros m.
revert powi divi.
induction m as [|m IHm] ; intros powi divi Hm Hpow Hdiv.
  simpl atan_fast0_aux.
  specialize (Hexit (n - 0) _ _ Hpow Hdiv).
  now case F'.cmp.
simpl atan_fast0_aux.
set (powi' := I.mul prec powi (I.sqr prec xi)).
set (divi' := I.add prec divi i2).
specialize (IHm powi' divi').
specialize (Hexit (n - S m) _ _ Hpow Hdiv).
assert (H: forall p, n - S m + S p = n - m + p).
  intros p.
  clear -Hm ; lia.
cut (contains (I.convert (I.sub prec (I.div prec powi' divi)
        (atan_fast0_aux prec thre powi' (I.sqr prec xi) divi' m)))
      (Xreal ((-1) ^ (n - S m + 1) * (atanc x - Ai x (n - S m))))).
  now case F'.cmp.
replace ((-1) ^ (n - S m + 1) * (atanc x - Ai x (n - S m)%nat))%R
  with ((-1) ^ (n - S m + 1) * (-1) ^ S (n - S m) * x ^ (2 * S (n - S m)) * / INR (2 * S (n - S m) + 1) - (((-1) * (-1) ^ (n - S m + 1)) * (atanc x - (Ai x (n - S m)%nat + ((-1) ^ S (n - S m) * / INR (2 * S (n - S m) + 1) * x ^ (2 * S (n - S m)))))))%R by ring.
assert (Hpow': contains (I.convert powi') (Xreal (x ^ (2 * (n - S m + 1))))).
  replace (2 * (n - S m + 1)) with (2 * (n - S m) + 2) by ring.
  rewrite pow_add, <- Rsqr_pow2.
  apply J.mul_correct with (1 := Hpow).
  now apply J.sqr_correct.
apply J.sub_correct.
  rewrite <- pow_add.
  replace (n - S m + 1 + S (n - S m)) with (2 * (n - S m + 1)) by (clear -Hm ; omega).
  rewrite pow_1_even, Rmult_1_l.
  replace (S (n - S m)) with (n - S m + 1) by now rewrite plus_comm.
  apply J.div_correct.
  exact Hpow'.
  exact Hdiv.
evar_last.
apply IHm.
now apply le_Sn_le.
rewrite <- (plus_0_r (n - m)), <- H.
exact Hpow'.
rewrite H, plus_0_r in Hdiv.
replace (2 * (n - m + 1) + 1) with (2 * (n - m) + 1 + 2) by ring.
rewrite plus_INR.
apply J.add_correct with (1 := Hdiv).
apply I.fromZ_correct.
change (Ai x (n - S m)%nat + (-1) ^ S (n - S m) * / INR (2 * S (n - S m) + 1) * x ^ (2 * S (n - S m)))%R
  with (Ai x (S (n - S m))).
change (-1 * (-1) ^ (n - S m + 1))%R with ((-1) ^ (S (n - S m + 1)))%R.
rewrite <- plus_Sn_m.
now rewrite -> minus_Sn_m.
Qed.

Lemma pi4_correct :
  forall prec, contains (I.convert (pi4 prec)) (Xreal (PI/4)).
Proof.
intros prec.
rewrite Machin_4_5_239.
unfold pi4, constant_getter.
set (n := Z.abs_nat _).
unfold pi4_seq, constant_generator.
generalize xH at 1.
induction n as [|n].
2: intros p ; apply IHn.
simpl.
intros p.
generalize (F.PtoP (p * 31)).
clear prec p.
intros prec.
assert (H: forall p, (2 <= p)%Z ->
    contains (I.convert (atan_fast0 prec (I.inv prec (I.fromZ p)))) (Xreal (atan (/ IZR p)))).
  intros p Hp.
  apply atan_fast0_correct.
  rewrite Rabs_pos_eq.
  apply Rle_Rinv_pos.
  apply Rlt_0_2.
  now apply IZR_le.
  apply Rlt_le, Rinv_0_lt_compat.
  apply IZR_lt.
  now apply Z.lt_le_trans with (2 := Hp).
  replace (Xreal (/ IZR p)) with (Xinv (Xreal (IZR p))).
  apply I.inv_correct.
  apply I.fromZ_correct.
  unfold Xinv'.
  simpl.
  case is_zero_spec ; try easy.
  intros H.
  apply (eq_IZR p 0) in H.
  elim Hp.
  now rewrite H.
unfold pi4_gen.
apply (I.sub_correct _ _ _ (Xreal _) (Xreal _)).
rewrite Rmult_comm.
apply (I.scale2_correct _ (Xreal _)).
now apply (H 5%Z).
now apply (H 239%Z).
Qed.

Lemma atan_fastP_correct :
  forall prec x,
  F.toX x = Xreal (toR x) ->
  (0 <= toR x)%R ->
  contains (I.convert (atan_fastP prec x)) (Xreal (atan (toR x))).
Proof.
intros prec x Rx Bx.
unfold atan_fastP, c1_2, c1, c2, sm1.
rewrite F'.lt_correct with (2 := Rx).
2: {
  unfold F.toR.
  rewrite F.scale2_correct by easy.
  now rewrite F.fromZ_correct. }
unfold F.toR at 1.
rewrite F.scale2_correct by easy.
rewrite F.fromZ_correct.
simpl Rlt_bool.
rewrite Rmult_1_l.
change (Z.pow_pos 2 1) with 2%Z.
assert (Ix: contains (I.convert (I.bnd x x)) (Xreal (toR x))).
  rewrite I.bnd_correct, Rx.
  split ; apply Rle_refl.
case Rlt_bool_spec ; intros Bx'.
2: {
  apply atan_fast0_correct with (2 := Ix).
  now rewrite Rabs_pos_eq. }
rewrite F'.lt_correct with (2 := Rx).
2: unfold F.toR ; now rewrite F.fromZ_correct.
unfold F.toR at 1.
rewrite F.fromZ_correct.
simpl Rlt_bool.
case Rlt_bool_spec ; intros Bx'' ; cycle 1.
  replace (Xreal (atan (toR x))) with (Xadd (Xreal (PI / 4)) (Xatan (Xreal ((toR x - 1) / (toR x + 1))))).
  apply I.add_correct.
  apply pi4_correct.
  apply atan_fast0_correct.
  apply Rabs_le.
  assert (Bx1: (0 < toR x + 1)%R) by (clear -Bx ; lra).
  split.
  apply Rmult_le_reg_r with (1 := Bx1).
  unfold Rdiv.
  rewrite Rmult_assoc, Rinv_l, Rmult_1_r.
  apply Rminus_le.
  replace (- / 2 * (toR x + 1) - (toR x - 1))%R with (-3/2 * toR x + /2)%R by field.
  clear -Bx' ; lra.
  now apply Rgt_not_eq.
  apply Rmult_le_reg_r with (1 := Bx1).
  unfold Rdiv.
  rewrite Rmult_assoc, Rinv_l, Rmult_1_r.
  apply Rminus_le.
  replace (toR x - 1 - / 2 * (toR x + 1))%R with (/2 * toR x - 3/2)%R by field.
  lra.
  now apply Rgt_not_eq.
  apply J.div_correct.
  apply J.sub_correct with (1 := Ix).
  apply I.fromZ_correct.
  apply J.add_correct with (1 := Ix).
  apply I.fromZ_correct.
  simpl.
  apply (f_equal Xreal).
  rewrite Rplus_comm.
  apply atan_plus_PI4.
  lra.
replace (Xreal (atan (toR x))) with (Xsub (Xmul (Xreal (PI/4)) (Xreal 2)) (Xatan (Xreal (/ toR x)))).
apply I.sub_correct.
apply I.scale2_correct.
apply pi4_correct.
apply atan_fast0_correct.
  rewrite Rabs_pos_eq.
  apply Rle_Rinv_pos.
  apply Rlt_0_2.
  now apply Rlt_le.
  apply Rlt_le, Rinv_0_lt_compat.
  lra.
rewrite <- (Rmult_1_l (/ toR x)).
apply J.div_correct with (2 := Ix).
apply I.fromZ_correct.
  simpl.
  apply f_equal.
  rewrite atan_inv; lra.
Qed.

Lemma atan_fast_correct :
  forall prec x,
  contains (I.convert (atan_fast prec x)) (Xatan (F.toX x)).
Proof.
intros prec x.
unfold atan_fast.
rewrite F'.cmp_correct, F.zero_correct.
case_eq (F.toX x) ; simpl.
easy.
intros r Hr.
case Rcompare_spec ; intros H.
(* neg *)
rewrite <- (Ropp_involutive r).
replace (Ropp r) with (toR (F.neg x)).
rewrite atan_opp.
apply (I.neg_correct _ (Xreal _)).
apply atan_fastP_correct.
unfold toR.
now rewrite F.neg_correct, Hr.
unfold toR.
rewrite F.neg_correct, Hr.
simpl.
rewrite <- Ropp_0.
now apply Ropp_le_contravar, Rlt_le.
unfold toR.
now rewrite F.neg_correct, Hr.
(* zero *)
rewrite H, atan_0.
simpl.
rewrite F.zero_correct.
split ; apply Rle_refl.
(* pos *)
replace r with (toR x).
apply atan_fastP_correct.
unfold toR.
now rewrite Hr.
unfold toR.
rewrite Hr.
now apply Rlt_le.
unfold toR.
now rewrite Hr.
Qed.

(* 0 <= inputs *)
Fixpoint ln1p_fast0_aux prec thre powi xi divi (nb : nat) { struct nb } :=
  let npwi := I.mul prec powi xi in
  let vali := I.div prec npwi divi in
  match F'.cmp (I.upper vali) thre, nb with
  | Xlt, _
  | _, O => I.bnd F.zero (I.upper vali)
  | _, S n =>
    I.sub prec vali (ln1p_fast0_aux prec thre npwi xi (I.add prec divi i1) n)
  end.

(* 0 <= input <= 1/2 *)
Definition ln1p_fast0 prec xi :=
  let p := F.prec prec in
  let thre := F.scale c1 (F.ZtoS (Zneg p)) in
  let rem := ln1p_fast0_aux prec thre i1 xi i2 (nat_of_P p) in
  I.mul prec (I.sub prec (I.bnd c1 c1) rem) xi.

(* 1 <= input *)
Definition ln_fast1P prec xi :=
  let th := F.add_exact c1 (F.scale2 c1 sm8) in
  match F'.le' (I.upper xi) th with
  | true =>
    ln1p_fast0 prec (I.sub prec xi i1)
  | false =>
    let m := Digits.Zdigits2 (F.StoZ (F.mag (I.upper xi))) in
    let prec := F.incr_prec prec 10 in
    let fix reduce xi (nb : nat) {struct nb} :=
      match F'.le' (I.upper xi) th, nb with
      | true, _ => ln1p_fast0 prec (I.sub prec xi i1)
      | _, O => I.bnd F.zero F.nan
      | _, S n => I.scale2 (reduce (I.sqrt prec xi) n) s1
      end in
    reduce xi (8 + Z2nat m)
  end.

Definition ln_fast prec x :=
  match F'.cmp x F.zero with
  | Xgt =>
    let xi := I.bnd x x in
    match F.cmp x c1 with
    | Eq => I.zero
    | Lt =>
      let m := Z.opp (F.StoZ (F.mag (F.sub rnd_UP prec c1 x))) in
      let prec := F.incr_prec prec (Z2P m) in
      I.neg (ln_fast1P prec (I.div prec i1 xi))
    | Gt => ln_fast1P prec xi
    end
  | _ => I.nai
  end.

Lemma ln1p_fast0_correct :
  forall prec xi x,
  (0 <= x <= /2)%R ->
  contains (I.convert xi) (Xreal x) ->
  contains (I.convert (ln1p_fast0 prec xi)) (Xreal (ln (1 + x))).
Proof.
intros prec xi x Bx Ix.
unfold ln1p_fast0.
rewrite ln1p_ln1pc.
replace (ln1pc x) with (1 - (1 - ln1pc x))%R by ring.
rewrite Rmult_comm.
apply J.mul_correct with (2 := Ix).
apply J.sub_correct.
apply I.fromZ_correct.
pose (Ai := fun x => sum_f_R0 (fun n : nat => ((-1) ^ n / INR (n + 1) * x ^ n)%R)).
assert (Hexit : forall k powi divi,
    contains (I.convert powi) (Xreal (x ^ k)) ->
    contains (I.convert divi) (Xreal (INR ((k + 1) + 1))) ->
    contains (I.convert (I.bnd F.zero (I.upper (I.div prec (I.mul prec powi xi) divi))))
      (Xreal ((-1) ^ (k + 1) * (ln1pc x - Ai x k)))).
  intros k powi divi Hpow Hdiv.
  rewrite I.bnd_correct.
  rewrite F.zero_correct, I.upper_correct.
  assert (A: (0 <= (-1) ^ (k + 1) * (ln1pc x - Ai x k) <= x ^ (k + 1) / INR ((k + 1) + 1))%R).
    replace (Ai x k) with (sum_f_R0 (tg_alt (fun n => / INR (n + 1) * x ^ n)%R) k).
    unfold Rdiv.
    rewrite (Rmult_comm (x ^ _)).
    replace (k + 1) with (S k) by ring.
    apply alternated_series_ineq'.
    apply Un_decreasing_ln1pc.
    lra.
    apply Un_cv_ln1pc.
    rewrite Rabs_pos_eq ; lra.
    unfold ln1pc.
    case ln1pc_in_int ; intros Hx.
    case ln1pc_exists ; simpl projT1 ; intros l C.
    exact C.
    elim Hx.
    lra.
    apply sum_eq.
    intros n _.
    unfold tg_alt.
    apply sym_eq, Rmult_assoc.
  apply (conj (proj1 A)).
  assert (H1 := J.mul_correct prec _ _ _ _ Hpow Ix).
  assert (H2 := J.div_correct prec _ _ _ _ H1 Hdiv).
  destruct (I.convert (I.div _ _ _)) as [|l [|u]] ; try easy.
  apply Rle_trans with (1 := proj2 A).
  apply Rle_trans with (2 := proj2 H2).
  apply Req_le, Rmult_eq_compat_r.
  rewrite pow_add.
  simpl.
  now rewrite Rmult_1_r.
generalize (F.scale c1 (F.ZtoS (Z.neg (F.prec prec)))) (Pos.to_nat (F.prec prec)).
intros thre n.
replace 1%R with (Ai x 0) by (unfold Ai ; simpl ; field).
generalize (I.fromZ_correct 1) (I.fromZ_correct 2).
fold i1 i2.
generalize i1 i2.
intros powi divi.
change 1%R with (pow x 0).
change 2%Z with (Z_of_nat ((0 + 1) + 1)).
rewrite <- INR_IZR_INZ.
replace (Ai x 0%nat - ln1pc x)%R with ((-1) * 1 * (ln1pc x - Ai x 0%nat))%R by ring.
change (-1 * 1)%R with (pow (-1) (0 + 1)).
rewrite <- (minus_diag n) at 1 2 5 7.
generalize (le_refl n).
generalize n at 1 4 6 7 9 11.
intros m.
revert powi divi.
induction m as [|m IHm] ; intros powi divi Hm Hpow Hdiv.
  simpl.
  cut (contains (I.convert (I.bnd F.zero (I.upper (I.div prec (I.mul prec powi xi) divi))))
        (Xreal ((-1) ^ (n - 0 + 1) * (ln1pc x - Ai x (n - 0))))).
  now destruct F'.cmp.
  now apply Hexit.
simpl ln1p_fast0_aux.
set (powi' := I.mul prec powi xi).
set (divi' := I.add prec divi i1).
specialize (IHm powi' divi').
assert (H: forall p, n - S m + S p = n - m + p).
  intros p.
  clear -Hm ; omega.
cut (contains (I.convert (I.sub prec (I.div prec powi' divi) (ln1p_fast0_aux prec thre powi' xi divi' m)))
    (Xreal ((-1) ^ (n - S m + 1) * (ln1pc x - Ai x (n - S m))))).
  case F'.cmp ; try easy.
  intros H'.
  now apply Hexit.
replace ((-1) ^ (n - S m + 1) * (ln1pc x - Ai x (n - S m)%nat))%R
  with ((-1) ^ (n - S m + 1) * (-1) ^ S (n - S m) * x ^ (S (n - S m)) * / INR (S (n - S m) + 1) - (((-1) * (-1) ^ (n - S m + 1)) * (ln1pc x - (Ai x (n - S m)%nat + ((-1) ^ S (n - S m) * / INR (S (n - S m) + 1) * x ^ (S (n - S m)))))))%R by ring.
apply J.sub_correct.
  rewrite <- pow_add.
  replace (n - S m + 1 + S (n - S m)) with (2 * (n - S m + 1)) by (clear -Hm ; omega).
  replace (S (n - S m)) with (n - S m + 1) by now rewrite plus_comm.
  apply J.div_correct with (2 := Hdiv).
  rewrite pow_1_even, Rmult_1_l.
  rewrite pow_add, pow_1.
  now apply J.mul_correct.
evar_last.
apply IHm.
clear -Hm ; lia.
rewrite <- (plus_0_r (n - m)), <- H.
rewrite pow_add, pow_1.
now apply J.mul_correct.
rewrite <- H.
replace (_ + 2 + 1) with (n - S m + 1 + 1 + 1) by ring.
rewrite plus_INR.
apply J.add_correct with (1 := Hdiv).
apply I.fromZ_correct.
change (Ai x (n - S m)%nat + (-1) ^ S (n - S m) * / INR (S (n - S m) + 1) * x ^ (S (n - S m)))%R
  with (Ai x (S (n - S m))).
change (-1 * (-1) ^ (n - S m + 1))%R with ((-1) ^ (S (n - S m + 1)))%R.
rewrite <- plus_Sn_m.
now rewrite -> minus_Sn_m.
Qed.

Lemma ln_fast1P_correct :
  forall prec xi x,
  (1 <= x)%R ->
  contains (I.convert xi) (Xreal x) ->
  contains (I.convert (ln_fast1P prec xi)) (Xreal (ln x)).
Proof.
set (thre := F.add_exact c1 (F.scale2 c1 sm8)).
assert (H: forall prec xi x,
    (1 <= x)%R ->
    (F'.le' (I.upper xi) thre = true) ->
    contains (I.convert xi) (Xreal x) ->
    contains (I.convert (ln1p_fast0 prec (I.sub prec xi i1))) (Xreal (ln x))).
  intros prec xi x Hx Hxu Ix.
  replace x with (1 + (x - 1))%R by ring.
  apply ln1p_fast0_correct.
  split. lra.
  apply F'.le'_correct in Hxu.
  rewrite I.upper_correct in Hxu.
  destruct (I.convert xi) as [|l [|u]] ; try easy.
  revert Hxu.
  simpl.
  unfold thre, c1, sm8.
  rewrite F.add_exact_correct, F.scale2_correct, F.fromZ_correct by easy.
  simpl.
  change (Z.pow_pos 2 8) with 256%Z.
  generalize (proj2 Ix).
  lra.
  apply J.sub_correct with (1 := Ix).
  apply I.fromZ_correct.
intros prec xi x Hx Ix.
unfold ln_fast1P.
fold thre.
case_eq (F'.le' (I.upper xi) thre) ; intros Hxu.
now apply H.
clear Hxu.
set (m := Zdigits2 (F.StoZ (F.mag (I.upper xi)))).
clearbody m.
generalize (F.incr_prec prec 10).
clear prec. intro prec.
generalize (8 + Z2nat m).
intro nb.
revert xi x Hx Ix.
induction nb as [|nb] ; intros xi x Hx Ix.
(* nb = 0 *)
simpl.
case_eq (F'.le' (I.upper xi) thre) ; intros Hxu.
now apply H.
simpl.
rewrite F.zero_correct, F.nan_correct.
refine (conj _ I).
destruct (Rlt_dec 1 x) as [Hx'|Hx'].
rewrite <- ln_1.
apply Rlt_le, ln_increasing.
exact Rlt_0_1.
exact Hx'.
replace x with 1%R by lra.
rewrite ln_1.
apply Rle_refl.
(* nb > 0 *)
case_eq (F'.le' (I.upper xi) thre) ; intros Hxu.
now apply H.
clear H Hxu.
replace (ln x) with (ln (sqrt x) * 2)%R.
change (Xreal (ln (sqrt x) * 2)) with (Xmul (Xreal (ln (sqrt x))) (Xreal (bpow radix2 1))).
apply I.scale2_correct.
apply IHnb.
clear IHnb.
rewrite <- sqrt_1.
now apply sqrt_le_1_alt.
now apply J.sqrt_correct.
rewrite <- (sqrt_sqrt x) at 2 by lra.
assert (0 < sqrt x)%R.
  apply sqrt_lt_R0.
  lra.
rewrite ln_mult by easy.
ring.
Qed.

Theorem ln_fast_correct :
  forall prec x,
  contains (I.convert (ln_fast prec x)) (Xln (F.toX x)).
Proof.
intros prec x.
unfold ln_fast.
rewrite F'.cmp_correct, F.zero_correct.
case_eq (Xcmp (F.toX x) (Xreal 0)) ; try easy.
destruct (F'.toX_spec x) as [|Rx].
easy.
unfold c1.
rewrite F.cmp_correct with (1 := Rx).
2: unfold F.toR ; now rewrite F.fromZ_correct.
unfold F.toR at 3.
rewrite F.fromZ_correct.
unfold Xcmp, proj_val.
case Rcompare_spec ; try easy.
intros Hx _.
unfold Xln'.
simpl Xbind.
rewrite is_positive_true by easy.
case Rcompare_spec.
(* x < 1 *)
intros Hx'.
generalize (F.incr_prec prec (Z2P (Z.opp (F.StoZ (F.mag (F.sub rnd_UP prec (F.fromZ 1) x)))))).
clear prec.
intros prec.
rewrite <- (Rinv_involutive (F.toR x)).
rewrite ln_Rinv.
apply J.neg_correct.
apply ln_fast1P_correct.
rewrite <- Rinv_1.
apply Rinv_le.
exact Hx.
now apply Rlt_le.
rewrite <- (Rmult_1_l (/ _)).
apply J.div_correct.
apply I.fromZ_correct.
rewrite I.bnd_correct, Rx.
split ; apply Rle_refl.
now apply Rinv_0_lt_compat.
now apply Rgt_not_eq.
(* x = 1 *)
intros ->.
rewrite I.zero_correct, ln_1.
split ; apply Rle_refl.
(* x > 1 *)
intros Hx'.
apply ln_fast1P_correct.
now apply Rlt_le.
rewrite I.bnd_correct, Rx.
split ; apply Rle_refl.
Qed.

(*
(* 0 <= inputs *)
Fixpoint umc_fast0_aux prec thre powl powu sqrl sqru fact div (nb : nat) { struct nb } :=
  let npwu := F.mul rnd_UP prec powu sqru in
  let valu := F.div rnd_UP prec npwu div in
  match F.cmp valu thre, nb with
  | Xlt, _
  | _, O => I.bnd F.zero valu
  | _, S n =>
    let npwl := F.mul rnd_DN prec powl sqrl in
    let vall := F.div rnd_DN prec npwl div in
    let one := F.fromZ 1 in
    let nfact := F.add_exact fact (F.add_exact one one) in
    let ndiv := F.mul_exact div (F.mul_exact fact (F.add_exact fact one)) in
    I.sub prec (I.bnd vall valu)
      (umc_fast0_aux prec thre npwl npwu sqrl sqru nfact ndiv n)
  end.

Definition umc_fast0 prec x :=
  let x2l := F.mul rnd_DN prec x x in
  let x2u := F.mul rnd_UP prec x x in
  let c1 := F.fromZ 1 in
  let p := F.prec prec in
  let thre := F.scale c1 (F.ZtoS (Zneg p)) in
  I.scale2
   (I.mul prec
     (I.bnd x2l x2u)
     (I.sub prec
       (I.bnd c1 c1)
       (umc_fast0_aux prec thre c1 c1 x2l x2u (F.fromZ 5) (F.fromZ 12) (nat_of_P p))))
   (F.ZtoS (-1)%Z).

Definition umc_reduce prec x :=
  let c1 := F.fromZ 1 in
  let th := F.scale2 c1 (F.ZtoS (-4)%Z) in
  (*let prec := F.incr_prec prec 1 in*)
  let c2 := F.fromZ 2 in
  let i2 := I.bnd c2 c2 in
  let s1 := F.ZtoS 1 in
  let sm1 := F.ZtoS (-1)%Z in
  let fix reduce x (nb : nat) {struct nb} :=
    match le x th, nb with
    | true, _ => umc_fast0 prec x
    | _, O => umc_fast0 prec x
    | _, S n =>
      (*match reduce (F.scale2 x sm1) n with
      | Ibnd yl yu => I.scale2 (Ibnd (F.mul rnd_DN prec yl (F.sub rnd_DN prec c2 yl)) (F.mul rnd_UP prec yu (F.sub rnd_UP prec c2 yu))) s1
      | Inan => Inan
      end*)
      let u := reduce (F.scale2 x sm1) n in
      I.scale2 (I.mul prec u (I.sub prec i2 u)) s1
    end in
  reduce x 10.

Definition cos_fast0 prec x :=
  let c1 := F.fromZ 1 in
  I.sub prec (I.bnd c1 c1) (umc_reduce prec x).
*)

(* 0 <= inputs *)
Fixpoint cos_fast0_aux prec thre powi sqri facti divi (nb : nat) { struct nb } :=
  let npwi := I.mul prec powi sqri in
  let vali := I.div prec npwi divi in
  match F'.cmp (I.upper vali) thre, nb with
  | Xlt, _
  | _, O => I.bnd F.zero (I.upper vali)
  | _, S n =>
    let nfacti := I.add prec facti i2 in
    let ndivi := I.mul prec divi (I.mul prec facti (I.add prec facti i1)) in
    I.sub prec vali (cos_fast0_aux prec thre npwi sqri nfacti ndivi n)
  end.

(* -1/2 <= input <= 1/2 *)
Definition cos_fast0 prec x :=
  let xi := I.bnd x x in
  let x2i := I.sqr prec xi in
  let p := F.prec prec in
  let thre := F.scale c1 (F.ZtoS (Zneg p)) in
  let rem := cos_fast0_aux prec thre i1 x2i i3 i2 (nat_of_P p) in
  I.sub prec i1 rem.

(* 0 <= input *)
Definition sin_cos_reduce prec x :=
  let th := F.scale2 c1 sm1 in
  let fix reduce x (nb : nat) {struct nb} :=
    match F'.le' x th, nb with
    | true, _ => (Gt, cos_fast0 prec x)
    | _, O => (Eq, I.bnd (F.neg c1) c1)
    | _, S n =>
      match reduce (F.scale2 x sm1) n with
      | (s, c) =>
       (match s, I.sign_large c with
        | Lt, Xgt => Lt
        | Lt, Xlt => Gt
        | Lt, _ => Eq
        | Gt, Xlt => Lt
        | Gt, Xgt => Gt
        | Gt, _ => Eq
        | _, _ => s
        end,
        I.sub prec (I.scale2 (I.sqr prec c) s1) i1)
      end
    end in
  reduce x.

Lemma cos_fast0_correct :
  forall prec x,
  F.toX x = Xreal (toR x) ->
  (Rabs (toR x) <= /2)%R ->
  contains (I.convert (cos_fast0 prec x)) (Xreal (cos (toR x))).
Proof.
intros prec x Rx Bx.
unfold cos_fast0.
replace (cos (toR x)) with (1 - (1 - cos (toR x)))%R by ring.
apply J.sub_correct.
apply I.fromZ_correct.
set (xi := I.bnd x x).
assert (Ix: contains (I.convert xi) (Xreal (toR x))).
  unfold xi.
  rewrite I.bnd_correct, Rx.
  split ; apply Rle_refl.
set (x2i := I.sqr prec xi).
assert (Hexit: forall k powi divi,
    contains (I.convert powi) (Xreal (toR x ^ (2 * k))) ->
    contains (I.convert divi) (Xreal (INR (fact (2 * (k + 1))))) ->
    contains (I.convert (I.bnd F.zero (I.upper (I.div prec (I.mul prec powi x2i) divi))))
      (Xreal ((-1) ^ (k + 1) * (cos (toR x) - A1 (toR x) k)))).
  intros k powi facti Hpow Hdiv.
  rewrite I.bnd_correct.
  rewrite F.zero_correct, I.upper_correct.
  assert (A: (0 <= (-1) ^ (k + 1) * (cos (toR x) - A1 (toR x) k) <= toR x ^ (2 * (k + 1)) / INR (fact (2 * (k + 1))))%R).
    replace (A1 (toR x) k) with (sum_f_R0 (tg_alt (fun n => / INR (fact (2 * n)) * toR x ^ (2 * n))%R) k).
    unfold Rdiv.
    rewrite (Rmult_comm (toR x ^ _)).
    replace (k + 1) with (S k) by ring.
    apply alternated_series_ineq'.
    apply Un_decreasing_cos.
    lra.
    apply (Un_cv_subseq (fun n => (/ INR (fact n) * toR x ^ n)%R)).
    clear ; intros n ; omega.
    eapply Un_cv_ext.
    intros n.
    apply Rmult_comm.
    apply cv_speed_pow_fact.
    generalize (A1_cvg (toR x)).
    apply Un_cv_ext.
    intros n.
    unfold A1, tg_alt.
    apply sum_eq.
    intros i _.
    apply Rmult_assoc.
    unfold A1, tg_alt.
    apply sum_eq.
    intros i _.
    apply sym_eq, Rmult_assoc.
  apply (conj (proj1 A)).
  assert (Hx2 := J.sqr_correct prec _ _ Ix).
  assert (H1 := J.mul_correct prec _ _ _ _ Hpow Hx2).
  assert (H2 := J.div_correct prec _ _ _ _ H1 Hdiv).
  destruct (I.convert (I.div _ _ _)) as [|l [|u]] ; try easy.
  apply Rle_trans with (1 := proj2 A).
  apply Rle_trans with (2 := proj2 H2).
  apply Req_le, Rmult_eq_compat_r.
  replace (2 * (k + 1)) with (2 * k + 2) by ring.
  rewrite pow_add.
  now rewrite Rsqr_pow2.
generalize (F.scale c1 (F.ZtoS (Z.neg (F.prec prec)))) (Pos.to_nat (F.prec prec)).
intros thre n.
replace 1%R with (A1 (toR x) 0) by (unfold A1 ; simpl ; field).
generalize (I.fromZ_correct 1) (I.fromZ_correct 2) (I.fromZ_correct 3).
fold i1 i2 i3.
generalize i1 i2 i3.
intros powi divi facti.
change 1%R with (pow (toR x) (2 * 0)).
change 3%Z with (Z_of_nat (2 * (0 + 1) + 1)).
change 2%Z with (Z_of_nat (fact (2 * (0 + 1)))).
rewrite <- 2!INR_IZR_INZ.
replace (A1 (toR x) 0 - cos (toR x))%R with ((-1) * 1 * (cos (toR x) - A1 (toR x) 0))%R by ring.
change (-1 * 1)%R with (pow (-1) (0 + 1)).
rewrite <- (minus_diag n) at 2 4 7 10 12.
generalize (le_refl n).
generalize n at 1 4 6 8 9 11 13.
intros m.
revert powi divi facti.
induction m as [|m IHm] ; intros powi divi facti Hm Hpow Hdiv Hfact.
  simpl cos_fast0_aux.
  cut (contains (I.convert (I.bnd F.zero (I.upper (I.div prec (I.mul prec powi x2i) divi))))
        (Xreal ((-1) ^ (n - 0 + 1) * (cos (toR x) - A1 (toR x) (n - 0))))).
  now destruct F'.cmp.
  now apply Hexit.
simpl cos_fast0_aux.
set (powi' := I.mul prec powi x2i).
set (divi' := I.mul prec divi (I.mul prec facti (I.add prec facti i1))).
set (facti' := I.add prec facti i2).
specialize (IHm powi' divi' facti').
assert (H: forall p, n - S m + S p = n - m + p).
  intros p.
  clear -Hm ; lia.
cut (contains (I.convert (I.sub prec (I.div prec powi' divi)
           (cos_fast0_aux prec thre powi' x2i facti' divi' m)))
    (Xreal ((-1) ^ (n - S m + 1) * (cos (toR x) - A1 (toR x) (n - S m))))).
  case F'.cmp ; try easy.
  intros H'.
  now apply Hexit.
replace ((-1) ^ (n - S m + 1) * (cos (toR x) - A1 (toR x) (n - S m)))%R
  with ((-1) ^ (n - S m + 1) * (-1) ^ S (n - S m) * (toR x) ^ (2 * S (n - S m)) * / INR (fact (2 * S (n - S m))) - (((-1) * (-1) ^ (n - S m + 1)) * (cos (toR x) - (A1 (toR x) (n - S m) + ((-1) ^ S (n - S m) * / INR (fact (2 * S (n - S m))) * (toR x) ^ (2 * S (n - S m)))))))%R by ring.
assert (Hpow': contains (I.convert powi') (Xreal (toR x ^ (2 * (n - S m + 1))))).
  replace (2 * (n - S m + 1)) with (2 * (n - S m) + 2) by ring.
  rewrite pow_add, <- Rsqr_pow2.
  apply J.mul_correct with (1 := Hpow).
  now apply J.sqr_correct.
apply J.sub_correct.
  rewrite <- pow_add.
  replace (n - S m + 1 + S (n - S m)) with (2 * (n - S m + 1)) by (clear -Hm ; omega).
  rewrite pow_1_even, Rmult_1_l.
  replace (S (n - S m)) with (n - S m + 1) by now rewrite plus_comm.
  now apply J.div_correct.
evar_last.
apply IHm.
clear -Hm ; lia.
now rewrite <- (plus_0_r (n - m)), <- H.
rewrite <- H.
replace (2 * (n - S m + 2)) with (S (S (2 * (n - S m + 1)))) by ring.
rewrite 2!fact_simpl.
rewrite 2!mult_INR, <- Rmult_assoc, Rmult_comm.
apply J.mul_correct with (1 := Hdiv).
rewrite Rmult_comm.
apply J.mul_correct.
now rewrite <- Nat.add_1_r.
rewrite <- 2!Nat.add_1_r.
rewrite plus_INR.
apply J.add_correct with (1 := Hfact).
apply I.fromZ_correct.
rewrite <- H.
replace (2 * (n - S m + 2) + 1) with (2 * (n - S m + 1) + 1 + 2) by ring.
rewrite plus_INR.
apply J.add_correct with (1 := Hfact).
apply I.fromZ_correct.
apply f_equal.
change (A1 (toR x) (n - S m) + (-1) ^ S (n - S m) * / INR (fact (2 * S (n - S m))) * toR x ^ (2 * S (n - S m)))%R
  with (A1 (toR x) (S (n - S m))).
change (-1 * (-1) ^ (n - S m + 1))%R with ((-1) ^ (S (n - S m + 1)))%R.
rewrite <- plus_Sn_m.
now rewrite -> minus_Sn_m.
Qed.

Lemma sin_cos_reduce_correct :
  forall prec nb x,
  F.toX x = Xreal (toR x) ->
  (0 <= toR x)%R ->
  match sin_cos_reduce prec x nb with
  | (ss, ci) =>
    contains (I.convert ci) (Xreal (cos (toR x))) /\
    match ss with
    | Lt => (sin (toR x) <= 0)%R
    | Gt => (0 <= sin (toR x))%R
    | _ => True
    end
  end.
Proof.
intros prec.
(* . *)
assert (forall x, F.toX x = Xreal (toR x) -> (0 <= toR x)%R ->
        F'.le' x (F.scale2 (F.fromZ 1) (F.ZtoS (-1))) = true ->
        contains (I.convert (cos_fast0 prec x)) (Xreal (cos (toR x))) /\
        (0 <= sin (toR x))%R).
intros x Hxr Hx0 H.
assert (toR x <= /2)%R.
apply F'.le'_correct in H.
revert H.
rewrite Hxr, F.scale2_correct, F.fromZ_correct by easy.
simpl.
rewrite Rmult_1_l.
now intros.
(* .. *)
split.
apply cos_fast0_correct with (1 := Hxr).
rewrite Rabs_right.
exact H0.
now apply Rle_ge.
apply sin_ge_0 with (1 := Hx0).
(*   x <= pi *)
apply Rle_trans with (1 := H0).
apply Rlt_le.
apply Rmult_lt_reg_l with (/4)%R.
apply Rinv_0_lt_compat.
now apply IZR_lt.
rewrite <- (Rmult_comm PI).
apply Rlt_le_trans with (2 := proj1 (PI_ineq 0)).
unfold tg_alt, PI_tg.
simpl.
lra.
(* . *)
induction nb ; intros x Hxr Hx.
(* nb = 0 *)
simpl.
case_eq (F'.le' x (F.scale2 c1 sm1)).
intros.
exact (H x Hxr Hx H0).
intros _.
simpl.
unfold c1.
rewrite F.neg_correct.
rewrite F.fromZ_correct.
refine (conj _ I).
simpl.
apply COS_bound.
(* nb > 0 *)
simpl.
case_eq (F'.le' x (F.scale2 c1 sm1)).
intros.
exact (H x Hxr Hx H0).
intros _.
refine (_ (IHnb (F.scale2 x sm1) _ _)).
destruct (sin_cos_reduce prec (F.scale2 x sm1) nb) as (ss, ci).
clear -Hxr.
replace (toR x) with (2 * (toR (F.scale2 x sm1)))%R.
generalize (toR (F.scale2 x sm1)).
clear.
intros hx (Hc, Hs).
split.
(* - cos *)
replace (Xreal (cos (2 * hx))) with (Xsub (Xmul (Xsqr (Xreal (cos hx))) (Xreal 2)) (Xreal 1)).
apply I.sub_correct.
apply I.scale2_correct.
apply I.sqr_correct.
exact Hc.
apply I.fromZ_correct.
simpl.
apply f_equal.
rewrite cos_2a_cos.
unfold Rsqr.
ring.
(* - sin *)
rewrite sin_2a.
destruct ss.
exact I.
change (cos hx) with (proj_val (Xreal (cos hx))).
generalize (I.sign_large_correct ci).
case (I.sign_large ci) ; intros ; try exact I.
apply Rmult_le_neg_neg.
apply Rmult_le_pos_neg.
now apply IZR_le.
exact Hs.
exact (proj2 (H _ Hc)).
apply Rmult_le_neg_pos.
apply Rmult_le_pos_neg.
now apply IZR_le.
exact Hs.
exact (proj2 (H _ Hc)).
change (cos hx) with (proj_val (Xreal (cos hx))).
generalize (I.sign_large_correct ci).
case (I.sign_large ci) ; intros ; try exact I.
apply Rmult_le_pos_neg.
apply Rmult_le_pos_pos.
now apply IZR_le.
exact Hs.
exact (proj2 (H _ Hc)).
apply Rmult_le_pos_pos.
apply Rmult_le_pos_pos.
now apply IZR_le.
exact Hs.
exact (proj2 (H _ Hc)).
(* - . *)
unfold toR, sm1.
rewrite F.scale2_correct, Hxr by easy.
simpl.
change (Z.pow_pos 2 1) with 2%Z.
field.
(* - . *)
unfold toR, sm1.
now rewrite F.scale2_correct, Hxr.
unfold toR, sm1.
rewrite F.scale2_correct, Hxr by easy.
simpl.
apply Rmult_le_pos with (1 := Hx).
apply Rlt_le, Rinv_0_lt_compat.
now apply IZR_lt.
Qed.

(* 0 <= input *)
Definition cos_fastP prec x :=
  let th := F.scale2 c1 sm1 in
  match F'.le' x th with
  | true => cos_fast0 prec x
  | _ =>
    let m := F.StoZ (F.mag x) in
    let prec := F.incr_prec prec (Z2P (m + 6)) in
    snd (sin_cos_reduce prec x (S (Z2nat m)))
  end.

Lemma cos_fastP_correct :
  forall prec x,
  F.toX x = Xreal (toR x) ->
  (0 <= toR x)%R ->
  contains (I.convert (cos_fastP prec x)) (Xreal (cos (toR x))).
Proof.
intros prec x Hxr Hx0.
unfold cos_fastP.
case_eq (F'.le' x (F.scale2 c1 sm1)) ; intros H.
apply cos_fast0_correct.
easy.
rewrite Rabs_pos_eq with (1 := Hx0).
apply F'.le'_correct in H.
revert H.
unfold toR, sm1, c1.
rewrite Hxr, F.scale2_correct, F.fromZ_correct by easy.
simpl.
now rewrite Rmult_1_l.
generalize (S (Z2nat (F.StoZ (F.mag x)))) (F.incr_prec prec (Z2P (F.StoZ (F.mag x) + 6))).
intros nb prec'.
generalize (sin_cos_reduce_correct prec' nb x Hxr Hx0).
destruct sin_cos_reduce as [ss ci].
apply proj1.
Qed.

Definition cos_fast prec x :=
  match F'.cmp x F.zero with
  | Xeq => I.bnd c1 c1
  | Xlt => cos_fastP prec (F.neg x)
  | Xgt => cos_fastP prec x
  | Xund => I.nai
  end.

Theorem cos_fast_correct :
  forall prec x,
  contains (I.convert (cos_fast prec x)) (Xcos (F.toX x)).
Proof.
intros prec x.
unfold cos_fast.
rewrite F'.cmp_correct, F.zero_correct.
case_eq (F.toX x).
easy.
intros r Hr.
simpl.
case Rcompare_spec ; intros H.
(* neg *)
replace r with (- toR (F.neg x))%R.
rewrite cos_neg.
apply cos_fastP_correct.
unfold toR.
now rewrite F.neg_correct, Hr.
unfold toR.
rewrite F.neg_correct, Hr.
rewrite <- Ropp_0.
apply Ropp_le_contravar.
now apply Rlt_le.
unfold toR.
rewrite F.neg_correct, Hr.
apply Ropp_involutive.
(* zero *)
rewrite H, cos_0.
unfold c1.
simpl.
rewrite F.fromZ_correct.
split ; apply Rle_refl.
(* pos *)
replace r with (toR x).
apply cos_fastP_correct.
unfold toR.
now rewrite Hr.
unfold toR.
rewrite Hr.
now apply Rlt_le.
unfold toR.
now rewrite Hr.
Qed.

(* -1/2 <= input <= 1/2 *)
Definition sin_fast0 prec x :=
  let xi := I.bnd x x in
  let x2i := I.sqr prec xi in
  let p := F.prec prec in
  let thre := F.scale c1 (F.ZtoS (Zneg p)) in
  let rem := cos_fast0_aux prec thre i1 x2i i4 i6 (nat_of_P p) in
  I.mul prec (I.sub prec i1 rem) xi.

Lemma sin_fast0_correct :
  forall prec x,
  F.toX x = Xreal (toR x) ->
  (Rabs (toR x) <= /2)%R ->
  contains (I.convert (sin_fast0 prec x)) (Xreal (sin (toR x))).
Proof.
intros prec x Rx Bx.
unfold sin_fast0.
rewrite sin_sinc.
replace (sinc (toR x)) with (1 - (1 - sinc (toR x)))%R by ring.
rewrite Rmult_comm.
set (xi := I.bnd x x).
assert (Ix: contains (I.convert xi) (Xreal (toR x))).
  unfold xi.
  rewrite I.bnd_correct, Rx.
  split ; apply Rle_refl.
apply J.mul_correct with (2 := Ix).
apply J.sub_correct.
apply I.fromZ_correct.
set (x2i := I.sqr prec xi).
pose (Si := fun x => sum_f_R0 (fun n : nat => ((-1) ^ n / INR (fact (2 * n + 1)) * x ^ (2 * n))%R)).
assert (Hexit : forall k powi divi,
    contains (I.convert powi) (Xreal (toR x ^ (2 * k))) ->
    contains (I.convert divi) (Xreal (INR (fact (2 * (k + 1) + 1)))) ->
    contains (I.convert (I.bnd F.zero (I.upper (I.div prec (I.mul prec powi x2i) divi))))
      (Xreal ((-1) ^ (k + 1) * (sinc (toR x) - Si (toR x) k)))).
  intros k powi divi Hpow Hdiv.
  rewrite I.bnd_correct.
  rewrite F.zero_correct, I.upper_correct.
  assert (A: (0 <= (-1) ^ (k + 1) * (sinc (toR x) - Si (toR x) k) <= toR x ^ (2 * (k + 1)) / INR (fact (2 * (k + 1) + 1)))%R).
    replace (Si (toR x) k) with (sum_f_R0 (tg_alt (fun n => / INR (fact (2 * n + 1)) * toR x ^ (2 * n))%R) k).
    unfold Rdiv.
    rewrite (Rmult_comm (toR x ^ _)).
    replace (k + 1) with (S k) by ring.
    apply alternated_series_ineq'.
    apply Un_decreasing_sinc.
    lra.
    destruct (Req_dec (toR x) 0) as [Zx|Zx].
    rewrite Zx.
    intros eps Heps.
    exists 1%nat.
    intros n Hn.
    rewrite pow_ne_zero by (clear -Hn ; omega).
    unfold R_dist, Rminus.
    now rewrite Rmult_0_r, Rplus_opp_r, Rabs_R0.
    rewrite <- (Rmult_0_l (/toR x)).
    apply Un_cv_ext with (fun n : nat => (/ INR (fact (2 * n + 1)) * toR x ^ (2 * n + 1) * / toR x)%R).
    intros n.
    rewrite pow_add.
    field.
    split.
    apply Rgt_not_eq.
    apply INR_fact_lt_0.
    exact Zx.
    apply CV_mult.
    apply (Un_cv_subseq (fun n => (/ INR (fact n) * toR x ^ n)%R)).
    clear ; intros n ; omega.
    eapply Un_cv_ext.
    intros n.
    apply Rmult_comm.
    apply cv_speed_pow_fact.
    intros eps Heps.
    exists 0.
    intros _ _.
    unfold R_dist, Rminus.
    now rewrite Rplus_opp_r, Rabs_R0.
    unfold sinc.
    case exist_sin.
    intro l.
    change (projT1 _) with l.
    apply Un_cv_ext.
    intros n.
    apply sum_eq.
    intros i _.
    unfold sin_n, tg_alt.
    rewrite pow_Rsqr.
    apply Rmult_assoc.
    unfold Si, tg_alt.
    apply sum_eq.
    intros i _.
    apply sym_eq, Rmult_assoc.
  apply (conj (proj1 A)).
  assert (Hx2 := J.sqr_correct prec _ _ Ix).
  assert (H1 := J.mul_correct prec _ _ _ _ Hpow Hx2).
  assert (H2 := J.div_correct prec _ _ _ _ H1 Hdiv).
  destruct (I.convert (I.div prec _ _)) as [|l [|u]] ; try easy.
  apply Rle_trans with (1 := proj2 A).
  apply Rle_trans with (2 := proj2 H2).
  apply Req_le, Rmult_eq_compat_r.
  replace (2 * (k + 1)) with (2 * k + 2) by ring.
  now rewrite pow_add, Rsqr_pow2.
generalize (F.scale c1 (F.ZtoS (Z.neg (F.prec prec)))) (Pos.to_nat (F.prec prec)).
intros thre n.
replace 1%R with (Si (toR x) 0) by (unfold Si ; simpl ; field).
generalize (I.fromZ_correct 1) (I.fromZ_correct 6) (I.fromZ_correct 4).
fold i1 i6 i4.
generalize i1 i6 i4.
intros powi divi facti.
change 1%R with (pow (toR x) (2 * 0)).
change 4%Z with (Z_of_nat (2 * (0 + 1) + 2)).
change 6%Z with (Z_of_nat (fact (2 * (0 + 1) + 1))).
rewrite <- 2!INR_IZR_INZ.
replace (Si (toR x) 0%nat - sinc (toR x))%R with ((-1) * 1 * (sinc (toR x) - Si (toR x) 0%nat))%R by ring.
change (-1 * 1)%R with (pow (-1) (0 + 1)).
rewrite <- (minus_diag n) at 2 4 8 11 13.
generalize (le_refl n).
generalize n at 1 4 6 8 9 11 13.
intros m.
revert powi divi facti.
induction m as [|m IHm] ; intros powi divi facti Hm Hpow Hdiv Hfact.
  simpl cos_fast0_aux.
  cut (contains (I.convert (I.bnd F.zero (I.upper (I.div prec (I.mul prec powi x2i) divi))))
    (Xreal ((-1) ^ (n - 0 + 1) * (sinc (toR x) - Si (toR x) (n - 0))))).
  now destruct F'.cmp.
  now apply Hexit.
simpl cos_fast0_aux.
set (powi' := I.mul prec powi x2i).
set (divi' := I.mul prec divi (I.mul prec facti (I.add prec facti i1))).
set (facti' := I.add prec facti i2).
specialize (IHm powi' divi' facti').
assert (H: forall p, n - S m + S p = n - m + p).
  intros p.
  clear -Hm ; omega.
cut (contains (I.convert (I.sub prec (I.div prec powi' divi) (cos_fast0_aux prec thre powi' x2i facti' divi' m)))
    (Xreal ((-1) ^ (n - S m + 1) * (sinc (toR x) - Si (toR x) (n - S m))))).
  case F'.cmp ; try easy.
  intros H'.
  now apply Hexit.
replace ((-1) ^ (n - S m + 1) * (sinc (toR x) - Si (toR x) (n - S m)%nat))%R
  with ((-1) ^ (n - S m + 1) * (-1) ^ S (n - S m) * (toR x) ^ (2 * S (n - S m)) * / INR (fact (2 * S (n - S m) + 1)) - (((-1) * (-1) ^ (n - S m + 1)) * (sinc (toR x) - (Si (toR x) (n - S m)%nat + ((-1) ^ S (n - S m) * / INR (fact (2 * S (n - S m) + 1)) * (toR x) ^ (2 * S (n - S m)))))))%R by ring.
assert (Hpow': contains (I.convert powi') (Xreal (toR x ^ (2 * (n - S m + 1))))).
  replace (2 * (n - S m + 1)) with (2 * (n - S m) + 2) by ring.
  rewrite pow_add, <- Rsqr_pow2.
  apply J.mul_correct with (1 := Hpow).
  now apply J.sqr_correct.
apply J.sub_correct.
  rewrite <- pow_add.
  replace (n - S m + 1 + S (n - S m)) with (2 * (n - S m + 1)) by (clear -Hm ; omega).
  rewrite pow_1_even, Rmult_1_l.
  replace (S (n - S m)) with (n - S m + 1) by now rewrite plus_comm.
  now apply J.div_correct.
evar_last.
apply IHm.
clear -Hm ; lia.
now rewrite <- (plus_0_r (n - m)), <- H.
rewrite <- H.
replace (2 * (n - S m + 2) + 1) with (S (S (2 * (n - S m + 1) + 1))) by ring.
rewrite 2!fact_simpl.
rewrite 2!mult_INR, <- Rmult_assoc, Rmult_comm.
apply J.mul_correct with (1 := Hdiv).
rewrite Rmult_comm.
apply J.mul_correct.
now rewrite <- Nat.add_1_r, <- plus_assoc.
replace (S (S (2 * (n - S m + 1) + 1))) with (2 * (n - S m + 1) + 2 + 1) by ring.
rewrite plus_INR.
apply J.add_correct with (1 := Hfact).
apply I.fromZ_correct.
rewrite <- H.
replace (2 * (n - S m + 2) + 2) with (2 * (n - S m + 1) + 2 + 2) by ring.
rewrite plus_INR.
apply J.add_correct with (1 := Hfact).
apply I.fromZ_correct.
apply f_equal.
change (Si (toR x) (n - S m)%nat + (-1) ^ S (n - S m) * / INR (fact (2 * S (n - S m) + 1)) * toR x ^ (2 * S (n - S m)))%R
  with (Si (toR x) (S (n - S m))).
change (-1 * (-1) ^ (n - S m + 1))%R with ((-1) ^ (S (n - S m + 1)))%R.
rewrite <- plus_Sn_m.
now rewrite -> minus_Sn_m.
Qed.

(* 0 <= input *)
Definition sin_fastP prec x :=
  let th := F.scale2 c1 sm1 in
  match F'.le' x th with
  | true => sin_fast0 (F.incr_prec prec 1) x
  | _ =>
    let m := F.StoZ (F.mag x) in
    let prec := F.incr_prec prec (Z2P (m + 6)) in
    match sin_cos_reduce prec x (S (Z2nat m)) with
    | (s, c) =>
      let v := I.sqrt prec (I.sub prec (I.bnd c1 c1) (I.sqr prec c)) in
      match s with
      | Lt => I.neg v
      | Gt => v
      | _ => I.bnd (F.neg c1) c1
      end
    end
  end.

Lemma sin_fastP_correct :
  forall prec x,
  F.toX x = Xreal (toR x) ->
  (0 <= toR x)%R ->
  contains (I.convert (sin_fastP prec x)) (Xreal (sin (toR x))).
Proof.
intros prec x Hxr Hx0.
unfold sin_fastP.
case_eq (F'.le' x (F.scale2 c1 sm1)) ; intros Hx.
apply sin_fast0_correct.
easy.
rewrite Rabs_pos_eq with (1 := Hx0).
apply F'.le'_correct in Hx.
revert Hx.
unfold toR, sm1, c1.
rewrite Hxr, F.scale2_correct, F.fromZ_correct by easy.
simpl.
now rewrite Rmult_1_l.
generalize (S (Z2nat (F.StoZ (F.mag x)))) (F.incr_prec prec (Z2P (F.StoZ (F.mag x) + 6))).
intros nb prec'.
generalize (sin_cos_reduce_correct prec' nb x Hxr Hx0).
destruct sin_cos_reduce as [ss ci].
intros [Hc Hs].
destruct ss.
simpl.
unfold c1.
rewrite F.neg_correct, F.fromZ_correct.
apply SIN_bound.
rewrite <- (Ropp_involutive (sin (toR x))).
change (Xreal (- - sin (toR x))) with (Xneg (Xreal (- sin (toR x)))).
apply I.neg_correct.
rewrite <- Rabs_left1 with (1 := Hs).
rewrite <- sqrt_Rsqr_abs.
replace (Xreal (sqrt (sin (toR x))²)) with (Xsqrt (Xreal (sin (toR x))²)).
apply I.sqrt_correct.
rewrite sin2.
change (Xreal (1 - (cos (toR x))²)) with (Xsub (Xreal 1) (Xsqr (Xreal (cos (toR x))))).
apply I.sub_correct.
simpl.
unfold c1.
rewrite F.fromZ_correct.
split ; apply Rle_refl.
now apply I.sqr_correct.
unfold Xsqrt'.
simpl.
destruct (is_negative_spec (sin (toR x))²).
elim (Rlt_not_le _ _ H).
apply Rle_0_sqr.
apply refl_equal.
rewrite <- (Rabs_pos_eq (sin (toR x))) with (1 := Hs).
rewrite <- sqrt_Rsqr_abs.
replace (Xreal (sqrt (sin (toR x))²)) with (Xsqrt (Xreal (sin (toR x))²)).
apply I.sqrt_correct.
rewrite sin2.
change (Xreal (1 - (cos (toR x))²)) with (Xsub (Xreal 1) (Xsqr (Xreal (cos (toR x))))).
apply I.sub_correct.
simpl.
unfold I.convert_bound, c1.
rewrite F.fromZ_correct.
split ; apply Rle_refl.
now apply I.sqr_correct.
unfold Xsqrt'.
simpl.
destruct (is_negative_spec (sin (toR x))²).
elim (Rlt_not_le _ _ H).
apply Rle_0_sqr.
apply refl_equal.
Qed.

Definition sin_fast prec x :=
  match F'.cmp x F.zero with
  | Xeq => I.bnd F.zero F.zero
  | Xlt => I.neg (sin_fastP prec (F.neg x))
  | Xgt => sin_fastP prec x
  | Xund => I.nai
  end.

Theorem sin_fast_correct :
  forall prec x,
  contains (I.convert (sin_fast prec x)) (Xsin (F.toX x)).
Proof.
intros prec x.
unfold sin_fast.
rewrite F'.cmp_correct, F.zero_correct.
case_eq (F.toX x).
easy.
intros r Hr.
simpl.
case Rcompare_spec ; intros H.
(* neg *)
rewrite <- (Xneg_involutive (Xreal _)).
apply I.neg_correct.
simpl.
rewrite <- sin_neg.
replace (Ropp r) with (toR (F.neg x)).
apply sin_fastP_correct.
unfold toR.
now rewrite F.neg_correct, Hr.
unfold toR.
rewrite F.neg_correct, Hr.
rewrite <- Ropp_0.
apply Ropp_le_contravar.
now apply Rlt_le.
unfold toR.
now rewrite F.neg_correct, Hr.
(* zero *)
rewrite H, sin_0.
simpl.
rewrite F.zero_correct.
split ; apply Rle_refl.
(* pos *)
replace r with (toR x).
apply sin_fastP_correct.
unfold toR.
now rewrite Hr.
unfold toR.
rewrite Hr.
now apply Rlt_le.
unfold toR.
now rewrite Hr.
Qed.

(* 0 <= input *)
Definition tan_fastP prec x :=
  let th := F.scale2 c1 sm1 in
  match F'.le' x th with
  | true =>
    let prec := F.incr_prec prec 2 in
    let s := sin_fast0 prec x in
    I.div prec s (I.sqrt prec (I.sub prec i1 (I.sqr prec s)))
  | _ =>
    let m := F.StoZ (F.mag x) in
    let prec := F.incr_prec prec (Z2P (m + 7)) in
    match sin_cos_reduce prec x (S (Z2nat m)) with
    | (s, c) =>
      let v := I.sqrt prec (I.sub prec (I.div prec i1 (I.sqr prec c)) i1) in
      match s, I.sign_large c with
      | Lt, Xgt => I.neg v
      | Gt, Xlt => I.neg v
      | Lt, Xlt => v
      | Gt, Xgt => v
      | _, _ => I.nai
      end
    end
  end.

Definition tan_fast prec x :=
  match F'.cmp x F.zero with
  | Xeq => I.bnd F.zero F.zero
  | Xlt => I.neg (tan_fastP prec (F.neg x))
  | Xgt => tan_fastP prec x
  | Xund => I.nai
  end.

Lemma tan_fastP_correct :
  forall prec x,
  F.toX x = Xreal (toR x) ->
  (0 <= toR x)%R ->
  contains (I.convert (tan_fastP prec x)) (Xtan (Xreal (toR x))).
Proof.
intros prec x Rx Bx.
unfold tan_fastP.
case_eq (F'.le' x (F.scale2 c1 sm1)) ; intros Hx.
- apply F'.le'_correct in Hx.
  revert Hx.
  unfold toR, c1, sm1.
  rewrite Rx, F.scale2_correct, F.fromZ_correct by easy.
  intros Bx'.
  simpl in Bx'.
  change (Z.pow_pos 2 1) with 2%Z in Bx'.
  rewrite Rmult_1_l in Bx'.
  simpl proj_val.
  replace (Xtan (Xreal (toR x))) with (Xdiv (Xreal (sin (toR x))) (Xsqrt (Xsub (Xreal 1) (Xsqr (Xreal (sin (toR x))))))).
  apply I.div_correct.
  apply sin_fast0_correct with (1 := Rx).
  now rewrite Rabs_pos_eq.
  apply I.sqrt_correct.
  apply I.sub_correct.
  simpl.
  unfold I.convert_bound.
  rewrite F.fromZ_correct.
  split ; apply Rle_refl.
  apply I.sqr_correct.
  apply sin_fast0_correct with (1 := Rx).
  now rewrite Rabs_pos_eq.
  unfold Xsqrt'.
  simpl.
  case is_negative_spec.
  intros H.
  elim Rlt_not_le with (1 := H).
  apply Rle_0_minus.
  rewrite <- (Rmult_1_r 1).
  apply neg_pos_Rsqr_le ; apply SIN_bound.
  change (sin (toR x) * sin (toR x))%R with (Rsqr (sin (toR x))).
  rewrite <- cos2.
  intros H'.
  assert (Hc: (0 < cos (toR x))%R).
    apply cos_gt_0.
    apply Rlt_le_trans with (2 := Bx).
    apply Ropp_lt_gt_0_contravar.
    apply PI2_RGT_0.
    apply Rle_lt_trans with (1 := Bx').
    apply Rlt_trans with (2 := PI2_1).
    lra.
  unfold Xdiv'.
  case is_zero_spec.
  intros H.
  elim Rgt_not_eq with (1 := Hc).
  apply Rsqr_0_uniq.
  now apply sqrt_eq_0.
  intros H''.
  unfold Xtan'.
  simpl.
  case is_zero_spec.
  intros H.
  rewrite H in Hc.
  elim Rlt_irrefl with (1 := Hc).
  intros _.
  apply (f_equal (fun v => Xreal (_ / v))).
  apply sqrt_Rsqr.
  now apply Rlt_le.
- generalize (F.incr_prec prec (Z2P (F.StoZ (F.mag x) + 7))).
  clear prec. intros prec.
  generalize (sin_cos_reduce_correct prec (S (Z2nat (F.StoZ (F.mag x)))) x Rx Bx).
  case sin_cos_reduce.
  intros s c [Hc Hs].
  assert (H: contains (I.convert (I.sqrt prec (I.sub prec (I.div prec (I.bnd c1 c1) (I.sqr prec c)) (I.bnd c1 c1)))) (Xabs (Xdiv (Xreal (sin (toR x))) (Xreal (cos (toR x)))))).
    replace (Xabs (Xdiv (Xreal (sin (toR x))) (Xreal (cos (toR x)))))
      with (Xsqrt (Xsub (Xdiv (Xreal 1) (Xsqr (Xreal (cos (toR x))))) (Xreal 1))).
    apply I.sqrt_correct.
    apply I.sub_correct.
    apply I.div_correct.
    simpl.
    unfold I.convert_bound, c1.
    rewrite F.fromZ_correct.
    split ; apply Rle_refl.
    now apply I.sqr_correct.
    simpl.
    unfold I.convert_bound, c1.
    rewrite F.fromZ_correct.
    split ; apply Rle_refl.
    unfold Xdiv'.
    simpl.
    case is_zero_spec ; intros Zc.
    rewrite Rsqr_0_uniq with (1 := Zc).
    now rewrite is_zero_0.
    case is_zero_spec ; intros Zc'.
    rewrite Zc' in Zc.
    elim Zc.
    apply Rmult_0_l.
    unfold Xsqrt'.
    simpl.
    replace (1 / (Rsqr (cos (toR x))) - 1)%R with (Rsqr (sin (toR x) / cos (toR x))).
    case is_negative_spec ; intros H.
    elim Rlt_not_le with (1 := H).
    apply Rle_0_sqr.
    apply f_equal, sqrt_Rsqr_abs.
    rewrite Rsqr_div with (1 := Zc').
    rewrite sin2.
    unfold Rsqr.
    now field.
  unfold Xdiv', Xbind2 in H.
  generalize (I.sign_large_correct c).
  unfold Xtan', Xbind.
  destruct s ; try easy ; case I.sign_large ; try easy ; intros Hc'.
  destruct (is_zero_spec (cos (toR x))) as [H0|H0].
  easy.
  evar_last.
  apply H.
  apply (f_equal Xreal).
  apply Rabs_pos_eq.
  apply Rmult_le_neg_neg with (1 := Hs).
  apply Rlt_le, Rinv_lt_0_compat.
  apply Rnot_le_lt.
  contradict H0.
  apply Rle_antisym with (2 := H0).
  now specialize (Hc' _ Hc).
  rewrite <- (Xneg_involutive (if is_zero _ then _ else _)).
  apply I.neg_correct.
  destruct (is_zero_spec (cos (toR x))) as [H0|H0].
  easy.
  evar_last.
  apply H.
  apply (f_equal Xreal).
  apply Rabs_left1.
  apply Rmult_le_neg_pos with (1 := Hs).
  apply Rlt_le, Rinv_0_lt_compat.
  apply Rnot_le_lt.
  contradict H0.
  apply Rle_antisym with (1 := H0).
  now specialize (Hc' _ Hc).
  rewrite <- (Xneg_involutive (if is_zero _ then _ else _)).
  apply I.neg_correct.
  destruct (is_zero_spec (cos (toR x))) as [H0|H0].
  easy.
  evar_last.
  apply H.
  apply (f_equal Xreal).
  apply Rabs_left1.
  apply Rmult_le_pos_neg with (1 := Hs).
  apply Rlt_le, Rinv_lt_0_compat.
  apply Rnot_le_lt.
  contradict H0.
  apply Rle_antisym with (2 := H0).
  now specialize (Hc' _ Hc).
  destruct (is_zero_spec (cos (toR x))) as [H0|H0].
  easy.
  evar_last.
  apply H.
  apply (f_equal Xreal).
  apply Rabs_pos_eq.
  apply Rmult_le_pos_pos with (1 := Hs).
  apply Rlt_le, Rinv_0_lt_compat.
  apply Rnot_le_lt.
  contradict H0.
  apply Rle_antisym with (1 := H0).
  now specialize (Hc' _ Hc).
Qed.

Theorem tan_fast_correct :
  forall prec x,
  contains (I.convert (tan_fast prec x)) (Xtan (F.toX x)).
Proof.
intros prec x.
unfold tan_fast.
rewrite F'.cmp_correct, F.zero_correct.
case_eq (F.toX x).
easy.
intros r Hr.
simpl Xcmp.
case Rcompare_spec ; intros H.
(* neg *)
rewrite <- (Xneg_involutive (Xtan _)).
apply I.neg_correct.
generalize (tan_fastP_correct prec (F.neg x)).
unfold toR.
rewrite F.neg_correct, Hr.
simpl.
intros H'.
assert (H1 : (0 <= -r)%R).
  rewrite <- Ropp_0.
  apply Ropp_le_contravar.
  now apply Rlt_le.
specialize (H' eq_refl H1).
revert H'.
unfold Xtan'.
simpl.
rewrite cos_neg.
case is_zero_spec.
easy.
intros _.
now rewrite tan_neg.
(* zero *)
simpl.
rewrite H, F.zero_correct.
unfold Xtan'.
simpl.
case is_zero_spec.
rewrite cos_0.
apply R1_neq_R0.
intros _.
rewrite tan_0.
split ; apply Rle_refl.
(* pos *)
replace r with (toR x).
apply tan_fastP_correct.
unfold toR.
now rewrite Hr.
unfold toR.
rewrite Hr.
now apply Rlt_le.
unfold toR.
now rewrite Hr.
Qed.

Definition semi_extension f fi :=
  forall x, contains (I.convert (fi x)) (f (F.toX x)).

Definition cos_correct : forall prec, semi_extension Xcos (cos_fast prec) := cos_fast_correct.
Definition sin_correct : forall prec, semi_extension Xsin (sin_fast prec) := sin_fast_correct.
Definition tan_correct : forall prec, semi_extension Xtan (tan_fast prec) := tan_fast_correct.
Definition atan_correct : forall prec, semi_extension Xatan (atan_fast prec) := atan_fast_correct.

(* 0 <= inputs *)
Fixpoint expn_fast0_aux prec thre powi xi facti divi (nb : nat) { struct nb } :=
  let npwi := I.mul prec powi xi in
  let vali := I.div prec npwi divi in
  match F'.cmp (I.upper vali) thre, nb with
  | Xlt, _
  | _, O => I.bnd F.zero (I.upper vali)
  | _, S n =>
    let nfacti := I.add prec facti i1 in
    let ndivi := I.mul prec divi facti in
    I.sub prec vali (expn_fast0_aux prec thre npwi xi nfacti ndivi n)
  end.

(* 0 <= input <= 1/2 *)
Definition expn_fast0 prec x :=
  let p := F.prec prec in
  let thre := F.scale c1 (F.ZtoS (Zneg p)) in
  let xi := I.bnd x x in
  let rem := expn_fast0_aux prec thre xi xi i3 i2 (nat_of_P p) in
  I.sub prec i1 (I.sub prec xi rem).

(* 0 <= input *)
Definition expn_reduce prec x :=
  let th := F.scale2 c1 sm8 in
  match F'.le' x th with
  | true => expn_fast0 (F.incr_prec prec 1) x
  | false =>
    let m := F.StoZ (F.mag x) in
    let prec := F.incr_prec prec (Z2P (9 + m)) in
    let fix reduce x (nb : nat) {struct nb} :=
      match F'.le' x th, nb with
      | true, _ => expn_fast0 prec x
      | _, O => I.bnd F.zero c1
      | _, S n => I.sqr prec (reduce (F.scale2 x sm1) n)
      end in
    reduce x (8 + Z2nat m)
  end.

Definition exp_fast prec x :=
  match F'.cmp x F.zero with
  | Xeq => i1
  | Xlt => expn_reduce prec (F.neg x)
  | Xgt =>
    let prec := F.incr_prec prec 1 in
    match I.inv prec (expn_reduce prec x) with
    | Ibnd _ _ as b => b
    | Inai => I.bnd c1 F.nan
    end
  | Xund => I.nai
  end.

Lemma expn_fast0_correct :
  forall prec x,
  F.toX x = Xreal (toR x) ->
  (0 <= toR x <= /2)%R ->
  contains (I.convert (expn_fast0 prec x)) (Xreal (exp (- toR x))).
Proof.
intros prec x Rx Bx.
unfold expn_fast0.
replace (exp (-toR x)) with (1 - (toR x - (- (1 - toR x) + exp (-toR x))))%R by ring.
apply J.sub_correct.
apply I.fromZ_correct.
set (xi := I.bnd x x).
assert (Ix: contains (I.convert xi) (Xreal (toR x))).
  unfold xi.
  rewrite I.bnd_correct, Rx.
  split ; apply Rle_refl.
apply J.sub_correct with (1 := Ix).
assert (Hexit : forall k powi divi,
    contains (I.convert powi) (Xreal (toR x ^ (k + 1))) ->
    contains (I.convert divi) (Xreal (INR (fact (k + 2)))) ->
    contains (I.convert (I.bnd F.zero (I.upper (I.div prec (I.mul prec powi xi) divi))))
      (Xreal ((-1) ^ k * (exp (- toR x) + - E1 (- toR x) (k + 1))))).
  intros k powi divi Hpow Hdiv.
  rewrite I.bnd_correct.
  rewrite F.zero_correct, I.upper_correct.
  assert (A: (0 <= (-1) ^ k * (exp (- toR x) + - E1 (- toR x) (k + 1)) <= toR x ^ (k + 2) / INR (fact (k + 2)))%R).
    replace ((-1) ^ k)%R with ((-1) * ((-1) * (-1) ^ k))%R by ring.
    change ((-1) * ((-1) * (-1) ^ k))%R with ((-1) ^ (S (S k)))%R.
    unfold Rdiv.
    rewrite (Rmult_comm (toR x ^ (k + 2))).
    replace (E1 (- toR x) (k + 1)) with (sum_f_R0 (tg_alt (fun n => / INR (fact n) * toR x ^ n)%R) (k + 1)).
    rewrite <- (plus_n_Sm _ 1).
    replace (S k) with (k + 1) by ring.
    apply alternated_series_ineq'.
    apply Un_decreasing_exp.
    split.
    apply Bx.
    lra.
    eapply Un_cv_ext.
    intros n.
    apply Rmult_comm.
    apply cv_speed_pow_fact.
    generalize (E1_cvg (- toR x)).
    apply Un_cv_ext.
    intros n.
    unfold E1, tg_alt.
    apply sum_eq.
    intros i _.
    rewrite (Rmult_comm _ (toR x ^ i)), <- Rmult_assoc.
    rewrite <- Rpow_mult_distr.
    rewrite Rmult_comm.
    apply (f_equal (fun v => (v ^ i * _)%R)).
    ring.
    unfold E1, tg_alt.
    apply sum_eq.
    intros i _.
    unfold Rdiv.
    rewrite Rmult_comm, Rmult_assoc.
    rewrite <- Rpow_mult_distr.
    apply (f_equal (fun v => (_ * v ^ i)%R)).
    ring.
  apply (conj (proj1 A)).
  assert (H1 := J.mul_correct prec _ _ _ _ Hpow Ix).
  assert (H2 := J.div_correct prec _ _ _ _ H1 Hdiv).
  destruct (I.convert (I.div prec _ _)) as [|l [|u]] ; try easy.
  apply Rle_trans with (1 := proj2 A).
  apply Rle_trans with (2 := proj2 H2).
  apply Req_le, Rmult_eq_compat_r.
  rewrite <- plus_n_Sm.
  apply Rmult_comm.
generalize (F.scale c1 (F.ZtoS (Z.neg (F.prec prec)))) (Pos.to_nat (F.prec prec)).
intros thre n.
replace (1 - toR x)%R with (E1 (- toR x) (0 + 1)) by (unfold E1 ; simpl ; field).
generalize Ix (I.fromZ_correct 2) (I.fromZ_correct 3).
fold i2 i3.
generalize i2 i3.
generalize xi at 1 2.
intros powi divi facti.
rewrite <- (pow_1 (toR x)) at 1.
rewrite Rplus_comm.
change 1 with (0 + 1) at 1.
change 3%Z with (Z_of_nat (0 + 3)).
change 2%Z with (Z_of_nat (fact (0 + 2))).
rewrite <- 2!INR_IZR_INZ.
rewrite <- (Rmult_1_l (_ + _)).
change 1%R with ((-1)^0)%R.
rewrite <- (minus_diag n) at 1 3 5 7 8.
generalize (le_refl n).
generalize n at 1 4 6 8 9 11 13.
intros m.
revert powi divi facti.
induction m as [|m IHm] ; intros powi divi facti Hm Hpow Hdiv Hfact.
  simpl expn_fast0_aux.
  cut (contains (I.convert (I.bnd F.zero (I.upper (I.div prec (I.mul prec powi xi) divi))))
    (Xreal ((-1) ^ (n - 0) * (exp (- toR x) + - E1 (- toR x) (n - 0 + 1))))).
  now destruct F'.cmp.
  now apply Hexit.
simpl expn_fast0_aux.
set (powi' := I.mul prec powi xi).
set (divi' := I.mul prec divi facti).
set (facti' := I.add prec facti i1).
specialize (IHm powi' divi' facti').
assert (H: forall p, n - m + p = n - S m + p + 1).
  intros p.
  clear -Hm ; omega.
cut (contains (I.convert (I.sub prec (I.div prec powi' divi) (expn_fast0_aux prec thre powi' xi facti' divi' m)))
    (Xreal ((-1) ^ (n - S m) * (exp (- toR x) + - E1 (- toR x) (n - S m + 1))))).
  case F'.cmp ; try easy.
  intros H'.
  now apply Hexit.
replace ((-1) ^ (n - S m) * (exp (- toR x) + - E1 (- toR x) (n - S m + 1)))%R
  with ((toR x) ^ (n - m + 1) * / INR (fact (n - m + 1)) - (((-1) * (-1) ^ (n - S m)) * (exp (- toR x) + - E1 (- toR x) (n - S m + 1)) + / INR (fact (n - m + 1)) * (toR x) ^ (n - m + 1)))%R by ring.
change (-1 * (-1) ^ (n - S m))%R with ((-1) ^ (S (n - S m)))%R.
rewrite -> minus_Sn_m with (1 := Hm).
simpl (S n - S m).
assert (Hpow': contains (I.convert powi') (Xreal (toR x ^ (n - m + 1)))).
  rewrite H.
  rewrite pow_add, pow_1.
  now apply J.mul_correct.
apply J.sub_correct.
  apply J.div_correct with (1 := Hpow').
  now rewrite H, <- plus_assoc.
evar_last.
apply IHm.
clear -Hm ; lia.
exact Hpow'.
rewrite H.
rewrite plus_comm, fact_simpl.
rewrite mult_comm, mult_INR.
apply J.mul_correct with (1 := Hdiv).
now rewrite plus_n_Sm.
rewrite H.
rewrite plus_INR.
apply J.add_correct with (1 := Hfact).
apply I.fromZ_correct.
apply f_equal.
rewrite 2!Rmult_plus_distr_l.
rewrite Rplus_assoc.
apply f_equal.
rewrite <- plus_n_Sm at 1.
unfold E1.
change (sum_f_R0 (fun k : nat => / INR (fact k) * (- toR x) ^ k) (S (n - m + 0)))%R
  with (sum_f_R0 (fun k : nat => / INR (fact k) * (- toR x) ^ k) (n - m + 0) + / INR (fact (S (n - m + 0))) * (- toR x) ^ (S (n - m + 0)))%R.
rewrite H, <- plus_assoc at 1.
rewrite Ropp_plus_distr, Rmult_plus_distr_l.
apply f_equal.
rewrite <- Ropp_mult_distr_r_reverse.
rewrite (Rmult_comm (_ ^ _)), Rmult_assoc.
rewrite plus_n_Sm.
apply f_equal.
replace (- (- toR x) ^ (n - m + 1) * (-1) ^ (n - m))%R
  with ((- toR x) ^ (n - m + 1) * ((-1) * (-1) ^ (n - m)))%R by ring.
change (-1 * (-1) ^ (n - m))%R with ((-1) ^ (S (n - m)))%R .
rewrite <- plus_n_Sm, <- plus_n_O.
rewrite <- Rpow_mult_distr.
now replace (- toR x * -1)%R with (toR x) by ring.
Qed.

Lemma expn_reduce_correct :
  forall prec x,
  F.toX x = Xreal (toR x) ->
  (0 < toR x)%R ->
  contains (I.convert (expn_reduce prec x)) (Xreal (exp (- toR x))).
Proof.
assert (forall prec x,
  F.toX x = Xreal (toR x) ->
  (0 < toR x)%R -> F'.le' x (F.scale2 c1 sm8) = true ->
  contains (I.convert (expn_fast0 prec x)) (Xreal (exp (- toR x)))).
intros prec x Hx1 Hx2 Hx3.
apply expn_fast0_correct.
exact Hx1.
split.
now apply Rlt_le.
apply F'.le'_correct in Hx3.
revert Hx3.
rewrite Hx1.
unfold c1, sm8.
rewrite F.scale2_correct, F.fromZ_correct by easy.
simpl.
intros Hx3.
apply Rle_trans with (1 := Hx3).
rewrite Rmult_1_l.
apply Rle_Rinv_pos.
now apply IZR_lt.
now apply IZR_le.
(* . *)
intros prec x Hx H0.
unfold expn_reduce.
case_eq (F'.le' x (F.scale2 c1 sm8)) ; intros Hx'.
(* . no reduction *)
now apply H.
(* . reduction *)
clear Hx'.
generalize (F.incr_prec prec (Z2P (9 + F.StoZ (F.mag x)))).
clear prec. intro prec.
generalize (8 + Z2nat (F.StoZ (F.mag x))).
intro nb.
revert x Hx H0.
induction nb ; intros ; simpl.
(* nb = 0 *)
case_eq (F'.le' x (F.scale2 c1 sm8)) ; intros Hx'.
now apply H.
simpl.
unfold c1.
rewrite F.zero_correct, F.fromZ_correct.
split.
apply Rlt_le.
apply exp_pos.
simpl.
rewrite <- exp_0.
apply Rlt_le.
apply exp_increasing.
rewrite <- Ropp_0.
now apply Ropp_lt_contravar.
(* nb > 0 *)
case_eq (F'.le' x (F.scale2 c1 sm8)) ; intros Hx'.
now apply H.
assert (toR (F.scale2 x sm1) = toR x * /2)%R.
unfold toR, sm1.
now rewrite F.scale2_correct, Hx.
replace (toR x) with (toR (F.scale2 x sm1) + toR (F.scale2 x sm1))%R.
rewrite Ropp_plus_distr.
rewrite exp_plus.
change (Xreal (exp (- toR (F.scale2 x sm1)) * exp (- toR (F.scale2 x sm1))))
  with (Xsqr (Xreal (exp (- toR (F.scale2 x sm1))))).
apply I.sqr_correct.
apply IHnb.
unfold toR, sm1.
now rewrite F.scale2_correct, Hx.
rewrite H1.
apply Rmult_lt_0_compat.
exact H0.
apply Rinv_0_lt_compat, Rlt_0_2.
rewrite H1.
apply sym_eq, double_var.
Qed.

Theorem exp_fast_correct :
  forall prec x,
  contains (I.convert (exp_fast prec x)) (Xexp (F.toX x)).
Proof.
intros prec x.
unfold exp_fast.
rewrite F'.cmp_correct, F.zero_correct.
case_eq (F.toX x).
easy.
intros r Hr.
(* neg *)
simpl.
case Rcompare_spec ; intros H.
replace r with (Ropp (toR (F.neg x))).
apply expn_reduce_correct.
unfold toR.
now rewrite F.neg_correct, Hr.
unfold toR.
rewrite F.neg_correct, Hr.
rewrite <- Ropp_0.
now apply Ropp_lt_contravar.
unfold toR.
rewrite F.neg_correct, Hr.
apply Ropp_involutive.
(* zero *)
simpl.
unfold c1.
rewrite F.fromZ_correct.
rewrite H, exp_0.
split ; apply Rle_refl.
(* pos *)
generalize (F.incr_prec prec 1).
clear prec. intro prec.
case_eq (I.inv prec (expn_reduce prec x)) ; intros.
(* pos too big *)
split ; unfold c1.
rewrite F.fromZ_correct.
simpl.
rewrite <- exp_0.
apply Rlt_le.
now apply exp_increasing.
now rewrite F.nan_correct.
(* pos fine *)
rewrite <- H0.
rewrite <- (Ropp_involutive r).
rewrite exp_Ropp.
replace (Xreal (/ exp (- r))) with (Xinv (Xreal (exp (- toR x)))).
apply I.inv_correct.
apply expn_reduce_correct.
unfold toR.
now rewrite Hr.
unfold toR.
now rewrite Hr.
unfold toR.
rewrite Hr.
unfold Xinv'.
simpl.
case is_zero_spec ; intro H1.
elim Rgt_not_eq with (2 := H1).
apply exp_pos.
apply refl_equal.
Qed.

End TranscendentalFloatFast.

(*
Require Import Interval_specific_ops.
Require Import Interval_stdz_carrier.
Module F := SpecificFloat StdZRadix2.
Module A := TranscendentalFloatFast F.
Time Eval vm_compute in (A.exp_fast 50%Z (Float 201%Z (-8)%Z)).
Time Eval vm_compute in (A.atan_fast 50%Z (Float 201%Z (-8)%Z)).
Time Eval vm_compute in (A.cos_fast 50%Z (Float 201%Z (-8)%Z)).
Time Eval vm_compute in (A.tan_fast 50%Z (Float 3619%Z (-8)%Z)).
Time Eval vm_compute in (A.sin_fast 50%Z (Float 201%Z (-8)%Z)).
Time Eval vm_compute in (A.ln_fast 50%Z (Float 1%Z 20009%Z)).
Time Eval vm_compute in (A.ln_fast 50%Z (Float 1125899906842623%Z (-50)%Z)).
*)
