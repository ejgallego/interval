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
Require Import Interval_xreal.
Require Import Interval_xreal_derive.
Require Import Interval_missing.
Require Import Interval_generic_proof.
Require Import Rstruct.
Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq fintype bigop.
Require Import xreal_ssr_compat.
Require Import seq_compl.

(** Describe the n-th derivatives for several basic functions *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section generic.

Definition nth_derivable_pt (f : R ->R) (Df : nat -> R -> R) x :=
  (forall y, f y = Df 0%nat y) /\
  forall k, derivable_pt_lim (Df k) x (Df (S k) x).

Definition nth_Xderive_pt Xf XDf x :=
  (forall y, Xf y = XDf 0%nat y) /\
  forall k: nat, Xderive_pt (XDf k) x (XDf (S k) x).

End generic.

Section nth_exp.

Lemma nth_derivable_pt_exp x : nth_derivable_pt exp (fun _ => exp) x.
Proof. split=>// _;apply: derivable_pt_lim_exp. Qed.

Lemma nth_Xderive_pt_exp x : nth_Xderive_pt Xexp (fun _ => Xexp) x.
Proof.
split=>// k.
have Hder :=
  Xderive_pt_exp (fun x => x) (Xmask (Xreal 1) x) x (Xderive_pt_identity x).
replace (Xexp x) with (Xmask (Xreal 1) x * Xexp x)%XR=>//.
by case x=>//= r; rewrite Rmult_1_l.
Qed.

End nth_exp.

Section nth_pow.

Lemma nth_derivable_pt_pow n x :
  nth_derivable_pt (fun x => x ^ n)%Re
  (fun k x => \big[Rmult/1]_(i < k) INR (n - i) * x^(n - k))%Re x.
Proof.
split => k; first by rewrite big_ord0 subn0 Rmult_1_l.
rewrite big_ord_recr /= Rmult_assoc.
apply:derivable_pt_lim_scal.
replace (n - k.+1)%nat with (predn (n-k)).
  by apply derivable_pt_lim_pow.
by rewrite -/predn subnS.
Qed.

Lemma nth_Xderive_pt_pow n x :
  nth_Xderive_pt (fun x => x ^ n)%XR
  (fun k x => \big[Xmul/Xreal 1]_(i < k) Xreal (INR (n - i)) * x^(n - k))%XR x.
Proof.
split=>[y | k].
  by rewrite big_ord0 subn0; case: (y ^ n)%XR => // r; rewrite Xmul_1_l.
rewrite big_ord_recr /=.
have -> : (\big[Xmul/Xreal 1]_(i < k) Xreal (INR (n - i)))%XR =
      Xreal (\big[Rmult/R1]_(i < k) (INR (n - i))).
  elim: k; first by rewrite !big_ord0.
  by move=> k Hrec; rewrite !big_ord_recr Hrec.
set b := Xreal _.
have H := Xderive_pt_mul (fun _ => b) (fun x => x ^ (n - k))%XR
 _ _ x (Xderive_pt_constant (\big[Rmult/1%Re]_(i < k) INR (n - i))x).
rewrite Xmul_comm (Xmul_comm b) -Xmul_assoc.
set e:= (x ^ (n - k.+1) * Xreal (INR (n - k)))%XR.
have -> : (e * b)%XR= ((Xmask (Xreal 0) x * x ^ (n - k) + e * b))%XR.
  rewrite /e=> {e H}.
  case : x; first by rewrite Xpow_idem Xpow_Xnan.
  by move=> r; rewrite !Xpow_idem !Xpow_Xreal /= Rmult_0_l Rplus_0_l.
apply: H; rewrite /e Xmul_comm subnS.
move: (Xderive_pt_Xpow (n - k) (Xderive_pt_identity x)).
case : x {e}; first by rewrite Xmul_comm Xpow_idem Xpow_Xnan /=.
by move=> r; rewrite Xmul_1_r.
Qed.

Lemma nth_Xderive_pt_power_int (n : Z) x :
  nth_Xderive_pt (fun x => Xpower_int x n)%XR
  (fun k x => (\big[Xmul/Xreal 1]_(i < k) Xreal (IZR (n - Z.of_nat i))) *
              (if Z.ltb n Z0 || Z.geb n (Z.of_nat k) then
                 Xpower_int x (n - Z.of_nat k)%Z
               else Xmask (Xreal 0) x))%XR x.
Proof.
split=>[y | k].
  rewrite big_ord0 Xmul_1_l Zminus_0_r.
  by rewrite ifT; case: n.
rewrite big_ord_recr /=.
have -> : (\big[Xmul/Xreal 1]_(i < k) Xreal (IZR (n - Z.of_nat i)))%XR =
      Xreal (\big[Rmult/R1]_(i < k) (IZR (n - Z.of_nat i))).
  elim: k; first by rewrite !big_ord0.
  by move=> k Hrec; rewrite !big_ord_recr Hrec.
set b := Xreal _.
have H := Xderive_pt_mul (fun _ => b) (fun x => Xpower_int x (n - Z.of_nat k))%XR
 _ _ x (Xderive_pt_constant (\big[Rmult/1%Re]_(i < k) IZR (n - Z.of_nat i))x).
rewrite Xmul_comm (Xmul_comm b) -Xmul_assoc.
case E :((n <? 0)%Z || (n >=? Z.pos (Pos.of_succ_nat k)))%Z.
eapply Xderive_pt_eq_fun.
move=> y.
rewrite ifT.
reflexivity.
case/orP: E =>[->//|].
do 2! case: Z.geb_spec =>//.
by rewrite orbC.
intros; zify; romega.

set e:= (Xpower_int x (n - Z.of_nat k.+1) * Xreal (IZR (n - Z.of_nat k)))%XR.
have -> : (e * b)%XR= ((Xmask (Xreal 0) x * Xpower_int x (n - Z.of_nat k) + e * b))%XR.
  rewrite /e=> {e H}.
  case : x; first done.
  move=> r.
  rewrite Xmul_0_l.
  set x0 := Xmask _ _.
rewrite /= /x0 /=.
case: (Req_EM_T r R0) => Hr; case Enk: (n - Z.of_nat k.+1)%Z @b @x0 =>[|p|p] b x0.
have->: (n - Z.of_nat k)%Z = 1%Z by zify; romega.
simpl.
by rewrite Rplus_0_l.
have->: (n - Z.of_nat k)%Z = Z.pos (Pos.succ p)%Z by zify; romega.
by rewrite Xadd_0_l.
by rewrite zeroT //= Xadd_comm.
have->: (n - Z.of_nat k)%Z = 1%Z by zify; romega.
by rewrite Xadd_0_l.
have->: (n - Z.of_nat k)%Z = Z.pos (Pos.succ p)%Z by zify; romega.
by rewrite Xadd_0_l.
rewrite zeroF //.
case E': (n - Z.of_nat k)%Z => [|q|q]; try (zify; romega).
by rewrite /= Rplus_0_l.
by rewrite /= Rplus_0_l.
(* . *)
apply: H; rewrite /e.
have := (Xderive_pt_power_int (n - Z.of_nat k) _ _ _ (Xderive_pt_identity x)).
(* Check Xderive_pt_eq_fun. *)
congr Xderive_pt.
case: x {e} =>[//|r].
simpl.
set nk := (n - Z.pos (Pos.of_succ_nat k))%Z.
have->: Z.pred (n - Z.of_nat k)%Z = nk by rewrite /nk; zify; romega.
case: nk =>//=.
by rewrite Z2R_IZR Rmult_1_r.
by move=> p; rewrite Rmult_1_l Rmult_comm Z2R_IZR.
move=> p; case: is_zero =>//=.
by rewrite Rmult_1_l Rmult_comm Z2R_IZR.

case E' :((n <? 0)%Z || (n >=? Z.of_nat k))%Z.
suff->: n = Z.of_nat k.
rewrite Z.sub_diag.
rewrite /Xpower_int.
case: x H => [//|x] H.
move=> v.
rewrite !Rmult_0_l.
exact: derivable_pt_lim_const.
have [H1 H2] := Bool.orb_false_elim _ _ E.
case: Z.geb_spec H2=>// H2.
rewrite H1 /= in E'.
case: Z.geb_spec E'=>// E'.
move=> _ _; zify; omega.
case: x {H}; first done.
move=> r.
rewrite /= !Rmult_0_l.
exact: derivable_pt_lim_const.
Qed.

Lemma nth_derivable_pt_inv_pow n x :
  x <> R0 ->
  nth_derivable_pt (fun x => / x ^ n)%Re
  (fun k x => \big[Rmult/1%Re]_(i < k) - INR (n + i) * /x^(n + k))%Re x.
Proof.
split=>[y | k]; first by rewrite big_ord0 addn0 Rmult_1_l.
rewrite big_ord_recr /= Rmult_assoc.
apply: derivable_pt_lim_scal.
apply: (derivable_pt_lim_eq (fun y => 1/y^(n+k))%Re).
  by move=> y; rewrite /Rdiv Rmult_1_l.
have Hd := derivable_pt_lim_div (fun _ => 1%Re) (fun x => x ^ (n+k))%Re x 0%Re _
  (derivable_pt_lim_const 1%Re x) (derivable_pt_lim_pow x (n+k))
  (pow_nonzero _ _ H).
replace (- INR (n + k) * / x ^ (n + k.+1))%Re with
  ((0 * x ^ (n + k) - INR (n + k) * x ^ predn (n + k) * 1) /
        (x ^ (n + k))²)%Re => //=.
rewrite addnS Rmult_0_l Rmult_1_r.
set (p := (n+k)%nat).
rewrite /Rsqr; field_simplify; [|by apply pow_nonzero|by apply pow_nonzero].
case cp : p => [|p' ] /=; field=>//.
by split; [apply pow_nonzero|].
Qed.

End nth_pow.

Section inverse.

Lemma nth_derivable_pt_inv x :
  x <> R0 ->
  nth_derivable_pt (fun x => / x)%Re
  (fun k x => \big[Rmult/1]_(i < k) - INR (i.+1) * /x^(k.+1))%Re x.
Proof.
move=> Hx;split=> k; first by rewrite /= big_ord0 Rmult_1_l Rmult_1_r.
case: (nth_derivable_pt_inv_pow 1 Hx) => [_ /(_ k)].
apply: (derivable_pt_lim_eq
  (fun x : R => (\big[Rmult/1]_(i < k) - INR (1 + i) * / x ^ (1 + k))%R)).
move=> y;rewrite add1n; apply Rmult_eq_compat_r.
by apply eq_bigr=> *; rewrite add1n.
Qed.

Lemma nth_Xderive_pt_inv x :
  nth_Xderive_pt (fun x => Xinv x)
  (fun k x => ((- Xreal 1) ^ k * Xreal (INR (fact k)) * Xmask (Xreal 1) x /
    x ^ k.+1)%XR) x.
Proof.
split=> [| k].
  by case=>//= y; rewrite /Rdiv !Rmult_1_r Rmult_1_l.
have -> : ((- Xreal 1) ^ k * Xreal (INR (fact k)))%XR =
 Xreal ((- 1) ^ k * INR (fact k))%R.
  by rewrite Xpow_idem Xpow_Xreal.
have Hdiv := Xderive_pt_div
  (fun x => (Xreal ((-1) ^ k * INR (fact k)) * (Xmask (Xreal 1) x))%XR)
  (fun x => x ^ k.+1)%XR
  (Xmask (Xreal 0) x)
  (Xreal (INR k.+1) * x ^ k * (Xmask (Xreal 1) x))%XR
  x
  (Xderive_pt_mulXmask ((-1) ^ k * INR (fact k))%R x)
  (Xderive_pt_Xpow (k.+1) (Xderive_pt_identity x)).
suff <- : ((Xmask (Xreal 0) x * x ^ k.+1 -
           Xreal (INR k.+1) * x ^ k * Xmask (Xreal 1) x *
           (Xreal ((-1) ^ k * INR (fact k)) * Xmask (Xreal 1) x)) /
          (x ^ k.+1 * x ^ k.+1))%XR =
  ((- Xreal 1) ^ k.+1 * Xreal (INR (fact k.+1)) * Xmask (Xreal 1) x /
   x ^ k.+2)%XR by [].
case Cx : x => [|rx] //.
rewrite !Xpow_idem !Xpow_Xreal /= Rmult_0_l Rmult_1_r /=.
case:(Req_EM_T rx R0)=>[->|Hneq]; first by rewrite !Rmult_0_l is_zero_correct_zero.
have Hpow0 : forall i, (rx ^ i)%R = R0 -> rx = R0.
  elim; first by move => H; case: (R1_neq_R0).
  by move=> n /= Hi /Rmult_integral; case.
have -> : is_zero (rx * rx ^ k * (rx * rx ^ k)) = false.
  rewrite /is_zero /Req_bool.
  case Rceq : (Rcompare (rx * rx ^ k * (rx * rx ^ k)) 0)=>//.
  have: (rx * rx ^ k * (rx * rx ^ k))%R = R0 by apply Rcompare_Eq_inv.
  by move/Rmult_integral; case;move/(Hpow0 k.+1).
have -> : is_zero (rx * (rx * rx ^ k)) = false.
  rewrite /is_zero /Req_bool.
  case Rceq: (Rcompare (rx * (rx * rx ^ k)) 0)=>//.
  move/Rcompare_Eq_inv: Rceq.
  by move/Rmult_integral; case=>// /(Hpow0 k.+1).
f_equal; field_simplify; first last.
    by split=> //; apply pow_nonzero.
  by split=> //; apply pow_nonzero.
replace (INR (fact k + (k * fact k)%coq_nat)%coq_nat) with
     (INR (fact k.+1))=>//.
have He : (match k with
                | 0%N => R1
                | _.+1 => (INR k + 1)%R
              end) = (INR k.+1) by [].
rewrite He; field_simplify; first last.
    by split=>//; apply pow_nonzero.
  by split=>//; apply pow_nonzero.
replace ((-INR k.+1 * (-1) ^ k * INR (fact k))%R) with
        (-(-1) ^ k * INR (fact k.+1))%R =>//.
by rewrite /= plus_INR He S_INR mult_INR; ring.
Qed.

End inverse.

Section power.

Lemma nth_derivable_pt_power a x :
  (0 < x)%Re ->
  nth_derivable_pt (fun x => Rpower x a)
  (fun k x =>
    \big[Rmult/1%Re]_(i < k) (a - INR i) * Rpower x (a - INR k))%Re x.
Proof.
move=> hx; split=>[y|k].
  by rewrite big_ord0 Rmult_1_l Rminus_0_r.
rewrite big_ord_recr Rmult_assoc; apply derivable_pt_lim_scal.
replace (a - INR k.+1)%Re with (a - INR k -1)%Re; last by (rewrite S_INR; ring).
by apply derivable_pt_lim_power.
Qed.

End power.

Section square_root.

(*
Fixpoint nth_sqrt k x :
 match k with 0 => sqrt x
  | S n =>
let nn := INR n in
let n1 := INR n.-1 in
let one := INR 1 in
let two := INR 2 in
((one - (two * n1)) * (nth_sqrt n x)) / (two * x *nn)
end.
*)

Lemma nth_derivable_pt_sqrt x :
  (0 < x)%Re ->
  nth_derivable_pt sqrt
  (fun k x => match k with 0 => sqrt x | _ =>
  \big[Rmult/1]_(i < k) (/2 - INR i) * Rpower x (/2 - INR k) end)%Re x.
Proof.
move=> Hx; case: (nth_derivable_pt_power (/2) Hx)=> [H1 H2].
split=>//; case=>//.
have Hs := derivable_pt_lim_sqrt x Hx.
replace ((\big[Rmult/1]_(i < 1) (/ 2 - INR i) * Rpower x (/ 2 - INR 1)))%Re with
  (/(2 * sqrt x))%Re; first by [].
rewrite big_ord_recl big_ord0 /= Rmult_1_r Rminus_0_r.
replace (/2 - 1)%Re with (-/2)%Re by field.
rewrite Rpower_Ropp Rpower_sqrt //.
by field; apply Rgt_not_eq; apply sqrt_lt_R0.
Qed.

Lemma nth_Xderive_pt_sqrt (x : ExtendedR) :
  nth_Xderive_pt (fun x => Xsqrt x)
  (fun k x => \big[Xmul/Xreal 1]_(i < k) Xreal (/2 - INR i) * ((Xsqrt x)/ x ^ k))%XR x.
Proof.
split=>[y|k].
  rewrite big_ord0 Xmul_1_l; case: y =>// r.
  rewrite Xpow_idem Xpow_Xreal Xdiv_split.
  suff -> : Xinv (Xreal (pow r 0)) = Xreal 1 by rewrite Xmul_1_r.
  by rewrite /= zeroF ?Rinv_1 //; apply:R1_neq_R0.
rewrite big_ord_recr /=.
have -> : (\big[Xmul/Xreal 1]_(i < k) Xreal (/2 - INR i))%XR =
      Xreal (\big[Rmult/R1]_(i < k) (/2 - INR i))%Re.
  elim: k; first by rewrite !big_ord0.
  by move=> k Hrec; rewrite !big_ord_recr Hrec.
set b := Xreal _.
have H := Xderive_pt_mul (fun _ => b) (fun x => (Xsqrt x / x ^ k))%XR
 _ _ x (Xderive_pt_constant (\big[Rmult/1]_(i < k) (/ 2 - INR i))%Re x).
rewrite Xmul_comm (Xmul_comm b) -Xmul_assoc.
set e := (Xsqrt x / x ^ k.+1 * Xreal (/ 2 - INR k))%XR.
have -> : (e * b)%XR= ((Xmask (Xreal 0) x * (Xsqrt x / x ^ k)+ e * b))%XR.
  rewrite /e {e H}.
  case : x; first by rewrite Xpow_idem Xpow_Xnan.
  move=> r; rewrite !Xpow_idem !Xpow_Xreal; case: (Xsqrt (Xreal r))=>//= r0.
  case : (boolP (r == R0)).
    move/eqP => ->; rewrite Rmult_0_l /=.
    by rewrite is_zero_correct_zero Xadd_comm.
  move/eqP=> rn0.
  case: (boolP (r ^ k == 0)%Re)=> Hrk0.
    by move/eqP:(Hrk0); move:(pow_nonzero r k rn0).
  move/eqP/zeroF :(Hrk0)=> ->.
  case: (boolP ((r * r ^ k)==0))%Re =>Hrkp10.
    move/eqP:Hrkp10; move -> => /=.
    by rewrite zeroT.
  move/eqP/zeroF :(Hrkp10)=> ->.
  by rewrite Rmult_0_l Xadd_0_l.
apply:H; rewrite /e.
have Hi:=(Xderive_pt_sqrt _ _ _ (Xderive_pt_identity x)).
have Hpow:= (Xderive_pt_Xpow k (Xderive_pt_identity x)).
move: (Xderive_pt_div (fun x => Xsqrt x) (fun x => x ^ k)%XR _ _ _ Hi Hpow).
suff <-: ((Xmask (Xreal 1) x / (Xsqrt x + Xsqrt x) * x ^ k -
    Xreal (INR k) * x ^ k.-1 * Xmask (Xreal 1) x * Xsqrt x) / (x ^ k * x ^ k))%XR =
(Xsqrt x / x ^ k.+1 * Xreal (/ 2 - INR k))%XR.
  by apply.
clear e Hi Hpow b.
case: x=> // r.
have -> : (Xmask (Xreal 1) (Xreal r)) = (Xreal 1) by [].
have -> : forall x, (x + x)%XR = (Xreal 2 * x)%XR.
  by case=> //= r0; rewrite RIneq.double.
set s := Xsqrt (Xreal r).
rewrite Xmul_1_r !Xdiv_split Xmul_1_l.
rewrite /s [Xsqrt _]/=.
case: (boolP (is_negative r))=>//.
rewrite !Xpow_idem !Xpow_Xreal /=;move/negbTE=> rpos.
have rge0: (0 <= r)%Re.
  move:rpos; rewrite /is_negative.
  case: (Rlt_bool_spec 0 r).
    move => rpos Hf; apply:Rcompare_not_Gt_inv.
    by rewrite (Rcompare_Lt _ _ rpos).
  case/Rle_lt_or_eq_dec; first by move/Rlt_bool_true ->.
  by move -> => _; apply:Rle_refl.
case: (boolP (r == 0)%Re) =>/eqP.
  by move->; rewrite sqrt_0 Rmult_0_l Rmult_0_r is_zero_correct_zero.
move=> rn0.
have: sqrt r <> R0 => hsq.
  by apply: rn0;rewrite (sqrt_eq_0 r).
have h2n0 : 2%Re <> R0.
  move/Rlt_not_eq: Rlt_0_2 => // Hdiff Heq.
  by rewrite Heq in Hdiff.
case: (boolP (2 * sqrt r == 0))%Re.
  by move/eqP=> r0; case: (Rmult_integral _ _ r0).
move/eqP=> Hr; rewrite (zeroF Hr) /=.
case: (boolP ((r * r ^ k) == 0))%Re.
  move/eqP=> r0; rewrite r0 /= is_zero_correct_zero.
  case: (Rmult_integral _ _ r0)=> //.
  by move => h; rewrite h Rmult_0_r is_zero_correct_zero.
move/eqP=> Hrk; rewrite (zeroF Hrk) /=.
case: (Rmult_neq_0_reg _ _ Hrk)=> _.
case: (boolP ((r ^ k * r ^ k)== 0))%Re.
  move/eqP=> r0.
  by case: (Rmult_integral _ _ r0)=> //.
move/eqP=> Hr0; rewrite (zeroF Hr0) /=.
case : k Hrk Hr0.
  rewrite pow_O !Rmult_1_r Rmult_0_l !Rminus_0_r.
  move=> *.
  rewrite Rmult_comm.
  suff->: (/ 1 * / (2 * sqrt r) = sqrt r * / r * / 2)%Re by done.
  by rewrite -{3}(sqrt_sqrt r) //; field.
move=> k *.
suff->:
     ((/ (2 * sqrt r) * r ^ k.+1 - INR k.+1 * r ^ k.+1.-1 * sqrt r) *
      / (r ^ k.+1 * r ^ k.+1) =
   sqrt r * / (r * r ^ k.+1) * (/ 2 - INR k.+1))%Re by [].
have ->: (sqrt r * / (r * r ^ k.+1) * (/ 2 - INR k.+1)=
          (/ 2 - INR k.+1)/ (sqrt r * r ^k.+1))%Re.
  by rewrite -{2}(sqrt_sqrt r) //; field; split.
rewrite Rinv_mult_distr // Rmult_assoc.
have ->: ((/ sqrt r) * r ^ k.+1 = r ^ k.+1.-1 * sqrt r)%Re.
  by rewrite /= - {2}(sqrt_sqrt r) //; field.
rewrite Rmult_assoc -Rmult_minus_distr_r /Rdiv.
have->: ((/ 2 - INR k.+1) * (r ^ k.+1.-1 * sqrt r) * / (r ^ k.+1 * r ^ k.+1)
= (/ 2 - INR k.+1) * ((r ^ k.+1.-1 * sqrt r) * / (r ^ k.+1 * r ^ k.+1)))%Re by field.
congr Rmult;rewrite Rinv_mult_distr // Rmult_comm Rmult_assoc.
suff->: (/ r ^ k.+1 * (r ^ k.+1.-1 * sqrt r) = /sqrt r)%Re by field.
have->: (r ^ k.+1 = r * r^k)%Re by done.
rewrite -{1} (sqrt_sqrt r) //.
by rewrite Rmult_comm /=;field; split => //; apply:pow_nonzero.
Qed.

Lemma nth_Xderive_pt_invsqrt (x : ExtendedR) :
  nth_Xderive_pt (fun x => Xinv (Xsqrt x))
  (fun k x => \big[Xmul/Xreal 1]_(i < k) Xreal (- / 2 - INR i) *
    (Xinv (Xsqrt x) / x ^ k))%XR x.
Proof.
split.
  case.
    by rewrite /= big_ord0 Xmul_1_l.
  move=> r; rewrite big_ord0 Xmul_1_l.
  by rewrite Xpow_idem Xpow_Xreal /= Xdiv_split Xinv_1 Xmul_1_r.
move=> k; rewrite big_ord_recr /=.
(* lemme a ajouter *)
have -> : (\big[Xmul/Xreal 1]_(i < k) Xreal (-/2 - INR i))%XR =
      Xreal (\big[Rmult/R1]_(i < k) (-/2 - INR i)%Re).
  elim: k; first by rewrite !big_ord0.
  by move=> k Hrec; rewrite !big_ord_recr Hrec.
set p := Xreal _.
have H := Xderive_pt_mul (fun _ => p) (fun x => (Xinv (Xsqrt x) / x ^ k))%XR
 _ _ x (Xderive_pt_constant (\big[Rmult/R1]_(i < k) (-/ 2 - INR i)%Re) x).
rewrite Xmul_assoc.
set e := ((Xreal _) * _)%XR.
have <- : (Xmask (Xreal 0) x * (Xinv (Xsqrt x) / x ^ k)+ e * p)%XR = (p * e)%XR.
rewrite /e {e H}.
  case: x; first by rewrite Xmul_comm.
  move => r.
  rewrite Xmul_0_l.
  case: (boolP (is_negative r)); first by rewrite /=; move ->.
  move/negbTE=> rpos.
  case: (boolP (r == 0))%Re; move/eqP => r0.
    rewrite r0.
    have -> : (Xsqrt (Xreal 0))= Xreal 0.
      by rewrite r0 in rpos; rewrite /= rpos sqrt_0.
    by rewrite /Xinv zeroT.
  case :(boolP (r ^ k == 0))%Re => /eqP Hrk0.
    by move:(Hrk0); move:(pow_nonzero r k r0).
  rewrite /Xsqrt rpos.
  suff -> : (Xmask (Xreal 0) (Xinv (Xreal (sqrt r)) / Xreal r ^ k)%XR) = Xreal R0.
    by rewrite Xadd_0_l Xmul_comm.
have rge0: (0 <= r)%Re.
  move:rpos; rewrite /is_negative.
  case: (Rlt_bool_spec 0 r).
    move => rpos Hf; apply:Rcompare_not_Gt_inv.
    by rewrite (Rcompare_Lt _ _ rpos).
  case/Rle_lt_or_eq_dec; first by move/Rlt_bool_true ->.
  by move -> => _; apply:Rle_refl.
  case: (boolP (sqrt r == R0)).
    move/eqP /(sqrt_eq_0 _ rge0) => re0.
    by rewrite re0 in r0.
  move/eqP=> sqrtn0; rewrite [Xinv _]/= zeroF //.
  by rewrite Xpow_idem Xpow_Xreal /= !zeroF.
apply:H.
have Hsqrt':=(Xderive_pt_sqrt _ _ _ (Xderive_pt_identity x)).
have Hpow':= (Xderive_pt_Xpow k (Xderive_pt_identity x)).
have Hinv':= (Xderive_pt_inv (fun x => Xsqrt x)_ _ Hsqrt').
move: (Xderive_pt_div (fun x => Xinv (Xsqrt x)) (fun x => x ^ k)%XR _ _ _ Hinv' Hpow').
suff -> : e = ((- (Xmask (Xreal 1) x / (Xsqrt x + Xsqrt x) / Xsqr (Xsqrt x)) * x ^ k -
    Xreal (INR k) * x ^ k.-1 * Xmask (Xreal 1) x * Xinv (Xsqrt x)) /
   (x ^ k * x ^ k))%XR.
  by apply.
rewrite /e => {e} {Hsqrt'} {Hpow'} {Hinv'} {p}.
case: x => //.
move=> r.
  case: (boolP (is_negative r)); first by rewrite /=; move ->.
  move/negbTE=> rpos.
have rge0: (0 <= r)%Re.
  move:rpos; rewrite /is_negative.
  case: (Rlt_bool_spec 0 r).
    move => rpos Hf; apply:Rcompare_not_Gt_inv.
    by rewrite (Rcompare_Lt _ _ rpos).
  case/Rle_lt_or_eq_dec; first by move/Rlt_bool_true ->.
  by move -> => _; apply:Rle_refl.
case: (boolP (r == 0))%Re; move/eqP => r0.
  rewrite r0.
  have -> : (Xsqrt (Xreal 0))= Xreal 0.
    by rewrite r0 in rpos; rewrite /= rpos sqrt_0.
  by rewrite /= !zeroT ?Rplus_0_l.
case :(boolP (r ^ k == 0))%Re=> /eqP Hrk0.
    by move:(Hrk0); move:(pow_nonzero r k r0).
rewrite /Xsqrt rpos.
rewrite !Xdiv_split.
rewrite Xmul_1_l Xmul_1_r.
  case: (boolP (sqrt r == R0)).
    move/eqP /(sqrt_eq_0 _ rge0) => re0.
    by rewrite re0 in r0.
  move/eqP=> sqrtn0.
rewrite [Xinv _]/= zeroF //.
have Rm0 x1 x2 := (Rmult_integral_contrapositive_currified x1 x2).
have [H1 H2 H3 H4]:
  [/\ r ^ k * r ^ k <> 0, sqrt r * sqrt r <> 0,
   sqrt r + sqrt r <> 0 & r * r ^ k <> 0]%Re.
  split; rewrite -1?RIneq.double; apply: Rm0 => //.
apply:tech_Rplus; [exact:Rle_0_1| exact: Rlt_0_1].
rewrite !Xpow_idem !Xpow_Xreal /= !zeroF //=.
f_equal; field_simplify =>//.
case:k Hrk0 H1 H4.
  move=> * /=.
  field_simplify=> //.
  set s:= sqrt r; rewrite -(sqrt_sqrt r) /s {s} //.
  by set s:= sqrt r; field.
move => k *.
have -> : k.+1.-1 = k by [].
rewrite 3!Rmult_assoc.
have->: (sqrt r ^ 2 * r ^ k = r ^ k.+1)%Re.
  rewrite -(muln1 2%N) pow_sqr sqrt_sqrt //.
  by rewrite -(addn1 k) pow_add Rmult_comm.
have-> : (sqrt r ^ 3 = sqrt r * r)%Re.
  set s:= sqrt r; rewrite -(sqrt_sqrt r) /s {s} //.
  by field.
by field.
Qed.

End square_root.

Section sin_cos.

Lemma nth_derivable_pt_sin x :
  nth_derivable_pt sin
  (fix dersin k x := match k with 0 => sin x
     | 1 => cos x
     | S (S k') => (-1 * (dersin k' x))%Re
   end) x.
Proof.
split=>//; elim/nat_ind_gen => k IHk.
case ck : k => [|k']; first by apply derivable_pt_lim_sin.
case ck': k' =>[|k''].
  by ring_simplify; apply derivable_pt_lim_cos.
by apply derivable_pt_lim_scal; apply IHk; apply/ltP; omega.
Qed.

Fixpoint nth_Xsin (k : nat) x :=
  match k with
    | 0 => Xsin x
    | 1 => Xcos x
    | S (S k') => (Xreal (-1) * (nth_Xsin k' x))%XR
  end.

Fixpoint nth_Xcos (k: nat) x :=
  match k with
    | 0 => Xcos x
    | 1 => (- Xsin x)%XR
    | S (S k') => (Xreal (-1) * (nth_Xcos k' x))%XR
  end.

Lemma Xderive_pt_mul_const a f f' x :
  Xderive_pt f x f' ->
  Xderive_pt (fun y => a * f y)%XR x (a * f')%XR.
Proof.
case eqa: a=> [| r]; first by case: x.
case: x; case: f' =>//=.
move=> r1 r0; case eqf: (f (Xreal r0))=> [| rf] // H u v.
apply: (derivable_pt_lim_eq_locally (fun x => r * (proj_fun v f x))%Re).
  apply locally_true_imp with (P := (fun a0 : R =>
        (exists w1 : R, a = Xreal w1) /\
        (exists w2 : R, f (Xreal a0) = Xreal w2))).
    by rewrite /proj_fun => x [[w1 Hw1][w2 ->]].
  apply (derivable_imp_defined_any_2 (fun _ => a) f r0 (0) r1 r _ eqa eqf)=> v0.
    by rewrite /proj_fun eqa; apply derivable_pt_lim_const.
  by apply: H.
by apply derivable_pt_lim_scal.
Qed.

Lemma nth_Xderive_pt_sin x : nth_Xderive_pt Xsin nth_Xsin x.
Proof.
split=>// k.
elim/nat_ind_gen : k => k IHk.
case ck : k => [/=|k'].
  have H := (Xderive_pt_sin (fun x => x) (Xmask (Xreal 1) x) x).
  replace (Xcos x) with (Xmask (Xreal 1) x * Xcos x)%XR.
    by apply H; apply Xderive_pt_identity.
  by case x => // r; rewrite /Xmask /=; f_equal; ring.
case ck': k' =>[|k''].
  rewrite /nth_Xsin (_ : (Xreal (-1) * Xsin x)%XR = (Xmask (Xreal 1) x * -Xsin x)%XR).
    by apply Xderive_pt_cos; apply Xderive_pt_identity.
  by case x => // r; rewrite /Xmask /=; f_equal; ring.
by apply Xderive_pt_mul_const; apply IHk; apply/ltP; omega.
Qed.

Lemma nth_derivable_pt_cos x :
  nth_derivable_pt cos
  (fix dercos k x := match k with 0 => cos x
     | 1 => - sin x
     | S (S k') => -1 * (dercos k' x)
   end)%Re x.
Proof.
split=>//; elim/nat_ind_gen => k IHk.
case ck : k => [|k'].
  by apply derivable_pt_lim_cos.
case ck': k' =>[|k''].
  by ring_simplify; apply derivable_pt_lim_opp; apply derivable_pt_lim_sin.
by apply derivable_pt_lim_scal; apply IHk; apply/ltP; omega.
Qed.

Lemma nth_Xderive_pt_cos x : nth_Xderive_pt Xcos nth_Xcos x.
Proof.
split=>//; elim/nat_ind_gen => k IHk.
case ck : k => [/=|k'].
  have H := (Xderive_pt_cos (fun x => x) (Xmask (Xreal 1) x) x).
  replace (- Xsin x)%XR with (Xmask (Xreal 1) x * (- Xsin x))%XR.
    by apply: H; apply Xderive_pt_identity.
  by case x=>// r; rewrite /Xmask /=; f_equal; ring.
case ck': k' =>[|k''].
  rewrite /nth_Xcos.
  rewrite (_ : (Xreal (-1) * Xcos x)%XR = (-Xcos x)%XR).
    apply Xderive_pt_neg.
    have H := (Xderive_pt_sin (fun x => x) (Xmask (Xreal 1) x) x).
    replace (Xcos x)%XR with (Xmask (Xreal 1) x * (Xcos x))%XR.
      by apply Xderive_pt_sin; apply Xderive_pt_identity.
    by case x; rewrite // => r; rewrite /Xmask /=; f_equal; ring.
  by case (Xcos x) => [|cr] //=; f_equal; ring.
by apply Xderive_pt_mul_const; apply IHk; apply/ltP; omega.
Qed.

End sin_cos.

Section cst_var.

Lemma nth_Xderive_pt_cst (cst : ExtendedR) x :
  nth_Xderive_pt (Xmask cst) (fun (n : nat) (y : ExtendedR) =>
    match n with
      | 0 => Xmask cst y
      | n'.+1 => Xmask (Xmask (Xreal 0) cst) y
    end) x.
Proof.
split=>// k; xtotal =>[|v]; first by case: k X.
by case: k X=> [|k] X;apply: derivable_pt_lim_const.
Qed.

Lemma nth_Xderive_pt_var x :
  nth_Xderive_pt (fun x => x) (fun (n : nat) (y : ExtendedR) =>
    if n == O then y else
    if n == 1%N then Xmask (Xreal 1) y else
    Xmask (Xreal 0) y) x.
Proof.
split=> k; xtotal; [by case: k X|by case: k X X0=>//; case|move=> v].
case: k X X0=>[X _|]; first by case: X =><-; apply: derivable_pt_lim_id.
by case=>/= [|k ] X _; case: X =><-; apply: derivable_pt_lim_const.
Qed.

End cst_var.
