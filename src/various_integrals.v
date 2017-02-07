Require Import Reals Coquelicot.Coquelicot.
Require Import mathcomp.ssreflect.ssreflect mathcomp.ssreflect.ssrfun mathcomp.ssreflect.ssrbool mathcomp.ssreflect.ssrnat.
Require Import coquelicot_compl Interval_missing.
Require Import mathcomp.ssreflect.bigop.
Require Import ZArith Psatz.
Require Import Fourier_util.
Require Import interval_compl.

(* ultimately, any common results should be put in a different file *)
Require Import bertrand.

(* This file aims to prove results about various integrals, mainly to be    *)
(* used to integrate bounded functions against them at poles or at infinity *)


(* ************************ *)
(* ************************ *)
(* ************************ *)
(* ************************ *)
(* ************************ *)
(* ************************ *)
(* the exponential function *)
(* ************************ *)
(* ************************ *)
(* ************************ *)
(* ************************ *)
(* ************************ *)
(* ************************ *)

Definition expn x := exp (-x).

Lemma continuous_expn x : continuous expn x.
Proof.
apply: continuous_comp.
  exact: continuous_opp.
exact: continuous_exp.
Qed.

Lemma is_RInt_gen_exp_infty a : is_RInt_gen (fun x => exp (-x)) (at_point a) (Rbar_locally p_infty) (exp (-a)).
rewrite /is_RInt_gen.
rewrite prodi_to_single_l.
apply: (filterlimi_lim_ext_loc (fun x => - (exp(- x) - exp(-a)))).
  exists a.
  move => x Hx.
  have H : forall x,  -1 * x + 0 = - x by move => x1; ring.
  apply: (is_RInt_ext (fun x => - scal (-1) (exp (-1 * x + 0)))).
  move => x0 Hx0; rewrite /scal /= /mult /= .
  rewrite H; ring.
  apply: is_RInt_opp.
  apply: is_RInt_comp_lin.
  by rewrite !H; apply: is_RInt_exp.
  apply: (filterlim_ext (fun x => exp (-a) - exp (-x))).
    move => x; ring.
  apply: filterlim_comp.
  apply: filterlim_comp.
  apply: filterlim_Rbar_opp => /= .
  by rewrite /Rbar_opp; exact: is_lim_exp_m.
  suff {2}-> : exp (-a) = exp (-a) - 0.
  suff H : continuous (fun x => Rminus (exp (-a)) x) 0.
    by apply: H.
  apply: continuous_minus.
    exact: continuous_const.
    exact: continuous_id.
  by rewrite Rminus_0_r.
Qed.

Require Import Interval_xreal.
Require Import Interval_float_sig.
Require Import Interval_interval.

Module ExpNInterval (F : FloatOps with Definition even_radix := true) (I : IntervalOps with Definition bound_type := F.type with Definition precision := F.precision with Definition convert_bound := F.toX).

Module J := IntervalExt I.

Section EffectiveExpN.

Variable prec : F.precision.

(* This is overly verbose for the exponential, but the aim is to
provide guidance for the structure of possibly more complicated
functions *)

Section Infinity.

Variable a : R.
Variable A : I.type.
Let iA := I.convert A.

Hypothesis Hcontainsa : contains iA (Xreal a).

Definition ExpN := I.exp prec (I.neg (A)).

Lemma ExpN_correct : contains (I.convert ExpN) (Xreal (expn a)).
Proof.
apply: J.exp_correct.
exact: J.neg_correct.
Qed.

End Infinity.
End EffectiveExpN.

End ExpNInterval.