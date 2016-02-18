Require Import Reals.
Require Import List.
Require Import Coquelicot.
Require Import Interval_xreal.
Require Import Interval_float_sig.
Require Import Interval_interval.
Require Import Interval_interval_float.
Require Import Interval_interval_float_full.
Require Import Ssreflect.ssreflect Ssreflect.ssrfun Ssreflect.ssrbool.
Require Import xreal_ssr_compat.
Require Import Interval_transcend.
Require Import Interval_missing.
Require Import integrability.
Require Import Coquelicot coquelicot_compl.

Require Import interval_compl.
Require Import poly_datatypes.
Require Import taylor_poly.
Require Import poly_bound.
Require Import Interval_taylor_model.
Require Import taylor_model_int_sharp.
Require Import Interval_integral.

Variables (f : R -> R) (ra rb : R).

Hypothesis ltab : ra < rb.
Hypothesis fint : ex_RInt f ra rb.

Module IntegralTacticTaylor (F : FloatOps with Definition even_radix := true).

Module EF := ExtraFloats F.
Import EF.
Module I := FloatIntervalFull F.
Module Int := Integrability F.
Module IntTac := IntegralTactic F.

Module TM := TM I.

Section DepthZeroPol.

(* A fixed precision *)
Variable prec : F.precision.

Variables (f : R -> R) (iF : I.type -> I.type).

Let g := toXreal_fun f.

Let Hfgext := toXreal_fun_correct f.

Hypothesis HiFIntExt : forall xi x, contains (I.convert xi) (Xreal x) -> contains (I.convert (iF xi)) (Xreal (f x)).

Variable Mf : TM.TMI.rpa.
Variables X : I.type.
Definition X0 := I.bnd (I.midpoint X) (I.midpoint X).
Variable dom : R -> bool.
Definition iX := I.convert X.
Definition iX0 := I.convert X0.

Hypothesis validMf : TM.TMI.i_validTM iX0 iX Mf g.

Variables (a b : F.type).

(* f is integrable on [a, b]*)
Hypothesis Hintegrable : ex_RInt f (T.toR a) (T.toR b).

(* a <= b *)
Hypothesis  Hleab : T.toR a <= T.toR b.

(* a and b are no Nan. This cannot be deduced from Hleab *)
Hypothesis ha : F.real a.
Hypothesis hb : F.real b.

Variables ia ib : I.type.

Definition x0 := T.toR (I.midpoint X).
Hypothesis Hconta : contains (I.convert ia) (Xreal (T.toR a)).
Hypothesis Hcontb : contains (I.convert ib) (Xreal (T.toR b)).
Hypothesis Hcontxa : contains iX (Xreal (T.toR a)).
Hypothesis Hcontxb : contains iX (Xreal (T.toR b)).

Definition taylor_integral :=
  TM.TMI.integralEnclosure prec X0 Mf ia ib.

Definition taylor_integral_subtle :=
  match taylor_integral with
    | Inan => IntTac.naive_integral prec iF a b
    | x => x
  end.

(* now we take the intersection of a naive and intelligent way of computing the integral *)
Definition taylor_integral_naive_intersection :=
  let temp := IntTac.naive_integral prec iF a b in
  match temp with
    | Inan => Inan
    | temp => match taylor_integral with
                | Inan => temp
                | x => I.meet x temp
              end
  end.

Lemma taylor_integral_correct :
  contains
    (I.convert taylor_integral)
    (Xreal (RInt f (T.toR a) (T.toR b))).
Proof.
rewrite /taylor_integral.
apply: (@TM.TMI.integralEnclosure_correct prec X0 X (toXreal_fun f) Mf x0) => //.
rewrite /X0 I.bnd_correct (proj1 (I.midpoint_correct X _)).
split ; apply Rle_refl.
eexists.
exact: Hcontxa.
Qed.

Lemma taylor_integral_subtle_correct :
  contains
    (I.convert taylor_integral_subtle)
    (Xreal (RInt f (T.toR a) (T.toR b))).
Proof.
rewrite /taylor_integral_subtle.
case Htaylor_int : taylor_integral => [|l u].
apply: IntTac.naive_integral_correct => // .
rewrite -Htaylor_int.
apply: taylor_integral_correct.
Qed.

Lemma taylor_integral_naive_intersection_correct :
  contains
    (I.convert taylor_integral_naive_intersection)
    (Xreal (RInt f (T.toR a) (T.toR b))).
Proof.
rewrite /taylor_integral_naive_intersection.
set tmp := (IntTac.naive_integral _ _ _ _).
case Ht : tmp => [| l u] => // .
set int := Xreal _.
case Hti : (taylor_integral) => [| l1 u1]; rewrite -Ht.
- by apply: IntTac.naive_integral_correct.
- rewrite -Hti; apply: (I.meet_correct taylor_integral tmp).
  apply: taylor_integral_correct.
  by apply: IntTac.naive_integral_correct.
Qed.

End DepthZeroPol.

End IntegralTacticTaylor.
