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

Module I := FloatInterval F.
Module T := TranscendentalFloatFast F.
Module Int := Integrability F.
Module IntTac := IntegralTactic F.
Module EF := ExtraFloats F.
Import EF.
(* Export EF. *)

(* Module IntervalIntegralPol (* (II : IntervalOps) *) (Pol : PolyIntOps I) (Bnd : PolyBound I Pol). *)



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
Definition X0 := thin (I.midpoint X).
Variable dom : R -> bool.
Definition iX := I.convert X.
Definition iX0 := I.convert X0.

Hypothesis Hsubset : subset (I.convert X0) (I.convert X).
Hypothesis Hdomx: forall x, contains iX (Xreal x) -> dom x.
Hypothesis validMf : TM.TMI.i_validTM iX0 iX Mf g dom.

Variables (a b : F.type).

(* f is integrable on [a, b]*)
Hypothesis Hintegrable : ex_RInt f (T.toR a) (T.toR b).

(* a <= b *)
Hypothesis  Hleab : T.toR a <= T.toR b.

(* a and b are no Nan. This cannot be deduced from Hleab *)
Hypothesis ha : F.real a.
Hypothesis hb : F.real b.

Variables ia ib : I.type.

Variable x0 : R.
Hypothesis Hcontx0 : contains iX0 (Xreal x0).
Hypothesis Hconta : contains iX (Xreal (T.toR a)).
Hypothesis Hcontb : contains iX (Xreal (T.toR b)).

Section Functions.

Definition taylor_integral :=
  TM.TMI.integralEnclosure prec X0 Mf ia ib.

Definition deg := 10%nat. (* magic value, shouldn't be needed but for some reason it appears in the arguments of TaylorEvaluator in integrability *)

(* Let iF1 := TM.TMI.ComputeBound prec Mf X0. *)

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

(* Print TM.TMI.polIntegral. *)

(* SearchAbout TM.TMI.rpa. *)
(* Search _ TM.TMI.ComputeBound. *)
(* Print IntTac.naive_integral. *)
(* Print Int.TaylorEvaluator. *)

End Functions.

Section CorrectionLemmas.

End CorrectionLemmas.

Lemma taylor_integral_correct :
  contains
    (I.convert taylor_integral)
    (Xreal (RInt f (T.toR a) (T.toR b))).
Proof.
rewrite /taylor_integral.
(* move: (@TM.TMI.integralEnclosure_correct prec ia ib (toXreal_fun f) Mf). *)
(*apply: (TM.TMI.IntegralByPol Iprec _ _ _ _ _ _ _ validMf) => // .*)
admit.
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

Section Depth_Sk_Pol.

(* Variable getRpa : I.type -> TM.TMI.rpa. (* general parameter for any depth, including zero -> GO UP*) *)

End Depth_Sk_Pol.

End IntegralTacticTaylor.


(* Require Import Interval_bigint_carrier. *)
(* Require Import Interval_specific_ops. *)
(* Module SFBI2 := SpecificFloat BigIntRadix2. *)
(* Module IT := IntegralTacticTaylor SFBI2. *)
(* Require Import BigZ. *)

(* Eval vm_compute in ( *)
(*   let prec := 20%bigZ in *)
(*   let a := SFBI2.fromZ 0 in *)
(*   let b := SFBI2.fromZ 10 in *)
(*   let X := IT.I.bnd a b in *)
(*   let x0 := IT.I.midpoint X in *)
(*   let X0 := IT.EF.thin x0 in *)
(*   let var := IT.TM.TMI.TM_var X0 in *)
(*   let f := IT.TM.TMI.TM_sin prec X0 X 10 in *)
(*   f). *)
  (* IT.TM.TMI.integralEnclosure prec X0 f (IT.EF.thin a) (IT.EF.thin b) *)
