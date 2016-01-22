Require Import Reals.
Require Import List.
Require Import Coquelicot.
Require Import Interval_xreal.
Require Import Interval_float_sig.
Require Import Interval_interval.
Require Import Interval_interval_float.
Require Import Interval_interval_float_full.
Require Import ssreflect ssrfun ssrbool.
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
Module EF := ExtraFloats F.
Import EF.
(* Export EF. *)

(* Module IntervalIntegralPol (* (II : IntervalOps) *) (Pol : PolyIntOps I) (Bnd : PolyBound I Pol). *)



Module TM := TM I.

(* A fixed precision *)
Variable prec : F.precision.

Variables (f : R -> R) (* (iF : I.type -> I.type) *).

(* This is a std monadic operation. Does it exist somewhere in the libs? *)
Let g := toXreal_fun f.

(* g is a restriction of f as an extendedR function. *)
Let Hfgext := toXreal_fun_correct f.

(* Hypothesis HiFIntExt : forall xi x, contains (I.convert xi) (Xreal x) -> contains (I.convert (iF xi)) (Xreal (f x)). *)

Section DepthZeroPol.

Variable Mf : TM.TMI.rpa.
Variable X X0 : I.type.
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

Variable Iprec : I.precision.


(* Lemma integral_depth_zero_pol_correct : *)
(*   contains *)
(*     (I.convert (TM.integralEnclosure Iprec X0 Mf ia ib)) *)
(*     (Xreal (RInt f (T.toR a) (T.toR b))). *)
(* Proof. *)
(* apply: (TM.IntegralByPol Iprec _ _ _ _ _ _ _ validMf) => // . *)
(* admit. *)
(* Qed. *)

End DepthZeroPol.

Section Depth_Sk_Pol.

Variable getRpa : I.type -> TM.TMI.rpa. (* general parameter for any depth, including zero -> GO UP*)

End Depth_Sk_Pol.

End IntegralTacticTaylor.

Require Import Interval_bigint_carrier.
Require Import Interval_specific_ops.
Module SFBI2 := SpecificFloat BigIntRadix2.
Module IT := IntegralTacticTaylor SFBI2.
Require Import BigZ.

Eval vm_compute in (
  let prec := 20%bigZ in
  let a := SFBI2.fromZ 0 in
  let b := SFBI2.fromZ 1 in
  let X := IT.I.bnd a b in
  let x0 := IT.I.midpoint X in
  let X0 := IT.EF.thin x0 in
  let var := IT.TM.TMI.TM_var X0 in
  let f := IT.TM.TMI.TM_exp prec X0 X 10 in
  IT.TM.TMI.integralEnclosure prec X0 f (IT.EF.thin a) (IT.EF.thin b)).
