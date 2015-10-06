Require Import Reals.
Require Import List.
Require Import Coquelicot.
Require Import Interval_xreal.
Require Import Interval_float_sig.
Require Import Interval_interval.
Require Import Interval_interval_float.
Require Import Interval_interval_float_full.
Require Import Interval_bisect.

Require Import ssreflect ssrfun ssrbool.

Module IntegralTactic (F : FloatOps with Definition even_radix := true).

Module FInt := FloatIntervalFull F.
Module IntA := IntervalAlgos FInt.

Import FInt.

Section IntervalIntegral.

(* A fixed precision *)
Variable prec : F.precision.

Variables (f : R -> R) (iF : I.type -> I.type).

(* Hypothesis HiFIntExt : I.extension g iF. *)
Hypothesis HiFIntExt : forall xi x, contains (I.convert xi) (Xreal x) -> contains (I.convert (iF xi)) (Xreal (f x)).

Section OrderOne.

Variables (a b : F.type).

(* f is integrable on [a, b]*)
Hypothesis Hintegrable : ex_RInt f (T.toR a) (T.toR b).

(* a <= b *)
Hypothesis  Hleab : T.toR a <= T.toR b.

(* a and b are no Nan. This cannot be deduced from Hleab *)
Hypothesis ha : F.real a = true.
Hypothesis hb : F.real b = true.

End OrderOne.

Definition thin (f : F.type) : FInt.type :=
  if F.real f then I.bnd f f else I.nai.

Fixpoint integral (depth : nat) (a b : F.type) :=
  let int := I.bnd a b in
  match depth with
    | O => I.mul prec (iF (int)) (I.sub prec (thin b) (thin a))
    | S n => let m := I.midpoint int in
             let i1 := integral n a m in
             let i2 := integral n m b in
             I.add prec i1 i2
  end.

(* using F.sub instead? *)
Definition diam x :=
  match x with
    | Inan => F.nan
    | Ibnd a b => F.sub_exact b a
  end.

Definition integral_intBounds depth (a b : I.type) :=
  if a is Ibnd _ b1 then
    if b is Ibnd a2 _ then
      let sab := I.mul prec (thin (diam a)) (FInt.join (thin F.zero) (iF a)) in
      let scd := I.mul prec (thin (diam b)) (FInt.join (thin F.zero) (iF b)) in
      I.add prec (I.add prec sab scd) (integral depth b1 a2)
    else
      Inan
  else
    Inan.

End IntervalIntegral.

Axiom integral_correct :
  forall prec (depth : nat) (a b : R) (ia ib : I.type) prog bounds,
  let f := fun x => nth 0 (eval_real prog (x::map IntA.real_from_bp bounds)) R0 in
  contains (I.convert ia) (Xreal a) ->
  contains (I.convert ib) (Xreal b) ->
  ex_RInt f a b /\
  contains
    (I.convert (integral_intBounds prec
       (fun xi => nth 0 (IntA.BndValuator.eval prec prog (xi::map IntA.interval_from_bp bounds)) I.nai)
        depth ia ib))
    (Xreal (RInt f a b)).

End IntegralTactic.
