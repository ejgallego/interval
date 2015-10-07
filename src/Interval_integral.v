Require Import Reals.
Require Import List.
Require Import Coquelicot.
Require Import Interval_xreal.
Require Import Interval_float_sig.
Require Import Interval_interval.
Require Import Interval_interval_float.

Require Import ssreflect ssrfun ssrbool.

Module IntegralTactic (F : FloatOps with Definition even_radix := true).

Module I := FloatInterval F.

Section IntervalIntegral.

(* A fixed precision *)
Variable prec : F.precision.

Variables (f : R -> R) (iF : I.type -> I.type).

Hypothesis HiFIntExt : forall xi x, contains (I.convert xi) (Xreal x) -> contains (I.convert (iF xi)) (Xreal (f x)).

Definition thin (f : F.type) : I.type :=
  if F.real f then I.bnd f f else I.nai.

Fixpoint integral (depth : nat) (a b : F.type) :=
  let int := I.bnd a b in
  match depth with
    | O => I.mul prec (iF int) (I.sub prec (thin b) (thin a))
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
      let sab := I.mul prec (thin (diam a)) (I.join (thin F.zero) (iF a)) in
      let scd := I.mul prec (thin (diam b)) (I.join (thin F.zero) (iF b)) in
      I.add prec (I.add prec sab scd) (integral depth b1 a2)
    else
      Inan
  else
    Inan.

Lemma integral_correct :
  forall (depth : nat) (a b : R) (ia ib : I.type),
  contains (I.convert ia) (Xreal a) ->
  contains (I.convert ib) (Xreal b) ->
  ex_RInt f a b ->
  contains
    (I.convert (integral_intBounds depth ia ib))
    (Xreal (RInt f a b)).
Proof.
generalize HiFIntExt.
admit.
Qed.

End IntervalIntegral.

End IntegralTactic.
