Require Import Reals.
Require Import Interval_interval.
Require Import Interval_xreal.

Module Type UnivariateApprox (I : IntervalOps).

Parameter T : Type.

Definition U := (I.precision * nat (* for degree *) )%type.

Parameter approximates : I.type -> (ExtendedR -> ExtendedR) -> T -> Prop.

Parameter eval : U -> I.type -> I.type -> T -> I.type.

Parameter const : I.type -> T.

Parameter var : T.

Parameter add : U -> I.type -> T -> T -> T.

Parameter exp : U -> I.type -> T -> T.

(* Local Coercion I.convert : I.type >-> interval. *)

Parameter eval_correct :
  forall u (Y : I.type) f tf, approximates Y f tf ->
  forall (X : I.type),
  forall x, contains (I.convert X) x ->
  contains (I.convert (eval u Y X tf)) (f x).

Parameter const_correct :
  forall (c : I.type) (r : R), contains (I.convert c) (Xreal r) ->
  forall (X : I.type),
  approximates X (Xmask (Xreal r)) (const c).

Parameter var_correct :
  forall (X : I.type),
  approximates X (fun x => x) var.

Parameter add_correct :
  forall u (Y : I.type) tf tg f g,
  approximates Y f tf -> approximates Y g tg ->
  approximates Y (fun x => Xadd (f x) (g x)) (add u Y tf tg).

Parameter exp_correct :
  forall u (Y : I.type) f tf,
  approximates Y f tf ->
  approximates Y (fun x => Xexp (f x)) (exp u Y tf).

Parameter dummy : T.

Parameter approximates_dummy :
  forall xi f, f Xnan = Xnan -> approximates xi f dummy.

Parameter approximates_ext :
  forall f g h xi,
  (forall x, f x = g x) ->
  approximates xi f h -> approximates xi g h.

End UnivariateApprox.
