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
  forall (X : I.type), not_empty (I.convert X) ->
  approximates X (Xmask (Xreal r)) (const c).

Parameter var_correct :
  forall (X : I.type), not_empty (I.convert X) ->
  approximates X (fun x => x) var.

Parameter add_correct :
  forall u (Y : I.type) f tf g tg,
  approximates Y f tf -> approximates Y g tg ->
  approximates Y (fun x => Xadd (f x) (g x)) (add u Y tf tg).

Parameter exp_correct :
  forall u (Y : I.type) f tf, approximates Y f tf ->
  approximates Y (fun x => Xexp (f x)) (exp u Y tf).

End UnivariateApprox.
