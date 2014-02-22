Require Import Reals.
Require Import Interval_interval.
Require Import Interval_xreal.

Module Type UnivariateApprox (I : IntervalOps).

(* Local Coercion I.convert : I.type >-> interval. *)

Parameter T : Type.

Definition U := (I.precision * nat (* for degree *) )%type.

Parameter approximates : I.type -> T -> (ExtendedR -> ExtendedR) -> Prop.

Parameter approximates_ext :
  forall f g xi t,
  (forall x, f x = g x) ->
  approximates xi t f -> approximates xi t g.

Parameter const : I.type -> T.

Parameter const_correct :
  forall (c : I.type) (r : R), contains (I.convert c) (Xreal r) ->
  forall (X : I.type),
  approximates X (const c) (Xmask (Xreal r)).

Parameter dummy : T.

Parameter dummy_correct :
  forall xi f, f Xnan = Xnan -> approximates xi dummy f.

Parameter var : T.

Parameter var_correct :
  forall (X : I.type), approximates X var (fun x => x).

Parameter eval : U -> T -> I.type -> I.type -> I.type.

Parameter eval_correct :
  forall u (Y : I.type) t f,
  approximates Y t f -> I.extension f (eval u t Y).

Parameter add : U -> I.type -> T -> T -> T.

Parameter add_correct :
  forall u (Y : I.type) tf tg f g,
  approximates Y tf f -> approximates Y tg g ->
  approximates Y (add u Y tf tg) (fun x => Xadd (f x) (g x)).

Parameter opp : U -> I.type -> T -> T.

Parameter opp_correct :
  forall u (Y : I.type) tf f,
  approximates Y tf f ->
  approximates Y (opp u Y tf) (fun x => Xneg (f x)).

Parameter sub : U -> I.type -> T -> T -> T.

Parameter sub_correct :
  forall u (Y : I.type) tf tg f g,
  approximates Y tf f -> approximates Y tg g ->
  approximates Y (sub u Y tf tg) (fun x => Xsub (f x) (g x)).

Parameter mul : U -> I.type -> T -> T -> T.

Parameter mul_correct :
  forall u (Y : I.type) tf tg f g,
  approximates Y tf f -> approximates Y tg g ->
  approximates Y (mul u Y tf tg) (fun x => Xmul (f x) (g x)).

Parameter exp : U -> I.type -> T -> T.

Parameter exp_correct :
  forall u (Y : I.type) tf f,
  approximates Y tf f ->
  approximates Y (exp u Y tf) (fun x => Xexp (f x)).

End UnivariateApprox.
