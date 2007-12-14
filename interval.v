Require Import Bool.
Require Import Reals.
Require Import missing.
Require Import xreal.
Require Import definitions.
Require Import float_sig.
Require Import generic.
Require Import generic_proof.

Inductive interval : Set :=
  | Inan : interval
  | Ibnd (l u : ExtendedR) : interval.

Definition contains i v :=
  match i, v with
  | Ibnd l u, Xreal x =>
    match l with
    | Xreal r => Rle r x
    | Xnan => True
    end /\
    match u with
    | Xreal r => Rle x r
    | Xnan => True
    end
  | Inan, _ => True
  | _, Xnan => False
  end.

Definition le_upper x y :=
  match y with
  | Xnan => True
  | Xreal yr =>
    match x with
    | Xnan => False
    | Xreal xr => Rle xr yr
    end
  end.

Definition le_lower x y :=
  le_upper (Xneg y) (Xneg x).

Lemma le_upper_trans :
  forall x y z,
  le_upper x y -> le_upper y z -> le_upper x z.
intros x y z.
case z.
split.
intro zr.
case y.
intros _ H.
elim H.
intros yr.
case x.
intros H _.
elim H.
intros xr.
simpl.
apply Rle_trans.
Qed.

Lemma le_lower_trans :
  forall x y z,
  le_lower x y -> le_lower y z -> le_lower x z.
unfold le_lower.
intros.
eapply le_upper_trans ; eassumption.
Qed.

Lemma contains_le :
  forall xl xu v,
  contains (Ibnd xl xu) v ->
  le_lower xl v /\ le_upper v xu.
intros xl xu v.
case v.
intro.
elim H.
intros r.
case xl.
intro.
exact H.
intros l (Hl, Hu).
split.
exact (Ropp_le_contravar _ _ Hl).
exact Hu.
Qed.

Lemma le_contains :
  forall xl xu v,
  le_lower xl (Xreal v) -> le_upper (Xreal v) xu ->
  contains (Ibnd xl xu) (Xreal v).
intros xl xu v.
case xl.
intros _ Hu.
exact (conj I Hu).
intros l Hl Hu.
split.
exact (Ropp_le_cancel _ _ Hl).
exact Hu.
Qed.

Definition subset xi yi :=
  match xi, yi with
  | Ibnd xl xu, Ibnd yl yu =>
    le_lower yl xl /\ le_upper xu yu
  | _, Inan => True
  | _, _ => False
  end.

Theorem subset_contains :
  forall xi yi,
  subset xi yi ->
  forall v,
  contains xi v ->
  contains yi v.
intros xi yi.
case yi.
intros _ v _.
exact I.
intros yl yu.
case xi.
intros H v _.
elim H.
intros xl xu Hx v.
case v.
intro H.
elim H.
intros r H.
apply le_contains.
apply le_lower_trans with xl.
exact (proj1 Hx).
exact (proj1 (contains_le _ _ _ H)).
apply le_upper_trans with xu.
exact (proj2 (contains_le _ _ _ H)).
exact (proj2 Hx).
Qed.

Definition domain P b :=
  forall x, contains b x -> P x.

Theorem subset_domain :
  forall P yi,
  domain P yi ->
  forall xi,
  subset xi yi ->
  domain P xi.
intros P yi Hp xi Hx x H.
apply Hp.
apply subset_contains with (1 := Hx).
exact H.
Qed.

Theorem subset_subset :
  forall xi yi zi,
  subset xi yi ->
  subset yi zi ->
  subset xi zi.
intros xi yi zi.
case zi.
case xi ; intros ; exact I.
intros zl zu.
case xi.
case yi ; simpl ; trivial.
intros xl xu.
case yi.
intros _ H.
elim H.
intros yl yu Hx Hy.
split.
apply le_lower_trans with yl.
exact (proj1 Hy).
exact (proj1 Hx).
apply le_upper_trans with yu.
exact (proj2 Hx).
exact (proj2 Hy).
Qed.

Theorem bisect :
  forall P xl xm xu,
  domain P (Ibnd xl xm) ->
  domain P (Ibnd xm xu) ->
  domain P (Ibnd xl xu).
intros P xl xm xu Hl Hu [|x] H.
elim H.
case_eq xm ; intros.
apply Hu.
rewrite H0.
exact (conj I (proj2 H)).
case (Rle_dec x r) ; intros Hr.
apply Hl.
apply le_contains.
exact (proj1 (contains_le _ _ _ H)).
rewrite H0.
exact Hr.
apply Hu.
apply le_contains.
rewrite H0.
unfold le_lower.
simpl.
apply Ropp_le_contravar.
auto with real.
exact (proj2 (contains_le _ _ _ H)).
Qed.

Definition interval_extension
  (f : ExtendedR -> ExtendedR)
  (fi : interval -> interval) :=
  forall b : interval, forall x : ExtendedR,
  contains b x -> contains (fi b) (f x).

Definition interval_extension_2
  (f : ExtendedR -> ExtendedR -> ExtendedR)
  (fi : interval -> interval -> interval) :=
  forall bx by : interval, forall x y : ExtendedR,
  contains bx x -> contains by y ->
  contains (fi bx by) (f x y).


(*
Theorem compose_1_1_1 :
  forall f g fi gi,
  interval_extension_1_1 f fi ->
  interval_extension_1_1 g gi ->
  interval_extension_1_1 (fun x => g (f x)) (fun b => gi (fi b)).
intros f g fi gi Hf Hg b x H.
apply Hg.
apply Hf.
apply H.
Qed.
*)

Module Type IntervalOps.

Parameter bound_type : Set.
Parameter convert_bound : bound_type -> ExtendedR.
Parameter type : Set.
Parameter convert : type -> interval.
Parameter nai : type.
Parameter bnd : bound_type -> bound_type -> type.

Parameter bnd_correct :
  forall l u,
  convert (bnd l u) = Ibnd (convert_bound l) (convert_bound u).

Parameter nai_correct :
  convert nai = Inan.

Notation subset_ := subset.

Parameter subset : type -> type -> bool.

Parameter subset_correct :
  forall xi yi : type,
  subset xi yi = true -> subset_ (convert xi) (convert yi).

Parameter join : type -> type -> type.

Parameter meet : type -> type -> type.

Parameter sign_large : type -> Xcomparison.

Parameter midpoint : type -> bound_type.

Parameter midpoint_correct :
  forall xi,
  (exists x, contains (convert xi) (Xreal x)) ->
  contains (convert xi) (convert_bound (midpoint xi)).

Definition extension f fi := forall b x,
  contains (convert b) x -> contains (convert (fi b)) (f x).

Definition extension_2 f fi := forall bx by x y,
  contains (convert bx) x ->
  contains (convert by) y ->
  contains (convert (fi bx by)) (f x y).

Parameter precision : Set.

Parameter neg : type -> type.
Parameter abs : type -> type.
Parameter inv : precision -> type -> type.
Parameter sqr : precision -> type -> type.
Parameter sqrt : precision -> type -> type.
Parameter atan : precision -> type -> type.
Parameter add : precision -> type -> type -> type.
Parameter sub : precision -> type -> type -> type.
Parameter mul : precision -> type -> type -> type.
Parameter div : precision -> type -> type -> type.

Parameter neg_correct : extension Xneg neg.
Parameter inv_correct : forall prec, extension Xinv (inv prec).
Parameter sqr_correct : forall prec, extension Xsqr (sqr prec).
Parameter abs_correct : extension Xabs abs.
Parameter sqrt_correct : forall prec, extension Xsqrt (sqrt prec).
Parameter atan_correct : forall prec, extension Xatan (atan prec).
Parameter add_correct : forall prec, extension_2 Xadd (add prec).
Parameter sub_correct : forall prec, extension_2 Xsub (sub prec).
Parameter mul_correct : forall prec, extension_2 Xmul (mul prec).
Parameter div_correct : forall prec, extension_2 Xdiv (div prec).

Parameter bounded : type -> bool.
Parameter lower_bounded : type -> bool.
Parameter upper_bounded : type -> bool.

Parameter lower_extent : type -> type.
Parameter upper_extent : type -> type.
Parameter whole : type.

Parameter lower : type -> bound_type.
Parameter upper : type -> bound_type.

Parameter fromZ : Z -> type.

End IntervalOps.
