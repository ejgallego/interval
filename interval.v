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

Lemma contains_connected :
  forall xi, connected (fun x => contains xi (Xreal x)).
intros [|l u] a b Ha Hb x Hx.
exact I.
split.
destruct l as [|l].
exact I.
exact (Rle_trans _ _ _ (proj1 Ha) (proj1 Hx)).
destruct u as [|u].
exact I.
exact (Rle_trans _ _ _ (proj2 Hx) (proj2 Hb)).
Qed.

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

Definition le_mixed x y :=
  match y with
  | Xnan => True
  | Xreal yr =>
    match x with
    | Xnan => True
    | Xreal xr => Rle xr yr
    end
  end.

Lemma le_mixed_lower :
  forall xl yr,
  le_mixed xl (Xreal yr) -> le_lower xl (Xreal yr).
intros [|xr] yr H.
exact H.
exact (Ropp_le_contravar _ _ H).
Qed.

Lemma le_mixed_upper :
  forall xr yu,
  le_mixed (Xreal xr) yu -> le_upper (Xreal xr) yu.
intros xr [|yr] H ; exact H.
Qed.

Definition not_empty xi :=
  exists v, contains xi (Xreal v).

Lemma le_mixed_not_empty :
  forall x y, le_mixed x y ->
  not_empty (Ibnd x y).
intros [|xr] [|yr] Hl.
exists R0. now split.
exists yr. repeat split.
apply Rle_refl.
exists xr. repeat split.
apply Rle_refl.
exists xr. split.
apply Rle_refl.
exact Hl.
Qed.

Lemma contains_minf_not_empty :
  forall xu, not_empty (Ibnd Xnan xu).
intros [|xr].
exists R0. now split.
exists xr. repeat split.
apply Rle_refl.
Qed.

Lemma contains_pinf_not_empty :
  forall xl, not_empty (Ibnd xl Xnan).
intros [|xr].
exists R0. now split.
exists xr. repeat split.
apply Rle_refl.
Qed.

Lemma contains_not_empty :
  forall x xi, contains xi x -> not_empty xi.
intros x [|[u _|l [_|u]]].
intros _.
exists R0.
exact I.
apply contains_minf_not_empty.
apply contains_pinf_not_empty.
case x.
intro H.
elim H.
intros xr H.
exists xr.
exact H.
Qed.

(*
Lemma contains_not_empty_2 :
  forall xi x, contains xi x ->
 (exists v, forall y, contains xi y -> y = Xreal v) \/
 (exists u, exists v, (u < v)%R /\ subset (Ibnd (Xreal u) (Xreal v)) xi).
intros [|[u|l [|u]]] x H.
(* NaI *)
right.
exists R0.
exists R1.
exact (conj Rlt_0_1 I).
(* (-inf,?] *)
right.
destruct (contains_minf_not_empty u) as (v, Hv).
exists (v + -1)%R.
exists v.
split.
pattern v at 2 ; replace v with (v + -1 + 1)%R by ring.
apply Rlt_plus_1.
exact Hv.
(* [l,+inf) *)
right.
destruct (contains_pinf_not_empty (Xreal l)) as (v, Hv).
exists v.
exists (v + 1)%R.
split.
apply Rlt_plus_1.
split.
exact (Ropp_le_contravar _ _ (proj1 Hv)).
exact I.
(* [l,u] *)
destruct (contains_not_empty _ _ H) as (w, Hw).
destruct (Rle_lt_or_eq_dec _ _ (Rle_trans _ _ _ (proj1 Hw) (proj2 Hw))) as [Hr|Hr].
clear -Hr.
right.
exists l.
exists u.
split.
exact Hr.
split ; exact (Rle_refl _).
left.
exists l.
intros [|y] Hy.
elim Hy.
apply f_equal.
apply Rle_antisym.
rewrite <- Hr in Hy.
exact (proj2 Hy).
exact (proj1 Hy).
Qed.
*)

Definition overlap xi yi :=
  match xi, yi with
  | Ibnd xl xu, Ibnd yl yu =>
    (le_lower xl yl /\ le_mixed yl xu /\ le_mixed yl yu) \/
    (le_lower yl xl /\ le_mixed xl yu /\ le_mixed xl xu)
  | Ibnd xl xu, Inan => le_mixed xl xu
  | Inan, Ibnd yl yu => le_mixed yl yu
  | Inan, Inan => True
  end.

Lemma overlap_contains_aux :
  forall xl xu yl yu,
  le_lower xl yl -> le_mixed yl xu -> le_mixed yl yu ->
  exists v, contains (Ibnd xl xu) (Xreal v) /\ contains (Ibnd yl yu) (Xreal v).
intros xl xu yl yu Ho1 Ho2 Ho3.
destruct yl as [|yr].
destruct xl. 2: elim Ho1.
destruct xu as [|xr].
destruct (contains_minf_not_empty yu) as (yr, Hy).
exists yr.
split ; [ now split | exact Hy ].
destruct yu as [|yr].
exists xr. repeat split.
apply Rle_refl.
exists (Rmin xr yr).
repeat split.
apply Rmin_l.
apply Rmin_r.
exists yr.
split.
apply le_contains.
exact Ho1.
exact Ho2.
split.
apply Rle_refl.
exact Ho3.
Qed.

Theorem overlap_contains :
  forall xi yi,
  overlap xi yi ->
  exists v,
  contains xi (Xreal v) /\ contains yi (Xreal v).
intros [|xl xu] [|yl yu] Ho.
exists R0. now split.
destruct (le_mixed_not_empty _ _ Ho) as (v, Hv).
exists v. now split.
destruct (le_mixed_not_empty _ _ Ho) as (v, Hv).
exists v. now split.
destruct Ho as [(Ho1,(Ho2,Ho3))|(Ho1,(Ho2,Ho3))].
exact (overlap_contains_aux _ _ _ _ Ho1 Ho2 Ho3).
destruct (overlap_contains_aux _ _ _ _ Ho1 Ho2 Ho3) as (v, (H1, H2)).
exists v. split ; assumption.
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
Parameter overlap : type -> type -> bool.

Parameter subset_correct :
  forall xi yi : type,
  subset xi yi = true -> subset_ (convert xi) (convert yi).

Parameter join : type -> type -> type.
Parameter meet : type -> type -> type.
Parameter sign_large : type -> Xcomparison.

Parameter sign_large_correct :
  forall xi,
  match sign_large xi with
  | Xeq => forall x, contains (convert xi) x -> x = Xreal 0
  | Xlt => forall x, contains (convert xi) x -> exists v, x = Xreal v /\ Rle v 0
  | Xgt => forall x, contains (convert xi) x -> exists v, x = Xreal v /\ Rle 0 v
  | Xund => True
  end.

(*
Parameter join_correct :
  forall xi yi v,
  contains xi v \/ contains yi v -> contains (join xi yi) v.
*)

Parameter meet_correct :
  forall xi yi v,
  contains (convert xi) v -> contains (convert yi) v ->
  contains (convert (meet xi yi)) v.

Parameter midpoint : type -> bound_type.

Parameter midpoint_correct :
  forall xi,
  (exists x, contains (convert xi) x) ->
  contains (convert xi) (convert_bound (midpoint xi)).

Definition extension f fi := forall b x,
  contains (convert b) x -> contains (convert (fi b)) (f x).

Definition extension_2 f fi := forall bx by x y,
  contains (convert bx) x ->
  contains (convert by) y ->
  contains (convert (fi bx by)) (f x y).

Parameter mask : type -> type -> type.

Parameter mask_correct : extension_2 Xmask mask.

Parameter precision : Set.

Parameter neg : type -> type.
Parameter abs : type -> type.
Parameter inv : precision -> type -> type.
Parameter sqr : precision -> type -> type.
Parameter sqrt : precision -> type -> type.
Parameter cos : precision -> type -> type.
Parameter sin : precision -> type -> type.
Parameter tan : precision -> type -> type.
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
Parameter cos_correct : forall prec, extension Xcos (cos prec).
Parameter sin_correct : forall prec, extension Xsin (sin prec).
Parameter tan_correct : forall prec, extension Xtan (tan prec).
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

(*
Parameter lower_extent_correct :
  forall xi x,
 (exists y, (x <= y)%R /\ contains (convert xi) (Xreal y)) ->
  contains (convert (lower_extent xi)) (Xreal x).
*)

Parameter lower : type -> bound_type.
Parameter upper : type -> bound_type.

Parameter lower_bounded_correct :
  forall xi,
  lower_bounded xi = true ->
  exists l, convert xi = Ibnd (Xreal l) (convert_bound (upper xi)).

Parameter upper_bounded_correct :
  forall xi,
  upper_bounded xi = true ->
  exists u, convert xi = Ibnd (convert_bound (lower xi)) (Xreal u).

Parameter bounded_correct :
  forall xi,
  bounded xi = true ->
  exists l, exists u, convert xi = Ibnd (Xreal l) (Xreal u).

Parameter fromZ : Z -> type.

End IntervalOps.
