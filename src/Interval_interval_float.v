Require Import Bool.
Require Import Reals.
Require Import Interval_missing.
Require Import Interval_xreal.
Require Import Interval_definitions.
Require Import Interval_generic.
Require Import Interval_generic_proof.
Require Import Interval_float_sig.
Require Import Interval_interval.

Inductive f_interval (A : Type) : Type :=
  | Inan : f_interval A
  | Ibnd (l u : A) : f_interval A.

Implicit Arguments Inan [A].
Implicit Arguments Ibnd [A].

Definition le_lower' x y :=
  match x with
  | Xnan => True
  | Xreal xr =>
    match y with
    | Xnan => False
    | Xreal yr => Rle xr yr
    end
  end.

Module FloatInterval (F : FloatOps with Definition even_radix := true).

Definition type := f_interval F.type.
Definition bound_type := F.type.
Definition precision := F.precision.

Definition convert_bound x := FtoX (F.toF x).
Definition convert xi :=
  match xi with
  | Inan => Interval_interval.Inan
  | Ibnd l u => Interval_interval.Ibnd (convert_bound l) (convert_bound u)
  end.

Definition nai := @Inan F.type.
Definition bnd := @Ibnd F.type.
Definition zero := Ibnd F.zero F.zero.

Lemma bnd_correct :
  forall l u,
  convert (bnd l u) = Interval_interval.Ibnd (convert_bound l) (convert_bound u).
split.
Qed.

Lemma nai_correct :
  convert nai = Interval_interval.Inan.
split.
Qed.

Lemma zero_correct :
  convert zero = Interval_interval.Ibnd (Xreal 0) (Xreal 0).
Proof. now simpl; unfold convert_bound; rewrite F.zero_correct. Qed.

Definition bounded xi :=
  match xi with
  | Ibnd xl xu => F.real xl && F.real xu
  | _ => false
  end.

Definition lower_bounded xi :=
  match xi with
  | Ibnd xl _ => F.real xl
  | _ => false
  end.

Definition upper_bounded xi :=
  match xi with
  | Ibnd _ xu => F.real xu
  | _ => false
  end.

Definition subset xi yi :=
  match xi, yi with
  | Ibnd xl xu, Ibnd yl yu =>
    match F.cmp xl yl with
    | Xund => negb (F.real yl)
    | Xlt => false
    | _ => true
    end &&
    match F.cmp xu yu with
    | Xund => negb (F.real yu)
    | Xgt => false
    | _ => true
    end
  | _, Inan => true
  | _, _ => false
  end.

Definition overlap xi yi :=
  match xi, yi with
  | Ibnd xl xu, Ibnd yl yu =>
    match F.cmp xl yl with
    | Xund =>
      match F.real xl, F.real yl with
      | false, true => match F.cmp xu yl with Xlt => false | _ => true end
      | true, false => match F.cmp yu xl with Xlt => false | _ => true end
      | _, _ => true
      end
    | Xlt => match F.cmp xu yl with Xlt => false | _ => true end
    | _ => match F.cmp yu xl with Xlt => false | _ => true end
    end
  | Inan, _ => true
  | _, Inan => true
  end.

Definition join xi yi :=
  match xi, yi with
  | Ibnd xl xu, Ibnd yl yu =>
    Ibnd (F.min xl yl) (F.max xu yu)
  | _, _ => Inan
  end.

Definition meet xi yi :=
  match xi, yi with
  | Ibnd xl xu, Ibnd yl yu =>
    let l :=
      match F.real xl, F.real yl with
      | false, _ => yl
      | true, false => xl
      | true, true => F.max xl yl
      end in
    let u :=
      match F.real xu, F.real yu with
      | false, _ => yu
      | true, false => xu
      | true, true => F.min xu yu
      end in
    Ibnd l u
  | _, _ => Inan
  end.

Definition mask xi yi : type :=
  match yi with
  | Inan => yi
  | _ => xi
  end.

Definition lower_extent xi :=
  match xi with
  | Ibnd _ xu => Ibnd F.nan xu
  | _ => Inan
  end.

Definition upper_extent xi :=
  match xi with
  | Ibnd xl _ => Ibnd xl F.nan
  | _ => Inan
  end.

Definition whole := Ibnd F.nan F.nan.

Definition lower xi :=
  match xi with
  | Ibnd xl _ => xl
  | _ => F.nan
  end.

Definition upper xi :=
  match xi with
  | Ibnd _ xu => xu
  | _ => F.nan
  end.

Definition fromZ n := let f := F.fromZ n in Ibnd f f.

Definition midpoint xi :=
  match xi with
  | Inan => F.zero
  | Ibnd xl xu =>
    match F.cmp xl F.zero, F.cmp xu F.zero with
    | Xund, Xund => F.zero
    | Xeq, Xeq => F.zero
    | Xlt, Xund => F.zero
    | Xund, Xgt => F.zero
    | Xeq, Xund => F.fromZ 1%Z
    | Xund, Xeq => F.fromZ (-1)%Z
    | Xgt, Xund => F.scale xl (F.ZtoS 1%Z)
    | Xund, Xlt => F.scale xu (F.ZtoS 1%Z)
    | _, _ => F.scale2 (F.add_exact xl xu) (F.ZtoS (-1)%Z)
    end
  end.

Definition extension f fi := forall b x,
  contains (convert b) x -> contains (convert (fi b)) (f x).

Definition extension_2 f fi := forall ix iy x y,
  contains (convert ix) x ->
  contains (convert iy) y ->
  contains (convert (fi ix iy)) (f x y).

Definition sign_large_ xl xu :=
  match F.cmp xl F.zero, F.cmp xu F.zero with
  | Xeq, Xeq => Xeq
  | _, Xlt => Xlt
  | _, Xeq => Xlt
  | Xgt, _ => Xgt
  | Xeq, _ => Xgt
  | _, _ => Xund
  end.

Definition sign_large xi :=
  match xi with
  | Ibnd xl xu => sign_large_ xl xu
  | Inan => Xund
  end.

Definition sign_strict_ xl xu :=
  match F.cmp xl F.zero, F.cmp xu F.zero with
  | Xeq, Xeq => Xeq
  | _, Xlt => Xlt
  | Xgt, _ => Xgt
  | _, _ => Xund
  end.

Definition sign_strict xi :=
  match xi with
  | Ibnd xl xu => sign_strict_ xl xu
  | Inan => Xund
  end.

Definition neg xi :=
  match xi with
  | Ibnd xl xu => Ibnd (F.neg xu) (F.neg xl)
  | Inan => Inan
  end.

Definition abs xi :=
  match xi with
  | Ibnd xl xu =>
    match sign_large_ xl xu with
    | Xgt => xi
    | Xeq => Ibnd F.zero F.zero
    | Xlt => Ibnd (F.neg xu) (F.neg xl)
    | Xund => Ibnd F.zero (F.max (F.neg xl) xu)
    end
  | Inan => Inan
  end.

Definition scale xi d :=
  match xi with
  | Ibnd xl xu => Ibnd (F.scale xl d) (F.scale xu d)
  | Inan => Inan
  end.

Definition scale2 xi d :=
  match xi with
  | Ibnd xl xu => Ibnd (F.scale2 xl d) (F.scale2 xu d)
  | Inan => Inan
  end.

Definition sqrt prec xi :=
  match xi with
  | Ibnd xl xu =>
    match F.cmp xl F.zero with
    | Xeq => Ibnd F.zero (F.sqrt rnd_UP prec xu)
    | Xgt => Ibnd (F.sqrt rnd_DN prec xl) (F.sqrt rnd_UP prec xu)
    | _ => Inan
    end
  | Inan => Inan
  end.

Definition add prec xi yi :=
  match xi, yi with
  | Ibnd xl xu, Ibnd yl yu =>
    Ibnd (F.add rnd_DN prec xl yl) (F.add rnd_UP prec xu yu)
  | _, _ => Inan
  end.

Definition sub prec xi yi :=
  match xi, yi with
  | Ibnd xl xu, Ibnd yl yu =>
    Ibnd (F.sub rnd_DN prec xl yu) (F.sub rnd_UP prec xu yl)
  | _, _ => Inan
  end.

Definition mul_mixed prec xi y :=
  match xi with
  | Ibnd xl xu =>
    match F.cmp y F.zero with
    | Xlt => Ibnd (F.mul rnd_DN prec xu y) (F.mul rnd_UP prec xl y)
    | Xeq => Ibnd F.zero F.zero
    | Xgt => Ibnd (F.mul rnd_DN prec xl y) (F.mul rnd_UP prec xu y)
    | Xund => Inan
    end
  | Inan => Inan
  end.

Definition div_mixed_r prec xi y :=
  match xi with
  | Ibnd xl xu =>
    match F.cmp y F.zero with
    | Xlt => Ibnd (F.div rnd_DN prec xu y) (F.div rnd_UP prec xl y)
    | Xgt => Ibnd (F.div rnd_DN prec xl y) (F.div rnd_UP prec xu y)
    | _ => Inan
    end
  | Inan => Inan
  end.

Definition sqr prec xi :=
  match xi with
  | Ibnd xl xu =>
    match sign_large_ xl xu with
    | Xund =>
      let xm := F.max (F.abs xl) xu in
      Ibnd F.zero (F.mul rnd_UP prec xm xm)
    | Xeq => Ibnd F.zero F.zero
    | Xlt => Ibnd (F.mul rnd_DN prec xu xu) (F.mul rnd_UP prec xl xl)
    | Xgt => Ibnd (F.mul rnd_DN prec xl xl) (F.mul rnd_UP prec xu xu)
    end
  | _ => Inan
  end.

Definition mul prec xi yi :=
  match xi, yi with
  | Ibnd xl xu, Ibnd yl yu =>
    match sign_large_ xl xu, sign_large_ yl yu with
    | Xeq, _ => Ibnd F.zero F.zero
    | _, Xeq => Ibnd F.zero F.zero
    | Xgt, Xgt => Ibnd (F.mul rnd_DN prec xl yl) (F.mul rnd_UP prec xu yu)
    | Xlt, Xlt => Ibnd (F.mul rnd_DN prec xu yu) (F.mul rnd_UP prec xl yl)
    | Xgt, Xlt => Ibnd (F.mul rnd_DN prec xu yl) (F.mul rnd_UP prec xl yu)
    | Xlt, Xgt => Ibnd (F.mul rnd_DN prec xl yu) (F.mul rnd_UP prec xu yl)
    | Xgt, Xund => Ibnd (F.mul rnd_DN prec xu yl) (F.mul rnd_UP prec xu yu)
    | Xlt, Xund => Ibnd (F.mul rnd_DN prec xl yu) (F.mul rnd_UP prec xl yl)
    | Xund, Xgt => Ibnd (F.mul rnd_DN prec xl yu) (F.mul rnd_UP prec xu yu)
    | Xund, Xlt => Ibnd (F.mul rnd_DN prec xu yl) (F.mul rnd_UP prec xl yl)
    | Xund, Xund => Ibnd (F.min (F.mul rnd_DN prec xl yu) (F.mul rnd_DN prec xu yl))
                         (F.max (F.mul rnd_UP prec xl yl) (F.mul rnd_UP prec xu yu))
    end
  | _, _ => Inan
  end.

Definition Fdivz mode prec x y :=
  if F.real y then F.div mode prec x y else F.zero.

Definition inv prec xi :=
  match xi with
  | Ibnd xl xu =>
    match sign_strict_ xl xu with
    | Xund => Inan
    | Xeq => Inan
    | _ => let one := F.fromZ 1 in
      Ibnd (Fdivz rnd_DN prec one xu) (Fdivz rnd_UP prec one xl)
    end
  | _ => Inan
  end.

Definition div prec xi yi :=
  match xi, yi with
  | Ibnd xl xu, Ibnd yl yu =>
    match sign_strict_ xl xu, sign_strict_ yl yu with
    | _, Xund => Inan
    | _, Xeq => Inan
    | Xeq, _ => Ibnd F.zero F.zero
    | Xgt, Xgt => Ibnd (Fdivz rnd_DN prec xl yu) (F.div rnd_UP prec xu yl)
    | Xlt, Xlt => Ibnd (Fdivz rnd_DN prec xu yl) (F.div rnd_UP prec xl yu)
    | Xgt, Xlt => Ibnd (F.div rnd_DN prec xu yu) (Fdivz rnd_UP prec xl yl)
    | Xlt, Xgt => Ibnd (F.div rnd_DN prec xl yl) (Fdivz rnd_UP prec xu yu)
    | Xund, Xgt => Ibnd (F.div rnd_DN prec xl yl) (F.div rnd_UP prec xu yl)
    | Xund, Xlt => Ibnd (F.div rnd_DN prec xu yu) (F.div rnd_UP prec xl yu)
    end
  | _, _ => Inan
  end.

Fixpoint Fpower_pos rnd prec x n :=
  match n with
  | xH => x
  | xO p => Fpower_pos rnd prec (F.mul rnd prec x x) p
  | xI p => F.mul rnd prec x (Fpower_pos rnd prec (F.mul rnd prec x x) p)
  end.

Definition power_pos prec xi n :=
  match xi with
  | Ibnd xl xu =>
    match sign_large_ xl xu with
    | Xund =>
      match n with
      | xH => xi
      | xO _ =>
        let xm := F.max (F.abs xl) xu in
        Ibnd F.zero (Fpower_pos rnd_UP prec xm n)
      | xI _ => Ibnd (F.neg (Fpower_pos rnd_UP prec (F.abs xl) n)) (Fpower_pos rnd_UP prec xu n)
      end
    | Xeq => Ibnd F.zero F.zero
    | Xlt =>
      match n with
      | xH => xi
      | xO _ => Ibnd (Fpower_pos rnd_DN prec (F.abs xu) n) (Fpower_pos rnd_UP prec (F.abs xl) n)
      | xI _ => Ibnd (F.neg (Fpower_pos rnd_UP prec (F.abs xl) n)) (F.neg (Fpower_pos rnd_DN prec (F.abs xu) n))
      end
    | Xgt => Ibnd (Fpower_pos rnd_DN prec xl n) (Fpower_pos rnd_UP prec xu n)
    end
  | _ => Inan
  end.

Definition power_int prec xi n :=
  match n with
  | Zpos p => power_pos prec xi p
  | Z0 => match xi with Inan => Inan | _ => fromZ 1 end
  | Zneg p => inv prec (power_pos prec xi p)
  end.

Ltac convert_clean :=
  repeat
  match goal with
  | H: context [FtoX (F.toF ?v)] |- _
    => change (FtoX (F.toF v)) with (convert_bound v) in H
  | |- context [FtoX (F.toF ?v)]
    => change (FtoX (F.toF v)) with (convert_bound v)
  end.

Ltac xreal_tac v :=
  convert_clean ;
  let X := fresh "X" in
  case_eq (convert_bound v) ;
  [ intros X ; try exact I
  | let r := fresh "r" in
    intros r X ; try rewrite X in * ].

Ltac xreal_tac2 :=
  convert_clean ;
  match goal with
  | H: convert_bound ?v = Xreal _ |- context [convert_bound ?v] =>
    rewrite H
  | |- context [convert_bound ?v] => xreal_tac v
  end.

Ltac bound_tac :=
  unfold xround ;
  match goal with
  | |- (round ?r rnd_DN ?p ?v <= ?w)%R =>
    apply Rle_trans with (1 := proj1 (proj2 (Fcore_generic_fmt.round_DN_pt F.radix (Fcore_FLX.FLX_exp (Zpos p)) v)))
  | |- (?w <= round ?r rnd_UP ?p ?v)%R =>
    apply Rle_trans with (2 := proj1 (proj2 (Fcore_generic_fmt.round_UP_pt F.radix (Fcore_FLX.FLX_exp (Zpos p)) v)))
  end.

Lemma lower_correct :
  forall xi : type, convert_bound (lower xi) = Xlower (convert xi).
Proof.
intros [|xl xu].
simpl.
unfold convert_bound.
now rewrite F.nan_correct.
easy.
Qed.

Lemma upper_correct :
  forall xi : type, convert_bound (upper xi) = Xupper (convert xi).
Proof.
intros [|xl xu].
simpl.
unfold convert_bound.
now rewrite F.nan_correct.
easy.
Qed.

Lemma real_correct :
  forall (A : Type) x (y1 y2 : A),
  (if F.real x then y1 else y2) = match convert_bound x with Xnan => y2 | _ => y1 end.
intros.
generalize (F.real_correct x).
unfold convert_bound.
case (F.toF x) ; intros ; rewrite H ; apply refl_equal.
Qed.

Lemma Fcmp_le_mixed :
  forall xl yu,
  F.cmp xl yu <> Xgt -> le_mixed (convert_bound xl) (convert_bound yu).
intros.
rewrite F.cmp_correct in H.
rewrite Fcmp_correct in H.
xreal_tac yu.
xreal_tac xl.
refine (Rnot_lt_le _ _ _).
intro H0.
simpl in H.
elim H.
now rewrite Rcompare_Gt.
Qed.

Theorem subset_correct :
  forall xi yi : type,
  subset xi yi = true -> Interval_interval.subset (convert xi) (convert yi).
intros xi yi.
case xi ; case yi ; try (simpl ; intros ; try exact I ; discriminate).
intros yl yu xl xu H.
destruct (andb_prop _ _ H) as (H1, H2).
split.
(* lower bound *)
generalize H1. clear.
rewrite F.cmp_correct.
rewrite Fcmp_correct.
unfold le_lower, le_upper, convert_bound.
case (FtoX (F.toF xl)) ; simpl.
unfold negb. rewrite real_correct.
intros. now xreal_tac2.
intros xrl.
xreal_tac2.
split.
destruct (Rcompare_spec xrl r) ; intros ; simpl.
discriminate H1.
rewrite H.
apply Rle_refl.
apply Ropp_le_contravar.
now left.
(* upper bound *)
generalize H2. clear.
rewrite F.cmp_correct.
rewrite Fcmp_correct.
unfold le_upper, convert_bound.
case (FtoX (F.toF xu)) ; simpl.
unfold negb. rewrite real_correct.
intros. now xreal_tac2.
intros xru.
xreal_tac2.
split.
destruct (Rcompare_spec xru r) ; intros.
now left.
now right.
now right.
Qed.

Lemma Xmin_Rle : forall a b c,
  Xreal c = Xmin (Xreal a) (Xreal b) -> (c <= a /\ c <= b)%R.
Proof.
unfold Xmin; intros a b c H.
injection H; intros H'; rewrite H'.
now split; [apply Rmin_l|apply Rmin_r].
Qed.

Lemma Xmax_Rle : forall a b c,
  Xreal c = Xmax (Xreal a) (Xreal b) -> (a <= c /\ b <= c)%R.
Proof.
unfold Xmax; intros a b c H.
injection H; intros H'; rewrite H'.
now split; [apply Rmax_l|apply Rmax_r].
Qed.

Lemma join_correct :
  forall xi yi v,
  contains (convert xi) v \/ contains (convert yi) v ->
  contains (convert (join xi yi)) v.
Proof.
intros [|xl xu] [|yl yu] [|v]; simpl; try tauto.
pose proof F.min_correct xl yl as Hmin.
pose proof F.max_correct xu yu as Hmax.
rewrite Fmin_correct in Hmin.
rewrite Fmax_correct in Hmax.
intros [(Hx1,Hx2)|(Hx1,Hx2)]; split;
  xreal_tac2;
  convert_clean;
  [xreal_tac xl;xreal_tac yl|
    xreal_tac xu;xreal_tac yu|
    xreal_tac xl;xreal_tac yl|
    xreal_tac xu;xreal_tac yu];
  try rewrite X0 in Hmin;
  try rewrite X1 in Hmin;
  try rewrite X0 in Hmax;
  try rewrite X1 in Hmax;
  try discriminate.
apply Rle_trans with (r2 := r0); trivial.
exact (proj1 (Xmin_Rle _ _ _ Hmin)).
apply Rle_trans with (r2 := r0); trivial.
exact (proj1 (Xmax_Rle _ _ _ Hmax)).
apply Rle_trans with (r2 := r1); trivial.
exact (proj2 (Xmin_Rle _ _ _ Hmin)).
apply Rle_trans with (r2 := r1); trivial.
exact (proj2 (Xmax_Rle _ _ _ Hmax)).
Qed.

Theorem meet_correct :
  forall xi yi v,
  contains (convert xi) v -> contains (convert yi) v ->
  contains (convert (meet xi yi)) v.
intros [|xl xu] [|yl yu] [|v] ; simpl ; intros Hx Hy ; trivial.
destruct Hx as (Hx1, Hx2).
destruct Hy as (Hy1, Hy2).
split.
(* . *)
rewrite real_correct.
xreal_tac xl.
exact Hy1.
rewrite real_correct.
xreal_tac yl.
now rewrite X.
unfold convert_bound in *.
rewrite F.max_correct.
rewrite Fmax_correct.
rewrite X, X0.
simpl.
now apply Rmax_best.
(* . *)
rewrite real_correct.
xreal_tac xu.
exact Hy2.
rewrite real_correct.
xreal_tac yu.
now rewrite X.
unfold convert_bound in *.
rewrite F.min_correct.
rewrite Fmin_correct.
rewrite X, X0.
simpl.
now apply Rmin_best.
Qed.

Definition bounded_prop xi :=
  convert xi = Interval_interval.Ibnd (convert_bound (lower xi)) (convert_bound (upper xi)).

Theorem lower_bounded_correct :
  forall xi,
  lower_bounded xi = true ->
  convert_bound (lower xi) = Xreal (proj_val (convert_bound (lower xi))) /\
  bounded_prop xi.
unfold lower_bounded.
intros [|xl xu] H.
discriminate H.
generalize (F.real_correct xl).
rewrite H.
clear H.
unfold convert_bound.
simpl.
case (F.toF xl).
intro H.
discriminate H.
repeat split.
repeat split.
Qed.

Theorem upper_bounded_correct :
  forall xi,
  upper_bounded xi = true ->
  convert_bound (upper xi) = Xreal (proj_val (convert_bound (upper xi))) /\
  bounded_prop xi.
unfold upper_bounded.
intros [|xl xu] H.
discriminate H.
generalize (F.real_correct xu).
rewrite H.
clear H.
unfold convert_bound.
simpl.
case (F.toF xu).
intro H.
discriminate H.
repeat split.
repeat split.
Qed.

Theorem bounded_correct :
  forall xi,
  bounded xi = true ->
  lower_bounded xi = true /\ upper_bounded xi = true.
unfold bounded.
intros [|xl xu] H.
discriminate H.
now apply andb_prop.
Qed.

Theorem lower_extent_correct :
  forall xi x y,
  contains (convert xi) (Xreal y) ->
  (x <= y)%R ->
  contains (convert (lower_extent xi)) (Xreal x).
intros [|xl xu] x y Hy Hx.
exact I.
split.
unfold convert_bound.
rewrite F.nan_correct.
exact I.
simpl in Hy.
xreal_tac xu.
apply Rle_trans with (1 := Hx).
exact (proj2 Hy).
Qed.

Theorem upper_extent_correct :
  forall xi x y,
  contains (convert xi) (Xreal y) ->
  (y <= x)%R ->
  contains (convert (upper_extent xi)) (Xreal x).
intros [|xl xu] x y Hy Hx.
exact I.
split.
simpl in Hy.
xreal_tac xl.
apply Rle_trans with (2 := Hx).
exact (proj1 Hy).
unfold convert_bound.
rewrite F.nan_correct.
exact I.
Qed.

Theorem whole_correct :
  forall x,
  contains (convert whole) (Xreal x).
intros x.
simpl.
unfold convert_bound.
rewrite F.nan_correct.
split ; split.
Qed.

Lemma sign_large_correct_ :
  forall xl xu x,
  contains (convert (Ibnd xl xu)) (Xreal x) ->
  match sign_large_ xl xu with
  | Xeq => x = R0 /\ FtoX (F.toF xl) = Xreal R0 /\ FtoX (F.toF xu) = Xreal R0
  | Xlt => (x <= 0)%R /\ (match FtoX (F.toF xl) with Xreal rl => (rl <= 0)%R | _=> True end) /\ (exists ru, FtoX (F.toF xu) = Xreal ru /\ (ru <= 0)%R)
  | Xgt => (0 <= x)%R /\ (match FtoX (F.toF xu) with Xreal ru => (0 <= ru)%R | _=> True end) /\ (exists rl, FtoX (F.toF xl) = Xreal rl /\ (0 <= rl)%R)
  | Xund =>
    match FtoX (F.toF xl) with Xreal rl => (rl <= 0)%R | _=> True end /\
    match FtoX (F.toF xu) with Xreal ru => (0 <= ru)%R | _=> True end
  end.
intros xl xu x (Hxl, Hxu).
unfold sign_large_.
do 2 rewrite F.cmp_correct.
rewrite F.zero_correct.
generalize Hxl Hxu.
clear.
unfold convert_bound.
case (F.toF xl) ; [ idtac | idtac | intros sl ml el ; case sl ] ;
  ( case (F.toF xu) ; [ idtac | idtac | intros su mu eu ; case su ] ) ; simpl ;
  intros ; repeat split ; try exact I ; try assumption ;
  try refl_exists ; try apply Rle_refl ;
  try ( try apply Rle_trans with (2 := Hxl) ; apply Rlt_le ; apply FtoR_Rpos ) ;
  try ( try apply Rle_trans with (1 := Hxu) ; apply Rlt_le ; apply FtoR_Rneg ).
apply Rle_antisym ; assumption.
apply Rle_trans with x ; assumption.
apply Rle_trans with (1 := Hxl).
apply Rle_trans with (1 := Hxu).
apply Rlt_le.
apply FtoR_Rneg.
Qed.

Theorem sign_large_correct :
  forall xi,
  match sign_large xi with
  | Xeq => forall x, contains (convert xi) x -> x = Xreal 0
  | Xlt => forall x, contains (convert xi) x -> x = Xreal (proj_val x) /\ Rle (proj_val x) 0
  | Xgt => forall x, contains (convert xi) x -> x = Xreal (proj_val x) /\ Rle 0 (proj_val x)
  | Xund => True
  end.
intros [|xl xu].
exact I.
generalize (sign_large_correct_ xl xu).
unfold sign_large.
case (sign_large_ xl xu) ;
  try intros H [|x] Hx ;
  try (elim Hx ; fail) ;
  try refl_exists ;
  try apply f_equal ;
  exact (proj1 (H _ Hx)).
Qed.

Lemma sign_strict_correct_ :
  forall xl xu x,
  contains (convert (Ibnd xl xu)) (Xreal x) ->
  match sign_strict_ xl xu with
  | Xeq => x = R0 /\ convert_bound xl = Xreal R0 /\ convert_bound xu = Xreal R0
  | Xlt => (x < 0)%R /\ (match convert_bound xl with Xreal rl => (rl < 0)%R | _=> True end) /\ (exists ru, convert_bound xu = Xreal ru /\ (ru < 0)%R)
  | Xgt => (0 < x)%R /\ (match convert_bound xu with Xreal ru => (0 < ru)%R | _=> True end) /\ (exists rl, convert_bound xl = Xreal rl /\ (0 < rl)%R)
  | Xund =>
    match convert_bound xl with Xreal rl => (rl <= 0)%R | _=> True end /\
    match convert_bound xu with Xreal ru => (0 <= ru)%R | _=> True end
  end.
intros xl xu x (Hxl, Hxu).
unfold sign_strict_.
do 2 rewrite F.cmp_correct.
rewrite F.zero_correct.
generalize Hxl Hxu.
clear.
unfold convert_bound.
case_eq (F.toF xl) ; [ idtac | idtac | intros sl ml el ; case sl ] ;
  ( case_eq (F.toF xu) ; [ idtac | idtac | intros su mu eu ; case su ] ) ; simpl ;
  intros ; repeat split ; try exact I ; try assumption ;
  try refl_exists ; try apply Rle_refl ;
  try ( try apply Rlt_le_trans with (2 := Hxl) ; try apply Rlt_le ; apply FtoR_Rpos ) ;
  try ( try apply Rle_lt_trans with (1 := Hxu) ; try apply Rlt_le ; apply FtoR_Rneg ).
apply Rle_antisym ; assumption.
apply Rle_lt_trans with (1 := Hxl).
apply Rle_lt_trans with (1 := Hxu).
apply FtoR_Rneg.
apply Rlt_le_trans with (2 := Hxu).
apply Rlt_le_trans with (2 := Hxl).
apply FtoR_Rpos.
apply Rle_lt_trans with (1 := Hxl).
apply Rle_lt_trans with (1 := Hxu).
apply FtoR_Rneg.
Qed.

Theorem sign_strict_correct :
  forall xi,
  match sign_strict xi with
  | Xeq => forall x, contains (convert xi) x -> x = Xreal 0
  | Xlt => forall x, contains (convert xi) x -> x = Xreal (proj_val x) /\ Rlt (proj_val x) 0
  | Xgt => forall x, contains (convert xi) x -> x = Xreal (proj_val x) /\ Rlt 0 (proj_val x)
  | Xund => True
  end.
Proof.
intros [|xl xu].
exact I.
generalize (sign_strict_correct_ xl xu).
unfold sign_strict.
case (sign_strict_ xl xu) ;
  try intros H [|x] Hx ;
  try (elim Hx ; fail) ;
  try refl_exists ;
  try apply f_equal ;
  exact (proj1 (H _ Hx)).
Qed.

Theorem fromZ_correct :
  forall v,
  contains (convert (fromZ v)) (Xreal (Z2R v)).
intros.
simpl.
unfold convert_bound.
rewrite F.fromZ_correct.
split ; apply Rle_refl.
Qed.

Theorem midpoint_correct :
  forall xi,
  (exists x, contains (convert xi) x) ->
  convert_bound (midpoint xi) = Xreal (proj_val (convert_bound (midpoint xi))) /\
  contains (convert xi) (convert_bound (midpoint xi)).
intros [|xl xu].
intros _.
refine (conj _ I).
unfold convert_bound.
simpl.
now rewrite F.zero_correct.
intros (x, Hx).
destruct x as [|x].
elim Hx.
destruct Hx as (Hx1,Hx2).
assert (Hr: (1 <= Z2R (Zpower_pos F.radix 1))%R).
rewrite Z2R_Zpower_pos.
rewrite <- bpow_powerRZ.
now apply (bpow_le F.radix 0).
(* . *)
simpl.
repeat rewrite F.cmp_correct.
repeat rewrite Fcmp_correct.
xreal_tac xl ; xreal_tac xu ; simpl ;
  change (convert_bound F.zero) with (FtoX (F.toF F.zero)) ;
  rewrite F.zero_correct ; simpl.
repeat split.
(* infinite lower *)
destruct (Rcompare_spec r 0) ; unfold convert_bound.
rewrite F.scale_correct, Fscale_correct.
unfold convert_bound in X0.
rewrite X0.
simpl.
repeat split.
pattern r at 2 ; rewrite <- Rmult_1_r.
apply Rmult_le_compat_neg_l.
exact (Rlt_le _ _ H).
exact Hr.
rewrite H.
rewrite F.fromZ_correct.
repeat split.
now apply (Z2R_le (-1) 0).
rewrite F.zero_correct.
repeat split.
exact (Rlt_le _ _ H).
(* infinite upper *)
destruct (Rcompare_spec r 0) ; unfold convert_bound.
rewrite F.zero_correct.
repeat split.
exact (Rlt_le _ _ H).
rewrite H.
rewrite F.fromZ_correct.
repeat split.
now apply (Z2R_le 0 1).
rewrite F.scale_correct, Fscale_correct.
unfold convert_bound in X.
rewrite X.
simpl.
repeat split.
pattern r at 1 ; rewrite <- Rmult_1_r.
apply Rmult_le_compat_l.
exact (Rlt_le _ _ H).
exact Hr.
(* finite bounds *)
assert (
  match FtoX (F.toF (F.scale2 (F.add_exact xl xu) (F.ZtoS (-1)))) with
  | Xnan => False
  | Xreal x0 => (r <= x0 <= r0)%R
  end).
rewrite F.scale2_correct. 2: apply refl_equal.
rewrite Fscale2_correct. 2: apply F.even_radix_correct.
rewrite F.add_exact_correct.
rewrite Fadd_exact_correct.
unfold convert_bound in *.
rewrite X, X0.
simpl.
pattern r at 1 ; rewrite <- eps2.
pattern r0 at 3 ; rewrite <- eps2.
rewrite Rmult_plus_distr_r.
split.
apply Rplus_le_compat_l.
apply Rmult_le_compat_r.
auto with real.
eapply Rle_trans ; eassumption.
apply Rplus_le_compat_r.
apply Rmult_le_compat_r.
auto with real.
eapply Rle_trans ; eassumption.
(* finite bounds 2 *)
case_eq (FtoX (F.toF (F.scale2 (F.add_exact xl xu) (F.ZtoS (-1))))) ; intros.
rewrite H0 in H.
elim H.
destruct (Rcompare_spec r 0) as [H1|H1|H1] ;
  destruct (Rcompare_spec r0 0) as [H2|H2|H2] ;
  unfold convert_bound ;
  try (
    refine (conj _ H) ;
    rewrite H0 ;
    apply refl_equal).
rewrite F.zero_correct.
simpl.
rewrite H1, H2.
repeat split ; apply Rle_refl.
Qed.

Theorem mask_correct :
  extension_2 Xmask mask.
now intros xi [|yl yu] x [|y] Hx Hy.
Qed.

Theorem neg_correct :
  extension Xneg neg.
intros [ | xl xu] [ | x] ; simpl ; trivial.
intros (Hxl, Hxu).
unfold convert_bound.
split ; rewrite F.neg_correct ; rewrite Fneg_correct ;
  unfold Xneg ; [ xreal_tac xu | xreal_tac xl ] ;
  apply Ropp_le_contravar ; assumption.
Qed.

Theorem abs_correct :
  extension Xabs abs.
intros [ | xl xu] [ | x] Hx ; trivial ; [ elim Hx | idtac ].
simpl.
generalize (sign_large_correct_ _ _ _ Hx).
case (sign_large_ xl xu) ; intros.
(* zero *)
rewrite (proj1 H).
rewrite Rabs_R0.
simpl.
unfold convert_bound.
rewrite F.zero_correct.
split ; exact (Rle_refl R0).
(* negative *)
rewrite (Rabs_left1 _ (proj1 H)).
exact (neg_correct _ _ Hx).
(* positive *)
rewrite (Rabs_right _ (Rle_ge _ _ (proj1 H))).
exact Hx.
(* both *)
clear H.
simpl.
unfold convert_bound.
rewrite F.zero_correct.
split.
exact (Rabs_pos x).
(* - upper *)
rewrite F.max_correct.
rewrite Fmax_correct.
rewrite F.neg_correct.
rewrite Fneg_correct.
unfold contains, convert, convert_bound in Hx.
destruct Hx as (Hxl, Hxu).
do 2 xreal_tac2.
simpl.
apply <- Rmax_Rle.
unfold Rabs.
destruct (Rcase_abs x) as [H|H].
left.
apply Ropp_le_contravar.
exact Hxl.
right.
exact Hxu.
Qed.

Theorem abs_ge_0 :
  forall xi, convert xi <> Interval_interval.Inan ->
  le_lower' (Xreal 0) (FtoX (F.toF (lower (abs xi)))).
Proof.
intros [|xl xu].
intros H.
now elim H.
intros _.
simpl.
unfold sign_large_.
rewrite 2!F.cmp_correct, 2!Fcmp_correct, F.zero_correct.
case_eq (FtoX (F.toF xl)) ; case_eq (FtoX (F.toF xu)).
simpl.
intros _ _.
rewrite F.zero_correct.
apply Rle_refl.
simpl.
intros ru Hu _.
case Rcompare_spec ; simpl ; intros H.
rewrite F.neg_correct, Fneg_correct, Hu.
simpl.
rewrite <- Ropp_0.
apply Ropp_le_contravar.
now apply Rlt_le.
rewrite F.neg_correct, Fneg_correct, Hu.
rewrite H.
simpl.
rewrite Ropp_0.
apply Rle_refl.
rewrite F.zero_correct.
apply Rle_refl.
intros _ rl Hl.
simpl.
case Rcompare_spec ; simpl ; intros H.
rewrite F.zero_correct.
apply Rle_refl.
rewrite Hl, H.
apply Rle_refl.
rewrite Hl.
now apply Rlt_le.
intros ru Hu rl Hl.
simpl.
case Rcompare_spec ; simpl ; intros H1 ;
  case Rcompare_spec ; simpl ; intros H2 ;
    try rewrite F.neg_correct, Fneg_correct ;
    try rewrite F.zero_correct ;
    try apply Rle_refl.
rewrite <- Ropp_0, Hu.
apply Ropp_le_contravar.
now apply Rlt_le.
rewrite Hu, H2.
simpl.
rewrite Ropp_0.
apply Rle_refl.
rewrite <- Ropp_0, Hu.
apply Ropp_le_contravar.
now apply Rlt_le.
rewrite Hl, H1.
apply Rle_refl.
rewrite <- Ropp_0, Hu.
apply Ropp_le_contravar.
now apply Rlt_le.
rewrite Hu, H2.
simpl.
rewrite Ropp_0.
apply Rle_refl.
rewrite Hl.
now apply Rlt_le.
Qed.

Theorem abs_ge_0' :
  forall xi, (0 <= proj_val (FtoX (F.toF (lower (abs xi)))))%R.
Proof.
intros [|xl xu].
simpl.
rewrite F.nan_correct.
apply Rle_refl.
refine (_ (abs_ge_0 (Ibnd xl xu) _)).
2: discriminate.
simpl.
now case FtoX.
Qed.

Theorem scale2_correct :
  forall xi x d,
  contains (convert xi) x ->
  contains (convert (scale2 xi (F.ZtoS d))) (Xmul x (Xreal (bpow radix2 d))).
intros [ | xl xu].
split.
intros [ | x] d Hx.
elim Hx.
unfold convert, convert_bound in Hx.
destruct Hx as (Hxl, Hxu).
unfold convert, convert_bound, scale2.
do 2 ( rewrite F.scale2_correct ; [ idtac | apply refl_equal ] ).
do 2 ( rewrite Fscale2_correct ; [ idtac | apply F.even_radix_correct ]).
split ; xreal_tac2 ; simpl ;
  ( apply Rmult_le_compat_r ;
    [ (apply Rlt_le ; apply bpow_gt_0) | assumption ] ).
Qed.

Theorem add_correct :
  forall prec,
  extension_2 Xadd (add prec).
intros prec [ | xl xu] [ | yl yu] [ | x] [ | y] ; trivial.
intros (Hxl, Hxu) (Hyl, Hyu).
simpl.
unfold convert_bound.
split ;
  rewrite F.add_correct ; rewrite Fadd_correct ;
  do 2 xreal_tac2 ; unfold Xadd ; bound_tac ;
  apply Rplus_le_compat ; assumption.
Qed.

Theorem sub_correct :
  forall prec,
  extension_2 Xsub (sub prec).
intros prec [ | xl xu] [ | yl yu] [ | x] [ | y] ; trivial.
intros (Hxl, Hxu) (Hyl, Hyu).
simpl.
unfold convert_bound.
split ;
  rewrite F.sub_correct ; rewrite Fsub_correct ;
  do 2 xreal_tac2 ; unfold Xsub ; bound_tac ;
  unfold Rminus ; apply Rplus_le_compat ;
  try apply Ropp_le_contravar ; assumption.
Qed.

Lemma is_zero_float :
  forall r s m e,
  is_zero (FtoR r s m e) = false.
intros.
destruct (is_zero_spec (FtoR r s m e)).
destruct s.
elim Rlt_not_eq with (2 := H).
apply FtoR_Rneg.
elim Rgt_not_eq with (2 := H).
apply FtoR_Rpos.
apply refl_equal.
Qed.

Lemma is_positive_float :
  forall r s m e,
  is_positive (FtoR r s m e) = negb s.
intros.
destruct (is_positive_spec (FtoR r s m e)) ;
  destruct s ; try apply refl_equal.
elim Rlt_not_ge with (1 := H).
left.
apply FtoR_Rneg.
elim Rgt_not_le with (2 := H).
apply FtoR_Rpos.
Qed.

Lemma is_negative_float :
  forall r s m e,
  is_negative (FtoR r s m e) = s.
intros.
destruct (is_negative_spec (FtoR r s m e)) ;
  destruct s ; try apply refl_equal.
elim Rlt_not_ge with (1 := H).
left.
apply FtoR_Rpos.
elim Rgt_not_le with (2 := H).
apply FtoR_Rneg.
Qed.

Theorem sqrt_correct :
  forall prec, extension Xsqrt (sqrt prec).
intros prec [ | xl xu] [ | x] ; simpl ; trivial.
intro.
elim H.
intros (Hxl, Hxu).
rewrite F.cmp_correct.
rewrite Fcmp_correct.
rewrite F.zero_correct.
generalize Hxl. clear Hxl.
unfold convert_bound.
case_eq (FtoX (F.toF xl)) ; [ split | idtac ].
intros rl Hrl Hxl.
simpl.
destruct (is_negative_spec x).
rewrite Rcompare_Lt.
exact I.
apply Rle_lt_trans with (1 := Hxl) (2 := H).
destruct (Rcompare_spec rl 0) ; simpl ; unfold convert_bound ;
  repeat ( rewrite F.sqrt_correct ; rewrite Fsqrt_correct ).
exact I.
(* xl zero *)
rewrite F.zero_correct.
simpl.
split.
now apply sqrt_positivity.
unfold convert_bound in Hxu.
xreal_tac xu.
simpl.
destruct (is_negative_spec r).
exact I.
bound_tac.
apply sqrt_le_1.
exact H.
apply Rle_trans with (1 := H) (2 := Hxu).
exact Hxu.
(* xl positive *)
rewrite Hrl.
split.
simpl.
destruct (is_negative_spec rl).
exact I.
bound_tac.
apply sqrt_le_1.
exact (Rlt_le _ _ H0).
exact H.
exact Hxl.
unfold convert_bound in Hxu.
xreal_tac xu.
simpl.
destruct (is_negative_spec r).
exact I.
bound_tac.
apply sqrt_le_1.
exact H.
apply Rle_trans with (1 := H) (2 := Hxu).
exact Hxu.
Qed.

Lemma Xmin_swap_nan : forall x, Xmin x Xnan = Xnan.
intros x.
case x ; intros ; apply refl_equal.
Qed.

Lemma Xmax_swap_nan : forall x, Xmax x Xnan = Xnan.
intros x.
case x ; intros ; apply refl_equal.
Qed.

Ltac clear_complex_aux :=
  match goal with
  | H: Rle _ _ |- _ =>
    generalize H ; clear H ; try clear_complex_aux
  | H: (Rle _ _) /\ _ |- _ =>
    generalize (proj1 H) ;
    destruct H as (_, H) ;
    try clear_complex_aux
  | H: Rlt _ _ |- _ =>
    generalize H ; clear H ; try clear_complex_aux
  | H: (Rlt _ _) /\ _ |- _ =>
    generalize (proj1 H) ;
    destruct H as (_, H) ;
    try clear_complex_aux
  | H: ex (fun r : R => _ /\ _) |- _ =>
    let a := fresh "a" in
    let K := fresh in
    destruct H as (a, (K, H)) ;
    injection K ; clear K ; intro K ;
    rewrite <- K in H ;
    clear K a ; try clear_complex_aux
  | H: _ /\ _ |- _ =>
    destruct H as (_, H) ;
    try clear_complex_aux
  | H: _ |- _ =>
    clear H ; try clear_complex_aux
  end.

Ltac clear_complex :=
  clear_complex_aux ; clear ; intros.

Hint Local Resolve Rlt_le : mulauto.
Hint Local Resolve Rle_trans : mulauto.
Hint Local Resolve Rmult_le_compat_l : mulauto.
Hint Local Resolve Rmult_le_compat_r : mulauto.
Hint Local Resolve Rmult_le_compat_neg_l : mulauto.
Hint Local Resolve Rmult_le_compat_neg_r : mulauto.

Theorem mul_mixed_correct :
  forall prec yf,
  extension (fun x => Xmul x (FtoX (F.toF yf))) (fun xi => mul_mixed prec xi yf).
Proof.
intros prec yf [ | xl xu] [ | x] ; try easy.
intros (Hxl, Hxu).
simpl.
rewrite F.cmp_correct, Fcmp_correct, F.zero_correct.
xreal_tac2.
simpl.
case Rcompare_spec ; intros Hr ;
  try ( simpl ; unfold convert_bound ;
        rewrite 2!F.mul_correct, 2!Fmul_correct ;
        xreal_tac2 ;
        split ;
          ( xreal_tac2 ; simpl ; bound_tac ; eauto with mulauto ; fail ) ).
simpl.
unfold convert_bound.
rewrite F.zero_correct.
rewrite Hr, Rmult_0_r.
split ; simpl ; apply Rle_refl.
Qed.

Theorem mul_correct :
  forall prec,
  extension_2 Xmul (mul prec).
intros prec [ | xl xu] [ | yl yu] [ | x] [ | y] ;
  try ( intros ; exact I ) ;
  try ( intros H1 H2 ; try elim H1 ; elim H2 ; fail ).
intros (Hxl, Hxu) (Hyl, Hyu).
simpl.
unfold bnd, contains, convert, convert_bound.
(* case study on sign of xi *)
generalize (sign_large_correct_ xl xu x (conj Hxl Hxu)).
case (sign_large_ xl xu) ; intros Hx0 ; simpl in Hx0 ;
  (* case study on sign of yi *)
  try ( generalize (sign_large_correct_ yl yu y (conj Hyl Hyu)) ;
        case (sign_large_ yl yu) ; intros Hy0 ; simpl in Hy0 ) ;
  (* remove trivial comparisons with zero *)
  try ( rewrite F.zero_correct ; simpl ;
        try ( rewrite (proj1 Hx0) ; rewrite Rmult_0_l ) ;
        try ( rewrite (proj1 Hy0) ; rewrite Rmult_0_r ) ;
        split ; apply Rle_refl ) ;
  (* remove rounding operators *)
  try ( split ; rewrite F.mul_correct ; rewrite Fmul_correct ;
        do 2 xreal_tac2 ; unfold Xmul ; bound_tac ;
        clear_complex ) ;
  (* solve by transivity *)
  try ( eauto with mulauto ; fail ).
(* multiplication around zero *)
rewrite F.min_correct.
rewrite Fmin_correct.
rewrite F.max_correct.
rewrite Fmax_correct.
do 4 rewrite F.mul_correct.
do 4 rewrite Fmul_correct.
do 4 xreal_tac2 ;
  unfold Xmul ;
  try rewrite Xmin_swap_nan ;
  try rewrite Xmax_swap_nan ;
  try ( split ; simpl ; exact I ).
unfold xround.
simpl.
clear_complex.
destruct (Rle_or_lt x 0) as [Hx|Hx].
split ;
  [ apply <- Rmin_Rle | apply <- Rmax_Rle ] ;
  left ; bound_tac ;
  eauto with mulauto.
generalize (Rlt_le _ _ Hx).
clear Hx. intro Hx.
split ;
  [ apply <- Rmin_Rle | apply <- Rmax_Rle ] ;
  right ; bound_tac ;
  eauto with mulauto.
Qed.

Ltac simpl_is_zero :=
  let X := fresh "X" in
  match goal with
  | H: Rlt ?v R0 |- context [is_zero ?v] =>
    destruct (is_zero_spec v) as [X|X] ;
    [ rewrite X in H ; elim (Rlt_irrefl _ H) | idtac ]
  | H: Rlt R0 ?v |- context [is_zero ?v] =>
    destruct (is_zero_spec v) as [X|X] ;
    [ rewrite X in H ; elim (Rlt_irrefl _ H) | idtac ]
  | H: Rlt ?v R0 /\ _ |- context [is_zero ?v] =>
    destruct (is_zero_spec v) as [X|X] ;
    [ rewrite X in H ; elim (Rlt_irrefl _ (proj1 H)) | idtac ]
    (*rewrite (Rcompare_correct_lt _ _ (proj1 H))*)
  | H: _ /\ (Rlt ?v R0 /\ _) |- context [is_zero ?v] =>
    destruct (is_zero_spec v) as [X|X] ;
    [ rewrite X in H ; elim (Rlt_irrefl _ (proj1 (proj2 H))) | idtac ]
    (*rewrite (Rcompare_correct_lt _ _ (proj1 (proj2 H)))*)
  | H: Rlt R0 ?v /\ _ |- context [is_zero ?v] =>
    destruct (is_zero_spec v) as [X|X] ;
    [ rewrite X in H ; elim (Rlt_irrefl _ (proj1 H)) | idtac ]
    (*rewrite (Rcompare_correct_gt _ _ (proj1 H))*)
  | H: _ /\ (Rlt R0 ?v /\ _) |- context [is_zero ?v] =>
    destruct (is_zero_spec v) as [X|X] ;
    [ rewrite X in H ; elim (Rlt_irrefl _ (proj1 (proj2 H))) | idtac ]
    (*rewrite (Rcompare_correct_gt _ _ (proj1 (proj2 H)))*)
  end.

Hint Local Resolve Rinv_lt_0_compat : mulauto.
Hint Local Resolve Rinv_0_lt_compat : mulauto.
Hint Local Resolve Rle_Rinv_pos : mulauto.
Hint Local Resolve Rle_Rinv_neg : mulauto.

Hint Local Resolve Rlt_le : mulauto2.
Hint Local Resolve Rinv_lt_0_compat : mulauto2.
Hint Local Resolve Rinv_0_lt_compat : mulauto2.
Hint Local Resolve Rmult_le_pos_pos : mulauto2.
Hint Local Resolve Rmult_le_neg_pos : mulauto2.
Hint Local Resolve Rmult_le_pos_neg : mulauto2.
Hint Local Resolve Rmult_le_neg_neg : mulauto2.

Theorem div_mixed_r_correct :
  forall prec yf,
  extension (fun x => Xdiv x (FtoX (F.toF yf))) (fun xi => div_mixed_r prec xi yf).
Proof.
intros prec yf [ | xl xu] [x | ] ; try easy.
intros y (Hxl, Hxu).
simpl.
rewrite F.cmp_correct, Fcmp_correct, F.zero_correct.
xreal_tac2.
simpl.
case Rcompare_spec ; intros Hy ; try exact I ;
  simpl ; simpl_is_zero ;
  unfold convert_bound ;
  rewrite 2!F.div_correct, 2!Fdiv_correct ;
  xreal_tac2 ;
  split ;
    xreal_tac2 ;
    simpl ; simpl_is_zero; simpl ;
    bound_tac ;
    unfold Rdiv ; eauto with mulauto ; fail.
Qed.

Theorem div_correct :
  forall prec,
  extension_2 Xdiv (div prec).
intros prec [ | xl xu] [ | yl yu] [ | x] [ | y] ;
  try ( intros ; exact I ) ;
  try ( intros H1 H2 ; try elim H1 ; elim H2 ; fail ).
intros (Hxl, Hxu) (Hyl, Hyu).
simpl.
unfold bnd, contains, convert, convert_bound.
(* case study on sign of xi *)
generalize (sign_strict_correct_ xl xu x (conj Hxl Hxu)).
case (sign_strict_ xl xu) ; intros Hx0 ; simpl in Hx0 ;
  (* case study on sign of yi *)
  try ( generalize (sign_strict_correct_ yl yu y (conj Hyl Hyu)) ;
        case (sign_strict_ yl yu) ; intros Hy0 ; simpl in Hy0 ) ;
  try exact I ; try simpl_is_zero ; unfold Rdiv ;
  (* remove trivial comparisons with zero *)
  try ( rewrite F.zero_correct ; simpl ;
        rewrite (proj1 Hx0) ; rewrite Rmult_0_l ;
        split ; apply Rle_refl ) ;
  (* simplify Fdivz *)
  try ( unfold Fdivz ;
        rewrite real_correct ;
        try xreal_tac yl ; xreal_tac yu ) ;
  unfold convert_bound ;
  try rewrite F.zero_correct ;
  split ;
  (* remove rounding operators *)
  try ( rewrite F.div_correct ;
        rewrite Fdiv_correct ;
        do 2 xreal_tac2 ; unfold Xdiv, Rdiv ;
        match goal with |- context [is_zero ?v] => case (is_zero v) ; try exact I end ;
        bound_tac ) ;
  clear_complex ;
  (* solve by comparing to zero *)
  try ( simpl ; eauto with mulauto2 ; fail ) ;
  (* solve by transivity *)
  eauto 8 with mulauto.
Qed.

Theorem inv_correct :
  forall prec,
  extension Xinv (inv prec).
Proof.
intros prec [ | xl xu] [ | x] ;
  try ( intros ; exact I ) ;
  try ( intros H1 ; elim H1 ; fail ).
intros (Hxl, Hxu).
simpl.
unfold bnd, contains, convert, convert_bound.
generalize (sign_strict_correct_ xl xu x (conj Hxl Hxu)).
(* case study on sign of xi *)
case (sign_strict_ xl xu) ; intros Hx0 ; simpl in Hx0 ;
  (* case study on sign of yi *)
  try exact I ; try simpl_is_zero ;
  (* simplify Fdivz *)
  unfold Fdivz ; rewrite 2!real_correct ;
  destruct Hx0 as (Hx0, (Hx1, (r, (Hx2, Hx3)))) ;
  rewrite Hx2 in * ;
  split ;
  [ idtac | xreal_tac xl | xreal_tac xu | idtac ] ;
  try ( unfold convert_bound ; rewrite F.zero_correct ;
        simpl ; auto with mulauto ; fail ) ;
  (* remove rounding operators *)
  unfold convert_bound ;
  rewrite F.div_correct, Fdiv_correct, F.fromZ_correct ;
  try ( unfold convert_bound in X0 ; rewrite X0 ) ;
  try ( unfold convert_bound in Hx2 ; rewrite Hx2 ) ;
  unfold Xdiv, Rdiv ;
  match goal with |- context [is_zero ?v] => case (is_zero v) ; try exact I end ;
  bound_tac ; rewrite Rmult_1_l ; auto with mulauto.
Qed.

Theorem sqr_correct :
  forall prec,
  extension Xsqr (sqr prec).
Proof.
intros prec [ | xl xu] [ | x] ;
  try ( intros ; exact I ) ;
  try ( intros H1 ; elim H1 ; fail ).
intros (Hxl, Hxu).
simpl.
unfold bnd, contains, convert, convert_bound.
(* case study on sign of xi *)
generalize (sign_large_correct_ xl xu x (conj Hxl Hxu)).
case (sign_large_ xl xu) ; intros Hx0 ; simpl in Hx0 ;
  (* remove trivial comparisons with zero *)
  try ( rewrite F.zero_correct ; simpl ;
        try ( rewrite (proj1 Hx0) ; rewrite Rmult_0_l ) ;
        split ; apply Rle_refl ) ;
  (* remove rounding operators *)
  try ( split ; rewrite F.mul_correct ; rewrite Fmul_correct  ;
        xreal_tac2 ; unfold Xmul ; bound_tac ;
        clear_complex ) ;
  (* solve by transivity *)
  try ( eauto with mulauto ; fail ).
(* multiplication around zero *)
split.
rewrite F.zero_correct ; simpl.
apply Rle_0_sqr.
rewrite F.mul_correct, Fmul_correct.
rewrite F.max_correct, Fmax_correct.
rewrite F.abs_correct, Fabs_correct.
do 2 xreal_tac2.
simpl.
bound_tac.
clear_complex.
apply Rsqr_le_abs_1.
rewrite Rabs_left1 with (1 := H).
unfold Rmax.
case Rle_dec ; intros H0.
rewrite Rabs_pos_eq with (1 := Hx0).
apply Rabs_le.
refine (conj _ Hxu).
apply Rle_trans with (2 := Hxl).
rewrite <- (Ropp_involutive r).
now apply Ropp_le_contravar.
rewrite Rabs_Ropp, Rabs_left1 with (1 := H).
apply Rabs_le.
rewrite Ropp_involutive.
refine (conj Hxl _).
apply Rle_trans with (1 := Hxu).
apply Rlt_le.
now apply Rnot_le_lt.
Qed.

Theorem sqr_ge_0 :
  forall prec xi, convert xi <> Interval_interval.Inan ->
  le_lower' (Xreal 0) (FtoX (F.toF (lower (sqr prec xi)))).
Proof.
intros prec [|xl xu].
intros H.
now elim H.
intros _.
simpl.
unfold sign_large_.
rewrite 2!F.cmp_correct, 2!Fcmp_correct, F.zero_correct.
assert (Hd: forall x xr, FtoX (F.toF x) = Xreal xr ->
    match FtoX (F.toF (F.mul rnd_DN prec x x)) with
    | Xnan => False
    | Xreal yr => (0 <= yr)%R
    end).
  intros x xr Hx.
  rewrite F.mul_correct, Fmul_correct.
  rewrite Hx.
  simpl.
  apply Fcore_generic_fmt.round_ge_generic ; auto with typeclass_instances.
  apply Fcore_generic_fmt.generic_format_0.
  apply Rle_0_sqr.
assert (Hz: match FtoX (F.toF F.zero) with
    | Xnan => False
    | Xreal yr => (0 <= yr)%R
    end).
  rewrite F.zero_correct.
  apply Rle_refl.
case_eq (FtoX (F.toF xl)) ; case_eq (FtoX (F.toF xu)) ; simpl.
now intros _ _.
intros ru Hu _.
case Rcompare_spec ; simpl ; intros H ; try apply Hz ; apply Hd with (1 := Hu).
intros _ rl Hl.
case Rcompare_spec ; simpl ; intros H ; try apply Hz ; apply Hd with (1 := Hl).
intros ru Hu rl Hl.
case Rcompare_spec ; simpl ; intros H1 ;
  case Rcompare_spec ; simpl ; intros H2 ;
    try apply Hz ; eapply Hd ; eassumption.
Qed.

Theorem sqr_ge_0' :
  forall prec xi, (0 <= proj_val (FtoX (F.toF (lower (sqr prec xi)))))%R.
Proof.
intros prec [|xl xu].
simpl.
rewrite F.nan_correct.
apply Rle_refl.
refine (_ (sqr_ge_0 prec (Ibnd xl xu) _)).
2: discriminate.
simpl.
now case FtoX.
Qed.

Lemma Fpower_pos_up_correct :
  forall prec x n,
  le_upper (Xreal 0) (FtoX (F.toF x)) ->
  le_upper (Xpower_int (FtoX (F.toF x)) (Zpos n)) (FtoX (F.toF (Fpower_pos rnd_UP prec x n))).
Proof.
intros prec x n.
revert x.
unfold le_upper, Xpower_int.
induction n ; intros x Hx ; simpl.
(* *)
generalize (IHn (F.mul rnd_UP prec x x)).
rewrite 2!F.mul_correct, 2!Fmul_correct.
xreal_tac x ; simpl.
easy.
xreal_tac (Fpower_pos rnd_UP prec (F.mul rnd_UP prec x x) n) ; simpl.
easy.
intros H.
bound_tac.
apply Rmult_le_compat_l with (1 := Hx).
refine (Rle_trans _ _ _ _ (H _)).
change (Pmult_nat n 2) with (nat_of_P (xO n)).
rewrite nat_of_P_xO, pow_sqr.
apply pow_incr.
split.
now apply Rmult_le_pos.
bound_tac.
apply Rle_refl.
bound_tac.
now apply Rmult_le_pos.
(* *)
generalize (IHn (F.mul rnd_UP prec x x)).
rewrite F.mul_correct, Fmul_correct.
xreal_tac x ; simpl.
intros H.
now apply H.
xreal_tac (Fpower_pos rnd_UP prec (F.mul rnd_UP prec x x) n) ; simpl.
easy.
intros H.
refine (Rle_trans _ _ _ _ (H _)).
rewrite nat_of_P_xO, pow_sqr.
apply pow_incr.
split.
now apply Rmult_le_pos.
bound_tac.
apply Rle_refl.
bound_tac.
now apply Rmult_le_pos.
(* *)
xreal_tac x.
rewrite Rmult_1_r.
apply Rle_refl.
Qed.

Lemma Fpower_pos_dn_correct :
  forall prec x n,
  le_lower' (Xreal 0) (FtoX (F.toF x)) ->
  le_lower' (FtoX (F.toF (Fpower_pos rnd_DN prec x n))) (Xpower_int (FtoX (F.toF x)) (Zpos n)).
Proof.
intros prec x n.
revert x.
unfold le_lower', Xpower_int.
induction n ; intros x Hx ; simpl.
(* *)
generalize (IHn (F.mul rnd_DN prec x x)).
rewrite 2!F.mul_correct, 2!Fmul_correct.
xreal_tac x ; simpl.
easy.
xreal_tac (Fpower_pos rnd_DN prec (F.mul rnd_DN prec x x) n) ; simpl.
easy.
intros H.
bound_tac.
apply Rmult_le_compat_l with (1 := Hx).
refine (Rle_trans _ _ _ (H _) _).
apply (Fcore_generic_fmt.round_ge_generic _ _ _).
apply Fcore_generic_fmt.generic_format_0.
now apply Rmult_le_pos.
change (Pmult_nat n 2) with (nat_of_P (xO n)).
rewrite nat_of_P_xO, pow_sqr.
apply pow_incr.
split.
apply (Fcore_generic_fmt.round_ge_generic _ _ _).
apply Fcore_generic_fmt.generic_format_0.
now apply Rmult_le_pos.
bound_tac.
apply Rle_refl.
(* *)
generalize (IHn (F.mul rnd_DN prec x x)).
rewrite F.mul_correct, Fmul_correct.
xreal_tac x ; simpl.
now rewrite X in Hx.
xreal_tac (Fpower_pos rnd_DN prec (F.mul rnd_DN prec x x) n) ; simpl.
easy.
intros H.
refine (Rle_trans _ _ _ (H _) _).
apply (Fcore_generic_fmt.round_ge_generic _ _ _).
apply Fcore_generic_fmt.generic_format_0.
now apply Rmult_le_pos.
rewrite nat_of_P_xO, pow_sqr.
apply pow_incr.
split.
apply (Fcore_generic_fmt.round_ge_generic _ _ _).
apply Fcore_generic_fmt.generic_format_0.
now apply Rmult_le_pos.
bound_tac.
apply Rle_refl.
(* *)
xreal_tac x.
rewrite Rmult_1_r.
apply Rle_refl.
Qed.

Theorem power_pos_correct :
  forall prec n,
  extension (fun x => Xpower_int x (Zpos n)) (fun x => power_pos prec x n).
Proof.
intros prec n [ | xl xu] [ | x] ; try easy.
unfold contains, convert, convert_bound, power_pos, Xpower_int.
intros (Hxl,Hxu).
generalize (sign_large_correct_ xl xu x (conj Hxl Hxu)).
case (sign_large_ xl xu) ; intros Hx0 ; simpl in Hx0.
(* *)
rewrite F.zero_correct.
simpl.
rewrite (proj1 Hx0), pow_i.
split ; apply Rle_refl.
apply lt_O_nat_of_P.
(* *)
destruct n as [n|n|].
(* . *)
rewrite 2!F.neg_correct, 2!Fneg_correct.
split.
(* .. *)
generalize (Fpower_pos_up_correct prec (F.abs xl) (xI n)).
unfold le_upper.
rewrite F.abs_correct, Fabs_correct.
xreal_tac (Fpower_pos rnd_UP prec (F.abs xl) n~1).
easy.
xreal_tac xl ; simpl.
intros H.
now elim H.
intros H.
specialize (H (Rabs_pos _)).
apply Ropp_le_contravar in H.
apply Rle_trans with (1 := H).
rewrite Rabs_left1.
2: apply Hx0.
rewrite Ropp_mult_distr_l_reverse, Ropp_involutive.
change (Pmult_nat n 2) with (nat_of_P (xO n)).
rewrite nat_of_P_xO at 2.
rewrite pow_sqr.
rewrite <- (Rmult_opp_opp x x).
rewrite <- pow_sqr, <- nat_of_P_xO.
apply Rle_trans with (r0 * (-x) ^ nat_of_P (xO n))%R.
apply Rmult_le_compat_neg_l.
apply Hx0.
apply pow_incr.
split.
rewrite <- Ropp_0.
now apply Ropp_le_contravar.
now apply Ropp_le_contravar.
apply Rmult_le_compat_r.
apply pow_le.
rewrite <- Ropp_0.
now apply Ropp_le_contravar.
exact Hxl.
(* .. *)
generalize (Fpower_pos_dn_correct prec (F.abs xu) (xI n)).
unfold le_lower'.
rewrite F.abs_correct, Fabs_correct.
xreal_tac (Fpower_pos rnd_DN prec (F.abs xu) n~1).
easy.
xreal_tac xu ; simpl.
destruct Hx0 as (_,(_,(ru,(H,_)))).
now rewrite H in X0.
intros H.
specialize (H (Rabs_pos _)).
apply Ropp_le_contravar in H.
apply Rle_trans with (2 := H).
assert (Hr0 : (r0 <= 0)%R).
destruct Hx0 as (_,(_,(ru,(H1,H2)))).
now inversion H1.
rewrite Rabs_left1 with (1 := Hr0).
rewrite Ropp_mult_distr_l_reverse, Ropp_involutive.
change (Pmult_nat n 2) with (nat_of_P (xO n)).
rewrite nat_of_P_xO at 1.
rewrite pow_sqr.
rewrite <- (Rmult_opp_opp x x).
rewrite <- pow_sqr, <- nat_of_P_xO.
apply Rle_trans with (x * (-r0) ^ nat_of_P (xO n))%R.
apply Rmult_le_compat_neg_l.
apply Hx0.
apply pow_incr.
split.
rewrite <- Ropp_0.
now apply Ropp_le_contravar.
now apply Ropp_le_contravar.
apply Rmult_le_compat_r.
apply pow_le.
rewrite <- Ropp_0.
now apply Ropp_le_contravar.
exact Hxu.
(* . *)
split.
(* .. *)
generalize (Fpower_pos_dn_correct prec (F.abs xu) (xO n)).
unfold le_lower'.
rewrite F.abs_correct, Fabs_correct.
xreal_tac (Fpower_pos rnd_DN prec (F.abs xu) n~0).
easy.
xreal_tac xu ; simpl.
intros _.
destruct Hx0 as (_,(_,(ru,(H,_)))).
now rewrite H in X0.
intros H.
specialize (H (Rabs_pos _)).
apply Rle_trans with (1 := H).
assert (Hr0 : (r0 <= 0)%R).
destruct Hx0 as (_,(_,(ru,(H1,H2)))).
now inversion H1.
rewrite Rabs_left1 with (1 := Hr0).
change (Pmult_nat n 2) with (nat_of_P (xO n)).
rewrite nat_of_P_xO at 2.
rewrite pow_sqr.
rewrite <- (Rmult_opp_opp x x).
rewrite <- pow_sqr, <- nat_of_P_xO.
apply pow_incr.
split.
rewrite <- Ropp_0.
now apply Ropp_le_contravar.
now apply Ropp_le_contravar.
(* .. *)
generalize (Fpower_pos_up_correct prec (F.abs xl) (xO n)).
unfold le_upper.
rewrite F.abs_correct, Fabs_correct.
xreal_tac (Fpower_pos rnd_UP prec (F.abs xl) n~0).
easy.
xreal_tac xl ; simpl.
intros H.
now elim H.
intros H.
specialize (H (Rabs_pos _)).
apply Rle_trans with (2 := H).
rewrite Rabs_left1.
2: apply Hx0.
change (Pmult_nat n 2) with (nat_of_P (xO n)).
rewrite nat_of_P_xO at 1.
rewrite pow_sqr.
rewrite <- (Rmult_opp_opp x x).
rewrite <- pow_sqr, <- nat_of_P_xO.
apply pow_incr.
split.
rewrite <- Ropp_0.
now apply Ropp_le_contravar.
now apply Ropp_le_contravar.
(* . *)
simpl.
split.
xreal_tac xl.
now rewrite Rmult_1_r.
xreal_tac xu.
now rewrite Rmult_1_r.
(* *)
split.
(* . *)
generalize (Fpower_pos_dn_correct prec xl n).
unfold le_lower'.
xreal_tac (Fpower_pos rnd_DN prec xl n).
easy.
xreal_tac xl.
intros _.
destruct Hx0 as (_,(_,(rl,(H1,_)))).
now rewrite H1 in X0.
intros H.
assert (Hr0: (0 <= r0)%R).
destruct Hx0 as (_,(_,(rl,(H1,H2)))).
now inversion H1.
specialize (H Hr0).
apply Rle_trans with (1 := H).
apply pow_incr.
now split.
(* . *)
generalize (Fpower_pos_up_correct prec xu n).
unfold le_upper.
xreal_tac (Fpower_pos rnd_UP prec xu n).
easy.
xreal_tac xu.
intros H.
now elim H.
intros H.
refine (Rle_trans _ _ _ _ (H _)).
2: apply Hx0.
apply pow_incr.
now split.
(* *)
destruct n as [n|n|].
(* . *)
split.
(* .. *)
rewrite F.neg_correct, Fneg_correct.
generalize (Fpower_pos_up_correct prec (F.abs xl) (xI n)).
unfold le_upper.
rewrite F.abs_correct, Fabs_correct.
xreal_tac (Fpower_pos rnd_UP prec (F.abs xl) n~1).
easy.
xreal_tac xl ; simpl.
intros H.
now elim H.
intros H.
specialize (H (Rabs_pos _)).
apply Ropp_le_contravar in H.
apply Rle_trans with (1 := H).
rewrite Rabs_left1.
2: apply Hx0.
rewrite Ropp_mult_distr_l_reverse, Ropp_involutive.
destruct (Rle_or_lt x 0) as [Hx|Hx].
change (Pmult_nat n 2) with (nat_of_P (xO n)).
rewrite nat_of_P_xO at 2.
rewrite pow_sqr.
rewrite <- (Rmult_opp_opp x x).
rewrite <- pow_sqr, <- nat_of_P_xO.
apply Rle_trans with (r0 * (-x) ^ nat_of_P (xO n))%R.
apply Rmult_le_compat_neg_l.
apply Hx0.
apply pow_incr.
split.
rewrite <- Ropp_0.
now apply Ropp_le_contravar.
now apply Ropp_le_contravar.
apply Rmult_le_compat_r.
apply pow_le.
rewrite <- Ropp_0.
now apply Ropp_le_contravar.
exact Hxl.
apply Rlt_le in Hx.
apply Rle_trans with R0.
apply Ropp_le_cancel.
rewrite Ropp_0, <- Ropp_mult_distr_l_reverse.
apply Rmult_le_pos.
rewrite <- Ropp_0.
now apply Ropp_le_contravar.
apply pow_le.
rewrite <- Ropp_0.
now apply Ropp_le_contravar.
apply Rmult_le_pos with (1 := Hx).
now apply pow_le.
(* .. *)
generalize (Fpower_pos_up_correct prec xu (xI n)).
unfold le_upper.
xreal_tac (Fpower_pos rnd_UP prec xu n~1).
easy.
xreal_tac xu ; simpl.
intros H.
now elim H.
intros H.
refine (Rle_trans _ _ _ _ (H _)).
2: apply Hx0.
destruct (Rle_or_lt x 0) as [Hx|Hx].
apply Rle_trans with R0.
apply Ropp_le_cancel.
rewrite Ropp_0, <- Ropp_mult_distr_l_reverse.
change (Pmult_nat n 2) with (nat_of_P (xO n)).
rewrite nat_of_P_xO.
rewrite pow_sqr.
rewrite <- (Rmult_opp_opp x x).
rewrite <- pow_sqr, <- nat_of_P_xO.
apply Rmult_le_pos.
rewrite <- Ropp_0.
now apply Ropp_le_contravar.
apply pow_le.
rewrite <- Ropp_0.
now apply Ropp_le_contravar.
apply Rmult_le_pos.
apply Hx0.
now apply pow_le.
apply Rlt_le in Hx.
apply Rmult_le_compat with (1 := Hx).
now apply pow_le.
exact Hxu.
apply pow_incr.
now split.
(* . *)
split.
(* .. *)
rewrite F.zero_correct.
rewrite nat_of_P_xO.
rewrite pow_sqr.
change (x * x)%R with (Rsqr x).
simpl.
apply pow_le.
apply Rle_0_sqr.
(* .. *)
generalize (Fpower_pos_up_correct prec (F.max (F.abs xl) xu) (xO n)).
unfold le_upper.
rewrite F.max_correct, Fmax_correct, F.abs_correct, Fabs_correct.
xreal_tac (Fpower_pos rnd_UP prec (F.max (F.abs xl) xu) n~0).
easy.
xreal_tac xl ; simpl.
intros H.
now elim H.
xreal_tac xu ; simpl.
intros H.
now elim H.
intros H.
assert (Hr: (0 <= Rmax (Rabs r0) r1)%R).
apply Rmax_case.
apply Rabs_pos.
apply Hx0.
apply Rle_trans with (2 := H Hr).
destruct (Rle_or_lt x 0) as [Hx|Hx].
change (Pmult_nat n 2) with (nat_of_P (xO n)).
rewrite nat_of_P_xO at 1.
rewrite pow_sqr.
rewrite <- (Rmult_opp_opp x x).
rewrite <- pow_sqr, <- nat_of_P_xO.
apply pow_incr.
split.
rewrite <- Ropp_0.
now apply Ropp_le_contravar.
apply Rle_trans with (2 := Rmax_l _ _).
rewrite Rabs_left1.
now apply Ropp_le_contravar.
apply Hx0.
apply pow_incr.
split.
now apply Rlt_le.
now apply Rle_trans with (2 := Rmax_r _ _).
(* . *)
simpl.
split.
xreal_tac xl.
now rewrite Rmult_1_r.
xreal_tac xu.
now rewrite Rmult_1_r.
Qed.

Theorem power_int_correct :
  forall prec n,
  extension (fun x => Xpower_int x n) (fun x => power_int prec x n).
Proof.
intros prec [|n|n].
unfold power_int, Xpower_int.
intros [ | xl xu] [ | x] ; try easy.
intros _.
simpl.
unfold convert_bound.
rewrite F.fromZ_correct.
split ; apply Rle_refl.
apply power_pos_correct.
intros xi x Hx.
generalize (power_pos_correct prec n _ _ Hx).
intros Hp.
generalize (inv_correct prec _ _ Hp).
unfold Xpower_int, Xinv, power_int.
destruct x as [ | x].
easy.
replace (is_zero x) with (is_zero (x ^ nat_of_P n)).
easy.
case (is_zero_spec x) ; intros Zx.
rewrite Zx, pow_i.
apply is_zero_correct_zero.
apply lt_O_nat_of_P.
case is_zero_spec ; try easy.
intros H.
elim (pow_nonzero _ _ Zx H).
Qed.

End FloatInterval.
