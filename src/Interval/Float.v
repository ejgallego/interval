(**
This file is part of the Coq.Interval library for proving bounds of
real-valued expressions in Coq: http://coq-interval.gforge.inria.fr/

Copyright (C) 2007-2016, Inria

This library is governed by the CeCILL-C license under French law and
abiding by the rules of distribution of free software. You can use,
modify and/or redistribute the library under the terms of the CeCILL-C
license as circulated by CEA, CNRS and Inria at the following URL:
http://www.cecill.info/

As a counterpart to the access to the source code and rights to copy,
modify and redistribute granted by the license, users are provided
only with a limited warranty and the library's author, the holder of
the economic rights, and the successive licensors have only limited
liability. See the COPYING file for more details.
*)

From Coq Require Import Bool Reals Psatz.
From Flocq Require Import Raux.

Require Import Stdlib.
Require Import Xreal.
Require Import Basic.
Require Import Sig.
Require Import Interval.

Inductive f_interval (A : Type) : Type :=
  | Inan : f_interval A
  | Ibnd (l u : A) : f_interval A.

Arguments Inan {A}.
Arguments Ibnd {A} _ _.

Definition le_lower' x y :=
  match x with
  | Xnan => True
  | Xreal xr =>
    match y with
    | Xnan => False
    | Xreal yr => Rle xr yr
    end
  end.

Module FloatInterval (F : FloatOps with Definition sensible_format := true).

Module F' := FloatExt F.

Definition c1 := F.fromZ 1.
Definition cm1 := F.fromZ (-1).
Definition c2 := F.fromZ 2.
Definition p52 := F.PtoP 52.

Definition type := f_interval F.type.
Definition bound_type := F.type.
Definition precision := F.precision.

Definition convert_bound := F.toX.
Definition convert (xi : type) :=
  match xi with
  | Inan => Interval.Inan
  | Ibnd l u => Interval.Ibnd (F.toX l) (F.toX u)
  end.

Definition nai : type := @Inan F.type.
Definition bnd l u : type := Ibnd l u.
Definition zero : type := Ibnd F.zero F.zero.
Definition empty : type := Ibnd c1 F.zero.
Definition real (xi : type) :=
  match xi with
  | Inan => false
  | Ibnd _ _ => true
  end.

Lemma bnd_correct :
  forall l u,
  convert (bnd l u) = Interval.Ibnd (F.toX l) (F.toX u).
Proof.
split.
Qed.

Lemma nai_correct :
  convert nai = Interval.Inan.
Proof.
split.
Qed.

Lemma zero_correct :
  convert zero = Interval.Ibnd (Xreal 0) (Xreal 0).
Proof.
simpl.
now rewrite F.zero_correct.
Qed.

Lemma empty_correct :
  forall x, contains (convert empty) x -> False.
Proof.
intros [|x].
easy.
simpl.
unfold c1.
rewrite F.fromZ_correct, F.zero_correct by easy.
lra.
Qed.

Lemma real_correct :
  forall xi, real xi = match convert xi with Interval.Inan => false | _ => true end.
Proof.
now intros [|xl xu].
Qed.

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
    match F'.cmp xl yl with
    | Xund => negb (F.real yl)
    | Xlt => false
    | _ => true
    end &&
    match F'.cmp xu yu with
    | Xund => negb (F.real yu)
    | Xgt => false
    | _ => true
    end
  | _, Inan => true
  | _, _ => false
  end.

Definition wider prec xi yi :=
  match yi, xi with
  | Inan, _ => false
  | Ibnd yl yu, Inan => true
  | Ibnd yl yu, Ibnd xl xu =>
    let yw := F.sub_UP prec yu yl in
    if F.real yw then
      match F'.cmp (F.sub_UP prec xu xl) yw with
      | Xlt | Xeq => false
      | _ => true
      end
    else false
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
  | Inan, _ => yi
  | _, Inan => xi
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

Definition lower_complement xi :=
  match xi with
  | Ibnd xl _ => if F.real xl then Ibnd F.nan xl else empty
  | Inan => empty
  end.

Definition upper_complement xi :=
  match xi with
  | Ibnd _ xu => if F.real xu then Ibnd xu F.nan else empty
  | Inan => empty
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

Definition fromZ_small n :=
  let f := F.fromZ n in Ibnd f f.

Definition fromZ prec n :=
  Ibnd (F.fromZ_DN prec n) (F.fromZ_UP prec n).

Definition midpoint xi :=
  match xi with
  | Inan => F.zero
  | Ibnd xl xu =>
    match F'.cmp xl F.zero, F'.cmp xu F.zero with
    | Xund, Xund => F.zero
    | Xeq, Xeq => F.zero
    | Xlt, Xund => F.zero
    | Xund, Xgt => F.zero
    | Xeq, Xund => c1
    | Xund, Xeq => cm1
    | Xgt, Xund => F.mul_UP p52 xl c2
    | Xund, Xlt => F.mul_DN p52 xu c2
    | _, _ => F.midpoint xl xu
    end
  end.

Definition midpoint' xi :=
  match xi with
  | Inan => zero
  | Ibnd xl xu =>
    match F'.cmp xl F.zero, F'.cmp xu F.zero with
    | Xund, Xund => zero
    | Xeq, Xeq => zero
    | Xlt, Xund => zero
    | Xund, Xgt => zero
    | Xeq, Xund => Ibnd c1 c1
    | Xund, Xeq => Ibnd cm1 cm1
    | Xgt, Xund => let m := F.mul_UP p52 xl c2 in Ibnd m m
    | Xund, Xlt => let m := F.mul_DN p52 xu c2 in Ibnd m m
    | _, _ =>
      if F'.lt xu xl then empty
      else let m := F.midpoint xl xu in Ibnd m m
    end
  end.

Definition bisect xi :=
  match xi with
  | Inan => (Inan, Inan)
  | Ibnd xl xu =>
    let m :=
      match F'.cmp xl F.zero, F'.cmp xu F.zero with
      | Xund, Xund => F.zero
      | Xeq, Xeq => F.zero
      | Xlt, Xund => F.zero
      | Xund, Xgt => F.zero
      | Xeq, Xund => c1
      | Xund, Xeq => cm1
      | Xgt, Xund => F.mul_UP p52 xl c2
      | Xund, Xlt => F.mul_DN p52 xu c2
      | _, _ => F.midpoint xl xu
      end in
    (Ibnd xl m, Ibnd m xu)
  end.

Definition extension f fi := forall b x,
  contains (convert b) x -> contains (convert (fi b)) (f x).

Definition extension_2 f fi := forall ix iy x y,
  contains (convert ix) x ->
  contains (convert iy) y ->
  contains (convert (fi ix iy)) (f x y).

Definition sign_large_ xl xu :=
  match F'.cmp xl F.zero, F'.cmp xu F.zero with
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
  match F'.cmp xl F.zero, F'.cmp xu F.zero with
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

Definition mul2 prec xi :=
  match xi with
  | Ibnd xl xu =>
    Ibnd (F.mul_DN prec xl c2) (F.mul_UP prec xu c2)
  | Inan => Inan
  end.

Definition sqrt prec xi :=
  match xi with
  | Ibnd xl xu =>
    match F'.cmp xl F.zero with
    | Xeq => Ibnd F.zero (F.sqrt_UP prec xu)
    | Xgt => Ibnd (F.sqrt_DN prec xl) (F.sqrt_UP prec xu)
    | _ => Inan
    end
  | Inan => Inan
  end.

Definition add prec xi yi :=
  match xi, yi with
  | Ibnd xl xu, Ibnd yl yu =>
    Ibnd (F.add_DN prec xl yl) (F.add_UP prec xu yu)
  | _, _ => Inan
  end.

Definition sub prec xi yi :=
  match xi, yi with
  | Ibnd xl xu, Ibnd yl yu =>
    Ibnd (F.sub_DN prec xl yu) (F.sub_UP prec xu yl)
  | _, _ => Inan
  end.

Definition cancel_add prec xi yi :=
  match xi, yi with
  | Ibnd xl xu, Ibnd yl yu =>
    Ibnd (F.sub_DN prec xl yl) (F.sub_UP prec xu yu)
  | _, _ => Inan
  end.

Definition cancel_sub prec xi yi :=
  match xi, yi with
  | Ibnd xl xu, Ibnd yl yu =>
    Ibnd (F.add_DN prec xl yu) (F.add_UP prec xu yl)
  | _, _ => Inan
  end.

Definition mul_mixed prec xi y :=
  match xi with
  | Ibnd xl xu =>
    match F'.cmp y F.zero with
    | Xlt => Ibnd (F.mul_DN prec xu y) (F.mul_UP prec xl y)
    | Xeq => Ibnd F.zero F.zero
    | Xgt => Ibnd (F.mul_DN prec xl y) (F.mul_UP prec xu y)
    | Xund => Inan
    end
  | Inan => Inan
  end.

Definition div_mixed_r prec xi y :=
  match xi with
  | Ibnd xl xu =>
    match F'.cmp y F.zero with
    | Xlt => Ibnd (F.div_DN prec xu y) (F.div_UP prec xl y)
    | Xgt => Ibnd (F.div_DN prec xl y) (F.div_UP prec xu y)
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
      Ibnd F.zero (F.mul_UP prec xm xm)
    | Xeq => Ibnd F.zero F.zero
    | Xlt =>
      let lb := F.mul_DN prec xu xu in
      match F'.cmp lb F.zero with
      | Xgt => Ibnd lb (F.mul_UP prec xl xl)
      | _ => Ibnd F.zero (F.mul_UP prec xl xl)
      end
    | Xgt =>
      let lb := F.mul_DN prec xl xl in
      match F'.cmp lb F.zero with
      | Xgt => Ibnd lb (F.mul_UP prec xu xu)
      | _ => Ibnd F.zero (F.mul_UP prec xu xu)
      end
    end
  | _ => Inan
  end.

Definition mul prec xi yi :=
  match xi, yi with
  | Ibnd xl xu, Ibnd yl yu =>
    match sign_large_ xl xu, sign_large_ yl yu with
    | Xeq, _ => Ibnd F.zero F.zero
    | _, Xeq => Ibnd F.zero F.zero
    | Xgt, Xgt => Ibnd (F.mul_DN prec xl yl) (F.mul_UP prec xu yu)
    | Xlt, Xlt => Ibnd (F.mul_DN prec xu yu) (F.mul_UP prec xl yl)
    | Xgt, Xlt => Ibnd (F.mul_DN prec xu yl) (F.mul_UP prec xl yu)
    | Xlt, Xgt => Ibnd (F.mul_DN prec xl yu) (F.mul_UP prec xu yl)
    | Xgt, Xund => Ibnd (F.mul_DN prec xu yl) (F.mul_UP prec xu yu)
    | Xlt, Xund => Ibnd (F.mul_DN prec xl yu) (F.mul_UP prec xl yl)
    | Xund, Xgt => Ibnd (F.mul_DN prec xl yu) (F.mul_UP prec xu yu)
    | Xund, Xlt => Ibnd (F.mul_DN prec xu yl) (F.mul_UP prec xl yl)
    | Xund, Xund => Ibnd (F.min (F.mul_DN prec xl yu) (F.mul_DN prec xu yl))
                         (F.max (F.mul_UP prec xl yl) (F.mul_UP prec xu yu))
    end
  | _, _ => Inan
  end.

Definition Fdivz_UP prec x y :=
  if F.real y then F.div_UP prec x y else F.zero.

Definition Fdivz_DN prec x y :=
  if F.real y then F.div_DN prec x y else F.zero.

Definition inv prec xi :=
  match xi with
  | Ibnd xl xu =>
    match sign_strict_ xl xu with
    | Xund => Inan
    | Xeq => Inan
    | _ =>
      Ibnd (Fdivz_DN prec c1 xu) (Fdivz_UP prec c1 xl)
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
    | Xgt, Xgt => Ibnd (Fdivz_DN prec xl yu) (F.div_UP prec xu yl)
    | Xlt, Xlt => Ibnd (Fdivz_DN prec xu yl) (F.div_UP prec xl yu)
    | Xgt, Xlt => Ibnd (F.div_DN prec xu yu) (Fdivz_UP prec xl yl)
    | Xlt, Xgt => Ibnd (F.div_DN prec xl yl) (Fdivz_UP prec xu yu)
    | Xund, Xgt => Ibnd (F.div_DN prec xl yl) (F.div_UP prec xu yl)
    | Xund, Xlt => Ibnd (F.div_DN prec xu yu) (F.div_UP prec xl yu)
    end
  | _, _ => Inan
  end.

Fixpoint Fpower_pos_UP prec x n :=
  match n with
  | xH => x
  | xO p => Fpower_pos_UP prec (F.mul_UP prec x x) p
  | xI p => F.mul_UP prec x (Fpower_pos_UP prec (F.mul_UP prec x x) p)
  end.

Fixpoint Fpower_pos_DN prec x n :=
  match n with
  | xH => x
  | xO p =>
    let xx := F.mul_DN prec x x in
    match F'.cmp xx F.zero with
    | Xgt => Fpower_pos_DN prec (F.mul_DN prec x x) p
    | Xeq | Xlt => F.zero
    | Xund => F.nan
    end
  | xI p =>
    let xx := F.mul_DN prec x x in
    match F'.cmp xx F.zero with
    | Xgt => F.mul_DN prec x (Fpower_pos_DN prec (F.mul_DN prec x x) p)
    | Xeq | Xlt => F.zero
    | Xund => F.nan
    end
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
        Ibnd F.zero (Fpower_pos_UP prec xm n)
      | xI _ => Ibnd (F.neg (Fpower_pos_UP prec (F.abs xl) n)) (Fpower_pos_UP prec xu n)
      end
    | Xeq => Ibnd F.zero F.zero
    | Xlt =>
      match n with
      | xH => xi
      | xO _ => Ibnd (Fpower_pos_DN prec (F.abs xu) n) (Fpower_pos_UP prec (F.abs xl) n)
      | xI _ => Ibnd (F.neg (Fpower_pos_UP prec (F.abs xl) n)) (F.neg (Fpower_pos_DN prec (F.abs xu) n))
      end
    | Xgt => Ibnd (Fpower_pos_DN prec xl n) (Fpower_pos_UP prec xu n)
    end
  | _ => Inan
  end.

Definition power_int prec xi n :=
  match n with
  | Zpos p => power_pos prec xi p
  | Z0 => match xi with Inan => Inan | _ => Ibnd c1 c1 end
  | Zneg p => inv prec (power_pos prec xi p)
  end.

Definition nearbyint mode xi :=
  match xi with
  | Inan => Inan
  | Ibnd xl xu => Ibnd (F.nearbyint mode xl) (F.nearbyint mode xu)
  end.

Ltac xreal_tac v :=
  let X := fresh "X" in
  case_eq (F.toX v) ;
  [ intros X ; try exact I
  | let r := fresh "r" in
    intros r X ; try rewrite X in * ].

Ltac xreal_tac2 :=
  match goal with
  | H: F.toX ?v = Xreal _ |- context [F.toX ?v] =>
    rewrite H
  | |- context [F.toX ?v] => xreal_tac v
  end.

Ltac bound_tac :=
  unfold Xround, Xbind ;
  match goal with
  | |- (round ?r rnd_DN ?p ?v <= ?w)%R =>
    apply Rle_trans with (1 := proj1 (proj2 (Generic_fmt.round_DN_pt F.radix (FLX.FLX_exp (Zpos p)) v)))
  | |- (?w <= round ?r_UP ?p ?v)%R =>
    apply Rle_trans with (2 := proj1 (proj2 (Generic_fmt.round_UP_pt F.radix (FLX.FLX_exp (Zpos p)) v)))
  end.

Lemma lower_correct :
  forall xi : type, F.toX (lower xi) = Xlower (convert xi).
Proof.
intros [|xl xu].
simpl.
now rewrite F.nan_correct.
easy.
Qed.

Lemma upper_correct :
  forall xi : type, F.toX (upper xi) = Xupper (convert xi).
Proof.
intros [|xl xu].
simpl.
now rewrite F.nan_correct.
easy.
Qed.

Theorem subset_correct :
  forall xi yi : type,
  subset xi yi = true -> Interval.subset (convert xi) (convert yi).
Proof.
intros xi yi.
case xi ; case yi ; try (simpl ; intros ; try exact I ; discriminate).
intros yl yu xl xu H.
destruct (andb_prop _ _ H) as (H1, H2).
split.
(* lower bound *)
generalize H1. clear.
rewrite F'.cmp_correct.
unfold le_lower, le_upper, negb.
rewrite F.real_correct.
destruct (F.toX yl) as [|ylr].
easy.
destruct (F.toX xl) as [|xlr].
easy.
simpl.
destruct (Rcompare_spec xlr ylr) ; intros ; simpl.
discriminate H1.
rewrite H.
apply Rle_refl.
apply Ropp_le_contravar.
now left.
(* upper bound *)
generalize H2. clear.
rewrite F'.cmp_correct.
unfold le_upper, negb.
rewrite F.real_correct.
destruct (F.toX yu) as [|yur].
easy.
destruct (F.toX xu) as [|xur].
easy.
simpl.
destruct (Rcompare_spec xur yur) ; intros.
now left.
now right.
easy.
Qed.

Lemma join_correct :
  forall xi yi v,
  contains (convert xi) v \/ contains (convert yi) v ->
  contains (convert (join xi yi)) v.
Proof.
intros [|xl xu] [|yl yu] [|v]; simpl; try tauto.
rewrite F.min_correct, F.max_correct.
split.
xreal_tac xl ; xreal_tac yl ; try easy.
simpl.
destruct H as [[H _]|[H _]].
apply Rle_trans with (2 := H).
apply Rmin_l.
apply Rle_trans with (2 := H).
apply Rmin_r.
xreal_tac xu ; xreal_tac yu ; try easy.
simpl.
destruct H as [[_ H]|[_ H]].
apply Rle_trans with (1 := H).
apply Rmax_l.
apply Rle_trans with (1 := H).
apply Rmax_r.
Qed.

Theorem meet_correct :
  forall xi yi v,
  contains (convert xi) v -> contains (convert yi) v ->
  contains (convert (meet xi yi)) v.
Proof.
intros [|xl xu] [|yl yu] [|v] ; simpl ; intros Hx Hy ; trivial.
destruct Hx as (Hx1, Hx2).
destruct Hy as (Hy1, Hy2).
split ; rewrite 2!F.real_correct.
(* . *)
xreal_tac xl.
exact Hy1.
xreal_tac yl.
now rewrite X.
rewrite F.max_correct.
rewrite X, X0.
simpl.
now apply Rmax_lub.
(* . *)
xreal_tac xu.
exact Hy2.
xreal_tac yu.
now rewrite X.
rewrite F.min_correct.
rewrite X, X0.
simpl.
now apply Rmin_glb.
Qed.

Theorem meet_correct' :
  forall xi yi v,
  contains (convert (meet xi yi)) v ->
  contains (convert xi) v /\ contains (convert yi) v.
Proof.
intros [|xl xu] [|yl yu] v H ; try easy.
destruct v as [|v] ; try easy.
revert H.
simpl.
assert (Hmin: forall p q, (v <= Rmin p q)%R -> (v <= p /\ v <= q)%R).
  intros p q H.
  unfold Rmin in H.
  destruct Rle_dec as [H'|H'] ; lra.
assert (Hmax: forall p q, (Rmax p q <= v)%R -> (p <= v /\ q <= v)%R).
  intros p q H.
  unfold Rmax in H.
  destruct Rle_dec as [H'|H'] ; lra.
rewrite 4!F.real_correct.
case_eq (F.toX xl) ; [intros _ | intros xl' Hxl] ;
  (case_eq (F.toX xu) ; [intros _ | intros xu' Hxu]) ;
  (case_eq (F.toX yl) ; [intros _ | intros yl' Hyl]) ;
  (case_eq (F.toX yu) ; [intros _ | intros yu' Hyu]) ;
  try easy.
- now rewrite Hxu.
- intros [_ H].
  rewrite F.min_correct in H.
  rewrite Hxu, Hyu in H.
  now apply Hmin in H.
- now rewrite Hxu.
- intros [H1 H2].
  rewrite F.min_correct in H2.
  rewrite Hxu, Hyu in H2.
  now apply Hmin in H2.
- now rewrite Hxl.
- now rewrite Hxl.
- intros [H _].
  rewrite F.max_correct in H.
  rewrite Hxl, Hyl in H.
  now apply Hmax in H.
- intros [H1 H2].
  rewrite F.max_correct in H1.
  rewrite Hxl, Hyl in H1.
  now apply Hmax in H1.
- now rewrite Hxl, Hxu.
- intros [H1 H2].
  rewrite Hxl in H1.
  rewrite F.min_correct in H2.
  rewrite Hxu, Hyu in H2.
  now apply Hmin in H2.
- intros [H1 H2].
  rewrite F.max_correct in H1.
  rewrite Hxl, Hyl in H1.
  rewrite Hxu in H2.
  now apply Hmax in H1.
- intros [H1 H2].
  rewrite F.max_correct in H1.
  rewrite Hxl, Hyl in H1.
  rewrite F.min_correct in H2.
  rewrite Hxu, Hyu in H2.
  apply Hmin in H2.
  now apply Hmax in H1.
Qed.

Definition bounded_prop xi :=
  convert xi = Interval.Ibnd (F.toX (lower xi)) (F.toX (upper xi)).

Theorem lower_bounded_correct :
  forall xi,
  lower_bounded xi = true ->
  F.toX (lower xi) = Xreal (proj_val (F.toX (lower xi))) /\
  bounded_prop xi.
Proof.
unfold lower_bounded.
intros [|xl xu] H.
discriminate H.
generalize (F.real_correct xl).
rewrite H.
clear H.
simpl.
unfold F.toX.
case (F.toF xl).
intro H.
discriminate H.
repeat split.
repeat split.
Qed.

Theorem upper_bounded_correct :
  forall xi,
  upper_bounded xi = true ->
  F.toX (upper xi) = Xreal (proj_val (F.toX (upper xi))) /\
  bounded_prop xi.
Proof.
unfold upper_bounded.
intros [|xl xu] H.
discriminate H.
generalize (F.real_correct xu).
rewrite H.
clear H.
simpl.
unfold F.toX.
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
Proof.
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
Proof.
intros [|xl xu] x y Hy Hx.
exact I.
split.
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
Proof.
intros [|xl xu] x y Hy Hx.
exact I.
split.
simpl in Hy.
xreal_tac xl.
apply Rle_trans with (2 := Hx).
exact (proj1 Hy).
rewrite F.nan_correct.
exact I.
Qed.

Theorem lower_complement_correct :
  forall xi x y,
  contains (convert xi) (Xreal x) ->
  contains (convert (lower_complement xi)) (Xreal y) ->
  (y <= x)%R.
Proof.
intros [|xl xu] x y.
intros _ H.
now apply empty_correct in H.
intros [H _].
simpl.
rewrite F.real_correct.
case_eq (F.toX xl).
intros _ H'.
now apply empty_correct in H'.
intros l Hl [_ H'].
rewrite Hl in H, H'.
now apply Rle_trans with l.
Qed.

Theorem upper_complement_correct :
  forall xi x y,
  contains (convert xi) (Xreal x) ->
  contains (convert (upper_complement xi)) (Xreal y) ->
  (x <= y)%R.
Proof.
intros [|xl xu] x y.
intros _ H.
now apply empty_correct in H.
intros [_ H].
simpl.
rewrite F.real_correct.
case_eq (F.toX xu).
intros _ H'.
now apply empty_correct in H'.
intros u Hu [H' _].
rewrite Hu in H, H'.
now apply Rle_trans with u.
Qed.

Theorem whole_correct :
  forall x,
  contains (convert whole) (Xreal x).
Proof.
intros x.
simpl.
rewrite F.nan_correct.
split ; split.
Qed.

Lemma sign_large_correct_ :
  forall xl xu x,
  contains (convert (Ibnd xl xu)) (Xreal x) ->
  match sign_large_ xl xu with
  | Xeq => x = 0%R /\ F.toX xl = Xreal 0 /\ F.toX xu = Xreal 0
  | Xlt => (x <= 0)%R /\ (match F.toX xl with Xreal rl => (rl <= 0)%R | _=> True end) /\ (exists ru, F.toX xu = Xreal ru /\ (ru <= 0)%R)
  | Xgt => (0 <= x)%R /\ (match F.toX xu with Xreal ru => (0 <= ru)%R | _=> True end) /\ (exists rl, F.toX xl = Xreal rl /\ (0 <= rl)%R)
  | Xund =>
    match F.toX xl with Xreal rl => (rl <= 0)%R | _=> True end /\
    match F.toX xu with Xreal ru => (0 <= ru)%R | _=> True end
  end.
Proof.
intros xl xu x (Hxl, Hxu).
unfold sign_large_.
rewrite 2!F'.cmp_correct.
rewrite F.zero_correct.
destruct (F.toX xu) as [|xur].
simpl.
destruct (F.toX xl) as [|xlr].
easy.
simpl.
case Rcompare_spec ; intro Hl ; repeat split.
now apply Rlt_le.
now rewrite Hl in Hxl.
rewrite Hl in Hxl |- *.
eexists ; repeat split.
apply Rle_refl.
now apply Rlt_le, Rlt_le_trans with (2 := Hxl).
eexists ; repeat split.
now apply Rlt_le.
simpl.
case Rcompare_spec.
intros Hu.
replace (match Xcmp (F.toX xl) (Xreal 0) with Xeq => Xlt | _ => Xlt end) with Xlt by now case Xcmp.
destruct (F.toX xl) as [|xlr].
repeat split.
now apply Rlt_le, Rle_lt_trans with (1 := Hxu).
eexists ; repeat split.
now apply Rlt_le.
repeat split.
now apply Rlt_le, Rle_lt_trans with (1 := Hxu).
now apply Rlt_le, Rle_lt_trans with (2 := Hu), Rle_trans with x.
eexists ; repeat split.
now apply Rlt_le.
intros ->.
destruct (F.toX xl) as [|xlr].
repeat split.
easy.
eexists ; repeat split.
apply Rle_refl.
simpl.
case Rcompare_spec.
intros Hl.
repeat split.
easy.
now apply Rlt_le.
eexists ; repeat split.
apply Rle_refl.
intros ->.
repeat split.
now apply Rle_antisym.
intros Hl.
repeat split.
easy.
now apply Rle_trans with (1 := Hxl).
eexists ; repeat split.
apply Rle_refl.
intros Hu.
destruct (F.toX xl) as [|xlr].
repeat split.
now apply Rlt_le.
simpl.
case Rcompare_spec.
intros Hl.
now split ; apply Rlt_le.
intros ->.
repeat split.
easy.
now apply Rlt_le.
eexists ; repeat split.
apply Rle_refl.
intros Hl.
repeat split.
now apply Rlt_le, Rlt_le_trans with (2 := Hxl).
now apply Rlt_le.
eexists ; repeat split.
now apply Rlt_le.
Qed.

Theorem sign_large_correct :
  forall xi,
  match sign_large xi with
  | Xeq => forall x, contains (convert xi) x -> x = Xreal 0
  | Xlt => forall x, contains (convert xi) x -> x = Xreal (proj_val x) /\ Rle (proj_val x) 0
  | Xgt => forall x, contains (convert xi) x -> x = Xreal (proj_val x) /\ Rle 0 (proj_val x)
  | Xund => True
  end.
Proof.
intros [|xl xu].
exact I.
generalize (sign_large_correct_ xl xu).
unfold sign_large.
case (sign_large_ xl xu) ;
  try intros H [|x] Hx ;
  try (elim Hx ; fail) ;
  try eexists ; repeat split ;
  try apply f_equal ;
  exact (proj1 (H _ Hx)).
Qed.

Lemma sign_strict_correct_ :
  forall xl xu x,
  contains (convert (Ibnd xl xu)) (Xreal x) ->
  match sign_strict_ xl xu with
  | Xeq => x = 0%R /\ F.toX xl = Xreal 0 /\ F.toX xu = Xreal 0
  | Xlt => (x < 0)%R /\ (match F.toX xl with Xreal rl => (rl < 0)%R | _=> True end) /\ (exists ru, F.toX xu = Xreal ru /\ (ru < 0)%R)
  | Xgt => (0 < x)%R /\ (match F.toX xu with Xreal ru => (0 < ru)%R | _=> True end) /\ (exists rl, F.toX xl = Xreal rl /\ (0 < rl)%R)
  | Xund =>
    match F.toX xl with Xreal rl => (rl <= 0)%R | _=> True end /\
    match F.toX xu with Xreal ru => (0 <= ru)%R | _=> True end
  end.
Proof.
intros xl xu x (Hxl, Hxu).
unfold sign_strict_.
rewrite 2!F'.cmp_correct.
rewrite F.zero_correct.
destruct (F.toX xu) as [|xur].
simpl.
destruct (F.toX xl) as [|xlr].
easy.
simpl.
case Rcompare_spec ; intro Hl ; repeat split.
now apply Rlt_le.
rewrite Hl.
apply Rle_refl.
now apply Rlt_le_trans with (2 := Hxl).
now eexists ; repeat split.
simpl.
case Rcompare_spec.
intros Hu.
replace (match Xcmp (F.toX xl) (Xreal 0) with Xeq => Xlt | _ => Xlt end) with Xlt by now case Xcmp.
destruct (F.toX xl) as [|xlr].
repeat split.
now apply Rle_lt_trans with (1 := Hxu).
now eexists ; repeat split.
repeat split.
now apply Rle_lt_trans with (1 := Hxu).
now apply Rle_lt_trans with (2 := Hu), Rle_trans with x.
now eexists ; repeat split.
intros ->.
destruct (F.toX xl) as [|xlr].
repeat split.
apply Rle_refl.
simpl.
case Rcompare_spec.
intros Hl.
split.
now apply Rlt_le.
apply Rle_refl.
intros ->.
repeat split.
now apply Rle_antisym.
intros Hl.
elim Rlt_not_le with (1 := Hl).
now apply Rle_trans with (1 := Hxl).
intros Hu.
destruct (F.toX xl) as [|xlr].
repeat split.
now apply Rlt_le.
simpl.
case Rcompare_spec.
intros Hl.
now split ; apply Rlt_le.
intros ->.
split.
apply Rle_refl.
now apply Rlt_le.
intros Hl.
repeat split.
now apply Rlt_le_trans with (2 := Hxl).
easy.
now eexists ; repeat split.
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
  try eexists ; repeat split ;
  try apply f_equal ;
  exact (proj1 (H _ Hx)).
Qed.

Theorem fromZ_small_correct :
  forall v,
  (Z.abs v <= 256)%Z ->
  contains (convert (fromZ_small v)) (Xreal (IZR v)).
Proof.
intros.
simpl.
rewrite F.fromZ_correct by easy.
split ; apply Rle_refl.
Qed.

Theorem fromZ_correct :
  forall prec v,
  contains (convert (fromZ prec v)) (Xreal (IZR v)).
Proof.
intros.
apply le_contains.
apply F.fromZ_DN_correct.
apply F.fromZ_UP_correct.
Qed.

Theorem midpoint_correct :
  forall xi,
  (exists x, contains (convert xi) x) ->
  F.toX (midpoint xi) = Xreal (proj_val (F.toX (midpoint xi))) /\
  contains (convert xi) (F.toX (midpoint xi)).
Proof.
intros [|xl xu].
{ intros _.
  refine (conj _ I).
  simpl.
  now rewrite F.zero_correct. }
intros (x, Hx).
destruct x as [|x]; [now elim Hx|].
destruct Hx as (Hx1,Hx2).
assert (Hr: (1 <= IZR (Zpower_pos F.radix 1))%R).
{ rewrite IZR_Zpower_pos.
  rewrite <- bpow_powerRZ.
  now apply (bpow_le F.radix 0). }
simpl.
unfold c1, cm1, c2.
repeat rewrite F'.cmp_correct.
xreal_tac xl ; xreal_tac xu ; simpl ;
  rewrite F.zero_correct ; simpl; [now repeat split| | |].
(*
{ (* infinite lower *)
  destruct (Rcompare_spec r 0).
  { rewrite F.mul_correct, F.fromZ_correct by easy.
    rewrite X0.
    simpl.
    repeat split.
    apply (Rle_trans _ (r * 2)).
    { now apply Generic_fmt.round_DN_pt, FLX.FLX_exp_valid. }
    pattern r at 2 ; rewrite <- Rmult_1_r.
    apply Rmult_le_compat_neg_l.
    { exact (Rlt_le _ _ H). }
    lra. }
  { rewrite H.
    rewrite F.fromZ_correct by easy.
    repeat split.
    now apply IZR_le. }
  rewrite F.zero_correct.
  repeat split.
  exact (Rlt_le _ _ H). }
{ (* infinite upper *)
  destruct (Rcompare_spec r 0).
  { rewrite F.zero_correct.
    repeat split.
    exact (Rlt_le _ _ H). }
  { rewrite H.
    rewrite F.fromZ_correct by easy.
    repeat split.
    now apply IZR_le. }
  rewrite F.mul_correct, F.fromZ_correct by easy.
  rewrite X.
  simpl.
  repeat split.
  apply (Rle_trans _ (r * 2)).
  { pattern r at 1 ; rewrite <- Rmult_1_r.
    apply Rmult_le_compat_l.
    { exact (Rlt_le _ _ H). }
    lra. }
  now apply Generic_fmt.round_UP_pt, FLX.FLX_exp_valid. }
(* finite bounds *)
assert (
  match F.toX (F.midpoint xl xu) with
  | Xnan => False
  | Xreal x0 => (r <= x0 <= r0)%R
  end).
{ generalize (F.midpoint_correct xl xu (eq_refl _)).
  unfold F.toR.
  rewrite !F.real_correct, X, X0.
  intro H.
  specialize (H (eq_refl _) (eq_refl) (Rle_trans _ _ _ Hx1 Hx2)).
  revert H.
  now case F.toX. }
(* finite bounds 2 *)
case_eq (F.toX (F.midpoint xl xu)) ; intros.
{ now rewrite H0 in H. }
destruct (Rcompare_spec r 0) as [H1|H1|H1] ;
  destruct (Rcompare_spec r0 0) as [H2|H2|H2] ;
  try (
    refine (conj _ H) ;
    rewrite H0 ;
    apply refl_equal).
rewrite F.zero_correct.
simpl.
rewrite H1, H2.
repeat split ; apply Rle_refl.
Qed.
*)
Admitted.

Theorem midpoint'_correct :
  forall xi,
  (forall x, contains (convert (midpoint' xi)) x -> contains (convert xi) x) /\
  (not_empty (convert xi) -> not_empty (convert (midpoint' xi))).
Proof.
intros [|xl xu].
{ split; [easy|].
  intros _.
  exists R0.
  simpl.
  rewrite F.zero_correct.
  split ; apply Rle_refl. }
unfold midpoint'.
unfold c1, cm1, c2.
set (m := F.midpoint xl xu).
set (mi := if F'.lt xu xl then empty else Ibnd m m).
rewrite 2!F'.cmp_correct, F.zero_correct.
unfold not_empty.
simpl.
assert (He: forall b, exists v : R, contains (convert (Ibnd b b)) (Xreal v)).
{ intros b.
  exists (proj_val (F.toX b)).
  simpl.
  destruct (F.toX b) as [|br] ; split ; try exact I ; apply Rle_refl. }
(*
case_eq (F.toX xl) ; [|intros xlr] ; intros Hl.
{ (* infinite lower *)
  case_eq (F.toX xu) ; [|intros xur] ; intros Hu ; simpl.
  { split.
    { now intros [|x]. }
    intros _.
    exists R0.
    rewrite F.zero_correct.
    split ; apply Rle_refl. }
  split.
  { case Rcompare_spec ; intros Hu0 ; simpl ;
      (intros [|x] ; [easy|]).
    { rewrite F.mul_correct, F.fromZ_correct, Hu by easy.
      simpl.
      intros [_ H].
      apply (conj I).
      apply Rle_trans with (1 := H).
      apply (Rle_trans _ (xur * 2)).
      { now apply Generic_fmt.round_DN_pt, FLX.FLX_exp_valid. }
      rewrite <- (Rmult_1_r xur) at 2.
      apply Rmult_le_compat_neg_l.
      { now apply Rlt_le. }
      lra. }
    { rewrite F.fromZ_correct by easy.
      intros [H1 H2].
      apply (conj I).
      rewrite (Rle_antisym _ _ H2 H1), Hu0.
      now apply IZR_le. }
    rewrite F.zero_correct.
    intros [H1 H2].
    apply (conj I).
    rewrite (Rle_antisym _ _ H2 H1).
    now apply Rlt_le. }
  intros _.
  case Rcompare ; apply He. }
case_eq (F.toX xu) ; [|intros xur] ; intros Hu ; simpl.
{ (* infinite upper *)
  split.
  case Rcompare_spec ; intros Hl0 ; simpl ;
    (intros [|x] ; [easy|]).
  { rewrite F.zero_correct.
    intros [H1 H2].
    refine (conj _ I).
    rewrite (Rle_antisym _ _ H2 H1).
    now apply Rlt_le. }
  { rewrite F.fromZ_correct by easy.
    intros [H1 H2].
    refine (conj _ I).
    rewrite (Rle_antisym _ _ H2 H1), Hl0.
    now apply IZR_le. }
  { rewrite F.mul_correct, F.fromZ_correct, Hl by easy.
    simpl.
    intros [H _].
    refine (conj _ I).
    apply Rle_trans with (2 := H).
    apply (Rle_trans _ (xlr * 2)).
    { rewrite <- (Rmult_1_r xlr) at 1.
      apply Rmult_le_compat_l.
      { now apply Rlt_le. }
      lra. }
    now apply Generic_fmt.round_UP_pt, FLX.FLX_exp_valid. }
  intros _.
  case Rcompare ; apply He. }
(* finite bounds *)
split.
{ intros x.
  assert (contains (convert mi) x -> match x with Xnan => False | Xreal x => (xlr <= x <= xur)%R end).
  { unfold mi, m. clear -Hl Hu.
    rewrite F'.lt_correct.
    2: now unfold F.toR ; rewrite Hu.
    2: now unfold F.toR ; rewrite Hl.
    unfold F.toR.
    rewrite Hl, Hu.
    simpl.
    case Rlt_bool_spec ; intros Hlu.
    { intros H.
      now elim empty_correct with x. }
    simpl.
    destruct x as [|x]; [easy|].
    generalize (F.midpoint_correct xl xu (eq_refl _)).
    unfold F.toR.
    rewrite !F.real_correct, Hl, Hu.
    intro H.
    specialize (H (eq_refl _) (eq_refl _) Hlu).
    revert H.
    case F.toX; [easy|]; intro rm.
    simpl.
    lra. }
  case Rcompare_spec ; intros Hl0 ;
  case Rcompare_spec ; intros Hu0 ; try exact H.
  destruct x as [|x]; [easy|].
  simpl.
  rewrite F.zero_correct.
  lra. }
intros [v Hv].
revert mi.
rewrite F'.lt_correct.
2: now unfold F.toR ; rewrite Hu.
2: now unfold F.toR ; rewrite Hl.
unfold F.toR.
rewrite Hl, Hu.
rewrite Rlt_bool_false.
{ case Rcompare ; case Rcompare ; apply He. }
now apply Rle_trans with v.
Qed.
*)
Admitted.

Theorem bisect_correct :
  forall xi x,
  contains (convert xi) x ->
  contains (convert (fst (bisect xi))) x \/ contains (convert (snd (bisect xi))) x.
Proof.
intros [|xl xu] [|x] H.
  now left.
  now left.
  easy.
unfold bisect.
fold (midpoint (Ibnd xl xu)).
destruct (midpoint_correct (Ibnd xl xu)) as [H1 H2].
  now exists (Xreal x).
set (m := midpoint _).
fold m in H1, H2.
clearbody m.
revert H.
simpl.
rewrite H1.
intros [H3 H4].
destruct (Rle_or_lt x (proj_val (F.toX m))) as [H5|H5].
  now left.
right.
split.
now apply Rlt_le.
exact H4.
Qed.

Theorem mask_correct :
  extension_2 Xmask mask.
Proof.
now intros xi [|yl yu] x [|y] Hx Hy.
Qed.

Theorem mask_correct' :
  forall xi yi x,
  contains (convert xi) x ->
  contains (convert (mask xi yi)) x.
Proof.
now intros xi [|yl yu] x Hx.
Qed.

Definition propagate_l fi :=
  forall xi yi : type, convert xi = Interval.Inan ->
                       convert (fi xi yi) = Interval.Inan.

Definition propagate_r fi :=
  forall xi yi : type, convert yi = Interval.Inan ->
                       convert (fi xi yi) = Interval.Inan.

Theorem neg_correct :
  extension Xneg neg.
Proof.
intros [ | xl xu] [ | x] ; simpl ; trivial.
intros (Hxl, Hxu).
split ; rewrite F.neg_correct ;
  [ xreal_tac xu | xreal_tac xl ] ;
  apply Ropp_le_contravar ; assumption.
Qed.

Theorem neg_correct' :
  forall xi x,
  contains (convert (neg xi)) (Xneg x) ->
  contains (convert xi) x.
Proof.
intros [|xl xu] [|x] ; try easy.
simpl.
rewrite 2!F.neg_correct.
destruct (F.toX xl) as [|xl'] ;
  destruct (F.toX xu) as [|xu'] ; simpl.
easy.
intros [H _].
apply (conj I).
now apply Ropp_le_cancel.
intros [_ H].
refine (conj _ I).
now apply Ropp_le_cancel.
intros [H1 H2].
now split ; apply Ropp_le_cancel.
Qed.

Theorem abs_correct :
  extension Xabs abs.
Proof.
intros [ | xl xu] [ | x] Hx ; trivial ; [ elim Hx | idtac ].
simpl.
generalize (sign_large_correct_ _ _ _ Hx).
case (sign_large_ xl xu) ; intros.
(* zero *)
rewrite (proj1 H).
rewrite Rabs_R0.
simpl.
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
rewrite F.zero_correct.
split.
exact (Rabs_pos x).
(* - upper *)
rewrite F.max_correct.
rewrite F.neg_correct.
unfold contains, convert in Hx.
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
  forall xi, convert xi <> Interval.Inan ->
  le_lower' (Xreal 0) (F.toX (lower (abs xi))).
Proof.
intros [|xl xu].
intros H.
now elim H.
intros _.
simpl.
unfold sign_large_.
rewrite 2!F'.cmp_correct, F.zero_correct.
case_eq (F.toX xl) ; case_eq (F.toX xu).
simpl.
intros _ _.
rewrite F.zero_correct.
apply Rle_refl.
simpl.
intros ru Hu _.
case Rcompare_spec ; simpl ; intros H.
rewrite F.neg_correct, Hu.
simpl.
rewrite <- Ropp_0.
apply Ropp_le_contravar.
now apply Rlt_le.
rewrite F.neg_correct, Hu.
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
    try rewrite F.neg_correct ;
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
  forall xi, (0 <= proj_val (F.toX (lower (abs xi))))%R.
Proof.
intros [|xl xu].
simpl.
rewrite F.nan_correct.
apply Rle_refl.
refine (_ (abs_ge_0 (Ibnd xl xu) _)).
2: discriminate.
simpl.
now case F.toX.
Qed.

Theorem mul2_correct :
  forall prec xi x,
  contains (convert xi) x ->
  contains (convert (mul2 prec xi)) (Xmul x (Xreal 2)).
Proof.
intros prec [ | xl xu].
split.
intros [ | x] Hx.
elim Hx.
unfold convert in Hx.
destruct Hx as (Hxl, Hxu).
unfold convert, mul2, c2.
(*
rewrite 2!F.mul_correct, F.fromZ_correct by easy.
split ; xreal_tac2 ; simpl ; apply (Rle_trans _ (r * 2)) ; try lra.
{ now apply Generic_fmt.round_DN_pt, FLX.FLX_exp_valid. }
now apply Generic_fmt.round_UP_pt, FLX.FLX_exp_valid.
Qed.
*)
Admitted.

Theorem add_correct :
  forall prec,
  extension_2 Xadd (add prec).
Proof.
intros prec [ | xl xu] [ | yl yu] [ | x] [ | y] ; trivial.
intros (Hxl, Hxu) (Hyl, Hyu).
apply le_contains.
{ apply (le_lower_trans _ (Xadd (F.toX xl) (F.toX yl)));
    [now apply F.add_DN_correct|].
  revert Hxl Hyl.
  xreal_tac2; [now simpl|intro Hx].
  xreal_tac2; [now simpl|intro Hy].
  now apply Ropp_le_contravar, Rplus_le_compat. }
apply (le_upper_trans _ (Xadd (F.toX xu) (F.toX yu)));
  [|now apply F.add_UP_correct].
revert Hxu Hyu.
xreal_tac2; [now simpl|intro Hx].
xreal_tac2; [now simpl|intro Hy].
now apply Rplus_le_compat.
Qed.

Theorem sub_correct :
  forall prec,
  extension_2 Xsub (sub prec).
Proof.
intros prec [ | xl xu] [ | yl yu] [ | x] [ | y] ; trivial.
intros (Hxl, Hxu) (Hyl, Hyu).
apply le_contains.
{ apply (le_lower_trans _ (Xsub (F.toX xl) (F.toX yu)));
    [now apply F.sub_DN_correct|].
  revert Hxl Hyu.
  xreal_tac2; [now simpl|intro Hx].
  xreal_tac2; [now simpl|intro Hy].
  now apply Ropp_le_contravar, Rplus_le_compat; [|apply Ropp_le_contravar]. }
apply (le_upper_trans _ (Xsub (F.toX xu) (F.toX yl)));
  [|now apply F.sub_UP_correct].
revert Hxu Hyl.
xreal_tac2; [now simpl|intro Hx].
xreal_tac2; [now simpl|intro Hy].
now apply Rplus_le_compat; [|apply Ropp_le_contravar].
Qed.

Theorem sqrt_correct :
  forall prec, extension Xsqrt (sqrt prec).
Proof.
intros prec [ | xl xu] [ | x] ; simpl; trivial; [easy|].
intros [Hxl Hxu].
rewrite F'.cmp_correct.
rewrite F.zero_correct.
revert Hxl.
case_eq (F.toX xl) ; [ split | idtac ].
intros rl Hrl Hxl.
unfold Xsqrt'.
simpl.
destruct (is_negative_spec x).
now rewrite Rcompare_Lt; [|apply (Rle_lt_trans _ x)].
case Rcompare_spec; intro Hrl'; [exact I| |].
(* xl zero *)
apply le_contains.
now rewrite F.zero_correct; apply Ropp_le_contravar, sqrt_positivity.
assert (H' := F.sqrt_UP_correct prec xu); revert H'.
apply le_upper_trans.
revert Hxu; xreal_tac2; intro Hxu; [exact I|].
simpl; unfold Xsqrt'.
now case is_negative_spec; intro Hr; [|apply sqrt_le_1_alt].
(* xl positive *)
apply le_contains.
apply (le_lower_trans _ _ _ (F.sqrt_DN_correct prec xl)).
rewrite Hrl.
simpl; unfold Xsqrt'.
now case is_negative_spec; intro Hr; [|apply Ropp_le_contravar, sqrt_le_1_alt].
assert (H' := F.sqrt_UP_correct prec xu); revert H'.
apply le_upper_trans.
revert Hxu; xreal_tac2; intro Hxu; [exact I|].
simpl; unfold Xsqrt'.
now case is_negative_spec; intro Hr; [|apply sqrt_le_1_alt].
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

Local Hint Resolve Rlt_le : mulauto.
Local Hint Resolve Rle_trans : mulauto.
Local Hint Resolve Rmult_le_compat_l : mulauto.
Local Hint Resolve Rmult_le_compat_r : mulauto.
Local Hint Resolve Rmult_le_compat_neg_l : mulauto.
Local Hint Resolve Rmult_le_compat_neg_r : mulauto.

Theorem mul_mixed_correct :
  forall prec yf,
  extension (fun x => Xmul x (F.toX yf)) (fun xi => mul_mixed prec xi yf).
Proof.
intros prec yf [ | xl xu] [ | x] ; try easy.
intros (Hxl, Hxu).
simpl.
rewrite F'.cmp_correct,  F.zero_correct.
xreal_tac2.
simpl.
case Rcompare_spec; intro Hr.
{ apply le_contains.
  { apply (le_lower_trans _ (Xmul (F.toX xu) (F.toX yf)));
      [now apply F.mul_DN_correct|].
    rewrite X.
    revert Hxu; xreal_tac2; [now simpl|]; intro Hx.
    now apply Ropp_le_contravar, Rmult_le_compat_neg_r; [apply Rlt_le|]. }
  apply (le_upper_trans _ (Xmul (F.toX xl) (F.toX yf)));
    [|now apply F.mul_UP_correct].
  rewrite X.
  revert Hxl; xreal_tac2; [now simpl|]; intro Hx.
  now apply Rmult_le_compat_neg_r; [apply Rlt_le|]. }
{ rewrite Hr, Rmult_0_r.
  now apply le_contains; rewrite F.zero_correct; right. }
apply le_contains.
{ apply (le_lower_trans _ (Xmul (F.toX xl) (F.toX yf)));
    [now apply F.mul_DN_correct|].
  rewrite X.
  revert Hxl; xreal_tac2; [now simpl|]; intro Hx.
  now apply Ropp_le_contravar, Rmult_le_compat_r; [apply Rlt_le|]. }
apply (le_upper_trans _ (Xmul (F.toX xu) (F.toX yf)));
  [|now apply F.mul_UP_correct].
rewrite X.
revert Hxu; xreal_tac2; [now simpl|]; intro Hx.
now apply Rmult_le_compat_r; [apply Rlt_le|].
Qed.

(* TODO improve and move *)
Ltac bound_tac2 :=
  match goal with
  | H:F.toX (F.mul_DN ?prec ?x ?y) = Xreal ?r |- (?r <= ?z)%R =>
    generalize (F.mul_DN_correct prec x y); rewrite H;
    (xreal_tac x; [now simpl|]);
    (xreal_tac y; [now simpl|]);
    (let H := fresh "H" in
     intro H; apply Ropp_le_cancel in H;
     apply (Rle_trans _ _ _ H); clear H)
  | H:F.toX (F.mul_UP ?prec ?x ?y) = Xreal ?r |- (?z <= ?r)%R =>
    generalize (F.mul_UP_correct prec x y); rewrite H;
    (xreal_tac x; [now simpl|]);
    (xreal_tac y; [now simpl|]);
    apply Rle_trans
  end.

Theorem mul_correct :
  forall prec,
  extension_2 Xmul (mul prec).
Proof.
intros prec [ | xl xu] [ | yl yu] [ | x] [ | y] ;
  try ( intros ; exact I ) ;
  try ( intros H1 H2 ; try elim H1 ; elim H2 ; fail ).
intros (Hxl, Hxu) (Hyl, Hyu).
simpl.
unfold bnd, contains, convert.
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
  try ( split; xreal_tac2 ; bound_tac2 ;
        clear_complex ) ;
  (* solve by transivity *)
  try ( eauto with mulauto ; fail ).
(* multiplication around zero *)
rewrite F.min_correct, F.max_correct.
split.
{ generalize (F.mul_DN_correct prec xl yu).
  xreal_tac2; [now simpl|intro H_DN_xl_yu].
  generalize (F.mul_DN_correct prec xu yl).
  xreal_tac2; [now simpl|intro H_DN_xu_yl].
  simpl; apply <-Rmin_Rle.
  destruct (Rle_or_lt x 0) as [Hx|Hx];
    [left|right; generalize (Rlt_le _ _ Hx); clear Hx; intro Hx] ;
    bound_tac2 ;
    clear_complex ;
    eauto with mulauto. }
generalize (F.mul_UP_correct prec xl yl).
xreal_tac (F.mul_UP prec xl yl); [now simpl|intro H_UP_xl_yl].
generalize (F.mul_UP_correct prec xu yu).
xreal_tac (F.mul_UP prec xu yu); [now simpl|intro H_UP_xu_yu].
simpl; apply <-Rmax_Rle.
destruct (Rle_or_lt x 0) as [Hx|Hx];
  [left|right; generalize (Rlt_le _ _ Hx); clear Hx; intro Hx] ;
  bound_tac2 ;
  clear_complex ;
  eauto with mulauto.
Qed.

Ltac simpl_is_zero :=
  let X := fresh "X" in
  match goal with
  | H: Rlt ?v 0 |- context [is_zero ?v] =>
    destruct (is_zero_spec v) as [X|X] ;
    [ rewrite X in H ; elim (Rlt_irrefl _ H) | idtac ]
  | H: Rlt 0 ?v |- context [is_zero ?v] =>
    destruct (is_zero_spec v) as [X|X] ;
    [ rewrite X in H ; elim (Rlt_irrefl _ H) | idtac ]
  | H: Rlt ?v 0 /\ _ |- context [is_zero ?v] =>
    destruct (is_zero_spec v) as [X|X] ;
    [ rewrite X in H ; elim (Rlt_irrefl _ (proj1 H)) | idtac ]
    (*rewrite (Rcompare_correct_lt _ _ (proj1 H))*)
  | H: _ /\ (Rlt ?v 0 /\ _) |- context [is_zero ?v] =>
    destruct (is_zero_spec v) as [X|X] ;
    [ rewrite X in H ; elim (Rlt_irrefl _ (proj1 (proj2 H))) | idtac ]
    (*rewrite (Rcompare_correct_lt _ _ (proj1 (proj2 H)))*)
  | H: Rlt 0 ?v /\ _ |- context [is_zero ?v] =>
    destruct (is_zero_spec v) as [X|X] ;
    [ rewrite X in H ; elim (Rlt_irrefl _ (proj1 H)) | idtac ]
    (*rewrite (Rcompare_correct_gt _ _ (proj1 H))*)
  | H: _ /\ (Rlt 0 ?v /\ _) |- context [is_zero ?v] =>
    destruct (is_zero_spec v) as [X|X] ;
    [ rewrite X in H ; elim (Rlt_irrefl _ (proj1 (proj2 H))) | idtac ]
    (*rewrite (Rcompare_correct_gt _ _ (proj1 (proj2 H)))*)
  end.

Local Hint Resolve Rinv_lt_0_compat : mulauto.
Local Hint Resolve Rinv_0_lt_compat : mulauto.
Local Hint Resolve Rle_Rinv_pos : mulauto.
Local Hint Resolve Rle_Rinv_neg : mulauto.

Local Hint Resolve Rlt_le : mulauto2.
Local Hint Resolve Rinv_lt_0_compat : mulauto2.
Local Hint Resolve Rinv_0_lt_compat : mulauto2.
Local Hint Resolve Rmult_le_pos_pos : mulauto2.
Local Hint Resolve Rmult_le_neg_pos : mulauto2.
Local Hint Resolve Rmult_le_pos_neg : mulauto2.
Local Hint Resolve Rmult_le_neg_neg : mulauto2.

Theorem div_mixed_r_correct :
  forall prec yf,
  extension (fun x => Xdiv x (F.toX yf)) (fun xi => div_mixed_r prec xi yf).
Proof.
intros prec yf [ | xl xu] [ | x] ; try easy.
intros [Hxl Hxu].
simpl.
rewrite F'.cmp_correct, F.zero_correct.
xreal_tac2.
unfold Xdiv'.
simpl.
case Rcompare_spec ; intros Hy ; try exact I ;
  simpl; simpl_is_zero ;
  split ; xreal_tac2.
{ generalize (F.div_DN_correct prec xu yf); rewrite X1.
  do 2 xreal_tac2; [now simpl|].
  unfold Xdiv, Xdiv'; simpl_is_zero.
  intro H; apply Ropp_le_cancel in H; revert H.
  unfold Rdiv ; eauto with mulauto. }
{ generalize (F.div_UP_correct prec xl yf); rewrite X1.
  do 2 xreal_tac2; [now simpl|].
  unfold Xdiv, Xdiv'; simpl_is_zero.
  unfold Rdiv ; eauto with mulauto. }
{ generalize (F.div_DN_correct prec xl yf); rewrite X1.
  do 2 xreal_tac2; [now simpl|].
  unfold Xdiv, Xdiv'; simpl_is_zero.
  intro H; apply Ropp_le_cancel in H; revert H.
  unfold Rdiv ; eauto with mulauto. }
generalize (F.div_UP_correct prec xu yf); rewrite X1.
do 2 xreal_tac2; [now simpl|].
unfold Xdiv, Xdiv'; simpl_is_zero.
unfold Rdiv ; eauto with mulauto.
Qed.

Theorem div_correct :
  forall prec,
  extension_2 Xdiv (div prec).
Proof.
intros prec [ | xl xu] [ | yl yu] [ | x] [ | y] ;
  try ( intros ; exact I ) ;
  try ( intros H1 H2 ; try elim H1 ; elim H2 ; fail ).
intros (Hxl, Hxu) (Hyl, Hyu).
simpl.
unfold bnd, contains, convert, Xdiv'.
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
  try ( (unfold Fdivz_DN || unfold Fdivz_UP) ;
        rewrite F.real_correct ;
        xreal_tac yl ; xreal_tac yu ;
        try rewrite F.zero_correct ) ;
  split ;
  (* solve by comparing to zero *)
  try ( clear_complex ; simpl ; eauto with mulauto2 ; fail ) ;
  (* remove rounding operators *)
  xreal_tac2 ;
  try ( match goal with
        | H:F.toX (F.div_UP ?prec ?x ?y) = Xreal ?r
          |- (?z <= ?r)%R =>
          generalize (F.div_UP_correct prec x y) ; rewrite H ;
          match goal with
          | H:F.toX x = Xnan |- _ => rewrite H ; now simpl
          | H:F.toX x = Xreal _ |- _ => rewrite H
          | _ => xreal_tac x; [now simpl|]
          end ;
          match goal with
          | H:F.toX y = Xnan |- _ => rewrite H ; now simpl
          | H:F.toX y = Xreal _ |- _ => rewrite H
          | _ => xreal_tac y; [now simpl|]
          end ;
          unfold Xdiv, Xdiv', Rdiv ;
          match goal with
            |- context [is_zero ?v] => case (is_zero v) ; [now simpl|]
          end ;
          apply Rle_trans
        | H:F.toX (F.div_DN ?prec ?x ?y) = Xreal ?r
          |- (?r <= ?z)%R =>
          generalize (F.div_DN_correct prec x y) ; rewrite H ;
          match goal with
          | H:F.toX x = Xnan |- _ => rewrite H ; now simpl
          | H:F.toX x = Xreal _ |- _ => rewrite H
          | _ => xreal_tac x; [now simpl|]
          end ;
          match goal with
          | H:F.toX y = Xnan |- _ => rewrite H ; now simpl
          | H:F.toX y = Xreal _ |- _ => rewrite H
          | _ => xreal_tac y; [now simpl|]
          end ;
          unfold Xdiv, Xdiv', Rdiv ;
          match goal with
            |- context [is_zero ?v] => case (is_zero v) ; [now simpl|]
          end ;
          (let H := fresh "H" in
           intro H; apply Ropp_le_cancel in H;
           apply (Rle_trans _ _ _ H); clear H)
        end ) ;
  clear_complex ;
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
unfold bnd, contains, convert, Xinv'.
(* case study on sign of xi *)
generalize (sign_strict_correct_ xl xu x (conj Hxl Hxu)).
unfold c1.
case (sign_strict_ xl xu) ; intros Hx0 ; simpl in Hx0 ;
  (* case study on sign of yi *)
  try exact I ; try simpl_is_zero ;
  (* simplify Fdivz *)
  unfold Fdivz_DN, Fdivz_UP ;
  rewrite 2!F.real_correct ;
  destruct Hx0 as (Hx0, (Hx1, (r, (Hx2, Hx3)))) ;
  rewrite Hx2 in * ;
  split ;
  [ idtac | xreal_tac xl | xreal_tac xu | idtac ] ;
  try ( rewrite F.zero_correct ;
        simpl ; auto with mulauto ; fail ) ;
  (* remove rounding operators *)
  xreal_tac2 ;
  try ( match goal with
        | H:F.toX (F.div_UP ?prec ?x ?y) = Xreal ?r
          |- (?z <= ?r)%R =>
          generalize (F.div_UP_correct prec x y) ; rewrite H ;
          rewrite F.fromZ_correct by easy ;
          match goal with
          | H:F.toX y = Xnan |- _ => rewrite H ; now simpl
          | H:F.toX y = Xreal _ |- _ => rewrite H
          | _ => xreal_tac y; [now simpl|]
          end ;
          unfold Xdiv, Xdiv', Rdiv ;
          match goal with
            |- context [is_zero ?v] => case (is_zero v) ; [now simpl|]
          end ;
          apply Rle_trans
        | H:F.toX (F.div_DN ?prec ?x ?y) = Xreal ?r
          |- (?r <= ?z)%R =>
          generalize (F.div_DN_correct prec x y) ; rewrite H ;
          rewrite F.fromZ_correct by easy ;
          match goal with
          | H:F.toX y = Xnan |- _ => rewrite H ; now simpl
          | H:F.toX y = Xreal _ |- _ => rewrite H
          | _ => xreal_tac y; [now simpl|]
          end ;
          unfold Xdiv, Xdiv', Rdiv ;
          match goal with
            |- context [is_zero ?v] => case (is_zero v) ; [now simpl|]
          end ;
          (let H := fresh "H" in
           intro H; apply Ropp_le_cancel in H;
           apply (Rle_trans _ _ _ H); clear H)
        end ) ;
  rewrite Rmult_1_l ;
  auto with mulauto.
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
unfold bnd, contains, convert.
(* case study on sign of xi *)
generalize (sign_large_correct_ xl xu x (conj Hxl Hxu)).
unfold Rsqr.
case (sign_large_ xl xu) ; intros Hx0 ; simpl in Hx0 ;
  (* remove trivial comparisons with zero *)
  try ( rewrite F.zero_correct ; simpl ;
        try ( rewrite (proj1 Hx0) ; rewrite Rmult_0_l ) ;
        split ; apply Rle_refl ) ;
  try ( match goal with
          |- context [F'.cmp ?x ?y] => case_eq (F'.cmp x y); intro Hcmp
        end ) ;
  split ;
  (* remove trivial comparisons with zero *)
  try ( rewrite F.zero_correct ; apply Rle_0_sqr ) ;
  (* remove rounding operators *)
  try rewrite F.max_correct, F.zero_correct ;
  xreal_tac2 ; simpl ;
  try ( match goal with
        | H:F.toX (F.mul_UP ?prec ?x ?y) = Xreal ?r
          |- (?z <= ?r)%R =>
          generalize (F.mul_UP_correct prec x y) ; rewrite H ;
            xreal_tac2; [now simpl|] ;
          apply Rle_trans
        | H:F.toX (F.mul_DN ?prec ?x ?y) = Xreal ?r
          |- (?r <= ?z)%R =>
          generalize (F.mul_DN_correct prec x y) ; rewrite H ;
            xreal_tac2; [now simpl|] ;
          (let H := fresh "H" in
           intro H; apply Ropp_le_cancel in H;
           apply (Rle_trans _ _ _ H); clear H)
        end ) ;
  (* solve by transivity *)
  try ( clear_complex ; eauto with mulauto ; fail ).
(* multiplication around zero *)
revert X0; rewrite F.max_correct, F.abs_correct.
revert Hxl Hxu Hx0.
xreal_tac2; [discriminate|intro Hr1].
xreal_tac2; [discriminate|intro Hr2].
intros [Hr1' Hr2']; simpl; intro H; inversion H.
rewrite (Rabs_left1 _ Hr1').
case (Rle_lt_dec 0 x); intro Hx.
{ now apply (Rmult_le_compat _ _ _ _ Hx Hx); rewrite Rmax_Rle; right. }
rewrite <-(Ropp_involutive (x * x)).
rewrite Ropp_mult_distr_l, Ropp_mult_distr_r.
now apply Rmult_le_compat;
  try (now rewrite <-Ropp_0; apply Ropp_le_contravar, Rlt_le);
  rewrite Rmax_Rle; left; apply Ropp_le_contravar.
Qed.

Lemma Fpower_pos_up_correct :
  forall prec x n,
  le_upper (Xreal 0) (F.toX x) ->
  le_upper (Xpower_int (F.toX x) (Zpos n)) (F.toX (Fpower_pos_UP prec x n)).
Proof.
intros prec.
intros x n; revert x; induction n; intros x Hx.
{ simpl.
  generalize (F.mul_UP_correct
                prec x (Fpower_pos_UP prec (F.mul_UP prec x x) n)).
  revert Hx; xreal_tac2; [now simpl|]; intro Hr.
  xreal_tac2; [now xreal_tac2|].
  xreal_tac2; [now simpl|].
  apply Rle_trans.
  rewrite nat_of_P_xI.
  apply (Rmult_le_compat_l _ _ _ Hr); fold (r ^ (2 * Pos.to_nat n))%R.
  rewrite pow_sqr.
  change (_ <= _)%R with (le_upper (Xreal ((r * r) ^ Pos.to_nat n)) (Xreal r0)).
  apply (le_upper_trans _ (Xpower_int (F.toX (F.mul_UP prec x x)) (Z.pos n))).
  { generalize (Xpower_int_correct (Z.pos n) (F.toX (F.mul_UP prec x x))).
    xreal_tac2; (case (Xpower_int _ _); [intros _; exact I|]);
      intros r1' Hr1'; [now simpl|].
    rewrite <-Hr1'.
    apply pow_incr; split; [now apply Rmult_le_pos|].
    change (_ <= _)%R with (le_upper (Xmul (Xreal r) (Xreal r)) (Xreal r2)).
    rewrite <-X, <-X2; apply F.mul_UP_correct. }
  rewrite <-X0; apply IHn.
  apply (le_upper_trans _ (Xmul (Xreal r) (Xreal r)));
    [now apply Rmult_le_pos|].
  rewrite <-X; apply F.mul_UP_correct. }
{ simpl.
  generalize (F.mul_UP_correct prec x x).
  revert Hx; xreal_tac2.
  { intros _.
    xreal_tac2; [|now simpl]; intros _.
    apply (le_upper_trans _ (Xpower_int Xnan (Z.pos n))); [now simpl|].
    now rewrite <-X0; apply IHn; rewrite X0. }
  simpl; intros Hr Hxx.
  apply (le_upper_trans _ (Xpower_int (F.toX (F.mul_UP prec x x)) (Z.pos n))).
  { generalize (Xpower_int_correct (Z.pos n) (F.toX (F.mul_UP prec x x))).
    xreal_tac2; (case (Xpower_int _ _); [intros _; exact I|]);
      intros r1 Hr1; [now simpl|].
    rewrite nat_of_P_xO, pow_sqr, <-Hr1.
    now apply pow_incr; split; [apply Rmult_le_pos|]. }
  apply IHn.
  now revert Hxx; apply le_upper_trans, Rmult_le_pos. }
unfold Xpower_int, Xbind; simpl; case (F.toX x); [exact I|].
now intro x'; rewrite Rmult_1_r; right.
Qed.

Lemma Fpower_pos_dn_correct :
  forall prec x n,
  le_lower' (Xreal 0) (F.toX x) ->
  le_lower' (F.toX (Fpower_pos_DN prec x n)) (Xpower_int (F.toX x) (Zpos n)).
Proof.
intros prec.
assert (Hnan : forall x n,
           F.toX x = Xnan -> F.toX (Fpower_pos_DN prec x n) = Xnan).
{ intros x n; revert x; induction n; intros x Hx; simpl.
  { rewrite F'.cmp_correct, F.zero_correct.
    xreal_tac (F.mul_DN prec x x); simpl; [now apply F.nan_correct|].
    now generalize (F.mul_DN_correct prec x x); rewrite Hx, X. }
  { rewrite F'.cmp_correct, F.zero_correct.
    xreal_tac (F.mul_DN prec x x); simpl; [now apply F.nan_correct|].
    now generalize (F.mul_DN_correct prec x x); rewrite Hx, X. }
  exact Hx. }
intros x n; revert x.
unfold le_lower', Xpower_int.
induction n ; intros x Hx ; simpl.
{ rewrite F'.cmp_correct, F.zero_correct.
  xreal_tac (F.mul_DN prec x x); simpl; [now rewrite F.nan_correct|].
  case Rcompare_spec; intro Hr; try (rewrite F.zero_correct; unfold Xbind).
  { revert Hx; xreal_tac2; [now simpl|]; intro Hx.
    now apply (Rmult_le_pos _ _ Hx), pow_le. }
  { revert Hx; xreal_tac2; [now simpl|]; intro Hx.
    now apply (Rmult_le_pos _ _ Hx), pow_le. }
  xreal_tac2; unfold Xbind.
  generalize (F.mul_DN_correct prec x x); rewrite X.
  xreal_tac2; [now simpl|]; intro Hr'; apply Ropp_le_cancel in Hr'.
  generalize (F.mul_DN_correct
                prec x (Fpower_pos_DN prec (F.mul_DN prec x x) n)).
  rewrite X0, X1.
  xreal_tac2; [now simpl|].
  intro Hr0; apply Ropp_le_cancel in Hr0.
  apply (Rle_trans _ _ _ Hr0), (Rmult_le_compat_l _ _ _ Hx).
  generalize (IHn (F.mul_DN prec x x)); clear IHn; rewrite X; intro IHn.
  specialize (IHn (Rlt_le _ _ Hr)); revert IHn; rewrite X2.
  unfold Xbind, Xpower_int'; intro IHn.
  apply (Rle_trans _ _ _ IHn).
  rewrite Pmult_nat_mult, Nat.mul_comm, pow_sqr.
  now apply pow_incr; split; [left|]. }
{ rewrite F'.cmp_correct, F.zero_correct.
  xreal_tac (F.mul_DN prec x x); simpl; [now rewrite F.nan_correct|].
  case Rcompare_spec; intro Hr; try (rewrite F.zero_correct; unfold Xbind).
  { now revert Hx; xreal_tac2; [now simpl|]; intro Hx; apply pow_le. }
  { now revert Hx; xreal_tac2; [now simpl|]; intro Hx; apply pow_le. }
  revert Hx; xreal_tac2; [now simpl|intro Hr0].
  generalize (IHn (F.mul_DN prec x x)); clear IHn; rewrite X.
  intro IHn; specialize (IHn (Rlt_le _ _ Hr)).
  xreal_tac2.
  revert IHn; unfold Xbind, Xpower_int'; intro IHn.
  apply (Rle_trans _ _ _ IHn).
  rewrite nat_of_P_xO, pow_sqr.
  apply pow_incr; split; [now left|].
  generalize (F.mul_DN_correct prec x x); rewrite X, X0; intro H.
  now apply Ropp_le_cancel in H. }
now xreal_tac2; unfold Xbind; rewrite Rmult_1_r; right.
Qed.

Theorem power_pos_correct :
  forall prec n,
  extension (fun x => Xpower_int x (Zpos n)) (fun x => power_pos prec x n).
Proof.
intros prec n [ | xl xu] [ | x] ; try easy.
unfold contains, convert, power_pos, Xpower_int.
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
rewrite 2!F.neg_correct.
split.
(* .. *)
generalize (Fpower_pos_up_correct prec (F.abs xl) (xI n)).
unfold le_upper.
rewrite F.abs_correct.
xreal_tac (Fpower_pos_UP prec (F.abs xl) n~1).
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
rewrite F.abs_correct.
xreal_tac (Fpower_pos_DN prec (F.abs xu) n~1).
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
rewrite F.abs_correct.
xreal_tac (Fpower_pos_DN prec (F.abs xu) n~0).
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
rewrite F.abs_correct.
xreal_tac (Fpower_pos_UP prec (F.abs xl) n~0).
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
xreal_tac (Fpower_pos_DN prec xl n).
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
xreal_tac (Fpower_pos_UP prec xu n).
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
rewrite F.neg_correct.
generalize (Fpower_pos_up_correct prec (F.abs xl) (xI n)).
unfold le_upper.
rewrite F.abs_correct.
xreal_tac (Fpower_pos_UP prec (F.abs xl) n~1).
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
apply Rle_trans with 0%R.
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
xreal_tac (Fpower_pos_UP prec xu n~1).
easy.
xreal_tac xu ; simpl.
intros H.
now elim H.
intros H.
refine (Rle_trans _ _ _ _ (H _)).
2: apply Hx0.
destruct (Rle_or_lt x 0) as [Hx|Hx].
apply Rle_trans with 0%R.
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
rewrite F.max_correct.
rewrite F.abs_correct.
xreal_tac (Fpower_pos_UP prec (F.max (F.abs xl) xu) n~0).
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
unfold c1.
rewrite F.fromZ_correct by easy.
split ; apply Rle_refl.
apply power_pos_correct.
intros xi x Hx.
generalize (power_pos_correct prec n _ _ Hx).
intros Hp.
generalize (inv_correct prec _ _ Hp).
unfold Xpower_int, Xpower_int', Xinv', Xbind, power_int.
destruct x as [ | x].
easy.
replace (is_zero x) with (is_zero (x ^ nat_of_P n)).
easy.
case (is_zero_spec x) ; intros Zx.
rewrite Zx, pow_i.
apply is_zero_0.
apply lt_O_nat_of_P.
case is_zero_spec ; try easy.
intros H.
elim (pow_nonzero _ _ Zx H).
Qed.

Lemma mask_propagate_l : propagate_l mask.
Proof. intros xi yi; destruct xi; destruct yi; easy. Qed.

Lemma mask_propagate_r : propagate_r mask.
Proof. intros xi yi; destruct xi; destruct yi; easy. Qed.

Lemma add_propagate_l : forall prec, propagate_l (add prec).
Proof. intros prec xi yi; destruct xi; destruct yi; easy. Qed.

Lemma sub_propagate_l : forall prec, propagate_l (sub prec).
Proof. intros prec xi yi; destruct xi; destruct yi; easy. Qed.

Lemma mul_propagate_l : forall prec, propagate_l (mul prec).
Proof. intros prec xi yi; destruct xi; destruct yi; easy. Qed.

Lemma div_propagate_l : forall prec, propagate_l (div prec).
Proof. intros prec xi yi; destruct xi; destruct yi; easy. Qed.

Lemma add_propagate_r : forall prec, propagate_r (add prec).
Proof. intros prec xi yi; destruct xi; destruct yi; easy. Qed.

Lemma sub_propagate_r : forall prec, propagate_r (sub prec).
Proof. intros prec xi yi; destruct xi; destruct yi; easy. Qed.

Lemma mul_propagate_r : forall prec, propagate_r (mul prec).
Proof. intros prec xi yi; destruct xi; destruct yi; easy. Qed.

Lemma div_propagate_r : forall prec, propagate_r (div prec).
Proof. intros prec xi yi; destruct xi; destruct yi; easy. Qed.

Lemma nearbyint_correct :
  forall mode, extension (Xnearbyint mode) (nearbyint mode).
Proof.
intros mode [|xl xu] [|xr] ; try easy.
simpl.
intros [Hl Hu].
rewrite 2!F.nearbyint_correct.
split ; xreal_tac2; simpl.
now apply Rnearbyint_le.
now apply Rnearbyint_le.
Qed.

End FloatInterval.
