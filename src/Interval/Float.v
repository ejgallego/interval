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

Module FloatInterval (F : FloatOps with Definition sensible_format := true) <: IntervalBasicOps with Module F := F.

Module F := F.
Module F' := FloatExt F.

Definition c1 := F.fromZ 1.
Definition cm1 := F.fromZ (-1).
Definition c2 := F.fromZ 2.
Definition p52 := F.PtoP 52.

Definition type := f_interval F.type.
Definition bound_type := F.type.
Definition precision := F.precision.

Definition valid_lb x := F.valid_lb x = true.
Definition valid_ub x := F.valid_ub x = true.
Definition nan := F.nan.
Definition convert_bound := F.toX.
Definition convert (xi : type) :=
  match xi with
  | Inan => Interval.Inan
  | Ibnd l u =>
    if (F.valid_lb l && F.valid_ub u)%bool then Interval.Ibnd (F.toX l) (F.toX u)
    else Interval.Ibnd (Xreal 1) (Xreal 0)
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

Definition singleton b :=
  if andb (F.valid_lb b) (F.valid_ub b) then @Ibnd F.type b b
  else @Inan F.type.

Lemma valid_lb_real :
  forall b, F.toX b = Xreal (proj_val (F.toX b)) -> F.valid_lb b = true.
Proof.
now intros b Hb; rewrite F'.valid_lb_real; [|rewrite F.real_correct, Hb].
Qed.

Lemma valid_ub_real :
  forall b, F.toX b = Xreal (proj_val (F.toX b)) -> F.valid_ub b = true.
Proof.
now intros b Hb; rewrite F'.valid_ub_real; [|rewrite F.real_correct, Hb].
Qed.

Lemma valid_lb_nan : F.valid_lb F.nan = true.
Proof. apply F'.valid_lb_nan. Qed.

Lemma valid_ub_nan : F.valid_ub F.nan = true.
Proof. apply F'.valid_ub_nan. Qed.

Lemma bnd_correct :
  forall l u, valid_lb l -> valid_ub u ->
  convert (bnd l u) = Interval.Ibnd (F.toX l) (F.toX u).
Proof. now intros l u Vl Vu; unfold convert; simpl; rewrite Vl, Vu. Qed.

Lemma singleton_correct :
  forall b,
  contains (convert (singleton b)) (Xreal (proj_val (convert_bound b))).
Proof.
intros b.
unfold singleton, convert, convert_bound.
destruct F.valid_lb eqn:Hl. 2: easy.
destruct F.valid_ub eqn:Hu. 2: easy.
simpl.
rewrite Hl, Hu.
simpl.
destruct F.toX.
repeat split.
split ; apply Rle_refl.
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
rewrite F'.valid_lb_zero, F'.valid_ub_zero.
now rewrite F.zero_correct.
Qed.

Lemma empty_correct :
  forall x, contains (convert empty) x -> False.
Proof.
intros [|x].
{ now simpl; case (_ && _). }
simpl.
unfold c1.
rewrite F.fromZ_correct, F.zero_correct by easy.
case (_ && _); simpl; lra.
Qed.

Lemma real_correct :
  forall xi, real xi = match convert xi with Interval.Inan => false | _ => true end.
Proof. now intros [|xl xu]; [|simpl; case (_ && _)]. Qed.

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
    | Xund =>
      match F.classify yl with
      | Fnan | Fminfty => true
      | Freal | Fpinfty => false
      end
    | Xlt => false
    | _ => true
    end &&
    match F.cmp xu yu with
    | Xund =>
      match F.classify yu with
      | Fnan | Fpinfty => true
      | Freal | Fminfty => false
      end
    | Xgt => false
    | _ => true
    end
  | _, Inan => true
  | Inan, Ibnd _ _ => false
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
      match F.is_nan xl, F.is_nan yl with
      | true, _ => yl
      | false, true => xl
      | false, false => F.max xl yl
      end in
    let u :=
      match F.is_nan xu, F.is_nan yu with
      | true, _ => yu
      | false, true => xu
      | false, false => F.min xu yu
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
    match F.real xl, F.real xu with
    | false, false => F.zero
    | true, false =>
      match F.cmp xl F.zero with
      | Xund | Xlt => F.zero
      | Xeq => c1
      | Xgt => let m := F.mul_UP p52 xl c2 in if F.real m then m else xl
      end
    | false, true =>
      match F.cmp xu F.zero with
      | Xund | Xgt => F.zero
      | Xeq => cm1
      | Xlt => let m := F.mul_DN p52 xu c2 in if F.real m then m else xu
      end
    | true, true => F.midpoint xl xu
    end
  end.

Definition bisect xi :=
  match xi with
  | Inan => (Inan, Inan)
  | Ibnd xl xu =>
    let m := midpoint xi in (Ibnd xl m, Ibnd m xu)
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

Definition mul2 prec xi :=
  match xi with
  | Ibnd xl xu =>
    Ibnd (F.mul_DN prec xl c2) (F.mul_UP prec xu c2)
  | Inan => Inan
  end.

Definition sqrt prec xi :=
  match xi with
  | Ibnd xl xu =>
    match F.cmp xl F.zero with
    | Xgt => Ibnd (F.sqrt_DN prec xl) (F.sqrt_UP prec xu)
    | _ => Ibnd F.zero (F.sqrt_UP prec xu)
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
    if F.real y then
      match F.cmp y F.zero with
      | Xlt => Ibnd (F.mul_DN prec xu y) (F.mul_UP prec xl y)
      | Xeq => Ibnd F.zero F.zero
      | Xgt => Ibnd (F.mul_DN prec xl y) (F.mul_UP prec xu y)
      | Xund => Inan
      end
    else Inan
  | Inan => Inan
  end.

Definition div_mixed_r prec xi y :=
  match xi with
  | Ibnd xl xu =>
    if F.real y then
      match F.cmp y F.zero with
      | Xlt => Ibnd (F.div_DN prec xu y) (F.div_UP prec xl y)
      | Xgt => Ibnd (F.div_DN prec xl y) (F.div_UP prec xu y)
      | _ => Inan
      end
    else Inan
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
      match F.cmp lb F.zero with
      | Xgt => Ibnd lb (F.mul_UP prec xl xl)
      | _ => Ibnd F.zero (F.mul_UP prec xl xl)
      end
    | Xgt =>
      let lb := F.mul_DN prec xl xl in
      match F.cmp lb F.zero with
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
    match F.cmp xx F.zero with
    | Xgt => Fpower_pos_DN prec xx p
    | Xeq | Xlt => F.zero
    | Xund => F.nan
    end
  | xI p =>
    let xx := F.mul_DN prec x x in
    match F.cmp xx F.zero with
    | Xgt => F.mul_DN prec x (Fpower_pos_DN prec xx p)
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
  | Ibnd xl xu => Ibnd (F.nearbyint_DN mode xl) (F.nearbyint_UP mode xu)
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

Ltac xreal_tac3 v :=
  match goal with
  | H: F.toX v = Xreal _ |- _ => rewrite H
  | H: F.toX v = Xnan |- _ => rewrite H
  | _ => xreal_tac v
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
  forall xi : type,
  not_empty (convert xi) ->
  F.toX (lower xi) = Xlower (convert xi).
Proof.
intros [|xl xu].
simpl.
now rewrite F'.nan_correct.
simpl; unfold convert; case (_ && _); [easy|].
intros [x Hx]; revert Hx; simpl; lra.
Qed.

Lemma valid_lb_lower :
  forall xi : type,
  not_empty (convert xi) ->
  valid_lb (lower xi).
Proof.
intros [|l u] [x Hx]; unfold valid_lb; simpl; [now rewrite F'.valid_lb_nan|].
now revert Hx; unfold convert; case F.valid_lb; [|simpl; lra].
Qed.

Lemma upper_correct :
  forall xi : type,
  not_empty (convert xi) ->
  F.toX (upper xi) = Xupper (convert xi).
Proof.
intros [|xl xu].
simpl.
now rewrite F'.nan_correct.
simpl; unfold convert; case (_ && _); [easy|].
intros [x Hx]; revert Hx; simpl; lra.
Qed.

Lemma valid_ub_upper :
  forall xi : type,
  not_empty (convert xi) ->
  valid_ub (upper xi).
Proof.
intros [|l u] [x Hx]; unfold valid_ub; simpl; [now rewrite F'.valid_ub_nan|].
revert Hx; unfold convert.
now case F.valid_ub; rewrite andb_comm; [|simpl; lra].
Qed.

Theorem subset_correct :
  forall xi yi : type,
  subset xi yi = true -> Interval.subset (convert xi) (convert yi).
Proof.
intros xi yi.
case xi ; case yi ; try (simpl ; intros ; try exact I ; discriminate).
{ now intros l u _; simpl; case (_ && _). }
simpl; intros yl yu xl xu.
rewrite !F.cmp_correct, !F.valid_lb_correct, !F.valid_ub_correct.
rewrite andb_true_iff.
intros [H H']; revert H H'.
generalize (F.classify_correct xl); rewrite F.real_correct ;
case (F.classify xl) ;
  [xreal_tac xl; [easy|] | xreal_tac xl; [|easy]..] ; intros _ ;
  ( generalize (F.classify_correct yl); rewrite F.real_correct ;
    case (F.classify yl) ;
      [xreal_tac yl; [easy|] | xreal_tac yl; [|easy]..] ; intros _ ) ;
  ( generalize (F.classify_correct xu); rewrite F.real_correct ;
    case (F.classify xu) ;
      [xreal_tac xu; [easy|] | xreal_tac xu; [|easy]..] ; intros _ ) ;
  ( generalize (F.classify_correct yu); rewrite F.real_correct ;
    case (F.classify yu) ;
      [xreal_tac yu; [easy|] | xreal_tac yu; [|easy]..] ; intros _ ) ;
  simpl ;
  try easy ;
  try match goal with
      | |- _ -> _ -> _ \/ le_lower Xnan _ /\ True => intros _ _; now right
      | |- _ -> _ -> (0 < 1)%R \/ _ => intros _ _; left; exact Rlt_0_1
      end ;
  case Rcompare_spec; intros H1 ; try easy ; intros _ ;
  try ( case Rcompare_spec; intros H2 ; try easy ) ; intros _ ;
  unfold le_lower; simpl ;
  right ; lra.
Qed.

Lemma join_correct :
  forall xi yi v,
  contains (convert xi) v \/ contains (convert yi) v ->
  contains (convert (join xi yi)) v.
Proof.
assert (H1v0 : forall v, ~(1 <= v <= 0)%R).
{ intros v Hf.
  apply (Rlt_irrefl 0), (Rlt_le_trans _ 1); [apply Rlt_0_1|].
  elim Hf; apply Rle_trans. }
intros [|xl xu] [|yl yu] [|v]; simpl;
  try rewrite Hxl, Hxu; try rewrite Hyl, Hyu; simpl; try tauto; [|].
{ now case (_ && _); case (_ && _); intros [H|H]. }
generalize (F.max_correct xu yu).
generalize (F.min_correct xl yl).
generalize (F.real_correct yu) ;
  generalize (F.classify_correct yu) ;
  generalize (F.valid_ub_correct yu) ;
  case (F.classify yu) => -> -> ;
    [xreal_tac yu; [easy|intros _]|xreal_tac yu; [intros _|easy]..] ;
  ( generalize (F.real_correct xu) ;
    generalize (F.classify_correct xu) ;
    generalize (F.valid_ub_correct xu) ;
    case (F.classify xu) => -> -> ;
      [xreal_tac xu; [easy|intros _]|xreal_tac xu; [intros _|easy]..] ) ;
  ( generalize (F.real_correct yl) ;
    generalize (F.classify_correct yl) ;
    generalize (F.valid_lb_correct yl) ;
    case (F.classify yl) => -> -> ;
      [xreal_tac yl; [easy|intros _]|xreal_tac yl; [intros _|easy]..] ) ;
  ( generalize (F.real_correct xl) ;
    generalize (F.classify_correct xl) ;
    generalize (F.valid_lb_correct xl) ;
    case (F.classify xl) => -> -> ;
      [xreal_tac xl; [easy|intros _]|xreal_tac xl; [intros _|easy]..] ) ;
  simpl ;
  intros Hmin Hmax ;
  rewrite ?Hmin, ?Hmax ;
  try ( intro H; exfalso; lra ) ;
  try match type of Hmin with
      | F.classify _ = _ =>
        generalize (F.valid_lb_correct (F.min xl yl)) ;
          rewrite Hmin => ->
      | F.toX _ = Xreal _ =>
        rewrite F'.valid_lb_real; [|now rewrite F.real_correct, Hmin]
      end ;
  try match type of Hmax with
      | F.classify _ = _ =>
        generalize (F.valid_ub_correct (F.max xu yu)) ;
          rewrite Hmax => ->
      | F.toX _ = Xreal _ =>
        rewrite F'.valid_ub_real; [|now rewrite F.real_correct, Hmax]
      end ;
  simpl ;
  try match goal with
      | |- context [ F.valid_lb ?x ] =>
        match goal with
        | H : F.toX x = Xreal _ |- _ =>
          rewrite F'.valid_lb_real; [|now rewrite F.real_correct, H]
        end
      end ;
  try match goal with
      | |- context [ F.valid_ub ?x ] =>
        match goal with
        | H : F.toX x = Xreal _ |- _ =>
          rewrite F'.valid_ub_real; [|now rewrite F.real_correct, H]
        end
      end ;
  simpl ;
  (* no more if valid... at this point *)
  try match goal with
      | |- context [ F.toX (F.min _ _) ] =>
        match type of Hmin with
        | F.classify _ = _ =>
          generalize (F.classify_correct (F.min xl yl)) ;
            rewrite Hmin, F.real_correct ;
            case (F.toX (F.min xl yl)); try easy; intros _
        end
      end ;
  try match goal with
      | |- context [ F.toX (F.max _ _) ] =>
        match type of Hmax with
        | F.classify _ = _ =>
          generalize (F.classify_correct (F.max xu yu)) ;
            rewrite Hmax, F.real_correct ;
            case (F.toX (F.max xu yu)); try easy; intros _
        end
      end ;
  do 2 try match goal with
           | |- context [ F.toX ?x ] =>
             match goal with
             | H : F.toX x = _ |- _ => rewrite H
             end
           end ;
  (* no more match *)
  intro H ;
  split ;
  try exact I ;
  destruct H ;
  try ( exfalso ; lra ) ;
  try match goal with
      | |- context [ Rmin ?x ?y ] =>
        generalize (Rmin_l x y) ;
          generalize (Rmin_r x y) ;
          lra
      end ;
  try match goal with
      | |- context [ Rmax ?x ?y ] =>
        generalize (Rmax_l x y) ;
          generalize (Rmax_r x y) ;
          lra
      end ;
  easy.
Qed.

Theorem meet_correct :
  forall xi yi v,
  contains (convert xi) v -> contains (convert yi) v ->
  contains (convert (meet xi yi)) v.
Proof.
intros [|xl xu] [|yl yu] [|v] ; simpl ; trivial; [now case (_ && _)|].
case_eq (F.valid_lb xl); [|intros _ [H0 H1]; exfalso; lra].
case_eq (F.valid_ub xu); [|intros _ _ [H0 H1]; exfalso; lra].
intros Vxu Vxl.
case_eq (F.valid_lb yl); [|intros _ _ [H0 H1]; exfalso; lra].
case_eq (F.valid_ub yu); [|intros _ _ _ [H0 H1]; exfalso; lra].
intros Vyu Vyl.
intros (Hxl, Hxu) (Hyl, Hyu).
simpl.
generalize (F.max_correct xl yl).
generalize (F.min_correct xu yu).
generalize (F.real_correct yu) ;
  generalize (F.is_nan_correct yu) ;
  generalize (F.classify_correct yu) ;
  generalize Vyu; rewrite F.valid_ub_correct ;
  case (F.classify yu); try easy; intros _ H H'; rewrite H, H'; clear H H' ;
    [xreal_tac yu; [easy|intros _]|xreal_tac yu; [intros _|easy]..] ;
  ( generalize (F.real_correct xu) ;
    generalize (F.is_nan_correct xu) ;
    generalize (F.classify_correct xu) ;
    generalize Vxu; rewrite F.valid_ub_correct ;
    case (F.classify xu); try easy; intros _ H H'; rewrite H, H'; clear H H' ;
      [xreal_tac xu; [easy|intros _]|xreal_tac xu; [intros _|easy]..] ) ;
  ( generalize (F.real_correct yl) ;
    generalize (F.is_nan_correct yl) ;
    generalize (F.classify_correct yl) ;
    generalize Vyl; rewrite F.valid_lb_correct ;
    case (F.classify yl); try easy; intros _ H H'; rewrite H, H'; clear H H' ;
      [xreal_tac yl; [easy|intros _]|xreal_tac yl; [intros _|easy]..] ) ;
  ( generalize (F.real_correct xl) ;
    generalize (F.is_nan_correct xl) ;
    generalize (F.classify_correct xl) ;
    generalize Vxl; rewrite F.valid_lb_correct ;
    case (F.classify xl); try easy; intros _ H H'; rewrite H, H'; clear H H' ;
    [xreal_tac xl; [easy|intros _]|xreal_tac xl; [intros _|easy]..] ) ;
  simpl ;
  intros Hmin Hmax ;
  rewrite ?Hmin, ?Hmax, ?Vxu, ?Vxl, ?Vyu, ?Vyl ;
  try match type of Hmin with
      | F.toX _ = Xreal _ =>
        rewrite F'.valid_ub_real; [|now rewrite F.real_correct, Hmin]
      end ;
  try match type of Hmax with
      | F.toX _ = Xreal _ =>
        rewrite F'.valid_lb_real; [|now rewrite F.real_correct, Hmax]
      end ;
  simpl ;
  (* no more if valid... at this point *)
  do 2 try match goal with
           | |- context [ F.toX ?x ] =>
             match goal with
             | H : F.toX x = _ |- _ => rewrite H
             end
           end ;
  (* no more match *)
  split ;
  try exact I ;
  try match goal with
      | |- (?z <= Rmin ?x ?y)%R =>
        generalize (Rmin_glb x y z) ; lra
      end ;
  try match goal with
      | |- (Rmax ?x ?y <= ?z)%R =>
        generalize (Rmax_lub x y z) ; lra
      end ;
  easy.
Qed.

Theorem meet_correct' :
  forall xi yi v,
  contains (convert (meet xi yi)) v ->
  contains (convert xi) v /\ contains (convert yi) v.
Proof.
intros [|xl xu] [|yl yu] v H ; try easy.
destruct v as [|v]; revert H; simpl; [now case (_ && _)|].
assert (HRmin: forall p q, (v <= Rmin p q)%R -> (v <= p /\ v <= q)%R).
  intros p q H.
  unfold Rmin in H.
  destruct Rle_dec as [H'|H'] ; lra.
assert (HRmax: forall p q, (Rmax p q <= v)%R -> (p <= v /\ q <= v)%R).
  intros p q H.
  unfold Rmax in H.
  destruct Rle_dec as [H'|H'] ; lra.
generalize (F.max_correct xl yl).
generalize (F.min_correct xu yu).
generalize (F.real_correct yu) ;
  generalize (F.is_nan_correct yu) ;
  generalize (F.classify_correct yu) ;
  generalize (F.valid_ub_correct yu) ;
  ( case (F.classify yu) ; intros Vyu H H'; rewrite H, H'; clear H H' ) ;
    [xreal_tac yu; [easy|intros _]|xreal_tac yu; [intros _|easy]..] ;
  ( generalize (F.real_correct xu) ;
    generalize (F.is_nan_correct xu) ;
    generalize (F.classify_correct xu) ;
    generalize (F.valid_ub_correct xu) ;
    ( case (F.classify xu) ; intros Vxu H H'; rewrite H, H'; clear H H' ) ;
      [xreal_tac xu; [easy|intros _]|xreal_tac xu; [intros _|easy]..] ) ;
  ( generalize (F.real_correct yl) ;
    generalize (F.is_nan_correct yl) ;
    generalize (F.classify_correct yl) ;
    generalize (F.valid_lb_correct yl) ;
    ( case (F.classify yl) ; intros Vyl H H'; rewrite H, H'; clear H H' ) ;
      [xreal_tac yl; [easy|intros _]|xreal_tac yl; [intros _|easy]..] ) ;
  ( generalize (F.real_correct xl) ;
    generalize (F.is_nan_correct xl) ;
    generalize (F.classify_correct xl) ;
    generalize (F.valid_lb_correct xl) ;
    ( case (F.classify xl) ; intros Vxl H H'; rewrite H, H'; clear H H' ) ;
      [xreal_tac xl; [easy|intros _]|xreal_tac xl; [intros _|easy]..] ) ;
  simpl ;
  intros Hmin Hmax ;
  rewrite ?Hmin, ?Hmax, ?Vxu, ?Vxl, ?Vyu, ?Vyl ;
  try match type of Hmin with
      | F.toX _ = Xreal _ =>
        rewrite F'.valid_ub_real; [|now rewrite F.real_correct, Hmin]
      | F.classify ?m = _ =>
        generalize (F.valid_ub_correct m) ; rewrite Hmin => ->
      end ;
  try match type of Hmax with
      | F.toX _ = Xreal _ =>
        rewrite F'.valid_lb_real; [|now rewrite F.real_correct, Hmax]
      | F.classify ?m = _ =>
        generalize (F.valid_lb_correct m) ; rewrite Hmax => ->
      end ;
  simpl ;
  (* no more if valid... at this point *)
  do 2 try match goal with
           | |- context [ F.toX ?x ] =>
             match goal with
             | H : F.toX x = _ |- _ => rewrite H
             end
           end ;
  (* no more match *)
  intros [Hl Hu] ;
  try match type of Hl with
      | (Rmax ?x ?y <= _)%R => apply (HRmax x y) in Hl
      end ;
  try match type of Hu with
      | (_ <= Rmin ?x ?y)%R => apply (HRmin x y) in Hu
      end ;
  lra.
Qed.

Definition bounded_prop xi :=
  not_empty (convert xi) ->
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
{ unfold bounded_prop, convert; simpl; case (_ && _); [easy|].
  intros [x Hx]; revert Hx; simpl; lra. }
intros s m e; case (FtoX _); [now simpl|]; intros r _; split; [now simpl|].
unfold bounded_prop, convert; simpl; case (_ && _); [easy|].
intros [x Hx]; revert Hx; simpl; lra.
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
{ unfold bounded_prop, convert; simpl; case (_ && _); [easy|].
  intros [x Hx]; revert Hx; simpl; lra. }
intros s m e; case (FtoX _); [now simpl|]; intros r _; split; [now simpl|].
unfold bounded_prop, convert; simpl; case (_ && _); [easy|].
intros [x Hx]; revert Hx; simpl; lra.
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
assert (H1v0 : forall v, ~(1 <= v <= 0)%R).
{ intros v Hf.
  apply (Rlt_irrefl 0), (Rlt_le_trans _ 1); [apply Rlt_0_1|].
  elim Hf; apply Rle_trans. }
intros [|xl xu] x y; simpl; [now simpl|].
case_eq (F.valid_lb xl); intro Vxl; [|now intro H; destruct (H1v0 y)].
case_eq (F.valid_ub xu); intro Vxu; [|now intro H; destruct (H1v0 y)].
intros (Hyl, Hyu) Hx; rewrite F'.valid_lb_nan; split.
{ now rewrite F'.nan_correct. }
now revert Hyu; xreal_tac xu; [now simpl|]; apply Rle_trans.
Qed.

Theorem upper_extent_correct :
  forall xi x y,
  contains (convert xi) (Xreal y) ->
  (y <= x)%R ->
  contains (convert (upper_extent xi)) (Xreal x).
Proof.
assert (H1v0 : forall v, ~(1 <= v <= 0)%R).
{ intros v Hf.
  apply (Rlt_irrefl 0), (Rlt_le_trans _ 1); [apply Rlt_0_1|].
  elim Hf; apply Rle_trans. }
intros [|xl xu] x y; simpl; [now simpl|].
case_eq (F.valid_lb xl); intro Vxl; [|now intro H; destruct (H1v0 y)].
case_eq (F.valid_ub xu); intro Vxu; [|now intro H; destruct (H1v0 y)].
intros (Hxl, Hxu) Hx; rewrite F'.valid_ub_nan; split.
{ now revert Hxl; xreal_tac xl; [now simpl|];
    intro Hxl; apply (Rle_trans _ y). }
now rewrite F'.nan_correct.
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
unfold convert at 1.
case F.valid_lb; simpl; [|lra].
case F.valid_ub; simpl; [|lra].
intros [H _].
simpl.
rewrite F.real_correct.
case_eq (F.toX xl).
intros _ H'.
now apply empty_correct in H'.
intros l Hl.
unfold convert.
rewrite F'.valid_lb_nan; simpl.
case F.valid_ub; [|simpl; lra].
intros [_ H'].
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
unfold convert at 1.
case F.valid_lb; simpl; [|lra].
case F.valid_ub; simpl; [|lra].
intros [_ H].
simpl.
rewrite F.real_correct.
case_eq (F.toX xu).
intros _ H'.
now apply empty_correct in H'.
intros u Hu.
unfold convert.
rewrite F'.valid_ub_nan; simpl.
case F.valid_lb; [|simpl; lra].
intros [H' _].
rewrite Hu in H, H'.
now apply Rle_trans with u.
Qed.

Theorem whole_correct :
  forall x,
  contains (convert whole) (Xreal x).
Proof.
intros x.
simpl.
rewrite F'.nan_correct.
now rewrite F'.valid_lb_nan, F'.valid_ub_nan.
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
assert (H1v0 : forall v, ~(1 <= v <= 0)%R).
{ intros v Hf.
  apply (Rlt_irrefl 0), (Rlt_le_trans _ 1); [apply Rlt_0_1|].
  elim Hf; apply Rle_trans. }
intros xl xu x; simpl.
case_eq (F.valid_lb xl); intro Vxl; [|now intro H; destruct (H1v0 x)].
case_eq (F.valid_ub xu); intro Vxu; [|now intro H; destruct (H1v0 x)].
simpl.
unfold sign_large_.
rewrite 2!F.cmp_correct.
rewrite F.zero_correct, F'.classify_zero.
generalize Vxl ; rewrite F.valid_lb_correct ;
generalize (F.classify_correct xl) ; rewrite F.real_correct ;
case_eq (F.classify xl); intro Cxl ; [..|easy] ;
  [case_eq (F.toX xl); [easy|] ; intros rxl Hrxl _
  |case_eq (F.toX xl); [|easy] ; intros Hrxl _..] ;
  ( generalize Vxu ; rewrite F.valid_ub_correct ;
    generalize (F.classify_correct xu) ; rewrite F.real_correct ;
    case_eq (F.classify xu); intro Cxu ; [..|easy|] ;
      [case_eq (F.toX xu); [easy|] ; intros rxu Hrxu _
      |case_eq (F.toX xu); [|easy] ; intros Hrxu _..] ) ;
  intros  _ _ [Hxl Hxu] ;
  unfold Xcmp ;
  try ( case (Rcompare_spec rxl 0) ; intros Hrxl0 ) ;
  try ( case (Rcompare_spec rxu 0) ; intros Hrxu0 ) ;
  rewrite ?Hrxl0, ?Hrxu0 ;
  ( split; [lra|] ) ;
  try ( easy || lra ) ;
  ( split ; [try ( exact I || lra )|] ) ;
  try ( now exists 0%R; split; [|lra] ) ;
  try ( now exists rxu; split; [|lra] ) ;
  try ( now exists rxl; split; [|lra] ).
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
case (sign_large_ xl xu);
  intro H; try exact I;
    (intros [|x]; [try easy; try now simpl; case (_ && _)|]); intro H'; [| |].
{ now rewrite (proj1 (H _ H')). }
{ now split; simpl; [|elim (H _ H')]. }
now split; simpl; [|elim (H _ H')].
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
assert (H1v0 : forall v, ~(1 <= v <= 0)%R).
{ intros v Hf.
  apply (Rlt_irrefl 0), (Rlt_le_trans _ 1); [apply Rlt_0_1|].
  elim Hf; apply Rle_trans. }
intros xl xu x; simpl.
case_eq (F.valid_lb xl); intro Vxl; [|now intro H; destruct (H1v0 x)].
case_eq (F.valid_ub xu); intro Vxu; [|now intro H; destruct (H1v0 x)].
unfold sign_strict_.
rewrite 2!F.cmp_correct, F.zero_correct, F'.classify_zero.
generalize Vxl ; rewrite F.valid_lb_correct ;
generalize (F.classify_correct xl) ; rewrite F.real_correct ;
case_eq (F.classify xl); [..|easy]; intro Cxl ;
  [case_eq (F.toX xl); [easy|]; intros rxl|case_eq (F.toX xl); [|easy]..] ;
  intros Hrxl  _ _ ;
  ( generalize Vxu ; rewrite F.valid_ub_correct ;
    generalize (F.classify_correct xu) ; rewrite F.real_correct ;
    case_eq (F.classify xu); [..|easy|]; intro Cxu ;
    [case_eq (F.toX xu); [easy|]; intros rxu|case_eq (F.toX xu); [|easy]..] ;
    intros Hrxu _ _ ) ;
  intros [Hxl Hxu] ;
  unfold Xcmp ;
  try ( case Rcompare_spec; intros H1 ; try easy ) ;
  try ( case Rcompare_spec; intros H2 ; try easy ) ;
  try lra ;
  ( split ; [try lra|] ) ;
  ( split ; [try lra|] ) ;
  rewrite ?H1, ?H2 ; try easy ;
  try ( now exists rxu ) ;
  try ( now exists rxl ).
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
case (sign_strict_ xl xu);
  intro H; try exact I;
    (intros [|x]; [try easy; try now simpl; case (_ && _)|]); intro H'; [| |].
{ now rewrite (proj1 (H _ H')). }
{ now split; simpl; [|elim (H _ H')]. }
now split; simpl; [|elim (H _ H')].
Qed.

Theorem fromZ_small_correct :
  forall v,
  (Z.abs v <= 256)%Z ->
  contains (convert (fromZ_small v)) (Xreal (IZR v)).
Proof.
intros.
simpl.
rewrite F'.valid_lb_real, F'.valid_ub_real by now rewrite F.real_correct, F.fromZ_correct.
rewrite F.fromZ_correct by easy.
split ; apply Rle_refl.
Qed.

Theorem fromZ_correct :
  forall prec v,
  contains (convert (fromZ prec v)) (Xreal (IZR v)).
Proof.
intros.
simpl.
destruct (F.fromZ_DN_correct prec v) as [Hlv Lv].
destruct (F.fromZ_UP_correct prec v) as [Huv Uv].
rewrite Hlv, Huv.
now apply le_contains.
Qed.

Theorem midpoint_correct :
  forall xi,
  not_empty (convert xi) ->
  F.toX (midpoint xi) = Xreal (proj_val (F.toX (midpoint xi))) /\
  contains (convert xi) (F.toX (midpoint xi)).
Proof.
intros [|xl xu].
{ intros _.
  refine (conj _ I).
  simpl.
  now rewrite F.zero_correct. }
intros (x, Hx).
unfold midpoint, c1, cm1, c2.
destruct (F.real xl) eqn:Rl.
- destruct (F.real xu) eqn:Ru.
  + revert Hx.
    simpl.
    rewrite F'.valid_lb_real, F'.valid_ub_real by easy.
    rewrite 2!F'.real_correct by easy.
    intros [Hxl Hxu].
    destruct (F.midpoint_correct _ _ eq_refl Rl Ru (Rle_trans _ _ _ Hxl Hxu)) as [Hm1 Hm2].
    simpl.
    now rewrite F'.real_correct.
  + assert (Hx': (proj_val (F.toX xl) <= x)%R).
    { revert Hx.
      simpl.
      case andb ; simpl.
      now rewrite F'.real_correct.
      lra. }
    assert (Hz: forall z, (F.toR xl <= z)%R -> contains (convert (Ibnd xl xu)) (Xreal z)).
    { intros z Hz.
      revert Hx.
      simpl.
      case andb ; simpl.
      intros _.
      split.
      now rewrite F'.real_correct.
      now rewrite F'.real_correct_false.
      lra. }
    rewrite F.cmp_correct.
    rewrite F'.classify_real by easy.
    rewrite F'.classify_real by now rewrite F.real_correct, F.zero_correct.
    rewrite (F'.real_correct xl) by easy.
    rewrite F.zero_correct.
    simpl Xcmp.
    case Rcompare_spec ; intros Hl.
    * rewrite F.zero_correct.
      apply (conj eq_refl).
      apply Hz.
      now apply Rlt_le.
    * rewrite F.fromZ_correct by easy.
      apply (conj eq_refl).
      apply Hz.
      rewrite Hl.
      apply Rle_0_1.
    * destruct (F.mul_UP_correct p52 xl (F.fromZ 2)) as [Hm1 Hm2].
      { left.
        unfold F.is_non_neg.
        repeat split.
        now apply F'.valid_ub_real.
        rewrite F'.real_correct by easy.
        now apply Rlt_le.
        apply F'.valid_ub_real.
        now rewrite F.real_correct, F.fromZ_correct.
        rewrite F.fromZ_correct by easy.
        now apply IZR_le. }
      destruct (F.real (F.mul_UP p52 xl (F.fromZ 2))) eqn:Rp.
      split.
      now apply F'.real_correct.
      rewrite F'.real_correct by easy.
      apply Hz.
      revert Hm2.
      unfold le_upper, F.toR.
      rewrite F'.real_correct by easy.
      rewrite F'.real_correct by easy.
      rewrite F.fromZ_correct by easy.
      simpl.
      lra.
      split.
      now apply F'.real_correct.
      rewrite F'.real_correct by easy.
      apply Hz.
      apply Rle_refl.
- destruct (F.real xu) eqn:Ru.
  + assert (Hx': (x <= proj_val (F.toX xu))%R).
    { revert Hx.
      simpl.
      case andb ; simpl.
      now rewrite (F'.real_correct xu).
      lra. }
    assert (Hz: forall z, (z <= F.toR xu)%R -> contains (convert (Ibnd xl xu)) (Xreal z)).
    { intros z Hz.
      revert Hx.
      simpl.
      case andb ; simpl.
      intros _.
      split.
      now rewrite F'.real_correct_false.
      now rewrite F'.real_correct.
      lra. }
    rewrite F.cmp_correct.
    rewrite F'.classify_real by easy.
    rewrite F'.classify_real by now rewrite F.real_correct, F.zero_correct.
    rewrite (F'.real_correct xu) by easy.
    rewrite F.zero_correct.
    simpl Xcmp.
    case Rcompare_spec ; intros Hu.
    * destruct (F.mul_DN_correct p52 xu (F.fromZ 2)) as [Hm1 Hm2].
      { right. right. right.
        unfold F.is_non_pos, F.is_non_neg.
        repeat split.
        now apply F'.valid_lb_real.
        rewrite F'.real_correct by easy.
        now apply Rlt_le.
        apply F'.valid_ub_real.
        now rewrite F.real_correct, F.fromZ_correct.
        rewrite F.fromZ_correct by easy.
        now apply IZR_le. }
      destruct (F.real (F.mul_DN p52 xu (F.fromZ 2))) eqn:Rp.
      split.
      now apply F'.real_correct.
      rewrite F'.real_correct by easy.
      apply Hz.
      revert Hm2.
      unfold le_lower, le_upper, F.toR.
      unfold Xneg.
      rewrite F'.real_correct by easy.
      rewrite F'.real_correct by easy.
      rewrite F.fromZ_correct by easy.
      simpl.
      lra.
      split.
      now apply F'.real_correct.
      rewrite F'.real_correct by easy.
      apply Hz.
      apply Rle_refl.
    * rewrite F.fromZ_correct by easy.
      apply (conj eq_refl).
      apply Hz.
      rewrite Hu.
      now apply IZR_le.
    * rewrite F.zero_correct.
      apply (conj eq_refl).
      apply Hz.
      now apply Rlt_le.
  + rewrite F.zero_correct.
    apply (conj eq_refl).
    revert Hx.
    simpl.
    case andb ; simpl.
    intros _.
    now rewrite 2!F'.real_correct_false.
    lra.
Qed.

Theorem bisect_correct :
  forall xi x,
  contains (convert xi) x ->
  contains (convert (fst (bisect xi))) x \/ contains (convert (snd (bisect xi))) x.
Proof.
intros xi x Hx.
destruct (midpoint_correct xi) as [H1 H2].
{ apply not_empty_contains with (1 := Hx). }
unfold bisect.
set (m := midpoint xi).
fold m in H1, H2.
clearbody m.
destruct xi as [|xl xu].
now left.
revert Hx.
simpl.
destruct x as [|x].
  now case (_ && _).
destruct (F.valid_lb xl).
2: simpl ; lra.
destruct (F.valid_ub xu).
2: simpl ; lra.
intros [H3 H4].
rewrite valid_lb_real by easy.
rewrite valid_ub_real by easy.
simpl.
rewrite H1.
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
intros xi [|yl yu] x [|y] Hx Hy; try easy.
now revert Hy; simpl; case (_ && _).
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
intros [ | xl xu] [ | x] ; simpl ; trivial; [now case (_ && _)|].
case_eq (F.valid_lb xl); [|intros _ [H0 H1]; exfalso; lra].
case_eq (F.valid_ub xu); [|intros _ _ [H0 H1]; exfalso; lra].
intros Vu Vl (Hxl, Hxu).
rewrite F'.valid_lb_neg, F'.valid_ub_neg, Vu, Vl.
rewrite !F'.neg_correct.
now split ;
  [ xreal_tac xu | xreal_tac xl ] ;
  apply Ropp_le_contravar.
Qed.

Theorem neg_correct' :
  forall xi x,
  contains (convert (neg xi)) (Xneg x) ->
  contains (convert xi) x.
Proof.
intros [|xl xu] [|x] ; try easy ;
  unfold convert ; simpl ;
  rewrite F'.valid_lb_neg, F'.valid_ub_neg, !F'.neg_correct ;
  [now case (_ && _)|].
rewrite andb_comm; case (_ && _); [|simpl; lra].
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
intros [ | xl xu] [ | x] Hx ; trivial; [ | ].
{ now revert Hx; unfold convert; case (_ && _). }
simpl.
generalize (sign_large_correct_ _ _ _ Hx).
case (sign_large_ xl xu) ; intros.
{ (* zero *)
  rewrite (proj1 H).
  rewrite Rabs_R0.
  simpl.
  rewrite F'.valid_lb_zero, F'.valid_ub_zero.
  rewrite F.zero_correct.
  split ; exact (Rle_refl R0). }
{ (* negative *)
  rewrite (Rabs_left1 _ (proj1 H)).
  exact (neg_correct _ _ Hx). }
{ (* positive *)
  rewrite (Rabs_right _ (Rle_ge _ _ (proj1 H))).
  exact Hx. }
(* both *)
clear H.
simpl.
rewrite F.zero_correct.
rewrite F'.valid_lb_zero.
assert (Vxu : F.valid_ub xu = true).
{ revert Hx; unfold convert; case (F.valid_ub xu); [easy|].
  rewrite andb_comm; intros (H0, H1); lra. }
revert Hx; unfold convert; rewrite Vxu.
case_eq (F.valid_lb xl); [|now intros _ [H0 H1]; exfalso; lra].
intros Vxl [Hxl Hxu].
generalize (F.max_correct (F.neg xl) xu).
generalize (F.real_correct xu) ;
  generalize (F.classify_correct xu) ;
  generalize Vxu; rewrite F.valid_ub_correct ;
  case (F.classify xu); try easy; intros _ H; rewrite H; clear H ;
    [xreal_tac xu; [easy|intros _]|xreal_tac xu; [intros _|easy]..] ;
  ( generalize (F.real_correct (F.neg xl)) ;
    generalize (F.classify_correct (F.neg xl)) ;
    generalize Vxl ;
    rewrite F'.neg_correct, <-F'.valid_ub_neg, F.valid_ub_correct ;
    ( case (F.classify (F.neg xl)); try easy; intros _ H; rewrite H; clear H ) ;
      [xreal_tac xl; [easy|intros _]|xreal_tac xl; [intros _|easy]..] ) ;
  simpl ;
  intro Hmax ;
  rewrite ?Hmax ;
  try match type of Hmax with
      | F.toX _ = Xreal _ =>
        rewrite F'.valid_ub_real; [|now rewrite F.real_correct, Hmax]
      | F.classify ?m = _ =>
        generalize (F.valid_ub_correct m) ; rewrite Hmax => ->
      end ;
  (* no more if valid... at this point *)
  ( split; [now apply Rabs_pos|] ) ;
  [|now generalize (F.classify_correct (F.max (F.neg xl) xu)) ; rewrite Hmax ;
    rewrite F.real_correct ; xreal_tac2..].
(* - upper *)
apply <- Rmax_Rle.
unfold Rabs.
destruct (Rcase_abs x) as [H|H].
{ left.
  apply Ropp_le_contravar.
  exact Hxl. }
right.
exact Hxu.
Qed.

Theorem abs_ge_0 :
  forall xi, not_empty (convert xi) -> convert xi <> Interval.Inan ->
  le_lower' (Xreal 0) (F.toX (lower (abs xi))).
Proof.
intros [|xl xu].
{ now intros H; elim H. }
intros [x Hx] _; revert Hx.
unfold convert.
case_eq (F.valid_lb xl); intro Vxl; [|intros [H0 H1]; lra].
case_eq (F.valid_ub xu); intro Vxu; [|intros [H0 H1]; lra].
intros [Hxl Hxu].
simpl.
unfold sign_large_.
rewrite 2!F.cmp_correct, F.zero_correct, F'.classify_zero.
generalize Vxl Vxu.
rewrite F.valid_lb_correct, F.valid_ub_correct.
generalize (F.classify_correct xl) ; rewrite F.real_correct ;
case_eq (F.classify xl) ; intros Cxl ; [..|easy] ;
  [case_eq (F.toX xl); [easy|]; intros rxl Hrxl _ _
  |case_eq (F.toX xl); [|easy]; intros Hrxl _ _..] ;
  ( generalize (F.classify_correct xu) ; rewrite F.real_correct ;
    case_eq (F.classify xu) ; intros Cxu ; [..|easy|] ;
    [case_eq (F.toX xu); [easy|]; intros rxu Hrxu _ _
    |case_eq (F.toX xu); [|easy]; intros Hrxu _ _..] ) ;
  unfold Xcmp ;
  try ( case (Rcompare_spec rxl 0) ; intros Hrxl0 ) ;
  try ( case (Rcompare_spec rxu 0) ; intros Hrxu0 ) ;
  simpl ;
  rewrite ?F'.neg_correct, ?F.zero_correct, ?Hrxl, ?Hrxu ;
  simpl ;
  lra.
Qed.

Theorem abs_ge_0' :
  forall xi, not_empty (convert xi) ->
  (0 <= proj_val (F.toX (lower (abs xi))))%R.
Proof.
intros [|xl xu] Hne.
simpl.
rewrite F'.nan_correct.
apply Rle_refl.
refine (_ (abs_ge_0 (Ibnd xl xu) Hne _)).
2: now unfold convert; case (_ && _).
simpl.
now case F.toX.
Qed.

Theorem mul2_correct :
  forall prec xi x,
  contains (convert xi) x ->
  contains (convert (mul2 prec xi)) (Xmul x (Xreal 2)).
Proof.
intros prec [ | xl xu].
easy.
intros [|x]; unfold convert; [now case (_ && _)|].
case_eq (F.valid_lb xl); [|intros _ [H0 H1]; exfalso; lra].
case_eq (F.valid_ub xu); [|intros _ _ [H0 H1]; exfalso; lra].
intros Vxu Vxl [Hxl Hxu].
simpl.
unfold c2.
elim (F.mul_DN_correct prec xl (F.fromZ 2)); [intros Vl Hl; rewrite Vl|].
{ elim (F.mul_UP_correct prec xu (F.fromZ 2)); [intros Vu Hu; rewrite Vu|].
  { split.
    { xreal_tac2.
      revert Hl; rewrite F.fromZ_correct by easy.
      unfold le_lower, le_upper; simpl.
      now xreal_tac2; simpl; [|lra]. }
    xreal_tac2.
    revert Hu; rewrite F.fromZ_correct by easy.
    unfold le_upper.
    now xreal_tac2; simpl; [|lra]. }
  unfold F.is_non_neg, F.is_non_pos,F.is_non_neg_real, F.is_non_pos_real.
  rewrite Vxu.
  rewrite F'.valid_ub_real;
    [|now rewrite F.real_correct, F.fromZ_correct].
  rewrite F.fromZ_correct; [|easy..].
  xreal_tac2; [now left; repeat split; lra|].
  case (Rlt_or_le 0 r); intro Hr.
  { left; repeat split; lra. }
  do 2 right; left; lra. }
unfold F.is_non_neg, F.is_non_pos,F.is_non_neg_real, F.is_non_pos_real.
rewrite Vxl.
rewrite (F'.valid_ub_real (F.fromZ 2));
  [|now rewrite F.real_correct, F.fromZ_correct].
rewrite F.fromZ_correct by easy.
xreal_tac2; [now do 3 right; repeat split; lra|].
case (Rlt_or_le 0 r); intro Hr.
{ left; repeat split; lra. }
do 3 right; repeat split; lra.
Qed.

Theorem add_correct :
  forall prec,
  extension_2 Xadd (add prec).
Proof.
intros prec [ | xl xu] [ | yl yu] [ | x] [ | y] ; trivial;
  [| |intros _|]; [now unfold convert; case (_ && _)..|].
unfold convert.
case_eq (F.valid_lb xl); [|intros _ [H0 H1]; exfalso; lra].
case_eq (F.valid_ub xu); [|intros _ _ [H0 H1]; exfalso; lra].
intros Vxu Vxl.
case_eq (F.valid_lb yl); [|intros _ _ [H0 H1]; exfalso; lra].
case_eq (F.valid_ub yu); [|intros _ _ _ [H0 H1]; exfalso; lra].
intros Vyu Vyl.
intros (Hxl, Hxu) (Hyl, Hyu).
simpl.
elim (F.add_DN_correct prec xl yl); [|easy..]; intros H _; rewrite H; clear H.
elim (F.add_UP_correct prec xu yu); [|easy..]; intros H _; rewrite H; clear H.
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
intros prec [ | xl xu] [ | yl yu] [ | x] [ | y] ; trivial;
  [| |intros _|]; [now unfold convert; case (_ && _)..|].
unfold convert.
case_eq (F.valid_lb xl); [|intros _ [H0 H1]; exfalso; lra].
case_eq (F.valid_ub xu); [|intros _ _ [H0 H1]; exfalso; lra].
intros Vxu Vxl.
case_eq (F.valid_lb yl); [|intros _ _ [H0 H1]; exfalso; lra].
case_eq (F.valid_ub yu); [|intros _ _ _ [H0 H1]; exfalso; lra].
intros Vyu Vyl.
intros (Hxl, Hxu) (Hyl, Hyu).
simpl.
elim (F.sub_DN_correct prec xl yu); [|easy..]; intros H _; rewrite H; clear H.
elim (F.sub_UP_correct prec xu yl); [|easy..]; intros H _; rewrite H; clear H.
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
intros prec [ | xl xu] [ | x]; trivial; [now unfold convert; case (_ && _)|].
unfold convert.
case_eq (F.valid_lb xl); [|intros _ [H0 H1]; exfalso; lra].
case_eq (F.valid_ub xu); [|intros _ _ [H0 H1]; exfalso; lra].
intros Vxu Vxl.
intros [Hxl Hxu].
elim (F.sqrt_UP_correct prec xu); intros Vsuxu Hsuxu.
unfold sqrt; rewrite F.cmp_correct, F.zero_correct, F'.classify_zero.
generalize Vxl; rewrite F.valid_lb_correct.
generalize (F.classify_correct xl); rewrite F.real_correct.
case_eq (F.toX xl); [|intro rl]; intro Hrl.
{ now case F.classify; [easy|..|easy]; intros _ _;
    (rewrite F'.valid_lb_zero, Vsuxu; split;
     [rewrite F.zero_correct; apply sqrt_pos|
      revert Hxu Hsuxu;
      case (F.toX (F.sqrt_UP _ _)); [easy|intro rsxu];
      case F.toX; [easy|intro rxu];
      intro Hx; apply Rle_trans, sqrt_le_1_alt]). }
(* xl real *)
revert Hxl.
rewrite Hrl.
intros Hxl.
case F.classify; [|easy..]; intros _ _.
unfold Xsqrt'.
unfold Xcmp; case Rcompare_spec; intro Hrl0; rewrite Vsuxu;
  [rewrite F'.valid_lb_zero..|rewrite Bool.andb_comm]; simpl;
    [now split; [rewrite F.zero_correct; apply sqrt_pos|];
     revert Hxu Hsuxu;
     case (F.toX (F.sqrt_UP _ _)); [easy|intro rsuxu];
     case F.toX; [easy|intros rxu Hrxu];
     apply Rle_trans, sqrt_le_1_alt..|].
(* xl positive *)
elim (F.sqrt_DN_correct prec _ Vxl).
intros Vslxl Hslxl.
rewrite Vslxl.
apply le_contains.
{ apply (le_lower_trans _ _ _ Hslxl).
  rewrite Hrl.
  simpl; unfold Xsqrt'.
  now apply Ropp_le_contravar, sqrt_le_1_alt. }
revert Hsuxu.
apply le_upper_trans.
revert Hxu; xreal_tac2; intro Hxu; [exact I|].
simpl; unfold Xsqrt'.
now apply sqrt_le_1_alt.
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
intros prec yf [|xl xu] [|x]; trivial; [now unfold convert; case (_ && _)|].
unfold convert.
case_eq (F.valid_lb xl); [|intros _ [H0 H1]; exfalso; lra].
case_eq (F.valid_ub xu); [|intros _ _ [H0 H1]; exfalso; lra].
intros Vxu Vxl.
intros (Hxl, Hxu).
simpl.
generalize (F.classify_correct yf).
rewrite F.cmp_correct, F.zero_correct, F.real_correct, F'.classify_zero.
case_eq (F.classify yf); intro Cyf;
  [xreal_tac2; [easy|]|xreal_tac2; [|easy]..]; intros _; [|easy..].
unfold Xcmp.
case Rcompare_spec; intro Hr.
{ elim (F.mul_DN_correct prec xu yf).
  { intros Vl Hl; rewrite Vl.
    elim (F.mul_UP_correct prec xl yf).
    { intros Vu Hu; rewrite Vu.
      apply le_contains.
      { apply (le_lower_trans _ _ _ Hl).
        rewrite X.
        revert Hxu; xreal_tac2; [now simpl|]; intro Hx.
        now apply Ropp_le_contravar, Rmult_le_compat_neg_r; [apply Rlt_le|]. }
      revert Hu; apply le_upper_trans.
      rewrite X.
      revert Hxl; xreal_tac2; [now simpl|]; intro Hx.
      now apply Rmult_le_compat_neg_r; [apply Rlt_le|]. }
    unfold F.is_non_neg, F.is_non_pos, F.is_non_pos_real, F.is_non_neg_real.
    case (F.toX xl).
    { now right; left; split;
        [split|split; [rewrite F'.valid_lb_real;
           [|rewrite F.real_correct, X]|rewrite X; apply Rlt_le]]. }
    intro r'; case (Rlt_or_le 0 r'); intro Hr'.
    { now do 3 right; split; [|rewrite X]; apply Rlt_le. }
    now right; left; split; [split|split; [rewrite F'.valid_lb_real;
      [|rewrite F.real_correct, X]|rewrite X; apply Rlt_le]]. }
  unfold F.is_non_neg_real, F.is_non_pos_real, F.is_non_pos, F.is_non_neg.
  case (F.toX xu).
  { now right; right; left; split; [split|split; [rewrite F'.valid_lb_real;
      [|rewrite F.real_correct, X]|rewrite X; apply Rlt_le]]. }
  intro r'; case (Rlt_or_le 0 r'); intro Hr'.
  { now do 2 right; left; split; [split; [|apply Rlt_le]|split; [rewrite F'.valid_lb_real;
      [|rewrite F.real_correct, X]|rewrite X; apply Rlt_le]]. }
  now right; left; split; [|rewrite X; apply Rlt_le]. }
{ rewrite Hr, Rmult_0_r.
  rewrite F'.valid_lb_real, ?F'.valid_ub_real;
    [|now rewrite F.real_correct, F.zero_correct..].
  now apply le_contains; rewrite F.zero_correct; right. }
elim (F.mul_DN_correct prec xl yf).
{ intros Vl Hl; rewrite Vl.
  elim (F.mul_UP_correct prec xu yf).
  { intros Vu Hu; rewrite Vu.
    apply le_contains.
    { apply (le_lower_trans _ _ _ Hl).
      rewrite X.
      revert Hxl; xreal_tac2; [now simpl|]; intro Hx.
      now apply Ropp_le_contravar, Rmult_le_compat_r; [apply Rlt_le|]. }
    revert Hu; apply le_upper_trans.
    rewrite X.
    revert Hxu; xreal_tac2; [now simpl|]; intro Hx.
    now apply Rmult_le_compat_r; [apply Rlt_le|]. }
  unfold F.is_non_neg, F.is_non_pos, F.is_non_pos_real, F.is_non_neg_real.
  case (F.toX xu).
  { now left; split; [split|split; [rewrite F'.valid_ub_real;
      [|rewrite F.real_correct, X]|rewrite X; apply Rlt_le]]. }
  intro r'; case (Rlt_or_le 0 r'); intro Hr'.
  { now left; split; [split; [|apply Rlt_le]|split; [rewrite F'.valid_ub_real;
      [|rewrite F.real_correct, X]|rewrite X; apply Rlt_le]]. }
  now do 2 right; left; split; [|rewrite X; apply Rlt_le]. }
unfold F.is_non_neg_real, F.is_non_pos_real, F.is_non_pos, F.is_non_neg.
case (F.toX xl).
{ now do 3 right; split; [split|split; [rewrite F'.valid_ub_real;
    [|rewrite F.real_correct, X]|rewrite X; apply Rlt_le]]. }
intro r'; case (Rlt_or_le 0 r'); intro Hr'.
{ now left; split; [|rewrite X]; apply Rlt_le. }
now do 3 right; split; [split|split; [rewrite F'.valid_ub_real;
  [|rewrite F.real_correct, X]|rewrite X; apply Rlt_le]].
Qed.

Theorem mul_correct :
  forall prec,
  extension_2 Xmul (mul prec).
Proof.
intros prec [ | xl xu] [ | yl yu] [ | x] [ | y] ; trivial;
  [| |intros _|]; [now unfold convert; case (_ && _)..|].
intros Hxlu Hylu.
generalize Hxlu Hylu.
unfold convert.
case_eq (F.valid_lb xl); [|intros _ [H0 H1]; exfalso; lra].
case_eq (F.valid_ub xu); [|intros _ _ [H0 H1]; exfalso; lra].
intros Vxu Vxl.
case_eq (F.valid_lb yl); [|intros _ _ [H0 H1]; exfalso; lra].
case_eq (F.valid_ub yu); [|intros _ _ _ [H0 H1]; exfalso; lra].
intros Vyu Vyl.
intros (Hxl, Hxu) (Hyl, Hyu).
simpl.
unfold bnd, contains, convert.
(* case study on sign of xi *)
generalize (sign_large_correct_ xl xu x Hxlu).
case (sign_large_ xl xu) ; intros (Hx0, Hx0') ;
  (* case study on sign of yi *)
  try ( generalize (sign_large_correct_ yl yu y Hylu) ;
        case (sign_large_ yl yu) ; intros (Hy0, Hy0') ) ;
  (* remove trivial comparisons with zero *)
  try ( rewrite F'.valid_lb_real, ?F'.valid_ub_real;
        [|now rewrite F.real_correct, F.zero_correct..] ; simpl ;
        try ( rewrite Hx0 ; rewrite Rmult_0_l ) ;
        try ( rewrite Hy0 ; rewrite Rmult_0_r ) ;
        split ; rewrite F.zero_correct ; apply Rle_refl ) ;
  (* most cases *)
  try ( match goal with
        | |- context [F.valid_lb (F.mul_DN ?prec ?x ?y)] =>
          elim (F.mul_DN_correct prec x y); [intros Vl Hl; rewrite Vl|
            unfold F.is_non_neg_real, F.is_non_pos_real;
            unfold F.is_non_neg, F.is_non_pos]
        end ;
        [ match goal with
          | |- context [F.valid_ub (F.mul_UP ?prec ?x ?y)] =>
            elim (F.mul_UP_correct prec x y); [intros Vu Hu; rewrite Vu|
              unfold F.is_non_neg_real, F.is_non_pos_real;
              unfold F.is_non_neg, F.is_non_pos]
          end|] ;
        [split;
         match goal with
         | |- context [F.toX (F.mul_DN ?prec ?x ?y)] =>
           xreal_tac2; revert Hl;
           (xreal_tac x; [now simpl|]);
           (xreal_tac y; [now simpl|]);
           (let H := fresh "H" in
            intro H; apply Ropp_le_cancel in H;
            apply (Rle_trans _ _ _ H); clear H)
         | |- context [F.toX (F.mul_UP ?prec ?x ?y)] =>
           xreal_tac2; revert Hu;
           (xreal_tac x; [now simpl|]);
           (xreal_tac y; [now simpl|]);
           apply Rle_trans
         end ;
         clear_complex;
         (* solve by transivity *)
         try ( eauto with mulauto ; fail )
        | |] ;
        try (destruct Hx0' as (Hx0', (rHx0, (Hx0'', Hx0'''))); rewrite Hx0'') ;
        try (destruct Hy0' as (Hy0', (rHy0, (Hy0'', Hy0'''))); rewrite Hy0'') ;
        try (now left);
        try (now (right; left));
        try (now (right; right; left));
        try (now (right; right; right)) ).
(* multiplication around zero *)
elim (F.mul_DN_correct prec xl yu);
  [intros Vxlyu Hxlyu
  |now (try (now left); try (now (right; left));
        try (now (right; right; left)); try (now (right; right; right)))].
elim (F.mul_DN_correct prec xu yl);
  [intros Vxuyl Hxuyl
  |now (try (now left); try (now (right; left));
        try (now (right; right; left)); try (now (right; right; right)))].
elim (F.mul_UP_correct prec xl yl);
  [intros Vxlyl Hxlyl
  |now (try (now left); try (now (right; left));
        try (now (right; right; left)); try (now (right; right; right)))].
elim (F.mul_UP_correct prec xu yu);
  [intros Vxuyu Hxuyu
  |now (try (now left); try (now (right; left));
        try (now (right; right; left)); try (now (right; right; right)))].
elim (F'.min_valid_lb _ _ Vxlyu Vxuyl).
intros Vmin Hmin.
elim (F'.max_valid_ub _ _ Vxlyl Vxuyu).
intros Vmax Hmax.
rewrite Vmin, Vmax, Hmin, Hmax.
split.
{ do 2 xreal_tac2.
  simpl; apply <-Rmin_Rle.
  destruct (Rle_or_lt x 0) as [Hx|Hx];
    [left|right; generalize (Rlt_le _ _ Hx); clear Hx; intro Hx];
    [revert Hxlyu;
     xreal_tac xl; [now simpl|];
     xreal_tac yu; [now simpl|]
    |revert Hxuyl;
     xreal_tac xu; [now simpl|];
     xreal_tac yl; [now simpl|]];
    (let H := fresh "H" in
     intro H; apply Ropp_le_cancel in H;
     apply (Rle_trans _ _ _ H); clear H);
    clear_complex ;
    eauto with mulauto. }
do 2 xreal_tac2.
simpl; apply <-Rmax_Rle.
destruct (Rle_or_lt x 0) as [Hx|Hx];
  [left|right; generalize (Rlt_le _ _ Hx); clear Hx; intro Hx];
  [revert Hxlyl;
   xreal_tac xl; [now simpl|];
   xreal_tac yl; [now simpl|]
  |revert Hxuyu;
   xreal_tac xu; [now simpl|];
   xreal_tac yu; [now simpl|]];
  apply Rle_trans;
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
intros prec yf [| xl xu] [| x]; trivial; [now unfold convert; case (_ && _)|].
unfold convert at 1.
case_eq (F.valid_lb xl); [|intros _ [H0 H1]; exfalso; lra].
case_eq (F.valid_ub xu); [|intros _ _ [H0 H1]; exfalso; lra].
intros Vxu Vxl.
intros [Hxl Hxu].
simpl.
generalize (F.classify_correct yf).
rewrite F.cmp_correct, F.zero_correct, F.real_correct, F'.classify_zero.
case_eq (F.classify yf); intro Cyf;
  [xreal_tac2; [easy|]|xreal_tac2; [|easy]..]; intros _; [|easy..].
unfold Xcmp.
unfold Xdiv'.
simpl.
case Rcompare_spec ; intros Hy ; try exact I ;
  simpl; simpl_is_zero.
{ elim (F.div_DN_correct prec xu yf); [intros Vl Hl|]; last first.
  { unfold F.is_non_neg_real, F.is_non_pos_real, F.is_non_neg, F.is_non_pos.
    unfold F.is_neg_real, F.is_pos_real.
    generalize (F.real_correct yf).
    rewrite X, Vxu.
    intro Ryf.
    xreal_tac xu; [now left|].
    destruct (Rle_or_lt r0 0) as [Hr0|Hr0].
    { now (do 3 right). }
    now left; split; [|now simpl]; split; [|left]. }
  elim (F.div_UP_correct prec xl yf); [intros Vu Hu|]; last first.
  { unfold F.is_non_neg_real, F.is_non_pos_real, F.is_non_neg, F.is_non_pos.
    unfold F.is_neg_real, F.is_pos_real.
    generalize (F.real_correct yf).
    rewrite X, Vxl.
    intro Ryf.
    xreal_tac xl; [now right; left|].
    destruct (Rle_or_lt r0 0) as [Hr0|Hr0].
    { now right; left. }
    now right; right; left; split; [left|]. }
  rewrite Vl, Vu.
  split.
  { revert Hl; rewrite X.
    xreal_tac (F.div_DN prec xu yf); [now simpl|].
    revert Hxu; xreal_tac xu; [now simpl|]; intro Hxu.
    unfold Xdiv, Xdiv'; simpl_is_zero.
    intro H; apply Ropp_le_cancel in H; revert H.
    unfold Rdiv ; eauto with mulauto. }
  revert Hu; rewrite X.
  xreal_tac (F.div_UP prec xl yf); [now simpl|].
  revert Hxl; xreal_tac xl; [now simpl|]; intro Hxl.
  unfold Xdiv, Xdiv'; simpl_is_zero.
  unfold Rdiv ; eauto with mulauto. }
elim (F.div_DN_correct prec xl yf); [intros Vl Hl|]; last first.
{ unfold F.is_non_neg_real, F.is_non_pos_real, F.is_non_neg, F.is_non_pos.
  unfold F.is_neg_real, F.is_pos_real.
  generalize (F.real_correct yf).
  rewrite X, Vxl.
  intro Ryf.
  xreal_tac xl; [now right; left|].
  destruct (Rle_or_lt r0 0) as [Hr0|Hr0].
  { now right; left. }
  now right; right; left; split; [left|]. }
elim (F.div_UP_correct prec xu yf); [intros Vu Hu|]; last first.
{ unfold F.is_non_neg_real, F.is_non_pos_real, F.is_non_neg, F.is_non_pos.
  unfold F.is_neg_real, F.is_pos_real.
  generalize (F.real_correct yf).
  rewrite X, Vxu.
  intro Ryf.
  xreal_tac xu; [now left|].
  destruct (Rle_or_lt r0 0) as [Hr0|Hr0].
  { now do 3 right. }
  now left; split; [|now simpl]; split; [|left]. }
rewrite Vl, Vu.
split.
{ revert Hl; rewrite X.
  xreal_tac (F.div_DN prec xl yf); [now simpl|].
  revert Hxl; xreal_tac xl; [now simpl|]; intro Hxl.
  unfold Xdiv, Xdiv'; simpl_is_zero.
  intro H; apply Ropp_le_cancel in H; revert H.
  unfold Rdiv ; eauto with mulauto. }
revert Hu; rewrite X.
xreal_tac (F.div_UP prec xu yf); [now simpl|].
revert Hxu; xreal_tac xu; [now simpl|]; intro Hxu.
unfold Xdiv, Xdiv'; simpl_is_zero.
unfold Rdiv ; eauto with mulauto.
Qed.

Theorem div_correct :
  forall prec,
  extension_2 Xdiv (div prec).
Proof.
intros prec [ | xl xu] [ | yl yu] [ | x] [ | y] ;
  try ( intros ; exact I ) ;
  [now unfold convert; case (_ && _)..
  |now unfold convert at 2; case (_ && _)|].
intros Hxlu Hylu.
generalize Hxlu Hylu.
unfold convert at -3.
case_eq (F.valid_lb xl); [|intros _ [H0 H1]; exfalso; lra].
case_eq (F.valid_ub xu); [|intros _ _ [H0 H1]; exfalso; lra].
intros Vxu Vxl [Hxl Hxu].
case_eq (F.valid_lb yl); [|intros _ [H0 H1]; exfalso; lra].
case_eq (F.valid_ub yu); [|intros _ _ [H0 H1]; exfalso; lra].
intros Vyu Vyl [Hyl Hyu].
simpl.
unfold bnd, contains, convert, Xdiv'.
(* case study on sign of xi *)
generalize (sign_strict_correct_ xl xu x Hxlu).
case (sign_strict_ xl xu) ; intros (Hx0, Hx0') ;
  (* case study on sign of yi *)
  try ( generalize (sign_strict_correct_ yl yu y Hylu) ;
        case (sign_strict_ yl yu) ; intros (Hy0, Hy0') ) ;
  try exact I ; try simpl_is_zero ; unfold Rdiv ;
  (* remove trivial comparisons with zero *)
  try ( rewrite F'.valid_lb_real, ?F'.valid_ub_real;
        [|now rewrite F.real_correct, F.zero_correct..] ; simpl ;
        try ( rewrite Hx0 ; rewrite Rmult_0_l ) ;
        split ; rewrite F.zero_correct ; apply Rle_refl ) ;
  (* simplify Fdivz *)
  try ( (unfold Fdivz_DN || unfold Fdivz_UP) ;
        rewrite F.real_correct ;
        xreal_tac3 yl ; xreal_tac3 yu ;
        try rewrite F.zero_correct ) ;
  try ( rewrite (F'.valid_lb_real F.zero) ;
        [|now rewrite F.real_correct, F.zero_correct] ) ;
  try ( rewrite (F'.valid_ub_real F.zero) ;
        [|now rewrite F.real_correct, F.zero_correct] ) ;
  try ( destruct Hy0' as (_, (rHy0', (Hy0', _))) ;
        match type of Hy0' with
        | F.toX ?x = Xreal _ =>
          match goal with
          | H : F.toX x = Xnan |- _ => rewrite H in Hy0'
          end
        end ;
        discriminate ) ;
  try match goal with
      | |- context [F.valid_lb (F.div_DN ?prec ?x ?y)] =>
        elim (F.div_DN_correct prec x y); [intros Vl Hl; rewrite Vl|
          unfold F.is_non_neg, F.is_neg_real, F.is_non_pos, F.is_pos_real;
          unfold F.is_non_neg_real, F.is_non_pos_real ] ;
        rewrite ?F.real_correct
      end ;
  try match goal with
      | |- context [F.valid_ub (F.div_UP ?prec ?x ?y)] =>
        elim (F.div_UP_correct prec x y); [intros Vu Hu; rewrite Vu|
          unfold F.is_non_neg, F.is_neg_real, F.is_non_pos, F.is_pos_real;
          unfold F.is_non_neg_real, F.is_non_pos_real ] ;
        rewrite ?F.real_correct
      end ;
  try split ;
  (* solve by comparing to zero *)
  try ( clear_complex ; simpl ; eauto with mulauto2 ; fail ) ;
  try match goal with
      | |- context [F.toX (F.div_UP ?prec ?x ?y)] =>
        xreal_tac2; revert Hu ;
        xreal_tac3 x; (try now simpl) ;
        xreal_tac3 y; (try now simpl) ;
        unfold Xdiv, Xdiv', Rdiv ;
        match goal with
          |- context [is_zero ?v] => case (is_zero v) ; [now simpl|]
        end ;
        apply Rle_trans ;
        clear_complex ;
        (* solve by transivity *)
        eauto 8 with mulauto
      | |- context [F.toX (F.div_DN ?prec ?x ?y)] =>
        xreal_tac2; revert Hl ;
        xreal_tac3 x; (try now simpl) ;
        xreal_tac3 y; (try now simpl) ;
        unfold Xdiv, Xdiv', Rdiv ;
        match goal with
          |- context [is_zero ?v] => case (is_zero v) ; [now simpl|]
        end ;
        (let H := fresh "H" in
         intro H; apply Ropp_le_cancel in H;
         apply (Rle_trans _ _ _ H); clear H) ;
        clear_complex ;
        (* solve by transivity *)
        eauto 8 with mulauto
      end ;
  repeat match goal with
         | H:F.toX _ = _ |- _ => (try rewrite H) ; clear H
         end ;
  try destruct Hx0' as (Hx0', (rHx0, (Hx0'', Hx0'''))) ;
  try rewrite Hx0'' ;
  try apply Rlt_le in Hx0''' ;
  try destruct Hy0' as (Hy0', (rHy0, (Hy0'', Hy0'''))) ;
  try rewrite Hy0'' ;
  try ( match type of Hx0' with
        | context [F.toX ?x] => revert Hx0'; xreal_tac x; intro Hx0'
        end ) ;
  try apply Rlt_le in Hx0' ;
  try rewrite X0 ;
  try rewrite X1 ;
  try inversion Hy0'' ;
  try (now left) ;
  try (now (right; left)) ;
  try (now (right; right; left)) ;
  try (now (right; right; right)).
Qed.

Theorem inv_correct :
  forall prec,
  extension Xinv (inv prec).
Proof.
intros prec [ | xl xu] [ | x] ;
  try ( intros ; exact I ) ;
  [now unfold convert; case (_ && _)|].
intros Hxlu.
generalize Hxlu.
unfold convert at 1.
case_eq (F.valid_lb xl); [|intros _ [H0 H1]; exfalso; lra].
case_eq (F.valid_ub xu); [|intros _ _ [H0 H1]; exfalso; lra].
intros Vxu Vxl [Hxl Hxu].
simpl.
unfold bnd, contains, convert, Xinv'.
(* case study on sign of xi *)
generalize (sign_strict_correct_ xl xu x Hxlu).
unfold c1.
case (sign_strict_ xl xu) ;
  (intros (Hx0, (Hx0', (rHx0, (Hx0'', Hx0''')))) || intros (Hx0, Hx0')) ;
  try exact I ; try simpl_is_zero ; unfold Rdiv ;
  (* simplify Fdivz *)
  try ( (unfold Fdivz_DN, Fdivz_UP) ;
        rewrite 2!F.real_correct ;
        xreal_tac3 xl ; xreal_tac3 xu ;
        try rewrite F.zero_correct ) ;
  try ( rewrite (F'.valid_lb_real F.zero) ;
        [|now rewrite F.real_correct, F.zero_correct] ) ;
  try ( rewrite (F'.valid_ub_real F.zero) ;
        [|now rewrite F.real_correct, F.zero_correct] ) ;
  try match goal with
      | |- context [F.valid_lb (F.div_DN ?prec ?x ?y)] =>
        elim (F.div_DN_correct prec x y); [intros Vl Hl; rewrite Vl|
          unfold F.is_non_neg, F.is_neg_real, F.is_non_pos, F.is_pos_real;
          unfold F.is_non_neg_real, F.is_non_pos_real ] ;
        rewrite ?F.real_correct
      end ;
  try match goal with
      | |- context [F.valid_ub (F.div_UP ?prec ?x ?y)] =>
        elim (F.div_UP_correct prec x y); [intros Vu Hu; rewrite Vu|
          unfold F.is_non_neg, F.is_neg_real, F.is_non_pos, F.is_pos_real;
          unfold F.is_non_neg_real, F.is_non_pos_real ] ;
        rewrite ?F.real_correct
      end ;
  try split ;
  (* solve by comparing to zero *)
  try ( clear_complex ; simpl ; eauto with mulauto2 ; fail ) ;
  try match goal with
      | |- context [F.toX (F.div_UP ?prec ?x ?y)] =>
        xreal_tac2; revert Hu ;
          rewrite F.fromZ_correct by easy ;
          xreal_tac3 y; (try now simpl) ;
          unfold Xdiv, Xdiv', Rdiv ;
          rewrite Rmult_1_l ;
          match goal with
            |- context [is_zero ?v] => case (is_zero v) ; [now simpl|]
          end ;
          apply Rle_trans ;
          try (revert Hxl; rewrite Hx0'') ;
          auto with mulauto
      | |- context [F.toX (F.div_DN ?prec ?x ?y)] =>
        xreal_tac2; revert Hl ;
          rewrite F.fromZ_correct by easy ;
          xreal_tac3 y; (try now simpl) ;
          unfold Xdiv, Xdiv', Rdiv ;
          rewrite Rmult_1_l ;
          match goal with
            |- context [is_zero ?v] => case (is_zero v) ; [now simpl|]
          end ;
          (let H := fresh "H" in
           intro H; apply Ropp_le_cancel in H;
           apply (Rle_trans _ _ _ H); clear H) ;
          try (revert Hxu; rewrite Hx0'') ;
          auto with mulauto
      end ;
  repeat match goal with
         | H:F.toX _ = _ |- _ => (try rewrite H) ; clear H
         end ;
  try rewrite F.fromZ_correct by easy ;
  try ( rewrite (F'.valid_lb_real (F.fromZ 1)) ;
        [|now rewrite F.real_correct, F.fromZ_correct] ) ;
  try ( rewrite (F'.valid_ub_real (F.fromZ 1)) ;
        [|now rewrite F.real_correct, F.fromZ_correct] ) ;
  set (H01 := Rlt_le _ _ Rlt_0_1) ;
  try (now left) ;
  try (now (right; left)) ;
  try (now (right; right; left)) ;
  try (now (right; right; right)).
Qed.

Theorem sqr_correct :
  forall prec,
  extension Xsqr (sqr prec).
Proof.
intros prec [ | xl xu] [ | x] ;
  try ( intros ; exact I ) ;
  [now unfold convert; case (_ && _)|].
intros Hxlu.
generalize Hxlu.
unfold convert at 1.
case_eq (F.valid_lb xl); [|intros _ [H0 H1]; exfalso; lra].
case_eq (F.valid_ub xu); [|intros _ _ [H0 H1]; exfalso; lra].
intros Vxu Vxl [Hxl Hxu].
simpl.
unfold bnd, contains, convert.
(* case study on sign of xi *)
generalize (sign_large_correct_ xl xu x Hxlu).
unfold Rsqr.
case (sign_large_ xl xu) ; intros [Hx0 Hx0'] ;
  [|revert Hx0'; intros [Hxl0 [rxu [Hrxu Hrxu0]]]..|] ;
  (* remove trivial comparisons with zero *)
  try ( rewrite F'.valid_lb_real, ?F'.valid_ub_real;
        [|now rewrite F.real_correct, F.zero_correct..] ; simpl ;
        try ( rewrite Hx0 ; rewrite Rmult_0_l ) ;
        split ; rewrite F.zero_correct ; apply Rle_refl ) ;
  rewrite ?F.cmp_correct, ?F.zero_correct ;
  rewrite ?F'.classify_zero, ?F'.valid_lb_zero ;
  try match goal with
      | |- context [F.mul_DN ?prec ?x ?y] =>
        elim (F.mul_DN_correct prec x x);
          [intros Vmdn Hmdn|
           unfold F.is_non_neg_real, F.is_non_neg, F.is_non_pos_real, F.is_non_pos ;
           rewrite Hrxu ; try ( now left ) ; now right ; left] ;
          generalize Vmdn ;
          rewrite ?F.valid_lb_correct, ?F.valid_ub_correct ;
          case_eq (F.classify (F.mul_DN prec x x)) ;
          intros Cmdn; try easy; intros _ ;
          generalize (F.classify_correct (F.mul_DN prec x x)) ;
          rewrite F.real_correct, Cmdn ;
          [xreal_tac2; [easy|]; intros _|xreal_tac2; [|easy]; intros _..] ;
          unfold Xcmp ;
          try ( case Rcompare_spec ; intros Hr ) ;
          rewrite ?F'.valid_lb_zero, ?F.valid_lb_correct, ?Cmdn ;
          rewrite ?F.zero_correct
      end ;
  try match goal with
      | |- context [ F.mul_UP prec ?x ?y ] =>
        elim (F.mul_UP_correct prec x x) ;
          [intros Vmdu Hmdu|
           now rewrite ?Vxl, ?Vxu ; try ( now left ) ; now right ; left] ;
        rewrite Vmdu ;
        split
      end ;
  try apply Rle_0_sqr ;
  try ( generalize Hmdu ; unfold le_upper ;
        xreal_tac2; [easy|] ; xreal_tac2; [easy|] ; simpl ;
        clear_complex ;
        (* solve by transivity *)
        eauto with mulauto ; fail ) ;
  try ( generalize Hmdn ; unfold le_lower, le_upper ; simpl ;
        xreal_tac2 ; simpl; xreal_tac2 ;
        intro H; apply Ropp_le_cancel in H; revert H ;
        try ( revert Hxu; rewrite Hrxu ) ;
        try ( revert Hxl; rewrite Hrxu ) ;
        clear_complex ;
        (* solve by transivity *)
        eauto with mulauto ; fail ).
(* multiplication around zero *)
simpl.
destruct (F.abs_correct xl) as [Haxl Vaxl].
destruct (F'.max_valid_ub _ _ Vaxl Vxu) as [Vmax Hmax].
elim (F.mul_UP_correct prec (F.max (F.abs xl) xu) (F.max (F.abs xl) xu)).
2:{ unfold F.is_non_neg, F.is_non_pos, F.is_non_neg_real, F.is_non_pos_real.
    rewrite Vmax, Hmax, Haxl.
    left.
    split; (split; [exact eq_refl|]); revert Hx0';
      (xreal_tac xu; case (Xabs (F.toX xl)); [now simpl..|]);
      intros r' Hr; apply (Rle_trans _ _ _ Hr), Rmax_r. }
intros Vu Hu.
rewrite Vu.
split; [apply Rle_0_sqr|].
revert Hu.
unfold le_upper.
xreal_tac2; [easy|].
rewrite Hmax, Haxl.
do 2 ( xreal_tac2; [easy|] ) ; simpl.
apply Rle_trans.
rewrite (Rabs_left1 _ Hx0).
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
  F.valid_ub x = true ->
  le_upper (Xreal 0) (F.toX x) ->
  F.valid_ub (Fpower_pos_UP prec x n) = true
  /\ le_upper (Xpower_int (F.toX x) (Zpos n)) (F.toX (Fpower_pos_UP prec x n)).
Proof.
intros prec x n Vx Hx.
set (p := Fpower_pos_UP prec x n).
cut (F.valid_ub p = true /\ le_upper (Xreal 0) (F.toX p)
     /\ le_upper (Xpower_int (F.toX x) (Z.pos n)) (F.toX p)).
{ now simpl. }
unfold p; clear p.
revert x Vx Hx; induction n; intros x Vx Hx; last first.
{ do 2 (split; [now simpl|]).
  simpl.
  xreal_tac x.
  now simpl; rewrite Rmult_1_r; right. }
{ assert (Vxx : F.valid_ub (F.mul_UP prec x x) = true).
  { now apply F.mul_UP_correct; left. }
  assert (Hxx : le_upper (Xreal 0) (F.toX (F.mul_UP prec x x))).
  { apply (le_upper_trans _ (Xmul (F.toX x) (F.toX x))).
    { now xreal_tac2; apply Rmult_le_pos. }
    now apply F.mul_UP_correct; left. }
  do 2 (split; [now apply (IHn _ Vxx Hxx)|]).
  generalize (proj2 (proj2 (IHn _ Vxx Hxx))).
  apply le_upper_trans.
  generalize (Xpower_int_correct (Z.pos n) (F.toX (F.mul_UP prec x x))).
  xreal_tac2; (case (Xpower_int _ _); [intros _; exact I|]);
    intros r1' Hr1'; [now simpl|].
  rewrite <-Hr1'.
  xreal_tac2.
  { cut (le_upper (Xnan * Xnan)%XR (Xreal r)); [now simpl|].
    rewrite <-X0, <-X.
    now apply F.mul_UP_correct; left. }
  simpl.
  rewrite Pos2Nat.inj_xO.
  rewrite pow_sqr.
  apply pow_incr; split; [now apply Rmult_le_pos|].
  change (_ <= _)%R with (le_upper (Xmul (Xreal r0) (Xreal r0)) (Xreal r)).
  rewrite <-X0, <-X.
  now apply F.mul_UP_correct; left; rewrite <-X0 in Hx. }
assert (Vxx : F.valid_ub (F.mul_UP prec x x) = true).
{ now apply F.mul_UP_correct; left. }
assert (Hxx : le_upper (Xreal 0) (F.toX (F.mul_UP prec x x))).
{ apply (le_upper_trans _ (Xmul (F.toX x) (F.toX x))).
  { now xreal_tac2; apply Rmult_le_pos. }
  now apply F.mul_UP_correct; left. }
elim (F.mul_UP_correct
        prec x (Fpower_pos_UP prec (F.mul_UP prec x x) n)).
{ intros Vu Hu.
  split; [now simpl; rewrite Vu|].
  split.
  { revert Hu; apply le_upper_trans.
    do 2 xreal_tac2.
    apply Rmult_le_pos; [now simpl|].
    change (_ <= _)%R with (le_upper (Xreal 0) (Xreal r0)).
    rewrite <-X0.
    now apply IHn. }
  revert Hu.
  apply le_upper_trans.
  revert Hx; xreal_tac2; [now simpl|]; intro Hr.
  xreal_tac2.
  simpl.
  rewrite Pmult_nat_mult, Nat.mul_comm.
  apply (Rmult_le_compat_l _ _ _ Hr).
  rewrite pow_sqr.
  change (_ <= _)%R
    with (le_upper (Xreal ((r * r) ^ Pos.to_nat n)) (Xreal r0)).
  rewrite <-X0.
  apply (le_upper_trans _ (Xpower_int (F.toX (F.mul_UP prec x x)) (Z.pos n))).
  { generalize (Xpower_int_correct (Z.pos n) (F.toX (F.mul_UP prec x x))).
    xreal_tac2; (case (Xpower_int _ _); [intros _; exact I|]);
      intros r1' Hr1'; [now simpl|].
    rewrite <-Hr1'.
    apply pow_incr; split; [now apply Rmult_le_pos|].
    change (_ <= _)%R with (le_upper (Xmul (Xreal r) (Xreal r)) (Xreal r1)).
    rewrite <-X, <-X1; apply F.mul_UP_correct.
    left.
    unfold F.is_non_neg.
    now rewrite F'.valid_ub_real, X; [|rewrite F.real_correct, X]. }
  now apply IHn. }
left.
split; [now simpl|].
now split; now apply IHn.
Qed.

Lemma Fpower_pos_dn_correct :
  forall prec x n,
  le_lower' (Xreal 0) (F.toX x) ->
  F.valid_lb (Fpower_pos_DN prec x n) = true
  /\ le_lower' (F.toX (Fpower_pos_DN prec x n)) (Xpower_int (F.toX x) (Zpos n)).
Proof.
intros prec x n.
xreal_tac2; [now simpl|].
simpl.
intro Hx.
set (p := Fpower_pos_DN prec x n).
cut (F.valid_lb p = true /\ le_lower' (F.toX p) (Xreal (r ^ Pos.to_nat n))).
{ now simpl. }
unfold p; clear p.
revert x r X Hx.
unfold le_lower'.
induction n ; intros x rx Hrx Hx ; simpl; last first.
{ split.
  { now rewrite F'.valid_lb_real; [|rewrite F.real_correct, Hrx]. }
  now rewrite Hrx, Rmult_1_r; right. }
{ rewrite F.cmp_correct, F.zero_correct, F'.classify_zero.
  elim (F.mul_DN_correct prec x x);
    [|now left; unfold F.is_non_neg_real; rewrite Hrx].
  intros Vmdn Hmdn.
  generalize Vmdn; rewrite F.valid_lb_correct.
  case F.classify; [..|easy]; intros _.
  2: now rewrite F'.valid_lb_nan, F'.nan_correct.
  2: { rewrite F'.valid_lb_zero, F.zero_correct; split; [easy|].
       rewrite Pos2Nat.inj_xO, pow_sqr.
       apply pow_le, Rle_0_sqr. }
  unfold Xcmp.
  xreal_tac2; [now rewrite F'.valid_lb_nan, F'.nan_correct|].
  case Rcompare_spec; intro Hr0;
    [rewrite F'.valid_lb_zero, F.zero_correct; split; [easy|] ;
     rewrite Pos2Nat.inj_xO, pow_sqr ;
     apply pow_le, Rle_0_sqr..|].
  rewrite Pos2Nat.inj_xO, pow_sqr.
  generalize (IHn _ _ X (Rlt_le _ _ Hr0)).
  intros [Vp Hp]; split; [exact Vp|].
  revert Hp; xreal_tac2; [easy|]; intro Hp.
  apply (Rle_trans _ _ _ Hp).
  apply pow_incr.
  split; [now left|].
  apply Ropp_le_cancel.
  change (_ <= _)%R with (le_lower (Xreal r) (Xmul (Xreal rx) (Xreal rx))).
  now rewrite <-Hrx. }
rewrite F.cmp_correct, F.zero_correct, F'.classify_zero.
elim (F.mul_DN_correct prec x x);
  [|now left; unfold F.is_non_neg_real; rewrite Hrx].
intros Vmdn Hmdn.
generalize Vmdn; rewrite F.valid_lb_correct.
case F.classify; [..|easy]; intros _.
2: now rewrite F'.valid_lb_nan, F'.nan_correct.
2: { rewrite F'.valid_lb_zero, F.zero_correct; split; [easy|].
     apply (Rmult_le_pos _ _ Hx).
     rewrite Pmult_nat_mult, Nat.mul_comm, pow_sqr.
     apply pow_le, Rle_0_sqr. }
unfold Xcmp.
xreal_tac2; [now rewrite F'.valid_lb_nan, F'.nan_correct|].
case Rcompare_spec; intro Hr0;
  [rewrite F'.valid_lb_zero, F.zero_correct; split; [easy|];
   apply (Rmult_le_pos _ _ Hx);
   rewrite Pmult_nat_mult, Nat.mul_comm, pow_sqr;
   apply pow_le, Rle_0_sqr..|].
elim (IHn _ _ X (Rlt_le _ _ Hr0)).
intros Vp Hp.
elim (F.mul_DN_correct prec x (Fpower_pos_DN prec (F.mul_DN prec x x) n)).
2:{ unfold F.is_non_neg_real, F.is_non_pos_real, F.is_non_neg, F.is_non_pos.
    rewrite Hrx, F'.valid_ub_real, Vp; [|now rewrite F.real_correct, Hrx].
    xreal_tac2; [now right; right; left|].
    now case (Rle_or_lt 0 r0); intro H0r0;
      [left|right; right; left; repeat split; lra]. }
intros Vxp Hxp; split; [easy|].
revert Hxp; rewrite Hrx.
do 2 (xreal_tac2; [easy|]).
unfold le_lower; intro H; apply Ropp_le_cancel in H.
apply (Rle_trans _ _ _ H); clear H.
apply (Rmult_le_compat_l _ _ _ Hx).
apply (Rle_trans _ _ _ Hp).
rewrite Pmult_nat_mult, Nat.mul_comm, pow_sqr.
apply pow_incr; split; [now apply Rlt_le|].
rewrite Hrx in Hmdn.
now apply Ropp_le_cancel in Hmdn.
Qed.

Theorem power_pos_correct :
  forall prec n,
  extension (fun x => Xpower_int x (Zpos n)) (fun x => power_pos prec x n).
Proof.
intros prec n [ | xl xu] [ | x] ;
  try ( intros ; exact I ) ;
  [now unfold convert; case (_ && _)|].
intros Hxlu.
generalize Hxlu.
unfold convert at 1.
case_eq (F.valid_lb xl); [|intros _ [H0 H1]; exfalso; lra].
case_eq (F.valid_ub xu); [|intros _ _ [H0 H1]; exfalso; lra].
unfold contains, convert, power_pos, Xpower_int.
intros Vxu Vxl [Hxl Hxu].
generalize (sign_large_correct_ xl xu x Hxlu).
case (sign_large_ xl xu) ; intros Hx0 ; simpl in Hx0.
{ rewrite F.zero_correct.
  simpl.
  rewrite (proj1 Hx0), pow_i.
  rewrite F'.valid_lb_real, ?F'.valid_ub_real;
    [|now rewrite F.real_correct, F.zero_correct..].
  split ; apply Rle_refl.
  apply lt_O_nat_of_P. }
{ assert (Hxl_pos : le_upper (Xreal 0) (F.toX (F.abs xl))).
  { rewrite (proj1 (F.abs_correct _)).
    now xreal_tac2; apply Rabs_pos. }
  assert (Hxu_pos : le_lower' (Xreal 0) (F.toX (F.abs xu))).
  { destruct Hx0 as (_, (_, (rHx0, (Hx0, _)))).
    rewrite (proj1 (F.abs_correct _)), Hx0.
    apply Rabs_pos. }
  generalize (Fpower_pos_up_correct
                prec _ n (proj2 (F.abs_correct xl)) Hxl_pos).
  generalize (Fpower_pos_dn_correct prec _ n Hxu_pos).
  destruct n as [n|n|].
  { rewrite !F'.neg_correct, F'.valid_lb_neg, F'.valid_ub_neg.
    intros (Vpow_DN, Hpow_DN) (Vpow_UP, Hpow_UP).
    rewrite Vpow_UP, Vpow_DN.
    split.
    { revert Hpow_UP.
      unfold le_upper.
      rewrite (proj1 (F.abs_correct _)).
      xreal_tac2; [now simpl|].
      xreal_tac2; [now simpl|].
      simpl.
      intros H.
      apply Ropp_le_contravar in H.
      apply Rle_trans with (1 := H).
      rewrite Rabs_left1; [|now apply Hx0].
      rewrite Ropp_mult_distr_l_reverse, Ropp_involutive.
      change (Pmult_nat n 2) with (nat_of_P (xO n)).
      rewrite nat_of_P_xO at 2.
      rewrite pow_sqr.
      rewrite <- (Rmult_opp_opp x x).
      rewrite <- pow_sqr, <- nat_of_P_xO.
      apply Rle_trans with (r0 * (-x) ^ nat_of_P (xO n))%R.
      { apply Rmult_le_compat_neg_l; [now apply Hx0|].
        apply pow_incr.
        now split; [rewrite <- Ropp_0|]; apply Ropp_le_contravar. }
      apply Rmult_le_compat_r; [|exact Hxl].
      apply pow_le.
      rewrite <- Ropp_0.
      now apply Ropp_le_contravar. }
    revert Hpow_DN.
    unfold le_lower'.
    rewrite (proj1 (F.abs_correct _)).
    xreal_tac2; [now simpl|].
    xreal_tac2; [now simpl|].
    simpl.
    intros H'.
    apply Ropp_le_contravar in H'.
    apply Rle_trans with (2 := H').
    assert (Hr0 : (r0 <= 0)%R).
    { destruct Hx0 as (_,(_,(ru,(H1,H2)))).
      now inversion H1. }
    rewrite Rabs_left1 with (1 := Hr0).
    rewrite Ropp_mult_distr_l_reverse, Ropp_involutive.
    change (Pmult_nat n 2) with (nat_of_P (xO n)).
    rewrite nat_of_P_xO at 1.
    rewrite pow_sqr.
    rewrite <- (Rmult_opp_opp x x).
    rewrite <- pow_sqr, <- nat_of_P_xO.
    apply Rle_trans with (x * (-r0) ^ nat_of_P (xO n))%R.
    { apply Rmult_le_compat_neg_l.
      apply Hx0.
      apply pow_incr.
      now split; [rewrite <- Ropp_0|]; apply Ropp_le_contravar. }
    apply Rmult_le_compat_r; [|exact Hxu].
    apply pow_le.
    rewrite <- Ropp_0.
    now apply Ropp_le_contravar. }
  { intros (Vpow_DN, Hpow_DN) (Vpow_UP, Hpow_UP).
    rewrite Vpow_UP, Vpow_DN.
    split.
    { revert Hpow_DN.
      unfold le_lower'.
      rewrite (proj1 (F.abs_correct _)).
      xreal_tac2; [now simpl|].
      xreal_tac2; [now simpl|].
      simpl.
      intros H.
      apply Rle_trans with (1 := H).
      assert (Hr0 : (r0 <= 0)%R).
      { destruct Hx0 as (_,(_,(ru,(H1,H2)))).
        now inversion H1. }
      rewrite Rabs_left1 with (1 := Hr0).
      change (Pmult_nat n 2) with (nat_of_P (xO n)).
      rewrite nat_of_P_xO at 2.
      rewrite pow_sqr.
      rewrite <- (Rmult_opp_opp x x).
      rewrite <- pow_sqr, <- nat_of_P_xO.
      apply pow_incr.
      now split; [rewrite <- Ropp_0|]; apply Ropp_le_contravar. }
    revert Hpow_UP.
    unfold le_upper.
    rewrite (proj1 (F.abs_correct _)).
    xreal_tac2; [now simpl|].
    xreal_tac2; [now simpl|].
    simpl.
    intros H.
    apply Rle_trans with (2 := H).
    rewrite Rabs_left1; [|now apply Hx0].
    change (Pmult_nat n 2) with (nat_of_P (xO n)).
    rewrite nat_of_P_xO at 1.
    rewrite pow_sqr.
    rewrite <- (Rmult_opp_opp x x).
    rewrite <- pow_sqr, <- nat_of_P_xO.
    apply pow_incr.
    now split; [rewrite <- Ropp_0|]; apply Ropp_le_contravar. }
  intros _ _.
  rewrite Vxl, Vxu.
  now simpl; split; xreal_tac2; rewrite Rmult_1_r. }
{ assert (Hxl_pos : le_lower' (Xreal 0) (F.toX xl)).
  { destruct Hx0 as (_, (_, (rHx0, (Hx0, Hx0')))).
    now rewrite Hx0. }
  assert (Hxu_pos : le_upper (Xreal 0) (F.toX xu)).
  { apply Hx0. }
  generalize (Fpower_pos_up_correct prec _ n Vxu Hxu_pos).
  generalize (Fpower_pos_dn_correct prec _ n Hxl_pos).
  intros (Vpow_DN, Hpow_DN) (Vpow_UP, Hpow_UP).
  rewrite Vpow_UP, Vpow_DN.
  split.
  { revert Hpow_DN.
    unfold le_lower'.
    xreal_tac2; [now simpl|].
    xreal_tac2; [now simpl|].
    intros H.
    assert (Hr0: (0 <= r0)%R).
    { destruct Hx0 as (_,(_,(rl,(H1,H2)))).
      now inversion H1. }
    apply Rle_trans with (1 := H).
    apply pow_incr.
    now split. }
  revert Hpow_UP.
  unfold le_upper.
  xreal_tac2; [now simpl|].
  xreal_tac2; [now simpl|].
  intros H.
  refine (Rle_trans _ _ _ _ H).
  apply pow_incr.
  now split. }
destruct n as [n|n|].
{ assert (Hxl_pos : le_upper (Xreal 0) (F.toX (F.abs xl))).
  { rewrite (proj1 (F.abs_correct _)).
    now xreal_tac2; apply Rabs_pos. }
  assert (Hxu_pos : le_upper (Xreal 0) (F.toX xu)).
  { apply Hx0. }
  generalize (Fpower_pos_up_correct
                prec _ n~1 (proj2 (F.abs_correct xl)) Hxl_pos).
  generalize (Fpower_pos_up_correct prec _ n~1 Vxu Hxu_pos).
  rewrite F'.neg_correct, F'.valid_lb_neg.
  intros (Vpow_DN, Hpow_DN) (Vpow_UP, Hpow_UP).
  rewrite Vpow_UP, Vpow_DN.
  split.
  { revert Hpow_UP.
    unfold le_upper.
    rewrite (proj1 (F.abs_correct _)).
    xreal_tac2; [now simpl|].
    xreal_tac2; [now simpl|].
    simpl.
    rewrite Rabs_left1; [|now apply Hx0].
    intros H.
    apply Ropp_le_contravar in H.
    apply Rle_trans with (1 := H).
    rewrite Ropp_mult_distr_l_reverse, Ropp_involutive.
    destruct (Rle_or_lt x 0) as [Hx|Hx].
    { change (Pmult_nat n 2) with (nat_of_P (xO n)).
      rewrite nat_of_P_xO at 2.
      rewrite pow_sqr.
      rewrite <- (Rmult_opp_opp x x).
      rewrite <- pow_sqr, <- nat_of_P_xO.
      apply Rle_trans with (r0 * (-x) ^ nat_of_P (xO n))%R.
      { apply Rmult_le_compat_neg_l.
        { apply Hx0. }
        apply pow_incr.
        now split; [rewrite <- Ropp_0|]; apply Ropp_le_contravar. }
      apply Rmult_le_compat_r; [|exact Hxl].
      apply pow_le.
      rewrite <- Ropp_0.
      now apply Ropp_le_contravar. }
    apply Rlt_le in Hx.
    apply Rle_trans with 0%R.
    { apply Ropp_le_cancel.
      rewrite Ropp_0, <- Ropp_mult_distr_l_reverse.
      now apply Rmult_le_pos; [|apply pow_le];
        rewrite <- Ropp_0; apply Ropp_le_contravar. }
    apply Rmult_le_pos with (1 := Hx).
    now apply pow_le. }
  revert Hpow_DN.
  unfold le_upper.
  xreal_tac2; [now simpl|].
  xreal_tac2; [now simpl|].
  simpl.
  intros H.
  refine (Rle_trans _ _ _ _ H).
  destruct (Rle_or_lt x 0) as [Hx|Hx].
  { apply Rle_trans with 0%R.
    { apply Ropp_le_cancel.
      rewrite Ropp_0, <- Ropp_mult_distr_l_reverse.
      change (Pmult_nat n 2) with (nat_of_P (xO n)).
      rewrite nat_of_P_xO.
      rewrite pow_sqr.
      rewrite <- (Rmult_opp_opp x x).
      rewrite <- pow_sqr, <- nat_of_P_xO.
      now apply Rmult_le_pos; [|apply pow_le];
        rewrite <- Ropp_0; apply Ropp_le_contravar. }
    apply Rmult_le_pos; [now apply Hx0|].
    now apply pow_le. }
  apply Rlt_le in Hx.
  apply Rmult_le_compat with (1 := Hx).
  { now apply pow_le. }
  { exact Hxu. }
  apply pow_incr.
  now split. }
{ elim (F'.max_valid_ub _ _ (proj2 (F.abs_correct xl)) Vxu).
  intros Vmax Hmax.
  assert (Hxu_pos : le_upper (Xreal 0) (F.toX (F.max (F.abs xl) xu))).
  { rewrite Hmax.
    rewrite (proj1 (F.abs_correct _)).
    xreal_tac xl; xreal_tac xu.
    apply (Rle_trans _ _ _ (proj2 Hx0)), Rmax_r. }
  generalize (Fpower_pos_up_correct prec _ n~0 Vmax Hxu_pos).
  intros (Vpow_UP, Hpow_UP).
  rewrite Vpow_UP.
  rewrite F'.valid_lb_real; [|now rewrite F.real_correct, F.zero_correct].
  split.
  { rewrite F.zero_correct.
    rewrite nat_of_P_xO.
    rewrite pow_sqr.
    change (x * x)%R with (Rsqr x).
    simpl.
    apply pow_le.
    apply Rle_0_sqr. }
  revert Hpow_UP.
  unfold le_upper.
  rewrite Hmax.
  rewrite (proj1 (F.abs_correct _)).
  xreal_tac2; [now simpl|].
  xreal_tac2; [now simpl|].
  xreal_tac2; [now simpl|].
  simpl.
  intros H.
  assert (Hr: (0 <= Rmax (Rabs r0) r1)%R).
  { apply Rmax_case.
    { apply Rabs_pos. }
    apply Hx0. }
  apply Rle_trans with (2 := H).
  destruct (Rle_or_lt x 0) as [Hx|Hx].
  { change (Pmult_nat n 2) with (nat_of_P (xO n)).
    rewrite nat_of_P_xO at 1.
    rewrite pow_sqr.
    rewrite <- (Rmult_opp_opp x x).
    rewrite <- pow_sqr, <- nat_of_P_xO.
    apply pow_incr.
    split.
    { rewrite <- Ropp_0.
      now apply Ropp_le_contravar. }
    apply Rle_trans with (2 := Rmax_l _ _).
    rewrite Rabs_left1.
    { now apply Ropp_le_contravar. }
    apply Hx0. }
  apply pow_incr.
  split.
  { now apply Rlt_le. }
  now apply Rle_trans with (2 := Rmax_r _ _). }
rewrite Vxl, Vxu.
now split; xreal_tac2; simpl; rewrite Rmult_1_r.
Qed.

Theorem power_int_correct :
  forall prec n,
  extension (fun x => Xpower_int x n) (fun x => power_int prec x n).
Proof.
intros prec [|n|n].
{ unfold power_int, Xpower_int.
  intros [ | xl xu] [ | x] ;
    try ( intros ; exact I ) ;
    [now unfold convert; case (_ && _)|].
  intros _.
  simpl.
  unfold c1.
  rewrite F.fromZ_correct by easy.
  rewrite F'.valid_lb_real, ?F'.valid_ub_real;
    [|now rewrite F.real_correct, F.fromZ_correct..].
  split ; apply Rle_refl. }
{ apply power_pos_correct. }
intros xi x Hx.
generalize (power_pos_correct prec n _ _ Hx).
intros Hp.
generalize (inv_correct prec _ _ Hp).
unfold Xpower_int, Xpower_int', Xinv', Xbind, power_int.
destruct x as [ | x]; [easy|].
replace (is_zero x) with (is_zero (x ^ nat_of_P n)); [easy|].
case (is_zero_spec x) ; intros Zx.
{ rewrite Zx, pow_i.
  { apply is_zero_0. }
  apply lt_O_nat_of_P. }
case is_zero_spec ; try easy.
intros H.
elim (pow_nonzero _ _ Zx H).
Qed.

Lemma mask_propagate_l : propagate_l mask.
Proof. intros xi yi; destruct xi; destruct yi; easy. Qed.

Lemma mask_propagate_r : propagate_r mask.
Proof.
intros xi yi; destruct xi; destruct yi; [easy..|].
now unfold convert; case (_ && _).
Qed.

Lemma add_propagate_l : forall prec, propagate_l (add prec).
Proof.
intros prec xi yi; destruct xi; destruct yi; [easy..|].
now unfold convert; case (_ && _).
Qed.

Lemma sub_propagate_l : forall prec, propagate_l (sub prec).
Proof.
intros prec xi yi; destruct xi; destruct yi; [easy..|].
now unfold convert; case (_ && _).
Qed.

Lemma mul_propagate_l : forall prec, propagate_l (mul prec).
Proof.
intros prec xi yi; destruct xi; destruct yi; [easy..|].
now unfold convert; case (_ && _).
Qed.

Lemma div_propagate_l : forall prec, propagate_l (div prec).
Proof.
intros prec xi yi; destruct xi; destruct yi; [easy..|].
now unfold convert; case (_ && _).
Qed.

Lemma add_propagate_r : forall prec, propagate_r (add prec).
Proof.
intros prec xi yi; destruct xi; destruct yi; [easy..|].
now unfold convert; case (_ && _).
Qed.

Lemma sub_propagate_r : forall prec, propagate_r (sub prec).
Proof.
intros prec xi yi; destruct xi; destruct yi; [easy..|].
now unfold convert; case (_ && _).
Qed.

Lemma mul_propagate_r : forall prec, propagate_r (mul prec).
Proof.
intros prec xi yi; destruct xi; destruct yi; [easy..|].
now unfold convert; case (_ && _).
Qed.

Lemma div_propagate_r : forall prec, propagate_r (div prec).
Proof.
intros prec xi yi; destruct xi; destruct yi; [easy..|].
now unfold convert; case (_ && _).
Qed.

Lemma nearbyint_correct :
  forall mode, extension (Xnearbyint mode) (nearbyint mode).
Proof.
intros mode [|xl xu] [|xr] ;
  try ( intros ; exact I ) ;
  [now unfold convert; case (_ && _)|].
simpl.
intros Hlu.
generalize Hlu.
case_eq (F.valid_lb xl); [|intros _ [H0 H1]; exfalso; lra].
case_eq (F.valid_ub xu); [|intros _ _ [H0 H1]; exfalso; lra].
intros Vu Vl [Hl Hu].
unfold convert.
rewrite (proj1 (F.nearbyint_DN_correct _ _)).
rewrite (proj1 (F.nearbyint_UP_correct _ _)).
split.
{ xreal_tac2.
  generalize (F.nearbyint_DN_correct mode xl).
  rewrite X.
  unfold le_lower, le_upper; simpl.
  xreal_tac2; [easy|]; simpl.
  intros [_ H].
  now apply (Rle_trans _ _ _ (Ropp_le_cancel _ _ H)), Rnearbyint_le. }
xreal_tac2.
generalize (F.nearbyint_UP_correct mode xu).
rewrite X.
unfold le_upper; simpl.
xreal_tac2; [easy|]; simpl.
intros [_ H].
now revert H; apply Rle_trans, Rnearbyint_le.
Qed.

End FloatInterval.
