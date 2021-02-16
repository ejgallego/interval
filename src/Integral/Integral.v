(**
This file is part of the Coq.Interval library for proving bounds of
real-valued expressions in Coq: http://coq-interval.gforge.inria.fr/

Copyright (C) 2015-2016, Inria

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

From Coq Require Import Reals List Psatz.
From Coquelicot Require Import Coquelicot.
From mathcomp.ssreflect Require Import ssreflect ssrfun ssrbool.

Require Import Stdlib.
Require Import Coquelicot.
Require Import Xreal.
Require Import Interval.
Require Import Taylor_model.
Require Import Interval_compl.

Section Missing.

Lemma filter_prod_at_point_infty :
  forall a (P : R -> R -> Prop),
  (forall x y, a <= x <= y -> P x y) ->
  filter_prod (at_point a) (Rbar_locally p_infty)
  (fun ab : R * R => P ab.1 ab.2).
Proof.
intros a P HP.
apply (Filter_prod _ _ _ (fun x => x = a) (fun x => a < x)).
- easy.
- now exists a.
- move => x y -> /= H.
  apply HP.
  split.
  apply Rle_refl.
  now apply Rlt_le.
Qed.

Lemma filter_prod_at_point :
  forall {T F} { FF : Filter F} a (P : R -> T -> Prop) Q,
  F Q ->
  (forall y, Q y -> P a y) ->
  filter_prod (at_point a) F
  (fun ab : R * T => P ab.1 ab.2).
Proof.
intros T F FF a P Q FQ HQ.
apply: (Filter_prod _ _ _ (fun x => x = a) Q) => // .
- move => x y -> /= H.
  exact: HQ.
Qed.

Lemma filter_prod_at_point_l :
  forall {T F} { FF : Filter F} a (P : T -> R -> Prop) Q,
  F Q ->
  (forall y, Q y -> P y a) ->
  filter_prod F (at_point a)
  (fun ab : T * R => P ab.1 ab.2).
Proof.
intros T F FF a P Q FQ HQ.
apply: (Filter_prod _ _ _ Q (fun x => x = a)) => // .
- move => x y /= H ->.
  exact: HQ.
Qed.

Lemma at_point_filter_prod :
  forall {T F} { FF : Filter F} a (P : R -> T -> Prop),
  filter_prod (at_point a) F
              (fun ab : R * T => P ab.1 ab.2) ->
  F (P a).
Proof.
move => T F FF a P [Q R inQ inR H].
apply: filter_imp inR.
move => x; exact: H.
Qed.

Lemma at_point_filter_prod_l :
  forall {T F} { FF : Filter F} a (P : T -> R -> Prop),
  filter_prod F (at_point a)
              (fun ab : T * R => P ab.1 ab.2) ->
  F (fun y => P y a).
Proof.
move => T F FF a P [Q R inQ inR H].
apply: filter_imp inQ.
move => x /= HQ; apply: H => // .
Qed.

Lemma filterlimi_const_loc {T} {U : UniformSpace}
  {F : (T -> Prop) -> Prop} {FF : Filter F} :
  forall (f : T -> U -> Prop) (a : U),
  F (fun x => f x a) ->
  filterlimi f F (locally a).
Proof.
intros f a Hf P HP.
rewrite /filtermapi /=.
apply: filter_imp Hf => x H.
exists a.
apply (conj H).
exact: locally_singleton.
Qed.

Lemma filterlimi_const {T} {U : UniformSpace}
  {F : (T -> Prop) -> Prop} {FF : Filter F} :
  forall (f : T -> U -> Prop) (a : U),
  (forall x, f x a) ->
  filterlimi f F (locally a).
Proof.
intros f a Hf.
apply filterlimi_const_loc.
exact: filter_forall.
Qed.

Lemma is_RInt_gen_0 {Fa Fb : (R -> Prop) -> Prop}
  {FFa : Filter Fa} {FFb : Filter Fb} :
  is_RInt_gen (fun y => 0) Fa Fb zero.
Proof.
apply: filterlimi_const.
intros [a b].
rewrite -(scal_zero_r (b - a)).
exact: is_RInt_const.
Qed.

(* TODO: find better name *)
Lemma is_RInt_gen_filterlim {V : CompleteNormedModule R_AbsRing}
  {Fa Fb : (R -> Prop) -> Prop}
  {FFa : ProperFilter Fa} {FFb : ProperFilter Fb} (f : R -> V) (lf : V) :
  is_RInt_gen f Fa Fb lf ->
  filterlim (fun x => RInt f x.1 x.2) (filter_prod Fa Fb) (locally lf).
Proof.
move => Hlf P HlfP.
have := (Hlf P HlfP).
case => Q R HFa HFb.
econstructor.
exact: HFa.
exact: HFb.
move => x y HQx HRy.
case : (p x y HQx HRy) => x0 [HRInt HP].
by move: (is_RInt_unique f x y _ HRInt ) => ->.
Qed.

(* very inelegant *)
Lemma ex_RInt_ex_RInt_gen {V : CompleteNormedModule R_AbsRing}
  {Fa Fb : (R -> Prop) -> Prop}
  {FFa : ProperFilter Fa} {FFb : ProperFilter Fb} (f : R -> V) :
  ex_RInt_gen f Fa Fb ->
  (filter_prod Fa Fb (fun ab => ex_RInt f ab.1 ab.2)).
Proof.
intros [lf Hlf].
have := (Hlf (fun _ => True)).
case. now exists (mkposreal _ Rlt_0_1).
move => Q R HFaQ HFbR His_RInt.
apply: Filter_prod HFaQ HFbR _.
move => x y HQx HRy.
case: (His_RInt x y HQx HRy) => I [H _].
now exists I.
Qed.

(* very inelegant again *)
(* we probably want a more general lemma linking filterlim and filterlimi *)
Lemma RInt_gen_le {Fa Fb : (R -> Prop) -> Prop}
  {FFa : ProperFilter Fa} {FFb : ProperFilter Fb} (f : R -> R) (g : R -> R) (lf : R) (lg : R) :
  filter_prod Fa Fb (fun ab => fst ab <= snd ab)
  -> filter_prod Fa Fb (fun ab => forall x, fst ab <= x <= snd ab -> f x <= g x)
  -> is_RInt_gen f Fa Fb lf -> is_RInt_gen g Fa Fb lg
    -> lf <= lg.
Proof.
move => Hab Hle.
move => Hlf Hlg.
apply (filterlim_le (F := filter_prod Fa Fb) (fun x => RInt f x.1 x.2) (fun x => RInt g x.1 x.2) lf lg).
apply: (filter_imp (fun x => ex_RInt f x.1 x.2 /\ ex_RInt g x.1 x.2 /\ (forall y, x.1 <= y <= x.2 -> f y <= g y) /\ x.1 <= x.2)).
move => x [H1 [H2 [H3 H4]]].
apply: RInt_le => // .
move => x0 Hx0. have:= H3 x0. apply.
by split; now apply Rlt_le.
apply: filter_and.
apply: ex_RInt_ex_RInt_gen.
now exists lf.
apply: filter_and.
apply: ex_RInt_ex_RInt_gen.
now exists lg.
apply: filter_and => // .
exact: is_RInt_gen_filterlim.
exact: is_RInt_gen_filterlim.
Qed.

Lemma ex_RInt_gen_cauchy {V : CompleteNormedModule R_AbsRing}
  {Fb : (R -> Prop) -> Prop} {FFb : ProperFilter Fb}
  (a : R) (f : R -> V) :
  ex_RInt_gen f (at_point a) Fb <->
  (filter_prod (at_point a) Fb (fun ab => ex_RInt f ab.1 ab.2) /\
   forall eps : posreal, exists P,
     Fb P /\
     (forall u v,
        P u -> P v ->
        forall I, is_RInt f u v I -> norm I <= eps)).
Proof.
split.
- intros [If HIf].
  split.
  apply ex_RInt_ex_RInt_gen.
  now exists If.
  move => eps.
  exists (fun x => ex_RInt f a x /\ forall I, is_RInt f a x I -> ball_norm If (pos_div_2 eps) I).
  split.
    - assert (Hb: locally If (ball_norm If (pos_div_2 eps))).
      exact: locally_ball_norm.
      have toto := (HIf _ Hb).
      rewrite /filtermapi in toto.
      pose K x1 x2 :=
        exists y : V, is_RInt f x1 x2 y /\
                      ball_norm If (pos_div_2 eps) y.
      assert (titi := at_point_filter_prod a K toto).
      + apply: filter_and.
        apply: filter_imp titi => x.
        rewrite /K; case => y [Hy _].
        by eexists; exact Hy.
      apply: filter_imp titi => x [y [Hy1 Hy2]] I HI.
      rewrite -(is_RInt_unique _ _ _ _ HI).
      by rewrite  (is_RInt_unique _ _ _ _ Hy1).
    - move => u v [Hau Hu] [Hvu Hv] I HI.
      suff Hfau : is_RInt f a u (RInt f a u).
      suff Hfav : is_RInt f a v (RInt f a v).
      suff -> : (I = plus (minus If (RInt f a u)) (minus (RInt f a v) If))%R.
      rewrite /ball_norm.
      rewrite /minus.
      suff -> : (pos eps%R = (pos (pos_div_2 eps)) + (pos (pos_div_2 eps)))%R.
      apply :Rle_trans. apply: (norm_triangle).
      apply: Rle_trans.
        apply: Rplus_le_compat_l.
        move: (Hv _ Hfav). rewrite /ball_norm /minus.
        exact: Rlt_le.
      apply: Rplus_le_compat_r.
      move: (Hu _ Hfau). rewrite /ball_norm /minus.
      rewrite -{2}[If]opp_opp -opp_plus norm_opp plus_comm.
      exact: Rlt_le.
      rewrite /pos_div_2 /=; lra.
      rewrite -opp_minus -[minus (RInt f a v) If]opp_minus. rewrite -opp_plus.
      rewrite -minus_trans /minus -opp_RInt_swap. rewrite opp_plus !opp_opp.
      rewrite RInt_Chasles. symmetry; apply: is_RInt_unique => // .
      apply: ex_RInt_swap; eexists; exact: Hfau.
      eexists; exact: Hfav.
      apply: ex_RInt_swap; eexists; exact: Hfau.
      apply: RInt_correct => // .
      apply: RInt_correct => // .
- intros [Hab Hb].
  refine (proj1 (filterlimi_locally_cauchy _ _) _).
    apply: filter_imp Hab.
    move => /= [a' b'] /= HIf.
    apply (conj HIf).
    intros y1 y2 H1 H2.
    rewrite -(is_RInt_unique _ _ _ _ H1).
    exact: is_RInt_unique.
  intros eps.
  destruct (Hb (pos_div_2 eps)) as [Qb [FbQb H]].
  exists (fun ab => ab.1 = a /\ Qb ab.2).
  split.
    eexists (fun x => x = a) _.
    easy.
    exact: FbQb.
    easy.
  intros [u1 u2] [v1 v2] [-> Qbu2] [-> Qbv2] I1 I2 HI1 HI2.
  apply: norm_compat1.
  unfold minus.
  apply is_RInt_swap in HI1.
  have HC := (is_RInt_Chasles _ _ _ _ _ _ HI1 HI2).
  rewrite plus_comm.
  move: (H _ _ Qbu2 Qbv2) => /= .
  move => /(_ _ HC) Hle.
  apply: Rle_lt_trans Hle _.
  move: (cond_pos eps); lra.
Qed.

(* this proof should be much shorter *)
Lemma ex_RInt_gen_cauchy_left {V : CompleteNormedModule R_AbsRing}
  {Fb : (R -> Prop) -> Prop} {FFb : ProperFilter Fb}
  (a : R) (f : R -> V) :
  ex_RInt_gen f Fb (at_point a) <->
  (filter_prod Fb (at_point a) (fun ab => ex_RInt f ab.1 ab.2) /\
   forall eps : posreal, exists P,
     Fb P /\
     (forall u v,
        P u -> P v ->
        forall I, is_RInt f u v I -> norm I <= eps)).
Proof.
split.
- move => [I HI].
  have Hswap : ex_RInt_gen (fun x => opp (f x)) (at_point a) Fb.
    apply is_RInt_gen_swap,is_RInt_gen_opp in HI.
    by eexists; exact: HI.
  case ((proj1 (ex_RInt_gen_cauchy a (fun x => opp (f x)))) Hswap) => Hprod Hint.
  split.
  + case: Hprod => Q R HQ HR H.
    econstructor.
    * exact: HR.
    * exact: HQ.
    * move => x y Hx Hy /= .
      case: (H y x Hy Hx) => /= I1 HI1.
      eexists; apply: is_RInt_swap.
      apply: is_RInt_ext => [x1 Hx1|]; first by rewrite -[f x1]opp_opp.
      by apply: is_RInt_opp; exact: HI1.
  + move => eps; case: (Hint eps) => Peps [HFeps HRInt].
    exists Peps; split => // .
    move => u v Hu Hv I0 HI0.
    case: (HRInt u v Hu Hv (opp I0)).
    exact: is_RInt_opp.
    by rewrite norm_opp; lra.
    by rewrite norm_opp; lra.
- move => [Hfilter HInt].
  eexists.
  apply: is_RInt_gen_swap.
  case: (proj2 (ex_RInt_gen_cauchy a f)).
  split.
  + case: Hfilter => Q R HQ HR Hex.
    apply: (Filter_prod).
      * exact: HR.
      * exact: HQ.
      * move => x y Rx Qy; apply: ex_RInt_swap; exact: Hex.
  + move => eps; case: (HInt eps) => Peps [HFPeps His_RInt].
    exists Peps ;split => // .
  + move => x Hx. apply RInt_gen_correct.
    eexists. exact: Hx.
Qed.

Lemma at_right_le_at_point a b (Hab : a < b) : (filter_prod (at_right a) (at_point b) (fun x => x.1 <= x.2)).
Proof.
pose Q x := a < x < b.
pose R x := x = b.
apply: (Filter_prod _ _ _ Q R) => // .
rewrite /at_right /within /locally.
pose epsilon := (b - a).
have Hepspos : 0 < epsilon by rewrite /epsilon; lra.
pose eps := mkposreal epsilon Hepspos.
exists (pos_div_2 eps) => y.
by move/ball_to_lra; rewrite /Q; rewrite  /= /epsilon; lra.
move => x y . rewrite /Q /R /=.  lra.
Qed.

Lemma RInt_gen_pos (* {V : CompleteNormedModule R_AbsRing} *)
  {Fa : (R -> Prop) -> Prop} {FFa : ProperFilter Fa}
  {Fb : (R -> Prop) -> Prop} {FFb : ProperFilter Fb}
  (P Q : R -> Prop) (f : R -> R) (If : R) :
  (Fa P) ->
  (Fb Q) ->
  (forall x y z, P x -> Q y -> x <= z <= y -> 0 <= f z) ->
  filter_prod Fa Fb (fun ab : R * R => ab.1 <= ab.2) ->
  is_RInt_gen f Fa Fb If ->
  0 <= If.
Proof.
  move => HFa HFb Hfx Hle Hint.
  have -> : 0 = norm 0 by rewrite norm_zero.
  apply: (RInt_gen_norm (fun _ => 0) f 0 If _ _ _ Hint) => // .
  apply: (Filter_prod _ _ _ P Q HFa HFb) => x y HPx HQy x0 /= Hx0.
  rewrite norm_zero; apply: (Hfx _ _ _ HPx HQy) => // .
  exact: is_RInt_gen_0.
Qed.


Lemma RInt_gen_neg (* {V : CompleteNormedModule R_AbsRing} *)
  {Fa : (R -> Prop) -> Prop} {FFa : ProperFilter Fa}
  {Fb : (R -> Prop) -> Prop} {FFb : ProperFilter Fb}
  (P Q : R -> Prop) (f : R -> R) (If : R) :
  (Fa P) ->
  (Fb Q) ->
  (forall x y z, P x -> Q y -> x <= z <= y -> f z <= 0) ->
  filter_prod Fa Fb (fun ab : R * R => ab.1 <= ab.2) ->
  is_RInt_gen f Fa Fb If ->
  If <= 0.
Proof.
  move => HFa HFb Hfx Hle Hint.
  (* have -> : 0 = norm 0 by rewrite norm_zero. *)
  apply is_RInt_gen_opp in Hint.
  suff: 0 <= opp If.
    by rewrite /opp /=; lra.
  apply: (@RInt_gen_pos Fa FFa Fb FFb P Q (fun x => opp (f x)) (opp If)) => // .
  move => x y z HPx HQy Hxzy; move: (Hfx x y z HPx HQy Hxzy).
  by rewrite /opp /=; lra.
Qed.

End Missing.

Module IntegralTactic (I : IntervalOps).

Module J := IntervalExt I.

(* this can probably be significantly shortened *)
Lemma bounded_ex {xi} (Hne : not_empty (I.convert xi)) (Hbnded : I.bounded xi) :
  (exists l u : R, I.convert xi = Ibnd (Xreal l) (Xreal u)).
Proof.
exists (proj_val (I.F.convert (I.lower xi))).
exists (proj_val (I.F.convert (I.upper xi))).
have := (I.bounded_correct xi).
rewrite Hbnded; case => // .
move => Hlb Hub.
case: (I.lower_bounded_correct xi Hlb) => <- => /= HbndedProp.
case: (I.upper_bounded_correct xi Hub) => <-.
by rewrite /I.bounded_prop; apply.
Qed.

Lemma at_right_open_interval a lb : (lb < a) -> at_right lb (fun x : R => lb < x < a).
Proof.
move => Hlba. rewrite /at_right /within /locally.
pose epsilon := (a - lb).
have Hepspos : 0 < epsilon by rewrite /epsilon; lra.
pose eps := mkposreal epsilon Hepspos.
exists (pos_div_2 eps) => y.
by move/ball_to_lra; rewrite /= /epsilon; lra.
Qed.

Lemma at_right_semi_open_interval a lb : (lb < a) -> at_right lb (fun x : R => lb < x <= a).
Proof.
move => Hlba. rewrite /at_right /within /locally.
pose epsilon := (a - lb).
have Hepspos : 0 < epsilon by rewrite /epsilon; lra.
pose eps := mkposreal epsilon Hepspos.
exists (pos_div_2 eps) => y.
by move/ball_to_lra; rewrite /= /epsilon; lra.
Qed.

Definition constant_sign (S : R -> Prop) (f : R -> R) :=
  (forall x, S x -> 0 <= f x) \/ (forall x, S x -> f x <= 0).


Lemma is_RInt_le_0 :
forall (f : R -> R) (a b If : R),
a <= b ->
is_RInt f a b If -> (forall x : R, a < x < b -> f x <= 0) -> If <= 0.
Proof.
move => f a b If leab fint fneg.
suff: (0 <= -If) by lra.
apply: (is_RInt_ge_0 (fun x => - (f x)) a b _ leab).
  exact: is_RInt_opp.
by move => x Hx; move: (fneg x Hx); lra.
Qed.

Lemma is_RInt_const_sign (f : R -> R) (If : R) a b (le_ab : a <= b) :
  constant_sign (fun x => Rmin a b <= x <= Rmax a b) f ->
  is_RInt f a b If ->
  is_RInt (fun x => Rabs (f x)) a b (Rabs If).
Proof.
move => cst_sgn fint.
case: cst_sgn => [f_pos|f_neg].
- have Habs : forall x , Rmin a b < x < Rmax a b -> f x = Rabs (f x).
    by move => x Hx; rewrite Rabs_pos_eq //; apply: f_pos; lra.
  apply: (is_RInt_ext f _ _ _ _ Habs).
  rewrite Rabs_pos_eq // .
    apply: (is_RInt_ge_0 f a b If le_ab fint).
      by move => x Hx; apply: f_pos; rewrite Rmin_left ?Rmax_right; lra.
- have Habs : forall x , Rmin a b < x < Rmax a b -> - (f x) = Rabs (f x).
    by move => x Hx; rewrite Rabs_left1 //; apply: f_neg; lra.
  apply: (is_RInt_ext _ _ _ _ _ Habs).
  rewrite Rabs_left1.
  apply: is_RInt_opp => // .
  apply: (is_RInt_le_0 _ a b _ le_ab) => // .
    exact: fint.
    move => x Hx. apply: f_neg. rewrite Rmin_left ?Rmax_right; lra.
Qed.

Lemma integral_interval_mul_sing :
  forall prec sing a ia f fi g Ig Igi,
  (sing < a) ->
  contains (I.convert ia) (Xreal a) ->
  (forall x, sing <= x <= a -> contains (I.convert fi) (Xreal (f x))) ->
  I.bounded fi ->
  (forall x, sing <= x <= a -> continuous f x) ->
  (forall x, sing < x <= a -> continuous g x) ->
  constant_sign (fun x => sing < x <= a) g ->
  is_RInt_gen g (at_right sing) (at_point a) Ig ->
  contains (I.convert Igi) (Xreal Ig) ->
  exists Ifg,
  is_RInt_gen (fun t => f t * g t) (at_right sing) (at_point a) Ifg /\
  contains (I.convert (I.mul prec fi Igi)) (Xreal Ifg).
Proof.
move => prec sing a ia f fi g Ig Igi H0a Hia Hf Hfi Cf Cg Hg HIg HIg'.

have Hnefi : not_empty (I.convert fi).
{ now exists (f sing); apply Hf; split; [right|left]. }

move: (bounded_ex Hnefi Hfi) => [] l [] u HiFia.
have Hgoodorder_bis : forall x, sing <= x <= a -> l <= f x <= u.
  move => x0 Hax0.
  move: (Hf _ Hax0).
  by rewrite HiFia.
suff [Ifg HIfg]: ex_RInt_gen (fun t => f t * g t) (at_right sing) (at_point a).
  exists Ifg.
  have HIntl : is_RInt_gen (fun x => scal l (g x)) (at_right sing) (at_point a)  (scal l Ig).
    exact: is_RInt_gen_scal.
  have HIntu : is_RInt_gen (fun x => scal u (g x)) (at_right sing) (at_point a) (scal u Ig).
    exact: is_RInt_gen_scal.
  have Hgoodorder : l <= u.
    by case: (Hgoodorder_bis a); try lra.
  apply: (conj HIfg).

  case: Hg => [Hg|Hg]; last first.

  apply: (contains_connected _ (scal u Ig) (scal l Ig)).
  + apply: J.mul_correct => // .
    rewrite HiFia.
    exact: (conj _ (Rle_refl _)).
  + apply: J.mul_correct => // .
    rewrite HiFia.
    exact: (conj (Rle_refl _)).
  split.
    apply: (@RInt_gen_le (at_right sing) (at_point a) _ _ (fun x => scal u (g x)) (fun x => scal (f x) (g x))  _ _) => // .
      exact: at_right_le_at_point.
    apply: (filter_prod_at_point_l a (fun x y => forall z, x <= z <= y -> _ <= _) (fun z => sing < z < a)).
      exact: at_right_open_interval.
    by move => y Hy z Hz; apply: Rmult_le_compat_neg_r; case: (Hg z) (Hgoodorder_bis z); lra.

    apply: (@RInt_gen_le (at_right sing) (at_point a) _ _ (fun x => scal (f x) (g x)) (fun x => scal l (g x))  _ _) => // .
      exact: at_right_le_at_point.
    apply: (filter_prod_at_point_l a (fun x y => forall z, x <= z <= y -> _ <= _) (fun z => sing < z < a)).
      exact: at_right_open_interval.
    by move => y Hy z Hz; apply: Rmult_le_compat_neg_r; case: (Hg z) (Hgoodorder_bis z); lra.

  (* second case: 0 <= g x *)
      apply: (contains_connected _ (scal l Ig) (scal u Ig)).
  + apply: J.mul_correct => // .
    rewrite HiFia.
    exact: (conj (Rle_refl _)).
  + apply: J.mul_correct => // .
    rewrite HiFia.
    exact: (conj _ (Rle_refl _)).
  split.
    apply: (@RInt_gen_le (at_right sing) (at_point a) _ _ (fun x => scal l (g x)) (fun x => scal (f x) (g x))  _ _) => // .
      exact: at_right_le_at_point.
    apply: (filter_prod_at_point_l a (fun x y => forall z, x <= z <= y -> _ <= _) (fun z => sing < z < a)).
      exact: at_right_open_interval.
    by move => y Hy z Hz; apply: Rmult_le_compat_r; case: (Hg z) (Hgoodorder_bis z); lra.

    apply: (@RInt_gen_le (at_right sing) (at_point a) _ _ (fun x => scal (f x) (g x)) (fun x => scal u (g x))  _ _) => // .
      exact: at_right_le_at_point.
    apply: (filter_prod_at_point_l a (fun x y => forall z, x <= z <= y -> _ <= _) (fun z => sing < z < a)).
      exact: at_right_open_interval.
    by move => y Hy z Hz; apply: Rmult_le_compat_r; case: (Hg z) (Hgoodorder_bis z); lra.


refine (proj2 (ex_RInt_gen_cauchy_left _ _) _).
split.
- apply: filter_prod_at_point_l; first exact: (at_right_open_interval a).
  move => y Hxay; apply: ex_RInt_continuous => z Hz.
  rewrite Rmin_left in Hz; last by lra.
  rewrite Rmax_right in Hz; last by lra.
  apply: continuous_mult.
    by apply: Cf; lra.
    by apply: Cg; lra.
- move => eps.
  set eps1 := eps / (1 + Rmax (Rabs l) (Rabs u)).
  have Hmaxpos : 1 + Rmax (Rabs l) (Rabs u) > 0.
    by rewrite /Rmax; case: Rle_dec; move: (Rabs_pos u) (Rabs_pos l); lra.
  have eps1_pos : 0 < eps1.
    by apply: RIneq.Rdiv_lt_0_compat => // ; first apply: cond_pos eps.
  set pos_eps1 := mkposreal eps1 eps1_pos.
  case: (proj1 (ex_RInt_gen_cauchy_left _ _) (ex_intro _ _  HIg)) => Hexg Heps.
  case: (Heps (pos_eps1)) => Peps1 [HPinf HPint].
  have HPge : at_right sing (fun x => sing < x < a).
    exact: at_right_open_interval.
  assert(Hand := filter_and _ _ (at_point_filter_prod_l _ _ Hexg) HPinf).
  assert(Hand1 := filter_and _ _ Hand HPge).
  eexists; split. exact: Hand1.
  move => u0 v0 [[Hu1 Hu2] Hule] [[Hv1 Hv2] Hvle] I HisInt.
  wlog : I u0 v0 Hv1 Hv2 Hvle HisInt Hu1 Hu2 Hule / (u0 <= v0).
    move => Hwlog.
    case: (Rle_dec v0 u0) => Huv; last first.
      by apply: (Hwlog _ u0 v0 Hv1) => // ; lra.
    rewrite -norm_opp.
    apply: (Hwlog (opp I) v0 u0) => // .
    exact: is_RInt_swap.
  move => Hu0v0.

  have [Ig' HIg'']: ex_RInt g u0 v0.
    apply: ex_RInt_Chasles. exact: Hu1.
    exact: ex_RInt_swap.
  move: (HPint u0 v0 Hu2 Hv2 Ig' HIg'') => {HPint} HPint.
  suff Hineq: norm I <= (1 + Rmax (Rabs l) (Rabs u)) * norm Ig'.
    apply: Rle_trans Hineq _.
    rewrite /pos_eps1 /eps1 /=  in HPint.
    have ->: eps = (1 + Rmax (Rabs l) (Rabs u)) * (eps / (1 + Rmax (Rabs l) (Rabs u))) :> R .
      by field; lra.
    by apply: Rmult_le_compat_l HPint; lra.
  apply: norm_RInt_le HisInt _; first lra.
    move => x Hx.
    2: {
      apply: is_RInt_scal.
      apply: (is_RInt_const_sign g) => // .
        case: Hg => [gpos | gneg]; [left|right] => x Hx.
          by apply: gpos; move: Hx; rewrite Rmin_left ?Rmax_right; lra.
        by apply: gneg; move: Hx; rewrite Rmin_left ?Rmax_right; lra.
    }
  rewrite /=.
  eapply Rle_trans.
    exact: norm_scal.
  rewrite /norm /= /abs /= .
  apply: Rmult_le_compat_r; first exact: Rabs_pos.
  have Hax : sing <= x <= a by lra.
  suff: Rabs (f x) <= Rmax (Rabs l) (Rabs u) by lra.
    by apply: RmaxAbs; move: (Hgoodorder_bis x Hax) ;lra.
Qed.






Lemma integral_interval_mul_zero :
  forall prec a ia f fi g Ig Igi,
  (0 < a) ->
  contains (I.convert ia) (Xreal a) ->
  (forall x, 0 <= x <= a -> contains (I.convert fi) (Xreal (f x))) ->
  I.bounded fi ->
  (forall x, 0 <= x <= a -> continuous f x) ->
  (forall x, 0 < x <= a -> continuous g x) ->
  constant_sign (fun x => 0 < x <= a) g ->
  is_RInt_gen g (at_right 0) (at_point a) Ig ->
  contains (I.convert Igi) (Xreal Ig) ->
  exists Ifg,
  is_RInt_gen (fun t => f t * g t) (at_right 0) (at_point a) Ifg /\
  contains (I.convert (I.mul prec fi Igi)) (Xreal Ifg).
Proof.
move => prec a ia f fi g Ig Igi H0a Hia Hf Hfi Cf Cg Hg HIg HIg'.
apply: (integral_interval_mul_sing) => // ; last exact: HIg'; last exact: HIg.
exact: Hia.
Qed.


Lemma integral_interval_mul_infty :
  forall prec a ia f fi g Ig Igi,
  contains (I.convert ia) (Xreal a) ->
  (forall x, a <= x -> contains (I.convert fi) (Xreal (f x))) ->
  I.bounded fi ->
  (forall x, a <= x -> continuous f x) ->
  (forall x, a <= x -> continuous g x) ->
  (forall x, a <= x -> 0 <= g x) ->
  is_RInt_gen g (at_point a) (Rbar_locally p_infty) Ig ->
  contains (I.convert Igi) (Xreal Ig) ->
  exists Ifg,
  is_RInt_gen (fun t => f t * g t) (at_point a) (Rbar_locally p_infty) Ifg /\
  contains (I.convert (I.mul prec fi Igi)) (Xreal Ifg).
Proof.
move => prec a ia f fi g Ig Igi Hia Hf Hfi Cf Cg Hg HIg HIg'.
have Hnefi : not_empty (I.convert fi).
{ now exists (f a); apply Hf; right. }
move: (bounded_ex Hnefi Hfi) => [] l [] u HiFia.
have Hgoodorder_bis : forall x, a <= x -> l <= f x <= u.
  move => x0 Hax0.
  move: (Hf _ Hax0).
  by rewrite HiFia.
suff [Ifg HIfg]: ex_RInt_gen (fun t => f t * g t) (at_point a) (Rbar_locally p_infty).
  exists Ifg.
  have HIntl : is_RInt_gen (fun x => scal l (g x)) (at_point a) (Rbar_locally p_infty) (scal l Ig).
    by apply: is_RInt_gen_scal.
  have HIntu : is_RInt_gen (fun x => scal u (g x)) (at_point a) (Rbar_locally p_infty) (scal u Ig).
    by apply: is_RInt_gen_scal.
  have Hgoodorder : l <= u.
    move: (Hgoodorder_bis a (Rle_refl a)).
    move => [H1 H2].
    exact: Rle_trans H1 H2.
  have intgpos : 0 <= Ig.
    apply: (@RInt_gen_pos (at_point a) _ (Rbar_locally p_infty) _ (fun x => x = a) (fun y => y > a) g) => // .
      by rewrite /= ; exists a => x; lra.
    by move => x y z Hxa Hya Hxz; apply: Hg; lra.
    now apply filter_prod_at_point_infty.
  apply: (conj HIfg).
  apply: (contains_connected _ (scal l Ig) (scal u Ig)).
  + apply: J.mul_correct => // .
    rewrite HiFia.
    exact: (conj (Rle_refl _)).
  + apply: J.mul_correct => // .
    rewrite HiFia.
    exact: conj (Rle_refl _).
  split.
    apply: (@RInt_gen_le (at_point a) (Rbar_locally p_infty) _ _ (fun x => scal l (g x)) (fun x => scal (f x) (g x)) _ _) => // .
      now apply filter_prod_at_point_infty. (* now and by behave differently here *)
    apply (filter_prod_at_point_infty a (fun x y => forall z, x <= z <= y -> _ <= _)).
    move => m n [Hm _] o [Ho _].
    rewrite /scal /= /mult /= .
    apply: Rmult_le_compat_r => // .
      apply Hg.
      now apply Rle_trans with m.
    apply Hgoodorder_bis.
    now apply Rle_trans with m.
  apply: (@RInt_gen_le (at_point a) (Rbar_locally p_infty) _ _ (fun x => scal (f x) (g x)) (fun x => scal u (g x)) _ _) => // .
    now apply filter_prod_at_point_infty.
  apply (filter_prod_at_point_infty a (fun x y => forall z, x <= z <= y -> _ <= _)).
  move => m n [Hm _] o [Ho _].
  rewrite /scal /= /mult /= .
  apply: Rmult_le_compat_r => // .
    apply Hg.
    now apply Rle_trans with m.
  apply Hgoodorder_bis.
  now apply Rle_trans with m.
refine (proj2 (ex_RInt_gen_cauchy _ _) _).
split.
- apply: filter_prod_at_point_infty.
  move => x y Hxay; apply: ex_RInt_continuous => z Hz.
  rewrite Rmin_left in Hz; last by lra.
  rewrite Rmax_right in Hz; last by lra.
  apply: continuous_mult.
    by apply: Cf; lra.
    by apply: Cg; lra.
- move => eps.
  set eps1 := eps / (1 + Rmax (Rabs l) (Rabs u)).
  have Hmaxpos : 1 + Rmax (Rabs l) (Rabs u) > 0.
    by rewrite /Rmax; case: Rle_dec; move: (Rabs_pos u) (Rabs_pos l); lra.
  have eps1_pos : 0 < eps1.
    by apply: RIneq.Rdiv_lt_0_compat => // ; first apply: cond_pos eps.
  set pos_eps1 := mkposreal eps1 eps1_pos.
  case: (proj1 (ex_RInt_gen_cauchy _ _) (ex_intro _ _  HIg)) => Hexg Heps.
  case: (Heps (pos_eps1)) => Peps1 [HPinf HPint].
  have HPge : Rbar_locally p_infty (fun x => a <= x).
    by exists a => x; lra.
  assert(Hand := filter_and _ _ (at_point_filter_prod _ _ Hexg) HPinf).
  assert(Hand1 := filter_and _ _ Hand HPge).
  eexists; split. exact: Hand1.
  move => u0 v0 [[Hu1 Hu2] Hule] [[Hv1 Hv2] Hvle] I HisInt.
  wlog : I u0 v0 Hv1 Hv2 Hvle HisInt Hu1 Hu2 Hule / (u0 <= v0).
    move => Hwlog.
    case: (Rle_dec v0 u0) => Huv; last first.
      by apply: (Hwlog _ u0 v0 Hv1) => // ; lra.
    rewrite -norm_opp.
    apply: (Hwlog (opp I) v0 u0) => // .
    exact: is_RInt_swap.
  move => Hu0v0.

  have [Ig' HIg'']: ex_RInt g u0 v0.
    apply: ex_RInt_Chasles Hv1.
    exact: ex_RInt_swap.
  have Ig'pos : 0 <= Ig'.
    apply: (is_RInt_le (fun _ => zero) g) Hu0v0 _ HIg'' _.
    have -> : 0 = scal (v0 - u0) zero by rewrite scal_zero_r.
    by apply: is_RInt_const.
    by move => x Hx; apply: Hg; lra.
  move: (HPint u0 v0 Hu2 Hv2 Ig' HIg'') => {HPint} HPint.
  suff Hineq: norm I <= (1 + Rmax (Rabs l) (Rabs u)) * norm Ig'.
    apply: Rle_trans Hineq _.
    rewrite /pos_eps1 /eps1 /=  in HPint.
    have ->: eps = (1 + Rmax (Rabs l) (Rabs u)) * (eps / (1 + Rmax (Rabs l) (Rabs u))) :> R .
      by field; lra.
    by apply: Rmult_le_compat_l HPint; lra.
  apply: norm_RInt_le HisInt _; first lra.
    move => x Hx.
    2: {
    apply: is_RInt_scal.
      suff -> : norm Ig' = Ig'.
        exact: HIg''.
      by rewrite /norm /= /abs /=; rewrite Rabs_right //; lra.
    }
  rewrite /=.
  eapply Rle_trans.
    exact: norm_scal.
  rewrite /norm /= /abs /= .
  rewrite (Rabs_pos_eq (g x)).
  apply: Rmult_le_compat_r; first by (apply: Hg; lra).
  have Hax : a <= x by lra.
  suff: Rabs (f x) <= Rmax (Rabs l) (Rabs u) by lra.
    by apply: RmaxAbs; move: (Hgoodorder_bis x Hax) ;lra.
  by apply: Hg; lra.
Qed.

End IntegralTactic.

Module IntegralTaylor (I : IntervalOps).

Module J := IntervalExt I.
Module TM := TM I.

Section DepthZeroPol.

(* A fixed precision *)
Variable prec : I.precision.

Variables (f : R -> R) (iF : I.type -> I.type).

Hypothesis HiFIntExt : forall xi x, contains (I.convert xi) (Xreal x) -> contains (I.convert (iF xi)) (Xreal (f x)).

Variable Mf : TM.TMI.rpa.
Variables X : I.type.
Let x0 := proj_val (I.F.convert (I.midpoint X)).
Let X0 := J.midpoint X.
Let iX := I.convert X.
Let iX0 := I.convert X0.

Hypothesis validMf : TM.TMI.i_validTM x0 iX Mf (fun x => Xreal (f x)).

Variables (a b : R).

(* f is integrable on [a, b]*)
Hypothesis Hintegrable : ex_RInt f a b.

Variables ia ib : I.type.

Hypothesis Hconta : contains (I.convert ia) (Xreal a).
Hypothesis Hcontb : contains (I.convert ib) (Xreal b).
Hypothesis Hcontxa : contains iX (Xreal a).
Hypothesis Hcontxb : contains iX (Xreal b).

Definition taylor_integral :=
  TM.TMI.integralEnclosure prec X0 Mf ia ib.

(* now we take the intersection of a naive and intelligent way of computing the integral *)
Definition taylor_integral_naive_intersection :=
  let temp := I.mul prec (I.sub prec ib ia) (iF (I.join ia ib)) in
  if I.real temp then I.meet temp taylor_integral else temp.

Lemma taylor_integral_correct :
  contains
    (I.convert taylor_integral)
    (Xreal (RInt f a b)).
Proof.
rewrite /taylor_integral.
apply: (@TM.TMI.integralEnclosure_correct prec X0 X (fun x => Xreal (f x)) Mf (proj_val (I.F.convert (I.midpoint X)))) => //.
apply J.contains_midpoint.
now exists a.
Qed.

Lemma taylor_integral_naive_intersection_correct :
  contains
    (I.convert taylor_integral_naive_intersection)
    (Xreal (RInt f a b)).
Proof.
rewrite /taylor_integral_naive_intersection.
set tmp := I.mul prec (I.sub prec ib ia) (iF (I.join ia ib)).
generalize (I.real_correct tmp).
case I.real ; intros Hr.
2: now destruct (I.convert tmp).
apply I.meet_correct.
apply J.contains_RInt => //.
intros x Hx.
apply HiFIntExt.
assert (H := I.join_correct ia ib).
apply: contains_connected Hx.
apply H.
now apply Rmin_case ; [left|right].
apply H.
now apply Rmax_case ; [left|right].
exact: taylor_integral_correct.
Qed.

End DepthZeroPol.

End IntegralTaylor.
