Require Import Bool.
Require Import List.
Require Import Reals.
Require Import missing.
Require Import xreal.
Require Import xreal_derive.
Require Import definitions.
Require Import generic_proof.
Require Import interval.

Module IntervalAlgos (I : IntervalOps).

Definition bisect_1d_step fi l u output cont :=
  if I.subset (fi (I.bnd l u)) output then true
  else
    let m := I.midpoint (I.bnd l u) in
    match cont l m with
    | true => cont m u
    | false => false
    end.

Fixpoint bisect_1d fi l u output steps { struct steps } :=
  match steps with
  | O => false
  | S n =>
    bisect_1d_step fi l u output
      (fun l u => bisect_1d fi l u output n)
  end.

Theorem bisect_1d_correct :
  forall steps f fi inpl inpu output,
  I.extension f fi ->
  bisect_1d fi inpl inpu output steps = true ->
  forall x,
  contains (I.convert (I.bnd inpl inpu)) x -> contains (I.convert output) (f x).
intros.
generalize inpl inpu H0 x H1. clear inpl inpu H0 x H1.
induction steps.
intros.
discriminate H0.
intros inpl inpu.
simpl.
(*fold (I.bnd (I.Ibnd inpl inpu) x).*)
unfold bisect_1d_step.
case_eq (I.subset (fi (I.bnd inpl inpu)) output).
intros H0 _ x H1.
eapply subset_contains.
apply I.subset_correct with (1 := H0).
apply H.
exact H1.
intros _.
set (inpm := I.midpoint (I.bnd inpl inpu)).
case_eq (bisect_1d fi inpl inpm output steps).
intros H0 H1 x H2.
apply (bisect (fun x => contains (I.convert output) (f x))
              (I.convert_bound inpl) (I.convert_bound inpm) (I.convert_bound inpu)).
unfold domain.
rewrite <- I.bnd_correct.
apply IHsteps with (1 := H0).
unfold domain.
rewrite <- I.bnd_correct.
apply IHsteps with (1 := H1).
rewrite <- I.bnd_correct.
exact H2.
intros _ H0 x _.
discriminate H0.
Qed.

Definition lookup_1d_step fi l u output cont :=
  if I.subset (fi (I.bnd l u)) output then output
  else
    let m := I.midpoint (I.bnd l u) in
    let output := cont l m output in
    if I.lower_bounded output || I.upper_bounded output then cont m u output
    else cont m u output.

Fixpoint lookup_1d_main fi l u output steps { struct steps } :=
  match steps with
  | O => I.join (fi (I.bnd l u)) output
  | S n =>
    lookup_1d_step fi l u output
      (fun l u output => lookup_1d_main fi l u output n)
  end.

Definition lookup_1d fi l u extend steps :=
  let m := iter_nat steps _ (fun u => I.midpoint (I.bnd l u)) u in
  let output := extend (fi (I.bnd l m)) in
  if I.lower_bounded output || I.upper_bounded output then
    lookup_1d_main fi l u output steps
  else output.

Definition diff_refining_points prec xi di yi yi' ym yl yu :=
  match I.sign_large yi' with
  | Xund =>
    if I.bounded yi' then
      I.meet yi (I.add prec ym (I.mul prec di yi'))
    else yi
  | Xeq => ym
  | Xlt =>
    I.meet
     (if I.lower_bounded xi then I.lower_extent yl
      else I.whole)
     (if I.upper_bounded xi then I.upper_extent yu
      else I.whole)
  | Xgt =>
    I.meet
     (if I.lower_bounded xi then I.upper_extent yl
      else I.whole)
     (if I.upper_bounded xi then I.lower_extent yu
      else I.whole)
  end.

Definition diff_refining prec xi yi yi' fi :=
  match I.sign_large yi' with
  | Xund =>
    if I.bounded yi' then
      let m := I.midpoint xi in
      let mi := I.bnd m m in
      I.meet yi
       (I.add prec (fi mi) (I.mul prec (I.sub prec xi mi) yi'))
    else yi
  | Xeq =>
    let m := I.midpoint xi in fi (I.bnd m m)
  | Xlt =>
    I.meet
     (if I.lower_bounded xi then
        let l := I.lower xi in
        I.lower_extent (fi (I.bnd l l))
      else I.whole)
     (if I.upper_bounded xi then
        let u := I.upper xi in
        I.upper_extent (fi (I.bnd u u))
      else I.whole)
  | Xgt =>
    I.meet
     (if I.lower_bounded xi then
        let l := I.lower xi in
        I.upper_extent (fi (I.bnd l l))
      else I.whole)
     (if I.upper_bounded xi then
      let u := I.upper xi in
        I.lower_extent (fi (I.bnd u u))
      else I.whole)
  end.

Lemma diff_refining_aux_0 :
  forall f f' xi yi',
  Xderive f f' ->
  I.sign_large yi' <> Xund ->
 (forall x, contains xi x -> contains (I.convert yi') (f' x)) ->
  forall x, contains xi x ->
  x = Xreal (proj_val x) /\
  forall v,
  f x = Xreal (proj_fun v f (proj_val x)) /\
  f' x = Xreal (proj_fun v f' (proj_val x)).
intros f f' xi yi' Hd Hs Hy' x Hx.
case_eq (f' x).
(* assuming f'(x) is NaN ... *)
intros Hnf'.
generalize (Hy' _ Hx).
rewrite Hnf'.
intros Hny'.
apply False_ind.
generalize (I.sign_large_correct yi').
destruct (I.sign_large yi') ; intros H.
generalize (H _ Hny').
discriminate.
destruct (H _ Hny') as (H0, _).
discriminate H0.
destruct (H _ Hny') as (H0, _).
discriminate H0.
now elim Hs.
(* ... leads to a contradiction, so f'(x) is real ... *)
intros ry' Hrf'.
generalize (Hd x).
destruct x as [|x].
rewrite Hrf'.
now intro H.
(* ... so x is real too *)
rewrite Hrf'.
unfold Xderive_pt.
case_eq (f (Xreal x)).
now intros _ H.
intros ry Hrf _.
refl_exists.
unfold proj_fun, proj_val.
now rewrite Hrf.
unfold proj_fun, proj_val.
now rewrite Hrf'.
Qed.

Lemma diff_refining_aux_1 :
  forall prec f f' xi yi' m mi ymi,
  Xderive f f' ->
  contains (I.convert mi) (Xreal m) ->
  contains (I.convert xi) (Xreal m) ->
  contains (I.convert ymi) (f (Xreal m)) ->
 (forall x, contains (I.convert xi) x -> contains (I.convert yi') (f' x)) ->
  forall x, contains (I.convert xi) x ->
  contains (I.convert (I.add prec ymi (I.mul prec (I.sub prec xi mi) yi'))) (f x).
intros prec f f' xi yi' m mi ymi Hd Hxm Hm Hym Hy' x Hx.
case_eq (I.convert yi').
(* - yi' is NaI *)
intro Hyn'.
assert (contains (I.convert (I.add prec ymi (I.mul prec (I.sub prec xi mi) yi'))) Xnan).
replace Xnan with (Xadd (f (Xreal m)) Xnan).
change Xnan with (Xmul (Xsub (Xreal m) (Xreal m)) Xnan).
apply I.add_correct.
exact Hym.
apply I.mul_correct.
now apply I.sub_correct.
rewrite Hyn'.
exact I.
exact (Xadd_comm _ _).
generalize H.
now induction (I.convert (I.add prec ymi (I.mul prec (I.sub prec xi mi) yi'))).
(* - yi' is real ... *)
intros yl' yu' Hyi'.
destruct x as [|x].
case_eq (I.convert xi).
intros Hxi.
generalize (Hy' _ Hx).
rewrite Hyi'.
generalize (Hd Xnan).
unfold Xderive_pt.
case (f' Xnan).
intros _ H.
elim H.
intros _ H _.
elim H.
intros xl xu Hxi.
rewrite Hxi in Hx.
elim Hx.
(* ... so x is real ... *)
set (Pxi := fun x => contains (I.convert xi) (Xreal x)).
assert (H': forall c, Pxi c -> f' (Xreal c) <> Xnan).
intros c Hc H.
generalize (Hy' (Xreal c) Hc).
rewrite H, Hyi'.
intro H0.
elim H0.
(* ... and we can apply the MVT *)
destruct (Xderive_MVT _ _ Hd Pxi (contains_connected _) H' _ Hm _ Hx) as (c, (Hc1, Hc2)).
rewrite Hc2.
apply I.add_correct.
exact Hym.
rewrite Xmul_comm.
apply I.mul_correct.
now apply I.sub_correct.
apply Hy'.
exact Hc1.
Qed.

Lemma diff_refining_aux_2 :
  forall f f' xi m ymi,
  Xderive f f' ->
  contains xi (Xreal m) ->
  contains ymi (f (Xreal m)) ->
 (forall x, contains xi x -> contains (Ibnd (Xreal 0) (Xreal 0)) (f' x)) ->
  forall x, contains xi x ->
  contains ymi (f x).
intros f f' xi m ymi Hd Hm Hym Hy'.
(* the derivative is zero ... *)
destruct xi as [|xl xu].
apply False_ind.
generalize (Hy' Xnan I) (Hd Xnan).
now case (f' (Xnan)).
intros [|x] Hx.
elim Hx.
(* ... so x is real ... *)
set (Pxi := fun x => contains (Ibnd xl xu) (Xreal x)).
assert (H': forall c, Pxi c -> f' (Xreal c) <> Xnan).
intros c Hc H.
generalize (Hy' (Xreal c) Hc).
now rewrite H.
(* ... and we can apply the MVT *)
destruct (Xderive_MVT _ _ Hd Pxi (contains_connected _) H' _ Hm _ Hx) as (c, (Hc1, Hc2)).
rewrite Hc2.
replace (f' (Xreal c)) with (Xreal 0).
simpl.
rewrite Rmult_0_l.
rewrite Xadd_0_r.
exact Hym.
generalize (Hy' (Xreal c) Hc1).
destruct (f' (Xreal c)) as [|y].
intro H.
elim H.
intros (H3,H4).
apply f_equal.
now apply Rle_antisym.
Qed.

(*
Lemma diff_refining_correct_aux_5 :
  forall f f' fi',
  I.extension f' fi' ->
  Xderive f f' ->
  forall xi,
  I.convert (fi' xi) <> Inan ->
 (exists x, contains (I.convert xi) x) ->
  exists m, I.convert_bound (I.midpoint xi) = Xreal m.
intros f f' fi' Hf' Hd xi Hyi'.
case_eq (I.convert xi).
(* - xi = NaI *)
intros Hxi _.
elim Hyi'.
generalize (Hf' xi Xnan).
rewrite Hxi.
generalize (Hd Xnan).
case (f' Xnan).
destruct (I.convert (fi' xi)) as [|l u].
now intros _ _.
simpl.
intros _ H0.
simpl in H0.
elim (H0 I).
intros _ H0 _.
elim H0.
(* - xi = [l,u] *)
intros xl xu Hxi Hx.
rewrite <- Hxi in Hx.
generalize (I.midpoint_correct _ Hx).
rewrite Hxi.
destruct (I.convert_bound (I.midpoint xi)) as [|m].
intro H.
elim H.
intros _.
exists m.
apply refl_equal.
Qed.
*)

Theorem diff_refining_points_correct :
  forall prec f f' xi yi yi' ym yl yu,
  Xderive f f' ->
 (forall x, contains (I.convert xi) x -> contains (I.convert yi) (f x)) ->
 (forall x, contains (I.convert xi) x -> contains (I.convert yi') (f' x)) ->
  contains (I.convert ym) (f (I.convert_bound (I.midpoint xi))) ->
 (if I.lower_bounded xi then
    contains (I.convert yl) (f (I.convert_bound (I.lower xi)))
  else True) ->
 (if I.upper_bounded xi then
    contains (I.convert yu) (f (I.convert_bound (I.upper xi)))
  else True) ->
  let m := I.midpoint xi in
  forall x, contains (I.convert xi) x ->
  contains (I.convert (diff_refining_points prec xi (I.sub prec xi (I.bnd m m)) yi yi' ym yl yu)) (f x).
intros prec f f' xi yi yi' ym yl yu Hd Hyi Hyi' Hym Hyl Hyu m x Hx.
unfold m. clear m.
unfold diff_refining_points.
generalize (I.sign_large_correct yi').
case_eq (I.sign_large yi') ; intros Hs1 Hs2.
(* - sign is Xeq *)
destruct (I.midpoint_correct xi (ex_intro _ _ Hx)) as (H1, H2).
eapply diff_refining_aux_2 with (1 := Hd) (5 := Hx).
instantiate (1 := proj_val (I.convert_bound (I.midpoint xi))).
now rewrite <- H1.
now rewrite <- H1.
intros.
rewrite (Hs2 (f' x0)).
split ; apply Rle_refl.
now apply Hyi'.
(* - sign is Xlt *)
assert (I.sign_large yi' <> Xund).
now rewrite Hs1.
clear Hs1. rename H into Hs1.
assert (forall x, contains (I.convert xi) x -> forall v,
  f x = Xreal (proj_fun v f (proj_val x)) /\
  f' x = Xreal (proj_fun v f' (proj_val x)) /\
  (proj_fun v f' (proj_val x) <= 0)%R).
intros a Ha v.
destruct (Hs2 _ (Hyi' _ Ha)) as (Ha1, Ha2).
destruct (diff_refining_aux_0 _ _ _ _ Hd Hs1 Hyi' _ Ha) as (Ha3, Ha4).
destruct (Ha4 v) as (Ha5, Ha6).
split.
exact Ha5.
split.
exact Ha6.
rewrite Ha1 in Ha6.
inversion Ha6.
exact Ha2.
clear Hs2. rename H into Hs2.
apply I.meet_correct.
(*   lower part *)
case_eq (I.lower_bounded xi).
intros H.
destruct (I.lower_bounded_correct xi H) as (Hxl, Hxi).
rewrite H in Hyl.
clear Hym Hyu H.
assert (Hl: contains (I.convert xi) (I.convert_bound (I.lower xi))).
rewrite Hxi, Hxl.
apply contains_lower with x.
now rewrite <- Hxl, <- Hxi.
rewrite (proj1 (Hs2 _ Hx R0)).
apply I.lower_extent_correct with (proj_fun 0 f (proj_val (I.convert_bound (I.lower xi)))).
now rewrite <- (proj1 (Hs2 _ Hl R0)).
destruct (diff_refining_aux_0 _ _ _ _ Hd Hs1 Hyi' _ Hx) as (Hx1, _).
eapply (derivable_neg_imp_decreasing (proj_fun R0 f) (proj_fun R0 f')).
apply (contains_connected (I.convert xi)).
intros a Ha.
simpl in Ha.
destruct (Hs2 _ Ha R0) as (Ha1, (Ha2, Ha3)).
split.
generalize (Hd (Xreal a)).
unfold Xderive_pt.
rewrite Ha2, Ha1.
intro H.
exact (H R0).
exact Ha3.
simpl.
now rewrite <- Hxl.
simpl.
now rewrite <- Hx1.
rewrite Hxi, Hx1, Hxl in Hx.
exact (proj1 Hx).
intros _.
rewrite (proj1 (Hs2 x Hx R0)).
apply I.whole_correct.
(*   upper part *)
case_eq (I.upper_bounded xi).
intros H.
destruct (I.upper_bounded_correct xi H) as (Hxu, Hxi).
rewrite H in Hyu.
clear H.
assert (Hu: contains (I.convert xi) (I.convert_bound (I.upper xi))).
rewrite Hxi, Hxu.
apply contains_upper with x.
now rewrite <- Hxu, <- Hxi.
rewrite (proj1 (Hs2 _ Hx R0)).
apply I.upper_extent_correct with (proj_fun 0 f (proj_val (I.convert_bound (I.upper xi)))).
now rewrite <- (proj1 (Hs2 _ Hu R0)).
destruct (diff_refining_aux_0 _ _ _ _ Hd Hs1 Hyi' _ Hx) as (Hx1, _).
eapply (derivable_neg_imp_decreasing (proj_fun R0 f) (proj_fun R0 f')).
apply (contains_connected (I.convert xi)).
intros a Ha.
simpl in Ha.
destruct (Hs2 _ Ha R0) as (Ha1, (Ha2, Ha3)).
split.
generalize (Hd (Xreal a)).
unfold Xderive_pt.
rewrite Ha2, Ha1.
intro H.
exact (H R0).
exact Ha3.
simpl.
now rewrite <- Hx1.
simpl.
now rewrite <- Hxu.
rewrite Hxi, Hx1, Hxu in Hx.
exact (proj2 Hx).
intros _.
rewrite (proj1 (Hs2 x Hx R0)).
apply I.whole_correct.
(* - sign is Xgt *)
assert (I.sign_large yi' <> Xund).
now rewrite Hs1.
clear Hs1. rename H into Hs1.
assert (forall x, contains (I.convert xi) x -> forall v,
  f x = Xreal (proj_fun v f (proj_val x)) /\
  f' x = Xreal (proj_fun v f' (proj_val x)) /\
  (0 <= proj_fun v f' (proj_val x))%R).
intros a Ha v.
destruct (Hs2 _ (Hyi' _ Ha)) as (Ha1, Ha2).
destruct (diff_refining_aux_0 _ _ _ _ Hd Hs1 Hyi' _ Ha) as (Ha3, Ha4).
destruct (Ha4 v) as (Ha5, Ha6).
split.
exact Ha5.
split.
exact Ha6.
rewrite Ha1 in Ha6.
inversion Ha6.
exact Ha2.
clear Hs2. rename H into Hs2.
apply I.meet_correct.
(*   lower part *)
case_eq (I.lower_bounded xi).
intros H.
destruct (I.lower_bounded_correct xi H) as (Hxl, Hxi).
rewrite H in Hyl.
clear H.
assert (Hl: contains (I.convert xi) (I.convert_bound (I.lower xi))).
rewrite Hxi, Hxl.
apply contains_lower with x.
now rewrite <- Hxl, <- Hxi.
rewrite (proj1 (Hs2 _ Hx R0)).
apply I.upper_extent_correct with (proj_fun 0 f (proj_val (I.convert_bound (I.lower xi)))).
now rewrite <- (proj1 (Hs2 _ Hl R0)).
destruct (diff_refining_aux_0 _ _ _ _ Hd Hs1 Hyi' _ Hx) as (Hx1, _).
eapply (derivable_pos_imp_increasing (proj_fun R0 f) (proj_fun R0 f')).
apply (contains_connected (I.convert xi)).
intros a Ha.
simpl in Ha.
destruct (Hs2 _ Ha R0) as (Ha1, (Ha2, Ha3)).
split.
generalize (Hd (Xreal a)).
unfold Xderive_pt.
rewrite Ha2, Ha1.
intro H.
exact (H R0).
exact Ha3.
simpl.
now rewrite <- Hxl.
simpl.
now rewrite <- Hx1.
rewrite Hxi, Hx1, Hxl in Hx.
exact (proj1 Hx).
intros _.
rewrite (proj1 (Hs2 x Hx R0)).
apply I.whole_correct.
(*   upper part *)
case_eq (I.upper_bounded xi).
intros H.
destruct (I.upper_bounded_correct xi H) as (Hxu, Hxi).
rewrite H in Hyu.
clear H.
assert (Hu: contains (I.convert xi) (I.convert_bound (I.upper xi))).
rewrite Hxi, Hxu.
apply contains_upper with x.
now rewrite <- Hxu, <- Hxi.
rewrite (proj1 (Hs2 _ Hx R0)).
apply I.lower_extent_correct with (proj_fun 0 f (proj_val (I.convert_bound (I.upper xi)))).
now rewrite <- (proj1 (Hs2 _ Hu R0)).
destruct (diff_refining_aux_0 _ _ _ _ Hd Hs1 Hyi' _ Hx) as (Hx1, _).
eapply (derivable_pos_imp_increasing (proj_fun R0 f) (proj_fun R0 f')).
apply (contains_connected (I.convert xi)).
intros a Ha.
simpl in Ha.
destruct (Hs2 _ Ha R0) as (Ha1, (Ha2, Ha3)).
split.
generalize (Hd (Xreal a)).
unfold Xderive_pt.
rewrite Ha2, Ha1.
intro H.
exact (H R0).
exact Ha3.
simpl.
now rewrite <- Hx1.
simpl.
now rewrite <- Hxu.
rewrite Hxi, Hx1, Hxu in Hx.
exact (proj2 Hx).
intros _.
rewrite (proj1 (Hs2 x Hx R0)).
apply I.whole_correct.
(* - sign is Xund *)
clear Hs1 Hs2.
case_eq (I.bounded yi') ; intro Hb.
apply I.meet_correct.
now apply Hyi.
destruct (I.midpoint_correct xi (ex_intro _ _ Hx)) as (Hm1, Hm2).
eapply diff_refining_aux_1 with (1 := Hd).
rewrite I.bnd_correct.
rewrite Hm1.
split ; apply Rle_refl.
now rewrite <- Hm1.
now rewrite <- Hm1.
exact Hyi'.
exact Hx.
now apply Hyi.
Qed.

Lemma convert_bnd :
  forall l u v, contains (Ibnd l u) (I.convert_bound v) ->
  contains (I.convert (I.bnd v v)) (I.convert_bound v).
intros l u v H.
rewrite I.bnd_correct.
destruct (I.convert_bound v).
elim H.
split ; apply Rle_refl.
Qed.

Theorem diff_refining_correct :
  forall prec f f' fi fi',
  I.extension f fi ->
  I.extension f' fi' ->
  Xderive f f' ->
  I.extension f (fun b => diff_refining prec b (fi b) (fi' b) fi).
intros prec f f' fi fi' Hf Hf' Hd xi x Hx.
unfold diff_refining.
case_eq (I.convert xi) ; intros.
(* - xi is Inan *)
assert (contains (I.convert (fi' xi)) Xnan).
replace Xnan with (f' Xnan).
apply Hf'.
now rewrite H.
generalize (Hd Xnan).
now case (f' Xnan) ; intros.
generalize (I.sign_large_correct (fi' xi)).
case (I.sign_large (fi' xi)) ; intro.
now assert (H2 := H1 _ H0).
now assert (H2 := proj1 (H1 _ H0)).
now assert (H2 := proj1 (H1 _ H0)).
clear H1.
generalize (I.bounded_correct (fi' xi)).
case (I.bounded (fi' xi)).
intro H1.
generalize (I.lower_bounded_correct _ (proj1 (H1 (refl_equal _)))).
clear H1. intros (_, H1).
unfold I.bounded_prop in H1.
now destruct (I.convert (fi' xi)).
intros _.
now apply Hf.
(* - xi is Ibnd *)
apply diff_refining_points_correct with (1 := Hd) (7 := Hx).
apply Hf.
apply Hf'.
apply Hf.
apply (convert_bnd l u).
rewrite <- H.
exact (proj2 (I.midpoint_correct _ (ex_intro _ _ Hx))).
(*   lower bound *)
generalize (I.lower_bounded_correct xi).
case (I.lower_bounded xi).
refine (fun H0 => _ (H0 (refl_equal true))).
clear H0.
intros (H0, H1).
apply Hf.
apply (convert_bnd l l).
rewrite H1, H0 in H.
rewrite H0.
inversion H.
split ; apply Rle_refl.
now intros _.
(*   upper bound *)
generalize (I.upper_bounded_correct xi).
case (I.upper_bounded xi).
refine (fun H0 => _ (H0 (refl_equal true))).
clear H0.
intros (H0, H1).
apply Hf.
apply (convert_bnd u u).
rewrite H1, H0 in H.
rewrite H0.
inversion H.
split ; apply Rle_refl.
now intros _.
Qed.

(*
generalize (I.sign_large_correct (fi' xi)).
case_eq (I.sign_large (fi' xi)) ; intros Hs1 Hs2.
(* - sign is Xeq *)
refine ((fun Hm => _) (diff_refining_correct_aux_5 _ _ _ Hf' Hd xi _ (ex_intro _ _ Hx))).
destruct Hm as (m, Hm).
eapply diff_refining_aux_2 with (1 := Hd).
instantiate (1 := m).
rewrite <- Hm.
apply I.midpoint_correct.
exists x.
exact Hx.
apply Hf.
rewrite I.bnd_correct.
rewrite Hm.
split ; apply Rle_refl.
intros.
rewrite (Hs2 (f' x0)).
split ; apply Rle_refl.
apply Hf'.
exact H.
exact Hx.
intro H.
rewrite H in Hs2.
generalize (Hs2 Xnan I).
discriminate.
(* - sign is Xlt *)
assert (I.sign_large (fi' xi) <> Xund).
now rewrite Hs1.
clear Hs1. rename H into Hs1.
assert (forall x, contains (I.convert xi) x -> forall v,
  f x = Xreal (proj_fun v f (proj_val x)) /\
  f' x = Xreal (proj_fun v f' (proj_val x)) /\
  (proj_fun v f' (proj_val x) <= 0)%R).
intros a Ha v.
destruct (Hs2 _ (Hf' _ _ Ha)) as (Ha1, Ha2).
destruct (diff_refining_aux_0 _ _ _ _ Hd Hs1 (Hf' _) _ Ha) as (Ha3, Ha4).
destruct (Ha4 v) as (Ha5, Ha6).
split.
exact Ha5.
split.
exact Ha6.
rewrite Ha1 in Ha6.
inversion Ha6.
exact Ha2.
clear Hs2. rename H into Hs2.
apply I.meet_correct.
(*   lower part *)
case_eq (I.lower_bounded xi).
intros H.
destruct (I.lower_bounded_correct xi H) as (Hxl, Hxi).
clear H.
assert (Hl: contains (I.convert xi) (I.convert_bound (I.lower xi))).
rewrite Hxi, Hxl.
apply contains_lower with x.
now rewrite <- Hxl, <- Hxi.
rewrite (proj1 (Hs2 _ Hx R0)).
apply I.lower_extent_correct with (proj_fun 0 f (proj_val (I.convert_bound (I.lower xi)))).
rewrite <- (proj1 (Hs2 _ Hl R0)).
apply Hf.
rewrite I.bnd_correct.
rewrite Hxl.
split ; apply Rle_refl.
destruct (diff_refining_aux_0 _ _ _ _ Hd Hs1 (Hf' _) _ Hx) as (Hx1, _).
eapply (derivable_neg_imp_decreasing (proj_fun R0 f) (proj_fun R0 f')).
apply (contains_connected (I.convert xi)).
intros a Ha.
simpl in Ha.
destruct (Hs2 _ Ha R0) as (Ha1, (Ha2, Ha3)).
split.
generalize (Hd (Xreal a)).
rewrite Ha2, Ha1.
intro H.
exact (H R0).
exact Ha3.
simpl.
now rewrite <- Hxl.
simpl.
now rewrite <- Hx1.
rewrite Hxi, Hx1, Hxl in Hx.
exact (proj1 Hx).
intros _.
rewrite (proj1 (Hs2 x Hx R0)).
apply I.whole_correct.
(*   upper part *)
case_eq (I.upper_bounded xi).
intros H.
destruct (I.upper_bounded_correct xi H) as (Hxu, Hxi).
clear H.
assert (Hu: contains (I.convert xi) (I.convert_bound (I.upper xi))).
rewrite Hxi, Hxu.
apply contains_upper with x.
now rewrite <- Hxu, <- Hxi.
rewrite (proj1 (Hs2 _ Hx R0)).
apply I.upper_extent_correct with (proj_fun 0 f (proj_val (I.convert_bound (I.upper xi)))).
rewrite <- (proj1 (Hs2 _ Hu R0)).
apply Hf.
rewrite I.bnd_correct.
rewrite Hxu.
split ; apply Rle_refl.
destruct (diff_refining_aux_0 _ _ _ _ Hd Hs1 (Hf' _) _ Hx) as (Hx1, _).
eapply (derivable_neg_imp_decreasing (proj_fun R0 f) (proj_fun R0 f')).
apply (contains_connected (I.convert xi)).
intros a Ha.
simpl in Ha.
destruct (Hs2 _ Ha R0) as (Ha1, (Ha2, Ha3)).
split.
generalize (Hd (Xreal a)).
rewrite Ha2, Ha1.
intro H.
exact (H R0).
exact Ha3.
simpl.
now rewrite <- Hx1.
simpl.
now rewrite <- Hxu.
rewrite Hxi, Hx1, Hxu in Hx.
exact (proj2 Hx).
intros _.
rewrite (proj1 (Hs2 x Hx R0)).
apply I.whole_correct.
(* - sign is Xgt *)
assert (I.sign_large (fi' xi) <> Xund).
now rewrite Hs1.
clear Hs1. rename H into Hs1.
assert (forall x, contains (I.convert xi) x -> forall v,
  f x = Xreal (proj_fun v f (proj_val x)) /\
  f' x = Xreal (proj_fun v f' (proj_val x)) /\
  (0 <= proj_fun v f' (proj_val x))%R).
intros a Ha v.
destruct (Hs2 _ (Hf' _ _ Ha)) as (Ha1, Ha2).
destruct (diff_refining_aux_0 _ _ _ _ Hd Hs1 (Hf' _) _ Ha) as (Ha3, Ha4).
destruct (Ha4 v) as (Ha5, Ha6).
split.
exact Ha5.
split.
exact Ha6.
rewrite Ha1 in Ha6.
inversion Ha6.
exact Ha2.
clear Hs2. rename H into Hs2.
apply I.meet_correct.
(*   lower part *)
case_eq (I.lower_bounded xi).
intros H.
destruct (I.lower_bounded_correct xi H) as (Hxl, Hxi).
clear H.
assert (Hl: contains (I.convert xi) (I.convert_bound (I.lower xi))).
rewrite Hxi, Hxl.
apply contains_lower with x.
now rewrite <- Hxl, <- Hxi.
rewrite (proj1 (Hs2 _ Hx R0)).
apply I.upper_extent_correct with (proj_fun 0 f (proj_val (I.convert_bound (I.lower xi)))).
rewrite <- (proj1 (Hs2 _ Hl R0)).
apply Hf.
rewrite I.bnd_correct.
rewrite Hxl.
split ; apply Rle_refl.
destruct (diff_refining_aux_0 _ _ _ _ Hd Hs1 (Hf' _) _ Hx) as (Hx1, _).
eapply (derivable_pos_imp_increasing (proj_fun R0 f) (proj_fun R0 f')).
apply (contains_connected (I.convert xi)).
intros a Ha.
simpl in Ha.
destruct (Hs2 _ Ha R0) as (Ha1, (Ha2, Ha3)).
split.
generalize (Hd (Xreal a)).
rewrite Ha2, Ha1.
intro H.
exact (H R0).
exact Ha3.
simpl.
now rewrite <- Hxl.
simpl.
now rewrite <- Hx1.
rewrite Hxi, Hx1, Hxl in Hx.
exact (proj1 Hx).
intros _.
rewrite (proj1 (Hs2 x Hx R0)).
apply I.whole_correct.
(*   upper part *)
case_eq (I.upper_bounded xi).
intros H.
destruct (I.upper_bounded_correct xi H) as (Hxu, Hxi).
clear H.
assert (Hu: contains (I.convert xi) (I.convert_bound (I.upper xi))).
rewrite Hxi, Hxu.
apply contains_upper with x.
now rewrite <- Hxu, <- Hxi.
rewrite (proj1 (Hs2 _ Hx R0)).
apply I.lower_extent_correct with (proj_fun 0 f (proj_val (I.convert_bound (I.upper xi)))).
rewrite <- (proj1 (Hs2 _ Hu R0)).
apply Hf.
rewrite I.bnd_correct.
rewrite Hxu.
split ; apply Rle_refl.
destruct (diff_refining_aux_0 _ _ _ _ Hd Hs1 (Hf' _) _ Hx) as (Hx1, _).
eapply (derivable_pos_imp_increasing (proj_fun R0 f) (proj_fun R0 f')).
apply (contains_connected (I.convert xi)).
intros a Ha.
simpl in Ha.
destruct (Hs2 _ Ha R0) as (Ha1, (Ha2, Ha3)).
split.
generalize (Hd (Xreal a)).
rewrite Ha2, Ha1.
intro H.
exact (H R0).
exact Ha3.
simpl.
now rewrite <- Hx1.
simpl.
now rewrite <- Hxu.
rewrite Hxi, Hx1, Hxu in Hx.
exact (proj2 Hx).
intros _.
rewrite (proj1 (Hs2 x Hx R0)).
apply I.whole_correct.
(* - sign is Xund *)
clear Hs1 Hs2.
case_eq (I.bounded (fi' xi)) ; intro Hb.
apply I.meet_correct.
now apply Hf.
refine ((fun Hm => _) (diff_refining_correct_aux_5 _ _ _ Hf' Hd xi _ (ex_intro _ _ Hx))).
destruct Hm as (m, Hm).
eapply diff_refining_aux_1 with (1 := Hd).
instantiate (1 := m).
rewrite I.bnd_correct.
rewrite Hm.
split ; apply Rle_refl.
rewrite <- Hm.
apply I.midpoint_correct.
exists x.
exact Hx.
apply Hf.
rewrite I.bnd_correct.
rewrite Hm.
split ; apply Rle_refl.
apply Hf'.
exact Hx.
destruct (I.bounded_correct _ Hb) as (Hbl, _).
destruct (I.lower_bounded_correct _ Hbl) as (_, Hl).
rewrite Hl.
discriminate.
now apply Hf.
Qed.
*)

End IntervalAlgos.

Module Valuator (I : IntervalOps).

Inductive unary_op : Set :=
  | Neg | Abs | Inv | Sqr | Sqrt | Cos | Sin | Tan | Atan.

Inductive binary_op : Set :=
  | Add | Sub | Mul | Div.

Inductive term : Set :=
  | Unary : unary_op -> nat -> term
  | Binary : binary_op -> nat -> nat -> term.

Set Implicit Arguments.

Record operations (A : Type) : Type :=
  { constant : Z -> A
  ; unary : unary_op -> A -> A
  ; binary : binary_op -> A -> A -> A }.

Unset Implicit Arguments.

Definition eval_generic_body A def (ops : operations A) values op :=
  let nth n := nth n values def in
  match op with
  | Unary o u => unary ops o (nth u)
  | Binary o u v => binary ops o (nth u) (nth v)
  end :: values.

Implicit Arguments eval_generic_body.

Definition eval_generic A def (ops : operations A) :=
  fold_left (eval_generic_body def ops).

Implicit Arguments eval_generic.

Lemma rev_formula :
  forall A formula terms def (ops : operations A),
  eval_generic def ops formula terms =
  fold_right (fun y x => eval_generic_body def ops x y) terms (rev formula).
intros.
pattern formula at 1 ; rewrite <- rev_involutive.
unfold eval_generic, eval_generic_body.
rewrite <- fold_left_rev_right.
rewrite rev_involutive.
apply refl_equal.
Qed.

Theorem eval_inductive_prop :
  forall A B P defA defB (opsA : operations A) (opsB : operations B),
  P defA defB ->
 (forall o a b, P a b -> P (unary opsA o a) (unary opsB o b)) ->
 (forall o a1 a2 b1 b2, P a1 b1 -> P a2 b2 -> P (binary opsA o a1 a2) (binary opsB o b1 b2)) ->
  forall inpA inpB,
 (forall n, P (nth n inpA defA) (nth n inpB defB)) ->
  forall prog,
  forall n, P (nth n (eval_generic defA opsA prog inpA) defA) (nth n (eval_generic defB opsB prog inpB) defB).
intros A B P defA defB opsA opsB Hdef Hun Hbin inpA inpB Hinp prog.
do 2 rewrite rev_formula.
induction (rev prog).
exact Hinp.
intros [|n].
simpl.
case a.
intros o n.
apply Hun.
apply IHl.
intros o n1 n2.
apply Hbin.
apply IHl.
apply IHl.
simpl.
apply IHl.
Qed.

Definition bnd_operations prec :=
  Build_operations I.fromZ
    (fun o => match o with Neg => I.neg | Abs => I.abs | Inv => I.inv prec | Sqr => I.sqr prec | Sqrt => I.sqrt prec | Cos => I.cos prec | Sin => I.sin prec | Tan => I.tan prec | Atan => I.atan prec end)
    (fun o => match o with Add => I.add prec | Sub => I.sub prec | Mul => I.mul prec | Div => I.div prec end).

Definition eval_bnd prec :=
  eval_generic I.nai (bnd_operations prec).

Definition ext_operations :=
  Build_operations (fun x => Xreal (Z2R x))
    (fun o => match o with Neg => Xneg | Abs => Xabs | Inv => Xinv | Sqr => Xsqr | Sqrt => Xsqrt | Cos => Xcos | Sin => Xsin | Tan => Xtan | Atan => Xatan end)
    (fun o => match o with Add => Xadd | Sub => Xsub | Mul => Xmul | Div => Xdiv end).

Definition eval_ext :=
  eval_generic (Xreal 0) ext_operations.

Theorem eval_inductive_prop_fun :
  forall A B P defA defB (opsA : operations A) (opsB : operations B),
 (forall a1 a2, (forall x, a1 x = a2 x) -> forall b, P a1 b -> P a2 b) ->
  P (fun _ : ExtendedR => defA) defB ->
 (forall o a b, P a b -> P (fun x => unary opsA o (a x)) (unary opsB o b)) ->
 (forall o a1 a2 b1 b2, P a1 b1 -> P a2 b2 -> P (fun x => binary opsA o (a1 x) (a2 x)) (binary opsB o b1 b2)) ->
  forall inpA inpB,
 (forall n, P (fun x => nth n (inpA x) defA) (nth n inpB defB)) ->
  forall prog,
  forall n, P (fun x => nth n (eval_generic defA opsA prog (inpA x)) defA) (nth n (eval_generic defB opsB prog inpB) defB).
intros A B P defA defB opsA opsB HP Hdef Hun Hbin inpA inpB Hinp prog n.
apply HP with (fun x => nth n (fold_right (fun y x => eval_generic_body defA opsA x y) (inpA x) (rev prog)) defA).
intros x.
now rewrite rev_formula.
rewrite rev_formula.
generalize n. clear n.
induction (rev prog).
exact Hinp.
intros [|n].
simpl.
case a.
intros o n.
refine (Hun _ _ _ _).
apply IHl.
intros o n1 n2.
refine (Hbin _ _ _ _ _ _ _).
apply IHl.
apply IHl.
simpl.
apply IHl.
Qed.

Definition real_operations :=
  Build_operations Z2R
    (fun o => match o with Neg => Ropp | Abs => Rabs | Inv => Rinv | Sqr => Rsqr | Sqrt => R_sqrt.sqrt | Cos => cos | Sin => sin | Tan => tan | Atan => atan end)
    (fun o => match o with Add => Rplus | Sub => Rminus | Mul => Rmult | Div => Rdiv end).

Definition eval_real :=
  eval_generic R0 real_operations.

Definition diff_operations A (ops : @operations A) :=
  Build_operations
   (fun x => (constant ops x, constant ops 0))
   (fun o x =>
    match x with
    | (v, d) =>
      match o with
      | Neg => let f := unary ops Neg in (f v, f d)
      | Abs => let w := unary ops Abs v in (w,
        binary ops Mul d (binary ops Div v w))
      | Inv => let w := unary ops Inv v in (w,
        binary ops Mul d (unary ops Neg (unary ops Sqr w)))
      | Sqr => let w := binary ops Mul d v in (unary ops Sqr v, binary ops Add w w)
      | Sqrt => let w := unary ops Sqrt v in (w,
        binary ops Div d (binary ops Add w w))
      | Cos => (unary ops Cos v,
        binary ops Mul d (unary ops Neg (unary ops Sin v)))
      | Sin => (unary ops Sin v,
        binary ops Mul d (unary ops Cos v))
      | Tan => let w := unary ops Tan v in (w,
        binary ops Mul d (binary ops Add (constant ops 1) (unary ops Sqr w)))
      | Atan => (unary ops Atan v,
        binary ops Div d (binary ops Add (constant ops 1) (unary ops Sqr v)))
      end
    end)
   (fun o x y =>
    match x, y with
    | (vx, dx), (vy, dy) =>
      match o with
      | Add => let f := binary ops Add in (f vx vy, f dx dy)
      | Sub => let f := binary ops Sub in (f vx vy, f dx dy)
      | Mul => let f := binary ops Mul in (f vx vy,
        binary ops Add (f dx vy) (f dy vx))
      | Div => let f := binary ops Div in
        let w := f vx vy in
        (w, f (binary ops Sub dx (binary ops Mul dy w)) vy)
      end
    end).

(*
Lemma unary_ext_correct :
  forall o x y,
  unary ext_operations o x = Xreal y ->
  exists u, x = Xreal u /\ unary real_operations o u = y.
intros o x y.
case o ; simpl ;
  [ unfold Xneg
  | unfold Xabs
  | unfold Xinv
  | unfold Xsqr, Xmul
  | unfold Xsqrt
  | unfold Xcos
  | unfold Xsin
  | unfold Xtan
  | unfold Xatan ] ;
  intros ; xtotal ; refl_exists ; assumption.
Qed.

Lemma binary_ext_correct :
  forall o x y z,
  binary ext_operations o x y = Xreal z ->
  exists u, x = Xreal u /\
  exists v, y = Xreal v /\ binary real_operations o u v = z.
intros o x y z.
case o ; simpl ; [ unfold Xadd | unfold Xsub | unfold Xmul | unfold Xdiv ] ;
  intros ; xtotal ; refl_exists ; refl_exists ; assumption.
Qed.
*)

Lemma rewrite_inv_diff :
  forall u u',
  Xmul u' (Xneg (Xsqr (Xinv u))) = Xneg (Xdiv u' (Xsqr u)).
intros.
rewrite Xmul_Xneg_distr_r.
apply f_equal.
rewrite Xdiv_split.
apply f_equal.
unfold Xsqr.
apply sym_eq.
apply Xinv_Xmul_distr.
Qed.

(*
Lemma unary_diff_correct :
  forall o f f',
  Xderive f f' ->
  let g := fun x => unary (diff_operations _ ext_operations) o (f x, f' x) in
  Xderive (fun x => fst (g x)) (fun x => snd (g x)).
intros o f f' Hf g.
unfold g. clear g.
case o ; simpl.
apply Xderive_neg with (1 := Hf).
admit.
(* Xinv *)
apply Xderive_eq_diff with (fun x => Xneg (Xdiv (f' x) (Xsqr (f x)))).
intros.
apply rewrite_inv_diff.
apply Xderive_inv with (1 := Hf).
(* Xsqr *)
change (fun x => Xsqr (f x)) with (fun x => Xmul (f x) (f x)).
apply Xderive_mul ; exact Hf.
(* *)
apply Xderive_sqrt with (1 := Hf).
apply Xderive_cos with (1 := Hf).
apply Xderive_sin with (1 := Hf).
apply Xderive_tan with (1 := Hf).
admit.
Qed.
*)

Lemma rewrite_div_diff :
  forall u v u' v',
  Xdiv (Xsub u' (Xmul v' (Xdiv u v))) v = Xdiv (Xsub (Xmul u' v) (Xmul v' u)) (Xmul v v).
intros.
repeat rewrite Xdiv_split.
rewrite Xinv_Xmul_distr.
repeat rewrite <- Xmul_assoc.
apply (f_equal (fun x => Xmul x (Xinv v))).
pattern u' at 1 ; rewrite <- Xmul_1_r.
pattern (Xmul (Xmul v' u) (Xinv v)) ; rewrite <- Xmask_Xfun_r with (1 := Xmul_propagate).
rewrite Xfun_Xmask_r with (1 := Xsub_propagate).
rewrite <- Xfun_Xmask_l with (1 := Xsub_propagate).
rewrite <- Xfun_Xmask_r with (1 := Xmul_propagate).
rewrite <- Xmul_Xinv.
repeat rewrite Xsub_split.
rewrite <- Xmul_assoc.
rewrite <- Xmul_Xneg_distr_l.
apply sym_eq.
apply Xmul_Xadd_distr_r.
Qed.

(*
Lemma binary_diff_correct :
  forall o f f' g g',
  Xderive f f' -> Xderive g g' ->
  let h := fun x => binary (diff_operations _ ext_operations) o (f x, f' x) (g x, g' x) in
  Xderive (fun x => fst (h x)) (fun x => snd (h x)).
intros o f f' g g' Hf Hg h.
unfold h. clear h.
case o ; simpl.
apply Xderive_add ; assumption.
apply Xderive_sub ; assumption.
apply Xderive_mul ; assumption.
(* Xdiv *)
apply Xderive_eq_diff with (fun x => Xdiv (Xsub (Xmul (f' x) (g x)) (Xmul (g' x) (f x))) (Xmul (g x) (g x))).
intros.
apply rewrite_div_diff.
apply Xderive_div ; assumption.
Qed.
*)

Lemma xreal_to_real :
  forall prog terms n xi,
  contains xi (nth n (eval_ext prog (map Xreal terms)) (Xreal 0)) ->
  contains xi (Xreal (nth n (eval_real prog terms) R0)).
assert (Heq : forall a b, (forall xi, contains xi (Xreal a) -> contains xi (Xreal b)) -> b = a).
intros.
assert (Hb := H (Ibnd (Xreal a) (Xreal a)) (conj (Rle_refl a) (Rle_refl a))).
apply Rle_antisym.
exact (proj2 Hb).
exact (proj1 Hb).
(* . *)
intros prog terms.
unfold eval_ext, eval_real.
apply (eval_inductive_prop _ _ (fun a b => forall xi, contains xi a -> contains xi (Xreal b))) ;
  simpl ; intros.
exact H.
(* unary *)
destruct xi.
exact I.
destruct a as [|a].
destruct o ; exact (False_ind _ H0).
rewrite (Heq _ _ H).
destruct o ; try exact H0.
unfold Xinv in H0.
now destruct (is_zero a).
unfold Xsqrt in H0.
now destruct (is_negative a).
unfold Xtan, Xdiv, Xsin, Xcos in H0.
now destruct (is_zero (cos a)).
(* binary *)
destruct xi.
exact I.
destruct a1 as [|a1].
destruct o ; exact (False_ind _ H1).
destruct a2 as [|a2].
destruct o ; exact (False_ind _ H1).
rewrite (Heq _ _ H).
rewrite (Heq _ _ H0).
destruct o ; try exact H1.
unfold Xdiv in H1.
now destruct (is_zero a2).
(* . *)
rewrite map_nth in H.
exact H.
Qed.

Inductive bound_proof :=
  | Bproof : forall x xi, contains (I.convert xi) (Xreal x) -> bound_proof.

Definition real_from_bp v := match v with Bproof x _ _ => x end.
Definition xreal_from_bp v := match v with Bproof x _ _ => Xreal x end.
Definition interval_from_bp v := match v with Bproof _ xi _ => xi end.

Lemma iterated_bnd_nth :
  forall bounds n,
  contains (I.convert (nth n (map interval_from_bp bounds) I.nai))
    (nth n (map xreal_from_bp bounds) (Xreal R0)).
intros.
assert (contains (I.convert I.nai) (Xreal 0)).
rewrite I.nai_correct. exact I.
pose (b := Bproof R0 I.nai H).
change (Xreal 0) with (xreal_from_bp b).
change I.nai with (interval_from_bp b).
do 2 rewrite map_nth.
now case (nth n bounds b).
Qed.

Lemma eval_bnd_correct_aux :
  forall prec prog terms bounds,
 (forall n, contains (I.convert (nth n bounds I.nai)) (nth n terms (Xreal 0))) ->
  forall n,
  contains (I.convert (nth n (eval_bnd prec prog bounds) I.nai))
   (nth n (eval_ext prog terms) (Xreal 0)).
intros prec prog terms bounds Hinp.
unfold eval_bnd, eval_ext.
apply (eval_inductive_prop _ _ (fun a b => contains (I.convert a) b)).
(* . *)
rewrite I.nai_correct.
exact I.
(* unary *)
destruct o ; simpl ;
  [ apply I.neg_correct
  | apply I.abs_correct
  | apply I.inv_correct
  | apply I.sqr_correct
  | apply I.sqrt_correct
  | apply I.cos_correct
  | apply I.sin_correct
  | apply I.tan_correct
  | apply I.atan_correct ].
(* binary *)
destruct o ; simpl ;
  [ apply I.add_correct
  | apply I.sub_correct
  | apply I.mul_correct
  | apply I.div_correct ].
(* . *)
exact Hinp.
Qed.

Theorem eval_bnd_correct :
  forall prec prog bounds n,
  contains
    (I.convert (nth n (eval_bnd prec prog (map interval_from_bp bounds)) I.nai))
    (nth n (eval_ext prog (map xreal_from_bp bounds)) (Xreal 0)).
intros prec prog bounds.
apply eval_bnd_correct_aux.
apply iterated_bnd_nth.
Qed.

Theorem eval_bnd_correct_ext :
  forall prec prog bounds n,
  I.extension
    (fun x => nth n (eval_ext prog (x :: map xreal_from_bp bounds)) (Xreal 0))
    (fun b => nth n (eval_bnd prec prog (b :: map interval_from_bp bounds)) I.nai).
intros prec prog bounds n xi x Hx.
generalize n. clear n.
apply eval_bnd_correct_aux.
intros [|n].
exact Hx.
apply iterated_bnd_nth.
Qed.

Lemma Xderive_eq :
  forall g g' f f',
 (forall x, f x = g x) ->
 (forall x, f' x = g' x) ->
  Xderive g g' ->
  Xderive f f'.
intros.
apply Xderive_eq_fun with (1 := H).
apply Xderive_eq_diff with (1 := H0).
exact H1.
Qed.

(*
Lemma eval_diff_1_correct :
  forall prog terms n x,
  nth n (eval_ext prog (x :: map Xreal terms)) (Xreal 0) =
  fst (nth n (eval_generic (Xreal 0, Xnan) (diff_operations _ ext_operations) prog ((x, Xmask (Xreal 1) x) :: map (fun v => (Xreal v, Xmask (Xreal 0) x)) terms)) (Xreal 0, Xnan)).
intros.
unfold eval_ext.
apply (eval_inductive_prop _ (ExtendedR * ExtendedR) (fun a b => a = fst b)) ; try split.
intros o a (bl,br) H.
rewrite H.
now case o.
intros o a1 a2 (bl1,br1) (bl2,br2) H1 H2.
rewrite H1, H2.
now case o.
clear n.
intros [|n].
apply refl_equal.
rewrite <- map_nth.
simpl.
rewrite map_map.
apply (f_equal (fun v => nth n v (Xreal 0))).
now apply map_ext.
Qed.
*)

Lemma unary_diff_correct :
  forall o f d x,
  Xderive_pt f x d ->
  let v := unary (diff_operations _ ext_operations) o (f x, d) in
  unary ext_operations o (f x) = fst v /\
  Xderive_pt (fun x0 => unary ext_operations o (f x0)) x (snd v).
intros o f d x Hd.
destruct o ; simpl ; repeat split.
now apply Xderive_pt_neg.
admit.
rewrite rewrite_inv_diff.
now apply Xderive_pt_inv.
unfold Xsqr.
now apply Xderive_pt_mul.
now apply Xderive_pt_sqrt.
now apply Xderive_pt_cos.
now apply Xderive_pt_sin.
now apply Xderive_pt_tan.
admit.
Qed.

Lemma binary_diff_correct :
  forall o f1 f2 d1 d2 x,
  Xderive_pt f1 x d1 ->
  Xderive_pt f2 x d2 ->
  let v := binary (diff_operations _ ext_operations) o (f1 x, d1) (f2 x, d2) in
  binary ext_operations o (f1 x) (f2 x) = fst v /\
  Xderive_pt (fun x0 => binary ext_operations o (f1 x0) (f2 x0)) x (snd v).
intros o f1 f2 d1 d2 x Hd1 Hd2.
destruct o ; simpl ; repeat split.
now apply Xderive_pt_add.
now apply Xderive_pt_sub.
now apply Xderive_pt_mul.
rewrite rewrite_div_diff.
now apply Xderive_pt_div.
Qed.

Lemma eval_diff_correct :
  forall prog terms n x,
  let v := nth n (eval_generic (Xreal 0, Xnan) (diff_operations _ ext_operations) prog ((x, Xmask (Xreal 1) x) :: map (fun v => (Xreal v, Xmask (Xreal 0) x)) terms)) (Xreal 0, Xnan) in
  nth n (eval_ext prog (x :: map Xreal terms)) (Xreal 0) = fst v /\
  Xderive_pt (fun x => nth n (eval_ext prog (x :: map Xreal terms)) (Xreal 0)) x (snd v).
intros prog terms n x.
(*set (inpA x := x :: map Xreal terms).
set (inpB := (x, Xmask (Xreal 1) x) :: map (fun v : R => (Xreal v, Xmask (Xreal 0) x)) terms).*)
refine (eval_inductive_prop_fun _ _ (fun a b => a x = fst b /\ Xderive_pt a x (snd b)) _ _ _ _ _ _ _ _ _ _ _ _ _).
(* extensionality *)
intros a1 a2 Heq (bl, br).
simpl.
intros (Hl, Hr).
split.
now rewrite <- Heq.
apply Xderive_pt_eq_fun with (2 := Hr).
intros.
now apply sym_eq.
(* default *)
destruct x ; repeat split.
(* unary *)
intros o a (bl, br) (Hl, Hr).
simpl in Hl.
rewrite <- Hl.
now apply unary_diff_correct.
(* binary *)
intros o a1 a2 (bl1, br1) (bl2, br2) (Hl1, Hr1) (Hl2, Hr2).
simpl in Hl1, Hl2.
rewrite <- Hl1, <- Hl2.
now apply binary_diff_correct.
(* inputs *)
clear n.
intros [|n].
simpl.
repeat split.
apply Xderive_pt_identity.
simpl.
split.
rewrite <- map_nth.
rewrite map_map.
apply (f_equal (fun v => nth n v (Xreal 0))).
now apply map_ext.
rewrite <- map_nth.
rewrite map_map.
simpl.
destruct (le_or_lt (length (map (fun _ : R => Xmask (Xreal 0) x) terms)) n).
rewrite nth_overflow with (1 := H).
now destruct x.
replace (nth n (map (fun _ : R => Xmask (Xreal 0) x) terms) Xnan) with (Xmask (Xreal 0) x).
rewrite map_nth.
apply Xderive_pt_constant.
rewrite (nth_indep _ Xnan (Xmask (Xreal 0) x) H).
apply sym_eq.
exact (map_nth _ _ R0 _).
Qed.

Lemma unary_diff_bnd_correct :
  forall prec o f f',
  let u x := unary (diff_operations _ ext_operations) o (f x, f' x) in
  forall yi yi' xi,  
 (forall x, contains xi x -> contains (I.convert yi) (f x)) ->
 (forall x, contains xi x -> contains (I.convert yi') (f' x)) ->
  let v := unary (diff_operations _ (bnd_operations prec)) o (yi, yi') in
 (forall x, contains xi x -> contains (I.convert (snd v)) (snd (u x))).
intros prec o f f' u yi yi' xi Hf Hf' v x Hx.
destruct o ; simpl ;
  repeat first
  [ apply I.neg_correct
  | apply I.abs_correct
  | apply I.inv_correct
  | apply I.sqr_correct
  | apply I.sqrt_correct
  | apply I.cos_correct
  | apply I.sin_correct
  | apply I.tan_correct
  | apply I.atan_correct
  | apply I.add_correct
  | apply I.mul_correct
  | apply I.div_correct
  | apply I.fromZ_correct
  | refine (I.add_correct _ _ _ (Xreal (Z2R 1)) _ _ _) ] ;
  now first [ apply Hf | apply Hf' ].
Qed.

Lemma binary_diff_bnd_correct :
  forall prec o f1 f2 f1' f2',
  let u x := binary (diff_operations _ ext_operations) o (f1 x, f1' x) (f2 x, f2' x) in
  forall yi1 yi2 yi1' yi2' xi,  
 (forall x, contains xi x -> contains (I.convert yi1) (f1 x)) ->
 (forall x, contains xi x -> contains (I.convert yi2) (f2 x)) ->
 (forall x, contains xi x -> contains (I.convert yi1') (f1' x)) ->
 (forall x, contains xi x -> contains (I.convert yi2') (f2' x)) ->
  let v := binary (diff_operations _ (bnd_operations prec)) o (yi1, yi1') (yi2, yi2') in
 (forall x, contains xi x -> contains (I.convert (snd v)) (snd (u x))).
intros prec o f1 f2 f1' f2' u yi1 yi2 yi1' yi2' xi Hf1 Hf2 Hf1' Hf2' v x Hx.
destruct o ; simpl ;
  repeat first
  [ apply I.add_correct
  | apply I.sub_correct
  | apply I.mul_correct
  | apply I.div_correct ] ;
  now first [ apply Hf1 | apply Hf2 | apply Hf1' | apply Hf2' ].
Qed.

Lemma eval_diff_bnd_correct :
  forall prec prog bounds n,
  let ff' x := nth n (eval_generic (Xreal 0, Xnan) (diff_operations _ ext_operations) prog ((x, Xmask (Xreal 1) x) :: map (fun v => (Xreal v, Xmask (Xreal 0) x)) (map real_from_bp bounds))) (Xreal 0, Xnan) in
  let ffi' xi := nth n (eval_generic (I.nai, I.nai) (diff_operations _ (bnd_operations prec)) prog
    ((xi, I.mask (I.fromZ 1) xi) :: map (fun b => (b, I.mask (I.fromZ 0) xi)) (map interval_from_bp bounds))) (I.nai, I.nai) in
  forall xi,
  nth n (eval_bnd prec prog (xi :: map interval_from_bp bounds)) I.nai = fst (ffi' xi) /\
 (forall x, contains (I.convert xi) x -> contains (I.convert (snd (ffi' xi))) (snd (ff' x))).
intros prec prog bounds n ff' ffi' xi.
split.
(* . *)
unfold ffi', eval_bnd.
apply (eval_inductive_prop _ (I.type * I.type) (fun a b => a = fst b)).
apply refl_equal.
intros o a (bl, br) H.
rewrite H.
now destruct o.
intros o a1 a2 (bl1, br1) (bl2, br2) H1 H2.
rewrite H1, H2.
now destruct o.
clear.
intros [|n].
apply refl_equal.
simpl.
rewrite <- map_nth.
rewrite map_map.
simpl.
apply sym_eq.
exact (map_nth _ _ _ _).
(* . *)
refine (let toto := _ in fun x Hx => proj2 (toto x Hx : contains (I.convert (fst (ffi' xi))) (fst (ff' x)) /\ _)).
apply (eval_inductive_prop_fun (ExtendedR * _) (I.type * _) (fun a b =>
  forall x, contains (I.convert xi) x ->
  contains (I.convert (fst b)) (fst (a x)) /\
  contains (I.convert (snd b)) (snd (a x)))).
intros f1 f2 Heq (yi, yi') H x Hx.
rewrite <- Heq.
now apply H.
intros _ _.
simpl.
rewrite I.nai_correct.
now split.
intros o f (yi, yi') H x Hx.
rewrite (surjective_pairing (f x)).
split.
assert (Hf := proj1 (H x Hx)).
destruct o ; simpl ;
  [ apply I.neg_correct
  | apply I.abs_correct
  | apply I.inv_correct
  | apply I.sqr_correct
  | apply I.sqrt_correct
  | apply I.cos_correct
  | apply I.sin_correct
  | apply I.tan_correct
  | apply I.atan_correct ] ;
  exact Hf.
apply (unary_diff_bnd_correct prec o (fun x => fst (f x)) (fun x => snd (f x))) with (3 := Hx).
exact (fun x Hx => proj1 (H x Hx)).
exact (fun x Hx => proj2 (H x Hx)).
intros o f1 f2 (yi1, yi1') (yi2, yi2') H1 H2 x Hx.
rewrite (surjective_pairing (f1 x)).
rewrite (surjective_pairing (f2 x)).
split.
assert (Hf1 := proj1 (H1 x Hx)).
assert (Hf2 := proj1 (H2 x Hx)).
destruct o ; simpl ;
  [ apply I.add_correct
  | apply I.sub_correct
  | apply I.mul_correct
  | apply I.div_correct ] ;
  first [ exact Hf1 | exact Hf2 ].
apply (binary_diff_bnd_correct prec o (fun x => fst (f1 x)) (fun x => fst (f2 x)) (fun x => snd (f1 x)) (fun x => snd (f2 x))) with (5 := Hx).
exact (fun x Hx => proj1 (H1 x Hx)).
exact (fun x Hx => proj1 (H2 x Hx)).
exact (fun x Hx => proj2 (H1 x Hx)).
exact (fun x Hx => proj2 (H2 x Hx)).
clear.
intros [|n] x Hx ; simpl.
split.
exact Hx.
apply I.mask_correct.
apply I.fromZ_correct.
exact Hx.
split.
rewrite <- (map_nth (@fst I.type I.type)).
rewrite <- (map_nth (@fst ExtendedR ExtendedR)).
do 4 rewrite map_map.
simpl.
replace (map (fun x => interval_from_bp x) bounds) with (map interval_from_bp bounds).
replace (map (fun x => Xreal (real_from_bp x)) bounds) with (map xreal_from_bp bounds).
apply iterated_bnd_nth.
apply map_ext.
now destruct a.
apply map_ext.
now destruct a.
rewrite <- (map_nth (@snd I.type I.type)).
rewrite <- (map_nth (@snd ExtendedR ExtendedR)).
do 4 rewrite map_map.
simpl.
assert (H1 := map_length (fun _ => I.mask (I.fromZ 0) xi) bounds).
assert (H2 := map_length (fun _ => Xmask (Xreal 0) x) bounds).
destruct (le_or_lt (length bounds) n).
generalize H. intro H0.
rewrite <- H1 in H.
rewrite <- H2 in H0.
rewrite nth_overflow with (1 := H).
rewrite nth_overflow with (1 := H0).
now rewrite I.nai_correct.
replace (nth n (map (fun _ => I.mask (I.fromZ 0) xi) bounds) I.nai) with (I.mask (I.fromZ 0) xi).
replace (nth n (map (fun _ => Xmask (Xreal 0) x) bounds) Xnan) with (Xmask (Xreal 0) x).
apply I.mask_correct.
apply I.fromZ_correct.
exact Hx.
rewrite <- H2 in H.
rewrite (nth_indep _ Xnan (Xmask (Xreal 0) x) H).
apply sym_eq.
refine (map_nth _ bounds (Bproof 0 I.nai _) _).
now rewrite I.nai_correct.
rewrite <- H1 in H.
rewrite (nth_indep _ I.nai (I.mask (I.fromZ 0) xi) H).
apply sym_eq.
refine (map_nth _ bounds (Bproof 0 I.nai _) _).
now rewrite I.nai_correct.
Qed.

(*
(* Note: The derivative of default values is set to NaN, which is sub-optimal, but they are not supposed to be used anyway. *)
Lemma eval_diff_correct_aux :
  forall formula terms n,
  let f x := nth n (eval_generic (Xreal 0, Xnan) (diff_operations _ ext_operations) formula ((x, Xmask (Xreal 1) x) :: map (fun v => (Xreal v, Xmask (Xreal 0) x)) terms)) (Xreal 0, Xnan) in
  Xderive (fun x => fst (f x)) (fun x => snd (f x)).
intros.
pose (g := fun n x =>
       nth n
          (fold_right
             (fun t l =>
              eval_generic_body (Xreal 0, Xnan)
                (diff_operations ExtendedR ext_operations) l t)
             ((x, Xmask (Xreal 1) x)
              :: map (fun v => (Xreal v, Xmask (Xreal 0) x)) terms) (rev formula))
          (Xreal 0, Xnan)).
apply Xderive_eq with (fun x => fst (g n x)) (fun x => snd (g n x)) ;
  try (intros ; unfold f ; now rewrite rev_formula).
generalize n. clear.
induction (rev formula).
(* empty formula *)
simpl in g.
intros [|n].
apply Xderive_identity.
generalize n. clear n.
induction terms.
now intros [|n] [|x].
intros [|n] ; simpl.
apply Xderive_constant.
apply IHterms.
(* non-empty formulas *)
intros [|n].
unfold g. simpl. clear -IHl.
induction a.
eapply Xderive_eq.
3: eexact (unary_diff_correct u _ _ (IHl n)).
intros x. simpl.
now match goal with |- context [match ?p with (v, d) => _ end] => destruct p end.
intros x. simpl.
now match goal with |- context [match ?p with (v, d) => _ end] => destruct p end.
eapply Xderive_eq.
3: eexact (binary_diff_correct b _ _ _ _ (IHl n) (IHl n0)).
intros x. simpl.
now do 2 match goal with |- context [match ?p with (v, d) => _ end] => destruct p end.
intros x. simpl.
now do 2 match goal with |- context [match ?p with (v, d) => _ end] => destruct p end.
exact (IHl n).
Qed.

Theorem eval_diff_correct :
  forall prog terms n,
  Xderive
    (fun x => nth n (eval_ext prog (x :: map (fun v => Xreal v) terms)) (Xreal R0))
    (fun x => snd (nth n (eval_generic (Xreal 0, Xnan) (diff_operations _ ext_operations) prog ((x, Xmask (Xreal 1) x) :: map (fun v => (Xreal v, Xmask (Xreal 0) x)) terms)) (Xreal 0, Xnan))).
intros.
eapply Xderive_eq_fun.
2: apply (eval_diff_correct_aux prog terms n).
intros x.
unfold eval_ext.
generalize n. clear n.
apply (eval_inductive_prop _ (ExtendedR * ExtendedR) (fun a b => a = fst b)).
apply refl_equal.
intros i.
apply refl_equal.
intros o a (b, c) H.
rewrite H.
now case o.
intros o a1 a2 (b1, c1) (b2, c2) H1 H2.
rewrite H1, H2.
now case o.
intros [|n].
apply refl_equal.
simpl.
rewrite map_nth.
rewrite <- map_nth.
rewrite map_map.
simpl.
now rewrite map_nth.
Qed.
*)

Module Algos := IntervalAlgos I.

Definition eval_diff prec formula bounds n xi :=
  match nth n (eval_generic (I.nai, I.nai) (diff_operations _ (bnd_operations prec)) formula
    ((xi, I.mask (I.fromZ 1) xi) :: map (fun b => (b, I.mask (I.fromZ 0) xi)) bounds)) (I.nai, I.nai) with
  | (yi, yi') =>
    Algos.diff_refining prec xi yi yi'
      (fun b => nth n (eval_bnd prec formula (b :: bounds)) I.nai)
  end.

Theorem eval_diff_correct_ext :
  forall prec prog bounds n,
  I.extension
    (fun x => nth n (eval_ext prog (x :: map xreal_from_bp bounds)) (Xreal 0))
    (fun b => eval_diff prec prog (map interval_from_bp bounds) n b).
intros prec prog bounds n xi x Hx.
unfold eval_diff.
pose (f := fun x => nth n (eval_ext prog (x :: map xreal_from_bp bounds)) (Xreal 0)).
fold (f x).
pose (ff' := fun x => nth n (eval_generic (Xreal 0, Xnan) (diff_operations _ ext_operations) prog
     ((x, Xmask (Xreal 1) x) :: map (fun v => (Xreal v, Xmask (Xreal 0) x)) (map real_from_bp bounds))) (Xreal 0, Xnan)).
set (fi := fun xi => nth n (eval_bnd prec prog (xi :: map interval_from_bp bounds)) I.nai).
pose (ffi' := fun xi => nth n (eval_generic (I.nai, I.nai) (diff_operations _ (bnd_operations prec)) prog
     ((xi, I.mask (I.fromZ 1) xi) :: map (fun b => (b, I.mask (I.fromZ 0) xi)) (map interval_from_bp bounds))) (I.nai, I.nai)).
fold (ffi' xi).
rewrite (surjective_pairing (ffi' xi)).
refine (_ (eval_diff_bnd_correct prec prog bounds n)).
intros H.
replace (fst (ffi' xi)) with (fi xi).
pose (fi' := fun xi => snd (ffi' xi)).
fold (fi' xi).
pose (f' x := snd (ff' x)).
refine (Algos.diff_refining_correct prec f f' _ _ _ _ _ xi x Hx) ;
  clear Hx xi x.
(* . *)
apply eval_bnd_correct_ext.
intros xi x Hx.
exact (proj2 (H xi) x Hx).
intros x.
generalize (proj2 (eval_diff_correct prog (map real_from_bp bounds) n x)).
fold (ff' x).
replace (map Xreal (map real_from_bp bounds)) with (map xreal_from_bp bounds).
fold f.
exact (fun p => p).
rewrite map_map.
apply map_ext.
now destruct a.
exact (proj1 (H xi)).
Qed.

(*
Inductive first_order_data : Type :=
  FO_data (y y' ym yl yu : I.type) : first_order_data.

Definition first_order_operations prec x dx :=
  let ops := bnd_operations prec in
  let dops := diff_operations _ ops in
  Build_operations
   (fun a => let y := I.fromZ a in FO_data y (I.fromZ 0) y y y)
   (fun o a =>
    let 'FO_data ay ay' am al au := a in
    let '(cy, cy') := unary dops o (ay, ay') in
    let op := unary ops o in
    FO_data cy cy' (op am) (op al) (op au))
   (fun o a b =>
    let 'FO_data ay ay' am al au := a in
    let 'FO_data by by' bm bl bu := b in
    let '(cy, cy') := binary dops o (ay, ay') (by, by') in
    let op := binary ops o in
    let cm := op am bm in
    let cl := op al bl in
    let cu := op au bu in
    let cy2 := Algos.diff_refining_points prec x dx cy cy' cm cl cu in
    FO_data cy2 cy' cm cl cu).

Definition FO_def := FO_data I.nai I.nai I.nai I.nai I.nai.

Definition eval_first_order prec prog bounds xi :=
  let xm := I.midpoint xi in
  let mm := I.bnd xm xm in
  eval_generic FO_def (first_order_operations prec xi (I.sub prec xi mm)) prog
    ((FO_data xi (I.mask (I.fromZ 1) xi) mm
       (if I.lower_bounded xi then let l := I.lower xi in I.bnd l l else I.nai (*I.lower_extent mm*))
       (if I.upper_bounded xi then let u := I.upper xi in I.bnd u u else I.nai (*I.upper_extent mm*))) ::
     map (fun b => FO_data b (I.mask (I.fromZ 0) xi) b b b) bounds).

Definition FO_prop xi f v :=
  let 'FO_data yi yi' ym yl yu := v in
 (forall x, contains (I.convert xi) x -> contains (I.convert yi) (f x)) /\
 (exists f', Xderive f f' /\ forall x, contains (I.convert xi) x -> contains (I.convert yi') (f' x)) /\
  contains (I.convert ym) (f (I.convert_bound (I.midpoint xi))) /\
 (if I.lower_bounded xi then
    contains (I.convert yl) (f (I.convert_bound (I.lower xi)))
  else True) /\
 (if I.upper_bounded xi then
    contains (I.convert yu) (f (I.convert_bound (I.upper xi)))
  else True).

Lemma eval_first_order_correct_aux :
  forall prec prog terms bounds,
 (forall n, contains (I.convert (nth n bounds I.nai)) (nth n terms (Xreal 0))) ->
  forall xi n,
  FO_prop xi (fun x => nth n (eval_ext prog (x :: terms)) (Xreal 0))
   (nth n (eval_first_order prec prog bounds xi) FO_def).
intros prec prog terms bounds Hinp xi n.
unfold eval_first_order.
apply (eval_inductive_prop_fun _ (FO_prop xi)).
(* extensionality *)
clear.
intros a1 a2 Heq (yi, yi', ym, yl, yu).
intros (H1, ((f', (H2, H3)), (H4, (H5, H6)))).
repeat split ; try now rewrite <- Heq.
intros.
rewrite <- Heq.
now apply H1.
exists f'.
split.
apply Xderive_eq_fun with (2 := H2).
intros.
now apply sym_eq.
exact H3.
(* default *)
simpl.
rewrite I.nai_correct.
repeat split.
exists (Xmask (Xreal 0)).
repeat split.
exact (Xderive_pt_constant 0).
now case (I.lower_bounded xi).
now case (I.upper_bounded xi).
(* unary *)
intros o a (b, b', bm, bl, bu) (H1, ((c', (H2, H3)), (H4, (H5, H6)))).
unfold FO_prop, first_order_operations, unary at 1.
case_eq (unary (diff_operations I.type (bnd_operations prec)) o (b, b')).
intros d d' Hu.
repeat split.
intros x Hx.
Admitted.

CoInductive Lazy := Data (v : I.type) : Lazy.
CoFixpoint lazy (f : unit -> I.type) := let v := f tt in Data v.
Definition force (v : Lazy) := match v with Data w => w end.

Inductive first_order_data2 : Type :=
  FO_data2 (y y' : I.type) (ym yl yu : Lazy) : first_order_data2.

Definition first_order_operations2 prec x dx :=
  let ops := bnd_operations prec in
  let dops := diff_operations _ ops in
  Build_operations
   (fun a =>
    let y := I.fromZ a in
    let ly := lazy (fun _ => y) in
    FO_data2 y (I.fromZ 0) ly ly ly)
   (fun o a =>
    let 'FO_data2 ay ay' am al au := a in
    let '(cy, cy') := unary dops o (ay, ay') in
    let op := unary ops o in
    FO_data2 cy cy' (lazy (fun _ => op (force am))) (lazy (fun _ => op (force al))) (lazy (fun _ => op (force au))))
   (fun o a b =>
    let 'FO_data2 ay ay' am al au := a in
    let 'FO_data2 by by' bm bl bu := b in
    let '(cy, cy') := binary dops o (ay, ay') (by, by') in
    let op := binary ops o in
    match I.sign_large cy' with
    | Xund | Xeq =>
      let cm := op (force am) (force bm) in
      let cy2 := Algos.diff_refining_points prec x dx cy cy' cm I.nai I.nai in
      FO_data2 cy2 cy' (lazy (fun _ => cm)) (lazy (fun _ => op (force al) (force bl))) (lazy (fun _ => op (force au) (force bu)))
    | Xlt | Xgt =>
      let cl := op (force al) (force bl) in
      let cu := op (force au) (force bu) in
      let cy2 := Algos.diff_refining_points prec x dx cy cy' I.nai cl cu in
      FO_data2 cy2 cy' (lazy (fun _ => op (force am) (force bm))) (lazy (fun _ => cl)) (lazy (fun _ => cu))
    end).

Definition FO_def2 :=
  let lnai := lazy (fun _ =>I.nai) in
  FO_data2 I.nai I.nai lnai lnai lnai.

Definition eval_first_order2 prec prog bounds xi :=
  let xm := I.midpoint xi in
  let mm := I.bnd xm xm in
  eval_generic FO_def2 (first_order_operations2 prec xi (I.sub prec xi mm)) prog
    ((FO_data2 xi (I.mask (I.fromZ 1) xi) (lazy (fun _ => mm))
       (lazy (fun _ => if I.lower_bounded xi then let l := I.lower xi in I.bnd l l else I.nai (*I.lower_extent mm*)))
       (lazy (fun _ => if I.upper_bounded xi then let u := I.upper xi in I.bnd u u else I.nai (*I.upper_extent mm*)))) ::
     map (fun b => let lb := lazy (fun _ => b) in FO_data2 b (I.mask (I.fromZ 0) xi) lb lb lb) bounds).

Definition eval_first_order_nth prec prog bounds n xi :=
  match nth n (eval_first_order2 prec prog bounds xi) FO_def2 with
  | FO_data2 yi _ _ _ _ => yi
  end.

Theorem eval_first_order_correct_ext :
  forall prec prog bounds n,
  I.extension
    (fun x => nth n (eval_ext prog (x :: map xreal_from_bp bounds)) (Xreal 0))
    (fun b => eval_first_order_nth prec prog (map interval_from_bp bounds) n b).
intros prec prog bounds n xi x Hx.
Admitted.
*)

End Valuator.
