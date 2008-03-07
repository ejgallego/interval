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

Theorem diff_refining_aux_1 :
  forall prec f f' xi yi yi' m mi ymi,
  Xderive f f' ->
  contains (I.convert mi) (Xreal m) ->
  contains (I.convert xi) (Xreal m) ->
  contains (I.convert ymi) (f (Xreal m)) ->
 (forall x, contains (I.convert xi) x -> contains (I.convert yi) (f x)) ->
 (forall x, contains (I.convert xi) x -> contains (I.convert yi') (f' x)) ->
  forall x, contains (I.convert xi) x ->
  contains (I.convert (I.add prec ymi (I.mul prec (I.sub prec xi mi) yi'))) (f x).
intros prec f f' xi yi yi' m mi ymi Hd Hxm Hm Hym Hy Hy' x Hx.
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
rewrite Hxi in Hy.
generalize (Hy' _ Hx).
rewrite Hyi'.
generalize (Hd Xnan).
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

Theorem diff_refining_aux_2 :
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

Theorem diff_refining_correct :
  forall prec f f' fi fi',
  I.extension f fi ->
  I.extension f' fi' ->
  Xderive f f' ->
  I.extension f (fun b => diff_refining prec b (fi b) (fi' b) fi).
intros prec f f' fi fi' Hf Hf' Hd xi x Hx.
unfold diff_refining.
generalize (I.sign_large_correct (fi' xi)).
case (I.sign_large (fi' xi)) ; intro Hs.
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
rewrite (Hs (f' x0)).
split ; apply Rle_refl.
apply Hf'.
exact H.
exact Hx.
intro H.
rewrite H in Hs.
generalize (Hs Xnan I).
discriminate.
(* - sign is Xlt *)
apply I.meet_correct.
admit.
admit.
(*
case_eq (I.lower_bounded xi) ; intro Hlb.
destruct (I.lower_bounded_correct _ Hlb) as (xl,Hxi).
case_eq (f x).
intro Hy.
apply False_ind.
generalize (Hd x).
destruct x as [|x].
rewrite Hxi in Hx.
elim Hx.
destruct (Hs _ (Hf' _ _ Hx)) as (y', (Hy1', Hy2')).
now rewrite Hy1', Hy.
intros r Hy.
apply I.lower_extent_correct.
case_eq (I.convert (fi (I.bnd (I.lower xi) (I.lower xi)))).
intros _.
exists r.
split.
apply Rle_refl.
exact I.
intros yl yu Hyi.
generalize (Hf _ _ Hx).
rewrite Hy.
intros Hyi yl [|yu] Hyi2.
*)
(* - sign is Xgt *)
admit.
(* - sign is Xund *)
clear Hs.
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
apply Hf.
apply Hf'.
exact Hx.
destruct (I.bounded_correct _ Hb) as (l, (u, H)).
rewrite H.
discriminate.
now apply Hf.
Qed.

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

Record operations (A : Set) : Set :=
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

Lemma xreal_to_real_aux :
  forall formula terms n x,
  nth n (eval_ext formula (map Xreal terms)) (Xreal 0) = Xreal x ->
  nth n (eval_real formula terms) R0 = x.
intros formula terms n x.
unfold eval_ext, eval_real.
do 2 rewrite rev_formula.
generalize n x. clear.
induction (rev formula).
(* empty formula *)
simpl.
intros n x H.
apply (@f_equal _ _ (fun v => match v with Xreal r => r | Xnan => R0 end)
       (Xreal (nth n terms R0)) (Xreal x)).
rewrite <- H.
generalize n.
clear.
induction terms.
intro n. case n ; intros ; apply refl_equal.
intro n. case n.
apply refl_equal.
exact IHterms.
(* non-empty formula *)
intros n.
case n.
case a ; simpl ; intros.
destruct (unary_ext_correct u _ _ H) as (y, (H1, H2)).
rewrite (IHl _ _ H1).
exact H2.
destruct (binary_ext_correct b _ _ _ H) as (y, (H1, (z, (H2, H3)))).
rewrite (IHl _ _ H1).
rewrite (IHl _ _ H2).
exact H3.
exact IHl.
Qed.

Lemma xreal_to_real :
  forall formula terms n xi,
  contains xi (nth n (eval_ext formula (map Xreal terms)) (Xreal 0)) ->
  contains xi (Xreal (nth n (eval_real formula terms) R0)).
intros formula terms n xi.
case xi.
split.
intros l u.
case_eq (nth n (eval_ext formula (map Xreal terms)) (Xreal 0)).
intros _ H.
elim H.
intros r H1 H2.
rewrite (xreal_to_real_aux _ _ _ _ H1).
exact H2.
Qed.

Inductive bound_proof :=
  | Bproof : forall x xi, contains (I.convert xi) x -> bound_proof.

Definition xreal_from_bp v := match v with Bproof x _ _ => x end.
Definition interval_from_bp v := match v with Bproof _ xi _ => xi end.

Lemma iterated_bnd_nth :
  forall bounds n,
  contains (I.convert (nth n (map interval_from_bp bounds) I.nai))
    (nth n (map xreal_from_bp bounds) (Xreal R0)).
intros.
assert (contains (I.convert I.nai) (Xreal 0)).
now rewrite I.nai_correct.
pose (b := Bproof (Xreal R0) I.nai H).
change (Xreal 0) with (xreal_from_bp b).
change I.nai with (interval_from_bp b).
do 2 rewrite map_nth.
now case (nth n bounds b).
Qed.

Theorem eval_bnd_correct :
  forall prec formula bounds n,
  contains (I.convert (nth n (eval_bnd prec formula (map interval_from_bp bounds)) I.nai))
   (nth n (eval_ext formula (map xreal_from_bp bounds)) (Xreal 0)).
intros.
unfold eval_bnd, eval_ext.
do 2 rewrite rev_formula.
generalize n. clear n.
induction (rev formula).
simpl.
apply iterated_bnd_nth.
intros.
case n.
case a ; intros ; simpl ;
  [ case u ; [ apply I.neg_correct
             | apply I.abs_correct
             | apply I.inv_correct
             | apply I.sqr_correct
             | apply I.sqrt_correct
             | apply I.cos_correct
             | apply I.sin_correct
             | apply I.tan_correct
             | apply I.atan_correct ]
  | case b ; [ apply I.add_correct
             | apply I.sub_correct
             | apply I.mul_correct
             | apply I.div_correct ]
  ] ; apply IHl.
apply IHl.
Qed.

Theorem eval_bnd_correct_ext :
  forall prec formula bounds n,
  I.extension
    (fun x => nth n (eval_ext formula (x :: map xreal_from_bp bounds)) (Xreal R0))
    (fun b => nth n (eval_bnd prec formula (b :: map interval_from_bp bounds)) I.nai).
unfold I.extension.
intros.
exact (eval_bnd_correct _ _ (Bproof x b H :: bounds) _).
Qed.

Theorem Xderive_eq :
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

(* Note: The derivative of default values is set to NaN, which is sub-optimal, but they are not supposed to be used anyway. *)
Theorem eval_diff_correct_aux :
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
  forall formula terms n,
  Xderive
    (fun x => nth n (eval_ext formula (x :: map (fun v => Xreal v) terms)) (Xreal R0))
    (fun x => snd (nth n (eval_generic (Xreal 0, Xnan) (diff_operations _ ext_operations) formula ((x, Xmask (Xreal 1) x) :: map (fun v => (Xreal v, Xmask (Xreal 0) x)) terms)) (Xreal 0, Xnan))).
intros.
eapply Xderive_eq_fun.
2: apply (eval_diff_correct_aux formula terms n).
intros x.
unfold eval_ext.
do 2 rewrite rev_formula.
generalize n. clear.
induction (rev formula).
(* empty formula *)
simpl.
intros [|n].
apply refl_equal.
generalize n. clear n.
induction terms.
now intros [|n].
intros [|n].
apply refl_equal.
simpl.
apply IHterms.
(* non-empty formula *)
intros [|n].
induction a.
simpl.
rewrite IHl.
match goal with |- context [match ?p with (v, d) => _ end] => destruct p end.
now case u.
simpl.
do 2 rewrite IHl.
do 2 match goal with |- context [match ?p with (v, d) => _ end] => destruct p end.
now case b.
simpl.
apply IHl.
Qed.

Module Algos := IntervalAlgos I.

Definition eval_diff prec formula bounds n xi :=
  match nth n (eval_generic (I.nai, I.nai) (diff_operations _ (bnd_operations prec)) formula
    ((xi, I.mask (I.fromZ 1) xi) :: map (fun b => (b, I.mask (I.fromZ 0) b)) bounds)) (I.nai, I.nai) with
  | (yi, yi') =>
    Algos.diff_refining prec xi yi yi'
      (fun b => nth n (eval_bnd prec formula (b :: bounds)) I.nai)
  end.

Theorem eval_diff_correct_ext :
  forall prec formula bounds n,
  I.extension
    (fun x => nth n (eval_ext formula (x :: map xreal_from_bp bounds)) (Xreal 0))
    (fun b => eval_diff prec formula (map interval_from_bp bounds) n b).
intros.
set (f := fun x => nth n (eval_ext formula (x :: map xreal_from_bp bounds)) (Xreal 0)).
set (fi := fun xi => nth n (eval_bnd prec formula (xi :: map interval_from_bp bounds)) I.nai).
intros b x Hb.
unfold eval_diff.
set (ff' := fun xi => nth n (eval_generic (I.nai, I.nai) (diff_operations _ (bnd_operations prec)) formula
    ((xi, I.mask (I.fromZ 1) xi) :: map (fun b => (b, I.mask (I.fromZ 0) b)) (map interval_from_bp bounds))) (I.nai, I.nai)).
set (fi' := fun xi => snd (ff' xi)).
match goal with |- context [match ?v with (yi, yi') => _ end] => replace v with (fi b, fi' b) end.
(*
set (f' := (fun x => snd (nth n (eval_generic (Xreal 0, Xnan) (diff_operations _ ext_operations) formula
    ((x, Xmask (Xreal 1) x) :: map (fun v => (Xreal v, Xmask (Xreal 0) x)) (map xreal_from_bp bounds))) (Xreal 0, Xnan)))).
refine (Algos.diff_refining_correct prec f f' _ _ _ _ _ b x H).
unfold f, fi.
apply eval_bnd_correct_ext.
admit.
admit.
*)
Admitted.

End Valuator.
