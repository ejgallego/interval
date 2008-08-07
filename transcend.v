Require Import Reals.
Require Import missing.
Require Import xreal.
Require Import definitions.
Require Import float_sig.
Require Import generic.
Require Import generic_proof.
Require Import interval.
Require Import interval_float.

Module TranscendentalFloatFast (F : FloatOps with Definition even_radix := true).

Module I := FloatInterval F.

CoInductive constant : Type :=
  | Consts: I.type -> constant -> constant.

Fixpoint constant_getter_aux n cst :=
  match cst, n with
  | Consts xi _, O => xi
  | Consts _ c, S p => constant_getter_aux p c
  end.

Definition constant_getter cst prec :=
  let nb := Zabs_nat (Zpred (fst (Zdiv.Zdiv_eucl_POS (F.prec prec + 30)%positive 31%Z))) in
  constant_getter_aux nb cst.

CoFixpoint constant_generator_aux gen n :=
  Consts (gen (F.PtoP (n * 31)%positive)) (constant_generator_aux gen (Psucc n)).

Definition constant_generator gen :=
  constant_generator_aux gen 1.

(* 0 <= inputs *)
Fixpoint atan_fast0_aux prec thre powl powu sqrl sqru two div (nb : nat) { struct nb } :=
  let npwu := F.mul rnd_UP prec powu sqru in
  let valu := F.div rnd_UP prec npwu div in
  match F.cmp valu thre, nb with
  | Xlt, _
  | _, O => I.bnd F.zero valu
  | _, S n =>
    let npwl := F.mul rnd_DN prec powl sqrl in
    let vall := F.div rnd_DN prec npwl div in
    I.sub prec (I.bnd vall valu)
      (atan_fast0_aux prec thre npwl npwu sqrl sqru two (F.add_exact div two) n)
  end.

(*
Definition atan_fast0_aux prec thre powl powu sqrl sqru two div nb :=
  let fix aux powl powu div (nb : nat) { struct nb } :=
    let npwu := F.mul rnd_UP prec powu sqru in
    let valu := F.div rnd_UP prec npwu div in
    match F.cmp valu thre, nb with
    | Xlt, _ => I.bnd (F.neg valu) valu
    | _, O => I.bnd (F.neg valu) valu
    | _, S n =>
      let npwl := F.mul rnd_DN prec powl sqrl in
      let vall := F.div rnd_DN prec npwl div in
      I.sub prec (I.bnd vall valu)
        (aux npwl npwu (F.add_exact div two) n)
    end in
  aux powl powu div nb.
*)

(* -1/2 <= input <= 1/2 *)
Definition atan_fast0 prec x :=
  let x2l := F.mul rnd_DN prec x x in
  let x2u := F.mul rnd_UP prec x x in
  let c1 := F.fromZ 1 in
  let p := F.prec prec in
  let thre := F.scale c1 (F.ZtoS (Zneg p)) in
  let rem := atan_fast0_aux prec thre c1 c1 x2l x2u (F.fromZ 2) (F.fromZ 3) (nat_of_P p) in
  I.mul_mixed prec (I.sub prec (I.bnd c1 c1) rem) x.

(* -1/2 <= input <= 1/2 *)
Definition atan_fast0i prec xi :=
  let x2 := I.sqr prec xi in
  let c1 := F.fromZ 1 in
  let p := F.prec prec in
  let thre := F.scale c1 (F.ZtoS (Zneg p)) in
  let rem := atan_fast0_aux prec thre c1 c1 (I.lower x2) (I.upper x2) (F.fromZ 2) (F.fromZ 3) (nat_of_P p) in
  I.mul prec (I.sub prec (I.bnd c1 c1) rem) xi.

Definition pi4_gen prec :=
  let s2 := F.ZtoS 2 in
  I.sub prec
   (I.scale2 (atan_fast0i prec (I.inv prec (I.fromZ 5))) s2)
   (atan_fast0i prec (I.inv prec (I.fromZ 239))).

Definition pi4_seq := constant_generator pi4_gen.
Definition pi4 := constant_getter pi4_seq.

Definition atan_fastP prec x :=
  let c1 := F.fromZ 1 in
  match F.cmp x (F.scale2 c1 (F.ZtoS (-1)%Z)) with
  | Xgt =>
    let pi4i := pi4 prec in
    let s1 := F.ZtoS 1%Z in
    match F.cmp x (F.scale2 c1 s1) with
    | Xgt =>
      I.sub prec
       (I.scale2 pi4i s1)
       (atan_fast0i prec (I.bnd (F.div rnd_DN prec c1 x) (F.div rnd_UP prec c1 x)))
    | _ =>
      let xm1 := F.sub_exact x c1 in
      let xp1 := F.add_exact x c1 in
      I.add prec pi4i
       (atan_fast0i prec (I.bnd (F.div rnd_DN prec xm1 xp1) (F.div rnd_UP prec xm1 xp1)))
    end
  | _ => atan_fast0 prec x
  end.

Definition atan_fast prec x :=
  match F.cmp x F.zero with
  | Xeq => I.bnd F.zero F.zero
  | Xlt => I.neg (atan_fastP prec (F.neg x))
  | Xgt => atan_fastP prec x
  | Xund => I.nai
  end.

(* 0 <= inputs *)
Fixpoint cos_fast0_aux prec thre powl powu sqrl sqru fact div (nb : nat) { struct nb } :=
  let npwu := F.mul rnd_UP prec powu sqru in
  let valu := F.div rnd_UP prec npwu div in
  match F.cmp valu thre, nb with
  | Xlt, _
  | _, O => I.bnd F.zero valu
  | _, S n =>
    let npwl := F.mul rnd_DN prec powl sqrl in
    let vall := F.div rnd_DN prec npwl div in
    let one := F.fromZ 1 in
    let nfact := F.add_exact fact (F.add_exact one one) in
    let ndiv := F.mul_exact div (F.mul_exact fact (F.add_exact fact one)) in
    I.sub prec (I.bnd vall valu)
      (cos_fast0_aux prec thre npwl npwu sqrl sqru nfact ndiv n)
  end.

(* -1/2 <= input <= 1/2 *)
Definition cos_fast0 prec x :=
  let x2l := F.mul rnd_DN prec x x in
  let x2u := F.mul rnd_UP prec x x in
  let c1 := F.fromZ 1 in
  let p := F.prec prec in
  let thre := F.scale c1 (F.ZtoS (Zneg p)) in
  let rem := cos_fast0_aux prec thre c1 c1 x2l x2u (F.fromZ 3) (F.fromZ 2) (nat_of_P p) in
  I.sub prec (I.bnd c1 c1) rem.

Definition le x y :=
  match F.cmp x y with
  | Xlt | Xeq => true
  | Xgt | Xund => false
  end.

Definition toR x := proj_val (FtoX (F.toF x)).

Inductive le_prop x y : bool -> Prop :=
  | le_true
    (Hx : FtoX (F.toF x) = Xreal (toR x))
    (Hy : FtoX (F.toF y) = Xreal (toR y))
    (Hxy : (toR x <= toR y)%R) : le_prop x y true
  | le_false : le_prop x y false.

Lemma le_spec :
  forall x y,
  le_prop x y (le x y).
intros.
unfold le.
rewrite F.cmp_correct, Fcmp_correct.
case_eq (FtoX (F.toF x)).
intros _. apply le_false.
intros xr Hx.
case_eq (FtoX (F.toF y)).
intros _. apply le_false.
intros yr Hy.
simpl.
destruct (Rcompare_spec xr yr) ;
  constructor ;
  unfold toR ;
  try rewrite Hx ;
  try rewrite Hy ;
  try apply refl_equal.
now apply Rlt_le.
now apply Req_le.
Qed.

(* 0 <= input *)
Definition sin_cos_reduce prec x :=
  let c1 := F.fromZ 1 in
  let sp1 := F.ZtoS 1%Z in
  let sm1 := F.ZtoS (-1)%Z in
  let i1 := I.bnd c1 c1 in
  let th := F.scale2 c1 sm1 in
  let fix reduce x (nb : nat) {struct nb} :=
    match le x th, nb with
    | true, _ => (Gt, cos_fast0 prec x)
    | _, O => (Eq, I.bnd (F.neg c1) c1)
    | _, S n =>
      match reduce (F.scale2 x sm1) n with
      | (s, c) =>
       (match s, I.sign_large c with
        | Lt, Xgt => Lt
        | Lt, Xlt => Gt
        | Lt, _ => Eq
        | Gt, Xlt => Lt
        | Gt, Xgt => Gt
        | Gt, _ => Eq
        | _, _ => s
        end,
        I.sub prec (I.scale2 (I.sqr prec c) sp1) i1)
      end
    end in
  reduce x.

Axiom cos_fast0_correct :
  forall prec x,
  FtoX (F.toF x) = Xreal (toR x) ->
  (Rabs (toR x) <= /2)%R ->
  contains (I.convert (cos_fast0 prec x)) (Xreal (cos (toR x))).

Lemma scale2_correct :
  forall x d,
  FtoX (F.toF (F.scale2 x (F.ZtoS d))) = Xmul (FtoX (F.toF x)) (Xreal (exp_factor 2 d)).
intros x d.
rewrite F.scale2_correct. 2: apply refl_equal.
rewrite Fscale2_correct. 2: exact F.even_radix_correct.
apply refl_equal.
Qed.

Lemma sin_cos_reduce_correct :
  forall prec nb x,
  FtoX (F.toF x) = Xreal (toR x) ->
  (0 < toR x)%R ->
  match sin_cos_reduce prec x nb with
  | (ss, ci) =>
    contains (I.convert ci) (Xreal (cos (toR x))) /\
    match ss with
    | Lt => (sin (toR x) <= 0)%R
    | Gt => (0 <= sin (toR x))%R
    | _ => True
    end
  end.
intros prec.
(* . *)
assert (forall x, FtoX (F.toF x) = Xreal (toR x) -> (0 < toR x)%R ->
        le x (F.scale2 (F.fromZ 1) (F.ZtoS (-1))) = true ->
        contains (I.convert (cos_fast0 prec x)) (Xreal (cos (toR x))) /\
        (0 <= sin (toR x))%R).
intros x Hxr Hx0 H.
assert (toR x <= /2)%R.
destruct (le_spec x (F.scale2 (F.fromZ 1) (F.ZtoS (-1)))).
2: discriminate H.
clear Hy.
generalize Hxy.
unfold toR at 2.
rewrite scale2_correct.
rewrite F.fromZ_correct.
simpl.
rewrite Rmult_1_l.
now intros.
(* .. *)
split.
apply cos_fast0_correct with (1 := Hxr).
rewrite Rabs_right.
exact H0.
apply Rle_ge.
now apply Rlt_le.
apply sin_ge_0.
now apply Rlt_le.
(*   x <= pi *)
apply Rle_trans with (1 := H0).
apply Rlt_le.
apply Rmult_lt_reg_l with (/4)%R.
apply Rinv_0_lt_compat.
now apply (Z2R_lt 0 4).
rewrite <- (Rmult_comm PI).
apply Rlt_le_trans with (2 := proj1 (PI_ineq 0)).
unfold tg_alt, PI_tg.
simpl.
replace (1 * / 1 + -1 * 1 * / (2 + 1))%R with (13*/24 + /8)%R by field.
replace (/4 * /2)%R with (0 + /8)%R by field.
apply Rplus_lt_compat_r.
apply Rmult_lt_0_compat.
now apply (Z2R_lt 0 13).
apply Rinv_0_lt_compat.
now apply (Z2R_lt 0 24).
(* . *)
induction nb ; intros x Hxr Hx.
(* nb = 0 *)
simpl.
case_eq (le x (F.scale2 (F.fromZ 1) (F.ZtoS (-1)))).
intros.
exact (H x Hxr Hx H0).
intros _.
simpl.
unfold I.convert_bound.
rewrite F.neg_correct, Fneg_correct, F.fromZ_correct.
refine (conj _ I).
simpl.
apply COS_bound.
(* nb > 0 *)
simpl.
case_eq (le x (F.scale2 (F.fromZ 1) (F.ZtoS (-1)))).
intros.
exact (H x Hxr Hx H0).
intros _.
refine (_ (IHnb (F.scale2 x (F.ZtoS (-1))) _ _)).
destruct (sin_cos_reduce prec (F.scale2 x (F.ZtoS (-1))) nb) as (ss, ci).
clear -Hxr.
replace (toR x) with (2 * (toR (F.scale2 x (F.ZtoS (-1)))))%R.
generalize (toR (F.scale2 x (F.ZtoS (-1)))).
clear.
intros hx (Hc, Hs).
split.
(* - cos *)
replace (Xreal (cos (2 * hx))) with (Xsub (Xmul (Xsqr (Xreal (cos hx))) (Xreal 2)) (Xreal 1)).
apply I.sub_correct.
apply I.scale2_correct.
apply I.sqr_correct.
exact Hc.
apply I.fromZ_correct.
simpl.
apply f_equal.
rewrite cos_2a_cos.
ring.
(* - sin *)
rewrite sin_2a.
destruct ss.
exact I.
change (cos hx) with (proj_val (Xreal (cos hx))).
generalize (I.sign_large_correct ci).
case (I.sign_large ci) ; intros ; try exact I.
apply Rmult_le_neg_neg.
apply Rmult_le_pos_neg.
now apply (Z2R_le 0 2).
exact Hs.
exact (proj2 (H _ Hc)).
apply Rmult_le_neg_pos.
apply Rmult_le_pos_neg.
now apply (Z2R_le 0 2).
exact Hs.
exact (proj2 (H _ Hc)).
change (cos hx) with (proj_val (Xreal (cos hx))).
generalize (I.sign_large_correct ci).
case (I.sign_large ci) ; intros ; try exact I.
apply Rmult_le_pos_neg.
apply Rmult_le_pos_pos.
now apply (Z2R_le 0 2).
exact Hs.
exact (proj2 (H _ Hc)).
apply Rmult_le_pos_pos.
apply Rmult_le_pos_pos.
now apply (Z2R_le 0 2).
exact Hs.
exact (proj2 (H _ Hc)).
(* - . *)
unfold toR.
rewrite scale2_correct.
rewrite Hxr.
simpl.
field.
(* - . *)
unfold toR.
now rewrite scale2_correct, Hxr.
unfold toR.
rewrite scale2_correct, Hxr.
simpl.
apply Rmult_lt_0_compat.
exact Hx.
apply Rinv_0_lt_compat.
now apply (Z2R_lt 0 2).
Qed.

(* 0 <= input *)
Definition cos_fastP prec x :=
  snd (sin_cos_reduce prec x 20).

Definition cos_fast prec x :=
  match F.cmp x F.zero with
  | Xeq => I.fromZ 1
  | Xlt => cos_fastP prec (F.neg x)
  | Xgt => cos_fastP prec x
  | Xund => I.nai
  end.

Theorem cos_fast_correct :
  forall prec x,
  contains (I.convert (cos_fast prec x)) (Xcos (FtoX (F.toF x))).
intros prec x.
unfold cos_fast.
rewrite F.cmp_correct.
rewrite F.zero_correct.
case_eq (F.toF x) ; intros ; simpl.
exact I.
(* zero *)
unfold I.convert_bound.
rewrite F.fromZ_correct.
rewrite cos_0.
split ; apply Rle_refl.
unfold cos_fastP.
destruct b.
(* neg *)
change true with (negb false).
rewrite <- FtoR_neg.
rewrite cos_neg.
generalize (sin_cos_reduce_correct prec 20 (F.neg x)).
destruct (sin_cos_reduce prec (F.neg x) 20).
unfold toR.
rewrite F.neg_correct.
rewrite H.
intros H0.
exact (proj1 (H0 (refl_equal _) (FtoR_Rpos _ _ _))).
(* pos *)
generalize (sin_cos_reduce_correct prec 20 x).
destruct (sin_cos_reduce prec x 20).
unfold toR.
rewrite H.
intros H0.
exact (proj1 (H0 (refl_equal _) (FtoR_Rpos _ _ _))).
Qed.

(* 0 <= inputs *)
Fixpoint sin_fast0_aux prec thre powl powu sqrl sqru fact div (nb : nat) { struct nb } :=
  let npwu := F.mul rnd_UP prec powu sqru in
  let valu := F.div rnd_UP prec npwu div in
  match F.cmp valu thre, nb with
  | Xlt, _
  | _, O => I.bnd F.zero valu
  | _, S n =>
    let npwl := F.mul rnd_DN prec powl sqrl in
    let vall := F.div rnd_DN prec npwl div in
    let one := F.fromZ 1 in
    let nfact := F.add_exact fact (F.add_exact one one) in
    let ndiv := F.mul_exact div (F.mul_exact fact (F.add_exact fact one)) in
    I.sub prec (I.bnd vall valu)
      (cos_fast0_aux prec thre npwl npwu sqrl sqru nfact ndiv n)
  end.

(* -1/2 <= input <= 1/2 *)
Definition sin_fast0 prec x :=
  let x2l := F.mul rnd_DN prec x x in
  let x2u := F.mul rnd_UP prec x x in
  let c1 := F.fromZ 1 in
  let p := F.prec prec in
  let thre := F.scale c1 (F.ZtoS (Zneg p)) in
  let rem := sin_fast0_aux prec thre c1 c1 x2l x2u (F.fromZ 4) (F.fromZ 6) (nat_of_P p) in
  I.mul_mixed prec (I.sub prec (I.bnd c1 c1) rem) x.

Axiom sin_fast0_correct :
  forall prec x,
  FtoX (F.toF x) = Xreal (toR x) ->
  (Rabs (toR x) <= /2)%R ->
  contains (I.convert (sin_fast0 prec x)) (Xreal (sin (toR x))).

(* 0 <= input *)
Definition sin_fastP prec x :=
  let c1 := F.fromZ 1 in
  let sm1 := F.ZtoS (-1)%Z in
  let th := F.scale2 c1 sm1 in
  match le x th with
  | true => sin_fast0 prec x
  | _ =>
    match sin_cos_reduce prec x 20 with
    | (s, c) =>
      let v := I.sqrt prec (I.sub prec (I.bnd c1 c1) (I.sqr prec c)) in
      match s with
      | Lt => I.neg v
      | Gt => v
      | _ => I.bnd (F.neg c1) c1
      end
    end
  end.

Definition sin_fast prec x :=
  match F.cmp x F.zero with
  | Xeq => I.bnd F.zero F.zero
  | Xlt => I.neg (sin_fastP prec (F.neg x))
  | Xgt => sin_fastP prec x
  | Xund => I.nai
  end.

Theorem sin_fast_correct :
  forall prec x,
  contains (I.convert (sin_fast prec x)) (Xsin (FtoX (F.toF x))).
intros prec x.
unfold sin_fast.
rewrite F.cmp_correct.
rewrite F.zero_correct.
case_eq (F.toF x) ; intros ; simpl.
exact I.
(* zero *)
unfold I.convert_bound.
rewrite F.zero_correct.
simpl.
rewrite sin_0.
split ; apply Rle_refl.
destruct b.
(* neg *)
change true with (negb false).
rewrite <- FtoR_neg.
rewrite sin_neg.
change (Xreal (- sin (FtoR F.radix false p z))) with (Xneg (Xreal (sin (FtoR F.radix false p z)))).
apply I.neg_correct.
unfold sin_fastP.
destruct (le_spec (F.neg x) (F.scale2 (F.fromZ 1) (F.ZtoS (-1)))).
(* . small *)
replace (FtoR F.radix false p z) with (toR (F.neg x)).
apply sin_fast0_correct.
unfold toR.
rewrite F.neg_correct.
now rewrite H.
rewrite Rabs_right.
replace (/ 2)%R with (toR (F.scale2 (F.fromZ 1) (F.ZtoS (-1)))).
exact Hxy.
unfold toR.
rewrite F.scale2_correct, Fscale2_correct.
rewrite F.fromZ_correct.
simpl.
apply Rmult_1_l.
exact F.even_radix_correct.
apply refl_equal.
unfold toR.
rewrite F.neg_correct.
rewrite H.
simpl.
left.
apply FtoR_Rpos.
unfold toR.
rewrite F.neg_correct.
now rewrite H.
(* . big *)
generalize (sin_cos_reduce_correct prec 20 (F.neg x)).
destruct (sin_cos_reduce prec (F.neg x) 20).
unfold toR.
rewrite F.neg_correct.
rewrite H.
intros H0.
generalize (H0 (refl_equal _) (FtoR_Rpos _ _ _)).
clear H0.
case c ; intros (H0, H1).
simpl.
unfold I.convert_bound.
rewrite F.neg_correct, Fneg_correct.
rewrite F.fromZ_correct.
simpl.
apply SIN_bound.
rewrite <- (Ropp_involutive (sin (FtoR F.radix false p z))).
change (Xreal (- - sin (FtoR F.radix false p z))) with (Xneg (Xreal (- sin (FtoR F.radix false p z)))).
apply I.neg_correct.
rewrite <- Rabs_left1.
rewrite <- sqrt_Rsqr_abs.
replace (Xreal (sqrt (sin (FtoR F.radix false p z))²)) with (Xsqrt (Xreal (sin (FtoR F.radix false p z))²)).
apply I.sqrt_correct.
rewrite sin2.
change (Xreal (1 - (cos (FtoR F.radix false p z))²)) with (Xsub (Xreal 1) (Xsqr (Xreal (cos (FtoR F.radix false p z))))).
apply I.sub_correct.
simpl.
unfold I.convert_bound.
rewrite F.fromZ_correct.
split ; apply Rle_refl.
apply I.sqr_correct.
exact H0.
simpl.
destruct (is_negative_spec (sin (FtoR F.radix false p z))²).
elim (Rlt_not_le _ _ H2).
apply Rle_0_sqr.
apply refl_equal.
exact H1.
rewrite <- (Rabs_right (sin (FtoR F.radix false p z))).
rewrite <- sqrt_Rsqr_abs.
replace (Xreal (sqrt (sin (FtoR F.radix false p z))²)) with (Xsqrt (Xreal (sin (FtoR F.radix false p z))²)).
apply I.sqrt_correct.
rewrite sin2.
change (Xreal (1 - (cos (FtoR F.radix false p z))²)) with (Xsub (Xreal 1) (Xsqr (Xreal (cos (FtoR F.radix false p z))))).
apply I.sub_correct.
simpl.
unfold I.convert_bound.
rewrite F.fromZ_correct.
split ; apply Rle_refl.
apply I.sqr_correct.
exact H0.
simpl.
destruct (is_negative_spec (sin (FtoR F.radix false p z))²).
elim (Rlt_not_le _ _ H2).
apply Rle_0_sqr.
apply refl_equal.
apply Rle_ge.
exact H1.
(* pos *)
unfold sin_fastP.
destruct (le_spec x (F.scale2 (F.fromZ 1) (F.ZtoS (-1)))).
(* . small *)
replace (FtoR F.radix false p z) with (toR x).
apply sin_fast0_correct.
unfold toR.
now rewrite H.
rewrite Rabs_right.
replace (/ 2)%R with (toR (F.scale2 (F.fromZ 1) (F.ZtoS (-1)))).
exact Hxy.
unfold toR.
rewrite F.scale2_correct, Fscale2_correct.
rewrite F.fromZ_correct.
simpl.
apply Rmult_1_l.
exact F.even_radix_correct.
apply refl_equal.
unfold toR.
rewrite H.
simpl.
left.
apply FtoR_Rpos.
unfold toR.
now rewrite H.
(* . big *)
generalize (sin_cos_reduce_correct prec 20 x).
destruct (sin_cos_reduce prec x 20).
unfold toR.
rewrite H.
intros H0.
generalize (H0 (refl_equal _) (FtoR_Rpos _ _ _)).
clear H0.
case c ; intros (H0, H1).
simpl.
unfold I.convert_bound.
rewrite F.neg_correct, Fneg_correct.
rewrite F.fromZ_correct.
simpl.
apply SIN_bound.
rewrite <- (Ropp_involutive (sin (FtoR F.radix false p z))).
change (Xreal (- - sin (FtoR F.radix false p z))) with (Xneg (Xreal (- sin (FtoR F.radix false p z)))).
apply I.neg_correct.
rewrite <- Rabs_left1.
rewrite <- sqrt_Rsqr_abs.
replace (Xreal (sqrt (sin (FtoR F.radix false p z))²)) with (Xsqrt (Xreal (sin (FtoR F.radix false p z))²)).
apply I.sqrt_correct.
rewrite sin2.
change (Xreal (1 - (cos (FtoR F.radix false p z))²)) with (Xsub (Xreal 1) (Xsqr (Xreal (cos (FtoR F.radix false p z))))).
apply I.sub_correct.
simpl.
unfold I.convert_bound.
rewrite F.fromZ_correct.
split ; apply Rle_refl.
apply I.sqr_correct.
exact H0.
simpl.
destruct (is_negative_spec (sin (FtoR F.radix false p z))²).
elim (Rlt_not_le _ _ H2).
apply Rle_0_sqr.
apply refl_equal.
exact H1.
rewrite <- (Rabs_right (sin (FtoR F.radix false p z))).
rewrite <- sqrt_Rsqr_abs.
replace (Xreal (sqrt (sin (FtoR F.radix false p z))²)) with (Xsqrt (Xreal (sin (FtoR F.radix false p z))²)).
apply I.sqrt_correct.
rewrite sin2.
change (Xreal (1 - (cos (FtoR F.radix false p z))²)) with (Xsub (Xreal 1) (Xsqr (Xreal (cos (FtoR F.radix false p z))))).
apply I.sub_correct.
simpl.
unfold I.convert_bound.
rewrite F.fromZ_correct.
split ; apply Rle_refl.
apply I.sqr_correct.
exact H0.
simpl.
destruct (is_negative_spec (sin (FtoR F.radix false p z))²).
elim (Rlt_not_le _ _ H2).
apply Rle_0_sqr.
apply refl_equal.
apply Rle_ge.
exact H1.
Qed.

(* 0 <= input *)
Definition tan_fastP prec x :=
  let c1 := F.fromZ 1 in
  let i1 := I.bnd c1 c1 in
  let sm1 := F.ZtoS (-1)%Z in
  let th := F.scale2 c1 sm1 in
  match le x th with
  | true =>
    let s := sin_fast0 prec x in
    I.div prec s (I.sqrt prec (I.sub prec i1 (I.sqr prec s)))
  | _ =>
    match sin_cos_reduce prec x 20 with
    | (s, c) =>
      let v := I.sqrt prec (I.sub prec (I.div prec i1 (I.sqr prec c)) i1) in
      match s, I.sign_large c with
      | Lt, Xgt => I.neg v
      | Gt, Xlt => I.neg v
      | Lt, Xlt => v
      | Gt, Xgt => v
      | _, _ => I.nai
      end
    end
  end.

Definition tan_fast prec x :=
  match F.cmp x F.zero with
  | Xeq => I.bnd F.zero F.zero
  | Xlt => I.neg (tan_fastP prec (F.neg x))
  | Xgt => tan_fastP prec x
  | Xund => I.nai
  end.

Definition semi_extension f fi :=
  forall x, interval.contains (I.convert (fi x)) (f (FtoX (F.toF x))).

Axiom pi4_correct : forall prec, interval.contains (I.convert (pi4 prec)) (Xreal (PI/4)).
Definition cos_correct : forall prec, semi_extension Xcos (cos_fast prec) := cos_fast_correct.
Definition sin_correct : forall prec, semi_extension Xsin (sin_fast prec) := sin_fast_correct.
Axiom tan_correct : forall prec, semi_extension Xtan (tan_fast prec).
Axiom atan_correct : forall prec, semi_extension Xatan (atan_fast prec).

End TranscendentalFloatFast.

(*
Require Import specific_ops.
Require Import stdz_carrier.
Module F := SpecificFloat StdZRadix2.
Module A := TranscendentalFloatFast F.
Time Eval vm_compute in (A.atan_fast 50%Z (Float 201%Z (-8)%Z)).
Time Eval vm_compute in (A.cos_fast 50%Z (Float 201%Z (-8)%Z)).
Time Eval vm_compute in (A.tan_fast 50%Z (Float 3619%Z (-8)%Z)).
Time Eval vm_compute in (A.sin_fast 50%Z (Float 201%Z (-8)%Z)).
*)

(*
Module Transcendental (F : FloatOps).

Definition try_round mode prec x e :=
  let l := F.sub mode prec x e in
  let u := F.add mode prec x e in
  match F.cmp l u with
  | Xeq => Some l
  | _ => None
  end.

Lemma try_round_correct :
  forall mode prec x e r,
  Xcmp (Xabs (Xsub (FtoX (F.toF x)) r)) (FtoX (F.toF e)) = Xlt ->
  match try_round mode prec x e with
  | Some f => FtoX (F.toF f) = FtoX (round F.radix mode (F.prec prec) r)
  | None => True
  end.
intros mode prec x e r H.
unfold try_round.
case_eq (F.cmp (F.sub mode prec x e) (F.add mode prec x e)) ; trivial.
rewrite F.cmp_correct.
rewrite Fcmp_correct.
rewrite F.sub_correct.
rewrite Fsub_correct.
rewrite F.add_correct.
rewrite Fadd_correct.
generalize H. clear H.
case r ; case (FtoX (F.toF x)) ; case (FtoX (F.toF e)) ;
  try (intros ; discriminate).
clear.
intros e x r.
unfold Xsub, Xadd, Xabs.
repeat rewrite round_correct_real.
unfold Xcmp.
generalize (Rcompare_correct (Rabs (x - r)) e).
case (Rcompare (Rabs (x - r)) e) ; intros He H ;
  try discriminate H ; clear H.
set (l := round_real F.radix mode (F.prec prec) (x - e)).
set (u := round_real F.radix mode (F.prec prec) (x + e)).
generalize (Rcompare_correct l u).
case (Rcompare l u) ; intros Hlu H ;
  try discriminate H ; clear H.
apply f_equal.
set (s := round_real F.radix mode (F.prec prec) r).
destruct (Rtotal_order l s) as [H|[H|H]].
2: trivial.
(* l < round r *)
assert (Xcmp (FtoX (round F.radix mode (F.prec prec) (Xreal (x + e))))
             (FtoX (round F.radix mode (F.prec prec) (Xreal r))) = Xlt).
repeat rewrite round_correct_real.
simpl.
fold u s.
rewrite <- Hlu.
rewrite Rcompare_correct_lt with (1 := H).
apply refl_equal.
generalize (round_monotone F.radix mode (F.prec prec) (Xreal (x + e)) (Xreal r)).
rewrite H0. clear H H0.
simpl.
rewrite Rcompare_correct_gt.
intro. discriminate.
destruct (Rabs_def2 _ _ He) as (_, H).
apply Rplus_lt_reg_r with (-e - r)%R.
replace (-e - r + r)%R with (-e)%R. 2: ring.
replace (-e - r + (x + e))%R with (x - r)%R. 2: ring.
exact H.
(* l > round r *)
assert (Xcmp (FtoX (round F.radix mode (F.prec prec) (Xreal (x - e))))
             (FtoX (round F.radix mode (F.prec prec) (Xreal r))) = Xgt).
repeat rewrite round_correct_real.
simpl.
fold l s.
rewrite Rcompare_correct_gt with (1 := H).
apply refl_equal.
generalize (round_monotone F.radix mode (F.prec prec) (Xreal (x - e)) (Xreal r)).
rewrite H0. clear H H0.
simpl.
rewrite Rcompare_correct_lt.
intro. discriminate.
destruct (Rabs_def2 _ _ He) as (H, _).
apply Rplus_lt_reg_r with (e - r)%R.
replace (e - r + (x - e))%R with (x - r)%R. 2: ring.
replace (e - r + r)%R with e. 2: ring.
exact H.
Qed.

End Transcendental.
*)