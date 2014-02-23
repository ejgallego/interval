Require Import Reals.
Require Import Interval_missing.
Require Import Interval_xreal.
Require Import Interval_definitions.
Require Import Interval_float_sig.
Require Import Interval_generic.
Require Import Interval_generic_proof.
Require Import Interval_interval.
Require Import Interval_interval_float.

Module TranscendentalFloatFast (F : FloatOps with Definition even_radix := true).

Module I := FloatInterval F.

CoInductive hidden_constant : Type :=
  | HConst : I.type -> hidden_constant.

CoInductive constants : Type :=
  | Consts: hidden_constant -> constants -> constants.

Fixpoint constant_getter_aux n cst :=
  match n, cst with
  | O, Consts (HConst xi) _ => xi
  | S p, Consts _ c => constant_getter_aux p c
  end.

Definition constant_getter cst prec :=
  let nb := Zabs_nat (Zpred (fst (Zdiv.Zdiv_eucl_POS (F.prec prec + 30)%positive 31%Z))) in
  constant_getter_aux nb cst.

CoFixpoint hidden_constant_generator gen n :=
  HConst (gen (F.PtoP (n * 31)%positive)).

CoFixpoint constant_generator_aux gen n :=
  Consts (hidden_constant_generator gen n) (constant_generator_aux gen (Psucc n)).

Definition constant_generator gen :=
  constant_generator_aux gen 1.

Definition Z2Zp x :=
  match x with
  | Zpos p => x
  | _ => Z0
  end.

Definition Z2nat x :=
  match x with
  | Zpos p => nat_of_P p
  | _ => O
  end.

Definition Z2P x :=
  match x with
  | Zpos p => p
  | _ => xH
  end.

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
    let prec := F.incr_prec prec 2 in
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
  | _ => atan_fast0 (F.incr_prec prec 1) x
  end.

Definition atan_fast prec x :=
  match F.cmp x F.zero with
  | Xeq => I.bnd F.zero F.zero
  | Xlt => I.neg (atan_fastP prec (F.neg x))
  | Xgt => atan_fastP prec x
  | Xund => I.nai
  end.

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
Proof.
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

(*
(* 0 <= inputs *)
Fixpoint umc_fast0_aux prec thre powl powu sqrl sqru fact div (nb : nat) { struct nb } :=
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
      (umc_fast0_aux prec thre npwl npwu sqrl sqru nfact ndiv n)
  end.

Definition umc_fast0 prec x :=
  let x2l := F.mul rnd_DN prec x x in
  let x2u := F.mul rnd_UP prec x x in
  let c1 := F.fromZ 1 in
  let p := F.prec prec in
  let thre := F.scale c1 (F.ZtoS (Zneg p)) in
  I.scale2
   (I.mul prec
     (I.bnd x2l x2u)
     (I.sub prec
       (I.bnd c1 c1)
       (umc_fast0_aux prec thre c1 c1 x2l x2u (F.fromZ 5) (F.fromZ 12) (nat_of_P p))))
   (F.ZtoS (-1)%Z).

Definition umc_reduce prec x :=
  let c1 := F.fromZ 1 in
  let th := F.scale2 c1 (F.ZtoS (-4)%Z) in
  (*let prec := F.incr_prec prec 1 in*)
  let c2 := F.fromZ 2 in
  let i2 := I.bnd c2 c2 in
  let s1 := F.ZtoS 1 in
  let sm1 := F.ZtoS (-1)%Z in
  let fix reduce x (nb : nat) {struct nb} :=
    match le x th, nb with
    | true, _ => umc_fast0 prec x
    | _, O => umc_fast0 prec x
    | _, S n =>
      (*match reduce (F.scale2 x sm1) n with
      | Ibnd yl yu => I.scale2 (Ibnd (F.mul rnd_DN prec yl (F.sub rnd_DN prec c2 yl)) (F.mul rnd_UP prec yu (F.sub rnd_UP prec c2 yu))) s1
      | Inan => Inan
      end*)
      let u := reduce (F.scale2 x sm1) n in
      I.scale2 (I.mul prec u (I.sub prec i2 u)) s1
    end in
  reduce x 10.

Definition cos_fast0 prec x :=
  let c1 := F.fromZ 1 in
  I.sub prec (I.bnd c1 c1) (umc_reduce prec x).
*)

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
  FtoX (F.toF (F.scale2 x (F.ZtoS d))) = Xmul (FtoX (F.toF x)) (Xreal (bpow radix2 d)).
Proof.
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
Proof.
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
  let c1 := F.fromZ 1 in
  let sm1 := F.ZtoS (-1)%Z in
  let th := F.scale2 c1 sm1 in
  match le x th with
  | true => cos_fast0 prec x
  | _ =>
    let m := F.StoZ (F.mag x) in
    let prec := F.incr_prec prec (Z2P (m + 6)) in
    snd (sin_cos_reduce prec x (S (Z2nat m)))
  end.

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
Proof.
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
assert (H12: (/2)%R = toR (F.scale2 (F.fromZ 1) (F.ZtoS (-1)))).
unfold toR.
rewrite F.scale2_correct, Fscale2_correct.
rewrite F.fromZ_correct.
apply sym_eq.
simpl.
apply Rmult_1_l.
apply F.even_radix_correct.
apply refl_equal.
destruct b.
(* neg *)
change true with (negb false).
rewrite <- FtoR_neg.
rewrite cos_neg.
destruct (le_spec (F.neg x) (F.scale2 (F.fromZ 1) (F.ZtoS (-1)))).
(* . no reduction *)
replace (FtoR F.radix false p z) with (toR (F.neg x)).
apply cos_fast0_correct.
unfold toR.
rewrite F.neg_correct.
now rewrite H.
rewrite Rabs_right.
now rewrite H12.
unfold toR.
rewrite F.neg_correct.
rewrite H.
simpl.
apply Rgt_ge.
apply FtoR_Rpos.
unfold toR.
rewrite F.neg_correct.
now rewrite H.
(* . reduction *)
generalize (F.incr_prec prec (Z2P (F.StoZ (F.mag (F.neg x)) + 6))).
clear prec. intros prec.
generalize (S (Z2nat (F.StoZ (F.mag (F.neg x))))).
intros nb.
generalize (sin_cos_reduce_correct prec nb (F.neg x)).
destruct (sin_cos_reduce prec (F.neg x) nb).
unfold toR.
rewrite F.neg_correct.
rewrite H.
intros H0.
exact (proj1 (H0 (refl_equal _) (FtoR_Rpos _ _ _))).
(* pos *)
destruct (le_spec x (F.scale2 (F.fromZ 1) (F.ZtoS (-1)))).
(* . no reduction *)
replace (FtoR F.radix false p z) with (toR x).
apply cos_fast0_correct.
unfold toR.
now rewrite H.
rewrite Rabs_right.
now rewrite H12.
unfold toR.
rewrite H.
simpl.
apply Rgt_ge.
apply FtoR_Rpos.
unfold toR.
now rewrite H.
(* . reduction *)
generalize (F.incr_prec prec (Z2P (F.StoZ (F.mag x) + 6))).
clear prec. intros prec.
generalize (S (Z2nat (F.StoZ (F.mag x)))).
intros nb.
generalize (sin_cos_reduce_correct prec nb x).
destruct (sin_cos_reduce prec x).
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
  | true => sin_fast0 (F.incr_prec prec 1) x
  | _ =>
    let m := F.StoZ (F.mag x) in
    let prec := F.incr_prec prec (Z2P (m + 6)) in
    match sin_cos_reduce prec x (S (Z2nat m)) with
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
Proof.
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
generalize (F.incr_prec prec (Z2P (F.StoZ (F.mag (F.neg x)) + 6))).
clear prec. intro prec.
set (nb := S (Z2nat (F.StoZ (F.mag (F.neg x))))).
generalize (sin_cos_reduce_correct prec nb (F.neg x)).
destruct (sin_cos_reduce prec (F.neg x) nb).
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
generalize (F.incr_prec prec (Z2P (F.StoZ (F.mag x) + 6))).
clear prec. intro prec.
set (nb := S (Z2nat (F.StoZ (F.mag x)))).
generalize (sin_cos_reduce_correct prec nb x).
destruct (sin_cos_reduce prec x).
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
    let prec := F.incr_prec prec 2 in
    let s := sin_fast0 prec x in
    I.div prec s (I.sqrt prec (I.sub prec i1 (I.sqr prec s)))
  | _ =>
    let m := F.StoZ (F.mag x) in
    let prec := F.incr_prec prec (Z2P (m + 7)) in
    match sin_cos_reduce prec x (S (Z2nat m)) with
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
  forall x, contains (I.convert (fi x)) (f (FtoX (F.toF x))).

Axiom pi4_correct : forall prec, contains (I.convert (pi4 prec)) (Xreal (PI/4)).
Definition cos_correct : forall prec, semi_extension Xcos (cos_fast prec) := cos_fast_correct.
Definition sin_correct : forall prec, semi_extension Xsin (sin_fast prec) := sin_fast_correct.
Axiom tan_correct : forall prec, semi_extension Xtan (tan_fast prec).
Axiom atan_correct : forall prec, semi_extension Xatan (atan_fast prec).

(* 0 <= inputs *)
Fixpoint expn_fast0_aux prec thre powl powu x fact div (nb : nat) { struct nb } :=
  let npwu := F.mul rnd_UP prec powu x in
  let valu := F.div rnd_UP prec npwu div in
  match F.cmp valu thre, nb with
  | Xlt, _
  | _, O => I.bnd F.zero valu
  | _, S n =>
    let npwl := F.mul rnd_DN prec powl x in
    let vall := F.div rnd_DN prec npwl div in
    let nfact := F.add_exact fact (F.fromZ 1) in
    let ndiv := F.mul_exact div fact in
    I.sub prec (I.bnd vall valu)
      (expn_fast0_aux prec thre npwl npwu x nfact ndiv n)
  end.

(* 0 <= input <= 1/2 *)
Definition expn_fast0 prec x :=
  let c1 := F.fromZ 1 in
  let p := F.prec prec in
  let thre := F.scale c1 (F.ZtoS (Zneg p)) in
  let rem := expn_fast0_aux prec thre x x x (F.fromZ 3) (F.fromZ 2) (nat_of_P p) in
  I.sub prec (I.bnd c1 c1) (I.sub prec (I.bnd x x) rem).

(* 0 <= input *)
Definition expn_reduce prec x :=
  let c1 := F.fromZ 1 in
  let th := F.scale2 c1 (F.ZtoS (-8)%Z) in
  match le x th with
  | true => expn_fast0 (F.incr_prec prec 1) x
  | false =>
    let m := F.StoZ (F.mag x) in
    let prec := F.incr_prec prec (Z2P (9 + m)) in
    let sm1 := F.ZtoS (-1)%Z in
    let fix reduce x (nb : nat) {struct nb} :=
      match le x th, nb with
      | true, _ => expn_fast0 prec x
      | _, O => I.bnd F.zero c1
      | _, S n => I.sqr prec (reduce (F.scale2 x sm1) n)
      end in
    reduce x (8 + Z2nat m)
  end.

Definition exp_fast prec x :=
  match F.cmp x F.zero with
  | Xeq => let c1 := F.fromZ 1 in I.bnd c1 c1
  | Xlt => expn_reduce prec (F.neg x)
  | Xgt =>
    let prec := F.incr_prec prec 1 in
    match I.inv prec (expn_reduce prec x) with
    | Ibnd _ _ as b => b
    | Inai => I.bnd (F.fromZ 1) F.nan
    end
  | Xund => I.nai
  end.

Ltac bound_tac :=
  unfold xround ;
  match goal with
  | |- (round ?r rnd_DN ?p ?v <= ?w)%R =>
    apply Rle_trans with (1 := proj1 (proj2 (Fcore_generic_fmt.round_DN_pt F.radix (Fcore_FLX.FLX_exp (Zpos p)) v)))
  | |- (?w <= round ?r rnd_UP ?p ?v)%R =>
    apply Rle_trans with (2 := proj1 (proj2 (Fcore_generic_fmt.round_UP_pt F.radix (Fcore_FLX.FLX_exp (Zpos p)) v)))
  end.

Lemma expn_fast0_correct :
  forall prec x,
  FtoX (F.toF x) = Xreal (toR x) ->
  (0 <= toR x <= /2)%R ->
  contains (I.convert (expn_fast0 prec x)) (Xreal (exp (- toR x))).
Proof.
intros prec x Rx Bx.
unfold expn_fast0.
replace (exp (-toR x)) with (1 - (toR x - (- (1 - toR x) + exp (-toR x))))%R by ring.
apply (I.sub_correct _ _ _ (Xreal _) (Xreal _)).
rewrite I.bnd_correct.
unfold I.convert_bound.
rewrite F.fromZ_correct.
split ; apply Rle_refl.
apply (I.sub_correct _ _ _ (Xreal _) (Xreal _)).
rewrite I.bnd_correct.
unfold I.convert_bound.
rewrite Rx.
split ; apply Rle_refl.
assert (Hexit : forall k powxu,
    (toR x ^ (k + 1) <= toR powxu)%R ->
    contains (I.convert (I.bnd F.zero (F.div rnd_UP prec (F.mul rnd_UP prec powxu x) (F.fromZ (Z.of_nat (fact (k + 2)))))))
      (Xreal ((-1) ^ k * (exp (- toR x) + - E1 (- toR x) (k + 1))))).
  intros k powxu Hpu.
  rewrite I.bnd_correct.
  unfold I.convert_bound.
  rewrite F.zero_correct.
  rewrite F.div_correct, Fdiv_correct.
  rewrite F.mul_correct, Fmul_correct.
  rewrite F.fromZ_correct.
  rewrite Rx.
  simpl.
  split.
  (* apply alternated *)
  admit.
  case_eq (FtoX (F.toF powxu)).
  easy.
  intros powxu' Hpu'.
  simpl.
  case is_zero_spec.
  easy.
  intros H1.
  simpl.
  bound_tac.
  apply Rle_trans with ((toR x ^ (k + 2)) / Z2R (Z.of_nat (fact (k + 2))))%R.
  (* apply alternated *)
  admit.
  apply Rmult_le_compat_r.
  apply Rlt_le, Rinv_0_lt_compat.
  apply (Z2R_lt 0), (inj_lt 0).
  apply lt_O_fact.
  bound_tac.
  rewrite <- plus_n_Sm.
  simpl.
  rewrite Rmult_comm.
  apply Rmult_le_compat_r.
  apply Bx.
  unfold toR at 2 in Hpu.
  now rewrite Hpu' in Hpu.
generalize (F.scale (F.fromZ 1) (F.ZtoS (Z.neg (F.prec prec)))) (Pos.to_nat (F.prec prec)).
intros thre n.
replace (1 - toR x)%R with (E1 (- toR x) (0 + 1)) by (unfold E1 ; simpl ; field).
generalize (eq_refl x).
generalize x at 1 3.
intros powxl Hpl.
apply (f_equal toR) in Hpl.
apply Req_le in Hpl.
generalize (eq_refl x).
generalize x at 2 3.
intros powxu Hpu.
apply (f_equal toR) in Hpu.
apply Req_le in Hpu.
revert Hpl Hpu.
rewrite <- (pow_1 (toR x)) at 1 2.
rewrite Rplus_comm.
change 1 with (0 + 1) at 1 2.
change 3%Z with (Z_of_nat (0 + 3)).
change 2%Z with (Z_of_nat (fact (0 + 2))).
rewrite <- (Rmult_1_l (_ + _)).
change R1 with ((-1)^0)%R.
rewrite <- (minus_diag n) at 1 3 5 7 9 10.
generalize (le_refl n).
generalize n at 1 4 6 8 10 11 13 15.
intros m.
revert powxl powxu.
induction m as [|m IHm] ; intros powxl powxu Hm Hpl Hpu.
- simpl.
  cut (contains (I.convert (I.bnd F.zero (F.div rnd_UP prec (F.mul rnd_UP prec powxu x)
    (F.fromZ (Z.of_nat (fact (n - 0 + 2))))))) (Xreal ((-1) ^ (n - 0) * (exp (- toR x) + - E1 (- toR x) (n - 0 + 1))))).
  now destruct F.cmp.
  now apply Hexit.
- simpl.
  specialize (IHm (F.mul rnd_DN prec powxl x) (F.mul rnd_UP prec powxu x)).
  assert (H: forall p, n - S m + S p = n - m + p).
    intros p.
    clear -Hm ; omega.
  rewrite 3!H.
  replace (F.add_exact (F.fromZ (Z.of_nat (n - m + 2))) (F.fromZ 1)) with (F.fromZ (Z.of_nat (n - m + 3))).
  replace (F.mul_exact (F.fromZ (Z.of_nat (fact (n - m + 1)))) (F.fromZ (Z.of_nat (n - m + 2)))) with (F.fromZ (Z.of_nat (fact (n - m + 2)))).
  destruct ((expn_fast0_aux prec thre (F.mul rnd_DN prec powxl x)
              (F.mul rnd_UP prec powxu x) x (F.fromZ (Z.of_nat (n - m + 3)))
              (F.fromZ (Z.of_nat (fact (n - m + 2)))) m)).
  case F.cmp ; try easy.
  rewrite <- 2!H.
  now apply Hexit.
  assert (Hind: contains (I.convert (Ibnd
        (F.sub rnd_DN prec (F.div rnd_DN prec (F.mul rnd_DN prec powxl x) (F.fromZ (Z.of_nat (fact (n - m + 1))))) u)
        (F.sub rnd_UP prec (F.div rnd_UP prec (F.mul rnd_UP prec powxu x) (F.fromZ (Z.of_nat (fact (n - m + 1))))) l)))
      (Xreal ((-1) ^ (n - S m) * (exp (- toR x) + - E1 (- toR x) (n - m + 0))))).
    admit.
  case F.cmp ; try easy.
  rewrite <- 2!H.
  now apply Hexit.
  admit.
  admit.
Qed.

Lemma expn_reduce_correct :
  forall prec x,
  FtoX (F.toF x) = Xreal (toR x) ->
  (0 < toR x)%R ->
  contains (I.convert (expn_reduce prec x)) (Xreal (exp (- toR x))).
Proof.
assert (forall prec x,
  FtoX (F.toF x) = Xreal (toR x) ->
  (0 < toR x <= toR (F.scale2 (F.fromZ 1) (F.ZtoS (-8))))%R ->
  contains (I.convert (expn_fast0 prec x)) (Xreal (exp (- toR x)))).
intros prec x Hx1 (Hx2, Hx3).
apply expn_fast0_correct.
exact Hx1.
split.
now apply Rlt_le.
apply Rle_trans with (1 := Hx3).
unfold toR.
rewrite F.scale2_correct ; trivial.
rewrite Fscale2_correct ; try apply F.even_radix_correct.
rewrite F.fromZ_correct.
simpl.
rewrite Rmult_1_l.
apply Rle_Rinv_pos.
now apply (Z2R_lt 0 2).
now apply (Z2R_le 2 256).
(* . *)
intros prec x Hx H0.
unfold expn_reduce.
destruct (le_spec x (F.scale2 (F.fromZ 1) (F.ZtoS (-8)))).
(* . no reduction *)
clear Hx0.
apply H ; now try split.
(* . reduction *)
generalize (F.incr_prec prec (Z2P (9 + F.StoZ (F.mag x)))).
clear prec. intro prec.
generalize (8 + Z2nat (F.StoZ (F.mag x))).
intro nb.
revert x Hx H0.
induction nb ; intros ; simpl.
(* nb = 0 *)
destruct (le_spec x (F.scale2 (F.fromZ 1) (F.ZtoS (-8)))).
apply H ; now try split.
simpl.
unfold I.convert_bound.
rewrite F.zero_correct, F.fromZ_correct.
simpl.
split.
apply Rlt_le.
apply exp_pos.
rewrite <- exp_0.
apply Rlt_le.
apply exp_increasing.
rewrite <- Ropp_0.
now apply Ropp_lt_contravar.
(* nb > 0 *)
destruct (le_spec x (F.scale2 (F.fromZ 1) (F.ZtoS (-8)))).
apply H ; now try split.
assert (toR (F.scale2 x (F.ZtoS (-1))) = toR x * /2)%R.
unfold toR.
rewrite F.scale2_correct, Fscale2_correct.
now rewrite Hx.
exact F.even_radix_correct.
apply refl_equal.
replace (toR x) with (toR (F.scale2 x (F.ZtoS (-1))) + toR (F.scale2 x (F.ZtoS (-1))))%R.
rewrite Ropp_plus_distr.
rewrite exp_plus.
change (Xreal (exp (- toR (F.scale2 x (F.ZtoS (-1)))) * exp (- toR (F.scale2 x (F.ZtoS (-1))))))
  with (Xsqr (Xreal (exp (- toR (F.scale2 x (F.ZtoS (-1))))))).
apply I.sqr_correct.
apply IHnb.
unfold toR.
rewrite F.scale2_correct , Fscale2_correct.
now rewrite Hx.
exact F.even_radix_correct.
apply refl_equal.
rewrite H1.
apply Rmult_lt_0_compat.
exact H0.
auto with real.
rewrite H1.
clear.
field.
Qed.

Theorem exp_fast_correct :
  forall prec x,
  contains (I.convert (exp_fast prec x)) (Xexp (FtoX (F.toF x))).
Proof.
intros prec x.
unfold exp_fast.
rewrite F.cmp_correct.
rewrite F.zero_correct.
case_eq (F.toF x) ; intros ; unfold Fcmp.
exact I.
(* zero *)
simpl.
unfold I.convert_bound.
rewrite F.fromZ_correct.
rewrite exp_0.
split ; apply Rle_refl.
replace (Xexp  (FtoX (Float F.radix b p z)))
  with (Xreal (exp (- toR (F.neg x)))).
destruct b.
(* neg *)
apply expn_reduce_correct.
unfold toR.
rewrite F.neg_correct, Fneg_correct.
now rewrite H.
unfold toR.
rewrite F.neg_correct, Fneg_correct.
rewrite H.
simpl.
rewrite FtoR_neg.
apply FtoR_Rpos.
(* pos *)
generalize (F.incr_prec prec 1).
clear prec. intro prec.
case_eq (I.inv prec (expn_reduce prec x)) ; intros.
(* pos too big *)
split ; unfold I.convert_bound.
rewrite F.fromZ_correct.
unfold toR.
rewrite F.neg_correct, Fneg_correct.
rewrite H.
simpl.
rewrite Ropp_involutive.
rewrite <- exp_0.
apply Rlt_le.
apply exp_increasing.
apply FtoR_Rpos.
now rewrite F.nan_correct.
(* pos fine *)
rewrite <- H0.
rewrite exp_Ropp.
replace (Xreal (/ exp (toR (F.neg x)))) with (Xinv (Xreal (exp (toR (F.neg x))))).
apply I.inv_correct.
replace (toR (F.neg x)) with (- toR x)%R.
apply expn_reduce_correct.
unfold toR.
now rewrite H.
unfold toR.
rewrite H.
simpl.
apply FtoR_Rpos.
unfold toR.
rewrite F.neg_correct, Fneg_correct.
now rewrite H.
unfold toR.
rewrite F.neg_correct, Fneg_correct.
rewrite H.
simpl.
destruct (is_zero_spec (exp (- FtoR F.radix false p z))).
elim Rgt_not_eq with (2 := H1).
apply exp_pos.
apply refl_equal.
(* . *)
unfold toR.
rewrite F.neg_correct, Fneg_correct.
rewrite H.
simpl.
now rewrite Ropp_involutive.
Qed.

End TranscendentalFloatFast.

(*
Require Import Interval_specific_ops.
Require Import Interval_stdz_carrier.
Module F := SpecificFloat StdZRadix2.
Module A := TranscendentalFloatFast F.
Time Eval vm_compute in (A.exp_fast 50%Z (Float 201%Z (-8)%Z)).
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