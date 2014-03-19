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

Definition c1 := F.fromZ 1.
Definition c2 := F.fromZ 2.
Definition c3 := F.fromZ 3.
Definition c4 := F.fromZ 4.
Definition c6 := F.fromZ 6.
Definition s1 := F.ZtoS 1.
Definition sm1 := F.ZtoS (-1).
Definition sm8 := F.ZtoS (-8).

Ltac bound_tac :=
  unfold xround ;
  match goal with
  | |- (round ?r rnd_DN ?p ?v <= ?w)%R =>
    apply Rle_trans with (1 := proj1 (proj2 (Fcore_generic_fmt.round_DN_pt F.radix (Fcore_FLX.FLX_exp (Zpos p)) v)))
  | |- (?w <= round ?r rnd_UP ?p ?v)%R =>
    apply Rle_trans with (2 := proj1 (proj2 (Fcore_generic_fmt.round_UP_pt F.radix (Fcore_FLX.FLX_exp (Zpos p)) v)))
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
  let p := F.prec prec in
  let thre := F.scale c1 (F.ZtoS (Zneg p)) in
  let rem := atan_fast0_aux prec thre c1 c1 x2l x2u c2 c3 (nat_of_P p) in
  I.mul_mixed prec (I.sub prec (I.bnd c1 c1) rem) x.

(* -1/2 <= input <= 1/2 *)
Definition atan_fast0i prec xi :=
  let x2 := I.sqr prec xi in
  let p := F.prec prec in
  let thre := F.scale c1 (F.ZtoS (Zneg p)) in
  let rem := atan_fast0_aux prec thre c1 c1 (I.lower x2) (I.upper x2) c2 c3 (nat_of_P p) in
  I.mul prec (I.sub prec (I.bnd c1 c1) rem) xi.

Definition pi4_gen prec :=
  let s2 := F.ZtoS 2 in
  I.sub prec
   (I.scale2 (atan_fast0i prec (I.inv prec (I.fromZ 5))) s2)
   (atan_fast0i prec (I.inv prec (I.fromZ 239))).

Definition pi4_seq := constant_generator pi4_gen.
Definition pi4 := constant_getter pi4_seq.

Definition atan_fastP prec x :=
  match F.cmp x (F.scale2 c1 sm1) with
  | Xgt =>
    let prec := F.incr_prec prec 2 in
    let pi4i := pi4 prec in
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
    let nfact := F.add_exact fact c2 in
    let ndiv := F.mul_exact div (F.mul_exact fact (F.add_exact fact c1)) in
    I.sub prec (I.bnd vall valu)
      (cos_fast0_aux prec thre npwl npwu sqrl sqru nfact ndiv n)
  end.

(* -1/2 <= input <= 1/2 *)
Definition cos_fast0 prec x :=
  let x2l := F.mul rnd_DN prec x x in
  let x2u := F.mul rnd_UP prec x x in
  let p := F.prec prec in
  let thre := F.scale c1 (F.ZtoS (Zneg p)) in
  let rem := cos_fast0_aux prec thre c1 c1 x2l x2u c3 c2 (nat_of_P p) in
  I.sub prec (I.bnd c1 c1) rem.

(* 0 <= input *)
Definition sin_cos_reduce prec x :=
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
        I.sub prec (I.scale2 (I.sqr prec c) s1) i1)
      end
    end in
  reduce x.

Lemma cos_fast0_correct :
  forall prec x,
  FtoX (F.toF x) = Xreal (toR x) ->
  (Rabs (toR x) <= /2)%R ->
  contains (I.convert (cos_fast0 prec x)) (Xreal (cos (toR x))).
Proof.
intros prec x Rx Bx.
unfold cos_fast0.
replace (cos (toR x)) with (1 - (1 - cos (toR x)))%R by ring.
apply (I.sub_correct _ _ _ (Xreal _) (Xreal _)).
rewrite I.bnd_correct.
unfold I.convert_bound, c1.
rewrite F.fromZ_correct.
split ; apply Rle_refl.
set (sqrl := F.mul rnd_DN prec x x).
set (sqru := F.mul rnd_UP prec x x).
assert (Hexit : forall k powu ft,
    (toR x ^ (2 * k) <= toR powu)%R ->
    FtoX (F.toF ft) = FtoX (F.toF (F.fromZ (Z.of_nat (fact (2 * (k + 1)))))) ->
    contains (I.convert (I.bnd F.zero (F.div rnd_UP prec (F.mul rnd_UP prec powu sqru) ft)))
      (Xreal ((-1) ^ (k + 1) * (cos (toR x) - A1 (toR x) k)))).
  intros k powu ft Hpu Hft.
  rewrite I.bnd_correct.
  unfold I.convert_bound.
  rewrite F.zero_correct.
  rewrite F.div_correct, Fdiv_correct.
  unfold sqru.
  do 2 rewrite F.mul_correct, Fmul_correct.
  rewrite Hft.
  rewrite F.fromZ_correct.
  rewrite Rx.
  simpl.
  assert (A: (0 <= (-1) ^ (k + 1) * (cos (toR x) - A1 (toR x) k) <= toR x ^ (2 * (k + 1)) / Z2R (Z.of_nat (fact (2 * (k + 1)))))%R).
    rewrite Z2R_IZR, <- INR_IZR_INZ.
    replace (A1 (toR x) k) with (sum_f_R0 (tg_alt (fun n => / INR (fact (2 * n)) * toR x ^ (2 * n))%R) k).
    unfold Rdiv.
    rewrite (Rmult_comm (toR x ^ _)).
    replace (k + 1) with (S k) by ring.
    apply alternated_series_ineq'.
    apply Un_decreasing_cos.
    apply Rle_trans with (1 := Bx).
    rewrite <- (Rinv_1) at 3.
    apply Rinv_le.
    apply Rlt_0_1.
    now apply (Z2R_le 1 2).
    apply (Un_cv_subseq (fun n => (/ INR (fact n) * toR x ^ n)%R)).
    clear ; intros n ; omega.
    eapply Un_cv_ext.
    intros n.
    apply Rmult_comm.
    apply cv_speed_pow_fact.
    generalize (A1_cvg (toR x)).
    apply Un_cv_ext.
    intros n.
    unfold A1, tg_alt.
    apply sum_eq.
    intros i _.
    apply Rmult_assoc.
    unfold A1, tg_alt.
    apply sum_eq.
    intros i _.
    apply sym_eq, Rmult_assoc.
  split.
    apply A.
  case_eq (FtoX (F.toF powu)).
  easy.
  intros powu' Hpu'.
  simpl.
  case is_zero_spec.
  easy.
  intros H1.
  simpl.
  bound_tac.
  apply Rle_trans with (1 := proj2 A).
  apply Rmult_le_compat_r.
  apply Rlt_le, Rinv_0_lt_compat.
  apply (Z2R_lt 0), (inj_lt 0).
  apply lt_O_fact.
  bound_tac.
  replace (2 * (k + 1)) with (2 * k + 2) by ring.
  rewrite pow_add.
  simpl (toR x ^ 2)%R.
  rewrite Rmult_1_r.
  apply Rmult_le_compat.
  rewrite pow_sqr.
  apply pow_le.
  apply Rle_0_sqr.
  apply Rle_0_sqr.
  unfold toR at 2 in Hpu.
  now rewrite Hpu' in Hpu.
  apply (Fcore_generic_fmt.round_UP_pt _ (Fcore_FLX.FLX_exp _)).
unfold c1, c2, c3.
generalize (F.scale (F.fromZ 1) (F.ZtoS (Z.neg (F.prec prec)))) (Pos.to_nat (F.prec prec)).
intros thre n.
replace R1 with (A1 (toR x) 0) by (unfold A1 ; simpl ; field).
generalize (eq_refl (F.fromZ 1)).
generalize (F.fromZ 1) at 1 3.
intros powl Hpl.
assert (Rpl: FtoX (F.toF powl) = Xreal (toR powl)).
  rewrite Hpl.
  unfold toR.
  now rewrite F.fromZ_correct.
apply (f_equal toR) in Hpl.
assert (H: (0 <= toR powl)%R).
  rewrite Hpl.
  unfold toR.
  rewrite F.fromZ_correct.
  apply Rle_0_1.
apply Req_le in Hpl.
apply (conj H) in Hpl.
clear H.
generalize (eq_refl (F.fromZ 1)).
generalize (F.fromZ 1) at 2 3.
intros powu Hpu.
assert (Rpu: FtoX (F.toF powu) = Xreal (toR powu)).
  rewrite <- Hpu.
  unfold toR.
  now rewrite F.fromZ_correct.
apply (f_equal toR) in Hpu.
apply Req_le in Hpu.
revert Hpl Hpu.
unfold toR at 3 4.
rewrite F.fromZ_correct.
change (Z2R 1) with (pow (toR x) (2 * 0)).
change 3%Z with (Z_of_nat (2 * (0 + 1) + 1)).
change 2%Z with (Z_of_nat (fact (2 * (0 + 1)))).
replace (A1 (toR x) 0 - cos (toR x))%R with ((-1) * 1 * (cos (toR x) - A1 (toR x) 0))%R by ring.
change (-1 * 1)%R with (pow (-1) (0 + 1)).
rewrite <- (minus_diag n) at 2 4 6 10 12 14.
generalize (le_refl n).
generalize n at 1 4 6 8 10 11 13 15.
intros m.
generalize (f_equal (fun v => FtoX (F.toF v)) (eq_refl (F.fromZ (Z.of_nat (2 * (n - m + 1) + 1))))).
generalize (f_equal (fun v => FtoX (F.toF v)) (eq_refl (F.fromZ (Z.of_nat (fact (2 * (n - m + 1))))))).
generalize (F.fromZ (Z.of_nat (2 * (n - m + 1) + 1))) at 1 3.
generalize (F.fromZ (Z.of_nat (fact (2 * (n - m + 1))))) at 1 3.
intros ft tp1.
revert powl powu ft tp1 Rpl Rpu.
induction m as [|m IHm] ; intros powl powu ft tp1 Rpl Rpu Hft Htp1 Hm Hpl Hpu.
  simpl.
  cut (contains (I.convert (I.bnd F.zero (F.div rnd_UP prec (F.mul rnd_UP prec powu sqru)
    ft))) (Xreal ((-1) ^ (n - 0 + 1) * (cos (toR x) - A1 (toR x) (n - 0))))).
  now destruct F.cmp.
  now apply Hexit.
simpl.
specialize (IHm (F.mul rnd_DN prec powl sqrl) (F.mul rnd_UP prec powu sqru) (F.mul_exact ft (F.mul_exact tp1 (F.add_exact tp1 c1))) (F.add_exact tp1 c2)).
assert (H: forall p, n - S m + S p = n - m + p).
  intros p.
  clear -Hm ; omega.
destruct ((cos_fast0_aux prec thre (F.mul rnd_DN prec powl sqrl)
    (F.mul rnd_UP prec powu sqru) sqrl sqru (F.add_exact tp1 c2)
    (F.mul_exact ft (F.mul_exact tp1 (F.add_exact tp1 c1))) m)).
  case F.cmp ; try easy.
  now apply Hexit.
cut (contains (I.convert (Ibnd
      (F.sub rnd_DN prec (F.div rnd_DN prec (F.mul rnd_DN prec powl sqrl) ft) u)
      (F.sub rnd_UP prec (F.div rnd_UP prec (F.mul rnd_UP prec powu sqru) ft) l)))
    (Xreal ((-1) ^ (n - S m + 1) * (cos (toR x) - A1 (toR x) (n - S m))))).
  case F.cmp ; try easy.
  intros H'.
  now apply Hexit.
replace ((-1) ^ (n - S m + 1) * (cos (toR x) - A1 (toR x) (n - S m)))%R
  with ((-1) ^ (n - S m + 1) * (-1) ^ S (n - S m) * (toR x) ^ (2 * S (n - S m)) * / INR (fact (2 * S (n - S m))) - (((-1) * (-1) ^ (n - S m + 1)) * (cos (toR x) - (A1 (toR x) (n - S m) + ((-1) ^ S (n - S m) * / INR (fact (2 * S (n - S m))) * (toR x) ^ (2 * S (n - S m)))))))%R by ring.
apply (I.sub_correct prec (Ibnd _ _) (Ibnd _ _) (Xreal _) (Xreal _)).
  rewrite <- pow_add.
  replace (n - S m + 1 + S (n - S m)) with (2 * (n - S m + 1)) by (clear -Hm ; omega).
  rewrite pow_1_even, Rmult_1_l.
  replace (S (n - S m)) with (n - S m + 1) by now rewrite plus_comm.
  unfold I.convert, I.convert_bound.
  rewrite 2!F.div_correct, 2!Fdiv_correct.
  rewrite 2!F.mul_correct, 2!Fmul_correct.
  rewrite Rpl, Rpu, Hft.
  rewrite F.fromZ_correct.
  unfold sqrl, sqru.
  rewrite 2!F.mul_correct, 2!Fmul_correct.
  rewrite Rx.
  unfold Xmul, Xdiv, xround.
  case is_zero_spec.
  intros H'.
  apply (eq_Z2R _ 0) in H'.
  elim (fact_neq_0 (2 * (n - S m + 1))).
  now apply Nat2Z.inj.
  intros _.
  rewrite Z2R_IZR, <- INR_IZR_INZ.
  replace (2 * (n - S m + 1)) with (2 * (n - S m) + 2) by ring.
  rewrite pow_add.
  change (toR x ^ 2)%R with (toR x * (toR x * 1))%R.
  rewrite Rmult_1_r.
  split ; bound_tac ; apply Rmult_le_compat_r ;
    (try apply Rlt_le, Rinv_0_lt_compat, (lt_INR 0), lt_O_fact) ;
    bound_tac ; apply Rmult_le_compat ; try easy.
  apply Fcore_generic_fmt.round_ge_generic ; auto with typeclass_instances.
  apply Fcore_generic_fmt.generic_format_0.
  apply Rle_0_sqr.
  apply (Fcore_generic_fmt.round_DN_pt _ (Fcore_FLX.FLX_exp _)).
  rewrite pow_sqr.
  apply pow_le.
  apply Rle_0_sqr.
  apply Rle_0_sqr.
  apply (Fcore_generic_fmt.round_UP_pt _ (Fcore_FLX.FLX_exp _)).
match goal with |- ?f ?x => refine (@eq_ind _ _ f _ x _) end.
apply IHm.
unfold toR, sqrl.
do 2 rewrite F.mul_correct, Fmul_correct.
now rewrite Rpl, Rx.
unfold toR, sqru.
do 2 rewrite F.mul_correct, Fmul_correct.
now rewrite Rpu, Rx.
do 2 rewrite F.mul_exact_correct, Fmul_exact_correct.
rewrite F.add_exact_correct, Fadd_exact_correct.
rewrite Hft, Htp1.
unfold c1.
rewrite 4!F.fromZ_correct.
simpl.
rewrite <- (Z2R_plus _ 1), <- (inj_plus _ 1).
rewrite <- 2!Z2R_mult, <- 2!inj_mult.
apply (f_equal (fun v => Xreal (Z2R (Z.of_nat v)))).
rewrite H.
replace (n - m + 1 + (n - m + 1 + 0)) with (S (S (n - m + 0 + (n - m + 0 + 0)))) by ring.
simpl.
ring.
rewrite F.add_exact_correct, Fadd_exact_correct.
rewrite Htp1, H.
unfold c2.
rewrite 3!F.fromZ_correct.
simpl.
rewrite <- (Z2R_plus _ 2), <- (inj_plus _ 2).
apply (f_equal (fun v => Xreal (Z2R (Z.of_nat v)))).
ring.
clear -Hm ; omega.
unfold toR, sqrl.
do 2 rewrite F.mul_correct, Fmul_correct.
rewrite Rpl, Rx.
simpl.
split.
apply Fcore_generic_fmt.round_ge_generic ; auto with typeclass_instances.
apply Fcore_generic_fmt.generic_format_0.
apply Rmult_le_pos.
apply Hpl.
apply Fcore_generic_fmt.round_ge_generic ; auto with typeclass_instances.
apply Fcore_generic_fmt.generic_format_0.
apply Rle_0_sqr.
bound_tac.
replace (n - m + (n - m + 0)) with (2 * (n - S m) + 2) by (clear -Hm ; omega).
rewrite pow_add.
apply Rmult_le_compat ; try easy.
apply Fcore_generic_fmt.round_ge_generic ; auto with typeclass_instances.
apply Fcore_generic_fmt.generic_format_0.
apply Rle_0_sqr.
unfold pow.
rewrite Rmult_1_r.
apply (Fcore_generic_fmt.round_DN_pt _ (Fcore_FLX.FLX_exp _)).
unfold toR, sqru.
do 2 rewrite F.mul_correct, Fmul_correct.
rewrite Rpu, Rx.
simpl.
bound_tac.
replace (n - m + (n - m + 0)) with (2 * (n - S m) + 2) by (clear -Hm ; omega).
rewrite pow_add.
apply Rmult_le_compat ; try easy.
rewrite pow_sqr.
apply pow_le.
apply Rle_0_sqr.
apply pow2_ge_0.
unfold pow.
rewrite Rmult_1_r.
apply (Fcore_generic_fmt.round_UP_pt _ (Fcore_FLX.FLX_exp _)).
apply f_equal.
change (A1 (toR x) (n - S m) + (-1) ^ S (n - S m) * / INR (fact (2 * S (n - S m))) * toR x ^ (2 * S (n - S m)))%R
  with (A1 (toR x) (S (n - S m))).
change (-1 * (-1) ^ (n - S m + 1))%R with ((-1) ^ (S (n - S m + 1)))%R.
rewrite <- plus_Sn_m.
now rewrite -> minus_Sn_m.
Qed.

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
case_eq (le x (F.scale2 c1 sm1)).
intros.
exact (H x Hxr Hx H0).
intros _.
simpl.
unfold I.convert_bound, c1.
rewrite F.neg_correct, Fneg_correct, F.fromZ_correct.
refine (conj _ I).
simpl.
apply COS_bound.
(* nb > 0 *)
simpl.
case_eq (le x (F.scale2 c1 sm1)).
intros.
exact (H x Hxr Hx H0).
intros _.
refine (_ (IHnb (F.scale2 x sm1) _ _)).
destruct (sin_cos_reduce prec (F.scale2 x sm1) nb) as (ss, ci).
clear -Hxr.
replace (toR x) with (2 * (toR (F.scale2 x sm1)))%R.
generalize (toR (F.scale2 x sm1)).
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
unfold toR, sm1.
rewrite scale2_correct.
rewrite Hxr.
simpl.
field.
(* - . *)
unfold toR, sm1.
now rewrite scale2_correct, Hxr.
unfold toR, sm1.
rewrite scale2_correct, Hxr.
simpl.
apply Rmult_lt_0_compat.
exact Hx.
apply Rinv_0_lt_compat.
now apply (Z2R_lt 0 2).
Qed.

(* 0 <= input *)
Definition cos_fastP prec x :=
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
  | Xeq => I.bnd c1 c1
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
unfold I.convert_bound, c1.
rewrite F.fromZ_correct.
rewrite cos_0.
split ; apply Rle_refl.
unfold cos_fastP.
assert (H12: (/2)%R = toR (F.scale2 c1 sm1)).
unfold toR, c1, sm1.
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
destruct (le_spec (F.neg x) (F.scale2 c1 sm1)).
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
destruct (le_spec x (F.scale2 c1 sm1)).
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
    let nfact := F.add_exact fact c2 in
    let ndiv := F.mul_exact div (F.mul_exact fact (F.add_exact fact c1)) in
    I.sub prec (I.bnd vall valu)
      (sin_fast0_aux prec thre npwl npwu sqrl sqru nfact ndiv n)
  end.

(* -1/2 <= input <= 1/2 *)
Definition sin_fast0 prec x :=
  let x2l := F.mul rnd_DN prec x x in
  let x2u := F.mul rnd_UP prec x x in
  let p := F.prec prec in
  let thre := F.scale c1 (F.ZtoS (Zneg p)) in
  let rem := sin_fast0_aux prec thre c1 c1 x2l x2u c4 c6 (nat_of_P p) in
  I.mul_mixed prec (I.sub prec (I.bnd c1 c1) rem) x.

Lemma sin_fast0_correct :
  forall prec x,
  FtoX (F.toF x) = Xreal (toR x) ->
  (Rabs (toR x) <= /2)%R ->
  contains (I.convert (sin_fast0 prec x)) (Xreal (sin (toR x))).
Proof.
intros prec x Rx Bx.
unfold sin_fast0.
rewrite sin_sinc.
replace (sinc (toR x)) with (1 - (1 - sinc (toR x)))%R by ring.
rewrite Rmult_comm.
change (Xreal (_ * _)) with (Xmul (Xreal (1 - (1 - sinc (toR x)))) (Xreal (toR x))).
rewrite <- Rx.
apply I.mul_mixed_correct.
apply (I.sub_correct _ _ _ (Xreal _) (Xreal _)).
rewrite I.bnd_correct.
unfold I.convert_bound, c1.
rewrite F.fromZ_correct.
split ; apply Rle_refl.
set (sqrl := F.mul rnd_DN prec x x).
set (sqru := F.mul rnd_UP prec x x).
pose (Si := fun x => sum_f_R0 (fun n : nat => ((-1) ^ n / INR (fact (2 * n + 1)) * x ^ (2 * n))%R)).
assert (Hexit : forall k powu ft,
    (toR x ^ (2 * k) <= toR powu)%R ->
    FtoX (F.toF ft) = FtoX (F.toF (F.fromZ (Z.of_nat (fact (2 * (k + 1) + 1))))) ->
    contains (I.convert (I.bnd F.zero (F.div rnd_UP prec (F.mul rnd_UP prec powu sqru) ft)))
      (Xreal ((-1) ^ (k + 1) * (sinc (toR x) - Si (toR x)%R k)))).
  intros k powu ft Hpu Hft.
  rewrite I.bnd_correct.
  unfold I.convert_bound.
  rewrite F.zero_correct.
  rewrite F.div_correct, Fdiv_correct.
  unfold sqru.
  do 2 rewrite F.mul_correct, Fmul_correct.
  rewrite Hft.
  rewrite F.fromZ_correct.
  rewrite Rx.
  simpl.
  assert (A: (0 <= (-1) ^ (k + 1) * (sinc (toR x) - Si (toR x) k) <= toR x ^ (2 * (k + 1)) / Z2R (Z.of_nat (fact (2 * (k + 1) + 1))))%R).
    rewrite Z2R_IZR, <- INR_IZR_INZ.
    replace (Si (toR x)%R k) with (sum_f_R0 (tg_alt (fun n => / INR (fact (2 * n + 1)) * toR x ^ (2 * n))%R) k).
    unfold Rdiv.
    rewrite (Rmult_comm (toR x ^ _)).
    replace (k + 1) with (S k) by ring.
    apply alternated_series_ineq'.
    apply Un_decreasing_sinc.
    apply Rle_trans with (1 := Bx).
    rewrite <- (Rinv_1) at 3.
    apply Rinv_le.
    apply Rlt_0_1.
    now apply (Z2R_le 1 2).
    destruct (Req_dec (toR x) 0) as [Zx|Zx].
    rewrite Zx.
    intros eps Heps.
    exists 1%nat.
    intros n Hn.
    rewrite pow_ne_zero by (clear -Hn ; omega).
    unfold R_dist, Rminus.
    now rewrite Rmult_0_r, Rplus_opp_r, Rabs_R0.
    rewrite <- (Rmult_0_l (/toR x)).
    apply Un_cv_ext with (fun n : nat => (/ INR (fact (2 * n + 1)) * toR x ^ (2 * n + 1) * / toR x)%R).
    intros n.
    rewrite pow_add.
    field.
    split.
    apply Rgt_not_eq.
    apply INR_fact_lt_0.
    exact Zx.
    apply CV_mult.
    apply (Un_cv_subseq (fun n => (/ INR (fact n) * toR x ^ n)%R)).
    clear ; intros n ; omega.
    eapply Un_cv_ext.
    intros n.
    apply Rmult_comm.
    apply cv_speed_pow_fact.
    intros eps Heps.
    exists 0.
    intros _ _.
    unfold R_dist, Rminus.
    now rewrite Rplus_opp_r, Rabs_R0.
    unfold sinc.
    case exist_sin.
    intro l.
    change (projT1 _) with l.
    apply Un_cv_ext.
    intros n.
    apply sum_eq.
    intros i _.
    unfold sin_n, tg_alt.
    rewrite pow_Rsqr.
    apply Rmult_assoc.
    unfold Si, tg_alt.
    apply sum_eq.
    intros i _.
    apply sym_eq, Rmult_assoc.
  split.
    apply A.
  case_eq (FtoX (F.toF powu)).
  easy.
  intros powu' Hpu'.
  simpl.
  case is_zero_spec.
  easy.
  intros H1.
  simpl.
  bound_tac.
  apply Rle_trans with (1 := proj2 A).
  apply Rmult_le_compat_r.
  apply Rlt_le, Rinv_0_lt_compat.
  apply (Z2R_lt 0), (inj_lt 0).
  apply lt_O_fact.
  bound_tac.
  replace (2 * (k + 1)) with (2 * k + 2) by ring.
  rewrite pow_add.
  simpl (toR x ^ 2)%R.
  rewrite Rmult_1_r.
  apply Rmult_le_compat.
  rewrite pow_sqr.
  apply pow_le.
  apply Rle_0_sqr.
  apply Rle_0_sqr.
  unfold toR at 2 in Hpu.
  now rewrite Hpu' in Hpu.
  apply (Fcore_generic_fmt.round_UP_pt _ (Fcore_FLX.FLX_exp _)).
unfold c1, c4, c6.
generalize (F.scale (F.fromZ 1) (F.ZtoS (Z.neg (F.prec prec)))) (Pos.to_nat (F.prec prec)).
intros thre n.
replace R1 with (Si (toR x) 0) by (unfold Si ; simpl ; field).
generalize (eq_refl (F.fromZ 1)).
generalize (F.fromZ 1) at 1 3.
intros powl Hpl.
assert (Rpl: FtoX (F.toF powl) = Xreal (toR powl)).
  rewrite Hpl.
  unfold toR.
  now rewrite F.fromZ_correct.
apply (f_equal toR) in Hpl.
assert (H: (0 <= toR powl)%R).
  rewrite Hpl.
  unfold toR.
  rewrite F.fromZ_correct.
  apply Rle_0_1.
apply Req_le in Hpl.
apply (conj H) in Hpl.
clear H.
generalize (eq_refl (F.fromZ 1)).
generalize (F.fromZ 1) at 2 3.
intros powu Hpu.
assert (Rpu: FtoX (F.toF powu) = Xreal (toR powu)).
  rewrite <- Hpu.
  unfold toR.
  now rewrite F.fromZ_correct.
apply (f_equal toR) in Hpu.
apply Req_le in Hpu.
revert Hpl Hpu.
unfold toR at 3 4.
rewrite F.fromZ_correct.
change (Z2R 1) with (pow (toR x) (2 * 0)).
change 4%Z with (Z_of_nat (2 * (0 + 1) + 2)).
change 6%Z with (Z_of_nat (fact (2 * (0 + 1) + 1))).
replace (Si (toR x) 0%nat - sinc (toR x))%R with ((-1) * 1 * (sinc (toR x) - Si (toR x) 0%nat))%R by ring.
change (-1 * 1)%R with (pow (-1) (0 + 1)).
rewrite <- (minus_diag n) at 2 4 6 10 13 15.
generalize (le_refl n).
generalize n at 1 4 6 8 10 11 13 15.
intros m.
generalize (f_equal (fun v => FtoX (F.toF v)) (eq_refl (F.fromZ (Z.of_nat (2 * (n - m + 1) + 2))))).
generalize (f_equal (fun v => FtoX (F.toF v)) (eq_refl (F.fromZ (Z.of_nat (fact (2 * (n - m + 1) + 1)))))).
generalize (F.fromZ (Z.of_nat (2 * (n - m + 1) + 2))) at 1 3.
generalize (F.fromZ (Z.of_nat (fact (2 * (n - m + 1) + 1)))) at 1 3.
intros ft tp1.
revert powl powu ft tp1 Rpl Rpu.
induction m as [|m IHm] ; intros powl powu ft tp1 Rpl Rpu Hft Htp1 Hm Hpl Hpu.
  simpl.
  cut (contains (I.convert (I.bnd F.zero (F.div rnd_UP prec (F.mul rnd_UP prec powu sqru)
    ft))) (Xreal ((-1) ^ (n - 0 + 1) * (sinc (toR x) - Si (toR x) (n - 0))))).
  now destruct F.cmp.
  now apply Hexit.
simpl.
specialize (IHm (F.mul rnd_DN prec powl sqrl) (F.mul rnd_UP prec powu sqru) (F.mul_exact ft (F.mul_exact tp1 (F.add_exact tp1 c1))) (F.add_exact tp1 c2)).
assert (H: forall p, n - S m + S p = n - m + p).
  intros p.
  clear -Hm ; omega.
destruct ((sin_fast0_aux prec thre (F.mul rnd_DN prec powl sqrl)
    (F.mul rnd_UP prec powu sqru) sqrl sqru (F.add_exact tp1 c2)
    (F.mul_exact ft (F.mul_exact tp1 (F.add_exact tp1 c1))) m)).
  case F.cmp ; try easy.
  now apply Hexit.
cut (contains (I.convert (Ibnd
      (F.sub rnd_DN prec (F.div rnd_DN prec (F.mul rnd_DN prec powl sqrl) ft) u)
      (F.sub rnd_UP prec (F.div rnd_UP prec (F.mul rnd_UP prec powu sqru) ft) l)))
    (Xreal ((-1) ^ (n - S m + 1) * (sinc (toR x) - Si (toR x) (n - S m))))).
  case F.cmp ; try easy.
  intros H'.
  now apply Hexit.
replace ((-1) ^ (n - S m + 1) * (sinc (toR x) - Si (toR x) (n - S m)%nat))%R
  with ((-1) ^ (n - S m + 1) * (-1) ^ S (n - S m) * (toR x) ^ (2 * S (n - S m)) * / INR (fact (2 * S (n - S m) + 1)) - (((-1) * (-1) ^ (n - S m + 1)) * (sinc (toR x) - (Si (toR x) (n - S m)%nat + ((-1) ^ S (n - S m) * / INR (fact (2 * S (n - S m) + 1)) * (toR x) ^ (2 * S (n - S m)))))))%R by ring.
apply (I.sub_correct prec (Ibnd _ _) (Ibnd _ _) (Xreal _) (Xreal _)).
  rewrite <- pow_add.
  replace (n - S m + 1 + S (n - S m)) with (2 * (n - S m + 1)) by (clear -Hm ; omega).
  rewrite pow_1_even, Rmult_1_l.
  replace (S (n - S m)) with (n - S m + 1) by now rewrite plus_comm.
  unfold I.convert, I.convert_bound.
  rewrite 2!F.div_correct, 2!Fdiv_correct.
  rewrite 2!F.mul_correct, 2!Fmul_correct.
  rewrite Rpl, Rpu, Hft.
  rewrite F.fromZ_correct.
  unfold sqrl, sqru.
  rewrite 2!F.mul_correct, 2!Fmul_correct.
  rewrite Rx.
  unfold Xmul, Xdiv, xround.
  case is_zero_spec.
  intros H'.
  apply (eq_Z2R _ 0) in H'.
  elim (fact_neq_0 (2 * (n - S m + 1) + 1)).
  now apply Nat2Z.inj.
  intros _.
  rewrite Z2R_IZR, <- INR_IZR_INZ.
  replace (2 * (n - S m + 1)) with (2 * (n - S m) + 2) by ring.
  rewrite pow_add.
  change (toR x ^ 2)%R with (toR x * (toR x * 1))%R.
  rewrite Rmult_1_r.
  split ; bound_tac ; apply Rmult_le_compat_r ;
    (try apply Rlt_le, Rinv_0_lt_compat, (lt_INR 0), lt_O_fact) ;
    bound_tac ; apply Rmult_le_compat ; try easy.
  apply Fcore_generic_fmt.round_ge_generic ; auto with typeclass_instances.
  apply Fcore_generic_fmt.generic_format_0.
  apply Rle_0_sqr.
  apply (Fcore_generic_fmt.round_DN_pt _ (Fcore_FLX.FLX_exp _)).
  rewrite pow_sqr.
  apply pow_le.
  apply Rle_0_sqr.
  apply Rle_0_sqr.
  apply (Fcore_generic_fmt.round_UP_pt _ (Fcore_FLX.FLX_exp _)).
match goal with |- ?f ?x => refine (@eq_ind _ _ f _ x _) end.
apply IHm.
unfold toR, sqrl.
do 2 rewrite F.mul_correct, Fmul_correct.
now rewrite Rpl, Rx.
unfold toR, sqru.
do 2 rewrite F.mul_correct, Fmul_correct.
now rewrite Rpu, Rx.
do 2 rewrite F.mul_exact_correct, Fmul_exact_correct.
rewrite F.add_exact_correct, Fadd_exact_correct.
rewrite Hft, Htp1.
unfold c1.
rewrite 4!F.fromZ_correct.
simpl.
rewrite <- (Z2R_plus _ 1), <- (inj_plus _ 1).
rewrite <- 2!Z2R_mult, <- 2!inj_mult.
apply (f_equal (fun v => Xreal (Z2R (Z.of_nat v)))).
rewrite H.
replace (n - m + 1 + (n - m + 1 + 0)) with (S (S (n - m + 0 + (n - m + 0 + 0)))) by ring.
simpl.
ring.
rewrite F.add_exact_correct, Fadd_exact_correct.
rewrite Htp1, H.
unfold c2.
rewrite 3!F.fromZ_correct.
simpl.
rewrite <- (Z2R_plus _ 2), <- (inj_plus _ 2).
apply (f_equal (fun v => Xreal (Z2R (Z.of_nat v)))).
ring.
clear -Hm ; omega.
unfold toR, sqrl.
do 2 rewrite F.mul_correct, Fmul_correct.
rewrite Rpl, Rx.
simpl.
split.
apply Fcore_generic_fmt.round_ge_generic ; auto with typeclass_instances.
apply Fcore_generic_fmt.generic_format_0.
apply Rmult_le_pos.
apply Hpl.
apply Fcore_generic_fmt.round_ge_generic ; auto with typeclass_instances.
apply Fcore_generic_fmt.generic_format_0.
apply Rle_0_sqr.
bound_tac.
replace (n - m + (n - m + 0)) with (2 * (n - S m) + 2) by (clear -Hm ; omega).
rewrite pow_add.
apply Rmult_le_compat ; try easy.
apply Fcore_generic_fmt.round_ge_generic ; auto with typeclass_instances.
apply Fcore_generic_fmt.generic_format_0.
apply Rle_0_sqr.
unfold pow.
rewrite Rmult_1_r.
apply (Fcore_generic_fmt.round_DN_pt _ (Fcore_FLX.FLX_exp _)).
unfold toR, sqru.
do 2 rewrite F.mul_correct, Fmul_correct.
rewrite Rpu, Rx.
simpl.
bound_tac.
replace (n - m + (n - m + 0)) with (2 * (n - S m) + 2) by (clear -Hm ; omega).
rewrite pow_add.
apply Rmult_le_compat ; try easy.
rewrite pow_sqr.
apply pow_le.
apply Rle_0_sqr.
apply pow2_ge_0.
unfold pow.
rewrite Rmult_1_r.
apply (Fcore_generic_fmt.round_UP_pt _ (Fcore_FLX.FLX_exp _)).
apply f_equal.
change (Si (toR x) (n - S m)%nat + (-1) ^ S (n - S m) * / INR (fact (2 * S (n - S m) + 1)) * toR x ^ (2 * S (n - S m)))%R
  with (Si (toR x) (S (n - S m))).
change (-1 * (-1) ^ (n - S m + 1))%R with ((-1) ^ (S (n - S m + 1)))%R.
rewrite <- plus_Sn_m.
now rewrite -> minus_Sn_m.
Qed.

(* 0 <= input *)
Definition sin_fastP prec x :=
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
destruct (le_spec (F.neg x) (F.scale2 c1 sm1)).
(* . small *)
replace (FtoR F.radix false p z) with (toR (F.neg x)).
apply sin_fast0_correct.
unfold toR.
rewrite F.neg_correct.
now rewrite H.
rewrite Rabs_right.
replace (/ 2)%R with (toR (F.scale2 c1 sm1)).
exact Hxy.
unfold toR, c1, sm1.
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
unfold I.convert_bound, c1.
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
unfold I.convert_bound, c1.
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
unfold I.convert_bound, c1.
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
destruct (le_spec x (F.scale2 c1 sm1)).
(* . small *)
replace (FtoR F.radix false p z) with (toR x).
apply sin_fast0_correct.
unfold toR.
now rewrite H.
rewrite Rabs_right.
replace (/ 2)%R with (toR (F.scale2 c1 sm1)).
exact Hxy.
unfold toR, c1, sm1.
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
unfold I.convert_bound, c1.
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
unfold I.convert_bound, c1.
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
unfold I.convert_bound, c1.
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
  let i1 := I.bnd c1 c1 in
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
    let nfact := F.add_exact fact c1 in
    let ndiv := F.mul_exact div fact in
    I.sub prec (I.bnd vall valu)
      (expn_fast0_aux prec thre npwl npwu x nfact ndiv n)
  end.

(* 0 <= input <= 1/2 *)
Definition expn_fast0 prec x :=
  let p := F.prec prec in
  let thre := F.scale c1 (F.ZtoS (Zneg p)) in
  let rem := expn_fast0_aux prec thre x x x c3 c2 (nat_of_P p) in
  I.sub prec (I.bnd c1 c1) (I.sub prec (I.bnd x x) rem).

(* 0 <= input *)
Definition expn_reduce prec x :=
  let th := F.scale2 c1 sm8 in
  match le x th with
  | true => expn_fast0 (F.incr_prec prec 1) x
  | false =>
    let m := F.StoZ (F.mag x) in
    let prec := F.incr_prec prec (Z2P (9 + m)) in
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
  | Xeq => I.bnd c1 c1
  | Xlt => expn_reduce prec (F.neg x)
  | Xgt =>
    let prec := F.incr_prec prec 1 in
    match I.inv prec (expn_reduce prec x) with
    | Ibnd _ _ as b => b
    | Inai => I.bnd c1 F.nan
    end
  | Xund => I.nai
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
unfold I.convert_bound, c1.
rewrite F.fromZ_correct.
split ; apply Rle_refl.
apply (I.sub_correct _ _ _ (Xreal _) (Xreal _)).
rewrite I.bnd_correct.
unfold I.convert_bound.
rewrite Rx.
split ; apply Rle_refl.
assert (Hexit : forall k powxu fp2,
    (toR x ^ (k + 1) <= toR powxu)%R ->
    FtoX (F.toF fp2) = FtoX (F.toF (F.fromZ (Z.of_nat (fact (k + 2))))) ->
    contains (I.convert (I.bnd F.zero (F.div rnd_UP prec (F.mul rnd_UP prec powxu x) fp2)))
      (Xreal ((-1) ^ k * (exp (- toR x) + - E1 (- toR x) (k + 1))))).
  intros k powxu fp2 Hpu Hfp2.
  rewrite I.bnd_correct.
  unfold I.convert_bound.
  rewrite F.zero_correct.
  rewrite F.div_correct, Fdiv_correct.
  rewrite F.mul_correct, Fmul_correct.
  rewrite Hfp2.
  rewrite F.fromZ_correct.
  rewrite Rx.
  simpl.
  assert (A: (0 <= (-1) ^ k * (exp (- toR x) + - E1 (- toR x) (k + 1)) <= toR x ^ (k + 2) / Z2R (Z.of_nat (fact (k + 2))))%R).
    replace ((-1) ^ k)%R with ((-1) * ((-1) * (-1) ^ k))%R by ring.
    change ((-1) * ((-1) * (-1) ^ k))%R with ((-1) ^ (S (S k)))%R.
    rewrite Z2R_IZR, <- INR_IZR_INZ.
    unfold Rdiv.
    rewrite (Rmult_comm (toR x ^ (k + 2))).
    replace (E1 (- toR x) (k + 1)) with (sum_f_R0 (tg_alt (fun n => / INR (fact n) * toR x ^ n)%R) (k + 1)).
    rewrite <- (plus_n_Sm _ 1).
    replace (S k) with (k + 1) by ring.
    apply alternated_series_ineq'.
    apply Un_decreasing_exp.
    split.
    apply Bx.
    apply Rle_trans with (1 := proj2 Bx).
    rewrite <- (Rinv_1) at 3.
    apply Rinv_le.
    apply Rlt_0_1.
    now apply (Z2R_le 1 2).
    eapply Un_cv_ext.
    intros n.
    apply Rmult_comm.
    apply cv_speed_pow_fact.
    generalize (E1_cvg (- toR x)).
    apply Un_cv_ext.
    intros n.
    unfold E1, tg_alt.
    apply sum_eq.
    intros i _.
    rewrite (Rmult_comm _ (toR x ^ i)), <- Rmult_assoc.
    rewrite <- Rpow_mult_distr.
    rewrite Rmult_comm.
    apply (f_equal (fun v => (v ^ i * _)%R)).
    ring.
    unfold E1, tg_alt.
    apply sum_eq.
    intros i _.
    unfold Rdiv.
    rewrite Rmult_comm, Rmult_assoc.
    rewrite <- Rpow_mult_distr.
    apply (f_equal (fun v => (_ * v ^ i)%R)).
    ring.
  split.
    apply A.
  case_eq (FtoX (F.toF powxu)).
  easy.
  intros powxu' Hpu'.
  simpl.
  case is_zero_spec.
  easy.
  intros H1.
  simpl.
  bound_tac.
  apply Rle_trans with (1 := proj2 A).
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
unfold c1, c2, c3.
generalize (F.scale (F.fromZ 1) (F.ZtoS (Z.neg (F.prec prec)))) (Pos.to_nat (F.prec prec)).
intros thre n.
replace (1 - toR x)%R with (E1 (- toR x) (0 + 1)) by (unfold E1 ; simpl ; field).
generalize (eq_refl x).
generalize x at 1 3.
intros powxl Hpl.
assert (Rpl: FtoX (F.toF powxl) = Xreal (toR powxl)).
  rewrite Hpl at 2.
  now rewrite <- Rx, Hpl.
apply (f_equal toR) in Hpl.
apply Req_le in Hpl.
generalize (eq_refl x).
generalize x at 2 3.
intros powxu Hpu.
assert (Rpu: FtoX (F.toF powxu) = Xreal (toR powxu)).
  rewrite <- Hpu at 2.
  now rewrite <- Rx, <- Hpu.
apply (f_equal toR) in Hpu.
apply Req_le in Hpu.
revert Hpl Rpl Hpu Rpu.
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
generalize (f_equal (fun v => FtoX (F.toF v)) (eq_refl (F.fromZ (Z.of_nat (n - m + 3))))).
generalize (f_equal (fun v => FtoX (F.toF v)) (eq_refl (F.fromZ (Z.of_nat (fact (n - m + 2)))))).
generalize (F.fromZ (Z.of_nat (n - m + 3))) at 1 3.
generalize (F.fromZ (Z.of_nat (fact (n - m + 2)))) at 1 3.
revert powxl powxu.
induction m as [|m IHm] ; intros powxl powxu fp2 p3 Hfp2 Hp3 Hm Hpl Rpl Hpu Rpu.
  simpl.
  cut (contains (I.convert (I.bnd F.zero (F.div rnd_UP prec (F.mul rnd_UP prec powxu x)
    fp2))) (Xreal ((-1) ^ (n - 0) * (exp (- toR x) + - E1 (- toR x) (n - 0 + 1))))).
  now destruct F.cmp.
  now apply Hexit.
simpl.
specialize (IHm (F.mul rnd_DN prec powxl x) (F.mul rnd_UP prec powxu x) (F.mul_exact fp2 p3) (F.add_exact p3 c1)).
assert (H: forall p, n - S m + S p = n - m + p).
  intros p.
  clear -Hm ; omega.
destruct ((expn_fast0_aux prec thre (F.mul rnd_DN prec powxl x)
    (F.mul rnd_UP prec powxu x) x (F.add_exact p3 c1)
    (F.mul_exact fp2 p3) m)).
  case F.cmp ; try easy.
  now apply Hexit.
cut (contains (I.convert (Ibnd
      (F.sub rnd_DN prec (F.div rnd_DN prec (F.mul rnd_DN prec powxl x) fp2) u)
      (F.sub rnd_UP prec (F.div rnd_UP prec (F.mul rnd_UP prec powxu x) fp2) l)))
    (Xreal ((-1) ^ (n - S m) * (exp (- toR x) + - E1 (- toR x) (n - S m + 1))))).
  case F.cmp ; try easy.
  intros H'.
  now apply Hexit.
replace ((-1) ^ (n - S m) * (exp (- toR x) + - E1 (- toR x) (n - S m + 1)))%R
  with ((toR x) ^ (n - m + 1) * / INR (fact (n - m + 1)) - (((-1) * (-1) ^ (n - S m)) * (exp (- toR x) + - E1 (- toR x) (n - S m + 1)) + / INR (fact (n - m + 1)) * (toR x) ^ (n - m + 1)))%R by ring.
change (-1 * (-1) ^ (n - S m))%R with ((-1) ^ (S (n - S m)))%R.
rewrite -> minus_Sn_m with (1 := Hm).
simpl (S n - S m).
apply (I.sub_correct prec (Ibnd _ _) (Ibnd _ _) (Xreal _) (Xreal _)).
  unfold I.convert, I.convert_bound.
  rewrite 2!F.div_correct, 2!Fdiv_correct.
  rewrite 2!F.mul_correct, 2!Fmul_correct.
  rewrite Rx, Rpl, Rpu, Hfp2.
  rewrite F.fromZ_correct.
  simpl.
  case is_zero_spec.
  intros H'.
  apply (eq_Z2R _ 0) in H'.
  elim (fact_neq_0 (n - S m + 2)).
  now apply Nat2Z.inj.
  intros _.
  simpl.
  rewrite H.
  rewrite Z2R_IZR, <- INR_IZR_INZ.
  rewrite <- plus_n_Sm.
  simpl pow.
  rewrite (Rmult_comm (toR x)).
  rewrite <- H.
  split ; bound_tac ; apply Rmult_le_compat_r ;
    (try apply Rlt_le, Rinv_0_lt_compat, (lt_INR 0), lt_O_fact) ;
    bound_tac ;
    now apply Rmult_le_compat_r.
match goal with |- ?f ?x => refine (@eq_ind _ _ f _ x _) end.
apply IHm.
rewrite F.mul_exact_correct, Fmul_exact_correct.
rewrite Hfp2, Hp3, 2!H.
rewrite 3!F.fromZ_correct.
simpl.
rewrite <- Z2R_mult, <- inj_mult.
now rewrite mult_comm, <- plus_n_Sm.
rewrite F.add_exact_correct, Fadd_exact_correct.
rewrite Hp3, H.
unfold c1.
rewrite 3!F.fromZ_correct.
simpl.
rewrite <- (Z2R_plus _ 1), <- (inj_plus _ 1).
now rewrite <- plus_assoc.
clear -Hm ; omega.
unfold toR.
rewrite F.mul_correct, Fmul_correct.
rewrite Rpl, Rx.
simpl.
bound_tac.
rewrite H in Hpl.
rewrite <- plus_n_Sm.
rewrite Rmult_comm.
now apply Rmult_le_compat_l.
unfold toR.
rewrite F.mul_correct, Fmul_correct.
now rewrite Rpl, Rx.
unfold toR.
rewrite F.mul_correct, Fmul_correct.
rewrite Rpu, Rx.
simpl.
bound_tac.
rewrite H in Hpu.
rewrite <- plus_n_Sm.
rewrite Rmult_comm.
now apply Rmult_le_compat_l.
unfold toR.
rewrite F.mul_correct, Fmul_correct.
now rewrite Rpu, Rx.
apply f_equal.
rewrite 2!Rmult_plus_distr_l.
rewrite Rplus_assoc.
apply f_equal.
rewrite H.
rewrite <- plus_n_Sm at 1.
unfold E1.
change (sum_f_R0 (fun k : nat => / INR (fact k) * (- toR x) ^ k) (S (n - m + 0)))%R
  with (sum_f_R0 (fun k : nat => / INR (fact k) * (- toR x) ^ k) (n - m + 0) + / INR (fact (S (n - m + 0))) * (- toR x) ^ (S (n - m + 0)))%R.
rewrite plus_n_Sm.
rewrite Ropp_plus_distr, Rmult_plus_distr_l.
apply f_equal.
rewrite <- Ropp_mult_distr_r_reverse.
rewrite (Rmult_comm (_ ^ _)), Rmult_assoc.
apply f_equal.
replace (- (- toR x) ^ (n - m + 1) * (-1) ^ (n - m))%R
  with ((- toR x) ^ (n - m + 1) * ((-1) * (-1) ^ (n - m)))%R by ring.
change (-1 * (-1) ^ (n - m))%R with ((-1) ^ (S (n - m)))%R .
rewrite <- plus_n_Sm, <- plus_n_O.
rewrite <- Rpow_mult_distr.
now replace (- toR x * -1)%R with (toR x) by ring.
Qed.

Lemma expn_reduce_correct :
  forall prec x,
  FtoX (F.toF x) = Xreal (toR x) ->
  (0 < toR x)%R ->
  contains (I.convert (expn_reduce prec x)) (Xreal (exp (- toR x))).
Proof.
assert (forall prec x,
  FtoX (F.toF x) = Xreal (toR x) ->
  (0 < toR x <= toR (F.scale2 c1 sm8))%R ->
  contains (I.convert (expn_fast0 prec x)) (Xreal (exp (- toR x)))).
intros prec x Hx1 (Hx2, Hx3).
apply expn_fast0_correct.
exact Hx1.
split.
now apply Rlt_le.
apply Rle_trans with (1 := Hx3).
unfold toR, c1, sm8.
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
destruct (le_spec x (F.scale2 c1 sm8)).
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
destruct (le_spec x (F.scale2 c1 sm8)).
apply H ; now try split.
simpl.
unfold I.convert_bound, c1.
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
destruct (le_spec x (F.scale2 c1 sm8)).
apply H ; now try split.
assert (toR (F.scale2 x sm1) = toR x * /2)%R.
unfold toR, sm1.
rewrite F.scale2_correct, Fscale2_correct.
now rewrite Hx.
exact F.even_radix_correct.
apply refl_equal.
replace (toR x) with (toR (F.scale2 x sm1) + toR (F.scale2 x sm1))%R.
rewrite Ropp_plus_distr.
rewrite exp_plus.
change (Xreal (exp (- toR (F.scale2 x sm1)) * exp (- toR (F.scale2 x sm1))))
  with (Xsqr (Xreal (exp (- toR (F.scale2 x sm1))))).
apply I.sqr_correct.
apply IHnb.
unfold toR, sm1.
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
unfold I.convert_bound, c1.
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
split ; unfold I.convert_bound, c1.
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