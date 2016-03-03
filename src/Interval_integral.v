Require Import Reals.
Require Import List.
Require Import Coquelicot.
Require Import Interval_xreal.
Require Import Interval_float_sig.
Require Import Interval_interval.
Require Import Interval_interval_float.
Require Import Ssreflect.ssreflect Ssreflect.ssrfun Ssreflect.ssrbool.
Require Import xreal_ssr_compat.
Require Import Interval_missing.
Require Import integrability.
Require Import Coquelicot coquelicot_compl.
Require Import Interval_generic.
Require Import Interval.Interval_generic_proof.

Require Import interval_compl.

Module ExtraFloats (F : FloatOps with Definition even_radix := true).
Module I := FloatInterval F.

Definition toR x := proj_val (FtoX (F.toF x)).

Lemma F_realP (fl : F.type) :
 reflect (I.convert_bound fl = Xreal (toR fl)) (F.real fl).
Proof.
have := (F.real_correct fl); rewrite /I.convert_bound /toR.
by case: (F.toF fl)=> [||y z t] ->; constructor.
Qed.

Definition notFnan (f : F.type) :=
  match F.toF f with
    | Interval_generic.Fnan  => false
    | _ => true
  end = true.

Lemma contains_convert_bnd_l (a b : F.type) : F.real a ->
  toR a <= toR b -> contains (I.convert (I.bnd a b)) (I.convert_bound a).
Proof.
move/F_realP => hra  hleab; rewrite hra; apply: le_contains.
  by rewrite hra; apply: le_lower_refl.
case Hb : (F.real b).
by move/F_realP : Hb ->.
move: (F.real_correct b); case H: (F.toF b); rewrite Hb //.
move => _.
have HXnan : I.convert_bound b = Xnan by rewrite /I.convert_bound H.
by rewrite HXnan.
Qed.

Lemma contains_convert_bnd_r (a b : F.type) : F.real b ->
  toR a <= toR b -> contains (I.convert (I.bnd a b)) (I.convert_bound b).
Proof.
move/F_realP =>  hrb hleab; rewrite hrb; apply: le_contains.
case Ha : (F.real a).
move/F_realP : Ha ->.
  rewrite /le_lower /=; exact: Ropp_le_contravar.
move: (F.real_correct a); case H : (F.toF a); rewrite Ha // .
move => _.
have -> : I.convert_bound a = Xnan by rewrite /I.convert_bound H.
done.
rewrite hrb; exact: le_upper_refl.
Qed.

Lemma contains_convert_bnd (a b : F.type) r :  F.real a -> F.real b ->
  toR a <= r <= toR b -> contains (I.convert (I.bnd a b)) (Xreal r).
Proof.
move/F_realP => hra /F_realP hrb hleab; apply: le_contains.
  by rewrite hra /le_lower /=; apply: Ropp_le_contravar; case: hleab.
by rewrite hrb /le_lower /=; case: hleab.
Qed.

(* Remember : toR = fun x : F.type => proj_val (FtoX (F.toF x)) *)
(* The statement of I.midpoint_correct is really clumsy *)
(* contains_le is also difficult to use... *)
(* I.midpoint_correct should be stated using toR *)
(* le_lower should either be a notation over le_upper or a new def *)
(* so that it simplifies to <= or else provide suitable lemmas *)
Lemma midpoint_bnd_in (a b : F.type) :
  F.real a -> F.real b -> toR a <= toR b ->
  toR a <= toR (I.midpoint (I.bnd a b)) <= toR b.
Proof.
move => hra hrb hleab; set iab := I.bnd a b; set m := I.midpoint iab.
pose xa := I.convert_bound a; pose xb := I.convert_bound b.
have non_empty_iab : exists x : ExtendedR, contains (I.convert iab) x.
  by exists xa; apply: contains_convert_bnd_l.
have [isr_xm xm_in_iab {non_empty_iab}] := I.midpoint_correct iab non_empty_iab.
rewrite -/(toR m) in isr_xm. (* I.midpoint_correct is ill stated *)
have [le_xa_xm le_xm_xb {xm_in_iab}] := contains_le xa xb _ xm_in_iab.
split; last by move: le_xm_xb; rewrite isr_xm /xb (F_realP _ hrb).
move: le_xa_xm.
by rewrite isr_xm /xa (F_realP _ hra) /le_lower /=; exact: Ropp_le_cancel.
Qed.

Definition thin (f : F.type) : I.type :=
  if F.real f then I.bnd f f else I.nai.

Lemma thin_correct (fl : F.type) :
 contains (I.convert (thin fl)) (I.convert_bound fl).
Proof.
rewrite /thin I.real_correct.
case ex: (I.convert_bound fl) => [|r] //=.
rewrite ex; split; exact: Rle_refl.
Qed.

Lemma thin_correct_toR (fl : F.type) :
  contains (I.convert (thin fl)) (Xreal (toR fl)).
Proof.
  case Hrealfl : (F.real fl);move: Hrealfl; move/F_realP => Hrealfl.
  * rewrite -Hrealfl.
      by apply: (thin_correct fl).
  * move/F_realP: Hrealfl; rewrite /thin.
      by rewrite -Bool.if_negb; move ->. (* probably not ideal *)
Qed.

End ExtraFloats.


Module IntegralTactic (F : FloatOps with Definition even_radix := true).

Module I := FloatInterval F.
Module Int := Integrability F.
Module EF := ExtraFloats F.
Import EF.

Section IntervalIntegral.

Section XRInt.

Variables (f : R -> R) (ra rb : R).

Hypothesis ltab : ra < rb.
Hypothesis fint : ex_RInt f ra rb.

Lemma XRInt1_correct (i : interval) :
  (forall x, ra < x < rb -> contains i (Xreal (f x))) ->
  contains i (Xreal ((RInt f ra rb) / (rb - ra))).
Proof.
move=> hif.
have sbapos : rb - ra > 0 by apply: Rgt_minus.
case: i hif => [|[|?] [|?]] //= hif; split => //.
- by apply: RInt_le_r_strict => // x /hif [].
- by apply: RInt_le_l_strict => // x /hif [].
- by apply: RInt_le_l_strict => // x /hif [].
- by apply: RInt_le_r_strict => // x /hif [].
Qed.

End XRInt.


(* A fixed precision *)
Variable prec : F.precision.

Variables (f : R -> R) (iF : I.type -> I.type).

(* This is a std monadic operation. Does it exist somewhere in the libs? *)
Let g := toXreal_fun f.

(* g is a restriction of f as an extendedR function. *)
Let Hfgext := toXreal_fun_correct f.


Hypothesis HiFIntExt : forall xi x, contains (I.convert xi) (Xreal x) -> contains (I.convert (iF xi)) (Xreal (f x)).

Section OrderOne.

Variables (a b : F.type).

(* f is integrable on [a, b]*)
Hypothesis Hintegrable : ex_RInt f (toR a) (toR b).

(* a <= b *)
Hypothesis  Hleab : toR a <= toR b.

(* a and b are not Nan. This cannot be deduced from Hleab *)
Hypothesis ha : F.real a.
Hypothesis hb : F.real b.

Definition naive_integral := I.mul prec (iF (I.bnd a b)) (I.sub prec (thin b) (thin a)).

Lemma naive_integral_correct :
  contains
    (I.convert (naive_integral))
    (Xreal (RInt f (toR a) (toR b))).
Proof.
rewrite /naive_integral.
case elu: (iF (I.bnd a b)) => // [l u].
set ra := toR a; set rb := toR b; fold ra rb in Hintegrable, ha, hb, Hleab.
set Iab := RInt _ _ _.
case: (Rle_lt_or_eq_dec _ _ Hleab) => [Hleab1 | Heqab]; last first.
  + have -> : Xreal Iab = Xmul (g (Xreal ra)) (Xsub (Xreal rb) (Xreal ra)).
      rewrite /Iab Heqab /= RInt_point; congr Xreal; ring.
    apply: I.mul_correct; last by apply: I.sub_correct; exact: thin_correct_toR.
    rewrite -elu; apply: HiFIntExt;  move/F_realP: ha<-.
    by apply: contains_convert_bnd_l.
  + have -> : Xreal Iab = Xmul (Xreal (Iab / (rb - ra))) (Xreal (rb - ra)).
       rewrite Xmul_Xreal; congr Xreal; field.
       by apply: Rminus_eq_contra; apply: Rlt_dichotomy_converse; right.
    apply: I.mul_correct; last first.
    - rewrite -[Xreal (rb - ra)]/(Xsub (Xreal rb) (Xreal ra)). (* 1 *)
      apply: I.sub_correct; exact: thin_correct_toR.
      (* try and show l * (b - a) <= int <= u * (b - a) instead *)
    - apply: XRInt1_correct => // x hx; rewrite -elu -[Xreal _]/(g (Xreal x)).
      apply: HiFIntExt; apply: contains_convert_bnd=> //; case: hx; split; exact: Rlt_le.
Qed.

End OrderOne.

Definition integralEstimatorCorrect (estimator : F.type -> F.type -> I.type) :=
        forall a b,
          ex_RInt f (toR a) (toR b) ->
          toR a <= toR b ->
          F.real a ->
          F.real b ->
          contains (I.convert (estimator a b)) (Xreal (RInt f (toR a) (toR b))).

Let Fle := Int.I.Fle.

Section Functions.

Variable est : F.type -> F.type -> I.type.

(* using F.sub instead? *)
Definition diam x :=
  match x with
    | Inan => F.nan
    | Ibnd a b => F.sub Interval_definitions.rnd_UP prec b a
  end.

Definition div2 f := F.scale2 f (F.ZtoS (-1)).

Fixpoint integral_float_absolute (depth : nat) (a b : F.type) (epsilon : F.type) :=
  let int := I.bnd a b in
  match depth with
    | O => let m := I.midpoint int in
           I.add prec (est a m) (est m b)
    | S n => let m := I.midpoint int in
             let int1 := I.bnd a m in
             let int2 := I.bnd m b in
             let halfeps := div2 epsilon in
             let roughEstimate_1 := est a m in
             let roughEstimate_2 := est m b in
             match Fle (diam roughEstimate_1) halfeps,Fle (diam roughEstimate_2) halfeps with
               | true,true => I.add prec roughEstimate_1 roughEstimate_2
               | true,false => let int2 := integral_float_absolute n m b (F.sub_exact epsilon (diam roughEstimate_1)) in I.add prec roughEstimate_1 int2
               | false,true => let int1 := integral_float_absolute n a m (F.sub_exact epsilon (diam roughEstimate_2)) in I.add prec int1 roughEstimate_2
               | false,false =>
                 let i1 := integral_float_absolute n a m halfeps in
                 let i2 := integral_float_absolute n m b halfeps in
                 I.add prec i1 i2
             end
  end.

Definition integral_float_relative
    (depth : nat) (a b : F.type) (epsilon : F.type) :=
  if F.real a && F.real b then
    let roughEst := est a b in
    if depth is O then roughEst
    else
      let epsilon :=
        if I.bounded roughEst then
          F.mul Interval_definitions.rnd_UP prec epsilon
            (I.upper (I.abs roughEst))
        else epsilon in
      if Fle (diam roughEst) epsilon then roughEst
      else integral_float_absolute (depth-1) a b epsilon
  else I.nai.

Lemma integral_float_absolute_Sn n a b epsilon :
  let int := I.bnd a b in
  let m := I.midpoint int in
  let int1 := I.bnd a m in
  let int2 := I.bnd m b in
  let halfeps := div2 epsilon in
  let roughEstimate_1 := est a m in
  let roughEstimate_2 := est m b in
  integral_float_absolute (S n) a b epsilon =
  match Fle (diam roughEstimate_1) halfeps,Fle (diam roughEstimate_2) halfeps with
    | true,true => I.add prec roughEstimate_1 roughEstimate_2
    | true,false => let int2 := integral_float_absolute n m b (F.sub_exact epsilon (diam roughEstimate_1)) in I.add prec roughEstimate_1 int2
    | false,true => let int1 := integral_float_absolute n a m (F.sub_exact epsilon (diam roughEstimate_2)) in I.add prec int1 roughEstimate_2
    | false,false =>
      let i1 := integral_float_absolute n a m halfeps in
      let i2 := integral_float_absolute n m b halfeps in
      I.add prec i1 i2
  end.
Proof.
by [].
Qed.

Definition integral_float_absolute_signed (depth : nat) (a b : F.type) (epsilon : F.type) :=
  match Fle a b with
    | false => I.neg (integral_float_relative depth b a epsilon)
    | true => integral_float_relative depth a b epsilon
  end.

Definition all_integrals (ia ib : I.type) :=
I.mul prec (iF (I.join ia ib)) (I.sub prec ib ia).

Definition integral_intBounds_epsilon depth (i1 i2 : I.type) epsilon :=
  if i1 is Ibnd a1 b1 then
    if i2 is Ibnd a2 b2 then
      match F.cmp b1 a2 with
        | Xeq | Xlt =>
                let si1 := all_integrals i1 (thin b1) in
                let si2 := all_integrals (thin a2) i2 in
                I.add prec
                      (I.add prec si1 (integral_float_absolute_signed depth b1 a2 epsilon)) si2
        | _ => Inan end
    else
      Inan
  else
    Inan.


End Functions.

Section Proofs.

Variable estimator : F.type -> F.type -> I.type.

Hypothesis Hcorrect : integralEstimatorCorrect estimator.

Let integral_float_relative := integral_float_relative (estimator).

Lemma integral_float_absolute_correct (depth : nat) (a b : F.type) epsilon :
  F.real a -> F.real b ->
  ex_RInt f (toR a) (toR b) ->
  toR a <= toR b ->
  contains (I.convert (integral_float_absolute estimator depth a b epsilon)) (Xreal (RInt f (toR a) (toR b))).
Proof.
move => Hareal Hbreal.
elim: depth a b epsilon Hareal Hbreal => [ | k Hk] a b epsilon Hareal Hbreal Hintegrable Hleab.
- set midpoint := I.midpoint (I.bnd a b).
  have hIl : ex_RInt f (toR a) (toR midpoint).
    by apply:  (ex_RInt_Chasles_1 _ _ _ (toR b)) => //; apply: midpoint_bnd_in.
  have hIr : ex_RInt f (toR midpoint) (toR b).
    by apply:  (ex_RInt_Chasles_2 f (toR a))=> //; apply: midpoint_bnd_in.
  have -> : RInt f (toR a) (toR b) =
            RInt f (toR a) (toR midpoint) + RInt f (toR midpoint) (toR b).
    by rewrite RInt_Chasles.
  set I1 := RInt _ _ _; set I2 := RInt _ _ _.
  have [in1 in2] := midpoint_bnd_in a b Hareal Hbreal Hleab.
  have hm : F.real (I.midpoint (I.bnd a b)).
  suff /I.midpoint_correct []:
    exists x : ExtendedR, contains (I.convert (I.bnd a b)) x by move/F_realP.
    by exists (I.convert_bound a); apply: contains_convert_bnd_l => //; exact/F_realP.
 by rewrite Xreal_add; apply: I.add_correct; apply: Hcorrect => // .
- set midpoint := I.midpoint (I.bnd a b).
have hIl : ex_RInt f (toR a) (toR midpoint).
  by apply:  (ex_RInt_Chasles_1 _ _ _ (toR b)) => //; apply: midpoint_bnd_in.
have hIr : ex_RInt f (toR midpoint) (toR b).
  by apply:  (ex_RInt_Chasles_2 f (toR a))=> //; apply: midpoint_bnd_in.
have -> : RInt f (toR a) (toR b) =
  RInt f (toR a) (toR midpoint) + RInt f (toR midpoint) (toR b).
  by rewrite RInt_Chasles.
set I1 := RInt _ _ _; set I2 := RInt _ _ _.
have [in1 in2] := midpoint_bnd_in a b Hareal Hbreal Hleab.
rewrite integral_float_absolute_Sn.
rewrite (* /integral_float_absolute -/integral_float_absolute. *) -[Xreal (_ + _)]/(Xadd (Xreal I1) (Xreal I2)).
set d1 := diam _.
set d2 := diam _.
have hm : F.real (I.midpoint (I.bnd a b)).
  suff /I.midpoint_correct []:
    exists x : ExtendedR, contains (I.convert (I.bnd a b)) x by move/F_realP.
  by exists (I.convert_bound a); apply: contains_convert_bnd_l => //; exact/F_realP.
case Hcmp1 : (Fle d1 (div2 epsilon)); case Hcmp2 : (Fle d2 (div2 epsilon));
repeat ((try (apply: I.add_correct => // )); try (apply: Hcorrect => // ); try (apply: Hk => // )).
Qed.

Lemma integral_float_relative_correct (depth : nat) (a b : F.type) epsilon :
  ex_RInt f (toR a) (toR b) ->
  toR a <= toR b ->
  contains (I.convert (integral_float_relative depth a b epsilon)) (Xreal (RInt f (toR a) (toR b))).
Proof.
(* case: depth => [|depth]. *)
(*   - rewrite /integral_float_relative /IntervalIntegral.integral_float_relative. *)
(*     move => Hfint Hab. apply:Hcorrect. *)
case Hareal : (F.real a); case Hbreal: (F.real b) => Hfint Hab; case: depth => [|depth] => // ;rewrite /integral_float_relative /IntervalIntegral.integral_float_relative ?Hareal ?Hbreal // .
- by rewrite /=; apply: Hcorrect.
- case: I.bounded; case: Fle; first by apply: Hcorrect.
  + by apply: integral_float_absolute_correct.
  + by apply: Hcorrect.
  + by apply: integral_float_absolute_correct.
Qed.

Lemma real_correct' :
  forall a, F.real a -> FtoX (F.toF a) = Xreal (toR a).
Proof.
intros a Ha.
generalize (F.real_correct a).
rewrite Ha /toR.
now destruct F.toF.
Qed.

Lemma RgtToFcmp a b :
  F.real a -> F.real b -> toR b < toR a -> F.cmp a b = Xgt.
Proof.
move => Ha Hb Hlt.
rewrite F.cmp_correct Interval_generic_proof.Fcmp_correct.
by rewrite (real_correct' a Ha) (real_correct' b Hb) /= Rcompare_Gt.
Qed.

Lemma RltToFcmp a b :
  F.real a -> F.real b -> toR a < toR b -> F.cmp a b = Xlt.
Proof.
move => Ha Hb Hlt.
rewrite F.cmp_correct Interval_generic_proof.Fcmp_correct.
by rewrite (real_correct' a Ha) (real_correct' b Hb) /= Rcompare_Lt.
Qed.

Lemma ReqToFcmp a b :
  F.real a -> F.real b -> toR a = toR b -> F.cmp a b = Xeq.
Proof.
move => Ha Hb Heq.
rewrite F.cmp_correct Interval_generic_proof.Fcmp_correct.
by rewrite (real_correct' a Ha) (real_correct' b Hb) /= Rcompare_Eq.
Qed.

Lemma Fcmp_geP u0 l1 :
  F.real u0 -> F.real l1 ->
  match F.cmp u0 l1 with
    | Xeq => True
    | Xlt => True
    | _ => False end -> (toR u0) <= (toR l1).
Proof.
  move => /F_realP Hrealu0 /F_realP Hreall1.
  rewrite F.cmp_correct Fcmp_correct /Xcmp.
  rewrite /I.convert_bound in Hrealu0.
  rewrite /I.convert_bound in Hreall1.
  rewrite Hreall1.
  rewrite Hrealu0.
  case Hcomp : (Rcompare (toR u0) (toR l1)) => // .
  have := (Rcompare_Eq_inv _ _ Hcomp) => -> _.
    exact: Rle_refl.
  have := (Rcompare_Lt_inv _ _ Hcomp).
    by move => H1 _; apply: Rlt_le.
Qed.

Lemma Fle_Rle u0 l1 :
  F.real u0 ->
  F.real l1 ->
  Int.I.Fle u0 l1 ->
  toR u0 <= toR l1.
Proof.
move => /F_realP Hrealu0 /F_realP Hreall1.
move: (Int.I.Fle_correct u0 l1).
have -> : Int.I.I.convert_bound u0 = I.convert_bound u0 by []. (* ?? *)
have -> : Int.I.I.convert_bound l1 = I.convert_bound l1 by [].
by rewrite Hreall1 Hrealu0.
Qed.

Lemma Rle_Fle a b :
  F.real a ->
  F.real b ->
  toR a <= toR b ->
  Int.I.Fle a b.
Proof.
case Hle : (Int.I.Fle a b) => // .
move: Hle; rewrite /Int.I.Fle.
case Hcmp: (F.cmp a b) => // _.
- move => /F_realP Hreala /F_realP Hrealb.
  move: Hcmp.
  rewrite F.cmp_correct Fcmp_correct /Xcmp.
  rewrite /I.convert_bound in Hreala.
  rewrite /I.convert_bound in Hrealb.
  rewrite Hreala Hrealb.
  case Hcomp : (Rcompare (toR a) (toR b)) => // _ Hab.
  by have Habs := (Rcompare_not_Gt (toR a) (toR b) Hab).
- move => /F_realP Hreala /F_realP Hrealb.
  move: Hcmp.
  rewrite F.cmp_correct Fcmp_correct /Xcmp.
  rewrite /I.convert_bound in Hreala.
  rewrite /I.convert_bound in Hrealb.
  rewrite Hreala Hrealb.
  by case: (Rcompare (toR a) (toR b)).
Qed.

Lemma Req_Fle a b :
  F.real a ->
  F.real b ->
  toR a = toR b ->
  Int.I.Fle a b.
Proof.
move => Hareal Hbreal Heq.
apply: Rle_Fle => // .
by apply: Req_le_sym.
Qed.


Lemma Fle_rev a b :
  F.real a -> F.real b -> Fle a b = false -> Fle b a = true.
Proof.
move => Hareal Hbreal Hfalse.
rewrite /Fle /Int.I.Fle F.cmp_correct Fcmp_correct.
move/F_realP : Hareal. move /F_realP : Hbreal.
rewrite /I.convert_bound => Hbreal Hareal.
rewrite Hareal Hbreal /Xcmp.
case Hcomp : (Rcompare (toR b) (toR a)) => // .
have Hleba := Rlt_le _ _ (Rcompare_Gt_inv (toR b) (toR a) Hcomp).
move/F_realP in Hareal. move/F_realP in Hbreal.
have := Rle_Fle a b Hareal Hbreal Hleba.
have -> : Int.I.Fle = Fle by []. (* ?? *)
by rewrite Hfalse.
Qed.

Lemma Fle_eq a b :
  F.real a -> F.real b -> Fle a b = true -> Fle b a = true -> toR a = toR b.
Proof.
move => Hareal Hbreal Htrue.
case Hba : (Fle b a) => // .
have := (Fle_Rle a b Hareal Hbreal Htrue).
have :=(Fle_Rle b a Hbreal Hareal Hba).
move => Hlbz Hlab _.
by apply: Rle_antisym.
Qed.

Lemma Fle_Rlt_Inv a b :
  F.real a -> F.real b -> (toR a > toR b) -> Fle a b = false.
Proof.
move => Hareal Hbreal Hgt.
case Hab: (Fle a b) => // .
have Hge := (Rlt_le _ _ Hgt).
have := (Rle_Fle b a Hbreal Hareal Hge) => Hba.
have := Fle_eq a b Hareal Hbreal Hab Hba => Habs.
rewrite Habs in Hgt.
elim (Rlt_irrefl _ Hgt).
Qed.

Lemma FcmpCancelRight beta dummy : Fcmp dummy (@Fnan beta) = Xund.
Proof.
case: dummy => // .
by move => b p z; case: b.
Qed.

Let integral_float_absolute_signed := integral_float_absolute_signed (estimator).

Lemma integral_float_absolute_signed_correct (depth : nat) (a b : F.type) epsilon :
  ex_RInt f (toR a) (toR b) ->
  (F.real a) -> (F.real b) ->
  contains (I.convert (integral_float_absolute_signed depth a b epsilon)) (Xreal (RInt f (toR a) (toR b))).
Proof.
rewrite /integral_float_absolute_signed /IntervalIntegral.integral_float_absolute_signed.
case (Rle_dec (toR a) (toR b)) => Hab Hintf Hreala Hrealb.
- have -> : Fle a b = true by apply: Rle_Fle.
  exact: integral_float_relative_correct.
- have -> : Fle a b = false.
    apply: Fle_Rlt_Inv => // .
    by apply Rnot_le_gt.
rewrite -RInt_swap Xreal_neg.
apply: I.neg_correct.
apply: integral_float_relative_correct.
+ exact: ex_RInt_swap.
+ apply: Rlt_le; exact: Rnot_le_gt.
Qed.

Lemma all_integrals_correct_leq (ia ib: I.type) (a b : R) :
  a <= b ->
  contains (I.convert ia) (Xreal a) ->
  contains (I.convert ib) (Xreal b) ->
  ex_RInt f a b ->
  contains (I.convert (all_integrals ia ib)) (Xreal (RInt f a b)).
Proof.
move => Hleab Hcont1 Hcont2 Hfint.
rewrite /all_integrals.
case elu: (iF (I.join ia ib)) => // [l u].
set Iab := RInt _ _ _.
have Hjoina : contains (I.convert (I.join ia ib)) (Xreal a).
  by apply: I.join_correct; left.
have Hjoinb : contains (I.convert (I.join ia ib)) (Xreal b).
  by apply: I.join_correct; right.
case: (Rle_lt_or_eq_dec _ _ Hleab) => [Hleab1 | Heqab]; last first.
  + have -> : Xreal Iab = Xmul (g (Xreal a)) (Xsub (Xreal b) (Xreal a)).
      rewrite /Iab Heqab /= RInt_point; congr Xreal; ring.
    apply: I.mul_correct; last by apply: I.sub_correct.
    by rewrite -elu; apply: HiFIntExt.
  + have -> : Xreal Iab = Xmul (Xreal (Iab / (b - a))) (Xreal (b - a)).
       rewrite Xmul_Xreal; congr Xreal; field.
       by apply: Rminus_eq_contra; apply: Rlt_dichotomy_converse; right.
    apply: I.mul_correct; last first.
    - rewrite -[Xreal (b - a)]/(Xsub (Xreal b) (Xreal a)). (* 1 *)
      by apply: I.sub_correct.
      (* try and show l * (b - a) <= int <= u * (b - a) instead *)
    - apply: XRInt1_correct => // x hx; rewrite -elu -[Xreal _]/(g (Xreal x)).
      apply: HiFIntExt.
      + apply (contains_connected _ a b) => // .
        split.
        * by move : hx => [] Hltax _; apply: Rlt_le.
        * by move : hx => [] _ Hltxb; apply: Rlt_le.
Qed.

Notation XRInt := (fun f a b => Xreal (RInt f a b)).

Lemma foo :
  forall a b,
  match Xcmp a b with Xeq | Xlt => a <> Xnan /\ b <> Xnan /\ proj_val a <= proj_val b | _ => True end.
Proof.
move => [|a] [|b] //=.
case: Rcompare_spec => // H.
repeat split => //.
exact: Rlt_le.
repeat split => //.
rewrite H.
apply Rle_refl.
Qed.

Lemma toX_toF_Freal a : FtoX (F.toF a) <> Xnan -> F.real a.
Proof.
move: (F.real_correct a).
  by case: (F.toF a).
Qed.

Let integral_intBounds_epsilon := integral_intBounds_epsilon (estimator).

Lemma integral_epsilon_correct (depth : nat) (a b : R) (ia ib : I.type) epsilon :
  contains (I.convert ia) (Xreal a) ->
  contains (I.convert ib) (Xreal b) ->
  ex_RInt f a b ->
  contains
    (I.convert (integral_intBounds_epsilon depth ia ib epsilon))
    (Xreal (RInt f a b)).
Proof.
move => Hconta Hcontb HFInt.
case Ha : ia Hconta => // [la ua] Hconta.
case Hb : ib Hcontb => // [lb ub] Hcontb.
rewrite /integral_intBounds_epsilon /IntervalIntegral.integral_intBounds_epsilon.
rewrite F.cmp_correct.
rewrite Interval_generic_proof.Fcmp_correct.
suff H: (FtoX (F.toF ua) <> Xnan /\
FtoX (F.toF lb) <> Xnan /\
proj_val (FtoX (F.toF ua)) <= proj_val (FtoX (F.toF lb)) ->
contains
  (I.convert
     (I.add prec
        (I.add prec (all_integrals (Ibnd la ua) (thin ua))
           (integral_float_absolute_signed depth ua lb epsilon))
        (all_integrals (thin lb) (Ibnd lb ub)))) (Xreal (RInt f a b))).
generalize (foo (FtoX (F.toF ua)) (FtoX (F.toF lb))).
now case Xcmp.
intros [Hua [Hlb Hualb]].
have Haua: (a <= toR ua).
  generalize (proj2 Hconta).
  unfold I.convert_bound, toR.
  by destruct FtoX.
have Hlbb : (toR lb <= b).
  generalize (proj1 Hcontb).
  unfold I.convert_bound, toR.
  by destruct (FtoX (F.toF lb)).
have Hfint_a_lb : ex_RInt f a (toR lb).
  apply: (ex_RInt_Chasles_1 _ _ _ b) HFInt.
  split => //.
  now apply Rle_trans with (1 := Haua).
have Hfint_ua_lb : ex_RInt f (toR ua) (toR lb).
apply: (ex_RInt_Chasles_2 _ a) Hfint_a_lb.
by split.
have -> : Xreal (RInt f a b) =
        Xadd
          (Xadd (XRInt f a (toR ua)) (XRInt f (toR ua) (toR lb)))
          (XRInt f (toR lb) b).
     rewrite /= 2?RInt_Chasles //.
     apply: (ex_RInt_Chasles_2 _ a) => //.
     split => //.
     now apply Rle_trans with (1 := Haua).
     apply: ex_RInt_Chasles_1 Hfint_a_lb.
     by split.
   apply: I.add_correct.
   + apply: I.add_correct.
     * apply: all_integrals_correct_leq => // .
       generalize (thin_correct ua).
       unfold I.convert_bound, toR.
       by destruct FtoX.
       apply: ex_RInt_Chasles_1 Hfint_a_lb.
       by split.
     * apply: integral_float_absolute_signed_correct => // ; apply: toX_toF_Freal => // .
   + apply: (all_integrals_correct_leq _ _ (toR lb) b) => //.
     generalize (thin_correct lb).
     unfold I.convert_bound, toR.
     by destruct (FtoX (F.toF lb)).
     apply: (ex_RInt_Chasles_2 _ a) => //.
     split => //.
     now apply Rle_trans with (1 := Haua).
Qed.

End Proofs.

End IntervalIntegral.

End IntegralTactic.
