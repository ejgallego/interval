Require Import Reals.
Require Import List.
Require Import Coquelicot.
Require Import Interval_xreal.
Require Import Interval_float_sig.
Require Import Interval_float_ext.
Require Import Interval_interval.
Require Import Interval_interval_float.
Require Import Ssreflect.ssreflect Ssreflect.ssrfun Ssreflect.ssrbool.
Require Import xreal_ssr_compat.
Require Import Interval_missing.
Require Import Coquelicot coquelicot_compl.
Require Import Interval_generic.
Require Import Interval.Interval_generic_proof.

Require Import interval_compl.

Module ExtraFloats (F : FloatOps with Definition even_radix := true).
Module I := FloatInterval F.

Definition toR x := proj_val (F.toX x).

Lemma F_realP (fl : F.type) :
 reflect (F.toX fl = Xreal (toR fl)) (F.real fl).
Proof.
have := (F.real_correct fl); rewrite /I.convert_bound /toR.
rewrite <- F.toF_correct.
by case: (F.toF fl)=> [||y z t] ->; constructor.
Qed.

Lemma contains_convert_bnd_l (a b : F.type) : F.real a ->
  toR a <= toR b -> contains (I.convert (I.bnd a b)) (F.toX a).
Proof.
rewrite F.real_correct /toR /I.convert /=.
case: F.toX => //= r _ H.
split.
apply Rle_refl.
now destruct F.toX.
Qed.

Lemma contains_convert_bnd_r (a b : F.type) : F.real b ->
  toR a <= toR b -> contains (I.convert (I.bnd a b)) (F.toX b).
Proof.
rewrite F.real_correct /toR /I.convert /=.
case: F.toX => //= r _ H.
split.
now destruct F.toX.
apply Rle_refl.
Qed.

Lemma contains_convert_bnd (a b : F.type) r :  F.real a -> F.real b ->
  toR a <= r <= toR b -> contains (I.convert (I.bnd a b)) (Xreal r).
Proof.
rewrite 2!F.real_correct /toR /I.convert /=.
case: F.toX => //= ra _.
by case: F.toX.
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
split; last by move: le_xm_xb; rewrite isr_xm /xb /I.convert_bound (F_realP _ hrb).
move: le_xa_xm.
by rewrite isr_xm /xa /I.convert_bound (F_realP _ hra) /le_lower /=; exact: Ropp_le_cancel.
Qed.

Definition thin (f : F.type) : I.type :=
  if F.real f then I.bnd f f else I.nai.

Lemma thin_correct (fl : F.type) :
 contains (I.convert (thin fl)) (F.toX fl).
Proof.
rewrite /thin F.real_correct /I.convert_bound.
case ex: (F.toX fl) => [|r] //=.
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
Module F' := FloatExt F.
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

Definition naive_integral_float :=
  I.mul prec (iF (I.bnd a b)) (I.sub prec (thin b) (thin a)).

Lemma naive_integral_float_correct :
  contains
    (I.convert (naive_integral_float))
    (Xreal (RInt f (toR a) (toR b))).
Proof.
rewrite /naive_integral_float.
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
             match F'.le (diam roughEstimate_1) halfeps, F'.le (diam roughEstimate_2) halfeps with
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
      if F'.le (diam roughEst) epsilon then roughEst
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
  match F'.le (diam roughEstimate_1) halfeps, F'.le (diam roughEstimate_2) halfeps with
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
  match F'.le a b with
    | false => I.neg (integral_float_relative depth b a epsilon)
    | true => integral_float_relative depth a b epsilon
  end.

Definition naive_integral (ia ib : I.type) :=
  I.mul prec (iF (I.join ia ib)) (I.sub prec ib ia).

Definition integral_intBounds_epsilon depth (i1 i2 : I.type) epsilon :=
  if i1 is Ibnd a1 b1 then
    if i2 is Ibnd a2 b2 then
      if F'.le b1 a2 then
        let si1 := naive_integral i1 (thin b1) in
        let si2 := naive_integral (thin a2) i2 in
        I.add prec (I.add prec si1 (integral_float_absolute_signed depth b1 a2 epsilon)) si2
      else Inan
    else
      Inan
  else
    Inan.


End Functions.

Section Proofs.

Variable estimator : F.type -> F.type -> I.type.

Hypothesis Hcorrect : integralEstimatorCorrect estimator.

Let notInan fi :=
  match I.convert fi with
  | Interval_interval.Inan => false
  | _ => true
  end = true.

Definition ex_RInt_base_case :=
  forall u0 l1,
  F.real u0 ->
  F.real l1 ->
  toR u0 <= toR l1 ->
  notInan (estimator u0 l1) ->
  ex_RInt f (toR u0) (toR l1).

Lemma integral_ex_RInt_aux u0 l1 :
  F'.le u0 l1 ->
  F.real u0 /\ F.real l1 /\ toR u0 <= toR l1.
Proof.
  rewrite 2!F.real_correct.
  move /F'.le_correct => H.
  unfold toR.
  destruct F.toX ; try easy.
  by destruct F.toX.
Qed.

Lemma integral_float_absolute_ex_RInt (depth : nat) u0 l1 epsilon :
  ex_RInt_base_case ->
  notInan (integral_float_absolute estimator depth u0 l1 epsilon) ->
  F'.le u0 l1 ->
  ex_RInt f (toR u0) (toR l1).
Proof.
move => ex_RInt_base_case HnotInan Hleu0l1.
have [Hrealu0 [Hreall1 Hleu0ml1]] := integral_ex_RInt_aux _ _ Hleu0l1.
elim: depth u0 l1 epsilon Hreall1 Hrealu0 HnotInan {Hleu0l1} Hleu0ml1 => [|d HId] u0 l1 epsilon Hreall1 Hrealu0 HnotInan Hleu0ml1.
- pose m := I.midpoint (I.bnd u0 l1).
  have Hrealm : (F.real m).
    suff: F.toX m = Xreal (toR m).
    by rewrite F.real_correct => ->.
  have := (I.midpoint_correct (I.bnd u0 l1)).
    + case.
      exists (Xreal (toR u0)).
      move: (contains_convert_bnd_l u0 l1 Hrealu0 Hleu0ml1).
      by move/F_realP :Hrealu0 => -> .
    + by [].
  (* first we establish a useful inequality on u0, m and l1 *)
  have := (midpoint_bnd_in u0 l1 Hrealu0 Hreall1 Hleu0ml1).
  rewrite -[I.midpoint _]/m.
  move => [Hleu0m Hleml1].
  apply: (ex_RInt_Chasles _ _ (toR m)).
    + apply: ex_RInt_base_case => //.
      by move: HnotInan; rewrite /integral_float_absolute; case: (estimator u0 m).
    + apply: ex_RInt_base_case => //.
      move: HnotInan; rewrite /integral_float_absolute.
      by case: (estimator m l1); case: estimator.
- pose m := I.midpoint (I.bnd u0 l1).
  have Hrealm : (F.real m).
    suff: F.toX m = Xreal (toR m).
      by move/F_realP.
    have := (I.midpoint_correct (I.bnd u0 l1)).
      case.
      exists (Xreal (toR u0)).
      move: (contains_convert_bnd_l u0 l1 Hrealu0 Hleu0ml1).
      by move/F_realP :Hrealu0 => ->.
    by [].
  (* first we establish a useful inequality on u0, m and l1 *)
  have := (midpoint_bnd_in u0 l1 Hrealu0 Hreall1 Hleu0ml1).
  rewrite -[I.midpoint _]/m.
  move => [Hleu0m Hleml1].
  apply: (ex_RInt_Chasles _ _ (toR m)).
  + move: HnotInan.
    rewrite integral_float_absolute_Sn -[I.midpoint _]/m.
    set b1 := (X in (if X then _ else _)).
    set b2 := (X in (if X then (I.add prec _ _) else _)).
    case Hb1 : b1.
    * by case Hb2 : b2; move => HnotInan;
      apply: (ex_RInt_base_case) => //;
      move: HnotInan; case:(estimator u0 m).
    * set b3 := (X in (if X then _ else _)).
      case Hb3 : b3.
      - set epsilon' := (F.sub_exact _ _); move => HnotInan.
        apply: (HId u0 m epsilon') => //.
        move: HnotInan.
        by case: integral_float_absolute.
      - set epsilon' := (div2 _); move => HnotInan.
        apply: (HId u0 m epsilon') => //.
        move: HnotInan.
        by case: integral_float_absolute.
  + move: HnotInan.
    rewrite integral_float_absolute_Sn -[I.midpoint _]/m.
    set b1 := (X in (if X then _ else _)).
    set b2 := (X in (if X then (I.add prec _ _) else _)).
    case Hb1 : b1.
    * case Hb2 : b2.
      + move => HnotInan.
        apply: ex_RInt_base_case => //.
      move: HnotInan.
      by case: (estimator m l1); case: (estimator u0 m).
      + set epsilon' := (F.sub_exact _ _); move => HnotInan.
        apply: (HId m l1 epsilon') => //.
        move: HnotInan.
        by case: integral_float_absolute => // ; case: estimator.
    * set b3 := (X in (if X then _ else _)).
      case Hb3 : b3.
      - move => HnotInan; apply: ex_RInt_base_case => //.
        rewrite -/iF.
        move: HnotInan; case: (estimator m l1) => //.
        by case: integral_float_absolute.
      - set epsilon' := (div2 _); move => HnotInan.
        apply: (HId m l1 epsilon') => //.
        move: HnotInan.
        by case: integral_float_absolute => // ; case: integral_float_absolute.
Qed.

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
case Hcmp1 : (F'.le d1 (div2 epsilon)); case Hcmp2 : (F'.le d2 (div2 epsilon));
repeat ((try (apply: I.add_correct => // )); try (apply: Hcorrect => // ); try (apply: Hk => // )).
Qed.

Lemma integral_float_relative_ex_RInt (depth : nat) u0 l1 epsilon :
  ex_RInt_base_case ->
  notInan (integral_float_relative estimator depth u0 l1 epsilon) ->
  F'.le u0 l1 ->
  ex_RInt f (toR u0) (toR l1).
Proof.
move => ex_RInt_base_case HnotInan Hleu0l1.
have [Hrealu0 [Hreall1 Hleu0ml1]] := integral_ex_RInt_aux _ _ Hleu0l1.
move: HnotInan.
rewrite /integral_float_relative.
rewrite Hrealu0 Hreall1.
case: depth => [|depth].
exact: ex_RInt_base_case.
case: F'.le.
- exact: ex_RInt_base_case.
- move => HnotInan.
  exact: integral_float_absolute_ex_RInt HnotInan _.
Qed.

Lemma integral_float_relative_correct (depth : nat) (a b : F.type) epsilon :
  ex_RInt f (toR a) (toR b) ->
  toR a <= toR b ->
  contains (I.convert (integral_float_relative estimator depth a b epsilon)) (Xreal (RInt f (toR a) (toR b))).
Proof.
case Hareal : (F.real a); case Hbreal: (F.real b) => Hfint Hab; case: depth => [|depth] => // ;rewrite /integral_float_relative /IntervalIntegral.integral_float_relative ?Hareal ?Hbreal // .
- by rewrite /=; apply: Hcorrect.
- case: I.bounded; case: F'.le; first by apply: Hcorrect.
  + by apply: integral_float_absolute_correct.
  + by apply: Hcorrect.
  + by apply: integral_float_absolute_correct.
Qed.

Lemma real_correct' :
  forall a, F.real a -> F.toX a = Xreal (toR a).
Proof.
intros a.
rewrite F.real_correct /toR.
now destruct F.toX.
Qed.

Lemma Fle_Rle u0 l1 :
  F.real u0 ->
  F.real l1 ->
  F'.le u0 l1 ->
  toR u0 <= toR l1.
Proof.
move => /F_realP Hrealu0 /F_realP Hreall1.
move: (F'.le_correct u0 l1).
by rewrite Hreall1 Hrealu0.
Qed.

Lemma Rle_Fle a b :
  F.real a ->
  F.real b ->
  toR a <= toR b ->
  F'.le a b.
Proof.
rewrite 2!F.real_correct /toR /F'.le F.cmp_correct.
destruct F.toX. easy.
destruct F.toX. easy.
move => _ _ /=.
case Rcompare_spec => //.
by move /Rlt_not_le.
Qed.

Lemma Fle_rev a b :
  F.real a -> F.real b ->
  F'.le a b = false ->
  F'.le b a = true.
Proof.
rewrite 2!F.real_correct /toR /F'.le 2!F.cmp_correct.
destruct F.toX. easy.
destruct F.toX. easy.
move => _ _ /=.
case Rcompare_spec => // H _.
by rewrite Rcompare_Lt.
Qed.

Lemma Fle_Rgt a b :
  F.real a -> F.real b -> toR b < toR a -> F'.le a b = false.
Proof.
move => Hareal Hbreal Hgt.
case Hab: (F'.le a b) => //.
elim Rlt_not_le with (1 := Hgt).
now apply Fle_Rle.
Qed.

Lemma integral_float_absolute_signed_correct (depth : nat) (a b : F.type) epsilon :
  ex_RInt f (toR a) (toR b) ->
  (F.real a) -> (F.real b) ->
  contains (I.convert (integral_float_absolute_signed estimator depth a b epsilon)) (Xreal (RInt f (toR a) (toR b))).
Proof.
rewrite /integral_float_absolute_signed.
case (Rle_dec (toR a) (toR b)) => Hab Hintf Hreala Hrealb.
- have -> : F'.le a b = true by apply: Rle_Fle.
  exact: integral_float_relative_correct.
- have -> : F'.le a b = false.
    apply: Fle_Rgt => //.
    now apply Rnot_le_lt.
rewrite -RInt_swap Xreal_neg.
apply: I.neg_correct.
apply: integral_float_relative_correct.
+ exact: ex_RInt_swap.
+ apply: Rlt_le; exact: Rnot_le_gt.
Qed.

Lemma naive_integral_correct_leq (ia ib: I.type) (a b : R) :
  a <= b ->
  contains (I.convert ia) (Xreal a) ->
  contains (I.convert ib) (Xreal b) ->
  ex_RInt f a b ->
  contains (I.convert (naive_integral ia ib)) (Xreal (RInt f a b)).
Proof.
move => Hleab Hcont1 Hcont2 Hfint.
rewrite /naive_integral.
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

Lemma toX_toF_Freal a : F.toX a <> Xnan -> F.real a.
Proof.
move: (F.real_correct a).
rewrite -F.toF_correct.
by case: (F.toF a).
Qed.

Lemma integral_epsilon_correct (depth : nat) (a b : R) (ia ib : I.type) epsilon :
  contains (I.convert ia) (Xreal a) ->
  contains (I.convert ib) (Xreal b) ->
  ex_RInt f a b ->
  contains
    (I.convert (integral_intBounds_epsilon estimator depth ia ib epsilon))
    (Xreal (RInt f a b)).
Proof.
move => Hconta Hcontb HFInt.
case Ha : ia Hconta => // [la ua] Hconta.
case Hb : ib Hcontb => // [lb ub] Hcontb.
rewrite /integral_intBounds_epsilon.
case Hle: F'.le. 2: easy.
assert (F.toX ua <> Xnan /\ F.toX lb <> Xnan /\
  proj_val (F.toX ua) <= proj_val (F.toX lb)) as [Hua [Hlb Hualb]].
  generalize (F'.le_correct ua lb).
  destruct F'.le. 2: easy.
  intros H.
  specialize (H eq_refl).
  destruct F.toX. easy.
  destruct F.toX. easy.
  split. easy.
  split ; easy.
have Haua: (a <= toR ua).
  generalize (proj2 Hconta).
  unfold I.convert_bound, toR.
  by destruct F.toX.
have Hlbb : (toR lb <= b).
  generalize (proj1 Hcontb).
  unfold I.convert_bound, toR.
  by destruct (F.toX lb).
have Hfint_a_lb : ex_RInt f a (toR lb).
  apply: (ex_RInt_Chasles_1 _ _ _ b) HFInt.
  split => //.
  now apply Rle_trans with (1 := Haua).
have Hfint_ua_lb : ex_RInt f (toR ua) (toR lb).
apply: (ex_RInt_Chasles_2 _ a) Hfint_a_lb.
by split.
have -> : Xreal (RInt f a b) =
        Xadd
          (Xadd (Xreal (RInt f a (toR ua))) (Xreal (RInt f (toR ua) (toR lb))))
          (Xreal (RInt f (toR lb) b)).
     rewrite /= 2?RInt_Chasles //.
     apply: (ex_RInt_Chasles_2 _ a) => //.
     split => //.
     now apply Rle_trans with (1 := Haua).
     apply: ex_RInt_Chasles_1 Hfint_a_lb.
     by split.
   apply: I.add_correct.
   + apply: I.add_correct.
     * apply: naive_integral_correct_leq => // .
       generalize (thin_correct ua).
       unfold I.convert_bound, toR.
       by destruct F.toX.
       apply: ex_RInt_Chasles_1 Hfint_a_lb.
       by split.
     * apply: integral_float_absolute_signed_correct => // ; apply: toX_toF_Freal => // .
   + apply: (naive_integral_correct_leq _ _ (toR lb) b) => //.
     generalize (thin_correct lb).
     unfold I.convert_bound, toR.
     by destruct (F.toX lb).
     apply: (ex_RInt_Chasles_2 _ a) => //.
     split => //.
     now apply Rle_trans with (1 := Haua).
Qed.

End Proofs.

End IntervalIntegral.

End IntegralTactic.
