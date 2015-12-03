Require Import Reals.
Require Import List.
Require Import Coquelicot.
Require Import Interval_xreal.
Require Import Interval_float_sig.
Require Import Interval_interval.
Require Import Interval_interval_float.
Require Import ssreflect ssrfun ssrbool.
Require Import xreal_ssr_compat.
Require Import Interval_transcend.
Require Import Interval_missing.
Require Import integrability.
(* Require Import Interval_generic_proof Interval_generic Interval_xreal Fcore_Raux. *)

Module IntegralTactic (F : FloatOps with Definition even_radix := true).

Module I := FloatInterval F.
Module T := TranscendentalFloatFast F.
Module Integrability := Integrability F.

Section IntervalIntegral.

Section ExtraCoquelicot. (* to be moved eventually *)
Section Integrability.

Variables (V : CompleteNormedModule R_AbsRing) (g : R -> V) (a b c d : R).

Lemma ex_RInt_Chasles_sub :
 a <= b -> b <= c -> c <= d -> ex_RInt g a d -> ex_RInt g b c.
Proof.
move=> leab lebc lecd hiad; apply: (ex_RInt_Chasles_1 _ _ _ d) => //.
by apply: (ex_RInt_Chasles_2 _ a) => //; split=> //; apply: (Rle_trans _ c).
Qed.

End Integrability.


(* Below : a couple of helper lemmas about maj/min of integrals *)
(* We should probably also add the more general case of ra <= rb *)
Section IntegralEstimation.

Variables (f : R -> R) (ra rb : R).

Hypothesis ltab : ra < rb.

Hypothesis fint : ex_RInt f ra rb.

Lemma RInt_le_r (u : R) :
 (forall x : R, ra < x < rb -> f x <= u) -> RInt f ra rb / (rb - ra) <= u.
Proof.
move=> hfu; apply/Rle_div_l;first by apply: Rgt_minus.
have -> : u * (rb - ra) = RInt (fun _ => u) ra rb.
  by rewrite RInt_const Rmult_comm.
apply: RInt_le => //; first exact: Rlt_le.
exact: ex_RInt_const.
Qed.

Lemma RInt_le_l (l : R) :
  (forall x : R, ra < x < rb -> l <= f x) -> l <= RInt f ra rb / (rb - ra).
Proof.
move=> hfl; apply/Rle_div_r; first by apply: Rgt_minus.
have -> : l * (rb - ra) = RInt (fun _ => l) ra rb.
  by rewrite RInt_const Rmult_comm.
apply: RInt_le => //; first exact: Rlt_le.
exact: ex_RInt_const.
Qed.

End IntegralEstimation.
End ExtraCoquelicot.



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
- by apply: RInt_le_r => // x /hif [].
- by apply: RInt_le_l => // x /hif [].
- by apply: RInt_le_l => // x /hif [].
- by apply: RInt_le_r => // x /hif [].
Qed.

End XRInt.


Section ExtraFloats.
Lemma F_realP (fl : F.type) :
 reflect (I.convert_bound fl = Xreal (T.toR fl)) (F.real fl).
Proof.
have := (F.real_correct fl); rewrite /I.convert_bound /T.toR.
by case: (F.toF fl)=> [||y z t] ->; constructor.
Qed.

Lemma contains_convert_bnd_l (a b : F.type) :  (F.real a) -> (F.real b) ->
  (T.toR a) <= (T.toR b) -> contains (I.convert (I.bnd a b)) (I.convert_bound a).
Proof.
move/F_realP => hra /F_realP hrb hleab; rewrite hra; apply: le_contains.
  by rewrite hra; apply: le_lower_refl.
by rewrite hrb.
Qed.

Lemma contains_convert_bnd_r (a b : F.type) :  (F.real a) -> (F.real b) ->
  (T.toR a) <= (T.toR b) -> contains (I.convert (I.bnd a b)) (I.convert_bound b).
Proof.
move/F_realP => hra /F_realP hrb hleab; rewrite hrb; apply: le_contains.
  rewrite hra /le_lower /=; exact: Ropp_le_contravar.
rewrite hrb; exact: le_upper_refl.
Qed.

Lemma contains_convert_bnd (a b : F.type) r :  (F.real a) -> (F.real b) ->
  (T.toR a) <= r <= (T.toR b) -> contains (I.convert (I.bnd a b)) (Xreal r).
Proof.
move/F_realP => hra /F_realP hrb hleab; apply: le_contains.
  by rewrite hra /le_lower /=; apply: Ropp_le_contravar; case: hleab.
by rewrite hrb /le_lower /=; case: hleab.
Qed.

(* Remember : T.toR = fun x : F.type => proj_val (FtoX (F.toF x)) *)
(* The statement of I.midpoint_correct is really clumsy *)
(* contains_le is also difficult to use... *)
(* I.midpoint_correct should be stated using T.toR *)
(* le_lower should either be a notation over le_upper or a new def *)
(* so that it simplifies to <= or else provide suitable lemmas *)
Lemma midpoint_bnd_in (a b : F.type) :
  F.real a -> F.real b -> T.toR a <= T.toR b->
  T.toR a <= T.toR (I.midpoint (I.bnd a b)) <= T.toR b.
Proof.
move => hra hrb hleab; set iab := I.bnd a b; set m := I.midpoint iab.
pose xa := I.convert_bound a; pose xb := I.convert_bound b.
have non_empty_iab : exists x : ExtendedR, contains (I.convert iab) x.
  by exists xa; apply: contains_convert_bnd_l.
have [isr_xm xm_in_iab {non_empty_iab}] := I.midpoint_correct iab non_empty_iab.
rewrite -/(T.toR m) in isr_xm. (* I.midpoint_correct is ill stated *)
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
  (F.real fl) -> contains (I.convert (thin fl)) (Xreal (T.toR fl)).
Proof. move/F_realP<-; exact: thin_correct. Qed.

End ExtraFloats.



(* A fixed precision *)
Variable prec : F.precision.

Variables (f : R -> R) (iF : I.type -> I.type).

(* This is a std monadic operation. Does it exist somewhere in the libs? *)
Let g := toXreal_fun f.

(* g is a restriction of f as an extendedR function. *)
Let Hfgext := xreal_extension_toXreal_fun f.


Hypothesis HiFIntExt : forall xi x, contains (I.convert xi) (Xreal x) -> contains (I.convert (iF xi)) (Xreal (f x)).

Section OrderOne.

Variables (a b : F.type).

(* f is integrable on [a, b]*)
Hypothesis Hintegrable : ex_RInt f (T.toR a) (T.toR b).

(* a <= b *)
Hypothesis  Hleab : T.toR a <= T.toR b.

(* a and b are no Nan. This cannot be deduced from Hleab *)
Hypothesis ha : F.real a.
Hypothesis hb : F.real b.

Lemma integral_order_one_correct :
  contains
    (I.convert ((I.mul prec (iF (I.bnd a b)) (I.sub prec (thin b) (thin a)))))
    (Xreal (RInt f (T.toR a) (T.toR b))).
Proof.
case elu: (iF (I.bnd a b)) => // [l u].
set ra := T.toR a; set rb := T.toR b; fold ra rb in Hintegrable, ha, hb, Hleab.
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

Fixpoint integral_float (depth : nat) (a b : F.type) :=
  let int := I.bnd a b in
  match depth with
    | O => I.mul prec (iF int) (I.sub prec (thin b) (thin a))
    | S n => let m := I.midpoint int in
             let i1 := integral_float n a m in
             let i2 := integral_float n m b in
             I.add prec i1 i2
  end.

Definition integral_float_signed (depth : nat) (a b : F.type) :=
  match F.cmp a b with
    | Xgt => I.neg (integral_float depth b a)
    | _ => integral_float depth a b
  end.

Lemma integral_float_correct (depth : nat) (a b : F.type) :
  ex_RInt f (T.toR a) (T.toR b) ->
  T.toR a <= T.toR b ->
  (F.real a) -> (F.real b) ->
  contains (I.convert (integral_float depth a b)) (Xreal (RInt f (T.toR a) (T.toR b))).
Proof.
elim: depth a b => [ | k Hk] a b Hintegrable Hleab ha hb.
  by apply: integral_order_one_correct => //.
set midpoint := I.midpoint (I.bnd a b).
have hIl : ex_RInt f (T.toR a) (T.toR midpoint).
  by apply:  (ex_RInt_Chasles_1 _ _ _ (T.toR b)) => //; apply: midpoint_bnd_in.
have hIr : ex_RInt f (T.toR midpoint) (T.toR b).
  by apply:  (ex_RInt_Chasles_2 f (T.toR a))=> //; apply: midpoint_bnd_in.
have -> : RInt f (T.toR a) (T.toR b) =
  RInt f (T.toR a) (T.toR midpoint) + RInt f (T.toR midpoint) (T.toR b).
  by rewrite RInt_Chasles.
set I1 := RInt _ _ _; set I2 := RInt _ _ _.
rewrite /integral_float -/integral_float -[Xreal (_ + _)]/(Xadd (Xreal I1) (Xreal I2)).
have [in1 in2] := midpoint_bnd_in a b ha hb Hleab.
suff hm : F.real (I.midpoint (I.bnd a b)) by apply: I.add_correct; apply: Hk.
  suff /I.midpoint_correct []:
    exists x : ExtendedR, contains (I.convert (I.bnd a b)) x by move/F_realP.
  exists (I.convert_bound a); apply: contains_convert_bnd_l => //; exact/F_realP.
Qed.

Require Import Interval_generic.

(* This proof seems much too complicated *)
Lemma RgtToFcmp a b :
F.real a -> F.real b -> T.toR a > T.toR b -> F.cmp a b = Xgt.
Proof.
move => Hreala Hrealb Hgtab.
rewrite F.cmp_correct Interval_generic_proof.Fcmp_correct.
rewrite /T.toR /proj_val in Hgtab.
move: Hgtab. About F.real_correct.
move: (F.real_correct a).
rewrite Hreala.
case Ha1 : (F.toF a) => [||bb pp zz] // _ .
- move: (F.real_correct b).
  rewrite Hrealb.
  case Hb1 : (F.toF b)=> [||bb1 pp1 zz1] //= _; first by move/Rgt_irrefl.
  + by move => ?; rewrite Rcompare_Gt.
- rewrite /FtoX /Xcmp.
  move: (F.real_correct b).
  rewrite Hrealb.
  case Hb1 : (F.toF b) => [||bb1 pp1 zz1] // _ ;
  rewrite /FtoX;move => Hgt; by rewrite Rcompare_Gt.
Qed.

Lemma RltToFcmp a b :
F.real a -> F.real b -> T.toR a < T.toR b -> F.cmp a b = Xlt.
Proof.
move => Hreala Hrealb Hgtba.
suff: F.cmp b a = Xgt.
(* move => Hgt. *)
rewrite !F.cmp_correct !Interval_generic_proof.Fcmp_correct.
case: (FtoX (F.toF b)); case: (FtoX (F.toF a)) => // r1 r2.
rewrite /Xcmp.
Search _ Rcompare.
rewrite Rcompare_sym.
by case: (Rcompare r1 r2).
apply: RgtToFcmp => //.
Qed.

(* again, way too complicated *)
Lemma ReqToFcmp a b :
F.real a -> F.real b -> T.toR a = T.toR b -> F.cmp a b = Xeq.
Proof.
move => Hreala Hrealb Hgtab.
rewrite F.cmp_correct Interval_generic_proof.Fcmp_correct.
rewrite /T.toR /proj_val in Hgtab.
move: Hgtab.
move: (F.real_correct a).
rewrite Hreala.
case Ha1 : (F.toF a) => [||bb pp zz] // _ .
- move: (F.real_correct b).
  rewrite Hrealb.
  case Hb1 : (F.toF b) => [||bb1 pp1 zz1] // _.
  + by rewrite /FtoX /= Rcompare_Eq.
  + rewrite /FtoX /Xcmp.
    by move => Heq; rewrite Rcompare_Eq.
- rewrite /FtoX /Xcmp.
  move: (F.real_correct b).
  rewrite Hrealb.
  by case Hb1 : (F.toF b) => [||bb1 pp1 zz1] // _  => Heq;
  rewrite Rcompare_Eq.
Qed.

Lemma integral_float_signed_correct_neg (depth : nat) (a b : F.type) :
  ex_RInt f (T.toR a) (T.toR b) ->
  T.toR a > T.toR b ->
  (F.real a) -> (F.real b) ->
  contains (I.convert (integral_float_signed depth a b))
           (Xreal (RInt f (T.toR a) (T.toR b))).
Proof.
move => Hfint Hgeab HaR HbR.
rewrite /integral_float_signed.
have -> : F.cmp a b = Xgt. (* rewrite F.cmp_correct. *)
(* rewrite Interval_generic_proof.Fcmp_correct. *)
  apply: RgtToFcmp => //.
rewrite -RInt_swap.
set it := (RInt _ _ _).
have -> : Xreal (- it) = Xneg (Xreal it) by [].
set It := integral_float _ _ _.
suff: contains (I.convert It) (Xreal it).
  by apply: I.neg_correct.
apply: integral_float_correct => //.
  by apply: ex_RInt_swap.
by apply: Rlt_le.
Qed.

Lemma integral_float_signed_correct (depth : nat) (a b : F.type) :
  ex_RInt f (T.toR a) (T.toR b) ->
  (F.real a) -> (F.real b) ->
  contains (I.convert (integral_float_signed depth a b)) (Xreal (RInt f (T.toR a) (T.toR b))).
Proof.
case (Rle_dec (T.toR a) (T.toR b)) => Hab Hintf Hreala Hrealb.
- rewrite /integral_float_signed.
  case (Rle_lt_or_eq_dec (T.toR a) (T.toR b)) => // [Hlt|Hle].
    + have -> : F.cmp a b = Xlt by apply: RltToFcmp.
      exact: integral_float_correct.
    + have -> : F.cmp a b = Xeq by apply: ReqToFcmp.
      exact: integral_float_correct.
by apply: integral_float_signed_correct_neg => //; apply: Rnot_le_lt.
Qed.

(* using F.sub instead? *)
Definition diam x :=
  match x with
    | Inan => F.nan
    | Ibnd a b => F.sub_exact b a
  end.

Definition all_integrals (ia ib : I.type) :=
I.mul prec (iF (I.join ia ib)) (I.sub prec ib ia).

Lemma all_integrals_correct_leq (ia ib: I.type) (a b : R) :
  (a <= b) ->
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
    (* rewrite -elu; apply: HiFIntExt;  move/F_realP: ha<-. *)
    (* by apply: contains_convert_bnd_l. *)
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

Lemma all_integrals_correct_lt_swap (ia ib: I.type) (a b : R) :
  (b < a) ->
  contains (I.convert ia) (Xreal a) ->
  contains (I.convert ib) (Xreal b) ->
  ex_RInt f a b ->
  contains (I.convert (all_integrals ia ib)) (Xreal (RInt f a b)).
Proof.
(* for now it is impossible to prove this because we don't know that I.join is symmetrical*)
Admitted.

Lemma all_integrals_correct (ia ib: I.type) (a b : R) :
  contains (I.convert ia) (Xreal a) ->
  contains (I.convert ib) (Xreal b) ->
  ex_RInt f a b ->
  contains (I.convert (all_integrals ia ib)) (Xreal (RInt f a b)).
Proof.
move: (Rle_dec a b).
case => [Hleab | Hltba].
move: Hleab.
by apply: all_integrals_correct_leq.
apply: all_integrals_correct_lt_swap.
Search _ (~ _ <= _).
by apply: Rnot_le_lt.
Qed.

Notation XRInt := (fun f a b => Xreal (RInt f a b)).

Definition integral_intBounds depth (i1 i2 : I.type) :=
  if i1 is Ibnd a1 b1 then
    if i2 is Ibnd a2 b2 then
      match F.cmp b1 a2 with
        | Xeq | Xlt =>
                let si1 := all_integrals i1 (thin b1) in
                let si2 := all_integrals (thin a2) i2 in
                I.add prec
                      (I.add prec si1 (integral_float_signed depth b1 a2)) si2
        | _ => Inan end
    else
      Inan
  else
    Inan.

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

(* Import Integrability. (* for contains_eval *) *)

Lemma toX_toF_Freal a : (FtoX (F.toF a) <> Xnan) -> F.real a.
Proof.
move: (F.real_correct a).
  by case: (F.toF a).
Qed.


Lemma integral_correct (depth : nat) (a b : R) (ia ib : I.type):
  contains (I.convert ia) (Xreal a) ->
  contains (I.convert ib) (Xreal b) ->
  ex_RInt f a b ->
  contains
    (I.convert (integral_intBounds depth ia ib))
    (Xreal (RInt f a b)).
Proof.
move => Hconta Hcontb HFInt.
case Ha : ia Hconta => // [la ua] Hconta.
case Hb : ib Hcontb => // [lb ub] Hcontb.
unfold integral_intBounds.
rewrite F.cmp_correct.
rewrite Interval_generic_proof.Fcmp_correct.
suff H: (FtoX (F.toF ua) <> Xnan /\
FtoX (F.toF lb) <> Xnan /\
proj_val (FtoX (F.toF ua)) <= proj_val (FtoX (F.toF lb)) ->
contains
  (I.convert
     (I.add prec
        (I.add prec (all_integrals (Ibnd la ua) (thin ua))
           (integral_float_signed depth ua lb))
        (all_integrals (thin lb) (Ibnd lb ub)))) (Xreal (RInt f a b))).
generalize (foo (FtoX (F.toF ua)) (FtoX (F.toF lb))).
now case Xcmp.
intros [Hua [Hlb Hualb]].
have Haua: (a <= T.toR ua).
  generalize (proj2 Hconta).
  unfold I.convert_bound, T.toR.
  by destruct FtoX.
have Hlbb : (T.toR lb <= b).
  generalize (proj1 Hcontb).
  unfold I.convert_bound, T.toR.
  by destruct (FtoX (F.toF lb)).
have Hfint_a_lb : ex_RInt f a (T.toR lb).
  apply: (ex_RInt_Chasles_1 _ _ _ b) HFInt.
  split => //.
  now apply Rle_trans with (1 := Haua).
have Hfint_ua_lb : ex_RInt f (T.toR ua) (T.toR lb).
apply: (ex_RInt_Chasles_2 _ a) Hfint_a_lb.
by split.
have -> : Xreal (RInt f a b) =
        Xadd
          (Xadd (XRInt f a (T.toR ua)) (XRInt f (T.toR ua) (T.toR lb)))
          (XRInt f (T.toR lb) b).
     rewrite /= 2?RInt_Chasles //.
     apply: (ex_RInt_Chasles_2 _ a) => //.
     split => //.
     now apply Rle_trans with (1 := Haua).
     apply: ex_RInt_Chasles_1 Hfint_a_lb.
     by split.
   apply: I.add_correct.
   + apply: I.add_correct.
     * apply: (all_integrals_correct _ _ a (T.toR ua)) => //.
       generalize (thin_correct ua).
       unfold I.convert_bound, T.toR.
       by destruct FtoX.
       apply: ex_RInt_Chasles_1 Hfint_a_lb.
       by split.
     * apply: integral_float_signed_correct => // ; apply: toX_toF_Freal => // .
   + apply: (all_integrals_correct _ _ (T.toR lb) b) => //.
     generalize (thin_correct lb).
     unfold I.convert_bound, T.toR.
     by destruct (FtoX (F.toF lb)).
     apply: (ex_RInt_Chasles_2 _ a) => //.
     split => //.
     now apply Rle_trans with (1 := Haua).
Qed.

End IntervalIntegral.

End IntegralTactic.

