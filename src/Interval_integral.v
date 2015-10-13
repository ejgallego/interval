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
(* Require Import Interval_generic_proof Interval_generic Interval_xreal Fcore_Raux. *)

Module IntegralTactic (F : FloatOps with Definition even_radix := true).

Module I := FloatInterval F.
Module T := TranscendentalFloatFast F.

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
  admit.
rewrite -RInt_swap.
set it := (RInt _ _ _).
have -> : Xreal (- it) = Xneg (Xreal it) by [].
set It := integral_float _ _ _.
suff: contains (I.convert It) (Xreal it).
  admit. (* can't find this lemma *)
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
    + have -> : F.cmp a b = Xlt by admit.
      exact: integral_float_correct.
    + have -> : F.cmp a b = Xeq by admit.
      exact: integral_float_correct.
by apply: integral_float_signed_correct_neg => //; apply: Rnot_le_lt.
Qed.

(* using F.sub instead? *)
Definition diam x :=
  match x with
    | Inan => F.nan
    | Ibnd a b => F.sub_exact b a
  end.

(* Definition all_integrals (ia : I.type) := *)
(* I.mul prec (thin (diam ia)) (I.join (I.neg (iF ia)) (iF ia)). *)

(* Lemma all_integrals_correct (ia : I.type) (t1 t2 : R) : *)
(*   (contains (I.convert ia) (Xreal t1)) -> *)
(*   (contains (I.convert ia) (Xreal t2)) -> *)
(*   (contains (I.convert (all_integrals ia)) (Xreal (RInt f t1 t2))). *)
(* Proof. *)
(* move => Hat1 Hat2. *)
(* rewrite /all_integrals. *)
(* wlog : t1 t2 Hat1 Hat2 / t1 <= t2 => Hleq. *)
(* Admitted. *)

(* Definition integral_intBounds depth (a b : I.type) := *)
(*   if a is Ibnd _ b1 then *)
(*     if b is Ibnd a2 _ then *)
(*       let sab := all_integrals a in *)
(*       let scd := all_integrals b in *)
(*       I.add prec (I.add prec sab (integral_float_signed depth b1 a2)) scd *)
(*     else *)
(*       Inan *)
(*   else *)
(*     Inan. *)

Axiom convex_hull :  I.type -> I.type -> I.type.
Axiom convex_hull_correct : forall (ia ib : I.type) (x1 x2 y : R) ,
x1 <= y <= x2 ->
contains (I.convert ia) (Xreal x1) ->
contains (I.convert ib) (Xreal x2) ->
contains (I.convert (convex_hull ia ib)) (Xreal y).

Definition all_integrals (ia ib : I.type) :=
I.mul prec (iF (convex_hull ia ib)) (I.sub prec ib ia).

Lemma all_integrals_correct (ia ib : I.type) (x1 x2 y1 y2 : R) :
  contains (I.convert ia) (Xreal x1) ->
  contains (I.convert ib) (Xreal x2) ->
  ex_RInt f x1 x2 ->
  (x1 <= y1 /\ y1 <= y2 /\ y2 <= x2) ->
  contains (I.convert (all_integrals ia ib)) (Xreal (RInt f y1 y2)).
Proof.
move => Hcont1 Hcont2 Hfint.
Admitted.


Notation XRInt := (fun f a b => Xreal (RInt f a b)).

Definition integral_intBounds depth (ia ib : I.type) :=
  if ia is Ibnd a1 b1 then
    if ib is Ibnd a2 b2 then
      match F.cmp b1 a2 with
        | Xeq | Xlt => let sab := all_integrals (thin a1) (thin b1) in
                       let scd := all_integrals (thin a2) (thin b2) in
                       I.add prec (I.add prec sab (integral_float_signed depth b1 a2)) scd
        | _ => Inan end
    else
      Inan
  else
    Inan.

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
have Hfint_la_ua : ex_RInt f (T.toR la) (T.toR ua) by admit.
have Hfint_lb_ub : ex_RInt f (T.toR lb) (T.toR ub) by admit.
have Hfint_ua_lb : ex_RInt f (T.toR ua) (T.toR lb) by admit.
have Hfint_a_ua : ex_RInt f a (T.toR ua) by admit.
have Hfint_b_lb : ex_RInt f (T.toR lb) b by admit.
have Hfint_a_lb : ex_RInt f a (T.toR lb) by admit.
rewrite /integral_intBounds.
case ualb : (F.cmp ua lb) => //.
-  have -> : Xreal (RInt f a b) = 
        Xadd
          (Xadd (XRInt f  a (T.toR ua)) (XRInt f (T.toR ua) (T.toR lb)))
          (XRInt f (T.toR lb) b).
     by rewrite /= 2?RInt_Chasles => // .
   apply: I.add_correct.
   + apply: I.add_correct.
     * apply: (all_integrals_correct _ _ (T.toR la) (T.toR ua)) => //; admit .
     * case HR_ua : (F.real ua); case HR_lb : (F.real lb).
       - apply: integral_float_signed_correct => // .
       - admit.
       - admit.
       - admit.
   + apply: (all_integrals_correct _ _ (T.toR lb) (T.toR ub)) => //; admit.
- (* bis repetita *)
Admitted.


(* (* generalize HiFIntExt. *) *)
(* case Hia: ia => [|lba uba] //. *)
(* case Hib: ib => [|lbb ubb] // Ha Hb Hintf. *)
(* rewrite /integral_intBounds. *)
(* case ubaReal : (F.real uba). *)
(*   - case ubaReal1 : (F.real uba); last by rewrite ubaReal1 in ubaReal. (* hack to keep F.real uba in context for a later "slash slash" *) *)
(*     case lbbReal : (F.real lbb). *)
(*     + case lbbReal1 : (F.real lbb); last by rewrite lbbReal1 in lbbReal. *)
(*       move/F_realP: ubaReal => Huba. *)
(*       move/F_realP: lbbReal => Hlbb. *)
(*       have -> : *)
(*         Xreal (RInt f a b) = *)
(*         Xadd *)
(*           (Xadd (XRInt f  a (T.toR uba)) (XRInt f (T.toR uba) (T.toR lbb))) *)
(*           (XRInt f (T.toR lbb) b). *)
(*         * rewrite /= . *)
(*           rewrite 2?RInt_Chasles => // . *)
(*           - by admit. *)
(*           - by admit. *)
(*           - by admit. *)
(*           - by admit. *)
(*       apply: I.add_correct. *)
(*         apply: I.add_correct. *)
(*           apply: all_integrals_correct => // . *)
(*           by admit. *)
(*         apply: integral_float_signed_correct => // . *)
(*         apply: Hintf. *)
(*           by admit. *)
(*         by admit. *)
(*     + apply: all_integrals_correct => //. *)
(*        admit. *)
(* case Hflbb : (F.toF lbb); have := (F.real_correct lbb); *)
(* rewrite Hflbb lbbReal=> // _. *)
(* (* some intermediary lemmas are needed here *) *)
(* (* for example one saying that the integral is *) *)
(* (* Inan as soon as one of the bounds is not a real *) *)
(* Admitted. *)

End IntervalIntegral.

End IntegralTactic.
