Require Import List.
Require Import ZArith.
Require Import Coquelicot coquelicot_compl.
Require Import Interval_missing.
Require Import Interval_xreal.
Require Import Interval_definitions.
Require Import Interval_generic.
Require Import Interval_generic_proof.
Require Import Interval_float_sig.
Require Import Interval_interval.
Require Import Interval_interval_float_full.
Require Import Interval_bisect.

Require Import Ssreflect.ssreflect Ssreflect.ssrbool Ssreflect.ssrnat.
Require Import seq_patch.

Section Prelude.

Variable Ftype : Type.

Definition notInan (fi : Interval_interval_float.f_interval Ftype) :=
  match fi with
    | Interval_interval_float.Inan => false
    | _ => true end = true.


Section InversionUsualFunctions.

Lemma Xnan_inversion_Inv f (x : R) :
 notXnan (Xinv (Xreal (f x))) ->
 f x <> 0.
Proof.
move => HnotXnan Hfxeq0.
by rewrite Hfxeq0 /= is_zero_correct_zero in HnotXnan.
Qed.

Lemma Xnan_inversion_sqrt f (x : R) :
  notXnan (Xsqrt (Xreal (f x))) ->
  0 <= f x.
Proof.
rewrite /Xsqrt.
case Hneg : (is_negative (f x)) => // .
move:  (is_negative_spec (f x)); rewrite Hneg.
move => Habs.
by inversion Habs.
Qed.

Lemma Xnan_inversion_ln f (x : R) :
  notXnan(Xln (Xreal (f x))) ->
  0 < f x.
Proof.
rewrite /Xln.
case Hpos : (is_positive (f x)) => // .
move:  (is_positive_spec (f x)); rewrite Hpos.
move => Habs.
by inversion Habs.
Qed.

Lemma domain_correct unop a b x :
  (notXnan b -> b = Xreal (a x) /\ continuous a x) ->
  continuous a x ->
  notXnan ((unary ext_operations unop) b) ->
  (unary ext_operations unop) b = Xreal (unary real_operations unop (a x)) /\
  continuous (fun x0 : R => unary real_operations unop (a x0)) x.
Proof.
move => Hb Hconta HbnotXnan.
case Hbnan: b Hb => [|b1] // Hb.
rewrite Hbnan /= in HbnotXnan.
by case unop in HbnotXnan.
case: Hb => // Hb Hcontax.
split.
inversion Hb.
case: unop HbnotXnan; rewrite Hbnan -H0 //=.
- by case: (is_zero b1).
- by case: (is_negative b1).
- rewrite /Xtan /tan.
  rewrite /Xdiv /Xcos.
  by case Hzero : (is_zero (cos b1)).
- by case: (is_positive b1).
- case => [||p] // .
  by case : (is_zero b1).
case: unop HbnotXnan.
- move => _. by apply: continuous_opp.
- move => _. by apply: continuous_Rabs_comp.
- move => HnotXnan. apply: continuous_Rinv_comp => // .
  by apply: (Xnan_inversion_Inv); rewrite Hbnan Hb in HnotXnan.
- move => _. by apply: continuous_mult.
- move => HnotXnan. apply: continuous_sqrt_comp => // .
  by apply: Xnan_inversion_sqrt; rewrite -Hb -Hbnan.
- move => _. by apply: continuous_cos_comp.
- move => _. by apply: continuous_sin_comp.
- move => HnotXnan.
  apply: continuous_comp => // .
  apply: continuous_tan.
    rewrite Hbnan /= /Xtan /Xdiv Hb /Xcos in HnotXnan.
    move => Habs. move: HnotXnan.
    rewrite Habs. rewrite is_zero_correct_zero.
    by case: (Xsin _).
- move => _. by apply: continuous_atan_comp.
- move => _. by apply: continuous_exp_comp.
- move => HnotXnan.
    apply: continuous_comp => // .
    apply: continuous_ln.
    rewrite Hb in Hbnan.
    rewrite Hbnan /= in HnotXnan.
    move: HnotXnan.
    case Hpos : (is_positive (a x)) => HnotXnan.
    by apply: (is_positive_positive _ Hpos).
    by move: HnotXnan.
- move => n HnotXnan.
  rewrite /= /powerRZ.
  case: n HnotXnan => [|n|n] => HnotXnan.
  + exact: continuous_const.
  + apply: (continuous_comp a (fun x => pow x _)) => // .
    apply: ex_derive_continuous.
    apply: ex_derive_pow.
    exact: ex_derive_id.
  + have Hanot0 : a x <> 0.
    move => Habs. move: HnotXnan.
    rewrite /= /Xpower_int. rewrite Hb in Hbnan. rewrite Hbnan. case: ifP => // .
    rewrite Habs.
    by rewrite is_zero_correct_zero.
    apply: continuous_comp.
    apply: (continuous_comp a (fun x => pow x _)) => // .
    apply: ex_derive_continuous.
    apply: ex_derive_pow.
    exact: ex_derive_id.
    apply: continuous_Rinv.
    exact: pow_nonzero.
Qed.

End InversionUsualFunctions.

End Prelude.


Module Integrability (F : FloatOps with Definition even_radix := true).

Module I := FloatIntervalFull F.
Module A := IntervalAlgos I.

Section Integrability.

Variable prec : I.precision.
Definition evalInt := A.BndValuator.eval prec. (* to abstract to any evaluation *)
Definition boundsToInt b := map A.interval_from_bp b.
Definition boundsToR b := map A.real_from_bp b.
Definition notInan := notInan F.type.

Section Preliminary.
Require Import Ssreflect.seq.

Definition interval_operations := (A.BndValuator.operations prec).

Lemma evalOpRight (A : Type) (ops : operations A) (z : A) op (prog : seq term) l m :
  nth z (@eval_generic A z ops (rcons prog op) l) m =
  nth z
      (@eval_generic_body A z
         ops
         (@eval_generic _ z ops prog l) op) m.
Proof.
rewrite  /A.BndValuator.eval rev_formula revEq rev_rcons /= .
by rewrite rev_formula revEq.
Qed.


Section notInanProperties.

Lemma notInan_convert i :
  I.convert i = Inan -> i = Interval_interval_float.Inan.
case: i => // .
Qed.

Lemma notInan_inversion_Inv i :
notInan (I.inv prec i) -> ~ contains (I.convert i) (Xreal 0) .
Proof.
move => HnotInan Hcontains0.
suff: contains (I.convert (I.inv prec i)) Xnan => [Habs|].
  move: HnotInan.
  have := (proj1(xreal_ssr_compat.contains_Xnan (I.convert (I.inv prec i)))) Habs.
  by case: (I.inv prec i).
have -> : Xnan = Xinv (Xreal 0) by rewrite /= is_zero_correct_zero.
by apply: I.inv_correct.
Qed.


(* the two following lemmas (and the next two) are close copies of the above, but for any negative power instead of just (-1) *)
Lemma notInan_inversion_PowNeg i p:
notInan (I.power_int prec i (Z.neg p)) -> ~ contains (I.convert i) (Xreal 0) .
Proof.
move => HnotInan Hcontains0.
suff: contains (I.convert (I.power_int prec i (Z.neg p))) Xnan => [Habs|].
  move: HnotInan.
  have := (proj1(xreal_ssr_compat.contains_Xnan _ )) Habs.
  by case: (I.power_int prec i (Z.neg p)).
have -> : Xnan = Xpower_int (Xreal 0) (Z.neg p) by rewrite /= is_zero_correct_zero.
by apply: I.power_int_correct.
Qed.

Lemma notInan_inversion_Sqrt i :
  notInan (I.sqrt prec i) ->
  (forall x, contains (I.convert i) (Xreal x) -> x >= 0).
Proof.
move => HnotInan x Hcontains.
suff: contains (I.convert (I.sqrt prec i)) (Xsqrt (Xreal x)).
- rewrite /Xsqrt.
  case Hposx : (is_negative x); last first.
    move => Hcontsqrt.
    by apply: is_negative_positive.
  move => HcontXnan.
  have Habs := (proj1 (xreal_ssr_compat.contains_Xnan _)) HcontXnan.
  by rewrite (notInan_convert _ Habs) in HnotInan.
by apply: I.sqrt_correct.
Qed.

Lemma notInan_inversion_Ln i :
  notInan (I.ln prec i) ->
  (forall x, contains (I.convert i) (Xreal x) -> x > 0).
Proof.
move => HnotInan x Hcontains.
suff: contains (I.convert (I.ln prec i)) (Xln (Xreal x)).
- rewrite /Xln.
  case Hposx : (is_positive x).
    move => Hcontln.
    by apply: is_positive_positive.
  move => HcontXnan.
  have Habs := (proj1 (xreal_ssr_compat.contains_Xnan _)) HcontXnan.
  by rewrite (notInan_convert _ Habs) in HnotInan.
by apply: I.ln_correct.
Qed.

End notInanProperties.


(* copied from Interval_tactic *)
Lemma contains_eval prog bounds n :
  contains
    (I.convert
       (List.nth n
                 (A.BndValuator.eval prec prog (map A.interval_from_bp bounds))
                 I.nai))
    (Xreal (List.nth n (eval_real prog (List.map A.real_from_bp bounds)) 0)).
Proof.
set (xi := List.nth n (A.BndValuator.eval prec prog (map A.interval_from_bp bounds)) I.nai).
apply (xreal_to_real (fun x => contains (I.convert xi) x) (fun x => contains (I.convert xi) (Xreal x))).
now case (I.convert xi).
easy.
unfold xi.
replace (List.map Xreal (List.map A.real_from_bp bounds)) with (List.map A.xreal_from_bp bounds).
apply A.BndValuator.eval_correct.
clear.
induction bounds.
easy.
simpl.
rewrite IHbounds.
now case a.
Qed.

Lemma contains_eval_arg prog bounds n i x:
  contains (I.convert i) (Xreal x) ->
  contains
    (I.convert
       (List.nth n
                 (A.BndValuator.eval prec prog (i :: map A.interval_from_bp bounds))
                 I.nai))
    (Xreal (List.nth n (eval_real prog (x :: List.map A.real_from_bp bounds)) 0)).
Proof.
move => Hcontains.
set (xi := List.nth n (A.BndValuator.eval prec prog (i :: [seq A.interval_from_bp i | i <- bounds])%SEQ) I.nai).
apply (xreal_to_real (fun x => contains (I.convert xi) x) (fun x => contains (I.convert xi) (Xreal x))).
now case (I.convert xi).
easy.
unfold xi.
replace (List.map Xreal (x :: List.map A.real_from_bp bounds)) with
((Xreal x)::(List.map A.xreal_from_bp (bounds))).
apply A.BndValuator.eval_correct_ext => //.
clear.
rewrite /=. congr (_ :: _).
induction bounds.
easy.
simpl.
rewrite IHbounds.
now case a.
Qed.

Lemma notInan_inversion_unop prog unop i bounds n :
      notInan
        (nth I.nai
             (evalInt (rcons prog (Unary unop n)) (i :: boundsToInt bounds)) 0) ->
      notInan (nth I.nai (evalInt prog (i :: boundsToInt bounds)) n).
Proof.
move => HnotInan.
rewrite evalOpRight /eval_generic_body in HnotInan.
rewrite /notInan.
case Hnan : (nth I.nai (evalInt prog (i :: boundsToInt bounds)%SEQ) n) => // .
rewrite nthEq Hnan /= in HnotInan.
case: unop HnotInan => //= .
by case => // .
Qed.

Lemma notXnan_inversion_unop prog unop x bounds n :
      notXnan
        (nth Xnan
             (eval_ext (rcons prog (Unary unop n)) ((Xreal x) :: map A.xreal_from_bp bounds)) 0) ->
      notXnan (nth Xnan (eval_ext prog ((Xreal x) :: map A.xreal_from_bp bounds)) n).
Proof.
move => HnotXnan.
rewrite evalOpRight /eval_generic_body in HnotXnan.
rewrite /notXnan.
set xR := (nth _ _ _).
case Hnan : xR  => // .
rewrite /xR in Hnan.
rewrite nthEq Hnan in HnotXnan.
by case: unop HnotXnan => //= .
Qed.

Lemma notXnan_inversion_binop_left prog binop x bounds n1 n2 :
      notXnan
        (nth Xnan
             (eval_ext (rcons prog (Binary binop n1 n2)) (Xreal x :: map A.xreal_from_bp bounds)%SEQ) 0) ->
      notXnan (nth Xnan (eval_ext prog (Xreal x :: map A.xreal_from_bp bounds)%SEQ) n1).
Proof.
move => HnotXnan.
rewrite evalOpRight /eval_generic_body in HnotXnan.
rewrite /notXnan.
set xR := (nth _ _ _).
case Hnan : xR => // .
rewrite /xR in Hnan.
rewrite nthEq Hnan /= in HnotXnan.
by case: binop HnotXnan => //= .
Qed.

Lemma notXnan_inversion_binop_right prog binop x bounds n1 n2 :
      notXnan
        (nth Xnan
             (eval_ext (rcons prog (Binary binop n1 n2)) (Xreal x :: map A.xreal_from_bp bounds)%SEQ) 0) ->
      notXnan (nth Xnan (eval_ext prog (Xreal x :: map A.xreal_from_bp bounds)%SEQ) n2).
Proof.
move => HnotXnan.
rewrite evalOpRight /eval_generic_body in HnotXnan.
rewrite /notXnan.
set xR := (nth _ _ _).
case Hnan : xR => // .
rewrite /xR in Hnan.
case: binop HnotXnan => //= ;
  rewrite !nthEq; rewrite Hnan /= ;
  case: (nth Xnan
           (eval_generic Xnan ext_operations prog
               (Xreal x :: [seq A.xreal_from_bp i | i <- bounds])%SEQ) n1) => //=. (* dirty hack for now *)
Qed.


Lemma notInan_inversion_binop_left prog binop i bounds i1 i2 :
      notInan
        (nth I.nai
             (evalInt (rcons prog (Binary binop i1 i2)) (i :: boundsToInt bounds)%SEQ) 0) ->
      notInan (nth I.nai (evalInt prog (i :: boundsToInt bounds)%SEQ) i1).
Proof.
move => HnotInan.
rewrite evalOpRight /eval_generic_body in HnotInan.
rewrite /notInan.
case Hnan : (nth I.nai (evalInt prog (i :: boundsToInt bounds)%SEQ) i1) => // .
rewrite nthEq Hnan /= in HnotInan.
by case: binop HnotInan => //= .
Qed.

Lemma notInan_inversion_binop_right prog binop i bounds i1 i2 :
      notInan
        (nth I.nai
             (evalInt (rcons prog (Binary binop i1 i2)) (i :: boundsToInt bounds)%SEQ) 0) ->
      notInan (nth I.nai (evalInt prog (i :: boundsToInt bounds)%SEQ) i2).
Proof.
move => HnotInan.
- rewrite evalOpRight /eval_generic_body in HnotInan.
  rewrite /notInan.
  case Hnan : (nth I.nai (evalInt prog (i :: boundsToInt bounds)%SEQ) i2) => // .
  rewrite !nthEq Hnan /= in HnotInan.
  by case: binop HnotInan => //= ; case: (nth I.nai (evalInt prog (i :: boundsToInt bounds)%SEQ) i1).
Qed.

Lemma continuousProg2 prog bounds (x : R) : forall m : nat,
  notXnan (List.nth m
          (eval_ext prog ((Xreal x)::List.map A.xreal_from_bp bounds))
          Xnan) ->
  continuous
    (fun x =>
       List.nth
         m
         (eval_real
            prog
            (x::boundsToR bounds)) R0) x.
Proof.
rewrite /eval_ext /eval_real.
intros m H.
eapply proj2.
revert H.
apply: (eval_inductive_prop_fun _ _ (fun (f : R -> R) v => notXnan v -> v = Xreal (f x) /\ continuous f x)) => //.
intros f1 f2 Heq b H Hb.
case: (H Hb) => {H} H H'.
split.
by rewrite -Heq.
now eapply continuous_ext.
move => unop a b Hb HnotXnan.
apply: domain_correct => // .
case : Hb => // .
by move: HnotXnan; case: b => //; case: unop => // .
(* case of binary operator *)
case => a1 a2 b1 b2 Ha1 Ha2 HnotXnan /=.
- move: HnotXnan Ha1 Ha2.
  case: b1 => [|b1] // ;case: b2 => [|b2] // .
  move => _ [] // -> Hconta1 [] // -> Hconta2.
  by split => //; apply: continuous_plus.
- move: HnotXnan Ha1 Ha2.
  case: b1 => [|b1] // ;case: b2 => [|b2] // .
  move => _ [] // -> Hconta1 [] // -> Hconta2.
  by split => //; apply: continuous_minus.
- move: HnotXnan Ha1 Ha2.
  case: b1 => [|b1] // ;case: b2 => [|b2] // .
  move => _ [] // -> Hconta1 [] // -> Hconta2.
  by split => //; apply: continuous_mult.
- move: HnotXnan Ha1 Ha2.
  case: b1 => [|b1] // ;case: b2 => [|b2] // .
  move => HnotXnan [] // Heq1 Hconta1 [] // Heq2 Hconta2.
  split => // .
  + move: HnotXnan.
    rewrite /binary /ext_operations /Xdiv.
    case: (is_zero b2) => // .
    by inversion Heq1; inversion Heq2.
  + apply: continuous_mult => // .
    apply: continuous_Rinv_comp => // Habs .
    by move: Heq2 HnotXnan => ->; rewrite Habs /= is_zero_correct_zero.
intros [|n].
simpl.
intros _.
apply (conj eq_refl).
apply continuous_id.
simpl.
unfold boundsToR.
destruct (le_or_lt (length bounds) n).
rewrite nth_overflow => //.
by rewrite map_length.
rewrite (nth_indep _ _ (Xreal 0)).
replace (List.map A.xreal_from_bp bounds) with (List.map Xreal (List.map A.real_from_bp bounds)).
rewrite map_nth.
intros _.
apply (conj eq_refl).
apply continuous_const.
rewrite map_map.
apply map_ext.
now intros [].
by rewrite map_length.
Qed.

Definition TaylorEvaluator deg prog bounds m i :=
  A.TaylorValuator.TM.eval (prec, deg)
    (List.nth m
       (A.TaylorValuator.eval prec deg i prog
         (A.TaylorValuator.TM.var::
           List.map (fun b0 : A.bound_proof =>
             A.TaylorValuator.TM.const (A.interval_from_bp b0)) bounds))
       A.TaylorValuator.TM.dummy)
    i i.

(* we ensure that we get the former result by using the new one *)
Lemma continuousProgTaylor deg prog bounds (m : nat) i :
  forall x, contains (I.convert i) (Xreal x) ->
  (notInan (TaylorEvaluator deg prog bounds m i)) ->
  continuous
    (fun x =>
       List.nth
         m
         (eval_real
            prog
            (x::boundsToR bounds)) R0) x.
Proof.
move => x Hcontains HnotInan.
apply: continuousProg2.
generalize (A.TaylorValuator.eval_correct_ext prec deg prog bounds m i i (Xreal x) Hcontains).
revert HnotInan.
rewrite /TaylorEvaluator.
case: A.TaylorValuator.TM.eval => //.
case: (List.nth _ _ _) => //.
Qed.


(* we ensure that we get the former result by using the new one *)
Lemma continuousProg prog bounds (m : nat) i:
  forall x, contains (I.convert i) (Xreal x) ->
  (notInan (List.nth m
          (evalInt prog (i::boundsToInt bounds))
          I.nai)) ->
  continuous
    (fun x =>
       List.nth
         m
         (eval_real
            prog
            (x::boundsToR bounds)) R0) x.
Proof.
move => x Hcontains HnotInan.
apply: continuousProg2.
generalize (A.BndValuator.eval_correct_ext prec prog bounds m i (Xreal x) Hcontains).
revert HnotInan.
unfold evalInt, boundsToInt.
case: (List.nth _ _ _) => //.
case: (List.nth _ _ _) => //.
Qed.

Lemma integrableProg prog bounds m a b i:
  (forall x, Rmin a b <= x <= Rmax a b ->  contains (I.convert i) (Xreal x)) ->
  (notInan (List.nth m
          (evalInt prog (i::boundsToInt bounds))
          I.nai)) ->
  ex_RInt
    (fun x =>
       List.nth
         m
         (eval_real
            prog
            (x::boundsToR bounds)) R0)
    a
    b.
Proof.
move => Hcontains HnotInan.
apply: ex_RInt_continuous.
intros z Hz.
apply: continuousProg HnotInan.
by apply: Hcontains.
Qed.

Lemma integrableProgTaylor deg prog bounds m a b i:
  (forall x, Rmin a b <= x <= Rmax a b ->  contains (I.convert i) (Xreal x)) ->
  notInan (TaylorEvaluator deg prog bounds m i) ->
  ex_RInt
    (fun x =>
       List.nth
         m
         (eval_real
            prog
            (x::boundsToR bounds)) R0)
    a
    b.
Proof.
move => Hcontains HnotInan.
apply: ex_RInt_continuous.
intros z Hz.
apply: continuousProgTaylor HnotInan.
by apply: Hcontains.
Qed.

End Preliminary.

End Integrability.
End Integrability.
