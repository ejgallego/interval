Require Import ZArith.
Require Import missing.
Require Import xreal.
Require Import definitions.
Require Import generic.
Require Import generic_proof.
Require Import float_sig.

Module Type Radix.
  Parameter val : positive.
  Parameter spec : (1 < Zpos val)%Z.
End Radix.

Module Radix2 <: Radix.
  Definition val := 2%positive.
  Definition spec := refl_equal Lt.
End Radix2.

Module Radix10 <: Radix.
  Definition val := 10%positive.
  Definition spec := refl_equal Lt.
End Radix10.

Module GenericFloat (Rad : Radix) <: FloatOps.
  Definition radix := Rad.val.
  Definition even_radix := match radix with xO _ => true | _ => false end.
  Definition radix_correct := Rad.spec.
  Definition even_radix_correct := refl_equal even_radix.
  Definition type := float radix.
  Definition toF := fun x : float radix => x.
  Definition fromF := fun x : float radix => x.
  Definition precision := positive.
  Definition sfactor := Z.
  Definition prec := fun x : positive => x.
  Definition ZtoS := fun x : Z => x.
  Definition PtoP := fun x : positive => x.
  Definition zero := Fzero radix.
  Definition nan := Fnan radix.
  Definition cmp := @Fcmp radix.
  Definition min := @Fmin radix.
  Definition max := @Fmax radix.
  Definition round := @Fround radix.
  Definition neg := @Fneg radix.
  Definition abs := @Fabs radix.
  Definition scale := @Fscale radix.
  Definition scale2 := @Fscale2 radix.
  Definition add_exact := @Fadd_exact radix.
  Definition sub_exact := @Fsub_exact radix.
  Definition mul_exact := @Fmul_exact radix.
  Definition add := @Fadd radix.
  Definition sub := @Fsub radix.
  Definition mul := @Fmul radix.
  Definition div := @Fdiv radix.
  Definition sqrt := @Fsqrt radix.
  Definition zero_correct := refl_equal zero.
  Definition nan_correct := refl_equal nan.
  Definition cmp_correct := fun x y => refl_equal (cmp x y).
  Definition min_correct := fun x y => refl_equal (FtoX (min x y)).
  Definition max_correct := fun x y => refl_equal (FtoX (max x y)).
  Definition neg_correct := fun x => refl_equal (FtoX (neg x)).
  Definition abs_correct := fun x => refl_equal (FtoX (abs x)).
  Definition scale_correct := fun x d => refl_equal (FtoX (scale x d)).
  Definition scale2_correct := fun x d (_ : even_radix = true) => refl_equal (FtoX (scale2 x d)).
  Definition add_exact_correct := fun x y => refl_equal (FtoX (add_exact x y)).
  Definition sub_exact_correct := fun x y => refl_equal (FtoX (sub_exact x y)).
  Definition mul_exact_correct := fun x y => refl_equal (FtoX (mul_exact x y)).
  Definition add_correct := fun mode prec x y => refl_equal (FtoX (add mode prec x y)).
  Definition sub_correct := fun mode prec x y => refl_equal (FtoX (sub mode prec x y)).
  Definition mul_correct := fun mode prec x y => refl_equal (FtoX (mul mode prec x y)).
  Definition div_correct := fun mode prec x y => refl_equal (FtoX (div mode prec x y)).
  Definition sqrt_correct := fun mode prec x => refl_equal (FtoX (sqrt mode prec x)).

  Definition fromZ n := match n with Zpos p => Float radix false p Z0 | Zneg p => Float radix true p Z0 | Z0 => Fzero radix end.
  Lemma fromZ_correct : forall n, FtoX (toF (fromZ n)) = Xreal (Z2R n).
    intros. case n ; split.
  Qed.

  Definition real (f : float radix) := match f with Fnan => false | _ => true end.
  Lemma real_correct :
    forall f, match toF f with Fnan => real f = false | _ => real f = true end.
  intros f.
  now case f.
  Qed.

End GenericFloat.
