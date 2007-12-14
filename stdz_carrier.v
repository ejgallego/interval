Require Import ZArith.
Require Import Bool.
Require Import definitions.
Require Import generic.
Require Import specific_sig.

Module StdZRadix2 <: FloatCarrier.

Definition radix := 2%positive.
Definition radix_correct := refl_equal Lt.
Definition smantissa_type := Z.
Definition mantissa_type := positive.
Definition exponent_type := Z.

Definition MtoP := fun (m : positive) => m.
Definition PtoM := fun (m : positive) => m.
Definition MtoZ := fun (m : Z) => m.
Definition ZtoM := fun (m : Z) => m.
Definition EtoZ := fun (e : Z) => e.
Definition ZtoE := fun (e : Z) => e.

Definition exponent_zero := Z0.
Definition exponent_one := Zpos xH.
Definition exponent_neg := Zopp.
Definition exponent_add := Zplus.
Definition exponent_sub := Zminus.
Definition exponent_cmp := Zcompare.
Definition mantissa_zero := Z0.
Definition mantissa_one := xH.
Definition mantissa_add := Pplus.
Definition mantissa_sub := Pminus.
Definition mantissa_mul := Pmult.
Definition mantissa_cmp x y := Pcompare x y Eq.
Definition mantissa_pos := Zpos.
Definition mantissa_neg := Zneg.

Definition valid_mantissa := fun (m : positive) => True.

Definition mantissa_sign m :=
  match m with
  | Zneg p => Mnumber true p
  | Z0 => Mzero
  | Zpos p => Mnumber false p
  end.

Definition mantissa_even m :=
  match m with
  | xO _ => true
  | _ => false
  end.

Definition mantissa_shl m d :=
  match d with Zpos nb => iter_pos nb _ (fun x => xO x) m | _ => xH end.

Definition mantissa_scale2 (m : mantissa_type) (d : exponent_type) := (m, d).

Fixpoint digits_aux m nb { struct m } :=
  match m with
  | xH => nb
  | xO p => digits_aux p (Psucc nb)
  | xI p => digits_aux p (Psucc nb)
  end.

Definition mantissa_digits m := Zpos (digits_aux m xH).

Definition mantissa_split_div m d pos :=
  match Zdiv_eucl (Zpos m) (Zpos d) with
  | (Zpos q, r) => (q, adjust_pos r d pos)
  | _ => (xH, pos_Eq) (* dummy *)
  end.

Definition mantissa_shr m d pos :=
  match d with
  | Zpos nb =>
    iter_pos nb _ (fun v =>
      match v with
      | (xO p, pos_Eq) => (p, pos_Eq)
      | (xO p, _)      => (p, pos_Lo)
      | (xI p, pos_Eq) => (p, pos_Mi)
      | (xI p, _)      => (p, pos_Up)
      | _ => (xH, pos_Eq) (* dummy *)
      end) (m, pos)
  | _ => (xH, pos_Eq) (* dummy *)
  end.

Definition mantissa_div := fun m d => mantissa_split_div m d pos_Eq.

Definition exponent_div2_floor n :=
  match n with
  | Z0 => (Z0, false)
  | Zpos xH => (Z0, true)
  | Zneg xH => (Zneg xH, true)
  | Zpos (xO p) => (Zpos p, false)
  | Zneg (xO p) => (Zneg p, false)
  | Zpos (xI p) => (Zpos p, true)
  | Zneg (xI p) => (Zneg (Psucc p), true)
  end.

Definition mantissa_sqrt (m : positive) : positive * position.
intros.
refine
  (match Zsqrt (Zpos m) _ with
  | existT s (exist r _) =>
    match s with
    | Zpos p =>
      let pos :=
        match r with
        | Z0 => pos_Eq
        | Zpos p0 =>
          match Pcompare p0 p Eq with
          | Gt => pos_Up
          | _ => pos_Lo
          end
        | Zneg _ => pos_Eq (* dummy *)
        end in
      (p, pos)
    | _ => (xH, pos_Eq) (* dummy *)
    end
  end).
compute.
discriminate.
Defined.

Definition PtoM_correct := fun x : positive => refl_equal x.
Definition ZtoM_correct := fun x : Z => refl_equal x.
Definition ZtoE_correct := fun x : Z => refl_equal x.
Definition exponent_zero_correct := refl_equal Z0.
Definition exponent_neg_correct := fun x => refl_equal (- EtoZ x)%Z.
Definition exponent_add_correct := fun x y => refl_equal (EtoZ x + EtoZ y)%Z.
Definition exponent_sub_correct := fun x y => refl_equal (EtoZ x - EtoZ y)%Z.
Definition exponent_cmp_correct := fun x y => refl_equal (EtoZ x ?= EtoZ y)%Z.
Definition mantissa_zero_correct := refl_equal Z0.
Definition mantissa_pos_correct :=
  fun (x : positive) (_ : True) => refl_equal (Zpos x).
Definition mantissa_neg_correct :=
  fun (x : positive) (_ : True) => refl_equal (Zneg x).
Definition mantissa_mul_correct :=
  fun x y (Hx Hy : True) => conj (refl_equal (MtoP x * MtoP y)%positive) I.
Definition mantissa_cmp_correct :=
  fun x y (Hx Hy : True) => refl_equal (Zpos (MtoP x) ?= Zpos (MtoP y))%Z.

Lemma mantissa_sign_correct :
  forall x,
  match mantissa_sign x with
  | Mzero => MtoZ x = Z0
  | Mnumber s p => MtoZ x = (if s then Zneg else Zpos) (MtoP p) /\ valid_mantissa p
  end.
intros.
case x ; repeat split.
Qed.

Axiom mantissa_digits_correct :
  forall x, valid_mantissa x ->
  EtoZ (mantissa_digits x) = Zpos (count_digits radix (MtoP x)).

Lemma mantissa_shl_correct :
  forall x y z, valid_mantissa y ->
  z = Zpos x ->
  MtoP (mantissa_shl y z) = shift radix (MtoP y) x /\
  valid_mantissa (mantissa_shl y z).
repeat split.
unfold EtoZ in H0.
rewrite H0.
apply refl_equal.
Qed.

End StdZRadix2.
