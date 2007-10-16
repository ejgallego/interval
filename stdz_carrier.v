Require Import ZArith.
Require Import Bool.
Require Import definitions.
Require Import generic.
Require Import specific_sig.

Module StdZRadix2 <: FloatCarrier.

Definition radix := 2%positive.
Definition radix_correct := refl_equal Lt.
Definition mantissa_type := positive.
Definition exponent_type := Z.

Definition PtoM := fun (m : positive) => m.
Definition MtoP := fun (m : positive) => m.
Definition EtoZ := fun (e : Z) => e.
Definition ZtoE := fun (e : Z) => e.

Definition exponent_zero := Z0.
Definition exponent_one := Zpos xH.
Definition exponent_neg := Zopp.
Definition exponent_add := Zplus.
Definition exponent_sub := Zminus.
Definition exponent_cmp := Zcompare.
Definition mantissa_one := xH.
Definition mantissa_add := Pplus.
Definition mantissa_sub := Pminus.
Definition mantissa_mul := Pmult.
Definition mantissa_cmp x y := Pcompare x y Eq.
Definition mantissa_shl m d :=
  match d with Zpos nb => iter_pos nb _ (fun x => xO x) m | _ => m end.
Definition mantissa_even m :=
  match m with xO _ => true | _ => false end.

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
      | (xH, _) => (xH, pos_Eq) (* dummy *)
      | (xO p, pos_Eq) => (p, pos_Eq)
      | (xO p, _) => (p, pos_Lo)
      | (xI p, pos_Eq) => (p, pos_Mi)
      | (xI p, _) => (p, pos_Up)
      end) (m, pos)
  | _ => (m, pos) (* dummy *)
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
          match (Zcompare (Zpos p0) (Zpos p)) with
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
Definition ZtoE_correct := fun x : Z => refl_equal x.
Definition exponent_zero_correct := refl_equal Z0.
Definition exponent_neg_correct := fun x => refl_equal (- EtoZ x)%Z.
Definition exponent_add_correct := fun x y => refl_equal (EtoZ x + EtoZ y)%Z.
Definition exponent_sub_correct := fun x y => refl_equal (EtoZ x - EtoZ y)%Z.
Definition exponent_cmp_correct := fun x y => refl_equal (EtoZ x ?= EtoZ y)%Z.
Definition mantissa_mul_correct := fun x y => refl_equal (MtoP x * MtoP y)%positive.
Definition mantissa_cmp_correct := fun x y => refl_equal (Zpos (MtoP x) ?= Zpos (MtoP y))%Z.

Axiom mantissa_digits_correct :
  forall x, EtoZ (mantissa_digits x) = Zpos (count_digits radix (MtoP x)).

Lemma mantissa_shl_correct :
  forall x y z, EtoZ z = Zpos x ->
  MtoP (mantissa_shl y z) = shift radix (MtoP y) x.
intros.
unfold EtoZ in H.
rewrite H.
apply refl_equal.
Qed.

End StdZRadix2.
