Require Import Reals.
Require Import ZArith.
Require Import Fcore_Raux.
Require Import Interval_xreal.
Require Import Interval_missing.

Inductive rounding_mode : Set :=
  rnd_UP | rnd_DN | rnd_ZR | rnd_NE.

Definition radix2 := Build_radix 2 (refl_equal _).

Section Definitions.

Variable beta : radix.

Fixpoint count_digits_aux nb pow (p q : positive) { struct q } : positive :=
  if Zlt_bool (Zpos p) pow then nb
  else
    match q with
    | xH => nb
    | xI r => count_digits_aux (Psucc nb) (Zmult beta pow) p r
    | xO r => count_digits_aux (Psucc nb) (Zmult beta pow) p r
    end.

Definition count_digits n :=
  count_digits_aux 1 beta n n.

Definition FtoR (s : bool) m e :=
  let sm := if s then Zneg m else Zpos m in
  match e with
  | Zpos p => Z2R (sm * Zpower_pos beta p)
  | Z0 => Z2R sm
  | Zneg p => (Z2R sm / Z2R (Zpower_pos beta p))%R
  end.

Definition is_float (prec : positive) (x : R) :=
  x = R0 \/
  exists s : bool, exists m : positive, exists e : Z,
  (Zpos (count_digits m) <= Zpos prec)%Z /\
  x = FtoR s m e.

Definition is_even_float (prec : positive) (x : R) :=
  x = R0 \/
  exists s : bool, exists m : positive, exists e : Z,
  (Zpos (count_digits (xO m)) <= Zpos prec)%Z /\
  x = FtoR s (xO m) e.

Definition is_around prec f x :=
  forall g, is_float prec g ->
  (Rle g x -> Rle g f) /\ (Rle x g -> Rle f g).

Definition is_correctly_rounded mode prec f' x' :=
  match x', f' with
  | Xnan, Xnan => True
  | Xreal x, Xreal f =>
    is_float prec f /\
    is_around prec f x /\
    match mode with
    | rnd_UP => Rle x f
    | rnd_DN => Rle f x
    | rnd_ZR => Rle (Rabs f) (Rabs x)
    | rnd_NE =>
      (forall g, is_float prec g ->
       f = g \/
       (Rabs (x - f) < Rabs (x - g))%R \/
       ((Rabs (x - f) = Rabs (x - g))%R /\ is_even_float prec f))
    end
  | _, _ => False
  end.

End Definitions.