Require Import Reals.
Require Import ZArith.
Require Import Interval_xreal.
Require Import Interval_missing.

Inductive rounding_mode : Set :=
  rnd_UP | rnd_DN | rnd_ZR | rnd_NE.

Fixpoint count_digits_aux (radix nb pow p q : positive) { struct q } : positive :=
  if Zlt_bool (Zpos p) (Zpos pow) then nb
  else
    match q with
    | xH => xH
    | xI r => count_digits_aux radix (Psucc nb) (Pmult radix pow) p r
    | xO r => count_digits_aux radix (Psucc nb) (Pmult radix pow) p r
    end.

Definition count_digits radix n :=
  count_digits_aux radix 1 radix n n.

Definition FtoR radix (s : bool) m e :=
  let sm := if s then Zneg m else Zpos m in
  match e with
  | Zpos p => Z2R (sm * Zpower_pos (Zpos radix) p)
  | Z0 => Z2R sm
  | Zneg p => (Z2R sm / Z2R (Zpower_pos (Zpos radix) p))%R
  end.

Definition is_float (radix prec : positive) (x : R) :=
  x = R0 \/
  exists s : bool, exists m : positive, exists e : Z,
  (Zpos (count_digits radix m) <= Zpos prec)%Z /\
  x = FtoR radix s m e.

Definition is_even_float (radix prec : positive) (x : R) :=
  x = R0 \/
  exists s : bool, exists m : positive, exists e : Z,
  (Zpos (count_digits radix (xO m)) <= Zpos prec)%Z /\
  x = FtoR radix s (xO m) e.

Definition is_around radix prec f x :=
  forall g, is_float radix prec g ->
  (Rle g x -> Rle g f) /\ (Rle x g -> Rle f g).

Definition is_correctly_rounded radix mode prec f' x' :=
  match x', f' with
  | Xnan, Xnan => True
  | Xreal x, Xreal f =>
    is_float radix prec f /\
    is_around radix prec f x /\
    match mode with
    | rnd_UP => Rle x f
    | rnd_DN => Rle f x
    | rnd_ZR => Rle (Rabs f) (Rabs x)
    | rnd_NE =>
      (forall g, is_float radix prec g ->
       f = g \/
       (Rabs (x - f) < Rabs (x - g))%R \/
       ((Rabs (x - f) = Rabs (x - g))%R /\ is_even_float radix prec f))
    end
  | _, _ => False
  end.
