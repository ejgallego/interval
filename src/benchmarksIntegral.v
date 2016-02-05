Require Import Interval_tactic.
Require Import Interval_bigint_carrier.
Require Import Interval_specific_ops.
Module SFBI2 := SpecificFloat BigIntRadix2.
Module ITSFBI2 := IntervalTactic SFBI2.
Export ITSFBI2.

Require Import Coquelicot Reals.

Lemma bench1 : (* remark : it would be nice to have ... = 3 as a goal*)
 3 <=  RInt (fun x => 1 + 0 * x) 0 3 <= 3.
Proof.
Time interval.
Qed.

(* apparently we can't have both side mention delta, so lemmas are made into two lemmas *)
Lemma bench2_1 delta :
1/(1024*1024) <= delta ->
RInt (fun x => exp x) 0 3 <= exp(1)*exp(1)*exp(1) - 1 + delta.
(* integral = e^3 - 1 *)
Proof.
move => Hdelta.
Time interval with (i_integral_depth 1).
Qed.

Lemma bench2_2 delta :
1 / (1024*1024) <= delta ->
  exp(1)*exp(1)*exp(1) - (1 + delta) <=
  RInt (fun x => exp x) 0 3.
(* integral = e^3 - 1 *)
Proof.
move => Hdelta.
Time interval with (i_integral_depth 10).
Qed.

Lemma bench3_1 delta :
1/1024 <= delta ->
1 / 4 - delta <= RInt (fun x => x * ln(1 + x)) 0 1.
(* integral = 1 / 4 *)
Proof.
move => Heps.
Time interval.
Qed.

Lemma bench3_2 delta :
1/1024 <= delta <= 1 ->
RInt (fun x => x * ln(1 + x)) 0 1 <= 1 / 4 + delta.
(* integral = 1 / 4 *)
Proof.
move => Heps.
interval.
Qed.

(*
Lemma bench4_1 delta :
1/256 <= delta ->
RInt (fun x => sqrt(1 - x * x)) 0 1 <= PI / 4 + delta.
(* integral = Pi / 4 *)
Proof.
move => Heps.
Time interval with (i_integral_depth 1).
(* illustrates the interest of the epsilon parameter in the tactic *)
Qed.

Lemma bench4_2 delta :
1/16 <= delta ->
PI / 4 - delta <= RInt (fun x => sqrt(1 - x * x)) 0 1.
(* integral = Pi / 4 *)
Proof.
move => Heps.
interval with (i_integral_depth 4).
Qed.
*)

Lemma bench5 : True.
interval_intro (RInt (fun x => sin(sin x)) 0 1). (* TODO : hardcode result and launch interval *)
by [].
Qed.

Lemma bench6_1 delta :
1/1024 <= delta ->
exp 1  - exp(cos 1) - delta <= RInt (fun x => sin(x) * exp(cos x)) 0 1.
(* integral = 1 - 1 / e *)
Proof.
move => Heps.
interval with (i_integral_depth 0).
Qed.

(* we need a much smaller delta to conclude, strange *)
Lemma bench6_2 delta :
1/1024 <= delta ->
RInt (fun x => sin(x) * exp(cos x)) 0 1 <= exp 1 - exp(cos 1) + delta.
(* integral = 1 / 4 *)
Proof.
move => Heps.
interval with (i_integral_depth 0).
Qed.

Lemma bench7_1 delta :
1/(1024*1024)<= delta ->
RInt (fun x => 1 / (1 + x*x)) 0 1 <= PI / 4 + delta.
(* integral = Pi / 4 *)
Proof.
move => Heps.
Time interval with (i_integral_depth 5).
Qed.

Lemma bench7_2 delta :
1/1024 <= delta ->
PI / 4 - delta <= RInt (fun x => 1 / (1 + x*x)) 0 1.
(* integral = Pi / 4 *)
Proof.
move => Heps.
interval with (i_integral_depth 10). (* thanks to epsilons this is now reasonable *)
Qed.

(*
Lemma bench8_1 delta :
1/10^4 <= delta <= 1 ->
RInt (fun x => 1 / (1 + 10^10 * x*x)) 0 1 <= 1 / 10^5 * atan(10^5) + delta.
(* integral = Pi / 4 *)
Proof.
move => Heps.
Time interval  with (i_integral_depth 14,i_integral_prec 10,i_prec 30).
(* Time interval_intro (RInt (fun x => 1 / (1 + 10^10 * x*x)) 0 1) with (i_integral_depth 15,i_integral_prec 10,i_prec 50). *)
Qed.
*)

Lemma bench8_2 delta :
1/1024 <= delta ->
1 / 10 ^(5) * atan(1 / 10^(5)) - delta <= RInt (fun x => 1 / (1 + 10^10 * x*x)) 0 1.
(* integral = Pi / 4 *)
Proof.
move => Heps.
interval.
Qed.

Lemma bench9 : True.
Proof.
interval_intro (RInt (fun x => exp (- x^(100))) 1 (11/10)) with (i_integral_depth 3).
by [].
Qed.

Lemma bench10_1 delta :
10 <= delta ->
1 / 3 * (1 - cos(1000)) - delta <= RInt (fun x => x*x*sin(x*x*x)) 0 10.
(* integral = 1 / 3 ( 1 - cos(1000)) *)
Proof.
move => Heps.
(* interval with (i_integral_depth 10, i_integral_prec 1000). *)
Admitted.

Lemma bench10_2 delta :
10 <= delta ->
RInt (fun x => x*x*sin(x*x*x)) 0 10 <= 1 / 3 * (1 - cos(1000)) + delta.
(* integral = 1 / 3 ( 1 - cos(1000)) *)
Proof.
move => Heps.
(* interval with (i_integral_depth 10, i_integral_prec 1000). *)
Admitted.


Lemma bench11_1 delta :
1/8 <= delta ->
2 / 3 - delta <= RInt (fun x => sqrt(x)) 0 1.
Proof.
move => Heps.
interval.
Qed.


Lemma bench11_2 delta :
1/16 <= delta ->
RInt (fun x => sqrt(x)) 0 1 <= 2 / 3 + delta.
(* integral = 1 / 3 ( 1 - cos(1000)) *)
Proof.
move => Heps.
interval.
Qed.

(* actual integral : RInt (fun x => max (sin x) (cos x)) 0 1 *)
(* = sin PI / 4 + cos PI / 4 - cos 1 *)
Lemma bench12_1 delta :
1/1024 <= delta ->
sqrt(2) - cos(1) - delta <= RInt (fun x => cos x) 0 (PI / 4) + RInt (fun x => sin x) (PI / 4) 1.
(* sum of integrals = sqrt(2) - cos(1) *)
Proof.
move => Heps.
interval with (i_integral_depth 0).
Qed.

Lemma bench12_2 delta :
1/1024 <= delta ->
RInt (fun x => cos x) 0 (PI / 4) + RInt (fun x => sin x) (PI / 4) 1 <=
sqrt(2) - cos(1) + delta.
Proof.
move => Heps.
interval with (i_integral_depth 0).
Qed.

Lemma bench13 : True.
Proof.
interval_intro (RInt (fun t => exp (-t^2)) 0 1) with (i_integral_depth 1).
exact I.
Qed.

(* benchmark from Yves Bertot : can't be done for now *)
(* Rabs (intégrale de 1/((k+1)*PI) à 1/(k*PI) de (fun x =>sin(1/x))) <=  1/(k*PI) * Rabs (intégrale de 0 à PI de sin) *)
Lemma Bertot_1 (k : R) : (* k is an integer but it should not be pertinent *)
k = 100 -> (* seems to work for any k!! *)
Rabs (RInt (fun x => sin(1 / x)) (1/((k+1)*PI)) (1/(k*PI))) <= 1/((k + 1)*PI) * Rabs (RInt sin 0 PI).
Proof.
move => Hk.
rewrite Hk.
interval.
Qed.

(*
Goal forall x, 10/121 <= x <= 10/120 -> True.
intros x H.
interval_intro (sin (1/x)) with (i_bisect_taylor x 3).

interval_intro (RInt (fun x => sin(1 / x)) (1/4) 1) with (i_integral_depth 5).
Qed.

Lemma Bertot_2 (k : R) :
(1 <= k) ->
1/(k*PI) * Rabs (RInt sin 0 PI) - Rabs (RInt (fun x => sin(1 / x)) (1/((k+1)*PI)) (1/(k*PI))) >= 0.
Proof.
move => Hk.
interval_intro (1 / k * PI).
(* interval_intro ((RInt (fun x : R => sin (1 / x)) (1 / ((k + 1) * PI)) (1 / (k * PI)))). *)
(* interval_intro (1/(k*PI) * Rabs (RInt sin 0 PI) - Rabs (RInt (fun x => sin(1 / x)) (1/((k+1)*PI)) (1/(k*PI)))) with (i_integral_depth 5, i_integral_prec 100, i_prec 100). *)
Admitted.
*)

Lemma Helfgott (* delta *) :
(* 1/32 <= delta -> *)
Rabs (RInt (fun x => x^2 * exp (- x^2 / 2) * ln(x)) (1 / 32) 1) <= 93426 / 10^6 (* + delta *).
Proof.
assert (forall x, 0 <= x <= 1/32 -> True).
intros x Hx.
interval_intro (x * exp (-x^2/2)).
exact I.
interval with (i_integral_depth 15, i_prec 40, i_integral_prec 10).
(* Maple says 0.09342500233 *)
Qed.
