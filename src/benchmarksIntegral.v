Require Import Interval_tactic.
Require Import Interval_bigint_carrier.
Require Import Interval_specific_ops.
Module SFBI2 := SpecificFloat BigIntRadix2.
Module ITSFBI2 := IntervalTactic SFBI2.
Export ITSFBI2.

Require Import Coquelicot Reals.

Lemma bench1 :
 3 <=  RInt (fun x => 1 + 0 * x) 0 3 <= 3.
Proof.
Time interval.
Qed.

(* apparently we can't have both side mention epsilon, so lemmas are made into two lemmas *)
Lemma bench2_1 epsilon :
1 / 10 <= epsilon <= 1 ->
RInt (fun x => exp x - 1) 0 3 <= exp(1)*exp(1)*exp(1) - 1 + epsilon. 
(* integral = e^3 - 1 *)
Proof.
move => Hepsilon.
interval with (i_integral_depth 4).
Qed.

Lemma bench2_2 epsilon :
1 / 10 <= epsilon <= 1 ->
  exp(1)*exp(1)*exp(1) - (1 + epsilon) <=
  RInt (fun x => exp x - 1) 0 3.
(* integral = e^3 - 1 *)
Proof.
move => Hepsilon.
(* interval_intro (RInt (fun x => exp x - 1) 0 3) with (i_prec 200, i_integral_depth 10,i_integral_prec 10). *) (* whatever we do, no way to make the left side work *)
Admitted.

Lemma bench3_1 epsilon :
1/8 <= epsilon <= 1 -> 
1 / 4 - epsilon <=RInt (fun x => x * ln(1 + x)) 0 1.
(* integral = 1 / 4 *)
Proof.
move => Heps.
interval.
Qed.

Lemma bench3_2 epsilon :
1/8 <= epsilon <= 1 -> 
RInt (fun x => x * ln(1 + x)) 0 1 <= 1 / 4 + epsilon.
(* integral = 1 / 4 *)
Proof.
move => Heps.
interval.
Qed.

Lemma bench4_1 epsilon :
1/16 <= epsilon <= 1 -> 
RInt (fun x => sqrt(1 - x * x)) 0 1 <= PI / 4 + epsilon.
(* integral = Pi / 4 *)
Proof.
move => Heps.
interval.
Qed.

Lemma bench4_2 epsilon :
1/16 <= epsilon <= 1 -> 
PI / 4 - epsilon <= RInt (fun x => sqrt(1 - x * x)) 0 1.
(* integral = Pi / 4 *)
Proof.
move => Heps.
interval with (i_integral_depth 4).
Qed.

Lemma bench5 : True.
interval_intro (RInt (fun x => sin(sin x)) 0 1).
by [].
Qed.

Lemma bench6_1 epsilon :
2 <= epsilon -> 
exp(1) - 1 / exp(1) - epsilon <=RInt (fun x => sin(x) * exp(cos x)) 0 1.
(* integral = 1 - 1 / e *)
Proof.
move => Heps.
interval with (i_integral_depth 6).
Qed.

(* we need a much smaller epsilon to conclude, strange *)
Lemma bench6_2 epsilon :
1/8 <= epsilon -> 
RInt (fun x => sin(x) * exp(cos x)) 0 1 <= exp(1) - 1 / exp(1) + epsilon.
(* integral = 1 / 4 *)
Proof.
move => Heps.
interval with (i_integral_depth 6).
Qed.

Lemma bench7_1 epsilon :
1/32 <= epsilon <= 1 -> 
RInt (fun x => 1 / (1 + x*x)) 0 1 <= PI / 4 + epsilon.
(* integral = Pi / 4 *)
Proof.
move => Heps.
interval.
Qed.

Lemma bench7_2 epsilon :
1/32 <= epsilon <= 1 -> 
PI / 4 - epsilon <= RInt (fun x => 1 / (1 + x*x)) 0 1.
(* integral = Pi / 4 *)
Proof.
move => Heps.
interval with (i_integral_depth 4).
Qed.

Lemma bench8_1 epsilon :
1/32 <= epsilon <= 1 -> 
RInt (fun x => 1 / (1 + 10^10 * x*x)) 0 1 <= 1 / 10 ^(5) * atan(1 / 10^(5)) + epsilon.
(* integral = Pi / 4 *)
Proof.
move => Heps.
(* interval. *) admit. (* can't talk about atan *)
Qed.

Lemma bench8_2 epsilon :
1/32 <= epsilon <= 1 -> 
1 / 10 ^(5) * atan(1 / 10^(5)) - epsilon <= RInt (fun x => 1 / (1 + 10^10 * x*x)) 0 1.
(* integral = Pi / 4 *)
Proof.
move => Heps.
(* interval. *) admit. (* can't talk about atan *)
Qed.

Lemma bench9 : True.
Proof.
(* interval_intro (RInt (fun x => exp (1 / x^(100))) 0 (11/10)) with (i_integral_depth 2).  *) (* loops *)
Proof.
by [].
Qed.

Lemma bench10_1 epsilon :
10 <= epsilon -> 
1 / 3 * (1 - cos(1000)) - epsilon <= RInt (fun x => x*x*sin(x*x*x)) 0 10.
(* integral = 1 / 3 ( 1 - cos(1000)) *)
Proof.
move => Heps.
(* interval with (i_integral_depth 10, i_integral_prec 1000). *)
Admitted.

Lemma bench10_2 epsilon :
10 <= epsilon -> 
RInt (fun x => x*x*sin(x*x*x)) 0 10 <= 1 / 3 * (1 - cos(1000)) + epsilon.
(* integral = 1 / 3 ( 1 - cos(1000)) *)
Proof.
move => Heps.
(* interval with (i_integral_depth 10, i_integral_prec 1000). *)
Admitted.

Lemma bench11_1 epsilon :
1/8 <= epsilon -> 
2 / 3 - epsilon <= RInt (fun x => sqrt(x)) 0 1.
(* integral = 1 / 3 ( 1 - cos(1000)) *)
Proof.
move => Heps.
interval.
Qed.

Lemma bench11_2 epsilon :
1/16 <= epsilon -> 
RInt (fun x => sqrt(x)) 0 1 <= 2 / 3 + epsilon.
(* integral = 1 / 3 ( 1 - cos(1000)) *)
Proof.
move => Heps.
interval.
Qed.

(* actual integral : RInt (fun x => max (sin x) (cos x)) 0 1 *)
(* = sin PI / 4 + cos PI / 4 - cos 1 *)
Lemma bench12_1 epsilon :
1/16 <= epsilon ->
sqrt(2) - cos(1) - epsilon <= RInt (fun x => cos x) 0 (PI / 4) + RInt (fun x => sin x) (PI / 4) 1.
(* sum of integrals = sqrt(2) - cos(1) *)
Proof.
move => Heps.
interval.
Qed.

Lemma bench12_2 epsilon :
1/16 <= epsilon ->
RInt (fun x => cos x) 0 (PI / 4) + RInt (fun x => sin x) (PI / 4) 1 <= 
sqrt(2) - cos(1) + epsilon.
Proof.
move => Heps.
interval.
Qed.

