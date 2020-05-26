Require Import Reals Coquelicot.Coquelicot.
Require Import Interval.Tactic.

Lemma constant :
  3 <= RInt (fun x => 1) 0 3 <= 3.
Proof.
integral with (i_prec 10).
Qed.

Lemma exp_0_3 :
  Rabs (RInt (fun x => exp x) 0 3 - (exp 1 ^ 3 - 1)) <= 1/(1000*1000).
Proof.
integral with (i_fuel 1).
Qed.

Lemma x_ln1p_0_1 :
  Rabs (RInt (fun x => x * ln (1 + x)) 0 1 - 1/4) <= 1/1000.
Proof.
integral with (i_fuel 1).
Qed.

Lemma circle :
  Rabs (RInt (fun x => sqrt (1 - x * x)) 0 1 - PI / 4) <= 1/100.
Proof.
integral with (i_fuel 7, i_degree 1).
Qed.

Lemma exp_cos_0_1 :
  Rabs (RInt (fun x => sin x * exp (cos x)) 0 1 - (exp 1 - exp (cos 1))) <= 1/1000.
Proof.
integral with (i_fuel 1).
Qed.

Lemma arctan_0_1 :
  Rabs (RInt (fun x => 1 / (1 + x*x)) 0 1 - PI / 4) <= 1/1000.
Proof.
integral with (i_fuel 1).
Qed.
