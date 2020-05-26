Require Import Reals.
From Interval Require Import Tactic Basic.

Open Scope R_scope.

Lemma h_54_ln_2  h :
  -53 <= h <= 0 ->
  -  Rnearbyint rnd_DN (h * ln 2 / ln 5) * ln 5 <= 54 * ln 2.
Proof.
intros.
interval with (i_prec 10).
Qed.
