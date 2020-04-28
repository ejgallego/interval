Require Import Reals.
Require Import Coquelicot.Coquelicot.
Require Import Tactic.

Goal True.
integral_intro (RInt (fun x => ln x) 1 (sqrt 2)) with (i_relwidth 20).
integral_intro (RInt_gen (fun x => (1 + 1 / x) / (x * ln x ^ 2)) (at_point (PI * 5)) (Rbar_locally p_infty)).
integral_intro (RInt_gen (fun x => (1 + 1 / x) * (powerRZ x (-2) * ln x ^ 2)) (at_point 10) (Rbar_locally p_infty)).
integral_intro (RInt_gen (fun x => cos x * (powerRZ x 2 * ln x ^ 3)) (at_right 0) (at_point 2)) with (i_width (-20)).
Abort.
