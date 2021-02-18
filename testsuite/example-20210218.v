From Coq Require Import Reals.
From Interval Require Import Tactic.

Open Scope R_scope.

Definition p1 := ltac:(plot (fun x => x^2 * sin (x^2)) (-4) 4 with (i_degree 8)).
Definition p2 := ltac:(plot (fun x => 1/x) (-1) 1 (-1) 1 with (i_size 1024 768)).
Definition p3 := ltac:(plot (fun x => x*x) 0 1).

Definition p4 := ltac:(plot
  (fun x => 1 + x * (4503599627370587 * powerRZ 2 (-52) + x * (4503599627370551 * powerRZ 2 (-53) + x * (6004799497195935 * powerRZ 2 (-55) + x * (6004799498485985 * powerRZ 2 (-57) + x * (2402017533563707 * powerRZ 2 (-58) + x * (6405354563481393 * powerRZ 2 (-62)))))))- exp x)
  (-1/32) (1/32) with (i_prec 90)).

(* plot [-1./32:1./32] 1 + x * (4503599627370587. * 2**(-52) + x * (4503599627370551. * 2**(-53) + x * (6004799497195935. * 2**(-55) + x * (6004799498485985. * 2**(-57) + x * (2402017533563707. * 2**(-58) + x * (6405354563481393. * 2**(-62))))))) - exp(x) *)
