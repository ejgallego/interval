From Interval Require Import Tactic.
From Coq Require Import Reals.
From Coquelicot Require Import Coquelicot.
Open Scope R_scope.

Goal RInt (fun x => x) 0 1 <= 2.
Proof. integral. Qed.