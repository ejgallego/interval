(**
This file is part of the Coq.Interval library for proving bounds of
real-valued expressions in Coq: http://coq-interval.gforge.inria.fr/

Copyright (C) 2015-2016, Inria.
Copyright (C) 2015-2016, IRIT.

This library is governed by the CeCILL-C license under French law and
abiding by the rules of distribution of free software. You can use,
modify and/or redistribute the library under the terms of the CeCILL-C
license as circulated by CEA, CNRS and Inria at the following URL:
http://www.cecill.info/

As a counterpart to the access to the source code and rights to copy,
modify and redistribute granted by the license, users are provided
only with a limited warranty and the library's author, the holder of
the economic rights, and the successive licensors have only limited
liability. See the COPYING file for more details.
*)

From Coq Require Import Reals Psatz.
From Coquelicot Require Import Coquelicot.
From mathcomp.ssreflect Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq fintype bigop.

Require Import Stdlib Coquelicot Datatypes.

Import PolR.Notations.

Lemma is_derive_n_atan n (x : R) :
  let q n := iteri n
    (fun i c => PolR.div_mixed_r tt (PolR.sub tt (PolR.add tt c^`() (PolR.lift 2 c^`()))
      (PolR.mul_mixed tt (INR (i.+1).*2) (PolR.lift 1 c))) (INR i.+2))
    PolR.one in
  is_derive_n atan n x
  (if n is n.+1 then PolR.horner tt (q n) x / (1 + x²) ^ (n.+1) * INR (fact n.+1)
   else atan x)%R.
Proof.
move=> q; move: n x.
help_is_derive_n_whole n x.
- rewrite /Rdiv !Rsimpl.
  have := is_derive_atan x; exact: is_derive_ext.
- set Q := (1 + x * x)%R.
  have HQ : Q <> 0%R by exact: Rsqr_plus1_neq0.
  have HQ' : Q ^ n <> 0%R by exact: pow_nonzero.
  have HQ'' : Q * Q ^ n <> 0%R.
    rewrite Rmult_comm -(Rmult_0_l (1 + x * x)).
    by apply:Rmult_neq_compat_r; try apply: pow_nonzero; exact: Rsqr_plus1_neq0.
  auto_derive; first split.
  + exact: PolR.ex_derive_horner.
  + by split.
  + rewrite Rmult_1_l PolR.Derive_horner [q n.+1]iteriS -/(q n).
    rewrite PolR.horner_div_mixed_r PolR.horner_sub PolR.horner_add.
    rewrite PolR.horner_mul_mixed !PolR.horner_lift.
    rewrite -{1}[in RHS](Rmult_1_r (q n)^`().[x]) -Rmult_plus_distr_l.
    have->: x ^ 2 = x² by simpl; rewrite Rmult_1_r.
    rewrite pow_1 /Rdiv.
    have H1 : (if n is _.+1 then (INR n + 1)%R else 1%R) = INR n.+1 by [].
    rewrite H1.
    rewrite !Rinv_mult_distr // -/pow -/Q.
    have->: INR (fact n + (n * fact n))%coq_nat = INR (fact n.+1) by [].
    rewrite [in RHS]fact_simpl mult_INR.
    set A := (((q n)^`()).[x] * Q - INR (n.+1).*2 * ((q n).[x] * x)).
    have->: (A * / INR n.+2 * (/ Q * (/ Q * / Q ^ n)) * (INR n.+2 * INR (fact n.+1)) =
      A * (/ INR n.+2 * INR n.+2) * (/ Q * (/ Q * / Q ^ n)) * INR (fact n.+1))%R by ring.
    rewrite Rinv_l; last exact: not_0_INR.
    rewrite /A !Rsimpl. rewrite -mul2n [INR (2 * _)%N]mult_INR; simpl (INR 2).
    field; by split.
Qed.

Lemma is_derive_n_tan n x :
  cos x <> 0 ->
  let q n := iteri n
    (fun i c => PolR.div_mixed_r tt (PolR.add tt c^`() (PolR.lift 2 c^`())) (INR i.+1))
    (PolR.lift 1 PolR.one) in
  is_derive_n tan n x ((q n).[tan x] * INR (fact n)).
Proof.
move=> Hx q; move: n x Hx.
help_is_derive_n n x.
- by move=> x Hx; rewrite /= !Rsimpl.
- move=> Hx; auto_derive.
  + by eapply ex_derive_is_derive; apply: is_derive_tan.
  + rewrite !Rsimpl; rewrite (is_derive_unique _ _ _ (is_derive_tan _ Hx)).
    ring.
- exact: (open_comp cos (fun y => y <> 0%R)
                    (fun y _ => continuous_cos y) (open_neq 0%R)).
- move=> x Hx.
  move En1 : n.+1 => n1.
  (* Remember n.+1 as n1 to have a more tidy context after auto_derive *)
  auto_derive; repeat split.
  + apply: PolR.ex_derive_horner.
  + by eapply ex_derive_is_derive; apply: is_derive_tan.
  + rewrite Rmult_1_l.
    rewrite (is_derive_unique _ _ _ (is_derive_tan _ Hx)).
    rewrite PolR.Derive_horner [q n1.+1]iteriS -/(q n1).
    rewrite PolR.horner_div_mixed_r PolR.horner_add.
    rewrite !PolR.horner_lift.
    rewrite fact_simpl mult_INR.
    set A := (((q n1)^`()).[tan x] + ((q n1)^`()).[tan x] * tan x ^ 2).
    rewrite /Rdiv.
    have->: (A * / INR n1.+1 * (INR n1.+1 * INR (fact n1)) =
             A * INR (fact n1) * (/ INR n1.+1 * INR n1.+1))%R by ring.
    rewrite Rinv_l; last exact: not_0_INR.
    rewrite /A; ring.
Qed.
