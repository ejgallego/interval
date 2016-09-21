Require Import Reals Coquelicot.Coquelicot.
Require Import mathcomp.ssreflect.ssreflect mathcomp.ssreflect.ssrfun mathcomp.ssreflect.ssrbool mathcomp.ssreflect.ssrnat.
Require Import coquelicot_compl Interval_missing.
Require Import mathcomp.ssreflect.bigop.
Require Import ZArith Psatz.

Fixpoint f (alpha : Z) (beta : nat) (A B : R) {struct beta} :=
  match beta with
    | 0 => (powerRZ B (alpha+1)- powerRZ A (alpha+1)) / (IZR (alpha + 1))
    | S m =>
      (powerRZ B (alpha+1) * (pow (ln B) (beta)) -
       powerRZ A (alpha+1) * (pow (ln A) beta)) / (IZR (alpha + 1)) -
      (INR beta) / (IZR (alpha+1)) * f alpha m A B end.

Fixpoint f_lim (alpha : Z) (beta : nat) (A : R) {struct beta} :=
  match beta with
    | 0 => (- powerRZ A (alpha+1)) / (IZR (alpha + 1))
    | S m =>
       - ( powerRZ A (alpha+1) * (pow (ln A) beta)) / (IZR (alpha + 1)) -
      (INR beta) / (IZR (alpha+1)) * f_lim alpha m A end.

Variables (A B : R).

Eval vm_compute in f 1 1 A B.

Definition Bertrand alpha beta A B (I : R) :=
  is_RInt (fun x => powerRZ x alpha * (pow (ln x) beta)) A B I.

Definition Bertrand_lim alpha beta (A : R) (I : R) :=
  is_RInt_gen (fun x => powerRZ x alpha * (pow (ln x) beta)) (at_point A) (Rbar_locally p_infty) I.

Lemma powerRZ_ind (P : Z -> (R -> R) -> Prop) :
  P 0%Z (fun x => 1) ->
  (forall n, P (Z.of_nat n) (fun x => x ^ n)) ->
  (forall n, P ((-(Z.of_nat n))%Z) (fun x => / x ^ n)) ->
  (forall f g, f =1 g -> forall n, P n f -> P n g) ->
  forall (m : Z), P m (fun x => powerRZ x m).
Proof.
move => H0 Hpos Hneg Hext m.
case: m => [|p|p].
- by rewrite /=.
- rewrite -positive_nat_Z.
  apply: Hext. move => x.
  by rewrite -pow_powerRZ.
  exact: Hpos.
- rewrite /powerRZ.
  apply: Hext. move => x.
  by [].
  rewrite -Pos2Z.opp_pos.
  rewrite -positive_nat_Z.
  exact: Hneg.
Qed.

Lemma is_derive_powerRZ (n : Z) (x : R):
  ((0 <= n)%Z \/ x <> 0) ->
  is_derive (fun x : R => powerRZ x n) x (IZR n * (powerRZ x (n - 1))).
Proof.
move => Hnx.
move: (is_derive_n_powerRZ n 1 x Hnx).
case Hn : n => [|p|p] /= .
- by rewrite !Rmult_0_l; move => _; apply: is_derive_const.
- rewrite big_ord_recl /= big_ord0 /=  subn0 Rmult_1_r.
  case: p Hn => p.
  + rewrite -[Z.pos p~0]positive_nat_Z pow_powerRZ.
    move => _.
    congr (is_derive _ _); congr(_ * _).
    have -> : (1 = (Pos.to_nat 1))%N by [].
    by rewrite -[(Pos.to_nat p~1 - Pos.to_nat 1)%N]nat_of_P_minus_morphism. (* !!! *)
  + move => _.
    have -> : (1 = (Pos.to_nat 1))%N by [].
    by rewrite -[(Pos.to_nat p~0 - Pos.to_nat 1)%N]nat_of_P_minus_morphism.
  + by rewrite pow_powerRZ.
- rewrite big_ord_recl /= big_ord0 /= addn0 Rmult_1_r.
  by rewrite Pos2Nat.inj_add.
Qed.

Lemma is_derive_powerRZS (n : Z) (x : R):
  ((1 <= n)%Z \/ x <> 0) ->
  is_derive (fun x : R => powerRZ x (n+1)) x (IZR (n+1) * (powerRZ x n)).
Proof.
move => Hnx.
move: (is_derive_powerRZ (n+1) x).
rewrite Z.add_simpl_r // ; apply.
case: Hnx => [Hn | Hx].
  left; lia.
by right.
Qed.

Lemma ex_derive_powerRZ (n : Z) (x : R):
  ((0 <= n)%Z \/ x <> 0) ->
  ex_derive (fun x : R => powerRZ x n) x.
Proof.
move => H.
apply: (ex_derive_is_derive ((fun x : R => powerRZ x (n)))).
exact: is_derive_powerRZ.
Qed.

Lemma ex_derive_powerRZS (n : Z) (x : R):
  ((1 <= n)%Z \/ x <> 0) ->
  ex_derive (fun x : R => powerRZ x (n+1)) x.
Proof.
move => H.
apply: ex_derive_powerRZ.
case: H => [Hn | Hx].
  left; lia.
by right.
Qed.

Lemma is_RInt_powerRZ (alpha : Z) (a b : R) (HneqN1 : alpha <> (-1)%Z) (H : 0 < a <= b) :
is_RInt (powerRZ^~ alpha) a b
    ((powerRZ b (alpha + 1) - powerRZ a (alpha + 1)) / IZR (alpha + 1)).
Proof.
have neq0 : IZR (alpha + 1) <> 0.
  apply: not_0_IZR.
  by rewrite Z.add_move_0_r; exact: HneqN1.
pose F := fun x => powerRZ x (alpha+1) / IZR (alpha + 1).
have -> : ((powerRZ b (alpha + 1) - powerRZ a (alpha + 1)) / IZR (alpha + 1)) = F b - F a.
rewrite /F.
field => // .
have xneq0 : forall x, Rmin a b <= x <= Rmax a b -> x <> 0.
  move => x [Hax Hxb].
  apply: Rgt_not_eq.
  apply: (Rlt_le_trans 0 (Rmin a b) x) => // .
  by case: H => [H0a Hab]; rewrite Rmin_left.
apply: is_RInt_derive => x Hx.
rewrite /F.
have -> : (powerRZ x alpha) = ((IZR (alpha+1)) * ((powerRZ x alpha)) / (IZR (alpha+1))).
  by field.
rewrite !/Rdiv.
apply: is_derive_scal_l.
apply: is_derive_powerRZS.
by right; apply xneq0.
apply: ex_derive_continuous.
apply: (ex_derive_n_powerRZ alpha 1).
by right; apply xneq0.
Qed.

(* this one should be in Coquelicot to relieve users *)
Lemma continuous_Rdiv_1_x x (H : x <> 0) : continuous (Rdiv 1) x.
Proof.
apply: (continuous_ext (fun (x : R) => (/ x))).
  by move => x0; rewrite /Rdiv Rmult_1_l.
exact: continuous_Rinv.
Qed.

Lemma one_step_by_parts alpha beta (A : R) (B : R) (H : 0 < A <= B) (Halpha:  alpha <> (-1)%Z) :
  forall I, Bertrand alpha beta A B I ->
  Bertrand alpha (S beta) A B
     ((powerRZ B (alpha+1) * (pow (ln B) (S beta)) -
       powerRZ A (alpha+1) * (pow (ln A) (S beta))) / (IZR (alpha + 1)) -
      (INR (S beta)) / (IZR (alpha+1)) * I).
Proof.
have Salpha_neq_0 :   IZR (alpha + 1) <> 0.
  by apply: not_0_IZR; lia.
move => I HABI.
rewrite/Bertrand.
pose f := (fun x => Rdiv (powerRZ x (alpha+1)) (IZR(alpha+1))).
pose f' := (fun x => powerRZ x alpha).
pose g := (fun x => pow (ln x) (beta.+1)).
pose g' := (fun x => (1 / x) * (INR (beta.+1) * pow (ln x) beta)).
set f'g := (fun x : R => scal (f' x) (g x)).
pose fg' := (fun t => scal (f t) (g' t)).
pose f'gplusfg' := (fun t : R => plus (f'g t) (fg' t)).
apply (is_RInt_ext (fun x => minus (f'gplusfg' x) (fg' x))) => [x HX|].
rewrite /f'gplusfg' /fg' /f /g /f'g.
by rewrite /minus -plus_assoc plus_opp_r plus_zero_r /scal.
apply: is_RInt_minus.
- apply: (is_RInt_ext (fun t : R => plus (scal (f' t) (g t)) (scal (f t) (g' t)))) =>[x Hx|].
    by [].
  have -> : ((powerRZ B (alpha + 1) * ln B ^ beta.+1 -
      powerRZ A (alpha + 1) * ln A ^ beta.+1) / IZR (alpha + 1)) = (minus (scal (f B) (g B)) (scal (f A) (g A))).
    rewrite /f /g /minus /opp /plus /scal /mult  /= /mult /= .
    by field.
  apply: (is_RInt_scal_derive f g f' g' A B) => x Hx.
  have xgt0 : x > 0 by case: Hx; rewrite Rmin_left; lra.
  + rewrite /f /f'.
    apply: (is_derive_ext (fun x0 => scal (powerRZ x0 (alpha + 1)) (1 / IZR (alpha + 1)))) => [t|].
      by rewrite /scal /= /mult /=;field.
    have -> : powerRZ x alpha = scal (IZR (alpha+1) * (powerRZ x alpha)) (1 / IZR (alpha + 1)).
      by rewrite /scal /mult /= /mult /=; field.
    apply: is_derive_scal_l.
    apply: (is_derive_powerRZS alpha x).
    by lra.
  + rewrite /g /g'.
    have -> : (1 / x * (INR beta.+1 * ln x ^ beta)) = (INR beta.+1 * ( / x) * ln x ^ beta.+1.-1).
      rewrite -pred_Sn; field.
      by case: Hx; rewrite Rmin_left; lra.
    apply: (is_derive_pow).
    apply: is_derive_ln.
    by case: Hx; rewrite Rmin_left; lra.
  + have Hxneq0 : x <> 0 by rewrite Rmin_left in Hx; lra.
    apply: ex_derive_continuous.
    apply: ex_derive_powerRZ; right => // .
  + have Hxgt0 : x > 0 by rewrite Rmin_left in Hx; lra.
    have Hxneq0 : x <> 0 by lra.
    apply: continuous_mult.
    apply: continuous_Rdiv_1_x => // .
    apply: continuous_mult; first exact: continuous_const.
    (* intermediary lemmas needed here *)
    apply: ex_derive_continuous.
    apply: ex_derive_is_derive.
    apply: is_derive_pow.
    by apply: is_derive_ln.
    move: HABI; rewrite /Bertrand.
    suff Hx : forall x, Rmin A B < x < Rmax A B -> (fun x => scal (INR beta.+1 / IZR (alpha + 1)) (powerRZ x alpha * ln x ^ beta)) x = fg' x => [HABI|t HAtB].
      apply: is_RInt_ext.
      exact: Hx.
      apply: is_RInt_scal => // .
    have Hxgt0 : t > 0 by rewrite Rmin_left in HAtB; lra.
    have Hxneq0 : t <> 0 by lra.
    rewrite /fg' /f /g'.
    rewrite powerRZ_add // .
    rewrite /scal /= /mult /=.
    field; lra.
Qed.

Lemma Bertrand_beta0 alpha (A : R) (B : R) (HneqN1 : alpha <> (-1)%Z) (H : 0 < A <= B) :
  Bertrand alpha 0 A B ((powerRZ B (alpha+1)- powerRZ A (alpha+1)) / (IZR (alpha + 1))).
Proof.
rewrite /Bertrand.
apply: (is_RInt_ext (fun x => powerRZ x alpha)).
by move => x Hx; rewrite pow_O Rmult_1_r.
apply: is_RInt_powerRZ => // .
Qed.

Lemma int_x_alpha alpha A B (H : 0 < A <= B) (Halpha:  alpha <> (-1)%Z) :
is_RInt (powerRZ^~ alpha) A B
((powerRZ B (alpha + 1) - powerRZ A (alpha + 1)) / IZR (alpha + 1)).
Proof.
apply: is_RInt_powerRZ => // .
Qed.

Lemma f_correct alpha beta A B (H : 0 < A <= B) (Halpha:  alpha <> (-1)%Z) :
 Bertrand alpha beta A B (f alpha beta A B).
Proof.
elim: beta => [|m HIm] // .
  rewrite /f /Bertrand.
  apply: (is_RInt_ext (fun x => powerRZ x alpha)).
  + by move => x Hx; rewrite pow_O Rmult_1_r.
  exact: int_x_alpha.
by move: (one_step_by_parts alpha m A B H Halpha _ HIm).
Qed.

Lemma at_point_refl (a : R) : at_point a (eq^~ a).
Proof.
move => x Hx. apply: eq_sym.
apply: (ball_eq _ _ Hx).
Qed.


Lemma prod_to_single_general {T U V : UniformSpace} (HTSeparable : forall c t, (forall eps : posreal, @ball T c eps t) -> t=c) A (f : T -> U -> V) (F: (U -> Prop) -> Prop) {HF : Filter F} (G : (V -> Prop) -> Prop) :
filterlim (fun xtu : T * U => f xtu.1 xtu.2)
          (filter_prod (at_point A) F) G
<->
filterlim (fun u : U => f A u) F G.
Proof.
split => H.
- move => P GP.
  rewrite /filtermap.
  move: (filter_prod_ind T U (at_point A) F (fun x => P (f (fst x) (snd x)))).
  case: (H P GP) => /= Q1 R1 HAQ1 HFR1 HPfxy.
  apply => /= .
  move => Q R HAQ HFR HPf.
  eapply filter_imp.
  2: exact: HFR.
  move => x HRx.
  apply: HPf => // .
  apply: HAQ => eps // ; exact: ball_center.
  econstructor.
  exact: HAQ1.
  exact: HFR1.
  exact: HPfxy.
- move => P GP.
  rewrite /filtermap.
  move: (H P GP).
  rewrite /filtermap => HFP.
  set R := (fun x : U => P (f A x)).
  set Q := (fun x => x = A).
  apply: (Filter_prod _ _ _ Q R) => //= ; last first.
  move => t u.
  rewrite /Q.
  move => HQt /= HPfAu.
  rewrite HQt.
  exact: HPfAu.
  move => t Heps.
  rewrite /Q.
  exact: HTSeparable.
Qed.

Lemma prod_to_single_normedmodule (K : AbsRing) {T U V : NormedModule K} A (f : T -> U -> V) (F: (U -> Prop) -> Prop) {HF : Filter F} (G : (V -> Prop) -> Prop) :
filterlim (fun xtu : T * U => f xtu.1 xtu.2)
          (filter_prod (at_point A) F) G
<->
filterlim (fun u : U => f A u) F G.
Proof.
apply: prod_to_single_general.
move => c t Hct.
apply: eq_sym.
exact: ball_eq.
Qed.

Lemma is_lim_RInv_p_infty:
is_lim [eta Rinv] p_infty 0.
Proof.
  apply: (is_lim_ext (fun x => 1 / x)).
    move => y. rewrite -Rinv_Rdiv ?Rdiv_1 // .
    admit.
    exact: R1_neq_R0.
Admitted.

Lemma is_lim_powerRZ_0 alpha (Halpha : (alpha < 0)%Z) :
  is_lim (powerRZ^~ (alpha)%Z) p_infty (0%R).
Proof.
apply: (powerRZ_ind (fun n f => (n < 0)%Z -> is_lim f p_infty (0%R))) => // [n Hn|n Hn|].
- admit. (* absurd hypothesis, TODO *)
- elim: n Hn => [|m Hm Hn] // .
  rewrite /= .
  apply: (is_lim_ext (fun x => / x * / x^m)).
    move => y; rewrite Rinv_mult_distr // .
    (* we should be able to say that for y big enough, this is true *)
    (* there probably needs to be another is_lim_ext for this case  *)
    admit.
    admit.
  case: m Hm Hn => [|m Hm] Hn.
  + move => _ /=.
    have -> : 0 = Rbar_mult (Finite 0) (Finite 1) by rewrite /= Rmult_0_l.
    apply: (is_lim_mult (fun x => / x) (fun x => / 1) p_infty 0 1) => // .
    exact: is_lim_RInv_p_infty.
    by rewrite Rinv_1; exact: is_lim_const.

  have -> : 0 = Rbar_mult (Finite 0) (Finite 0) by rewrite /= Rmult_0_l.
  (* why so much detail needed ? *)
  apply: (is_lim_mult (fun x => / x) (fun x => / x^m.+1) p_infty 0 0) => // .
  exact: is_lim_RInv_p_infty.
  apply: Hm. rewrite Z.opp_neg_pos. rewrite /Z.of_nat. admit. (* :-( *)

move => f g Hfg n H1 H2.
apply: (is_lim_ext f g _ _ Hfg).
by apply: H1.
Admitted.

Lemma x_alpha_0 alpha (Halpha : (alpha < -1)%Z) :
  is_lim (powerRZ^~ (alpha + 1)%Z) p_infty (0%R).
Proof.
apply: is_lim_powerRZ_0.
by lia.
Qed.

Lemma x_alpha_beta alpha beta (Halpha : (alpha < -1)%Z) :
  is_lim (fun x => powerRZ x (alpha + 1)%Z * (pow (ln x) beta)) p_infty (0%R).
Proof.
(* apply: (is_lim_ext *)
Admitted.

Lemma f_lim_correct alpha beta A (H : 0 < A) (Halpha : (alpha < -1)%Z) :
 Bertrand_lim alpha beta A (f_lim alpha beta A).
Proof.
rewrite /Bertrand_lim /is_RInt_gen.
exists (fun xab => (f alpha beta (fst xab) (snd xab))).
split.
- exists (fun x => A = x) (fun x => A < x) .
    exact: ball_eq.
    by exists A.
  move => x y HAx HAy /=.
  apply: f_correct.
  + by lra.
  + by apply: Zlt_not_eq.
rewrite prod_to_single.
elim: beta => [ | beta Hbeta].
rewrite /f /f_lim /Rdiv /Rminus.
rewrite -[locally _]/(Rbar_locally (Rbar_mult (Finite _) (Finite _))).
rewrite -[filterlim _ _ _]/(is_lim _ p_infty _).
apply: is_lim_mult.
apply: is_lim_plus.
exact: x_alpha_0.
exact: is_lim_const.
rewrite /is_Rbar_plus /=.
apply f_equal, f_equal, Rplus_0_l.
apply is_lim_const.
done.
rewrite /f /f_lim -/f -/f_lim /Rdiv /Rminus.
rewrite -[locally _]/(Rbar_locally (Finite _)).
rewrite -[filterlim _ _ _]/(is_lim _ p_infty _).
apply: is_lim_plus.
apply: is_lim_mult.
apply: is_lim_plus.
exact: x_alpha_beta.
exact: is_lim_const.
done.
exact: is_lim_const.
done.
apply: is_lim_opp.
apply: is_lim_mult.
exact: is_lim_const.
rewrite -[locally _]/(Rbar_locally (Finite _)) in Hbeta.
exact Hbeta.
done.
by rewrite Rplus_0_l.
Qed.
