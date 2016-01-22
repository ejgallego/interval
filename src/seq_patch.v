Require Import seq.
Require Import ssreflect ssrnat.

Section revEq.

Lemma revEq : forall A l, @List.rev A l = rev l.
Proof.
move => A.
elim => [|a l HI] //.
rewrite /= rev_cons.
by rewrite -cats1 HI.
Qed.

Lemma nthEq A n (l : seq A) def : List.nth n l def = nth def l n.
move: l.
elim Hn : n => [|n0 HIn] l.
  by case: l.
case: l HIn => [ | a0 l] HIn // .
by rewrite /= -HIn.
Qed.

Lemma mapEq A B (l : seq A) (f : A -> B) : List.map f l = map f l.
Proof.
elim: l => [|a0 l HIl] => //= .
Qed.

End revEq.
