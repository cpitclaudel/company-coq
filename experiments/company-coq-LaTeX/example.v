(*** company-coq—LaTeX ***)

(** Before stepping through this file, run the following (‘M-:’):
      (load-file "company-coq-latex.el") *)

Require Import NArith ArithRing.

Fixpoint nsum max f :=
  match max with
  | O => f 0
  | S max' => f max + nsum max' f
  end.

Infix "\wedge" := and (at level 190, right associativity).
Notation "A \implies{} B" := (forall (_ : A), B) (at level 200, right associativity).
Notation "'\ccForall{' x .. y '}{' P '}'" := (forall x, .. (forall y, P) ..) (at level 200, x binder, y binder, right associativity, format "'\ccForall{' x .. y '}{' P '}'").
Notation "'\ccNat{}'" := nat.
Notation "'\ccSucc{' n '}'" := (S n).
Infix "\times" := mult (at level 30).
Notation "'\ccNsum{' x '}{' max '}{' f '}'" := (nsum max (fun x => f)).

Require Import List.
Lemma gauss: forall n, 2 * (nsum n (fun x => x)) = n * (n + 1).
  intros.
  induction n.
  - cbv [nsum].
    reflexivity.
  - unfold nsum; fold nsum.
    rewrite Mult.mult_plus_distr_l.
    rewrite IHn.
    ring.
Qed.

Require Import Coq.QArith.QArith Coq.QArith.Qring Coq.QArith.Qfield.

Notation "'\ccQ{}'" := Q.
Notation "\ccPow{ x }{ y }" := (Qpower x y).
Notation "'\ccFrac{' x '}{' y '}'" := (Qdiv x y)  : Q_scope.
Infix "\le" := Qle (at level 100).
Infix "\eq" := Qeq (at level 100).
Infix "\times" := Qmult (at level 30).
Notation "\ccNot{ x }" := (not x) (at level 100).
Notation "x '\neq' y" := (not (Qeq x y)) (at level 100).

Lemma Qmult_Qdiv_fact :
  forall a b c, not (c == 0) -> a * (b / c) == (a * b) / c.
Proof.
  intros; field; assumption.
Qed.

Lemma Qdiv_1 :
  forall a, a / 1 == a.
Proof.
  intros; field.
Qed.

Lemma Qplus_le_0 :
  forall a b, 0 <= a -> 0 <= b -> 0 <= a + b.
Proof.
  intros a b Ha Hb.
  pose proof (Qplus_le_compat _ _ _ _ Ha Hb) as Hab.
  ring_simplify in Hab; assumption.
Qed.

Lemma Qplus_lt_0 :
  forall a b, 0 < a -> 0 <= b -> 0 < a + b.
Proof.
  intros a b Ha Hb.
  pose proof (Qplus_lt_le_compat _ _ _ _ Ha Hb) as Hab.
  ring_simplify in Hab; assumption.
Qed.

Lemma Qmult_0 :
  forall a b, 0 < a -> 0 < b -> 0 < a * b.
Proof.
  intros a b Ha Hb.
  rewrite <- (Qmult_lt_l _ _ _ Ha), Qmult_0_r in Hb; assumption.
Qed.

Lemma Qsqr_0 :
  forall a, 0 <= a ^ 2.
Proof.
  intros [n d].
  simpl; unfold Qmult, Qle; simpl.
  rewrite Z.mul_1_r; apply Z.ge_le, sqr_pos.
Qed.

Lemma Qgt_0_Qneq_0 :
  forall a, 0 < a -> not (a == 0).
Proof.
  intros [n d].
  unfold Qeq, Qlt; simpl.
  rewrite !Z.mul_1_r, Z.neg_pos_cases; intuition.
Qed.

Ltac Qside :=
  auto using Qplus_le_0, Qmult_le_0_compat, Qmult_0, Qgt_0_Qneq_0, Qlt_le_weak, Qsqr_0, Qplus_lt_0.

Lemma Qfracs :
  forall a b c d,
    a > 0 /\ b > 0 /\ c > 0 /\ d > 0 ->
    (a + c)/(b + d) <= a/b + c/d.
Proof with Qside.
  intros a b c d H.
  destruct H as (Ha & Hb & Hc & Hd).
  field_simplify...
  rewrite <- Qmult_le_l with (z := b + d)...
  rewrite Qmult_div_r...
  rewrite Qmult_Qdiv_fact...
  rewrite <- Qmult_le_l with (z := b * d)...
  rewrite Qmult_div_r...
  field_simplify; rewrite !Qdiv_1...
  rewrite <- Qplus_le_l with (z := - b * d * a); ring_simplify.
  rewrite <- Qplus_le_l with (z := - b * d * c); ring_simplify.
  Qside.
Qed.