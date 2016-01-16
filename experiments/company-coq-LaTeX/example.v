(*** company-coq—LaTeX ***)

(** Before stepping through this file, run the following (‘M-:’):
      (load-file "company-coq-latex.el") *)

Require Import NArith ArithRing.

Fixpoint nsum max f :=
  match max with
  | O => f 0
  | S max' => f max + nsum max' f
  end.

Notation "'\ccNat{}'" := nat.
Notation "'\ccSucc{' n '}'" := (S n).
Notation "x \times y" := (mult x y) (at level 50).
Notation "'\ccNsum{' x '}{' max '}{' f '}'" := (nsum max (fun x => f)).
Notation "'\ccForall' x .. y , P" := (forall x, .. (forall y, P) ..) (at level 200, x binder, y binder, right associativity).

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
