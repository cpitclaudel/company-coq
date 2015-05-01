(*****************************************)
(* Welcome to this company-coq tutorial! *)
(* Here's a demo of a few nice features  *)
(*****************************************)

(* First of all, let's ensure that company-coq is running. Did you add

      (package-initialize)

      ;; Open .v files with Proof-General's coq-mode
      (require 'proof-site)

      ;; Load company-coq when opening Coq files
      (add-hook 'coq-mode-hook #'company-coq-initialize)

  to your .emacs? If not, you can try company-coq temporarily; just type
  `M-x company-coq-initialize'. *)

(* Let's get started! If you use emacs ≥ 24, the symbols below should be
   prettified, though they appear as ASCII in the source file. You can disable
   this feature by typing M-x prettify-symbols-mode. If the symbols show as
   square boxes instead, you may want to install a good unicode font, such as
   Symbola. *)

Definition PrettySymbols : (nat -> nat -> Prop) :=
  (fun (n m: nat) =>
     forall p, p <> n -> p >= m -> True \/ False).

(* Try typing an arrow `->' here: *)

(*****************************************************************************)

(* company-coq knows most basic Coq tactics, just a few letters are enough to
   locate a tactic. Pressing RET inserts it. You can navigate the auto-inserted
   fields using TAB *)

(* Try typing `setrewin RET' here: *)


(*****************************************************************************)

(* Math symbols also auto-complete *)

(* Try typing `\gam RET' here: *)

(*****************************************************************************)

(* company-coq binds a few convenient shortcuts, like M-RET and M-S-RET, to
   insert additional match cases *)

Ltac BasicTactic :=
  match goal with
  | [ H: ?a /\ ?b |- _ ] => destruct H
  (* Place the point on the empty line before `end', and press `M-S-RET'. *)
  (* You can press C-d to remove the contents of a field and move to the next *)

  end.

(*****************************************************************************)

(* Not sure what a tactic does? Type part of its name, and press C-h. *)

(* Try typing `appl C-h' here: *)

(*****************************************************************************)

(* Completion is smart enough to look for theorems and tactics in the current
buffer (and with the proper Coq patches, in the whole library). For example, it
knows about BasicTactic and PrettySymbols *)

(* Try typing `BasicTac' here: *)

(*****************************************************************************)

(* company-coq can extract an outline of your proof script; it includes links to
each definition, theorem, and lemma. *)

(* Try pressing `C-c C-,'. Press q to exit the outline buffer. *)

(*****************************************************************************)

(* Now for a few interactive features. You'll want to start the prover *)

(* Start Coq by pressing C-c RET here *)

(*****************************************************************************)

(* Now that Coq is started, company-coq can auto-complete library modules *)

(* Try typing `Require Import Coq.Z.B' here: *)

(*****************************************************************************)

(* Confused by an error message? company-coq has documentation for (some) of
   them, auto-extracted from the manual *)

(* Consider the following attempt at using Omega: *)

Require Import Omega.
Lemma refl : forall x, exists (y: nat), x = y.
Proof.
  (* Run the following line and inspect the error message: *)
  Fail omega.

  (* Now press `C-c C-a C-e' (Error). This suggest adding intros: *)
  intros.

  (* Try running omega again: *)
  Fail omega.

  (* Pressing C-c C-a C-e again. Suggests that this wasn't the right approach
     after all. *)
  eauto.

  (* By the way, did you notice that the goals line looked different? (If you're
  using Emacs ≥ 24.4) *)
Qed.

(*****************************************************************************)

(* Even if you know what the error means, sometimes it's hard to parse: *)

(* Evaluate the following block: *)

Inductive Tr {T} := TrL : T -> Tr | TrB : Tr -> Tr -> Tr.
Inductive Tt : @Tr Type -> Type := TtL : forall A, A -> Tt (TrL A) | TtBr : forall t1 t2, Tt t1 -> Tt t2 -> Tt (TrB t1 t2).

Fixpoint MkLarge {A} d (l ll:A) :=
  match d with O => TrL ll | S n => TrB (MkLarge n l l) (MkLarge n l ll) end.

Lemma inH: forall T n (t: T), inhabited (Tt (@MkLarge Type n T T)).
  intros; constructor; induction n; simpl; constructor; eauto. Qed.

Lemma LargeGoal : inhabited (Tt (@MkLarge Type 5 unit nat)).
  pose proof (inH unit 5 tt) as pr; simpl in *.
  Set Printing All.

  (* Run up to this point. The next command fails, due to a type error: *)
  Fail exact pr.

  (* This message is not very readable, as the two terms are very similar. It
     would be much nicer with just a diff of the two types. company-coq supports
     this: type `M-x company-coq-diff-unification-error'. Type q to exit. *)

  Unset Printing All.
Abort.

(*****************************************************************************)

(* One last nice feature is goal extraction. Let's prove a theorem by
   induction: *)

Lemma my_plus_comm :
  forall n m, n + m = m + n.
Proof.
  induction n; intros.
  - apply plus_n_O.
  - (* Evaluate everything up to this point. Wouldn't the proof would like nicer
       if this was a separate lemma? *)
    (* Press `C-c C-a C-x` (eXtract) to automatically extract a lemma from your
       goal. You will be prompted for a name, then for hypotheses to keep in
       your lemma. Try it on the empty line below: *)
    
Abort.