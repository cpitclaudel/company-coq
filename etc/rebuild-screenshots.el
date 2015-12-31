;; Packages

(eval-and-compile
  (add-to-list 'load-path "~/.emacs.d/lisp/ProofGeneral/generic")
  (add-to-list 'load-path "~/.emacs.d/lisp/company-coq/etc/")
  (add-to-list 'load-path "~/.emacs.d/lisp/company-coq")
  (add-to-list 'load-path "~/.emacs.d/lisp/company-mode"))

(require 'company)

(package-initialize)
(require 'dash)
(require 'noflet)
(require 'screenshots)

(my/basic-setup)
(my/faces-setup)

;;; Redefine parts of company

(defmacro company--electric-do (&rest body)
  (declare (indent 0) (debug t))
  `(when (company-manual-begin)
     ,@body))

(defun company-show-doc-buffer ()
  "Temporarily show the documentation buffer for the selection."
  (interactive)
  (let (other-window-scroll-buffer)
    (company--electric-do
      (let* ((selected (nth company-selection company-candidates))
             (doc-buffer (or (company-call-backend 'doc-buffer selected)
                             (error "No documentation available")))
             start)
        (when (consp doc-buffer)
          (setq start (cdr doc-buffer)
                doc-buffer (car doc-buffer)))
        (setq other-window-scroll-buffer (get-buffer doc-buffer))
        (let ((win (display-buffer doc-buffer t)))
          (set-window-start win (if start start (point-min))))))))

(defun company-show-location ()
  "Temporarily display a buffer showing the selected candidate in context."
  (interactive)
  (let (other-window-scroll-buffer)
    (company--electric-do
      (let* ((selected (nth company-selection company-candidates))
             (location (company-call-backend 'location selected))
             (pos (or (cdr location) (error "No location available")))
             (buffer (or (and (bufferp (car location)) (car location))
                         (find-file-noselect (car location) t))))
        (setq other-window-scroll-buffer (get-buffer buffer))
        (with-selected-window (display-buffer buffer t)
          (save-restriction
            (widen)
            (if (bufferp (car location))
                (goto-char pos)
              (goto-char (point-min))
              (forward-line (1- pos))))
          (set-window-start nil (point)))))))

;;; Setup company-coq

(require 'proof-site)

(setq proof-splash-enable nil
      company-coq-disabled-features nil
      company-coq--prettify-abbrevs t)

(put 'company-coq-fold 'disabled nil)

(add-hook 'coq-mode-hook (lambda ()
                           (require 'company-coq)
                           (set-face-attribute 'company-coq-comment-h1-face nil :height 1.5)
                           (set-face-attribute 'company-coq-comment-h2-face nil :height 1.3)
                           (set-face-attribute 'company-coq-comment-h3-face nil :height 1.2)
                           (company-coq-mode)))

(defvar my/github-width/3   '(0.3333 . 275))
(defvar my/github-width/2   '(0.5    . 420))
(defvar my/github-width*2/3 '(0.6666 . 560))

;;; Screenshots

;;;;;;;;;;;;;;;;;;;;;;
;; Prettify-symbols ;;
;;;;;;;;;;;;;;;;;;;;;;

;; With | Without

(my/with-screenshot my/github-width/2 6 "west" "Prettification of math symbols (enabled)." "prettify"
  (insert "Definition PrettySymbols : (nat -> nat -> Prop) :=
  (fun (n m: nat) =>
     forall p, p <> n -> p >= m -> True \\/ False)."))

(my/with-screenshot my/github-width/2 6 "east" "Prettification of math symbols (disabled)." "prettify-disabled"
  (company-coq-features/prettify-symbols -1)
  (insert "Definition PrettySymbols : (nat -> nat -> Prop) :=
  (fun (n m: nat) =>
     forall p, p <> n -> p >= m -> True \\/ False)."))

;;;;;;;;;;;;;;;;;;;;;
;; Auto completion ;;
;;;;;;;;;;;;;;;;;;;;;

;; Tactics withs docs | Options with docs

(my/with-screenshot my/github-width/2 18 "west" "Auto-completion of tactics, with documentation." "refman-tactics"
  (insert "inve")
  (setq-local company-tooltip-limit 5)
  (split-window-vertically 8)
  (my/send-keys "<C-return> C-h"))

(my/with-screenshot my/github-width/2 18 "east" "Auto-completion of commands, with documentation." "refman-commands"
  (insert "SetA")
  (setq-local company-tooltip-limit 5)
  (split-window-vertically 8)
  (my/send-keys "<C-return> C-h"))

;; Local | Modules

(my/with-screenshot my/github-width/2 13 "west" "Auto-completion of local definitions." "defun-completion"
  (insert "Theorem MyVeryOwnTheorem : True. Proof. apply I. Qed.
Definition MyVeryOwnDefinition : nat -> Type. Proof. apply (fun _ => nat). Defined.
Lemma MyVeryOwnLemma : 1 + 1 >= 2. Proof. auto. Qed.
Example MyVeryOwnExample : forall p, False -> p. Proof. tauto. Qed.")
  (my/send-keys "C-c C-/ C-c C-/")
  (insert "\n\nMyV")
  (my/send-keys "<C-return>"))

(my/with-screenshot my/github-width/2 13 "east" "Auto-completion of module names." "modules-completion"
  (my/start-pg-no-windows)
  (insert "Require Import Co.N.Cy.Abs.")
  (my/send-keys "<C-return>"))

;; Hyps | Search | Unicode

(my/with-screenshot my/github-width/3 16 "west" "Auto-completion of hypotheses." "hypotheses-completion"
  (my/start-pg-no-windows)
  (my/insert-with-point "Goal forall (myVar1 myVar2 myVar3: nat), nat.
Proof.
  intros.<|>
  apply my")
  (my/send-keys "C-c <C-return>")
  (my/send-keys "C-x 1 M-> <C-return>"))

(my/with-screenshot my/github-width/3 16 "center" "Auto-completion of search results." "search-completion"
  (my/start-pg-no-windows)
  (my/insert-with-point "Require Import NArith.
Import Plus.
Set Printing Width 1000.
SearchPattern (_ + _ = _).<|>
plus_")
  (my/send-keys "C-l C-l C-c <C-return>")
  (delete-other-windows)
  (with-selected-window (split-window-vertically 10)
    (set-window-buffer-start-and-point nil proof-response-buffer 1 1))
  (with-current-buffer proof-response-buffer
    (visual-line-mode -1))
  (my/send-keys "M-> <C-return>"))

(my/with-screenshot my/github-width/3 16 "east" "Insertion of Unicode symbols." "math-completion"
  (insert "forall α \\bet")
  (my/send-keys "<C-return>"))

;; Tactic notations | Source view

(my/with-screenshot my/github-width/3 13 "west" "Auto-completion of user-defined tactic notations." "ltac-completion"
  (my/start-pg-no-windows)
  (toggle-truncate-lines 1) ;; 55 119
  (my/insert-with-point "Tactic Notation \"myR\" constr(from)
  \"in\" hyp(hyp) := idtac.

Tactic Notation \"myR\" constr(from)
  \"by\" tactic(tac) := idtac.
<|>
myR")
  (put-text-property 54 60 'invisible 'outline)
  (put-text-property 119 125 'invisible 'outline)
  (my/send-keys "C-c <C-return>")
  (my/send-keys "C-x 1 M-< M-> <C-return>")
  (set-window-start nil 1))

(my/with-screenshot my/github-width*2/3 13 "east" "Source browser (w/ patch)." "source-view"
  (my/start-pg-no-windows)
  (my/insert-with-point "Require Import Arith.
<|>le")
  (my/send-keys "C-c <C-return>")
  (my/send-keys "C-x 1 M->")
  (split-window-horizontally 26)
  (my/send-keys "<C-return> C-u 10 <down> C-u 8 <up> C-w")
  (with-current-buffer "*company-coq: documentation*"
    (toggle-truncate-lines 1)
    (message nil)))

;;;;;;;;;;;;;;;;;;;
;; PG extensions ;;
;;;;;;;;;;;;;;;;;;;

;; Deprecated | Titles in comments | Inline docs

(my/with-screencast my/github-width/3 13 "west" 60 1 "Inline docs (quick peek)." "inline-docs"
  (progn
    (my/start-pg-no-windows)
    (company-coq-ask-prover "Set Printing Width 40.")
    (my/insert-with-point "Lemma le_S: forall n m : nat,
 <|>le n m ->
 le n <= (S m).
"))
  (ignore)
  "<menu>")

(my/with-screenshot my/github-width/3 13 "center" "Special comments for titles." "titles" ;; FIXME sizes
  (insert "(***    H1 title    ***)

(*+     H2 title in a     +*)
(*+ slightly smaller font +*)

(*!  H3 title for remarks !*)

(** Documentation comment **)
(* Regular comment *)")
  (setq cursor-type nil))

(my/with-screenshot my/github-width/3 13 "east" "Highlighting of deprecated forms." "deprecated"
  (my/insert-with-point "Set Undo 1.
SearchAbout True.
cutrewrite -> (1 + 1 = 2).
double induction x y.
Save Lemma plus_comm.
assert (x := y).")
  (my/send-keys "M-<")
  (display-local-help t))

;; Error diffs | Documentation of errors

(my/with-screenshot my/github-width/2 16 "west" "Diff of unification errors." "unification"
  (my/start-pg-no-windows)
  (my/insert-with-point "Inductive Tree {T} :=
| Leaf : T -> Tree
| Branch : Tree -> Tree -> Tree.

Fixpoint MakeLargeTree {A} depth (leaf lastleaf:A) :=
match depth with
| O => Leaf lastleaf
| S n => Branch (MakeLargeTree n leaf leaf) (MakeLargeTree n leaf lastleaf)
end.

Inductive TypedTree : @Tree Type -> Type :=
Tr : forall tr, TypedTree tr.

Eval compute in (MakeLargeTree 7 unit nat).

Lemma inhabited_homogeneous:
forall T n (t: T),
inhabited (TypedTree (@MakeLargeTree Type n T T)).
Proof.
intros; constructor.
induction n; simpl; constructor; eauto.
Qed.

Lemma LargeGoal :
inhabited (TypedTree (@MakeLargeTree Type 1 unit nat)).
Proof.
pose (inhabited_homogeneous unit 1 tt) as pr; simpl in *.
exact pr.")
  (my/send-keys "C-c C-b")
  (delete-window (get-buffer-window proof-goals-buffer))
  (my/send-keys "C-x 1")
  (progn
    (company-coq-diff-unification-error)
    (set-window-buffer-with-search proof-script-buffer "Lemma LargeGoal")
    (with-selected-window (split-window-vertically 6)
      (set-window-buffer-with-search proof-response-buffer "The term")
      (with-selected-window (split-window-vertically 5)
        (set-window-buffer nil "*Diff*")))))

(my/with-screenshot my/github-width/2 16 "east" "Documentation of errors." "errors-doc"
  (my/start-pg-no-windows)
  (my/insert-with-point "Require Import Omega.
Goal forall n: nat, exists m, n = m.
<|>  intros; omega.")
  (my/send-keys "C-c <C-return>")
  (my/send-keys "C-c C-n")
  (recenter 1)
  (my/send-keys "C-c C-a C-e")
  (my/send-keys "C-x 1")
  (with-selected-window (split-window-vertically 4)
    (set-window-buffer-with-search "*company-coq: documentation*" "omega can")
    (with-selected-window (split-window-vertically 8)
      (with-current-buffer proof-response-buffer
        (set-window-buffer nil (current-buffer))
        (kill-local-variable 'mode-line-format)))))

;; Outlines | Code folding
;; TODO: outline could be thinner, leaving space for something else (what?)

(my/with-screenshot my/github-width*2/3 18 "west" "Buffer outlines." "outline"
  (insert-file-contents "/usr/local/lib/coq/theories/Arith/Plus.v")
  (rename-buffer "Plus.v")
  (progn
    (my/send-keys "C-c C-,")
    (toggle-truncate-lines 1)
    (message nil)))

(my/with-screencast my/github-width/3 18 "center" 50 1 "Code folding." "folding"
  (my/insert-with-point "<|>Goal forall a b c d e: Prop,
  a -> b -> c -> d -> e ->
  (a /\\ b) /\\ (c /\\ (d /\\ e)).
Proof.
  split.
  - split.
    + trivial.
    + assumption.
  - split.
    + trivial.
    + { split.
        * assumption.
        * auto. }
Qed.

Goal True -> True.
Proof.
  intros; apply I.
Qed.

Goal False -> True.
Proof.
  intros; assumption.
Qed.")
  "C-u 105 C-f"
  "RET" "RET" "RET"
  "C-u 74 C-f"
  "RET" "RET" "RET"
  "M-<"
  "C-c C-/" "C-c C-/ C-c C-/" "C-c C-\\" "C-c C-\\ C-c C-\\");; HACK due to incorrect last-command

(my/with-screencast my/github-width/3 13 "west" 20 8 "Snippets for match branches (Gallina)." "match-function"
  (:split "Fixpoint sum l :=") "RET"
  (:split "miw") "<C-return>" "<C-return> RET"
  (:split "l") "TAB" "<M-return>"
  (:split "[]") "TAB" (:split "0") "TAB <M-return>"
  (:split "h :: t") "TAB" (:split "h + sum t") "M->" ".")

(my/with-screencast my/github-width/3 13 "center" 20 8 "Snippets for match branches (Ltac)." "match-goal"
  (:split "mgw") "<C-return>" "<C-return> RET"
  "<M-S-return>" "TAB" (:split "?a /\\ ?b") "TAB" (:split "?a") "TAB" "RET"
  (:split "destr") "<C-return>" "<C-return> RET" (:split "H; eas") "<C-return>" "<C-return> RET" "M->" ".")

(my/with-screencast my/github-width/3 13 "east" 20 8 "Smart intros." "smart-intros"
  (progn
    (my/start-pg-no-windows)
    (insert "Goal forall x y z: nat,
  x >= y -> y >= z -> x >= z.
Proof.
  ")
    (my/send-keys "C-c <C-return>")
    (proof-shell-wait)
    (my/send-keys "C-x 1 M-< M->"))
  (:split "intros!") "<C-return>" "<C-return> RET")

(kill-emacs)
