;;; company-coq.el --- Company-based completion of Coq symbols

;;; Commentary:
;;;
;;; Sending commands to the prover when it's already busy breaks everything.
;;; 'proof-shell-handle-delayed-output-hook is a good place to reload stuff,
;;; except when an error occurs (in that case it runs before all output has been
;;; processed.
;;;
;;; This problem is solved by refusing to communicate with the prover, unless it
;;; is reported as available. When it isn't, the interaction is either
;;; abandonned (documentation (and completion if the symbols aren't available
;;; yet)) or delayed using an idle timer (reload; in fact, this one is always
;;; wrapped in an idle timer). To prevent loops due to idle timers firing in
;;; succession, reloads are only attempted once.
;;;
;;; The current implementation uses two hooks:
;;;  * (add-hook 'proof-shell-insert-hook 'company-coq-maybe-proof-input-reload-symbols)
;;;    This parses the input to see if it is might introduce new symbols (e.g. [Require ...])
;;;  * (add-hook 'proof-shell-handle-delayed-output-hook 'company-coq-maybe-proof-output-reload-symbols)
;;;    This parses the output to see if it suggests that new symbols have been introduced (e.g. [... defined])
;;;
;;; Since these two hooks are called into even for commands issued by our own
;;; code, we only execute their body if we are not currently asking a question
;;; to the prover (company-coq-asking-question).

;;; Code:

(require 'company)
(require 'cl-lib)
;; (require 'proof-site)

(defvar company-coq-debug nil
  "Debug mode for company-coq.")

(defvar company-coq-asking-question nil
  "Indicates whether a interaction has been initiated with the prover, to disable the input and output hooks.")

(defvar company-coq-symbols-reload-needed nil
  "Indicates whether a reload might be needed. This variable is
  set from places where immediate reloading is impossible, for example in proof-shell-insert-hook")

(defvar company-coq-defined-symbols nil
  "Keep track of defined symbols. Updated on save.")

(defconst company-coq-name-regexp-base "[a-zA-Z0-9_.]")

(defvar company-coq-fast nil
  "Indicates whether we have access to a faster, patched REPL")

(defconst company-coq-all-symbols-slow-regexp (concat "^\\(" company-coq-name-regexp-base "+\\):.*")
  "Regexp used to filter out lines without symbols in output of SearchPattern")

(defun company-coq-all-symbols-prelude ()
  "Command to run before listing all symbols, using a patched version of Coq"
  (when company-coq-fast "Set Search Minimal"))

(defun company-coq-all-symbols-cmd ()
  "Command used to list all symbols."
  (if company-coq-fast "SearchAny" "SearchPattern _"))

(defun company-coq-all-symbols-coda ()
  "Command to run after listing all symbols, using a patched version of Coq"
  (when company-coq-fast "Unset Search Minimal"))

(defun company-coq-all-symbols-filter-line ()
  "Lambda used to filter each output line"
  (if company-coq-fast
      (lambda (line) (> (length line) 0))
    (lambda (line) (string-match company-coq-all-symbols-slow-regexp line))))

(defun company-coq-all-symbols-extract-names ()
  "Lambda used to extract names from the list of output lines"
  (if company-coq-fast
      'identity
    (lambda (lines) (mapcar (lambda (line) (replace-regexp-in-string company-coq-all-symbols-slow-regexp "\\1" line)) lines))))

(defconst company-coq-doc-cmd "About %s"
  "Command used to retrieve the documentation of a symbol.")

(defconst company-coq-def-cmd "Print %s"
  "Command used to retrieve the definition of a symbol.")

(defconst company-coq-prefix-regexp (concat company-coq-name-regexp-base "*")
  "Regexp used to find symbol prefixes")

(defconst company-coq-undefined-regexp " not a defined object.$"
  "Regexp used to detect missing documentation (useful if database becomes outdated)")

(defconst company-coq-output-reload-regexp "is \\(defined\\|assumed\\)"
  "Regexp used to detect signs that new definitions have been added to the context")

(defconst company-coq-input-reload-regexp "\\(Require\\)\\|\\(Import\\)"
  "Regexp used to detect signs that new definitions will be added to the context")

(defconst company-coq-doc-tagline "DOCUMENTATION FOR SYMBOL '%s'"
  "Format string for the header of the documentation buffer")

(defconst company-coq-doc-def-sep "\n---\n\n"
  "Separation line between the output of company-coq-doc-cmd and company-coq-def-cmd in the doc buffer.")

(defun company-coq-dbg (format &rest args)
  "Print a message if company-coq-debug is non-nil"
  (when company-coq-debug
    (apply 'message (concat "company-coq: " format) args)))

(defun company-coq-ask-prover (question)
  (when question
    (if (company-coq-prover-available)
        (progn
          (setq company-coq-asking-question t)
          (unwind-protect
              (proof-shell-invisible-cmd-get-result question)
            (setq company-coq-asking-question nil)))
      (company-coq-dbg "Prover not available; question discarded"))))

(defun company-coq-split-lines (str)
  (if str (split-string str "\n")))

(defun company-coq-join-lines (lines sep &optional trans)
  (if lines (mapconcat (or trans 'identity) lines sep)))

(defun company-coq-take-while-non-empty (lines)
  (if lines
      (loop for line in lines
            while (not (string-equal line ""))
            collect line)))

(defun company-coq-string-or-undefined (doc)
  "Returns DOC, unless DOC is a message saying that a symbol is undefined"
  (unless (string-match company-coq-undefined-regexp doc) doc))

(defun company-coq-boundp-string-match (regexp symbol)
  (and (boundp symbol)
       (symbol-value symbol)
       (string-match regexp (symbol-value symbol))))

(defun company-coq-boundp-equal (var symbol)
  (and (boundp var) (equal (symbol-value var) symbol)))

(defun company-coq-prover-available ()
  (let ((available (and (not company-coq-asking-question) (fboundp 'proof-shell-available-p) (proof-shell-available-p))))
    (when (not available) (company-coq-dbg "company-coq-prover-available: Prover not available"))
    available))

(defun company-coq-get-symbols ()
  "Load symbols by issuing command company-coq-all-symbols-fast-cmd and parsing the results. Do not call if proof process is busy."
  (interactive)
  (with-temp-message "company-coq: Loading symbols..."
    (let* ((time           (current-time))
           (prelude-output (company-coq-ask-prover (company-coq-all-symbols-prelude)))
           (output         (company-coq-ask-prover (company-coq-all-symbols-cmd)))
           (coda-output    (company-coq-ask-prover (company-coq-all-symbols-coda)))
           (lines          (company-coq-split-lines output))
           (line-filter    (company-coq-all-symbols-filter-line))
           (line-extractor (company-coq-all-symbols-extract-names))
           (filtered-lines (cl-remove-if-not (lambda (line) (funcall line-filter line)) lines))
           (names          (sort (funcall line-extractor filtered-lines) 'string<)))
      (message "Loaded %d symbols (%.03f seconds)" (length names) (float-time (time-since time)))
      names)))

(defun company-coq-force-reload-symbols ()
  (interactive)
  (company-coq-dbg "company-coq-force-reload-symbols: Reloading symbols (forced)")
  (unless (company-coq-prover-available)
    (company-coq-dbg "company-coq-force-reload-symbols: Reloading aborted; proof process busy"))
  (and (company-coq-prover-available)
       (progn
         (setq company-coq-symbols-reload-needed nil)
         (setq company-coq-defined-symbols (company-coq-get-symbols)))))

(defun company-coq-init-symbols ()
  (interactive)
  (company-coq-dbg "company-coq-init-symbols: Loading symbols (if never loaded)")
  (or company-coq-defined-symbols
      (progn
        (company-coq-dbg "company-coq-init-symbols: Symbols not loaded yet, reloading")
        (company-coq-force-reload-symbols))))

(defun company-coq-complete-symbol (prefix)
  "List elements of company-coq-defined-symbols starting with PREFIX"
  (interactive)
  (company-coq-dbg "company-coq-complete-symbol: Completing for prefix %s (%s symbols)" prefix (length company-coq-defined-symbols))
  (all-completions prefix company-coq-defined-symbols))

(defun company-coq-shell-output-is-end-of-def ()
  "Checks whether the output of the last command matches company-coq-output-reload-regexp"
  (company-coq-boundp-string-match company-coq-output-reload-regexp 'proof-shell-last-output))

(defun company-coq-shell-output-is-end-of-proof ()
  "Checks whether proof-general signaled a finished proof"
  (and (boundp 'proof-shell-proof-completed) proof-shell-proof-completed))

(defun company-coq-maybe-reload-symbols ()
  (company-coq-dbg "company-coq-maybe-reload-symbols: Reloading symbols (maybe): %s" company-coq-symbols-reload-needed)
  (when company-coq-symbols-reload-needed
    (run-with-idle-timer 0 nil 'company-coq-force-reload-symbols)))

(defun company-coq-maybe-proof-output-reload-symbols ()
  "Updates company-coq-symbols-reload-needed if a proof just
completed or if output mentions new symbol, then calls
company-coq-maybe-reload-symbols."
  (interactive)
  (company-coq-dbg "company-coq-maybe-proof-output-reload-symbols: Reloading symbols (maybe)")
  (unless company-coq-asking-question
    (let ((is-end-of-def (company-coq-shell-output-is-end-of-def))
          (is-end-of-proof (company-coq-shell-output-is-end-of-proof)))
      (when is-end-of-proof (company-coq-dbg "company-coq-maybe-proof-output-reload-symbols: At end of proof"))
      (when is-end-of-def (company-coq-dbg "company-coq-maybe-proof-output-reload-symbols: At end of definition"))
      (when (or is-end-of-def is-end-of-proof)
        (company-coq-dbg "company-coq-maybe-proof-output-reload-symbols: Setting company-coq-symbols-reload-needed")
        (setq company-coq-symbols-reload-needed t))
      (company-coq-maybe-reload-symbols))))

(defun company-coq-maybe-proof-input-reload-symbols ()
  "Reload symbols if input mentions new symbols"
  (interactive)
  (company-coq-dbg "company-coq-maybe-proof-input-reload-symbols: Reloading symbols (maybe)")
  (unless company-coq-asking-question
    (let ((is-backwards (company-coq-boundp-equal 'action 'proof-done-retracting))
          (is-import (and (company-coq-boundp-equal 'action 'proof-done-advancing)
                          (company-coq-boundp-string-match company-coq-input-reload-regexp 'string))))
      (when is-backwards (company-coq-dbg "company-coq-maybe-proof-input-reload-symbols: Rewinding"))
      (when is-import (company-coq-dbg "company-coq-maybe-proof-input-reload-symbols: New import"))
      (when (or is-backwards is-import)
        (company-coq-dbg "company-coq-maybe-proof-input-reload-symbols: Setting company-coq-symbols-reload-needed")
        (setq company-coq-symbols-reload-needed t)))))

(defun company-coq-grab-symbol ()
  (if (looking-at "\\_>")
      (save-excursion ;; TODO could be optimized
        (when (looking-back company-coq-prefix-regexp (point-at-bol) t)
          (match-string 0)))
    (unless (and (char-after) (memq (char-syntax (char-after)) '(?w ?_))) "")))

(defun company-coq-prefix-symbol ()
  (interactive)
  (company-coq-dbg "company-coq-prefix-symbol: prefix-symbol called")
  (let ((in-coq-mode (derived-mode-p 'coq-mode))
        (in-scripting-mode (and (boundp 'proof-script-buffer) proof-script-buffer)))
    (unless in-coq-mode (company-coq-dbg "company-coq-prefix-symbol: Not in Coq mode"))
    (unless in-scripting-mode (company-coq-dbg "company-coq-prefix-symbol: Not scripting"))
    (when (and in-coq-mode in-scripting-mode)
      (let ((symbol (company-coq-grab-symbol)))
        (company-coq-dbg "Found symbol %s" symbol)
        symbol))))

(defun company-coq-documentation (name)
  (company-coq-dbg "company-coq-documentation: Called for name %s" name)
  (when (company-coq-prover-available)
    (company-coq-string-or-undefined (company-coq-ask-prover (format company-coq-doc-cmd name)))))

(defun company-coq-definition (name)
  (company-coq-dbg "company-coq-definition: Called for name %s" name)
  (when (company-coq-prover-available)
    (company-coq-string-or-undefined (company-coq-ask-prover (format company-coq-def-cmd name)))))

(defun company-coq-get-header (doc)
  (when doc
    (company-coq-take-while-non-empty
     (company-coq-split-lines doc))))

(defun company-coq-documentation-header (name)
  (company-coq-get-header
   (company-coq-documentation name)))

(defun company-coq-definition-header (name)
  (company-coq-get-header
   (company-coq-definition name)))

(defun company-coq-meta (name)
  (company-coq-dbg "company-coq-meta: Called for name %s" name)
  (let* ((meta (company-coq-join-lines (company-coq-documentation-header name) " " 'string-trim))
         (minibuf-w (window-body-width (minibuffer-window)))
         (meta-trunc (if (> (length meta) minibuf-w)
                         (concat (substring meta 0 (- minibuf-w 3)) "...") meta)))
    (company-coq-dbg "Meta: %s" meta)
    meta-trunc))

(defun company-coq-get-pg-buffer ()
  (get-buffer "*goals*"))

(defun company-coq-get-pg-window ()
  (let ((pg-buffer (company-coq-get-pg-buffer)))
    (when pg-buffer
      (let ((window (get-buffer-window pg-buffer)))
        window))))

(defun company-coq-print-doc-in-buffer (doc window buffer)
  (let ((was-dedicated-p (window-dedicated-p window))
        (original-buffer (window-buffer window)))
    (company-coq-dbg "company-coq-print-in-buffer: Called, window dedication is %s" was-dedicated-p)
    (with-current-buffer buffer
      (let ((inhibit-read-only t))
        (erase-buffer)
        (insert doc)
        (coq-response-mode)
        (goto-char (point-min))))
    ;; Disable dedication; in general, the *goal* buffer isn't dedicated, and if
    ;; it is it's not worth restoring
    (set-window-dedicated-p window nil)
    (set-window-buffer window buffer)))

(defun company-coq-print-in-pg-buffer (doc)
  (company-coq-dbg "company-print-in-pg-buffer: Called (%s)" (equal doc nil))
  (when doc
    (let ((window (company-coq-get-pg-window))
          (doc-buffer (get-buffer-create "*company-documentation*")))
      (if window
          (company-coq-print-doc-in-buffer doc window doc-buffer)
        (company-coq-dbg "company-coq-print-in-pg-buffer: Buffer *goals* not found"))
      doc-buffer)))

(defun company-coq-doc-buffer (name)
  (company-coq-dbg "company-coq-doc-buffer: Called for name %s" name)
  (let ((doc (company-coq-documentation name))
        (def (company-coq-join-lines (company-coq-definition-header name) "\n")))
    (when (and doc def)
      (let* ((doc-tagline (format company-coq-doc-tagline name))
             (doc-underline (make-string (length doc-tagline) ?=))
             (doc-full (concat doc-tagline "\n" doc-underline "\n\n" doc company-coq-doc-def-sep def)))
        (company-coq-print-in-pg-buffer doc-full)))))

(defun company-coq-candidates ()
  (interactive)
  (company-coq-dbg "company-coq-candidates: Called")
  (when (company-coq-init-symbols)
    (company-coq-complete-symbol (company-coq-prefix-symbol))))

(defun company-coq (command &optional arg &rest ignored)
  "A company-mode backend for known Coq symbols."
  (interactive (list 'interactive))
  (company-coq-dbg "Coq backend called with command %s" command)
  (pcase command
    (`interactive (company-begin-backend 'coq-company-backend))
    ;; init => Called once per buffer
    ;; prefix => return the prefix at point
    (`prefix (company-coq-prefix-symbol))
    ;; candidates <prefix> => return candidates for this prefix
    (`candidates (cons :async (lambda (callback) (funcall callback (company-coq-candidates)))))
    ;; sorted => t if the list is already sorted
    (`sorted t)
    ;; duplicates => t if there could be duplicates
    (`duplicates nil)
    ;; no-cache <prefix> => t if company shouldn't cache results
    ;; meta <candidate> => short docstring for minibuffer
    (`meta (company-coq-meta arg))
    ;; annotation <candidate> => short docstring for completion buffer
    ;; (`annotation
    ;; doc-buffer <candidate> => put doc buffer in `company-doc-buffer'
    (`doc-buffer (company-coq-doc-buffer arg))
    ;; require-match => Never require a match, even if the user
    ;; started to interact with company. See `company-require-match'.
    (`require-match 'never)
    ;; location <candidate> => (buffer . point) or (file . line-number)
    ;; match <candidate> => for non-prefix based backends
    ;; post-completion <candidate> => after insertion, for snippets
    ))

;; TODO Support autocompletion of commands

(provide 'company-coq)
;;; company-coq.el ends here
