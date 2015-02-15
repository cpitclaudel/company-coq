;;; company-coq.el --- Company-based completion of Coq symbols

;;; Commentary:

;;; Code:

(require 'company)
(require 'cl-lib)
;; (require 'proof-site)

(defvar company-coq-debug nil
  "Debug mode for company-coq.")

(defvar company-coq-symbols-loading nil
  "Indicates whether the list of symbols is currently being reloaded.")

(defvar company-coq-symbols-reload-needed nil
  "Indicates whether a reload might be needed. This variable is
  set from places where immediate reloading is impossible, for example in proof-shell-insert-hook")

(defvar company-coq-defined-symbols nil
  "Keep track of defined symbols. Updated on save.")

(defconst company-coq-all-symbols-cmd "SearchPattern _"
  "COmmand used to list all symbols.")

(defconst company-coq-doc-cmd "About %s"
  "Command used to retrieve the documentation of a symbol.")

(defconst company-coq-def-cmd "Print %s"
  "Command used to retrieve the definition of a symbol.")

(defconst company-coq-name-regexp-base "[a-zA-Z0-9_.]")

(defconst company-coq-name-regexp (concat "\\(" company-coq-name-regexp-base "+\\)")
  "Regexp used to find symbol names")

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
  (proof-shell-invisible-cmd-get-result question))

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
  (let ((available (and (fboundp 'proof-shell-available-p) (proof-shell-available-p))))
    (when (not available) (company-coq-dbg "company-coq-prover-available: Prover not available"))
    available))

(defun company-coq-get-symbols ()
  "Load symbols by issuing command company-coq-all-symbols-cmd and parsing the results. Do not call if proof process is busy."
  (interactive)
  (with-temp-message "company-coq: Loading symbols..."
  (let* ((name-regexp (concat "^" company-coq-name-regexp ":.*"))
         (output (company-coq-ask-prover company-coq-all-symbols-cmd))
         (lines (company-coq-split-lines output))
         (filtered-lines (cl-remove-if-not (lambda (line) (string-match name-regexp line)) lines))
         (names (mapcar (lambda (line) (replace-regexp-in-string name-regexp "\\1" line)) filtered-lines))
         (names-sorted (sort names 'string<)))
    (company-coq-dbg "Loaded %d symbols" (length names-sorted))
      names-sorted)))

;; TODO don't sort

(defun company-coq-force-reload-symbols ()
  (interactive)
  (company-coq-dbg "company-coq-force-reload-symbols: Reloading symbols (forced)")
  (when company-coq-symbols-loading
    (company-coq-dbg "company-coq-force-reload-symbols: Reloading aborted; another reloading is already in process"))
  (unless company-coq-symbols-loading
    (setq company-coq-symbols-loading t)
    (setq company-coq-symbols-reload-needed nil)
    (unwind-protect
        (setq company-coq-defined-symbols (company-coq-get-symbols))
      (setq company-coq-symbols-loading nil))))

(defun company-coq-init-symbols ()
  (interactive)
  (company-coq-dbg "company-coq-init-symbols: Loading symbols (if never loaded)")
  (when (not company-coq-defined-symbols)
    (company-coq-dbg "company-coq-init-symbols: Symbols not loaded yet, reloading")
    (company-coq-force-reload-symbols)))

(defun company-coq-complete-symbol (prefix)
  "List elements of company-coq-defined-symbols starting with PREFIX"
  (interactive)
  (company-coq-dbg "company-coq-complete-symbol: Completing for prefix %s" prefix)
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
    (company-coq-force-reload-symbols)))

(defun company-coq-maybe-proof-output-reload-symbols ()
  "Updates company-coq-symbols-reload-needed if a proof just
completed or if output mentions new symbol, then calls
company-coq-maybe-reload-symbols."
  (interactive)
  (company-coq-dbg "company-coq-maybe-proof-output-reload-symbols: Reloading symbols (maybe)")
  (let ((is-end-of-def (company-coq-shell-output-is-end-of-def))
        (is-end-of-proof (company-coq-shell-output-is-end-of-proof)))
    (when is-end-of-proof (company-coq-dbg "company-coq-maybe-proof-output-reload-symbols: At end of proof"))
    (when is-end-of-def (company-coq-dbg "company-coq-maybe-proof-output-reload-symbols: At end of definition"))
    (when (or is-end-of-def is-end-of-proof)
      (company-coq-dbg "company-coq-maybe-proof-output-reload-symbols: Setting company-coq-symbols-reload-needed")
      (setq company-coq-symbols-reload-needed t))
    (company-coq-maybe-reload-symbols)))

(defun company-coq-maybe-proof-input-reload-symbols ()
  "Reload symbols if input mentions new symbols"
  (interactive)
  (company-coq-dbg "company-coq-maybe-proof-input-reload-symbols: Reloading symbols (maybe)")
  (let ((is-backwards (company-coq-boundp-equal 'action 'proof-done-retracting))
        (is-import (and (company-coq-boundp-equal 'action 'proof-done-advancing)
                        (company-coq-boundp-string-match company-coq-input-reload-regexp 'string))))
    (when is-backwards (company-coq-dbg "company-coq-maybe-proof-input-reload-symbols: Rewinding"))
    (when is-import (company-coq-dbg "company-coq-maybe-proof-input-reload-symbols: New import"))
    (when (or is-backwards is-import)
      (company-coq-dbg "company-coq-maybe-proof-input-reload-symbols: Setting company-coq-symbols-reload-needed")
      (setq company-coq-symbols-reload-needed t))))

(defun company-coq-grab-symbol ()
  (when (or (looking-at "\\_>") (equal (point) (point-at-bol)))
    (save-excursion ;; TODO could be optimized
      (when (looking-back company-coq-prefix-regexp (point-at-bol) t)
        (match-string 0))))) ;; Only match when either at the beginning of a line, or at end of symbol (according to syntax table)

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
  (company-coq-init-symbols)
  (company-coq-complete-symbol (company-coq-prefix-symbol)))

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
;; TODO Fix import of non-existent modules

(provide 'company-coq)
;;; company-coq.el ends here
