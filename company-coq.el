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
  "Keep track of defined symbols.")

(defvar  company-coq-known-keywords nil
  "List of defined Coq syntax forms")

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

(defvar company-coq-explicit-placeholders t
  "Show holes using explicit placeholders")

(defconst company-coq-dabbrev-placeholders-regexp "#\\|@{\\([^}]+\\)}"
  "Used to match placeholders in dabbrev definitions")

(when nil
  (defvar company-coq-symbol-matching-scheme 'substring
    "The strategy used to look for keywords")

  (defun company-coq-symbol-matching-scheme-is-plain ()
    (equal company-coq-symbol-matching-scheme 'plain)))

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
      (cl-loop for line in lines
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

(defun company-coq-init-db (db initfun)
  (interactive)
  (company-coq-dbg "company-coq-init-db: Loading %s (if nil; currently has %s elems)" db (length (symbol-value db)))
  (or (symbol-value db)
      (progn
        (company-coq-dbg "company-coq-init-db: reloading")
        (funcall initfun))))

(defun company-coq-init-symbols ()
  (interactive)
  (company-coq-dbg "company-coq-init-symbols: Loading symbols (if never loaded)")
  (company-coq-init-db 'company-coq-defined-symbols 'company-coq-force-reload-symbols))

(defun company-coq-get-keywords-db ()
  (let* ((db-symbols '(coq-tactics-db coq-solve-tactics-db coq-solve-cheat-tactics-db coq-tacticals-db coq-commands-db)))
    (or (apply 'append (mapcar (lambda (x) (and (boundp x) (symbol-value x)))
                               db-symbols))
        (ignore (company-coq-dbg "company-coq-get-db: coq databases are nil or unbound")))))

(defun company-coq-parse-keywords-db-entry (menuname abbrev insert &optional statech kwreg insert-fun hide)
;;  (add-text-properties menuname 0 (length menuname) '(insert insert) menuname))
  (propertize menuname 'insert insert)) ;; TODO: Remove inter-word spaces

(defun company-coq-get-annotated-keywords ()
  (company-coq-dbg "company-coq-get-annotated-keywords: Called")
  (mapcar (lambda (db-entry)
            (apply 'company-coq-parse-keywords-db-entry db-entry))
          (company-coq-get-keywords-db))) ;; TODO sort ;; TODO handle "intros!"

(defun company-coq-force-reload-keywords ()
  (company-coq-dbg "company-coq-force-reload-keywords: Called")
  (setq company-coq-known-keywords (company-coq-get-annotated-keywords))
  (company-coq-dbg "company-coq-force-reload-keywords: Loaded %s symbols" (length company-coq-known-keywords)))

(defun company-coq-init-keywords ()
  (interactive)
  (company-coq-dbg "company-coq-init-keywords: Loading keywords (if never loaded)")
  (company-coq-init-db 'company-coq-known-keywords 'company-coq-force-reload-keywords))

(defun company-coq-string-lessp-foldcase (str1 str2)
  (let ((mb1 (equal 0 (get-text-property 0 'match-beginning str1)))
        (mb2 (equal 0 (get-text-property 0 'match-beginning str2))))
    (or (and mb1 (not mb2))
        (and (equal mb1 mb2) (string-lessp (upcase str1) (upcase str2))))))

(defun company-coq-make-proper-list (improper-list)
  (let ((last-cell (last improper-list)))
    (setcdr last-cell nil)
    improper-list))

(defun company-coq-propertize-match (match beginning end)
  (company-coq-dbg "company-coq-propertize-match: %s %s %s" match beginning end)
  (put-text-property 0 (length match) 'match-beginning beginning match)
  (put-text-property 0 (length match) 'match-end end match)
  match)

(defun company-coq-complete-prefix-substring (prefix completions &optional ignore-case)
  "List elements of COMPLETIONS containing with PREFIX"
  (let ((completion-ignore-case ignore-case)
        (case-fold-search       ignore-case)
        (prefix-re              (regexp-quote prefix)))
    (sort (cl-loop for completion in completions
                   if (string-match prefix-re completion)
                   collect (company-coq-propertize-match completion (match-beginning 0) (match-end 0)))
          #'company-coq-string-lessp-foldcase)))

(defun company-coq-complete-prefix-fuzzy (prefix completions &optional ignore-case)
  "List elements of COMPLETIONS matching PREFIX"
  (let ((completion-ignore-case ignore-case))
    (company-coq-make-proper-list (completion-pcm-all-completions prefix completions nil (length prefix)))))

(defun company-coq-complete-prefix (prefix completions &optional ignore-case)
  "List elements of COMPLETIONS starting with PREFIX"
  (company-coq-dbg "company-coq-complete-prefix: Completing for prefix %s (%s symbols)" prefix (length completions))
  (let ((completion-ignore-case ignore-case)
        (prefix-len             (length prefix)))
    (sort (mapcar
           (lambda (completion) (company-coq-propertize-match completion 0 prefix-len))
           (all-completions prefix completions))
          #'string<)))

(defun company-coq-complete-symbol (prefix)
  "List elements of company-coq-defined-symbols starting with PREFIX"
  (interactive)
  (company-coq-complete-prefix-substring prefix company-coq-defined-symbols))

(defun company-coq-complete-keyword (prefix)
  "List elements of company-coq-defined-symbols starting with PREFIX"
  (interactive)
  (company-coq-complete-prefix prefix company-coq-known-keywords))

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

(defun company-coq-in-coq-mode ()
  (or (derived-mode-p 'coq-mode)
      (ignore (company-coq-dbg "Not in Coq mode"))))

(defun company-coq-in-scripting-mode ()
  (or (and (boundp 'proof-script-buffer) proof-script-buffer)
      (ignore (company-coq-dbg "Not in scripting mode"))))

(defun company-coq-grab-symbol ()
  (if (looking-at "\\_>")
      (save-excursion ;; TODO could be optimized
        (when (looking-back company-coq-prefix-regexp (point-at-bol) t)
          (match-string-no-properties 0)))
    (unless (and (char-after) (memq (char-syntax (char-after)) '(?w ?_))) "")))

(defun company-coq-grab-keyword ()
  (company-grab-symbol)) ;; Works because '.' is not part of symbols in Coq mode. If that bug was fixed, then this should be swapped with company-coq-grab-symbol

(defun company-coq-prefix (conditions match-function)
  (when conditions
    (let ((prefix (funcall match-function)))
      (company-coq-dbg "Found prefix %s" prefix)
      prefix)))

(defun company-coq-prefix-symbol ()
  (interactive)
  (company-coq-dbg "company-coq-prefix-symbol: prefix-symbol called")
  (company-coq-prefix (and (company-coq-in-coq-mode) (company-coq-in-scripting-mode)) 'company-coq-grab-symbol))

(defun company-coq-prefix-keyword ()
  (interactive)
  (company-coq-dbg "company-coq-prefix-symbol: prefix-symbol called")
  (company-coq-prefix (company-coq-in-coq-mode) 'company-coq-grab-keyword))

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

(defun company-coq-candidates-symbols ()
  (interactive)
  (company-coq-dbg "company-coq-symbols-candidates: Called")
  (when (company-coq-init-symbols)
    (company-coq-complete-symbol (company-coq-prefix-symbol))))

(defun company-coq-candidates-keywords ()
  (interactive)
  (company-coq-dbg "company-coq-symbols-candidates: Called")
  (when (company-coq-init-keywords)
    (company-coq-complete-keyword (company-coq-prefix-keyword))))

(defun company-coq-match (completion)
  (company-coq-dbg "company-coq-match: matching %s" completion)
  (get-text-property 0 'match-end completion))
  ;; (let ((prefix (company-coq-prefix-symbol)))
    ;; (print prefix))
    ;; (print (completion-pcm-all-completions prefix '(completion) nil (length prefix))))
  ;; nil)
  ;; (let* ((prefix          (company-coq-prefix-symbol))
         ;; (completions     (completion-pcm-all-completions prefix '(completion) nil (length prefix)))
         ;; (annotated-compl (car completions)))
    ;; (company-coq-dbg "Annotated compl is %s / %s / %s / %s" prefix completion completions annotated-compl)
    ;; (and annotated-compl (next-single-property-change 0 'font-lock-face annotated-compl))))

(defun company-coq-dabbrev-to-yas-format-marker (match match-num)
  (string-match company-coq-dabbrev-placeholders-regexp match)
  (let* ((start      (match-beginning 1))
         (end        (match-end       1))
         (identifier (or (and start end (substring match start end))
                         (and company-coq-explicit-placeholders "_")))
         (format-str (if identifier (concat  "${%d:" identifier "}") "$%d")))
    (format format-str match-num)))

(defun company-coq-dabbrev-to-yas (abbrev)
  (interactive)
  (company-coq-dbg "company-coq-dabbrev-to-yas: Transforming %s" abbrev)
  (let* ((match-num        0)
         (number-matches   (lambda (match)
                             (setq match-num (+ match-num 1))
                             (company-coq-dabbrev-to-yas-format-marker match match-num)))
         (snippet          (replace-regexp-in-string company-coq-dabbrev-placeholders-regexp number-matches abbrev))
         ;;(clean-snippet  (replace-regexp-in-string "[[:space:]]*\\'" "" snippet))
         ;;(ends-with-dot  (string-match "\\.[[:space:]]*\\'" snippet))
         (ends-with-space  (string-match "[^\\.][[:space:]]+\\'" snippet))
         (suffix           (if (and ends-with-space (equal 0 match-num))
                               (company-coq-dabbrev-to-yas-format-marker "#" 1) ""))
         (final-snippet    (concat snippet suffix)))
    (company-coq-dbg "company-coq-dabbrev-to-yas: transformed using suffix %s, to %s" suffix final-snippet)
    final-snippet))
;; TODO support other types of annotations
;; TODO: fix rewrite-all

(when nil
  (defun company-coq-exit-snippet (char)
    (company-coq-dbg "Exiting snippet (received %s)" char)
    (let ((snippet (first (yas--snippets-at-point))))
      (yas-exit-snippet snippet)))

  (defmacro company-coq-register-snippet-terminator (char)
    `(progn
       (company-coq-dbg "registering %s as a snippet terminator" ,char)
       (when (boundp 'yas-keymap)
         ;;(make-local-variable 'yas-keymap)
         (define-key yas-keymap (kbd ,char)
           (lambda ()
             (interactive)
             (and (fboundp 'company-coq-exit-snippet)
                  (company-coq-exit-snippet ,char))
             (insert ,char)))))) ;; FIXME: Should call electric terminator instead of insert
  )

(defun company-coq-post-completion-keyword (kwd)
  (let* ((found  (search-backward kwd))
         (abbrev (get-text-property 0 'insert kwd)))
    (when (and found abbrev)
      (delete-region (match-beginning 0) (match-end 0))
      ;; (when (boundp 'yas-keymap) ;; Make ; and . exit completion
        ;; (company-coq-register-snippet-terminator ";")
        ;; (company-coq-register-snippet-terminator "."))
      (yas-expand-snippet (company-coq-dabbrev-to-yas abbrev)))))

;; FIXME coq-symbols complete at end of full symbol

(defun company-coq-symbols (command &optional arg &rest ignored)
  "A company-mode backend for known Coq symbols."
  (interactive (list 'interactive))
  (company-coq-dbg "symbols backend: called with command %s" command)
  (pcase command
    (`interactive (company-begin-backend 'company-coq-symbols))
    (`prefix (company-coq-prefix-symbol))
    (`candidates (company-coq-candidates-symbols))
    (`sorted t)
    (`duplicates nil)
    (`ignore-case nil)
    (`meta (company-coq-meta arg))
    (`no-cache t)
    (`match (company-coq-match arg))
    (`doc-buffer (company-coq-doc-buffer arg))
    (`require-match 'never)))

(defun company-coq-keywords (command &optional arg &rest ignored)
  "A company-mode backend for Coq keywords."
  (interactive (list 'interactive))
  (company-coq-dbg "keywords backend: called with command %s" command)
  (pcase command
    (`interactive (company-begin-backend 'company-coq-keywords))
    (`prefix (company-coq-prefix-keyword))
    (`candidates (company-coq-candidates-keywords))
    (`sorted t)
    (`duplicates nil)
    (`ignore-case nil)
    (`no-cache t)
    (`match (company-coq-match arg))
    (`post-completion (company-coq-post-completion-keyword arg))
    (`require-match 'never)))

(defvar company-coq-backends '(company-math-symbols-unicode company-coq-keywords company-coq-symbols)
  ;;'((lambda (&rest args) (company-coq-async-wrapper #'company-math-symbols-unicode args)))
  "List of backends to use")


(defun company-coq (command &optional arg &rest more-args)
  "A backend that mixes results from company-coq-symbols and company-coq-keywords."
  (interactive (list 'interactive))
  (company-coq-dbg "meta-backend: called with command %s" command)
  (lexical-let ((arg arg) ;; Rebind to use in lambda
                (more-args more-args))
    (pcase command
      (`interactive (company-begin-backend 'company-coq))
      (`sorted     t)
      (`duplicates nil)
      (`no-cache   t)
      (`candidates (cons :async
                         (lambda (callback)
                           (funcall callback (apply #'company--multi-backend-adapter
                                                    company-coq-backends
                                                    'candidates arg more-args)))))
      (_           (apply #'company--multi-backend-adapter
                          company-coq-backends
                          command arg more-args)))))

;; FIXME '.' in symbol name

(provide 'company-coq)
;;; company-coq.el ends here
