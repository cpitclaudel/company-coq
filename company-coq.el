;;; company-coq.el --- Company-mode backend for Proof General's coq-mode

;; Copyright 2015 Clément Pit--Claudel

;;; Commentary:
;;
;; See https://github.com/cpitclaudel/company-coq/ for documentation
;;

;;; Code:

;; Technical notes
;; ===============
;;
;; Sending  commands to  the prover  when it's  already busy  breaks everything.
;; 'proof-shell-handle-delayed-output-hook is  a good  place to  reload symbols,
;; except when an error occurs (in that case the hook runs before all output has
;; been processed.
;;
;; This problem is solved by refusing  to communicate with the prover, unless it
;; is reported as available. When it isn't, the interaction is either abandonned
;; (that's what happens  with documentation, and with completion  if the symbols
;; aren't available yet)) or delayed using  an idle timer (reload; in fact, this
;; one is always wrapped in an idle  timer). To prevent loops due to idle timers
;; firing in succession, reloads are only attempted once.
;;
;; The current implementation uses two hooks:
;;  * 'proof-shell-insert-hook
;;      In this one we check the input to see if it might introduce new symbols
;;      (e.g. [Require ...])
;;  * 'proof-shell-handle-delayed-output-hook
;;      In this one we parse the output to see if it suggests that new symbols
;;      have been introduced (e.g. [... defined])
;;
;; Since these  two hooks are  called into even for  commands issued by  our own
;; code, we only execute their body if  we are not currently already waiting for
;; an answer from the prover (company-coq-asking-question).

(require 'shr)
(require 'company)
(require 'company-math)
(require 'cl-lib)
(require 'yasnippet)

(require 'company-coq-abbrev)

(unless (require 'proof-site nil t)
  (message "company-coq: Unable to load proof-site. Is ProofGeneral installed, and did you add it to your load-path?"))

(defgroup company-coq-opts nil
  "Options for the Coq company mode"
  :group 'company)

(defcustom company-coq-debug nil
  "Debug mode for company-coq."
  :group 'company-coq-opts)

(defcustom company-coq-autocomplete-symbols nil
  "Autocomplete theorem names by periodically querying coq about defined identifiers. This is an experimental feature. It requires a patched version of Coq to work properly; it will be very slow otherwise."
  :group 'company-coq-opts)

(defcustom company-coq-fast nil
  "Indicates whether we have access to a faster, patched REPL"
  :group 'company-coq-opts)

(defcustom company-coq-explicit-placeholders t
  "Show holes using explicit placeholders"
  :group 'company-coq-opts)

(defcustom company-coq-backends '(company-math-symbols-unicode company-coq-keywords)
  "List of backends to use, listed in the order in which you want the results displayed. Note that the first backend to return a prefix superseeds all the others; they all must work with the same prefix."
  :group 'company-coq-opts)

(defvar company-coq-asking-question nil
  "Indicates whether a interaction has been initiated with the prover, to disable the input and output hooks.")

(defvar company-coq-symbols-reload-needed nil
  "Indicates whether a reload might be needed. This variable is
  set from places where immediate reloading is impossible, for example in proof-shell-insert-hook")

(defvar company-coq-defined-symbols nil
  "Keep track of defined symbols.")

(defvar  company-coq-known-keywords nil
  "List of defined Coq syntax forms")

(defconst company-coq-name-regexp-base "[a-zA-Z0-9_.!]") ;; '!' included so that patterns like [intros!] still work

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

(defconst company-coq-doc-tagline "Documentation for symbol %s"
  "Format string for the header of the documentation buffer")

(defconst company-coq-doc-def-sep "\n---\n\n"
  "Separation line between the output of company-coq-doc-cmd and company-coq-def-cmd in the doc buffer.")

(defconst company-coq-dabbrev-placeholders-regexp "#\\|@{\\([^}]+\\)}"
  "Used to match placeholders in dabbrev definitions")

(defconst script-full-path load-file-name
  "Full path of this script")

(defface company-coq-doc-header-face
  '((t :inherit highlight :height 1.2))
  "Face used to highlight the target line in the docs"
  :group 'defaut)

(defface company-coq-doc-tt-face
  '((t :inherit font-lock-keyword-face :weight bold))
  "Face used to highlight the keywords in the docs"
  :group 'defaut)

(defface company-coq-doc-i-face
  '((t :inherit font-lock-variable-name-face :weight bold :slant italic))
  "Face used to highlight the symbol names in the docs"
  :group 'defaut)

(when nil
  (defcustom company-coq-symbol-matching-scheme 'substring
    "The strategy used to look for keywords"
    :group company-coq-opts)

  (defun company-coq-symbol-matching-scheme-is-plain ()
    (equal company-coq-symbol-matching-scheme 'plain)))

(defun company-coq-dbg (format &rest args)
  "Print a message if company-coq-debug is non-nil"
  (when company-coq-debug
    (apply 'message (concat "company-coq: " format) args)))

(defun company-coq-ask-prover (question)
  (when question
    (if (and (company-coq-prover-available) (fboundp 'proof-shell-invisible-cmd-get-result))
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

(defun company-coq-value-or-nil (symbol)
  (and (boundp symbol) (symbol-value symbol)))

(defun company-coq-prover-available ()
  (let ((available (and (not company-coq-asking-question)
                        (fboundp 'proof-shell-available-p)
                        (proof-shell-available-p))))
    (when (not available)
      (company-coq-dbg "company-coq-prover-available: Prover not available"))
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

(defun company-coq-get-pg-keywords-db ()
  (apply #'append
         (mapcar #'company-coq-value-or-nil ;; Don't fail when PG is missing
                 '(coq-tactics-db coq-solve-tactics-db coq-solve-cheat-tactics-db coq-tacticals-db coq-commands-db))))

(defun company-coq-get-own-keywords-db ()
  (apply #'append company-coq-abbrevs-all))

(defun company-coq-normalize-abbrev (kwd)
  (downcase
   (replace-regexp-in-string
    "[ \\.]+\\'" ""
    (replace-regexp-in-string
     (concat " *\\(" company-coq-dabbrev-placeholders-regexp "\\) *") "#"
     kwd))))

(defun company-coq-parse-keywords-db-entry (menuname abbrev insert &optional statech kwreg insert-fun hide)
  (when (or insert insert-fun)
    (propertize (if insert-fun menuname insert)
                'source 'pg
                'insert insert
                'insert-fun insert-fun
                'stripped (company-coq-normalize-abbrev insert)))) ;; TODO: Remove inter-word spaces

(defun company-coq-parse-own-db-entry (abbrev-and-anchor)
  (let ((abbrev (car abbrev-and-anchor))
        (anchor (cdr abbrev-and-anchor)))
    (propertize abbrev
                'source 'own
                'anchor anchor
                'insert abbrev
                'stripped (company-coq-normalize-abbrev abbrev))))

(defun company-coq-abbrev-equal (a1 a2)
  (and (equal (company-coq-read-normalized-abbrev a1)
              (company-coq-read-normalized-abbrev a2))
       (not (equal (company-coq-read-abbrev-source a1)
                   (company-coq-read-abbrev-source a2)))))

(defun company-coq-read-normalized-abbrev (kwd)
  (get-text-property 0 'stripped kwd))

(defun company-coq-read-abbrev-source (kwd)
  (get-text-property 0 'source kwd))

(defun company-coq-union-nosort (test comp key &rest lists)
  (let ((merged  (cl-stable-sort (apply #'append lists) comp :key key))
        (prev    nil))
    (while merged
      (let ((top (pop merged)))
        (when (and prev (funcall test top prev))
          (put-text-property 0 (length top) 'dup t top))
        (setq prev top)))
    (cl-loop for abbrev in (apply #'append lists)
             if (not (get-text-property 0 'dup abbrev))
             collect abbrev)))

(defun company-coq-number (ls)
  (let ((num 0))
    (mapc (lambda (x)
            (put-text-property 0 (length x) 'num num x)
            (setq num (+ 1 num)))
          ls)))

(defun company-coq-get-annotated-keywords ()
  (company-coq-dbg "company-coq-get-annotated-keywords: Called")
  (let ((pg-keywords  (remove nil (mapcar (lambda (db-entry) (apply 'company-coq-parse-keywords-db-entry db-entry))
                                           (company-coq-get-pg-keywords-db))))
        (own-keywords (company-coq-number
                       (mapcar #'company-coq-parse-own-db-entry (company-coq-get-own-keywords-db)))))
     (company-coq-union-nosort
      #'company-coq-abbrev-equal #'string-lessp #'company-coq-read-normalized-abbrev
      own-keywords pg-keywords)))

(defun company-coq-force-reload-keywords ()
  (company-coq-dbg "company-coq-force-reload-keywords: Called")
  (setq company-coq-known-keywords (company-coq-get-annotated-keywords))
  (company-coq-dbg "company-coq-force-reload-keywords: Loaded %s symbols" (length company-coq-known-keywords)))

(defun company-coq-init-keywords ()
  (interactive)
  (company-coq-dbg "company-coq-init-keywords: Loading keywords (if never loaded)")
  (company-coq-init-db 'company-coq-known-keywords 'company-coq-force-reload-keywords))

(defun company-coq-is-lower (str)
  (let ((case-fold-search nil))
    (string-match-p "\\`[[:lower:]]" str)))

(defun company-coq-string-lessp-foldcase (str1 str2)
  (string-lessp (upcase str1) (upcase str2)))

(defun company-coq-string-lessp-symbols (str1 str2)
  (let ((mb1 (equal 0 (get-text-property 0 'match-beginning str1)))
        (mb2 (equal 0 (get-text-property 0 'match-beginning str2))))
    (or (and mb1 (not mb2))
        (and (equal mb1 mb2)
             (company-coq-string-lessp-foldcase str1 str2)))))

(defun company-coq-string-lessp-keywords (str1 str2)
  (let ((mb1 (equal 0 (get-text-property 0 'match-beginning str1)))
        (mb2 (equal 0 (get-text-property 0 'match-beginning str2)))
        (id1 (get-text-property 0 'num str1))
        (id2 (get-text-property 0 'num str2))
        (l1 (company-coq-is-lower str1))
        (l2 (company-coq-is-lower str2)))
    (or (and      l1  (not l2))
        (and (not l1) (not l2) (company-coq-string-lessp-foldcase str1 str2))
        (and      l1       l2  (or (and id1 (not id2))
                                   (and id1 id2 (< id1 id2))
                                   (and (equal id1 id2)
                                        (company-coq-string-lessp-foldcase str1 str2)))))))

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
    (cl-loop for completion in completions
             if (string-match prefix-re completion)
             collect (company-coq-propertize-match completion (match-beginning 0) (match-end 0)))))

(defun company-coq-complete-prefix-fuzzy (prefix completions &optional ignore-case)
  "List elements of COMPLETIONS matching PREFIX"
  (let ((completion-ignore-case ignore-case))
    (company-coq-make-proper-list (completion-pcm-all-completions prefix completions nil (length prefix)))))

(defun company-coq-complete-prefix (prefix completions &optional ignore-case)
  "List elements of COMPLETIONS starting with PREFIX"
  (company-coq-dbg "company-coq-complete-prefix: Completing for prefix %s (%s symbols)" prefix (length completions))
  (let ((completion-ignore-case ignore-case)
        (prefix-len             (length prefix)))
    (mapcar
     (lambda (completion) (company-coq-propertize-match completion 0 prefix-len))
     (all-completions prefix completions))))

(defun company-coq-complete-symbol (prefix)
  "List elements of company-coq-defined-symbols containing PREFIX"
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
  (company-coq-value-or-nil 'proof-shell-proof-completed))

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
  (or (company-coq-value-or-nil 'proof-script-buffer)
      (ignore (company-coq-dbg "Not in scripting mode"))))

(defun company-coq-grab-prefix ()
  ;; Only one grab function; otherwise the first backend in the list of backend shadows the others
  (unless (and (char-after) (memq (char-syntax (char-after)) '(?w ?_)))
    (save-excursion ;; TODO could be optimized
      (when (looking-back company-coq-prefix-regexp (point-at-bol) t)
        (match-string-no-properties 0)))))

(defun company-coq-prefix-symbol ()
  (interactive)
  (company-coq-dbg "company-coq-prefix-symbol: prefix-symbol called")
  (when (and (company-coq-in-coq-mode) (company-coq-in-scripting-mode))
    (company-coq-grab-prefix)))

(defun company-coq-prefix-keyword ()
  (interactive)
  (company-coq-dbg "company-coq-prefix-symbol: prefix-symbol called")
  (when (company-coq-in-coq-mode)
    (company-coq-grab-prefix)))

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

(defun company-coq-meta-symbol (name)
  (company-coq-dbg "company-coq-meta-symbol: Called for name %s" name)
  (let* ((meta (company-coq-join-lines (company-coq-documentation-header name) " " 'string-trim))
         (minibuf-w (window-body-width (minibuffer-window)))
         (meta-trunc (if (> (length meta) minibuf-w)
                         (concat (substring meta 0 (- minibuf-w 3)) "...") meta)))
    (company-coq-dbg "Meta: %s" meta)
    meta-trunc))

(defun company-coq-meta-keyword (name)
  (company-coq-dbg "company-coq-meta-keyword: Called for name %s" name)
  (and (company-coq-get-anchor name)
       (format "C-h: Quick docs")))

(defun company-coq-get-pg-buffer ()
  (get-buffer "*goals*"))

(defun company-coq-get-pg-window ()
  (let ((pg-buffer (company-coq-get-pg-buffer)))
    (when pg-buffer
      (let ((window (get-buffer-window pg-buffer)))
        window))))

(defun company-coq-is-doc-buffer (name action)
  (equal name "*company-documentation*"))

(defun company-coq-display-in-pg-window (buffer alist)
  (company-coq-dbg "Called company-coq-display-in-pg-buffer with %s %s" buffer alist)
  (let ((pg-window (company-coq-get-pg-window)))
    (when pg-window
      ;; Disable dedication; in general, the *goal* buffer isn't dedicated, and
      ;; if it is it's not worth restoring
      (set-window-dedicated-p pg-window nil)
      (set-window-buffer pg-window buffer))
   pg-window))

(defun company-coq-prepare-doc-buffer ()
  (company-coq-dbg "company-prepare-doc-buffer: Called")
  ;; This ensures that we take control when emacs tries to display the doc buffer
  ;; TODO should it be buffer-local
  ;; Unneeded thanks to fix of company-mode
  ;; (add-to-list 'display-buffer-alist (cons #'company-coq-is-doc-buffer
                                           ;; (cons #'company-coq-display-in-pg-buffer nil)))
  (let ((doc-buffer (get-buffer-create "*company-documentation*")))
    (with-current-buffer doc-buffer
      (let ((inhibit-read-only t))
        (remove-overlays)
        (erase-buffer)))
    (company-coq-display-in-pg-window doc-buffer nil)
    doc-buffer))

(defun company-coq-make-title-line ()
  (let ((overlay (make-overlay (point-at-bol) (+ 1 (point-at-eol))))) ;; +1 to cover the full line
    (overlay-put overlay 'face 'company-coq-doc-header-face)))

(defun company-coq-get-anchor (kwd)
  (get-text-property 0 'anchor kwd))

(defun company-coq-annotation-keywords (candidate)
  (let* ((snippet   (company-coq-get-snippet candidate))
         (num-holes (and snippet (get-text-property 0 'num-holes snippet)))
         (prefix    (if (company-coq-get-anchor candidate) "… " "")))
    (if (and (numberp num-holes) (> num-holes 0))
        (format "%s<kwd (%d)>" prefix num-holes)
      (format "%s<kwd>" prefix))))

(defun company-coq-doc-buffer-symbols (name)
  (company-coq-dbg "company-coq-doc-buffer-symbols: Called for name %s" name)
  (let ((doc (company-coq-documentation name))
        (def (company-coq-join-lines (company-coq-definition-header name) "\n")))
    (when (and doc def)
      (let* ((fontized-name (propertize name 'font-lock-face 'company-coq-doc-i-face))
             (doc-tagline (format company-coq-doc-tagline fontized-name))
             (doc-full (concat doc-tagline "\n\n" doc company-coq-doc-def-sep def)))
        (with-current-buffer (company-coq-prepare-doc-buffer)
          (let ((inhibit-read-only t))
            (insert doc-full)
            (when (fboundp 'coq-response-mode)
              (coq-response-mode))
            (goto-char (point-min))
            (company-coq-make-title-line))
          (current-buffer))))))

(defun company-coq-shr-tag-tt (cont)
  (shr-fontize-cont cont 'company-coq-doc-tt-face))

(defun company-coq-shr-tag-i (cont)
  (shr-fontize-cont cont 'company-coq-doc-i-face))

(defun company-coq-doc-keywords-prettify-title (target-point truncate)
  (goto-char (or target-point (point-min)))
  (when target-point
    ;; Remove the star ("*") added by shr
    (delete-char 1)
    (company-coq-make-title-line)
    (when truncate
      ;; Company-mode returns to the beginning of the buffer, so centering
      ;; vertically doesn't work.  Instead, just truncate everything, leaving
      ;; just a bit of room for comments preceeding the tactic if any.
      (forward-line -2)
      (delete-region (point-min) (point)))))

(defun company-coq-doc-keywords-put-html (html-full-path truncate)
  (let ((inhibit-read-only t)
        (doc (with-temp-buffer
               (insert-file-contents html-full-path)
               (libxml-parse-html-region (point-min) (point-max))))
        (shr-width nil)
        (after-change-functions nil)
        (shr-external-rendering-functions '((tt . company-coq-shr-tag-tt)
                                            (i  . company-coq-shr-tag-i))))
    (shr-insert-document doc) ;; This sets the 'shr-target-id property upon finding the shr-target-id anchor
    (company-coq-doc-keywords-prettify-title (next-single-property-change (point-min) 'shr-target-id) truncate)))

(defun company-coq-doc-buffer-keywords (name &optional truncate)
  (interactive)
  (company-coq-dbg "company-coq-doc-buffer-keywords: Called for %s" name)
  (when (fboundp 'libxml-parse-html-region)
    (let* ((anchor         (company-coq-get-anchor name))
           (shr-target-id  (and anchor (concat "hevea_quickhelp" (int-to-string (cdr anchor)))))
           (doc-short-path (and anchor (concat (car anchor) ".html.gz")))
           (doc-full-path  (and doc-short-path
                                (concat (file-name-directory script-full-path) "refman/" doc-short-path))))
      (when doc-full-path
        (with-current-buffer (company-coq-prepare-doc-buffer)
          ;; The window must be visible at this point, to ensure proper html rendering
          (company-coq-doc-keywords-put-html doc-full-path truncate)
          (cons (current-buffer) (point)))))))

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

(defun company-coq-dabbrev-to-yas-format-marker (match regexp)
  (string-match company-coq-dabbrev-placeholders-regexp match)
  (let* ((start      (match-beginning 1))
         (end        (match-end       1))
         (identifier (or (and start end (substring match start end))
                         (and company-coq-explicit-placeholders "_") "")))
    (concat  "${" identifier "}")))

(defun company-coq-dabbrev-to-yas (abbrev)
  (interactive)
  (company-coq-dbg "company-coq-dabbrev-to-yas: Transforming %s" abbrev)
  (let* ((match-num        0)
         (number-matches    (lambda (match)
                              (setq match-num (+ match-num 1))
                              (company-coq-dabbrev-to-yas-format-marker match company-coq-dabbrev-placeholders-regexp)))
         (snippet           (replace-regexp-in-string company-coq-dabbrev-placeholders-regexp number-matches abbrev))
         (ends-with-space   (string-match "[^\\.][[:space:]]+\\'" snippet))
         (suffix            (if (and ends-with-space (equal 0 match-num))
                                (progn (setq match-num (+ match-num 1))
                                       (company-coq-dabbrev-to-yas-format-marker "#" match-num)) ""))
         (final-snippet    (concat snippet suffix)))
    (put-text-property 0 (length final-snippet) 'num-holes match-num final-snippet)
    (company-coq-dbg "company-coq-dabbrev-to-yas: transformed using suffix %s, to %s" suffix final-snippet)
    final-snippet))

(when nil
  (defun company-coq-exit-snippet (char)
    (company-coq-dbg "Exiting snippet (received %s)" char)
    (let ((snippet (first (yas--snippets-at-point))))
      (yas-exit-snippet snippet)))

  ;; FIXME: Should call electric terminator instead of insert
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
             (insert ,char)))))))

(defun company-coq-get-snippet (candidate)
  (let* ((abbrev  (get-text-property 0 'insert candidate))
         (snippet (and abbrev (company-coq-dabbrev-to-yas abbrev))))
    snippet))

(defun company-coq-post-completion-keyword (kwd)
  (let* ((found   (search-backward kwd))
         (start   (match-beginning 0))
         (end     (match-end 0))
         (snippet (company-coq-get-snippet kwd)))
    (when (and found start end snippet)
      (let ((insert-fun (get-text-property 0 'insert-fun kwd)))
        (if insert-fun
            (progn
              (delete-region start end)
              (funcall insert-fun))
          (yas-expand-snippet snippet start end))))))

;; TODO completion at end of full symbol

(defun company-coq-symbols (command &optional arg &rest ignored)
  "A company-mode backend for known Coq symbols."
  (interactive (list 'interactive))
  (company-coq-dbg "symbols backend: called with command %s" command)
  (pcase command
    (`interactive (company-begin-backend 'company-coq-symbols))
    (`prefix (company-coq-prefix-symbol))
    (`candidates (cons :async (lambda (callback) (funcall callback (company-coq-candidates-symbols)))))
    (`sorted t)
    (`duplicates nil)
    (`ignore-case nil)
    (`meta (company-coq-meta-symbol arg))
    (`no-cache t)
    (`match (company-coq-match arg))
    (`annotation "<symb>")
    (`doc-buffer (company-coq-doc-buffer-symbols arg))
    (`comparison-fun #'company-coq-string-lessp-symbols)
    (`require-match 'never)))

;;;###autoload
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
    (`meta (company-coq-meta-keyword arg))
    (`no-cache t)
    (`match (company-coq-match arg))
    (`annotation (company-coq-annotation-keywords arg))
    (`post-completion (company-coq-post-completion-keyword arg))
    (`doc-buffer (car (company-coq-doc-buffer-keywords arg t)))
    (`location (company-coq-doc-buffer-keywords arg nil)) ;; TODO
    (`comparison-fun #'company-coq-string-lessp-keywords)
    (`require-match 'never)))

(defun company-coq-make-backends-alist ()
  (mapcar (lambda (backend) (cons backend ())) (append '(nil) company-coq-backends)))

(defun company-coq-push-to-backend-alist (candidate backends-alist)
  (let* ((company-tag   (get-text-property 0 'company-backend candidate))
         (tag-container (or (assq company-tag backends-alist)
                            (assq nil         backends-alist))))
    (push candidate (cdr tag-container))))

(defun company-coq-sort-in-backends-order (candidates)
  (let ((backends-alist (company-coq-make-backends-alist)))
    (mapc (lambda (candidate) ;; Partition the candidates by backend
            (company-coq-push-to-backend-alist candidate backends-alist))
          candidates)
    (apply #'append
           (mapcar (lambda (pair) ;; Sort the results of each backends, and concat all
                     (cl-stable-sort (cdr pair) (or (and (car pair) (funcall (car pair) 'comparison-fun))
                                                    #'company-coq-string-lessp-foldcase)))
                   backends-alist))))

(defun company-coq-init-symbols-completion () ;; NOTE: This could be made callable at the beginning of every completion.
  (when company-coq-autocomplete-symbols
      ;; PG hooks
      (add-hook 'proof-shell-insert-hook 'company-coq-maybe-proof-input-reload-symbols)
      (add-hook 'proof-shell-handle-delayed-output-hook 'company-coq-maybe-proof-output-reload-symbols)
      ;; General save hook
      (add-hook 'after-save-hook 'company-coq-maybe-reload-symbols nil t)
      ;; Company backend
      (add-to-list 'company-coq-backends #'company-coq-symbols t)
      (when (not company-coq-fast)
        (message "Warning: Symbols autocompletion is an
        experimental feature. Performance won't be good unless
        you use a patched coqtop. If you do, set company-coq-fast
        to true."))))

;;;###autoload
(defun company-coq-initialize (&optional force-load)
  (interactive)
  (when (not (or (company-coq-in-coq-mode) force-load))
    (error "company-coq only works with coq-mode."))

  ;; Enable relevant minor modes
  (company-mode 1)
  (yas-minor-mode 1)

  ;; Set a few company settings
  (setq-local company-idle-delay 0)
  (setq-local company-tooltip-align-annotations t)

  ;; Load identifiers and register hooks
  (company-coq-init-keywords)
  (company-coq-init-symbols-completion)

  ;; Let company know about our backends
  (add-to-list (make-local-variable 'company-backends) company-coq-backends)
  (add-to-list (make-local-variable 'company-transformers) #'company-coq-sort-in-backends-order)

  ;; Bind C-RET to company's autocompletion
  (if (and (boundp 'proof-mode-map) (fboundp 'proof-script-complete))
      (substitute-key-definition #'proof-script-complete #'company-manual-begin proof-mode-map)
    (local-set-key [\C-return] 'company-manual-begin)))

;; TODO add a binding to look up the word at point

(provide 'company-coq)
;;; company-coq.el ends here
