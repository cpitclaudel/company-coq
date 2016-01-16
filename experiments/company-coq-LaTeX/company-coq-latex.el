(require 'dash)
(require 'color)

(defun company-coq-features/latex--substitute-placeholder (kwd repl)
  "Find KWD and replace it with REPL.
Search is case-insensitive."
  (let ((case-fold-search nil))
    (goto-char (point-min))
    (search-forward kwd)
    (replace-match repl t t)))

(defun company-coq-features/latex--default-color (attr)
  "Get ATTR of default face as LaTeX friendly color."
  (let ((color (face-attribute 'default attr)))
    (unless (string-match-p "#......" color)
      (setq color (apply #'color-rgb-to-hex (color-name-to-rgb color))))
    (upcase (substring color 1))))

(defun company-coq-features/latex--img-plist (fname alt)
  "Construct a text attributes plist to display image FNAME.
Uses ALT as help-echo."
  (list 'help-echo alt
        'display `(image :type imagemagick
                         :file ,(expand-file-name fname default-directory)
                         :ascent center)))

(defconst company-coq-features/latex--template-file-name "coq.template.tex"
  "Name of template file for LaTeX rendering.
This file is recursively searched for, starting from the current
script's folder.")

(defun company-coq-features/latex--find-template ()
  "Explore parent directories to locate a rendering template."
  (-if-let* ((script-name buffer-file-name))
      (let ((dir (directory-file-name script-name)))
        (while (not (file-exists-p (expand-file-name company-coq-features/latex--template-file-name dir)))
          (let ((parent (file-name-directory (directory-file-name dir))))
            (when (string= dir parent)
              (error "Not found: %s" company-coq-features/latex--template-file-name))
            (setq dir parent)))
        (expand-file-name company-coq-features/latex--template-file-name dir))
    (error "Buffer must be saved before LaTeX rendering can happen")))

(defvar company-coq-features/latex--template-path nil
  "Path to ‘company-coq-features/latex--template-file-name’.
Usually populated by calling ‘company-coq-features/latex--find-template’.")

(defun company-coq-features/latex--make-file-name (fname ext)
  "Construct a file name from FNAME and EXT."
  (format "%s.%s" fname ext))

(defun company-coq-features/latex--cleanup-temporaries (prefix)
  "Cleanup temporary files created by LaTeX while rendering PREFIX.
Does not remove the image."
  (dolist (ext '("dvi" "log" "aux" "tex"))
    (ignore-errors (delete-file (company-coq-features/latex--make-file-name prefix ext)))))

(defvar company-coq-features/latex--disk-cache-size 100
  "Max number of goal pictures to keep in disk cache.")

(defvar company-coq-features/latex--disk-cache nil
  "List of PNGs present on disk, in order of last use.")

(defun company-coq-features/latex--add-to-cache (png)
  "Move PNG to the front of the disk cache."
  (setq company-coq-features/latex--disk-cache
        (cons png (remove png company-coq-features/latex--disk-cache))))

(defun company-coq-features/latex-evict-cache (&optional keep-n flush-emacs)
  "Remove all images but KEEP-N from disk cache.
KEEP-N defaults to ‘company-coq-features/latex--disk-cache-size’.
Interactively, empty the whole cache.  With FLUSH-EMACS (and
interactively), also empty Emacs' cache."
  (interactive '(0 t)) ;; FIXME check this
  (setq keep-n (or keep-n company-coq-features/latex--disk-cache-size))
  (let ((cache-cdr (nthcdr keep-n company-coq-features/latex--disk-cache)))
    (dolist (file cache-cdr)
      (ignore-errors (delete-file file)))
    (setf cache-cdr nil))
  (when flush-emacs
    (clear-image-cache)))

(defconst company-coq-features/latex--log-buffer "*LaTeX rendering log*"
  "Name of buffer into which LaTeX rendering output is placed.")

(defun company-coq-features/latex--check-process (prog &rest args)
  "Run PROG with ARGS, inserting output in the current buffer.
Raise an error if PROG exits with a non-zero error code."
  (let ((retv (apply #'call-process prog nil (current-buffer) nil args)))
    (unless (eq 0 retv)
      (error "%s failed.  See ‘%s’ for a full trace"
             prog company-coq-features/latex--log-buffer))))

(defun company-coq-features/latex--prepare-tex-file (str fname)
  "Prepare a LaTeX source file from STR; save it as FNAME.
Uses template file in ‘company-coq-features/latex--template-path’."
  (with-temp-buffer
    (insert-file-contents (buffer-local-value 'company-coq-features/latex--template-path proof-script-buffer))
    (company-coq-features/latex--substitute-placeholder "BACKGROUND" (company-coq-features/latex--default-color :background))
    (company-coq-features/latex--substitute-placeholder "FOREGROUND" (company-coq-features/latex--default-color :foreground))
    (company-coq-features/latex--substitute-placeholder "CONTENTS" (concat "\\[" str "\\]"))
    (write-region (point-min) (point-max) fname nil nil)))

(defun company-coq-features/latex--render-tex-file (tex-fname dvi-fname png-fname)
  "Compile and convert LaTeX source file TEX-FNAME.
Uses DVI-FNAME as an intermediate step, before final conversion
to PNG-FNAME."
  (with-current-buffer (get-buffer-create company-coq-features/latex--log-buffer)
    (erase-buffer)
    (company-coq-features/latex--check-process "latex" tex-fname)
    (company-coq-features/latex--check-process "dvipng" "-T" "tight" "-D" "150" "-o" png-fname dvi-fname)))

(defun company-coq-features/latex--prepare-latex (str)
  "Cleanup STR before sending it to LaTeX."
  (pcase-dolist (`(,from . ,to) `(("(" . "\\\\left(")
                                  (")" . "\\\\right)")
                                  (,(concat "[?]\\(" coq-id "\\)\\({[^}]}\\)?") . "\\\\ccEvar{\\1}")))
    (setq str (replace-regexp-in-string from to str t)))
  str)

(defun company-coq-features/latex--render-string (beg end)
  "Render region BEG .. END as a bit of LaTeX code.
Uses the LaTeX template at ‘company-coq-features/latex--template-path’."
  (let* ((str (buffer-substring-no-properties beg end))
         (latex (company-coq-features/latex--prepare-latex str))
         (prefix (format "cc-preview-%s" (md5 latex)))
         (tex-name (company-coq-features/latex--make-file-name prefix "tex"))
         (dvi-name (company-coq-features/latex--make-file-name prefix "dvi"))
         (png-name (company-coq-features/latex--make-file-name prefix "png"))
         (default-directory temporary-file-directory))
    (company-coq-features/latex--add-to-cache (expand-file-name png-name temporary-file-directory))
    (unless (file-exists-p png-name)
      (unwind-protect
          (progn (company-coq-features/latex--prepare-tex-file latex tex-name)
                 (company-coq-features/latex--render-tex-file tex-name dvi-name png-name))
        (company-coq-features/latex--cleanup-temporaries (expand-file-name prefix temporary-file-directory))))
    (let ((inhibit-read-only t))
      (add-text-properties beg end (company-coq-features/latex--img-plist png-name str)))))

(defun company-coq-features/latex--render-goal ()
  "Parse and LaTeX-render the contents of the goals buffer.
Does not run when output is silenced."
  (unless (or (memq 'no-goals-display proof-shell-delayed-output-flags)
              (null proof-script-buffer)
              (not (display-graphic-p)))
    (condition-case-unless-debug err
        (company-coq-with-current-buffer-maybe proof-goals-buffer
          (company-coq-features/latex-evict-cache)
          (pcase-dolist (`(_ _ ,type _ _ ,beg ,end) (company-coq--collect-hypotheses))
            (company-coq-features/latex--render-string beg end))
          (pcase-dolist (`(,type ,beg ,end) (company-coq--collect-subgoals))
            (company-coq-features/latex--render-string beg end)))
      (error (company-coq-features/latex-evict-cache)
             (remove-list-of-text-properties (point-min) (point-max) 'display)
             (message "Error while rendering goals buffers: %S" (error-message-string err))))))

(define-minor-mode company-coq-TeX
  "Render Coq goals using LaTeX."
  :lighter " 🐤—TeX"
  (if company-coq-TeX
      (progn
        (add-hook 'proof-shell-handle-delayed-output-hook #'company-coq-features/latex--render-goal)
        (unless company-coq-features/latex--template-path
          (setq-local company-coq-features/latex--template-path (company-coq-features/latex--find-template))))
    (company-coq-features/latex-evict-cache 0)
    (company-coq-with-current-buffer-maybe proof-goals-buffer
      (remove-list-of-text-properties (point-min) (point-max) '(display)))
    (remove-hook 'proof-shell-handle-delayed-output-hook #'company-coq-features/latex--render-goal)))

(company-coq-TeX)
