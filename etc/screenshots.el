;;; screenshots.el --- Programmable screenshots

;;; Commentary:

;;; Code:

(require 'dash)
(require 'noflet)

(defvar my/fringe-width 8)

(defun my/basic-setup ()
  (ido-mode)
  (tool-bar-mode -1)
  (menu-bar-mode -1)
  (scroll-bar-mode -1)
  (column-number-mode)
  (fringe-mode (cons my/fringe-width my/fringe-width))
  (blink-cursor-mode -1)
  (setq-default cursor-type 'bar
                debug-on-error t
                shr-use-fonts nil
                split-width-threshold 140
                mode-line-format '("%e" mode-line-front-space mode-line-buffer-identification " " ;; Only show company-coq
                                   "(" mode-name (:eval (-filter (lambda (m) (equal (car m) 'company-coq-mode)) minor-mode-alist)) ")"
                                   mode-line-end-spaces))
  (load-theme 'tango t)
  (redisplay t))

(defun my/faces-setup ()
  (set-face-attribute 'default nil :family "Ubuntu Mono" :height 105)
  (set-face-attribute 'mode-line nil :foreground "gray60" :background "black" :height 105)
  (set-face-attribute 'mode-line-inactive nil :foreground "gray60" :background "#404045" :height 105)
  (set-face-attribute 'mode-line-buffer-id nil :foreground "#eab700")
  (set-fontset-font t 'unicode "Ubuntu Mono")
  (set-fontset-font t 'unicode "Symbola Monospacified for Ubuntu Mono" nil 'append))

(defun my/x-window-id ()
  (frame-parameter nil 'outer-window-id))

(eval-and-compile
  (defvar my/github-w 800)
  (defvar my/real-github-w 880))

(defun my/next-insertion-point (&optional end)
  (when (search-forward "<|>" end t)
    (replace-match ""))
  (redisplay t))

(defun my/insert-with-point (str)
  (let ((start (point)))
    (insert str)
    (let ((end (point)))
      (goto-char start)
      (my/next-insertion-point end))))

(defun my/send-keys (keys)
  (redisplay t) ;; Helps company align its popups
  (ignore-errors
    (execute-kbd-macro (kbd (cond
                             ((equal " " keys) "SPC")
                             ((equal "\n" keys) "RET")
                             (t keys))))))

(defun my/frame-file-name (name ext frame-id)
  (setq ext (or ext "png"))
  (expand-file-name (if frame-id
                        (format "%s-%03d.%s" name frame-id ext)
                      (format "%s.%s" name ext))
                    "img"))

(defun my/save-screenshot (name width-spec gravity &optional ext frame-id)
  (force-window-update)
  (redisplay t)
  (let ((fname (my/frame-file-name name ext frame-id)))
    (process-lines "import" "-window" (my/x-window-id) fname)
    (pcase-let* (((seq frame-h frame-w) (mapcar #'string-to-number (process-lines "identify" "-ping" "-format" "%h\n%w" fname)))
                 (target-width (floor (* (car width-spec) my/real-github-w))))
      (when (> frame-w target-width)
        (error "Frame is too large (%d > %d)" frame-w target-width))
      (process-lines "mogrify" "-matte"
                     "-bordercolor" (face-attribute 'fringe :background) "-border" (format "0x%d" my/fringe-width)
                     "-background" "none" "-gravity" gravity "-extent" (format "%dx%d" target-width (+ frame-h (* 2 my/fringe-width)))
                     fname))))

(defun my/save-screencast (name frame-duration frame-ids)
  (apply #'process-lines
         "gifsicle" "--careful" "-O2" (format "--delay=%d" frame-duration)
         "--loop" "--output" (my/frame-file-name name "gif" nil)
         (mapcar (apply-partially #'my/frame-file-name name "gif") frame-ids))
  (dolist (fid frame-ids)
    (ignore-errors
      (delete-file (my/frame-file-name name "gif" fid)))))

(defmacro my/with-coq-buffer-and-stable-windows (frame-w-spec frame-h-columns buf-name capture-prefix &rest body)
  (declare (indent defun))
  `(progn
     (dolist (buf (buffer-list))
       (when (and (buffer-live-p buf)
                  (buffer-name buf)
                  (not (eq (aref (buffer-name buf) 0) ?\s)))
         (kill-buffer buf)))
     (delete-other-windows)
     (set-frame-size nil (floor (cdr ,frame-w-spec)) (floor (* ,frame-h-columns (frame-char-height))) t)
     (redisplay t)
     (let ((--buf-- (get-buffer-create (replace-regexp-in-string "\\.?\\'" "." ,buf-name))))
       (set-buffer --buf--)
       (set-window-buffer nil --buf--)
       (coq-mode)
       (message nil)
       (noflet ((set-window-dedicated-p (&rest args) nil))
         ,@(mapcar (lambda (f) `(progn
                                  (proof-shell-wait)
                                  (set-buffer-modified-p nil)
                                  (set-window-buffer nil --buf--)
                                  (set-window-point nil  (point))
                                  ,f))
                   body)))))

(defmacro my/with-screenshot (frame-w-spec frame-h-columns gravity buf-name capture-prefix &rest body)
  (declare (indent defun))
  `(progn
     (my/with-coq-buffer-and-stable-windows ,frame-w-spec ,frame-h-columns ,buf-name ,capture-prefix
       ,@body)
     (my/save-screenshot ,capture-prefix ,frame-w-spec ,gravity)
     (ignore-errors (proof-shell-exit t))))

(eval-and-compile
  (defun my/compile-screencast-dsl-1 (prog)
    (pcase prog
      ((pred stringp)
       `((my/send-keys ,prog)))
      (`(,':split ,(pred stringp))
       (mapcar (lambda (c) `(my/send-keys ,(char-to-string c))) (string-to-list (cadr prog))))
      ((pred listp)
       (list prog))
      (_ (error "Unknown form %S" prog))))

  (defun my/compile-screencast-dsl (prog)
    (-mapcat #'my/compile-screencast-dsl-1 prog)))

(defvar my/screencast-frame-id nil)

(defun my/save-screencast-frame (name width-factor gravity)
  (my/save-screenshot name width-factor gravity "gif" my/screencast-frame-id)
  (cl-incf my/screencast-frame-id))

(defmacro my/with-screencast (frame-w-spec frame-h-columns gravity frame-duration last-frame-repeats buf-name capture-prefix &rest body)
  (declare (indent defun))
  `(progn
     (my/with-coq-buffer-and-stable-windows ,frame-w-spec ,frame-h-columns ,buf-name ,capture-prefix
       (setq my/screencast-frame-id 0)
       ,@(-mapcat (lambda (form) `(,form (my/save-screencast-frame ,capture-prefix ,frame-w-spec ,gravity)))
                  (my/compile-screencast-dsl body)))
     (let ((last-frame (1- my/screencast-frame-id)))
       ;; repeat last frame to lengthen final image
       (my/save-screencast ,capture-prefix ,frame-duration (append (number-sequence 0 last-frame)
                                                                   (-repeat ,last-frame-repeats last-frame))))
     (ignore-errors (proof-shell-exit t))))

(defun my/start-pg-no-windows ()
  (save-window-excursion
    (noflet ((proof-layout-windows () nil))
      (proof-activate-scripting)))
  (message nil))

(defun set-window-buffer-with-search (buffer-or-name search)
  "As `set-window-buffer' with BUFFER-OR-NAME.
Sets window start using SEARCH."
  (set-window-buffer nil buffer-or-name)
  (set-window-start  nil (with-current-buffer buffer-or-name
                           (goto-char (point-min))
                           (search-forward search)
                           (point))))

(provide 'screenshots)
;;; screenshots.el ends here
