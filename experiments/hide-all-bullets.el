(setq-local hs-allow-nesting t)

(with-current-buffer proof-script-buffer
  (save-excursion
    (goto-char (point-max))
    (while (company-coq-features/code-folding--next-bullet #'re-search-backward)
      (hs-hide-block-at-point)
      (goto-char (point-at-bol)))))
