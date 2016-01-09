SANDBOX := ./sandbox
TAGGED_REFMAN_ROOT := /build/coq-8.5-tagged-refman/
PG_GENERIC_ROOT := ~/.emacs.d/lisp/ProofGeneral/generic/
OLD_PG_GENERIC_ROOT := ~/.emacs.d/lisp/ProofGeneral-4.2/generic/
CASK := env --unset INSIDE_EMACS cask
EMACS ?= emacs
COMPANY_COQ_ARGS := --eval "(progn (setq-default company-coq--check-forward-declarations t) (add-hook 'coq-mode-hook (lambda () (require 'company-coq) (company-coq-mode))))"

.PHONY: pkg-def

all: elc package

clean: clean-elc clean-package clean-sandbox

test: elc
	$(EMACS) --debug-init -L . -l company-coq tests.v

baretest: clean-sandbox package
	$(CASK) exec $(EMACS) -Q \
		-L $(PG_GENERIC_ROOT) -l proof-site -L . $(COMPANY_COQ_ARGS) tests.v

baretest-old: elc
	$(CASK) exec $(EMACS) -Q \
		-L $(OLD_PG_GENERIC_ROOT) -l proof-site -L . $(COMPANY_COQ_ARGS) tests.v

elc:
	$(CASK) build

clean-elc:
	$(CASK) clean-elc

pkg-def:
	$(eval PKG := "dist/company-coq-$(shell cask version).tar")

package: pkg-def
	$(CASK) package

clean-package:
	rm -rf dist

screenshots: elc
	$(CASK) exec $(EMACS) --debug-init -Q --load etc/rebuild-screenshots.el

install: package
	$(EMACS) --eval "(package-install-file $(PKG))"

clean-sandbox:
	rm -rf $(SANDBOX)

etc: clean-etc
	env --unset COQPATH make -j8 -C $(TAGGED_REFMAN_ROOT) doc-html
	./parse-hevea.py refman/ ./company-coq-abbrev.el.template $(TAGGED_REFMAN_ROOT)/doc/refman/html/Reference-Manual*.html
	parallel -j8 gzip -9 -- refman/*.html

clean-etc:
	rm -rf refman/*.gz

deep-clean: clean clean-etc
	make -C $(TAGGED_REFMAN_ROOT) docclean

symbols:
	awk -F'\\s+' -v NL=$$(wc -l < etc/symbols) -f etc/symbols.awk < etc/symbols
	awk -F'\\s+' -v NL=$$(wc -l < etc/more-symbols) -f etc/symbols.awk < etc/more-symbols
	awk -F'\\s+' -v NL=$$(wc -l < etc/greek-symbols) -f etc/symbols.awk < etc/greek-symbols
