SANDBOX := ./sandbox
TAGGED_REFMAN_ROOT := /build/coq-8.5-tagged-refman/
PG_GENERIC_ROOT := ~/.emacs.d/lisp/ProofGeneral/generic/
OLD_PG_GENERIC_ROOT := ~/.emacs.d/lisp/ProofGeneral-4.2/generic/
EMACS ?= emacs
CASK = env --unset INSIDE_EMACS EMACS=$(EMACS) cask
COMPANY_COQ_ARGS := --debug-init --eval "(progn (setq-default company-coq--check-forward-declarations t) (add-hook 'coq-mode-hook (lambda () (require 'company-coq) (company-coq-mode))))"

.PHONY: pkg-def

all: elc package

clean: clean-elc clean-package clean-sandbox

sandbox: elc
	$(EMACS) --debug-init -L . $(COMPANY_COQ_ARGS) tests.v

emacs24:
	$(eval EMACS := /usr/bin/emacs24)

test: elc
	$(CASK) exec $(EMACS) -Q \
		-L $(PG_GENERIC_ROOT) -l proof-site -L . $(COMPANY_COQ_ARGS) tests.v

test-old-pg: elc
	$(CASK) exec $(EMACS) -Q \
		-L $(OLD_PG_GENERIC_ROOT) -l proof-site -L . $(COMPANY_COQ_ARGS) tests.v

compatibility: emacs24 elc
	$(CASK) exec $(EMACS) -Q \
		-L $(OLD_PG_GENERIC_ROOT) -l proof-site -L . $(COMPANY_COQ_ARGS) tests.v

clean-elc:
	$(CASK) clean-elc

elc: clean-elc
	$(CASK) build

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

etc: clean-etc
	env --unset COQPATH make -j8 -C $(TAGGED_REFMAN_ROOT) doc-html
	./parse-hevea.py refman/ ./company-coq-abbrev.el.template $(TAGGED_REFMAN_ROOT)/doc/refman/html/Reference-Manual*.html
	parallel -j8 gzip -9 -- refman/*.html

icons:
	etc/rebuild-icons.sh

clean-etc:
	rm -rf refman/*.gz

deep-clean: clean clean-etc
	make -C $(TAGGED_REFMAN_ROOT) docclean

symbols:
	awk -F'\\s+' -v NL=$$(wc -l < etc/symbols) -f etc/symbols.awk < etc/symbols
	awk -F'\\s+' -v NL=$$(wc -l < etc/more-symbols) -f etc/symbols.awk < etc/more-symbols
	awk -F'\\s+' -v NL=$$(wc -l < etc/greek-symbols) -f etc/symbols.awk < etc/greek-symbols
