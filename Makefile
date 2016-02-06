SANDBOX := ./sandbox
TAGGED_REFMAN_ROOT := /build/coq-8.5-tagged-refman/
PG_GENERIC_ROOT := ~/.emacs.d/lisp/ProofGeneral/generic/
OLD_PG_GENERIC_ROOT := ~/.emacs.d/lisp/ProofGeneral-4.2/generic/
EMACS ?= emacs
CASK = env --unset INSIDE_EMACS EMACS=$(EMACS) cask
COMPANY_COQ_ARGS := --debug-init --eval "(progn (setq-default company-coq--check-forward-declarations t) (add-hook 'coq-mode-hook (lambda () (require 'company-coq) (company-coq-mode))))"
COQ_85_ARGS := --eval '(setq coq-prog-name "/build/coq-8.5/dist/bin/coqtop")'

.PHONY: pkg-def

all: elc package

clean: clean-elc clean-package

sandbox: elc
	$(EMACS) --debug-init -L . $(COMPANY_COQ_ARGS) tests.v

test: elc
	$(CASK) exec $(EMACS) --debug-init -Q \
		-L $(PG_GENERIC_ROOT) -l proof-site -L . $(COMPANY_COQ_ARGS) tests.v

test-old-pg: elc
	$(CASK) exec $(EMACS) --debug-init -Q \
		-L $(OLD_PG_GENERIC_ROOT) -l proof-site -L . $(COMPANY_COQ_ARGS) tests.v

emacs243:
	$(eval EMACS := /build/emacs-24.3/src/emacs)

emacs245:
	$(eval EMACS := /build/emacs-24.5/src/emacs)

compatibility: emacs243 elc
	$(CASK) exec $(EMACS) --debug-init -Q \
		-L $(PG_GENERIC_ROOT) -l proof-site -L . $(COQ_85_ARGS) $(COMPANY_COQ_ARGS) tests.v

full-compatibility: emacs243 elc
	$(CASK) exec $(EMACS) --debug-init -Q \
		-L $(OLD_PG_GENERIC_ROOT) -l proof-site -L . $(COQ_85_ARGS) $(COMPANY_COQ_ARGS) tests.v

update:
	$(CASK) install
	$(CASK) update

pkg-file:
	$(CASK) pkg-file

clean-elc:
	$(CASK) clean-elc

elc: update clean-elc pkg-file
	$(CASK) build

pkg-def:
	$(eval PKG := "dist/company-coq-$(shell cask version).tar")

package: pkg-def
	$(CASK) package

clean-package:
	rm -rf dist

screenshots: elc
	$(CASK) exec $(EMACS) --debug-init -Q -L $(PG_GENERIC_ROOT) --load etc/rebuild-screenshots.el

screenshots-8.5: elc
	$(CASK) exec $(EMACS) --debug-init -Q -L $(PG_GENERIC_ROOT) $(COQ_85_ARGS) --load etc/rebuild-screenshots.el

screenshots-8.5-24.5: emacs245 elc
	$(CASK) exec $(EMACS) --debug-init -Q \
		-L $(OLD_PG_GENERIC_ROOT) -L . $(COQ_85_ARGS) $(COMPANY_COQ_ARGS) --load etc/rebuild-screenshots.el

# find ./.cask/ -type d -name elpa -exec rm -rf {} +
pkg-install: elc package
	rm -rf .emacs.d
	mkdir .emacs.d
	$(CASK) exec $(EMACS) --debug-init -Q \
		--eval '(setq user-init-directory "./.emacs.d/")' \
		--eval '(package-initialize)' \
		--eval '(package-install-file $(PKG))' \
		-L $(OLD_PG_GENERIC_ROOT) -l proof-site $(COMPANY_COQ_ARGS) tests.v

etc: clean-etc
	env --unset COQPATH make -j8 -C $(TAGGED_REFMAN_ROOT) doc-html
	./etc/parse-hevea.py refman/ ./company-coq-abbrev.el.template $(TAGGED_REFMAN_ROOT)/doc/refman/html/Reference-Manual*.html
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

check-patches:
	etc/check-patches.sh
