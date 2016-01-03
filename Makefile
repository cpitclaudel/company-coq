SANDBOX := ./sandbox
TAGGED_REFMAN_ROOT := /build/coq-8.5-tagged-refman/

.PHONY: symbols

all: elc package

clean: clean-elc clean-package clean-sandbox

test: elc
	emacs -mm -L . --debug-init -l company-coq.el tests.v

test24: elc24
	emacs24 -mm -L . --debug-init -l company-coq.el tests.v

elc:
	emacs -q -L . --batch --eval '(setq byte-compile-error-on-warn t)' \
		 --eval "(package-initialize)" -f batch-byte-compile *.el

elc24:
	emacs24 -q -L . --batch --eval '(setq byte-compile-error-on-warn t)' \
		 --eval "(package-initialize)" -f batch-byte-compile *.el

clean-elc:
	rm -rf *.elc

package-name:
	$(eval PKG := company-coq-$(shell sed -n -e 's/.*"\(.*\)".*/\1/' -e 3p company-coq-pkg.el))

package: clean-package package-name
	mkdir -p build/$(PKG)
	cp -R *.el refman build/$(PKG)
	cd build && tar -cf $(PKG).tar $(PKG)

screenshots: elc
	\emacs --debug-init -Q --load etc/rebuild-screenshots.el

clean-package:
	rm -rf build

install:
	emacs \
		-l package \
		--eval "(add-to-list 'package-archives '(\"melpa\" . \"http://melpa.org/packages/\") t)" \
		--eval "(package-refresh-contents)" \
		--eval "(package-initialize)" \
		--eval "(package-install-file \"build/$(PKG).tar\")"

sandbox: clean-sandbox package
	mkdir -p $(SANDBOX)

	emacs24 -Q \
		--eval '(setq user-emacs-directory "$(SANDBOX)")' \
		-L "~/.emacs.d/lisp/ProofGeneral/generic/" \
		-l package \
		-l proof-site \
		--eval "(setq garbage-collection-messages t)" \
		--eval "(add-to-list 'package-archives '(\"gnu\" . \"http://elpa.gnu.org/packages/\") t)" \
		--eval "(add-to-list 'package-archives '(\"melpa\" . \"http://melpa.org/packages/\") t)" \
		--eval "(package-refresh-contents)" \
		--eval "(package-initialize)" \
		--eval "(package-install-file (expand-file-name \"build/$(PKG).tar\"))"

clean-sandbox:
	rm -rf $(SANDBOX)

etc: clean-etc
	export COQPATH=
	make -j8 -C $(TAGGED_REFMAN_ROOT) doc-html
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
