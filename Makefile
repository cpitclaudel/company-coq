SANDBOX := ./sandbox

all: elc package

clean: clean-elc clean-package clean-sandbox

test:
	emacs -mm large-coq-imports.v

elc:
	emacs --batch -L . --script ~/.emacs -f batch-byte-compile *.el

clean-elc:
	rm -rf *.elc

package: clean-package
	$(eval PKG := company-coq-$(shell sed -n -e 's/.*"\(.*\)".*/\1/' -e 3p company-coq-pkg.el))
	mkdir -p build/$(PKG)
	cp -R *.el refman build/$(PKG)
	cd build && tar -cf $(PKG).tar $(PKG)

clean-package:
	rm -rf build

sandbox: clean-sandbox package
	mkdir -p $(SANDBOX)

	emacs -Q \
		--eval '(setq user-emacs-directory "$(SANDBOX)")' \
		-L "~/.emacs.d/lisp/ProofGeneral/generic/" \
		-l package \
		-l proof-site \
		--eval "(setq garbage-collection-messages t)" \
		--eval "(add-to-list 'package-archives '(\"gnu\" . \"http://elpa.gnu.org/packages/\") t)" \
		--eval "(add-to-list 'package-archives '(\"melpa\" . \"http://melpa.org/packages/\") t)" \
		--eval "(package-refresh-contents)" \
		--eval "(package-initialize)" \
		--eval "(package-install-file \"build/$(PKG).tar\")"

clean-sandbox:
	rm -rf $(SANDBOX)

etc: clean-etc
	cd /build/coq/ && make doc-html
	python3 html-minify.py refman /build/coq/doc/refman/html/*.html
	python3 extract-tactics.py
	parallel -j8 gzip -9 -- refman/*.html

clean-etc:
	rm -rf refman/

deep-clean: clean clean-etc
	cd /build/coq/ && make docclean

ack:
	cd refman && ack "hevea_quickhelp.*" -o | cut -c -80
