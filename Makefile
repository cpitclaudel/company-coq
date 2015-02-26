all: elc

elc:
	emacs --batch -L . --script ~/.emacs -f batch-byte-compile company-coq*.el

clean:
	rm -rf *.elc

src: refman elc

refman: clean-refman
	cd /build/coq/ && make doc-html
	python3 html-minify.py refman /build/coq/doc/refman/html/*.html
	python3 extract-tactics.py
	parallel -j8 gzip -9 -- refman/*.html

clean-coq:
	cd /build/coq/ && make docclean

clean-refman:
	rm -rf refman/

deep-clean: clean-refman clean-coq clean

test:
	emacs -mm large-coq-imports.v

ack:
	cd refman && ack "hevea_quickhelp.*" -o | cut -c -80
