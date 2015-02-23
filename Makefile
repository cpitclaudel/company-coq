all: cleangz
	cd /build/coq/ && make doc-html
	python3 html-minify.py refman /build/coq/doc/refman/html/*.html
	python3 extract-tactics.py
	parallel -j8 gzip -9 -- refman/*.html

clean: cleangz
	cd /build/coq/ && make docclean
	rm -f refman/*.html

cleangz:
	rm -f refman/*.gz

view:
	gnome-open /build/coq/doc/refman/html/Reference-Manual.html

test:
	emacs ~/.emacs.d/lisp/own/company-coq/large-coq-imports.v

ack:
	cd ~/.emacs.d/lisp/own/company-coq/refman/ && ack "heveal_quickhelp.*" -o | cut -c -80
