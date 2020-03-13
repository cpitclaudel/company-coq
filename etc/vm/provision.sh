#!/usr/bin/env bash

export DEBIAN_FRONTEND=noninteractive

touch /vagrant/provision.log
chown vagrant /vagrant/provision.log
echo '* Starting; see ./provision.log for details.'

echo ""
echo '************************************'
echo '***   Installing base packages   ***'
echo '************************************'

echo '* apt-get update'
add-apt-repository -y ppa:avsm/ppa >> /vagrant/provision.log 2>&1 # OPAM
echo '* apt-get install (needs to download about 90MB)'
apt-get -y install make m4 patch unzip git aspcud camlp4-extra opam emacs virtualbox-guest-dkms virtualbox-guest-utils virtualbox-guest-x11 >> /vagrant/provision.log 2>&1

sudo su vagrant <<-EOF
	cat > ~/gui-setup.sh <<-EOS
		#!/usr/bin/env bash
		apt-get -y install lubuntu-desktop

	    su vagrant <<-EOEOS
			mkdir -p ~/.fonts
			wget -O ~/.fonts/symbola-monospace.ttf https://raw.githubusercontent.com/cpitclaudel/monospacifier/master/fonts/Symbola_monospacified_for_UbuntuMono.ttf
			wget -O /tmp/ubuntu-fonts.zip http://font.ubuntu.com/download/ubuntu-font-family-0.83.zip
			unzip /tmp/ubuntu-fonts.zip -d ~/.fonts/
			fc-cache
		EOEOS
	EOS
	chmod +x ~/gui-setup.sh

	cat >> ~/.profile <<< 'export TERM=xterm-256color'

	echo '************************************'
	echo '*** Downloading and building Coq ***'
	echo '************************************'

	export OPAMYES=true
	echo '* OPAM init'
	opam init --auto-setup --compiler=4.07.0 >> /vagrant/provision.log 2>&1
	eval \$(opam env)
	echo '* OPAM update'
	opam update >> /vagrant/provision.log 2>&1
	echo '* OPAM install (will take a while; maybe 30 minutes)'
	opam install -j2 coq=8.10.2 >> /vagrant/provision.log 2>&1

	echo ""
	echo '************************************'
	echo '***   Setting up Proof General   ***'
	echo '************************************'

	mkdir -p ~/.emacs.d/
	cat > ~/.emacs.d/init.el <<-EOS
		(add-to-list 'load-path "~/.emacs.d/lisp/PG/generic")

		(require 'package)
		(add-to-list 'package-archives '("melpa" . "https://melpa.org/packages/"))
		(package-initialize)

		;; Open .v files with Proof General's coq-mode
		(require 'proof-site)

		;; Load company-coq when opening Coq files
		(add-hook 'coq-mode-hook #'company-coq-mode)

		;; Terminal keybindings
		(with-eval-after-load 'company-coq
		  (define-key company-coq-map (kbd "C-c RET") #'company-coq-proof-goto-point)
		  (define-key company-coq-map (kbd "C-c C-j") #'company-coq-proof-goto-point))

		;; Font fallback
		(when (functionp 'set-fontset-font)
		  (set-face-attribute 'default nil :family "Ubuntu Mono")
		  (set-fontset-font t 'unicode (font-spec :name "Ubuntu Mono"))
		  (set-fontset-font t 'unicode (font-spec :name "Symbola monospacified for Ubuntu Mono") nil 'append))

		;; Basic usability
		(xterm-mouse-mode)
		(load-theme 'tango-dark t)
	EOS

	echo '* package install'
	emacs --batch --load ~/.emacs.d/init.el \
		--eval "(progn (package-refresh-contents) (package-install 'proof-general) (package-install 'company-coq))" >> /vagrant/provision.log 2>&1

	echo ""
	echo '************************************'
	echo '***        Setup complete        ***'
	echo '************************************'

	echo ""
	echo Log into the VM using ‘vagrant ssh’.
    echo You can now run ‘sudo \~/gui-setup.sh’ in the VM to install a GUI, or start using Coq straight away.
EOF

# Local Variables:
# indent-tabs-mode: t
# End:
