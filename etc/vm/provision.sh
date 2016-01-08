#!/usr/bin/env sh

export DEBIAN_FRONTEND=noninteractive

apt-get -y update
apt-get -y install make m4 patch unzip git aspcud ocaml ocaml-native-compilers camlp4-extra opam emacs virtualbox-guest-dkms virtualbox-guest-utils virtualbox-guest-x11 lxde lightdm

echo "allowed_users=anybody" > /etc/X11/Xwrapper.config
echo "autologin-user=vagrant" >> /etc/lightdm/lightdm.conf
echo "autologin-user-timeout=0" >> /etc/lightdm/lightdm.conf

sudo su vagrant <<EOF
    yes | opam init
    yes | opam repo add coq-core-dev https://coq.inria.fr/opam/core-dev
    yes | opam install -j2 coq.8.5~rc1

    mkdir -p ~/.fonts
    wget -O ~/.fonts/symbola-monospace.ttf https://raw.githubusercontent.com/cpitclaudel/monospacifier/master/fonts/Symbola_monospacified_for_UbuntuMono.ttf
    wget -O /tmp/ubuntu-fonts.zip http://font.ubuntu.com/download/ubuntu-font-family-0.83.zip
    unzip /tmp/ubuntu-fonts.zip -d ~/.fonts/
    fc-cache

    mkdir -p ~/.emacs.d/
    git clone https://github.com/ProofGeneral/PG ~/.emacs.d/lisp/PG
    make -C ~/.emacs.d/lisp/PG

    cat > ~/.emacs.d/init.el <<EOS
(add-to-list 'load-path "~/.emacs.d/lisp/PG/generic")

(require 'package)
(add-to-list 'package-archives '("melpa" . "https://melpa.org/packages/"))
(package-initialize)

;; Open .v files with Proof General's coq-mode
(require 'proof-site)

;; Load company-coq when opening Coq files
(add-hook 'coq-mode-hook #'company-coq-mode)

;; Configure font fallback
(set-face-attribute 'default nil :family "Ubuntu Mono")
(set-fontset-font t 'unicode (font-spec :name "Ubuntu Mono"))
(set-fontset-font t 'unicode (font-spec :name "Symbola monospacified for Ubuntu Mono") nil 'append)
EOS

    emacs --batch --load ~/.emacs.d/init.el --eval "(progn (package-refresh-contents) (package-install 'company-coq))"
EOF
