# company-coq

Company backend for Proof-General's Coq mode. Setup should be pretty straightforward, although the most advanced features require a patched version of coqtop.

## Features

* Auto-completion of [math symbols](img/tactic-completion-doc.png) (using company-math)
* Easy access to [Proof-General's templates](img/lemma-completion.png) (using yasnippet)
* Auto-completion of (most of) Coq's [tactics](img/command-completion-doc.png) and [commands](img/symbol-completion-doc.png), with snippets auto-extracted from the manual.
* [Documentation](img/keyword-completion-doc.png) for (most) auto-completion entries, with excerpts from the manual shown directly in Emacs.

Advanced features (requires a patched version of `coqtop`:

* Auto-completion of all known [theorem and symbol names](img/symbol-completion-doc.png), with [inline documentation](img/symbol-completion.png).

## Screenshots

### Autocompletion of tactics with documentation

<img src="img/tactic-completion-doc.png" alt="Autocompletion of tactics with documentation" />

### Autocompletion of commands with documentation

<img src="img/keyword-completion-doc.png" alt="Autocompletion of commands with documentation" />

### Auto insertion of Proof-General's templates

<img src="img/lemma-completion.png" alt="Auto insertion of Proof-General's templates" />

### Unicode math symbols

<img src="img/math-completion.png" alt="Unicode math symbols" />

### Autocompletion of symbol names (w/ patched `coqtop`, see notes)

<img src="img/symbol-completion.png" alt="Autocompletion of symbol names" />

(notice the help string in the mini-buffer)

<img src="img/symbol-completion-doc.png" alt="Autocompletion of symbol names with documentation" />

## Setup

### `Coq`

```bash
sudo apt-get install coq
```

### `Proof-General`

```bash
sudo apt-get install proof-general
```

(or [from source](http://proofgeneral.inf.ed.ac.uk/releases/ProofGeneral-4.2.tgz))

### `CompAny`, `YASnippet`

```elisp
M-x package-install RET company RET
M-x package-install RET company-math RET
M-x package-install RET yasnippet RET
```

### `company-coq`

```bash
mkdir -p ~/.emacs.d/lisp/
git clone git@github.com:cpitclaudel/company-coq.git ~/.emacs.d/lisp/company-coq
```

## Configuration

Add the following to your `.emacs`

```elisp
(package-initialize)

(add-to-list 'load-path "~/.emacs.d/lisp/ProofGeneral/generic/")
(add-to-list 'load-path "~/.emacs.d/lisp/company-coq/")

(add-to-list
 'auto-mode-alist
 '("\\.v\\'" . (lambda ()
                 (require 'proof-site)
                 (coq-mode))))

(add-hook 'coq-mode-hook (lambda ()
                           (require 'company-coq)
                           (company-coq-initialize)))
```

### Autocompleting symbols

The procedure above will give you auto-completion and documentation for tactics and commands, but not for theorem names and symbols. To get the latter, add the following to your `.emacs`, before `(company-coq-initialize)`:

```elisp
(setq company-coq-autocomplete-symbols t)
```

This feature won't work well unless you build and use a [patched coq REPL](https://github.com/cpitclaudel/coq/tree/V8.4pl2-SearchAny).


## Quick start guide

`company-coq` should be pretty transparent. Completion windows will pop up when `company-coq` has suggestions to make. By default, this would be when you start writing a tactic name, or a command. If you want to manually invoke completion from time to time, you can add the following to your `.emacs`:

```elisp
(add-hook 'company-mode-hook (lambda ()
                               (local-set-key [\C-return] 'company-manual-begin)))
```

Once auto-completion has started, use <kbd>RET</kbd> to select a completion, or <kbd>C-g</kbd> to interrupt completion. Pressing <kbd>C-h</kbd> or <kbd>&lt;f1></kbd> displays documentation for the currently highlighted identifier.

Selecting a completion generally inserts a snippet with holes at the current point (`company-coq` uses `yasnippet` as the snippet backend). You can move between holes by using <kbd>&lt;tab></kbd> and <kbd>S-&lt;tab></kbd>.
