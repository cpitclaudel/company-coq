# company-coq

Company backend for Proof-General's Coq mode. Setup should be pretty straightforward, although the most advanced features require a patched version of coqtop.

## Features

* Auto-completion of [math symbols](img/tactic-completion-doc.png) (using company-math)
* Easy access to [Proof-General's templates](img/lemma-completion.png) (using yasnippet)
* Auto-completion of (most of) Coq's [tactics](img/command-completion-doc.png) and [commands](img/symbol-completion-doc.png), with snippets auto-extracted from the manual.
* [Documentation](img/keyword-completion-doc.png) for (most) auto-completion entries, with excerpts from the manual shown directly in Emacs.

Advanced features (requires a patched version of `coqtop`):

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

Note: You need a version of Emacs >= 24 for this to work properly. You can check which version you are running with <kbd>M-x emacs-version RET</kbd>

### `Coq`

```bash
sudo apt-get install coq
```

### `Proof-General`

```bash
sudo apt-get install proof-general
```

(or [from source](http://proofgeneral.inf.ed.ac.uk/releases/ProofGeneral-4.2.tgz))

### `company-coq`

```elisp
M-x package-install RET company-coq RET
```

<small>
Note that `company-coq` is on [MELPA](http://melpa.org/#/getting-started). If you don't have it, add the following to your `.emacs` and reload it before running the commands above:

```elisp
(require 'package)
(add-to-list 'package-archives '("melpa" . "http://melpa.org/packages/") t)
(package-initialize)
```
</small>

Compiling the dependencies of `company-coq` will produce a few warnings. That's ok.

## Configuration

Add the following to your `.emacs`

```elisp
(package-initialize)

;; Open .v files with Proof-General's coq-mode
(require 'proof-site)

;; Load company-coq when opening Coq files
(add-hook 'coq-mode-hook (lambda () (company-coq-initialize)))
```

## Quick start guide

`company-coq` should be pretty transparent. Completion windows will pop up when `company-coq` has suggestions to make. By default, this would be when you start writing a tactic name or a command. You can also launch manual completion by using <kbd>C-RET</kbd> (or whatever was originally assigned to `proof-script-complete` in Coq mode).

Once auto-completion has started, the following key bindings are available:

* <kbd>RET</kbd> selects a completion
* <kbd>C-g</kbd> interrupts completion.
* <kbd>C-h</kbd> and <kbd>&lt;f1></kbd> display documentation for the currently highlighted keyword or identifier.
* <kbd>C-M-v</kbd> scrolls down in the documentation window.
* <kbd>C-w</kbd> opens the relevant section of the documentation, scrolling to the part about the currently highlighted keyword or identifier. Using <kbd>C-w</kbd> allows you scroll up (<kbd>C-M-S-v</kbd>) in the documentation window to see more context.

You can customize these keybindings by editing `company-active-map`.

Selecting a completion generally often a snippet with holes at the current point (`company-coq` uses `yasnippet` as the snippet backend). You can move between holes by using <kbd>&lt;tab></kbd> and <kbd>S-&lt;tab></kbd>.

## Advanced topics

### Autocompleting symbols

The procedure above will give you auto-completion and documentation for tactics and commands, but not for theorem names and symbols. To get the latter, add the following to your `.emacs`, before `(company-coq-initialize)`:

```elisp
(setq company-coq-autocomplete-symbols t)
```

This feature won't work well unless you build and use a [patched coq REPL](https://github.com/cpitclaudel/coq/tree/V8.4pl2-SearchAny).

### Installing from source

#### `company-coq`

```bash
mkdir -p ~/.emacs.d/lisp/
git clone https://github.com/cpitclaudel/company-coq.git ~/.emacs.d/lisp/company-coq
```

#### Dependencies

```elisp
M-x package-refresh-contents RET
M-x package-install RET company RET
M-x package-install RET company-math RET
M-x package-install RET yasnippet RET
```

### Configuration

```elisp
(add-to-list 'load-path "~/.emacs.d/lisp/ProofGeneral/generic/")
(add-to-list 'load-path "~/.emacs.d/lisp/company-coq/")
(require 'company-coq)
```
