Cubicle
=======

Cubicle is a tool that combines model checking algorithms and automatic SMT
theorem provers with a powerful invariants inference mechanism.

Various examples can be found in the [examples subdirectory](examples).

Copyright
---------

    Copyright (C) 2011-2017
    Sylvain Conchon and Alain Mebsout
    Université Paris-Sud 11

This program is distributed underthe
[Apache Software License version 2.0](https://www.apache.org/licenses/LICENSE-2.0).
See the enclosed file [LICENSE](LICENSE).


Installation
------------

To compile Cubicle you will need [OCaml](http://ocaml.org) version 4.03.0 (or
newer) and issue:

    ./configure
    make

then with superuser rights:

    make install

Cubicle comes with its own emacs major
mode [cubicle-mode.el](doc/emacs/cubicle-mode.el). You should copy this file to
your emacs.d directory (or anywhere in your load path) and add the following to
your init file (`.emacs` or `emacs.d/init.el`):

```elisp
(setq auto-mode-alist
     (cons '("\\.cub$" . cubicle-mode) auto-mode-alist))
(autoload 'cubicle-mode "cubicle-mode" "Major mode for Cubicle." t)
```
    
To add colors to the compilation buffer, also add this:

```elisp
(require 'ansi-color)
(defun colorize-compilation-buffer ()
   (toggle-read-only)
   (ansi-color-apply-on-region (point-min) (point-max))
   (toggle-read-only))
(add-hook 'compilation-filter-hook 'colorize-compilation-buffer)
```

Usage
-----

To run Cubicle with its classical backward reachability algorithm on a file
`file.cub` simply do:
 
    cubicle file.cub

To run Cubicle with the BRAB algorithm (with a preliminary forward exploration
using 2 processes) on a file `file.cub` simply do:
 
    cubicle -brab 2 file.cub

You can see the list of Cubcile's options by doing:

    cubicle -h


Developers
----------

Documentation for developers is available as ocamldoc comments and can be
generated in html format in the `doc/ocamldoc` directory with:

    make doc

A pdf file depicting dependency relations between modules can be generated
with:

    make archi
