# UniCoq

![Unicoq logo](/doc/unicoq-small.png?raw=true)

An enhanced unification algorithm for Coq

Copyright (c) 2015 Beta Ziliani <bziliani@famaf.unc.edu.ar>,
	           Matthieu Sozeau <mattam@mattam.org>

Distributed under the terms of the MIT License,
see LICENSE for details.

This archive contains a new unification algorithm for Coq, as
a plugin that replaces the existing unification algorithm. This
algorithm is described in detail in
[A Unification Algorithm for Coq Featuring Universe Polymorphism
and Overloading](http://www.mpi-sws.org/~beta/#publications).

The archive has 3 subdirectories:
* `src` contains the code of the plugin in `munify.ml4`.

* `theories` contains support Coq files for the plugin.
  `Unicoq.v` declares the plugin on the Coq side.

* `test-suite` just demonstrates a use of the plugin

Installation
============

The plugin works currently with Coq v8.5. Through OPAM,
this plugin is available in the [Coq's repository](http://coq.io/opam/):
```
 opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq-unicoq
```
Otherwise, you should have coqc, ocamlc and make in your path.
Then simply do:
```
 coq_makefile -f Make -o Makefile
```
To generate a makefile from the description in Make, then `make`.
This will consecutively build the plugin, the supporting
theories and the test-suite file.

You can then either `make install` the plugin or leave it in its
current directory. To be able to import it from anywhere in Coq,
simply add the following to `~/.coqrc`:
```
Add LoadPath "path_to_unicoq/theories" as Unicoq.
Add ML Path "path_to_unicoq/src".
```
# Usage

Once installed, you can `Require Import Unicoq.Unicoq` to load the
plugin, which will install unicoq's unification algorithm as the
unifier called when typechecking terms (Definitions...) and when
using the `refine` tactic. Note that Coq's standard `apply`,
`rewrite` etc... still use a different unification algorithm.
On the other hand, if you use Ssreflect all tactics will call
unicoq's unifier.

The plugin also defines a tactic `munify t u` taking two terms and
unifying them.

### Options, debugging

To trace what the algorithm is doing, one can use `Set Unicoq Debug`
which will produce a trace on stdout. Additionally, if a file is set
using `Set Unicoq LaTex File "file.tex"` the algorithm, upon success,
will write a derivation tree in LaTex. In the directory `doc` there is
a file named `treelog.tex` with an example on how to build such document.

The option `Set Unicoq Aggressive` activates the strong `Meta-DelDeps`
rule to remove dependencies of meta-variables (see the paper for details).
It is _on_ by default.

The option `Set Unicoq Super Aggressive` activates specialization of a
meta-variable to its instance arguments (in case it is of function
type). Implies Aggressive. Such arguments can be pruned afterwards to
fall back into HOPU.
It is _off_ by default.

The option `Set Unicoq Use Hash` enables the use of a hash table to
record unification failures, improving time performance but consuming
more memory.
It is _off_ by default.

The command `Print Unicoq Stats` will print the number of times the
unifier was called and the number of meta-variable instantiations performed.
