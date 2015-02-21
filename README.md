# UniCoq
An enhanced unification algorithm for Coq

Copyright (c) 2015 Beta Ziliani <beta@mpi-sws.de>,
	           Matthieu Sozeau <mattam@mattam.org>
	       
Distributed under the terms of the MIT License,
see LICENSE for details.

This archive contains a new unification algorithm for Coq, as
a plugin that replaces the existing unification algorithm.

The archive has 3 subdirectories:
* `src` contains the code of the plugin in `munify.ml4`.

* `theories` contains support Coq files for the plugin.
  `Unicoq.v` declares the plugin on the Coq side.

* `test-suite` just demonstrates a use of the plugin

Installation
============

Through OPAM, this plugin is available in Coq's repo-unstable:
```
 # opam install coq:unicoq
```
Otherwise, you should have coqc, ocamlc and make in your path. 
Then simply do:
```
 # coq_makefile -f Make -o Makefile
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

To trace what the algorithm is doing, one can use `Set Munify Debug`
which will produce a trace on stdout.

The option `Set Munify Aggressive` activates the strong `Meta-DelDeps` 
rule to remove dependencies of meta-variables (see the paper for details).

The option `Set Munify Use Hash` enables the use of a hash table to
record unification failures, improving time performance but consuming 
more memory.

The command `Print Munify Stats` will print the number of times the
unifier was called and the number of meta-variable instantiations performed.
