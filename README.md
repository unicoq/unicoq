# Unicoq

![Unicoq logo](/doc/unicoq-small.png?raw=true)

A different unification algorithm for Rocq.

Copyright (c) 2015--2026
  Beta Ziliani <beta.ziliani@gmail.com>,
  Jan-Oliver Kaiser <mail@janno-kaiser.de>,
  Matthieu Sozeau <mattam@mattam.org>

Distributed under the terms of the MIT License, see LICENSE for details.

## Why another algorithm?

Rocq comes with two user-facing unification algorithms, one used by tactics
like `apply` and `rewrite`, and another one used by ssreflect's tactics and
term elaboration. The former is unsound, meaning that it's possible to unify
terms yet the resulting substitution produces ill-typed terms. The latter,
called evarconv, _seems_ sound, but it applies several heuristics that makes
it hard to debug and understand.

Unicoq is a plugin that replaces evarconv with an algorithm that is described
in detail in [A comprehensible guide to a new unifier for CIC including universe polymorphism and overloading](https://doi.org/10.1017/S0956796817000028).

Pros:
 * It's simpler and easier to debug than evarconv.
 * It's formally described, which in itself is not a proof of soundness, but it's a big first step.
 * It solves some problems that evarconv can't solve.

Cons:
 * evarconv solves more problems, even if it misses some that Unicoq solve.
 * evarconv is faster.

## Contents

The repository has 3 subdirectories:
* `src` contains the code of the plugin in `munify.ml`.

* `theories` contains support Rocq files for the plugin.
  `Unicoq.v` declares the plugin on the Coq side.

* `test-suite` just tests and demonstrates the use of the plugin.

## Installation

The plugin works currently with Rocq master, although there are releases
for previous versions as well. Through OPAM, this plugin is available
in [Rocq's repository](https://rocq-prover.org/opam/released):
```
opam repo add rocq-released https://rocq-prover.org/opam/released
opam install coq-unicoq
```
Otherwise, you should have rocq, ocamlc and make in your path.
Then simply do:
```
rocq makefile -f _CoqProject -o Makefile
```
To generate a makefile from the `_CoqProject` file, then `make`.
This will consecutively build the plugin, the supporting
theories and the test-suite file.

You can then either `make install` the plugin or leave it in its
current directory. To be able to import it from anywhere in Coq,
simply add the following to `~/.rocqrc`:
```
Add LoadPath "path_to_unicoq/theories" as Unicoq.
Add ML Path "path_to_unicoq/src".
```

## Usage

Once installed, you can `Require Import Unicoq.Unicoq` to load the
plugin, which will install Unicoq's unification algorithm as the
unifier called when typechecking terms (Definitions...) and when
using the `refine` tactic. Note that Coq's standard `apply`,
`rewrite`, etc... still use a different unification algorithm.
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
