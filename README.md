# unicoq
An enhanced unification algorithm for Coq

Copyright 2015 Beta Ziliani <beta@mpi-sws.de>,
	       Matthieu Sozeau <mattam@mattam.org>
Distributed under the terms of the MIT License,
see LICENSE for details.

This archive contains a new unification algorithm for Coq, as
a plugin that replaces the existing unification algorithm.

The archive has 3 subdirectories:
src/ contains the code of the plugin in munify.ml.

theories/ contains support Coq files for the plugin.
  Unicoq.v declares the plugin on the Coq side.

test-suite/ just demonstrates a use of the plugin

Installation
============

Through OPAM, this plugin is available in Coq's repo-unstable:

# opam install coq:unicoq

Otherwise, you should have coqc, ocamlc and make in your path. 
Then simply do:

# coq_makefile -f Make -o Makefile

To generate a makefile from the description in Make, then [make].
This will consecutively build the plugin, the supporting 
theories and the test-suite file.

You can then either [make install] the plugin or leave it in its
current directory. To be able to import it from anywhere in Coq,
simply add the following to ~/.coqrc:

Add Rec LoadPath "path_to_unicoq/theories" as Unicoq.
Add ML Path "path_to_unicoq/src".
