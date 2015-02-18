(************************************************************************************************)
(* Unicoq plugin.                                                                               *)
(* Copyright (c) 2015 Beta Ziliani <beta@mpi-sws.org>                                           *)
(*                    Matthieu Sozeau <mattam@mattam.org>.                                      *)
(************************************************************************************************)

Require Import Unicoq.Unicoq.

Goal True.
  munify 0 0.
  Fail munify 0 1.
  exact I.
Qed.