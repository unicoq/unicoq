(************************************************************************************************)
(* Unicoq plugin.                                                                               *)
(* Copyright (c) 2015--2020 Beta Ziliani <beta@mpi-sws.org>                                     *)
(*                          Matthieu Sozeau <mattam@mattam.org>.                                *)
(************************************************************************************************)

Require Import Unicoq.Unicoq.

Ltac pollute N :=
  match N with
  | 0 => idtac
  | S ?N => let H := fresh in pose (H := N); pollute N
  end.
 
Require Import ssreflect.

Unset Unicoq Debug.

Goal True.
  pollute 30.
  evar (x : nat).
  clear H9.
  evar (y : nat).
  Time (apply: ((fun e: H1 + H2 + H3 + x = H4 + H5 + H6 + y => I) eq_refl)). (* ~2 secs. it is exponential *)
  Unshelve.
  - exact: 0.
  - exact: 1. 
Qed.
