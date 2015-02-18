(************************************************************************************************)
(* Unicoq plugin.                                                                               *)
(* Copyright (c) 2015 Beta Ziliani <beta@mpi-sws.org>                                           *)
(*                    Matthieu Sozeau <mattam@mattam.org>.                                      *)
(************************************************************************************************)

Require Import Unicoq.Unicoq.

Unset Aggressive.
Set Munify Debug.
Definition test1 : (_ : nat -> nat) 0 = S 0 := eq_refl.

Definition test2 : match 0 return nat with 0 => (_ : nat -> nat) 0 | _ => 1 end = S 0 := eq_refl.


Set Aggressive.
Fail Definition test3 : (_ : nat -> nat) 0 = 0 := eq_refl.

Set Printing Existential Instances.
Set Munify Debug.
Set Use Munify.
Definition test3 : (_ : nat -> nat) 0 = 0 := eq_refl.



Goal True.
  munify 0 0.
  Fail munify 0 1.
  exact I.
Qed.


