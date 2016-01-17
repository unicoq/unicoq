(************************************************************************************************)
(* Unicoq plugin.                                                                               *)
(* Copyright (c) 2015 Beta Ziliani <beta@mpi-sws.org>                                           *)
(*                    Matthieu Sozeau <mattam@mattam.org>.                                      *)
(************************************************************************************************)

Require Import Unicoq.Unicoq.
Print Unicoq Stats.
Set Unicoq Aggressive.
Set Unicoq Debug.

Definition test1 : (_ : nat -> nat) 0 = S 0 := eq_refl.

Definition test2 : match 0 return nat with 0 => (_ : nat -> nat) 0 | _ => 1 end = S 0 := eq_refl.


Unset Unicoq Aggressive.
Fail Definition test3 : (_ : nat -> nat) 0 = 0 := eq_refl.

Set Unicoq Super Aggressive.  (* Needs super aggressive option *)
Definition test3 : (_ : nat -> nat) 0 = 0 := eq_refl.

Unset Use Unicoq.
(* fails in std coq unif, although the Unset Use Unicoq option is not working*)
Definition test4 : (_ : nat -> nat) 0 = 0 := eq_refl.
Set Use Unicoq.

Unset Unicoq Super Aggressive.
(* This one should fail *)
Fail Definition test5 (x:nat) : _ x x = S x := eq_refl.

Goal True.
  munify 0 0.
  Fail munify 0 1.
  exact I.
Qed.

Print Unicoq Stats.
(* Local Variables: *)
(* coq-prog-name: "coqtop.byte" *)
(* coq-load-path: nil *)
(* End: *)
