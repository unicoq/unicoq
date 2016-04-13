(************************************************************************************************)
(* Unicoq plugin.                                                                               *)
(* Copyright (c) 2015 Beta Ziliani <beta@mpi-sws.org>                                           *)
(*                    Matthieu Sozeau <mattam@mattam.org>.                                      *)
(************************************************************************************************)

Require Import Unicoq.Unicoq.
Print Unicoq Stats.
Set Unicoq Aggressive.
Set Unicoq Debug.
Set Unicoq LaTex File "unif.tex".

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

Goal forall x y : nat, True.
  intros.
  mmatch 0 0.
  Fail munify 0 1.
Set Unicoq Dump Equalities.
  evar (X : nat).
  munify 0 X.
  mmatch X 0.
  mmatch (S _) (1 + 0).
  mmatch (S _) (0 + (fun x=>x) 1).
  Fail mmatch (0 + (fun x=>x) _) 1.
  mmatch _ 0.
  mmatch (_ X) 0.
  mmatch (_ X X) X. (* works because meta-reduce changes the rhs to 0 *)
  Fail mmatch (_ x x) _.
  munify (_ x x) _.
  exact I.
Abort.


Unset Unicoq Debug.
Set Unicoq Aggressive.
Definition aggressive_double_var (x:nat) : (fun y=>_) x = x := eq_refl.
Print aggressive_double_var. (* must be [fun y => y] *)

Definition aggressive_double_var' (x y:nat) : (fun z=>_) x y = x + y := eq_refl.
Print aggressive_double_var'. 

Definition aggressive_const (x y z:nat) : (fun u v w=>_) x 0 y = x := eq_refl.
Print aggressive_const.

Set Unicoq Debug.
Definition aggressive_const' (x y z:nat) : (fun u v w : nat =>_) 0 x y = x := eq_refl.
Print aggressive_const'.

Definition aggressive_const'' (x y z:nat) : (fun u v w=>_) y x 0 = x := eq_refl.
Print aggressive_const''.

Fixpoint nary_congruence_statement (n : nat)
         : (forall B, (B -> B -> Prop) -> Prop) -> Prop :=
  match n with
  | O => fun k => forall B, k B (fun x1 x2 : B => x1 = x2)
  | S n' =>
    let k' A B e (f1 f2 : A -> B) :=
      forall x1 x2, x1 = x2 -> (e (f1 x1) (f2 x2) : Prop) in
    fun k => forall A, nary_congruence_statement n' (fun B e => k _ (k' A B e))
  end.


Definition intersec1 :
  let T : nat -> nat -> nat -> nat := fun x y z=> _ in
  forall x y z:nat, T x y z = T y y x /\ T x y z = y := fun x y z:nat=>conj eq_refl eq_refl.

Definition intersec2 :
  let T : nat -> nat -> nat -> nat := fun x y z=> _ in
  forall x y z:nat, T x x x = T y y y /\ T x y z = 0 := fun x y z:nat=>conj eq_refl eq_refl.

Fail Definition intersec3 :
  let T : nat -> nat -> nat -> nat := fun x y z=> _ in
  forall x y z:nat, T x y z = T y y x /\ T x y z = x := fun x y z:nat=>conj eq_refl eq_refl.

Fail Definition intersec3 :
  let T : nat -> nat -> nat -> nat := fun x y z=> _ in
  forall x y z:nat, T x y z = T y y x /\ T x y z = x := fun x y z:nat=>conj eq_refl eq_refl.

Definition intersec3 :
  let T : nat -> nat -> nat -> nat := fun x y z=> _ in
  forall x y z:nat, T x y z = T x z z /\ T x y z = x := fun x y z:nat=>conj eq_refl eq_refl.

Definition intersec4 :
  let T : nat -> nat -> nat -> nat := fun x y z=> _ in
  forall x y z:nat, T z y z = T z z z /\ T x y z = z := fun x y z:nat=>conj eq_refl eq_refl.

Fail Definition intersec5 :
  let T : nat -> nat -> nat -> nat := fun x y z=> _ in
  forall x y z:nat, T x y z = T x z z /\ T x y z = y := fun x y z:nat=>conj eq_refl eq_refl.

Print Unicoq Stats.
