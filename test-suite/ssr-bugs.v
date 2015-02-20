Require Import Ssreflect.ssreflect Ssreflect.ssrbool Ssreflect.ssrnat.
Require Import Ssreflect.ssrfun Ssreflect.choice.
Require Import Ssreflect.eqtype Ssreflect.seq.

Variable T : choiceType.
Implicit Types P Q : pred T.
Set Munify Debug.

Definition choose P x0 :=
  if insub x0 : {? x | P x} is Some (exist x Px) then
    xchoose (ex_intro [eta P] x Px)
  else x0.
Check choose.
(* it should be : pred T -> T -> T *)

