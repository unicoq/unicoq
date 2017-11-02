Require Import Unicoq.Unicoq.

Set Unicoq Trace.
Set Unicoq Aggressive.

(* Meta-Inst and Meta-DelDeps *)
Section Inst.
Variables x y z : nat.
Example inst1 : _ x = 0 := eq_refl 0.
Print inst1. (* should be [(fun _=>0) x = 0] *)

Example inst2 : _ x = x := eq_refl x.
Print inst2. (* should be [(fun w=>w) x = x] *)

Example inst3 : _ x y z = x := eq_refl x.
Print inst3. (* should be [(fun w _ _=>w) x y z = x] *)

Example inst4 : _ x y z = z := eq_refl z.
Print inst4. (* should be [(fun _ _ w=>w) x y z = z] *)

Set Printing All.
Example inst_letzetaR : let X := _ : nat -> nat in X x = 0 := eq_refl.

Example inst_letzetaL : 0 = 0 := eq_refl (let X := _ : nat -> nat in X x) .

Example inst_betaR : (fun w=>w) _ x = 0 := eq_refl.

Example inst_betaL : 0 = 0 := eq_refl ((fun w=>w) _ x).

Example inst_iotaR : match 0 with 0 => _ | _ => 0 end = x := eq_refl.

Example inst_iotaR' : match 0 with 0 => _ | _ => (fun _ =>0) end x = x := eq_refl.

Example inst_iotaL : x = x := eq_refl (match 0 with 0 => _ | _ => (fun _ =>0) end x).

(* Meta-Same-Same *)
Example same1 : let X := _ : nat -> nat in (X x, X x) = (X x, x) := eq_refl.

Example prod1 : (forall (T:Type) (t : T), t = t) = (forall (T:_) (t : _), _ = _) := eq_refl.
Print prod1.

(* Example prod2 : (forall (t : Prop), True) = (forall (t : Prop), _ : Prop) := eq_refl. *)

End Inst.
