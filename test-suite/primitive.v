From Unicoq Require Import Unicoq.

Set Primitive Projections.

Record cs := { ty : Type; data : nat }.
Canonical Structure cs_unit := {| ty := unit; data:=0 |}.

(* The definition below used to fail with:

Error: In environment
c := ?c : cs
The term "tt" has type "unit" while it is expected to have type "ty c".

 *)
Definition x :=
  let c : cs := _ in
  let x := (fun (u : ty c) => u) (tt) in
  data c.
