From Unicoq Require Import Unicoq.

Set Primitive Projections.

Module Test1.

  Record cs := { ty : Type }.
  Canonical Structure cs_unit := {| ty := unit |}.

  (* The definition below used to fail with:

Error: In environment
c := ?c : cs
The term "tt" has type "unit" while it is expected to have type "ty c".

   *)
  Definition x :=
    let c : cs := _ in
    let x := (fun (u : ty c) => u) (tt) in
    c.

End Test1.

(* Similar to Test1 but with parameters *)
Module Test2.

  Record cs (A : Type) := { ty : Type }.
  Canonical Structure cs_unit {A} : cs A := {| ty := unit |}.

  Definition x :=
    let c : cs nat := _ in
    let x := (fun (u : ty _ c) => u) (tt) in
    c.

End Test2.
