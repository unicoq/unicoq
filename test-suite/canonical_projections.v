From Unicoq Require Import Unicoq.

(* Regression tests for [munify]'s canonical-structure path when the
   projection is represented primitively.  Each test leaves the record evar
   open and makes [munify] infer it from a projected field. *)

(* Set Primitive Projections. *)

Module NoParameters.
  Record structure := { carrier : Type }.

  Canonical Structure as_unit : structure := {| carrier := unit |}.
  Canonical Structure as_nat : structure := {| carrier := nat |}.

  Goal True.
  Proof.
    evar (s : structure).
    let s := eval unfold s in s in
    munify (carrier s) unit.
    exact I.
  Qed.

  (* The value pattern must select [as_nat], rather than merely finding an
     arbitrary default canonical structure for [carrier]. *)
  Goal True.
  Proof.
    evar (s : structure).
    let s := eval unfold s in s in
    munify (carrier s) nat.
    exact I.
  Qed.
End NoParameters.

Module WithParameters.
  Record structure (A : Type) := { carrier : Type }.
  Canonical Structure as_unit {A} : structure A := {| carrier := unit |}.

  Goal True.
  Proof.
    evar (s : structure nat).
    let s := eval unfold s in s in
    munify (carrier _ s) unit.
    exact I.
  Qed.
End WithParameters.

Module ProductField.
  Record structure (A : Type) := {
    #[canonical=no] carrier : Type;
    family : Type
  }.

  Canonical Structure product_family {A} : structure A := {|
    carrier := unit;
    family := nat -> nat
  |}.

  (* The RHS is a product, so this exercises the [Prod_cs] canonical-pattern
     lookup through the primitive [family] projection. *)
  Goal True.
  Proof.
    evar (s : structure nat).
    let s := eval unfold s in s in
    munify (family _ s) (nat -> nat).
    exact I.
  Qed.
End ProductField.
