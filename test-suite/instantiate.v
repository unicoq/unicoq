Require Import Unicoq.Unicoq.

Goal Prop.
  evar (x : Type).
  let x := eval hnf in x in
  minstantiate x (True : Prop : Type).
  Show Proof.
Abort.
