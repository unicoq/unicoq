Require Import Unicoq.Unicoq.

(* This used to cause an assertion error in cClosure.ml *)
Theorem eq_trans_refl_l A (x y:A) (e:x=y) : eq_trans eq_refl e = e.
Proof.
  destruct e. reflexivity.
Defined.
