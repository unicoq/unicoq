From Unicoq Require Import Unicoq.
Polymorphic Record dyn : Prop := mkdyn {}.
Polymorphic Definition Dyn {A} (a:A) : dyn. constructor. Qed.

(* This used to loop *)
Fail Check ltac:(mmatch Dyn@{Set} Dyn@{Type}; exact tt).

Check ltac:(munify Dyn@{Type} Dyn@{Type}; exact tt).
