From Unicoq Require Import Unicoq.
Polymorphic Record dyn : Prop := mkdyn {}.
Polymorphic Definition Dyn {A} (a:A) : dyn. Proof. constructor. Qed.

Universe a.
Constraint Set < a.

(* This used to loop *)
Fail Check ltac:(mmatch (@Dyn@{Set}) (@Dyn@{a}); exact tt).

(* Applied to its first argument, the universe of Dyn is irrelevant *)
Check ltac:(mmatch Dyn@{Set} Dyn@{a}; exact tt).

Check ltac:(munify Dyn@{Type} Dyn@{Type}; exact tt).
