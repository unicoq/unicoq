From Unicoq Require Import Unicoq.
Unset Use Unicoq.
Ltac finish_subject r v := let s:=eval unfold r in r in unify s v.
Module Primitive.
Set Primitive Projections.

Module Defaults.
Record R := { f : nat -> nat }.
Canonical wrap (g:nat->nat) : R := {|f:=g|}.
Goal True.
Proof.
  evar (r:R).
  let s:=eval unfold r in r in
  munify (f s 0) (S 0);
  let expected:=constr:(wrap S) in constr_eq s expected;
  pose proof (eq_refl (f s 0) : f s 0 = S 0).
  exact I.
Qed.
Goal True.
Proof.
  evar (r:R).
  let s:=eval unfold r in r in
  munify (S 0) (f s 0);
  let expected:=constr:(wrap S) in constr_eq s expected;
  pose proof (eq_refl (f s 0) : f s 0 = S 0).
  exact I.
Qed.
End Defaults.

Module BinaryDefaults.
Record R := { f : nat -> nat -> nat }.
Canonical wrap (g:nat->nat->nat) : R := {|f:=g|}.
Goal forall n:nat, True.
Proof.
  intros n; evar (r:R).
  let s:=eval unfold r in r in
  munify (f s n) (Nat.add n);
  let expected:=constr:(wrap Nat.add) in constr_eq s expected;
  pose proof (eq_refl (f s n) : f s n = Nat.add n).
  exact I.
Qed.
Goal forall n m:nat, True.
Proof.
  intros n m; evar (r:R).
  let s:=eval unfold r in r in
  munify (Nat.add n m) (f s n m);
  let expected:=constr:(wrap Nat.add) in constr_eq s expected;
  pose proof (eq_refl (f s n m) : f s n m = Nat.add n m).
  exact I.
Qed.
End BinaryDefaults.

Module ParameterDefaults.
Record R (A:Type) (a:A) := { f : nat -> nat }.
Canonical wrap (A:Type) (a:A) (g:nat->nat) : R A a := {|f:=g|}.
Goal True.
Proof.
  evar (r:R unit tt).
  let s:=eval unfold r in r in
  munify (f _ _ s 0) (S 0);
  let expected:=constr:(wrap unit tt S) in constr_eq s expected;
  pose proof (eq_refl (f _ _ s 0) : f _ _ s 0 = S 0).
  exact I.
Qed.
End ParameterDefaults.

Module DefaultTypes.
Record R := { carrier : Type }.
Canonical wrap (A:Type) : R := {|carrier:=A|}.

Goal forall A:Type, True.
Proof.
  intros A; evar (r:R).
  let s:=eval unfold r in r in munify (carrier s) A.
  exact I.
Qed.
End DefaultTypes.

Module Lambdas.
Record R := { f : nat -> nat }.
Canonical succR : R := {|f:=S|}.
Goal True.
Proof.
  evar (r:R).
  assert_fails ltac:(let s:=eval unfold r in r in munify (f s) (fun n:nat=>S(S n))).
  let s:=eval unfold r in r in is_evar s.
  finish_subject r succR; exact I.
Qed.
Goal True.
Proof.
  evar (r:R).
  assert_fails ltac:(let s:=eval unfold r in r in munify (fun n:nat=>S(S n)) (f s)).
  let s:=eval unfold r in r in is_evar s.
  finish_subject r succR; exact I.
Qed.
Goal True.
Proof.
  evar (r:R).
  let s:=eval unfold r in r in
  munify (f s) (fun n:nat=>S n);
  let expected:=constr:(succR) in constr_eq s expected;
  pose proof (eq_refl (f s) : f s = (fun n:nat=>S n)).
  exact I.
Qed.
End Lambdas.

Module ResidualEvars.
Record R := { f : nat -> nat }.
Canonical wrap (g:nat->nat) : R := {|f:=fun n=>S(g n)|}.

Goal True.
Proof.
  evar (r:R).
  let s:=eval unfold r in r in
  munify (f s) (fun n:nat=>S(S n));
  let expected:=constr:(wrap S) in constr_eq s expected;
  pose proof (eq_refl (f s) : f s = (fun n:nat=>S(S n))).
  exact I.
Qed.
End ResidualEvars.

Module UniverseDirections.
Universe lo hi top.
Constraint lo < hi. Constraint hi < top.
Module Sorts.
Record R := { carrier : Type@{top} }.
Canonical high : R := {|carrier:=Type@{hi}|}.
Goal True.
Proof.
  evar (r:R).

  let s:=eval unfold r in r in munify Type@{lo} (carrier s).
  exact I.
Qed.
Goal True.
Proof.
  evar (r:R).
  assert_fails ltac:(let s:=eval unfold r in r in munify (carrier s) Type@{lo}).
  let s:=eval unfold r in r in is_evar s.
  finish_subject r high; exact I.
Qed.
Goal True.
Proof.
  evar (r:R).

  assert_fails ltac:(let s:=eval unfold r in r in mmatch (carrier s) Type@{lo}).
  let s:=eval unfold r in r in is_evar s.
  finish_subject r high; exact I.
Qed.
End Sorts.
Module Functions.
Record R := { f : nat -> Type@{top} }.
Canonical high : R := {|f:=fun _=>Type@{hi}|}.
Goal True.
Proof.
  evar (r:R).
  assert_fails ltac:(let s:=eval unfold r in r in munify (f s) (fun _:nat=>Type@{lo})).
  let s:=eval unfold r in r in is_evar s.
  finish_subject r high; exact I.
Qed.
Goal True.
Proof.
  evar (r:R).
  assert_fails ltac:(let s:=eval unfold r in r in munify (fun _:nat=>Type@{lo}) (f s)).
  let s:=eval unfold r in r in is_evar s.
  finish_subject r high; exact I.
Qed.
End Functions.
End UniverseDirections.
End Primitive.
Module Ordinary.
Unset Primitive Projections.
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

  Goal True.
  Proof.
    evar (s : structure nat).
    let s := eval unfold s in s in
    munify (family _ s) (nat -> nat).
    exact I.
  Qed.
End ProductField.

Module Defaults.
Record R := { f : nat -> nat }.
Canonical wrap (g:nat->nat) : R := {|f:=g|}.
Goal True.
Proof.
  evar (r:R).
  let s:=eval unfold r in r in
  munify (f s 0) (S 0);
  let expected:=constr:(wrap S) in constr_eq s expected;
  pose proof (eq_refl (f s 0) : f s 0 = S 0).
  exact I.
Qed.
Goal True.
Proof.
  evar (r:R).
  let s:=eval unfold r in r in
  munify (S 0) (f s 0);
  let expected:=constr:(wrap S) in constr_eq s expected;
  pose proof (eq_refl (f s 0) : f s 0 = S 0).
  exact I.
Qed.
End Defaults.

Module BinaryDefaults.
Record R := { f : nat -> nat -> nat }.
Canonical wrap (g:nat->nat->nat) : R := {|f:=g|}.
Goal forall n:nat, True.
Proof.
  intros n; evar (r:R).
  let s:=eval unfold r in r in
  munify (f s n) (Nat.add n);
  let expected:=constr:(wrap Nat.add) in constr_eq s expected;
  pose proof (eq_refl (f s n) : f s n = Nat.add n).
  exact I.
Qed.
Goal forall n m:nat, True.
Proof.
  intros n m; evar (r:R).
  let s:=eval unfold r in r in
  munify (Nat.add n m) (f s n m);
  let expected:=constr:(wrap Nat.add) in constr_eq s expected;
  pose proof (eq_refl (f s n m) : f s n m = Nat.add n m).
  exact I.
Qed.
End BinaryDefaults.

Module ParameterDefaults.
Record R (A:Type) (a:A) := { f : nat -> nat }.
Canonical wrap (A:Type) (a:A) (g:nat->nat) : R A a := {|f:=g|}.
Goal True.
Proof.
  evar (r:R unit tt).
  let s:=eval unfold r in r in
  munify (f _ _ s 0) (S 0);
  let expected:=constr:(wrap unit tt S) in constr_eq s expected;
  pose proof (eq_refl (f _ _ s 0) : f _ _ s 0 = S 0).
  exact I.
Qed.
End ParameterDefaults.

Module DefaultTypes.
Record R := { carrier : Type }.
Canonical wrap (A:Type) : R := {|carrier:=A|}.

Goal forall A:Type, True.
Proof.
  intros A; evar (r:R).
  let s:=eval unfold r in r in munify (carrier s) A.
  exact I.
Qed.
End DefaultTypes.

Module Lambdas.
Record R := { f : nat -> nat }.
Canonical succR : R := {|f:=S|}.
Goal True.
Proof.
  evar (r:R).
  assert_fails ltac:(let s:=eval unfold r in r in munify (f s) (fun n:nat=>S(S n))).
  let s:=eval unfold r in r in is_evar s.
  finish_subject r succR; exact I.
Qed.
Goal True.
Proof.
  evar (r:R).
  assert_fails ltac:(let s:=eval unfold r in r in munify (fun n:nat=>S(S n)) (f s)).
  let s:=eval unfold r in r in is_evar s.
  finish_subject r succR; exact I.
Qed.
Goal True.
Proof.
  evar (r:R).
  let s:=eval unfold r in r in
  munify (f s) (fun n:nat=>S n);
  let expected:=constr:(succR) in constr_eq s expected;
  pose proof (eq_refl (f s) : f s = (fun n:nat=>S n)).
  exact I.
Qed.
End Lambdas.

Module ResidualEvars.
Record R := { f : nat -> nat }.
Canonical wrap (g:nat->nat) : R := {|f:=fun n=>S(g n)|}.

Goal True.
Proof.
  evar (r:R).
  let s:=eval unfold r in r in
  munify (f s) (fun n:nat=>S(S n));
  let expected:=constr:(wrap S) in constr_eq s expected;
  pose proof (eq_refl (f s) : f s = (fun n:nat=>S(S n))).
  exact I.
Qed.
End ResidualEvars.

Module UniverseDirections.
Universe lo hi top.
Constraint lo < hi. Constraint hi < top.
Module Sorts.
Record R := { carrier : Type@{top} }.
Canonical high : R := {|carrier:=Type@{hi}|}.
Goal True.
Proof.
  evar (r:R).

  let s:=eval unfold r in r in munify Type@{lo} (carrier s).
  exact I.
Qed.
Goal True.
Proof.
  evar (r:R).
  assert_fails ltac:(let s:=eval unfold r in r in munify (carrier s) Type@{lo}).
  let s:=eval unfold r in r in is_evar s.
  finish_subject r high; exact I.
Qed.
Goal True.
Proof.
  evar (r:R).

  assert_fails ltac:(let s:=eval unfold r in r in mmatch (carrier s) Type@{lo}).
  let s:=eval unfold r in r in is_evar s.
  finish_subject r high; exact I.
Qed.
End Sorts.
Module Functions.
Record R := { f : nat -> Type@{top} }.
Canonical high : R := {|f:=fun _=>Type@{hi}|}.
Goal True.
Proof.
  evar (r:R).
  assert_fails ltac:(let s:=eval unfold r in r in munify (f s) (fun _:nat=>Type@{lo})).
  let s:=eval unfold r in r in is_evar s.
  finish_subject r high; exact I.
Qed.
Goal True.
Proof.
  evar (r:R).
  assert_fails ltac:(let s:=eval unfold r in r in munify (fun _:nat=>Type@{lo}) (f s)).
  let s:=eval unfold r in r in is_evar s.
  finish_subject r high; exact I.
Qed.
End Functions.
End UniverseDirections.
End Ordinary.
