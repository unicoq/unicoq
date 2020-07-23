From Unicoq Require Import Unicoq.

Set Primitive Projections.
Module M.
  Record bla := { c :> Type;  goal : c -> c -> Prop }.
  Arguments goal {_}.
End M.
Import M.

Ltac IHateLtac B k :=
    let ep := fresh "p" in
    let eq := fresh "q" in
    evar (ep : c B);
    evar (eq : c B);
    let p := eval unfold ep in ep in
    let q := eval unfold eq in eq in
    k p q; clear ep eq.

Section Test.
  Context (B : bla) (P Q : B).

  Set Printing Primitive Projection Parameters.

  Goal B.(@goal) P Q.
    (* Everything is phrased in terms of the constant [goal]. *)
    IHateLtac B ltac:(fun p q =>
      match goal with
      | |- ?g =>
        unify g (@goal B p q)
      end
    ).

    IHateLtac B ltac:(fun p q =>
      match goal with
      | |- ?g =>
        munify g (@goal B p q)
      end
    ).

    (* Let's make the RHS primitive *)

    (* [unify] doesn't care and succeeds *)
    IHateLtac B ltac:(fun p q =>
      match goal with
      | |- ?g =>
        let t := constr:(@goal B) in
        let t := eval unfold goal in t in
        is_proj t;
        unify g (t p q)
      end
    ).

    (* [munify] fails *)
    IHateLtac B ltac:(fun p q =>
      match goal with
      | |- ?g =>
        let t := constr:(@goal B) in
        let t := eval unfold goal in t in
        is_proj t;
        assert_fails (munify g (t p q))
      end
    ).

    progress unfold goal.
    (* goal is now a primitive projection. *)

    (* [unify] still does the right thing. *)
    IHateLtac B ltac:(fun p q =>
      match goal with
      | |- ?g =>
        unify g (@goal B p q)
      end
    ).

    (* [munify] fails *)
    IHateLtac B ltac:(fun p q =>
      match goal with
      | |- ?g =>
        assert_fails (munify g (@goal B p q))
      end
    ).

  Abort.

End Test.
