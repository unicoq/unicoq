Require Unicoq.Unicoq.

Set Unicoq Debug.

Definition test_oneS : _ (S _) = S 0 + 0 := eq_refl.

(* wont go under binders *)
Fail Definition test_binder : _ (S _) = forall x, S x > 0 := eq_refl.

(* two occurrences, no go *)
Fail Definition test_twoS : _ (S _) = (S 0, S 1, 0) := eq_refl.

(* two occurrences of the head, but only one matches: OK *)
Definition test_twoS_OK : _ (S (S _)) = (S 0, S 1, 0) := eq_refl.

Definition test_def : _ (1 + _) = (S 0, _ + 1, 0) := eq_refl.

Definition test_type : _ (list nat) = (fun A B : Type => A = B) (list nat) (list Prop) := eq_refl.

Definition test_twoS_stillOK x : _ (S x) = (S x, S 1, 0) := eq_refl.
Definition test_twoS_stillOK' x : _ (S x) = (S 1, S x, 0) := eq_refl.


(* Local Variables: *)
(* coq-prog-name: "coqtop.byte" *)
(* coq-load-path: nil *)
(* End: *)
