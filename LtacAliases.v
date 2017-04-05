
From HaysTac Require Import Inv.

(* Coq's tactics are not really first-class, so aliasing them helps. *)
Ltac apply'                H := apply H.
Ltac destruct'             H := destruct H.
Ltac eapply'               H := eapply H.
Ltac erewrite_l            H := erewrite <- H.
Ltac erewrite_r            H := erewrite -> H.
Ltac exact'                H := exact H.
Ltac exists'               H := exists H.
Ltac generalize_dependent' H := generalize dependent H.
Ltac idtac'                H := idtac H.
Ltac induction'            H := induction H.
Ltac inversion'            H := inv_clear_subst H. (* I prefer this by default *)
Ltac rewrite_l             H := rewrite <- H.
Ltac rewrite_r             H := rewrite -> H.
Ltac simpl'                H := simpl in H.
Ltac symmetry'             H := symmetry in H.

(* [do'] and [repeat'] need a little extra care to be useful in
   practice: *)

Ltac do' n tac arg :=
  match n with
  | O => idtac
  | S ?n' => tac arg ; do' n' tac arg
  end.

Ltac repeat' tac arg :=
  progress tac arg; repeat' tac arg
  || idtac.
