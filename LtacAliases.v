
From HaysTac Require Import Inv.

(* Coq's tactics are not really first-class, so aliasing them helps. *)
Ltac apply'     H := apply H.
Ltac destruct'  H := destruct H.
Ltac exact'     H := exact H.
Ltac exists'    H := exists H.
Ltac idtac'     H := idtac H.
Ltac induction' H := induction H.
Ltac inversion' H := inv_clear_subst H. (* I prefer this by default *)
Ltac lrewrite   H := rewrite <- H.
Ltac rrewrite   H := rewrite -> H.
Ltac simpl'     H := simpl in H.
Ltac symmetry'  H := symmetry in H.
