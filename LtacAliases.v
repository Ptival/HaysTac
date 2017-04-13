From HaysTac Require Import
     Inv
.

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
Ltac injection'            H := injection H.
Ltac inversion'            H := inv_clear_subst H. (* I prefer this by default *)
Ltac rewrite_l             H := rewrite <- H.
Ltac rewrite_r             H := rewrite -> H.
Ltac simpl'                H := simpl in H.
Ltac symmetry'             H := symmetry in H.

(** So that you can write:
    [on foo (in_unfold def)]
    [on foo (in_rewrite_r EQ)]
 *)
Ltac in_apply      X H := apply X in H.
Ltac in_eapply     X H := eapply X in H.
Ltac in_rewrite_l  X H := rewrite <- X in H.
Ltac in_rewrite_r  X H := rewrite -> X in H.
Ltac in_simpl        H := simpl in H.
Ltac in_unfold     X H := unfold X in H.

(** So that you can write:
    [on foo (rewrite_r_in H)]
 *)
Ltac apply_in     H X := apply X in H.
Ltac eapply_in    H X := eapply X in H.
Ltac rewrite_l_in H X := rewrite <- X in H.
Ltac rewrite_r_in H X := rewrite -> X in H.
Ltac simpl_in     H   := simpl in H.
Ltac unfold_in    H X := unfold X in H.

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
