From HaysTac.Core Require Import
     Subst
.

(** Coq's tactics are not really first-class, so aliasing them helps.
    Eta-expanding makes company-coq's auto-completion more pleasant,
    as it does not attemp to fill in the H. *)
Ltac apply'                := fun H => apply H.
Ltac destruct'             := fun H => destruct H.
Ltac eapply'               := fun H => eapply H.
Ltac edestruct'            := fun H => edestruct H.
Ltac erewrite_l            := fun H => erewrite <- H.
Ltac erewrite_r            := fun H => erewrite -> H.
Ltac exact'                := fun H => exact H.
Ltac exists'               := fun H => exists H.
Ltac generalize_dependent' := fun H => generalize dependent H.
Ltac idtac'                := fun H => idtac H.
Ltac induction'            := fun H => induction H.
Ltac injection'            := fun H => injection H.
Ltac inversion'            := fun H => inv_clear_subst H. (* I prefer this by default *)
Ltac revert'               := fun H => revert H.
Ltac rewrite_l             := fun H => rewrite <- H.
Ltac rewrite_r             := fun H => rewrite -> H.
Ltac setoid_rewrite_l      := fun H => setoid_rewrite <- H.
Ltac setoid_rewrite_r      := fun H => setoid_rewrite -> H.
Ltac simpl'                := fun H => simpl in H.
Ltac symmetry'             := fun H => symmetry in H.

(** For tactics with 2 arguments, we adopt the following convention:
    [action A1 in A2] becomes:

    - [action_in_selected A1] for [fun A2 => action A1 in A2]

    - [action_selected_in A2] for [fun A1 => action A1 in A2]

    This allows writing:

    - on selection ltac:(in_selected_apply my_lemma)

    - on selection ltac:(apply_selected_in my_hypothesis)

    Note that the latter is using names, so probably discouraged.
 *)

Ltac apply_in_selected            A1 := fun A2 => apply A1 in A2.
Ltac apply_selected_in            A2 := fun A1 => apply A1 in A2.

Ltac eapply_in_selected           A1 := fun A2 => eapply A1 in A2.
Ltac eapply_selected_in           A2 := fun A1 => eapply A1 in A2.

Ltac rewrite_l_in_selected        A1 := fun A2 => rewrite <- A1 in A2.
Ltac rewrite_l_selected_in        A2 := fun A1 => rewrite <- A1 in A2.
Ltac rewrite_r_in_selected        A1 := fun A2 => rewrite -> A1 in A2.
Ltac rewrite_r_selected_in        A2 := fun A1 => rewrite -> A1 in A2.

Ltac erewrite_l_in_selected       A1 := fun A2 => erewrite <- A1 in A2.
Ltac erewrite_l_selected_in       A2 := fun A1 => erewrite <- A1 in A2.
Ltac erewrite_r_in_selected       A1 := fun A2 => erewrite -> A1 in A2.
Ltac erewrite_r_selected_in       A2 := fun A1 => erewrite -> A1 in A2.

Ltac setoid_rewrite_l_in_selected A1 := fun A2 => setoid_rewrite <- A1 in A2.
Ltac setoid_rewrite_l_selected_in A2 := fun A1 => setoid_rewrite <- A1 in A2.
Ltac setoid_rewrite_r_in_selected A1 := fun A2 => setoid_rewrite -> A1 in A2.
Ltac setoid_rewrite_r_selected_in A2 := fun A1 => setoid_rewrite -> A1 in A2.

Ltac unfold_in_selected           A1 := fun A2 => unfold A1 in A2.
Ltac unfold_selected_in           A2 := fun A1 => unfold A1 in A2.

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

(** To be used with [on2] and [on3] *)
Ltac idtac2 x y   := idtac x y.
Ltac idtac3 x y z := idtac x y z.
