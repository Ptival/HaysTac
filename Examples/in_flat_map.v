(* Adapted from, thus following the license of: *)

(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

From Coq Require Import List.

From HaysTac Require Import HaysTac.

Import ListNotations.

Lemma in_flat_map : forall A B (f : A -> list B) (l : list A) (y : B),
    In y (flat_map f l) <-> exists x, In x l /\ In y (f x).
Proof.
  do 4 intro.
  on list induction'; simpl; split; intros.
  + contradiction.
  + on @ex ltac:(fun H => repeat (destruct H)).
  + on_head In ltac:(in_apply in_app_or).
    on_head or destruct'.
    * eauto.
    * on_head In find_apply_in.
      on @ex destruct'.
      on @and destruct'.
      eauto.
  + apply in_or_app.
    on @ex destruct'.
    on @and destruct'.
    on @or destruct'.
    * subst. auto.
    * right.
      on @iff apply'.
      eauto.
Qed.
