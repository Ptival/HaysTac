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

Lemma in_prod_iff :
  forall A B (l : list A) (l' : list B) (x : A) (y : B),
    In (x,y) (list_prod l l') <-> In x l /\ In y l'.
Proof.
  split.
  - on (list A) induction'; simpl; intros.
    + intuition.
    + on In ltac:(in_apply in_app_or).
      on @or destruct'.
      * on_head In ltac:(in_apply in_map_iff).
        on @ex destruct'.
        on @and destruct'.
        on_head @eq inversion'.
        auto.
      * intuition.
  - intros.
    now apply in_prod.
Qed.
