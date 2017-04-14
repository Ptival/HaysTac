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

Theorem Forall2_app_inv_l : forall T (l1 l2 l' : list T) P,
    Forall2 P (l1 ++ l2) l' ->
    exists l1' l2', Forall2 P l1 l1' /\ Forall2 P l2 l2' /\ l' = l1' ++ l2'.
Proof.
  do 2 intro.
  on list induction'; intros.
  + eauto.
  + on_head Forall2 inversion'.
    on_head Forall2 find_apply_in.
    repeat on @ex destruct'.
    repeat on @and destruct'.
    subst_all.
    eexists (_ :: _).
    eauto.
Qed.
