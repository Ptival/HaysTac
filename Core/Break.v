From Coq Require Import
     DecidableClass
.

From HaysTac.Core Require Import
     Enumerate
     Subst
     With
.

Ltac break_decide_in H :=
  match type of H with
  | context [ decide ?P ] => let D := fresh "DECIDE" in _decide_ P D
  end.

Ltac break_decide_in_hyp := with_hyp break_decide_in.

Ltac break_decide_in_goal :=
  match goal with
  | [ |- context [ decide ?P ] ] => let D := fresh "DECIDE" in _decide_ P D
  end.

Ltac break_let_pair_in H :=
  match type of H with
  | context [ let (_, _) := ?d in _ ] => destruct d eqn:?; subst_all
  end.

Ltac break_let_pair_in_hyp := with_hyp  break_let_pair_in.

Ltac break_let_pair_in_goal :=
  match goal with
  | [ |- context [ let (_, _) := ?d in _ ] ] => destruct d eqn:?; subst_all
  end.

Ltac break_match_in H :=
  match type of H with
  | context [ match ?d with _ => _ end ] => destruct d eqn:?
  end.

Ltac break_match_in_hyp := with_hyp break_match_in.

Ltac break_match_in_goal :=
  match goal with
  | [ |- context [ match ?d with _ => _ end ] ] => destruct d eqn:?
  end.

Ltac break_if_in H :=
  match type of H with
  | context [ if ?d then _ else _ ] => destruct d eqn:?
  end.

Ltac break_if_in_hyp := with_hyp break_if_in.

Ltac break_if_in_goal :=
  match goal with
  | [ |- context [ if ?d then _ else _ ] ] => destruct d eqn:?
  end.
