
From HaysTac Require Import Bind.
From HaysTac Require Import Enumerate.
From HaysTac Require Import LtacAliases.

(** [find_apply] looks for a hypothesis that can be [apply]-ed to your
    goal and performs the application. *)
Ltac find_apply := bind enumerate_hypotheses in apply'.

(** [find_apply_in H] looks for a hypothesis that can be [apply]-ed in
    [H] and performs the application. *)
Ltac find_apply_in H := bind enumerate_hypotheses in (fun X => apply X in H).

(** [check_hyp_mentions_all H tuple] returns [H] if its type mentions all
    the terms in nested tuple [tuple], fails otherwise. *)
Ltac check_hyp_mentions_all H tuple :=
  match tuple with
  | (?ms, ?m) =>
    match type of H with
    | context[ m ] => check_hyp_mentions_all H ms
    end
  | ?m =>
    match type of H with
    | context[ m ] => H
    end
  end.

(** [find_hyp_mentioning_all tuple] returns a hypothesis that mentions all
    the terms in nested tuple [tuple] if it exists, fails otherwise. *)
Ltac find_hyp_mentioning_all list :=
  let H := enumerate_hypotheses in
  check_hyp_mentions_all H list.

(** [find_specialize_in H] *)
Ltac find_specialize_in H :=
  multimatch goal with
  | [ v : _ |- _ ] => specialize (H v)
  end.

Ltac find_n_specializes_in n H :=
  match n with
  | 0 => idtac
  | S ?n' => find_specialize_in H; find_n_specializes_in n' H
  end.
