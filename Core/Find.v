From HaysTac.Core Require Import
     Bind
     Enumerate
     LtacAliases
.

(** [find_apply] looks for a hypothesis that can be [apply]-ed to your
    goal and performs the application. *)
Ltac find_apply := bind enumerate_hyps in apply'.

(** [find_eapply] looks for a hypothesis that can be [eapply]-ed to
    your goal and performs the application. *)
Ltac find_eapply := bind enumerate_hyps in eapply'.

(** [find_apply_in H] looks for a hypothesis that can be [apply]-ed in
    [H] and performs the application. *)
Ltac find_apply_in H := bind enumerate_hyps in ltac:(fun X => apply X in H).

(** [find_eapply_in H] looks for a hypothesis that can be [eapply]-ed
    in [H] and performs the application. *)
Ltac find_eapply_in H := bind enumerate_hyps in ltac:(fun X => eapply X in H).

(** [apply_in_hyp L] looks for a hypothesis [H] in which [L] can be
    [apply]-ed and performs the application. *)
Ltac apply_in_hyp L := bind enumerate_hyps in ltac:(fun H => apply L in H).

(** [eapply_in_hyp L] looks for a hypothesis [H] in which [L] can be
    [eapply]-ed and performs the application. *)
Ltac eapply_in_hyp L := bind enumerate_hyps in ltac:(fun H => eapply L in H).

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
Ltac find_hyp_mentioning_all tuple :=
  let H := enumerate_hyps in
  check_hyp_mentions_all H tuple.

(** [find_rewrite_l] and [find_rewrite_r] find a hypothesis [H] to,
    respectively, [rewrite -> H] or [rewrite <- H] with, and perform
    the rewrite. *)
Ltac find_rewrite_l := bind enumerate_hyps in rewrite_l.
Ltac find_rewrite_r := bind enumerate_hyps in rewrite_r.

(** [find_erewrite_l] and [find_erewrite_r] find a hypothesis [H] to,
    respectively, [erewrite -> H] or [erewrite <- H] with, and perform
    the rewrite. *)
Ltac find_erewrite_l := bind enumerate_hyps in erewrite_l.
Ltac find_erewrite_r := bind enumerate_hyps in erewrite_r.

(** [find_specialize_in H] looks for a value [v] such that is can
    [specialize (H v)]. *)
Ltac find_specialize_in H :=
  multimatch goal with
  | [ v : _ |- _ ] => specialize (H v)
  end.

(** [find_specialize] looks for a hypothesis [H] and a value [v] such
    that is can [specialize (H v)]. *)
Ltac find_specialize :=
  multimatch goal with
  | [ H : _, v : _ |- _ ] => specialize (H v)
  end.
