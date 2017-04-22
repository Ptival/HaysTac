From HaysTac.Core Require Import
     Bind
     Enumerate
     LtacAliases
     With
.

(** [find_apply] looks for a hypothesis that can be [apply]-ed to your
    goal and performs the application. *)
(** [find_eapply] looks for a hypothesis that can be [eapply]-ed to
    your goal and performs the application. *)
(** [find_apply_in H] looks for a hypothesis that can be [apply]-ed in
    [H] and performs the application. *)
(** [find_eapply_in H] looks for a hypothesis that can be [eapply]-ed
    in [H] and performs the application. *)
(** [find_apply_in_hyp L] looks for a hypothesis [H] in which [L] can
    be [apply]-ed and performs the application. *)
(** [find_eapply_in_hyp L] looks for a hypothesis [H] in which [L] can
    be [eapply]-ed and performs the application. *)

Ltac find_apply           := with_hyp apply'.
Ltac find_eapply          := with_hyp eapply'.
Ltac find_apply_in      H := with_hyp ltac:(apply_selected_in  H).
Ltac find_eapply_in     H := with_hyp ltac:(eapply_selected_in H).
Ltac find_apply_in_hyp  L := with_hyp ltac:(apply_in_selected  L).
Ltac find_eapply_in_hyp L := with_hyp ltac:(eapply_in_selected L).

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
(** [find_erewrite_l] and [find_erewrite_r] find a hypothesis [H] to,
    respectively, [erewrite -> H] or [erewrite <- H] with, and perform
    the rewrite. *)

Ltac find_rewrite_l        := with_hyp rewrite_l.
Ltac find_rewrite_r        := with_hyp rewrite_r.
Ltac find_erewrite_l       := with_hyp erewrite_l.
Ltac find_erewrite_r       := with_hyp erewrite_r.
Ltac find_setoid_rewrite_l := with_hyp setoid_rewrite_l.
Ltac find_setoid_rewrite_r := with_hyp setoid_rewrite_r.

Ltac find_rewrite_l_in_hyp        := with_2_hyps rewrite_l_in_selected.
Ltac find_rewrite_r_in_hyp        := with_2_hyps rewrite_r_in_selected.
Ltac find_erewrite_l_in_hyp       := with_2_hyps erewrite_l_in_selected.
Ltac find_erewrite_r_in_hyp       := with_2_hyps erewrite_r_in_selected.
Ltac find_setoid_rewrite_l_in_hyp := with_2_hyps setoid_rewrite_l_in_selected.
Ltac find_setoid_rewrite_r_in_hyp := with_2_hyps setoid_rewrite_r_in_selected.

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
