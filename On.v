
From HaysTac Require Import Find.
From HaysTac Require Import GetHead.

Ltac dbg flag tactic H :=
  match constr:(flag) with
  | true => tactic H; idtac H
  | false => tactic H
  end.

Local Ltac _on flag tuple tactic :=
  let H := find_hyp_mentioning_all tuple in
  dbg flag tactic H.

(** [on (t1, ..., tn) tac] finds a hypothesis [H] whose type mentions
    all the terms [t1], ..., [tn], and runs [tac H]. *)
Ltac on := _on false.

(** [on'] is the same as [on] but it outputs what hypothesis was used,
    for debugging purposes. *)
Ltac on' := _on true.

Ltac _on_head flag type tactic :=
  match goal with
  | [ H : ?U |- _ ] =>
    match get_head_type U with
    | type => dbg flag tactic H
    end
  end.

(** [on_head type tac] finds a hypothesis [H] whose type starts with
    [type] and runs [tac H]. *)
Ltac on_head := _on_head false.

(** [on_head'] is the same as [on_head] but it outputs what hypothesis
    was used, for debugging purposes. *)
Ltac on_head' := _on_head true.
