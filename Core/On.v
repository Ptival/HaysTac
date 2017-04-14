From HaysTac Require Import
     Bind
     Enumerate
     Find
     Get
.

Local Ltac dbg flag tactic H :=
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

Ltac distinct_hyps H1 H2 := match H1 with H2 => fail 1 | _ => idtac end.

Local Ltac _on2 flag tuple tactic :=
  let H1 := find_hyp_mentioning_all tuple in
  let H2 := find_hyp_mentioning_all tuple in
  distinct_hyps H1 H2; dbg flag tactic H1 H2.

Ltac on2 := _on2 false.

Ltac on2' := _on2 true.

Local Ltac _on3 flag tuple tactic :=
  let H1 := find_hyp_mentioning_all tuple in
  let H2 := find_hyp_mentioning_all tuple in
  let H3 := find_hyp_mentioning_all tuple in
  distinct_hyps H1 H2;
  distinct_hyps H2 H3;
  distinct_hyps H1 H3;
  dbg flag tactic H1 H2 H3.

Ltac on3 := _on3 false.

Ltac on3' := _on3 true.

Local Ltac _on_head flag type tactic :=
  bind enumerate_hypotheses in
    ltac:(fun H =>
      match get_head_hyp H with
      | type => dbg flag tactic H
      end
    ).

(** [on_head type tac] finds a hypothesis [H] whose type starts with
    [type] and runs [tac H]. *)
Ltac on_head := _on_head false.

(** [on_head'] is the same as [on_head] but it outputs what hypothesis
    was used, for debugging purposes. *)
Ltac on_head' := _on_head true.
