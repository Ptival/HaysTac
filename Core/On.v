From HaysTac.Core Require Import
     Assert
     Bind
     Enumerate
     Find
     Get
     With
.

Local Ltac dbg flag tactic H :=
  match constr:(flag) with
  | true => tactic H; idtac H
  | false => tactic H
  end.

(** [on (t1, ..., tn) tac] finds a hypothesis [H] whose type mentions
    all the terms [t1], ..., [tn], and runs [tac H].  [on'] is the
    same as [on] but it outputs what hypothesis was used, for
    debugging purposes. *)
Local Ltac _on flag tuple tactic :=
  let H := find_hyp_mentioning_all tuple in
  dbg flag tactic H.
Ltac on  := _on false.
Ltac on' := _on true.

Local Ltac _on2 flag tuple tactic := with_2_hyps ltac:(dbg flag tactic).
Ltac on2  := _on2 false.
Ltac on2' := _on2 true.

Local Ltac _on3 flag tuple tactic := with_3_hyps ltac:(dbg flag tactic).
Ltac on3  := _on3 false.
Ltac on3' := _on3 true.

(** [on_head type tac] finds a hypothesis [H] whose type starts with
    [type] and runs [tac H].  [on_head'] is the same as [on_head] but
    it outputs what hypothesis was used, for debugging purposes. *)
Local Ltac _on_head flag type tactic :=
  with_hyp ltac:(
    fun H =>
      assert_same ltac:(get_head_hyp H) type;
      dbg flag tactic H
  ).
Ltac on_head := _on_head false.
Ltac on_head' := _on_head true.


Local Ltac _on_head2 flag type tactic :=
  with_2_hyps ltac:(
    fun H1 H2 =>
      assert_same ltac:(get_head_hyp H1) type;
      assert_same ltac:(get_head_hyp H2) type;
      dbg flag tactic H1 H2
  ).
Ltac on_head2 := _on_head2 false.
Ltac on_head2' := _on_head2 true.

Local Ltac _on_head3 flag type tactic :=
  with_3_hyps ltac:(
    fun H1 H2 H3 =>
      assert_same ltac:(get_head_hyp H1) type;
      assert_same ltac:(get_head_hyp H2) type;
      assert_same ltac:(get_head_hyp H3) type;
      dbg flag tactic
  ).
Ltac on_head3 := _on_head3 false.
Ltac on_head3' := _on_head3 true.
