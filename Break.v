Ltac break_let_pair_in H :=
  match type of H with
  | context [ let (_, _) := ?d in _ ] => destruct d eqn:?; subst_all
  end.

Ltac break_let_pair_in_goal :=
  match goal with
  | [ |- context [ let (_, _) := ?d in _ ] ] => destruct d eqn:?; subst_all
  end.

Ltac break_match_in H :=
  match type of H with
  | context [ match ?d with _ => _ end ] => destruct d eqn:?
  end.

Ltac break_match_in_goal :=
  match goal with
  | [ |- context [ match ?d with _ => _ end ] ] => destruct d eqn:?
  end.

Ltac break_if_in H :=
  match type of H with
  | context [ if ?d then _ else _ ] => destruct d eqn:?
  end.

Ltac break_if_in_goal :=
  match goal with
  | [ |- context [ if ?d then _ else _ ] ] => destruct d eqn:?
  end.
