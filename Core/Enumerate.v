(** [enumerate_hyps] multi-returns each hypothesis in context,
    starting from the most recently introduced one. *)
Ltac enumerate_hyps :=
  multimatch goal with
  | [ H : _ |- _ ] => H
  end.

(** [enumerate_hypotheses_reverse] multi-returns each hypothesis in
    context, starting from the least recently introduced one. *)
Ltac enumerate_reverse_hyps :=
  multimatch reverse goal with
  | [ H : _ |- _ ] => H
  end.

(** [enumerate_numbers_starting_from] multi-returns, in order, [n], [S
    n], etc. *)
Ltac enumerate_numbers_starting_from n :=
  multimatch n with
  | _ => n
  | _ => enumerate_numbers_starting_from (S n)
  end.

(** [enumerate_numbers] multi-returns, in order, [0], [1], etc. *)
Ltac enumerate_numbers := enumerate_numbers_starting_from 0.

(** [enumerate_numbers_up_to n] multi-returns, in order, [0], [1],
    etc., [n] *)
Ltac enumerate_numbers_up_to limit :=
  let n := enumerate_numbers in
  match n with
  | S limit => fail 2 (* fails the multimatch in enumerate_numbers *)
  | _ => n
  end.
