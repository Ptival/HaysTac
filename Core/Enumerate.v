
(** [enumerate_hypotheses] enumerates each hypothesis in context,
    starting from the most recently introduced one. *)
Ltac enumerate_hypotheses :=
  multimatch goal with
  | [ H : _ |- _ ] => H
  end.

(** [enumerate_hypotheses_reverse] enumerates each hypothesis in context,
    starting from the least recently introduced one. *)
Ltac enumerate_hypotheses_reverse :=
  multimatch reverse goal with
  | [ H : _ |- _ ] => H
  end.

(** [enumerate_numbers_starting_from] returns, in order, [n], [S n], etc. *)
Ltac enumerate_numbers_starting_from n :=
  multimatch n with
  | _ => n
  | _ => enumerate_numbers_starting_from (S n)
  end.

(** [enumerate_numbers] returns, in order, [0], [1], etc. *)
Ltac enumerate_numbers := enumerate_numbers_starting_from 0.

(** [enumerate_numbers_up_to n] returns, in order, [0], [1], etc., [n] *)
Ltac enumerate_numbers_up_to limit :=
  let n := enumerate_numbers in
  match n with
  | S limit => fail 2 (* fails the multimatch in enumerate_numbers *)
  | _ => n
  end.
