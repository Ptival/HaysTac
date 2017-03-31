
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
