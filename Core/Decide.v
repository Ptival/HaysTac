(** Use [decide_equality] when your goal looks like: [{ x = y } + { x
    <> y }] and there's enough information in the context to solve
    it. *)
Ltac decide_equality :=
  try solve
      [ left; congruence
      | right; congruence
      ].
