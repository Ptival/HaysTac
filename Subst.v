
Ltac subst_one :=
  match goal with
  | [ H : ?X = _ |- _ ] => subst X
  | [ H : _ = ?X |- _ ] => subst X
  end.

Ltac subst_all := repeat subst_one.
