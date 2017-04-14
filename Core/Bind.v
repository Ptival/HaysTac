
(** [bind t1 in t2] performs tactic [t1] and passes the result to
    [t2]. *)
Tactic Notation "bind" tactic(a) "in" tactic(b) := (let H := a in b H).
