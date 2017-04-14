
(** [get_type_of H] returns the type of H *)
Ltac get_type_of H :=
  match type of H with
  | ?T => T
  end.

(** [get_head_type T] returns the head constructor of term [T]. *)
Ltac get_head_type T :=
  multimatch T with
  | ?P _ _ _ _ _ _ _ _ _ _ _ _ => constr:(P)
  | ?P _ _ _ _ _ _ _ _ _ _ _   => constr:(P)
  | ?P _ _ _ _ _ _ _ _ _ _     => constr:(P)
  | ?P _ _ _ _ _ _ _ _ _       => constr:(P)
  | ?P _ _ _ _ _ _ _ _         => constr:(P)
  | ?P _ _ _ _ _ _ _           => constr:(P)
  | ?P _ _ _ _ _ _             => constr:(P)
  | ?P _ _ _ _ _               => constr:(P)
  | ?P _ _ _ _                 => constr:(P)
  | ?P _ _ _                   => constr:(P)
  | ?P _ _                     => constr:(P)
  | ?P _                       => constr:(P)
  | ?P                         => constr:(P)
  end.

(** [get_head_hyp H] returns the head constructor of hypothesis [H]. *)
Ltac get_head_hyp H := get_head_type ltac:(get_type_of H).
