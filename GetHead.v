
(** [get_head_type T] returns the head constructor of term [T]. *)
Ltac get_head_type T :=
  match T with
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
Ltac get_head_hyp H :=
  match type of H with
  | ?T => get_head_type T
  end.
