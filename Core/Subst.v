From HaysTac.Core Require Import
     Get
     Inv
.

Local Ltac subst_one :=
  match goal with
  | [_ : ?X = _ |- _] => subst X
  | [_ : _ = ?X |- _] => subst X
  | [H : ?L = ?R |- _] =>
    let LH := get_head_type L in
    let RH := get_head_type R in
    is_constructor LH;
    match RH with LH => inv_clear H end
  end.

(** [subst_all] performs as many substitutions as possible, including
    substitutions obtained from inverting equalities like [C ?a =
    C ?b] for some constructor [C]. *)
Ltac subst_all := repeat subst_one.

Ltac inv_clear_subst H := inv_clear H; subst_all.
