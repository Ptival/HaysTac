From HaysTac Require Import
     Subst
.

Ltac inv_clear H := inversion H; clear H.

Ltac inv_clear_subst H := inversion H; clear H; subst_all.
