From HaysTac.Core Require Import
     Subst
.

Ltac inv_clear H := inversion H; clear H.

Ltac inv_clear_subst H :=
  inversion H;
  try (clear H); (* sometimes H can't be cleared because it's referred to *)
  subst_all.
