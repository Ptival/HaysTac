From Coq Require Import EquivDec.

Ltac destruct_EqDec a b := destruct (a == b).
