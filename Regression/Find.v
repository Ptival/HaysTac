From HaysTac Require Import
     HaysTac
.

Goal forall A B C D (a : A) (ab : A -> B) (bc : B -> C) (cd : C -> D), D.
  intros.
  do 4 find_apply.
Qed.

Goal forall A B C D (a : A) (ab : A -> B) (bc : B -> C) (cd : C -> D), D.
  intros.
  find_specialize_in ab.
  find_specialize_in bc.
  find_specialize_in cd.
  exact cd.
Qed.
