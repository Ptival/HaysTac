From Coq Require Import
     List
.

From HaysTac Require Import
     HaysTac
.

Import ListNotations.

Theorem in_split : forall A x (l:list A),
    In x l -> exists l1 l2, l = l1 ++ x :: l2.
Proof.
  intros.
  on list induction'.
  - on In inversion'.
  - on In inversion'.
    + exists [].
      on list exists'.
      reflexivity.
    + on @eq find_specialize_in.
      do 2 on ex destruct'.
      eexists (_ :: _).
      eexists.
      simpl.
      apply f_equal.
      find_apply.
Qed.
