From HaysTac Require Import
     HaysTac
.

(** Regression for [find] *)

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

(** Regression for [on] *)

Goal forall F (b : F bool) (n : F nat) (u : F unit), F nat.
  intros.
  on nat exact'.
Qed.

Goal forall Q (A B C D : Type)
            (ABC : Q A B C) (ABD: Q A B D) (ACD : Q A C D) (BCD : Q B C D),
    Q A B D.
  intros.
  on (A, B, D) exact'.
Qed.

Goal forall (A B : Type) (a : A) (b : B),
    exists (p : (A * B)), True.
  intros.
  now on A ltac:(fun a => on B ltac:(fun B => exists (a, b))).
Qed.

Goal forall (A B : Type) (a : A) (a' : A) (a'' : A),
    exists (x : A), x = a'.
  intros.
  on_head A exists'; reflexivity.
Qed.
