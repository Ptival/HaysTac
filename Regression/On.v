From HaysTac Require Import
     HaysTac
.

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
  now on A ltac:(fun a => on B ltac:(fun b => exists (a, b))).
Qed.

Goal forall (A B : Type) (a : A) (a' : A) (a'' : A),
    exists (x : A), x = a'.
  intros.
  on_head A exists'; reflexivity.
Qed.

Goal forall P (A B : Type) (a : P A B) (b : P B B), P A B.
  intros.
  on_head (P A) exact'.
Qed.
