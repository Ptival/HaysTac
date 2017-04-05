From Coq Require Export Lists.List.

Set Implicit Arguments.

Import ListNotations.

Theorem Forall_cons_inv_tail T R (h : T) t : Forall R (h :: t) -> Forall R t.
Proof. now inversion 1. Qed.

Hint Resolve Forall_cons_inv_tail.

Theorem Forall2_cons_inv_tail_l T1 T2 R (h1 : T1) t1 (l2 t2 : list T2) :
  t2 = tl l2 ->
  Forall2 R (h1 :: t1) l2 ->
  Forall2 R t1 t2.
Proof. inversion 2. now subst. Qed.

Hint Resolve Forall2_cons_inv_tail_l.

Theorem Forall2_cons_inv_tail_r T1 T2 R (h2 : T2) (l1 t1 : list T1) t2 :
  t1 = tl l1 ->
  Forall2 R l1 (h2 :: t2) ->
  Forall2 R t1 t2.
Proof. inversion 2. now subst. Qed.

Hint Resolve Forall2_cons_inv_tail_r.

Theorem Forall2_cons_inv_tail T R (h1 h2 : T) t1 t2 :
  Forall2 R (h1 :: t1) (h2 :: t2) -> Forall2 R t1 t2.
Proof. now inversion 1. Qed.

Hint Resolve Forall2_cons_inv_tail.
