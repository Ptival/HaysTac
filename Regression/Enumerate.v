From HaysTac Require Import HaysTac.

Goal exists n, n = 7.
  let n := enumerate_numbers in
  idtac "Trying" n;
  exists n; reflexivity.
Qed.
