From HaysTac Require Import HaysTac.

Goal exists n, n = 7.
  let n := enumerate_numbers in
  idtac "Trying" n;
    exists n; reflexivity.
Qed.

Goal exists n, n = 7.
  Fail
    let n := enumerate_numbers_up_to 6 in
    idtac "Trying" n;
      exists n; reflexivity.
  let n := enumerate_numbers_up_to 7 in
  idtac "Trying" n;
    exists n; reflexivity.
Qed.
