From HaysTac.Core Require Import
     Assert
     Enumerate
.

(** [with_hyp t] enumerates hypotheses [H] and succeeds on the first
    success of [t H]. *)
Ltac with_hyp t :=
  let H := enumerate_hyps in
  t H.

(** [with_2_hyps t] enumerates pairs of distinct hypotheses [H1] [H2]
    and succeeds on the first success of [t H1 H2]. *)
Ltac with_2_hyps t :=
  let H1 := enumerate_hyps in
  let H2 := enumerate_hyps in
  assert_distinct H1 H2;
  t H1 H2.

(** [with_3_hyps t] enumerates triples of distinct hypotheses [H1]
    [H2] [H3] and succeeds on the first success of [t H1 H2 H3]. *)
Ltac with_3_hyps t :=
  let H1 := enumerate_hyps in
  let H2 := enumerate_hyps in
  let H3 := enumerate_hyps in
  assert_distinct H1 H2;
  assert_distinct H1 H3;
  assert_distinct H2 H3;
  t H1 H2 H3.
