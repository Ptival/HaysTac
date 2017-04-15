
Ltac assert_distinct X Y := match X with Y => fail 1 | _ => idtac end.

Ltac assert_same X Y := match X with Y => idtac end.
