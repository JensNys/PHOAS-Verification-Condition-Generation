Require Import ZArith Psatz.
Open Scope Z_scope.
#[local] Hint Extern 1 => nia : arith_hints.

Theorem test_file :
(forall x0 : Z, (forall _ :True, (and (forall _ :(Z.lt x0 0), (and (Z.ge (Z.sub 0 x0) 0)(Z.ge (Z.sub 0 x0) x0)))(forall _ :(not (Z.lt x0 0)), (and (Z.ge x0 0)(Z.ge x0 x0)))))).
Proof.
eauto 10 with arith_hints.
Qed.