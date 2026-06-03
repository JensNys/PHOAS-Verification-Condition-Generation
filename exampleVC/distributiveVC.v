Require Import ZArith Psatz.
Open Scope Z_scope.
#[local] Hint Extern 1 => nia : arith_hints.

Theorem distributiveVC :
(forall x0 : Z, (forall x1 : Z, (forall x2 : Z, (forall _ :True, (eq (Z.add (Z.mul x0 x1) (Z.mul x0 x2)) (Z.mul x0 (Z.add x1 x2))))))).
Proof.
eauto 10 with arith_hints.
Qed.