Require Import ZArith Psatz.
Open Scope Z_scope.
#[local] Hint Extern 1 => nia : arith_hints.

Theorem mySumVerificationCondition :
(forall x0 : Z, (forall _ :(Z.ge x0 0), (and (forall _ :(eq 0 x0), (eq (Z.mul 2 0) (Z.mul x0 (Z.add x0 1))))(forall _ :(not (eq 0 x0)), (exists x1 : Z, (and (and (eq x1 (Z.sub x0 1))True)(and (Z.ge x1 0)(forall x2 : Z, (forall _ :(eq (Z.mul 2 x2) (Z.mul x1 (Z.add x1 1))), (eq (Z.mul 2 (Z.add x0 x2)) (Z.mul x0 (Z.add x0 1)))))))))))).
Proof.
eauto 10 with arith_hints.
Qed.