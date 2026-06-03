Require Import ZArith Psatz.
Open Scope Z_scope.
#[local] Hint Extern 1 => nia : arith_hints.

Theorem max :
(forall x0 : Z, (forall x1 : Z, (forall _ :(Z.le 0 x0), (and (forall _ :(Z.ge (Z.add x0 x1) x1), (eq (Z.add x0 x1) (Z.add x0 x1)))(forall _ :(not (Z.ge (Z.add x0 x1) x1)), (eq x1 (Z.add x0 x1))))))).
Proof.
eauto 10 with arith_hints.
Qed.