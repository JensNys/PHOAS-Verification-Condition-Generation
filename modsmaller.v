Require Import ZArith Psatz.
Open Scope Z_scope.
#[local] Hint Extern 1 => nia : arith_hints.

Theorem modsmaller :
(forall x0 : Z, (forall x1 : Z, (forall _ :(and (Z.le 0 x1)(Z.le 0 x0)), (and (forall _ :(Z.lt x1 x0), (Z.lt x1 x0))(forall _ :(not (Z.lt x1 x0)), (exists x2 : Z, (exists x3 : Z, (and (and (eq x3 x0)(and (eq x2 (Z.sub x1 x0))True))(and (and (Z.le 0 x3)(Z.le 0 x2))(forall x4 : Z, (forall _ :(Z.lt x4 x2), (Z.lt x4 x0)))))))))))).
Proof.
eauto 10 with arith_hints.
Qed.