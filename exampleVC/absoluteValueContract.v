Require Import ZArith.
Require Import Lia.
Open Scope Z_scope.

Theorem absoluteValueContract :
(forall x : Z, (forall _ :True, (and (forall _ :(Z.lt x 0), (and (Z.ge (Z.sub 0 x) 0)(Z.ge (Z.sub 0 x) x)))(forall _ :(not (Z.lt x 0)), (and (Z.ge x 0)(Z.ge x x)))))).
Proof.
lia.
Qed.