# ThreeArmJointAlgebra

This module is the public algebra layer for
`linearizedRicciThreeArmHjoint`.  It exposes closure under coefficient-family
addition, subtraction, and constant scalar multiplication without importing a
Ricci--DeTurck consumer.

Focused verification passed.  The only development repair was the standard
transparency setting needed to avoid the model-space `NormedSpace` instance
diamond; the final source uses no `whnf`.

This is dedicated infrastructure; it does not prove
`ricci_flow_unif_existence`, which remains 0% as a theorem.
