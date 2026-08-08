# ThreeArmJointAlgebra

This module is the public algebra layer for
`linearizedRicciThreeArmHjoint`.  It exposes closure under constant families,
coefficient-family addition, subtraction, constant scalar multiplication, and
postcomposition by a fixed smooth coefficient without importing a
Ricci--DeTurck consumer.  The two new generic declarations are
`threeArmJoint_const` and `threeArmJoint_comp`; they replace consumer-local
copies needed by the diagonal full-slope path-integral normal form.

Focused verification status for the new closures is recorded below.  The
module retains the standard transparency setting needed to avoid the
model-space `NormedSpace` instance diamond; the final source uses no `whnf`.

## 2026-08-08 — constant and fixed-composition closures

The two declarations are routine joint-smoothness infrastructure at the
lowest reusable three-arm algebra layer.  They add no geometric hypotheses and
do not assert any off-diagonal Ricci--DeTurck action identity.

Focused verification passed with the requested four-thread, 6144 MB cap.

This is dedicated infrastructure; it does not prove
`ricci_flow_unif_existence`, which remains 0% as a theorem.
