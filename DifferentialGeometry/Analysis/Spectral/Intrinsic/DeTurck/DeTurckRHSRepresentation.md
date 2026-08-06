# DeTurckRHSRepresentation

## 2026-08-05 - reusable realized-RHS bridge

`deTurck_rem_repr` extracts the representation identity that had previously
lived as a local proof inside the supercritical short-time theorem.  It proves
that the symmetrized low-regularity remainder plus the frozen connection
Laplacian evaluates to the Ricci--DeTurck right-hand side at the realized
metric.

The proof reuses the local slot-swap equivariance of the connection Laplacian
and the existing metric-realization symmetry theorem.  Two small private
component lemmas keep this analysis-layer module independent of the
HeatSemigroup endpoint layer.  Focused verification and the targeted module
build passed warning-free.  The bridge is included in the 80-declaration
ShortTime axiom census and uses only the standard three axioms.
