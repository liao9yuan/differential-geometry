# LowRegDeTurckOpen

## 2026-08-05 - concrete positive per-metric endpoint

`lowreg_dt_open` specializes `lowreg_joint_open` with
`deTurckRicciRHS g` and discharges its representation input by
`deTurck_rem_repr`.  The result has no additional analytic assumption: every
fixed three-dimensional metric receives a positive, metric-dependent horizon
with the realized Ricci--DeTurck evolution and full joint chart-Gram
regularity package.

Focused verification and the targeted module build passed warning-free.  The
endpoint is included in the 80-declaration ShortTime axiom census and uses only
the standard three axioms.  This closes the self-background per-metric endpoint
only.  A fixed-background class-uniform producer and the DeTurck-to-Ricci
pullback remain separate frontiers.
