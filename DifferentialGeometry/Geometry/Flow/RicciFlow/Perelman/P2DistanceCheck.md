# P2DistanceCheck

## Role

This diagnostic module isolates the fixed-endpoint changing-distance chain
from the larger P2 audit.  It exists because the unified audit still imports a
separate fixed-center Gaussian-tail adapter whose named artifact is blocked by
a dirty comparison/Jacobi dependency cone.

## Scope

The audit prints the canonical fixed-path Ricci-flow length derivative, the
static endpoint-Ricci integral estimate, the short- and long-distance
differentiable upper supports, the chosen-metric triangle and symmetry facts,
the abstract moving-endpoint slope transfer, both fixed- and varying-metric
endpoint-rate producers, and the final short/long moving-distance conclusions.
It adds no declarations and does not replace the unified `P2AxiomCheck`.

## Verification

The expanded eleven-declaration focused audit is warning-free GREEN.  Every
printed declaration, including `edist_inc_tendsto`, `edist_smooth_rate`,
`dist_short_slope`, and `dist_long_slope`, uses only `propext`,
`Classical.choice`, and `Quot.sound`.  No named refresh of this diagnostic
module is required because it has no downstream consumer.
