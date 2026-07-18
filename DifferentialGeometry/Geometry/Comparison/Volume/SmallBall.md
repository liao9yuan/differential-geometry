# SmallBall

## 2026-07-17

Added the pointwise small-geodesic-ball lower route needed by Perelman's
dyadic selector.  It uses chart-local continuity and positivity of the actual
normal-coordinate density, then the existing realized metric-ball lower
consumer.  The conclusion chooses a positive normalized-volume constant and
radius for each fixed metric and centre; no Bishop--Gromov hypothesis or
uniform injectivity radius is added.

`exists_edist_vol` packages the same lower bound for the explicit
`riemannianEDistOf g` carrier used by `FlowMetricBall`.  Its proof installs the
bundle, emetric, and finite Hopf--Rinow metric belonging to `g` locally, then
proves equality of the two ball carriers.  This keeps the topology/norm diamond
out of downstream scale-selection statements.

This pointwise constant is sufficient: geometric decay under persistently bad
dyadic ratios would force normalized volume to zero at that same centre.

Focused verification passed without warnings.
