# `MetricComparison.lean`

## Local moving-distance continuity

`edistContAt_ctr` proves that, at every regular time `t`, the moving-metric
extended distance from a fixed center `O` is jointly continuous at `(t, O)`.
It uses only `IsSolutionOn` and `t ∈ D.regular`; it assumes no global Ricci
bound, completeness, `IsMetricNorm`, or extra realization interface.

The proof takes a compact regular time window from `exists_Icc_regular` and a
compact normal-coordinate ball at `O`.  Joint smooth metric control gives a
uniform chart-speed bound there.  The fixed-chart segment estimate
`param_edist_le` then bounds the moving distance by a constant times the model
coordinate displacement, which tends to zero at the center.  The private
helper `exists_param_speed` is the compact-family speed bound used in this
argument; it reuses the native metric-family quadratic-form continuity API.

## Verification and project position

Focused verification passed without warnings or placeholders.  No downstream
named refresh was run here; the coordinating lane must refresh this module
before checking the source-written `ShiBallCutoff.exists_cutoff_ctr` consumer.

Endpoint accounting: `edistContAt_ctr` is **100%**, and its dedicated local
metric-control machinery is **100%**.  This closes one local continuity input
for the P2 cutoff construction, not the local Shi estimate itself.
`shiRm1_ball`, `smooth_nlc`, P2, and the final Poincare theorem remain **0%**
theorem endpoints.  Against the current L-geometry plan, dedicated L8--L9
machinery remains about **78--80%**, reused generic infrastructure is **100%**,
and whole P0--P9 infrastructure remains about **15--25%**.
