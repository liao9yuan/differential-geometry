# PointedConvergence

Source used: MSM135 Chapter 3 Definition 3.1 and the following paragraph on exhaustions by open sets, together with the chapter's pointed Cheeger-Gromov-Hamilton convergence setup.

Introduced definitions: `metricCovDerivStep`, `metricCovDeriv`, `metricDiffCovDerivAt`, `metricDerivNorm`, `metricDerivNormSupOn`, `MetricCPConvOn`, `MetricCInfConvOn`, `MetricCInfConvOnCompacts`, `MetricCInfConvData`, `ExhaustsByOpen`, `PointedCGHMaps`, `SourceDomain`, `sourceCompactSet`, `SourceDomainMetricData`, `SourceMetricCPConvOn`, `SourceMetricCPConvOnWindow`, `SourceMetricConvergenceData`, `SourceSpacetimeConvergenceData`, `FunctionPullbackTendsto`, `ScalarPullbackTendsto`, `PointedCGConverges`, and `SmoothCGHConverges`.

The `C^p` definition is formalized using the displayed `sup_{0 <= alpha <= p} sup_{x in K}` condition. `metricDerivNorm` is now concrete: it uses the Levi-Civita connection of the reference metric `g` and the metric-induced tensor norm. The tensor `nabla^a(g_k - g_infty)` is represented as `nabla^a g_k - nabla^a g_infty`, which is the Lean-friendly form of the same expression by linearity of covariant differentiation.

`MetricCPConvOn` now takes compactness of `K` as an explicit hypothesis. The raw `metricDerivNormSupOn` remains available only as the low-level supremum used under that compactness hypothesis.

`ExhaustsByOpen` now records openness, monotonicity `U k ⊆ U (k+1)`, and eventual containment of every compact subset. `PointedCGHMaps` stores actual smooth `PartialDiffeomorph` data rather than an arbitrary predicate, and the projection helpers `source`, `target`, and `map` make clear that the semantic convergence lives on the open sources.

For MSM135 Definition 3.2, the file now has an HCG-local open-domain metric layer. `SourceDomainMetricData` keeps the source-subtype topology/manifold instances, restricted limit metrics, pulled-back sequence metrics, reference metrics, compact-preimage input, and the `mfderiv` inner-product formulas. `SourceMetricConvergenceData` and `SourceSpacetimeConvergenceData` are data-bearing convergence records, not arbitrary `Prop` placeholders.

`FunctionPullbackTendsto.le_of_bound0` is the reusable order-closure bridge for Section 12 pinching transfer: pointwise pullback convergence plus eventual upper bounds tending to zero gives arbitrary positive upper bounds on the limit value. `ScalarPullbackTendsto` is a concrete field of `SmoothCGHConverges`.

Frontier: the remaining honest backend is construction of the open-source subtype manifold metrics and their pullback/restriction formulas from general RicciFlower manifold infrastructure, plus the trace-free Ricci/pinching-ratio pullback convergence producer needed by Hamilton Section 12. These frontiers are located in the HCG source-domain and function-pullback layers, not hidden behind placeholder convergence predicates.

2026-05-27 review update: the fixed-manifold `C^p` convergence API and `SourceDomainMetricData` no longer expose a public `IsManifold I (∞ + 1)`/`smoothPlus` assumption. The derivative definitions and source-domain supremum derive `∞ + 1` locally from the stored `IsManifold I ∞` instance when a lower RicciFlower producer needs that exact instance.

Verification: passed for this file and for the Ricci-flow convergence wrapper.

2026-05-29 Lemma 3.11 update: added the first-order local-frame bridge for
the background covariant derivative of a metric tensor.  The new theorems
`metricCovDeriv_one_eval_smooth_slots`,
`metricCovDeriv_one_eval_localFrame`, and
`metricCovDeriv_one_component_localFrame` express the first displayed formula
in the second part of MSM135 Lemma 3.11 in terms of the concrete
`metricCovDeriv` API.  This connects the HCG convergence norm to local-frame
Christoffel/connection-difference estimates without introducing a new
placeholder operator for `nabla - nabla_k`.

Verification: passed for this file after the local-frame bridge.
