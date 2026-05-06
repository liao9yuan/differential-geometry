# RicciFlow Formalization Plan

This is the current working plan for the synthetic Ricci-flow branch after the
P4 producer closeout. Keep it short enough to read before a coding session.

## Current Shape

This branch owns the synthetic tensor/evolution/curvature-algebra/pinching
layer and the Section 12 assembly for `RicciFlow/main.tex`.

The collaborator-facing analytic/global layer remains explicit: short-time
existence, maximal interval construction, extension criteria, maximum
principles, point selection, Perelman noncollapsing, Hamilton-CGH compactness,
Myers compactness, and smooth manifold realization are interfaces, not goals of
this branch.

Presentation and boundary files:

- `blackbox.lean`: the named boundary for analytic black boxes, plus the
  experimental smooth-initial-metric maximal-flow skeleton. It correctly states
  the maximal-time dichotomy: a maximal flow may be long-time, and only a
  finite maximal endpoint is singular/nonextendable.
- `wordlyLatex.lean`: a theorem-by-theorem presentation spine for
  `RicciFlow/main.tex`. It presents actual proved synthetic work and explicitly
  marks when a theorem is only a wrapper around an interface.
- P4 does not consume `blackbox.lean`. The quotient and algebraic pinching
  work stays in `Evolution/` + `DimensionThree/`; only the Section 12 limit
  handoff uses the global compactness interfaces.

## Current Status

### Tensor Calculus And Evolution

Status: real synthetic proof work exists.

Done:

- The invariant Ricci-flow connection variation is proved in
  `Evolution/Connection.lean` as `connection_evolution`.
- `wordlyLatex.lean` exposes this as
  `wordly_latex_lem_evol_christoffel_symbols`, the invariant form of
  the Christoffel-symbol evolution equation.
- Coordinate-facing Christoffel wrappers exist in
  `Realization/Coordinates/Christoffel.lean`.
- `Evolution/RicciNorm.lean` contains the assembled trace-free Ricci norm
  interfaces and proved component identities, including the P4 trace-free heat
  input `hamilton3D_tracefree_norm_eq_of_heat_components`.

Still realization-sensitive:

- Generic scalar product/chain/power rules should eventually be proved from a
  concrete `dt`, `grad`, `divergence`, and `laplacian = div grad` layer.
- The positive scalar power API for `R^(2 - epsilon)` is still an explicit
  realization interface.

### P1: Contracted Second Bianchi

Status: closed at the synthetic wrapper boundary.

Use:

- `HamiltonP1ContractedSecondBianchiTheorem`
- `HamiltonP1NamedCalculusInputs`
- `hamiltonP1ContractedSecondBianchiTheorem_of_named_calculus`

Do not restart P1. If cleanup is needed, keep it inside
`CurvatureAlgebra.lean`, `MetricTraceFubini.lean`, or
`HamiltonThreeManifold.lean`.

### P2: 3D Riemann From Ricci

Status: packaged, with real finite-dimensional slice producers.

Use:

- `HamiltonP2RiemannFromRicci3DTheorem`
- `hamiltonP2RiemannFromRicci3DTheorem_of_trace_eigenframe_packages`
- `hamiltonP2RiemannFromRicci3DTheorem_of_real_trace_inner_product`
- `RiemannFromRicci3DTraceEigenframePackage`

The trace/eigenframe package is the preferred route; finite-frame and
real-trace constructors remain supported realization bridges. Remaining work
is realization wiring, not new synthetic 3D algebra.

### P3: Cubic Reaction And Trace-Free Ricci Norm

Status: cubic-reaction geometry is closed at the synthetic/eigenframe boundary,
and the trace-free heat input exists for P4.

Use:

- `HamiltonP3CubicReactionGeometryTheorem`
  lives in `HamiltonThreeManifold.lean`.
- `hamiltonP3CubicReactionGeometryTheorem_of_trace_eigenframe_packages`
  lives in `HamiltonThreeManifold.lean`.
- `hamiltonP3CubicReactionGeometryTheorem_of_eigenvalue_packages`
  lives in `HamiltonThreeManifold.lean`.
- `hamilton3D_tracefree_norm_eq_of_heat_components`
  lives in `Evolution/RicciNorm.lean`; this is the P4-A trace-free norm input.

Do not redo the cubic eigenvalue contraction.

### P4: Improved Pinching

Status: producer-level synthetic closeout is in repo.

Closed pieces:

- P4-A quotient evolution entry:
  `hamiltonPinchingAdjustedEvolutionData_of_tracefree_ricci_norm_heat`
  (`DimensionThree/ImprovedPinching.lean`).
- One-stop P4 producer:
  `hamilton_improved_pinching_producer_data_of_tracefree_ricci_norm_heat`
  (`DimensionThree/ImprovedPinching.lean`).
- Domain-wise Q lower-bound helper:
  `cubicQ_lower_bound_on_domain_of_ordered_nonnegative_eigenvalue_realizations`
  (`DimensionThree/Pinching.lean`).
- Improved-pinching consumer:
  `improved_ricci_pinching_ratio_bound_from_hamilton_producer`
  (`DimensionThree/ImprovedPinching.lean`).
- Section 12 limit consumer:
  `limit_tracefree_norm_zero_from_hamilton_improved_pinching_producer`
  (`Global/Compactness.lean`).
- Presentation wrappers:
  `wordly_latex_cor_improved_ricci_pinching` and
  `wordly_latex_cor_limit_tracefree_norm_zero_from_p4`
  (`wordlyLatex.lean`).
- Section 12 P4 handoff:
  `section12_limit_tracefree_norm_zero_from_p4` and
  `section12_limit_tracefree_norm_zero_from_p4_builder_field`
  (`HamiltonThreeManifold.lean`).

Remaining explicit inputs to instantiate in a concrete geometric setting:

- scalar positivity and denominator nonzero;
- coefficient identities for the selected power convention at
  `beta = 2 - epsilon`;
- gradient-square completion for the `P` quotient;
- shifted adjusted heat equality for the chosen parabolic problem;
- initial bound, reaction nonnegativity, ratio-decay relation, and decay
  nonnegativity;
- preserved pinching/eigenvalue hypotheses feeding the domain-wise `Q` lower
  bound.

## P4 Delivery Status

The P4 producer now reaches the Section 12 builder boundary.

Keep compatibility:

- Do not rename or remove the existing
  `HamiltonSection12ClaimBuilderInput.limit_tracefree_norm_zero_from_p3` field
  in this pass.
- Use `section12_limit_tracefree_norm_zero_from_p4_builder_field` when a
  realization wants to fill that compatibility field from P4 data instead of
  the old direct P3 route.

Remaining checklist for a concrete realization:

- [have] P4 producer data:
  `HamiltonImprovedPinchingProducerData`.
- [have] P4 limit-zero theorem:
  `limit_tracefree_norm_zero_from_hamilton_improved_pinching_producer`.
- [have] Section 12 builder-field adapter:
  `section12_limit_tracefree_norm_zero_from_p4_builder_field`.
- [need] sequence identification:
  `conclusion.tracefree_ratio.seq = D.ratio`.
- [need] eventual domain membership:
  `eventually (fun i => D.problem.domain i)`.
- [need] decay upper convergence:
  `scalarConvergesTo (fun i => D.C * D.decay i) 0`.
- [need] eventual nonnegativity of the trace-free ratio.

## Next Milestone: Positive-Power Scalar Calculus

The serious remaining P4 proof work is now the realization-level positive
scalar power package for `R^(2 - epsilon)`.

Concrete targets:

- A positive-power API over the chosen scalar field, probably a `Real`/`rpow`
  realization first.
- Product, gradient, Laplacian, and heat rules specialized enough to discharge
  the coefficient identities used by
  `hamiltonPinchingAdjustedEvolutionData_of_tracefree_ricci_norm_heat`.
- A named gradient-square completion lemma for Hamilton's `P` quotient.
- A denominator-nonzero lemma from scalar positivity.
- A ratio-decay realization showing
  `|Ric^0|^2 / R^2 <= P * decay`.

This work may introduce theorem-shaped black boxes only for precise
realization-level analytic/power facts in `blackbox.lean`. It should not add
`sorry` or `admit` in `DimensionThree/` or `Evolution/`.

## What Not To Do Next

- Do not redo P1, P2, P3, or the P4 producer algebra unless a build exposes a
  concrete regression.
- Do not try to prove short-time existence, Hamilton compactness, Perelman
  noncollapsing, or Myers compactness in this synthetic branch.
- Do not introduce `sorry` or `admit` in `DimensionThree/` or `Evolution/`.
- If a theorem-shaped `sorry` is needed for a concrete analytic/global fact,
  put it in `blackbox.lean` with a precise mathematical statement and a
  docstring explaining why it is outside the synthetic layer.
- Do not broaden to a full `lake build` by default. Use narrow file or module
  checks.
- Do not hide missing analytic/geometric steps behind name-only assumptions
  when the synthetic quantity already exists. Prefer typed producer structures.

## Focused Checks

Use these narrow work-site checks for the next pass:

```powershell
lake env lean DifferentialGeometry\Synthetic\Flow\RicciFlow\HamiltonThreeManifold.lean
lake env lean DifferentialGeometry\Synthetic\Flow\RicciFlow\wordlyLatex.lean

lake build DifferentialGeometry.Synthetic.Flow.RicciFlow.HamiltonThreeManifold
lake build DifferentialGeometry.Synthetic.Flow.RicciFlow.wordlyLatex
```

If touching P4 dependencies, also check:

```powershell
lake env lean DifferentialGeometry\Synthetic\Flow\RicciFlow\Evolution\RicciNorm.lean
lake env lean DifferentialGeometry\Synthetic\Flow\RicciFlow\DimensionThree\Pinching.lean
lake env lean DifferentialGeometry\Synthetic\Flow\RicciFlow\DimensionThree\ImprovedPinching.lean
lake build DifferentialGeometry.Synthetic.Flow.RicciFlow.DimensionThree.ImprovedPinching
```

If an import fails because a direct `.olean` is stale, rebuild the direct
dependency only. Do not clean or kill unrelated Lean/lake processes.
