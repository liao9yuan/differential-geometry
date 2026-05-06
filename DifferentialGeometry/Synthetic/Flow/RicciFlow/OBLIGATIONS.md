# Hamilton Three-Manifold Theorem Obligations

This file records what is still owed to close the Section 12 Hamilton
positive-Ricci theorem in the current synthetic branch.

It is not a history log. Older P1/P2/P3/P4 attack plans were removed after the
producer-level refactors. For design context, see `FORMALIZATION_PLAN.md`; for
the import inventory, see `SECTION12_DEPENDENCY_AUDIT.md`.

## Top-Level Target

The main synthetic theorem is:

```lean
hamilton_three_manifold_from_typed_input
    [HamiltonSyntheticAnalyticInputs]
    [HamiltonP1ContractedSecondBianchiTheorem]
    [HamiltonP2RiemannFromRicci3DTheorem]
    [HamiltonP3CubicReactionGeometryTheorem]
    (hpos)
    (builder : HamiltonSection12ClaimBuilderInput)
    (input : HamiltonThreeManifoldTypedInput)
  : exists g, metricOn input.initialManifold g /\
      hasConstantPositiveSectionalCurvature input.initialManifold g
```

The Lean composition from these inputs to the final existential conclusion is
done. What remains is supplying the inputs from concrete realization and
analysis.

## Current State

### Closed In The Synthetic Layer

- P1 contracted second Bianchi is packaged by
  `HamiltonP1ContractedSecondBianchiTheorem` and produced from
  `HamiltonP1NamedCalculusInputs`.
- P2 3D Riemann-from-Ricci is packaged by
  `HamiltonP2RiemannFromRicci3DTheorem`, with trace/eigenframe and real-trace
  producers.
- P3 cubic reaction geometry is packaged by
  `HamiltonP3CubicReactionGeometryTheorem`, with eigenvalue and trace/eigenframe
  producers.
- The P4 quotient-evolution producer is packaged by
  `hamiltonPinchingAdjustedEvolutionData_of_tracefree_ricci_norm_heat`.
- The one-stop P4 producer is
  `hamilton_improved_pinching_producer_data_of_tracefree_ricci_norm_heat`.
- The domain-wise `Q` lower-bound helper is
  `cubicQ_lower_bound_on_domain_of_ordered_nonnegative_eigenvalue_realizations`.
- The P4 limit-zero consumer is
  `limit_tracefree_norm_zero_from_hamilton_improved_pinching_producer`.
- The Section 12 P4 compatibility handoff is
  `section12_limit_tracefree_norm_zero_from_p4_builder_field`, which fills the
  existing builder field `limit_tracefree_norm_zero_from_p3` from P4 producer
  data.

Do not reopen these unless a concrete build failure exposes a regression.

### Not Closed By Design

The global analytic theorems remain black boxes or collaborator-owned
interfaces. They are listed below for completeness, but they are not synthetic
proof obligations for this branch.

## A. Analytic And Global Black Boxes

These are represented by `HamiltonSyntheticAnalyticInputs`, inherited global
interfaces, or maximum-principle classes.

- `PositiveScalarFiniteTimeTheorem`: positive scalar curvature gives finite
  maximal time.
- `MaximalTimeWitness`: extracts the terminal maximal time.
- `CurvatureBlowUpAlternative`: finite maximal endpoint forces curvature
  blow-up.
- `ScalarBlowUpFromCurvatureBlowUp`: in the positive-Ricci 3D setting,
  curvature blow-up gives scalar blow-up.
- `PointSelectionAndRescalingTheorem`: Hamilton point selection and parabolic
  rescaling.
- `ScalarSpatialPromotionFromTime`: promotes time-only scalar blow-up to the
  point-spacetime hypothesis used by point selection.
- `HamiltonCompactnessTheorem`: Hamilton-Cheeger-Gromov compactness.
- `CurvatureRatioConvergenceUnderSmoothCGH`: smooth CGH convergence transports
  the relevant curvature-ratio data.
- `ScalarWeakMaximumPrinciple`: used by the improved pinching estimate.
- `ScalarStrongMaximumPrinciple`: used for strict positivity of the limit
  scalar.
- `ScalarConvergenceSqueezeToZero` and `EventuallyImp`: convergence/eventuality
  interfaces used by the P4 limit-zero consumer.
- Myers compactness and compact-limit diffeomorphism interfaces in
  `Global/Compactness.lean`.

If a theorem-shaped `sorry` is needed for one of these, it belongs in
`blackbox.lean` with a precise mathematical statement. Do not put analytic
black boxes in `DimensionThree/` or `Evolution/`.

## B. Remaining Non-Blackbox Obligations

These are the current non-analytic obligations after the P4 handoff.

### B1. Positive-Power Scalar Calculus

This is the next main proof project.

Needed:

- choose and document the concrete positive-power convention, probably first
  over `Real` with `rpow`;
- prove denominator nonzero from scalar positivity;
- prove the coefficient identities used by
  `hamiltonPinchingAdjustedEvolutionData_of_tracefree_ricci_norm_heat` at
  `beta = 2 - epsilon`;
- prove product, gradient, Laplacian, and heat rules strong enough for
  `R^(2 - epsilon)`;
- prove the exponent/decay relation
  `R^(-epsilon) = R^(2 - epsilon) / R^2` in the chosen convention.

This can live in a realization/power API. The abstract P4 producer should not
be stubbed.

### B2. P4 Gradient-Square Completion And Adjusted Heat Equality

The producer keeps these as explicit inputs:

- gradient-square completion for
  `P = |Ric^0|^2 / R^(2 - epsilon)`;
- shifted adjusted heat equality for the parabolic problem used in the scalar
  maximum principle;
- reaction weight nonnegativity;
- initial bound for `P - C`.

The quotient-evolution skeleton is already packaged. The remaining work is the
concrete calculation in the selected scalar calculus.

### B3. P4 Algebraic Side Conditions In The Geometric Setting

The polynomial `Q` lower bound is proved, but a concrete flow realization still
has to provide the hypotheses at each relevant time:

- ordered nonnegative Ricci eigenvalue realization data;
- preserved pinching in the form `delta * R <= lambda_3`;
- `epsilon <= 2 * delta^2`;
- nonnegativity of `|Ric|^2 * |Ric^0|^2`;
- the identification of the concrete `ricciNormSq`, `tracefreeNormSq`, and
  `cubicQ` functions with the geometric quantities used by the domain-wise
  helper.

Use:

```lean
cubicQ_lower_bound_on_domain_of_ordered_nonnegative_eigenvalue_realizations
```

### B4. P4 Ratio-Decay And Limit-Zero Inputs

To use `section12_limit_tracefree_norm_zero_from_p4_builder_field`, a
realization must provide, for each Section 12 rescaling/CGH data package:

- a `HamiltonImprovedPinchingProducerData`;
- `sectionData.ratio.tracefree_ratio.seq = D.ratio`;
- eventual membership in `D.problem.domain`;
- convergence of `fun i => D.C * D.decay i` to `0`;
- eventual nonnegativity of `sectionData.ratio.tracefree_ratio.seq`;
- the squeeze and eventuality instances for the convergence profile.

This is where the rescaling decay estimate enters the Section 12 proof.

### B5. Limit Einstein-To-Space-Form Bridge

The builder field `constant_positive_from_p1_p2` still needs a concrete bridge:

```lean
ctx.metricOn ... ->
ricciFlowScalarCurvatureAt ... = 1 ->
ricciFlowTracefreeRicciNormSqAt ... = 0 ->
ctx.hasConstantPositiveSectionalCurvature ...
```

Available synthetic ingredients:

- P1 contracted Bianchi;
- P2 3D Riemann-from-Ricci;
- `einsteinRicciFormula_of_tracefree_ricci_tensor_eq_zero`;
- scalar-spatial-constant lemmas in `DimensionThree/CurvatureAlgebra.lean`;
- Einstein-to-constant-curvature algebra in
  `DimensionThree/CurvatureAlgebra.lean`.

Still owed:

- norm-definiteness or realization bridge from trace-free Ricci norm squared
  zero to trace-free Ricci tensor zero;
- metric/trace realization facts needed to apply the synthetic algebra to the
  CGH limit flow;
- final packaging into the builder field.

### B6. Builder Bookkeeping Fields

The final Section 12 composition expects the realization to fill:

- `limitScalarProblem`;
- `scalar_time_eq`;
- `scalar_sample_eq`;
- `scalar_constant_converges`;
- `scalar_convergence_unique`;
- `limit_dimensionThree_from_input`;
- `limitMetric`;
- `limit_metric_on`;
- `limit_compact_from_constant_positive`;
- `compact_limit_diffeomorphism` and `_matches`;
- `original_limit_diffeomorphism` and `_to_limit`.

Some of these are analytic/global, but they remain fields of
`HamiltonSection12ClaimBuilderInput` and must be supplied by the final
realization layer.

## C. Concrete Realization Obligations

These are not new synthetic theorem statements, but they are needed to turn the
current interfaces into an end-to-end concrete proof.

### C1. Tangent-Fiber To Synthetic-Module Bridge

P2/P3 have strong finite-dimensional and trace/eigenframe producers. The
remaining realization work is bridging pointwise tangent-fiber data into the
synthetic module used by `RicciFlowData`.

Useful entry points:

- `RiemannFromRicci3DTraceEigenframePackage`;
- `riemannFromRicci3DTraceEigenframePackage_of_real_trace_inner_product`;
- `hamiltonP2RiemannFromRicci3DTheorem_of_real_trace_inner_product`;
- `hasRicciReactionContractionCalculus_of_trace_eigenframe_package`;
- `hamiltonP3CubicReactionGeometryTheorem_of_trace_eigenframe_packages`.

### C2. Trace-Free Ricci Norm Heat Inputs

The P4-facing heat theorem exists:

```lean
hamilton3D_tracefree_norm_eq_of_heat_components
```

Concrete callers still need to provide or discharge the component hypotheses
used by the Ricci-norm/scalar heat wrappers, including:

- Ricci norm heat component;
- scalar heat component;
- reaction binding to the canonical eigenframe reaction scalar when the caller
  chooses a noncanonical reaction scalar;
- coordinate/Bochner component identities if using the coordinate variants in
  `Evolution/RicciNorm.lean`.

## D. Recommended Order

1. Prove the positive-power scalar calculus package for the chosen realization.
2. Use it to instantiate the P4 producer inputs:
   coefficient identities, denominator nonzero, gradient-square completion,
   adjusted heat equality, and ratio-decay.
3. Use preserved pinching/eigenvalue data to discharge the domain-wise `Q`
   lower-bound field.
4. Fill the Section 12 P4 builder-field route via
   `section12_limit_tracefree_norm_zero_from_p4_builder_field`.
5. Build the `constant_positive_from_p1_p2` bridge from trace-free Ricci zero
   and scalar normalization to constant positive sectional curvature.
6. Fill the remaining builder bookkeeping/global realization fields.

## E. What Not To Do

- Do not add `sorry` or `admit` in `DimensionThree/` or `Evolution/`.
- Do not move P1/P2/P3/P4 synthetic algebra into `blackbox.lean`.
- Do not rename `limit_tracefree_norm_zero_from_p3` in this pass; it is a
  compatibility field now fillable from P4.
- Do not restart P1/P2/P3/P4 producer algebra unless a checked regression
  appears.
- Do not run a full `lake build` by default in the shared workspace. Use narrow
  file/module checks.

## F. Narrow Checks

For P4 or Section 12 work:

```powershell
lake env lean DifferentialGeometry\Synthetic\Flow\RicciFlow\Evolution\RicciNorm.lean
lake env lean DifferentialGeometry\Synthetic\Flow\RicciFlow\DimensionThree\Pinching.lean
lake env lean DifferentialGeometry\Synthetic\Flow\RicciFlow\DimensionThree\ImprovedPinching.lean
lake env lean DifferentialGeometry\Synthetic\Flow\RicciFlow\HamiltonThreeManifold.lean
lake env lean DifferentialGeometry\Synthetic\Flow\RicciFlow\wordlyLatex.lean
```

Then, if needed:

```powershell
lake build DifferentialGeometry.Synthetic.Flow.RicciFlow.DimensionThree.ImprovedPinching
lake build DifferentialGeometry.Synthetic.Flow.RicciFlow.HamiltonThreeManifold
lake build DifferentialGeometry.Synthetic.Flow.RicciFlow.wordlyLatex
```

Invariant check:

```powershell
rg -n "sorry|admit" DifferentialGeometry\Synthetic\Flow\RicciFlow\DimensionThree DifferentialGeometry\Synthetic\Flow\RicciFlow\Evolution
```
