# RicciFlow Formalization Plan

This is the current working map for the synthetic Ricci-flow branch. It is not
a history log. Keep this file short enough that it can be read before a coding
session.

## Scope

This branch owns the synthetic tensor, curvature-algebra, evolution, pinching,
and Section 12 wrapper layer for `RicciFlow/main.tex`.

The collaborator owns the concrete analysis/PDE/integration/CGH realization:
short-time existence, maximal intervals, extension criteria, maximum
principles, point selection, compactness, noncollapsing, and Myers-type inputs.
Do not import `DifferentialGeometry/Analysis`, `DifferentialGeometry/Integral`,
or `DifferentialGeometry/PDE` into the synthetic Ricci-flow files.

When a proof needs a tensor calculation, first look for the reusable statement
that belongs in `Synthetic/Algebra/TensorAlgebra.lean`,
`Synthetic/Algebra/MetricTrace.lean`, or
`Synthetic/Geometry/CurvatureContractions.lean`. Avoid one-off local
coordinate proofs unless the calculation is genuinely realization-specific.

## Current File Map

Core Ricci-flow files:

- `Basic.lean`: `RicciFlowData`, time-dependent metric/connection/Ricci data.
- `Geometric.lean`: `GeometricRicciFlowData`, the manifold-aware wrapper over
  `RicciFlowData` with point/time domains, metric realization, pointwise scalar
  evaluation, and global curvature/pinching accessors.
- `Evolution/Connection.lean`: Palatini and Ricci-flow connection variation.
- `Evolution/RicciCore.lean`: public Ricci evolution interfaces and the
  pointwise/tensor-level named equations.
- `Evolution/RicciTrace.lean`: Ricci-slot traces, Riemann-to-Ricci trace
  algebra, and the `Rm*Ric`/`Ric^2` reaction tensors.
- `Evolution/RicciTraceCoordinate.lean`: finite-basis representatives and the
  trace/time-derivative commutation bridge.
- `Evolution/RicciFromRiemann.lean`: constructors deriving explicit Ricci
  evolution from Riemann evolution plus trace reductions.
- `Evolution/Ricci.lean`: compatibility facade importing the split Ricci
  evolution modules. New code should import the narrow module it needs.
- `Evolution/Lichnerowicz.lean`: Lichnerowicz-form interfaces.
- `Evolution/ScalarCurvature.lean`: scalar evolution interfaces and `(0,2)`
  tensor inner-product algebra.
- `Evolution/RicciNorm.lean`: trace-free Ricci norm algebra and evolution
  assembly interfaces.
- `DimensionThree/CurvatureAlgebra.lean`: contracted Bianchi, trace/divergence
  calculus, Einstein-to-constant-curvature, and 3D algebraic support.
- `DimensionThree/RiemannFromRicci3D.lean`: P2, the 3D Riemann-from-Ricci
  package and eigenframe/trace route.
- `DimensionThree/RicciReaction.lean`: P3, the 3D Ricci reaction contraction
  package.
- `DimensionThree/Pinching.lean`: Hamilton cubic `Q`, ordered eigenvalue
  algebra, and quotient algebra.
- `DimensionThree/ImprovedPinching.lean`: P4 producer and scalar WMP consumer
  for improved pinching.
- `Global/BlowUp.lean`, `Global/Compactness.lean`: typed global interfaces.
  New geometric interfaces consume `GeometricRicciFlowData`; legacy bare-core
  interfaces remain temporarily for compatibility.
- `HamiltonThreeManifold.lean`: Section 12 assembly and final theorem wrapper,
  plus the geometric-flow final wrapper that uses the manifold stored in
  `GeometricRicciFlowData`.

Realization support:

- `Synthetic/Realization/Coordinates/Christoffel.lean`: frame and raw-coordinate
  Christoffel symbols, including Lemma 14.23 coordinate wrappers.
- `Synthetic/Realization/MetricTraceFubini.lean`: concrete standard-trace
  Fubini, metric-adjoint trace invariance, and concrete P1 named calculus.
- `Synthetic/Realization/NablaTrComm.lean`: concrete trace-commutation for
  `concreteConn` and `concreteAbstractTrace`.
- `Synthetic/Realization/LeviCivita.lean`: realization-facing Levi-Civita
  bridge, including the explicit-metric bridge
  `concreteLeviCivita_of_metricCompatible_torsionFree` and the ForMathlib
  product-rule bridge
  `concreteLeviCivita_of_forMathlib_metricCompatible_torsionFree`.
- `Synthetic/Realization/TensorContract.lean`: concrete `AbstractTrace`
  assembly; `concreteAbstractTrace_tr_apply` states that trace is the fiberwise
  `LinearMap.trace` of the bundle endomorphism represented by a section
  endomorphism.
- `Synthetic/Realization/OrthonormalTrace.lean`: concrete target for the
  3-dimensional orthonormal-basis trace formula.

Temporary ForMathlib support should stay minimal and only cover APIs missing
from pinned mathlib or written locally.

## Status

### Christoffel / Lemma 14.23

Status: usable.

- Christoffel symbols are frame coefficients of `(nabla_{e_i} e_j)(x)`.
- Lower-index Christoffel symbols are metric-paired frame coefficients.
- The Ricci-flow connection variation is proved invariantly in
  `Evolution/Connection.lean`.
- Raw coordinate wrappers exist in
  `Realization/Coordinates/Christoffel.lean`.

Do not block the core proof on more coordinate work. Add local-coordinate
lemmas only when a downstream realization needs them.

### P1: Contracted Second Bianchi

Status: closed at the synthetic wrapper boundary.

Main public targets:

- `ContractedSecondBianchiIdentity`
- `contractedSecondBianchiIdentity_from_second_bianchi_named_patterns`
- `HamiltonP1ContractedSecondBianchiTheorem`
- `HamiltonP1NamedCalculusInputs`
- `hamiltonP1ContractedSecondBianchiTheorem_of_named_calculus`

Current sign convention for the lowered `(0,5)` tensor
`T(A, X, Y, Z, W) = (nabla_A Rm)(X, Y, Z, W)`:

- `divPattern + divFubiniPattern + gradPattern = 0`
- `divPattern = - div Ric`
- `divFubiniPattern = - div Ric`
- `gradPattern = dR`
- therefore `2 * div Ric = dR`.

The P1 implementation now has three layers:

1. Tensor layer in `CurvatureAlgebra.lean`:
   `HasContractedSecondBianchiNamedPatternCalculus` packages the cyclic
   slot-audit, divergence identification, and scalar-gradient identification.
2. Concrete trace layer in `MetricTraceFubini.lean`:
   `concreteHasContractedSecondBianchiNamedPatternCalculus` and
   `concreteContractedSecondBianchiIdentity` discharge the standard-trace
   realization using raw finite sums.
3. Hamilton layer in `HamiltonThreeManifold.lean`:
   `HamiltonP1NamedCalculusInputs` feeds the final wrapper without requiring a
   fake global P1 instance.

Do not recreate standalone P1 files. If P1 needs more cleanup, refactor inside
`CurvatureAlgebra.lean`, `MetricTraceFubini.lean`, or
`HamiltonThreeManifold.lean`.

### P2: 3D Riemann From Ricci

Status: packaged, with a real finite-dimensional slice producer and a
Hamilton-level wrapper. Full manifold/CGH realization is still collaborator
territory.

Main public targets:

- `HasRiemannFromRicci3DCalculus`
- `RiemannFromRicci3DTraceEigenframePackage`
- `RiemannFromRicci3DFinThreeComponentPackage`
- `HamiltonP2RiemannFromRicci3DTheorem`
- `hamiltonP2RiemannFromRicci3DTheorem_of_trace_eigenframe_packages`
- `hamiltonP2RiemannFromRicci3DTheorem_of_real_trace_inner_product`

What is done:

- The convention is fixed as `RcEndo X Z = tr (Y |-> Rm X Y Z)`.
- The RHS tensor and symmetry algebra for the 3D formula are available.
- `RicciDiagonalization3D` records the pointwise Ricci eigenframe package.
- Over real finite-dimensional inner-product spaces, the spectral-theorem
  route is available through
  `ricciDiagonalization3D_of_real_inner_product_and_Rc_symm`.
- The sectional-curvature equations are solved from diagonal Ricci trace
  equations.
- Off-diagonal Ricci trace equations are produced from the orthonormal trace
  formula by `ricciOffDiagonalTraceFormula3D_of_orthonormal_trace3`; mixed
  curvature vanishings are then derived from diagonal Ricci.
- `riemannFromRicci3DTraceEigenframePackage_of_diagonalization` builds the P2
  trace/eigenframe package from a Ricci diagonalization.
- `riemannFromRicci3DTraceEigenframePackage_of_real_inner_product` builds the
  same package in the real finite-dimensional inner-product setting from
  metric-adjoint trace invariance, `met.g = inner`, and the spectral theorem.
- `realTrace_hasOrthonormalBasisTraceFormula3` and
  `realTrace_hasMetricAdjointTraceInvariant` discharge the two trace bridges
  from `atr.tr = LinearMap.trace` and `met.g = inner`.
- `riemannFromRicci3DTraceEigenframePackage_of_real_trace_inner_product`
  builds the per-slice trace/eigenframe package directly from the standard
  finite-dimensional real trace.
- The trace/eigenframe package lowers to the six-component package, then to
  `HasRiemannFromRicci3DCalculus`, then to the Hamilton-level P2 theorem.
- `hamiltonP2RiemannFromRicci3DTheorem_of_real_trace_inner_product` lifts the
  real finite-dimensional per-slice producer to the final Hamilton P2
  typeclass. It stores the canonical coefficient `(2 : ℝ)⁻¹`; the public P2
  theorem still accepts any `half` with `IsHalfCoefficient half`.
- `Realization/OrthonormalTrace.lean` proves
  `concreteOrthonormalBasisTraceFormula3`: evaluating a global orthonormal
  `C∞(M)` section basis gives a pointwise fiber basis, and
  `concreteAbstractTrace.tr` is the fiberwise trace sum of diagonal metric
  pairings. The theorem `concreteHasOrthonormalBasisTraceFormula3` now provides
  the concrete `HasOrthonormalBasisTraceFormula3` instance without an extra
  hypothesis.

What remains:

- Thread the real inner-product producer through the tangent realization. In
  this project `V` should always be read as the tangent module supplied by the
  realization; the finite-dimensional theorem is the pointwise tangent-fiber
  algebra that must be bridged back to that module-level tensor identity.
- For the tangent-section realization, combine
  `concreteHasOrthonormalBasisTraceFormula3`,
  `concreteHasMetricAdjointTraceInvariant`, and the concrete Levi-Civita
  metric/torsion package into the existing trace/eigenframe Hamilton wrapper.
- Complex/Hermitian spectral variants are low priority and should stay in the
  TODO list until the real 3D route is wired.

### P3: Cubic Reaction Geometry And Trace-Free Ricci Norm Evolution

Status: the P3.3 cubic-reaction geometry is closed at the
synthetic/eigenframe wrapper boundary. The full trace-free Ricci norm
evolution still needs the Ricci-norm and scalar heat components supplied to
`Evolution/RicciNorm.lean`.

Main public targets:

- `HasRicciReactionContractionCalculus`
- `RicciReactionEigenvaluePackage`
- `HamiltonP3CubicReactionGeometryTheorem`
- `HamiltonP3ReactionCalculusInputs`
- `hamiltonP3CubicReactionGeometryTheorem_of_reaction_calculus`
- `hamilton3D_tracefree_norm_eq_of_cubic_reaction_components`

The current P3 reaction identity is:

```text
2 * R * reaction = 2 * |Ric|^4 - Q
```

where `reaction` is the geometric `Rm * Ric * Ric` contraction and `Q` is
Hamilton's cubic quantity.

What is done:

- `RicciReaction.lean` defines the residual
  `ricciReactionContractionResidual`.
- The eigenvalue algebra is packaged by `RicciReactionEigenvaluePackage`.
- `ricciEigenframeRiemannReaction3D` is the canonical eigenframe reaction
  scalar attached to a P2 Ricci eigenframe.
- `ricciEigenframeRiemannReaction3D_eq_ricciEigenRiemannReaction3_of_sectional_trace`
  identifies that finite-frame scalar with Hamilton's three-eigenvalue
  reaction expression.
- `ricciReactionEigenvalueRealization_of_trace_eigenframe_package` builds the
  P3 eigenvalue realization from the same trace/eigenframe package used for
  P2.
- `hasRicciReactionContractionCalculus_of_trace_eigenframe_package` turns a P2
  trace/eigenframe package into the slice-level P3 calculus.
- `hamiltonP3CubicReactionGeometryTheorem_of_trace_eigenframe_packages` and
  `hamiltonP3CubicReactionGeometryTheorem_of_eigenvalue_packages` turn the
  slice-level calculus into `HamiltonP3CubicReactionGeometryTheorem`.
- `Evolution/RicciNorm.lean` has the component assembly lemmas for the
  trace-free norm evolution once the Ricci norm, scalar evolution, Laplacian,
  and cubic-reaction inputs are supplied.

Caller-facing caveat:

- The default P3 theorem uses a parameterized predicate
  `IsGeometricReactionData`. For the checked eigenframe route this predicate
  says that the chosen `reaction` is the canonical finite-frame scalar
  `ricciEigenframeRiemannReaction3D ... pkg.diagonalization`.
- If a caller chooses a different concrete reaction scalar, the remaining
  cubic-reaction obligation is the equality between that scalar and the
  canonical eigenframe contraction.
- For the full trace-free Ricci norm evolution, callers still have to provide
  the Ricci norm heat input
  `h_ricciNorm_heat : ricciNormDt - ricciNormLap =
    -2 * |nabla Ric|^2 + 4 * reaction`, the scalar heat input
  `h_scalar_heat : scalarDt - scalarLap = 2 * |Ric|^2`, and the binding
  between the `reaction` used there and the canonical eigenframe reaction
  supplied by the P3.3 theorem.
- No pure synthetic cubic-reaction tensor calculation remains. P4 should now
  proceed only after those heat-component inputs are wired into
  `hamilton3D_tracefree_norm_eq_of_cubic_reaction_components`.

### P4: Improved Pinching

Status: quotient-evolution handoff and maximum-principle producer are in
place. P4 now waits on the full trace-free norm evolution, the concrete
quotient evolution/gradient-square completion, and collaborator-owned analytic
inputs. It is no longer blocked by the P3.3 cubic-reaction geometry.

Main public targets:

- `ImprovedRicciPinchingEstimateAlongFlow`
- `hamiltonImprovedPinchingQuantity`
- `quotientEvolutionRHS`
- `QuotientEvolutionIdentity`
- `hamiltonPinchingEvolutionRHS`
- `HamiltonPinchingEvolutionEquation`
- `HamiltonPinchingQuotientEvolutionData`
- `HamiltonPinchingAdjustedEvolutionData`
- `HamiltonImprovedPinchingProducerData`
- `hamilton_improved_pinching_producer_data_of_quotient_evolution`
- `hamilton_improved_pinching_producer_data_of_adjusted_pinching_evolution`
- `hamiltonPinchingEvolutionEquation_of_quotient_identity`
- `hamiltonPinchingAdjustedEvolutionData_of_quotient_identity`
- `improved_ricci_pinching_estimate_along_flow_of_hamilton_producer`
- `limit_tracefree_norm_zero_from_hamilton_improved_pinching_producer`

Section 10 mapping:

- Definition 10.2 is `hamiltonImprovedPinchingQuantity`; the denominator
  `R^(2 - epsilon)` is abstract.
- Lemma 10.5 is `quotientEvolutionRHS` plus the predicate
  `QuotientEvolutionIdentity`; the power coefficients are abstract.
- Lemma 10.6 is `hamiltonPinchingEvolutionRHS` plus the predicate
  `HamiltonPinchingEvolutionEquation`; drift, completed-square, scalar-gradient,
  and reaction weights are abstract. `HamiltonPinchingAdjustedEvolutionData`
  records the move from the bare Lemma 10.6 operator to the drift-adjusted
  operator used by the scalar weak maximum principle.
- The direct calculation from Lemma 10.5 plus Lemma 10.4 is
  `hamiltonPinchingEvolutionEquation_of_quotient_identity`; the packaged
  constructor is `hamiltonPinchingAdjustedEvolutionData_of_quotient_identity`.
  These keep the remaining exponent/coefficient identities and the
  gradient-square completion explicit.

What remains:

- concrete quotient evolution for `P = |Ric^0|^2 / R^(2-epsilon)`, packaged as
  `HamiltonPinchingAdjustedEvolutionData`;
- scalar positivity and denominator side conditions;
- coefficient identities for the selected positive-power API:
  `2 * phiHeatCoeff = reactionWeight * R` and
  `2 * psiHeatCoeff = reactionWeight * |Ric^0|^2`;
- the gradient-square completion identity needed by
  `hamiltonPinchingAdjustedEvolutionData_of_quotient_identity`;
- strict positive Ricci gives a uniform pinching cone;
- analytic WMP instantiation, left to the collaborator unless it is already
  available as a small interface.

### Section 12 Final Wrapper

Status: wrapper shape is correct, with a new manifold-aware entry point.

Main public targets:

- `HamiltonSection12Claims`
- `hamilton_section12_assembly_from_claims`
- `hamilton_three_manifold_exists_constant_positive_metric`
- `hamilton_three_manifold_from_section12_claims`
- `hamilton_three_manifold_from_typed_input`
- `hamilton_three_manifold_from_typed_input_with_p1_named_calculus`
- `HamiltonThreeManifoldFlowContext`
- `HamiltonThreeManifoldGeometricFlowInput`
- `hamilton_three_manifold_exists_constant_positive_metric_geometric_flow`

The final theorem target is the right one: the initial manifold admits a metric
with constant positive sectional curvature.

The Section 12 wrapper should remain stable. Future work should discharge
claim fields by adding producers, not by changing the final theorem statement.
P1 is fed through named calculus. P3 can be fed through the eigenvalue-package
route. P2 remains explicit unless the caller uses one of the real trace or
trace/eigenframe package wrappers.

Global realization should now target the geometric layer:

- local tensor/evolution/P1-P4 theorems continue consuming `flow.core`;
- singularity, blow-up, point selection, rescaling, compactness, and
  diffeomorphism interfaces should consume `GeometricRicciFlowData`;
- the old `HamiltonThreeManifoldGeometricContext.manifoldOfFlow` path is
  compatibility-only. New final wrappers use `input.flow.manifold`.

## Out Of Scope For This Branch

Leave these as typed interfaces for the collaborator:

- short-time existence and maximal interval construction;
- finite-time singularity from positive scalar curvature;
- extension criterion and curvature blow-up;
- scalar blow-up to point-selection hypotheses;
- point selection and parabolic rescaling;
- Hamilton-Cheeger-Gromov compactness;
- Perelman noncollapsing;
- Myers compactness;
- concrete scalar/tensor maximum principles;
- integration, Sobolev, and PDE estimates.

Interface precision is still welcome. Replace name-only `Prop` fields with
concrete predicates when the synthetic quantity already exists, but do not
start proving the analytic theorems here.

## Next Session Checklist

Highest leverage path after P1-P2 and P3.3:

1. Start P4 from `Evolution/RicciNorm.lean` and
   `DimensionThree/ImprovedPinching.lean`.
2. Instantiate the quotient evolution for
   `P = |Ric^0|^2 / R^(2 - epsilon)`.
3. Prove the denominator/positivity side conditions and gradient-square
   completion needed by Hamilton's improved pinching estimate.
4. Use the existing Lemma 10.8 lower bound on `Q`.
5. Keep analytic weak maximum-principle inputs as collaborator-owned
   interfaces unless a small existing interface already suffices.

Do not spend more time on P1, P2, or the P3.3 cubic-reaction geometry unless a
build or downstream theorem exposes a real regression.

## Focused Checks

Use narrow checks. Avoid umbrella builds unless imports changed broadly.

```text
./scripts/lake-locked.ps1 -Files @(
  'DifferentialGeometry/Synthetic/Flow/RicciFlow/Geometric.lean',
  'DifferentialGeometry/Synthetic/Flow/RicciFlow/Global/BlowUp.lean',
  'DifferentialGeometry/Synthetic/Flow/RicciFlow/Global/Compactness.lean',
  'DifferentialGeometry/Synthetic/Flow/RicciFlow/DimensionThree/CurvatureAlgebra.lean',
  'DifferentialGeometry/Synthetic/Realization/MetricTraceFubini.lean',
  'DifferentialGeometry/Synthetic/Flow/RicciFlow/DimensionThree/RiemannFromRicci3D.lean',
  'DifferentialGeometry/Synthetic/Realization/OrthonormalTrace.lean',
  'DifferentialGeometry/Synthetic/Flow/RicciFlow/DimensionThree/RicciReaction.lean',
  'DifferentialGeometry/Synthetic/Flow/RicciFlow/HamiltonThreeManifold.lean'
)
```
