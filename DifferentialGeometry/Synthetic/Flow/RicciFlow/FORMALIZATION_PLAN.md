# RicciFlow formalization plan

This note compactly records how `RicciFlow/main.tex` maps into the current Lean
source tree. The project is already organized around a synthetic tensor
calculus, so the main implementation path should stay invariant and tensorial.
Local-coordinate calculations from the LaTeX are treated as proof blueprints or
as later realization lemmas, not as the core API.

## Current project shape

The Ricci flow source lives under
`DifferentialGeometry/Synthetic/Flow/RicciFlow/`. The existing core is:

- `Basic.lean`: Ricci flow data, Riemann tensor, Ricci form, Levi-Civita at each
  time.
- `Evolution/Connection.lean`: the Ricci-flow specialization of the Palatini
  connection variation. This is the Lean form of the first variation of
  Christoffel symbols.
- `Evolution/RiemannVariation.lean`, `RiemannLaplacian.lean`,
  `RiemannEvolution.lean`: variation and heat-type evolution of the Riemann
  tensor, including a Hamilton-style quadratic term.
- `Evolution/Ricci.lean`: contains pointwise extraction for time derivatives of
  Ricci and interface plumbing for the Lichnerowicz-form evolution RHS
  `rough Laplacian + curvature reaction`. The actual identification of `rough`
  with the rough Laplacian of Ricci and `reaction` with the curvature reaction
  is still a theorem target.
- `Evolution/ScalarCurvature.lean`: proves the partial scalar curvature formula
  `d_t R = 2 |Rc|^2 + tr_g(d_t Rc)`, exposes bilinearity/symmetry lemmas for
  the `(0,2)` tensor trace inner product, and has the closed scalar evolution
  theorem once a Ricci RHS trace identity is supplied. The RHS-trace interface
  is deliberately named `rhs_trace`; it becomes the scalar Laplacian only after
  an additional trace/Laplacian identification theorem.
- `Evolution/RicciNorm.lean`: defines trace-free Ricci, its norm, norm
  evolution interfaces, and compiled algebraic expansions of
  `|Rc - (R/n)g|^2`.
- `Calculus.lean`: bundles the common Ricci-flow hypotheses and exposes wrapper
  theorems, including bundled Lichnerowicz-form Ricci and closed scalar
  evolution wrappers.

Known gaps are proving the full Ricci evolution from contractions/commutators,
closing the scalar formula with the contracted Bianchi/trace identity, proving
Ricci norm and trace-free Ricci evolution rather than assuming interfaces,
three-dimensional curvature estimates, pinching estimates, global
blow-up/compactness inputs, and the final Hamilton theorem assembly. Short-time
existence is deliberately not an active near-term target.

## LaTeX-to-Lean roadmap

The first target from `main.tex` is the first variation of Christoffel symbols.
In Lean this should remain the invariant statement already developed through
Palatini:

- generic variation: `DifferentialGeometry/Synthetic/Operator/Variation.lean`;
- Ricci-flow specialization:
  `DifferentialGeometry/Synthetic/Flow/RicciFlow/Evolution/Connection.lean`.

The next tensor-evolution targets are:

- `Evolution/Ricci.lean`: full Ricci evolution as an equation interface, then as
  a theorem once the needed contraction and commutator identities are available.
- `Evolution/Lichnerowicz.lean`: named Lichnerowicz-laplacian interface for
  `(0,2)` tensors.
- `Evolution/ScalarCurvature.lean`: close
  `d_t R = Delta R + 2 |Rc|^2` from the trace identity for `d_t Rc`.
  Current wrappers reduce this to identifying the trace of the chosen Ricci
  evolution RHS with the actual scalar Laplacian.
- `Evolution/RicciNorm.lean`: Ricci norm, trace-free Ricci tensor, expansion
  identities, and evolution interfaces for pinching.

The three-dimensional and analytic layers should be separated:

- `DimensionThree/CurvatureAlgebra.lean`: three-dimensional curvature algebra,
  Riemann-from-Ricci formula, sectional/eigenvalue identities, and control of
  `Rm` by `Rc`.
- `DimensionThree/Pinching.lean`: positivity, pinching cones, Hamilton's
  pinching quantity, and cubic reaction terms.
- `DimensionThree/ImprovedPinching.lean`: the minimal maximum-principle
  consumer for improved pinching. It imports only `Pinching.lean` and the
  scalar maximum-principle interface; it does not import the larger
  Sobolev/De Giorgi analysis subtree.
- `Synthetic/Analysis/Parabolic/`: scalar and tensor maximum-principle
  interfaces.
- `Global/`: maximal interval, extension criterion, blow-up, noncollapsing,
  compactness, and Myers-type inputs. Short-time existence can remain a
  black-box placeholder until the evolution/pinching layers are mature.
- `HamiltonThreeManifold.lean`: final assembly target for Hamilton's positive
  Ricci theorem in dimension three.

## Coordinate strategy

Mathlib has useful infrastructure for coordinate work:

- charts and tangent coordinates: `extChartAt`, `chartAt`,
  `tangentCoordChange`, `mfderiv`;
- local frames and coefficients: `LocalFrame` and `localFrame_coeff`;
- tangent-bundle trivializations and coordinate changes;
- covariant derivative infrastructure, especially
  `CovariantDerivative.difference`.

Mathlib does not currently provide a ready-made Christoffel/Ricci/Levi-Civita
curvature API matching the coordinate formulas in `main.tex`. Because of this,
the synthetic proof path should not wait for normal coordinates. If raw
coordinates are needed later, place that bridge under
`DifferentialGeometry/Synthetic/Realization/Coordinates/`, define local
connection coefficients in a frame, and model normal coordinates at a point as a
local-frame normalization hypothesis until a stronger manifold-level theorem is
available.

Current status: `Synthetic/Realization/Coordinates/Christoffel.lean` defines a
minimal frame-based Christoffel API for a mathlib `CovariantDerivative`:
pointwise coefficients, the frame-expansion lemma, tensorial
connection-difference coefficients, and a vanishing-at-a-point predicate for
normal-coordinate arguments. It also names `partial_t Gamma^k_ij` in a fixed
frame, adds lower-index metric-paired coefficients
`Gamma_{ij l} = g(nabla_i e_j, e_l)`, and records both lower-index and raised
Ricci-flow Lemma 14.23 coordinate equations as interfaces whose Ricci-derivative
components will be supplied by the later metric/Ricci coordinate realization.
It also records the exact bridge obligation
`RicciCovDerivComponentsInFrame` and the theorem
`ricciFlowChristoffelLowerEvolution_from_invariant_components`: once the
coordinate components are identified with invariant Ricci covariant derivatives
and the metric-paired connection variation is identified with the lower
Christoffel time derivative, the coordinate lower-index equation follows. The
proved invariant anchor is `christoffel_evolution_metric_paired`, an alias of
`connection_evolution`, in `Evolution/Connection.lean`.
The file now also has raw-coordinate accessors built from Mathlib's tangent
trivialization at a base point `x0` and the standard model basis
`Module.finBasis Real E`: `rawCoordinateFrame`, `rawCoordinateDomain`,
`christoffelSymbolInRawCoordinates`,
`christoffelSymbolLowerInRawCoordinates`,
`christoffelSymbolLowerTimeDerivativeInRawCoordinates`, and
`ricciCovDerivComponentsInRawCoordinates`. The theorem
`ricciFlowChristoffelLowerEvolution_in_raw_coordinates` removes the old
free `nablaRic` component placeholder in the raw-coordinate setting by using
the actual coordinate-frame components of the invariant Ricci covariant
derivative. The remaining inputs are the invariant connection-variation/time
derivative bridge and the invariant Ricci-flow connection evolution, normally
supplied from `christoffel_evolution_metric_paired` after realization.
General trivialization users can still pass `e.localFrame b` and
`e.isLocalFrameOn_localFrame_baseSet I 1 b` to the frame API.

Recent completed infrastructure:

- `DimensionThree/CurvatureAlgebra.lean` now names the 3D
  Riemann-from-Ricci RHS formula with a supplied `half`, and the formula
  predicate `RiemannFromRicci3DFormula` carries the constraint `2 * half = 1`.
  The raw RHS helper also requires this proof, so callers cannot use an
  incoherent coefficient such as `0`.
  The dimension-three marker is now `abstractTraceDimension atr = 3`, with a
  normalization lemma turning `nInv * 3 = 1` into
  `nInv * abstractTraceDimension atr = 1`.
- `DimensionThree/Pinching.lean` now defines Hamilton's pinching quotient
  `|Rc°|^2 / R^2` directly from the trace-free Ricci norm and scalar curvature.
- Pinching also proves the algebraic rewrite of Hamilton's quotient to
  `|Rc|^2 / R^2 - nInv` under the trace-dimension normalization and nonzero
  scalar curvature.
- Lemma 10.8 (`lem:Q-lower-bound`) is formalized at the ordered-eigenvalue
  algebra level: `hamiltonCubicQ3_lower_bound_ordered_eigenvalues` proves
  `Q >= 2 * delta^2 * |Ric|^2 * |Ric°|^2` from ordered Ricci eigenvalues,
  `delta R <= lambda_3`, nonnegative scalar, and `|Ric|^2 <= R^2`.
  The stronger wrapper
  `hamiltonCubicQ3_lower_bound_ordered_nonnegative_eigenvalues` derives
  `|Ric|^2 <= R^2` from nonnegative Ricci eigenvalues.
  `Evolution/ScalarCurvature.lean` now defines the synthetic cubic trace
  `tensor_trace_cube_02` and Ricci specialization `ricci_trace_cube`.
  `DimensionThree/Pinching.lean` defines the synthetic cubic reaction
  `hamiltonCubicQ` and the bridge structure
  `HamiltonCubicQEigenvalueRealization`, making the exact diagonal-frame
  obligations explicit: scalar curvature, `|Ric|^2`, `tr(Ric^3)`, and
  `|Ric°|^2` must match the three eigenvalue expressions. The remaining
  geometric bridge is to derive those identities and the ordered/nonnegative
  eigenvalue hypotheses from `Ric >= delta R g` in an orthonormal frame.
  This is currently a per-tangent-space bridge. Hamilton's flow argument also
  needs a family bridge with eigenvalue functions over spacetime, including the
  analytic/geometric handling of repeated eigenvalues where a smooth eigenframe
  need not be globally available.
  Future algebra note: `tensor_trace_cube_02` deliberately has only the
  definition and Ricci specialization for now. Add add/smul/trilinear expansion
  lemmas only when a later proof needs to expand `tr((Ric° + (R/3)g)^3)`.
- `Evolution/RicciNorm.lean` includes
  `tracefree_ricci_norm_sq_expand_closed`, which shows the classical
  `|Rc°|^2 = |Rc|^2 - (1/n)R^2` shape once the remaining contraction bridge
  facts `<Rc,g> = R`, `<g,g> = n`, and `(1/n) * n = 1` are supplied.

The `<Rc,g> = R` and `<g,g> = tr(id)` contractions are now proved, so
`tracefree_ricci_norm_sq_expand_abstractTraceDimension` only needs the
normalization `(1/n) * tr(id) = 1`.

Owed realization bridge: for the concrete standard trace on a finite free
module, prove
`abstractTraceDimension std_atr = (Module.finrank R V : R)`. This is what will
let downstream 3D callers derive the synthetic dimension marker from the usual
`Module.finrank R V = 3` statement instead of assuming
`abstractTraceDimension atr = 3` directly.

Chapter 11 auxiliary/blow-up status:

- `Global/BlowUp.lean` has theorem interfaces for Lemma 11.1
  (`finite_time_singularity_from_positive_scalar` and its bound wrapper) and
  Lemma 11.2 (`finite_time_curvature_blow_up_from_maximality`), plus the
  scalar-unboundedness bridge used by point selection. The finite-time bound is
  existential (`exists bound, UpperBoundForMaximalTime D bound`), not a claim
  that every bound works. `MaximalTimeWitness` is the bridge from an abstract
  `HasFiniteMaximalTime D` predicate to a concrete terminal time and
  nonextendability proof; `finite_time_curvature_blow_up_from_finite_time`
  composes that bridge with the curvature blow-up alternative. Curvature
  blow-up is expressed as unboundedness of a concrete `curvatureQuantity` on a
  terminal-time-dependent domain, and the scalar blow-up bridge takes that
  blow-up instance directly rather than an existential over typeclass
  instances.
- `DimensionThree/CurvatureAlgebra.lean` has the curvature-control-by-scalar
  interface and proves the algebraic Einstein-to-constant-curvature formula
  from the 3D Riemann-from-Ricci identity and `Rc = (R/3)g`.
- `Global/Compactness.lean` has interfaces for Lemma 11.4 point
  selection/rescaling, Lemma 11.5 CGH curvature convergence, and the curvature
  ratio convergence corollary. These interfaces now use concrete witness
  shapes instead of name-only `Prop` fields: `PointSelectionHypothesis` is
  scalar unboundedness on a spacetime domain, `ParabolicRescalingData` carries
  scalar and pinching-ratio quantities plus the backward region. Pinching-ratio
  invariance is recorded both at the selected base point and across the
  backward region, for later consumers that need the full rescaled flow rather
  than only the basepoint normalization.
  `ScalarSpatialPromotionFromTime` packages the realization bridge from
  time-only scalar unboundedness to the point-spacetime
  `PointSelectionHypothesis`; concrete geometry should instantiate it from
  compactness/continuity of the scalar curvature. `ConvergenceWitness` records an
  actual sequence, limit, and proof against a shared convergence
  relation; the scalar curvature, `|Rm|^2`, `|Ric|^2`, `|Ric°|^2`, and ratio
  witnesses in a conclusion share a single scalar convergence relation.
  `CurvatureConvergenceProfile` packages the tensor/scalar convergence
  relations and eventuality/filter relation once for a compactness interface.
  Curvature-ratio convergence now extends the curvature-convergence interface,
  takes an `EventuallyPositiveWitness` parameterized by that shared eventuality
  relation, and returns a ratio conclusion containing the curvature conclusion
  whose scalar topology/filter it uses. Compactness extraction returns smooth
  CGH convergence data for the selected sequence. Curvature convergence
  conclusions now tie their witnesses
  to canonical synthetic samples: `Rm_tensor`, `ricciForm_tensor`,
  `ScalarCurvature`, `ricci_norm_sq`, and
  `tracefree_ricci_norm_sq`; the Riemann norm remains a supplied quantity,
  explicitly marked in code, until a full `|Rm|^2` tensor norm accessor is
  built. The abstract convergence profile should eventually be replaced by
  `Filter.Tendsto` statements for the chosen topology/filter. Compact
  exhaustion, pullback convergence, and parabolic time arithmetic remain
  realization bridges.
- Remaining global interface debt: `PerelmanNoncollapsing` and
  `MyersTheoremInterface` are still deliberately abstract. They should be
  revisited with the same discipline before final assembly: noncollapsing
  should expose balls, radii, volume, and curvature-scale hypotheses, and Myers
  should expose the Ricci lower bound and diameter/compactness conclusion
  rather than only a name-level predicate.
- The differential part of Lemma 11.6 remains a bridge: use the contracted
  Bianchi identity to prove scalar curvature is constant from `Ric° = 0`, then
  combine it with the algebraic 3D constant-curvature theorem.

## Interface boundary with the Integral/Analysis plan

`DifferentialGeometry/Analysis/INTEGRAL_PLAN.md` is the collaborator-owned
manifold/analysis route: concrete Mathlib integration, Sobolev and heat
machinery, DeTurck short-time existence, concrete tensor maximum principles,
normalized-flow analytic estimates, geodesics/exponential maps, and final
topological sphere recognition. The synthetic Ricci-flow core should not import
`DifferentialGeometry/Integral`, `DifferentialGeometry/Analysis`, or
`DifferentialGeometry/PDE`. The boundary between the two projects should be
theorem interfaces and realization instances: Synthetic proves pointwise
tensor identities, while the concrete manifold layer instantiates them for
`RiemannianMetric` families and applies analytic compactness/integration.

High-priority synthetic quote package for the collaborator:

1. Contracted Bianchi, as a theorem.
   - Target file: `DimensionThree/CurvatureAlgebra.lean` or a small imported
     tensor-calculus file.
   - Intended declaration:
     `contractedSecondBianchiIdentity_from_second_bianchi`.
   - Output:
     `ContractedSecondBianchiIdentity emb conn ha hal hsl hl atr met half`.
   - Inputs:
     `IsHalfCoefficient half`, metric compatibility, the existing
     second-Bianchi/covariant-Riemann identity, and the contraction rules for
     `AbstractTrace`.
   - Use:
     closes the differential half of Lemma 11.6 and gives the concrete
     `div Ric = (1/2)dR` identity that the integral plan quotes in integrated
     scalar-curvature evolution.

2. Three-dimensional Riemann-from-Ricci formula, as a theorem.
   - Current status:
     `RiemannFromRicci3DFormula` is a coefficient-safe predicate/structure,
     and downstream algebra can already consume it.
   - Intended declaration:
     `riemannFromRicci3DFormula_of_dimension_three`.
   - Output:
     `RiemannFromRicci3DFormula emb conn ha hal hsl hl atr met half`.
   - Inputs:
     `IsDimensionThree atr`, `IsHalfCoefficient half`, metric/Riemann
     symmetries and first Bianchi in the synthetic curvature convention, plus
     the finite-dimensional trace realization needed by the 3D algebra.
   - Use:
     the collaborator's MH2/H3 plans call this the pure linear-algebra 3D
     identity. It should be quotable without redoing the curvature algebra in
     the concrete manifold layer.

3. Ricci evolution by contracting the master Riemann evolution.
   - Target file: `Evolution/Ricci.lean`; if the proof grows, split a helper
     file `Evolution/RicciFromRiemann.lean`.
   - Intended declarations:
     `ricci_evolution_from_riemann_evolution`,
     `ricci_contraction_dt_commute`,
     `ricci_contraction_laplacian_commute`, and
     `ricci_contraction_hamilton_reaction`.
   - Output:
     a proved `RicciEvolutionEquation` or
     `RicciLichnerowiczEvolutionEquation`, not only the current interface
     plumbing.
   - Inputs:
     the Synthetic master theorem for
     `dt Rm = laplacian Rm + Q_rm`, contraction through `AbstractTrace`,
     commutation of metric contraction with `dt_tensor` and the rough
     Laplacian, and an algebraic contraction computation for `Q_rm`.
   - Use:
     this is the exact quote point requested by the collaborator's MH2
     `RicciEvolution.lean`.

4. Closed scalar evolution from the Ricci evolution RHS.
   - Current status:
     `Evolution/ScalarCurvature.lean` has the partial formula and the
     `rhs_trace` interface.
   - Intended declarations:
     `trace_rough_laplacian_ricci_eq_scalar_laplacian`,
     `trace_ricci_reaction_eq_zero` for the chosen Lichnerowicz RHS, and
     `scalar_evolution_from_ricci_laplace_reaction`.
   - Output:
     the closed pointwise identity
     `dt R = scalar_laplacian + 2 * ricci_norm_sq`.
   - Inputs:
     Ricci evolution from item 3, trace/Laplacian commutation, contracted
     Bianchi where needed, and the already-proved metric trace contractions.
   - Use:
     keeps the integral plan's scalar evolution input a direct quote rather
     than a concrete-manifold rederivation.

5. Trace-free Ricci norm evolution for Section 10/MH2.
   - Target file:
     `Evolution/RicciNorm.lean` or
     `DimensionThree/TraceFreeEvolution.lean`.
   - Intended declarations:
     `tracefree_ricci_tensor_evolution_from_ricci_scalar`,
     `tracefree_ricci_norm_sq_evolution_hamilton3D`, and the helper
     contractions for `|nabla Ric|^2`, `|grad R|^2`, and Hamilton's cubic
     `Q`.
   - Output:
     a proved `TracefreeRicciNormEvolutionEquation` with the Hamilton 3D RHS
     used to derive the improved pinching subsolution.
   - Inputs:
     Ricci evolution, closed scalar evolution, metric evolution under Ricci
     flow, the 3D Riemann-from-Ricci theorem, tensor-inner-product
     differentiation rules, and the existing cubic trace/`hamiltonCubicQ`
     algebra.
   - Use:
     the collaborator's MH2 `TraceFreeEvolution.lean` should quote this
     instead of expanding the synthetic tensor algebra again.

6. Quotient and improved-pinching producer.
   - Current status:
     `DimensionThree/ImprovedPinching.lean` contains the scalar weak
     maximum-principle consumer once a shifted subsolution is supplied.
   - Intended declarations:
     `quotient_evolution_for_positive_scalar`,
     `improved_pinching_subsolution_from_tracefree_evolution`, and
     `improved_pinching_estimate_for_ricci_flow`.
   - Output:
     an instantiated `ImprovedRicciPinchingEstimateAlongFlow` for
     `P = |Ric0|^2 / R^(2 - epsilon)` and
     `ratio = |Ric0|^2 / R^2`.
   - Inputs:
     item 5, scalar positivity, algebra for powers/quotients in the chosen
     scalar field, and the strict positive-Ricci pinching input supplied by
     the tensor maximum-principle layer.
   - Use:
     feeds the Section 12 squeeze lemmas already present in
     `Global/Compactness.lean`.

7. Norm-definiteness and Einstein conversion on the limit.
   - Intended declarations:
     `tracefree_ricci_tensor_eq_zero_of_norm_sq_zero` and
     `constant_positive_sectional_curvature_of_tracefree_zero`.
   - Output:
     from `tracefree_ricci_norm_sq = 0`, scalar positivity, contracted
     Bianchi, and the 3D Riemann-from-Ricci theorem, produce the typed
     constant-positive-sectional-curvature predicate needed by
     `HamiltonSection12AssemblyData`.
   - Inputs:
     positive-definiteness of the concrete metric inner product as a
     realization bridge, item 1, item 2, and the existing
     `riemannFromRicci3DFormula_constant_curvature_of_einstein`.
   - Use:
     removes another manual field from the Section 12 assembly certificate.

Concrete realization hooks the collaborator should instantiate, not reprove in
Synthetic:

- identify a concrete Ricci-flow metric family with `RicciFlowData`;
- prove `abstractTraceDimension atr = (Module.finrank R V : R)` for the
  standard trace, and specialize it to dimension three;
- identify `Rm_tensor`, `ricciForm_tensor`, `ScalarCurvature`,
  `ricci_norm_sq`, `tracefree_ricci_norm_sq`, `hamiltonCubicQ`, and
  `tracefreeRicciPinchingQuantity` with the concrete manifold curvature
  quantities;
- instantiate `PositiveInitialScalarFromRicciPositive` from finite-dimensional
  positive-definite Ricci trace algebra;
- instantiate convergence profiles with concrete `Filter.Tendsto` or smooth
  Cheeger-Gromov-Hamilton convergence;
- instantiate `ScalarConvergenceSqueezeToZero` from the chosen topology and
  eventuality filter;
- instantiate compactness, noncollapsing, Myers, and diffeomorphism
  interfaces from the concrete manifold/analysis layer.

Avoid duplicating collaborator work:

- Do not build concrete Riemannian volume, integration by parts, Sobolev,
  heat-semigroup, parabolic-existence, DeTurck, or Ricci short-time existence
  inside `Synthetic/Flow/RicciFlow`.
- Do not import the heavy analysis tree into the synthetic evolution or
  pinching modules. When an analytic fact is needed, expose it as a narrow
  theorem parameter/typeclass and document the concrete instantiation point.
- Do not differentiate eigenvalue functions globally in the synthetic core.
  Keep the proved eigenvalue algebra pointwise and route global pinching
  through tensor/norm quantities unless a concrete manifold proof supplies the
  needed selection regularity.

Subsection 14.2 tensor-calculus goals:

- Existing Lean coverage:
  - `TensorData` and `AbstractTrace` in
    `Synthetic/Algebra/TensorAlgebra.lean` cover the `(r,s)` tensor model and
    abstract contraction.
  - `nabla_dual`, `nabla_tensor`, `nabla_add`, `nabla_smul`,
    `nabla_add_left`, `nabla_smul_left`, `nabla_tensor_prod`, and
    `genericCovDeriv_contract` in `Synthetic/Analysis/NablaOnTensors.lean`
    and `Synthetic/Operator/CovariantDerivative.lean` cover the covariant
    derivative, linearity, Leibniz rule, and contraction-commutation API.
  - `R_XY`, `R_XY_vector`, `nabla_02_eval`, and
    `tensor_ricci_identity_02` in `Synthetic/Geometry/ConnectionExtended.lean`
    cover the invariant curvature operator and the proved Ricci identity for
    `(0,2)` tensors.
  - `tensor_inner_02`, `ricci_norm_sq`, and `tensor_trace_cube_02` in
    `Evolution/ScalarCurvature.lean` cover the inner product/norm/cubic-trace
    layer currently needed by pinching.
  - `laplacian`, `SecondCovDerivTensor`, and vector-field `divergence` are in
    `Synthetic/Operator/Laplacian.lean` and
    `Synthetic/Operator/Divergence.lean`.
- Current Lean status added for the Lemma 11.6 differential half:
  - `Synthetic/Operator/CovariantDerivative.lean` now defines the narrow
    `(0,2)` divergence support needed for contracted Bianchi:
    `covDeriv02TraceCovector`, `covDivergence02Endomorphism`, and
    `covariantDivergence02At`. It also proves the product-rule calculation
    `covariantDivergence02At_smul_metric`, i.e. `div(f g)(Y) = Y(f)` under
    metric compatibility.
  - `DimensionThree/CurvatureAlgebra.lean` now defines
    `ricciDivergenceAt`, `ContractedSecondBianchiIdentity`, and
    `EinsteinDivergenceFormula`.
  - `einsteinRicciFormula_of_tracefree_ricci_tensor_eq_zero` proves the
    algebraic bridge `Ric° = 0 -> Ric = third * R * g` once
    `third = nInv`.
  - `scalar_spatial_constant_of_contracted_bianchi_and_einstein_divergence`
    proves the differential consumer: contracted Bianchi plus the divergence
    formula for an Einstein Ricci tensor imply `IsSpatialConstant R`, assuming
    the coefficient `(half - third)` is cancellable.
  - `einsteinDivergenceFormula_of_einsteinRicciFormula` now proves
    `EinsteinDivergenceFormula` from `EinsteinRicciFormula`, `nabla_g_zero`,
    and spatial constancy of `third`.
  - `scalar_spatial_constant_of_contracted_bianchi_and_tracefree_ricci_zero`
    packages the differential half from `Ric° = 0` using `nInv` directly; the
    only remaining geometric input is contracted second Bianchi.
  - `Synthetic/Operator/SpatialConstant.lean` has
    `isSpatialConstant_algebraMap`, so coefficients written as base-field
    constants `algebraMap k R c` discharge spatial constancy automatically.
    This is the right structural statement: arbitrary elements of the
    synthetic scalar ring `R` need not be spatially constant.
  - `DimensionThree/CurvatureAlgebra.lean` has `coeff_cancel_of_ne`, turning
    a nonzero coefficient such as `half - nInv` into the cancellation
    hypothesis used by the contracted-Bianchi consumer.
- Remaining tensor-calculus proof targets before Lemma 11.6 is fully internal:
  1. Prove `ContractedSecondBianchiIdentity` from the existing
     `covDerivRm_sum_endo`/second-Bianchi theorem by contracting the right
     slots through `AbstractTrace`.
  2. Add a realization lemma identifying `covariantDivergence02At` with the
     local-frame formula
     `g^{ij} (nabla_i T)_{j k}` used in the LaTeX subsection.
  3. TODO: build a general tensor divergence API. The current
     `covariantDivergence02At` is only a narrow `(0,2)` bridge for contracted
     Bianchi. Section 14.2 ultimately needs a uniform `(r,s)`/at least `(0,s)`
     divergence operator, trace-over-a-covariant-derivative lemmas, local-frame
     component formulas, and compatibility with the rough Laplacian used in
     derivative estimates.
  These tensor-calculus items are now parked while the near-term work returns
  to the Section 12 proof skeleton. Do not add more local-coordinate or general
  divergence infrastructure unless it directly discharges a Section 12 field.

Section 12 assembly status:

- `HamiltonThreeManifold.lean` now has the tensor weak maximum-principle
  consumer for preservation of nonnegative Ricci curvature:
  `ricci_nonnegative_preserved_by_tensor_wmp`. The remaining bridge is to prove
  that the actual Ricci tensor evolution satisfies the supplied cone
  subsolution predicate.
- `HamiltonThreeManifold.lean` now has the typed finite-time/blow-up start of
  Section 12:
  `PositiveInitialScalarFromRicciPositive`,
  `positive_initial_scalar_from_typed_positive_ricci`,
  `finite_time_from_typed_positive_ricci`,
  `finite_time_bound_from_typed_positive_ricci`,
  `curvature_blow_up_from_typed_maximal_time`,
  `scalar_unbounded_from_typed_maximal_time`, and
  `point_selection_rescaling_from_typed_maximal_time`, plus the fully composed
  wrappers `curvature_blow_up_from_typed_finite_time`,
  `scalar_unbounded_from_typed_finite_time`, and
  `rescaling_certificate_from_typed_input`. The positive-Ricci to
  positive-scalar step is kept as a finite-dimensional trace/eigenvalue
  realization bridge. The finite-time to terminal-time link is now isolated in
  `MaximalTimeWitness`, and the scalar-blow-up to point-spacetime
  point-selection link is packaged as `ScalarSpatialPromotionFromTime`.
  `finite_time_bound_from_typed_positive_ricci` is recorded for downstream
  time-window/compactness arguments, but the current rescaling certificate does
  not yet consume that bound.
- `HamiltonThreeManifold.lean` now also has
  `HamiltonSection12RescalingConvergenceData` and
  `rescaling_convergence_data_from_typed_input`. This composes typed positive
  Ricci through rescaling, Hamilton compactness, and curvature-ratio
  convergence. The curvature conclusion used downstream is `ratio.curvature`,
  so the ratio and curvature data share the same CGH convergence profile by
  construction. The only extra input at this stage is the eventual
  scalar-positivity witness required by the ratio-convergence interface.
- `HamiltonThreeManifold.lean` also has
  `LimitScalarPositivityProblem` and
  `limit_scalar_positive_everywhere_from_strong_mp`. This is the typed
  consumer for the argument "Ricci nonnegative on the CGH limit plus
  normalized scalar `R(base)=1` implies scalar curvature is positive on the
  chosen spacetime region." `LimitScalarPositivityProblem` now exposes the
  limit Ricci tensor as a pointwise quadratic-form predicate over a limit
  point type; the concrete manifold/spacetime model is still abstract.
- `Global/Compactness.lean` now includes
  `CompactLimitDiffeomorphismUnderSmoothCGH`, the Section 12 interface for
  compact smooth CGH limits implying eventual diffeomorphism between the
  sequence manifolds and the limit manifold.
- `Global/Compactness.lean` now also has
  `scalar_limit_eq_one_from_rescaling_curvature_convergence`: normalized
  scalar curvature at the selected rescaling basepoints transfers through the
  scalar convergence profile to the CGH limit scalar value `1`, once the
  realization identifies the point-selection scalar quantity with the
  synthetic scalar sample and scalar convergence has unique limits.
- `HamiltonThreeManifold.lean` now has
  `original_limit_diffeomorphism_from_compact_limit_at_index`: from one
  sufficiently large-index instance of the compact-limit diffeomorphism
  conclusion and the realization fact that rescaling preserves the underlying
  initial manifold, it extracts the original-to-limit diffeomorphism used by
  the final pullback step.
- `ParabolicRescalingData` now records the quantitative pinching decay rule at
  the selected base point through `pinchingDecayQuantity`,
  `pinchingDecayFactor`, and `pinching_ratio_decay_rule_at_base`. This is the
  slot for the concrete `R_i^{-epsilon}` factor coming from the improved
  pinching estimate.
- `Global/Compactness.lean` now has the Section 12 squeeze bridge
  `ScalarConvergenceSqueezeToZero`, `EventuallyImp`, and the producer lemmas
  `tracefree_ratio_quantity_limit_eq_zero_of_squeeze` and
  `limit_tracefree_ricci_norm_sq_eq_zero_of_squeezed_ratio`. These convert
  ratio convergence plus an eventual zero-convergent upper bound into
  `|Ric^0|^2 = 0` on the CGH limit sample. The remaining realization work is
  to instantiate the squeeze bridge with the chosen `Filter.Tendsto` profile
  and prove the improved-pinching upper bound supplies the required
  zero-convergent upper sequence.
- `Global/Compactness.lean` now also has the improved-pinching-to-limit sample
  bridge
  `limit_tracefree_ricci_norm_sq_eq_zero_of_improved_pinching_decay` and its
  weak-maximum-principle consumer
  `limit_tracefree_ricci_norm_sq_eq_zero_of_improved_pinching_wmp_decay`. These
  take an `ImprovedRicciPinchingEstimateAlongFlow`, identify its ratio sequence
  with the CGH trace-free ratio sequence, use eventual membership in the
  pinching domain, and conclude `|Ric^0|^2 = 0` on the limit sample once
  `C * decay_i -> 0`.
- The compact-region version is now represented by
  `UniformTracefreeRatioDecayOnRegion` and
  `limit_tracefree_ricci_norm_sq_eq_zero_on_region_of_uniform_decay`. This uses
  one shared upper sequence on a region and proves vanishing of
  `|Ric^0|^2` at every limit sample in that region. The realization layer still
  has to instantiate `RegionPoint` and prove the uniform decay/convergence
  hypotheses from smooth CGH convergence and the concrete rescaling.
- The large missing Section 12 input is still the improved pinching theorem
  from Section 10: trace-free Ricci norm evolution, quotient evolution,
  evolution of `P = |Ric^0|^2 / R^(2-epsilon)`, and strict positive Ricci
  pinching. The final scalar weak maximum-principle step is now isolated in
  `DimensionThree/ImprovedPinching.lean`.

Section 12 proof plan:

The final assembly should move from the current single
`HamiltonThreeManifoldBlackBoxes` class to a granular proof skeleton in
`HamiltonThreeManifold.lean`. Each field should correspond to one displayed
step in `main.tex` Section 12, and the final theorem should be a real Lean
composition of those fields.

1. Refine the theorem input/output.
   - Current Lean status: `HamiltonThreeManifoldGeometricContext` now carries
     the realization hooks `Manifold`, `Metric`, `Diffeomorphism`,
     `manifoldOfFlow`, `metricOn`, compactness/connectedness predicates, the
     diffeomorphism predicate, and the pullback rule for constant-positive
     sectional curvature.
   - Current Lean status: `HamiltonThreeManifoldTypedInput` replaces the old
     name-only initial assumptions by compact/connected predicates on the
     initial manifold and a genuine
     `RicciPositive ... (conn_fam initialTime) ...` hypothesis.
   - Current Lean status: `HamiltonThreeManifoldTypedConclusion` says the
     initial manifold carries a metric with constant positive sectional
     curvature. The canonical final wrapper is
     `hamilton_three_manifold_exists_constant_positive_metric`, which states
     exactly the `main.tex` conclusion:
     `exists g, metricOn initialManifold g` and `g` has constant positive
     sectional curvature. The old `HamiltonThreeManifoldBlackBoxes` theorem
     remains only as a compatibility wrapper.
   - Current Lean status: `HamiltonSection12Claims` is the collaborator-facing
     typed claim bundle for this branch. It reuses
     `HamiltonSection12RescalingConvergenceData` for the rescaling/CGH/ratio
     prefix and asks only for the remaining Section 12 limit-geometry and
     final-diffeomorphism claims.

2. Build the maximal-flow and blow-up branch.
   - File: `Global/BlowUp.lean` plus `HamiltonThreeManifold.lean`.
   - Consume `PositiveScalarFiniteTimeTheorem` to obtain finite maximal time.
   - Consume `CurvatureBlowUpAlternative` and
     `ScalarBlowUpFromCurvatureBlowUp` to obtain scalar unboundedness.
   - Feed scalar unboundedness into `PointSelectionAndRescalingTheorem` to
     obtain `ParabolicRescalingData` with `scale_tends_to_infinity`,
     scalar normalization at the base, and backward-region scalar control.
   - Current Lean status:
     `positive_initial_scalar_from_typed_positive_ricci` and
     `finite_time_from_typed_positive_ricci` compose typed positive Ricci with
     the finite-time theorem through the bridge class
     `PositiveInitialScalarFromRicciPositive`.
   - Current Lean status:
     `curvature_blow_up_from_typed_maximal_time` and
     `scalar_unbounded_from_typed_maximal_time` compose a supplied terminal
     maximal time/nonextendability proof with the curvature- and
     scalar-blow-up interfaces.
   - Current Lean status:
     `point_selection_rescaling_from_typed_maximal_time` feeds the resulting
     scalar unboundedness into `PointSelectionAndRescalingTheorem`, with the
     point-spacetime realization bridge supplied explicitly.
   - Current Lean status:
     `MaximalTimeWitness` connects the abstract finite-time predicate to a
     concrete terminal time and nonextendability proof, and
     `curvature_blow_up_from_typed_finite_time`/
     `scalar_unbounded_from_typed_finite_time` use that bridge so callers no
     longer have to pass `T` and `hmax` by hand.
   - Current Lean status:
     `ScalarSpatialPromotionFromTime` packages the time-only scalar
     unboundedness to point-spacetime point-selection bridge, and
     `rescaling_certificate_from_typed_input` returns the exact
     `ParabolicRescalingData` subtype certificate shape used by
     `HamiltonSection12AssemblyData`.
   - Current Lean status:
     `HamiltonSection12RescalingConvergenceData` and
     `rescaling_convergence_data_from_typed_input` push this one step further:
     from the typed input they produce rescaling data, a smooth CGH limit, and
     a curvature-ratio convergence conclusion whose curvature profile is the
     same one used by the ratio.
   - Remaining bridge: instantiate `PositiveInitialScalarFromRicciPositive`
     from finite-dimensional positivity/trace algebra, instantiate
     `MaximalTimeWitness` from the concrete maximal-interval object, and
     instantiate `ScalarSpatialPromotionFromTime` from compactness/continuity
     of the scalar curvature. The produced maximal-time bound is still waiting
     for a downstream consumer in the parabolic-region/time-window part of the
     Section 12 proof.

3. Get uniform curvature and noncollapsing on rescaled flows.
   - File: `DimensionThree/CurvatureAlgebra.lean`,
     `Global/Compactness.lean`, and possibly a new
     `Global/Section12.lean` if `HamiltonThreeManifold.lean` becomes too large.
   - Use `ricci_nonnegative_preserved_by_tensor_wmp` to preserve
     `Ric >= 0`; the owed input is the Ricci-evolution cone subsolution.
   - Use the 3D curvature-control-by-scalar interface plus
     `scalar_max_on_backward_interval` and base normalization to prove a
     uniform `|Rm| <= C` statement on the backward parabolic region.
   - Current Lean status: `PerelmanNoncollapsingAtScale` and
     `KappaNoncollapsedAtScale` are the typed replacement for the old
     name-only noncollapsing interface. They mention a base point, time,
     radius, ball-volume function, kappa, positivity of radius/kappa, and the
     lower bound `kappa * radius^3 <= volume`.
   - Owed concrete theorem: convert the normalized `|Rm|` bound and
     noncollapsing lower volume bound into the hypotheses of
     `HamiltonCompactnessTheorem`.

4. Extract the CGH limit and transfer curvature information.
   - File: `Global/Compactness.lean`.
   - Use `HamiltonCompactnessTheorem.extract_limit` to get
     `SmoothCGHConvergenceData`.
   - Use `CurvatureConvergenceUnderSmoothCGH` to transfer Riemann, Ricci,
     scalar, Ricci norm, trace-free Ricci norm, and ratio convergence.
   - Current Lean status: `RicciNonnegativeClosedUnderCGHCurvatureConvergence`
     and `limit_ricci_nonnegative_from_cgh_curvature_convergence` name the
     closed-cone bridge from `Ric(g_i) >= 0` to `Ric(g_infty) >= 0`.
   - Current Lean status: `scalar_limit_eq_of_constant_samples` proves the
     profile-level scalar-normalization transfer from a constant scalar sample
     sequence to the limit, assuming uniqueness of scalar convergence limits
     for that profile.
   - Current Lean status:
     `scalar_limit_eq_one_from_rescaling_curvature_convergence` specializes
     this to the Section 12 rescaling setup and produces the limit scalar
     normalization `R_infty = 1`.
   - Current Lean status:
     `rescaling_convergence_data_from_typed_input` composes the rescaling and
     compactness/convergence interfaces through the ratio-convergence layer,
     using `ratio.curvature` as the curvature conclusion to avoid
     cross-conclusion topology/profile mismatch.
   - These are still profile-level statements; the later realization should
     replace the abstract convergence profile by `Filter.Tendsto`.

5. Prove scalar positivity on the limit.
   - File: `HamiltonThreeManifold.lean` or `Global/Section12.lean`.
   - Instantiate `LimitScalarPositivityProblem` from the CGH limit data:
     limit scalar function, spacetime region `M_infty x (alpha,0]`,
     nonnegative Ricci, and normalized base scalar.
   - Apply `limit_scalar_positive_everywhere_from_strong_mp`.
   - Missing bridge: encode connectedness/completeness/bounded-geometry
     assumptions needed by the strong maximum-principle interface.

6. Use improved pinching to force the limit Einstein.
   - File: `DimensionThree/Pinching.lean` for the algebra/evolution
     prerequisites, `DimensionThree/ImprovedPinching.lean` for the scalar WMP
     consumer, and final use in `HamiltonThreeManifold.lean`.
   - Current status: `ImprovedRicciPinchingEstimateAlongFlow` records the
     Hamilton quantity `P`, the scale-invariant ratio, the abstract decay
     factor intended as `R^(-epsilon)`, and the shifted subsolution
     `P - C`. The proved theorem
     `improved_ricci_pinching_ratio_bound_from_wmp` gives
     `ratio <= C * decay` from the scalar weak maximum principle.
     The WMP consumer only needs the inequality
     `ratio <= P * decay`; the intended instantiation from
     `tracefreeRicciPinchingQuantity` is an equality under positive scalar
     curvature.
   - Remaining input: instantiate this structure by proving the quotient
     evolution/subsolution statement for
     `P = |Ric^0|^2 / R^(2-epsilon)`, including the trace-free Ricci norm
     evolution and strict positive Ricci pinching.
   - Use `ParabolicRescalingData.pinching_ratio_decay_rule_at_base` and then
     extend it to compact regions, not only the selected base point, if the
     final limit argument needs region-wise decay.
    - Current Lean status:
      the basepoint/sample version is in `ScalarConvergenceSqueezeToZero`,
      `tracefree_ratio_quantity_limit_eq_zero_of_squeeze`,
      `limit_tracefree_ricci_norm_sq_eq_zero_of_squeezed_ratio`, and
      `limit_tracefree_ricci_norm_sq_eq_zero_of_improved_pinching_wmp_decay`.
      The compact-region abstraction is in `UniformTracefreeRatioDecayOnRegion`
      and `limit_tracefree_ricci_norm_sq_eq_zero_on_region_of_uniform_decay`.
      Section 12 still needs the concrete `Filter.Tendsto` instantiation and
      the smooth-CGH proof that the chosen decay factors tend uniformly to zero
      on the region being passed to the limit.
   - Conclude `tracefree_ricci_norm_sq = 0` on all compact subsets and hence
     `Ric^0(g_infty(t)) = 0`. This last implication needs a norm-definiteness
     bridge for the metric tensor norm.

7. Turn Einstein limit into positive constant curvature.
   - File: `DimensionThree/CurvatureAlgebra.lean` and
     `HamiltonThreeManifold.lean`.
   - Use the existing 3D algebraic theorem
     `riemannFromRicci3DFormula_constant_curvature_of_einstein`.
   - Finish the differential bridge from Lemma 11.6: contracted Bianchi gives
     scalar curvature constant from `Ric^0 = 0`; normalized scalar at the base
     gives positive scalar.
   - Package the result as a typed constant-positive-sectional-curvature metric
     on the CGH limit manifold.

8. Compactness of the limit and diffeomorphism back to the original manifold.
   - File: `Global/Compactness.lean`.
   - Current Lean status: `MyersPositiveRicciCompactness` and
     `MyersCompactnessConclusion` are the typed replacement for the old
     name-only Myers interface. They consume a positive Ricci lower-bound
     predicate and return compactness plus a diameter-bound slot.
   - Current Lean status: `CompactLimitDiffeomorphismUnderSmoothCGH` gives the
     compact-limit diffeomorphism interface.
   - Current Lean status:
     `original_limit_diffeomorphism_from_compact_limit_at_index` converts one
     large-index instance of that eventual diffeomorphism into the exact
     original-to-limit diffeomorphism used in the final typed theorem, provided
     rescaling is known to preserve the underlying manifold.
   - Current Lean status:
     `typed_conclusion_of_diffeomorphic_constant_positive_limit` performs the
     final pullback of a constant-positive-curvature metric across a
     diffeomorphism.

9. Final theorem replacement.
   - Current Lean status: `HamiltonSection12AssemblyData` is a typed
     certificate with fields for the Section 12 checkpoints: rescaling, CGH
     data, curvature and ratio convergence, limit scalar positivity, normalized
     scalar, trace-free Ricci norm vanishing, constant-positive-curvature limit
     metric, Myers compactness, compact-limit diffeomorphism, and the final
     original-to-limit diffeomorphism.
   - Current Lean status:
      `hamilton_three_manifold_from_section12_assembly` constructs the typed
      final conclusion from that certificate.
      `hamilton_section12_assembly_from_claims` builds a nonempty assembly
      certificate from `HamiltonSection12Claims`.
      `hamilton_three_manifold_typed_conclusion_of_section12_claims` packages
      the nonempty-certificate version, and
      `hamilton_three_manifold_exists_constant_positive_metric` is the actual
      theorem statement matching `main.tex`: the original manifold admits a
      constant-positive-sectional-curvature metric.
      `hamilton_three_manifold_from_section12_claims` is the convenience
      theorem for this branch. The collaborator may realize the claims from the
      analytic/manifold plan; this synthetic branch should only replace claims
      with producer lemmas when the proof is lightweight and does not import the
      collaborator analysis/integral/PDE subtree.

## Implementation discipline

Prefer theorem interfaces or typeclasses for analytic/geometric black boxes.
Avoid `sorry` in new roadmap modules. The implementation can use classes for
short-time existence, maximum principles, compactness, noncollapsing, and Myers
until those analytic proofs are formalized.

Targeted compile checks for each phase:

```text
lake env lean DifferentialGeometry/Synthetic/Flow/RicciFlow/Evolution/Connection.lean
lake env lean DifferentialGeometry/Synthetic/Flow/RicciFlow/Evolution/ScalarCurvature.lean
lake env lean DifferentialGeometry/Synthetic/Flow/RicciFlow/Evolution/RiemannEvolution.lean
lake build
```
