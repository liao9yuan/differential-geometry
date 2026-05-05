# Hamilton Three-Manifold Theorem — Obligations

This document is the single source of truth for **what we still need to prove**
to close the Hamilton positive-Ricci theorem in this branch. Each item is
backed by a concrete Lean object (typeclass, structure field, or theorem
target). Cross-reference: `FORMALIZATION_PLAN.md` for design intent and source
map.

## Top-level statement

```
hamilton_three_manifold_from_typed_input
    [HamiltonSyntheticAnalyticInputs]    -- 9 PDE/global typeclasses
    [HamiltonP1ContractedSecondBianchiTheorem]
    [HamiltonP2RiemannFromRicci3DTheorem]
    [HamiltonP3CubicReactionGeometryTheorem]
    (hpos)                                -- eventually-positive curvature ratio
    (builder : HamiltonSection12ClaimBuilderInput)
    (input  : HamiltonThreeManifoldTypedInput)
  : ∃ g, metricOn input.initialManifold g ∧ hasConstantPositiveSectionalCurvature
```

The theorem is structurally complete in Lean. **Nothing here asks for new
synthetic architecture.** Every obligation below is either:

- a typeclass instance to be proved,
- a structure field to be filled,
- or a coordinate calculation to be performed against an existing theorem
  skeleton.

Status legend: ✅ done · 🟡 partially done / has skeleton · ❌ not started

---

## A. Analytic / PDE obligations (collaborator territory)

These are the nine typeclasses bundled by
[`HamiltonSyntheticAnalyticInputs`](HamiltonThreeManifold.lean#L1081). They
are kept abstract in this branch; the collaborator owns the concrete proofs.
Listed for completeness so it's clear what we are *not* responsible for.

### A1. `PositiveScalarFiniteTimeTheorem` ❌
**Math:** Lemma 11.1. Positive initial scalar curvature ⟹ Ricci flow has
finite maximal existence time, with an initial-data-dependent upper bound.
**Tool:** scalar maximum principle on `∂_t R = ΔR + 2|Ric|²`.
**Where:** `Global/BlowUp.lean:35`.

### A2. `PositiveInitialScalarFromRicciPositive` 🟡
**Math:** Positive Ricci ⟹ positive scalar (point-trace).
**Status:** synthetic skeleton present at
`HamiltonThreeManifold.lean:265`; instance comes from algebraic
`Rc_positive ⟹ R_positive` once `RicciFlowData` carries a Levi-Civita.

### A3. `MaximalTimeWitness` ❌
**Math:** Hamilton-Ricci-flow maximal-interval realization. Picks the
terminal time from an abstract `HasFiniteMaximalTime` predicate.
**Where:** `Global/BlowUp.lean:73`.

### A4. `CurvatureBlowUpAlternative` ❌
**Math:** Lemma 11.2. At finite maximal time, curvature is unbounded above
(i.e., the only obstruction to extension is curvature blow-up).
**Tool:** Hamilton's extension criterion + parabolic regularity.
**Where:** `Global/BlowUp.lean:92`.

### A5. `ScalarBlowUpFromCurvatureBlowUp` ❌
**Math:** Curvature blow-up + 3-dim positive Ricci ⟹ scalar curvature
unbounded above.
**Where:** `Global/BlowUp.lean:127`.

### A6. `PointSelectionAndRescalingTheorem` ❌
**Math:** Hamilton's point selection lemma. From scalar-unbounded data, pick
basepoints `(p_i, t_i)` where the rescaling factor is asymptotically maximal.
Returns a parabolically rescaled flow sequence.
**Where:** `Global/Compactness.lean:177`.

### A7. `ScalarSpatialPromotionFromTime` 🟡
**Math:** Promote time-domain scalar blow-up to a point-selection-shaped
hypothesis. Bookkeeping bridge.
**Where:** `Global/Compactness.lean:115`.

### A8. `HamiltonCompactnessTheorem` ❌
**Math:** Hamilton-Cheeger-Gromov compactness. Bounded curvature + injectivity
radius bound (Perelman noncollapsing) ⟹ smooth subsequential CGH limit.
**Where:** `Global/Compactness.lean:652`.

### A9. `CurvatureRatioConvergenceUnderSmoothCGH` ❌
**Math:** Under smooth CGH convergence, the Ricci-pinching ratio
`|Ric⁰|² / R^(2−ε)` passes to the limit.
**Where:** `Global/Compactness.lean:631`.

### A10. (consumed inside `section12_claims_from_typed_input`)
`ScalarStrongMaximumPrinciple R SpaceTime` ❌
**Math:** Strong maximum principle for the limit scalar PDE: limit scalar ≥ 0
and not zero somewhere ⟹ limit scalar > 0 everywhere.
**Where:** `Analysis/Parabolic/ScalarMaximumPrinciple.lean:67`.

---

## B. Synthetic gap typeclasses (our territory)

The three named gaps. Each is a single typeclass abstracting the per-slice
geometric content.

### B1. `HamiltonP1ContractedSecondBianchiTheorem` 🟢
**Math:** twice-contracted second Bianchi identity, `2 div Ric = ∇R`.
**Lean target:** [`HamiltonThreeManifold.lean:755`].
**Status:** typeclass declared, Hamilton-level builder **done**.

#### B1.1 — Hamilton-level builder ✅
`hamiltonP1ContractedSecondBianchiTheorem_of_named_calculus` is now analogous
to P2's `_of_dim3_calculus`. It lifts per-slice
`HasDoubleMetricTrace05PatternFubini`,
`HasContractedSecondBianchiNamedPatternCalculus`, and `NablaTrComm` witnesses
to the Hamilton P1 typeclass, deriving metric compatibility and torsion-free
from each `RicciFlowData` slice.

`HamiltonP1NamedCalculusInputs` is the final-proof-facing bundle for those
three per-slice witnesses, and
`hamilton_three_manifold_from_typed_input_with_p1_named_calculus` feeds it into
the Section 12 theorem. The final wrapper now derives P1 internally from the
named-pattern calculus package; P2 remains explicit unless the caller uses one
of the P2 package wrappers, and P3 can be derived from the eigenvalue-package
route.

#### B1.2 — Per-slice `HasContractedSecondBianchiNamedPatternCalculus` ✅
This typeclass extends the slot-audit class and adds two trace-accessor
identifications. The concrete standard-trace P1 package has now proved the
slot-audit and raw trace identifications in
`Realization/MetricTraceFubini.lean`. The public theorem
`concreteHasContractedSecondBianchiNamedPatternCalculus` exposes those
calculations as the per-slice named calculus; the Hamilton builder then lifts
that calculus through `HamiltonP1ContractedSecondBianchiTheorem`.

| Field | Status | Notes |
|---|---|---|
| `cycle_right_apply_eq_gradPattern` | DONE concrete | Proved for the concrete standard-trace package; needs only public instance wiring if we want a global typeclass. |
| `cycle_left_apply_eq_divFubiniPattern` | DONE concrete | Proved through the slot-audit package, using the lowered-curvature symmetries and concrete metric-trace Fubini. |
| `divPattern_apply_eq_ricciDivergence` | DONE concrete modulo trace-commutation input | Raw concrete trace-to-swapped-Ricci-divergence is proved, and concrete `HasMetricAdjointTraceInvariant` now supplies the Ricci-symmetry/adjoint-trace bridge. |
| `gradPattern_apply_eq_neg_grad_R` | DONE concrete modulo trace-commutation input | The concrete pattern is identified with the trace of `∇Ric♯`; the final `-dR` statement consumes the existing `NablaTrComm` bridge. |

#### B1.3 — `HasMetricAdjointTraceInvariant` concrete instance DONE
**Math:** `tr(A) = tr(B)` when B is the metric adjoint of A. Standard
finite-dim fact `tr(A) = tr(A†)`, instantiated for `concreteAbstractTrace`
and any synthetic `MetricDuality` over smooth tangent sections.
**Where:** `Realization/MetricTraceFubini.lean`.
**Declarations:** `concreteTr_eq_of_metric_adjoint`,
`concreteHasMetricAdjointTraceInvariant`.

---

### B2. `HamiltonP2RiemannFromRicci3DTheorem` 🟢
**Math:** In dimension 3, the Weyl tensor vanishes, so Riemann is fully
determined by Ricci + scalar:
```
Rm(X,Y,Z,W) = Ric(X,Z)g(Y,W) + Ric(Y,W)g(X,Z) − Ric(X,W)g(Y,Z) − Ric(Y,Z)g(X,W)
            − ½ R · (g(X,Z)g(Y,W) − g(X,W)g(Y,Z))
```
**Lean target:** `HamiltonThreeManifold.lean:765`.
**Status:** typeclass declared, Hamilton-level builders ✅, per-slice real
finite-dimensional producer ✅. Concrete manifold realization remains F6.

#### B2.1 — Per-slice `HasRiemannFromRicci3DCalculus` DONE for the real finite-dimensional model
Single `residual_zero` field: a proof of the 3D Riemann decomposition formula
at a point. `CurvatureAlgebra.lean` already has the coefficient-safe
`RiemannFromRicci3DFormula` interface and the Ricci-symmetry bridge
`Rc_symm_of_metric_adjoint_trace_invariant`; the finite-frame reduction lives
in `DimensionThree/RiemannFromRicci3D.lean`.

The current P2 route is split into three concrete primitives:

1. **M1: Ricci diagonalization in an orthonormal `Fin 3` frame.**
   DONE for real finite-dimensional inner-product models:
   `ricciDiagonalization3D_of_real_inner_product` builds
   `RicciDiagonalization3D` from `Module.finrank ℝ E = 3`, `met.g = inner ℝ`,
   and Mathlib symmetry of the Ricci endomorphism. The convenience theorem
   `ricciDiagonalization3D_of_real_inner_product_and_Rc_symm` derives that
   Mathlib symmetry from pointwise Ricci symmetry. A generic RCLike
   `symmetricEigenbasis3` helper records the same spectral theorem over both
   `ℝ` and `ℂ`; the Ricci-flow package remains real-valued because the current
   synthetic `MetricDuality` is bilinear, not Hermitian. Low-priority TODO:
   add a Hermitian analogue of `MetricDuality` before promoting the complex
   spectral helper into a complex Ricci-flow-facing diagonalization theorem.
2. **M2: orthonormal trace expansion and sectional solve.**
   The interfaces are `HasOrthonormalBasisTraceFormula3` and
   `RicciSectionalTraceFormula3D`. This turns Ricci diagonal components into
   the scalar trace and the three sectional components `K_01`, `K_02`, and
   `K_12`. The algebraic solve is now factored:
   `sectionalComponent3D_swap` proves `K_ij = K_ji`, and
   `ricciSectionalTraceFormula3D_of_trace_equations` builds the solved
   sectional package from the diagonal Ricci trace equations.
   `scalarCurvature_eq_sum_lambda_of_orthonormal_trace3` proves the scalar
   eigenvalue sum, and
   `ricciForm_tensor_eq_sectional_sum_of_orthonormal_trace3` proves the
   positive diagonal trace equations after fixing the source Ricci convention
   to `RcEndo X Z = (Y ↦ Rm X Y Z)`.
   The finite-dimensional standard-trace route is now available through
   `realTrace_hasOrthonormalBasisTraceFormula3`, from the hypotheses
   `atr.tr = LinearMap.trace` and `met.g = inner`.
3. **M3: off-diagonal curvature components vanish in the Ricci eigenframe.**
   The interfaces are `RicciOffDiagonalTraceFormula3D` and
   `RicciMixedCurvatureFormula3D`. These mixed identities come from the
   off-diagonal Ricci trace formula plus the first-Bianchi/curvature-symmetry
   sign convention. `ricciMixedCurvatureFormula3D_of_offDiagonal_trace`
   performs the final zeroing step from the off-diagonal trace identities and
   Ricci diagonalization.

**Where:** `DimensionThree/RiemannFromRicci3D.lean`.
**Current producer:** `riemannFromRicci3DTraceEigenframePackage_of_real_trace_inner_product`
builds the trace/eigenframe package from the standard finite-dimensional real
trace, `met.g = inner`, metric compatibility, torsion-freeness, and
`Module.finrank ℝ E = 3`.
`hamiltonP2RiemannFromRicci3DTheorem_of_real_trace_inner_product` lifts this
to the Hamilton-level P2 typeclass for `RicciFlowData ℝ ℝ E Time A`.

**Effort:** M1 now has the standard real metric bridge
`realInnerProductMetricDuality_g_eq_inner` in
`Synthetic/Realization/Metric.lean`; the remaining realization work is not a
semantic choice of what `V` means. `V` is the tangent module in the realization.
The work is to bridge the pointwise finite-dimensional tangent-fiber algebra
back to the module-level tensor identity, or to use the tangent-section
realization hooks below.

#### B2.1.1 — `RiemannFromRicci3DTraceEigenframePackage` DONE as API

This is the preferred P2 package. It bundles the orthonormal trace formula,
metric/torsion side conditions, a coherent half coefficient, Ricci symmetry, a
Ricci eigenframe, and the off-diagonal Ricci trace equations.
`riemannFromRicci3DFinThreeComponentPackage_of_trace_eigenframe_package`
derives the six residual components, and
`hamiltonP2RiemannFromRicci3DTheorem_of_trace_eigenframe_packages` lifts a
slice-level package family to the Hamilton-level P2 typeclass.

#### B2.2 — `RiemannFromRicci3DFinThreeComponentPackage` DONE as API
The package and constructors are present. In particular,
`riemannFromRicci3DFinThreeComponentPackage_of_eigenframe` fills all six
residual fields from prebuilt sectional and mixed packages, while the newer
trace/eigenframe package builds those sectional and mixed packages internally.
The real finite-dimensional standard-trace model fills these fields via
`riemannFromRicci3DTraceEigenframePackage_of_real_trace_inner_product`.

---

### B3. `HamiltonP3CubicReactionGeometryTheorem` 🟢
**Math:** Hamilton's cubic reaction relation in dim 3:
```
2R · reaction(t) = 2|Ric|²(t)² − Q(t)
```
where `Q` is Hamilton's cubic in the eigenvalues of Ric.
**Lean target:** `HamiltonThreeManifold.lean:914`.
**Status:** typeclass declared with parameterized `IsGeometricReactionData`,
Hamilton-level builder ✅, per-slice eigenframe calculus ✅ for the canonical
finite-frame reaction scalar. Caller obligation only when the reaction is not
the canonical eigenframe contraction.

#### B3.1 — Per-slice `HasRicciReactionContractionCalculus` ✅ for the canonical eigenframe reaction
The per-slice calculus is now built directly from a P2 trace/eigenframe
package by
`hasRicciReactionContractionCalculus_of_trace_eigenframe_package`
(`DimensionThree/RicciReaction.lean:974`). The geometric-reaction predicate it
exposes is the equation
```
reaction = ricciEigenframeRiemannReaction3D emb conn … pkg.diagonalization
```
i.e., the Ricci-eigenframe finite-frame contraction associated to the P2
diagonalization. The supporting structure is:

* `ricciEigenframeRiemannReaction3D` (`DimensionThree/RicciReaction.lean:540`)
  — the canonical eigenframe scalar.
* `ricciEigenframeRiemannReaction3D_eq_ricciEigenRiemannReaction3_of_sectional_trace`
  (`DimensionThree/RicciReaction.lean:555`) — identifies it with
  `ricciEigenRiemannReaction3 λ₁ λ₂ λ₃`.
* `ricciReactionEigenvalueRealization_of_trace_eigenframe_package`
  (`DimensionThree/RicciReaction.lean:733`) — produces the eigenvalue
  realization predicate from the P2 package.
* `ricciReactionEigenvaluePackage_of_eigenvalue_realization`
  (`DimensionThree/RicciReaction.lean:322`) — produces the structure
  `RicciReactionEigenvaluePackage` from the realization predicate.

**Caller obligation.** `RicciReactionEigenvaluePackage` is a structure, not a
theorem, and the constructors above produce it specifically for the canonical
eigenframe scalar
`ricciEigenframeRiemannReaction3D … pkg.diagonalization`. For an arbitrary
caller-chosen `reaction : R`, the only outstanding equality is
```
reaction = ricciEigenframeRiemannReaction3D emb conn … pkg.diagonalization
```
which the caller either discharges directly or avoids by choosing the
canonical eigenframe contraction as the reaction scalar. There is no
remaining pure-synthetic calculation beyond the trace/eigenframe package
needed for P2.

#### B3.2 — Hamilton-level builder ✅
`hamiltonP3CubicReactionGeometryTheorem_of_reaction_calculus`
(`HamiltonThreeManifold.lean:936`) lifts the per-slice calculus to the global
Section 12 typeclass. `HamiltonP3ReactionCalculusInputs`
(`HamiltonThreeManifold.lean:969`) is the final-input bundle, with a
low-priority instance
`hamiltonP3CubicReactionGeometryTheorem_of_reaction_calculus_inputs`
feeding the synthesized P3 witness to the final theorem.

---

## C. Builder field obligations

[`HamiltonSection12ClaimBuilderInput`](HamiltonThreeManifold.lean#L842)
collects ~15 fields the realization must supply. Most are caller choices
(metrics, diffeomorphism witnesses), but a few have synthetic content.

### C1. `limit_dimensionThree_from_input` 🟡
**Math:** `IsDimensionThree input.atr ⟹ IsDimensionThree (CGH-limit).atr`.
**Status:** caller-supplied; could be a synthetic preservation lemma if the
abstract trace dimension is preserved by the limit construction.
**Where:** `HamiltonThreeManifold.lean:878`.

### C2. `limit_tracefree_norm_zero_from_p3` 🟡
**Math:** Routes through `limit_tracefree_norm_zero_from_improved_pinching`.
Needs an improved-pinching subsolution + decay-to-zero on the rescaled
sequence. **This is the P4 obligation below.**

### C3. `constant_positive_from_p1_p2` 🟡
**Math:** Routes through `limit_constant_positive_from_einstein` consuming
`[P1]` and `[P2]`. Once B1, B2 are done, this field is essentially free.

### C4. `limit_compact_from_constant_positive` ❌
**Math:** Myers compactness theorem on the limit manifold. Analytic.
Realization layer uses `MyersPositiveRicciCompactness`.

### C5. `compact_limit_diffeomorphism` (and `_matches`) ❌
**Math:** Cheeger finiteness / topological diffeomorphism of CGH limits.
Analytic. Realization via `CompactLimitDiffeomorphismUnderSmoothCGH`.

### C6. `original_limit_diffeomorphism` (and `_to_limit`) ❌
**Math:** CGH-inverse: original manifold is diffeomorphic to the limit.
Realization choice; depends on the concrete CGH machinery.

---

## D. P4 — Improved pinching producer (auxiliary)

Not in the typeclass triple, but flows into the builder via
`limit_tracefree_norm_zero_from_improved_pinching`.

### D1. Quotient evolution ❌
**Math:** Evolution equation for `P = |Ric⁰|² / R^(2−ε)` along Ricci flow.
Mixed PDE/algebraic content.
**Where:** `Evolution/RicciNorm.lean` extension. The eventual output should
instantiate `HamiltonPinchingAdjustedEvolutionData`: first prove the bare
Lemma 10.6 equation, then prove the drift-adjusted heat identity that moves
the drift and nonpositive gradient-square terms into the maximum-principle
operator. `hamilton_improved_pinching_producer_data_of_adjusted_pinching_evolution`
then produces `HamiltonImprovedPinchingProducerData`.

Current direct route:

- `hamiltonPinchingEvolutionEquation_of_quotient_identity` proves Lemma 10.6
  from `QuotientEvolutionIdentity`, the trace-free norm heat equation, scalar
  heat equation, coefficient identities, and the gradient-square completion.
- `hamiltonPinchingAdjustedEvolutionData_of_quotient_identity` packages that
  calculation into the adjusted-evolution data. No new quotient interface is
  needed for this step.

### D2. Shifted subsolution proof ✅ as producer algebra
**Math:** `P` (suitably shifted) is a subsolution once the quotient evolution
has reaction
```
weight · (ε |Ric|² |Ric⁰|² − Q)
```
with `weight ≥ 0`, `ε ≤ 2δ²`, and Hamilton's `Q` lower bound.
**Lean:** `DimensionThree/ImprovedPinching.lean` now has
`HamiltonImprovedPinchingProducerData`,
`HamiltonPinchingAdjustedEvolutionData`,
`hamiltonPinchingAdjustedEvolutionData_of_quotient_identity`,
`hamilton_improved_pinching_shifted_subsolution`, and
`improved_ricci_pinching_estimate_along_flow_of_hamilton_producer`.
The remaining work is to instantiate the producer from the actual quotient
evolution and preserved pinching cone.

### D3. Strict-positive-Ricci ⟹ uniform pinching ❌
**Math:** Initial Ric > 0 implies a uniform `|Ric⁰|² ≤ C R²` along the flow.

### D4. Decay-to-zero on rescaled sequence ❌
**Math:** On the parabolically rescaled subsequence, `P(rescaled, t) → 0`
in a uniform sense. Analytic content.

---

## D5. P3.3 complete; full P3/P4 proof structure after the book-reference pass

P3.3, the cubic-reaction geometry, is now complete at the
synthetic/eigenframe wrapper boundary. The full trace-free Ricci norm
evolution still needs the Ricci-norm and scalar heat components supplied to
`Evolution/RicciNorm.lean`. This section records the completed cubic-reaction
route and the remaining full-P3/P4 route. It keeps the
Chow-Knopf/Hamilton equations as references but preserves the current Lean
convention:

```text
Rm_lowered(X,Y,Z,W) = g(Rm(X,Y)Z,W)
Rc(X,Z) = tr (fun Y => Rm(X,Y)Z)
partial_t g = -2 Rc
```

### P3.3 cubic reaction and full trace-free Ricci norm evolution

Target equation:

```text
(partial_t - Delta)|Ric^0|^2
  = -2|nabla Ric|^2 + (2/3)|nabla R|^2
    + (4|Ric|^2|Ric^0|^2 - 2Q)/R.
```

Proof route:

1. Use P2 to work in an orthonormal Ricci eigenframe.
2. Identify the geometric reaction contraction with
   `ricciEigenRiemannReaction3`.
3. Apply `ricciEigenRiemannReaction3_cubicQ_relation`.
4. Feed the resulting contraction identity into
   `hamilton3D_tracefree_norm_rhs_of_cubic_reaction`.
5. Package the cubic-reaction result as
   `HamiltonP3CubicReactionGeometryTheorem`.

New Lean abstraction:

- `DimensionThree/RicciReaction.lean` now has
  `RicciReactionEigenvaluePackage`,
  `IsRicciReactionEigenvalueGeometric`,
  `ricciEigenframeRiemannReaction3D`,
  `ricciEigenframeRiemannReaction3D_eq_ricciEigenRiemannReaction3_of_sectional_trace`,
  `ricciReactionEigenvalueRealization_of_trace_eigenframe_package`,
  `ricciReactionEigenvaluePackage_of_eigenvalue_realization`,
  `hasRicciReactionContractionCalculus_of_eigenvalue_packages`, and
  `hasRicciReactionContractionCalculus_of_trace_eigenframe_package`.

P3.3 coordinate/eigenframe work owed: DONE for the canonical
eigenframe reaction scalar. The frame expansion of the geometric
`Rm · Ric · Ric` contraction, the eigenvalue identification with
`ricciEigenRiemannReaction3 λ₁ λ₂ λ₃`, and the
scalar/`|Ric|²`/`Q` equalities are all produced from a P2 trace/eigenframe
package. The only obligation that remains for callers is the equality
`reaction = ricciEigenframeRiemannReaction3D emb conn … pkg.diagonalization`
when the chosen reaction scalar is not the canonical finite-eigenframe
contraction itself.

Full trace-free norm evolution owed: callers still have to provide the heat
components consumed by `hamilton3D_tracefree_norm_rhs_of_cubic_reaction` and
`hamilton3D_tracefree_norm_eq_of_cubic_reaction_components`:

- `h_ricciNorm_heat`, the Ricci norm heat component
  `ricciNormDt - ricciNormLap = -2 * |nabla Ric|^2 + 4 * reaction`;
- `h_scalar_heat`, the scalar heat component
  `scalarDt - scalarLap = 2 * |Ric|^2`;
- the binding between that chosen `reaction` and the canonical finite
  eigenframe reaction scalar produced by the P3.3 theorem.

### P4. Improved pinching producer

Target output:

```text
|Ric^0|^2 / R^2 <= C * R^(-epsilon)
```

Proof route:

1. Use the P3 trace-free norm evolution and scalar evolution to derive the
   quotient evolution for `P = |Ric^0|^2 / R^(2 - epsilon)`.
2. Complete the gradient square terms so the heat operator has reaction
   weight times `epsilon * |Ric|^2 * |Ric^0|^2 - Q`.
3. Use the Lemma 10.8 lower bound on `Q` and `epsilon <= 2 delta^2`.
4. Apply the scalar weak maximum-principle consumer already in
   `ImprovedPinching.lean`.
5. Use quotient algebra to rewrite the scale-invariant ratio as
   `P * decay`.
6. Let the compactness/rescaling layer supply decay-to-zero.

New Lean abstraction:

- `DimensionThree/ImprovedPinching.lean` now has
  `hamiltonImprovedPinchingQuantity`,
  `hamiltonImprovedPinchingQuantityFromRicci`,
  `quotientEvolutionRHS`,
  `QuotientEvolutionIdentity`,
  `hamiltonPinchingEvolutionRHS`,
  `HamiltonPinchingEvolutionEquation`,
  `HamiltonPinchingQuotientEvolutionData`,
  `shifted_heat_eq_reaction_of_quotient_evolution`,
  `hamilton_improved_pinching_producer_data_of_quotient_evolution`,
  `HamiltonPinchingQuotientRealizationData`,
  `pinching_ratio_eq_P_mul_decay_of_denominator_decay`, and
  `ratio_decay_relation_of_quotient_realization`.
- `Global/Compactness.lean` now has
  `limit_tracefree_norm_zero_from_hamilton_improved_pinching_producer`, the
  direct consumer from `HamiltonImprovedPinchingProducerData` to the Section 12
  trace-free-limit vanishing conclusion.

Coordinate/analysis work still owed:

- exponent identity for the chosen positive-scalar power API:
  `R^(-epsilon) = R^(2 - epsilon) / R^2`;
- concrete quotient evolution and gradient-square completion for `P`;
- uniform pinching from preserved positive Ricci;
- decay-to-zero on the selected parabolic rescaling sequence.

---

## E. Section 12 wrapper (synthetic core, mostly done)

These are not new obligations — they are existing theorem chains that
become *real* once B1–B3 are filled. Listed so callers know the entry
points.

| Theorem | Status | Notes |
|---|---|---|
| `hamilton_three_manifold_from_typed_input` | ✅ structurally complete | Closes once A, B, C, D are filled. |
| `section12_claims_from_typed_input` | ✅ | Builds claims from typed input + 9 analytic + 3 P-typeclasses + builder. |
| `hamilton_section12_assembly_from_claims` | ✅ | Assembles the full certificate. |
| `hamilton_three_manifold_from_section12_claims` | ✅ | Convenience entry point for collaborators. |
| `hamilton_three_manifold_typeclass_smoke` | ✅ | End-to-end smoke test using stub instances. |

---

## F. Realization-layer obligations (concrete coordinate work)

These are the concrete instances/expansions that turn the synthetic
typeclasses into actual instances at `concreteAbstractTrace` /
`concreteMetricDuality` / Levi-Civita. Required to execute B1–B3.

### F1. Concrete trace API ✅ mostly done
- `concreteAbstractTrace I M` — exists.
- `concreteHasTensorContractFubini` — ✅.
- `concreteHasContractedBianchiDivMetricTraceFubini` — ✅.
- `concreteHasTensorContractSwapNaturality` — ✅ (in
  `Realization/TensorContractSwapNaturality.lean`).
- 4-index unfolds: `concreteContractedBianchiDivPattern_apply_unfold`,
  `_apply_cycle_left_unfold`, `concreteContractedBianchiGradPattern_apply_unfold`
  — ✅.

### F2. Concrete `HasMetricAdjointTraceInvariant` DONE
See B1.3.

### F3. Concrete cycle-side identifications for `loweredCovDerivRmTensor` DONE
The concrete slot-audit package in `Realization/MetricTraceFubini.lean`
provides the cyclic trace audit for the named patterns. This is no longer the
blocking part of P1.

### F4. Concrete bridge for `divPattern_apply_eq_ricciDivergence` PARTIAL
The plan flags two precise bridges:
- Identify the concrete 4-index pattern with the trace of the swapped-Ricci
  divergence endomorphism. DONE.
- Use `HasMetricAdjointTraceInvariant` (F2) to swap from
  `ricciDivergenceAtSecond` to `ricciDivergenceAt`. DONE for
  `concreteAbstractTrace`.

### F5. Concrete bridge for `gradPattern_apply_eq_neg_grad_R` DONE for concrete trace
The concrete 4-index pattern has been identified with the trace of
`∇ Ric♯`. The final `-dR` form consumes `NablaTrComm`; the concrete wrapper
`concreteConn_NablaTrComm` now supplies this for `concreteAbstractTrace` and
`concreteConn`.

### F6. Concrete `HasRiemannFromRicci3DCalculus` for Levi-Civita 🟡
Pointwise 3D algebraic curvature decomposition in an orthonormal frame.
The synthetic/finite-dimensional real route is complete; the remaining work is
to bridge that pointwise tangent-fiber algebra into the concrete tangent
module used by `RicciFlowData`.

Current P2 trace status: `Realization/OrthonormalTrace.lean` proves the
global-section trace formula
`concreteOrthonormalBasisTraceFormula3`. A synthetic `Fin 3` orthonormal basis
of smooth tangent sections is evaluated to a pointwise fiber basis, and
`concreteAbstractTrace.tr` is identified with the corresponding sum of diagonal
metric pairings. The constructor
`concreteHasOrthonormalBasisTraceFormula3` is now unconditional.

For finite-dimensional real slices, the newer
`riemannFromRicci3DTraceEigenframePackage_of_real_trace_inner_product` and
`hamiltonP2RiemannFromRicci3DTheorem_of_real_trace_inner_product` avoid the
tangent-section trace problem entirely at a point: supply
`atr.tr = LinearMap.trace`, `met.g = inner`, `finrank = 3`, metric
compatibility, and torsion-freeness, then bridge the resulting pointwise tensor
identity back to the tangent-module statement.

### F7. Concrete `HasRicciReactionContractionCalculus` ✅ for the canonical eigenframe reaction
The synthetic P3 calculus is now produced directly from a P2 trace/eigenframe
package by `hasRicciReactionContractionCalculus_of_trace_eigenframe_package`,
with the geometric reaction predicate set to
`reaction = ricciEigenframeRiemannReaction3D … pkg.diagonalization`. The
concrete realization therefore inherits a P3 instance for free once it
supplies a P2 trace/eigenframe package on each slice.

The only remaining concrete obligation is the same one as for F6: bridging
between pointwise tangent-fiber data and the tangent-module statement so that
the trace/eigenframe package is available for `RicciFlowData ℝ ℝ E Time A`.
For arbitrary caller-chosen reaction scalars, the caller additionally has to
supply the equality with the canonical eigenframe contraction; choosing
`ricciEigenframeRiemannReaction3D … pkg.diagonalization` itself avoids that
equality entirely.

---

## G. Recommended order of attack

The previous P1-P2 and P3.3 attack list is complete at the synthetic wrapper
boundary:

1. **P1** — DONE. The concrete named-pattern package in
   `Realization/MetricTraceFubini.lean` produces
   `HasContractedSecondBianchiNamedPatternCalculus`, and
   `hamiltonP1ContractedSecondBianchiTheorem_of_named_calculus` lifts it to
   `HamiltonP1ContractedSecondBianchiTheorem`.

2. **P2** — DONE for the real finite-dimensional model and for the
   trace/eigenframe package route. The load-bearing entry points are
   `riemannFromRicci3DTraceEigenframePackage_of_real_trace_inner_product`,
   `concreteHasOrthonormalBasisTraceFormula3`, and
   `hamiltonP2RiemannFromRicci3DTheorem_of_real_trace_inner_product`.

3. **P3.3 cubic reaction geometry** — DONE for the canonical eigenframe
   reaction scalar. The load-bearing
   entry points are
   `hasRicciReactionContractionCalculus_of_trace_eigenframe_package`,
   `hamiltonP3CubicReactionGeometryTheorem_of_trace_eigenframe_packages`, and
   `hamiltonP3CubicReactionGeometryTheorem_of_eigenvalue_packages`. If a caller
   chooses a different concrete reaction scalar, they only owe the equality
   with `ricciEigenframeRiemannReaction3D ... pkg.diagonalization`.

   Full P3, meaning the trace-free Ricci norm evolution identity used by
   improved pinching, still needs the Ricci norm heat component, scalar heat
   component, and reaction binding described in D5.

Next work should start at:

4. **D1-D4** — improved-pinching producer. The quotient-evolution handoff
   object and direct compactness consumer now exist. This is still blocked by
   the concrete quotient evolution, denominator/positivity side conditions,
   gradient-square completion, and the analytic weak maximum principle, not by
   P1, P2, or P3.3 cubic-reaction geometry.

5. **A1-A10** — collaborator territory. Listed for completeness; not blocking
   our work because they are typeclass arguments to the final theorem.

6. **C1, C4-C6** — remaining builder fields. Caller / realization decisions
   interleaved with A1-A10.

After P4 and the analytic/builder fields are supplied, the Hamilton
three-manifold theorem reduces to:

```
A1-A10 (PDE)  +  C4-C6 (concrete realization choices)
```

i.e., the synthetic side is fully complete and Section 12 is closed up to
the analytic gaps and realization plumbing.

---

## H. What's already proved in the synthetic core

For orientation — these are the load-bearing synthetic theorems that B1–B3
build on. None of them are obligations; they are tools.

- `Synthetic/Algebra/TensorAlgebra.lean`:
  - `tensor_prod`, `swap_covariant`, `swap_contravariant`, `contract_general`,
    `tensor_contract_twice`, evaluation rules.
  - `HasTensorContractFubini`, `HasTensorContractSwapNaturality` (theorem
    forms).
  - `NablaTrComm`, `TimeTrComm`.
- `Synthetic/Algebra/Metric.lean`:
  - `MetricDuality.{flat, sharp, g_symm, g_inv_symm}`, `IsMetricCompatible`,
    `nabla_g_zero`, `nabla_g_inv_zero`, `nabla_metric_trace_comm`.
  - `HasMetricAdjointTraceInvariant` (typeclass).
- `Synthetic/Algebra/MetricTrace.lean`:
  - `doubleMetricTrace04`, `doubleMetricTrace05`,
    `DoubleMetricTrace05Pattern` (with `contractedBianchiDivPattern`,
    `divFubiniPattern`, `gradPattern`).
  - `HasDoubleMetricTrace05PatternFubini`, `apply_*`/`tensor_*` linearity.
- `Synthetic/Geometry/CurvatureContractions.lean`:
  - All Rm symmetries lifted to (0,4) and (0,5) tensor levels:
    `loweredRmTensor_{antisymm_first_pair, antisymm_second_pair, block_symm,
    first_bianchi}`, `covDerivRmLoweredTensor_{antisymm_first_pair,
    antisymm_second_pair, first_bianchi, cyclic_sum_tensor}`.
  - `covariantCycle012Left05`, `covariantCycle012Right05` and their
    eval lemmas.
- `Synthetic/Flow/RicciFlow/DimensionThree/CurvatureAlgebra.lean`:
  - `ContractedSecondBianchiIdentity`, `RiemannFromRicci3DFormula`,
    `riemannFromRicci3DRHS`, `IsHalfCoefficient`,
    `ricciDivergenceAt(Second)`, `grad_R`, `ScalarCurvature`,
    `ricciForm_tensor`, plus all four entry-point theorems for P1.
- `Synthetic/Realization/MetricTraceFubini.lean`:
  - 4-index unfolds for `divPattern`, `divFubiniPattern`, `gradPattern`,
    `cycle_left`, `cycle_right`. Plus the `_eq_gradPattern` slot equality
    for arbitrary T.

---

## I. File map

```
DifferentialGeometry/Synthetic/Flow/RicciFlow/
├── HamiltonThreeManifold.lean                  ← top-level theorem + bundle
├── FORMALIZATION_PLAN.md                       ← design intent / source map
├── OBLIGATIONS.md                              ← THIS FILE
├── DimensionThree/
│   ├── CurvatureAlgebra.lean                   ← P1 contracted Bianchi machinery
│   ├── RiemannFromRicci3D.lean                 ← P2 packages + theorem route
│   ├── RicciReaction.lean                      ← P3 reaction packages + theorem route
│   ├── SlotAuditFromNaturality.lean            ← P1 obligations bridge
│   ├── Pinching.lean                           ← Hamilton cubic Q algebra
│   └── ImprovedPinching.lean                   ← P4 ratio bound consumer
├── Evolution/
│   ├── RiemannEvolution.lean
│   ├── Ricci.lean / RicciNorm.lean
│   └── ScalarCurvature.lean
├── Global/
│   ├── BlowUp.lean                             ← A1, A3, A4, A5
│   ├── Compactness.lean                        ← A6, A7, A8, A9
│   └── Existence.lean                          ← short-time existence iface
└── HamiltonThreeManifoldSmoke.lean             ← end-to-end smoke test

DifferentialGeometry/Synthetic/Realization/
├── TensorContract.lean                         ← concreteAbstractTrace
├── MetricTraceFubini.lean                      ← F1 unfolds + Fubini
├── TensorContractSwapNaturality.lean           ← swap-naturality concrete instance
├── Trace.lean                                  ← F2 (HasMetricAdjointTraceInvariant) target
└── LeviCivita.lean                             ← Levi-Civita realization

ForMathlib/Geometry/Manifold/VectorBundle/
└── OrthonormalFrame.lean                       ← B2.1 / F6 foundation
```

---

## J. Last update

This document reflects the source tree state after the P3.3 eigenframe-reaction
producers landed in `DimensionThree/RicciReaction.lean`:
`ricciEigenframeRiemannReaction3D`,
`ricciReactionEigenvalueRealization_of_trace_eigenframe_package`,
`ricciReactionEigenvaluePackage_of_eigenvalue_realization`, and
`hasRicciReactionContractionCalculus_of_trace_eigenframe_package`. Combined
with the unconditional concrete trace formula
`concreteOrthonormalBasisTraceFormula3` in
`Realization/OrthonormalTrace.lean`, P2 and the P3.3 cubic-reaction geometry
are both done at the synthetic core for the canonical eigenframe reaction.
Full trace-free norm evolution still requires the heat-component inputs
recorded in D5; only F6/F7 realization plumbing and (for non-canonical
reactions) the caller-supplied
`reaction = ricciEigenframeRiemannReaction3D ...` equality remain for the
cubic-reaction layer.
Update when any of A1–A10, B1–B3, C1–C6, D1–D4, F1–F7 changes status.
