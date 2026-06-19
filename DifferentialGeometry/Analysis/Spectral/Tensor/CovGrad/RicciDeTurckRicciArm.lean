import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RicciDeTurckSectionDifference
import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.TensorHsRealize
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.RicciConnDiffPalatini
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciDifferenceMeanValue
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RicciDeTurckMetricArmCoeffField
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.SmoothParametricCoeffIntegral
import DifferentialGeometry.Analysis.Parabolic.DeTurckRicci.RHSStrictParabolic

/-!
# The Ricci-tensor difference of two realized metrics: the Palatini telescope and its `appCc` grading

For a closed smooth Riemannian manifold `(M, g₀)`, two endpoint metrics `g₁, g₁'`, and fibre vectors
`v, w ∈ T_x M`, this file records the eval-level reduction of the **Ricci-arm difference**
`Ric(g₁) − Ric(g₁')` to the intrinsic Palatini (connection-difference) telescope, and the order-graded
`appCc` decomposition of the realized `(−2)`-scaled Ricci-arm difference that the Ricci–DeTurck
linearization consumes (the parallel of `deTurckLieArm_appCc_graded` for the Lie arm).

The two metrics are compared to the common base `g₀`: writing `A₁ = connDiff g₁ g₀` and
`A₁' = connDiff g₁' g₀` for the two connection-difference tensors, the intrinsic Palatini identity
`ricciTensor_sub_eq_connDiff_palatini` expresses `Ric(g₁) − Ric(g₀)` and `Ric(g₁') − Ric(g₀)` each as a
`chartModelBasis`-trace of the divergence-type `(∇₀ A)` term (`covDerivConnDiff`) and the quadratic
`A ∧ A` contraction.  Subtracting collapses the common `Ric(g₀)` base, leaving the difference of the
two Palatini traces — the `connDiff`-native, chart-jet-free core that the Ricci–DeTurck right-hand-side
linearization expands by `∂`-order of the section difference (`ricciTensor_sub_eq_palatini_telescope`).

## The order-graded `appCc` decomposition (the Ricci arm)

`deTurckRicciArm_appCc_graded` is the eval-level grading node: there exist endpoint-dependent operator
coefficient fields
```
R₀ : SmoothCcTensor g₀ 2 2,   R₁ : SmoothCcTensor g₀ 3 2,   R₂ : SmoothCcTensor g₀ 4 2,
```
such that the `(−2)`-scaled Ricci-arm difference value is, at every base point and on every tangent
pair, the `unitModel` read-off of the order-graded operator-field action on the iterated covariant
gradients `Wₘ = iteratedCovGrad g₀ 0 2 m (T − T')` of the perturbation difference:
```
(−2)·(Ric(g₁) − Ric(g₁'))(v 0, v 1)
  = unitModel g₀ 2 (appCc g₀ 2 2 R₀ W₀ + appCc g₀ 3 2 R₁ W₁ + appCc g₀ 4 2 R₂ W₂) x v,
  g₁ = realize(g₀ + T),  g₁' = realize(g₀ + T').
```
This is stated so the `−2·Ric + 𝓛` leaf-identity glue of the Lichnerowicz `_core` sums it cleanly with
the Lie-arm grading `deTurckLieArm_appCc_graded` (same realize-tie hypotheses, same `unitModel`/`appCc`
shape, same `Wₘ`); adding the two graded triples reproduces the Ricci–DeTurck right-hand-side difference
`deTurckRicciRHS g_bg g₁ − deTurckRicciRHS g_bg g₁' = −2(Ric(g₁) − Ric(g₁')) + (𝓛_{W} g₁ − 𝓛_{W} g₁')`.

## The classical reduction (order by order) and the posited eval-matching residual

The Palatini telescope `ricciTensor_sub_eq_palatini_telescope` reduces the value to the
`chartModelBasis`-trace of the differentiated connection-difference `covDerivConnDiff`, whose two-endpoint
order grading `covDerivConnDiff_diff_endpoint_graded` (`RicciDeTurckSectionDifference`) splits it into:

* the **order-`2` PRINCIPAL** `♯_{g₁}(∇^{g₁}_X (K_{g₁} − K_{g₁'}))`, whose covector difference is the
  Koszul covector of the section difference `S = T − T'` (the inverse-Gram raise
  `connDiff_eq_appCc_invGram_covGrad`).  Through the cotangent/`(0,1)`-tensor connector
  `cotangentCov_eq_tensorCovDerivAt_ccTensor01` and the metric-compat parallelism of the cometric raise
  (`inverseMetricSharpField_covGrad_eq_zero`), the principal reads as the second covariant gradient
  `W₂ = ∇₀²(T − T')` contracted by the canonical `g₁`-cometric double-trace field; the coefficient field
  is `R₂ = cometricTraceFieldG₀Tag g₀ g₁ 2`;
* the **order-`1`** cross/slot `connDiff` couplings (the `δΓ` terms `A_{g₁}(♯K, X)`, `A_{g₁}(Y, ∇₀_X Z)`,
  `A_{g₁}(∇₀_X Y, Z)` and their endpoint differences), each a fibre operator (built from
  `g₁⁻¹`/`∇g₁⁻¹`/the Christoffel difference) applied to `W₁ = ∇₀(T − T')`, packaged into `R₁`;
* the **order-`0`** operator-difference arm `♯_{g₁}∇^{g₁} − ♯_{g₁'}∇^{g₁'}` on the endpoint development
  (the inverse-metric-difference multiplier `gInvDiffRaisedEndo_eq_metricSharp_flatDiff` plus the
  endpoint curvature), a fibre operator applied to `W₀ = T − T'`, packaged into `R₀`.

The *order grading* is genuine classical content (the Palatini telescope + the on-disk two-endpoint
graded differentiated connection difference + the inverse-Gram raise).  The **exact endpoint operator
fields `R₀, R₁, R₂`** and the eval-matching identity are the deep mean-value/Leibniz content of the
linearization: producing them requires repackaging the `chartModelBasis`-trace of the `g₁`-connection
telescope (in `inverseMetricSharpFib`/`cotangentCov (LeviCivita g₁)`/`koszulCovGradCovec` form) into the
`g₀`-iterated-covariant-gradient `appCc` form — the Palatini-trace ↔ `appCc`/`unitModel` bridge and the
`∇^{g₁} ↔ ∇₀` conversion that are not yet on disk.  This is exactly the "deep mean-value content posited
downstream" that the sibling Lie arm `deTurckLieArm_appCc_graded` and the curvature/metric arm
coefficient fields (`ricBackgroundArmCoeffField`, `gInvDiffMetricArmCoeffField`) likewise posit at the
eval-matching level; it is stated here as the genuine existential grading node, to be discharged by
recursing into those missing covariant bridges.  Its predicate genuinely constrains `(R₀, R₁, R₂)` to
*reproduce the actual `(−2)`-scaled Ricci-arm difference value*, so it is non-vacuous — the zero triple
does not satisfy it on any background where the Ricci arm is nonzero.
-/

noncomputable section

set_option linter.style.setOption false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open Bundle Manifold Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators Matrix

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.DeTurck
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.PDE.DeTurck.RicciLinearization
open DifferentialGeometry.PDE.DeTurck.DeTurckLinearization
open DifferentialGeometry.Integral.DivergenceTheorem

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

/-! ## The Palatini telescope of the Ricci-tensor difference -/

omit [CompactSpace M] [I.Boundaryless] in
/-- **The Ricci-tensor difference of two metrics as the difference of their Palatini traces.**

For two metrics `g₁, g₁'` compared to a common base `g₀`, the difference of their Ricci tensors at `x`
is the difference of the two intrinsic Palatini traces (the `chartModelBasis`-trace of the
divergence-type `covDerivConnDiff` term plus the quadratic `connDiff ∧ connDiff` contraction), with the
common base curvature `Ric(g₀)` cancelled.

This is the on-disk Palatini identity `ricciTensor_sub_eq_connDiff_palatini` applied at `g₁` and at
`g₁'`, subtracted: `Ric(g₁) − Ric(g₁') = (Ric(g₁) − Ric(g₀)) − (Ric(g₁') − Ric(g₀))`.  It is the
intrinsic, chart-jet-free reduction the Ricci-arm linearization expands by `∂`-order of the section
difference. -/
theorem ricciTensor_sub_eq_palatini_telescope
    (g₀ g₁ g₁' : SmoothRiemannianMetric I M) (x : M) (v w : TangentSpace I x) :
    ricciTensor (I := I) g₁ x v w - ricciTensor (I := I) g₁' x v w =
      (∑ i : Fin (Module.finrank ℝ E),
        (chartModelBasis E).repr
          ((covDerivConnDiff (I := I) g₀ g₁
                (smoothExtensionTangent (I := I) x ((chartModelBasis E) i))
                (smoothExtensionTangent (I := I) x v)
                (smoothExtensionTangent (I := I) x w) x
              - covDerivConnDiff (I := I) g₀ g₁
                (smoothExtensionTangent (I := I) x v)
                (smoothExtensionTangent (I := I) x ((chartModelBasis E) i))
                (smoothExtensionTangent (I := I) x w) x)
            + (connDiff (I := I) g₁ g₀ x
                  (diffSec (LeviCivita (I := I) g₀) (LeviCivita (I := I) g₁)
                    (smoothExtensionTangent (I := I) x v)
                    (smoothExtensionTangent (I := I) x w) x)
                  (smoothExtensionTangent (I := I) x ((chartModelBasis E) i) x)
                - connDiff (I := I) g₁ g₀ x
                  (diffSec (LeviCivita (I := I) g₀) (LeviCivita (I := I) g₁)
                    (smoothExtensionTangent (I := I) x ((chartModelBasis E) i))
                    (smoothExtensionTangent (I := I) x w) x)
                  (smoothExtensionTangent (I := I) x v x))) i)
        - (∑ i : Fin (Module.finrank ℝ E),
        (chartModelBasis E).repr
          ((covDerivConnDiff (I := I) g₀ g₁'
                (smoothExtensionTangent (I := I) x ((chartModelBasis E) i))
                (smoothExtensionTangent (I := I) x v)
                (smoothExtensionTangent (I := I) x w) x
              - covDerivConnDiff (I := I) g₀ g₁'
                (smoothExtensionTangent (I := I) x v)
                (smoothExtensionTangent (I := I) x ((chartModelBasis E) i))
                (smoothExtensionTangent (I := I) x w) x)
            + (connDiff (I := I) g₁' g₀ x
                  (diffSec (LeviCivita (I := I) g₀) (LeviCivita (I := I) g₁')
                    (smoothExtensionTangent (I := I) x v)
                    (smoothExtensionTangent (I := I) x w) x)
                  (smoothExtensionTangent (I := I) x ((chartModelBasis E) i) x)
                - connDiff (I := I) g₁' g₀ x
                  (diffSec (LeviCivita (I := I) g₀) (LeviCivita (I := I) g₁')
                    (smoothExtensionTangent (I := I) x ((chartModelBasis E) i))
                    (smoothExtensionTangent (I := I) x w) x)
                  (smoothExtensionTangent (I := I) x v x))) i) := by
  have h₁ := ricciTensor_sub_eq_connDiff_palatini (I := I) g₀ g₁ x v w
  have h₁' := ricciTensor_sub_eq_connDiff_palatini (I := I) g₀ g₁' x v w
  rw [show ricciTensor (I := I) g₁ x v w - ricciTensor (I := I) g₁' x v w =
      (ricciTensor (I := I) g₁ x v w - ricciTensor (I := I) g₀ x v w)
        - (ricciTensor (I := I) g₁' x v w - ricciTensor (I := I) g₀ x v w) from by ring]
  rw [h₁, h₁']

/-! ## Linearity of the unit read-off and the operator-field smul -/

/-- The unit read-off `unitModel` is additive in the `(0, s)`-tensor argument. -/
private lemma unitModel_add_left (g : SmoothRiemannianMetric I M) (s : ℕ)
    (W₁ W₂ : SmoothCcTensor g 0 s) (x : M) :
    unitModel (I := I) (M := M) g s (W₁ + W₂) x =
      unitModel (I := I) (M := M) g s W₁ x + unitModel (I := I) (M := M) g s W₂ x := by
  rw [unitModel, unitModel, unitModel]
  have hsec : (W₁ + W₂).toSection x = W₁.toSection x + W₂.toSection x := by
    rw [SmoothCcTensor.toSection_add]; rfl
  rw [show ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from (W₁ + W₂).toSection x)
        (unitTensor (I := I) (M := M) x)) =
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from W₁.toSection x)
          (unitTensor (I := I) (M := M) x) +
        (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from W₂.toSection x)
          (unitTensor (I := I) (M := M) x) from by
    rw [hsec]; rfl]
  rw [Tensor0SSpace.toModel_add]

/-- The unit read-off `unitModel` is `ℝ`-homogeneous in the `(0, s)`-tensor argument. -/
private lemma unitModel_smul_left (g : SmoothRiemannianMetric I M) (s : ℕ)
    (c : ℝ) (W : SmoothCcTensor g 0 s) (x : M) :
    unitModel (I := I) (M := M) g s (c • W) x =
      c • unitModel (I := I) (M := M) g s W x := by
  rw [unitModel, unitModel]
  have hsec : (c • W).toSection x = c • W.toSection x := by
    rw [SmoothCcTensor.toSection_smul]; rfl
  rw [show ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from (c • W).toSection x)
        (unitTensor (I := I) (M := M) x)) =
      c • (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from W.toSection x)
          (unitTensor (I := I) (M := M) x) from by
    rw [hsec]; rfl]
  rw [Tensor0SSpace.toModel_smul]

/-- The operator-field action is `ℝ`-homogeneous in the operator-field (coefficient) factor. -/
private lemma appCc_smul_left (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (c : ℝ) (Φ : SmoothCcTensor g r s) (W : SmoothCcTensor g 0 r) :
    appCc (I := I) (M := M) g r s (c • Φ) W =
      c • appCc (I := I) (M := M) g r s Φ W := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [show ((c • appCc (I := I) (M := M) g r s Φ W).toSection x) =
      c • (appCc (I := I) (M := M) g r s Φ W).toSection x from rfl]
  rw [appCc_toSection, appCc_toSection]
  rw [show ((c • Φ).toSection x : TensorRSSpace r s I x) = c • Φ.toSection x from by
    rw [SmoothCcTensor.toSection_smul]; rfl]
  rw [ContinuousLinearMap.smul_comp]

/-! ## The chart-level DeTurck gauge cancellation (general symmetric perturbation) -/

open DifferentialGeometry.PDE.DeTurck.RicciLinearization in
open DifferentialGeometry.PDE.DeTurck.DeTurckLinearization in
/-- **The chart-level DeTurck gauge cancellation (general perturbation).**

For any chart metric perturbation `h` (symmetric by construction, `ChartMetricPerturbation.symm`,
the form a metric-Gram velocity always takes), at a chart-interior point `y`, the combined principal
symbol of the Ricci–DeTurck operator — `(-2)·chartRicciSecondOrderPrincipalSymbol g α h +
chartDeTurckCorrPrincipalSymbolExpr g g' α h` — collapses to the **pure rough Laplacian**
`∑_{j,l} G^{jl}(y)·∂_j∂_l h_{ik}(y)`.

This is the general-`h` (chart-functional) analogue of the symbol-level gauge cancellation
`deTurckSymbol_apply_apply_eq_isotropic_of_symm`: there it is proved with the `∂_a∂_b ↦ ξ_aξ_b`
substitution, here it is proved directly on the explicit `∂²h` chart expressions.  The DeTurck
correction's outer `∑_k g_{kj}(y)·∑_l G^{kl}(y)·(…)` block contracts by the inverse-Gram identity
`∑_k g_{jk} G^{kl} = δ^l_j` (`chartGramMatrix_mul_chartInvGramMatrix`), and the residual
non-isotropic raised-divergence/trace-gradient terms of the bare Ricci symbol are exactly killed by
the corresponding DeTurck-correction terms once Schwarz symmetry
(`partialDeriv_partialDeriv_perturbation_swap`) and the symmetry of `h` (`ChartMetricPerturbation.symm`)
are used, leaving only the isotropic `G^{jl}∂_j∂_l h_{ik}` term.  (A dim-3/4 random-SPD numeric confirms
the identity is exact, and that it genuinely needs the symmetry of `h`.) -/
private theorem deTurckRicciChartPrincipalSymbol_eq_roughLaplacian
    (g g_bg : SmoothRiemannianMetric I M) (α : M) (h : ChartMetricPerturbation E)
    (i k : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ (extChartAt I α).target) :
    (-2 : ℝ) * chartRicciSecondOrderPrincipalSymbol (I := I) g α h i k y +
        chartDeTurckCorrPrincipalSymbolExpr (I := I) g g_bg α h i k y =
      ∑ j : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
        chartInvGramOnE (I := I) g α j l y *
          partialDeriv (E := E) j (partialDeriv (E := E) l (h i k)) y := by
  classical
  -- Abbreviations.  `D a b c d = ∂_a∂_b h_{cd}(y)`; `G`/`g'` the chart inverse-Gram / Gram entries.
  set D : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
      Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ :=
    fun a b c d => partialDeriv (E := E) a (partialDeriv (E := E) b (h c d)) y with hD
  set G : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ :=
    fun a b => chartInvGramOnE (I := I) g α a b y with hGdef
  set g' : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ :=
    fun a b => chartGramOnE (I := I) g α a b y with hg'def
  -- Schwarz symmetry of the iterated chart partial in the two differentiation indices.
  have hsw : ∀ a b c d, D a b c d = D b a c d := fun a b c d =>
    partialDeriv_partialDeriv_perturbation_swap h c d a b y
  -- Symmetry of `h` transports into the iterated chart partial's component indices.
  have hcd : ∀ a b c d, D a b c d = D a b d c := by
    intro a b c d; simp only [hD]; rw [h.symm_fun c d]
  -- The inverse-Gram/Gram contraction `∑_kk g_{j,kk}·G^{kk,l} = δ^l_j`.
  have hcontr : ∀ j l : Fin (Module.finrank ℝ E),
      ∑ kk : Fin (Module.finrank ℝ E), g' j kk * G kk l = (if l = j then (1 : ℝ) else 0) := by
    intro j l
    have hbase : (extChartAt I α).symm y ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
      have hsrc : (extChartAt I α).symm y ∈ (extChartAt I α).source :=
        (extChartAt I α).map_target hy
      rw [extChartAt_source_eq_chartAt_source (I := I)] at hsrc
      rw [trivializationAt_baseSet_eq_chartAt_source]; exact hsrc
    have hmul := chartGramMatrix_mul_chartInvGramMatrix (I := I) g α hbase
    have hentry : (chartGramMatrix (I := I) g α ((extChartAt I α).symm y) *
        chartInvGramMatrix (I := I) g α ((extChartAt I α).symm y)) j l =
        (1 : Matrix _ _ ℝ) j l := by rw [hmul]
    rw [Matrix.mul_apply] at hentry
    have hsum_eq : (∑ kk : Fin (Module.finrank ℝ E), g' j kk * G kk l) =
        (∑ kk : Fin (Module.finrank ℝ E),
          chartGramMatrix (I := I) g α ((extChartAt I α).symm y) j kk *
            chartInvGramMatrix (I := I) g α ((extChartAt I α).symm y) kk l) := by
      refine Finset.sum_congr rfl (fun kk _ => ?_)
      simp only [hg'def, hGdef, chartGramOnE_def, chartInvGramOnE_def]
    rw [hsum_eq, hentry]
    by_cases hlj : l = j
    · subst hlj; rw [Matrix.one_apply_eq]; simp
    · rw [Matrix.one_apply_ne (Ne.symm hlj), if_neg hlj]
  -- Expand both principal symbols in terms of `D`, `G`, `g'`.
  have hRic : chartRicciSecondOrderPrincipalSymbol (I := I) g α h i k y =
      (1 / 2 : ℝ) * ∑ j, ∑ l, G j l * (D j i l k + D k l i j - D j l i k - D k i l j) := by
    rw [chartRicciSecondOrderPrincipalSymbol_def]
  have hDT : chartDeTurckCorrPrincipalSymbolExpr (I := I) g g_bg α h i k y =
      (∑ m, g' m k * ∑ a, ∑ b, G a b *
          ((1 / 2 : ℝ) * ∑ l, G m l * (D i a l b + D i b l a - D i l a b))) +
      (∑ m, g' i m * ∑ a, ∑ b, G a b *
          ((1 / 2 : ℝ) * ∑ l, G m l * (D k a l b + D k b l a - D k l a b))) := by
    rw [chartDeTurckCorrPrincipalSymbolExpr_eq_explicit]
  rw [hRic, hDT]
  -- Symmetry of the chart inverse Gram in its two indices.
  have hGsym : ∀ a b : Fin (Module.finrank ℝ E), G a b = G b a := by
    intro a b
    simp only [hGdef, chartInvGramOnE_def]
    have hHerm := (chartGramMatrix_isHermitian (I := I) g α ((extChartAt I α).symm y)).inv
    have := hHerm.apply b a
    rwa [star_trivial] at this
  -- Collapse the DeTurck outer Gram contraction in each block: `∑_m g'_{m,k}·G^{m,l} = δ^l_k`.
  -- Block 1 (output index `i,k`): contract `∑_m g'_{m,k}·(∑_l G^{m,l}·Z_l) = Z_k`.
  have hDTcollapse : ∀ (q : Fin (Module.finrank ℝ E))
      (Z : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ),
      (∑ m, g' m q * ∑ a, ∑ b, G a b *
          ((1 / 2 : ℝ) * ∑ l, G m l * Z a b l)) =
        ∑ a, ∑ b, G a b * ((1 / 2 : ℝ) * Z a b q) := by
    intro q Z
    -- Distribute `g' m q ·` and swap `∑_m` past `∑_a ∑_b`, isolating `∑_m g'_{m,q}·G^{m,l}`.
    have hstep : (∑ m, g' m q * ∑ a, ∑ b, G a b * ((1 / 2 : ℝ) * ∑ l, G m l * Z a b l)) =
        ∑ a, ∑ b, G a b * ((1 / 2 : ℝ) * ∑ l, (∑ m, g' m q * G m l) * Z a b l) := by
      -- Flatten LHS to a quadruple sum `∑_m ∑_a ∑_b ∑_l g'_{mq}·G_{ab}·½·G_{ml}·Z_{abl}`.
      have hL : (∑ m, g' m q * ∑ a, ∑ b, G a b * ((1 / 2 : ℝ) * ∑ l, G m l * Z a b l)) =
          ∑ a, ∑ b, ∑ l, ∑ m,
            g' m q * (G a b * ((1 / 2 : ℝ) * (G m l * Z a b l))) := by
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun a _ => ?_)
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun b _ => ?_)
        rw [Finset.sum_comm]
      have hR : (∑ a, ∑ b, G a b * ((1 / 2 : ℝ) * ∑ l, (∑ m, g' m q * G m l) * Z a b l)) =
          ∑ a, ∑ b, ∑ l, ∑ m,
            g' m q * (G a b * ((1 / 2 : ℝ) * (G m l * Z a b l))) := by
        simp only [Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ =>
          Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun m _ => by ring))))
      rw [hL, hR]
    rw [hstep]
    refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
    congr 1
    congr 1
    -- contract `∑_m g'_{m,q}·G^{m,l} = ∑_m g'_{q,m}·G^{m,l} = δ^l_q`
    rw [show (∑ l, (∑ m, g' m q * G m l) * Z a b l) =
        ∑ l, (if l = q then (1 : ℝ) else 0) * Z a b l from by
      refine Finset.sum_congr rfl (fun l _ => ?_)
      rw [← hcontr q l]
      congr 1
      refine Finset.sum_congr rfl (fun m _ => ?_)
      rw [hg'def]; simp only [chartGramOnE_symm (I := I) g α q m y]]
    simp only [ite_mul, one_mul, zero_mul]
    rw [Finset.sum_ite_eq' Finset.univ q (fun l => Z a b l)]
    simp
  -- Symmetry of the chart Gram in its two indices (for the second DeTurck block, summed on the right).
  have hg'sym : ∀ a b : Fin (Module.finrank ℝ E), g' a b = g' b a := by
    intro a b; simp only [hg'def]; exact chartGramOnE_symm (I := I) g α a b y
  rw [show (∑ m, g' i m * ∑ a, ∑ b, G a b *
          ((1 / 2 : ℝ) * ∑ l, G m l * (D k a l b + D k b l a - D k l a b))) =
        ∑ m, g' m i * ∑ a, ∑ b, G a b *
          ((1 / 2 : ℝ) * ∑ l, G m l * (D k a l b + D k b l a - D k l a b)) from
    Finset.sum_congr rfl (fun m _ => by rw [hg'sym i m])]
  rw [hDTcollapse k (fun a b l => D i a l b + D i b l a - D i l a b),
    hDTcollapse i (fun a b l => D k a l b + D k b l a - D k l a b)]
  -- Now the goal is a finite-sum identity in `G` and `D`.  Combine the three double sums into a single
  -- `∑_{j,l} G^{j,l} · C_{j,l}` and reduce to `∑_{j,l} G^{j,l} · D_{j,l,i,k}` by symmetrising in `(j,l)`.
  set C : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ :=
    fun j l => (-2 : ℝ) * ((1 / 2 : ℝ) * (D j i l k + D k l i j - D j l i k - D k i l j)) +
      ((1 / 2 : ℝ) * (D i j k l + D i l k j - D i k j l) +
        (1 / 2 : ℝ) * (D k j i l + D k l i j - D k i j l)) with hCdef
  have hLHS : (-2 : ℝ) *
        ((1 / 2 : ℝ) * ∑ j, ∑ l, G j l * (D j i l k + D k l i j - D j l i k - D k i l j)) +
      ((∑ a, ∑ b, G a b * ((1 / 2 : ℝ) * (D i a k b + D i b k a - D i k a b))) +
        (∑ a, ∑ b, G a b * ((1 / 2 : ℝ) * (D k a i b + D k b i a - D k i a b)))) =
      ∑ j, ∑ l, G j l * C j l := by
    -- Write each of the three terms as a double sum `∑_j ∑_l G_{jl}·(…)`, then combine pointwise.
    have hT1 : (-2 : ℝ) *
        ((1 / 2 : ℝ) * ∑ j, ∑ l, G j l * (D j i l k + D k l i j - D j l i k - D k i l j)) =
        ∑ j, ∑ l, G j l *
          ((-2 : ℝ) * ((1 / 2 : ℝ) * (D j i l k + D k l i j - D j l i k - D k i l j))) := by
      rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun l _ => ?_); ring
    rw [hT1, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [hCdef]; ring
  rw [hLHS]
  -- Symmetrise `∑_{j,l} G^{j,l} C_{j,l} = ∑_{j,l} G^{j,l}·(C_{j,l}+C_{l,j})/2` (G symmetric),
  -- then `(C_{j,l}+C_{l,j})/2 = D_{j,l,i,k}` per pair.
  have hsymsum : (∑ j, ∑ l, G j l * C j l) =
      ∑ j, ∑ l, G j l * ((1 / 2 : ℝ) * (C j l + C l j)) := by
    -- `∑ G_{jl}·½(C_{jl}+C_{lj}) = ½∑ G_{jl}C_{jl} + ½∑ G_{jl}C_{lj}`; the second sum equals the first.
    have hswap : (∑ j, ∑ l, G j l * C l j) = ∑ j, ∑ l, G j l * C j l := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun l _ => ?_))
      rw [hGsym l j]
    calc (∑ j, ∑ l, G j l * C j l)
        = (1 / 2 : ℝ) * ((∑ j, ∑ l, G j l * C j l) + ∑ j, ∑ l, G j l * C l j) := by
          rw [hswap]; ring
      _ = ∑ j, ∑ l, G j l * ((1 / 2 : ℝ) * (C j l + C l j)) := by
          rw [mul_add, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl (fun j _ => ?_)
          rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl (fun l _ => ?_)
          ring
  rw [hsymsum]
  refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun l _ => ?_))
  congr 1
  -- per-pair: `(C_{j,l} + C_{l,j})/2 = D_{j,l,i,k}`, by Schwarz `hsw` + `h`-symmetry `hcd`.
  -- Canonicalise every iterated-partial atom to a fixed representative, then `ring`.
  simp only [hCdef]
  have c1 : D i j k l = D j i l k := by rw [hsw i j k l, hcd j i k l]
  have c2 : D i k l j = D i k j l := by rw [hcd i k l j]
  have c3 : D i l k j = D l i j k := by rw [hsw i l k j, hcd l i k j]
  have c4 : D k i j l = D i k j l := by rw [hsw k i j l]
  have c5 : D k i l j = D i k j l := by rw [hsw k i l j, hcd i k l j]
  have c6 : D k j i l = D j k l i := by rw [hsw k j i l, hcd j k i l]
  have c7 : D k l i j = D l k j i := by rw [hsw k l i j, hcd l k i j]
  have c8 : D l j i k = D j l i k := by rw [hsw l j i k]
  rw [c1, c2, c3, c4, c5, c6, c7, c8]
  ring

/-! ## The pointwise Lichnerowicz `appCc` form and the path-integral coefficient construction
(the two deep mean-value inputs, posited and recursed into downstream) -/

/-- **The order-`0` (curvature) coefficient field of the linearized Ricci operator along the realized
path.**  For the realized path metric `g_s = realizedFam g₀ T T' s`, this is the genuine `(2, 2)`
**curvature** slot-insertion field `ricciArmOrder0CurvCoeff g₀ g_s` of the order-`0` arm — the
leading-slot insertion of the raised curvature endomorphism `ricEndoRaisedFib g_s` (the classical
Lichnerowicz `Rm(g_s)·h` order-`0` action, `RicciDeTurckSectionDifference`).  It is the per-`s`
coefficient `R₀fib(s)` the linearized-Ricci two-term Lichnerowicz form contracts against `W₀ = T − T'`.

Re-minted from the earlier `gInvDiffSlotCoeff g₀ g_s` (the cometric inverse-difference multiplier),
which vanishes identically at `g_s = g₀` and is therefore NOT the genuine order-`0` (value-level) arm:
the order-`0` symbol of `D Ric(g_s)[h]` is the curvature action, nonzero at `g_s = g₀` on a curved
background. -/
noncomputable def ricciArmOrder0Coeff (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (s : ℝ) : SmoothCcTensor g₀ 2 2 :=
  ricciArmOrder0CurvCoeff (I := I) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' s)

/-- **The order-`2` (PURE rough-Laplacian principal) coefficient field of the linearized Ricci–DeTurck
operator along the realized path.**  For the realized path metric `g_s = realizedFam g₀ T T' s`, this is the
PURE rough-Laplacian `(4, 2)` principal field `ricciArmPrincipalCoeffPure g₀ g_s` of the order-`2` arm — the
single `{0, 1}`-cometric double trace `cometricDoubleTraceFib g_s 2`, whose `appCc` read-off is the pure
rough Laplacian `A_{ik} = ∑_{j,l} g_s^{jl} ∂_j ∂_l h_{ik}` (`ricciArmPrincipalCoeffPure_appCc_eq_roughLaplacian`).

This is the COMBINED-operator's order-2 principal AFTER the DeTurck gauge cancellation: the bare Ricci symbol
carries the non-isotropic gauge terms `½ξ_i(ξt)_k + ½ξ_k(ξt)_i − ½ξ_iξ_k·tr`, which the DeTurck-correction
symbol exactly kills on a symmetric perturbation, leaving the pure rough Laplacian.  It is therefore NOT the
gauge-carrying combined three-trace `ricciArmPrincipalCoeff g₀ g_s` (`= ½(BT1 + BT2 − A)`, the bare-Ricci
symbol, off by the surviving cross-divergence terms): a dim-`4` random-SPD numeric confirms `A ≠
combinedTrace42Model`.  It is the per-`s` coefficient `R₂fib(s)` the combined linearized two-term Lichnerowicz
form contracts against `W₂ = ∇₀²(T − T')`. -/
noncomputable def ricciArmOrder2Coeff (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (s : ℝ) : SmoothCcTensor g₀ 4 2 :=
  ricciArmPrincipalCoeffPure (I := I) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' s)

/-- **The chart-Gram velocity of the realized section-difference perturbation at parameter `s`.**

For the realized metric path `g_s = realizedFam g₀ T T' s`, every chart-Gram component
`σ ↦ g_{ij}(g_σ)(α, y)` is, on the smallness set, affine in `σ` (`realizedFam_chartGramOnE` is the convex
combination `(1 − σ)·g_{ij}(realize(g₀ + T')) + σ·g_{ij}(realize(g₀ + T))`), hence its `σ`-derivative at
`s` is the constant velocity `g_{ij}(realize(g₀ + T)) − g_{ij}(realize(g₀ + T'))`.  A chart perturbation
`h : ChartMetricPerturbation E` **is the realized section-difference velocity at `(α, s)`** when, at every
chart-interior point `y`, each chart-Gram component of the realized family has `σ`-derivative at `s` equal
to the component `h i j y`:
`(d/dσ) g_{ij}(realizedFam σ)(α, y)|_{σ = s} = h i j y`.  This is exactly the chart-Gram value-velocity
pin of `IsMetricPerturbationFamily` for the family translated to base `s`, and it pins `h` to the
section-difference jet that the chart-symbol → intrinsic transfer reads off. -/
def IsRealizedChartVelocity (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (α : M) (s : ℝ) (h : ChartMetricPerturbation E) : Prop :=
  ∀ (i j : Fin (Module.finrank ℝ E)),
    ∀ᶠ y in nhds (extChartAt I α α),
      HasDerivAt
        (fun σ : ℝ => chartGramOnE (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' σ) α i j y)
        (h i j y) s

/-- **(Posited deep input — the cutoff metric-perturbation family of the re-base metric `g_s`,
with the locality agreement to the realized family near `x`.)**

For the realized re-base metric `g_s = realizedFam g₀ T T' s` at an interior parameter `s ∈ (0,1)`
and a base point `x`, there are a chart perturbation `h : ChartMetricPerturbation E` (the chart
section-difference velocity `χ · V`, with `V` the convex chart-Gram velocity and `χ` a smooth bump
`≡ 1` near `extChartAt I x x`, `tsupport χ ⊆ interior (extChartAt I x).target`) and a smooth
one-parameter family `gfam` of positive-definite metrics such that:

* `gfam` is a `g_s`-metric-perturbation family along `h` (`IsMetricPerturbationFamily g_s x h gfam`),
  built as the realized metric of the cutoff chart-Gram perturbation `g_s ⊕ σ · χ · V`: it passes
  through `g_s` at `σ = 0`, its chart-Gram value/first-jet/second-jet `σ`-derivatives at `0` are
  exactly the corresponding jets of `h = χ · V` (affine in `σ`, with all `∂χ`-factors absorbed into
  `h` itself), and the chart Gram is jointly `(σ, y)`-`C^∞`;
* `h` is the realized section-difference chart velocity at `(x, s)` (`IsRealizedChartVelocity`): near
  `extChartAt I x x` the cutoff `χ ≡ 1`, so `h = V`, and there `V` is the constant `σ`-derivative of
  the affine realized chart Gram (`realizedFam_chartGramOnE`);
* (locality) for every pair `(i, k)`, the chart-Ricci read-off **and** the combined Ricci–DeTurck
  chart read-off `chartDeTurckRicciRHS (· ) g_bg` at the single chart point `extChartAt I x x` of the
  *translated* cutoff family `gfam` agree, on a whole neighbourhood of `σ = 0`, with those of the
  *re-based realized* family `σ ↦ realizedFam (s + σ)`, because near `x` the cutoff `χ ≡ 1` makes
  `gfam σ` and `realizedFam (s + σ)` have the *same chart Gram on a neighbourhood of `extChartAt I x x`*,
  hence the same chart Christoffel/Riemann/Ricci jet AND the same chart DeTurck-vector-field jet there
  (both `chartRicciTensor` and `chartDeTurckRicciRHS = −2·chartRicciTensor + chartLieDeTurckComp` read
  only the chart-Gram jet near `x`, so the chart-Gram agreement transfers both).

This is the classical "extend a local chart-Gram perturbation to a global positive-definite metric
family" construction (the cutoff realiser, parallel to `realize`/`realizedMetricPathOpen`), packaged
together with its base-point chart-Ricci/Ricci–DeTurck locality; it is not yet on disk and is *posited*
here, to be discharged by recursing into it.  It genuinely constrains `(h, gfam)` to be the cutoff
perturbation family of `g_s` with velocity `h` matching the realized chart velocity near `x`, so it is
non-vacuous: the zero perturbation (`h = 0`, `gfam ≡ g_s`) fails it wherever the realized chart velocity
`V` is nonzero near `x`. -/
theorem exists_rebased_cutoffMetricPerturbationFamily
    (g₀ g_bg : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    {s : ℝ} (hs : s ∈ Set.Ioo (0 : ℝ) 1) (x : M) :
    ∃ (h : ChartMetricPerturbation E) (gfam : ℝ → SmoothRiemannianMetric I M),
      IsMetricPerturbationFamily (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x h gfam ∧
        IsRealizedChartVelocity (I := I) g₀ T T' hδ hδ' x s h ∧
        (∀ (i k : Fin (Module.finrank ℝ E)),
          (fun σ : ℝ => chartRicciTensor (I := I) (gfam σ) x i k (extChartAt I x x))
            =ᶠ[nhds (0 : ℝ)]
              (fun σ : ℝ => chartRicciTensor (I := I)
                (realizedFam (I := I) g₀ T T' hδ hδ' (s + σ)) x i k (extChartAt I x x))) ∧
        (∀ (i k : Fin (Module.finrank ℝ E)),
          (fun σ : ℝ => DifferentialGeometry.PDE.RicciFlow.chartFComponentOnE (I := I)
              (DifferentialGeometry.PDE.RicciFlow.deTurckRicciRHS (I := I) g_bg) (gfam σ) x i k
              (extChartAt I x x))
            =ᶠ[nhds (0 : ℝ)]
              (fun σ : ℝ => DifferentialGeometry.PDE.RicciFlow.chartFComponentOnE (I := I)
                (DifferentialGeometry.PDE.RicciFlow.deTurckRicciRHS (I := I) g_bg)
                (realizedFam (I := I) g₀ T T' hδ hδ' (s + σ)) x i k (extChartAt I x x))) :=
  sorry

/-- **The realized combined Ricci–DeTurck chart sum along the metric path.**

For the realized metric path `g_s = realizedFam g₀ T T' s`, the `chartModelBasis`-trace read-off, at the
single chart point `extChartAt I x x`, of the chart `(i, k)`-components of the **combined** Ricci–DeTurck
right-hand side `deTurckRicciRHS g_bg (g_s)` (the operator `g ↦ −2 Rc(g) + 𝓛_{W(g, g_bg)} g`), weighted
by the chart components of the tangent pair `(v, w)`.  This is the combined-operator analogue of
`realizedRicciChartSum` (the bare `−2 Rc` arm), whose `s`-derivative the re-basing reads off as the
gauge-cancelled rough Laplacian. -/
def realizedDeTurckRicciChartSum (g₀ g_bg : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (v w : TangentSpace I x) (s : ℝ) : ℝ :=
  ∑ i, ∑ k,
    ((chartModelBasis E).repr v) k * ((chartModelBasis E).repr w) i *
      DifferentialGeometry.PDE.RicciFlow.chartFComponentOnE (I := I)
        (DifferentialGeometry.PDE.RicciFlow.deTurckRicciRHS (I := I) g_bg)
        (realizedFam (I := I) g₀ T T' hδ hδ' s) x i k (extChartAt I x x)

/-- **The re-basing of the combined Ricci–DeTurck chart `s`-derivative at an interior parameter.**

For the realized metric path `g_s = realizedFam g₀ T T' s` and every interior parameter `s ∈ (0,1)`,
the `s`-derivative of the realized combined chart sum `deriv (realizedDeTurckRicciChartSum) s` equals the
`chartModelBasis`-trace read-off, at the re-base metric `g_s`, of the on-disk **combined** chart
second-order split `deTurckRicciRHSChartSecondOrderPart g_s g_bg h +
metricFamilyDeTurckRicciFirstOrderRemainder g_s g_bg h`, where `h` is the section-difference chart
velocity (`IsRealizedChartVelocity`).

This is the **re-basing** half of the combined Ricci–DeTurck-arm linearization, assembled from the cutoff
metric-perturbation family `exists_rebased_cutoffMetricPerturbationFamily`: the metric-family
chart-linearization keystone `hasDerivAt_chartFComponentOnE_deTurckRicciRHS`
(`MetricFamilyChartLinearization`) computes the `σ`-derivative at `σ = 0` of
`σ ↦ chartFComponentOnE (deTurckRicciRHS g_bg) (gfam σ) x i k y` for the cutoff family `gfam` of `g_s`,
giving the combined second-order part `−2·chartRicciSecondOrderPart + chartDeTurckCorrSecondOrderPart`
(definitionally `deTurckRicciRHSChartSecondOrderPart`) plus the genuinely-first-order
`metricFamilyDeTurckRicciFirstOrderRemainder`; by the family's base-point combined locality this transfers
(`HasDerivAt.congr_of_eventuallyEq`) to the re-based realized family, and the translation invariance of
the derivative (`HasDerivAt.comp_sub_const`) re-bases it from `σ = 0` of the translated family to `s`. -/
theorem deriv_realizedDeTurckRicciChartSum_eq_rebased_chartSymbol
    (g₀ g_bg : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    {s : ℝ} (hs : s ∈ Set.Ioo (0 : ℝ) 1) (x : M) (v w : TangentSpace I x) :
    ∃ h : ChartMetricPerturbation E,
      IsRealizedChartVelocity (I := I) g₀ T T' hδ hδ' x s h ∧
        deriv (realizedDeTurckRicciChartSum (I := I) g₀ g_bg T T' hδ hδ' x v w) s =
          ∑ i : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
            ((chartModelBasis E).repr v) k * ((chartModelBasis E).repr w) i *
              (DifferentialGeometry.PDE.RicciFlow.deTurckRicciRHSChartSecondOrderPart (I := I)
                  (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg h x i k (extChartAt I x x) +
                DifferentialGeometry.PDE.DeTurck.DeTurckLinearization.metricFamilyDeTurckRicciFirstOrderRemainder
                  (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg x h i k (extChartAt I x x)) := by
  classical
  -- The cutoff metric-perturbation family of `g_s`, its velocity-pin, and its base-point combined locality.
  obtain ⟨h, gfam, hfam, hvel, _hlocRic, hloc⟩ :=
    exists_rebased_cutoffMetricPerturbationFamily (I := I) g₀ g_bg T T' hδ_lt hδ hδ'_lt hδ' hs x
  refine ⟨h, hvel, ?_⟩
  -- Abbreviate the re-base metric and the fixed chart-evaluation point.
  set gs : SmoothRiemannianMetric I M := realizedFam (I := I) g₀ T T' hδ hδ' s with hgs
  set y₀ : E := extChartAt I x x with hy₀
  -- The chart-interior membership of the base chart point (boundaryless atlas).
  have hy : y₀ ∈ interior (extChartAt I x).target :=
    extChartAt_target_subset_interior_of_boundaryless (I := I) x (mem_extChartAt_target x)
  -- The combined second-order part value, as the keystone derivative target.
  set Pval : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ :=
    fun i k => DifferentialGeometry.PDE.RicciFlow.deTurckRicciRHSChartSecondOrderPart (I := I)
        gs g_bg h x i k y₀ +
      DifferentialGeometry.PDE.DeTurck.DeTurckLinearization.metricFamilyDeTurckRicciFirstOrderRemainder
        (I := I) gs g_bg x h i k y₀ with hPval
  -- Per-summand: `t ↦ chartFComponentOnE (deTurckRicciRHS g_bg) (realizedFam t) x i k y₀` has, at `s`,
  -- the combined chart second-order split.
  have hper : ∀ i k : Fin (Module.finrank ℝ E),
      HasDerivAt (fun t : ℝ => DifferentialGeometry.PDE.RicciFlow.chartFComponentOnE (I := I)
          (DifferentialGeometry.PDE.RicciFlow.deTurckRicciRHS (I := I) g_bg)
          (realizedFam (I := I) g₀ T T' hδ hδ' t) x i k y₀)
        (Pval i k) s := by
    intro i k
    -- The combined chart `σ`-derivative split at `σ = 0` for the cutoff family `gfam` of `g_s`.
    have hsplit : HasDerivAt
        (fun σ : ℝ => DifferentialGeometry.PDE.RicciFlow.chartFComponentOnE (I := I)
          (DifferentialGeometry.PDE.RicciFlow.deTurckRicciRHS (I := I) g_bg) (gfam σ) x i k y₀)
        (((-2 : ℝ) * chartRicciSecondOrderPart (I := I) gs x h i k y₀ +
            DifferentialGeometry.PDE.DeTurck.DeTurckLinearization.chartDeTurckCorrSecondOrderPart
              (I := I) gs g_bg x h i k y₀) +
          DifferentialGeometry.PDE.DeTurck.DeTurckLinearization.metricFamilyDeTurckRicciFirstOrderRemainder
            (I := I) gs g_bg x h i k y₀) 0 :=
      DifferentialGeometry.PDE.DeTurck.DeTurckLinearization.hasDerivAt_chartFComponentOnE_deTurckRicciRHS
        (I := I) hfam g_bg i k hy
    -- The keystone derivative is exactly `Pval i k` (unfold the combined second-order part).
    have hsplit' : HasDerivAt
        (fun σ : ℝ => DifferentialGeometry.PDE.RicciFlow.chartFComponentOnE (I := I)
          (DifferentialGeometry.PDE.RicciFlow.deTurckRicciRHS (I := I) g_bg) (gfam σ) x i k y₀)
        (Pval i k) 0 := by
      rw [hPval]
      simp only [DifferentialGeometry.PDE.RicciFlow.deTurckRicciRHSChartSecondOrderPart]
      exact hsplit
    -- Transfer to the re-based realized family by the family's base-point combined locality.
    have htrans : HasDerivAt
        (fun σ : ℝ => DifferentialGeometry.PDE.RicciFlow.chartFComponentOnE (I := I)
          (DifferentialGeometry.PDE.RicciFlow.deTurckRicciRHS (I := I) g_bg)
          (realizedFam (I := I) g₀ T T' hδ hδ' (s + σ)) x i k y₀)
        (Pval i k) 0 :=
      hsplit'.congr_of_eventuallyEq (hloc i k).symm
    -- Re-base from `σ = 0` of the translated family to `s` of the original via `(· - s)` translation.
    have htrans' : HasDerivAt
        (fun σ : ℝ => DifferentialGeometry.PDE.RicciFlow.chartFComponentOnE (I := I)
          (DifferentialGeometry.PDE.RicciFlow.deTurckRicciRHS (I := I) g_bg)
          (realizedFam (I := I) g₀ T T' hδ hδ' (s + σ)) x i k y₀)
        (Pval i k) (s - s) := by
      rwa [sub_self]
    have hsub := htrans'.comp_sub_const s s
    have hcongr : (fun t : ℝ => DifferentialGeometry.PDE.RicciFlow.chartFComponentOnE (I := I)
          (DifferentialGeometry.PDE.RicciFlow.deTurckRicciRHS (I := I) g_bg)
          (realizedFam (I := I) g₀ T T' hδ hδ' (s + (t - s))) x i k y₀) =
        (fun t : ℝ => DifferentialGeometry.PDE.RicciFlow.chartFComponentOnE (I := I)
          (DifferentialGeometry.PDE.RicciFlow.deTurckRicciRHS (I := I) g_bg)
          (realizedFam (I := I) g₀ T T' hδ hδ' t) x i k y₀) := by
      funext t; rw [add_sub_cancel]
    rwa [hcongr] at hsub
  -- Differentiate the combined chart sum term by term, then read off the derivative.
  have hsum : HasDerivAt
      (fun t : ℝ => ∑ i : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
        ((chartModelBasis E).repr v) k * ((chartModelBasis E).repr w) i *
          DifferentialGeometry.PDE.RicciFlow.chartFComponentOnE (I := I)
            (DifferentialGeometry.PDE.RicciFlow.deTurckRicciRHS (I := I) g_bg)
            (realizedFam (I := I) g₀ T T' hδ hδ' t) x i k y₀)
      (∑ i : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
        ((chartModelBasis E).repr v) k * ((chartModelBasis E).repr w) i * (Pval i k)) s := by
    refine HasDerivAt.fun_sum (fun i _ => HasDerivAt.fun_sum (fun k _ => ?_))
    exact (hper i k).const_mul _
  have hfun : realizedDeTurckRicciChartSum (I := I) g₀ g_bg T T' hδ hδ' x v w =
      (fun t : ℝ => ∑ i : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
        ((chartModelBasis E).repr v) k * ((chartModelBasis E).repr w) i *
          DifferentialGeometry.PDE.RicciFlow.chartFComponentOnE (I := I)
            (DifferentialGeometry.PDE.RicciFlow.deTurckRicciRHS (I := I) g_bg)
            (realizedFam (I := I) g₀ T T' hδ hδ' t) x i k y₀) := by
    funext t; rw [realizedDeTurckRicciChartSum, hy₀]
  rw [hfun]
  exact hsum.deriv

/-- **(Posited deep input — the pointwise covariant Lichnerowicz/Weitzenböck fold, in coordinate
read-off form.)**

This is the single irreducible covariant content of the chart → intrinsic transfer (gauge cancellation
already factored out by `deTurckRicciChartPrincipalSymbol_eq_roughLaplacian`).  It equates the
`chartModelBasis`-trace read-off of the gauge-cancelled chart form (the pure chart rough Laplacian
`∑_{j,l} G^{j,l}(g_s)·∂_j∂_l h_{ik}` plus the genuinely-lower-order chart remainder) directly to the
**covariant read-off pair**: the cometric double-trace of the covariant Hessian `∇₀²(T − T')` (the
intrinsic rough Laplacian `∑ₖ (∇₀² S)(♯_{g_s} b^k, b_k, v 0, v 1)`) plus the **two-slot** Bochner
Ricci-curvature action `(T − T')(ricEndoRaisedFib g_s (v 0), v 1) + (T − T')(v 0, ricEndoRaisedFib g_s (v 1))`.

**The order-`0` is the SYMMETRIC two-slot Ricci action, not a single leading slot.**  The order-`0`
content of the fold is the curvature commutator `Δ_chart h − Δ_∇ h` of the chart coordinate Laplacian
and the covariant rough Laplacian on the SYMMETRIC `(0, 2)`-tensor `h = T − T'`.  By the classical
Bochner identity this commutator is the two-slot raised-Ricci contraction `h(Ric♯·, ·) + h(·, Ric♯·)`,
symmetric in the two slots with EQUAL coefficients and NO independent Riemann `Rm·h` term (the chart
coordinate Laplacian, unlike the Lichnerowicz operator, picks up only the contracted-Christoffel-
derivative Ricci pieces, one per slot).  A single leading-slot action `h(Ric♯·, ·)` alone is asymmetric
and therefore an INCOMPLETE order-`0`; it omits the trailing-slot contraction.  An exact-arithmetic
normal-coordinate jet computation (dims 3/4/5) confirms the order-`0` commutator is symmetric, lies in
the span of the two slot Ricci insertions with equal coefficients, and has no Riemann component.

The right-hand side is written here in the EXACT shape the two sorry-free `appCc`/`unitModel` read-offs
`ricciArmPrincipalCoeffPure_appCc_eq_roughLaplacian` (order-`2`) and
`ricciArmOrder0CurvCoeff_appCc_eq_curvatureAction` (order-`0`, the two-slot Bochner action) produce, so
that the consumer bridge `rebased_chartSymbol_covariantBridge` is a pure `unitModel`/`appCc` ASSEMBLY on
top of this fold and the two read-offs (no further covariant content).  Establishing this fold is the
classical Bochner/Lichnerowicz computation: (i) the chart-vs-covariant Hessian conversion
`chartCovariantSecondGrad_chartHessian_sub_correction` turning `∂²h` into the covariant Hessian
component plus the Christoffel `Γ·∂h + (∂Γ + ΓΓ)·h` corrections (with `h` the realized section-difference
chart velocity, `realizedFam_chartGramOnE` + `IsRealizedChartVelocity` +
`chartGramOnE_realize_sub_eqOn_symm_rawComponent`), and (ii) the Bochner fold of those Christoffel
corrections together with the three lower-order chart remainders into the two-slot Ricci action via the
contracted Christoffel-derivative identity.  It genuinely constrains the chart value to reproduce the
covariant read-off, so it is non-vacuous: the zero chart value fails it where the curvature/Hessian
read-off is nonzero. -/
theorem rebased_chartSymbol_covariantWeitzenbockFold
    (g₀ g_bg : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (s : ℝ) (x : M) (h : ChartMetricPerturbation E)
    (hh : IsRealizedChartVelocity (I := I) g₀ T T' hδ hδ' x s h)
    (v : Fin 2 → TangentSpace I x) :
    (∑ i : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
        ((chartModelBasis E).repr (v 0)) k * ((chartModelBasis E).repr (v 1)) i *
          ((∑ j : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
              chartInvGramOnE (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x j l
                  (extChartAt I x x) *
                partialDeriv (E := E) j (partialDeriv (E := E) l (h i k)) (extChartAt I x x)) +
            ((-2 : ℝ) * DifferentialGeometry.PDE.DeTurck.RicciLinearization.chartRicciFirstOrderRemainder
                  (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x h i k (extChartAt I x x) +
                DifferentialGeometry.PDE.DeTurck.DeTurckLinearization.chartDeTurckCorrFirstOrderRemainder
                  (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg x h i k (extChartAt I x x) +
              DifferentialGeometry.PDE.DeTurck.DeTurckLinearization.metricFamilyDeTurckRicciFirstOrderRemainder
                (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg x h i k (extChartAt I x x)))) =
      (∑ k : Fin (Module.finrank ℝ E),
          unitModel (I := I) (M := M) g₀ 4
              (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T')) x
            (Fin.cons (DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck.cometricLmodel
                (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
                (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                  ((Module.finBasis ℝ E).cDualBasis k)))
              (Fin.cons ((Module.finBasis ℝ E) k) v))) +
        (unitModel (I := I) (M := M) g₀ 2
              (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T')) x
            (Function.update v 0
              (ricEndoRaisedFib (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x (v 0))) +
          unitModel (I := I) (M := M) g₀ 2
              (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T')) x
            (Function.update v 1
              (ricEndoRaisedFib (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x (v 1)))) :=
  sorry

/-- **(The covariant Lichnerowicz/Weitzenböck bridge, gauge cancellation already factored out.)**

For the re-base metric `g_s = realizedFam g₀ T T' s` and the realized section-difference chart velocity
`h` (`IsRealizedChartVelocity`), the `chartModelBasis`-trace read-off of the **gauge-cancelled** chart
form — the pure rough Laplacian `∑_{j,l} G^{j,l}(g_s)·∂_j∂_l h_{ik}` of the section-difference velocity
plus the genuinely-lower-order chart remainder
`(-2)·chartRicciFirstOrderRemainder g_s + chartDeTurckCorrFirstOrderRemainder g_s g_bg +
metricFamilyDeTurckRicciFirstOrderRemainder g_s g_bg` — equals the intrinsic two-term Lichnerowicz
`unitModel`/`appCc` read-off of the order-`0` curvature coefficient `ricciArmOrder0Coeff s` on
`W₀ = T − T'` plus the PURE order-`2` rough-Laplacian coefficient `ricciArmOrder2Coeff s` on
`W₂ = ∇₀²(T − T')`.

This is a pure `unitModel`/`appCc` ASSEMBLY: the order-`0` coefficient `ricciArmOrder0Coeff s` is, by
definition, `ricciArmOrder0CurvCoeff g₀ g_s`, whose `appCc` read-off is the leading-slot curvature
action (`ricciArmOrder0CurvCoeff_appCc_eq_curvatureAction`, sorry-free), and the order-`2` coefficient
`ricciArmOrder2Coeff s` is, by definition, `ricciArmPrincipalCoeffPure g₀ g_s`, whose `appCc` read-off is
the cometric double-trace of the covariant Hessian (`ricciArmPrincipalCoeffPure_appCc_eq_roughLaplacian`,
sorry-free).  Distributing the `unitModel` over the `appCc` sum (`unitModel_add_left`) and applying the
two read-offs reduces the right-hand side to the covariant read-off pair, which is exactly the right-hand
side of the posited fold `rebased_chartSymbol_covariantWeitzenbockFold`. -/
theorem rebased_chartSymbol_covariantBridge
    (g₀ g_bg : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (s : ℝ) (x : M) (h : ChartMetricPerturbation E)
    (hh : IsRealizedChartVelocity (I := I) g₀ T T' hδ hδ' x s h)
    (v : Fin 2 → TangentSpace I x) :
    (∑ i : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
        ((chartModelBasis E).repr (v 0)) k * ((chartModelBasis E).repr (v 1)) i *
          ((∑ j : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
              chartInvGramOnE (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x j l
                  (extChartAt I x x) *
                partialDeriv (E := E) j (partialDeriv (E := E) l (h i k)) (extChartAt I x x)) +
            ((-2 : ℝ) * DifferentialGeometry.PDE.DeTurck.RicciLinearization.chartRicciFirstOrderRemainder
                  (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x h i k (extChartAt I x x) +
                DifferentialGeometry.PDE.DeTurck.DeTurckLinearization.chartDeTurckCorrFirstOrderRemainder
                  (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg x h i k (extChartAt I x x) +
              DifferentialGeometry.PDE.DeTurck.DeTurckLinearization.metricFamilyDeTurckRicciFirstOrderRemainder
                (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg x h i k (extChartAt I x x)))) =
      unitModel (I := I) (M := M) g₀ 2
        (appCc (I := I) (M := M) g₀ 2 2
            (ricciArmOrder0Coeff (I := I) g₀ T T' hδ hδ' s)
            (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T'))
          + appCc (I := I) (M := M) g₀ 4 2
              (ricciArmOrder2Coeff (I := I) g₀ T T' hδ hδ' s)
              (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))) x v := by
  classical
  -- Distribute the `unitModel` over the `appCc` sum and evaluate the resulting multilinear sum at `v`.
  rw [unitModel_add_left, ContinuousMultilinearMap.add_apply]
  -- The order-`0` coefficient is the curvature coefficient; its `appCc` read-off is the leading-slot
  -- Ricci action.  The order-`2` coefficient is the pure rough-Laplacian coefficient; its `appCc`
  -- read-off is the cometric double-trace of the covariant Hessian.  Both are sorry-free read-offs.
  rw [show ricciArmOrder0Coeff (I := I) g₀ T T' hδ hδ' s =
        ricciArmOrder0CurvCoeff (I := I) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' s) from rfl,
    show ricciArmOrder2Coeff (I := I) g₀ T T' hδ hδ' s =
        ricciArmPrincipalCoeffPure (I := I) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' s) from rfl,
    ricciArmOrder0CurvCoeff_appCc_eq_curvatureAction (I := I) g₀
      (realizedFam (I := I) g₀ T T' hδ hδ' s) (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T')) x v,
    ricciArmPrincipalCoeffPure_appCc_eq_roughLaplacian (I := I) g₀
      (realizedFam (I := I) g₀ T T' hδ hδ' s) (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T')) x v]
  -- The remaining identity is the posited covariant Weitzenböck fold (the two arms are now in the
  -- exact read-off shape the fold delivers), commuting the two summands.
  rw [add_comm]
  exact rebased_chartSymbol_covariantWeitzenbockFold (I := I) g₀ g_bg T T' hδ hδ' s x h hh v

/-- **The combined chart-derivative split → intrinsic two-term `appCc` transfer.**

The chart → intrinsic transfer half of the combined Ricci–DeTurck-arm linearization.  Per chart
`(i, k)`-component, the on-disk combined chart second-order part
`deTurckRicciRHSChartSecondOrderPart g_s g_bg = -2·chartRicciSecondOrderPart + chartDeTurckCorrSecondOrderPart`
splits (the two boundaryless split lemmas
`chartRicciSecondOrderPart_eq_principalSymbol_add_remainder_of_mem_source`,
`chartDeTurckCorrSecondOrderPart_eq_principalSymbol_add_remainder_of_mem_source`) into the combined
principal symbol plus the lower-order remainders.  The **DeTurck gauge cancels at the chart 2nd-order
level** on the (always-symmetric) perturbation `h`: the combined principal symbol
`-2·chartRicciSecondOrderPrincipalSymbol + chartDeTurckCorrPrincipalSymbolExpr` is the *pure rough
Laplacian* `∑_{j,l} G^{j,l}·∂_j∂_l h_{ik}` (the proven, reusable
`deTurckRicciChartPrincipalSymbol_eq_roughLaplacian`).  The combined chart value then equals the
gauge-cancelled chart form (rough Laplacian plus lower-order remainder), which the covariant
Lichnerowicz/Weitzenböck bridge `rebased_chartSymbol_covariantBridge` converts to the intrinsic
two-term `unitModel`/`appCc` read-off. -/
theorem rebased_chartSymbol_eq_appCc_pointwise
    (g₀ g_bg : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (s : ℝ) (x : M) (h : ChartMetricPerturbation E)
    (hh : IsRealizedChartVelocity (I := I) g₀ T T' hδ hδ' x s h)
    (v : Fin 2 → TangentSpace I x) :
    (∑ i : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
        ((chartModelBasis E).repr (v 0)) k * ((chartModelBasis E).repr (v 1)) i *
          (DifferentialGeometry.PDE.RicciFlow.deTurckRicciRHSChartSecondOrderPart (I := I)
              (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg h x i k (extChartAt I x x) +
            DifferentialGeometry.PDE.DeTurck.DeTurckLinearization.metricFamilyDeTurckRicciFirstOrderRemainder
              (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg x h i k (extChartAt I x x))) =
      unitModel (I := I) (M := M) g₀ 2
        (appCc (I := I) (M := M) g₀ 2 2
            (ricciArmOrder0Coeff (I := I) g₀ T T' hδ hδ' s)
            (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T'))
          + appCc (I := I) (M := M) g₀ 4 2
              (ricciArmOrder2Coeff (I := I) g₀ T T' hδ hδ' s)
              (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))) x v := by
  classical
  set gs : SmoothRiemannianMetric I M := realizedFam (I := I) g₀ T T' hδ hδ' s with hgs
  set y₀ : E := extChartAt I x x with hy₀
  -- The base chart point lies in the chart target (boundaryless atlas) and the chart source.
  have hx_src : x ∈ (chartAt H x).source := mem_chart_source H x
  have hy_t : y₀ ∈ (extChartAt I x).target := by
    rw [hy₀]; exact mem_extChartAt_target x
  -- Per `(i, k)`: the combined chart second-order part, split + gauge-cancelled, equals the rough
  -- Laplacian plus the lower-order chart remainder `(-2·RicRem + DTRem)`.
  have hsplit : ∀ i k : Fin (Module.finrank ℝ E),
      DifferentialGeometry.PDE.RicciFlow.deTurckRicciRHSChartSecondOrderPart (I := I)
          gs g_bg h x i k y₀ =
        (∑ j : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
            chartInvGramOnE (I := I) gs x j l y₀ *
              partialDeriv (E := E) j (partialDeriv (E := E) l (h i k)) y₀) +
          ((-2 : ℝ) * DifferentialGeometry.PDE.DeTurck.RicciLinearization.chartRicciFirstOrderRemainder
                (I := I) gs x h i k y₀ +
            DifferentialGeometry.PDE.DeTurck.DeTurckLinearization.chartDeTurckCorrFirstOrderRemainder
                (I := I) gs g_bg x h i k y₀) := by
    intro i k
    rw [DifferentialGeometry.PDE.RicciFlow.deTurckRicciRHSChartSecondOrderPart]
    rw [chartRicciSecondOrderPart_eq_principalSymbol_add_remainder_of_mem_source
        (I := I) gs x h i k hx_src,
      DifferentialGeometry.PDE.DeTurck.DeTurckLinearization.chartDeTurckCorrSecondOrderPart_eq_principalSymbol_add_remainder_of_mem_source
        (I := I) gs g_bg x h i k hx_src]
    rw [hy₀] at *
    -- regroup: -2·(RicPrinc + RicRem) + (DTPrinc + DTRem)
    --        = (-2·RicPrinc + DTPrinc) + (-2·RicRem + DTRem)
    rw [show ((-2 : ℝ) * (chartRicciSecondOrderPrincipalSymbol (I := I) gs x h i k (extChartAt I x x) +
            DifferentialGeometry.PDE.DeTurck.RicciLinearization.chartRicciFirstOrderRemainder
              (I := I) gs x h i k (extChartAt I x x)) +
          (DifferentialGeometry.PDE.DeTurck.DeTurckLinearization.chartDeTurckCorrPrincipalSymbolExpr
              (I := I) gs g_bg x h i k (extChartAt I x x) +
            DifferentialGeometry.PDE.DeTurck.DeTurckLinearization.chartDeTurckCorrFirstOrderRemainder
              (I := I) gs g_bg x h i k (extChartAt I x x))) =
        ((-2 : ℝ) * chartRicciSecondOrderPrincipalSymbol (I := I) gs x h i k (extChartAt I x x) +
            DifferentialGeometry.PDE.DeTurck.DeTurckLinearization.chartDeTurckCorrPrincipalSymbolExpr
              (I := I) gs g_bg x h i k (extChartAt I x x)) +
          ((-2 : ℝ) * DifferentialGeometry.PDE.DeTurck.RicciLinearization.chartRicciFirstOrderRemainder
                (I := I) gs x h i k (extChartAt I x x) +
            DifferentialGeometry.PDE.DeTurck.DeTurckLinearization.chartDeTurckCorrFirstOrderRemainder
              (I := I) gs g_bg x h i k (extChartAt I x x)) from by ring]
    rw [deTurckRicciChartPrincipalSymbol_eq_roughLaplacian (I := I) gs g_bg x h i k hy_t]
  -- Rewrite the LHS sum per `(i, k)` and reduce to the covariant bridge.
  rw [show (∑ i : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
        ((chartModelBasis E).repr (v 0)) k * ((chartModelBasis E).repr (v 1)) i *
          (DifferentialGeometry.PDE.RicciFlow.deTurckRicciRHSChartSecondOrderPart (I := I)
              gs g_bg h x i k y₀ +
            DifferentialGeometry.PDE.DeTurck.DeTurckLinearization.metricFamilyDeTurckRicciFirstOrderRemainder
              (I := I) gs g_bg x h i k y₀)) =
      ∑ i : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
        ((chartModelBasis E).repr (v 0)) k * ((chartModelBasis E).repr (v 1)) i *
          ((∑ j : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
              chartInvGramOnE (I := I) gs x j l y₀ *
                partialDeriv (E := E) j (partialDeriv (E := E) l (h i k)) y₀) +
            ((-2 : ℝ) * DifferentialGeometry.PDE.DeTurck.RicciLinearization.chartRicciFirstOrderRemainder
                  (I := I) gs x h i k y₀ +
                DifferentialGeometry.PDE.DeTurck.DeTurckLinearization.chartDeTurckCorrFirstOrderRemainder
                  (I := I) gs g_bg x h i k y₀ +
              DifferentialGeometry.PDE.DeTurck.DeTurckLinearization.metricFamilyDeTurckRicciFirstOrderRemainder
                (I := I) gs g_bg x h i k y₀)) from by
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun k _ => ?_))
    rw [hsplit i k]; ring]
  exact rebased_chartSymbol_covariantBridge (I := I) g₀ g_bg T T' hδ hδ' s x h hh v

/-- **The pointwise combined chart-derivative → intrinsic two-term `appCc` identity (the deep covariant
bridge, gauge cancelled).**

For the realized metric path `g_s = realizedFam g₀ T T' s` and every interior parameter `s ∈ (0,1)`, the
`s`-derivative of the realized **combined** Ricci–DeTurck chart sum `deriv (realizedDeTurckRicciChartSum)`
equals the intrinsic two-term Lichnerowicz `unitModel`/`appCc` read-off of the order-`0` coefficient
`ricciArmOrder0Coeff s` acting on `W₀ = T − T'` plus the order-`2` coefficient `ricciArmOrder2Coeff s`
acting on `W₂ = ∇₀²(T − T')`.

This is the irreducible deep mean-value/covariant content of the *combined* Ricci–DeTurck-arm
linearization, assembled from the two halves: the **re-basing**
`deriv_realizedDeTurckRicciChartSum_eq_rebased_chartSymbol` (the metric-family chart-linearization
keystone `hasDerivAt_chartFComponentOnE_deTurckRicciRHS` re-based to the interior parameter `s` via the
translated `IsMetricPerturbationFamily` of `g_s`, yielding `deriv = ∑ repr·repr·(combined chart
second-order part + first-order remainder)` with `h` the section-difference chart velocity) and the
**combined chart → intrinsic transfer** `rebased_chartSymbol_eq_appCc_pointwise` (the DeTurck gauge
cancels at the chart 2nd-order/symbol level, so the combined principal symbol is the pure rough Laplacian,
and the chart-vs-covariant Hessian conversion folds `½G^{jl}∂²h` into the combined three-trace
`ricciArmPrincipalCoeff_appCc_eq_combinedTrace` on `∇₀²(T − T')`, the lower-order terms into the order-`0`
inverse-Gram slot field on `T − T'`, NO genuine order-`1` arm).  These covariant bridges are posited in
the transfer half, to be discharged by recursing into them.  It genuinely constrains the combined
linearized value to be the two-term read-off pointwise, so it is non-vacuous: the zero coefficients fail
it where the combined linearized operator is nonzero. -/
theorem deriv_realizedDeTurckRicciChartSum_eq_appCc_pointwise
    (g₀ g_bg : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    {s : ℝ} (hs : s ∈ Set.Ioo (0 : ℝ) 1) (x : M) (v : Fin 2 → TangentSpace I x) :
    deriv (realizedDeTurckRicciChartSum (I := I) g₀ g_bg T T' hδ hδ' x (v 0) (v 1)) s =
      unitModel (I := I) (M := M) g₀ 2
        (appCc (I := I) (M := M) g₀ 2 2
            (ricciArmOrder0Coeff (I := I) g₀ T T' hδ hδ' s)
            (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T'))
          + appCc (I := I) (M := M) g₀ 4 2
              (ricciArmOrder2Coeff (I := I) g₀ T T' hδ hδ' s)
              (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))) x v := by
  obtain ⟨h, hh, hderiv⟩ :=
    deriv_realizedDeTurckRicciChartSum_eq_rebased_chartSymbol (I := I) g₀ g_bg T T' hδ_lt hδ hδ'_lt hδ'
      hs x (v 0) (v 1)
  rw [hderiv]
  exact rebased_chartSymbol_eq_appCc_pointwise (I := I) g₀ g_bg T T' hδ hδ' s x h hh v

/-- **The per-arm `unitModel`/`appCc` read-off is continuous in `s` whenever the model-fibre value
of the coefficient family is.**  At a fixed base point `x`, contracted tensor `W`, and tangent
tuple `v`, the scalar read-off `s ↦ unitModel g₀ 2 (appCc g₀ r 2 (Ψ s) W) x v` factors through the
*fixed* continuous-linear chain `T ↦ ((T) (toModel u)) v` applied to the model-fibre value
`toModel ((Ψ s).toSection x)` (where `u = (W x) unit`), via `toModel_tensorRS_apply`; so its
continuity in `s` follows from continuity in `s` of `s ↦ toModel ((Ψ s).toSection x)`.  This turns the
joint-`(s, x)`-smoothness keystone's continuity slice into the per-arm read-off continuity. -/
private theorem appCc_unitModel_read_continuousOn_of_toModel_continuousOn
    (g₀ : SmoothRiemannianMetric I M) (r : ℕ)
    (Ψ : ℝ → SmoothCcTensor g₀ r 2) (W : SmoothCcTensor g₀ 0 r) {S : Set ℝ}
    {x : M} (hΨ : ContinuousOn (fun s : ℝ => TensorRSSpace.toModel ((Ψ s).toSection x)) S)
    (v : Fin 2 → TangentSpace I x) :
    ContinuousOn (fun s : ℝ =>
      unitModel (I := I) (M := M) g₀ 2 (appCc (I := I) (M := M) g₀ r 2 (Ψ s) W) x v) S := by
  -- Abbreviate the fixed contracted-then-unit-evaluated `(0, r)`-tensor `u = (W x) unit`.
  set u : Tensor0SSpace r I x :=
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace r I x from W.toSection x)
      (unitTensor (I := I) (M := M) x) with hu
  -- Reduce the read-off to the model-operator action at `u`, evaluated at `v` (the `key` pattern).
  have key : ∀ s : ℝ,
      unitModel (I := I) (M := M) g₀ 2 (appCc (I := I) (M := M) g₀ r 2 (Ψ s) W) x v =
        ((TensorRSSpace.toModel ((Ψ s).toSection x)) (Tensor0SSpace.toModel u)) v := by
    intro s
    rw [unitModel, appCc_toSection, ContinuousLinearMap.comp_apply,
      toModel_tensorRS_apply (I := I) r 2 x ((Ψ s).toSection x) u]
  -- The read-off is the fixed CLM chain `T ↦ (T (toModel u)) v` applied to `toModel ((Ψ s).toSection x)`.
  have hchain : Continuous (fun T : Tensor0SBundle.TensorRSModel r 2 ℝ E =>
      (T (Tensor0SBundle.Tensor0SSpace.toModel u)) v) :=
    (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 => E) ℝ v).continuous.comp
      (ContinuousLinearMap.apply ℝ (Tensor0SBundle.Tensor0SModel 2 ℝ E)
        (Tensor0SBundle.Tensor0SSpace.toModel u)).continuous
  exact (hchain.comp_continuousOn hΨ).congr (fun s _ => (key s).symm)

set_option backward.isDefEq.respectTransparency false in
/-- **Joint `(x, s)`-smoothness of the PURE order-`2` principal coefficient along the realized path.**

For the realized metric family `g_s = realizedFam g₀ T T' s`, the PURE order-`2` rough-Laplacian coefficient
operator field `ricciArmPrincipalCoeffPure g₀ g_s` (the single `{0, 1}`-cometric double trace
`cometricDoubleTraceFib g_s 2`, the `(4, 2)`-operator field of `g_s`) is jointly `C^∞` in the pair `(x, s)`,
as a section over `M × ℝ` of the `(4, 2)`-tensor bundle, **on the slab `univ ×ˢ realizedSmallSet`**.

This is the joint-parameter lift of the single-metric base-point smoothness `cometricDoubleTraceFib_contMDiff`:
it routes through the named cometric-double-trace SUB-STEP of the principal keystone,
`cometricDoubleTraceFib_realizedFam_jointContMDiffOn (p := 2)` (the joint cometric tower built it as an
intermediate of `ricciArmPrincipalCoeffFib_realizedFam_jointContMDiffOn`), via the joint section constructor
`contMDiffOn_clm_section_of_pointwise_jointMR` (which reduces the operator-field section smoothness to the
joint smoothness of the operator applied to each smooth global section).  It is the joint smoothness of the
re-minted order-`2` coefficient `ricciArmPrincipalCoeffPure`. -/
theorem ricciArmPrincipalCoeffPure_realizedFam_jointContMDiff [BoundarylessManifold I M]
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ') :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 4 2 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 4 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace 4 2 I z) p.1
        ((ricciArmPrincipalCoeffPure (I := I) g₀
            (realizedFam (I := I) g₀ T T' hδ hδ' p.2)).toSection p.1))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
  -- The operator-field section is, at every `(x, s)`, the cometric double-trace fibre operator of `g_s`
  -- (`ricciArmPrincipalCoeffPure_toSection`).  Reduce the section smoothness to the joint smoothness of
  -- that operator applied to an arbitrary smooth global `(0, 4)`-section, via the joint section constructor.
  have hsection :
      ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 4 2 ℝ E)) ∞
        (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 4 2 ℝ E)
          (E := fun z : M => Tensor0SBundle.TensorRSSpace 4 2 I z) p.1
          (DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck.cometricDoubleTraceFib (I := I)
            (realizedFam (I := I) g₀ T T' hδ hδ' p.2) 2 p.1))
        ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
    apply contMDiffOn_clm_section_of_pointwise_jointMR (I := I) (M := M)
      (F₁ := Tensor0SBundle.Tensor0SModel 4 ℝ E) (V₁ := fun x : M => Tensor0SBundle.Tensor0SSpace 4 I x)
      (F₂ := Tensor0SBundle.Tensor0SModel 2 ℝ E) (V₂ := fun x : M => Tensor0SBundle.Tensor0SSpace 2 I x)
      (φ := fun p : M × ℝ =>
        DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck.cometricDoubleTraceFib (I := I)
          (realizedFam (I := I) g₀ T T' hδ hδ' p.2) 2 p.1)
      (S := realizedSmallSet (δ := δ) (δ' := δ'))
    intro Y
    -- joint smoothness of `Y` pulled back via `fst`.
    have hYjoint : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 4 ℝ E)) ∞
        (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 4 ℝ E)
          (E := fun z : M => Tensor0SBundle.Tensor0SSpace 4 I z) p.1 (Y p.1))
        ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) :=
      Y.contMDiff.comp_contMDiffOn contMDiffOn_fst
    -- the joint `{0, 1}`-double trace of `Y` (the named cometric-double-trace keystone, `p = 2`).
    exact cometricDoubleTraceFib_realizedFam_jointContMDiffOn (I := I) (p := 2) g₀ T T' hδ hδ'
      (fun p : M × ℝ => Y p.1) hYjoint
  refine hsection.congr (fun p _ => ?_)
  rw [ricciArmPrincipalCoeffPure_toSection]

/-- **Continuity-in-`s` slice of the PURE order-`2` principal coefficient along the realized path.**

The continuity slice of the joint `(s, x)`-smoothness `ricciArmPrincipalCoeffPure_realizedFam_jointContMDiff`:
at every fixed base point `x`, the model-fibre value
`s ↦ (ricciArmPrincipalCoeffPure g₀ g_s).toSection x |>.toModel` is continuous on the realized small set.
Obtained by `jointContMDiff_toModel_continuous_slice`, the same slice extraction used for the combined
coefficient. -/
theorem ricciArmPrincipalCoeffPure_realizedFam_toModel_continuous [BoundarylessManifold I M]
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) :
    ContinuousOn (fun t : ℝ =>
      Tensor0SBundle.TensorRSSpace.toModel
        ((ricciArmPrincipalCoeffPure (I := I) g₀
            (realizedFam (I := I) g₀ T T' hδ hδ' t)).toSection x))
      (realizedSmallSet (δ := δ) (δ' := δ')) := by
  have hjoint := ricciArmPrincipalCoeffPure_realizedFam_jointContMDiff (I := I) g₀ T T' hδ hδ'
  exact jointContMDiff_toModel_continuous_slice (I := I) g₀ 4 2
    (fun t => ricciArmPrincipalCoeffPure (I := I) g₀
      (realizedFam (I := I) g₀ T T' hδ hδ' t)) (realizedSmallSet (δ := δ) (δ' := δ')) hjoint x

/-- **Continuity in `s` of the per-arm `unitModel`/`appCc` read-offs of the linearized-Ricci
coefficient families (the deep mean-value continuity input).**

For the realized metric path `g_s = realizedFam g₀ T T' s`, each per-arm scalar read-off
`s ↦ unitModel g₀ 2 (appCc (Rₘfib s) Wₘ) x v` of the order-`0` coefficient `ricciArmOrder0Coeff s` (on
`W₀ = T − T'`) and the order-`2` coefficient `ricciArmOrder2Coeff s` (on `W₂ = ∇₀²(T − T')`) is
continuous on the closed interval `[0, 1]`.

This is the analytic half of the deep mean-value input: the chart Gram of `g_s` is a convex combination
of the two endpoint Grams (`realizedFam_chartGramOnE`), hence smooth — indeed real-analytic — in `s`, so
its Christoffel, Riemann/Ricci, and cometric jets (which build the two coefficient fibre operators
`ricciArmOrder0CurvCoeff` and `ricciArmPrincipalCoeff`) are continuous in `s`.  This is proved here
by reducing each read-off to the fixed continuous-linear chain `T ↦ ((T) (toModel u)) v`
(`appCc_unitModel_read_continuousOn_of_toModel_continuousOn`) applied to the model-fibre value of the
coefficient family, whose `s`-continuity on the realized small set is the continuity slice of the joint
`(s, x)`-smoothness keystone (`ricciArmOrder0CurvCoeff_realizedFam_toModel_continuous` /
`ricciArmPrincipalCoeff_realizedFam_toModel_continuous`, each `ContinuousOn realizedSmallSet`), then
restricting the resulting continuity to `[0, 1] ⊆ realizedSmallSet`.  It genuinely constrains the
read-off to be continuous, so it is non-vacuous. -/
theorem ricciArmCoeff_appCc_read_continuousOn
    (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (v : Fin 2 → TangentSpace I x) :
    ContinuousOn
        (fun s => unitModel (I := I) (M := M) g₀ 2
          (appCc (I := I) (M := M) g₀ 2 2
            (ricciArmOrder0Coeff (I := I) g₀ T T' hδ hδ' s)
            (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T'))) x v)
        (Set.Icc (0 : ℝ) 1) ∧
      ContinuousOn
        (fun s => unitModel (I := I) (M := M) g₀ 2
          (appCc (I := I) (M := M) g₀ 4 2
            (ricciArmOrder2Coeff (I := I) g₀ T T' hδ hδ' s)
            (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))) x v)
        (Set.Icc (0 : ℝ) 1) := by
  have hIcc : Set.Icc (0 : ℝ) 1 ⊆ realizedSmallSet (δ := δ) (δ' := δ') :=
    Icc_subset_realizedSmallSet hδ_lt hδ'_lt
  refine ⟨?_, ?_⟩
  · -- Order-`0` arm: the read-off is a fixed CLM of `s ↦ toModel ((ricciArmOrder0Coeff s).toSection x)`,
    -- continuous on the small set by the order-`0` continuity slice of the joint-smoothness keystone,
    -- then restricted to `[0, 1] ⊆ realizedSmallSet`.
    exact (appCc_unitModel_read_continuousOn_of_toModel_continuousOn (I := I) g₀ 2
      (fun s => ricciArmOrder0Coeff (I := I) g₀ T T' hδ hδ' s)
      (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T'))
      (ricciArmOrder0CurvCoeff_realizedFam_toModel_continuous (I := I) g₀ T T' hδ hδ' x) v).mono hIcc
  · -- Order-`2` arm: same, via the PURE order-`2` continuity slice (`ricciArmOrder2Coeff` is now the pure
    -- rough-Laplacian coefficient `ricciArmPrincipalCoeffPure`).
    exact (appCc_unitModel_read_continuousOn_of_toModel_continuousOn (I := I) g₀ 4
      (fun s => ricciArmOrder2Coeff (I := I) g₀ T T' hδ hδ' s)
      (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))
      (ricciArmPrincipalCoeffPure_realizedFam_toModel_continuous (I := I) g₀ T T' hδ hδ' x) v).mono hIcc

/-- **The pointwise-in-`s` Lichnerowicz `appCc` coefficient families of the linearized Ricci
operator (with `s`-continuous read-offs).**

For the realized metric path `g_s = realize(g₀, (1 - s)·T' + s·T)`, this is the deep chart-derivative
→ intrinsic-Lichnerowicz bridge: there are continuous-in-`s` coefficient families
`R₀fib(s) : (2,2)` (the order-`0` curvature field of `g_s`,
`exists_GcurvSection_eq_appCc_curvatureOpField`) and `R₂fib(s) : (4,2)` (the order-`2` rough-Laplacian
combined-trace field of `g_s`, `ricciArmPrincipalCoeff g₀ g_s`) such that, at every interior parameter
`s ∈ (0,1)`, the linearized Ricci value `linearizedRicciAt g_s (T - T')_x(v 0, v 1)` is the two-term
`unitModel`/`appCc` read-off on `W₀ = (T - T')` and `W₂ = ∇₀²(T - T')`, AND such that each per-arm
read-off `s ↦ unitModel g₀ 2 (appCc (Rₘfib s) Wₘ) x v` is continuous on the closed interval `[0,1]`.

This is the irreducible deep mean-value content of the Ricci-arm linearization: connecting the genuine
`s`-derivative of the realized chart Ricci `deriv (realizedRicciChartSum)` (the affine chart-Christoffel
→ Riemann polynomial differentiated in `s`, `linearizedRicciAt_eq_deriv_chartSum_on_Ioo`) to the
intrinsic two-term Lichnerowicz `appCc` form runs through (i) the per-`s` chart principal-symbol closed
form `ricciSymbolComp_eq_closedForm` (the four classical `∂²h` terms reorganising into the rough
Laplacian `−½|ξ|²h` plus the divergence/trace-gradient gauge terms, NO genuine order-`1` arm) and (ii)
the chart-trace → intrinsic `appCc` transfer of each piece, the same Palatini-trace ↔ `appCc`/`unitModel`
bridge (`ricciArmPrincipalCoeff_appCc_eq_combinedTrace`, `palatini_tracedPrincipal_eq_combinedTrace`)
and `∇^{g_s} ↔ ∇₀` conversion that the eval-matching of the sibling arms posits.  These covariant
bridges are not yet on disk; the construction is *posited* here as the single deferred mean-value input,
to be discharged by recursing into them.  The predicate genuinely constrains the families to reproduce
the actual linearized-Ricci value pointwise, so it is non-vacuous: the zero families fail it where the
linearized Ricci is nonzero. -/
theorem exists_linearizedRicci_pointwise_appCc_families
    (g₀ g_bg : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ') :
    ∃ (R₀fib : ℝ → SmoothCcTensor g₀ 2 2) (R₂fib : ℝ → SmoothCcTensor g₀ 4 2),
      (∀ (s : ℝ), s ∈ Set.Ioo (0 : ℝ) 1 → ∀ (x : M) (v : Fin 2 → TangentSpace I x),
        deriv (realizedDeTurckRicciChartSum (I := I) g₀ g_bg T T' hδ hδ' x (v 0) (v 1)) s =
          unitModel (I := I) (M := M) g₀ 2
            (appCc (I := I) (M := M) g₀ 2 2 (R₀fib s)
                (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T'))
              + appCc (I := I) (M := M) g₀ 4 2 (R₂fib s)
                  (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))) x v) ∧
      (∀ (x : M) (v : Fin 2 → TangentSpace I x), ContinuousOn
        (fun s => unitModel (I := I) (M := M) g₀ 2
          (appCc (I := I) (M := M) g₀ 2 2 (R₀fib s)
            (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T'))) x v)
        (Set.Icc (0 : ℝ) 1)) ∧
      (∀ (x : M) (v : Fin 2 → TangentSpace I x), ContinuousOn
        (fun s => unitModel (I := I) (M := M) g₀ 2
          (appCc (I := I) (M := M) g₀ 4 2 (R₂fib s)
            (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))) x v)
        (Set.Icc (0 : ℝ) 1)) := by
  refine ⟨ricciArmOrder0Coeff (I := I) g₀ T T' hδ hδ',
    ricciArmOrder2Coeff (I := I) g₀ T T' hδ hδ', ?_, ?_, ?_⟩
  · -- The pointwise identity on `Ioo 0 1`: the combined chart-derivative → intrinsic `appCc` transfer.
    intro s hs x v
    exact deriv_realizedDeTurckRicciChartSum_eq_appCc_pointwise (I := I) g₀ g_bg T T' hδ_lt hδ hδ'_lt hδ'
      hs x v
  · -- The order-`0` read-off continuity (first conjunct of the posited continuity bridge).
    intro x v
    exact (ricciArmCoeff_appCc_read_continuousOn (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x v).1
  · -- The order-`2` read-off continuity (second conjunct of the posited continuity bridge).
    intro x v
    exact (ricciArmCoeff_appCc_read_continuousOn (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x v).2

/-- **The pointwise-in-`s` Lichnerowicz `appCc` form of the linearized Ricci operator.**

For the realized metric path `g_s = realize(g₀, (1 - s)·T' + s·T)`, the linearized Ricci operator
`linearizedRicciAt g_s (T - T')` at every interior parameter `s ∈ (0,1)` is the two-term Lichnerowicz
`unitModel`/`appCc` read-off of an order-`0` curvature field `R₀fib(s) : (2,2)` acting on
`W₀ = (T - T')` and an order-`2` rough-Laplacian double-trace field `R₂fib(s) : (4,2)` acting on
`W₂ = ∇₀²(T - T')`:
```
DRic(g_s)[T - T']_x(v 0, v 1) = unitModel g₀ 2 (appCc (R₀fib s) W₀ + appCc (R₂fib s) W₂) x v,  s ∈ (0,1),
```
with the per-base-point fibre families `s ↦ (R₀fib s).toSection x`, `s ↦ (R₂fib s).toSection x`
interval-integrable on `[0,1]`.

This is the classical Lichnerowicz structure of the linearized Ricci operator: the principal part is
the rough Laplacian `−½Δ_{g_s} h` (order `2`, the second covariant gradient `∇₀²`), the remainder is
the order-`0` curvature action (`Rm·h`, `Ric∘h`), and the order-`1` connection part has vanishing
contribution (its chart principal symbol is the closed form `−½|ξ|²h + curvature`,
`ricciSymbolComp_eq_closedForm`).  The principal coefficient `R₂fib(g_s)` is the chart-symbol
double-trace field; the curvature coefficient `R₀fib(g_s)` is the curvature operator field
(`exists_GcurvSection_eq_appCc_curvatureOpField`).  Connecting `linearizedRicciAt :=
deriv (realizedRicciPathValue)` to this Lichnerowicz form runs through the joint-Gram-`C∞`
chart-derivative tower (`realizedRicciChartSum_contDiffAt`) and the chart-symbol bridge.  This deep
chart-derivative → intrinsic-Lichnerowicz-`appCc` content is *posited* as the single deferred
mean-value input, to be discharged by recursing into the chart-symbol / `∇^{g_s} ↔ ∇₀` covariant
bridges.  The predicate genuinely constrains the families to reproduce the actual linearized-Ricci
value pointwise, so it is non-vacuous: the zero families fail it where the linearized Ricci is
nonzero. -/
theorem linearizedRicci_pointwise_appCc
    (g₀ g_bg : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ') :
    ∃ (R₀fib : ℝ → SmoothCcTensor g₀ 2 2) (R₂fib : ℝ → SmoothCcTensor g₀ 4 2),
      (∀ (s : ℝ), s ∈ Set.Ioo (0 : ℝ) 1 → ∀ (x : M) (v : Fin 2 → TangentSpace I x),
        deriv (realizedDeTurckRicciChartSum (I := I) g₀ g_bg T T' hδ hδ' x (v 0) (v 1)) s =
          unitModel (I := I) (M := M) g₀ 2
            (appCc (I := I) (M := M) g₀ 2 2 (R₀fib s)
                (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T'))
              + appCc (I := I) (M := M) g₀ 4 2 (R₂fib s)
                  (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))) x v) ∧
      (∀ (x : M) (v : Fin 2 → TangentSpace I x), IntervalIntegrable
        (fun s => unitModel (I := I) (M := M) g₀ 2
          (appCc (I := I) (M := M) g₀ 2 2 (R₀fib s)
            (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T'))) x v)
        MeasureTheory.volume 0 1) ∧
      (∀ (x : M) (v : Fin 2 → TangentSpace I x), IntervalIntegrable
        (fun s => unitModel (I := I) (M := M) g₀ 2
          (appCc (I := I) (M := M) g₀ 4 2 (R₂fib s)
            (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))) x v)
        MeasureTheory.volume 0 1) := by
  -- The deep chart-derivative → intrinsic Lichnerowicz bridge supplies the continuous-in-`s`
  -- coefficient families together with the pointwise identity; the two per-arm interval-integrabilities
  -- are then the `ContinuousOn`-on-`[0,1]` read-offs integrated (`intervalIntegrable_of_Icc`).
  obtain ⟨R₀fib, R₂fib, hpt, hcont₀, hcont₂⟩ :=
    exists_linearizedRicci_pointwise_appCc_families (I := I) (M := M) g₀ g_bg T T'
      hδ_lt hδ hδ'_lt hδ'
  refine ⟨R₀fib, R₂fib, hpt, fun x v => ?_, fun x v => ?_⟩
  · exact (hcont₀ x v).intervalIntegrable_of_Icc (zero_le_one)
  · exact (hcont₂ x v).intervalIntegrable_of_Icc (zero_le_one)

/-- **The fibre Bochner path integral of a smooth operator-field coefficient family, read off
through `unitModel`/`appCc`.**

For a family `Φ : ℝ → SmoothCcTensor g₀ r 2` of operator-field coefficients and a fixed contracted
`(0, r)`-tensor `W : SmoothCcTensor g₀ 0 r`, such that the scalar read-off
`s ↦ unitModel g₀ 2 (appCc (Φ s) W) x v` is interval-integrable on `[0,1]` at every base point `x` and
tangent pair `v`, there is an integrated coefficient `IΦ : SmoothCcTensor g₀ r 2` (a smooth
compactly-supported tensor) — the fibre Bochner path integral `IΦ.toSection x = ∫₀¹ (Φ s).toSection x ds`
— whose `unitModel`/`appCc` read-off is the `s`-integral of the per-`s` read-offs:
```
unitModel g₀ 2 (appCc IΦ W) x v = ∫₀¹ unitModel g₀ 2 (appCc (Φ s) W) x v ds.
```

This packages two pieces: the smooth-parametric-integral construction (each fibre `TensorRSSpace r 2 I x`
is finite-dimensional, hence Banach, so the pointwise Bochner integral is well defined; smoothness in `x`
follows from the joint `(s,x)`-smoothness of the family through differentiation under the integral sign,
and compact support from the closed manifold) together with the `appCc`/`unitModel` ↔ `intervalIntegral`
swap (the fibrewise composition `A ↦ A.comp (W x)`, the section value at the unit, the model read-off,
and the evaluation at `v` are each fixed continuous-linear in the integrated coefficient, so the Bochner
integral commutes with them — `ContinuousLinearMap.intervalIntegral_comp_comm`).  It is *posited* here as
the missing smooth-parametric-integral infrastructure, recursed into downstream.  The predicate genuinely
constrains `IΦ` to reproduce the actual fibrewise path-integral read-off of `Φ`, so it is non-vacuous:
the zero coefficient fails it whenever the path-integral read-off of `Φ` is nonzero. -/
theorem exists_pathIntegralCoeffField
    (g₀ : SmoothRiemannianMetric I M) (r : ℕ)
    (Φ : ℝ → SmoothCcTensor g₀ r 2) (W : SmoothCcTensor g₀ 0 r)
    (S : Set ℝ) (hS : IsOpen S) (hSI : Set.uIcc (0:ℝ) 1 ⊆ S)
    (hjoint : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel r 2 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel r 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace r 2 I z) p.1 ((Φ p.2).toSection p.1))
      ((Set.univ : Set M) ×ˢ S))
    (hcont : ∀ x : M, ContinuousOn (fun t : ℝ =>
      Tensor0SBundle.TensorRSSpace.toModel ((Φ t).toSection x)) S) :
    ∃ IΦ : SmoothCcTensor g₀ r 2,
      ∀ (x : M) (v : Fin 2 → TangentSpace I x),
        unitModel (I := I) (M := M) g₀ 2 (appCc (I := I) (M := M) g₀ r 2 IΦ W) x v =
          ∫ s in (0 : ℝ)..1,
            unitModel (I := I) (M := M) g₀ 2 (appCc (I := I) (M := M) g₀ r 2 (Φ s) W) x v := by
  -- The smooth-parametric fibre Bochner path integral of the jointly-smooth family `Φ`.
  refine ⟨pathIntegralCoeffField (I := I) (M := M) g₀ r 2 Φ S hS hSI hjoint, fun x v => ?_⟩
  -- Its `appCc`/`unitModel` read-off is the `s`-integral of the per-`s` read-offs (the swap).
  exact pathIntegralCoeffField_appCc_eq (I := I) (M := M) g₀ r 2 Φ W S hS hSI hjoint hcont x v

/-! ## The integrated linearized-Ricci `appCc` form (the Lichnerowicz mean-value content) -/

/-- **The integrated linearized-Ricci operator in single-arm Lichnerowicz `appCc` form.**

For the realized metric path `g_s = realize(g₀, (1 - s)·T' + s·T)` joining `realize(g₀, T')` to
`realize(g₀, T)`, the `s`-integral over `[0,1]` of the linearized Ricci operator
`linearizedRicciAt g_s (T - T')` (the integrand of the mean-value reduction
`ricciTensor_realized_sub_eq_integral_linearizedRicci`), scaled by `(-2)`, is the order-graded
`unitModel`/`appCc` read-off of a *two-term* (order-`0` and order-`2`) Lichnerowicz decomposition on
the iterated covariant gradients `W₀ = (T - T')` and `W₂ = ∇₀²(T - T')` of the perturbation
difference:
```
(-2)·∫₀¹ DRic(g_s)[T - T']_x(v 0, v 1) ds
  = unitModel g₀ 2 (appCc g₀ 2 2 R₀ W₀ + appCc g₀ 4 2 R₂ W₂) x v.
```

This is the classical **Lichnerowicz** structure of the linearized Ricci operator: the principal
part is the rough Laplacian `−½Δ_{g_s} h` (order `2`, the second covariant gradient `∇₀²`), and the
remainder is the order-`0` curvature action (`Rm·h`, `Ric∘h`).  The linearized Ricci has *no genuine
order-`1` arm*: the connection part is the order-`1` piece, whose contribution vanishes in a normal
frame (its chart principal symbol is the closed form `−½|ξ|²h + curvature`,
`ricciSymbolComp_eq_closedForm`), so the only surviving orders after integration are `0` and `2`.
The order-`2` PRINCIPAL coefficient is the integrated rough-Laplacian double-trace field
`R₂ = (-2)∫₀¹ R₂(g_s) ds` and the order-`0` coefficient is the integrated curvature field
`R₀ = (-2)∫₀¹ R₀(g_s) ds`, both bounded operator-field path integrals (the path metric `g_s` stays
`g₀`-fibre small with constant `< 1` on `[0,1]`).

This is the irreducible deep mean-value/Leibniz content of the Ricci arm rebuilt on the mean-value
foundation: the pointwise-in-`s` Lichnerowicz `appCc` form of `DRic(g_s)` (chart principal symbol →
intrinsic `appCc`) together with the operator-field path integration (`∫ appCc R(g_s) W ds =
appCc (∫ R(g_s) ds) W` by `appCc`-linearity in the coefficient and `intervalIntegral` linearity,
producing the integrated coefficient fields `R₀, R₂` as smooth compactly-supported tensors).  It is
*posited* here as the single deferred input, recursed into downstream.  The predicate genuinely
constrains `(R₀, R₂)` to *reproduce the actual `(-2)`-scaled integrated linearized-Ricci value*, so
it is non-vacuous: the zero pair fails it on any background where the integrated linearized Ricci is
nonzero. -/
theorem integratedLinearizedRicci_appCc_eq
    (g₀ g_bg : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ') :
    ∃ (R₀ : SmoothCcTensor g₀ 2 2) (R₂ : SmoothCcTensor g₀ 4 2),
      ∀ (x : M) (v : Fin 2 → TangentSpace I x),
        (∫ s in (0 : ℝ)..1,
              deriv (realizedDeTurckRicciChartSum (I := I) g₀ g_bg T T' hδ hδ' x (v 0) (v 1)) s) =
          unitModel (I := I) (M := M) g₀ 2
            (appCc (I := I) (M := M) g₀ 2 2 R₀
                (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T'))
              + appCc (I := I) (M := M) g₀ 4 2 R₂
                  (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))) x v := by
  classical
  -- The deep mean-value inputs, on the CONCRETE order-`0`/order-`2` coefficient families
  -- `R₀fib = ricciArmOrder0Coeff`, `R₂fib = ricciArmOrder2Coeff`: the pointwise combined Lichnerowicz
  -- `appCc` form (gauge cancelled) together with the per-arm read-off continuity/interval-integrability
  -- supplied by the joint `(s, x)`-smoothness keystone's continuity slices.
  set R₀fib : ℝ → SmoothCcTensor g₀ 2 2 := ricciArmOrder0Coeff (I := I) g₀ T T' hδ hδ' with hR₀fib
  set R₂fib : ℝ → SmoothCcTensor g₀ 4 2 := ricciArmOrder2Coeff (I := I) g₀ T T' hδ hδ' with hR₂fib
  -- Pointwise combined Lichnerowicz `appCc` form on `Ioo 0 1` (combined chart-derivative → intrinsic
  -- two-term form, gauge cancelled).
  have hpt : ∀ (s : ℝ), s ∈ Set.Ioo (0 : ℝ) 1 → ∀ (x : M) (v : Fin 2 → TangentSpace I x),
      deriv (realizedDeTurckRicciChartSum (I := I) g₀ g_bg T T' hδ hδ' x (v 0) (v 1)) s =
        unitModel (I := I) (M := M) g₀ 2
          (appCc (I := I) (M := M) g₀ 2 2 (R₀fib s)
              (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T'))
            + appCc (I := I) (M := M) g₀ 4 2 (R₂fib s)
                (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))) x v := by
    intro s hs x v
    exact deriv_realizedDeTurckRicciChartSum_eq_appCc_pointwise (I := I) g₀ g_bg T T' hδ_lt hδ hδ'_lt hδ'
      hs x v
  -- Per-arm read-off interval-integrability from the keystone's continuity slices on `[0,1]`.
  have hcontRead := ricciArmCoeff_appCc_read_continuousOn (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ'
  have hint₀ : ∀ (x : M) (v : Fin 2 → TangentSpace I x), IntervalIntegrable
      (fun s => unitModel (I := I) (M := M) g₀ 2
        (appCc (I := I) (M := M) g₀ 2 2 (R₀fib s)
          (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T'))) x v)
      MeasureTheory.volume 0 1 :=
    fun x v => ((hcontRead x v).1).intervalIntegrable_of_Icc zero_le_one
  have hint₂ : ∀ (x : M) (v : Fin 2 → TangentSpace I x), IntervalIntegrable
      (fun s => unitModel (I := I) (M := M) g₀ 2
        (appCc (I := I) (M := M) g₀ 4 2 (R₂fib s)
          (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))) x v)
      MeasureTheory.volume 0 1 :=
    fun x v => ((hcontRead x v).2).intervalIntegrable_of_Icc zero_le_one
  -- The joint `(s, x)`-smoothness keystone (`hjoint`) and its continuity slice (`hcont`) for each arm.
  have hSopen : IsOpen (realizedSmallSet (δ := δ) (δ' := δ')) := realizedSmallSet_isOpen
  have hSI : Set.uIcc (0:ℝ) 1 ⊆ realizedSmallSet (δ := δ) (δ' := δ') := by
    rw [Set.uIcc_of_le (zero_le_one)]
    exact Icc_subset_realizedSmallSet hδ_lt hδ'_lt
  obtain ⟨IΦ₀, heval₀⟩ :=
    exists_pathIntegralCoeffField (I := I) (M := M) g₀ 2 R₀fib
      (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T'))
      (realizedSmallSet (δ := δ) (δ' := δ')) hSopen hSI
      (ricciArmOrder0CurvCoeff_realizedFam_jointContMDiff (I := I) g₀ T T' hδ hδ')
      (fun x => ricciArmOrder0CurvCoeff_realizedFam_toModel_continuous (I := I) g₀ T T' hδ hδ' x)
  obtain ⟨IΦ₂, heval₂⟩ :=
    exists_pathIntegralCoeffField (I := I) (M := M) g₀ 4 R₂fib
      (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))
      (realizedSmallSet (δ := δ) (δ' := δ')) hSopen hSI
      (ricciArmPrincipalCoeffPure_realizedFam_jointContMDiff (I := I) g₀ T T' hδ hδ')
      (fun x => ricciArmPrincipalCoeffPure_realizedFam_toModel_continuous (I := I) g₀ T T' hδ hδ' x)
  -- The integrated coefficient fields are the fibre path integrals (the combined operator already
  -- carries the `−2` Ricci scaling, so no extra scaling is needed here).
  refine ⟨IΦ₀, IΦ₂, fun x v => ?_⟩
  set W₀ : SmoothCcTensor g₀ 0 2 := iteratedCovGrad (I := I) g₀ 0 2 0 (T - T') with hW₀
  set W₂ : SmoothCcTensor g₀ 0 4 := iteratedCovGrad (I := I) g₀ 0 2 2 (T - T') with hW₂
  -- Push the `unitModel`/`appCc` additivity through the RHS, distributing the evaluation at the tuple
  -- `v`, reducing it to `unitModel (appCc IΦ₀ W₀) x v + unitModel (appCc IΦ₂ W₂) x v`.
  have hrhs :
      unitModel (I := I) (M := M) g₀ 2
          (appCc (I := I) (M := M) g₀ 2 2 IΦ₀ W₀
            + appCc (I := I) (M := M) g₀ 4 2 IΦ₂ W₂) x v =
        unitModel (I := I) (M := M) g₀ 2 (appCc (I := I) (M := M) g₀ 2 2 IΦ₀ W₀) x v +
          unitModel (I := I) (M := M) g₀ 2 (appCc (I := I) (M := M) g₀ 4 2 IΦ₂ W₂) x v := by
    rw [unitModel_add_left, ContinuousMultilinearMap.add_apply]
  rw [hrhs]
  -- The two per-term path-integral swaps (`unitModel ∘ appCc` commutes with the `s`-integral).
  rw [heval₀ x v, heval₂ x v]
  -- The integrand splits as the sum of the two per-order read-offs; combine via `intervalIntegral`
  -- additivity and the a.e. pointwise Lichnerowicz form on `Ioo 0 1` (= `Ioc 0 1` up to a null set).
  have hii₀ : IntervalIntegrable
      (fun s => unitModel (I := I) (M := M) g₀ 2 (appCc (I := I) (M := M) g₀ 2 2 (R₀fib s) W₀) x v)
      MeasureTheory.volume 0 1 := hint₀ x v
  have hii₂ : IntervalIntegrable
      (fun s => unitModel (I := I) (M := M) g₀ 2 (appCc (I := I) (M := M) g₀ 4 2 (R₂fib s) W₂) x v)
      MeasureTheory.volume 0 1 := hint₂ x v
  rw [← intervalIntegral.integral_add hii₀ hii₂]
  -- Replace `linearizedRicciAt` by its pointwise Lichnerowicz `appCc` form a.e. on `Ι 0 1 = Ioc 0 1`
  -- (the pointwise form holds on the open `Ioo 0 1`, which agrees with `Ioc 0 1` up to the null
  -- set `{1}`).
  refine intervalIntegral.integral_congr_ae ?_
  -- The bad set `{s | ¬(s ∈ Ι 0 1 → f s = g s)} ⊆ {1}` is volume-null.
  refine MeasureTheory.measure_mono_null (t := {(1 : ℝ)}) (fun s hs => ?_)
    (MeasureTheory.measure_singleton 1)
  -- `hs : ¬(s ∈ Ι 0 1 → f s = g s)`; show `s = 1` by contradiction.
  rw [Set.mem_singleton_iff]
  by_contra hne1
  apply hs
  intro hsmem
  rw [Set.mem_uIoc] at hsmem
  rcases hsmem with ⟨hs0, hs1⟩ | ⟨hs1, hs0⟩
  · -- `s ∈ Ioc 0 1` and `s ≠ 1`, so `s ∈ Ioo 0 1`: the pointwise Lichnerowicz form applies.
    rw [hpt s ⟨hs0, lt_of_le_of_ne hs1 hne1⟩ x v, unitModel_add_left,
      ContinuousMultilinearMap.add_apply]
  · -- `s ∈ Ioc 1 0` is empty (would need `1 < s` and `s ≤ 0`).
    exact absurd (lt_of_lt_of_le hs1 hs0) (by norm_num)

/-! ## The combined-operator mean-value (FTC) foundation -/

/-- **(Posited deep input — the mean-value (FTC) reduction of the combined Ricci–DeTurck-operator
difference.)**

For two endpoint perturbation tensor sections `T, T'`, both `g₀`-fibre small with constant `< 1`, the
chart read-off of the difference of the two realized **combined** Ricci–DeTurck right-hand sides
`deTurckRicciRHS g_bg g₁ − deTurckRicciRHS g_bg g₁'` (with `g₁ = realize(g₀ + T)`,
`g₁' = realize(g₀ + T')`) at the base chart point equals the `s`-integral over `[0,1]` of the
`s`-derivative of the realized combined chart sum `realizedDeTurckRicciChartSum`:
```
(deTurckRicciRHS g_bg g₁ − deTurckRicciRHS g_bg g₁')_x(v 0, v 1)
  = ∫₀¹ (d/ds) realizedDeTurckRicciChartSum g_s x(v0, v1) ds.
```

This is the combined-operator analogue of the on-disk bare-Ricci mean-value FTC
`ricciTensor_realized_sub_eq_integral_linearizedRicci`: the realized combined chart sum
`realizedDeTurckRicciChartSum` is jointly `C^∞` in `(s, x)` on a neighbourhood of `[0,1]` (the chart
Gram of `g_s` is a convex combination of the two endpoint Grams, hence smooth in `s`, and
`deTurckRicciRHS = −2 Rc + 𝓛_W` is a chart-jet polynomial of it), so it is continuous on `[0,1]`,
differentiable on `(0,1)`, with derivative interval-integrable; the fundamental theorem of calculus then
equates the integral to the endpoint difference `realizedDeTurckRicciChartSum 1 −
realizedDeTurckRicciChartSum 0`, and the chart-Riemann-basis read-off
(`deTurckRicciRHS_chartBasisVecFiber_eq_chartDeTurckRicciRHS`) identifies the two endpoints with the
genuine intrinsic combined operator values at `g₁`, `g₁'`.  This analytic FTC-with-endpoint-readoff
content (the joint-Gram smoothness of the combined chart sum + the intrinsic↔chart-sum endpoint bridge
for the combined operator) is the same kind of analytic input as the on-disk bare-Ricci FTC; it is
*posited* here, to be discharged by recursing into the combined joint-Gram smoothness tower.  It
genuinely constrains the chart integral to reproduce the combined operator difference, so it is
non-vacuous: it fails wherever the combined operator difference is nonzero. -/
theorem deTurckRicciRHS_realized_sub_eq_integral_chartDeriv
    (g₀ g_bg : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (v w : TangentSpace I x) :
    DifferentialGeometry.PDE.RicciFlow.deTurckRicciRHS (I := I) g_bg
          (tensorSectionRealizeMetric (I := I) g₀ T hδ_lt hδ) x v w -
        DifferentialGeometry.PDE.RicciFlow.deTurckRicciRHS (I := I) g_bg
          (tensorSectionRealizeMetric (I := I) g₀ T' hδ'_lt hδ') x v w =
      ∫ s in (0 : ℝ)..1,
        deriv (realizedDeTurckRicciChartSum (I := I) g₀ g_bg T T' hδ hδ' x v w) s :=
  sorry

/-! ## The order-graded `appCc` decomposition (Ricci arm) -/

/-- **The Ricci–DeTurck combined-arm order-graded `appCc` eval-matching (via the mean-value
Lichnerowicz integration, gauge cancelled).**

There exist endpoint-dependent operator coefficient fields
```
R₀ : SmoothCcTensor g₀ 2 2,   R₁ : SmoothCcTensor g₀ 3 2,   R₂ : SmoothCcTensor g₀ 4 2,
```
reproducing the `(−2)`-scaled difference of the two realized Ricci tensors `Ric(g₁) − Ric(g₁')` (with
`g₁ = realize(g₀ + T)`, `g₁' = realize(g₀ + T')`) as the `unitModel`/`appCc` order-graded read-off on the
iterated covariant gradients `Wₘ = iteratedCovGrad g₀ 0 2 m (T − T')` of the perturbation difference
`S = T − T'`.  This is the eval-matching half of the strengthened grading node
`deTurckRicciArm_appCc_graded`; its order-`0` `C⁰` and order-`a` `L²` coefficient controls are proved on
top of it by the fixed-field compactness bound.

The Ricci-arm difference is rebuilt here on the **mean-value (FTC) foundation**, replacing the
single-endpoint Palatini telescope (which leaves un-capturable two-endpoint cross terms).  The classical
mean-value identity `ricciTensor_realized_sub_eq_integral_linearizedRicci` expresses the difference as
the `s`-integral of the linearized Ricci operator along the convex metric path `g_s`:
```
Ric(g₁)_x(v 0, v 1) − Ric(g₁')_x(v 0, v 1) = ∫₀¹ DRic(g_s)[T − T']_x(v 0, v 1) ds.
```
The integrated linearized Ricci is the single-arm Lichnerowicz form
`integratedLinearizedRicci_appCc_eq`: a *two-term* (order-`0` curvature, order-`2` rough Laplacian)
`appCc` read-off, with **no genuine order-`1` arm** (the connection part integrates away — the combined
chart principal symbol is the gauge-cancelled rough Laplacian `|ξ|²h`).  So the eval holds with `R₁ = 0`:
the combined FTC rewrites the LHS to the integral, the Lichnerowicz integration supplies `R₀, R₂`, and the
order-`1` read-off `appCc 0 W₁` vanishes (`appCc_zero_left`).  The deep mean-value/Leibniz content (the
combined pointwise-in-`s` Lichnerowicz `appCc` form together with the operator-field path integration
producing `R₀, R₂` as smooth fields) is *posited* in `integratedLinearizedRicci_appCc_eq` and the combined
FTC `deTurckRicciRHS_realized_sub_eq_integral_chartDeriv` (the deferred inputs, recursed into downstream);
this node combines them.  The predicate genuinely constrains `(R₀, R₁, R₂)` to *reproduce the combined
Ricci–DeTurck-arm value*, so it is non-vacuous: it fails for the zero triple whenever the realized combined
arm is nonzero. -/
theorem deTurckRicciArm_appCc_eval
    (g₀ g_bg : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ') :
    ∃ (R₀ : SmoothCcTensor g₀ 2 2) (R₁ : SmoothCcTensor g₀ 3 2) (R₂ : SmoothCcTensor g₀ 4 2),
      ∀ (x : M) (v : Fin 2 → TangentSpace I x),
        (DifferentialGeometry.PDE.RicciFlow.deTurckRicciRHS (I := I) g_bg
              (tensorSectionRealizeMetric (I := I) g₀ T hδ_lt hδ) x (v 0) (v 1)
            - DifferentialGeometry.PDE.RicciFlow.deTurckRicciRHS (I := I) g_bg
                (tensorSectionRealizeMetric (I := I) g₀ T' hδ'_lt hδ') x (v 0) (v 1)) =
          unitModel (I := I) (M := M) g₀ 2
            (appCc (I := I) (M := M) g₀ 2 2 R₀
                (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T'))
              + appCc (I := I) (M := M) g₀ 3 2 R₁
                  (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T'))
              + appCc (I := I) (M := M) g₀ 4 2 R₂
                  (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))) x v := by
  classical
  -- The integrated combined Lichnerowicz `appCc` form supplies the order-`0`/order-`2` coefficient
  -- fields; the order-`1` arm is absent (`R₁ = 0`).
  obtain ⟨R₀, R₂, heval⟩ :=
    integratedLinearizedRicci_appCc_eq (I := I) (M := M) g₀ g_bg T T' hδ_lt hδ hδ'_lt hδ'
  refine ⟨R₀, 0, R₂, fun x v => ?_⟩
  -- Rewrite the realized combined-operator difference as the FTC integral of the combined chart deriv.
  rw [deTurckRicciRHS_realized_sub_eq_integral_chartDeriv (I := I) g₀ g_bg T T' hδ_lt hδ hδ'_lt hδ'
    x (v 0) (v 1)]
  -- The order-`1` read-off `appCc 0 W₁` vanishes, collapsing the three-term sum to the two-term
  -- Lichnerowicz read-off matched by the integrated combined identity.
  rw [appCc_zero_left, add_zero]
  exact heval x v

/-- **The Ricci–DeTurck Ricci-arm order-graded `appCc` decomposition with order-`0` `C⁰` and order-`a`
`L²` coefficient control (genuine grading node).**

There exist a ball-uniform constant `Λ ≥ 0` and endpoint-dependent operator coefficient fields
```
R₀ : SmoothCcTensor g₀ 2 2,   R₁ : SmoothCcTensor g₀ 3 2,   R₂ : SmoothCcTensor g₀ 4 2,
```
such that, with `g₁ = realize(g₀ + T)` and `g₁' = realize(g₀ + T')`:

* **(eval)** the `(−2)`-scaled difference of the two realized Ricci tensors `Ric(g₁) − Ric(g₁')` is, at
  every base point `x` and on every tangent pair `v`, the `unitModel` read-off of the order-graded
  operator-field action on the iterated covariant gradients `Wₘ = iteratedCovGrad g₀ 0 2 m (T − T')` of
  the perturbation difference:
  ```
  (−2)·(Ric(g₁) − Ric(g₁'))(v 0, v 1)
    = unitModel g₀ 2 (appCc g₀ 2 2 R₀ W₀ + appCc g₀ 3 2 R₁ W₁ + appCc g₀ 4 2 R₂ W₂) x v,
    W₀ = (T − T'),  W₁ = ∇₀(T − T'),  W₂ = ∇₀²(T − T');
  ```
* **(C⁰ norm)** each coefficient field's intrinsic squared Riemannian fibre operator norm is uniformly
  bounded by `Λ²` at every base point `x`:
  ```
  rfns(R₀ x) ≤ Λ²,   rfns(R₁ x) ≤ Λ²,   rfns(R₂ x) ≤ Λ²;
  ```
* **(order-`a` `L²` norm)** at the supplied top covariant order `a`, the intrinsic squared Riemannian
  fibre norm of the order-`a` iterated covariant gradient of each coefficient field is uniformly bounded
  by `Λ²` at every base point `x`:
  ```
  rfns((∇₀^a R₀) x) ≤ Λ²,   rfns((∇₀^a R₁) x) ≤ Λ²,   rfns((∇₀^a R₂) x) ≤ Λ².
  ```
  This is the fixed-field jet content the top-order Gagliardo–Nirenberg arm of the RHS-arm tame bound
  consumes (`‖∇^a Rₘ‖_{L²}`): the `Rₘ` are fixed smooth coefficient fields reading only the order-`≤ 2`
  jets of the endpoint metrics through the `g₁⁻¹`/`∇g₁⁻¹`/`connDiff`/inverse-Gram structure, so their
  order-`a` iterated covariant gradients `∇₀^a Rₘ` are again fixed smooth compactly-supported tensors
  with a uniform fibre-norm sup on the closed manifold (the compactness bound
  `exists_bound_riemannianFiberNormSq_smoothCcTensor`, never an order-`a` `L∞` of the section — a
  loss-free `L²` window).  The order `a` is supplied as an argument and `Λ` is chosen after it (a single
  `Λ` cannot bound every covariant order at once, since a fixed smooth field's covariant-gradient norms
  grow with the order).

Both the `C⁰` and `L²` controls ride on top of the eval-matching `deTurckRicciArm_appCc_eval`: they bound
whatever concrete `Rₘ` the eval-matching constructs (and their order-`a` covariant gradients), so they are
discharged together with the eval-matching once the concrete coefficient fields are built.  The (eval)
predicate genuinely constrains `(R₀, R₁, R₂)` to *reproduce the `(−2)`-scaled Ricci-arm value*, so it is
non-vacuous: it fails for the zero triple whenever the realized Ricci arm is nonzero.

This matches the existential shape of the Lie-arm grading `deTurckLieArm_appCc_graded` (same realize-tie
hypotheses, same `unitModel`/`appCc`/`Wₘ` shape), so the `−2·Ric + 𝓛` leaf-identity glue of the
Lichnerowicz `_core` sums the two graded triples cleanly into the Ricci–DeTurck right-hand-side
difference grading.  The order-2 PRINCIPAL coefficient is closed
(`R₂ = ricciArmPrincipalCoeff g₀ g₁`, the combined three-trace whose `appCc` read-off is the traced
Palatini principal `palatini_tracedPrincipal_eq_combinedTrace`); the order-`0`/`1` eval-matching is the
single posited prerequisite. -/
theorem deTurckRicciArm_appCc_graded
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ') :
    ∃ (Λ : ℝ), 0 ≤ Λ ∧
      ∃ (R₀ : SmoothCcTensor g₀ 2 2) (R₁ : SmoothCcTensor g₀ 3 2) (R₂ : SmoothCcTensor g₀ 4 2),
        (∀ (x : M) (v : Fin 2 → TangentSpace I x),
          (DifferentialGeometry.PDE.RicciFlow.deTurckRicciRHS (I := I) g_bg
                (tensorSectionRealizeMetric (I := I) g₀ T hδ_lt hδ) x (v 0) (v 1)
              - DifferentialGeometry.PDE.RicciFlow.deTurckRicciRHS (I := I) g_bg
                  (tensorSectionRealizeMetric (I := I) g₀ T' hδ'_lt hδ') x (v 0) (v 1)) =
            unitModel (I := I) (M := M) g₀ 2
              (appCc (I := I) (M := M) g₀ 2 2 R₀
                  (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T'))
                + appCc (I := I) (M := M) g₀ 3 2 R₁
                    (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T'))
                + appCc (I := I) (M := M) g₀ 4 2 R₂
                    (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))) x v) ∧
        (∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x (R₀.toSection x) ≤ Λ ^ 2 ∧
          riemannianFiberNormSq (I := I) (M := M) g₀ 3 2 x (R₁.toSection x) ≤ Λ ^ 2 ∧
          riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x (R₂.toSection x) ≤ Λ ^ 2) ∧
        (∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + a) x
              ((iteratedCovGrad (I := I) g₀ 2 2 a R₀).toSection x) ≤ Λ ^ 2 ∧
          riemannianFiberNormSq (I := I) (M := M) g₀ 3 (2 + a) x
              ((iteratedCovGrad (I := I) g₀ 3 2 a R₁).toSection x) ≤ Λ ^ 2 ∧
          riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + a) x
              ((iteratedCovGrad (I := I) g₀ 4 2 a R₂).toSection x) ≤ Λ ^ 2) := by
  -- The eval-matching prerequisite supplies the concrete order-graded coefficient fields.
  obtain ⟨R₀, R₁, R₂, heval⟩ :=
    deTurckRicciArm_appCc_eval (I := I) (M := M) g₀ g_bg T T' hδ_lt hδ hδ'_lt hδ'
  -- The order-`0` `C⁰` control: each fixed smooth coefficient field has a uniform fibre-norm sup on the
  -- closed manifold (`exists_bound_riemannianFiberNormSq_smoothCcTensor`).
  obtain ⟨K₀, hK₀_nn, hK₀⟩ :=
    exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ 2 2 R₀
  obtain ⟨K₁, hK₁_nn, hK₁⟩ :=
    exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ 3 2 R₁
  obtain ⟨K₂, hK₂_nn, hK₂⟩ :=
    exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ 4 2 R₂
  -- The order-`a` `L²` control: each order-`a` iterated covariant gradient of a fixed smooth coefficient
  -- field is again a fixed smooth field, hence has a uniform fibre-norm sup on the closed manifold.
  obtain ⟨J₀, hJ₀_nn, hJ₀⟩ :=
    exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ 2 (2 + a)
      (iteratedCovGrad (I := I) g₀ 2 2 a R₀)
  obtain ⟨J₁, hJ₁_nn, hJ₁⟩ :=
    exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ 3 (2 + a)
      (iteratedCovGrad (I := I) g₀ 3 2 a R₁)
  obtain ⟨J₂, hJ₂_nn, hJ₂⟩ :=
    exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ 4 (2 + a)
      (iteratedCovGrad (I := I) g₀ 4 2 a R₂)
  -- Take the common ball-uniform bound `Λ = √(max of the six levels)`, so `Λ² ≥ each level`.
  set Kmax : ℝ := max (max (max K₀ K₁) K₂) (max (max J₀ J₁) J₂) with hKmax_def
  have hKmax_nn : 0 ≤ Kmax :=
    le_trans hK₀_nn (le_trans (le_max_left _ _) (le_trans (le_max_left _ _) (le_max_left _ _)))
  refine ⟨Real.sqrt Kmax, Real.sqrt_nonneg _, R₀, R₁, R₂, heval, fun x => ?_, fun x => ?_⟩
  · have hsq : Real.sqrt Kmax ^ 2 = Kmax := Real.sq_sqrt hKmax_nn
    rw [hsq]
    refine ⟨le_trans (hK₀ x) ?_, le_trans (hK₁ x) ?_, le_trans (hK₂ x) ?_⟩
    · exact le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_left _ _)
    · exact le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_left _ _)
    · exact le_trans (le_max_right _ _) (le_max_left _ _)
  · have hsq : Real.sqrt Kmax ^ 2 = Kmax := Real.sq_sqrt hKmax_nn
    rw [hsq]
    refine ⟨le_trans (hJ₀ x) ?_, le_trans (hJ₁ x) ?_, le_trans (hJ₂ x) ?_⟩
    · exact le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_right _ _)
    · exact le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_right _ _)
    · exact le_trans (le_max_right _ _) (le_max_right _ _)

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
