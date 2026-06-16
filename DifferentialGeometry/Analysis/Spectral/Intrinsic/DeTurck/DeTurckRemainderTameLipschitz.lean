import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderDefs
import DifferentialGeometry.Analysis.Sobolev.MoserTameProduct
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.GagliardoNirenbergProductTwoArm
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.IteratedCovGradLinear
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.RiemannianFiberNormSqSmoothCcUniformBound
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.RiemannianFiberNormSqLeRawComponents
import DifferentialGeometry.Analysis.Integration.Measure.FamilyDecomposition
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.RawComponentEuclideanBridge
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.ChartDeTurckRicciRHSRealizeJet
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.RHSSectionChartComponentIdentity
import DifferentialGeometry.Analysis.Spectral.Tensor.ChartTensor.ChartGeometry.GoodSetMeasure

/-!
# The two-arm covariant-`L²` ball-Lipschitz bound on the DeTurck–Ricci remainder difference

This file builds the **covariant-gradient iterate `L²` core** of the smooth-ball Lipschitz
estimate for the genuine Ricci–DeTurck remainder difference — the named-but-absent
`RHSHighOrderSobolevLipschitz` bridge referenced by
`Analysis/Sobolev/MoserTameProduct.lean`.  It is the long pole of the existence forcing
estimate `deTurckSobolevNHa2_mixed_lipschitz`, supplying the spatial half (the spectral
`H^σ` translation is the concurrently-built interior-elliptic/Gårding tower's job and is
**not** attempted here — everything stays in the `iteratedCovGrad`/`tensorL2Norm` world).

## The estimate

For `g₀`-fibre-small smooth perturbations `T, T' : SmoothCcTensor g₀ 0 2` in a covariant-`L²`
ball of radius `R` (`∑_{j ≤ a+2} ‖∇^j T‖_{L²} ≤ R`, idem `T'`), the order-`a` covariant-gradient
iterate `L²` norm of the genuine remainder difference

  `D := deTurckSmoothRemainder g₀ g_bg T − deTurckSmoothRemainder g₀ g_bg T'`
      `( = deTurckRicciRHS g_bg (g₀ + T) − Δ_∇ T − [same for T'] )`

obeys, at the squared level, the **two-arm tame bound**

  `‖∇^a D‖² ≤ C · ( Λ_coeff² · ∑_{i ≤ a+2} ‖∇^i (T − T')‖²`
  `              + Λ_{T−T'}² · ∑_{l ≤ a+2} (‖∇^l coeff₁‖² + ‖∇^l coeff₂‖²) )`,

with the **difference arm** carrying the full covariant-`L²` jet scale of `T − T'` against the
`C⁰`-sup `Λ_coeff` of the (fixed, smooth) DeTurck–Ricci chart-polynomial coefficient data, and the
**cross arm** carrying the full jet scale of that coefficient data against the `C⁰`-sup
`Λ_{T−T'}` of the perturbation difference.  Both arms vanish as `T − T' → 0` (the difference arm
through the jets, the cross arm through `Λ_{T−T'}`), so the bound is a genuine Lipschitz-squared
estimate, not a static envelope.

## The honest integrated route (no refuted pointwise two-arm split)

The two arms reflect the principal-symbol / lower-order split
`chartDeTurckRicciRHS_sub_eq_principalSymbol_add_lowerOrder` of the quasilinear Ricci–DeTurck
nonlinearity: the genuinely `∂²(T − T')`-linear Ricci principal symbol carries an
`O(‖metric jet‖) ≤ R` coefficient defect (the `O(R)` factor lives in `Λ_coeff`), and the
`chartRicciDiffFirstOrderRemainder`, `Γ·Γ` and Lie/DeTurck vector-field terms carry `∂^{≤1}(T − T')`.

A **pointwise** two-arm fibre-norm sum at high order is *false*: a joint concentration bump makes
the middle-diagonal covariant Leibniz terms `∇^i(diff)⊛∇^{l}(coeff)` larger than both arms (the
refuted shape documented in `GagliardoNirenbergProductTwoArm`).  The honest route bounds `∇^a D`
**pointwise by the diagonal covariant-Leibniz product grid** (the true covariant-Leibniz shape) and
converts to the two `L²` arms only through the **integrated** Gagliardo–Nirenberg engine
`exists_integrated_diagonalProductGrid_twoArm_pair_le`, which redistributes the high covariant
orders by `Lᵖ` interpolation so each arm carries one factor's full `L²`-jet scale against the
*other* factor's `C⁰` sup.

## Architecture

* `tensorL2Norm_le_of_pointwise_fiberNormSq_twoCoeff` — a pointwise-to-`L²` packaging that lifts a
  **two-coefficient** pointwise fibre-norm domination `rfns(C)(x) ≤ p₁² rfns(A)(x) + p₂² rfns(B)(x)`
  to `‖C‖ ≤ p₁ ‖A‖ + p₂ ‖B‖`.  It is the two-distinct-coefficient companion of
  `tensorL2Norm_le_of_pointwise_fiberNormSq_bound_two`; it is **not** used by the headline below
  (a pointwise two-arm split is the refuted shape), but is kept as reusable covariant-`L²` packaging.

* `deTurckRemainderDiff_singleField_diagonalGrid_intrinsicCore` — the **single posited leaf**, the
  irreducible chart→intrinsic content stripped of all packaging: the intrinsic covariant Faà-di-Bruno
  **single-coefficient diagonal product-grid domination** of the sealed remainder difference `D`
  itself, against a single intrinsic coefficient field `coeff : SmoothCcTensor g₀ 0 s`,
  `rfns(∇^a D)(x) ≤ Cmid · ∑_{i ≤ a+2} rfns(∇^i (T − T'))(x) · ∑_{l ≤ a+2−i} rfns(∇^l coeff)(x)`.  This
  is the genuine analytic prerequisite (the chart→intrinsic covariant-bilinear realization of the
  sealed remainder difference, with the chart-polynomial coefficient lifted to an intrinsic
  `SmoothCcTensor` and the two-factor diagonal `rfns` grid, has no on-disk antecedent — it is the
  chart-locality-free covariant-jet comparison documented as the open analytic sub-program); its body
  is `sorry`.

* `deTurckRemainderDiff_singleField_diagonalGrid` — the same single-coefficient diagonal grid **with
  the two `C⁰` fibre-sup levels** `ΛW, Λcoeff`, **proved** (no `sorry` of its own) from the core posit
  by mechanically recovering the sups via the uniform smooth-tensor fibre-norm bound
  `exists_bound_riemannianFiberNormSq_smoothCcTensor` on the compact manifold.

* `deTurckRemainderDiff_principalSplit_singleCoeffDiagonalGrid` — the **two-field
  principal/lower-order split** of the sealed remainder difference `D = D₁ + D₂` with each field `Dₚ`
  dominated by its single-coefficient diagonal grid against `coeffₚ`.  It is **proved** (no `sorry` of
  its own) from the single-field posit by taking the principal field `D₁ := D` (the whole sealed
  remainder difference), the lower-order field `D₂ := 0` (whose grid is trivial since `∇^a 0 = 0`),
  and both coefficient columns equal to the posited `coeff`; the split is `add_zero`.

* `pointwise_iteratedCovGrad_deTurckRemainderDiff_productGrid` — the covariant Faà-di-Bruno expansion
  of the genuine remainder difference, in the honest **diagonal product-grid** shape the integrated
  engine consumes: a fixed DeTurck coefficient pair `(coeff₁, coeff₂)` and a middle constant `Cmid`
  such that `rfns(∇^a D)` is dominated pointwise by the diagonal product grid of `(T − T')` against the
  pair.  It is **proved** (no `sorry` of its own) from the posited split by `2`-sub-additivity of the
  intrinsic fibre norm (`riemannianFiberNormSq_add_le`) on `∇^a D = ∇^a D₁ + ∇^a D₂` and the
  diagonal-column merge of the two single-coefficient grids into the `coeff₁ + coeff₂` pair grid.

* `deTurckRemainderDiff_iteratedCovGrad_twoArm_ballLipschitz` — the headline two-arm bound,
  assembled by feeding the product-grid domination through the sorry-free integrated
  engine `exists_integrated_diagonalProductGrid_twoArm_pair_le`.
-/

noncomputable section

open MeasureTheory Set Filter Topology Bundle Manifold Tensor0SBundle ContinuousLinearMap
open scoped ENNReal NNReal BigOperators Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral (covGrad)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

/-- **Two-coefficient pointwise-to-`L²` packaging.**

If, for every base point `x`, the intrinsic fibre norm of a smooth compactly-supported tensor
`Curv` is bounded by the **two-arm** quadratic form
```
rfns(Curv)(x) ≤ p₁² · rfns(A)(x) + p₂² · rfns(B)(x)
```
in the squared fibre norms of two further smooth tensors `A`, `B` (with nonnegative
coefficients `p₁, p₂`), then the metric `L²` (semi)norms satisfy the two-arm bound
```
‖Curv‖ ≤ p₁ · ‖A‖ + p₂ · ‖B‖.
```

This is the genuine two-distinct-coefficient companion of
`tensorL2Norm_le_of_pointwise_fiberNormSq_bound_two` (which forces a single shared constant on
both arms).  The proof is the same integral identity
`tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq` together with monotonicity of the
volume integral and the elementary scalar inequality
`p₁² a² + p₂² b² ≤ (p₁ a + p₂ b)²` (`0 ≤ a, b`).

It is retained as reusable covariant-`L²` packaging; the headline below does **not** route through
it, because a pointwise two-arm fibre-norm split is the refuted shape (see
`GagliardoNirenbergProductTwoArm`). -/
theorem tensorL2Norm_le_of_pointwise_fiberNormSq_twoCoeff
    (g : SmoothRiemannianMetric I M) {a b c : ℕ}
    (A : SmoothCcTensor g 0 a) (B : SmoothCcTensor g 0 b)
    (Curv : SmoothCcTensor g 0 c) (p₁ p₂ : ℝ) (hp₁ : 0 ≤ p₁) (hp₂ : 0 ≤ p₂)
    (hpt : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g 0 c x (Curv.toSection x) ≤
        p₁ ^ 2 * riemannianFiberNormSq (I := I) (M := M) g 0 a x (A.toSection x) +
          p₂ ^ 2 * riemannianFiberNormSq (I := I) (M := M) g 0 b x (B.toSection x)) :
    ‖Curv‖ ≤ p₁ * ‖A‖ + p₂ * ‖B‖ := by
  classical
  set μ := riemannianVolumeMeasure (I := I) (M := M) g with hμ_def
  -- The three `L²`-norm ↔ ∫ rfns bridges.
  have hbridgeCurv :
      ‖Curv‖ ^ 2 =
        ∫ x, riemannianFiberNormSq (I := I) (M := M) g 0 c x (Curv.toSection x) ∂μ := by
    rw [SmoothCcTensor.norm_def (I := I) (M := M) Curv, hμ_def]
    exact tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq (I := I) (M := M) g c Curv
  have hbridgeA :
      ‖A‖ ^ 2 = ∫ x, riemannianFiberNormSq (I := I) (M := M) g 0 a x (A.toSection x) ∂μ := by
    rw [SmoothCcTensor.norm_def (I := I) (M := M) A, hμ_def]
    exact tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq (I := I) (M := M) g a A
  have hbridgeB :
      ‖B‖ ^ 2 = ∫ x, riemannianFiberNormSq (I := I) (M := M) g 0 b x (B.toSection x) ∂μ := by
    rw [SmoothCcTensor.norm_def (I := I) (M := M) B, hμ_def]
    exact tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq (I := I) (M := M) g b B
  -- Integrability of every arm's squared fibre norm.
  have hintCurv : MeasureTheory.Integrable
      (fun x => riemannianFiberNormSq (I := I) (M := M) g 0 c x (Curv.toSection x)) μ := by
    rw [hμ_def]; exact integrable_riemannianFiberNormSq_toSection (I := I) (M := M) g 0 c Curv
  have hintA : MeasureTheory.Integrable
      (fun x => riemannianFiberNormSq (I := I) (M := M) g 0 a x (A.toSection x)) μ := by
    rw [hμ_def]; exact integrable_riemannianFiberNormSq_toSection (I := I) (M := M) g 0 a A
  have hintB : MeasureTheory.Integrable
      (fun x => riemannianFiberNormSq (I := I) (M := M) g 0 b x (B.toSection x)) μ := by
    rw [hμ_def]; exact integrable_riemannianFiberNormSq_toSection (I := I) (M := M) g 0 b B
  -- The two-arm pointwise integrand bound, with the RHS integrable.
  set RHS : M → ℝ := fun x =>
    p₁ ^ 2 * riemannianFiberNormSq (I := I) (M := M) g 0 a x (A.toSection x) +
      p₂ ^ 2 * riemannianFiberNormSq (I := I) (M := M) g 0 b x (B.toSection x) with hRHS_def
  have hRHS_int : MeasureTheory.Integrable RHS μ :=
    (hintA.const_mul (p₁ ^ 2)).add (hintB.const_mul (p₂ ^ 2))
  have hcurv_nn_ae : (0 : M → ℝ) ≤ᵐ[μ]
      (fun x => riemannianFiberNormSq (I := I) (M := M) g 0 c x (Curv.toSection x)) :=
    Filter.Eventually.of_forall (fun x =>
      riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 c x _)
  have hint_le :
      (∫ x, riemannianFiberNormSq (I := I) (M := M) g 0 c x (Curv.toSection x) ∂μ) ≤
        ∫ x, RHS x ∂μ :=
    MeasureTheory.integral_mono_of_nonneg hcurv_nn_ae hRHS_int
      (Filter.Eventually.of_forall (fun x => by rw [hRHS_def]; exact hpt x))
  have hRHS_integral :
      (∫ x, RHS x ∂μ) =
        p₁ ^ 2 * (∫ x, riemannianFiberNormSq (I := I) (M := M) g 0 a x (A.toSection x) ∂μ) +
          p₂ ^ 2 * (∫ x, riemannianFiberNormSq (I := I) (M := M) g 0 b x (B.toSection x) ∂μ) := by
    rw [hRHS_def, MeasureTheory.integral_add (hintA.const_mul (p₁ ^ 2)) (hintB.const_mul (p₂ ^ 2)),
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
  -- Squared-norm two-arm bound.
  have hsq_bound : ‖Curv‖ ^ 2 ≤ p₁ ^ 2 * ‖A‖ ^ 2 + p₂ ^ 2 * ‖B‖ ^ 2 := by
    rw [hbridgeCurv, hbridgeA, hbridgeB]
    calc (∫ x, riemannianFiberNormSq (I := I) (M := M) g 0 c x (Curv.toSection x) ∂μ)
        ≤ ∫ x, RHS x ∂μ := hint_le
      _ = p₁ ^ 2 * (∫ x, riemannianFiberNormSq (I := I) (M := M) g 0 a x (A.toSection x) ∂μ) +
            p₂ ^ 2 * (∫ x, riemannianFiberNormSq (I := I) (M := M) g 0 b x (B.toSection x) ∂μ) :=
          hRHS_integral
  -- Conclude by `√` and `p₁²a² + p₂²b² ≤ (p₁a + p₂b)²`.
  have hCurv_nn : 0 ≤ ‖Curv‖ := norm_nonneg _
  have hA_nn : 0 ≤ ‖A‖ := norm_nonneg _
  have hB_nn : 0 ≤ ‖B‖ := norm_nonneg _
  have htarget_nn : 0 ≤ p₁ * ‖A‖ + p₂ * ‖B‖ := by positivity
  have hcross : p₁ ^ 2 * ‖A‖ ^ 2 + p₂ ^ 2 * ‖B‖ ^ 2 ≤ (p₁ * ‖A‖ + p₂ * ‖B‖) ^ 2 := by
    have hmid : 0 ≤ 2 * (p₁ * ‖A‖) * (p₂ * ‖B‖) := by positivity
    nlinarith [hmid]
  have hsq_final : ‖Curv‖ ^ 2 ≤ (p₁ * ‖A‖ + p₂ * ‖B‖) ^ 2 := le_trans hsq_bound hcross
  have hsqrt := Real.sqrt_le_sqrt hsq_final
  rwa [Real.sqrt_sq hCurv_nn, Real.sqrt_sq htarget_nn] at hsqrt

/-- The `(0,2)`-tensor fibre at `x` obtained from the metric bilinear form `g₀.inner x` by the fibre
isometry `bilinFormToModel`.  Factored out (outside the bundle-topology `letI` of
`metricTensor0SField`) so the `Tensor0SModel` normed-space instance is visible at elaboration. -/
private def metricTensorModelFun (g₀ : SmoothRiemannianMetric I M) (x : M) :
    Tensor0SBundle.Tensor0SSpace 2 I x :=
  Tensor0SBundle.Tensor0SSpace.ofModel
    (bilinFormToModel (TangentSpace I x) (g₀.inner x))

set_option linter.unusedSectionVars false in
private theorem metricTensorModelFun_toModel_apply (g₀ : SmoothRiemannianMetric I M)
    (x : M) (v : Fin 2 → TangentSpace I x) :
    Tensor0SBundle.Tensor0SSpace.toModel (metricTensorModelFun (I := I) g₀ x) v =
      g₀.inner x (v 0) (v 1) := by
  unfold metricTensorModelFun
  rw [Tensor0SBundle.Tensor0SSpace.toModel_ofModel]
  exact bilinFormToModel_apply (TangentSpace I x) (g₀.inner x) v

set_option backward.isDefEq.respectTransparency false in
/-- The metric `g₀`, viewed as the model `(0,2)`-multilinear field `x ↦ (v ↦ g₀(v 0, v 1))`.  This is
the smooth `(0,2)`-tensor field obtained from the bilinear metric form `g₀.inner x` by the fibre
isometry `bilinFormToModel`.  Its smoothness is the metric analog of `deTurckRHSField`: in any chart at
`α`, each chart-frame component `x ↦ g₀(e_i^α(x), e_j^α(x))` is smooth, by the chart Gram smoothness
together with the smoothness of the metric inner product on smooth tangent sections. -/
private def metricTensor0SField (g₀ : SmoothRiemannianMetric I M) :
    Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) ∞ 2 :=
  letI := tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 2
  letI := TangentBundle.contMDiffVectorBundle (I := I) (M := M) (n := ∞)
  ⟨fun x => metricTensorModelFun (I := I) g₀ x, by
    let d := Module.finrank ℝ E
    let b : Module.Basis (Fin d) ℝ E := DifferentialGeometry.Integral.Measure.chartModelBasis E
    refine (contMDiff_multilinearSection_iff_coord (TangentSpace I) ∞ b _).mpr
      fun σ x₀ => ?_
    have hcomp : ContMDiffOn I 𝓘(ℝ, ℝ) ∞
        (fun x : M =>
          g₀.inner x
            (DifferentialGeometry.PDE.RicciFlow.chartFrameVec (I := I) x₀ (σ 0) x)
            (DifferentialGeometry.PDE.RicciFlow.chartFrameVec (I := I) x₀ (σ 1) x))
        (chartAt H x₀).source := by
      intro y hy
      have h_frame_on : ∀ k : Fin (Module.finrank ℝ E),
          ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
            (fun w : M => TotalSpace.mk' E w
              (DifferentialGeometry.PDE.RicciFlow.chartFrameVec (I := I) x₀ k w))
            (chartAt H x₀).source := fun k =>
        DifferentialGeometry.Integral.Measure.chartAlphaFrame_section_contMDiffOn (I := I) x₀ k
      obtain ⟨S, hS_eq⟩ :=
        exists_contMDiffSection_eqOn_nhd
          (s := fun k : Fin (Module.finrank ℝ E) => fun w : M =>
            DifferentialGeometry.PDE.RicciFlow.chartFrameVec (I := I) x₀ k w)
          (u := (chartAt H x₀).source) (p := y)
          h_frame_on ((chartAt H x₀).open_source) hy
      have h_scalar :
          ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun w : M => g₀.inner w ((S (σ 0)) w) ((S (σ 1)) w)) :=
        DifferentialGeometry.Integral.DivergenceTheorem.contMDiff_g_inner_of_smooth_sections
          (I := I) g₀ (S (σ 0)) (S (σ 1))
      have h_at : ContMDiffAt I 𝓘(ℝ, ℝ) ∞
          (fun x : M => g₀.inner x
            (DifferentialGeometry.PDE.RicciFlow.chartFrameVec (I := I) x₀ (σ 0) x)
            (DifferentialGeometry.PDE.RicciFlow.chartFrameVec (I := I) x₀ (σ 1) x)) y := by
        refine (h_scalar y).congr_of_eventuallyEq ?_
        filter_upwards [hS_eq] with w hw
        rw [hw (σ 0), hw (σ 1)]
      exact h_at.contMDiffWithinAt
    have hx₀_src : x₀ ∈ (chartAt H x₀).source := mem_chart_source H x₀
    have h_src_nhd : (chartAt H x₀).source ∈ 𝓝 x₀ :=
      (chartAt H x₀).open_source.mem_nhds hx₀_src
    have hx₀_base : x₀ ∈ (trivializationAt E (TangentSpace I) x₀).baseSet :=
      mem_baseSet_trivializationAt E (TangentSpace I) x₀
    refine ((hcomp x₀ hx₀_src).contMDiffAt h_src_nhd).congr_of_eventuallyEq ?_
    have h_base_nhd :
        (trivializationAt E (TangentSpace I) x₀).baseSet ∈ 𝓝 x₀ :=
      (trivializationAt E (TangentSpace I) x₀).open_baseSet.mem_nhds hx₀_base
    filter_upwards [h_base_nhd] with x hx
    rw [continuousMultilinearMap_basis_repr]
    change Tensor0SBundle.Tensor0SSpace.toModel
        (metricTensorModelFun (I := I) g₀ x)
        (fun j => (trivializationAt E (TangentSpace I) x₀).symmL ℝ x (b (σ j))) = _
    rw [metricTensorModelFun_toModel_apply]
    rfl⟩

/-- The model value of `metricTensor0SField` recovers the metric bilinear form. -/
private theorem metricTensor0SField_toModel_apply (g₀ : SmoothRiemannianMetric I M)
    (x : M) (v : Fin 2 → TangentSpace I x) :
    Tensor0SBundle.Tensor0SSpace.toModel (metricTensor0SField (I := I) g₀ x) v =
      g₀.inner x (v 0) (v 1) :=
  metricTensorModelFun_toModel_apply (I := I) g₀ x v

set_option backward.isDefEq.respectTransparency false in
/-- The metric `g₀`, promoted to a smooth mixed `(0,2)`-tensor section via the scalar-extension
`MixedSection.fromMultilinearSection` (the metric analog of `deTurckRHSMixedSection`). -/
private def metricMixedSection (g₀ : SmoothRiemannianMetric I M) :
    Cₛ^∞⟮I; TensorRSModel 0 2 ℝ E, (fun x : M => TensorRSSpace 0 2 I x)⟯ :=
  MixedSection.fromMultilinearSection (𝕜 := ℝ) (F := E) (IB := I)
    (E := (TangentSpace I : M → Type _)) ∞ (metricTensor0SField (I := I) g₀)

set_option backward.isDefEq.respectTransparency false in
/-- The metric `g₀` as a smooth, compactly-supported `(0,2)`-tensor section (compact support is
automatic on a compact manifold). -/
private def metricSmoothCcTensor (g₀ : SmoothRiemannianMetric I M) :
    SmoothCcTensor g₀ 0 2 where
  toSection := metricMixedSection (I := I) g₀
  hasCompactSupport := HasCompactSupport.of_compactSpace _

set_option backward.isDefEq.respectTransparency false in
/-- The underlying section value of `metricSmoothCcTensor`, evaluated at the canonical unit
`(0,0)`-tensor and a tangent pair, recovers the metric bilinear form `g₀(v 0, v 1)`. -/
private theorem metricSmoothCcTensor_toModel_apply (g₀ : SmoothRiemannianMetric I M)
    (x : M) (v : Fin 2 → TangentSpace I x) :
    Tensor0SBundle.Tensor0SSpace.toModel
        ((metricSmoothCcTensor (I := I) g₀).toSection x
          (ContinuousMultilinearMap.constOfIsEmpty ℝ
            (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))) v =
      g₀.inner x (v 0) (v 1) := by
  have hsec : ((metricSmoothCcTensor (I := I) g₀).toSection x
        (ContinuousMultilinearMap.constOfIsEmpty ℝ
          (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ)))
      = (MixedSection.eval₀ (F := E) (E := (TangentSpace I : M → Type _)) x).smulRight
          (metricTensor0SField (I := I) g₀ x)
        (ContinuousMultilinearMap.constOfIsEmpty ℝ
          (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ)) := rfl
  rw [hsec, ContinuousLinearMap.smulRight_apply, MixedSection.eval₀_apply]
  rw [show (ContinuousMultilinearMap.constOfIsEmpty ℝ
        (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ)) Fin.elim0 = (1 : ℝ) from rfl, one_smul,
    metricTensor0SField_toModel_apply]

/-- **(The positive intrinsic coefficient column — PROVED via the metric tensor.)**  A fixed
intrinsic coefficient field `coeff : SmoothCcTensor g₀ 0 s` with a strictly-positive fibre-norm floor
`1 ≤ rfns(coeff)(x)` at every base point.  This is the auxiliary positive parallel coefficient used to
lift the single-sum covariant-Leibniz `rfns` grid of the linearized operator to the two-factor diagonal
product-grid shape the integrated Gagliardo–Nirenberg engine consumes: its `l = 0` column carries the
positive floor that absorbs the single-sum grid constant.

The witness is the metric tensor `metricSmoothCcTensor g₀` (`s = 2`).  In a `g₀(x)`-orthonormal frame
`e` of `T_x M` (`exists_orthonormal_frame_riemannianFiberNormSq`), the model value of the metric tensor
on the pair `(e_{J 0}, e_{J 1})` is `g₀(e_{J 0}, e_{J 1}) = δ_{J 0, J 1}`; hence the rfns frame
double-sum collapses to the count of the diagonal multi-indices `J : Fin 2 → Fin n`, which is `n =
finrank E ≥ 1`.  Picking out the single diagonal multi-index `J = ![0, 0]` (present since `n ≥ 1`)
already contributes a `1`, and all other summands are nonnegative, so the rfns is `≥ 1`.

**Non-vacuity.**  The floor `1 ≤ rfns(coeff)(x)` rejects the degenerate `coeff = 0` witness
(`rfns(0) = 0`), so the coefficient genuinely carries a positive column. -/
private theorem exists_positiveFloor_intrinsicCoeff (g₀ : SmoothRiemannianMetric I M) :
    ∃ (s : ℕ) (coeff : SmoothCcTensor g₀ 0 s),
      ∀ x : M, (1 : ℝ) ≤ riemannianFiberNormSq (I := I) (M := M) g₀ 0 s x (coeff.toSection x) := by
  classical
  refine ⟨2, metricSmoothCcTensor (I := I) g₀, fun x => ?_⟩
  -- The `g₀(x)`-orthonormal frame `e` representing `rfns` as a frame double-sum.
  obtain ⟨n, e, hn, horth, _hpars, hrepr⟩ :=
    exists_orthonormal_frame_riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x
  have hn1 : 1 ≤ n := by
    rw [hn]
    have hne : Module.finrank ℝ (TangentSpace I x) ≠ 0 := by
      change Module.finrank ℝ E ≠ 0
      exact NeZero.ne _
    omega
  -- Rewrite the rfns as the frame double-sum and isolate the diagonal multi-index `J = ![0, 0]`.
  rw [hrepr]
  have hsummand_eq : ∀ (K : Fin 0 → Fin n) (J : Fin 2 → Fin n),
      fiberNormSqSummand (I := I) (M := M) g₀ x 0 2
          ((metricSmoothCcTensor (I := I) g₀).toSection x) n e K J =
        (g₀.inner x (e (J 0)) (e (J 1))) ^ 2 := by
    intro K J
    unfold fiberNormSqSummand
    congr 1
    have hconst : ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 0) ℝ).compContinuousLinearMap
          (fun k : Fin 0 => g₀.inner x (e (K k))) :
          Tensor0SBundle.Tensor0SSpace 0 I x) =
        ContinuousMultilinearMap.constOfIsEmpty ℝ
          (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ) := by
      apply Tensor0SBundle.tensor0SSpace_ext
      intro w
      change ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 0) ℝ).compContinuousLinearMap
          (fun k : Fin 0 => g₀.inner x (e (K k)))) w =
        (ContinuousMultilinearMap.constOfIsEmpty ℝ
          (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ)) w
      rw [show ((ContinuousMultilinearMap.constOfIsEmpty ℝ
            (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ)) w : ℝ) = 1 from rfl]
      change (ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 0) ℝ)
          (fun k => g₀.inner x (e (K k)) (w k)) = 1
      rw [ContinuousMultilinearMap.mkPiAlgebra_apply]
      exact Finset.prod_of_isEmpty _
    rw [hconst]
    have h := metricSmoothCcTensor_toModel_apply (I := I) g₀ x (fun k => e (J k))
    rw [show ((metricSmoothCcTensor (I := I) g₀).toSection x
            (ContinuousMultilinearMap.constOfIsEmpty ℝ
              (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))
          (fun k => e (J k)) : ℝ)
        = Tensor0SBundle.Tensor0SSpace.toModel
            ((metricSmoothCcTensor (I := I) g₀).toSection x
              (ContinuousMultilinearMap.constOfIsEmpty ℝ
                (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ)))
            (fun k => e (J k)) from rfl]
    rw [h]
  simp only [hsummand_eq]
  have hJ0 : (g₀.inner x (e ((![⟨0, hn1⟩, ⟨0, hn1⟩] : Fin 2 → Fin n) 0))
      (e ((![⟨0, hn1⟩, ⟨0, hn1⟩] : Fin 2 → Fin n) 1))) ^ 2 = 1 := by
    have h00 : g₀.inner x (e ⟨0, hn1⟩) (e ⟨0, hn1⟩) = 1 := by
      have := horth ⟨0, hn1⟩ ⟨0, hn1⟩; simpa using this
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [h00]; norm_num
  rw [Fintype.sum_unique]
  refine le_trans (le_of_eq hJ0.symm) ?_
  refine Finset.single_le_sum
    (f := fun J : Fin 2 → Fin n => (g₀.inner x (e (J 0)) (e (J 1))) ^ 2)
    (fun J _ => sq_nonneg _) (Finset.mem_univ _)

/-- **The squared intrinsic fibre norm is invariant under negation of the tensor value.** For any
`(r, s)`-tensor `v` at `x`, `rfns(−v)(x) = rfns(v)(x)`.  Proved through the model-inner-product bridge
`riemannianFiberNormSq_eq_tensorInnerPointwise`: negation passes to `−toModel v` (`toModel_neg`), and
the two sign factors cancel by `ℝ`-bilinearity of `tensorInnerPointwise`. -/
private theorem riemannianFiberNormSq_neg_value
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M) (v : TensorRSSpace r s I x) :
    riemannianFiberNormSq (I := I) (M := M) g r s x (-v) =
      riemannianFiberNormSq (I := I) (M := M) g r s x v := by
  rw [riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g r s x (-v),
    riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g r s x v]
  rw [TensorRSSpace.toModel_neg]
  rw [← neg_one_smul ℝ (TensorRSSpace.toModel (𝕜 := ℝ) (E := E) (I := I) (M := M)
        (r := r) (s := s) (x := x) v),
    tensorInnerPointwise_smul_left, tensorInnerPointwise_smul_right]
  ring

/-- **(POSIT — the pointwise order-`0` rough-Laplacian fibre bound, public jet form.)**

For a smooth compactly-supported `(0, s)`-tensor `S` there is a single nonnegative constant `C`,
uniform over `S` and the base point `x`, with the **order-`0`** pointwise domination of the rough
(connection) Laplacian `Δ_∇ S := rawTensorConnLapSmooth g₀ 0 s S` by the **order-`2`** covariant jet of
`S`:
```
rfns(Δ_∇ S)(x) ≤ C · rfns(∇²S)(x),   ∇²S := iteratedCovGrad g₀ 0 s 2 S.
```

This is the value-local order-`0` content of the rough Laplacian: pointwise `Δ_∇ S` is the diagonal
`g₀`-trace of the Hessian `∑_i ∇²_{B_i,B_i} S` (`rawTensorConnLap_eq_frame_trace_secondCovDeriv`), and
the `n`-sub-additivity of the squared fibre norm together with the per-slot two-slot-evaluation Parseval
bound dominates the trace by `dim² · rfns(∇²S)(x)` (the witness `C := dim²`).  The on-disk material
already carries this exact bound as the **private** lemma `rawConnLap_fiberNormSq_le_secondCovGrad`
(`Geometry/Connection/Laplacian/RoughLaplacianSecondCovGradL2Bound.lean`), built from the private
per-slot two-slot-evaluation bound `riemannianFiberNormSq_twoSlotUnitEval_le`; only its **public** jet
restatement (in `iteratedCovGrad g₀ 0 s 2`-form) is absent on disk.  Posited here as one precise true
order-`0` infrastructure child; its body is `sorry`, and consumers transitively depend on its `sorryAx`.

**Non-vacuity / order self-check.**  The bound reads `∇²S`; a `C = 0` witness is rejected by a
nonvanishing `Δ_∇ S` for a non-flat `S` (already at `s = 0`, `Δ_∇ f = trace ∇²f ≠ 0`). -/
private theorem rawTensorConnLapSmooth_fiberNormSq_le_secondCovGrad_jet
    (g₀ : SmoothRiemannianMetric I M) (s : ℕ) :
    ∃ C : ℝ,
      0 ≤ C ∧
      ∀ (S : SmoothCcTensor g₀ 0 s) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 s x
            ((rawTensorConnLapSmooth (I := I) g₀ 0 s S).toSection x) ≤
          C * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + 2) x
            ((iteratedCovGrad (I := I) g₀ 0 s 2 S).toSection x) := by
  refine ⟨((Module.finrank ℝ E : ℝ)) ^ 2, by positivity, fun S x => ?_⟩
  have hbase := rawConnLap_fiberNormSq_le_secondCovGrad (I := I) (M := M) g₀ s S x
  -- `iteratedCovGrad g₀ 0 s 2 S = covGrad g₀ 0 (s+1) (covGrad g₀ 0 s S)` (twice `iteratedCovGrad_succ`,
  -- `s + 2` and `s + 1 + 1` definitionally equal), so the RHS jet form matches the on-disk bound.
  simpa only [iteratedCovGrad_succ, iteratedCovGrad_zero] using hbase

/-- **The pointwise iterated-gradient fibre bound of the single-level commutator defect.**

For every covariant rank `s` there is a nonnegative per-gradient-order constant family `K : ℕ → ℝ`,
uniform in `S`, such that for every gradient order `p` the squared fibre norm of the `p`-fold covariant
gradient of the single-level rough-Laplacian / covariant-gradient commutator defect
`pointwiseTensorCurv g s S = Δ_∇(∇S) − ∇(Δ_∇ S)` obeys, pointwise,
```
rfns(∇^p (pointwiseTensorCurv g s S))(x) ≤ K p · ∑_{a ∈ range (p + 2)} rfns(∇^a S)(x).
```

This is the pointwise (`riemannianFiberNormSq`) analogue of the `L²` bound
`exists_iteratedCovGrad_pointwiseTensorCurv_l2Norm_le`; it is **proved** here (no `sorry`) from the
sorry-free Hom-field first-order section identity
`exists_pointwiseTensorCurv_firstOrder_homField_section` (`Curv S = appFullSec H_R (∇S) +
appFullSec H_dR S`) and the two order-shifted Hom-field jet window bounds
`exists_appFullSec_iteratedCovGrad_window_bound`, split by the `2`-sub-additivity
`riemannianFiberNormSq_add_le` of the squared fibre norm. -/
private theorem pointwiseTensorCurv_iteratedCovGrad_fiberNormSq_jet_le
    (g₀ : SmoothRiemannianMetric I M) (s : ℕ) :
    ∃ K : ℕ → ℝ, (∀ p, 0 ≤ K p) ∧
      ∀ (p : ℕ) (S : SmoothCcTensor g₀ 0 s) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((s + 1) + p) x
            ((iteratedCovGrad (I := I) g₀ 0 (s + 1) p
              (pointwiseTensorCurv (I := I) (M := M) g₀ s S)).toSection x) ≤
          K p * ∑ a ∈ Finset.range (p + 2),
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + a) x
              ((iteratedCovGrad (I := I) g₀ 0 s a S).toSection x) := by
  classical
  obtain ⟨H_R, H_dR, hsec⟩ :=
    exists_pointwiseTensorCurv_firstOrder_homField_section (I := I) (M := M) g₀ s
  obtain ⟨ccR, hccR_nn, hccR⟩ :=
    exists_appFullSec_iteratedCovGrad_window_bound (I := I) (M := M) g₀ 0 (s + 1) (s + 1) H_R
  obtain ⟨ccdR, hccdR_nn, hccdR⟩ :=
    exists_appFullSec_iteratedCovGrad_window_bound (I := I) (M := M) g₀ 0 s (s + 1) H_dR
  refine ⟨fun p => 2 * ccR p + 2 * ccdR p,
    fun p => by have := hccR_nn p; have := hccdR_nn p; positivity, fun p S x => ?_⟩
  set rfnsS : ℕ → ℝ := fun a =>
    riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + a) x
      ((iteratedCovGrad (I := I) g₀ 0 s a S).toSection x) with hrfnsS_def
  have hrfnsS_nn : ∀ a, 0 ≤ rfnsS a := fun a =>
    riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (s + a) x _
  set FULL : ℝ := ∑ a ∈ Finset.range (p + 2), rfnsS a with hFULL_def
  have hFULL_nn : 0 ≤ FULL := Finset.sum_nonneg (fun a _ => hrfnsS_nn a)
  -- The two Hom-field arms of the section identity.
  set AR : SmoothCcTensor g₀ 0 (s + 1) :=
    appFullSec (I := I) (M := M) g₀ 0 (s + 1) (s + 1) H_R (covGrad (I := I) (M := M) g₀ 0 s S)
    with hAR_def
  set AdR : SmoothCcTensor g₀ 0 (s + 1) :=
    appFullSec (I := I) (M := M) g₀ 0 s (s + 1) H_dR S with hAdR_def
  have hgradsplit :
      iteratedCovGrad (I := I) g₀ 0 (s + 1) p (pointwiseTensorCurv (I := I) (M := M) g₀ s S) =
        iteratedCovGrad (I := I) g₀ 0 (s + 1) p AR + iteratedCovGrad (I := I) g₀ 0 (s + 1) p AdR := by
    rw [hsec S, ← hAR_def, ← hAdR_def, iteratedCovGrad_add (I := I) (M := M) g₀ 0 (s + 1) p]
  have happ :
      (iteratedCovGrad (I := I) g₀ 0 (s + 1) p
          (pointwiseTensorCurv (I := I) (M := M) g₀ s S)).toSection x =
        (iteratedCovGrad (I := I) g₀ 0 (s + 1) p AR).toSection x +
          (iteratedCovGrad (I := I) g₀ 0 (s + 1) p AdR).toSection x := by
    rw [hgradsplit, SmoothCcTensor.toSection_add]; rfl
  rw [happ]
  refine le_trans (riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 0 ((s + 1) + p) x
    ((iteratedCovGrad (I := I) g₀ 0 (s + 1) p AR).toSection x)
    ((iteratedCovGrad (I := I) g₀ 0 (s + 1) p AdR).toSection x)) ?_
  -- The `H_R` arm reads the jets `∇^i (∇S) = ∇^{i+1} S`, the `H_dR` arm reads `∇^i S`.
  have hAR_w :
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((s + 1) + p) x
          ((iteratedCovGrad (I := I) g₀ 0 (s + 1) p AR).toSection x) ≤
        ccR p * ∑ i ∈ Finset.range (p + 1), rfnsS (i + 1) := by
    -- `covGrad g₀ 0 s S = iteratedCovGrad g₀ 0 s 1 S` definitionally.
    have hcov1 : covGrad (I := I) (M := M) g₀ 0 s S = iteratedCovGrad (I := I) g₀ 0 s 1 S := rfl
    have h := hccR (iteratedCovGrad (I := I) g₀ 0 s 1 S) p x
    rw [hAR_def, hcov1]
    refine h.trans_eq ?_
    refine congrArg (ccR p * ·) (Finset.sum_congr rfl (fun i _ => ?_))
    have hcomp := rfns_iteratedCovGrad_comp (I := I) (M := M) g₀ 0 s 1 i S x
    -- `rfns(∇^i (∇S)) = rfns(∇^{1+i} S) = rfnsS (1 + i) = rfnsS (i + 1)`.
    have harg : rfnsS (1 + i) = rfnsS (i + 1) := by rw [Nat.add_comm 1 i]
    rw [← harg, hrfnsS_def]
    exact hcomp
  have hAdR_w :
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((s + 1) + p) x
          ((iteratedCovGrad (I := I) g₀ 0 (s + 1) p AdR).toSection x) ≤
        ccdR p * ∑ i ∈ Finset.range (p + 1), rfnsS i := by
    have h := hccdR S p x
    rw [hAdR_def]
    exact h.trans_eq (by rw [hrfnsS_def])
  -- Both windows inject into `range (p + 2)`.
  have hsubR : ∑ i ∈ Finset.range (p + 1), rfnsS (i + 1) ≤ FULL := by
    rw [hFULL_def]
    have hIco : ∑ i ∈ Finset.range (p + 1), rfnsS (i + 1) =
        ∑ a ∈ Finset.Ico 1 (1 + (p + 1)), rfnsS a := by
      rw [Finset.sum_Ico_eq_sum_range]
      refine Finset.sum_congr (by congr 1; omega) (fun i _ => by rw [Nat.add_comm 1 i])
    rw [hIco]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun a _ _ => hrfnsS_nn a)
    intro a ha; rw [Finset.mem_Ico] at ha; rw [Finset.mem_range]; omega
  have hsubdR : ∑ i ∈ Finset.range (p + 1), rfnsS i ≤ FULL := by
    rw [hFULL_def]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun a _ _ => hrfnsS_nn a)
    intro a ha; rw [Finset.mem_range] at ha ⊢; omega
  calc 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((s + 1) + p) x
            ((iteratedCovGrad (I := I) g₀ 0 (s + 1) p AR).toSection x) +
          2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((s + 1) + p) x
            ((iteratedCovGrad (I := I) g₀ 0 (s + 1) p AdR).toSection x)
      ≤ 2 * (ccR p * ∑ i ∈ Finset.range (p + 1), rfnsS (i + 1)) +
          2 * (ccdR p * ∑ i ∈ Finset.range (p + 1), rfnsS i) :=
        add_le_add (by linarith [hAR_w]) (by linarith [hAdR_w])
    _ ≤ 2 * (ccR p * FULL) + 2 * (ccdR p * FULL) := by
        refine add_le_add ?_ ?_
        · exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hsubR (hccR_nn p)) (by norm_num)
        · exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hsubdR (hccdR_nn p)) (by norm_num)
    _ = (2 * ccR p + 2 * ccdR p) * FULL := by ring

set_option linter.style.show false in
/-- **The pointwise `m`-fold rough-Laplacian / covariant-gradient iterated-commutator fibre bound.**

For every commutator order `m`, all covariant ranks `s` and all gradient orders `p`, there is a
nonnegative per-gradient-order constant family `Cfun : ℕ → ℝ`, uniform in `S`, with the pointwise
domination
```
rfns(∇^p ([Δ_∇, ∇^m] S))(x) ≤ Cfun p · ∑_{a ∈ range (m + p + 1)} rfns(∇^a S)(x),
```
where `[Δ_∇, ∇^m] S = Δ_∇(∇^m S) − ∇^m(Δ_∇ S)` (`∇^m S = iteratedCovGrad g₀ 0 s m S`,
`Δ_∇ = rawTensorConnLapSmooth`) and `∇^p (·) = iteratedCovGrad g₀ 0 (s + m) p (·)`.

This is the pointwise (`riemannianFiberNormSq`) analogue of
`iteratedRoughLapGrad_commutator_l2Norm_le_aux`; it is **proved** here (no `sorry`) by the same
telescoping induction on `m`, simultaneously for all `s` and all `p`.  The recursion
`[Δ_∇, ∇^{m+1}] S = pointwiseTensorCurv g (s + m) (∇^m S) + ∇([Δ_∇, ∇^m] S)`
(`pointwiseTensorCurv_commutator_eq` at rank `s + m` applied to `∇^m S`) feeds the first arm into the
single-level pointwise jet bound `pointwiseTensorCurv_iteratedCovGrad_fiberNormSq_jet_le` and the second
arm into the induction hypothesis at gradient order `p + 1`, with the `2`-sub-additivity
`riemannianFiberNormSq_add_le` in place of the `L²` triangle inequality. -/
private theorem iteratedRoughLapGrad_commutator_fiberNormSq_jet_le_aux
    (g₀ : SmoothRiemannianMetric I M) (m : ℕ) :
    ∀ s : ℕ, ∃ Cfun : ℕ → ℝ, (∀ p, 0 ≤ Cfun p) ∧
      ∀ (p : ℕ) (S : SmoothCcTensor g₀ 0 s) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((s + m) + p) x
            ((iteratedCovGrad (I := I) g₀ 0 (s + m) p
              (rawTensorConnLapSmooth (I := I) g₀ 0 (s + m)
                  (iteratedCovGrad (I := I) g₀ 0 s m S) -
                iteratedCovGrad (I := I) g₀ 0 s m
                  (rawTensorConnLapSmooth (I := I) g₀ 0 s S))).toSection x) ≤
          Cfun p * ∑ a ∈ Finset.range (m + p + 1),
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + a) x
              ((iteratedCovGrad (I := I) g₀ 0 s a S).toSection x) := by
  induction m with
  | zero =>
    intro s
    refine ⟨fun _ => 0, fun _ => le_refl _, fun p S x => ?_⟩
    -- `[Δ_∇, ∇^0] S = Δ_∇ S − Δ_∇ S = 0`, so its `p`-fold gradient vanishes.
    have hcomm0 :
        rawTensorConnLapSmooth (I := I) g₀ 0 (s + 0) (iteratedCovGrad (I := I) g₀ 0 s 0 S) -
            iteratedCovGrad (I := I) g₀ 0 s 0 (rawTensorConnLapSmooth (I := I) g₀ 0 s S) =
          (0 : SmoothCcTensor g₀ 0 (s + 0)) := by
      simp only [iteratedCovGrad_zero, Nat.add_zero, sub_self]
    rw [hcomm0]
    have hz : iteratedCovGrad (I := I) g₀ 0 (s + 0) p (0 : SmoothCcTensor g₀ 0 (s + 0)) =
        (0 : SmoothCcTensor g₀ 0 (s + 0 + p)) := by
      have := iteratedCovGrad_sub (I := I) (M := M) g₀ 0 (s + 0) p
        (0 : SmoothCcTensor g₀ 0 (s + 0)) (0 : SmoothCcTensor g₀ 0 (s + 0))
      simpa using this
    rw [hz]
    have hzero : ((0 : SmoothCcTensor g₀ 0 (s + 0 + p)).toSection x :
        TensorRSSpace 0 ((s + 0) + p) I x) = 0 := rfl
    rw [show ((0 : SmoothCcTensor g₀ 0 (s + 0 + p)).toSection x) =
        (0 : TensorRSSpace 0 ((s + 0) + p) I x) from hzero]
    rw [riemannianFiberNormSq_zero (I := I) (M := M) g₀ 0 ((s + 0) + p) x]
    exact mul_nonneg (le_refl 0)
      (Finset.sum_nonneg (fun a _ => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (s + a) x _))
  | succ m ih =>
    intro s
    obtain ⟨Cm, hCm_nn, hCm⟩ := ih s
    obtain ⟨K, hK_nn, hK⟩ :=
      pointwiseTensorCurv_iteratedCovGrad_fiberNormSq_jet_le (I := I) (M := M) g₀ (s + m)
    refine ⟨fun p => 2 * K p + 2 * Cm (p + 1),
      fun p => by have := hK_nn p; have := hCm_nn (p + 1); positivity, fun p S x => ?_⟩
    -- The telescoping split at the section level.
    have hsplit :
        rawTensorConnLapSmooth (I := I) g₀ 0 (s + (m + 1))
              (iteratedCovGrad (I := I) g₀ 0 s (m + 1) S) -
            iteratedCovGrad (I := I) g₀ 0 s (m + 1)
              (rawTensorConnLapSmooth (I := I) g₀ 0 s S) =
          pointwiseTensorCurv (I := I) (M := M) g₀ (s + m) (iteratedCovGrad (I := I) g₀ 0 s m S) +
            covGrad (I := I) (M := M) g₀ 0 (s + m)
              (rawTensorConnLapSmooth (I := I) g₀ 0 (s + m) (iteratedCovGrad (I := I) g₀ 0 s m S) -
                iteratedCovGrad (I := I) g₀ 0 s m (rawTensorConnLapSmooth (I := I) g₀ 0 s S)) := by
      rw [iteratedCovGrad_succ (I := I) (M := M) g₀ 0 s m S,
        iteratedCovGrad_succ (I := I) (M := M) g₀ 0 s m
          (rawTensorConnLapSmooth (I := I) g₀ 0 s S)]
      show rawTensorConnLapSmooth (I := I) g₀ 0 (s + m + 1)
            (covGrad (I := I) (M := M) g₀ 0 (s + m) (iteratedCovGrad (I := I) g₀ 0 s m S)) -
          covGrad (I := I) (M := M) g₀ 0 (s + m)
            (iteratedCovGrad (I := I) g₀ 0 s m (rawTensorConnLapSmooth (I := I) g₀ 0 s S)) =
        pointwiseTensorCurv (I := I) (M := M) g₀ (s + m) (iteratedCovGrad (I := I) g₀ 0 s m S) +
          covGrad (I := I) (M := M) g₀ 0 (s + m)
            (rawTensorConnLapSmooth (I := I) g₀ 0 (s + m) (iteratedCovGrad (I := I) g₀ 0 s m S) -
              iteratedCovGrad (I := I) g₀ 0 s m (rawTensorConnLapSmooth (I := I) g₀ 0 s S))
      rw [pointwiseTensorCurv_commutator_eq (I := I) (M := M) g₀ (s + m)
          (iteratedCovGrad (I := I) g₀ 0 s m S),
        covGrad_sub (I := I) (M := M) g₀ 0 (s + m)]
      abel
    set comm_m : SmoothCcTensor g₀ 0 (s + m) :=
      rawTensorConnLapSmooth (I := I) g₀ 0 (s + m) (iteratedCovGrad (I := I) g₀ 0 s m S) -
        iteratedCovGrad (I := I) g₀ 0 s m (rawTensorConnLapSmooth (I := I) g₀ 0 s S) with hcomm_m
    set gradm : SmoothCcTensor g₀ 0 (s + m) := iteratedCovGrad (I := I) g₀ 0 s m S with hgradm
    set fullSum : ℝ := ∑ a ∈ Finset.range (m + 1 + p + 1),
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + a) x
        ((iteratedCovGrad (I := I) g₀ 0 s a S).toSection x) with hfullSum
    have hfullSum_nn : 0 ≤ fullSum :=
      Finset.sum_nonneg (fun a _ => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (s + a) x _)
    -- Distribute `∇^p` over the split and apply `2`-sub-additivity.
    have happ :
        (iteratedCovGrad (I := I) g₀ 0 (s + (m + 1)) p
            (rawTensorConnLapSmooth (I := I) g₀ 0 (s + (m + 1))
                (iteratedCovGrad (I := I) g₀ 0 s (m + 1) S) -
              iteratedCovGrad (I := I) g₀ 0 s (m + 1)
                (rawTensorConnLapSmooth (I := I) g₀ 0 s S))).toSection x =
          (iteratedCovGrad (I := I) g₀ 0 (s + (m + 1)) p
              (pointwiseTensorCurv (I := I) (M := M) g₀ (s + m) gradm)).toSection x +
            (iteratedCovGrad (I := I) g₀ 0 (s + (m + 1)) p
              (covGrad (I := I) (M := M) g₀ 0 (s + m) comm_m)).toSection x := by
      rw [hsplit, iteratedCovGrad_add (I := I) (M := M) g₀ 0 (s + (m + 1)) p,
        SmoothCcTensor.toSection_add]
      rfl
    rw [happ]
    refine le_trans (riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 0 ((s + (m + 1)) + p) x
      ((iteratedCovGrad (I := I) g₀ 0 (s + (m + 1)) p
        (pointwiseTensorCurv (I := I) (M := M) g₀ (s + m) gradm)).toSection x)
      ((iteratedCovGrad (I := I) g₀ 0 (s + (m + 1)) p
        (covGrad (I := I) (M := M) g₀ 0 (s + m) comm_m)).toSection x)) ?_
    -- Arm 1: the single-level pointwise jet bound at rank `s + m`, applied to `∇^m S`.
    have harm1 :
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((s + (m + 1)) + p) x
            ((iteratedCovGrad (I := I) g₀ 0 (s + (m + 1)) p
              (pointwiseTensorCurv (I := I) (M := M) g₀ (s + m) gradm)).toSection x) ≤
          K p * fullSum := by
      have hKb := hK p gradm x
      -- Reindex `∇^a (∇^m S) → ∇^{m + a} S`.
      have hreindex : ∀ a,
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((s + m) + a) x
              ((iteratedCovGrad (I := I) g₀ 0 (s + m) a gradm).toSection x) =
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + (m + a)) x
              ((iteratedCovGrad (I := I) g₀ 0 s (m + a) S).toSection x) := by
        intro a
        rw [hgradm]
        exact rfns_iteratedCovGrad_comp (I := I) (M := M) g₀ 0 s m a S x
      rw [Finset.sum_congr rfl (fun a _ => hreindex a)] at hKb
      -- `hKb`'s LHS rank `((s + m) + 1) + p` is defeq to the goal's `(s + (m + 1)) + p`.
      refine hKb.trans ?_
      refine mul_le_mul_of_nonneg_left ?_ (hK_nn p)
      -- The reindexed window `∑_{a < p + 2} ‖∇^{m + a} S‖²` injects into `fullSum`.
      have hIco : ∑ a ∈ Finset.range (p + 2),
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + (m + a)) x
              ((iteratedCovGrad (I := I) g₀ 0 s (m + a) S).toSection x) =
          ∑ b ∈ Finset.Ico m (m + (p + 2)),
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + b) x
              ((iteratedCovGrad (I := I) g₀ 0 s b S).toSection x) := by
        rw [Finset.sum_Ico_eq_sum_range]
        refine Finset.sum_congr (by congr 1; omega) (fun a _ => by rw [show m + a = m + a from rfl])
      rw [hfullSum, hIco]
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_
        (fun b _ _ => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (s + b) x _)
      intro b hb; rw [Finset.mem_Ico] at hb; rw [Finset.mem_range]; omega
    -- Arm 2: the induction hypothesis at gradient order `p + 1` on `[Δ_∇, ∇^m] S`.
    have harm2 :
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((s + (m + 1)) + p) x
            ((iteratedCovGrad (I := I) g₀ 0 (s + (m + 1)) p
              (covGrad (I := I) (M := M) g₀ 0 (s + m) comm_m)).toSection x) ≤
          Cm (p + 1) * fullSum := by
      -- `∇^p (∇ comm_m) = ∇^{p+1} comm_m`; the induction hypothesis at gradient order `p + 1`.
      have hCmb := hCm (p + 1) S x
      rw [← hcomm_m] at hCmb
      have hsum_eq : ∑ a ∈ Finset.range (m + (p + 1) + 1),
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + a) x
              ((iteratedCovGrad (I := I) g₀ 0 s a S).toSection x) = fullSum := by
        rw [hfullSum, show m + (p + 1) + 1 = m + 1 + p + 1 from by omega]
      rw [hsum_eq] at hCmb
      -- Relate `∇^p (∇ comm_m)` to `∇^{p+1} comm_m` by the iterated-gradient composition.
      have h := rfns_iteratedCovGrad_comp (I := I) (M := M) g₀ 0 (s + m) 1 p comm_m x
      rw [iteratedCovGrad_succ (I := I) (M := M) g₀ 0 (s + m) 0 comm_m,
        iteratedCovGrad_zero] at h
      -- `h : rfns(∇^p (∇ comm_m)) = rfns(∇^{1+p} comm_m)`; rewrite the order `1 + p → p + 1`
      -- uniformly (both the rank index and the gradient order share the subterm `1 + p`).
      rw [Nat.add_comm 1 p] at h
      exact h.trans_le hCmb
    -- Assemble: `2·arm1 + 2·arm2 ≤ (2K + 2Cm) · fullSum`.
    calc 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((s + (m + 1)) + p) x
              ((iteratedCovGrad (I := I) g₀ 0 (s + (m + 1)) p
                (pointwiseTensorCurv (I := I) (M := M) g₀ (s + m) gradm)).toSection x) +
            2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((s + (m + 1)) + p) x
              ((iteratedCovGrad (I := I) g₀ 0 (s + (m + 1)) p
                (covGrad (I := I) (M := M) g₀ 0 (s + m) comm_m)).toSection x)
        ≤ 2 * (K p * fullSum) + 2 * (Cm (p + 1) * fullSum) :=
          add_le_add (mul_le_mul_of_nonneg_left harm1 (by norm_num))
            (mul_le_mul_of_nonneg_left harm2 (by norm_num))
      _ = (2 * K p + 2 * Cm (p + 1)) * fullSum := by ring

/-- **(The genuine pointwise order-`a` covariant-jet bound of the linear connection
Laplacian, the Δ-arm of the sealed remainder difference — PROVED from the order-`0` rough-Laplacian
fibre posit and the pointwise iterated commutator telescope.)**

For a smooth compactly-supported `(0,2)`-tensor `W` (the perturbation difference `T − T'` at the call
site) there is a single nonnegative constant `C`, uniform over `W` and the base point `x`, such that
the order-`a` covariant gradient of the rough (connection) Laplacian `Δ_∇ W := rawTensorConnLapSmooth
g₀ 0 2 W` is dominated, at the squared fibre-norm level, by the **order-`(a + 2)` covariant jet** of
`W`:
```
rfns(∇^a (Δ_∇ W))(x) ≤ C · ∑_{q ≤ a+2} rfns(∇^q W)(x).
```

**The jet order is `a + 2`, not `a`** — the rough Laplacian is genuinely *second order*: pointwise it
is the diagonal `g₀`-trace of the Hessian `∑_i ∇²_{B_i,B_i} W`, so `Δ_∇ W` reads `∇²W` already at order
`0`, and commuting the order-`a` gradient past `Δ_∇` advances the read order by exactly two.  A window-`a`
bound (`q ≤ a`) is FALSE: the rough Laplacian loses exactly two derivatives.

**Assembly.**  Splitting `∇^a(Δ_∇ W) = Δ_∇(∇^a W) − [Δ_∇, ∇^a]W` (the iterated commutator, `abel`),
the `2`-sub-additivity of the squared fibre norm bounds `rfns(∇^a(Δ_∇ W))` by `2·rfns(Δ_∇(∇^a W)) +
2·rfns([Δ_∇, ∇^a]W)`.  The **top-jet** term `Δ_∇(∇^a W)` is dominated by the order-`0` rough-Laplacian
fibre posit `rawTensorConnLapSmooth_fiberNormSq_le_secondCovGrad_jet` at rank `2 + a` applied to
`∇^a W`, whose `∇²(∇^a W)` reindexes (`rfns_iteratedCovGrad_comp`) onto the genuine `q = a + 2` jet
`∇^{a+2}W`; the **lower-order** commutator term is dominated by the pointwise iterated-commutator
telescope `iteratedRoughLapGrad_commutator_fiberNormSq_jet_le_aux` at `m := a`, `p := 0`, `s := 2`,
controlled by the `∇^{≤ a}W` jets.  Both land in the read window `q ≤ a + 2`.

**Non-vacuity / order self-check.**  The bound reads `∇^{≤ a+2}W`; the `q = a + 2` term is the genuine
top jet (the second-order Laplacian read), so a window-`a` weakening is rejected.  A `C = 0` witness is
rejected by a nonvanishing `∇^a (Δ_∇ W)` for a non-flat `W`. -/
private theorem rawTensorConnLapSmooth_iteratedCovGrad_riemannianFiberNormSq_jet_le
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ) :
    ∃ C : ℝ,
      0 ≤ C ∧
      ∀ (W : SmoothCcTensor g₀ 0 2) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + a) x
            ((iteratedCovGrad (I := I) g₀ 0 2 a
              (rawTensorConnLapSmooth (I := I) g₀ 0 2 W)).toSection x) ≤
          C * ∑ q ∈ Finset.range (a + 2 + 1),
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + q) x
              ((iteratedCovGrad (I := I) g₀ 0 2 q W).toSection x) := by
  classical
  -- The order-`0` rough-Laplacian fibre posit at rank `2 + a` (the top-jet Δ-arm).
  obtain ⟨Cpost, hCpost_nn, hCpost⟩ :=
    rawTensorConnLapSmooth_fiberNormSq_le_secondCovGrad_jet (I := I) (M := M) g₀ (2 + a)
  -- The pointwise iterated-commutator telescope at `m := a`, `s := 2` (the lower-order arm).
  obtain ⟨Cfun, hCfun_nn, hCfun⟩ :=
    iteratedRoughLapGrad_commutator_fiberNormSq_jet_le_aux (I := I) (M := M) g₀ a 2
  refine ⟨2 * Cpost + 2 * Cfun 0, by have := hCfun_nn 0; positivity, fun W x => ?_⟩
  set Scol : ℝ := ∑ q ∈ Finset.range (a + 2 + 1),
    riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + q) x
      ((iteratedCovGrad (I := I) g₀ 0 2 q W).toSection x) with hScol_def
  have hScol_nn : 0 ≤ Scol :=
    Finset.sum_nonneg fun q _ => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + q) x _
  -- The iterated-commutator section, and the `abel` split `∇^a(Δ_∇ W) = Δ_∇(∇^a W) − Comm`.
  set Comm : SmoothCcTensor g₀ 0 (2 + a) :=
    rawTensorConnLapSmooth (I := I) g₀ 0 (2 + a) (iteratedCovGrad (I := I) g₀ 0 2 a W) -
      iteratedCovGrad (I := I) g₀ 0 2 a (rawTensorConnLapSmooth (I := I) g₀ 0 2 W) with hComm_def
  have hsplit :
      iteratedCovGrad (I := I) g₀ 0 2 a (rawTensorConnLapSmooth (I := I) g₀ 0 2 W) =
        rawTensorConnLapSmooth (I := I) g₀ 0 (2 + a) (iteratedCovGrad (I := I) g₀ 0 2 a W) +
          (-Comm) := by
    rw [hComm_def]; abel
  have hsec :
      (iteratedCovGrad (I := I) g₀ 0 2 a
          (rawTensorConnLapSmooth (I := I) g₀ 0 2 W)).toSection x =
        (rawTensorConnLapSmooth (I := I) g₀ 0 (2 + a) (iteratedCovGrad (I := I) g₀ 0 2 a W)).toSection x +
          (-Comm).toSection x := by
    rw [hsplit, SmoothCcTensor.toSection_add]; rfl
  rw [hsec]
  refine le_trans (riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 0 (2 + a) x
    ((rawTensorConnLapSmooth (I := I) g₀ 0 (2 + a) (iteratedCovGrad (I := I) g₀ 0 2 a W)).toSection x)
    ((-Comm).toSection x)) ?_
  -- The Δ-arm: order-`0` fibre posit at `S := ∇^a W`, top jet `q = a + 2`.
  have hΔarm :
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + a) x
          ((rawTensorConnLapSmooth (I := I) g₀ 0 (2 + a)
            (iteratedCovGrad (I := I) g₀ 0 2 a W)).toSection x) ≤ Cpost * Scol := by
    refine (hCpost (iteratedCovGrad (I := I) g₀ 0 2 a W) x).trans ?_
    -- `rfns(∇²(∇^a W)) = rfns(∇^{a+2} W)`, the `q = a + 2` summand of `Scol`.
    have hreindex :
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((2 + a) + 2) x
            ((iteratedCovGrad (I := I) g₀ 0 (2 + a) 2 (iteratedCovGrad (I := I) g₀ 0 2 a W)).toSection x) =
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (a + 2)) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (a + 2) W).toSection x) :=
      rfns_iteratedCovGrad_comp (I := I) (M := M) g₀ 0 2 a 2 W x
    rw [hreindex]
    refine mul_le_mul_of_nonneg_left ?_ hCpost_nn
    rw [hScol_def]
    refine Finset.single_le_sum
      (f := fun q => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + q) x
        ((iteratedCovGrad (I := I) g₀ 0 2 q W).toSection x))
      (fun q _ => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + q) x _) ?_
    rw [Finset.mem_range]; omega
  -- The commutator arm: telescope at `m = a`, `p = 0`, `s = 2`, lower-order jets `q ≤ a`.
  have hCommarm :
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + a) x ((-Comm).toSection x) ≤
        Cfun 0 * Scol := by
    -- `rfns((-Comm)(x)) = rfns(Comm(x))` by negation-invariance of the fibre norm.
    have hneg : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + a) x ((-Comm).toSection x) =
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + a) x (Comm.toSection x) := by
      rw [SmoothCcTensor.toSection_neg]
      rw [show ((-Comm.toSection) x : TensorRSSpace 0 (2 + a) I x) = -(Comm.toSection x) from rfl]
      exact riemannianFiberNormSq_neg_value (I := I) (M := M) g₀ 0 (2 + a) x (Comm.toSection x)
    rw [hneg]
    -- The telescope at `m = a`, `p = 0`, `s = 2`; `∇^0 [Δ_∇, ∇^a]W = Comm` (`(2 + a) + 0 = 2 + a`).
    have hC := hCfun 0 W x
    rw [iteratedCovGrad_zero] at hC
    refine hC.trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (hCfun_nn 0)
    rw [hScol_def]
    -- The telescope window `∑_{a' < a + 0 + 1}` injects into `∑_{q < a + 2 + 1}`.
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_
      (fun q _ _ => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + q) x _)
    intro q hq; rw [Finset.mem_range] at hq ⊢; omega
  calc 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + a) x
            ((rawTensorConnLapSmooth (I := I) g₀ 0 (2 + a)
              (iteratedCovGrad (I := I) g₀ 0 2 a W)).toSection x) +
          2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + a) x ((-Comm).toSection x)
      ≤ 2 * (Cpost * Scol) + 2 * (Cfun 0 * Scol) :=
        add_le_add (mul_le_mul_of_nonneg_left hΔarm (by norm_num))
          (mul_le_mul_of_nonneg_left hCommarm (by norm_num))
    _ = (2 * Cpost + 2 * Cfun 0) * Scol := by ring

/-- **The reverse chart-component Euclidean coordinate bridge (`E`-jet ≤ `EuclN`-jet).**
For `S : SmoothCcTensor g 0 2`, the order-`m` `iteratedFDerivWithin` jet of the `E`-coordinate raw
chart component `rawCompOnE` on the chart-target interior is bounded by `‖toEuclidean‖^m` times the
order-`m` plain `EuclN` Fréchet jet of `rawPullR` at the `toEuclidean`-image point.  This is the
companion of the forward bridge `norm_iteratedFDeriv_rawPullR_le_iteratedFDerivWithin_rawCompOnE`,
proved by the same composition-with-the-continuous-linear-equivalence argument with `toEuclidean`
in place of `toEuclidean.symm`. -/
private lemma norm_iteratedFDerivWithin_rawCompOnE_le_iteratedFDeriv_rawPullR
    (g : SmoothRiemannianMetric I M)
    (S : DifferentialGeometry.Integral.L2.SmoothCcTensor g 0 2) (α : M)
    (Jdx : Fin 2 → Fin (Module.finrank ℝ E)) (m : ℕ) {y : E}
    (hy : y ∈ interior (extChartAt I α).target) :
    ‖iteratedFDerivWithin ℝ m
        (DeTurckCoefficients.rawCompOnE (I := I) (M := M) g S α Jdx)
        (interior (extChartAt I α).target) y‖ ≤
      ‖((toEuclidean (E := E)) : E →L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))‖ ^ m *
        ‖iteratedFDeriv ℝ m (rawPullR (I := I) (M := M) g 0 2 S α
            (![] : Fin 0 → Fin (Module.finrank ℝ E)) Jdx) ((toEuclidean (E := E)) y)‖ := by
  classical
  set e : E ≃L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) := toEuclidean (E := E) with he_def
  set O : Set E := interior (extChartAt I α).target with hO_def
  have hO_open : IsOpen O := isOpen_interior
  have hUD : UniqueDiffOn ℝ O := hO_open.uniqueDiffOn
  -- `rawCompOnE = rawPullR ∘ e`, with `e := toEuclidean`.
  have hcompose :
      DeTurckCoefficients.rawCompOnE (I := I) (M := M) g S α Jdx =
        rawPullR (I := I) (M := M) g 0 2 S α (![] : Fin 0 → Fin (Module.finrank ℝ E)) Jdx ∘ ⇑e := by
    have hpull := rawPullR_eq_rawCompOnE_comp (I := I) (M := M) g S α Jdx
    funext z
    have := congrArg (fun f => f (e z)) hpull
    simp only [Function.comp_apply, he_def, ContinuousLinearEquiv.symm_apply_apply] at this ⊢
    rw [← this]
  rw [hcompose]
  -- The image set `e '' O` is open and `iteratedFDeriv (rawPullR) = iteratedFDerivWithin … (e '' O)`.
  have himg_open : IsOpen (e '' O) := e.isOpenMap _ hO_open
  have hey_mem : e y ∈ e '' O := ⟨y, hy, rfl⟩
  have hOeq : O = e ⁻¹' (e '' O) := by
    ext z; constructor
    · intro hz; exact ⟨z, hz, rfl⟩
    · rintro ⟨w, hw, hwz⟩; rwa [e.injective hwz] at hw
  -- Composition-on-the-right within-jet formula on the open image.
  have hcomp := e.iteratedFDerivWithin_comp_right
    (f := rawPullR (I := I) (M := M) g 0 2 S α (![] : Fin 0 → Fin (Module.finrank ℝ E)) Jdx)
    himg_open.uniqueDiffOn (x := y) hey_mem m
  rw [← hOeq] at hcomp
  rw [hcomp]
  -- The within-jet of `rawPullR` on the open image equals the plain jet.
  have hplain : iteratedFDerivWithin ℝ m
      (rawPullR (I := I) (M := M) g 0 2 S α (![] : Fin 0 → Fin (Module.finrank ℝ E)) Jdx)
      (e '' O) (e y) =
      iteratedFDeriv ℝ m
        (rawPullR (I := I) (M := M) g 0 2 S α (![] : Fin 0 → Fin (Module.finrank ℝ E)) Jdx) (e y) :=
    iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) m himg_open hey_mem
  rw [hplain]
  -- The composed multilinear map has norm `≤ ‖∂^m rawPullR (e y)‖ · ‖e‖^m`.
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have he_norm : ‖(e : E →L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))‖ =
      ‖((toEuclidean (E := E)) : E →L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))‖ := rfl
  rw [he_norm, mul_comm]

/-- **The `E`-coordinate bare chart-jet content is dominated by the square roots of the intrinsic
covariant fibre-norm jets, on the partition-of-unity support.**

The `E`-coordinate analog of `DeTurckCoefficients.bareChartJetContent_le_sqrt_fiberNormSq_sum`: for a
smooth compactly-supported `(0,2)`-tensor `D`, chart `α`, order `N`, and a base point `b` of the
closed POU support of the chart-`α` weight, the `E`-coordinate bare chart-jet content
`bareChartJetContentOnE D α N (extChartAt I α b)` is dominated by a single uniform constant times
`∑_{i ≤ N} √rfns(∇^i D)(b)`.  It is the reverse Euclidean coordinate bridge composed with the
`EuclN` content Stage-4 bound. -/
private lemma bareChartJetContentOnE_le_sqrt_fiberNormSq_sum
    (g : SmoothRiemannianMetric I M)
    (D : DifferentialGeometry.Integral.L2.SmoothCcTensor g 0 2) (α : M) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {b : M},
        b ∈ tsupport (fun x : M =>
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) →
        DeTurckCoefficients.bareChartJetContentOnE (I := I) (M := M) g D α N (extChartAt I α b) ≤
          C * ∑ i ∈ Finset.range (N + 1),
            Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g 0 (2 + i) b
              ((iteratedCovGrad (I := I) g 0 2 i D).toSection b)) := by
  classical
  set n : ℕ := Module.finrank ℝ E with hn_def
  set eNorm : ℝ := ‖((toEuclidean (E := E)) : E →L[ℝ] EuclideanSpace ℝ (Fin n))‖ with heNorm_def
  have heNorm_nn : 0 ≤ eNorm := norm_nonneg _
  set eFac : ℝ := (Finset.range (N + 1)).sup' (by simp) (fun m => eNorm ^ m) with heFac_def
  have heFac_nn : 0 ≤ eFac := le_trans (by positivity : (0:ℝ) ≤ eNorm ^ 0)
    (Finset.le_sup' (fun m => eNorm ^ m) (by simp))
  obtain ⟨Cstage, hCstage_nn, hCstage⟩ :=
    bareChartJetContent_le_sqrt_fiberNormSq_sum (I := I) (M := M) g 0 2 D α N
  refine ⟨eFac * Cstage, by positivity, ?_⟩
  intro b hb
  set y : E := extChartAt I α b with hy_def
  have hb_src : b ∈ (extChartAt I α).source := by
    rw [extChartAt_source]
    exact DifferentialGeometry.Integral.Measure.chartAtlasPOU_isSubordinate I M α hb
  have hy_target : y ∈ (extChartAt I α).target := (extChartAt I α).map_source hb_src
  have hy_int : y ∈ interior (extChartAt I α).target := by
    rw [(isOpen_extChartAt_target (I := I) α).interior_eq]; exact hy_target
  -- The `toEuclidean`-image of `y` is the POU-kernel point feeding the `EuclN` Stage-4 bound.
  set yE : EuclideanSpace ℝ (Fin n) := (toEuclidean (E := E)) y with hyE_def
  have hyE_kernel : yE ∈
      DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartPouKernel (I := I) (M := M) α := by
    refine ⟨y, ?_, rfl⟩
    exact ⟨b, hb, rfl⟩
  -- The chart preimage of `yE` recovers `b`.
  have hround : (extChartAt I α).symm ((toEuclidean (E := E)).symm yE) = b := by
    rw [hyE_def, hy_def, ContinuousLinearEquiv.symm_apply_apply]
    exact (extChartAt I α).left_inv hb_src
  have hstage := hCstage hyE_kernel
  rw [hround] at hstage
  -- Per-`Jdx`, per-order: reverse bridge transfers the `E`-jet to the `EuclN`-jet.
  -- The order-column of one `(![] , Jdx)` pair, in `EuclN`.
  set colE : (Fin 2 → Fin n) → ℝ := fun Jdx =>
    ∑ m ∈ Finset.range (N + 1),
      ‖iteratedFDeriv ℝ m (rawPullR (I := I) (M := M) g 0 2 D α (![] : Fin 0 → Fin n) Jdx) yE‖
    with hcolE_def
  have hcolE_nn : ∀ Jdx, 0 ≤ colE Jdx := fun Jdx =>
    Finset.sum_nonneg fun m _ => norm_nonneg _
  have hbridge : DeTurckCoefficients.bareChartJetContentOnE (I := I) (M := M) g D α N y ≤
      eFac * bareChartJetContent (I := I) (M := M) g 0 2 D α N yE := by
    -- First: the `E`-content is bounded by `eFac · ∑_{Jdx} colE Jdx`.
    have hstep1 : DeTurckCoefficients.bareChartJetContentOnE (I := I) (M := M) g D α N y ≤
        eFac * ∑ Jdx : Fin 2 → Fin n, colE Jdx := by
      rw [DeTurckCoefficients.bareChartJetContentOnE, Finset.mul_sum]
      refine Finset.sum_le_sum (fun Jdx _ => ?_)
      rw [hcolE_def, Finset.mul_sum]
      refine Finset.sum_le_sum (fun m hm => ?_)
      have hmN : m ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
      have hb' := norm_iteratedFDerivWithin_rawCompOnE_le_iteratedFDeriv_rawPullR
        (I := I) (M := M) g D α Jdx m hy_int
      rw [show (toEuclidean (E := E)) y = yE from rfl] at hb'
      refine hb'.trans ?_
      refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
      exact Finset.le_sup' (fun m => eNorm ^ m) (Finset.mem_range.mpr (Nat.lt_succ_of_le hmN))
    -- Second: `bareChartJetContent = ∑_{Jdx} colE Jdx` (the `(Fin 0 → Fin n)` factor is a singleton).
    have hstep2 : bareChartJetContent (I := I) (M := M) g 0 2 D α N yE =
        ∑ Jdx : Fin 2 → Fin n, colE Jdx := by
      rw [bareChartJetContent, Fintype.sum_prod_type, Fintype.sum_unique]
      refine Finset.sum_congr rfl (fun Jdx _ => ?_)
      rw [hcolE_def]
      refine Finset.sum_congr rfl (fun m _ => ?_)
      congr 2
    rw [hstep2]
    exact hstep1
  calc DeTurckCoefficients.bareChartJetContentOnE (I := I) (M := M) g D α N y
      ≤ eFac * bareChartJetContent (I := I) (M := M) g 0 2 D α N yE := hbridge
    _ ≤ eFac * (Cstage * ∑ i ∈ Finset.range (N + 1),
          Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g 0 (2 + i) b
            ((iteratedCovGrad (I := I) g 0 2 i D).toSection b))) :=
        mul_le_mul_of_nonneg_left hstage heFac_nn
    _ = (eFac * Cstage) * ∑ i ∈ Finset.range (N + 1),
          Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g 0 (2 + i) b
            ((iteratedCovGrad (I := I) g 0 2 i D).toSection b)) := by ring

/-- The raw chart-frame component depends only on the underlying section, not on the (phantom)
metric type-tag of the `SmoothCcTensor`. -/
private lemma tensorChartComponentRaw_toSection_congr
    (g g' : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (S' : SmoothCcTensor g' r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) (x : M)
    (hSS' : S.toSection x = S'.toSection x) :
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentRaw
        (I := I) (M := M) g r s S α Idx Jdx x =
      DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentRaw
          (I := I) (M := M) g' r s S' α Idx Jdx x := by
  unfold DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentRaw
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorTrivProj
  rw [hSS']

/-- Subtractivity of the raw chart-frame component in the tensor argument. -/
private lemma tensorChartComponentRaw_sub'
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S₁ S₂ : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) (x : M) :
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentRaw
        (I := I) (M := M) g r s (S₁ - S₂) α Idx Jdx x =
      DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentRaw
          (I := I) (M := M) g r s S₁ α Idx Jdx x -
        DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentRaw
          (I := I) (M := M) g r s S₂ α Idx Jdx x := by
  have hsub : S₁ - S₂ = S₁ + (-1 : ℝ) • S₂ := by
    rw [neg_one_smul]; abel
  rw [hsub,
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentRaw_add
      (I := I) (M := M) g r s S₁ ((-1 : ℝ) • S₂) α Idx Jdx x,
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentRaw_smul
      (I := I) (M := M) g r s (-1 : ℝ) S₂ α Idx Jdx x]
  rw [smul_eq_mul]; ring

/-- **The Ricci–DeTurck RHS-arm residual, as the genuine RHS-difference smooth tensor.**
The Δ-arms cancel: `(deTurckSmoothRemainder T − deTurckSmoothRemainder T') + Δ_∇(T − T')` equals the
re-tagged Ricci–DeTurck RHS difference `deTurckRHSSectionBg g_bg (g₀+T) − deTurckRHSSectionBg g_bg (g₀+T')`
at the `toSection` level. -/
private lemma deTurckRHSArm_toSection_eq
    (g₀ g_bg : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ') :
    ((deTurckSmoothRemainder (I := I) g₀ g_bg T hδ_lt hδ -
        deTurckSmoothRemainder (I := I) g₀ g_bg T' hδ'_lt hδ') +
      rawTensorConnLapSmooth (I := I) g₀ 0 2 (T - T')).toSection =
      ((deTurckRHSSectionBg (I := I) g_bg
            (tensorSectionRealizeMetric (I := I) g₀ T hδ_lt hδ)).toSection -
        (deTurckRHSSectionBg (I := I) g_bg
            (tensorSectionRealizeMetric (I := I) g₀ T' hδ'_lt hδ')).toSection) := by
  classical
  rw [SmoothCcTensor.toSection_add, SmoothCcTensor.toSection_sub]
  rw [rawTensorConnLapSmooth_sub (I := I) g₀ 0 2 T T']
  -- Unfold both `deTurckSmoothRemainder = RHSwrap − Δ_∇` at the `toSection` level.
  change (((deTurckRHSSectionBg (I := I) g_bg
            (tensorSectionRealizeMetric (I := I) g₀ T hδ_lt hδ)).toSection -
        (rawTensorConnLapSmooth (I := I) g₀ 0 2 T).toSection) -
      ((deTurckRHSSectionBg (I := I) g_bg
            (tensorSectionRealizeMetric (I := I) g₀ T' hδ'_lt hδ')).toSection -
        (rawTensorConnLapSmooth (I := I) g₀ 0 2 T').toSection)) +
      ((rawTensorConnLapSmooth (I := I) g₀ 0 2 T).toSection -
        (rawTensorConnLapSmooth (I := I) g₀ 0 2 T').toSection) =
      _
  abel

/-- **The chart-`α` raw `(0,2)`-component of the Ricci–DeTurck RHS-arm residual equals the chart
Ricci–DeTurck carrier difference of the realized metrics, on the chart-`α` Levi–Civita good set.**
On the good set (which contains the full chart-target interior preimage and the POU support under the
boundaryless assumption) the raw chart component of `RHSarm = RHSwrap T − RHSwrap T'` reads off the
textbook chart polynomial difference `chartDeTurckRicciRHS (g₀+T) g_bg − chartDeTurckRicciRHS (g₀+T') g_bg`. -/
private lemma tensorChartComponentRaw_deTurckRHSArm_eq_chartDeTurckRicciRHS_diff
    (g₀ g_bg : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (α : M) {b : M}
    (hb : b ∈ DifferentialGeometry.Integral.Connection.chartLeviCivitaGoodSet (I := I) α)
    (Jdx : Fin 2 → Fin (Module.finrank ℝ E)) :
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentRaw
        (I := I) (M := M) g₀ 0 2
        ((deTurckSmoothRemainder (I := I) g₀ g_bg T hδ_lt hδ -
            deTurckSmoothRemainder (I := I) g₀ g_bg T' hδ'_lt hδ') +
          rawTensorConnLapSmooth (I := I) g₀ 0 2 (T - T'))
        α (![] : Fin 0 → Fin (Module.finrank ℝ E)) Jdx b =
      DeTurckCoefficients.chartDeTurckRicciRHS (I := I)
          (tensorSectionRealizeMetric (I := I) g₀ T hδ_lt hδ) g_bg α (Jdx 0) (Jdx 1)
          (extChartAt I α b) -
        DeTurckCoefficients.chartDeTurckRicciRHS (I := I)
          (tensorSectionRealizeMetric (I := I) g₀ T' hδ'_lt hδ') g_bg α (Jdx 0) (Jdx 1)
          (extChartAt I α b) := by
  classical
  set g₁ := tensorSectionRealizeMetric (I := I) g₀ T hδ_lt hδ with hg₁_def
  set g₂ := tensorSectionRealizeMetric (I := I) g₀ T' hδ'_lt hδ' with hg₂_def
  set RHSarm : SmoothCcTensor g₀ 0 2 :=
    (deTurckSmoothRemainder (I := I) g₀ g_bg T hδ_lt hδ -
        deTurckSmoothRemainder (I := I) g₀ g_bg T' hδ'_lt hδ') +
      rawTensorConnLapSmooth (I := I) g₀ 0 2 (T - T') with hRHSarm_def
  set S₁ : SmoothCcTensor g₀ 0 2 :=
    { toSection := (deTurckRHSSectionBg (I := I) g_bg g₁).toSection
      hasCompactSupport := (deTurckRHSSectionBg (I := I) g_bg g₁).hasCompactSupport } with hS₁_def
  set S₂ : SmoothCcTensor g₀ 0 2 :=
    { toSection := (deTurckRHSSectionBg (I := I) g_bg g₂).toSection
      hasCompactSupport := (deTurckRHSSectionBg (I := I) g_bg g₂).hasCompactSupport } with hS₂_def
  -- `RHSarm.toSection = S₁.toSection − S₂.toSection`, so `RHSarm = S₁ − S₂` as `SmoothCcTensor`.
  have hsec : RHSarm.toSection = (S₁ - S₂).toSection := by
    rw [SmoothCcTensor.toSection_sub]
    exact deTurckRHSArm_toSection_eq (I := I) g₀ g_bg T T' hδ_lt hδ hδ'_lt hδ'
  have hRHSeq : RHSarm = S₁ - S₂ := by
    apply DifferentialGeometry.Integral.L2.SmoothCcTensor.ext
    exact hsec
  rw [hRHSeq]
  -- Linearity of the raw component + the per-metric chart identity.
  rw [tensorChartComponentRaw_sub' (I := I) (M := M) g₀ 0 2 S₁ S₂ α _ Jdx b]
  have hS₁comp : DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentRaw
        (I := I) (M := M) g₀ 0 2 S₁ α (![] : Fin 0 → Fin (Module.finrank ℝ E)) Jdx b =
      DeTurckCoefficients.chartDeTurckRicciRHS (I := I) g₁ g_bg α (Jdx 0) (Jdx 1)
        (extChartAt I α b) := by
    rw [tensorChartComponentRaw_toSection_congr (I := I) (M := M) g₀ g_bg 0 2 S₁
      (deTurckRHSSectionBg (I := I) g_bg g₁) α (![] : Fin 0 → Fin (Module.finrank ℝ E)) Jdx b rfl]
    rw [DeTurckCoefficients.chartDeTurckRicciRHS_def]
    rw [← DeTurckCoefficients.tensorChartComponentRaw_deTurckRHSSectionBg_eq_chartRicciLie
      (I := I) (M := M) g_bg g₁ α hb (![] : Fin 0 → Fin (Module.finrank ℝ E)) Jdx]
  have hS₂comp : DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentRaw
        (I := I) (M := M) g₀ 0 2 S₂ α (![] : Fin 0 → Fin (Module.finrank ℝ E)) Jdx b =
      DeTurckCoefficients.chartDeTurckRicciRHS (I := I) g₂ g_bg α (Jdx 0) (Jdx 1)
        (extChartAt I α b) := by
    rw [tensorChartComponentRaw_toSection_congr (I := I) (M := M) g₀ g_bg 0 2 S₂
      (deTurckRHSSectionBg (I := I) g_bg g₂) α (![] : Fin 0 → Fin (Module.finrank ℝ E)) Jdx b rfl]
    rw [DeTurckCoefficients.chartDeTurckRicciRHS_def]
    rw [← DeTurckCoefficients.tensorChartComponentRaw_deTurckRHSSectionBg_eq_chartRicciLie
      (I := I) (M := M) g_bg g₂ α hb (![] : Fin 0 → Fin (Module.finrank ℝ E)) Jdx]
  rw [hS₁comp, hS₂comp]

/-- **The bare chart-jet content of the Ricci–DeTurck RHS-arm residual is dominated by the square
roots of the intrinsic covariant fibre-norm jets of the perturbation difference.**

For the RHS-arm residual `RHSarm = (deTurckSmoothRemainder T − deTurckSmoothRemainder T') + Δ_∇(T − T')`,
chart `α`, order `a`, and a base point `b` of the closed POU support of the chart-`α` weight, the
order-`a` `EuclN` bare chart-jet content of `RHSarm` at the `toEuclidean`-image point is dominated by a
single nonnegative per-pair constant times `∑_{q ≤ a+2} √rfns(∇^q (T − T'))(b)`.

The proof routes each chart Fréchet jet of `RHSarm` through the reverse Euclidean coordinate bridge to
its `E`-coordinate `rawCompOnE` jet, identifies `rawCompOnE RHSarm` with the chart Ricci–DeTurck carrier
difference of the realized metrics on the chart-target interior (the Δ-arms cancel and the raw component
reads off the textbook chart polynomial on the chart Levi–Civita good set, which under the boundaryless
assumption contains the whole interior preimage), bounds that by the chart-jet Nemytskii estimate
`chartDeTurckRicciRHS_realize_seminorm_le_bareChartJetContentOnE` (the second-order `+2`
quasilinearity), and finally converts the `E`-coordinate content of `T − T'` to the intrinsic
fibre-norm jets via `bareChartJetContentOnE_le_sqrt_fiberNormSq_sum`. -/
private lemma bareChartJetContent_deTurckRHSArm_le_sqrt_fiberNormSq_sum
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (α : M) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ {b : M},
        b ∈ tsupport (fun x : M =>
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) →
        bareChartJetContent (I := I) (M := M) g₀ 0 2
            ((deTurckSmoothRemainder (I := I) g₀ g_bg T hδ_lt hδ -
                deTurckSmoothRemainder (I := I) g₀ g_bg T' hδ'_lt hδ') +
              rawTensorConnLapSmooth (I := I) g₀ 0 2 (T - T')) α a
            ((toEuclidean (E := E)) (extChartAt I α b)) ≤
          K * ∑ q ∈ Finset.range (a + 2 + 1),
            Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + q) b
              ((iteratedCovGrad (I := I) g₀ 0 2 q (T - T')).toSection b)) := by
  classical
  set n : ℕ := Module.finrank ℝ E with hn_def
  set g₁ := tensorSectionRealizeMetric (I := I) g₀ T hδ_lt hδ with hg₁_def
  set g₂ := tensorSectionRealizeMetric (I := I) g₀ T' hδ'_lt hδ' with hg₂_def
  set RHSarm : SmoothCcTensor g₀ 0 2 :=
    (deTurckSmoothRemainder (I := I) g₀ g_bg T hδ_lt hδ -
        deTurckSmoothRemainder (I := I) g₀ g_bg T' hδ'_lt hδ') +
      rawTensorConnLapSmooth (I := I) g₀ 0 2 (T - T') with hRHSarm_def
  -- The fixed compact target neighbourhood (the chart image of the closed POU support).
  set Kc : Set E := (extChartAt I α) '' (tsupport (fun x : M =>
      ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)) with hKc_def
  have hKc_compact : IsCompact Kc :=
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartImage_pouTsupport_isCompact
      (I := I) (M := M) α
  have hKc_sub : Kc ⊆ interior ((extChartAt I α).target : Set E) :=
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartImage_pouTsupport_subset_interior_target
      (I := I) (M := M) α
  -- The forward-bridge factor (`EuclN`-jet ≤ `E`-jet, scaled by `‖toEuclidean.symm‖^m`).
  set eNorm : ℝ :=
    ‖((toEuclidean (E := E)).symm : EuclideanSpace ℝ (Fin n) →L[ℝ] E)‖ with heNorm_def
  set eFac : ℝ := (Finset.range (a + 1)).sup' (by simp) (fun m => eNorm ^ m) with heFac_def
  have heFac_nn : 0 ≤ eFac := le_trans (by positivity : (0:ℝ) ≤ eNorm ^ 0)
    (Finset.le_sup' (fun m => eNorm ^ m) (by simp))
  -- **Two-metric Nemytskii** (`g₀`-anchored realization, `g_bg` background, `g₀ ≠ g_bg`): the order-`a`
  -- seminorm of the chart Ricci–DeTurck carrier difference is bounded by `C·bareChartJetContentOnE g₀`.
  -- Assembled from `hasChartJetLip_chartDeTurckRicciRHS g₁ g₂ g_bg .seminorm_le` and the `g₀`-anchored
  -- chart-Gram realize-difference jet bound (the realize bound's first slot is the anchor — here `g₀`).
  have hNem : ∀ ik : Fin n × Fin n, ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ Kc,
      DeTurckCoefficients.iteratedFDerivSeminorm a
          (fun z => DeTurckCoefficients.chartDeTurckRicciRHS (I := I) g₁ g_bg α ik.1 ik.2 z -
            DeTurckCoefficients.chartDeTurckRicciRHS (I := I) g₂ g_bg α ik.1 ik.2 z)
          (interior (extChartAt I α).target) y ≤
        C * DeTurckCoefficients.bareChartJetContentOnE (I := I) (M := M) g₀ (T - T') α (a + 2) y := by
    intro ik
    obtain ⟨C, hC_pos, hC⟩ :=
      (DeTurckCoefficients.hasChartJetLip_chartDeTurckRicciRHS (I := I) (M := M) g₁ g₂ g_bg α
        hKc_compact hKc_sub ik.1 ik.2).seminorm_le a
    refine ⟨C * ((n : ℝ)), by positivity, fun y hy => ?_⟩
    have hyint : y ∈ interior (extChartAt I α).target := hKc_sub hy
    refine (hC y hy).trans ?_
    have hgram := DeTurckCoefficients.chartGramJetDiffSeminormSum_realize_le_bareChartJetContentOnE
      (I := I) (M := M) g₀ T T' hδ_lt hδ hδ'_lt hδ' α (a + 2) hyint
    rw [← hg₁_def, ← hg₂_def] at hgram
    calc C * DeTurckCoefficients.chartGramJetDiffSeminormSum (I := I) (M := M) (a + 2) g₁ g₂ α
          (interior (extChartAt I α).target) y
        ≤ C * (((n : ℝ)) *
            DeTurckCoefficients.bareChartJetContentOnE (I := I) (M := M) g₀ (T - T') α (a + 2) y) :=
          mul_le_mul_of_nonneg_left hgram hC_pos.le
      _ = (C * ((n : ℝ))) *
            DeTurckCoefficients.bareChartJetContentOnE (I := I) (M := M) g₀ (T - T') α (a + 2) y := by
          ring
  choose CNem hCNem_nn hCNem using hNem
  set CNemMax : ℝ := Finset.univ.sup' (Finset.univ_nonempty (α := Fin n × Fin n)) CNem
    with hCNemMax_def
  have hCNemMax_nn : 0 ≤ CNemMax :=
    le_trans (hCNem_nn (Classical.arbitrary _)) (Finset.le_sup' CNem (Finset.mem_univ _))
  -- The `E`-content Stage-4 constant (anchored at `g₀`, so the fibre-norm jets are `g₀`-tagged).
  obtain ⟨Cstage, hCstage_nn, hCstage⟩ :=
    bareChartJetContentOnE_le_sqrt_fiberNormSq_sum (I := I) (M := M) g₀ (T - T') α (a + 2)
  refine ⟨((n : ℝ) ^ 2) * (((a : ℝ) + 1) * (eFac * (CNemMax * Cstage))),
    by positivity, ?_⟩
  intro b hb
  -- Setup the manifold/chart points.
  have hb_src : b ∈ (extChartAt I α).source := by
    rw [extChartAt_source]
    exact DifferentialGeometry.Integral.Measure.chartAtlasPOU_isSubordinate I M α hb
  set yb : E := extChartAt I α b with hyb_def
  have hyb_Kc : yb ∈ Kc := ⟨b, hb, rfl⟩
  have hyb_int : yb ∈ interior ((extChartAt I α).target : Set E) := hKc_sub hyb_Kc
  set yE : EuclideanSpace ℝ (Fin n) := (toEuclidean (E := E)) yb with hyE_def
  -- `b` is in the good set (boundaryless ⟹ goodset = chart source).
  have hb_good : b ∈ DifferentialGeometry.Integral.Connection.chartLeviCivitaGoodSet (I := I) α := by
    rw [DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartLeviCivitaGoodSet_eq_extChartAt_source
      (I := I) α]
    exact hb_src
  -- Stage-4 OnE bound at `b`.
  have hstage4 := hCstage hb
  -- The chartDeTurck carrier difference Stage-3 bound, per `(Jdx 0, Jdx 1)`, at the chart point.
  set Sdiff : ℝ := ∑ q ∈ Finset.range (a + 2 + 1),
    Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + q) b
      ((iteratedCovGrad (I := I) g₀ 0 2 q (T - T')).toSection b)) with hSdiff_def
  have hSdiff_nn : 0 ≤ Sdiff := Finset.sum_nonneg fun q _ => Real.sqrt_nonneg _
  -- The reduced per-`(Jdx', m)` bound: each chart Fréchet jet of `RHSarm` is `≤ const · Sdiff`.
  have hper : ∀ (Jdx : Fin 2 → Fin n) (m : ℕ), m ∈ Finset.range (a + 1) →
      ‖iteratedFDeriv ℝ m (rawPullR (I := I) (M := M) g₀ 0 2 RHSarm α
          (![] : Fin 0 → Fin n) Jdx) yE‖ ≤
        eFac * (CNemMax * Cstage) * Sdiff := by
    intro Jdx m hm
    have hmA : m ≤ a := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
    -- Forward Euclidean bridge: the `EuclN`-jet of `rawPullR` is bounded by the `E`-jet of `rawCompOnE`.
    have hyb_pre : (toEuclidean (E := E)).symm yE ∈ interior (extChartAt I α).target := by
      rw [hyE_def, ContinuousLinearEquiv.symm_apply_apply]; exact hyb_int
    have hbridge := norm_iteratedFDeriv_rawPullR_le_iteratedFDerivWithin_rawCompOnE
      (I := I) (M := M) g₀ RHSarm α Jdx m hyb_pre
    rw [hyE_def, ContinuousLinearEquiv.symm_apply_apply] at hbridge
    -- `rawCompOnE RHSarm =ᶠ F` on the interior, where `F` is the chart carrier difference.
    set F : E → ℝ := fun z =>
      DeTurckCoefficients.chartDeTurckRicciRHS (I := I) g₁ g_bg α (Jdx 0) (Jdx 1) z -
        DeTurckCoefficients.chartDeTurckRicciRHS (I := I) g₂ g_bg α (Jdx 0) (Jdx 1) z with hF_def
    have hEqOn : Set.EqOn (DeTurckCoefficients.rawCompOnE (I := I) (M := M) g₀ RHSarm α Jdx) F
        (interior (extChartAt I α).target) := by
      intro z hz
      have hz_src : (extChartAt I α).symm z ∈
          DifferentialGeometry.Integral.Connection.chartLeviCivitaGoodSet (I := I) α := by
        rw [DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartLeviCivitaGoodSet_eq_extChartAt_source
          (I := I) α]
        exact (extChartAt I α).map_target (interior_subset hz)
      have hzt : z ∈ (extChartAt I α).target := interior_subset hz
      have hid := tensorChartComponentRaw_deTurckRHSArm_eq_chartDeTurckRicciRHS_diff
        (I := I) (M := M) g₀ g_bg T T' hδ_lt hδ hδ'_lt hδ' α hz_src Jdx
      rw [DeTurckCoefficients.rawCompOnE, hF_def]
      rw [← hg₁_def, ← hg₂_def] at hid
      rw [show (extChartAt I α) ((extChartAt I α).symm z) = z from (extChartAt I α).right_inv hzt]
        at hid
      rw [hRHSarm_def]
      exact hid
    -- Transfer the order-`m` within-jet through the EqOn, then to the seminorm and Nemytskii.
    have hcongr := iteratedFDerivWithin_congr (𝕜 := ℝ) hEqOn hyb_int m
    have hStage3 : ‖iteratedFDerivWithin ℝ m
        (DeTurckCoefficients.rawCompOnE (I := I) (M := M) g₀ RHSarm α Jdx)
        (interior (extChartAt I α).target) yb‖ ≤
        CNemMax * DeTurckCoefficients.bareChartJetContentOnE (I := I) (M := M) g₀ (T - T') α
          (a + 2) yb := by
      rw [hcongr]
      have hsemi : ‖iteratedFDerivWithin ℝ m F (interior (extChartAt I α).target) yb‖ ≤
          DeTurckCoefficients.iteratedFDerivSeminorm a F (interior (extChartAt I α).target) yb :=
        DeTurckCoefficients.norm_iteratedFDerivWithin_le_seminorm hmA F _ yb
      refine hsemi.trans ?_
      have hnem := hCNem (Jdx 0, Jdx 1) yb hyb_Kc
      refine hnem.trans ?_
      refine mul_le_mul_of_nonneg_right ?_
        (DeTurckCoefficients.bareChartJetContentOnE_nonneg (I := I) (M := M) g₀ (T - T') α (a + 2) yb)
      exact Finset.le_sup' CNem (Finset.mem_univ _)
    -- Stage-4: convert the `g₀`-anchored `E`-content of `T − T'` to `√rfns`.
    have hOnE_le : DeTurckCoefficients.bareChartJetContentOnE (I := I) (M := M) g₀ (T - T') α
        (a + 2) yb ≤ Cstage * Sdiff := by
      rw [hSdiff_def]
      simpa only [hyb_def] using hstage4
    calc ‖iteratedFDeriv ℝ m (rawPullR (I := I) (M := M) g₀ 0 2 RHSarm α
            (![] : Fin 0 → Fin n) Jdx) yE‖
        ≤ eNorm ^ m * ‖iteratedFDerivWithin ℝ m
            (DeTurckCoefficients.rawCompOnE (I := I) (M := M) g₀ RHSarm α Jdx)
            (interior (extChartAt I α).target) yb‖ := hbridge
      _ ≤ eFac * (CNemMax * Cstage * Sdiff) := by
          refine mul_le_mul (Finset.le_sup' (fun m => eNorm ^ m) hm) ?_ (norm_nonneg _) heFac_nn
          refine hStage3.trans ?_
          rw [mul_assoc]
          exact mul_le_mul_of_nonneg_left hOnE_le hCNemMax_nn
      _ = eFac * (CNemMax * Cstage) * Sdiff := by ring
  -- Assemble the bare-content double sum: `n²·(a+1)` terms each `≤ eFac·(CNemMax·Cstage)·Sdiff`.
  rw [bareChartJetContent]
  have hCard2 : (Fintype.card ((Fin 0 → Fin n) × (Fin 2 → Fin n)) : ℝ) = (n : ℝ) ^ 2 := by
    simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, pow_zero, one_mul]
    push_cast; ring
  calc (∑ q' : (Fin 0 → Fin n) × (Fin 2 → Fin n),
          ∑ m ∈ Finset.range (a + 1),
            ‖iteratedFDeriv ℝ m (rawPullR (I := I) (M := M) g₀ 0 2 RHSarm α q'.1 q'.2) yE‖)
      ≤ ∑ _q' : (Fin 0 → Fin n) × (Fin 2 → Fin n),
          ((((a : ℝ) + 1) * (eFac * (CNemMax * Cstage))) * Sdiff) := by
        refine Finset.sum_le_sum (fun q' _ => ?_)
        -- The `(Fin 0 → Fin n)` factor is the unique `![]`; bound each of the `a+1` orders.
        have hq1 : q'.1 = (![] : Fin 0 → Fin n) := Subsingleton.elim _ _
        calc (∑ m ∈ Finset.range (a + 1),
                ‖iteratedFDeriv ℝ m (rawPullR (I := I) (M := M) g₀ 0 2 RHSarm α q'.1 q'.2) yE‖)
            ≤ ∑ _m ∈ Finset.range (a + 1), (eFac * (CNemMax * Cstage) * Sdiff) := by
              refine Finset.sum_le_sum (fun m hm => ?_)
              rw [hq1]
              exact hper q'.2 m hm
          _ = (((a : ℝ) + 1) * (eFac * (CNemMax * Cstage))) * Sdiff := by
              rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
              push_cast; ring
    _ = (Fintype.card ((Fin 0 → Fin n) × (Fin 2 → Fin n)) : ℝ) *
          ((((a : ℝ) + 1) * (eFac * (CNemMax * Cstage))) * Sdiff) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ = ((n : ℝ) ^ 2) * (((a : ℝ) + 1) * (eFac * (CNemMax * Cstage))) * Sdiff := by
        rw [hCard2]; ring

/-- **The chart→intrinsic covariant Faà-di-Bruno / Leibniz raw-component domination of the
Ricci–DeTurck RHS-arm difference, localised to one chart of the finite atlas.**

This is the per-chart raw-component core of the RHS-arm globalization (the two-metric, `g₀ ≠ g_bg`
analog of the single-metric `DeTurckRHSReanchor`-style domination).

For the **RHS-arm residual**
```
RHSarm := (deTurckSmoothRemainder g₀ g_bg T − deTurckSmoothRemainder g₀ g_bg T')
            + rawTensorConnLapSmooth g₀ 0 2 (T − T')
```
— which by `deTurckSmoothRemainder`'s definition and `rawTensorConnLapSmooth_sub` value-equals the
genuine Ricci–DeTurck RHS difference `deTurckRHSSection g_bg (g₀ + T) − deTurckRHSSection g_bg (g₀ + T')`
(the connection-Laplacian Δ-arms cancel) — a fixed chart base point `α` of the chart atlas and a
covariant order `a`, there is a single constant `Λ ≥ 0` such that, on the closed support of the
chart-atlas partition-of-unity weight at `α`, the sum of squares of the raw chart-`α`-frame components
of the order-`a` covariant gradient `∇^a RHSarm` is dominated by `Λ²` times the order-`≤ a + 2`
covariant fibre-norm jets of the perturbation difference `T − T'`:
```
∑_{Idx,Jdx} (tensorChartComponentRaw g₀ 0 (2+a) (∇^a RHSarm) α Idx Jdx b)²
  ≤ Λ² · ∑_{q ≤ a+2} rfns(∇^q (T − T'))(b) .
```

**The proof (a stacking of the committed chart-jet spine).**  The order-`0` raw chart component of
`∇^a RHSarm` at `b` is the order-`0` Fréchet jet of its `rawPullR` at the chart-image point; the
forward covariant chart-jet peel `iteratedFDeriv_rawPullR_iteratedCovGrad_le_bareChartJetContent`
bounds it by the bare chart-jet content `bareChartJetContent g₀ 0 2 RHSarm α a`.  That bare content is
in turn dominated (lemma `bareChartJetContent_deTurckRHSArm_le_sqrt_fiberNormSq_sum`) by
`∑_{q ≤ a+2} √rfns(∇^q (T − T'))(b)`: each chart Fréchet jet of `RHSarm` passes through the forward
Euclidean coordinate bridge to its `E`-coordinate `rawCompOnE` jet, which on the chart-target interior
equals the chart Ricci–DeTurck carrier difference
`chartDeTurckRicciRHS (g₀+T) g_bg − chartDeTurckRicciRHS (g₀+T') g_bg` (the Δ-arms cancel at the
`toSection` level via `deTurckRHSArm_toSection_eq`, and the raw component reads off the textbook chart
polynomial on the chart Levi–Civita good set — which under the boundaryless assumption equals the whole
chart source — via `tensorChartComponentRaw_deTurckRHSArm_eq_chartDeTurckRicciRHS_diff`); the
**two-metric Nemytskii bound** built from `hasChartJetLip_chartDeTurckRicciRHS (g₀+T) (g₀+T') g_bg`
(anchored at `g₀`, with `g_bg` the separate DeTurck background) and the `g₀`-anchored chart-Gram
realize-difference jet bound `chartGramJetDiffSeminormSum_realize_le_bareChartJetContentOnE` (its first
slot is the realization anchor — here `g₀`) controls that by `bareChartJetContentOnE g₀ (T − T')(a+2)`,
the second-order `+2` quasilinearity; finally `bareChartJetContentOnE_le_sqrt_fiberNormSq_sum`
(`g₀`-anchored, the reverse Euclidean coordinate bridge composed with the bare-content Stage-4 bound)
converts that to the intrinsic `g₀` covariant fibre-norm jets.  Squaring and Cauchy–Schwarz
`(∑ √xᵢ)² ≤ (a+3) · ∑ xᵢ`, then summing over the `n^{2+a}` component multi-indices, yield the constant
`Λ² = n^{2+a} · (a+3) · (C_peel · K)²`.

**Per-pair, not ball-uniform.**  The constant `Λ` is allowed to depend on `T, T'` through the
metric-path coefficient data; no ball-uniformity is required.

**Non-vacuity / order self-check.**  The grid reads `∇^{≤ a+2}(T − T')`; the genuine `∂²(T − T')`
Ricci principal symbol forces a top jet at `q = a + 2`, so a window-`a` weakening is rejected.  A
`Λ = 0` witness is rejected by a nonvanishing raw chart component for a non-flat, genuinely
second-order RHS difference. -/
private theorem deTurckRHSArmDiff_iteratedCovGrad_rawComponentSq_domination_on_pouTsupport
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (α : M) :
    ∃ Λ : ℝ, 0 ≤ Λ ∧
      ∀ b : M,
        b ∈ tsupport (fun x : M =>
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) →
        (∑ Idx : Fin 0 → Fin (Module.finrank ℝ E),
          ∑ Jdx : Fin (2 + a) → Fin (Module.finrank ℝ E),
            (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentRaw
              (I := I) (M := M) g₀ 0 (2 + a)
              (iteratedCovGrad (I := I) g₀ 0 2 a
                ((deTurckSmoothRemainder (I := I) g₀ g_bg T hδ_lt hδ -
                    deTurckSmoothRemainder (I := I) g₀ g_bg T' hδ'_lt hδ') +
                  rawTensorConnLapSmooth (I := I) g₀ 0 2 (T - T'))) α Idx Jdx b) ^ 2) ≤
          Λ ^ 2 * ∑ q ∈ Finset.range (a + 2 + 1),
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + q) b
              ((iteratedCovGrad (I := I) g₀ 0 2 q (T - T')).toSection b) := by
  classical
  set n : ℕ := Module.finrank ℝ E with hn_def
  set RHSarm : SmoothCcTensor g₀ 0 2 :=
    (deTurckSmoothRemainder (I := I) g₀ g_bg T hδ_lt hδ -
        deTurckSmoothRemainder (I := I) g₀ g_bg T' hδ'_lt hδ') +
      rawTensorConnLapSmooth (I := I) g₀ 0 2 (T - T') with hRHSarm_def
  -- Forward covariant chart-jet peel of `∇^a RHSarm` (order window `P = a`).
  obtain ⟨Cpeel, hCpeel_nn, hCpeel⟩ :=
    iteratedFDeriv_rawPullR_iteratedCovGrad_le_bareChartJetContent (I := I) (M := M) g₀ 0 2
      RHSarm α a
  -- The RHS-arm bare chart-jet content domination by the intrinsic fibre-norm jets.
  obtain ⟨K, hK_nn, hK⟩ :=
    bareChartJetContent_deTurckRHSArm_le_sqrt_fiberNormSq_sum (I := I) (M := M) g₀ g_bg a T T'
      hδ_lt hδ hδ'_lt hδ' α
  refine ⟨Real.sqrt (((n : ℝ) ^ (2 + a)) * ((a : ℝ) + 3)) * (Cpeel * K),
    by positivity, ?_⟩
  intro b hb
  set R : ℝ := ∑ q ∈ Finset.range (a + 2 + 1),
    riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + q) b
      ((iteratedCovGrad (I := I) g₀ 0 2 q (T - T')).toSection b) with hR_def
  have hR_nn : 0 ≤ R := Finset.sum_nonneg fun q _ =>
    riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + q) b _
  set Ssqrt : ℝ := ∑ q ∈ Finset.range (a + 2 + 1),
    Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + q) b
      ((iteratedCovGrad (I := I) g₀ 0 2 q (T - T')).toSection b)) with hSsqrt_def
  have hSsqrt_nn : 0 ≤ Ssqrt := Finset.sum_nonneg fun q _ => Real.sqrt_nonneg _
  -- Chart-`α` setup: `b` lies in the chart source, and the Euclidean kernel point round-trips to `b`.
  have hb_src : b ∈ (extChartAt I α).source := by
    rw [extChartAt_source]
    exact DifferentialGeometry.Integral.Measure.chartAtlasPOU_isSubordinate I M α hb
  set yb : EuclideanSpace ℝ (Fin n) := (toEuclidean (E := E)) (extChartAt I α b) with hyb_def
  have hy_kernel : yb ∈ DifferentialGeometry.Analysis.Sobolev.Chart.chartImagePOUTsupport
      (I := I) (M := M) α := ⟨extChartAt I α b, ⟨b, hb, rfl⟩, rfl⟩
  -- The forward peel applied to the bare RHS-arm content, then RHS-arm → `√rfns`.
  have hcontent : bareChartJetContent (I := I) (M := M) g₀ 0 2 RHSarm α a yb ≤ K * Ssqrt := by
    rw [hSsqrt_def]; exact hK hb
  -- Per index pair `(![] , Jdx)`: the raw chart component value is bounded by `Cpeel · K · Ssqrt`.
  have hperPair : ∀ Jdx : Fin (2 + a) → Fin n,
      |DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentRaw
          (I := I) (M := M) g₀ 0 (2 + a)
          (iteratedCovGrad (I := I) g₀ 0 2 a RHSarm) α (![] : Fin 0 → Fin n) Jdx b| ≤
        (Cpeel * K) * Ssqrt := by
    intro Jdx
    -- The chart component value at `b` is the order-`0` `rawPullR` jet at the kernel point.
    have hval : DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentRaw
          (I := I) (M := M) g₀ 0 (2 + a)
          (iteratedCovGrad (I := I) g₀ 0 2 a RHSarm) α (![] : Fin 0 → Fin n) Jdx b =
        rawPullR (I := I) (M := M) g₀ 0 (2 + a)
          (iteratedCovGrad (I := I) g₀ 0 2 a RHSarm) α (![] : Fin 0 → Fin n) Jdx yb := by
      rw [hyb_def]
      simp only [rawPullR, Function.comp_apply, ContinuousLinearEquiv.symm_apply_apply]
      rw [(extChartAt I α).left_inv hb_src]
    rw [hval]
    have hpeel := hCpeel a 0 (by omega) (![] : Fin 0 → Fin n) Jdx yb hy_kernel
    rw [Nat.zero_add] at hpeel
    have hzero : ‖iteratedFDeriv ℝ 0
        (rawPullR (I := I) (M := M) g₀ 0 (2 + a)
          (iteratedCovGrad (I := I) g₀ 0 2 a RHSarm) α (![] : Fin 0 → Fin n) Jdx) yb‖ =
        |rawPullR (I := I) (M := M) g₀ 0 (2 + a)
          (iteratedCovGrad (I := I) g₀ 0 2 a RHSarm) α (![] : Fin 0 → Fin n) Jdx yb| := by
      rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs]
    rw [hzero] at hpeel
    refine hpeel.trans ?_
    calc Cpeel * bareChartJetContent (I := I) (M := M) g₀ 0 2 RHSarm α a yb
        ≤ Cpeel * (K * Ssqrt) := mul_le_mul_of_nonneg_left hcontent hCpeel_nn
      _ = (Cpeel * K) * Ssqrt := by ring
  -- Square the per-pair bound and apply Cauchy–Schwarz `(∑ √xᵢ)² ≤ (a+3)·∑ xᵢ`.
  have hSsqrt_sq : Ssqrt ^ 2 ≤ ((a : ℝ) + 3) * R := by
    rw [hSsqrt_def, hR_def]
    have hcheb := sq_sum_le_card_mul_sum_sq (s := Finset.range (a + 2 + 1))
      (f := fun q => Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + q) b
        ((iteratedCovGrad (I := I) g₀ 0 2 q (T - T')).toSection b)))
    refine hcheb.trans (le_of_eq ?_)
    rw [Finset.card_range]
    congr 1
    · push_cast; ring
    · refine Finset.sum_congr rfl (fun q _ => ?_)
      exact Real.sq_sqrt (riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + q) b _)
  have hperPairSq : ∀ Jdx : Fin (2 + a) → Fin n,
      (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentRaw
          (I := I) (M := M) g₀ 0 (2 + a)
          (iteratedCovGrad (I := I) g₀ 0 2 a RHSarm) α (![] : Fin 0 → Fin n) Jdx b) ^ 2 ≤
        (Cpeel * K) ^ 2 * (((a : ℝ) + 3) * R) := by
    intro Jdx
    have h1 := hperPair Jdx
    have h2 : (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentRaw
          (I := I) (M := M) g₀ 0 (2 + a)
          (iteratedCovGrad (I := I) g₀ 0 2 a RHSarm) α (![] : Fin 0 → Fin n) Jdx b) ^ 2 ≤
        ((Cpeel * K) * Ssqrt) ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) h1 2
    refine h2.trans ?_
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_left hSsqrt_sq (by positivity)
  -- Assemble the double sum and identify the constant `Λ²`.
  have hΛsq : (Real.sqrt (((n : ℝ) ^ (2 + a)) * ((a : ℝ) + 3)) * (Cpeel * K)) ^ 2 =
      ((n : ℝ) ^ (2 + a)) * ((Cpeel * K) ^ 2 * ((a : ℝ) + 3)) := by
    rw [mul_pow, Real.sq_sqrt (by positivity)]; ring
  rw [hΛsq]
  calc (∑ Idx : Fin 0 → Fin n, ∑ Jdx : Fin (2 + a) → Fin n,
          (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentRaw
            (I := I) (M := M) g₀ 0 (2 + a)
            (iteratedCovGrad (I := I) g₀ 0 2 a RHSarm) α Idx Jdx b) ^ 2)
      ≤ ∑ _Idx : Fin 0 → Fin n, ∑ _Jdx : Fin (2 + a) → Fin n,
          ((Cpeel * K) ^ 2 * (((a : ℝ) + 3) * R)) := by
        refine Finset.sum_le_sum (fun Idx _ => Finset.sum_le_sum (fun Jdx _ => ?_))
        rw [Subsingleton.elim Idx (![] : Fin 0 → Fin n)]
        exact hperPairSq Jdx
    _ = (((n : ℝ) ^ (2 + a))) * ((Cpeel * K) ^ 2 * (((a : ℝ) + 3) * R)) := by
        rw [Finset.sum_const, Finset.sum_const, Finset.card_univ, Finset.card_univ, nsmul_eq_mul,
          nsmul_eq_mul, ← mul_assoc]
        have hcard : ((Fintype.card (Fin 0 → Fin n) : ℝ) * (Fintype.card (Fin (2 + a) → Fin n) : ℝ)) =
            (n : ℝ) ^ (2 + a) := by
          simp only [Fintype.card_fun, Fintype.card_fin, pow_zero]
          push_cast; ring
        rw [hcard]
    _ = ((n : ℝ) ^ (2 + a)) * ((Cpeel * K) ^ 2 * ((a : ℝ) + 3)) * R := by ring

/-- **(The chart→intrinsic per-pair order-`a` single-factor covariant-jet bound of the Ricci–DeTurck
RHS-arm of the sealed remainder difference — PROVED from the per-chart raw-component posit.)**

For the RHS-arm residual `RHSarm` (the genuine Ricci–DeTurck RHS difference, Δ-arms added back), there
is a single nonnegative **per-pair** constant `C` (uniform over `x`) with
```
rfns(∇^a RHSarm)(x) ≤ C · ∑_{q ≤ a+2} rfns(∇^q (T − T'))(x).
```

It is **proved** (no `sorry` of its own) from the per-chart raw-component posit
`deTurckRHSArmDiff_iteratedCovGrad_rawComponentSq_domination_on_pouTsupport` via the reverse
fibre-norm/raw-component bridge `riemannianFiberNormSq_le_raw_components_on_pouTsupport` and a maximum
over the finite chart atlas `chartAtlasPOU_finset` (every base point lies in the closed POU support of
some atlas chart).  This is the two-metric analog of the sibling
`DeTurckCoefficients.deTurckRHSSection_iteratedCovGrad_pointwise_leibniz_domination`.  Consumers
transitively depend on the posit's `sorryAx`. -/
private theorem deTurckRHSArmDiff_iteratedCovGrad_singleFactor_jet
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ') :
    ∃ C : ℝ,
      0 ≤ C ∧
      ∀ x : M,
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + a) x
            ((iteratedCovGrad (I := I) g₀ 0 2 a
              ((deTurckSmoothRemainder (I := I) g₀ g_bg T hδ_lt hδ -
                  deTurckSmoothRemainder (I := I) g₀ g_bg T' hδ'_lt hδ') +
                rawTensorConnLapSmooth (I := I) g₀ 0 2 (T - T'))).toSection x) ≤
          C * ∑ q ∈ Finset.range (a + 2 + 1),
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + q) x
              ((iteratedCovGrad (I := I) g₀ 0 2 q (T - T')).toSection x) := by
  classical
  set RHSarm : SmoothCcTensor g₀ 0 2 :=
    (deTurckSmoothRemainder (I := I) g₀ g_bg T hδ_lt hδ -
        deTurckSmoothRemainder (I := I) g₀ g_bg T' hδ'_lt hδ') +
      rawTensorConnLapSmooth (I := I) g₀ 0 2 (T - T') with hRHSarm_def
  set RHSa : SmoothCcTensor g₀ 0 (2 + a) :=
    iteratedCovGrad (I := I) g₀ 0 2 a RHSarm with hRHSa_def
  set R : M → ℝ := fun b => ∑ q ∈ Finset.range (a + 2 + 1),
    riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + q) b
      ((iteratedCovGrad (I := I) g₀ 0 2 q (T - T')).toSection b) with hR_def
  have hR_nn : ∀ b : M, 0 ≤ R b := by
    intro b
    exact Finset.sum_nonneg fun q _ =>
      riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + q) b _
  -- Per chart `α` of the finite atlas: the reverse fibre-norm bridge composed with the posited
  -- per-chart raw-component domination produces a single constant `Kα` with
  -- `rfns(∇^a RHSarm)(b) ≤ Kα · R b` on the closed POU support of `α`.
  have hperChart : ∀ α : M, ∃ Kα : ℝ, 0 ≤ Kα ∧
      ∀ {b : M},
        b ∈ tsupport (fun x : M =>
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) →
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + a) b (RHSa.toSection b) ≤
          Kα * R b := by
    intro α
    obtain ⟨C, hC_nn, hC⟩ :=
      riemannianFiberNormSq_le_raw_components_on_pouTsupport
        (I := I) (M := M) g₀ 0 (2 + a) α
    obtain ⟨Λ, hΛ_nn, hΛ⟩ :=
      deTurckRHSArmDiff_iteratedCovGrad_rawComponentSq_domination_on_pouTsupport
        (I := I) (M := M) g₀ g_bg a T T' hδ_lt hδ hδ'_lt hδ' α
    refine ⟨C * Λ ^ 2, mul_nonneg hC_nn (sq_nonneg _), ?_⟩
    intro b hb
    have h1 := hC RHSa hb
    have h2 := hΛ b hb
    calc riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + a) b (RHSa.toSection b)
        ≤ C * (∑ Idx : Fin 0 → Fin (Module.finrank ℝ E),
              ∑ Jdx : Fin (2 + a) → Fin (Module.finrank ℝ E),
                (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentRaw
                  (I := I) (M := M) g₀ 0 (2 + a) RHSa α Idx Jdx b) ^ 2) := h1
      _ ≤ C * (Λ ^ 2 * R b) := by
          refine mul_le_mul_of_nonneg_left ?_ hC_nn
          simpa only [hRHSa_def, hRHSarm_def, hR_def] using h2
      _ = (C * Λ ^ 2) * R b := by ring
  -- Glue over the finite chart atlas: the maximum of the per-chart constants is a single global
  -- constant; each base point lies in the closed POU support of some atlas chart.
  choose! Kα hKα_nn hKα using hperChart
  set Ksum : ℝ := ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M), Kα α with hKsum_def
  have hKsum_nn : 0 ≤ Ksum := Finset.sum_nonneg (fun α _ => hKα_nn α)
  refine ⟨Ksum, hKsum_nn, ?_⟩
  intro x
  obtain ⟨α, hα_pos⟩ := (chartAtlasPOU I M).exists_pos_of_mem (Set.mem_univ x)
  have hα_finset : α ∈ chartAtlasPOU_finset (I := I) (M := M) := by
    rw [chartAtlasPOU_finset_mem]
    exact ⟨x, Function.mem_support.mpr (ne_of_gt hα_pos)⟩
  have hx_tsupport : x ∈ tsupport (fun y : M =>
      ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) y) :=
    subset_tsupport _ (Function.mem_support.mpr (ne_of_gt hα_pos))
  have hKα_le : Kα α ≤ Ksum := by
    rw [hKsum_def]
    exact Finset.single_le_sum (fun β _ => hKα_nn β) hα_finset
  calc riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + a) x (RHSa.toSection x)
      ≤ Kα α * R x := hKα α hx_tsupport
    _ ≤ Ksum * R x := mul_le_mul_of_nonneg_right hKα_le (hR_nn x)

/-- **(The genuine chart→intrinsic parallel-bilinear covariant-Leibniz diagonal grid of the
Ricci–DeTurck right-hand-side arm of the sealed remainder difference — PROVED from the per-chart
raw-component posit + the positive intrinsic coefficient floor.)**

For any two `g₀`-fibre-small smooth perturbations `T, T'`, there are a realized coefficient rank `s`, an
intrinsic coefficient field `coeff : SmoothCcTensor g₀ 0 s`, and a single nonnegative **per-pair** grid
constant `Cmid` (depending on the metric path, hence on `T, T'`, but uniform over `x`), such that for
the **RHS-arm residual**
```
RHSarm := (deTurckSmoothRemainder g₀ g_bg T − deTurckSmoothRemainder g₀ g_bg T')
            + rawTensorConnLapSmooth g₀ 0 2 (T − T')
```
— i.e. the sealed remainder difference with the linear connection-Laplacian (Δ-)arm added back, which
by `deTurckSmoothRemainder`'s definition `deTurckRHSSection g_bg (g₀ + ·) − Δ_∇ (·)` and the linearity
`rawTensorConnLapSmooth_sub` equals the genuine Ricci–DeTurck RHS difference
`deTurckRHSSection g_bg (g₀ + T) − deTurckRHSSection g_bg (g₀ + T')` — the order-`a` covariant gradient
is dominated, at the squared fibre-norm level, by the **single-coefficient diagonal covariant-Leibniz
product grid**
```
rfns(∇^a RHSarm)(x)
  ≤ Cmid · ∑_{q ≤ a+2} rfns(∇^q (T − T'))(x) · ∑_{l ≤ a+2−q} rfns(∇^l coeff)(x).
```

It is **proved** (no `sorry` of its own) by combining two ingredients:
* the single-factor covariant-jet bound `deTurckRHSArmDiff_iteratedCovGrad_singleFactor_jet`
  (`rfns(∇^a RHSarm)(x) ≤ C · ∑_{q ≤ a+2} rfns(∇^q (T − T'))(x)`, itself assembled from the
  per-chart raw-component posit
  `deTurckRHSArmDiff_iteratedCovGrad_rawComponentSq_domination_on_pouTsupport` via the reverse
  fibre-norm/raw-component bridge and an atlas maximum), and
* the positive intrinsic coefficient column `exists_positiveFloor_intrinsicCoeff` (the metric tensor
  `coeff := metricSmoothCcTensor g₀`, `s = 2`, with `1 ≤ rfns(coeff)(x)` everywhere — **proved**).

Taking `Cmid := C`, each single-factor term `C · rfns(∇^q (T − T'))(x)` (window `q ≤ a + 2`) is lifted
to the diagonal term `C · rfns(∇^q (T − T'))(x) · ∑_{l ≤ a+2−q} rfns(∇^l coeff)(x)` by the positive
coefficient floor `1 ≤ ∑_{l ≤ a+2−q} rfns(∇^l coeff)(x)` (always contains the `l = 0` term
`rfns(coeff)(x) ≥ 1` since `q ≤ a + 2` makes the window nonempty).  Consumers transitively depend on the
per-chart raw-component posit's `sorryAx`.

**Per-pair, not ball-uniform.**  The constant `Cmid` lives inside the per-pair statement (it is allowed
to depend on `T, T'` through the metric-path coefficient data), so no ball-uniformity is required.

**Non-vacuity / order self-check.**  The grid reads `∇^{≤ a+2}(T − T')`; the genuine `∂²(T − T')` Ricci
principal symbol forces a top jet at `q = a + 2`, so a window-`a` weakening is rejected.  A `Cmid = 0`
witness is rejected by a nonvanishing `∇^a RHSarm` for a non-flat, genuinely-second-order RHS
difference. -/
private theorem deTurckRHSArmDiff_iteratedCovGrad_parallelBilinearGrid_jet
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ') :
    ∃ (s : ℕ) (coeff : SmoothCcTensor g₀ 0 s) (Cmid : ℝ),
      0 ≤ Cmid ∧
      ∀ x : M,
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + a) x
            ((iteratedCovGrad (I := I) g₀ 0 2 a
              ((deTurckSmoothRemainder (I := I) g₀ g_bg T hδ_lt hδ -
                  deTurckSmoothRemainder (I := I) g₀ g_bg T' hδ'_lt hδ') +
                rawTensorConnLapSmooth (I := I) g₀ 0 2 (T - T'))).toSection x) ≤
          Cmid * ∑ q ∈ Finset.range (a + 2 + 1),
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + q) x
                ((iteratedCovGrad (I := I) g₀ 0 2 q (T - T')).toSection x)
              * ∑ l ∈ Finset.range (a + 2 + 1 - q),
                  riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + l) x
                    ((iteratedCovGrad (I := I) g₀ 0 s l coeff).toSection x) := by
  classical
  -- The positive intrinsic coefficient column (`1 ≤ rfns(coeff)` everywhere): the metric tensor.
  obtain ⟨s, coeff, hcoeff_floor⟩ := exists_positiveFloor_intrinsicCoeff (I := I) (M := M) g₀
  -- The single-factor covariant-jet bound of the RHS-arm at this `(T, T')`.
  obtain ⟨C, hC_nn, hsingle⟩ :=
    deTurckRHSArmDiff_iteratedCovGrad_singleFactor_jet (I := I) (M := M) g₀ g_bg a
      T T' hδ_lt hδ hδ'_lt hδ'
  refine ⟨s, coeff, C, hC_nn, fun x => ?_⟩
  refine (hsingle x).trans ?_
  -- Abbreviate the difference-jet column entries (window `q ≤ a + 2`).
  set Wq : ℕ → ℝ := fun q =>
    riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + q) x
      ((iteratedCovGrad (I := I) g₀ 0 2 q (T - T')).toSection x) with hWq_def
  have hWq_nn : ∀ q, 0 ≤ Wq q := fun q =>
    riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + q) x _
  -- The coefficient column at gradient order `q`: `∑_{l ≤ a+2−q} rfns(∇^l coeff)(x)`, with `1 ≤` floor.
  set Ccol : ℕ → ℝ := fun q =>
    ∑ l ∈ Finset.range (a + 2 + 1 - q),
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + l) x
        ((iteratedCovGrad (I := I) g₀ 0 s l coeff).toSection x) with hCcol_def
  have hCcol_floor : ∀ q, q ≤ a + 2 → (1 : ℝ) ≤ Ccol q := by
    intro q hq
    rw [hCcol_def]
    have hmem : 0 ∈ Finset.range (a + 2 + 1 - q) := by
      rw [Finset.mem_range]; omega
    have hl0 : (1 : ℝ) ≤
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + 0) x
          ((iteratedCovGrad (I := I) g₀ 0 s 0 coeff).toSection x) :=
      hcoeff_floor x
    refine le_trans hl0 ?_
    exact Finset.single_le_sum
      (f := fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + l) x
        ((iteratedCovGrad (I := I) g₀ 0 s l coeff).toSection x))
      (fun l _ => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (s + l) x _) hmem
  -- Each single-factor term `C · Wq q` (window `q ≤ a + 2`) is dominated by the diagonal term
  -- `C · Wq q · Ccol q` via the floor `1 ≤ Ccol q`.
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun q hq => ?_)) hC_nn
  have hq' : q ≤ a + 2 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hq)
  calc Wq q = Wq q * 1 := (mul_one _).symm
    _ ≤ Wq q * Ccol q := mul_le_mul_of_nonneg_left (hCcol_floor q hq') (hWq_nn q)

/-- **(The genuine chart→intrinsic per-pair order-`a` covariant-jet bound of the Ricci–DeTurck
right-hand-side arm of the sealed remainder difference — PROVED from the parallel-bilinear diagonal-grid
posit by supremising the realized coefficient column.)**

For any two `g₀`-fibre-small smooth perturbations `T, T'`, the order-`a` covariant gradient of the
**RHS-arm residual**
```
RHSarm := (deTurckSmoothRemainder g₀ g_bg T − deTurckSmoothRemainder g₀ g_bg T')
            + rawTensorConnLapSmooth g₀ 0 2 (T − T')
```
— the genuine Ricci–DeTurck RHS difference `deTurckRHSSection g_bg (g₀ + T) − deTurckRHSSection g_bg
(g₀ + T')` (the Δ-arms cancel by `rawTensorConnLapSmooth_sub`) — is dominated, at the squared fibre-norm
level, by a single nonnegative **per-pair** constant `C` (uniform over `x`) times the **order-`(a + 2)`
covariant jet** of `T − T'`:
```
rfns(∇^a RHSarm)(x) ≤ C · ∑_{q ≤ a+2} rfns(∇^q (T − T'))(x).
```

It is **proved** (no `sorry` of its own) from the parallel-bilinear covariant-Leibniz diagonal-grid posit
`deTurckRHSArmDiff_iteratedCovGrad_parallelBilinearGrid_jet`.  That posit supplies the realized intrinsic
coefficient field `coeff : SmoothCcTensor g₀ 0 s` and the diagonal product grid
`rfns(∇^a RHSarm)(x) ≤ Cmid · ∑_{q ≤ a+2} rfns(∇^q (T − T'))(x) · ∑_{l ≤ a+2−q} rfns(∇^l coeff)(x)`.  The
coefficient column `∑_{l ≤ a+2−q} rfns(∇^l coeff)(x)` is bounded, **uniformly in `x`**, by the finite
per-pair number `Kcol := ∑_{l ≤ a+2} (sup_x rfns(∇^l coeff))`, each summand finite on the compact
manifold by `exists_bound_riemannianFiberNormSq_smoothCcTensor` applied to the smooth covariant jet
`iteratedCovGrad g₀ 0 s l coeff`; collapsing the column into `Kcol` and setting `C := Cmid · Kcol` gives
the single-sum order-`(a + 2)` jet bound.  Consumers transitively depend on the posit's `sorryAx`.

**Non-vacuity / order self-check.**  The bound reads `∇^{≤ a+2}(T − T')`; the genuine `∂²(T − T')` Ricci
principal symbol forces a top jet at `q = a + 2`, so a window-`a` weakening is rejected.  A `C = 0`
witness is rejected by a nonvanishing `∇^a RHSarm` for a non-flat, genuinely-second-order RHS
difference. -/
private theorem deTurckRHSArmDiff_iteratedCovGrad_riemannianFiberNormSq_jet_le
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ') :
    ∃ C : ℝ,
      0 ≤ C ∧
      ∀ x : M,
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + a) x
            ((iteratedCovGrad (I := I) g₀ 0 2 a
              ((deTurckSmoothRemainder (I := I) g₀ g_bg T hδ_lt hδ -
                  deTurckSmoothRemainder (I := I) g₀ g_bg T' hδ'_lt hδ') +
                rawTensorConnLapSmooth (I := I) g₀ 0 2 (T - T'))).toSection x) ≤
          C * ∑ q ∈ Finset.range (a + 2 + 1),
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + q) x
              ((iteratedCovGrad (I := I) g₀ 0 2 q (T - T')).toSection x) := by
  classical
  -- The genuine chart→intrinsic parallel-bilinear diagonal-grid posit at this `(T, T')`.
  obtain ⟨s, coeff, Cmid, hCmid_nn, hgrid⟩ :=
    deTurckRHSArmDiff_iteratedCovGrad_parallelBilinearGrid_jet (I := I) (M := M) g₀ g_bg a
      T T' hδ_lt hδ hδ'_lt hδ'
  -- The uniform per-pair coefficient-column bound `Kl l := sup_x rfns(∇^l coeff)(x)`, finite on `M`.
  set Kl : ℕ → ℝ := fun l =>
    (exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ 0 (s + l)
      (iteratedCovGrad (I := I) g₀ 0 s l coeff)).choose with hKl_def
  have hKl_nn : ∀ l, 0 ≤ Kl l := fun l =>
    (exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ 0 (s + l)
      (iteratedCovGrad (I := I) g₀ 0 s l coeff)).choose_spec.1
  have hKl_bound : ∀ (l : ℕ) (x : M),
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + l) x
          ((iteratedCovGrad (I := I) g₀ 0 s l coeff).toSection x) ≤ Kl l := fun l =>
    (exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ 0 (s + l)
      (iteratedCovGrad (I := I) g₀ 0 s l coeff)).choose_spec.2
  -- The full coefficient-column cap: every truncated column `∑_{l < a+2+1−q}` is `≤ Kcol`.
  set Kcol : ℝ := ∑ l ∈ Finset.range (a + 2 + 1), Kl l with hKcol_def
  have hKcol_nn : 0 ≤ Kcol := Finset.sum_nonneg fun l _ => hKl_nn l
  have hcol_le : ∀ (q : ℕ) (x : M),
      ∑ l ∈ Finset.range (a + 2 + 1 - q),
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + l) x
          ((iteratedCovGrad (I := I) g₀ 0 s l coeff).toSection x) ≤ Kcol := by
    intro q x
    rw [hKcol_def]
    refine le_trans (Finset.sum_le_sum (fun l _ => hKl_bound l x)) ?_
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun l _ _ => hKl_nn l)
    intro l hl; rw [Finset.mem_range] at hl ⊢; omega
  refine ⟨Cmid * Kcol, by positivity, fun x => ?_⟩
  refine (hgrid x).trans ?_
  -- Abbreviate the difference-jet column entries (window `q ≤ a + 2`), all nonnegative.
  set Wq : ℕ → ℝ := fun q =>
    riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + q) x
      ((iteratedCovGrad (I := I) g₀ 0 2 q (T - T')).toSection x) with hWq_def
  have hWq_nn : ∀ q, 0 ≤ Wq q := fun q =>
    riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + q) x _
  set Ccol : ℕ → ℝ := fun q =>
    ∑ l ∈ Finset.range (a + 2 + 1 - q),
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + l) x
        ((iteratedCovGrad (I := I) g₀ 0 s l coeff).toSection x) with hCcol_def
  have hCcol_nn : ∀ q, 0 ≤ Ccol q := fun q =>
    Finset.sum_nonneg fun l _ => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (s + l) x _
  -- Cap each diagonal term `Wq q · Ccol q ≤ Wq q · Kcol` and pull `Kcol` out of the sum.
  calc Cmid * ∑ q ∈ Finset.range (a + 2 + 1), Wq q * Ccol q
      ≤ Cmid * ∑ q ∈ Finset.range (a + 2 + 1), Wq q * Kcol := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun q _ => ?_)) hCmid_nn
        exact mul_le_mul_of_nonneg_left (hcol_le q x) (hWq_nn q)
    _ = Cmid * Kcol * ∑ q ∈ Finset.range (a + 2 + 1), Wq q := by
        rw [← Finset.sum_mul]; ring

/-- **(The ball-uniform order-`(a+2)`-window covariant-jet bound on the Ricci–DeTurck RHS arm of
the sealed remainder difference — the uniform-over-`R`-ball Nemytskii estimate.)**

This is the **single named honest leaf** carrying the uniform-over-`R`-ball Lipschitz constant of the
two-metric chart Nemytskii nonlinearity at the quasilinear order.  Fix `g₀`, the DeTurck background
`g_bg`, an order `a`, and a covariant-`L²` ball radius `R ≥ 0`.  There is **one** nonnegative constant
`CR` — uniform over the fibre-small radius-`R` ball, i.e. **outside** the `∀ T T'` quantifier — such
that for any two `g₀`-fibre-small smooth perturbations `T, T'` whose covariant-`L²` jets up to order
`a + 2` lie in the radius-`R` ball, the order-`a` covariant gradient of the **RHS-arm residual**
```
RHSarm := (deTurckSmoothRemainder g₀ g_bg T − deTurckSmoothRemainder g₀ g_bg T')
            + rawTensorConnLapSmooth g₀ 0 2 (T − T')
```
— the genuine Ricci–DeTurck RHS difference `deTurckRHSSection g_bg (g₀ + T) − deTurckRHSSection g_bg
(g₀ + T')` (the Δ-arms cancel by `rawTensorConnLapSmooth_sub`) — is dominated, at the squared
fibre-norm level, by `CR` times the order-`(a + 2)` covariant jet of `T − T'`:
```
rfns(∇^a RHSarm)(x) ≤ CR · ∑_{q ≤ a+2} rfns(∇^q (T − T'))(x).
```

It is the per-pair bound `deTurckRHSArmDiff_iteratedCovGrad_riemannianFiberNormSq_jet_le` with the grid
constant **hoisted to a single ball-uniform value**: the chart-Nemytskii Lipschitz constant of
`hasChartJetLip_chartDeTurckRicciRHS` (anchored at `g₀`, the metric path constrained to the realized
ball `g₀ + T`, `g₀ + T'` with `‖∇^j T‖, ‖∇^j T'‖ ≤ R`) is uniform over the realized fibre-small `R`-ball
(the chart-jet Lipschitz modulus is taken over the bounded realized-metric jet set, hence finite and
`(T, T')`-independent), and the realized coefficient column `Kcol` is the fixed metric-tensor sup, also
`(T, T')`-independent.  Threading both uniform constants through the per-chart raw-component domination
and the atlas maximum gives the single `CR := Cmid · Kcol`.

**Non-vacuity / order self-check.**  The bound reads `∇^{≤ a+2}(T − T')`; the genuine `∂²(T − T')`
Ricci principal symbol forces a top jet at `q = a + 2`, so a window-`a` weakening is rejected.  A
`CR = 0` witness is rejected by a nonvanishing `∇^a RHSarm` for a non-flat, genuinely second-order RHS
difference. -/
private theorem deTurckRHSArmDiff_iteratedCovGrad_riemannianFiberNormSq_jet_le_ballUniform
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ) {R : ℝ} (hR : 0 ≤ R) :
    ∃ CR : ℝ,
      0 ≤ CR ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_lt : δ < 1)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (hδ'_lt : δ' < 1)
        (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + a) x
              ((iteratedCovGrad (I := I) g₀ 0 2 a
                ((deTurckSmoothRemainder (I := I) g₀ g_bg T hδ_lt hδ -
                    deTurckSmoothRemainder (I := I) g₀ g_bg T' hδ'_lt hδ') +
                  rawTensorConnLapSmooth (I := I) g₀ 0 2 (T - T'))).toSection x) ≤
            CR * ∑ q ∈ Finset.range (a + 2 + 1),
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + q) x
                ((iteratedCovGrad (I := I) g₀ 0 2 q (T - T')).toSection x) :=
  sorry

set_option linter.unusedVariables false in
/-- **(The genuine order-`(a+2)`-window single-factor covariant grid of the sealed
Ricci–DeTurck remainder difference — PROVED from the Δ-arm and RHS-arm covariant-jet posits.)**

This is the irreducible analytic content of the single-field diagonal grid, stripped of the auxiliary
coefficient column: for any two `g₀`-fibre-small smooth ball-radius-`R` perturbations `T, T'`, the
order-`a` covariant gradient of the sealed remainder difference
`D := deTurckSmoothRemainder g₀ g_bg T − deTurckSmoothRemainder g₀ g_bg T'` is dominated, at the squared
fibre-norm level, by a single nonnegative constant `C` times the **order-`(a + 2)` covariant jet** of the
perturbation difference `T − T'`:
```
rfns(∇^a D)(x) ≤ C · ∑_{q ≤ a+2} rfns(∇^q (T − T'))(x).
```

**The jet order is `a + 2`, not `a`** — this is the genuinely quasilinear content.  The remainder
difference `D` is genuinely *second order* in `T − T'`: its connection-Laplacian arm
`−rawTensorConnLapSmooth g₀ 0 2 (T − T')` reads `∇²(T − T')`
(`rawTensorConnLap_eq_frame_trace_secondCovDeriv`), so `∇^a D` reads `∇^{a+2}(T − T')`, and the read
window of the contracted-section jet sum is correspondingly `q ≤ a + 2`.  A window-`a` bound
(`q ≤ a`) is FALSE — it is the value-local order-`0` realization refuted by
`DiffBilinOp.exists_rfns_iteratedCovGrad_singleSum_le` (`rfns(∇^a (op 0 W)) ≤ C · ∑_{q ≤ a} rfns(∇^q W)`
forces order-`0` reading, which `D` violates by losing two derivatives).

**Assembly.**  The sealed remainder difference splits at the value level as
`D = RHSarm − rawTensorConnLapSmooth g₀ 0 2 (T − T')`, where
`RHSarm := D + rawTensorConnLapSmooth g₀ 0 2 (T − T')` is the genuine Ricci–DeTurck RHS difference
(by `deTurckSmoothRemainder`'s definition and the connection-Laplacian linearity
`rawTensorConnLapSmooth_sub`).  The order-`a` covariant gradient distributes over this difference
(`iteratedCovGrad_sub`), and the `2`-sub-additivity of the intrinsic fibre norm
(`riemannianFiberNormSq_add_le`) splits `rfns(∇^a D)` into `2·rfns(∇^a RHSarm) + 2·rfns(∇^a Δarm)`.  The
RHS-arm term is the chart→intrinsic per-pair posit
`deTurckRHSArmDiff_iteratedCovGrad_riemannianFiberNormSq_jet_le`; the Δ-arm term is the rough-Laplacian
covariant-jet posit `rawTensorConnLapSmooth_iteratedCovGrad_riemannianFiberNormSq_jet_le` at `W := T − T'`
— both bounding `rfns(∇^a ·)` by `C · ∑_{q ≤ a+2} rfns(∇^q (T − T'))(x)`.  Adding the two scaled bounds
gives the claim with `C := 2·(C_RHS + C_Δ)`.  Consumers transitively depend on both posits' `sorryAx`.

**Non-vacuity / order self-check.**  The bound reads `∇^{≤ a+2}(T − T')`; the `q = a + 2` term is the
genuine top jet (carried by the Δ-arm), so a window-`a` weakening is rejected.  A `C = 0` witness is
rejected by a nonvanishing `∇^a D` (a genuinely second-order, non-flat remainder difference). -/
private theorem deTurckRemainderDiff_singleField_singleFactorGrid
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ) {R : ℝ} (hR : 0 ≤ R) :
    ∃ C : ℝ,
      0 ≤ C ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_lt : δ < 1)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (hδ'_lt : δ' < 1)
        (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        (∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + a) x
              ((iteratedCovGrad (I := I) g₀ 0 2 a
                (deTurckSmoothRemainder (I := I) g₀ g_bg T hδ_lt hδ -
                  deTurckSmoothRemainder (I := I) g₀ g_bg T' hδ'_lt hδ')).toSection x) ≤
            C * ∑ q ∈ Finset.range (a + 2 + 1),
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + q) x
                ((iteratedCovGrad (I := I) g₀ 0 2 q (T - T')).toSection x)) := by
  -- The Δ-arm covariant-jet posit at `W := T − T'` — its constant is already ball-uniform
  -- (`(T, T')`-independent: the `∀ W x` quantifier is inside the `∃ CΔ`).
  obtain ⟨CΔ, hCΔ_nn, hCΔ⟩ :=
    rawTensorConnLapSmooth_iteratedCovGrad_riemannianFiberNormSq_jet_le (I := I) (M := M) g₀ a
  -- The RHS-arm ball-uniform covariant-jet posit — its constant `CR` is hoisted outside `∀ T T'`.
  obtain ⟨CR, hCR_nn, hCR⟩ :=
    deTurckRHSArmDiff_iteratedCovGrad_riemannianFiberNormSq_jet_le_ballUniform
      (I := I) (M := M) g₀ g_bg a hR
  refine ⟨2 * (CR + CΔ), by positivity, ?_⟩
  intro T T' δ hδ_lt hδ δ' hδ'_lt hδ' hTball hT'ball x
  -- The sealed remainder difference and the two arms.
  set D : SmoothCcTensor g₀ 0 2 :=
    deTurckSmoothRemainder (I := I) g₀ g_bg T hδ_lt hδ -
      deTurckSmoothRemainder (I := I) g₀ g_bg T' hδ'_lt hδ' with hD_def
  set Δdiff : SmoothCcTensor g₀ 0 2 :=
    rawTensorConnLapSmooth (I := I) g₀ 0 2 (T - T') with hΔdiff_def
  set RHSarm : SmoothCcTensor g₀ 0 2 := D + Δdiff with hRHSarm_def
  -- Abbreviate the order-`(a+2)` jet column of `T − T'` at `x`.
  set Scol : ℝ := ∑ q ∈ Finset.range (a + 2 + 1),
    riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + q) x
      ((iteratedCovGrad (I := I) g₀ 0 2 q (T - T')).toSection x) with hScol_def
  have hScol_nn : 0 ≤ Scol :=
    Finset.sum_nonneg fun q _ => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + q) x _
  -- The value-level split `D = RHSarm + (−Δdiff)`, lifted to the order-`a` covariant gradient.
  have hDsplit : D = RHSarm + (-Δdiff) := by
    rw [hRHSarm_def, add_neg_cancel_right]
  have hgrad_split :
      iteratedCovGrad (I := I) g₀ 0 2 a D =
        iteratedCovGrad (I := I) g₀ 0 2 a RHSarm +
          iteratedCovGrad (I := I) g₀ 0 2 a (-Δdiff) := by
    rw [hDsplit, iteratedCovGrad_add]
  -- `2`-sub-additivity of the squared fibre norm on the split.
  have hsub :
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + a) x
          ((iteratedCovGrad (I := I) g₀ 0 2 a D).toSection x) ≤
        2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + a) x
              ((iteratedCovGrad (I := I) g₀ 0 2 a RHSarm).toSection x) +
          2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + a) x
              ((iteratedCovGrad (I := I) g₀ 0 2 a (-Δdiff)).toSection x) := by
    rw [hgrad_split]
    exact riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 0 (2 + a) x
      ((iteratedCovGrad (I := I) g₀ 0 2 a RHSarm).toSection x)
      ((iteratedCovGrad (I := I) g₀ 0 2 a (-Δdiff)).toSection x)
  -- The `−Δdiff` term reduces to the Δ-arm term by negation-invariance of `rfns`.
  have hneg_grad : iteratedCovGrad (I := I) g₀ 0 2 a (-Δdiff) =
      -iteratedCovGrad (I := I) g₀ 0 2 a Δdiff := iteratedCovGrad_neg (I := I) g₀ 0 2 a Δdiff
  have hneg_rfns :
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + a) x
          ((iteratedCovGrad (I := I) g₀ 0 2 a (-Δdiff)).toSection x) =
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + a) x
          ((iteratedCovGrad (I := I) g₀ 0 2 a Δdiff).toSection x) := by
    rw [hneg_grad]
    rw [show ((-iteratedCovGrad (I := I) g₀ 0 2 a Δdiff).toSection x) =
        -((iteratedCovGrad (I := I) g₀ 0 2 a Δdiff).toSection x) from rfl]
    exact riemannianFiberNormSq_neg_value (I := I) (M := M) g₀ 0 (2 + a) x _
  -- The Δ-arm bound at `W := T − T'` (`Δdiff = rawTensorConnLapSmooth g₀ 0 2 (T − T')`).
  have hΔbound :
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + a) x
          ((iteratedCovGrad (I := I) g₀ 0 2 a Δdiff).toSection x) ≤ CΔ * Scol := by
    rw [hScol_def]; exact hCΔ (T - T') x
  -- The RHS-arm bound (`RHSarm = D + Δdiff`).
  have hRbound :
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + a) x
          ((iteratedCovGrad (I := I) g₀ 0 2 a RHSarm).toSection x) ≤ CR * Scol := by
    rw [hScol_def, hRHSarm_def, hD_def, hΔdiff_def]
    exact hCR T T' hδ_lt hδ hδ'_lt hδ' hTball hT'ball x
  -- Assemble: `rfns(∇^a D) ≤ 2·(CR·Scol) + 2·(CΔ·Scol) = 2·(CR + CΔ)·Scol`.
  calc riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + a) x
          ((iteratedCovGrad (I := I) g₀ 0 2 a D).toSection x)
      ≤ 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + a) x
              ((iteratedCovGrad (I := I) g₀ 0 2 a RHSarm).toSection x) +
          2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + a) x
              ((iteratedCovGrad (I := I) g₀ 0 2 a (-Δdiff)).toSection x) := hsub
    _ = 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + a) x
              ((iteratedCovGrad (I := I) g₀ 0 2 a RHSarm).toSection x) +
          2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + a) x
              ((iteratedCovGrad (I := I) g₀ 0 2 a Δdiff).toSection x) := by rw [hneg_rfns]
    _ ≤ 2 * (CR * Scol) + 2 * (CΔ * Scol) := by
        refine add_le_add ?_ ?_
        · exact mul_le_mul_of_nonneg_left hRbound (by norm_num)
        · exact mul_le_mul_of_nonneg_left hΔbound (by norm_num)
    _ = 2 * (CR + CΔ) * Scol := by ring

/-- **The irreducible chart→intrinsic content of the single-field diagonal grid: the intrinsic
covariant Faà-di-Bruno coefficient + diagonal product grid of the sealed Ricci–DeTurck remainder
difference, WITHOUT the `C⁰` fibre-sup packaging.**

This is the genuine analytic prerequisite stripped to its irreducible core.  It delivers, for any two
`g₀`-fibre-small smooth ball-radius-`R` perturbations `T, T'`, a fixed intrinsic coefficient field
`coeff : SmoothCcTensor g₀ 0 s` and a middle grid constant `Cmid ≥ 0`, with the **single-coefficient
diagonal covariant-Leibniz product-grid domination** of the sealed remainder difference
`D := deTurckSmoothRemainder g₀ g_bg T − deTurckSmoothRemainder g₀ g_bg T'`:
```
rfns(∇^a D)(x) ≤ Cmid · ∑_{i ≤ a+2} rfns(∇^i (T − T'))(x) · ∑_{l ≤ a+2−i} rfns(∇^l coeff)(x).
```

It is **assembled** from two ingredients:
* the genuine order-`(a + 2)`-window single-factor covariant grid posit
  `deTurckRemainderDiff_singleField_singleFactorGrid`
  (`rfns(∇^a D)(x) ≤ C · ∑_{q ≤ a+2} rfns(∇^q (T − T'))(x)`, the irreducible quasilinear analytic
  content reading `∇^{≤ a+2}(T − T')` — **not** the value-local order-`0` form, which is refuted), and
* the positive intrinsic coefficient column `exists_positiveFloor_intrinsicCoeff` (the metric tensor
  `coeff := metricSmoothCcTensor g₀`, `s = 2`, with `1 ≤ rfns(coeff)(x)` everywhere — **proved**, no
  posit).

Taking `Cmid := C`, each single-factor term `C · rfns(∇^i (T − T'))(x)` (window `i ≤ a + 2`) is lifted
to the diagonal term `C · rfns(∇^i (T − T'))(x) · ∑_{l ≤ a+2−i} rfns(∇^l coeff)(x)` by the positive
coefficient floor `1 ≤ ∑_{l ≤ a+2−i} rfns(∇^l coeff)(x)` (which always contains the `l = 0` term
`rfns(coeff)(x) ≥ 1` since `i ≤ a + 2` makes the window nonempty).  The coefficient column is auxiliary
bookkeeping for the downstream Gagliardo–Nirenberg two-arm redistribution; the genuine analytic order
content lives entirely in the single-factor posit.

It is **finer** than `deTurckRemainderDiff_singleField_diagonalGrid`: that consumer's two `C⁰`
fibre-sup clauses (`√rfns(T − T') ≤ ΛW`, `√rfns(coeff) ≤ Λcoeff`) are NOT carried here — they are
mechanically recovered from this core by the uniform smooth-tensor fibre-norm bound
`exists_bound_riemannianFiberNormSq_smoothCcTensor` on the compact manifold.  Consumers transitively
depend on the single-factor grid posit's `sorryAx`.

**Non-vacuity.**  The grid bounds the genuine sealed remainder difference `D`, not a free choice; the
`l = 0` column carries `∑_i rfns(∇^i (T − T'))·rfns(coeff)`, so a `Cmid = 0` witness is rejected by a
nonvanishing remainder-difference jet (the metric coefficient floor `rfns(coeff) ≥ 1` is nonzero). -/
private theorem deTurckRemainderDiff_singleField_diagonalGrid_intrinsicCore
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ) {R : ℝ} (hR : 0 ≤ R) :
    ∃ (s : ℕ) (coeff : SmoothCcTensor g₀ 0 s) (Cmid : ℝ),
      0 ≤ Cmid ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_lt : δ < 1)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (hδ'_lt : δ' < 1)
        (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        (∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + a) x
              ((iteratedCovGrad (I := I) g₀ 0 2 a
                (deTurckSmoothRemainder (I := I) g₀ g_bg T hδ_lt hδ -
                  deTurckSmoothRemainder (I := I) g₀ g_bg T' hδ'_lt hδ')).toSection x) ≤
            Cmid * ∑ i ∈ Finset.range (a + 2 + 1),
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
                  ((iteratedCovGrad (I := I) g₀ 0 2 i (T - T')).toSection x)
                * ∑ l ∈ Finset.range (a + 2 + 1 - i),
                    riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + l) x
                      ((iteratedCovGrad (I := I) g₀ 0 s l coeff).toSection x)) := by
  classical
  -- The positive intrinsic coefficient column (`1 ≤ rfns(coeff)` everywhere): the metric tensor —
  -- `(T, T')`-independent, hence hoisted outside the perturbation quantifier.
  obtain ⟨s, coeff, hcoeff_floor⟩ := exists_positiveFloor_intrinsicCoeff (I := I) (M := M) g₀
  -- The ball-uniform single-factor covariant grid: its constant `Cmid` is now hoisted outside `∀ T T'`.
  obtain ⟨Cmid, hCmid_nn, hgrid⟩ :=
    deTurckRemainderDiff_singleField_singleFactorGrid (I := I) (M := M) g₀ g_bg a hR
  refine ⟨s, coeff, Cmid, hCmid_nn, ?_⟩
  intro T T' δ hδ_lt hδ δ' hδ'_lt hδ' hTball hT'ball x
  refine (hgrid T T' hδ_lt hδ hδ'_lt hδ' hTball hT'ball x).trans ?_
  -- Abbreviate the difference-jet column entries (window `q ≤ a + 2`).
  set Wq : ℕ → ℝ := fun q =>
    riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + q) x
      ((iteratedCovGrad (I := I) g₀ 0 2 q (T - T')).toSection x) with hWq_def
  have hWq_nn : ∀ q, 0 ≤ Wq q := fun q =>
    riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + q) x _
  -- The coefficient column at gradient order `i`: `∑_{l ≤ a+2−i} rfns(∇^l coeff)(x)`, with `1 ≤` floor.
  set Ccol : ℕ → ℝ := fun i =>
    ∑ l ∈ Finset.range (a + 2 + 1 - i),
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + l) x
        ((iteratedCovGrad (I := I) g₀ 0 s l coeff).toSection x) with hCcol_def
  have hCcol_floor : ∀ i, i ≤ a + 2 → (1 : ℝ) ≤ Ccol i := by
    intro i hi
    rw [hCcol_def]
    -- The window `range (a+2+1−i)` is nonempty (contains `l = 0` since `i ≤ a+2`); its `l = 0` term is
    -- `rfns(∇^0 coeff) = rfns(coeff) ≥ 1`; all other terms are nonnegative.
    have hmem : 0 ∈ Finset.range (a + 2 + 1 - i) := by
      rw [Finset.mem_range]; omega
    have hl0 : (1 : ℝ) ≤
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + 0) x
          ((iteratedCovGrad (I := I) g₀ 0 s 0 coeff).toSection x) :=
      hcoeff_floor x
    refine le_trans hl0 ?_
    exact Finset.single_le_sum
      (f := fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + l) x
        ((iteratedCovGrad (I := I) g₀ 0 s l coeff).toSection x))
      (fun l _ => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (s + l) x _) hmem
  -- Each single-factor term `Cmid · Wq i` (window `i ≤ a + 2`) is dominated by the diagonal term
  -- `Cmid · Wq i · Ccol i` via the floor `1 ≤ Ccol i`.
  have hsum_le :
      Cmid * ∑ q ∈ Finset.range (a + 2 + 1), Wq q ≤
        Cmid * ∑ i ∈ Finset.range (a + 2 + 1), Wq i * Ccol i := by
    refine mul_le_mul_of_nonneg_left ?_ hCmid_nn
    refine Finset.sum_le_sum (fun i hi => ?_)
    rw [Finset.mem_range] at hi
    have hi' : i ≤ a + 2 := by omega
    nlinarith [hWq_nn i, hCcol_floor i hi', mul_nonneg (hWq_nn i) (sub_nonneg.2 (hCcol_floor i hi'))]
  refine hsum_le.trans_eq ?_
  -- Re-expose the abbreviations.
  rw [hWq_def, hCcol_def]

set_option maxHeartbeats 1600000 in
attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
/-- **The sharp supercritical-Sobolev pointwise fibre-norm bound on a smooth tensor section.**

At a supercritical spectral order (`ha_super : 2·finrank E + 3 ≤ a`) there is a uniform constant
`C₀ ≥ 0` such that, for **every** smooth compactly-supported `(0,2)`-tensor `S` and **every** base
point `x`, the intrinsic squared Riemannian fibre norm of the section value is dominated by the
square of `C₀` times the order-`(a + 2)` spectral norm of `S`:

  `riemannianFiberNormSq g₀ 0 2 x (S.toSection x) ≤ (C₀ · ‖smoothCcToTensorHs g₀ (a+2) S‖)²`.

This is the section-level supercritical Sobolev embedding `H ↪ C⁰`, transported to the intrinsic
fibre norm.  Concretely the chart `H^{2·kE} ↪ C⁰` embedding `tensorPouSobolevHilbert_embedding_Ck_gNorm`
(at the smallest chart order `kE = finrank E / 2 + 1`, so `2·kE > finrank E`) bounds the bundle fibre
norm `‖S.toSection x‖` by `C₁ · ‖S.toHs (2·kE)‖`; the lossy-bridge spectral chain (the `toHs`/PoU
norm identity `tensorPouSobolevHilbert_norm_eq`, the PoU → spectral comparison
`tensorPouSobolevHsNorm_le_ccSpectralEmbed`, the spectral monotonicity `ccSpectralEmbed_norm_mono`
raising the order `4·kE ≤ a + 2`, and the `ccSpectralEmbed = smoothCcToTensorHs` definitional
equality) lifts it to `C₀ · ‖smoothCcToTensorHs g₀ (a+2) S‖`; finally the fibre-norm/bundle-norm
bridge `riemannianFiberNormSq_eq_bundle_norm_sq'` rewrites `rfns` as `‖S.toSection x‖²` and squaring
gives the bound.  This is the **sharp** witness that replaces the loose
`exists_bound_riemannianFiberNormSq_smoothCcTensor` upper bound on the perturbation-difference
`C⁰` sup, exposing the `‖smoothCcToTensorHs‖` scale of the sup so a downstream consumer can absorb
the cross arm. -/
private theorem exists_riemannianFiberNormSq_section_le_smoothCcToTensorHs_sq
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 3 ≤ a) :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ (S : SmoothCcTensor g₀ 0 2) (x : M),
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x (S.toSection x) ≤
        (C₀ * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) S‖) ^ 2 := by
  classical
  set kE : ℕ := Module.finrank ℝ E / 2 + 1 with hkE_def
  have hkE_super : 2 * kE > Module.finrank ℝ E + 2 * 0 := by rw [hkE_def]; omega
  have h4kE_le : (2 * (2 * kE) : ℕ) ≤ a + 2 := by rw [hkE_def]; omega
  -- chart `H^{2 kE} ↪ C⁰` (section-level supercritical Sobolev embedding)
  obtain ⟨C₁, hC₁_pos, hC₁⟩ :=
    DifferentialGeometry.PDE.RicciFlow.tensorPouSobolevHilbert_embedding_Ck_gNorm
      (I := I) (M := M) g₀ 0 2 kE 0 hkE_super
  -- PoU → spectral comparison (N1)
  obtain ⟨C₂, hC₂_nn, hC₂⟩ :=
    tensorPouSobolevHsNorm_le_ccSpectralEmbed (I := I) (M := M) g₀ (2 * kE)
  refine ⟨C₁ * (C₂ + 1), by positivity, fun S x => ?_⟩
  letI : Bundle.RiemannianBundle
      (fun b : M => Tensor0SBundle.TensorRSSpace 0 2 I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 2
  -- the spectral lift of the chart fibre-norm bound, mirroring the lossy bridge's `hupper`
  have hupper : C₁ * ‖DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev.SmoothCcTensor.toHs
        (g := g₀) (r := 0) (s := 2) (2 * kE) S‖ ≤
      (C₁ * (C₂ + 1)) * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) S‖ := by
    have hstep2 : ‖DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev.SmoothCcTensor.toHs
          (g := g₀) (r := 0) (s := 2) (2 * kE) S‖ =
        (DifferentialGeometry.Analysis.Sobolev.Tensor.tensorPouSobolevHsNorm
          (I := I) (M := M) g₀ (2 * kE) S).toReal :=
      DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev.tensorPouSobolevHilbert_norm_eq
        (I := I) (M := M) g₀ (2 * kE) S
    have hstep3 : (DifferentialGeometry.Analysis.Sobolev.Tensor.tensorPouSobolevHsNorm
          (I := I) (M := M) g₀ (2 * kE) S).toReal ≤
        C₂ * ‖ccSpectralEmbed (I := I) (M := M) g₀ ((2 * (2 * kE) : ℕ) : ℝ) S‖ := hC₂ S
    have hstep4 : ‖ccSpectralEmbed (I := I) (M := M) g₀ ((2 * (2 * kE) : ℕ) : ℝ) S‖ ≤
        ‖ccSpectralEmbed (I := I) (M := M) g₀ ((a : ℝ) + 2) S‖ := by
      refine ccSpectralEmbed_norm_mono (I := I) (M := M) g₀ ?_ S
      have h2 : ((2 * (2 * kE) : ℕ) : ℝ) ≤ ((a + 2 : ℕ) : ℝ) := by exact_mod_cast h4kE_le
      push_cast at h2 ⊢
      linarith [h2]
    have hembed_eq : ccSpectralEmbed (I := I) (M := M) g₀ ((a : ℝ) + 2) S =
        smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) S :=
      DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorHs.ext
        (funext (fun i => rfl))
    set Nm : ℝ := ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) S‖ with hNm_def
    have hNm_nn : 0 ≤ Nm := norm_nonneg _
    have hspec_le : ‖ccSpectralEmbed (I := I) (M := M) g₀ ((2 * (2 * kE) : ℕ) : ℝ) S‖ ≤ Nm := by
      rw [hNm_def, ← hembed_eq]; exact hstep4
    calc C₁ * ‖DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev.SmoothCcTensor.toHs
            (g := g₀) (r := 0) (s := 2) (2 * kE) S‖
        = C₁ * (DifferentialGeometry.Analysis.Sobolev.Tensor.tensorPouSobolevHsNorm
            (I := I) (M := M) g₀ (2 * kE) S).toReal := by rw [hstep2]
      _ ≤ C₁ * (C₂ * ‖ccSpectralEmbed (I := I) (M := M) g₀ ((2 * (2 * kE) : ℕ) : ℝ) S‖) :=
          mul_le_mul_of_nonneg_left hstep3 hC₁_pos.le
      _ ≤ C₁ * (C₂ * Nm) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hspec_le hC₂_nn) hC₁_pos.le
      _ ≤ (C₁ * (C₂ + 1)) * Nm := by nlinarith [hNm_nn, hC₁_pos.le, hC₂_nn]
  -- the section fibre-norm bound (instance inferred from `hC₁ S x`, never annotated), then
  -- rewrite `rfns = ‖·‖²` and square
  have hsection := le_trans (hC₁ S x) hupper
  rw [riemannianFiberNormSq_eq_bundle_norm_sq' (I := I) (M := M) g₀ 0 2 x (S.toSection x)]
  exact pow_le_pow_left₀ (norm_nonneg _) hsection 2

/-- **The intrinsic covariant Faà-di-Bruno single-coefficient diagonal product-grid domination of the
sealed Ricci–DeTurck remainder difference, with the two `C⁰` fibre-sup levels.**

Fix `g₀`, the DeTurck background `g_bg`, an order `a`, and a covariant-`L²` ball radius `R ≥ 0`.  For
any two `g₀`-fibre-small smooth perturbations `T, T'` whose covariant-`L²` jets up to order `a + 2`
lie in the radius-`R` ball, there are a single intrinsic coefficient field
`coeff : SmoothCcTensor g₀ 0 s`, a middle grid constant `Cmid ≥ 0`, and two `C⁰` fibre-sup levels
`ΛW, Λcoeff ≥ 0`, such that for the **sealed remainder difference**
`D := deTurckSmoothRemainder g₀ g_bg T − deTurckSmoothRemainder g₀ g_bg T'`:

* `√rfns(T − T') ≤ ΛW` everywhere (the `C⁰` sup of the perturbation difference),
* `√rfns(coeff) ≤ Λcoeff` everywhere (the `C⁰` sup of the coefficient data), and
* the **single-coefficient diagonal covariant-Leibniz product-grid domination**: for every `x`,
  ```
  rfns(∇^a D)(x)
    ≤ Cmid · ∑_{i ≤ a+2} rfns(∇^i (T − T'))(x) · ∑_{l ≤ a+2−i} rfns(∇^l coeff)(x).
  ```

It is **assembled** from the irreducible chart→intrinsic posit
`deTurckRemainderDiff_singleField_diagonalGrid_intrinsicCore` (which supplies the intrinsic coefficient
field `coeff` and the diagonal product grid): the two `C⁰` fibre-sup clauses are mechanically recovered
from that core by the uniform smooth-tensor fibre-norm bound
`exists_bound_riemannianFiberNormSq_smoothCcTensor` on the compact manifold (set `ΛW := √(sup rfns(T −
T'))`, `Λcoeff := √(sup rfns(coeff))`).  Consumers transitively depend on the core's `sorryAx`.

**Non-vacuity.**  The grid bounds the genuine sealed remainder difference `D`, not a free choice; the
`l = 0` column reads `∑_i rfns(∇^i (T − T'))·rfns(coeff)`, so a `Cmid = 0` witness is rejected by a
nonvanishing remainder-difference jet where `coeff` is nonzero. -/
private theorem deTurckRemainderDiff_singleField_diagonalGrid
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 3 ≤ a) {R : ℝ} (hR : 0 ≤ R) :
    ∃ (s : ℕ) (coeff : SmoothCcTensor g₀ 0 s) (Cmid Λcoeff Cw : ℝ),
      0 ≤ Cmid ∧ 0 ≤ Λcoeff ∧ 0 ≤ Cw ∧
      (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 s x (coeff.toSection x) ≤
        Λcoeff ^ 2) ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_lt : δ < 1)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (hδ'_lt : δ' < 1)
        (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ∃ ΛW : ℝ,
          0 ≤ ΛW ∧
          ΛW ≤ Cw * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) (T - T')‖ ∧
          (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x ((T - T').toSection x) ≤
            ΛW ^ 2) ∧
          (∀ x : M,
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + a) x
                ((iteratedCovGrad (I := I) g₀ 0 2 a
                  (deTurckSmoothRemainder (I := I) g₀ g_bg T hδ_lt hδ -
                    deTurckSmoothRemainder (I := I) g₀ g_bg T' hδ'_lt hδ')).toSection x) ≤
              Cmid * ∑ i ∈ Finset.range (a + 2 + 1),
                riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
                    ((iteratedCovGrad (I := I) g₀ 0 2 i (T - T')).toSection x)
                  * ∑ l ∈ Finset.range (a + 2 + 1 - i),
                      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + l) x
                        ((iteratedCovGrad (I := I) g₀ 0 s l coeff).toSection x)) := by
  -- Strip the `C⁰` fibre-sup packaging off the irreducible chart→intrinsic core: the core supplies
  -- the intrinsic coefficient field and the (ball-uniform) diagonal product grid; the coefficient
  -- sup and the `Cw` scale are `(T, T')`-independent and hoisted outside the perturbation quantifier.
  obtain ⟨s, coeff, Cmid, hCmid, hgrid⟩ :=
    deTurckRemainderDiff_singleField_diagonalGrid_intrinsicCore (I := I) (M := M) g₀ g_bg a hR
  -- **Sharp** `C⁰` fibre-sup scale of the perturbation difference: the supercritical-Sobolev section
  -- embedding constant `C₀ = Cw` is `(T, T')`-independent.
  obtain ⟨C₀, hC₀_nn, hC₀⟩ :=
    exists_riemannianFiberNormSq_section_le_smoothCcToTensorHs_sq (I := I) (M := M) g₀ a ha_super
  -- `C⁰` fibre-sup of the FIXED coefficient field `coeff` on the compact manifold (uniform).
  obtain ⟨Kc, hKc_nn, hKc⟩ :=
    exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ 0 s coeff
  refine ⟨s, coeff, Cmid, Real.sqrt Kc, C₀, hCmid, Real.sqrt_nonneg Kc, hC₀_nn, ?_, ?_⟩
  · intro x
    rw [Real.sq_sqrt hKc_nn]
    exact hKc x
  intro T T' δ hδ_lt hδ δ' hδ'_lt hδ' hTball hT'ball
  set ΛW : ℝ := C₀ * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) (T - T')‖ with hΛW_def
  have hΛW_nn : 0 ≤ ΛW := by rw [hΛW_def]; positivity
  refine ⟨ΛW, hΛW_nn, le_of_eq hΛW_def, ?_,
    hgrid T T' hδ_lt hδ hδ'_lt hδ' hTball hT'ball⟩
  intro x
  rw [hΛW_def]
  exact hC₀ (T - T') x

/-- **The intrinsic covariant Faà-di-Bruno principal/lower-order split of the sealed Ricci–DeTurck
remainder difference into two single-coefficient covariant-bilinear product fields** (assembled from
the single-field diagonal grid posit).

Fix `g₀`, the DeTurck background `g_bg`, an order `a`, and a covariant-`L²` ball radius `R ≥ 0`.
There is a fixed DeTurck chart-polynomial coefficient valence `s`; for any two `g₀`-fibre-small smooth
perturbations `T, T'` whose covariant-`L²` jets up to order `a + 2` lie in the radius-`R` ball, there
are a coefficient pair `coeff₁, coeff₂ : SmoothCcTensor g₀ 0 s`, a per-coefficient middle grid
constant `Cmid ≥ 0`, two `C⁰` fibre-sup levels `ΛW, Λcoeff ≥ 0`, and a **two-field split** of the
sealed remainder difference
`D := deTurckSmoothRemainder g₀ g_bg T − deTurckSmoothRemainder g₀ g_bg T'`,
`D = D₁ + D₂` with `D₁, D₂ : SmoothCcTensor g₀ 0 2`, such that `√rfns(T − T') ≤ ΛW`,
`√rfns(coeffₚ) ≤ Λcoeff`, and for **each** field `Dₚ` the single-coefficient diagonal
covariant-Leibniz product-grid domination
`rfns(∇^a Dₚ)(x) ≤ Cmid · ∑_{i ≤ a+2} rfns(∇^i (T − T'))(x) · ∑_{l ≤ a+2−i} rfns(∇^l coeffₚ)(x)`.

It is **assembled** from the single-field diagonal grid posit
`deTurckRemainderDiff_singleField_diagonalGrid` by taking the principal field to be the entire sealed
remainder difference `D₁ := D`, the lower-order field to be `D₂ := 0`, and both coefficient columns to
be the single posited coefficient (`coeff₁ = coeff₂ = coeff`).  The principal-field grid is the posit;
the lower-order-field grid is trivial (`∇^a 0 = 0`, `rfns(0) = 0 ≤ Cmid · (nonneg grid)`); the split
`D = D₁ + D₂` is `add_zero`.  Consumers transitively depend on the posit's `sorryAx`. -/
private theorem deTurckRemainderDiff_principalSplit_singleCoeffDiagonalGrid
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 3 ≤ a) {R : ℝ} (hR : 0 ≤ R) :
    ∃ (s : ℕ) (coeff₁ coeff₂ : SmoothCcTensor g₀ 0 s) (Cmid Λcoeff Cw : ℝ),
      0 ≤ Cmid ∧ 0 ≤ Λcoeff ∧ 0 ≤ Cw ∧
      (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 s x (coeff₁.toSection x) ≤
        Λcoeff ^ 2) ∧
      (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 s x (coeff₂.toSection x) ≤
        Λcoeff ^ 2) ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_lt : δ < 1)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (hδ'_lt : δ' < 1)
        (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ∃ (D₁ D₂ : SmoothCcTensor g₀ 0 2) (ΛW : ℝ),
          0 ≤ ΛW ∧
          ΛW ≤ Cw * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) (T - T')‖ ∧
          deTurckSmoothRemainder (I := I) g₀ g_bg T hδ_lt hδ -
              deTurckSmoothRemainder (I := I) g₀ g_bg T' hδ'_lt hδ' = D₁ + D₂ ∧
          (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x ((T - T').toSection x) ≤
            ΛW ^ 2) ∧
          (∀ x : M,
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + a) x
                ((iteratedCovGrad (I := I) g₀ 0 2 a D₁).toSection x) ≤
              Cmid * ∑ i ∈ Finset.range (a + 2 + 1),
                riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
                    ((iteratedCovGrad (I := I) g₀ 0 2 i (T - T')).toSection x)
                  * ∑ l ∈ Finset.range (a + 2 + 1 - i),
                      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + l) x
                        ((iteratedCovGrad (I := I) g₀ 0 s l coeff₁).toSection x)) ∧
          (∀ x : M,
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + a) x
                ((iteratedCovGrad (I := I) g₀ 0 2 a D₂).toSection x) ≤
              Cmid * ∑ i ∈ Finset.range (a + 2 + 1),
                riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
                    ((iteratedCovGrad (I := I) g₀ 0 2 i (T - T')).toSection x)
                  * ∑ l ∈ Finset.range (a + 2 + 1 - i),
                      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + l) x
                        ((iteratedCovGrad (I := I) g₀ 0 s l coeff₂).toSection x)) := by
  obtain ⟨s, coeff, Cmid, Λcoeff, Cw, hCmid, hΛcoeff, hCw, hcoeffsup, hgrid⟩ :=
    deTurckRemainderDiff_singleField_diagonalGrid (I := I) (M := M) g₀ g_bg a ha_super hR
  refine ⟨s, coeff, coeff, Cmid, Λcoeff, Cw, hCmid, hΛcoeff, hCw, hcoeffsup, hcoeffsup, ?_⟩
  intro T T' δ hδ_lt hδ δ' hδ'_lt hδ' hTball hT'ball
  obtain ⟨ΛW, hΛW, hWupper, hWsup, hgridD⟩ :=
    hgrid T T' hδ_lt hδ hδ'_lt hδ' hTball hT'ball
  -- Principal field `D₁ := D` (the whole sealed remainder difference); lower-order field `D₂ := 0`.
  refine ⟨deTurckSmoothRemainder (I := I) g₀ g_bg T hδ_lt hδ -
      deTurckSmoothRemainder (I := I) g₀ g_bg T' hδ'_lt hδ',
    0, ΛW, hΛW, hWupper, ?_, hWsup, hgridD, ?_⟩
  · -- The split `D = D + 0`.
    rw [add_zero]
  · -- The lower-order grid: `∇^a 0 = 0`, so `rfns(∇^a D₂) = 0`, dominated by the nonnegative grid.
    intro x
    have hzero_grad_all : ∀ n : ℕ,
        iteratedCovGrad (I := I) g₀ 0 2 n (0 : SmoothCcTensor g₀ 0 2) = 0 := by
      intro n
      induction n with
      | zero => rw [iteratedCovGrad_zero]
      | succ k ih =>
          rw [iteratedCovGrad_succ, ih,
            DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covGrad_zero
              (I := I) (M := M) g₀ 0 (2 + k)]
    have hzero_grad := hzero_grad_all a
    have hzero_rfns :
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + a) x
            ((iteratedCovGrad (I := I) g₀ 0 2 a (0 : SmoothCcTensor g₀ 0 2)).toSection x) = 0 := by
      rw [hzero_grad]
      simp only [SmoothCcTensor.toSection_zero, ContMDiffSection.coe_zero, Pi.zero_apply]
      exact riemannianFiberNormSq_zero (I := I) (M := M) g₀ 0 (2 + a) x
    rw [hzero_rfns]
    -- The grid RHS is nonnegative (product of two nonnegative `rfns` sums, scaled by `Cmid ≥ 0`).
    refine mul_nonneg hCmid (Finset.sum_nonneg (fun i _ => ?_))
    exact mul_nonneg
      (riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + i) x _)
      (Finset.sum_nonneg (fun l _ =>
        riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (s + l) x _))

/-- **The covariant Faà-di-Bruno diagonal-product-grid pointwise domination of the genuine
Ricci–DeTurck remainder difference (the honest, engine-consumable shape).**

Fix `g₀`, the DeTurck background `g_bg`, an order `a`, and a covariant-`L²` ball radius `R ≥ 0`.
There is a fixed DeTurck chart-polynomial **coefficient valence** `s` and, for any two
`g₀`-fibre-small smooth perturbations `T, T'` whose covariant-`L²` jets up to order `a + 2` lie in the
radius-`R` ball, there are a **coefficient pair** `coeff₁, coeff₂ : SmoothCcTensor g₀ 0 s`, a middle
grid constant `Cmid ≥ 0`, and two `C⁰` fibre-sup levels `ΛW, Λcoeff ≥ 0` with `√rfns(T − T') ≤ ΛW`,
`√rfns(coeffₚ) ≤ Λcoeff`, and the **diagonal product-grid domination**: for every `x`, the order-`a`
covariant gradient of the genuine remainder difference
`D := deTurckSmoothRemainder g₀ g_bg T − deTurckSmoothRemainder g₀ g_bg T'` obeys
```
rfns(∇^a D)(x)
  ≤ Cmid · ∑_{i ≤ a+2} rfns(∇^i (T − T'))(x) · ∑_{l ≤ a+2−i} (rfns(∇^l coeff₁)(x)+rfns(∇^l coeff₂)(x)).
```

This is the honest covariant-Leibniz product-grid shape consumed by the integrated engine
`exists_integrated_diagonalProductGrid_twoArm_pair_le` (no pointwise two-arm split — that shape is
refuted, see `GagliardoNirenbergProductTwoArm`).  It is **assembled** from the principal/lower-order
split `deTurckRemainderDiff_principalSplit_singleCoeffDiagonalGrid`: that posit exhibits
`D = D₁ + D₂` with each field `Dₚ` dominated by its single-coefficient diagonal grid against `coeffₚ`;
the `2`-sub-additivity of the intrinsic fibre norm (`riemannianFiberNormSq_add_le`) on `∇^a D =
∇^a D₁ + ∇^a D₂` splits `rfns(∇^a D)` into `2·rfns(∇^a D₁) + 2·rfns(∇^a D₂)`, and the two
single-coefficient grids merge per diagonal column into the `coeff₁ + coeff₂` pair grid (the
leaf-`Cmid` is `2·Cmid`).  Consumers transitively depend on the `sorryAx` of the posited split. -/
theorem pointwise_iteratedCovGrad_deTurckRemainderDiff_productGrid
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 3 ≤ a) {R : ℝ} (hR : 0 ≤ R) :
    ∃ (s : ℕ) (coeff₁ coeff₂ : SmoothCcTensor g₀ 0 s) (Cmid Λcoeff Cw : ℝ),
      0 ≤ Cmid ∧ 0 ≤ Λcoeff ∧ 0 ≤ Cw ∧
      (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 s x (coeff₁.toSection x) ≤
        Λcoeff ^ 2) ∧
      (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 s x (coeff₂.toSection x) ≤
        Λcoeff ^ 2) ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_lt : δ < 1)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (hδ'_lt : δ' < 1)
        (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ∃ ΛW : ℝ,
          0 ≤ ΛW ∧
          ΛW ≤ Cw * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) (T - T')‖ ∧
          (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x ((T - T').toSection x) ≤
            ΛW ^ 2) ∧
          ∀ x : M,
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + a) x
                ((iteratedCovGrad (I := I) g₀ 0 2 a
                  (deTurckSmoothRemainder (I := I) g₀ g_bg T hδ_lt hδ -
                    deTurckSmoothRemainder (I := I) g₀ g_bg T' hδ'_lt hδ')).toSection x) ≤
              Cmid * ∑ i ∈ Finset.range (a + 2 + 1),
                riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
                    ((iteratedCovGrad (I := I) g₀ 0 2 i (T - T')).toSection x)
                  * ∑ l ∈ Finset.range (a + 2 + 1 - i),
                      (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + l) x
                          ((iteratedCovGrad (I := I) g₀ 0 s l coeff₁).toSection x)
                        + riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + l) x
                          ((iteratedCovGrad (I := I) g₀ 0 s l coeff₂).toSection x)) := by
  obtain ⟨s, coeff₁, coeff₂, Cmid, Λcoeff, Cw, hCmid, hΛcoeff, hCw, hcoeff₁sup, hcoeff₂sup, hsplit⟩ :=
    deTurckRemainderDiff_principalSplit_singleCoeffDiagonalGrid (I := I) (M := M) g₀ g_bg a
      ha_super hR
  refine ⟨s, coeff₁, coeff₂, 2 * Cmid, Λcoeff, Cw, by positivity, hΛcoeff, hCw,
    hcoeff₁sup, hcoeff₂sup, ?_⟩
  intro T T' δ hδ_lt hδ δ' hδ'_lt hδ' hTball hT'ball
  obtain ⟨D₁, D₂, ΛW, hΛW, hWupper, hDsplit, hWsup, hgrid₁, hgrid₂⟩ :=
    hsplit T T' hδ_lt hδ hδ'_lt hδ' hTball hT'ball
  refine ⟨ΛW, hΛW, hWupper, hWsup, ?_⟩
  intro x
  -- Abbreviations: the difference-jet column and the two coefficient diagonal columns at `x`.
  set Wcol : ℕ → ℝ := fun i =>
    riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
      ((iteratedCovGrad (I := I) g₀ 0 2 i (T - T')).toSection x) with hWcol
  set c₁col : ℕ → ℝ := fun l =>
    riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + l) x
      ((iteratedCovGrad (I := I) g₀ 0 s l coeff₁).toSection x) with hc₁col
  set c₂col : ℕ → ℝ := fun l =>
    riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + l) x
      ((iteratedCovGrad (I := I) g₀ 0 s l coeff₂).toSection x) with hc₂col
  -- The order-`a` covariant gradient of the split remainder difference is `∇^a D₁ + ∇^a D₂`.
  have hsplit_grad :
      iteratedCovGrad (I := I) g₀ 0 2 a
          (deTurckSmoothRemainder (I := I) g₀ g_bg T hδ_lt hδ -
            deTurckSmoothRemainder (I := I) g₀ g_bg T' hδ'_lt hδ') =
        iteratedCovGrad (I := I) g₀ 0 2 a D₁ + iteratedCovGrad (I := I) g₀ 0 2 a D₂ := by
    rw [hDsplit, iteratedCovGrad_add]
  -- `2`-sub-additivity of the intrinsic fibre norm on the split.
  have hsub :
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + a) x
          ((iteratedCovGrad (I := I) g₀ 0 2 a
            (deTurckSmoothRemainder (I := I) g₀ g_bg T hδ_lt hδ -
              deTurckSmoothRemainder (I := I) g₀ g_bg T' hδ'_lt hδ')).toSection x) ≤
        2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + a) x
              ((iteratedCovGrad (I := I) g₀ 0 2 a D₁).toSection x) +
          2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + a) x
              ((iteratedCovGrad (I := I) g₀ 0 2 a D₂).toSection x) := by
    rw [hsplit_grad]
    exact riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 0 (2 + a) x
      ((iteratedCovGrad (I := I) g₀ 0 2 a D₁).toSection x)
      ((iteratedCovGrad (I := I) g₀ 0 2 a D₂).toSection x)
  -- The two posited single-coefficient diagonal grids, in column abbreviations.
  have hg₁ : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + a) x
        ((iteratedCovGrad (I := I) g₀ 0 2 a D₁).toSection x) ≤
      Cmid * ∑ i ∈ Finset.range (a + 2 + 1), Wcol i * ∑ l ∈ Finset.range (a + 2 + 1 - i), c₁col l :=
    hgrid₁ x
  have hg₂ : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + a) x
        ((iteratedCovGrad (I := I) g₀ 0 2 a D₂).toSection x) ≤
      Cmid * ∑ i ∈ Finset.range (a + 2 + 1), Wcol i * ∑ l ∈ Finset.range (a + 2 + 1 - i), c₂col l :=
    hgrid₂ x
  -- Merge the two single-coefficient grids into the pair grid, column by column.
  have hmerge :
      Cmid * ∑ i ∈ Finset.range (a + 2 + 1), Wcol i * ∑ l ∈ Finset.range (a + 2 + 1 - i), c₁col l +
        Cmid * ∑ i ∈ Finset.range (a + 2 + 1),
            Wcol i * ∑ l ∈ Finset.range (a + 2 + 1 - i), c₂col l =
      Cmid * ∑ i ∈ Finset.range (a + 2 + 1),
          Wcol i * ∑ l ∈ Finset.range (a + 2 + 1 - i), (c₁col l + c₂col l) := by
    rw [← mul_add, ← Finset.sum_add_distrib]
    refine congrArg (Cmid * ·) (Finset.sum_congr rfl (fun i _ => ?_))
    rw [← mul_add, Finset.sum_add_distrib]
  -- Chain: subadditivity, the two grids (scaled by 2), and the merge.
  calc riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + a) x
          ((iteratedCovGrad (I := I) g₀ 0 2 a
            (deTurckSmoothRemainder (I := I) g₀ g_bg T hδ_lt hδ -
              deTurckSmoothRemainder (I := I) g₀ g_bg T' hδ'_lt hδ')).toSection x)
      ≤ 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + a) x
              ((iteratedCovGrad (I := I) g₀ 0 2 a D₁).toSection x) +
          2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + a) x
              ((iteratedCovGrad (I := I) g₀ 0 2 a D₂).toSection x) := hsub
    _ ≤ 2 * (Cmid * ∑ i ∈ Finset.range (a + 2 + 1),
            Wcol i * ∑ l ∈ Finset.range (a + 2 + 1 - i), c₁col l) +
          2 * (Cmid * ∑ i ∈ Finset.range (a + 2 + 1),
            Wcol i * ∑ l ∈ Finset.range (a + 2 + 1 - i), c₂col l) := by
        exact add_le_add (by linarith [hg₁]) (by linarith [hg₂])
    _ = 2 * (Cmid * ∑ i ∈ Finset.range (a + 2 + 1),
            Wcol i * ∑ l ∈ Finset.range (a + 2 + 1 - i), (c₁col l + c₂col l)) := by
        rw [← hmerge]; ring
    _ = 2 * Cmid * ∑ i ∈ Finset.range (a + 2 + 1),
            Wcol i * ∑ l ∈ Finset.range (a + 2 + 1 - i),
              (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + l) x
                  ((iteratedCovGrad (I := I) g₀ 0 s l coeff₁).toSection x)
                + riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + l) x
                  ((iteratedCovGrad (I := I) g₀ 0 s l coeff₂).toSection x)) := by
        rw [hc₁col, hc₂col]; ring

/-- **The two-arm covariant-`L²` ball-Lipschitz bound on the genuine Ricci–DeTurck remainder
difference (the `covGrad`-iterate `L²` core of `smoothRemainderDiff_ballLipschitz_Ha2`).**

Fix `g₀`, the DeTurck background `g_bg`, an order `a`, and a covariant-`L²` ball radius `R ≥ 0`.
There is a fixed DeTurck chart-polynomial coefficient valence `s` such that for any two
`g₀`-fibre-small smooth perturbations `T, T' : SmoothCcTensor g₀ 0 2` in the radius-`R`
covariant-`L²` ball (`∀ j ≤ a + 2, ‖∇^j T‖ ≤ R`, idem `T'`), there are a fixed smooth DeTurck
coefficient pair `coeff₁, coeff₂ : SmoothCcTensor g₀ 0 s`, sup levels `ΛW, Λcoeff ≥ 0`, and a
constant `C ≥ 0`, such that the order-`a` covariant-gradient iterate `L²` norm of the genuine
remainder difference
`D := deTurckSmoothRemainder g₀ g_bg T − deTurckSmoothRemainder g₀ g_bg T'` obeys the **two-arm
tame bound** (at the squared level)
```
‖∇^a D‖² ≤ C · Λcoeff² · ∑_{i ≤ a+2} ‖∇^i (T − T')‖²
            + C · ΛW²    · ∑_{l ≤ a+2} (‖∇^l coeff₁‖² + ‖∇^l coeff₂‖²).
```

The **difference arm** carries the full covariant-`L²` jet scale of `T − T'` (up to the quasilinear
order `a + 2`, because the Ricci–DeTurck remainder difference carries second-order `∂²(T − T')`
factors, `chartDeTurckRicciRHS_sub_eq_principalSymbol_add_lowerOrder`) against the `C⁰` sup `Λcoeff`
of the fixed coefficient data (an `O(R)` metric defect on the principal column); the **cross arm**
carries the full jet scale of the coefficient data against the `C⁰` sup `ΛW` of the perturbation
difference.  Both arms vanish as `T − T' → 0` (the difference arm through the jets, the cross arm
through `ΛW`), so this is a genuine Lipschitz-squared estimate.  It is the spatial half of the
existence forcing input `deTurckSobolevNHa2_mixed_lipschitz`; the spectral `H^σ` translation of this
covariant-`L²` bound is the interior-elliptic/Gårding tower's separate job.

The bound is assembled by feeding the posited covariant diagonal product-grid domination
`pointwise_iteratedCovGrad_deTurckRemainderDiff_productGrid` through the **sorry-free** integrated
Gagliardo–Nirenberg two-arm engine `exists_integrated_diagonalProductGrid_twoArm_pair_le` (the honest
integrated replacement for the refuted pointwise two-arm split).  It depends transitively on the
`sorry` of the posited covariant expansion and on the `Lᵖ`-interpolation `sorry` underneath the
engine. -/
theorem deTurckRemainderDiff_iteratedCovGrad_twoArm_ballLipschitz
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 3 ≤ a) {R : ℝ} (hR : 0 ≤ R) :
    ∃ (s : ℕ) (coeff₁ coeff₂ : SmoothCcTensor g₀ 0 s) (C Λcoeff Cw : ℝ),
      0 ≤ C ∧ 0 ≤ Λcoeff ∧ 0 ≤ Cw ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_lt : δ < 1)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (hδ'_lt : δ' < 1)
        (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ∃ ΛW : ℝ,
          0 ≤ ΛW ∧
          ΛW ≤ Cw * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) (T - T')‖ ∧
          ‖iteratedCovGrad (I := I) g₀ 0 2 a
              (deTurckSmoothRemainder (I := I) g₀ g_bg T hδ_lt hδ -
                deTurckSmoothRemainder (I := I) g₀ g_bg T' hδ'_lt hδ')‖ ^ 2 ≤
            C * Λcoeff ^ 2 * ∑ i ∈ Finset.range (a + 2 + 1),
                ‖iteratedCovGrad (I := I) g₀ 0 2 i (T - T')‖ ^ 2
              + C * ΛW ^ 2 * ∑ l ∈ Finset.range (a + 2 + 1),
                (‖iteratedCovGrad (I := I) g₀ 0 s l coeff₁‖ ^ 2
                  + ‖iteratedCovGrad (I := I) g₀ 0 s l coeff₂‖ ^ 2) := by
  obtain ⟨s, coeff₁, coeff₂, Cmid, Λcoeff, Cw, hCmid, hΛcoeff, hCw, hcoeff₁sup, hcoeff₂sup, hgrid⟩ :=
    pointwise_iteratedCovGrad_deTurckRemainderDiff_productGrid (I := I) (M := M) g₀ g_bg a
      ha_super hR
  -- The sorry-free integrated two-arm pair engine, at valences (2, s), window (a+2), order a —
  -- its constant `Cd` is `(T, T')`-independent, so `C := Cd · Cmid` is ball-uniform.
  obtain ⟨Cd, hCd, hpair⟩ :=
    Analysis.Sobolev.Tensor.exists_integrated_diagonalProductGrid_twoArm_pair_le
      (I := I) (M := M) g₀ 2 s (a + 2) a
  refine ⟨s, coeff₁, coeff₂, Cd * Cmid, Λcoeff, Cw, by positivity, hΛcoeff, hCw, ?_⟩
  intro T T' δ hδ_lt hδ δ' hδ'_lt hδ' hTball hT'ball
  obtain ⟨ΛW, hΛW, hWupper, hWsup, hdom⟩ :=
    hgrid T T' hδ_lt hδ hδ'_lt hδ' hTball hT'ball
  refine ⟨ΛW, hΛW, hWupper, ?_⟩
  -- Feed the posited product grid (with `U := D`, `W := T - T'`, pair `(coeff₁, coeff₂)`).
  have hres :=
    hpair (deTurckSmoothRemainder (I := I) g₀ g_bg T hδ_lt hδ -
        deTurckSmoothRemainder (I := I) g₀ g_bg T' hδ'_lt hδ')
      (T - T') coeff₁ coeff₂ Cmid ΛW Λcoeff hCmid hΛW hΛcoeff hWsup hcoeff₁sup hcoeff₂sup hdom
  -- The engine concludes the squared two-arm bound; re-associate the constant.
  calc ‖iteratedCovGrad (I := I) g₀ 0 2 a
          (deTurckSmoothRemainder (I := I) g₀ g_bg T hδ_lt hδ -
            deTurckSmoothRemainder (I := I) g₀ g_bg T' hδ'_lt hδ')‖ ^ 2
      ≤ Cd * Cmid * Λcoeff ^ 2 * ∑ i ∈ Finset.range (a + 2 + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 2 i (T - T')‖ ^ 2
        + Cd * Cmid * ΛW ^ 2 * ∑ l ∈ Finset.range (a + 2 + 1),
            (‖iteratedCovGrad (I := I) g₀ 0 s l coeff₁‖ ^ 2
              + ‖iteratedCovGrad (I := I) g₀ 0 s l coeff₂‖ ^ 2) := hres
    _ = (Cd * Cmid) * Λcoeff ^ 2 * ∑ i ∈ Finset.range (a + 2 + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 2 i (T - T')‖ ^ 2
        + (Cd * Cmid) * ΛW ^ 2 * ∑ l ∈ Finset.range (a + 2 + 1),
            (‖iteratedCovGrad (I := I) g₀ 0 s l coeff₁‖ ^ 2
              + ‖iteratedCovGrad (I := I) g₀ 0 s l coeff₂‖ ^ 2) := by ring

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral
