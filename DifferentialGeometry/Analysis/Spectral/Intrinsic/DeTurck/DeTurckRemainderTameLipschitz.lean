import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.SobolevNonlinearityExistence
import DifferentialGeometry.Analysis.Sobolev.MoserTameProduct
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.GagliardoNirenbergProductTwoArm
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.IteratedCovGradLinear
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.RiemannianFiberNormSqSmoothCcUniformBound

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

/-- **(POSIT — the genuine chart→intrinsic parallel-bilinear covariant-Leibniz diagonal grid of the
Ricci–DeTurck right-hand-side arm of the sealed remainder difference.)**

This is the irreducible chart→intrinsic realization datum, in its raw parallel-bilinear covariant-Leibniz
diagonal-grid form (the immediate output of the covariant-Leibniz engine applied to the monomial
realization, BEFORE the coefficient column is supremised).  For any two `g₀`-fibre-small smooth
perturbations `T, T'`, there are a realized coefficient rank `s`, an intrinsic coefficient field
`coeff : SmoothCcTensor g₀ 0 s` (the assembled per-pair undifferenced curvature / metric / Christoffel /
inverse-Gram chart-monomial coefficient data, realized as a single smooth `(0,s)`-tensor section on the
compact `M`), and a single nonnegative **per-pair** grid constant `Cmid` (depending on the metric path,
hence on `T, T'`, but uniform over `x`), such that for the **RHS-arm residual**
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

**The chart→intrinsic content.**  By the chart-polynomial difference
`chartDeTurckRicciRHS_sub_eq_principalSymbol_add_lowerOrder` grounded against the intrinsic operator
(`deTurckRicciRHS_chartBasisVecFiber_eq_chartDeTurckRicciRHS`), the RHS difference is a finite sum of
bilinear monomials, each a product of fixed (per-pair-smooth) undifferenced curvature / metric /
Christoffel / inverse-Gram coefficient data `coeff_k(g₀ + T, g₀ + T')` with a single `(T − T')` jet of
chart order `≤ 2`.  Realized intrinsically, each monomial is a parallel (metric-contraction, `∇g = 0`)
covariant-bilinear product reading `∇^{≤ 2}(T − T')`, whose order-`a` covariant Leibniz double grid
(`ParallelTensorProduct.exists_norm_iteratedCovGrad_prod_le`) bounds `rfns(∇^a monomial)(x)` by the
diagonal product grid of the `∇^{≤ a+2}(T − T')` jet against the realized coefficient jets
`rfns(∇^{≤ a+2−q} coeff)`; merging the finitely many monomial coefficient columns into the single
realized coefficient field `coeff` gives the displayed diagonal grid.  The chart-locality-free
realization of the monomial coefficient data as an intrinsic smooth section `coeff` and the parallel
covariant-bilinear product structure has **no on-disk antecedent** (the chart→intrinsic globalization of
the coefficient data is the irreducible open analytic sub-program); its body is `sorry`, and consumers
transitively depend on its `sorryAx`.

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
  sorry

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
    ∀ (T T' : SmoothCcTensor g₀ 0 2)
      {δ : ℝ} (hδ_lt : δ < 1)
      (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
      {δ' : ℝ} (hδ'_lt : δ' < 1)
      (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
      (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
      (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
      ∃ C : ℝ,
        0 ≤ C ∧
        (∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + a) x
              ((iteratedCovGrad (I := I) g₀ 0 2 a
                (deTurckSmoothRemainder (I := I) g₀ g_bg T hδ_lt hδ -
                  deTurckSmoothRemainder (I := I) g₀ g_bg T' hδ'_lt hδ')).toSection x) ≤
            C * ∑ q ∈ Finset.range (a + 2 + 1),
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + q) x
                ((iteratedCovGrad (I := I) g₀ 0 2 q (T - T')).toSection x)) := by
  intro T T' δ hδ_lt hδ δ' hδ'_lt hδ' hTball hT'ball
  -- The sealed remainder difference and the two arms.
  set D : SmoothCcTensor g₀ 0 2 :=
    deTurckSmoothRemainder (I := I) g₀ g_bg T hδ_lt hδ -
      deTurckSmoothRemainder (I := I) g₀ g_bg T' hδ'_lt hδ' with hD_def
  set Δdiff : SmoothCcTensor g₀ 0 2 :=
    rawTensorConnLapSmooth (I := I) g₀ 0 2 (T - T') with hΔdiff_def
  set RHSarm : SmoothCcTensor g₀ 0 2 := D + Δdiff with hRHSarm_def
  -- The Δ-arm covariant-jet posit at `W := T − T'`.
  obtain ⟨CΔ, hCΔ_nn, hCΔ⟩ :=
    rawTensorConnLapSmooth_iteratedCovGrad_riemannianFiberNormSq_jet_le (I := I) (M := M) g₀ a
  -- The RHS-arm chart→intrinsic per-pair covariant-jet posit.
  obtain ⟨CR, hCR_nn, hCR⟩ :=
    deTurckRHSArmDiff_iteratedCovGrad_riemannianFiberNormSq_jet_le (I := I) (M := M) g₀ g_bg a
      T T' hδ_lt hδ hδ'_lt hδ'
  refine ⟨2 * (CR + CΔ), by positivity, fun x => ?_⟩
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
    rw [hScol_def]; exact hCR x
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
    ∃ s : ℕ,
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_lt : δ < 1)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (hδ'_lt : δ' < 1)
        (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ∃ (coeff : SmoothCcTensor g₀ 0 s) (Cmid : ℝ),
          0 ≤ Cmid ∧
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
  -- The positive intrinsic coefficient column (`1 ≤ rfns(coeff)` everywhere): the metric tensor.
  obtain ⟨s, coeff, hcoeff_floor⟩ := exists_positiveFloor_intrinsicCoeff (I := I) (M := M) g₀
  refine ⟨s, fun T T' δ hδ_lt hδ δ' hδ'_lt hδ' hTball hT'ball => ?_⟩
  -- The genuine order-`(a+2)`-window single-factor covariant grid of the sealed remainder difference
  -- at this `(T, T')` (the grid constant `C` depends on the metric path, hence on `T, T'`).
  obtain ⟨Cmid, hCmid_nn, hgrid⟩ :=
    deTurckRemainderDiff_singleField_singleFactorGrid (I := I) (M := M) g₀ g_bg a hR
      T T' hδ_lt hδ hδ'_lt hδ' hTball hT'ball
  refine ⟨coeff, Cmid, hCmid_nn, fun x => ?_⟩
  refine (hgrid x).trans ?_
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
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ) {R : ℝ} (hR : 0 ≤ R) :
    ∃ s : ℕ,
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_lt : δ < 1)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (hδ'_lt : δ' < 1)
        (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ∃ (coeff : SmoothCcTensor g₀ 0 s) (Cmid ΛW Λcoeff : ℝ),
          0 ≤ Cmid ∧ 0 ≤ ΛW ∧ 0 ≤ Λcoeff ∧
          (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x ((T - T').toSection x) ≤
            ΛW ^ 2) ∧
          (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 s x (coeff.toSection x) ≤
            Λcoeff ^ 2) ∧
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
  -- the intrinsic coefficient field and the diagonal product grid; the two sups are recovered from
  -- the uniform smooth-tensor fibre-norm bound on the compact manifold.
  obtain ⟨s, hcore⟩ :=
    deTurckRemainderDiff_singleField_diagonalGrid_intrinsicCore (I := I) (M := M) g₀ g_bg a hR
  refine ⟨s, ?_⟩
  intro T T' δ hδ_lt hδ δ' hδ'_lt hδ' hTball hT'ball
  obtain ⟨coeff, Cmid, hCmid, hgrid⟩ :=
    hcore T T' hδ_lt hδ hδ'_lt hδ' hTball hT'ball
  -- `C⁰` fibre-sup of the perturbation difference `T − T'` on the compact manifold.
  obtain ⟨KW, hKW_nn, hKW⟩ :=
    exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ 0 2 (T - T')
  -- `C⁰` fibre-sup of the coefficient field `coeff` on the compact manifold.
  obtain ⟨Kc, hKc_nn, hKc⟩ :=
    exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ 0 s coeff
  refine ⟨coeff, Cmid, Real.sqrt KW, Real.sqrt Kc, hCmid, Real.sqrt_nonneg KW,
    Real.sqrt_nonneg Kc, ?_, ?_, hgrid⟩
  · intro x
    rw [Real.sq_sqrt hKW_nn]
    exact hKW x
  · intro x
    rw [Real.sq_sqrt hKc_nn]
    exact hKc x

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
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ) {R : ℝ} (hR : 0 ≤ R) :
    ∃ s : ℕ,
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_lt : δ < 1)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (hδ'_lt : δ' < 1)
        (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ∃ (coeff₁ coeff₂ : SmoothCcTensor g₀ 0 s) (D₁ D₂ : SmoothCcTensor g₀ 0 2)
          (Cmid ΛW Λcoeff : ℝ),
          0 ≤ Cmid ∧ 0 ≤ ΛW ∧ 0 ≤ Λcoeff ∧
          deTurckSmoothRemainder (I := I) g₀ g_bg T hδ_lt hδ -
              deTurckSmoothRemainder (I := I) g₀ g_bg T' hδ'_lt hδ' = D₁ + D₂ ∧
          (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x ((T - T').toSection x) ≤
            ΛW ^ 2) ∧
          (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 s x (coeff₁.toSection x) ≤
            Λcoeff ^ 2) ∧
          (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 s x (coeff₂.toSection x) ≤
            Λcoeff ^ 2) ∧
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
  obtain ⟨s, hgrid⟩ :=
    deTurckRemainderDiff_singleField_diagonalGrid (I := I) (M := M) g₀ g_bg a hR
  refine ⟨s, ?_⟩
  intro T T' δ hδ_lt hδ δ' hδ'_lt hδ' hTball hT'ball
  obtain ⟨coeff, Cmid, ΛW, Λcoeff, hCmid, hΛW, hΛcoeff, hWsup, hcoeffsup, hgridD⟩ :=
    hgrid T T' hδ_lt hδ hδ'_lt hδ' hTball hT'ball
  -- Principal field `D₁ := D` (the whole sealed remainder difference); lower-order field `D₂ := 0`.
  refine ⟨coeff, coeff,
    deTurckSmoothRemainder (I := I) g₀ g_bg T hδ_lt hδ -
      deTurckSmoothRemainder (I := I) g₀ g_bg T' hδ'_lt hδ',
    0, Cmid, ΛW, Λcoeff, hCmid, hΛW, hΛcoeff, ?_, hWsup, hcoeffsup, hcoeffsup, hgridD, ?_⟩
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
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ) {R : ℝ} (hR : 0 ≤ R) :
    ∃ s : ℕ,
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_lt : δ < 1)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (hδ'_lt : δ' < 1)
        (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ∃ (coeff₁ coeff₂ : SmoothCcTensor g₀ 0 s) (Cmid ΛW Λcoeff : ℝ),
          0 ≤ Cmid ∧ 0 ≤ ΛW ∧ 0 ≤ Λcoeff ∧
          (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x ((T - T').toSection x) ≤
            ΛW ^ 2) ∧
          (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 s x (coeff₁.toSection x) ≤
            Λcoeff ^ 2) ∧
          (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 s x (coeff₂.toSection x) ≤
            Λcoeff ^ 2) ∧
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
  obtain ⟨s, hsplit⟩ :=
    deTurckRemainderDiff_principalSplit_singleCoeffDiagonalGrid (I := I) (M := M) g₀ g_bg a hR
  refine ⟨s, ?_⟩
  intro T T' δ hδ_lt hδ δ' hδ'_lt hδ' hTball hT'ball
  obtain ⟨coeff₁, coeff₂, D₁, D₂, Cmid, ΛW, Λcoeff, hCmid, hΛW, hΛcoeff,
      hDsplit, hWsup, hcoeff₁sup, hcoeff₂sup, hgrid₁, hgrid₂⟩ :=
    hsplit T T' hδ_lt hδ hδ'_lt hδ' hTball hT'ball
  refine ⟨coeff₁, coeff₂, 2 * Cmid, ΛW, Λcoeff, by positivity, hΛW, hΛcoeff,
    hWsup, hcoeff₁sup, hcoeff₂sup, ?_⟩
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
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ) {R : ℝ} (hR : 0 ≤ R) :
    ∃ s : ℕ,
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_lt : δ < 1)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (hδ'_lt : δ' < 1)
        (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ∃ (coeff₁ coeff₂ : SmoothCcTensor g₀ 0 s) (C ΛW Λcoeff : ℝ),
          0 ≤ C ∧ 0 ≤ ΛW ∧ 0 ≤ Λcoeff ∧
          ‖iteratedCovGrad (I := I) g₀ 0 2 a
              (deTurckSmoothRemainder (I := I) g₀ g_bg T hδ_lt hδ -
                deTurckSmoothRemainder (I := I) g₀ g_bg T' hδ'_lt hδ')‖ ^ 2 ≤
            C * Λcoeff ^ 2 * ∑ i ∈ Finset.range (a + 2 + 1),
                ‖iteratedCovGrad (I := I) g₀ 0 2 i (T - T')‖ ^ 2
              + C * ΛW ^ 2 * ∑ l ∈ Finset.range (a + 2 + 1),
                (‖iteratedCovGrad (I := I) g₀ 0 s l coeff₁‖ ^ 2
                  + ‖iteratedCovGrad (I := I) g₀ 0 s l coeff₂‖ ^ 2) := by
  obtain ⟨s, hgrid⟩ :=
    pointwise_iteratedCovGrad_deTurckRemainderDiff_productGrid (I := I) (M := M) g₀ g_bg a hR
  refine ⟨s, ?_⟩
  intro T T' δ hδ_lt hδ δ' hδ'_lt hδ' hTball hT'ball
  obtain ⟨coeff₁, coeff₂, Cmid, ΛW, Λcoeff, hCmid, hΛW, hΛcoeff,
      hWsup, hcoeff₁sup, hcoeff₂sup, hdom⟩ :=
    hgrid T T' hδ_lt hδ hδ'_lt hδ' hTball hT'ball
  -- The sorry-free integrated two-arm pair engine, at valences (2, s), window (a+2), order a.
  obtain ⟨Cd, hCd, hpair⟩ :=
    Analysis.Sobolev.Tensor.exists_integrated_diagonalProductGrid_twoArm_pair_le
      (I := I) (M := M) g₀ 2 s (a + 2) a
  refine ⟨coeff₁, coeff₂, Cd * Cmid, ΛW, Λcoeff, by positivity, hΛW, hΛcoeff, ?_⟩
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
