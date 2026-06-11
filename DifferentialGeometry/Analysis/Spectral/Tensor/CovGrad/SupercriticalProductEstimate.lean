import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.DeTurckCartanRfnsBilinearProduct
import DifferentialGeometry.Analysis.Sobolev.Embedding.SobolevEmbeddingManifoldC0
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.PointwiseToL2Packaging
import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.RealizeSymmIteratedCovGradFiberNormBound

/-! # The supercritical `L²` product estimate for the bare model tensor product

For a closed (compact, boundaryless) smooth Riemannian manifold `(M, g)` modelled on a real
inner-product space `E`, this file proves the **supercritical Banach-algebra (Moser) product
estimate** for the bare fibrewise model tensor product `bareTensorProdSection`, in the metric `L²`
norm:

  `‖S ⊗ T‖_{L²} ≤ C · ‖S‖_{H^{2k}} · ‖T‖_{L²}`

for `2k > dim M` (the supercritical sup-embedding threshold), where `‖·‖_{H^{2k}}` is the
chart-partition-of-unity Sobolev Hilbert norm `‖SmoothCcTensor.toHs (2k) ·‖` and `‖·‖_{L²}` is the
metric `L²` norm `‖·‖ = tensorL2Norm g 0 s ·.toFun` of a smooth compactly-carried tensor section.

## The mechanism (pointwise multiplicativity, integrated)

The bare model tensor product is *exactly multiplicative on intrinsic fibre norms*
(`bareTensorProdSection_rfns_le`, the `μ = 1` operator bound):
`rfns(S ⊗ T)(x) ≤ rfns(S)(x) · rfns(T)(x)` pointwise.  Embedding the first factor in the `C⁰` sup
norm by the supercritical Sobolev embedding `tensorPouSobolevHilbert_embedding_Ck_gNorm`
(`‖S.toSection x‖ ≤ C · ‖S.toHs (2k)‖`, identifying `‖S.toSection x‖² = rfns(S)(x)` through
`norm_toSection_eq_sqrt_riemannianFiberNormSq_installed`) bounds `rfns(S)(x)` uniformly by
`C² · ‖S.toHs (2k)‖²`, and the remaining factor stays in `L²`:

```
‖S ⊗ T‖²_{L²} = ∫ rfns(S ⊗ T) ≤ ∫ rfns(S)·rfns(T)
            ≤ (C² ‖S.toHs (2k)‖²) · ∫ rfns(T) = C² ‖S.toHs (2k)‖² · ‖T‖²_{L²}.
```

Taking square roots gives the stated bound.  This is the genuine Sobolev-multiplication content for
the bare product: one factor's full supercritical Sobolev regularity controls its sup norm, against
the other factor's bare `L²` mass.

## Why the output is stated in the `L²` norm (and not in `toHs`)

This estimate is stated in the intrinsic `L²` / covariant-jet currency (like the rest of the
covariant product machinery, cf. the integrated Gagliardo–Nirenberg two-arm bound) rather than in
the chart-PoU `toHs` currency that the bilinear-completion consumer
`Analysis.Sobolev.TensorHilbert.SobolevProductBound` expects, for two independent structural
reasons, both genuine gaps in the present library:

* **The reverse `toHs` bridge is absent at this output valence.**  Every sorry-free chart-Sobolev↔
  intrinsic-Sobolev norm bridge in the library is *one-directional*, controlling covariant-jet /
  `L²` data **by** the chart-PoU Sobolev norm (`iteratedCovGradJetSum_le_toHs`,
  `exists_iteratedCovGrad_l2Norm_le_toHs`, `iteratedCovGradSobolevNorm_le_baseSpectral`, …).  The
  *reverse* inequality — bounding `‖toHs s' (·)‖` of a section *above* by its covariant-jet `L²`
  sums (the hard half of the chart Sobolev norm equivalence) — exists only for the specific output
  valence `(0, 2)` of the DeTurck linearization (through the spectral coefficients), never for the
  general output valence `(0, s₁ + s₂)` produced here.

* **The bare product is not yet a bundled bilinear `LinearMap`.**  The consumer's `prod` argument is
  a `SmoothCcTensor g r₁ s₁ →ₗ[ℝ] SmoothCcTensor g r₂ s₂ →ₗ[ℝ] SmoothCcTensor g r₃ s₃`; the bare
  fibrewise product `bareTensorProdSection` is a plain `def` with no `map_add` / `map_smul`
  (fibrewise additivity / homogeneity) lemmas on disk, so the `→ₗ →ₗ` packaging the consumer
  consumes is not yet available either.

This file supplies the genuine analytic *content* of the Sobolev product — the pointwise
multiplicativity integrated against the supercritical embedding — independently of those two
packaging/bridge layers; instantiating the bilinear-completion consumer requires them in addition.
Sorry-free. -/

noncomputable section

set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry.Analysis.Sobolev.Tensor

open DifferentialGeometry
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [BoundarylessManifold I M]
      [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E
private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

set_option linter.unusedSectionVars false in
/-- **Pointwise uniform sup bound on the first factor's fibre norm from its supercritical Sobolev
norm.**  In the supercritical regime `2k > dim M`, the intrinsic fibre norm of a smooth
compactly-carried `(0, s₁)`-tensor `S` is bounded uniformly (over the manifold) by the square of a
constant times its chart-PoU Sobolev norm `‖S.toHs (2k)‖`:
`rfns(S)(x) ≤ C² · ‖S.toHs (2k)‖²` for all `x`, with `0 ≤ C` independent of `S`.

The constant `C` is the supercritical `C⁰` Sobolev embedding constant
`tensorPouSobolevHilbert_embedding_Ck_gNorm` at jet window `m = 0`; the squared form follows from
`‖S.toSection x‖² = rfns(S)(x)` (`norm_toSection_eq_sqrt_riemannianFiberNormSq_installed`). -/
theorem exists_riemannianFiberNormSq_le_toHs_sq_supercritical
    (g : SmoothRiemannianMetric I M) (s₁ k : ℕ)
    (h_super : 2 * k > Module.finrank ℝ E) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (S : Integral.L2.SmoothCcTensor g 0 s₁) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g 0 s₁ x (S.toSection x) ≤
          C ^ 2 * ‖IntrinsicSobolev.SmoothCcTensor.toHs (2 * k) S‖ ^ 2 := by
  obtain ⟨C, hCpos, hbound⟩ :=
    tensorPouSobolevHilbert_embedding_Ck_gNorm (I := I) (M := M) g 0 s₁ k 0
      (by simpa using h_super)
  refine ⟨C, le_of_lt hCpos, fun S x => ?_⟩
  have hCnn : 0 ≤ C := le_of_lt hCpos
  set NS := ‖IntrinsicSobolev.SmoothCcTensor.toHs (2 * k) S‖ with hNS
  have hNSnn : 0 ≤ NS := norm_nonneg _
  have hrfns_nonneg :
      0 ≤ riemannianFiberNormSq (I := I) (M := M) g 0 s₁ x (S.toSection x) :=
    riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 s₁ x (S.toSection x)
  -- `√rfns = ‖S.toSection x‖` (Riemannian-bundle instance), and `‖S.toSection x‖ ≤ C · NS`;
  -- combine to `√rfns ≤ C · NS` without ever touching the bare fibre norm in the goal.
  have hsqrt_le :
      Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g 0 s₁ x (S.toSection x)) ≤ C * NS := by
    have hsq := norm_toSection_eq_sqrt_riemannianFiberNormSq_installed (I := I) (M := M) g 0 s₁ S x
    have hnorm := hbound S x
    rw [hsq] at hnorm
    exact hnorm
  -- Square: rfns = (√rfns)² ≤ (C·NS)² = C²·NS².
  calc riemannianFiberNormSq (I := I) (M := M) g 0 s₁ x (S.toSection x)
      = Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g 0 s₁ x (S.toSection x)) ^ 2 :=
        (Real.sq_sqrt hrfns_nonneg).symm
    _ ≤ (C * NS) ^ 2 := by
        apply sq_le_sq'
        · linarith [mul_nonneg hCnn hNSnn, Real.sqrt_nonneg
            (riemannianFiberNormSq (I := I) (M := M) g 0 s₁ x (S.toSection x))]
        · exact hsqrt_le
    _ = C ^ 2 * NS ^ 2 := by rw [mul_pow]

set_option linter.unusedSectionVars false in
/-- **The supercritical `L²` product estimate for the bare model tensor product.**

For two smooth compactly-carried tensor sections `S : (0, s₁)`, `T : (0, s₂)` on a closed Riemannian
manifold, in the supercritical regime `2k > dim M`, the metric `L²` norm of their bare model tensor
product `S ⊗ T = bareTensorProdSection g S T : (0, s₁ + s₂)` is bounded by a constant (independent of
`S, T`) times the chart-PoU Sobolev norm `‖S.toHs (2k)‖` of the first factor and the metric `L²`
norm `‖T‖` of the second:

  `‖S ⊗ T‖ ≤ C · ‖S.toHs (2k)‖ · ‖T‖`.

This is the genuine Sobolev-multiplication (Banach-algebra) content of the bare product: the
pointwise multiplicativity `rfns(S ⊗ T) ≤ rfns(S)·rfns(T)` (`bareTensorProdSection_rfns_le`,
operator constant `μ = 1`) integrated, with the first factor controlled in the `C⁰` sup norm by its
supercritical Sobolev norm and the second kept in `L²`.

**Non-vacuity.**  The constant is uniform over `(S, T)` (quantified before them); the product
genuinely carries both factors (`prod 0 T = 0`, `prod S 0 = 0` are forced by the `μ = 1`
multiplicativity, so a `C = 0` witness is rejected by any pair with nonvanishing `L²` masses on both
sides).  The output is stated in the intrinsic `L²` currency because the reverse chart-Sobolev bridge
`‖toHs (s₁ + s₂) (·)‖ ≤ (covariant-jet L² data)` is absent in the library at this output valence
(see the module docstring). -/
theorem exists_bareTensorProdSection_l2Norm_le_toHs_mul_l2Norm_supercritical
    (g : SmoothRiemannianMetric I M) (s₁ s₂ k : ℕ)
    (h_super : 2 * k > Module.finrank ℝ E) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (S : Integral.L2.SmoothCcTensor g 0 s₁) (T : Integral.L2.SmoothCcTensor g 0 s₂),
        ‖bareTensorProdSection (I := I) g S T‖ ≤
          C * ‖IntrinsicSobolev.SmoothCcTensor.toHs (2 * k) S‖ * ‖T‖ := by
  obtain ⟨C, hCnn, hSbound⟩ :=
    exists_riemannianFiberNormSq_le_toHs_sq_supercritical (I := I) (M := M) g s₁ k h_super
  refine ⟨C, hCnn, fun S T => ?_⟩
  set μ := riemannianVolumeMeasure (I := I) (M := M) g with hμ
  set NSh := ‖IntrinsicSobolev.SmoothCcTensor.toHs (2 * k) S‖ with hNSh
  have hNSh_nonneg : 0 ≤ NSh := norm_nonneg _
  -- The integrability facts for the pointwise integrands.
  have hint_prod :
      MeasureTheory.Integrable
        (fun x => riemannianFiberNormSq (I := I) (M := M) g 0 (s₁ + s₂) x
          ((bareTensorProdSection (I := I) g S T).toSection x)) μ :=
    integrable_riemannianFiberNormSq_toSection (I := I) (M := M) g 0 (s₁ + s₂)
      (bareTensorProdSection (I := I) g S T)
  have hint_T :
      MeasureTheory.Integrable
        (fun x => riemannianFiberNormSq (I := I) (M := M) g 0 s₂ x (T.toSection x)) μ :=
    integrable_riemannianFiberNormSq_toSection (I := I) (M := M) g 0 s₂ T
  have hint_scaledT :
      MeasureTheory.Integrable
        (fun x => C ^ 2 * NSh ^ 2 *
          riemannianFiberNormSq (I := I) (M := M) g 0 s₂ x (T.toSection x)) μ :=
    hint_T.const_mul _
  -- Pointwise: rfns(S ⊗ T)(x) ≤ (C² NSh²) · rfns(T)(x).
  have hpt : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g 0 (s₁ + s₂) x
          ((bareTensorProdSection (I := I) g S T).toSection x) ≤
        C ^ 2 * NSh ^ 2 *
          riemannianFiberNormSq (I := I) (M := M) g 0 s₂ x (T.toSection x) := by
    intro x
    have hmul := bareTensorProdSection_rfns_le (I := I) g S T x
    rw [one_mul] at hmul
    have hTnn : 0 ≤ riemannianFiberNormSq (I := I) (M := M) g 0 s₂ x (T.toSection x) :=
      riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 s₂ x (T.toSection x)
    calc riemannianFiberNormSq (I := I) (M := M) g 0 (s₁ + s₂) x
            ((bareTensorProdSection (I := I) g S T).toSection x)
        ≤ riemannianFiberNormSq (I := I) (M := M) g 0 s₁ x (S.toSection x) *
            riemannianFiberNormSq (I := I) (M := M) g 0 s₂ x (T.toSection x) := hmul
      _ ≤ (C ^ 2 * NSh ^ 2) *
            riemannianFiberNormSq (I := I) (M := M) g 0 s₂ x (T.toSection x) := by
          exact mul_le_mul_of_nonneg_right (hSbound S x) hTnn
  -- Integrate the pointwise bound.
  have hint_le :
      ∫ x, riemannianFiberNormSq (I := I) (M := M) g 0 (s₁ + s₂) x
            ((bareTensorProdSection (I := I) g S T).toSection x) ∂μ ≤
        ∫ x, C ^ 2 * NSh ^ 2 *
            riemannianFiberNormSq (I := I) (M := M) g 0 s₂ x (T.toSection x) ∂μ :=
    MeasureTheory.integral_mono hint_prod hint_scaledT hpt
  rw [MeasureTheory.integral_const_mul] at hint_le
  -- Identify the integrals with squared L² norms.
  have hLHS :
      tensorL2Norm (I := I) (M := M) g 0 (s₁ + s₂)
          (bareTensorProdSection (I := I) g S T).toFun ^ 2 =
        ∫ x, riemannianFiberNormSq (I := I) (M := M) g 0 (s₁ + s₂) x
          ((bareTensorProdSection (I := I) g S T).toSection x) ∂μ :=
    tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq (I := I) (M := M) g (s₁ + s₂)
      (bareTensorProdSection (I := I) g S T)
  have hRHS :
      tensorL2Norm (I := I) (M := M) g 0 s₂ T.toFun ^ 2 =
        ∫ x, riemannianFiberNormSq (I := I) (M := M) g 0 s₂ x (T.toSection x) ∂μ :=
    tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq (I := I) (M := M) g s₂ T
  -- Rewrite the integrated inequality in terms of the L² norms.
  rw [SmoothCcTensor.norm_def, SmoothCcTensor.norm_def]
  set P := tensorL2Norm (I := I) (M := M) g 0 (s₁ + s₂)
      (bareTensorProdSection (I := I) g S T).toFun with hP
  set Q := tensorL2Norm (I := I) (M := M) g 0 s₂ T.toFun with hQ
  have hPnn : 0 ≤ P := by
    rw [hP, ← SmoothCcTensor.norm_def]; exact norm_nonneg _
  have hQnn : 0 ≤ Q := by
    rw [hQ, ← SmoothCcTensor.norm_def]; exact norm_nonneg _
  have hPsq : P ^ 2 ≤ (C ^ 2 * NSh ^ 2) * Q ^ 2 := by
    rw [hP, hLHS, hQ, hRHS]; exact hint_le
  -- Square-root: P ≤ C · NSh · Q.
  have hRHSnn : 0 ≤ C * NSh * Q := by positivity
  have hsq_target : P ^ 2 ≤ (C * NSh * Q) ^ 2 := by
    have : (C * NSh * Q) ^ 2 = (C ^ 2 * NSh ^ 2) * Q ^ 2 := by ring
    rw [this]; exact hPsq
  exact le_of_sq_le_sq hsq_target hRHSnn

end DifferentialGeometry.Analysis.Sobolev.Tensor

end
