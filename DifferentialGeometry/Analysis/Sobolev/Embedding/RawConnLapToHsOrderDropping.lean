import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RawConnLapL2SobolevBounds.RawTensorConnLapIterL2WtwokTwoBound
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.HilbertSpace
import DifferentialGeometry.Analysis.Sobolev.Tensor.PouWeightedHsNorm
import DifferentialGeometry.Analysis.Sobolev.Tensor.PouWeightedHsNormReverseOrderZero
import DifferentialGeometry.Analysis.Integration.L2.Hilbert.DenseSubset
import DifferentialGeometry.Analysis.Spectral.Tensor.Estimates.TensorSectionL2BoundByComponents
import DifferentialGeometry.Analysis.Sobolev.Manifold.MeasureBridgeUniform

/-! # Order-dropping completion-norm bounds for the rough tensor connection Laplacian

This file ships the intrinsic chart-Sobolev (`SmoothCcTensor.toHs`) boundedness of the rough
tensor connection Laplacian `Δ_∇ = rawTensorConnLapSmooth`, in the **easy** (differentiation)
direction needed by the order-`a` chart-RHS spectral tower.

The rough Laplacian is the frame trace of the second covariant derivative
(`rawTensorConnLap_eq_frame_trace_secondCovDeriv`), hence a *single* second-order operator: it
maps `H^{2(k+1)} → H^{2k}` boundedly, losing exactly **one** `toHs`-order (`= 2` derivatives),
not two.  This is the elliptic-boundedness primitive `exists_rawConnLapSmooth_toHs_le_toHs_succ`
(the order-`k` analogue of the on-disk `L²`/`H¹` instance
`rawTensorConnLapIter_intrinsicL2_le_tensorPouSobolevNorm_sq_one`, which is the `k = 0` case in
`∫⁻`-form): the tight single-step `H^σ(Δ_∇ T) ≤ C · H^{σ+1}(T)` bound, with no curvature
commutator / Gårding regularity (no `Order2GardingFamily`, no `CommutatorDefectBound`).  It is the
rough-Laplacian counterpart of the covariant-derivative order-dropping bound `covGrad_toHs_norm_le`
— but tight at `+1` `toHs`-order, since `Δ_∇` is a single second-order operator whereas a naive
`covGrad ∘ covGrad` composition would charge `+2`.

The `ℝ≥0∞` form `exists_rawConnLapSmooth_tensorPouSobolevHsNorm_le`, and on top of it the
completion-norm forms `exists_rawConnLapSmooth_toHs_le_toHs_succ` and the iterated bound
`exists_rawConnLapIter_toHs_le_toHs` (`H^k(Δ_∇^i T) ≤ C · H^{k+i}(T)`, the mirror of
`iteratedCovGrad_toHs_norm_le`), are proved by assembling the per-chart order-drop
`exists_rawConnLapSmooth_tensorPouSobolevHsNorm_le_perChart` over the chart base points (its body
is the single remaining `sorry`: the genuine atomic per-chart second-order elliptic-boundedness
content of the chart-coordinate formula `tensorChartComponentRaw_rawTensorConnLap_eq_chart_α_coord_formula`).

The companion primitive `exists_l2Norm_le_toHs_zero` records the reverse of the on-disk
`tensorPouSobolevHsNorm_zero_le_tensorL2Norm`: the global metric `L²` norm of a smooth
compactly-supported section is controlled by its order-`0` partition-of-unity chart-Sobolev
norm (the partition of unity sums to one, so the chart-`H⁰` norm recovers the full `L²` norm up
to the bounded metric-density factor on the compact manifold).  It is proved sorry-free, by
composing the on-disk reverse fibre-norm component bound
`tensorL2Norm_sq_le_const_mul_sum_componentL2Norm_sq` with the reverse measure-bridge comparison
`exists_sum_componentL2Norm_sq_le_tensorPouSobolevHsNormSq_zero` (itself proved here from the
reverse change-of-variables bridge `eLpNorm_riemannianMeasure_le_const_mul_eLpNorm_chartPushedRaw`). -/

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle
open scoped Manifold ContDiff NNReal ENNReal Topology BigOperators
open DifferentialGeometry
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Sobolev.Tensor
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [BoundarylessManifold I M]
      [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

section RawConnLapOrderDrop

open MeasureTheory
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Sobolev.Tensor
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

/-- **The per-chart inner-sum order-drop for the rough connection Laplacian (the genuine atomic
analytic primitive).**

For a closed Riemannian manifold and ranks `(r, s)`, there is a non-negative constant `C` such
that, for every smooth compactly-supported `(r, s)`-tensor section `T` and every chart base point
`α : M`, the chart-`α` order-`k` Hilbert-Schmidt partition-of-unity-weighted summand of
`Δ_∇ T = rawTensorConnLapSmooth g r s T` is bounded by `ofReal C` times the chart-`α`
order-`(k + 1)` summand of `T`:
```
∑_{IJ} ∑_{j ≤ 2k} ∑_{bIdx} ∫_{ChTE α} ρ_α · |D^j (raw_{IJ}(Δ_∇ T))(bIdx)|²
  ≤ ofReal C · ∑_{IJ} ∑_{j ≤ 2(k+1)} ∑_{bIdx} ∫_{ChTE α} ρ_α · |D^j (raw_{IJ}(T))(bIdx)|² .
```
The constant `C` is uniform in `(T, α)`.

This is the genuine analytic single-step rough-Laplacian chart-Sobolev order-dropping content,
localised per chart.  The rough Laplacian `Δ_∇` is the frame trace of the second covariant
derivative (`rawTensorConnLap_eq_frame_trace_secondCovDeriv`); in chart-Euclidean coordinates its
raw `(Idx, Jdx)`-component is a finite linear combination of *second* Euclidean partials of the raw
components of `T` with smooth (volume-weighted inverse-Gram) coefficients plus a lower-order
correction (`tensorChartComponentRaw_rawTensorConnLap_eq_chart_α_coord_formula`).  An order-`j`
(`j ≤ 2k`) Fréchet derivative of such a component is therefore dominated by order-`(j + 2) ≤
2(k + 1)` Fréchet derivatives of the raw components of `T` (the second-order operator costs exactly
two Fréchet, hence one `tensorPouSobolevHsNorm`-order); the smooth coefficients are uniformly bounded
on the compact chart image of the partition-of-unity support.  This is the exact rough-Laplacian
analogue of the per-chart bound underlying `exists_covGrad_tensorPouSobolevHsNorm_le`, tight at `+1`
order.  Its body is `sorry`: it carries no spectral nonlinearity and no Weyl dependence. -/
theorem exists_rawConnLapSmooth_tensorPouSobolevHsNorm_le_perChart
    (g : SmoothRiemannianMetric I M) (r s k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (T : Integral.L2.SmoothCcTensor g r s) (α : M),
        (∑ IJ : (Fin r → Fin (Module.finrank ℝ E)) ×
              (Fin s → Fin (Module.finrank ℝ E)),
            ∑ j ∈ Finset.range (2 * k + 1),
              ∑ bIdx : Fin j → Fin (Module.finrank ℝ E),
                ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
                  ENNReal.ofReal
                    (((chartAtlasPOU I M α : M → ℝ)
                        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
                      |(iteratedFDeriv ℝ j
                            (tensorChartComponentRaw (I := I) (M := M) g r s
                                (rawTensorConnLapSmooth (I := I) g r s T) α IJ.1 IJ.2
                              ∘ (extChartAt I α).symm
                              ∘ (toEuclidean (E := E)).symm)
                            y)
                          (fun i => EuclideanSpace.basisFun
                            (Fin (Module.finrank ℝ E)) ℝ (bIdx i))| ^ 2)
                  ∂(volume : Measure EuclN)) ≤
          ENNReal.ofReal C *
            (∑ IJ : (Fin r → Fin (Module.finrank ℝ E)) ×
                  (Fin s → Fin (Module.finrank ℝ E)),
              ∑ j ∈ Finset.range (2 * (k + 1) + 1),
                ∑ bIdx : Fin j → Fin (Module.finrank ℝ E),
                  ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
                    ENNReal.ofReal
                      (((chartAtlasPOU I M α : M → ℝ)
                          ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
                        |(iteratedFDeriv ℝ j
                              (tensorChartComponentRaw (I := I) (M := M) g r s T α IJ.1 IJ.2
                                ∘ (extChartAt I α).symm
                                ∘ (toEuclidean (E := E)).symm)
                              y)
                            (fun i => EuclideanSpace.basisFun
                              (Fin (Module.finrank ℝ E)) ℝ (bIdx i))| ^ 2)
                    ∂(volume : Measure EuclN)) :=
  sorry

/-- **The tight single-step order-dropping `ℝ≥0∞` chart-Sobolev norm bound for the rough
connection Laplacian (the genuine analytic primitive).**

For a closed Riemannian manifold and ranks `(r, s)`, there is a non-negative constant `C` such
that for every smooth compactly-supported `(r, s)`-tensor section `T`,
```
tensorPouSobolevHsNorm g k (Δ_∇ T) ≤ ENNReal.ofReal C · tensorPouSobolevHsNorm g (k + 1) T ,
```
where `Δ_∇ = rawTensorConnLapSmooth g r s`.  This is the `ℝ≥0∞`-level (`tensorPouSobolevHsNorm`)
form of the tight single-step bound: the rough Laplacian is the frame trace of the second
covariant derivative (`rawTensorConnLap_eq_frame_trace_secondCovDeriv`), hence a single
second-order operator `H^{2(k+1)} → H^{2k}`, losing exactly **one** `toHs`-order.  It is the
rough-Laplacian counterpart of `exists_covGrad_tensorPouSobolevHsNorm_le`, tight at `+1` order.

It is assembled from the per-chart order-drop
`exists_rawConnLapSmooth_tensorPouSobolevHsNorm_le_perChart`: unfolding both
`tensorPouSobolevHsNorm`s via `tensorPouSobolevHsNorm_eq`, the per-chart inner-summand bound is
summed over the chart base points (`ENNReal.tsum_le_tsum` and `ENNReal.tsum_mul_left`), and the
outer `^(1/2)` is distributed (`ENNReal.mul_rpow_of_nonneg`), turning `ofReal C` into
`ofReal (√C)`.  The completion-norm forms `exists_rawConnLapSmooth_toHs_le_toHs_succ` and
`exists_rawConnLapIter_toHs_le_toHs` are proved on top of it via `tensorPouSobolevHilbert_norm_eq`. -/
theorem exists_rawConnLapSmooth_tensorPouSobolevHsNorm_le
    (g : SmoothRiemannianMetric I M) (r s k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ T : Integral.L2.SmoothCcTensor g r s,
        tensorPouSobolevHsNorm (I := I) (M := M) g k
            (rawTensorConnLapSmooth (I := I) g r s T) ≤
          ENNReal.ofReal C *
            tensorPouSobolevHsNorm (I := I) (M := M) g (k + 1) T := by
  classical
  obtain ⟨C, hC_nn, hC⟩ :=
    exists_rawConnLapSmooth_tensorPouSobolevHsNorm_le_perChart (I := I) (M := M) g r s k
  refine ⟨Real.sqrt C, Real.sqrt_nonneg _, fun T => ?_⟩
  rw [tensorPouSobolevHsNorm_eq, tensorPouSobolevHsNorm_eq]
  set lhsInner : M → ℝ≥0∞ := fun α =>
    ∑ IJ : (Fin r → Fin (Module.finrank ℝ E)) ×
        (Fin s → Fin (Module.finrank ℝ E)),
      ∑ j ∈ Finset.range (2 * k + 1),
        ∑ bIdx : Fin j → Fin (Module.finrank ℝ E),
          ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
            ENNReal.ofReal
              (((chartAtlasPOU I M α : M → ℝ)
                  ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
                |(iteratedFDeriv ℝ j
                      (tensorChartComponentRaw (I := I) (M := M) g r s
                          (rawTensorConnLapSmooth (I := I) g r s T) α IJ.1 IJ.2
                        ∘ (extChartAt I α).symm
                        ∘ (toEuclidean (E := E)).symm)
                      y)
                    (fun i => EuclideanSpace.basisFun
                      (Fin (Module.finrank ℝ E)) ℝ (bIdx i))| ^ 2)
            ∂(volume : Measure EuclN) with hlhsInner_def
  set rhsInner : M → ℝ≥0∞ := fun α =>
    ∑ IJ : (Fin r → Fin (Module.finrank ℝ E)) ×
        (Fin s → Fin (Module.finrank ℝ E)),
      ∑ j ∈ Finset.range (2 * (k + 1) + 1),
        ∑ bIdx : Fin j → Fin (Module.finrank ℝ E),
          ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
            ENNReal.ofReal
              (((chartAtlasPOU I M α : M → ℝ)
                  ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
                |(iteratedFDeriv ℝ j
                      (tensorChartComponentRaw (I := I) (M := M) g r s T α IJ.1 IJ.2
                        ∘ (extChartAt I α).symm
                        ∘ (toEuclidean (E := E)).symm)
                      y)
                    (fun i => EuclideanSpace.basisFun
                      (Fin (Module.finrank ℝ E)) ℝ (bIdx i))| ^ 2)
            ∂(volume : Measure EuclN) with hrhsInner_def
  have h_main : (∑' α : M, lhsInner α) ≤ ENNReal.ofReal C * ∑' α : M, rhsInner α := by
    rw [← ENNReal.tsum_mul_left]
    refine ENNReal.tsum_le_tsum (fun α => ?_)
    rw [hlhsInner_def, hrhsInner_def]
    exact hC T α
  have h_rpow : (∑' α : M, lhsInner α) ^ (1 / 2 : ℝ) ≤
      (ENNReal.ofReal C * ∑' α : M, rhsInner α) ^ (1 / 2 : ℝ) :=
    ENNReal.rpow_le_rpow h_main (by norm_num)
  calc (∑' α : M, lhsInner α) ^ (1 / 2 : ℝ)
      ≤ (ENNReal.ofReal C * ∑' α : M, rhsInner α) ^ (1 / 2 : ℝ) := h_rpow
    _ = ENNReal.ofReal (Real.sqrt C) * (∑' α : M, rhsInner α) ^ (1 / 2 : ℝ) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2)]
        congr 1
        rw [ENNReal.ofReal_rpow_of_nonneg hC_nn (by norm_num : (0 : ℝ) ≤ 1 / 2),
          ← Real.sqrt_eq_rpow]

end RawConnLapOrderDrop

/-- **The tight single-step order-dropping completion-norm bound for the rough connection
Laplacian (the genuine atomic elliptic-boundedness primitive).**

For a closed Riemannian manifold and an order `k`, there is a non-negative constant `C` such
that for every smooth compactly-supported `(0, 2)`-tensor section `T`,
```
‖(Δ_∇ T).toHs k‖ ≤ C · ‖T.toHs (k + 1)‖ ,
```
where `Δ_∇ = rawTensorConnLapSmooth g 0 2`.  This is the intrinsic `H^{2k}(Δ_∇ T) ≤
C · H^{2(k+1)}(T)` order-dropping inequality: the rough Laplacian is the frame trace of the
second covariant derivative (`rawTensorConnLap_eq_frame_trace_secondCovDeriv`), hence a *single*
second-order operator, so it loses exactly **one** `toHs`-order (`= 2` derivatives) — the tight
count, as opposed to the `+2` a naive `covGrad ∘ covGrad` composition would charge.  It is proved
on top of the `ℝ≥0∞`-level primitive `exists_rawConnLapSmooth_tensorPouSobolevHsNorm_le` via
`tensorPouSobolevHilbert_norm_eq`, exactly as `covGrad_toHs_norm_le` is built from
`exists_covGrad_tensorPouSobolevHsNorm_le`. -/
theorem exists_rawConnLapSmooth_toHs_le_toHs_succ
    (g : SmoothRiemannianMetric I M) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ T : Integral.L2.SmoothCcTensor g 0 2,
        ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g) (r := 0) (s := 2) k
            (rawTensorConnLapSmooth (I := I) g 0 2 T)‖ ≤
          C * ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g) (r := 0) (s := 2) (k + 1) T‖ := by
  obtain ⟨C, hC_nn, hC⟩ :=
    exists_rawConnLapSmooth_tensorPouSobolevHsNorm_le (I := I) (M := M) g 0 2 k
  refine ⟨C, hC_nn, fun T => ?_⟩
  rw [tensorPouSobolevHilbert_norm_eq, tensorPouSobolevHilbert_norm_eq]
  have hle := hC T
  have h_rhs_ne_top :
      ENNReal.ofReal C *
          tensorPouSobolevHsNorm (I := I) (M := M) g (k + 1) T ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (tensorPouSobolevHsNorm_lt_top (I := I) (M := M) g (k + 1) T).ne
  calc (tensorPouSobolevHsNorm (I := I) (M := M) g k
          (rawTensorConnLapSmooth (I := I) g 0 2 T)).toReal
      ≤ (ENNReal.ofReal C *
          tensorPouSobolevHsNorm (I := I) (M := M) g (k + 1) T).toReal :=
        ENNReal.toReal_mono h_rhs_ne_top hle
    _ = (ENNReal.ofReal C).toReal *
          (tensorPouSobolevHsNorm (I := I) (M := M) g (k + 1) T).toReal := by
        rw [ENNReal.toReal_mul]
    _ = C * (tensorPouSobolevHsNorm (I := I) (M := M) g (k + 1) T).toReal := by
        rw [ENNReal.toReal_ofReal hC_nn]

/-- **The iterated order-dropping completion-norm bound for the rough connection Laplacian.**

For each iteration count `i` and each order `k` there is a non-negative constant `C` such that
for every smooth compactly-supported `(0, 2)`-tensor section `T`,
```
‖(Δ_∇^i T).toHs k‖ ≤ C · ‖T.toHs (k + i)‖ ,
```
where `Δ_∇^i = rawTensorConnLapIter g 0 2 i`.  The proof iterates the tight single-step bound
`exists_rawConnLapSmooth_toHs_le_toHs_succ` exactly `i` times (peeling one `Δ_∇` at each step
and raising the inner order by one), the constant being the product of the single-step
constants.  This is the rough-Laplacian mirror of `iteratedCovGrad_toHs_norm_le`. -/
theorem exists_rawConnLapIter_toHs_le_toHs
    (g : SmoothRiemannianMetric I M) (i k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (T : Integral.L2.SmoothCcTensor g 0 2),
        ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g) (r := 0) (s := 2) k
            (rawTensorConnLapIter (I := I) g 0 2 i T)‖ ≤
          C * ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g) (r := 0) (s := 2) (k + i) T‖ := by
  induction i generalizing k with
  | zero =>
      refine ⟨1, zero_le_one, fun T => ?_⟩
      simp only [rawTensorConnLapIter_zero, Nat.add_zero, one_mul, le_refl]
  | succ i ih =>
      obtain ⟨Ci, hCi_nn, hCi⟩ := ih (k + 1)
      obtain ⟨C1, hC1_nn, hC1⟩ := exists_rawConnLapSmooth_toHs_le_toHs_succ (I := I) g k
      refine ⟨C1 * Ci, mul_nonneg hC1_nn hCi_nn, fun T => ?_⟩
      -- One peel: `Δ_∇^{i+1} T = Δ_∇ (Δ_∇^i T)`, then single-step at order `k` and `ih` at
      -- order `k+1`.
      have hpeel : rawTensorConnLapIter (I := I) g 0 2 (i + 1) T
          = rawTensorConnLapSmooth (I := I) g 0 2 (rawTensorConnLapIter (I := I) g 0 2 i T) := by
        rw [rawTensorConnLapIter_succ]
      rw [hpeel]
      have hstep := hC1 (rawTensorConnLapIter (I := I) g 0 2 i T)
      have hih := hCi T
      have hord : k + 1 + i = k + (i + 1) := by ring
      rw [hord] at hih
      refine le_trans hstep ?_
      calc C1 * ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g) (r := 0) (s := 2) (k + 1)
              (rawTensorConnLapIter (I := I) g 0 2 i T)‖
          ≤ C1 * (Ci * ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g) (r := 0) (s := 2)
              (k + (i + 1)) T‖) := mul_le_mul_of_nonneg_left hih hC1_nn
        _ = C1 * Ci * ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g) (r := 0) (s := 2)
              (k + (i + 1)) T‖ := by ring

/-- **Monotonicity of the order-`k` chart-Sobolev completion norm in the order `k`.**

For `m ≤ n`, the order-`m` chart-Sobolev (`toHs`) norm is dominated by the order-`n` one:
`‖T.toHs m‖ ≤ ‖T.toHs n‖`.  This is the completion-norm reflection of the monotonicity
`tensorPouSobolevHsNorm_le_succ` of the partition-of-unity chart-Sobolev `ℝ≥0∞`-norm in the
order, transported through `tensorPouSobolevHilbert_norm_eq`. -/
theorem toHs_norm_mono (g : SmoothRiemannianMetric I M) {r s : ℕ} {m n : ℕ} (hmn : m ≤ n)
    (T : Integral.L2.SmoothCcTensor g r s) :
    ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g) (r := r) (s := s) m T‖ ≤
      ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g) (r := r) (s := s) n T‖ := by
  rw [tensorPouSobolevHilbert_norm_eq, tensorPouSobolevHilbert_norm_eq]
  refine ENNReal.toReal_mono (tensorPouSobolevHsNorm_lt_top (I := I) (M := M) g n T).ne ?_
  -- Monotone in the order via the successor step, by induction on the gap `n - m`.
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hmn
  clear hmn
  induction d with
  | zero => simp
  | succ d ihd =>
      refine le_trans ihd ?_
      have : m + d + 1 = m + (d + 1) := by ring
      rw [← this]
      exact tensorPouSobolevHsNorm_le_succ (I := I) (M := M) g (m + d) T

/-- The intrinsic order-`k` chart-Sobolev completion embedding `SmoothCcTensor.toHs` is additive:
`(R₁ + R₂).toHs k = R₁.toHs k + R₂.toHs k`.  Both sides are the completion coercion of the
`SmoothCcTensorHs`-wrapper addition (`UniformSpace.Completion.coe_add`). -/
theorem SmoothCcTensor.toHs_add {g : SmoothRiemannianMetric I M} {r s : ℕ} (k : ℕ)
    (R₁ R₂ : Integral.L2.SmoothCcTensor g r s) :
    IntrinsicSobolev.SmoothCcTensor.toHs (g := g) (r := r) (s := s) k (R₁ + R₂)
      = IntrinsicSobolev.SmoothCcTensor.toHs (g := g) (r := r) (s := s) k R₁
        + IntrinsicSobolev.SmoothCcTensor.toHs (g := g) (r := r) (s := s) k R₂ := by
  unfold IntrinsicSobolev.SmoothCcTensor.toHs
  rw [← UniformSpace.Completion.coe_add]
  rfl

/-- The intrinsic order-`k` chart-Sobolev completion embedding `SmoothCcTensor.toHs` commutes with
subtraction: `(R₁ − R₂).toHs k = R₁.toHs k − R₂.toHs k` (`UniformSpace.Completion.coe_sub`). -/
theorem SmoothCcTensor.toHs_sub {g : SmoothRiemannianMetric I M} {r s : ℕ} (k : ℕ)
    (R₁ R₂ : Integral.L2.SmoothCcTensor g r s) :
    IntrinsicSobolev.SmoothCcTensor.toHs (g := g) (r := r) (s := s) k (R₁ - R₂)
      = IntrinsicSobolev.SmoothCcTensor.toHs (g := g) (r := r) (s := s) k R₁
        - IntrinsicSobolev.SmoothCcTensor.toHs (g := g) (r := r) (s := s) k R₂ := by
  unfold IntrinsicSobolev.SmoothCcTensor.toHs
  rw [← UniformSpace.Completion.coe_sub]
  rfl

section LinearityT2

open DifferentialGeometry.Integral.Connection Bundle Tensor0SBundle

set_option backward.isDefEq.respectTransparency false

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

/-- The unconditional smoothness witness of the total-space form of `rawTensorConnLap` applied to a
bundled smooth section `T : SmoothCcTensor g r s`. -/
private lemma rawConnLap_smooth_witness (g : SmoothRiemannianMetric I M) {r s : ℕ}
    (T : Integral.L2.SmoothCcTensor g r s) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun y : M => Bundle.TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) y
        (rawTensorConnLap (I := I) g r s (fun z : M => T.toSection z) y)) :=
  rawTensorConnLap_contMDiff (I := I) g r s
    (fun z : M => T.toSection z) T.toSection.contMDiff_toFun

/-- **Subtraction-linearity of the bundled rough connection Laplacian on `SmoothCcTensor`
(an atomic algebraic linearity primitive).**

`Δ_∇ (T − T') = Δ_∇ T − Δ_∇ T'`, where `Δ_∇ = rawTensorConnLapSmooth g r s`.  The rough
Laplacian is the section-level packaging of the fibrewise-linear pointwise operator
`rawTensorConnLap`, which is additive (`tensorConnLaplacian_of_contMDiff_add`) and `smul`-linear
(`tensorConnLaplacian_of_contMDiff_smul`); hence so is its bundled form.  Writing
`T − T' = T + (-1) • T'` and reducing by `SmoothCcTensor.ext`/`ContMDiffSection.ext` to the
pointwise `.toSection`, the bundled additivity and scalar-homogeneity (mirroring the on-disk
`connLaplacianL2Action.map_add'`/`map_smul'`) assemble the subtraction identity.  This splits off
the linear part of the second-order DeTurck right-hand side. -/
theorem rawTensorConnLapSmooth_sub (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T T' : Integral.L2.SmoothCcTensor g r s) :
    rawTensorConnLapSmooth (I := I) g r s (T - T')
      = rawTensorConnLapSmooth (I := I) g r s T - rawTensorConnLapSmooth (I := I) g r s T' := by
  have hsub_eq : (T - T' : Integral.L2.SmoothCcTensor g r s) = T + (-1 : ℝ) • T' := by
    rw [neg_one_smul, ← sub_eq_add_neg]
  have h_smul : rawTensorConnLapSmooth (I := I) g r s ((-1 : ℝ) • T')
      = (-1 : ℝ) • rawTensorConnLapSmooth (I := I) g r s T' := by
    refine Integral.L2.SmoothCcTensor.ext ?_
    refine ContMDiffSection.ext (fun x => ?_)
    have hsmul := tensorConnLaplacian_of_contMDiff_smul (I := I) g r s (-1 : ℝ) T'
      (rawConnLap_smooth_witness (I := I) g T')
      (rawConnLap_smooth_witness (I := I) g ((-1 : ℝ) • T')) x
    have hLHS : (rawTensorConnLapSmooth (I := I) g r s ((-1 : ℝ) • T')).toSection x =
        (tensorConnLaplacian_of_contMDiff (I := I) g r s ((-1 : ℝ) • T')
          (rawConnLap_smooth_witness (I := I) g ((-1 : ℝ) • T'))).toSection x := rfl
    have hRHS : (rawTensorConnLapSmooth (I := I) g r s T').toSection x =
        (tensorConnLaplacian_of_contMDiff (I := I) g r s T'
          (rawConnLap_smooth_witness (I := I) g T')).toSection x := rfl
    rw [hLHS, Integral.L2.SmoothCcTensor.toSection_smul, ContMDiffSection.coe_smul,
      Pi.smul_apply, hRHS, hsmul]
  have h_add : rawTensorConnLapSmooth (I := I) g r s (T + (-1 : ℝ) • T')
      = rawTensorConnLapSmooth (I := I) g r s T
        + rawTensorConnLapSmooth (I := I) g r s ((-1 : ℝ) • T') := by
    refine Integral.L2.SmoothCcTensor.ext ?_
    refine ContMDiffSection.ext (fun x => ?_)
    have hsum := tensorConnLaplacian_of_contMDiff_add (I := I) g r s T ((-1 : ℝ) • T')
      (rawConnLap_smooth_witness (I := I) g T)
      (rawConnLap_smooth_witness (I := I) g ((-1 : ℝ) • T'))
      (rawConnLap_smooth_witness (I := I) g (T + (-1 : ℝ) • T')) x
    have hLHS : (rawTensorConnLapSmooth (I := I) g r s (T + (-1 : ℝ) • T')).toSection x =
        (tensorConnLaplacian_of_contMDiff (I := I) g r s (T + (-1 : ℝ) • T')
          (rawConnLap_smooth_witness (I := I) g (T + (-1 : ℝ) • T'))).toSection x := rfl
    have hRHS₁ : (rawTensorConnLapSmooth (I := I) g r s T).toSection x =
        (tensorConnLaplacian_of_contMDiff (I := I) g r s T
          (rawConnLap_smooth_witness (I := I) g T)).toSection x := rfl
    have hRHS₂ : (rawTensorConnLapSmooth (I := I) g r s ((-1 : ℝ) • T')).toSection x =
        (tensorConnLaplacian_of_contMDiff (I := I) g r s ((-1 : ℝ) • T')
          (rawConnLap_smooth_witness (I := I) g ((-1 : ℝ) • T'))).toSection x := rfl
    rw [hLHS, Integral.L2.SmoothCcTensor.toSection_add, ContMDiffSection.coe_add,
      Pi.add_apply, hRHS₁, hRHS₂, hsum]
  rw [hsub_eq, h_add, h_smul, neg_one_smul, ← sub_eq_add_neg]

end LinearityT2

section ReverseOrderZeroBridge

open MeasureTheory
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Sobolev.Tensor
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

/-- For a real-valued function the squared `L²` seminorm equals the `lintegral` of the squared
enorm. -/
private lemma sq_eLpNorm_two_eq_lintegral_enorm_sq'
    {β : Type*} [MeasurableSpace β] (μ : Measure β) (f : β → ℝ) :
    (eLpNorm f 2 μ) ^ 2 = ∫⁻ x, (‖f x‖ₑ : ℝ≥0∞) ^ 2 ∂μ := by
  classical
  have h2_ne_zero : (2 : ℝ≥0∞) ≠ 0 := by norm_num
  have h2_ne_top : (2 : ℝ≥0∞) ≠ (⊤ : ℝ≥0∞) := by norm_num
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (μ := μ) h2_ne_zero h2_ne_top]
  have h2_toReal : ((2 : ℝ≥0∞)).toReal = 2 := by show ENNReal.toReal 2 = 2; rfl
  rw [h2_toReal]
  have h_inner_eq : ∫⁻ x, (‖f x‖ₑ : ℝ≥0∞) ^ (2 : ℝ) ∂μ =
      ∫⁻ x, (‖f x‖ₑ : ℝ≥0∞) ^ 2 ∂μ := by
    refine lintegral_congr_ae ?_
    filter_upwards with x
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, ENNReal.rpow_natCast]
  rw [h_inner_eq, ← ENNReal.rpow_natCast _ 2, ← ENNReal.rpow_mul]
  norm_num

/-- The order-`0` chart-Sobolev summand integral for chart `α` and component `(Idx, Jdx)` equals
the squared chart-Euclidean `L²` norm of the chart-push of the square-root-weighted raw component
`√ρ_α · raw_{IJ}`.  This is the integrand identity underlying the order-`0` reverse comparison. -/
private lemma hsNorm_zero_summand_eq_sq_eLpNorm_chartPushedSqrtPou
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : Integral.L2.SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    (basisIdx : Fin 0 → Fin (Module.finrank ℝ E)) :
    (∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
        ENNReal.ofReal
          (((chartAtlasPOU I M α : M → ℝ)
              ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
            |(iteratedFDeriv ℝ 0
                  (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
                    ∘ (extChartAt I α).symm
                    ∘ (toEuclidean (E := E)).symm)
                  y)
                (fun i => EuclideanSpace.basisFun
                  (Fin (Module.finrank ℝ E)) ℝ (basisIdx i))| ^ 2)
        ∂(volume : Measure EuclN)) =
      (eLpNorm
          (chartPushedRaw I α
            (tensorChartComponentSqrtPou (I := I) (M := M) g r s T α Idx Jdx)) 2
          ((volume : Measure EuclN).restrict
            (chartTargetEuclid (I := I) (M := M) α))) ^ 2 := by
  classical
  rw [sq_eLpNorm_two_eq_lintegral_enorm_sq']
  rw [← MeasureTheory.lintegral_indicator
        (chartTargetEuclid_isOpen (I := I) (M := M) α).measurableSet,
      ← MeasureTheory.lintegral_indicator
        (chartTargetEuclid_isOpen (I := I) (M := M) α).measurableSet]
  refine MeasureTheory.lintegral_congr (fun y => ?_)
  by_cases hy : y ∈ chartTargetEuclid (I := I) (M := M) α
  · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy]
    set b : M := (extChartAt I α).symm ((toEuclidean (E := E)).symm y) with hb_def
    have hraw_eval :
        (iteratedFDeriv ℝ 0
              (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
                ∘ (extChartAt I α).symm
                ∘ (toEuclidean (E := E)).symm) y)
            (fun i => EuclideanSpace.basisFun
              (Fin (Module.finrank ℝ E)) ℝ (basisIdx i)) =
          tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx b := by
      rw [iteratedFDeriv_zero_apply]; rfl
    have hpush :
        chartPushedRaw I α
            (tensorChartComponentSqrtPou (I := I) (M := M) g r s T α Idx Jdx) y =
          tensorChartComponentSqrtPou (I := I) (M := M) g r s T α Idx Jdx b :=
      chartPushedRaw_apply_of_mem (I := I) (M := M) α _ hy
    rw [hraw_eval, hpush]
    have hw_sq :
        (tensorChartComponentSqrtPou (I := I) (M := M) g r s T α Idx Jdx b) ^ 2 =
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) b *
            (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx b) ^ 2 :=
      tensorChartComponentSqrtPou_sq (I := I) (M := M) g r s T α Idx Jdx b
    rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _) 2]
    congr 1
    rw [sq_abs, sq_abs, hw_sq]
  · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy]

/-- The support of `√ρ_α` equals the support of `ρ_α`. -/
private lemma support_sqrt_pou_eq' (α : M) :
    Function.support
        (fun b : M => Real.sqrt
          (((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) b)) =
      Function.support (((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)) := by
  ext b
  simp only [Function.mem_support, ne_eq, Real.sqrt_eq_zero']
  constructor
  · intro hb hcontra
    exact hb (by rw [hcontra])
  · intro hb hle
    have hρ_nn : 0 ≤ ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) b :=
      (chartAtlasPOU I M).nonneg α b
    exact hb (le_antisymm hle hρ_nn)

/-- The square-root-weighted raw component is supported in `tsupport ρ_α`. -/
private lemma tsupport_sqrtPou_subset
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : Integral.L2.SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    tsupport (tensorChartComponentSqrtPou (I := I) (M := M) g r s T α Idx Jdx) ⊆
      tsupport (((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)) := by
  have h_mul : tsupport (tensorChartComponentSqrtPou (I := I) (M := M)
        g r s T α Idx Jdx) ⊆
      tsupport (fun b : M => Real.sqrt
        (((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) b)) :=
    tsupport_mul_subset_left
      (f := fun b : M => Real.sqrt
        (((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) b))
      (g := tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx)
  refine h_mul.trans ?_
  unfold tsupport
  rw [support_sqrt_pou_eq' (I := I) (M := M) α]

/-- The square-root-weighted raw component is globally continuous on `M`. -/
private lemma continuous_sqrtPou
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : Integral.L2.SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    Continuous
      (tensorChartComponentSqrtPou (I := I) (M := M) g r s T α Idx Jdx) := by
  classical
  have hSqrt_cont : Continuous
      (fun y : M => Real.sqrt
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) y)) :=
    Real.continuous_sqrt.comp
      (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯).contMDiff.continuous
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx_chart : x ∈ (chartAt H α).source
  · have hRaw_on := tensorChartComponentRaw_contMDiffOn_chart_source
      (I := I) (M := M) g r s T α Idx Jdx
    have hRaw_at : ContinuousAt
        (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx) x :=
      ((hRaw_on.contMDiffAt
        (IsOpen.mem_nhds (chartAt H α).open_source hx_chart)).continuousAt)
    exact (hSqrt_cont.continuousAt).mul hRaw_at
  · have hsupp_sub :
        tsupport (tensorChartComponentSqrtPou (I := I) (M := M)
            g r s T α Idx Jdx) ⊆ (chartAt H α).source :=
      (tsupport_sqrtPou_subset (I := I) (M := M)
        g r s T α Idx Jdx).trans
        (chartAtlasPOU_isSubordinate I M α)
    have hx_notin : x ∉ tsupport (tensorChartComponentSqrtPou (I := I) (M := M)
        g r s T α Idx Jdx) := fun h => hx_chart (hsupp_sub h)
    refine (continuousAt_const (y := (0 : ℝ))).congr ?_
    have hopen : IsOpen
        (tsupport (tensorChartComponentSqrtPou (I := I) (M := M)
          g r s T α Idx Jdx))ᶜ :=
      isClosed_tsupport _ |>.isOpen_compl
    filter_upwards [hopen.mem_nhds hx_notin] with y hy
    have hy_notsupp : y ∉ Function.support
        (tensorChartComponentSqrtPou (I := I) (M := M)
          g r s T α Idx Jdx) := fun h_in => hy (subset_tsupport _ h_in)
    have hzero : tensorChartComponentSqrtPou (I := I) (M := M)
        g r s T α Idx Jdx y = 0 := by
      by_contra hne; exact hy_notsupp hne
    exact hzero.symm

/-- The square-root-weighted raw component is measurable. -/
private lemma measurable_sqrtPou
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : Integral.L2.SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    Measurable
      (tensorChartComponentSqrtPou (I := I) (M := M) g r s T α Idx Jdx) :=
  (continuous_sqrtPou (I := I) (M := M) g r s T α Idx Jdx).measurable

/-- **The per-chart-and-component reverse comparison.** For every chart `α` there is a
non-negative constant `C_α` so that for every `T`, `(Idx, Jdx)`, the squared intrinsic metric
`L²` norm of `ρ_α · raw_{IJ}` is bounded by `ofReal C_α` times the order-`0` chart-Sobolev summand
integral (at the `ℝ≥0∞` level). -/
private lemma sq_eLpNorm_scalar_le_const_mul_hsNorm_zero_summand
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (T : Integral.L2.SmoothCcTensor g r s)
        (Idx : Fin r → Fin (Module.finrank ℝ E))
        (Jdx : Fin s → Fin (Module.finrank ℝ E)),
        (eLpNorm (tensorChartComponentScalar (I := I) (M := M) g r s T α Idx Jdx) 2
              (riemannianVolumeMeasure (I := I) (M := M) g)) ^ 2 ≤
          ENNReal.ofReal C *
            (∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
                ENNReal.ofReal
                  (((chartAtlasPOU I M α : M → ℝ)
                      ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
                    |(iteratedFDeriv ℝ 0
                          (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
                            ∘ (extChartAt I α).symm
                            ∘ (toEuclidean (E := E)).symm)
                          y)
                        (fun i => EuclideanSpace.basisFun
                          (Fin (Module.finrank ℝ E)) ℝ
                          ((default : Fin 0 → Fin (Module.finrank ℝ E)) i))| ^ 2)
                ∂(volume : Measure EuclN)) := by
  classical
  set Kα : Set M := tsupport ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) with hKα_def
  have hKα_compact : IsCompact Kα := (isClosed_tsupport _).isCompact
  have hKα_sub : Kα ⊆ (chartAt H α).source := chartAtlasPOU_isSubordinate I M α
  obtain ⟨Cbr, hCbr_pos, hCbr⟩ :=
    eLpNorm_riemannianMeasure_le_const_mul_eLpNorm_chartPushedRaw_uniform_of_subset
      (I := I) (M := M) g α hKα_compact hKα_sub (by norm_num : (1 : ℝ≥0∞) ≤ 2)
      (by decide : (2 : ℝ≥0∞) ≠ ⊤)
  refine ⟨Cbr ^ 2, sq_nonneg _, ?_⟩
  intro T Idx Jdx
  set w : M → ℝ := tensorChartComponentSqrtPou (I := I) (M := M) g r s T α Idx Jdx with hw_def
  have hw_meas : Measurable w :=
    measurable_sqrtPou (I := I) (M := M) g r s T α Idx Jdx
  have hw_supp : tsupport w ⊆ Kα :=
    tsupport_sqrtPou_subset (I := I) (M := M) g r s T α Idx Jdx
  -- Pointwise: `|Scalar = ρ·raw| ≤ |w = √ρ·raw|`, hence `eLpNorm Scalar ≤ eLpNorm w`.
  have h_ptwise : ∀ x : M,
      ‖tensorChartComponentScalar (I := I) (M := M) g r s T α Idx Jdx x‖ ≤ ‖w x‖ := by
    intro x
    have hρ_nn : 0 ≤ ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x :=
      (chartAtlasPOU I M).nonneg α x
    have hρ_le_one : ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x ≤ 1 :=
      (chartAtlasPOU I M).le_one α x
    have hsqrt_nn : 0 ≤ Real.sqrt (((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) :=
      Real.sqrt_nonneg _
    have hsqrt_le_one :
        Real.sqrt (((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ≤ 1 := by
      rw [show (1 : ℝ) = Real.sqrt 1 from (Real.sqrt_one).symm]
      exact Real.sqrt_le_sqrt hρ_le_one
    have hρ_eq : ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x =
        Real.sqrt (((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) *
          Real.sqrt (((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) :=
      (Real.mul_self_sqrt hρ_nn).symm
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    rw [show tensorChartComponentScalar (I := I) (M := M) g r s T α Idx Jdx x =
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x *
            tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx x from rfl,
      hw_def, tensorChartComponentSqrtPou_apply]
    rw [abs_mul, abs_mul]
    refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
    rw [abs_of_nonneg hρ_nn, abs_of_nonneg hsqrt_nn]
    calc ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x
        = Real.sqrt (((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) *
            Real.sqrt (((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) := hρ_eq
      _ ≤ 1 * Real.sqrt (((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) :=
          mul_le_mul_of_nonneg_right hsqrt_le_one hsqrt_nn
      _ = Real.sqrt (((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) := one_mul _
  have h_scalar_le_w :
      eLpNorm (tensorChartComponentScalar (I := I) (M := M) g r s T α Idx Jdx) 2
          (riemannianVolumeMeasure (I := I) (M := M) g) ≤
        eLpNorm w 2 (riemannianVolumeMeasure (I := I) (M := M) g) :=
    eLpNorm_mono h_ptwise
  -- Reverse measure bridge for `w`.
  have h_bridge := hCbr (u := w) hw_meas hw_supp
  rw [show DifferentialGeometry.Integral.Measure.riemannianMeasure (I := I) g
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M)
        = DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure I M g
      from rfl] at h_bridge
  -- Chain at the `ℝ≥0∞` level.
  set lhsE : ℝ≥0∞ :=
    eLpNorm (tensorChartComponentScalar (I := I) (M := M) g r s T α Idx Jdx) 2
      (riemannianVolumeMeasure (I := I) (M := M) g) with hlhsE_def
  set chE : ℝ≥0∞ :=
    eLpNorm (chartPushedRaw I α w) 2
      ((volume : Measure EuclN).restrict (chartTargetEuclid (I := I) (M := M) α)) with hchE_def
  have h_lhsE_le : lhsE ≤ ENNReal.ofReal Cbr * chE :=
    le_trans h_scalar_le_w h_bridge
  have h_chE_sq :
      chE ^ 2 =
        ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
          ENNReal.ofReal
            (((chartAtlasPOU I M α : M → ℝ)
                ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
              |(iteratedFDeriv ℝ 0
                    (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
                      ∘ (extChartAt I α).symm
                      ∘ (toEuclidean (E := E)).symm)
                    y)
                  (fun i => EuclideanSpace.basisFun
                    (Fin (Module.finrank ℝ E)) ℝ
                    ((default : Fin 0 → Fin (Module.finrank ℝ E)) i))| ^ 2)
          ∂(volume : Measure EuclN) := by
    rw [hchE_def, hw_def,
      ← hsNorm_zero_summand_eq_sq_eLpNorm_chartPushedSqrtPou
          (I := I) (M := M) g r s T α Idx Jdx (default : Fin 0 → Fin (Module.finrank ℝ E))]
  rw [← h_chE_sq]
  calc lhsE ^ 2 ≤ (ENNReal.ofReal Cbr * chE) ^ 2 := pow_le_pow_left' h_lhsE_le 2
    _ = (ENNReal.ofReal Cbr) ^ 2 * chE ^ 2 := by rw [mul_pow]
    _ = ENNReal.ofReal (Cbr ^ 2) * chE ^ 2 := by rw [← ENNReal.ofReal_pow hCbr_pos.le]

/-- **The reverse measure-bridge comparison at chart-Sobolev order `0` (the genuine atomic
analytic primitive).**

For a closed Riemannian manifold and ranks `(r, s)` there is a non-negative constant `C` such
that for every smooth compactly-supported `(r, s)`-tensor section `T`, the finite double sum,
over the active charts `α ∈ chartAtlasPOU_finset` and the component multi-index pairs
`(Idx, Jdx)`, of the squared intrinsic metric `L²` norm of the partition-of-unity-weighted raw
chart-frame scalar component `tensorChartComponentScalar = ρ_α · raw_{IJ}` is controlled by the
squared order-`0` Hilbert-Schmidt partition-of-unity-weighted chart-Sobolev norm:
```
∑_{α} ∑_{IJ} ((eLpNorm (ρ_α · raw_{IJ}) 2 dVol_g).toReal)²
  ≤ C · (tensorPouSobolevHsNormSq g 0 T).toReal .
```
This is the genuine reverse change-of-variables (intrinsic Riemannian `L²` → chart-Euclidean
`L²`) comparison: the chart-frame raw component `raw_{IJ}` is the chart-`α`-frame coordinate of
the trivialised tensor, the partition-of-unity weight `ρ_α ≤ 1` so `|ρ_α · raw|² ≤ ρ_α · |raw|²`
matches the (first-power) weight of the order-`0` chart-Sobolev integrand, and the reverse
measure bridge `eLpNorm_riemannianMeasure_le_const_mul_eLpNorm_chartPushedRaw_uniform_of_subset`
on the compact chart image of the partition-of-unity support transfers the intrinsic `L²` norm to
the chart-Euclidean `L²` norm appearing in `tensorPouSobolevHsNormSq g 0`.

It is proved by composing the pointwise weight inequality `|ρ_α · raw|² ≤ ρ_α · |raw|² =
(√ρ_α · raw)²`, the reverse measure bridge, and the order-`0` chart-Sobolev integrand identity:
each chart-component intrinsic `L²` norm squared is dominated by the corresponding order-`0`
chart-Sobolev summand integral, uniformly over the finitely many active charts. -/
theorem exists_sum_componentL2Norm_sq_le_tensorPouSobolevHsNormSq_zero
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ T : Integral.L2.SmoothCcTensor g r s,
        (∑ α ∈ DifferentialGeometry.Integral.Measure.chartAtlasPOU_finset (I := I) (M := M),
            ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
              ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
                ((MeasureTheory.eLpNorm
                    (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentScalar
                      (I := I) (M := M) g r s T α Idx Jdx) 2
                    (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure
                      (I := I) (M := M) g)).toReal) ^ 2) ≤
          C * (tensorPouSobolevHsNormSq (I := I) (M := M) g 0 T).toReal := by
  classical
  set Sf : Finset M := DifferentialGeometry.Integral.Measure.chartAtlasPOU_finset
    (I := I) (M := M) with hSf_def
  -- A uniform constant: the finset-sum of the per-chart reverse-bridge constants.
  choose Cα hCα_nn hCα using fun α (_ : α ∈ Sf) =>
    sq_eLpNorm_scalar_le_const_mul_hsNorm_zero_summand (I := I) (M := M) (E := E) g r s α
  set Cmax : ℝ := ∑ α ∈ Sf.attach, Cα α.val α.property with hCmax_def
  have hCmax_nn : 0 ≤ Cmax :=
    Finset.sum_nonneg (fun α _ => hCα_nn α.val α.property)
  refine ⟨Cmax, hCmax_nn, fun T => ?_⟩
  -- Abbreviation for the order-`0` chart-Sobolev summand at chart `α`, component `(Idx, Jdx)`.
  set summand : M → (Fin r → Fin (Module.finrank ℝ E)) →
      (Fin s → Fin (Module.finrank ℝ E)) → ℝ≥0∞ :=
    fun α Idx Jdx =>
      ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
        ENNReal.ofReal
          (((chartAtlasPOU I M α : M → ℝ)
              ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
            |(iteratedFDeriv ℝ 0
                  (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
                    ∘ (extChartAt I α).symm
                    ∘ (toEuclidean (E := E)).symm)
                  y)
                (fun i => EuclideanSpace.basisFun
                  (Fin (Module.finrank ℝ E)) ℝ
                  ((default : Fin 0 → Fin (Module.finrank ℝ E)) i))| ^ 2)
        ∂(volume : Measure EuclN) with hsummand_def
  set lhsEsq : M → (Fin r → Fin (Module.finrank ℝ E)) →
      (Fin s → Fin (Module.finrank ℝ E)) → ℝ≥0∞ :=
    fun α Idx Jdx =>
      (MeasureTheory.eLpNorm
          (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentScalar
            (I := I) (M := M) g r s T α Idx Jdx) 2
          (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure
            (I := I) (M := M) g)) ^ 2 with hlhsEsq_def
  -- Per-`(α ∈ Sf, Idx, Jdx)`: `lhsEsq ≤ ofReal Cmax · summand`.
  have h_perchart : ∀ α ∈ Sf, ∀ Idx Jdx,
      lhsEsq α Idx Jdx ≤ ENNReal.ofReal Cmax * summand α Idx Jdx := by
    intro α hα Idx Jdx
    have hCα_le : Cα α hα ≤ Cmax := by
      rw [hCmax_def]
      refine Finset.single_le_sum (f := fun β : Sf => Cα β.val β.property)
        (fun β _ => hCα_nn β.val β.property) (Finset.mem_attach Sf ⟨α, hα⟩)
    calc lhsEsq α Idx Jdx
        ≤ ENNReal.ofReal (Cα α hα) * summand α Idx Jdx := hCα α hα T Idx Jdx
      _ ≤ ENNReal.ofReal Cmax * summand α Idx Jdx :=
          mul_le_mul_right' (ENNReal.ofReal_le_ofReal hCα_le) _
  -- Sum over `(Idx, Jdx)` and `α ∈ Sf`.
  have h_sum_le :
      (∑ α ∈ Sf, ∑ Idx, ∑ Jdx, lhsEsq α Idx Jdx) ≤
        ENNReal.ofReal Cmax * ∑ α ∈ Sf, ∑ Idx, ∑ Jdx, summand α Idx Jdx := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun α hα => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun Idx _ => ?_)
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun Jdx _ => h_perchart α hα Idx Jdx)
  -- The finset double sum of summands is `≤` the full `tsum` representation, which is
  -- `tensorPouSobolevHsNormSq g 0 T`.
  have h_summand_eq_normSq :
      tensorPouSobolevHsNormSq (I := I) (M := M) g 0 T =
        ∑' α : M, ∑ Idx, ∑ Jdx, summand α Idx Jdx := by
    rw [tensorPouSobolevHsNormSq_eq_inner_sum (I := I) (M := M) g 0 T]
    refine tsum_congr (fun α => ?_)
    rw [Fintype.sum_prod_type
      (f := fun IJ : (Fin r → Fin (Module.finrank ℝ E)) ×
            (Fin s → Fin (Module.finrank ℝ E)) =>
        ∑ j ∈ Finset.range (2 * 0 + 1),
          ∑ basisIdx : Fin j → Fin (Module.finrank ℝ E),
            ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
              ENNReal.ofReal
                (((chartAtlasPOU I M α : M → ℝ)
                    ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
                  |(iteratedFDeriv ℝ j
                        (tensorChartComponentRaw (I := I) (M := M) g r s T α IJ.1 IJ.2
                          ∘ (extChartAt I α).symm
                          ∘ (toEuclidean (E := E)).symm)
                        y)
                      (fun i => EuclideanSpace.basisFun
                        (Fin (Module.finrank ℝ E)) ℝ (basisIdx i))| ^ 2)
              ∂(volume : Measure EuclN))]
    refine Finset.sum_congr rfl (fun Idx _ => ?_)
    refine Finset.sum_congr rfl (fun Jdx _ => ?_)
    rw [show (2 * 0 + 1) = 1 from rfl, Finset.sum_range_one,
      Fintype.sum_subsingleton _ (default : Fin 0 → Fin (Module.finrank ℝ E))]
  have h_finset_le_tsum :
      (∑ α ∈ Sf, ∑ Idx, ∑ Jdx, summand α Idx Jdx) ≤
        ∑' α : M, ∑ Idx, ∑ Jdx, summand α Idx Jdx :=
    ENNReal.sum_le_tsum Sf
  have h_total_le :
      (∑ α ∈ Sf, ∑ Idx, ∑ Jdx, lhsEsq α Idx Jdx) ≤
        ENNReal.ofReal Cmax * tensorPouSobolevHsNormSq (I := I) (M := M) g 0 T := by
    rw [h_summand_eq_normSq]
    exact h_sum_le.trans (mul_le_mul_left' h_finset_le_tsum _)
  -- Transport to `ℝ` via `.toReal`.
  have h_lhsEsq_ne_top : ∀ α Idx Jdx, lhsEsq α Idx Jdx ≠ ⊤ := by
    intro α Idx Jdx
    rw [hlhsEsq_def]
    refine (ENNReal.pow_ne_top ?_)
    exact (tensorChartComponentScalar_eLpNorm_two_lt_top
      (I := I) (M := M) (E := E) g r s T α Idx Jdx).ne
  have h_normSq_ne_top :
      tensorPouSobolevHsNormSq (I := I) (M := M) g 0 T ≠ ⊤ :=
    (tensorPouSobolevHsNormSq_lt_top (I := I) (M := M) g 0 T).ne
  have h_rhs_ne_top :
      ENNReal.ofReal Cmax * tensorPouSobolevHsNormSq (I := I) (M := M) g 0 T ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top h_normSq_ne_top
  have h_toReal := ENNReal.toReal_mono h_rhs_ne_top h_total_le
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hCmax_nn] at h_toReal
  -- Identify the `.toReal` of the finset double sum with the real-valued goal LHS.
  have h_lhs_toReal :
      (∑ α ∈ Sf, ∑ Idx, ∑ Jdx, lhsEsq α Idx Jdx).toReal =
        ∑ α ∈ Sf, ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
          ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
            ((MeasureTheory.eLpNorm
                (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentScalar
                  (I := I) (M := M) g r s T α Idx Jdx) 2
                (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure
                  (I := I) (M := M) g)).toReal) ^ 2 := by
    rw [ENNReal.toReal_sum (fun α _ => ?_)]
    · refine Finset.sum_congr rfl (fun α _ => ?_)
      rw [ENNReal.toReal_sum (fun Idx _ => ?_)]
      · refine Finset.sum_congr rfl (fun Idx _ => ?_)
        rw [ENNReal.toReal_sum (fun Jdx _ => h_lhsEsq_ne_top α Idx Jdx)]
        refine Finset.sum_congr rfl (fun Jdx _ => ?_)
        rw [hlhsEsq_def, ENNReal.toReal_pow]
      · exact ENNReal.sum_ne_top.mpr (fun Jdx _ => h_lhsEsq_ne_top α Idx Jdx)
    · exact ENNReal.sum_ne_top.mpr (fun Idx _ =>
        ENNReal.sum_ne_top.mpr (fun Jdx _ => h_lhsEsq_ne_top α Idx Jdx))
  rw [hSf_def] at h_lhs_toReal
  rw [← h_lhs_toReal]
  exact h_toReal

end ReverseOrderZeroBridge

/-- **The reverse order-`0` partition-of-unity completeness comparison (the genuine analytic
primitive).**

For a closed Riemannian manifold and ranks `(r, s)` there is a non-negative constant `C` such
that for every smooth compactly-supported `(r, s)`-tensor section `T`,
```
‖T‖ ≤ C · (tensorPouSobolevHsNorm g 0 T).toReal ,
```
where `‖T‖ = tensorL2Norm g r s T.toFun` is the global metric `L²` (semi-)norm.  This is the
reverse (lower) partition-of-unity completeness bound: the partition of unity sums to one, so the
chart-`H⁰` norm recovers the full metric `L²` norm up to the bounded metric-density factor on the
compact manifold.  It is the exact reverse of the on-disk forward comparison
`tensorPouSobolevHsNorm_zero_le_tensorL2Norm`, and is precisely the seminorm hypothesis `h_norm_le`
left open by `TensorPouSobolevHilbert.toTensorL2_continuousLinearEquiv`.

It is proved by composing the (on-disk, sorry-free) reverse fibre-norm component bound
`tensorL2Norm_sq_le_const_mul_sum_componentL2Norm_sq` (the metric `L²` norm squared is dominated
by the partition-of-unity-weighted chart-component `L²` sum) with the reverse measure-bridge
comparison `exists_sum_componentL2Norm_sq_le_tensorPouSobolevHsNormSq_zero` (that chart-component
`L²` sum is dominated by the order-`0` chart-Sobolev norm squared), then taking square roots.  The
completion-norm form `exists_l2Norm_le_toHs_zero` is proved on top of it. -/
theorem exists_l2Norm_le_tensorPouSobolevHsNorm_zero
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ T : Integral.L2.SmoothCcTensor g r s,
        ‖T‖ ≤ C * (tensorPouSobolevHsNorm (I := I) (M := M) g 0 T).toReal := by
  classical
  obtain ⟨C₁, hC₁_nn, hC₁⟩ :=
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorL2Norm_sq_le_const_mul_sum_componentL2Norm_sq
      (I := I) (M := M) (E := E) g r s
  obtain ⟨C₂, hC₂_nn, hC₂⟩ :=
    exists_sum_componentL2Norm_sq_le_tensorPouSobolevHsNormSq_zero (I := I) (M := M) g r s
  refine ⟨Real.sqrt (C₁ * C₂), Real.sqrt_nonneg _, fun T => ?_⟩
  -- `‖T‖² ≤ C₁ · (component sum) ≤ C₁ · C₂ · ‖·‖²_{H⁰_chart}`, then take square roots.
  set L : ℝ := tensorL2Norm (I := I) (M := M) g r s T.toFun with hL_def
  have hL_eq : ‖T‖ = L := (tensorL2Norm_toFun_eq_norm (I := I) (M := M) g T).symm
  set N : ℝ := (tensorPouSobolevHsNorm (I := I) (M := M) g 0 T).toReal with hN_def
  have hN_nn : 0 ≤ N := ENNReal.toReal_nonneg
  have hNormSq_toReal : (tensorPouSobolevHsNormSq (I := I) (M := M) g 0 T).toReal = N ^ 2 := by
    unfold tensorPouSobolevHsNormSq
    rw [ENNReal.toReal_pow]
  set S : ℝ := ∑ α ∈ DifferentialGeometry.Integral.Measure.chartAtlasPOU_finset (I := I) (M := M),
      ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
        ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
          ((MeasureTheory.eLpNorm
              (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentScalar
                (I := I) (M := M) g r s T α Idx Jdx) 2
              (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure
                (I := I) (M := M) g)).toReal) ^ 2 with hS_def
  have hS_le : L ^ 2 ≤ C₁ * S := hC₁ T
  have hcomp_le : S ≤ C₂ * N ^ 2 := by
    have := hC₂ T
    rwa [hNormSq_toReal] at this
  have hL_nn : 0 ≤ L := tensorL2Norm_nonneg (I := I) (M := M) g r s T.toFun
  have h_sq_le : L ^ 2 ≤ C₁ * C₂ * N ^ 2 := by
    calc L ^ 2 ≤ C₁ * S := hS_le
      _ ≤ C₁ * (C₂ * N ^ 2) := mul_le_mul_of_nonneg_left hcomp_le hC₁_nn
      _ = C₁ * C₂ * N ^ 2 := by ring
  rw [hL_eq]
  calc L = Real.sqrt (L ^ 2) := (Real.sqrt_sq hL_nn).symm
    _ ≤ Real.sqrt (C₁ * C₂ * N ^ 2) := Real.sqrt_le_sqrt h_sq_le
    _ = Real.sqrt (C₁ * C₂) * N := by
        rw [Real.sqrt_mul (mul_nonneg hC₁_nn hC₂_nn), Real.sqrt_sq hN_nn]

/-- **The reverse order-`0` comparison: the global metric `L²` norm is controlled by the
order-`0` partition-of-unity chart-Sobolev completion norm (the genuine atomic comparison
primitive).**

For a closed Riemannian manifold there is a non-negative constant `C` such that for every smooth
compactly-supported `(0, 2)`-tensor section `T`,
```
‖T.toL2‖ ≤ C · ‖T.toHs 0‖ .
```
`‖T.toL2‖ = ‖T‖` is the global metric `L²` (semi-)norm (`norm_toL2`) and `‖T.toHs 0‖` is the
order-`0` partition-of-unity chart-Sobolev completion norm.  This is the reverse of the on-disk
forward comparison `tensorPouSobolevHsNorm_zero_le_tensorL2Norm` (`H⁰_chart ≤ C · L²`): the
partition of unity sums to one, so the chart-`H⁰` norm recovers the full `L²` norm up to the
metric-density factor, bounded on the compact manifold.  It is proved on top of the underlying
seminorm primitive `exists_l2Norm_le_tensorPouSobolevHsNorm_zero` via `norm_toL2` and
`tensorPouSobolevHilbert_norm_eq`. -/
theorem exists_l2Norm_le_toHs_zero
    (g : SmoothRiemannianMetric I M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ T : Integral.L2.SmoothCcTensor g 0 2,
        ‖Integral.L2.SmoothCcTensor.toL2 (g := g) (r := 0) (s := 2) T‖ ≤
          C * ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g) (r := 0) (s := 2) 0 T‖ := by
  obtain ⟨C, hC_nn, hC⟩ :=
    exists_l2Norm_le_tensorPouSobolevHsNorm_zero (I := I) (M := M) g 0 2
  refine ⟨C, hC_nn, fun T => ?_⟩
  rw [Integral.L2.SmoothCcTensor.norm_toL2, tensorPouSobolevHilbert_norm_eq]
  exact hC T

end DifferentialGeometry.PDE.RicciFlow
