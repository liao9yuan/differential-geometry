import DifferentialGeometry.Analysis.Sobolev.Tensor.PouWeightedNorm

/-!
# Hilbert-Schmidt-style partition-of-unity-weighted chart-Sobolev norm
for tensor sections

For a closed Riemannian manifold `(M, g)` modelled on a finite-dimensional
real inner-product space `E`, and a smooth compactly-supported
`(r, s)`-tensor section `T`, this file defines a Hilbert-Schmidt-style
aggregated chart-Sobolev norm `tensorPouSobolevHsNorm g k T`.

The norm collects, on every chart, the sum-of-squares (Hilbert-Schmidt
expansion) of the iterated Fréchet derivative components of the raw
chart-frame scalar components pulled back through the model-Euclidean
representation map, in the orthonormal basis `EuclideanSpace.basisFun`.

Schematically, with `n = finrank ℝ E`, `IJ = (Idx, Jdx)` the component
multi-index pair, and writing `ρ_α := chartAtlasPOU I M α` for the chart-`α`
partition-of-unity weight,
`tensorPouSobolevHsNorm g k T` is

`(∑'α, ∑_{IJ} ∑_{j ≤ 2k} ∑_{basisIdx : Fin j → Fin n}
  ∫ ρ_α(pull(y)) · |D^j (Tᵅ_{IJ} ∘ pull)(y)(e_{basisIdx_1}, ..., e_{basisIdx_j})|² dy)^{1/2}`,

where `pull := (extChartAt I α).symm ∘ toEuclidean.symm : EuclN → M`, the
iterated derivative is taken of the EuclN-pulled scalar, and the multilinear
evaluation uses the standard orthonormal basis `EuclideanSpace.basisFun`.

The crucial difference from `tensorPouSobolevNorm` (which uses the
*operator norm* of the iterated Fréchet derivative) is that the
inner-most term here is `|A(e_{i₁}, ..., e_{iⱼ})|²` summed over
all index tuples `(i₁, ..., iⱼ) ∈ (Fin n)^j`. This is the
Hilbert-Schmidt norm-squared expansion of `A`, equal to the L² norm of
its component vector in the chosen basis, and therefore satisfies the
parallelogram law. It is consequently induced by an inner product.

## Main definitions

* `tensorPouSobolevHsNorm g k T` — the Hilbert-Schmidt partition-of-unity-
  weighted chart-Sobolev norm of `T` at regularity order `2k`.

## Main results

* `tensorPouSobolevHsNorm_nonneg`, `tensorPouSobolevHsNorm_zero_section` —
  basic non-negativity and vanishing-at-zero.
* `tensorPouSobolevHsNorm_le_succ` — monotonicity in `k`:
  `tensorPouSobolevHsNorm g k T ≤ tensorPouSobolevHsNorm g (k + 1) T`.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Sobolev
namespace Tensor

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Sobolev.Euclidean
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

/-! ## The Hilbert-Schmidt partition-of-unity-weighted chart-Sobolev norm -/

/-- The Hilbert-Schmidt partition-of-unity-weighted chart-Sobolev norm of a
smooth compactly-supported `(r, s)`-tensor section `T` at regularity order
`2k`.

Concretely, a square root of a `tsum` over chart base points `α : M` of the
finite sum, over component multi-indices `IJ`, over Fréchet-derivative
orders `j ≤ 2k`, and over basis-index tuples `basisIdx : Fin j → Fin n`
(where `n = finrank ℝ E`), of the integral, against the volume measure of
the chart target in `EuclideanSpace ℝ (Fin n)`, of the partition-of-unity
weight at `α` (composed with the Euclidean representation map back to `M`)
times the squared absolute value of the multilinear evaluation of the
`j`-th Fréchet derivative of the EuclN-pulled raw chart-frame
`(Idx, Jdx)`-component on the standard `EuclideanSpace.basisFun` argument
tuple indexed by `basisIdx`.

The Hilbert-Schmidt summation `∑_{basisIdx} |·|²` over all index tuples is
the squared HS norm of the iterated derivative, equal to the L² norm of its
component vector in the chosen orthonormal basis, and therefore
satisfies the parallelogram law. Consequently this norm is induced by an
inner product. -/
noncomputable def tensorPouSobolevHsNorm
    (g : SmoothRiemannianMetric I M) {r s : ℕ}
    (k : ℕ) (T : SmoothCcTensor g r s) : ℝ≥0∞ :=
  (∑' α : M,
    ∑ IJ : (Fin r → Fin (Module.finrank ℝ E)) ×
        (Fin s → Fin (Module.finrank ℝ E)),
      ∑ j ∈ Finset.range (2 * k + 1),
        ∑ basisIdx : Fin j → Fin (Module.finrank ℝ E),
          ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
            ENNReal.ofReal
              (((chartAtlasPOU I M α : M → ℝ)
                  ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
                |(iteratedFDeriv ℝ j
                      (tensorChartComponentRaw (I := I) (M := M) g r s T α
                          IJ.1 IJ.2
                        ∘ (extChartAt I α).symm
                        ∘ (toEuclidean (E := E)).symm)
                      y)
                    (fun i => EuclideanSpace.basisFun
                      (Fin (Module.finrank ℝ E)) ℝ (basisIdx i))| ^ 2)
            ∂(volume :
              Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))))) ^
    (1 / 2 : ℝ)

/-- Unfolding lemma for `tensorPouSobolevHsNorm`. -/
theorem tensorPouSobolevHsNorm_eq
    (g : SmoothRiemannianMetric I M) {r s : ℕ}
    (k : ℕ) (T : SmoothCcTensor g r s) :
    tensorPouSobolevHsNorm (I := I) (M := M) g k T =
      (∑' α : M,
        ∑ IJ : (Fin r → Fin (Module.finrank ℝ E)) ×
            (Fin s → Fin (Module.finrank ℝ E)),
          ∑ j ∈ Finset.range (2 * k + 1),
            ∑ basisIdx : Fin j → Fin (Module.finrank ℝ E),
              ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
                ENNReal.ofReal
                  (((chartAtlasPOU I M α : M → ℝ)
                      ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
                    |(iteratedFDeriv ℝ j
                          (tensorChartComponentRaw (I := I) (M := M) g r s T α
                              IJ.1 IJ.2
                            ∘ (extChartAt I α).symm
                            ∘ (toEuclidean (E := E)).symm)
                          y)
                        (fun i => EuclideanSpace.basisFun
                          (Fin (Module.finrank ℝ E)) ℝ (basisIdx i))| ^ 2)
                ∂(volume :
                  Measure (EuclideanSpace ℝ
                    (Fin (Module.finrank ℝ E))))) ^ (1 / 2 : ℝ) := rfl

/-- The Hilbert-Schmidt partition-of-unity-weighted chart-Sobolev norm is
non-negative. (Trivially `0 ≤ ·` on `ℝ≥0∞`; recorded for downstream
convenience.) -/
theorem tensorPouSobolevHsNorm_nonneg
    (g : SmoothRiemannianMetric I M) {r s : ℕ}
    (k : ℕ) (T : SmoothCcTensor g r s) :
    0 ≤ tensorPouSobolevHsNorm (I := I) (M := M) g k T :=
  zero_le _

/-! ## Vanishing at the zero tensor section -/

/-- The composite of the raw chart-frame scalar component of the zero
tensor section with the Euclidean pull-back map vanishes identically on
`EuclideanSpace ℝ (Fin n)`. -/
private lemma tensorChartComponentRaw_comp_euclid_zero_section
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    (tensorChartComponentRaw (I := I) (M := M) g r s
        (0 : SmoothCcTensor g r s) α Idx Jdx
      ∘ (extChartAt I α).symm
      ∘ (toEuclidean (E := E)).symm) =
      (fun _ : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) => (0 : ℝ)) := by
  funext y
  -- Reduce to the M-level identity for the zero section.
  have hM : tensorChartComponentRaw (I := I) (M := M) g r s
      (0 : SmoothCcTensor g r s) α Idx Jdx
      ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) = 0 := by
    -- Use the auxiliary lemma from PouWeightedNorm: at every M-point,
    -- the raw component of the zero section is zero.
    have hraw_comp :
        (tensorChartComponentRaw (I := I) (M := M) g r s
            (0 : SmoothCcTensor g r s) α Idx Jdx
          ∘ (extChartAt I α).symm) =
          (fun _ : E => (0 : ℝ)) := by
      -- This is the existing private lemma's content; rebuild it here.
      funext x
      -- Reduce to: tensorChartComponentRaw (0) is identically zero on M.
      -- Strategy: use the same projection argument as in PouWeightedNorm.
      change tensorChartComponentRaw (I := I) (M := M) g r s
          (0 : SmoothCcTensor g r s) α Idx Jdx ((extChartAt I α).symm x) = 0
      -- Unfold the raw component on `M`.
      classical
      have h0 : (trivializationAt (TensorRSModel r s ℝ E)
            (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ
              ((extChartAt I α).symm x)
              ((0 : SmoothCcTensor g r s).toSection ((extChartAt I α).symm x))
              = 0 := by
        have hsec : (0 : SmoothCcTensor g r s).toSection
            ((extChartAt I α).symm x) = 0 := by rfl
        rw [hsec]
        exact map_zero _
      unfold tensorChartComponentRaw
      change tensorChartComponentProjection (E := E) r s Idx Jdx
          (tensorTrivProj (I := I) (M := M) g r s
            (0 : SmoothCcTensor g r s) α ((extChartAt I α).symm x)) = 0
      unfold tensorTrivProj
      rw [h0]
      exact map_zero _
    -- Apply hraw_comp at `(toEuclidean.symm y)`.
    have := congrFun hraw_comp ((toEuclidean (E := E)).symm y)
    exact this
  exact hM

/-- The Hilbert-Schmidt partition-of-unity-weighted chart-Sobolev norm of
the zero tensor section is zero. -/
theorem tensorPouSobolevHsNorm_zero_section
    (g : SmoothRiemannianMetric I M) {r s : ℕ} (k : ℕ) :
    tensorPouSobolevHsNorm (I := I) (M := M) g k
        (0 : SmoothCcTensor g r s) = 0 := by
  classical
  rw [tensorPouSobolevHsNorm_eq]
  -- The integrand is identically zero on every chart, so the tsum is zero.
  have htsum :
      (∑' α : M,
        ∑ IJ : (Fin r → Fin (Module.finrank ℝ E)) ×
            (Fin s → Fin (Module.finrank ℝ E)),
          ∑ j ∈ Finset.range (2 * k + 1),
            ∑ basisIdx : Fin j → Fin (Module.finrank ℝ E),
              ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
                ENNReal.ofReal
                  (((chartAtlasPOU I M α : M → ℝ)
                      ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
                    |(iteratedFDeriv ℝ j
                          (tensorChartComponentRaw (I := I) (M := M) g r s
                              (0 : SmoothCcTensor g r s) α IJ.1 IJ.2
                            ∘ (extChartAt I α).symm
                            ∘ (toEuclidean (E := E)).symm)
                          y)
                        (fun i => EuclideanSpace.basisFun
                          (Fin (Module.finrank ℝ E)) ℝ (basisIdx i))| ^ 2)
                ∂(volume :
                  Measure (EuclideanSpace ℝ
                    (Fin (Module.finrank ℝ E))))) = 0 := by
    have hpt : ∀ α : M,
        (∑ IJ : (Fin r → Fin (Module.finrank ℝ E)) ×
            (Fin s → Fin (Module.finrank ℝ E)),
          ∑ j ∈ Finset.range (2 * k + 1),
            ∑ basisIdx : Fin j → Fin (Module.finrank ℝ E),
              ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
                ENNReal.ofReal
                  (((chartAtlasPOU I M α : M → ℝ)
                      ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
                    |(iteratedFDeriv ℝ j
                          (tensorChartComponentRaw (I := I) (M := M) g r s
                              (0 : SmoothCcTensor g r s) α IJ.1 IJ.2
                            ∘ (extChartAt I α).symm
                            ∘ (toEuclidean (E := E)).symm)
                          y)
                        (fun i => EuclideanSpace.basisFun
                          (Fin (Module.finrank ℝ E)) ℝ (basisIdx i))| ^ 2)
                ∂(volume :
                  Measure (EuclideanSpace ℝ
                    (Fin (Module.finrank ℝ E))))) = 0 := by
      intro α
      refine Finset.sum_eq_zero ?_
      intro IJ _
      refine Finset.sum_eq_zero ?_
      intro j _
      refine Finset.sum_eq_zero ?_
      intro basisIdx _
      -- The composite is the zero function, so its iterated derivative is zero.
      have hraw := tensorChartComponentRaw_comp_euclid_zero_section
        (I := I) (M := M) g r s α IJ.1 IJ.2
      have hiter : iteratedFDeriv ℝ j
          (tensorChartComponentRaw (I := I) (M := M) g r s
              (0 : SmoothCcTensor g r s) α IJ.1 IJ.2
            ∘ (extChartAt I α).symm
            ∘ (toEuclidean (E := E)).symm) = 0 := by
        rw [hraw]
        exact iteratedFDeriv_fun_zero
      have hintegrand_zero :
          (fun y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) =>
            ENNReal.ofReal
              (((chartAtlasPOU I M α : M → ℝ)
                  ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
                |(iteratedFDeriv ℝ j
                      (tensorChartComponentRaw (I := I) (M := M) g r s
                          (0 : SmoothCcTensor g r s) α IJ.1 IJ.2
                        ∘ (extChartAt I α).symm
                        ∘ (toEuclidean (E := E)).symm)
                      y)
                    (fun i => EuclideanSpace.basisFun
                      (Fin (Module.finrank ℝ E)) ℝ (basisIdx i))| ^ 2)) =
            (fun _ => 0) := by
        funext y
        rw [hiter]
        simp
      rw [hintegrand_zero]
      simp
    rw [tsum_congr hpt]
    exact tsum_zero
  rw [htsum]
  exact ENNReal.zero_rpow_of_pos (by norm_num)

/-! ## Monotonicity in the regularity order `k` -/

/-- The Hilbert-Schmidt partition-of-unity-weighted chart-Sobolev norm is
monotone in the regularity order: passing from order `2k` to order `2(k+1)`
cannot decrease the norm, because the additional iterated-derivative
orders contribute non-negative summands to the inner finite sum. -/
theorem tensorPouSobolevHsNorm_le_succ
    (g : SmoothRiemannianMetric I M) {r s : ℕ}
    (k : ℕ) (T : SmoothCcTensor g r s) :
    tensorPouSobolevHsNorm (I := I) (M := M) g k T ≤
      tensorPouSobolevHsNorm (I := I) (M := M) g (k + 1) T := by
  classical
  rw [tensorPouSobolevHsNorm_eq, tensorPouSobolevHsNorm_eq]
  have hrange : Finset.range (2 * k + 1) ⊆ Finset.range (2 * (k + 1) + 1) :=
    Finset.range_subset_range.mpr (by omega)
  have hper_chart : ∀ α : M,
      (∑ IJ : (Fin r → Fin (Module.finrank ℝ E)) ×
          (Fin s → Fin (Module.finrank ℝ E)),
        ∑ j ∈ Finset.range (2 * k + 1),
          ∑ basisIdx : Fin j → Fin (Module.finrank ℝ E),
            ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
              ENNReal.ofReal
                (((chartAtlasPOU I M α : M → ℝ)
                    ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
                  |(iteratedFDeriv ℝ j
                        (tensorChartComponentRaw (I := I) (M := M) g r s T α
                            IJ.1 IJ.2
                          ∘ (extChartAt I α).symm
                          ∘ (toEuclidean (E := E)).symm)
                        y)
                      (fun i => EuclideanSpace.basisFun
                        (Fin (Module.finrank ℝ E)) ℝ (basisIdx i))| ^ 2)
              ∂(volume :
                Measure (EuclideanSpace ℝ
                  (Fin (Module.finrank ℝ E))))) ≤
      (∑ IJ : (Fin r → Fin (Module.finrank ℝ E)) ×
          (Fin s → Fin (Module.finrank ℝ E)),
        ∑ j ∈ Finset.range (2 * (k + 1) + 1),
          ∑ basisIdx : Fin j → Fin (Module.finrank ℝ E),
            ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
              ENNReal.ofReal
                (((chartAtlasPOU I M α : M → ℝ)
                    ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
                  |(iteratedFDeriv ℝ j
                        (tensorChartComponentRaw (I := I) (M := M) g r s T α
                            IJ.1 IJ.2
                          ∘ (extChartAt I α).symm
                          ∘ (toEuclidean (E := E)).symm)
                        y)
                      (fun i => EuclideanSpace.basisFun
                        (Fin (Module.finrank ℝ E)) ℝ (basisIdx i))| ^ 2)
              ∂(volume :
                Measure (EuclideanSpace ℝ
                  (Fin (Module.finrank ℝ E))))) := by
    intro α
    refine Finset.sum_le_sum ?_
    intro IJ _
    exact Finset.sum_le_sum_of_subset_of_nonneg hrange
      (by intro j _ _; exact zero_le _)
  have htsum_le :
      (∑' α : M,
        ∑ IJ : (Fin r → Fin (Module.finrank ℝ E)) ×
            (Fin s → Fin (Module.finrank ℝ E)),
          ∑ j ∈ Finset.range (2 * k + 1),
            ∑ basisIdx : Fin j → Fin (Module.finrank ℝ E),
              ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
                ENNReal.ofReal
                  (((chartAtlasPOU I M α : M → ℝ)
                      ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
                    |(iteratedFDeriv ℝ j
                          (tensorChartComponentRaw (I := I) (M := M) g r s T α
                              IJ.1 IJ.2
                            ∘ (extChartAt I α).symm
                            ∘ (toEuclidean (E := E)).symm)
                          y)
                        (fun i => EuclideanSpace.basisFun
                          (Fin (Module.finrank ℝ E)) ℝ (basisIdx i))| ^ 2)
                ∂(volume :
                  Measure (EuclideanSpace ℝ
                    (Fin (Module.finrank ℝ E))))) ≤
        (∑' α : M,
          ∑ IJ : (Fin r → Fin (Module.finrank ℝ E)) ×
              (Fin s → Fin (Module.finrank ℝ E)),
            ∑ j ∈ Finset.range (2 * (k + 1) + 1),
              ∑ basisIdx : Fin j → Fin (Module.finrank ℝ E),
                ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
                  ENNReal.ofReal
                    (((chartAtlasPOU I M α : M → ℝ)
                        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
                      |(iteratedFDeriv ℝ j
                            (tensorChartComponentRaw (I := I) (M := M) g r s T α
                                IJ.1 IJ.2
                              ∘ (extChartAt I α).symm
                              ∘ (toEuclidean (E := E)).symm)
                            y)
                          (fun i => EuclideanSpace.basisFun
                            (Fin (Module.finrank ℝ E)) ℝ (basisIdx i))| ^ 2)
                  ∂(volume :
                    Measure (EuclideanSpace ℝ
                      (Fin (Module.finrank ℝ E))))) := by
    exact ENNReal.tsum_le_tsum hper_chart
  exact ENNReal.rpow_le_rpow htsum_le (by norm_num)

#print axioms tensorPouSobolevHsNorm
#print axioms tensorPouSobolevHsNorm_nonneg
#print axioms tensorPouSobolevHsNorm_zero_section
#print axioms tensorPouSobolevHsNorm_le_succ

end Tensor
end Sobolev
end Analysis
end DifferentialGeometry
