import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CrossCorrectionContractionTopRest
import DifferentialGeometry.Geometry.Connection.TensorNabla.LiftedSectionCovariantRealizeBridge
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.MetricContractionLeibnizGrid

/-! # The pointwise full-window product grid of the parallel rank-reducing contraction

The intrinsic squared fibre norm of the order-`p` covariant gradient of the parallel `g₀`-single
contraction `crossCorrParallelContraction g₀ S T` of a rank-`2` section `S` against a rank-`3`
section `T` is dominated, at every point, by the **zero-jet-inclusive full-window product grid** in
the two factors' covariant jets:
```
rfns(∇^p (S ⌟ T))(x)
  ≤ Cd · ∑_{i ≤ p} rfns(∇^i T)(x) · (∑_{l ≤ p − i} rfns(∇^l S)(x)).
```

This is the contraction-native consequence of three sorry-free ingredients: the structural identity
`crossCorrParallelContraction_iteratedCovGrad_eq_appCcRS_slotExtendPow` rewriting the iterated
covariant gradient of the contraction as the slot-extended cometric operator field applied to the
iterated covariant gradient of the realized bare product `crossCorrProdSection`; the uniform
operator-norm envelope `exists_uniform_riemannianFiberNormSq_appCcRS_le` of that bundle operator
field; and the proven bare two-section bilinear-product covariant-jet grid
`RfnsBilinearProduct.exists_rfns_iteratedCovGrad_prod_diagGrid_le`, transported across the
permutation/cast strip identifying `crossCorrProdSection` with the unit-model bare product
(`crossCorrProdSection_eq_permute_unitModelProdSection`, `rfns_iteratedCovGrad_castRankCc_db`).

The window is the **full** `i + l ≤ p` triangle and the bound is a **product** of the two single-jet
sums (never a pointwise two-arm *sum* — that bilinear form is Lean-refuted), so this primitive is the
correct pointwise building block for the higher cross-correction product-grid bounds. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.DeTurck
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

/-- **The pointwise full-window product-grid covariant-jet bound of the parallel rank-reducing
contraction.**  At every point `x`, the intrinsic squared fibre norm of the order-`p` covariant
gradient of the parallel `g₀`-single contraction `crossCorrParallelContraction g₀ S T` of the rank-`2`
section `S` against the rank-`3` section `T` is bounded by the zero-jet-inclusive full-window product
grid
```
rfns(∇^p (S ⌟ T))(x)
  ≤ Cd · ∑_{i ≤ p} rfns(∇^i T)(x) · (∑_{l ≤ p − i} rfns(∇^l S)(x)),
```
with a nonnegative constant `Cd` independent of `x` (it depends only on the uniform operator-norm of
the slot-extended cometric operator field and the bare-product grid constant).

The outer sum carries the rank-`3` factor `T`'s jets; the inner sum carries the rank-`2` factor `S`'s
jets — the orientation of the two-section bare bilinear-product grid. -/
theorem crossCorrParallelContraction_iteratedCovGrad_rfns_fullWindowProductGrid_le
    (g₀ : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g₀ 0 (2 + 0)) (T : SmoothCcTensor g₀ 0 (3 + 0)) (p : ℕ) :
    ∃ Cd : ℝ, 0 ≤ Cd ∧ ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + 0 + 0 + p) x
          ((iteratedCovGrad g₀ 0 (3 + 0 + 0) p
              (crossCorrParallelContraction (I := I) g₀ (a := 0) (b := 0) S T)).toSection x) ≤
        Cd * ∑ i ∈ Finset.range (p + 1),
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + i) x
                ((iteratedCovGrad g₀ 0 3 i T).toSection x)
              * ∑ l ∈ Finset.range (p + 1 - i),
                  riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
                    ((iteratedCovGrad g₀ 0 2 l S).toSection x) := by
  obtain ⟨Cgrid, hCgrid0, hCgrid⟩ :=
    (bareTensorRfnsBilinearProduct (I := I) g₀ 3 2).exists_rfns_iteratedCovGrad_prod_diagGrid_le T S
  obtain ⟨Cenv, hCenv0, hCenv⟩ := exists_uniform_riemannianFiberNormSq_appCcRS_le (I := I) (M := M) g₀
    0 (((3 + 0) + (2 + 0)) + p) ((3 + 0 + 0) + p)
    (slotExtendPow (I := I) (M := M) g₀ ((3 + 0) + (2 + 0)) (3 + 0 + 0) p
      (crossCorrCometricOp (I := I) g₀ 0 0))
  refine ⟨Cenv * Cgrid p, mul_nonneg hCenv0 (hCgrid0 p), fun x => ?_⟩
  rw [crossCorrParallelContraction_iteratedCovGrad_eq_appCcRS_slotExtendPow (I := I) g₀ S T p]
  refine le_trans (hCenv _ x) ?_
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ hCenv0
  rw [crossCorrProdSection_eq_permute_unitModelProdSection (I := I) g₀ S T,
    riemannianFiberNormSq_iteratedCovGrad_permuteCcTensor (I := I) (M := M) g₀
      (crossCorrPerm 0 0) (unitModelProdSection (I := I) g₀ T S) p x]
  have hgrid := hCgrid x p
  have hcast : riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((3 + 2) + p) x
      ((iteratedCovGrad g₀ 0 (3 + 2) p
        ((bareTensorRfnsBilinearProduct (I := I) g₀ 3 2).prod (a := 0) (b := 0) T S)).toSection x)
      = riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((3 + 0) + (2 + 0) + p) x
        ((iteratedCovGrad g₀ 0 ((3 + 0) + (2 + 0)) p
          (unitModelProdSection (I := I) g₀ T S)).toSection x) := by
    rw [show ((bareTensorRfnsBilinearProduct (I := I) g₀ 3 2).prod (a := 0) (b := 0) T S)
      = castRankCc_db g₀ 0 (by omega : (3 + 0) + (2 + 0) = (3 + 2) + 0 + 0)
        (unitModelProdSection (I := I) g₀ T S) from rfl]
    rw [rfns_iteratedCovGrad_castRankCc_db (I := I) (M := M) g₀ 0
      (by omega : (3 + 0) + (2 + 0) = (3 + 2) + 0 + 0)
      (unitModelProdSection (I := I) g₀ T S) p x]
  rw [hcast] at hgrid
  exact hgrid

/-- **(POSIT — birth-probe pending — the pointwise full-window product-grid covariant-jet bound of
the bilinear DIFFERENCE of two parallel rank-reducing contractions.)**  At every point `x`, the
intrinsic squared fibre norm of the order-`p` covariant gradient of the bilinear difference
`crossCorrParallelContraction g₀ S₁ T₁ − crossCorrParallelContraction g₀ S₂ T₂` of two parallel
`g₀`-single contractions of rank-`2` first factors `S₁, S₂` against rank-`3` second factors `T₁, T₂`
is dominated by the zero-jet-inclusive **full-window product grid** in the two factor differences and
the fixed endpoints
```
rfns(∇^p (S₁ ⌟ T₁ − S₂ ⌟ T₂))(x)
  ≤ Cd · ∑_{i ≤ p} (rfns(∇^i (S₁ − S₂))(x) + rfns(∇^i (T₁ − T₂))(x))
            · (∑_{l ≤ p − i} (rfns(∇^l S₂)(x) + rfns(∇^l T₂)(x))),
```
with a nonnegative constant `Cd` independent of `x`.

This is the bilinear-DIFFERENCE counterpart of the proven single-contraction grid
`crossCorrParallelContraction_iteratedCovGrad_rfns_fullWindowProductGrid_le` above: by the contraction
bilinearity (`crossCorrParallelContraction_sub_left`, `_sub_right`) the difference telescopes onto a
clean arm `(S₁ − S₂) ⌟ T₁` carrying the first-factor difference and a second arm `S₂ ⌟ (T₁ − T₂)`
carrying the second-factor difference, and each arm is bounded by the single-contraction full-window
product grid — putting one of the two factor differences in the outer sum and the fixed endpoints in
the inner sum, on the full `i + l ≤ p` triangle.  It is a **product** of the two single-jet sums
(never a pointwise two-arm *sum* — that bilinear form is Lean-refuted at `CrossCorrectionContractionTopRest:304`),
so it stays in the admissible product-grid family.

**Consumers.**  This is the consumer-minimal reusable core beneath
`crossCorrectionSectionDiff_iteratedCovGrad_diagonalProductGrid_rfns_le` (SUB1,
`SegmentMetricCurvatureDifferenceCovJet.lean:2599`), whose rank-`3` cross-correction-section
difference `cc(g₁,T₁) − cc(g₂,T₂)` is exactly such a contraction difference
(`crossCorrectionSectionDiff_eq_bilinearFactorization`, with `Sₖ = realizeSymm g₀ Tₖ` and
`Tₖ = permute c[0,1,2] (loweredConnDiffSection gₖ g₀)`); SUB1's glue specialises the difference
factors to `realizeSymm(T₁ − T₂)` and the lowered-connection cocycle, then folds the rank-`3`
lowered-connection jets into the `Tₖ`-jets (`crossCorrectionSection_iteratedCovGrad_rfns_le`) and
absorbs the order-zero fibre-small Neumann factor (`δ < 1/2`).

The *traced quadratic Cross* consumer
`crossSectionDiff_iteratedCovGrad_diagonalProductGrid_rfns_le` (SUB2, `…:3129`) does **NOT** reduce to
this contraction grid: its `crossSection` fibre is a quadratic `connDiffField ∘ connDiffField`
endomorphism-trace difference (`ricciDiffQuad_modelTrace_eq_crossEndoTrace`), a different bilinear
engine; it needs an analogous quadratic-trace-difference product grid (a separate posit, distinct
file/object).  Both consumers' holes were extracted and are **pointwise** full-window product grids
(no integrated-vs-pointwise currency divergence at the consumer interface).

**T11 risk (pointwise-vs-integrated).**  A prior session warned the `l ≥ 1` cross-correction cells may
need C⁰-sup / L²-Gagliardo–Nirenberg absorption — i.e. the *pointwise* fold could be FALSE, true only
in an integrated / self-product-augmented currency.  The two consumer holes are pointwise, so the
posit is stated pointwise; the **birth-probe is pending** and must Lean-refute-or-reduce this bound
before any glue is written over it (if the pointwise form fails, the integrated two-arm form via
`exists_integrated_iteratedCovGrad_diagonalProductGrid_twoArm_le` is the fallback currency).

**Non-vacuity.**  At `S₁ = S₂` and `T₁ = T₂` the difference vanishes, so both sides are `0`; a zero
`Cd` is rejected whenever either factor difference is genuinely present.

**Base-anchor correction (orchestrator).**  The inner (undifferenced) sum runs over BOTH endpoints
`S₁, S₂, T₁, T₂` — the original `(S₂, T₂)`-only base was refuted by the zero-base counterexample
(`S₂ = T₂ = 0` makes that RHS vanish identically while the LHS is `rfns(∇^p (S₁ ⌟ T₁)) ≢ 0`); with
both endpoints the bound follows from the bilinear telescope `(S₁−S₂) ⌟ T₁ + S₂ ⌟ (T₁−T₂)` and two
applications of the proven single-contraction grid above.  Its body is `sorry`. -/
theorem crossCorrParallelContraction_iteratedCovGrad_rfns_bilinearDifference_fullWindowProductGrid_le
    (g₀ : SmoothRiemannianMetric I M)
    (S₁ S₂ : SmoothCcTensor g₀ 0 (2 + 0)) (T₁ T₂ : SmoothCcTensor g₀ 0 (3 + 0)) (p : ℕ) :
    ∃ Cd : ℝ, 0 ≤ Cd ∧ ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + 0 + 0 + p) x
          ((iteratedCovGrad g₀ 0 (3 + 0 + 0) p
              (crossCorrParallelContraction (I := I) g₀ (a := 0) (b := 0) S₁ T₁
                - crossCorrParallelContraction (I := I) g₀ (a := 0) (b := 0) S₂ T₂)).toSection x) ≤
        Cd * ∑ i ∈ Finset.range (p + 1),
            (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
                ((iteratedCovGrad g₀ 0 2 i (S₁ - S₂)).toSection x)
              + riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + i) x
                ((iteratedCovGrad g₀ 0 3 i (T₁ - T₂)).toSection x))
              * ∑ l ∈ Finset.range (p + 1 - i),
                  (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
                      ((iteratedCovGrad g₀ 0 2 l S₁).toSection x)
                    + riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
                      ((iteratedCovGrad g₀ 0 2 l S₂).toSection x)
                    + riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + l) x
                      ((iteratedCovGrad g₀ 0 3 l T₁).toSection x)
                    + riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + l) x
                      ((iteratedCovGrad g₀ 0 3 l T₂).toSection x)) :=
  sorry

end Connection
end Integral
end DifferentialGeometry
