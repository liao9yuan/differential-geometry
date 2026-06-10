import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.RealizedJet2CovGradBound
import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.RealizedCovGradJetGeneralOrder

/-! # The sharp-order `C²` Sobolev embedding of the covariant 2-jet sum

For a closed (compact, boundaryless) smooth Riemannian manifold `(M, g₀)` modelled on a real
inner-product space `E`, this file supplies the **sharp-order** intrinsic `H^m ↪ C²` Sobolev
embedding for smooth compactly-supported `(0,2)`-tensors, stated on the iterated covariant-gradient
2-jet sum `iteratedCovGradJetSum g₀ S x = ∑_{j ≤ 2} ‖(∇^j S)(x)‖_{g₀}`
(`RealizedJet2CovGradBound.lean`):

  `iteratedCovGradJetSum g₀ S x ≤ C · ‖S.toHs m‖`   whenever `2 * m > dim M + 4`.

The on-disk embedding `iteratedCovGradJetSum_le_toHs` is the **even-order** variant: its Sobolev
order is forced to the doubled form `2k` with the (non-sharp) threshold `2k > dim M + 4` on the
order itself, so it cannot serve a supercritical order-`a` budget with `2a > dim M + 4` (there `a`
itself, which may be odd and well below `dim M + 4`, is the available Sobolev order).  The
sharp-order refinement posited here is the classical embedding at its true threshold
`m > dim M / 2 + 2` (`⟺ 2m > dim M + 4`), at an arbitrary (in particular odd) order `m`.

On top of the posited sharp-order leaf the file proves outright:

* `realizeSymm_iteratedCovGradJetSum_le` — the symmetric realization `realizeSymmCcTensor` does not
  increase the covariant 2-jet sum (constant `1`; the slot swap is a parallel fibre isometry,
  `flipCcTensor_iteratedCovGrad_norm_eq`);
* `exists_realizedJetSum_le_toHs_sharpOrder` — the sharp-order `C²` control of the **realized**
  perturbation `realizeSymmCcTensor g₀ S` by the order-`m` Sobolev norm of the *unrealized* `S`;
* `riemannianFiberNormSq_le_sq_iteratedCovGradJetSum` — the order-`0` extraction: the intrinsic
  squared fibre norm of the tensor value is at most the squared 2-jet sum, so the embedding yields
  pointwise `C⁰` sup control `rfns(S)(x) ≤ (C · ‖S.toHs m‖)²` of the form the integrated
  Gagliardo–Nirenberg two-arm product engine consumes as its `Λ²` sup hypotheses.

The sharp-order leaf `exists_iteratedCovGradJetSum_le_toHs_sharpOrder` has a `sorry` body (the
genuine sharp-threshold closed-manifold tensor Sobolev embedding); every consumer transitively
depends on its `sorryAx`. -/

noncomputable section

set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

open Bundle Manifold Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace IntrinsicSpectral
namespace MetricRealization

open DifferentialGeometry
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

/-- **(POSIT — the sharp-order intrinsic `H^m ↪ C²` tensor Sobolev embedding.)**  For
`2 * m > dim M + 4` (the sharp `C²` threshold `m > dim M / 2 + 2`, at an arbitrary — in particular
odd — Sobolev order `m`), there is a constant `C > 0` such that for every smooth
compactly-supported `(0,2)`-tensor `S` and every base point `x`,

  `iteratedCovGradJetSum g₀ S x ≤ C · ‖S.toHs m‖`.

This is the order-sharp refinement of the proven even-order embedding
`iteratedCovGradJetSum_le_toHs` (whose Sobolev order is forced to the doubled form `2k`): the
classical Sobolev embedding `H^m ↪ C²` on a closed `n`-manifold holds exactly when
`m > n / 2 + 2`, i.e. `2m > n + 4`, with no parity constraint on `m`.

**Non-vacuity.**  `C > 0` is strict, the left side carries the full covariant 2-jet of `S`
(orders `0, 1, 2`), and the right side the genuine order-`m` intrinsic Sobolev norm; a degenerate
`C` is rejected by any `S` with nonvanishing 2-jet.  Its body is `sorry`: the genuine
sharp-threshold closed-manifold tensor Sobolev embedding; consumers transitively depend on its
`sorryAx`. -/
theorem exists_iteratedCovGradJetSum_le_toHs_sharpOrder
    (g₀ : SmoothRiemannianMetric I M) (m : ℕ)
    (h_super : 2 * m > Module.finrank ℝ E + 4) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (S : SmoothCcTensor g₀ 0 2) (x : M),
        iteratedCovGradJetSum (I := I) g₀ S x ≤
          C * ‖SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) m S‖ :=
  sorry

attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
/-- **The symmetric realization does not increase the covariant 2-jet sum.**  For every smooth
compactly-supported `(0,2)`-tensor `S` and every base point `x`,

  `iteratedCovGradJetSum g₀ (realizeSymmCcTensor g₀ S) x ≤ iteratedCovGradJetSum g₀ S x`.

Termwise: `realizeSymm S = ½ • S + ½ • flip S` (`realizeSymmCcTensor_eq`), the iterated covariant
gradient is `ℝ`-linear (`iteratedCovGrad_add`, `iteratedCovGrad_smul`), and the slot swap is a
parallel fibre isometry of every iterated covariant gradient
(`flipCcTensor_iteratedCovGrad_norm_eq`), so
`‖∇^j (realizeSymm S)(x)‖ ≤ ½‖∇^j S(x)‖ + ½‖∇^j (flip S)(x)‖ = ‖∇^j S(x)‖`.  Proved outright; no
posit. -/
theorem realizeSymm_iteratedCovGradJetSum_le
    (g₀ : SmoothRiemannianMetric I M) (S : SmoothCcTensor g₀ 0 2) (x : M) :
    iteratedCovGradJetSum (I := I) g₀ (realizeSymmCcTensor (I := I) g₀ S) x ≤
      iteratedCovGradJetSum (I := I) g₀ S x := by
  classical
  rw [iteratedCovGradJetSum, iteratedCovGradJetSum]
  refine Finset.sum_le_sum (fun j _ => ?_)
  letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 (2 + j) I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 (2 + j)
  have hdecomp :
      iteratedCovGrad (I := I) (M := M) g₀ 0 2 j (realizeSymmCcTensor (I := I) g₀ S) =
        (1 / 2 : ℝ) • iteratedCovGrad (I := I) (M := M) g₀ 0 2 j S +
          (1 / 2 : ℝ) • iteratedCovGrad (I := I) (M := M) g₀ 0 2 j
            (flipCcTensor (I := I) g₀ S) := by
    rw [realizeSymmCcTensor_eq, PDE.RicciFlow.iteratedCovGrad_add,
      MetricRealization.iteratedCovGrad_smul, MetricRealization.iteratedCovGrad_smul]
  rw [hdecomp]
  rw [show ((1 / 2 : ℝ) • iteratedCovGrad (I := I) (M := M) g₀ 0 2 j S +
        (1 / 2 : ℝ) • iteratedCovGrad (I := I) (M := M) g₀ 0 2 j
          (flipCcTensor (I := I) g₀ S)).toSection x =
      (1 / 2 : ℝ) • (iteratedCovGrad (I := I) (M := M) g₀ 0 2 j S).toSection x +
        (1 / 2 : ℝ) • (iteratedCovGrad (I := I) (M := M) g₀ 0 2 j
          (flipCcTensor (I := I) g₀ S)).toSection x from by
    rw [SmoothCcTensor.toSection_add, SmoothCcTensor.toSection_smul,
      SmoothCcTensor.toSection_smul]; rfl]
  refine le_trans (norm_add_le _ _) ?_
  rw [norm_smul, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  have hflip := flipCcTensor_iteratedCovGrad_norm_eq (I := I) g₀ S j x
  linarith [hflip]

/-- **The sharp-order `C²` control of the realized perturbation by the unrealized Sobolev norm.**
For `2 * a > dim M + 4` there is a constant `C > 0` such that for every smooth
compactly-supported `(0,2)`-tensor `S` and every base point `x`,

  `iteratedCovGradJetSum g₀ (realizeSymmCcTensor g₀ S) x ≤ C · ‖S.toHs a‖`.

Composition of the realization monotonicity `realizeSymm_iteratedCovGradJetSum_le` (constant `1`)
with the posited sharp-order embedding `exists_iteratedCovGradJetSum_le_toHs_sharpOrder`; consumers
transitively depend on the `sorryAx` of the latter. -/
theorem exists_realizedJetSum_le_toHs_sharpOrder
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha : 2 * a > Module.finrank ℝ E + 4) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (S : SmoothCcTensor g₀ 0 2) (x : M),
        iteratedCovGradJetSum (I := I) g₀ (realizeSymmCcTensor (I := I) g₀ S) x ≤
          C * ‖SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) a S‖ := by
  obtain ⟨C, hC_pos, hC⟩ := exists_iteratedCovGradJetSum_le_toHs_sharpOrder (I := I) g₀ a ha
  exact ⟨C, hC_pos, fun S x =>
    le_trans (realizeSymm_iteratedCovGradJetSum_le (I := I) g₀ S x) (hC S x)⟩

attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
/-- **The order-`0` extraction from the covariant 2-jet sum.**  The intrinsic squared fibre norm
of the tensor value is at most the squared 2-jet sum:

  `rfns(S)(x) ≤ (iteratedCovGradJetSum g₀ S x)²`.

The `j = 0` summand of the jet sum is the installed-bundle fibre norm `‖S(x)‖ = √(rfns(S)(x))`,
the remaining summands are nonnegative, and squaring is monotone on nonnegatives.  This converts
the (sharp-order) `C²` embedding into the pointwise `Λ²`-sup hypotheses
`rfns(S)(x) ≤ (C · ‖S.toHs m‖)²` of the integrated Gagliardo–Nirenberg two-arm engine.  Proved
outright; no posit. -/
theorem riemannianFiberNormSq_le_sq_iteratedCovGradJetSum
    (g₀ : SmoothRiemannianMetric I M) (S : SmoothCcTensor g₀ 0 2) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x (S.toSection x) ≤
      iteratedCovGradJetSum (I := I) g₀ S x ^ 2 := by
  classical
  have hterm_nn : ∀ j : ℕ, 0 ≤
      (letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 (2 + j) I b) :=
        Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 (2 + j)
      ‖(iteratedCovGrad (I := I) (M := M) g₀ 0 2 j S).toSection x‖) := by
    intro j
    letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 (2 + j) I b) :=
      Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 (2 + j)
    exact norm_nonneg _
  have h0 :
      (letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 (2 + 0) I b) :=
        Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 (2 + 0)
      ‖(iteratedCovGrad (I := I) (M := M) g₀ 0 2 0 S).toSection x‖) =
        Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x (S.toSection x)) := by
    letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 (2 + 0) I b) :=
      Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 (2 + 0)
    rw [riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g₀ 0 2 x (S.toSection x)]
    exact norm_eq_sqrt_tensorInnerPointwise (I := I) (M := M) g₀ 0 2 x (S.toSection x)
  have hle : Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x (S.toSection x)) ≤
      iteratedCovGradJetSum (I := I) g₀ S x := by
    rw [iteratedCovGradJetSum, ← h0]
    exact Finset.single_le_sum (f := fun j =>
        (letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 (2 + j) I b) :=
          Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 (2 + j)
        ‖(iteratedCovGrad (I := I) (M := M) g₀ 0 2 j S).toSection x‖))
      (fun j _ => hterm_nn j) (Finset.mem_range.mpr (by omega : (0 : ℕ) < 3))
  calc riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x (S.toSection x)
      = Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x (S.toSection x)) ^ 2 :=
        (Real.sq_sqrt (riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 2 x _)).symm
    _ ≤ iteratedCovGradJetSum (I := I) g₀ S x ^ 2 :=
        pow_le_pow_left₀ (Real.sqrt_nonneg _) hle 2

end MetricRealization
end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end
