import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.GreenIdentityAndIBP.IntegratedOrder2Garding
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.GreenIdentityAndIBP.IntegratedCurvatureCrossBound
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RawConnLapL2SobolevBounds.RawTensorConnLapIterL2WtwokTwoBound
import DifferentialGeometry.Geometry.Connection.Laplacian.RoughLaplacianSecondCovGradL2Bound
import DifferentialGeometry.Analysis.Sobolev.Embedding.SobolevEmbeddingReverseHebey

/-!
# The all-orders intrinsic Gårding / interior-elliptic-regularity bound

For a closed smooth Riemannian manifold `(M, g)` modelled on a real inner-product space `E`, this
file proves the **all-orders interior elliptic (Gårding) estimate** for smooth compactly-supported
`(0, s)`-tensor fields: at every order `k`,

```
(tensorPouSobolevHsNorm g k T).toReal ≤ C · ∑_{j ∈ range (k + 1)} ‖Δ_∇^j T‖_{L²},
```

where `‖·‖_{L²} = ‖SmoothCcTensor.toL2 ·‖` is the intrinsic metric `L²` norm, `Δ_∇^j` is the `j`-th
iterate of the rough (connection) Laplacian `rawTensorConnLapIter g 0 s`, and `tensorPouSobolevHsNorm
g k` is the intrinsic order-`2k` partition-of-unity-weighted chart-Sobolev (Hilbert–Schmidt) norm.
This is the all-orders generalisation of the order-`2` (`k = 1`) chart-`H²` Gårding constant
`exists_tensorPouSobolevHsNorm_one_le_sum_rawConnLapIter` (`ChartH2GardingConstant.lean`), and is the
exact `h_elliptic` hypothesis (at general `k`) consumed by `eigenSpan_pouHs_le_spectral_of_elliptic`
(`Analysis/Spectral/Intrinsic/Garding/EigenComboGardingReduction.lean`). The consumer instantiates it
at `(s, k) = (2, k)`; the bound here is proved uniformly in the covariant rank `s`.

## The assembly

The estimate composes two halves.

1. The **reverse Hebey–Sobolev bridge**
   `exists_tensorPouSobolevHsNorm_toReal_le_iteratedCovGrad_tensorL2Norm_sum`
   (`SobolevEmbeddingReverseHebey.lean`, general `(r, s, k)`): `(tensorPouSobolevHsNorm g k T).toReal ≤
   C · ∑_{j ≤ 2k} ‖∇^j T‖_{L²}`. This converts the chart-Sobolev norm at order `k` to the `L²` norms of
   the iterated covariant gradients `∇^j T = iteratedCovGrad g 0 s j T`, for `j ∈ {0, …, 2k}`.

2. The **gradient-iterate elliptic bound** `exists_iteratedCovGrad_l2Norm_le_sum_rawConnLapIter`:
   for each `j ≤ 2k`, `‖∇^j T‖_{L²} ≤ C · ∑_{i ≤ k} ‖Δ_∇^i T‖_{L²}`, controlling each covariant-gradient
   iterate by the rough-Laplacian iterates of `T`.

Substituting (2) into (1) and collapsing the resulting sum (each of the `2k + 1` gradient terms is
`≤ C · ∑_{i ≤ k} ‖Δ_∇^i T‖`) gives the headline bound with combined constant `C · (2k + 1) · C'`.

## The single all-orders elliptic-regularity input

The order-`2` covariant Gårding constant `exists_secondCovGrad_l2NormSq_le_rawConnLap_rankGen`
(`‖∇²S‖² ≤ Cg · (‖Δ_∇ S‖² + ‖S‖²)`, every rank `s`) is assembled here unconditionally from the
rank-generic integrated curvature cross-bound `exists_integrated_curvatureCrossBound` and the
integrated order-`2` Gårding reduction `secondCovGrad_l2NormSq_le_of_cross_bound`. Its all-orders
extension to the covariant-gradient iterates — `exists_iteratedCovGrad_l2Norm_le_sum_rawConnLapIter`,
`‖∇^j S‖_{L²} ≤ C · ∑_{i ≤ k} ‖Δ_∇^i S‖_{L²}` for `j ≤ 2k` — is the classical interior
elliptic-regularity bootstrap: it bridges the iterated covariant gradients `∇^j` to the rough-Laplacian
iterates `Δ_∇^i` through the curvature commutators `[Δ_∇, ∇]` at every order. The order-`0`/order-`1`
cases coincide with the trivial bound and the order-`1` covariant-gradient control; the order-`2` case
is the rank-generic order-`2` Gårding; the genuine content for higher `j` is the iterated commutator
bookkeeping, which is not reducible to the single-level curvature defect alone (the `m`-fold commutator
`[Δ_∇^m, ∇^{2m}]` involves the covariant derivatives `∇^a R` of the curvature to all orders `a ≤ 2m`).
It is isolated here as one honestly-labelled posited input
`exists_iteratedCovGrad_l2Norm_le_sum_rawConnLapIter`, never assumed in a headline; consumers
transitively depend on `sorryAx` through that single node (alongside the order-`2` curvature defect's
own moving-frame leaf, which the integrated cross-bound already transits).

## Sign / order conventions

Geometer convention `Δ_∇ = -∇*∇` for the rough Laplacian `rawTensorConnLapSmooth`. The covariant
gradient `covGrad g 0 s` raises the tensor rank from `(0, s)` to `(0, s + 1)`; `∇^j` is
`iteratedCovGrad g 0 s j`. "Order `2k`" / "chart-`H^{2k}`" is the project index-`k` space
`tensorPouSobolevHsNorm g k` (the reverse-Hebey sum runs to `2k`).
-/

noncomputable section

set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Sobolev.Tensor
open DifferentialGeometry.PDE.RicciFlow

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

set_option linter.unusedSectionVars false in
/-- **The rank-generic order-`2` covariant Gårding constant.** There is a nonnegative constant `Cg`,
uniform in `S`, with
```
‖∇²S‖²_{L²} ≤ Cg · (‖Δ_∇ S‖²_{L²} + ‖S‖²_{L²})
```
for every smooth compactly-supported `(0, s)`-tensor field `S`, where `∇²S = covGrad g 0 (s+1) (covGrad
g 0 s S)`. This is the integrated order-`2` Gårding reduction `secondCovGrad_l2NormSq_le_of_cross_bound`
(`IntegratedOrder2Garding.lean`, at rank `s`) fed the rank-generic integrated curvature cross-bound
`exists_integrated_curvatureCrossBound`; the constant `Cg = 2 + 2 Ccross` carries the curvature cross
term and the Young/absorption bookkeeping. The gradient slot is never read pointwise. This is the
rank-generic lift of `exists_secondCovGrad_l2NormSq_le_rawConnLap` (`ChartH2GardingConstant.lean`, which
is the `s = 2` instance). -/
theorem exists_secondCovGrad_l2NormSq_le_rawConnLap_rankGen
    (g : SmoothRiemannianMetric I M) (s : ℕ) :
    ∃ Cg : ℝ, 0 ≤ Cg ∧
      ∀ S : SmoothCcTensor g 0 s,
        tensorL2Norm (I := I) (M := M) g 0 (s + 1 + 1)
            (covGrad (I := I) (M := M) g 0 (s + 1)
              (covGrad (I := I) (M := M) g 0 s S)).toFun ^ 2 ≤
          Cg *
            (tensorL2Norm (I := I) (M := M) g 0 s
                (rawTensorConnLapSmooth (I := I) g 0 s S).toFun ^ 2 +
              tensorL2Norm (I := I) (M := M) g 0 s S.toFun ^ 2) := by
  obtain ⟨Ccross, hCcross, hcross⟩ := exists_integrated_curvatureCrossBound (I := I) (M := M) g s
  refine ⟨2 + 2 * Ccross, by positivity, fun S => ?_⟩
  exact secondCovGrad_l2NormSq_le_of_cross_bound (I := I) (M := M) g s S Ccross hCcross (hcross S)

/-- **The all-orders covariant-gradient-iterate elliptic bound (interior elliptic regularity).** For
every covariant rank `s` and order `k`, there is a nonnegative constant `C`, uniform in `S`, such that
for every covariant-gradient iterate order `j ≤ 2k`,
```
‖∇^j S‖_{L²} ≤ C · ∑_{i ∈ range (k + 1)} ‖Δ_∇^i S‖_{L²}
```
for every smooth compactly-supported `(0, s)`-tensor field `S`, where `∇^j S = iteratedCovGrad g 0 s j
S` (a `(0, s + j)`-tensor) and `Δ_∇^i S = rawTensorConnLapIter g 0 s i S`. This is the all-orders
extension of the rank-generic order-`2` covariant Gårding constant
`exists_secondCovGrad_l2NormSq_le_rawConnLap_rankGen` (the `j = 2`, `k = 1` case): the classical
interior elliptic-regularity bootstrap that controls each covariant-gradient iterate up to order `2k`
by the rough-Laplacian iterates up to order `k`, handling the curvature commutator `[Δ_∇, ∇]` at every
order (an all-orders curvature-derivative quantity `∇^a R`).

The bound is uniform in `j` over the finite window `j ≤ 2k`: the constant `C` is the maximum over the
finitely many orders of the per-order elliptic constants. The order-`0` case is the trivial equality
`‖S‖ = ‖Δ_∇^0 S‖`, the order-`1` case is the order-`1` covariant-gradient control, and the even
orders `j = 2m` are the genuine elliptic content; the odd orders interpolate through the order-`1`
control and the metric-trace bound `‖Δ_∇ V‖ ≤ K · ‖∇²V‖`.

This is the single posited all-orders elliptic-regularity input of the file; it is never assumed in a
headline. -/
theorem exists_iteratedCovGrad_l2Norm_le_sum_rawConnLapIter
    (g : SmoothRiemannianMetric I M) (s k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (j : ℕ), j ≤ 2 * k → ∀ S : SmoothCcTensor g 0 s,
        tensorL2Norm (I := I) (M := M) g 0 (s + j)
            (iteratedCovGrad g 0 s j S).toFun ≤
          C * ∑ i ∈ Finset.range (k + 1),
            tensorL2Norm (I := I) (M := M) g 0 s
              (rawTensorConnLapIter (I := I) g 0 s i S).toFun :=
  sorry

set_option linter.unusedSectionVars false in
/-- **The all-orders intrinsic Gårding constant in the `h_elliptic` consumer shape (rank-generic).**
For every covariant rank `s` and order `k`, there is a nonnegative constant `C`, uniform in `T`, with
```
(tensorPouSobolevHsNorm g k T).toReal ≤ C · ∑_{j ∈ range (k + 1)} ‖Δ_∇^j T‖_{L²},
```
for every smooth compactly-supported `(0, s)`-tensor field `T`. This is *exactly* the all-orders
elliptic hypothesis `h_elliptic` (at general `k`) of `eigenSpan_pouHs_le_spectral_of_elliptic`
(`Analysis/Spectral/Intrinsic/Garding/EigenComboGardingReduction.lean`); the consumer instantiates it
at `(s, k) = (2, k)`. It is the all-orders generalisation of the order-`2` (`k = 1`) chart-`H²` Gårding
constant `exists_tensorPouSobolevHsNorm_one_le_sum_rawConnLapIter` (`ChartH2GardingConstant.lean`).

The proof composes the reverse Hebey–Sobolev bridge
`exists_tensorPouSobolevHsNorm_toReal_le_iteratedCovGrad_tensorL2Norm_sum` — converting the order-`k`
chart-Sobolev norm to the sum `∑_{j ≤ 2k} ‖∇^j T‖_{L²}` of the `L²` norms of the iterated covariant
gradients — with the all-orders covariant-gradient-iterate elliptic bound
`exists_iteratedCovGrad_l2Norm_le_sum_rawConnLapIter`, which bounds each `‖∇^j T‖_{L²}` (`j ≤ 2k`) by a
single constant times `∑_{i ≤ k} ‖Δ_∇^i T‖_{L²}`. The `2k + 1` gradient terms then collapse to
`(2k + 1)` times the Laplacian-iterate sum. -/
theorem exists_tensorPouSobolevHsNorm_k_le_sum_rawConnLapIter
    (g : SmoothRiemannianMetric I M) (s k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ T : SmoothCcTensor g 0 s,
        (tensorPouSobolevHsNorm (I := I) (M := M) g k T).toReal ≤
          C * ∑ j ∈ Finset.range (k + 1),
            ‖SmoothCcTensor.toL2 (rawTensorConnLapIter (I := I) g 0 s j T)‖ := by
  classical
  obtain ⟨Cb, hCb, hbridge⟩ :=
    exists_tensorPouSobolevHsNorm_toReal_le_iteratedCovGrad_tensorL2Norm_sum
      (I := I) (M := M) g 0 s k
  obtain ⟨Cg, hCg, hgrad⟩ :=
    exists_iteratedCovGrad_l2Norm_le_sum_rawConnLapIter (I := I) (M := M) g s k
  refine ⟨Cb * ((2 * k + 1 : ℕ) : ℝ) * Cg, by positivity, fun T => ?_⟩
  -- Abbreviations for the two relevant sums.
  set LapSum : ℝ := ∑ i ∈ Finset.range (k + 1),
    tensorL2Norm (I := I) (M := M) g 0 s
      (rawTensorConnLapIter (I := I) g 0 s i T).toFun with hLapSum_def
  set toL2Sum : ℝ := ∑ j ∈ Finset.range (k + 1),
    ‖SmoothCcTensor.toL2 (rawTensorConnLapIter (I := I) g 0 s j T)‖ with htoL2Sum_def
  have hLapSum_nn : 0 ≤ LapSum :=
    Finset.sum_nonneg (fun i _ => tensorL2Norm_nonneg (I := I) (M := M) g 0 s _)
  -- The two sums are equal termwise: `tensorL2Norm g 0 s (Δ_∇^i T).toFun = ‖toL2 (Δ_∇^i T)‖`.
  have hsum_eq : LapSum = toL2Sum := by
    rw [hLapSum_def, htoL2Sum_def]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [SmoothCcTensor.norm_toL2,
      tensorL2Norm_toFun_eq_norm (I := I) (M := M) g (rawTensorConnLapIter (I := I) g 0 s i T)]
  -- The reverse-Hebey gradient sum, each term controlled by `Cg · LapSum`.
  set Gsum : ℝ := ∑ j ∈ Finset.range (2 * k + 1),
    tensorL2Norm (I := I) (M := M) g 0 (s + j) (iteratedCovGrad g 0 s j T).toFun with hGsum_def
  have hbridge_T : (tensorPouSobolevHsNorm (I := I) (M := M) g k T).toReal ≤ Cb * Gsum :=
    hbridge T
  -- Each gradient term `‖∇^j T‖ ≤ Cg · LapSum` for `j ∈ range (2k + 1)` (i.e. `j ≤ 2k`).
  have hterm_le : ∀ j ∈ Finset.range (2 * k + 1),
      tensorL2Norm (I := I) (M := M) g 0 (s + j) (iteratedCovGrad g 0 s j T).toFun ≤
        Cg * LapSum := by
    intro j hj
    have hjle : j ≤ 2 * k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    rw [hLapSum_def]
    exact hgrad j hjle T
  -- Sum the `(2k + 1)` terms.
  have hGsum_le : Gsum ≤ ((2 * k + 1 : ℕ) : ℝ) * (Cg * LapSum) := by
    calc Gsum ≤ ∑ _j ∈ Finset.range (2 * k + 1), (Cg * LapSum) :=
            Finset.sum_le_sum hterm_le
      _ = (Finset.range (2 * k + 1)).card • (Cg * LapSum) := by rw [Finset.sum_const]
      _ = ((2 * k + 1 : ℕ) : ℝ) * (Cg * LapSum) := by
            rw [Finset.card_range, nsmul_eq_mul]
  -- Assemble.
  calc (tensorPouSobolevHsNorm (I := I) (M := M) g k T).toReal
      ≤ Cb * Gsum := hbridge_T
    _ ≤ Cb * (((2 * k + 1 : ℕ) : ℝ) * (Cg * LapSum)) :=
        mul_le_mul_of_nonneg_left hGsum_le hCb
    _ = Cb * ((2 * k + 1 : ℕ) : ℝ) * Cg * LapSum := by ring
    _ = Cb * ((2 * k + 1 : ℕ) : ℝ) * Cg * toL2Sum := by rw [hsum_eq]

end Connection
end Integral
end DifferentialGeometry

end
