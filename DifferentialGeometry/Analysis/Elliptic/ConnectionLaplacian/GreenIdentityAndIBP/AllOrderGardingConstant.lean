import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.GreenIdentityAndIBP.IntegratedOrder2Garding
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.GreenIdentityAndIBP.IntegratedCurvatureCrossBound
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RawConnLapL2SobolevBounds.RawTensorConnLapIterL2WtwokTwoBound
import DifferentialGeometry.Geometry.Connection.Laplacian.RoughLaplacianSecondCovGradL2Bound
import DifferentialGeometry.Analysis.Sobolev.Embedding.SobolevEmbeddingReverseHebey
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.IteratedCovGradLinear
import DifferentialGeometry.Geometry.Connection.TensorNabla.HomFieldActionIteratedCovGradWindow
import DifferentialGeometry.Analysis.Sobolev.Embedding.RawConnLapToHsOrderDropping

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

/-- **Norm-level composition of iterated covariant gradients.** Applying `i` further covariant
gradients to the `j`-th covariant jet `∇^j S` produces a tensor whose intrinsic metric `L²` norm
equals that of the `(j + i)`-fold iterated gradient of `S`. The two sections live in the ranks
`(s + j) + i` and `s + (j + i)` (equal as naturals); their underlying fibre values are
heterogeneously equal, so the pointwise intrinsic fibre norms agree (`rfns_iteratedCovGrad_comp`) and
hence so do the integrated `L²` norms. -/
private theorem norm_iteratedCovGrad_comp
    (g : SmoothRiemannianMetric I M) (s j i : ℕ) (S : SmoothCcTensor g 0 s) :
    ‖iteratedCovGrad g 0 (s + j) i (iteratedCovGrad g 0 s j S)‖ =
      ‖iteratedCovGrad g 0 s (j + i) S‖ := by
  have hsq :
      ‖iteratedCovGrad g 0 (s + j) i (iteratedCovGrad g 0 s j S)‖ ^ 2 =
        ‖iteratedCovGrad g 0 s (j + i) S‖ ^ 2 := by
    rw [← tensorL2Norm_toFun_eq_norm (I := I) (M := M) g
        (iteratedCovGrad g 0 (s + j) i (iteratedCovGrad g 0 s j S)),
      ← tensorL2Norm_toFun_eq_norm (I := I) (M := M) g (iteratedCovGrad g 0 s (j + i) S),
      tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq (I := I) (M := M) g
        ((s + j) + i) (iteratedCovGrad g 0 (s + j) i (iteratedCovGrad g 0 s j S)),
      tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq (I := I) (M := M) g
        (s + (j + i)) (iteratedCovGrad g 0 s (j + i) S)]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    exact rfns_iteratedCovGrad_comp (I := I) (M := M) g 0 s j i S x
  have h1 : 0 ≤ ‖iteratedCovGrad g 0 (s + j) i (iteratedCovGrad g 0 s j S)‖ := norm_nonneg _
  have h2 : 0 ≤ ‖iteratedCovGrad g 0 s (j + i) S‖ := norm_nonneg _
  nlinarith [hsq, h1, h2]

/-- **The iterated-gradient `L²` bound of the single-level commutator defect (the all-orders
curvature-derivative input).** For a closed smooth Riemannian manifold `(M, g)` and every covariant
rank `s`, there is a nonnegative per-gradient-order constant family `K : ℕ → ℝ`, uniform in `S`, such
that for every gradient order `p` the `L²` norm of the `p`-fold covariant gradient of the single-level
rough-Laplacian / covariant-gradient commutator defect `pointwiseTensorCurv g s S = Δ_∇(∇S) − ∇(Δ_∇ S)`
is controlled by the covariant-gradient norms of `S` up to order `p + 1`:
```
‖∇^p (pointwiseTensorCurv g s S)‖_{L²} ≤ K p · ∑_{a ∈ range (p + 2)} ‖∇^a S‖_{L²},
```
for every smooth compactly-supported `(0, s)`-tensor field `S`, where `∇^a S = iteratedCovGrad g 0 s a
S` and `∇^p (·) = iteratedCovGrad g 0 (s + 1) p (·)`.

**Why this is TRUE (and the genuine carried content).** The defect is a *first-order* curvature
contraction of `(∇S, S)`: by the moving-frame third-order Bochner–Weitzenböck `∇²S`-elimination
(`pointwiseTensorCurv_fiberNormSq_le_first_order`) it equals a finite contraction of the Riemann
curvature `R` against `∇S` plus the differentiated curvature `∇R` against `S`. Differentiating `p`
times, the Leibniz rule produces a finite sum of contractions of the iterated curvature derivatives
`∇^q R` (`q ≤ p + 1`) against the gradients `∇^b S` (`b ≤ p + 1`); each `∇^q R` is a continuous, hence
uniformly fibre-bounded, field on the compact manifold, so the pointwise fibre norm of
`∇^p (defect)` is bounded by `(∑_q ‖∇^q R‖_∞)² · ∑_{b ≤ p + 1} rfns(∇^b S)`, which integrates to the
stated `L²` bound. This is exactly the all-orders `∇^a R` content the iterated commutator bookkeeping
needs, isolated here as one honestly-labelled node (the `p = 0` case is the rank-generic single-level
defect bound `exists_pointwiseTensorCurv_fiberNormSq_bound`, already proved sorry-free).

**Non-vacuity.** With `K p = 0` the bound forces `∇^p (pointwiseTensorCurv g s S) = 0` for all `S`; at
`p = 0` this is `pointwiseTensorCurv g s S = 0`, i.e. the rough Laplacian and the covariant gradient
commute, which is *false* on a non-flat manifold already at `s = 0` (the defect is the Ricci
contraction `Ric(∇f, ·) ≠ 0` on a positively-curved `M`). So the constant family `K` genuinely
envelopes the per-order curvature-derivative sups. It is never assumed in a headline; consumers
transitively depend on `sorryAx` through this single all-orders curvature node. -/
theorem exists_iteratedCovGrad_pointwiseTensorCurv_l2Norm_le
    (g : SmoothRiemannianMetric I M) (s : ℕ) :
    ∃ K : ℕ → ℝ, (∀ p, 0 ≤ K p) ∧
      ∀ (p : ℕ) (S : SmoothCcTensor g 0 s),
        ‖iteratedCovGrad g 0 (s + 1) p (pointwiseTensorCurv (I := I) (M := M) g s S)‖ ≤
          K p * ∑ a ∈ Finset.range (p + 2), ‖iteratedCovGrad g 0 s a S‖ :=
  sorry

/-! ### The iterated rough-Laplacian / covariant-gradient commutator

The bootstrap below rests on one all-orders curvature input: the `m`-fold *iterated commutator*
`[Δ_∇, ∇^m]S = Δ_∇(∇^m S) − ∇^m(Δ_∇ S)`. Unrolling the single-level defect
`covGradRoughLapCurv_gen g s' S' = Δ_∇(∇S') − ∇(Δ_∇ S')` one slot at a time, the `m`-fold commutator
expands into a finite sum of contractions of the covariant derivatives `∇^a R` (`a ≤ m`) of the
Riemann curvature against the gradients `∇^b S` (`b ≤ m`), all of which are uniformly fibre-bounded on
the compact manifold (each `∇^a R` is a continuous, hence bounded, field). Consequently the `L²` norm
of the iterated commutator is controlled by the gradient norms `‖∇^a S‖_{L²}` for `a ≤ m`. -/

set_option linter.style.show false in
/-- **The strengthened telescoping induction for the iterated commutator.** Proved by induction on the
commutator order `m`, simultaneously for ALL covariant ranks `s` and ALL extra gradient orders `p`:
there is a per-gradient-order constant family `Cfun : ℕ → ℝ`, uniform in `S`, with
```
‖∇^p ([Δ_∇, ∇^m] S)‖_{L²} ≤ Cfun p · ∑_{a ∈ range (m + p + 1)} ‖∇^a S‖_{L²},
```
where `[Δ_∇, ∇^m] S = Δ_∇(∇^m S) − ∇^m(Δ_∇ S)` (`∇^m S = iteratedCovGrad g 0 s m S`,
`Δ_∇ = rawTensorConnLapSmooth`) and `∇^p (·) = iteratedCovGrad g 0 (s + m) p (·)`.

The `p`-simultaneous strengthening is what makes the telescope close: the recursion
`[Δ_∇, ∇^{m+1}] S = pointwiseTensorCurv g (s + m) (∇^m S) + ∇([Δ_∇, ∇^m] S)`
(the single-level commutator equation `pointwiseTensorCurv_commutator_eq` at rank `s + m` applied to
`∇^m S`, peeling the outermost gradient) makes `∇^p` of the second arm an `(p + 1)`-fold gradient of
the order-`m` commutator — handled by the induction hypothesis at gradient order `p + 1` — while
`∇^p` of the first arm is the posited iterated-gradient defect bound
`exists_iteratedCovGrad_pointwiseTensorCurv_l2Norm_le` at rank `s + m`, whose `∇^m S`-jets reindex onto
the `S`-jets `∇^{m + a} S` (`norm_iteratedCovGrad_comp`). Both arms land in the order budget
`∑_{a ∈ range ((m + 1) + p + 1)}`, so `Cfun_{m+1} p := K p + Cfun_m (p + 1)`. The base `m = 0` is the
vanishing commutator `[Δ_∇, ∇^0] S = Δ_∇ S − Δ_∇ S = 0`. -/
private theorem iteratedRoughLapGrad_commutator_l2Norm_le_aux
    (g : SmoothRiemannianMetric I M) (m : ℕ) :
    ∀ s : ℕ, ∃ Cfun : ℕ → ℝ, (∀ p, 0 ≤ Cfun p) ∧
      ∀ (p : ℕ) (S : SmoothCcTensor g 0 s),
        ‖iteratedCovGrad g 0 (s + m) p
            (rawTensorConnLapSmooth (I := I) g 0 (s + m) (iteratedCovGrad g 0 s m S) -
              iteratedCovGrad g 0 s m (rawTensorConnLapSmooth (I := I) g 0 s S))‖ ≤
          Cfun p * ∑ a ∈ Finset.range (m + p + 1), ‖iteratedCovGrad g 0 s a S‖ := by
  induction m with
  | zero =>
    intro s
    refine ⟨fun _ => 0, fun _ => le_refl _, fun p S => ?_⟩
    -- `[Δ_∇, ∇^0] S = Δ_∇ S − Δ_∇ S = 0`, so its `p`-fold gradient is `0`.
    have hcomm0 :
        rawTensorConnLapSmooth (I := I) g 0 (s + 0) (iteratedCovGrad g 0 s 0 S) -
            iteratedCovGrad g 0 s 0 (rawTensorConnLapSmooth (I := I) g 0 s S) =
          (0 : SmoothCcTensor g 0 (s + 0)) := by
      simp only [iteratedCovGrad_zero, Nat.add_zero, sub_self]
    rw [hcomm0]
    have hz : iteratedCovGrad g 0 (s + 0) p (0 : SmoothCcTensor g 0 (s + 0)) =
        (0 : SmoothCcTensor g 0 (s + 0 + p)) := by
      have := iteratedCovGrad_sub (I := I) (M := M) g 0 (s + 0) p
        (0 : SmoothCcTensor g 0 (s + 0)) (0 : SmoothCcTensor g 0 (s + 0))
      simpa using this
    rw [hz, norm_zero]
    exact mul_nonneg (le_refl 0) (Finset.sum_nonneg (fun a _ => norm_nonneg _))
  | succ m ih =>
    intro s
    -- The order-`m` constant at the SAME rank `s` (the induction hypothesis), and the posited
    -- iterated-gradient defect constant at the shifted rank `s + m`.
    obtain ⟨Cm, hCm_nn, hCm⟩ := ih s
    obtain ⟨K, hK_nn, hK⟩ :=
      exists_iteratedCovGrad_pointwiseTensorCurv_l2Norm_le (I := I) (M := M) g (s + m)
    refine ⟨fun p => K p + Cm (p + 1), fun p => add_nonneg (hK_nn p) (hCm_nn (p + 1)),
      fun p S => ?_⟩
    -- The telescoping algebraic identity at the section level (fully explicit):
    -- `[Δ_∇, ∇^{m+1}] S = pointwiseTensorCurv g (s+m) (∇^m S) + ∇([Δ_∇, ∇^m] S)`.
    have hsplit :
        rawTensorConnLapSmooth (I := I) g 0 (s + (m + 1)) (iteratedCovGrad g 0 s (m + 1) S) -
            iteratedCovGrad g 0 s (m + 1) (rawTensorConnLapSmooth (I := I) g 0 s S) =
          pointwiseTensorCurv (I := I) (M := M) g (s + m) (iteratedCovGrad g 0 s m S) +
            covGrad (I := I) (M := M) g 0 (s + m)
              (rawTensorConnLapSmooth (I := I) g 0 (s + m) (iteratedCovGrad g 0 s m S) -
                iteratedCovGrad g 0 s m (rawTensorConnLapSmooth (I := I) g 0 s S)) := by
      rw [iteratedCovGrad_succ (I := I) (M := M) g 0 s m S,
        iteratedCovGrad_succ (I := I) (M := M) g 0 s m
          (rawTensorConnLapSmooth (I := I) g 0 s S)]
      show rawTensorConnLapSmooth (I := I) g 0 (s + m + 1)
            (covGrad (I := I) (M := M) g 0 (s + m) (iteratedCovGrad g 0 s m S)) -
          covGrad (I := I) (M := M) g 0 (s + m)
            (iteratedCovGrad g 0 s m (rawTensorConnLapSmooth (I := I) g 0 s S)) =
        pointwiseTensorCurv (I := I) (M := M) g (s + m) (iteratedCovGrad g 0 s m S) +
          covGrad (I := I) (M := M) g 0 (s + m)
            (rawTensorConnLapSmooth (I := I) g 0 (s + m) (iteratedCovGrad g 0 s m S) -
              iteratedCovGrad g 0 s m (rawTensorConnLapSmooth (I := I) g 0 s S))
      rw [pointwiseTensorCurv_commutator_eq (I := I) (M := M) g (s + m)
          (iteratedCovGrad g 0 s m S),
        covGrad_sub (I := I) (M := M) g 0 (s + m)]
      abel
    -- Abbreviations.
    set comm_m : SmoothCcTensor g 0 (s + m) :=
      rawTensorConnLapSmooth (I := I) g 0 (s + m) (iteratedCovGrad g 0 s m S) -
        iteratedCovGrad g 0 s m (rawTensorConnLapSmooth (I := I) g 0 s S) with hcomm_m
    set gradm : SmoothCcTensor g 0 (s + m) := iteratedCovGrad g 0 s m S with hgradm
    set fullSum : ℝ := ∑ a ∈ Finset.range (m + 1 + p + 1),
      ‖iteratedCovGrad g 0 s a S‖ with hfullSum
    have hfullSum_nn : 0 ≤ fullSum :=
      Finset.sum_nonneg (fun a _ => norm_nonneg _)
    -- The `p`-fold gradient of the split, distributed by `iteratedCovGrad_add`.
    rw [hsplit, iteratedCovGrad_add (I := I) (M := M) g 0 (s + (m + 1)) p]
    -- Bound by the triangle inequality.
    refine le_trans (norm_add_le _ _) ?_
    -- Arm 1: the posited iterated-gradient defect bound at rank `s + m`, applied to `∇^m S`.
    have harm1 :
        ‖iteratedCovGrad g 0 (s + (m + 1)) p
            (pointwiseTensorCurv (I := I) (M := M) g (s + m) gradm)‖ ≤
          K p * fullSum := by
      have hKb := hK p gradm
      -- Reindex the `∇^m S`-jets `∇^a (∇^m S)` onto the `S`-jets `∇^{m + a} S`.
      have hreindex : ∀ a, ‖iteratedCovGrad g 0 (s + m) a gradm‖ =
          ‖iteratedCovGrad g 0 s (m + a) S‖ := by
        intro a
        rw [hgradm, norm_iteratedCovGrad_comp (I := I) (M := M) g s m a S]
      rw [Finset.sum_congr rfl (fun a _ => hreindex a)] at hKb
      -- The reindexed sum `∑_{a < p + 2} ‖∇^{m + a} S‖` injects into `fullSum`.
      have hsub : ∑ a ∈ Finset.range (p + 2), ‖iteratedCovGrad g 0 s (m + a) S‖ ≤ fullSum := by
        rw [hfullSum]
        have hIco : ∑ a ∈ Finset.range (p + 2), ‖iteratedCovGrad g 0 s (m + a) S‖ =
            ∑ b ∈ Finset.Ico m (m + (p + 2)), ‖iteratedCovGrad g 0 s b S‖ := by
          rw [Finset.sum_Ico_eq_sum_range]
          refine Finset.sum_congr ?_ (fun a _ => rfl)
          congr 1
          omega
        rw [hIco]
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun b _ _ => norm_nonneg _)
        intro b hb
        rw [Finset.mem_Ico] at hb
        rw [Finset.mem_range]
        omega
      calc ‖iteratedCovGrad g 0 (s + (m + 1)) p
              (pointwiseTensorCurv (I := I) (M := M) g (s + m) gradm)‖
          ≤ K p * ∑ a ∈ Finset.range (p + 2), ‖iteratedCovGrad g 0 s (m + a) S‖ := hKb
        _ ≤ K p * fullSum := mul_le_mul_of_nonneg_left hsub (hK_nn p)
    -- Arm 2: the induction hypothesis at gradient order `p + 1` on `[Δ_∇, ∇^m] S`.
    have harm2 :
        ‖iteratedCovGrad g 0 (s + (m + 1)) p
            (covGrad (I := I) (M := M) g 0 (s + m) comm_m)‖ ≤
          Cm (p + 1) * fullSum := by
      -- `∇^p (∇ comm_m) = ∇^{p+1} comm_m` up to the norm-composition.
      have hcomp :
          ‖iteratedCovGrad g 0 (s + (m + 1)) p
              (covGrad (I := I) (M := M) g 0 (s + m) comm_m)‖ =
            ‖iteratedCovGrad g 0 (s + m) (p + 1) comm_m‖ := by
        have h := norm_iteratedCovGrad_comp (I := I) (M := M) g (s + m) 1 p comm_m
        rw [Nat.add_comm 1 p] at h
        exact h
      rw [hcomp]
      have hCmb := hCm (p + 1) S
      rw [← hcomm_m] at hCmb
      -- `m + (p + 1) + 1 = m + 1 + p + 1`, so the order budget matches `fullSum`.
      have hsum_eq : ∑ a ∈ Finset.range (m + (p + 1) + 1), ‖iteratedCovGrad g 0 s a S‖ = fullSum := by
        rw [hfullSum, show m + (p + 1) + 1 = m + 1 + p + 1 from by omega]
      rw [hsum_eq] at hCmb
      exact hCmb
    -- Assemble: both arms over the common sum `fullSum`.
    have hfinal : K p * fullSum + Cm (p + 1) * fullSum =
        (K p + Cm (p + 1)) * fullSum := by ring
    calc ‖iteratedCovGrad g 0 (s + (m + 1)) p
            (pointwiseTensorCurv (I := I) (M := M) g (s + m) gradm)‖ +
          ‖iteratedCovGrad g 0 (s + (m + 1)) p
            (covGrad (I := I) (M := M) g 0 (s + m) comm_m)‖
        ≤ K p * fullSum + Cm (p + 1) * fullSum := add_le_add harm1 harm2
      _ = (K p + Cm (p + 1)) * fullSum := hfinal

/-- **The `m`-fold iterated rough-Laplacian / covariant-gradient commutator (all-orders).** For a
closed smooth Riemannian manifold `(M, g)`, every covariant rank `s`, and every order `m`, there is a
nonnegative constant `C`, uniform in `S`, such that the `L²` norm of the `m`-fold commutator
```
[Δ_∇, ∇^m] S := Δ_∇(∇^m S) − ∇^m(Δ_∇ S)
            =  rawTensorConnLapSmooth g 0 (s + m) (∇^m S) − ∇^m (rawTensorConnLapSmooth g 0 s S)
```
is bounded by the covariant-gradient norms of `S` up to order `m`:
```
‖[Δ_∇, ∇^m] S‖_{L²} ≤ C · ∑_{a ∈ range (m + 1)} ‖∇^a S‖_{L²},
```
for every smooth compactly-supported `(0, s)`-tensor field `S`, where `∇^a S = iteratedCovGrad g 0 s a
S`.

**Why this is TRUE (and the genuine carried content).** The single-level defect
`covGradRoughLapCurv_gen g s' S' = Δ_∇(∇S') − ∇(Δ_∇ S')` is, by the moving-frame third-order
Bochner–Weitzenböck `∇²S`-elimination (`pointwiseTensorCurv_fiberNormSq_le_first_order`), a *first-order*
curvature contraction of `(∇S', S')`: `√(rfns(defect)) ≤ K_R √(rfns(∇S')) + K_{dR} √(rfns(S'))`. The
`m`-fold commutator telescopes through this single-level defect: passing `Δ_∇` outward across each of
the `m` gradient slots produces `m` differentiated copies of the single-level defect, whose pointwise
fibre norms are bounded by the curvature derivatives `∇^a R` (`a ≤ m`, each a continuous field on the
compact `M`, hence uniformly bounded) contracted against the gradients `∇^b S` (`b ≤ m`). Integrating
the finitely many pointwise bounds gives the `L²` estimate.

**Non-vacuity.** With `C = 0` the bound forces `[Δ_∇, ∇^m] S = 0` for all `S`, i.e. the rough Laplacian
and the iterated covariant gradient commute; this is *false* on a non-flat manifold already at `m = 1`,
`s = 0`, where the defect is the Ricci contraction `Ric(∇f, ·) ≠ 0` on a positively-curved `M`. So the
constant `C` genuinely envelopes the per-order curvature-derivative sups.

It is the all-orders (`m`-fold) extension of the `m = 1` single-level defect bound — itself the
rank-generic integrated cross-bound `exists_integrated_curvatureCrossBound` assembled from the
first-order fibre leaf `pointwiseTensorCurv_fiberNormSq_le_first_order`. The telescope below rests on
the single posited all-orders curvature-derivative node
`exists_iteratedCovGrad_pointwiseTensorCurv_l2Norm_le` (the iterated-gradient `L²` bound of the
single-level defect); it is never assumed in a headline; consumers transitively depend on `sorryAx`
through that node alongside the first-order curvature leaf. -/
theorem exists_iteratedRoughLapGrad_commutator_l2Norm_le
    (g : SmoothRiemannianMetric I M) (s m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ S : SmoothCcTensor g 0 s,
        ‖rawTensorConnLapSmooth (I := I) g 0 (s + m) (iteratedCovGrad g 0 s m S) -
            iteratedCovGrad g 0 s m (rawTensorConnLapSmooth (I := I) g 0 s S)‖ ≤
          C * ∑ a ∈ Finset.range (m + 1), ‖iteratedCovGrad g 0 s a S‖ := by
  obtain ⟨Cfun, _hCfun_nn, hbound⟩ :=
    iteratedRoughLapGrad_commutator_l2Norm_le_aux (I := I) (M := M) g m s
  refine ⟨Cfun 0, _hCfun_nn 0, fun S => ?_⟩
  have h := hbound 0 S
  simpa only [iteratedCovGrad_zero, Nat.add_zero, Nat.add_zero] using h

/-- The inner-applied iterate shift: applying `i` rough Laplacians to `Δ_∇ S` is the `(i + 1)`-th
iterate of `S`. Both unfold to `i + 1` successive applications of `rawTensorConnLapSmooth`. -/
private theorem rawTensorConnLapIter_rawTensorConnLapSmooth
    (g : SmoothRiemannianMetric I M) (s : ℕ) (i : ℕ) (S : SmoothCcTensor g 0 s) :
    rawTensorConnLapIter (I := I) g 0 s i (rawTensorConnLapSmooth (I := I) g 0 s S) =
      rawTensorConnLapIter (I := I) g 0 s (i + 1) S := by
  induction i with
  | zero => rfl
  | succ n ih =>
    rw [rawTensorConnLapIter_succ (I := I) g 0 s n
          (rawTensorConnLapSmooth (I := I) g 0 s S),
        ih, rawTensorConnLapIter_succ (I := I) g 0 s (n + 1) S]

/-- `‖·‖`-form of the rank-generic order-`1` covariant-gradient control
`covGrad_l2NormSq_le_rawConnLap_mul_self_gen`: `‖∇S‖² ≤ ‖Δ_∇ S‖ · ‖S‖`. -/
private theorem covGrad_norm_sq_le_rawConnLap_mul_self
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) :
    ‖covGrad (I := I) (M := M) g 0 s S‖ ^ 2 ≤
      ‖rawTensorConnLapSmooth (I := I) g 0 s S‖ * ‖S‖ := by
  have h := covGrad_l2NormSq_le_rawConnLap_mul_self_gen (I := I) (M := M) g s S
  rwa [tensorL2Norm_toFun_eq_norm (I := I) (M := M) g (covGrad (I := I) (M := M) g 0 s S),
    tensorL2Norm_toFun_eq_norm (I := I) (M := M) g (rawTensorConnLapSmooth (I := I) g 0 s S),
    tensorL2Norm_toFun_eq_norm (I := I) (M := M) g S] at h

/-- `‖·‖`-form of the rank-generic order-`2` covariant Gårding constant
`exists_secondCovGrad_l2NormSq_le_rawConnLap_rankGen`: for a single nonnegative `Cg`, uniform in `S`,
`‖∇²S‖² ≤ Cg · (‖Δ_∇ S‖² + ‖S‖²)`, where `∇²S = covGrad g 0 (s + 1) (covGrad g 0 s S)`. -/
private theorem exists_secondCovGrad_norm_sq_le_rawConnLap
    (g : SmoothRiemannianMetric I M) (s : ℕ) :
    ∃ Cg : ℝ, 0 ≤ Cg ∧
      ∀ S : SmoothCcTensor g 0 s,
        ‖covGrad (I := I) (M := M) g 0 (s + 1) (covGrad (I := I) (M := M) g 0 s S)‖ ^ 2 ≤
          Cg * (‖rawTensorConnLapSmooth (I := I) g 0 s S‖ ^ 2 + ‖S‖ ^ 2) := by
  obtain ⟨Cg, hCg, hbound⟩ := exists_secondCovGrad_l2NormSq_le_rawConnLap_rankGen (I := I) (M := M) g s
  refine ⟨Cg, hCg, fun S => ?_⟩
  have h := hbound S
  rwa [tensorL2Norm_toFun_eq_norm (I := I) (M := M) g
        (covGrad (I := I) (M := M) g 0 (s + 1) (covGrad (I := I) (M := M) g 0 s S)),
      tensorL2Norm_toFun_eq_norm (I := I) (M := M) g (rawTensorConnLapSmooth (I := I) g 0 s S),
      tensorL2Norm_toFun_eq_norm (I := I) (M := M) g S] at h

/-- The two-slot covariant gradient `covGrad g 0 (s + 1) (covGrad g 0 s S)` is the order-`2` iterated
covariant gradient `∇²S = iteratedCovGrad g 0 s 2 S` (definitionally, by `iteratedCovGrad_succ`). -/
private theorem covGrad_covGrad_eq_iteratedCovGrad_two
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) :
    covGrad (I := I) (M := M) g 0 (s + 1) (covGrad (I := I) (M := M) g 0 s S) =
      iteratedCovGrad g 0 s 2 S := rfl

/-- The order-`(j + 2)` iterated covariant gradient is the order-`2` two-slot gradient of the
order-`j` gradient: `∇^{j+2}S = covGrad (covGrad (∇^j S))`. The two outer slots are added on the
outside, so this is definitional. -/
private theorem iteratedCovGrad_add_two
    (g : SmoothRiemannianMetric I M) (s j : ℕ) (S : SmoothCcTensor g 0 s) :
    iteratedCovGrad g 0 s (j + 2) S =
      covGrad (I := I) (M := M) g 0 (s + j + 1)
        (covGrad (I := I) (M := M) g 0 (s + j) (iteratedCovGrad g 0 s j S)) := rfl

/-- `Δ_∇(∇^m S) = ∇^m(Δ_∇ S) + [Δ_∇, ∇^m]S`: the iterated commutator splits the rough Laplacian of
the gradient iterate into the gradient iterate of the rough Laplacian plus the commutator defect. -/
private theorem rawConnLap_iteratedCovGrad_eq_iteratedCovGrad_rawConnLap_add_comm
    (g : SmoothRiemannianMetric I M) (s m : ℕ) (S : SmoothCcTensor g 0 s) :
    rawTensorConnLapSmooth (I := I) g 0 (s + m) (iteratedCovGrad g 0 s m S) =
      iteratedCovGrad g 0 s m (rawTensorConnLapSmooth (I := I) g 0 s S) +
        (rawTensorConnLapSmooth (I := I) g 0 (s + m) (iteratedCovGrad g 0 s m S) -
          iteratedCovGrad g 0 s m (rawTensorConnLapSmooth (I := I) g 0 s S)) := by
  abel

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

The proof is a strong induction on `k`, proving the bound for *all* `j ≤ 2k` simultaneously with a
single constant. The base `k = 0` is the trivial equality `‖∇^0 S‖ = ‖S‖ = ‖Δ_∇^0 S‖`. The step
`k → k + 1` reaches the two new orders `j = 2k + 1` and `j = 2k + 2` from the order-`1` covariant
control and the order-`2` Gårding constant applied to `∇^{2k} S`, splitting the appearing
`Δ_∇(∇^{2k} S)` into `∇^{2k}(Δ_∇ S) + [Δ_∇, ∇^{2k}]S`: the first folds into the induction hypothesis
applied to `Δ_∇ S` (one fewer Laplacian budget), and the iterated commutator
`[Δ_∇, ∇^{2k}]S` is the posited all-orders curvature input
`exists_iteratedRoughLapGrad_commutator_l2Norm_le`, controlled by the gradients `∇^{≤2k} S` — which
fold back into the same induction hypothesis. -/
theorem exists_iteratedCovGrad_l2Norm_le_sum_rawConnLapIter
    (g : SmoothRiemannianMetric I M) (s k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (j : ℕ), j ≤ 2 * k → ∀ S : SmoothCcTensor g 0 s,
        tensorL2Norm (I := I) (M := M) g 0 (s + j)
            (iteratedCovGrad g 0 s j S).toFun ≤
          C * ∑ i ∈ Finset.range (k + 1),
            tensorL2Norm (I := I) (M := M) g 0 s
              (rawTensorConnLapIter (I := I) g 0 s i S).toFun := by
  classical
  -- Work in the `SmoothCcTensor` norm `‖·‖` throughout; convert at the end.
  -- `lapSum r S := ∑ i ∈ range (r + 1), ‖Δ_∇^i S‖` (the order-`r` Laplacian-iterate sum).
  -- The whole statement is proved, uniformly in `s`, in the abbreviation `‖·‖`.
  suffices h : ∀ s : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ (j : ℕ), j ≤ 2 * k → ∀ S : SmoothCcTensor g 0 s,
        ‖iteratedCovGrad g 0 s j S‖ ≤
          C * ∑ i ∈ Finset.range (k + 1), ‖rawTensorConnLapIter (I := I) g 0 s i S‖ by
    obtain ⟨C, hC, hbound⟩ := h s
    refine ⟨C, hC, fun j hj S => ?_⟩
    have hb := hbound j hj S
    rw [tensorL2Norm_toFun_eq_norm (I := I) (M := M) g (iteratedCovGrad g 0 s j S)]
    refine le_trans hb (le_of_eq ?_)
    simp only [tensorL2Norm_toFun_eq_norm (I := I) (M := M) g]
  -- Induct on `k`, proving the bound for ALL ranks `s` simultaneously (so that the induction
  -- hypothesis can be applied at the shifted rank `s` to `Δ_∇ S` and to the gradient iterates).
  induction k with
  | zero =>
    intro s
    refine ⟨1, by norm_num, fun j hj S => ?_⟩
    have hj0 : j = 0 := by omega
    subst hj0
    rw [iteratedCovGrad_zero, Finset.sum_range_one, rawTensorConnLapIter_zero, one_mul]
  | succ n ih =>
    intro s
    -- Notation: `lapSum r S := ∑ i ∈ range (r + 1), ‖Δ_∇^i S‖`.
    set lapSum : ∀ r : ℕ, SmoothCcTensor g 0 s → ℝ :=
      fun r S => ∑ i ∈ Finset.range (r + 1), ‖rawTensorConnLapIter (I := I) g 0 s i S‖
      with hlapSum_def
    -- Order-`1` and order-`2` constants at the relevant ranks.
    obtain ⟨Cn, hCn_nn, hCn⟩ := ih s
    -- The induction hypothesis at the shifted rank `s` for `Δ_∇ S` and for the gradient iterates
    -- is just `hCn` itself (same rank `s`).
    obtain ⟨Cg, hCg_nn, hgard⟩ := exists_secondCovGrad_norm_sq_le_rawConnLap (I := I) (M := M) g (s + 2 * n)
    obtain ⟨Ccomm, hCcomm_nn, hcomm⟩ :=
      exists_iteratedRoughLapGrad_commutator_l2Norm_le (I := I) (M := M) g s (2 * n)
    -- The combined "step" constant for the new orders.
    set P : ℝ := Cn + Ccomm * ((2 * n + 1 : ℕ) : ℝ) * Cn with hP_def
    have hP_nn : 0 ≤ P := by
      have : 0 ≤ Ccomm * ((2 * n + 1 : ℕ) : ℝ) * Cn :=
        mul_nonneg (mul_nonneg hCcomm_nn (by positivity)) hCn_nn
      positivity
    set C2 : ℝ := Real.sqrt (Cg * (P ^ 2 + Cn ^ 2)) with hC2_def
    set C1 : ℝ := Real.sqrt (P * Cn) with hC1_def
    refine ⟨max Cn (max C2 C1), le_trans hCn_nn (le_max_left _ _), fun j hj S => ?_⟩
    -- Basic facts about `lapSum`.
    have hlapSum_nn : ∀ r, 0 ≤ lapSum r S := fun r =>
      Finset.sum_nonneg (fun i _ => norm_nonneg _)
    -- Monotonicity in the order: `lapSum n S ≤ lapSum (n + 1) S`.
    have hlapSum_mono : lapSum n S ≤ lapSum (n + 1) S := by
      simp only [hlapSum_def]
      rw [Finset.sum_range_succ
        (fun i => ‖rawTensorConnLapIter (I := I) g 0 s i S‖) (n + 1)]
      have := norm_nonneg (rawTensorConnLapIter (I := I) g 0 s (n + 1) S)
      linarith
    -- `‖∇^i S‖ ≤ Cn · lapSum n S` for `i ≤ 2n` (the induction hypothesis at rank `s`).
    have hgrad_le : ∀ i : ℕ, i ≤ 2 * n → ‖iteratedCovGrad g 0 s i S‖ ≤ Cn * lapSum n S := by
      intro i hi
      have := hCn i hi S
      rwa [hlapSum_def]
    -- The induction hypothesis applied to `Δ_∇ S` at order `2n`, reindexed: it yields
    -- `‖∇^{2n}(Δ_∇ S)‖ ≤ Cn · ∑_{i≤n} ‖Δ^{i+1} S‖ ≤ Cn · lapSum (n + 1) S`.
    have hgrad_lap_le :
        ‖iteratedCovGrad g 0 s (2 * n) (rawTensorConnLapSmooth (I := I) g 0 s S)‖ ≤
          Cn * lapSum (n + 1) S := by
      have hih := hCn (2 * n) (le_refl _) (rawTensorConnLapSmooth (I := I) g 0 s S)
      -- Reindex the Laplacian-iterate sum of `Δ_∇ S` into the order-`(n+1)` sum of `S`.
      have hreindex :
          ∑ i ∈ Finset.range (n + 1),
              ‖rawTensorConnLapIter (I := I) g 0 s i (rawTensorConnLapSmooth (I := I) g 0 s S)‖ ≤
            lapSum (n + 1) S := by
        have hterm : ∀ i ∈ Finset.range (n + 1),
            ‖rawTensorConnLapIter (I := I) g 0 s i (rawTensorConnLapSmooth (I := I) g 0 s S)‖ =
              ‖rawTensorConnLapIter (I := I) g 0 s (i + 1) S‖ := by
          intro i _
          rw [rawTensorConnLapIter_rawTensorConnLapSmooth (I := I) (M := M) g s i S]
        rw [Finset.sum_congr rfl hterm]
        rw [hlapSum_def]
        simp only
        -- `∑_{i ∈ range (n+1)} ‖Δ^{i+1} S‖ ≤ ∑_{i ∈ range (n+2)} ‖Δ^i S‖`.
        rw [Finset.sum_range_succ' (fun i => ‖rawTensorConnLapIter (I := I) g 0 s i S‖) (n + 1)]
        have : (0 : ℝ) ≤ ‖rawTensorConnLapIter (I := I) g 0 s 0 S‖ := norm_nonneg _
        linarith
      calc ‖iteratedCovGrad g 0 s (2 * n) (rawTensorConnLapSmooth (I := I) g 0 s S)‖
          ≤ Cn * ∑ i ∈ Finset.range (n + 1),
              ‖rawTensorConnLapIter (I := I) g 0 s i (rawTensorConnLapSmooth (I := I) g 0 s S)‖ := hih
        _ ≤ Cn * lapSum (n + 1) S := by
            exact mul_le_mul_of_nonneg_left hreindex hCn_nn
    -- The commutator term `‖[Δ_∇, ∇^{2n}] S‖ ≤ Ccomm · (2n+1) · Cn · lapSum (n+1) S`.
    have hcomm_le :
        ‖rawTensorConnLapSmooth (I := I) g 0 (s + 2 * n) (iteratedCovGrad g 0 s (2 * n) S) -
            iteratedCovGrad g 0 s (2 * n) (rawTensorConnLapSmooth (I := I) g 0 s S)‖ ≤
          Ccomm * ((2 * n + 1 : ℕ) : ℝ) * Cn * lapSum (n + 1) S := by
      have hc := hcomm S
      -- Bound the commutator's gradient sum: each `‖∇^a S‖ ≤ Cn · lapSum n S` for `a ≤ 2n`.
      have hsum_le :
          ∑ a ∈ Finset.range (2 * n + 1), ‖iteratedCovGrad g 0 s a S‖ ≤
            ((2 * n + 1 : ℕ) : ℝ) * (Cn * lapSum n S) := by
        calc ∑ a ∈ Finset.range (2 * n + 1), ‖iteratedCovGrad g 0 s a S‖
            ≤ ∑ _a ∈ Finset.range (2 * n + 1), (Cn * lapSum n S) :=
              Finset.sum_le_sum (fun a ha =>
                hgrad_le a (Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)))
          _ = ((2 * n + 1 : ℕ) : ℝ) * (Cn * lapSum n S) := by
              rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      calc ‖rawTensorConnLapSmooth (I := I) g 0 (s + 2 * n) (iteratedCovGrad g 0 s (2 * n) S) -
              iteratedCovGrad g 0 s (2 * n) (rawTensorConnLapSmooth (I := I) g 0 s S)‖
          ≤ Ccomm * ∑ a ∈ Finset.range (2 * n + 1), ‖iteratedCovGrad g 0 s a S‖ := hc
        _ ≤ Ccomm * (((2 * n + 1 : ℕ) : ℝ) * (Cn * lapSum n S)) :=
            mul_le_mul_of_nonneg_left hsum_le hCcomm_nn
        _ ≤ Ccomm * ((2 * n + 1 : ℕ) : ℝ) * Cn * lapSum (n + 1) S := by
            have hmono := mul_le_mul_of_nonneg_left hlapSum_mono
              (by positivity : (0 : ℝ) ≤ Ccomm * ((2 * n + 1 : ℕ) : ℝ) * Cn)
            nlinarith [hmono, mul_nonneg (mul_nonneg hCcomm_nn
              (by positivity : (0 : ℝ) ≤ ((2 * n + 1 : ℕ) : ℝ))) hCn_nn]
    -- Hence `‖Δ_∇(∇^{2n} S)‖ ≤ P · lapSum (n + 1) S`.
    have hrawlap_grad_le :
        ‖rawTensorConnLapSmooth (I := I) g 0 (s + 2 * n) (iteratedCovGrad g 0 s (2 * n) S)‖ ≤
          P * lapSum (n + 1) S := by
      have hsplit := rawConnLap_iteratedCovGrad_eq_iteratedCovGrad_rawConnLap_add_comm
        (I := I) (M := M) g s (2 * n) S
      rw [hsplit]
      refine le_trans (norm_add_le _ _) ?_
      have := add_le_add hgrad_lap_le hcomm_le
      rw [hP_def]
      calc ‖iteratedCovGrad g 0 s (2 * n) (rawTensorConnLapSmooth (I := I) g 0 s S)‖ +
            ‖rawTensorConnLapSmooth (I := I) g 0 (s + 2 * n) (iteratedCovGrad g 0 s (2 * n) S) -
              iteratedCovGrad g 0 s (2 * n) (rawTensorConnLapSmooth (I := I) g 0 s S)‖
          ≤ Cn * lapSum (n + 1) S +
              Ccomm * ((2 * n + 1 : ℕ) : ℝ) * Cn * lapSum (n + 1) S := this
        _ = (Cn + Ccomm * ((2 * n + 1 : ℕ) : ℝ) * Cn) * lapSum (n + 1) S := by ring
    -- `‖∇^{2n} S‖ ≤ Cn · lapSum (n + 1) S` (from the IH and monotonicity of `lapSum`).
    have hgrad2n_le : ‖iteratedCovGrad g 0 s (2 * n) S‖ ≤ Cn * lapSum (n + 1) S :=
      le_trans (hgrad_le (2 * n) (le_refl _))
        (mul_le_mul_of_nonneg_left hlapSum_mono hCn_nn)
    -- Now case on `j ≤ 2 * (n + 1) = 2n + 2`.
    rcases Nat.lt_or_ge j (2 * n + 1) with hjlt | hjge
    · -- `j ≤ 2n`: the induction hypothesis at rank `s` suffices (with `lapSum n ≤ lapSum (n+1)`).
      have hjle : j ≤ 2 * n := Nat.lt_succ_iff.mp hjlt
      calc ‖iteratedCovGrad g 0 s j S‖
          ≤ Cn * lapSum n S := hgrad_le j hjle
        _ ≤ Cn * lapSum (n + 1) S := mul_le_mul_of_nonneg_left hlapSum_mono hCn_nn
        _ = Cn * ∑ i ∈ Finset.range (n + 1 + 1), ‖rawTensorConnLapIter (I := I) g 0 s i S‖ := by
            simp only [hlapSum_def]
        _ ≤ max Cn (max C2 C1) *
              ∑ i ∈ Finset.range (n + 1 + 1), ‖rawTensorConnLapIter (I := I) g 0 s i S‖ :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
    · -- `j ∈ {2n+1, 2n+2}`.
      have hjcase : j = 2 * n + 1 ∨ j = 2 * n + 2 := by omega
      rcases hjcase with hj1 | hj2
      · subst hj1
        -- `j = 2n + 1`: order-`1` covariant control on `∇^{2n} S`.
        -- `∇^{2n+1} S = covGrad (∇^{2n} S)`.
        have heq : iteratedCovGrad g 0 s (2 * n + 1) S =
            covGrad (I := I) (M := M) g 0 (s + 2 * n) (iteratedCovGrad g 0 s (2 * n) S) := rfl
        have hord1 := covGrad_norm_sq_le_rawConnLap_mul_self (I := I) (M := M) g (s + 2 * n)
          (iteratedCovGrad g 0 s (2 * n) S)
        -- `‖∇^{2n+1} S‖² ≤ ‖Δ_∇(∇^{2n}S)‖ · ‖∇^{2n}S‖ ≤ (P·L)·(Cn·L) = (P·Cn)·L²`.
        have hsq : ‖iteratedCovGrad g 0 s (2 * n + 1) S‖ ^ 2 ≤
            (P * Cn) * lapSum (n + 1) S ^ 2 := by
          rw [heq]
          refine le_trans hord1 ?_
          have h1 := hrawlap_grad_le
          have h2 := hgrad2n_le
          have hL := hlapSum_nn (n + 1)
          nlinarith [mul_nonneg (norm_nonneg
            (rawTensorConnLapSmooth (I := I) g 0 (s + 2 * n) (iteratedCovGrad g 0 s (2 * n) S)))
            (norm_nonneg (iteratedCovGrad g 0 s (2 * n) S)),
            mul_le_mul h1 h2 (norm_nonneg _) (mul_nonneg hP_nn hL),
            mul_nonneg hP_nn hL, mul_nonneg hCn_nn hL]
        -- Take square roots.
        have hle : ‖iteratedCovGrad g 0 s (2 * n + 1) S‖ ≤ C1 * lapSum (n + 1) S := by
          rw [hC1_def]
          have hfinal : ‖iteratedCovGrad g 0 s (2 * n + 1) S‖ ^ 2 ≤
              (Real.sqrt (P * Cn) * lapSum (n + 1) S) ^ 2 := by
            rw [mul_pow, Real.sq_sqrt (mul_nonneg hP_nn hCn_nn)]
            exact hsq
          exact le_of_sq_le_sq hfinal
            (mul_nonneg (Real.sqrt_nonneg _) (hlapSum_nn (n + 1)))
        calc ‖iteratedCovGrad g 0 s (2 * n + 1) S‖
            ≤ C1 * lapSum (n + 1) S := hle
          _ ≤ max Cn (max C2 C1) * lapSum (n + 1) S :=
              mul_le_mul_of_nonneg_right (le_trans (le_max_right _ _) (le_max_right _ _))
                (hlapSum_nn (n + 1))
          _ = max Cn (max C2 C1) *
                ∑ i ∈ Finset.range (n + 1 + 1), ‖rawTensorConnLapIter (I := I) g 0 s i S‖ := by
              simp only [hlapSum_def]
      · subst hj2
        -- `j = 2n + 2`: order-`2` Gårding on `∇^{2n} S`.
        -- `∇^{2n+2} S = covGrad (covGrad (∇^{2n} S))`.
        have heq : iteratedCovGrad g 0 s (2 * n + 2) S =
            covGrad (I := I) (M := M) g 0 (s + 2 * n + 1)
              (covGrad (I := I) (M := M) g 0 (s + 2 * n) (iteratedCovGrad g 0 s (2 * n) S)) :=
          iteratedCovGrad_add_two (I := I) (M := M) g s (2 * n) S
        have hord2 := hgard (iteratedCovGrad g 0 s (2 * n) S)
        -- `‖∇^{2n+2} S‖² ≤ Cg·(‖Δ_∇(∇^{2n}S)‖² + ‖∇^{2n}S‖²) ≤ Cg·(P²+Cn²)·L²`.
        have hsq : ‖iteratedCovGrad g 0 s (2 * n + 2) S‖ ^ 2 ≤
            (Cg * (P ^ 2 + Cn ^ 2)) * lapSum (n + 1) S ^ 2 := by
          rw [heq]
          refine le_trans hord2 ?_
          have h1 := hrawlap_grad_le
          have h2 := hgrad2n_le
          have hL := hlapSum_nn (n + 1)
          have hb1 : ‖rawTensorConnLapSmooth (I := I) g 0 (s + 2 * n)
              (iteratedCovGrad g 0 s (2 * n) S)‖ ^ 2 ≤ P ^ 2 * lapSum (n + 1) S ^ 2 := by
            have hnn := norm_nonneg (rawTensorConnLapSmooth (I := I) g 0 (s + 2 * n)
              (iteratedCovGrad g 0 s (2 * n) S))
            nlinarith [h1, mul_nonneg hP_nn hL]
          have hb2 : ‖iteratedCovGrad g 0 s (2 * n) S‖ ^ 2 ≤ Cn ^ 2 * lapSum (n + 1) S ^ 2 := by
            have hnn := norm_nonneg (iteratedCovGrad g 0 s (2 * n) S)
            nlinarith [h2, mul_nonneg hCn_nn hL]
          nlinarith [hb1, hb2, hCg_nn, mul_nonneg hCg_nn
            (add_nonneg (sq_nonneg P) (sq_nonneg Cn))]
        have hle : ‖iteratedCovGrad g 0 s (2 * n + 2) S‖ ≤ C2 * lapSum (n + 1) S := by
          rw [hC2_def]
          have hfinal : ‖iteratedCovGrad g 0 s (2 * n + 2) S‖ ^ 2 ≤
              (Real.sqrt (Cg * (P ^ 2 + Cn ^ 2)) * lapSum (n + 1) S) ^ 2 := by
            rw [mul_pow, Real.sq_sqrt
              (mul_nonneg hCg_nn (add_nonneg (sq_nonneg P) (sq_nonneg Cn)))]
            exact hsq
          exact le_of_sq_le_sq hfinal
            (mul_nonneg (Real.sqrt_nonneg _) (hlapSum_nn (n + 1)))
        calc ‖iteratedCovGrad g 0 s (2 * n + 2) S‖
            ≤ C2 * lapSum (n + 1) S := hle
          _ ≤ max Cn (max C2 C1) * lapSum (n + 1) S :=
              mul_le_mul_of_nonneg_right (le_trans (le_max_left _ _) (le_max_right _ _))
                (hlapSum_nn (n + 1))
          _ = max Cn (max C2 C1) *
                ∑ i ∈ Finset.range (n + 1 + 1), ‖rawTensorConnLapIter (I := I) g 0 s i S‖ := by
              simp only [hlapSum_def]

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
