import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.HeatOutputRealize
import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.SpectralWeylCounting
import DifferentialGeometry.Analysis.Spectral.Intrinsic.HeatSemigroup.SpectralSmoothing
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.GeneralOrderPouSpectralBound
import DifferentialGeometry.Analysis.Integration.L2.Hilbert.SimpLemmas
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.WeylEigenvalueCountingBound
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.DeTurckG0AnalyticInputs

/-!
# Smooth realization of the non-finite-support spectral heat output

For a closed (compact, boundaryless) smooth Riemannian manifold `(M, g)` the
analytic-semigroup heat operator `tensorHeatSemigroupHs ht` (file
`Analysis/Parabolic/TensorHeatEquation/SmoothingHs.lean`) maps an `Hᵃ` Sobolev
element `v` into `Hᵇ` for *every* exponent `b` — even `b > a` — gaining
arbitrarily many derivatives (parabolic smoothing). Its eigenbasis coordinate is
`exp(-λᵢ t) · v.coeff i`, which is **not** finitely supported (every coordinate is
scaled by a nonzero factor). The finite-support smooth representative
`heatOutputSmoothRepr` (file `HeatOutputRealize.lean`) therefore does not apply.

This file produces a genuine smooth (`SmoothCcTensor`) representative of the heat
output `tensorHeatSemigroupHs ht v` for *arbitrary* (non-finite-support) input `v`,
together with the intrinsic `H^{2k}` Sobolev bounds and `Hᵃ⁺¹`-Lipschitz control
needed by the DeTurck forward-existence synthesis (the `ChartJet2LipControl` arms).

## The smooth realization

The heat output `tensorHeatSemigroupHs ht v ∈ Hᵇ` for every `b`; its `L²` class is
the `L²`-level heat output `tensorHeatSemigroup t u₀` of `u₀ := tensorHsToL2 v`,
which lies in the spectral smooth subspace `⋂_σ Hˢ` (`heat_semigroup_into_all_tensorHs`).
The unconditional spectral smooth-representative gate
`spectralSmoothRealizesAsSmooth_of_eigenvalueTailSummable` — fed by the closed-manifold
Weyl counting bound `weyl_eigenvalue_counting_bound_of_closed` through
`eigenvalueTailSummable_of_countingBound` — then realizes that `L²` class as a genuine
`C^∞` section. (This transits the project's single Weyl node, exactly as the sibling
`(0,2)` gate `deTurckRealizeGate` does; no new `sorry`.)

## Main definitions

* `tensorHeatSemigroupHs_output_smoothRepr g r s ht v` — the genuine smooth,
  compactly-supported `(r, s)`-tensor representative of the positive-time heat output
  `tensorHeatSemigroupHs ht v`, for an arbitrary spectral Sobolev input `v`.

## Main results

* `tensorHeatSemigroupHs_output_smoothRepr_toL2` — its `L²` class is the `L²`-level
  heat output `tensorHeatSemigroup t (tensorHsToL2 v)`.
* `tensorHeatSemigroupHs_output_smoothRepr_coeff` — its eigenbasis `L²` coordinate is
  `exp(-λᵢ t) · v.coeff i`, i.e. the coordinate of `tensorHeatSemigroupHs ht v`.
* `tensorHeatSemigroupHs_output_smoothRepr_toHs_le` — the all-order intrinsic `H^{2k}`
  bound `‖(repr v).toHs (2k)‖ ≤ C(k, t) · ‖v‖_{Hᵃ}` (parabolic smoothing through the
  general-order Gårding spectral bound `pouSobolevToHsNorm_le_spectral`).
* `tensorHeatSemigroupHs_output_smoothRepr_toHs_sub_le` — the `Hᵃ`-Lipschitz form
  `‖(repr v − repr v').toHs (2k)‖ ≤ C(k, t) · ‖v − v'‖_{Hᵃ}`.
* `tensorHeatSemigroupHs_output_smoothRepr_fibreOpBound` — the `g`-fibre operator bound
  on the extracted symmetric form `ccTensorBilinSymm g (repr v)`, controlled by
  `C · ‖v‖_{Hᵃ}`, the `fibreSmall`-arm engine.

## Sign convention

Geometer convention `Δ_∇ = -∇*∇`, spectrum `⊆ (-∞, 0]`; the resolvent is `(1 - Δ_∇)⁻¹`.
The eigenvalues `λᵢ ≥ 0`, so `exp(-λᵢ t) ∈ (0, 1]` for `t ≥ 0`.
-/

noncomputable section

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace IntrinsicSpectral
namespace MetricRealization

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Sobolev.Tensor
open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral.SobolevScale
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless]
  [T2Space M] [SigmaCompactSpace M]

/-- **The unconditional spectral smooth-representative gate at rank `(r, s)`.**
Every `L²` tensor lying (via the chart-locality-free inclusion) in every `Hˢ` admits a
genuine `C^∞` (`SmoothCcTensor`) representative. The Weyl-type spectral input is supplied
from the closed-manifold polynomial eigenvalue-counting bound
`weyl_eigenvalue_counting_bound_of_closed` through `eigenvalueTailSummable_of_countingBound`.
(Transits the single Weyl node; the rank-`(0,2)` instance is `deTurckRealizeGate`.) -/
theorem spectralSmoothRealizesAsSmooth_of_closed
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    SpectralSmoothRealizesAsSmooth (I := I) (M := M) g r s :=
  spectralSmoothRealizesAsSmooth_of_eigenvalueTailSummable (I := I) (M := M) g r s
    (eigenvalueTailSummable_of_countingBound (I := I) (M := M) g r s
      (DifferentialGeometry.PDE.RicciFlow.weyl_eigenvalue_counting_bound_of_closed
        (I := I) (M := M) g r s))

/-- **The genuine smooth representative of the non-finite-support heat output.** For a
closed Riemannian manifold `(M, g)`, ranks `(r, s)`, an arbitrary spectral Sobolev input
`v : tensorHs g r s a`, and a positive time `t`, this is the genuine smooth,
compactly-supported `(r, s)`-tensor section representing the positive-time heat output
`tensorHeatSemigroupHs ht v`.

It is the unconditional spectral smooth representative of the `L²` class of the heat
output (the `L²`-level heat output `tensorHeatSemigroup t (tensorHsToL2 v)`), which lies
in every `Hˢ` by parabolic smoothing and is realized as a `C^∞` section by the
smooth-representative gate `spectralSmoothRealizesAsSmooth_of_closed`. -/
def tensorHeatSemigroupHs_output_smoothRepr
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    {t : ℝ} (ht : 0 < t) {a : ℝ} (ha : 0 ≤ a)
    (v : tensorHs (I := I) (M := M) g r s a) :
    SmoothCcTensor g r s :=
  (spectralSmoothRealizesAsSmooth_of_closed (I := I) (M := M) g r s
    (tensorHeatSemigroup (I := I) (M := M) g r s t
      (tensorHsToL2 (I := I) (M := M) (g := g) (r := r) (s := s)
        (tensorResolventL2_isCompactOperator (I := I) (M := M) g r s) ha v))
    (heat_semigroup_into_all_tensorHs (I := I) (M := M) g r s ht
      (tensorHsToL2 (I := I) (M := M) (g := g) (r := r) (s := s)
        (tensorResolventL2_isCompactOperator (I := I) (M := M) g r s) ha v))).choose

/-- **The smooth representative realizes the heat output (at the `L²` level).** The `L²`
class of `tensorHeatSemigroupHs_output_smoothRepr` is the `L²`-level heat output
`tensorHeatSemigroup t (tensorHsToL2 v)` of the input's `L²` class. -/
theorem tensorHeatSemigroupHs_output_smoothRepr_toL2
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    {t : ℝ} (ht : 0 < t) {a : ℝ} (ha : 0 ≤ a)
    (v : tensorHs (I := I) (M := M) g r s a) :
    (tensorHeatSemigroupHs_output_smoothRepr (I := I) (M := M) g r s ht ha v :
        TensorL2 r s g) =
      tensorHeatSemigroup (I := I) (M := M) g r s t
        (tensorHsToL2 (I := I) (M := M) (g := g) (r := r) (s := s)
          (tensorResolventL2_isCompactOperator (I := I) (M := M) g r s) ha v) :=
  (spectralSmoothRealizesAsSmooth_of_closed (I := I) (M := M) g r s
    (tensorHeatSemigroup (I := I) (M := M) g r s t
      (tensorHsToL2 (I := I) (M := M) (g := g) (r := r) (s := s)
        (tensorResolventL2_isCompactOperator (I := I) (M := M) g r s) ha v))
    (heat_semigroup_into_all_tensorHs (I := I) (M := M) g r s ht
      (tensorHsToL2 (I := I) (M := M) (g := g) (r := r) (s := s)
        (tensorResolventL2_isCompactOperator (I := I) (M := M) g r s) ha v))).choose_spec

/-- **Eigenbasis `L²` coordinate of the smooth representative.** The `i`-th eigenbasis
coordinate of the `L²` class of `tensorHeatSemigroupHs_output_smoothRepr` is
`exp(-λᵢ t) · v.coeff i`, i.e. exactly the coordinate of `tensorHeatSemigroupHs ht v`. -/
theorem tensorHeatSemigroupHs_output_smoothRepr_coeff
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    {t : ℝ} (ht : 0 < t) {a : ℝ} (ha : 0 ≤ a)
    (v : tensorHs (I := I) (M := M) g r s a)
    (i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g r s) :
    tensorL2Coeff (I := I) (M := M)
        (tensorResolventL2_isCompactOperator (I := I) (M := M) g r s)
        (tensorHeatSemigroupHs_output_smoothRepr (I := I) (M := M) g r s ht ha v :
          TensorL2 r s g) i =
      Real.exp (-(Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx.lambda
          (I := I) (M := M) i) * t) * v.coeff i := by
  rw [tensorHeatSemigroupHs_output_smoothRepr_toL2 (I := I) (M := M) g r s ht ha v]
  rw [tensorHeatSemigroup_intrinsic_tensorL2Coeff_ofCompact (I := I) (M := M) g r s ht.le]
  rw [tensorHsToL2_tensorL2Coeff]

/-- The order-`4k` spectral square-sum of the `L²`-coordinates of the smooth
representative coincides with the squared `H^{4k}` norm of the heat output
`tensorHeatSemigroupHs ht v` (whose `i`-th coordinate is the same
`exp(-λᵢ t) · v.coeff i`). -/
theorem tensorHeatSemigroupHs_output_smoothRepr_spectralSum_eq
    (g : SmoothRiemannianMetric I M)
    {t : ℝ} (ht : 0 < t) {a : ℝ} (ha : 0 ≤ a)
    (v : tensorHs (I := I) (M := M) g 0 2 a) (k : ℕ) :
    (∑' i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 2,
        tensorSobolevWeight (I := I) (M := M) i ((2 * (2 * k) : ℕ) : ℝ) *
          (tensorL2Coeff (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2)
            (SmoothCcTensor.toL2
              (tensorHeatSemigroupHs_output_smoothRepr (I := I) (M := M) g 0 2 ht ha v)) i) ^ 2) =
      ‖tensorHeatSemigroupHs (I := I) (M := M) (g := g) (r := 0) (s := 2) ht
          (a := a) (b := ((2 * (2 * k) : ℕ) : ℝ)) v‖ ^ 2 := by
  rw [tensorHs.norm_sq_eq_tsum (I := I) (M := M)
    (tensorHeatSemigroupHs (I := I) (M := M) (g := g) (r := 0) (s := 2) ht
      (a := a) (b := ((2 * (2 * k) : ℕ) : ℝ)) v)]
  refine tsum_congr (fun i => ?_)
  congr 1
  rw [show SmoothCcTensor.toL2
        (tensorHeatSemigroupHs_output_smoothRepr (I := I) (M := M) g 0 2 ht ha v) =
      ((tensorHeatSemigroupHs_output_smoothRepr (I := I) (M := M) g 0 2 ht ha v :
        TensorL2 0 2 g)) from rfl]
  rw [tensorHeatSemigroupHs_output_smoothRepr_coeff (I := I) (M := M) g 0 2 ht ha v i]
  rw [tensorHeatSemigroupHs_coeff]

set_option maxHeartbeats 3200000 in
/-- **All-order intrinsic `H^{2k}` bound of the smooth representative.** For every order
`k`, the intrinsic `H^{2k}` Sobolev norm of the smooth heat-output representative is
controlled by `C(k, t) · ‖v‖_{Hᵃ}`. The constant is the general-order Gårding spectral
constant `pouSobolevToHsNorm_le_spectral` times the analytic-semigroup operator norm
`‖tensorHeatSemigroupHs ht‖_{Hᵃ → H^{4k}}` (finite, all-order parabolic smoothing). -/
theorem tensorHeatSemigroupHs_output_smoothRepr_toHs_le
    (g : SmoothRiemannianMetric I M)
    {t : ℝ} (ht : 0 < t) {a : ℝ} (ha : 0 ≤ a) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ v : tensorHs (I := I) (M := M) g 0 2 a,
        ‖SmoothCcTensor.toHs (g := g) (r := 0) (s := 2) (2 * k)
            (tensorHeatSemigroupHs_output_smoothRepr (I := I) (M := M) g 0 2 ht ha v)‖ ≤
          C * ‖v‖ := by
  obtain ⟨Cspec, hCspec_nn, hCspec⟩ :=
    pouSobolevToHsNorm_le_spectral (I := I) (M := M) g k
  refine ⟨Cspec *
      ‖tensorHeatSemigroupHs (I := I) (M := M) (g := g) (r := 0) (s := 2) ht
        (a := a) (b := ((2 * (2 * k) : ℕ) : ℝ))‖, ?_, fun v => ?_⟩
  · exact mul_nonneg hCspec_nn
      (norm_nonneg (tensorHeatSemigroupHs (I := I) (M := M) (g := g) (r := 0) (s := 2) ht
        (a := a) (b := ((2 * (2 * k) : ℕ) : ℝ))))
  · set T : SmoothCcTensor g 0 2 :=
      tensorHeatSemigroupHs_output_smoothRepr (I := I) (M := M) g 0 2 ht ha v with hT_def
    have hspec := hCspec T
    rw [tensorHeatSemigroupHs_output_smoothRepr_spectralSum_eq
      (I := I) (M := M) g ht ha v k] at hspec
    rw [Real.sqrt_sq (norm_nonneg _)] at hspec
    refine hspec.trans ?_
    have hop : ‖tensorHeatSemigroupHs (I := I) (M := M) (g := g) (r := 0) (s := 2) ht
          (a := a) (b := ((2 * (2 * k) : ℕ) : ℝ)) v‖ ≤
        ‖tensorHeatSemigroupHs (I := I) (M := M) (g := g) (r := 0) (s := 2) ht
          (a := a) (b := ((2 * (2 * k) : ℕ) : ℝ))‖ * ‖v‖ :=
      ContinuousLinearMap.le_opNorm _ v
    calc Cspec *
          ‖tensorHeatSemigroupHs (I := I) (M := M) (g := g) (r := 0) (s := 2) ht
            (a := a) (b := ((2 * (2 * k) : ℕ) : ℝ)) v‖
        ≤ Cspec * (‖tensorHeatSemigroupHs (I := I) (M := M) (g := g) (r := 0) (s := 2) ht
            (a := a) (b := ((2 * (2 * k) : ℕ) : ℝ))‖ * ‖v‖) :=
          mul_le_mul_of_nonneg_left hop hCspec_nn
      _ = Cspec *
            ‖tensorHeatSemigroupHs (I := I) (M := M) (g := g) (r := 0) (s := 2) ht
              (a := a) (b := ((2 * (2 * k) : ℕ) : ℝ))‖ * ‖v‖ := by ring

/-- The `i`-th eigenbasis `L²` coordinate of the *difference* of two smooth heat-output
representatives is `exp(-λᵢ t) · (v − v').coeff i` (the heat output is `L²`-linear). -/
theorem tensorHeatSemigroupHs_output_smoothRepr_sub_coeff
    (g : SmoothRiemannianMetric I M)
    {t : ℝ} (ht : 0 < t) {a : ℝ} (ha : 0 ≤ a)
    (v v' : tensorHs (I := I) (M := M) g 0 2 a)
    (i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 2) :
    tensorL2Coeff (I := I) (M := M)
        (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2)
        (SmoothCcTensor.toL2
          (tensorHeatSemigroupHs_output_smoothRepr (I := I) (M := M) g 0 2 ht ha v -
            tensorHeatSemigroupHs_output_smoothRepr (I := I) (M := M) g 0 2 ht ha v')) i =
      Real.exp (-(Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx.lambda
          (I := I) (M := M) i) * t) * (v - v').coeff i := by
  have hcoeff_split :
      tensorL2Coeff (I := I) (M := M)
          (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2)
          (SmoothCcTensor.toL2
            (tensorHeatSemigroupHs_output_smoothRepr (I := I) (M := M) g 0 2 ht ha v -
              tensorHeatSemigroupHs_output_smoothRepr (I := I) (M := M) g 0 2 ht ha v')) i =
        tensorL2Coeff (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2)
            (SmoothCcTensor.toL2
              (tensorHeatSemigroupHs_output_smoothRepr (I := I) (M := M) g 0 2 ht ha v)) i -
          tensorL2Coeff (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2)
            (SmoothCcTensor.toL2
              (tensorHeatSemigroupHs_output_smoothRepr (I := I) (M := M) g 0 2 ht ha v')) i := by
    rw [Integral.L2.SmoothCcTensor.toL2_sub]
    unfold tensorL2Coeff
    rw [map_sub]; rfl
  rw [hcoeff_split]
  have hv :
      tensorL2Coeff (I := I) (M := M)
          (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2)
          (SmoothCcTensor.toL2
            (tensorHeatSemigroupHs_output_smoothRepr (I := I) (M := M) g 0 2 ht ha v)) i =
        Real.exp (-(Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx.lambda
            (I := I) (M := M) i) * t) * v.coeff i :=
    tensorHeatSemigroupHs_output_smoothRepr_coeff (I := I) (M := M) g 0 2 ht ha v i
  have hv' :
      tensorL2Coeff (I := I) (M := M)
          (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2)
          (SmoothCcTensor.toL2
            (tensorHeatSemigroupHs_output_smoothRepr (I := I) (M := M) g 0 2 ht ha v')) i =
        Real.exp (-(Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx.lambda
            (I := I) (M := M) i) * t) * v'.coeff i :=
    tensorHeatSemigroupHs_output_smoothRepr_coeff (I := I) (M := M) g 0 2 ht ha v' i
  rw [hv, hv']
  have hsub : (v - v').coeff i = v.coeff i - v'.coeff i := by
    rw [sub_eq_add_neg]
    simp only [tensorHs.add_coeff, tensorHs.neg_coeff]
    rw [← sub_eq_add_neg]
  rw [hsub, mul_sub]

/-- The order-`4k` spectral square-sum of the `L²`-coordinates of the *difference* of two
smooth heat-output representatives equals the squared `H^{4k}` norm of
`tensorHeatSemigroupHs ht (v − v')`. -/
theorem tensorHeatSemigroupHs_output_smoothRepr_sub_spectralSum_eq
    (g : SmoothRiemannianMetric I M)
    {t : ℝ} (ht : 0 < t) {a : ℝ} (ha : 0 ≤ a)
    (v v' : tensorHs (I := I) (M := M) g 0 2 a) (k : ℕ) :
    (∑' i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 2,
        tensorSobolevWeight (I := I) (M := M) i ((2 * (2 * k) : ℕ) : ℝ) *
          (tensorL2Coeff (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2)
            (SmoothCcTensor.toL2
              (tensorHeatSemigroupHs_output_smoothRepr (I := I) (M := M) g 0 2 ht ha v -
                tensorHeatSemigroupHs_output_smoothRepr (I := I) (M := M) g 0 2 ht ha v')) i) ^ 2) =
      ‖tensorHeatSemigroupHs (I := I) (M := M) (g := g) (r := 0) (s := 2) ht
          (a := a) (b := ((2 * (2 * k) : ℕ) : ℝ)) (v - v')‖ ^ 2 := by
  rw [tensorHs.norm_sq_eq_tsum (I := I) (M := M)
    (tensorHeatSemigroupHs (I := I) (M := M) (g := g) (r := 0) (s := 2) ht
      (a := a) (b := ((2 * (2 * k) : ℕ) : ℝ)) (v - v'))]
  refine tsum_congr (fun i => ?_)
  congr 1
  rw [tensorHeatSemigroupHs_output_smoothRepr_sub_coeff (I := I) (M := M) g ht ha v v' i]
  rw [tensorHeatSemigroupHs_coeff]

set_option maxHeartbeats 3200000 in
/-- **All-order `Hᵃ`-Lipschitz `H^{2k}` bound of the smooth representative.** For every
order `k`, the intrinsic `H^{2k}` Sobolev norm of the difference of two smooth heat-output
representatives is controlled by `C(k, t) · ‖v − v'‖_{Hᵃ}`. Same constant as
`…_toHs_le` (the realization's `L²`-class is `Hᵃ`-linear, so the difference is the heat
output of the difference). -/
theorem tensorHeatSemigroupHs_output_smoothRepr_toHs_sub_le
    (g : SmoothRiemannianMetric I M)
    {t : ℝ} (ht : 0 < t) {a : ℝ} (ha : 0 ≤ a) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ v v' : tensorHs (I := I) (M := M) g 0 2 a,
        ‖SmoothCcTensor.toHs (g := g) (r := 0) (s := 2) (2 * k)
            (tensorHeatSemigroupHs_output_smoothRepr (I := I) (M := M) g 0 2 ht ha v -
              tensorHeatSemigroupHs_output_smoothRepr (I := I) (M := M) g 0 2 ht ha v')‖ ≤
          C * ‖v - v'‖ := by
  obtain ⟨Cspec, hCspec_nn, hCspec⟩ :=
    pouSobolevToHsNorm_le_spectral (I := I) (M := M) g k
  refine ⟨Cspec *
      ‖tensorHeatSemigroupHs (I := I) (M := M) (g := g) (r := 0) (s := 2) ht
        (a := a) (b := ((2 * (2 * k) : ℕ) : ℝ))‖, ?_, fun v v' => ?_⟩
  · exact mul_nonneg hCspec_nn
      (norm_nonneg (tensorHeatSemigroupHs (I := I) (M := M) (g := g) (r := 0) (s := 2) ht
        (a := a) (b := ((2 * (2 * k) : ℕ) : ℝ))))
  · have hspec := hCspec
      (tensorHeatSemigroupHs_output_smoothRepr (I := I) (M := M) g 0 2 ht ha v -
        tensorHeatSemigroupHs_output_smoothRepr (I := I) (M := M) g 0 2 ht ha v')
    rw [tensorHeatSemigroupHs_output_smoothRepr_sub_spectralSum_eq
      (I := I) (M := M) g ht ha v v' k] at hspec
    rw [Real.sqrt_sq (norm_nonneg _)] at hspec
    refine hspec.trans ?_
    have hop : ‖tensorHeatSemigroupHs (I := I) (M := M) (g := g) (r := 0) (s := 2) ht
          (a := a) (b := ((2 * (2 * k) : ℕ) : ℝ)) (v - v')‖ ≤
        ‖tensorHeatSemigroupHs (I := I) (M := M) (g := g) (r := 0) (s := 2) ht
          (a := a) (b := ((2 * (2 * k) : ℕ) : ℝ))‖ * ‖v - v'‖ :=
      ContinuousLinearMap.le_opNorm _ (v - v')
    calc Cspec *
          ‖tensorHeatSemigroupHs (I := I) (M := M) (g := g) (r := 0) (s := 2) ht
            (a := a) (b := ((2 * (2 * k) : ℕ) : ℝ)) (v - v')‖
        ≤ Cspec * (‖tensorHeatSemigroupHs (I := I) (M := M) (g := g) (r := 0) (s := 2) ht
            (a := a) (b := ((2 * (2 * k) : ℕ) : ℝ))‖ * ‖v - v'‖) :=
          mul_le_mul_of_nonneg_left hop hCspec_nn
      _ = Cspec *
            ‖tensorHeatSemigroupHs (I := I) (M := M) (g := g) (r := 0) (s := 2) ht
              (a := a) (b := ((2 * (2 * k) : ℕ) : ℝ))‖ * ‖v - v'‖ := by ring

set_option maxHeartbeats 3200000 in
/-- **The `g`-fibre operator bound on the extracted symmetric form (the `fibreSmall`-arm
engine).** There is a fixed constant `Cfib ≥ 0` such that, for every input `v`, the
symmetric bilinear extraction `ccTensorBilinSymm g (repr v)` of the smooth heat-output
representative is `g`-fibre controlled by `Cfib · ‖v‖_{Hᵃ}`. This composes the supercritical
`C⁰`-Sobolev fibre embedding `gFibreOpBound_ccTensorBilinSymm_le_tensorHsNorm`
(`gFibreOpBound (ccTensorBilinSymm T) (C · ‖T.toHs (2k)‖)`) with the all-order `H^{2k}`
bound `…_toHs_le` (`‖(repr v).toHs (2k)‖ ≤ C' · ‖v‖`). Choosing `‖v‖` small (via a ball
radius) makes the constant `< 1`, so `g + ccTensorBilinSymm g (repr v)` is a genuine smooth
metric — exactly the `ChartJet2LipControl.fibreSmall` input. -/
theorem tensorHeatSemigroupHs_output_smoothRepr_fibreOpBound
    (g : SmoothRiemannianMetric I M)
    {t : ℝ} (ht : 0 < t) {a : ℝ} (ha : 0 ≤ a) :
    ∃ Cfib : ℝ, 0 ≤ Cfib ∧
      ∀ v : tensorHs (I := I) (M := M) g 0 2 a,
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (tensorHeatSemigroupHs_output_smoothRepr (I := I) (M := M) g 0 2 ht ha v))
          (Cfib * ‖v‖) := by
  classical
  set k₀ : ℕ := (Module.finrank ℝ E + 4) / 2 + 1 with hk₀_def
  have hk₀_super : 2 * k₀ > Module.finrank ℝ E + 4 := by rw [hk₀_def]; omega
  obtain ⟨Cemb, hCemb_nn, hCemb⟩ :=
    DifferentialGeometry.PDE.RicciFlow.gFibreOpBound_ccTensorBilinSymm_le_tensorHsNorm
      (I := I) (M := M) g
  obtain ⟨Cbd, hCbd_nn, hCbd⟩ :=
    tensorHeatSemigroupHs_output_smoothRepr_toHs_le (I := I) (M := M) g ht ha k₀
  refine ⟨Cemb * Cbd, mul_nonneg hCemb_nn hCbd_nn, fun v => ?_⟩
  set T : SmoothCcTensor g 0 2 :=
    tensorHeatSemigroupHs_output_smoothRepr (I := I) (M := M) g 0 2 ht ha v with hT_def
  intro x p q
  have hbase := hCemb k₀ hk₀_super T x p q
  have hnorm_le :
      Cemb * ‖SmoothCcTensor.toHs (g := g) (r := 0) (s := 2) (2 * k₀) T‖ ≤
        Cemb * Cbd * ‖v‖ := by
    have h := hCbd v
    calc Cemb * ‖SmoothCcTensor.toHs (g := g) (r := 0) (s := 2) (2 * k₀) T‖
        ≤ Cemb * (Cbd * ‖v‖) := mul_le_mul_of_nonneg_left h hCemb_nn
      _ = Cemb * Cbd * ‖v‖ := by ring
  have hsqp : 0 ≤ Real.sqrt (g.inner x p p) := Real.sqrt_nonneg _
  have hsqq : 0 ≤ Real.sqrt (g.inner x q q) := Real.sqrt_nonneg _
  refine hbase.trans ?_
  refine mul_le_mul_of_nonneg_right ?_ hsqq
  refine mul_le_mul_of_nonneg_right hnorm_le hsqp

end MetricRealization
end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end
