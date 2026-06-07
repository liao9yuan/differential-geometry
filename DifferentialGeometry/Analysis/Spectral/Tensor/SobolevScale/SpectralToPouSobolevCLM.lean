import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.GeneralOrderPouSpectralBound
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Inclusion
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.Regularity.EigenvectorTensorHsToWtwokTwo
import DifferentialGeometry.Analysis.Sobolev.Embedding.RawConnLapToHsOrderDropping
import Mathlib.Analysis.Normed.Operator.Extend

/-!
# The spectral-`Hˢ`-to-chart-Sobolev transfer as a bounded linear map

For a closed Riemannian manifold `(M, g₀)` and an order `k : ℕ`, the section-level
norm bound `pouSobolevToHsNorm_le_spectral` controls the intrinsic order-`2k`
partition-of-unity Hilbert–Schmidt chart-Sobolev norm `‖T.toHs (2k)‖` of a smooth
compactly-supported `(0, 2)`-tensor `T` by the spectral order-`4k` Sobolev norm of
`T`'s `L²` class.  That bound is a `‖·‖`-domination on smooth representatives; this
file upgrades it to a genuine **bounded linear map**

  `spectralToPouSobolevCLM g₀ k :
      tensorHs g₀ 0 2 ((2 * (2 * k) : ℕ) : ℝ) →L[ℝ] TensorPouSobolevHilbert g₀ 0 2 (2 * k)`

from the spectral `H^{4k}` Sobolev space (the eigenbasis-coordinate Hilbert space
`tensorHs`) to the chart-POU `H^{2k}` Sobolev Hilbert space.

The bounded-linear upgrade is what makes the transfer usable in *higher-order*
regularity: composing a `ContDiffOn`/`ContMDiff` Banach-valued path with a nonlinear
`‖·‖`-Lipschitz domination loses derivatives, whereas composing with a continuous
**linear** map preserves every order (`ContDiffOn.continuousLinearMap_comp`).

## Construction

`spectralToPouSobolevCLM` is the dense extension (`LinearMap.extendOfNorm`,
`Analysis/Normed/Operator/Extend.lean`) of two linear maps off the smooth sections:

* `spectralCoeffLinearMap g₀ k : SmoothCcTensor g₀ 0 2 →ₗ[ℝ] tensorHs g₀ 0 2 (4k)`
  sends a smooth section `T` to the spectral `H^{4k}` element whose eigenbasis
  coordinates are the `L²` coordinates `tensorL2Coeff (T.toL2)` of `T` (well-defined
  by `smoothCcTensor_tensorL2Coeff_weighted_summable`, linear by the linearity of
  `tensorL2Coeff` and `SmoothCcTensor.toL2`).  Its range is **dense** because every
  finitely-supported `H^{4k}` element is the spectral image of its finite-support
  smooth representative `tensorHsSmoothRepr`, and the finitely-supported elements are
  dense (`tensorHs_dense_finiteSupport`).
* `toHsLinearMap g₀ k : SmoothCcTensor g₀ 0 2 →ₗ[ℝ] TensorPouSobolevHilbert g₀ 0 2 (2k)`
  sends `T` to its chart-Sobolev class `T.toHs (2k)` (linear by `SmoothCcTensor.toHs_add`
  and the completion-coercion `smul` law).

The norm comparison `‖toHsLinearMap T‖ ≤ C · ‖spectralCoeffLinearMap T‖` is exactly
`pouSobolevToHsNorm_le_spectral` together with the spectral Parseval identity
`tensorHs.norm_sq_eq_tsum` identifying `‖spectralCoeffLinearMap T‖²` with the weighted
spectral square-sum on the right-hand side of the bound (weight `4k`).

## Order bookkeeping

The spectral source exponent is `N = 2 · (2k) = 4k`, matching the `H^{4k}` regularity
that the order-`2k` chart-Sobolev norm aggregates (see the bound's docstring): no order
shift is silently introduced.  The constant `C` depends on `k` (it is the bound's
order-`k` constant), so it is fixed once `k` is.

## The identification (realization-compatibility)

`spectralToPouSobolevCLM_apply_spectralCoeff` records the defining identity on the
dense range: for every smooth `T`,

  `spectralToPouSobolevCLM g₀ k (spectralCoeffLinearMap g₀ k T) = T.toHs (2k)`.

Because `spectralCoeffLinearMap T` is the `H^{4k}` element with coordinates
`tensorL2Coeff (T.toL2)`, this reads — via `spectralToPouSobolevCLM_apply_of_coeff` —
as: whenever a spectral element `w` has `w.coeff i = tensorL2Coeff (T.toL2) i` for all
`i` (the `hcanon` coordinate tie of the Duhamel-trajectory time-regularity consumer),
`spectralToPouSobolevCLM g₀ k w = T.toHs (2k)`.  This holds for **every** smooth `T`
(not merely finitely-supported ones), since `spectralCoeffLinearMap` is defined on all
of `SmoothCcTensor` and the dense-range extension equation `extendOfNorm_eq` applies at
each `T` directly.

`spectralToPouSobolevCLM_ne_zero` records that the map is not the zero map (the
identification pins it to a nonzero value on a smooth section with nonzero chart-Sobolev
norm).

It carries no chart-locality predicate.  It rests transitively, through
`pouSobolevToHsNorm_le_spectral`, on that bound's posited curvature inputs (which are
`sorry`); consumers therefore transitively depend on `sorryAx`.
-/

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral
namespace SobolevScale

open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Sobolev.Tensor
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

/-- The completion-coercion `smul` law for the chart-Sobolev embedding
`SmoothCcTensor.toHs`: `(c • T).toHs k = c • T.toHs k`.  Both sides are the completion
coercion of the `SmoothCcTensorHs`-wrapper scalar multiplication
(`UniformSpace.Completion.coe_smul`), mirroring the additive law
`SmoothCcTensor.toHs_add`. -/
theorem smoothCcTensor_toHs_smul
    {g : SmoothRiemannianMetric I M} {r s : ℕ} (k : ℕ) (c : ℝ)
    (T : SmoothCcTensor g r s) :
    IntrinsicSobolev.SmoothCcTensor.toHs (g := g) (r := r) (s := s) k (c • T)
      = c • IntrinsicSobolev.SmoothCcTensor.toHs (g := g) (r := r) (s := s) k T := by
  unfold IntrinsicSobolev.SmoothCcTensor.toHs
  rw [show (⟨c • T⟩ : SmoothCcTensorHs g r s k)
        = c • (⟨T⟩ : SmoothCcTensorHs g r s k) from rfl]
  rw [← UniformSpace.Completion.coe_smul]

section Construction

variable (g₀ : SmoothRiemannianMetric I M) (k : ℕ)

/-- The spectral `H^{4k}` element attached to a smooth compactly-supported
`(0, 2)`-tensor `T`: the eigenbasis-coordinate family of `T`'s `L²` class
(`tensorL2Coeff (T.toL2)`), which is weighted-summable at the order-`4k` exponent
because `T` is smooth (`smoothCcTensor_tensorL2Coeff_weighted_summable`). -/
def spectralCoeffElement (T : SmoothCcTensor g₀ 0 2) :
    tensorHs (I := I) (M := M) g₀ 0 2 ((2 * (2 * k) : ℕ) : ℝ) where
  coeff i :=
    tensorL2Coeff (I := I) (M := M)
      (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
      (SmoothCcTensor.toL2 T) i
  weighted_summable :=
    smoothCcTensor_tensorL2Coeff_weighted_summable (I := I) (M := M) g₀
      ((2 * (2 * k) : ℕ) : ℝ) T
      (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)

@[simp] theorem spectralCoeffElement_coeff (T : SmoothCcTensor g₀ 0 2)
    (i : TensorEigenIdx (I := I) (M := M) g₀ 0 2) :
    (spectralCoeffElement (I := I) (M := M) g₀ k T).coeff i =
      tensorL2Coeff (I := I) (M := M)
        (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
        (SmoothCcTensor.toL2 T) i := rfl

/-- The spectral-coordinate realization as a linear map
`SmoothCcTensor g₀ 0 2 →ₗ[ℝ] tensorHs g₀ 0 2 (4k)`.  Linearity is the linearity of
`tensorL2Coeff` (in its `L²` argument) composed with the continuous linear embedding
`SmoothCcTensor.toL2`. -/
def spectralCoeffLinearMap :
    SmoothCcTensor g₀ 0 2 →ₗ[ℝ] tensorHs (I := I) (M := M) g₀ 0 2 ((2 * (2 * k) : ℕ) : ℝ) where
  toFun := spectralCoeffElement (I := I) (M := M) g₀ k
  map_add' S T := by
    refine tensorHs.ext ?_
    funext i
    simp only [tensorHs.add_coeff, spectralCoeffElement_coeff]
    rw [map_add, tensorL2Coeff_add]
  map_smul' c T := by
    refine tensorHs.ext ?_
    funext i
    simp only [tensorHs.smul_coeff, spectralCoeffElement_coeff, RingHom.id_apply]
    rw [map_smul, tensorL2Coeff_smul]

@[simp] theorem spectralCoeffLinearMap_apply (T : SmoothCcTensor g₀ 0 2) :
    spectralCoeffLinearMap (I := I) (M := M) g₀ k T =
      spectralCoeffElement (I := I) (M := M) g₀ k T := rfl

/-- The chart-Sobolev realization as a linear map
`SmoothCcTensor g₀ 0 2 →ₗ[ℝ] TensorPouSobolevHilbert g₀ 0 2 (2k)`, sending `T` to its
order-`2k` chart-Sobolev class `T.toHs (2k)`.  Linearity is `SmoothCcTensor.toHs_add`
and `smoothCcTensor_toHs_smul`. -/
def toHsLinearMap :
    SmoothCcTensor g₀ 0 2 →ₗ[ℝ]
      TensorPouSobolevHilbert (I := I) (M := M) g₀ 0 2 (2 * k) where
  toFun T := IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (2 * k) T
  map_add' S T :=
    DifferentialGeometry.PDE.RicciFlow.SmoothCcTensor.toHs_add (I := I) (M := M) (2 * k) S T
  map_smul' c T := smoothCcTensor_toHs_smul (I := I) (M := M) (2 * k) c T

@[simp] theorem toHsLinearMap_apply (T : SmoothCcTensor g₀ 0 2) :
    toHsLinearMap (I := I) (M := M) g₀ k T =
      IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (2 * k) T := rfl

/-- The `H^{4k}` norm of `spectralCoeffElement T` is the square root of the weighted
spectral square-sum appearing on the right-hand side of `pouSobolevToHsNorm_le_spectral`
(weight `4k`). -/
theorem norm_spectralCoeffElement_eq (T : SmoothCcTensor g₀ 0 2) :
    ‖spectralCoeffElement (I := I) (M := M) g₀ k T‖ =
      Real.sqrt (∑' i : TensorEigenIdx (I := I) (M := M) g₀ 0 2,
        tensorSobolevWeight (I := I) (M := M) i ((2 * (2 * k) : ℕ) : ℝ) *
          (tensorL2Coeff (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
            (SmoothCcTensor.toL2 T) i) ^ 2) := by
  rw [tensorHs.norm_eq_sqrt_tsum (I := I) (M := M)
    (spectralCoeffElement (I := I) (M := M) g₀ k T)]
  refine congrArg Real.sqrt (tsum_congr (fun i => ?_))
  rw [spectralCoeffElement_coeff]

/-- The range of `spectralCoeffLinearMap` is dense: every finitely-supported `H^{4k}`
element `v` is the spectral image of its finite-support smooth representative
`tensorHsSmoothRepr v`, and the finitely-supported elements are dense
(`tensorHs_dense_finiteSupport`). -/
theorem denseRange_spectralCoeffLinearMap :
    DenseRange (spectralCoeffLinearMap (I := I) (M := M) g₀ k) := by
  classical
  have hsub : {v : tensorHs (I := I) (M := M) g₀ 0 2 ((2 * (2 * k) : ℕ) : ℝ) |
        (Function.support v.coeff).Finite} ⊆
      Set.range (spectralCoeffLinearMap (I := I) (M := M) g₀ k) := by
    intro v hv
    refine ⟨tensorHsSmoothRepr (I := I) (M := M) v hv, ?_⟩
    refine tensorHs.ext ?_
    funext i
    rw [spectralCoeffLinearMap_apply, spectralCoeffElement_coeff]
    have hN : (0 : ℝ) ≤ ((2 * (2 * k) : ℕ) : ℝ) := by positivity
    rw [show SmoothCcTensor.toL2 (tensorHsSmoothRepr (I := I) (M := M) v hv) =
          ((tensorHsSmoothRepr (I := I) (M := M) v hv : TensorL2 0 2 g₀)) from
        SmoothCcTensor.toL2_apply _]
    rw [tensorHsSmoothRepr_toL2 (I := I) (M := M) hN v hv]
    rw [tensorHsToL2_tensorL2Coeff]
  exact (tensorHs_dense_finiteSupport (I := I) (M := M)).mono hsub

end Construction

section CLM

variable (g₀ : SmoothRiemannianMetric I M) (k : ℕ)

/-- **The spectral-`Hˢ`-to-chart-Sobolev transfer continuous linear map.**

For a closed Riemannian manifold `(M, g₀)` and order `k`, the bounded linear map
from the spectral order-`4k` Sobolev space `tensorHs g₀ 0 2 (4k)` (the
eigenbasis-coordinate Hilbert space) to the chart-POU order-`2k` Sobolev Hilbert space
`TensorPouSobolevHilbert g₀ 0 2 (2k)`, obtained as the dense extension
(`LinearMap.extendOfNorm`) of the smooth-section realization `T ↦ T.toHs (2k)` along the
dense spectral-coordinate map `T ↦ spectralCoeffElement T`.

Its continuity is exactly the section-level norm bound
`pouSobolevToHsNorm_le_spectral`; its defining identity on the dense range (the
realization-compatibility) is `spectralToPouSobolevCLM_apply_spectralCoeff`.

The spectral source exponent is `4k = 2 · (2k)`, matching the `H^{4k}` regularity of
the order-`2k` chart-Sobolev norm.  No chart-locality predicate. -/
def spectralToPouSobolevCLM :
    tensorHs (I := I) (M := M) g₀ 0 2 ((2 * (2 * k) : ℕ) : ℝ) →L[ℝ]
      TensorPouSobolevHilbert (I := I) (M := M) g₀ 0 2 (2 * k) :=
  LinearMap.extendOfNorm
    (toHsLinearMap (I := I) (M := M) g₀ k)
    (spectralCoeffLinearMap (I := I) (M := M) g₀ k)

/-- The transfer CLM dominates the smooth-section realization by the spectral norm:
the very bound `pouSobolevToHsNorm_le_spectral`, repackaged as the
`‖toHsLinearMap T‖ ≤ C · ‖spectralCoeffLinearMap T‖` comparison feeding the dense
extension.  Returns the order-`k` constant `C ≥ 0`. -/
theorem exists_toHsLinearMap_le_spectralCoeff :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : SmoothCcTensor g₀ 0 2,
      ‖toHsLinearMap (I := I) (M := M) g₀ k T‖ ≤
        C * ‖spectralCoeffLinearMap (I := I) (M := M) g₀ k T‖ := by
  obtain ⟨C, hC_nn, hC⟩ := pouSobolevToHsNorm_le_spectral (I := I) (M := M) g₀ k
  refine ⟨C, hC_nn, fun T => ?_⟩
  rw [toHsLinearMap_apply, spectralCoeffLinearMap_apply,
    norm_spectralCoeffElement_eq]
  exact hC T

/-- **The defining identity of the transfer CLM on the dense range
(realization-compatibility).** For every smooth `T`, the transfer CLM sends the spectral
element of `T` (the `H^{4k}` element with coordinates `tensorL2Coeff (T.toL2)`) to the
chart-Sobolev class `T.toHs (2k)`. -/
@[simp] theorem spectralToPouSobolevCLM_apply_spectralCoeff (T : SmoothCcTensor g₀ 0 2) :
    spectralToPouSobolevCLM (I := I) (M := M) g₀ k
        (spectralCoeffLinearMap (I := I) (M := M) g₀ k T) =
      IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (2 * k) T := by
  obtain ⟨C, _hC_nn, hC⟩ := exists_toHsLinearMap_le_spectralCoeff (I := I) (M := M) g₀ k
  rw [spectralToPouSobolevCLM,
    LinearMap.extendOfNorm_eq (denseRange_spectralCoeffLinearMap (I := I) (M := M) g₀ k)
      ⟨C, hC⟩ T]
  rw [toHsLinearMap_apply]

/-- **The realization-compatibility in coordinate-tie form (the `hcanon` shape).**
Whenever a spectral `H^{4k}` element `w` has eigenbasis coordinates equal to the `L²`
coordinates of a smooth section `T` (`w.coeff i = tensorL2Coeff (T.toL2) i` for all `i`),
the transfer CLM sends `w` to `T.toHs (2k)`.  This is exactly the tie the Duhamel
trajectory time-regularity consumer (`hcanon`) carries, for every smooth `T`. -/
theorem spectralToPouSobolevCLM_apply_of_coeff (T : SmoothCcTensor g₀ 0 2)
    (w : tensorHs (I := I) (M := M) g₀ 0 2 ((2 * (2 * k) : ℕ) : ℝ))
    (hw : ∀ i : TensorEigenIdx (I := I) (M := M) g₀ 0 2,
      w.coeff i = tensorL2Coeff (I := I) (M := M)
        (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
        (SmoothCcTensor.toL2 T) i) :
    spectralToPouSobolevCLM (I := I) (M := M) g₀ k w =
      IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (2 * k) T := by
  have hwe : w = spectralCoeffLinearMap (I := I) (M := M) g₀ k T := by
    refine tensorHs.ext ?_
    funext i
    rw [spectralCoeffLinearMap_apply, spectralCoeffElement_coeff]
    exact hw i
  rw [hwe]
  exact spectralToPouSobolevCLM_apply_spectralCoeff (I := I) (M := M) g₀ k T

/-- The operator norm of the transfer CLM is bounded by the order-`k` spectral constant
`C` of `pouSobolevToHsNorm_le_spectral`. -/
theorem spectralToPouSobolevCLM_opNorm_le :
    ∃ C : ℝ, 0 ≤ C ∧ ‖spectralToPouSobolevCLM (I := I) (M := M) g₀ k‖ ≤ C := by
  obtain ⟨C, hC_nn, hC⟩ := exists_toHsLinearMap_le_spectralCoeff (I := I) (M := M) g₀ k
  refine ⟨C, hC_nn, ?_⟩
  rw [spectralToPouSobolevCLM]
  exact LinearMap.opNorm_extendOfNorm_le
    (denseRange_spectralCoeffLinearMap (I := I) (M := M) g₀ k) hC_nn hC

/-- **Faithful pin of the transfer CLM on the dense range.** For every smooth `T`, the
transfer CLM transmits the exact order-`2k` chart-Sobolev norm of `T`'s image:
`‖spectralToPouSobolevCLM (spectralCoeff T)‖ = ‖T.toHs (2k)‖`.  This is an immediate
consequence of the realization-compatibility identity, and certifies the map is not a
degenerate/vacuous operator (the zero map satisfies it only where `T.toHs (2k) = 0`). -/
theorem spectralToPouSobolevCLM_apply_spectralCoeff_norm (T : SmoothCcTensor g₀ 0 2) :
    ‖spectralToPouSobolevCLM (I := I) (M := M) g₀ k
        (spectralCoeffLinearMap (I := I) (M := M) g₀ k T)‖ =
      ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (2 * k) T‖ := by
  rw [spectralToPouSobolevCLM_apply_spectralCoeff]

/-- The order-`0` chart-Sobolev norm of a smooth section is bounded by its order-`2k`
chart-Sobolev norm (Sobolev norms are monotone in the regularity order,
`tensorPouSobolevHsNorm_le_succ` iterated). -/
private theorem toHs_zero_norm_le_toHs (T : SmoothCcTensor g₀ 0 2) :
    ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) 0 T‖ ≤
      ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (2 * k) T‖ := by
  rw [tensorPouSobolevHilbert_norm_eq (I := I) (M := M) g₀ 0 T,
    tensorPouSobolevHilbert_norm_eq (I := I) (M := M) g₀ (2 * k) T]
  refine ENNReal.toReal_mono ?_ ?_
  · exact (tensorPouSobolevHsNorm_lt_top (I := I) (M := M) g₀ (2 * k) T).ne
  · have hmono : ∀ j : ℕ,
        tensorPouSobolevHsNorm (I := I) (M := M) g₀ 0 T ≤
          tensorPouSobolevHsNorm (I := I) (M := M) g₀ j T := by
      intro j
      induction j with
      | zero => exact le_refl _
      | succ n ih => exact ih.trans (tensorPouSobolevHsNorm_le_succ (I := I) (M := M) g₀ n T)
    exact hmono (2 * k)

/-- **The transfer CLM is not the zero map.** Given a spectral index `i₀` (the
nondegeneracy that the eigenbasis is nonempty — equivalently the connection-Laplacian has
a nonzero eigenvalue), the smooth eigenvector `eigenvectorSmooth i₀` has unit `L²` norm,
hence a positive order-`2k` chart-Sobolev norm, and the realization-compatibility identity
pins `spectralToPouSobolevCLM` to that nonzero value. -/
theorem spectralToPouSobolevCLM_ne_zero
    (i₀ : TensorEigenIdx (I := I) (M := M) g₀ 0 2) :
    spectralToPouSobolevCLM (I := I) (M := M) g₀ k ≠ 0 := by
  classical
  set T₀ : SmoothCcTensor g₀ 0 2 :=
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorSmooth
      (I := I) (M := M) g₀ 0 2 i₀ with hT₀_def
  -- `‖T₀‖ = 1`, since its `L²` class is the unit eigenbasis vector.
  have hT₀_norm : ‖SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) T₀‖ = 1 := by
    rw [show SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) T₀ =
          ((T₀ : TensorL2 0 2 g₀)) from SmoothCcTensor.toL2_apply _]
    rw [hT₀_def, DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorSmooth_toL2
      (I := I) (M := M) g₀ 0 2 i₀]
    exact (tensorResolventEigenbasisVec_orthonormal (I := I) (M := M)
      (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)).norm_eq_one i₀
  -- `‖T₀.toHs 0‖ > 0` from the `L² ≤ C · H⁰_chart` comparison.
  obtain ⟨C, _hC_nn, hC⟩ := exists_l2Norm_le_toHs_zero (I := I) (M := M) g₀
  have hpos0 : 0 < ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) 0 T₀‖ := by
    by_contra hle
    have hzero : ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) 0 T₀‖ = 0 :=
      le_antisymm (not_lt.mp hle) (norm_nonneg _)
    have hbd := hC T₀
    rw [hzero, mul_zero] at hbd
    rw [hT₀_norm] at hbd
    linarith
  -- `‖T₀.toHs (2k)‖ > 0` by order monotonicity.
  have hpos : 0 < ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (2 * k) T₀‖ :=
    lt_of_lt_of_le hpos0 (toHs_zero_norm_le_toHs (I := I) (M := M) g₀ k T₀)
  -- Hence the value of `Φ` at `spectralCoeff T₀` is nonzero, so `Φ ≠ 0`.
  intro hΦ
  have hval := spectralToPouSobolevCLM_apply_spectralCoeff (I := I) (M := M) g₀ k T₀
  rw [hΦ] at hval
  simp only [ContinuousLinearMap.zero_apply] at hval
  rw [← hval] at hpos
  simp only [norm_zero, lt_self_iff_false] at hpos

end CLM

end SobolevScale
end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
