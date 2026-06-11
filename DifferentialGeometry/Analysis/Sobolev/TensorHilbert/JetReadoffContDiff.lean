import DifferentialGeometry.Analysis.Sobolev.Embedding.SobolevEmbeddingCmOrderReduction
import DifferentialGeometry.Analysis.Sobolev.Embedding.RawConnLapToHsOrderDropping
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.SmoothCcDense
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.SpectralToPouSobolevCLM

/-! # The fixed-order chart-Sobolev jet read-off as a continuous linear map (`H^q → H^a`,
order-dropping, hence `C^∞`)

The chart `≤ 2`-jet of a realized metric `g₁ = g₀ + ccTensorBilinSymm g₀ T` enters every
chart-rational DeTurck quantity (Christoffel, Ricci, Lie, the inverse-Gram Neumann denominator)
through the perturbation section `T`; a downstream consumer reads that jet at a **fixed** lower
Sobolev order — the honest two-derivative loss `a = q − 2` — and assembles the retag rationally
from there.  This file isolates the *linear backbone* of that read-off: the canonical inclusion of
the order-`q` chart-Sobolev Hilbert completion into the order-`a` completion,

  `toHsOrderDropCLM g a q (hq : a ≤ q) : TensorPouSobolevHilbert g r s q →L[ℝ]
                                          TensorPouSobolevHilbert g r s a`,

the dense extension of the identity section map `T ↦ T` read at the dropped order.  It is a genuine
**continuous linear map** — its `‖·‖_{H^q}`-domination is the order-monotonicity of the chart-Sobolev
norm (`toHs_norm_mono_order`, `a ≤ q`) — and, being continuous-linear, it is `ContDiff ℝ ∞` for free
(`ContinuousLinearMap.contDiff`).  That is the whole point: the depth is in *constructing* the CLM
(the order-dropping inclusion is a well-defined bounded linear map between the fixed-order
completions); differentiating it is then trivial, so the consumer obtains `ContDiffOn` of the
chart-Sobolev jet read-off by composing this CLM (on either side) with its bilinear-product and
inverse-Gram-Neumann bricks (`ContDiffOn.continuousLinearMap_comp`).

## Why this is fixed-order, not all-order (the bigraded jet wall)

A **single** chart-Sobolev space `H^{q}` does *not* read the full `C^∞` jet: `H^{q} ↪ C^N` only for
`N < q/2 − dim M / 2`, so the jet order `N` and the Sobolev exponent `q` are genuinely coupled.  This
file therefore states only a **fixed-order** read-off: the inclusion `H^q → H^a` at the fixed pair
`(q, a)` with `a ≤ q`.  There is no all-order single-space claim and no single uniform constant
across all orders — the order drop `q − a` is the explicit, finite derivative budget the consumer
spends.  (The construction mirrors the on-disk order-dropping CLMs `rawConnLapToHsCLM` /
`deTurckG0SpectralLiftCLM`, replacing the rough-Laplacian / spectral section map by the identity.)

## Sorry-free

The construction is sorry-free: `LinearMap.extendOfNorm` of the identity-section completion map,
whose linearity is `SmoothCcTensor.toHs_add` / `smoothCcTensor_toHs_smul`, whose domination is
`toHs_norm_mono_order`, and whose dense range is `smoothCcTensor_denseRange_toHs`. -/

noncomputable section

open Bundle
open scoped Manifold ContDiff NNReal ENNReal Topology BigOperators

namespace DifferentialGeometry.Analysis.Sobolev.TensorHilbert

open DifferentialGeometry
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

/-- The order-`a` chart-Sobolev completion embedding `T ↦ T.toHs a` of smooth compactly-supported
`(r, s)`-tensor sections, packaged as an `ℝ`-linear map
`SmoothCcTensor g r s →ₗ[ℝ] TensorPouSobolevHilbert g r s a`.  Additivity is
`SmoothCcTensor.toHs_add` and scalar-homogeneity is `smoothCcTensor_toHs_smul` (both the
completion-coercion laws of the `SmoothCcTensorHs` wrapper).  This is the dense linear map both the
source order `q` and the target order `a` of the inclusion CLM factor through. -/
def toHsLinearMap (g : SmoothRiemannianMetric I M) (r s a : ℕ) :
    Integral.L2.SmoothCcTensor g r s →ₗ[ℝ]
      IntrinsicSobolev.TensorPouSobolevHilbert (I := I) (M := M) g r s a where
  toFun T := IntrinsicSobolev.SmoothCcTensor.toHs (g := g) (r := r) (s := s) a T
  map_add' S T :=
    DifferentialGeometry.PDE.RicciFlow.SmoothCcTensor.toHs_add (I := I) (M := M) (g := g) a S T
  map_smul' c T := by
    simp only [RingHom.id_apply]
    exact DifferentialGeometry.Analysis.Parabolic.TensorSpectral.SobolevScale.smoothCcTensor_toHs_smul
      (I := I) (M := M) (g := g) a c T

@[simp] theorem toHsLinearMap_apply (g : SmoothRiemannianMetric I M) (r s a : ℕ)
    (T : Integral.L2.SmoothCcTensor g r s) :
    toHsLinearMap (I := I) g r s a T =
      IntrinsicSobolev.SmoothCcTensor.toHs (g := g) (r := r) (s := s) a T := rfl

set_option linter.unusedVariables false in
/-- **The order-dropping chart-Sobolev inclusion continuous linear map `H^q → H^a` (`a ≤ q`,
sorry-free).**

The dense extension (`LinearMap.extendOfNorm`) of the identity section map `T ↦ T`, read at the
lower order `a`, along the dense order-`q` chart-Sobolev embedding `T ↦ T.toHs q`.  Its `ℝ`-linearity
is `toHsLinearMap g r s a`; its `‖·‖_{H^q}`-domination is the chart-Sobolev order-monotonicity
`toHs_norm_mono_order` (`a ≤ q`); its dense range is `smoothCcTensor_denseRange_toHs`.  The order
hypothesis `hq : a ≤ q` is the well-definedness gate of the order drop (it is what makes the CLM
agree with the inclusion on smooth sections, via the domination bound — see
`toHsOrderDropCLM_apply_toHs`); restricting the construction to `a ≤ q` keeps the map's contract
honest, so `hq` is genuinely load-bearing even though the bare `extendOfNorm` term does not mention
it.

This is the **linear backbone of the fixed-order chart `≤ 2`-jet read-off**: the perturbation
section's class, read two orders down (`a = q − 2`), is what every chart-rational DeTurck quantity is
assembled from.  Being a continuous linear map, it is `ContDiff ℝ ∞`
(`contDiff_toHsOrderDropCLM`), so a downstream consumer obtains `ContDiffOn` of the assembled retag
by composing it with the bilinear-product and inverse-Gram-Neumann smoothness bricks.  Its defining
identity on the dense smooth sections is `toHsOrderDropCLM_apply_toHs`. -/
def toHsOrderDropCLM (g : SmoothRiemannianMetric I M) (r s a q : ℕ) (hq : a ≤ q) :
    IntrinsicSobolev.TensorPouSobolevHilbert (I := I) (M := M) g r s q →L[ℝ]
      IntrinsicSobolev.TensorPouSobolevHilbert (I := I) (M := M) g r s a :=
  LinearMap.extendOfNorm
    (toHsLinearMap (I := I) g r s a)
    (toHsLinearMap (I := I) g r s q)

/-- **The defining identity of the order-dropping chart-Sobolev inclusion CLM on the dense range.**
For every smooth compactly-supported section `T`, `toHsOrderDropCLM g r s a q hq (T.toHs q) =
T.toHs a` — the inclusion is the identity on smooth sections, re-read at the lower order. -/
@[simp] theorem toHsOrderDropCLM_apply_toHs (g : SmoothRiemannianMetric I M) (r s a q : ℕ)
    (hq : a ≤ q) (T : Integral.L2.SmoothCcTensor g r s) :
    toHsOrderDropCLM (I := I) g r s a q hq
        (IntrinsicSobolev.SmoothCcTensor.toHs (g := g) (r := r) (s := s) q T)
      = IntrinsicSobolev.SmoothCcTensor.toHs (g := g) (r := r) (s := s) a T := by
  have hnorm : ∃ C : ℝ, ∀ R : Integral.L2.SmoothCcTensor g r s,
      ‖toHsLinearMap (I := I) g r s a R‖ ≤ C * ‖toHsLinearMap (I := I) g r s q R‖ := by
    refine ⟨1, fun R => ?_⟩
    rw [toHsLinearMap_apply, toHsLinearMap_apply, one_mul]
    exact toHs_norm_mono_order (I := I) (M := M) g hq R
  have hext := LinearMap.extendOfNorm_eq
    (f := toHsLinearMap (I := I) g r s a)
    (e := toHsLinearMap (I := I) g r s q)
    (IntrinsicSobolev.smoothCcTensor_denseRange_toHs (I := I) g r s q) hnorm T
  rw [toHsLinearMap_apply, toHsLinearMap_apply] at hext
  rw [toHsOrderDropCLM]
  exact hext

/-- **The order-dropping chart-Sobolev inclusion CLM is `ContDiff ℝ ∞`.**  A continuous linear map is
`C^∞` (`ContinuousLinearMap.contDiff`); this is the linear backbone's contribution to the consumer's
`ContDiffOn` of the assembled chart-Sobolev jet read-off (compose on either side via
`ContDiffOn.continuousLinearMap_comp` or `.comp_continuousLinearMap`). -/
theorem contDiff_toHsOrderDropCLM (g : SmoothRiemannianMetric I M) (r s a q : ℕ) (hq : a ≤ q) :
    ContDiff ℝ (∞ : WithTop ℕ∞) (toHsOrderDropCLM (I := I) g r s a q hq) :=
  (toHsOrderDropCLM (I := I) g r s a q hq).contDiff (n := (∞ : WithTop ℕ∞))

/-- **The order-dropping chart-Sobolev inclusion CLM is `ContDiffOn ℝ ∞` on any set.**  The on-set
form of `contDiff_toHsOrderDropCLM`, the shape a consumer pre-composes with a validity-ball map. -/
theorem contDiffOn_toHsOrderDropCLM (g : SmoothRiemannianMetric I M) (r s a q : ℕ) (hq : a ≤ q)
    (U : Set (IntrinsicSobolev.TensorPouSobolevHilbert (I := I) (M := M) g r s q)) :
    ContDiffOn ℝ (∞ : WithTop ℕ∞) (toHsOrderDropCLM (I := I) g r s a q hq) U :=
  (contDiff_toHsOrderDropCLM (I := I) g r s a q hq).contDiffOn

end DifferentialGeometry.Analysis.Sobolev.TensorHilbert

end
