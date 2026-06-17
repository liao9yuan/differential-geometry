import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.BareTensorProductCovariantLeibniz
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CovariantBilinearLeibniz

/-! # The intrinsic metric-variation foundation of the Ricci–DeTurck right-hand side

For a closed (compact, boundaryless) smooth Riemannian manifold `(M, g)` modelled on a real
inner-product space `E`, the Ricci–DeTurck right-hand side
`F(g) = −2 Ric(g) + 𝓛_{W(g, g_bg)}(g)` is a second-order quasilinear Nemytskii nonlinearity in the
metric.  Its mean-value Fréchet linearization `dF(g)[h]` is a second-order operator
`coeff₀·h + coeff₁·∇h + coeff₂·∇²h` whose intrinsic, chart-free symbols are built from the curvature,
the Christoffel variation, and the inverse-metric (Neumann-series) variation along the metric path.

This file builds the **chart-free `unitModel`-extensionality foundation** of that linearization — the
keystone every concrete `SmoothCcTensor`-valued metric-variation identity needs to lift its on-disk
`unitModel`-component form to a genuine `SmoothCcTensor` equality:

* `smoothCcTensor_ext_of_unitModel` — lifts a pointwise `unitModel`-component equality of two smooth
  compactly-supported `(0, s)`-tensors to a genuine `SmoothCcTensor` equality (the general-rank form of
  the rank-`3` unit-extensionality `tensor03_ext_unit`), via the unit-tensor scalar identity
  `zeroTensor_eq_smul_unitTensor`, the unit-CLM-extensionality `tensor0s_clm_ext_unit`, and
  `Tensor0SSpace.toModel`-injectivity.  No concrete `ParallelTensorProduct` value or section-level
  metric-variation identity exists on disk; this bridge is the missing primitive they all require.
* `unitModel_add`, `unitModel_castRankCc` — the additivity and rank-cast compatibility of the
  `unitModel`-component map, the bookkeeping lemmas the lift consumes.

Everything is phrased in `unitModel` / `covGrad` / `Tensor0SSpace.toModel` — `g`-native and chart-free;
never a chart-jet ball Lipschitz chain, never the model `opNorm`, never the chart-component route.

## Structural note on the concrete `ParallelTensorProduct` witness

The canonical concrete `ParallelTensorProduct` (`CovariantBilinearLeibniz.lean`) is NOT the bare model
tensor product `unitModelProdSection`: its `covGrad_prod` field is *false-as-stated* for the bare product.
By `unitModel_unitModelProdSection_covGrad_right` (`BareTensorProductCovariantLeibniz.lean:1248`) the
right covariant-Leibniz summand `prod S (∇T)` carries its new gradient slot at the *mid* position
`s₁ + a`, whereas `covGrad (prod S T)` carries it at the *front* position `0`; the field equation omits
the reconciling slot-permutation `domDomCongr σ`.  The exact-field witness is a `g₀`-parallel metric
*contraction* (which collapses the contracted slots and reindexes the surviving gradient slot to the
front), whose front-slot covariant Leibniz is genuine deep intrinsic content — built on top of this
extensionality bridge.

## Main results

* `smoothCcTensor_ext_of_unitModel` — `unitModel`-component extensionality for `SmoothCcTensor g 0 s`.
* `unitModel_add`, `unitModel_castRankCc` — `unitModel`-component additivity and rank-cast compatibility.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators Matrix

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.PDE.RicciFlow

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

/-! ## The `unitModel`-component extensionality bridge -/

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] in
/-- Every `(0, 0)`-tensor `D` is its scalar coordinate times the unit `(0, 0)`-tensor:
`D = (tensor0Iso M x D) • unitTensor x`.  The general-rank analogue of
`zeroTensor_eq_smul_unit`, stated for the `TensorSpectral.unitTensor` form (which is `rfl`-equal to
`unitZeroSec x`). -/
private theorem zeroTensor_eq_smul_unitTensor (x : M)
    (D : Tensor0SSpace 0 I x) :
    D = (Tensor0SNabla.tensor0Iso I M x D) • unitTensor (I := I) (M := M) x := by
  classical
  have hunit : Tensor0SNabla.tensor0Iso I M x (unitTensor (I := I) (M := M) x) = (1 : ℝ) := by
    have h := Tensor0SNabla.scalarFn_unitZero (I := I) (M := M)
    have hx := congrFun h x
    simpa [Tensor0SNabla.scalarFn_apply, unitTensor] using hx
  apply (Tensor0SNabla.tensor0Iso I M x).injective
  rw [map_smul, hunit, smul_eq_mul, mul_one]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] in
/-- **Unit-extensionality for `(0, s)`-tensors.** Two continuous linear maps
`φ, ψ : Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x` (i.e. two `(0, s)`-tensors) that agree on the
unit `(0, 0)`-tensor are equal.  The general-rank form of `tensor03_ext_unit`; the proof is
rank-independent (`zeroTensor_eq_smul_unitTensor` + `map_smul`). -/
private theorem tensor0s_clm_ext_unit {s : ℕ} {x : M}
    {φ ψ : Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x}
    (h : φ (unitTensor (I := I) (M := M) x) = ψ (unitTensor (I := I) (M := M) x)) :
    φ = ψ := by
  classical
  ext D
  rw [zeroTensor_eq_smul_unitTensor (I := I) (M := M) x D, map_smul, map_smul, h]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] in
/-- **`unitModel`-component extensionality for `SmoothCcTensor g 0 s`.**  Two smooth
compactly-supported `(0, s)`-tensors whose unit-evaluated model fibres agree at every base point are
equal.  This is the keystone bridge that lifts the on-disk unitModel-component covariant-Leibniz
identities (e.g. `unitModelProdSection_covGrad_unitModel`) to genuine `SmoothCcTensor` equalities.

`unitModel g s S x = toModel (S.toSection x (unitTensor x))`, so a pointwise `unitModel` equality gives,
through `Tensor0SSpace.toModel`-injectivity, the section value at the unit, and then through the
unit-extensionality `tensor0s_clm_ext_unit` the full section value; `SmoothCcTensor.ext` /
`ContMDiffSection.ext` close it. -/
theorem smoothCcTensor_ext_of_unitModel (g : SmoothRiemannianMetric I M) {s : ℕ}
    {S S' : SmoothCcTensor g 0 s}
    (h : ∀ x : M, unitModel (I := I) (M := M) g s S x = unitModel (I := I) (M := M) g s S' x) :
    S = S' := by
  classical
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  have hval : (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from S.toSection x)
      (unitTensor (I := I) (M := M) x) =
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from S'.toSection x)
        (unitTensor (I := I) (M := M) x) := by
    apply Tensor0SSpace.toModel_injective
    have := h x
    simpa [unitModel] using this
  exact tensor0s_clm_ext_unit (I := I) (M := M) hval

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M] in
/-- `unitModel` is additive in the section: `unitModel (S + S') = unitModel S + unitModel S'`. -/
private theorem unitModel_add (g : SmoothRiemannianMetric I M) (s : ℕ)
    (S S' : SmoothCcTensor g 0 s) (x : M) :
    unitModel (I := I) (M := M) g s (S + S') x =
      unitModel (I := I) (M := M) g s S x + unitModel (I := I) (M := M) g s S' x := by
  classical
  simp only [unitModel]
  rw [SmoothCcTensor.toSection_add, ContMDiffSection.coe_add, Pi.add_apply,
    ContinuousLinearMap.add_apply, Tensor0SSpace.toModel_add]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M] in
/-- The unit-evaluated model fibre of a rank-cast `castRankCc g 0 h W` is the rank-cast of the
unit-evaluated model fibre of `W`.  Proved by `subst` on the rank equality, which collapses the cast to
the identity on both sides. -/
private theorem unitModel_castRankCc (g : SmoothRiemannianMetric I M) {a b : ℕ} (h : a = b)
    (W : SmoothCcTensor g 0 a) (x : M) :
    unitModel (I := I) (M := M) g b (castRankCc g 0 h W) x =
      h ▸ unitModel (I := I) (M := M) g a W x := by
  subst h
  rfl

/-! ## The metric-contraction `ParallelTensorProduct` constructor (POSITED — deep)

The canonical concrete `ParallelTensorProduct` witness is a `g₀`-parallel metric *contraction* of a
tensor product, NOT the bare model tensor product `unitModelProdSection`.  The bare product fails the
`ParallelTensorProduct.covGrad_prod` field as literally stated: by `unitModel_unitModelProdSection_covGrad_right`
the right covariant-Leibniz summand `prod S (∇T)` carries its gradient slot at the *mid* position
`s₁ + a`, whereas `covGrad (prod S T)` carries the new gradient slot at the *front* position `0`; the
two differ by a slot-permutation `domDomCongr σ`, which the field does not insert.  A genuine
*contraction* against a parallel tensor (`∇ Φ = 0`) collapses the contracted slots and reindexes the
surviving gradient slot to the front, satisfying the field exactly.  Building that contraction's exact
covariant Leibniz (front-slot placement) is deep intrinsic content; it is posited here. -/

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry
