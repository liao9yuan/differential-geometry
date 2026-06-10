import DifferentialGeometry.Geometry.Flow.RicciFlow.Pullback.Cartan.LieDerivSectionCartan
import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.ConnectionDifferenceKoszul
import DifferentialGeometry.Geometry.Connection.ChartTensorNabla.Agreement.Tensor0SRSCovariantDerivativeAgreement
import DifferentialGeometry.Geometry.Connection.MetricCompatibility.CovGradCovDerivCommutation
import DifferentialGeometry.Analysis.Spectral.Tensor.Variational.CovDerivPointwise

/-! # The first covariant gradient of the symmetrised-lowered DeTurck field

For a closed (compact, boundaryless) smooth Riemannian manifold `(M, g₀)` modelled on a real
inner-product space `E`, this file supplies the **foundational covariant-Faà-di-Bruno building block**
beneath the gauge half of the Ricci–DeTurck linearization: the **first** `g₀`-Levi-Civita covariant
gradient of the symmetrised-`g₁`-lowering of `∇^{g₁}W`, `W = deTurckVF g₁ g_bg`.

The section `symLoweredDeTurckVF g₁ g_bg` (built in `LieDerivSectionCartan.lean`) is the symmetrised
`g₁`-lowering of the Levi-Civita covariant gradient of the DeTurck vector field: its fibre value is
the **Cartan bilinear form** `cartanRHSBilin g₁ W x = g₁(∇^{g₁}_v W, w) + g₁(v, ∇^{g₁}_w W)`.  Its
`g₀`-retag `symLoweredDeTurckVFRetagG0 g₀ g₁ g_bg` carries the same underlying section under the `g₀`
type tag (`LieDerivSectionCartan.lean`), so it is the carrier on which the `g₀`-Levi-Civita covariant
gradient `covGrad g₀ 0 2` acts.

## What this file proves

* `symLoweredDeTurckVFRetagG0_unitModel_eq` — the **order-0 fibre identity**: the unit-evaluated model
  `(0, 2)`-value of `symLoweredDeTurckVFRetagG0 g₀ g₁ g_bg` is exactly the Cartan bilinear form
  `cartanRHSBilin g₁ (deTurckVF g₁ g_bg)`.  This is the `(0, 2)` carrier the linear / quadratic engine
  arms wrap.

* `symLoweredDeTurckVF_covGrad_section_expansion` — the **first-covariant-gradient expansion**: the
  unit-evaluated model `(0, 3)`-value of the first covariant gradient
  `covGrad g₀ 0 2 (symLoweredDeTurckVFRetagG0 g₀ g₁ g_bg)`, read on a tangent triple `![u, v, w]`
  (`u` the gradient direction, `v, w` the two Cartan slots), equals the Leibniz product-rule expansion
  of the Cartan bilinear form: the `u`-directional derivative of `x ↦ cartanRHSBilin g₁ W x (V, W)`
  minus the two correction terms in which the `g₀`-Levi-Civita derivative falls on the frame
  extensions of `v` and `w`.  This is the rank-`2` sibling of
  `tensorCovDerivAt_loweredConnDiffSection_unitModel_eq` (the lowered connection-difference covariant
  derivative), specialised to the Cartan section.

## Why this is the `≤ 2`-in-metric Faà-di-Bruno building block

The Cartan bilinear form is order-`≤ 2` in the metric: `W = deTurckVF g₁ g_bg` is the `g₁`-trace of
the connection difference `connDiff (g₁, g_bg)` (`deTurckVF_apply_eq`), a `g₁⁻¹·∂g₁`-type field
(order-`1`), and the lowering pairs its **inner** `g₁`-Levi-Civita covariant gradient `∇^{g₁}W`
through `g₁.inner`, adding one more metric-derivative slot.  The **outer** covariant gradient applied
here uses the *background* `g₀`-Levi-Civita derivative; the Leibniz expansion exposes the directional
derivative of the Cartan form and the two `g₀`-Christoffel correction terms.  This is exactly the
order-by-order structure the linear arm (`DiffBilinOp`) and the quadratic arm (`RfnsBilinearProduct`)
consume: the carrier is the `(0, 2)` Cartan section, and its single covariant gradient is the
`(0, 3)`-form whose fibre value this identity pins.

## Non-vacuity

The expansion is a genuine algebraic identity, not a tautology: at `g₁ = g₀` against itself the
DeTurck field vanishes (`deTurckVF_self`), so `W = 0`, `∇^{g₁}W = 0`, the Cartan bilinear form is the
zero form (`cartanRHSBilin` is built from `(LeviCivita g₁) W`, linear in `W`), and both sides reduce
to `0`; for a non-trivial pair the form is genuinely nonzero and reads the inner `∇^{g₁}W`.  The
identity carries the full Leibniz expansion (directional derivative plus the two Christoffel
corrections), so it is not the degenerate "value only" reading. -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open Bundle Manifold Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry
namespace PDE
namespace DeTurck

open DifferentialGeometry
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2 (SmoothCcTensor)
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.Pullback
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open Tensor0SNabla

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

/-- **The order-0 fibre identity of the symmetrised-lowered DeTurck field.**

The unit-evaluated model `(0, 2)`-value of the `g₀`-retagged symmetrised covariant lowering of the
DeTurck vector field `symLoweredDeTurckVFRetagG0 g₀ g₁ g_bg`, read on a tangent pair `![v, w]`, is
exactly the intrinsic Cartan bilinear form
`cartanRHSBilin g₁ (deTurckVF g₁ g_bg) x v w = g₁(∇^{g₁}_v W, w) + g₁(v, ∇^{g₁}_w W)`.

The retag carries the identical underlying section as `symLoweredDeTurckVF g₁ g_bg`
(`symLoweredDeTurckVFRetagG0`), whose unit-evaluated value is the Cartan form by
`symLoweredDeTurckVF_toModel_apply`; this is that fibre identity transported through the pure type-tag
change.  This `(0, 2)` value is the carrier the engine arms `DiffBilinOp` / `RfnsBilinearProduct`
wrap. -/
theorem symLoweredDeTurckVFRetagG0_unitModel_eq (g₀ g₁ g_bg : SmoothRiemannianMetric I M) (x : M)
    (v w : TangentSpace I x) :
    Tensor0SSpace.toModel
        ((symLoweredDeTurckVFRetagG0 (I := I) g₀ g₁ g_bg).toSection x
          (ContinuousMultilinearMap.constOfIsEmpty ℝ
            (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))) ![v, w] =
      cartanRHSBilin (I := I) g₁ (deTurckVF (I := I) g₁ g_bg) x v w := by
  classical
  have hsec : (symLoweredDeTurckVFRetagG0 (I := I) g₀ g₁ g_bg).toSection =
      (symLoweredDeTurckVF (I := I) g₁ g_bg).toSection := rfl
  rw [show ((symLoweredDeTurckVFRetagG0 (I := I) g₀ g₁ g_bg).toSection x
        (ContinuousMultilinearMap.constOfIsEmpty ℝ
          (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))) =
      ((symLoweredDeTurckVF (I := I) g₁ g_bg).toSection x
        (ContinuousMultilinearMap.constOfIsEmpty ℝ
          (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))) from by rw [hsec]]
  rw [symLoweredDeTurckVF_toModel_apply]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]

/-- **The first covariant gradient of the symmetrised-lowered DeTurck field, expanded into its Cartan
bilinear structure.**

The unit-evaluated model `(0, 3)`-value of the **first** `g₀`-Levi-Civita covariant gradient
`covGrad g₀ 0 2 (symLoweredDeTurckVFRetagG0 g₀ g₁ g_bg)`, read on a tangent triple `![u, v, w]`
(`u` the gradient/direction slot, `v, w` the two Cartan-bilinear slots), equals the Leibniz
product-rule expansion of the Cartan bilinear form `B x := cartanRHSBilin g₁ (deTurckVF g₁ g_bg) x`:
$$
  (\nabla_u^{g_0} B)(v, w)
    = \partial_u\bigl(B\,(V, W)\bigr)
      - B\bigl(\nabla^{g_0}_u V,\; w\bigr)
      - B\bigl(v,\; \nabla^{g_0}_u W\bigr),
$$
where `V = smoothExtensionTangent x v`, `W = smoothExtensionTangent x w` are the chosen smooth frame
extensions and `∇^{g_0}` is the `g₀`-Levi-Civita derivative.

This is the genuine **first-covariant-gradient expansion**: it pins the `(0, 3)`-fibre value of `∇W`
(the `g₀`-Levi-Civita gradient of the Cartan `(0, 2)`-carrier) to the directional derivative of the
Cartan form plus the two `g₀`-Christoffel correction terms — the ≤2-in-metric Faà-di-Bruno building
block.  The carrier `B` is itself order-`≤ 2` in the metric (`W` the `g₁`-trace of
`connDiff (g₁, g_bg)`, lowered through `g₁.inner` against its inner `g₁`-covariant gradient
`∇^{g₁}W`), and this outer single `g₀`-gradient is the `(0, 3)`-form the engine arms differentiate.

**Mechanism.**  `tensorCovDerivAt_def` unfolds the bundled `(0, 2)`-tensor covariant derivative;
`tensorRSCovariantDerivative_zeroS_unit_eval` descends the unit-evaluation through the parallel unit
`(0, 0)`-section (no correction term) to the abstract `tensor0SCovariantDerivative` of the
unit-evaluated section; and `tensorCovDeriv02_eval` is the first-order `(0, 2)`-tensor covariant
Leibniz product rule, whose terms are rewritten through the order-0 fibre identity
`symLoweredDeTurckVFRetagG0_unitModel_eq` into the Cartan bilinear form.  The leading gradient slot of
`covGrad g₀ 0 2 …` is read by `covGrad_toSection_apply_eval`. -/
theorem symLoweredDeTurckVF_covGrad_section_expansion
    (g₀ g₁ g_bg : SmoothRiemannianMetric I M) (x : M) (u v w : TangentSpace I x) :
    Tensor0SSpace.toModel
        ((Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g₀ 0 2
            (symLoweredDeTurckVFRetagG0 (I := I) g₀ g₁ g_bg)).toSection x
          (ContinuousMultilinearMap.constOfIsEmpty ℝ
            (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))) ![u, v, w] =
      directionalDeriv (I := I)
          (fun y : M => cartanRHSBilin (I := I) g₁ (deTurckVF (I := I) g₁ g_bg) y
            (smoothExtensionTangent (I := I) x v y)
            (smoothExtensionTangent (I := I) x w y)) x u
        - cartanRHSBilin (I := I) g₁ (deTurckVF (I := I) g₁ g_bg) x
            ((LeviCivita (I := I) g₀).toFun (smoothExtensionTangent (I := I) x v) x u) w
        - cartanRHSBilin (I := I) g₁ (deTurckVF (I := I) g₁ g_bg) x v
            ((LeviCivita (I := I) g₀).toFun (smoothExtensionTangent (I := I) x w) x u) := by
  classical
  -- The unit `(0,0)`-tensor.
  have hunit0 : (ContinuousMultilinearMap.constOfIsEmpty ℝ
      (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ)) = unitZeroSec (I := I) (M := M) x := rfl
  -- Read the leading (gradient) slot `u` off `covGrad g₀ 0 2 …`.
  rw [covGrad_toSection_apply_eval (I := I) (M := M) g₀ 0 2
    (symLoweredDeTurckVFRetagG0 (I := I) g₀ g₁ g_bg) x
    (ContinuousMultilinearMap.constOfIsEmpty ℝ
      (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ)) ![u, v, w]]
  -- `![u, v, w] 0 = u`; the remaining tail is `![v, w]`.
  rw [show (![u, v, w] : Fin 3 → TangentSpace I x) 0 = u from rfl]
  rw [show Matrix.vecTail (![u, v, w] : Fin 3 → TangentSpace I x) = ![v, w] from by
    funext i; fin_cases i <;> rfl]
  -- Unfold the directional covariant derivative and descend the unit-evaluation.
  rw [hunit0, tensorCovDerivAt_def (I := I) (M := M) g₀ 0 2
      (symLoweredDeTurckVFRetagG0 (I := I) g₀ g₁ g_bg) x u,
    tensorRSCovariantDerivative_zeroS_unit_eval (I := I) (M := M) g₀ 2
      (symLoweredDeTurckVFRetagG0 (I := I) g₀ g₁ g_bg).toSection x u]
  -- The unit-evaluated `(0,2)`-section of the carrier.
  set V2 : Π y : M, Tensor0SSpace 2 I y := fun y : M =>
    (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace 2 I y from
      (symLoweredDeTurckVFRetagG0 (I := I) g₀ g₁ g_bg).toSection y)
      (unitZeroSec (I := I) (M := M) y) with hV2def
  have hV2_at : TensorSectionMDiffAt (I := I) 2 V2 x := by
    unfold TensorSectionMDiffAt
    have h := contMDiff_unitEvalSection (I := I) (M := M) g₀ 2
      (symLoweredDeTurckVFRetagG0 (I := I) g₀ g₁ g_bg)
    exact (h x).mdifferentiableAt (by simp)
  -- Apply the first-order `(0,2)`-tensor covariant Leibniz product rule.
  rw [tensorCovDeriv02_eval g₀ V2 hV2_at v w u]
  -- Rewrite each fibre value through the order-0 Cartan fibre identity.
  have hval : ∀ (y : M) (p q : TangentSpace I y),
      Tensor0SSpace.toModel (V2 y) ![p, q] =
        cartanRHSBilin (I := I) g₁ (deTurckVF (I := I) g₁ g_bg) y p q := fun y p q =>
    symLoweredDeTurckVFRetagG0_unitModel_eq (I := I) g₀ g₁ g_bg y p q
  rw [show (fun y : M => Tensor0SSpace.toModel (V2 y)
        ![smoothExtensionTangent (I := I) x v y, smoothExtensionTangent (I := I) x w y]) =
      (fun y : M => cartanRHSBilin (I := I) g₁ (deTurckVF (I := I) g₁ g_bg) y
        (smoothExtensionTangent (I := I) x v y)
        (smoothExtensionTangent (I := I) x w y)) from by funext y; exact hval y _ _]
  rw [hval x ((LeviCivita (I := I) g₀).toFun (smoothExtensionTangent (I := I) x v) x u) w,
    hval x v ((LeviCivita (I := I) g₀).toFun (smoothExtensionTangent (I := I) x w) x u)]

/-- **Non-vacuity: the first-covariant-gradient expansion of the DeTurck field against itself
vanishes.**  When `g₁` is taken against itself in the DeTurck field — i.e. the background equals the
evolving metric, `g_bg = g₁` — the DeTurck vector field is the zero section (`deTurckVF_self`), so the
Cartan bilinear form `cartanRHSBilin g₁ (deTurckVF g₁ g₁)` is the zero form (it is built from
`(LeviCivita g₁) W`, linear in `W = 0`), and the first-covariant-gradient expansion reduces to
`0 = 0 − 0 − 0`.  This certifies the identity is genuinely the gradient of the Cartan structure (it
collapses on the degenerate witness), not a constant nonzero `(0, 3)`-form. -/
theorem symLoweredDeTurckVF_covGrad_section_expansion_self
    (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) (u v w : TangentSpace I x) :
    Tensor0SSpace.toModel
        ((Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g₀ 0 2
            (symLoweredDeTurckVFRetagG0 (I := I) g₀ g₁ g₁)).toSection x
          (ContinuousMultilinearMap.constOfIsEmpty ℝ
            (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))) ![u, v, w] = 0 := by
  classical
  -- The Cartan form of the self-DeTurck field is the Lie deformation along the zero field, which
  -- vanishes (`cartanRHSBilin_eq_lieDerivMetric`, `deTurckVF_self`, `lieDerivMetric_zero`).
  have hcartan_zero : ∀ (y : M) (p q : TangentSpace I y),
      cartanRHSBilin (I := I) g₁ (deTurckVF (I := I) g₁ g₁) y p q = 0 := by
    intro y p q
    rw [cartanRHSBilin_eq_lieDerivMetric, deTurckVF_self (I := I) g₁,
      lieDerivMetric_zero (I := I) g₁]
    simp
  rw [symLoweredDeTurckVF_covGrad_section_expansion (I := I) g₀ g₁ g₁ x u v w]
  rw [show (fun y : M => cartanRHSBilin (I := I) g₁ (deTurckVF (I := I) g₁ g₁) y
        (smoothExtensionTangent (I := I) x v y)
        (smoothExtensionTangent (I := I) x w y)) = (fun _ : M => (0 : ℝ)) from by
    funext y; exact hcartan_zero y _ _]
  rw [hcartan_zero x _ w, hcartan_zero x v _]
  simp [directionalDeriv]

end DeTurck
end PDE
end DifferentialGeometry

end
