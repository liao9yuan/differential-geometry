import DifferentialGeometry.Geometry.Flow.RicciFlow.Pullback.Cartan.Formula
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.SegmentMetricRicciSectionIdentity
import DifferentialGeometry.Geometry.Operator.NormGradSq
import DifferentialGeometry.Geometry.Connection.TensorNabla.LiftedSectionCovariantRealizeBridge

/-! # The Lie deformation as the symmetrised covariant lowering of the DeTurck field

For a closed (compact, boundaryless) smooth Riemannian manifold `(M, g)` modelled on a real
inner-product space `E`, the sealed Lie-derivative summand `𝓛_{W(g)} g` of the Ricci–DeTurck
right-hand side is, by the **Cartan formula** `cartan_formula_for_lie_deriv_metric`, the symmetrised
`g`-lowering of the Levi-Civita covariant gradient of the DeTurck vector field
`W = deTurckVF g g_bg`:
$$
  (\mathcal L_W g)(v, w) = g(\nabla_v W, w) + g(v, \nabla_w W).
$$

This file builds the concrete `(0,2)`-tensor section `symLoweredDeTurckVF g g_bg` whose fibre value
is exactly this **intrinsic** right-hand side (built from `g.inner` and the Levi-Civita covariant
derivative `(LeviCivita g) W`, with no chart read), and proves that it equals the opaque sealed Lie
section `lieDerivCcSection g_bg g` (`lieDerivCcSection_eq_symLoweredCovGrad_deTurckVF`).

The point of this identification is to expose the `∇W`-structure of the Lie deformation at the
section level: `symLoweredDeTurckVF` is the symmetrised lowering of `∇W`, and `W` is the metric
`g`-trace of `connDiff (g, g_bg)`, so its covariant gradient is a covariant-Faà-di-Bruno contraction
of the metric jet — the structure the downstream gauge top/rest split rides through the
`DiffBilinOp` / `RfnsBilinearProduct` engine.  The opaque `lieDerivCcSection` (defined as the
algebraic complement `deTurckRHSSection g_bg g − ricciNeg2CcSection g`) hides this structure; the
Cartan identity recovers it.

The smoothness of the intrinsic field is **borrowed from the already-established chart-component
smoothness of `lieDerivMetric g W`** (`liederivmetric_chart_component_smooth_in_g_w_input`) through
the pointwise Cartan identity, so no new chart-coordinate boilerplate is re-derived. -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open Bundle Manifold Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace Pullback

open DifferentialGeometry
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.PDE.DeTurck
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

/-- **The intrinsic Cartan right-hand-side bilinear form.**  For a smooth metric `g` and a smooth
tangent vector field `W`, the symmetrised `g`-lowering of the Levi-Civita covariant gradient of `W`,
as a continuous bilinear form on `T_x M`:
`(v, w) ↦ g(∇_v W, w) + g(v, ∇_w W)`, where `∇ = LeviCivita g`.

By the Cartan formula `cartan_formula_for_lie_deriv_metric` this equals `lieDerivMetric g W x v w`. -/
def cartanRHSBilin (g : SmoothRiemannianMetric I M)
    (W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  (g.inner x).comp ((LeviCivita (I := I) g) (W : ∀ x : M, TangentSpace I x) x)
    + ((g.inner x).comp ((LeviCivita (I := I) g) (W : ∀ x : M, TangentSpace I x) x)).flip

/-- **The intrinsic Cartan bilinear form evaluated.**  `cartanRHSBilin g W x v w = g(∇_v W, w)
+ g(v, ∇_w W)`.  The second summand is the `g`-symmetry transpose of `g(∇_w W, v)`. -/
theorem cartanRHSBilin_apply (g : SmoothRiemannianMetric I M)
    (W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) (v w : TangentSpace I x) :
    cartanRHSBilin (I := I) g W x v w =
      g.inner x ((LeviCivita (I := I) g) (W : ∀ x : M, TangentSpace I x) x v) w
      + g.inner x v ((LeviCivita (I := I) g) (W : ∀ x : M, TangentSpace I x) x w) := by
  classical
  rw [cartanRHSBilin]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply]
  rw [g.symm x ((LeviCivita (I := I) g) (W : ∀ x : M, TangentSpace I x) x w) v]

/-- **The intrinsic Cartan bilinear form equals the Lie-derivative bilinear form.**  Direct from the
Cartan formula `cartan_formula_for_lie_deriv_metric`. -/
theorem cartanRHSBilin_eq_lieDerivMetric (g : SmoothRiemannianMetric I M)
    (W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) (v w : TangentSpace I x) :
    cartanRHSBilin (I := I) g W x v w = lieDerivMetric (I := I) g W x v w := by
  rw [cartanRHSBilin_apply, cartan_formula_for_lie_deriv_metric (I := I) g W x v w]

/-- The pointwise model `(0,2)`-tensor value of the intrinsic Cartan right-hand side. -/
def symLoweredModelFun (g : SmoothRiemannianMetric I M)
    (W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) : Tensor0SSpace 2 I x :=
  Tensor0SSpace.ofModel (bilinFormToModel (TangentSpace I x) (cartanRHSBilin (I := I) g W x))

theorem symLoweredModelFun_toModel_apply (g : SmoothRiemannianMetric I M)
    (W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) (v : Fin 2 → TangentSpace I x) :
    Tensor0SSpace.toModel (symLoweredModelFun (I := I) g W x) v =
      cartanRHSBilin (I := I) g W x (v 0) (v 1) := by
  unfold symLoweredModelFun
  rw [Tensor0SSpace.toModel_ofModel]
  exact bilinFormToModel_apply (TangentSpace I x) (cartanRHSBilin (I := I) g W x) v

/-- **The symmetrised lowering of `∇(deTurckVF)` as a smooth covariant `(0,2)`-tensor field.**  Its
fibre value is the intrinsic Cartan right-hand side `cartanRHSBilin g (deTurckVF g g_bg)`.  The
chart-component smoothness is **borrowed** from the already-established chart-component smoothness of
`lieDerivMetric g (deTurckVF g g_bg)` (`liederivmetric_chart_component_smooth_in_g_w_input`) through
the pointwise Cartan identity `cartanRHSBilin_eq_lieDerivMetric` (the same
`contMDiff_multilinearSection_iff_coord` route as `deTurckRHSField`). -/
def symLoweredDeTurckVFField (g g_bg : SmoothRiemannianMetric I M) :
    Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) ∞ 2 :=
  letI := tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 2
  letI := TangentBundle.contMDiffVectorBundle (I := I) (M := M) (n := ∞)
  ⟨fun x => symLoweredModelFun (I := I) g
      (deTurckVF (I := I) g g_bg : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x, by
    let d := Module.finrank ℝ E
    let b : Module.Basis (Fin d) ℝ E := chartModelBasis E
    refine (contMDiff_multilinearSection_iff_coord (TangentSpace I) ∞ b _).mpr
      fun σ x₀ => ?_
    set W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
      deTurckVF (I := I) g g_bg with hW
    have hcomp : ContMDiffOn I 𝓘(ℝ, ℝ) ∞
        (fun x : M =>
          cartanRHSBilin (I := I) g W x
            (chartFrameVec (I := I) x₀ (σ 0) x)
            (chartFrameVec (I := I) x₀ (σ 1) x))
        (chartAt H x₀).source := by
      have hlie : ContMDiffOn I 𝓘(ℝ, ℝ) ∞
          (fun x : M =>
            lieDerivMetric (I := I) g W x
              (chartFrameVec (I := I) x₀ (σ 0) x)
              (chartFrameVec (I := I) x₀ (σ 1) x))
          (chartAt H x₀).source :=
        liederivmetric_chart_component_smooth_in_g_w_input (I := I) g W x₀ (σ 0) (σ 1)
      refine hlie.congr (fun x _ => ?_)
      exact cartanRHSBilin_eq_lieDerivMetric (I := I) g W x
        (chartFrameVec (I := I) x₀ (σ 0) x) (chartFrameVec (I := I) x₀ (σ 1) x)
    have hx₀_src : x₀ ∈ (chartAt H x₀).source := mem_chart_source H x₀
    have hx₀_base : x₀ ∈ (trivializationAt E (TangentSpace I) x₀).baseSet :=
      mem_baseSet_trivializationAt E (TangentSpace I) x₀
    have h_src_nhd : (chartAt H x₀).source ∈ 𝓝 x₀ :=
      (chartAt H x₀).open_source.mem_nhds hx₀_src
    refine ((hcomp x₀ hx₀_src).contMDiffAt h_src_nhd).congr_of_eventuallyEq ?_
    have h_base_nhd :
        (trivializationAt E (TangentSpace I) x₀).baseSet ∈ 𝓝 x₀ :=
      (trivializationAt E (TangentSpace I) x₀).open_baseSet.mem_nhds hx₀_base
    filter_upwards [h_base_nhd] with x hx
    rw [continuousMultilinearMap_basis_repr]
    change Tensor0SSpace.toModel (symLoweredModelFun (I := I) g W x)
        (fun j => (trivializationAt E (TangentSpace I) x₀).symmL ℝ x (b (σ j))) = _
    rw [symLoweredModelFun_toModel_apply]
    rfl⟩

/-- The symmetrised lowering of `∇(deTurckVF)` as a smooth mixed `(0,2)`-tensor section. -/
def symLoweredDeTurckVFMixedSection (g g_bg : SmoothRiemannianMetric I M) :
    Cₛ^∞⟮I; TensorRSModel 0 2 ℝ E, (fun x : M => TensorRSSpace 0 2 I x)⟯ :=
  MixedSection.fromMultilinearSection (𝕜 := ℝ) (F := E) (IB := I)
    (E := (TangentSpace I : M → Type _)) ∞ (symLoweredDeTurckVFField (I := I) g g_bg)

/-- **The symmetrised covariant lowering of the DeTurck vector field as a `SmoothCcTensor g 0 2`.**
The concrete intrinsic representative of the sealed Lie deformation `𝓛_{W(g)} g`: its fibre value is
`g(∇_v W, w) + g(v, ∇_w W)`, `W = deTurckVF g g_bg`, `∇ = LeviCivita g`. -/
def symLoweredDeTurckVF (g g_bg : SmoothRiemannianMetric I M) :
    Integral.L2.SmoothCcTensor g 0 2 where
  toSection := symLoweredDeTurckVFMixedSection (I := I) g g_bg
  hasCompactSupport := HasCompactSupport.of_compactSpace _

/-- **The fibre value of the symmetrised covariant lowering of the DeTurck vector field.**
Evaluating at the canonical unit `(0,0)`-tensor and a tangent pair recovers the intrinsic Cartan
right-hand side `g(∇_v W, w) + g(v, ∇_w W)`. -/
theorem symLoweredDeTurckVF_toModel_apply (g g_bg : SmoothRiemannianMetric I M) (x : M)
    (v : Fin 2 → TangentSpace I x) :
    Tensor0SSpace.toModel
        ((symLoweredDeTurckVF (I := I) g g_bg).toSection x
          (ContinuousMultilinearMap.constOfIsEmpty ℝ
            (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))) v =
      cartanRHSBilin (I := I) g (deTurckVF (I := I) g g_bg) x (v 0) (v 1) := by
  classical
  change Tensor0SSpace.toModel
      ((MixedSection.eval₀ (F := E) (E := (TangentSpace I : M → Type _)) x).smulRight
          (symLoweredDeTurckVFField (I := I) g g_bg x)
        (ContinuousMultilinearMap.constOfIsEmpty ℝ
          (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))) v = _
  rw [ContinuousLinearMap.smulRight_apply, MixedSection.eval₀_apply,
    ContinuousMultilinearMap.constOfIsEmpty_apply, one_smul]
  change Tensor0SSpace.toModel (symLoweredModelFun (I := I) g (deTurckVF (I := I) g g_bg) x) v = _
  rw [symLoweredModelFun_toModel_apply]

/-- **(P1a — the section-level Cartan identity.)**  The sealed `g₀`-Lie-derivative summand section
`lieDerivCcSection g_bg g` equals the symmetrised covariant lowering of the DeTurck vector field
`symLoweredDeTurckVF g g_bg`.

This is the **section-level Cartan formula**: lifted pointwise from
`cartan_formula_for_lie_deriv_metric` (the soundness pivot, kept at the `toModel`-fibre-value level,
exactly as `koszulCombSection_toModel_apply` lifts the Koszul formula), it re-expresses the opaque
algebraic-complement Lie section (`deTurckRHSSection − ricciNeg2`) as the manifestly
`∇W`-built intrinsic section `g(∇_v W, w) + g(v, ∇_w W)` — the form whose covariant top/rest split is
amenable to the metric-contraction `DiffBilinOp` engine.

Proved by section extensionality through the unit `(0,0)`-tensor evaluation: both fibre values are
`lieDerivMetric g W x` — `lieDerivCcSection`'s by `lieDerivCcSection_toModel_apply`,
`symLoweredDeTurckVF`'s by `symLoweredDeTurckVF_toModel_apply` followed by
`cartanRHSBilin_eq_lieDerivMetric`. -/
theorem lieDerivCcSection_eq_symLoweredCovGrad_deTurckVF (g g_bg : SmoothRiemannianMetric I M) :
    lieDerivCcSection (I := I) g_bg g = symLoweredDeTurckVF (I := I) g g_bg := by
  classical
  refine Integral.L2.SmoothCcTensor.ext ?_
  refine ContMDiffSection.ext (fun x => ?_)
  apply tensor0s_ext_unitZero (I := I) (M := M) (s := 2)
  apply Tensor0SSpace.toModel_injective
  refine ContinuousMultilinearMap.ext (fun v => ?_)
  -- The unit `(0,0)`-tensor `unitZeroSec x` is the canonical `constOfIsEmpty 1`.
  have hunit : (unitZeroSec (I := I) (M := M) x : Tensor0SSpace 0 I x) =
      ContinuousMultilinearMap.constOfIsEmpty ℝ
        (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ) := rfl
  rw [hunit, lieDerivCcSection_toModel_apply, symLoweredDeTurckVF_toModel_apply,
    cartanRHSBilin_eq_lieDerivMetric]
  rfl

/-- **The `g₀`-re-tagged symmetrised covariant lowering of the DeTurck vector field.**  The section
`symLoweredDeTurckVF g₁ g_bg` re-tagged from the `g₁` type tag to the `g₀` type tag (a pure type-level
parameter change; the underlying section is unchanged).  The intrinsic, `∇W`-manifest representative
of the `g₀`-retagged Lie summand `lieDerivRetagG0 g₀ g_bg g₁`. -/
def symLoweredDeTurckVFRetagG0 (g₀ g₁ g_bg : SmoothRiemannianMetric I M) :
    Integral.L2.SmoothCcTensor g₀ 0 2 :=
  { toSection := (symLoweredDeTurckVF (I := I) g₁ g_bg).toSection
    hasCompactSupport := (symLoweredDeTurckVF (I := I) g₁ g_bg).hasCompactSupport }

/-- **(P1a, retagged form.)**  The `g₀`-retagged sealed Lie-derivative summand
`lieDerivRetagG0 g₀ g_bg g₁` equals the `g₀`-retagged symmetrised covariant lowering of the DeTurck
vector field `symLoweredDeTurckVFRetagG0 g₀ g₁ g_bg`.  Both retags carry the identical underlying
section, so this is the section-level Cartan identity
`lieDerivCcSection_eq_symLoweredCovGrad_deTurckVF` transported through the pure type-tag change. -/
theorem lieDerivRetagG0_eq_symLoweredRetagG0 (g₀ g₁ g_bg : SmoothRiemannianMetric I M) :
    lieDerivRetagG0 (I := I) g₀ g_bg g₁ = symLoweredDeTurckVFRetagG0 (I := I) g₀ g₁ g_bg := by
  refine Integral.L2.SmoothCcTensor.ext ?_
  have h : (lieDerivCcSection (I := I) g_bg g₁).toSection =
      (symLoweredDeTurckVF (I := I) g₁ g_bg).toSection :=
    congrArg Integral.L2.SmoothCcTensor.toSection
      (lieDerivCcSection_eq_symLoweredCovGrad_deTurckVF (I := I) g₁ g_bg)
  exact h

end Pullback
end RicciFlow
end PDE
end DifferentialGeometry

end
