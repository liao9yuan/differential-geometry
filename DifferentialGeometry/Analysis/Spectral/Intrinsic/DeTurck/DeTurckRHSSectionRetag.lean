import DifferentialGeometry.Analysis.Parabolic.DeTurckRicci.RHSSmoothQuasilinear
import DifferentialGeometry.Geometry.Flow.RicciFlow.DeTurckRHSSection

/-! # The `g₀`-retagged Ricci–DeTurck right-hand-side section and its `Ric + Lie` summands

For a closed (compact, boundaryless) smooth Riemannian manifold `(M, g₀)` modelled on a real
inner-product space `E`, this file is the low-rank section anchor for the covariant-jet Faà-di-Bruno
analysis of the Ricci–DeTurck right-hand side.  It supplies the genuine section-level objects every
downstream file builds on:

* `deTurckRHSRetagG0 g₀ g_bg g₁` — the chart-frame DeTurck right-hand-side section
  `deTurckRHSSection g_bg g₁`, re-tagged from the `g₁` type tag to the `g₀` type tag (a pure
  type-level parameter change);
* `ricciNeg2CcSection g` / `lieDerivCcSection g_bg g` — the curvature summand `-2 • Ric(g)` and the
  Lie-derivative summand `𝓛_{W(g, g_bg)} g` of `deTurckRHSSection`, as genuine smooth compactly
  supported `(0,2)`-tensor sections, with the additive split
  `deTurckRHSSection_eq_ricciNeg2_add_lieDeriv`;
* `ricciNeg2RetagG0 g₀ g₁` / `lieDerivRetagG0 g₀ g_bg g₁` — the two summands re-tagged to the `g₀`
  type tag, with the retagged additive split `deTurckRHSRetagG0_eq_ricciNeg2_add_lieDeriv`.

These are the objects the segment-metric covariant-jet expansion (`SegmentMetricRHSCovJetExpansion.lean`)
and the order-zero curvature/Lie difference decompositions
(`SegmentMetricCurvatureDifferenceOpDecomposition.lean`,
`SegmentMetricLieDifferenceDecomposition.lean`) consume; collecting them here keeps the anchor's import
surface minimal and breaks what would otherwise be an import cycle between the leaf file and the
order-zero decomposition files. -/

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
namespace IntrinsicSpectral
namespace DeTurck

open DifferentialGeometry
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.PDE
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

/-- **The `g₀`-re-tagged Ricci–DeTurck right-hand-side section.**  The chart-frame DeTurck
right-hand side `deTurckRHSSection g_bg g₁` of the realized metric `g₁`, re-tagged from the `g₁`
type tag to the `g₀` type tag (the metric tag being a pure type-level parameter): the non-linear
`Ric + Lie` summand whose higher-order covariant-jet Nemytskii fibre bound the leaf file states.  This is
definitionally identical to the downstream consumer's `deTurckRHSRetag g₀ g_bg g₁`; the follow-up
assembler bridges the two by `rfl`. -/
def deTurckRHSRetagG0 (g₀ g_bg g₁ : SmoothRiemannianMetric I M) :
    Integral.L2.SmoothCcTensor g₀ 0 2 :=
  { toSection := (deTurckRHSSection (I := I) g_bg g₁).toSection
    hasCompactSupport := (deTurckRHSSection (I := I) g_bg g₁).hasCompactSupport }

omit [CompleteSpace E] [BoundarylessManifold I M] in
/-- The underlying smooth section of `deTurckRHSRetagG0 g₀ g_bg g₁` is the DeTurck right-hand-side
section `deTurckRHSSection g_bg g₁`'s section (the retag is a pure type-tag change). -/
@[simp] theorem deTurckRHSRetagG0_toSection (g₀ g_bg g₁ : SmoothRiemannianMetric I M) :
    (deTurckRHSRetagG0 (I := I) g₀ g_bg g₁).toSection =
      (deTurckRHSSection (I := I) g_bg g₁).toSection := rfl

/-! ### The additive `Ric + Lie` split of the DeTurck right-hand-side section

The genuine first decomposition of the second-order Ricci–DeTurck right-hand side `F(g) =
deTurckRicciRHS g_bg g = -2 • Ric(g) + 𝓛_{W(g, g_bg)} g` into its two *separate* geometric
nonlinearities — the **Ricci-curvature** summand `-2 • Ric(g)` and the **Lie-derivative-of-metric**
summand `𝓛_{W(g, g_bg)} g`.  Both are promoted to genuine smooth compactly-supported `(0,2)`-tensor
sections (`SmoothCcTensor g 0 2`), so the section difference `F(g₁) − F(g₂)` splits additively as
`-2 • (Ric(g₁) − Ric(g₂)) + (Lie(g₁) − Lie(g₂))`.  This is the additive bridge over which the
target's per-order covariant `L²` bound reduces to the two **per-field** covariant-Faà-di-Bruno
`L²` primitives (each a separately-reusable Nemytskii estimate). -/

/-- The model `(0,2)`-multilinear value of the **Ricci-tensor** bilinear form `-2 • Ric(g) x`
(the curvature summand of the Ricci–DeTurck right-hand side), via `bilinFormToModel`. -/
private def ricciNeg2ModelFun (g : SmoothRiemannianMetric I M) (x : M) :
    Tensor0SSpace 2 I x :=
  Tensor0SSpace.ofModel
    (bilinFormToModel (TangentSpace I x)
      ((-2 : ℝ) • ricciTensor (I := I) (smoothRiemannianMetricToInfty (I := I) g) x))

private theorem ricciNeg2ModelFun_toModel_apply (g : SmoothRiemannianMetric I M) (x : M)
    (v : Fin 2 → TangentSpace I x) :
    Tensor0SSpace.toModel (ricciNeg2ModelFun (I := I) g x) v =
      ((-2 : ℝ) • ricciTensor (I := I) (smoothRiemannianMetricToInfty (I := I) g) x)
        (v 0) (v 1) := by
  unfold ricciNeg2ModelFun
  rw [Tensor0SSpace.toModel_ofModel]
  exact bilinFormToModel_apply (TangentSpace I x)
    ((-2 : ℝ) • ricciTensor (I := I) (smoothRiemannianMetricToInfty (I := I) g) x) v

/-- **The `-2 • Ric(g)` curvature summand is a smooth covariant `(0,2)`-tensor field.**  Its chart
component smoothness is the Ricci chart-component smoothness `chartRicci_affine_in_d2g` scaled by
`-2`. -/
def ricciNeg2Field (g : SmoothRiemannianMetric I M) :
    Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) ∞ 2 :=
  letI := tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 2
  letI := TangentBundle.contMDiffVectorBundle (I := I) (M := M) (n := ∞)
  ⟨fun x => ricciNeg2ModelFun (I := I) g x, by
    let d := Module.finrank ℝ E
    let b : Module.Basis (Fin d) ℝ E := chartModelBasis E
    refine (contMDiff_multilinearSection_iff_coord (TangentSpace I) ∞ b _).mpr
      fun σ x₀ => ?_
    have hcomp : ContMDiffOn I 𝓘(ℝ, ℝ) ∞
        (fun x : M =>
          (-2 : ℝ) • ricciTensor (I := I) (smoothRiemannianMetricToInfty (I := I) g) x
            (chartFrameVec (I := I) x₀ (σ 0) x)
            (chartFrameVec (I := I) x₀ (σ 1) x))
        (chartAt H x₀).source :=
      (contMDiffOn_const (c := (-2 : ℝ))).smul
        (chartRicci_affine_in_d2g (I := I)
          (smoothRiemannianMetricToInfty (I := I) g) x₀ (σ 0) (σ 1))
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
    change Tensor0SSpace.toModel (ricciNeg2ModelFun (I := I) g x)
        (fun j => (trivializationAt E (TangentSpace I) x₀).symmL ℝ x (b (σ j))) = _
    rw [ricciNeg2ModelFun_toModel_apply]
    simp only [ContinuousLinearMap.smul_apply, chartFrameVec]
    rfl⟩

/-- The `-2 • Ric(g)` curvature summand as a smooth mixed `(0,2)`-tensor section. -/
def ricciNeg2MixedSection (g : SmoothRiemannianMetric I M) :
    Cₛ^∞⟮I; TensorRSModel 0 2 ℝ E, (fun x : M => TensorRSSpace 0 2 I x)⟯ :=
  MixedSection.fromMultilinearSection (𝕜 := ℝ) (F := E) (IB := I)
    (E := (TangentSpace I : M → Type _)) ∞ (ricciNeg2Field (I := I) g)

/-- **The `-2 • Ric(g)` curvature summand as a `SmoothCcTensor g 0 2`.** -/
def ricciNeg2CcSection (g : SmoothRiemannianMetric I M) :
    SmoothCcTensor g 0 2 where
  toSection := ricciNeg2MixedSection (I := I) g
  hasCompactSupport := HasCompactSupport.of_compactSpace _

/-- **The `𝓛_{W(g, g_bg)} g` Lie-derivative summand as a `SmoothCcTensor g 0 2`.**  Defined as the
algebraic complement `deTurckRHSSection g_bg g − ricciNeg2CcSection g`, so the additive `Ric + Lie`
split `deTurckRHSSection g_bg g = ricciNeg2CcSection g + lieDerivCcSection g_bg g` holds by
construction; its underlying field is `𝓛_{W(g, g_bg)} g` (the deTurck-vector-field Lie deformation),
since `deTurckRHSSection`'s field is `-2 • Ric(g) + 𝓛_{W} g`. -/
def lieDerivCcSection (g_bg g : SmoothRiemannianMetric I M) :
    SmoothCcTensor g 0 2 :=
  deTurckRHSSection (I := I) g_bg g - ricciNeg2CcSection (I := I) g

/-- **The additive `Ric + Lie` split of the DeTurck right-hand-side section.**  The Ricci–DeTurck
right-hand-side section is the sum of its curvature summand `-2 • Ric(g)` and its Lie-derivative
summand `𝓛_{W(g, g_bg)} g` (both genuine `SmoothCcTensor`s). -/
theorem deTurckRHSSection_eq_ricciNeg2_add_lieDeriv (g_bg g : SmoothRiemannianMetric I M) :
    deTurckRHSSection (I := I) g_bg g =
      ricciNeg2CcSection (I := I) g + lieDerivCcSection (I := I) g_bg g := by
  rw [lieDerivCcSection]; abel

/-- **The `g₀`-re-tagged `-2 • Ric(g₁)` curvature summand.**  The curvature summand
`ricciNeg2CcSection g₁` re-tagged from the `g₁` type tag to the `g₀` type tag (a pure type-level
parameter change; the underlying section is unchanged). -/
def ricciNeg2RetagG0 (g₀ g₁ : SmoothRiemannianMetric I M) :
    Integral.L2.SmoothCcTensor g₀ 0 2 :=
  { toSection := (ricciNeg2CcSection (I := I) g₁).toSection
    hasCompactSupport := (ricciNeg2CcSection (I := I) g₁).hasCompactSupport }

/-- **The `g₀`-re-tagged `𝓛_{W(g₁, g_bg)} g₁` Lie-derivative summand.**  The Lie-derivative summand
`lieDerivCcSection g_bg g₁` re-tagged from the `g₁` type tag to the `g₀` type tag. -/
def lieDerivRetagG0 (g₀ g_bg g₁ : SmoothRiemannianMetric I M) :
    Integral.L2.SmoothCcTensor g₀ 0 2 :=
  { toSection := (lieDerivCcSection (I := I) g_bg g₁).toSection
    hasCompactSupport := (lieDerivCcSection (I := I) g_bg g₁).hasCompactSupport }

/-- **The retagged additive `Ric + Lie` split.**  The `g₀`-retagged DeTurck right-hand-side section
splits additively into its `g₀`-retagged curvature and Lie-derivative summands. -/
theorem deTurckRHSRetagG0_eq_ricciNeg2_add_lieDeriv
    (g₀ g_bg g₁ : SmoothRiemannianMetric I M) :
    deTurckRHSRetagG0 (I := I) g₀ g_bg g₁ =
      ricciNeg2RetagG0 (I := I) g₀ g₁ + lieDerivRetagG0 (I := I) g₀ g_bg g₁ := by
  refine Integral.L2.SmoothCcTensor.ext ?_
  have h := congrArg Integral.L2.SmoothCcTensor.toSection
    (deTurckRHSSection_eq_ricciNeg2_add_lieDeriv (I := I) g_bg g₁)
  rw [Integral.L2.SmoothCcTensor.toSection_add] at h
  exact h

end DeTurck
end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end
