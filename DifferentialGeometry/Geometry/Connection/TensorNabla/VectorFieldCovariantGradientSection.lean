import DifferentialGeometry.Geometry.Flow.RicciFlow.Pullback.Cartan.LieDerivSectionCartan
import DifferentialGeometry.Geometry.Connection.ConnectionDifferenceFieldJets

/-! # The lowered covariant gradient of the DeTurck vector field as a `(0,2)`-section

For a closed (compact, boundaryless) smooth Riemannian manifold `(M, g)` modelled on a real
inner-product space `E`, this file builds the **intrinsic lowered covariant gradient** of the DeTurck
vector field `W = deTurckVF g g_bg` as a genuine covariant `(0, 2)`-tensor section in the
`Integral.L2.SmoothCcTensor` framework — the building block the gauge half of the Ricci–DeTurck
linearization differentiates, and the layer that makes the Cartan-difference telescope *expressible*.

## What this file supplies

The carrier of the Lie deformation summand is the **symmetrised** lowering
`symLoweredDeTurckVF g g_bg`, whose unit fibre is the Cartan bilinear form
`cartanRHSBilin g W x = g(∇^g_v W, w) + g(v, ∇^g_w W)` (`LieDerivSectionCartan.lean`).  This file
factors out its un-symmetrised half:

* `loweredCovGradDeTurckVFBilin g g_bg x` — the continuous bilinear form
  `(v, w) ↦ g(∇^g_v W, w)`, i.e. the `g`-lowering of the **first** slot of the Levi-Civita covariant
  gradient `∇^g W` (`W = deTurckVF g g_bg`).
* `loweredCovGradDeTurckVF g g_bg : SmoothCcTensor g 0 2` — its packaging as a smooth covariant
  `(0, 2)`-tensor section (fibre `loweredCovGradDeTurckVF_toModel_apply : ![v, w] ↦ g(∇^g_v W, w)`),
  built by the same multilinear-bundle coordinate route as `symLoweredDeTurckVFField` /
  `loweredConnDiffField`; its smoothness is the `g`-inner pairing of the smooth covariant-gradient
  field `x ↦ ∇^g_{X x} W` (`LeviCivita_section_contMDiffOn_univ` applied to the smooth field `W`,
  then `clm_bundle_apply`) with a smooth direction frame.
* `loweredCovGradDeTurckVFRetagG0 g₀ g₁ g_bg : SmoothCcTensor g₀ 0 2` — its `g₀`-retag (the carrier
  type tag the outer `g₀`-Levi-Civita covariant gradient acts on, matching
  `symLoweredDeTurckVFRetagG0`).

## The keystone re-expression

`symLoweredDeTurckVFRetagG0_eq_loweredCovGrad_add_swap` rebuilds the symmetrised retagged carrier from
the un-symmetrised lowered covariant gradient and its slot swap:
$$
  \mathrm{symLoweredDeTurckVFRetagG0}\,g_0\,g_1\,g_{bg}
    = \mathrm{loweredCovGradDeTurckVFRetagG0}\,g_0\,g_1\,g_{bg}
      + \mathrm{permuteCcTensor}\,g_0\,(0\;1)\,
          (\mathrm{loweredCovGradDeTurckVFRetagG0}\,g_0\,g_1\,g_{bg}),
$$
proved through the unit-`(0, 0)`-evaluation fibre identity: the left fibre is the Cartan form
`g₁(∇_v W, w) + g₁(v, ∇_w W)`, the right fibre is `g₁(∇_v W, w) + g₁(∇_w W, v)`, and the two agree by
the `g₁`-symmetry `g₁(∇_w W, v) = g₁(v, ∇_w W)`.  This is the section-level "symmetrisation = sum with
the slot swap" identity that lets the telescope worker push the difference through the realized
connection-difference algebra.

## The DeTurck-field difference algebra

`deTurckVF g₁ g_bg − deTurckVF g₂ g_bg` is re-expressed through the on-disk connection-difference
cocycle: `deTurckVF_sub_apply_eq_trace_connDiff` writes the difference of the two DeTurck fields as the
`g`-inverse-Gram-weighted trace of the **pair** connection difference `connDiff g₁ g₂`
(`connDiff_cocycle`), the concrete section the realized Koszul jet algebra
(`loweredConnDiffSection_sub_eq_koszulRealizeDiff_sub_crossCorrDiff`) consumes.

## Linearity / non-vacuity

`loweredCovGradDeTurckVFBilin` is genuinely the `∇^g W` reader: at `g_bg = g` the DeTurck field is the
zero section (`deTurckVF_self`), so `∇^g W = 0` and the lowered form vanishes
(`loweredCovGradDeTurckVF_self_toModel`), rejecting the degenerate constant-section reading. -/

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

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

/-! ### The lowered covariant-gradient bilinear form -/

/-- **The `g`-lowered covariant gradient of the DeTurck vector field, as a continuous bilinear
form.**  For a smooth metric `g` and background `g_bg`, with `W = deTurckVF g g_bg`, the `g`-lowering
of the **first** (differentiated) slot of the Levi-Civita covariant gradient `∇^g W`:
`(v, w) ↦ g(∇^g_v W, w)`, where `∇^g = LeviCivita g`.

This is the un-symmetrised half of the Cartan right-hand side `cartanRHSBilin g W x = g(∇_v W, w)
+ g(v, ∇_w W)` (`cartanRHSBilin`): `loweredCovGradDeTurckVFBilin` is its first summand. -/
def loweredCovGradDeTurckVFBilin (g g_bg : SmoothRiemannianMetric I M) (x : M) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  (g.inner x).comp ((LeviCivita (I := I) g)
    (deTurckVF (I := I) g g_bg : ∀ x : M, TangentSpace I x) x)

/-- **The lowered covariant gradient bilinear form evaluated.**
`loweredCovGradDeTurckVFBilin g g_bg x v w = g(∇^g_v W, w)`, `W = deTurckVF g g_bg`. -/
theorem loweredCovGradDeTurckVFBilin_apply (g g_bg : SmoothRiemannianMetric I M) (x : M)
    (v w : TangentSpace I x) :
    loweredCovGradDeTurckVFBilin (I := I) g g_bg x v w =
      g.inner x ((LeviCivita (I := I) g)
        (deTurckVF (I := I) g g_bg : ∀ x : M, TangentSpace I x) x v) w := by
  rfl

/-- **The lowered covariant gradient is the first summand of the Cartan right-hand side.**
`cartanRHSBilin g W x v w = loweredCovGradDeTurckVFBilin g g_bg x v w
+ loweredCovGradDeTurckVFBilin g g_bg x w v`, `W = deTurckVF g g_bg`.  The second summand is the
slot-swap of the lowered form, equal to the Cartan form's `g(v, ∇_w W)` by `g`-symmetry. -/
theorem cartanRHSBilin_eq_loweredCovGrad_add_swap (g g_bg : SmoothRiemannianMetric I M) (x : M)
    (v w : TangentSpace I x) :
    cartanRHSBilin (I := I) g (deTurckVF (I := I) g g_bg) x v w =
      loweredCovGradDeTurckVFBilin (I := I) g g_bg x v w
      + loweredCovGradDeTurckVFBilin (I := I) g g_bg x w v := by
  rw [cartanRHSBilin_apply, loweredCovGradDeTurckVFBilin_apply, loweredCovGradDeTurckVFBilin_apply]
  rw [g.symm x ((LeviCivita (I := I) g)
    (deTurckVF (I := I) g g_bg : ∀ x : M, TangentSpace I x) x w) v]

/-! ### The lowered covariant gradient as a smooth `(0,2)`-tensor section -/

/-- **Smoothness of the lowered covariant-gradient bilinear form on smooth fields.**  For smooth
tangent vector fields `X`, `Y`, the scalar field
`x ↦ loweredCovGradDeTurckVFBilin g g_bg x (X x) (Y x) = g(∇^g_{X x} W, Y x)` is smooth.  The inner
covariant-gradient field `x ↦ (LeviCivita g) W x (X x)` is smooth by
`LeviCivita_section_contMDiffOn_univ` (applied to the smooth DeTurck field `W`) post-applied to the
smooth direction `X` (`clm_bundle_apply`), and the `g`-inner pairing of two smooth tangent fields is
smooth by `contMDiff_g_inner_of_smooth_sections`. -/
theorem loweredCovGradDeTurckVFBilin_pairing_contMDiff (g g_bg : SmoothRiemannianMetric I M)
    {X Y : Π b : M, TangentSpace I b}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Y)) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun b : M => loweredCovGradDeTurckVFBilin (I := I) g g_bg b (X b) (Y b)) := by
  classical
  set W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ := deTurckVF (I := I) g g_bg with hW
  -- The covariant gradient `x ↦ (LeviCivita g) W x` is a smooth Hom-bundle section.
  have hWsmooth : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ((∞ : WithTop ℕ∞) + 1)
      (fun x : M => (⟨x, (W : ∀ x : M, TangentSpace I x) x⟩ : TotalSpace E (TangentSpace I)))
      Set.univ := by
    have h_le : ((∞ : WithTop ℕ∞) + 1) ≤ ∞ := by rw [ENat.coe_top_add_one]
    exact (W.contMDiff.of_le h_le).contMDiffOn
  have hcov : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun x : M =>
        (⟨x, (LeviCivita (I := I) g) (W : ∀ x : M, TangentSpace I x) x⟩ :
          TotalSpace (E →L[ℝ] E) (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x))) := by
    rw [← contMDiffOn_univ]
    exact LeviCivita_section_contMDiffOn_univ (I := I) g hWsmooth
  -- Apply the Hom-section to the smooth direction `X`: a smooth tangent vector field.
  have hD : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M =>
        (TotalSpace.mk' E (E := fun y : M => TangentSpace I y) b
          ((LeviCivita (I := I) g) (W : ∀ x : M, TangentSpace I x) b (X b)))) :=
    ContMDiff.clm_bundle_apply (b := id) hcov hX
  let D : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    ContMDiffSection.mk (fun b : M => (LeviCivita (I := I) g)
      (W : ∀ x : M, TangentSpace I x) b (X b)) hD
  let Ys : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    ContMDiffSection.mk Y hY
  have hpair : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun b : M => g.inner b (D b) (Ys b)) :=
    Integral.DivergenceTheorem.contMDiff_g_inner_of_smooth_sections (I := I) g D Ys
  refine hpair.congr (fun b => ?_)
  rfl

/-- The pointwise model `(0,2)`-tensor value of the lowered covariant gradient. -/
def loweredCovGradModelFun (g g_bg : SmoothRiemannianMetric I M) (x : M) : Tensor0SSpace 2 I x :=
  Tensor0SSpace.ofModel
    (bilinFormToModel (TangentSpace I x) (loweredCovGradDeTurckVFBilin (I := I) g g_bg x))

theorem loweredCovGradModelFun_toModel_apply (g g_bg : SmoothRiemannianMetric I M) (x : M)
    (v : Fin 2 → TangentSpace I x) :
    Tensor0SSpace.toModel (loweredCovGradModelFun (I := I) g g_bg x) v =
      loweredCovGradDeTurckVFBilin (I := I) g g_bg x (v 0) (v 1) := by
  unfold loweredCovGradModelFun
  rw [Tensor0SSpace.toModel_ofModel]
  exact bilinFormToModel_apply (TangentSpace I x) (loweredCovGradDeTurckVFBilin (I := I) g g_bg x) v

/-- **The lowered covariant gradient of the DeTurck vector field as a smooth covariant
`(0,2)`-tensor field.**  Its chart-component smoothness is the bilinear-form pairing smoothness
`loweredCovGradDeTurckVFBilin_pairing_contMDiff` on the chart-`x₀`-pushforward frame `chartFrameVec`
(the same `contMDiff_multilinearSection_iff_coord` route as `symLoweredDeTurckVFField` /
`loweredConnDiffField`). -/
def loweredCovGradDeTurckVFField (g g_bg : SmoothRiemannianMetric I M) :
    Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) ∞ 2 :=
  letI := tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 2
  letI := TangentBundle.contMDiffVectorBundle (I := I) (M := M) (n := ∞)
  ⟨fun x => loweredCovGradModelFun (I := I) g g_bg x, by
    let d := Module.finrank ℝ E
    let b : Module.Basis (Fin d) ℝ E := chartModelBasis E
    refine (contMDiff_multilinearSection_iff_coord (TangentSpace I) ∞ b _).mpr
      fun σ x₀ => ?_
    have hcomp : ContMDiffOn I 𝓘(ℝ, ℝ) ∞
        (fun x : M =>
          loweredCovGradDeTurckVFBilin (I := I) g g_bg x
            (chartFrameVec (I := I) x₀ (σ 0) x)
            (chartFrameVec (I := I) x₀ (σ 1) x))
        (chartAt H x₀).source := by
      intro x hx
      have hframe_on : ∀ k : Fin (Module.finrank ℝ E),
          ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
            (fun bb : M => TotalSpace.mk' E bb (chartFrameVec (I := I) x₀ k bb))
            (chartAt H x₀).source := fun k => chartAlphaFrame_section_contMDiffOn (I := I) x₀ k
      obtain ⟨S, hS_eq⟩ :=
        exists_contMDiffSection_eqOn_nhd
          (s := fun k : Fin (Module.finrank ℝ E) => fun bb : M => chartFrameVec (I := I) x₀ k bb)
          (u := (chartAt H x₀).source) (p := x)
          hframe_on ((chartAt H x₀).open_source) hx
      have hSk : ∀ k, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
          (T% (fun bb : M => (S k) bb : Π bb : M, TangentSpace I bb)) := fun k => (S k).contMDiff
      have hpair : ContMDiff I 𝓘(ℝ, ℝ) ∞
          (fun bb : M => loweredCovGradDeTurckVFBilin (I := I) g g_bg bb
            ((S (σ 0)) bb) ((S (σ 1)) bb)) :=
        loweredCovGradDeTurckVFBilin_pairing_contMDiff (I := I) g g_bg (hSk (σ 0)) (hSk (σ 1))
      have hchart_at : ContMDiffAt I 𝓘(ℝ, ℝ) ∞
          (fun x : M => loweredCovGradDeTurckVFBilin (I := I) g g_bg x
            (chartFrameVec (I := I) x₀ (σ 0) x)
            (chartFrameVec (I := I) x₀ (σ 1) x)) x := by
        refine (hpair x).congr_of_eventuallyEq ?_
        filter_upwards [hS_eq] with bb hb
        rw [hb (σ 0), hb (σ 1)]
      exact hchart_at.contMDiffWithinAt
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
    change Tensor0SSpace.toModel (loweredCovGradModelFun (I := I) g g_bg x)
        (fun j => (trivializationAt E (TangentSpace I) x₀).symmL ℝ x (b (σ j))) = _
    rw [loweredCovGradModelFun_toModel_apply]
    rfl⟩

/-- The lowered covariant gradient as a smooth mixed `(0,2)`-tensor section. -/
def loweredCovGradDeTurckVFMixedSection (g g_bg : SmoothRiemannianMetric I M) :
    Cₛ^∞⟮I; TensorRSModel 0 2 ℝ E, (fun x : M => TensorRSSpace 0 2 I x)⟯ :=
  MixedSection.fromMultilinearSection (𝕜 := ℝ) (F := E) (IB := I)
    (E := (TangentSpace I : M → Type _)) ∞ (loweredCovGradDeTurckVFField (I := I) g g_bg)

/-- **The `g`-lowered covariant gradient of the DeTurck vector field as a `SmoothCcTensor g 0 2`.**
The concrete intrinsic un-symmetrised representative: its fibre value is `g(∇^g_v W, w)`,
`W = deTurckVF g g_bg`, `∇^g = LeviCivita g`.  Compact support is automatic on the compact manifold
`M`. -/
def loweredCovGradDeTurckVF (g g_bg : SmoothRiemannianMetric I M) :
    Integral.L2.SmoothCcTensor g 0 2 where
  toSection := loweredCovGradDeTurckVFMixedSection (I := I) g g_bg
  hasCompactSupport := HasCompactSupport.of_compactSpace _

/-- **The fibre value of the lowered covariant gradient section.**  Evaluating at the canonical unit
`(0,0)`-tensor and a tangent pair recovers `g(∇^g_v W, w)`. -/
theorem loweredCovGradDeTurckVF_toModel_apply (g g_bg : SmoothRiemannianMetric I M) (x : M)
    (v : Fin 2 → TangentSpace I x) :
    Tensor0SSpace.toModel
        ((loweredCovGradDeTurckVF (I := I) g g_bg).toSection x
          (ContinuousMultilinearMap.constOfIsEmpty ℝ
            (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))) v =
      loweredCovGradDeTurckVFBilin (I := I) g g_bg x (v 0) (v 1) := by
  classical
  change Tensor0SSpace.toModel
      ((MixedSection.eval₀ (F := E) (E := (TangentSpace I : M → Type _)) x).smulRight
          (loweredCovGradDeTurckVFField (I := I) g g_bg x)
        (ContinuousMultilinearMap.constOfIsEmpty ℝ
          (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))) v = _
  rw [ContinuousLinearMap.smulRight_apply, MixedSection.eval₀_apply,
    ContinuousMultilinearMap.constOfIsEmpty_apply, one_smul]
  change Tensor0SSpace.toModel (loweredCovGradModelFun (I := I) g g_bg x) v = _
  rw [loweredCovGradModelFun_toModel_apply]

set_option linter.unusedSectionVars false in
/-- **Self-vanishing of the lowered covariant gradient** (non-vacuity litmus).  When `g_bg = g`, the
DeTurck vector field is the zero section (`deTurckVF_self`), so its covariant gradient vanishes, and
the lowered form is `0` on every tangent pair — rejecting the degenerate constant-section reading. -/
theorem loweredCovGradDeTurckVF_self_toModel (g : SmoothRiemannianMetric I M) (x : M)
    (v : Fin 2 → TangentSpace I x) :
    Tensor0SSpace.toModel
        ((loweredCovGradDeTurckVF (I := I) g g).toSection x
          (ContinuousMultilinearMap.constOfIsEmpty ℝ
            (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))) v = 0 := by
  rw [loweredCovGradDeTurckVF_toModel_apply, loweredCovGradDeTurckVFBilin_apply]
  -- The DeTurck field of `g` against itself is the zero section (`deTurckVF_self`), so its
  -- coercion is the zero function `(0 : Π x, TangentSpace I x)`.
  have h0 : (deTurckVF (I := I) g g : ∀ x : M, TangentSpace I x) =
      (0 : ∀ x : M, TangentSpace I x) := by
    rw [deTurckVF_self (I := I) g]
    rfl
  rw [h0]
  -- The covariant derivative of the zero section vanishes (`CovariantDerivative.zero`).
  have hz : (LeviCivita (I := I) g) (0 : ∀ x : M, TangentSpace I x) = 0 :=
    CovariantDerivative.zero (LeviCivita (I := I) g)
  rw [hz]
  simp only [Pi.zero_apply, ContinuousLinearMap.zero_apply, map_zero,
    ContinuousLinearMap.zero_apply]

/-! ### The `g₀`-retag and its unit fibre -/

/-- **The `g₀`-retagged lowered covariant gradient of the DeTurck vector field.**  The section
`loweredCovGradDeTurckVF g₁ g_bg` re-tagged from the `g₁` type tag to the `g₀` type tag (a pure
type-level parameter change; the underlying section is unchanged).  The carrier the outer
`g₀`-Levi-Civita covariant gradient acts on, matching `symLoweredDeTurckVFRetagG0`. -/
def loweredCovGradDeTurckVFRetagG0 (g₀ g₁ g_bg : SmoothRiemannianMetric I M) :
    Integral.L2.SmoothCcTensor g₀ 0 2 :=
  { toSection := (loweredCovGradDeTurckVF (I := I) g₁ g_bg).toSection
    hasCompactSupport := (loweredCovGradDeTurckVF (I := I) g₁ g_bg).hasCompactSupport }

set_option linter.unusedSectionVars false in
/-- **The unit fibre of the `g₀`-retagged lowered covariant gradient.**  The retag carries the
identical underlying section, so its unit-evaluated `(0,2)`-value on `![v, w]` is the lowered form
`loweredCovGradDeTurckVFBilin g₁ g_bg x v w = g₁(∇^{g₁}_v W, w)`. -/
theorem loweredCovGradDeTurckVFRetagG0_unitModel_eq (g₀ g₁ g_bg : SmoothRiemannianMetric I M)
    (x : M) (v w : TangentSpace I x) :
    Tensor0SSpace.toModel
        ((loweredCovGradDeTurckVFRetagG0 (I := I) g₀ g₁ g_bg).toSection x
          (ContinuousMultilinearMap.constOfIsEmpty ℝ
            (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))) ![v, w] =
      loweredCovGradDeTurckVFBilin (I := I) g₁ g_bg x v w := by
  classical
  have hsec : (loweredCovGradDeTurckVFRetagG0 (I := I) g₀ g₁ g_bg).toSection =
      (loweredCovGradDeTurckVF (I := I) g₁ g_bg).toSection := rfl
  rw [show ((loweredCovGradDeTurckVFRetagG0 (I := I) g₀ g₁ g_bg).toSection x
        (ContinuousMultilinearMap.constOfIsEmpty ℝ
          (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))) =
      ((loweredCovGradDeTurckVF (I := I) g₁ g_bg).toSection x
        (ContinuousMultilinearMap.constOfIsEmpty ℝ
          (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))) from by rw [hsec]]
  rw [loweredCovGradDeTurckVF_toModel_apply]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]

/-! ### The keystone: the symmetrised carrier is the lowered gradient plus its slot swap -/

set_option linter.unusedSectionVars false in
/-- **(Keystone.)**  The `g₀`-retagged symmetrised covariant lowering of the DeTurck vector field is
the `g₀`-retagged un-symmetrised lowered covariant gradient plus its slot swap:
$$
  \mathrm{symLoweredDeTurckVFRetagG0}\,g_0\,g_1\,g_{bg}
    = \mathrm{loweredCovGradDeTurckVFRetagG0}\,g_0\,g_1\,g_{bg}
      + \mathrm{permuteCcTensor}\,g_0\,(0\;1)\,(\mathrm{loweredCovGradDeTurckVFRetagG0}\,g_0\,g_1\,g_{bg}).
$$

This is the section-level **"symmetrisation = sum with the slot swap"** identity.  Proved by unit
`(0, 0)`-evaluation fibre extensionality: the left fibre on `![v, w]` is the Cartan bilinear form
`g₁(∇_v W, w) + g₁(v, ∇_w W)` (`symLoweredDeTurckVFRetagG0_unitModel_eq`); the right fibre is
`loweredCovGradDeTurckVFBilin g₁ g_bg x v w + loweredCovGradDeTurckVFBilin g₁ g_bg x w v
= g₁(∇_v W, w) + g₁(∇_w W, v)` (the `add` splits through `toSection_add` and `toModel_add`, the swap
through `permuteCcTensor_unitModel`/`domDomCongr`), and the two agree by
`cartanRHSBilin_eq_loweredCovGrad_add_swap`.

This is the brick the Cartan-difference telescope rides: it re-expresses the symmetrised carrier
through the un-symmetrised lowered gradient, whose difference factors through the realized
connection-difference algebra. -/
theorem symLoweredDeTurckVFRetagG0_eq_loweredCovGrad_add_swap
    (g₀ g₁ g_bg : SmoothRiemannianMetric I M) :
    symLoweredDeTurckVFRetagG0 (I := I) g₀ g₁ g_bg =
      loweredCovGradDeTurckVFRetagG0 (I := I) g₀ g₁ g_bg
      + permuteCcTensor (I := I) g₀ (Equiv.swap 0 1)
          (loweredCovGradDeTurckVFRetagG0 (I := I) g₀ g₁ g_bg) := by
  classical
  refine Integral.L2.SmoothCcTensor.ext ?_
  refine ContMDiffSection.ext (fun x => ?_)
  apply tensor0s_ext_unitZero (I := I) (M := M) (s := 2)
  apply Tensor0SSpace.toModel_injective
  refine ContinuousMultilinearMap.ext (fun v => ?_)
  have hunit : (unitZeroSec (I := I) (M := M) x : Tensor0SSpace 0 I x) =
      ContinuousMultilinearMap.constOfIsEmpty ℝ
        (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ) := rfl
  rw [hunit]
  -- Left fibre: the Cartan bilinear form on `v` (the retag carries the same underlying section as
  -- `symLoweredDeTurckVF g₁ g_bg`, whose unit fibre is the Cartan form
  -- by `symLoweredDeTurckVF_toModel_apply`).
  have hLeft : Tensor0SSpace.toModel
      ((symLoweredDeTurckVFRetagG0 (I := I) g₀ g₁ g_bg).toSection x
        (ContinuousMultilinearMap.constOfIsEmpty ℝ
          (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))) v =
      cartanRHSBilin (I := I) g₁ (deTurckVF (I := I) g₁ g_bg) x (v 0) (v 1) := by
    have hsec : (symLoweredDeTurckVFRetagG0 (I := I) g₀ g₁ g_bg).toSection =
        (symLoweredDeTurckVF (I := I) g₁ g_bg).toSection := rfl
    rw [show ((symLoweredDeTurckVFRetagG0 (I := I) g₀ g₁ g_bg).toSection x
          (ContinuousMultilinearMap.constOfIsEmpty ℝ
            (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))) =
        ((symLoweredDeTurckVF (I := I) g₁ g_bg).toSection x
          (ContinuousMultilinearMap.constOfIsEmpty ℝ
            (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))) from by rw [hsec]]
    rw [symLoweredDeTurckVF_toModel_apply]
  -- Right fibre: split the `add`, then split the swap.
  have hsplit : ((loweredCovGradDeTurckVFRetagG0 (I := I) g₀ g₁ g_bg
        + permuteCcTensor (I := I) g₀ (Equiv.swap 0 1)
            (loweredCovGradDeTurckVFRetagG0 (I := I) g₀ g₁ g_bg)).toSection x
        (ContinuousMultilinearMap.constOfIsEmpty ℝ
          (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))) =
      ((loweredCovGradDeTurckVFRetagG0 (I := I) g₀ g₁ g_bg).toSection x
        (ContinuousMultilinearMap.constOfIsEmpty ℝ
          (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ)))
      + ((permuteCcTensor (I := I) g₀ (Equiv.swap 0 1)
          (loweredCovGradDeTurckVFRetagG0 (I := I) g₀ g₁ g_bg)).toSection x
        (ContinuousMultilinearMap.constOfIsEmpty ℝ
          (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))) := by
    rw [Integral.L2.SmoothCcTensor.toSection_add]
    rfl
  rw [hLeft, hsplit]
  simp only [Tensor0SSpace.toModel_add, ContinuousMultilinearMap.add_apply]
  -- The un-swapped summand.
  rw [show Tensor0SSpace.toModel
      ((loweredCovGradDeTurckVFRetagG0 (I := I) g₀ g₁ g_bg).toSection x
        (ContinuousMultilinearMap.constOfIsEmpty ℝ
          (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))) v =
      loweredCovGradDeTurckVFBilin (I := I) g₁ g_bg x (v 0) (v 1) from by
    have h := loweredCovGradDeTurckVFRetagG0_unitModel_eq (I := I) g₀ g₁ g_bg x (v 0) (v 1)
    rw [show (![v 0, v 1] : Fin 2 → TangentSpace I x) = v from by
      funext i; fin_cases i <;> rfl] at h
    exact h]
  -- The swapped summand: `permuteCcTensor_unitModel` reindexes by `domDomCongr (swap 0 1)`.
  have hswap : Tensor0SSpace.toModel
      ((permuteCcTensor (I := I) g₀ (Equiv.swap 0 1)
          (loweredCovGradDeTurckVFRetagG0 (I := I) g₀ g₁ g_bg)).toSection x
        (ContinuousMultilinearMap.constOfIsEmpty ℝ
          (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))) v =
      loweredCovGradDeTurckVFBilin (I := I) g₁ g_bg x (v 1) (v 0) := by
    have hperm := permuteCcTensor_unitModel (I := I) g₀ (Equiv.swap (0 : Fin 2) 1)
      (loweredCovGradDeTurckVFRetagG0 (I := I) g₀ g₁ g_bg) x
    have hbase : Analysis.Parabolic.TensorSpectral.unitModel (I := I) g₀ 2
        (loweredCovGradDeTurckVFRetagG0 (I := I) g₀ g₁ g_bg) x =
        Tensor0SSpace.toModel
          ((loweredCovGradDeTurckVFRetagG0 (I := I) g₀ g₁ g_bg).toSection x
            (ContinuousMultilinearMap.constOfIsEmpty ℝ
              (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))) := rfl
    have hpermModel : Analysis.Parabolic.TensorSpectral.unitModel (I := I) g₀ 2
        (permuteCcTensor (I := I) g₀ (Equiv.swap (0 : Fin 2) 1)
          (loweredCovGradDeTurckVFRetagG0 (I := I) g₀ g₁ g_bg)) x =
        Tensor0SSpace.toModel
          ((permuteCcTensor (I := I) g₀ (Equiv.swap (0 : Fin 2) 1)
            (loweredCovGradDeTurckVFRetagG0 (I := I) g₀ g₁ g_bg)).toSection x
            (ContinuousMultilinearMap.constOfIsEmpty ℝ
              (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))) := rfl
    rw [hbase, hpermModel] at hperm
    rw [hperm, ContinuousMultilinearMap.domDomCongr_apply]
    rw [show Tensor0SSpace.toModel
        ((loweredCovGradDeTurckVFRetagG0 (I := I) g₀ g₁ g_bg).toSection x
          (ContinuousMultilinearMap.constOfIsEmpty ℝ
            (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ)))
          (fun i => v (Equiv.swap (0 : Fin 2) 1 i)) =
        loweredCovGradDeTurckVFBilin (I := I) g₁ g_bg x
          (v (Equiv.swap (0 : Fin 2) 1 0)) (v (Equiv.swap (0 : Fin 2) 1 1)) from by
      have h := loweredCovGradDeTurckVFRetagG0_unitModel_eq (I := I) g₀ g₁ g_bg x
        (v (Equiv.swap (0 : Fin 2) 1 0)) (v (Equiv.swap (0 : Fin 2) 1 1))
      rw [show (![v (Equiv.swap (0 : Fin 2) 1 0), v (Equiv.swap (0 : Fin 2) 1 1)] :
            Fin 2 → TangentSpace I x) = (fun i => v (Equiv.swap (0 : Fin 2) 1 i)) from by
        funext i; fin_cases i <;> rfl] at h
      exact h]
    rw [show Equiv.swap (0 : Fin 2) 1 0 = 1 from Equiv.swap_apply_left 0 1,
      show Equiv.swap (0 : Fin 2) 1 1 = 0 from Equiv.swap_apply_right 0 1]
  rw [hswap, cartanRHSBilin_eq_loweredCovGrad_add_swap]

/-! ### The DeTurck-field difference algebra -/

/-- **The difference of two DeTurck vector fields, as the `g₁`-inverse-Gram trace of the pair
connection difference.**  By the trace formula `deTurckVF_apply_eq` (the field is the
`chartInvGramMatrix g`-weighted trace of `connDiff g g_bg`) and the connection-difference cocycle
`connDiff_cocycle` (`connDiff g₁ g₂ = connDiff g₁ g_bg − connDiff g₂ g_bg`), the difference of the two
DeTurck fields at `x` is
`(deTurckVF g₁ g_bg − deTurckVF g₂ g_bg) x = ∑ j k, [G₁⁻¹]_{jk} • (connDiff g₁ g₂ x eⱼ) eₖ
+ ∑ j k, ([G₁⁻¹]_{jk} − [G₂⁻¹]_{jk}) • (connDiff g₂ g_bg x eⱼ) eₖ`, splitting the difference into a
**pair-connection-difference** trace (`connDiff g₁ g₂`, the realized-Koszul section) plus an
**inverse-Gram-difference** trace of the endpoint connection difference `connDiff g₂ g_bg`.  Here
`eⱼ = chartBasisVecFiber x j x` and `Gᵢ⁻¹ = chartInvGramMatrix gᵢ x x`. -/
theorem deTurckVF_sub_apply_eq_trace_connDiff (g₁ g₂ g_bg : SmoothRiemannianMetric I M) (x : M) :
    (deTurckVF (I := I) g₁ g_bg) x - (deTurckVF (I := I) g₂ g_bg) x =
      (∑ j, ∑ k, Integral.DivergenceTheorem.chartInvGramMatrix g₁ x x j k •
          ((connDiff (I := I) g₁ g₂ x) (chartBasisVecFiber x j x)) (chartBasisVecFiber x k x))
      + ∑ j, ∑ k,
          (Integral.DivergenceTheorem.chartInvGramMatrix g₁ x x j k
            - Integral.DivergenceTheorem.chartInvGramMatrix g₂ x x j k) •
          ((connDiff (I := I) g₂ g_bg x) (chartBasisVecFiber x j x)) (chartBasisVecFiber x k x) := by
  classical
  rw [deTurckVF_apply_eq (I := I) g₁ g_bg x, deTurckVF_apply_eq (I := I) g₂ g_bg x]
  -- Merge the LHS difference and the RHS sum/sum into single double sums over the same index
  -- set, then compare the summands per `(j, k)`.
  rw [← Finset.sum_sub_distrib (s := Finset.univ)
    (f := fun j => ∑ k, Integral.DivergenceTheorem.chartInvGramMatrix g₁ x x j k •
      ((connDiff (I := I) g₁ g_bg x) (chartBasisVecFiber x j x)) (chartBasisVecFiber x k x))
    (g := fun j => ∑ k, Integral.DivergenceTheorem.chartInvGramMatrix g₂ x x j k •
      ((connDiff (I := I) g₂ g_bg x) (chartBasisVecFiber x j x)) (chartBasisVecFiber x k x))]
  rw [← Finset.sum_add_distrib (s := Finset.univ)
    (f := fun j => ∑ k, Integral.DivergenceTheorem.chartInvGramMatrix g₁ x x j k •
      ((connDiff (I := I) g₁ g₂ x) (chartBasisVecFiber x j x)) (chartBasisVecFiber x k x))
    (g := fun j => ∑ k,
      (Integral.DivergenceTheorem.chartInvGramMatrix g₁ x x j k
        - Integral.DivergenceTheorem.chartInvGramMatrix g₂ x x j k) •
      ((connDiff (I := I) g₂ g_bg x) (chartBasisVecFiber x j x)) (chartBasisVecFiber x k x))]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  -- Per-`(j,k)`: split the connection difference via the cocycle and re-collect the inverse-Gram
  -- difference.
  set G₁ := Integral.DivergenceTheorem.chartInvGramMatrix g₁ x x j k with hG₁
  set G₂ := Integral.DivergenceTheorem.chartInvGramMatrix g₂ x x j k with hG₂
  set ej := chartBasisVecFiber (I := I) x j x with hej
  set ek := chartBasisVecFiber (I := I) x k x with hek
  set D₁ := ((connDiff (I := I) g₁ g_bg x) ej) ek with hD₁
  set D₂ := ((connDiff (I := I) g₂ g_bg x) ej) ek with hD₂
  set Dpair := ((connDiff (I := I) g₁ g₂ x) ej) ek with hDpair
  have hcoc : Dpair = D₁ - D₂ := by
    rw [hDpair, hD₁, hD₂]
    exact IntrinsicSpectral.MetricRealization.connDiff_cocycle (I := I) g₁ g₂ g_bg x ej ek
  rw [show G₁ • Dpair + (G₁ - G₂) • D₂ = G₁ • (D₁ - D₂) + (G₁ - G₂) • D₂ from by rw [hcoc]]
  rw [smul_sub, sub_smul]
  abel

/-! ### Linearity mini-API for the lowered covariant-gradient section -/

set_option linter.unusedSectionVars false in
/-- **The lowered covariant gradient bilinear form is additive in the differentiated (first) slot.**
`loweredCovGradDeTurckVFBilin g g_bg x (v₁ + v₂) w
= loweredCovGradDeTurckVFBilin g g_bg x v₁ w + loweredCovGradDeTurckVFBilin g g_bg x v₂ w`.  This is
the linearity of `∇^g_· W` (the covariant gradient in its direction slot) followed by the linearity
of `g.inner`. -/
theorem loweredCovGradDeTurckVFBilin_add_left (g g_bg : SmoothRiemannianMetric I M) (x : M)
    (v₁ v₂ w : TangentSpace I x) :
    loweredCovGradDeTurckVFBilin (I := I) g g_bg x (v₁ + v₂) w =
      loweredCovGradDeTurckVFBilin (I := I) g g_bg x v₁ w
      + loweredCovGradDeTurckVFBilin (I := I) g g_bg x v₂ w := by
  rw [loweredCovGradDeTurckVFBilin_apply, loweredCovGradDeTurckVFBilin_apply,
    loweredCovGradDeTurckVFBilin_apply, map_add, map_add, ContinuousLinearMap.add_apply]

set_option linter.unusedSectionVars false in
/-- **The lowered covariant gradient bilinear form is homogeneous in the differentiated (first)
slot.**  `loweredCovGradDeTurckVFBilin g g_bg x (c • v) w
= c • loweredCovGradDeTurckVFBilin g g_bg x v w`. -/
theorem loweredCovGradDeTurckVFBilin_smul_left (g g_bg : SmoothRiemannianMetric I M) (x : M)
    (c : ℝ) (v w : TangentSpace I x) :
    loweredCovGradDeTurckVFBilin (I := I) g g_bg x (c • v) w =
      c • loweredCovGradDeTurckVFBilin (I := I) g g_bg x v w := by
  rw [loweredCovGradDeTurckVFBilin_apply, loweredCovGradDeTurckVFBilin_apply, map_smul, map_smul,
    ContinuousLinearMap.smul_apply]

set_option linter.unusedSectionVars false in
/-- **The lowered covariant gradient bilinear form is additive in the lowered (second) slot.** -/
theorem loweredCovGradDeTurckVFBilin_add_right (g g_bg : SmoothRiemannianMetric I M) (x : M)
    (v w₁ w₂ : TangentSpace I x) :
    loweredCovGradDeTurckVFBilin (I := I) g g_bg x v (w₁ + w₂) =
      loweredCovGradDeTurckVFBilin (I := I) g g_bg x v w₁
      + loweredCovGradDeTurckVFBilin (I := I) g g_bg x v w₂ := by
  rw [loweredCovGradDeTurckVFBilin_apply, loweredCovGradDeTurckVFBilin_apply,
    loweredCovGradDeTurckVFBilin_apply, map_add]

set_option linter.unusedSectionVars false in
/-- **The lowered covariant gradient bilinear form is homogeneous in the lowered (second) slot.** -/
theorem loweredCovGradDeTurckVFBilin_smul_right (g g_bg : SmoothRiemannianMetric I M) (x : M)
    (c : ℝ) (v w : TangentSpace I x) :
    loweredCovGradDeTurckVFBilin (I := I) g g_bg x v (c • w) =
      c • loweredCovGradDeTurckVFBilin (I := I) g g_bg x v w := by
  rw [loweredCovGradDeTurckVFBilin_apply, loweredCovGradDeTurckVFBilin_apply, map_smul]

end Pullback
end RicciFlow
end PDE
end DifferentialGeometry

end
