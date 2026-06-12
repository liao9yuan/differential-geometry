import DifferentialGeometry.Geometry.Connection.TensorNabla.VectorFieldCovariantGradientSection

/-! # The slot telescope of the symmetrised-lowered DeTurck-field difference

For a closed (compact, boundaryless) smooth Riemannian manifold modelled on a real inner-product
space `E`, the difference of two metrics' symmetrised covariant lowerings of the DeTurck vector
field, `symLoweredDeTurckVFRetagG0 g₀ g₁ g_bg − symLoweredDeTurckVFRetagG0 g₀ g₂ g_bg`, varies the
metric in **three independent slots at once**: the `g`-inner lowering, the Levi-Civita `g`
connection, and the DeTurck field `W = deTurckVF g g_bg` itself.  This file makes the three slots
*separable* and proves the **slot-telescope identity**: the difference is the sum of the three
single-slot difference sections.

## The mixed carrier

`loweredCovGradDeTurckVFMixed g₀ g_low g_conn g_fld g_bg : SmoothCcTensor g₀ 0 2` is the
`g₀`-tagged un-symmetrised lowered covariant gradient with the three metric roles **decoupled**:
its fibre value is `g_low(∇^{g_conn}_v W_fld, w)`, `W_fld = deTurckVF g_fld g_bg`.  At equal
metrics it recovers the on-disk carrier
(`loweredCovGradDeTurckVFMixed_diag_eq : Mixed g₀ g g g g_bg = loweredCovGradDeTurckVFRetagG0
g₀ g g_bg`).  Its construction is the verbatim multilinear-bundle coordinate route of
`loweredCovGradDeTurckVF` (`VectorFieldCovariantGradientSection.lean`) with the three roles split:
smoothness pairs the `g_conn`-covariant-gradient field of the smooth DeTurck field
(`LeviCivita_section_contMDiffOn_univ` + `clm_bundle_apply`) against a smooth direction frame
through the smooth `g_low`-inner (`contMDiff_g_inner_of_smooth_sections`).

## The three slot-difference sections

Walking the metric chain `(g₁,g₁,g₁) → (g₂,g₁,g₁) → (g₂,g₂,g₁) → (g₂,g₂,g₂)` one slot at a time
and symmetrising (adding the `(0 1)`-slot swap of each difference, matching the keystone
`symLoweredDeTurckVFRetagG0_eq_loweredCovGrad_add_swap`):

* `deTurckVFLoweringSlotDiff g₀ g₁ g₂ g_bg` — the **lowering-slot** difference, fibre
  `(g₁ − g₂)(∇^{g₁}_v W₁, w)` symmetrised;
* `deTurckVFConnectionSlotDiff g₀ g₁ g₂ g_bg` — the **connection-slot** difference, fibre
  `g₂((∇^{g₁} − ∇^{g₂})_v W₁, w)` symmetrised;
* `deTurckVFFieldSlotDiff g₀ g₁ g₂ g_bg` — the **field-slot** difference, fibre
  `g₂(∇^{g₂}_v (W₁ − W₂), w)` symmetrised.

## The telescope

`symLoweredDeTurckVFRetagG0_sub_eq_slotTelescope`: the symmetrised-lowered DeTurck-field
difference is exactly the sum of the three slot differences.  After the keystone symmetrisation
re-expression and the diagonal identification of the mixed carrier, this is the pure
additive-group telescope `a − d = (a − b) + (b − c) + (c − d)` applied under the (additive) slot
swap — closed by `abel`.

## Non-vacuity

Each slot difference vanishes at `g₁ = g₂` (each is a difference of two mixed carriers whose
arguments coincide there, `sub_self`), and the mixed carrier itself is the genuine `∇W` reader
(at `g_bg = g_fld` the DeTurck field is the zero section, inherited from
`loweredCovGradDeTurckVF_self_toModel` through `loweredCovGradDeTurckVFMixed_diag_eq`). -/

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

/-! ### The mixed-slot lowered covariant-gradient bilinear form -/

/-- **The mixed-slot lowered covariant gradient of the DeTurck vector field, as a continuous
bilinear form.**  The three metric roles decoupled: the lowering metric `g_low`, the connection
metric `g_conn`, and the field metric `g_fld`; with `W = deTurckVF g_fld g_bg`,
`(v, w) ↦ g_low(∇^{g_conn}_v W, w)`.  At `g_low = g_conn = g_fld = g` this is definitionally
`loweredCovGradDeTurckVFBilin g g_bg x`. -/
def loweredCovGradDeTurckVFMixedBilin (g_low g_conn g_fld g_bg : SmoothRiemannianMetric I M)
    (x : M) : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  (g_low.inner x).comp ((LeviCivita (I := I) g_conn)
    (deTurckVF (I := I) g_fld g_bg : ∀ x : M, TangentSpace I x) x)

set_option linter.unusedSectionVars false in
/-- **The mixed-slot lowered covariant gradient bilinear form evaluated.**
`loweredCovGradDeTurckVFMixedBilin g_low g_conn g_fld g_bg x v w = g_low(∇^{g_conn}_v W, w)`,
`W = deTurckVF g_fld g_bg`. -/
theorem loweredCovGradDeTurckVFMixedBilin_apply
    (g_low g_conn g_fld g_bg : SmoothRiemannianMetric I M) (x : M) (v w : TangentSpace I x) :
    loweredCovGradDeTurckVFMixedBilin (I := I) g_low g_conn g_fld g_bg x v w =
      g_low.inner x ((LeviCivita (I := I) g_conn)
        (deTurckVF (I := I) g_fld g_bg : ∀ x : M, TangentSpace I x) x v) w := by
  rfl

/-- **Smoothness of the mixed-slot lowered covariant-gradient bilinear form on smooth fields.**
For smooth tangent vector fields `X`, `Y`, the scalar field
`x ↦ g_low(∇^{g_conn}_{X x} W, Y x)` is smooth: the covariant-gradient field is smooth by
`LeviCivita_section_contMDiffOn_univ` applied to the smooth DeTurck field, post-applied to the
smooth direction `X` (`clm_bundle_apply`); the `g_low`-inner pairing of two smooth tangent fields
is smooth (`contMDiff_g_inner_of_smooth_sections`). -/
theorem loweredCovGradDeTurckVFMixedBilin_pairing_contMDiff
    (g_low g_conn g_fld g_bg : SmoothRiemannianMetric I M)
    {X Y : Π b : M, TangentSpace I b}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Y)) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun b : M =>
        loweredCovGradDeTurckVFMixedBilin (I := I) g_low g_conn g_fld g_bg b (X b) (Y b)) := by
  classical
  set W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ := deTurckVF (I := I) g_fld g_bg with hW
  have hWsmooth : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ((∞ : WithTop ℕ∞) + 1)
      (fun x : M => (⟨x, (W : ∀ x : M, TangentSpace I x) x⟩ : TotalSpace E (TangentSpace I)))
      Set.univ := by
    have h_le : ((∞ : WithTop ℕ∞) + 1) ≤ ∞ := by rw [ENat.coe_top_add_one]
    exact (W.contMDiff.of_le h_le).contMDiffOn
  have hcov : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun x : M =>
        (⟨x, (LeviCivita (I := I) g_conn) (W : ∀ x : M, TangentSpace I x) x⟩ :
          TotalSpace (E →L[ℝ] E) (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x))) := by
    rw [← contMDiffOn_univ]
    exact LeviCivita_section_contMDiffOn_univ (I := I) g_conn hWsmooth
  have hD : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M =>
        (TotalSpace.mk' E (E := fun y : M => TangentSpace I y) b
          ((LeviCivita (I := I) g_conn) (W : ∀ x : M, TangentSpace I x) b (X b)))) :=
    ContMDiff.clm_bundle_apply (b := id) hcov hX
  let D : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    ContMDiffSection.mk (fun b : M => (LeviCivita (I := I) g_conn)
      (W : ∀ x : M, TangentSpace I x) b (X b)) hD
  let Ys : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    ContMDiffSection.mk Y hY
  have hpair : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun b : M => g_low.inner b (D b) (Ys b)) :=
    Integral.DivergenceTheorem.contMDiff_g_inner_of_smooth_sections (I := I) g_low D Ys
  refine hpair.congr (fun b => ?_)
  rfl

/-! ### The mixed carrier as a smooth `(0,2)`-tensor section -/

/-- The pointwise model `(0,2)`-tensor value of the mixed-slot lowered covariant gradient. -/
def loweredCovGradMixedModelFun (g_low g_conn g_fld g_bg : SmoothRiemannianMetric I M) (x : M) :
    Tensor0SSpace 2 I x :=
  Tensor0SSpace.ofModel
    (bilinFormToModel (TangentSpace I x)
      (loweredCovGradDeTurckVFMixedBilin (I := I) g_low g_conn g_fld g_bg x))

set_option linter.unusedSectionVars false in
theorem loweredCovGradMixedModelFun_toModel_apply
    (g_low g_conn g_fld g_bg : SmoothRiemannianMetric I M) (x : M)
    (v : Fin 2 → TangentSpace I x) :
    Tensor0SSpace.toModel (loweredCovGradMixedModelFun (I := I) g_low g_conn g_fld g_bg x) v =
      loweredCovGradDeTurckVFMixedBilin (I := I) g_low g_conn g_fld g_bg x (v 0) (v 1) := by
  unfold loweredCovGradMixedModelFun
  rw [Tensor0SSpace.toModel_ofModel]
  exact bilinFormToModel_apply (TangentSpace I x)
    (loweredCovGradDeTurckVFMixedBilin (I := I) g_low g_conn g_fld g_bg x) v

/-- **The mixed-slot lowered covariant gradient as a smooth covariant `(0,2)`-tensor field.**
Chart-component smoothness is `loweredCovGradDeTurckVFMixedBilin_pairing_contMDiff` on the
chart-pushforward frame (the same `contMDiff_multilinearSection_iff_coord` route as
`loweredCovGradDeTurckVFField`). -/
def loweredCovGradDeTurckVFMixedField (g_low g_conn g_fld g_bg : SmoothRiemannianMetric I M) :
    Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) ∞ 2 :=
  letI := tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 2
  letI := TangentBundle.contMDiffVectorBundle (I := I) (M := M) (n := ∞)
  ⟨fun x => loweredCovGradMixedModelFun (I := I) g_low g_conn g_fld g_bg x, by
    let d := Module.finrank ℝ E
    let b : Module.Basis (Fin d) ℝ E := chartModelBasis E
    refine (contMDiff_multilinearSection_iff_coord (TangentSpace I) ∞ b _).mpr
      fun σ x₀ => ?_
    have hcomp : ContMDiffOn I 𝓘(ℝ, ℝ) ∞
        (fun x : M =>
          loweredCovGradDeTurckVFMixedBilin (I := I) g_low g_conn g_fld g_bg x
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
          (fun bb : M => loweredCovGradDeTurckVFMixedBilin (I := I) g_low g_conn g_fld g_bg bb
            ((S (σ 0)) bb) ((S (σ 1)) bb)) :=
        loweredCovGradDeTurckVFMixedBilin_pairing_contMDiff (I := I) g_low g_conn g_fld g_bg
          (hSk (σ 0)) (hSk (σ 1))
      have hchart_at : ContMDiffAt I 𝓘(ℝ, ℝ) ∞
          (fun x : M => loweredCovGradDeTurckVFMixedBilin (I := I) g_low g_conn g_fld g_bg x
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
    change Tensor0SSpace.toModel
        (loweredCovGradMixedModelFun (I := I) g_low g_conn g_fld g_bg x)
        (fun j => (trivializationAt E (TangentSpace I) x₀).symmL ℝ x (b (σ j))) = _
    rw [loweredCovGradMixedModelFun_toModel_apply]
    rfl⟩

/-- The mixed-slot lowered covariant gradient as a smooth mixed `(0,2)`-tensor section. -/
def loweredCovGradDeTurckVFMixedSection' (g_low g_conn g_fld g_bg : SmoothRiemannianMetric I M) :
    Cₛ^∞⟮I; TensorRSModel 0 2 ℝ E, (fun x : M => TensorRSSpace 0 2 I x)⟯ :=
  MixedSection.fromMultilinearSection (𝕜 := ℝ) (F := E) (IB := I)
    (E := (TangentSpace I : M → Type _)) ∞
    (loweredCovGradDeTurckVFMixedField (I := I) g_low g_conn g_fld g_bg)

/-- **The `g₀`-tagged mixed-slot lowered covariant gradient of the DeTurck vector field.**  The
`SmoothCcTensor g₀ 0 2` whose fibre value is `g_low(∇^{g_conn}_v W, w)`, `W = deTurckVF g_fld
g_bg` — the three metric roles of `loweredCovGradDeTurckVFRetagG0` decoupled so the DeTurck-field
difference can be telescoped one slot at a time.  Compact support is automatic on the compact
manifold. -/
def loweredCovGradDeTurckVFMixed (g₀ g_low g_conn g_fld g_bg : SmoothRiemannianMetric I M) :
    Integral.L2.SmoothCcTensor g₀ 0 2 where
  toSection := loweredCovGradDeTurckVFMixedSection' (I := I) g_low g_conn g_fld g_bg
  hasCompactSupport := HasCompactSupport.of_compactSpace _

set_option linter.unusedSectionVars false in
/-- **The fibre value of the mixed carrier.**  Evaluating at the canonical unit `(0,0)`-tensor
and a tangent pair recovers `g_low(∇^{g_conn}_v W, w)`, `W = deTurckVF g_fld g_bg`. -/
theorem loweredCovGradDeTurckVFMixed_toModel_apply
    (g₀ g_low g_conn g_fld g_bg : SmoothRiemannianMetric I M) (x : M)
    (v : Fin 2 → TangentSpace I x) :
    Tensor0SSpace.toModel
        ((loweredCovGradDeTurckVFMixed (I := I) g₀ g_low g_conn g_fld g_bg).toSection x
          (ContinuousMultilinearMap.constOfIsEmpty ℝ
            (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))) v =
      loweredCovGradDeTurckVFMixedBilin (I := I) g_low g_conn g_fld g_bg x (v 0) (v 1) := by
  classical
  change Tensor0SSpace.toModel
      ((MixedSection.eval₀ (F := E) (E := (TangentSpace I : M → Type _)) x).smulRight
          (loweredCovGradDeTurckVFMixedField (I := I) g_low g_conn g_fld g_bg x)
        (ContinuousMultilinearMap.constOfIsEmpty ℝ
          (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))) v = _
  rw [ContinuousLinearMap.smulRight_apply, MixedSection.eval₀_apply,
    ContinuousMultilinearMap.constOfIsEmpty_apply, one_smul]
  change Tensor0SSpace.toModel
    (loweredCovGradMixedModelFun (I := I) g_low g_conn g_fld g_bg x) v = _
  rw [loweredCovGradMixedModelFun_toModel_apply]

set_option linter.unusedSectionVars false in
/-- **Diagonal identification.**  At equal metric slots the mixed carrier is the on-disk
`g₀`-retagged lowered covariant gradient: `loweredCovGradDeTurckVFMixed g₀ g g g g_bg =
loweredCovGradDeTurckVFRetagG0 g₀ g g_bg`.  Proved by unit-fibre extensionality: both fibres are
`g(∇^g_v W, w)` (`loweredCovGradDeTurckVFMixed_toModel_apply` against
`loweredCovGradDeTurckVFRetagG0_unitModel_eq`, the bilinear forms agreeing definitionally). -/
theorem loweredCovGradDeTurckVFMixed_diag_eq (g₀ g g_bg : SmoothRiemannianMetric I M) :
    loweredCovGradDeTurckVFMixed (I := I) g₀ g g g g_bg =
      loweredCovGradDeTurckVFRetagG0 (I := I) g₀ g g_bg := by
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
  rw [loweredCovGradDeTurckVFMixed_toModel_apply (I := I) g₀ g g g g_bg x v]
  have hR := loweredCovGradDeTurckVFRetagG0_unitModel_eq (I := I) g₀ g g_bg x (v 0) (v 1)
  rw [show (![v 0, v 1] : Fin 2 → TangentSpace I x) = v from by
    funext i; fin_cases i <;> rfl] at hR
  rw [hR]
  rfl

/-! ### The three slot-difference sections -/

/-- **The lowering-slot difference of the symmetrised-lowered DeTurck-field difference.**  The
symmetrised section whose un-symmetrised half has fibre `(g₁ − g₂)(∇^{g₁}_v W₁, w)`,
`W₁ = deTurckVF g₁ g_bg`: the first leg of the slot telescope, varying only the `g`-inner
lowering slot.  Vanishes at `g₁ = g₂` (`sub_self`). -/
def deTurckVFLoweringSlotDiff (g₀ g₁ g₂ g_bg : SmoothRiemannianMetric I M) :
    Integral.L2.SmoothCcTensor g₀ 0 2 :=
  (loweredCovGradDeTurckVFMixed (I := I) g₀ g₁ g₁ g₁ g_bg
      - loweredCovGradDeTurckVFMixed (I := I) g₀ g₂ g₁ g₁ g_bg)
    + permuteCcTensor (I := I) g₀ (Equiv.swap 0 1)
        (loweredCovGradDeTurckVFMixed (I := I) g₀ g₁ g₁ g₁ g_bg
          - loweredCovGradDeTurckVFMixed (I := I) g₀ g₂ g₁ g₁ g_bg)

/-- **The connection-slot difference of the symmetrised-lowered DeTurck-field difference.**  The
symmetrised section whose un-symmetrised half has fibre `g₂((∇^{g₁} − ∇^{g₂})_v W₁, w)`,
`W₁ = deTurckVF g₁ g_bg`: the second leg of the slot telescope, varying only the Levi-Civita
connection slot.  Vanishes at `g₁ = g₂` (`sub_self`). -/
def deTurckVFConnectionSlotDiff (g₀ g₁ g₂ g_bg : SmoothRiemannianMetric I M) :
    Integral.L2.SmoothCcTensor g₀ 0 2 :=
  (loweredCovGradDeTurckVFMixed (I := I) g₀ g₂ g₁ g₁ g_bg
      - loweredCovGradDeTurckVFMixed (I := I) g₀ g₂ g₂ g₁ g_bg)
    + permuteCcTensor (I := I) g₀ (Equiv.swap 0 1)
        (loweredCovGradDeTurckVFMixed (I := I) g₀ g₂ g₁ g₁ g_bg
          - loweredCovGradDeTurckVFMixed (I := I) g₀ g₂ g₂ g₁ g_bg)

/-- **The field-slot difference of the symmetrised-lowered DeTurck-field difference.**  The
symmetrised section whose un-symmetrised half has fibre `g₂(∇^{g₂}_v (W₁ − W₂), w)`,
`Wᵢ = deTurckVF gᵢ g_bg`: the third leg of the slot telescope, varying only the DeTurck field
slot.  Vanishes at `g₁ = g₂` (`sub_self`). -/
def deTurckVFFieldSlotDiff (g₀ g₁ g₂ g_bg : SmoothRiemannianMetric I M) :
    Integral.L2.SmoothCcTensor g₀ 0 2 :=
  (loweredCovGradDeTurckVFMixed (I := I) g₀ g₂ g₂ g₁ g_bg
      - loweredCovGradDeTurckVFMixed (I := I) g₀ g₂ g₂ g₂ g_bg)
    + permuteCcTensor (I := I) g₀ (Equiv.swap 0 1)
        (loweredCovGradDeTurckVFMixed (I := I) g₀ g₂ g₂ g₁ g_bg
          - loweredCovGradDeTurckVFMixed (I := I) g₀ g₂ g₂ g₂ g_bg)

set_option linter.unusedSectionVars false in
/-- **Slot permutation distributes over a section difference.**  `permuteCcTensor g₀ σ` is a
fibrewise slot reindexing, hence additive: its unit model is the `domDomCongr σ` of the operand's
(`permuteCcTensor_unitModel`), and `domDomCongr` is linear.  Local re-statement at the
`SmoothCcTensor` level (no subtractivity lemma for `permuteCcTensor` is on disk). -/
private theorem permuteCcTensor_sub_local (g₀ : SmoothRiemannianMetric I M) {s : ℕ}
    (σ : Equiv.Perm (Fin s)) (A B : Integral.L2.SmoothCcTensor g₀ 0 s) :
    DeTurck.permuteCcTensor (I := I) g₀ σ (A - B) =
      DeTurck.permuteCcTensor (I := I) g₀ σ A - DeTurck.permuteCcTensor (I := I) g₀ σ B := by
  classical
  apply Integral.L2.SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply DifferentialGeometry.PDE.DeTurck.tensor0s_ext_unitZero (I := I) (M := M) (s := s)
  apply Tensor0SBundle.Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro m
  beta_reduce
  have hL : Tensor0SBundle.Tensor0SSpace.toModel
        ((DeTurck.permuteCcTensor (I := I) g₀ σ (A - B)).toSection x
          (Integral.Connection.unitZeroSec (I := I) (M := M) x)) =
      ContinuousMultilinearMap.domDomCongr σ
        (Tensor0SBundle.Tensor0SSpace.toModel ((A - B).toSection x
          (Integral.Connection.unitZeroSec (I := I) (M := M) x))) :=
    DeTurck.permuteCcTensor_unitModel (I := I) g₀ σ (A - B) x
  have hA : Tensor0SBundle.Tensor0SSpace.toModel
        ((DeTurck.permuteCcTensor (I := I) g₀ σ A).toSection x
          (Integral.Connection.unitZeroSec (I := I) (M := M) x)) =
      ContinuousMultilinearMap.domDomCongr σ
        (Tensor0SBundle.Tensor0SSpace.toModel (A.toSection x
          (Integral.Connection.unitZeroSec (I := I) (M := M) x))) :=
    DeTurck.permuteCcTensor_unitModel (I := I) g₀ σ A x
  have hB : Tensor0SBundle.Tensor0SSpace.toModel
        ((DeTurck.permuteCcTensor (I := I) g₀ σ B).toSection x
          (Integral.Connection.unitZeroSec (I := I) (M := M) x)) =
      ContinuousMultilinearMap.domDomCongr σ
        (Tensor0SBundle.Tensor0SSpace.toModel (B.toSection x
          (Integral.Connection.unitZeroSec (I := I) (M := M) x))) :=
    DeTurck.permuteCcTensor_unitModel (I := I) g₀ σ B x
  have hsubval : (A - B).toSection x = A.toSection x - B.toSection x := by
    rw [Integral.L2.SmoothCcTensor.toSection_sub, ContMDiffSection.coe_sub, Pi.sub_apply]
  have hsubval' : ((DeTurck.permuteCcTensor (I := I) g₀ σ A
        - DeTurck.permuteCcTensor (I := I) g₀ σ B)).toSection x =
      (DeTurck.permuteCcTensor (I := I) g₀ σ A).toSection x
        - (DeTurck.permuteCcTensor (I := I) g₀ σ B).toSection x := by
    rw [Integral.L2.SmoothCcTensor.toSection_sub, ContMDiffSection.coe_sub, Pi.sub_apply]
  calc Tensor0SBundle.Tensor0SSpace.toModel
        ((DeTurck.permuteCcTensor (I := I) g₀ σ (A - B)).toSection x
          (Integral.Connection.unitZeroSec (I := I) (M := M) x)) m
      = (ContinuousMultilinearMap.domDomCongr σ
          (Tensor0SBundle.Tensor0SSpace.toModel ((A - B).toSection x
            (Integral.Connection.unitZeroSec (I := I) (M := M) x)))) m := by rw [hL]
    _ = (ContinuousMultilinearMap.domDomCongr σ
            (Tensor0SBundle.Tensor0SSpace.toModel (A.toSection x
              (Integral.Connection.unitZeroSec (I := I) (M := M) x)))) m
          - (ContinuousMultilinearMap.domDomCongr σ
            (Tensor0SBundle.Tensor0SSpace.toModel (B.toSection x
              (Integral.Connection.unitZeroSec (I := I) (M := M) x)))) m := by
        rw [hsubval]; rfl
    _ = Tensor0SBundle.Tensor0SSpace.toModel
          ((DeTurck.permuteCcTensor (I := I) g₀ σ A).toSection x
            (Integral.Connection.unitZeroSec (I := I) (M := M) x)) m
          - Tensor0SBundle.Tensor0SSpace.toModel
          ((DeTurck.permuteCcTensor (I := I) g₀ σ B).toSection x
            (Integral.Connection.unitZeroSec (I := I) (M := M) x)) m := by
        rw [hA, hB]
    _ = Tensor0SBundle.Tensor0SSpace.toModel
          ((DeTurck.permuteCcTensor (I := I) g₀ σ A
            - DeTurck.permuteCcTensor (I := I) g₀ σ B).toSection x
            (Integral.Connection.unitZeroSec (I := I) (M := M) x)) m := by
        rw [hsubval']; rfl

/-! ### The slot-telescope identity -/

set_option linter.unusedSectionVars false in
/-- **(The slot-telescope identity.)**  The difference of the two metrics' symmetrised covariant
lowerings of the DeTurck vector field is the sum of the three single-slot difference sections:
```
symLoweredDeTurckVFRetagG0 g₀ g₁ g_bg − symLoweredDeTurckVFRetagG0 g₀ g₂ g_bg
  = deTurckVFLoweringSlotDiff + deTurckVFConnectionSlotDiff + deTurckVFFieldSlotDiff.
```
By the keystone symmetrisation `symLoweredDeTurckVFRetagG0_eq_loweredCovGrad_add_swap` and the
diagonal identification `loweredCovGradDeTurckVFMixed_diag_eq`, both sides are additive
combinations of mixed carriers along the metric chain `(g₁,g₁,g₁) → (g₂,g₁,g₁) → (g₂,g₂,g₁) →
(g₂,g₂,g₂)`; after distributing the slot swap over the three differences
(`permuteCcTensor_sub_local`) the identity is the pure additive-group telescope
`a − d = (a − b) + (b − c) + (c − d)` (under the swap as well), closed by `abel`. -/
theorem symLoweredDeTurckVFRetagG0_sub_eq_slotTelescope
    (g₀ g₁ g₂ g_bg : SmoothRiemannianMetric I M) :
    symLoweredDeTurckVFRetagG0 (I := I) g₀ g₁ g_bg
        - symLoweredDeTurckVFRetagG0 (I := I) g₀ g₂ g_bg =
      deTurckVFLoweringSlotDiff (I := I) g₀ g₁ g₂ g_bg
        + deTurckVFConnectionSlotDiff (I := I) g₀ g₁ g₂ g_bg
        + deTurckVFFieldSlotDiff (I := I) g₀ g₁ g₂ g_bg := by
  rw [symLoweredDeTurckVFRetagG0_eq_loweredCovGrad_add_swap (I := I) g₀ g₁ g_bg,
    symLoweredDeTurckVFRetagG0_eq_loweredCovGrad_add_swap (I := I) g₀ g₂ g_bg,
    ← loweredCovGradDeTurckVFMixed_diag_eq (I := I) g₀ g₁ g_bg,
    ← loweredCovGradDeTurckVFMixed_diag_eq (I := I) g₀ g₂ g_bg]
  unfold deTurckVFLoweringSlotDiff deTurckVFConnectionSlotDiff deTurckVFFieldSlotDiff
  rw [permuteCcTensor_sub_local (I := I) g₀ (Equiv.swap 0 1)
      (loweredCovGradDeTurckVFMixed (I := I) g₀ g₁ g₁ g₁ g_bg)
      (loweredCovGradDeTurckVFMixed (I := I) g₀ g₂ g₁ g₁ g_bg),
    permuteCcTensor_sub_local (I := I) g₀ (Equiv.swap 0 1)
      (loweredCovGradDeTurckVFMixed (I := I) g₀ g₂ g₁ g₁ g_bg)
      (loweredCovGradDeTurckVFMixed (I := I) g₀ g₂ g₂ g₁ g_bg),
    permuteCcTensor_sub_local (I := I) g₀ (Equiv.swap 0 1)
      (loweredCovGradDeTurckVFMixed (I := I) g₀ g₂ g₂ g₁ g_bg)
      (loweredCovGradDeTurckVFMixed (I := I) g₀ g₂ g₂ g₂ g_bg)]
  abel

end Pullback
end RicciFlow
end PDE
end DifferentialGeometry

end
