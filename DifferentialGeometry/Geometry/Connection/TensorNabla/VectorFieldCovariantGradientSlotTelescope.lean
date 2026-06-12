import DifferentialGeometry.Geometry.Connection.TensorNabla.VectorFieldCovariantGradientSection
import DifferentialGeometry.Geometry.Connection.TensorNabla.VectorFieldCovariantGradientDifference
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CrossCorrectionParallelContraction

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

set_option linter.unusedSectionVars false in
/-- **The connection-slot carrier difference as the connection-difference action section.**  Holding
the lowering metric at `g₀` and the field metric at `g₁`, the connection-slot difference of the mixed
carrier — only the Levi-Civita connection varied `g₀ → g₁` — is the on-disk connection-difference
action section `connDiffActionSection g₀ g₁ g₀ g_bg` (`VectorFieldCovariantGradientDifference.lean`):
```
loweredCovGradDeTurckVFMixed g₀ g₀ g₁ g₁ g_bg − loweredCovGradDeTurckVFMixed g₀ g₀ g₀ g₁ g_bg
  = connDiffActionSection g₀ g₁ g₀ g_bg,
```
both fibres being the connection-difference contraction `g₀(connDiff g₁ g₀ x (W₁ x) v, w)`,
`W₁ = deTurckVF g₁ g_bg`.  Proved by unit-fibre extensionality: the LHS fibre is the difference of
the two mixed bilinear forms `g₀(∇^{g₁}_v W₁, w) − g₀(∇^{g₀}_v W₁, w)`
(`loweredCovGradDeTurckVFMixedBilin_apply`), which by `connDiff_deTurckVF_apply` and the additivity of
the `g₀`-inner lowering equals the RHS fibre `g₀(connDiff g₁ g₀ x (W₁ x) v, w)`
(`connDiffActionBilin_apply`). -/
theorem loweredCovGradDeTurckVFMixed_connSlot_sub_eq_connDiffActionSection
    (g₀ g₁ g_bg : SmoothRiemannianMetric I M) :
    loweredCovGradDeTurckVFMixed (I := I) g₀ g₀ g₁ g₁ g_bg
        - loweredCovGradDeTurckVFMixed (I := I) g₀ g₀ g₀ g₁ g_bg =
      connDiffActionSection (I := I) g₀ g₁ g₀ g_bg := by
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
  have hL : ((loweredCovGradDeTurckVFMixed (I := I) g₀ g₀ g₁ g₁ g_bg
          - loweredCovGradDeTurckVFMixed (I := I) g₀ g₀ g₀ g₁ g_bg).toSection x
        (ContinuousMultilinearMap.constOfIsEmpty ℝ
          (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))) =
      (loweredCovGradDeTurckVFMixed (I := I) g₀ g₀ g₁ g₁ g_bg).toSection x
          (ContinuousMultilinearMap.constOfIsEmpty ℝ
            (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))
        - (loweredCovGradDeTurckVFMixed (I := I) g₀ g₀ g₀ g₁ g_bg).toSection x
          (ContinuousMultilinearMap.constOfIsEmpty ℝ
            (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ)) := by
    rw [Integral.L2.SmoothCcTensor.toSection_sub, ContMDiffSection.coe_sub, Pi.sub_apply,
      ContinuousLinearMap.sub_apply]
  rw [hL]
  simp only [Tensor0SSpace.toModel_sub, ContinuousMultilinearMap.sub_apply]
  rw [loweredCovGradDeTurckVFMixed_toModel_apply (I := I) g₀ g₀ g₁ g₁ g_bg x v,
    loweredCovGradDeTurckVFMixed_toModel_apply (I := I) g₀ g₀ g₀ g₁ g_bg x v]
  rw [loweredCovGradDeTurckVFMixedBilin_apply, loweredCovGradDeTurckVFMixedBilin_apply]
  have hRHS := connDiffActionSection_toModel_apply (I := I) g₀ g₁ g₀ g_bg x (v 0) (v 1)
  rw [show (![v 0, v 1] : Fin 2 → TangentSpace I x) = v from by
    funext i; fin_cases i <;> rfl] at hRHS
  rw [hRHS, connDiffActionBilin_apply,
    connDiff_deTurckVF_apply (I := I) g₁ g₀ g_bg x (v 0),
    map_sub, ContinuousLinearMap.sub_apply]

set_option linter.unusedSectionVars false in
/-- **The field-slot carrier difference as the field-difference gradient section.**  Holding the
lowering and connection metrics both at `g₀`, the field-slot difference of the mixed carrier — only
the DeTurck field metric varied `g₀ → g₁` — is the on-disk field-difference gradient section
`fieldDiffGradSection g₀ g₁ g₀ g_bg` (`VectorFieldCovariantGradientDifference.lean`):
```
loweredCovGradDeTurckVFMixed g₀ g₀ g₀ g₁ g_bg − loweredCovGradDeTurckVFMixed g₀ g₀ g₀ g₀ g_bg
  = fieldDiffGradSection g₀ g₁ g₀ g_bg,
```
both fibres being the field-difference contraction `g₀(∇^{g₀}_v (W₁ − W₀), w)`,
`Wᵢ = deTurckVF gᵢ g_bg`.  Proved by unit-fibre extensionality: the LHS fibre is the difference of
the two mixed bilinear forms `g₀(∇^{g₀}_v W₁, w) − g₀(∇^{g₀}_v W₀, w)`
(`loweredCovGradDeTurckVFMixedBilin_apply`), which by `leviCivita_section_sub_apply` and the
additivity of the `g₀`-inner lowering equals the RHS fibre `g₀(∇^{g₀}_v (W₁ − W₀), w)`
(`fieldDiffGradBilin_apply`). -/
theorem loweredCovGradDeTurckVFMixed_fldSlot_sub_eq_fieldDiffGradSection
    (g₀ g₁ g_bg : SmoothRiemannianMetric I M) :
    loweredCovGradDeTurckVFMixed (I := I) g₀ g₀ g₀ g₁ g_bg
        - loweredCovGradDeTurckVFMixed (I := I) g₀ g₀ g₀ g₀ g_bg =
      fieldDiffGradSection (I := I) g₀ g₁ g₀ g_bg := by
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
  have hL : ((loweredCovGradDeTurckVFMixed (I := I) g₀ g₀ g₀ g₁ g_bg
          - loweredCovGradDeTurckVFMixed (I := I) g₀ g₀ g₀ g₀ g_bg).toSection x
        (ContinuousMultilinearMap.constOfIsEmpty ℝ
          (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))) =
      (loweredCovGradDeTurckVFMixed (I := I) g₀ g₀ g₀ g₁ g_bg).toSection x
          (ContinuousMultilinearMap.constOfIsEmpty ℝ
            (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))
        - (loweredCovGradDeTurckVFMixed (I := I) g₀ g₀ g₀ g₀ g_bg).toSection x
          (ContinuousMultilinearMap.constOfIsEmpty ℝ
            (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ)) := by
    rw [Integral.L2.SmoothCcTensor.toSection_sub, ContMDiffSection.coe_sub, Pi.sub_apply,
      ContinuousLinearMap.sub_apply]
  rw [hL]
  simp only [Tensor0SSpace.toModel_sub, ContinuousMultilinearMap.sub_apply]
  rw [loweredCovGradDeTurckVFMixed_toModel_apply (I := I) g₀ g₀ g₀ g₁ g_bg x v,
    loweredCovGradDeTurckVFMixed_toModel_apply (I := I) g₀ g₀ g₀ g₀ g_bg x v]
  rw [loweredCovGradDeTurckVFMixedBilin_apply, loweredCovGradDeTurckVFMixedBilin_apply]
  have hRHS := fieldDiffGradSection_toModel_apply (I := I) g₀ g₁ g₀ g_bg x (v 0) (v 1)
  rw [show (![v 0, v 1] : Fin 2 → TangentSpace I x) = v from by
    funext i; fin_cases i <;> rfl] at hRHS
  rw [hRHS, fieldDiffGradBilin_apply,
    leviCivita_section_sub_apply (I := I) g₀ (deTurckVF (I := I) g₁ g_bg)
      (deTurckVF (I := I) g₀ g_bg) x (v 0),
    map_sub, ContinuousLinearMap.sub_apply]

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

/-! ### The connection-slot single-leg jet inputs -/

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization in
set_option linter.unusedSectionVars false in
/-- **(POSIT — the family-uniform order-`0` fibre sup of the connection-slot carrier difference.)**
For the fibre-small (`gFibreOpBound g₀ (ccTensorBilinSymm g₀ T₁) δ`, `δ < 1/2`) supercritically
`H^{a+2}`-bounded (`2a > finrank + 4`) realized perturbation family, the order-`0` intrinsic squared
fibre norm of the connection-slot carrier difference
`loweredCovGradDeTurckVFMixed g₀ g₀ g₁ g₁ g_bg − loweredCovGradDeTurckVFMixed g₀ g₀ g₀ g₁ g_bg`
— equal by `loweredCovGradDeTurckVFMixed_connSlot_sub_eq_connDiffActionSection` to the
connection-difference action section `connDiffActionSection g₀ g₁ g₀ g_bg`, fibre
`g₀(connDiff g₁ g₀ x (W₁ x) v, w)`, `W₁ = deTurckVF g₁ g_bg` — is uniformly bounded by a single
constant `Λ²` over the manifold and the family.

The order-`0` fibre value is the `g₀`-inner of the connection difference `connDiff g₁ g₀ x (W₁ x)`
against `W₁ x`; the connection difference's fibre sup is the Neumann-absorbed supercritical-`C¹`
bound `exists_loweredConnDiffSection_rfns_fibre_sup_le` and the smooth DeTurck field `W₁` has a
fibre sup, so the contraction has a family-uniform order-`0` sup.  Vanishes at `T₁ = 0` realized
(`g₁ = g₀`, the difference is the zero section).  Body `sorry`: a posited deep order-`0` family
fibre sup of the connection-slot carrier difference. -/
theorem exists_riemannianFiberNormSq_loweredCovGradDeTurckVFMixed_connSlot_diff_fibre_sup_le
    (g₀ g_bg : SmoothRiemannianMetric I M) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1 / 2) (B : ℝ)
    (a : ℕ) (ha : 2 * a > Module.finrank ℝ E + 4) :
    ∃ Λ : ℝ, 0 ≤ Λ ∧
      ∀ (T₁ : Integral.L2.SmoothCcTensor g₀ 0 2) (g₁ : SmoothRiemannianMetric I M),
        (∀ (x : M) (v w : TangentSpace I x),
          g₁.inner x v w = g₀.inner x v w + ccTensorBilinSymm (I := I) g₀ T₁ x v w) →
        gFibreOpBound (I := I) g₀ (fun y => ccTensorBilinSymm (I := I) g₀ T₁ y) δ →
        ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (a + 2) T₁‖ ≤ B →
        ∀ x : M,
          Integral.Connection.riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x
            ((loweredCovGradDeTurckVFMixed (I := I) g₀ g₀ g₁ g₁ g_bg
                - loweredCovGradDeTurckVFMixed (I := I) g₀ g₀ g₀ g₁ g_bg).toSection x) ≤ Λ ^ 2 :=
  sorry

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization in
set_option linter.unusedSectionVars false in
/-- **(POSIT — the family-uniform integrated Hamilton-tame jet bound of the connection-difference
action section.)**  For the fibre-small (`gFibreOpBound g₀ (ccTensorBilinSymm g₀ T₁) δ`, `δ < 1/2`)
supercritically `H^{a+2}`-bounded realized perturbation family, the order-`l` covariant-jet `L²`
norm of the connection-difference action section `connDiffActionSection g₀ g₁ g₀ g_bg` (fibre
`g₀(connDiff g₁ g₀ x (W₁ x) v, w)`, `W₁ = deTurckVF g₁ g_bg`) is dominated by the `≤ (l+2)`-jet of
the perturbation `T₁`:
```
‖∇^l (connDiffActionSection g₀ g₁ g₀ g_bg)‖² ≤ C · ∑_{i ∈ range(l+3)} ‖∇^i T₁‖².
```

The action section is the middle-slot contraction of the `g₀`-lowered connection difference
`loweredConnDiffSection g₁ g₀` (a covariant `(0,3)`-tensor) against the fixed smooth DeTurck field
`W₁ = deTurckVF g₁ g_bg`, whose covariant jets have a family-uniform fibre sup `Λ_W` (a single
smooth field per `g₁`, with the Neumann-absorbed order-`0` sup of the connection difference threaded
through `W₁`).  The covariant-Leibniz product-jet expansion of the contraction reads the order-`l`
jet of the contraction as a binomial-weighted sum of `∇^i (loweredConnDiffSection g₁ g₀)`
(`i ≤ l`) against the bounded jets of `W₁`; the connection-difference jet engine
`exists_riemannianFiberNormSq_iteratedCovGrad_loweredConnDiff_le_jetSum` folds each
`∇^i (loweredConnDiffSection g₁ g₀)` into the `≤ (i+1)`-jet of `T₁` (`i + 1 ≤ l + 1 < l + 3`), so
the whole order-`l` jet of the action section is Hamilton-tame in the `≤ (l+2)`-jet of `T₁` with a
family-uniform constant.  Vanishes at `T₁ = 0` realized (`g₁ = g₀`, `connDiff = 0`, the action
section is the zero section).  Body `sorry`: a posited deep covariant-Leibniz contraction jet
engine. -/
theorem exists_iteratedCovGrad_connDiffActionSection_connSlot_hamiltonTame_le
    (g₀ g_bg : SmoothRiemannianMetric I M) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1 / 2) (B : ℝ)
    (a : ℕ) (ha : 2 * a > Module.finrank ℝ E + 4) (l : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (T₁ : Integral.L2.SmoothCcTensor g₀ 0 2) (g₁ : SmoothRiemannianMetric I M),
        (∀ (x : M) (v w : TangentSpace I x),
          g₁.inner x v w = g₀.inner x v w + ccTensorBilinSymm (I := I) g₀ T₁ x v w) →
        gFibreOpBound (I := I) g₀ (fun y => ccTensorBilinSymm (I := I) g₀ T₁ y) δ →
        ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (a + 2) T₁‖ ≤ B →
        ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l
              (connDiffActionSection (I := I) g₀ g₁ g₀ g_bg)‖ ^ 2 ≤
          C * ∑ i ∈ Finset.range (l + 3),
            ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i T₁‖ ^ 2 :=
  sorry

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization in
set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
/-- **(The connection-slot single-leg Hamilton-tame jet bound — glued.)**  The
connection-slot leg of the `g₀`-lowered mixed DeTurck-gradient carrier difference: only the
Levi-Civita connection metric is varied `g₀ → g₁` (lowering fixed at `g₀`, field fixed at the
perturbed `g₁`).  The carrier is `loweredCovGradDeTurckVFMixed g₀ g₀ g₁ g₁ g_bg −
loweredCovGradDeTurckVFMixed g₀ g₀ g₀ g₁ g_bg`, whose fibre is the connection-difference
contraction `g₀((∇^{g₁} − ∇^{g₀})_v W₁, w)`, `W₁ = deTurckVF g₁ g_bg`.  Same three-clause shape
as the diagonal node: a background jet sup of the fixed background carrier, an order-`0` value
sup, and an integrated Hamilton-tame bound `≤ C · ∑_{i ∈ range(l+3)} ‖∇^i T₁‖²`.

Glued (consumers transitively depend on `sorryAx` only through the two posited children below):
the background clause is the pointwise jet sup of the single fixed background carrier
`loweredCovGradDeTurckVFMixed g₀ g₀ g₀ g₀ g_bg`
(`exists_bound_riemannianFiberNormSq_smoothCcTensor`); the order-`0` family value sup is the posited
fibre sup `exists_riemannianFiberNormSq_loweredCovGradDeTurckVFMixed_connSlot_diff_fibre_sup_le`; and
the integrated jet clause rewrites the carrier difference to the connection-difference action section
`connDiffActionSection g₀ g₁ g₀ g_bg`
(`loweredCovGradDeTurckVFMixed_connSlot_sub_eq_connDiffActionSection`) and reads the posited
contraction jet engine `exists_iteratedCovGrad_connDiffActionSection_connSlot_hamiltonTame_le`. -/
theorem loweredCovGradDeTurckVFMixed_connSlot_iteratedCovGrad_hamiltonTame_le
    (g₀ g_bg : SmoothRiemannianMetric I M)
    (a : ℕ) (ha : 2 * a > Module.finrank ℝ E + 4)
    (B : ℝ) (hB : 0 ≤ B) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1 / 2) (l : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      (∀ x : M,
        Integral.Connection.riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
          ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l
              (loweredCovGradDeTurckVFMixed (I := I) g₀ g₀ g₀ g₀ g_bg)).toSection x) ≤ C ^ 2) ∧
      ∀ (T₁ : Integral.L2.SmoothCcTensor g₀ 0 2) (g₁ : SmoothRiemannianMetric I M),
        (∀ (x : M) (v w : TangentSpace I x),
          g₁.inner x v w = g₀.inner x v w + ccTensorBilinSymm (I := I) g₀ T₁ x v w) →
        gFibreOpBound (I := I) g₀ (fun y => ccTensorBilinSymm (I := I) g₀ T₁ y) δ →
        ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (a + 2) T₁‖ ≤ B →
          (∀ x : M,
            Integral.Connection.riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x
              ((loweredCovGradDeTurckVFMixed (I := I) g₀ g₀ g₁ g₁ g_bg
                  - loweredCovGradDeTurckVFMixed (I := I) g₀ g₀ g₀ g₁ g_bg).toSection x) ≤
                C ^ 2) ∧
          ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l
              (loweredCovGradDeTurckVFMixed (I := I) g₀ g₀ g₁ g₁ g_bg
                - loweredCovGradDeTurckVFMixed (I := I) g₀ g₀ g₀ g₁ g_bg)‖ ^ 2 ≤
            C * ∑ i ∈ Finset.range (l + 3),
              ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i T₁‖ ^ 2 := by
  classical
  obtain ⟨K₁, hK₁0, hK₁⟩ :=
    exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ 0 (2 + l)
      (PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l
        (loweredCovGradDeTurckVFMixed (I := I) g₀ g₀ g₀ g₀ g_bg))
  obtain ⟨Λ, hΛ0, hΛ⟩ :=
    exists_riemannianFiberNormSq_loweredCovGradDeTurckVFMixed_connSlot_diff_fibre_sup_le
      (I := I) g₀ g_bg δ hδ0 hδ1 B a ha
  obtain ⟨C₃, hC₃0, hC₃⟩ :=
    exists_iteratedCovGrad_connDiffActionSection_connSlot_hamiltonTame_le
      (I := I) g₀ g_bg δ hδ0 hδ1 B a ha l
  refine ⟨Real.sqrt K₁ + Λ + C₃, by positivity, ?_, ?_⟩
  · intro x
    refine le_trans (hK₁ x) ?_
    have hsq : Real.sqrt K₁ ^ 2 = K₁ := Real.sq_sqrt hK₁0
    have hnn : (0 : ℝ) ≤ Real.sqrt K₁ := Real.sqrt_nonneg _
    nlinarith [hsq, Real.sqrt_nonneg K₁, hΛ0, hC₃0, sq_nonneg (Λ + C₃),
      mul_nonneg hnn (add_nonneg hΛ0 hC₃0)]
  · intro T₁ g₁ hg₁ hδbnd hB₁
    refine ⟨?_, ?_⟩
    · intro x
      refine le_trans (hΛ T₁ g₁ hg₁ hδbnd hB₁ x) ?_
      have hnn : (0 : ℝ) ≤ Real.sqrt K₁ := Real.sqrt_nonneg _
      nlinarith [Real.sqrt_nonneg K₁, hΛ0, hC₃0, sq_nonneg (Real.sqrt K₁ + C₃),
        mul_nonneg hΛ0 (add_nonneg hnn hC₃0)]
    · have hSnn : (0 : ℝ) ≤ ∑ i ∈ Finset.range (l + 3),
          ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i T₁‖ ^ 2 :=
        Finset.sum_nonneg fun i _ => sq_nonneg _
      rw [loweredCovGradDeTurckVFMixed_connSlot_sub_eq_connDiffActionSection (I := I) g₀ g₁ g_bg]
      refine le_trans (hC₃ T₁ g₁ hg₁ hδbnd hB₁) ?_
      have hCle : C₃ ≤ Real.sqrt K₁ + Λ + C₃ := by
        have : (0 : ℝ) ≤ Real.sqrt K₁ + Λ := by positivity
        linarith
      exact mul_le_mul_of_nonneg_right hCle hSnn

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization in
set_option linter.unusedSectionVars false in
/-- **(POSIT — the family-uniform order-`0` fibre sup of the field-slot carrier difference.)**
For the fibre-small (`gFibreOpBound g₀ (ccTensorBilinSymm g₀ T₁) δ`, `δ < 1/2`) supercritically
`H^{a+2}`-bounded (`2a > finrank + 4`) realized perturbation family, the order-`0` intrinsic squared
fibre norm of the field-slot carrier difference
`loweredCovGradDeTurckVFMixed g₀ g₀ g₀ g₁ g_bg − loweredCovGradDeTurckVFMixed g₀ g₀ g₀ g₀ g_bg`
— equal by `loweredCovGradDeTurckVFMixed_fldSlot_sub_eq_fieldDiffGradSection` to the
field-difference gradient section `fieldDiffGradSection g₀ g₁ g₀ g_bg`, fibre
`g₀(∇^{g₀}_v (W₁ − W₀), w)`, `Wᵢ = deTurckVF gᵢ g_bg` — is uniformly bounded by a single
constant `Λ²` over the manifold and the family.

The order-`0` fibre value is the `g₀`-inner of the `g₀`-Levi-Civita covariant gradient of the
field difference `W₁ − W₀`; the field difference is the inverse-Gram-weighted trace of the pair
connection difference (`deTurckVF_sub_apply_eq_trace_connDiff`), whose connection-difference fibre
sup is the Neumann-absorbed supercritical-`C¹` bound, so the covariant gradient of the field
difference has a family-uniform order-`0` sup.  Vanishes at `T₁ = 0` realized (`g₁ = g₀`, the
difference is the zero section).  Body `sorry`: a posited deep order-`0` family fibre sup of the
field-slot carrier difference. -/
theorem exists_riemannianFiberNormSq_loweredCovGradDeTurckVFMixed_fldSlot_diff_fibre_sup_le
    (g₀ g_bg : SmoothRiemannianMetric I M) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1 / 2) (B : ℝ)
    (a : ℕ) (ha : 2 * a > Module.finrank ℝ E + 4) :
    ∃ Λ : ℝ, 0 ≤ Λ ∧
      ∀ (T₁ : Integral.L2.SmoothCcTensor g₀ 0 2) (g₁ : SmoothRiemannianMetric I M),
        (∀ (x : M) (v w : TangentSpace I x),
          g₁.inner x v w = g₀.inner x v w + ccTensorBilinSymm (I := I) g₀ T₁ x v w) →
        gFibreOpBound (I := I) g₀ (fun y => ccTensorBilinSymm (I := I) g₀ T₁ y) δ →
        ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (a + 2) T₁‖ ≤ B →
        ∀ x : M,
          Integral.Connection.riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x
            ((loweredCovGradDeTurckVFMixed (I := I) g₀ g₀ g₀ g₁ g_bg
                - loweredCovGradDeTurckVFMixed (I := I) g₀ g₀ g₀ g₀ g_bg).toSection x) ≤ Λ ^ 2 :=
  sorry

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization in
set_option linter.unusedSectionVars false in
/-- **(POSIT — the family-uniform integrated Hamilton-tame jet bound of the field-difference
gradient section.)**  For the fibre-small (`gFibreOpBound g₀ (ccTensorBilinSymm g₀ T₁) δ`, `δ < 1/2`)
supercritically `H^{a+2}`-bounded realized perturbation family, the order-`l` covariant-jet `L²`
norm of the field-difference gradient section `fieldDiffGradSection g₀ g₁ g₀ g_bg` (fibre
`g₀(∇^{g₀}_v (W₁ − W₀), w)`, `Wᵢ = deTurckVF gᵢ g_bg`) is dominated by the `≤ (l+2)`-jet of the
perturbation `T₁`:
```
‖∇^l (fieldDiffGradSection g₀ g₁ g₀ g_bg)‖² ≤ C · ∑_{i ∈ range(l+3)} ‖∇^i T₁‖².
```

The section is the `g₀`-lowered `g₀`-Levi-Civita covariant gradient of the field difference
`W₁ − W₀`, which is the inverse-Gram-weighted trace of the pair connection difference
`connDiff g₁ g₀` (`deTurckVF_sub_apply_eq_trace_connDiff`), again connDiff-driven and
realized-Koszul in `T₁`.  The covariant-Leibniz expansion of the lowered covariant gradient reads
the order-`l` jet of the section as a binomial-weighted sum of the covariant jets of the lowered
connection difference (`i ≤ l+1`, folded into the `≤ (i+1)`-jet of `T₁` by the connection-difference
jet engine `exists_riemannianFiberNormSq_iteratedCovGrad_loweredConnDiff_le_jetSum`) against the
bounded jets of the smooth inverse-Gram trace weights, so the whole order-`l` jet is Hamilton-tame
in the `≤ (l+2)`-jet of `T₁` with a family-uniform constant.  Vanishes at `T₁ = 0` realized
(`g₁ = g₀`, `W₁ − W₀ = 0`, the section is the zero section).  Body `sorry`: a posited deep
covariant-Leibniz field-difference jet engine. -/
theorem exists_iteratedCovGrad_fieldDiffGradSection_fldSlot_hamiltonTame_le
    (g₀ g_bg : SmoothRiemannianMetric I M) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1 / 2) (B : ℝ)
    (a : ℕ) (ha : 2 * a > Module.finrank ℝ E + 4) (l : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (T₁ : Integral.L2.SmoothCcTensor g₀ 0 2) (g₁ : SmoothRiemannianMetric I M),
        (∀ (x : M) (v w : TangentSpace I x),
          g₁.inner x v w = g₀.inner x v w + ccTensorBilinSymm (I := I) g₀ T₁ x v w) →
        gFibreOpBound (I := I) g₀ (fun y => ccTensorBilinSymm (I := I) g₀ T₁ y) δ →
        ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (a + 2) T₁‖ ≤ B →
        ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l
              (fieldDiffGradSection (I := I) g₀ g₁ g₀ g_bg)‖ ^ 2 ≤
          C * ∑ i ∈ Finset.range (l + 3),
            ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i T₁‖ ^ 2 :=
  sorry

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization in
set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
/-- **(The field-slot single-leg Hamilton-tame jet bound — glued.)**  The field-slot leg of
the `g₀`-lowered mixed DeTurck-gradient carrier difference: only the DeTurck field metric is
varied `g₀ → g₁` (lowering and connection both fixed at `g₀`).  The carrier is
`loweredCovGradDeTurckVFMixed g₀ g₀ g₀ g₁ g_bg − loweredCovGradDeTurckVFMixed g₀ g₀ g₀ g₀ g_bg`,
whose fibre is the field-difference contraction `g₀(∇^{g₀}_v (W₁ − W₀), w)`,
`Wᵢ = deTurckVF gᵢ g_bg`.  Same three-clause shape as the diagonal node: a background jet sup of
the fixed background carrier, an order-`0` value sup, and an integrated Hamilton-tame bound
`≤ C · ∑_{i ∈ range(l+3)} ‖∇^i T₁‖²`.

Glued (consumers transitively depend on `sorryAx` only through the two posited children below):
the background clause is the pointwise jet sup of the single fixed background carrier
`loweredCovGradDeTurckVFMixed g₀ g₀ g₀ g₀ g_bg`
(`exists_bound_riemannianFiberNormSq_smoothCcTensor`); the order-`0` family value sup is the posited
fibre sup `exists_riemannianFiberNormSq_loweredCovGradDeTurckVFMixed_fldSlot_diff_fibre_sup_le`; and
the integrated jet clause rewrites the carrier difference to the field-difference gradient section
`fieldDiffGradSection g₀ g₁ g₀ g_bg`
(`loweredCovGradDeTurckVFMixed_fldSlot_sub_eq_fieldDiffGradSection`) and reads the posited
field-difference jet engine `exists_iteratedCovGrad_fieldDiffGradSection_fldSlot_hamiltonTame_le`. -/
theorem loweredCovGradDeTurckVFMixed_fldSlot_iteratedCovGrad_hamiltonTame_le
    (g₀ g_bg : SmoothRiemannianMetric I M)
    (a : ℕ) (ha : 2 * a > Module.finrank ℝ E + 4)
    (B : ℝ) (hB : 0 ≤ B) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1 / 2) (l : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      (∀ x : M,
        Integral.Connection.riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
          ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l
              (loweredCovGradDeTurckVFMixed (I := I) g₀ g₀ g₀ g₀ g_bg)).toSection x) ≤ C ^ 2) ∧
      ∀ (T₁ : Integral.L2.SmoothCcTensor g₀ 0 2) (g₁ : SmoothRiemannianMetric I M),
        (∀ (x : M) (v w : TangentSpace I x),
          g₁.inner x v w = g₀.inner x v w + ccTensorBilinSymm (I := I) g₀ T₁ x v w) →
        gFibreOpBound (I := I) g₀ (fun y => ccTensorBilinSymm (I := I) g₀ T₁ y) δ →
        ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (a + 2) T₁‖ ≤ B →
          (∀ x : M,
            Integral.Connection.riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x
              ((loweredCovGradDeTurckVFMixed (I := I) g₀ g₀ g₀ g₁ g_bg
                  - loweredCovGradDeTurckVFMixed (I := I) g₀ g₀ g₀ g₀ g_bg).toSection x) ≤
                C ^ 2) ∧
          ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l
              (loweredCovGradDeTurckVFMixed (I := I) g₀ g₀ g₀ g₁ g_bg
                - loweredCovGradDeTurckVFMixed (I := I) g₀ g₀ g₀ g₀ g_bg)‖ ^ 2 ≤
            C * ∑ i ∈ Finset.range (l + 3),
              ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i T₁‖ ^ 2 := by
  classical
  obtain ⟨K₁, hK₁0, hK₁⟩ :=
    exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ 0 (2 + l)
      (PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l
        (loweredCovGradDeTurckVFMixed (I := I) g₀ g₀ g₀ g₀ g_bg))
  obtain ⟨Λ, hΛ0, hΛ⟩ :=
    exists_riemannianFiberNormSq_loweredCovGradDeTurckVFMixed_fldSlot_diff_fibre_sup_le
      (I := I) g₀ g_bg δ hδ0 hδ1 B a ha
  obtain ⟨C₃, hC₃0, hC₃⟩ :=
    exists_iteratedCovGrad_fieldDiffGradSection_fldSlot_hamiltonTame_le
      (I := I) g₀ g_bg δ hδ0 hδ1 B a ha l
  refine ⟨Real.sqrt K₁ + Λ + C₃, by positivity, ?_, ?_⟩
  · intro x
    refine le_trans (hK₁ x) ?_
    have hsq : Real.sqrt K₁ ^ 2 = K₁ := Real.sq_sqrt hK₁0
    have hnn : (0 : ℝ) ≤ Real.sqrt K₁ := Real.sqrt_nonneg _
    nlinarith [hsq, Real.sqrt_nonneg K₁, hΛ0, hC₃0, sq_nonneg (Λ + C₃),
      mul_nonneg hnn (add_nonneg hΛ0 hC₃0)]
  · intro T₁ g₁ hg₁ hδbnd hB₁
    refine ⟨?_, ?_⟩
    · intro x
      refine le_trans (hΛ T₁ g₁ hg₁ hδbnd hB₁ x) ?_
      have hnn : (0 : ℝ) ≤ Real.sqrt K₁ := Real.sqrt_nonneg _
      nlinarith [Real.sqrt_nonneg K₁, hΛ0, hC₃0, sq_nonneg (Real.sqrt K₁ + C₃),
        mul_nonneg hΛ0 (add_nonneg hnn hC₃0)]
    · have hSnn : (0 : ℝ) ≤ ∑ i ∈ Finset.range (l + 3),
          ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i T₁‖ ^ 2 :=
        Finset.sum_nonneg fun i _ => sq_nonneg _
      rw [loweredCovGradDeTurckVFMixed_fldSlot_sub_eq_fieldDiffGradSection (I := I) g₀ g₁ g_bg]
      refine le_trans (hC₃ T₁ g₁ hg₁ hδbnd hB₁) ?_
      have hCle : C₃ ≤ Real.sqrt K₁ + Λ + C₃ := by
        have : (0 : ℝ) ≤ Real.sqrt K₁ + Λ := by positivity
        linarith
      exact mul_le_mul_of_nonneg_right hCle hSnn

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization in
set_option linter.unusedSectionVars false in
/-- **(POSIT — the family-uniform Hamilton-tame jet engine of the `g₀`-lowered mixed
DeTurck-gradient carrier.)**  For an anchor `g₀`, a flow background `g_bg`, a supercritical order
`a` (`2a > dim + 4`), a family bound `B`, fibre-smallness `δ < 1/2`, and a gradient order `l`,
there is one constant `C = C(g₀, g_bg, a, B, δ, l) ≥ 0` such that

* (**background jet sup**) the FIXED background carrier
  `F_bg := loweredCovGradDeTurckVFMixed g₀ g₀ g₀ g₀ g_bg` (the `g₀`-lowering of
  `∇^{g₀} (deTurckVF g₀ g_bg)`, no perturbation) has its order-`l` covariant jet pointwise
  bounded: `rfns(∇^l F_bg)(x) ≤ C²` — a single smooth section on the compact manifold, all
  orders legitimate (NOT a family bound); and

* for every realized fibre-small perturbation `(T₁, g₁)` of the family, the
  **background-subtracted** carrier
  `F(g₁) − F_bg`, `F(g₁) := loweredCovGradDeTurckVFMixed g₀ g₀ g₁ g₁ g_bg` (the `g₀`-lowering
  of `∇^{g₁} (deTurckVF g₁ g_bg)`), satisfies
  - (**value sup**) the order-`0` family-uniform `C⁰` fibre bound
    `rfns(F(g₁) − F_bg)(x) ≤ C²` (supercritical `C²`-control of the metric jet, order `0`
    ONLY — pointwise family bounds on `≥ 1`-jets are refuted and not stated); and
  - (**integrated Hamilton-tame jet bound**)
    `‖∇^l (F(g₁) − F_bg)‖² ≤ C · ∑_{i ≤ l+2} ‖∇^i T₁‖²` — the carrier difference is a
    realized-Koszul second-order contraction of the `T₁`-jet (the carrier is second-order in the
    metric), so its order-`l` jet carries at most the order-`(l+2)` jets of `T₁`, with a
    family-uniform Hamilton-tame constant.

The carrier is `g₀`-LOWERED (`g_low = g₀`): the consumer extracts the raw covariant gradient
`∇^{g₁} W₁` from the carrier through the `g₀`-cometric trace, which is the unique
`∇^{g₀}`-parallel un-lowering (a `g₁`-lowered carrier is not parallel-recoverable).  The
background subtraction is forced by the frozen two-arm shape of the consumer
`deTurckVFLoweringSlotDiff_iteratedCovGrad_twoArm_le`: the unsubtracted carrier retains the
`T₁`-independent background mass `∇ W(g₀)`, whose Gagliardo–Nirenberg cross arm would produce a
bare `‖(T₁ − T₂).toHs a‖²` term with no fixed-pair jet factor, refuted against the frozen
target by the antisymmetric-perturbation family (`T₁ = εA`, `A` antisymmetric, `T₂ = 0`:
realized metrics coincide, LHS `= 0`, but the bare term survives).

Vanishes at `T₁ = 0` realized (`g₁ = g₀`, both family clauses `0 ≤ ·`); non-vacuous: the
background clause carries the genuine nonzero gauge field `∇ (deTurckVF g₀ g_bg)` and the family
clauses carry the full first-order Koszul content of the carrier difference.  Its body is
`sorry`: a posited deep child (consumers transitively depend on `sorryAx`), the
lowering-slot engine of the GN-product two-arm assembly. -/
theorem loweredCovGradDeTurckVFMixed_diag_iteratedCovGrad_hamiltonTame_le
    (g₀ g_bg : SmoothRiemannianMetric I M)
    (a : ℕ) (ha : 2 * a > Module.finrank ℝ E + 4)
    (B : ℝ) (hB : 0 ≤ B) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1 / 2) (l : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      (∀ x : M,
        Integral.Connection.riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
          ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l
              (loweredCovGradDeTurckVFMixed (I := I) g₀ g₀ g₀ g₀ g_bg)).toSection x) ≤ C ^ 2) ∧
      ∀ (T₁ : Integral.L2.SmoothCcTensor g₀ 0 2) (g₁ : SmoothRiemannianMetric I M),
        (∀ (x : M) (v w : TangentSpace I x),
          g₁.inner x v w = g₀.inner x v w + ccTensorBilinSymm (I := I) g₀ T₁ x v w) →
        gFibreOpBound (I := I) g₀ (fun y => ccTensorBilinSymm (I := I) g₀ T₁ y) δ →
        ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (a + 2) T₁‖ ≤ B →
          (∀ x : M,
            Integral.Connection.riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x
              ((loweredCovGradDeTurckVFMixed (I := I) g₀ g₀ g₁ g₁ g_bg
                  - loweredCovGradDeTurckVFMixed (I := I) g₀ g₀ g₀ g₀ g_bg).toSection x) ≤
                C ^ 2) ∧
          ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l
              (loweredCovGradDeTurckVFMixed (I := I) g₀ g₀ g₁ g₁ g_bg
                - loweredCovGradDeTurckVFMixed (I := I) g₀ g₀ g₀ g₀ g_bg)‖ ^ 2 ≤
            C * ∑ i ∈ Finset.range (l + 3),
              ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i T₁‖ ^ 2 := by
  classical
  obtain ⟨C_A, hCA_nn, hbgA, hfamA⟩ :=
    loweredCovGradDeTurckVFMixed_connSlot_iteratedCovGrad_hamiltonTame_le
      (I := I) g₀ g_bg a ha B hB δ hδ0 hδ1 l
  obtain ⟨C_B, hCB_nn, _hbgB, hfamB⟩ :=
    loweredCovGradDeTurckVFMixed_fldSlot_iteratedCovGrad_hamiltonTame_le
      (I := I) g₀ g_bg a ha B hB δ hδ0 hδ1 l
  refine ⟨2 * (C_A + C_B) + 1, by positivity, ?_, ?_⟩
  · intro x
    refine le_trans (hbgA x) ?_
    have hle : C_A ≤ 2 * (C_A + C_B) + 1 := by nlinarith
    nlinarith [sq_nonneg C_A, sq_nonneg (2 * (C_A + C_B) + 1 - C_A)]
  · intro T₁ g₁ hg₁ hδbnd hB₁
    obtain ⟨hvalA, hintA⟩ := hfamA T₁ g₁ hg₁ hδbnd hB₁
    obtain ⟨hvalB, hintB⟩ := hfamB T₁ g₁ hg₁ hδbnd hB₁
    set cA : Integral.L2.SmoothCcTensor g₀ 0 2 :=
      loweredCovGradDeTurckVFMixed (I := I) g₀ g₀ g₁ g₁ g_bg
        - loweredCovGradDeTurckVFMixed (I := I) g₀ g₀ g₀ g₁ g_bg with hcA
    set cB : Integral.L2.SmoothCcTensor g₀ 0 2 :=
      loweredCovGradDeTurckVFMixed (I := I) g₀ g₀ g₀ g₁ g_bg
        - loweredCovGradDeTurckVFMixed (I := I) g₀ g₀ g₀ g₀ g_bg with hcB
    have hPsum : loweredCovGradDeTurckVFMixed (I := I) g₀ g₀ g₁ g₁ g_bg
        - loweredCovGradDeTurckVFMixed (I := I) g₀ g₀ g₀ g₀ g_bg = cA + cB := by
      rw [hcA, hcB]; abel
    have hSnn : (0 : ℝ) ≤ ∑ i ∈ Finset.range (l + 3),
        ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i T₁‖ ^ 2 :=
      Finset.sum_nonneg fun i _ => sq_nonneg _
    refine ⟨?_, ?_⟩
    · intro x
      rw [hPsum, Integral.L2.SmoothCcTensor.toSection_add]
      refine le_trans
        (Integral.Connection.riemannianFiberNormSq_add_le (I := I) g₀ 0 2 x
          (cA.toSection x) (cB.toSection x)) ?_
      have hA' := hvalA x
      have hB' := hvalB x
      nlinarith [hA', hB', hCA_nn, hCB_nn, sq_nonneg (C_A + C_B), sq_nonneg (C_A - C_B)]
    · rw [hPsum, PDE.RicciFlow.iteratedCovGrad_add]
      refine le_trans (sq_le_sq' ?_ (norm_add_le _ _)) ?_
      · have := norm_nonneg
          (PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l cA
            + PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l cB)
        nlinarith [norm_nonneg (PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l cA),
          norm_nonneg (PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l cB)]
      · refine le_trans (add_sq_le_two_mul_sq_add_sq _ _) ?_
        have hAi : ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l cA‖ ^ 2 ≤
            C_A * ∑ i ∈ Finset.range (l + 3),
              ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i T₁‖ ^ 2 := hintA
        have hBi : ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l cB‖ ^ 2 ≤
            C_B * ∑ i ∈ Finset.range (l + 3),
              ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i T₁‖ ^ 2 := hintB
        nlinarith [hAi, hBi, hSnn, hCA_nn, hCB_nn]

end Pullback
end RicciFlow
end PDE
end DifferentialGeometry

end
