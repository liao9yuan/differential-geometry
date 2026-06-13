import DifferentialGeometry.Geometry.Connection.TensorNabla.VectorFieldCovariantGradientSection
import DifferentialGeometry.Geometry.Connection.TensorNabla.DeTurckVFIntrinsicValueBound
import DifferentialGeometry.Geometry.Connection.TensorNabla.VectorFieldCovariantGradientDifference
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CrossCorrectionParallelContraction
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.DeTurckVFCovariantJetBound

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
/-- **The Hilbert–Schmidt frame reduction of a `(0,2)` fibre norm from a pointwise `g₀`-Cauchy–Schwarz
value bound.**  If the extracted bilinear form `ccTensorBilin g₀ S x` of a smooth `(0,2)`-tensor
section `S` obeys the pointwise `g₀`-Cauchy–Schwarz value bound
`|ccTensorBilin g₀ S x v w| ≤ Λ₀ · √(g₀ x v v) · √(g₀ x w w)` for all `v, w`, then the intrinsic
squared Riemannian fibre norm of `S` at `x` is bounded by `(finrank · Λ₀)²`.  Proved by expanding the
fibre norm in a `g₀`-orthonormal tangent frame `e`
(`exists_orthonormal_frame_riemannianFiberNormSq`), identifying each frame component with the
bilinear value at the unit frame vectors (`ccTensorBilin_eq_fiberNormSqComponent`, where
`√(g₀ x (e j) (e j)) = √1 = 1`), and counting the `finrank²` frame-pair summands.  This is the pure
fibre-algebra bridge by which a `C⁰` value bound on the first-order metric carrier yields the
order-`0` Riemannian fibre sup. -/
theorem rfns_le_of_ccTensorBilin_gcs_bound
    (g₀ : SmoothRiemannianMetric I M) (S : Integral.L2.SmoothCcTensor g₀ 0 2)
    (x : M) (Λ₀ : ℝ) (_hΛ₀ : 0 ≤ Λ₀)
    (hbound : ∀ v w : TangentSpace I x,
      |ccTensorBilin (I := I) g₀ S x v w| ≤
        Λ₀ * Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x w w)) :
    Integral.Connection.riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x (S.toSection x) ≤
      (Module.finrank ℝ E * Λ₀) ^ 2 := by
  classical
  obtain ⟨n, e, hn, horth, _hpars, hrepr⟩ :=
    Integral.Connection.exists_orthonormal_frame_riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x
  set K₀ : Fin 0 → Fin n := fun k => k.elim0 with hK₀
  rw [Integral.Connection.riemannianFiberNormSq_eq_sum_componentS_sq (I := I) (M := M) g₀ x 2 e
      hrepr (S.toSection x) K₀]
  have hcomp_le : ∀ J : Fin 2 → Fin n,
      (Integral.Connection.fiberNormSqComponent (I := I) (M := M) g₀ x 0 2
        (S.toSection x) n e K₀ J) ^ 2 ≤ Λ₀ ^ 2 := by
    intro J
    rw [ccTensorBilin_eq_fiberNormSqComponent (I := I) g₀ S x e K₀ J]
    have hjj : ∀ j : Fin n, Real.sqrt (g₀.inner x (e j) (e j)) = 1 := by
      intro j
      have hjj1 : g₀.inner x (e j) (e j) = 1 := by simpa using horth j j
      rw [hjj1, Real.sqrt_one]
    have hb := hbound (e (J 0)) (e (J 1))
    rw [hjj (J 0), hjj (J 1)] at hb
    have hb' : |ccTensorBilin (I := I) g₀ S x (e (J 0)) (e (J 1))| ≤ Λ₀ := by simpa using hb
    exact sq_le_sq' (neg_le_of_abs_le hb') (le_of_abs_le hb')
  calc (∑ J : Fin 2 → Fin n,
          (Integral.Connection.fiberNormSqComponent (I := I) (M := M) g₀ x 0 2
            (S.toSection x) n e K₀ J) ^ 2)
        ≤ ∑ _J : Fin 2 → Fin n, Λ₀ ^ 2 := Finset.sum_le_sum (fun J _ => hcomp_le J)
    _ = (Fintype.card (Fin 2 → Fin n) : ℝ) * Λ₀ ^ 2 := by
          rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
    _ = (n : ℝ) ^ 2 * Λ₀ ^ 2 := by
          rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]; push_cast; ring
    _ = (Module.finrank ℝ E * Λ₀) ^ 2 := by
          have hnE : n = Module.finrank ℝ E := hn
          rw [hnE]; ring


/-! ### Bedrock value algebra for the connection-difference operator bound -/

set_option linter.unusedSectionVars false in
/-- **The `g₀`-self-norm Riesz lift.**  If a vector `z` has its `g₀`-pairing against every direction
`c` bounded by `K · √(g₀ c c)`, then its `g₀`-self-norm is bounded by `K`.  Tested at `c = z`:
`g₀(z, z) ≤ K · √(g₀ z z)` and `g₀(z, z) = √(g₀ z z)²` give `√(g₀ z z) ≤ K` (or `√(g₀ z z) = 0`). -/
private theorem sqrt_gInner_self_le_of_forall_inner_le
    (g₀ : SmoothRiemannianMetric I M) (x : M) (z : TangentSpace I x) {K : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ c : TangentSpace I x, |g₀.inner x z c| ≤ K * Real.sqrt (g₀.inner x c c)) :
    Real.sqrt (g₀.inner x z z) ≤ K := by
  have hzz_nn : 0 ≤ g₀.inner x z z :=
    DifferentialGeometry.Analysis.Laplacian.metric_inner_self_nonneg (I := I) (M := M) g₀ x z
  have hsq : Real.sqrt (g₀.inner x z z) * Real.sqrt (g₀.inner x z z) = g₀.inner x z z := by
    rw [← Real.sqrt_mul hzz_nn, Real.sqrt_mul_self hzz_nn]
  have hzz : g₀.inner x z z ≤ K * Real.sqrt (g₀.inner x z z) := by
    have h := hK z
    have hle : g₀.inner x z z ≤ |g₀.inner x z z| := le_abs_self _
    exact le_trans hle h
  rcases eq_or_lt_of_le (Real.sqrt_nonneg (g₀.inner x z z)) with hzero | hpos
  · rw [← hzero]; exact hK0
  · have hsqz : Real.sqrt (g₀.inner x z z) * Real.sqrt (g₀.inner x z z) ≤
        K * Real.sqrt (g₀.inner x z z) := by rw [hsq]; exact hzz
    exact le_of_mul_le_mul_right (by linarith [hsqz]) hpos

set_option linter.unusedSectionVars false in
/-- **The rank-`(0,3)` `g₀`-fibre Cauchy–Schwarz for a model `(0,3)`-form.**  For a `(0,3)`-fibre
value `S : Tensor0SSpace 3 I x`, the absolute model evaluation `|toModel S ![a, b, c]|` is bounded by
the square root of the `(0,3)` Riemannian fibre-norm-squared of the unit-section value times the
`g₀`-quadratic factors of the three directions.  Proved by expanding `a, b, c` in a `g₀`-orthonormal
frame, applying the triple Cauchy–Schwarz over the frame-triple index, and Parseval
`∑_i (g₀ x (e i) v)² = g₀ x v v`, identifying the frame-triple square-sum with the `(0,3)` fibre norm
through `fiberNormSqComponent` and `riemannianFiberNormSq_eq_sum_componentS_sq`. -/
private theorem abs_toModel_three_le_sqrt_rfns
    (g₀ : SmoothRiemannianMetric I M) (x : M)
    (Sec : Integral.L2.SmoothCcTensor g₀ 0 3) (a b c : TangentSpace I x) :
    |Tensor0SBundle.Tensor0SSpace.toModel (Sec.toSection x
        (ContinuousMultilinearMap.constOfIsEmpty ℝ
          (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))) ![a, b, c]| ≤
      Real.sqrt (Integral.Connection.riemannianFiberNormSq (I := I) (M := M) g₀ 0 3 x
          (Sec.toSection x)) *
        Real.sqrt (g₀.inner x a a) *
        Real.sqrt (g₀.inner x b b) * Real.sqrt (g₀.inner x c c) := by
  classical
  obtain ⟨n, e, hn, horth, hpars, hexpand, _hrepr2⟩ :=
    Integral.Connection.tangent_frame_expansion (I := I) (M := M) g₀ x
  have hrepr : ∀ (S : Tensor0SBundle.TensorRSSpace 0 3 I x),
      Integral.Connection.riemannianFiberNormSq (I := I) (M := M) g₀ 0 3 x S =
        ∑ K, ∑ J, Integral.Connection.fiberNormSqSummand (I := I) (M := M) g₀ x 0 3 S n e K J := by
    intro S
    exact Integral.Connection.rfns_eq_sum_fiberNormSqSummand_of_orthoFrame (I := I) (M := M)
      g₀ 3 x S e hn horth
  set K₀ : Fin 0 → Fin n := fun k => k.elim0 with hK₀
  -- The model value of the unit-evaluated section equals the frame component when read at the frame.
  have hcomp_eq : ∀ J : Fin 3 → Fin n,
      Integral.Connection.fiberNormSqComponent (I := I) (M := M) g₀ x 0 3
          (Sec.toSection x) n e K₀ J =
        Tensor0SBundle.Tensor0SSpace.toModel (Sec.toSection x
          (ContinuousMultilinearMap.constOfIsEmpty ℝ
            (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ)))
          ![e (J 0), e (J 1), e (J 2)] := by
    intro J
    have hcoframe :
        (ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 0) ℝ).compContinuousLinearMap
            (fun k => g₀.inner x (e (K₀ k))) =
          ContinuousMultilinearMap.constOfIsEmpty ℝ
            (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ) := by
      apply ContinuousMultilinearMap.ext
      intro v
      rw [ContinuousMultilinearMap.compContinuousLinearMap_apply,
        ContinuousMultilinearMap.mkPiAlgebra_apply, Finset.prod_of_isEmpty]
      rfl
    unfold Integral.Connection.fiberNormSqComponent
    rw [hcoframe]
    rw [Tensor0SBundle.Tensor0SSpace.toModel,
      Tensor0SBundle.tensor0SSpace_continuousLinearEquiv_apply]
    congr 1
    funext k
    fin_cases k <;> rfl
  -- The model value expands over the frame triples `J : Fin 3 → Fin n`.
  set σ := Sec.toSection x
    (ContinuousMultilinearMap.constOfIsEmpty ℝ
      (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ)) with hσ
  set B : ℝ := Tensor0SBundle.Tensor0SSpace.toModel σ ![a, b, c] with hB_def
  set abc : Fin 3 → TangentSpace I x := ![a, b, c] with habc
  set Tval : (Fin 3 → Fin n) → ℝ := fun J =>
    Tensor0SBundle.Tensor0SSpace.toModel σ (fun t => e (J t)) with hT_def
  set cf : (Fin 3 → Fin n) → ℝ := fun J =>
    ∏ t : Fin 3, g₀.inner x (e (J t)) (abc t) with hcf_def
  -- `toModel σ` is a continuous multilinear map; expand each slot in the frame via `map_sum`.
  have hexp : B = ∑ J : Fin 3 → Fin n, cf J * Tval J := by
    have hcong : abc = (fun t : Fin 3 => ∑ i : Fin n, g₀.inner x (e i) (abc t) • e i) := by
      funext t; exact hexpand (abc t)
    have hmap := (Tensor0SBundle.Tensor0SSpace.toModel σ).map_sum_finset
      (fun (t : Fin 3) (i : Fin n) => g₀.inner x (e i) (abc t) • e i)
    rw [hB_def]
    calc Tensor0SBundle.Tensor0SSpace.toModel σ abc
        = Tensor0SBundle.Tensor0SSpace.toModel σ
            (fun t : Fin 3 => ∑ i : Fin n, g₀.inner x (e i) (abc t) • e i) := by rw [← hcong]
      _ = ∑ J ∈ Fintype.piFinset (fun _ : Fin 3 => (Finset.univ : Finset (Fin n))),
            Tensor0SBundle.Tensor0SSpace.toModel σ
              (fun t => g₀.inner x (e (J t)) (abc t) • e (J t)) :=
            hmap (fun _ : Fin 3 => (Finset.univ : Finset (Fin n)))
      _ = ∑ J : Fin 3 → Fin n, cf J * Tval J := by
            rw [Fintype.piFinset_univ]
            refine Finset.sum_congr rfl (fun J _ => ?_)
            rw [hcf_def, hT_def]
            have hsmul := (Tensor0SBundle.Tensor0SSpace.toModel σ).toMultilinearMap.map_smul_univ
              (fun t : Fin 3 => g₀.inner x (e (J t)) (abc t)) (fun t : Fin 3 => e (J t))
            rw [ContinuousMultilinearMap.coe_coe] at hsmul
            rw [hsmul, smul_eq_mul]
  have hCS : (∑ J : Fin 3 → Fin n, cf J * Tval J) ^ 2 ≤
      (∑ J : Fin 3 → Fin n, cf J ^ 2) * ∑ J : Fin 3 → Fin n, Tval J ^ 2 :=
    Finset.sum_mul_sq_le_sq_mul_sq Finset.univ cf Tval
  -- The frame-factor square-sum is the product of the three g₀-quadratics.
  have hcfsq : (∑ J : Fin 3 → Fin n, cf J ^ 2) =
      g₀.inner x a a * g₀.inner x b b * g₀.inner x c c := by
    have hstep : (∑ J : Fin 3 → Fin n, cf J ^ 2) =
        ∏ t : Fin 3, ∑ i : Fin n, g₀.inner x (e i) (abc t) ^ 2 := by
      rw [Finset.prod_univ_sum (fun _ : Fin 3 => (Finset.univ : Finset (Fin n)))
        (fun (t : Fin 3) (i : Fin n) => g₀.inner x (e i) (abc t) ^ 2)]
      rw [Fintype.piFinset_univ]
      refine Finset.sum_congr rfl (fun J _ => ?_)
      rw [hcf_def, ← Finset.prod_pow]
    rw [hstep, Fin.prod_univ_three]
    have h0 : abc 0 = a := rfl
    have h1 : abc 1 = b := rfl
    have h2 : abc 2 = c := rfl
    rw [h0, h1, h2, hpars a, hpars b, hpars c]
  -- The frame-value square-sum is the (0,3) fibre norm.
  have hTsq : (∑ J : Fin 3 → Fin n, Tval J ^ 2) =
      Integral.Connection.riemannianFiberNormSq (I := I) (M := M) g₀ 0 3 x (Sec.toSection x) := by
    rw [Integral.Connection.riemannianFiberNormSq_eq_sum_componentS_sq (I := I) (M := M) g₀ x 3 e
      hrepr (Sec.toSection x) K₀]
    refine Finset.sum_congr rfl (fun J _ => ?_)
    have hfun : (fun t : Fin 3 => e (J t)) = ![e (J 0), e (J 1), e (J 2)] := by
      funext t; fin_cases t <;> rfl
    change (Tensor0SBundle.Tensor0SSpace.toModel σ (fun t : Fin 3 => e (J t))) ^ 2 =
      Integral.Connection.fiberNormSqComponent (I := I) (M := M) g₀ x 0 3
        (Sec.toSection x) n e K₀ J ^ 2
    rw [hfun, ← hcomp_eq J]
  -- Assemble the Cauchy–Schwarz into the square-root product bound.
  have hBsq : B ^ 2 ≤ g₀.inner x a a * g₀.inner x b b * g₀.inner x c c *
      Integral.Connection.riemannianFiberNormSq (I := I) (M := M) g₀ 0 3 x (Sec.toSection x) := by
    rw [hexp]
    refine hCS.trans ?_
    rw [hcfsq, hTsq]
  have hB_abs : |B| ≤ Real.sqrt (g₀.inner x a a * g₀.inner x b b * g₀.inner x c c *
      Integral.Connection.riemannianFiberNormSq (I := I) (M := M) g₀ 0 3 x (Sec.toSection x)) := by
    rw [show |B| = Real.sqrt (B ^ 2) from (Real.sqrt_sq_eq_abs B).symm]
    exact Real.sqrt_le_sqrt hBsq
  refine hB_abs.trans ?_
  have ha := DifferentialGeometry.Analysis.Laplacian.metric_inner_self_nonneg (I := I) (M := M) g₀ x a
  have hb := DifferentialGeometry.Analysis.Laplacian.metric_inner_self_nonneg (I := I) (M := M) g₀ x b
  have hc := DifferentialGeometry.Analysis.Laplacian.metric_inner_self_nonneg (I := I) (M := M) g₀ x c
  have hr := Integral.Connection.riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 3 x
    (Sec.toSection x)
  rw [show g₀.inner x a a * g₀.inner x b b * g₀.inner x c c *
        Integral.Connection.riemannianFiberNormSq (I := I) (M := M) g₀ 0 3 x (Sec.toSection x) =
      (Integral.Connection.riemannianFiberNormSq (I := I) (M := M) g₀ 0 3 x (Sec.toSection x)) *
        (g₀.inner x a a) * (g₀.inner x b b) * (g₀.inner x c c) from by ring]
  rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity)]

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization in
set_option linter.unusedSectionVars false in
/-- **The family-uniform `C⁰` value bound of the realized covariant-derivative `(0,3)`-evaluation.**
For the supercritically `H^{a + 2}`-bounded (`2a > finrank + 4`) perturbation family there is a single
constant `Φ ≥ 0` (depending on `g₀, a, B`, not on `T₁`) such that, whenever `‖T₁.toHs(a + 2)‖ ≤ B`,
the realized `(0,3)`-covariant-derivative evaluation obeys
`|covDerivRealizeEval g₀ T₁ x p q r| ≤ Φ · √(g₀ p p) · √(g₀ q q) · √(g₀ r r)` at every base point and
every triple.  The constant is the sharp-order `H^{a + 2} ↪ C²` embedding constant (`2(a + 2) > finrank
+ 4`) times `B`: the evaluation is the model reading of the order-`1` covariant gradient of the realized
symmetric tensor, whose `(0,3)` fibre norm is the `j = 1` summand of `iteratedCovGradJetSum
(realizeSymm T₁)`, dominated through `realizeSymm_iteratedCovGradJetSum_le` by
`iteratedCovGradJetSum T₁`, and through `exists_iteratedCovGradJetSum_le_toHs_sharpOrder` by
`C · ‖T₁.toHs(a + 2)‖ ≤ C · B`. -/
private theorem exists_covDerivRealizeEval_gcs_value_bound
    (g₀ : SmoothRiemannianMetric I M) (B : ℝ) (a : ℕ) (ha : 2 * a > Module.finrank ℝ E + 4) :
    ∃ Φ : ℝ, 0 ≤ Φ ∧
      ∀ (T₁ : Integral.L2.SmoothCcTensor g₀ 0 2),
        ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (a + 2) T₁‖ ≤ B →
        ∀ (x : M) (p q r : TangentSpace I x),
          |covDerivRealizeEval (I := I) g₀ T₁ x p q r| ≤
            Φ * Real.sqrt (g₀.inner x p p) * Real.sqrt (g₀.inner x q q) *
              Real.sqrt (g₀.inner x r r) := by
  classical
  have hsuper : 2 * (a + 2) > Module.finrank ℝ E + 4 := by omega
  obtain ⟨C₀, hC₀pos, hC₀⟩ :=
    exists_iteratedCovGradJetSum_le_toHs_sharpOrder (I := I) (M := M) g₀ (a + 2) hsuper
  refine ⟨C₀ * max B 0, by positivity, fun T₁ hB x p q r => ?_⟩
  letI : Bundle.RiemannianBundle (fun bb : M => TensorRSSpace 0 (2 + 0) I bb) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 (2 + 0)
  letI : Bundle.RiemannianBundle (fun bb : M => TensorRSSpace 0 (2 + 1) I bb) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 (2 + 1)
  letI : Bundle.RiemannianBundle (fun bb : M => TensorRSSpace 0 (2 + 2) I bb) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 (2 + 2)
  -- The realized `(0,3)` jet at `x`: bound its fibre norm through the embedding.
  set Sec : Integral.L2.SmoothCcTensor g₀ 0 3 :=
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g₀ 0 2 (realizeSymmCcTensor (I := I) g₀ T₁) with hSec
  -- `covGrad ∘ realizeSymm` is the order-1 iterated covariant gradient.
  have hSeceq : Sec = PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 1
      (realizeSymmCcTensor (I := I) g₀ T₁) := by
    rw [hSec, PDE.RicciFlow.iteratedCovGrad_succ (I := I) g₀ 0 2 0
      (realizeSymmCcTensor (I := I) g₀ T₁),
      PDE.RicciFlow.iteratedCovGrad_zero (I := I) g₀ 0 2
        (realizeSymmCcTensor (I := I) g₀ T₁)]
  -- The `(0,3)` fibre norm of the order-1 jet is the `j = 1` summand of the jet sum.
  have hsqrt_le : Real.sqrt (Integral.Connection.riemannianFiberNormSq (I := I) (M := M) g₀ 0 3 x
        (Sec.toSection x)) ≤ C₀ * max B 0 := by
    -- `√rfns(Sec) = ‖(∇¹ realizeSymm).toSection x‖`, the `j = 1` summand of the jet sum.
    have hsummand : Real.sqrt (Integral.Connection.riemannianFiberNormSq (I := I) (M := M) g₀ 0 3 x
          (Sec.toSection x)) ≤
        iteratedCovGradJetSum (I := I) g₀ (realizeSymmCcTensor (I := I) g₀ T₁) x := by
      rw [iteratedCovGradJetSum, Finset.sum_range_succ, Finset.sum_range_succ,
        Finset.sum_range_one]
      -- Rewrite all three jet summands to their `√rfns` forms, then compare as plain reals.
      rw [DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck.norm_toSection_eq_sqrt_riemannianFiberNormSq_installed
          (I := I) (M := M) g₀ 0 (2 + 0)
          (PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 0
            (realizeSymmCcTensor (I := I) g₀ T₁)) x,
        DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck.norm_toSection_eq_sqrt_riemannianFiberNormSq_installed
          (I := I) (M := M) g₀ 0 (2 + 1)
          (PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 1
            (realizeSymmCcTensor (I := I) g₀ T₁)) x,
        DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck.norm_toSection_eq_sqrt_riemannianFiberNormSq_installed
          (I := I) (M := M) g₀ 0 (2 + 2)
          (PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 2
            (realizeSymmCcTensor (I := I) g₀ T₁)) x]
      have hSec_rfns : Integral.Connection.riemannianFiberNormSq (I := I) (M := M) g₀ 0 3 x
            (Sec.toSection x) =
          Integral.Connection.riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + 1) x
            ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 1
              (realizeSymmCcTensor (I := I) g₀ T₁)).toSection x) := by rw [hSeceq]
      rw [hSec_rfns]
      have h0 := Real.sqrt_nonneg (Integral.Connection.riemannianFiberNormSq (I := I) (M := M)
        g₀ 0 (2 + 0) x ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 0
          (realizeSymmCcTensor (I := I) g₀ T₁)).toSection x))
      have h2 := Real.sqrt_nonneg (Integral.Connection.riemannianFiberNormSq (I := I) (M := M)
        g₀ 0 (2 + 2) x ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 2
          (realizeSymmCcTensor (I := I) g₀ T₁)).toSection x))
      linarith
    -- Domination by `T₁`'s jet sum and the embedding.
    have hreal := realizeSymm_iteratedCovGradJetSum_le (I := I) g₀ T₁ x
    have hemb := hC₀ T₁ x
    have hBmax : ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (a + 2) T₁‖ ≤
        max B 0 := le_trans hB (le_max_left _ _)
    have hchain : iteratedCovGradJetSum (I := I) g₀ (realizeSymmCcTensor (I := I) g₀ T₁) x ≤
        C₀ * max B 0 := by
      refine le_trans hreal (le_trans hemb ?_)
      exact mul_le_mul_of_nonneg_left hBmax hC₀pos.le
    exact le_trans hsummand hchain
  -- Apply the rank-3 Cauchy–Schwarz, then dominate the fibre-norm factor by `C₀ · max B 0`.
  have hmodel := covGrad_realizeSymm_unitModel_eq_covDerivRealizeEval (I := I) g₀ T₁ x p q r
  have hCS := abs_toModel_three_le_sqrt_rfns (I := I) (M := M) g₀ x Sec p q r
  rw [hSec] at hCS
  rw [hmodel] at hCS
  refine le_trans hCS ?_
  have hppnn : 0 ≤ Real.sqrt (g₀.inner x p p) := Real.sqrt_nonneg _
  have hqqnn : 0 ≤ Real.sqrt (g₀.inner x q q) := Real.sqrt_nonneg _
  have hrrnn : 0 ≤ Real.sqrt (g₀.inner x r r) := Real.sqrt_nonneg _
  have hsqrt_le' : Real.sqrt (Integral.Connection.riemannianFiberNormSq (I := I) (M := M) g₀ 0 3 x
      ((DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g₀ 0 2
        (realizeSymmCcTensor (I := I) g₀ T₁)).toSection x)) ≤ C₀ * max B 0 := by
    rw [← hSec]; exact hsqrt_le
  apply mul_le_mul_of_nonneg_right _ hrrnn
  apply mul_le_mul_of_nonneg_right _ hqqnn
  exact mul_le_mul_of_nonneg_right hsqrt_le' hppnn

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization in
set_option linter.unusedSectionVars false in
/-- **(POSIT — the family-uniform `g₀`-operator value bound of the connection difference.)**  For
the fibre-small (`gFibreOpBound g₀ (ccTensorBilinSymm g₀ T₁) δ`, `δ < 1/2`) supercritically
`H^{a+2}`-bounded (`2a > finrank + 4`) realized perturbation family, the connection difference
`connDiff g₁ g₀ x` of every realized member, as a `g₀`-operator, obeys the family-uniform value
bound
`√(g₀ x (connDiff g₁ g₀ x u v) (connDiff g₁ g₀ x u v)) ≤ Λ_C · √(g₀ x u u) · √(g₀ x v v)`
for a single constant `Λ_C ≥ 0` over the manifold and the family.

This is the value-form of the order-`0` Riemannian fibre sup of the `g₀`-lowered connection
difference `loweredConnDiffSection g₁ g₀` (whose `riemannianFiberNormSq` order-`0` fibre sup is the
Neumann-absorbed supercritical-`C¹` bound `exists_loweredConnDiffSection_rfns_fibre_sup_le`):
`connDiff g₁ g₀ = Γ(g₁) − Γ(g₀)` is first order in the metric perturbation
`h = ccTensorBilinSymm g₀ T₁` (`connDiff_g0_fibre_abs_bound`, the Koszul triangle with Neumann
self-absorption, `δ < 1/2`), and is `C⁰`-controlled family-uniformly by the supercritical
`H^{a+2} ↪ C¹` embedding of the metric jet (`iteratedCovGradJetSum_le_toHs`, `2a > finrank + 4`).
The trilinear `g₀`-fibre form `(u, v, w) ↦ g₀(connDiff g₁ g₀ x u v, w)` having a uniform fibre sup
is exactly a `g₀`-operator value bound on the contraction `u, v ↦ connDiff g₁ g₀ x u v`.

**Non-vacuity.**  Genuine (`Λ_C = 0` forces `connDiff g₁ g₀ ≡ 0`, false whenever `g₁ ≠ g₀`).  At
`g₁ = g₀` realized (`T₁ = 0`) the connection difference is `0` (`connDiff_self`) and `Λ_C = 0`
works.  Body `sorry`: the genuine supercritical-`C¹` / Neumann-absorption `C⁰` value bound of the
first-order Christoffel difference (consumers transitively depend on `sorryAx` through this posited
engine). -/
theorem exists_connDiff_gOp_sup_le
    (g₀ : SmoothRiemannianMetric I M) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1 / 2) (B : ℝ)
    (a : ℕ) (ha : 2 * a > Module.finrank ℝ E + 4) :
    ∃ Λ_C : ℝ, 0 ≤ Λ_C ∧
      ∀ (T₁ : Integral.L2.SmoothCcTensor g₀ 0 2) (g₁ : SmoothRiemannianMetric I M),
        (∀ (x : M) (v w : TangentSpace I x),
          g₁.inner x v w = g₀.inner x v w + ccTensorBilinSymm (I := I) g₀ T₁ x v w) →
        gFibreOpBound (I := I) g₀ (fun y => ccTensorBilinSymm (I := I) g₀ T₁ y) δ →
        ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (a + 2) T₁‖ ≤ B →
        ∀ (x : M) (u v : TangentSpace I x),
          Real.sqrt (g₀.inner x (connDiff (I := I) g₁ g₀ x u v) (connDiff (I := I) g₁ g₀ x u v)) ≤
            Λ_C * Real.sqrt (g₀.inner x u u) * Real.sqrt (g₀.inner x v v) := by
  classical
  obtain ⟨Φ, hΦ0, hΦ⟩ := exists_covDerivRealizeEval_gcs_value_bound (I := I) (M := M) g₀ B a ha
  -- The Neumann-absorbed constant; `1 - δ > 0` since `δ < 1/2`.
  have hδlt1 : δ < 1 := by linarith
  have h1δpos : 0 < 1 - δ := by linarith
  refine ⟨3 * Φ / (2 * (1 - δ)), by positivity, fun T₁ g₁ hg₁ hδbnd hB x u v => ?_⟩
  set z : TangentSpace I x := connDiff (I := I) g₁ g₀ x u v with hz
  set su := Real.sqrt (g₀.inner x u u) with hsu
  set sv := Real.sqrt (g₀.inner x v v) with hsv
  have hsu_nn : 0 ≤ su := Real.sqrt_nonneg _
  have hsv_nn : 0 ≤ sv := Real.sqrt_nonneg _
  -- `connDiff` evaluated at the smooth extensions reduces to its value at `u, v`.
  have hext : connDiff (I := I) g₁ g₀ x
        (Integral.Connection.smoothExtensionTangent (I := I) x u x)
        (Integral.Connection.smoothExtensionTangent (I := I) x v x) = z := by
    rw [Integral.Connection.smoothExtensionTangent_eq (I := I) x u,
      Integral.Connection.smoothExtensionTangent_eq (I := I) x v]
  -- Pairing bound against an arbitrary direction `c`, via the Koszul triangle.
  have hpair : ∀ c : TangentSpace I x,
      |g₀.inner x z c| ≤ ((3 * Φ / 2) * su * sv + δ * Real.sqrt (g₀.inner x z z)) *
        Real.sqrt (g₀.inner x c c) := by
    intro c
    have hkos := connDiff_g0_fibre_abs_bound (I := I) g₁ g₀ T₁ hg₁ x v u c
    rw [hext] at hkos
    -- Bound each covariant-derivative-evaluation term by the embedding constant.
    have hcdre1 := hΦ T₁ hB x v u c
    have hcdre2 := hΦ T₁ hB x u v c
    have hcdre3 := hΦ T₁ hB x c v u
    set sc := Real.sqrt (g₀.inner x c c) with hsc
    have hsc_nn : 0 ≤ sc := Real.sqrt_nonneg _
    -- The self-referential perturbation term, via `gFibreOpBound`.
    have hself : |ccTensorBilinSymm (I := I) g₀ T₁ x z c| ≤
        δ * Real.sqrt (g₀.inner x z z) * sc := hδbnd x z c
    have hszz_nn : 0 ≤ Real.sqrt (g₀.inner x z z) := Real.sqrt_nonneg _
    -- Assemble: `2|g₀(z,c)| ≤ 3Φ·su·sv·sc + 2δ·√(g₀ z z)·sc`.
    have hsum : |2 * g₀.inner x z c| ≤
        3 * Φ * su * sv * sc + 2 * (δ * Real.sqrt (g₀.inner x z z) * sc) := by
      refine le_trans hkos ?_
      have e1 : |covDerivRealizeEval (I := I) g₀ T₁ x v u c| ≤ Φ * sv * su * sc := hcdre1
      have e2 : |covDerivRealizeEval (I := I) g₀ T₁ x u v c| ≤ Φ * su * sv * sc := hcdre2
      have e3 : |covDerivRealizeEval (I := I) g₀ T₁ x c v u| ≤ Φ * sc * sv * su := hcdre3
      have hself2 : 2 * |ccTensorBilinSymm (I := I) g₀ T₁ x z c| ≤
          2 * (δ * Real.sqrt (g₀.inner x z z) * sc) := by linarith
      nlinarith [e1, e2, e3, hself2, hsu_nn, hsv_nn, hsc_nn, hΦ0, mul_nonneg hsu_nn hsv_nn]
    have h2zc : |2 * g₀.inner x z c| = 2 * |g₀.inner x z c| := by rw [abs_mul]; norm_num
    rw [h2zc] at hsum
    have hfinal : |g₀.inner x z c| ≤
        (3 * Φ / 2) * su * sv * sc + δ * Real.sqrt (g₀.inner x z z) * sc := by linarith
    calc |g₀.inner x z c|
        ≤ (3 * Φ / 2) * su * sv * sc + δ * Real.sqrt (g₀.inner x z z) * sc := hfinal
      _ = ((3 * Φ / 2) * su * sv + δ * Real.sqrt (g₀.inner x z z)) * sc := by ring
  -- Riesz-lift the pairing bound to a self-norm bound, then Neumann-absorb the `√(g₀ z z)` term.
  set R := Real.sqrt (g₀.inner x z z) with hR
  have hR_nn : 0 ≤ R := Real.sqrt_nonneg _
  have hKnn : 0 ≤ (3 * Φ / 2) * su * sv + δ * R := by positivity
  have hRle : R ≤ (3 * Φ / 2) * su * sv + δ * R :=
    sqrt_gInner_self_le_of_forall_inner_le (I := I) (M := M) g₀ x z hKnn hpair
  -- `(1 - δ)·R ≤ (3Φ/2)·su·sv`, so `R ≤ 3Φ/(2(1-δ))·su·sv`.
  have hRabsorb : (1 - δ) * R ≤ (3 * Φ / 2) * su * sv := by nlinarith [hRle]
  have hgoal : R ≤ 3 * Φ / (2 * (1 - δ)) * su * sv := by
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, le_div_iff₀ (by positivity : (0:ℝ) < 2 * (1 - δ))]
    nlinarith [hRabsorb, h1δpos, hsu_nn, hsv_nn, mul_nonneg hsu_nn hsv_nn, hR_nn]
  exact hgoal

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization in
set_option linter.unusedSectionVars false in
/-- **(The family-uniform `g₀`-fibre value sup of the connection-difference action — glued.)**
For the fibre-small supercritically `H^{a+2}`-bounded realized perturbation family, the
`g₀`-fibre norm of the connection-difference action `connDiff g₁ g₀ x (W₁ x) v`,
`W₁ = deTurckVF g₁ g_bg`, obeys the family-uniform value bound
`√(g₀ x (connDiff g₁ g₀ x (W₁ x) v) (connDiff g₁ g₀ x (W₁ x) v)) ≤ Λ · √(g₀ x v v)`.

Glued: the connection difference `g₀`-operator bound `exists_connDiff_gOp_sup_le` applied at the
field `u = W₁ x` gives `√(g₀ (action v)²) ≤ Λ_C · √(g₀ (W₁ x) (W₁ x)) · √(g₀ v v)`, and the DeTurck
field value sup `exists_deTurckVF_gNorm_sup_le` absorbs the middle factor into `Λ_W`, so the action
norm is bounded by `Λ_C · Λ_W · √(g₀ v v)`.  Both factors are the posited bedrock engines above
(consumers transitively depend on `sorryAx` through them). -/
theorem exists_connDiffActionG0_gNorm_sup_le
    (g₀ g_bg : SmoothRiemannianMetric I M) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1 / 2) (B : ℝ)
    (a : ℕ) (ha : 2 * a > Module.finrank ℝ E + 4) :
    ∃ Λ : ℝ, 0 ≤ Λ ∧
      ∀ (T₁ : Integral.L2.SmoothCcTensor g₀ 0 2) (g₁ : SmoothRiemannianMetric I M),
        (∀ (x : M) (v w : TangentSpace I x),
          g₁.inner x v w = g₀.inner x v w + ccTensorBilinSymm (I := I) g₀ T₁ x v w) →
        gFibreOpBound (I := I) g₀ (fun y => ccTensorBilinSymm (I := I) g₀ T₁ y) δ →
        ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (a + 2) T₁‖ ≤ B →
        ∀ (x : M) (v : TangentSpace I x),
          Real.sqrt (g₀.inner x
              (connDiff (I := I) g₁ g₀ x (deTurckVF (I := I) g₁ g_bg x) v)
              (connDiff (I := I) g₁ g₀ x (deTurckVF (I := I) g₁ g_bg x) v)) ≤
            Λ * Real.sqrt (g₀.inner x v v) := by
  obtain ⟨Λ_W, hW0, hW⟩ := exists_deTurckVF_gNorm_sup_le (I := I) g₀ g_bg δ hδ0 hδ1 B a ha
  obtain ⟨Λ_C, hC0, hC⟩ := exists_connDiff_gOp_sup_le (I := I) g₀ δ hδ0 hδ1 B a ha
  refine ⟨Λ_C * Λ_W, by positivity, fun T₁ g₁ hg₁ hδbnd hB₁ x v => ?_⟩
  have hWx := hW T₁ g₁ hg₁ hδbnd hB₁ x
  have hCx := hC T₁ g₁ hg₁ hδbnd hB₁ x (deTurckVF (I := I) g₁ g_bg x) v
  refine le_trans hCx ?_
  have hvnn : 0 ≤ Real.sqrt (g₀.inner x v v) := Real.sqrt_nonneg _
  apply mul_le_mul_of_nonneg_right _ hvnn
  exact mul_le_mul_of_nonneg_left hWx hC0

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization in
set_option linter.unusedSectionVars false in
/-- **(POSIT — the family-uniform pointwise `g₀`-Cauchy–Schwarz value bound of the
connection-difference action bilinear form.)**  For the fibre-small
(`gFibreOpBound g₀ (ccTensorBilinSymm g₀ T₁) δ`, `δ < 1/2`) supercritically `H^{a+2}`-bounded
(`2a > finrank + 4`) realized perturbation family, the extracted bilinear form
`ccTensorBilin g₀ (connDiffActionSection g₀ g₁ g₀ g_bg) x` — value
`g₀(connDiff g₁ g₀ x (W₁ x) v, w)`, `W₁ = deTurckVF g₁ g_bg` — obeys the family-uniform pointwise
`g₀`-Cauchy–Schwarz value bound
`|·| ≤ Λ₀ · √(g₀ x v v) · √(g₀ x w w)` for a single constant `Λ₀ ≥ 0` over the manifold and the
family.

This is the order-`0` `C⁰` value of the first-order metric carrier `connDiff g₁ g₀ x (W₁ x)`
(a Christoffel-difference value contracted against the smooth DeTurck field): the connection
difference is first order in the metric perturbation `h = ccTensorBilinSymm g₀ T₁`
(`connDiff_g0_fibre_abs_bound`, the Koszul triangle with Neumann self-absorption, `δ < 1/2`), and the
DeTurck field `W₁` is the `g₁`-trace of the same first-order Christoffel difference; both are
`C⁰`-controlled family-uniformly by the supercritical `H^{a+2} ↪ C¹` embedding of the metric jet
(`iteratedCovGradJetSum_le_toHs`, `2a > finrank + 4 ⟹ a + 2 > dim/2 + 1`).

**Non-vacuity.**  Vanishes at `T₁ = 0` realized (`g₁ = g₀`, `connDiff g₀ g₀ = 0`, the bilinear form
is `0`, `Λ₀ = 0` works); genuine (`Λ₀ = 0` forces the value `≡ 0`, false whenever `g₁ ≠ g₀`).

Glued (consumers transitively depend on `sorryAx` only through the posited bedrock engines): the
bilinear value rewrites — `ccTensorBilin_apply`, `ccTensorModel`, `ccTensorMultilinear_apply`,
`connDiffActionSection_toModel_apply`, `connDiffActionBilin_apply` — to
`g₀(connDiff g₁ g₀ x (W₁ x) v, w)`, `W₁ = deTurckVF g₁ g_bg`; the `g₀`-Cauchy–Schwarz
(`abs_metric_inner_le_sqrt_metric_quadratic`) folds it to
`√(g₀ (connDiff g₁ g₀ x (W₁ x) v)²) · √(g₀ w w)`, and the connection-difference action `g₀`-fibre
value sup `exists_connDiffActionG0_gNorm_sup_le` bounds the action factor by `Λ · √(g₀ v v)`. -/
theorem exists_connDiffActionBilin_gcs_value_bound
    (g₀ g_bg : SmoothRiemannianMetric I M) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1 / 2) (B : ℝ)
    (a : ℕ) (ha : 2 * a > Module.finrank ℝ E + 4) :
    ∃ Λ₀ : ℝ, 0 ≤ Λ₀ ∧
      ∀ (T₁ : Integral.L2.SmoothCcTensor g₀ 0 2) (g₁ : SmoothRiemannianMetric I M),
        (∀ (x : M) (v w : TangentSpace I x),
          g₁.inner x v w = g₀.inner x v w + ccTensorBilinSymm (I := I) g₀ T₁ x v w) →
        gFibreOpBound (I := I) g₀ (fun y => ccTensorBilinSymm (I := I) g₀ T₁ y) δ →
        ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (a + 2) T₁‖ ≤ B →
        ∀ (x : M) (v w : TangentSpace I x),
          |ccTensorBilin (I := I) g₀ (connDiffActionSection (I := I) g₀ g₁ g₀ g_bg) x v w| ≤
            Λ₀ * Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x w w) := by
  obtain ⟨Λ, hΛ0, hΛ⟩ := exists_connDiffActionG0_gNorm_sup_le (I := I) g₀ g_bg δ hδ0 hδ1 B a ha
  refine ⟨Λ, hΛ0, fun T₁ g₁ hg₁ hδbnd hB₁ x v w => ?_⟩
  have hred : ccTensorBilin (I := I) g₀ (connDiffActionSection (I := I) g₀ g₁ g₀ g_bg) x v w =
      g₀.inner x (connDiff (I := I) g₁ g₀ x (deTurckVF (I := I) g₁ g_bg x) v) w := by
    rw [ccTensorBilin_apply]
    show ccTensorModel (I := I) g₀ (connDiffActionSection (I := I) g₀ g₁ g₀ g_bg) x ![v, w] = _
    rw [ccTensorModel, ccTensorMultilinear_apply, connDiffActionSection_toModel_apply,
      connDiffActionBilin_apply]
  rw [hred]
  set u := connDiff (I := I) g₁ g₀ x (deTurckVF (I := I) g₁ g_bg x) v with hu
  refine le_trans
    (DifferentialGeometry.Analysis.Laplacian.abs_metric_inner_le_sqrt_metric_quadratic g₀ x u w) ?_
  have hwnn : 0 ≤ Real.sqrt (g₀.inner x w w) := Real.sqrt_nonneg _
  have hop := hΛ T₁ g₁ hg₁ hδbnd hB₁ x v
  calc Real.sqrt (g₀.inner x u u) * Real.sqrt (g₀.inner x w w)
      ≤ (Λ * Real.sqrt (g₀.inner x v v)) * Real.sqrt (g₀.inner x w w) :=
        mul_le_mul_of_nonneg_right hop hwnn
    _ = Λ * Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x w w) := by ring

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization in
set_option linter.unusedSectionVars false in
/-- **(POSIT — the family-uniform order-`0` fibre value sup of the connection-difference action
section.)**  For the fibre-small (`gFibreOpBound g₀ (ccTensorBilinSymm g₀ T₁) δ`, `δ < 1/2`)
supercritically `H^{a+2}`-bounded (`2a > finrank + 4`) realized perturbation family, the order-`0`
intrinsic squared fibre norm of the connection-difference action section
`connDiffActionSection g₀ g₁ g₀ g_bg` — fibre `g₀(connDiff g₁ g₀ x (W₁ x) v, w)`,
`W₁ = deTurckVF g₁ g_bg` — is uniformly bounded by a single constant `Λ²` over the manifold and the
family.

The fibre value is the partial contraction of the `g₀`-lowered connection difference
`loweredConnDiffSection g₁ g₀` (whose order-`0` fibre sup is the Neumann-absorbed supercritical-`C¹`
bound `exists_loweredConnDiffSection_rfns_fibre_sup_le`) against the smooth DeTurck field
`W₁ = deTurckVF g₁ g_bg` (whose realized order-`0` fibre value is supercritically `C⁰`-bounded
through the `H^{a+2} ↪ C¹` embedding of the metric jet, `2a > finrank + 4`); the contraction
Cauchy–Schwarz folds the two factor sups into a single family-uniform order-`0` value sup.

**Non-vacuity.**  A genuine fibre sup (a `Λ = 0` witness forces the action section `≡ 0` at every
point, false whenever `g₁ ≠ g₀` since `connDiff g₁ g₀ ≠ 0` and `W₁ ≠ 0`).  At `T₁ = 0` realized
(`g₁ = g₀`), `connDiff g₀ g₀ = 0`, the action section is the zero section, and `Λ = 0` works.  Its
body is `sorry`: the genuine supercritical-`C¹` / Neumann-absorption contraction value sup of the
connection-difference action section. -/
theorem exists_connDiffActionSection_rfns_fibre_sup_le
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
            ((connDiffActionSection (I := I) g₀ g₁ g₀ g_bg).toSection x) ≤ Λ ^ 2 := by
  obtain ⟨Λ₀, hΛ₀0, hΛ₀⟩ :=
    exists_connDiffActionBilin_gcs_value_bound (I := I) g₀ g_bg δ hδ0 hδ1 B a ha
  refine ⟨Module.finrank ℝ E * Λ₀, by positivity, fun T₁ g₁ hg₁ hδbnd hB₁ x => ?_⟩
  exact rfns_le_of_ccTensorBilin_gcs_bound (I := I) g₀
    (connDiffActionSection (I := I) g₀ g₁ g₀ g_bg) x Λ₀ hΛ₀0
    (fun v w => hΛ₀ T₁ g₁ hg₁ hδbnd hB₁ x v w)

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
(`g₁ = g₀`, the difference is the zero section).

Glued: the carrier difference rewrites to the connection-difference action section
`connDiffActionSection g₀ g₁ g₀ g_bg`
(`loweredCovGradDeTurckVFMixed_connSlot_sub_eq_connDiffActionSection`), whose family-uniform order-`0`
fibre value sup is the posited child `exists_connDiffActionSection_rfns_fibre_sup_le`. -/
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
                - loweredCovGradDeTurckVFMixed (I := I) g₀ g₀ g₀ g₁ g_bg).toSection x) ≤ Λ ^ 2 := by
  obtain ⟨Λ, hΛ0, hΛ⟩ :=
    exists_connDiffActionSection_rfns_fibre_sup_le (I := I) g₀ g_bg δ hδ0 hδ1 B a ha
  refine ⟨Λ, hΛ0, fun T₁ g₁ hg₁ hδbnd hB₁ x => ?_⟩
  rw [loweredCovGradDeTurckVFMixed_connSlot_sub_eq_connDiffActionSection (I := I) g₀ g₁ g_bg]
  exact hΛ T₁ g₁ hg₁ hδbnd hB₁ x

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
        ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (l + 3 + 3 + a) T₁‖ ≤ B →
        ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l
              (connDiffActionSection (I := I) g₀ g₁ g₀ g_bg)‖ ^ 2 ≤
          C * ∑ i ∈ Finset.range (l + 2 + 1),
              ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i
                (realizeSymmCcTensor (I := I) g₀ T₁)‖ ^ 2
            + C * (∑ m ∈ Finset.range (l + 3 + 1 + 1),
                ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 m T₁‖ ^ 2)
              * ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (2 * (a + 2))
                  (realizeSymmCcTensor (I := I) g₀ T₁)‖ ^ 2 :=
  DifferentialGeometry.PDE.RicciFlow.Pullback.exists_iteratedCovGrad_connDiffActionSection_le_jetSum
    (I := I) g₀ g_bg δ hδ0 hδ1 B a ha l

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
        ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (l + 3 + 3 + a) T₁‖ ≤ B →
          (∀ x : M,
            Integral.Connection.riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x
              ((loweredCovGradDeTurckVFMixed (I := I) g₀ g₀ g₁ g₁ g_bg
                  - loweredCovGradDeTurckVFMixed (I := I) g₀ g₀ g₀ g₁ g_bg).toSection x) ≤
                C ^ 2) ∧
          ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l
              (loweredCovGradDeTurckVFMixed (I := I) g₀ g₀ g₁ g₁ g_bg
                - loweredCovGradDeTurckVFMixed (I := I) g₀ g₀ g₀ g₁ g_bg)‖ ^ 2 ≤
            C * ∑ i ∈ Finset.range (l + 2 + 1),
                ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i
                  (realizeSymmCcTensor (I := I) g₀ T₁)‖ ^ 2
              + C * (∑ m ∈ Finset.range (l + 3 + 1 + 1),
                  ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 m T₁‖ ^ 2)
                * ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (2 * (a + 2))
                    (realizeSymmCcTensor (I := I) g₀ T₁)‖ ^ 2 := by
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
  · intro T₁ g₁ hg₁ hδbnd hB₁ hBjet
    refine ⟨?_, ?_⟩
    · intro x
      refine le_trans (hΛ T₁ g₁ hg₁ hδbnd hB₁ x) ?_
      have hnn : (0 : ℝ) ≤ Real.sqrt K₁ := Real.sqrt_nonneg _
      nlinarith [Real.sqrt_nonneg K₁, hΛ0, hC₃0, sq_nonneg (Real.sqrt K₁ + C₃),
        mul_nonneg hΛ0 (add_nonneg hnn hC₃0)]
    · rw [loweredCovGradDeTurckVFMixed_connSlot_sub_eq_connDiffActionSection (I := I) g₀ g₁ g_bg]
      have hC₃u := hC₃ T₁ g₁ hg₁ hδbnd hB₁ hBjet
      have hCle : C₃ ≤ Real.sqrt K₁ + Λ + C₃ := by
        have : (0 : ℝ) ≤ Real.sqrt K₁ + Λ := by positivity
        linarith
      set Sdiff : ℝ := ∑ i ∈ Finset.range (l + 2 + 1),
        ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i (realizeSymmCcTensor (I := I) g₀ T₁)‖ ^ 2
        with hSdiff
      set Scross : ℝ := (∑ m ∈ Finset.range (l + 3 + 1 + 1),
          ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 m T₁‖ ^ 2)
          * ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (2 * (a + 2))
              (realizeSymmCcTensor (I := I) g₀ T₁)‖ ^ 2 with hScross
      have hSdiff_nn : 0 ≤ Sdiff := Finset.sum_nonneg fun i _ => sq_nonneg _
      have hScross_nn : 0 ≤ Scross := by
        rw [hScross]; exact mul_nonneg (Finset.sum_nonneg fun m _ => sq_nonneg _) (sq_nonneg _)
      have hC₃u' : ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l
              (connDiffActionSection (I := I) g₀ g₁ g₀ g_bg)‖ ^ 2 ≤ C₃ * Sdiff + C₃ * Scross := by
        rw [hSdiff, hScross, ← mul_assoc]; exact hC₃u
      calc ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l
              (connDiffActionSection (I := I) g₀ g₁ g₀ g_bg)‖ ^ 2
          ≤ C₃ * Sdiff + C₃ * Scross := hC₃u'
        _ ≤ (Real.sqrt K₁ + Λ + C₃) * Sdiff + (Real.sqrt K₁ + Λ + C₃) * Scross := by
            have h1 := mul_le_mul_of_nonneg_right hCle hSdiff_nn
            have h2 := mul_le_mul_of_nonneg_right hCle hScross_nn
            linarith [h1, h2]
        _ = (Real.sqrt K₁ + Λ + C₃) * Sdiff + (Real.sqrt K₁ + Λ + C₃) *
              (∑ m ∈ Finset.range (l + 3 + 1 + 1),
                ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 m T₁‖ ^ 2)
              * ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (2 * (a + 2))
                  (realizeSymmCcTensor (I := I) g₀ T₁)‖ ^ 2 := by rw [hScross, mul_assoc]

/-! ### The pointwise fibre-norm sup of the field-difference covariant gradient

The genuine order-`2` content behind the field-difference covariant-gradient value sup is the
pointwise intrinsic fibre-norm sup of the field-difference gradient section
`fieldDiffGradSection g₀ g₁ g₀ g_bg`.  It is assembled from the proven `l = 0` covariant-Leibniz
product grid of that section (`fieldDiffGradSection_iteratedCovGrad_rfns_productGrid_le`), the proven
sharp-order supercritical fibre sups of the realized-perturbation jets
(`realizeSymm_iteratedCovGrad_rfns_fibre_sup`), and the per-order fibre sup of the `g₀`-lowered
connection-difference jets (`loweredConnDiff_iteratedCovGrad_rfns_fibre_sup`).  The connection-difference
factor reaches order `3` (the realized `4`-jet), so the assembly carries the **higher Sobolev ball**
`‖T₁.toHs(6 + a)‖ ≤ B`, mirroring the sibling field-difference jet engine
`exists_iteratedCovGrad_deTurckVF_le_jetSum` (whose second ball is `‖T₁.toHs(l + 3 + 3 + a)‖ ≤ B`, the
`l = 0` instance of which is `‖T₁.toHs(6 + a)‖ ≤ B`). -/

set_option linter.unusedSectionVars false in
/-- **The scalar `rfns` homogeneity.**  `rfns(c • T) = c² · rfns(T)` for a fibre tensor `T`, from
the pointwise inner-product `smul`-bilinearity (`tensorInnerPointwise_smul_left/right`,
`TensorRSSpace.toModel_smul`). -/
private lemma rfns_smul_local (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M) (c : ℝ)
    (T : TensorRSSpace r s I x) :
    Integral.Connection.riemannianFiberNormSq (I := I) (M := M) g r s x (c • T) =
      c ^ 2 * Integral.Connection.riemannianFiberNormSq (I := I) (M := M) g r s x T := by
  rw [Integral.Connection.riemannianFiberNormSq_eq_tensorInnerPointwise,
    Integral.Connection.riemannianFiberNormSq_eq_tensorInnerPointwise,
    TensorRSSpace.toModel_smul, Integral.L2.tensorInnerPointwise_smul_left,
    Integral.L2.tensorInnerPointwise_smul_right]
  ring

attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization in
set_option linter.unusedSectionVars false in
/-- **The family-uniform per-order pointwise fibre sup of the perturbation jets.**  For the
supercritically `H^{σ₀}`-bounded realized perturbation family (`2(a + 1) > finrank`, encoded as
`a + 1 + l ≤ σ₀` per order), the order-`l` intrinsic squared fibre norm of `T₁` is bounded by a
single per-order constant `K l` over the manifold and the family.  The order-`l` chain is the
sharp-order supercritical embedding `tensorC0_embedding_sharpOrder` (`N = a + 1`, `2(a + 1) >
finrank` from `2a > finrank + 4`) of the order-`l` covariant gradient `∇^l T₁`, composed with the
order-dropping `iteratedCovGrad_toHs_norm_le` (`‖(∇^l T₁).toHs(a + 1)‖ ≤ C · ‖T₁.toHs(a + 1 + l)‖`)
and the Sobolev-order monotonicity `toHs_norm_mono` (`‖T₁.toHs(a + 1 + l)‖ ≤ ‖T₁.toHs σ₀‖ ≤ B`,
whenever `a + 1 + l ≤ σ₀`); squaring `‖(∇^l T₁).toSection x‖ = √rfns` gives the per-order fibre
sup. -/
private lemma loweredConnDiff_t1jet_rfns_familyUniform
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ) (ha : 2 * a > Module.finrank ℝ E + 4) (B : ℝ)
    (σ₀ : ℕ) :
    ∃ K : ℕ → ℝ, (∀ l, 0 ≤ K l) ∧
      ∀ (T₁ : Integral.L2.SmoothCcTensor g₀ 0 2) (l : ℕ), a + 1 + l ≤ σ₀ →
        ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) σ₀ T₁‖ ≤ B →
        ∀ x : M,
          Integral.Connection.riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
              ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l T₁).toSection x) ≤ K l := by
  classical
  have hsuper : Module.finrank ℝ E < 2 * (a + 1) := by omega
  have hC0 : ∀ l : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ (T : Integral.L2.SmoothCcTensor g₀ 0 (2 + l)) (x : M),
        (letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 (2 + l) I b) :=
          Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 (2 + l)
        ‖T.toSection x‖) ≤
          C * ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2 + l) (a + 1) T‖ :=
    fun l => tensorC0_embedding_sharpOrder (I := I) (M := M) g₀ 0 (2 + l) (a + 1) hsuper
  choose Cemb hCemb0 hCemb using hC0
  have hCdrop : ∀ l : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ (T : Integral.L2.SmoothCcTensor g₀ 0 2),
        ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2 + l) (a + 1)
            (PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l T)‖ ≤
          C * ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2)
            ((a + 1) + l) T‖ :=
    fun l => iteratedCovGrad_toHs_norm_le (I := I) g₀ 0 2 l (a + 1)
  choose Cdrop hCdrop0 hCdrop using hCdrop
  refine ⟨fun l => (Cemb l * Cdrop l * max B 0) ^ 2, fun l => by positivity, ?_⟩
  intro T₁ l hσ hB x
  letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 (2 + l) I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 (2 + l)
  have hball : ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2)
      ((a + 1) + l) T₁‖ ≤ max B 0 :=
    le_trans (le_trans (toHs_norm_mono (I := I) g₀ (by omega) T₁) hB) (le_max_left _ _)
  have hnorm_le : ‖(PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l T₁).toSection x‖ ≤
      Cemb l * Cdrop l * max B 0 := by
    calc ‖(PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l T₁).toSection x‖
        ≤ Cemb l * ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2 + l) (a + 1)
            (PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l T₁)‖ :=
          hCemb l (PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l T₁) x
      _ ≤ Cemb l * (Cdrop l * ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2)
            ((a + 1) + l) T₁‖) :=
          mul_le_mul_of_nonneg_left (hCdrop l T₁) (hCemb0 l).le
      _ ≤ Cemb l * (Cdrop l * max B 0) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hball (hCdrop0 l)) (hCemb0 l).le
      _ = Cemb l * Cdrop l * max B 0 := by ring
  have hrfns_nn : 0 ≤ Integral.Connection.riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
      ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l T₁).toSection x) :=
    Integral.Connection.riemannianFiberNormSq_nonneg _ _ _ _ _
  have hsqrt := DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck.norm_toSection_eq_sqrt_riemannianFiberNormSq_installed
    (I := I) (M := M) g₀ 0 (2 + l)
    (PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l T₁) x
  rw [hsqrt] at hnorm_le
  have hsqrt_le : Real.sqrt (Integral.Connection.riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
      ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l T₁).toSection x)) ≤
      Cemb l * Cdrop l * max B 0 := hnorm_le
  calc Integral.Connection.riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
        ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l T₁).toSection x)
      = Real.sqrt (Integral.Connection.riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
          ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l T₁).toSection x)) ^ 2 :=
        (Real.sq_sqrt hrfns_nn).symm
    _ ≤ (Cemb l * Cdrop l * max B 0) ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) hsqrt_le 2

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization in
set_option linter.unusedSectionVars false in
/-- **The family-uniform per-order pointwise fibre sup of the realized-symmetric perturbation
jets (all orders).**  For the supercritically `H^{σ₀}`-bounded realized perturbation family, the
order-`i` intrinsic squared fibre norm of `realizeSymmCcTensor g₀ T₁` is bounded by a single
per-order constant `Krs i` whenever `a + 1 + i ≤ σ₀`.  The order-`i` realize-jet `rfns` is bounded by
`C_i · ∑_{l ≤ i} rfns(∇^l T₁)(x)` (`exists_riemannianFiberNormSq_iteratedCovGrad_realizeSymm_le_jetSum`,
no derivative gain through the realization map) and each underlying `T₁`-jet `rfns(∇^l T₁)(x)` by the
per-order perturbation-jet fibre sup `loweredConnDiff_t1jet_rfns_familyUniform` (`a + 1 + l ≤
a + 1 + i ≤ σ₀`), so the finite sum telescopes to `Krs i := C_i · ∑_{l ≤ i} K l`. -/
private lemma loweredConnDiff_realizeSymm_jet_rfns_familyUniform
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ) (ha : 2 * a > Module.finrank ℝ E + 4) (B : ℝ)
    (σ₀ : ℕ) :
    ∃ Krs : ℕ → ℝ, (∀ i, 0 ≤ Krs i) ∧
      ∀ (T₁ : Integral.L2.SmoothCcTensor g₀ 0 2) (i : ℕ), a + 1 + i ≤ σ₀ →
        ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) σ₀ T₁‖ ≤ B →
        ∀ x : M,
          Integral.Connection.riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
              ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i
                (realizeSymmCcTensor (I := I) g₀ T₁)).toSection x) ≤ Krs i := by
  classical
  obtain ⟨K, hK0, hK⟩ := loweredConnDiff_t1jet_rfns_familyUniform (I := I) g₀ a ha B σ₀
  have hrs : ∀ i : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ (T : Integral.L2.SmoothCcTensor g₀ 0 2) (x : M),
        Integral.Connection.riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
            ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i
              (realizeSymmCcTensor (I := I) g₀ T)).toSection x) ≤
          C * ∑ l ∈ Finset.range (i + 1),
            Integral.Connection.riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
              ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l T).toSection x) :=
    fun i => DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck.exists_riemannianFiberNormSq_iteratedCovGrad_realizeSymm_le_jetSum
      (I := I) g₀ i
  choose Crs hCrs0 hCrs using hrs
  refine ⟨fun i => Crs i * ∑ l ∈ Finset.range (i + 1), K l, fun i => ?_, ?_⟩
  · exact mul_nonneg (hCrs0 i) (Finset.sum_nonneg fun l _ => hK0 l)
  · intro T₁ i hσ hB x
    refine le_trans (hCrs i T₁ x) ?_
    refine mul_le_mul_of_nonneg_left ?_ (hCrs0 i)
    refine Finset.sum_le_sum (fun l hl => ?_)
    have hli : l ≤ i := by have := Finset.mem_range.mp hl; omega
    exact hK T₁ l (by omega) hB x

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization in
set_option linter.unusedSectionVars false in
/-- **(POSIT — the family-uniform Rest bound of the cross-correction covariant jet.)**  The
family-uniform restatement of the per-`(g₁, T₁)`-posited sibling
`crossCorrParallelContraction_iteratedCovGrad_rest_rfns_peel_le`
(`CrossCorrectionContractionTopRest.lean`), whose genuine combinatorial constant `Cenv(g₀, p) · 4^p`
is in fact family-uniform — the on-disk sibling merely places the `∃ C` after `(g₁, T₁)`.  The
difference-factor window is **strictly below `p`** (`i < p`), so it never re-introduces the order-`p`
jet `∇^p D`; the realized factor runs `l ≤ p + 1 − i`.  Its body is `sorry`: the contraction-native
operator-reconciliation + bare-product binomial telescope under the cometric trace annihilation
(consumers transitively depend on `sorryAx` through this posited Rest engine). -/
private theorem loweredConnDiff_crossCorr_rest_rfns_familyUniform
    (g₀ : SmoothRiemannianMetric I M) (p : ℕ) :
    ∃ Crest : ℝ, 0 ≤ Crest ∧
      ∀ (T₁ : Integral.L2.SmoothCcTensor g₀ 0 2) (g₁ : SmoothRiemannianMetric I M) (x : M),
        Integral.Connection.riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + 0 + 0 + p) x
            ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 (3 + 0 + 0) p
                (Integral.Connection.crossCorrParallelContraction (I := I) g₀ (a := 0) (b := 0)
                  (realizeSymmCcTensor (I := I) g₀ T₁)
                  (permuteCcTensor (I := I) g₀ c[(0 : Fin 3), 1, 2]
                    (loweredConnDiffSection (I := I) g₁ g₀)))
              - Integral.Connection.crossCorrParallelContraction (I := I) g₀ (a := 0) (b := p)
                  (realizeSymmCcTensor (I := I) g₀ T₁)
                  (PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 p
                    (permuteCcTensor (I := I) g₀ c[(0 : Fin 3), 1, 2]
                      (loweredConnDiffSection (I := I) g₁ g₀)))).toSection x) ≤
          Crest * ∑ i ∈ Finset.range p,
            Integral.Connection.riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + i) x
                ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 i
                  (loweredConnDiffSection (I := I) g₁ g₀)).toSection x) *
              ∑ l ∈ Finset.range (p + 1 - i),
                Integral.Connection.riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
                  ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l
                    (realizeSymmCcTensor (I := I) g₀ T₁)).toSection x) := by
  sorry

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization in
set_option linter.unusedSectionVars false in
/-- **The order-`p` Neumann-absorbed fibre sup of the `g₀`-lowered connection difference (strong
induction on `p`).**  The family-uniform inductive engine behind
`loweredConnDiff_iteratedCovGrad_rfns_fibre_sup`.  At order `p` the differentiated-Koszul section
identity `2 · ∇^p D = ∇^p (koszulComb) − 2 · ∇^p (crossCorrection)` controls `rD := rfns(∇^p D)(x)`
by `4 · rD ≤ 2 · rfns(∇^p koszul) + 8 · rfns(∇^p cross)`; the clean-linear-part Koszul arm is bounded
family-uniformly by `koszulCombSection_iteratedCovGrad_rfns_le` (the `≤ (p + 1)`-jet of the
perturbation, each jet dominated by `loweredConnDiff_t1jet_rfns_familyUniform`); the cross arm splits
into a Top cell `crossCorrParallelContraction (b := p) (realizeSymm T₁) (∇^p (permute D))` bounded by
the sharp `δ²` of `crossCorrParallelContraction_rfns_le_sq_passenger` (re-indexed to `rD` through the
permutation isometry `riemannianFiberNormSq_iteratedCovGrad_permuteCcTensor`) and a Rest cell bounded
by the family-uniform `loweredConnDiff_crossCorr_rest_rfns_familyUniform` (whose connection-difference
window is strictly `< p`, closed by the strong induction hypothesis, and whose realized window is
bounded by `loweredConnDiff_realizeSymm_jet_rfns_familyUniform`).  The order-uniform Neumann
absorption `(4 − 16δ²) > 0` (`δ < 1/2`) divides out the `δ²`-fed back-coupling. -/
private theorem loweredConnDiff_iteratedCovGrad_rfns_fibre_sup_aux
    (g₀ : SmoothRiemannianMetric I M) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1 / 2) (B : ℝ)
    (a : ℕ) (ha : 2 * a > Module.finrank ℝ E + 4) :
    ∀ p : ℕ, ∃ Λ : ℝ, 0 ≤ Λ ∧
      ∀ (T₁ : Integral.L2.SmoothCcTensor g₀ 0 2) (g₁ : SmoothRiemannianMetric I M),
        (∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T₁ y v w) →
        gFibreOpBound (I := I) g₀ (fun y => ccTensorBilinSymm (I := I) g₀ T₁ y) δ →
        ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (p + 3 + a) T₁‖ ≤ B →
        ∀ x : M,
          Integral.Connection.riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + p) x
              ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 p
                (loweredConnDiffSection (I := I) g₁ g₀)).toSection x) ≤ Λ ^ 2 := by
  classical
  intro p
  induction p using Nat.strong_induction_on with
  | _ p IH =>
    -- The Koszul clean-linear-part jet constant and the per-order perturbation-jet sups.
    obtain ⟨Ck, hCk0, hCk⟩ := koszulCombSection_iteratedCovGrad_rfns_le (I := I) g₀ p
    obtain ⟨K, hK0, hK⟩ :=
      loweredConnDiff_t1jet_rfns_familyUniform (I := I) g₀ a ha B (p + 3 + a)
    obtain ⟨Krs, hKrs0, hKrs⟩ :=
      loweredConnDiff_realizeSymm_jet_rfns_familyUniform (I := I) g₀ a ha B (p + 3 + a)
    obtain ⟨Crest, hCrest0, hCrest⟩ :=
      loweredConnDiff_crossCorr_rest_rfns_familyUniform (I := I) g₀ p
    -- The strong-induction lower-order connection-difference sups (one `Λq` per `q < p`).
    have hIH : ∀ q : ℕ, q < p → ∃ Λq : ℝ, 0 ≤ Λq ∧
        ∀ (T₁ : Integral.L2.SmoothCcTensor g₀ 0 2) (g₁ : SmoothRiemannianMetric I M),
          (∀ (y : M) (v w : TangentSpace I y),
            g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T₁ y v w) →
          gFibreOpBound (I := I) g₀ (fun y => ccTensorBilinSymm (I := I) g₀ T₁ y) δ →
          ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (p + 3 + a) T₁‖ ≤ B →
          ∀ x : M,
            Integral.Connection.riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + q) x
                ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 q
                  (loweredConnDiffSection (I := I) g₁ g₀)).toSection x) ≤ Λq ^ 2 := by
      intro q hq
      obtain ⟨Λq, hΛq0, hΛq⟩ := IH q hq
      refine ⟨Λq, hΛq0, fun T₁ g₁ hr hfib hball x => ?_⟩
      -- The order-`q` ball `‖T₁.toHs(q+3+a)‖ ≤ ‖T₁.toHs(p+3+a)‖ ≤ B` (`q < p`).
      have hballq : ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2)
          (q + 3 + a) T₁‖ ≤ B := le_trans (toHs_norm_mono (I := I) g₀ (by omega) T₁) hball
      exact hΛq T₁ g₁ hr hfib hballq x
    -- Uniform Koszul and Rest sums.
    set RKbound : ℝ := Ck * ∑ l ∈ Finset.range (p + 1 + 1), K l with hRKbound
    have hRKbound_nn : 0 ≤ RKbound := by
      rw [hRKbound]; exact mul_nonneg hCk0 (Finset.sum_nonneg fun l _ => hK0 l)
    -- The lower-order connection-difference sups packaged as a function `ΛD : ℕ → ℝ`.
    have hΛDexists : ∀ i : ℕ, i < p → ∃ c : ℝ, 0 ≤ c ∧
        ∀ (T₁ : Integral.L2.SmoothCcTensor g₀ 0 2) (g₁ : SmoothRiemannianMetric I M),
          (∀ (y : M) (v w : TangentSpace I y),
            g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T₁ y v w) →
          gFibreOpBound (I := I) g₀ (fun y => ccTensorBilinSymm (I := I) g₀ T₁ y) δ →
          ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (p + 3 + a) T₁‖ ≤ B →
          ∀ x : M,
            Integral.Connection.riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + i) x
                ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 i
                  (loweredConnDiffSection (I := I) g₁ g₀)).toSection x) ≤ c ^ 2 := hIH
    -- A uniform constant for `rfns(∇^i D)(x)`, `i < p`: `ΛDsq i := (Λi)²`.
    have hΛDsq : ∀ i : ℕ, ∃ c : ℝ, 0 ≤ c ∧
        (i < p → ∀ (T₁ : Integral.L2.SmoothCcTensor g₀ 0 2) (g₁ : SmoothRiemannianMetric I M),
          (∀ (y : M) (v w : TangentSpace I y),
            g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T₁ y v w) →
          gFibreOpBound (I := I) g₀ (fun y => ccTensorBilinSymm (I := I) g₀ T₁ y) δ →
          ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (p + 3 + a) T₁‖ ≤ B →
          ∀ x : M,
            Integral.Connection.riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + i) x
                ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 i
                  (loweredConnDiffSection (I := I) g₁ g₀)).toSection x) ≤ c) := by
      intro i
      by_cases hi : i < p
      · obtain ⟨c, hc0, hc⟩ := hΛDexists i hi
        exact ⟨c ^ 2, by positivity, fun _ T₁ g₁ hr hfib hball x => hc T₁ g₁ hr hfib hball x⟩
      · exact ⟨0, le_refl 0, fun h => absurd h hi⟩
    choose ΛDsq hΛDsq0 hΛDsq_bound using hΛDsq
    -- The uniform Rest sum: `∑_{i<p} ΛDsq i · ∑_{l < p+1-i} Krs l`.
    set RestSum : ℝ := ∑ i ∈ Finset.range p, ΛDsq i * ∑ l ∈ Finset.range (p + 1 - i), Krs l
      with hRestSum
    have hRestSum_nn : 0 ≤ RestSum := by
      rw [hRestSum]
      exact Finset.sum_nonneg fun i _ =>
        mul_nonneg (hΛDsq0 i) (Finset.sum_nonneg fun l _ => hKrs0 l)
    set RestBound : ℝ := Crest * RestSum with hRestBound
    have hRestBound_nn : 0 ≤ RestBound := mul_nonneg hCrest0 hRestSum_nn
    -- The denominator of the Neumann absorption.
    have hden_pos : (0 : ℝ) < 4 - 16 * δ ^ 2 := by nlinarith [hδ0, hδ1]
    set num : ℝ := 2 * RKbound + 16 * RestBound with hnum
    have hnum_nn : 0 ≤ num := by rw [hnum]; linarith [hRKbound_nn, hRestBound_nn]
    refine ⟨Real.sqrt (num / (4 - 16 * δ ^ 2)), Real.sqrt_nonneg _, ?_⟩
    intro T₁ g₁ hr hfib hball x
    rw [Real.sq_sqrt (by positivity)]
    set D := loweredConnDiffSection (I := I) g₁ g₀ with hD
    set rD := Integral.Connection.riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + p) x
      ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 p D).toSection x) with hrD
    have hrD_nn : 0 ≤ rD := Integral.Connection.riemannianFiberNormSq_nonneg _ _ _ _ _
    set rK := Integral.Connection.riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + p) x
      ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 p
        (koszulCombSection (I := I) g₁ g₀ T₁)).toSection x) with hrK
    set rC := Integral.Connection.riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + p) x
      ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 p
        (crossCorrectionSection (I := I) g₁ g₀ T₁)).toSection x) with hrC
    -- KOSZUL ARM: `rK ≤ RKbound`.
    have hkoszul : rK ≤ RKbound := by
      have h := hCk T₁ g₁ hr x
      rw [← hrK] at h
      refine le_trans h ?_
      rw [hRKbound]
      refine mul_le_mul_of_nonneg_left ?_ hCk0
      refine Finset.sum_le_sum (fun l hl => ?_)
      have hlp : l ≤ p + 1 := by have := Finset.mem_range.mp hl; omega
      exact hK T₁ l (by omega) hball x
    -- SECTION IDENTITY: `(2:ℝ) • ∇^p D = ∇^p koszul − (2:ℝ) • ∇^p cross`.
    have hsecid : (2 : ℝ) • PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 p D =
        PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 p (koszulCombSection (I := I) g₁ g₀ T₁)
          - (2 : ℝ) • PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 p
              (crossCorrectionSection (I := I) g₁ g₀ T₁) := by
      have h2D : (2 : ℝ) • PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 p D =
          PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 p ((2 : ℝ) • D) :=
        (DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization.iteratedCovGrad_smul
          (I := I) g₀ 0 3 p (2 : ℝ) D).symm
      have hkos : (2 : ℝ) • D = koszulCombSection (I := I) g₁ g₀ T₁
          - (2 : ℝ) • crossCorrectionSection (I := I) g₁ g₀ T₁ := by
        rw [hD, koszulCombSection]; abel
      rw [h2D, hkos, PDE.RicciFlow.iteratedCovGrad_sub,
        (DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization.iteratedCovGrad_smul
          (I := I) g₀ 0 3 p (2 : ℝ) (crossCorrectionSection (I := I) g₁ g₀ T₁))]
    -- Read the section identity pointwise and through `rfns`.
    have hpt : ((2 : ℝ) • PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 p D).toSection x =
        (PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 p
            (koszulCombSection (I := I) g₁ g₀ T₁)).toSection x
          - ((2 : ℝ) • PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 p
              (crossCorrectionSection (I := I) g₁ g₀ T₁)).toSection x := by
      rw [hsecid, Integral.L2.SmoothCcTensor.toSection_sub, ContMDiffSection.coe_sub,
        Pi.sub_apply]
    have h4D : Integral.Connection.riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + p) x
        (((2 : ℝ) • PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 p D).toSection x) = 4 * rD := by
      rw [show (((2 : ℝ) • PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 p D).toSection x :
            TensorRSSpace 0 (3 + p) I x) =
          (2 : ℝ) • (PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 p D).toSection x from by
            rw [Integral.L2.SmoothCcTensor.toSection_smul]; rfl,
        rfns_smul_local, ← hrD]
      norm_num
    have h2C : Integral.Connection.riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + p) x
        (((2 : ℝ) • PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 p
          (crossCorrectionSection (I := I) g₁ g₀ T₁)).toSection x) = 4 * rC := by
      rw [show (((2 : ℝ) • PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 p
            (crossCorrectionSection (I := I) g₁ g₀ T₁)).toSection x : TensorRSSpace 0 (3 + p) I x) =
          (2 : ℝ) • (PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 p
            (crossCorrectionSection (I := I) g₁ g₀ T₁)).toSection x from by
            rw [Integral.L2.SmoothCcTensor.toSection_smul]; rfl,
        rfns_smul_local, ← hrC]
      norm_num
    have hsub : 4 * rD ≤ 2 * rK + 8 * rC := by
      have hle := Integral.Connection.riemannianFiberNormSq_sub_le (I := I) (M := M) g₀ 0 (3 + p) x
        ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 p
          (koszulCombSection (I := I) g₁ g₀ T₁)).toSection x)
        (((2 : ℝ) • PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 p
          (crossCorrectionSection (I := I) g₁ g₀ T₁)).toSection x)
      rw [h2C, ← hrK] at hle
      have heq : Integral.Connection.riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + p) x
          ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 p
              (koszulCombSection (I := I) g₁ g₀ T₁)).toSection x
            - (((2 : ℝ) • PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 p
              (crossCorrectionSection (I := I) g₁ g₀ T₁)).toSection x)) = 4 * rD := by
        rw [← hpt]; exact h4D
      rw [heq] at hle
      linarith
    -- CROSS ARM Top/Rest split.
    -- Rewrite `cross` as the parallel cometric contraction.
    have hcrosseq : crossCorrectionSection (I := I) g₁ g₀ T₁ =
        Integral.Connection.crossCorrParallelContraction (I := I) g₀ (a := 0) (b := 0)
          (realizeSymmCcTensor (I := I) g₀ T₁)
          (permuteCcTensor (I := I) g₀ c[(0 : Fin 3), 1, 2] D) :=
      (Integral.Connection.crossCorrParallelContraction_eq_crossCorrectionSection
        (I := I) g₀ g₁ T₁).symm
    set Full : Integral.L2.SmoothCcTensor g₀ 0 (3 + p) :=
      PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 (3 + 0 + 0) p
        (Integral.Connection.crossCorrParallelContraction (I := I) g₀ (a := 0) (b := 0)
          (realizeSymmCcTensor (I := I) g₀ T₁)
          (permuteCcTensor (I := I) g₀ c[(0 : Fin 3), 1, 2] D)) with hFull
    set Top : Integral.L2.SmoothCcTensor g₀ 0 (3 + p) :=
      Integral.Connection.crossCorrParallelContraction (I := I) g₀ (a := 0) (b := p)
        (realizeSymmCcTensor (I := I) g₀ T₁)
        (PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 p
          (permuteCcTensor (I := I) g₀ c[(0 : Fin 3), 1, 2] D)) with hTop
    -- The reduced-degree abbreviations of the three cross-cell fibre norms.
    set rFull := Integral.Connection.riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + p) x
      (Full.toSection x) with hrFull
    set rRest := Integral.Connection.riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + p) x
      ((Full - Top).toSection x) with hrRest
    set rTop := Integral.Connection.riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + p) x
      (Top.toSection x) with hrTop
    -- `rfns(∇^p cross)(x) = rfns(Full)(x) = rFull`.
    have hrC_full : rC = rFull := by
      rw [hrC, hrFull, hFull]
      congr 1
      rw [hcrosseq]
    -- Top cell sharp `δ²` bound, re-indexed to `rD`.
    have hTopbound : rTop ≤ δ ^ 2 * rD := by
      have h := DifferentialGeometry.PDE.DeTurck.crossCorrParallelContraction_rfns_le_sq_passenger
        (I := I) g₀ p T₁ hfib
        (PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 p
          (permuteCcTensor (I := I) g₀ c[(0 : Fin 3), 1, 2] D)) x
      rw [← hTop] at h
      rw [hrTop]
      refine le_trans h ?_
      rw [hrD,
        DifferentialGeometry.PDE.DeTurck.riemannianFiberNormSq_iteratedCovGrad_permuteCcTensor
          (I := I) g₀ c[(0 : Fin 3), 1, 2] D p x]
    -- Rest cell bound via the posit + IH + realize-jet sups.
    have hRestbound : rRest ≤ RestBound := by
      have h := hCrest T₁ g₁ x
      rw [← hFull, ← hTop] at h
      rw [hrRest]
      refine le_trans h ?_
      rw [hRestBound, hRestSum]
      refine mul_le_mul_of_nonneg_left ?_ hCrest0
      refine Finset.sum_le_sum (fun i hi => ?_)
      have hip : i < p := Finset.mem_range.mp hi
      have hDi : Integral.Connection.riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + i) x
          ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 i D).toSection x) ≤ ΛDsq i :=
        hΛDsq_bound i hip T₁ g₁ hr hfib hball x
      have hRSi : (∑ l ∈ Finset.range (p + 1 - i),
            Integral.Connection.riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
              ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l
                (realizeSymmCcTensor (I := I) g₀ T₁)).toSection x)) ≤
          ∑ l ∈ Finset.range (p + 1 - i), Krs l := by
        refine Finset.sum_le_sum (fun l hl => ?_)
        have hlpi : l < p + 1 - i := Finset.mem_range.mp hl
        exact hKrs T₁ l (by omega) hball x
      exact mul_le_mul hDi hRSi (Finset.sum_nonneg fun l _ =>
        Integral.Connection.riemannianFiberNormSq_nonneg _ _ _ _ _) (hΛDsq0 i)
    -- `rFull ≤ 2·rRest + 2·rTop`.
    have hFullsplit : rFull ≤ 2 * rRest + 2 * rTop := by
      have hsplit : Full.toSection x = (Full - Top).toSection x + Top.toSection x := by
        rw [Integral.L2.SmoothCcTensor.toSection_sub, ContMDiffSection.coe_sub, Pi.sub_apply]
        abel
      rw [hrFull, hrRest, hrTop, hsplit]
      exact Integral.Connection.riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 0 (3 + p) x
        ((Full - Top).toSection x) (Top.toSection x)
    -- Stitch the cross arm: `rC ≤ 2·RestBound + 2·δ²·rD`.
    have hcross : rC ≤ 2 * RestBound + 2 * (δ ^ 2 * rD) := by
      rw [hrC_full]
      linarith [hFullsplit, hTopbound, hRestbound]
    -- NEUMANN ABSORPTION: `(4 − 16δ²) · rD ≤ num`, then divide by the positive denominator.
    rw [le_div_iff₀ hden_pos, hnum]
    have hexp : rD * (4 - 16 * δ ^ 2) = 4 * rD - 16 * (δ ^ 2 * rD) := by ring
    rw [hexp]
    linarith [hsub, hcross, hkoszul]

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization in
set_option linter.unusedSectionVars false in
/-- **(POSIT — the family-uniform per-order pointwise fibre sup of the `g₀`-lowered
connection-difference jets.)**  For the fibre-small
(`gFibreOpBound g₀ (ccTensorBilinSymm g₀ T₁) δ`, `δ < 1/2`) supercritically `H^{p + 3 + a}`-bounded
(`2a > finrank + 4`) realized perturbation family, the order-`p` intrinsic squared fibre norm of the
`g₀`-lowered connection difference `D = loweredConnDiffSection g₁ g₀` (its order-`p` covariant
gradient `∇^p D`, a `(0, 3 + p)`-tensor) is uniformly bounded by a single constant `Λ²` over the
manifold and the family: `∀ x, rfns(∇^p (loweredConnDiffSection g₁ g₀))(x) ≤ Λ²`.

This is the **order-`p ≥ 1` generalization** of the proven-`p = 0` Neumann-absorbed fibre sup
`exists_loweredConnDiffSection_rfns_fibre_sup_le` (`CrossCorrectionContractionTopRest.lean`).  The
order-`p` differentiated-Koszul section identity
`2·∇^p D = ∇^p (koszulComb) − 2·∇^p (crossCorrection)` controls `rfns(∇^p D)` by the pointwise
clean-linear-part jet brick `koszulCombSection_iteratedCovGrad_rfns_le` (the `≤ (p + 1)`-jet of the
realized perturbation, proven) divided out by the order-uniform `(1 − 2δ) > 0` Neumann absorption of
the cross-correction contraction (`crossCorrParallelContraction_rfns_le_sq_passenger`, sharp `δ²`,
proven), the realized `≤ (p + 1)`-jet itself being dominated family-uniformly by the sharp-order
supercritical jet embedding `exists_iteratedCovGradJetSum_le_toHs_sharpOrder`.

**Non-vacuity.**  A genuine fibre sup (`Λ = 0` forces `∇^p D ≡ 0`, false whenever `g₁ ≠ g₀`).  At
`T₁ = 0` realized (`g₁ = g₀`) the connection difference vanishes and `Λ = 0` works.  Its body is
`sorry`: the genuine order-`p` differentiated-Koszul / Neumann-absorption fibre sup (consumers
transitively depend on `sorryAx` through this posited per-order engine). -/
private theorem loweredConnDiff_iteratedCovGrad_rfns_fibre_sup
    (g₀ : SmoothRiemannianMetric I M) (p : ℕ) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1 / 2) (B : ℝ)
    (a : ℕ) (ha : 2 * a > Module.finrank ℝ E + 4) :
    ∃ Λ : ℝ, 0 ≤ Λ ∧
      ∀ (T₁ : Integral.L2.SmoothCcTensor g₀ 0 2) (g₁ : SmoothRiemannianMetric I M),
        (∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T₁ y v w) →
        gFibreOpBound (I := I) g₀ (fun y => ccTensorBilinSymm (I := I) g₀ T₁ y) δ →
        ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (p + 3 + a) T₁‖ ≤ B →
        ∀ x : M,
          Integral.Connection.riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + p) x
              ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 p
                (loweredConnDiffSection (I := I) g₁ g₀)).toSection x) ≤ Λ ^ 2 :=
  loweredConnDiff_iteratedCovGrad_rfns_fibre_sup_aux (I := I) g₀ δ hδ0 hδ1 B a ha p

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization in
set_option linter.unusedSectionVars false in
/-- **The family-uniform per-order pointwise fibre sup of the realized-perturbation jets.**  For the
supercritically `H^{a + 2}`-bounded (`2a > finrank + 4`) realized perturbation family and every order
`i ≤ 2`, the order-`i` intrinsic squared fibre norm of the symmetric realized tensor
`realizeSymmCcTensor g₀ T₁` (its order-`i` covariant gradient `∇^i (realizeSymm T₁)`, a
`(0, 2 + i)`-tensor) is uniformly bounded by a single constant `(C · max B 0)²` over the manifold and
the family: `∀ x, rfns(∇^i (realizeSymm T₁))(x) ≤ (C · max B 0)²` whenever `‖T₁.toHs(a + 2)‖ ≤ B`.

The order-`i` summand (`i ∈ {0, 1, 2}`) of the covariant 2-jet sum
`iteratedCovGradJetSum (realizeSymm T₁)` is `√rfns(∇^i (realizeSymm T₁))(x)`
(`norm_toSection_eq_sqrt_riemannianFiberNormSq_installed`), hence at most the whole nonnegative jet
sum, which is dominated by `C · ‖T₁.toHs(a + 2)‖ ≤ C · max B 0` through the sharp-order realized jet
embedding `exists_realizedJetSum_le_toHs_sharpOrder`; squaring gives the per-order fibre sup.  Proved
outright; no posit. -/
private theorem realizeSymm_iteratedCovGrad_rfns_fibre_sup
    (g₀ : SmoothRiemannianMetric I M) (B : ℝ) (a : ℕ) (ha : 2 * a > Module.finrank ℝ E + 4) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (T₁ : Integral.L2.SmoothCcTensor g₀ 0 2),
        ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (a + 2) T₁‖ ≤ B →
        ∀ (i : ℕ), i < 3 → ∀ x : M,
          Integral.Connection.riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
              ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i
                (realizeSymmCcTensor (I := I) g₀ T₁)).toSection x) ≤ (C * max B 0) ^ 2 := by
  classical
  have ha2 : 2 * (a + 2) > Module.finrank ℝ E + 4 := by omega
  obtain ⟨C, hC0, hC⟩ := exists_realizedJetSum_le_toHs_sharpOrder (I := I) g₀ (a + 2) ha2
  refine ⟨C, hC0.le, fun T₁ hB i hi x => ?_⟩
  set Q : ℝ := C * max B 0 with hQ
  have hQ_nn : 0 ≤ Q := by rw [hQ]; positivity
  have hjet : iteratedCovGradJetSum (I := I) g₀ (realizeSymmCcTensor (I := I) g₀ T₁) x ≤ Q := by
    refine le_trans (hC T₁ x) ?_
    rw [hQ]
    exact mul_le_mul_of_nonneg_left (le_trans hB (le_max_left _ _)) hC0.le
  -- Split the covariant `2`-jet sum into its three terms `j = 0, 1, 2`, each `√rfns(∇^j ⋯)(x)`.
  have hsplit : iteratedCovGradJetSum (I := I) g₀ (realizeSymmCcTensor (I := I) g₀ T₁) x =
      Real.sqrt (Integral.Connection.riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + 0) x
          ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 0
            (realizeSymmCcTensor (I := I) g₀ T₁)).toSection x))
        + Real.sqrt (Integral.Connection.riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + 1) x
            ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 1
              (realizeSymmCcTensor (I := I) g₀ T₁)).toSection x))
        + Real.sqrt (Integral.Connection.riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + 2) x
            ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 2
              (realizeSymmCcTensor (I := I) g₀ T₁)).toSection x)) := by
    rw [iteratedCovGradJetSum, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one,
      DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck.norm_toSection_eq_sqrt_riemannianFiberNormSq_installed
        (I := I) (M := M) g₀ 0 (2 + 0)
        (PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 0 (realizeSymmCcTensor (I := I) g₀ T₁)) x,
      DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck.norm_toSection_eq_sqrt_riemannianFiberNormSq_installed
        (I := I) (M := M) g₀ 0 (2 + 1)
        (PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 1 (realizeSymmCcTensor (I := I) g₀ T₁)) x,
      DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck.norm_toSection_eq_sqrt_riemannianFiberNormSq_installed
        (I := I) (M := M) g₀ 0 (2 + 2)
        (PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 2 (realizeSymmCcTensor (I := I) g₀ T₁)) x]
  have h0 : 0 ≤ Real.sqrt (Integral.Connection.riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + 0) x
      ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 0
        (realizeSymmCcTensor (I := I) g₀ T₁)).toSection x)) := Real.sqrt_nonneg _
  have h1 : 0 ≤ Real.sqrt (Integral.Connection.riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + 1) x
      ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 1
        (realizeSymmCcTensor (I := I) g₀ T₁)).toSection x)) := Real.sqrt_nonneg _
  have h2 : 0 ≤ Real.sqrt (Integral.Connection.riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + 2) x
      ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 2
        (realizeSymmCcTensor (I := I) g₀ T₁)).toSection x)) := Real.sqrt_nonneg _
  -- The order-`i` summand (`i < 3`) is `≤` the whole nonnegative jet sum `≤ Q`.
  have hsqrt : Real.sqrt (Integral.Connection.riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
        ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i
          (realizeSymmCcTensor (I := I) g₀ T₁)).toSection x)) ≤
      iteratedCovGradJetSum (I := I) g₀ (realizeSymmCcTensor (I := I) g₀ T₁) x := by
    rw [hsplit]
    interval_cases i <;> linarith
  have hrnn : 0 ≤ Integral.Connection.riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
      ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i
        (realizeSymmCcTensor (I := I) g₀ T₁)).toSection x) :=
    Integral.Connection.riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + i) x _
  have hsq : (Real.sqrt (Integral.Connection.riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
        ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i
          (realizeSymmCcTensor (I := I) g₀ T₁)).toSection x))) ^ 2 =
      Integral.Connection.riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
        ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i
          (realizeSymmCcTensor (I := I) g₀ T₁)).toSection x) := Real.sq_sqrt hrnn
  have hsqrt_nn : 0 ≤ Real.sqrt (Integral.Connection.riemannianFiberNormSq (I := I) (M := M)
      g₀ 0 (2 + i) x ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i
        (realizeSymmCcTensor (I := I) g₀ T₁)).toSection x)) := Real.sqrt_nonneg _
  nlinarith [hsqrt, hjet, hsq, hsqrt_nn, hQ_nn]

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization in
set_option linter.unusedSectionVars false in
/-- **The family-uniform pointwise fibre-norm sup of the field-difference gradient section.**  For
the fibre-small (`gFibreOpBound g₀ (ccTensorBilinSymm g₀ T₁) δ`, `δ < 1/2`) supercritically
`H^{a + 2}`- and `H^{6 + a}`-bounded (`2a > finrank + 4`) realized perturbation family, the order-`0`
intrinsic squared fibre norm of the field-difference gradient section `fieldDiffGradSection g₀ g₁ g₀
g_bg` (fibre `g₀(∇^{g₀}_v (W₁ − W₀), w)`, `Wᵢ = deTurckVF gᵢ g_bg`) is uniformly bounded by a single
constant `Λ` over the manifold and the family:
`∀ x, rfns(fieldDiffGradSection g₀ g₁ g₀ g_bg)(x) ≤ Λ`.

The `l = 0` covariant-Leibniz product grid `fieldDiffGradSection_iteratedCovGrad_rfns_productGrid_le`
dominates the fibre norm pointwise by the diagonal product of the realized-perturbation jets
(orders `i ≤ 2`, the difference factor) against the `g₀`-lowered connection-difference jets
(orders `m ≤ 3`, the fixed-pair factor); each realized-perturbation jet fibre norm is bounded by the
sharp-order supercritical fibre sup `realizeSymm_iteratedCovGrad_rfns_fibre_sup` (using `‖T₁.toHs(a +
2)‖ ≤ B`), and each connection-difference jet fibre norm by the per-order fibre sup
`loweredConnDiff_iteratedCovGrad_rfns_fibre_sup` (each order `m ≤ 3` using `‖T₁.toHs(m + 3 + a)‖ ≤
‖T₁.toHs(6 + a)‖ ≤ B`, `toHs_norm_mono`), so the finite product grid telescopes to a single
family-uniform constant `Λ`. -/
private theorem fieldDiffGradSection_rfns_fibre_sup_pointwise
    (g₀ g_bg : SmoothRiemannianMetric I M) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1 / 2) (B : ℝ)
    (a : ℕ) (ha : 2 * a > Module.finrank ℝ E + 4) :
    ∃ Λ : ℝ, 0 ≤ Λ ∧
      ∀ (T₁ : Integral.L2.SmoothCcTensor g₀ 0 2) (g₁ : SmoothRiemannianMetric I M),
        (∀ (x : M) (v w : TangentSpace I x),
          g₁.inner x v w = g₀.inner x v w + ccTensorBilinSymm (I := I) g₀ T₁ x v w) →
        gFibreOpBound (I := I) g₀ (fun y => ccTensorBilinSymm (I := I) g₀ T₁ y) δ →
        ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (a + 2) T₁‖ ≤ B →
        ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (6 + a) T₁‖ ≤ B →
        ∀ x : M,
          Integral.Connection.riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x
              ((fieldDiffGradSection (I := I) g₀ g₁ g₀ g_bg).toSection x) ≤ Λ := by
  classical
  obtain ⟨Cgrid, hCgrid0, hgrid⟩ :=
    fieldDiffGradSection_iteratedCovGrad_rfns_productGrid_le (I := I) g₀ g_bg δ hδ0 hδ1 B a ha 0
  obtain ⟨Cr, hCr0, hCr⟩ := realizeSymm_iteratedCovGrad_rfns_fibre_sup (I := I) g₀ B a ha
  -- The connection-difference per-order fibre sups, one constant per order `m ≤ 3`.
  choose ΛD hΛD0 hΛD using fun m : ℕ =>
    loweredConnDiff_iteratedCovGrad_rfns_fibre_sup (I := I) g₀ m δ hδ0 hδ1 B a ha
  -- The grid product, with each factor replaced by its uniform sup, is a single finite constant.
  set Rsup : ℝ := (Cr * max B 0) ^ 2 with hRsup
  have hRsup0 : 0 ≤ Rsup := by rw [hRsup]; positivity
  set Bound : ℝ := Cgrid * ∑ i ∈ Finset.range (0 + 2 + 1),
      Rsup * ∑ m ∈ Finset.range (0 + 3 + 1 - i), (ΛD m) ^ 2 with hBound
  have hBound0 : 0 ≤ Bound := by
    rw [hBound]
    refine mul_nonneg hCgrid0 (Finset.sum_nonneg fun i _ => ?_)
    exact mul_nonneg hRsup0 (Finset.sum_nonneg fun m _ => sq_nonneg _)
  refine ⟨Bound, hBound0, fun T₁ g₁ hg₁ hδbnd hB hBjet x => ?_⟩
  -- Read the `l = 0` grid and the order-`0` identity `∇^0 fieldDiffGradSection = fieldDiffGradSection`.
  have hg := hgrid T₁ g₁ hg₁ hδbnd hB x
  rw [show PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 0
      (fieldDiffGradSection (I := I) g₀ g₁ g₀ g_bg) = fieldDiffGradSection (I := I) g₀ g₁ g₀ g_bg
      from rfl] at hg
  -- The grid's RHS index ranges (`l = 0`): `i ∈ {0,1,2}`, `m ∈ {0,…,3-i}`.
  refine le_trans hg ?_
  rw [hBound]
  refine mul_le_mul_of_nonneg_left ?_ hCgrid0
  refine Finset.sum_le_sum (fun i hi => ?_)
  have hi3 : i < 3 := by simpa using Finset.mem_range.mp hi
  -- The realized-perturbation factor `rfns(∇^i realizeSymm T₁)(x) ≤ Rsup`.
  have hrz : Integral.Connection.riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
      ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i
        (realizeSymmCcTensor (I := I) g₀ T₁)).toSection x) ≤ Rsup := by
    rw [hRsup]; exact hCr T₁ hB i hi3 x
  -- The inner connection-difference sum is `≤ ∑_{m} ΛD m ^ 2`.
  have hinner : (∑ m ∈ Finset.range (0 + 3 + 1 - i),
        Integral.Connection.riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + m) x
          ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 m
            (loweredConnDiffSection (I := I) g₁ g₀)).toSection x)) ≤
      ∑ m ∈ Finset.range (0 + 3 + 1 - i), (ΛD m) ^ 2 := by
    refine Finset.sum_le_sum (fun m hm => ?_)
    have hm4 : m < 0 + 3 + 1 - i := Finset.mem_range.mp hm
    -- Each order-`m` connection-difference jet sup uses `‖T₁.toHs(m+3+a)‖ ≤ ‖T₁.toHs(6+a)‖ ≤ B`
    -- (`m ≤ 3` since `m < 4 - i ≤ 4` and `i ≥ 0`, so `m + 3 + a ≤ 6 + a`).
    have hball : ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (m + 3 + a) T₁‖ ≤
        B := le_trans (toHs_norm_mono (I := I) g₀ (by omega) T₁) hBjet
    exact hΛD m T₁ g₁ hg₁ hδbnd hball x
  have hinner_nn : 0 ≤ ∑ m ∈ Finset.range (0 + 3 + 1 - i),
      Integral.Connection.riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + m) x
        ((PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 3 m
          (loweredConnDiffSection (I := I) g₁ g₀)).toSection x) :=
    Finset.sum_nonneg fun m _ => Integral.Connection.riemannianFiberNormSq_nonneg _ _ _ _ _
  exact mul_le_mul hrz hinner hinner_nn hRsup0

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization in
set_option linter.unusedSectionVars false in
/-- **The family-uniform `g₀`-fibre value sup of the field-difference covariant gradient.**
For the fibre-small (`gFibreOpBound g₀ (ccTensorBilinSymm g₀ T₁) δ`, `δ < 1/2`) supercritically
`H^{a+2}`- and `H^{6 + a}`-bounded (`2a > finrank + 4`) realized perturbation family, the
`g₀`-Levi-Civita covariant gradient of the DeTurck field difference `W₁ − W₀`, `Wᵢ = deTurckVF gᵢ
g_bg`, obeys the family-uniform value bound
`√(g₀ x (∇^{g₀}_v (W₁ − W₀)) (∇^{g₀}_v (W₁ − W₀))) ≤ Λ · √(g₀ x v v)`
for a single constant `Λ ≥ 0` over the manifold and the family.

The bilinear value `g₀(∇^{g₀}_v (W₁ − W₀), w)` is the fibre of the field-difference gradient section
`fieldDiffGradSection g₀ g₁ g₀ g_bg` (`fieldDiffGradSection_toModel_apply`, `fieldDiffGradBilin_apply`),
whose pointwise intrinsic fibre-norm sup `fieldDiffGradSection_rfns_fibre_sup_pointwise` is
family-uniform.  The `(0,2)` `g₀`-fibre Cauchy–Schwarz `ccTensorBilin_sq_le_gInner_riemannianFiberNormSq`
folds the fibre norm into the bilinear value bound `|g₀(∇^{g₀}_v (W₁ − W₀), w)| ≤ √Λ_rfns · √(g₀ v v) ·
√(g₀ w w)`, and the `g₀`-Riesz lift `sqrt_gInner_self_le_of_forall_inner_le` (at fixed `v`) raises the
gradient self-norm to `√(g₀ (∇^{g₀}_v (W₁ − W₀))²) ≤ √Λ_rfns · √(g₀ v v)`, so `Λ = √Λ_rfns`.

The **higher Sobolev ball** `‖T₁.toHs(6 + a)‖ ≤ B` is the `l = 0` instance of the sibling
field-difference jet engine's second ball `‖T₁.toHs(l + 3 + 3 + a)‖ ≤ B`
(`exists_iteratedCovGrad_deTurckVF_le_jetSum`): the covariant-Leibniz expansion of the gradient of the
inverse-Gram-weighted connection-difference trace reaches the realized `4`-jet, which the supercritical
`H^{a + 2} ↪ C²` embedding alone does not control.

**Non-vacuity.**  Genuine (`Λ = 0` forces `∇^{g₀}(W₁ − W₀) ≡ 0`, false whenever `W₁ ≠ W₀`).  At
`g₁ = g₀` realized (`T₁ = 0`) the field difference is the zero section and `Λ = 0` works. -/
theorem exists_covGrad_deTurckVF_sub_gNorm_sup_le
    (g₀ g_bg : SmoothRiemannianMetric I M) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1 / 2) (B : ℝ)
    (a : ℕ) (ha : 2 * a > Module.finrank ℝ E + 4) :
    ∃ Λ : ℝ, 0 ≤ Λ ∧
      ∀ (T₁ : Integral.L2.SmoothCcTensor g₀ 0 2) (g₁ : SmoothRiemannianMetric I M),
        (∀ (x : M) (v w : TangentSpace I x),
          g₁.inner x v w = g₀.inner x v w + ccTensorBilinSymm (I := I) g₀ T₁ x v w) →
        gFibreOpBound (I := I) g₀ (fun y => ccTensorBilinSymm (I := I) g₀ T₁ y) δ →
        ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (a + 2) T₁‖ ≤ B →
        ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (6 + a) T₁‖ ≤ B →
        ∀ (x : M) (v : TangentSpace I x),
          Real.sqrt (g₀.inner x
              ((LeviCivita (I := I) g₀)
                ((deTurckVF (I := I) g₁ g_bg - deTurckVF (I := I) g₀ g_bg :
                  Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) : ∀ x : M, TangentSpace I x) x v)
              ((LeviCivita (I := I) g₀)
                ((deTurckVF (I := I) g₁ g_bg - deTurckVF (I := I) g₀ g_bg :
                  Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) : ∀ x : M, TangentSpace I x) x v)) ≤
            Λ * Real.sqrt (g₀.inner x v v) := by
  classical
  obtain ⟨Λ_rfns, hΛ_rfns0, hΛ_rfns⟩ :=
    fieldDiffGradSection_rfns_fibre_sup_pointwise (I := I) g₀ g_bg δ hδ0 hδ1 B a ha
  refine ⟨Real.sqrt Λ_rfns, Real.sqrt_nonneg _, fun T₁ g₁ hg₁ hδbnd hB hBjet x v => ?_⟩
  -- The gradient vector `z := ∇^{g₀}_v (W₁ − W₀) x`.
  set z : TangentSpace I x :=
    (LeviCivita (I := I) g₀)
      ((deTurckVF (I := I) g₁ g_bg - deTurckVF (I := I) g₀ g_bg :
        Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) : ∀ x : M, TangentSpace I x) x v with hz
  have hsv : 0 ≤ Real.sqrt (g₀.inner x v v) := Real.sqrt_nonneg _
  -- The fibre-norm sup of the field-difference gradient section at `x`.
  have hrfns := hΛ_rfns T₁ g₁ hg₁ hδbnd hB hBjet x
  have hrfns_nn : 0 ≤ Integral.Connection.riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x
      ((fieldDiffGradSection (I := I) g₀ g₁ g₀ g_bg).toSection x) :=
    Integral.Connection.riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 2 x _
  -- `K v := √Λ_rfns · √(g₀ v v)` is the Riesz constant for the functional `c ↦ g₀(z, c)`.
  refine sqrt_gInner_self_le_of_forall_inner_le (I := I) g₀ x z
    (K := Real.sqrt Λ_rfns * Real.sqrt (g₀.inner x v v)) (by positivity) (fun c => ?_)
  -- `g₀(z, c) = ccTensorBilin g₀ (fieldDiffGradSection g₀ g₁ g₀ g_bg) x v c`.
  have hbilin : g₀.inner x z c =
      ccTensorBilin (I := I) g₀ (fieldDiffGradSection (I := I) g₀ g₁ g₀ g_bg) x v c := by
    rw [ccTensorBilin_apply]
    show _ = ccTensorModel (I := I) g₀ (fieldDiffGradSection (I := I) g₀ g₁ g₀ g_bg) x ![v, c]
    rw [ccTensorModel, ccTensorMultilinear_apply, fieldDiffGradSection_toModel_apply,
      fieldDiffGradBilin_apply]
  -- The `(0,2)` `g₀`-fibre Cauchy–Schwarz: `(ccTensorBilin)² ≤ (g₀ v v)·(g₀ c c)·rfns`.
  have hcs := ccTensorBilin_sq_le_gInner_riemannianFiberNormSq (I := I) g₀
    (fieldDiffGradSection (I := I) g₀ g₁ g₀ g_bg) x v c
  have hvv_nn : 0 ≤ g₀.inner x v v :=
    DifferentialGeometry.Analysis.Laplacian.metric_inner_self_nonneg (I := I) (M := M) g₀ x v
  have hcc_nn : 0 ≤ g₀.inner x c c :=
    DifferentialGeometry.Analysis.Laplacian.metric_inner_self_nonneg (I := I) (M := M) g₀ x c
  rw [hbilin]
  -- `|B| = √(B²) ≤ √((g₀ v v)·(g₀ c c)·Λ_rfns) = √Λ_rfns · √(g₀ v v) · √(g₀ c c)`.
  have habs : |ccTensorBilin (I := I) g₀ (fieldDiffGradSection (I := I) g₀ g₁ g₀ g_bg) x v c| =
      Real.sqrt
        ((ccTensorBilin (I := I) g₀ (fieldDiffGradSection (I := I) g₀ g₁ g₀ g_bg) x v c) ^ 2) := by
    rw [Real.sqrt_sq_eq_abs]
  rw [habs]
  have hstep : Real.sqrt
        ((ccTensorBilin (I := I) g₀ (fieldDiffGradSection (I := I) g₀ g₁ g₀ g_bg) x v c) ^ 2) ≤
      Real.sqrt (g₀.inner x v v * g₀.inner x c c * Λ_rfns) := by
    refine Real.sqrt_le_sqrt (le_trans hcs ?_)
    refine mul_le_mul_of_nonneg_left hrfns ?_
    exact mul_nonneg hvv_nn hcc_nn
  refine le_trans hstep ?_
  -- `√((g₀ v v)·(g₀ c c)·Λ_rfns) = √Λ_rfns · √(g₀ v v) · √(g₀ c c)`, then reassociate to `K · √(g₀ c c)`.
  rw [show g₀.inner x v v * g₀.inner x c c * Λ_rfns =
      Λ_rfns * (g₀.inner x v v) * (g₀.inner x c c) from by ring]
  rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity)]

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization in
set_option linter.unusedSectionVars false in
/-- **(POSIT — the family-uniform pointwise `g₀`-Cauchy–Schwarz value bound of the
field-difference gradient bilinear form.)**  For the fibre-small
(`gFibreOpBound g₀ (ccTensorBilinSymm g₀ T₁) δ`, `δ < 1/2`) supercritically `H^{a+2}`-bounded
(`2a > finrank + 4`) realized perturbation family, the extracted bilinear form
`ccTensorBilin g₀ (fieldDiffGradSection g₀ g₁ g₀ g_bg) x` — value `g₀(∇^{g₀}_v (W₁ − W₀), w)`,
`Wᵢ = deTurckVF gᵢ g_bg` — obeys the family-uniform pointwise `g₀`-Cauchy–Schwarz value bound
`|·| ≤ Λ₀ · √(g₀ x v v) · √(g₀ x w w)` for a single constant `Λ₀ ≥ 0` over the manifold and the
family.

This is the order-`0` `C⁰` value of the `g₀`-Levi-Civita covariant gradient of the field difference
`W₁ − W₀`; the field difference is the inverse-Gram-weighted trace of the pair connection difference
(`deTurckVF_sub_apply_eq_trace_connDiff`), a first-order Christoffel-difference quantity, so its
covariant gradient is `C⁰`-controlled family-uniformly through the supercritical `H^{a+2} ↪ C¹`
embedding of the metric jet (`iteratedCovGradJetSum_le_toHs`, `2a > finrank + 4`).

**Non-vacuity.**  Vanishes at `T₁ = 0` realized (`g₁ = g₀`, `W₁ = W₀`, the bilinear form is `0`,
`Λ₀ = 0` works); genuine (`Λ₀ = 0` forces the value `≡ 0`, false whenever `g₁ ≠ g₀`).

Glued (consumers transitively depend on `sorryAx` only through the posited bedrock engine): the
bilinear value rewrites — `ccTensorBilin_apply`, `ccTensorModel`, `ccTensorMultilinear_apply`,
`fieldDiffGradSection_toModel_apply`, `fieldDiffGradBilin_apply` — to
`g₀(∇^{g₀}_v (W₁ − W₀), w)`, `Wᵢ = deTurckVF gᵢ g_bg`; the `g₀`-Cauchy–Schwarz
(`abs_metric_inner_le_sqrt_metric_quadratic`) folds it to
`√(g₀ (∇^{g₀}_v (W₁ − W₀))²) · √(g₀ w w)`, and the field-difference covariant-gradient `g₀`-fibre
value sup `exists_covGrad_deTurckVF_sub_gNorm_sup_le` bounds the gradient factor by
`Λ · √(g₀ v v)`. -/
theorem exists_fieldDiffGradBilin_gcs_value_bound
    (g₀ g_bg : SmoothRiemannianMetric I M) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1 / 2) (B : ℝ)
    (a : ℕ) (ha : 2 * a > Module.finrank ℝ E + 4) :
    ∃ Λ₀ : ℝ, 0 ≤ Λ₀ ∧
      ∀ (T₁ : Integral.L2.SmoothCcTensor g₀ 0 2) (g₁ : SmoothRiemannianMetric I M),
        (∀ (x : M) (v w : TangentSpace I x),
          g₁.inner x v w = g₀.inner x v w + ccTensorBilinSymm (I := I) g₀ T₁ x v w) →
        gFibreOpBound (I := I) g₀ (fun y => ccTensorBilinSymm (I := I) g₀ T₁ y) δ →
        ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (a + 2) T₁‖ ≤ B →
        ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (6 + a) T₁‖ ≤ B →
        ∀ (x : M) (v w : TangentSpace I x),
          |ccTensorBilin (I := I) g₀ (fieldDiffGradSection (I := I) g₀ g₁ g₀ g_bg) x v w| ≤
            Λ₀ * Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x w w) := by
  obtain ⟨Λ, hΛ0, hΛ⟩ :=
    exists_covGrad_deTurckVF_sub_gNorm_sup_le (I := I) g₀ g_bg δ hδ0 hδ1 B a ha
  refine ⟨Λ, hΛ0, fun T₁ g₁ hg₁ hδbnd hB₁ hBjet x v w => ?_⟩
  have hred : ccTensorBilin (I := I) g₀ (fieldDiffGradSection (I := I) g₀ g₁ g₀ g_bg) x v w =
      g₀.inner x ((LeviCivita (I := I) g₀)
          ((deTurckVF (I := I) g₁ g_bg - deTurckVF (I := I) g₀ g_bg :
            Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) : ∀ x : M, TangentSpace I x) x v) w := by
    rw [ccTensorBilin_apply]
    show ccTensorModel (I := I) g₀ (fieldDiffGradSection (I := I) g₀ g₁ g₀ g_bg) x ![v, w] = _
    rw [ccTensorModel, ccTensorMultilinear_apply, fieldDiffGradSection_toModel_apply,
      fieldDiffGradBilin_apply]
  rw [hred]
  set u := (LeviCivita (I := I) g₀)
      ((deTurckVF (I := I) g₁ g_bg - deTurckVF (I := I) g₀ g_bg :
        Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) : ∀ x : M, TangentSpace I x) x v with hu
  refine le_trans
    (DifferentialGeometry.Analysis.Laplacian.abs_metric_inner_le_sqrt_metric_quadratic g₀ x u w) ?_
  have hwnn : 0 ≤ Real.sqrt (g₀.inner x w w) := Real.sqrt_nonneg _
  have hop := hΛ T₁ g₁ hg₁ hδbnd hB₁ hBjet x v
  calc Real.sqrt (g₀.inner x u u) * Real.sqrt (g₀.inner x w w)
      ≤ (Λ * Real.sqrt (g₀.inner x v v)) * Real.sqrt (g₀.inner x w w) :=
        mul_le_mul_of_nonneg_right hop hwnn
    _ = Λ * Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x w w) := by ring

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization in
set_option linter.unusedSectionVars false in
/-- **(POSIT — the field-difference gradient action value sup.)**  For the fibre-small
(`gFibreOpBound g₀ (ccTensorBilinSymm g₀ T₁) δ`, `δ < 1/2`) supercritically `H^{a+2}`-bounded
(`2a > finrank + 4`) realized perturbation family, the order-`0` intrinsic squared fibre norm of
the field-difference gradient section `fieldDiffGradSection g₀ g₁ g₀ g_bg` — fibre
`g₀(∇^{g₀}_v (W₁ − W₀), w)`, `Wᵢ = deTurckVF gᵢ g_bg` — is uniformly bounded by a single constant
`Λ²` over the manifold and the family.

The fibre value is the `g₀`-inner of the `g₀`-Levi-Civita covariant gradient of the field
difference `W₁ − W₀`; the field difference is the inverse-Gram-weighted trace of the pair
connection difference (`deTurckVF_sub_apply_eq_trace_connDiff`), whose connection-difference fibre
sup is the Neumann-absorbed supercritical-`C¹` bound, so the covariant gradient of the field
difference has a family-uniform order-`0` sup.

**Non-vacuity.**  A genuine fibre sup (a `Λ = 0` witness forces the field-difference gradient
section `≡ 0` at every point, false whenever `g₁ ≠ g₀` since `W₁ ≠ W₀`).  At `T₁ = 0` realized
(`g₁ = g₀`), `W₁ = W₀`, the field difference is the zero section, and `Λ = 0` works.  Its body is
`sorry`: the genuine supercritical-`C¹` value sup of the field-difference covariant gradient. -/
theorem exists_fieldDiffGradSection_rfns_fibre_sup_le
    (g₀ g_bg : SmoothRiemannianMetric I M) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1 / 2) (B : ℝ)
    (a : ℕ) (ha : 2 * a > Module.finrank ℝ E + 4) :
    ∃ Λ : ℝ, 0 ≤ Λ ∧
      ∀ (T₁ : Integral.L2.SmoothCcTensor g₀ 0 2) (g₁ : SmoothRiemannianMetric I M),
        (∀ (x : M) (v w : TangentSpace I x),
          g₁.inner x v w = g₀.inner x v w + ccTensorBilinSymm (I := I) g₀ T₁ x v w) →
        gFibreOpBound (I := I) g₀ (fun y => ccTensorBilinSymm (I := I) g₀ T₁ y) δ →
        ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (a + 2) T₁‖ ≤ B →
        ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (6 + a) T₁‖ ≤ B →
        ∀ x : M,
          Integral.Connection.riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x
            ((fieldDiffGradSection (I := I) g₀ g₁ g₀ g_bg).toSection x) ≤ Λ ^ 2 := by
  obtain ⟨Λ₀, hΛ₀0, hΛ₀⟩ :=
    exists_fieldDiffGradBilin_gcs_value_bound (I := I) g₀ g_bg δ hδ0 hδ1 B a ha
  refine ⟨Module.finrank ℝ E * Λ₀, by positivity, fun T₁ g₁ hg₁ hδbnd hB₁ hBjet x => ?_⟩
  exact rfns_le_of_ccTensorBilin_gcs_bound (I := I) g₀
    (fieldDiffGradSection (I := I) g₀ g₁ g₀ g_bg) x Λ₀ hΛ₀0
    (fun v w => hΛ₀ T₁ g₁ hg₁ hδbnd hB₁ hBjet x v w)

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
difference is the zero section).

Glued: the carrier difference rewrites to the field-difference gradient section
`fieldDiffGradSection g₀ g₁ g₀ g_bg`
(`loweredCovGradDeTurckVFMixed_fldSlot_sub_eq_fieldDiffGradSection`), whose family-uniform order-`0`
fibre value sup is the posited child `exists_fieldDiffGradSection_rfns_fibre_sup_le`. -/
theorem exists_riemannianFiberNormSq_loweredCovGradDeTurckVFMixed_fldSlot_diff_fibre_sup_le
    (g₀ g_bg : SmoothRiemannianMetric I M) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1 / 2) (B : ℝ)
    (a : ℕ) (ha : 2 * a > Module.finrank ℝ E + 4) :
    ∃ Λ : ℝ, 0 ≤ Λ ∧
      ∀ (T₁ : Integral.L2.SmoothCcTensor g₀ 0 2) (g₁ : SmoothRiemannianMetric I M),
        (∀ (x : M) (v w : TangentSpace I x),
          g₁.inner x v w = g₀.inner x v w + ccTensorBilinSymm (I := I) g₀ T₁ x v w) →
        gFibreOpBound (I := I) g₀ (fun y => ccTensorBilinSymm (I := I) g₀ T₁ y) δ →
        ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (a + 2) T₁‖ ≤ B →
        ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (6 + a) T₁‖ ≤ B →
        ∀ x : M,
          Integral.Connection.riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x
            ((loweredCovGradDeTurckVFMixed (I := I) g₀ g₀ g₀ g₁ g_bg
                - loweredCovGradDeTurckVFMixed (I := I) g₀ g₀ g₀ g₀ g_bg).toSection x) ≤ Λ ^ 2 := by
  obtain ⟨Λ, hΛ0, hΛ⟩ :=
    exists_fieldDiffGradSection_rfns_fibre_sup_le (I := I) g₀ g_bg δ hδ0 hδ1 B a ha
  refine ⟨Λ, hΛ0, fun T₁ g₁ hg₁ hδbnd hB₁ hBjet x => ?_⟩
  rw [loweredCovGradDeTurckVFMixed_fldSlot_sub_eq_fieldDiffGradSection (I := I) g₀ g₁ g_bg]
  exact hΛ T₁ g₁ hg₁ hδbnd hB₁ hBjet x

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization in
set_option linter.unusedSectionVars false in
/-- **(EngineB — RESTATED TO TWO-ARM, PROVEN — the family-uniform integrated Hamilton/Moser two-arm
jet bound of the field-difference gradient section.)**  For the fibre-small
(`gFibreOpBound g₀ (ccTensorBilinSymm g₀ T₁) δ`, `δ < 1/2`) supercritically `H`-bounded realized
perturbation family, the order-`l` covariant-jet `L²` norm of the field-difference gradient section
`fieldDiffGradSection g₀ g₁ g₀ g_bg` (fibre `g₀(∇^{g₀}_v (W₁ − W₀), w)`, `Wᵢ = deTurckVF gᵢ g_bg`)
obeys the **integrated two-arm Moser bound**
```
‖∇^l (fieldDiffGradSection g₀ g₁ g₀ g_bg)‖²
  ≤ C · ∑_{i ≤ l+2} ‖∇^i (realizeSymm T₁)‖²
    + C · (∑_{m ≤ l+3} ‖∇^m T₁‖²) · ‖(realizeSymm T₁).toHs (2(a+2))‖².
```

The over-strong clean single-arm shape `C · ∑ ‖∇^i T₁‖²` was refuted at high order (the project fact
`MetricDifferenceFdBTermTree`: the `W₁` coefficient jets of order `> 2` are not family-uniformly
pointwise bounded).  The two-arm Moser shape is exactly the Lie-line foundation
`exists_iteratedCovGrad_deTurckVF_le_jetSum` (`DeTurckVFCovariantJetBound.lean`) of which this engine is
a verbatim restatement (same conclusion), proven there over the field-difference covariant-Leibniz
product grid + the Gagliardo–Nirenberg two-arm engine + the proven connection-difference jet tower. -/
theorem exists_iteratedCovGrad_fieldDiffGradSection_fldSlot_hamiltonTame_le
    (g₀ g_bg : SmoothRiemannianMetric I M) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1 / 2) (B : ℝ)
    (a : ℕ) (ha : 2 * a > Module.finrank ℝ E + 4) (l : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (T₁ : Integral.L2.SmoothCcTensor g₀ 0 2) (g₁ : SmoothRiemannianMetric I M),
        (∀ (x : M) (v w : TangentSpace I x),
          g₁.inner x v w = g₀.inner x v w + ccTensorBilinSymm (I := I) g₀ T₁ x v w) →
        gFibreOpBound (I := I) g₀ (fun y => ccTensorBilinSymm (I := I) g₀ T₁ y) δ →
        ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (a + 2) T₁‖ ≤ B →
        ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (l + 3 + 3 + a) T₁‖ ≤ B →
        ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l
              (fieldDiffGradSection (I := I) g₀ g₁ g₀ g_bg)‖ ^ 2 ≤
          C * ∑ i ∈ Finset.range (l + 2 + 1),
              ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i
                (realizeSymmCcTensor (I := I) g₀ T₁)‖ ^ 2
            + C * (∑ m ∈ Finset.range (l + 3 + 1 + 1),
                ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 m T₁‖ ^ 2)
              * ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (2 * (a + 2))
                  (realizeSymmCcTensor (I := I) g₀ T₁)‖ ^ 2 :=
  DifferentialGeometry.PDE.RicciFlow.Pullback.exists_iteratedCovGrad_deTurckVF_le_jetSum
    (I := I) g₀ g_bg δ hδ0 hδ1 B a ha l

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
        ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (l + 3 + 3 + a) T₁‖ ≤ B →
          (∀ x : M,
            Integral.Connection.riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x
              ((loweredCovGradDeTurckVFMixed (I := I) g₀ g₀ g₀ g₁ g_bg
                  - loweredCovGradDeTurckVFMixed (I := I) g₀ g₀ g₀ g₀ g_bg).toSection x) ≤
                C ^ 2) ∧
          ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l
              (loweredCovGradDeTurckVFMixed (I := I) g₀ g₀ g₀ g₁ g_bg
                - loweredCovGradDeTurckVFMixed (I := I) g₀ g₀ g₀ g₀ g_bg)‖ ^ 2 ≤
            C * ∑ i ∈ Finset.range (l + 2 + 1),
                ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i
                  (realizeSymmCcTensor (I := I) g₀ T₁)‖ ^ 2
              + C * (∑ m ∈ Finset.range (l + 3 + 1 + 1),
                  ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 m T₁‖ ^ 2)
                * ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (2 * (a + 2))
                    (realizeSymmCcTensor (I := I) g₀ T₁)‖ ^ 2 := by
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
  · intro T₁ g₁ hg₁ hδbnd hB₁ hBjet
    -- The fldSlot value sup uses the higher Sobolev ball `‖T₁.toHs(6+a)‖ ≤ B`, the `l = 0`
    -- instance of the integrated jet ball `‖T₁.toHs(l+3+3+a)‖ ≤ B` (`toHs_norm_mono`).
    have hB6 : ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (6 + a) T₁‖ ≤ B :=
      le_trans (toHs_norm_mono (I := I) g₀ (by omega) T₁) hBjet
    refine ⟨?_, ?_⟩
    · intro x
      refine le_trans (hΛ T₁ g₁ hg₁ hδbnd hB₁ hB6 x) ?_
      have hnn : (0 : ℝ) ≤ Real.sqrt K₁ := Real.sqrt_nonneg _
      nlinarith [Real.sqrt_nonneg K₁, hΛ0, hC₃0, sq_nonneg (Real.sqrt K₁ + C₃),
        mul_nonneg hΛ0 (add_nonneg hnn hC₃0)]
    · rw [loweredCovGradDeTurckVFMixed_fldSlot_sub_eq_fieldDiffGradSection (I := I) g₀ g₁ g_bg]
      have hC₃u := hC₃ T₁ g₁ hg₁ hδbnd hB₁ hBjet
      have hCle : C₃ ≤ Real.sqrt K₁ + Λ + C₃ := by
        have : (0 : ℝ) ≤ Real.sqrt K₁ + Λ := by positivity
        linarith
      set Sdiff : ℝ := ∑ i ∈ Finset.range (l + 2 + 1),
        ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i (realizeSymmCcTensor (I := I) g₀ T₁)‖ ^ 2
        with hSdiff
      set Scross : ℝ := (∑ m ∈ Finset.range (l + 3 + 1 + 1),
          ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 m T₁‖ ^ 2)
          * ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (2 * (a + 2))
              (realizeSymmCcTensor (I := I) g₀ T₁)‖ ^ 2 with hScross
      have hSdiff_nn : 0 ≤ Sdiff := Finset.sum_nonneg fun i _ => sq_nonneg _
      have hScross_nn : 0 ≤ Scross := by
        rw [hScross]; exact mul_nonneg (Finset.sum_nonneg fun m _ => sq_nonneg _) (sq_nonneg _)
      have hC₃u' : ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l
              (fieldDiffGradSection (I := I) g₀ g₁ g₀ g_bg)‖ ^ 2 ≤ C₃ * Sdiff + C₃ * Scross := by
        rw [hSdiff, hScross, ← mul_assoc]; exact hC₃u
      calc ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l
              (fieldDiffGradSection (I := I) g₀ g₁ g₀ g_bg)‖ ^ 2
          ≤ C₃ * Sdiff + C₃ * Scross := hC₃u'
        _ ≤ (Real.sqrt K₁ + Λ + C₃) * Sdiff + (Real.sqrt K₁ + Λ + C₃) * Scross := by
            have h1 := mul_le_mul_of_nonneg_right hCle hSdiff_nn
            have h2 := mul_le_mul_of_nonneg_right hCle hScross_nn
            linarith [h1, h2]
        _ = (Real.sqrt K₁ + Λ + C₃) * Sdiff + (Real.sqrt K₁ + Λ + C₃) *
              (∑ m ∈ Finset.range (l + 3 + 1 + 1),
                ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 m T₁‖ ^ 2)
              * ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (2 * (a + 2))
                  (realizeSymmCcTensor (I := I) g₀ T₁)‖ ^ 2 := by rw [hScross, mul_assoc]

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
        ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (l + 3 + 3 + a) T₁‖ ≤ B →
          (∀ x : M,
            Integral.Connection.riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x
              ((loweredCovGradDeTurckVFMixed (I := I) g₀ g₀ g₁ g₁ g_bg
                  - loweredCovGradDeTurckVFMixed (I := I) g₀ g₀ g₀ g₀ g_bg).toSection x) ≤
                C ^ 2) ∧
          ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l
              (loweredCovGradDeTurckVFMixed (I := I) g₀ g₀ g₁ g₁ g_bg
                - loweredCovGradDeTurckVFMixed (I := I) g₀ g₀ g₀ g₀ g_bg)‖ ^ 2 ≤
            C * ∑ i ∈ Finset.range (l + 2 + 1),
                ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i
                  (realizeSymmCcTensor (I := I) g₀ T₁)‖ ^ 2
              + C * (∑ m ∈ Finset.range (l + 3 + 1 + 1),
                  ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 m T₁‖ ^ 2)
                * ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (2 * (a + 2))
                    (realizeSymmCcTensor (I := I) g₀ T₁)‖ ^ 2 := by
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
  · intro T₁ g₁ hg₁ hδbnd hB₁ hBjet
    obtain ⟨hvalA, hintA⟩ := hfamA T₁ g₁ hg₁ hδbnd hB₁ hBjet
    obtain ⟨hvalB, hintB⟩ := hfamB T₁ g₁ hg₁ hδbnd hB₁ hBjet
    set cA : Integral.L2.SmoothCcTensor g₀ 0 2 :=
      loweredCovGradDeTurckVFMixed (I := I) g₀ g₀ g₁ g₁ g_bg
        - loweredCovGradDeTurckVFMixed (I := I) g₀ g₀ g₀ g₁ g_bg with hcA
    set cB : Integral.L2.SmoothCcTensor g₀ 0 2 :=
      loweredCovGradDeTurckVFMixed (I := I) g₀ g₀ g₀ g₁ g_bg
        - loweredCovGradDeTurckVFMixed (I := I) g₀ g₀ g₀ g₀ g_bg with hcB
    have hPsum : loweredCovGradDeTurckVFMixed (I := I) g₀ g₀ g₁ g₁ g_bg
        - loweredCovGradDeTurckVFMixed (I := I) g₀ g₀ g₀ g₀ g_bg = cA + cB := by
      rw [hcA, hcB]; abel
    set Sdiff : ℝ := ∑ i ∈ Finset.range (l + 2 + 1),
      ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i (realizeSymmCcTensor (I := I) g₀ T₁)‖ ^ 2
      with hSdiff
    set Scross : ℝ := (∑ m ∈ Finset.range (l + 3 + 1 + 1),
        ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 m T₁‖ ^ 2)
        * ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (2 * (a + 2))
            (realizeSymmCcTensor (I := I) g₀ T₁)‖ ^ 2 with hScross
    have hSdiff_nn : 0 ≤ Sdiff := Finset.sum_nonneg fun i _ => sq_nonneg _
    have hScross_nn : 0 ≤ Scross := by
      rw [hScross]; exact mul_nonneg (Finset.sum_nonneg fun m _ => sq_nonneg _) (sq_nonneg _)
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
      have hgoaleq : (2 * (C_A + C_B) + 1) * Sdiff + (2 * (C_A + C_B) + 1) *
            (∑ m ∈ Finset.range (l + 3 + 1 + 1),
              ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 m T₁‖ ^ 2)
            * ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (2 * (a + 2))
                (realizeSymmCcTensor (I := I) g₀ T₁)‖ ^ 2
          = (2 * (C_A + C_B) + 1) * Sdiff + (2 * (C_A + C_B) + 1) * Scross := by
        rw [hScross, mul_assoc]
      rw [hgoaleq]
      refine le_trans (sq_le_sq' ?_ (norm_add_le _ _)) ?_
      · have := norm_nonneg
          (PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l cA
            + PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l cB)
        nlinarith [norm_nonneg (PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l cA),
          norm_nonneg (PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l cB)]
      · refine le_trans (add_sq_le_two_mul_sq_add_sq _ _) ?_
        have hAi : ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l cA‖ ^ 2 ≤
            C_A * Sdiff + C_A * Scross := by rw [hSdiff, hScross, ← mul_assoc]; exact hintA
        have hBi : ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 l cB‖ ^ 2 ≤
            C_B * Sdiff + C_B * Scross := by rw [hSdiff, hScross, ← mul_assoc]; exact hintB
        nlinarith [hAi, hBi, hSdiff_nn, hScross_nn, hCA_nn, hCB_nn]

end Pullback
end RicciFlow
end PDE
end DifferentialGeometry

end
