import DifferentialGeometry.Geometry.Connection.ConnectionDifferenceFieldJets
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CrossCorrectionParallelContraction
import DifferentialGeometry.Geometry.Connection.TensorNabla.DeTurckVFIntrinsicValueBound

/-! # The bare connection-difference `(0,3)`-section and the DeTurck-field cometric-trace operator

For two smooth Riemannian metrics on a closed (compact, boundaryless) smooth manifold `M` modelled on
a real inner-product space `E`, the DeTurck vector-field difference `W₁ − W₀`
(`Wᵢ = deTurckVF gᵢ g_bg`) is — by the inverse-Gram-weighted trace formula
`deTurckVF_sub_apply_eq_trace_connDiff` — the sum of two arms, each a cometric-weighted trace of a
connection difference.  Arm 1 traces `connDiff g₁ g₀` (lowered into `loweredConnDiffSection g₁ g₀`);
arm 2 traces the *fixed* connection difference `connDiff g₀ g_bg`.  This file supplies the bare
covariant carrier of the arm-2 connection difference, the `g₀`-lowered

```
connDiffSection g₀ g_bg : SmoothCcTensor g₀ 0 3,
toModel(connDiffSection g₀ g_bg x) ![a, b, c] = g₀.inner x (connDiff g₀ g_bg x b a) c.
```

It is the arm-2 analog of `loweredConnDiffSection g₁ g₀` (`ConnectionDifferenceFieldJets.lean`), with
the *base* metric `g₀` doing the lowering of the *fixed-pair* connection difference `connDiff g₀ g_bg`
(rather than the second-slot metric lowering the perturbed-pair `connDiff g₁ g₀`).  The generic
lowering used here — a separately-named lowering metric on an arbitrary connection-difference pair —
is the `g₀`-fibre carrier that the two-arm DeTurck-field cometric-trace operator development consumes.

The file then proves the **intrinsic frame-free DeTurck-field cometric-double-trace identity** — the
foundational bottom of the Lie line, mirroring the curvature half's
`crossCorrParallelContraction_eq_crossCorrectionSection`.  The `g`-lowered DeTurck vector field
`W^♭ = g(deTurckVF g g', ·)` (the `(0,1)`-section `loweredDeTurckVFSection g g'`) is identified with the
operator-field action of the `∇₀`-parallel cometric double-trace field `cometricDoubleTraceField g 1`
on the bare lowered connection-difference section:

```
loweredDeTurckVFSection g g'
  = appCcRS g 0 (1 + 2) 1 (cometricDoubleTraceField g 1) (connDiffSection g g').
```

This is `W^k = g^{ij}(Γ(g)^k_{ij} − Γ̄^k_{ij})` read as the `g`-cometric (`g⁻¹`) double trace of the
connection difference, established with NO chart inverse-Gram (the chart-Gram-weighted trace
`deTurckVF_apply_eq` is read in a `g`-orthonormal frame where the inverse Gram is the identity, and the
cometric double trace becomes the matching orthonormal-frame diagonal).

## Main definitions

* `connDiffLoweredTri gL gA gB x` — the continuous trilinear form
  `(a, b, c) ↦ gL.inner x (connDiff gA gB x b a) c`, the `gL`-metrically-lowered connection difference
  of the pair `(gA, gB)`, generic in the lowering metric.
* `connDiffLoweredField gL gA gB` — its packaging as a smooth covariant `(0, 3)`-tensor field, by the
  same chart-coordinate route as `loweredConnDiffField`.
* `connDiffSection g₀ g_bg := connDiffLoweredSection g₀ g₀ g_bg` — the `g₀`-lowered fixed-pair
  connection difference, as a `SmoothCcTensor g₀ 0 3`.
* `loweredDeTurckVFField g g'` / `loweredDeTurckVFSection g g'` — the `g`-lowered DeTurck vector field
  as a smooth covariant `(0, 1)`-tensor field / `SmoothCcTensor g 0 1`, fibre value
  `c ↦ g.inner x (deTurckVF g g' x) c`.

## Main results

* `connDiffSection_toModel_apply` — its fibre value
  `toModel(connDiffSection g₀ g_bg x) ![a, b, c] = g₀.inner x (connDiff g₀ g_bg x b a) c`.
* `connDiffSection_self_toModel` — the `g`-lowered connection difference of `g` with itself is the
  zero section (the non-vacuity litmus; `connDiff_self`).
* `iteratedCovGrad_appCcRS_of_parallel`, `covGrad_slotExtendPow_eq_zero` — the public per-arm iterated
  parallel operator-field covariant Leibniz reductions.
* `deTurckVF_eq_sum_orthonormalBasis` — the public intrinsic frame-free DeTurck value
  `deTurckVF g g' x = ∑ i, connDiff g g' x (B i) (B i)` in any `g`-orthonormal frame.
* `cometricDualBasisDoubleTrace_eq_orthoFrameDiag` — the cometric dual-basis double trace equals the
  `g`-orthonormal-frame diagonal sum (generic rank).
* `deTurckVF_eq_appCcRS_cometricTrace_connDiffSection` — the **intrinsic frame-free cometric-double-trace
  identity** `loweredDeTurckVFSection g g' = appCcRS g 0 (1+2) 1 (cometricDoubleTraceField g 1)
  (connDiffSection g g')`.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open Bundle Manifold Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry
namespace PDE
namespace DeTurck

open DifferentialGeometry
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2 (SmoothCcTensor)
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [SigmaCompactSpace M] [T2Space M] [I.Boundaryless] [BoundarylessManifold I M]

/-! ### The bare connection-difference `(0,3)`-section, generic in the lowering metric -/

/-- **The `gL`-lowered connection-difference bilinear form** at `x`, as a continuous trilinear form
`T_x M →L T_x M →L T_x M →L ℝ`: `(a, b, c) ↦ gL.inner x (connDiff gA gB x b a) c`.  Generic in the
lowering metric `gL`: the metrically-lowered connection difference of the pair `(gA, gB)`, paired by
the separately-specified metric `gL`.  Linearity in all three slots is the bilinearity of
`connDiffField gA gB x` and the linearity of `gL.inner x`.  The companion of `loweredConnDiffTri`,
which fixes `gL = gB` (the second pair argument). -/
def connDiffLoweredTri (gL gA gB : SmoothRiemannianMetric I M) (x : M) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  (ContinuousLinearMap.compL ℝ (TangentSpace I x) (TangentSpace I x)
      (TangentSpace I x →L[ℝ] ℝ) (gL.inner x)).comp
    ((connDiffField (I := I) gA gB x).flip)

@[simp] lemma connDiffLoweredTri_apply (gL gA gB : SmoothRiemannianMetric I M) (x : M)
    (a b c : TangentSpace I x) :
    connDiffLoweredTri (I := I) gL gA gB x a b c =
      gL.inner x (connDiffField (I := I) gA gB x b a) c := by
  rfl

/-- **Smoothness of the `gL`-lowered connection-difference trilinear form on smooth fields.**  For
smooth tangent vector fields `X`, `Y`, `Z`, the scalar field
`x ↦ connDiffLoweredTri gL gA gB x (X x) (Y x) (Z x) = gL.inner x (connDiff gA gB x (Y x) (X x)) (Z x)`
is smooth.  The inner connection-difference field `x ↦ connDiff gA gB x (Y x) (X x)` is smooth by
`connDiff_contMDiff`, and the `gL`-inner pairing of two smooth tangent fields is smooth by
`contMDiff_g_inner_of_smooth_sections`. -/
theorem connDiffLoweredTri_pairing_contMDiff (gL gA gB : SmoothRiemannianMetric I M)
    {X Y Z : Π b : M, TangentSpace I b}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Y))
    (hZ : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Z)) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun b : M => connDiffLoweredTri (I := I) gL gA gB b (X b) (Y b) (Z b)) := by
  have hinner : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (T% (fun b : M => connDiff (I := I) gA gB b (Y b) (X b))) :=
    connDiff_contMDiff (I := I) gA gB hY hX
  let D : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    ContMDiffSection.mk (fun b : M => connDiff (I := I) gA gB b (Y b) (X b)) hinner
  let Zs : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    ContMDiffSection.mk Z hZ
  have hpair : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun b : M => gL.inner b (D b) (Zs b)) :=
    contMDiff_g_inner_of_smooth_sections (I := I) gL D Zs
  refine hpair.congr (fun b => ?_)
  change gL.inner b (connDiff (I := I) gA gB b (Y b) (X b)) (Z b) =
    connDiffLoweredTri (I := I) gL gA gB b (X b) (Y b) (Z b)
  rw [connDiffLoweredTri_apply, connDiffField_apply]

/-- The pointwise `(0,3)`-tensor model value of the `gL`-lowered connection difference of `(gA, gB)`:
the model multilinear map obtained from the trilinear form `connDiffLoweredTri gL gA gB x` by the
fibre bridge `triFormToModel`. -/
private def connDiffLoweredModelFun (gL gA gB : SmoothRiemannianMetric I M) (x : M) :
    Tensor0SSpace 3 I x :=
  Tensor0SSpace.ofModel (triFormToModel (TangentSpace I x) (connDiffLoweredTri (I := I) gL gA gB x))

omit [I.Boundaryless] in
private theorem connDiffLoweredModelFun_toModel_apply (gL gA gB : SmoothRiemannianMetric I M) (x : M)
    (v : Fin 3 → TangentSpace I x) :
    Tensor0SSpace.toModel (connDiffLoweredModelFun (I := I) gL gA gB x) v =
      connDiffLoweredTri (I := I) gL gA gB x (v 0) (v 1) (v 2) := by
  unfold connDiffLoweredModelFun
  rw [Tensor0SSpace.toModel_ofModel]
  exact triFormToModel_apply (TangentSpace I x) (connDiffLoweredTri (I := I) gL gA gB x) v

/-- **The `gL`-lowered connection difference of `(gA, gB)` as a smooth covariant `(0,3)`-tensor
field.**  Its chart-component smoothness is the trilinear-form pairing smoothness
`connDiffLoweredTri_pairing_contMDiff` on the chart-`α`-pushforward frame `chartFrameVec` (the same
`contMDiff_multilinearSection_iff_coord` route as `loweredConnDiffField`). -/
def connDiffLoweredField (gL gA gB : SmoothRiemannianMetric I M) :
    Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) ∞ 3 :=
  letI := tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 3
  letI := TangentBundle.contMDiffVectorBundle (I := I) (M := M) (n := ∞)
  ⟨fun x => connDiffLoweredModelFun (I := I) gL gA gB x, by
    let d := Module.finrank ℝ E
    let b : Module.Basis (Fin d) ℝ E := chartModelBasis E
    refine (contMDiff_multilinearSection_iff_coord (TangentSpace I) ∞ b _).mpr
      fun σ x₀ => ?_
    have hcomp : ContMDiffOn I 𝓘(ℝ, ℝ) ∞
        (fun x : M =>
          connDiffLoweredTri (I := I) gL gA gB x
            (chartFrameVec (I := I) x₀ (σ 0) x)
            (chartFrameVec (I := I) x₀ (σ 1) x)
            (chartFrameVec (I := I) x₀ (σ 2) x))
        (chartAt H x₀).source := by
      intro x hx
      have hframe_on : ∀ k : Fin (Module.finrank ℝ E),
          ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
            (fun bb : M => TotalSpace.mk' E bb (chartFrameVec (I := I) x₀ k bb))
            (chartAt H x₀).source := fun k => by
        have h := chartAlphaFrame_section_contMDiffOn (I := I) x₀ k
        exact h
      obtain ⟨S, hS_eq⟩ :=
        exists_contMDiffSection_eqOn_nhd
          (s := fun k : Fin (Module.finrank ℝ E) => fun bb : M => chartFrameVec (I := I) x₀ k bb)
          (u := (chartAt H x₀).source) (p := x)
          hframe_on ((chartAt H x₀).open_source) hx
      have hSk : ∀ k, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
          (T% (fun bb : M => (S k) bb : Π bb : M, TangentSpace I bb)) := fun k => (S k).contMDiff
      have hpair : ContMDiff I 𝓘(ℝ, ℝ) ∞
          (fun bb : M => connDiffLoweredTri (I := I) gL gA gB bb
            ((S (σ 0)) bb) ((S (σ 1)) bb) ((S (σ 2)) bb)) :=
        connDiffLoweredTri_pairing_contMDiff (I := I) gL gA gB (hSk (σ 0)) (hSk (σ 1)) (hSk (σ 2))
      have hpair_at : ContMDiffAt I 𝓘(ℝ, ℝ) ∞
          (fun bb : M => connDiffLoweredTri (I := I) gL gA gB bb
            ((S (σ 0)) bb) ((S (σ 1)) bb) ((S (σ 2)) bb)) x :=
        hpair x
      have hchart_at : ContMDiffAt I 𝓘(ℝ, ℝ) ∞
          (fun x : M => connDiffLoweredTri (I := I) gL gA gB x
            (chartFrameVec (I := I) x₀ (σ 0) x)
            (chartFrameVec (I := I) x₀ (σ 1) x)
            (chartFrameVec (I := I) x₀ (σ 2) x)) x := by
        refine hpair_at.congr_of_eventuallyEq ?_
        filter_upwards [hS_eq] with bb hb
        rw [hb (σ 0), hb (σ 1), hb (σ 2)]
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
    change Tensor0SSpace.toModel (connDiffLoweredModelFun (I := I) gL gA gB x)
        (fun j => (trivializationAt E (TangentSpace I) x₀).symmL ℝ x (b (σ j))) = _
    rw [connDiffLoweredModelFun_toModel_apply]
    rfl⟩

/-- The `gL`-lowered connection difference of `(gA, gB)` as a smooth mixed `(0,3)`-tensor section. -/
def connDiffLoweredMixedSection (gL gA gB : SmoothRiemannianMetric I M) :
    Cₛ^∞⟮I; TensorRSModel 0 3 ℝ E, (fun x : M => TensorRSSpace 0 3 I x)⟯ :=
  MixedSection.fromMultilinearSection (𝕜 := ℝ) (F := E) (IB := I)
    (E := (TangentSpace I : M → Type _)) ∞ (connDiffLoweredField (I := I) gL gA gB)

/-- **The `gL`-metrically-lowered connection difference of `(gA, gB)` as a `SmoothCcTensor gL 0 3`** —
the genuine covariant section-level lowered connection-difference object, generic in the lowering
metric.  Its fibre is `toModel(connDiffLoweredSection gL gA gB x) ![a, b, c] =
gL.inner x (connDiff gA gB x b a) c` (`connDiffLoweredSection_toModel_apply`); compact support is
automatic on the compact manifold `M`. -/
def connDiffLoweredSection (gL gA gB : SmoothRiemannianMetric I M) :
    Integral.L2.SmoothCcTensor gL 0 3 where
  toSection := connDiffLoweredMixedSection (I := I) gL gA gB
  hasCompactSupport := HasCompactSupport.of_compactSpace _

set_option linter.unusedSectionVars false in
/-- **The fibre value of the `gL`-lowered connection-difference section.**  Evaluating the underlying
`(0,3)` mixed tensor at the canonical unit `(0,0)`-tensor and a tangent triple recovers the
`gL`-pairing of the connection difference, `gL.inner x (connDiff gA gB x b a) c`, by traversing the
packaging chain `connDiffLoweredSection → MixedSection.fromMultilinearSection connDiffLoweredField`
(`MixedSection.eval₀_apply`) then `connDiffLoweredField → Tensor0SSpace.ofModel ∘ triFormToModel`
(`connDiffLoweredModelFun_toModel_apply`) and the trilinear-form evaluation
`connDiffLoweredTri_apply`. -/
theorem connDiffLoweredSection_toModel_apply (gL gA gB : SmoothRiemannianMetric I M) (x : M)
    (a b c : TangentSpace I x) :
    Tensor0SSpace.toModel
        ((connDiffLoweredSection (I := I) gL gA gB).toSection x
          (ContinuousMultilinearMap.constOfIsEmpty ℝ
            (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))) ![a, b, c] =
      gL.inner x (connDiff (I := I) gA gB x b a) c := by
  classical
  change Tensor0SSpace.toModel
      ((MixedSection.eval₀ (F := E) (E := (TangentSpace I : M → Type _)) x).smulRight
          (connDiffLoweredField (I := I) gL gA gB x)
        (ContinuousMultilinearMap.constOfIsEmpty ℝ
          (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))) ![a, b, c] = _
  rw [ContinuousLinearMap.smulRight_apply, MixedSection.eval₀_apply,
    ContinuousMultilinearMap.constOfIsEmpty_apply, one_smul]
  change Tensor0SSpace.toModel (connDiffLoweredModelFun (I := I) gL gA gB x) ![a, b, c] = _
  rw [connDiffLoweredModelFun_toModel_apply, connDiffLoweredTri_apply, connDiffField_apply]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons,
    Matrix.head_cons]

/-- **The bare `g₀`-lowered fixed-pair connection-difference `(0,3)`-section** — the arm-2 covariant
carrier of the DeTurck-field difference trace.  The `g₀`-metric lowering of the fixed connection
difference `connDiff g₀ g_bg`, as a `SmoothCcTensor g₀ 0 3` with fibre value
`toModel(connDiffSection g₀ g_bg x) ![a, b, c] = g₀.inner x (connDiff g₀ g_bg x b a) c`
(`connDiffSection_toModel_apply`).  Companion of `loweredConnDiffSection g₁ g₀` (the arm-1 carrier);
the difference is the lowering metric and connection-difference pair (`g₀` lowering `connDiff g₀ g_bg`
here, versus `g₀` lowering `connDiff g₁ g₀` there). -/
def connDiffSection (g₀ g_bg : SmoothRiemannianMetric I M) :
    Integral.L2.SmoothCcTensor g₀ 0 3 :=
  connDiffLoweredSection (I := I) g₀ g₀ g_bg

set_option linter.unusedSectionVars false in
/-- **The fibre value of the bare connection-difference section.**
`toModel(connDiffSection g₀ g_bg x) ![a, b, c] = g₀.inner x (connDiff g₀ g_bg x b a) c`. -/
theorem connDiffSection_toModel_apply (g₀ g_bg : SmoothRiemannianMetric I M) (x : M)
    (a b c : TangentSpace I x) :
    Tensor0SSpace.toModel
        ((connDiffSection (I := I) g₀ g_bg).toSection x
          (ContinuousMultilinearMap.constOfIsEmpty ℝ
            (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))) ![a, b, c] =
      g₀.inner x (connDiff (I := I) g₀ g_bg x b a) c :=
  connDiffLoweredSection_toModel_apply (I := I) g₀ g₀ g_bg x a b c

set_option linter.unusedSectionVars false in
/-- **Self-vanishing of the bare connection-difference section** (non-vacuity litmus).  The fibre
value of the `g`-lowered connection difference of `g` with itself vanishes on every tangent triple:
the two Levi-Civita covariant derivatives coincide, so `connDiff g g = 0`, hence every fibre
`g`-pairing is zero.  This rejects the degenerate constant-section reading (the section is genuinely
the lowered difference, not a fixed nonzero `(0,3)`-tensor), consistent with `connDiff_self`. -/
theorem connDiffSection_self_toModel (g : SmoothRiemannianMetric I M) (x : M)
    (a b c : TangentSpace I x) :
    Tensor0SSpace.toModel
        ((connDiffSection (I := I) g g).toSection x
          (ContinuousMultilinearMap.constOfIsEmpty ℝ
            (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))) ![a, b, c] = 0 := by
  rw [connDiffSection_toModel_apply]
  have h0 : connDiff (I := I) g g x b a = 0 := by
    rw [connDiff_self]; rfl
  rw [h0, map_zero, ContinuousLinearMap.zero_apply]

/-! ### The arm-2 fixed-factor `C⁰` fibre sup -/

set_option linter.unusedSectionVars false in
/-- **The `C⁰` fibre sup of the bare connection-difference section.**  Since `connDiffSection g₀ g_bg`
is a *fixed* smooth compactly-supported `(0,3)`-tensor on the compact manifold `M` — it depends only on
the base metric `g₀` and the flow background `g_bg`, not on the perturbed metric `g₁` — its intrinsic
squared `g₀`-fibre norm is bounded by a single nonnegative constant at every point, *unconditionally*
(no fibre-smallness or supercritical-ball gate).  This is the arm-2 analog of the (gated) arm-1 sup
`exists_loweredConnDiffSection_rfns_fibre_sup_le`; here the bound is unconditional precisely because the
arm-2 connection difference `connDiff g₀ g_bg` is the perturbation-independent fixed factor whose `C⁰`
jets the two-arm assembly absorbs as constants.  Proved directly from the compact-manifold smooth-tensor
fibre-norm bound `exists_bound_riemannianFiberNormSq_smoothCcTensor`. -/
theorem exists_connDiffSection_rfns_fibre_sup_le (g₀ g_bg : SmoothRiemannianMetric I M) :
    ∃ Λ : ℝ, 0 ≤ Λ ∧
      ∀ x : M,
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 3 x
            ((connDiffSection (I := I) g₀ g_bg).toSection x) ≤ Λ ^ 2 := by
  obtain ⟨K, hK0, hK⟩ := exists_bound_riemannianFiberNormSq_smoothCcTensor
    (I := I) (M := M) g₀ 0 3 (connDiffSection (I := I) g₀ g_bg)
  refine ⟨Real.sqrt K, Real.sqrt_nonneg _, fun x => ?_⟩
  refine (hK x).trans ?_
  rw [Real.sq_sqrt hK0]

/-! ### The per-arm iterated parallel operator-field covariant Leibniz (the reusable reduction)

The DeTurck-field cometric-trace operator development needs, per arm, the iterated covariant gradient
of a parallel operator-field action `appCcRS Φ W` to be carried through the operator as the `p`-fold
passenger extension of `Φ` on the order-`p` gradient of the contracted bare product `W`.  The
curvature half proves this only as a *private* lemma inside `CrossCorrectionParallelContraction`; the
Lie line bottoms at it as a foundational reduction, so it is exposed here as public reusable API. -/

set_option linter.unusedSectionVars false in
/-- **The `p`-fold passenger-slot extension of a `∇₀`-parallel operator field is `∇₀`-parallel.**
`slotExtend` preserves parallelism (`covGrad_slotExtend_eq_zero_of_covGrad_eq_zero`), so the `p`-fold
iterate `slotExtendPow p Φ` of a parallel `Φ` is parallel.  The public reusable companion of the
curvature half's private `covGrad_slotExtendPow_eq_zero`. -/
theorem covGrad_slotExtendPow_eq_zero (g₀ : SmoothRiemannianMetric I M) (r s : ℕ)
    (Φ : Integral.L2.SmoothCcTensor g₀ r s)
    (hΦ : covGrad (I := I) (M := M) g₀ r s Φ = 0) (p : ℕ) :
    covGrad (I := I) (M := M) g₀ (r + p) (s + p)
        (slotExtendPow (I := I) (M := M) g₀ r s p Φ) = 0 := by
  induction p with
  | zero => exact hΦ
  | succ p ih =>
    exact covGrad_slotExtend_eq_zero_of_covGrad_eq_zero
      (I := I) (M := M) g₀ (r + p) (s + p) (slotExtendPow (I := I) (M := M) g₀ r s p Φ) ih

set_option linter.unusedSectionVars false in
/-- **The iterated parallel operator-field covariant Leibniz (public reduction).**  For a
`∇₀`-parallel operator field `Φ` (`covGrad Φ = 0`), the order-`p` covariant gradient of the operator
action `appCcRS Φ W` is the action of the `p`-fold passenger extension on the order-`p` gradient of the
contracted section:
```
∇^p (appCcRS Φ W) = appCcRS (slotExtendPow p Φ) (∇^p W).
```
Each covariant gradient splits by the operator-field B-rule `covGrad_appCcRS_eq` into the
differentiated-coefficient action (which vanishes since `Φ` and its slot extensions are parallel,
`covGrad_slotExtendPow_eq_zero`) plus the slot-extended action on the gradient.  This is the per-arm
reduction the DeTurck-field two-arm cometric-trace operator identity carries `∇^l` through; the public
reusable companion of the curvature half's private `iteratedCovGrad_appCcRS_of_parallel`. -/
theorem iteratedCovGrad_appCcRS_of_parallel (g₀ : SmoothRiemannianMetric I M) (a b c : ℕ)
    (Φ : Integral.L2.SmoothCcTensor g₀ b c)
    (hΦ : covGrad (I := I) (M := M) g₀ b c Φ = 0)
    (W : Integral.L2.SmoothCcTensor g₀ a b) (p : ℕ) :
    PDE.RicciFlow.iteratedCovGrad (I := I) g₀ a c p (appCcRS (I := I) (M := M) g₀ a b c Φ W) =
      appCcRS (I := I) (M := M) g₀ a (b + p) (c + p)
        (slotExtendPow (I := I) (M := M) g₀ b c p Φ)
        (PDE.RicciFlow.iteratedCovGrad (I := I) g₀ a b p W) := by
  induction p with
  | zero =>
    rw [PDE.RicciFlow.iteratedCovGrad_zero, PDE.RicciFlow.iteratedCovGrad_zero]
    rfl
  | succ p ih =>
    rw [PDE.RicciFlow.iteratedCovGrad_succ, ih]
    rw [covGrad_appCcRS_eq (I := I) (M := M) g₀ a (b + p) (c + p)
      (slotExtendPow (I := I) (M := M) g₀ b c p Φ)
      (PDE.RicciFlow.iteratedCovGrad (I := I) g₀ a b p W)]
    rw [covGrad_slotExtendPow_eq_zero (I := I) (M := M) g₀ b c Φ hΦ p]
    rw [appCcRS_zero_left (I := I) (M := M) g₀ a (b + p) (c + p + 1)
      (PDE.RicciFlow.iteratedCovGrad (I := I) g₀ a b p W), zero_add]
    rw [PDE.RicciFlow.iteratedCovGrad_succ]
    rfl

/-! ### The intrinsic frame-free DeTurck-field cometric-double-trace identity

The DeTurck vector field `W = deTurckVF g g'`, lowered by `g` to the `(0,1)`-covector
`c ↦ g(W, c)`, is the genuine `g`-cometric double trace of the bare connection-difference
`(0,3)`-section `connDiffSection g g'` (whose fibre is `g(connDiff g g' x b a, c)`).  This is the
DeTurck-field analog of the curvature half's `crossCorrParallelContraction_eq_crossCorrectionSection`
(which identifies the parallel two-section cometric contraction with the concrete cross-correction
section): here the un-differentiated lowered DeTurck field is identified with the operator-field action
`appCcRS g 0 3 1 (cometricDoubleTraceField g 1) (connDiffSection g g')` of the **frame-free
`∇₀`-parallel** cometric double-trace operator field `cometricDoubleTraceField g 1`
(`cometricDoubleTraceField_covGrad_eq_zero`) on the bare lowered connection-difference section.

Everything is INTRINSIC: the chart-Gram-weighted trace `deTurckVF_apply_eq`
(`W = g^{jk}(Γ − Γ̄)`, T1-forbidden) is read in any `g`-orthonormal frame `{e_i}` where the inverse
Gram is the identity, collapsing to the plain frame sum `W x = ∑_i (connDiff g g' x)(e_i, e_i)`
(`deTurckVF_eq_sum_orthonormalBasis`); the cometric double trace, in the same frame, is the
orthonormal-frame diagonal `∑_i D(e_i, e_i, ·)` (`cometricDualBasisDoubleTrace_eq_orthoFrameDiag`),
routed through the smooth cometric Hom-section `inverseMetricSharpField` with NO chart-selected ambient
frame.  Once this base identity exists, the two-arm `fieldDiffGradSection` development closes its `∇^l`
reduction through `iteratedCovGrad_appCcRS_of_parallel` + `covGrad_slotExtendPow_eq_zero` above. -/

set_option linter.unusedSectionVars false in
/-- **Intrinsic orthonormal-frame trace identity for the DeTurck vector field** (public form).  For
any `g`-orthonormal frame `{B i}` at `x`, the DeTurck vector field collapses to the plain frame sum of
the connection difference: `deTurckVF g g' x = ∑ i, (connDiff g g' x)(B i, B i)`.  The chart-free reading
of the chart-Gram-weighted trace `deTurckVF_apply_eq`: the trace is the basis-independent `g`-cometric
trace of `connDiff g g'`, computed in the `g`-orthonormal frame where the inverse Gram is the identity
(by `orthonormal_basis_bilin_trace_chartα`).  The public companion of the value-bound file's private
`deTurckVF_eq_sum_orthonormalBasis`. -/
theorem deTurckVF_eq_sum_orthonormalBasis (g g' : SmoothRiemannianMetric I M) (x : M)
    (B : Fin (Module.finrank ℝ E) → TangentSpace I x)
    (hB : ∀ (i j : Fin (Module.finrank ℝ E)),
      g.inner x (B i) (B j) = if i = j then 1 else 0) :
    (deTurckVF (I := I) g g' : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x =
      ∑ i, connDiff (I := I) g g' x (B i) (B i) := by
  have hx : x ∈ (trivializationAt E (TangentSpace I) x).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt' x
  have htrace := Integral.Connection.orthonormal_basis_bilin_trace_chartα (I := I) (M := M)
    (A := TangentSpace I x) g x (b := x) hx (connDiff (I := I) g g' x) B hB
  rw [htrace, deTurckVF_apply_eq (I := I) g g' x]

set_option linter.unusedSectionVars false in
/-- **The cometric dual-basis double trace equals the `g`-orthonormal-frame diagonal sum.**  For a
`g`-orthonormal frame `{e i}` at `x` with the Parseval expansion `v = ∑ᵢ g(eᵢ, v) • eᵢ`, the frame-free
cometric double trace of a model `(0, s+2)`-tensor `T` — slot `0` raised by the cometric `♯` of the
model dual-basis covectors `b^k`, slot `1` contracted against the model basis `b_k`, summed over `k` —
equals the orthonormal-frame diagonal sum `∑ᵢ T(eᵢ, eᵢ, mm)`.  The cometric raise reads `g` only through
the smooth Hom-section (via `cometricReadingModel_dualBasis_inner`: `g(♯b^k, u) = repr(u)ₖ`); pairing the
raised covectors against the Parseval expansion of the frame collapses the chart-model double sum to the
intrinsic frame diagonal.  The public, generic-`s` companion of `CometricDoubleTraceField`'s private
`cometric_dualTrace_eq_orthoFrame_diag`. -/
theorem cometricDualBasisDoubleTrace_eq_orthoFrameDiag
    (g : SmoothRiemannianMetric I M) {s : ℕ} (x : M)
    (e : Fin (Module.finrank ℝ E) → TangentSpace I x)
    (hexpand : ∀ v : TangentSpace I x, v = ∑ i, g.inner x (e i) v • e i)
    (T : Tensor0SBundle.Tensor0SModel (s + 2) ℝ E) (mm : Fin s → E) :
    ∑ k : Fin (Module.finrank ℝ E),
        T (Fin.cons (cometricReadingModel (I := I) g x
              (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis k)))
            (Fin.cons ((Module.finBasis ℝ E) k) mm)) =
      ∑ i : Fin (Module.finrank ℝ E),
        T (Fin.cons ((e i : TangentSpace I x) : E)
            (Fin.cons ((e i : TangentSpace I x) : E) mm)) := by
  classical
  have hslot0_sum : ∀ (fs : Finset (Fin (Module.finrank ℝ E))) (f : Fin (Module.finrank ℝ E) → E)
      (rest : Fin (s + 1) → E),
      T (Fin.cons (∑ i ∈ fs, f i) rest) = ∑ i ∈ fs, T (Fin.cons (f i) rest) := by
    intro fs f rest
    have h : ∀ u : E, T (Fin.cons u rest) =
        ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (s + 2) => E) ℝ) T u) rest := by
      intro u; rw [continuousMultilinearCurryLeftEquiv_apply]
    rw [h, map_sum, ContinuousMultilinearMap.sum_apply]
    exact Finset.sum_congr rfl fun i _ => (h (f i)).symm
  have hslot0_smul : ∀ (c : ℝ) (u : E) (rest : Fin (s + 1) → E),
      T (Fin.cons (c • u) rest) = c * T (Fin.cons u rest) := by
    intro c u rest
    have h : ∀ z : E, T (Fin.cons z rest) =
        ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (s + 2) => E) ℝ) T z) rest := by
      intro z; rw [continuousMultilinearCurryLeftEquiv_apply]
    rw [h, map_smul, ContinuousMultilinearMap.smul_apply, smul_eq_mul, ← h]
  set P : Fin (Module.finrank ℝ E) → TangentSpace I x :=
    fun k => cometricReadingModel (I := I) g x
      (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
        ((Module.finBasis ℝ E).cDualBasis k)) with hP_def
  have hsharp : ∀ (k : Fin (Module.finrank ℝ E)) (u : TangentSpace I x),
      g.inner x (P k) u = (Module.finBasis ℝ E).repr (u : E) k :=
    fun k u => cometricReadingModel_dualBasis_inner (I := I) g x k u
  have hexp : ∀ k : Fin (Module.finrank ℝ E),
      (P k : TangentSpace I x) =
        ∑ i : Fin (Module.finrank ℝ E),
          ((Module.finBasis ℝ E).repr ((e i : TangentSpace I x) : E) k) • e i := by
    intro k
    conv_lhs => rw [hexpand (P k)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [g.symm x (e i) (P k), hsharp k (e i)]
  calc ∑ k : Fin (Module.finrank ℝ E),
        T (Fin.cons ((P k : TangentSpace I x) : E) (Fin.cons ((Module.finBasis ℝ E) k) mm))
      = ∑ k : Fin (Module.finrank ℝ E), ∑ i : Fin (Module.finrank ℝ E),
          ((Module.finBasis ℝ E).repr ((e i : TangentSpace I x) : E) k) *
            T (Fin.cons ((e i : TangentSpace I x) : E)
                (Fin.cons ((Module.finBasis ℝ E) k) mm)) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        have hPk : ((P k : TangentSpace I x) : E) =
            ∑ i : Fin (Module.finrank ℝ E),
              ((Module.finBasis ℝ E).repr ((e i : TangentSpace I x) : E) k) •
                ((e i : TangentSpace I x) : E) := by
          have h := hexp k
          calc ((P k : TangentSpace I x) : E)
              = (∑ i : Fin (Module.finrank ℝ E),
                  ((Module.finBasis ℝ E).repr ((e i : TangentSpace I x) : E) k) • e i :
                    TangentSpace I x) := by rw [← h]
            _ = ∑ i : Fin (Module.finrank ℝ E),
                  ((Module.finBasis ℝ E).repr ((e i : TangentSpace I x) : E) k) •
                    ((e i : TangentSpace I x) : E) := rfl
        calc T (Fin.cons ((P k : TangentSpace I x) : E)
                  (Fin.cons ((Module.finBasis ℝ E) k) mm))
            = T (Fin.cons (∑ i : Fin (Module.finrank ℝ E),
                  ((Module.finBasis ℝ E).repr ((e i : TangentSpace I x) : E) k) •
                    ((e i : TangentSpace I x) : E))
                (Fin.cons ((Module.finBasis ℝ E) k) mm)) := by rw [hPk]
          _ = ∑ i : Fin (Module.finrank ℝ E),
                T (Fin.cons (((Module.finBasis ℝ E).repr ((e i : TangentSpace I x) : E) k) •
                    ((e i : TangentSpace I x) : E))
                  (Fin.cons ((Module.finBasis ℝ E) k) mm)) :=
              hslot0_sum Finset.univ
                (fun i => ((Module.finBasis ℝ E).repr ((e i : TangentSpace I x) : E) k) •
                  ((e i : TangentSpace I x) : E))
                (Fin.cons ((Module.finBasis ℝ E) k) mm)
          _ = ∑ i : Fin (Module.finrank ℝ E),
                ((Module.finBasis ℝ E).repr ((e i : TangentSpace I x) : E) k) *
                  T (Fin.cons ((e i : TangentSpace I x) : E)
                      (Fin.cons ((Module.finBasis ℝ E) k) mm)) :=
              Finset.sum_congr rfl fun i _ => hslot0_smul _ _ _
    _ = ∑ i : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
          ((Module.finBasis ℝ E).repr ((e i : TangentSpace I x) : E) k) *
            T (Fin.cons ((e i : TangentSpace I x) : E)
                (Fin.cons ((Module.finBasis ℝ E) k) mm)) := Finset.sum_comm
    _ = ∑ i : Fin (Module.finrank ℝ E),
          T (Fin.cons ((e i : TangentSpace I x) : E)
              (Fin.cons ((e i : TangentSpace I x) : E) mm)) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        have hcurry2 : ∀ (lead : E) (z : E),
            T (Fin.cons lead (Fin.cons z mm)) =
              ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (s + 1) => E) ℝ)
                  ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (s + 2) => E) ℝ) T lead)
                  z) mm := by
          intro lead z
          rw [continuousMultilinearCurryLeftEquiv_apply, continuousMultilinearCurryLeftEquiv_apply]
        have hslot1_sum : ∀ (fs : Finset (Fin (Module.finrank ℝ E)))
            (f : Fin (Module.finrank ℝ E) → E) (lead : E),
            T (Fin.cons lead (Fin.cons (∑ j ∈ fs, f j) mm)) =
              ∑ j ∈ fs, T (Fin.cons lead (Fin.cons (f j) mm)) := by
          intro fs f lead
          rw [hcurry2, map_sum, ContinuousMultilinearMap.sum_apply]
          exact Finset.sum_congr rfl fun j _ => (hcurry2 lead (f j)).symm
        have hslot1_smul : ∀ (c : ℝ) (u : E) (lead : E),
            T (Fin.cons lead (Fin.cons (c • u) mm)) = c * T (Fin.cons lead (Fin.cons u mm)) := by
          intro c u lead
          rw [hcurry2, map_smul, ContinuousMultilinearMap.smul_apply, smul_eq_mul, ← hcurry2]
        calc ∑ k : Fin (Module.finrank ℝ E),
              ((Module.finBasis ℝ E).repr ((e i : TangentSpace I x) : E) k) *
                T (Fin.cons ((e i : TangentSpace I x) : E)
                    (Fin.cons ((Module.finBasis ℝ E) k) mm))
            = ∑ k : Fin (Module.finrank ℝ E),
                T (Fin.cons ((e i : TangentSpace I x) : E)
                    (Fin.cons (((Module.finBasis ℝ E).repr ((e i : TangentSpace I x) : E) k) •
                      ((Module.finBasis ℝ E) k)) mm)) := by
                refine Finset.sum_congr rfl fun k _ => ?_
                rw [hslot1_smul]
          _ = T (Fin.cons ((e i : TangentSpace I x) : E)
                  (Fin.cons (∑ k : Fin (Module.finrank ℝ E),
                    ((Module.finBasis ℝ E).repr ((e i : TangentSpace I x) : E) k) •
                      ((Module.finBasis ℝ E) k)) mm)) := (hslot1_sum Finset.univ _ _).symm
          _ = T (Fin.cons ((e i : TangentSpace I x) : E)
                  (Fin.cons ((e i : TangentSpace I x) : E) mm)) := by
                rw [(Module.finBasis ℝ E).sum_repr ((e i : TangentSpace I x) : E)]

/-- **The `g`-lowered DeTurck vector field as a smooth covariant `(0,1)`-tensor field.**  Its fibre
value is the `g`-covector `c ↦ g(deTurckVF g g' x, c)` (the metric lowering `W ↦ W^♭` of the DeTurck
vector field), packaged via the rank-`1` model bridge `model_covectorOfCLM`.  Chart-component smoothness
is the `g`-inner pairing of the smooth DeTurck section `deTurckVF g g'` against the smooth chart frame
(`contMDiff_g_inner_of_smooth_sections`), by the same `contMDiff_multilinearSection_iff_coord` route as
`connDiffLoweredField`. -/
def loweredDeTurckVFField (g g' : SmoothRiemannianMetric I M) :
    Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) ∞ 1 :=
  letI := tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 1
  letI := TangentBundle.contMDiffVectorBundle (I := I) (M := M) (n := ∞)
  ⟨fun x => Tensor0SSpace.ofModel
      (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
        (g.inner x (deTurckVF (I := I) g g' x))), by
    let d := Module.finrank ℝ E
    let b : Module.Basis (Fin d) ℝ E := chartModelBasis E
    refine (contMDiff_multilinearSection_iff_coord (TangentSpace I) ∞ b _).mpr
      fun σ x₀ => ?_
    have hcomp : ContMDiffOn I 𝓘(ℝ, ℝ) ∞
        (fun x : M =>
          g.inner x (deTurckVF (I := I) g g' x)
            (chartFrameVec (I := I) x₀ (σ 0) x))
        (chartAt H x₀).source := by
      intro x hx
      have hframe_on : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
          (fun bb : M => TotalSpace.mk' E bb (chartFrameVec (I := I) x₀ (σ 0) bb))
          (chartAt H x₀).source := chartAlphaFrame_section_contMDiffOn (I := I) x₀ (σ 0)
      obtain ⟨S, hS_eq⟩ :=
        exists_contMDiffSection_eqOn_nhd
          (s := fun _ : Fin 1 => fun bb : M => chartFrameVec (I := I) x₀ (σ 0) bb)
          (u := (chartAt H x₀).source) (p := x)
          (fun _ => hframe_on) ((chartAt H x₀).open_source) hx
      have hSk : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
          (T% (fun bb : M => (S 0) bb : Π bb : M, TangentSpace I bb)) := (S 0).contMDiff
      have hpair : ContMDiff I 𝓘(ℝ, ℝ) ∞
          (fun bb : M => g.inner bb (deTurckVF (I := I) g g' bb) ((S 0) bb)) :=
        contMDiff_g_inner_of_smooth_sections (I := I) g (deTurckVF (I := I) g g') (S 0)
      have hpair_at : ContMDiffAt I 𝓘(ℝ, ℝ) ∞
          (fun bb : M => g.inner bb (deTurckVF (I := I) g g' bb) ((S 0) bb)) x := hpair x
      have hchart_at : ContMDiffAt I 𝓘(ℝ, ℝ) ∞
          (fun x : M => g.inner x (deTurckVF (I := I) g g' x)
            (chartFrameVec (I := I) x₀ (σ 0) x)) x := by
        refine hpair_at.congr_of_eventuallyEq ?_
        filter_upwards [hS_eq] with bb hb
        rw [hb 0]
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
        (Tensor0SSpace.ofModel (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
          (g.inner x (deTurckVF (I := I) g g' x))) : Tensor0SSpace 1 I x)
        (fun j => (trivializationAt E (TangentSpace I) x₀).symmL ℝ x (b (σ j))) = _
    rw [Tensor0SSpace.toModel_ofModel, Tensor0SBundle.model_covectorOfCLM_apply]
    rfl⟩

/-- The `g`-lowered DeTurck vector field as a smooth mixed `(0,1)`-tensor section. -/
def loweredDeTurckVFMixedSection (g g' : SmoothRiemannianMetric I M) :
    Cₛ^∞⟮I; TensorRSModel 0 1 ℝ E, (fun x : M => TensorRSSpace 0 1 I x)⟯ :=
  MixedSection.fromMultilinearSection (𝕜 := ℝ) (F := E) (IB := I)
    (E := (TangentSpace I : M → Type _)) ∞ (loweredDeTurckVFField (I := I) g g')

/-- **The `g`-metrically-lowered DeTurck vector field as a `SmoothCcTensor g 0 1`** — the genuine
covariant `(0,1)`-section representative of the DeTurck field, with fibre value
`toModel(loweredDeTurckVFSection g g' x) ![c] = g.inner x (deTurckVF g g' x) c`
(`loweredDeTurckVFSection_toModel_apply`); compact support automatic on the closed manifold `M`.  This
is the LHS of the intrinsic cometric-double-trace identity
`deTurckVF_eq_appCcRS_cometricTrace_connDiffSection`. -/
def loweredDeTurckVFSection (g g' : SmoothRiemannianMetric I M) :
    Integral.L2.SmoothCcTensor g 0 1 where
  toSection := loweredDeTurckVFMixedSection (I := I) g g'
  hasCompactSupport := HasCompactSupport.of_compactSpace _

set_option linter.unusedSectionVars false in
/-- **The fibre value of the `g`-lowered DeTurck vector field section.**  Evaluating the underlying
`(0,1)` mixed tensor at the canonical unit `(0,0)`-tensor and a tangent vector `c` recovers the
`g`-lowering `g.inner x (deTurckVF g g' x) c`. -/
theorem loweredDeTurckVFSection_toModel_apply (g g' : SmoothRiemannianMetric I M) (x : M)
    (c : TangentSpace I x) :
    Tensor0SSpace.toModel
        ((loweredDeTurckVFSection (I := I) g g').toSection x
          (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ)))
          ![c] =
      g.inner x (deTurckVF (I := I) g g' x) c := by
  classical
  change Tensor0SSpace.toModel
      ((MixedSection.eval₀ (F := E) (E := (TangentSpace I : M → Type _)) x).smulRight
          (loweredDeTurckVFField (I := I) g g' x)
        (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ)))
          ![c] = _
  rw [ContinuousLinearMap.smulRight_apply, MixedSection.eval₀_apply,
    ContinuousMultilinearMap.constOfIsEmpty_apply, one_smul]
  change Tensor0SSpace.toModel
    (Tensor0SSpace.ofModel
      (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
        (g.inner x (deTurckVF (I := I) g g' x)))) ![c] = _
  rw [Tensor0SSpace.toModel_ofModel, Tensor0SBundle.model_covectorOfCLM_apply]
  rfl

set_option linter.unusedSectionVars false in
/-- **The intrinsic frame-free DeTurck-field cometric-double-trace identity.**  The `g`-lowered DeTurck
vector field `loweredDeTurckVFSection g g'` (fibre value `c ↦ g(deTurckVF g g' x, c)`) is the
operator-field action of the `∇₀`-parallel cometric double-trace operator field
`cometricDoubleTraceField g 1` on the bare `g`-lowered connection-difference `(0,3)`-section
`connDiffSection g g'`:
```
loweredDeTurckVFSection g g'
  = appCcRS g 0 (1 + 2) 1 (cometricDoubleTraceField g 1) (connDiffSection g g').
```
This is the DeTurck-field analog of the curvature half's
`crossCorrParallelContraction_eq_crossCorrectionSection`: the `W^k = g^{ij}(Γ(g)^k_{ij} − Γ̄^k_{ij})`
DeTurck field is the `g`-cometric (`g⁻¹`) double trace of the connection difference, established here
**INTRINSICALLY** (no chart inverse-Gram).  Proved by section extensionality through the unit
`(0,0)`-tensor read at a one-vector tuple `![c]`: a `g`-orthonormal frame `{e i}` at `x`
(`tangent_orthonormalBasis_witness`) makes the cometric double trace the orthonormal-frame diagonal
`∑ᵢ (connDiffSection)(eᵢ, eᵢ, c) = ∑ᵢ g(connDiff g g' x eᵢ eᵢ, c)`
(`cometricDualBasisDoubleTrace_eq_orthoFrameDiag` + `connDiffSection_toModel_apply`), and the DeTurck
field is the same frame's plain trace `∑ᵢ connDiff g g' x eᵢ eᵢ` (`deTurckVF_eq_sum_orthonormalBasis`),
so both sides equal `g(deTurckVF g g' x, c)`. -/
theorem deTurckVF_eq_appCcRS_cometricTrace_connDiffSection (g g' : SmoothRiemannianMetric I M) :
    loweredDeTurckVFSection (I := I) g g' =
      appCcRS (I := I) (M := M) g 0 (1 + 2) 1
        (cometricDoubleTraceField (I := I) g 1)
        (connDiffSection (I := I) g g') := by
  classical
  apply Integral.L2.SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply tensor0s_ext_unitZero (I := I) (M := M) (s := 1)
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro v
  have hvtuple : v = ![v 0] := by funext i; fin_cases i; rfl
  obtain ⟨n, e, _bse, hn, _hbse, horth, _hpars, hexpand, _hrepr⟩ :=
    Integral.Connection.tangent_orthonormalBasis_witness (I := I) (M := M) g x
  have hmn : n = Module.finrank ℝ E := hn
  subst hmn
  have hLHS : Tensor0SSpace.toModel
      ((loweredDeTurckVFSection (I := I) g g').toSection x
        (unitZeroSec (I := I) (M := M) x)) v = g.inner x (deTurckVF (I := I) g g' x) (v 0) := by
    rw [hvtuple]
    exact loweredDeTurckVFSection_toModel_apply (I := I) g g' x (v 0)
  have hRHS : Tensor0SSpace.toModel
      ((appCcRS (I := I) (M := M) g 0 (1 + 2) 1
          (cometricDoubleTraceField (I := I) g 1)
          (connDiffSection (I := I) g g')).toSection x
        (unitZeroSec (I := I) (M := M) x)) v = g.inner x (deTurckVF (I := I) g g' x) (v 0) := by
    rw [show (unitZeroSec (I := I) (M := M) x : Tensor0SSpace 0 I x)
        = ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ) from rfl]
    rw [appCcRS_toSection]
    rw [ContinuousLinearMap.comp_apply]
    rw [show (cometricDoubleTraceField (I := I) g 1).toSection x
        = (show Tensor0SBundle.TensorRSSpace (1 + 2) 1 I x from
            cometricDoubleTraceFib (I := I) g 1 x) from rfl]
    set D : Tensor0SBundle.Tensor0SSpace (1 + 2) I x :=
      (connDiffSection (I := I) g g').toSection x
        (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))
      with hD_def
    rw [show ((show Tensor0SBundle.Tensor0SSpace (1 + 2) I x →L[ℝ]
            Tensor0SBundle.Tensor0SSpace 1 I x from cometricDoubleTraceFib (I := I) g 1 x)
        ((connDiffSection (I := I) g g').toSection x
          (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))))
        = cometricDoubleTraceFib (I := I) g 1 x D from rfl]
    rw [show Tensor0SSpace.toModel (cometricDoubleTraceFib (I := I) g 1 x D) v
        = modelDoubleTrace (E := E) 1 (cometricLmodel (I := I) g x)
            (Tensor0SSpace.toModel D) v from by
      rw [cometricDoubleTraceFib_toModel]]
    rw [modelDoubleTrace_apply]
    rw [show cometricLmodel (I := I) g x = cometricReadingModel (I := I) g x from rfl]
    rw [cometricDualBasisDoubleTrace_eq_orthoFrameDiag (I := I) g (s := 1) x e hexpand
      (Tensor0SSpace.toModel D) v]
    have hsummand : ∀ i : Fin (Module.finrank ℝ E),
        (Tensor0SSpace.toModel D)
          (Fin.cons ((e i : TangentSpace I x) : E)
            (Fin.cons ((e i : TangentSpace I x) : E) v)) =
          g.inner x (connDiff (I := I) g g' x (e i) (e i)) (v 0) := by
      intro i
      have hcons : (Fin.cons ((e i : TangentSpace I x) : E)
            (Fin.cons ((e i : TangentSpace I x) : E) v) : Fin 3 → TangentSpace I x)
          = ![e i, e i, v 0] := by
        funext j; fin_cases j <;> rfl
      rw [hcons]
      exact connDiffSection_toModel_apply (I := I) g g' x (e i) (e i) (v 0)
    rw [Finset.sum_congr rfl (fun i _ => hsummand i)]
    have hW := deTurckVF_eq_sum_orthonormalBasis (I := I) g g' x e horth
    rw [hW]
    have hflip : g.inner x (∑ i, connDiff (I := I) g g' x (e i) (e i)) (v 0)
        = ∑ i, g.inner x (connDiff (I := I) g g' x (e i) (e i)) (v 0) := by
      have h := map_sum ((g.inner x).flip (v 0))
        (fun i => connDiff (I := I) g g' x (e i) (e i)) Finset.univ
      simp only [ContinuousLinearMap.flip_apply] at h
      exact h
    rw [hflip]
  rw [hLHS, hRHS]

end DeTurck
end PDE
end DifferentialGeometry

end
