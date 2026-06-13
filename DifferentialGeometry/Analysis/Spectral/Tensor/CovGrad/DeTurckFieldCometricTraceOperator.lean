import DifferentialGeometry.Geometry.Connection.ConnectionDifferenceFieldJets
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CrossCorrectionParallelContraction

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

## Main definitions

* `connDiffLoweredTri gL gA gB x` — the continuous trilinear form
  `(a, b, c) ↦ gL.inner x (connDiff gA gB x b a) c`, the `gL`-metrically-lowered connection difference
  of the pair `(gA, gB)`, generic in the lowering metric.
* `connDiffLoweredField gL gA gB` — its packaging as a smooth covariant `(0, 3)`-tensor field, by the
  same chart-coordinate route as `loweredConnDiffField`.
* `connDiffSection g₀ g_bg := connDiffLoweredSection g₀ g₀ g_bg` — the `g₀`-lowered fixed-pair
  connection difference, as a `SmoothCcTensor g₀ 0 3`.

## Main results

* `connDiffSection_toModel_apply` — its fibre value
  `toModel(connDiffSection g₀ g_bg x) ![a, b, c] = g₀.inner x (connDiff g₀ g_bg x b a) c`.
* `connDiffSection_self_toModel` — the `g`-lowered connection difference of `g` with itself is the
  zero section (the non-vacuity litmus; `connDiff_self`).
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

end DeTurck
end PDE
end DifferentialGeometry

end
