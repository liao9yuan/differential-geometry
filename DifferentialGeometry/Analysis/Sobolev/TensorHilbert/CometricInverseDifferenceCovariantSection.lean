import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.CometricInverseDifferenceAppliedJet
import DifferentialGeometry.Geometry.Connection.ConnectionDifferenceFieldJets
import DifferentialGeometry.Geometry.Operator.NormGradSq
import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.CcTensorFibreCauchySchwarz

/-! # The cometric inverse-difference as a covariant `(0,2)`-section and its Koszul jet tower

For two smooth Riemannian metrics `g₁`, `g₀` on a closed (compact, boundaryless) smooth manifold
`M` modelled on a real inner-product space `E`, the cometric inverse-difference fibre-endomorphism
field `gInvDiffFibreEndo g₀ g₁` (`CometricInverseDifferenceMultiplier.lean`) is built from the
`g₀`-lowered raised representative `gInvDiffRaisedEndo g₀ g₁ x : TₓM →L TₓM`, `v ↦ g₁^♯(g₀^♭ v) − v`,
the `(1,1)`-endomorphism implementing the cometric difference `g₁⁻¹ − g₀⁻¹` through its `g₀`-lowered
representative.  Pairing that `(1,1)`-endomorphism's value with the background metric `g₀` produces a
genuine **covariant `(0,2)`-tensor** — the metrically-lowered cometric inverse difference

```
cometricInverseDiffSection g₁ g₀ : SmoothCcTensor g₀ 0 2,
toModel(cometricInverseDiffSection g₁ g₀ x) ![a, b] = g₀.inner x (gInvDiffRaisedEndo g₀ g₁ x a) b.
```

This is the inverse-Gram analog of `loweredConnDiffSection` (`ConnectionDifferenceFieldJets.lean`),
packaged at valence `(0, 2)` instead of `(0, 3)`, and built by the identical bilinear-form → field →
mixed-section chain (the arity-`2` model bridge `biForm₂ToModel`).

## What the section is and why it is the right object

The `g₀`-lowering uses the *background* metric `g₀`, whose Levi-Civita covariant derivative is
parallel (`∇₀ g₀ = 0`), so the metric-lowering is a **parallel fibre operation** that commutes with
`∇₀` and neither raises the differentiation order nor enlarges the `g₀`-fibre norm.  The `(0, 2)`
section is therefore the natural covariant carrier of the cometric difference — exactly the shape
under which its iterated covariant gradient `∇^p` can be controlled (the inverse-Gram analog of
`loweredConnDiffSection`'s role for the connection difference).

## The order-`0` link to the multiplier and the Neumann fibre bound

The order-`0` `g₀`-fibre norm of this section reads the raised representative through the slot-norm
calculus already developed for the multiplier.  Concretely the order-`0` Neumann fibre bound on the
raised representative `sqrt_inner_gInvDiffRaisedEndo_le` and the slot Neumann bound
`riemannianFiberNormSq_gInvDiffSlotEndo_le` (`CometricInverseDifferenceMultiplier.lean`) supply the
base case `p = 0` of the differentiated-Neumann Koszul jet tower: the cometric inverse-difference
section is fibre-small (`≤ Cnorm · δ` in the `g₀`-fibre norm) uniformly over the perturbation family.

## Non-vacuity

At `g₁ = g₀` the raised representative vanishes (`gInvDiffRaisedEndo_self`), so the lowered section is
the zero section (`cometricInverseDiffSection_self_toModel`); the cometric difference genuinely
measures `g₁⁻¹ − g₀⁻¹` (it is not a bound-only stand-in).
-/

noncomputable section

set_option linter.style.setOption false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open Bundle Manifold Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry.Analysis.Sobolev.TensorHilbert

open DifferentialGeometry
open DifferentialGeometry.Analysis.Laplacian
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck
open DifferentialGeometry.PDE.DeTurck
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.L2 (SmoothCcTensor)

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [BoundarylessManifold I M]
      [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

/-! ## Stage 1 — the `g₀`-lowered cometric inverse-difference bilinear form -/

/-- **The `g₀`-lowered cometric inverse-difference bilinear form** at `x`, as a continuous bilinear
form `T_x M →L[ℝ] T_x M →L[ℝ] ℝ`: `(a, b) ↦ g₀.inner x (gInvDiffRaisedEndo g₀ g₁ x a) b`.  This is the
metrically-lowered cometric inverse difference as an operator-packaged covariant `(0, 2)`-form (the
`a`-slot is the differentiated/input vector, the `b`-slot the lowered output index).  Linearity in
both slots is the linearity of the raised endomorphism `gInvDiffRaisedEndo g₀ g₁ x` and of `g₀.inner
x`.  Concretely, postcomposing `gInvDiffRaisedEndo g₀ g₁ x : T_x →L T_x` with the lowering `g₀.inner x
: T_x →L (T_x →L ℝ)` (via `ContinuousLinearMap.compL`) lowers the output index to `b`. -/
def cometricInvDiffBi (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  (g₀.inner x).comp (gInvDiffRaisedEndo (I := I) g₀ g₁ x)

@[simp] lemma cometricInvDiffBi_apply (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (a b : TangentSpace I x) :
    cometricInvDiffBi (I := I) g₀ g₁ x a b =
      g₀.inner x (gInvDiffRaisedEndo (I := I) g₀ g₁ x a) b := by
  rfl

/-- **The lowered cometric inverse-difference form of a metric with itself vanishes.**  When the two
metrics coincide, the raised representative is the zero endomorphism (`gInvDiffRaisedEndo_self`), so
the lowered bilinear form is the zero form. -/
lemma cometricInvDiffBi_self (g₀ : SmoothRiemannianMetric I M) (x : M) :
    cometricInvDiffBi (I := I) g₀ g₀ x = 0 := by
  ext a b
  rw [cometricInvDiffBi_apply, gInvDiffRaisedEndo_self, map_zero,
    ContinuousLinearMap.zero_apply]
  rfl

/-- **Smoothness of the raised representative applied to a smooth tangent field.**  For a smooth
tangent vector field `Y`, the field `x ↦ gInvDiffRaisedEndo g₀ g₁ x (Y x)` is a smooth section of the
tangent bundle: the smooth `(1,1)`-endomorphism field `gInvDiffRaisedEndo_contMDiff` applied to the
smooth field `Y` through the bundle evaluation `ContMDiff.clm_bundle_apply`. -/
lemma gInvDiffRaisedEndo_apply_field_contMDiff (g₀ g₁ : SmoothRiemannianMetric I M)
    (Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) x
        (gInvDiffRaisedEndo (I := I) g₀ g₁ x (Y x))) :=
  ContMDiff.clm_bundle_apply (b := id)
    (gInvDiffRaisedEndo_contMDiff (I := I) g₀ g₁) Y.contMDiff

/-- **Smoothness of the `g₀`-lowered cometric inverse-difference bilinear form on smooth fields.**
For smooth tangent vector fields `X`, `Z`, the scalar field
`x ↦ cometricInvDiffBi g₀ g₁ x (X x) (Z x) = g₀.inner x (gInvDiffRaisedEndo g₀ g₁ x (X x)) (Z x)` is
smooth: the inner raised field `x ↦ gInvDiffRaisedEndo g₀ g₁ x (X x)` is smooth
(`gInvDiffRaisedEndo_apply_field_contMDiff`), and the `g₀`-inner pairing of two smooth tangent fields
is smooth (`contMDiff_g_inner_of_smooth_sections`). -/
theorem cometricInvDiffBi_pairing_contMDiff (g₀ g₁ : SmoothRiemannianMetric I M)
    {X Z : Π b : M, TangentSpace I b}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X))
    (hZ : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Z)) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun b : M => cometricInvDiffBi (I := I) g₀ g₁ b (X b) (Z b)) := by
  let Xs : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ := ContMDiffSection.mk X hX
  have hinner : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (T% (fun b : M => gInvDiffRaisedEndo (I := I) g₀ g₁ b (Xs b))) :=
    gInvDiffRaisedEndo_apply_field_contMDiff (I := I) g₀ g₁ Xs
  let D : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    ContMDiffSection.mk (fun b : M => gInvDiffRaisedEndo (I := I) g₀ g₁ b (Xs b)) hinner
  let Zs : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ := ContMDiffSection.mk Z hZ
  have hpair : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun b : M => g₀.inner b (D b) (Zs b)) :=
    contMDiff_g_inner_of_smooth_sections (I := I) g₀ D Zs
  refine hpair.congr (fun b => ?_)
  change g₀.inner b (gInvDiffRaisedEndo (I := I) g₀ g₁ b (X b)) (Z b) =
    cometricInvDiffBi (I := I) g₀ g₁ b (X b) (Z b)
  rw [cometricInvDiffBi_apply]

/-- The pointwise `(0,2)`-tensor model value of the `g₀`-lowered cometric inverse difference: the
model multilinear map obtained from the bilinear form `cometricInvDiffBi g₀ g₁ x` by the arity-`2`
fibre bridge `biForm₂ToModel`. -/
private def cometricInvDiffModelFun (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) :
    Tensor0SSpace 2 I x :=
  Tensor0SSpace.ofModel (I := I)
    (biForm₂ToModel (TangentSpace I x) (cometricInvDiffBi (I := I) g₀ g₁ x))

set_option linter.unusedSectionVars false in
private theorem cometricInvDiffModelFun_toModel_apply (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (v : Fin 2 → TangentSpace I x) :
    Tensor0SSpace.toModel (cometricInvDiffModelFun (I := I) g₀ g₁ x) v =
      cometricInvDiffBi (I := I) g₀ g₁ x (v 0) (v 1) := by
  unfold cometricInvDiffModelFun
  rw [Tensor0SSpace.toModel_ofModel]
  exact biForm₂ToModel_apply (TangentSpace I x) (cometricInvDiffBi (I := I) g₀ g₁ x) v

/-- **The `g₀`-lowered cometric inverse difference as a smooth covariant `(0,2)`-tensor field.**  Its
chart-component smoothness is the bilinear-form pairing smoothness `cometricInvDiffBi_pairing_contMDiff`
on the chart-`x₀`-pushforward frame `chartFrameVec` (the same `contMDiff_multilinearSection_iff_coord`
route as `metricDiff02Field` / `loweredConnDiffField`). -/
def cometricInvDiffField (g₀ g₁ : SmoothRiemannianMetric I M) :
    Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) ∞ 2 :=
  letI := tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 2
  letI := TangentBundle.contMDiffVectorBundle (I := I) (M := M) (n := ∞)
  ⟨fun x => cometricInvDiffModelFun (I := I) g₀ g₁ x, by
    let d := Module.finrank ℝ E
    let b : Module.Basis (Fin d) ℝ E := chartModelBasis E
    refine (contMDiff_multilinearSection_iff_coord (TangentSpace I) ∞ b _).mpr
      fun σ x₀ => ?_
    have hcomp : ContMDiffOn I 𝓘(ℝ, ℝ) ∞
        (fun x : M =>
          cometricInvDiffBi (I := I) g₀ g₁ x
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
          (fun bb : M => cometricInvDiffBi (I := I) g₀ g₁ bb
            ((S (σ 0)) bb) ((S (σ 1)) bb)) :=
        cometricInvDiffBi_pairing_contMDiff (I := I) g₀ g₁ (hSk (σ 0)) (hSk (σ 1))
      have hchart_at : ContMDiffAt I 𝓘(ℝ, ℝ) ∞
          (fun x : M => cometricInvDiffBi (I := I) g₀ g₁ x
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
    change Tensor0SSpace.toModel (cometricInvDiffModelFun (I := I) g₀ g₁ x)
        (fun j => (trivializationAt E (TangentSpace I) x₀).symmL ℝ x (b (σ j))) = _
    rw [cometricInvDiffModelFun_toModel_apply]
    rfl⟩

/-- The `g₀`-lowered cometric inverse difference as a smooth mixed `(0,2)`-tensor section. -/
def cometricInvDiffMixedSection (g₀ g₁ : SmoothRiemannianMetric I M) :
    Cₛ^∞⟮I; TensorRSModel 0 2 ℝ E, (fun x : M => TensorRSSpace 0 2 I x)⟯ :=
  MixedSection.fromMultilinearSection (𝕜 := ℝ) (F := E) (IB := I)
    (E := (TangentSpace I : M → Type _)) ∞ (cometricInvDiffField (I := I) g₀ g₁)

/-- **The `g₀`-metrically-lowered cometric inverse difference as a `SmoothCcTensor g₀ 0 2`** — the
genuine covariant section-level lowered cometric-inverse-difference object.  Its fibre is
`toModel(cometricInverseDiffSection g₁ g₀ x) ![a, b] = g₀.inner x (gInvDiffRaisedEndo g₀ g₁ x a) b`
(`cometricInverseDiffSection_toModel_apply`); compact support is automatic on the compact manifold
`M`. -/
def cometricInverseDiffSection (g₁ g₀ : SmoothRiemannianMetric I M) :
    Integral.L2.SmoothCcTensor g₀ 0 2 where
  toSection := cometricInvDiffMixedSection (I := I) g₀ g₁
  hasCompactSupport := HasCompactSupport.of_compactSpace _

set_option linter.unusedSectionVars false in
/-- **The fibre value of the cometric inverse-difference section.**  Evaluating the underlying
`(0,2)` mixed tensor at the canonical unit `(0,0)`-tensor and a tangent pair recovers the `g₀`-pairing
of the raised cometric-difference representative, `g₀.inner x (gInvDiffRaisedEndo g₀ g₁ x a) b`, by
traversing the packaging chain `cometricInverseDiffSection → MixedSection.fromMultilinearSection
cometricInvDiffField` (`MixedSection.eval₀_apply`) then `cometricInvDiffField → Tensor0SSpace.ofModel ∘
biForm₂ToModel` (`cometricInvDiffModelFun_toModel_apply`) and the bilinear-form evaluation
`cometricInvDiffBi_apply`. -/
theorem cometricInverseDiffSection_toModel_apply (g₁ g₀ : SmoothRiemannianMetric I M) (x : M)
    (a b : TangentSpace I x) :
    Tensor0SSpace.toModel
        ((cometricInverseDiffSection (I := I) g₁ g₀).toSection x
          (ContinuousMultilinearMap.constOfIsEmpty ℝ
            (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))) ![a, b] =
      g₀.inner x (gInvDiffRaisedEndo (I := I) g₀ g₁ x a) b := by
  classical
  change Tensor0SSpace.toModel
      ((MixedSection.eval₀ (F := E) (E := (TangentSpace I : M → Type _)) x).smulRight
          (cometricInvDiffField (I := I) g₀ g₁ x)
        (ContinuousMultilinearMap.constOfIsEmpty ℝ
          (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))) ![a, b] = _
  rw [ContinuousLinearMap.smulRight_apply, MixedSection.eval₀_apply,
    ContinuousMultilinearMap.constOfIsEmpty_apply, one_smul]
  change Tensor0SSpace.toModel (cometricInvDiffModelFun (I := I) g₀ g₁ x) ![a, b] = _
  rw [cometricInvDiffModelFun_toModel_apply, cometricInvDiffBi_apply]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]

set_option linter.unusedSectionVars false in
/-- **Self-vanishing of the cometric inverse-difference section** (non-vacuity litmus).  The fibre
value of the `g₀`-lowered cometric inverse difference of `g₀` with itself vanishes on every tangent
pair: the raised representative `gInvDiffRaisedEndo g₀ g₀` is the zero endomorphism
(`gInvDiffRaisedEndo_self`), so every fibre `g₀`-pairing is zero.  This rejects the degenerate reading
of the lowered object (it is genuinely the cometric difference `g₁⁻¹ − g₀⁻¹`, not a constant nonzero
`(0,2)`-section). -/
theorem cometricInverseDiffSection_self_toModel (g₀ : SmoothRiemannianMetric I M) (x : M)
    (a b : TangentSpace I x) :
    Tensor0SSpace.toModel
        ((cometricInverseDiffSection (I := I) g₀ g₀).toSection x
          (ContinuousMultilinearMap.constOfIsEmpty ℝ
            (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))) ![a, b] = 0 := by
  rw [cometricInverseDiffSection_toModel_apply, gInvDiffRaisedEndo_self, map_zero,
    ContinuousLinearMap.zero_apply]

/-! ## Stage 2 — the cross-correction `(0,2)`-section and the resolvent Koszul identity

The resolvent identity `inner_g1_gInvDiffRaisedEndo` reads the `g₁`-pairing of the raised
representative `D = gInvDiffRaisedEndo g₀ g₁` as the *negative* metric difference,
`g₁(D a, b) = g₀(a, b) − g₁(a, b)`.  Under the realize-tie `g₁ = g₀ + h` (`h = ccTensorBilinSymm g₀
T₁`), this gives the `g₀`-pairing carried by `cometricInverseDiffSection`,

```
g₀(D a, b) = g₁(D a, b) − h(D a, b) = −h(a, b) − h(D a, b),
```

i.e. the section-level resolvent split

```
cometricInverseDiffSection g₁ g₀ = −realizeSymmCcTensor g₀ T₁ − crossCometricSection g₁ g₀ T₁,
```

a *clean linear part* `−realizeSymmCcTensor g₀ T₁` (the perturbation itself, jet-bounded by `T₁`
unconditionally) minus a *fibre-small cross correction* `crossCometricSection g₁ g₀ T₁` carrying the
nonlinear `h(D, ·)` content.  This is the inverse-Gram analog of the connection-difference Koszul
identity `koszulCombSection = 2·loweredConnDiffSection + 2·crossCorrectionSection`. -/

/-- **The cometric cross-correction bilinear form** `(a, b) ↦ ccTensorBilinSymm g₀ T₁ x
(gInvDiffRaisedEndo g₀ g₁ x a) b`, the `(0,2)`-fibre value of the resolvent correction `h(D, ·)`. -/
def crossCometricBi (g₀ g₁ : SmoothRiemannianMetric I M)
    (T₁ : Integral.L2.SmoothCcTensor g₀ 0 2) (x : M) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  (ccTensorBilinSymm (I := I) g₀ T₁ x).comp (gInvDiffRaisedEndo (I := I) g₀ g₁ x)

@[simp] lemma crossCometricBi_apply (g₀ g₁ : SmoothRiemannianMetric I M)
    (T₁ : Integral.L2.SmoothCcTensor g₀ 0 2) (x : M) (a b : TangentSpace I x) :
    crossCometricBi (I := I) g₀ g₁ T₁ x a b =
      ccTensorBilinSymm (I := I) g₀ T₁ x (gInvDiffRaisedEndo (I := I) g₀ g₁ x a) b := by
  rfl

/-- **Smoothness of the cometric cross-correction bilinear form on smooth fields.**  For smooth
tangent vector fields `X`, `Z`, the scalar `x ↦ crossCometricBi g₀ g₁ T₁ x (X x) (Z x)` is smooth:
the inner raised field `x ↦ gInvDiffRaisedEndo g₀ g₁ x (X x)` is smooth
(`gInvDiffRaisedEndo_apply_field_contMDiff`), and the `ccTensorBilinSymm`-pairing of two smooth tangent
fields is smooth (`contMDiff_ccTensorBilinSymm_pairing`). -/
theorem crossCometricBi_pairing_contMDiff (g₀ g₁ : SmoothRiemannianMetric I M)
    (T₁ : Integral.L2.SmoothCcTensor g₀ 0 2)
    {X Z : Π b : M, TangentSpace I b}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X))
    (hZ : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Z)) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun b : M => crossCometricBi (I := I) g₀ g₁ T₁ b (X b) (Z b)) := by
  let Xs : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ := ContMDiffSection.mk X hX
  have hinner : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (T% (fun b : M => gInvDiffRaisedEndo (I := I) g₀ g₁ b (Xs b))) :=
    gInvDiffRaisedEndo_apply_field_contMDiff (I := I) g₀ g₁ Xs
  let D : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    ContMDiffSection.mk (fun b : M => gInvDiffRaisedEndo (I := I) g₀ g₁ b (Xs b)) hinner
  let Zs : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ := ContMDiffSection.mk Z hZ
  have hpair : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun b : M => ccTensorBilinSymm (I := I) g₀ T₁ b (D b) (Zs b)) :=
    contMDiff_ccTensorBilinSymm_pairing (I := I) g₀ T₁ D Zs
  refine hpair.congr (fun b => ?_)
  change ccTensorBilinSymm (I := I) g₀ T₁ b (gInvDiffRaisedEndo (I := I) g₀ g₁ b (X b)) (Z b) =
    crossCometricBi (I := I) g₀ g₁ T₁ b (X b) (Z b)
  rw [crossCometricBi_apply]

/-- The pointwise `(0,2)`-tensor model value of the cometric cross-correction. -/
private def crossCometricModelFun (g₀ g₁ : SmoothRiemannianMetric I M)
    (T₁ : Integral.L2.SmoothCcTensor g₀ 0 2) (x : M) : Tensor0SSpace 2 I x :=
  Tensor0SSpace.ofModel (I := I)
    (biForm₂ToModel (TangentSpace I x) (crossCometricBi (I := I) g₀ g₁ T₁ x))

set_option linter.unusedSectionVars false in
private theorem crossCometricModelFun_toModel_apply (g₀ g₁ : SmoothRiemannianMetric I M)
    (T₁ : Integral.L2.SmoothCcTensor g₀ 0 2) (x : M) (v : Fin 2 → TangentSpace I x) :
    Tensor0SSpace.toModel (crossCometricModelFun (I := I) g₀ g₁ T₁ x) v =
      crossCometricBi (I := I) g₀ g₁ T₁ x (v 0) (v 1) := by
  unfold crossCometricModelFun
  rw [Tensor0SSpace.toModel_ofModel]
  exact biForm₂ToModel_apply (TangentSpace I x) (crossCometricBi (I := I) g₀ g₁ T₁ x) v

/-- **The cometric cross-correction as a smooth covariant `(0,2)`-tensor field.** -/
def crossCometricField (g₀ g₁ : SmoothRiemannianMetric I M)
    (T₁ : Integral.L2.SmoothCcTensor g₀ 0 2) :
    Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) ∞ 2 :=
  letI := tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 2
  letI := TangentBundle.contMDiffVectorBundle (I := I) (M := M) (n := ∞)
  ⟨fun x => crossCometricModelFun (I := I) g₀ g₁ T₁ x, by
    let d := Module.finrank ℝ E
    let b : Module.Basis (Fin d) ℝ E := chartModelBasis E
    refine (contMDiff_multilinearSection_iff_coord (TangentSpace I) ∞ b _).mpr
      fun σ x₀ => ?_
    have hcomp : ContMDiffOn I 𝓘(ℝ, ℝ) ∞
        (fun x : M =>
          crossCometricBi (I := I) g₀ g₁ T₁ x
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
          (fun bb : M => crossCometricBi (I := I) g₀ g₁ T₁ bb
            ((S (σ 0)) bb) ((S (σ 1)) bb)) :=
        crossCometricBi_pairing_contMDiff (I := I) g₀ g₁ T₁ (hSk (σ 0)) (hSk (σ 1))
      have hchart_at : ContMDiffAt I 𝓘(ℝ, ℝ) ∞
          (fun x : M => crossCometricBi (I := I) g₀ g₁ T₁ x
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
    change Tensor0SSpace.toModel (crossCometricModelFun (I := I) g₀ g₁ T₁ x)
        (fun j => (trivializationAt E (TangentSpace I) x₀).symmL ℝ x (b (σ j))) = _
    rw [crossCometricModelFun_toModel_apply]
    rfl⟩

/-- The cometric cross-correction as a smooth mixed `(0,2)`-tensor section. -/
def crossCometricMixedSection (g₀ g₁ : SmoothRiemannianMetric I M)
    (T₁ : Integral.L2.SmoothCcTensor g₀ 0 2) :
    Cₛ^∞⟮I; TensorRSModel 0 2 ℝ E, (fun x : M => TensorRSSpace 0 2 I x)⟯ :=
  MixedSection.fromMultilinearSection (𝕜 := ℝ) (F := E) (IB := I)
    (E := (TangentSpace I : M → Type _)) ∞ (crossCometricField (I := I) g₀ g₁ T₁)

/-- **The cometric cross-correction `h ⌟ D` as a `SmoothCcTensor g₀ 0 2`.**  Its fibre value is
`toModel(crossCometricSection g₁ g₀ T₁ x) ![a, b] = ccTensorBilinSymm g₀ T₁ x (gInvDiffRaisedEndo g₀
g₁ x a) b` (`crossCometricSection_toModel_apply`); compact support is automatic on `M`. -/
def crossCometricSection (g₁ g₀ : SmoothRiemannianMetric I M)
    (T₁ : Integral.L2.SmoothCcTensor g₀ 0 2) :
    Integral.L2.SmoothCcTensor g₀ 0 2 where
  toSection := crossCometricMixedSection (I := I) g₀ g₁ T₁
  hasCompactSupport := HasCompactSupport.of_compactSpace _

set_option linter.unusedSectionVars false in
/-- **The fibre value of the cometric cross-correction section.** -/
theorem crossCometricSection_toModel_apply (g₁ g₀ : SmoothRiemannianMetric I M)
    (T₁ : Integral.L2.SmoothCcTensor g₀ 0 2) (x : M) (a b : TangentSpace I x) :
    Tensor0SSpace.toModel
        ((crossCometricSection (I := I) g₁ g₀ T₁).toSection x
          (ContinuousMultilinearMap.constOfIsEmpty ℝ
            (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))) ![a, b] =
      ccTensorBilinSymm (I := I) g₀ T₁ x (gInvDiffRaisedEndo (I := I) g₀ g₁ x a) b := by
  classical
  change Tensor0SSpace.toModel
      ((MixedSection.eval₀ (F := E) (E := (TangentSpace I : M → Type _)) x).smulRight
          (crossCometricField (I := I) g₀ g₁ T₁ x)
        (ContinuousMultilinearMap.constOfIsEmpty ℝ
          (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))) ![a, b] = _
  rw [ContinuousLinearMap.smulRight_apply, MixedSection.eval₀_apply,
    ContinuousMultilinearMap.constOfIsEmpty_apply, one_smul]
  change Tensor0SSpace.toModel (crossCometricModelFun (I := I) g₀ g₁ T₁ x) ![a, b] = _
  rw [crossCometricModelFun_toModel_apply, crossCometricBi_apply]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]

/-! ### The unit-toModel reading of the realized perturbation section -/

set_option linter.unusedSectionVars false in
/-- **The unit-toModel reading of the realized symmetric perturbation section.**  For any `(0,2)`
section `T₁`, the unit-evaluated model value of `realizeSymmCcTensor g₀ T₁` is the symmetric realized
perturbation `ccTensorBilinSymm g₀ T₁ x a b`.  This is the direct `(0,2)`-tensor reading: the
unit-evaluated `toModel` of a `(0,2)` section is its extracted bilinear form `ccTensorBilin`
(`ccTensorBilin_apply`, `ccTensorModel`, `ccTensorMultilinear_apply`), and that of `realizeSymmCcTensor
g₀ T₁` is `ccTensorBilinSymm g₀ T₁` (`realizeSymmCcTensor_ccTensorBilin_apply`). -/
theorem realizeSymmCcTensor_toModel_unit (g₀ : SmoothRiemannianMetric I M)
    (T₁ : Integral.L2.SmoothCcTensor g₀ 0 2) (x : M) (a b : TangentSpace I x) :
    Tensor0SSpace.toModel
        ((realizeSymmCcTensor (I := I) g₀ T₁).toSection x
          (ContinuousMultilinearMap.constOfIsEmpty ℝ
            (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))) ![a, b] =
      ccTensorBilinSymm (I := I) g₀ T₁ x a b := by
  have hbil := realizeSymmCcTensor_ccTensorBilin_apply (I := I) g₀ T₁ x a b
  rw [ccTensorBilin_apply, ccTensorModel, ccTensorMultilinear_apply] at hbil
  exact hbil

/-! ### The section-level resolvent Koszul identity -/

set_option linter.unusedSectionVars false in
/-- **The section-level resolvent Koszul identity.**  Under the realize-tie `g₁ = g₀ +
ccTensorBilinSymm g₀ T₁`, the cometric inverse-difference section splits as the *negated* clean linear
part (the realized perturbation `realizeSymmCcTensor g₀ T₁`) minus the fibre-small cross correction:

```
cometricInverseDiffSection g₁ g₀ = −realizeSymmCcTensor g₀ T₁ − crossCometricSection g₁ g₀ T₁.
```

This is the inverse-Gram resolvent split `g₁⁻¹ − g₀⁻¹ = −g₁⁻¹(g₁ − g₀)g₀⁻¹` at the `(0,2)`-section
level.  Proved by unit-extensionality (`tensor0s_ext_unitZero`): the unit-evaluated model fibre value
of the left side is `g₀(D a, b)` (`cometricInverseDiffSection_toModel_apply`), which the resolvent
pairing `inner_g1_gInvDiffRaisedEndo` together with the realize-tie rewrites as `−h(a, b) − h(D a, b)`
— exactly the unit-evaluated model fibre value of the right side
(`realizeSymmCcTensor_toModel_unit`, `crossCometricSection_toModel_apply`). -/
theorem cometricInverseDiffSection_eq_neg_realizeSymm_sub_cross
    (g₁ g₀ : SmoothRiemannianMetric I M) (T₁ : Integral.L2.SmoothCcTensor g₀ 0 2)
    (hr : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T₁ y v w) :
    cometricInverseDiffSection (I := I) g₁ g₀ =
      -realizeSymmCcTensor (I := I) g₀ T₁ - crossCometricSection (I := I) g₁ g₀ T₁ := by
  classical
  apply Integral.L2.SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply tensor0s_ext_unitZero (I := I) (M := M) (s := 2)
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro v
  have hunit : (unitZeroSec (I := I) (M := M) x : Tensor0SSpace 0 I x) =
      ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ) := rfl
  have hvtuple : (![v 0, v 1] : Fin 2 → TangentSpace I x) = v := by
    funext i; fin_cases i <;> rfl
  -- LHS unit model value: `g₀(D (v 0), v 1)`.
  have hL : Tensor0SSpace.toModel
      ((cometricInverseDiffSection (I := I) g₁ g₀).toSection x
        (unitZeroSec (I := I) (M := M) x)) v =
      g₀.inner x (gInvDiffRaisedEndo (I := I) g₀ g₁ x (v 0)) (v 1) := by
    rw [hunit]
    have h := cometricInverseDiffSection_toModel_apply (I := I) g₁ g₀ x (v 0) (v 1)
    rw [hvtuple] at h
    exact h
  -- RHS unit model value: `−h(v 0, v 1) − h(D (v 0), v 1)`.
  have hR : Tensor0SSpace.toModel
      ((-realizeSymmCcTensor (I := I) g₀ T₁ - crossCometricSection (I := I) g₁ g₀ T₁).toSection x
        (unitZeroSec (I := I) (M := M) x)) v =
      -ccTensorBilinSymm (I := I) g₀ T₁ x (v 0) (v 1)
        - ccTensorBilinSymm (I := I) g₀ T₁ x (gInvDiffRaisedEndo (I := I) g₀ g₁ x (v 0)) (v 1) := by
    rw [hunit]
    rw [show (-realizeSymmCcTensor (I := I) g₀ T₁ - crossCometricSection (I := I) g₁ g₀ T₁).toSection x
          (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ)) =
        -((realizeSymmCcTensor (I := I) g₀ T₁).toSection x
            (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ)))
          - (crossCometricSection (I := I) g₁ g₀ T₁).toSection x
            (ContinuousMultilinearMap.constOfIsEmpty ℝ
              (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ)) from by
      rw [Integral.L2.SmoothCcTensor.toSection_sub, Integral.L2.SmoothCcTensor.toSection_neg,
        ContMDiffSection.coe_sub, ContMDiffSection.coe_neg, Pi.sub_apply, Pi.neg_apply,
        ContinuousLinearMap.sub_apply, ContinuousLinearMap.neg_apply]]
    rw [Tensor0SSpace.toModel_sub, Tensor0SSpace.toModel_neg,
      ContinuousMultilinearMap.sub_apply, ContinuousMultilinearMap.neg_apply]
    have hreal := realizeSymmCcTensor_toModel_unit (I := I) g₀ T₁ x (v 0) (v 1)
    have hcross := crossCometricSection_toModel_apply (I := I) g₁ g₀ T₁ x (v 0) (v 1)
    rw [hvtuple] at hreal hcross
    rw [hreal, hcross]
  -- The resolvent identity: `g₀(D a, b) = −h(a, b) − h(D a, b)`.
  have hp := inner_g1_gInvDiffRaisedEndo (I := I) g₀ g₁ x (v 0) (v 1)
  have htie_ab := hr x (v 0) (v 1)
  have htie_Db := hr x (gInvDiffRaisedEndo (I := I) g₀ g₁ x (v 0)) (v 1)
  linarith [hp, htie_ab, htie_Db]

/-! ## Stage 3 — the order-`0` family-uniform fibre bound (the base case of the jet tower)

The order-`0` `g₀`-fibre norm of the cometric inverse-difference section reads the raised
representative `D = gInvDiffRaisedEndo g₀ g₁` through the extracted bilinear form
`ccTensorBilin g₀ (cometricInverseDiffSection g₁ g₀) x = cometricInvDiffBi g₀ g₁ x = g₀(D ·, ·)`.
Expanding the squared fibre norm in a `g₀`-orthonormal frame and collapsing the second index by
Parseval gives `rfns = ∑_a g₀(D e_a, D e_a)`, each term bounded by the per-vector raised Neumann bound
`sqrt_inner_gInvDiffRaisedEndo_le` (squared); the family-uniform fibre-smallness `≤ dim · (δ/(1−δ))²`
follows.  This is the base case `p = 0` of the differentiated-Neumann Koszul jet tower. -/

set_option linter.unusedSectionVars false in
/-- **The extracted bilinear form of the cometric inverse-difference section is the lowered raised
representative.**  `ccTensorBilin g₀ (cometricInverseDiffSection g₁ g₀) x v w = g₀.inner x
(gInvDiffRaisedEndo g₀ g₁ x v) w`: the extracted bilinear form is the unit-evaluated `toModel` reading
(`ccTensorBilin_apply`, `ccTensorModel`, `ccTensorMultilinear_apply`), which is the section's fibre
value `cometricInverseDiffSection_toModel_apply`. -/
theorem ccTensorBilin_cometricInverseDiffSection_apply (g₁ g₀ : SmoothRiemannianMetric I M) (x : M)
    (v w : TangentSpace I x) :
    ccTensorBilin (I := I) g₀ (cometricInverseDiffSection (I := I) g₁ g₀) x v w =
      g₀.inner x (gInvDiffRaisedEndo (I := I) g₀ g₁ x v) w := by
  rw [ccTensorBilin_apply, ccTensorModel, ccTensorMultilinear_apply]
  exact cometricInverseDiffSection_toModel_apply (I := I) g₁ g₀ x v w

set_option linter.unusedSectionVars false in
/-- **The order-`0` `g₀`-fibre norm of the cometric inverse-difference section as a frame sum.**  In a
`g₀`-orthonormal tangent frame `e`, `rfns g₀ 0 2 x (cometricInverseDiffSection g₁ g₀ .toSection x) =
∑_J (g₀(D e_{J 0}, e_{J 1}))²`, where `D = gInvDiffRaisedEndo g₀ g₁`.  This is the
`riemannianFiberNormSq`-as-frame-pair-square-sum identity (`fiberNormSqSummand_eq_component_sq`,
`ccTensorBilin_eq_fiberNormSqComponent`) applied to the extracted bilinear form
`ccTensorBilin_cometricInverseDiffSection_apply`. -/
theorem riemannianFiberNormSq_cometricInverseDiffSection_frameSum
    (g₁ g₀ : SmoothRiemannianMetric I M) (x : M)
    {n : ℕ} (e : Fin n → TangentSpace I x)
    (hrepr : ∀ S : TensorRSSpace 0 2 I x,
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x S =
        ∑ K : Fin 0 → Fin n, ∑ J : Fin 2 → Fin n,
          fiberNormSqSummand (I := I) (M := M) g₀ x 0 2 S n e K J) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x
        ((cometricInverseDiffSection (I := I) g₁ g₀).toSection x) =
      ∑ J : Fin 2 → Fin n,
        (g₀.inner x (gInvDiffRaisedEndo (I := I) g₀ g₁ x (e (J 0))) (e (J 1))) ^ 2 := by
  classical
  rw [hrepr ((cometricInverseDiffSection (I := I) g₁ g₀).toSection x)]
  rw [Fintype.sum_subsingleton
    (fun K : Fin 0 → Fin n => ∑ J : Fin 2 → Fin n,
      fiberNormSqSummand (I := I) (M := M) g₀ x 0 2
        ((cometricInverseDiffSection (I := I) g₁ g₀).toSection x) n e K J)
    (fun k : Fin 0 => k.elim0)]
  refine Finset.sum_congr rfl (fun J _ => ?_)
  rw [fiberNormSqSummand_eq_component_sq,
    ccTensorBilin_eq_fiberNormSqComponent (I := I) g₀ (cometricInverseDiffSection (I := I) g₁ g₀) x e
      (fun k : Fin 0 => k.elim0) J,
    ccTensorBilin_cometricInverseDiffSection_apply]

set_option linter.unusedSectionVars false in
/-- **The order-`0` family-uniform `g₀`-fibre bound of the cometric inverse-difference section.**  For
the realize-tie `g₁ = g₀ + h` with the fibre gate `gFibreOpBound g₀ h δ` and `δ < 1`, the order-`0`
`g₀`-fibre norm of the cometric inverse-difference section is bounded family-uniformly:

  `rfns g₀ 0 2 x (cometricInverseDiffSection g₁ g₀ .toSection x) ≤ dim · (δ / (1 − δ))²`.

This is the **base case** (order `0`) of the differentiated-Neumann Koszul jet tower.  Expanding the
fibre norm in a `g₀`-orthonormal frame (`riemannianFiberNormSq_cometricInverseDiffSection_frameSum`),
splitting `J` into `(a, b)` and collapsing the `b`-sum by Parseval gives `∑_a g₀(D e_a, D e_a)`; the
per-vector raised Neumann bound `sqrt_inner_gInvDiffRaisedEndo_le` (squared, on unit frame vectors)
bounds each term by `(δ/(1−δ))²`, so the total is `≤ dim · (δ/(1−δ))²`.

**Non-vacuity.**  At `g₁ = g₀` (realize `h = 0`, gate `δ = 0`) the raised representative vanishes
(`gInvDiffRaisedEndo_self`), so the bound is `0 ≤ 0`; the `δ`-arm genuinely carries the inverse-Gram
smallness. -/
theorem riemannianFiberNormSq_cometricInverseDiffSection_order0_le
    (g₀ g₁ : SmoothRiemannianMetric I M)
    (h : ∀ y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + h y v w)
    {δ : ℝ} (hδ_lt : δ < 1) (hδ_nn : 0 ≤ δ) (hδ : gFibreOpBound (I := I) g₀ h δ)
    (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x
        ((cometricInverseDiffSection (I := I) g₁ g₀).toSection x)
      ≤ (Module.finrank ℝ E : ℝ) * (δ / (1 - δ)) ^ 2 := by
  classical
  set Λ : TangentSpace I x →L[ℝ] TangentSpace I x := gInvDiffRaisedEndo (I := I) g₀ g₁ x with hΛ
  -- The `g₀`-orthonormal frame with Parseval and the `(0,2)`-fibre-norm frame-sum representation.
  obtain ⟨n, e, hn, horth, hpar, hexpand, hrepr⟩ :=
    Integral.Connection.tangent_frame_expansion (I := I) (M := M) g₀ x
  have hframeSum := riemannianFiberNormSq_cometricInverseDiffSection_frameSum (I := I) g₁ g₀ x e hrepr
  rw [hframeSum]
  set r : ℝ := δ / (1 - δ) with hr
  have hcoeff : 0 < 1 - δ := by linarith
  have hr_nn : 0 ≤ r := div_nonneg hδ_nn hcoeff.le
  -- Per-vector squared raised bound `g₀(Λ a, Λ a) ≤ r²` for a unit frame vector `a := e i`.
  have hper : ∀ i : Fin n, g₀.inner x (Λ (e i)) (Λ (e i)) ≤ r ^ 2 := by
    intro i
    have hsqrt := sqrt_inner_gInvDiffRaisedEndo_le (I := I) g₀ g₁ h htie hδ_lt hδ_nn hδ x (e i)
    rw [← hΛ] at hsqrt
    have he1 : g₀.inner x (e i) (e i) = 1 := by rw [horth i i]; simp
    rw [he1, Real.sqrt_one, mul_one] at hsqrt
    have hLnn : 0 ≤ g₀.inner x (Λ (e i)) (Λ (e i)) :=
      metric_inner_self_nonneg (I := I) (M := M) g₀ x (Λ (e i))
    have hsq := Real.sq_sqrt hLnn
    nlinarith [Real.sqrt_nonneg (g₀.inner x (Λ (e i)) (Λ (e i))), hsqrt, hsq, hr_nn]
  -- Reindex `∑_J` over `J : Fin 2 → Fin n` as `∑_a ∑_b`, apply Parseval in `b`, then bound in `a`.
  have hJsplit : (∑ J : Fin 2 → Fin n, (g₀.inner x (Λ (e (J 0))) (e (J 1))) ^ 2)
      = ∑ a : Fin n, ∑ b : Fin n, (g₀.inner x (Λ (e a)) (e b)) ^ 2 := by
    rw [← (finTwoArrowEquiv (Fin n)).symm.sum_comp
      (fun J : Fin 2 → Fin n => (g₀.inner x (Λ (e (J 0))) (e (J 1))) ^ 2)]
    rw [Fintype.sum_prod_type]; rfl
  -- Parseval collapses the `b`-sum to `g₀(Λ e_a, Λ e_a)` (using `g₀`-symmetry to match the frame
  -- index in the first slot, as `tangent_frame_expansion`'s Parseval reads `∑_b g₀(e_b, ·)²`).
  have hParseval : (∑ a : Fin n, ∑ b : Fin n, (g₀.inner x (Λ (e a)) (e b)) ^ 2)
      = ∑ a : Fin n, g₀.inner x (Λ (e a)) (Λ (e a)) := by
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [show (∑ b : Fin n, (g₀.inner x (Λ (e a)) (e b)) ^ 2)
          = ∑ b : Fin n, (g₀.inner x (e b) (Λ (e a))) ^ 2 from
        Finset.sum_congr rfl (fun b _ => by rw [g₀.symm x (Λ (e a)) (e b)])]
    exact hpar (Λ (e a))
  -- Bound the `a`-sum: each summand ≤ r², so the sum ≤ n · r².
  have hsum_le : (∑ a : Fin n, g₀.inner x (Λ (e a)) (Λ (e a))) ≤ (n : ℝ) * r ^ 2 := by
    calc (∑ a : Fin n, g₀.inner x (Λ (e a)) (Λ (e a)))
        ≤ ∑ _a : Fin n, r ^ 2 := Finset.sum_le_sum (fun a _ => hper a)
      _ = (n : ℝ) * r ^ 2 := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]; ring
  have hnE : (n : ℝ) = (Module.finrank ℝ E : ℝ) := by
    have hnn : n = Module.finrank ℝ E := by rw [hn]; rfl
    rw [hnn]
  rw [hJsplit, hParseval]
  rw [← hnE]; exact hsum_le

end DifferentialGeometry.Analysis.Sobolev.TensorHilbert

end
