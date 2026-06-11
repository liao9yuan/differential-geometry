import DifferentialGeometry.Geometry.Connection.TensorNabla.VectorFieldCovariantGradientSection

/-! # The lowered-covariant-gradient-difference telescope of the DeTurck vector field

For two realized metrics `g₁ = g₀ + T₁`, `g₂ = g₀ + T₂` on a closed Riemannian manifold `(M, g₀)`
(the realization hypotheses `hr1`/`hr2` of `ccTensorBilinSymm`-perturbations) and background `g_bg`,
this file builds the **three-slot telescope** of the lowered covariant gradient of the DeTurck vector
field `W_k = deTurckVF g_k g_bg`.  With `loweredCovGradDeTurckVF` the `(0,2)`-section with fibre
`(v, w) ↦ g(∇^g_v W, w)` (`VectorFieldCovariantGradientSection.lean`), the identity is
$$
  g_1(\nabla^{g_1}_v W_1, w) - g_2(\nabla^{g_2}_v W_2, w)
    = \underbrace{[g_1-g_2](\nabla^{g_1}_v W_1, w)}_{(A)}
    + \underbrace{g_2(\mathrm{connDiff}(g_1,g_2)\,W_1\,v, w)}_{(B)}
    + \underbrace{g_2(\nabla^{g_2}_v(W_1-W_2), w)}_{(C)} .
$$

## The three concrete `(0,2)`-builders

* `metricDiffPairingSection g₀ g₁ g_bg T₁ T₂` — **(A) the metric-difference pairing**, fibre
  `(v, w) ↦ ccTensorBilinSymm g₀ (T₁ − T₂) x (∇^{g₁}_v W₁) w`: the realized difference factor
  `T₁ − T₂` paired against the **endpoint** gradient field `∇^{g₁} W₁` in slot one.
* `connDiffActionSection g₀ g₁ g₂ g_bg` — **(B) the connection-difference action**, fibre
  `(v, w) ↦ g₂(connDiff g₁ g₂ x (W₁ x) v, w)`: the classical "difference of connections acting on a
  field" term (`connDiff g₁ g₂ x (W₁ x) v = ∇^{g₁}_v W₁ − ∇^{g₂}_v W₁`, `connDiff_apply`).
* `fieldDiffGradSection g₀ g₁ g₂ g_bg` — **(C) the field-difference gradient**, fibre
  `(v, w) ↦ g₂(∇^{g₂}_v (W₁ − W₂), w)`: the `g₂`-lowered Levi-Civita gradient of the *difference*
  section `W₁ − W₂`.

All three are built through the generic chart-frame bilinear-form field-builder `bilinFormSection`
(the same `contMDiff_multilinearSection_iff_coord` route as `loweredCovGradDeTurckVFField`), with
`_toModel_apply` fibre-value lemmas.

## The telescope

`loweredCovGradDeTurckVF_sub_eq_telescope` lands the identity as a `SmoothCcTensor g₀ 0 2` equation
(LHS is the `g₀`-retag difference `loweredCovGradDeTurckVFRetagG0 g₀ g₁ g_bg
− loweredCovGradDeTurckVFRetagG0 g₀ g₂ g_bg`), proved by unit-`(0,0)`-evaluation fibre
extensionality through the bilinear telescope `loweredCovGradDeTurckVFBilin_sub_eq_telescope`.  The
fibre algebra telescopes the three summands (`(A)` carries `g₁−g₂` against `∇^{g₁}W₁`; `(B)` carries
`g₂(∇^{g₁}W₁ − ∇^{g₂}W₁)`; `(C)` carries `g₂(∇^{g₂}W₁ − ∇^{g₂}W₂)`) onto `g₁(∇^{g₁}W₁) −
g₂(∇^{g₂}W₂)`.

## Non-vacuity

At `T₁ = T₂` (so `g₁ = g₂` fibrewise where the realizations agree) every summand collapses and the
identity reads `0 = 0`; the `g_bg`-dependence sits in `W₁`/`W₂` on *both* sides, each summand
carrying it. -/

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
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization

/-! ### The covariant-derivative jet facts (boundaryless-free block)

The two `MDiffAt`-gated covariant-derivative identities below are pure tangent-bundle facts; they are
proved in the connection-difference variable context (without `CompactSpace` / `Boundaryless`, whose
tangent-bundle `ChartedSpace` instances obstruct the `MDiffAt (T% ·)` elaboration), then consumed at
the fibre level by the telescope. -/

section CovDerivJets

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

/-- **The connection difference acting on the endpoint DeTurck field.**  For `W₁ = deTurckVF g₁ g_bg`
the connection-difference tensor evaluated at `W₁ x` reproduces the difference of the two Levi-Civita
covariant gradients of `W₁`:
`connDiff g₁ g₂ x (W₁ x) v = (LeviCivita g₁) W₁ x v − (LeviCivita g₂) W₁ x v` (`connDiff_apply`). -/
theorem connDiff_deTurckVF_apply (g₁ g₂ g_bg : SmoothRiemannianMetric I M)
    (x : M) (v : TangentSpace I x) :
    connDiff (I := I) g₁ g₂ x (deTurckVF (I := I) g₁ g_bg x) v =
      (LeviCivita (I := I) g₁)
          (deTurckVF (I := I) g₁ g_bg : ∀ z : M, TangentSpace I z) x v
      - (LeviCivita (I := I) g₂)
          (deTurckVF (I := I) g₁ g_bg : ∀ z : M, TangentSpace I z) x v := by
  have hσ : MDiffAt (T% (deTurckVF (I := I) g₁ g_bg : ∀ z : M, TangentSpace I z)) x :=
    (deTurckVF (I := I) g₁ g_bg).mdifferentiableAt
  exact connDiff_apply (I := I) g₁ g₂ hσ v

/-- **Section-subtraction of the Levi-Civita covariant gradient.**  For the section difference
`W₁ − W₂`, the `g₂`-Levi-Civita covariant gradient is additive:
`(LeviCivita g₂)(W₁ − W₂) x v = (LeviCivita g₂) W₁ x v − (LeviCivita g₂) W₂ x v`, by the additivity
axiom `IsCovariantDerivativeOn.add` of the bundled Levi-Civita derivative. -/
theorem leviCivita_section_sub_apply (g₂ : SmoothRiemannianMetric I M)
    (W₁ W₂ : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) (v : TangentSpace I x) :
    (LeviCivita (I := I) g₂)
        ((W₁ - W₂ : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
          ∀ z : M, TangentSpace I z) x v =
      (LeviCivita (I := I) g₂) (W₁ : ∀ z : M, TangentSpace I z) x v
      - (LeviCivita (I := I) g₂) (W₂ : ∀ z : M, TangentSpace I z) x v := by
  have hD : MDiffAt (T% fun y => (W₁ - W₂ :
      Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) y) x := (W₁ - W₂).mdifferentiableAt
  have hW₂ : MDiffAt (T% fun y => (W₂ : ∀ z : M, TangentSpace I z) y) x := W₂.mdifferentiableAt
  have hadd := (LeviCivita (I := I) g₂).isCovariantDerivativeOnUniv.add hD hW₂ (mem_univ x)
  have hsum : ((fun y => (W₁ - W₂ : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) y)
      + (fun y => (W₂ : ∀ z : M, TangentSpace I z) y)) =
      (fun y => (W₁ : ∀ z : M, TangentSpace I z) y) := by
    funext y
    rw [Pi.add_apply, ContMDiffSection.coe_sub]
    simp [Pi.sub_apply]
  rw [hsum] at hadd
  have hgoal := congrArg (fun (c : TangentSpace I x →L[ℝ] TangentSpace I x) => c v) hadd
  simp only [ContinuousLinearMap.add_apply] at hgoal
  rw [hgoal]
  abel

end CovDerivJets

/-! ### The closed-manifold telescope -/

section Telescope

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

/-! #### Generic bilinear-form → smooth `(0,2)`-tensor field helper -/

/-- The pointwise model `(0,2)`-tensor value of a bilinear-form family. -/
def bilinFormModelFun (φ : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) (x : M) :
    Tensor0SSpace 2 I x :=
  Tensor0SSpace.ofModel (bilinFormToModel (TangentSpace I x) (φ x))

set_option linter.unusedSectionVars false in
theorem bilinFormModelFun_toModel_apply
    (φ : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) (x : M)
    (v : Fin 2 → TangentSpace I x) :
    Tensor0SSpace.toModel (bilinFormModelFun (I := I) φ x) v = φ x (v 0) (v 1) := by
  unfold bilinFormModelFun
  rw [Tensor0SSpace.toModel_ofModel]
  exact bilinFormToModel_apply (TangentSpace I x) (φ x) v

/-- **Generic chart-frame field-builder.**  A bilinear-form family whose pairing on smooth fields is
smooth assembles into a smooth covariant `(0,2)`-tensor field, by the
`contMDiff_multilinearSection_iff_coord` chart-`x₀`-pushforward-frame route (the shared template of
`loweredCovGradDeTurckVFField` / `loweredConnDiffField`). -/
def bilinFormField (φ : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
    (hpair : ∀ {X Y : Π b : M, TangentSpace I b},
      ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X) → ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Y) →
      ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun b : M => φ b (X b) (Y b))) :
    Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) ∞ 2 :=
  letI := tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 2
  letI := TangentBundle.contMDiffVectorBundle (I := I) (M := M) (n := ∞)
  ⟨fun x => bilinFormModelFun (I := I) φ x, by
    let d := Module.finrank ℝ E
    let b : Module.Basis (Fin d) ℝ E := chartModelBasis E
    refine (contMDiff_multilinearSection_iff_coord (TangentSpace I) ∞ b _).mpr
      fun σ x₀ => ?_
    have hcomp : ContMDiffOn I 𝓘(ℝ, ℝ) ∞
        (fun x : M => φ x (chartFrameVec (I := I) x₀ (σ 0) x) (chartFrameVec (I := I) x₀ (σ 1) x))
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
      have hp : ContMDiff I 𝓘(ℝ, ℝ) ∞
          (fun bb : M => φ bb ((S (σ 0)) bb) ((S (σ 1)) bb)) :=
        hpair (hSk (σ 0)) (hSk (σ 1))
      have hchart_at : ContMDiffAt I 𝓘(ℝ, ℝ) ∞
          (fun x : M => φ x (chartFrameVec (I := I) x₀ (σ 0) x)
            (chartFrameVec (I := I) x₀ (σ 1) x)) x := by
        refine (hp x).congr_of_eventuallyEq ?_
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
    change Tensor0SSpace.toModel (bilinFormModelFun (I := I) φ x)
        (fun j => (trivializationAt E (TangentSpace I) x₀).symmL ℝ x (b (σ j))) = _
    rw [bilinFormModelFun_toModel_apply]
    rfl⟩

/-- **Generic bilinear-form `(0,2)`-section.**  Compact support is automatic on the compact
manifold `M`. -/
def bilinFormSection (g₀ : SmoothRiemannianMetric I M)
    (φ : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
    (hpair : ∀ {X Y : Π b : M, TangentSpace I b},
      ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X) → ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Y) →
      ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun b : M => φ b (X b) (Y b))) :
    Integral.L2.SmoothCcTensor g₀ 0 2 where
  toSection :=
    MixedSection.fromMultilinearSection (𝕜 := ℝ) (F := E) (IB := I)
      (E := (TangentSpace I : M → Type _)) ∞ (bilinFormField (I := I) φ hpair)
  hasCompactSupport := HasCompactSupport.of_compactSpace _

set_option linter.unusedSectionVars false in
theorem bilinFormSection_toModel_apply (g₀ : SmoothRiemannianMetric I M)
    (φ : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
    (hpair : ∀ {X Y : Π b : M, TangentSpace I b},
      ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X) → ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Y) →
      ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun b : M => φ b (X b) (Y b)))
    (x : M) (v : Fin 2 → TangentSpace I x) :
    Tensor0SSpace.toModel
        ((bilinFormSection (I := I) g₀ φ hpair).toSection x
          (ContinuousMultilinearMap.constOfIsEmpty ℝ
            (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))) v =
      φ x (v 0) (v 1) := by
  classical
  change Tensor0SSpace.toModel
      ((MixedSection.eval₀ (F := E) (E := (TangentSpace I : M → Type _)) x).smulRight
          (bilinFormField (I := I) φ hpair x)
        (ContinuousMultilinearMap.constOfIsEmpty ℝ
          (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))) v = _
  rw [ContinuousLinearMap.smulRight_apply, MixedSection.eval₀_apply,
    ContinuousMultilinearMap.constOfIsEmpty_apply, one_smul]
  change Tensor0SSpace.toModel (bilinFormModelFun (I := I) φ x) v = _
  rw [bilinFormModelFun_toModel_apply]

/-! #### (A) The metric-difference pairing -/

/-- **(A) The metric-difference pairing bilinear form.**
`(v, w) ↦ ccTensorBilinSymm g₀ (T₁ − T₂) x (∇^{g₁}_v W₁) w`, `W₁ = deTurckVF g₁ g_bg`. -/
def metricDiffPairingBilin (g₀ g₁ g_bg : SmoothRiemannianMetric I M)
    (T₁ T₂ : Integral.L2.SmoothCcTensor g₀ 0 2) (x : M) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  (ccTensorBilinSymm (I := I) g₀ (T₁ - T₂) x).comp
    ((LeviCivita (I := I) g₁)
      (deTurckVF (I := I) g₁ g_bg : ∀ x : M, TangentSpace I x) x)

set_option linter.unusedSectionVars false in
@[simp] theorem metricDiffPairingBilin_apply (g₀ g₁ g_bg : SmoothRiemannianMetric I M)
    (T₁ T₂ : Integral.L2.SmoothCcTensor g₀ 0 2) (x : M) (v w : TangentSpace I x) :
    metricDiffPairingBilin (I := I) g₀ g₁ g_bg T₁ T₂ x v w =
      ccTensorBilinSymm (I := I) g₀ (T₁ - T₂) x
        ((LeviCivita (I := I) g₁)
          (deTurckVF (I := I) g₁ g_bg : ∀ x : M, TangentSpace I x) x v) w := by
  rfl

set_option linter.unusedSectionVars false in
/-- **(A) Smoothness of the metric-difference pairing on smooth fields.**  The `ccTensorBilinSymm`
pairing (`contMDiff_ccTensorBilinSymm_pairing`) of the smooth covariant-gradient field `∇^{g₁} W₁`
(`LeviCivita_section_contMDiffOn_univ` on the smooth field `W₁`, then `clm_bundle_apply`) and the
smooth direction frame. -/
theorem metricDiffPairingBilin_pairing_contMDiff (g₀ g₁ g_bg : SmoothRiemannianMetric I M)
    (T₁ T₂ : Integral.L2.SmoothCcTensor g₀ 0 2)
    {X Y : Π b : M, TangentSpace I b}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Y)) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun b : M => metricDiffPairingBilin (I := I) g₀ g₁ g_bg T₁ T₂ b (X b) (Y b)) := by
  classical
  set W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ := deTurckVF (I := I) g₁ g_bg with hW
  have hWsmooth : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ((∞ : WithTop ℕ∞) + 1)
      (fun x : M => (⟨x, (W : ∀ x : M, TangentSpace I x) x⟩ : TotalSpace E (TangentSpace I)))
      Set.univ := by
    have h_le : ((∞ : WithTop ℕ∞) + 1) ≤ ∞ := by rw [ENat.coe_top_add_one]
    exact (W.contMDiff.of_le h_le).contMDiffOn
  have hcov : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun x : M =>
        (⟨x, (LeviCivita (I := I) g₁) (W : ∀ x : M, TangentSpace I x) x⟩ :
          TotalSpace (E →L[ℝ] E) (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x))) := by
    rw [← contMDiffOn_univ]
    exact LeviCivita_section_contMDiffOn_univ (I := I) g₁ hWsmooth
  have hD : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M =>
        (TotalSpace.mk' E (E := fun y : M => TangentSpace I y) b
          ((LeviCivita (I := I) g₁) (W : ∀ x : M, TangentSpace I x) b (X b)))) :=
    ContMDiff.clm_bundle_apply (b := id) hcov hX
  let D : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    ContMDiffSection.mk (fun b : M => (LeviCivita (I := I) g₁)
      (W : ∀ x : M, TangentSpace I x) b (X b)) hD
  let Ys : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    ContMDiffSection.mk Y hY
  have hpair : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun b : M => ccTensorBilinSymm (I := I) g₀ (T₁ - T₂) b (D b) (Ys b)) :=
    DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck.contMDiff_ccTensorBilinSymm_pairing
      (I := I) g₀ (T₁ - T₂) D Ys
  refine hpair.congr (fun b => ?_)
  rfl

/-- **(A) The metric-difference pairing as a `SmoothCcTensor g₀ 0 2`.** -/
def metricDiffPairingSection (g₀ g₁ g_bg : SmoothRiemannianMetric I M)
    (T₁ T₂ : Integral.L2.SmoothCcTensor g₀ 0 2) :
    Integral.L2.SmoothCcTensor g₀ 0 2 :=
  bilinFormSection (I := I) g₀ (metricDiffPairingBilin (I := I) g₀ g₁ g_bg T₁ T₂)
    (fun hX hY => metricDiffPairingBilin_pairing_contMDiff (I := I) g₀ g₁ g_bg T₁ T₂ hX hY)

set_option linter.unusedSectionVars false in
/-- **(A) The fibre value of the metric-difference pairing section.** -/
theorem metricDiffPairingSection_toModel_apply (g₀ g₁ g_bg : SmoothRiemannianMetric I M)
    (T₁ T₂ : Integral.L2.SmoothCcTensor g₀ 0 2) (x : M) (v w : TangentSpace I x) :
    Tensor0SSpace.toModel
        ((metricDiffPairingSection (I := I) g₀ g₁ g_bg T₁ T₂).toSection x
          (ContinuousMultilinearMap.constOfIsEmpty ℝ
            (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))) ![v, w] =
      metricDiffPairingBilin (I := I) g₀ g₁ g_bg T₁ T₂ x v w := by
  rw [metricDiffPairingSection, bilinFormSection_toModel_apply]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]

/-! #### (B) The connection-difference action -/

/-- **(B) The connection-difference action bilinear form.**  `(v, w) ↦ g₂(connDiff g₁ g₂ x (W₁ x) v,
w)`, `W₁ = deTurckVF g₁ g_bg`.  By `connDiff_apply` this is `g₂(∇^{g₁}_v W₁ − ∇^{g₂}_v W₁, w)`. -/
def connDiffActionBilin (g₁ g₂ g_bg : SmoothRiemannianMetric I M) (x : M) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  (g₂.inner x).comp (connDiff (I := I) g₁ g₂ x (deTurckVF (I := I) g₁ g_bg x))

set_option linter.unusedSectionVars false in
@[simp] theorem connDiffActionBilin_apply (g₁ g₂ g_bg : SmoothRiemannianMetric I M) (x : M)
    (v w : TangentSpace I x) :
    connDiffActionBilin (I := I) g₁ g₂ g_bg x v w =
      g₂.inner x (connDiff (I := I) g₁ g₂ x (deTurckVF (I := I) g₁ g_bg x) v) w := by
  rfl

set_option linter.unusedSectionVars false in
/-- **(B) Smoothness of the connection-difference action on smooth fields.**  The inner field
`x ↦ connDiff g₁ g₂ x (W₁ x) (X x)` is smooth (`connDiff_contMDiff` on the smooth field `W₁` and the
smooth direction `X`), and the `g₂`-inner pairing of two smooth tangent fields is smooth. -/
theorem connDiffActionBilin_pairing_contMDiff (g₁ g₂ g_bg : SmoothRiemannianMetric I M)
    {X Y : Π b : M, TangentSpace I b}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Y)) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun b : M => connDiffActionBilin (I := I) g₁ g₂ g_bg b (X b) (Y b)) := by
  classical
  set W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ := deTurckVF (I := I) g₁ g_bg with hW
  have hWvf : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (W : Π b : M, TangentSpace I b)) := W.contMDiff
  have hinner : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (T% (fun b : M => connDiff (I := I) g₁ g₂ b ((W : Π b : M, TangentSpace I b) b) (X b))) :=
    connDiff_contMDiff (I := I) g₁ g₂ hWvf hX
  let D : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    ContMDiffSection.mk (fun b : M => connDiff (I := I) g₁ g₂ b
      ((W : Π b : M, TangentSpace I b) b) (X b)) hinner
  let Ys : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    ContMDiffSection.mk Y hY
  have hpair : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun b : M => g₂.inner b (D b) (Ys b)) :=
    Integral.DivergenceTheorem.contMDiff_g_inner_of_smooth_sections (I := I) g₂ D Ys
  refine hpair.congr (fun b => ?_)
  rfl

/-- **(B) The connection-difference action as a `SmoothCcTensor g₀ 0 2`.** -/
def connDiffActionSection (g₀ g₁ g₂ g_bg : SmoothRiemannianMetric I M) :
    Integral.L2.SmoothCcTensor g₀ 0 2 :=
  bilinFormSection (I := I) g₀ (connDiffActionBilin (I := I) g₁ g₂ g_bg)
    (fun hX hY => connDiffActionBilin_pairing_contMDiff (I := I) g₁ g₂ g_bg hX hY)

set_option linter.unusedSectionVars false in
/-- **(B) The fibre value of the connection-difference action section.** -/
theorem connDiffActionSection_toModel_apply (g₀ g₁ g₂ g_bg : SmoothRiemannianMetric I M)
    (x : M) (v w : TangentSpace I x) :
    Tensor0SSpace.toModel
        ((connDiffActionSection (I := I) g₀ g₁ g₂ g_bg).toSection x
          (ContinuousMultilinearMap.constOfIsEmpty ℝ
            (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))) ![v, w] =
      connDiffActionBilin (I := I) g₁ g₂ g_bg x v w := by
  rw [connDiffActionSection, bilinFormSection_toModel_apply]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]

/-! #### (C) The field-difference gradient -/

/-- **(C) The field-difference gradient bilinear form.**  `(v, w) ↦ g₂(∇^{g₂}_v (W₁ − W₂), w)`,
`W_k = deTurckVF g_k g_bg` — the `g₂`-lowered Levi-Civita covariant gradient of the *difference*
section `W₁ − W₂`. -/
def fieldDiffGradBilin (g₁ g₂ g_bg : SmoothRiemannianMetric I M) (x : M) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  (g₂.inner x).comp ((LeviCivita (I := I) g₂)
    ((deTurckVF (I := I) g₁ g_bg - deTurckVF (I := I) g₂ g_bg :
      Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) : ∀ x : M, TangentSpace I x) x)

set_option linter.unusedSectionVars false in
@[simp] theorem fieldDiffGradBilin_apply (g₁ g₂ g_bg : SmoothRiemannianMetric I M) (x : M)
    (v w : TangentSpace I x) :
    fieldDiffGradBilin (I := I) g₁ g₂ g_bg x v w =
      g₂.inner x ((LeviCivita (I := I) g₂)
        ((deTurckVF (I := I) g₁ g_bg - deTurckVF (I := I) g₂ g_bg :
          Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) : ∀ x : M, TangentSpace I x) x v) w := by
  rfl

set_option linter.unusedSectionVars false in
/-- **(C) Smoothness of the field-difference gradient on smooth fields.**  The covariant-gradient
field `∇^{g₂}(W₁ − W₂)` of the smooth difference section is smooth
(`LeviCivita_section_contMDiffOn_univ`, then `clm_bundle_apply`); its `g₂`-inner pairing with a smooth
direction frame is smooth. -/
theorem fieldDiffGradBilin_pairing_contMDiff (g₁ g₂ g_bg : SmoothRiemannianMetric I M)
    {X Y : Π b : M, TangentSpace I b}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Y)) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun b : M => fieldDiffGradBilin (I := I) g₁ g₂ g_bg b (X b) (Y b)) := by
  classical
  set W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    deTurckVF (I := I) g₁ g_bg - deTurckVF (I := I) g₂ g_bg with hW
  have hWsmooth : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ((∞ : WithTop ℕ∞) + 1)
      (fun x : M => (⟨x, (W : ∀ x : M, TangentSpace I x) x⟩ : TotalSpace E (TangentSpace I)))
      Set.univ := by
    have h_le : ((∞ : WithTop ℕ∞) + 1) ≤ ∞ := by rw [ENat.coe_top_add_one]
    exact (W.contMDiff.of_le h_le).contMDiffOn
  have hcov : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun x : M =>
        (⟨x, (LeviCivita (I := I) g₂) (W : ∀ x : M, TangentSpace I x) x⟩ :
          TotalSpace (E →L[ℝ] E) (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x))) := by
    rw [← contMDiffOn_univ]
    exact LeviCivita_section_contMDiffOn_univ (I := I) g₂ hWsmooth
  have hD : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M =>
        (TotalSpace.mk' E (E := fun y : M => TangentSpace I y) b
          ((LeviCivita (I := I) g₂) (W : ∀ x : M, TangentSpace I x) b (X b)))) :=
    ContMDiff.clm_bundle_apply (b := id) hcov hX
  let D : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    ContMDiffSection.mk (fun b : M => (LeviCivita (I := I) g₂)
      (W : ∀ x : M, TangentSpace I x) b (X b)) hD
  let Ys : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    ContMDiffSection.mk Y hY
  have hpair : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun b : M => g₂.inner b (D b) (Ys b)) :=
    Integral.DivergenceTheorem.contMDiff_g_inner_of_smooth_sections (I := I) g₂ D Ys
  refine hpair.congr (fun b => ?_)
  rfl

/-- **(C) The field-difference gradient as a `SmoothCcTensor g₀ 0 2`.** -/
def fieldDiffGradSection (g₀ g₁ g₂ g_bg : SmoothRiemannianMetric I M) :
    Integral.L2.SmoothCcTensor g₀ 0 2 :=
  bilinFormSection (I := I) g₀ (fieldDiffGradBilin (I := I) g₁ g₂ g_bg)
    (fun hX hY => fieldDiffGradBilin_pairing_contMDiff (I := I) g₁ g₂ g_bg hX hY)

set_option linter.unusedSectionVars false in
/-- **(C) The fibre value of the field-difference gradient section.** -/
theorem fieldDiffGradSection_toModel_apply (g₀ g₁ g₂ g_bg : SmoothRiemannianMetric I M)
    (x : M) (v w : TangentSpace I x) :
    Tensor0SSpace.toModel
        ((fieldDiffGradSection (I := I) g₀ g₁ g₂ g_bg).toSection x
          (ContinuousMultilinearMap.constOfIsEmpty ℝ
            (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))) ![v, w] =
      fieldDiffGradBilin (I := I) g₁ g₂ g_bg x v w := by
  rw [fieldDiffGradSection, bilinFormSection_toModel_apply]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]

/-! #### The telescope identity -/

set_option linter.unusedSectionVars false in
/-- **The metric-difference realization bridge.**  Under the realization hypotheses `hr1`/`hr2`
(`g_k = g₀ + ccTensorBilinSymm g₀ T_k`), the fibre metric difference `g₁ − g₂` equals
`ccTensorBilinSymm g₀ (T₁ − T₂)` (`ccTensorBilinSymm_sub`). -/
theorem gInner_sub_eq_ccTensorBilinSymm_sub (g₀ g₁ g₂ : SmoothRiemannianMetric I M)
    (T₁ T₂ : Integral.L2.SmoothCcTensor g₀ 0 2)
    (hr1 : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T₁ y v w)
    (hr2 : ∀ (y : M) (v w : TangentSpace I y),
      g₂.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T₂ y v w)
    (x : M) (u w : TangentSpace I x) :
    g₁.inner x u w - g₂.inner x u w = ccTensorBilinSymm (I := I) g₀ (T₁ - T₂) x u w := by
  rw [hr1 x u w, hr2 x u w, ccTensorBilinSymm_sub]
  ring

set_option linter.unusedSectionVars false in
/-- **The bilinear-form telescope (fibre level).**  For realized metrics `g₁ = g₀ + T₁`,
`g₂ = g₀ + T₂` (hypotheses `hr1`/`hr2`) and `W_k = deTurckVF g_k g_bg`:
`g₁(∇^{g₁}_v W₁, w) − g₂(∇^{g₂}_v W₂, w) = (A) + (B) + (C)` (the metric-difference pairing, the
connection-difference action, and the lowered gradient of the difference field).  Finite fibre
algebra over `connDiff_deTurckVF_apply` and `leviCivita_section_sub_apply`: with `a₁ = ∇^{g₁}_v W₁`,
`a₁' = ∇^{g₂}_v W₁`, `a₂ = ∇^{g₂}_v W₂`, the summands are `g₁(a₁) − g₂(a₁)`, `g₂(a₁) − g₂(a₁')`,
`g₂(a₁') − g₂(a₂)`, which telescope to `g₁(a₁) − g₂(a₂)`. -/
theorem loweredCovGradDeTurckVFBilin_sub_eq_telescope
    (g₀ g₁ g₂ g_bg : SmoothRiemannianMetric I M)
    (T₁ T₂ : Integral.L2.SmoothCcTensor g₀ 0 2)
    (hr1 : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T₁ y v w)
    (hr2 : ∀ (y : M) (v w : TangentSpace I y),
      g₂.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T₂ y v w)
    (x : M) (v w : TangentSpace I x) :
    loweredCovGradDeTurckVFBilin (I := I) g₁ g_bg x v w
      - loweredCovGradDeTurckVFBilin (I := I) g₂ g_bg x v w =
      metricDiffPairingBilin (I := I) g₀ g₁ g_bg T₁ T₂ x v w
      + connDiffActionBilin (I := I) g₁ g₂ g_bg x v w
      + fieldDiffGradBilin (I := I) g₁ g₂ g_bg x v w := by
  classical
  rw [loweredCovGradDeTurckVFBilin_apply, loweredCovGradDeTurckVFBilin_apply]
  set a1 := (LeviCivita (I := I) g₁)
    (deTurckVF (I := I) g₁ g_bg : ∀ x : M, TangentSpace I x) x v with ha1
  set a2 := (LeviCivita (I := I) g₂)
    (deTurckVF (I := I) g₂ g_bg : ∀ x : M, TangentSpace I x) x v with ha2
  set a1' := (LeviCivita (I := I) g₂)
    (deTurckVF (I := I) g₁ g_bg : ∀ x : M, TangentSpace I x) x v with ha1'
  -- (A): the realized metric-difference pairing against the endpoint gradient `a1`.
  rw [metricDiffPairingBilin_apply, ← ha1,
    ← gInner_sub_eq_ccTensorBilinSymm_sub (I := I) g₀ g₁ g₂ T₁ T₂ hr1 hr2 x a1 w]
  -- (B): the connection-difference action `g₂(a1 − a1', w)`.
  rw [connDiffActionBilin_apply,
    connDiff_deTurckVF_apply (I := I) g₁ g₂ g_bg x v, ← ha1, ← ha1',
    map_sub, ContinuousLinearMap.sub_apply]
  -- (C): the field-difference gradient `g₂(a1' − a2, w)`.
  rw [fieldDiffGradBilin_apply,
    leviCivita_section_sub_apply (I := I) g₂ (deTurckVF (I := I) g₁ g_bg)
      (deTurckVF (I := I) g₂ g_bg) x v, ← ha1', ← ha2,
    map_sub, ContinuousLinearMap.sub_apply]
  -- Telescope.
  abel

set_option linter.unusedSectionVars false in
/-- **The lowered-covariant-gradient-difference telescope (section level).**  For realized metrics
`g₁ = g₀ + T₁`, `g₂ = g₀ + T₂` (hypotheses `hr1`/`hr2`) and `W_k = deTurckVF g_k g_bg`, the
`g₀`-retag difference of the lowered covariant gradient sections decomposes as the metric-difference
pairing `(A)` plus the connection-difference action `(B)` plus the field-difference gradient `(C)`:
$$
  \mathrm{loweredCovGradDeTurckVFRetagG0}\,g_0\,g_1\,g_{bg}
    - \mathrm{loweredCovGradDeTurckVFRetagG0}\,g_0\,g_2\,g_{bg}
  = \mathrm{metricDiffPairingSection} + \mathrm{connDiffActionSection}
      + \mathrm{fieldDiffGradSection}.
$$
Proved by unit-`(0,0)`-evaluation fibre extensionality (the keystone `ext` technique of
`VectorFieldCovariantGradientSection.lean`) through the bilinear telescope
`loweredCovGradDeTurckVFBilin_sub_eq_telescope`. -/
theorem loweredCovGradDeTurckVF_sub_eq_telescope
    (g₀ g₁ g₂ g_bg : SmoothRiemannianMetric I M)
    (T₁ T₂ : Integral.L2.SmoothCcTensor g₀ 0 2)
    (hr1 : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T₁ y v w)
    (hr2 : ∀ (y : M) (v w : TangentSpace I y),
      g₂.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T₂ y v w) :
    loweredCovGradDeTurckVFRetagG0 (I := I) g₀ g₁ g_bg
        - loweredCovGradDeTurckVFRetagG0 (I := I) g₀ g₂ g_bg =
      metricDiffPairingSection (I := I) g₀ g₁ g_bg T₁ T₂
      + connDiffActionSection (I := I) g₀ g₁ g₂ g_bg
      + fieldDiffGradSection (I := I) g₀ g₁ g₂ g_bg := by
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
  -- Split the LHS difference through `toSection_sub` and the unit evaluation.
  have hLHS : Tensor0SSpace.toModel
      ((loweredCovGradDeTurckVFRetagG0 (I := I) g₀ g₁ g_bg
          - loweredCovGradDeTurckVFRetagG0 (I := I) g₀ g₂ g_bg).toSection x
        (ContinuousMultilinearMap.constOfIsEmpty ℝ
          (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))) v =
      loweredCovGradDeTurckVFBilin (I := I) g₁ g_bg x (v 0) (v 1)
      - loweredCovGradDeTurckVFBilin (I := I) g₂ g_bg x (v 0) (v 1) := by
    rw [Integral.L2.SmoothCcTensor.toSection_sub]
    rw [ContMDiffSection.coe_sub, Pi.sub_apply, ContinuousLinearMap.sub_apply,
      Tensor0SSpace.toModel_sub, ContinuousMultilinearMap.sub_apply]
    rw [show v = (![v 0, v 1] : Fin 2 → TangentSpace I x) from by
      funext i; fin_cases i <;> rfl]
    rw [loweredCovGradDeTurckVFRetagG0_unitModel_eq, loweredCovGradDeTurckVFRetagG0_unitModel_eq]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  -- Split the RHS sum through `toSection_add` and the three section value lemmas.
  have hRHS : Tensor0SSpace.toModel
      ((metricDiffPairingSection (I := I) g₀ g₁ g_bg T₁ T₂
          + connDiffActionSection (I := I) g₀ g₁ g₂ g_bg
          + fieldDiffGradSection (I := I) g₀ g₁ g₂ g_bg).toSection x
        (ContinuousMultilinearMap.constOfIsEmpty ℝ
          (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))) v =
      metricDiffPairingBilin (I := I) g₀ g₁ g_bg T₁ T₂ x (v 0) (v 1)
      + connDiffActionBilin (I := I) g₁ g₂ g_bg x (v 0) (v 1)
      + fieldDiffGradBilin (I := I) g₁ g₂ g_bg x (v 0) (v 1) := by
    rw [Integral.L2.SmoothCcTensor.toSection_add, Integral.L2.SmoothCcTensor.toSection_add]
    rw [ContMDiffSection.coe_add, Pi.add_apply, ContinuousLinearMap.add_apply,
      ContMDiffSection.coe_add, Pi.add_apply, ContinuousLinearMap.add_apply,
      Tensor0SSpace.toModel_add, ContinuousMultilinearMap.add_apply,
      Tensor0SSpace.toModel_add, ContinuousMultilinearMap.add_apply]
    rw [show v = (![v 0, v 1] : Fin 2 → TangentSpace I x) from by
      funext i; fin_cases i <;> rfl]
    rw [metricDiffPairingSection_toModel_apply, connDiffActionSection_toModel_apply,
      fieldDiffGradSection_toModel_apply]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [hLHS, hRHS]
  exact loweredCovGradDeTurckVFBilin_sub_eq_telescope (I := I) g₀ g₁ g₂ g_bg T₁ T₂ hr1 hr2 x
    (v 0) (v 1)

end Telescope

end Pullback
end RicciFlow
end PDE
end DifferentialGeometry

end
