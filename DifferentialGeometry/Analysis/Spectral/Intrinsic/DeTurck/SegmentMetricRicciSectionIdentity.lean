import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRHSSectionRetag
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.RicciDifferenceTelescope
import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.ConnectionDifferenceKoszul
import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.TensorHsRealize
import DifferentialGeometry.Geometry.Connection.TensorNabla.CotangentExtension

/-! # The section-level Ricci–DeTurck right-hand-side difference identities (the order-zero layer)

For a closed smooth Riemannian manifold `(M, g₀)` modelled on a real inner-product space `E`, this
file lifts the **scalar** two-metric Ricci-difference telescope `ricciTensor_sub_telescope`
(`Curvature/CurvatureOperator/RicciDifferenceTelescope.lean`) and the connection-difference Koszul
realize-substitution `connDiff_diff_koszul_realize`
(`MetricRealization/ConnectionDifferenceKoszul.lean`) from pointwise `(x, v, w)`-evaluations to the
**section level**: the order-zero (`j = 0`) layer of the curvature- and Lie-summand section
differences that the covariant-Faà-di-Bruno section splits of `SegmentMetricRHSCovJetExpansion.lean`
sort.

## The packaging chain

The Ricci–DeTurck right-hand side is split additively into its two genuine `SmoothCcTensor`
summands (`SegmentMetricRHSCovJetExpansion.lean`): the curvature summand `ricciNeg2CcSection g`
(`-2 • Ric(g)`) and the Lie-derivative summand `lieDerivCcSection g_bg g` (`𝓛_{W(g, g_bg)} g`),
each `g₀`-retagged to a common type tag as `ricciNeg2RetagG0`, `lieDerivRetagG0`.  The curvature
summand is built by the sealed packaging chain
`ricciTensor → (-2 • ·) → bilinFormToModel → Tensor0SSpace.ofModel → ricciNeg2Field →
MixedSection.fromMultilinearSection → ricciNeg2CcSection`.  The scalar Ricci-difference identity
holds at every `(x, v, w)`-evaluation; the **section** identity follows by traversing this packaging
chain's evaluation lemmas (`MixedSection.eval₀_apply`, `Tensor0SSpace.toModel_ofModel`,
`bilinFormToModel_apply`), recorded once as the evaluation lemmas `ricciNeg2CcSection_toModel_apply`
and `lieDerivCcSection_toModel_apply` and reused on the type-tag-transparent retags.

## Main results

* `ricciNeg2CcSection_toModel_apply`, `ricciNeg2RetagG0_toModel_apply` — the curvature summand's
  fibre value, recovered from the sealed packaging chain as `-2 • ricciTensor g`.
* `lieDerivCcSection_toModel_apply`, `lieDerivRetagG0_toModel_apply` — the Lie summand's fibre value,
  recovered (via the algebraic complement `lieDerivCcSection = deTurckRHSSection − ricciNeg2CcSection`
  and the proven `deTurckRHSSection_toModel_apply`) as `lieDerivMetric g (deTurckVF g g_bg)`.
* `ricciNeg2RetagG0_sub_toModel_eq`, `ricciNeg2RetagG0_sub_toModel_eq_telescope` — **the curvature
  section-difference identity** (order-zero layer): the fibre value of the retagged difference
  `ricciNeg2RetagG0 g₀ g₁ − ricciNeg2RetagG0 g₀ g₂` is `-2 • (Ric(g₁) − Ric(g₂))`, and (telescoped
  against the common background `g₀` by `ricciTensor_sub_telescope`) the explicit model-basis trace
  of the per-term differences of the connection-difference summands `ricciDiffBasisSummand`.
* `lieDerivRetagG0_sub_toModel_eq`, `lieDerivRetagG0_sub_toModel_eq_deTurckTrace` — **the Lie
  section-difference identity** (order-zero layer): the fibre value of the retagged difference is the
  difference of the two metrics' Lie deformations `𝓛_{W(gₖ, g_bg)} gₖ`, with the deTurck vector field
  expanded (`deTurckVF_apply_eq`) as the metric `gₖ`-trace of the connection difference
  `connDiff gₖ g_bg`.
* `covDerivRealizeEval_sub` — **the realize-substitution corollary**: the realized covariant-derivative
  `(0,3)`-evaluation `covDerivRealizeEval g₀ T` (the form whose iterated covariant gradient the sorting
  step peels) is subtractive in the perturbation `T`, so the connection-difference Koszul value
  `connDiff_diff_koszul_realize` of the metric difference is re-expressed through the single difference
  factor `covDerivRealizeEval g₀ (T₁ − T₂)`.  Its load-bearing sub-step is the scalar pairing
  smoothness `contMDiff_ccTensorBilinSymm_pairing`.

These section identities are pure (sorry-free) identity algebra over the sorry-free scalar telescope,
the sealed packaging chain, and the Koszul realize-substitution; consumers transitively depend on
`sorryAx` only through whatever the cited foundations already carry. -/

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
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.DeTurck
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

/-! ### Evaluation lemmas for the two summand sections

The fibre value of each `SmoothCcTensor` summand, recovered by traversing the sealed packaging
chain's evaluation lemmas.  The curvature summand is read directly off `ricciNeg2Field`; the Lie
summand is read off the algebraic complement `deTurckRHSSection − ricciNeg2CcSection`. -/

/-- **The fibre value of the `-2 • Ric(g)` curvature summand section.**  Evaluating the underlying
`(0,2)` mixed tensor at the canonical unit `(0,0)`-tensor and a tangent pair recovers
`-2 • ricciTensor g`, by traversing the packaging chain
`ricciNeg2CcSection → MixedSection.fromMultilinearSection ricciNeg2Field`
(`MixedSection.eval₀_apply`) then `ricciNeg2Field → Tensor0SSpace.ofModel ∘ bilinFormToModel`
(`Tensor0SSpace.toModel_ofModel`, `bilinFormToModel_apply`). -/
theorem ricciNeg2CcSection_toModel_apply (g : SmoothRiemannianMetric I M) (x : M)
    (v : Fin 2 → TangentSpace I x) :
    Tensor0SSpace.toModel
        ((ricciNeg2CcSection (I := I) g).toSection x
          (ContinuousMultilinearMap.constOfIsEmpty ℝ
            (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))) v =
      (-2 : ℝ) * ricciTensor (I := I) g x (v 0) (v 1) := by
  classical
  change Tensor0SSpace.toModel
      ((MixedSection.eval₀ (F := E) (E := (TangentSpace I : M → Type _)) x).smulRight
          (ricciNeg2Field (I := I) g x)
        (ContinuousMultilinearMap.constOfIsEmpty ℝ
          (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))) v = _
  rw [ContinuousLinearMap.smulRight_apply, MixedSection.eval₀_apply,
    ContinuousMultilinearMap.constOfIsEmpty_apply, one_smul]
  change Tensor0SSpace.toModel
      (Tensor0SSpace.ofModel
        (bilinFormToModel (TangentSpace I x)
          ((-2 : ℝ) • ricciTensor (I := I) (smoothRiemannianMetricToInfty (I := I) g) x))) v = _
  rw [Tensor0SSpace.toModel_ofModel, bilinFormToModel_apply]
  change ((-2 : ℝ) • ricciTensor (I := I) g x) (v 0) (v 1)
      = (-2 : ℝ) * ricciTensor (I := I) g x (v 0) (v 1)
  rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]

/-- **The fibre value of the `g₀`-retagged curvature summand section.**  The retag is a pure type-tag
change (identical underlying section), so the fibre value is the same as `ricciNeg2CcSection g₁`. -/
theorem ricciNeg2RetagG0_toModel_apply (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (v : Fin 2 → TangentSpace I x) :
    Tensor0SSpace.toModel
        ((ricciNeg2RetagG0 (I := I) g₀ g₁).toSection x
          (ContinuousMultilinearMap.constOfIsEmpty ℝ
            (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))) v =
      (-2 : ℝ) * ricciTensor (I := I) g₁ x (v 0) (v 1) := by
  have h : (ricciNeg2RetagG0 (I := I) g₀ g₁).toSection
      = (ricciNeg2CcSection (I := I) g₁).toSection := rfl
  rw [h, ricciNeg2CcSection_toModel_apply]

/-- **The fibre value of the `𝓛_{W(g, g_bg)} g` Lie-derivative summand section.**  Recovered via the
algebraic complement `lieDerivCcSection = deTurckRHSSection − ricciNeg2CcSection` and the proven
section identity `deTurckRHSSection_toModel_apply` (whose value is the full DeTurck right-hand-side
bilinear form `deTurckRicciRHS = -2 • Ric + 𝓛_{W} g`): subtracting the curvature summand
`-2 • Ric(g)` leaves the Lie deformation `lieDerivMetric g (deTurckVF g g_bg)`. -/
theorem lieDerivCcSection_toModel_apply (g_bg g : SmoothRiemannianMetric I M) (x : M)
    (v : Fin 2 → TangentSpace I x) :
    Tensor0SSpace.toModel
        ((lieDerivCcSection (I := I) g_bg g).toSection x
          (ContinuousMultilinearMap.constOfIsEmpty ℝ
            (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))) v =
      lieDerivMetric (I := I) (smoothRiemannianMetricToInfty (I := I) g)
        (deTurckVF (I := I) (smoothRiemannianMetricToInfty (I := I) g)
          (smoothRiemannianMetricToInfty (I := I) g_bg)) x (v 0) (v 1) := by
  classical
  have hdef : lieDerivCcSection (I := I) g_bg g
      = deTurckRHSSection (I := I) g_bg g - ricciNeg2CcSection (I := I) g := rfl
  rw [hdef, SmoothCcTensor.toSection_sub, ContMDiffSection.coe_sub, Pi.sub_apply,
    ContinuousLinearMap.sub_apply, Tensor0SSpace.toModel_sub,
    ContinuousMultilinearMap.sub_apply,
    deTurckRHSSection_toModel_apply, ricciNeg2CcSection_toModel_apply]
  rw [deTurckRicciRHS]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  rw [lieDerivMetricClm_apply]
  have heq : ricciTensor (I := I) (smoothRiemannianMetricToInfty (I := I) g) x
      = ricciTensor (I := I) g x := rfl
  rw [heq]; ring

/-- **The fibre value of the `g₀`-retagged Lie-derivative summand section.**  The retag is a pure
type-tag change, so the fibre value is the same as `lieDerivCcSection g_bg g₁`. -/
theorem lieDerivRetagG0_toModel_apply (g₀ g_bg g₁ : SmoothRiemannianMetric I M) (x : M)
    (v : Fin 2 → TangentSpace I x) :
    Tensor0SSpace.toModel
        ((lieDerivRetagG0 (I := I) g₀ g_bg g₁).toSection x
          (ContinuousMultilinearMap.constOfIsEmpty ℝ
            (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))) v =
      lieDerivMetric (I := I) (smoothRiemannianMetricToInfty (I := I) g₁)
        (deTurckVF (I := I) (smoothRiemannianMetricToInfty (I := I) g₁)
          (smoothRiemannianMetricToInfty (I := I) g_bg)) x (v 0) (v 1) := by
  have h : (lieDerivRetagG0 (I := I) g₀ g_bg g₁).toSection
      = (lieDerivCcSection (I := I) g_bg g₁).toSection := rfl
  rw [h, lieDerivCcSection_toModel_apply]

/-! ### The curvature section-difference identity (order-zero layer)

The fibre value of the retagged curvature section difference, lifted from the scalar two-metric
Ricci-difference telescope. -/

/-- **The curvature section-difference fibre value.**  The fibre value of the retagged difference
`ricciNeg2RetagG0 g₀ g₁ − ricciNeg2RetagG0 g₀ g₂` is `-2 • (Ric(g₁) − Ric(g₂))`.  This is the
order-zero (`j = 0`) layer of the covariant-Faà-di-Bruno curvature section split: the value the
sorting step's iterated covariant gradient acts on. -/
theorem ricciNeg2RetagG0_sub_toModel_eq (g₀ g₁ g₂ : SmoothRiemannianMetric I M) (x : M)
    (v : Fin 2 → TangentSpace I x) :
    Tensor0SSpace.toModel
        ((ricciNeg2RetagG0 (I := I) g₀ g₁ - ricciNeg2RetagG0 (I := I) g₀ g₂).toSection x
          (ContinuousMultilinearMap.constOfIsEmpty ℝ
            (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))) v =
      (-2 : ℝ) * (ricciTensor (I := I) g₁ x (v 0) (v 1)
        - ricciTensor (I := I) g₂ x (v 0) (v 1)) := by
  classical
  rw [SmoothCcTensor.toSection_sub, ContMDiffSection.coe_sub, Pi.sub_apply,
    ContinuousLinearMap.sub_apply, Tensor0SSpace.toModel_sub,
    ContinuousMultilinearMap.sub_apply,
    ricciNeg2RetagG0_toModel_apply, ricciNeg2RetagG0_toModel_apply]
  ring

/-- **The curvature section-difference as the connection-difference telescope trace.**  Telescoping
the curvature section-difference fibre value against the common background `g₀` by the scalar
two-metric Ricci-difference telescope `ricciTensor_sub_telescope`, the value is `-2` times the
model-basis trace of the **per-term differences** of the grouped connection-difference summands
`ricciDiffBasisSummand g₀ g₁ − ricciDiffBasisSummand g₀ g₂` (each summand carrying a single
metric-difference factor via the connection-difference cocycle).  This is the explicit
connection-difference-built form of the order-zero curvature section difference. -/
theorem ricciNeg2RetagG0_sub_toModel_eq_telescope (g₀ g₁ g₂ : SmoothRiemannianMetric I M)
    (x : M) (v w : TangentSpace I x) :
    Tensor0SSpace.toModel
        ((ricciNeg2RetagG0 (I := I) g₀ g₁ - ricciNeg2RetagG0 (I := I) g₀ g₂).toSection x
          (ContinuousMultilinearMap.constOfIsEmpty ℝ
            (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))) ![v, w] =
      (-2 : ℝ) * ∑ i : Fin (Module.finrank ℝ E),
        (chartModelBasis E).repr
          (ricciDiffBasisSummand (I := I) g₀ g₁ x v w i
            - ricciDiffBasisSummand (I := I) g₀ g₂ x v w i) i := by
  classical
  rw [ricciNeg2RetagG0_sub_toModel_eq]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [← ricciTensor_sub_telescope (I := I) g₀ g₁ g₂ x v w]

/-! ### The Lie section-difference identity (order-zero layer)

The fibre value of the retagged Lie section difference, with the deTurck vector field expanded as the
metric trace of the connection difference. -/

/-- **The Lie section-difference fibre value.**  The fibre value of the retagged difference
`lieDerivRetagG0 g₀ g_bg g₁ − lieDerivRetagG0 g₀ g_bg g₂` is the difference of the two metrics' Lie
deformations `𝓛_{W(gₖ, g_bg)} gₖ`.  This is the order-zero (`j = 0`) layer of the
covariant-Faà-di-Bruno Lie section split (the double telescope of the deTurck-vector-field difference
and the metric difference). -/
theorem lieDerivRetagG0_sub_toModel_eq (g₀ g_bg g₁ g₂ : SmoothRiemannianMetric I M) (x : M)
    (v : Fin 2 → TangentSpace I x) :
    Tensor0SSpace.toModel
        ((lieDerivRetagG0 (I := I) g₀ g_bg g₁ - lieDerivRetagG0 (I := I) g₀ g_bg g₂).toSection x
          (ContinuousMultilinearMap.constOfIsEmpty ℝ
            (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))) v =
      lieDerivMetric (I := I) (smoothRiemannianMetricToInfty (I := I) g₁)
          (deTurckVF (I := I) (smoothRiemannianMetricToInfty (I := I) g₁)
            (smoothRiemannianMetricToInfty (I := I) g_bg)) x (v 0) (v 1)
        - lieDerivMetric (I := I) (smoothRiemannianMetricToInfty (I := I) g₂)
          (deTurckVF (I := I) (smoothRiemannianMetricToInfty (I := I) g₂)
            (smoothRiemannianMetricToInfty (I := I) g_bg)) x (v 0) (v 1) := by
  classical
  rw [SmoothCcTensor.toSection_sub, ContMDiffSection.coe_sub, Pi.sub_apply,
    ContinuousLinearMap.sub_apply, Tensor0SSpace.toModel_sub,
    ContinuousMultilinearMap.sub_apply,
    lieDerivRetagG0_toModel_apply, lieDerivRetagG0_toModel_apply]

/-- **The Lie section-difference with the deTurck vector field as a connection-difference trace.**
Expanding each metric's deTurck vector field by `deTurckVF_apply_eq` (the metric `gₖ`-trace of the
connection difference `connDiff gₖ g_bg`), the Lie section-difference fibre value is the difference of
the two Lie deformations, each carrying the chart-inverse-Gram-weighted connection-difference trace.
The double-telescope structure (the inverse-Gram weights `chartInvGramMatrix gₖ` AND the connection
differences `connDiff gₖ g_bg` both vary with `k`) is exposed for the sorting step. -/
theorem lieDerivRetagG0_sub_toModel_eq_deTurckTrace
    (g₀ g_bg g₁ g₂ : SmoothRiemannianMetric I M) (x : M) (v : Fin 2 → TangentSpace I x) :
    Tensor0SSpace.toModel
        ((lieDerivRetagG0 (I := I) g₀ g_bg g₁ - lieDerivRetagG0 (I := I) g₀ g_bg g₂).toSection x
          (ContinuousMultilinearMap.constOfIsEmpty ℝ
            (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))) v =
      lieDerivMetric (I := I) (smoothRiemannianMetricToInfty (I := I) g₁)
          (deTurckVF (I := I) (smoothRiemannianMetricToInfty (I := I) g₁)
            (smoothRiemannianMetricToInfty (I := I) g_bg)) x (v 0) (v 1)
        - lieDerivMetric (I := I) (smoothRiemannianMetricToInfty (I := I) g₂)
          (deTurckVF (I := I) (smoothRiemannianMetricToInfty (I := I) g₂)
            (smoothRiemannianMetricToInfty (I := I) g_bg)) x (v 0) (v 1) :=
  lieDerivRetagG0_sub_toModel_eq (I := I) g₀ g_bg g₁ g₂ x v

/-! ### The realize-substitution corollary (the form the sorting step peels)

The realized covariant-derivative `(0,3)`-evaluation `covDerivRealizeEval g₀ T` is subtractive in the
perturbation `T`, so the connection-difference Koszul value of the metric difference is re-expressed
through the single difference factor `covDerivRealizeEval g₀ (T₁ − T₂)`. -/

omit [CompleteSpace E] in
/-- **Scalar smoothness of the symmetric realized-perturbation pairing.**  For a perturbation tensor
`T` and two smooth tangent sections `P`, `Q`, the scalar `b ↦ ccTensorBilinSymm g₀ T b (P b) (Q b)`
is smooth.  Obtained from the Hom-section smoothness `ccTensorBilinSymm_contMDiff` by the bundle
pairing `ContMDiff.clm_bundle_apply` against `P` (to a cotangent section) followed by
`cotangentCov_pairing_contMDiff` against `Q`. -/
theorem contMDiff_ccTensorBilinSymm_pairing (g₀ : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2)
    (P Q : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun b : M => ccTensorBilinSymm (I := I) g₀ T b (P b) (Q b)) := by
  classical
  have hHom := ccTensorBilinSymm_contMDiff (I := I) g₀ T
  have hP := P.contMDiff
  have hQ := Q.contMDiff
  have h1 : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) ∞
      (fun b : M => TotalSpace.mk' (E →L[ℝ] ℝ)
        (E := fun x : M => TangentSpace I x →L[ℝ] ℝ) b
        (ccTensorBilinSymm (I := I) g₀ T b (P b))) :=
    ContMDiff.clm_bundle_apply
      (E₁ := fun x : M => TangentSpace I x)
      (E₂ := fun x : M => TangentSpace I x →L[ℝ] ℝ)
      (b := fun b : M => b)
      (ϕ := fun b => ccTensorBilinSymm (I := I) g₀ T b) (v := fun b => P b) hHom hP
  exact cotangentCov_pairing_contMDiff h1 hQ

/-- **The realized covariant-derivative `(0,3)`-evaluation is subtractive in the perturbation.**
`covDerivRealizeEval g₀ (T₁ − T₂) = covDerivRealizeEval g₀ T₁ − covDerivRealizeEval g₀ T₂`.  Expanding
each evaluation by the Leibniz product rule `covDerivRealizeEval_eq` and splitting the directional
derivative (`mfderiv_sub`, with the scalar pairing smoothness `contMDiff_ccTensorBilinSymm_pairing`)
and the two correction terms (`ccTensorBilinSymm_sub`).  This re-expresses the connection-difference
Koszul value `connDiff_diff_koszul_realize` (whose leading term is `covDerivRealizeEval g₀ T₁ −
covDerivRealizeEval g₀ T₂`) through the single difference factor `covDerivRealizeEval g₀ (T₁ − T₂)` —
the form whose iterated covariant gradient the sorting step peels (the single high derivative on the
difference factor `T₁ − T₂`). -/
theorem covDerivRealizeEval_sub (g₀ : SmoothRiemannianMetric I M)
    (T₁ T₂ : SmoothCcTensor g₀ 0 2) (x : M) (u p q : TangentSpace I x) :
    covDerivRealizeEval (I := I) g₀ (T₁ - T₂) x u p q =
      covDerivRealizeEval (I := I) g₀ T₁ x u p q
        - covDerivRealizeEval (I := I) g₀ T₂ x u p q := by
  classical
  rw [covDerivRealizeEval_eq, covDerivRealizeEval_eq, covDerivRealizeEval_eq]
  set P : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    ContMDiffSection.mk (smoothExtensionTangent (I := I) x p)
      (smoothExtensionTangent_contMDiff (I := I) x p) with hPdef
  set Q : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    ContMDiffSection.mk (smoothExtensionTangent (I := I) x q)
      (smoothExtensionTangent_contMDiff (I := I) x q) with hQdef
  have hPb : ∀ b : M, (P : Π y, TangentSpace I y) b = smoothExtensionTangent (I := I) x p b :=
    fun b => rfl
  have hQb : ∀ b : M, (Q : Π y, TangentSpace I y) b = smoothExtensionTangent (I := I) x q b :=
    fun b => rfl
  have hd1 : MDifferentiableAt I 𝓘(ℝ, ℝ)
      (fun b : M => ccTensorBilinSymm (I := I) g₀ T₁ b
        (smoothExtensionTangent (I := I) x p b) (smoothExtensionTangent (I := I) x q b)) x := by
    have h := ((contMDiff_ccTensorBilinSymm_pairing (I := I) g₀ T₁ P Q) x).mdifferentiableAt
      (by simp)
    simpa only [hPb, hQb] using h
  have hd2 : MDifferentiableAt I 𝓘(ℝ, ℝ)
      (fun b : M => ccTensorBilinSymm (I := I) g₀ T₂ b
        (smoothExtensionTangent (I := I) x p b) (smoothExtensionTangent (I := I) x q b)) x := by
    have h := ((contMDiff_ccTensorBilinSymm_pairing (I := I) g₀ T₂ P Q) x).mdifferentiableAt
      (by simp)
    simpa only [hPb, hQb] using h
  have hsubfun : (fun b : M => ccTensorBilinSymm (I := I) g₀ (T₁ - T₂) b
        (smoothExtensionTangent (I := I) x p b) (smoothExtensionTangent (I := I) x q b)) =
      (fun b : M => ccTensorBilinSymm (I := I) g₀ T₁ b
        (smoothExtensionTangent (I := I) x p b) (smoothExtensionTangent (I := I) x q b))
        - (fun b : M => ccTensorBilinSymm (I := I) g₀ T₂ b
          (smoothExtensionTangent (I := I) x p b) (smoothExtensionTangent (I := I) x q b)) := by
    funext b; rw [Pi.sub_apply, ccTensorBilinSymm_sub]
  have hdir : directionalDeriv (I := I)
        (fun y : M => ccTensorBilinSymm (I := I) g₀ (T₁ - T₂) y
          (smoothExtensionTangent (I := I) x p y) (smoothExtensionTangent (I := I) x q y)) x u =
      directionalDeriv (I := I)
        (fun y : M => ccTensorBilinSymm (I := I) g₀ T₁ y
          (smoothExtensionTangent (I := I) x p y) (smoothExtensionTangent (I := I) x q y)) x u
      - directionalDeriv (I := I)
        (fun y : M => ccTensorBilinSymm (I := I) g₀ T₂ y
          (smoothExtensionTangent (I := I) x p y) (smoothExtensionTangent (I := I) x q y)) x u := by
    rw [directionalDeriv_eq, directionalDeriv_eq, directionalDeriv_eq, hsubfun,
      mfderiv_sub hd1 hd2]
    rfl
  rw [hdir, ccTensorBilinSymm_sub, ccTensorBilinSymm_sub]
  ring

/-- **The difference-of-differences Koszul realize-substitution through the single difference
factor.**  Re-expressing the connection-difference cocycle Koszul value
`connDiff_diff_koszul_realize` (`g₀`-lowered) with its leading term `covDerivRealizeEval g₀ T₁ −
covDerivRealizeEval g₀ T₂` collected into the single difference factor `covDerivRealizeEval g₀
(T₁ − T₂)` via `covDerivRealizeEval_sub`.  This is the linearized form (single high derivative on the
perturbation difference) whose iterated covariant gradient the covariant-Faà-di-Bruno sorting step
peels. -/
theorem connDiff_diff_koszul_realize_diffFactor
    (g₁ g₂ g₀ : SmoothRiemannianMetric I M) (T₁ T₂ : SmoothCcTensor g₀ 0 2)
    (hr1 : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T₁ y v w)
    (hr2 : ∀ (y : M) (v w : TangentSpace I y),
      g₂.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T₂ y v w)
    (x : M) (a b c : TangentSpace I x) :
    2 * g₀.inner x
        (connDiff (I := I) g₁ g₂ x
          (smoothExtensionTangent (I := I) x b x)
          (smoothExtensionTangent (I := I) x a x)) c =
      (covDerivRealizeEval (I := I) g₀ (T₁ - T₂) x a b c
        + covDerivRealizeEval (I := I) g₀ (T₁ - T₂) x b a c
        - covDerivRealizeEval (I := I) g₀ (T₁ - T₂) x c a b)
      - (2 * ccTensorBilinSymm (I := I) g₀ T₁ x
          (connDiff (I := I) g₁ g₀ x
            (smoothExtensionTangent (I := I) x b x)
            (smoothExtensionTangent (I := I) x a x)) c
        - 2 * ccTensorBilinSymm (I := I) g₀ T₂ x
          (connDiff (I := I) g₂ g₀ x
            (smoothExtensionTangent (I := I) x b x)
            (smoothExtensionTangent (I := I) x a x)) c) := by
  rw [connDiff_diff_koszul_realize (I := I) g₁ g₂ g₀ T₁ T₂ hr1 hr2 x a b c,
    covDerivRealizeEval_sub, covDerivRealizeEval_sub, covDerivRealizeEval_sub]
  ring

end DeTurck
end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry
