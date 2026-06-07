import DifferentialGeometry.Geometry.Connection.TensorNabla.TensorSlotwiseCurvatureRS
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.MovingFrameCurvatureTraceSmooth
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.MovingFrameGenuineFieldPairing
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.FiberNormSubadditivity
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.RankRDiffBilinGrid
import DifferentialGeometry.Analysis.Integration.L2.Pairing.Algebra
import DifferentialGeometry.Analysis.Integration.L2.SmoothSections.Integrability
import DifferentialGeometry.Analysis.Sobolev.Embedding.SobolevEmbeddingCm

/-!
# The genuine moving-frame third-order field decomposition at contravariant rank `r`

For a closed (compact, boundaryless) smooth Riemannian manifold `(M, g)` this file is the
contravariant-rank-`r` lift of the genuine moving-frame third-order Bochner–Weitzenböck field
decomposition (`MovingFrameGenuineFieldPairing`, `MovingFrameCurvatureTraceSmooth`,
`MovingFrameGenuineSectionOrderDivergence`) of the rank-generic order-`2` rough-Laplacian /
covariant-gradient commutator defect

```
Curv S := Δ_∇(∇S) − ∇(Δ_∇ S)
```

(`pointwiseTensorCurvRS g r s S`, a `(r, s + 1)`-tensor field; `∇S = covGrad g r s S`).

The `(0, s)` apparatus is *already rank-generic in everything except the literal contravariant index
`0`*: the bundled curvature operator `riemannOp (tensorCov g r s)`, the curvature section
`riemannSec`, the directional covariant derivative `covApply`, their smoothness lemmas
(`riemannSec_contMDiff`, `riemannOp_apply_smooth`, `covApplyRS_contMDiff`), the covariant-gradient
bundle equivalence `covGradBundleEquiv r s` / `covGradBundleSmoothEquiv r s`, and the operator-to-bundle
smoothness bridge `cotangentCov_clmSection_smooth_aux` all take a generic bundle/connection. The
`ContMDiffCovariantDerivative` instance for `tensorCov g r s` (the abbrev
`tensorRSCovariantDerivative I M r s (LeviCivita g)`) holds at every rank by `TensorRSNabla`. Hence the
**concrete pure-Riemann genuine section** and its smoothness/frame-independence port verbatim by
replacing `0` with `r` and the `(0, s)`-fibre scalarization `T ↦ toModel (T (unit)) m` with the
generic `(r, s)`-fibre scalarization `T ↦ toModel (T D) m` over an arbitrary
`D : Tensor0SSpace r I y` (`TensorRSSpace r s I y = Tensor0SSpace r I y →L[ℝ] Tensor0SSpace s I y`).

The frame-independence of the pure-Riemann genuine metric trace (the frame index is contracted twice —
in slot-`0` of the Riemann operator and as the covariant-gradient direction) is purely the bilinear
Parseval fact `orthonormal_basis_bilin_trace` (target `ℝ`), so it ports unchanged.

The genuinely-deep moving-frame curvature-endomorphism content — the differentiated-curvature and
moving-frame remainder fields, their order-separated fibre bounds, the integrated nullity, and the
proportional `rfns(∇S)`-bound on the pure-Riemann section — is, at general contravariant rank `r`,
absent from the library (the rank-`0` proportional curvature sups
`riemannianFiberNormSq_riemannOp_covGrad_uniform_proportional_bound`,
`exists_uniform_riemannianFiberNormSq_covGrad_riemannOp_bound`, and the deepest tri-split
`exists_pointwiseTensorCurv_genuineTriSplit_divergence` are stated only at contravariant rank `0`). It
is collected here as **one** deepest curvature primitive at `(r, s)`,
`exists_pointwiseTensorCurvRS_genuineTriSplit_divergence`, in its **sound integrated form** (the
pointwise pairing is non-zero — it carries the non-divergence Bochner content — so only the global `L²`
pairing vanishes), exactly mirroring the rank-`0` deepest node, with the proportional pure-Riemann
section bound folded in (it too needs the absent rank-`r` proportional sup).

## Main definitions

* `pointwiseTensorCurvRS g r s S` — the rank-`r` order-`2` commutator defect, definitionally
  `Δ_∇(∇S) − ∇(Δ_∇ S)`.
* `GcurvSectionRS g r s S : SmoothCcTensor g r (s + 1)` — the concrete pure-Riemann genuine curvature
  section (the slot-`0` assembly of the *tensorial* moving-frame trace `∑ᵢ R(Bᵢ, ·)(∇_{Bᵢ} S)`), with
  base-point smoothness proved by the frame-independence freeze of the pure-Riemann metric trace
  (sorry-free). The general-`B` companion is `fixedFramePureRSectionRS`.

## Main results

* `genuineCurvTraceFixedFramePureRRS_contMDiff` — smoothness of the fixed-frame pure-Riemann genuine
  trace.
* `genuineCurvPureRFibRS_contMDiff` — base-point smoothness of the moving-centre pure-Riemann fibre
  field (the frame-independence freeze, sorry-free).
* `exists_pointwiseTensorCurvRS_movingFrameField_orderSeparated_bracketFreePairing` — the rank-`r`
  analogue of `exists_pointwiseTensorCurv_movingFrameField_orderSeparated_bracketFreePairing`: the two
  genuine curvature fields with their three order-separated fibre bounds and the bracket-free `L²`
  pairing, proved over the concrete pure-Riemann section and the deepest tri-split primitive.

## Convention

Geometer convention `Δ_∇ = ∑ᵢ ∇²_{Bᵢ, Bᵢ}` (frame trace). All fibre norms are the intrinsic
Riemannian fibre norm `riemannianFiberNormSq`. The moving frame is `Bᵢ := smoothOrthoFrame g x i`
(centre = the evaluation point), exactly as `rawTensorConnLapSmooth` is.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.PDE.RicciFlow

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

/-- **The rank-`r` order-`2` commutator defect.** The difference of the rough Laplacian of the
`(r, s + 1)`-tensor gradient field `∇S` and the covariant gradient of the rough Laplacian of `S`, as a
smooth compactly-supported `(r, s + 1)`-tensor field:
```
pointwiseTensorCurvRS g r s S := Δ_∇(∇S) − ∇(Δ_∇ S).
```
This is the contravariant-rank-`r` lift of `pointwiseTensorCurv` (`PointwiseTensorBochner`); at `r = 0`
it is definitionally `pointwiseTensorCurv g s`. Its body matches the inline defect form the rank-`r`
leaf-`C` consumers (`LocalWeylReproducingKernel`) state. -/
noncomputable def pointwiseTensorCurvRS
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (S : SmoothCcTensor g r s) :
    SmoothCcTensor g r (s + 1) :=
  rawTensorConnLapSmooth (I := I) g r (s + 1) (covGrad (I := I) (M := M) g r s S) -
    covGrad (I := I) (M := M) g r s (rawTensorConnLapSmooth (I := I) g r s S)

/-- The section value of the rank-`r` defect as a pointwise difference. -/
theorem pointwiseTensorCurvRS_toSection_eq_sub
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (S : SmoothCcTensor g r s) (x : M) :
    (pointwiseTensorCurvRS (I := I) (M := M) g r s S).toSection x =
      (rawTensorConnLapSmooth (I := I) g r (s + 1)
          (covGrad (I := I) (M := M) g r s S)).toSection x -
        (covGrad (I := I) (M := M) g r s
          (rawTensorConnLapSmooth (I := I) g r s S)).toSection x := by
  have hdef : (pointwiseTensorCurvRS (I := I) (M := M) g r s S) =
      rawTensorConnLapSmooth (I := I) g r (s + 1) (covGrad (I := I) (M := M) g r s S) -
        covGrad (I := I) (M := M) g r s (rawTensorConnLapSmooth (I := I) g r s S) := rfl
  rw [hdef, SmoothCcTensor.toSection_sub]
  rfl

/-- **The fixed-frame pure-Riemann genuine curvature trace at `(r, s)`.** For a fixed smooth tangent
frame `B` and a fixed smooth tangent field `W`, the frame sum at `y` of the pure-Riemann curvature
contraction `R(Bᵢ, W)(∇_{Bᵢ} S)`, a `(r, s)`-tensor. The rank-`r` analogue of
`genuineCurvTraceFixedFramePureR`; built from the rank-generic bundled curvature section `riemannSec`
and directional derivative `covApply` of the `(r, s)`-tensor connection `tensorCov g r s`. -/
noncomputable def genuineCurvTraceFixedFramePureRRS
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (W : Π b : M, TangentSpace I b)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b)
    (S : Π b : M, TensorRSSpace r s I b) (y : M) :
    TensorRSSpace r s I y :=
  ∑ i : Fin (Module.finrank ℝ E),
    riemannSec (tensorCov (I := I) g r s) (B i) W
      (covApply (tensorCov (I := I) g r s) (B i) S) y

/-- **Smoothness of the fixed-frame pure-Riemann genuine curvature trace at `(r, s)`.** For a smooth
tangent frame `B`, a smooth tangent field `W` and a smooth `(r, s)`-tensor section `S`, the trace is a
smooth `(r, s)`-tensor section: a finite frame sum of curvature contractions, each smooth via
`covApplyRS_contMDiff` (the contracted gradient) and `riemannSec_contMDiff` (the curvature section) for
the rank-generic connection `tensorCov g r s`. -/
theorem genuineCurvTraceFixedFramePureRRS_contMDiff
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    {W : Π b : M, TangentSpace I b}
    {B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b}
    {S : Π b : M, TensorRSSpace r s I b}
    (hW : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% W))
    (hB : ∀ i, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (B i)))
    (hS_total : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) y (S y))) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) y
        (genuineCurvTraceFixedFramePureRRS (I := I) g r s W B S y)) := by
  classical
  refine ContMDiff.sum_section (s := Finset.univ) (fun i _ => ?_)
  have hcovBS : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) y
        (covApply (tensorCov (I := I) g r s) (B i) S y)) :=
    covApplyRS_contMDiff (I := I) g r s hS_total (hB i)
  exact riemannSec_contMDiff (cov := tensorCov (I := I) g r s) (hB i) hW hcovBS

/-- **The slot-`i` pure-Riemann genuine direction linear map at `(r, s)`, for a general fixed frame.**
The curvature-direction-linear summand `v ↦ riemannOp (tensorCov g r s) x (Bᵢ x) v (∇_{Bᵢ} S(x))`. -/
def pureRDirLMSummandFixedFrameRS
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (S : SmoothCcTensor g r s)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b) (x : M)
    (i : Fin (Module.finrank ℝ E)) :
    TangentSpace I x →ₗ[ℝ] TensorRSSpace r s I x where
  toFun v := riemannOp (tensorCov (I := I) g r s) x (B i x) v
    (covApply (tensorCov (I := I) g r s) (B i) (fun y : M => S.toSection y) x)
  map_add' v v' := by
    rw [(riemannOp (tensorCov (I := I) g r s) x (B i x)).map_add v v']
    rfl
  map_smul' c v := by
    rw [(riemannOp (tensorCov (I := I) g r s) x (B i x)).map_smul c v]
    rfl

/-- The continuous-linear-map form of `pureRDirLMSummandFixedFrameRS`. -/
noncomputable def pureRDirCLMSummandFixedFrameRS
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (S : SmoothCcTensor g r s)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b) (x : M)
    (i : Fin (Module.finrank ℝ E)) :
    TangentSpace I x →L[ℝ] TensorRSSpace r s I x :=
  haveI : T2Space (TangentSpace I x) := inferInstanceAs (T2Space E)
  haveI : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  LinearMap.toContinuousLinearMap (pureRDirLMSummandFixedFrameRS (I := I) (M := M) g r s S B x i)

/-- **The fixed-frame pure-Riemann genuine curvature direction continuous-linear map at `(r, s)`.**
The frame sum over `i` of `pureRDirCLMSummandFixedFrameRS`. -/
noncomputable def pureRDirCLMFixedFrameRS
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (S : SmoothCcTensor g r s)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b) (x : M) :
    TangentSpace I x →L[ℝ] TensorRSSpace r s I x :=
  ∑ i : Fin (Module.finrank ℝ E), pureRDirCLMSummandFixedFrameRS (I := I) (M := M) g r s S B x i

/-- **The fixed-frame pure-Riemann genuine direction CLM, evaluated on a smooth tangent field, is the
fixed-frame pure-Riemann genuine trace at that field.** Each summand is identified by
`riemannOp_apply_smooth` against the smooth fields `B i`, `W`, and the smooth covariant-derivative
section `covApply (tensorCov g r s) (B i) (S.toSection)`. -/
lemma pureRDirCLMFixedFrameRS_apply_smooth
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (S : SmoothCcTensor g r s)
    {W : Π b : M, TangentSpace I b}
    {B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b}
    (hW : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% W))
    (hB : ∀ i, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (B i))) (x : M) :
    pureRDirCLMFixedFrameRS (I := I) (M := M) g r s S B x (W x) =
      genuineCurvTraceFixedFramePureRRS (I := I) g r s W B (fun y : M => S.toSection y) x := by
  classical
  rw [pureRDirCLMFixedFrameRS, ContinuousLinearMap.sum_apply, genuineCurvTraceFixedFramePureRRS]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [pureRDirCLMSummandFixedFrameRS, LinearMap.coe_toContinuousLinearMap',
    pureRDirLMSummandFixedFrameRS, LinearMap.coe_mk, AddHom.coe_mk]
  have hS_total : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) y (S.toSection y)) :=
    S.toSection.contMDiff_toFun
  have hcovBS : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) y
        (covApply (tensorCov (I := I) g r s) (B i) (fun z : M => S.toSection z) y)) :=
    covApplyRS_contMDiff (I := I) g r s hS_total (hB i)
  have happly := riemannOp_apply_smooth (cov := tensorCov (I := I) g r s)
    (X := B i) (Y := W)
    (Z := covApply (tensorCov (I := I) g r s) (B i) (fun z : M => S.toSection z))
    (x := x) (hB i) hW hcovBS
  rw [happly]

/-- **The fixed-frame pure-Riemann genuine direction CLM is a smooth `Hom(TM, T^{(r,s)})`-bundle
section.** On every smooth tangent field `Y`, the section `x ↦ ⟨x, pureRDirCLMFixedFrameRS g r s S B x
(Y x)⟩` is the fixed-frame pure-Riemann genuine trace
`genuineCurvTraceFixedFramePureRRS g r s Y B (S.toSection)`
(`pureRDirCLMFixedFrameRS_apply_smooth`), a smooth `(r, s)`-section
(`genuineCurvTraceFixedFramePureRRS_contMDiff`); the operator-to-bundle bridge is
`cotangentCov_clmSection_smooth_aux`. -/
private theorem pureRDirCLMFixedFrameRS_homSection_contMDiff
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (S : SmoothCcTensor g r s)
    {B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b}
    (hB : ∀ i, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (B i))) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] TensorRSModel r s ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (E →L[ℝ] TensorRSModel r s ℝ E)
        (E := fun y : M => TangentSpace I y →L[ℝ] TensorRSSpace r s I y) x
        (pureRDirCLMFixedFrameRS (I := I) (M := M) g r s S B x)) := by
  classical
  refine cotangentCov_clmSection_smooth_aux
    (φ := fun x : M => pureRDirCLMFixedFrameRS (I := I) (M := M) g r s S B x) (fun Y => ?_)
  have hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (fun b : M => (Y : Π b : M, TangentSpace I b) b)) :=
    Y.contMDiff
  have htrace := genuineCurvTraceFixedFramePureRRS_contMDiff (I := I) g r s
    (W := fun b : M => Y b) (B := B) (S := fun y : M => S.toSection y) hY hB
    S.toSection.contMDiff_toFun
  refine htrace.congr ?_
  intro x
  exact congrArg (TotalSpace.mk' (TensorRSModel r s ℝ E)
    (E := fun z : M => TensorRSSpace r s I z) x)
    (pureRDirCLMFixedFrameRS_apply_smooth (I := I) (M := M) g r s S hY hB x)

/-- **The fixed-frame pure-Riemann moving-centre genuine curvature `(r, s + 1)`-tensor fibre value.**
The slot-`0` uncurry, through `covGradBundleEquiv r s x`, of the fixed-frame pure-Riemann direction CLM
`pureRDirCLMFixedFrameRS g r s S B x`. -/
noncomputable def genuineCurvPureRFibFixedFrameRS
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (S : SmoothCcTensor g r s)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b) (x : M) :
    TensorRSSpace r (s + 1) I x :=
  covGradBundleEquiv (I := I) (M := M) r s x (pureRDirCLMFixedFrameRS (I := I) (M := M) g r s S B x)

/-- **Base-point smoothness of the fixed-frame pure-Riemann genuine curvature `(r, s + 1)`-fibre
field.** The smooth `Hom(TM, T^{(r,s)})`-section `x ↦ ⟨x, pureRDirCLMFixedFrameRS g r s S B x⟩`
(`pureRDirCLMFixedFrameRS_homSection_contMDiff`) transported, fibrewise through
`covGradBundleSmoothEquiv r s`, into the `(r, s + 1)`-tensor bundle. -/
private theorem genuineCurvPureRFibFixedFrameRS_contMDiff
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (S : SmoothCcTensor g r s)
    {B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b}
    (hB : ∀ i, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (B i))) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r (s + 1) ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel r (s + 1) ℝ E)
        (E := fun z : M => TensorRSSpace r (s + 1) I z) x
        (genuineCurvPureRFibFixedFrameRS (I := I) (M := M) g r s S B x)) := by
  classical
  have hcomp :
      ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r (s + 1) ℝ E)) ∞
        ((covGradBundleSmoothEquiv (I := I) (M := M) r s).toDiffeomorph ∘
          (fun x : M => TotalSpace.mk' (E →L[ℝ] TensorRSModel r s ℝ E)
            (E := fun y : M => TangentSpace I y →L[ℝ] TensorRSSpace r s I y) x
            (pureRDirCLMFixedFrameRS (I := I) (M := M) g r s S B x))) :=
    (covGradBundleSmoothEquiv (I := I) (M := M) r s).toDiffeomorph.contMDiff.comp
      (pureRDirCLMFixedFrameRS_homSection_contMDiff (I := I) (M := M) g r s S hB)
  refine hcomp.congr ?_
  intro x
  rw [Function.comp_apply]
  exact covGradBundleSmoothEquiv_toDiffeomorph_apply (I := I) (M := M) r s x
    (pureRDirCLMFixedFrameRS (I := I) (M := M) g r s S B x)

/-- **The fixed-frame pure-Riemann genuine curvature section against a smooth frame `B`** at `(r, s)`,
a smooth compactly-supported `(r, s + 1)`-tensor section: fibre value
`genuineCurvPureRFibFixedFrameRS g r s S B x`, base-point smoothness
`genuineCurvPureRFibFixedFrameRS_contMDiff`, compact support on the closed manifold. The general-`B`
companion of `GcurvSectionRS`. -/
noncomputable def fixedFramePureRSectionRS
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (S : SmoothCcTensor g r s)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b)
    (hB : ∀ i, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (B i))) :
    SmoothCcTensor g r (s + 1) where
  toSection :=
    { toFun := fun x : M => genuineCurvPureRFibFixedFrameRS (I := I) (M := M) g r s S B x
      contMDiff_toFun := genuineCurvPureRFibFixedFrameRS_contMDiff (I := I) (M := M) g r s S hB }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

/-- **The pure-Riemann genuine bilinear form at `y` (rank `r`).** The continuous bilinear form
`(X, Y) ↦ riemannOp (tensorCov g r s) y X (W y) (∇^{CLM}_Y S(y))`, where `∇^{CLM}_· S(y) :=
(tensorCov g r s).toFun (S.toSection) y`. The frame index of the pure-Riemann genuine trace is
contracted twice (as `X` in slot-`0` of `R` and as `Y` in the gradient direction). -/
private noncomputable def pureRValuedBilinAtRS
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (S : SmoothCcTensor g r s)
    (W : Π b : M, TangentSpace I b) (y : M) :
    TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] TensorRSSpace r s I y :=
  haveI : T2Space (TangentSpace I y) := inferInstanceAs (T2Space E)
  haveI : FiniteDimensional ℝ (TangentSpace I y) := inferInstanceAs (FiniteDimensional ℝ E)
  LinearMap.toContinuousLinearMap
    { toFun := fun X => (riemannOp (tensorCov (I := I) g r s) y X (W y)).comp
        ((tensorCov (I := I) g r s).toFun (fun b : M => S.toSection b) y)
      map_add' := fun X X' => by
        ext Y
        simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply,
          (riemannOp (tensorCov (I := I) g r s) y).map_add X X']
      map_smul' := fun c X => by
        ext Y
        simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
          RingHom.id_apply, (riemannOp (tensorCov (I := I) g r s) y).map_smul c X] }

/-- The defining apply formula for `pureRValuedBilinAtRS`. -/
private lemma pureRValuedBilinAtRS_apply
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (S : SmoothCcTensor g r s)
    (W : Π b : M, TangentSpace I b) (y : M) (X Y : TangentSpace I y) :
    pureRValuedBilinAtRS (I := I) (M := M) g r s S W y X Y =
      riemannOp (tensorCov (I := I) g r s) y X (W y)
        ((tensorCov (I := I) g r s).toFun (fun b : M => S.toSection b) y Y) := rfl

/-- **The diagonal of `pureRValuedBilinAtRS` on a smooth frame is the pure-Riemann genuine trace
summand.** `riemannOp_apply_smooth` identifies the bundled `riemannOp` value with `riemannSec` on the
smooth fields `B i`, `W`, and the smooth covariant-derivative section
`covApply (tensorCov g r s) (B i) (S.toSection)`. -/
private lemma pureRValuedBilinAtRS_frame_summand
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (S : SmoothCcTensor g r s)
    {W : Π b : M, TangentSpace I b}
    {B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b}
    (hW : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% W))
    (hB : ∀ i, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (B i)))
    (i : Fin (Module.finrank ℝ E)) (x : M) :
    pureRValuedBilinAtRS (I := I) (M := M) g r s S W x (B i x) (B i x) =
      riemannSec (tensorCov (I := I) g r s) (B i) W
        (covApply (tensorCov (I := I) g r s) (B i) (fun y : M => S.toSection y)) x := by
  classical
  rw [pureRValuedBilinAtRS_apply]
  have hS_total : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) y (S.toSection y)) :=
    S.toSection.contMDiff_toFun
  have hcovBS : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) y
        (covApply (tensorCov (I := I) g r s) (B i) (fun z : M => S.toSection z) y)) :=
    covApplyRS_contMDiff (I := I) g r s hS_total (hB i)
  have happly := riemannOp_apply_smooth (cov := tensorCov (I := I) g r s)
    (X := B i) (Y := W)
    (Z := covApply (tensorCov (I := I) g r s) (B i) (fun z : M => S.toSection z))
    (x := x) (hB i) hW hcovBS
  exact happly

/-- **The pure-Riemann genuine trace at `(r, s)` is frame-independent among `g_y`-orthonormal frames.**
For two smooth tangent frames `B`, `C` both `g_y`-orthonormal at `y` and a smooth field `W`,
```
genuineCurvTraceFixedFramePureRRS g r s W B (S.toSection) y
  = genuineCurvTraceFixedFramePureRRS g r s W C (S.toSection) y.
```
The trace summand is the diagonal `pureRValuedBilinAtRS g r s S W y (·, ·)` of a continuous bilinear
`(r, s)`-valued form (`pureRValuedBilinAtRS_frame_summand`); evaluating against an arbitrary lower-input
`D : Tensor0SSpace r I y` and a tail tuple `m`, the scalar diagonal trace `∑ᵢ Hb(Bᵢ, Bᵢ)` is
frame-independent by `orthonormal_basis_bilin_trace` (both equal `∑_{kl} G^{kl}(y) Hb(e_k, e_l)`), so
the `(r, s)`-tensors agree on every `D` and `m`. The rank-`r` scalarization
`T ↦ toModel (T D) m : TensorRSSpace r s I y →L[ℝ] ℝ` reads off the `(r, s)`-tensor through its
underlying `Tensor0SSpace r I y →L[ℝ] Tensor0SSpace s I y` (this is the only place the contravariant
rank enters, and it ports the `(0, s)` scalarization with `unit` replaced by the universally
quantified `D`). -/
private theorem genuineCurvTraceFixedFramePureRRS_frame_independent
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (S : SmoothCcTensor g r s)
    {W : Π b : M, TangentSpace I b}
    {B C : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b}
    (hW : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% W))
    (hB : ∀ i, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (B i)))
    (hC : ∀ i, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (C i))) (y : M)
    (hB_orth : ∀ i j : Fin (Module.finrank ℝ E),
      g.inner y (B i y) (B j y) = if i = j then (1 : ℝ) else 0)
    (hC_orth : ∀ i j : Fin (Module.finrank ℝ E),
      g.inner y (C i y) (C j y) = if i = j then (1 : ℝ) else 0) :
    genuineCurvTraceFixedFramePureRRS (I := I) g r s W B (fun b : M => S.toSection b) y =
      genuineCurvTraceFixedFramePureRRS (I := I) g r s W C (fun b : M => S.toSection b) y := by
  classical
  haveI : T2Space (TangentSpace I y) := inferInstanceAs (T2Space E)
  haveI : FiniteDimensional ℝ (TangentSpace I y) := inferInstanceAs (FiniteDimensional ℝ E)
  refine ContinuousLinearMap.ext (fun D => ?_)
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro m
  haveI : T2Space (TensorRSSpace r s I y) :=
    inferInstanceAs (T2Space (Tensor0SSpace r I y →L[ℝ] Tensor0SSpace s I y))
  haveI : FiniteDimensional ℝ (TensorRSSpace r s I y) :=
    inferInstanceAs (FiniteDimensional ℝ (Tensor0SSpace r I y →L[ℝ] Tensor0SSpace s I y))
  set scalarize : TensorRSSpace r s I y →L[ℝ] ℝ :=
    LinearMap.toContinuousLinearMap
      { toFun := fun T => Tensor0SSpace.toModel
          ((show Tensor0SSpace r I y →L[ℝ] Tensor0SSpace s I y from T) D) m
        map_add' := fun T T' => by
          change Tensor0SSpace.toModel ((T + T') D) m =
            Tensor0SSpace.toModel (T D) m + Tensor0SSpace.toModel (T' D) m
          rw [ContinuousLinearMap.add_apply, Tensor0SSpace.toModel_add,
            ContinuousMultilinearMap.add_apply]
        map_smul' := fun c T => by
          change Tensor0SSpace.toModel ((c • T) D) m = c • Tensor0SSpace.toModel (T D) m
          rw [ContinuousLinearMap.smul_apply, Tensor0SSpace.toModel_smul,
            ContinuousMultilinearMap.smul_apply] }
    with hscalarize_def
  have hscalarize_apply : ∀ T : TensorRSSpace r s I y,
      scalarize T = Tensor0SSpace.toModel
        ((show Tensor0SSpace r I y →L[ℝ] Tensor0SSpace s I y from T) D) m := by
    intro T
    rw [hscalarize_def, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk]
  set Hb : TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ :=
    LinearMap.toContinuousLinearMap
      { toFun := fun X => scalarize.comp (pureRValuedBilinAtRS (I := I) (M := M) g r s S W y X)
        map_add' := fun X X' => by
          ext Y
          change scalarize (pureRValuedBilinAtRS (I := I) (M := M) g r s S W y (X + X') Y) =
            scalarize (pureRValuedBilinAtRS (I := I) (M := M) g r s S W y X Y) +
              scalarize (pureRValuedBilinAtRS (I := I) (M := M) g r s S W y X' Y)
          rw [map_add (pureRValuedBilinAtRS (I := I) (M := M) g r s S W y) X X',
            ContinuousLinearMap.add_apply, map_add scalarize]
        map_smul' := fun c X => by
          ext Y
          change scalarize (pureRValuedBilinAtRS (I := I) (M := M) g r s S W y (c • X) Y) =
            c • scalarize (pureRValuedBilinAtRS (I := I) (M := M) g r s S W y X Y)
          rw [map_smul (pureRValuedBilinAtRS (I := I) (M := M) g r s S W y) c X,
            ContinuousLinearMap.smul_apply, map_smul scalarize] }
    with hHb_def
  have hHb_apply : ∀ X Y : TangentSpace I y,
      Hb X Y = Tensor0SSpace.toModel
        ((show Tensor0SSpace r I y →L[ℝ] Tensor0SSpace s I y from
          pureRValuedBilinAtRS (I := I) (M := M) g r s S W y X Y) D) m := by
    intro X Y
    rw [hHb_def, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk,
      ContinuousLinearMap.comp_apply, hscalarize_apply]
  have hframe : ∀ (F : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b),
      (∀ i, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (F i))) →
      Tensor0SSpace.toModel
        ((show Tensor0SSpace r I y →L[ℝ] Tensor0SSpace s I y from
          genuineCurvTraceFixedFramePureRRS (I := I) g r s W F (fun b : M => S.toSection b) y) D) m =
      ∑ i : Fin (Module.finrank ℝ E), Hb (F i y) (F i y) := by
    intro F hF
    have hsum_apply :
        (show Tensor0SSpace r I y →L[ℝ] Tensor0SSpace s I y from
          genuineCurvTraceFixedFramePureRRS (I := I) g r s W F (fun b : M => S.toSection b) y) D =
        ∑ i : Fin (Module.finrank ℝ E),
          (show Tensor0SSpace r I y →L[ℝ] Tensor0SSpace s I y from
            riemannSec (tensorCov (I := I) g r s) (F i) W
              (covApply (tensorCov (I := I) g r s) (F i) (fun b : M => S.toSection b)) y) D := by
      rw [genuineCurvTraceFixedFramePureRRS, ContinuousLinearMap.sum_apply]
    rw [hsum_apply, ← Tensor0SSpace.toModelL_apply, map_sum, ContinuousMultilinearMap.sum_apply]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Tensor0SSpace.toModelL_apply, hHb_apply (F i y) (F i y),
      pureRValuedBilinAtRS_frame_summand (I := I) (M := M) g r s S hW hF i y]
  rw [hframe B hB, hframe C hC]
  rw [orthonormal_basis_bilin_trace (I := I) (M := M) g (x := y) Hb (fun i => B i y) hB_orth,
    orthonormal_basis_bilin_trace (I := I) (M := M) g (x := y) Hb (fun i => C i y) hC_orth]

/-- **The moving-centre pure-Riemann genuine direction CLM at `(r, s)`** (`B = smoothOrthoFrame g x`).
True by definition the fixed-frame direction CLM against the moving frame. -/
private noncomputable def genuinePureRDirCLMRS
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (S : SmoothCcTensor g r s) (x : M) :
    TangentSpace I x →L[ℝ] TensorRSSpace r s I x :=
  pureRDirCLMFixedFrameRS (I := I) (M := M) g r s S (smoothOrthoFrame (I := I) g x) x

/-- **The moving-centre pure-Riemann genuine direction CLM, evaluated at the smooth extension of a
tangent vector, is the moving-frame pure-Riemann genuine trace at that direction.** -/
private lemma genuinePureRDirCLMRS_apply_extend
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (S : SmoothCcTensor g r s) (x : M)
    (v : TangentSpace I x) :
    genuinePureRDirCLMRS (I := I) (M := M) g r s S x v =
      genuineCurvTraceFixedFramePureRRS (I := I) g r s (smoothExtensionTangent (I := I) x v)
        (smoothOrthoFrame (I := I) g x) (fun y : M => S.toSection y) x := by
  classical
  rw [genuinePureRDirCLMRS]
  rw [show v = (smoothExtensionTangent (I := I) x v) x from (smoothExtensionTangent_eq x v).symm]
  rw [pureRDirCLMFixedFrameRS_apply_smooth (I := I) (M := M) g r s S
    (smoothExtensionTangent_contMDiff x v)
    (fun i => smoothOrthoFrame_smooth (I := I) g x i) x]
  rw [smoothExtensionTangent_eq x v]

/-- **The pure-Riemann moving-centre genuine curvature `(r, s + 1)`-tensor fibre value.** The slot-`0`
uncurry of the moving-centre pure-Riemann genuine direction CLM `genuinePureRDirCLMRS` through
`covGradBundleEquiv r s x`. Its base-point smoothness is the frame-independence freeze
`genuineCurvPureRFibRS_contMDiff`. -/
noncomputable def genuineCurvPureRFibRS
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (S : SmoothCcTensor g r s) (x : M) :
    TensorRSSpace r (s + 1) I x :=
  covGradBundleEquiv (I := I) (M := M) r s x (genuinePureRDirCLMRS (I := I) (M := M) g r s S x)

/-- **On `smoothOrthoFrameNbhd x₀`, the moving-centre pure-Riemann fibre value equals the
frozen-frame fibre value against `smoothOrthoFrame g x₀`.** Both are the slot-`0` uncurry of a
pure-Riemann genuine direction CLM, so it suffices to identify the CLMs; on `v`, both reduce to the
pure-Riemann genuine trace at `smoothExtensionTangent y v`, against the *moving* frame
`smoothOrthoFrame g y` (orthonormal at its centre `y`) and the *frozen* frame `smoothOrthoFrame g x₀`
(orthonormal at `y` for `y ∈ smoothOrthoFrameNbhd x₀`), which agree by frame-independence
`genuineCurvTraceFixedFramePureRRS_frame_independent`. -/
private lemma genuineCurvPureRFibRS_eq_fixedFrame_smoothOrthoFrame_on_nbhd
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (S : SmoothCcTensor g r s) (x₀ : M)
    {y : M} (hy : y ∈ smoothOrthoFrameNbhd (I := I) (M := M) x₀) :
    genuineCurvPureRFibRS (I := I) (M := M) g r s S y =
      genuineCurvPureRFibFixedFrameRS (I := I) (M := M) g r s S
        (smoothOrthoFrame (I := I) g x₀) y := by
  classical
  rw [genuineCurvPureRFibRS, genuineCurvPureRFibFixedFrameRS]
  congr 1
  refine ContinuousLinearMap.ext (fun v => ?_)
  have hRHS : pureRDirCLMFixedFrameRS (I := I) (M := M) g r s S
        (smoothOrthoFrame (I := I) g x₀) y v =
      genuineCurvTraceFixedFramePureRRS (I := I) g r s (smoothExtensionTangent (I := I) y v)
        (smoothOrthoFrame (I := I) g x₀) (fun b : M => S.toSection b) y := by
    rw [show v = (smoothExtensionTangent (I := I) y v) y from
      (smoothExtensionTangent_eq y v).symm]
    rw [pureRDirCLMFixedFrameRS_apply_smooth (I := I) (M := M) g r s S
      (smoothExtensionTangent_contMDiff y v)
      (fun i => smoothOrthoFrame_smooth (I := I) g x₀ i) y]
    rw [smoothExtensionTangent_eq y v]
  rw [genuinePureRDirCLMRS_apply_extend (I := I) (M := M) g r s S y v, hRHS]
  exact genuineCurvTraceFixedFramePureRRS_frame_independent (I := I) (M := M) g r s S
    (smoothExtensionTangent_contMDiff y v)
    (fun i => smoothOrthoFrame_smooth (I := I) g y i)
    (fun i => smoothOrthoFrame_smooth (I := I) g x₀ i) y
    (fun i j => smoothOrthoFrame_orthonormal_at_center (I := I) g y i j)
    (fun i j => smoothOrthoFrame_orthonormal (I := I) g x₀ hy i j)

/-- **Base-point smoothness of the pure-Riemann moving-centre genuine curvature fibre field at
`(r, s)`.** The pure-Riemann genuine trace `∑ᵢ R(Bᵢ, v)(∇_{Bᵢ} S)` is a *genuine metric trace* (the
frame index `Bᵢ` is contracted twice), hence frame-independent among `g_y`-orthonormal frames
(`genuineCurvTraceFixedFramePureRRS_frame_independent`, the bilinear-Parseval argument
`orthonormal_basis_bilin_trace`). Therefore on `smoothOrthoFrameNbhd x₀` the moving fibre equals the
frozen fibre against `smoothOrthoFrame g x₀`
(`genuineCurvPureRFibRS_eq_fixedFrame_smoothOrthoFrame_on_nbhd`), a smooth `(r, s + 1)`-section
(`genuineCurvPureRFibFixedFrameRS_contMDiff`), and `ContMDiffAt.congr_of_eventuallyEq` transfers
smoothness.

**Non-vacuity.** Its slot-`0` curry along any `v` is the pure-Riemann contraction
`∑ᵢ R(Bᵢ, v)(∇_{Bᵢ} S)(x)`, non-zero when `R ≠ 0` and `∇S ≠ 0`; the field carries the actual
pure-Riemann `R(∇S)` content and cannot be replaced by the zero section. -/
private theorem genuineCurvPureRFibRS_contMDiff
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (S : SmoothCcTensor g r s) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r (s + 1) ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel r (s + 1) ℝ E)
        (E := fun z : M => TensorRSSpace r (s + 1) I z) y
        (genuineCurvPureRFibRS (I := I) (M := M) g r s S y)) := by
  classical
  intro x₀
  have h_fixed_at : ContMDiffAt I (I.prod 𝓘(ℝ, TensorRSModel r (s + 1) ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel r (s + 1) ℝ E)
        (E := fun z : M => TensorRSSpace r (s + 1) I z) y
        (genuineCurvPureRFibFixedFrameRS (I := I) (M := M) g r s S
          (smoothOrthoFrame (I := I) g x₀) y)) x₀ :=
    genuineCurvPureRFibFixedFrameRS_contMDiff (I := I) (M := M) g r s S
      (fun i => smoothOrthoFrame_smooth (I := I) g x₀ i) x₀
  refine h_fixed_at.congr_of_eventuallyEq ?_
  filter_upwards [smoothOrthoFrameNbhd_mem_nhds (I := I) (M := M) x₀] with y hy
  exact congrArg (TotalSpace.mk' (TensorRSModel r (s + 1) ℝ E)
    (E := fun z : M => TensorRSSpace r (s + 1) I z) y)
    (genuineCurvPureRFibRS_eq_fixedFrame_smoothOrthoFrame_on_nbhd (I := I) (M := M) g r s S x₀ hy)

/-- **The moving-centre pure-Riemann genuine curvature section** `GcurvSectionRS`, a smooth compactly-
supported `(r, s + 1)`-tensor section packaging the pure-Riemann contraction `R(∇S)` of the order-`2`
rough-Laplacian / covariant-gradient commutator defect (the slot-`0` assembly of the moving-frame
genuine curvature trace `∑ᵢ R(Bᵢ, ·)(∇_{Bᵢ} S)`) at contravariant rank `r`. Its base-point smoothness
is `genuineCurvPureRFibRS_contMDiff` (a frame-independence freeze of the pure-Riemann metric trace,
*sorry-free*). The rank-`r` analogue of `GcurvSection`. -/
noncomputable def GcurvSectionRS
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (S : SmoothCcTensor g r s) :
    SmoothCcTensor g r (s + 1) where
  toSection :=
    { toFun := fun y : M => genuineCurvPureRFibRS (I := I) (M := M) g r s S y
      contMDiff_toFun := genuineCurvPureRFibRS_contMDiff (I := I) (M := M) g r s S }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

@[simp] theorem GcurvSectionRS_toSection
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (S : SmoothCcTensor g r s) (x : M) :
    (GcurvSectionRS (I := I) (M := M) g r s S).toSection x =
      genuineCurvPureRFibRS (I := I) (M := M) g r s S x := rfl

/-- **Heterogeneous rank-congruence for `covGrad` at rank `r` (file-local).** If `h : a = b`, then
`covGrad g r a Y` and `covGrad g r b Z` are heterogeneously equal whenever `Y, Z` are. -/
private theorem covGradRS_heq_congr_fp (g : SmoothRiemannianMetric I M) (r : ℕ) {a b : ℕ}
    (h : a = b) {Y : SmoothCcTensor g r a} {Z : SmoothCcTensor g r b} (hYZ : HEq Y Z) :
    HEq (covGrad (I := I) (M := M) g r a Y) (covGrad (I := I) (M := M) g r b Z) := by
  subst h; rw [eq_of_heq hYZ]

/-- **Heterogeneous commuting of one covariant gradient through the iterated gradient at rank `r`
(file-local).** Applying `q` covariant gradients to `covGrad g r s S` is heterogeneously equal to the
`(q + 1)`-fold iterated gradient of `S`. -/
private theorem iteratedCovGradRS_covGrad_comm_heq_fp (g : SmoothRiemannianMetric I M)
    (r s q : ℕ) (S : SmoothCcTensor g r s) :
    HEq (iteratedCovGrad g r (s + 1) q (covGrad (I := I) (M := M) g r s S))
      (iteratedCovGrad g r s (q + 1) S) := by
  induction q with
  | zero => rw [iteratedCovGrad_zero, iteratedCovGrad_succ, iteratedCovGrad_zero]; exact HEq.rfl
  | succ k ih =>
      rw [iteratedCovGrad_succ (g := g) (r := r) (s := s + 1) (j := k)
        (covGrad (I := I) (M := M) g r s S)]
      rw [iteratedCovGrad_succ (g := g) (r := r) (s := s) (j := k + 1) S]
      exact covGradRS_heq_congr_fp g r (by omega : (s + 1) + k = s + (k + 1)) ih

/-- **`rfns` is invariant under a `SmoothCcTensor` rank-cast at rank `r` (file-local).**
Heterogeneously equal smooth compactly-supported `(r, ·)`-tensors over agreeing ranks have equal
section-value `riemannianFiberNormSq` at every point. Proved by `subst` on the rank variable. -/
private theorem rfns_toSection_heq_congr_fp (g : SmoothRiemannianMetric I M)
    (r : ℕ) {a b : ℕ} (h : a = b) {Y : SmoothCcTensor g r a} {Z : SmoothCcTensor g r b}
    (hYZ : HEq Y Z) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g r a x (Y.toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g r b x (Z.toSection x) := by
  subst h; rw [eq_of_heq hYZ]

/-- **Front-commuting one covariant gradient through the iterated gradient (rfns form) at rank `r`.**
The intrinsic squared fibre norm of `∇^q(∇S)` at `x` equals that of `∇^{q+1}S` (ranks `(s + 1) + q` and
`s + (q + 1)` agree as naturals; `rfns` is invariant under that rank-cast). The reindex collapsing the
engine's `∇S`-jet window `0 … k` to the `1 … 1 + k` window of `S` in the pure-Riemann grid. -/
private theorem rfns_iteratedCovGradRS_covGrad_comm_local (g : SmoothRiemannianMetric I M)
    (r s q : ℕ) (S : SmoothCcTensor g r s) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g r ((s + 1) + q) x
        ((iteratedCovGrad g r (s + 1) q (covGrad (I := I) (M := M) g r s S)).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g r (s + (q + 1)) x
        ((iteratedCovGrad g r s (q + 1) S).toSection x) :=
  rfns_toSection_heq_congr_fp (I := I) (M := M) g r (by omega : (s + 1) + q = s + (q + 1))
    (iteratedCovGradRS_covGrad_comm_heq_fp (I := I) (M := M) g r s q S) x

/-- **The rank-`r` frame-free pure-Riemann differentiated curvature operator tower (posited
general-rank curvature primitive).** For a closed smooth Riemannian manifold `(M, g)` and a fixed
contravariant rank `r` there is a `DiffBilinOpRS g r` — a differentiated fibrewise-linear bilinear
contraction operator family (`RankRDiffBilinGrid`) carrying the exact recursive single-step covariant
Leibniz and a per-order, per-rank base-point-uniform proportional fibre envelope — whose order-`0`
operator, applied to the gradient field `∇S := covGrad g r s S` of any smooth compactly-supported
`(r, s)`-tensor `S`, is the concrete moving-centre pure-Riemann genuine curvature section
`GcurvSectionRS g r s S` (the slot-`0` assembly of the *tensorial* moving-frame trace
`∑ᵢ R(Bᵢ, ·)(∇_{Bᵢ} S)`, the `R(∇S)` contraction):

```
Φ.op 0 (s + 1) (covGrad g r s S) = GcurvSectionRS g r s S.
```

**Why this is TRUE.** This is the contravariant-rank-`r` mirror of the rank-`0` frame-free pure-Riemann
differentiated tower `pureRGenuineDiffOp` (`FrozenFramePureRCurvatureTower`), together with its exact
single-step covariant Leibniz `covGrad_pureRGenuineDiffOp_eq` (the `DiffBilinOpRS` field `covGrad_op`),
its frame-free per-order envelope `exists_proportional_pureRGenuineDiffOp` (the field `rfns_op_le`), and
the order-`0` bridge `pureRGenuineDiffOp0_eq_GcurvSection` (the displayed equation). The order-`0`
operator is the frame-free pure-Riemann curvature endomorphism, value-local per rank, reconstructing the
tensorial `R(∇S)` trace; the differentiated tower differentiates only the curvature factor (never a
frame jet), the sound frame-free analogue. The entire rank-`r` frame-free pure-Riemann differentiated
tower — its `op` family, the order-`0` endomorphism reading slot-`0` of the `(r, ·)`-bundle through
`covGradBundleEquiv r ·`, its Leibniz, and its envelope — is stated only at contravariant rank `0` in
the library (the rank-`0` `pureRGenuineDiffOp` tower is rank-`0`-coded: the slot-`0` endomorphism reads,
the `IsOrderZeroCurvFactor` predicate, and the rank-`0`-locked grid engine `DiffBilinOp`), so this
rank-`r` tower is posited here as the single precise true child — the genuinely-missing rank-`r`
upstream curvature primitive from which the rank-`r` pure-Riemann grid
`exists_GcurvSectionRS_iteratedCovGrad_grid_bound` is *proved* over the sorry-free generic rank-`r`
engine `DiffBilinOpRS`. Consumers transitively depend on `sorryAx`.

**Non-vacuity (the bridge rejects the zero tower).** A degenerate `Φ` with `op ≡ 0` (and `kappa ≡ 0`)
would force, by the bridge, `GcurvSectionRS g r s S = Φ.op 0 (s + 1) (∇S) = 0` at every `s`, `S`; but
the pure-Riemann section carries the genuine contraction `∑ᵢ R(Bᵢ, ·)(∇_{Bᵢ} S)`, non-zero on a
non-flat manifold (`R ≠ 0`) for a non-parallel `S` (`∇S ≠ 0`) (`genuineCurvPureRFibRS_contMDiff`, never
the zero section), so the bridge rejects the zero tower; and the `DiffBilinOpRS` envelope field
`rfns_op_le` with `kappa` is genuinely non-degenerate (its `kappa ≡ 0` witness is rejected whenever
`op 0 r W ≠ 0`). The posited tower genuinely computes the rank-`r` pure-Riemann contraction. -/
theorem exists_pureRGenuineDiffOpRS_bridge (g : SmoothRiemannianMetric I M) (r : ℕ) :
    ∃ Φ : DiffBilinOpRS g r, ∀ (s : ℕ) (S : SmoothCcTensor g r s),
      Φ.op 0 (s + 1) (covGrad (I := I) (M := M) g r s S) = GcurvSectionRS (I := I) (M := M) g r s S := by
  sorry

/-- **The rank-`r` pure-Riemann genuine-section iterated-gradient grid (posited general-rank curvature
child).** The contravariant-rank-`r` lift of the rank-`0` frame-free pure-Riemann grid headline
`exists_GcurvSection_iteratedCovGrad_grid_bound` (`FrozenFramePureRCurvatureTower`, *sorry-free* at rank
`0`). For a closed smooth Riemannian manifold `(M, g)` and a fixed contravariant rank `r` there is a
valence/order-dependent nonnegative constant family `c : ℕ → ℕ → ℝ` such that, at every covariant rank
`s`, every smooth compactly-supported `(r, s)`-tensor `S`, every gradient order `k` and every point `x`,
the `k`-fold iterated covariant gradient of the concrete moving-centre pure-Riemann genuine curvature
section `GcurvSectionRS g r s S` (the slot-`0` assembly of the *tensorial* moving-frame trace
`∑ᵢ R(Bᵢ, ·)(∇_{Bᵢ} S)`, the `R(∇S)` contraction) is fibre-bounded by the truncated contracted-order
window `1 … 1 + k` of the iterated gradients of `S`:

```
rfns(∇^k (GcurvSectionRS g r s S))(x) ≤ (c s k)² · ∑_{i < 1 + k} rfns(∇^{i + 1} S)(x).
```

**Why this is TRUE.** This is the verbatim contravariant-rank-`r` mirror of the rank-`0`
`exists_GcurvSection_iteratedCovGrad_grid_bound`. The pure-Riemann genuine section is the slot-`0`
assembly of a *tensorial* contraction of the bundled curvature operator `riemannOp (tensorCov g r s)`
against `∇S` (the frame index `Bᵢ` is contracted twice — in slot-`0` of the operator and as the
covariant-gradient direction), so each of its iterated covariant gradients `∇^k (GcurvSectionRS g r s S)`
is, by the iterated covariant Leibniz expansion of a non-parallel differentiated bilinear contraction,
a sum of contractions of `∇^p R` (`p ≤ k`) against `∇^{q + 1} S` (`q ≤ k`), with the contracted-order
window `1 … 1 + k` (the contraction enters the gradient field `∇S` at order `1`). Every curvature
coefficient is absorbed uniformly over the compact manifold into the per-order constant `(c s k)²`
(carrying `‖∇^{≤ k} R‖_∞`, finite by per-`k` compactness). At rank `0` the grid is *proved* off the
frame-free differentiated pure-Riemann operator tower (`pureRGenuineDiffOp`) through the generic
single-sum covariant-Leibniz grid engine `DiffBilinOp.exists_rfns_iteratedCovGrad_singleSum_le_at`; that
engine and the entire `DiffBilinOp` calculus are stated **only at contravariant rank `0`** (the
operator family `op : ∀ p r, SmoothCcTensor g 0 r → SmoothCcTensor g 0 (r + p)` carries a literal
contravariant `0`), so the rank-`r` grid is absent sorry-free below this file and is posited here as the
single precise true child — exactly the genuinely-missing rank-`r` upstream primitive from which the
rank-`r` graded packaging `GcurvSectionRS_gradedCurvJet` and the rank-`r` proportional section bound
`GcurvSectionRS_fiberNormSq_le_covGrad` (its `k = 0` collapse) are *proved*. Consumers transitively
depend on `sorryAx`.

**Non-vacuity.** With `c s 0 = 0` the bound at `k = 0` (where `∇^0(GcurvSectionRS g r s S) =
GcurvSectionRS g r s S`) forces `rfns(GcurvSectionRS g r s S)(x) = 0`, i.e. the pure-Riemann contraction
`∑ᵢ R(Bᵢ, ·)(∇_{Bᵢ} S)` vanishes; *false* on a non-flat manifold (`R ≠ 0`) for a non-parallel `S`
(`∇S ≠ 0`) — the field `GcurvSectionRS g r s S` carries the genuine pure-Riemann `R(∇S)` content
(`genuineCurvPureRFibRS_contMDiff`, never the zero section). The constant family is genuinely positive.
-/
theorem exists_GcurvSectionRS_iteratedCovGrad_grid_bound (g : SmoothRiemannianMetric I M) (r : ℕ) :
    ∃ c : ℕ → ℕ → ℝ, (∀ s k, 0 ≤ c s k) ∧
      ∀ (s : ℕ) (S : SmoothCcTensor g r s) (k : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g r ((s + 1) + k) x
            ((iteratedCovGrad g r (s + 1) k
              (GcurvSectionRS (I := I) (M := M) g r s S)).toSection x) ≤
          (c s k) ^ 2 * ∑ i ∈ Finset.range (1 + k),
            riemannianFiberNormSq (I := I) (M := M) g r (s + (i + 1)) x
              ((iteratedCovGrad g r s (i + 1) S).toSection x) := by
  classical
  -- The rank-`r` pure-Riemann grid is the sorry-free generic rank-`r` engine
  -- (`DiffBilinOpRS.exists_rfns_iteratedCovGrad_singleSum_le`) applied to the posited rank-`r`
  -- frame-free pure-Riemann differentiated tower `Φ`, base width `s + 1`, section `∇S`, gradient order
  -- `k`; the order-`0` bridge identifies `Φ.op 0 (s + 1) (∇S)` with `GcurvSectionRS`, and the rank-`r`
  -- reindex `∇^q(∇S) ≅ ∇^{q + 1}S` collapses the `∇S`-jet window `0 … k` to `1 … 1 + k` of `S`.
  obtain ⟨Φ, hbridge⟩ := exists_pureRGenuineDiffOpRS_bridge (I := I) (M := M) g r
  obtain ⟨C, hC_nn, hgrid⟩ := Φ.exists_rfns_iteratedCovGrad_singleSum_le
  refine ⟨fun s k => Real.sqrt (C (s + 1) k), fun s k => Real.sqrt_nonneg _, fun s S k x => ?_⟩
  have hCsq : (Real.sqrt (C (s + 1) k)) ^ 2 = C (s + 1) k := by
    rw [Real.sq_sqrt]; exact hC_nn (s + 1) k
  rw [hCsq]
  -- The engine grid for the tower at base width `s + 1`, section `∇S := covGrad g r s S`, order `k`.
  have hg := hgrid (s + 1) (covGrad (I := I) (M := M) g r s S) k x
  rw [hbridge s S] at hg
  refine hg.trans (le_of_eq ?_)
  refine congrArg (fun t => C (s + 1) k * t) ?_
  -- Re-index the `∇S`-jet window `q < k + 1` onto the `S`-jet window `i < 1 + k`.
  rw [Nat.add_comm 1 k]
  refine Finset.sum_congr rfl (fun q _ => ?_)
  exact rfns_iteratedCovGradRS_covGrad_comm_local (I := I) (M := M) g r s q S x

/-- **The rank-`r` coupled differentiated-curvature explicit split datum (posited general-rank
curvature primitive).** The contravariant-rank-`r` mirror of the rank-`0` explicit-remainder split
`exists_movingCentreDiffCurvSection_splitDivergenceDatum` (`MovingFrameDiffCurvAnchor`). For a closed
smooth Riemannian manifold `(M, g)` and a fixed contravariant rank `r` there is a *valence-dependent*
nonnegative constant `K : ℕ → ℝ` such that, at every covariant rank `s` and for every smooth
compactly-supported `(r, s)`-tensor `S`, there are smooth compactly-supported `(r, s + 1)`-tensors
`Gcd` — the **tensorial, existentially-carried** (never extension-curried) gauge-glued moving-centre
section of the differentiated-curvature contraction `∑ᵢ ∇_{Bᵢ}(R(Bᵢ, ·) S)` (the `(∇R) S` field) — and
`Grem` — the moving-frame / frame-bracket remainder — for which, writing
`Curv := pointwiseTensorCurvRS g r s S`, `Gcurv := GcurvSectionRS g r s S`, `∇S := covGrad g r s S`
and `∇²S := covGrad g r (s + 1) (covGrad g r s S)`, the **four coupled facts** hold:

* the **section split** `Curv = Gcurv + Gcd + Grem`;
* the **sum** fibre bound on the constructed section
  `rfns(Gcd)(x) ≤ (K s)² · ( rfns(∇S)(x) + rfns(S)(x) )`;
* the **sum** fibre bound on the explicit remainder
  `rfns(Grem)(x) ≤ (K s)² · ( rfns(∇²S)(x) + rfns(∇S)(x) + rfns(S)(x) )`;
* the **integrated moving-frame nullity** of that explicit remainder `⟨Grem, ∇S⟩_{L²} = 0`.

**Why this is TRUE.** This is the contravariant-rank-`r` lift of the rank-`0` coupled atom that the
rank-`0` `exists_movingCentreDiffCurvSection_splitDivergenceDatum` carries. The genuine third-order
Weitzenböck field split reads `Curv` as the pure-Riemann `R(∇S)` trace (the concrete `Gcurv`,
frame-free), the differentiated-curvature `(∇R) S` trace (the non-tensorial trace whose content the
gauge-glued tensorial `Gcd` carries — assembled tensorially from the frame-traced curvature-contraction
building block summed over a frozen orthonormal frame and partition-of-unity-glued across a finite chart
cover, the **sum** envelope absorbing the Leibniz defect against the non-tensorial trace), and the
moving-frame remainder `Grem` (`∇²S`-order in its leading term after the iterated Ricci identity
`secondCovDeriv_covGrad_antisymm_eq_riemannOp_gen` cancels the top-order `∇³S` terms, lifted to the
`(r, s)`-bundle through the slot-wise curvature formula `riemannSec_tensorCov_apply_eval` of
`TensorSlotwiseCurvatureRS`). Paired against `∇S` and summed over the `g_x`-orthonormal frame, `Grem`
telescopes into a total covariant divergence of an `∇S`-order field, whose integral over the closed
manifold vanishes. The `∇³S`-cancellation and divergence form are *false term-by-term* through
`smoothExtensionTangent`; only the tensorial frame-summed remainder is `∇²S`-order and a total
divergence. The rank-`r` gauge-glued construction, its bounds, and the integrated cross-pairing nullity
are absent sorry-free below this file (the rank-`0` carriers `genuineDiffCurvSection` / `ricTraceSection`,
their sups, and the cross-pairing value `genuineDiffCurv_crossPairing_value` are stated only at
contravariant rank `0`), so this coupled split datum is posited here as the single precise true child.
The constant is per-valence (`ℕ → ℝ`), not a single scalar (the curvature endomorphism of the
`(r, s)`-bundle is an `(r + s)`-slot derivation whose operator norm on the compact manifold grows with
the valence). Consumers transitively depend on `sorryAx`.

**Non-vacuity (the coupling rejects `Gcd = Grem = 0`).** With `Gcd = 0`, the split forces
`Grem = Curv − Gcurv`, so the nullity reads `⟨Curv − Gcurv, ∇S⟩_{L²} = 0`, i.e.
`⟨Curv, ∇S⟩_{L²} = ⟨Gcurv, ∇S⟩_{L²}`; but the genuine Weitzenböck value
`⟨Curv, ∇S⟩_{L²} = ‖Δ_∇S‖²_{L²} − ‖∇²S‖²_{L²}` is *not* carried by the pure-Riemann pairing
`⟨Gcurv, ∇S⟩_{L²}` alone on a non-flat manifold (the differentiated-curvature `(∇R) S` content is
genuinely missing), a contradiction; and the `Grem` bound with `Grem = Curv − Gcurv` would read
`rfns(Curv − Gcurv) ≤ (K s)² · (rfns(∇²S) + rfns(∇S) + rfns(S))`, *false* since the `(∇R) S` content is
genuinely `rfns(S)`-order and would not be carried. So the existential `Gcd`, `Grem` must carry the
actual third-order Weitzenböck content; the constant family is genuinely positive. -/
theorem diffCurvSplitDatumRS (g : SmoothRiemannianMetric I M) (r : ℕ) :
    ∃ K : ℕ → ℝ, (∀ s, 0 ≤ K s) ∧
      ∀ (s : ℕ) (S : SmoothCcTensor g r s),
        ∃ Gcd Grem : SmoothCcTensor g r (s + 1),
          pointwiseTensorCurvRS (I := I) (M := M) g r s S =
              GcurvSectionRS (I := I) (M := M) g r s S + Gcd + Grem ∧
          (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g r (s + 1) x (Gcd.toSection x) ≤
            K s ^ 2 *
              (riemannianFiberNormSq (I := I) (M := M) g r (s + 1) x
                  ((covGrad (I := I) (M := M) g r s S).toSection x) +
                riemannianFiberNormSq (I := I) (M := M) g r s x (S.toSection x))) ∧
          (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g r (s + 1) x (Grem.toSection x) ≤
            K s ^ 2 *
              (riemannianFiberNormSq (I := I) (M := M) g r (s + 1 + 1) x
                  ((covGrad (I := I) (M := M) g r (s + 1)
                    (covGrad (I := I) (M := M) g r s S)).toSection x) +
                riemannianFiberNormSq (I := I) (M := M) g r (s + 1) x
                    ((covGrad (I := I) (M := M) g r s S).toSection x) +
                riemannianFiberNormSq (I := I) (M := M) g r s x (S.toSection x))) ∧
          tensorL2Inner (I := I) (M := M) g r (s + 1) Grem.toFun
              (covGrad (I := I) (M := M) g r s S).toFun = 0 := by
  sorry

/-- **The rank-`r` order-`2` commutator-defect fibre order bound (posited general-rank curvature
child).** The contravariant-rank-`r` lift of the rank-`0` upstream defect fibre order bound
`exists_pointwiseTensorCurv_fiberNormSq_bound_upstream` (`MovingFrameDiffCurvAnchor`'s upstream curvature
input). For a closed smooth Riemannian manifold `(M, g)` and a fixed contravariant rank `r` there is a
valence-dependent nonnegative constant `C : ℕ → ℝ` such that, at every covariant rank `s`, every smooth
compactly-supported `(r, s)`-tensor `S` and every point `x`, the order-`2` commutator defect
`Curv S := pointwiseTensorCurvRS g r s S = Δ_∇(∇S) − ∇(Δ_∇ S)` is fibre-bounded by the order-`≤ 2`
covariant jet of `S` (`∇²S := covGrad g r (s + 1) (covGrad g r s S)`):

```
rfns(Curv S)(x) ≤ (C s)² · ( rfns(∇²S)(x) + rfns(∇S)(x) + rfns(S)(x) ).
```

**Why this is TRUE.** This is the verbatim contravariant-rank-`r` mirror of the rank-`0`
`exists_pointwiseTensorCurv_fiberNormSq_bound_upstream`. Pointwise `Curv S` is the genuine third-order
Bochner–Weitzenböck field: by the metric-trace reading of the rough Laplacian `Δ_∇ = tr_g ∘ ∇²`
(`rawTensorConnLap_eq_metricTrace2`, frame-free, rank-generic) the defect `Δ_∇(∇S) − ∇(Δ_∇ S)` is the
metric trace of the antisymmetrised second covariant derivative of `∇S` after the outer `∇` is passed
through the trace by metric compatibility (`metricTrace2_covDeriv_comm`, rank-generic), which the
third-order tensor Ricci identity `secondCovDeriv_covGrad_antisymm_eq_riemannOp_gen` exhibits as a
`riemannOp`-contraction of `(∇S, S)`, lifted to the `(r, s)`-bundle through the slot-wise curvature
formula `riemannSec_tensorCov_apply_eval` (`TensorSlotwiseCurvatureRS`). The top order surviving in the
defect is `∇²S` (the third-order field `∇³S` cancels between the two terms by the symmetry of the
third covariant derivative against the antisymmetrised commutator), with the lower orders `∇S`, `S`
entering through the curvature contraction; all curvature coefficients are absorbed uniformly over the
compact manifold into the per-order constant `(C s)²`. The rank-`r` defect fibre order is itself absent
sorry-free below this file (only the rank-`0` upstream defect bound is proven), so it is posited here as
a single precise true child. Consumers transitively depend on `sorryAx`.

**Non-vacuity.** With `C s = 0` the bound forces `rfns(Curv S)(x) = 0` pointwise, i.e. the order-`2`
commutator defect `Δ_∇(∇S) − ∇(Δ_∇ S)` vanishes; *false* on a non-flat manifold for a non-parallel `S`
(the defect is the genuine third-order curvature contraction of `S`, non-zero when `R ≠ 0` and the jet
of `S` is non-trivial). The constant family is genuinely positive. -/
theorem exists_pointwiseTensorCurvRS_fiberNormSq_bound (g : SmoothRiemannianMetric I M) (r : ℕ) :
    ∃ C : ℕ → ℝ, (∀ s, 0 ≤ C s) ∧
      ∀ (s : ℕ) (S : SmoothCcTensor g r s) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g r (s + 1) x
            ((pointwiseTensorCurvRS (I := I) (M := M) g r s S).toSection x) ≤
          C s ^ 2 *
            (riemannianFiberNormSq (I := I) (M := M) g r (s + 1 + 1) x
                ((covGrad (I := I) (M := M) g r (s + 1)
                  (covGrad (I := I) (M := M) g r s S)).toSection x) +
              riemannianFiberNormSq (I := I) (M := M) g r (s + 1) x
                  ((covGrad (I := I) (M := M) g r s S).toSection x) +
              riemannianFiberNormSq (I := I) (M := M) g r s x (S.toSection x)) := by
  classical
  -- The rank-`r` defect fibre order is the aggregation, over the coupled split datum
  -- `Curv = GcurvSectionRS + Gcd + Grem` (posit `diffCurvSplitDatumRS`), of the three sum fibre
  -- bounds: the pure-Riemann section bound `rfns(GcurvSectionRS) ≤ (c s 0)² · rfns(∇S)` (the rank-`r`
  -- pure-Riemann grid `exists_GcurvSectionRS_iteratedCovGrad_grid_bound` at gradient order `k = 0`,
  -- whose contracted range collapses to `rfns(∇S)`), the `Gcd` sum bound, and the `Grem` sum bound;
  -- the section split is opened by the fibre subadditivity `riemannianFiberNormSq_add_le` twice.
  obtain ⟨K, hK_nn, hdatum⟩ := diffCurvSplitDatumRS (I := I) (M := M) g r
  obtain ⟨cg, hcg_nn, hcg⟩ := exists_GcurvSectionRS_iteratedCovGrad_grid_bound (I := I) (M := M) g r
  refine ⟨fun s => Real.sqrt (16 * (K s) ^ 2 + 16 * (cg s 0) ^ 2),
    fun s => Real.sqrt_nonneg _, fun s S x => ?_⟩
  obtain ⟨Gcd, Grem, hsplit, hGcd, hGrem, _hnull⟩ := hdatum s S
  have hCsq : (Real.sqrt (16 * (K s) ^ 2 + 16 * (cg s 0) ^ 2)) ^ 2 =
      16 * (K s) ^ 2 + 16 * (cg s 0) ^ 2 := by
    rw [Real.sq_sqrt]; positivity
  rw [hCsq]
  -- Open the section split into the pointwise sum of three fibre values.
  have hsec : (pointwiseTensorCurvRS (I := I) (M := M) g r s S).toSection x =
      (GcurvSectionRS (I := I) (M := M) g r s S).toSection x +
        Gcd.toSection x + Grem.toSection x := by
    rw [hsplit, SmoothCcTensor.toSection_add, SmoothCcTensor.toSection_add]
    simp only [ContMDiffSection.coe_add, Pi.add_apply]
  rw [hsec]
  -- The pure-Riemann section bound off the grid at `k = 0`.
  have hgc0 := hcg s S 0 x
  simp only [iteratedCovGrad_zero, Nat.add_zero, Finset.range_one, Finset.sum_singleton,
    iteratedCovGrad_succ] at hgc0
  -- The three fibre atoms and their nonnegativity.
  set fS : ℝ := riemannianFiberNormSq (I := I) (M := M) g r s x (S.toSection x) with hfS
  set fgS : ℝ := riemannianFiberNormSq (I := I) (M := M) g r (s + 1) x
      ((covGrad (I := I) (M := M) g r s S).toSection x) with hfgS
  set fg2S : ℝ := riemannianFiberNormSq (I := I) (M := M) g r (s + 1 + 1) x
      ((covGrad (I := I) (M := M) g r (s + 1) (covGrad (I := I) (M := M) g r s S)).toSection x)
    with hfg2S
  have hfS_nn : 0 ≤ fS := riemannianFiberNormSq_nonneg (I := I) (M := M) g r s x _
  have hfgS_nn : 0 ≤ fgS := riemannianFiberNormSq_nonneg (I := I) (M := M) g r (s + 1) x _
  have hfg2S_nn : 0 ≤ fg2S := riemannianFiberNormSq_nonneg (I := I) (M := M) g r (s + 1 + 1) x _
  -- The `GcurvSectionRS`-bound (at `k = 0`), the `Gcd`-bound, and the `Grem`-bound on the same atoms.
  have hgc : riemannianFiberNormSq (I := I) (M := M) g r (s + 1) x
      ((GcurvSectionRS (I := I) (M := M) g r s S).toSection x) ≤ cg s 0 ^ 2 * fgS := hgc0
  have hgcdB := hGcd x
  have hgremB := hGrem x
  -- Two fibre-subadditivity steps over the section split.
  have hadd1 := riemannianFiberNormSq_add_le (I := I) (M := M) g r (s + 1) x
    ((GcurvSectionRS (I := I) (M := M) g r s S).toSection x + Gcd.toSection x) (Grem.toSection x)
  have hadd2 := riemannianFiberNormSq_add_le (I := I) (M := M) g r (s + 1) x
    ((GcurvSectionRS (I := I) (M := M) g r s S).toSection x) (Gcd.toSection x)
  have hGcurv_nn : 0 ≤ riemannianFiberNormSq (I := I) (M := M) g r (s + 1) x
      ((GcurvSectionRS (I := I) (M := M) g r s S).toSection x) :=
    riemannianFiberNormSq_nonneg (I := I) (M := M) g r (s + 1) x _
  have hGcd_nn : 0 ≤ riemannianFiberNormSq (I := I) (M := M) g r (s + 1) x (Gcd.toSection x) :=
    riemannianFiberNormSq_nonneg (I := I) (M := M) g r (s + 1) x _
  have hGrem_nn : 0 ≤ riemannianFiberNormSq (I := I) (M := M) g r (s + 1) x (Grem.toSection x) :=
    riemannianFiberNormSq_nonneg (I := I) (M := M) g r (s + 1) x _
  have hsum_nn : 0 ≤ riemannianFiberNormSq (I := I) (M := M) g r (s + 1) x
      ((GcurvSectionRS (I := I) (M := M) g r s S).toSection x + Gcd.toSection x) :=
    riemannianFiberNormSq_nonneg (I := I) (M := M) g r (s + 1) x _
  nlinarith [hadd1, hadd2, hgc, hgcdB, hgremB, hfS_nn, hfgS_nn, hfg2S_nn,
    hGcurv_nn, hGcd_nn, hGrem_nn, hsum_nn, sq_nonneg (K s), sq_nonneg (cg s 0),
    mul_nonneg hfgS_nn (sq_nonneg (cg s 0)), mul_nonneg hfgS_nn (sq_nonneg (K s)),
    mul_nonneg hfS_nn (sq_nonneg (K s)), mul_nonneg hfg2S_nn (sq_nonneg (K s)),
    mul_nonneg hfg2S_nn (sq_nonneg (cg s 0)), mul_nonneg hfS_nn (sq_nonneg (cg s 0))]

/-- **The rank-`r` coupled differentiated-curvature anchor: the gauge-glued `(∇R) S` section with its
sum fibre bound and the integrated moving-frame nullity (posited general-rank curvature child).** The
contravariant-rank-`r` lift of the rank-`0` deepest coupled moving-frame differentiated-curvature
content — the construction of the gauge-glued tensorial `(∇R) S` section
(`genuineDiffCurvSection`/`ricTraceSection` of `MovingFrameDiffCurvTraceSection`/`RicciTraceCarrier`),
its sum fibre bound (`exists_genuineDiffCurvSection_fiberNormSq_bound`,
`exists_ricTraceSection_fiberNormSq_bound`), and the integrated cross-pairing nullity
(`genuineDiffCurv_crossPairing_value` + `movingFrameNullity_of_genuineCrossPairingValue`,
`MovingFrameIntegratedNullity`). For a closed smooth Riemannian manifold `(M, g)` and a fixed
contravariant rank `r` there is a valence-dependent nonnegative constant `K : ℕ → ℝ` such that, at every
covariant rank `s` and for every smooth compactly-supported `(r, s)`-tensor `S`, the order-`2`
commutator defect `Curv S := pointwiseTensorCurvRS g r s S` admits a single differentiated-curvature
genuine field `Gcd : SmoothCcTensor g r (s + 1)` — the gauge-glued tensorial `(∇R) S` section over the
concrete pure-Riemann genuine section `GcurvSectionRS g r s S` (the `R(∇S)` contraction) — such that,
writing `Gcurv := GcurvSectionRS g r s S` and `∇S := covGrad g r s S`:

* `rfns(Gcd)(x) ≤ (K s)² · ( rfns(∇S)(x) + rfns(S)(x) )` — the differentiated-curvature `(∇R) S` field,
  sum-order (the gauge-glued tensorial section, the Leibniz defect against the non-tensorial
  moving-frame `(∇R) S` trace absorbed into the wider envelope);
* `⟨Curv S − Gcurv − Gcd, ∇S⟩_{L²} = 0` — the integrated moving-frame nullity of the companion remainder
  `Grem := Curv S − Gcurv − Gcd` (the moving-frame remainder is a total covariant divergence of an
  `∇S`-order field, integrating to zero against `∇S` over the closed manifold by the covariant Green
  identity; only the *integrated* pairing vanishes — the pointwise pairing carries the genuine
  non-divergence Bochner content `‖∇²S‖² − ⟨Δ_∇²(∇S), S⟩`).

**Why this is TRUE.** This is the contravariant-rank-`r` lift of the rank-`0` coupled anchor that the
rank-`0` `exists_movingCentreDiffCurvSection_splitDivergenceDatum` is built from. The
differentiated-curvature contraction `∑ᵢ ∇_{Bᵢ}(R(Bᵢ, ·) S)` is the *tensorial* gauge-glued smooth
section `Gcd`, assembled tensorially from the frame-traced curvature-contraction building block summed
over a frozen orthonormal frame and partition-of-unity-glued across a finite chart cover (the
frozen-frame fibre value agreeing on overlaps because the contraction reads only the *values* of the
frame), with fibre norm uniformly bounded by the **sum** envelope `rfns(∇S) + rfns(S)` (absorbing the
Leibniz defect between the gauge-glued tensorial section and the genuine non-tensorial moving-frame
`(∇R) S` trace). The companion remainder `Grem := Curv S − Gcurv − Gcd`, paired against `∇S` and summed
over the `g_x`-orthonormal frame, telescopes into a total covariant divergence of an `∇S`-order field,
whose integral over the closed manifold vanishes. The `∇³S`-cancellation and divergence form are *false
term-by-term* through `smoothExtensionTangent`; only the tensorial frame-summed remainder is `∇²S`-order
and a total divergence — the irreducible coupled moving-frame content. The rank-`r` gauge-glued
construction, its bound, and the cross-pairing nullity are all absent sorry-free below this file (the
rank-`0` carriers, sups and cross-pairing are stated only at contravariant rank `0`), so this coupled
anchor is posited here as a single precise true child. The constant is per-valence (`ℕ → ℝ`), not a
single scalar (the curvature endomorphism of the `(r, s)`-bundle is an `(r + s)`-slot derivation whose
operator norm on the compact manifold grows with the valence). Consumers transitively depend on
`sorryAx`.

**Non-vacuity (the coupling rejects `Gcd = 0`).** The bound alone does *not* reject `Gcd = 0`, but the
COUPLING does: with `Gcd = 0`, the nullity reads `⟨Curv S − Gcurv, ∇S⟩_{L²} = 0`, i.e. the pure-Riemann
pairing carries the entire Weitzenböck value `⟨Curv S, ∇S⟩_{L²} = ‖Δ_∇S‖²_{L²} − ‖∇²S‖²_{L²}`, which
fails on a non-flat manifold (the differentiated-curvature `(∇R) S` content is genuinely missing). So
the existential `Gcd` must carry the actual differentiated-curvature content; the constant family is
genuinely positive. -/
theorem exists_diffCurvSectionRS_anchor (g : SmoothRiemannianMetric I M) (r : ℕ) :
    ∃ K : ℕ → ℝ, (∀ s, 0 ≤ K s) ∧
      ∀ (s : ℕ) (S : SmoothCcTensor g r s),
        ∃ Gcd : SmoothCcTensor g r (s + 1),
          (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g r (s + 1) x (Gcd.toSection x) ≤
            K s ^ 2 *
              (riemannianFiberNormSq (I := I) (M := M) g r (s + 1) x
                  ((covGrad (I := I) (M := M) g r s S).toSection x) +
                riemannianFiberNormSq (I := I) (M := M) g r s x (S.toSection x))) ∧
          tensorL2Inner (I := I) (M := M) g r (s + 1)
              (pointwiseTensorCurvRS (I := I) (M := M) g r s S -
                GcurvSectionRS (I := I) (M := M) g r s S - Gcd).toFun
              (covGrad (I := I) (M := M) g r s S).toFun = 0 := by
  classical
  -- The coupled anchor reads off the coupled split datum `diffCurvSplitDatumRS`: the existential `Gcd`,
  -- its sum fibre bound, and the integrated nullity all transport. The literal-subtraction remainder
  -- `Curv − GcurvSectionRS − Gcd` equals the explicit `Grem` of the split (`abel`), so the nullity
  -- carried about `Grem` transports verbatim. (The companion remainder's order bound is not part of
  -- this anchor's conclusion — it is carried separately by `diffCurvSplitDatumRS`.)
  obtain ⟨K, hK_nn, hdatum⟩ := diffCurvSplitDatumRS (I := I) (M := M) g r
  refine ⟨K, hK_nn, fun s S => ?_⟩
  obtain ⟨Gcd, Grem, hsplit, hGcd, _hGrem, hnull⟩ := hdatum s S
  have hGrem_eq : Grem = pointwiseTensorCurvRS (I := I) (M := M) g r s S -
      GcurvSectionRS (I := I) (M := M) g r s S - Gcd := by
    rw [hsplit]; abel
  refine ⟨Gcd, hGcd, ?_⟩
  rw [show (pointwiseTensorCurvRS (I := I) (M := M) g r s S -
      GcurvSectionRS (I := I) (M := M) g r s S - Gcd).toFun = Grem.toFun from by rw [hGrem_eq]]
  exact hnull

/-- **The rank-`r` proportional pure-Riemann genuine-section fibre bound (posited general-rank
curvature child).** The contravariant-rank-`r` lift of the rank-`0` proportional pure-Riemann section
bound `GcurvSection_fiberNormSq_le_covGrad` (`MovingFrameGenuineSectionOrderDivergence`, *sorry-free*
at rank `0`). For a closed smooth Riemannian manifold `(M, g)` and a fixed contravariant rank `r`
there is a *valence-dependent* nonnegative constant `C₁ : ℕ → ℝ` such that, at every covariant rank
`s`, for every smooth compactly-supported `(r, s)`-tensor `S`, and at *every point* `x`, the intrinsic
fibre norm of the concrete moving-centre pure-Riemann genuine curvature section `GcurvSectionRS g r s
S` (the slot-`0` assembly of the *tensorial* moving-frame trace `∑ᵢ R(Bᵢ, ·)(∇_{Bᵢ} S)`, the `R(∇S)`
contraction) is bounded by `(C₁ s)²` times the intrinsic fibre norm of `∇S := covGrad g r s S`:

```
rfns(GcurvSectionRS g r s S)(x) ≤ (C₁ s)² · rfns(∇S)(x).
```

**Why this is TRUE.** This is the verbatim contravariant-rank-`r` mirror of the rank-`0`
`GcurvSection_fiberNormSq_le_covGrad`. The pure-Riemann genuine section `GcurvSectionRS g r s S` is the
slot-`0` assembly of the *tensorial* moving-frame trace `∑ᵢ R(Bᵢ, ·)(∇_{Bᵢ} S)`: each summand is a
bundled curvature operator `riemannOp (tensorCov g r s) x (Bᵢ x) · (∇_{Bᵢ} S(x))` applied to the
gradient field, fibre-bounded proportional to `rfns(∇S)` by the rank-`r` analogue of the proportional
curvature sup `riemannianFiberNormSq_riemannOp_covGrad_uniform_proportional_bound` (the curvature
operator `g`-norm sup over the compact manifold), summed over the `g_x`-orthonormal frame. The
rank-`r` proportional curvature sup is itself absent sorry-free below this file (only the rank-`0`
proportional sup is proven), so this rank-`r` proportional section bound is posited here as the single
precise true child. Consumers transitively depend on `sorryAx`.

**Non-vacuity.** A zero envelope `C₁ s = 0` would force `rfns(GcurvSectionRS g r s S)(x) = 0`
pointwise, but its fibre value carries the pure-Riemann contraction `∑ᵢ R(Bᵢ, ·)(∇_{Bᵢ} S)`, genuinely
non-zero when `R ≠ 0` and `∇S ≠ 0` on a non-flat manifold (`genuineCurvPureRFibRS_contMDiff`, never
the zero section); so the bound genuinely envelopes the per-point curvature operator norm and the
constant family is genuinely positive. -/
theorem GcurvSectionRS_fiberNormSq_le_covGrad
    (g : SmoothRiemannianMetric I M) (r : ℕ) :
    ∃ C₁ : ℕ → ℝ, (∀ s, 0 ≤ C₁ s) ∧
      ∀ (s : ℕ) (S : SmoothCcTensor g r s) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g r (s + 1) x
            ((GcurvSectionRS (I := I) (M := M) g r s S).toSection x) ≤
          C₁ s ^ 2 *
            riemannianFiberNormSq (I := I) (M := M) g r (s + 1) x
              ((covGrad (I := I) (M := M) g r s S).toSection x) := by
  classical
  -- The proportional section bound is the rank-`r` pure-Riemann grid at gradient order `k = 0`: there
  -- `∇^0(GcurvSectionRS) = GcurvSectionRS` and the contracted-order window `∑_{i < 1} rfns(∇^{i+1} S)`
  -- collapses to the single term `rfns(∇^1 S) = rfns(∇S)`, with constant `C₁ s := c s 0`.
  obtain ⟨c, hc_nn, hgrid⟩ := exists_GcurvSectionRS_iteratedCovGrad_grid_bound (I := I) (M := M) g r
  refine ⟨fun s => c s 0, fun s => hc_nn s 0, fun s S x => ?_⟩
  have hg0 := hgrid s S 0 x
  simpa only [iteratedCovGrad_zero, Nat.add_zero, Finset.range_one, Finset.sum_singleton,
    iteratedCovGrad_succ] using hg0

/-- **The rank-`r` coupled differentiated-curvature divergence datum (posited general-rank curvature
child).** The contravariant-rank-`r` lift of the rank-`0` coupled differentiated-curvature primitive
`exists_movingCentreDiffCurvSection_divergenceDatum` (`MovingFrameDiffCurvAnchor`). For a closed smooth
Riemannian manifold `(M, g)` and a fixed contravariant rank `r` there is a *valence-dependent*
nonnegative constant `K : ℕ → ℝ` such that, at every covariant rank `s` and for every smooth
compactly-supported `(r, s)`-tensor `S`, the order-`2` commutator defect
`Curv S := pointwiseTensorCurvRS g r s S` admits a single differentiated-curvature genuine field
`Gcd : SmoothCcTensor g r (s + 1)` — the gauge-glued tensorial `(∇R) S` section over the concrete
pure-Riemann genuine section `GcurvSectionRS g r s S` (the `R(∇S)` contraction) — such that, writing
the moving-frame remainder as the literal subtraction `Grem := Curv S − GcurvSectionRS g r s S − Gcd`:

* `rfns(Gcd)(x) ≤ (K s)² · (rfns(∇S)(x) + rfns(S)(x))` — the differentiated-curvature `(∇R) S` field,
  sum-order (the gauge-glued tensorial section, the Leibniz defect against the non-tensorial
  moving-frame `(∇R) S` trace absorbed into the wider envelope);
* `rfns(Grem)(x) ≤ (K s)² · (rfns(∇²S)(x) + rfns(∇S)(x) + rfns(S)(x))` — the moving-frame /
  frame-bracket remainder, `rfns(∇²S)`-order in its leading term after the third-order Weitzenböck
  cancellation of the top-order `∇³S` terms by the iterated Ricci identity
  (`secondCovDeriv_covGrad_antisymm_eq_riemannOp_gen`, lifted to the `(r, s)`-bundle through the
  slot-wise curvature formula `riemannSec_tensorCov_apply_eval` of `TensorSlotwiseCurvatureRS`);
* `⟨Grem, ∇S⟩_{L²} = 0` — the integrated moving-frame nullity (the moving-frame remainder is a total
  covariant divergence of an `∇S`-order field, integrating to zero against `∇S` over the closed
  manifold by the covariant Green identity).

**Why this is TRUE.** This is the contravariant-rank-`r` lift of the rank-`0`
`exists_movingCentreDiffCurvSection_divergenceDatum`: the differentiated-curvature contraction
`R(Bᵢ, ·) S` followed by the covariant gradient along `Bᵢ` is the *tensorial* gauge-glued smooth
section `Gcd`, whose fibre norm is uniformly bounded by the **sum** envelope `rfns(∇S) + rfns(S)`
(absorbing the Leibniz defect between the gauge-glued tensorial section and the genuine non-tensorial
moving-frame `(∇R) S` trace). The companion remainder `Grem := Curv S − GcurvSectionRS g r s S − Gcd`
is the bracket field plus the Leibniz defect, `rfns(∇²S)`-order in its leading term after the iterated
Ricci identity cancels the top-order `∇³S` terms; paired against `∇S` and summed over the
`g_x`-orthonormal frame it telescopes into a total covariant divergence of an `∇S`-order field, whose
integral over the closed manifold vanishes. The `∇³S`-cancellation and divergence form are *false
term-by-term* through `smoothExtensionTangent`; only the tensorial frame-summed remainder is
`∇²S`-order and a total divergence — the irreducible coupled moving-frame content. The rank-`r`
moving-frame curvature-endomorphism content is absent sorry-free below this file (the rank-`0` atom and
the rank-`0` proportional sups are stated only at contravariant rank `0`), so it is posited here as the
single coupled differentiated-curvature primitive. The constant is per-valence (`ℕ → ℝ`), not a single
scalar (the curvature endomorphism of the `(r, s)`-bundle is an `(r + s)`-slot derivation whose
operator norm on the compact manifold grows with the valence), so this is NOT the unsatisfiable
single-const-∀s shape. Consumers transitively depend on `sorryAx`.

**Non-vacuity (the coupling rejects `Gcd = 0`).** The bound alone does *not* reject `Gcd = 0`, but
the COUPLING does: with `Gcd = 0`, the nullity reads `⟨Curv S − GcurvSectionRS, ∇S⟩_{L²} = 0`, i.e.
the pure-Riemann pairing carries the entire Weitzenböck value, which fails on a non-flat manifold (the
differentiated-curvature `(∇R) S` content is genuinely missing); and the `Grem` bound with `Gcd = 0`
would read `rfns(Curv S − GcurvSectionRS) ≤ (K s)² · (rfns(∇²S) + rfns(∇S) + rfns(S))`, *false* since
the `(∇R) S` content is genuinely `rfns(S)`-order and would not be carried. So the existential `Gcd`
must carry the actual differentiated-curvature content; the constant family is genuinely positive. -/
theorem exists_movingCentreDiffCurvSectionRS_divergenceDatum
    (g : SmoothRiemannianMetric I M) (r : ℕ) :
    ∃ K : ℕ → ℝ, (∀ s, 0 ≤ K s) ∧
      ∀ (s : ℕ) (S : SmoothCcTensor g r s),
        ∃ Gcd : SmoothCcTensor g r (s + 1),
          (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g r (s + 1) x (Gcd.toSection x) ≤
            K s ^ 2 *
              (riemannianFiberNormSq (I := I) (M := M) g r (s + 1) x
                  ((covGrad (I := I) (M := M) g r s S).toSection x) +
                riemannianFiberNormSq (I := I) (M := M) g r s x (S.toSection x))) ∧
          (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g r (s + 1) x
              ((pointwiseTensorCurvRS (I := I) (M := M) g r s S -
                  GcurvSectionRS (I := I) (M := M) g r s S - Gcd).toSection x) ≤
            K s ^ 2 *
              (riemannianFiberNormSq (I := I) (M := M) g r (s + 1 + 1) x
                  ((covGrad (I := I) (M := M) g r (s + 1)
                    (covGrad (I := I) (M := M) g r s S)).toSection x) +
                riemannianFiberNormSq (I := I) (M := M) g r (s + 1) x
                    ((covGrad (I := I) (M := M) g r s S).toSection x) +
                riemannianFiberNormSq (I := I) (M := M) g r s x (S.toSection x))) ∧
          tensorL2Inner (I := I) (M := M) g r (s + 1)
              (pointwiseTensorCurvRS (I := I) (M := M) g r s S -
                GcurvSectionRS (I := I) (M := M) g r s S - Gcd).toFun
              (covGrad (I := I) (M := M) g r s S).toFun = 0 := by
  classical
  -- The existential `Gcd`, its sum bound, and the integrated nullity come from the rank-`r` coupled
  -- differentiated-curvature anchor; the companion remainder's order bound is *derived* from the
  -- rank-`r` defect fibre order (`Curv`), the proven rank-`r` proportional pure-Riemann section bound
  -- (the `Gcurv` bound, off the grid at `k = 0`), and the anchor's `Gcd` bound by the fibre-norm
  -- triangle. The three valence constants are merged into one per-valence family.
  obtain ⟨C₁, hC₁_nn, hScurv⟩ := GcurvSectionRS_fiberNormSq_le_covGrad (I := I) (M := M) g r
  obtain ⟨Ccurv, hCcurv_nn, hCcurv⟩ := exists_pointwiseTensorCurvRS_fiberNormSq_bound (I := I) (M := M) g r
  obtain ⟨K₀, hK₀_nn, hanchor⟩ := exists_diffCurvSectionRS_anchor (I := I) (M := M) g r
  refine ⟨fun s => Real.sqrt (8 * (K₀ s) ^ 2 + 8 * (Ccurv s) ^ 2 + 8 * (C₁ s) ^ 2),
    fun s => Real.sqrt_nonneg _, fun s S => ?_⟩
  obtain ⟨Gcd, hGcd, hnull⟩ := hanchor s S
  have hKsq : (Real.sqrt (8 * (K₀ s) ^ 2 + 8 * (Ccurv s) ^ 2 + 8 * (C₁ s) ^ 2)) ^ 2 =
      8 * (K₀ s) ^ 2 + 8 * (Ccurv s) ^ 2 + 8 * (C₁ s) ^ 2 := by
    rw [Real.sq_sqrt]; positivity
  refine ⟨Gcd, fun x => ?_, fun x => ?_, hnull⟩
  · -- Conjunct `(1)`: weaken the anchor's `Gcd` sum bound's constant `K₀ s` to the merged family.
    refine (hGcd x).trans ?_
    rw [hKsq]
    have hfgS_nn : 0 ≤ riemannianFiberNormSq (I := I) (M := M) g r (s + 1) x
        ((covGrad (I := I) (M := M) g r s S).toSection x) :=
      riemannianFiberNormSq_nonneg (I := I) (M := M) g r (s + 1) x _
    have hfS_nn : 0 ≤ riemannianFiberNormSq (I := I) (M := M) g r s x (S.toSection x) :=
      riemannianFiberNormSq_nonneg (I := I) (M := M) g r s x _
    nlinarith [hfgS_nn, hfS_nn, sq_nonneg (K₀ s), sq_nonneg (Ccurv s), sq_nonneg (C₁ s),
      mul_nonneg (add_nonneg hfgS_nn hfS_nn) (sq_nonneg (Ccurv s)),
      mul_nonneg (add_nonneg hfgS_nn hfS_nn) (sq_nonneg (C₁ s))]
  · -- Conjunct `(2)`: the companion remainder order bound, derived by the fibre-norm triangle over the
    -- defect order (`Curv`), the proportional pure-Riemann section bound (`Gcurv`), and the `Gcd` bound.
    -- `Curv − Gcurv − Gcd = (Curv − Gcurv) − Gcd`; split the section into the pointwise difference.
    have hsec : (pointwiseTensorCurvRS (I := I) (M := M) g r s S -
          GcurvSectionRS (I := I) (M := M) g r s S - Gcd).toSection x =
        ((pointwiseTensorCurvRS (I := I) (M := M) g r s S).toSection x -
            (GcurvSectionRS (I := I) (M := M) g r s S).toSection x) - Gcd.toSection x := by
      rw [SmoothCcTensor.toSection_sub, SmoothCcTensor.toSection_sub]; rfl
    have hsub1 := riemannianFiberNormSq_sub_le (I := I) (M := M) g r (s + 1) x
      ((pointwiseTensorCurvRS (I := I) (M := M) g r s S).toSection x -
          (GcurvSectionRS (I := I) (M := M) g r s S).toSection x) (Gcd.toSection x)
    have hsub2 := riemannianFiberNormSq_sub_le (I := I) (M := M) g r (s + 1) x
      ((pointwiseTensorCurvRS (I := I) (M := M) g r s S).toSection x)
      ((GcurvSectionRS (I := I) (M := M) g r s S).toSection x)
    rw [hsec]
    -- The defect fibre order, the proportional pure-Riemann section bound, and the anchor's `Gcd` bound.
    have hCurvB := hCcurv s S x
    have hgcurvB := hScurv s S x
    have hgcB := hGcd x
    -- Fold the squared fibre norms (the goal RHS and all hypotheses use the same atoms after `set`).
    rw [hKsq]
    set fS : ℝ := riemannianFiberNormSq (I := I) (M := M) g r s x (S.toSection x) with hfS
    set fgS : ℝ := riemannianFiberNormSq (I := I) (M := M) g r (s + 1) x
        ((covGrad (I := I) (M := M) g r s S).toSection x) with hfgS
    set fg2S : ℝ := riemannianFiberNormSq (I := I) (M := M) g r (s + 1 + 1) x
        ((covGrad (I := I) (M := M) g r (s + 1) (covGrad (I := I) (M := M) g r s S)).toSection x)
      with hfg2S
    set fCurv : ℝ := riemannianFiberNormSq (I := I) (M := M) g r (s + 1) x
        ((pointwiseTensorCurvRS (I := I) (M := M) g r s S).toSection x) with hfCurv
    set fGcurv : ℝ := riemannianFiberNormSq (I := I) (M := M) g r (s + 1) x
        ((GcurvSectionRS (I := I) (M := M) g r s S).toSection x) with hfGcurv
    set fGcd : ℝ := riemannianFiberNormSq (I := I) (M := M) g r (s + 1) x (Gcd.toSection x) with hfGcd
    have hfS_nn : 0 ≤ fS := riemannianFiberNormSq_nonneg (I := I) (M := M) g r s x _
    have hfgS_nn : 0 ≤ fgS := riemannianFiberNormSq_nonneg (I := I) (M := M) g r (s + 1) x _
    have hfg2S_nn : 0 ≤ fg2S := riemannianFiberNormSq_nonneg (I := I) (M := M) g r (s + 1 + 1) x _
    have hfCurv_nn : 0 ≤ fCurv := riemannianFiberNormSq_nonneg (I := I) (M := M) g r (s + 1) x _
    have hfGcurv_nn : 0 ≤ fGcurv := riemannianFiberNormSq_nonneg (I := I) (M := M) g r (s + 1) x _
    have hfGcd_nn : 0 ≤ fGcd := riemannianFiberNormSq_nonneg (I := I) (M := M) g r (s + 1) x _
    nlinarith [hsub1, hsub2, hCurvB, hgcurvB, hgcB, hfS_nn, hfgS_nn, hfg2S_nn, hfCurv_nn, hfGcurv_nn,
      hfGcd_nn, sq_nonneg (K₀ s), sq_nonneg (Ccurv s), sq_nonneg (C₁ s),
      mul_nonneg hfg2S_nn (sq_nonneg (Ccurv s)), mul_nonneg hfgS_nn (sq_nonneg (Ccurv s)),
      mul_nonneg hfS_nn (sq_nonneg (Ccurv s)), mul_nonneg hfg2S_nn (sq_nonneg (C₁ s)),
      mul_nonneg hfgS_nn (sq_nonneg (C₁ s)), mul_nonneg hfS_nn (sq_nonneg (C₁ s)),
      mul_nonneg hfg2S_nn (sq_nonneg (K₀ s)), mul_nonneg hfgS_nn (sq_nonneg (K₀ s)),
      mul_nonneg hfS_nn (sq_nonneg (K₀ s))]

/-- **The moving-centre differentiated-curvature fibre bound at contravariant rank `r` (the deepest
coupled curvature atom).** The rank-`r` lift of the rank-`0` deepest moving-frame curvature atom
`exists_movingCentreDiffCurvSection_fiberNormSq_bound`
(`MovingFrameDifferentiatedCurvatureSection`), with the proportional pure-Riemann section bound folded
in (the rank-`r` analogue of `GcurvSection_fiberNormSq_le_covGrad` is itself absent — it needs the
absent rank-`r` proportional curvature sup
`riemannianFiberNormSq_riemannOp_covGrad_uniform_proportional_bound`, stated only at rank `0`). For a
closed smooth Riemannian manifold `(M, g)` there is a *valence-dependent* nonnegative constant
`K : ℕ → ℝ` such that, at every covariant rank `s` and for every smooth compactly-supported
`(r, s)`-tensor `S`, the order-`2` commutator defect `Curv S := pointwiseTensorCurvRS g r s S` admits a
single differentiated-curvature genuine field `Gcd : SmoothCcTensor g r (s + 1)` — the gauge-glued
tensorial `(∇R) S` section over the concrete pure-Riemann genuine section `GcurvSectionRS g r s S` (the
`R(∇S)` contraction) — such that, writing the moving-frame remainder as the literal subtraction
`Grem := Curv S − GcurvSectionRS g r s S − Gcd`:

* `rfns(GcurvSectionRS)(x) ≤ (K s)² · rfns(∇S)(x)` — the pure-`R` field, genuinely `rfns(∇S)`-order
  (each summand is a bundled curvature operator `riemannOp (tensorCov g r (s + 1)) x Bᵢ · (∇S(x))`,
  fibre-bounded proportional to `rfns(∇S)` by the rank-`r` proportional curvature sup, summed over the
  orthonormal frame);
* `rfns(Gcd)(x) ≤ (K s)² · (rfns(∇S)(x) + rfns(S)(x))` — the differentiated-curvature `(∇R) S` field,
  sum-order (the gauge-glued tensorial section, the Leibniz defect against the non-tensorial
  moving-frame `(∇R) S` trace absorbed into the wider envelope);
* `rfns(Grem)(x) ≤ (K s)² · (rfns(∇²S)(x) + rfns(∇S)(x) + rfns(S)(x))` — the moving-frame /
  frame-bracket remainder, `rfns(∇²S)`-order in its leading term after the third-order Weitzenböck
  cancellation of the top-order `∇³S` terms by the iterated Ricci identity
  (`secondCovDeriv_covGrad_antisymm_eq_riemannOp_gen`, lifted to the `(r, s)`-bundle through the
  slot-wise curvature formula `riemannSec_tensorCov_apply_eval` of `TensorSlotwiseCurvatureRS`), the
  lower-order Leibniz-defect terms in the sum;
* `⟨Grem, ∇S⟩_{L²} = 0` — the integrated moving-frame nullity (the moving-frame remainder is a total
  covariant divergence of an `∇S`-order field, integrating to zero against `∇S` over the closed
  manifold by the covariant Green identity).

**T1 (integrated-only).** Only the *integrated* nullity `⟨Grem, ∇S⟩_{L²} = 0` and the *summed* fibre
bounds are sound; the per-point / per-direction moving-frame remainder is non-tensorial
(chartJ-unbounded through `smoothExtensionTangent`) and a pointwise-divergence form would be
false-as-stated. The pointwise pairing is *not* zero — it carries the genuine non-divergence Bochner
content `‖∇²S‖² − ⟨Δ_∇²(∇S), S⟩`.

**Non-vacuity.** The zero witness `Gcd = 0` is rejected by the *coupling*: with `Gcd = 0` the nullity
reads `⟨Curv S − GcurvSectionRS, ∇S⟩_{L²} = 0`, i.e. the pure-Riemann pairing carries the entire
Weitzenböck value, which fails on a non-flat manifold (the differentiated-curvature `(∇R) S` content is
genuinely missing); and the `Grem` bound with `Gcd = 0` reads
`rfns(Curv S − GcurvSectionRS) ≤ (K s)² · (rfns(∇²S) + rfns(∇S) + rfns(S))`, *false* since the `(∇R) S`
content is genuinely `rfns(S)`-order and would not be carried. So the existential `Gcd` must carry the
actual differentiated-curvature content; the constant family is genuinely positive.

This genuinely general-rank `(r, s)` moving-frame curvature-endomorphism content is absent from the
library (the rank-`0` atom, the rank-`0` proportional curvature sups, and the rank-`0` tri-split are all
stated only at contravariant rank `0`), so it is posited here as **one** deepest coupled curvature
atom — exactly the rank-`r` lift of the rank-`0` deepest atom
`exists_movingCentreDiffCurvSection_fiberNormSq_bound`, with the proportional pure-Riemann section bound
folded in. The constant is per-valence (`ℕ → ℝ`), not a single scalar (the curvature endomorphism of
the `(r, s)`-bundle is an `(r + s)`-slot derivation whose operator norm on the compact manifold grows
with the valence), so this is NOT the unsatisfiable single-const-∀s shape.

The body is `sorry`; consumers transitively depend on `sorryAx`. -/
theorem exists_movingCentreDiffCurvSectionRS_fiberNormSq_bound
    (g : SmoothRiemannianMetric I M) (r : ℕ) :
    ∃ K : ℕ → ℝ, (∀ s, 0 ≤ K s) ∧
      ∀ (s : ℕ) (S : SmoothCcTensor g r s),
        ∃ Gcd : SmoothCcTensor g r (s + 1),
          (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g r (s + 1) x
              ((GcurvSectionRS (I := I) (M := M) g r s S).toSection x) ≤
            K s ^ 2 *
              riemannianFiberNormSq (I := I) (M := M) g r (s + 1) x
                ((covGrad (I := I) (M := M) g r s S).toSection x)) ∧
          (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g r (s + 1) x (Gcd.toSection x) ≤
            K s ^ 2 *
              (riemannianFiberNormSq (I := I) (M := M) g r (s + 1) x
                  ((covGrad (I := I) (M := M) g r s S).toSection x) +
                riemannianFiberNormSq (I := I) (M := M) g r s x (S.toSection x))) ∧
          (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g r (s + 1) x
              ((pointwiseTensorCurvRS (I := I) (M := M) g r s S -
                  GcurvSectionRS (I := I) (M := M) g r s S - Gcd).toSection x) ≤
            K s ^ 2 *
              (riemannianFiberNormSq (I := I) (M := M) g r (s + 1 + 1) x
                  ((covGrad (I := I) (M := M) g r (s + 1)
                    (covGrad (I := I) (M := M) g r s S)).toSection x) +
                riemannianFiberNormSq (I := I) (M := M) g r (s + 1) x
                    ((covGrad (I := I) (M := M) g r s S).toSection x) +
                riemannianFiberNormSq (I := I) (M := M) g r s x (S.toSection x))) ∧
          tensorL2Inner (I := I) (M := M) g r (s + 1)
              (pointwiseTensorCurvRS (I := I) (M := M) g r s S -
                GcurvSectionRS (I := I) (M := M) g r s S - Gcd).toFun
              (covGrad (I := I) (M := M) g r s S).toFun = 0 := by
  classical
  -- The proportional pure-Riemann section bound (conjunct `(1)`) is the rank-`r` posited proportional
  -- child; the existential `Gcd` with its sum bound, the companion remainder's order bound, and the
  -- integrated nullity (conjuncts `(2)`–`(4)`) come from the rank-`r` posited coupled divergence
  -- datum. Combine the two valence constants into a single per-valence family by `max`.
  obtain ⟨C₁, hC₁_nn, hScurv⟩ := GcurvSectionRS_fiberNormSq_le_covGrad (I := I) (M := M) g r
  obtain ⟨K, hK_nn, hdatum⟩ := exists_movingCentreDiffCurvSectionRS_divergenceDatum (I := I) (M := M) g r
  refine ⟨fun s => max (C₁ s) (K s), fun s => le_trans (hC₁_nn s) (le_max_left _ _), fun s S => ?_⟩
  obtain ⟨Gcd, hGcd, hGrem, hnull⟩ := hdatum s S
  refine ⟨Gcd, fun x => ?_, fun x => ?_, fun x => ?_, hnull⟩
  · -- Conjunct `(1)`: weaken the proportional bound's constant `C₁ s` to `max (C₁ s) (K s)`.
    refine (hScurv s S x).trans ?_
    refine mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (hC₁_nn s) (le_max_left _ _) 2) ?_
    exact riemannianFiberNormSq_nonneg (I := I) (M := M) g r (s + 1) x _
  · -- Conjunct `(2)`: weaken the `Gcd` sum bound's constant `K s` to `max (C₁ s) (K s)`.
    refine (hGcd x).trans ?_
    refine mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (hK_nn s) (le_max_right _ _) 2) ?_
    exact add_nonneg (riemannianFiberNormSq_nonneg (I := I) (M := M) g r (s + 1) x _)
      (riemannianFiberNormSq_nonneg (I := I) (M := M) g r s x _)
  · -- Conjunct `(3)`: weaken the remainder order bound's constant `K s` to `max (C₁ s) (K s)`.
    refine (hGrem x).trans ?_
    refine mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (hK_nn s) (le_max_right _ _) 2) ?_
    exact add_nonneg (add_nonneg
      (riemannianFiberNormSq_nonneg (I := I) (M := M) g r (s + 1 + 1) x _)
      (riemannianFiberNormSq_nonneg (I := I) (M := M) g r (s + 1) x _))
      (riemannianFiberNormSq_nonneg (I := I) (M := M) g r s x _)

/-- **The deepest moving-frame curvature primitive at contravariant rank `r` (posited general-rank
curvature child).** For a closed smooth Riemannian manifold `(M, g)` there is a *valence-dependent*
nonnegative constant `Cper : ℕ → ℝ` such that, at every covariant rank `s` and for every smooth
compactly-supported `(r, s)`-tensor `S`, the order-`2` commutator defect
`Curv S := pointwiseTensorCurvRS g r s S` splits, over the concrete pure-Riemann genuine section
`GcurvSectionRS g r s S` (the slot-`0` assembly of the *tensorial* pure-Riemann trace
`∑ᵢ R(Bᵢ, ·)(∇_{Bᵢ} S)`, the `R(∇S)` contraction), into a differentiated-curvature field `Gcd` and a
moving-frame remainder field `Grem`, both smooth compactly-supported `(r, s + 1)`-tensors carried
**existentially** (never extension-curried):
```
Curv S = GcurvSectionRS g r s S + Gcd + Grem,
```
with the integrated nullity `⟨Grem, ∇S⟩_{L²} = 0` and the three intrinsic **sum** fibre bounds
(`∇S := covGrad g r s S`, `∇²S := covGrad g r (s + 1) (covGrad g r s S)`):

* `rfns(GcurvSectionRS)(x) ≤ (Cper s)² · rfns(∇S)(x)` — the pure-`R` field, genuinely `rfns(∇S)`-order
  (the tensorial trace bound: each summand is a bundled curvature operator
  `riemannOp (tensorCov g r (s + 1)) x Bᵢ · (∇S(x))`, fibre-bounded proportional to `rfns(∇S)` by the
  rank-`r` analogue of the proportional curvature sup
  `riemannianFiberNormSq_riemannOp_covGrad_uniform_proportional_bound`, summed over the orthonormal
  frame);
* `rfns(Gcd)(x) ≤ (Cper s)² · (rfns(∇S)(x) + rfns(S)(x))` — the differentiated-curvature contraction
  `(∇R) S`, packaged as the gauge-glued tensorial section; the **sum** order absorbs the Leibniz defect
  between the gauge-glued tensorial section and the non-tensorial moving-frame `(∇R) S` trace;
* `rfns(Grem)(x) ≤ (Cper s)² · (rfns(∇²S)(x) + rfns(∇S)(x) + rfns(S)(x))` — the moving-frame /
  frame-bracket remainder, `rfns(∇²S)`-order in its leading term after the third-order Weitzenböck
  cancellation of the top-order `∇³S` terms by the iterated Ricci identity, with the lower-order
  Leibniz-defect terms in the sum.

**Why this is TRUE.** This is the contravariant-rank-`r` lift of the rank-`0` deepest moving-frame
curvature node `exists_pointwiseTensorCurv_genuineTriSplit_divergence`
(`MovingFrameGenuineSectionOrderDivergence`, proven glue over the posited coupled
differentiated-curvature atom, transiting `sorryAx`) together with the proportional pure-Riemann
section bound `GcurvSection_fiberNormSq_le_covGrad` (`MovingFrameGenuineSectionOrderDivergence`,
*sorry-free* at rank `0`). Fibrewise, by the rank-generic frame-sum representation of the defect (the
Ricci identity on the gradient field, `secondCovDeriv_covGrad_antisymm_eq_riemannOp_gen`, lifts to the
`(r, s)`-bundle through the slot-wise curvature formula `riemannSec_tensorCov_apply_eval`
(`TensorSlotwiseCurvatureRS`) reducing every `(r, s + 1)`-curvature read to the proven `(0, t)`-curvature
reads), `Curv S` splits as the pure-Riemann contraction `GcurvSectionRS` plus the
differentiated-curvature contraction `Gcd` plus the moving-frame / frame-bracket remainder `Grem`. The
pure-`R` field is `rfns(∇S)`-order; the `(∇R) S` field is sum-order; the remainder's top-order `∇³S`
terms cancel by the iterated Ricci identity, leaving an `∇²S`-order tensorial field, *false
term-by-term* through `smoothExtensionTangent`, only the tensorial sum being order-controlled. The
remainder is additionally a total covariant divergence of an `∇S`-order field, so its `L²` pairing
against `∇S` vanishes by the covariant Green identity (the *pointwise* pairing is non-zero, carrying
`‖∇²S‖² − ⟨Δ_∇²(∇S), S⟩`, so only the *integrated* nullity holds — a pointwise-divergence form would be
false-as-stated).

This genuinely general-rank `(r, s)` moving-frame curvature-endomorphism content is absent from the
library (the rank-`0` proportional curvature sups and the rank-`0` tri-split are stated only at
contravariant rank `0`), so it is posited here as **one** deepest curvature primitive — exactly
mirroring the rank-`0` deepest node, with the proportional pure-Riemann section bound folded in (it too
needs the absent rank-`r` proportional sup). The constant is per-valence (`ℕ → ℝ`), not a single scalar
(the curvature endomorphism of the `(r, s)`-bundle is an `(r + s)`-slot derivation, whose operator norm
on the compact manifold grows with the valence), so this is NOT the unsatisfiable single-const-∀s shape.

**Non-vacuity.** The zero witness `Gcd = Grem = 0` is rejected: the split would then read
`Curv S = GcurvSectionRS`, forcing the integrated nullity `⟨Curv S − GcurvSectionRS, ∇S⟩_{L²} = 0` to
hold of the (generally non-trivial) differentiated-curvature plus bracket content, and the remainder
bound `rfns(0) ≤ (Cper s)² · (rfns(∇²S) + rfns(∇S) + rfns(S))` carries no information while the genuine
`Gcd`-content (the differentiated curvature `(∇R) S`) is genuinely `rfns(S)`-order non-zero when
`∇R ≠ 0` and `S ≠ 0`; the genuine curvature fields must carry the actual curvature content.

The body is `sorry`; consumers transitively depend on `sorryAx`. -/
theorem exists_pointwiseTensorCurvRS_genuineTriSplit_divergence
    (g : SmoothRiemannianMetric I M) (r : ℕ) :
    ∃ Cper : ℕ → ℝ, (∀ s, 0 ≤ Cper s) ∧
      ∀ (s : ℕ) (S : SmoothCcTensor g r s),
        ∃ Gcd Grem : SmoothCcTensor g r (s + 1),
          pointwiseTensorCurvRS (I := I) (M := M) g r s S =
              GcurvSectionRS (I := I) (M := M) g r s S + Gcd + Grem ∧
          tensorL2Inner (I := I) (M := M) g r (s + 1) Grem.toFun
              (covGrad (I := I) (M := M) g r s S).toFun = 0 ∧
          (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g r (s + 1) x
              ((GcurvSectionRS (I := I) (M := M) g r s S).toSection x) ≤
            Cper s ^ 2 *
              riemannianFiberNormSq (I := I) (M := M) g r (s + 1) x
                ((covGrad (I := I) (M := M) g r s S).toSection x)) ∧
          (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g r (s + 1) x (Gcd.toSection x) ≤
            Cper s ^ 2 *
              (riemannianFiberNormSq (I := I) (M := M) g r (s + 1) x
                  ((covGrad (I := I) (M := M) g r s S).toSection x) +
                riemannianFiberNormSq (I := I) (M := M) g r s x (S.toSection x))) ∧
          (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g r (s + 1) x (Grem.toSection x) ≤
            Cper s ^ 2 *
              (riemannianFiberNormSq (I := I) (M := M) g r (s + 1 + 1) x
                  ((covGrad (I := I) (M := M) g r (s + 1)
                    (covGrad (I := I) (M := M) g r s S)).toSection x) +
                riemannianFiberNormSq (I := I) (M := M) g r (s + 1) x
                    ((covGrad (I := I) (M := M) g r s S).toSection x) +
                riemannianFiberNormSq (I := I) (M := M) g r s x (S.toSection x))) := by
  obtain ⟨K, hK_nn, h⟩ :=
    exists_movingCentreDiffCurvSectionRS_fiberNormSq_bound (I := I) (M := M) g r
  refine ⟨K, hK_nn, fun s S => ?_⟩
  obtain ⟨Gcd, hGScurv, hGcd, hGrem, hnull⟩ := h s S
  refine ⟨Gcd, pointwiseTensorCurvRS (I := I) (M := M) g r s S -
      GcurvSectionRS (I := I) (M := M) g r s S - Gcd, ?_, hnull, hGScurv, hGcd, hGrem⟩
  abel

/-- **The bracket-free `L²` pairing of the genuine fields at `(r, s)` (purely-algebraic nullity
reduction).** If the moving-frame remainder `Curv S − Gcurv − GcurvDeriv` pairs to zero against `∇S`
in `L²`, then the genuine fields `Gcurv + GcurvDeriv` carry the entire cross-pairing
`⟨Curv S, ∇S⟩_{L²}`. The rank-`r` analogue of
`tensorL2Inner_genuineFields_covGrad_eq_pointwiseTensorCurv_of_movingFrameRemainder_nullity`, proved by
the left additivity of the `L²` pairing on
`(Gcurv + GcurvDeriv).toFun + (Curv − Gcurv − GcurvDeriv).toFun = Curv.toFun` (joint integrability
`SmoothCcTensor.integrable_inner_cross`). -/
private theorem tensorL2Inner_genuineFieldsRS_covGrad_eq_pointwiseTensorCurvRS_of_movingFrameRemainder_nullity
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (S : SmoothCcTensor g r s)
    (Gcurv GcurvDeriv : SmoothCcTensor g r (s + 1))
    (hnull : tensorL2Inner (I := I) (M := M) g r (s + 1)
        (pointwiseTensorCurvRS (I := I) (M := M) g r s S - Gcurv - GcurvDeriv).toFun
        (covGrad (I := I) (M := M) g r s S).toFun = 0) :
    tensorL2Inner (I := I) (M := M) g r (s + 1) (Gcurv + GcurvDeriv).toFun
        (covGrad (I := I) (M := M) g r s S).toFun =
      tensorL2Inner (I := I) (M := M) g r (s + 1)
        (pointwiseTensorCurvRS (I := I) (M := M) g r s S).toFun
        (covGrad (I := I) (M := M) g r s S).toFun := by
  classical
  set Curv : SmoothCcTensor g r (s + 1) := pointwiseTensorCurvRS (I := I) (M := M) g r s S with hCurv
  set gradS : SmoothCcTensor g r (s + 1) := covGrad (I := I) (M := M) g r s S with hgrad
  have hCurv_eq : Curv = (Gcurv + GcurvDeriv) + (Curv - Gcurv - GcurvDeriv) := by abel
  have hfun : ((Gcurv + GcurvDeriv) + (Curv - Gcurv - GcurvDeriv)).toFun =
      (Gcurv + GcurvDeriv).toFun + (Curv - Gcurv - GcurvDeriv).toFun :=
    SmoothCcTensor.toFun_add _ _
  have hint₁ := SmoothCcTensor.integrable_inner_cross (I := I) (M := M) (Gcurv + GcurvDeriv) gradS
  have hint₂ :=
    SmoothCcTensor.integrable_inner_cross (I := I) (M := M) (Curv - Gcurv - GcurvDeriv) gradS
  have hsplit :
      tensorL2Inner (I := I) (M := M) g r (s + 1) Curv.toFun gradS.toFun =
        tensorL2Inner (I := I) (M := M) g r (s + 1) (Gcurv + GcurvDeriv).toFun gradS.toFun +
          tensorL2Inner (I := I) (M := M) g r (s + 1)
            (Curv - Gcurv - GcurvDeriv).toFun gradS.toFun := by
    nth_rewrite 1 [hCurv_eq]
    rw [hfun]
    exact tensorL2Inner_add_left (I := I) (M := M) g r (s + 1)
      (Gcurv + GcurvDeriv).toFun (Curv - Gcurv - GcurvDeriv).toFun gradS.toFun hint₁ hint₂
  rw [hnull] at hsplit
  linarith [hsplit]

/-- **The genuine moving-frame third-order Bochner–Weitzenböck field decomposition at contravariant
rank `r` (order-separated genuine fields, `∇²S`-order remainder, bracket-free `L²` pairing).** The
rank-`r` analogue of `exists_pointwiseTensorCurv_movingFrameField_orderSeparated_bracketFreePairing`:
for a closed smooth Riemannian manifold `(M, g)` there is a *valence-dependent* nonnegative constant
`Cper : ℕ → ℝ` such that, at every covariant rank `s` and for every smooth compactly-supported
`(r, s)`-tensor `S`, the order-`2` commutator defect `Curv S := pointwiseTensorCurvRS g r s S` admits
two *genuine curvature* fields `Gcurv, GcurvDeriv : SmoothCcTensor g r (s + 1)` — the section-level
packagings of the pure-Riemann contraction `R(∇S)` and the differentiated-curvature contraction
`(∇R) S` — with the three order-separated fibre bounds

* `rfns(Gcurv)(x) ≤ (Cper s)² · rfns(∇S)(x)`,
* `rfns(GcurvDeriv)(x) ≤ (Cper s)² · (rfns(∇S)(x) + rfns(S)(x))`,
* `rfns(Curv S − Gcurv − GcurvDeriv)(x) ≤ (Cper s)² · (rfns(∇²S)(x) + rfns(∇S)(x) + rfns(S)(x))`,

and the **bracket-free `L²` pairing** `⟨Gcurv + GcurvDeriv, ∇S⟩_{L²} = ⟨Curv S, ∇S⟩_{L²}` (the
moving-frame remainder integrates by parts to zero against `∇S`).

This is **proved** from the deepest moving-frame curvature primitive at `(r, s)`
`exists_pointwiseTensorCurvRS_genuineTriSplit_divergence` (which supplies the existential
differentiated-curvature field `Gcd` and remainder field `Grem` over the concrete pure-Riemann section
`GcurvSectionRS`, the section split, the integrated nullity `⟨Grem, ∇S⟩_{L²} = 0`, and the three sum
fibre bounds) by instantiating `Gcurv := GcurvSectionRS g r s S` (the concrete sound pure-Riemann
section) and `GcurvDeriv := Gcd`; the moving-frame remainder `Curv S − GcurvSectionRS − Gcd` is exactly
`Grem` by the section split, so its bound is read off directly and the bracket-free pairing is recovered
from the integrated nullity by the purely-algebraic left-additivity reduction
`tensorL2Inner_genuineFieldsRS_covGrad_eq_pointwiseTensorCurvRS_of_movingFrameRemainder_nullity`.
Consumers transitively depend on `sorryAx` through the posited deepest tri-split. -/
theorem exists_pointwiseTensorCurvRS_movingFrameField_orderSeparated_bracketFreePairing
    (g : SmoothRiemannianMetric I M) (r : ℕ) :
    ∃ Cper : ℕ → ℝ, (∀ s, 0 ≤ Cper s) ∧
      ∀ (s : ℕ) (S : SmoothCcTensor g r s),
        ∃ Gcurv GcurvDeriv : SmoothCcTensor g r (s + 1),
          (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g r (s + 1) x (Gcurv.toSection x) ≤
            Cper s ^ 2 *
              riemannianFiberNormSq (I := I) (M := M) g r (s + 1) x
                ((covGrad (I := I) (M := M) g r s S).toSection x)) ∧
          (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g r (s + 1) x (GcurvDeriv.toSection x) ≤
            Cper s ^ 2 *
              (riemannianFiberNormSq (I := I) (M := M) g r (s + 1) x
                  ((covGrad (I := I) (M := M) g r s S).toSection x) +
                riemannianFiberNormSq (I := I) (M := M) g r s x (S.toSection x))) ∧
          (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g r (s + 1) x
              ((pointwiseTensorCurvRS (I := I) (M := M) g r s S - Gcurv - GcurvDeriv).toSection x) ≤
            Cper s ^ 2 *
              (riemannianFiberNormSq (I := I) (M := M) g r (s + 1 + 1) x
                  ((covGrad (I := I) (M := M) g r (s + 1)
                    (covGrad (I := I) (M := M) g r s S)).toSection x) +
                riemannianFiberNormSq (I := I) (M := M) g r (s + 1) x
                    ((covGrad (I := I) (M := M) g r s S).toSection x) +
                riemannianFiberNormSq (I := I) (M := M) g r s x (S.toSection x))) ∧
          tensorL2Inner (I := I) (M := M) g r (s + 1) (Gcurv + GcurvDeriv).toFun
              (covGrad (I := I) (M := M) g r s S).toFun =
            tensorL2Inner (I := I) (M := M) g r (s + 1)
              (pointwiseTensorCurvRS (I := I) (M := M) g r s S).toFun
              (covGrad (I := I) (M := M) g r s S).toFun := by
  classical
  obtain ⟨Cper, hCper_nn, hdata⟩ :=
    exists_pointwiseTensorCurvRS_genuineTriSplit_divergence (I := I) (M := M) g r
  refine ⟨Cper, hCper_nn, fun s S => ?_⟩
  obtain ⟨Gcd, Grem, hsplit, hnull, hGScurv, hGcd, hGrem⟩ := hdata s S
  have hrem_eq : pointwiseTensorCurvRS (I := I) (M := M) g r s S -
      GcurvSectionRS (I := I) (M := M) g r s S - Gcd = Grem := by
    rw [hsplit]; abel
  refine ⟨GcurvSectionRS (I := I) (M := M) g r s S, Gcd, hGScurv, hGcd, fun x => ?_, ?_⟩
  · rw [hrem_eq]; exact hGrem x
  · refine tensorL2Inner_genuineFieldsRS_covGrad_eq_pointwiseTensorCurvRS_of_movingFrameRemainder_nullity
      (I := I) (M := M) g r s S (GcurvSectionRS (I := I) (M := M) g r s S) Gcd ?_
    rw [hrem_eq]; exact hnull

end Connection
end Integral
end DifferentialGeometry

end
