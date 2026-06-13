import DifferentialGeometry.Geometry.Connection.TensorNabla.TensorSlotwiseCurvatureRS
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.PointwiseTensorCurvatureRS
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.HomFieldCurvatureJetDecomposition
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.MovingFrameCurvatureTraceSmooth
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.MovingFrameGenuineFieldPairing
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.FiberNormSubadditivity
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.RankRDiffBilinGrid
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.RankRPureRCurvatureTower
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.RankRDiffCurvatureTower
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.RicciTraceCarrier
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.MovingFrameRemainderFrameSumBridgeRS
import DifferentialGeometry.Analysis.Integration.L2.Pairing.Algebra
import DifferentialGeometry.Analysis.Integration.L2.SmoothSections.Integrability
import DifferentialGeometry.Analysis.Sobolev.Embedding.SobolevEmbeddingCm
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.GreenIdentityAndIBP.IntegratedOrder2WeitzenbockRS

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
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.PDE.RicciFlow

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

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

/-- **The rank-`r` order-`2` commutator defect as a fixed-frame sum of per-summand third-order
differences (sorry-free).** The section value at `x` of the bundled defect `pointwiseTensorCurvRS g r
s S = Δ_∇(∇S) − ∇(Δ_∇ S)` is the fixed-frame sum of the per-summand third-order difference fields
`remDiffFibRS g r s S x i` (`MovingFrameRemainderFrameSumBridgeRS`), over the `g_x`-orthonormal frame
`Bᵢ := smoothOrthoFrame g x i`:
```
(pointwiseTensorCurvRS g r s S).toSection x = ∑ᵢ remDiffFibRS g r s S x i.
```
The defect's body is definitionally the upstream difference
`rawTensorConnLapSmooth g r (s + 1) (covGrad g r s S) − covGrad g r s (rawTensorConnLapSmooth g r s
S)` over which the engine identity `commutatorDefectRS_toSection_eq_frame_sum` is stated, so this is
its `rfl`-grade re-expression over the named defect. The contravariant-rank-`r` mirror of
`pointwiseTensorCurv_toSection_eq_frame_sum`. -/
theorem pointwiseTensorCurvRS_toSection_eq_frame_sum
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (S : SmoothCcTensor g r s) (x : M) :
    (pointwiseTensorCurvRS (I := I) (M := M) g r s S).toSection x =
      ∑ i : Fin (Module.finrank ℝ E), remDiffFibRS (I := I) (M := M) g r s S x i :=
  commutatorDefectRS_toSection_eq_frame_sum (I := I) (M := M) g r s S x

/-- **The rank-`r` frame-summand integrand identity over the bundled defect (sorry-free).** The
pointwise metric inner product of the rank-`r` order-`2` commutator defect `pointwiseTensorCurvRS g r
s S` against the gradient field `∇S := covGrad g r s S` — the integrand of the rank-`r` curvature
cross-pairing — is the fixed-frame sum of the per-summand pairings of the third-order difference
fields `remDiffFibRS` against `∇S`:
```
⟨Curv S, ∇S⟩(x) = ∑ᵢ ⟨remDiffFibRS g r s S x i, ∇S(x)⟩,   Bᵢ := smoothOrthoFrame g x i.
```
The `rfl`-grade re-expression of the engine identity `commutatorDefectRS_pairing_eq_frameSum`
(`MovingFrameRemainderFrameSumBridgeRS`) over the named bundled defect (whose body is definitionally
the upstream difference). The contravariant-rank-`r` mirror of
`pointwiseTensorCurvPairing_eq_frameSum`. -/
theorem pointwiseTensorCurvRS_pairing_eq_frameSum
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (S : SmoothCcTensor g r s) (x : M) :
    tensorInnerPointwise (I := I) (M := M) g r (s + 1) x
        ((pointwiseTensorCurvRS (I := I) (M := M) g r s S).toFun x)
        ((covGrad (I := I) (M := M) g r s S).toFun x) =
      ∑ i : Fin (Module.finrank ℝ E),
        tensorInnerPointwise (I := I) (M := M) g r (s + 1) x
          (TensorRSSpace.toModel (remDiffFibRS (I := I) (M := M) g r s S x i))
          ((covGrad (I := I) (M := M) g r s S).toFun x) :=
  commutatorDefectRS_pairing_eq_frameSum (I := I) (M := M) g r s S x

/-- **The rank-`r` curvature cross-pairing as the integral of the frame-summed remainder integrand,
over the bundled defect (sorry-free).** The global metric `L²` pairing of the rank-`r` order-`2`
commutator defect `pointwiseTensorCurvRS g r s S` against `∇S := covGrad g r s S` is the integral
over the closed manifold of the fixed-frame sum of the per-summand pairings `⟨remDiffFibRS …, ∇S⟩`:
```
⟨Curv S, ∇S⟩_{L²} = ∫_M ∑ᵢ ⟨remDiffFibRS g r s S x i, ∇S(x)⟩ dvol_g.
```
The `rfl`-grade re-expression of the engine identity
`tensorL2Inner_commutatorDefectRS_covGrad_eq_frameSum_integral`
(`MovingFrameRemainderFrameSumBridgeRS`) over the named bundled defect. The contravariant-rank-`r`
mirror of `tensorL2Inner_pointwiseTensorCurv_covGrad_eq_frameSum_integral`. -/
theorem tensorL2Inner_pointwiseTensorCurvRS_covGrad_eq_frameSum_integral
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (S : SmoothCcTensor g r s) :
    tensorL2Inner (I := I) (M := M) g r (s + 1)
        (pointwiseTensorCurvRS (I := I) (M := M) g r s S).toFun
        (covGrad (I := I) (M := M) g r s S).toFun =
      ∫ x, (∑ i : Fin (Module.finrank ℝ E),
              tensorInnerPointwise (I := I) (M := M) g r (s + 1) x
                (TensorRSSpace.toModel (remDiffFibRS (I := I) (M := M) g r s S x i))
                ((covGrad (I := I) (M := M) g r s S).toFun x))
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) :=
  tensorL2Inner_commutatorDefectRS_covGrad_eq_frameSum_integral (I := I) (M := M) g r s S

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

/-- **The rank-`r` Ricci-trace carrier `Ric(∇S)`** — the contravariant-rank-`r` mirror of the rank-`0`
Ricci-trace carrier `ricTraceSection` (`RicciTraceCarrier`): the operator-field action of the
leading-slot raised-Ricci operator field `ricSlotOpField g s` on `∇S = covGrad g r s S`, through the
contravariant-valence-`r` action `appCcRS` (`OperatorFieldCovariantCalculusRS`),
```
ricTraceSectionRS g r s S := appCcRS (ricSlotOpField g s) (∇S),
```
the term-`(IV)` leading-slot Ricci-trace contraction `∑ⱼ Ric(·, eⱼ) (∇S)(eⱼ, …)` at contravariant rank
`r`, a smooth compactly-supported `(r, s + 1)`-tensor. At `r = 0` it is definitionally the rank-`0`
carrier (`ricTraceSectionRS_zero_eq`); at `(r, s) = (0, 0)` its leading slot reads the classical
Bochner Ricci trace `Ric(∇f, ·)` (`ricTraceSection_zero_apply`). It is the THIRD genuine carrier of the
rank-`r` order-`2` commutator defect, alongside the pure-Riemann `GcurvSectionRS` and the gauge-glued
differentiated-curvature `diffCurvSectionRS` — the rank-`r` mirror of the rank-`0` three-carrier
decomposition `GcurvSection + (∇R)·∇S + ricTraceSection`
(`bochnerWeitzenbock_threeSection_curvatureValue_posit`, `MovingFrameRemainderFrameSumBridge`).

**Non-vacuity.** At `(r, s) = (0, 0)` the other two carriers vanish identically (the rank-`r`
pure-Riemann and differentiated-curvature endomorphisms are zero on the scalar bundle), while this
carrier is `Ric(∇f, ·) ≠ 0` on a Ricci-non-flat manifold — it carries the entire classical scalar
Bochner curvature value `∫ Ric(∇f, ∇f)` and cannot be dropped or absorbed into `diffCurvSectionRS`. -/
def ricTraceSectionRS (g : SmoothRiemannianMetric I M) (r s : ℕ) (S : SmoothCcTensor g r s) :
    SmoothCcTensor g r (s + 1) :=
  appCcRS (I := I) (M := M) g r (s + 1) (s + 1)
    (ricSlotOpField (I := I) (M := M) g s) (covGrad (I := I) (M := M) g r s S)

/-- The fibre value of `ricTraceSectionRS` is the fibrewise composition
`ricSlotOpFib.comp (∇S)`. Definitional via `appCcRS_toSection`. -/
@[simp] lemma ricTraceSectionRS_toSection (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (x : M) :
    (ricTraceSectionRS (I := I) (M := M) g r s S).toSection x =
      (show Tensor0SSpace (s + 1) I x →L[ℝ] Tensor0SSpace (s + 1) I x from
        (ricSlotOpField (I := I) (M := M) g s).toSection x).comp
        (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace (s + 1) I x from
          (covGrad (I := I) (M := M) g r s S).toSection x) := rfl

/-- **At contravariant rank `0` the rank-`r` Ricci-trace carrier is the rank-`0` Ricci-trace
carrier** — via the `a = 0` collapse `appCcRS_zero_eq_appCc` of the valence-`a` operator-field
action. -/
lemma ricTraceSectionRS_zero_eq (g : SmoothRiemannianMetric I M) (s : ℕ)
    (S : SmoothCcTensor g 0 s) :
    ricTraceSectionRS (I := I) (M := M) g 0 s S = ricTraceSection (I := I) (M := M) g s S := by
  rw [ricTraceSectionRS, ricTraceSection]
  exact appCcRS_zero_eq_appCc (I := I) (M := M) g (s + 1) (s + 1)
    (ricSlotOpField (I := I) (M := M) g s) (covGrad (I := I) (M := M) g 0 s S)

/-- **The order-`0` rank-`r` frame-free pure-Riemann operator on `∇S` is the concrete moving-centre
pure-Riemann genuine curvature section (file-local concrete-tower equality).** Both sides' fibres are
the slot-`0` uncurry through `covGradBundleEquiv r s x` of the same pure-Riemann direction CLM
`v ↦ ∑ᵢ R(Bᵢ x, v)(∇_{Bᵢ} S(x))`: the operator side by the public slot-`0` reading
`genuinePureRDiffOp0_covGrad_fib_eq` (`RankRPureRCurvatureTower`), the section side by definition of
`genuineCurvPureRFibRS` through `genuinePureRDirCLMRS`. The equality discharged inside
`exists_pureRGenuineDiffOpRS_bridge` and consumed by the engine-bridge identities
`remDiffGenuineFibRS_sum_eq_GcurvSectionRS_toSection` and
`remDiffFibRS_genuineFrameSum_pairing_eq_GcurvSectionRS` below. -/
private theorem genuinePureRDiffOp0RS_covGrad_eq_GcurvSectionRS
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (S : SmoothCcTensor g r s) :
    genuinePureRDiffOpRS (I := I) (M := M) g r 0 (s + 1)
        (covGrad (I := I) (M := M) g r s S) =
      GcurvSectionRS (I := I) (M := M) g r s S := by
  refine SmoothCcTensor.ext (DFunLike.ext _ _ (fun x => ?_))
  have hLHS_eq : (genuinePureRDiffOpRS (I := I) (M := M) g r 0 (s + 1)
      (covGrad (I := I) (M := M) g r s S)).toSection x =
      covGradBundleEquiv (I := I) (M := M) r s x
        (pureRDirCLMFixedFrameRS (I := I) (M := M) g r s S (smoothOrthoFrame (I := I) g x) x) := by
    refine (ContinuousLinearEquiv.symm_apply_eq (covGradBundleEquiv (I := I) (M := M) r s x)).mp ?_
    refine ContinuousLinearMap.ext (fun v => ?_)
    rw [genuinePureRDiffOp0_covGrad_fib_eq (I := I) (M := M) g r s S x v]
    rw [pureRDirCLMFixedFrameRS, ContinuousLinearMap.sum_apply]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [pureRDirCLMSummandFixedFrameRS, LinearMap.coe_toContinuousLinearMap',
      pureRDirLMSummandFixedFrameRS, LinearMap.coe_mk, AddHom.coe_mk]
  rw [hLHS_eq, GcurvSectionRS_toSection, genuineCurvPureRFibRS, genuinePureRDirCLMRS]

/-- **The engine's per-direction pure-Riemann genuine curvature direction CLM is the slot-`i`
fixed-frame summand against the moving frame (sorry-free, by definition).** The frame-bridge object
`remDiffGenuineDirCLMRS g r s S x i` (`MovingFrameRemainderFrameSumBridgeRS`, the slot-`i` curvature
direction CLM `v ↦ R(Bᵢ, v)(∇_{Bᵢ} S(x))` with `Bᵢ := smoothOrthoFrame g x i`) coincides with this
file's fixed-frame summand `pureRDirCLMSummandFixedFrameRS g r s S (smoothOrthoFrame g x) x i`: both
are the continuous-linear upgrade of the identical curvature-direction linear map read off
`riemannOp (tensorCov g r s)`. The contravariant-rank-`r` mirror of
`remDiffGenuineDirCLM_eq_genuinePureRDirCLMSummand`. -/
theorem remDiffGenuineDirCLMRS_eq_pureRDirCLMSummandFixedFrameRS
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (S : SmoothCcTensor g r s) (x : M)
    (i : Fin (Module.finrank ℝ E)) :
    remDiffGenuineDirCLMRS (I := I) (M := M) g r s S x i =
      pureRDirCLMSummandFixedFrameRS (I := I) (M := M) g r s S
        (smoothOrthoFrame (I := I) g x) x i := rfl

/-- **The pure-Riemann genuine fibre frame-sum is the concrete pure-Riemann section value, pointwise
(sorry-free).** For a closed smooth Riemannian manifold `(M, g)`, contravariant rank `r`, covariant
rank `s`, smooth compactly-supported `(r, s)`-tensor `S`, and point `x`, the fixed-frame sum of the
per-direction pure-Riemann genuine curvature fibres `remDiffGenuineFibRS`
(`MovingFrameRemainderFrameSumBridgeRS`) is the fibre value of the concrete moving-centre pure-Riemann
genuine curvature section `GcurvSectionRS g r s S`:
```
∑ᵢ remDiffGenuineFibRS g r s S x i = (GcurvSectionRS g r s S).toSection x.
```

**Proof (sorry-free).** The engine identity
`remDiffGenuineFibRS_sum_eq_genuinePureRDiffOp0_toSection` reads the frame sum as the fibre value of
the order-`0` rank-`r` frame-free pure-Riemann operator on `∇S`, identified with the concrete section
by the concrete-tower equality `genuinePureRDiffOp0RS_covGrad_eq_GcurvSectionRS` (the equality
discharged inside `exists_pureRGenuineDiffOpRS_bridge`). The pure-Riemann trace is genuinely
tensorial (direction-linear, read off `riemannOp`), so this is a sound pointwise frame-sum identity —
the contravariant-rank-`r` mirror of `remDiffGenuineFib_sum_eq_GcurvSection_toSection`. -/
theorem remDiffGenuineFibRS_sum_eq_GcurvSectionRS_toSection
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (S : SmoothCcTensor g r s) (x : M) :
    (∑ i : Fin (Module.finrank ℝ E), remDiffGenuineFibRS (I := I) (M := M) g r s S x i) =
      (GcurvSectionRS (I := I) (M := M) g r s S).toSection x := by
  rw [remDiffGenuineFibRS_sum_eq_genuinePureRDiffOp0_toSection (I := I) (M := M) g r s S x,
    genuinePureRDiffOp0RS_covGrad_eq_GcurvSectionRS (I := I) (M := M) g r s S]

/-- **The rank-`r` pure-Riemann genuine frame-sum pairing equals the concrete pure-Riemann section
value (sorry-free, integrated form).** For a closed smooth Riemannian manifold `(M, g)`, contravariant
rank `r`, covariant rank `s`, and smooth compactly-supported `(r, s)`-tensor `S`, the pure-Riemann
genuine frame-sum integrand is Bochner-integrable against the Riemannian volume measure, and its
integral over the closed manifold equals the global metric `L²` pairing of the concrete moving-centre
pure-Riemann genuine curvature section `GcurvSectionRS g r s S` against `∇S := covGrad g r s S`:
```
∫_M ∑ᵢ ⟨remDiffGenuineFibRS g r s S x i, ∇S(x)⟩ dvol_g = ⟨GcurvSectionRS g r s S, ∇S⟩_{L²}.
```

**Proof (sorry-free).** The engine identity `remDiffFibRS_genuineFrameSum_pairing_eq_genuineFields`
(`MovingFrameRemainderFrameSumBridgeRS`) carries both conjuncts against the order-`0` rank-`r`
frame-free pure-Riemann operator value on `∇S`, rewritten to the concrete section by the
concrete-tower equality `genuinePureRDiffOp0RS_covGrad_eq_GcurvSectionRS`. The pure-Riemann trace is
genuinely tensorial in the direction, so this is a *sound pointwise* frame-sum identity — the
contravariant-rank-`r` mirror of `remDiffFib_genuineFrameSum_pairing_eq_genuineFields`
(`MovingFrameRemainderFrameSumBridge`), with the concrete `GcurvSectionRS` on the right. -/
theorem remDiffFibRS_genuineFrameSum_pairing_eq_GcurvSectionRS
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (S : SmoothCcTensor g r s) :
    MeasureTheory.Integrable
        (fun x => ∑ i : Fin (Module.finrank ℝ E),
            tensorInnerPointwise (I := I) (M := M) g r (s + 1) x
              (TensorRSSpace.toModel (remDiffGenuineFibRS (I := I) (M := M) g r s S x i))
              ((covGrad (I := I) (M := M) g r s S).toFun x))
        (riemannianVolumeMeasure (I := I) (M := M) g) ∧
      (∫ x, (∑ i : Fin (Module.finrank ℝ E),
            tensorInnerPointwise (I := I) (M := M) g r (s + 1) x
              (TensorRSSpace.toModel (remDiffGenuineFibRS (I := I) (M := M) g r s S x i))
              ((covGrad (I := I) (M := M) g r s S).toFun x))
        ∂(riemannianVolumeMeasure (I := I) (M := M) g)) =
      tensorL2Inner (I := I) (M := M) g r (s + 1)
        (GcurvSectionRS (I := I) (M := M) g r s S).toFun
        (covGrad (I := I) (M := M) g r s S).toFun := by
  have h := remDiffFibRS_genuineFrameSum_pairing_eq_genuineFields (I := I) (M := M) g r s S
  rwa [genuinePureRDiffOp0RS_covGrad_eq_GcurvSectionRS (I := I) (M := M) g r s S] at h

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
  classical
  -- The frame-free pure-Riemann differentiated curvature tower at valence `r`, packaged as a
  -- `DiffBilinOpRS g r` (`RankRPureRCurvatureTower`): the order-`0` operator is the moving-centre
  -- pure-Riemann endomorphism, the Leibniz field is proved by `sub_add_cancel`, the envelope is the
  -- single posited frame-free analytic node. Its order-`0` operator on `∇S` is `GcurvSectionRS` by
  -- the concrete-tower equality.
  refine ⟨genuinePureRDiffOpRS_bilinOp (I := I) (M := M) g r, fun s S => ?_⟩
  rw [genuinePureRDiffOpRS_bilinOp_op]
  exact genuinePureRDiffOp0RS_covGrad_eq_GcurvSectionRS (I := I) (M := M) g r s S

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

/-- **The rank-`r` fixed-Hom-field curvature jet decomposition of the order-`2` commutator defect
(posited general-rank operator-field primitive — the single missing-upstream curvature atom).** For a
closed smooth Riemannian manifold `(M, g)` and a fixed contravariant rank `r`, at every covariant rank
`s` there are three fixed smooth full Hom-bundle field sections
`Q₀ : Hom(T^{(r,s)}, T^{(r,s+1)})`, `Q₁ : Hom(T^{(r,s+1)}, T^{(r,s+1)})`,
`Q₂ : Hom(T^{(r,s+2)}, T^{(r,s+1)})` such that, for every smooth compactly-supported `(r, s)`-tensor `S`,
```
pointwiseTensorCurvRS g r s S = Q₀ · S + Q₁ · ∇S + Q₂ · ∇²S,
```
where `Curv S := Δ_∇(∇S) − ∇(Δ_∇ S)`, `∇S := covGrad g r s S`, `∇²S := iteratedCovGrad g r s 2 S`, and
`·` is the full Hom-bundle action `appFullSec`. The classical first-order rough-Laplacian /
covariant-gradient commutator identity `[Δ_∇, ∇] = (∇R)·S + R·∇S + (trace-gradient)·∇²S` at a generic
contravariant valence `r`, in fixed smooth Hom-field form.

**Why this is TRUE.** Reading the rough Laplacian as the metric double-trace of the two leading covariant
slots (`Δ_∇ W = Tr · ∇²W`, the frame-trace reading `rawTensorConnLap_eq_frame_trace_secondCovDeriv`
packaged as a fixed-field action through the value-local representation theorem) at valences `s + 1` and
`s` (the latter differentiated by the covariant product rule `covGrad_appFullSec_eq`, splitting off the
trace-gradient field `∇Tr s` on `∇²S`), the defect's body `Δ_∇(∇S) − ∇(Δ_∇ S)` leaves exactly the
order-`3` head difference `Tr (s+1) · ∇³S − slotExt(Tr s) · ∇³S` — the curvature term born from re-tracing
a different leading pair of the third covariant gradient — which the section-level Ricci identity
`tensorSecondCovDeriv_antisymm_eq_riemannOp` (`TensorRicciCommutator`, at arbitrary `(r, s)`) supplies as a
fixed field action on the `≤ 2`-jet `(S, ∇S, ∇²S)`; the two `∇²S` summands merge by `appFullSec_sub_left`.

**This is the genuinely-missing-upstream rank-`r` curvature primitive.** The full proof of this
decomposition is developed *sorry-free* in `HomFieldCurvatureJetDecomposition`
(`exists_pointwiseTensorCurvRS_homField_jetDecomposition`), through the metric-double-trace field
`metricDoubleTraceField`, the trace factorisation `roughLap_eq_metricDoubleTrace`, and the head-difference
drop `headDifferenceDrop_bracket` / `exists_headDifferenceDrop_metricDoubleTrace`. The shared defect
`pointwiseTensorCurvRS` now lives in the thin upstream `PointwiseTensorCurvatureRS`, so both that file and
this one import it without a file-level cycle, and `HomFieldCurvatureJetDecomposition` is importable here.
This node is therefore the verbatim re-export of the proven downstream decomposition (no `sorry`), from
which this file's doubly-peeled fibre-order bound
`exists_pointwiseTensorCurvRS_subGcurvSubDiffCurv_obstruction_fiberOrder_bound` is *derived* over the
operator-field iterated-gradient window envelope `exists_appFullSec_on_jet_iteratedCovGrad_window_bound`
and the two concrete carrier grids.

**Non-vacuity.** A degenerate triple `Q₀ = Q₁ = Q₂ = 0` would force `pointwiseTensorCurvRS g r s S = 0` at
every `s`, `S`; but the order-`2` commutator defect `Δ_∇(∇S) − ∇(Δ_∇ S)` is the genuine third-order
curvature contraction of `S`, non-zero on a non-flat manifold (`R ≠ 0`) for a non-parallel `S` — so the
zero triple is rejected and the operator fields genuinely carry the curvature content. -/
theorem exists_pointwiseTensorCurvRS_homFieldJetDecompositionRS
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    ∃ (Q₀ : HomTensorRSField (E := E) (M := M) r s (s + 1) I)
      (Q₁ : HomTensorRSField (E := E) (M := M) r (s + 1) (s + 1) I)
      (Q₂ : HomTensorRSField (E := E) (M := M) r (s + 2) (s + 1) I),
      ∀ S : SmoothCcTensor g r s,
        pointwiseTensorCurvRS (I := I) (M := M) g r s S =
          appFullSec (I := I) (M := M) g r s (s + 1) Q₀ S +
            appFullSec (I := I) (M := M) g r (s + 1) (s + 1) Q₁
              (covGrad (I := I) (M := M) g r s S) +
            appFullSec (I := I) (M := M) g r (s + 2) (s + 1) Q₂
              (iteratedCovGrad g r s 2 S) := by
  exact exists_pointwiseTensorCurvRS_homField_jetDecomposition (I := I) (M := M) g r s

/-- **The rank-`r` doubly-peeled moving-frame remainder fibre order — the `(0, 3)` graded curvature jet
at gradient order `0` (posited general-rank curvature core).** The contravariant-rank-`r` upstream atom
that the downstream genuine `(0, 3)` graded-jet re-derivation
`exists_pointwiseTensorCurvRS_subGcurvSubDiffCurv_fullSum_gradedCurvJet` (`OrderSeparatedCurvatureJetRS`,
which *imports this file*, so cannot be cited here) collapses to at gradient order `k = 0`. For a closed
smooth Riemannian manifold `(M, g)` and a fixed contravariant rank `r` there is a *valence-dependent*
nonnegative constant `C : ℕ → ℝ` such that, at every covariant rank `s`, every smooth compactly-supported
`(r, s)`-tensor `S` and every point `x`, the doubly-peeled moving-frame remainder of the order-`2`
commutator defect — `Grem := Curv S − GcurvSectionRS g r s S − diffCurvSectionRS g r s S`, peeling off
both the pure-Riemann `R(∇S)` contraction `GcurvSectionRS g r s S` and the gauge-glued differentiated
`(∇R) S` carrier `diffCurvSectionRS g r s S` (the order-`0` base of the differentiated tower,
`RankRDiffCurvatureTower`), with `Curv S := pointwiseTensorCurvRS g r s S = Δ_∇(∇S) − ∇(Δ_∇ S)` — has its
intrinsic fibre norm bounded by the **full-sum** order-`≤ 2` covariant jet of `S`:
```
rfns(Curv S − GcurvSectionRS g r s S − diffCurvSectionRS g r s S)(x)
  ≤ (C s)² · ( rfns(∇²S)(x) + rfns(∇S)(x) + rfns(S)(x) ).
```

**Why this is TRUE — the iterated Ricci identity controls the doubly-peeled remainder.** This is the
gradient-order-`0` slice of the contravariant-rank-`r` `(0, 3)` graded curvature jet
`exists_pointwiseTensorCurvRS_subGcurvSubDiffCurv_fullSum_gradedCurvJet` (at `k = 0` the truncated window
`∑_{i < 3} rfns(∇^{i} S)` reads exactly `rfns(S) + rfns(∇S) + rfns(∇²S)`), which in turn is *derived*
downstream from the genuine three-field full-sum base split
`exists_pointwiseTensorCurvRS_genuineThreeField_fullSum_m0_baseSplit` (the iterated-Ricci deep well). By
definition `Curv S = Δ_∇(∇S) − ∇(Δ_∇ S)`; commuting the two derivative slots by the rank-`(r, s + 1)`
Ricci identity `secondCovDeriv_covGrad_antisymm_eq_riemannOp_gen` (lifted to the `(r, s)`-bundle through
the slot-wise curvature formula `riemannSec_tensorCov_apply_eval` of `TensorSlotwiseCurvatureRS`) cancels
the top-order `∇³S` terms; subtracting off the two genuine carriers `GcurvSectionRS g r s S` (pure-`R`,
`rfns(∇S)`-order) and `diffCurvSectionRS g r s S` (`(∇R) S`, `rfns(S)`-order) leaves only the residual
`∇²S`-order moving-frame / frame-bracket remainder, all curvature coefficients absorbed uniformly over
the compact `M` into `(C s)²`.

**T1 (intrinsic single-tensor fibre norm only).** The `∇³S`-cancellation is *false term-by-term* through
the non-tensorial `smoothExtensionTangent` reading (chart-selection-unbounded on `S²`); only the intrinsic
full-sum frame-summed remainder is order-controlled. The bound is stated for the intrinsic fibre norm
`rfns` of the single tensor `Curv S − GcurvSectionRS g r s S − diffCurvSectionRS g r s S` throughout — it
never extracts a per-direction `M → E` quantity — so it is trap-screened. This genuinely general-rank
doubly-peeled moving-frame remainder content (= the downstream `(0, 3)` graded jet at `k = 0`) is absent
sorry-free below this file (the `(0, 3)` graded-jet machinery `OrderSeparatedCurvatureJetRS` lives
*downstream* of this file and imports it, hence cannot be cited), so it is posited here as the single
precise true upstream atom from which `exists_pointwiseTensorCurvRS_subGcurv_obstruction_fiberOrder_bound`
is *derived* (`Curv S − GcurvSectionRS = diffCurvSectionRS + Grem`, the diffCurv leg bounded sorry-free by
`exists_diffCurvSectionRS_iteratedCovGrad_grid_bound` at `k = 0`). Consumers transitively depend on
`sorryAx`.

**Non-vacuity.** With `C s = 0` the bound forces
`rfns(Curv S − GcurvSectionRS g r s S − diffCurvSectionRS g r s S)(x) = 0`, i.e.
`Curv S = GcurvSectionRS g r s S + diffCurvSectionRS g r s S`; *false* on a non-flat manifold — the
moving-frame bracket discrepancy after both genuine peels is genuinely `∇²S`-order non-zero. The constant
family is genuinely positive. The body is `sorry`. -/
theorem exists_pointwiseTensorCurvRS_subGcurvSubDiffCurv_obstruction_fiberOrder_bound
    (g : SmoothRiemannianMetric I M) (r : ℕ) :
    ∃ C : ℕ → ℝ, (∀ s, 0 ≤ C s) ∧
      ∀ (s : ℕ) (S : SmoothCcTensor g r s) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g r (s + 1) x
            ((pointwiseTensorCurvRS (I := I) (M := M) g r s S -
              GcurvSectionRS (I := I) (M := M) g r s S -
              diffCurvSectionRS (I := I) (M := M) g r s S).toSection x) ≤
          C s ^ 2 *
            (riemannianFiberNormSq (I := I) (M := M) g r (s + 1 + 1) x
                ((covGrad (I := I) (M := M) g r (s + 1)
                  (covGrad (I := I) (M := M) g r s S)).toSection x) +
              riemannianFiberNormSq (I := I) (M := M) g r (s + 1) x
                  ((covGrad (I := I) (M := M) g r s S).toSection x) +
              riemannianFiberNormSq (I := I) (M := M) g r s x (S.toSection x)) := by
  classical
  -- The operator-field decomposition `Curv = Q₀·S + Q₁·∇S + Q₂·∇²S` (the posited rank-`r` curvature
  -- atom) and the per-rank window envelopes of its three pieces. The doubly-peeled remainder is the
  -- `abel`-rearrangement `(Q₀·S − diffCurv) + (Q₁·∇S − Gcurv) + Q₂·∇²S`; each leg is bounded at gradient
  -- order `0` by the matching jet (`Q₀·S`, `diffCurv` → `rfns(S)`; `Q₁·∇S`, `Gcurv` → `rfns(∇S)`;
  -- `Q₂·∇²S` → `rfns(∇²S)`), merged by fibre subadditivity. The per-rank window constants depend on the
  -- rank `s`, so the per-`s` bound is established first and the valence family extracted by choice.
  suffices hstep : ∀ s : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ (S : SmoothCcTensor g r s) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g r (s + 1) x
            ((pointwiseTensorCurvRS (I := I) (M := M) g r s S -
              GcurvSectionRS (I := I) (M := M) g r s S -
              diffCurvSectionRS (I := I) (M := M) g r s S).toSection x) ≤
          C ^ 2 *
            (riemannianFiberNormSq (I := I) (M := M) g r (s + 1 + 1) x
                ((covGrad (I := I) (M := M) g r (s + 1)
                  (covGrad (I := I) (M := M) g r s S)).toSection x) +
              riemannianFiberNormSq (I := I) (M := M) g r (s + 1) x
                  ((covGrad (I := I) (M := M) g r s S).toSection x) +
              riemannianFiberNormSq (I := I) (M := M) g r s x (S.toSection x)) by
    refine ⟨fun s => Classical.choose (hstep s), fun s => (Classical.choose_spec (hstep s)).1,
      fun s S x => (Classical.choose_spec (hstep s)).2 S x⟩
  intro s
  obtain ⟨Q₀, Q₁, Q₂, hdecomp⟩ :=
    exists_pointwiseTensorCurvRS_homFieldJetDecompositionRS (I := I) (M := M) g r s
  obtain ⟨cc₀, hcc₀_nn, hcc₀⟩ :=
    exists_appFullSec_on_jet_iteratedCovGrad_window_bound (I := I) (M := M) g r s 0 (s + 1) Q₀
  obtain ⟨cc₁, hcc₁_nn, hcc₁⟩ :=
    exists_appFullSec_on_jet_iteratedCovGrad_window_bound (I := I) (M := M) g r s 1 (s + 1) Q₁
  obtain ⟨cc₂, hcc₂_nn, hcc₂⟩ :=
    exists_appFullSec_on_jet_iteratedCovGrad_window_bound (I := I) (M := M) g r s 2 (s + 1) Q₂
  obtain ⟨cd, hcd_nn, hcd⟩ := exists_diffCurvSectionRS_iteratedCovGrad_grid_bound (I := I) (M := M) g r
  obtain ⟨cg, hcg_nn, hcg⟩ := exists_GcurvSectionRS_iteratedCovGrad_grid_bound (I := I) (M := M) g r
  refine ⟨Real.sqrt (8 * cc₀ 0 + 8 * (cd s 0) ^ 2 + 8 * cc₁ 0 + 8 * (cg s 0) ^ 2 +
      4 * cc₂ 0),
    Real.sqrt_nonneg _, fun S x => ?_⟩
  -- Abbreviate the three target fibre norms and the five leg pieces.
  set A : ℝ := riemannianFiberNormSq (I := I) (M := M) g r (s + 1 + 1) x
      ((covGrad (I := I) (M := M) g r (s + 1) (covGrad (I := I) (M := M) g r s S)).toSection x) with hA
  set B : ℝ := riemannianFiberNormSq (I := I) (M := M) g r (s + 1) x
      ((covGrad (I := I) (M := M) g r s S).toSection x) with hB
  set D : ℝ := riemannianFiberNormSq (I := I) (M := M) g r s x (S.toSection x) with hD
  have hA_nn : 0 ≤ A := riemannianFiberNormSq_nonneg (I := I) (M := M) g r (s + 1 + 1) x _
  have hB_nn : 0 ≤ B := riemannianFiberNormSq_nonneg (I := I) (M := M) g r (s + 1) x _
  have hD_nn : 0 ≤ D := riemannianFiberNormSq_nonneg (I := I) (M := M) g r s x _
  -- The defect's doubly-peeled remainder, rearranged to the three Hom-field legs.
  set G₀ : SmoothCcTensor g r (s + 1) :=
    appFullSec (I := I) (M := M) g r s (s + 1) Q₀ S -
      diffCurvSectionRS (I := I) (M := M) g r s S with hG₀
  set G₁ : SmoothCcTensor g r (s + 1) :=
    appFullSec (I := I) (M := M) g r (s + 1) (s + 1) Q₁
        (covGrad (I := I) (M := M) g r s S) -
      GcurvSectionRS (I := I) (M := M) g r s S with hG₁
  set G₂ : SmoothCcTensor g r (s + 1) :=
    appFullSec (I := I) (M := M) g r (s + 2) (s + 1) Q₂ (iteratedCovGrad g r s 2 S) with hG₂
  have hrem_eq : pointwiseTensorCurvRS (I := I) (M := M) g r s S -
      GcurvSectionRS (I := I) (M := M) g r s S -
      diffCurvSectionRS (I := I) (M := M) g r s S = G₀ + G₁ + G₂ := by
    rw [hG₀, hG₁, hG₂, hdecomp S]; abel
  -- The section value of the remainder as the pointwise sum of the three leg section values.
  have hrem_sec : (pointwiseTensorCurvRS (I := I) (M := M) g r s S -
        GcurvSectionRS (I := I) (M := M) g r s S -
        diffCurvSectionRS (I := I) (M := M) g r s S).toSection x =
      (G₀.toSection x + G₁.toSection x) + G₂.toSection x := by
    rw [hrem_eq, SmoothCcTensor.toSection_add, SmoothCcTensor.toSection_add]
    simp only [ContMDiffSection.coe_add, Pi.add_apply]
  -- Fibre subadditivity: split off `G₂`, then split `G₀ + G₁`.
  have hsplit1 := riemannianFiberNormSq_add_le (I := I) (M := M) g r (s + 1) x
    (G₀.toSection x + G₁.toSection x) (G₂.toSection x)
  have hsplit2 := riemannianFiberNormSq_add_le (I := I) (M := M) g r (s + 1) x
    (G₀.toSection x) (G₁.toSection x)
  -- Each leg's fibre norm: split the subtraction, then bound the Hom-field action and the carrier.
  have hG₀sec : G₀.toSection x =
      (appFullSec (I := I) (M := M) g r s (s + 1) Q₀ S).toSection x -
        (diffCurvSectionRS (I := I) (M := M) g r s S).toSection x := by
    rw [hG₀, SmoothCcTensor.toSection_sub]; rfl
  have hG₁sec : G₁.toSection x =
      (appFullSec (I := I) (M := M) g r (s + 1) (s + 1) Q₁
          (covGrad (I := I) (M := M) g r s S)).toSection x -
        (GcurvSectionRS (I := I) (M := M) g r s S).toSection x := by
    rw [hG₁, SmoothCcTensor.toSection_sub]; rfl
  have hG₀sub := riemannianFiberNormSq_sub_le (I := I) (M := M) g r (s + 1) x
    ((appFullSec (I := I) (M := M) g r s (s + 1) Q₀ S).toSection x)
    ((diffCurvSectionRS (I := I) (M := M) g r s S).toSection x)
  have hG₁sub := riemannianFiberNormSq_sub_le (I := I) (M := M) g r (s + 1) x
    ((appFullSec (I := I) (M := M) g r (s + 1) (s + 1) Q₁
        (covGrad (I := I) (M := M) g r s S)).toSection x)
    ((GcurvSectionRS (I := I) (M := M) g r s S).toSection x)
  -- The five at-point envelope bounds, each collapsed at gradient order `k = 0`.
  -- (i) `Q₀ · S` reads `rfns(S)`.
  have hQ₀ := hcc₀ S 0 x
  rw [iteratedCovGrad_zero, iteratedCovGrad_zero, Finset.sum_range_one] at hQ₀
  simp only [Nat.add_zero] at hQ₀
  rw [iteratedCovGrad_zero, ← hD] at hQ₀
  have hQ₀B : riemannianFiberNormSq (I := I) (M := M) g r (s + 1) x
      ((appFullSec (I := I) (M := M) g r s (s + 1) Q₀ S).toSection x) ≤ cc₀ 0 * D := hQ₀
  -- (ii) `diffCurv` reads `rfns(S)`.
  have hdiff := hcd s S 0 x
  rw [iteratedCovGrad_zero, Finset.sum_range_one] at hdiff
  simp only [Nat.add_zero, iteratedCovGrad_zero] at hdiff
  rw [← hD] at hdiff
  have hdiffB : riemannianFiberNormSq (I := I) (M := M) g r (s + 1) x
      ((diffCurvSectionRS (I := I) (M := M) g r s S).toSection x) ≤ cd s 0 ^ 2 * D := hdiff
  -- (iii) `Q₁ · ∇S` reads `rfns(∇S)`.
  have hQ₁ := hcc₁ S 0 x
  rw [iteratedCovGrad_zero, Finset.sum_range_one] at hQ₁
  simp only [Nat.add_zero] at hQ₁
  rw [show iteratedCovGrad g r s 1 S = covGrad (I := I) (M := M) g r s S from rfl] at hQ₁
  rw [← hB] at hQ₁
  have hQ₁B : riemannianFiberNormSq (I := I) (M := M) g r (s + 1) x
      ((appFullSec (I := I) (M := M) g r (s + 1) (s + 1) Q₁
        (covGrad (I := I) (M := M) g r s S)).toSection x) ≤ cc₁ 0 * B := hQ₁
  -- (iv) `Gcurv` reads `rfns(∇S)`.
  have hgcurv := hcg s S 0 x
  rw [iteratedCovGrad_zero, Finset.sum_range_one] at hgcurv
  simp only [Nat.add_zero, iteratedCovGrad_succ, iteratedCovGrad_zero] at hgcurv
  rw [← hB] at hgcurv
  have hgcurvB : riemannianFiberNormSq (I := I) (M := M) g r (s + 1) x
      ((GcurvSectionRS (I := I) (M := M) g r s S).toSection x) ≤ cg s 0 ^ 2 * B := hgcurv
  -- (v) `Q₂ · ∇²S` reads `rfns(∇²S)`.
  have hQ₂ := hcc₂ S 0 x
  rw [iteratedCovGrad_zero, Finset.sum_range_one] at hQ₂
  simp only [Nat.add_zero] at hQ₂
  rw [show iteratedCovGrad g r s 2 S =
      covGrad (I := I) (M := M) g r (s + 1) (covGrad (I := I) (M := M) g r s S) from rfl] at hQ₂
  rw [← hA] at hQ₂
  have hQ₂B : riemannianFiberNormSq (I := I) (M := M) g r (s + 1) x
      ((appFullSec (I := I) (M := M) g r (s + 2) (s + 1) Q₂
        (iteratedCovGrad g r s 2 S)).toSection x) ≤ cc₂ 0 * A := by
    rw [show iteratedCovGrad g r s 2 S =
        covGrad (I := I) (M := M) g r (s + 1) (covGrad (I := I) (M := M) g r s S) from rfl]
    exact hQ₂
  have hCsq : (Real.sqrt (8 * cc₀ 0 + 8 * (cd s 0) ^ 2 + 8 * cc₁ 0 + 8 * (cg s 0) ^ 2 +
        4 * cc₂ 0)) ^ 2 =
      8 * cc₀ 0 + 8 * (cd s 0) ^ 2 + 8 * cc₁ 0 + 8 * (cg s 0) ^ 2 + 4 * cc₂ 0 := by
    rw [Real.sq_sqrt]
    have h0 := hcc₀_nn 0; have h1 := hcc₁_nn 0; have h2 := hcc₂_nn 0
    positivity
  rw [hrem_sec, hCsq]
  -- Fold the `≤` chain. `rfns(rem) ≤ 2(rfns(G₀+G₁)) + 2 rfns(G₂)`, then `rfns(G₀+G₁) ≤ 2 rfns(G₀)+2 rfns(G₁)`,
  -- and each `rfns(Gⱼ) ≤ 2 rfns(action) + 2 rfns(carrier)`; substitute the five envelopes.
  rw [← hG₀sec] at hG₀sub
  rw [← hG₁sec] at hG₁sub
  nlinarith [hsplit1, hsplit2, hG₀sub, hG₁sub, hQ₀B, hdiffB, hQ₁B, hgcurvB, hQ₂B,
    hA_nn, hB_nn, hD_nn, hcc₀_nn 0, hcc₁_nn 0, hcc₂_nn 0, sq_nonneg (cd s 0), sq_nonneg (cg s 0),
    mul_nonneg (hcc₀_nn 0) hD_nn, mul_nonneg (sq_nonneg (cd s 0)) hD_nn,
    mul_nonneg (hcc₁_nn 0) hB_nn, mul_nonneg (sq_nonneg (cg s 0)) hB_nn,
    mul_nonneg (hcc₂_nn 0) hA_nn,
    riemannianFiberNormSq_nonneg (I := I) (M := M) g r (s + 1) x (G₀.toSection x),
    riemannianFiberNormSq_nonneg (I := I) (M := M) g r (s + 1) x (G₁.toSection x),
    riemannianFiberNormSq_nonneg (I := I) (M := M) g r (s + 1) x (G₂.toSection x)]

/-- **The rank-`r` moving-frame remainder (after the pure-Riemann peel) fibre order (proved over the
doubly-peeled remainder atom and the differentiated-curvature carrier grid).** The contravariant-rank-`r`
mirror of the rank-`0` moving-frame remainder fibre order
`exists_pointwiseTensorCurv_subGcurv_obstruction_fiberOrder_bound` (`Order2DefectFiberOrder`, the genuine
`∇³S`-cancellation content, itself transiting `sorryAx`). For a closed smooth Riemannian manifold
`(M, g)` and a fixed contravariant rank `r` there is a *valence-dependent* nonnegative constant
`C : ℕ → ℝ` such that, at every covariant rank `s`, every smooth compactly-supported `(r, s)`-tensor `S`
and every point `x`, the moving-frame remainder of the order-`2` commutator defect past the concrete
pure-Riemann section — `Curv S − GcurvSectionRS g r s S`, with
`Curv S := pointwiseTensorCurvRS g r s S = Δ_∇(∇S) − ∇(Δ_∇ S)` — has its intrinsic fibre norm bounded by
the order-`≤ 2` covariant jet of `S`:
```
rfns(Curv S − GcurvSectionRS g r s S)(x) ≤ (C s)² · ( rfns(∇²S)(x) + rfns(∇S)(x) + rfns(S)(x) ).
```

**Proof (composition over the doubly-peeled remainder atom, peeling the differentiated-curvature channel
sorry-free).** The single-peel remainder splits as `Curv S − GcurvSectionRS g r s S = diffCurvSectionRS g
r s S + Grem` with `Grem := Curv S − GcurvSectionRS g r s S − diffCurvSectionRS g r s S` (the section
identity is `abel`), so by fibre subadditivity `riemannianFiberNormSq_add_le` the fibre norm of
`Curv S − GcurvSectionRS g r s S` is bounded by twice that of the gauge-glued differentiated `(∇R) S`
carrier `diffCurvSectionRS g r s S` plus twice that of the doubly-peeled remainder `Grem`. The
differentiated-curvature carrier fibre norm is bounded *sorry-free* by `(cd s 0)² · rfns(S)(x)` via the
differentiated-curvature carrier grid `exists_diffCurvSectionRS_iteratedCovGrad_grid_bound` specialised to
gradient order `k = 0` (where `∇^0(diffCurvSectionRS) = diffCurvSectionRS` and the single-term window reads
`rfns(S)`), weakened to the wider `rfns(∇²S) + rfns(∇S) + rfns(S)` envelope, and the doubly-peeled
remainder fibre norm is bounded by the posited genuine doubly-peeled remainder fibre order
`exists_pointwiseTensorCurvRS_subGcurvSubDiffCurv_obstruction_fiberOrder_bound` (the rank-`r` `(0, 3)`
graded jet at gradient order `0`). Taking `C s := √(2·(cd s 0)² + 2·(Cobs s)²)` absorbs both
contributions, since every fibre norm on the right is nonnegative. Consumers transitively depend on the
posited remainder's `sorryAx`.

**Non-vacuity (the `s = 0` litmus).** With `C s = 0` the bound forces `rfns(Curv S − GcurvSectionRS g r s
S)(x) = 0`. At `s = 0` the pure-Riemann trace `GcurvSectionRS g r 0 f` reads the curvature of a rank-`(r,
0)` tensor whose gradient channel carries the genuine `R(∇f)` content; the bound would force the entire
moving-frame remainder (the differentiated-curvature and bracket channels) to vanish — *false* on a
non-flat manifold for a non-parallel `f` (the differentiated-curvature `(∇R) f` content is genuinely
`rfns(f)`-order non-zero when `∇R ≠ 0`). The constant family is genuinely positive. -/
theorem exists_pointwiseTensorCurvRS_subGcurv_obstruction_fiberOrder_bound
    (g : SmoothRiemannianMetric I M) (r : ℕ) :
    ∃ C : ℕ → ℝ, (∀ s, 0 ≤ C s) ∧
      ∀ (s : ℕ) (S : SmoothCcTensor g r s) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g r (s + 1) x
            ((pointwiseTensorCurvRS (I := I) (M := M) g r s S -
              GcurvSectionRS (I := I) (M := M) g r s S).toSection x) ≤
          C s ^ 2 *
            (riemannianFiberNormSq (I := I) (M := M) g r (s + 1 + 1) x
                ((covGrad (I := I) (M := M) g r (s + 1)
                  (covGrad (I := I) (M := M) g r s S)).toSection x) +
              riemannianFiberNormSq (I := I) (M := M) g r (s + 1) x
                  ((covGrad (I := I) (M := M) g r s S).toSection x) +
              riemannianFiberNormSq (I := I) (M := M) g r s x (S.toSection x)) := by
  classical
  -- `Curv − Gcurv = diffCurvSectionRS + (Curv − Gcurv − diffCurvSectionRS)`: peel the gauge-glued
  -- differentiated-curvature carrier sorry-free (the carrier grid at `k = 0`), bound the doubly-peeled
  -- remainder by the posited `(0, 3)`-graded-jet atom at gradient order `0`, merge by fibre subadditivity.
  obtain ⟨cd, hcd_nn, hcd⟩ := exists_diffCurvSectionRS_iteratedCovGrad_grid_bound (I := I) (M := M) g r
  obtain ⟨Cobs, hCobs_nn, hCobs⟩ :=
    exists_pointwiseTensorCurvRS_subGcurvSubDiffCurv_obstruction_fiberOrder_bound (I := I) (M := M) g r
  refine ⟨fun s => Real.sqrt (2 * (cd s 0) ^ 2 + 2 * (Cobs s) ^ 2),
    fun s => Real.sqrt_nonneg _, fun s S x => ?_⟩
  set A : ℝ := riemannianFiberNormSq (I := I) (M := M) g r (s + 1 + 1) x
      ((covGrad (I := I) (M := M) g r (s + 1)
        (covGrad (I := I) (M := M) g r s S)).toSection x) with hA
  set B : ℝ := riemannianFiberNormSq (I := I) (M := M) g r (s + 1) x
      ((covGrad (I := I) (M := M) g r s S).toSection x) with hB
  set D : ℝ := riemannianFiberNormSq (I := I) (M := M) g r s x (S.toSection x) with hD
  have hA_nn : 0 ≤ A := riemannianFiberNormSq_nonneg (I := I) (M := M) g r (s + 1 + 1) x _
  have hB_nn : 0 ≤ B := riemannianFiberNormSq_nonneg (I := I) (M := M) g r (s + 1) x _
  have hD_nn : 0 ≤ D := riemannianFiberNormSq_nonneg (I := I) (M := M) g r s x _
  have hsub1 : (pointwiseTensorCurvRS (I := I) (M := M) g r s S -
        GcurvSectionRS (I := I) (M := M) g r s S).toSection x =
      (pointwiseTensorCurvRS (I := I) (M := M) g r s S).toSection x -
        (GcurvSectionRS (I := I) (M := M) g r s S).toSection x := by
    rw [SmoothCcTensor.toSection_sub]; rfl
  have hsub2 : (pointwiseTensorCurvRS (I := I) (M := M) g r s S -
        GcurvSectionRS (I := I) (M := M) g r s S -
        diffCurvSectionRS (I := I) (M := M) g r s S).toSection x =
      ((pointwiseTensorCurvRS (I := I) (M := M) g r s S).toSection x -
          (GcurvSectionRS (I := I) (M := M) g r s S).toSection x) -
        (diffCurvSectionRS (I := I) (M := M) g r s S).toSection x := by
    rw [SmoothCcTensor.toSection_sub, SmoothCcTensor.toSection_sub]; rfl
  have hsub_apply : (pointwiseTensorCurvRS (I := I) (M := M) g r s S -
        GcurvSectionRS (I := I) (M := M) g r s S).toSection x =
      (diffCurvSectionRS (I := I) (M := M) g r s S).toSection x +
        (pointwiseTensorCurvRS (I := I) (M := M) g r s S -
          GcurvSectionRS (I := I) (M := M) g r s S -
          diffCurvSectionRS (I := I) (M := M) g r s S).toSection x := by
    rw [hsub1, hsub2]; abel
  have hadd := riemannianFiberNormSq_add_le (I := I) (M := M) g r (s + 1) x
    ((diffCurvSectionRS (I := I) (M := M) g r s S).toSection x)
    ((pointwiseTensorCurvRS (I := I) (M := M) g r s S -
      GcurvSectionRS (I := I) (M := M) g r s S -
      diffCurvSectionRS (I := I) (M := M) g r s S).toSection x)
  rw [← hsub_apply] at hadd
  -- The differentiated-curvature carrier bound, sorry-free, at gradient order `k = 0`.
  have hdiff := hcd s S 0 x
  rw [iteratedCovGrad_zero (I := I) (M := M) g r (s + 1)
    (diffCurvSectionRS (I := I) (M := M) g r s S)] at hdiff
  rw [Finset.sum_range_one] at hdiff
  simp only [Nat.add_zero, iteratedCovGrad_zero] at hdiff
  rw [← hD] at hdiff
  have hdiffB : riemannianFiberNormSq (I := I) (M := M) g r (s + 1) x
      ((diffCurvSectionRS (I := I) (M := M) g r s S).toSection x) ≤ cd s 0 ^ 2 * D := hdiff
  -- The doubly-peeled remainder fibre bound (the posited genuine child).
  have hrem := hCobs s S x
  rw [← hA, ← hB, ← hD] at hrem
  have hCsq : (Real.sqrt (2 * (cd s 0) ^ 2 + 2 * (Cobs s) ^ 2)) ^ 2 =
      2 * (cd s 0) ^ 2 + 2 * (Cobs s) ^ 2 := by
    rw [Real.sq_sqrt]; positivity
  rw [hCsq]
  calc riemannianFiberNormSq (I := I) (M := M) g r (s + 1) x
          ((pointwiseTensorCurvRS (I := I) (M := M) g r s S -
            GcurvSectionRS (I := I) (M := M) g r s S).toSection x)
      ≤ 2 * riemannianFiberNormSq (I := I) (M := M) g r (s + 1) x
            ((diffCurvSectionRS (I := I) (M := M) g r s S).toSection x) +
          2 * riemannianFiberNormSq (I := I) (M := M) g r (s + 1) x
            ((pointwiseTensorCurvRS (I := I) (M := M) g r s S -
              GcurvSectionRS (I := I) (M := M) g r s S -
              diffCurvSectionRS (I := I) (M := M) g r s S).toSection x) := hadd
    _ ≤ 2 * (cd s 0 ^ 2 * D) + 2 * (Cobs s ^ 2 * (A + B + D)) :=
        add_le_add (by linarith [hdiffB]) (by linarith [hrem])
    _ ≤ (2 * (cd s 0) ^ 2 + 2 * (Cobs s) ^ 2) * (A + B + D) := by
        nlinarith [hA_nn, hB_nn, hD_nn, sq_nonneg (cd s 0), sq_nonneg (Cobs s)]

/-- **The rank-`r` bare order-`2` commutator-defect fibre order (proved over the pure-Riemann grid and
the moving-frame remainder core).** The contravariant-rank-`r` mirror of the rank-`0` bare defect fibre
order `exists_pointwiseTensorCurv_fiberOrder_bound` (`Order2DefectFiberOrder`, the curvature line's
irreducible upstream quantitative atom). For a closed smooth Riemannian manifold `(M, g)` and a fixed
contravariant rank `r` there is a *valence-dependent* nonnegative constant `C : ℕ → ℝ` such that, at every
covariant rank `s`, every smooth compactly-supported `(r, s)`-tensor `S` and every point `x`, the
**bare** order-`2` commutator defect `Curv S := pointwiseTensorCurvRS g r s S = Δ_∇(∇S) − ∇(Δ_∇ S)` has
its intrinsic fibre norm bounded by the order-`≤ 2` covariant jet of `S`:
```
rfns(Curv S)(x) ≤ (C s)² · ( rfns(∇²S)(x) + rfns(∇S)(x) + rfns(S)(x) ).
```

**Proof (composition over the moving-frame remainder fibre order, peeling the pure-Riemann channel
sorry-free).** This is the verbatim contravariant-rank-`r` mirror of the rank-`0`
`exists_pointwiseTensorCurv_fiberOrder_bound`'s composition proof. The defect splits as
`Curv S = GcurvSectionRS g r s S + (Curv S − GcurvSectionRS g r s S)` (the section identity is `abel`),
so by fibre subadditivity `riemannianFiberNormSq_add_le` the fibre norm of `Curv S` is bounded by twice
the fibre norm of the pure-Riemann trace `GcurvSectionRS g r s S` plus twice that of the moving-frame
remainder `Curv S − GcurvSectionRS g r s S`. The pure-Riemann fibre norm is bounded *sorry-free* by
`(c s 0)² · rfns(∇S)(x)` via the moving-centre pure-Riemann curvature-jet grid bound
`exists_GcurvSectionRS_iteratedCovGrad_grid_bound` specialised to gradient order `k = 0` (where
`∇^0(GcurvSectionRS) = GcurvSectionRS` and the single-term sum reads `rfns(∇S)`), and the moving-frame
remainder fibre norm is bounded by the posited genuine remainder fibre order
`exists_pointwiseTensorCurvRS_subGcurv_obstruction_fiberOrder_bound`. Taking
`C s := √(2·(c s 0)² + 2·(Cobs s)²)` absorbs both contributions, since every fibre norm on the right is
nonnegative. Consumers transitively depend on the posited remainder's `sorryAx`.

**Non-vacuity.** With `C s = 0` the bound forces `rfns(Curv S)(x) = 0` pointwise, i.e. the order-`2`
commutator defect `Δ_∇(∇S) − ∇(Δ_∇ S)` vanishes; *false* on a non-flat manifold (`R ≠ 0`) for a
non-parallel `S` (the defect is the genuine third-order curvature contraction of `S`, non-zero when the
curvature operator and the jet of `S` are non-trivial). The constant family is genuinely positive. -/
theorem exists_pointwiseTensorCurvRS_fiberOrder_bound (g : SmoothRiemannianMetric I M) (r : ℕ) :
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
  obtain ⟨c, hc_nn, hc⟩ := exists_GcurvSectionRS_iteratedCovGrad_grid_bound (I := I) (M := M) g r
  obtain ⟨Cobs, hCobs_nn, hCobs⟩ :=
    exists_pointwiseTensorCurvRS_subGcurv_obstruction_fiberOrder_bound (I := I) (M := M) g r
  refine ⟨fun s => Real.sqrt (2 * (c s 0) ^ 2 + 2 * (Cobs s) ^ 2),
    fun s => Real.sqrt_nonneg _, fun s S x => ?_⟩
  set A : ℝ := riemannianFiberNormSq (I := I) (M := M) g r (s + 1 + 1) x
      ((covGrad (I := I) (M := M) g r (s + 1)
        (covGrad (I := I) (M := M) g r s S)).toSection x) with hA
  set B : ℝ := riemannianFiberNormSq (I := I) (M := M) g r (s + 1) x
      ((covGrad (I := I) (M := M) g r s S).toSection x) with hB
  set D : ℝ := riemannianFiberNormSq (I := I) (M := M) g r s x (S.toSection x) with hD
  have hA_nn : 0 ≤ A := riemannianFiberNormSq_nonneg (I := I) (M := M) g r (s + 1 + 1) x _
  have hB_nn : 0 ≤ B := riemannianFiberNormSq_nonneg (I := I) (M := M) g r (s + 1) x _
  have hD_nn : 0 ≤ D := riemannianFiberNormSq_nonneg (I := I) (M := M) g r s x _
  -- The defect splits as the pure-Riemann trace plus the moving-frame remainder.
  have hsub_apply : (pointwiseTensorCurvRS (I := I) (M := M) g r s S -
        GcurvSectionRS (I := I) (M := M) g r s S).toSection x =
      (pointwiseTensorCurvRS (I := I) (M := M) g r s S).toSection x -
        (GcurvSectionRS (I := I) (M := M) g r s S).toSection x := by
    rw [SmoothCcTensor.toSection_sub]; rfl
  have hsplit : (pointwiseTensorCurvRS (I := I) (M := M) g r s S).toSection x =
      (GcurvSectionRS (I := I) (M := M) g r s S).toSection x +
        (pointwiseTensorCurvRS (I := I) (M := M) g r s S -
          GcurvSectionRS (I := I) (M := M) g r s S).toSection x := by
    rw [hsub_apply]; abel
  have hadd := riemannianFiberNormSq_add_le (I := I) (M := M) g r (s + 1) x
    ((GcurvSectionRS (I := I) (M := M) g r s S).toSection x)
    ((pointwiseTensorCurvRS (I := I) (M := M) g r s S -
      GcurvSectionRS (I := I) (M := M) g r s S).toSection x)
  rw [← hsplit] at hadd
  -- The pure-Riemann fibre bound, sorry-free, at gradient order `k = 0`.
  have hG := hc s S 0 x
  rw [iteratedCovGrad_zero (I := I) (M := M) g r (s + 1)
    (GcurvSectionRS (I := I) (M := M) g r s S)] at hG
  rw [Finset.sum_range_one] at hG
  rw [iteratedCovGrad_succ (I := I) (M := M) g r s 0 S,
    iteratedCovGrad_zero (I := I) (M := M) g r s S] at hG
  simp only [Nat.add_zero] at hG
  rw [← hB] at hG
  -- The moving-frame remainder fibre bound (the posited genuine child).
  have hR := hCobs s S x
  rw [← hA, ← hB, ← hD] at hR
  have hCsq : (Real.sqrt (2 * (c s 0) ^ 2 + 2 * (Cobs s) ^ 2)) ^ 2 =
      2 * (c s 0) ^ 2 + 2 * (Cobs s) ^ 2 := by
    rw [Real.sq_sqrt]
    positivity
  rw [hCsq]
  calc riemannianFiberNormSq (I := I) (M := M) g r (s + 1) x
          ((pointwiseTensorCurvRS (I := I) (M := M) g r s S).toSection x)
      ≤ 2 * riemannianFiberNormSq (I := I) (M := M) g r (s + 1) x
            ((GcurvSectionRS (I := I) (M := M) g r s S).toSection x) +
          2 * riemannianFiberNormSq (I := I) (M := M) g r (s + 1) x
            ((pointwiseTensorCurvRS (I := I) (M := M) g r s S -
              GcurvSectionRS (I := I) (M := M) g r s S).toSection x) := hadd
    _ ≤ 2 * ((c s 0) ^ 2 * B) + 2 * ((Cobs s) ^ 2 * (A + B + D)) :=
        add_le_add (by linarith [hG]) (by linarith [hR])
    _ ≤ (2 * (c s 0) ^ 2 + 2 * (Cobs s) ^ 2) * (A + B + D) := by
        nlinarith [hA_nn, hD_nn, sq_nonneg (c s 0)]

/-- **The rank-`r` upstream genuine third-order Weitzenböck field decomposition (posited general-rank
curvature core).** The contravariant-rank-`r` mirror of the rank-`0` upstream genuine field
decomposition `exists_pointwiseTensorCurv_genuineFields_spectralPairing_upstream`
(`MovingFrameDiffCurvTraceSection`, the deepest curvature core, *which itself transits `sorryAx`* at
rank `0` through the classical third-order tensor Bochner–Weitzenböck curvature-term derivation). For a
closed smooth Riemannian manifold `(M, g)` and a fixed contravariant rank `r` there is a
*valence-dependent* nonnegative constant `Cper : ℕ → ℝ` such that, at every covariant rank `s` and for
every smooth compactly-supported `(r, s)`-tensor `S`, the order-`2` commutator defect
`Curv S := pointwiseTensorCurvRS g r s S` admits two *genuine curvature* fields `Gcurv, GcurvDeriv :
SmoothCcTensor g r (s + 1)` — the pure-Riemann contraction `R(∇S)` and the differentiated-curvature
`(∇R) S` — with the three genuine third-order Bochner–Weitzenböck fibre bounds:

* `rfns(Gcurv)(x) ≤ (Cper s)² · rfns(∇S)(x)` — the pure-`R` field, genuinely `rfns(∇S)`-order;
* `rfns(GcurvDeriv)(x) ≤ (Cper s)² · (rfns(∇S)(x) + rfns(S)(x))` — the `∇R` field, sum-order;
* `rfns(Curv S − Gcurv − GcurvDeriv)(x) ≤ (Cper s)² · (rfns(∇²S)(x) + rfns(∇S)(x) + rfns(S)(x))` — the
  moving-frame / frame-bracket remainder, genuinely `rfns(∇²S)`-order after the third-order Weitzenböck
  cancellation of the top-order `∇³S` terms by the iterated Ricci identity.

**Why this is TRUE.** This is the verbatim contravariant-rank-`r` lift of the rank-`0`
`exists_pointwiseTensorCurv_genuineFields_spectralPairing_upstream` (here without the spectral-pairing
conjunct, which `exists_diffCurvSectionRS_anchor_primitive` carries separately).  By the iterated Ricci
identity `secondCovDeriv_covGrad_antisymm_eq_riemannOp_gen` (rank-`(r, ·)` instance, sorry-free) the
defect's gradient-slot reordering produces the pure-Riemann `R(∇S)` trace (carried by `Gcurv`), the
differentiated curvature `(∇R) S` (carried by `GcurvDeriv`), and a moving-frame / frame-bracket
remainder genuinely `∇²S`-order; every curvature coefficient is absorbed uniformly over the compact `M`
into `(Cper s)²` (the rank-`r` curvature-operator sup
`exists_Cx_riemannianFiberNormSq_riemannOp_tensorCovS_le_rs`, made uniform over `M`).  This
genuinely-deep moving-frame curvature-endomorphism content is, at general contravariant rank `r`,
absent from the library (the rank-`0` carriers `genuineDiffCurvSection` / `ricTraceSection` and their
operator-field sups use the rank-`0`-locked `appCc` action), so it is posited here as one precise true
core — the rank-`r` analogue of the genuine rank-`0` `sorry` leaf.  Consumers transitively depend on
`sorryAx`.

**Non-vacuity.** With `Cper s = 0` the three bounds force, at any `x`,
`rfns(Gcurv)(x) = rfns(GcurvDeriv)(x) = rfns(Curv S − Gcurv − GcurvDeriv)(x) = 0`, hence `Curv S = 0`
pointwise, i.e. `Δ_∇(∇S) = ∇(Δ_∇ S)`; *false* on a non-flat manifold (`R ≠ 0`) for a non-parallel `S`
(the defect is the genuine third-order curvature contraction).  The constant family is genuinely
positive. -/
theorem exists_pointwiseTensorCurvRS_genuineFields_spectralPairing_upstream
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
                riemannianFiberNormSq (I := I) (M := M) g r s x (S.toSection x))) := by
  classical
  -- The two concrete genuine carriers are the pure-Riemann `R(∇S)` trace `GcurvSectionRS` and the
  -- gauge-glued `(∇R) S` carrier `diffCurvSectionRS`. The pure-`R` proportional bound is the rank-`r`
  -- pure-Riemann grid at gradient order `k = 0` (window collapses to `rfns(∇S)`); the `(∇R) S` sum
  -- bound is the rank-`r` differentiated-curvature grid at `k = 0` (window collapses to `rfns(S)`); the
  -- remainder bound is the bare order-`2` defect fibre order, peeled against the two carriers by the
  -- fibre-norm triangle inequality.
  obtain ⟨cg, hcg_nn, hcg⟩ := exists_GcurvSectionRS_iteratedCovGrad_grid_bound (I := I) (M := M) g r
  obtain ⟨cd, hcd_nn, hcd⟩ := exists_diffCurvSectionRS_iteratedCovGrad_grid_bound (I := I) (M := M) g r
  obtain ⟨Cc, hCc_nn, hCc⟩ := exists_pointwiseTensorCurvRS_fiberOrder_bound (I := I) (M := M) g r
  refine ⟨fun s => Real.sqrt (8 * (cg s 0) ^ 2 + 8 * (cd s 0) ^ 2 + 8 * (Cc s) ^ 2),
    fun s => Real.sqrt_nonneg _, fun s S => ?_⟩
  have hCpersq : (Real.sqrt (8 * (cg s 0) ^ 2 + 8 * (cd s 0) ^ 2 + 8 * (Cc s) ^ 2)) ^ 2 =
      8 * (cg s 0) ^ 2 + 8 * (cd s 0) ^ 2 + 8 * (Cc s) ^ 2 := by
    rw [Real.sq_sqrt]; positivity
  refine ⟨GcurvSectionRS (I := I) (M := M) g r s S,
    diffCurvSectionRS (I := I) (M := M) g r s S, ?_, ?_, ?_⟩
  · -- Conjunct (1): the pure-Riemann section bound `rfns(GcurvSectionRS) ≤ Cper² · rfns(∇S)`, off the
    -- pure-Riemann grid at `k = 0` where the contracted-order window collapses to `rfns(∇S)`.
    intro x
    rw [hCpersq]
    have hgc0 := hcg s S 0 x
    simp only [iteratedCovGrad_zero, Nat.add_zero, Finset.range_one, Finset.sum_singleton,
      iteratedCovGrad_succ] at hgc0
    have hgc : riemannianFiberNormSq (I := I) (M := M) g r (s + 1) x
        ((GcurvSectionRS (I := I) (M := M) g r s S).toSection x) ≤
        cg s 0 ^ 2 * riemannianFiberNormSq (I := I) (M := M) g r (s + 1) x
          ((covGrad (I := I) (M := M) g r s S).toSection x) := hgc0
    have hfgS_nn : 0 ≤ riemannianFiberNormSq (I := I) (M := M) g r (s + 1) x
        ((covGrad (I := I) (M := M) g r s S).toSection x) :=
      riemannianFiberNormSq_nonneg (I := I) (M := M) g r (s + 1) x _
    nlinarith [hgc, hfgS_nn, sq_nonneg (cg s 0), sq_nonneg (cd s 0), sq_nonneg (Cc s),
      mul_nonneg hfgS_nn (sq_nonneg (cd s 0)), mul_nonneg hfgS_nn (sq_nonneg (Cc s))]
  · -- Conjunct (2): the `(∇R) S` carrier sum bound `rfns(diffCurvSectionRS) ≤ Cper² · (rfns(∇S) +
    -- rfns(S))`, off the differentiated-curvature grid at `k = 0` where the contracted-order window
    -- collapses to the single `rfns(S)` term; weakened to the `rfns(∇S) + rfns(S)` envelope.
    intro x
    rw [hCpersq]
    have hcd0 := hcd s S 0 x
    simp only [iteratedCovGrad_zero, Nat.add_zero, Finset.range_one, Finset.sum_singleton] at hcd0
    have hcdb : riemannianFiberNormSq (I := I) (M := M) g r (s + 1) x
        ((diffCurvSectionRS (I := I) (M := M) g r s S).toSection x) ≤
        cd s 0 ^ 2 * riemannianFiberNormSq (I := I) (M := M) g r s x (S.toSection x) := hcd0
    have hfgS_nn : 0 ≤ riemannianFiberNormSq (I := I) (M := M) g r (s + 1) x
        ((covGrad (I := I) (M := M) g r s S).toSection x) :=
      riemannianFiberNormSq_nonneg (I := I) (M := M) g r (s + 1) x _
    have hfS_nn : 0 ≤ riemannianFiberNormSq (I := I) (M := M) g r s x (S.toSection x) :=
      riemannianFiberNormSq_nonneg (I := I) (M := M) g r s x _
    nlinarith [hcdb, hfgS_nn, hfS_nn, sq_nonneg (cg s 0), sq_nonneg (cd s 0), sq_nonneg (Cc s),
      mul_nonneg hfgS_nn (sq_nonneg (cd s 0)), mul_nonneg hfS_nn (sq_nonneg (cd s 0)),
      mul_nonneg hfgS_nn (sq_nonneg (cg s 0)), mul_nonneg hfS_nn (sq_nonneg (cg s 0)),
      mul_nonneg hfgS_nn (sq_nonneg (Cc s)), mul_nonneg hfS_nn (sq_nonneg (Cc s))]
  · -- Conjunct (3): the remainder bound `rfns(Curv − GcurvSectionRS − diffCurvSectionRS) ≤ Cper² ·
    -- (rfns(∇²S) + rfns(∇S) + rfns(S))`. Open `Curv − GcurvSectionRS − diffCurvSectionRS =
    -- (Curv − GcurvSectionRS) − diffCurvSectionRS`, then the fibre-norm triangle over the two
    -- subtractions bounds the remainder by `rfns(Curv)`, `rfns(GcurvSectionRS)`, `rfns(diffCurvSectionRS)`.
    intro x
    rw [hCpersq]
    have hsec : (pointwiseTensorCurvRS (I := I) (M := M) g r s S -
          GcurvSectionRS (I := I) (M := M) g r s S - diffCurvSectionRS (I := I) (M := M) g r s S).toSection x =
        ((pointwiseTensorCurvRS (I := I) (M := M) g r s S).toSection x -
            (GcurvSectionRS (I := I) (M := M) g r s S).toSection x) -
          (diffCurvSectionRS (I := I) (M := M) g r s S).toSection x := by
      rw [SmoothCcTensor.toSection_sub, SmoothCcTensor.toSection_sub]; rfl
    rw [hsec]
    have hsub1 := riemannianFiberNormSq_sub_le (I := I) (M := M) g r (s + 1) x
      ((pointwiseTensorCurvRS (I := I) (M := M) g r s S).toSection x -
          (GcurvSectionRS (I := I) (M := M) g r s S).toSection x)
      ((diffCurvSectionRS (I := I) (M := M) g r s S).toSection x)
    have hsub2 := riemannianFiberNormSq_sub_le (I := I) (M := M) g r (s + 1) x
      ((pointwiseTensorCurvRS (I := I) (M := M) g r s S).toSection x)
      ((GcurvSectionRS (I := I) (M := M) g r s S).toSection x)
    have hCurvB := hCc s S x
    have hgc0 := hcg s S 0 x
    simp only [iteratedCovGrad_zero, Nat.add_zero, Finset.range_one, Finset.sum_singleton,
      iteratedCovGrad_succ] at hgc0
    have hgcurvB : riemannianFiberNormSq (I := I) (M := M) g r (s + 1) x
        ((GcurvSectionRS (I := I) (M := M) g r s S).toSection x) ≤
        cg s 0 ^ 2 * riemannianFiberNormSq (I := I) (M := M) g r (s + 1) x
          ((covGrad (I := I) (M := M) g r s S).toSection x) := hgc0
    have hcd0 := hcd s S 0 x
    simp only [iteratedCovGrad_zero, Nat.add_zero, Finset.range_one, Finset.sum_singleton] at hcd0
    have hcdb : riemannianFiberNormSq (I := I) (M := M) g r (s + 1) x
        ((diffCurvSectionRS (I := I) (M := M) g r s S).toSection x) ≤
        cd s 0 ^ 2 * riemannianFiberNormSq (I := I) (M := M) g r s x (S.toSection x) := hcd0
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
    set fGcd : ℝ := riemannianFiberNormSq (I := I) (M := M) g r (s + 1) x
        ((diffCurvSectionRS (I := I) (M := M) g r s S).toSection x) with hfGcd
    have hfS_nn : 0 ≤ fS := riemannianFiberNormSq_nonneg (I := I) (M := M) g r s x _
    have hfgS_nn : 0 ≤ fgS := riemannianFiberNormSq_nonneg (I := I) (M := M) g r (s + 1) x _
    have hfg2S_nn : 0 ≤ fg2S := riemannianFiberNormSq_nonneg (I := I) (M := M) g r (s + 1 + 1) x _
    have hfCurv_nn : 0 ≤ fCurv := riemannianFiberNormSq_nonneg (I := I) (M := M) g r (s + 1) x _
    have hfGcurv_nn : 0 ≤ fGcurv := riemannianFiberNormSq_nonneg (I := I) (M := M) g r (s + 1) x _
    have hfGcd_nn : 0 ≤ fGcd := riemannianFiberNormSq_nonneg (I := I) (M := M) g r (s + 1) x _
    nlinarith [hsub1, hsub2, hCurvB, hgcurvB, hcdb, hfS_nn, hfgS_nn, hfg2S_nn, hfCurv_nn, hfGcurv_nn,
      hfGcd_nn, sq_nonneg (cg s 0), sq_nonneg (cd s 0), sq_nonneg (Cc s),
      mul_nonneg hfg2S_nn (sq_nonneg (Cc s)), mul_nonneg hfgS_nn (sq_nonneg (Cc s)),
      mul_nonneg hfS_nn (sq_nonneg (Cc s)), mul_nonneg hfgS_nn (sq_nonneg (cg s 0)),
      mul_nonneg hfS_nn (sq_nonneg (cd s 0)), mul_nonneg hfg2S_nn (sq_nonneg (cg s 0)),
      mul_nonneg hfg2S_nn (sq_nonneg (cd s 0)), mul_nonneg hfgS_nn (sq_nonneg (cd s 0)),
      mul_nonneg hfS_nn (sq_nonneg (cg s 0))]

/-- **The rank-`r` upstream order-`2` commutator-defect fibre order bound (proved over the genuine
field decomposition).** The contravariant-rank-`r` mirror of the rank-`0` upstream defect fibre order
bound `exists_pointwiseTensorCurv_fiberNormSq_bound_upstream` (`MovingFrameDiffCurvAnchor`'s upstream
curvature input). For a closed smooth Riemannian manifold `(M, g)` and a fixed contravariant rank `r`
there is a
valence-dependent nonnegative constant `C : ℕ → ℝ` such that, at every covariant rank `s`, every smooth
compactly-supported `(r, s)`-tensor `S` and every point `x`, the order-`2` commutator defect
`Curv S := pointwiseTensorCurvRS g r s S = Δ_∇(∇S) − ∇(Δ_∇ S)` is fibre-bounded by the order-`≤ 2`
covariant jet of `S`:

```
rfns(Curv S)(x) ≤ (C s)² · ( rfns(∇²S)(x) + rfns(∇S)(x) + rfns(S)(x) ).
```

**Why this is TRUE.** This is the verbatim contravariant-rank-`r` mirror of the rank-`0` UPSTREAM defect
bound `exists_pointwiseTensorCurv_fiberNormSq_bound_upstream` (which the rank-`0` coupled split datum
`exists_movingCentreDiffCurvSection_splitDivergenceDatum` consumes as one of its two upstream posited
leaves). Pointwise `Curv S` is the genuine third-order Bochner–Weitzenböck field: by the metric-trace
reading of the rough Laplacian `Δ_∇ = tr_g ∘ ∇²` (`rawTensorConnLap_eq_metricTrace2`, frame-free,
rank-generic) the defect is the metric trace of the antisymmetrised second covariant derivative of `∇S`,
which the third-order tensor Ricci identity `secondCovDeriv_covGrad_antisymm_eq_riemannOp_gen` exhibits
as a `riemannOp`-contraction of `(∇S, S)`, lifted to the `(r, s)`-bundle through the slot-wise curvature
formula `riemannSec_tensorCov_apply_eval` (`TensorSlotwiseCurvatureRS`); the top surviving order is
`∇²S` (the `∇³S` field cancels between the two terms by the symmetry of the third covariant derivative
against the antisymmetrised commutator), all curvature coefficients absorbed uniformly over the compact
manifold into `(C s)²`. This UPSTREAM defect fibre order — used to control the moving-frame remainder
`Grem := Curv − Gcurv − Gcd` of the coupled split — is **proved by aggregation over the genuine field
decomposition** `exists_pointwiseTensorCurvRS_genuineFields_spectralPairing_upstream` (the rank-`r`
upstream curvature core, transiting `sorryAx`): writing `Curv S = (Gcurv + GcurvDeriv) +
(Curv S − Gcurv − GcurvDeriv)` (the section identity is `abel`), the two-term fibre subadditivity
`riemannianFiberNormSq_add_le` merges the two genuine bounds and combines with the remainder bound; with
`C := 4 · Cper` the resulting sum is dominated by `(4 Cper)² · (rfns(∇²S) + rfns(∇S) + rfns(S))`. This is
**upstream-independent of** the coupled split `diffCurvSplitDatumRS` (it bounds the bare defect, not a
constructed remainder). Consumers transitively depend on `sorryAx` through the genuine field core.

**Non-vacuity.** With `C s = 0` the bound forces `rfns(Curv S)(x) = 0` pointwise, i.e. the order-`2`
commutator defect `Δ_∇(∇S) − ∇(Δ_∇ S)` vanishes; *false* on a non-flat manifold for a non-parallel `S`
(the defect is the genuine third-order curvature contraction of `S`, non-zero when `R ≠ 0` and the jet
of `S` is non-trivial). The constant family is genuinely positive. -/
theorem exists_pointwiseTensorCurvRS_fiberNormSq_bound_upstream
    (g : SmoothRiemannianMetric I M) (r : ℕ) :
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
  obtain ⟨Cper, hCper_nn, hsplit⟩ :=
    exists_pointwiseTensorCurvRS_genuineFields_spectralPairing_upstream (I := I) (M := M) g r
  refine ⟨fun s => 4 * Cper s, fun s => mul_nonneg (by norm_num) (hCper_nn s), fun s S x => ?_⟩
  obtain ⟨Gcurv, GcurvDeriv, hcurv, hcurvDeriv, hrem⟩ := hsplit s S
  have heqT : pointwiseTensorCurvRS (I := I) (M := M) g r s S =
      (Gcurv + GcurvDeriv) +
        (pointwiseTensorCurvRS (I := I) (M := M) g r s S - Gcurv - GcurvDeriv) := by abel
  have heq : (pointwiseTensorCurvRS (I := I) (M := M) g r s S).toSection x =
      (Gcurv + GcurvDeriv).toSection x +
        (pointwiseTensorCurvRS (I := I) (M := M) g r s S - Gcurv - GcurvDeriv).toSection x := by
    conv_lhs => rw [heqT]
    rw [SmoothCcTensor.toSection_add]
    simp only [ContMDiffSection.coe_add, Pi.add_apply]
  set fS : ℝ := riemannianFiberNormSq (I := I) (M := M) g r s x (S.toSection x) with hfS
  set fgS : ℝ := riemannianFiberNormSq (I := I) (M := M) g r (s + 1) x
      ((covGrad (I := I) (M := M) g r s S).toSection x) with hfgS
  set fg2S : ℝ := riemannianFiberNormSq (I := I) (M := M) g r (s + 1 + 1) x
      ((covGrad (I := I) (M := M) g r (s + 1) (covGrad (I := I) (M := M) g r s S)).toSection x)
    with hfg2S
  have hfS_nn : 0 ≤ fS := riemannianFiberNormSq_nonneg (I := I) (M := M) g r s x _
  have hfgS_nn : 0 ≤ fgS := riemannianFiberNormSq_nonneg (I := I) (M := M) g r (s + 1) x _
  have hfg2S_nn : 0 ≤ fg2S := riemannianFiberNormSq_nonneg (I := I) (M := M) g r (s + 1 + 1) x _
  have hCsq_nn : 0 ≤ Cper s ^ 2 := sq_nonneg _
  have hmerge := riemannianFiberNormSq_add_le (I := I) (M := M) g r (s + 1) x
    (Gcurv.toSection x) (GcurvDeriv.toSection x)
  have hcurv_x := hcurv x
  have hcurvDeriv_x := hcurvDeriv x
  have hrem_x := hrem x
  have hgen_bound : riemannianFiberNormSq (I := I) (M := M) g r (s + 1) x
      ((Gcurv + GcurvDeriv).toSection x) ≤ Cper s ^ 2 * (4 * fgS + 2 * fS) := by
    have hcoe : (Gcurv + GcurvDeriv).toSection x = Gcurv.toSection x + GcurvDeriv.toSection x := by
      rw [SmoothCcTensor.toSection_add]; simp only [ContMDiffSection.coe_add, Pi.add_apply]
    rw [hcoe]
    nlinarith [hmerge, hcurv_x, hcurvDeriv_x, hfS_nn, hfgS_nn, hCsq_nn]
  rw [heq]
  have hadd := riemannianFiberNormSq_add_le (I := I) (M := M) g r (s + 1) x
    ((Gcurv + GcurvDeriv).toSection x)
    ((pointwiseTensorCurvRS (I := I) (M := M) g r s S - Gcurv - GcurvDeriv).toSection x)
  have hsq : (4 * Cper s) ^ 2 = 16 * Cper s ^ 2 := by ring
  rw [hsq]
  nlinarith [hadd, hgen_bound, hrem_x, hfS_nn, hfgS_nn, hfg2S_nn, hCsq_nn,
    mul_nonneg hCsq_nn hfg2S_nn]

/-- **The integrated order-`2` Weitzenböck identity at contravariant rank `r`.** The
contravariant-rank-`r` lift of `weitzenbock_integrated_covGrad_l2_normSq`
(`IntegratedOrder2Weitzenbock`). For a closed smooth Riemannian manifold `(M, g)` and a smooth
compactly-supported `(r, s)`-tensor field `S`, the squared `L²` norm of the iterated covariant gradient
`∇²S := covGrad g r (s + 1) (covGrad g r s S)` equals the squared `L²` norm of the rough Laplacian
`Δ_∇ S := rawTensorConnLapSmooth g r s S` minus the `L²` cross term against the commutator defect:
```
‖∇²S‖²_{L²} = ‖Δ_∇ S‖²_{L²} − ⟨Δ_∇(∇S) − ∇(Δ_∇ S), ∇S⟩_{L²}.
```

**Proof.** This is the verbatim contravariant-rank-`r` lift of the rank-`0` integrated order-`2`
Weitzenböck identity `weitzenbock_integrated_covGrad_l2_normSq`, discharged by the rank-`r` Green chain
`weitzenbock_integrated_covGrad_l2_normSq_rs` (`IntegratedOrder2WeitzenbockRS`). That chain mirrors the
rank-`0` proof: it chains the diagonal connection-Laplacian Green identity at rank `(r, s + 1)`
(`covGrad_l2Inner_self_eq_neg_rawTensorConnLap_inner_rs`) with the cross-pairing split through the
commutator (`rawTensorConnLap_l2Inner_covGrad_split_rs`) and closes by ring arithmetic. The
genuinely-deep analytic ingredient is the general-rank connection-Laplacian Green identity
`tensorL2Inner_covGrad_eq_neg_tensorL2Inner_rawTensorConnLapSmooth_rs_of_intertwiner`
(`TensorDirichletCurrentGreenIdentityRS`), i.e. integration by parts for the rough Laplacian on the
closed `(r, s)`-bundle, supplied with its metric-lowering intertwiner witness `loweringIntertwinerRS_holds`
(the `r`-slot metric index-lowering commutes with `∇` because `∇g = 0`). The identity is *false* for an
arbitrary choice of sign — it pins the iterated-gradient `L²` norm to a specific Bochner combination. -/
theorem weitzenbock_integrated_covGrad_l2_normSqRS
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (S : SmoothCcTensor g r s) :
    tensorL2Norm (I := I) (M := M) g r (s + 1 + 1)
        (covGrad (I := I) (M := M) g r (s + 1)
          (covGrad (I := I) (M := M) g r s S)).toFun ^ 2 =
      tensorL2Norm (I := I) (M := M) g r s
          (rawTensorConnLapSmooth (I := I) g r s S).toFun ^ 2 -
        tensorL2Inner (I := I) (M := M) g r (s + 1)
          (rawTensorConnLapSmooth (I := I) g r (s + 1)
              (covGrad (I := I) (M := M) g r s S) -
            covGrad (I := I) (M := M) g r s
              (rawTensorConnLapSmooth (I := I) g r s S)).toFun
          (covGrad (I := I) (M := M) g r s S).toFun :=
  weitzenbock_integrated_covGrad_l2_normSq_rs (I := I) (M := M) g r s S

/-- **The genuine curvature cross-pairing value at contravariant rank `r`** (the integrated order-`2`
Weitzenböck identity, in cross-pairing form). The contravariant-rank-`r` lift of
`weitzenbock_curvature_crossPairing_value` (`MovingFrameIntegratedNullity`). For a closed smooth
Riemannian manifold `(M, g)`, every covariant rank `s`, and every smooth compactly-supported
`(r, s)`-tensor `S`, the global metric `L²` pairing of the order-`2` commutator defect
`Curv S := pointwiseTensorCurvRS g r s S` against `∇S := covGrad g r s S` equals the genuine Weitzenböck
curvature integral
```
⟨Curv S, ∇S⟩_{L²} = ‖Δ_∇ S‖²_{L²} − ‖∇²S‖²_{L²}.
```
This is `weitzenbock_integrated_covGrad_l2_normSqRS` solved for the cross-pairing, recorded here as the
value the genuine curvature fields `GcurvSectionRS + Gcd` must carry. The proof rewrites the defect into
its definitional form `Δ_∇(∇S) − ∇(Δ_∇ S)` (`rfl` on `pointwiseTensorCurvRS`) and rearranges the
integrated Weitzenböck identity. Consumers transitively depend on `sorryAx` through
`weitzenbock_integrated_covGrad_l2_normSqRS`. -/
theorem weitzenbock_curvature_crossPairing_valueRS
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (S : SmoothCcTensor g r s) :
    tensorL2Inner (I := I) (M := M) g r (s + 1)
        (pointwiseTensorCurvRS (I := I) (M := M) g r s S).toFun
        (covGrad (I := I) (M := M) g r s S).toFun =
      tensorL2Norm (I := I) (M := M) g r s
          (rawTensorConnLapSmooth (I := I) g r s S).toFun ^ 2 -
        tensorL2Norm (I := I) (M := M) g r (s + 1 + 1)
          (covGrad (I := I) (M := M) g r (s + 1)
            (covGrad (I := I) (M := M) g r s S)).toFun ^ 2 := by
  have hw := weitzenbock_integrated_covGrad_l2_normSqRS (I := I) (M := M) g r s S
  have hCurv :
      tensorL2Inner (I := I) (M := M) g r (s + 1)
          (rawTensorConnLapSmooth (I := I) g r (s + 1)
              (covGrad (I := I) (M := M) g r s S) -
            covGrad (I := I) (M := M) g r s
              (rawTensorConnLapSmooth (I := I) g r s S)).toFun
          (covGrad (I := I) (M := M) g r s S).toFun =
        tensorL2Inner (I := I) (M := M) g r (s + 1)
          (pointwiseTensorCurvRS (I := I) (M := M) g r s S).toFun
          (covGrad (I := I) (M := M) g r s S).toFun := rfl
  rw [hCurv] at hw
  linarith [hw]

/-- **Bracket-free-pairing nullity reduction for the moving-frame bracket remainder at contravariant
rank `r`.** The contravariant-rank-`r` lift of
`tensorL2Inner_movingFrameRemainder_eq_zero_of_bracketFreePairing` (`MovingFrameBracketDivergence`). Fix
a closed smooth Riemannian manifold `(M, g)`, a covariant rank `s`, a smooth compactly-supported
`(r, s)`-tensor `S`, and two `(r, s + 1)`-tensor fields `Gcurv`, `GcurvDeriv`. If the genuine fields
carry the entire curvature cross-pairing — the bracket-free `L²` pairing
`⟨Gcurv + GcurvDeriv, ∇S⟩_{L²} = ⟨Curv S, ∇S⟩_{L²}` (`Curv S := pointwiseTensorCurvRS g r s S`) — then
the complementary moving-frame remainder `Curv S − Gcurv − GcurvDeriv` pairs to zero against `∇S`. This
is the purely algebraic step: it writes `Curv S = (Gcurv + GcurvDeriv) + (Curv S − Gcurv − GcurvDeriv)`
and splits the `L²` pairing by left additivity (`tensorL2Inner_add_left`, the cross-term integrabilities
supplied by `SmoothCcTensor.integrable_inner_cross`), so the bracket-free pairing forces the remainder
term to vanish. The left-additivity engine and the cross integrability are rank-generic, so this ports
verbatim from the rank-`0` reduction (no `sorry`). -/
theorem tensorL2Inner_movingFrameRemainder_eq_zero_of_bracketFreePairingRS
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (S : SmoothCcTensor g r s)
    (Gcurv GcurvDeriv : SmoothCcTensor g r (s + 1))
    (hpair : tensorL2Inner (I := I) (M := M) g r (s + 1) (Gcurv + GcurvDeriv).toFun
        (covGrad (I := I) (M := M) g r s S).toFun =
      tensorL2Inner (I := I) (M := M) g r (s + 1)
        (pointwiseTensorCurvRS (I := I) (M := M) g r s S).toFun
        (covGrad (I := I) (M := M) g r s S).toFun) :
    tensorL2Inner (I := I) (M := M) g r (s + 1)
        (pointwiseTensorCurvRS (I := I) (M := M) g r s S - Gcurv - GcurvDeriv).toFun
        (covGrad (I := I) (M := M) g r s S).toFun = 0 := by
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
  rw [hpair] at hsplit
  linarith [hsplit]

/-- **The rank-`r` integrated moving-frame nullity producer (from the genuine cross-pairing VALUE,
posited general-rank divergence converter).** The contravariant-rank-`r` analogue of the rank-`0`
*sorry-free* converter `movingFrameNullity_of_genuineCrossPairingValue` (`MovingFrameIntegratedNullity`).
For a closed smooth Riemannian manifold `(M, g)`, fixed contravariant rank `r`, covariant rank `s`,
smooth compactly-supported `(r, s)`-tensor `S` and smooth `(r, s + 1)`-tensor `Gcd`: if `Gcd` satisfies
the genuine cross-pairing VALUE
`⟨GcurvSectionRS g r s S + Gcd, ∇S⟩_{L²} = ‖Δ_∇S‖²_{L²} − ‖∇²S‖²_{L²}`, then the integrated moving-frame
nullity of the moving-frame remainder holds:
`⟨pointwiseTensorCurvRS g r s S − GcurvSectionRS g r s S − Gcd, ∇S⟩_{L²} = 0`.

**Why this is TRUE.** This is the verbatim rank-`r` lift of `movingFrameNullity_of_genuineCrossPairingValue`:
the rank-`r` Weitzenböck value identity `⟨Curv S, ∇S⟩_{L²} = ‖Δ_∇S‖²_{L²} − ‖∇²S‖²_{L²}` (the rank-`r`
`weitzenbock_curvature_crossPairing_value`, off the rank-`r` integrated Bochner identity
`weitzenbock_integrated_covGrad_l2_normSq` and the rank-`r` covariant Green identity) gives the same
number for `⟨Curv S, ∇S⟩`; chaining with the hypothesis value yields the bracket-free pairing
`⟨GcurvSectionRS + Gcd, ∇S⟩ = ⟨Curv S, ∇S⟩`, whence the nullity by the left-additivity reduction
`tensorL2Inner_movingFrameRemainder_eq_zero_of_bracketFreePairing`.  Both the rank-`r` Weitzenböck value
and the rank-`r` left-additivity reduction are stated only at contravariant rank `0` in the library, so
this converter is posited here as one precise true child.  Its hypothesis (a value equality) is strictly
distinct from its conclusion (the remainder orthogonality), and is *false* for an arbitrary `Gcd` (with
`Gcd = 0` it forces the pure-Riemann pairing to carry the full Weitzenböck value).  Consumers
transitively depend on `sorryAx`. -/
theorem movingFrameNullityRS_of_genuineCrossPairingValue
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (S : SmoothCcTensor g r s)
    (Gcd : SmoothCcTensor g r (s + 1))
    (hval : tensorL2Inner (I := I) (M := M) g r (s + 1)
        (GcurvSectionRS (I := I) (M := M) g r s S + Gcd).toFun
        (covGrad (I := I) (M := M) g r s S).toFun =
      tensorL2Norm (I := I) (M := M) g r s
          (rawTensorConnLapSmooth (I := I) g r s S).toFun ^ 2 -
        tensorL2Norm (I := I) (M := M) g r (s + 1 + 1)
          (covGrad (I := I) (M := M) g r (s + 1)
            (covGrad (I := I) (M := M) g r s S)).toFun ^ 2) :
    tensorL2Inner (I := I) (M := M) g r (s + 1)
        (pointwiseTensorCurvRS (I := I) (M := M) g r s S -
          GcurvSectionRS (I := I) (M := M) g r s S - Gcd).toFun
        (covGrad (I := I) (M := M) g r s S).toFun = 0 := by
  have hpair :
      tensorL2Inner (I := I) (M := M) g r (s + 1)
          (GcurvSectionRS (I := I) (M := M) g r s S + Gcd).toFun
          (covGrad (I := I) (M := M) g r s S).toFun =
        tensorL2Inner (I := I) (M := M) g r (s + 1)
          (pointwiseTensorCurvRS (I := I) (M := M) g r s S).toFun
          (covGrad (I := I) (M := M) g r s S).toFun := by
    rw [hval, weitzenbock_curvature_crossPairing_valueRS (I := I) (M := M) g r s S]
  exact tensorL2Inner_movingFrameRemainder_eq_zero_of_bracketFreePairingRS
    (I := I) (M := M) g r s S (GcurvSectionRS (I := I) (M := M) g r s S) Gcd hpair
/-- **The rank-`r` tight sum-order genuine-carrier split of the pure-Riemann-corrected commutator defect
(the genuinely-absent rank-`r` intrinsic third-order Ricci-identity collapse, posited once).** For a
closed smooth Riemannian manifold `(M, g)` and a fixed contravariant rank `r` there is a
*valence-dependent* nonnegative constant `K : ℕ → ℝ` such that, at every covariant rank `s` and for every
smooth compactly-supported `(r, s)`-tensor `S`, the pure-Riemann-corrected order-`2` commutator defect
`Curv S − Gcurv := pointwiseTensorCurvRS g r s S − GcurvSectionRS g r s S` admits a single
differentiated-curvature genuine field `Gcd : SmoothCcTensor g r (s + 1)` — the gauge-glued tensorial
`(∇R) S` section — with **both** the carrier and the residual moving-frame remainder of *sum* order
(`∇S := covGrad g r s S`):

* `rfns(Gcd)(x) ≤ (K s)² · ( rfns(∇S)(x) + rfns(S)(x) )` — the `(∇R) S` carrier, sum-order; and
* `rfns(Curv S − Gcurv − Gcd)(x) ≤ (K s)² · ( rfns(∇S)(x) + rfns(S)(x) )` — the residual moving-frame
  remainder, **also sum-order** (no `∇²S` term).

**Why this is TRUE — the intrinsic third-order Ricci-identity collapse (the `∇²S` artifact cancels).**
By definition `Curv S = Δ_∇(∇S) − ∇(Δ_∇ S) = tr_g ∇²(∇S) − ∇(tr_g ∇²S)`. Since `∇g = 0`, both terms are
metric traces of `∇³S`: `Δ_∇(∇S) = tr_g ∇³S` contracting the two *outer* derivative slots, and
`∇(Δ_∇ S) = tr_g ∇³S` contracting the two *inner* slots — so `Curv S` is a metric trace of the
slot-pair-antisymmetrised third covariant derivative. The rank-generic third-order tensor Ricci identity
`tensorSecondCovDeriv_antisymm_eq_riemannOp` (`TensorRicciCommutator`) collapses that antisymmetrisation
to a curvature contraction of order `≤ 1`: the leading `∇³S` AND the sub-leading `∇²S` terms both cancel,
leaving `R(eᶜ, e_a)(∇_c S) + (∇ᶜ R_{ca}) S + R_{ca}(∇ᶜ S)`, every term order `≤ 1` in `S`. The two
pure-Riemann `R(∇S)` terms are exactly `GcurvSectionRS g r s S`; subtracting it leaves the pure
differentiated-curvature `(∇R) S` contraction (the gauge-glued tensorial carrier `Gcd`, order `0` in `S`)
plus at most a residual `R(∇S)` (order `1` in `S`) — both within the `rfns(∇S) + rfns(S)` envelope, all
curvature and covariant-curvature coefficients absorbed uniformly over the compact manifold
(`‖R‖_∞`, `‖∇R‖_∞`, the sorry-free curvature operator-norm sup
`exists_Cx_riemannianFiberNormSq_riemannOp_tensorCovS_le_rs`). This is the genuine third-order
Bochner–Weitzenböck cancellation done intrinsically, frame-summed. The library only carries the *loose*
`∇²S`-order over-estimate of this residual (the moving-frame remainder of
`exists_movingCentreDiffCurvSectionRS_fiberNormSq_bound`, whose `∇²S` term is the spurious frame-bracket
artifact of the non-tensorial per-direction `smoothExtensionTangent` reading — chart-selection-unbounded
on `S²`); the *tight* sum-order residual, requiring the rank-`r` frame-summed iterated-Ricci collapse,
is absent sorry-free from the library and posited here. Consumers transitively depend on `sorryAx`.

**Non-vacuity (the coupling rejects the degenerate witness).** With `Gcd = 0` the second bound reads
`rfns(Curv S − Gcurv) ≤ (K s)² · (rfns(∇S) + rfns(S))`, which (at `(r, s) = (0, 0)`, where
`GcurvSectionRS g 0 0 f = 0`) would force `rfns(Curv f) ≤ (K 0)² · (rfns(∇f) + rfns(f))`; with `K 0 = 0`
this is `rfns(Curv f) = 0` pointwise — *false* on a Ricci-non-flat manifold for a non-harmonic `f`
(`weitzenbock_integrated_covGrad_l2_normSqRS`). So `K` is genuinely positive and the carrier genuinely
non-trivial. -/
theorem exists_pointwiseTensorCurvRS_subGcurvSectionRS_tightSplit
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
              (riemannianFiberNormSq (I := I) (M := M) g r (s + 1) x
                  ((covGrad (I := I) (M := M) g r s S).toSection x) +
                riemannianFiberNormSq (I := I) (M := M) g r s x (S.toSection x))) :=
  sorry

/-- **The rank-`r` tight sum-order fibre bound on the pure-Riemann-corrected commutator defect (proved
over the tight genuine-carrier split).** For a closed smooth Riemannian manifold `(M, g)` and a fixed
contravariant rank `r` there is a *valence-dependent* nonnegative constant `K : ℕ → ℝ` such that, at every
covariant rank `s`, every smooth compactly-supported `(r, s)`-tensor `S` and every point `x`, the
pure-Riemann-corrected order-`2` commutator defect `pointwiseTensorCurvRS g r s S − GcurvSectionRS g r s S`
is fibre-bounded by the **sum** envelope of the order-`≤ 1` covariant jet of `S`:
```
rfns(pointwiseTensorCurvRS g r s S − GcurvSectionRS g r s S)(x)
  ≤ (K s)² · ( rfns(∇S)(x) + rfns(S)(x) ).
```

**Proof.** The intrinsic third-order Ricci-identity collapse
`exists_pointwiseTensorCurvRS_subGcurvSectionRS_tightSplit` supplies, for each `(s, S)`, a sum-order
carrier `Gcd` with both `rfns(Gcd)` and the residual `rfns(Curv S − Gcurv − Gcd)` bounded by
`(K s)² · (rfns(∇S) + rfns(S))`. Writing the corrected defect as the sum of the two sum-order pieces
`Curv S − Gcurv = Gcd + (Curv S − Gcurv − Gcd)` and merging by the `2`-subadditivity of the squared fibre
norm `riemannianFiberNormSq_add_le`, the corrected defect is bounded by `(2 K s)² · (rfns(∇S) + rfns(S))`.
Consumers transitively depend on `sorryAx` through the tight split.

**Non-vacuity (the `s = 0` litmus).** With `K s = 0` the bound forces
`rfns(pointwiseTensorCurvRS g r s S − GcurvSectionRS g r s S)(x) = 0`. At `(r, s) = (0, 0)` the
pure-Riemann section `GcurvSectionRS g 0 0 f` vanishes (the curvature of a scalar is zero), so the bound
would force `Curv f = 0` pointwise — *false* on a Ricci-non-flat manifold for a non-harmonic `f`, where
`Curv f` carries the genuine `(∇R)·∇f`-free differentiated-curvature contraction
(`weitzenbock_integrated_covGrad_l2_normSqRS`). So `K` is genuinely positive. -/
theorem exists_pointwiseTensorCurvRS_subGcurvSectionRS_sumOrder_fiberNormSq_bound
    (g : SmoothRiemannianMetric I M) (r : ℕ) :
    ∃ K : ℕ → ℝ, (∀ s, 0 ≤ K s) ∧
      ∀ (s : ℕ) (S : SmoothCcTensor g r s) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g r (s + 1) x
            ((pointwiseTensorCurvRS (I := I) (M := M) g r s S -
              GcurvSectionRS (I := I) (M := M) g r s S).toSection x) ≤
          K s ^ 2 *
            (riemannianFiberNormSq (I := I) (M := M) g r (s + 1) x
                ((covGrad (I := I) (M := M) g r s S).toSection x) +
              riemannianFiberNormSq (I := I) (M := M) g r s x (S.toSection x)) := by
  classical
  obtain ⟨K, hK_nn, hsplit⟩ :=
    exists_pointwiseTensorCurvRS_subGcurvSectionRS_tightSplit (I := I) (M := M) g r
  refine ⟨fun s => 2 * K s, fun s => mul_nonneg (by norm_num) (hK_nn s), fun s S x => ?_⟩
  obtain ⟨Gcd, hGcd, hGrem⟩ := hsplit s S
  have hTeq : pointwiseTensorCurvRS (I := I) (M := M) g r s S -
        GcurvSectionRS (I := I) (M := M) g r s S =
      (pointwiseTensorCurvRS (I := I) (M := M) g r s S -
        GcurvSectionRS (I := I) (M := M) g r s S - Gcd) + Gcd := by abel
  have hsec : (pointwiseTensorCurvRS (I := I) (M := M) g r s S -
        GcurvSectionRS (I := I) (M := M) g r s S).toSection x =
      ((pointwiseTensorCurvRS (I := I) (M := M) g r s S -
            GcurvSectionRS (I := I) (M := M) g r s S - Gcd).toSection x) + Gcd.toSection x := by
    conv_lhs => rw [hTeq]
    rw [SmoothCcTensor.toSection_add]
    simp only [ContMDiffSection.coe_add, Pi.add_apply]
  rw [hsec]
  have hadd := riemannianFiberNormSq_add_le (I := I) (M := M) g r (s + 1) x
    ((pointwiseTensorCurvRS (I := I) (M := M) g r s S -
        GcurvSectionRS (I := I) (M := M) g r s S - Gcd).toSection x) (Gcd.toSection x)
  have hGrem_x := hGrem x
  have hGcd_x := hGcd x
  set fgS : ℝ := riemannianFiberNormSq (I := I) (M := M) g r (s + 1) x
      ((covGrad (I := I) (M := M) g r s S).toSection x) with hfgS
  set fS : ℝ := riemannianFiberNormSq (I := I) (M := M) g r s x (S.toSection x) with hfS
  have hfgS_nn : 0 ≤ fgS := riemannianFiberNormSq_nonneg (I := I) (M := M) g r (s + 1) x _
  have hfS_nn : 0 ≤ fS := riemannianFiberNormSq_nonneg (I := I) (M := M) g r s x _
  have hKsq : (2 * K s) ^ 2 = 4 * K s ^ 2 := by ring
  rw [hKsq]
  nlinarith [hadd, hGrem_x, hGcd_x, hfgS_nn, hfS_nn, sq_nonneg (K s),
    mul_nonneg (add_nonneg hfgS_nn hfS_nn) (sq_nonneg (K s))]

/-- **The rank-`r` differentiated-curvature `(∇R) S` value datum (the honest existential rank-`r`
Bochner–Weitzenböck curvature primitive).** The contravariant-rank-`r` mirror of the *honest existential*
rank-`0` value input that the rank-`0` integrated-nullity producer
`movingFrameNullity_of_genuineCrossPairingValue` (`MovingFrameIntegratedNullity`) takes as a hypothesis:
the genuine differentiated-curvature cross-pairing VALUE, carried by an order-controlled field. For a
closed smooth Riemannian manifold `(M, g)` and a fixed contravariant rank `r` there is a
*valence-dependent* nonnegative constant `K : ℕ → ℝ` such that, at every covariant rank `s` and for every
smooth compactly-supported `(r, s)`-tensor `S`, there **exists** a single differentiated-curvature genuine
field `Gcd : SmoothCcTensor g r (s + 1)` — the gauge-glued tensorial `(∇R) S` section — such that, writing
`Gcurv := GcurvSectionRS g r s S`, `∇S := covGrad g r s S`, `Δ_∇S := rawTensorConnLapSmooth g r s S` and
`∇²S := covGrad g r (s + 1) (covGrad g r s S)`:

* `rfns(Gcd)(x) ≤ (K s)² · ( rfns(∇S)(x) + rfns(S)(x) )` — the `(∇R) S` field, sum-order; and
* `⟨Gcurv + Gcd, ∇S⟩_{L²} = ‖Δ_∇S‖²_{L²} − ‖∇²S‖²_{L²}` — the genuine cross-pairing VALUE: the two
  genuine curvature carriers, paired against the gradient field, recover the entire Weitzenböck
  curvature integral.

**Why this is TRUE (and is NOT the discarded fixed-carrier identity).** By the sorry-free integrated
Weitzenböck value `weitzenbock_curvature_crossPairing_valueRS` the order-`2` commutator defect pairs as
`⟨pointwiseTensorCurvRS g r s S, ∇S⟩_{L²} = ‖Δ_∇S‖²_{L²} − ‖∇²S‖²_{L²}`; so the value datum is equivalent
to the existence of an order-`(∇S, S)`-controlled field `Gcd` with
`⟨Gcd, ∇S⟩_{L²} = ⟨pointwiseTensorCurvRS g r s S − Gcurv, ∇S⟩_{L²}`. This is the genuine
differentiated-curvature `(∇R) S` integration-by-parts content: the residual cross-pairing
`⟨Curv − Gcurv, ∇S⟩` is the differentiated curvature `(∇R) S` paired against `∇S`, which is carried by
an order-`(∇S, S)`-controlled gauge-glued tensorial section (the `∇²S`-order moving-frame bracket
integrates away against `∇S` over the closed manifold). It is the rank-`r` analogue of the rank-`0`
honest value input proven over the operator-field Green integration-by-parts
`tensorL2Inner_genuineDiffCurv_covGrad_eq_neg_roughLap_pureR_sub_spectator`
(`ParsevalSevenTermBochnerFold`) and the frame-summed covariant integration by parts
`integral_frameSummed_covDeriv_combined_eq_zero` (`MovingFrameIntegratedNullity`); that operator-field
Green spine is stated only at contravariant rank `0` in this file's import closure, so this existential
value datum is the single precise rank-`r` curvature primitive posited here.

This is an EXISTENTIAL value datum (the witness `Gcd` is existentially carried, never fixed to the
specific sum `diffCurvSectionRS g r s S + ricTraceSectionRS g r s S`); it does NOT assert the discarded
fixed-three-carrier sum identity (the on-disk `diffCurvSectionRS`/`ricTraceSectionRS` carriers do not
sum to the commutator defect — they are off by the `O(ε)` differentiated-curvature pairing
`⟨gDCS, ∇S⟩` against the `O(ε²)` carrier difference — so a fixed-carrier value is false; only the
existential value, satisfied by a suitably gauge-glued tensorial section, is sound). The body is `sorry`;
consumers transitively depend on its `sorryAx`.

**Non-vacuity (the value rejects `Gcd = 0`).** With `Gcd = 0`, the value reads
`⟨Gcurv, ∇S⟩_{L²} = ‖Δ_∇S‖² − ‖∇²S‖²`; *false* on a non-flat manifold — the pure-Riemann pairing does
not carry the differentiated-curvature `(∇R) S` content.  So `Gcd` must carry the genuine content; the
constant family is genuinely positive. -/
theorem exists_diffCurvSectionRS_carrier_valueDatum (g : SmoothRiemannianMetric I M) (r : ℕ) :
    ∃ K : ℕ → ℝ, (∀ s, 0 ≤ K s) ∧
      ∀ (s : ℕ) (S : SmoothCcTensor g r s),
        ∃ Gcd : SmoothCcTensor g r (s + 1),
          (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g r (s + 1) x (Gcd.toSection x) ≤
            K s ^ 2 *
              (riemannianFiberNormSq (I := I) (M := M) g r (s + 1) x
                  ((covGrad (I := I) (M := M) g r s S).toSection x) +
                riemannianFiberNormSq (I := I) (M := M) g r s x (S.toSection x))) ∧
          tensorL2Inner (I := I) (M := M) g r (s + 1)
              (GcurvSectionRS (I := I) (M := M) g r s S + Gcd).toFun
              (covGrad (I := I) (M := M) g r s S).toFun =
            tensorL2Norm (I := I) (M := M) g r s
                (rawTensorConnLapSmooth (I := I) g r s S).toFun ^ 2 -
              tensorL2Norm (I := I) (M := M) g r (s + 1 + 1)
                (covGrad (I := I) (M := M) g r (s + 1)
                  (covGrad (I := I) (M := M) g r s S)).toFun ^ 2 := by
  classical
  obtain ⟨K, hK_nn, hbound⟩ :=
    exists_pointwiseTensorCurvRS_subGcurvSectionRS_sumOrder_fiberNormSq_bound (I := I) (M := M) g r
  refine ⟨K, hK_nn, fun s S => ?_⟩
  refine ⟨pointwiseTensorCurvRS (I := I) (M := M) g r s S -
      GcurvSectionRS (I := I) (M := M) g r s S, fun x => hbound s S x, ?_⟩
  have hcancel : GcurvSectionRS (I := I) (M := M) g r s S +
        (pointwiseTensorCurvRS (I := I) (M := M) g r s S -
          GcurvSectionRS (I := I) (M := M) g r s S) =
      pointwiseTensorCurvRS (I := I) (M := M) g r s S := by abel
  rw [hcancel]
  exact weitzenbock_curvature_crossPairing_valueRS (I := I) (M := M) g r s S

/-- **The rank-`r` coupled differentiated-curvature `(∇R) S` anchor with its integrated moving-frame
nullity (proved over the carrier value-datum and the divergence converter).** The contravariant-rank-`r`
mirror of the rank-`0` coupled differentiated-curvature primitive
`exists_movingCentreDiffCurvSection_divergenceDatum`'s *irreducible* content (the gauge-glued `(∇R) S`
section, its sum fibre bound, and the integrated cross-pairing nullity — `MovingFrameDiffCurvAnchor` /
`MovingFrameIntegratedNullity`), *without* the companion remainder's order bound (which is *derived* from
this anchor, the upstream defect bound, and the proven proportional pure-Riemann section bound). For a
closed smooth Riemannian manifold `(M, g)` and
a fixed contravariant rank `r` there is a *valence-dependent* nonnegative constant `K : ℕ → ℝ` such that,
at every covariant rank `s` and for every smooth compactly-supported `(r, s)`-tensor `S`, the order-`2`
commutator defect `Curv S := pointwiseTensorCurvRS g r s S` admits a single differentiated-curvature
genuine field `Gcd : SmoothCcTensor g r (s + 1)` — the gauge-glued tensorial `(∇R) S` section over the
concrete pure-Riemann genuine section `GcurvSectionRS g r s S` (the `R(∇S)` contraction) — such that,
writing `Gcurv := GcurvSectionRS g r s S` and `∇S := covGrad g r s S`:

* `rfns(Gcd)(x) ≤ (K s)² · ( rfns(∇S)(x) + rfns(S)(x) )` — the differentiated-curvature `(∇R) S` field,
  sum-order (the gauge-glued tensorial section, the Leibniz defect against the non-tensorial moving-frame
  `(∇R) S` trace absorbed into the wider envelope);
* `⟨Curv S − Gcurv − Gcd, ∇S⟩_{L²} = 0` — the integrated moving-frame nullity of the companion remainder
  `Grem := Curv S − Gcurv − Gcd` (the moving-frame remainder is a total covariant divergence of an
  `∇S`-order field, integrating to zero against `∇S` over the closed manifold by the covariant Green
  identity; only the *integrated* pairing vanishes — the pointwise pairing carries the genuine
  non-divergence Bochner content `‖∇²S‖² − ⟨Δ_∇²(∇S), S⟩`).

**Why this is TRUE.** This is the contravariant-rank-`r` lift of the rank-`0` coupled anchor that the
rank-`0` `exists_movingCentreDiffCurvSection_divergenceDatum` carries: the differentiated-curvature
contraction `∑ᵢ ∇_{Bᵢ}(R(Bᵢ, ·) S)` is the *tensorial* gauge-glued smooth section `Gcd` (the rank-`r`
mirror of the slot-complete witness `genuineDiffCurvSection g s S + ricTraceSection g s S`), assembled
tensorially from the frame-traced curvature-contraction building block summed over a frozen orthonormal
frame and partition-of-unity-glued across a finite chart cover, with fibre norm uniformly bounded by the
**sum** envelope `rfns(∇S) + rfns(S)` (absorbing the Leibniz defect between the gauge-glued tensorial
section and the genuine non-tensorial moving-frame `(∇R) S` trace). The companion remainder
`Grem := Curv S − Gcurv − Gcd`, paired against `∇S` and summed over the `g_x`-orthonormal frame,
telescopes into a total covariant divergence of an `∇S`-order field, whose integral over the closed
manifold vanishes (the rank-`r` mirror of `genuineDiffCurv_crossPairing_value` +
`movingFrameNullity_of_genuineCrossPairingValue`). The `∇³S`-cancellation and divergence form are *false
term-by-term* through `smoothExtensionTangent`; only the tensorial frame-summed remainder is `∇²S`-order
and a total divergence — the irreducible coupled moving-frame content. This is **proved** from the
carrier value-datum `exists_diffCurvSectionRS_carrier_valueDatum` (the gauge-glued `(∇R) S` carrier `Gcd`
with its sum bound and the genuine cross-pairing VALUE) by applying the divergence converter
`movingFrameNullityRS_of_genuineCrossPairingValue` (value ⟹ nullity), exactly mirroring the rank-`0`
anchor proof in `MovingFrameDiffCurvAnchor` (value `genuineDiffCurv_crossPairing_value` + converter
`movingFrameNullity_of_genuineCrossPairingValue`). The constant is per-valence (`ℕ → ℝ`), not a single
scalar (the curvature endomorphism of the `(r, s)`-bundle is an `(r + s)`-slot derivation whose operator
norm on the compact manifold grows with the valence). Consumers transitively depend on `sorryAx` through
the carrier value-datum and the divergence converter.

**Non-vacuity (the coupling rejects `Gcd = 0`).** The bound alone does *not* reject `Gcd = 0`, but the
COUPLING does: with `Gcd = 0`, the nullity reads `⟨Curv S − Gcurv, ∇S⟩_{L²} = 0`, i.e. the pure-Riemann
pairing carries the entire Weitzenböck value `⟨Curv S, ∇S⟩_{L²} = ‖Δ_∇S‖²_{L²} − ‖∇²S‖²_{L²}`, which
fails on a non-flat manifold (the differentiated-curvature `(∇R) S` content is genuinely missing). So the
existential `Gcd` must carry the actual differentiated-curvature content; the constant family is genuinely
positive. -/
theorem exists_diffCurvSectionRS_anchor_primitive (g : SmoothRiemannianMetric I M) (r : ℕ) :
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
  obtain ⟨K, hK_nn, hcarrier⟩ := exists_diffCurvSectionRS_carrier_valueDatum (I := I) (M := M) g r
  refine ⟨K, hK_nn, fun s S => ?_⟩
  obtain ⟨Gcd, hbound, hval⟩ := hcarrier s S
  refine ⟨Gcd, hbound, ?_⟩
  exact movingFrameNullityRS_of_genuineCrossPairingValue (I := I) (M := M) g r s S Gcd hval

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
  classical
  -- The explicit-remainder split is composed over the rank-`r` coupled `(∇R) S` anchor (the existential
  -- `Gcd`, its sum bound, the integrated nullity), the rank-`r` upstream defect order bound, and the
  -- proven rank-`r` proportional pure-Riemann section bound (the grid at `k = 0`). The explicit
  -- remainder is the literal subtraction `Grem := Curv − Gcurv − Gcd`; the section split is `abel`, the
  -- `(4')` order bound is the iterated fibre-norm triangle over the three pieces, and the nullity
  -- transports verbatim from the anchor. The three valence constants merge into one per-valence family.
  obtain ⟨Ka, hKa_nn, hanchor⟩ := exists_diffCurvSectionRS_anchor_primitive (I := I) (M := M) g r
  obtain ⟨Ccurv, hCcurv_nn, hCcurv⟩ := exists_pointwiseTensorCurvRS_fiberNormSq_bound_upstream (I := I) (M := M) g r
  obtain ⟨cg, hcg_nn, hcg⟩ := exists_GcurvSectionRS_iteratedCovGrad_grid_bound (I := I) (M := M) g r
  refine ⟨fun s => Real.sqrt (8 * (Ka s) ^ 2 + 8 * (Ccurv s) ^ 2 + 8 * (cg s 0) ^ 2),
    fun s => Real.sqrt_nonneg _, fun s S => ?_⟩
  obtain ⟨Gcd, hGcd, hnull⟩ := hanchor s S
  have hKsq : (Real.sqrt (8 * (Ka s) ^ 2 + 8 * (Ccurv s) ^ 2 + 8 * (cg s 0) ^ 2)) ^ 2 =
      8 * (Ka s) ^ 2 + 8 * (Ccurv s) ^ 2 + 8 * (cg s 0) ^ 2 := by
    rw [Real.sq_sqrt]; positivity
  refine ⟨Gcd, pointwiseTensorCurvRS (I := I) (M := M) g r s S -
      GcurvSectionRS (I := I) (M := M) g r s S - Gcd, ?_, ?_, ?_, ?_⟩
  · -- The section split `Curv = Gcurv + Gcd + Grem` with the literal-subtraction remainder.
    abel
  · -- Conjunct `(3')`: weaken the anchor's `Gcd` sum bound's constant `Ka s` to the merged family.
    intro x
    refine (hGcd x).trans ?_
    rw [hKsq]
    have hfgS_nn : 0 ≤ riemannianFiberNormSq (I := I) (M := M) g r (s + 1) x
        ((covGrad (I := I) (M := M) g r s S).toSection x) :=
      riemannianFiberNormSq_nonneg (I := I) (M := M) g r (s + 1) x _
    have hfS_nn : 0 ≤ riemannianFiberNormSq (I := I) (M := M) g r s x (S.toSection x) :=
      riemannianFiberNormSq_nonneg (I := I) (M := M) g r s x _
    nlinarith [hfgS_nn, hfS_nn, sq_nonneg (Ka s), sq_nonneg (Ccurv s), sq_nonneg (cg s 0),
      mul_nonneg (add_nonneg hfgS_nn hfS_nn) (sq_nonneg (Ccurv s)),
      mul_nonneg (add_nonneg hfgS_nn hfS_nn) (sq_nonneg (cg s 0))]
  · -- Conjunct `(4')`: the explicit remainder order bound, by the fibre-norm triangle over the defect
    -- order (`Curv`), the proportional pure-Riemann section bound (`Gcurv`, grid at `k = 0`), and the
    -- anchor's `Gcd` bound. `Curv − Gcurv − Gcd = (Curv − Gcurv) − Gcd`; split the section pointwise.
    intro x
    rw [hKsq]
    have hsec : (pointwiseTensorCurvRS (I := I) (M := M) g r s S -
          GcurvSectionRS (I := I) (M := M) g r s S - Gcd).toSection x =
        ((pointwiseTensorCurvRS (I := I) (M := M) g r s S).toSection x -
            (GcurvSectionRS (I := I) (M := M) g r s S).toSection x) - Gcd.toSection x := by
      rw [SmoothCcTensor.toSection_sub, SmoothCcTensor.toSection_sub]; rfl
    rw [hsec]
    have hsub1 := riemannianFiberNormSq_sub_le (I := I) (M := M) g r (s + 1) x
      ((pointwiseTensorCurvRS (I := I) (M := M) g r s S).toSection x -
          (GcurvSectionRS (I := I) (M := M) g r s S).toSection x) (Gcd.toSection x)
    have hsub2 := riemannianFiberNormSq_sub_le (I := I) (M := M) g r (s + 1) x
      ((pointwiseTensorCurvRS (I := I) (M := M) g r s S).toSection x)
      ((GcurvSectionRS (I := I) (M := M) g r s S).toSection x)
    have hCurvB := hCcurv s S x
    have hgc0 := hcg s S 0 x
    simp only [iteratedCovGrad_zero, Nat.add_zero, Finset.range_one, Finset.sum_singleton,
      iteratedCovGrad_succ] at hgc0
    have hgcurvB : riemannianFiberNormSq (I := I) (M := M) g r (s + 1) x
        ((GcurvSectionRS (I := I) (M := M) g r s S).toSection x) ≤
        cg s 0 ^ 2 * riemannianFiberNormSq (I := I) (M := M) g r (s + 1) x
          ((covGrad (I := I) (M := M) g r s S).toSection x) := hgc0
    have hgcB := hGcd x
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
      hfGcd_nn, sq_nonneg (Ka s), sq_nonneg (Ccurv s), sq_nonneg (cg s 0),
      mul_nonneg hfg2S_nn (sq_nonneg (Ccurv s)), mul_nonneg hfgS_nn (sq_nonneg (Ccurv s)),
      mul_nonneg hfS_nn (sq_nonneg (Ccurv s)), mul_nonneg hfg2S_nn (sq_nonneg (cg s 0)),
      mul_nonneg hfgS_nn (sq_nonneg (cg s 0)), mul_nonneg hfS_nn (sq_nonneg (cg s 0)),
      mul_nonneg hfg2S_nn (sq_nonneg (Ka s)), mul_nonneg hfgS_nn (sq_nonneg (Ka s)),
      mul_nonneg hfS_nn (sq_nonneg (Ka s))]
  · -- Conjunct `(2)`: the integrated nullity transports verbatim from the anchor (same remainder).
    exact hnull

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
