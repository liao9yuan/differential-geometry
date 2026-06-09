import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.MovingFrameRemainderFrameSumBridge
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.RankRPureRCurvatureTower

/-!
# The frame-summed integrand of the moving-frame remainder pairing at contravariant rank `r`

For a closed (compact, boundaryless) smooth Riemannian manifold `(M, g)` this file is the
contravariant-rank-`r` lift of the rank-`0` frame-sum bridge `MovingFrameRemainderFrameSumBridge`:
it builds the **frame-summed pointwise integrand** of the curvature cross-pairing
`⟨Curv S, ∇S⟩_{L²}` of the rank-`(r, s)` order-`2` rough-Laplacian / covariant-gradient commutator
defect `Curv S := Δ_∇(∇S) − ∇(Δ_∇ S)` (here written through its upstream constituents
`rawTensorConnLapSmooth g r (s + 1) (covGrad g r s S) − covGrad g r s (rawTensorConnLapSmooth g r s S)`,
the body of the downstream `pointwiseTensorCurvRS g r s S`), the per-direction genuine/bracket split
of the frame summand, and the **pure-Riemann genuine-sum identification** with the order-`0` operator
of the rank-`r` frame-free pure-Riemann differentiated curvature tower
`genuinePureRDiffOpRS g r 0 (s + 1) (∇S)` (`RankRPureRCurvatureTower`).

This is the upstream-safe rank-`r` carrier engine: every identity here is stated purely in the
upstream vocabulary (`rawTensorConnLapSmooth`, `covGrad`, `riemannOp (tensorCov g r s)`, `covApply`,
`genuinePureRDiffOpRS`), so the downstream `MovingFrameGenuineFieldPairingRS` — where the bundled
defect `pointwiseTensorCurvRS` and the concrete pure-Riemann section `GcurvSectionRS` live — can
import it and re-express each identity over its own named sections in one `rfl`-grade step, exactly
as the rank-`0` leaf file `MovingFrameDiffCurvTraceSection` consumes the rank-`0` bridge.

## The frame-summand decomposition of the integrand

The rank-generic frame-trace reading of the rough Laplacian
(`rawTensorConnLap_eq_frame_trace_secondCovDeriv`) and the rank-generic gradient-slot frame sum
(`covGradBundleEquiv_covDeriv_rawConnLap_eq_sum`) read the defect, at every point `x` and over the
`g_x`-orthonormal frame `Bᵢ := smoothOrthoFrame g x i`, as the fixed-frame sum of the
**per-summand third-order difference** `remDiffFibRS g r s S x i := ∇²_{Bᵢ, Bᵢ}(∇S)(x) −
covGradBundleEquiv r s x (∇·(∇²_{Bᵢ, Bᵢ} S)(x))` (`commutatorDefectRS_toSection_eq_frame_sum`).
Pairing against `∇S(x)` and distributing the metric inner product over the frame sum gives the
**integrand frame-sum identity** (`commutatorDefectRS_pairing_eq_frameSum`), integrated to the
curvature cross-pairing (`tensorL2Inner_commutatorDefectRS_covGrad_eq_frameSum_integral`).

## The per-direction genuine/bracket split and the pure-Riemann genuine-sum identification

Each frame summand splits into its pure-Riemann genuine curvature fibre `remDiffGenuineFibRS` (the
slot-`0` uncurry of the curvature-direction CLM `v ↦ R(Bᵢ, v)(∇_{Bᵢ} S)`, the pure-Riemann `R(∇S)`
contraction read off the bundled trilinear Riemann operator `riemannOp (tensorCov g r s)` — the
rank-`r` curvature whose slot-wise soundness is the sorry-free bundled path
`riemannSec_tensorCov_apply_eval` of `TensorSlotwiseCurvatureRS`) and its named frame-bracket
remainder `remDiffBracketFibRS := remDiffFibRS − remDiffGenuineFibRS` (carrying the
differentiated-curvature `(∇R) S` content and the `∇²S`-order frame-bracket discrepancy). The
pure-Riemann genuine fibres' frame sum is, pointwise, the fibre value of the order-`0` rank-`r`
frame-free pure-Riemann operator on `∇S` (`remDiffGenuineFibRS_sum_eq_genuinePureRDiffOp0_toSection`,
sorry-free, through the public slot-`0` reading `genuinePureRDiffOp0_covGrad_fib_eq`); their
frame-sum pairing against `∇S`, integrated, is `⟨genuinePureRDiffOpRS g r 0 (s + 1) (∇S), ∇S⟩_{L²}`
(`remDiffFibRS_genuineFrameSum_pairing_eq_genuineFields`) — a *sound pointwise* frame-sum identity
since the pure-Riemann trace is tensorial in the direction.

## Main results

* `remDiffFibRS`, `commutatorDefectRS_toSection_eq_frame_sum`,
  `commutatorDefectRS_pairing_eq_frameSum`,
  `tensorL2Inner_commutatorDefectRS_covGrad_eq_frameSum_integral` — the frame-sum integrand of the
  rank-`r` curvature cross-pairing, over the upstream defect body.
* `remDiffGenuineDirLMRS` / `remDiffGenuineDirCLMRS` / `remDiffGenuineFibRS`,
  `remDiffBracketFibRS`, `remDiffFibRS_eq_genuine_add_bracket` — the per-direction pure-Riemann
  genuine fibre chain and its named frame-bracket remainder.
* `remDiffGenuineFibRS_sum_eq_genuinePureRDiffOp0_toSection`,
  `genuineFrameSumRS_pairing_pointwise_eq_genuinePureRDiffOp0`,
  `remDiffFibRS_genuineFrameSum_pairing_eq_genuineFields` — the pure-Riemann genuine-sum
  identification against the rank-`r` frame-free tower (all sorry-free).

Every declaration in this file is sorry-free; the deep rank-`r` analytic content (the proportional
envelopes, the order-separated fibre bounds, the integrated bracket nullity) lives strictly above,
in `MovingFrameGenuineFieldPairingRS` and `OrderSeparatedCurvatureJetRS`.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 1200000
set_option maxHeartbeats 1600000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

/-- **The per-summand third-order difference field at contravariant rank `r`.** At a point `x`, with
the `g_x`-orthonormal frame `Bᵢ := smoothOrthoFrame g x i`, the `i`-th summand of the fixed-frame
representation of the rank-`(r, s)` order-`2` commutator defect:
```
remDiffFibRS g r s S x i
  := ∇²_{Bᵢ, Bᵢ}(∇S)(x) − covGradBundleEquiv r s x (∇·(∇²_{Bᵢ, Bᵢ} S)(x)),
```
the difference of the rank-`(r, s + 1)` second covariant derivative of the gradient tensor
`∇S = covGrad g r s S` and the `(r, s + 1)`-tensor covariant gradient of the rank-`(r, s)` second
covariant derivative `∇²_{Bᵢ, Bᵢ} S`. It is the gradient-slot reordering of the three covariant
derivative slots — the genuine off-diagonal Riemann curvature. The contravariant-rank-`r` mirror of
`remDiffFib`. -/
def remDiffFibRS (g : SmoothRiemannianMetric I M) (r s : ℕ) (S : SmoothCcTensor g r s) (x : M)
    (i : Fin (Module.finrank ℝ E)) : TensorRSSpace r (s + 1) I x :=
  tensorSecondCovDeriv (I := I) g r (s + 1)
      (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x i)
      (fun y : M => (covGrad (I := I) (M := M) g r s S).toSection y) x -
    covGradBundleEquiv (I := I) (M := M) r s x
      ((tensorCov (I := I) g r s).toFun
        (fun y : M => tensorSecondCovDeriv (I := I) g r s
          (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x i)
          (fun z : M => S.toSection z) y) x)

/-- **Frame-trace reading of the rough-Laplacian piece at rank `r`.** The rough Laplacian of the
`(r, s + 1)`-tensor gradient field `∇S`, read at `x`, is the frame trace of its second covariant
derivative over the `g_x`-orthonormal frame `Bᵢ`:
```
(Δ_∇(∇S)).toSection x = ∑ᵢ ∇²_{Bᵢ, Bᵢ}(∇S)(x).
```
This is the rank-generic `rawTensorConnLap_eq_frame_trace_secondCovDeriv` at rank `(r, s + 1)`
applied to the underlying section of `∇S = covGrad g r s S` — the contravariant-rank-`r` mirror of
`rawTensorConnLap_gradTensor_toSection_eq_frame_trace_gen`. -/
theorem rawTensorConnLap_gradTensorRS_toSection_eq_frame_trace
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (S : SmoothCcTensor g r s) (x : M) :
    (rawTensorConnLapSmooth (I := I) g r (s + 1)
        (covGrad (I := I) (M := M) g r s S)).toSection x =
      ∑ i : Fin (Module.finrank ℝ E),
        tensorSecondCovDeriv (I := I) g r (s + 1)
          (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x i)
          (fun y : M => (covGrad (I := I) (M := M) g r s S).toSection y) x := by
  rw [rawTensorConnLapSmooth_toSection_apply]
  exact rawTensorConnLap_eq_frame_trace_secondCovDeriv (I := I) g r (s + 1)
    (fun y : M => (covGrad (I := I) (M := M) g r s S).toSection y) x

/-- **The gradient piece as a fixed-frame sum of per-summand covariant gradients at rank `r`.** The
covariant gradient `∇(Δ_∇ S)` of the rough Laplacian equals, at `x`, the fixed-frame sum of the
covariant gradients of the per-summand second covariant derivatives:
```
(covGrad g r s (Δ_∇ S)).toSection x = ∑ᵢ covGradBundleEquiv r s x (∇·(∇²_{Bᵢ, Bᵢ} S)(x)).
```
This is the rank-generic `covGradBundleEquiv_covDeriv_rawConnLap_eq_sum` at `(r, s)`, read through
`covGrad_toSection_apply` and `rawTensorConnLapSmooth_toSection_apply` — the contravariant-rank-`r`
mirror of `covGrad_rawConnLap_toSection_eq_frame_sum_gen`. -/
theorem covGrad_rawConnLapRS_toSection_eq_frame_sum
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (S : SmoothCcTensor g r s) (x : M) :
    (covGrad (I := I) (M := M) g r s
        (rawTensorConnLapSmooth (I := I) g r s S)).toSection x =
      ∑ i : Fin (Module.finrank ℝ E),
        covGradBundleEquiv (I := I) (M := M) r s x
          ((tensorCov (I := I) g r s).toFun
            (fun y : M => tensorSecondCovDeriv (I := I) g r s
              (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x i)
              (fun z : M => S.toSection z) y) x) := by
  have hS : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) y (S.toSection y)) :=
    S.toSection.contMDiff
  rw [covGrad_toSection_apply (I := I) (M := M) g r s
    (rawTensorConnLapSmooth (I := I) g r s S) x]
  rw [show (fun y : M => (rawTensorConnLapSmooth (I := I) g r s S).toSection y) =
      (fun y : M => rawTensorConnLap (I := I) g r s (fun z : M => S.toSection z) y) from by
    funext y; rw [rawTensorConnLapSmooth_toSection_apply]]
  exact covGradBundleEquiv_covDeriv_rawConnLap_eq_sum (I := I) g r s hS x

/-- **The rank-`r` order-`2` commutator defect as a fixed-frame sum of per-summand third-order
differences (sorry-free).** The underlying section value, at `x`, of the difference
`Δ_∇(∇S) − ∇(Δ_∇ S)` — the upstream body of the downstream bundled defect
`pointwiseTensorCurvRS g r s S` — is the fixed-frame sum
```
(Δ_∇(∇S) − ∇(Δ_∇ S)).toSection x = ∑ᵢ remDiffFibRS g r s S x i,
```
with `Bᵢ := smoothOrthoFrame g x i`. The proof splits the section value of the difference, reads the
rough-Laplacian piece by `rawTensorConnLap_gradTensorRS_toSection_eq_frame_trace`, the gradient piece
by `covGrad_rawConnLapRS_toSection_eq_frame_sum`, and combines the two frame sums via
`Finset.sum_sub_distrib`. No moving-frame derivative and no curvature input is used — this is the
purely structural rank-`r` integrand decomposition, the contravariant-rank-`r` mirror of
`pointwiseTensorCurv_toSection_eq_frame_sum`. -/
theorem commutatorDefectRS_toSection_eq_frame_sum
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (S : SmoothCcTensor g r s) (x : M) :
    (rawTensorConnLapSmooth (I := I) g r (s + 1) (covGrad (I := I) (M := M) g r s S) -
        covGrad (I := I) (M := M) g r s (rawTensorConnLapSmooth (I := I) g r s S)).toSection x =
      ∑ i : Fin (Module.finrank ℝ E), remDiffFibRS (I := I) (M := M) g r s S x i := by
  classical
  have hsub : (rawTensorConnLapSmooth (I := I) g r (s + 1)
          (covGrad (I := I) (M := M) g r s S) -
        covGrad (I := I) (M := M) g r s
          (rawTensorConnLapSmooth (I := I) g r s S)).toSection x =
      (rawTensorConnLapSmooth (I := I) g r (s + 1)
          (covGrad (I := I) (M := M) g r s S)).toSection x -
        (covGrad (I := I) (M := M) g r s
          (rawTensorConnLapSmooth (I := I) g r s S)).toSection x := by
    rw [SmoothCcTensor.toSection_sub]
    rfl
  rw [hsub, rawTensorConnLap_gradTensorRS_toSection_eq_frame_trace (I := I) (M := M) g r s S x,
    covGrad_rawConnLapRS_toSection_eq_frame_sum (I := I) (M := M) g r s S x,
    ← Finset.sum_sub_distrib]
  rfl

/-- **The rank-`r` frame-summand integrand identity (sorry-free).** For a closed smooth Riemannian
manifold `(M, g)`, contravariant rank `r`, covariant rank `s`, smooth compactly-supported
`(r, s)`-tensor `S`, and point `x`, the pointwise metric inner product of the order-`2` commutator
defect `Δ_∇(∇S) − ∇(Δ_∇ S)` against the gradient field `∇S := covGrad g r s S` — the integrand of
the rank-`r` curvature cross-pairing — is the fixed-frame sum of the per-summand pairings of the
third-order difference fields against `∇S`:
```
⟨Curv S, ∇S⟩(x) = ∑ᵢ ⟨remDiffFibRS g r s S x i, ∇S(x)⟩,   Bᵢ := smoothOrthoFrame g x i.
```

**Proof (sorry-free).** Read the defect at `x` by the fixed-frame representation
`commutatorDefectRS_toSection_eq_frame_sum`, push the model coercion through the frame sum by
additivity of `TensorRSSpace.toModel`, and distribute the pointwise metric inner product over the
frame sum by `tensorInnerPointwise_sum_left`. The contravariant-rank-`r` mirror of
`pointwiseTensorCurvPairing_eq_frameSum`. -/
theorem commutatorDefectRS_pairing_eq_frameSum
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (S : SmoothCcTensor g r s) (x : M) :
    tensorInnerPointwise (I := I) (M := M) g r (s + 1) x
        ((rawTensorConnLapSmooth (I := I) g r (s + 1) (covGrad (I := I) (M := M) g r s S) -
          covGrad (I := I) (M := M) g r s (rawTensorConnLapSmooth (I := I) g r s S)).toFun x)
        ((covGrad (I := I) (M := M) g r s S).toFun x) =
      ∑ i : Fin (Module.finrank ℝ E),
        tensorInnerPointwise (I := I) (M := M) g r (s + 1) x
          (TensorRSSpace.toModel (remDiffFibRS (I := I) (M := M) g r s S x i))
          ((covGrad (I := I) (M := M) g r s S).toFun x) := by
  classical
  have htoM : TensorRSSpace.toModel
        (∑ i : Fin (Module.finrank ℝ E), remDiffFibRS (I := I) (M := M) g r s S x i) =
      ∑ i : Fin (Module.finrank ℝ E),
        TensorRSSpace.toModel (remDiffFibRS (I := I) (M := M) g r s S x i) := by
    induction (Finset.univ : Finset (Fin (Module.finrank ℝ E))) using Finset.induction with
    | empty => simp [TensorRSSpace.toModel_zero]
    | insert i₀ s'' hi₀ ih =>
        rw [Finset.sum_insert hi₀, TensorRSSpace.toModel_add, ih, Finset.sum_insert hi₀]
  rw [SmoothCcTensor.toFun_apply
      (rawTensorConnLapSmooth (I := I) g r (s + 1) (covGrad (I := I) (M := M) g r s S) -
        covGrad (I := I) (M := M) g r s (rawTensorConnLapSmooth (I := I) g r s S)) x,
    commutatorDefectRS_toSection_eq_frame_sum (I := I) (M := M) g r s S x, htoM]
  rw [show (∑ i : Fin (Module.finrank ℝ E),
        TensorRSSpace.toModel (remDiffFibRS (I := I) (M := M) g r s S x i)) =
      ∑ i : Fin (Module.finrank ℝ E), (1 : ℝ) •
        TensorRSSpace.toModel (remDiffFibRS (I := I) (M := M) g r s S x i) from by
    refine Finset.sum_congr rfl (fun i _ => ?_); rw [one_smul]]
  rw [tensorInnerPointwise_sum_left (I := I) (M := M) g r (s + 1) x Finset.univ]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [one_mul]

/-- **The rank-`r` curvature cross-pairing as the integral of the frame-summed remainder integrand
(sorry-free).** For a closed smooth Riemannian manifold `(M, g)`, contravariant rank `r`, covariant
rank `s`, and smooth compactly-supported `(r, s)`-tensor `S`, the global metric `L²` pairing of the
order-`2` commutator defect `Δ_∇(∇S) − ∇(Δ_∇ S)` against `∇S := covGrad g r s S` is the integral
over the closed manifold of the fixed-frame sum of the per-summand pairings `⟨remDiffFibRS …, ∇S⟩`:
```
⟨Curv S, ∇S⟩_{L²} = ∫_M ∑ᵢ ⟨remDiffFibRS g r s S x i, ∇S(x)⟩ dvol_g.
```

**Proof (sorry-free).** Unfold `tensorL2Inner` to the integral of the pointwise pairing and rewrite
the integrand pointwise by the sorry-free frame-summand identity
`commutatorDefectRS_pairing_eq_frameSum`. The contravariant-rank-`r` mirror of
`tensorL2Inner_pointwiseTensorCurv_covGrad_eq_frameSum_integral`. -/
theorem tensorL2Inner_commutatorDefectRS_covGrad_eq_frameSum_integral
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (S : SmoothCcTensor g r s) :
    tensorL2Inner (I := I) (M := M) g r (s + 1)
        (rawTensorConnLapSmooth (I := I) g r (s + 1) (covGrad (I := I) (M := M) g r s S) -
          covGrad (I := I) (M := M) g r s (rawTensorConnLapSmooth (I := I) g r s S)).toFun
        (covGrad (I := I) (M := M) g r s S).toFun =
      ∫ x, (∑ i : Fin (Module.finrank ℝ E),
              tensorInnerPointwise (I := I) (M := M) g r (s + 1) x
                (TensorRSSpace.toModel (remDiffFibRS (I := I) (M := M) g r s S x i))
                ((covGrad (I := I) (M := M) g r s S).toFun x))
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  rw [tensorL2Inner]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
  exact commutatorDefectRS_pairing_eq_frameSum (I := I) (M := M) g r s S x

/-- **The per-direction pure-Riemann genuine curvature direction linear map at rank `r`**
(pre-continuity). For the frame index `i`, the linear map in the curvature direction
`v ↦ riemannOp (tensorCov g r s) x (Bᵢ x) v (∇_{Bᵢ} S(x))` — the slot-`i` summand of the rank-`r`
pure-Riemann genuine trace `∑ᵢ R(Bᵢ, ·)(∇_{Bᵢ} S)`, with `Bᵢ := smoothOrthoFrame g x i` and
`∇_{Bᵢ} S := covApply (tensorCov g r s) (Bᵢ) (S.toSection)`. The curvature direction is read off the
bundled trilinear Riemann operator `riemannOp` of the `(r, s)`-tensor connection — the rank-`r`
curvature whose slot-wise soundness is `riemannSec_tensorCov_apply_eval`
(`TensorSlotwiseCurvatureRS`). The contravariant-rank-`r` mirror of `remDiffGenuineDirLM`. -/
def remDiffGenuineDirLMRS (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (x : M) (i : Fin (Module.finrank ℝ E)) :
    TangentSpace I x →ₗ[ℝ] TensorRSSpace r s I x where
  toFun v := riemannOp (tensorCov (I := I) g r s) x (smoothOrthoFrame (I := I) g x i x) v
    (covApply (tensorCov (I := I) g r s) (smoothOrthoFrame (I := I) g x i)
      (fun y : M => S.toSection y) x)
  map_add' v v' := by
    rw [(riemannOp (tensorCov (I := I) g r s) x
      (smoothOrthoFrame (I := I) g x i x)).map_add v v']; rfl
  map_smul' c v := by
    rw [(riemannOp (tensorCov (I := I) g r s) x
      (smoothOrthoFrame (I := I) g x i x)).map_smul c v]; rfl

/-- **The per-direction pure-Riemann genuine curvature direction CLM at rank `r`.** The
continuous-linear upgrade of `remDiffGenuineDirLMRS` (finite-dimensional source), the slot-`i`
curvature-direction-linear form `v ↦ R(Bᵢ, v)(∇_{Bᵢ} S(x))` of the rank-`r` pure-Riemann genuine
trace. The contravariant-rank-`r` mirror of `remDiffGenuineDirCLM`. -/
noncomputable def remDiffGenuineDirCLMRS (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (x : M) (i : Fin (Module.finrank ℝ E)) :
    TangentSpace I x →L[ℝ] TensorRSSpace r s I x :=
  haveI : T2Space (TangentSpace I x) := inferInstanceAs (T2Space E)
  haveI : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  LinearMap.toContinuousLinearMap (remDiffGenuineDirLMRS (I := I) (M := M) g r s S x i)

/-- The defining apply formula for `remDiffGenuineDirCLMRS`: the curvature contraction of the
slot-`i` directional covariant derivative. This is the public interface against which the downstream
`MovingFrameGenuineFieldPairingRS` identifies its own fixed-frame summand
`pureRDirCLMSummandFixedFrameRS g r s S (smoothOrthoFrame g x) x i`. -/
theorem remDiffGenuineDirCLMRS_apply (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (x : M) (i : Fin (Module.finrank ℝ E))
    (v : TangentSpace I x) :
    remDiffGenuineDirCLMRS (I := I) (M := M) g r s S x i v =
      riemannOp (tensorCov (I := I) g r s) x (smoothOrthoFrame (I := I) g x i x) v
        (covApply (tensorCov (I := I) g r s) (smoothOrthoFrame (I := I) g x i)
          (fun y : M => S.toSection y) x) := by
  rw [remDiffGenuineDirCLMRS, LinearMap.coe_toContinuousLinearMap', remDiffGenuineDirLMRS,
    LinearMap.coe_mk, AddHom.coe_mk]

/-- **The per-direction pure-Riemann genuine curvature fibre of the rank-`r` frame summand.** At a
point `x`, with `Bᵢ := smoothOrthoFrame g x i`, the pure-Riemann genuine-curvature part of the
`i`-th frame summand `remDiffFibRS g r s S x i` of the order-`2` commutator defect: the
rank-`(r, s + 1)` tensor obtained by uncurrying, through `covGradBundleEquiv r s x`, the
per-direction pure-Riemann curvature direction CLM `remDiffGenuineDirCLMRS` — the slot-`i` curvature
trace `v ↦ R(Bᵢ, v)(∇_{Bᵢ} S(x))` (the pure-Riemann `R(∇S)` contraction), read off the bundled
trilinear Riemann operator `riemannOp (tensorCov g r s)`.

This is the genuinely-tensorial pure-Riemann `R(∇S)` content carried by the `i`-th summand; its
frame sum is the fibre value of the order-`0` rank-`r` frame-free pure-Riemann operator on `∇S`
(`remDiffGenuineFibRS_sum_eq_genuinePureRDiffOp0_toSection`), identified downstream with the
concrete pure-Riemann genuine section `GcurvSectionRS g r s S`. The contravariant-rank-`r` mirror of
`remDiffGenuineFib`. -/
noncomputable def remDiffGenuineFibRS (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (x : M) (i : Fin (Module.finrank ℝ E)) :
    TensorRSSpace r (s + 1) I x :=
  covGradBundleEquiv (I := I) (M := M) r s x
    (remDiffGenuineDirCLMRS (I := I) (M := M) g r s S x i)

/-- **The per-direction frame-bracket remainder fibre of the rank-`r` frame summand.** The honest
moving-frame remainder of the `i`-th frame summand: the difference
`remDiffFibRS g r s S x i − remDiffGenuineFibRS g r s S x i` of the frame summand and its
pure-Riemann genuine curvature fibre, the rank-`(r, s + 1)` tensor carrying the
differentiated-curvature `(∇R) S` content and the frame-bracket discrepancy (the moving-frame
residual that the slot-`0` representation cannot remove).

This is the moving-frame discrepancy that the per-direction pointwise representation cannot remove
(the slot-`0` frame-trace matching is false on a normal manifold); only its *frame sum*, paired
against `∇S` and integrated over the closed manifold, carries the differentiated-curvature
divergence content (the rank-`r` divergence datum and integrated nullity, in the downstream files).
It is the honest named remainder over the genuine fibre `remDiffGenuineFibRS`, never an anonymous
subtraction of the conclusion. The contravariant-rank-`r` mirror of `remDiffBracketFib`. -/
noncomputable def remDiffBracketFibRS (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (x : M) (i : Fin (Module.finrank ℝ E)) :
    TensorRSSpace r (s + 1) I x :=
  remDiffFibRS (I := I) (M := M) g r s S x i - remDiffGenuineFibRS (I := I) (M := M) g r s S x i

/-- **The per-direction genuine/bracket split of the rank-`r` frame summand (sorry-free, by
definition of the named remainder).** For a closed smooth Riemannian manifold `(M, g)`,
contravariant rank `r`, covariant rank `s`, smooth compactly-supported `(r, s)`-tensor `S`, point
`x`, and frame index `i`, the `i`-th frame summand `remDiffFibRS g r s S x i` of the order-`2`
commutator defect is its pure-Riemann genuine curvature fibre plus its named frame-bracket
remainder:
```
remDiffFibRS g r s S x i = remDiffGenuineFibRS g r s S x i + remDiffBracketFibRS g r s S x i.
```
The frame-bracket remainder `remDiffBracketFibRS` is the honest named remainder
`remDiffFibRS − remDiffGenuineFibRS` over the genuine curvature fibre, so the split is
`add_sub_cancel` — sorry-free. The genuine content of the decomposition lives in the integrated
per-family identities (`remDiffFibRS_genuineFrameSum_pairing_eq_genuineFields` here; the bracket
divergence datum and integrated nullity downstream). The contravariant-rank-`r` mirror of
`remDiffFib_eq_genuine_add_bracket`. -/
theorem remDiffFibRS_eq_genuine_add_bracket (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (x : M) (i : Fin (Module.finrank ℝ E)) :
    remDiffFibRS (I := I) (M := M) g r s S x i =
      remDiffGenuineFibRS (I := I) (M := M) g r s S x i +
        remDiffBracketFibRS (I := I) (M := M) g r s S x i := by
  rw [remDiffBracketFibRS, add_sub_cancel]

/-- **The pure-Riemann genuine fibre frame-sum is the order-`0` rank-`r` frame-free pure-Riemann
operator value on `∇S`, pointwise (sorry-free).** For a closed smooth Riemannian manifold `(M, g)`,
contravariant rank `r`, covariant rank `s`, smooth compactly-supported `(r, s)`-tensor `S`, and
point `x`, the fixed-frame sum of the per-direction pure-Riemann genuine curvature fibres
`remDiffGenuineFibRS` is the fibre value of the order-`0` operator of the rank-`r` frame-free
pure-Riemann differentiated curvature tower (`RankRPureRCurvatureTower`) applied to the gradient
field `∇S := covGrad g r s S`:
```
∑ᵢ remDiffGenuineFibRS g r s S x i = (genuinePureRDiffOpRS g r 0 (s + 1) (∇S)).toSection x.
```

**Proof (sorry-free).** Each fibre `remDiffGenuineFibRS g r s S x i` is the slot-`0` uncurry through
`covGradBundleEquiv r s x` of the curvature-direction CLM `remDiffGenuineDirCLMRS g r s S x i`. The
public slot-`0` reading `genuinePureRDiffOp0_covGrad_fib_eq` expresses the order-`0`-on-`∇S` fibre,
read back through `covGradBundleEquiv.symm`, as exactly the frame sum of the same curvature
contractions `v ↦ ∑ᵢ R(Bᵢ x, v)(∇_{Bᵢ} S(x))` (`remDiffGenuineDirCLMRS_apply`), so the two sides
agree after pushing `covGradBundleEquiv r s x` (a continuous-linear equivalence) through the frame
sum (`map_sum`). The pure-Riemann trace is genuinely tensorial (direction-linear, read off
`riemannOp`), so this is a sound pointwise frame-sum identity. Downstream, the tower bridge
identifies the right-hand side with `(GcurvSectionRS g r s S).toSection x` — the rank-`r` mirror of
`remDiffGenuineFib_sum_eq_GcurvSection_toSection`. -/
theorem remDiffGenuineFibRS_sum_eq_genuinePureRDiffOp0_toSection
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (S : SmoothCcTensor g r s) (x : M) :
    (∑ i : Fin (Module.finrank ℝ E), remDiffGenuineFibRS (I := I) (M := M) g r s S x i) =
      (genuinePureRDiffOpRS (I := I) (M := M) g r 0 (s + 1)
        (covGrad (I := I) (M := M) g r s S)).toSection x := by
  classical
  have hCLM : (covGradBundleEquiv (I := I) (M := M) r s x).symm
      ((genuinePureRDiffOpRS (I := I) (M := M) g r 0 (s + 1)
        (covGrad (I := I) (M := M) g r s S)).toSection x) =
      ∑ i : Fin (Module.finrank ℝ E),
        remDiffGenuineDirCLMRS (I := I) (M := M) g r s S x i := by
    refine ContinuousLinearMap.ext (fun v => ?_)
    rw [ContinuousLinearMap.sum_apply,
      genuinePureRDiffOp0_covGrad_fib_eq (I := I) (M := M) g r s S x v]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [remDiffGenuineDirCLMRS_apply]
  rw [(ContinuousLinearEquiv.symm_apply_eq (covGradBundleEquiv (I := I) (M := M) r s x)).mp hCLM,
    map_sum]
  exact Finset.sum_congr rfl (fun i _ => rfl)

/-- **The pure-Riemann genuine fibre frame-sum against the order-`0` moving-centre endomorphism
(sorry-free).** The same pointwise identification as
`remDiffGenuineFibRS_sum_eq_genuinePureRDiffOp0_toSection`, stated against the order-`0`
moving-centre pure-Riemann curvature endomorphism `genuinePureREndo0RS` (to which the order-`0`
differentiated operator definitionally reduces). -/
theorem remDiffGenuineFibRS_sum_eq_genuinePureREndo0RS_toSection
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (S : SmoothCcTensor g r s) (x : M) :
    (∑ i : Fin (Module.finrank ℝ E), remDiffGenuineFibRS (I := I) (M := M) g r s S x i) =
      (genuinePureREndo0RS (I := I) (M := M) g r (s + 1)
        (covGrad (I := I) (M := M) g r s S)).toSection x :=
  remDiffGenuineFibRS_sum_eq_genuinePureRDiffOp0_toSection (I := I) (M := M) g r s S x

/-- **The genuine frame-sum integrand equals the order-`0` rank-`r` pure-Riemann operator pairing
integrand (sorry-free).** For a closed smooth Riemannian manifold `(M, g)`, contravariant rank `r`,
covariant rank `s`, smooth compactly-supported `(r, s)`-tensor `S`, and point `x`, the fixed-frame
sum of the per-direction pure-Riemann genuine curvature fibres `remDiffGenuineFibRS`, paired against
`∇S := covGrad g r s S`, is the pointwise metric inner product of the order-`0` rank-`r` frame-free
pure-Riemann operator value on `∇S` against `∇S`:
```
∑ᵢ ⟨remDiffGenuineFibRS g r s S x i, ∇S(x)⟩ = ⟨genuinePureRDiffOpRS g r 0 (s + 1) (∇S), ∇S⟩(x).
```

**Proof (sorry-free).** Pull the frame sum into the left argument of `tensorInnerPointwise`
(`tensorInnerPointwise_sum_left`, weights `1`), reduce
`∑ᵢ TensorRSSpace.toModel (remDiffGenuineFibRS …) = TensorRSSpace.toModel (∑ᵢ remDiffGenuineFibRS …)`
by additivity of `TensorRSSpace.toModel`, and rewrite the inner frame sum by the sorry-free pointwise
identity `remDiffGenuineFibRS_sum_eq_genuinePureRDiffOp0_toSection`. The contravariant-rank-`r`
mirror of `genuineFrameSum_pairing_pointwise_eq_GcurvSection`. -/
theorem genuineFrameSumRS_pairing_pointwise_eq_genuinePureRDiffOp0
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (S : SmoothCcTensor g r s) (x : M) :
    (∑ i : Fin (Module.finrank ℝ E),
        tensorInnerPointwise (I := I) (M := M) g r (s + 1) x
          (TensorRSSpace.toModel (remDiffGenuineFibRS (I := I) (M := M) g r s S x i))
          ((covGrad (I := I) (M := M) g r s S).toFun x)) =
      tensorInnerPointwise (I := I) (M := M) g r (s + 1) x
        ((genuinePureRDiffOpRS (I := I) (M := M) g r 0 (s + 1)
          (covGrad (I := I) (M := M) g r s S)).toFun x)
        ((covGrad (I := I) (M := M) g r s S).toFun x) := by
  classical
  have htoM : TensorRSSpace.toModel
        (∑ i : Fin (Module.finrank ℝ E), remDiffGenuineFibRS (I := I) (M := M) g r s S x i) =
      ∑ i : Fin (Module.finrank ℝ E),
        TensorRSSpace.toModel (remDiffGenuineFibRS (I := I) (M := M) g r s S x i) := by
    induction (Finset.univ : Finset (Fin (Module.finrank ℝ E))) using Finset.induction with
    | empty => simp [TensorRSSpace.toModel_zero]
    | insert i₀ s'' hi₀ ih =>
        rw [Finset.sum_insert hi₀, TensorRSSpace.toModel_add, ih, Finset.sum_insert hi₀]
  rw [show (genuinePureRDiffOpRS (I := I) (M := M) g r 0 (s + 1)
          (covGrad (I := I) (M := M) g r s S)).toFun x =
        TensorRSSpace.toModel ((genuinePureRDiffOpRS (I := I) (M := M) g r 0 (s + 1)
          (covGrad (I := I) (M := M) g r s S)).toSection x) from
      SmoothCcTensor.toFun_apply (genuinePureRDiffOpRS (I := I) (M := M) g r 0 (s + 1)
        (covGrad (I := I) (M := M) g r s S)) x,
    ← remDiffGenuineFibRS_sum_eq_genuinePureRDiffOp0_toSection (I := I) (M := M) g r s S x, htoM]
  rw [show (∑ i : Fin (Module.finrank ℝ E),
        TensorRSSpace.toModel (remDiffGenuineFibRS (I := I) (M := M) g r s S x i)) =
      ∑ i : Fin (Module.finrank ℝ E), (1 : ℝ) •
        TensorRSSpace.toModel (remDiffGenuineFibRS (I := I) (M := M) g r s S x i) from by
    refine Finset.sum_congr rfl (fun i _ => ?_); rw [one_smul]]
  rw [tensorInnerPointwise_sum_left (I := I) (M := M) g r (s + 1) x Finset.univ]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [one_mul]

/-- **The rank-`r` pure-Riemann genuine frame-sum pairing equals the order-`0` rank-`r` pure-Riemann
operator value (sorry-free, integrated form).** For a closed smooth Riemannian manifold `(M, g)`,
contravariant rank `r`, covariant rank `s`, and smooth compactly-supported `(r, s)`-tensor `S`, the
pure-Riemann genuine frame-sum integrand is Bochner-integrable against the Riemannian volume
measure, and its integral over the closed manifold equals the global metric `L²` pairing of the
order-`0` rank-`r` frame-free pure-Riemann operator value on `∇S := covGrad g r s S` against `∇S`:
```
∫_M ∑ᵢ ⟨remDiffGenuineFibRS g r s S x i, ∇S(x)⟩ dvol_g
  = ⟨genuinePureRDiffOpRS g r 0 (s + 1) (∇S), ∇S⟩_{L²}.
```

This is the **rank-`r` pure-Riemann genuine-sum identification** (per-family integrated identity).
The genuine per-direction fibres carry the pure-Riemann `R(Bᵢ, ·)(∇_{Bᵢ} S)` contraction; their
frame sum is the order-`0` rank-`r` frame-free pure-Riemann operator value on `∇S`
(`remDiffGenuineFibRS_sum_eq_genuinePureRDiffOp0_toSection`), a smooth compactly-supported
`(r, s + 1)`-tensor section, so the integrand is the smooth cross-pairing of two smooth
compactly-supported sections (`SmoothCcTensor.integrable_inner_cross`) and the integral is its
`tensorL2Inner`. The pure-Riemann trace is genuinely tensorial in the direction (linear in `v`
through `riemannOp`), so this is a *sound pointwise* frame-sum identity — no
`smoothExtensionTangent` obstruction. Downstream, the tower bridge replaces the operator value by
the concrete section `GcurvSectionRS g r s S` — the contravariant-rank-`r` mirror of
`remDiffFib_genuineFrameSum_pairing_eq_genuineFields`. -/
theorem remDiffFibRS_genuineFrameSum_pairing_eq_genuineFields
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
        (genuinePureRDiffOpRS (I := I) (M := M) g r 0 (s + 1)
          (covGrad (I := I) (M := M) g r s S)).toFun
        (covGrad (I := I) (M := M) g r s S).toFun := by
  classical
  have hpoint : (fun x => ∑ i : Fin (Module.finrank ℝ E),
        tensorInnerPointwise (I := I) (M := M) g r (s + 1) x
          (TensorRSSpace.toModel (remDiffGenuineFibRS (I := I) (M := M) g r s S x i))
          ((covGrad (I := I) (M := M) g r s S).toFun x)) =
      (fun x => tensorInnerPointwise (I := I) (M := M) g r (s + 1) x
          ((genuinePureRDiffOpRS (I := I) (M := M) g r 0 (s + 1)
            (covGrad (I := I) (M := M) g r s S)).toFun x)
          ((covGrad (I := I) (M := M) g r s S).toFun x)) := by
    funext x
    exact genuineFrameSumRS_pairing_pointwise_eq_genuinePureRDiffOp0 (I := I) (M := M) g r s S x
  have hint : MeasureTheory.Integrable
      (fun x => tensorInnerPointwise (I := I) (M := M) g r (s + 1) x
          ((genuinePureRDiffOpRS (I := I) (M := M) g r 0 (s + 1)
            (covGrad (I := I) (M := M) g r s S)).toFun x)
          ((covGrad (I := I) (M := M) g r s S).toFun x))
      (riemannianVolumeMeasure (I := I) (M := M) g) :=
    DifferentialGeometry.Integral.L2.SmoothCcTensor.integrable_inner_cross (I := I) (M := M)
      (genuinePureRDiffOpRS (I := I) (M := M) g r 0 (s + 1)
        (covGrad (I := I) (M := M) g r s S))
      (covGrad (I := I) (M := M) g r s S)
  refine ⟨hpoint ▸ hint, ?_⟩
  rw [tensorL2Inner]
  exact hpoint ▸ rfl

end Connection
end Integral
end DifferentialGeometry

end
