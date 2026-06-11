import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.MovingFrameCurvatureTraceSmooth
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.MovingFrameIntegratedNullity
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.MovingFramePureRCurvatureTracePairing
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.FrozenFramePureRCurvatureTower
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.RicciTraceCarrier
import DifferentialGeometry.Analysis.Spectral.Tensor.Variational.FrameInvariance

/-!
# The frame-summed integrand of the moving-frame remainder pairing and its pure-Riemann genuine leg

For a closed (compact, boundaryless) smooth Riemannian manifold `(M, g)` this file builds the
**frame-summed pointwise integrand** of the curvature cross-pairing `⟨Curv S, ∇S⟩_{L²}` of the
rank-generic order-`2` rough-Laplacian / covariant-gradient commutator defect
`Curv S := Δ_∇(∇S) − ∇(Δ_∇ S)` (`pointwiseTensorCurv g s S`, `∇S = covGrad g 0 s S`), the
per-direction genuine/bracket split of the frame summand, and the **pure-Riemann genuine-sum
identification** with the concrete pure-Riemann genuine section `GcurvSection g s S`.

This is the upstream-safe frame-sum bridge of the curvature line's terminal quantitative leaf: it
holds everything that needs only the pure-Riemann genuine trace `GcurvSection` (built from `g, R`
alone, frame-free, tensorial), so the leaf file `MovingFrameDiffCurvTraceSection` can import it and
discharge the leaf over its own concrete differentiated-curvature section `genuineDiffCurvSection`.

## The frame-summand decomposition of the integrand

The sorry-free representation `pointwiseTensorCurv_toSection_eq_frame_sum`
(`Bochner/PointwiseTensorBochner`) reads the defect, at every point `x` and over the `g_x`-orthonormal
frame `Bᵢ := smoothOrthoFrame g x i`, as the fixed-frame sum of the **per-summand third-order
difference** `remDiffFib g s S x i := ∇²_{Bᵢ, Bᵢ}(∇S)(x) − covGradBundleEquiv 0 s x (∇·(∇²_{Bᵢ, Bᵢ}
S)(x))`. Pairing against `∇S(x)` and distributing the metric inner product over the frame sum gives the
**integrand frame-sum identity** (`pointwiseTensorCurvPairing_eq_frameSum`):
`⟨Curv S, ∇S⟩(x) = ∑ᵢ ⟨remDiffFib g s S x i, ∇S(x)⟩`, integrated to
`⟨Curv S, ∇S⟩_{L²} = ∫_M ∑ᵢ ⟨remDiffFib g s S x i, ∇S(x)⟩ dvol_g`
(`tensorL2Inner_pointwiseTensorCurv_covGrad_eq_frameSum_integral`).

## The per-direction genuine/bracket split and the pure-Riemann genuine-sum identification

Each frame summand splits into its pure-Riemann genuine curvature fibre `remDiffGenuineFib` (the
slot-`0` uncurry of the curvature-direction CLM `v ↦ R(Bᵢ, v)(∇_{Bᵢ} S)`, the pure-Riemann `R(∇S)`
contraction, genuinely tensorial in the direction) and its named frame-bracket remainder
`remDiffBracketFib := remDiffFib − remDiffGenuineFib` (carrying the differentiated-curvature `(∇R) S`
content and the `∇²S`-order frame-bracket discrepancy). The pure-Riemann genuine fibres' frame-sum
pairing against `∇S`, integrated, is `⟨GcurvSection g s S, ∇S⟩_{L²}`
(`remDiffFib_genuineFrameSum_pairing_eq_genuineFields`) — a *sound pointwise* frame-sum identity since
the pure-Riemann trace is tensorial.

## Main results

* `remDiffFib`, `pointwiseTensorCurvPairing_eq_frameSum`,
  `tensorL2Inner_pointwiseTensorCurv_covGrad_eq_frameSum_integral` — the frame-sum integrand of the
  curvature cross-pairing.
* `remDiffGenuineFib`, `remDiffBracketFib`, `remDiffFib_eq_genuine_add_bracket` — the per-direction
  pure-Riemann genuine fibre and its named frame-bracket remainder.
* `remDiffFib_genuineFrameSum_pairing_eq_genuineFields` — the pure-Riemann genuine-sum identification
  (posit, per-family integrated identity): the genuine frame-sum integral is `⟨GcurvSection, ∇S⟩_{L²}`,
  with the genuine integrand Bochner-integrable.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
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

/-- **The per-summand third-order difference field of representation (A).** At a point `x`, with the
`g_x`-orthonormal frame `Bᵢ := smoothOrthoFrame g x i`, the `i`-th summand of the fixed-frame
representation `pointwiseTensorCurv_toSection_eq_frame_sum` of the order-`2` commutator defect:
```
remDiffFib g s S x i
  := ∇²_{Bᵢ, Bᵢ}(∇S)(x) − covGradBundleEquiv 0 s x (∇·(∇²_{Bᵢ, Bᵢ} S)(x)),
```
the difference of the rank-`(0, s + 1)` second covariant derivative of the gradient tensor
`∇S = covGrad g 0 s S` and the `(0, s + 1)`-tensor covariant gradient of the rank-`(0, s)` second
covariant derivative `∇²_{Bᵢ, Bᵢ} S`. It is the gradient-slot reordering of the three covariant
derivative slots — the genuine off-diagonal Riemann curvature. -/
def remDiffFib (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) (x : M)
    (i : Fin (Module.finrank ℝ E)) : TensorRSSpace 0 (s + 1) I x :=
  tensorSecondCovDeriv (I := I) g 0 (s + 1)
      (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x i)
      (fun y : M => (covGrad (I := I) (M := M) g 0 s S).toSection y) x -
    covGradBundleEquiv (I := I) (M := M) 0 s x
      ((tensorCov (I := I) g 0 s).toFun
        (fun y : M => tensorSecondCovDeriv (I := I) g 0 s
          (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x i)
          (fun z : M => S.toSection z) y) x)

/-- **The frame-summand integrand identity (sorry-free).** For a closed smooth Riemannian manifold
`(M, g)`, covariant rank `s`, smooth compactly-supported `(0, s)`-tensor `S`, and point `x`, the
pointwise metric inner product of the order-`2` commutator defect `Curv S := pointwiseTensorCurv g s S`
against the gradient field `∇S := covGrad g 0 s S` — the integrand of the curvature cross-pairing
`⟨Curv S, ∇S⟩_{L²}` — is the fixed-frame sum of the per-summand pairings of the third-order difference
fields against `∇S`:
```
⟨Curv S, ∇S⟩(x) = ∑ᵢ ⟨remDiffFib g s S x i, ∇S(x)⟩,   Bᵢ := smoothOrthoFrame g x i.
```

**Proof (sorry-free).** Read the defect at `x` by the fixed-frame representation
`pointwiseTensorCurv_toSection_eq_frame_sum`, push the model coercion through the frame sum by
additivity of `TensorRSSpace.toModel`, and distribute the pointwise metric inner product over the frame
sum by `tensorInnerPointwise_sum_left`. No moving-frame derivative and no curvature input is used — this
is the purely structural integrand decomposition. -/
theorem pointwiseTensorCurvPairing_eq_frameSum
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) (x : M) :
    tensorInnerPointwise (I := I) (M := M) g 0 (s + 1) x
        ((pointwiseTensorCurv (I := I) (M := M) g s S).toFun x)
        ((covGrad (I := I) (M := M) g 0 s S).toFun x) =
      ∑ i : Fin (Module.finrank ℝ E),
        tensorInnerPointwise (I := I) (M := M) g 0 (s + 1) x
          (TensorRSSpace.toModel (remDiffFib (I := I) (M := M) g s S x i))
          ((covGrad (I := I) (M := M) g 0 s S).toFun x) := by
  classical
  have hCurv : (pointwiseTensorCurv (I := I) (M := M) g s S).toFun x =
      TensorRSSpace.toModel ((pointwiseTensorCurv (I := I) (M := M) g s S).toSection x) := rfl
  have htoM : TensorRSSpace.toModel
        (∑ i : Fin (Module.finrank ℝ E), remDiffFib (I := I) (M := M) g s S x i) =
      ∑ i : Fin (Module.finrank ℝ E),
        TensorRSSpace.toModel (remDiffFib (I := I) (M := M) g s S x i) := by
    induction (Finset.univ : Finset (Fin (Module.finrank ℝ E))) using Finset.induction with
    | empty => simp [TensorRSSpace.toModel_zero]
    | insert i₀ s'' hi₀ ih =>
        rw [Finset.sum_insert hi₀, TensorRSSpace.toModel_add, ih, Finset.sum_insert hi₀]
  rw [hCurv, pointwiseTensorCurv_toSection_eq_frame_sum (I := I) (M := M) g s S x]
  rw [show (∑ i : Fin (Module.finrank ℝ E),
        (tensorSecondCovDeriv (I := I) g 0 (s + 1)
            (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x i)
            (fun y : M => (covGrad (I := I) (M := M) g 0 s S).toSection y) x -
          covGradBundleEquiv (I := I) (M := M) 0 s x
            ((tensorCov (I := I) g 0 s).toFun
              (fun y : M => tensorSecondCovDeriv (I := I) g 0 s
                (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x i)
                (fun z : M => S.toSection z) y) x))) =
      ∑ i : Fin (Module.finrank ℝ E), remDiffFib (I := I) (M := M) g s S x i from rfl]
  rw [htoM]
  rw [show (∑ i : Fin (Module.finrank ℝ E),
        TensorRSSpace.toModel (remDiffFib (I := I) (M := M) g s S x i)) =
      ∑ i : Fin (Module.finrank ℝ E), (1 : ℝ) •
        TensorRSSpace.toModel (remDiffFib (I := I) (M := M) g s S x i) from by
    refine Finset.sum_congr rfl (fun i _ => ?_); rw [one_smul]]
  rw [tensorInnerPointwise_sum_left (I := I) (M := M) g 0 (s + 1) x Finset.univ]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [one_mul]

/-- **The curvature cross-pairing as the integral of the frame-summed remainder integrand
(sorry-free).** For a closed smooth Riemannian manifold `(M, g)`, covariant rank `s`, and smooth
compactly-supported `(0, s)`-tensor `S`, the global metric `L²` pairing of the order-`2` commutator
defect `Curv S := pointwiseTensorCurv g s S` against `∇S := covGrad g 0 s S` is the integral over the
closed manifold of the fixed-frame sum of the per-summand pairings `⟨remDiffFib …, ∇S⟩`:
```
⟨Curv S, ∇S⟩_{L²} = ∫_M ∑ᵢ ⟨remDiffFib g s S x i, ∇S(x)⟩ dvol_g.
```

**Proof (sorry-free).** Unfold `tensorL2Inner` to the integral of the pointwise pairing and rewrite
the integrand pointwise by the sorry-free frame-summand identity
`pointwiseTensorCurvPairing_eq_frameSum`. -/
theorem tensorL2Inner_pointwiseTensorCurv_covGrad_eq_frameSum_integral
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) :
    tensorL2Inner (I := I) (M := M) g 0 (s + 1)
        (pointwiseTensorCurv (I := I) (M := M) g s S).toFun
        (covGrad (I := I) (M := M) g 0 s S).toFun =
      ∫ x, (∑ i : Fin (Module.finrank ℝ E),
              tensorInnerPointwise (I := I) (M := M) g 0 (s + 1) x
                (TensorRSSpace.toModel (remDiffFib (I := I) (M := M) g s S x i))
                ((covGrad (I := I) (M := M) g 0 s S).toFun x))
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  rw [tensorL2Inner]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
  exact pointwiseTensorCurvPairing_eq_frameSum (I := I) (M := M) g s S x

/-- **The per-direction pure-Riemann genuine curvature direction linear map** (pre-continuity). For the
frame index `i`, the linear map in the curvature direction
`v ↦ riemannOp (tensorCov g 0 s) x (Bᵢ x) v (∇_{Bᵢ} S(x))` — the slot-`i` summand of the pure-Riemann
genuine trace `∑ᵢ R(Bᵢ, ·)(∇_{Bᵢ} S)`, with `Bᵢ := smoothOrthoFrame g x i` and `∇_{Bᵢ} S :=
covApply (tensorCov g 0 s) (Bᵢ) (S.toSection)`. The curvature direction is read off the bundled
trilinear Riemann operator `riemannOp`, linear in its middle/direction slot. -/
def remDiffGenuineDirLM (g : SmoothRiemannianMetric I M) (s : ℕ)
    (S : SmoothCcTensor g 0 s) (x : M) (i : Fin (Module.finrank ℝ E)) :
    TangentSpace I x →ₗ[ℝ] TensorRSSpace 0 s I x where
  toFun v := riemannOp (tensorCov (I := I) g 0 s) x (smoothOrthoFrame (I := I) g x i x) v
    (covApply (tensorCov (I := I) g 0 s) (smoothOrthoFrame (I := I) g x i)
      (fun y : M => S.toSection y) x)
  map_add' v v' := by
    rw [(riemannOp (tensorCov (I := I) g 0 s) x
      (smoothOrthoFrame (I := I) g x i x)).map_add v v']; rfl
  map_smul' c v := by
    rw [(riemannOp (tensorCov (I := I) g 0 s) x
      (smoothOrthoFrame (I := I) g x i x)).map_smul c v]; rfl

/-- **The per-direction pure-Riemann genuine curvature direction CLM.** The continuous-linear upgrade
of `remDiffGenuineDirLM` (finite-dimensional source), the slot-`i` curvature-direction-linear form
`v ↦ R(Bᵢ, v)(∇_{Bᵢ} S(x))` of the pure-Riemann genuine trace. -/
noncomputable def remDiffGenuineDirCLM (g : SmoothRiemannianMetric I M) (s : ℕ)
    (S : SmoothCcTensor g 0 s) (x : M) (i : Fin (Module.finrank ℝ E)) :
    TangentSpace I x →L[ℝ] TensorRSSpace 0 s I x :=
  haveI : T2Space (TangentSpace I x) := inferInstanceAs (T2Space E)
  haveI : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  LinearMap.toContinuousLinearMap (remDiffGenuineDirLM (I := I) (M := M) g s S x i)

/-- **The per-direction pure-Riemann genuine curvature fibre of the frame summand.** At a point `x`,
with `Bᵢ := smoothOrthoFrame g x i`, the pure-Riemann genuine-curvature part of the `i`-th frame summand
`remDiffFib g s S x i` of the order-`2` commutator defect: the rank-`(0, s + 1)` tensor obtained by
uncurrying, through `covGradBundleEquiv 0 s x`, the per-direction pure-Riemann curvature direction CLM
`remDiffGenuineDirCLM` — the slot-`i` curvature trace `v ↦ R(Bᵢ, v)(∇_{Bᵢ} S(x))` (the pure-Riemann
`R(∇S)` contraction), read off the bundled trilinear Riemann operator `riemannOp`.

This is the genuinely-tensorial pure-Riemann `R(∇S)` content carried by the `i`-th summand; its frame
sum is the concrete pure-Riemann genuine section `GcurvSection g s S` (frame-free, tensorial), so its
frame-sum pairing against `∇S` and integrated is `⟨GcurvSection g s S, ∇S⟩_{L²}`
(`remDiffFib_genuineFrameSum_pairing_eq_genuineFields`). -/
noncomputable def remDiffGenuineFib (g : SmoothRiemannianMetric I M) (s : ℕ)
    (S : SmoothCcTensor g 0 s) (x : M) (i : Fin (Module.finrank ℝ E)) :
    TensorRSSpace 0 (s + 1) I x :=
  covGradBundleEquiv (I := I) (M := M) 0 s x
    (remDiffGenuineDirCLM (I := I) (M := M) g s S x i)

/-- **The per-direction frame-bracket remainder fibre of the frame summand.** The honest moving-frame
remainder of the `i`-th frame summand: the difference `remDiffFib g s S x i − remDiffGenuineFib g s S
x i` of the frame summand and its pure-Riemann genuine curvature fibre, the rank-`(0, s + 1)` tensor
carrying the differentiated-curvature `(∇R) S` content and the frame-bracket discrepancy
(`tensor3rdCurvBracket` plus the frame-trace discrepancy and the moving-frame residual that the slot-`0`
representation cannot remove).

This is the moving-frame discrepancy that the per-direction pointwise representation cannot remove (the
slot-`0` frame-trace matching is false on a normal manifold); only its *frame sum*, paired against `∇S`
and integrated over the closed manifold, equals `⟨genuineDiffCurvSection g s S, ∇S⟩_{L²}` (the
differentiated-curvature genuine-sum identification with integrated bracket nullity, in the leaf file).
It is the honest named remainder over the genuine fibre `remDiffGenuineFib`, never an anonymous
subtraction of the conclusion. -/
noncomputable def remDiffBracketFib (g : SmoothRiemannianMetric I M) (s : ℕ)
    (S : SmoothCcTensor g 0 s) (x : M) (i : Fin (Module.finrank ℝ E)) :
    TensorRSSpace 0 (s + 1) I x :=
  remDiffFib (I := I) (M := M) g s S x i - remDiffGenuineFib (I := I) (M := M) g s S x i

/-- **The per-direction genuine/bracket split of the frame summand (sorry-free, by definition of the
named remainder).** For a closed smooth Riemannian manifold `(M, g)`, covariant rank `s`, smooth
compactly-supported `(0, s)`-tensor `S`, point `x`, and frame index `i`, the `i`-th frame summand
`remDiffFib g s S x i` of the order-`2` commutator defect is its pure-Riemann genuine curvature fibre
plus its named frame-bracket remainder:
```
remDiffFib g s S x i = remDiffGenuineFib g s S x i + remDiffBracketFib g s S x i.
```
The frame-bracket remainder `remDiffBracketFib` is the honest named remainder `remDiffFib −
remDiffGenuineFib` over the genuine curvature fibre, so the split is `add_sub_cancel` — sorry-free. The
genuine content of the decomposition lives in the two *integrated* per-family identities
`remDiffFib_genuineFrameSum_pairing_eq_genuineFields` (the genuine fibres carry the concrete
pure-Riemann section value) and `integral_frameSum_remDiffBracket_pairing_eq_zero` (the bracket
remainder's integrated pairing against `∇S` is the differentiated-curvature section value, the bracket
discrepancy integrating to zero), the latter in the leaf file. -/
theorem remDiffFib_eq_genuine_add_bracket (g : SmoothRiemannianMetric I M) (s : ℕ)
    (S : SmoothCcTensor g 0 s) (x : M) (i : Fin (Module.finrank ℝ E)) :
    remDiffFib (I := I) (M := M) g s S x i =
      remDiffGenuineFib (I := I) (M := M) g s S x i +
        remDiffBracketFib (I := I) (M := M) g s S x i := by
  rw [remDiffBracketFib, add_sub_cancel]

omit [CompactSpace M] [I.Boundaryless] in
/-- **The per-direction pure-Riemann genuine curvature direction CLM is the slot-`i` summand of the
pure-Riemann genuine direction CLM (sorry-free, by definition).** The frame-bridge object
`remDiffGenuineDirCLM g s S x i` (the slot-`i` curvature direction CLM `v ↦ R(Bᵢ, v)(∇_{Bᵢ} S(x))`)
coincides with the trace-section summand `genuinePureRDirCLMSummand g s S x i` of
`MovingFrameCurvatureTraceSmooth`: both are the continuous-linear upgrade of the identical
curvature-direction linear map. -/
theorem remDiffGenuineDirCLM_eq_genuinePureRDirCLMSummand
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) (x : M)
    (i : Fin (Module.finrank ℝ E)) :
    remDiffGenuineDirCLM (I := I) (M := M) g s S x i =
      genuinePureRDirCLMSummand (I := I) (M := M) g s S x i := rfl

/-- **The pure-Riemann genuine fibre frame-sum is the concrete pure-Riemann section value, pointwise
(sorry-free).** For a closed smooth Riemannian manifold `(M, g)`, covariant rank `s`, smooth
compactly-supported `(0, s)`-tensor `S`, and point `x`, the fixed-frame sum of the per-direction
pure-Riemann genuine curvature fibres `remDiffGenuineFib` is the fibre value of the concrete
pure-Riemann genuine curvature section `GcurvSection g s S`:
```
∑ᵢ remDiffGenuineFib g s S x i = (GcurvSection g s S).toSection x.
```

**Proof (sorry-free).** Each fibre `remDiffGenuineFib g s S x i` is the slot-`0` uncurry through
`covGradBundleEquiv 0 s x` of the curvature-direction CLM `remDiffGenuineDirCLM g s S x i`, which is
the trace-section summand `genuinePureRDirCLMSummand g s S x i`. Pushing
`covGradBundleEquiv 0 s x` (a continuous-linear equivalence) through the frame sum (`map_sum`)
reconstructs `covGradBundleEquiv 0 s x (∑ᵢ genuinePureRDirCLMSummand g s S x i) =
covGradBundleEquiv 0 s x (genuinePureRDirCLM g s S x) = genuineCurvPureRFib g s S x`, which is the
fibre value of `GcurvSection g s S` (`genuineCurvPureRSection_toSection`). The pure-Riemann trace is
genuinely tensorial (direction-linear, read off `riemannOp`), so this is a sound pointwise frame-sum
identity. -/
theorem remDiffGenuineFib_sum_eq_GcurvSection_toSection
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) (x : M) :
    (∑ i : Fin (Module.finrank ℝ E), remDiffGenuineFib (I := I) (M := M) g s S x i) =
      (GcurvSection (I := I) (M := M) g s S).toSection x := by
  classical
  have hfib : ∀ i : Fin (Module.finrank ℝ E),
      remDiffGenuineFib (I := I) (M := M) g s S x i =
        covGradBundleEquiv (I := I) (M := M) 0 s x
          (genuinePureRDirCLMSummand (I := I) (M := M) g s S x i) := by
    intro i
    rw [remDiffGenuineFib, remDiffGenuineDirCLM_eq_genuinePureRDirCLMSummand]
  rw [Finset.sum_congr rfl (fun i _ => hfib i),
    ← map_sum (covGradBundleEquiv (I := I) (M := M) 0 s x)
      (fun i : Fin (Module.finrank ℝ E) =>
        genuinePureRDirCLMSummand (I := I) (M := M) g s S x i) Finset.univ]
  rfl

/-- **The genuine frame-sum integrand equals the concrete pure-Riemann section pairing integrand
(sorry-free).** For a closed smooth Riemannian manifold `(M, g)`, covariant rank `s`, smooth
compactly-supported `(0, s)`-tensor `S`, and point `x`, the fixed-frame sum of the per-direction
pure-Riemann genuine curvature fibres `remDiffGenuineFib`, paired against `∇S := covGrad g 0 s S`,
is the pointwise metric inner product of the concrete pure-Riemann genuine section `GcurvSection g s S`
against `∇S`:
```
∑ᵢ ⟨remDiffGenuineFib g s S x i, ∇S(x)⟩ = ⟨GcurvSection g s S, ∇S⟩(x).
```

**Proof (sorry-free).** Pull the frame sum into the left argument of `tensorInnerPointwise`
(`tensorInnerPointwise_sum_left`, weights `1`), reduce `∑ᵢ TensorRSSpace.toModel (remDiffGenuineFib …)
= TensorRSSpace.toModel (∑ᵢ remDiffGenuineFib …)` by additivity of `TensorRSSpace.toModel`, and rewrite
the inner frame sum by the sorry-free pointwise identity
`remDiffGenuineFib_sum_eq_GcurvSection_toSection`; the model coercion of the section fibre value is
`(GcurvSection g s S).toFun x`. -/
theorem genuineFrameSum_pairing_pointwise_eq_GcurvSection
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) (x : M) :
    (∑ i : Fin (Module.finrank ℝ E),
        tensorInnerPointwise (I := I) (M := M) g 0 (s + 1) x
          (TensorRSSpace.toModel (remDiffGenuineFib (I := I) (M := M) g s S x i))
          ((covGrad (I := I) (M := M) g 0 s S).toFun x)) =
      tensorInnerPointwise (I := I) (M := M) g 0 (s + 1) x
        ((GcurvSection (I := I) (M := M) g s S).toFun x)
        ((covGrad (I := I) (M := M) g 0 s S).toFun x) := by
  classical
  have htoM : TensorRSSpace.toModel
        (∑ i : Fin (Module.finrank ℝ E), remDiffGenuineFib (I := I) (M := M) g s S x i) =
      ∑ i : Fin (Module.finrank ℝ E),
        TensorRSSpace.toModel (remDiffGenuineFib (I := I) (M := M) g s S x i) := by
    induction (Finset.univ : Finset (Fin (Module.finrank ℝ E))) using Finset.induction with
    | empty => simp [TensorRSSpace.toModel_zero]
    | insert i₀ s'' hi₀ ih =>
        rw [Finset.sum_insert hi₀, TensorRSSpace.toModel_add, ih, Finset.sum_insert hi₀]
  rw [show (GcurvSection (I := I) (M := M) g s S).toFun x =
        TensorRSSpace.toModel ((GcurvSection (I := I) (M := M) g s S).toSection x) from
      SmoothCcTensor.toFun_apply (GcurvSection (I := I) (M := M) g s S) x,
    ← remDiffGenuineFib_sum_eq_GcurvSection_toSection (I := I) (M := M) g s S x, htoM]
  rw [show (∑ i : Fin (Module.finrank ℝ E),
        TensorRSSpace.toModel (remDiffGenuineFib (I := I) (M := M) g s S x i)) =
      ∑ i : Fin (Module.finrank ℝ E), (1 : ℝ) •
        TensorRSSpace.toModel (remDiffGenuineFib (I := I) (M := M) g s S x i) from by
    refine Finset.sum_congr rfl (fun i _ => ?_); rw [one_smul]]
  rw [tensorInnerPointwise_sum_left (I := I) (M := M) g 0 (s + 1) x Finset.univ]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [one_mul]

/-- **The pure-Riemann genuine frame-sum pairing equals the concrete pure-Riemann section value (posit,
per-family integrated identity).** For a closed smooth Riemannian manifold `(M, g)`, covariant rank
`s`, and smooth compactly-supported `(0, s)`-tensor `S`, the integral over the closed manifold of the
fixed-frame sum of the per-direction pure-Riemann genuine curvature fibres `remDiffGenuineFib`, paired
against `∇S := covGrad g 0 s S`, equals the global metric `L²` pairing of the concrete pure-Riemann
genuine curvature section `GcurvSection g s S` against `∇S`:
```
∫_M ∑ᵢ ⟨remDiffGenuineFib g s S x i, ∇S(x)⟩ dvol_g = ⟨GcurvSection g s S, ∇S⟩_{L²}.
```

This is the **pure-Riemann genuine-sum identification** (per-family integrated identity). The genuine
per-direction fibres carry the pure-Riemann `R(Bᵢ, ·)(∇_{Bᵢ} S)` contraction; their frame sum is the
concrete pure-Riemann genuine trace section `GcurvSection g s S` (frame-free, tensorial —
`pureRGenuineDiffOp0_eq_GcurvSection`, `GcurvSection_toSection_eq_genuineThirdCurvFieldFibPureR`), so
their frame-sum pairing against `∇S`, integrated over the closed manifold, is `⟨GcurvSection g s S,
∇S⟩_{L²}`. The pure-Riemann trace is genuinely tensorial in the direction (linear in `v` through
`riemannOp`), so this is a *sound pointwise* frame-sum identity — no `smoothExtensionTangent` obstruction.
The integrability conjunct is the genuine analytic content that the pure-Riemann genuine frame-sum
integrand is Bochner-integrable against the Riemannian volume measure (the pure-Riemann trace is the
smooth section `GcurvSection g s S`). It is the per-family integrated identity between named on-disk
objects, strictly below the integrated curvature value `(★)`. -/
theorem remDiffFib_genuineFrameSum_pairing_eq_genuineFields
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) :
    MeasureTheory.Integrable
        (fun x => ∑ i : Fin (Module.finrank ℝ E),
            tensorInnerPointwise (I := I) (M := M) g 0 (s + 1) x
              (TensorRSSpace.toModel (remDiffGenuineFib (I := I) (M := M) g s S x i))
              ((covGrad (I := I) (M := M) g 0 s S).toFun x))
        (riemannianVolumeMeasure (I := I) (M := M) g) ∧
      (∫ x, (∑ i : Fin (Module.finrank ℝ E),
            tensorInnerPointwise (I := I) (M := M) g 0 (s + 1) x
              (TensorRSSpace.toModel (remDiffGenuineFib (I := I) (M := M) g s S x i))
              ((covGrad (I := I) (M := M) g 0 s S).toFun x))
        ∂(riemannianVolumeMeasure (I := I) (M := M) g)) =
      tensorL2Inner (I := I) (M := M) g 0 (s + 1)
        (GcurvSection (I := I) (M := M) g s S).toFun
        (covGrad (I := I) (M := M) g 0 s S).toFun := by
  classical
  have hpoint : (fun x => ∑ i : Fin (Module.finrank ℝ E),
        tensorInnerPointwise (I := I) (M := M) g 0 (s + 1) x
          (TensorRSSpace.toModel (remDiffGenuineFib (I := I) (M := M) g s S x i))
          ((covGrad (I := I) (M := M) g 0 s S).toFun x)) =
      (fun x => tensorInnerPointwise (I := I) (M := M) g 0 (s + 1) x
          ((GcurvSection (I := I) (M := M) g s S).toFun x)
          ((covGrad (I := I) (M := M) g 0 s S).toFun x)) := by
    funext x
    exact genuineFrameSum_pairing_pointwise_eq_GcurvSection (I := I) (M := M) g s S x
  have hint : MeasureTheory.Integrable
      (fun x => tensorInnerPointwise (I := I) (M := M) g 0 (s + 1) x
          ((GcurvSection (I := I) (M := M) g s S).toFun x)
          ((covGrad (I := I) (M := M) g 0 s S).toFun x))
      (riemannianVolumeMeasure (I := I) (M := M) g) :=
    DifferentialGeometry.Integral.L2.SmoothCcTensor.integrable_inner_cross (I := I) (M := M)
      (GcurvSection (I := I) (M := M) g s S) (covGrad (I := I) (M := M) g 0 s S)
  refine ⟨hpoint ▸ hint, ?_⟩
  rw [tensorL2Inner]
  exact hpoint ▸ rfl

/-- **The pure-Riemann peel of the bracket-channel integrand (sorry-free, structural).** For a closed
smooth Riemannian manifold `(M, g)`, covariant rank `s`, smooth compactly-supported `(0, s)`-tensor `S`,
and point `x`, the fixed-frame sum of the per-direction frame-bracket remainder fibres `remDiffBracketFib`
(`remDiffFib − remDiffGenuineFib`), paired against `∇S := covGrad g 0 s S`, is the pointwise metric inner
product of the concrete moving-frame remainder `pointwiseTensorCurv g s S − GcurvSection g s S` against
`∇S`:
```
∑ᵢ ⟨remDiffBracketFib g s S x i, ∇S(x)⟩ = ⟨(Curv S − Gcurv)(x), ∇S(x)⟩.
```

This is the purely structural integrand reading, sorry-free: the bracket fibre frame-sum is the moving-frame
remainder section value (the frame summand frame-sum is `pointwiseTensorCurv` by
`pointwiseTensorCurv_toSection_eq_frame_sum`, the genuine fibre frame-sum is `GcurvSection` by
`remDiffGenuineFib_sum_eq_GcurvSection_toSection`, and the bracket fibre is their difference), then the
pointwise metric inner product distributes over the frame sum (`tensorInnerPointwise_sum_left`, weights
`1`). No moving-frame derivative and no curvature input survives — it lives upstream so the bracket-channel
assembly imports it directly (it was previously trapped as a `private` reproduction downstream). -/
theorem frameSumBracketFib_pairing_pointwise_eq_movingFrameRemainder
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) (x : M) :
    (∑ i : Fin (Module.finrank ℝ E),
        tensorInnerPointwise (I := I) (M := M) g 0 (s + 1) x
          (TensorRSSpace.toModel (remDiffBracketFib (I := I) (M := M) g s S x i))
          ((covGrad (I := I) (M := M) g 0 s S).toFun x)) =
      tensorInnerPointwise (I := I) (M := M) g 0 (s + 1) x
        ((pointwiseTensorCurv (I := I) (M := M) g s S -
          GcurvSection (I := I) (M := M) g s S).toFun x)
        ((covGrad (I := I) (M := M) g 0 s S).toFun x) := by
  classical
  have hfib : (∑ i : Fin (Module.finrank ℝ E), remDiffBracketFib (I := I) (M := M) g s S x i) =
      (pointwiseTensorCurv (I := I) (M := M) g s S -
        GcurvSection (I := I) (M := M) g s S).toSection x := by
    have hbr : ∀ i, remDiffBracketFib (I := I) (M := M) g s S x i =
        remDiffFib (I := I) (M := M) g s S x i -
          remDiffGenuineFib (I := I) (M := M) g s S x i := fun _ => rfl
    rw [Finset.sum_congr rfl (fun i _ => hbr i), Finset.sum_sub_distrib]
    rw [remDiffGenuineFib_sum_eq_GcurvSection_toSection (I := I) (M := M) g s S x]
    rw [SmoothCcTensor.toSection_sub]
    congr 1
    rw [pointwiseTensorCurv_toSection_eq_frame_sum (I := I) (M := M) g s S x]
    rfl
  have htoM : TensorRSSpace.toModel
        (∑ i : Fin (Module.finrank ℝ E), remDiffBracketFib (I := I) (M := M) g s S x i) =
      ∑ i : Fin (Module.finrank ℝ E),
        TensorRSSpace.toModel (remDiffBracketFib (I := I) (M := M) g s S x i) := by
    induction (Finset.univ : Finset (Fin (Module.finrank ℝ E))) using Finset.induction with
    | empty => simp [TensorRSSpace.toModel_zero]
    | insert i₀ s'' hi₀ ih =>
        rw [Finset.sum_insert hi₀, TensorRSSpace.toModel_add, ih, Finset.sum_insert hi₀]
  rw [show (pointwiseTensorCurv (I := I) (M := M) g s S -
        GcurvSection (I := I) (M := M) g s S).toFun x =
      TensorRSSpace.toModel ((pointwiseTensorCurv (I := I) (M := M) g s S -
        GcurvSection (I := I) (M := M) g s S).toSection x) from rfl]
  rw [← hfib, htoM]
  rw [show (∑ i : Fin (Module.finrank ℝ E),
        TensorRSSpace.toModel (remDiffBracketFib (I := I) (M := M) g s S x i)) =
      ∑ i : Fin (Module.finrank ℝ E), (1 : ℝ) •
        TensorRSSpace.toModel (remDiffBracketFib (I := I) (M := M) g s S x i) from by
    refine Finset.sum_congr rfl (fun i _ => ?_); rw [one_smul]]
  rw [tensorInnerPointwise_sum_left (I := I) (M := M) g 0 (s + 1) x Finset.univ]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [one_mul]

/-- **The bracket-channel frame-sum integral as the Weitzenböck energy minus the pure-Riemann gradient
bilinear (sorry-free, the upstream Bochner reduction).** For a closed smooth Riemannian manifold `(M, g)`,
covariant rank `s`, and smooth compactly-supported `(0, s)`-tensor `S`, the integral over the closed
manifold of the fixed-frame sum of the per-direction frame-bracket remainder fibres `remDiffBracketFib`,
paired against `∇S := covGrad g 0 s S`, equals the genuine Weitzenböck curvature integral minus the
gradient-field pure-Riemann curvature bilinear:
```
∫_M ∑ᵢ ⟨remDiffBracketFib g s S x i, ∇S(x)⟩ dvol_g
  = (‖Δ_∇ S‖²_{L²} − ‖∇²S‖²_{L²}) − ⟨pureRGenuineDiffOp g 0 (s + 1) (∇S), ∇S⟩_{L²},
```
with `Δ_∇ S := rawTensorConnLapSmooth g 0 s S` and `∇²S := covGrad g 0 (s + 1) (covGrad g 0 s S)`.

This is the sorry-free *upstream* Bochner reduction of the bracket-channel integral: the integrand pure-`R`
peel `frameSumBracketFib_pairing_pointwise_eq_movingFrameRemainder` reads the integral as the moving-frame
remainder cross-pairing `⟨Curv S − GcurvSection g s S, ∇S⟩_{L²}`; splitting by left additivity
(`tensorL2Inner_add_left`, the cross-integrabilities `integrable_inner_cross`) gives `⟨Curv S, ∇S⟩_{L²} −
⟨GcurvSection g s S, ∇S⟩_{L²}`; the defect cross-pairing is the integrated order-`2` Weitzenböck value
`‖Δ_∇ S‖²_{L²} − ‖∇²S‖²_{L²}` (`weitzenbock_curvature_crossPairing_value`) and the pure-Riemann pairing is
the gradient-field bilinear `⟨pureRGenuineDiffOp g 0 (s + 1) (∇S), ∇S⟩_{L²}`
(`tensorL2Inner_GcurvSection_covGrad_eq_pureRGenuineDiffOp`).

It isolates the entire genuine integrated curvature content of the bracket channel into the single
frame-free cross-pairing *value* `⟨pureRGenuineDiffOp g 0 (s + 1) (∇S), ∇S⟩_{L²} + ⟨(∇R) S +
ricTraceSection g s S, ∇S⟩_{L²} = ‖Δ_∇ S‖²_{L²} − ‖∇²S‖²_{L²}` (the classical tensor Bochner–Weitzenböck
curvature-term identity), strictly below which sit the differentiated-curvature operator-field
identification, the second-Bianchi Ricci fold, and the bracket-discrepancy divergence nullity. -/
theorem bracketChannelRemainder_integral_eq_weitzenbock_sub_pureRBilin
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) :
    (∫ x, (∑ i : Fin (Module.finrank ℝ E),
            tensorInnerPointwise (I := I) (M := M) g 0 (s + 1) x
              (TensorRSSpace.toModel (remDiffBracketFib (I := I) (M := M) g s S x i))
              ((covGrad (I := I) (M := M) g 0 s S).toFun x))
        ∂(riemannianVolumeMeasure (I := I) (M := M) g)) =
      (tensorL2Norm (I := I) (M := M) g 0 s
            (rawTensorConnLapSmooth (I := I) g 0 s S).toFun ^ 2 -
          tensorL2Norm (I := I) (M := M) g 0 (s + 1 + 1)
            (covGrad (I := I) (M := M) g 0 (s + 1)
              (covGrad (I := I) (M := M) g 0 s S)).toFun ^ 2) -
        tensorL2Inner (I := I) (M := M) g 0 (s + 1)
          (pureRGenuineDiffOp (I := I) (M := M) g 0 (s + 1)
            (covGrad (I := I) (M := M) g 0 s S)).toFun
          (covGrad (I := I) (M := M) g 0 s S).toFun := by
  classical
  -- Step 1 (pure-`R` peel, integrated). The bracket frame-sum integral is the moving-frame remainder
  -- cross-pairing `⟨Curv S − GcurvSection, ∇S⟩_{L²}`.
  have hLHS : (∫ x, (∑ i : Fin (Module.finrank ℝ E),
            tensorInnerPointwise (I := I) (M := M) g 0 (s + 1) x
              (TensorRSSpace.toModel (remDiffBracketFib (I := I) (M := M) g s S x i))
              ((covGrad (I := I) (M := M) g 0 s S).toFun x))
        ∂(riemannianVolumeMeasure (I := I) (M := M) g)) =
      tensorL2Inner (I := I) (M := M) g 0 (s + 1)
        (pointwiseTensorCurv (I := I) (M := M) g s S -
          GcurvSection (I := I) (M := M) g s S).toFun
        (covGrad (I := I) (M := M) g 0 s S).toFun := by
    rw [tensorL2Inner]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    exact frameSumBracketFib_pairing_pointwise_eq_movingFrameRemainder (I := I) (M := M) g s S x
  rw [hLHS]
  -- Step 2 (split the cross-pairing by left additivity): `⟨Curv − Gcurv, ∇S⟩ = ⟨Curv, ∇S⟩ − ⟨Gcurv, ∇S⟩`.
  have hintC := DifferentialGeometry.Integral.L2.SmoothCcTensor.integrable_inner_cross
    (I := I) (M := M)
    (pointwiseTensorCurv (I := I) (M := M) g s S - GcurvSection (I := I) (M := M) g s S)
    (covGrad (I := I) (M := M) g 0 s S)
  have hintGc := DifferentialGeometry.Integral.L2.SmoothCcTensor.integrable_inner_cross
    (I := I) (M := M)
    (GcurvSection (I := I) (M := M) g s S) (covGrad (I := I) (M := M) g 0 s S)
  have hLsplit : tensorL2Inner (I := I) (M := M) g 0 (s + 1)
        (pointwiseTensorCurv (I := I) (M := M) g s S -
          GcurvSection (I := I) (M := M) g s S).toFun
        (covGrad (I := I) (M := M) g 0 s S).toFun =
      tensorL2Inner (I := I) (M := M) g 0 (s + 1)
        (pointwiseTensorCurv (I := I) (M := M) g s S).toFun
        (covGrad (I := I) (M := M) g 0 s S).toFun -
      tensorL2Inner (I := I) (M := M) g 0 (s + 1)
        (GcurvSection (I := I) (M := M) g s S).toFun
        (covGrad (I := I) (M := M) g 0 s S).toFun := by
    have heq : pointwiseTensorCurv (I := I) (M := M) g s S =
        (pointwiseTensorCurv (I := I) (M := M) g s S - GcurvSection (I := I) (M := M) g s S) +
          GcurvSection (I := I) (M := M) g s S := by abel
    have hsum :
        tensorL2Inner (I := I) (M := M) g 0 (s + 1)
            (pointwiseTensorCurv (I := I) (M := M) g s S).toFun
            (covGrad (I := I) (M := M) g 0 s S).toFun =
          tensorL2Inner (I := I) (M := M) g 0 (s + 1)
            (pointwiseTensorCurv (I := I) (M := M) g s S -
              GcurvSection (I := I) (M := M) g s S).toFun
            (covGrad (I := I) (M := M) g 0 s S).toFun +
            tensorL2Inner (I := I) (M := M) g 0 (s + 1)
              (GcurvSection (I := I) (M := M) g s S).toFun
              (covGrad (I := I) (M := M) g 0 s S).toFun := by
      nth_rewrite 1 [heq]
      rw [SmoothCcTensor.toFun_add,
        tensorL2Inner_add_left (I := I) (M := M) g 0 (s + 1)
          (pointwiseTensorCurv (I := I) (M := M) g s S -
            GcurvSection (I := I) (M := M) g s S).toFun
          (GcurvSection (I := I) (M := M) g s S).toFun
          (covGrad (I := I) (M := M) g 0 s S).toFun hintC hintGc]
    linarith [hsum]
  rw [hLsplit]
  -- Step 3 (the Weitzenböck value of the defect cross-pairing).
  rw [weitzenbock_curvature_crossPairing_value (I := I) (M := M) g s S]
  -- Step 4 (the pure-Riemann pairing is the gradient-field pure-`R` bilinear).
  rw [tensorL2Inner_GcurvSection_covGrad_eq_pureRGenuineDiffOp (I := I) (M := M) g s S]

/-- **The frame-free integrated tensor Bochner–Weitzenböck three-section curvature value (the rank-`0`
curvature line's single genuine-math posit, in pure-`R` operator-field form).** For a closed smooth
Riemannian manifold `(M, g)`, every covariant rank `s`, and every smooth compactly-supported
`(0, s)`-tensor `S`, the global metric `L²` pairing of the three concrete frame-free operator-field
curvature carriers — the gradient-field pure-Riemann trace `pureRGenuineDiffOp g 0 (s + 1) (∇S)`
(`= GcurvSection g s S` by `tensorL2Inner_GcurvSection_covGrad_eq_pureRGenuineDiffOp`), the
differentiated-curvature `(∇R) S` operator-field trace `appCc (covGrad g s s (Φ₀ s)) S`
(`Φ₀ s := curvOpField g s`, definitionally `genuineDiffCurvSection g s S`), and the leading-slot
Ricci trace `ricTraceSection g s S` — against `∇S := covGrad g 0 s S` equals the genuine Weitzenböck
curvature integral `‖Δ_∇ S‖²_{L²} − ‖∇²S‖²_{L²}`:
```
⟨pureRGenuineDiffOp g 0 (s + 1) (∇S) + appCc (covGrad g s s (Φ₀ s)) S + ricTraceSection g s S, ∇S⟩_{L²}
  = ‖Δ_∇ S‖²_{L²} − ‖∇²S‖²_{L²},
```
with `Δ_∇ S := rawTensorConnLapSmooth g 0 s S` and `∇²S := covGrad g 0 (s + 1) (covGrad g 0 s S)`.

**This is the genuine new mathematical content of the entire rank-`0` curvature line — the classical
tensor Bochner–Weitzenböck curvature-term identity, in its cleanest fully-tensorial frame-free
operator-field value form** (no moving frame, no `remDiffBracketFib`, no `smoothExtensionTangent`
ext-jet). By the iterated Ricci identity the order-`2` rough-Laplacian / covariant-gradient commutator
defect's gradient-slot reordering produces (I) the pure-Riemann `R(∇S)` trace, (II) the differentiated
curvature `(∇R) S`, and (III) the leading-slot Ricci trace, plus a residual `∇²S`-order frame-bracket
discrepancy (`tensor3rdCurvBracket`) that is a total covariant divergence integrating to zero over the
closed manifold.

**Why the integrated value, not the pointwise per-direction match.** The differentiated-curvature trace
`∑ᵢ ∇_{Bᵢ}(R(Bᵢ, ·) S)` is **non-tensorial in the direction** — its per-direction fibre realisation reads
the `smoothExtensionTangent` jet of the frame direction, which is chart-selection-unbounded on `S²` (T1) —
so the `∇³S`-cancellation and divergence form are *false term-by-term*. Only the *summed, integrated*
match is sound, and that sound integrated content is exactly this value identity. The identity is stated
at the *integrated* frame-free `L²` level throughout — it never extracts a per-direction `M → E`
quantity — so it is trap-screened.

**Non-vacuity (the `s = 0` litmus rejects the degenerate carrier).** At `s = 0` the pure-Riemann and
differentiated-curvature carriers vanish (`pureRGenuineDiffOp g 0 1 (∇f)` reads the curvature trace of a
scalar gradient through `GcurvSection g 0 f`, which vanishes; `appCc (covGrad g 0 0 (Φ₀ 0)) f` acts as the
zero operator on the empty curvature slot), so the value collapses to
`⟨ricTraceSection g 0 f, ∇f⟩_{L²} = ‖Δ_∇ f‖²_{L²} − ‖∇²f‖²_{L²} = ∫ Ric(∇f, ∇f)` — the classical scalar
Bochner–Lichnerowicz identity, genuinely nonzero on a non-flat manifold. Dropping the Ricci-trace carrier
(perturbing the curvature to flat, the degenerate witness) makes the value FALSE at `s = 0`, so the
carrier is genuinely required and the identity is not vacuous.

This is the single irreducible analytic posit of the curvature line; it is disclosed as a `sorry`, and
consumers (`tensorL2Inner_curv_covGrad_eq_genuineThreeSection_value` and the operator-field atom that cites
it) transitively depend on its `sorryAx`. -/
theorem bochnerWeitzenbock_threeSection_curvatureValue_posit
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) :
    tensorL2Inner (I := I) (M := M) g 0 (s + 1)
        (pureRGenuineDiffOp (I := I) (M := M) g 0 (s + 1)
            (covGrad (I := I) (M := M) g 0 s S) +
          (appCc (I := I) (M := M) g s (s + 1)
              (covGrad (I := I) (M := M) g s s (curvOpField (I := I) (M := M) g s)) S +
            ricTraceSection (I := I) (M := M) g s S)).toFun
        (covGrad (I := I) (M := M) g 0 s S).toFun =
      tensorL2Norm (I := I) (M := M) g 0 s
          (rawTensorConnLapSmooth (I := I) g 0 s S).toFun ^ 2 -
        tensorL2Norm (I := I) (M := M) g 0 (s + 1 + 1)
          (covGrad (I := I) (M := M) g 0 (s + 1)
            (covGrad (I := I) (M := M) g 0 s S)).toFun ^ 2 :=
  sorry

/-- **The integrated tensor Bochner–Weitzenböck three-section value, in the curvature cross-pairing
form (sorry-free over the single posit).** For a closed smooth Riemannian manifold `(M, g)`, covariant
rank `s`, and smooth compactly-supported `(0, s)`-tensor `S`, the global metric `L²` pairing of the
order-`2` commutator defect `Curv S := pointwiseTensorCurv g s S` against `∇S := covGrad g 0 s S` splits
into the pure-Riemann `R(∇S)` trace, the differentiated-curvature `(∇R) S` operator-field trace, and the
leading-slot Ricci trace:
```
⟨Curv S, ∇S⟩_{L²}
  = ⟨GcurvSection g s S, ∇S⟩_{L²}
    + ⟨appCc (covGrad g s s (Φ₀ s)) S, ∇S⟩_{L²}
    + ⟨ricTraceSection g s S, ∇S⟩_{L²},   Φ₀ s := curvOpField g s.
```

This is the rank-`0` curvature line's deep cross-pairing value in the exact three-term shape the
operator-field atom consumes. **Assembly (sorry-free over the single posit
`bochnerWeitzenbock_threeSection_curvatureValue_posit`).** The Weitzenböck value
`weitzenbock_curvature_crossPairing_value` (sorry-free) reads `⟨Curv S, ∇S⟩_{L²} = ‖Δ_∇ S‖²_{L²} −
‖∇²S‖²_{L²}`; the posit reads the three-carrier sum-pairing as the same Weitzenböck value; left additivity
of the `L²` pairing `tensorL2Inner_add_left` (with the cross-integrabilities
`SmoothCcTensor.integrable_inner_cross`) expands the posited sum into the three summand pairings; and the
gradient-field pure-Riemann identification `tensorL2Inner_GcurvSection_covGrad_eq_pureRGenuineDiffOp`
(sorry-free) rewrites the pure-Riemann summand `⟨pureRGenuineDiffOp g 0 (s + 1) (∇S), ∇S⟩` as the genuine
`⟨GcurvSection g s S, ∇S⟩`. Consumers transitively depend on the posit's `sorryAx`. -/
theorem tensorL2Inner_curv_covGrad_eq_genuineThreeSection_value
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) :
    tensorL2Inner (I := I) (M := M) g 0 (s + 1)
        (pointwiseTensorCurv (I := I) (M := M) g s S).toFun
        (covGrad (I := I) (M := M) g 0 s S).toFun =
      tensorL2Inner (I := I) (M := M) g 0 (s + 1)
          (GcurvSection (I := I) (M := M) g s S).toFun
          (covGrad (I := I) (M := M) g 0 s S).toFun +
        tensorL2Inner (I := I) (M := M) g 0 (s + 1)
          (appCc (I := I) (M := M) g s (s + 1)
            (covGrad (I := I) (M := M) g s s (curvOpField (I := I) (M := M) g s)) S).toFun
          (covGrad (I := I) (M := M) g 0 s S).toFun +
        tensorL2Inner (I := I) (M := M) g 0 (s + 1)
          (ricTraceSection (I := I) (M := M) g s S).toFun
          (covGrad (I := I) (M := M) g 0 s S).toFun := by
  classical
  -- The Weitzenböck value of the curvature cross-pairing (sorry-free).
  have hW := weitzenbock_curvature_crossPairing_value (I := I) (M := M) g s S
  -- The single posited three-section value.
  have hposit := bochnerWeitzenbock_threeSection_curvatureValue_posit (I := I) (M := M) g s S
  -- Expand the posited sum-pairing by left additivity of the `L²` pairing.
  have hadd1 := tensorL2Inner_add_left (I := I) (M := M) g 0 (s + 1)
      (pureRGenuineDiffOp (I := I) (M := M) g 0 (s + 1)
        (covGrad (I := I) (M := M) g 0 s S)).toFun
      (appCc (I := I) (M := M) g s (s + 1)
          (covGrad (I := I) (M := M) g s s (curvOpField (I := I) (M := M) g s)) S +
        ricTraceSection (I := I) (M := M) g s S).toFun
      (covGrad (I := I) (M := M) g 0 s S).toFun
      (SmoothCcTensor.integrable_inner_cross (I := I) (M := M)
        (pureRGenuineDiffOp (I := I) (M := M) g 0 (s + 1)
          (covGrad (I := I) (M := M) g 0 s S)) (covGrad (I := I) (M := M) g 0 s S))
      (SmoothCcTensor.integrable_inner_cross (I := I) (M := M)
        (appCc (I := I) (M := M) g s (s + 1)
            (covGrad (I := I) (M := M) g s s (curvOpField (I := I) (M := M) g s)) S +
          ricTraceSection (I := I) (M := M) g s S) (covGrad (I := I) (M := M) g 0 s S))
  have hadd2 := tensorL2Inner_add_left (I := I) (M := M) g 0 (s + 1)
      (appCc (I := I) (M := M) g s (s + 1)
        (covGrad (I := I) (M := M) g s s (curvOpField (I := I) (M := M) g s)) S).toFun
      (ricTraceSection (I := I) (M := M) g s S).toFun
      (covGrad (I := I) (M := M) g 0 s S).toFun
      (SmoothCcTensor.integrable_inner_cross (I := I) (M := M)
        (appCc (I := I) (M := M) g s (s + 1)
          (covGrad (I := I) (M := M) g s s (curvOpField (I := I) (M := M) g s)) S)
        (covGrad (I := I) (M := M) g 0 s S))
      (SmoothCcTensor.integrable_inner_cross (I := I) (M := M)
        (ricTraceSection (I := I) (M := M) g s S) (covGrad (I := I) (M := M) g 0 s S))
  rw [SmoothCcTensor.toFun_add, hadd1, SmoothCcTensor.toFun_add, hadd2] at hposit
  -- Identify the pure-Riemann gradient-field pairing with the genuine `⟨GcurvSection, ∇S⟩` pairing.
  rw [tensorL2Inner_GcurvSection_covGrad_eq_pureRGenuineDiffOp (I := I) (M := M) g s S]
  linarith [hW, hposit]

end Connection
end Integral
end DifferentialGeometry

end
