import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.MovingFrameCurvatureTraceSmooth
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
  sorry

end Connection
end Integral
end DifferentialGeometry

end
