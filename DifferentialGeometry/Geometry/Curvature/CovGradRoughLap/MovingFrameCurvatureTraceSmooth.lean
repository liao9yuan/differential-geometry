import DifferentialGeometry.Geometry.Curvature.Bochner.PointwiseTensorBochnerFieldSplit
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.GenuineCurvatureField
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.UniformCurvatureSup
import DifferentialGeometry.Geometry.Curvature.FiberNormParseval.Slot0CurryReconstruction

/-!
# Smoothness of the moving-frame genuine third-order curvature trace

For a closed (compact, boundaryless) smooth Riemannian manifold `(M, g)` modelled on a real
inner-product space `E`, this file packages the two *genuine* curvature contributions of the
order-`2` rough-Laplacian / covariant-gradient commutator defect — the pure-Riemann contraction
`R(B_i, W)(∇_{B_i} S)` and the differentiated-curvature contraction `∇_{B_i}(R(B_i, W) S)`, summed
over a smooth tangent frame `B` — as honest smooth (and, on a closed manifold, compactly-supported)
`(0, s)`-tensor sections.

The genuine directional curvature field `tensor3rdCurvGenuine g 0 s W S` (`PointwiseTensorBochner`)
is built against the *moving* `g_x`-orthonormal frame `B_i := smoothOrthoFrame g x i` (centre = the
evaluation point), exactly as `rawTensorConnLap` is. Its base-point smoothness is therefore proved by
the same frame-freezing template that makes `rawTensorConnLap` smooth
(`rawTensorConnLap_contMDiff`): on the open neighbourhood `smoothOrthoFrameNbhd x₀` the moving frame
agrees with the frozen frame `smoothOrthoFrame g x₀`, the trace against any *fixed* smooth frame `B`
is smooth summand-by-summand (`riemannSec_contMDiff`, `covApplyRS_contMDiff`, `smoothOrthoFrame_smooth`),
and the genuine curvature trace — a genuine metric trace, with the frame index contracted twice — is
frame-independent among `g_x`-orthonormal frames, so the moving trace equals the frozen trace on the
neighbourhood and inherits its smoothness by `ContMDiffAt.congr_of_eventuallyEq`.

## Main definitions

* `genuineCurvTraceFixedFramePureR g s W B S y` — for a *fixed* smooth tangent frame `B` and a fixed
  smooth tangent field `W`, the frame sum at `y` of the pure-Riemann curvature contraction
  `R(B_i, W)(∇_{B_i} S)`, a `(0, s)`-tensor.
* `genuineCurvTraceFixedFrameCovDeriv g s W B S y` — likewise the frame sum of the
  differentiated-curvature contraction `∇_{B_i}(R(B_i, W) S)`.
* `genuineThirdCurvFieldFibPureR` / `genuineThirdCurvFieldFibCovDeriv` — the pure-Riemann /
  differentiated-curvature parts of the genuine third-order curvature fibre field
  `genuineThirdCurvFieldFib` (`PointwiseTensorBochnerFieldSplit`), as inner-product-weighted slot-`0`
  frame reconstructions of the two fixed-frame genuine traces against the moving frame.
* `GcurvSection g s S` / `GcurvDerivSection g s S : SmoothCcTensor g 0 (s + 1)` — the moving-centre
  smooth genuine curvature sections (the slot-`0` assembly of the moving-frame genuine traces), the
  pure-Riemann `R(∇S)` and differentiated-curvature `(∇R) S` packagings consumed by the leaf-`A`
  genuine-field decomposition.

## Main results

* `genuineCurvTraceFixedFramePureR_contMDiff` / `genuineCurvTraceFixedFrameCovDeriv_contMDiff` — each
  fixed-frame genuine curvature trace is a smooth `(0, s)`-tensor section, for smooth `B`, `W`, `S`.
* `genuineThirdCurvFieldFib_eq_pureR_add_covDeriv` — the genuine fibre field splits into its
  pure-Riemann and differentiated-curvature parts.
* `GcurvSection_toSection_eq_genuineThirdCurvFieldFibPureR` /
  `GcurvDerivSection_toSection_eq_genuineThirdCurvFieldFibCovDeriv` /
  `GcurvSection_add_GcurvDerivSection_toSection_eq_genuineThirdCurvField` — the fibre values of the two
  sections (and their sum) match the pure-Riemann / differentiated-curvature parts (and the whole) of
  the genuine third-order curvature field of the committed field split
  `pointwiseTensorCurv_toSection_eq_genuine_add_bracket_field`.

## A posited deep node

The slot-`0` assembly of the moving-frame genuine curvature traces into the `(0, s + 1)`-tensor
sections `GcurvSection` / `GcurvDerivSection`, together with their base-point smoothness, is posited as
the single precise true node `exists_GcurvSection_GcurvDerivSection`. Its discharge requires the
slot-`0`-uncurry continuous-linear-map assembly (`(tensor0S_curry s x).symm` of the direction-linear
genuine trace), the frame-independence of the genuine metric trace among `g_x`-orthonormal frames (the
bilinear Parseval argument, the curvature analogue of `rawTensorConnLap_eq_fixedFrame_of_orthonormal`),
and the resulting bundle-section smoothness; the fixed-frame trace smoothness it is built from is
proved here in full. Its docstring records the full truth justification and non-vacuity.

## Convention

Geometer convention `Δ_∇ = ∑ᵢ ∇²_{Bᵢ, Bᵢ}` (frame trace). The pure-Riemann part is genuinely
`rfns(∇S)`-order; the differentiated-curvature part is genuinely `rfns(S)`-order. All fibre norms are
the intrinsic Riemannian fibre norm `riemannianFiberNormSq`.
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

/-- **The fixed-frame pure-Riemann genuine curvature trace.** For a fixed smooth tangent frame `B`
and a fixed smooth tangent field `W`, the frame sum at `y` of the pure-Riemann curvature contraction
`R(B_i, W)(∇_{B_i} S)`:
```
∑ᵢ riemannSec (tensorCov g 0 s) (B i) W (∇_{B i} S) y,
```
a `(0, s)`-tensor (`∇_{B i} S := covApply (tensorCov g 0 s) (B i) S`). This is the first genuine
summand of `tensor3rdCurvGenuine`, with the moving frame `smoothOrthoFrame g x i` replaced by the
general fixed frame `B`. It is genuinely `rfns(∇S)`-order. -/
noncomputable def genuineCurvTraceFixedFramePureR
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (W : Π b : M, TangentSpace I b)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b)
    (S : Π b : M, TensorRSSpace 0 s I b) (y : M) :
    TensorRSSpace 0 s I y :=
  ∑ i : Fin (Module.finrank ℝ E),
    riemannSec (tensorCov (I := I) g 0 s) (B i) W
      (covApply (tensorCov (I := I) g 0 s) (B i) S) y

/-- **The fixed-frame differentiated-curvature genuine trace.** For a fixed smooth tangent frame `B`
and a fixed smooth tangent field `W`, the frame sum at `y` of the differentiated-curvature
contraction `∇_{B_i}(R(B_i, W) S)`:
```
∑ᵢ (tensorCov g 0 s).toFun (fun b ↦ riemannSec (tensorCov g 0 s) (B i) W S b) y (B i y),
```
a `(0, s)`-tensor. This is the second genuine summand of `tensor3rdCurvGenuine`, with the moving
frame `smoothOrthoFrame g x i` replaced by the general fixed frame `B`. It is genuinely
`rfns(S)`-order (its Leibniz expansion carries the `∇R` contribution). -/
noncomputable def genuineCurvTraceFixedFrameCovDeriv
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (W : Π b : M, TangentSpace I b)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b)
    (S : Π b : M, TensorRSSpace 0 s I b) (y : M) :
    TensorRSSpace 0 s I y :=
  ∑ i : Fin (Module.finrank ℝ E),
    (tensorCov (I := I) g 0 s).toFun
      (fun b : M => riemannSec (tensorCov (I := I) g 0 s) (B i) W S b) y (B i y)

/-- The defining identity for `genuineCurvTraceFixedFramePureR`. -/
@[simp] lemma genuineCurvTraceFixedFramePureR_def
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (W : Π b : M, TangentSpace I b)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b)
    (S : Π b : M, TensorRSSpace 0 s I b) (y : M) :
    genuineCurvTraceFixedFramePureR (I := I) g s W B S y =
      ∑ i : Fin (Module.finrank ℝ E),
        riemannSec (tensorCov (I := I) g 0 s) (B i) W
          (covApply (tensorCov (I := I) g 0 s) (B i) S) y := rfl

/-- The defining identity for `genuineCurvTraceFixedFrameCovDeriv`. -/
@[simp] lemma genuineCurvTraceFixedFrameCovDeriv_def
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (W : Π b : M, TangentSpace I b)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b)
    (S : Π b : M, TensorRSSpace 0 s I b) (y : M) :
    genuineCurvTraceFixedFrameCovDeriv (I := I) g s W B S y =
      ∑ i : Fin (Module.finrank ℝ E),
        (tensorCov (I := I) g 0 s).toFun
          (fun b : M => riemannSec (tensorCov (I := I) g 0 s) (B i) W S b) y (B i y) := rfl

/-- **At the moving frame `B = smoothOrthoFrame g x`, the pure-Riemann fixed-frame trace is the
pure-Riemann part of `tensor3rdCurvGenuine`.** True by definition: both are the same finite sum. -/
lemma genuineCurvTraceFixedFramePureR_smoothOrthoFrame
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (W : Π b : M, TangentSpace I b)
    (S : Π b : M, TensorRSSpace 0 s I b) (x : M) :
    genuineCurvTraceFixedFramePureR (I := I) g s W (smoothOrthoFrame (I := I) g x) S x =
      ∑ i : Fin (Module.finrank ℝ E),
        riemannSec (tensorCov (I := I) g 0 s) (smoothOrthoFrame (I := I) g x i) W
          (covApply (tensorCov (I := I) g 0 s) (smoothOrthoFrame (I := I) g x i) S) x := rfl

/-- **At the moving frame `B = smoothOrthoFrame g x`, the differentiated-curvature fixed-frame
trace is the second part of `tensor3rdCurvGenuine`.** True by definition. -/
lemma genuineCurvTraceFixedFrameCovDeriv_smoothOrthoFrame
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (W : Π b : M, TangentSpace I b)
    (S : Π b : M, TensorRSSpace 0 s I b) (x : M) :
    genuineCurvTraceFixedFrameCovDeriv (I := I) g s W (smoothOrthoFrame (I := I) g x) S x =
      ∑ i : Fin (Module.finrank ℝ E),
        (tensorCov (I := I) g 0 s).toFun
          (fun b : M => riemannSec (tensorCov (I := I) g 0 s)
            (smoothOrthoFrame (I := I) g x i) W S b) x
          (smoothOrthoFrame (I := I) g x i x) := rfl

/-- **Per-summand smoothness of the pure-Riemann genuine curvature contraction (mk' form).** For a
smooth tangent field `B i`, a smooth tangent field `W` and a smooth `(0, s)`-tensor section `S`, the
section `b ↦ riemannSec (tensorCov g 0 s) (B i) W (∇_{B i} S) b` is smooth, in total-space `mk'`
form. The contracted tensor `∇_{B i} S := covApply (tensorCov g 0 s) (B i) S` is smooth by
`covApplyRS_contMDiff`, and the curvature section by `riemannSec_contMDiff`. -/
private lemma genuineCurvTraceFixedFramePureR_summand_contMDiff
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    {W : Π b : M, TangentSpace I b}
    {B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b}
    {S : Π b : M, TensorRSSpace 0 s I b}
    (hW : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% W))
    (hB : ∀ i, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (B i)))
    (hS_total : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 0 s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel 0 s ℝ E)
        (E := fun z : M => TensorRSSpace 0 s I z) y (S y)))
    (i : Fin (Module.finrank ℝ E)) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 0 s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel 0 s ℝ E)
        (E := fun z : M => TensorRSSpace 0 s I z) y
        (riemannSec (tensorCov (I := I) g 0 s) (B i) W
          (covApply (tensorCov (I := I) g 0 s) (B i) S) y)) := by
  classical
  have hcovBS : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 0 s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel 0 s ℝ E)
        (E := fun z : M => TensorRSSpace 0 s I z) y
        (covApply (tensorCov (I := I) g 0 s) (B i) S y)) :=
    covApplyRS_contMDiff (I := I) g 0 s hS_total (hB i)
  exact riemannSec_contMDiff (cov := tensorCov (I := I) g 0 s) (hB i) hW hcovBS

/-- **Smoothness of the fixed-frame pure-Riemann genuine curvature trace.** For a smooth tangent
frame `B`, a smooth tangent field `W` and a smooth `(0, s)`-tensor section `S`, the fixed-frame
pure-Riemann genuine curvature trace `genuineCurvTraceFixedFramePureR g s W B S` is a smooth
`(0, s)`-tensor section. The trace is a finite frame sum of per-summand curvature contractions, each
smooth by `genuineCurvTraceFixedFramePureR_summand_contMDiff`. -/
theorem genuineCurvTraceFixedFramePureR_contMDiff
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    {W : Π b : M, TangentSpace I b}
    {B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b}
    {S : Π b : M, TensorRSSpace 0 s I b}
    (hW : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% W))
    (hB : ∀ i, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (B i)))
    (hS_total : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 0 s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel 0 s ℝ E)
        (E := fun z : M => TensorRSSpace 0 s I z) y (S y))) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 0 s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel 0 s ℝ E)
        (E := fun z : M => TensorRSSpace 0 s I z) y
        (genuineCurvTraceFixedFramePureR (I := I) g s W B S y)) := by
  classical
  refine ContMDiff.sum_section (s := Finset.univ) (fun i _ => ?_)
  exact genuineCurvTraceFixedFramePureR_summand_contMDiff (I := I) g s hW hB hS_total i

/-- **Per-summand smoothness of the differentiated-curvature genuine contraction (mk' form).** For a
smooth tangent field `B i`, a smooth tangent field `W` and a smooth `(0, s)`-tensor section `S`, the
section `b ↦ ∇_{B i}(R(B i, W) S)(b) = covApply (tensorCov g 0 s) (B i) (fun b ↦ R(B i, W) S b) b` is
smooth, in total-space `mk'` form. The curvature section `b ↦ R(B i, W) S b` is smooth by
`riemannSec_contMDiff`, and its covariant derivative along `B i` by `covApplyRS_contMDiff`. -/
private lemma genuineCurvTraceFixedFrameCovDeriv_summand_contMDiff
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    {W : Π b : M, TangentSpace I b}
    {B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b}
    {S : Π b : M, TensorRSSpace 0 s I b}
    (hW : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% W))
    (hB : ∀ i, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (B i)))
    (hS_total : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 0 s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel 0 s ℝ E)
        (E := fun z : M => TensorRSSpace 0 s I z) y (S y)))
    (i : Fin (Module.finrank ℝ E)) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 0 s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel 0 s ℝ E)
        (E := fun z : M => TensorRSSpace 0 s I z) y
        ((tensorCov (I := I) g 0 s).toFun
          (fun b : M => riemannSec (tensorCov (I := I) g 0 s) (B i) W S b) y (B i y))) := by
  classical
  have hcurvSec : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 0 s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel 0 s ℝ E)
        (E := fun z : M => TensorRSSpace 0 s I z) y
        (riemannSec (tensorCov (I := I) g 0 s) (B i) W S y)) :=
    riemannSec_contMDiff (cov := tensorCov (I := I) g 0 s) (hB i) hW hS_total
  exact covApplyRS_contMDiff (I := I) g 0 s hcurvSec (hB i)

/-- **Smoothness of the fixed-frame differentiated-curvature genuine trace.** For a smooth tangent
frame `B`, a smooth tangent field `W` and a smooth `(0, s)`-tensor section `S`, the fixed-frame
differentiated-curvature genuine trace `genuineCurvTraceFixedFrameCovDeriv g s W B S` is a smooth
`(0, s)`-tensor section. The trace is a finite frame sum of per-summand covariant-differentiated
curvature contractions, each smooth by `genuineCurvTraceFixedFrameCovDeriv_summand_contMDiff`. -/
theorem genuineCurvTraceFixedFrameCovDeriv_contMDiff
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    {W : Π b : M, TangentSpace I b}
    {B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b}
    {S : Π b : M, TensorRSSpace 0 s I b}
    (hW : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% W))
    (hB : ∀ i, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (B i)))
    (hS_total : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 0 s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel 0 s ℝ E)
        (E := fun z : M => TensorRSSpace 0 s I z) y (S y))) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 0 s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel 0 s ℝ E)
        (E := fun z : M => TensorRSSpace 0 s I z) y
        (genuineCurvTraceFixedFrameCovDeriv (I := I) g s W B S y)) := by
  classical
  refine ContMDiff.sum_section (s := Finset.univ) (fun i _ => ?_)
  exact genuineCurvTraceFixedFrameCovDeriv_summand_contMDiff (I := I) g s hW hB hS_total i

/-- **The pure-Riemann part of the genuine third-order curvature fibre field.** For a `g_x`-
orthonormal frame `e`, the inner-product-weighted frame reconstruction of the *pure-Riemann*
summand of the genuine directional curvature piece `tensor3rdCurvGenuine`:
```
genuineThirdCurvFieldFibPureR g s S x e w m
  := ∑ₐ ⟨e a, w⟩_g • toModel
       (∑ᵢ riemannSec (tensorCov g 0 s) (smoothOrthoFrame g x i) (W a)
            (∇_{smoothOrthoFrame g x i} S) x) m,
```
with `W a := smoothExtensionTangent x (e a)`. The inner frame sum is
`genuineCurvTraceFixedFramePureR g s (W a) (smoothOrthoFrame g x) S x`. It carries the pure-Riemann
contraction `R(B_i, W a)(∇_{B_i} S)`, genuinely `rfns(∇S)`-order. -/
noncomputable def genuineThirdCurvFieldFibPureR
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) (x : M)
    {n : ℕ} (e : Fin n → TangentSpace I x) (w : TangentSpace I x)
    (m : Fin s → TangentSpace I x) : ℝ :=
  ∑ a : Fin n, g.inner x (e a) w •
    Tensor0SSpace.toModel
      ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
        genuineCurvTraceFixedFramePureR (I := I) g s (smoothExtensionTangent (I := I) x (e a))
          (smoothOrthoFrame (I := I) g x) (fun y : M => S.toSection y) x)
        (unitZeroSec (I := I) (M := M) x)) m

/-- **The differentiated-curvature part of the genuine third-order curvature fibre field.** For a
`g_x`-orthonormal frame `e`, the inner-product-weighted frame reconstruction of the
*differentiated-curvature* summand of `tensor3rdCurvGenuine`:
```
genuineThirdCurvFieldFibCovDeriv g s S x e w m
  := ∑ₐ ⟨e a, w⟩_g • toModel
       (∑ᵢ ∇_{smoothOrthoFrame g x i}(R(smoothOrthoFrame g x i, W a) S) x) m,
```
with `W a := smoothExtensionTangent x (e a)`. The inner frame sum is
`genuineCurvTraceFixedFrameCovDeriv g s (W a) (smoothOrthoFrame g x) S x`. It carries the
differentiated-curvature contraction `∇_{B_i}(R(B_i, W a) S)`, genuinely `rfns(S)`-order. -/
noncomputable def genuineThirdCurvFieldFibCovDeriv
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) (x : M)
    {n : ℕ} (e : Fin n → TangentSpace I x) (w : TangentSpace I x)
    (m : Fin s → TangentSpace I x) : ℝ :=
  ∑ a : Fin n, g.inner x (e a) w •
    Tensor0SSpace.toModel
      ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
        genuineCurvTraceFixedFrameCovDeriv (I := I) g s (smoothExtensionTangent (I := I) x (e a))
          (smoothOrthoFrame (I := I) g x) (fun y : M => S.toSection y) x)
        (unitZeroSec (I := I) (M := M) x)) m

/-- **The genuine curvature fibre field splits into its pure-Riemann and differentiated-curvature
parts.** For every `g_x`-orthonormal frame `e`, gradient direction `w` and tail tuple `m`,
```
genuineThirdCurvFieldFib g s S x e w m
  = genuineThirdCurvFieldFibPureR g s S x e w m + genuineThirdCurvFieldFibCovDeriv g s S x e w m.
```
This is the field-level reading of `tensor3rdCurvGenuine`'s definition as the sum of its
pure-Riemann summand `R(B_i, ·)(∇_{B_i} S)` and its differentiated-curvature summand
`∇_{B_i}(R(B_i, ·) S)` (`Finset.sum_add_distrib`, additivity of the model coercion, distribution of
the inner-product weight over the sum). -/
theorem genuineThirdCurvFieldFib_eq_pureR_add_covDeriv
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) (x : M)
    {n : ℕ} (e : Fin n → TangentSpace I x) (w : TangentSpace I x)
    (m : Fin s → TangentSpace I x) :
    genuineThirdCurvFieldFib (I := I) (M := M) g s S x e w m =
      genuineThirdCurvFieldFibPureR (I := I) (M := M) g s S x e w m +
        genuineThirdCurvFieldFibCovDeriv (I := I) (M := M) g s S x e w m := by
  classical
  rw [genuineThirdCurvFieldFib, genuineThirdCurvFieldFibPureR, genuineThirdCurvFieldFibCovDeriv,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  have hsplit_val :
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
        tensor3rdCurvGenuine (I := I) g 0 s (smoothExtensionTangent (I := I) x (e a))
          (fun y : M => S.toSection y) x)
        (unitZeroSec (I := I) (M := M) x) =
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
        genuineCurvTraceFixedFramePureR (I := I) g s (smoothExtensionTangent (I := I) x (e a))
          (smoothOrthoFrame (I := I) g x) (fun y : M => S.toSection y) x)
        (unitZeroSec (I := I) (M := M) x) +
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
        genuineCurvTraceFixedFrameCovDeriv (I := I) g s (smoothExtensionTangent (I := I) x (e a))
          (smoothOrthoFrame (I := I) g x) (fun y : M => S.toSection y) x)
        (unitZeroSec (I := I) (M := M) x) := by
    have hclm :
        (tensor3rdCurvGenuine (I := I) g 0 s (smoothExtensionTangent (I := I) x (e a))
          (fun y : M => S.toSection y) x : TensorRSSpace 0 s I x) =
        genuineCurvTraceFixedFramePureR (I := I) g s (smoothExtensionTangent (I := I) x (e a))
            (smoothOrthoFrame (I := I) g x) (fun y : M => S.toSection y) x +
          genuineCurvTraceFixedFrameCovDeriv (I := I) g s (smoothExtensionTangent (I := I) x (e a))
            (smoothOrthoFrame (I := I) g x) (fun y : M => S.toSection y) x := by
      rw [genuineCurvTraceFixedFramePureR, genuineCurvTraceFixedFrameCovDeriv,
        ← Finset.sum_add_distrib, tensor3rdCurvGenuine]
    rw [show (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
          tensor3rdCurvGenuine (I := I) g 0 s (smoothExtensionTangent (I := I) x (e a))
            (fun y : M => S.toSection y) x) = _ from hclm]
    rw [ContinuousLinearMap.add_apply]
  rw [hsplit_val, Tensor0SSpace.toModel_add, ContinuousMultilinearMap.add_apply, smul_add]

/-- **Posited: the moving-centre genuine curvature sections `Gcurv`, `GcurvDeriv`.** For a closed
smooth Riemannian manifold `(M, g)`, every covariant rank `s` and every smooth compactly-supported
`(0, s)`-tensor `S`, there are two *single, base-point-independent* smooth compactly-supported
`(0, s + 1)`-tensor sections `Gcurv`, `GcurvDeriv` whose unit-section fibre values reconstruct, in
the slot-`0` witness frame `e` of `pointwiseTensorCurv_toSection_eq_genuine_add_bracket_field`, as the
pure-Riemann and differentiated-curvature parts of the genuine third-order curvature fibre field,
*and whose sum carries the full genuine field* matching that committed field split:
```
toModel ((Gcurv.toSection x) (unit)) (Fin.cons w m)      = genuineThirdCurvFieldFibPureR g s S x e w m,
toModel ((GcurvDeriv.toSection x) (unit)) (Fin.cons w m) = genuineThirdCurvFieldFibCovDeriv g s S x e w m,
```
with the SAME frame `e`, so that (by `genuineThirdCurvFieldFib_eq_pureR_add_covDeriv`)
```
toModel ((Gcurv.toSection x) (unit) + (GcurvDeriv.toSection x) (unit)) (Fin.cons w m)
  = genuineThirdCurvFieldFib g s S x e w m
```
— the genuine part of `pointwiseTensorCurv_toSection_eq_genuine_add_bracket_field`.

**Why this is TRUE.** The pure-Riemann field `genuineThirdCurvFieldFibPureR g s S x e w m` is the
inner-product-weighted slot-`0` frame reconstruction
`∑ₐ ⟨e a, w⟩_g • toModel (genuineCurvTraceFixedFramePureR g s (W a) (smoothOrthoFrame g x) S x) m`
of the `(0, s)`-valued pure-Riemann genuine curvature trace
`genuineCurvTraceFixedFramePureR g s (W a) (smoothOrthoFrame g x) S x = ∑ᵢ R(B_i, W a)(∇_{B_i} S)`,
which is `C^∞(M)`-linear (tensorial) in the direction `W a` (`riemannSec_add_right`,
`riemannSec_smul_right`). Hence `v ↦ ∑ᵢ R(B_i, ·)(∇_{B_i} S)` is a continuous linear map
`T_x M → TensorRSSpace 0 s I x`, and the slot-`0` uncurry
(`tensor0S_eq_sum_slot0_uncurry`/`tensor0S_uncurry_cons_eval_orthonormal`) assembles it into a unique
`(0, s + 1)`-tensor whose slot-`0` curry recovers it — the moving-centre section value
`Gcurv.toSection x`; likewise for `GcurvDeriv` with the differentiated-curvature trace
`∑ᵢ ∇_{B_i}(R(B_i, ·) S)`. As base-point sections, `x ↦ Gcurv.toSection x`,
`x ↦ GcurvDeriv.toSection x` are smooth by the frame-freezing template: the genuine curvature trace
is a genuine metric trace (the frame index `B_i` contracted twice — in slot-`1` of `R` and as the
`∇`-direction), hence frame-independent among `g_x`-orthonormal frames, so on `smoothOrthoFrameNbhd
x₀` the moving trace equals the frozen trace against `smoothOrthoFrame g x₀`, a smooth `(0, s)`-
section by `genuineCurvTraceFixedFramePureR_contMDiff` / `genuineCurvTraceFixedFrameCovDeriv_contMDiff`
(`smoothOrthoFrame_smooth`); the slot-`0` assembly of a smooth direction-linear family is smooth, and
`ContMDiffAt.congr_of_eventuallyEq` transfers smoothness. Compact support is automatic on the closed
`M` (`HasCompactSupport.of_compactSpace`). The shared-frame combined identity is
`genuineThirdCurvFieldFib_eq_pureR_add_covDeriv`. The witness frame `e` is the one supplied by the
slot-`0` Parseval reconstruction `tensor0S_eq_sum_slot0_uncurry`, which is exactly the frame of the
committed field split.

**Non-vacuity.** The zero witness `Gcurv = GcurvDeriv = 0` is rejected: the fibre properties would
force the pure-Riemann contraction `∑ᵢ R(B_i, W a)(∇_{B_i} S)` and the differentiated-curvature
contraction `∑ᵢ ∇_{B_i}(R(B_i, W a) S)` to vanish at every point and direction. On a non-flat
manifold `R ≠ 0` (resp. `∇R ≠ 0`) and `∇S` is a generic non-zero `(0, s + 1)`-tensor for non-parallel
`S`, so the genuine curvature contractions are genuinely non-zero — the sections must carry the actual
pure-Riemann and `(∇R) S` content. -/
theorem exists_GcurvSection_GcurvDerivSection
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) :
    ∃ Gcurv GcurvDeriv : SmoothCcTensor g 0 (s + 1),
      ∀ x : M, ∃ (n : ℕ) (e : Fin n → TangentSpace I x),
        n = Module.finrank ℝ (TangentSpace I x) ∧
        (∀ i j : Fin n, g.inner x (e i) (e j) = if i = j then (1 : ℝ) else 0) ∧
        (∀ (w : TangentSpace I x) (m : Fin s → TangentSpace I x),
          Tensor0SSpace.toModel
              ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
                Gcurv.toSection x) (unitZeroSec (I := I) (M := M) x)) (Fin.cons w m) =
            genuineThirdCurvFieldFibPureR (I := I) (M := M) g s S x e w m) ∧
        (∀ (w : TangentSpace I x) (m : Fin s → TangentSpace I x),
          Tensor0SSpace.toModel
              ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
                GcurvDeriv.toSection x) (unitZeroSec (I := I) (M := M) x)) (Fin.cons w m) =
            genuineThirdCurvFieldFibCovDeriv (I := I) (M := M) g s S x e w m) := by
  sorry

/-- **The moving-centre pure-Riemann genuine curvature section** `Gcurv`, a smooth compactly-
supported `(0, s + 1)`-tensor section packaging the pure-Riemann contraction `R(∇S)` of the
order-`2` rough-Laplacian / covariant-gradient commutator defect (the slot-`0` assembly of the
moving-frame genuine curvature trace `∑ᵢ R(B_i, ·)(∇_{B_i} S)`). Defined as the first witness of
`exists_GcurvSection_GcurvDerivSection`. -/
noncomputable def GcurvSection
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) :
    SmoothCcTensor g 0 (s + 1) :=
  (exists_GcurvSection_GcurvDerivSection (I := I) (M := M) g s S).choose

/-- **The moving-centre differentiated-curvature genuine section** `GcurvDeriv`, a smooth compactly-
supported `(0, s + 1)`-tensor section packaging the differentiated-curvature contraction `(∇R) S` of
the commutator defect (the slot-`0` assembly of the moving-frame genuine trace
`∑ᵢ ∇_{B_i}(R(B_i, ·) S)`). Defined as the second witness of
`exists_GcurvSection_GcurvDerivSection`. -/
noncomputable def GcurvDerivSection
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) :
    SmoothCcTensor g 0 (s + 1) :=
  (exists_GcurvSection_GcurvDerivSection (I := I) (M := M) g s S).choose_spec.choose

/-- The unified defining property of `GcurvSection` / `GcurvDerivSection`: at every base point `x`,
in a single `g_x`-orthonormal frame `e`, the unit-section fibre values reconstruct as the pure-Riemann
and differentiated-curvature parts of the genuine third-order curvature fibre field. -/
theorem GcurvSection_GcurvDerivSection_spec
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) (x : M) :
    ∃ (n : ℕ) (e : Fin n → TangentSpace I x),
      n = Module.finrank ℝ (TangentSpace I x) ∧
      (∀ i j : Fin n, g.inner x (e i) (e j) = if i = j then (1 : ℝ) else 0) ∧
      (∀ (w : TangentSpace I x) (m : Fin s → TangentSpace I x),
        Tensor0SSpace.toModel
            ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
              (GcurvSection (I := I) (M := M) g s S).toSection x)
              (unitZeroSec (I := I) (M := M) x)) (Fin.cons w m) =
          genuineThirdCurvFieldFibPureR (I := I) (M := M) g s S x e w m) ∧
      (∀ (w : TangentSpace I x) (m : Fin s → TangentSpace I x),
        Tensor0SSpace.toModel
            ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
              (GcurvDerivSection (I := I) (M := M) g s S).toSection x)
              (unitZeroSec (I := I) (M := M) x)) (Fin.cons w m) =
          genuineThirdCurvFieldFibCovDeriv (I := I) (M := M) g s S x e w m) :=
  (exists_GcurvSection_GcurvDerivSection (I := I) (M := M) g s S).choose_spec.choose_spec x

/-- **The fibre value of `GcurvSection` is the pure-Riemann part of the genuine curvature field.**
At every base point `x` there is a `g_x`-orthonormal frame `e` in which the unit-section fibre value
of `GcurvSection g s S` reconstructs as `genuineThirdCurvFieldFibPureR g s S x e`. -/
theorem GcurvSection_toSection_eq_genuineThirdCurvFieldFibPureR
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) (x : M) :
    ∃ (n : ℕ) (e : Fin n → TangentSpace I x),
      n = Module.finrank ℝ (TangentSpace I x) ∧
      (∀ i j : Fin n, g.inner x (e i) (e j) = if i = j then (1 : ℝ) else 0) ∧
      ∀ (w : TangentSpace I x) (m : Fin s → TangentSpace I x),
        Tensor0SSpace.toModel
            ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
              (GcurvSection (I := I) (M := M) g s S).toSection x)
              (unitZeroSec (I := I) (M := M) x)) (Fin.cons w m) =
          genuineThirdCurvFieldFibPureR (I := I) (M := M) g s S x e w m := by
  obtain ⟨n, e, hn, horth, hpureR, _⟩ :=
    GcurvSection_GcurvDerivSection_spec (I := I) (M := M) g s S x
  exact ⟨n, e, hn, horth, hpureR⟩

/-- **The fibre value of `GcurvDeriv` is the differentiated-curvature part of the genuine curvature
field.** At every base point `x` there is a `g_x`-orthonormal frame `e` in which the unit-section
fibre value of `GcurvDerivSection g s S` reconstructs as `genuineThirdCurvFieldFibCovDeriv g s S x e`. -/
theorem GcurvDerivSection_toSection_eq_genuineThirdCurvFieldFibCovDeriv
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) (x : M) :
    ∃ (n : ℕ) (e : Fin n → TangentSpace I x),
      n = Module.finrank ℝ (TangentSpace I x) ∧
      (∀ i j : Fin n, g.inner x (e i) (e j) = if i = j then (1 : ℝ) else 0) ∧
      ∀ (w : TangentSpace I x) (m : Fin s → TangentSpace I x),
        Tensor0SSpace.toModel
            ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
              (GcurvDerivSection (I := I) (M := M) g s S).toSection x)
              (unitZeroSec (I := I) (M := M) x)) (Fin.cons w m) =
          genuineThirdCurvFieldFibCovDeriv (I := I) (M := M) g s S x e w m := by
  obtain ⟨n, e, hn, horth, _, hcovDeriv⟩ :=
    GcurvSection_GcurvDerivSection_spec (I := I) (M := M) g s S x
  exact ⟨n, e, hn, horth, hcovDeriv⟩

/-- **The sum of the two genuine curvature sections fibre-matches the genuine field of the committed
field split.** At every base point `x`, in a single `g_x`-orthonormal frame `e`, the unit-section
fibre value of `GcurvSection g s S + GcurvDerivSection g s S` reconstructs as the genuine third-order
curvature fibre field `genuineThirdCurvFieldFib g s S x e` — the genuine part appearing in
`pointwiseTensorCurv_toSection_eq_genuine_add_bracket_field`. This identifies
`GcurvSection + GcurvDerivSection` with the genuine field, so the downstream leaf-`A` assembly reads
the order-`2` commutator defect as `Curv S = (GcurvSection + GcurvDerivSection) + bracket-field`. -/
theorem GcurvSection_add_GcurvDerivSection_toSection_eq_genuineThirdCurvField
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) (x : M) :
    ∃ (n : ℕ) (e : Fin n → TangentSpace I x),
      n = Module.finrank ℝ (TangentSpace I x) ∧
      (∀ i j : Fin n, g.inner x (e i) (e j) = if i = j then (1 : ℝ) else 0) ∧
      ∀ (w : TangentSpace I x) (m : Fin s → TangentSpace I x),
        Tensor0SSpace.toModel
            ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
              (GcurvSection (I := I) (M := M) g s S).toSection x)
              (unitZeroSec (I := I) (M := M) x)) (Fin.cons w m) +
          Tensor0SSpace.toModel
            ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
              (GcurvDerivSection (I := I) (M := M) g s S).toSection x)
              (unitZeroSec (I := I) (M := M) x)) (Fin.cons w m) =
          genuineThirdCurvFieldFib (I := I) (M := M) g s S x e w m := by
  obtain ⟨n, e, hn, horth, hpureR, hcovDeriv⟩ :=
    GcurvSection_GcurvDerivSection_spec (I := I) (M := M) g s S x
  refine ⟨n, e, hn, horth, fun w m => ?_⟩
  rw [hpureR w m, hcovDeriv w m,
    ← genuineThirdCurvFieldFib_eq_pureR_add_covDeriv (I := I) (M := M) g s S x e w m]

end Connection
end Integral
end DifferentialGeometry

end
