import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.MovingFrameCurvatureTraceSmooth
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.MetricContractionLeibnizGrid
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.UniformCurvatureSup

/-!
# The frozen-frame pure-Riemann curvature endomorphism tower and its iterated-gradient grid

For a closed (compact, boundaryless) smooth Riemannian manifold `(M, g)` modelled on a real
inner-product space `E`, and a *fixed* smooth tangent frame `B`, this file builds the recursive
differentiated-operator tower of the **frozen-frame pure-Riemann curvature endomorphism**

```
v ↦ ∑ᵢ R(B_iˣ, v)(slot0_{B_iˣ} W),   slot0_{B_iˣ} W := (tensor0S_curry r x (W x)) (B_iˣ),
```

uncurried through `covGradBundleEquiv 0 r`, packaged as a `DiffBilinOp` (the abstract differentiated
bilinear-contraction engine of `MetricContractionLeibnizGrid`), and uses the engine's *proved*
binomial covariant-Leibniz grid to bound the iterated covariant gradients of the frozen-frame
pure-Riemann section `fixedFramePureRSection` (`MovingFrameCurvatureTraceSmooth`).

## The endomorphism is a rank-generic fibrewise-linear operator

The order-`0` operator `pureRFrozenEndo g r B : SmoothCcTensor g 0 r → SmoothCcTensor g 0 r` reads the
leftmost (slot-`0`) component of its rank-`r` input `W` along each frame vector `B_iˣ`
(`tensor0SPartialEval`), contracts it through the curvature operator `R(B_iˣ, ·)`, and uncurries the
resulting curvature-direction continuous-linear map back into a rank-`r` tensor through
`covGradBundleEquiv 0 (r-1)`. It is defined for every rank `r ≥ 1`; at rank `0` (no slot to read) it
is the zero operator, which keeps the `DiffBilinOp` totality without affecting the grid (the recursion
only ever increases the rank, so rank `0` is never reached from the base rank `s + 1`). It is a fixed
(`B`-, `g`-, `R`-built) smooth fibrewise-`ℝ`-linear operator, exactly the shape `DiffBilinOp`
abstracts.

The differentiated tower `op (p + 1) r W := ∇(op p r W) − (rank-cast) op p (r + 1) (∇W)` is the exact
covariant-Leibniz remainder, so the structure field `covGrad_op` holds by `sub_add_cancel` — *proved*,
not posited. The bridge `op 0 (s + 1) (∇S) = fixedFramePureRSection g s S B` is definitional
bookkeeping through the slot-`0` reading of the differentiated section `∇S = covGrad g 0 s S`
(`covGrad_toSection_apply_eval`).

## What is proved vs. posited

The single genuinely-irreducible analytic primitive is the **per-order section-proportional fibre
envelope** for the differentiated frozen-frame operators, `exists_proportional_pureRFrozenFrameDiffOp`:
`rfns(op p r W)(x) ≤ kappa p · rfns(W)(x)`, **uniform in the frame `B`**. Each `op p` is a smooth
fixed fibrewise-linear operator (a recursive covariant-Leibniz remainder of the smooth frozen-frame
curvature endomorphism), so it is uniformly bounded, proportionally to its section, on the compact
`M` — and the bound is `B`-uniform because the frame `B` enters only through the curvature operator's
two contracted slots (`B_i` is contracted twice: as the slot-`1` argument of `R` and as the slot-`0`
reading direction), whose magnitude is the bounded curvature sup, not a frame jet. It is the exact
frozen-frame analogue of `exists_continuous_proportional_diffCurvOp` (the metric-contraction tower's
posited envelope), here `B`-uniform; consumers transitively depend on `sorryAx` through it.

Everything else — the recursive operator construction, the smoothness of the order-`0` endomorphism,
the `DiffBilinOp` packaging, the grid `DiffBilinOp.exists_rfns_iteratedCovGrad_singleSum_le`, the
bridge to `fixedFramePureRSection`, and the rank-shift `∇^q(∇S) ≅ ∇^{q + 1}S` re-indexing into the
graded curvature-jet shape — is *proved* here. The headline output
`fixedFramePureRSection_iteratedCovGrad_grid_bound` is the `(p, w) = (1, 1)` grid the moving-frame
curvature-jet induction (`OrderSeparatedCurvatureJet`) consumes.

## Convention

Geometer convention; all fibre norms are the intrinsic `riemannianFiberNormSq`. The endomorphism is
genuinely `rfns(W)`-order (it is a fixed operator applied to `W`), so its order-`0` instance on `∇S`
makes the grid genuinely `rfns(∇S) = rfns(∇^{·+1}S)`-order — lowest contracted order `1`.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

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

/-- **The slot-`i` frozen-frame pure-Riemann curvature direction linear map (rank `m + 1`).** Fixing
the frame index `i` and a smooth tangent frame `B`, the linear map in the curvature direction
```
v ↦ riemannOp (tensorCov g 0 m) x (B_iˣ) v (((covGradBundleEquiv 0 m x).symm (W x)) (B_iˣ)),
```
the slot-`i` summand of the frozen-frame pure-Riemann curvature endomorphism on the rank-`(m + 1)`
tensor `W`. The contracted argument `((covGradBundleEquiv 0 m x).symm (W x)) (B_iˣ)` is the slot-`0`
reading of `W` along the frame vector `B_iˣ` — a `(0, m)`-tensor; `B_i` is contracted *twice* (as the
slot-`1` argument of `R` and as the slot-`0` reading direction). -/
private def pureRFrozenDirLMSummand
    (g : SmoothRiemannianMetric I M) (m : ℕ)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b)
    (W : Π b : M, TensorRSSpace 0 (m + 1) I b) (x : M)
    (i : Fin (Module.finrank ℝ E)) :
    TangentSpace I x →ₗ[ℝ] TensorRSSpace 0 m I x where
  toFun v := riemannOp (tensorCov (I := I) g 0 m) x (B i x) v
    ((covGradBundleEquiv (I := I) (M := M) 0 m x).symm (W x) (B i x))
  map_add' v v' := by
    rw [map_add (riemannOp (tensorCov (I := I) g 0 m) x (B i x)) v v']
    rfl
  map_smul' c v := by
    rw [map_smul (riemannOp (tensorCov (I := I) g 0 m) x (B i x)) c v]
    rfl

private noncomputable def pureRFrozenDirCLMSummand
    (g : SmoothRiemannianMetric I M) (m : ℕ)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b)
    (W : Π b : M, TensorRSSpace 0 (m + 1) I b) (x : M)
    (i : Fin (Module.finrank ℝ E)) :
    TangentSpace I x →L[ℝ] TensorRSSpace 0 m I x :=
  haveI : T2Space (TangentSpace I x) := inferInstanceAs (T2Space E)
  haveI : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  LinearMap.toContinuousLinearMap (pureRFrozenDirLMSummand (I := I) (M := M) g m B W x i)

/-- **The frozen-frame pure-Riemann curvature direction continuous-linear map (rank `m + 1`).** The
frame sum over `i` of `pureRFrozenDirCLMSummand`: the curvature-direction-linear map
`v ↦ ∑ᵢ riemannOp (tensorCov g 0 m) x (B_iˣ) v (slot0_{B_iˣ} W)` whose slot-`0` uncurry is the
frozen-frame pure-Riemann curvature endomorphism on `W`. -/
private noncomputable def pureRFrozenDirCLM
    (g : SmoothRiemannianMetric I M) (m : ℕ)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b)
    (W : Π b : M, TensorRSSpace 0 (m + 1) I b) (x : M) :
    TangentSpace I x →L[ℝ] TensorRSSpace 0 m I x :=
  ∑ i : Fin (Module.finrank ℝ E), pureRFrozenDirCLMSummand (I := I) (M := M) g m B W x i

/-- The defining apply formula for `pureRFrozenDirCLM`: the frame sum of curvature contractions of
the slot-`0` readings of `W`. -/
private lemma pureRFrozenDirCLM_apply
    (g : SmoothRiemannianMetric I M) (m : ℕ)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b)
    (W : Π b : M, TensorRSSpace 0 (m + 1) I b) (x : M) (v : TangentSpace I x) :
    pureRFrozenDirCLM (I := I) (M := M) g m B W x v =
      ∑ i : Fin (Module.finrank ℝ E),
        riemannOp (tensorCov (I := I) g 0 m) x (B i x) v
          ((covGradBundleEquiv (I := I) (M := M) 0 m x).symm (W x) (B i x)) := by
  classical
  rw [pureRFrozenDirCLM, ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [pureRFrozenDirCLMSummand, LinearMap.coe_toContinuousLinearMap', pureRFrozenDirLMSummand,
    LinearMap.coe_mk, AddHom.coe_mk]

/-- **The order-`0` frozen-frame pure-Riemann curvature endomorphism fibre value (rank `m + 1`).**
The slot-`0` uncurry, through `covGradBundleEquiv 0 m x`, of the frozen-frame pure-Riemann curvature
direction CLM `pureRFrozenDirCLM g m B (W.toSection) x` — the unique `(0, m + 1)`-tensor whose slot-`0`
curry along `v` is `∑ᵢ R(B_iˣ, v)(slot0_{B_iˣ} W)`. -/
private noncomputable def pureRFrozenEndoFib
    (g : SmoothRiemannianMetric I M) (m : ℕ)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b)
    (W : SmoothCcTensor g 0 (m + 1)) (x : M) :
    TensorRSSpace 0 (m + 1) I x :=
  covGradBundleEquiv (I := I) (M := M) 0 m x
    (pureRFrozenDirCLM (I := I) (M := M) g m B (fun y : M => W.toSection y) x)

/-- **The slot-`0` reading of `W` along `B_i` is a smooth `(0, m)`-tensor section.** For a smooth
frame field `B_i` and a smooth `(0, m + 1)`-tensor section `W`, the section
`x ↦ ((covGradBundleEquiv 0 m x).symm (W.toSection x)) (B_iˣ)` is `C^∞`. The smooth
`Hom(TM, T^{(0,m)})`-section `x ↦ ⟨x, (covGradBundleEquiv 0 m x).symm (W.toSection x)⟩` (W smooth,
transported through the inverse smooth bundle equivalence
`covGradBundleEquiv_symm_contMDiff_totalSpace`) is evaluated at the smooth field `B_i`
(`ContMDiff.clm_bundle_apply`). -/
private theorem pureRFrozenSlot0Sec_contMDiff
    (g : SmoothRiemannianMetric I M) (m : ℕ)
    {B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b}
    (hB : ∀ i, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (B i)))
    (W : SmoothCcTensor g 0 (m + 1)) (i : Fin (Module.finrank ℝ E)) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 0 m ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel 0 m ℝ E)
        (E := fun z : M => TensorRSSpace 0 m I z) x
        ((covGradBundleEquiv (I := I) (M := M) 0 m x).symm (W.toSection x) (B i x))) := by
  classical
  have hHom : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] TensorRSModel 0 m ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (E →L[ℝ] TensorRSModel 0 m ℝ E)
        (E := fun z : M => TangentSpace I z →L[ℝ] TensorRSSpace 0 m I z) x
        ((covGradBundleEquiv (I := I) (M := M) 0 m x).symm (W.toSection x))) := by
    have hWtot : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 0 (m + 1) ℝ E)) ∞
        (fun x : M => TotalSpace.mk' (TensorRSModel 0 (m + 1) ℝ E)
          (E := fun z : M => TensorRSSpace 0 (m + 1) I z) x (W.toSection x)) :=
      W.toSection.contMDiff_toFun
    exact (covGradBundleEquiv_symm_contMDiff_totalSpace (I := I) (M := M) 0 m).comp hWtot
  exact ContMDiff.clm_bundle_apply (b := fun x : M => x)
    (ϕ := fun x => (covGradBundleEquiv (I := I) (M := M) 0 m x).symm (W.toSection x))
    (v := fun x => B i x) hHom (hB i)

/-- **The frozen-frame pure-Riemann curvature direction CLM is a smooth `Hom(TM, T^{(0,m)})`-bundle
section.** For a smooth frame `B`, the section `x ↦ ⟨x, pureRFrozenDirCLM g m B (W.toSection) x⟩` is
`C^∞`. On every smooth tangent field `Y`, the section
`x ↦ ⟨x, pureRFrozenDirCLM g m B (W.toSection) x (Y x)⟩` is the frame sum (over `i`) of the
curvature contractions `riemannSec (B_i) Y (slot0_{B_i} W)`, each smooth by `riemannSec_contMDiff`
on the smooth `B_i`, `Y`, and the smooth slot-`0` reading `pureRFrozenSlot0Sec_contMDiff`; bridged to
the bundle by `cotangentCov_clmSection_smooth_aux`. -/
private theorem pureRFrozenDirCLM_homSection_contMDiff
    (g : SmoothRiemannianMetric I M) (m : ℕ)
    {B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b}
    (hB : ∀ i, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (B i)))
    (W : SmoothCcTensor g 0 (m + 1)) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] TensorRSModel 0 m ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (E →L[ℝ] TensorRSModel 0 m ℝ E)
        (E := fun y : M => TangentSpace I y →L[ℝ] TensorRSSpace 0 m I y) x
        (pureRFrozenDirCLM (I := I) (M := M) g m B (fun y : M => W.toSection y) x)) := by
  classical
  refine cotangentCov_clmSection_smooth_aux
    (φ := fun x : M => pureRFrozenDirCLM (I := I) (M := M) g m B (fun y : M => W.toSection y) x)
    (fun Y => ?_)
  have hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (fun b : M => (Y : Π b : M, TangentSpace I b) b)) :=
    Y.contMDiff
  -- The frame sum of curvature contractions `riemannSec (B_i) Y (slot0_{B_i} W)` is smooth.
  have hsum : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 0 m ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel 0 m ℝ E)
        (E := fun z : M => TensorRSSpace 0 m I z) x
        (∑ i : Fin (Module.finrank ℝ E),
          riemannSec (tensorCov (I := I) g 0 m) (B i) (fun b : M => Y b)
            (fun y : M => (covGradBundleEquiv (I := I) (M := M) 0 m y).symm (W.toSection y) (B i y))
            x)) := by
    refine ContMDiff.sum_section (s := Finset.univ) (fun i _ => ?_)
    exact riemannSec_contMDiff (cov := tensorCov (I := I) g 0 m) (hB i) hY
      (pureRFrozenSlot0Sec_contMDiff (I := I) (M := M) g m hB W i)
  refine hsum.congr ?_
  intro x
  refine congrArg (TotalSpace.mk' (TensorRSModel 0 m ℝ E)
    (E := fun z : M => TensorRSSpace 0 m I z) x) ?_
  rw [pureRFrozenDirCLM_apply]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  exact (riemannOp_apply_smooth (cov := tensorCov (I := I) g 0 m) (X := B i) (Y := fun b : M => Y b)
    (Z := fun y : M => (covGradBundleEquiv (I := I) (M := M) 0 m y).symm (W.toSection y) (B i y))
    (x := x) (hB i) hY (pureRFrozenSlot0Sec_contMDiff (I := I) (M := M) g m hB W i)).symm ▸ rfl

/-- **Base-point smoothness of the order-`0` frozen-frame pure-Riemann curvature endomorphism fibre
field.** For a smooth frame `B`, the `(0, m + 1)`-tensor fibre field
`x ↦ pureRFrozenEndoFib g m B W x` is a smooth section. The smooth `Hom(TM, T^{(0,m)})`-section
`pureRFrozenDirCLM_homSection_contMDiff` is transported, fibrewise through the smooth bundle
equivalence `covGradBundleSmoothEquiv 0 m`, into the `(0, m + 1)`-tensor bundle. -/
private theorem pureRFrozenEndoFib_contMDiff
    (g : SmoothRiemannianMetric I M) (m : ℕ)
    {B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b}
    (hB : ∀ i, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (B i)))
    (W : SmoothCcTensor g 0 (m + 1)) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 0 (m + 1) ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel 0 (m + 1) ℝ E)
        (E := fun z : M => TensorRSSpace 0 (m + 1) I z) x
        (pureRFrozenEndoFib (I := I) (M := M) g m B W x)) := by
  classical
  have hcomp :
      ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 0 (m + 1) ℝ E)) ∞
        ((covGradBundleSmoothEquiv (I := I) (M := M) 0 m).toDiffeomorph ∘
          (fun x : M => TotalSpace.mk' (E →L[ℝ] TensorRSModel 0 m ℝ E)
            (E := fun y : M => TangentSpace I y →L[ℝ] TensorRSSpace 0 m I y) x
            (pureRFrozenDirCLM (I := I) (M := M) g m B (fun y : M => W.toSection y) x))) :=
    (covGradBundleSmoothEquiv (I := I) (M := M) 0 m).toDiffeomorph.contMDiff.comp
      (pureRFrozenDirCLM_homSection_contMDiff (I := I) (M := M) g m hB W)
  refine hcomp.congr ?_
  intro x
  rw [Function.comp_apply]
  exact covGradBundleSmoothEquiv_toDiffeomorph_apply (I := I) (M := M) 0 m x
    (pureRFrozenDirCLM (I := I) (M := M) g m B (fun y : M => W.toSection y) x)

/-- **The order-`0` frozen-frame pure-Riemann curvature endomorphism at rank `m + 1`**, a smooth
compactly-supported `(0, m + 1)`-tensor section: the slot-`0` uncurry of the frozen-frame pure-Riemann
curvature direction CLM `pureRFrozenDirCLM g m B (W.toSection)`. It is `B`-, `g`-, `R`-built and
fibrewise-`ℝ`-linear in `W`; smoothness `pureRFrozenEndoFib_contMDiff`, compact support on the closed
manifold. -/
private noncomputable def pureRFrozenEndoSucc
    (g : SmoothRiemannianMetric I M) (m : ℕ)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b)
    (hB : ∀ i, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (B i)))
    (W : SmoothCcTensor g 0 (m + 1)) :
    SmoothCcTensor g 0 (m + 1) where
  toSection :=
    { toFun := fun x : M => pureRFrozenEndoFib (I := I) (M := M) g m B W x
      contMDiff_toFun := pureRFrozenEndoFib_contMDiff (I := I) (M := M) g m hB W }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

@[simp] private lemma pureRFrozenEndoSucc_toSection
    (g : SmoothRiemannianMetric I M) (m : ℕ)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b)
    (hB : ∀ i, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (B i)))
    (W : SmoothCcTensor g 0 (m + 1)) (x : M) :
    (pureRFrozenEndoSucc (I := I) (M := M) g m B hB W).toSection x =
      pureRFrozenEndoFib (I := I) (M := M) g m B W x := rfl

/-- **The order-`0` frozen-frame pure-Riemann curvature endomorphism at every rank** (totalised).
For rank `r = m + 1 ≥ 1` it is the genuine endomorphism `pureRFrozenEndoSucc`; for rank `0` (no
slot-`0` to read) it is the zero operator. The zero junk at rank `0` is never reached by the grid
(the differentiated tower's recursion only increases the rank, starting from the base rank `s + 1`),
but it makes the `DiffBilinOp` totality hold. -/
private noncomputable def pureRFrozenEndo0
    (g : SmoothRiemannianMetric I M)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b)
    (hB : ∀ i, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (B i))) :
    ∀ (r : ℕ), SmoothCcTensor g 0 r → SmoothCcTensor g 0 r
  | 0 => fun _ => 0
  | (m + 1) => fun W => pureRFrozenEndoSucc (I := I) (M := M) g m B hB W

/-- **The order-`p` differentiated frozen-frame pure-Riemann curvature operator.** Acting on a smooth
compactly-supported `(0, r)`-tensor section `W`, `pureRFrozenDiffOp g B hB p r W` is the `p`-times
covariantly-differentiated frozen-frame pure-Riemann curvature endomorphism `(∇^p R(B, ·))W`, a smooth
compactly-supported `(0, r + p)`-tensor, defined recursively as the exact covariant-Leibniz remainder:

* `p = 0`: the order-`0` endomorphism `pureRFrozenEndo0 g B hB r W`;
* `p + 1`: `∇(pureRFrozenDiffOp p r W) − (rank-cast) pureRFrozenDiffOp p (r + 1) (∇W)` (the
  differentiated curvature: the part of `∇(∇^p R(B,·) W)` not captured by `∇^p R(B,·)(∇W)`); the
  right summand carries covariant rank `(r + 1) + p`, rank-cast to the differentiated rank `(r + p) + 1`
  via `castRankCc_db`.

By construction the single-step covariant Leibniz `∇(op p r W) = op (p + 1) r W + (rank-cast)
op p (r + 1) (∇W)` holds by `sub_add_cancel`. -/
private noncomputable def pureRFrozenDiffOp
    (g : SmoothRiemannianMetric I M)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b)
    (hB : ∀ i, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (B i))) :
    ∀ (p r : ℕ), SmoothCcTensor g 0 r → SmoothCcTensor g 0 (r + p)
  | 0, r => fun W => pureRFrozenEndo0 (I := I) (M := M) g B hB r W
  | (p + 1), r => fun W =>
      covGrad (I := I) (M := M) g 0 (r + p)
          (pureRFrozenDiffOp g B hB p r W) -
        castRankCc_db g 0 (by omega : (r + 1) + p = r + (p + 1))
          (pureRFrozenDiffOp g B hB p (r + 1) (covGrad (I := I) (M := M) g 0 r W))

/-- **The exact single-step covariant Leibniz of the differentiated frozen-frame curvature tower.**
By the recursive definition, `∇(op p r W)` splits exactly into the higher-order remainder
`op (p + 1) r W` and the rank-cast lower-order term applied to `∇W`. Proved by `sub_add_cancel`. -/
private theorem covGrad_pureRFrozenDiffOp_eq
    (g : SmoothRiemannianMetric I M)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b)
    (hB : ∀ i, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (B i)))
    (p r : ℕ) (W : SmoothCcTensor g 0 r) :
    covGrad (I := I) (M := M) g 0 (r + p) (pureRFrozenDiffOp (I := I) (M := M) g B hB p r W) =
      pureRFrozenDiffOp (I := I) (M := M) g B hB (p + 1) r W +
        castRankCc_db g 0 (by omega : (r + 1) + p = r + (p + 1))
          (pureRFrozenDiffOp (I := I) (M := M) g B hB p (r + 1)
            (covGrad (I := I) (M := M) g 0 r W)) := by
  change _ = (covGrad (I := I) (M := M) g 0 (r + p)
      (pureRFrozenDiffOp (I := I) (M := M) g B hB p r W) -
      castRankCc_db g 0 (by omega : (r + 1) + p = r + (p + 1))
        (pureRFrozenDiffOp (I := I) (M := M) g B hB p (r + 1)
          (covGrad (I := I) (M := M) g 0 r W))) + _
  rw [sub_add_cancel]

/-- **Posited centre-uniform at-centre per-order, per-rank section-proportional fibre envelope for the
differentiated frozen-frame pure-Riemann curvature tower.** For a closed smooth Riemannian manifold
`(M, g)` there is a *valence/order-dependent* nonnegative envelope family `kappa : ℕ → ℕ → ℝ` (indexed
by differentiation order `p` and covariant rank `r`), **uniform over the centre `x₀`**, such that for
every differentiation order `p`, covariant rank `r`, smooth compactly-supported `(0, r)`-tensor `W`,
and centre `x₀`, the order-`p` differentiated frozen-frame pure-Riemann curvature operator at the
*centre frame* `smoothOrthoFrame g x₀`, evaluated at its own centre `x₀`, has intrinsic squared fibre
norm at most `kappa p r` times that of `W`:

```
rfns(pureRFrozenDiffOp g (smoothOrthoFrame g x₀) … p r W)(x₀) ≤ kappa p r · rfns(W)(x₀).
```

**Restatement note (certificate-sanctioned restatement #2).** Two facts force this shape. (i) The
earlier `∀ B (smooth-only), x` free-frame form is FALSE: the operator is fibrewise-`ℝ`-bilinear in the
contracted frame (`B_i` is contracted *twice*), hence quadratic in `B`, with no scale constraint on a
generic smooth frame `B`; the centre-uniform form fixes the frame to the `g`-orthonormal
`smoothOrthoFrame g x₀` evaluated at its own centre `x₀`, where the frame is `g_{x₀}`-orthonormal
(`smoothOrthoFrame_orthonormal_at_center`), so the twice-contracted Gram factors are `1`. (ii) The
constant is genuinely **rank-indexed** (`kappa : ℕ → ℕ → ℝ`, not the earlier order-only `ℕ → ℝ`): the
rank-`m` curvature derivation `riemannOp (tensorCov g 0 m)` acts on *all* `m` tensor slots, so its raw
Hilbert–Schmidt fibre-operator constant — the dual-frame energy is slot-summed — grows with the rank
`m`; no single order-only `kappa p` covers all ranks `r` (the order-`0` constant of the discharge
roadmap is already `N·(N·Ccurv_sup m)` with `Ccurv_sup m` the *rank-`m`* curvature sup). This is
exactly the frame the moving-centre curvature jet consumes (a per-`x₀` choice of centre frame), so the
restriction loses nothing downstream; the rank index is absorbed by the consumer's per-rank constant
family `c : ℕ → ℕ → ℝ` through the rank window `[s + 1, s + 1 + k]` the grid headline supremises.

**Why this is TRUE — the frozen-frame analogue of `exists_continuous_proportional_diffCurvOp`.** Each
`pureRFrozenDiffOp p` is a smooth *fixed* fibrewise-`ℝ`-linear operator on tensor sections (a recursive
covariant-Leibniz remainder of the smooth frozen-frame curvature endomorphism `R(B, ·)` uncurried
through `covGradBundleEquiv`), assembled from the smooth metric `g`, the smooth Levi-Civita curvature
and its smooth covariant derivatives, and the smooth frame `B`. Its fibre-operator norm — the least
`c` with `rfns(op p r W)(x) ≤ c · rfns(W)(x)` for all `W` at `x` — is bounded uniformly over the
compact `M` (continuous in `x` by the smoothness of the constituent chart Christoffel / Riemann
coordinate data and their iterated partials on the compact chart partition-of-unity supports, exactly
as `exists_continuous_proportional_diffCurvOp` and the order-`0` curvature envelope
`exists_continuous_riemannOp_tensorCovS_frameEnergy_bound`). It is **`B`-uniform** because the frame
`B` enters the operator *only through the two contracted slots of the curvature operator* — `B_i` is
contracted twice (as the slot-`1` argument of the Riemann operator `R(B_iˣ, ·)` and as the slot-`0`
reading direction of the input) — so the `B`-dependence is the bounded curvature *magnitude*
(frame-energy-bounded by the curvature sup), not an unbounded frame jet; the per-order constant
absorbs `‖∇^{≤ p} R‖_∞`, finite by per-`p` compactness (no single scalar dominates all `p` since
`sup_p ‖∇^p R‖_∞ = ∞` on a generic closed metric). It is the genuinely-irreducible analytic primitive
of the frozen-frame jet tower, posited here as the precise atomic engine envelope; consumers
transitively depend on `sorryAx`.

**Discharge roadmap.** The order-`p = 0` layer is provable outright from existing public API (no new
posit): at rank `r = 0` the operator is `0` and the bound is trivial; at rank `r = m + 1`,
`pureRFrozenEndoFib g m B W x₀ = covGradBundleEquiv 0 m x₀ (∑ᵢ R(B_iˣ⁰, ·)(slot0_{B_iˣ⁰} W))`, whose
intrinsic fibre norm at `x₀` is, by the slot-`0` Parseval frame-sum
(`riemannianFiberNormSq_succ_eq_sum_slot0Curry_of_frame` over the `g_{x₀}`-orthonormal frame supplied
by `exists_orthonormal_frame_riemannianFiberNormSq`), the frame sum of the slice fibre norms of the
direction-CLM applied to the orthonormal directions; each slice (after the rank-`m` curry bridge
`tensor0S_curry ((covGradBundleEquiv 0 m x₀ Φ)(unit)) v = (Φ v)(unit)`, proved verbatim from the
generic-rank `covGradBundleEquiv_apply_eval`) is the curvature contraction
`∑ᵢ R(B_iˣ⁰, e_a)(slot0_{B_iˣ⁰} W)`, fibre-bounded by the rank-`m` curvature sup
(`exists_continuous_riemannianFiberNormSq_riemannOp_tensorCov_proportional`, supremised over compact
`M`) times the orthonormal Gram factors `g(B_iˣ⁰, B_iˣ⁰) = g(e_a, e_a) = 1`
(`smoothOrthoFrame_orthonormal_at_center`) times the slot-`0` reading fibre norm
`rfns((covGradBundleEquiv 0 m x₀).symm (W x₀) (B_iˣ⁰)))(x₀) ≤ rfns(W)(x₀)`
(`riemannianFiberNormSq_slot0Curry_le_of_frame` via `covGradBundleEquiv_symm_apply_eval`), giving
`kappa 0 = N·(N·Ccurv_sup m)`. The order-`p ≥ 1` layers read `∇^{≤ p}` of the centre frame at its own
centre `x₀`; the missing analytic input is the per-order *diagonal* frame-jet sup — the continuity on
the compact `M` of `x₀ ↦ ∇^{≤ p}(smoothOrthoFrame g x₀)-field(x₀)` (the joint (centre, base)
smoothness `smoothOrthoFrame_smooth` restricted to the diagonal), recorded as the sharp sub-node
`exists_uniform_smoothOrthoFrame_centre_jet_sup` — on top of which the `p ≥ 1` envelope follows by the
tower recursion `pureRFrozenDiffOp (p+1) = ∇(pureRFrozenDiffOp p) − cast` over the frame-jet and `∇R`
sups. The two layers combine into the single per-order `kappa`.

**Non-vacuity.** A degenerate witness `kappa ≡ 0` is rejected on any non-flat manifold: at `p = 0`,
some rank `r`, a centre `x₀` and a section `W` whose slot-`0` reading against the centre frame
`smoothOrthoFrame g x₀` carries a non-zero curvature contraction (`R(B_iˣ⁰, ·)(slot0_{B_iˣ⁰} W) ≠ 0`),
one has `rfns(pureRFrozenDiffOp g (smoothOrthoFrame g x₀) … 0 r W)(x₀) > 0` while
`kappa 0 r · rfns(W)(x₀) = 0` when `kappa 0 r = 0`. So the envelope must carry the genuine curvature
magnitude; it genuinely *uses* `W` (the operator is applied to `W`). -/
theorem exists_proportional_pureRFrozenFrameDiffOp (g : SmoothRiemannianMetric I M) :
    ∃ kappa : ℕ → ℕ → ℝ, (∀ p r, 0 ≤ kappa p r) ∧
      ∀ (p r : ℕ) (W : SmoothCcTensor g 0 r) (x₀ : M),
        riemannianFiberNormSq (I := I) (M := M) g 0 (r + p) x₀
            ((pureRFrozenDiffOp (I := I) (M := M) g (smoothOrthoFrame (I := I) g x₀)
              (fun i => smoothOrthoFrame_smooth (I := I) g x₀ i) p r W).toSection x₀) ≤
          kappa p r * riemannianFiberNormSq (I := I) (M := M) g 0 r x₀ (W.toSection x₀) := by
  sorry

/-- **The slot-`0` reading of the differentiated section `∇S` along `B_i` is the directional covariant
derivative `∇_{B_iˣ} S`.** `(covGradBundleEquiv 0 s x).symm ((covGrad g 0 s S).toSection x) (B_iˣ) =
covApply (tensorCov g 0 s) (B i) (S.toSection) x`. The covariant gradient's fibre is, by definition
(`covGrad_toSection_apply`), the slot-`0` uncurry `covGradBundleEquiv 0 s x` of the directional
covariant derivative CLM `tensorRSCovariantDerivative … (S.toSection) x = tensorCov g 0 s …`; the
inverse equivalence round-trips it back to that CLM, and `covApply` is its evaluation at `B_iˣ`. -/
private lemma pureRFrozenSlot0_covGrad_eq
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b) (x : M)
    (i : Fin (Module.finrank ℝ E)) :
    (covGradBundleEquiv (I := I) (M := M) 0 s x).symm
        ((covGrad (I := I) (M := M) g 0 s S).toSection x) (B i x) =
      covApply (tensorCov (I := I) g 0 s) (B i) (fun y : M => S.toSection y) x := by
  rw [covGrad_toSection_apply (I := I) (M := M) g 0 s S x,
    ContinuousLinearEquiv.symm_apply_apply]
  rfl

/-- **The bridge: the order-`0` frozen-frame curvature operator on `∇S` is the frozen-frame
pure-Riemann section.** `pureRFrozenDiffOp g B hB 0 (s + 1) (covGrad g 0 s S) = fixedFramePureRSection
g s S B hB`. Both sides are the slot-`0` uncurry (`covGradBundleEquiv 0 s x`) of a frozen-frame
pure-Riemann curvature direction CLM; the two CLMs agree summand-by-summand because the slot-`0`
reading of `∇S` is the directional covariant derivative `∇_{B_iˣ} S`
(`pureRFrozenSlot0_covGrad_eq`), which is exactly the contracted section of `pureRDirCLMFixedFrame`. -/
private lemma pureRFrozenDiffOp0_eq_fixedFramePureRSection
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b)
    (hB : ∀ i, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (B i))) :
    pureRFrozenDiffOp (I := I) (M := M) g B hB 0 (s + 1)
        (covGrad (I := I) (M := M) g 0 s S) =
      fixedFramePureRSection (I := I) (M := M) g s S B hB := by
  classical
  -- Both are `SmoothCcTensor`; compare their underlying sections fibrewise.
  refine SmoothCcTensor.ext (DFunLike.ext _ _ (fun x => ?_))
  -- LHS fibre = `pureRFrozenEndoFib g s B (∇S) x`; RHS fibre = `genuineCurvPureRFibFixedFrame`.
  change pureRFrozenEndoFib (I := I) (M := M) g s B (covGrad (I := I) (M := M) g 0 s S) x =
    (fixedFramePureRSection (I := I) (M := M) g s S B hB).toSection x
  rw [fixedFramePureRSection_toSection, pureRFrozenEndoFib, genuineCurvPureRFibFixedFrame]
  -- Reduce to equality of the two direction CLMs.
  refine congrArg (covGradBundleEquiv (I := I) (M := M) 0 s x) ?_
  refine ContinuousLinearMap.ext (fun v => ?_)
  rw [pureRFrozenDirCLM_apply, pureRDirCLMFixedFrame, ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [pureRDirCLMSummandFixedFrame, LinearMap.coe_toContinuousLinearMap', pureRDirLMSummandFixedFrame,
    LinearMap.coe_mk, AddHom.coe_mk, pureRFrozenSlot0_covGrad_eq (I := I) (M := M) g s S B x i]

/-- **Heterogeneous rank-congruence for `covGrad`.** If `h : a = b`, then `covGrad g 0 a Y` and
`covGrad g 0 b Z` are heterogeneously equal whenever `Y, Z` are. -/
private theorem covGrad_heq_congr_tw (g : SmoothRiemannianMetric I M) {a b : ℕ}
    (h : a = b) {Y : SmoothCcTensor g 0 a} {Z : SmoothCcTensor g 0 b} (hYZ : HEq Y Z) :
    HEq (covGrad (I := I) (M := M) g 0 a Y) (covGrad (I := I) (M := M) g 0 b Z) := by
  subst h
  rw [eq_of_heq hYZ]

/-- **Heterogeneous commuting of one covariant gradient through the iterated gradient.** Applying `q`
covariant gradients to `covGrad g 0 s X` is heterogeneously equal to the `(q + 1)`-fold iterated
gradient of `X`; the two live in ranks `(s + 1) + q` and `s + (q + 1)`, which agree as naturals. -/
private theorem iteratedCovGrad_covGrad_comm_heq_tw (g : SmoothRiemannianMetric I M)
    (s q : ℕ) (X : SmoothCcTensor g 0 s) :
    HEq (iteratedCovGrad g 0 (s + 1) q (covGrad (I := I) (M := M) g 0 s X))
      (iteratedCovGrad g 0 s (q + 1) X) := by
  induction q with
  | zero =>
      rw [iteratedCovGrad_zero, iteratedCovGrad_succ, iteratedCovGrad_zero]
      exact HEq.rfl
  | succ k ih =>
      rw [iteratedCovGrad_succ (g := g) (r := 0) (s := s + 1) (j := k)
        (covGrad (I := I) (M := M) g 0 s X)]
      rw [iteratedCovGrad_succ (g := g) (r := 0) (s := s) (j := k + 1) X]
      exact covGrad_heq_congr_tw g (by omega : (s + 1) + k = s + (k + 1)) ih

/-- **The intrinsic fibre norm is invariant under a `SmoothCcTensor` rank-cast.** Heterogeneously
equal smooth compactly-supported tensors over agreeing ranks have equal section-value
`riemannianFiberNormSq` at every point. -/
private theorem rfns_toSection_heq_congr_tw (g : SmoothRiemannianMetric I M)
    {a b : ℕ} (h : a = b) {Y : SmoothCcTensor g 0 a} {Z : SmoothCcTensor g 0 b}
    (hYZ : HEq Y Z) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g 0 a x (Y.toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g 0 b x (Z.toSection x) := by
  subst h
  rw [eq_of_heq hYZ]

/-- **Front-commuting one covariant gradient through the iterated gradient (rfns form).** The
intrinsic squared fibre norm of `∇^q(∇S)` at `x` equals that of `∇^{q + 1}S`. The rank reassociation
`(s + 1) + q = s + (q + 1)` is invisible to the intrinsic fibre norm. -/
private theorem rfns_iteratedCovGrad_covGrad_comm_tw (g : SmoothRiemannianMetric I M)
    (s q : ℕ) (S : SmoothCcTensor g 0 s) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g 0 ((s + 1) + q) x
        ((iteratedCovGrad g 0 (s + 1) q (covGrad (I := I) (M := M) g 0 s S)).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g 0 (s + (q + 1)) x
        ((iteratedCovGrad g 0 s (q + 1) S).toSection x) :=
  rfns_toSection_heq_congr_tw g (by omega : (s + 1) + q = s + (q + 1))
    (iteratedCovGrad_covGrad_comm_heq_tw (I := I) (M := M) g s q S) x

/-- **The frozen-frame pure-Riemann curvature-jet grid bound at the centre frame (the `(p, w) = (1, 1)`
headline).** For a closed smooth Riemannian manifold `(M, g)` there is a *valence/order-dependent*
nonnegative constant family `c : ℕ → ℕ → ℝ`, **uniform over the centre `x`**, such that at every
covariant rank `s`, smooth compactly-supported `(0, s)`-tensor `S`, gradient order `k`, and centre
`x`, the `k`-fold iterated covariant gradient of the frozen-frame pure-Riemann section against the
*centre frame* `smoothOrthoFrame g x`, evaluated at its own centre `x`, is fibre-bounded by

```
rfns(∇^k (fixedFramePureRSection g s S (smoothOrthoFrame g x)))(x)
  ≤ (c s k)² · ∑_{i < 1 + k} rfns(∇^{i + 1} S)(x).
```

This is the order-`1`/width-`1` centre-frame graded curvature-jet bound the moving-centre
curvature-jet induction (`OrderSeparatedCurvatureJet.GcurvSection_gradedCurvJet`, via the locality
transfer at each centre `x`) consumes. It is **proved** by the at-centre differentiated-bilinear-
contraction single-sum grid `DiffBilinOp.exists_rfns_iteratedCovGrad_singleSum_le_at` applied to the
frozen-frame curvature tower (`op := pureRFrozenDiffOp g (smoothOrthoFrame g x) …`, whose `covGrad_op`
Leibniz is *proved* by `covGrad_pureRFrozenDiffOp_eq`, whose centre-uniform at-centre envelope is the
single posited primitive `exists_proportional_pureRFrozenFrameDiffOp`), the bridge
`pureRFrozenDiffOp0_eq_fixedFramePureRSection` (the order-`0` operator on `∇S` is the frozen-frame
section), and the rank-shift `∇^q(∇S) ≅ ∇^{q + 1}S` (`rfns_iteratedCovGrad_covGrad_comm_tw`) collapsing
the contracted-order range `0 … k` of `∇S` to `1 … 1 + k` of `S`. The constant family is the engine's
single-sum constant `c s k := √(4^k · gridWindowSum kappa 0 (s + 1) k)` — the `4^k`-scaled order × rank
window sum over orders `[0, k]` and ranks `[s + 1, s + 1 + k]` (square-rooted to match the graded
predicate's squared multiplier), centre-uniform because the posited per-rank envelope `kappa` is. It
genuinely depends on the source rank `s` through the base rank `s + 1` of the rank window, since the
rank-`m` curvature derivation's fibre-operator constant grows with `m`.

**Restatement note.** This is the centre-frame restriction of the former free-frame `∀ B, x` form,
required because the underlying envelope is true only at the centre frame at its own centre (the
free-frame form is FALSE — quadratic in the frame, no scale bound). The sole consumer
(`GcurvSection_gradedCurvJet`) instantiates the free form only at `B = smoothOrthoFrame g x`, `x`, so
no downstream generality is lost.

**Non-vacuity.** With `c s 0 = 0` the bound forces `rfns(fixedFramePureRSection g s S
(smoothOrthoFrame g x))(x) = 0` at `k = 0`, i.e. the pure-Riemann contraction
`∑ᵢ R(B_iˣ, ·)(∇_{B_iˣ} S)` vanishes; false on a non-flat manifold (`R ≠ 0`) for a non-parallel `S`
(`∇S ≠ 0`). The constant family is genuinely positive. -/
theorem exists_fixedFramePureRSection_iteratedCovGrad_grid_bound (g : SmoothRiemannianMetric I M) :
    ∃ c : ℕ → ℕ → ℝ, (∀ s k, 0 ≤ c s k) ∧
      ∀ (s : ℕ) (S : SmoothCcTensor g 0 s) (k : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g 0 ((s + 1) + k) x
            ((iteratedCovGrad g 0 (s + 1) k
              (fixedFramePureRSection (I := I) (M := M) g s S
                (smoothOrthoFrame (I := I) g x)
                (fun i => smoothOrthoFrame_smooth (I := I) g x i))).toSection x) ≤
          (c s k) ^ 2 * ∑ i ∈ Finset.range (1 + k),
            riemannianFiberNormSq (I := I) (M := M) g 0 (s + (i + 1)) x
              ((iteratedCovGrad g 0 s (i + 1) S).toSection x) := by
  classical
  obtain ⟨kappa, hkappa_nn, hkappa⟩ := exists_proportional_pureRFrozenFrameDiffOp (I := I) (M := M) g
  -- The engine's single-sum constant `4^k · gridWindowSum kappa 0 (s + 1) k` (the `4^k`-scaled order ×
  -- rank window sum over orders `[0, k]` and ranks `[s + 1, s + 1 + k]`), centre-uniform (no opaque
  -- existential): square-root it to match the graded predicate's squared multiplier. The constant now
  -- genuinely depends on the source rank `s` through the base rank `s + 1` of the rank window — the
  -- per-rank curvature-operator constant.
  refine ⟨fun s' k => Real.sqrt ((4 : ℝ) ^ k * gridWindowSum kappa 0 (s' + 1) k),
    fun _ k => Real.sqrt_nonneg _, fun s S k x => ?_⟩
  have hcsq : (Real.sqrt ((4 : ℝ) ^ k * gridWindowSum kappa 0 (s + 1) k)) ^ 2 =
      (4 : ℝ) ^ k * gridWindowSum kappa 0 (s + 1) k := by
    rw [Real.sq_sqrt]
    exact mul_nonneg (by positivity) (gridWindowSum_nonneg hkappa_nn 0 (s + 1) k)
  rw [hcsq]
  -- The at-centre single-sum grid for the frozen-frame tower at the centre frame `smoothOrthoFrame g x`
  -- evaluated at its own centre `x`, base rank `s + 1`, section `∇S`, gradient order `k`. The pointwise
  -- (per-rank) envelope hypothesis at `x₀ := x` is exactly the centre-uniform at-centre envelope
  -- `hkappa … x`.
  have hgrid := DifferentialGeometry.Integral.Connection.DiffBilinOp.exists_rfns_iteratedCovGrad_singleSum_le_at
    (g := g)
    (op := fun p r W => pureRFrozenDiffOp (I := I) (M := M) g (smoothOrthoFrame (I := I) g x)
      (fun i => smoothOrthoFrame_smooth (I := I) g x i) p r W)
    (fun p r W => covGrad_pureRFrozenDiffOp_eq (I := I) (M := M) g (smoothOrthoFrame (I := I) g x)
      (fun i => smoothOrthoFrame_smooth (I := I) g x i) p r W)
    kappa hkappa_nn x
    (fun p r W => hkappa p r W x)
    (s + 1) (covGrad (I := I) (M := M) g 0 s S) k
  -- The operator value `op 0 (s + 1) (∇S)` is the frozen-frame section against the centre frame.
  rw [show pureRFrozenDiffOp (I := I) (M := M) g (smoothOrthoFrame (I := I) g x)
        (fun i => smoothOrthoFrame_smooth (I := I) g x i) 0 (s + 1)
        (covGrad (I := I) (M := M) g 0 s S) =
      fixedFramePureRSection (I := I) (M := M) g s S (smoothOrthoFrame (I := I) g x)
        (fun i => smoothOrthoFrame_smooth (I := I) g x i) from
    pureRFrozenDiffOp0_eq_fixedFramePureRSection (I := I) (M := M) g s S
      (smoothOrthoFrame (I := I) g x) (fun i => smoothOrthoFrame_smooth (I := I) g x i)] at hgrid
  refine hgrid.trans (le_of_eq ?_)
  -- Re-index `∇^q(∇S) ≅ ∇^{q + 1}S` and match the contracted-order range.
  refine congrArg (fun t => ((4 : ℝ) ^ k * gridWindowSum kappa 0 (s + 1) k) * t) ?_
  rw [Nat.add_comm 1 k]
  refine Finset.sum_congr rfl (fun q _ => ?_)
  exact rfns_iteratedCovGrad_covGrad_comm_tw (I := I) (M := M) g s q S x

end Connection
end Integral
end DifferentialGeometry

end
