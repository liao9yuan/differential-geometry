import DifferentialGeometry.Geometry.Connection.TensorNabla.OperatorFieldCovariantCalculus
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.FixedFieldThirdOrderCommutator
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.GradientSlotCurvatureSplit
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.BracketDivergenceForm
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.FrozenFramePureRCurvatureTower
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.RicciTraceCarrier
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.NablaRicciTraceCarrier
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.NablaRicciTraceIBP
import DifferentialGeometry.Geometry.Curvature.FiberNormParseval.ParsevalLaplacianSlot0Expansion
import DifferentialGeometry.Geometry.Curvature.FiberNormParseval.ParsevalFrameField
import DifferentialGeometry.Geometry.Curvature.Bochner.PointwiseTensorBochner
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.GreenIdentityAndIBP.TensorConnLapGreenIntertwiner
import DifferentialGeometry.Geometry.Curvature.Order2Defect.GradientSlotLeibniz
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.OperatorFieldPairingIBP
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.ContractedBianchi
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.DifferentiatedSlotwiseCurvature
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.DifferentiatedRicciEndomorphism
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.ParsevalFrameDiffCurvatureTrace
import DifferentialGeometry.Geometry.Connection.MetricCompatibility.TensorRSMetricCompatible
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.GradientField
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.SlotOperatorCarrierCalculus

/-!
# The seven-term Bochner fold: fixed-Parseval-family group carriers of the rank-`0` Bochner–Weitzenböck assembly

For a closed smooth Riemannian manifold `(M, g)`, covariant rank `s`, a smooth compactly-supported
`(0, s)`-tensor `S`, and a fixed Parseval frame family of smooth global tangent fields `V a`
(`exists_smooth_parseval_frame_family`), this file packages the four **group→carrier folds** through which
the rank-`0` integrated Bochner–Weitzenböck nullity assembles.

The per-fixed-field third-order carrier identity
`secondCovDeriv_covGrad_sub_covGrad_secondCovDeriv_slot0_eq` (`FixedFieldThirdOrderCommutator`) writes the
slot-`0` `V b`-read of `∇²_{V a, V a}(∇S) − ∇(∇²_{V a, V a} S)` as a seven-term curvature carrier
combination.  Reading each carrier against the slot-`0` curry `slot0_{V b}(∇S)` and double-summing/integrating
over the Parseval family `(a, b)` partitions those seven terms into four named carrier groups
(`bochnerFoldGroupSum` of `bochnerGroupElt1` … `bochnerGroupElt4`).

**Which group-level statements are admissible (the dim ≥ 3 per-group refutation, 2026-06-12).**
Assigning an individual gauge-invariant value to a single Bochner-fold group is FALSE in dimension
≥ 3 (`PROVE_REFUTED.md`, "Kernel per-group VALUE-ASSIGNMENT family"): an `S³` rotation family
evaluates the former per-group folds `G₃ = ⟨ricTraceSection, ∇S⟩` and `G₂ + G₄ = operator residue`
with a common nonzero error `±N` (`N(t) = −0.115184482·t`, three independent computations in 9-digit
agreement), and an ellipsoid evaluates the formerly posited `D = group2 − group1` to `+6.125 ≠ 0`
against the forced `0`.  The formerly public per-group folds (`bochnerFold_group3_eq_ricTrace`,
`bochnerFold_group2_add_group4_eq_operatorResidue`) and the whole per-`b` / `b`-summed
tension-field-nullity tower were therefore DELETED; the group-`1` fold survives because its value is
pointwise-Parseval (a pointwise slot identity, not an integrated cancellation).  What remains:

* `bochnerFold_group1_eq_GcurvSection` — fold `1`, sorry-free (pointwise-Parseval value);
* `bochnerFold_sevenTermSum_eq_pointwiseTensorCurvPairing` — the fixed-family bridge
  `⟨Curv S, ∇S⟩_{L²} = G₁ + G₂ + G₃ + G₄`, sorry-free;
* `bochnerFoldGroupSum_elt2_eq_residueSum` / `bochnerGroupElt2_perB_integral_eq_residueSum` — the
  frame-summed covariant-IBP engine identities, sorry-free (both sides carry matching gauge
  variance);
* `bochnerFoldGroupSum_elt3_eq_iiiIvSum_add_ricTrace` — the variance-honest group-`3` decomposition
  `G₃ = bochnerFoldGroupSum (bochnerGroupElt3IiiIv) + ⟨ricTraceSection g s S, ∇S⟩_{L²}`, sorry-free:
  the gauge-variant tension-field double sum stays explicit and is never equated to an invariant
  value;
* `parsevalFrameSum_group2_add_group3_add_group4_eq_curv_sub_gcurv` — the admissible summed fold
  `G₂ + G₃ + G₄ = ⟨Curv S, ∇S⟩ − ⟨GcurvSection g s S, ∇S⟩`, sorry-free over the seven-term and
  group-`1` folds (no per-group value step);
* `parsevalFrameSum_diffCurvTrace_doubleSum_eq_neg_group1_add_crossPairing` — **the proven
  `∇R`-vs-`∇S` primitive `D = −(G₁ + I₂)`**: the diagonal differentiated-curvature trace double sum
  `D := ∑_a ∑_b ∫ ⟨(∇_{V a} R^{(s)})(V a, V b) S, ∇_{V b} S⟩` equals the negated sum of the
  group-`1` pairing and the genuine-Hessian cross pairing
  `I₂ := ∑_a ∑_b ∫ ⟨R(V a, V b) S, ∇²_{V a, V b} S⟩` — the integrated `∇R`-vs-`∇S` covariant
  integration by parts, **sorry-free** through the Parseval covariant-derivative pair antisymmetry,
  the `riemannOp` slot antisymmetry, and the Parseval covariant divergence trace;
* `parsevalFrameSum_group4_sub_crossPairing_eq_curv_sub_gcurv_sub_ricTrace` — the summed chain over
  the primitive: `G₄ − I₂ = ⟨Curv S, ∇S⟩ − ⟨GcurvSection, ∇S⟩ − ⟨ricTraceSection, ∇S⟩`, sorry-free
  through the covariant-Leibniz split `bochnerFoldGroupSum_elt3IiiIv_eq_nablaDiffCurvTrace_split`
  and the group-`3` decomposition;
* `bochnerFoldGroupSum_elt4_eq_zero` — **the group-`4` fold vanishes (`G₄ = 0`)**, sorry-free:
  the genuine Hessian is value-bilinear in its two direction slots
  (`tensorSecondCovDeriv_unit_eq_twoSlotCurry`), so the symmetric second-order pair is killed
  pointwise by the cometric-parallel covariant-derivative pair antisymmetry (a pointwise-Parseval
  value, admissible like the group-`1` fold);
* `tensorL2Inner_genuineDiffCurv_covGrad_eq_neg_threeTerm` — the sorry-free B-rule/IBP normal
  form of the operator-field pairing,
  `⟨appCc (covGrad Φ₀) S, ∇S⟩ = −∑_b ∫ [⟨P, ∇_b∇_b S⟩ + ⟨P, ∇_b S⟩·divᵍ V_b + ⟨Φ₀(∇_b S), ∇_b S⟩]`
  (`P := appCc Φ₀ S`), through `fold_assembly_perB`, the spectator slot-read
  `spectatorSlot0_eq_appCc_gradSlot`, and the per-direction IBP `integral_covApplyPair_IBP`;
* `tensorL2Inner_genuineDiffCurv_covGrad_eq_group4_sub_crossPairing` — **the posited
  differentiated-curvature operator-field identification** (the only `sorry` in this file): the
  frame-free operator-field pairing `⟨appCc (covGrad Φ₀) S, ∇S⟩_{L²}` (`Φ₀ := curvOpField g s`)
  equals the gauge-cancelling difference combination `G₄ − I₂` of the Parseval fold; over the
  proven `G₄ = 0` and the three-term normal form, the remaining content is the integrated
  second-Bianchi cross pairing (see the posit's docstring for the landed route);
* `tensorL2Inner_genuineDiffCurv_covGrad_eq_curv_sub_gcurv_sub_ricTrace` — the frame-free reading of
  the chain: `⟨appCc (covGrad Φ₀) S, ∇S⟩ = ⟨Curv S, ∇S⟩ − ⟨GcurvSection, ∇S⟩ − ⟨ricTraceSection,
  ∇S⟩`, sorry-free glue over the operator-field posit through the summed chain endpoint and a
  Parseval frame family witness (`exists_smooth_parseval_frame_family`).

The frame-free corollary is what the three-section curvature value
`bochnerWeitzenbock_threeSection_curvatureValue_posit` (`MovingFrameRemainderFrameSumBridge`, glued
over this file) consumes; the `L²` B-rule split and the residue-form extraction
`tensorL2Inner_curv_covGrad_eq_gcurvRicOperatorResidue_value` live downstream in
`CurvatureCovGradResidueValue`. Consumers transitively depend on the operator-field posit's
`sorryAx`.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
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
private local instance : NormedSpace ℝ E := InnerProductSpace.toNormedSpace

set_option backward.isDefEq.respectTransparency false in
/-- The slot-`0` curry read of `∇S = covGrad g 0 s S` in the fixed Parseval direction `V b`, as a
`TensorRSSpace 0 s`. -/
def bochnerGradSlot0 (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s)
    (Vb : Π b : M, TangentSpace I b) (x : M) : TensorRSSpace 0 s I x :=
  tensor0SAsRS (I := I) (M := M) x
    ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x
      ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
        (covGrad (I := I) (M := M) g 0 s S).toSection x)
        (unitZeroSec (I := I) (M := M) x))) (Vb x))

set_option backward.isDefEq.respectTransparency false in
/-- Group `1` carrier (term i of the seven-term identity), `R(V a, V b)(∇_{V a} S)` read on the unit, in
direction-`V a`/read-`V b`, as a `TensorRSSpace 0 s`. -/
def bochnerGroupElt1 (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s)
    (Va Vb : Π b : M, TangentSpace I b) (x : M) : TensorRSSpace 0 s I x :=
  tensor0SAsRS (I := I) (M := M) x
    ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
        riemannSec (tensorCov (I := I) g 0 s) Va Vb
          (covApply (tensorCov (I := I) g 0 s) Va (fun y : M => S.toSection y)) x)
        (unitZeroSec (I := I) (M := M) x))

set_option backward.isDefEq.respectTransparency false in
/-- Group `2` carrier (term ii), `∇_{V a}(R(V a, V b) S)` read on the unit. -/
def bochnerGroupElt2 (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s)
    (Va Vb : Π b : M, TangentSpace I b) (x : M) : TensorRSSpace 0 s I x :=
  tensor0SAsRS (I := I) (M := M) x
    ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
        covApply (tensorCov (I := I) g 0 s) Va
          (fun y : M => riemannSec (tensorCov (I := I) g 0 s) Va Vb
            (fun z : M => S.toSection z) y) x)
        (unitZeroSec (I := I) (M := M) x))

set_option backward.isDefEq.respectTransparency false in
/-- Group `3` carrier (terms iii + iv − v): `R(∇_{V a} V b, V a) S + R(V b, ∇_{V a} V a) S −
∇_{R(V a, V b) V a} S`, read on the unit. -/
def bochnerGroupElt3 (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s)
    (Va Vb : Π b : M, TangentSpace I b) (x : M) : TensorRSSpace 0 s I x :=
  tensor0SAsRS (I := I) (M := M) x
    ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
        riemannOp (tensorCov (I := I) g 0 s) x
          ((LeviCivita (I := I) g).toFun Vb x (Va x)) (Va x) (S.toSection x))
        (unitZeroSec (I := I) (M := M) x) +
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
        riemannOp (tensorCov (I := I) g 0 s) x (Vb x)
          ((LeviCivita (I := I) g).toFun Va x (Va x)) (S.toSection x))
        (unitZeroSec (I := I) (M := M) x) -
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
        (tensorCov (I := I) g 0 s).toFun (fun y : M => S.toSection y) x
          (riemannOp (LeviCivita (I := I) g) x (Va x) (Vb x) (Va x)))
        (unitZeroSec (I := I) (M := M) x))

set_option backward.isDefEq.respectTransparency false in
/-- Group `4` carrier (− term vi − term vii, the symmetric second-order pair):
`−∇²_{∇_{V b} V a, V a} S − ∇²_{V a, ∇_{V b} V a} S`, read on the unit. -/
def bochnerGroupElt4 (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s)
    (Va Vb : Π b : M, TangentSpace I b) (x : M) : TensorRSSpace 0 s I x :=
  tensor0SAsRS (I := I) (M := M) x
    (- (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
        tensorSecondCovDeriv (I := I) g 0 s
          (fun y : M => (LeviCivita (I := I) g).toFun Va y (Vb y)) Va
          (fun y : M => S.toSection y) x)
        (unitZeroSec (I := I) (M := M) x) -
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
        tensorSecondCovDeriv (I := I) g 0 s Va
          (fun y : M => (LeviCivita (I := I) g).toFun Va y (Vb y))
          (fun y : M => S.toSection y) x)
        (unitZeroSec (I := I) (M := M) x))

/-- The group-`k` double-sum carrier: the Parseval double sum over `(a, b)` of the integral over the closed
manifold of the pointwise `(0, s)` pairing of the group-`k` carrier against the slot-`0` curry of `∇S`. -/
def bochnerFoldGroupSum (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s)
    {N : ℕ} (V : Fin N → Π b : M, TangentSpace I b)
    (Elt : (Π b : M, TangentSpace I b) → (Π b : M, TangentSpace I b) → (x : M) →
      TensorRSSpace 0 s I x) : ℝ :=
  ∑ a : Fin N, ∑ b : Fin N,
    ∫ x, tensorInnerPointwise (I := I) (M := M) g 0 s x
        (TensorRSSpace.toModel (Elt (V a) (V b) x))
        (TensorRSSpace.toModel (bochnerGradSlot0 (I := I) (M := M) g s S (V b) x))
      ∂(riemannianVolumeMeasure (I := I) (M := M) g)

set_option linter.unusedSectionVars false in
/-- **The fixed-family Parseval representation of the order-`2` commutator defect.** For a fixed global
smooth Parseval frame family `V a`, the section value of `pointwiseTensorCurv g s S = Δ_∇(∇S) − ∇(Δ_∇ S)`
at `x` is the fixed-family sum of the per-direction third-order differences
`∇²_{V_a, V_a}(∇S) − ∇(∇²_{V_a, V_a} S)`, both packaged through `secondCovDerivCc`:
```
pointwiseTensorCurv g s S (x) = ∑_a [secondCovDerivCc g (s+1) (∇S) (x) − ∇(secondCovDerivCc g s S) (x)].
```
Both legs are the fixed-family Parseval trace of the rough Laplacian
(`rawTensorConnLapSmooth_toSection_eq_parseval_secondCovDeriv_sum`); the second leg pushes the covariant
gradient through the finite frame sum by `covGrad_add`. -/
private lemma pointwiseTensorCurv_parsevalSum_aux
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s)
    {N : ℕ} (V : Fin N → Π b : M, TangentSpace I b)
    (hV : ∀ a, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => (⟨b, V a b⟩ : TotalSpace E (TangentSpace I))))
    (hPar : ∀ (x : M) (u : TangentSpace I x),
      (∑ a : Fin N, g.inner x (V a x) u • V a x) = u) (x : M) :
    (pointwiseTensorCurv (I := I) (M := M) g s S).toSection x =
      ∑ a : Fin N,
        ((secondCovDerivCc (I := I) (M := M) g (s + 1) (hV a)
            (covGrad (I := I) (M := M) g 0 s S)).toSection x -
          (covGrad (I := I) (M := M) g 0 s
            (secondCovDerivCc (I := I) (M := M) g s (hV a) S)).toSection x) := by
  classical
  rw [show (pointwiseTensorCurv (I := I) (M := M) g s S) =
      rawTensorConnLapSmooth (I := I) g 0 (s + 1) (covGrad (I := I) (M := M) g 0 s S) -
        covGrad (I := I) (M := M) g 0 s (rawTensorConnLapSmooth (I := I) g 0 s S) from rfl]
  rw [SmoothCcTensor.toSection_sub]
  rw [show ((rawTensorConnLapSmooth (I := I) g 0 (s + 1)
          (covGrad (I := I) (M := M) g 0 s S)).toSection -
        (covGrad (I := I) (M := M) g 0 s
          (rawTensorConnLapSmooth (I := I) g 0 s S)).toSection) x =
      (rawTensorConnLapSmooth (I := I) g 0 (s + 1)
          (covGrad (I := I) (M := M) g 0 s S)).toSection x -
        (covGrad (I := I) (M := M) g 0 s
          (rawTensorConnLapSmooth (I := I) g 0 s S)).toSection x from rfl]
  -- The Δ_∇(∇S) leg.
  rw [rawTensorConnLapSmooth_toSection_apply,
    rawTensorConnLapSmooth_toSection_eq_parseval_secondCovDeriv_sum
      (I := I) (M := M) g V hV hPar (s + 1) (covGrad (I := I) (M := M) g 0 s S) x]
  -- The ∇(Δ_∇ S) leg, at the section level (no `ContMDiffSection.ext`).
  rw [covGrad_toSection_apply (I := I) (M := M) g 0 s
    (rawTensorConnLapSmooth (I := I) g 0 s S) x]
  rw [show (fun y : M => (rawTensorConnLapSmooth (I := I) g 0 s S).toSection y) =
      (fun y : M => ∑ a : Fin N, tensorSecondCovDeriv (I := I) g 0 s (V a) (V a)
        (fun z : M => S.toSection z) y) from by
    funext y
    rw [rawTensorConnLapSmooth_toSection_apply]
    exact rawTensorConnLapSmooth_toSection_eq_parseval_secondCovDeriv_sum
      (I := I) (M := M) g V hV hPar s S y]
  have hσ : ∀ a : Fin N,
      MDifferentiableAt I (I.prod 𝓘(ℝ, TensorRSModel 0 s ℝ E))
        (fun y : M => TotalSpace.mk' (TensorRSModel 0 s ℝ E)
          (E := fun z : M => TensorRSSpace 0 s I z) y
          (tensorSecondCovDeriv (I := I) g 0 s (V a) (V a)
            (fun z : M => S.toSection z) y)) x :=
    fun a => (tensorSecondCovDeriv_section_contMDiff (I := I) g 0 s
      S.toSection.contMDiff (hV a)).mdifferentiable (by norm_num) x
  rw [tensorCov_toFun_finset_sum (I := I) g 0 s Finset.univ
    (fun a (y : M) => tensorSecondCovDeriv (I := I) g 0 s (V a) (V a)
      (fun z : M => S.toSection z) y) hσ]
  rw [map_sum (covGradBundleEquiv (I := I) (M := M) 0 s x) _ _]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [secondCovDerivCc_toSection_apply]
  rw [covGrad_toSection_apply (I := I) (M := M) g 0 s
    (secondCovDerivCc (I := I) (M := M) g s (hV a) S) x]
  congr 2

set_option linter.unusedSectionVars false in
/-- The scalar-extraction functional evaluates to `1` on the unit `(0, 0)`-tensor. -/
private lemma tensor00Scalar_unitZeroSec' (x : M) :
    tensor00Scalar (I := I) (M := M) x (unitZeroSec (I := I) (M := M) x) = 1 := by
  rw [tensor00Scalar_apply (I := I) (M := M) x _ (fun k : Fin 0 => k.elim0)]
  rw [show ((unitZeroSec (I := I) (M := M) x) (fun k : Fin 0 => k.elim0) : ℝ) =
      Tensor0SSpace.toModel (unitZeroSec (I := I) (M := M) x) (fun k : Fin 0 => k.elim0) from rfl]
  rw [unitZeroSec_apply (I := I) (M := M) x, Tensor0SSpace.toModel_ofModel,
    ContinuousMultilinearMap.constOfIsEmpty_apply]

set_option linter.unusedSectionVars false in
/-- Reading the unit-evaluation of a `(0, t)`-Hom-tensor through `tensor0SAsRS` reconstructs it. -/
private lemma tensor0SAsRS_rs_unit' (t : ℕ) (x : M) (W : TensorRSSpace 0 t I x) :
    tensor0SAsRS (I := I) (M := M) x
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace t I x from W)
          (unitZeroSec (I := I) (M := M) x)) = W := by
  apply tensorRSSpace_ext (𝕜 := ℝ) 0 t x
  intro τ
  rw [show (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace t I x from
        tensor0SAsRS (I := I) (M := M) x
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace t I x from W)
            (unitZeroSec (I := I) (M := M) x))) τ =
      tensor00Scalar (I := I) (M := M) x τ •
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace t I x from W)
          (unitZeroSec (I := I) (M := M) x)) from
    tensor0SAsRS_apply (I := I) (M := M) x _ τ]
  conv_rhs => rw [zeroTensor_eq_smul_unit (I := I) (M := M) x τ]
  rw [ContinuousLinearMap.map_smul]
  congr 1

set_option linter.unusedSectionVars false in
/-- The unit-evaluation of the `tensor0SAsRS`-wrapped `(0, t)`-tensor recovers it. -/
private lemma tensor0SAsRS_unit_eval' (t : ℕ) (x : M) (C : Tensor0SSpace t I x) :
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace t I x from
        tensor0SAsRS (I := I) (M := M) x C)
      (unitZeroSec (I := I) (M := M) x) = C := by
  rw [show (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace t I x from
        tensor0SAsRS (I := I) (M := M) x C)
      (unitZeroSec (I := I) (M := M) x) =
      tensor00Scalar (I := I) (M := M) x (unitZeroSec (I := I) (M := M) x) • C from
    tensor0SAsRS_apply (I := I) (M := M) x C (unitZeroSec (I := I) (M := M) x)]
  rw [tensor00Scalar_unitZeroSec' (I := I) (M := M) x, one_smul]

set_option linter.unusedSectionVars false in
/-- Two `tensor0SAsRS`-wrapped `(0, s)`-tensors are equal iff their wrapped values are. -/
private lemma tensor0SAsRS_eq_iff {s : ℕ} {x : M} {C D : Tensor0SSpace s I x} :
    tensor0SAsRS (I := I) (M := M) x C = tensor0SAsRS (I := I) (M := M) x D ↔ C = D := by
  constructor
  · intro h
    calc C = (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
                tensor0SAsRS (I := I) (M := M) x C) (unitZeroSec (I := I) (M := M) x) :=
            (tensor0SAsRS_unit_eval' (I := I) (M := M) s x C).symm
      _ = (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
                tensor0SAsRS (I := I) (M := M) x D) (unitZeroSec (I := I) (M := M) x) := by rw [h]
      _ = D := tensor0SAsRS_unit_eval' (I := I) (M := M) s x D
  · intro h; rw [h]

set_option linter.unusedSectionVars false in
/-- The `(0, t)`-tensor wrapper sends `0` to `0`. -/
private lemma tensor0SAsRS_zero (t : ℕ) (x : M) :
    tensor0SAsRS (I := I) (M := M) x (0 : Tensor0SSpace t I x) = 0 := by
  apply tensorRSSpace_ext (𝕜 := ℝ) 0 t x
  intro τ
  rw [show (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace t I x from
        tensor0SAsRS (I := I) (M := M) x (0 : Tensor0SSpace t I x)) τ =
      tensor00Scalar (I := I) (M := M) x τ • (0 : Tensor0SSpace t I x) from
    tensor0SAsRS_apply (I := I) (M := M) x _ τ]
  rw [smul_zero]
  rfl

set_option linter.unusedSectionVars false in
/-- The `(0, t)`-tensor wrapper is additive. -/
private lemma tensor0SAsRS_add (t : ℕ) (x : M) (C D : Tensor0SSpace t I x) :
    tensor0SAsRS (I := I) (M := M) x (C + D) =
      tensor0SAsRS (I := I) (M := M) x C + tensor0SAsRS (I := I) (M := M) x D := by
  apply tensorRSSpace_ext (𝕜 := ℝ) 0 t x
  intro τ
  rw [show (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace t I x from
        tensor0SAsRS (I := I) (M := M) x (C + D)) τ =
      tensor00Scalar (I := I) (M := M) x τ • (C + D) from
    tensor0SAsRS_apply (I := I) (M := M) x _ τ]
  rw [show (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace t I x from
        tensor0SAsRS (I := I) (M := M) x C + tensor0SAsRS (I := I) (M := M) x D) τ =
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace t I x from
        tensor0SAsRS (I := I) (M := M) x C) τ +
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace t I x from
        tensor0SAsRS (I := I) (M := M) x D) τ from rfl]
  rw [show (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace t I x from
        tensor0SAsRS (I := I) (M := M) x C) τ =
      tensor00Scalar (I := I) (M := M) x τ • C from
    tensor0SAsRS_apply (I := I) (M := M) x _ τ]
  rw [show (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace t I x from
        tensor0SAsRS (I := I) (M := M) x D) τ =
      tensor00Scalar (I := I) (M := M) x τ • D from
    tensor0SAsRS_apply (I := I) (M := M) x _ τ]
  rw [smul_add]

set_option linter.unusedSectionVars false in
/-- The `(0, t)`-tensor wrapper distributes over a finite sum. -/
private lemma tensor0SAsRS_finsetSum (t : ℕ) (x : M) {ι : Type*} (fs : Finset ι)
    (C : ι → Tensor0SSpace t I x) :
    tensor0SAsRS (I := I) (M := M) x (∑ i ∈ fs, C i) =
      ∑ i ∈ fs, tensor0SAsRS (I := I) (M := M) x (C i) := by
  classical
  induction fs using Finset.induction with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, tensor0SAsRS_zero]
  | insert i fs hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, ← ih, tensor0SAsRS_add]

set_option linter.unusedSectionVars false in
/-- The `(0, t)`-tensor wrapper negates. -/
private lemma tensor0SAsRS_neg (t : ℕ) (x : M) (C : Tensor0SSpace t I x) :
    tensor0SAsRS (I := I) (M := M) x (- C) = - tensor0SAsRS (I := I) (M := M) x C := by
  have h : tensor0SAsRS (I := I) (M := M) x (- C) +
      tensor0SAsRS (I := I) (M := M) x C = 0 := by
    rw [← tensor0SAsRS_add, neg_add_cancel, tensor0SAsRS_zero]
  linear_combination (norm := module) h

set_option linter.unusedSectionVars false in
/-- The `(0, t)`-tensor wrapper is homogeneous (file-local copy of the private
`BracketFrameSumFiberOrder` helper). -/
private lemma tensor0SAsRS_smul (t : ℕ) (x : M) (c : ℝ) (C : Tensor0SSpace t I x) :
    tensor0SAsRS (I := I) (M := M) x (c • C) = c • tensor0SAsRS (I := I) (M := M) x C := by
  apply tensorRSSpace_ext (𝕜 := ℝ) 0 t x
  intro τ
  rw [show (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace t I x from
        tensor0SAsRS (I := I) (M := M) x (c • C)) τ =
      tensor00Scalar (I := I) (M := M) x τ • (c • C) from
    tensor0SAsRS_apply (I := I) (M := M) x _ τ]
  rw [show (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace t I x from
        c • tensor0SAsRS (I := I) (M := M) x C) τ =
      c • (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace t I x from
        tensor0SAsRS (I := I) (M := M) x C) τ from rfl]
  rw [show (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace t I x from
        tensor0SAsRS (I := I) (M := M) x C) τ =
      tensor00Scalar (I := I) (M := M) x τ • C from
    tensor0SAsRS_apply (I := I) (M := M) x _ τ]
  rw [smul_comm]

set_option linter.unusedSectionVars false in
/-- The `(0, t)`-tensor wrapper distributes over a difference. -/
private lemma tensor0SAsRS_sub (t : ℕ) (x : M) (C D : Tensor0SSpace t I x) :
    tensor0SAsRS (I := I) (M := M) x (C - D) =
      tensor0SAsRS (I := I) (M := M) x C - tensor0SAsRS (I := I) (M := M) x D := by
  rw [sub_eq_add_neg, sub_eq_add_neg, tensor0SAsRS_add, tensor0SAsRS_neg]

set_option backward.isDefEq.respectTransparency false in
/-- The `(0, s)`-fibre value summing the four group carriers' wrapped values (the seven-term sum of the
per-fixed-field carrier identity, `V := V a`, `X := V b`), read on the unit. -/
private def groupSevenTermFib (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s)
    (Va Vb : Π b : M, TangentSpace I b) (x : M) : Tensor0SSpace s I x :=
  (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
      riemannSec (tensorCov (I := I) g 0 s) Va Vb
        (covApply (tensorCov (I := I) g 0 s) Va (fun y : M => S.toSection y)) x)
      (unitZeroSec (I := I) (M := M) x) +
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
      covApply (tensorCov (I := I) g 0 s) Va
        (fun y : M => riemannSec (tensorCov (I := I) g 0 s) Va Vb
          (fun z : M => S.toSection z) y) x)
      (unitZeroSec (I := I) (M := M) x) +
    ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
        riemannOp (tensorCov (I := I) g 0 s) x
          ((LeviCivita (I := I) g).toFun Vb x (Va x)) (Va x) (S.toSection x))
        (unitZeroSec (I := I) (M := M) x) +
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
        riemannOp (tensorCov (I := I) g 0 s) x (Vb x)
          ((LeviCivita (I := I) g).toFun Va x (Va x)) (S.toSection x))
        (unitZeroSec (I := I) (M := M) x) -
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
        (tensorCov (I := I) g 0 s).toFun (fun y : M => S.toSection y) x
          (riemannOp (LeviCivita (I := I) g) x (Va x) (Vb x) (Va x)))
        (unitZeroSec (I := I) (M := M) x)) +
    (- (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
        tensorSecondCovDeriv (I := I) g 0 s
          (fun y : M => (LeviCivita (I := I) g).toFun Va y (Vb y)) Va
          (fun y : M => S.toSection y) x)
        (unitZeroSec (I := I) (M := M) x) -
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
        tensorSecondCovDeriv (I := I) g 0 s Va
          (fun y : M => (LeviCivita (I := I) g).toFun Va y (Vb y))
          (fun y : M => S.toSection y) x)
        (unitZeroSec (I := I) (M := M) x))

set_option linter.unusedSectionVars false in
/-- Each four-group carrier sum is the `tensor0SAsRS`-wrap of `groupSevenTermFib`. -/
private lemma group_sum_eq_tensor0SAsRS_sevenTerm
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s)
    (Va Vb : Π b : M, TangentSpace I b) (x : M) :
    bochnerGroupElt1 (I := I) (M := M) g s S Va Vb x +
        bochnerGroupElt2 (I := I) (M := M) g s S Va Vb x +
        bochnerGroupElt3 (I := I) (M := M) g s S Va Vb x +
        bochnerGroupElt4 (I := I) (M := M) g s S Va Vb x =
      tensor0SAsRS (I := I) (M := M) x (groupSevenTermFib (I := I) (M := M) g s S Va Vb x) := by
  rw [bochnerGroupElt1, bochnerGroupElt2, bochnerGroupElt3, bochnerGroupElt4, groupSevenTermFib]
  rw [← tensor0SAsRS_add, ← tensor0SAsRS_add, ← tensor0SAsRS_add]

set_option linter.unusedSectionVars false in
/-- **The slot-`0` reading of the order-`2` defect splits into the four group carriers.** Through the
fixed-family Parseval representation `pointwiseTensorCurv_parsevalSum_aux` the defect `Curv S` is
`∑_a [∇²_{V_a,V_a}(∇S) − ∇(∇²_{V_a,V_a} S)]`; the per-fixed-field seven-term carrier identity
`secondCovDeriv_covGrad_sub_covGrad_secondCovDeriv_slot0_eq` (`V := V a`, `X := V b`) writes each summand's
slot-`0` read as the four-group carrier combination. -/
private lemma bochnerSlot0Curv_eq_groupSum
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s)
    {N : ℕ} (V : Fin N → Π b : M, TangentSpace I b)
    (hV : ∀ a, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => (⟨b, V a b⟩ : TotalSpace E (TangentSpace I))))
    (hPar : ∀ (x : M) (u : TangentSpace I x),
      (∑ a : Fin N, g.inner x (V a x) u • V a x) = u) (b : Fin N) (x : M) :
    tensor0SAsRS (I := I) (M := M) x
        ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
            (pointwiseTensorCurv (I := I) (M := M) g s S).toSection x)
            (unitZeroSec (I := I) (M := M) x))) (V b x)) =
      ∑ a : Fin N,
        (bochnerGroupElt1 (I := I) (M := M) g s S (V a) (V b) x +
          bochnerGroupElt2 (I := I) (M := M) g s S (V a) (V b) x +
          bochnerGroupElt3 (I := I) (M := M) g s S (V a) (V b) x +
          bochnerGroupElt4 (I := I) (M := M) g s S (V a) (V b) x) := by
  classical
  rw [Finset.sum_congr rfl (fun a _ =>
    group_sum_eq_tensor0SAsRS_sevenTerm (I := I) (M := M) g s S (V a) (V b) x)]
  rw [← tensor0SAsRS_finsetSum (I := I) (M := M) s x Finset.univ
    (fun a => groupSevenTermFib (I := I) (M := M) g s S (V a) (V b) x)]
  rw [tensor0SAsRS_eq_iff]
  rw [pointwiseTensorCurv_parsevalSum_aux (I := I) (M := M) g s S V hV hPar x]
  -- Push the frame sum through `(show Hom · ) unit`, the curry, and the read at `V b x`.
  rw [show (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
        ∑ a : Fin N,
          ((secondCovDerivCc (I := I) (M := M) g (s + 1) (hV a)
              (covGrad (I := I) (M := M) g 0 s S)).toSection x -
            (covGrad (I := I) (M := M) g 0 s
              (secondCovDerivCc (I := I) (M := M) g s (hV a) S)).toSection x))
        (unitZeroSec (I := I) (M := M) x) =
      ∑ a : Fin N,
        (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
          (secondCovDerivCc (I := I) (M := M) g (s + 1) (hV a)
              (covGrad (I := I) (M := M) g 0 s S)).toSection x -
            (covGrad (I := I) (M := M) g 0 s
              (secondCovDerivCc (I := I) (M := M) g s (hV a) S)).toSection x)
          (unitZeroSec (I := I) (M := M) x) from
    ContinuousLinearMap.sum_apply _ _ _]
  rw [show (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x
        (∑ a : Fin N,
          (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
            (secondCovDerivCc (I := I) (M := M) g (s + 1) (hV a)
                (covGrad (I := I) (M := M) g 0 s S)).toSection x -
              (covGrad (I := I) (M := M) g 0 s
                (secondCovDerivCc (I := I) (M := M) g s (hV a) S)).toSection x)
            (unitZeroSec (I := I) (M := M) x))) (V b x) =
      ∑ a : Fin N,
        (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
            (secondCovDerivCc (I := I) (M := M) g (s + 1) (hV a)
                (covGrad (I := I) (M := M) g 0 s S)).toSection x -
              (covGrad (I := I) (M := M) g 0 s
                (secondCovDerivCc (I := I) (M := M) g s (hV a) S)).toSection x)
            (unitZeroSec (I := I) (M := M) x))) (V b x) from by
    rw [map_sum (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x)]
    rw [ContinuousLinearMap.sum_apply]]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro m
  change Tensor0SSpace.toModel
      ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
          (secondCovDerivCc (I := I) (M := M) g (s + 1) (hV a)
              (covGrad (I := I) (M := M) g 0 s S)).toSection x -
            (covGrad (I := I) (M := M) g 0 s
              (secondCovDerivCc (I := I) (M := M) g s (hV a) S)).toSection x)
          (unitZeroSec (I := I) (M := M) x))) (V b x)) m = _
  -- Split the curry of the difference into the difference of curries (M4's two LHS terms).
  rw [show (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
        (secondCovDerivCc (I := I) (M := M) g (s + 1) (hV a)
            (covGrad (I := I) (M := M) g 0 s S)).toSection x -
          (covGrad (I := I) (M := M) g 0 s
            (secondCovDerivCc (I := I) (M := M) g s (hV a) S)).toSection x)
        (unitZeroSec (I := I) (M := M) x) =
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
        (secondCovDerivCc (I := I) (M := M) g (s + 1) (hV a)
          (covGrad (I := I) (M := M) g 0 s S)).toSection x)
        (unitZeroSec (I := I) (M := M) x) -
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
        (covGrad (I := I) (M := M) g 0 s
          (secondCovDerivCc (I := I) (M := M) g s (hV a) S)).toSection x)
        (unitZeroSec (I := I) (M := M) x) from rfl]
  rw [map_sub (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x),
    ContinuousLinearMap.sub_apply, Tensor0SSpace.toModel_sub,
    secondCovDerivCc_toSection_apply]
  change _ = Tensor0SSpace.toModel (groupSevenTermFib (I := I) (M := M) g s S (V a) (V b) x) m
  convert secondCovDeriv_covGrad_sub_covGrad_secondCovDeriv_slot0_eq
    (I := I) (M := M) g s S (hV a) (hV b) x m using 2
  rw [groupSevenTermFib]
  abel

/-- The packaged covariant directional derivative `∇_X S` as a smooth compactly-supported
`(0, s)`-tensor (`covApply (tensorCov g 0 s) X S`), used to feed the curvature/second-order
carrier packagings. -/
private def covApplyCc (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s)
    {X : Π b : M, TangentSpace I b}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => (⟨b, X b⟩ : TotalSpace E (TangentSpace I)))) : SmoothCcTensor g 0 s where
  toSection :=
    { toFun := fun y : M => covApply (tensorCov (I := I) g 0 s) X
        (fun z : M => S.toSection z) y
      contMDiff_toFun := covApplyRS_contMDiff (I := I) g 0 s S.toSection.contMDiff hX }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

set_option linter.unusedSectionVars false in
@[simp] private lemma covApplyCc_toSection_apply (g : SmoothRiemannianMetric I M) (s : ℕ)
    (S : SmoothCcTensor g 0 s) {X : Π b : M, TangentSpace I b}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => (⟨b, X b⟩ : TotalSpace E (TangentSpace I)))) (y : M) :
    (covApplyCc (I := I) (M := M) g s S hX).toSection y =
      covApply (tensorCov (I := I) g 0 s) X (fun z : M => S.toSection z) y := rfl

/-- Group `1` carrier packaged as a smooth compactly-supported `(0, s)`-tensor:
`x ↦ R(V a, V b)(∇_{V a} S)` (via `riemannSec`, with the `tensor0SAsRS`-wrap collapsed). -/
private def bochnerGroupElt1Cc (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s)
    {Va Vb : Π b : M, TangentSpace I b}
    (hVa : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => (⟨b, Va b⟩ : TotalSpace E (TangentSpace I))))
    (hVb : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => (⟨b, Vb b⟩ : TotalSpace E (TangentSpace I)))) : SmoothCcTensor g 0 s where
  toSection :=
    { toFun := fun x : M => riemannSec (tensorCov (I := I) g 0 s) Va Vb
        (covApply (tensorCov (I := I) g 0 s) Va (fun y : M => S.toSection y)) x
      contMDiff_toFun := riemannSec_contMDiff (cov := tensorCov (I := I) g 0 s) hVa hVb
        (covApplyRS_contMDiff (I := I) g 0 s S.toSection.contMDiff hVa) }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

set_option linter.unusedSectionVars false in
private lemma bochnerGroupElt1Cc_toSection_eq (g : SmoothRiemannianMetric I M) (s : ℕ)
    (S : SmoothCcTensor g 0 s) {Va Vb : Π b : M, TangentSpace I b}
    (hVa : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => (⟨b, Va b⟩ : TotalSpace E (TangentSpace I))))
    (hVb : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => (⟨b, Vb b⟩ : TotalSpace E (TangentSpace I)))) (x : M) :
    (bochnerGroupElt1Cc (I := I) (M := M) g s S hVa hVb).toSection x =
      bochnerGroupElt1 (I := I) (M := M) g s S Va Vb x := by
  rw [bochnerGroupElt1]
  exact (tensor0SAsRS_rs_unit' (I := I) (M := M) s x _).symm

/-- Group `2` carrier packaged as a smooth compactly-supported `(0, s)`-tensor:
`x ↦ ∇_{V a}(R(V a, V b) S)`. -/
private def bochnerGroupElt2Cc (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s)
    {Va Vb : Π b : M, TangentSpace I b}
    (hVa : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => (⟨b, Va b⟩ : TotalSpace E (TangentSpace I))))
    (hVb : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => (⟨b, Vb b⟩ : TotalSpace E (TangentSpace I)))) : SmoothCcTensor g 0 s where
  toSection :=
    { toFun := fun x : M => covApply (tensorCov (I := I) g 0 s) Va
        (fun y : M => riemannSec (tensorCov (I := I) g 0 s) Va Vb
          (fun z : M => S.toSection z) y) x
      contMDiff_toFun := covApplyRS_contMDiff (I := I) g 0 s
        (riemannSec_contMDiff (cov := tensorCov (I := I) g 0 s) hVa hVb S.toSection.contMDiff)
        hVa }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

set_option linter.unusedSectionVars false in
private lemma bochnerGroupElt2Cc_toSection_eq (g : SmoothRiemannianMetric I M) (s : ℕ)
    (S : SmoothCcTensor g 0 s) {Va Vb : Π b : M, TangentSpace I b}
    (hVa : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => (⟨b, Va b⟩ : TotalSpace E (TangentSpace I))))
    (hVb : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => (⟨b, Vb b⟩ : TotalSpace E (TangentSpace I)))) (x : M) :
    (bochnerGroupElt2Cc (I := I) (M := M) g s S hVa hVb).toSection x =
      bochnerGroupElt2 (I := I) (M := M) g s S Va Vb x := by
  rw [bochnerGroupElt2]
  exact (tensor0SAsRS_rs_unit' (I := I) (M := M) s x _).symm

/-- **Total-space smoothness of the off-diagonal second covariant derivative section.** For smooth
tangent fields `X, Y` and a smooth `(0, s)`-tensor section `T`, the section
`x ↦ ∇²_{X, Y} T (x)` is smooth: it is the difference of the iterated covariant section
`∇_X(∇_Y T)` and the Christoffel-correction section `∇_{∇_X Y} T`
(`tensorSecondCovDeriv_def`). -/
private lemma tensorSecondCovDeriv_offDiag_section_contMDiff (g : SmoothRiemannianMetric I M)
    (s : ℕ) {T : Π b : M, TensorRSSpace 0 s I b}
    (hT : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 0 s ℝ E)) ∞
      (fun y : M => (⟨y, T y⟩ : TotalSpace (TensorRSModel 0 s ℝ E)
        (fun z : M => TensorRSSpace 0 s I z))))
    {X Y : Π b : M, TangentSpace I b}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => (⟨b, X b⟩ : TotalSpace E (TangentSpace I))))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => (⟨b, Y b⟩ : TotalSpace E (TangentSpace I)))) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 0 s ℝ E)) ∞
      (fun x : M => (⟨x, tensorSecondCovDeriv (I := I) g 0 s X Y T x⟩ :
        TotalSpace (TensorRSModel 0 s ℝ E) (fun z : M => TensorRSSpace 0 s I z))) := by
  have h1 := covApplyRS_contMDiff (I := I) g 0 s
    (covApplyRS_contMDiff (I := I) g 0 s hT hY) hX
  have h2 := covApplyRS_contMDiff (I := I) g 0 s hT
    (covApply_contMDiff (cov := LeviCivita (I := I) g) hX hY)
  refine (h1.sub_section h2).congr fun x => ?_
  rw [tensorSecondCovDeriv_def (I := I) g 0 s X Y T x]
  rfl

/-- Group `3` carrier packaged as a smooth compactly-supported `(0, s)`-tensor:
`x ↦ R(∇_{V a} V b, V a) S + R(V b, ∇_{V a} V a) S − ∇_{R(V a, V b) V a} S` (the first two
curvature terms read through `riemannSec`, the third through `covApply` of the smooth direction
field `x ↦ R(V a, V b) V a`). -/
private def bochnerGroupElt3Cc (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s)
    {Va Vb : Π b : M, TangentSpace I b}
    (hVa : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => (⟨b, Va b⟩ : TotalSpace E (TangentSpace I))))
    (hVb : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => (⟨b, Vb b⟩ : TotalSpace E (TangentSpace I)))) : SmoothCcTensor g 0 s where
  toSection :=
    { toFun := fun x : M =>
        riemannSec (tensorCov (I := I) g 0 s)
          (fun b : M => (LeviCivita (I := I) g).toFun Vb b (Va b)) Va
          (fun y : M => S.toSection y) x +
        riemannSec (tensorCov (I := I) g 0 s) Vb
          (fun b : M => (LeviCivita (I := I) g).toFun Va b (Va b))
          (fun y : M => S.toSection y) x -
        covApply (tensorCov (I := I) g 0 s)
          (fun b : M => riemannOp (LeviCivita (I := I) g) b (Va b) (Vb b) (Va b))
          (fun y : M => S.toSection y) x
      contMDiff_toFun := by
        have hNbVa : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
            (fun b : M => (⟨b, (LeviCivita (I := I) g).toFun Vb b (Va b)⟩ :
              TotalSpace E (TangentSpace I))) :=
          covApply_contMDiff (cov := LeviCivita (I := I) g) hVa hVb
        have hNaVa : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
            (fun b : M => (⟨b, (LeviCivita (I := I) g).toFun Va b (Va b)⟩ :
              TotalSpace E (TangentSpace I))) :=
          covApply_contMDiff (cov := LeviCivita (I := I) g) hVa hVa
        have hRfield : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
            (fun b : M => (⟨b, riemannOp (LeviCivita (I := I) g) b (Va b) (Vb b) (Va b)⟩ :
              TotalSpace E (TangentSpace I))) :=
          ContMDiff.clm_bundle_apply (b := id)
            (ContMDiff.clm_bundle_apply (b := id)
              (ContMDiff.clm_bundle_apply (b := id)
                (riemannOp_section_contMDiff (I := I) (M := M) g) hVa) hVb) hVa
        have hT1 := riemannSec_contMDiff (cov := tensorCov (I := I) g 0 s) hNbVa hVa
          S.toSection.contMDiff
        have hT2 := riemannSec_contMDiff (cov := tensorCov (I := I) g 0 s) hVb hNaVa
          S.toSection.contMDiff
        have hT3 := covApplyRS_contMDiff (I := I) g 0 s S.toSection.contMDiff hRfield
        exact (hT1.add_section hT2).sub_section hT3 }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

set_option linter.unusedSectionVars false in
private lemma bochnerGroupElt3Cc_toSection_eq (g : SmoothRiemannianMetric I M) (s : ℕ)
    (S : SmoothCcTensor g 0 s) {Va Vb : Π b : M, TangentSpace I b}
    (hVa : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => (⟨b, Va b⟩ : TotalSpace E (TangentSpace I))))
    (hVb : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => (⟨b, Vb b⟩ : TotalSpace E (TangentSpace I)))) (x : M) :
    (bochnerGroupElt3Cc (I := I) (M := M) g s S hVa hVb).toSection x =
      bochnerGroupElt3 (I := I) (M := M) g s S Va Vb x := by
  have hd1 : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => (⟨b, (LeviCivita (I := I) g).toFun Vb b (Va b)⟩ :
        TotalSpace E (TangentSpace I))) :=
    covApply_contMDiff (cov := LeviCivita (I := I) g) hVa hVb
  have hd2 : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => (⟨b, (LeviCivita (I := I) g).toFun Va b (Va b)⟩ :
        TotalSpace E (TangentSpace I))) :=
    covApply_contMDiff (cov := LeviCivita (I := I) g) hVa hVa
  change riemannSec (tensorCov (I := I) g 0 s)
      (fun b : M => (LeviCivita (I := I) g).toFun Vb b (Va b)) Va
      (fun y : M => S.toSection y) x +
    riemannSec (tensorCov (I := I) g 0 s) Vb
      (fun b : M => (LeviCivita (I := I) g).toFun Va b (Va b))
      (fun y : M => S.toSection y) x -
    covApply (tensorCov (I := I) g 0 s)
      (fun b : M => riemannOp (LeviCivita (I := I) g) b (Va b) (Vb b) (Va b))
      (fun y : M => S.toSection y) x = _
  rw [riemannSec_eq_riemannOp_smooth (cov := tensorCov (I := I) g 0 s)
      hd1 hVa S.toSection.contMDiff,
    riemannSec_eq_riemannOp_smooth (cov := tensorCov (I := I) g 0 s) hVb
      hd2 S.toSection.contMDiff,
    covApply_apply (cov := tensorCov (I := I) g 0 s)]
  rw [bochnerGroupElt3, tensor0SAsRS_sub, tensor0SAsRS_add,
    tensor0SAsRS_rs_unit' (I := I) (M := M) s x _,
    tensor0SAsRS_rs_unit' (I := I) (M := M) s x _,
    tensor0SAsRS_rs_unit' (I := I) (M := M) s x _]

set_option backward.isDefEq.respectTransparency false in
/-- **The frame-derivative (tension-field) part of the group-`3` carrier** (terms iii + iv of the
seven-term identity), `R(∇_{V a} V b, V a) S + R(V b, ∇_{V a} V a) S`, read on the unit, as a
`TensorRSSpace 0 s`.  These are the two curvature carriers whose first/second slot carries a frame
derivative `∇V`; they are generally nonzero and frame-dependent pointwise, vanishing only after the
frame-summed covariant integration by parts (the total covariant divergence of the frame-summed
second Bianchi). -/
def bochnerGroupElt3IiiIv (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s)
    (Va Vb : Π b : M, TangentSpace I b) (x : M) : TensorRSSpace 0 s I x :=
  tensor0SAsRS (I := I) (M := M) x
    ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
        riemannOp (tensorCov (I := I) g 0 s) x
          ((LeviCivita (I := I) g).toFun Vb x (Va x)) (Va x) (S.toSection x))
        (unitZeroSec (I := I) (M := M) x) +
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
        riemannOp (tensorCov (I := I) g 0 s) x (Vb x)
          ((LeviCivita (I := I) g).toFun Va x (Va x)) (S.toSection x))
        (unitZeroSec (I := I) (M := M) x))

set_option backward.isDefEq.respectTransparency false in
/-- **The Ricci-direction (term v) part of the group-`3` carrier**, `−∇_{R(V a, V b) V a} S`, read on
the unit, as a `TensorRSSpace 0 s`.  Its frame sum over `a` is pointwise the leading-slot raised-Ricci
read of `∇S` (because `∑_a R(V a, V b) V a = −ricEndoRaisedFib g x (V b)` for any Parseval frame),
which is exactly the leading slot of `ricTraceSection`. -/
def bochnerGroupElt3NegV (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s)
    (Va Vb : Π b : M, TangentSpace I b) (x : M) : TensorRSSpace 0 s I x :=
  tensor0SAsRS (I := I) (M := M) x
    (- (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
        (tensorCov (I := I) g 0 s).toFun (fun y : M => S.toSection y) x
          (riemannOp (LeviCivita (I := I) g) x (Va x) (Vb x) (Va x)))
        (unitZeroSec (I := I) (M := M) x))

set_option backward.isDefEq.respectTransparency false in
/-- **The group-`3` carrier splits as its frame-derivative part plus its Ricci-direction part**, at
every point.  `bochnerGroupElt3 = bochnerGroupElt3IiiIv + bochnerGroupElt3NegV` is the regrouping
`(iii + iv) − v = (iii + iv) + (−v)` through the `tensor0SAsRS` wrapper additivity. -/
private lemma bochnerGroupElt3_eq_iiiIv_add_negV (g : SmoothRiemannianMetric I M) (s : ℕ)
    (S : SmoothCcTensor g 0 s) (Va Vb : Π b : M, TangentSpace I b) (x : M) :
    bochnerGroupElt3 (I := I) (M := M) g s S Va Vb x =
      bochnerGroupElt3IiiIv (I := I) (M := M) g s S Va Vb x +
        bochnerGroupElt3NegV (I := I) (M := M) g s S Va Vb x := by
  rw [bochnerGroupElt3, bochnerGroupElt3IiiIv, bochnerGroupElt3NegV, sub_eq_add_neg,
    tensor0SAsRS_add]

/-- The frame-derivative (tension-field) part `bochnerGroupElt3IiiIv` packaged as a smooth
compactly-supported `(0, s)`-tensor. -/
private def bochnerGroupElt3IiiIvCc (g : SmoothRiemannianMetric I M) (s : ℕ)
    (S : SmoothCcTensor g 0 s) {Va Vb : Π b : M, TangentSpace I b}
    (hVa : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => (⟨b, Va b⟩ : TotalSpace E (TangentSpace I))))
    (hVb : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => (⟨b, Vb b⟩ : TotalSpace E (TangentSpace I)))) : SmoothCcTensor g 0 s where
  toSection :=
    { toFun := fun x : M =>
        riemannSec (tensorCov (I := I) g 0 s)
          (fun b : M => (LeviCivita (I := I) g).toFun Vb b (Va b)) Va
          (fun y : M => S.toSection y) x +
        riemannSec (tensorCov (I := I) g 0 s) Vb
          (fun b : M => (LeviCivita (I := I) g).toFun Va b (Va b))
          (fun y : M => S.toSection y) x
      contMDiff_toFun := by
        have hNbVa : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
            (fun b : M => (⟨b, (LeviCivita (I := I) g).toFun Vb b (Va b)⟩ :
              TotalSpace E (TangentSpace I))) :=
          covApply_contMDiff (cov := LeviCivita (I := I) g) hVa hVb
        have hNaVa : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
            (fun b : M => (⟨b, (LeviCivita (I := I) g).toFun Va b (Va b)⟩ :
              TotalSpace E (TangentSpace I))) :=
          covApply_contMDiff (cov := LeviCivita (I := I) g) hVa hVa
        have hT1 := riemannSec_contMDiff (cov := tensorCov (I := I) g 0 s) hNbVa hVa
          S.toSection.contMDiff
        have hT2 := riemannSec_contMDiff (cov := tensorCov (I := I) g 0 s) hVb hNaVa
          S.toSection.contMDiff
        exact hT1.add_section hT2 }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

set_option linter.unusedSectionVars false in
private lemma bochnerGroupElt3IiiIvCc_toSection_eq (g : SmoothRiemannianMetric I M) (s : ℕ)
    (S : SmoothCcTensor g 0 s) {Va Vb : Π b : M, TangentSpace I b}
    (hVa : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => (⟨b, Va b⟩ : TotalSpace E (TangentSpace I))))
    (hVb : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => (⟨b, Vb b⟩ : TotalSpace E (TangentSpace I)))) (x : M) :
    (bochnerGroupElt3IiiIvCc (I := I) (M := M) g s S hVa hVb).toSection x =
      bochnerGroupElt3IiiIv (I := I) (M := M) g s S Va Vb x := by
  have hd1 : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => (⟨b, (LeviCivita (I := I) g).toFun Vb b (Va b)⟩ :
        TotalSpace E (TangentSpace I))) :=
    covApply_contMDiff (cov := LeviCivita (I := I) g) hVa hVb
  have hd2 : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => (⟨b, (LeviCivita (I := I) g).toFun Va b (Va b)⟩ :
        TotalSpace E (TangentSpace I))) :=
    covApply_contMDiff (cov := LeviCivita (I := I) g) hVa hVa
  change riemannSec (tensorCov (I := I) g 0 s)
      (fun b : M => (LeviCivita (I := I) g).toFun Vb b (Va b)) Va
      (fun y : M => S.toSection y) x +
    riemannSec (tensorCov (I := I) g 0 s) Vb
      (fun b : M => (LeviCivita (I := I) g).toFun Va b (Va b))
      (fun y : M => S.toSection y) x = _
  rw [riemannSec_eq_riemannOp_smooth (cov := tensorCov (I := I) g 0 s)
      hd1 hVa S.toSection.contMDiff,
    riemannSec_eq_riemannOp_smooth (cov := tensorCov (I := I) g 0 s) hVb
      hd2 S.toSection.contMDiff]
  rw [bochnerGroupElt3IiiIv, tensor0SAsRS_add,
    tensor0SAsRS_rs_unit' (I := I) (M := M) s x _,
    tensor0SAsRS_rs_unit' (I := I) (M := M) s x _]

/-- The Ricci-direction part `bochnerGroupElt3NegV` packaged as a smooth compactly-supported
`(0, s)`-tensor. -/
private def bochnerGroupElt3NegVCc (g : SmoothRiemannianMetric I M) (s : ℕ)
    (S : SmoothCcTensor g 0 s) {Va Vb : Π b : M, TangentSpace I b}
    (hVa : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => (⟨b, Va b⟩ : TotalSpace E (TangentSpace I))))
    (hVb : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => (⟨b, Vb b⟩ : TotalSpace E (TangentSpace I)))) : SmoothCcTensor g 0 s where
  toSection :=
    { toFun := fun x : M =>
        - covApply (tensorCov (I := I) g 0 s)
          (fun b : M => riemannOp (LeviCivita (I := I) g) b (Va b) (Vb b) (Va b))
          (fun y : M => S.toSection y) x
      contMDiff_toFun := by
        have hRfield : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
            (fun b : M => (⟨b, riemannOp (LeviCivita (I := I) g) b (Va b) (Vb b) (Va b)⟩ :
              TotalSpace E (TangentSpace I))) :=
          ContMDiff.clm_bundle_apply (b := id)
            (ContMDiff.clm_bundle_apply (b := id)
              (ContMDiff.clm_bundle_apply (b := id)
                (riemannOp_section_contMDiff (I := I) (M := M) g) hVa) hVb) hVa
        exact (covApplyRS_contMDiff (I := I) g 0 s S.toSection.contMDiff hRfield).neg_section }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

set_option linter.unusedSectionVars false in
private lemma bochnerGroupElt3NegVCc_toSection_eq (g : SmoothRiemannianMetric I M) (s : ℕ)
    (S : SmoothCcTensor g 0 s) {Va Vb : Π b : M, TangentSpace I b}
    (hVa : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => (⟨b, Va b⟩ : TotalSpace E (TangentSpace I))))
    (hVb : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => (⟨b, Vb b⟩ : TotalSpace E (TangentSpace I)))) (x : M) :
    (bochnerGroupElt3NegVCc (I := I) (M := M) g s S hVa hVb).toSection x =
      bochnerGroupElt3NegV (I := I) (M := M) g s S Va Vb x := by
  change - covApply (tensorCov (I := I) g 0 s)
      (fun b : M => riemannOp (LeviCivita (I := I) g) b (Va b) (Vb b) (Va b))
      (fun y : M => S.toSection y) x = _
  rw [covApply_apply (cov := tensorCov (I := I) g 0 s)]
  rw [bochnerGroupElt3NegV, tensor0SAsRS_neg,
    tensor0SAsRS_rs_unit' (I := I) (M := M) s x _]

/-- Group `4` carrier packaged as a smooth compactly-supported `(0, s)`-tensor:
`x ↦ −∇²_{∇_{V b} V a, V a} S − ∇²_{V a, ∇_{V b} V a} S`. -/
private def bochnerGroupElt4Cc (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s)
    {Va Vb : Π b : M, TangentSpace I b}
    (hVa : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => (⟨b, Va b⟩ : TotalSpace E (TangentSpace I))))
    (hVb : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => (⟨b, Vb b⟩ : TotalSpace E (TangentSpace I)))) : SmoothCcTensor g 0 s where
  toSection :=
    { toFun := fun x : M =>
        - tensorSecondCovDeriv (I := I) g 0 s
            (fun y : M => (LeviCivita (I := I) g).toFun Va y (Vb y)) Va
            (fun y : M => S.toSection y) x -
          tensorSecondCovDeriv (I := I) g 0 s Va
            (fun y : M => (LeviCivita (I := I) g).toFun Va y (Vb y))
            (fun y : M => S.toSection y) x
      contMDiff_toFun := by
        have hNbVa : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
            (fun b : M => (⟨b, covApply (LeviCivita (I := I) g) Vb Va b⟩ :
              TotalSpace E (TangentSpace I))) :=
          covApply_contMDiff (cov := LeviCivita (I := I) g) hVb hVa
        have h1 := tensorSecondCovDeriv_offDiag_section_contMDiff (I := I) g s
          S.toSection.contMDiff hNbVa hVa
        have h2 := tensorSecondCovDeriv_offDiag_section_contMDiff (I := I) g s
          S.toSection.contMDiff hVa hNbVa
        refine ((h1.neg_section).sub_section h2).congr fun x => ?_
        rfl }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

set_option linter.unusedSectionVars false in
private lemma bochnerGroupElt4Cc_toSection_eq (g : SmoothRiemannianMetric I M) (s : ℕ)
    (S : SmoothCcTensor g 0 s) {Va Vb : Π b : M, TangentSpace I b}
    (hVa : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => (⟨b, Va b⟩ : TotalSpace E (TangentSpace I))))
    (hVb : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => (⟨b, Vb b⟩ : TotalSpace E (TangentSpace I)))) (x : M) :
    (bochnerGroupElt4Cc (I := I) (M := M) g s S hVa hVb).toSection x =
      bochnerGroupElt4 (I := I) (M := M) g s S Va Vb x := by
  change - tensorSecondCovDeriv (I := I) g 0 s
        (fun y : M => (LeviCivita (I := I) g).toFun Va y (Vb y)) Va
        (fun y : M => S.toSection y) x -
      tensorSecondCovDeriv (I := I) g 0 s Va
        (fun y : M => (LeviCivita (I := I) g).toFun Va y (Vb y))
        (fun y : M => S.toSection y) x = _
  rw [bochnerGroupElt4, tensor0SAsRS_sub, tensor0SAsRS_neg,
    tensor0SAsRS_rs_unit' (I := I) (M := M) s x _,
    tensor0SAsRS_rs_unit' (I := I) (M := M) s x _]

set_option linter.unusedSectionVars false in
/-- The scalar read of a smooth `(0, 0)`-tensor section is a smooth real function (file-local
copy of the private `Slot0CurryCovariantLeibniz` helper). -/
private lemma contMDiff_tensor00Scalar_read'
    (Y : Cₛ^∞⟮I; Tensor0SModel 0 ℝ E, (fun z : M => Tensor0SSpace 0 I z)⟯) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun y : M => tensor00Scalar (I := I) (M := M) y (Y y)) := by
  have heq : (fun y : M => tensor00Scalar (I := I) (M := M) y (Y y)) =
      Tensor0SNabla.scalarFn I M (fun y : M => Y y) := by
    funext y; rfl
  rw [heq]
  exact (Tensor0SNabla.contMDiff_scalarFn_iff_section I M (fun y : M => Y y)).mpr Y.contMDiff

set_option linter.unusedSectionVars false in
/-- **Smoothness of the `tensor0SAsRS`-wrapped section** (file-local copy). -/
private lemma contMDiff_tensor0SAsRS_wrap' (t : ℕ) {C : Π y : M, Tensor0SSpace t I y}
    (hC : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel t ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (Tensor0SModel t ℝ E)
        (E := fun z : M => Tensor0SSpace t I z) y (C y))) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 0 t ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel 0 t ℝ E)
        (E := fun z : M => TensorRSSpace 0 t I z) y
        (tensor0SAsRS (I := I) (M := M) y (C y))) := by
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (F₁ := Tensor0SModel 0 ℝ E) (V₁ := fun z : M => Tensor0SSpace 0 I z)
    (F₂ := Tensor0SModel t ℝ E) (V₂ := fun z : M => Tensor0SSpace t I z)
    (φ := fun y : M => tensor0SAsRS (I := I) (M := M) y (C y))
  intro Y
  have hsmul := ContMDiff.smul_section (n := (∞ : WithTop ℕ∞))
    (contMDiff_tensor00Scalar_read' (I := I) (M := M) Y) hC
  refine hsmul.congr fun y => ?_
  rw [show ((fun z : M => tensor00Scalar (I := I) (M := M) z (Y z)) • C) y =
      tensor00Scalar (I := I) (M := M) y (Y y) • C y from rfl]
  rw [← tensor0SAsRS_apply (I := I) (M := M) y (C y) (Y y)]

set_option linter.unusedSectionVars false in
/-- **Smoothness of the unit-evaluated section of a smooth compactly-supported `(0, k)`-tensor**
(file-local copy). -/
private lemma contMDiff_unitEvalSection' (g : SmoothRiemannianMetric I M) (k : ℕ)
    (Z : SmoothCcTensor g 0 k) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel k ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (Tensor0SModel k ℝ E)
        (E := fun z : M => Tensor0SSpace k I z) y
        ((show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace k I y from Z.toSection y)
          (unitZeroSec (I := I) (M := M) y))) :=
  ContMDiff.clm_bundle_apply (b := fun y : M => y)
    (E₁ := fun z : M => Tensor0SSpace 0 I z) (E₂ := fun z : M => Tensor0SSpace k I z)
    (F₁ := Tensor0SModel 0 ℝ E) (F₂ := Tensor0SModel k ℝ E)
    Z.toSection.contMDiff (contMDiff_unitZeroSection (I := I) (M := M))

set_option linter.unusedSectionVars false in
/-- **Smoothness of the slot-`0` `X`-read of a smooth compactly-supported `(0, s + 1)`-tensor**,
in `tensor0SAsRS`-wrapped Hom-bundle form (file-local copy of the `Slot0CurryCovariantLeibniz`
private helper). -/
private lemma contMDiff_slot0Read' (g : SmoothRiemannianMetric I M) (s : ℕ)
    (Z : SmoothCcTensor g 0 (s + 1)) {X : Π b : M, TangentSpace I b}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => (⟨b, X b⟩ : TotalSpace E (TangentSpace I)))) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 0 s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel 0 s ℝ E)
        (E := fun z : M => TensorRSSpace 0 s I z) y
        (tensor0SAsRS (I := I) (M := M) y
          ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s y
            ((show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace (s + 1) I y from
              Z.toSection y) (unitZeroSec (I := I) (M := M) y))) (X y)))) := by
  have hUzS := contMDiff_unitEvalSection' (I := I) (M := M) g (s + 1) Z
  have hcur : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] Tensor0SModel s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (E →L[ℝ] Tensor0SModel s ℝ E)
        (E := fun z : M => TangentSpace I z →L[ℝ] Tensor0SSpace s I z) y
        (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s y
          ((show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace (s + 1) I y from
            Z.toSection y) (unitZeroSec (I := I) (M := M) y)))) :=
    fun y => TensorMultilinear.contMDiffAt_curriedSection_of_contMDiffAt_section
      (I := I) (M := M)
      (fun z : M => (show Tensor0SSpace 0 I z →L[ℝ] Tensor0SSpace (s + 1) I z from
        Z.toSection z) (unitZeroSec (I := I) (M := M) z)) y (hUzS y)
  have hCs : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (Tensor0SModel s ℝ E)
        (E := fun z : M => Tensor0SSpace s I z) y
        ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s y
          ((show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace (s + 1) I y from
            Z.toSection y) (unitZeroSec (I := I) (M := M) y))) (X y))) :=
    ContMDiff.clm_bundle_apply (b := fun y : M => y)
      (E₁ := TangentSpace I) (E₂ := fun z : M => Tensor0SSpace s I z)
      (F₁ := E) (F₂ := Tensor0SModel s ℝ E) hcur hX
  exact contMDiff_tensor0SAsRS_wrap' (I := I) (M := M) s hCs

/-- The slot-`0` `V b`-read of `∇S` packaged as a smooth compactly-supported `(0, s)`-tensor
(`bochnerGradSlot0 g s S V b`). -/
private def bochnerGradSlot0Cc (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s)
    {Vb : Π b : M, TangentSpace I b}
    (hVb : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => (⟨b, Vb b⟩ : TotalSpace E (TangentSpace I)))) : SmoothCcTensor g 0 s where
  toSection :=
    { toFun := fun x : M => bochnerGradSlot0 (I := I) (M := M) g s S Vb x
      contMDiff_toFun := contMDiff_slot0Read' (I := I) (M := M) g s
        (covGrad (I := I) (M := M) g 0 s S) hVb }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

set_option linter.unusedSectionVars false in
@[simp] private lemma bochnerGradSlot0Cc_toSection_apply (g : SmoothRiemannianMetric I M) (s : ℕ)
    (S : SmoothCcTensor g 0 s) {Vb : Π b : M, TangentSpace I b}
    (hVb : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => (⟨b, Vb b⟩ : TotalSpace E (TangentSpace I)))) (x : M) :
    (bochnerGradSlot0Cc (I := I) (M := M) g s S hVb).toSection x =
      bochnerGradSlot0 (I := I) (M := M) g s S Vb x := rfl

/-- The slot-`0` `V b`-read of a named smooth `(0, s + 1)`-tensor section `Named`, packaged as a
smooth compactly-supported `(0, s)`-tensor (`tensor0SAsRS x ((curry (Named(unit)))(V b x))`). -/
private def namedSlot0Cc (g : SmoothRiemannianMetric I M) (s : ℕ) (Named : SmoothCcTensor g 0 (s + 1))
    {Vb : Π b : M, TangentSpace I b}
    (hVb : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => (⟨b, Vb b⟩ : TotalSpace E (TangentSpace I)))) : SmoothCcTensor g 0 s where
  toSection :=
    { toFun := fun x : M => tensor0SAsRS (I := I) (M := M) x
        ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from Named.toSection x)
            (unitZeroSec (I := I) (M := M) x))) (Vb x))
      contMDiff_toFun := contMDiff_slot0Read' (I := I) (M := M) g s Named hVb }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

set_option linter.unusedSectionVars false in
/-- **The unified group→carrier fold assembly.** For a fixed Parseval frame family and a named
smooth `(0, s + 1)`-tensor section `Named`, if the slot-`0` `V b`-read of `Named` is, at every
point, the Parseval-family sum over `a` of the carrier `Elt (V a) (V b)` (the genuine content), and
every per-`(a, b)` carrier pairing is integrable, then the `L²` pairing of `Named` against `∇S`
equals the group double sum `bochnerFoldGroupSum`. The proof is the slot-`0` fixed-family Parseval
expansion of the `(0, s + 1)` pairing (`tensorInnerPointwise_succ_eq_parseval_sum_slot0`), the
pointwise carrier split (`tensorInnerPointwise_sum_left`), the finite integral/sum interchanges
(`MeasureTheory.integral_finset_sum`), and `Finset.sum_comm`. -/
private lemma fold_assembly
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s)
    {N : ℕ} (V : Fin N → Π b : M, TangentSpace I b)
    (hV : ∀ a, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => (⟨b, V a b⟩ : TotalSpace E (TangentSpace I))))
    (hPar : ∀ (x : M) (u : TangentSpace I x),
      (∑ a : Fin N, g.inner x (V a x) u • V a x) = u)
    (Named : SmoothCcTensor g 0 (s + 1))
    (Elt : (Π b : M, TangentSpace I b) → (Π b : M, TangentSpace I b) → (x : M) →
      TensorRSSpace 0 s I x)
    (hslot0 : ∀ (b : Fin N) (x : M),
      tensor0SAsRS (I := I) (M := M) x
          ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x
            ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from Named.toSection x)
              (unitZeroSec (I := I) (M := M) x))) (V b x)) =
        ∑ a : Fin N, Elt (V a) (V b) x)
    (hint : ∀ (a b : Fin N), Integrable
      (fun x : M => tensorInnerPointwise (I := I) (M := M) g 0 s x
        (TensorRSSpace.toModel (Elt (V a) (V b) x))
        (TensorRSSpace.toModel (bochnerGradSlot0 (I := I) (M := M) g s S (V b) x)))
      (riemannianVolumeMeasure (I := I) (M := M) g)) :
    tensorL2Inner (I := I) (M := M) g 0 (s + 1) (Named).toFun
        (covGrad (I := I) (M := M) g 0 s S).toFun =
      bochnerFoldGroupSum (I := I) (M := M) g s S V Elt := by
  classical
  -- Unfold the `L²` pairing and apply the slot-`0` Parseval expansion pointwise.
  rw [show tensorL2Inner (I := I) (M := M) g 0 (s + 1) (Named).toFun
        (covGrad (I := I) (M := M) g 0 s S).toFun =
      ∫ x, (∑ b : Fin N,
          tensorInnerPointwise (I := I) (M := M) g 0 s x
            ((namedSlot0Cc (I := I) (M := M) g s Named (hV b)).toFun x)
            ((bochnerGradSlot0Cc (I := I) (M := M) g s S (hV b)).toFun x))
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) from ?_]
  · -- Interchange the outer integral with the `∑ b`, then split each summand by the carrier sum.
    rw [MeasureTheory.integral_finset_sum Finset.univ
      (fun b _ => SmoothCcTensor.integrable_inner_cross (I := I) (M := M)
        (namedSlot0Cc (I := I) (M := M) g s Named (hV b))
        (bochnerGradSlot0Cc (I := I) (M := M) g s S (hV b)))]
    rw [show bochnerFoldGroupSum (I := I) (M := M) g s S V Elt =
        ∑ b : Fin N, ∑ a : Fin N,
          ∫ x, tensorInnerPointwise (I := I) (M := M) g 0 s x
              (TensorRSSpace.toModel (Elt (V a) (V b) x))
              (TensorRSSpace.toModel (bochnerGradSlot0 (I := I) (M := M) g s S (V b) x))
            ∂(riemannianVolumeMeasure (I := I) (M := M) g) from by
      rw [bochnerFoldGroupSum, Finset.sum_comm]]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [← MeasureTheory.integral_finset_sum Finset.univ (fun a _ => hint a b)]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    change tensorInnerPointwise (I := I) (M := M) g 0 s x
        (TensorRSSpace.toModel (tensor0SAsRS (I := I) (M := M) x
          ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x
            ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from Named.toSection x)
              (unitZeroSec (I := I) (M := M) x))) (V b x))))
        (TensorRSSpace.toModel (bochnerGradSlot0 (I := I) (M := M) g s S (V b) x)) = _
    rw [hslot0 b x]
    have hsumModel : ∀ (fs : Finset (Fin N)),
        TensorRSSpace.toModel (∑ a ∈ fs, Elt (V a) (V b) x) =
        ∑ a ∈ fs, (1 : ℝ) • TensorRSSpace.toModel (Elt (V a) (V b) x) := by
      intro fs
      induction fs using Finset.induction with
      | empty => rw [Finset.sum_empty, Finset.sum_empty, TensorRSSpace.toModel_zero]
      | insert i fs hi ih =>
        rw [Finset.sum_insert hi, Finset.sum_insert hi, TensorRSSpace.toModel_add, ih, one_smul]
    rw [hsumModel Finset.univ,
      tensorInnerPointwise_sum_left (I := I) (M := M) g 0 s x Finset.univ
        (fun a => TensorRSSpace.toModel (Elt (V a) (V b) x)) (fun _ => (1 : ℝ))
        (TensorRSSpace.toModel (bochnerGradSlot0 (I := I) (M := M) g s S (V b) x))]
    simp
  · -- The slot-`0` Parseval expansion of the integrand, pushed under the integral.
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    change tensorInnerPointwise (I := I) (M := M) g 0 (s + 1) x (Named.toFun x)
        ((covGrad (I := I) (M := M) g 0 s S).toFun x) = _
    rw [show (Named).toFun x = TensorRSSpace.toModel (Named.toSection x) from rfl,
      show (covGrad (I := I) (M := M) g 0 s S).toFun x =
        TensorRSSpace.toModel ((covGrad (I := I) (M := M) g 0 s S).toSection x) from rfl]
    rw [tensorInnerPointwise_succ_eq_parseval_sum_slot0 (I := I) (M := M) g V hPar s x
      (Named.toSection x) ((covGrad (I := I) (M := M) g 0 s S).toSection x)]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rfl

/-- The slot-`0` `u'`-read value of `∇S` as a `(0, s)`-fibre element `slot0_{u'}(∇S) :=
tensor0S_curry s x (∇S(x)(unit)) u'`, used as the curvature operand. -/
private noncomputable def gradCurry0 (g : SmoothRiemannianMetric I M) (s : ℕ)
    (S : SmoothCcTensor g 0 s) (x : M) (u' : TangentSpace I x) : Tensor0SSpace s I x :=
  (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x
    ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
      (covGrad (I := I) (M := M) g 0 s S).toSection x)
      (unitZeroSec (I := I) (M := M) x))) u'

set_option linter.unusedSectionVars false in
/-- `unitScalarRSLift x (W(unit)) = W` for any `(0, s)`-Hom tensor `W`: a `(0, s)`-Hom is
determined by its unit-evaluation. -/
private lemma unitScalarRSLift_unitEval_self {s : ℕ} (x : M) (W : TensorRSSpace 0 s I x) :
    unitScalarRSLift (I := I) (M := M) x
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from W)
          (unitZeroSec (I := I) (M := M) x)) = W := by
  apply tensorRSSpace_ext (𝕜 := ℝ) 0 s x
  intro D
  rw [unitScalarRSLift_apply (I := I) (M := M) x _ D]
  conv_rhs => rw [zeroTensor_eq_smul_unit (I := I) (M := M) x D]
  rw [ContinuousLinearMap.map_smul]

set_option linter.unusedSectionVars false in
/-- **The genuine fold-`1` slot-`0` identity (pure-Riemann frame trace, Parseval form).** The
slot-`0` `V b`-read of the concrete pure-Riemann section `GcurvSection g s S` is the
Parseval-family sum over `a` of the group-`1` carrier `R(V a, V b)(∇_{V a} S)`. The orthonormal
moving-frame trace value of the order-`0` pure-Riemann curvature operator
(`pureRGenuineDiffOp_zero_succ_toSection_unit_eval`, folded back to the section through
`pureRGenuineDiffOp0_eq_GcurvSection`) is converted to the fixed family by
`parseval_family_sum_bilin_eq` applied to the slot-`0`-read curvature bilinear, then identified
with the carrier through `riemannOp_tensorCov_unitScalarRSLift_unitEval` and the directional
slot-`0` curry `curry_covGrad_unit_eval_genVal`. -/
private lemma gcurv_slot0_eq_parseval_sum_elt1
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s)
    {N : ℕ} (V : Fin N → Π b : M, TangentSpace I b)
    (hV : ∀ a, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => (⟨b, V a b⟩ : TotalSpace E (TangentSpace I))))
    (hPar : ∀ (x : M) (u : TangentSpace I x),
      (∑ a : Fin N, g.inner x (V a x) u • V a x) = u) (b : Fin N) (x : M) :
    tensor0SAsRS (I := I) (M := M) x
        ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
            (GcurvSection (I := I) (M := M) g s S).toSection x)
            (unitZeroSec (I := I) (M := M) x))) (V b x)) =
      ∑ a : Fin N, bochnerGroupElt1 (I := I) (M := M) g s S (V a) (V b) x := by
  classical
  -- Push the family sum and the wrapper out; reduce to a `Tensor0SSpace s` identity.
  rw [show (∑ a : Fin N, bochnerGroupElt1 (I := I) (M := M) g s S (V a) (V b) x) =
      tensor0SAsRS (I := I) (M := M) x
        (∑ a : Fin N,
          (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
            riemannSec (tensorCov (I := I) g 0 s) (V a) (V b)
              (covApply (tensorCov (I := I) g 0 s) (V a) (fun y : M => S.toSection y)) x)
            (unitZeroSec (I := I) (M := M) x)) from by
    rw [tensor0SAsRS_finsetSum (I := I) (M := M) s x Finset.univ]
    rfl]
  rw [tensor0SAsRS_eq_iff]
  -- Both sides are `Tensor0SSpace s`; compare on every model tuple `m`.
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro m
  simp only []
  -- LHS value: the curry reads slot 0 at `V b x` of the unit-evaluated section.
  rw [TensorMultilinear.tensor0S_curry_apply_eval]
  -- Replace `GcurvSection` by the order-`0` pure-Riemann operator on `∇S`.
  rw [show (GcurvSection (I := I) (M := M) g s S).toSection x =
      (pureRGenuineDiffOp (I := I) (M := M) g 0 (s + 1)
        (covGrad (I := I) (M := M) g 0 s S)).toSection x from by
    rw [pureRGenuineDiffOp0_eq_GcurvSection (I := I) (M := M) g s S]]
  rw [pureRGenuineDiffOp_zero_succ_toSection_unit_eval (I := I) (M := M) g s
    (covGrad (I := I) (M := M) g 0 s S) x (Fin.cons (V b x) m)]
  simp only [Fin.cons_zero, Matrix.vecTail]
  -- RHS value: pull `toModel` through the family sum, read on the tuple `m`.
  rw [show Tensor0SSpace.toModel
        (∑ a : Fin N,
          (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
            riemannSec (tensorCov (I := I) g 0 s) (V a) (V b)
              (covApply (tensorCov (I := I) g 0 s) (V a) (fun y : M => S.toSection y)) x)
            (unitZeroSec (I := I) (M := M) x)) m =
      ∑ a : Fin N, Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
          riemannSec (tensorCov (I := I) g 0 s) (V a) (V b)
            (covApply (tensorCov (I := I) g 0 s) (V a) (fun y : M => S.toSection y)) x)
          (unitZeroSec (I := I) (M := M) x)) m from by
    induction (Finset.univ : Finset (Fin N)) using Finset.induction with
    | empty => simp [Tensor0SSpace.toModel_zero]
    | insert i fs hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi, Tensor0SSpace.toModel_add,
        ContinuousMultilinearMap.add_apply, ih]]
  -- Express the RHS carrier value through the abstract `(0, s)`-curvature operator.
  rw [show (fun a : Fin N => Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
          riemannSec (tensorCov (I := I) g 0 s) (V a) (V b)
            (covApply (tensorCov (I := I) g 0 s) (V a) (fun y : M => S.toSection y)) x)
          (unitZeroSec (I := I) (M := M) x)) m) =
      (fun a : Fin N => Tensor0SSpace.toModel
        (riemannOp (Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g)) x
          (V a x) (V b x)
          (gradCurry0 (I := I) (M := M) g s S x (V a x))) m) from by
    funext a
    rw [riemannSec_eq_riemannOp_smooth (cov := tensorCov (I := I) g 0 s) (hV a) (hV b)
      (covApplyRS_contMDiff (I := I) g 0 s S.toSection.contMDiff (hV a))]
    rw [show covApply (tensorCov (I := I) g 0 s) (V a) (fun y : M => S.toSection y) x =
        unitScalarRSLift (I := I) (M := M) x (gradCurry0 (I := I) (M := M) g s S x (V a x)) from by
      rw [gradCurry0, curry_covGrad_unit_eval_genVal (I := I) (M := M) g s S x (V a x)]
      rw [show (tensorCovDerivAt (I := I) (M := M) g 0 s S x (V a x))
            (unitZeroSec (I := I) (M := M) x) =
          (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
            covApply (tensorCov (I := I) g 0 s) (V a) (fun y : M => S.toSection y) x)
            (unitZeroSec (I := I) (M := M) x) from by
        rw [covApply_apply]; rfl]
      rw [unitScalarRSLift_unitEval_self (I := I) (M := M) x _]]
    rw [riemannOp_tensorCov_unitScalarRSLift_unitEval (I := I) (M := M) g s x (V a x) (V b x)
      (gradCurry0 (I := I) (M := M) g s S x (V a x))]]
  -- Both sides are now `∑ … toModel (riemannOp(tensor0SCov) x · (V b x) (slot0_·(∇S))) m`;
  -- convert the orthonormal frame trace to the Parseval family by the bilinear trace identity.
  set Bform : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ :=
    LinearMap.mk₂ ℝ
      (fun u u' => Tensor0SSpace.toModel
        (riemannOp (Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g)) x
          u (V b x)
          ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x
            ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
              (covGrad (I := I) (M := M) g 0 s S).toSection x)
              (unitZeroSec (I := I) (M := M) x))) u')) m)
      (fun u₁ u₂ u' => by
        simp only [map_add, ContinuousLinearMap.add_apply, Tensor0SSpace.toModel_add,
          ContinuousMultilinearMap.add_apply])
      (fun c u u' => by
        simp only [map_smul, ContinuousLinearMap.smul_apply, Tensor0SSpace.toModel_smul,
          ContinuousMultilinearMap.smul_apply, smul_eq_mul])
      (fun u u₁' u₂' => by
        simp only [map_add, Tensor0SSpace.toModel_add, ContinuousMultilinearMap.add_apply])
      (fun c u u' => by
        simp only [map_smul, Tensor0SSpace.toModel_smul, ContinuousMultilinearMap.smul_apply,
          smul_eq_mul]) with hBform_def
  have hBval : ∀ u u' : TangentSpace I x, Bform u u' =
      Tensor0SSpace.toModel
        (riemannOp (Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g)) x
          u (V b x)
          ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x
            ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
              (covGrad (I := I) (M := M) g 0 s S).toSection x)
              (unitZeroSec (I := I) (M := M) x))) u')) m :=
    fun u u' => rfl
  have hparse := parseval_family_sum_bilin_eq (I := I) (M := M) g x (fun a => V a x)
    (fun u => hPar x u) (fun i => smoothOrthoFrame (I := I) g x i x)
    (fun i j => smoothOrthoFrame_orthonormal_at_center (I := I) g x i j) Bform
  simp only [hBval] at hparse
  exact hparse.symm

/-- **Fold 1 (term i → pure-Riemann genuine curvature trace pairing).** For a fixed Parseval frame family,
the group-`1` double sum (the slot-`0` carrier `R(V a, V b)(∇_{V a} S)`) equals the `L²` pairing of the
concrete pure-Riemann genuine curvature section `GcurvSection g s S` against `∇S`:
```
∑_a ∑_b ∫ ⟨R(V a, V b)(∇_{V a} S)·slot0, slot0_{V b}(∇S)⟩ = ⟨GcurvSection g s S, ∇S⟩_{L²}.
```
The genuine content is the fixed-family Parseval reproduction of the moving-frame pure-Riemann trace value
(`pureRGenuineDiffOp_zero_succ_toSection_unit_eval`), folded back to the concrete section through
`pureRGenuineDiffOp0_eq_GcurvSection` (`pureRGenuineDiffOp g 0 (s + 1) (∇S) = GcurvSection g s S`) and
converted to the fixed family by `parseval_family_sum_bilin_eq`. -/
theorem bochnerFold_group1_eq_GcurvSection
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s)
    {N : ℕ} (V : Fin N → Π b : M, TangentSpace I b)
    (hV : ∀ a, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => (⟨b, V a b⟩ : TotalSpace E (TangentSpace I))))
    (hPar : ∀ (x : M) (u : TangentSpace I x),
      (∑ a : Fin N, g.inner x (V a x) u • V a x) = u) :
    bochnerFoldGroupSum (I := I) (M := M) g s S V
        (bochnerGroupElt1 (I := I) (M := M) g s S) =
      tensorL2Inner (I := I) (M := M) g 0 (s + 1)
        (GcurvSection (I := I) (M := M) g s S).toFun
        (covGrad (I := I) (M := M) g 0 s S).toFun := by
  rw [(fold_assembly (I := I) (M := M) g s S V hV hPar (GcurvSection (I := I) (M := M) g s S)
    (bochnerGroupElt1 (I := I) (M := M) g s S)
    (fun b x => gcurv_slot0_eq_parseval_sum_elt1 (I := I) (M := M) g s S V hV hPar b x)
    (fun a b => by
      have hib := SmoothCcTensor.integrable_inner_cross (I := I) (M := M)
        (bochnerGroupElt1Cc (I := I) (M := M) g s S (hV a) (hV b))
        (bochnerGradSlot0Cc (I := I) (M := M) g s S (hV b))
      refine hib.congr (Filter.Eventually.of_forall (fun x => ?_))
      simp only [SmoothCcTensor.toFun_apply,
        bochnerGroupElt1Cc_toSection_eq (I := I) (M := M) g s S (hV a) (hV b) x,
        bochnerGradSlot0Cc_toSection_apply (I := I) (M := M) g s S (hV b) x])).symm]

/-- The packaged directional covariant derivative `∇_X T` of a smooth compactly-supported
`(0, s)`-tensor `T` along a smooth field `X`, as a smooth compactly-supported `(0, s)`-tensor
(`covApply (tensorCov g 0 s) X T`).  The general-`T` packaging through which the divergence
engine consumes the once-derived sections of the seven-term carriers. -/
private def covApplyGenCc (g : SmoothRiemannianMetric I M) (s : ℕ) (T : SmoothCcTensor g 0 s)
    {X : Π b : M, TangentSpace I b}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => (⟨b, X b⟩ : TotalSpace E (TangentSpace I)))) : SmoothCcTensor g 0 s where
  toSection :=
    { toFun := fun y : M => covApply (tensorCov (I := I) g 0 s) X
        (fun z : M => T.toSection z) y
      contMDiff_toFun := covApplyRS_contMDiff (I := I) g 0 s T.toSection.contMDiff hX }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

set_option linter.unusedSectionVars false in
@[simp] private lemma covApplyGenCc_toSection_apply (g : SmoothRiemannianMetric I M) (s : ℕ)
    (T : SmoothCcTensor g 0 s) {X : Π b : M, TangentSpace I b}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => (⟨b, X b⟩ : TotalSpace E (TangentSpace I)))) (y : M) :
    (covApplyGenCc (I := I) (M := M) g s T hX).toSection y =
      covApply (tensorCov (I := I) g 0 s) X (fun z : M => T.toSection z) y := rfl

/-- The packaged section-level Riemann curvature `R(X, Y) S` of a smooth compactly-supported
`(0, s)`-tensor `S` along smooth fields `X, Y`, as a smooth compactly-supported `(0, s)`-tensor
(`riemannSec (tensorCov g 0 s) X Y S`).  The group-`2` inner section the divergence engine
differentiates. -/
private def riemannSecCc (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s)
    {X Y : Π b : M, TangentSpace I b}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => (⟨b, X b⟩ : TotalSpace E (TangentSpace I))))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => (⟨b, Y b⟩ : TotalSpace E (TangentSpace I)))) : SmoothCcTensor g 0 s where
  toSection :=
    { toFun := fun x : M => riemannSec (tensorCov (I := I) g 0 s) X Y
        (fun z : M => S.toSection z) x
      contMDiff_toFun := riemannSec_contMDiff (cov := tensorCov (I := I) g 0 s) hX hY
        S.toSection.contMDiff }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

set_option linter.unusedSectionVars false in
@[simp] private lemma riemannSecCc_toSection_apply (g : SmoothRiemannianMetric I M) (s : ℕ)
    (S : SmoothCcTensor g 0 s) {X Y : Π b : M, TangentSpace I b}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => (⟨b, X b⟩ : TotalSpace E (TangentSpace I))))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => (⟨b, Y b⟩ : TotalSpace E (TangentSpace I)))) (x : M) :
    (riemannSecCc (I := I) (M := M) g s S hX hY).toSection x =
      riemannSec (tensorCov (I := I) g 0 s) X Y (fun z : M => S.toSection z) x := rfl

set_option linter.unusedSectionVars false in
/-- **The slot-`0` `V b`-read of `∇S` is the directional covariant derivative `∇_{V b} S`.** As a
`TensorRSSpace 0 s` value, `bochnerGradSlot0 g s S V b x` collapses through the gradient-slot read
`slotRead_covGrad_dir` to `covApply (tensorCov g 0 s) (V b) (S) (x)`, the section value of the
packaged directional derivative `covApplyGenCc g s S (hVb)`. -/
private lemma bochnerGradSlot0_eq_covApply (g : SmoothRiemannianMetric I M) (s : ℕ)
    (S : SmoothCcTensor g 0 s) (Vb : Π b : M, TangentSpace I b) (x : M) :
    bochnerGradSlot0 (I := I) (M := M) g s S Vb x =
      covApply (tensorCov (I := I) g 0 s) Vb (fun z : M => S.toSection z) x := by
  rw [bochnerGradSlot0, curry_covGrad_unit_eval_genVal (I := I) (M := M) g s S x (Vb x)]
  rw [show (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
        tensorCovDerivAt (I := I) (M := M) g 0 s S x (Vb x))
        (unitZeroSec (I := I) (M := M) x) =
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
        covApply (tensorCov (I := I) g 0 s) Vb (fun z : M => S.toSection z) x)
        (unitZeroSec (I := I) (M := M) x) from by
    rw [covApply_apply]; rfl]
  exact tensor0SAsRS_rs_unit' (I := I) (M := M) s x _

set_option linter.unusedSectionVars false in
/-- **The engine first-slot bridge (rank `(0, s)`).** For smooth compactly-supported `(0, s)`-tensors
`W'`, `Z` and a smooth field `V`, the engine's metric-lowered first-slot pairing
`⟨loweredCovDerivAlongVF g 0 s W' V, lifted Z⟩₀` equals the un-lowered directional covariant derivative
pairing `⟨∇_V W', Z⟩` in `tensorInnerPointwise (0, s)` form.  This is
`loweredCovDerivAlongVF_firstSlot_eq_lower_covApply` (`BracketDivergenceForm`) re-read against the
`(0, s)`-inner product through the lifted-section metric bridge
`tensorInnerPointwise_eq_liftedTensorSection_inner`, the `r = 0` index-lowering being the identity lift
`liftedTensorSection_apply`. -/
private lemma loweredFirstSlot_eq_covApply_inner (g : SmoothRiemannianMetric I M) (s : ℕ)
    (W' Z : SmoothCcTensor g 0 s) {V : Π b : M, TangentSpace I b}
    (hV : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => (⟨b, V b⟩ : TotalSpace E (TangentSpace I)))) (x : M) :
    tensorInnerPointwise_0s (I := I) (M := M) (0 + s) g x
        (Tensor0SSpace.toModel
          (loweredCovDerivAlongVF (I := I) (M := M) g 0 s W'.toSection ⟨fun y => V y, hV⟩ x))
        (Tensor0SSpace.toModel
          (liftedTensorSection (I := I) (M := M) g 0 s Z.toSection x)) =
      tensorInnerPointwise (I := I) (M := M) g 0 s x
        (TensorRSSpace.toModel
          ((covApplyGenCc (I := I) (M := M) g s W' hV).toSection x))
        (TensorRSSpace.toModel (Z.toSection x)) := by
  classical
  rw [loweredCovDerivAlongVF_firstSlot_eq_lower_covApply (I := I) (M := M) g 0 s W' Z
    ⟨fun y => V y, hV⟩ x]
  rw [tensorInnerPointwise_eq_liftedTensorSection_inner (I := I) (M := M) g 0 s
    (covApplyGenCc (I := I) (M := M) g s W' hV).toSection Z.toSection x]
  rw [liftedTensorSection_apply (I := I) (M := M) g 0 s
    (covApplyGenCc (I := I) (M := M) g s W' hV).toSection x, Tensor0SSpace.toModel_ofModel]
  rfl

/-- **The Parseval-frame curvature self-trace is the negated raised Ricci endomorphism.** For *any*
`g_x`-Parseval family `V a` (`∑_a ⟨V a, u⟩_g • V a = u`) and any tangent vector `w`, the frame self-trace
of the curvature endomorphism `Z ↦ R(V a, w) Z` evaluated on `V a` is the negated raised Ricci
endomorphism:
```
∑_a R(V a, w) (V a) = − ricEndoRaisedFib g x w.
```
Both sides have the same `g_x`-inner product with every test vector `W`: by the metric skew-symmetry of
the Riemann operator (`riemannOp_metric_skew`, `⟨R(v, w) Z, W⟩ + ⟨Z, R(v, w) W⟩ = 0`) each summand
`⟨R(V a, w)(V a), W⟩` is `−⟨V a, R(V a, w) W⟩`; the bilinear trace conversion
`parseval_family_sum_bilin_eq` rewrites the frame self-sum as the orthonormal `smoothOrthoFrame` trace,
and `smoothOrthoFrame_riemannOp_trace_eq_ricci` collapses it to `−Ric(w, W) = −⟨ricEndoRaisedFib w, W⟩`
(`inner_ricEndoRaisedFib`).  Nondegeneracy of `g_x` (`metricFlatMap` is a linear equivalence) upgrades
the inner-product equality to the vector identity.  This is GENERAL Parseval-frame curvature content that
should be promoted to a curvature file. -/
theorem parsevalFrame_sum_riemannOp_self_eq_neg_ricEndo
    (g : SmoothRiemannianMetric I M) (x : M) {N : ℕ} (V : Fin N → Π b : M, TangentSpace I b)
    (hPar : ∀ (u : TangentSpace I x), (∑ a : Fin N, g.inner x (V a x) u • V a x) = u)
    (w : TangentSpace I x) :
    (∑ a : Fin N, riemannOp (LeviCivita (I := I) g) x (V a x) w (V a x)) =
      - ricEndoRaisedFib (I := I) g x w := by
  classical
  -- It suffices that both sides pair identically with every test vector `W` (nondegeneracy of `g`).
  apply (DifferentialGeometry.Integral.DivergenceTheorem.metricFlatMap (I := I) g x).injective
  refine LinearMap.ext (fun W => ?_)
  rw [DifferentialGeometry.Integral.DivergenceTheorem.metricFlatMap_apply,
    DifferentialGeometry.Integral.DivergenceTheorem.metricFlatMap_apply]
  -- Left side: distribute the inner product over the finite sum.
  rw [map_sum (g.inner x) (fun a : Fin N => riemannOp (LeviCivita (I := I) g) x (V a x) w (V a x))
      Finset.univ, ContinuousLinearMap.sum_apply]
  -- Each summand `⟨R(V a, w)(V a), W⟩ = −⟨V a, R(V a, w) W⟩` by metric skew.
  have hskew : ∀ a : Fin N,
      g.inner x (riemannOp (LeviCivita (I := I) g) x (V a x) w (V a x)) W =
        - g.inner x (V a x) (riemannOp (LeviCivita (I := I) g) x (V a x) w W) := by
    intro a
    have h := riemannOp_metric_skew (I := I) g x (V a x) w (V a x) W
    linarith [h]
  rw [Finset.sum_congr rfl (fun a _ => hskew a)]
  rw [Finset.sum_neg_distrib]
  -- The bilinear self-trace `∑_a ⟨V a, R(V a, w) W⟩` equals the orthonormal `smoothOrthoFrame` trace.
  set B : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ :=
    { toFun := fun u =>
        { toFun := fun u' => g.inner x u (riemannOp (LeviCivita (I := I) g) x u' w W)
          map_add' := fun u₁ u₂ => by
            rw [show riemannOp (LeviCivita (I := I) g) x (u₁ + u₂) w W =
                riemannOp (LeviCivita (I := I) g) x u₁ w W +
                  riemannOp (LeviCivita (I := I) g) x u₂ w W from by
              rw [map_add]; rfl]
            rw [map_add]
          map_smul' := fun c u' => by
            simp only [RingHom.id_apply]
            rw [show riemannOp (LeviCivita (I := I) g) x (c • u') w W =
                c • riemannOp (LeviCivita (I := I) g) x u' w W from by
              rw [map_smul]; rfl]
            rw [map_smul] }
      map_add' := fun u₁ u₂ => by
        ext u'; simp [map_add]
      map_smul' := fun c u => by
        ext u'; simp [map_smul] } with hB
  have hBval : ∀ u u' : TangentSpace I x,
      B u u' = g.inner x u (riemannOp (LeviCivita (I := I) g) x u' w W) := fun u u' => rfl
  have hsum_eq : (∑ a : Fin N, g.inner x (V a x)
        (riemannOp (LeviCivita (I := I) g) x (V a x) w W)) =
      ∑ a : Fin N, B (V a x) (V a x) := by
    refine Finset.sum_congr rfl (fun a _ => ?_); rw [hBval]
  rw [hsum_eq]
  rw [parseval_family_sum_bilin_eq (I := I) (M := M) g x (fun a => V a x) hPar
    (fun i => smoothOrthoFrame (I := I) g x i x)
    (fun i j => smoothOrthoFrame_orthonormal_at_center (I := I) g x i j) B]
  -- The orthonormal self-trace `∑_i ⟨e i, R(e i, w) W⟩ = ∑_i ⟨R(e i, w) W, e i⟩` is `Ric(w, W)`.
  have htrace : ∀ i : Fin (Module.finrank ℝ E),
      B (smoothOrthoFrame (I := I) g x i x) (smoothOrthoFrame (I := I) g x i x) =
        g.inner x (riemannOp (LeviCivita (I := I) g) x
            (smoothOrthoFrame (I := I) g x i x) w W) (smoothOrthoFrame (I := I) g x i x) := by
    intro i
    rw [hBval, g.symm x (smoothOrthoFrame (I := I) g x i x) _]
  rw [Finset.sum_congr rfl (fun i _ => htrace i),
    smoothOrthoFrame_riemannOp_trace_eq_ricci (I := I) (M := M) g x w W]
  rw [map_neg (g.inner x) (ricEndoRaisedFib (I := I) g x w), ContinuousLinearMap.neg_apply,
    inner_ricEndoRaisedFib (I := I) (M := M) g x w W]

/-- **The Ricci-direction (term v) carrier frame-sum is the leading-slot Ricci trace, pointwise.** For a
fixed Parseval frame family, the slot-`0` `V b`-read of the leading-slot Ricci-trace carrier
`ricTraceSection g s S` is the Parseval-family sum over `a` of the Ricci-direction carrier
`bochnerGroupElt3NegV` (`= −∇_{R(V a, V b) V a} S`):
```
tensor0SAsRS x (slot0_{V b}(ricTraceSection g s S)(x)) = ∑_a bochnerGroupElt3NegV g s S (V a) (V b) x.
```
This is the genuinely-pointwise (after the frame sum over `a`) Bochner–Lichnerowicz Ricci content: the
frame self-trace `∑_a R(V a, V b) (V a) = −ricEndoRaisedFib g x (V b)`
(`parsevalFrame_sum_riemannOp_self_eq_neg_ricEndo`), pushed through the direction-linearity of the
covariant derivative, makes the term-v frame sum the covariant derivative of `S` in the raised-Ricci
direction `ricEndoRaisedFib g x (V b)`, which is exactly the leading slot of `ricTraceSection`
(`ricTraceSection_apply_leadingSlot`). -/
private theorem parsevalFrameSum_ricSlot0_eq_sum_negV
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s)
    {N : ℕ} (V : Fin N → Π b : M, TangentSpace I b)
    (hPar : ∀ (x : M) (u : TangentSpace I x),
      (∑ a : Fin N, g.inner x (V a x) u • V a x) = u) (b : Fin N) (x : M) :
    tensor0SAsRS (I := I) (M := M) x
        ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
            (ricTraceSection (I := I) (M := M) g s S).toSection x)
            (unitZeroSec (I := I) (M := M) x))) (V b x)) =
      ∑ a : Fin N, bochnerGroupElt3NegV (I := I) (M := M) g s S (V a) (V b) x := by
  classical
  -- The frame self-trace identity for the direction `V b`.
  have hric : (∑ a : Fin N, riemannOp (LeviCivita (I := I) g) x (V a x) (V b x) (V a x)) =
      - ricEndoRaisedFib (I := I) g x (V b x) :=
    parsevalFrame_sum_riemannOp_self_eq_neg_ricEndo (I := I) (M := M) g x V (hPar x) (V b x)
  -- The right side: each carrier is `−∇_{R(V a, V b) V a} S` read on the unit; wrap-distribute the sum.
  have hRHS : (∑ a : Fin N, bochnerGroupElt3NegV (I := I) (M := M) g s S (V a) (V b) x) =
      tensor0SAsRS (I := I) (M := M) x
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
          (tensorCov (I := I) g 0 s).toFun (fun y : M => S.toSection y) x
            (ricEndoRaisedFib (I := I) g x (V b x)))
          (unitZeroSec (I := I) (M := M) x)) := by
    rw [show (∑ a : Fin N, bochnerGroupElt3NegV (I := I) (M := M) g s S (V a) (V b) x) =
        ∑ a : Fin N, tensor0SAsRS (I := I) (M := M) x
          (- (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
              (tensorCov (I := I) g 0 s).toFun (fun y : M => S.toSection y) x
                (riemannOp (LeviCivita (I := I) g) x (V a x) (V b x) (V a x)))
              (unitZeroSec (I := I) (M := M) x)) from rfl]
    rw [← tensor0SAsRS_finsetSum]
    congr 1
    rw [show (∑ a : Fin N, - (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
            (tensorCov (I := I) g 0 s).toFun (fun y : M => S.toSection y) x
              (riemannOp (LeviCivita (I := I) g) x (V a x) (V b x) (V a x)))
            (unitZeroSec (I := I) (M := M) x)) =
        - (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
            (tensorCov (I := I) g 0 s).toFun (fun y : M => S.toSection y) x
              (∑ a : Fin N, riemannOp (LeviCivita (I := I) g) x (V a x) (V b x) (V a x)))
            (unitZeroSec (I := I) (M := M) x) from ?_]
    · rw [hric, map_neg, ContinuousLinearMap.neg_apply, neg_neg]
    · rw [map_sum, ContinuousLinearMap.sum_apply, Finset.sum_neg_distrib]
  rw [hRHS, tensor0SAsRS_eq_iff]
  -- The remaining `(0, s)`-fibre equality, read through `Tensor0SSpace.toModel` injectivity.
  apply Tensor0SSpace.toModel_injective
  ext m
  -- Left: `ricTraceSection` slot-0 read at `V b` is `∇S` with leading slot `ricEndo (V b)`.
  rw [TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M) (n := s)
    ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
      (ricTraceSection (I := I) (M := M) g s S).toSection x)
      (unitZeroSec (I := I) (M := M) x)) (V b x) m,
    ricTraceSection_apply_leadingSlot (I := I) (M := M) g s S x (V b x) m]
  -- Right: `∇_{ricEndo (V b)} S` on the unit, read at `m`, folded into the leading slot of `∇S`.
  have hRcarrier : (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
        (tensorCov (I := I) g 0 s).toFun (fun y : M => S.toSection y) x
          (ricEndoRaisedFib (I := I) g x (V b x)))
        (unitZeroSec (I := I) (M := M) x) =
      (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
          (covGrad (I := I) (M := M) g 0 s S).toSection x)
          (unitZeroSec (I := I) (M := M) x))) (ricEndoRaisedFib (I := I) g x (V b x)) :=
    (curry_covGrad_unit_eval_genVal (I := I) (M := M) g s S x
      (ricEndoRaisedFib (I := I) g x (V b x))).symm
  rw [hRcarrier,
    TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M) (n := s)
      ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
        (covGrad (I := I) (M := M) g 0 s S).toSection x)
        (unitZeroSec (I := I) (M := M) x)) (ricEndoRaisedFib (I := I) g x (V b x)) m]

/-- **The group-`2` IBP residual integrand** (in `tensorInnerPointwise` form): the lower-order
two-term residue `−(⟨R(V a, V b) S, ∇_{V a}(∇_{V b} S)⟩ + ⟨R(V a, V b) S, ∇_{V b} S⟩ · divᵍ (V a))` of
the frame-summed covariant integration by parts of the group-`2` carrier `∇_{V a}(R(V a, V b) S)`
against the slot-`0` carrier `∇_{V b} S`.  `∇_{V a}(∇_{V b} S) := covApply (V a)(covApply (V b) S)`,
and `divᵍ (V a)` reads the bundled frame field `Vfield`. -/
private noncomputable def bochnerGroup2Residue (g : SmoothRiemannianMetric I M) (s : ℕ)
    (S : SmoothCcTensor g 0 s) (Va Vb : Π b : M, TangentSpace I b)
    (Vfield : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) : ℝ :=
  - (tensorInnerPointwise (I := I) (M := M) g 0 s x
        (TensorRSSpace.toModel
          (riemannSec (tensorCov (I := I) g 0 s) Va Vb (fun z : M => S.toSection z) x))
        (TensorRSSpace.toModel
          (covApply (tensorCov (I := I) g 0 s) Va
            (fun z : M => covApply (tensorCov (I := I) g 0 s) Vb
              (fun w : M => S.toSection w) z) x))
      + tensorInnerPointwise (I := I) (M := M) g 0 s x
          (TensorRSSpace.toModel
            (riemannSec (tensorCov (I := I) g 0 s) Va Vb (fun z : M => S.toSection z) x))
          (TensorRSSpace.toModel
            (covApply (tensorCov (I := I) g 0 s) Vb (fun z : M => S.toSection z) x))
        * DifferentialGeometry.Integral.DivergenceTheorem.divergence_g (I := I) g Vfield x)

set_option linter.unusedSectionVars false in
/-- **The engine first-slot term equals the group-`2` carrier pairing integrand.** For the
once-derived inner section `W' := R(V a, V b) S` (`riemannSecCc`), the bundled frame field
`⟨V a, hV a⟩`, and the slot-`0` carrier `Z := ∇_{V b} S` (`bochnerGradSlot0Cc`), the engine
first slot `⟨∇_{V a}(R(V a, V b) S), ∇_{V b} S⟩` (`loweredFirstSlot_eq_covApply_inner`) is exactly the
group-`2` `bochnerFoldGroupSum` integrand `⟨bochnerGroupElt2, bochnerGradSlot0⟩`. -/
private lemma engineFirstSlot_eq_group2_integrand (g : SmoothRiemannianMetric I M) (s : ℕ)
    (S : SmoothCcTensor g 0 s) {N : ℕ} (V : Fin N → Π b : M, TangentSpace I b)
    (hV : ∀ a, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => (⟨b, V a b⟩ : TotalSpace E (TangentSpace I)))) (a b : Fin N) (x : M) :
    tensorInnerPointwise_0s (I := I) (M := M) (0 + s) g x
        (Tensor0SSpace.toModel
          (loweredCovDerivAlongVF (I := I) (M := M) g 0 s
            (riemannSecCc (I := I) (M := M) g s S (hV a) (hV b)).toSection
            ⟨fun y : M => V a y, hV a⟩ x))
        (Tensor0SSpace.toModel
          (liftedTensorSection (I := I) (M := M) g 0 s
            (bochnerGradSlot0Cc (I := I) (M := M) g s S (hV b)).toSection x)) =
      tensorInnerPointwise (I := I) (M := M) g 0 s x
        (TensorRSSpace.toModel (bochnerGroupElt2 (I := I) (M := M) g s S (V a) (V b) x))
        (TensorRSSpace.toModel (bochnerGradSlot0 (I := I) (M := M) g s S (V b) x)) := by
  classical
  rw [loweredFirstSlot_eq_covApply_inner (I := I) (M := M) g s
    (riemannSecCc (I := I) (M := M) g s S (hV a) (hV b))
    (bochnerGradSlot0Cc (I := I) (M := M) g s S (hV b)) (V := V a) (hV a) x]
  -- The first slot: `covApplyGenCc (riemannSecCc) (V a) = bochnerGroupElt2`; the second is `rfl`.
  rw [show (covApplyGenCc (I := I) (M := M) g s
        (riemannSecCc (I := I) (M := M) g s S (hV a) (hV b)) (hV a)).toSection x =
      (bochnerGroupElt2Cc (I := I) (M := M) g s S (hV a) (hV b)).toSection x from rfl,
    bochnerGroupElt2Cc_toSection_eq (I := I) (M := M) g s S (hV a) (hV b) x,
    bochnerGradSlot0Cc_toSection_apply (I := I) (M := M) g s S (hV b) x]

set_option linter.unusedSectionVars false in
/-- **The engine residual two terms equal the negated group-`2` IBP residue integrand.** The engine's
second slot `⟨R(V a, V b) S, ∇_{V a}(∇_{V b} S)⟩` (via `loweredFirstSlot_eq_covApply_inner` flipped by
`tensorInnerPointwise_symm`, with `∇_{V b} S = bochnerGradSlot0 = covApply (V b) S`) plus the divergence
term `⟨R(V a, V b) S, ∇_{V b} S⟩ · divᵍ (V a)` (via `tensorInnerScalar_apply`) is exactly
`−bochnerGroup2Residue`. -/
private lemma engineRest_eq_neg_group2Residue (g : SmoothRiemannianMetric I M) (s : ℕ)
    (S : SmoothCcTensor g 0 s) {N : ℕ} (V : Fin N → Π b : M, TangentSpace I b)
    (hV : ∀ a, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => (⟨b, V a b⟩ : TotalSpace E (TangentSpace I)))) (a b : Fin N) (x : M) :
    tensorInnerPointwise_0s (I := I) (M := M) (0 + s) g x
        (Tensor0SSpace.toModel
          (liftedTensorSection (I := I) (M := M) g 0 s
            (riemannSecCc (I := I) (M := M) g s S (hV a) (hV b)).toSection x))
        (Tensor0SSpace.toModel
          (loweredCovDerivAlongVF (I := I) (M := M) g 0 s
            (bochnerGradSlot0Cc (I := I) (M := M) g s S (hV b)).toSection
            ⟨fun y : M => V a y, hV a⟩ x))
      + tensorInnerScalar (I := I) (M := M) g 0 s
          (riemannSecCc (I := I) (M := M) g s S (hV a) (hV b)).toSection
          (bochnerGradSlot0Cc (I := I) (M := M) g s S (hV b)).toSection x
        * DifferentialGeometry.Integral.DivergenceTheorem.divergence_g (I := I) g
            ⟨fun y : M => V a y, hV a⟩ x =
      - bochnerGroup2Residue (I := I) (M := M) g s S (V a) (V b) ⟨fun y : M => V a y, hV a⟩ x := by
  classical
  -- The `gradSlot0Cc` section is the directional derivative `∇_{V b} S`, as a function.
  have hgrad : (bochnerGradSlot0Cc (I := I) (M := M) g s S (hV b)).toSection =
      fun z : M => covApply (tensorCov (I := I) g 0 s) (V b) (fun w : M => S.toSection w) z := by
    funext z
    rw [bochnerGradSlot0Cc_toSection_apply (I := I) (M := M) g s S (hV b) z,
      bochnerGradSlot0_eq_covApply (I := I) (M := M) g s S (V b) z]
  rw [bochnerGroup2Residue]
  -- Term `T3` (divergence scalar) via `tensorInnerScalar_apply`.
  rw [tensorInnerScalar_apply (I := I) (M := M) g 0 s]
  rw [show (riemannSecCc (I := I) (M := M) g s S (hV a) (hV b)).toSection x =
      riemannSec (tensorCov (I := I) g 0 s) (V a) (V b) (fun z : M => S.toSection z) x from rfl]
  rw [bochnerGradSlot0Cc_toSection_apply (I := I) (M := M) g s S (hV b) x,
    bochnerGradSlot0_eq_covApply (I := I) (M := M) g s S (V b) x]
  -- Term `T2` (second-slot covariant derivative): flip, first-slot bridge, flip back.
  rw [tensorInnerPointwise_0s_symm (I := I) (M := M) g x (0 + s) _ _]
  rw [loweredFirstSlot_eq_covApply_inner (I := I) (M := M) g s
    (bochnerGradSlot0Cc (I := I) (M := M) g s S (hV b))
    (riemannSecCc (I := I) (M := M) g s S (hV a) (hV b)) (V := V a) (hV a) x]
  rw [tensorInnerPointwise_symm (I := I) (M := M) g 0 s x _ _]
  rw [show (covApplyGenCc (I := I) (M := M) g s
        (bochnerGradSlot0Cc (I := I) (M := M) g s S (hV b)) (hV a)).toSection x =
      covApply (tensorCov (I := I) g 0 s) (V a)
        (fun z : M => (bochnerGradSlot0Cc (I := I) (M := M) g s S (hV b)).toSection z) x from rfl]
  rw [show (riemannSecCc (I := I) (M := M) g s S (hV a) (hV b)).toSection x =
      riemannSec (tensorCov (I := I) g 0 s) (V a) (V b) (fun z : M => S.toSection z) x from rfl]
  rw [hgrad]
  ring

/-- The packaged second covariant directional derivative `∇_{V a}(∇_{V b} S)` as a smooth
compactly-supported `(0, s)`-tensor (`covApply (V a)(covApply (V b) S)`), the inner section paired
against `R(V a, V b) S` in the group-`2` IBP residue. -/
private def secondCovApplyCc (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s)
    {Va Vb : Π b : M, TangentSpace I b}
    (hVa : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => (⟨b, Va b⟩ : TotalSpace E (TangentSpace I))))
    (hVb : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => (⟨b, Vb b⟩ : TotalSpace E (TangentSpace I)))) : SmoothCcTensor g 0 s :=
  covApplyCc (I := I) (M := M) g s (covApplyCc (I := I) (M := M) g s S hVb) hVa

/-- The **genuine Hessian** `∇²_{V a, V b} S = ∇_{V a}(∇_{V b} S) − ∇_{∇_{V a} V b} S`
(`tensorSecondCovDeriv`) packaged as a smooth compactly-supported `(0, s)`-tensor.  Unlike the
iterated second derivative `secondCovApplyCc`, this carrier is tensorial (`C^∞(M)`-linear) in
**both** direction slots, so its Parseval double sums are frame-independent — the correct inner
section for the curvature/second-derivative cross pairing `I₂`. -/
private def crossHessianCc (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s)
    {Va Vb : Π b : M, TangentSpace I b}
    (hVa : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => (⟨b, Va b⟩ : TotalSpace E (TangentSpace I))))
    (hVb : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => (⟨b, Vb b⟩ : TotalSpace E (TangentSpace I)))) : SmoothCcTensor g 0 s where
  toSection :=
    { toFun := fun x : M =>
        tensorSecondCovDeriv (I := I) g 0 s Va Vb (fun y : M => S.toSection y) x
      contMDiff_toFun :=
        tensorSecondCovDeriv_offDiag_section_contMDiff (I := I) g s
          S.toSection.contMDiff hVa hVb }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

set_option linter.unusedSectionVars false in
/-- The group-`2` IBP residue integrand is integrable: it is `−(⟨R(V a, V b) S, ∇_{V a}(∇_{V b} S)⟩ +
⟨R(V a, V b) S, ∇_{V b} S⟩ · divᵍ (V a))`, a continuous function (sum of smooth inner-product scalars,
the divergence factor smooth by `divergence_g_contMDiff`) on the compact manifold. -/
private lemma integrable_bochnerGroup2Residue (g : SmoothRiemannianMetric I M) (s : ℕ)
    (S : SmoothCcTensor g 0 s) {N : ℕ} (V : Fin N → Π b : M, TangentSpace I b)
    (hV : ∀ a, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => (⟨b, V a b⟩ : TotalSpace E (TangentSpace I)))) (a b : Fin N) :
    Integrable
      (fun x : M =>
        bochnerGroup2Residue (I := I) (M := M) g s S (V a) (V b) ⟨fun y : M => V a y, hV a⟩ x)
      (riemannianVolumeMeasure (I := I) (M := M) g) := by
  classical
  have hcont1 : Continuous
      (fun x : M => tensorInnerScalar (I := I) (M := M) g 0 s
        (riemannSecCc (I := I) (M := M) g s S (hV a) (hV b)).toSection
        (secondCovApplyCc (I := I) (M := M) g s S (hV a) (hV b)).toSection x) :=
    (tensorInnerScalar_contMDiff (I := I) (M := M) g 0 s
      (riemannSecCc (I := I) (M := M) g s S (hV a) (hV b)).toSection
      (secondCovApplyCc (I := I) (M := M) g s S (hV a) (hV b)).toSection).continuous
  have hcont2 : Continuous
      (fun x : M => tensorInnerScalar (I := I) (M := M) g 0 s
        (riemannSecCc (I := I) (M := M) g s S (hV a) (hV b)).toSection
        (bochnerGradSlot0Cc (I := I) (M := M) g s S (hV b)).toSection x) :=
    (tensorInnerScalar_contMDiff (I := I) (M := M) g 0 s
      (riemannSecCc (I := I) (M := M) g s S (hV a) (hV b)).toSection
      (bochnerGradSlot0Cc (I := I) (M := M) g s S (hV b)).toSection).continuous
  have hdiv : Continuous
      (DifferentialGeometry.Integral.DivergenceTheorem.divergence_g (I := I) g
        ⟨fun y : M => V a y, hV a⟩) :=
    (DifferentialGeometry.Integral.DivergenceTheorem.divergence_g_contMDiff (I := I) g
      ⟨fun y : M => V a y, hV a⟩).continuous
  refine integrable_of_continuous_compactSpace (I := I) (M := M) g ?_
  refine Continuous.neg (Continuous.add ?_ (Continuous.mul ?_ hdiv))
  · refine hcont1.congr (fun x => ?_)
    rw [tensorInnerScalar_apply (I := I) (M := M) g 0 s]
    rw [show (secondCovApplyCc (I := I) (M := M) g s S (hV a) (hV b)).toSection x =
        covApply (tensorCov (I := I) g 0 s) (V a)
          (fun z : M => covApply (tensorCov (I := I) g 0 s) (V b)
            (fun w : M => S.toSection w) z) x from rfl]
    rfl
  · refine hcont2.congr (fun x => ?_)
    rw [tensorInnerScalar_apply (I := I) (M := M) g 0 s]
    rw [bochnerGradSlot0Cc_toSection_apply (I := I) (M := M) g s S (hV b) x,
      bochnerGradSlot0_eq_covApply (I := I) (M := M) g s S (V b) x]
    rfl

set_option linter.unusedSectionVars false in
/-- **The group-`2` frame-summed covariant integration by parts.** For a fixed Parseval frame family,
the group-`2` double sum (the slot-`0` carrier `∇_{V a}(R(V a, V b) S)` paired against `∇_{V b} S`)
equals the frame double sum of the IBP residue integrals:
```
bochnerFoldGroupSum g s S V (bochnerGroupElt2) = ∑_b ∑_a ∫ bochnerGroup2Residue.
```
For each fixed `b`, the frame-summed covariant integration-by-parts engine
`integral_frameSummed_covDeriv_combined_eq_zero` (`W a := R(V a, V b) S`, `Z := ∇_{V b} S`, direction
`V a`) gives `∑_a ∫ (⟨∇_{V a}(R(V a, V b) S), ∇_{V b} S⟩ + ⟨R(V a, V b) S, ∇_{V a}(∇_{V b} S)⟩ +
⟨R(V a, V b) S, ∇_{V b} S⟩ · divᵍ (V a)) = 0`; the first term is the group-`2` integrand
(`engineFirstSlot_eq_group2_integrand`) and the remaining two are `−bochnerGroup2Residue`
(`engineRest_eq_neg_group2Residue`), so the group-`2` integral equals the residue integral. -/
private lemma bochnerFoldGroupSum_elt2_eq_residueSum (g : SmoothRiemannianMetric I M) (s : ℕ)
    (S : SmoothCcTensor g 0 s) {N : ℕ} (V : Fin N → Π b : M, TangentSpace I b)
    (hV : ∀ a, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => (⟨b, V a b⟩ : TotalSpace E (TangentSpace I)))) :
    bochnerFoldGroupSum (I := I) (M := M) g s S V
        (bochnerGroupElt2 (I := I) (M := M) g s S) =
      ∑ b : Fin N, ∑ a : Fin N,
        ∫ x, bochnerGroup2Residue (I := I) (M := M) g s S (V a) (V b)
            ⟨fun y : M => V a y, hV a⟩ x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  classical
  rw [bochnerFoldGroupSum, Finset.sum_comm]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  -- Integrability of the group-`2` integrand for each `a` (the Cc cross-pairing).
  have hintG2 : ∀ a : Fin N, Integrable
      (fun x : M => tensorInnerPointwise (I := I) (M := M) g 0 s x
        (TensorRSSpace.toModel (bochnerGroupElt2 (I := I) (M := M) g s S (V a) (V b) x))
        (TensorRSSpace.toModel (bochnerGradSlot0 (I := I) (M := M) g s S (V b) x)))
      (riemannianVolumeMeasure (I := I) (M := M) g) := by
    intro a
    refine (SmoothCcTensor.integrable_inner_cross (I := I) (M := M)
      (bochnerGroupElt2Cc (I := I) (M := M) g s S (hV a) (hV b))
      (bochnerGradSlot0Cc (I := I) (M := M) g s S (hV b))).congr
      (Filter.Eventually.of_forall (fun x => ?_))
    simp only [SmoothCcTensor.toFun_apply,
      bochnerGroupElt2Cc_toSection_eq (I := I) (M := M) g s S (hV a) (hV b) x,
      bochnerGradSlot0Cc_toSection_apply (I := I) (M := M) g s S (hV b) x]
  -- The engine identity for fixed `b`.
  have heng := integral_frameSummed_covDeriv_combined_eq_zero (I := I) (M := M) g 0 s
    (fun a : Fin N => (⟨fun y : M => V a y, hV a⟩ : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯))
    (fun a : Fin N => riemannSecCc (I := I) (M := M) g s S (hV a) (hV b))
    (bochnerGradSlot0Cc (I := I) (M := M) g s S (hV b))
  -- Rewrite the engine's per-`a` integrand pointwise as `group2integrand − residue`.
  have hpt : ∀ a : Fin N, ∀ x : M,
      tensorInnerPointwise_0s (I := I) (M := M) (0 + s) g x
            (Tensor0SSpace.toModel
              (loweredCovDerivAlongVF (I := I) (M := M) g 0 s
                (riemannSecCc (I := I) (M := M) g s S (hV a) (hV b)).toSection
                ⟨fun y : M => V a y, hV a⟩ x))
            (Tensor0SSpace.toModel
              (liftedTensorSection (I := I) (M := M) g 0 s
                (bochnerGradSlot0Cc (I := I) (M := M) g s S (hV b)).toSection x))
          + tensorInnerPointwise_0s (I := I) (M := M) (0 + s) g x
              (Tensor0SSpace.toModel
                (liftedTensorSection (I := I) (M := M) g 0 s
                  (riemannSecCc (I := I) (M := M) g s S (hV a) (hV b)).toSection x))
              (Tensor0SSpace.toModel
                (loweredCovDerivAlongVF (I := I) (M := M) g 0 s
                  (bochnerGradSlot0Cc (I := I) (M := M) g s S (hV b)).toSection
                  ⟨fun y : M => V a y, hV a⟩ x))
          + tensorInnerScalar (I := I) (M := M) g 0 s
              (riemannSecCc (I := I) (M := M) g s S (hV a) (hV b)).toSection
              (bochnerGradSlot0Cc (I := I) (M := M) g s S (hV b)).toSection x
            * DifferentialGeometry.Integral.DivergenceTheorem.divergence_g (I := I) g
                ⟨fun y : M => V a y, hV a⟩ x =
        tensorInnerPointwise (I := I) (M := M) g 0 s x
            (TensorRSSpace.toModel (bochnerGroupElt2 (I := I) (M := M) g s S (V a) (V b) x))
            (TensorRSSpace.toModel (bochnerGradSlot0 (I := I) (M := M) g s S (V b) x))
          - bochnerGroup2Residue (I := I) (M := M) g s S (V a) (V b)
              ⟨fun y : M => V a y, hV a⟩ x := by
    intro a x
    have h1 := engineFirstSlot_eq_group2_integrand (I := I) (M := M) g s S V hV a b x
    have h2 := engineRest_eq_neg_group2Residue (I := I) (M := M) g s S V hV a b x
    linarith [h1, h2]
  -- Rewrite each engine integral via `hpt`, split into the difference of integrals.
  rw [Finset.sum_congr rfl (fun a _ =>
    MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (hpt a)))] at heng
  rw [Finset.sum_congr rfl (fun a _ =>
    MeasureTheory.integral_sub (hintG2 a)
      (integrable_bochnerGroup2Residue (I := I) (M := M) g s S V hV a b))] at heng
  rw [Finset.sum_sub_distrib] at heng
  linarith [heng]


/-- **The differentiated-curvature trace carrier (the `(∇R) S` content of the tension-field carrier),
packaged as a smooth compactly-supported `(0, s)`-tensor.** For a fixed Parseval frame family this is the
section value of the differentiated `(0, s)`-tensor curvature `(∇_{V a} R^{(s)})(V a, V b) S`
(`nablaTensor0SCurv g s (V a) (V a) (V b)` read on the unit), packaged through the *covariant-Leibniz
regrouping* as the sum of the tension-field curvature carrier `bochnerGroupElt3IiiIv` (terms iii + iv,
`R(∇_{V a} V b, V a) S + R(V b, ∇_{V a} V a) S`), the group-`2` carrier `bochnerGroupElt2`
(`∇_{V a}(R(V a, V b) S)`), minus the group-`1` carrier `bochnerGroupElt1` (`R(V a, V b)(∇_{V a} S)`).
The defining identity is the differentiated-curvature covariant Leibniz rule `nablaTensor0SCurv_def`
(`(∇_X R)(Y, Z) A = ∇_X(R(Y, Z) A) − R(∇_X Y, Z) A − R(Y, ∇_X Z) A − R(Y, Z)(∇_X A)`) at the derivation
slot `V a` with antisymmetric slots `(V a, V b)`, read through the section-level `riemannSec` antisymmetry;
this combination is smooth by construction (a finite sum of the three smooth carriers).  It is the carrier
whose Parseval-frame double-sum pairing against `∇S` is the `D` of the posited integrated covariant
IBP primitive `D = −(G₁ + I₂)`. -/
private def nablaDiffCurvTraceCc (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s)
    {Va Vb : Π b : M, TangentSpace I b}
    (hVa : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => (⟨b, Va b⟩ : TotalSpace E (TangentSpace I))))
    (hVb : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => (⟨b, Vb b⟩ : TotalSpace E (TangentSpace I)))) : SmoothCcTensor g 0 s :=
  (bochnerGroupElt3IiiIvCc (I := I) (M := M) g s S hVa hVb +
      bochnerGroupElt2Cc (I := I) (M := M) g s S hVa hVb) -
    bochnerGroupElt1Cc (I := I) (M := M) g s S hVa hVb

set_option linter.unusedSectionVars false in
/-- The differentiated-curvature trace carrier section value is the named regrouping
`bochnerGroupElt3IiiIv + bochnerGroupElt2 − bochnerGroupElt1`, pointwise. -/
private lemma nablaDiffCurvTraceCc_toSection_eq (g : SmoothRiemannianMetric I M) (s : ℕ)
    (S : SmoothCcTensor g 0 s) {Va Vb : Π b : M, TangentSpace I b}
    (hVa : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => (⟨b, Va b⟩ : TotalSpace E (TangentSpace I))))
    (hVb : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => (⟨b, Vb b⟩ : TotalSpace E (TangentSpace I)))) (x : M) :
    (nablaDiffCurvTraceCc (I := I) (M := M) g s S hVa hVb).toSection x =
      bochnerGroupElt3IiiIv (I := I) (M := M) g s S Va Vb x +
        bochnerGroupElt2 (I := I) (M := M) g s S Va Vb x -
        bochnerGroupElt1 (I := I) (M := M) g s S Va Vb x := by
  rw [nablaDiffCurvTraceCc, SmoothCcTensor.toSection_sub, SmoothCcTensor.toSection_add]
  simp only [ContMDiffSection.coe_sub, ContMDiffSection.coe_add, Pi.sub_apply, Pi.add_apply]
  rw [bochnerGroupElt3IiiIvCc_toSection_eq (I := I) (M := M) g s S hVa hVb x,
    bochnerGroupElt2Cc_toSection_eq (I := I) (M := M) g s S hVa hVb x,
    bochnerGroupElt1Cc_toSection_eq (I := I) (M := M) g s S hVa hVb x]

set_option linter.unusedSectionVars false in
/-- **The covariant-Leibniz regrouping of the tension-field carrier double sum (the system bridge).**
For a fixed Parseval frame family, the group-`3` tension-field double sum
`bochnerFoldGroupSum (bochnerGroupElt3IiiIv)` equals the differentiated-curvature trace double sum
`∑_a ∑_b ∫ ⟨nablaDiffCurvTrace, ∇_{V b} S⟩`, minus the group-`2` double sum
`bochnerFoldGroupSum (bochnerGroupElt2)`, plus the group-`1` double sum
`bochnerFoldGroupSum (bochnerGroupElt1)`:
```
bochnerFoldGroupSum (bochnerGroupElt3IiiIv)
  = (∑_a ∑_b ∫ ⟨nablaDiffCurvTrace, ∇_{V b} S⟩) − bochnerFoldGroupSum (bochnerGroupElt2)
      + bochnerFoldGroupSum (bochnerGroupElt1).
```
This is the integrated form of the pointwise covariant-Leibniz regrouping
`bochnerGroupElt3IiiIv = nablaDiffCurvTrace − bochnerGroupElt2 + bochnerGroupElt1`
(`nablaDiffCurvTraceCc_toSection_eq`, `nablaTensor0SCurv_def`), distributed over the per-`(a, b)` integral
by the pointwise left-additivity of the `(0, s)` inner product (`tensorInnerPointwise_add_left`) and the
per-carrier integrability of the cross pairings (`SmoothCcTensor.integrable_inner_cross`).  It re-expresses
the frame-derivative (`∇V`-in-a-curvature-slot) carrier in terms of the genuinely differentiated curvature
`∇R` (`nablaDiffCurvTrace`) plus the undifferentiated curvature carriers, the algebraic backbone of the
summed kernel chain over the proven primitive `D = −(G₁ + I₂)`.  It is general Parseval-frame
curvature content. -/
private lemma bochnerFoldGroupSum_elt3IiiIv_eq_nablaDiffCurvTrace_split
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s)
    {N : ℕ} (V : Fin N → Π b : M, TangentSpace I b)
    (hV : ∀ a, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => (⟨b, V a b⟩ : TotalSpace E (TangentSpace I)))) :
    bochnerFoldGroupSum (I := I) (M := M) g s S V
        (bochnerGroupElt3IiiIv (I := I) (M := M) g s S) =
      (∑ a : Fin N, ∑ b : Fin N,
          ∫ x, tensorInnerScalar (I := I) (M := M) g 0 s
              (nablaDiffCurvTraceCc (I := I) (M := M) g s S (hV a) (hV b)).toSection
              (bochnerGradSlot0Cc (I := I) (M := M) g s S (hV b)).toSection x
            ∂(riemannianVolumeMeasure (I := I) (M := M) g)) -
        bochnerFoldGroupSum (I := I) (M := M) g s S V
          (bochnerGroupElt2 (I := I) (M := M) g s S) +
        bochnerFoldGroupSum (I := I) (M := M) g s S V
          (bochnerGroupElt1 (I := I) (M := M) g s S) := by
  classical
  -- Per-`(a, b)` integrability of the tension-field, differentiated-curvature trace, group-`2`,
  -- group-`1` cross pairings.
  have hintIiiIv : ∀ a b : Fin N, Integrable
      (fun x : M => tensorInnerPointwise (I := I) (M := M) g 0 s x
        (TensorRSSpace.toModel (bochnerGroupElt3IiiIv (I := I) (M := M) g s S (V a) (V b) x))
        (TensorRSSpace.toModel (bochnerGradSlot0 (I := I) (M := M) g s S (V b) x)))
      (riemannianVolumeMeasure (I := I) (M := M) g) := by
    intro a b
    refine (SmoothCcTensor.integrable_inner_cross (I := I) (M := M)
      (bochnerGroupElt3IiiIvCc (I := I) (M := M) g s S (hV a) (hV b))
      (bochnerGradSlot0Cc (I := I) (M := M) g s S (hV b))).congr
      (Filter.Eventually.of_forall (fun x => ?_))
    simp only [SmoothCcTensor.toFun_apply,
      bochnerGroupElt3IiiIvCc_toSection_eq (I := I) (M := M) g s S (hV a) (hV b) x,
      bochnerGradSlot0Cc_toSection_apply (I := I) (M := M) g s S (hV b) x]
  have hintD : ∀ a b : Fin N, Integrable
      (fun x : M => tensorInnerScalar (I := I) (M := M) g 0 s
        (nablaDiffCurvTraceCc (I := I) (M := M) g s S (hV a) (hV b)).toSection
        (bochnerGradSlot0Cc (I := I) (M := M) g s S (hV b)).toSection x)
      (riemannianVolumeMeasure (I := I) (M := M) g) := fun a b =>
    SmoothCcTensor.integrable_inner_cross (I := I) (M := M)
      (nablaDiffCurvTraceCc (I := I) (M := M) g s S (hV a) (hV b))
      (bochnerGradSlot0Cc (I := I) (M := M) g s S (hV b))
  have hint2 : ∀ a b : Fin N, Integrable
      (fun x : M => tensorInnerPointwise (I := I) (M := M) g 0 s x
        (TensorRSSpace.toModel (bochnerGroupElt2 (I := I) (M := M) g s S (V a) (V b) x))
        (TensorRSSpace.toModel (bochnerGradSlot0 (I := I) (M := M) g s S (V b) x)))
      (riemannianVolumeMeasure (I := I) (M := M) g) := by
    intro a b
    refine (SmoothCcTensor.integrable_inner_cross (I := I) (M := M)
      (bochnerGroupElt2Cc (I := I) (M := M) g s S (hV a) (hV b))
      (bochnerGradSlot0Cc (I := I) (M := M) g s S (hV b))).congr
      (Filter.Eventually.of_forall (fun x => ?_))
    simp only [SmoothCcTensor.toFun_apply,
      bochnerGroupElt2Cc_toSection_eq (I := I) (M := M) g s S (hV a) (hV b) x,
      bochnerGradSlot0Cc_toSection_apply (I := I) (M := M) g s S (hV b) x]
  have hint1 : ∀ a b : Fin N, Integrable
      (fun x : M => tensorInnerPointwise (I := I) (M := M) g 0 s x
        (TensorRSSpace.toModel (bochnerGroupElt1 (I := I) (M := M) g s S (V a) (V b) x))
        (TensorRSSpace.toModel (bochnerGradSlot0 (I := I) (M := M) g s S (V b) x)))
      (riemannianVolumeMeasure (I := I) (M := M) g) := by
    intro a b
    refine (SmoothCcTensor.integrable_inner_cross (I := I) (M := M)
      (bochnerGroupElt1Cc (I := I) (M := M) g s S (hV a) (hV b))
      (bochnerGradSlot0Cc (I := I) (M := M) g s S (hV b))).congr
      (Filter.Eventually.of_forall (fun x => ?_))
    simp only [SmoothCcTensor.toFun_apply,
      bochnerGroupElt1Cc_toSection_eq (I := I) (M := M) g s S (hV a) (hV b) x,
      bochnerGradSlot0Cc_toSection_apply (I := I) (M := M) g s S (hV b) x]
  -- The pointwise integrand identity: `⟨group3IiiIv, ∇_{V b} S⟩ = ⟨nablaDiffCurvTrace, ∇_{V b} S⟩
  -- − ⟨group2, ∇_{V b} S⟩ + ⟨group1, ∇_{V b} S⟩`, from the carrier regrouping
  -- `nablaDiffCurvTrace = group3IiiIv + group2 − group1` and left-additivity of the inner product.
  have hpt : ∀ a b : Fin N, ∀ x : M,
      tensorInnerPointwise (I := I) (M := M) g 0 s x
          (TensorRSSpace.toModel (bochnerGroupElt3IiiIv (I := I) (M := M) g s S (V a) (V b) x))
          (TensorRSSpace.toModel (bochnerGradSlot0 (I := I) (M := M) g s S (V b) x)) =
        tensorInnerScalar (I := I) (M := M) g 0 s
            (nablaDiffCurvTraceCc (I := I) (M := M) g s S (hV a) (hV b)).toSection
            (bochnerGradSlot0Cc (I := I) (M := M) g s S (hV b)).toSection x -
          tensorInnerPointwise (I := I) (M := M) g 0 s x
            (TensorRSSpace.toModel (bochnerGroupElt2 (I := I) (M := M) g s S (V a) (V b) x))
            (TensorRSSpace.toModel (bochnerGradSlot0 (I := I) (M := M) g s S (V b) x)) +
          tensorInnerPointwise (I := I) (M := M) g 0 s x
            (TensorRSSpace.toModel (bochnerGroupElt1 (I := I) (M := M) g s S (V a) (V b) x))
            (TensorRSSpace.toModel (bochnerGradSlot0 (I := I) (M := M) g s S (V b) x)) := by
    intro a b x
    rw [tensorInnerScalar_apply (I := I) (M := M) g 0 s,
      bochnerGradSlot0Cc_toSection_apply (I := I) (M := M) g s S (hV b) x,
      nablaDiffCurvTraceCc_toSection_eq (I := I) (M := M) g s S (hV a) (hV b) x]
    rw [show (bochnerGroupElt3IiiIv (I := I) (M := M) g s S (V a) (V b) x +
            bochnerGroupElt2 (I := I) (M := M) g s S (V a) (V b) x -
            bochnerGroupElt1 (I := I) (M := M) g s S (V a) (V b) x) =
        (bochnerGroupElt3IiiIv (I := I) (M := M) g s S (V a) (V b) x +
            bochnerGroupElt2 (I := I) (M := M) g s S (V a) (V b) x) +
          (- bochnerGroupElt1 (I := I) (M := M) g s S (V a) (V b) x) from by abel,
      TensorRSSpace.toModel_add, TensorRSSpace.toModel_add, TensorRSSpace.toModel_neg,
      tensorInnerPointwise_add_left (I := I) (M := M) g 0 s x,
      tensorInnerPointwise_add_left (I := I) (M := M) g 0 s x,
      show (- TensorRSSpace.toModel (bochnerGroupElt1 (I := I) (M := M) g s S (V a) (V b) x)) =
          (-1 : ℝ) • TensorRSSpace.toModel (bochnerGroupElt1 (I := I) (M := M) g s S (V a) (V b) x) from by
        rw [neg_one_smul],
      tensorInnerPointwise_smul_left (I := I) (M := M) g 0 s x]
    ring
  -- Assemble: `bochnerFoldGroupSum` of each carrier is its double-sum integral; split each `(a, b)`
  -- integral additively (no `integral_sub`) by the regrouping `group3IiiIv + group2 = nablaDiffCurv
  -- + group1`, then reassociate the finite sums.
  -- Per-`(a, b)` additive integral identity: `∫⟨group3IiiIv⟩ + ∫⟨group2⟩ = ∫⟨nablaDiffCurv⟩ + ∫⟨group1⟩`.
  have hsplit : ∀ a b : Fin N,
      (∫ x, tensorInnerPointwise (I := I) (M := M) g 0 s x
            (TensorRSSpace.toModel (bochnerGroupElt3IiiIv (I := I) (M := M) g s S (V a) (V b) x))
            (TensorRSSpace.toModel (bochnerGradSlot0 (I := I) (M := M) g s S (V b) x))
          ∂(riemannianVolumeMeasure (I := I) (M := M) g)) +
        (∫ x, tensorInnerPointwise (I := I) (M := M) g 0 s x
              (TensorRSSpace.toModel (bochnerGroupElt2 (I := I) (M := M) g s S (V a) (V b) x))
              (TensorRSSpace.toModel (bochnerGradSlot0 (I := I) (M := M) g s S (V b) x))
            ∂(riemannianVolumeMeasure (I := I) (M := M) g)) =
        (∫ x, tensorInnerScalar (I := I) (M := M) g 0 s
              (nablaDiffCurvTraceCc (I := I) (M := M) g s S (hV a) (hV b)).toSection
              (bochnerGradSlot0Cc (I := I) (M := M) g s S (hV b)).toSection x
            ∂(riemannianVolumeMeasure (I := I) (M := M) g)) +
          (∫ x, tensorInnerPointwise (I := I) (M := M) g 0 s x
              (TensorRSSpace.toModel (bochnerGroupElt1 (I := I) (M := M) g s S (V a) (V b) x))
              (TensorRSSpace.toModel (bochnerGradSlot0 (I := I) (M := M) g s S (V b) x))
            ∂(riemannianVolumeMeasure (I := I) (M := M) g)) := by
    intro a b
    rw [← MeasureTheory.integral_add (hintIiiIv a b) (hint2 a b),
      ← MeasureTheory.integral_add (hintD a b) (hint1 a b)]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    -- `⟨group3IiiIv⟩ + ⟨group2⟩ = ⟨nablaDiffCurv⟩ + ⟨group1⟩` from `hpt` (which gives
    -- `⟨group3IiiIv⟩ = ⟨nablaDiffCurv⟩ − ⟨group2⟩ + ⟨group1⟩`).
    show tensorInnerPointwise (I := I) (M := M) g 0 s x
          (TensorRSSpace.toModel (bochnerGroupElt3IiiIv (I := I) (M := M) g s S (V a) (V b) x))
          (TensorRSSpace.toModel (bochnerGradSlot0 (I := I) (M := M) g s S (V b) x)) +
        tensorInnerPointwise (I := I) (M := M) g 0 s x
          (TensorRSSpace.toModel (bochnerGroupElt2 (I := I) (M := M) g s S (V a) (V b) x))
          (TensorRSSpace.toModel (bochnerGradSlot0 (I := I) (M := M) g s S (V b) x)) = _
    rw [hpt a b x]
    ring
  -- The group-`3` (iii + iv) double sum: rearrange `hsplit` to `∫⟨group3IiiIv⟩ = ∫⟨nablaDiffCurv⟩
  -- − ∫⟨group2⟩ + ∫⟨group1⟩`, sum over `(a, b)`, and identify the `bochnerFoldGroupSum`s.
  have hsplit' : ∀ a b : Fin N,
      (∫ x, tensorInnerPointwise (I := I) (M := M) g 0 s x
            (TensorRSSpace.toModel (bochnerGroupElt3IiiIv (I := I) (M := M) g s S (V a) (V b) x))
            (TensorRSSpace.toModel (bochnerGradSlot0 (I := I) (M := M) g s S (V b) x))
          ∂(riemannianVolumeMeasure (I := I) (M := M) g)) =
        (∫ x, tensorInnerScalar (I := I) (M := M) g 0 s
              (nablaDiffCurvTraceCc (I := I) (M := M) g s S (hV a) (hV b)).toSection
              (bochnerGradSlot0Cc (I := I) (M := M) g s S (hV b)).toSection x
            ∂(riemannianVolumeMeasure (I := I) (M := M) g)) -
          (∫ x, tensorInnerPointwise (I := I) (M := M) g 0 s x
              (TensorRSSpace.toModel (bochnerGroupElt2 (I := I) (M := M) g s S (V a) (V b) x))
              (TensorRSSpace.toModel (bochnerGradSlot0 (I := I) (M := M) g s S (V b) x))
            ∂(riemannianVolumeMeasure (I := I) (M := M) g)) +
          (∫ x, tensorInnerPointwise (I := I) (M := M) g 0 s x
              (TensorRSSpace.toModel (bochnerGroupElt1 (I := I) (M := M) g s S (V a) (V b) x))
              (TensorRSSpace.toModel (bochnerGradSlot0 (I := I) (M := M) g s S (V b) x))
            ∂(riemannianVolumeMeasure (I := I) (M := M) g)) :=
    fun a b => by linarith [hsplit a b]
  rw [bochnerFoldGroupSum, bochnerFoldGroupSum, bochnerFoldGroupSum]
  rw [Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => hsplit' a b))]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]

/-- **The Parseval-frame covariant-derivative relation (the differentiated cometric, scalar
bilinear-paired form).** For a fixed smooth Parseval frame family `V a` (`hPar`: the cometric
reproduction `∑_a ⟨V_a, ·⟩_g V_a = id`, i.e. `∑_a V_a ⊗ V_a = g⁻¹`), smooth tangent fields `U, P`,
a smooth direction field `W`, and a point `x`, the Parseval frame's covariant-derivative diagonal is
antisymmetric in the two frame slots:
```
∑_a [ ⟨∇_{W} V_a, U⟩_g · ⟨V_a, P⟩_g + ⟨V_a, U⟩_g · ⟨∇_{W} V_a, P⟩_g ] = 0,
```
where `∇_{W} V_a = (LeviCivita g).toFun (V a) x (W x)` is the Levi-Civita covariant derivative of the
frame field `V a` in the direction `W x`.

This is the genuine cometric-parallel core `∇(g⁻¹) = 0` read on the *fixed* Parseval frame: the field
identity `∑_a ⟨V_a(y), U(y)⟩_g · ⟨V_a(y), P(y)⟩_g = ⟨U(y), P(y)⟩_g` (`parseval_family_inner_mul_sum`,
the dual-Parseval reproduction at every `y`) differentiated in the direction `W` at `x`; the
metric-compatibility Leibniz rule (`LeviCivita_isMetricCompatible`) distributes the derivative across
each inner-product factor, and the two `∇_W U` / `∇_W P` summands recombine — through the same
dual-Parseval reproduction at `x` — into the derivative of the right side `⟨∇_W U, P⟩_g + ⟨U, ∇_W P⟩_g`,
which cancels, leaving exactly the frame-derivative antisymmetry above.

It is **non-vacuous**: with `U = P` it asserts `∑_a ⟨∇_W V_a, U⟩_g ⟨V_a, U⟩_g = 0`, the genuine
statement that the background cometric `∑_a V_a ⊗ V_a` is `∇`-parallel (false for a non-parallel
ambient frame, e.g. a coordinate frame on a curved torus). This is GENERAL Parseval-frame content that
should be promoted to a curvature/frame file. -/
private theorem parsevalFrame_sum_covDeriv_inner_antisymm
    (g : SmoothRiemannianMetric I M)
    {N : ℕ} (V : Fin N → Π b : M, TangentSpace I b)
    (hV : ∀ a, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => (⟨b, V a b⟩ : TotalSpace E (TangentSpace I))))
    (hPar : ∀ (x : M) (u : TangentSpace I x),
      (∑ a : Fin N, g.inner x (V a x) u • V a x) = u)
    {U P W : Π b : M, TangentSpace I b}
    (hU : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => (⟨b, U b⟩ : TotalSpace E (TangentSpace I))))
    (hP : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => (⟨b, P b⟩ : TotalSpace E (TangentSpace I)))) (x : M) :
    (∑ a : Fin N,
        (g.inner x ((LeviCivita (I := I) g).toFun (V a) x (W x)) (U x)
            * g.inner x (V a x) (P x)
          + g.inner x (V a x) (U x)
            * g.inner x ((LeviCivita (I := I) g).toFun (V a) x (W x)) (P x))) = 0 := by
  classical
  -- The dual-Parseval reproduction at every point: `∑_a ⟨V_a, U⟩ ⟨V_a, P⟩ = ⟨U, P⟩`, as a field.
  have hfield : (fun y : M => ∑ a : Fin N,
        g.inner y (V a y) (U y) * g.inner y (V a y) (P y)) =
      (fun y : M => g.inner y (U y) (P y)) := by
    funext y
    exact parseval_family_inner_mul_sum (I := I) (M := M) g y (fun a => V a y)
      (fun u => hPar y u) (U y) (P y)
  -- Smoothness/differentiability of each scalar factor `b ↦ ⟨V_a, U⟩` etc.
  have hmcU : ∀ a : Fin N,
      (mfderiv I 𝓘(ℝ, ℝ) (fun b : M => g.inner b (V a b) (U b)) x) (W x) =
        g.inner x ((LeviCivita (I := I) g).toFun (V a) x (W x)) (U x)
          + g.inner x (V a x) ((LeviCivita (I := I) g).toFun U x (W x)) := fun a =>
    (LeviCivita_isMetricCompatible (I := I) g).apply (Y := V a) (Z := U)
      ((hV a).mdifferentiableAt (by simp)) (hU.mdifferentiableAt (by simp)) (W x)
  have hmcP : ∀ a : Fin N,
      (mfderiv I 𝓘(ℝ, ℝ) (fun b : M => g.inner b (V a b) (P b)) x) (W x) =
        g.inner x ((LeviCivita (I := I) g).toFun (V a) x (W x)) (P x)
          + g.inner x (V a x) ((LeviCivita (I := I) g).toFun P x (W x)) := fun a =>
    (LeviCivita_isMetricCompatible (I := I) g).apply (Y := V a) (Z := P)
      ((hV a).mdifferentiableAt (by simp)) (hP.mdifferentiableAt (by simp)) (W x)
  have hmcUP :
      (mfderiv I 𝓘(ℝ, ℝ) (fun b : M => g.inner b (U b) (P b)) x) (W x) =
        g.inner x ((LeviCivita (I := I) g).toFun U x (W x)) (P x)
          + g.inner x (U x) ((LeviCivita (I := I) g).toFun P x (W x)) :=
    (LeviCivita_isMetricCompatible (I := I) g).apply (Y := U) (Z := P)
      (hU.mdifferentiableAt (by simp)) (hP.mdifferentiableAt (by simp)) (W x)
  -- Smoothness of the per-`a` scalar factors (for the product rule and the finite-sum rule).
  have hsmU : ∀ a : Fin N, ContMDiff I 𝓘(ℝ) ∞ (fun b : M => g.inner b (V a b) (U b)) := fun a =>
    DifferentialGeometry.Integral.DivergenceTheorem.contMDiff_g_inner_of_smooth_sections
      (I := I) (M := M) g (ContMDiffSection.mk (V a) (hV a)) (ContMDiffSection.mk U hU)
  have hsmP : ∀ a : Fin N, ContMDiff I 𝓘(ℝ) ∞ (fun b : M => g.inner b (V a b) (P b)) := fun a =>
    DifferentialGeometry.Integral.DivergenceTheorem.contMDiff_g_inner_of_smooth_sections
      (I := I) (M := M) g (ContMDiffSection.mk (V a) (hV a)) (ContMDiffSection.mk P hP)
  -- The explicit per-`a` factor derivatives, ascribed to `ℝ`-codomain CLMs (uniform frame sum).
  set dU : Fin N → (TangentSpace I x →L[ℝ] ℝ) :=
    fun a => (mfderiv I 𝓘(ℝ, ℝ) (fun b : M => g.inner b (V a b) (U b)) x :
      TangentSpace I x →L[ℝ] ℝ) with hdU_def
  set dP : Fin N → (TangentSpace I x →L[ℝ] ℝ) :=
    fun a => (mfderiv I 𝓘(ℝ, ℝ) (fun b : M => g.inner b (V a b) (P b)) x :
      TangentSpace I x →L[ℝ] ℝ) with hdP_def
  -- The explicit per-`a` Leibniz derivative CLM (typed into `ℝ` to keep the frame sum uniform).
  set D : Fin N → (TangentSpace I x →L[ℝ] ℝ) :=
    fun a => g.inner x (V a x) (U x) • dP a + g.inner x (V a x) (P x) • dU a with hD_def
  have hHasMF : ∀ a : Fin N, HasMFDerivAt I 𝓘(ℝ, ℝ)
      (fun b : M => g.inner b (V a b) (U b) * g.inner b (V a b) (P b)) x (D a) := fun a => by
    have hUd : HasMFDerivAt I 𝓘(ℝ, ℝ) (fun b : M => g.inner b (V a b) (U b)) x (dU a) :=
      ((hsmU a).mdifferentiableAt (by simp)).hasMFDerivAt
    have hPd : HasMFDerivAt I 𝓘(ℝ, ℝ) (fun b : M => g.inner b (V a b) (P b)) x (dP a) :=
      ((hsmP a).mdifferentiableAt (by simp)).hasMFDerivAt
    exact hUd.mul hPd
  -- The per-`a` factor evaluations via metric compatibility.
  have hdUapp : ∀ a : Fin N, dU a (W x) =
      g.inner x ((LeviCivita (I := I) g).toFun (V a) x (W x)) (U x)
        + g.inner x (V a x) ((LeviCivita (I := I) g).toFun U x (W x)) := fun a => by
    rw [hdU_def]; exact hmcU a
  have hdPapp : ∀ a : Fin N, dP a (W x) =
      g.inner x ((LeviCivita (I := I) g).toFun (V a) x (W x)) (P x)
        + g.inner x (V a x) ((LeviCivita (I := I) g).toFun P x (W x)) := fun a => by
    rw [hdP_def]; exact hmcP a
  -- The per-`a` evaluation `D a (W x)`, metric-compatibility-expanded into reals.
  have hDapp : ∀ a : Fin N, D a (W x) =
        (g.inner x ((LeviCivita (I := I) g).toFun (V a) x (W x)) (U x)
            + g.inner x (V a x) ((LeviCivita (I := I) g).toFun U x (W x)))
          * g.inner x (V a x) (P x)
        + g.inner x (V a x) (U x)
          * (g.inner x ((LeviCivita (I := I) g).toFun (V a) x (W x)) (P x)
            + g.inner x (V a x) ((LeviCivita (I := I) g).toFun P x (W x))) := by
    intro a
    rw [hD_def]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
    rw [hdUapp a, hdPapp a]
    ring
  -- The sum's `HasMFDerivAt` with derivative `∑_a D a` (uniform `ℝ`-codomain CLMs).
  have hSum : HasMFDerivAt I 𝓘(ℝ, ℝ)
      (∑ a : Fin N, fun b : M => g.inner b (V a b) (U b) * g.inner b (V a b) (P b)) x
      (∑ a : Fin N, D a) :=
    HasMFDerivAt.sum (t := (Finset.univ : Finset (Fin N))) (fun a _ => hHasMF a)
  have hEqfun : (fun y : M => ∑ a : Fin N,
        g.inner y (V a y) (U y) * g.inner y (V a y) (P y)) =
      (∑ a : Fin N, fun b : M => g.inner b (V a b) (U b) * g.inner b (V a b) (P b)) := by
    funext y; rw [Finset.sum_apply]
  -- The field identity gives `mfderiv (⟨U,P⟩) x = ∑_a D a`, evaluated at `W x`.
  have hkey : ∑ a : Fin N, D a (W x) =
      g.inner x ((LeviCivita (I := I) g).toFun U x (W x)) (P x)
        + g.inner x (U x) ((LeviCivita (I := I) g).toFun P x (W x)) := by
    have hUPmf : HasMFDerivAt I 𝓘(ℝ, ℝ)
        (fun y : M => g.inner y (U y) (P y)) x (∑ a : Fin N, D a) := by
      rw [← hfield, hEqfun]; exact hSum
    have hmfeq : (∑ a : Fin N, D a) = mfderiv I 𝓘(ℝ, ℝ)
        (fun y : M => g.inner y (U y) (P y)) x := hUPmf.mfderiv.symm
    have hUPmf' : (∑ a : Fin N, D a) (W x) =
        g.inner x ((LeviCivita (I := I) g).toFun U x (W x)) (P x)
          + g.inner x (U x) ((LeviCivita (I := I) g).toFun P x (W x)) := by
      rw [hmfeq]; exact hmcUP
    rw [← hUPmf']
    exact (ContinuousLinearMap.sum_apply (Finset.univ : Finset (Fin N)) D (W x)).symm
  -- `D a (W x) = (antisym summand) + (reproduction summand)`; the reproduction sum collapses to
  -- `⟨∇_W U, P⟩ + ⟨U, ∇_W P⟩` (dual-Parseval), so `hkey` forces `∑_a (antisym summand) = 0`.
  have hsplit : ∀ a : Fin N, D a (W x) =
      (g.inner x ((LeviCivita (I := I) g).toFun (V a) x (W x)) (U x)
          * g.inner x (V a x) (P x)
        + g.inner x (V a x) (U x)
          * g.inner x ((LeviCivita (I := I) g).toFun (V a) x (W x)) (P x))
      + (g.inner x (V a x) ((LeviCivita (I := I) g).toFun U x (W x))
          * g.inner x (V a x) (P x)
        + g.inner x (V a x) (U x)
          * g.inner x (V a x) ((LeviCivita (I := I) g).toFun P x (W x))) := by
    intro a; rw [hDapp a]; ring
  have hrepU : (∑ a : Fin N,
        g.inner x (V a x) ((LeviCivita (I := I) g).toFun U x (W x))
          * g.inner x (V a x) (P x)) =
      g.inner x ((LeviCivita (I := I) g).toFun U x (W x)) (P x) :=
    parseval_family_inner_mul_sum (I := I) (M := M) g x (fun a => V a x)
      (fun u => hPar x u) ((LeviCivita (I := I) g).toFun U x (W x)) (P x)
  have hrepP : (∑ a : Fin N,
        g.inner x (V a x) (U x)
          * g.inner x (V a x) ((LeviCivita (I := I) g).toFun P x (W x))) =
      g.inner x (U x) ((LeviCivita (I := I) g).toFun P x (W x)) := by
    rw [show (fun a : Fin N => g.inner x (V a x) (U x)
          * g.inner x (V a x) ((LeviCivita (I := I) g).toFun P x (W x))) =
        (fun a : Fin N => g.inner x (V a x) ((LeviCivita (I := I) g).toFun P x (W x))
          * g.inner x (V a x) (U x)) from by funext a; ring]
    rw [parseval_family_inner_mul_sum (I := I) (M := M) g x (fun a => V a x)
      (fun u => hPar x u) ((LeviCivita (I := I) g).toFun P x (W x)) (U x)]
    exact g.symm x ((LeviCivita (I := I) g).toFun P x (W x)) (U x)
  -- `∑_a D a (W x) = (antisym sum) + (∑_a repro) = (antisym sum) + ⟨∇U,P⟩ + ⟨U,∇P⟩`.
  have hDsum : ∑ a : Fin N, D a (W x) =
      (∑ a : Fin N,
          (g.inner x ((LeviCivita (I := I) g).toFun (V a) x (W x)) (U x)
              * g.inner x (V a x) (P x)
            + g.inner x (V a x) (U x)
              * g.inner x ((LeviCivita (I := I) g).toFun (V a) x (W x)) (P x)))
        + (∑ a : Fin N,
            g.inner x (V a x) ((LeviCivita (I := I) g).toFun U x (W x))
              * g.inner x (V a x) (P x))
        + (∑ a : Fin N,
            g.inner x (V a x) (U x)
              * g.inner x (V a x) ((LeviCivita (I := I) g).toFun P x (W x))) := by
    rw [Finset.sum_congr rfl (fun a _ => hsplit a)]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun a _ => ?_); ring
  rw [hrepU, hrepP] at hDsum
  linarith [hkey, hDsum]

set_option linter.unusedSectionVars false in
/-- **The differentiated-curvature trace carrier is the `(r = 0, s)` Hom-bundle differentiated
curvature of `S` (the moving-frame, `tensorCov`-world form).** The carrier
`nablaDiffCurvTraceCc = bochnerGroupElt3IiiIv + bochnerGroupElt2 − bochnerGroupElt1` is, at every
point, the section-level differentiated Riemann curvature `nablaRiemannSec` of the
`(r = 0, s)`-tensor connection `tensorCov g 0 s = tensorRSCovariantDerivative 0 s` on the raw
section `S.toSection`, in the derivation/antisymmetric directions `(V a, V a, V b)`:
```
nablaDiffCurvTraceCc g s S (V a) (V b) x
  = nablaRiemannSec (LeviCivita g) (tensorCov g 0 s) (V a) (V a) (V b) S.toSection x.
```
The defining identity is the differentiated-curvature covariant Leibniz unfolding
`nablaRiemannSec_def` (`(∇_X R)(Y, Z) A = ∇_X(R(Y, Z) A) − R(∇_X Y, Z) A − R(Y, ∇_X Z) A −
R(Y, Z)(∇_X A)`, with derivation `X = V a`, antisymmetric slots `(Y, Z) = (V a, V b)`), matched to
the three carriers through the section-level `riemannSec` antisymmetry
(`R(∇_{V a} V b, V a) S = − R(V a, ∇_{V a} V b) S`, `R(V b, ∇_{V a} V a) S = − R(∇_{V a} V a, V b) S`)
and `covApply_apply`. -/
private theorem nablaDiffCurvTraceCc_toSection_eq_nablaRiemannSec
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s)
    {Va Vb : Π b : M, TangentSpace I b}
    (hVa : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => (⟨b, Va b⟩ : TotalSpace E (TangentSpace I))))
    (hVb : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => (⟨b, Vb b⟩ : TotalSpace E (TangentSpace I)))) (x : M) :
    (nablaDiffCurvTraceCc (I := I) (M := M) g s S hVa hVb).toSection x =
      nablaRiemannSec (I := I) (LeviCivita (I := I) g) (tensorCov (I := I) g 0 s)
        Va Va Vb (fun y : M => S.toSection y) x := by
  rw [nablaDiffCurvTraceCc, SmoothCcTensor.toSection_sub, SmoothCcTensor.toSection_add]
  simp only [ContMDiffSection.coe_sub, ContMDiffSection.coe_add, Pi.sub_apply, Pi.add_apply]
  rw [show (bochnerGroupElt3IiiIvCc (I := I) (M := M) g s S hVa hVb).toSection x =
      riemannSec (tensorCov (I := I) g 0 s)
        (fun b : M => (LeviCivita (I := I) g).toFun Vb b (Va b)) Va
        (fun y : M => S.toSection y) x +
      riemannSec (tensorCov (I := I) g 0 s) Vb
        (fun b : M => (LeviCivita (I := I) g).toFun Va b (Va b))
        (fun y : M => S.toSection y) x from rfl,
    show (bochnerGroupElt2Cc (I := I) (M := M) g s S hVa hVb).toSection x =
      covApply (tensorCov (I := I) g 0 s) Va
        (fun y : M => riemannSec (tensorCov (I := I) g 0 s) Va Vb
          (fun z : M => S.toSection z) y) x from rfl,
    show (bochnerGroupElt1Cc (I := I) (M := M) g s S hVa hVb).toSection x =
      riemannSec (tensorCov (I := I) g 0 s) Va Vb
        (covApply (tensorCov (I := I) g 0 s) Va (fun y : M => S.toSection y)) x from rfl]
  rw [nablaRiemannSec_def]
  -- (II): R(∇_{Va}Va, Vb) S = − R(Vb, ∇_{Va}Va) S ; (III): R(Va, ∇_{Va}Vb) S = − R(∇_{Va}Vb, Va) S.
  rw [show riemannSec (tensorCov (I := I) g 0 s) (covApply (LeviCivita (I := I) g) Va Va) Vb
        (fun y : M => S.toSection y) x =
      - riemannSec (tensorCov (I := I) g 0 s) Vb
          (fun b : M => (LeviCivita (I := I) g).toFun Va b (Va b))
          (fun y : M => S.toSection y) x from by
    rw [riemannSec_swap (cov := tensorCov (I := I) g 0 s)
      (covApply (LeviCivita (I := I) g) Va Va) Vb]
    rfl]
  rw [show riemannSec (tensorCov (I := I) g 0 s) Va (covApply (LeviCivita (I := I) g) Va Vb)
        (fun y : M => S.toSection y) x =
      - riemannSec (tensorCov (I := I) g 0 s)
          (fun b : M => (LeviCivita (I := I) g).toFun Vb b (Va b)) Va
          (fun y : M => S.toSection y) x from by
    rw [riemannSec_swap (cov := tensorCov (I := I) g 0 s) Va
      (covApply (LeviCivita (I := I) g) Va Vb)]
    rfl]
  rw [covApply_apply (tensorCov (I := I) g 0 s) Va
    (fun y : M => riemannSec (tensorCov (I := I) g 0 s) Va Vb (fun z : M => S.toSection z) y) x]
  abel

set_option linter.unusedSectionVars false in
/-- **The unit-read of the `(r = 0, s)` Hom-bundle differentiated curvature is the differentiated
`(0, s)`-tensor curvature.** Reading the `(r = 0, s)`-tensor differentiated Riemann curvature
`nablaRiemannSec (LeviCivita g) (tensorCov g 0 s) (V a) (V a) (V b) S.toSection x` (a fibre
`Tensor0SSpace 0 →L Tensor0SSpace s`) against the unit `(0, 0)`-tensor `unitZeroSec x` recovers the
differentiated `(0, s)`-tensor curvature `nablaTensor0SCurv g s (V a) (V a) (V b) A x`, where
`A y := (S.toSection y) (unitZeroSec y)` is the unit-read abstract `(0, s)`-tensor section.
This is the differentiated (`nabla`) lift of the Hom-bundle curvature–Leibniz unit-read bridge: the
`(r = 0, s)`-tensor bundle is the Hom-bundle `Tensor0SSpace 0 →L Tensor0SSpace s`
(`tensorRSCovariantDerivative` is `homBundleCovariantDerivativeGen (tensor0SCov 0) (tensor0SCov s)`,
by definition), so `nablaRiemannSec_homBundleGen_apply_eq` splits the unit-read into the target
differentiated curvature on the paired section `pairedSection S.toSection unitZeroSec = A` minus the
source `(0, 0)`-scalar differentiated curvature on `unitZeroSec`, which vanishes
(`nablaTensor0SCurv_zero_eq_zero`, the scalar connection is flat). -/
private theorem nablaRiemannSec_tensorCov_unit_eq_nablaTensor0SCurv
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s)
    {Va Vb : Π b : M, TangentSpace I b}
    (hVa : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => (⟨b, Va b⟩ : TotalSpace E (TangentSpace I))))
    (hVb : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => (⟨b, Vb b⟩ : TotalSpace E (TangentSpace I)))) (x : M) :
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
        nablaRiemannSec (I := I) (LeviCivita (I := I) g) (tensorCov (I := I) g 0 s)
          Va Va Vb (fun y : M => S.toSection y) x)
        (unitZeroSec (I := I) (M := M) x) =
      nablaTensor0SCurv (I := I) g s ⟨fun b => Va b, hVa⟩ ⟨fun b => Va b, hVa⟩
        ⟨fun b => Vb b, hVb⟩
        (fun y : M =>
          (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace s I y from S.toSection y)
            (unitZeroSec (I := I) (M := M) y)) x := by
  classical
  have hbridge := nablaRiemannSec_homBundleGen_apply_eq
    (cov_U := Tensor0SNabla.tensor0SCovariantDerivative I M 0 (LeviCivita (I := I) g))
    (cov_V := Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g))
    (covT := LeviCivita (I := I) g)
    ⟨fun b => Va b, hVa⟩ ⟨fun b => Va b, hVa⟩ ⟨fun b => Vb b, hVb⟩
    S.toSection
    ⟨fun y : M => unitZeroSec (I := I) (M := M) y, contMDiff_unitZeroSection (I := I) (M := M)⟩ x
  rw [show (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
        nablaRiemannSec (I := I) (LeviCivita (I := I) g) (tensorCov (I := I) g 0 s)
          Va Va Vb (fun y : M => S.toSection y) x)
        (unitZeroSec (I := I) (M := M) x) =
      nablaRiemannSec (I := I) (LeviCivita (I := I) g)
          (Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g))
          (fun b => Va b) (fun b => Va b) (fun b => Vb b)
          (HomConnectionGen.pairedSection (M := M)
            (U := fun z : M => Tensor0SSpace 0 I z) (V := fun z : M => Tensor0SSpace s I z)
            (fun b => S.toSection b) (fun b => unitZeroSec (I := I) (M := M) b)) x -
        (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from S.toSection x)
          (nablaRiemannSec (I := I) (LeviCivita (I := I) g)
            (Tensor0SNabla.tensor0SCovariantDerivative I M 0 (LeviCivita (I := I) g))
            (fun b => Va b) (fun b => Va b) (fun b => Vb b)
            (fun b => unitZeroSec (I := I) (M := M) b) x) from hbridge]
  -- The source-bundle differentiated curvature is the scalar `(0, 0)` differentiated curvature `= 0`.
  rw [show nablaRiemannSec (I := I) (LeviCivita (I := I) g)
        (Tensor0SNabla.tensor0SCovariantDerivative I M 0 (LeviCivita (I := I) g))
        (fun b => Va b) (fun b => Va b) (fun b => Vb b)
        (fun b => unitZeroSec (I := I) (M := M) b) x =
      nablaTensor0SCurv (I := I) g 0 ⟨fun b => Va b, hVa⟩ ⟨fun b => Va b, hVa⟩
        ⟨fun b => Vb b, hVb⟩ (fun b => unitZeroSec (I := I) (M := M) b) x from rfl,
    nablaTensor0SCurv_zero_eq_zero (I := I) g ⟨fun b => Va b, hVa⟩ ⟨fun b => Va b, hVa⟩
      ⟨fun b => Vb b, hVb⟩ (fun b => unitZeroSec (I := I) (M := M) b)
      (contMDiff_unitZeroSection (I := I) (M := M)) x]
  rw [map_zero, sub_zero]
  -- The target-bundle differentiated curvature on the paired section is `nablaTensor0SCurv g s A`.
  rfl

set_option linter.unusedSectionVars false in
/-- **Representation identification (the connector bridge): the differentiated-curvature trace
carrier is the `tensor0SAsRS`-wrap of the differentiated `(0, s)`-tensor curvature.** For a fixed
Parseval frame family, the moving-frame carrier `nablaDiffCurvTraceCc g s S (V a) (V b)` — built in
the `(r = 0, s)`-tensor (`tensorCov g 0 s`) world on the raw section `S.toSection`, read on the unit
through `bochnerGroupElt*` — equals the `tensor0SAsRS`-wrap of the differentiated `(0, s)`-tensor
curvature operator object `nablaTensor0SCurv g s (V a) (V a) (V b) A`, built in the
`Tensor0SSpace s` (`tensor0SCovariantDerivative s`) world on the unit-read abstract section
`A y := (S.toSection y) (unitZeroSec y)`:
```
nablaDiffCurvTraceCc g s S (V a) (V b) x
  = tensor0SAsRS x (nablaTensor0SCurv g s (V a) (V a) (V b) (fun y => S.toSection y (unit)) x).
```
This is the pure representation bridge between the two `(0, s)`-covariant-derivative worlds — the
carrier's `tensorRSCovariantDerivative 0 s` Hom-bundle world and the div-`R` curvature bridge's
`tensor0SCovariantDerivative s` world — through which the rank-`0` Bochner kernel chain
consumes the diagonal-divergence curvature bridge `frame_sum_nablaTensor0SCurv_diag_baseSlot_eval`.
The carrier is the `(r = 0, s)`-Hom-bundle differentiated curvature `nablaRiemannSec` of `S.toSection`
(`nablaDiffCurvTraceCc_toSection_eq_nablaRiemannSec`), whose `tensor0SAsRS`-rewrap of its unit-read
(`tensor0SAsRS_rs_unit'`) is, by the Hom-bundle curvature–Leibniz unit-read bridge
(`nablaRiemannSec_tensorCov_unit_eq_nablaTensor0SCurv`), exactly the wrapped differentiated
`(0, s)`-tensor curvature on `A`. -/
private theorem nablaDiffCurvTraceCc_toSection_eq_tensor0SAsRS_nablaTensor0SCurv
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s)
    {Va Vb : Π b : M, TangentSpace I b}
    (hVa : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => (⟨b, Va b⟩ : TotalSpace E (TangentSpace I))))
    (hVb : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => (⟨b, Vb b⟩ : TotalSpace E (TangentSpace I)))) (x : M) :
    (nablaDiffCurvTraceCc (I := I) (M := M) g s S hVa hVb).toSection x =
      tensor0SAsRS (I := I) (M := M) x
        (nablaTensor0SCurv (I := I) g s ⟨fun b => Va b, hVa⟩ ⟨fun b => Va b, hVa⟩
          ⟨fun b => Vb b, hVb⟩
          (fun y : M =>
            (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace s I y from S.toSection y)
              (unitZeroSec (I := I) (M := M) y)) x) := by
  rw [nablaDiffCurvTraceCc_toSection_eq_nablaRiemannSec (I := I) (M := M) g s S hVa hVb x]
  rw [← nablaRiemannSec_tensorCov_unit_eq_nablaTensor0SCurv (I := I) (M := M) g s S hVa hVb x]
  exact (tensor0SAsRS_rs_unit' (I := I) (M := M) s x
    (nablaRiemannSec (I := I) (LeviCivita (I := I) g) (tensorCov (I := I) g 0 s)
      Va Va Vb (fun y : M => S.toSection y) x)).symm

set_option linter.unusedSectionVars false in
/-- **Inner↔curvature-object bridge: the carrier inner-scalar pairing is the `(0, s)` fibre pairing of
the differentiated `(0, s)`-tensor curvature object against `∇S`.** Reading the differentiated-curvature
trace carrier `nablaDiffCurvTraceCc g s S (V a) (V b)` against the slot-`0` directional gradient
`∇_{V b} S = bochnerGradSlot0Cc g s S (V b)` through the `(0, s)` metric inner scalar `tensorInnerScalar`
is, at every point `x`, the `(0, s)` fibre pairing `tensorInnerPointwise g 0 s` of the `tensor0SAsRS`-wrap
of the differentiated `(0, s)`-tensor curvature object `nablaTensor0SCurv g s (V a) (V a) (V b) A`
(`A y := S.toSection y (unit)`) against `∇_{V b} S`:
```
tensorInnerScalar g 0 s (nablaDiffCurvTraceCc g s S (V a) (V b)) (bochnerGradSlot0Cc g s S (V b)) x
  = tensorInnerPointwise g 0 s x
      (toModel (tensor0SAsRS x (nablaTensor0SCurv g s (V a) (V a) (V b) A x)))
      (toModel (bochnerGradSlot0 g s S (V b) x)).
```
This lands the differentiated-curvature pairing — the integrand of the contracted-second-Bianchi
summed kernel chain over the proven primitive `D = −(G₁ + I₂)` — onto the
`Tensor0SSpace s`-world curvature object `nablaTensor0SCurv` that the diagonal-divergence curvature
bridge `frame_sum_nablaTensor0SCurv_diag_baseSlot_eval` and its slot-wise tuple form
`nablaTensor0SCurv_apply_eval` act on.  It is `tensorInnerScalar_apply` followed by the representation
identification `nablaDiffCurvTraceCc_toSection_eq_tensor0SAsRS_nablaTensor0SCurv` and the definitional
`bochnerGradSlot0Cc_toSection_apply`. -/
private theorem tensorInnerScalar_nablaDiffCurvTrace_eq_tensorInnerPointwise_nablaTensor0SCurv
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s)
    {Va Vb : Π b : M, TangentSpace I b}
    (hVa : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => (⟨b, Va b⟩ : TotalSpace E (TangentSpace I))))
    (hVb : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => (⟨b, Vb b⟩ : TotalSpace E (TangentSpace I)))) (x : M) :
    tensorInnerScalar (I := I) (M := M) g 0 s
        (nablaDiffCurvTraceCc (I := I) (M := M) g s S hVa hVb).toSection
        (bochnerGradSlot0Cc (I := I) (M := M) g s S hVb).toSection x =
      tensorInnerPointwise (I := I) (M := M) g 0 s x
        (TensorRSSpace.toModel
          (tensor0SAsRS (I := I) (M := M) x
            (nablaTensor0SCurv (I := I) g s ⟨fun b => Va b, hVa⟩ ⟨fun b => Va b, hVa⟩
              ⟨fun b => Vb b, hVb⟩
              (fun y : M =>
                (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace s I y from S.toSection y)
                  (unitZeroSec (I := I) (M := M) y)) x)))
        (TensorRSSpace.toModel (bochnerGradSlot0 (I := I) (M := M) g s S Vb x)) := by
  rw [tensorInnerScalar_apply (I := I) (M := M) g 0 s,
    nablaDiffCurvTraceCc_toSection_eq_tensor0SAsRS_nablaTensor0SCurv (I := I) (M := M) g s S hVa hVb x,
    bochnerGradSlot0Cc_toSection_apply (I := I) (M := M) g s S hVb x]

set_option linter.unusedSectionVars false in
/-- **The Parseval-frame → orthonormal-frame conversion of the diagonal differentiated-curvature trace,
at the `tensor0SAsRS`-section level.** For a fixed Parseval frame family `V a`, a fixed read direction
`V b`, and the unit-read section `A y := S.toSection y (unit)`, the family sum over `a` of the
`tensor0SAsRS`-wrap of the diagonal differentiated `(0, s)`-tensor curvature object
`nablaTensor0SCurv g s ⟨V a⟩ ⟨V a⟩ ⟨V b⟩ A` equals the orthonormal-frame sum over `i` of the
`tensor0SAsRS`-wrap of `nablaTensor0SCurv g s ⟨B_i⟩ ⟨B_i⟩ ⟨V b⟩ A`
(`B_i := smoothOrthoFrame g x i`).  This is the now-committed Parseval = orthonormal diagonal-trace
bridge `parsevalFrame_eq_orthoFrame_diag_nablaTensor0SCurv` pushed through the additive
`tensor0SAsRS` wrap (`tensor0SAsRS_finsetSum`). -/
private lemma parsevalFrameSum_diag_nablaTensor0SCurv_tensor0SAsRS_eq_ortho
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s)
    {N : ℕ} (V : Fin N → Π b : M, TangentSpace I b)
    (hV : ∀ a, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => (⟨b, V a b⟩ : TotalSpace E (TangentSpace I))))
    (hPar : ∀ (x : M) (u : TangentSpace I x),
      (∑ a : Fin N, g.inner x (V a x) u • V a x) = u) (b : Fin N) (x : M) :
    (∑ a : Fin N, tensor0SAsRS (I := I) (M := M) x
        (nablaTensor0SCurv (I := I) g s ⟨fun y => V a y, hV a⟩ ⟨fun y => V a y, hV a⟩
          ⟨fun y => V b y, hV b⟩
          (fun y : M =>
            (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace s I y from S.toSection y)
              (unitZeroSec (I := I) (M := M) y)) x)) =
      ∑ i : Fin (Module.finrank ℝ E), tensor0SAsRS (I := I) (M := M) x
        (nablaTensor0SCurv (I := I) g s
          (ContMDiffSection.mk (smoothOrthoFrame (I := I) g x i)
            (smoothOrthoFrame_smooth (I := I) g x i))
          (ContMDiffSection.mk (smoothOrthoFrame (I := I) g x i)
            (smoothOrthoFrame_smooth (I := I) g x i))
          ⟨fun y => V b y, hV b⟩
          (fun y : M =>
            (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace s I y from S.toSection y)
              (unitZeroSec (I := I) (M := M) y)) x) := by
  classical
  rw [← tensor0SAsRS_finsetSum (I := I) (M := M) s x Finset.univ,
    ← tensor0SAsRS_finsetSum (I := I) (M := M) s x Finset.univ]
  rw [tensor0SAsRS_eq_iff]
  exact parsevalFrame_eq_orthoFrame_diag_nablaTensor0SCurv (I := I) (M := M) g s
    ⟨fun y => V b y, hV b⟩
    (fun y : M =>
      (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace s I y from S.toSection y)
        (unitZeroSec (I := I) (M := M) y))
    (contMDiff_unitEvalSection' (I := I) (M := M) g s S) V hV hPar x

set_option linter.unusedSectionVars false in
/-- **The `(0, s)` frame component of a `tensor0SAsRS`-wrap is the model evaluation.** At a frame `e`,
the rank-`0` frame component `fiberNormSqComponent g x 0 s (tensor0SAsRS x C) n e K₀ J` of the
`tensor0SAsRS`-wrapped model `(0, s)`-tensor `C` equals `Tensor0SSpace.toModel C (e ∘ J)` (the unit
scalar `tensor00Scalar` of the empty coframe covector is `1`). -/
private lemma fiberNormSqComponent_tensor0SAsRS
    (g : SmoothRiemannianMetric I M) (s : ℕ) (x : M) (C : Tensor0SSpace s I x)
    {n : ℕ} (e : Fin n → TangentSpace I x) (K₀ : Fin 0 → Fin n) (J : Fin s → Fin n) :
    fiberNormSqComponent (I := I) (M := M) g x 0 s (tensor0SAsRS (I := I) (M := M) x C) n e K₀ J =
      Tensor0SSpace.toModel C (fun k => e (J k)) := by
  classical
  have hscalar : tensor00Scalar (I := I) (M := M) x
      ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 0) ℝ).compContinuousLinearMap
        (fun k => g.inner x (e (K₀ k)))) = 1 := by
    rw [show ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 0) ℝ).compContinuousLinearMap
          (fun k => g.inner x (e (K₀ k))) : Tensor0SSpace 0 I x) =
        coframeS (I := I) (M := M) g x 0 e K₀ from rfl,
      tensor00Scalar_apply (I := I) (M := M) x _ (fun k : Fin 0 => k.elim0),
      coframeS_apply (I := I) (M := M) g x 0 e K₀]
    simp
  change Tensor0SSpace.toModel
      ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from tensor0SAsRS (I := I) (M := M) x C)
        ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 0) ℝ).compContinuousLinearMap
          (fun k => g.inner x (e (K₀ k))))) (fun k => e (J k)) = _
  rw [tensor0SAsRS_apply (I := I) (M := M) x C, hscalar, one_smul]

set_option linter.unusedSectionVars false in
/-- **The `(0, s)` metric pairing of two `tensor0SAsRS`-wraps is the diagonal frame product sum.** For a
`g(x)`-orthonormal frame `e` (basis `bse`, `n = finrank`), the pointwise `(0, s)` inner product of the
`tensor0SAsRS`-wraps of model `(0, s)`-tensors `C, D` is the diagonal frame double sum of their model
evaluations.  This is `tensorInnerPointwise_eq_sum_componentS_mul` at `r = 0` (the empty leading
`K`-index collapses) followed by the `tensor0SAsRS` component evaluation `fiberNormSqComponent_tensor0SAsRS`. -/
private lemma tensorInnerPointwise_tensor0SAsRS_eq_frameSum
    (g : SmoothRiemannianMetric I M) (s : ℕ) (x : M) (C D : Tensor0SSpace s I x)
    {n : ℕ} (e : Fin n → TangentSpace I x)
    (bse : Module.Basis (Fin n) ℝ (TangentSpace I x))
    (hn : n = Module.finrank ℝ E) (hbse : ∀ i : Fin n, bse i = e i)
    (horth : ∀ a b : Fin n, g.inner x (e a) (e b) = if a = b then (1 : ℝ) else 0) :
    tensorInnerPointwise (I := I) (M := M) g 0 s x
        (TensorRSSpace.toModel (tensor0SAsRS (I := I) (M := M) x C))
        (TensorRSSpace.toModel (tensor0SAsRS (I := I) (M := M) x D)) =
      ∑ J : Fin s → Fin n,
        Tensor0SSpace.toModel C (fun k => e (J k)) * Tensor0SSpace.toModel D (fun k => e (J k)) := by
  classical
  rw [tensorInnerPointwise_eq_sum_componentS_mul (I := I) (M := M) g 0 s x e bse hn hbse horth
    (tensor0SAsRS (I := I) (M := M) x C) (tensor0SAsRS (I := I) (M := M) x D)]
  rw [Finset.sum_eq_single (fun k : Fin 0 => k.elim0)]
  · refine Finset.sum_congr rfl (fun J _ => ?_)
    rw [fiberNormSqComponent_tensor0SAsRS (I := I) (M := M) g s x C e _ J,
      fiberNormSqComponent_tensor0SAsRS (I := I) (M := M) g s x D e _ J]
  · intro K _ hK; exact absurd (funext fun a => a.elim0) hK
  · intro h; exact absurd (Finset.mem_univ _) h

set_option linter.unusedSectionVars false in
/-- **The smooth orthonormal frame at the centre packages as a `Module.Basis`.** The `finrank`-many
`g(x)`-orthonormal vectors `smoothOrthoFrame g x i x` form a basis of `T_x M` (orthonormality gives
linear independence, and the cardinality equals the rank).  This is the basis the slot-`0` Parseval and
model-Parseval decompositions consume; a live re-derivation (it depends only on
`smoothOrthoFrame_orthonormal_at_center`). -/
private theorem smoothOrthoFrame_center_basis
    (g : SmoothRiemannianMetric I M) (x : M) :
    ∃ bse : Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I x),
      ∀ i, bse i = smoothOrthoFrame (I := I) g x i x := by
  classical
  have horth : ∀ a b : Fin (Module.finrank ℝ E),
      g.inner x (smoothOrthoFrame (I := I) g x a x) (smoothOrthoFrame (I := I) g x b x)
        = if a = b then 1 else 0 :=
    fun a b => smoothOrthoFrame_orthonormal_at_center (I := I) g x a b
  have he_li : LinearIndependent ℝ (fun i => smoothOrthoFrame (I := I) g x i x) := by
    rw [linearIndependent_iff']
    intro fs c hsum k hk_mem
    have h_zero : g.inner x (smoothOrthoFrame (I := I) g x k x)
        (∑ j ∈ fs, c j • smoothOrthoFrame (I := I) g x j x) = 0 := by rw [hsum]; simp
    rw [map_sum] at h_zero
    have h_pull : ∀ j ∈ fs, g.inner x (smoothOrthoFrame (I := I) g x k x)
        (c j • smoothOrthoFrame (I := I) g x j x) = c j * (if k = j then (1 : ℝ) else 0) := by
      intro j _
      rw [(g.inner x (smoothOrthoFrame (I := I) g x k x)).map_smul (c j), smul_eq_mul, horth k j]
    rw [Finset.sum_congr rfl h_pull, Finset.sum_eq_single_of_mem k hk_mem] at h_zero
    · rwa [if_pos rfl, mul_one] at h_zero
    · intro j _ hjk; rw [if_neg (fun h => hjk h.symm), mul_zero]
  have hcard : Fintype.card (Fin (Module.finrank ℝ E)) = Module.finrank ℝ E := Fintype.card_fin _
  exact ⟨basisOfLinearIndependentOfCardEqFinrank he_li hcard,
    fun i => congrFun (coe_basisOfLinearIndependentOfCardEqFinrank he_li hcard) i⟩

set_option linter.unusedSectionVars false in
/-- **The orthonormal-frame diagonal `nablaTensor0SCurv` trace, metric-paired against a `tensor0SAsRS`-wrap,
is the slot-substitution frame double sum (the metric-trace opening of the differentiated curvature).** For
the orthonormal frame `B_i := smoothOrthoFrame g x i` (basis `bse`), the `(0, s)` pointwise pairing of the
orthonormal-frame diagonal differentiated-curvature trace `∑_i tensor0SAsRS (nablaTensor0SCurv g s B_i B_i Vb A)`
against the `tensor0SAsRS`-wrap of `D` equals the frame double sum, over multi-indices `J`, of the slot-wise
divergence-of-curvature substitution of `A` paired with `D`'s `J`-component:
```
⟨∑_i tensor0SAsRS (nablaTensor0SCurv g s B_i B_i Vb A), tensor0SAsRS D⟩_g
  = ∑_J [ − ∑_k A(update (B∘J) k (∑_i nablaBaseSlotCurv g B_i B_i Vb (B_{J k}))) ] · D(B∘J).
```
This is the `tensor0SAsRS` collapse `tensorInnerPointwise_tensor0SAsRS_eq_frameSum` (H1) on the
frame-summed wrap, with the diagonal divergence-of-curvature transfer
`frame_sum_nablaTensor0SCurv_diag_baseSlot_eval` (Theorem B) folding the inner frame sum slot-wise.  It
opens the metric trace of the differentiated curvature onto exactly the shape the once-contracted second
Bianchi `nablaCurvSec_diag_frame_trace_eq_nablaRicci_sub` (Theorem A) acts on. -/
private lemma diagDiffCurv_pair_eq_slotSubstSum
    (g : SmoothRiemannianMetric I M) (s : ℕ) (x : M)
    (A : Π b : M, Tensor0SSpace s I b)
    (hA : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel s ℝ E)) ∞
      (fun b => TotalSpace.mk' (Tensor0SModel s ℝ E)
        (E := fun z : M => Tensor0SSpace s I z) b (A b)))
    (Vb : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (D : Tensor0SSpace s I x)
    (bse : Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I x))
    (hbse : ∀ i, bse i = smoothOrthoFrame (I := I) g x i x) :
    tensorInnerPointwise (I := I) (M := M) g 0 s x
        (TensorRSSpace.toModel (∑ i : Fin (Module.finrank ℝ E), tensor0SAsRS (I := I) (M := M) x
          (nablaTensor0SCurv (I := I) g s
            (ContMDiffSection.mk (smoothOrthoFrame (I := I) g x i)
              (smoothOrthoFrame_smooth (I := I) g x i))
            (ContMDiffSection.mk (smoothOrthoFrame (I := I) g x i)
              (smoothOrthoFrame_smooth (I := I) g x i)) Vb A x)))
        (TensorRSSpace.toModel (tensor0SAsRS (I := I) (M := M) x D)) =
      ∑ J : Fin s → Fin (Module.finrank ℝ E),
        (- ∑ k : Fin s,
            Tensor0SSpace.toModel (A x)
              (Function.update (fun j => smoothOrthoFrame (I := I) g x (J j) x) k
                (∑ i : Fin (Module.finrank ℝ E),
                  nablaBaseSlotCurv (I := I) g
                    (ContMDiffSection.mk (smoothOrthoFrame (I := I) g x i)
                      (smoothOrthoFrame_smooth (I := I) g x i))
                    (ContMDiffSection.mk (smoothOrthoFrame (I := I) g x i)
                      (smoothOrthoFrame_smooth (I := I) g x i)) Vb x
                    (smoothOrthoFrame (I := I) g x (J k) x)))) *
          Tensor0SSpace.toModel D (fun j => smoothOrthoFrame (I := I) g x (J j) x) := by
  classical
  have horth : ∀ a b : Fin (Module.finrank ℝ E),
      g.inner x (smoothOrthoFrame (I := I) g x a x) (smoothOrthoFrame (I := I) g x b x)
        = if a = b then 1 else 0 :=
    fun a b => smoothOrthoFrame_orthonormal_at_center (I := I) g x a b
  rw [← tensor0SAsRS_finsetSum (I := I) (M := M) s x Finset.univ,
    tensorInnerPointwise_tensor0SAsRS_eq_frameSum (I := I) (M := M) g s x _ D
      (fun j => smoothOrthoFrame (I := I) g x j x) bse rfl hbse horth]
  refine Finset.sum_congr rfl (fun J _ => ?_)
  congr 1
  rw [show Tensor0SSpace.toModel (∑ i : Fin (Module.finrank ℝ E),
        nablaTensor0SCurv (I := I) g s
          (ContMDiffSection.mk (smoothOrthoFrame (I := I) g x i)
            (smoothOrthoFrame_smooth (I := I) g x i))
          (ContMDiffSection.mk (smoothOrthoFrame (I := I) g x i)
            (smoothOrthoFrame_smooth (I := I) g x i)) Vb A x)
      = ∑ i : Fin (Module.finrank ℝ E), Tensor0SSpace.toModel
          (nablaTensor0SCurv (I := I) g s
            (ContMDiffSection.mk (smoothOrthoFrame (I := I) g x i)
              (smoothOrthoFrame_smooth (I := I) g x i))
            (ContMDiffSection.mk (smoothOrthoFrame (I := I) g x i)
              (smoothOrthoFrame_smooth (I := I) g x i)) Vb A x) from by
    rw [← Tensor0SSpace.toModelL_apply, map_sum]
    exact Finset.sum_congr rfl (fun i _ => Tensor0SSpace.toModelL_apply _)]
  rw [ContinuousMultilinearMap.sum_apply]
  exact frame_sum_nablaTensor0SCurv_diag_baseSlot_eval (I := I) g s Vb A hA x
    (fun j => smoothOrthoFrame (I := I) g x (J j) x)

set_option linter.unusedSectionVars false in
/-- **The Parseval-frame diagonal differentiated-curvature trace pairing equals the orthonormal-frame
slot-substitution double sum (the Parseval bridge into the metric-trace opening).** For a fixed Parseval
frame family `V a`, a read direction `V b`, the family sum over `a` of the `(0, s)` fibre pairing of the
`tensor0SAsRS`-wrap of `nablaTensor0SCurv g s (V a) (V a) (V b) A` against the slot-`0` gradient
`∇_{V b} S` (`A y := S.toSection y (unit)`) equals the orthonormal-frame slot-substitution double sum:
```
∑_a ⟨tensor0SAsRS (nablaTensor0SCurv g s (V a)(V a)(V b) A), ∇_{V b} S⟩_g
  = ∑_J [ − ∑_k A(update (B∘J) k (∑_i nablaBaseSlotCurv B_i B_i (V b) (B_{J k}))) ] · gradCurry0(B∘J).
```
The family sum is pushed inside the inner product (`tensor0SAsRS` additivity + `tensorInnerPointwise`
left-additivity), the diagonal Parseval trace is converted to the orthonormal-frame trace
(`parsevalFrameSum_diag_nablaTensor0SCurv_tensor0SAsRS_eq_ortho`), and the metric-trace opening
`diagDiffCurv_pair_eq_slotSubstSum` reads it off as the slot-substitution sum (with
`bochnerGradSlot0 = tensor0SAsRS (gradCurry0 (V b))`). -/
private lemma parsevalDiagDiffCurv_pair_eq_orthoSlotSubstSum
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s)
    {N : ℕ} (V : Fin N → Π b : M, TangentSpace I b)
    (hV : ∀ a, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => (⟨b, V a b⟩ : TotalSpace E (TangentSpace I))))
    (hPar : ∀ (x : M) (u : TangentSpace I x),
      (∑ a : Fin N, g.inner x (V a x) u • V a x) = u) (b : Fin N) (x : M)
    (bse : Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I x))
    (hbse : ∀ i, bse i = smoothOrthoFrame (I := I) g x i x) :
    (∑ a : Fin N, tensorInnerPointwise (I := I) (M := M) g 0 s x
        (TensorRSSpace.toModel
          (tensor0SAsRS (I := I) (M := M) x
            (nablaTensor0SCurv (I := I) g s ⟨fun b => V a b, hV a⟩ ⟨fun b => V a b, hV a⟩
              ⟨fun y => V b y, hV b⟩
              (fun y : M =>
                (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace s I y from S.toSection y)
                  (unitZeroSec (I := I) (M := M) y)) x)))
        (TensorRSSpace.toModel (bochnerGradSlot0 (I := I) (M := M) g s S (V b) x))) =
      ∑ J : Fin s → Fin (Module.finrank ℝ E),
        (- ∑ k : Fin s,
            Tensor0SSpace.toModel
              ((fun y : M =>
                (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace s I y from S.toSection y)
                  (unitZeroSec (I := I) (M := M) y)) x)
              (Function.update (fun j => smoothOrthoFrame (I := I) g x (J j) x) k
                (∑ i : Fin (Module.finrank ℝ E),
                  nablaBaseSlotCurv (I := I) g
                    (ContMDiffSection.mk (smoothOrthoFrame (I := I) g x i)
                      (smoothOrthoFrame_smooth (I := I) g x i))
                    (ContMDiffSection.mk (smoothOrthoFrame (I := I) g x i)
                      (smoothOrthoFrame_smooth (I := I) g x i)) ⟨fun y => V b y, hV b⟩ x
                    (smoothOrthoFrame (I := I) g x (J k) x)))) *
          Tensor0SSpace.toModel (gradCurry0 (I := I) (M := M) g s S x (V b x))
            (fun j => smoothOrthoFrame (I := I) g x (J j) x) := by
  classical
  -- The slot-`0` gradient carrier is the `tensor0SAsRS`-wrap of `gradCurry0 (V b)`.
  have hgrad : bochnerGradSlot0 (I := I) (M := M) g s S (V b) x =
      tensor0SAsRS (I := I) (M := M) x (gradCurry0 (I := I) (M := M) g s S x (V b x)) := rfl
  rw [hgrad]
  -- Push the family sum inside the inner product (left-additivity + `tensor0SAsRS` additivity).
  rw [show (∑ a : Fin N, tensorInnerPointwise (I := I) (M := M) g 0 s x
        (TensorRSSpace.toModel
          (tensor0SAsRS (I := I) (M := M) x
            (nablaTensor0SCurv (I := I) g s ⟨fun b => V a b, hV a⟩ ⟨fun b => V a b, hV a⟩
              ⟨fun y => V b y, hV b⟩
              (fun y : M =>
                (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace s I y from S.toSection y)
                  (unitZeroSec (I := I) (M := M) y)) x)))
        (TensorRSSpace.toModel
          (tensor0SAsRS (I := I) (M := M) x (gradCurry0 (I := I) (M := M) g s S x (V b x))))) =
      tensorInnerPointwise (I := I) (M := M) g 0 s x
        (TensorRSSpace.toModel
          (∑ a : Fin N, tensor0SAsRS (I := I) (M := M) x
            (nablaTensor0SCurv (I := I) g s ⟨fun b => V a b, hV a⟩ ⟨fun b => V a b, hV a⟩
              ⟨fun y => V b y, hV b⟩
              (fun y : M =>
                (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace s I y from S.toSection y)
                  (unitZeroSec (I := I) (M := M) y)) x)))
        (TensorRSSpace.toModel
          (tensor0SAsRS (I := I) (M := M) x (gradCurry0 (I := I) (M := M) g s S x (V b x)))) from by
    rw [show (TensorRSSpace.toModel
          (∑ a : Fin N, tensor0SAsRS (I := I) (M := M) x
            (nablaTensor0SCurv (I := I) g s ⟨fun b => V a b, hV a⟩ ⟨fun b => V a b, hV a⟩
              ⟨fun y => V b y, hV b⟩
              (fun y : M =>
                (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace s I y from S.toSection y)
                  (unitZeroSec (I := I) (M := M) y)) x))) =
        ∑ a : Fin N, (1 : ℝ) • TensorRSSpace.toModel
          (tensor0SAsRS (I := I) (M := M) x
            (nablaTensor0SCurv (I := I) g s ⟨fun b => V a b, hV a⟩ ⟨fun b => V a b, hV a⟩
              ⟨fun y => V b y, hV b⟩
              (fun y : M =>
                (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace s I y from S.toSection y)
                  (unitZeroSec (I := I) (M := M) y)) x)) from by
      rw [show (∑ a : Fin N, (1 : ℝ) • TensorRSSpace.toModel
            (tensor0SAsRS (I := I) (M := M) x
              (nablaTensor0SCurv (I := I) g s ⟨fun b => V a b, hV a⟩ ⟨fun b => V a b, hV a⟩
                ⟨fun y => V b y, hV b⟩
                (fun y : M =>
                  (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace s I y from S.toSection y)
                    (unitZeroSec (I := I) (M := M) y)) x))) =
          ∑ a : Fin N, TensorRSSpace.toModel
            (tensor0SAsRS (I := I) (M := M) x
              (nablaTensor0SCurv (I := I) g s ⟨fun b => V a b, hV a⟩ ⟨fun b => V a b, hV a⟩
                ⟨fun y => V b y, hV b⟩
                (fun y : M =>
                  (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace s I y from S.toSection y)
                    (unitZeroSec (I := I) (M := M) y)) x)) from by
        simp only [one_smul]]
      exact map_sum (TensorRSSpace.toModelL (I := I) 0 s x) _ Finset.univ,
      tensorInnerPointwise_sum_left (I := I) (M := M) g 0 s x Finset.univ _ _ _]
    simp]
  -- Convert the diagonal Parseval trace to the orthonormal-frame trace.
  rw [parsevalFrameSum_diag_nablaTensor0SCurv_tensor0SAsRS_eq_ortho
    (I := I) (M := M) g s S V hV hPar b x]
  -- Open the metric trace via the slot-substitution expansion.
  exact diagDiffCurv_pair_eq_slotSubstSum (I := I) (M := M) g s x
    (fun y : M =>
      (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace s I y from S.toSection y)
        (unitZeroSec (I := I) (M := M) y))
    (contMDiff_unitEvalSection' (I := I) (M := M) g s S) ⟨fun y => V b y, hV b⟩
    (gradCurry0 (I := I) (M := M) g s S x (V b x)) bse hbse

/-- **The frame-summed differentiated base-tangent curvature, metric-paired against a smooth field, is
the contracted-second-Bianchi differentiated-Ricci difference (the divergence of curvature, value form).**
For the orthonormal frame `B_i := smoothOrthoFrame g x i`, smooth fields `Vb, U`, and a tangent value `w`,
the metric pairing of the frame-summed inserted vector `∑_i nablaBaseSlotCurv g B_i B_i Vb x w` against
`U x` collapses, through the definitional `nablaBaseSlotCurv_eq_nablaCurvSec` and the once-contracted
second Bianchi `nablaCurvSec_diag_frame_trace_eq_nablaRicci_sub` (Theorem A, with the acted slot the smooth
extension `ext w`), onto the differentiated-Ricci difference:
```
g(∑_i nablaBaseSlotCurv g B_i B_i Vb x w, U) = ∇_U Ric(Vb, ext w) − ∇_{ext w} Ric(U, Vb).
```
This is the metric read-off of the divergence-of-curvature `div R = δ R` identity at a point. -/
private lemma inner_nablaBaseSlotCurvFrameSum_eq_nablaRicci_sub
    (g : SmoothRiemannianMetric I M) {x : M}
    {Vb U : Π b : M, TangentSpace I b}
    (hVb : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Vb))
    (hU : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% U)) (w : TangentSpace I x) :
    g.inner x (∑ i : Fin (Module.finrank ℝ E),
        nablaBaseSlotCurv (I := I) g
          (ContMDiffSection.mk (smoothOrthoFrame (I := I) g x i)
            (smoothOrthoFrame_smooth (I := I) g x i))
          (ContMDiffSection.mk (smoothOrthoFrame (I := I) g x i)
            (smoothOrthoFrame_smooth (I := I) g x i))
          ⟨fun b => Vb b, hVb⟩ x w) (U x) =
      nablaRicci (I := I) g U (fun b => Vb b)
          (fun b => smoothExtensionTangent (I := I) x w b) x -
        nablaRicci (I := I) g (fun b => smoothExtensionTangent (I := I) x w b) U
          (fun b => Vb b) x := by
  classical
  have hA := nablaCurvSec_diag_frame_trace_eq_nablaRicci_sub (I := I) g
    (Y := fun b => Vb b) (W := fun b => smoothExtensionTangent (I := I) x w b) (U := U) (x := x)
    hVb (smoothExtensionTangent_contMDiff (I := I) x w) hU
  rw [map_sum, ContinuousLinearMap.sum_apply]
  refine Eq.trans ?_ hA
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [nablaBaseSlotCurv_eq_nablaCurvSec]
  simp only [ContMDiffSection.coeFn_mk]

/-- **The slot-`k` substituted tensor evaluates by updating the slot-`k` argument through the CLM.** For
a continuous endomorphism `Φ` of `T_x M`, a `(0, s)`-tensor `C`, and a tangent tuple `m`, the model
evaluation of `tensorSlotSubstCLM (tangentSlotCLM k Φ) C` at `m` is `C` evaluated on the tuple with its
`k`-th entry replaced by `Φ (m k)`:
```
toModel (tensorSlotSubstCLM (tangentSlotCLM k Φ) C) m = toModel C (Function.update m k (Φ (m k))).
```
This is `tensorSlotSubstCLM_apply` followed by the pointwise identification of
`fun i => (tangentSlotCLM k Φ i) (m i)` with `Function.update m k (Φ (m k))` (`tangentSlotCLM_self`/
`tangentSlotCLM_other` against `Function.update_apply`). -/
private lemma toModel_tensorSlotSubst_tangentSlot_apply
    {s : ℕ} {x : M} (k : Fin s) (Φ : TangentSpace I x →L[ℝ] TangentSpace I x)
    (C : Tensor0SSpace s I x) (m : Fin s → TangentSpace I x) :
    Tensor0SSpace.toModel (tensorSlotSubstCLM (I := I) s x (tangentSlotCLM (I := I) s k Φ) C) m =
      Tensor0SSpace.toModel C (Function.update m k (Φ (m k))) := by
  classical
  have hupd : (fun i => (tangentSlotCLM (I := I) s k Φ i) (m i)) =
      Function.update m k (Φ (m k)) := by
    funext i
    by_cases hik : i = k
    · subst hik; rw [tangentSlotCLM_self, Function.update_self]
    · rw [tangentSlotCLM_other (I := I) s k Φ hik, ContinuousLinearMap.id_apply,
        Function.update_of_ne hik]
  have hsubst : (show ContinuousMultilinearMap ℝ (fun _ : Fin s => TangentSpace I x) ℝ from
        tensorSlotSubstCLM (I := I) s x (tangentSlotCLM (I := I) s k Φ) C) m =
      (show ContinuousMultilinearMap ℝ (fun _ : Fin s => TangentSpace I x) ℝ from C)
        (Function.update m k (Φ (m k))) := by
    rw [tensorSlotSubstCLM_apply (I := I) s x (tangentSlotCLM (I := I) s k Φ) C m, hupd]
  change Tensor0SSpace.toModel
      (tensorSlotSubstCLM (I := I) s x (tangentSlotCLM (I := I) s k Φ) C) m =
    Tensor0SSpace.toModel C (Function.update m k (Φ (m k)))
  rw [Tensor0SSpace.toModel, Tensor0SSpace.toModel]
  exact hsubst

/-- **The orthonormal-frame slot-substitution double sum is the negated folded slot-substitution metric
pairing (the metric-trace opening as a curvature-commutator inner product).** For the orthonormal frame
`B_i := smoothOrthoFrame g x i` and the frame-summed differentiated-curvature endomorphism
`T_x := nablaBaseSlotCurvFrameSumCLM g B Vb x`, the slot-substitution double sum produced by the bridges
equals the negated sum over slots `k` of the `(0, s)` metric pairing of the slot-`k` substitution of `A_x`
by `T_x` against `D`:
```
∑_J [−∑_k toModel(A_x)(update (B∘J) k (T_x (B_{Jk})))] · toModel(D)(B∘J)
  = −∑_k ⟨tensor0SAsRS (tensorSlotSubstCLM (tangentSlotCLM k T_x) A_x), tensor0SAsRS D⟩_g.
```
This is the frame double-sum collapse `tensorInnerPointwise_tensor0SAsRS_eq_frameSum` (H1) on the
slot-substituted wrap, with `toModel_tensorSlotSubst_tangentSlot_apply` naming the per-slot inserted
endomorphism and `nablaBaseSlotCurvFrameSumCLM_apply` identifying `T_x`. -/
private lemma orthoSlotSubstSum_eq_neg_folded_pairing
    (g : SmoothRiemannianMetric I M) (s : ℕ) (x : M)
    (A : Tensor0SSpace s I x) (D : Tensor0SSpace s I x)
    (B : Fin (Module.finrank ℝ E) → Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (_hB : ∀ i, B i = ContMDiffSection.mk (smoothOrthoFrame (I := I) g x i)
      (smoothOrthoFrame_smooth (I := I) g x i))
    (Vb : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (bse : Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I x))
    (hbse : ∀ i, bse i = smoothOrthoFrame (I := I) g x i x) :
    ∑ J : Fin s → Fin (Module.finrank ℝ E),
        (- ∑ k : Fin s,
            Tensor0SSpace.toModel A
              (Function.update (fun j => smoothOrthoFrame (I := I) g x (J j) x) k
                (nablaBaseSlotCurvFrameSumCLM (I := I) g B Vb x
                  (smoothOrthoFrame (I := I) g x (J k) x)))) *
          Tensor0SSpace.toModel D (fun j => smoothOrthoFrame (I := I) g x (J j) x) =
      - ∑ k : Fin s,
          tensorInnerPointwise (I := I) (M := M) g 0 s x
            (TensorRSSpace.toModel
              (tensor0SAsRS (I := I) (M := M) x
                (tensorSlotSubstCLM (I := I) s x
                  (tangentSlotCLM (I := I) s k (nablaBaseSlotCurvFrameSumCLM (I := I) g B Vb x)) A)))
            (TensorRSSpace.toModel (tensor0SAsRS (I := I) (M := M) x D)) := by
  classical
  have horth : ∀ a b : Fin (Module.finrank ℝ E),
      g.inner x (smoothOrthoFrame (I := I) g x a x) (smoothOrthoFrame (I := I) g x b x)
        = if a = b then 1 else 0 :=
    fun a b => smoothOrthoFrame_orthonormal_at_center (I := I) g x a b
  -- Each slot-`k` metric pairing is the frame double sum of the slot-substituted tensor's components.
  have hpslot : ∀ k : Fin s,
      tensorInnerPointwise (I := I) (M := M) g 0 s x
          (TensorRSSpace.toModel
            (tensor0SAsRS (I := I) (M := M) x
              (tensorSlotSubstCLM (I := I) s x
                (tangentSlotCLM (I := I) s k (nablaBaseSlotCurvFrameSumCLM (I := I) g B Vb x)) A)))
          (TensorRSSpace.toModel (tensor0SAsRS (I := I) (M := M) x D)) =
        ∑ J : Fin s → Fin (Module.finrank ℝ E),
          Tensor0SSpace.toModel A
            (Function.update (fun j => smoothOrthoFrame (I := I) g x (J j) x) k
              (nablaBaseSlotCurvFrameSumCLM (I := I) g B Vb x
                (smoothOrthoFrame (I := I) g x (J k) x))) *
            Tensor0SSpace.toModel D (fun j => smoothOrthoFrame (I := I) g x (J j) x) := by
    intro k
    rw [tensorInnerPointwise_tensor0SAsRS_eq_frameSum (I := I) (M := M) g s x _ D
      (fun j => smoothOrthoFrame (I := I) g x j x) bse rfl hbse horth]
    refine Finset.sum_congr rfl (fun J _ => ?_)
    rw [toModel_tensorSlotSubst_tangentSlot_apply (I := I) k
      (nablaBaseSlotCurvFrameSumCLM (I := I) g B Vb x) A
      (fun j => smoothOrthoFrame (I := I) g x (J j) x)]
  symm
  rw [Finset.sum_congr rfl (fun k _ => hpslot k), Finset.sum_comm, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl (fun J _ => ?_)
  conv_rhs => rw [neg_mul, Finset.sum_mul]

set_option linter.unusedSectionVars false in
/-- **The Parseval-frame diagonal differentiated-curvature trace pairing, at a point, is the negated
slot-folded differentiated-curvature operator pairing (the inner-vector reading of the metric-trace
opening).** Combining the Parseval-bridge metric-trace opening
`parsevalDiagDiffCurv_pair_eq_orthoSlotSubstSum` with the folded-pairing collapse
`orthoSlotSubstSum_eq_neg_folded_pairing` (over the explicit orthonormal frame
`B_i := smoothOrthoFrame g x i`, basis `bse := smoothOrthoFrame_center_basis`), the family sum over `a`
of the `(0, s)` fibre pairing of `tensor0SAsRS (nablaTensor0SCurv g s (V a) (V a) (V b) A)` against
`∇_{V b} S` equals the negated sum over slots `k` of the metric pairing of the slot-`k` substitution of
`A_x` by the frame-summed differentiated-curvature endomorphism `T_x := nablaBaseSlotCurvFrameSumCLM`. -/
private lemma parsevalDiagDiffCurv_pair_eq_neg_folded
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s)
    {N : ℕ} (V : Fin N → Π b : M, TangentSpace I b)
    (hV : ∀ a, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => (⟨b, V a b⟩ : TotalSpace E (TangentSpace I))))
    (hPar : ∀ (x : M) (u : TangentSpace I x),
      (∑ a : Fin N, g.inner x (V a x) u • V a x) = u) (b : Fin N) (x : M) :
    (∑ a : Fin N, tensorInnerPointwise (I := I) (M := M) g 0 s x
        (TensorRSSpace.toModel
          (tensor0SAsRS (I := I) (M := M) x
            (nablaTensor0SCurv (I := I) g s ⟨fun b => V a b, hV a⟩ ⟨fun b => V a b, hV a⟩
              ⟨fun y => V b y, hV b⟩
              (fun y : M =>
                (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace s I y from S.toSection y)
                  (unitZeroSec (I := I) (M := M) y)) x)))
        (TensorRSSpace.toModel (bochnerGradSlot0 (I := I) (M := M) g s S (V b) x))) =
      - ∑ k : Fin s,
          tensorInnerPointwise (I := I) (M := M) g 0 s x
            (TensorRSSpace.toModel
              (tensor0SAsRS (I := I) (M := M) x
                (tensorSlotSubstCLM (I := I) s x
                  (tangentSlotCLM (I := I) s k
                    (nablaBaseSlotCurvFrameSumCLM (I := I) g
                      (fun i => ContMDiffSection.mk (smoothOrthoFrame (I := I) g x i)
                        (smoothOrthoFrame_smooth (I := I) g x i))
                      ⟨fun y => V b y, hV b⟩ x))
                  ((fun y : M =>
                    (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace s I y from S.toSection y)
                      (unitZeroSec (I := I) (M := M) y)) x))))
            (TensorRSSpace.toModel
              (tensor0SAsRS (I := I) (M := M) x
                (gradCurry0 (I := I) (M := M) g s S x (V b x)))) := by
  classical
  obtain ⟨bse, hbse⟩ := smoothOrthoFrame_center_basis (I := I) (M := M) g x
  rw [parsevalDiagDiffCurv_pair_eq_orthoSlotSubstSum (I := I) (M := M) g s S V hV hPar b x bse hbse]
  exact orthoSlotSubstSum_eq_neg_folded_pairing (I := I) (M := M) g s x
    ((fun y : M =>
      (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace s I y from S.toSection y)
        (unitZeroSec (I := I) (M := M) y)) x)
    (gradCurry0 (I := I) (M := M) g s S x (V b x))
    (fun i => ContMDiffSection.mk (smoothOrthoFrame (I := I) g x i)
      (smoothOrthoFrame_smooth (I := I) g x i)) (fun _ => rfl)
    ⟨fun y => V b y, hV b⟩ bse hbse

set_option linter.unusedSectionVars false in
/-- **The slot-`k` substituted differentiated-curvature operator pairing, opened in the orthonormal
frame (the explicit metric-trace form).** For the orthonormal frame `B_i := smoothOrthoFrame g x i`,
the frame-summed differentiated-curvature endomorphism `T_x := nablaBaseSlotCurvFrameSumCLM g B Vb x`,
and `(0, s)`-tensors `A, D`, the `(0, s)` metric pairing of the slot-`k` substitution of `A` by `T_x`
against `D` expands as the explicit triple frame sum
```
⟨tensor0SAsRS (slotSubst_k T_x A), tensor0SAsRS D⟩_g
  = ∑_J ∑_m g(B_m, T_x B_{Jk}) · toModel(A)(update (B∘J) k B_m) · toModel(D)(B∘J).
```
This is `tensorInnerPointwise_tensor0SAsRS_eq_frameSum` (H1) opening the pairing into the frame double
sum, `toModel_tensorSlotSubst_tangentSlot_apply` naming the slot-`k` insertion `T_x B_{Jk}`, and the
orthonormal expansion `T_x B_{Jk} = ∑_m g(B_m, T_x B_{Jk}) • B_m`
(`orthonormal_tangent_expansion`) pushed through the slot-`k` multilinearity of `toModel A`
(`map_update_sum`, `map_update_smul`). -/
private lemma slotSubstPairing_eq_frameTripleSum
    (g : SmoothRiemannianMetric I M) (s : ℕ) (x : M)
    (A D : Tensor0SSpace s I x) (k : Fin s)
    (B : Fin (Module.finrank ℝ E) → Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (_hB : ∀ i, B i = ContMDiffSection.mk (smoothOrthoFrame (I := I) g x i)
      (smoothOrthoFrame_smooth (I := I) g x i))
    (Vb : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (bse : Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I x))
    (hbse : ∀ i, bse i = smoothOrthoFrame (I := I) g x i x) :
    tensorInnerPointwise (I := I) (M := M) g 0 s x
        (TensorRSSpace.toModel
          (tensor0SAsRS (I := I) (M := M) x
            (tensorSlotSubstCLM (I := I) s x
              (tangentSlotCLM (I := I) s k (nablaBaseSlotCurvFrameSumCLM (I := I) g B Vb x)) A)))
        (TensorRSSpace.toModel (tensor0SAsRS (I := I) (M := M) x D)) =
      ∑ J : Fin s → Fin (Module.finrank ℝ E),
        (∑ m : Fin (Module.finrank ℝ E),
          g.inner x (smoothOrthoFrame (I := I) g x m x)
              (nablaBaseSlotCurvFrameSumCLM (I := I) g B Vb x
                (smoothOrthoFrame (I := I) g x (J k) x)) *
            Tensor0SSpace.toModel A
              (Function.update (fun j => smoothOrthoFrame (I := I) g x (J j) x) k
                (smoothOrthoFrame (I := I) g x m x))) *
          Tensor0SSpace.toModel D (fun j => smoothOrthoFrame (I := I) g x (J j) x) := by
  classical
  have horth : ∀ a b : Fin (Module.finrank ℝ E),
      g.inner x (smoothOrthoFrame (I := I) g x a x) (smoothOrthoFrame (I := I) g x b x)
        = if a = b then 1 else 0 :=
    fun a b => smoothOrthoFrame_orthonormal_at_center (I := I) g x a b
  rw [tensorInnerPointwise_tensor0SAsRS_eq_frameSum (I := I) (M := M) g s x _ D
    (fun j => smoothOrthoFrame (I := I) g x j x) bse rfl hbse horth]
  refine Finset.sum_congr rfl (fun J _ => ?_)
  rw [toModel_tensorSlotSubst_tangentSlot_apply (I := I) k
    (nablaBaseSlotCurvFrameSumCLM (I := I) g B Vb x) A
    (fun j => smoothOrthoFrame (I := I) g x (J j) x)]
  congr 1
  -- Expand the inserted vector `T_x B_{Jk}` over the orthonormal frame and push through slot `k`.
  have hexp : (nablaBaseSlotCurvFrameSumCLM (I := I) g B Vb x
        ((fun j => smoothOrthoFrame (I := I) g x (J j) x) k)) =
      ∑ m : Fin (Module.finrank ℝ E),
        g.inner x (smoothOrthoFrame (I := I) g x m x)
            (nablaBaseSlotCurvFrameSumCLM (I := I) g B Vb x
              (smoothOrthoFrame (I := I) g x (J k) x)) •
          smoothOrthoFrame (I := I) g x m x :=
    (orthonormal_tangent_expansion (I := I) (M := M) g x
      (fun m => smoothOrthoFrame (I := I) g x m x) horth
      (nablaBaseSlotCurvFrameSumCLM (I := I) g B Vb x
        (smoothOrthoFrame (I := I) g x (J k) x))).symm
  conv_lhs => rw [hexp]
  have hsum := (Tensor0SSpace.toModel A).toMultilinearMap.map_update_sum
    (Finset.univ : Finset (Fin (Module.finrank ℝ E))) k
    (fun m => g.inner x (smoothOrthoFrame (I := I) g x m x)
        (nablaBaseSlotCurvFrameSumCLM (I := I) g B Vb x
          (smoothOrthoFrame (I := I) g x (J k) x)) •
      smoothOrthoFrame (I := I) g x m x)
    (fun j => smoothOrthoFrame (I := I) g x (J j) x)
  have hsmul : ∀ m : Fin (Module.finrank ℝ E),
      (Tensor0SSpace.toModel A).toMultilinearMap
          (Function.update (fun j => smoothOrthoFrame (I := I) g x (J j) x) k
            (g.inner x (smoothOrthoFrame (I := I) g x m x)
                (nablaBaseSlotCurvFrameSumCLM (I := I) g B Vb x
                  (smoothOrthoFrame (I := I) g x (J k) x)) •
              smoothOrthoFrame (I := I) g x m x)) =
        g.inner x (smoothOrthoFrame (I := I) g x m x)
            (nablaBaseSlotCurvFrameSumCLM (I := I) g B Vb x
              (smoothOrthoFrame (I := I) g x (J k) x)) *
          Tensor0SSpace.toModel A
            (Function.update (fun j => smoothOrthoFrame (I := I) g x (J j) x) k
              (smoothOrthoFrame (I := I) g x m x)) := by
    intro m
    rw [(Tensor0SSpace.toModel A).toMultilinearMap.map_update_smul, smul_eq_mul]
    rfl
  rw [show Tensor0SSpace.toModel A
        (Function.update (fun j => smoothOrthoFrame (I := I) g x (J j) x) k
          (∑ m : Fin (Module.finrank ℝ E),
            g.inner x (smoothOrthoFrame (I := I) g x m x)
                (nablaBaseSlotCurvFrameSumCLM (I := I) g B Vb x
                  (smoothOrthoFrame (I := I) g x (J k) x)) •
              smoothOrthoFrame (I := I) g x m x)) =
      (Tensor0SSpace.toModel A).toMultilinearMap
        (Function.update (fun j => smoothOrthoFrame (I := I) g x (J j) x) k
          (∑ m : Fin (Module.finrank ℝ E),
            g.inner x (smoothOrthoFrame (I := I) g x m x)
                (nablaBaseSlotCurvFrameSumCLM (I := I) g B Vb x
                  (smoothOrthoFrame (I := I) g x (J k) x)) •
              smoothOrthoFrame (I := I) g x m x)) from rfl, hsum]
  exact Finset.sum_congr rfl (fun m _ => hsmul m)

set_option linter.unusedSectionVars false in
/-- **The frame-summed differentiated-curvature inner factor, split into the differentiated-Ricci
difference (the once-contracted second Bianchi, value form at the frame).** For the orthonormal frame
`B_i := smoothOrthoFrame g x i`, the frame-summed differentiated-curvature endomorphism
`T_x := nablaBaseSlotCurvFrameSumCLM g B Vb x` (`Vb := V b`), and frame indices `m, p`, the metric
factor `g(B_m, T_x B_p)` equals the differentiated-Ricci difference
```
g(B_m, T_x B_p) = ∇_{ext B_m} Ric(Vb, ext B_p) − ∇_{ext B_p} Ric(ext B_m, Vb),
```
where `ext` is the smooth tangent extension `smoothExtensionTangent`.  This is the metric symmetry
`g.symm` followed by the once-contracted second Bianchi `inner_nablaBaseSlotCurvFrameSum_eq_nablaRicci_sub`
(with the smooth extensions `ext B_m`, `ext B_p` of the frame values as the acted and pairing fields). -/
private lemma innerFrame_nablaBaseSlotCurvFrameSum_eq_nablaRicci_sub
    (g : SmoothRiemannianMetric I M) {x : M}
    (Vb : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (B : Fin (Module.finrank ℝ E) → Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (hB : ∀ i, B i = ContMDiffSection.mk (smoothOrthoFrame (I := I) g x i)
      (smoothOrthoFrame_smooth (I := I) g x i)) (m p : Fin (Module.finrank ℝ E)) :
    g.inner x (smoothOrthoFrame (I := I) g x m x)
        (nablaBaseSlotCurvFrameSumCLM (I := I) g B Vb x
          (smoothOrthoFrame (I := I) g x p x)) =
      nablaRicci (I := I) g
          (fun b => smoothExtensionTangent (I := I) x (smoothOrthoFrame (I := I) g x m x) b)
          (fun b => Vb b)
          (fun b => smoothExtensionTangent (I := I) x (smoothOrthoFrame (I := I) g x p x) b) x -
        nablaRicci (I := I) g
          (fun b => smoothExtensionTangent (I := I) x (smoothOrthoFrame (I := I) g x p x) b)
          (fun b => smoothExtensionTangent (I := I) x (smoothOrthoFrame (I := I) g x m x) b)
          (fun b => Vb b) x := by
  classical
  rw [g.symm x (smoothOrthoFrame (I := I) g x m x) _]
  have hT : (nablaBaseSlotCurvFrameSumCLM (I := I) g B Vb x
        (smoothOrthoFrame (I := I) g x p x)) =
      ∑ i : Fin (Module.finrank ℝ E),
        nablaBaseSlotCurv (I := I) g
          (ContMDiffSection.mk (smoothOrthoFrame (I := I) g x i)
            (smoothOrthoFrame_smooth (I := I) g x i))
          (ContMDiffSection.mk (smoothOrthoFrame (I := I) g x i)
            (smoothOrthoFrame_smooth (I := I) g x i))
          ⟨fun b => Vb b, Vb.contMDiff⟩ x (smoothOrthoFrame (I := I) g x p x) := by
    rw [nablaBaseSlotCurvFrameSumCLM_apply]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [hB i]
    rfl
  rw [hT]
  have hkey := inner_nablaBaseSlotCurvFrameSum_eq_nablaRicci_sub (I := I) g
    (Vb := fun b => Vb b)
    (U := fun b => smoothExtensionTangent (I := I) x (smoothOrthoFrame (I := I) g x m x) b)
    Vb.contMDiff (smoothExtensionTangent_contMDiff (I := I) x (smoothOrthoFrame (I := I) g x m x))
    (smoothOrthoFrame (I := I) g x p x)
  rw [smoothExtensionTangent_eq (I := I) x (smoothOrthoFrame (I := I) g x m x)] at hkey
  rw [hkey]

set_option linter.unusedSectionVars false in
/-- **The Parseval-frame diagonal differentiated-curvature trace pairing, at a point, as the explicit
once-contracted second-Bianchi frame triple sum.** Chaining the three landed reductions
`parsevalDiagDiffCurv_pair_eq_neg_folded` (the metric-trace opening to the negated slot fold),
`slotSubstPairing_eq_frameTripleSum` (the explicit frame double sum of each slot fold), and
`innerFrame_nablaBaseSlotCurvFrameSum_eq_nablaRicci_sub` (each frame coefficient `g(B_m, T_x B_{Jk})` as
the differentiated-Ricci difference `ν₁ − ν₂`), the family sum over `a` of the `(0, s)` fibre pairing of
`tensor0SAsRS (nablaTensor0SCurv g s (V a) (V a) (V b) A)` against `∇_{V b} S` is the negated slot/frame
triple sum of `[ν₁(m, J k) − ν₂(m, J k)] · A_x(update (B∘J) k B_m) · D_b(B∘J)`, with
`ν₁(m, p) = (∇_{ext B_m} Ric)(V b, ext B_p)`, `ν₂(m, p) = (∇_{ext B_p} Ric)(ext B_m, V b)`,
`B i := smoothOrthoFrame g x i x`, `A_x := (S.toSection x)(unit)`, and `D_b := gradCurry0 g s S x (V b x)`. -/
private lemma parsevalDiagDiffCurv_pair_eq_nablaRicci_tripleSum
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s)
    {N : ℕ} (V : Fin N → Π b : M, TangentSpace I b)
    (hV : ∀ a, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => (⟨b, V a b⟩ : TotalSpace E (TangentSpace I))))
    (hPar : ∀ (x : M) (u : TangentSpace I x),
      (∑ a : Fin N, g.inner x (V a x) u • V a x) = u) (b : Fin N) (x : M) :
    (∑ a : Fin N, tensorInnerPointwise (I := I) (M := M) g 0 s x
        (TensorRSSpace.toModel
          (tensor0SAsRS (I := I) (M := M) x
            (nablaTensor0SCurv (I := I) g s ⟨fun b => V a b, hV a⟩ ⟨fun b => V a b, hV a⟩
              ⟨fun y => V b y, hV b⟩
              (fun y : M =>
                (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace s I y from S.toSection y)
                  (unitZeroSec (I := I) (M := M) y)) x)))
        (TensorRSSpace.toModel (bochnerGradSlot0 (I := I) (M := M) g s S (V b) x))) =
      - ∑ k : Fin s, ∑ J : Fin s → Fin (Module.finrank ℝ E),
          (∑ m : Fin (Module.finrank ℝ E),
            (nablaRicci (I := I) g
                (fun c => smoothExtensionTangent (I := I) x (smoothOrthoFrame (I := I) g x m x) c)
                (fun c => (⟨fun y => V b y, hV b⟩ :
                  Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) c)
                (fun c => smoothExtensionTangent (I := I) x
                  (smoothOrthoFrame (I := I) g x (J k) x) c) x -
              nablaRicci (I := I) g
                (fun c => smoothExtensionTangent (I := I) x
                  (smoothOrthoFrame (I := I) g x (J k) x) c)
                (fun c => smoothExtensionTangent (I := I) x (smoothOrthoFrame (I := I) g x m x) c)
                (fun c => (⟨fun y => V b y, hV b⟩ :
                  Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) c) x) *
            Tensor0SSpace.toModel
              ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from S.toSection x)
                (unitZeroSec (I := I) (M := M) x))
              (Function.update (fun j => smoothOrthoFrame (I := I) g x (J j) x) k
                (smoothOrthoFrame (I := I) g x m x))) *
          Tensor0SSpace.toModel (gradCurry0 (I := I) (M := M) g s S x (V b x))
            (fun j => smoothOrthoFrame (I := I) g x (J j) x) := by
  classical
  rw [parsevalDiagDiffCurv_pair_eq_neg_folded (I := I) (M := M) g s S V hV hPar b x]
  rw [Finset.sum_congr rfl (fun k _ =>
    slotSubstPairing_eq_frameTripleSum (I := I) (M := M) g s x
      ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from S.toSection x)
        (unitZeroSec (I := I) (M := M) x))
      (gradCurry0 (I := I) (M := M) g s S x (V b x)) k
      (fun i => ContMDiffSection.mk (smoothOrthoFrame (I := I) g x i)
        (smoothOrthoFrame_smooth (I := I) g x i)) (fun _ => rfl)
      ⟨fun y => V b y, hV b⟩
      (Classical.choose (smoothOrthoFrame_center_basis (I := I) (M := M) g x))
      (Classical.choose_spec (smoothOrthoFrame_center_basis (I := I) (M := M) g x)))]
  congr 1
  refine Finset.sum_congr rfl (fun k _ => ?_)
  refine Finset.sum_congr rfl (fun J _ => ?_)
  congr 1
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [innerFrame_nablaBaseSlotCurvFrameSum_eq_nablaRicci_sub (I := I) g
    ⟨fun y => V b y, hV b⟩
    (fun i => ContMDiffSection.mk (smoothOrthoFrame (I := I) g x i)
      (smoothOrthoFrame_smooth (I := I) g x i)) (fun _ => rfl) m (J k)]

set_option linter.unusedSectionVars false in
/-- **The differentiated-curvature trace double sum is the negated `b`-summed integral of the
differentiated-Ricci frame triple sum.**  For a fixed smooth Parseval frame family, the
differentiated-curvature trace double sum `D := ∑_a ∑_b ∫ ⟨nablaDiffCurvTrace, ∇_{V b} S⟩` equals the
negated single sum over `b` of the integral of the once-contracted second-Bianchi
differentiated-Ricci frame triple sum `tripleSum(b, x)` (the `ν₁ − ν₂` content of
`parsevalDiagDiffCurv_pair_eq_nablaRicci_tripleSum`):
```
D = − ∑_b ∫ tripleSum(b, x) ∂μ.
```
This is the connector `tensorInnerScalar_nablaDiffCurvTrace_eq_tensorInnerPointwise_nablaTensor0SCurv`
identifying the trace with the `nablaTensor0SCurv` diagonal-trace pairing, the finite-sum interchange
`Finset.sum_comm` to bring the `b`-sum outside, the linearity `integral_finset_sum` /
`Finset.sum_comm` of the integral over the `a`-sum, and the landed differentiated-Ricci collapse
`parsevalDiagDiffCurv_pair_eq_nablaRicci_tripleSum`.  It is the differentiated-Ricci (`ν₁`-arm) read
of `D`, the explicit `nablaRicci` form the proof of the primitive `D = −(G₁ + I₂)`
acts on. -/
private lemma nablaDiffCurvTrace_doubleSum_eq_neg_tripleSum_bSum
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s)
    {N : ℕ} (V : Fin N → Π b : M, TangentSpace I b)
    (hV : ∀ a, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => (⟨b, V a b⟩ : TotalSpace E (TangentSpace I))))
    (hPar : ∀ (x : M) (u : TangentSpace I x),
      (∑ a : Fin N, g.inner x (V a x) u • V a x) = u) :
    (∑ a : Fin N, ∑ b : Fin N,
        ∫ x, tensorInnerScalar (I := I) (M := M) g 0 s
            (nablaDiffCurvTraceCc (I := I) (M := M) g s S (hV a) (hV b)).toSection
            (bochnerGradSlot0Cc (I := I) (M := M) g s S (hV b)).toSection x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g)) =
      - ∑ b : Fin N,
          ∫ x, (∑ k : Fin s, ∑ J : Fin s → Fin (Module.finrank ℝ E),
              (∑ m : Fin (Module.finrank ℝ E),
                (nablaRicci (I := I) g
                    (fun c => smoothExtensionTangent (I := I) x (smoothOrthoFrame (I := I) g x m x) c)
                    (fun c => (⟨fun y => V b y, hV b⟩ :
                      Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) c)
                    (fun c => smoothExtensionTangent (I := I) x
                      (smoothOrthoFrame (I := I) g x (J k) x) c) x -
                  nablaRicci (I := I) g
                    (fun c => smoothExtensionTangent (I := I) x
                      (smoothOrthoFrame (I := I) g x (J k) x) c)
                    (fun c => smoothExtensionTangent (I := I) x (smoothOrthoFrame (I := I) g x m x) c)
                    (fun c => (⟨fun y => V b y, hV b⟩ :
                      Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) c) x) *
                Tensor0SSpace.toModel
                  ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from S.toSection x)
                    (unitZeroSec (I := I) (M := M) x))
                  (Function.update (fun j => smoothOrthoFrame (I := I) g x (J j) x) k
                    (smoothOrthoFrame (I := I) g x m x))) *
              Tensor0SSpace.toModel (gradCurry0 (I := I) (M := M) g s S x (V b x))
                (fun j => smoothOrthoFrame (I := I) g x (J j) x))
            ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  classical
  -- Identify the trace pairing with the `nablaTensor0SCurv` diagonal-trace pairing, term by term.
  have hconn : ∀ a b : Fin N,
      (∫ x, tensorInnerScalar (I := I) (M := M) g 0 s
            (nablaDiffCurvTraceCc (I := I) (M := M) g s S (hV a) (hV b)).toSection
            (bochnerGradSlot0Cc (I := I) (M := M) g s S (hV b)).toSection x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g)) =
        ∫ x, tensorInnerPointwise (I := I) (M := M) g 0 s x
            (TensorRSSpace.toModel
              (tensor0SAsRS (I := I) (M := M) x
                (nablaTensor0SCurv (I := I) g s ⟨fun b => V a b, hV a⟩ ⟨fun b => V a b, hV a⟩
                  ⟨fun y => V b y, hV b⟩
                  (fun y : M =>
                    (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace s I y from S.toSection y)
                      (unitZeroSec (I := I) (M := M) y)) x)))
            (TensorRSSpace.toModel (bochnerGradSlot0 (I := I) (M := M) g s S (V b) x))
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
    intro a b
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    exact tensorInnerScalar_nablaDiffCurvTrace_eq_tensorInnerPointwise_nablaTensor0SCurv
      (I := I) (M := M) g s S (hV a) (hV b) x
  rw [Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => hconn a b))]
  -- Bring the `b`-sum outside, sum the integrand over `a`, then collapse via the tripleSum lemma.
  rw [Finset.sum_comm]
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  -- Per-`a` integrability of the `nablaTensor0SCurv` diagonal-trace pairing (the Cc cross-pairing).
  have hint : ∀ a : Fin N, Integrable
      (fun x : M => tensorInnerPointwise (I := I) (M := M) g 0 s x
        (TensorRSSpace.toModel
          (tensor0SAsRS (I := I) (M := M) x
            (nablaTensor0SCurv (I := I) g s ⟨fun b => V a b, hV a⟩ ⟨fun b => V a b, hV a⟩
              ⟨fun y => V b y, hV b⟩
              (fun y : M =>
                (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace s I y from S.toSection y)
                  (unitZeroSec (I := I) (M := M) y)) x)))
        (TensorRSSpace.toModel (bochnerGradSlot0 (I := I) (M := M) g s S (V b) x)))
      (riemannianVolumeMeasure (I := I) (M := M) g) := by
    intro a
    refine (SmoothCcTensor.integrable_inner_cross (I := I) (M := M)
      (nablaDiffCurvTraceCc (I := I) (M := M) g s S (hV a) (hV b))
      (bochnerGradSlot0Cc (I := I) (M := M) g s S (hV b))).congr
      (Filter.Eventually.of_forall (fun x => ?_))
    simp only [SmoothCcTensor.toFun_apply,
      nablaDiffCurvTraceCc_toSection_eq_tensor0SAsRS_nablaTensor0SCurv
        (I := I) (M := M) g s S (hV a) (hV b) x,
      bochnerGradSlot0Cc_toSection_apply (I := I) (M := M) g s S (hV b) x]
  rw [← MeasureTheory.integral_finset_sum Finset.univ (fun a _ => hint a),
    ← MeasureTheory.integral_neg]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
  simp only []
  rw [parsevalDiagDiffCurv_pair_eq_nablaRicci_tripleSum (I := I) (M := M) g s S V hV hPar b x]

set_option linter.unusedSectionVars false in
/-- **The per-direction group-`2` frame-summed covariant integration by parts.**  For a fixed Parseval
frame family and a fixed `b`, the frame sum over `a` of the group-`2` integrand
`⟨∇_{V a}(R(V a, V b) S), ∇_{V b} S⟩` equals the frame sum over `a` of the IBP residue integral.  This
is the per-`b` slice of `bochnerFoldGroupSum_elt2_eq_residueSum` (the frame-summed engine
`integral_frameSummed_covDeriv_combined_eq_zero` at this fixed `b`). -/
private lemma bochnerGroupElt2_perB_integral_eq_residueSum (g : SmoothRiemannianMetric I M) (s : ℕ)
    (S : SmoothCcTensor g 0 s) {N : ℕ} (V : Fin N → Π b : M, TangentSpace I b)
    (hV : ∀ a, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => (⟨b, V a b⟩ : TotalSpace E (TangentSpace I)))) (b : Fin N) :
    (∑ a : Fin N,
        ∫ x, tensorInnerPointwise (I := I) (M := M) g 0 s x
            (TensorRSSpace.toModel (bochnerGroupElt2 (I := I) (M := M) g s S (V a) (V b) x))
            (TensorRSSpace.toModel (bochnerGradSlot0 (I := I) (M := M) g s S (V b) x))
          ∂(riemannianVolumeMeasure (I := I) (M := M) g)) =
      ∑ a : Fin N,
        ∫ x, bochnerGroup2Residue (I := I) (M := M) g s S (V a) (V b)
            ⟨fun y : M => V a y, hV a⟩ x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  classical
  have hintG2 : ∀ a : Fin N, Integrable
      (fun x : M => tensorInnerPointwise (I := I) (M := M) g 0 s x
        (TensorRSSpace.toModel (bochnerGroupElt2 (I := I) (M := M) g s S (V a) (V b) x))
        (TensorRSSpace.toModel (bochnerGradSlot0 (I := I) (M := M) g s S (V b) x)))
      (riemannianVolumeMeasure (I := I) (M := M) g) := by
    intro a
    refine (SmoothCcTensor.integrable_inner_cross (I := I) (M := M)
      (bochnerGroupElt2Cc (I := I) (M := M) g s S (hV a) (hV b))
      (bochnerGradSlot0Cc (I := I) (M := M) g s S (hV b))).congr
      (Filter.Eventually.of_forall (fun x => ?_))
    simp only [SmoothCcTensor.toFun_apply,
      bochnerGroupElt2Cc_toSection_eq (I := I) (M := M) g s S (hV a) (hV b) x,
      bochnerGradSlot0Cc_toSection_apply (I := I) (M := M) g s S (hV b) x]
  have heng := integral_frameSummed_covDeriv_combined_eq_zero (I := I) (M := M) g 0 s
    (fun a : Fin N => (⟨fun y : M => V a y, hV a⟩ : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯))
    (fun a : Fin N => riemannSecCc (I := I) (M := M) g s S (hV a) (hV b))
    (bochnerGradSlot0Cc (I := I) (M := M) g s S (hV b))
  have hpt : ∀ a : Fin N, ∀ x : M,
      tensorInnerPointwise_0s (I := I) (M := M) (0 + s) g x
            (Tensor0SSpace.toModel
              (loweredCovDerivAlongVF (I := I) (M := M) g 0 s
                (riemannSecCc (I := I) (M := M) g s S (hV a) (hV b)).toSection
                ⟨fun y : M => V a y, hV a⟩ x))
            (Tensor0SSpace.toModel
              (liftedTensorSection (I := I) (M := M) g 0 s
                (bochnerGradSlot0Cc (I := I) (M := M) g s S (hV b)).toSection x))
          + tensorInnerPointwise_0s (I := I) (M := M) (0 + s) g x
              (Tensor0SSpace.toModel
                (liftedTensorSection (I := I) (M := M) g 0 s
                  (riemannSecCc (I := I) (M := M) g s S (hV a) (hV b)).toSection x))
              (Tensor0SSpace.toModel
                (loweredCovDerivAlongVF (I := I) (M := M) g 0 s
                  (bochnerGradSlot0Cc (I := I) (M := M) g s S (hV b)).toSection
                  ⟨fun y : M => V a y, hV a⟩ x))
          + tensorInnerScalar (I := I) (M := M) g 0 s
              (riemannSecCc (I := I) (M := M) g s S (hV a) (hV b)).toSection
              (bochnerGradSlot0Cc (I := I) (M := M) g s S (hV b)).toSection x
            * DifferentialGeometry.Integral.DivergenceTheorem.divergence_g (I := I) g
                ⟨fun y : M => V a y, hV a⟩ x =
        tensorInnerPointwise (I := I) (M := M) g 0 s x
            (TensorRSSpace.toModel (bochnerGroupElt2 (I := I) (M := M) g s S (V a) (V b) x))
            (TensorRSSpace.toModel (bochnerGradSlot0 (I := I) (M := M) g s S (V b) x))
          - bochnerGroup2Residue (I := I) (M := M) g s S (V a) (V b)
              ⟨fun y : M => V a y, hV a⟩ x := by
    intro a x
    have h1 := engineFirstSlot_eq_group2_integrand (I := I) (M := M) g s S V hV a b x
    have h2 := engineRest_eq_neg_group2Residue (I := I) (M := M) g s S V hV a b x
    linarith [h1, h2]
  rw [Finset.sum_congr rfl (fun a _ =>
    MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (hpt a)))] at heng
  rw [Finset.sum_congr rfl (fun a _ =>
    MeasureTheory.integral_sub (hintG2 a)
      (integrable_bochnerGroup2Residue (I := I) (M := M) g s S V hV a b))] at heng
  rw [Finset.sum_sub_distrib] at heng
  linarith [heng]

set_option linter.unusedSectionVars false in
/-- The `(0, t)`-fibre `toModel` map distributes over a weighted finite sum. -/
private lemma toModel_weighted_finsetSum (t : ℕ) (x : M) {ι : Type*} (fs : Finset ι)
    (c : ι → ℝ) (A : ι → TensorRSSpace 0 t I x) :
    TensorRSSpace.toModel (∑ i ∈ fs, c i • A i) =
      ∑ i ∈ fs, c i • TensorRSSpace.toModel (A i) := by
  classical
  induction fs using Finset.induction with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, TensorRSSpace.toModel_zero]
  | insert i fs hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, TensorRSSpace.toModel_add,
      TensorRSSpace.toModel_smul, ih]

set_option linter.unusedSectionVars false in
/-- **The double-Parseval expansion of a tangent bilinear form.** Every `ℝ`-bilinear scalar form
on the tangent fibre at `x` expands over a `g_x`-Parseval family in both slots:
`B u p = ∑_c ∑_d ⟨V c, u⟩_g ⟨V d, p⟩_g · B (V c) (V d)`. -/
private lemma parsevalFrame_bilin_double_expansion
    (g : SmoothRiemannianMetric I M)
    {N : ℕ} (V : Fin N → Π b : M, TangentSpace I b)
    (hPar : ∀ (x : M) (u : TangentSpace I x),
      (∑ a : Fin N, g.inner x (V a x) u • V a x) = u) (x : M)
    (B : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ)
    (u p : TangentSpace I x) :
    B u p = ∑ c : Fin N, ∑ d : Fin N,
      g.inner x (V c x) u * g.inner x (V d x) p * B (V c x) (V d x) := by
  classical
  have hleft : B u p = ∑ c : Fin N, g.inner x (V c x) u * B (V c x) p := by
    conv_lhs => rw [← hPar x u]
    rw [map_sum B _ Finset.univ, LinearMap.sum_apply]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    rw [map_smul, LinearMap.smul_apply, smul_eq_mul]
  rw [hleft]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  have hright : B (V c x) p = ∑ d : Fin N, g.inner x (V d x) p * B (V c x) (V d x) := by
    conv_lhs => rw [← hPar x p]
    rw [map_sum (B (V c x)) _ Finset.univ]
    refine Finset.sum_congr rfl (fun d _ => ?_)
    rw [map_smul, smul_eq_mul]
  rw [hright, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun d _ => ?_)
  ring

set_option linter.unusedSectionVars false in
/-- **The Parseval-frame covariant-derivative pair antisymmetry, bilinear-contracted form.** For a
fixed smooth Parseval frame family `V`, any direction field `W`, and any `ℝ`-bilinear scalar form
`B` on the tangent fibre at `x`, the frame-diagonal covariant-derivative pair sum vanishes:
`∑_b [B(∇_{W} V_b, V_b) + B(V_b, ∇_{W} V_b)] = 0`.  This is the cometric-parallel antisymmetry
`parsevalFrame_sum_covDeriv_inner_antisymm` contracted against `B` through the double-Parseval
expansion of both slots. -/
private lemma parsevalFrame_sum_bilin_covDeriv_pair_antisymm
    (g : SmoothRiemannianMetric I M)
    {N : ℕ} (V : Fin N → Π b : M, TangentSpace I b)
    (hV : ∀ a, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => (⟨b, V a b⟩ : TotalSpace E (TangentSpace I))))
    (hPar : ∀ (x : M) (u : TangentSpace I x),
      (∑ a : Fin N, g.inner x (V a x) u • V a x) = u)
    (W : Π b : M, TangentSpace I b) (x : M)
    (B : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ) :
    (∑ b : Fin N,
        (B ((LeviCivita (I := I) g).toFun (V b) x (W x)) (V b x) +
          B (V b x) ((LeviCivita (I := I) g).toFun (V b) x (W x)))) = 0 := by
  classical
  have hexp : ∀ b : Fin N,
      B ((LeviCivita (I := I) g).toFun (V b) x (W x)) (V b x) +
        B (V b x) ((LeviCivita (I := I) g).toFun (V b) x (W x)) =
      ∑ c : Fin N, ∑ d : Fin N,
        (g.inner x ((LeviCivita (I := I) g).toFun (V b) x (W x)) (V c x) *
            g.inner x (V b x) (V d x) +
          g.inner x (V b x) (V c x) *
            g.inner x ((LeviCivita (I := I) g).toFun (V b) x (W x)) (V d x)) *
          B (V c x) (V d x) := by
    intro b
    rw [parsevalFrame_bilin_double_expansion (I := I) (M := M) g V hPar x B
        ((LeviCivita (I := I) g).toFun (V b) x (W x)) (V b x),
      parsevalFrame_bilin_double_expansion (I := I) (M := M) g V hPar x B
        (V b x) ((LeviCivita (I := I) g).toFun (V b) x (W x)),
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun d _ => ?_)
    rw [g.symm x (V c x) ((LeviCivita (I := I) g).toFun (V b) x (W x)),
      g.symm x (V d x) (V b x), g.symm x (V c x) (V b x),
      g.symm x (V d x) ((LeviCivita (I := I) g).toFun (V b) x (W x))]
    ring
  rw [Finset.sum_congr rfl (fun b _ => hexp b)]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero (fun c _ => ?_)
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero (fun d _ => ?_)
  rw [← Finset.sum_mul]
  rw [parsevalFrame_sum_covDeriv_inner_antisymm (I := I) (M := M) g V hV hPar
    (U := V c) (P := V d) (W := W) (hV c) (hV d) x, zero_mul]

set_option linter.unusedSectionVars false in
/-- **The intrinsic divergence is the Parseval-frame covariant trace.** For a fixed `g_x`-Parseval
family `V` and any smooth tangent field `Z`,
`divᵍ Z (x) = ∑_c ⟨∇_{V c} Z, V c⟩_g` — the orthonormal-frame trace
(`divergence_g_eq_smoothOrthoFrame_trace`) converted to the fixed family by the bilinear trace
conversion `parseval_family_sum_bilin_eq`. -/
private lemma divergence_g_eq_parsevalFrame_trace
    (g : SmoothRiemannianMetric I M)
    {N : ℕ} (V : Fin N → Π b : M, TangentSpace I b)
    (hPar : ∀ (x : M) (u : TangentSpace I x),
      (∑ a : Fin N, g.inner x (V a x) u • V a x) = u)
    (Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    DifferentialGeometry.Integral.DivergenceTheorem.divergence_g (I := I) g Z x =
      ∑ c : Fin N,
        g.inner x ((LeviCivita (I := I) g).toFun Z.toFun x (V c x)) (V c x) := by
  classical
  set B : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ :=
    LinearMap.mk₂ ℝ
      (fun u p => g.inner x ((LeviCivita (I := I) g).toFun Z.toFun x u) p)
      (fun u₁ u₂ p => by
        beta_reduce
        rw [map_add ((LeviCivita (I := I) g).toFun Z.toFun x) u₁ u₂,
          map_add (g.inner x), ContinuousLinearMap.add_apply])
      (fun cc u p => by
        beta_reduce
        rw [map_smul ((LeviCivita (I := I) g).toFun Z.toFun x) cc u,
          map_smul (g.inner x), ContinuousLinearMap.smul_apply])
      (fun u p₁ p₂ => by
        beta_reduce
        rw [map_add (g.inner x ((LeviCivita (I := I) g).toFun Z.toFun x u)) p₁ p₂])
      (fun cc u p => by
        beta_reduce
        rw [map_smul (g.inner x ((LeviCivita (I := I) g).toFun Z.toFun x u)) cc p])
    with hB_def
  have hBapp : ∀ u p : TangentSpace I x,
      B u p = g.inner x ((LeviCivita (I := I) g).toFun Z.toFun x u) p := fun u p => rfl
  have hb := parseval_family_sum_bilin_eq (I := I) (M := M) g x (fun a => V a x)
    (fun u => hPar x u) (fun i => smoothOrthoFrame (I := I) g x i x)
    (fun i j => smoothOrthoFrame_orthonormal_at_center (I := I) g x i j) B
  rw [divergence_g_eq_smoothOrthoFrame_trace (I := I) g Z x]
  rw [show (∑ i : Fin (Module.finrank ℝ E),
        g.inner x
          ((LeviCivita (I := I) g).toFun Z.toFun x (smoothOrthoFrame (I := I) g x i x))
          (smoothOrthoFrame (I := I) g x i x)) =
      ∑ i : Fin (Module.finrank ℝ E),
        B (smoothOrthoFrame (I := I) g x i x) (smoothOrthoFrame (I := I) g x i x) from
    Finset.sum_congr rfl (fun i _ => (hBapp _ _).symm)]
  rw [← hb]
  exact Finset.sum_congr rfl (fun c _ => hBapp _ _)

set_option linter.unusedSectionVars false in
/-- **Term-(iii) telescoping: the curvature-slot frame derivative crosses to the gradient slot.**
For a fixed Parseval family and a fixed `a`, the frame sum over `b` of the pairing of
`R(∇_{V a} V b, V a) S` against `∇_{V b} S` equals the frame sum of the pairing of
`R(V a, V b) S` against `∇_{∇_{V a} V b} S`: the covariant-derivative pair antisymmetry
(`parsevalFrame_sum_bilin_covDeriv_pair_antisymm`) moves the frame derivative across the
bilinear pairing, and the `riemannOp` slot antisymmetry restores the slot order. -/
private lemma parsevalFrame_termIii_sum_eq
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s)
    {N : ℕ} (V : Fin N → Π b : M, TangentSpace I b)
    (hV : ∀ a, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => (⟨b, V a b⟩ : TotalSpace E (TangentSpace I))))
    (hPar : ∀ (x : M) (u : TangentSpace I x),
      (∑ a : Fin N, g.inner x (V a x) u • V a x) = u)
    (a : Fin N) (x : M) :
    (∑ b : Fin N,
        tensorInnerPointwise (I := I) (M := M) g 0 s x
          (TensorRSSpace.toModel
            (riemannOp (tensorCov (I := I) g 0 s) x
              ((LeviCivita (I := I) g).toFun (V b) x (V a x)) (V a x) (S.toSection x)))
          (TensorRSSpace.toModel
            ((tensorCov (I := I) g 0 s).toFun (fun y : M => S.toSection y) x (V b x)))) =
      ∑ b : Fin N,
        tensorInnerPointwise (I := I) (M := M) g 0 s x
          (TensorRSSpace.toModel
            (riemannOp (tensorCov (I := I) g 0 s) x (V a x) (V b x) (S.toSection x)))
          (TensorRSSpace.toModel
            ((tensorCov (I := I) g 0 s).toFun (fun y : M => S.toSection y) x
              ((LeviCivita (I := I) g).toFun (V b) x (V a x)))) := by
  classical
  set B : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ :=
    LinearMap.mk₂ ℝ
      (fun u p => tensorInnerPointwise (I := I) (M := M) g 0 s x
        (TensorRSSpace.toModel
          (riemannOp (tensorCov (I := I) g 0 s) x u (V a x) (S.toSection x)))
        (TensorRSSpace.toModel
          ((tensorCov (I := I) g 0 s).toFun (fun y : M => S.toSection y) x p)))
      (fun u₁ u₂ p => by
        beta_reduce
        rw [map_add (riemannOp (tensorCov (I := I) g 0 s) x) u₁ u₂,
          ContinuousLinearMap.add_apply, ContinuousLinearMap.add_apply,
          TensorRSSpace.toModel_add,
          tensorInnerPointwise_add_left (I := I) (M := M) g 0 s x])
      (fun cc u p => by
        beta_reduce
        rw [map_smul (riemannOp (tensorCov (I := I) g 0 s) x) cc u,
          ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply,
          TensorRSSpace.toModel_smul,
          tensorInnerPointwise_smul_left (I := I) (M := M) g 0 s x, smul_eq_mul])
      (fun u p₁ p₂ => by
        beta_reduce
        rw [map_add ((tensorCov (I := I) g 0 s).toFun (fun y : M => S.toSection y) x) p₁ p₂,
          TensorRSSpace.toModel_add,
          tensorInnerPointwise_add_right (I := I) (M := M) g 0 s x])
      (fun cc u p => by
        beta_reduce
        rw [map_smul ((tensorCov (I := I) g 0 s).toFun (fun y : M => S.toSection y) x) cc p,
          TensorRSSpace.toModel_smul,
          tensorInnerPointwise_smul_right (I := I) (M := M) g 0 s x, smul_eq_mul])
    with hB_def
  have h0 := parsevalFrame_sum_bilin_covDeriv_pair_antisymm (I := I) (M := M) g V hV hPar
    (V a) x B
  simp only [hB_def, LinearMap.mk₂_apply] at h0
  rw [Finset.sum_add_distrib] at h0
  have hswap : ∀ b : Fin N,
      tensorInnerPointwise (I := I) (M := M) g 0 s x
        (TensorRSSpace.toModel
          (riemannOp (tensorCov (I := I) g 0 s) x (V b x) (V a x) (S.toSection x)))
        (TensorRSSpace.toModel
          ((tensorCov (I := I) g 0 s).toFun (fun y : M => S.toSection y) x
            ((LeviCivita (I := I) g).toFun (V b) x (V a x)))) =
      - tensorInnerPointwise (I := I) (M := M) g 0 s x
        (TensorRSSpace.toModel
          (riemannOp (tensorCov (I := I) g 0 s) x (V a x) (V b x) (S.toSection x)))
        (TensorRSSpace.toModel
          ((tensorCov (I := I) g 0 s).toFun (fun y : M => S.toSection y) x
            ((LeviCivita (I := I) g).toFun (V b) x (V a x)))) := by
    intro b
    rw [riemannOp_swap (cov := tensorCov (I := I) g 0 s) x (V b x) (V a x) (S.toSection x),
      TensorRSSpace.toModel_neg,
      ← neg_one_smul ℝ (TensorRSSpace.toModel
        (riemannOp (tensorCov (I := I) g 0 s) x (V a x) (V b x) (S.toSection x))),
      tensorInnerPointwise_smul_left (I := I) (M := M) g 0 s x, neg_one_mul]
  rw [Finset.sum_congr rfl (fun b _ => hswap b)] at h0
  rw [Finset.sum_neg_distrib] at h0
  linarith [h0]

set_option linter.unusedSectionVars false in
/-- **Term-(iv) telescoping: the frame tension direction is the divergence weight.** For a fixed
Parseval family and a fixed `b`, the frame sum over `a` of the pairing of `R(V b, ∇_{V a} V a) S`
against `∇_{V b} S` equals the divergence-weighted curvature pairing sum
`∑_a ⟨R(V a, V b) S, ∇_{V b} S⟩ · divᵍ(V a)`: the diagonal frame derivative `∇_{V a} V a` expands
over the family in its direction slot, the covariant-derivative pair antisymmetry swaps the
derivative onto the frame trace, and the trace collapses to the intrinsic divergence
(`divergence_g_eq_parsevalFrame_trace`). -/
private lemma parsevalFrame_termIv_sum_eq
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s)
    {N : ℕ} (V : Fin N → Π b : M, TangentSpace I b)
    (hV : ∀ a, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => (⟨b, V a b⟩ : TotalSpace E (TangentSpace I))))
    (hPar : ∀ (x : M) (u : TangentSpace I x),
      (∑ a : Fin N, g.inner x (V a x) u • V a x) = u)
    (b : Fin N) (x : M) :
    (∑ a : Fin N,
        tensorInnerPointwise (I := I) (M := M) g 0 s x
          (TensorRSSpace.toModel
            (riemannOp (tensorCov (I := I) g 0 s) x (V b x)
              ((LeviCivita (I := I) g).toFun (V a) x (V a x)) (S.toSection x)))
          (TensorRSSpace.toModel
            ((tensorCov (I := I) g 0 s).toFun (fun y : M => S.toSection y) x (V b x)))) =
      ∑ a : Fin N,
        tensorInnerPointwise (I := I) (M := M) g 0 s x
          (TensorRSSpace.toModel
            (riemannOp (tensorCov (I := I) g 0 s) x (V a x) (V b x) (S.toSection x)))
          (TensorRSSpace.toModel
            ((tensorCov (I := I) g 0 s).toFun (fun y : M => S.toSection y) x (V b x))) *
        DifferentialGeometry.Integral.DivergenceTheorem.divergence_g (I := I) g
          ⟨fun y : M => V a y, hV a⟩ x := by
  classical
  have hdir : ∀ a : Fin N, (LeviCivita (I := I) g).toFun (V a) x (V a x) =
      ∑ c : Fin N, g.inner x (V c x) (V a x) •
        (LeviCivita (I := I) g).toFun (V a) x (V c x) := by
    intro a
    conv_lhs => rw [← hPar x (V a x)]
    rw [map_sum ((LeviCivita (I := I) g).toFun (V a) x) _ Finset.univ]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    rw [map_smul]
  have hexp : ∀ a : Fin N,
      tensorInnerPointwise (I := I) (M := M) g 0 s x
        (TensorRSSpace.toModel
          (riemannOp (tensorCov (I := I) g 0 s) x (V b x)
            ((LeviCivita (I := I) g).toFun (V a) x (V a x)) (S.toSection x)))
        (TensorRSSpace.toModel
          ((tensorCov (I := I) g 0 s).toFun (fun y : M => S.toSection y) x (V b x))) =
      ∑ c : Fin N, g.inner x (V c x) (V a x) *
        tensorInnerPointwise (I := I) (M := M) g 0 s x
          (TensorRSSpace.toModel
            (riemannOp (tensorCov (I := I) g 0 s) x (V b x)
              ((LeviCivita (I := I) g).toFun (V a) x (V c x)) (S.toSection x)))
          (TensorRSSpace.toModel
            ((tensorCov (I := I) g 0 s).toFun (fun y : M => S.toSection y) x (V b x))) := by
    intro a
    rw [hdir a,
      map_sum (riemannOp (tensorCov (I := I) g 0 s) x (V b x)) _ Finset.univ,
      ContinuousLinearMap.sum_apply]
    rw [Finset.sum_congr rfl (fun c _ => by
      rw [map_smul (riemannOp (tensorCov (I := I) g 0 s) x (V b x))
          (g.inner x (V c x) (V a x))
          ((LeviCivita (I := I) g).toFun (V a) x (V c x)),
        ContinuousLinearMap.smul_apply])]
    rw [toModel_weighted_finsetSum (I := I) (M := M) s x Finset.univ _ _,
      tensorInnerPointwise_sum_left (I := I) (M := M) g 0 s x Finset.univ _ _ _]
  rw [Finset.sum_congr rfl (fun a _ => hexp a), Finset.sum_comm]
  have hc : ∀ c : Fin N,
      (∑ a : Fin N, g.inner x (V c x) (V a x) *
        tensorInnerPointwise (I := I) (M := M) g 0 s x
          (TensorRSSpace.toModel
            (riemannOp (tensorCov (I := I) g 0 s) x (V b x)
              ((LeviCivita (I := I) g).toFun (V a) x (V c x)) (S.toSection x)))
          (TensorRSSpace.toModel
            ((tensorCov (I := I) g 0 s).toFun (fun y : M => S.toSection y) x (V b x)))) =
      - ∑ a : Fin N,
          tensorInnerPointwise (I := I) (M := M) g 0 s x
            (TensorRSSpace.toModel
              (riemannOp (tensorCov (I := I) g 0 s) x (V b x) (V a x) (S.toSection x)))
            (TensorRSSpace.toModel
              ((tensorCov (I := I) g 0 s).toFun (fun y : M => S.toSection y) x (V b x))) *
            g.inner x ((LeviCivita (I := I) g).toFun (V a) x (V c x)) (V c x) := by
    intro c
    set Bc : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ :=
      LinearMap.mk₂ ℝ
        (fun u p => tensorInnerPointwise (I := I) (M := M) g 0 s x
          (TensorRSSpace.toModel
            (riemannOp (tensorCov (I := I) g 0 s) x (V b x) u (S.toSection x)))
          (TensorRSSpace.toModel
            ((tensorCov (I := I) g 0 s).toFun (fun y : M => S.toSection y) x (V b x))) *
          g.inner x p (V c x))
        (fun u₁ u₂ p => by
          beta_reduce
          rw [map_add (riemannOp (tensorCov (I := I) g 0 s) x (V b x)) u₁ u₂,
            ContinuousLinearMap.add_apply, TensorRSSpace.toModel_add,
            tensorInnerPointwise_add_left (I := I) (M := M) g 0 s x, add_mul])
        (fun cc u p => by
          beta_reduce
          rw [map_smul (riemannOp (tensorCov (I := I) g 0 s) x (V b x)) cc u,
            ContinuousLinearMap.smul_apply, TensorRSSpace.toModel_smul,
            tensorInnerPointwise_smul_left (I := I) (M := M) g 0 s x]
          simp only [smul_eq_mul]
          ring)
        (fun u p₁ p₂ => by
          beta_reduce
          rw [map_add (g.inner x) p₁ p₂, ContinuousLinearMap.add_apply, mul_add])
        (fun cc u p => by
          beta_reduce
          rw [map_smul (g.inner x) cc p, ContinuousLinearMap.smul_apply]
          simp only [smul_eq_mul]
          ring)
      with hBc_def
    have h0 := parsevalFrame_sum_bilin_covDeriv_pair_antisymm (I := I) (M := M) g V hV hPar
      (V c) x Bc
    simp only [hBc_def, LinearMap.mk₂_apply] at h0
    rw [Finset.sum_add_distrib] at h0
    have hL : (∑ a : Fin N, g.inner x (V c x) (V a x) *
        tensorInnerPointwise (I := I) (M := M) g 0 s x
          (TensorRSSpace.toModel
            (riemannOp (tensorCov (I := I) g 0 s) x (V b x)
              ((LeviCivita (I := I) g).toFun (V a) x (V c x)) (S.toSection x)))
          (TensorRSSpace.toModel
            ((tensorCov (I := I) g 0 s).toFun (fun y : M => S.toSection y) x (V b x)))) =
        ∑ a : Fin N,
          tensorInnerPointwise (I := I) (M := M) g 0 s x
            (TensorRSSpace.toModel
              (riemannOp (tensorCov (I := I) g 0 s) x (V b x)
                ((LeviCivita (I := I) g).toFun (V a) x (V c x)) (S.toSection x)))
            (TensorRSSpace.toModel
              ((tensorCov (I := I) g 0 s).toFun (fun y : M => S.toSection y) x (V b x))) *
            g.inner x (V a x) (V c x) := by
      refine Finset.sum_congr rfl (fun a _ => ?_)
      rw [g.symm x (V c x) (V a x)]
      ring
    rw [hL]
    linarith [h0]
  rw [Finset.sum_congr rfl (fun c _ => hc c), Finset.sum_neg_distrib, Finset.sum_comm]
  have hdiv : ∀ a : Fin N,
      (∑ c : Fin N,
        tensorInnerPointwise (I := I) (M := M) g 0 s x
          (TensorRSSpace.toModel
            (riemannOp (tensorCov (I := I) g 0 s) x (V b x) (V a x) (S.toSection x)))
          (TensorRSSpace.toModel
            ((tensorCov (I := I) g 0 s).toFun (fun y : M => S.toSection y) x (V b x))) *
          g.inner x ((LeviCivita (I := I) g).toFun (V a) x (V c x)) (V c x)) =
      tensorInnerPointwise (I := I) (M := M) g 0 s x
        (TensorRSSpace.toModel
          (riemannOp (tensorCov (I := I) g 0 s) x (V b x) (V a x) (S.toSection x)))
        (TensorRSSpace.toModel
          ((tensorCov (I := I) g 0 s).toFun (fun y : M => S.toSection y) x (V b x))) *
        DifferentialGeometry.Integral.DivergenceTheorem.divergence_g (I := I) g
          ⟨fun y : M => V a y, hV a⟩ x := by
    intro a
    rw [← Finset.mul_sum]
    congr 1
    rw [divergence_g_eq_parsevalFrame_trace (I := I) (M := M) g V hPar
      (⟨fun y : M => V a y, hV a⟩ : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x]
  rw [Finset.sum_congr rfl (fun a _ => hdiv a)]
  have hswap : ∀ a : Fin N,
      tensorInnerPointwise (I := I) (M := M) g 0 s x
        (TensorRSSpace.toModel
          (riemannOp (tensorCov (I := I) g 0 s) x (V b x) (V a x) (S.toSection x)))
        (TensorRSSpace.toModel
          ((tensorCov (I := I) g 0 s).toFun (fun y : M => S.toSection y) x (V b x))) =
      - tensorInnerPointwise (I := I) (M := M) g 0 s x
        (TensorRSSpace.toModel
          (riemannOp (tensorCov (I := I) g 0 s) x (V a x) (V b x) (S.toSection x)))
        (TensorRSSpace.toModel
          ((tensorCov (I := I) g 0 s).toFun (fun y : M => S.toSection y) x (V b x))) := by
    intro a
    rw [riemannOp_swap (cov := tensorCov (I := I) g 0 s) x (V b x) (V a x) (S.toSection x),
      TensorRSSpace.toModel_neg,
      ← neg_one_smul ℝ (TensorRSSpace.toModel
        (riemannOp (tensorCov (I := I) g 0 s) x (V a x) (V b x) (S.toSection x))),
      tensorInnerPointwise_smul_left (I := I) (M := M) g 0 s x, neg_one_mul]
  rw [Finset.sum_congr rfl (fun a _ => by rw [hswap a, neg_mul])]
  rw [Finset.sum_neg_distrib, neg_neg]

set_option linter.unusedSectionVars false in
/-- **The group-`2` IBP residue plus the genuine-Hessian cross pairing is the negated
Christoffel-corrected pairing pair, pointwise per `(a, b)`.**  The iterated derivative inside the
residue and the genuine Hessian (`tensorSecondCovDeriv`) differ exactly by the correction
`∇_{∇_{V a} V b} S`, so
`residue + ⟨R(V a, V b) S, ∇²_{V a, V b} S⟩ = −(⟨R S, ∇_{∇_{V a} V b} S⟩ + ⟨R S, ∇_{V b} S⟩·divᵍ V a)`. -/
private lemma residue_add_crossHessian_pointwise_eq
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s)
    {N : ℕ} (V : Fin N → Π b : M, TangentSpace I b)
    (hV : ∀ a, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => (⟨b, V a b⟩ : TotalSpace E (TangentSpace I))))
    (a b : Fin N) (x : M) :
    bochnerGroup2Residue (I := I) (M := M) g s S (V a) (V b)
        ⟨fun y : M => V a y, hV a⟩ x +
      tensorInnerScalar (I := I) (M := M) g 0 s
        (riemannSecCc (I := I) (M := M) g s S (hV a) (hV b)).toSection
        (crossHessianCc (I := I) (M := M) g s S (hV a) (hV b)).toSection x =
      - (tensorInnerPointwise (I := I) (M := M) g 0 s x
            (TensorRSSpace.toModel
              (riemannOp (tensorCov (I := I) g 0 s) x (V a x) (V b x) (S.toSection x)))
            (TensorRSSpace.toModel
              ((tensorCov (I := I) g 0 s).toFun (fun y : M => S.toSection y) x
                ((LeviCivita (I := I) g).toFun (V b) x (V a x)))) +
          tensorInnerPointwise (I := I) (M := M) g 0 s x
            (TensorRSSpace.toModel
              (riemannOp (tensorCov (I := I) g 0 s) x (V a x) (V b x) (S.toSection x)))
            (TensorRSSpace.toModel
              ((tensorCov (I := I) g 0 s).toFun (fun y : M => S.toSection y) x (V b x))) *
            DifferentialGeometry.Integral.DivergenceTheorem.divergence_g (I := I) g
              ⟨fun y : M => V a y, hV a⟩ x) := by
  classical
  have hR : riemannSec (tensorCov (I := I) g 0 s) (V a) (V b)
      (fun z : M => S.toSection z) x =
      riemannOp (tensorCov (I := I) g 0 s) x (V a x) (V b x) (S.toSection x) :=
    riemannSec_eq_riemannOp_smooth (cov := tensorCov (I := I) g 0 s) (hV a) (hV b)
      S.toSection.contMDiff
  rw [bochnerGroup2Residue, tensorInnerScalar_apply (I := I) (M := M) g 0 s]
  rw [show (riemannSecCc (I := I) (M := M) g s S (hV a) (hV b)).toSection x =
      riemannSec (tensorCov (I := I) g 0 s) (V a) (V b) (fun z : M => S.toSection z) x
      from rfl]
  rw [show (crossHessianCc (I := I) (M := M) g s S (hV a) (hV b)).toSection x =
      (tensorCov (I := I) g 0 s).toFun
          (covApply (tensorCov (I := I) g 0 s) (V b) (fun z : M => S.toSection z)) x (V a x) -
        (tensorCov (I := I) g 0 s).toFun (fun z : M => S.toSection z) x
          ((LeviCivita (I := I) g).toFun (V b) x (V a x)) from rfl]
  rw [show covApply (tensorCov (I := I) g 0 s) (V a)
        (fun z : M => covApply (tensorCov (I := I) g 0 s) (V b)
          (fun w : M => S.toSection w) z) x =
      (tensorCov (I := I) g 0 s).toFun
        (covApply (tensorCov (I := I) g 0 s) (V b) (fun z : M => S.toSection z)) x (V a x)
      from rfl]
  rw [show covApply (tensorCov (I := I) g 0 s) (V b) (fun z : M => S.toSection z) x =
      (tensorCov (I := I) g 0 s).toFun (fun z : M => S.toSection z) x (V b x) from rfl]
  rw [hR]
  rw [TensorRSSpace.toModel_sub, sub_eq_add_neg,
    ← neg_one_smul ℝ (TensorRSSpace.toModel
      ((tensorCov (I := I) g 0 s).toFun (fun z : M => S.toSection z) x
        ((LeviCivita (I := I) g).toFun (V b) x (V a x)))),
    tensorInnerPointwise_add_right (I := I) (M := M) g 0 s x,
    tensorInnerPointwise_smul_right (I := I) (M := M) g 0 s x]
  ring

set_option linter.unusedSectionVars false in
/-- **The pointwise value of the tension-field double sum (after the full Parseval double
sum).** At every point, the `(iii + iv)` carrier double sum equals the Christoffel-corrected
pairing plus the divergence-weighted pairing — the combination the group-`2` residue and the
genuine-Hessian cross pairing jointly negate. -/
private lemma elt3IiiIv_doubleSum_pointwise_eq
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s)
    {N : ℕ} (V : Fin N → Π b : M, TangentSpace I b)
    (hV : ∀ a, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => (⟨b, V a b⟩ : TotalSpace E (TangentSpace I))))
    (hPar : ∀ (x : M) (u : TangentSpace I x),
      (∑ a : Fin N, g.inner x (V a x) u • V a x) = u) (x : M) :
    (∑ a : Fin N, ∑ b : Fin N,
        tensorInnerPointwise (I := I) (M := M) g 0 s x
          (TensorRSSpace.toModel
            (bochnerGroupElt3IiiIv (I := I) (M := M) g s S (V a) (V b) x))
          (TensorRSSpace.toModel (bochnerGradSlot0 (I := I) (M := M) g s S (V b) x))) =
      ∑ a : Fin N, ∑ b : Fin N,
        (tensorInnerPointwise (I := I) (M := M) g 0 s x
            (TensorRSSpace.toModel
              (riemannOp (tensorCov (I := I) g 0 s) x (V a x) (V b x) (S.toSection x)))
            (TensorRSSpace.toModel
              ((tensorCov (I := I) g 0 s).toFun (fun y : M => S.toSection y) x
                ((LeviCivita (I := I) g).toFun (V b) x (V a x)))) +
          tensorInnerPointwise (I := I) (M := M) g 0 s x
            (TensorRSSpace.toModel
              (riemannOp (tensorCov (I := I) g 0 s) x (V a x) (V b x) (S.toSection x)))
            (TensorRSSpace.toModel
              ((tensorCov (I := I) g 0 s).toFun (fun y : M => S.toSection y) x (V b x))) *
            DifferentialGeometry.Integral.DivergenceTheorem.divergence_g (I := I) g
              ⟨fun y : M => V a y, hV a⟩ x) := by
  classical
  have hpt : ∀ a b : Fin N,
      tensorInnerPointwise (I := I) (M := M) g 0 s x
        (TensorRSSpace.toModel
          (bochnerGroupElt3IiiIv (I := I) (M := M) g s S (V a) (V b) x))
        (TensorRSSpace.toModel (bochnerGradSlot0 (I := I) (M := M) g s S (V b) x)) =
      tensorInnerPointwise (I := I) (M := M) g 0 s x
          (TensorRSSpace.toModel
            (riemannOp (tensorCov (I := I) g 0 s) x
              ((LeviCivita (I := I) g).toFun (V b) x (V a x)) (V a x) (S.toSection x)))
          (TensorRSSpace.toModel
            ((tensorCov (I := I) g 0 s).toFun (fun y : M => S.toSection y) x (V b x))) +
        tensorInnerPointwise (I := I) (M := M) g 0 s x
          (TensorRSSpace.toModel
            (riemannOp (tensorCov (I := I) g 0 s) x (V b x)
              ((LeviCivita (I := I) g).toFun (V a) x (V a x)) (S.toSection x)))
          (TensorRSSpace.toModel
            ((tensorCov (I := I) g 0 s).toFun (fun y : M => S.toSection y) x (V b x))) := by
    intro a b
    rw [show bochnerGroupElt3IiiIv (I := I) (M := M) g s S (V a) (V b) x =
        riemannOp (tensorCov (I := I) g 0 s) x
            ((LeviCivita (I := I) g).toFun (V b) x (V a x)) (V a x) (S.toSection x) +
          riemannOp (tensorCov (I := I) g 0 s) x (V b x)
            ((LeviCivita (I := I) g).toFun (V a) x (V a x)) (S.toSection x) from by
      rw [bochnerGroupElt3IiiIv, tensor0SAsRS_add,
        tensor0SAsRS_rs_unit' (I := I) (M := M) s x _,
        tensor0SAsRS_rs_unit' (I := I) (M := M) s x _]]
    rw [show bochnerGradSlot0 (I := I) (M := M) g s S (V b) x =
        (tensorCov (I := I) g 0 s).toFun (fun y : M => S.toSection y) x (V b x) from by
      rw [bochnerGradSlot0_eq_covApply (I := I) (M := M) g s S (V b) x]; rfl]
    rw [TensorRSSpace.toModel_add, tensorInnerPointwise_add_left (I := I) (M := M) g 0 s x]
  rw [Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => hpt a b))]
  rw [Finset.sum_congr rfl (fun a _ => Finset.sum_add_distrib), Finset.sum_add_distrib]
  rw [Finset.sum_congr rfl (fun a _ =>
    parsevalFrame_termIii_sum_eq (I := I) (M := M) g s S V hV hPar a x)]
  have hiv : (∑ a : Fin N, ∑ b : Fin N,
      tensorInnerPointwise (I := I) (M := M) g 0 s x
        (TensorRSSpace.toModel
          (riemannOp (tensorCov (I := I) g 0 s) x (V b x)
            ((LeviCivita (I := I) g).toFun (V a) x (V a x)) (S.toSection x)))
        (TensorRSSpace.toModel
          ((tensorCov (I := I) g 0 s).toFun (fun y : M => S.toSection y) x (V b x)))) =
      ∑ a : Fin N, ∑ b : Fin N,
        tensorInnerPointwise (I := I) (M := M) g 0 s x
          (TensorRSSpace.toModel
            (riemannOp (tensorCov (I := I) g 0 s) x (V a x) (V b x) (S.toSection x)))
          (TensorRSSpace.toModel
            ((tensorCov (I := I) g 0 s).toFun (fun y : M => S.toSection y) x (V b x))) *
          DifferentialGeometry.Integral.DivergenceTheorem.divergence_g (I := I) g
            ⟨fun y : M => V a y, hV a⟩ x := by
    rw [Finset.sum_comm]
    exact (Finset.sum_congr rfl (fun b _ =>
      parsevalFrame_termIv_sum_eq (I := I) (M := M) g s S V hV hPar b x)).trans
      Finset.sum_comm
  rw [hiv, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [← Finset.sum_add_distrib]

set_option linter.unusedSectionVars false in
/-- **The integrated differentiated-curvature covariant integration by parts (the proven `∇R`-vs-`∇S`
primitive of the rank-`0` Bochner kernel, `D = −(G₁ + I₂)`).**  For a fixed smooth Parseval
frame family, the diagonal differentiated-curvature trace double sum
`D := ∑_a ∑_b ∫ ⟨nablaDiffCurvTraceCc, ∇_{V b} S⟩` (the frame-free global-section pairing of the
differentiated curvature `(∇_{V a} R^{(s)})(V a, V b) S` against the slot-`0` gradient `∇_{V b} S`)
equals the negated sum of the group-`1` curvature pairing double sum and the
curvature/Hessian cross pairing double sum
`I₂ := ∑_a ∑_b ∫ ⟨R(V a, V b) S, ∇²_{V a, V b} S⟩`, built on the **genuine Hessian** carrier
`crossHessianCc` (`tensorSecondCovDeriv`, tensorial in both direction slots).  The former
iterated-derivative form (`secondCovApplyCc`, `∇_{V a}(∇_{V b} S)`) was numerically REFUTED:
its `I₂` is frame-variant by the missing `∇_{∇_{V a} V b} S` correction (defect
`∑∑∫ ⟨R(V a, V b) S, ∇_{∇_{V a} V b} S⟩ ≠ 0`), while the Hessian-based identity holds to
`≤ 4e-15` in dims `2` and `3`:
```
D = −(bochnerFoldGroupSum (bochnerGroupElt1) + I₂).
```
This is the honest formal shape of the covariant integration by parts moving the derivative off
`∇R`: `∫ ⟨(∇_X R)(·) S, ∇S⟩ = −∫ ⟨R(·)(∇_X S), ∇S⟩ − ∫ ⟨R(·) S, ∇_X(∇S)⟩ − (frame/divergence
corrections)`, the frame and divergence corrections cancelling only after the full Parseval `(a, b)`
double sum.

**Variance admissibility (why this, and not any per-group value).**  The per-`b` and `b`-summed
tension-field nullities and every individual per-group value assignment (`D = group2 − group1`,
`G₃ = ⟨ricTraceSection, ∇S⟩`, `G₂ + G₄ = operator residue`) are FALSE in dim ≥ 3
(`PROVE_REFUTED.md`, "Kernel per-group VALUE-ASSIGNMENT family": the `S³` rotation-family and
ellipsoid certificates, 2026-06-12).  This identity is the surviving difference-of-engine form:
over the sorry-free covariant-Leibniz split `bochnerFoldGroupSum_elt3IiiIv_eq_nablaDiffCurvTrace_split`
and the sorry-free frame-summed engine `bochnerFoldGroupSum_elt2_eq_residueSum` it is equivalent to
`bochnerFoldGroupSum (bochnerGroupElt3IiiIv) = ∑_a ∑_b ∫ ⟨R(V a, V b) S, ∇_{V b} S⟩ · divᵍ(V a)`,
both sides gauge-variant with matching variance under family-gauge rotations.  **Numerically
confirmed twice** in dim `3` (recorded with the 2026-06-12 adjudication; the dim-`2` fibre algebra
degenerates, so probes for this family must run in dim ≥ 3).  It genuinely uses `R`, `∇R`, the
Parseval reproduction `hPar`, and the frame's `∇V` structure.

**Proof.**  Through the covariant-Leibniz split
`bochnerFoldGroupSum_elt3IiiIv_eq_nablaDiffCurvTrace_split` (`D = T + G₂ − G₁`, with
`T := bochnerFoldGroupSum (bochnerGroupElt3IiiIv)`) and the frame-summed engine
`bochnerFoldGroupSum_elt2_eq_residueSum`, the identity is equivalent to the vanishing
`T + G₂ + I₂ = 0`.  That vanishing is *pointwise after the full `(a, b)` double sum*: the genuine
Hessian and the residue's iterated derivative differ exactly by the Christoffel correction
`∇_{∇_{V a} V b} S` (`residue_add_crossHessian_pointwise_eq`), and the tension-field double sum
evaluates to exactly the negated correction-plus-divergence combination
(`elt3IiiIv_doubleSum_pointwise_eq`): term (iii) telescopes its curvature-slot frame derivative onto
the gradient slot by the bilinear-contracted cometric-parallel antisymmetry
(`parsevalFrame_sum_bilin_covDeriv_pair_antisymm`, from
`parsevalFrame_sum_covDeriv_inner_antisymm`) plus the `riemannOp` slot antisymmetry
(`parsevalFrame_termIii_sum_eq`), and term (iv)'s diagonal frame tension collapses to the intrinsic
divergence weight through the Parseval covariant trace `divergence_g_eq_parsevalFrame_trace`
(`parsevalFrame_termIv_sum_eq`).  Integrating the pointwise vanishing over the closed manifold
(`integral_finset_sum`, the per-`(a, b)` cross-pairing integrabilities) yields the identity.
Sorry-free. -/
private theorem parsevalFrameSum_diffCurvTrace_doubleSum_eq_neg_group1_add_crossPairing
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s)
    {N : ℕ} (V : Fin N → Π b : M, TangentSpace I b)
    (hV : ∀ a, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => (⟨b, V a b⟩ : TotalSpace E (TangentSpace I))))
    (hPar : ∀ (x : M) (u : TangentSpace I x),
      (∑ a : Fin N, g.inner x (V a x) u • V a x) = u) :
    (∑ a : Fin N, ∑ b : Fin N,
        ∫ x, tensorInnerScalar (I := I) (M := M) g 0 s
            (nablaDiffCurvTraceCc (I := I) (M := M) g s S (hV a) (hV b)).toSection
            (bochnerGradSlot0Cc (I := I) (M := M) g s S (hV b)).toSection x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g)) =
      - (bochnerFoldGroupSum (I := I) (M := M) g s S V
            (bochnerGroupElt1 (I := I) (M := M) g s S) +
          ∑ a : Fin N, ∑ b : Fin N,
            ∫ x, tensorInnerScalar (I := I) (M := M) g 0 s
                (riemannSecCc (I := I) (M := M) g s S (hV a) (hV b)).toSection
                (crossHessianCc (I := I) (M := M) g s S (hV a) (hV b)).toSection x
              ∂(riemannianVolumeMeasure (I := I) (M := M) g)) := by
  classical
  have hsplit := bochnerFoldGroupSum_elt3IiiIv_eq_nablaDiffCurvTrace_split
    (I := I) (M := M) g s S V hV
  have hres := bochnerFoldGroupSum_elt2_eq_residueSum (I := I) (M := M) g s S V hV
  have hint3 : ∀ a b : Fin N, Integrable
      (fun x : M => tensorInnerPointwise (I := I) (M := M) g 0 s x
        (TensorRSSpace.toModel (bochnerGroupElt3IiiIv (I := I) (M := M) g s S (V a) (V b) x))
        (TensorRSSpace.toModel (bochnerGradSlot0 (I := I) (M := M) g s S (V b) x)))
      (riemannianVolumeMeasure (I := I) (M := M) g) := by
    intro a b
    refine (SmoothCcTensor.integrable_inner_cross (I := I) (M := M)
      (bochnerGroupElt3IiiIvCc (I := I) (M := M) g s S (hV a) (hV b))
      (bochnerGradSlot0Cc (I := I) (M := M) g s S (hV b))).congr
      (Filter.Eventually.of_forall (fun x => ?_))
    simp only [SmoothCcTensor.toFun_apply,
      bochnerGroupElt3IiiIvCc_toSection_eq (I := I) (M := M) g s S (hV a) (hV b) x,
      bochnerGradSlot0Cc_toSection_apply (I := I) (M := M) g s S (hV b) x]
  have hintH : ∀ a b : Fin N, Integrable
      (fun x : M => tensorInnerScalar (I := I) (M := M) g 0 s
        (riemannSecCc (I := I) (M := M) g s S (hV a) (hV b)).toSection
        (crossHessianCc (I := I) (M := M) g s S (hV a) (hV b)).toSection x)
      (riemannianVolumeMeasure (I := I) (M := M) g) := fun a b =>
    SmoothCcTensor.integrable_inner_cross (I := I) (M := M)
      (riemannSecCc (I := I) (M := M) g s S (hV a) (hV b))
      (crossHessianCc (I := I) (M := M) g s S (hV a) (hV b))
  have hintR : ∀ a b : Fin N, Integrable
      (fun x : M => bochnerGroup2Residue (I := I) (M := M) g s S (V a) (V b)
        ⟨fun y : M => V a y, hV a⟩ x)
      (riemannianVolumeMeasure (I := I) (M := M) g) := fun a b =>
    integrable_bochnerGroup2Residue (I := I) (M := M) g s S V hV a b
  have hzero : ∀ x : M,
      (∑ a : Fin N, ∑ b : Fin N,
          tensorInnerPointwise (I := I) (M := M) g 0 s x
            (TensorRSSpace.toModel
              (bochnerGroupElt3IiiIv (I := I) (M := M) g s S (V a) (V b) x))
            (TensorRSSpace.toModel (bochnerGradSlot0 (I := I) (M := M) g s S (V b) x))) +
        ((∑ a : Fin N, ∑ b : Fin N,
            bochnerGroup2Residue (I := I) (M := M) g s S (V a) (V b)
              ⟨fun y : M => V a y, hV a⟩ x) +
          (∑ a : Fin N, ∑ b : Fin N,
            tensorInnerScalar (I := I) (M := M) g 0 s
              (riemannSecCc (I := I) (M := M) g s S (hV a) (hV b)).toSection
              (crossHessianCc (I := I) (M := M) g s S (hV a) (hV b)).toSection x)) = 0 := by
    intro x
    have h1 := elt3IiiIv_doubleSum_pointwise_eq (I := I) (M := M) g s S V hV hPar x
    have hab : ∀ a : Fin N,
        ((∑ b : Fin N,
            bochnerGroup2Residue (I := I) (M := M) g s S (V a) (V b)
              ⟨fun y : M => V a y, hV a⟩ x) +
          ∑ b : Fin N,
            tensorInnerScalar (I := I) (M := M) g 0 s
              (riemannSecCc (I := I) (M := M) g s S (hV a) (hV b)).toSection
              (crossHessianCc (I := I) (M := M) g s S (hV a) (hV b)).toSection x) =
        - ∑ b : Fin N,
          (tensorInnerPointwise (I := I) (M := M) g 0 s x
              (TensorRSSpace.toModel
                (riemannOp (tensorCov (I := I) g 0 s) x (V a x) (V b x) (S.toSection x)))
              (TensorRSSpace.toModel
                ((tensorCov (I := I) g 0 s).toFun (fun y : M => S.toSection y) x
                  ((LeviCivita (I := I) g).toFun (V b) x (V a x)))) +
            tensorInnerPointwise (I := I) (M := M) g 0 s x
              (TensorRSSpace.toModel
                (riemannOp (tensorCov (I := I) g 0 s) x (V a x) (V b x) (S.toSection x)))
              (TensorRSSpace.toModel
                ((tensorCov (I := I) g 0 s).toFun (fun y : M => S.toSection y) x (V b x))) *
              DifferentialGeometry.Integral.DivergenceTheorem.divergence_g (I := I) g
                ⟨fun y : M => V a y, hV a⟩ x) := by
      intro a
      rw [← Finset.sum_add_distrib,
        Finset.sum_congr rfl (fun b _ =>
          residue_add_crossHessian_pointwise_eq (I := I) (M := M) g s S V hV a b x)]
      exact Finset.sum_neg_distrib _
    have h2 : ((∑ a : Fin N, ∑ b : Fin N,
          bochnerGroup2Residue (I := I) (M := M) g s S (V a) (V b)
            ⟨fun y : M => V a y, hV a⟩ x) +
        (∑ a : Fin N, ∑ b : Fin N,
          tensorInnerScalar (I := I) (M := M) g 0 s
            (riemannSecCc (I := I) (M := M) g s S (hV a) (hV b)).toSection
            (crossHessianCc (I := I) (M := M) g s S (hV a) (hV b)).toSection x)) =
        - ∑ a : Fin N, ∑ b : Fin N,
          (tensorInnerPointwise (I := I) (M := M) g 0 s x
              (TensorRSSpace.toModel
                (riemannOp (tensorCov (I := I) g 0 s) x (V a x) (V b x) (S.toSection x)))
              (TensorRSSpace.toModel
                ((tensorCov (I := I) g 0 s).toFun (fun y : M => S.toSection y) x
                  ((LeviCivita (I := I) g).toFun (V b) x (V a x)))) +
            tensorInnerPointwise (I := I) (M := M) g 0 s x
              (TensorRSSpace.toModel
                (riemannOp (tensorCov (I := I) g 0 s) x (V a x) (V b x) (S.toSection x)))
              (TensorRSSpace.toModel
                ((tensorCov (I := I) g 0 s).toFun (fun y : M => S.toSection y) x (V b x))) *
              DifferentialGeometry.Integral.DivergenceTheorem.divergence_g (I := I) g
                ⟨fun y : M => V a y, hV a⟩ x) := by
      rw [← Finset.sum_add_distrib, Finset.sum_congr rfl (fun a _ => hab a)]
      exact Finset.sum_neg_distrib _
    linarith [h1, h2]
  have hI1 : (∑ a : Fin N, ∑ b : Fin N,
      ∫ x, tensorInnerPointwise (I := I) (M := M) g 0 s x
          (TensorRSSpace.toModel
            (bochnerGroupElt3IiiIv (I := I) (M := M) g s S (V a) (V b) x))
          (TensorRSSpace.toModel (bochnerGradSlot0 (I := I) (M := M) g s S (V b) x))
        ∂(riemannianVolumeMeasure (I := I) (M := M) g)) =
      ∫ x, (∑ a : Fin N, ∑ b : Fin N,
          tensorInnerPointwise (I := I) (M := M) g 0 s x
            (TensorRSSpace.toModel
              (bochnerGroupElt3IiiIv (I := I) (M := M) g s S (V a) (V b) x))
            (TensorRSSpace.toModel (bochnerGradSlot0 (I := I) (M := M) g s S (V b) x)))
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
    rw [Finset.sum_congr rfl (fun a _ =>
      (MeasureTheory.integral_finset_sum Finset.univ (fun b _ => hint3 a b)).symm)]
    exact (MeasureTheory.integral_finset_sum Finset.univ (fun a _ =>
      MeasureTheory.integrable_finset_sum Finset.univ (fun b _ => hint3 a b))).symm
  have hI2 : (∑ a : Fin N, ∑ b : Fin N,
      ∫ x, tensorInnerScalar (I := I) (M := M) g 0 s
          (riemannSecCc (I := I) (M := M) g s S (hV a) (hV b)).toSection
          (crossHessianCc (I := I) (M := M) g s S (hV a) (hV b)).toSection x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g)) =
      ∫ x, (∑ a : Fin N, ∑ b : Fin N,
          tensorInnerScalar (I := I) (M := M) g 0 s
            (riemannSecCc (I := I) (M := M) g s S (hV a) (hV b)).toSection
            (crossHessianCc (I := I) (M := M) g s S (hV a) (hV b)).toSection x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
    rw [Finset.sum_congr rfl (fun a _ =>
      (MeasureTheory.integral_finset_sum Finset.univ (fun b _ => hintH a b)).symm)]
    exact (MeasureTheory.integral_finset_sum Finset.univ (fun a _ =>
      MeasureTheory.integrable_finset_sum Finset.univ (fun b _ => hintH a b))).symm
  have hI3 : (∑ a : Fin N, ∑ b : Fin N,
      ∫ x, bochnerGroup2Residue (I := I) (M := M) g s S (V a) (V b)
          ⟨fun y : M => V a y, hV a⟩ x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g)) =
      ∫ x, (∑ a : Fin N, ∑ b : Fin N,
          bochnerGroup2Residue (I := I) (M := M) g s S (V a) (V b)
            ⟨fun y : M => V a y, hV a⟩ x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
    rw [Finset.sum_congr rfl (fun a _ =>
      (MeasureTheory.integral_finset_sum Finset.univ (fun b _ => hintR a b)).symm)]
    exact (MeasureTheory.integral_finset_sum Finset.univ (fun a _ =>
      MeasureTheory.integrable_finset_sum Finset.univ (fun b _ => hintR a b))).symm
  have hone : (∑ a : Fin N, ∑ b : Fin N,
      ∫ x, tensorInnerPointwise (I := I) (M := M) g 0 s x
          (TensorRSSpace.toModel
            (bochnerGroupElt3IiiIv (I := I) (M := M) g s S (V a) (V b) x))
          (TensorRSSpace.toModel (bochnerGradSlot0 (I := I) (M := M) g s S (V b) x))
        ∂(riemannianVolumeMeasure (I := I) (M := M) g)) +
      ((∑ a : Fin N, ∑ b : Fin N,
        ∫ x, bochnerGroup2Residue (I := I) (M := M) g s S (V a) (V b)
            ⟨fun y : M => V a y, hV a⟩ x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g)) +
        (∑ a : Fin N, ∑ b : Fin N,
          ∫ x, tensorInnerScalar (I := I) (M := M) g 0 s
              (riemannSecCc (I := I) (M := M) g s S (hV a) (hV b)).toSection
              (crossHessianCc (I := I) (M := M) g s S (hV a) (hV b)).toSection x
            ∂(riemannianVolumeMeasure (I := I) (M := M) g))) = 0 := by
    have hPsum : Integrable
        (fun x : M => ∑ a : Fin N, ∑ b : Fin N,
          tensorInnerPointwise (I := I) (M := M) g 0 s x
            (TensorRSSpace.toModel
              (bochnerGroupElt3IiiIv (I := I) (M := M) g s S (V a) (V b) x))
            (TensorRSSpace.toModel (bochnerGradSlot0 (I := I) (M := M) g s S (V b) x)))
        (riemannianVolumeMeasure (I := I) (M := M) g) :=
      MeasureTheory.integrable_finset_sum Finset.univ (fun a _ =>
        MeasureTheory.integrable_finset_sum Finset.univ (fun b _ => hint3 a b))
    have hQsum : Integrable
        (fun x : M => ∑ a : Fin N, ∑ b : Fin N,
          tensorInnerScalar (I := I) (M := M) g 0 s
            (riemannSecCc (I := I) (M := M) g s S (hV a) (hV b)).toSection
            (crossHessianCc (I := I) (M := M) g s S (hV a) (hV b)).toSection x)
        (riemannianVolumeMeasure (I := I) (M := M) g) :=
      MeasureTheory.integrable_finset_sum Finset.univ (fun a _ =>
        MeasureTheory.integrable_finset_sum Finset.univ (fun b _ => hintH a b))
    have hRsum : Integrable
        (fun x : M => ∑ a : Fin N, ∑ b : Fin N,
          bochnerGroup2Residue (I := I) (M := M) g s S (V a) (V b)
            ⟨fun y : M => V a y, hV a⟩ x)
        (riemannianVolumeMeasure (I := I) (M := M) g) :=
      MeasureTheory.integrable_finset_sum Finset.univ (fun a _ =>
        MeasureTheory.integrable_finset_sum Finset.univ (fun b _ => hintR a b))
    have h12 : (∫ x, ((∑ a : Fin N, ∑ b : Fin N,
          bochnerGroup2Residue (I := I) (M := M) g s S (V a) (V b)
            ⟨fun y : M => V a y, hV a⟩ x) +
          (∑ a : Fin N, ∑ b : Fin N,
            tensorInnerScalar (I := I) (M := M) g 0 s
              (riemannSecCc (I := I) (M := M) g s S (hV a) (hV b)).toSection
              (crossHessianCc (I := I) (M := M) g s S (hV a) (hV b)).toSection x))
        ∂(riemannianVolumeMeasure (I := I) (M := M) g)) =
        (∫ x, (∑ a : Fin N, ∑ b : Fin N,
            bochnerGroup2Residue (I := I) (M := M) g s S (V a) (V b)
              ⟨fun y : M => V a y, hV a⟩ x)
          ∂(riemannianVolumeMeasure (I := I) (M := M) g)) +
        ∫ x, (∑ a : Fin N, ∑ b : Fin N,
            tensorInnerScalar (I := I) (M := M) g 0 s
              (riemannSecCc (I := I) (M := M) g s S (hV a) (hV b)).toSection
              (crossHessianCc (I := I) (M := M) g s S (hV a) (hV b)).toSection x)
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) :=
      MeasureTheory.integral_add hRsum hQsum
    have h123 : (∫ x, ((∑ a : Fin N, ∑ b : Fin N,
          tensorInnerPointwise (I := I) (M := M) g 0 s x
            (TensorRSSpace.toModel
              (bochnerGroupElt3IiiIv (I := I) (M := M) g s S (V a) (V b) x))
            (TensorRSSpace.toModel (bochnerGradSlot0 (I := I) (M := M) g s S (V b) x))) +
          ((∑ a : Fin N, ∑ b : Fin N,
            bochnerGroup2Residue (I := I) (M := M) g s S (V a) (V b)
              ⟨fun y : M => V a y, hV a⟩ x) +
          (∑ a : Fin N, ∑ b : Fin N,
            tensorInnerScalar (I := I) (M := M) g 0 s
              (riemannSecCc (I := I) (M := M) g s S (hV a) (hV b)).toSection
              (crossHessianCc (I := I) (M := M) g s S (hV a) (hV b)).toSection x)))
        ∂(riemannianVolumeMeasure (I := I) (M := M) g)) =
        (∫ x, (∑ a : Fin N, ∑ b : Fin N,
            tensorInnerPointwise (I := I) (M := M) g 0 s x
              (TensorRSSpace.toModel
                (bochnerGroupElt3IiiIv (I := I) (M := M) g s S (V a) (V b) x))
              (TensorRSSpace.toModel (bochnerGradSlot0 (I := I) (M := M) g s S (V b) x)))
          ∂(riemannianVolumeMeasure (I := I) (M := M) g)) +
        ∫ x, ((∑ a : Fin N, ∑ b : Fin N,
            bochnerGroup2Residue (I := I) (M := M) g s S (V a) (V b)
              ⟨fun y : M => V a y, hV a⟩ x) +
          (∑ a : Fin N, ∑ b : Fin N,
            tensorInnerScalar (I := I) (M := M) g 0 s
              (riemannSecCc (I := I) (M := M) g s S (hV a) (hV b)).toSection
              (crossHessianCc (I := I) (M := M) g s S (hV a) (hV b)).toSection x))
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) :=
      MeasureTheory.integral_add hPsum (hRsum.add hQsum)
    have hzint : (∫ x, ((∑ a : Fin N, ∑ b : Fin N,
          tensorInnerPointwise (I := I) (M := M) g 0 s x
            (TensorRSSpace.toModel
              (bochnerGroupElt3IiiIv (I := I) (M := M) g s S (V a) (V b) x))
            (TensorRSSpace.toModel (bochnerGradSlot0 (I := I) (M := M) g s S (V b) x))) +
          ((∑ a : Fin N, ∑ b : Fin N,
            bochnerGroup2Residue (I := I) (M := M) g s S (V a) (V b)
              ⟨fun y : M => V a y, hV a⟩ x) +
          (∑ a : Fin N, ∑ b : Fin N,
            tensorInnerScalar (I := I) (M := M) g 0 s
              (riemannSecCc (I := I) (M := M) g s S (hV a) (hV b)).toSection
              (crossHessianCc (I := I) (M := M) g s S (hV a) (hV b)).toSection x)))
        ∂(riemannianVolumeMeasure (I := I) (M := M) g)) = 0 := by
      rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hzero)]
      exact MeasureTheory.integral_zero _ _
    rw [hI1, hI2, hI3]
    linarith [h12, h123, hzint]
  have hfold3 : bochnerFoldGroupSum (I := I) (M := M) g s S V
      (bochnerGroupElt3IiiIv (I := I) (M := M) g s S) =
      ∑ a : Fin N, ∑ b : Fin N,
        ∫ x, tensorInnerPointwise (I := I) (M := M) g 0 s x
            (TensorRSSpace.toModel
              (bochnerGroupElt3IiiIv (I := I) (M := M) g s S (V a) (V b) x))
            (TensorRSSpace.toModel (bochnerGradSlot0 (I := I) (M := M) g s S (V b) x))
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
    rw [bochnerFoldGroupSum]
  have hcomm : (∑ b : Fin N, ∑ a : Fin N,
      ∫ x, bochnerGroup2Residue (I := I) (M := M) g s S (V a) (V b)
          ⟨fun y : M => V a y, hV a⟩ x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g)) =
      ∑ a : Fin N, ∑ b : Fin N,
        ∫ x, bochnerGroup2Residue (I := I) (M := M) g s S (V a) (V b)
            ⟨fun y : M => V a y, hV a⟩ x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) := Finset.sum_comm
  linarith [hsplit, hres, hone, hfold3, hcomm]

set_option linter.unusedSectionVars false in
/-- **The group-`3` fold splits into the tension-field double sum plus the Ricci-trace pairing (the
variance-honest group-`3` decomposition).**  For a fixed Parseval frame family, the group-`3` double
sum equals the tension-field carrier double sum `bochnerFoldGroupSum (bochnerGroupElt3IiiIv)` plus
the `L²` pairing of the leading-slot Ricci-trace carrier against `∇S`:
```
bochnerFoldGroupSum g s S V (bochnerGroupElt3)
  = bochnerFoldGroupSum g s S V (bochnerGroupElt3IiiIv) + ⟨ricTraceSection g s S, ∇S⟩_{L²}.
```
The group-`3` carrier `bochnerGroupElt3 = (iii + iv) − v` splits pointwise into the tension-field
part `bochnerGroupElt3IiiIv` and the Ricci-direction part `bochnerGroupElt3NegV`
(`bochnerGroupElt3_eq_iiiIv_add_negV`); the `−v` double sum collapses to the Ricci-trace pairing via
the pointwise fold assembly (`fold_assembly`, `parsevalFrameSum_ricSlot0_eq_sum_negV`).  The
gauge-variant tension-field double sum stays **explicit** on the right — the former fold equating it
to `0` (and hence `G₃` to the bare Ricci trace) is FALSE in dim ≥ 3 (`PROVE_REFUTED.md`, "Kernel
per-group VALUE-ASSIGNMENT family").  Sorry-free. -/
private theorem bochnerFoldGroupSum_elt3_eq_iiiIvSum_add_ricTrace
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s)
    {N : ℕ} (V : Fin N → Π b : M, TangentSpace I b)
    (hV : ∀ a, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => (⟨b, V a b⟩ : TotalSpace E (TangentSpace I))))
    (hPar : ∀ (x : M) (u : TangentSpace I x),
      (∑ a : Fin N, g.inner x (V a x) u • V a x) = u) :
    bochnerFoldGroupSum (I := I) (M := M) g s S V
        (bochnerGroupElt3 (I := I) (M := M) g s S) =
      bochnerFoldGroupSum (I := I) (M := M) g s S V
          (bochnerGroupElt3IiiIv (I := I) (M := M) g s S) +
        tensorL2Inner (I := I) (M := M) g 0 (s + 1)
          (ricTraceSection (I := I) (M := M) g s S).toFun
          (covGrad (I := I) (M := M) g 0 s S).toFun := by
  classical
  have hintIiiIv : ∀ a b : Fin N, Integrable
      (fun x : M => tensorInnerPointwise (I := I) (M := M) g 0 s x
        (TensorRSSpace.toModel (bochnerGroupElt3IiiIv (I := I) (M := M) g s S (V a) (V b) x))
        (TensorRSSpace.toModel (bochnerGradSlot0 (I := I) (M := M) g s S (V b) x)))
      (riemannianVolumeMeasure (I := I) (M := M) g) := by
    intro a b
    refine (SmoothCcTensor.integrable_inner_cross (I := I) (M := M)
      (bochnerGroupElt3IiiIvCc (I := I) (M := M) g s S (hV a) (hV b))
      (bochnerGradSlot0Cc (I := I) (M := M) g s S (hV b))).congr
      (Filter.Eventually.of_forall (fun x => ?_))
    simp only [SmoothCcTensor.toFun_apply,
      bochnerGroupElt3IiiIvCc_toSection_eq (I := I) (M := M) g s S (hV a) (hV b) x,
      bochnerGradSlot0Cc_toSection_apply (I := I) (M := M) g s S (hV b) x]
  have hintNegV : ∀ a b : Fin N, Integrable
      (fun x : M => tensorInnerPointwise (I := I) (M := M) g 0 s x
        (TensorRSSpace.toModel (bochnerGroupElt3NegV (I := I) (M := M) g s S (V a) (V b) x))
        (TensorRSSpace.toModel (bochnerGradSlot0 (I := I) (M := M) g s S (V b) x)))
      (riemannianVolumeMeasure (I := I) (M := M) g) := by
    intro a b
    refine (SmoothCcTensor.integrable_inner_cross (I := I) (M := M)
      (bochnerGroupElt3NegVCc (I := I) (M := M) g s S (hV a) (hV b))
      (bochnerGradSlot0Cc (I := I) (M := M) g s S (hV b))).congr
      (Filter.Eventually.of_forall (fun x => ?_))
    simp only [SmoothCcTensor.toFun_apply,
      bochnerGroupElt3NegVCc_toSection_eq (I := I) (M := M) g s S (hV a) (hV b) x,
      bochnerGradSlot0Cc_toSection_apply (I := I) (M := M) g s S (hV b) x]
  have hintegral : ∀ a b : Fin N,
      (∫ x, tensorInnerPointwise (I := I) (M := M) g 0 s x
            (TensorRSSpace.toModel (bochnerGroupElt3 (I := I) (M := M) g s S (V a) (V b) x))
            (TensorRSSpace.toModel (bochnerGradSlot0 (I := I) (M := M) g s S (V b) x))
          ∂(riemannianVolumeMeasure (I := I) (M := M) g)) =
        (∫ x, tensorInnerPointwise (I := I) (M := M) g 0 s x
              (TensorRSSpace.toModel
                (bochnerGroupElt3IiiIv (I := I) (M := M) g s S (V a) (V b) x))
              (TensorRSSpace.toModel (bochnerGradSlot0 (I := I) (M := M) g s S (V b) x))
            ∂(riemannianVolumeMeasure (I := I) (M := M) g)) +
        (∫ x, tensorInnerPointwise (I := I) (M := M) g 0 s x
              (TensorRSSpace.toModel
                (bochnerGroupElt3NegV (I := I) (M := M) g s S (V a) (V b) x))
              (TensorRSSpace.toModel (bochnerGradSlot0 (I := I) (M := M) g s S (V b) x))
            ∂(riemannianVolumeMeasure (I := I) (M := M) g)) := by
    intro a b
    rw [← MeasureTheory.integral_add (hintIiiIv a b) (hintNegV a b)]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    simp only []
    rw [bochnerGroupElt3_eq_iiiIv_add_negV (I := I) (M := M) g s S (V a) (V b) x,
      TensorRSSpace.toModel_add, tensorInnerPointwise_add_left (I := I) (M := M) g 0 s x]
  have hsplit : bochnerFoldGroupSum (I := I) (M := M) g s S V
        (bochnerGroupElt3 (I := I) (M := M) g s S) =
      bochnerFoldGroupSum (I := I) (M := M) g s S V
          (bochnerGroupElt3IiiIv (I := I) (M := M) g s S) +
        bochnerFoldGroupSum (I := I) (M := M) g s S V
          (bochnerGroupElt3NegV (I := I) (M := M) g s S) := by
    rw [bochnerFoldGroupSum, bochnerFoldGroupSum, bochnerFoldGroupSum,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    exact hintegral a b
  rw [hsplit,
    fold_assembly (I := I) (M := M) g s S V hV hPar
      (ricTraceSection (I := I) (M := M) g s S)
      (bochnerGroupElt3NegV (I := I) (M := M) g s S)
      (fun b x => parsevalFrameSum_ricSlot0_eq_sum_negV (I := I) (M := M) g s S V hPar b x)
      (fun a b => hintNegV a b)]

/-- **Fold 5 (the fixed-Parseval-family bridge).** For a fixed Parseval frame family, the sum of the four
group double-sums equals the curvature cross-pairing
```
∑_{k=1}^{4} bochnerFoldGroupSum_k = ⟨pointwiseTensorCurv g s S, ∇S⟩_{L²}.
```
The genuine content is the fixed-family Parseval reduction: the rough Laplacian as the fixed-family trace of
second covariant derivatives (`rawTensorConnLapSmooth_toSection_eq_parseval_secondCovDeriv_sum`), the slot-`0`
fibre Parseval expansion of the `(0, s + 1)` pairing (`tensorInnerPointwise_succ_eq_parseval_sum_slot0`), and
the seven-term carrier identity (`secondCovDeriv_covGrad_sub_covGrad_secondCovDeriv_slot0_eq`,
`FixedFieldThirdOrderCommutator`) splitting the per-`(a, b)` integrand into the four carrier groups.  The
body is fully proven (sorry-free). -/
theorem bochnerFold_sevenTermSum_eq_pointwiseTensorCurvPairing
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s)
    {N : ℕ} (V : Fin N → Π b : M, TangentSpace I b)
    (hV : ∀ a, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => (⟨b, V a b⟩ : TotalSpace E (TangentSpace I))))
    (hPar : ∀ (x : M) (u : TangentSpace I x),
      (∑ a : Fin N, g.inner x (V a x) u • V a x) = u) :
    tensorL2Inner (I := I) (M := M) g 0 (s + 1)
        (pointwiseTensorCurv (I := I) (M := M) g s S).toFun
        (covGrad (I := I) (M := M) g 0 s S).toFun =
      bochnerFoldGroupSum (I := I) (M := M) g s S V
          (bochnerGroupElt1 (I := I) (M := M) g s S) +
        bochnerFoldGroupSum (I := I) (M := M) g s S V
          (bochnerGroupElt2 (I := I) (M := M) g s S) +
        bochnerFoldGroupSum (I := I) (M := M) g s S V
          (bochnerGroupElt3 (I := I) (M := M) g s S) +
        bochnerFoldGroupSum (I := I) (M := M) g s S V
          (bochnerGroupElt4 (I := I) (M := M) g s S) := by
  classical
  -- Per-carrier integrability of every group pairing against the slot-`0` read of `∇S`.
  have hint : ∀ (Eltk : (Π b : M, TangentSpace I b) → (Π b : M, TangentSpace I b) → (x : M) →
        TensorRSSpace 0 s I x)
      (EltkCc : ∀ (a b : Fin N), SmoothCcTensor g 0 s),
      (∀ (a b : Fin N) (x : M), (EltkCc a b).toSection x = Eltk (V a) (V b) x) →
      ∀ (a b : Fin N), Integrable
        (fun x : M => tensorInnerPointwise (I := I) (M := M) g 0 s x
          (TensorRSSpace.toModel (Eltk (V a) (V b) x))
          (TensorRSSpace.toModel (bochnerGradSlot0 (I := I) (M := M) g s S (V b) x)))
        (riemannianVolumeMeasure (I := I) (M := M) g) := by
    intro Eltk EltkCc hEltkCc a b
    have hib := SmoothCcTensor.integrable_inner_cross (I := I) (M := M) (EltkCc a b)
      (bochnerGradSlot0Cc (I := I) (M := M) g s S (hV b))
    refine hib.congr (Filter.Eventually.of_forall (fun x => ?_))
    simp only [SmoothCcTensor.toFun_apply, hEltkCc a b x,
      bochnerGradSlot0Cc_toSection_apply (I := I) (M := M) g s S (hV b) x]
  have hint1 := hint (bochnerGroupElt1 (I := I) (M := M) g s S)
    (fun a b => bochnerGroupElt1Cc (I := I) (M := M) g s S (hV a) (hV b))
    (fun a b x => bochnerGroupElt1Cc_toSection_eq (I := I) (M := M) g s S (hV a) (hV b) x)
  have hint2 := hint (bochnerGroupElt2 (I := I) (M := M) g s S)
    (fun a b => bochnerGroupElt2Cc (I := I) (M := M) g s S (hV a) (hV b))
    (fun a b x => bochnerGroupElt2Cc_toSection_eq (I := I) (M := M) g s S (hV a) (hV b) x)
  have hint3 := hint (bochnerGroupElt3 (I := I) (M := M) g s S)
    (fun a b => bochnerGroupElt3Cc (I := I) (M := M) g s S (hV a) (hV b))
    (fun a b x => bochnerGroupElt3Cc_toSection_eq (I := I) (M := M) g s S (hV a) (hV b) x)
  have hint4 := hint (bochnerGroupElt4 (I := I) (M := M) g s S)
    (fun a b => bochnerGroupElt4Cc (I := I) (M := M) g s S (hV a) (hV b))
    (fun a b x => bochnerGroupElt4Cc_toSection_eq (I := I) (M := M) g s S (hV a) (hV b) x)
  -- The slot-`0` read of the defect splits into the four carriers (`bochnerSlot0Curv_eq_groupSum`),
  -- so the unified fold assembly produces the combined group double sum.
  rw [fold_assembly (I := I) (M := M) g s S V hV hPar (pointwiseTensorCurv (I := I) (M := M) g s S)
    (fun Va Vb x =>
      bochnerGroupElt1 (I := I) (M := M) g s S Va Vb x +
        bochnerGroupElt2 (I := I) (M := M) g s S Va Vb x +
        bochnerGroupElt3 (I := I) (M := M) g s S Va Vb x +
        bochnerGroupElt4 (I := I) (M := M) g s S Va Vb x)
    (fun b x => bochnerSlot0Curv_eq_groupSum (I := I) (M := M) g s S V hV hPar b x)
    (fun a b => by
      have h12 := (hint1 a b).add (hint2 a b)
      have h123 := h12.add (hint3 a b)
      have h1234 := h123.add (hint4 a b)
      refine h1234.congr (Filter.Eventually.of_forall (fun x => ?_))
      simp only [Pi.add_apply]
      rw [← tensorInnerPointwise_add_left, ← tensorInnerPointwise_add_left,
        ← tensorInnerPointwise_add_left,
        ← TensorRSSpace.toModel_add, ← TensorRSSpace.toModel_add, ← TensorRSSpace.toModel_add])]
  -- Distribute the combined carrier double sum into the four group double sums via a
  -- `Fin 4`-indexed carrier family and `∫∑ = ∑∫`.
  set carr : Fin 4 → (Π b : M, TangentSpace I b) → (Π b : M, TangentSpace I b) → (x : M) →
      TensorRSSpace 0 s I x :=
    ![bochnerGroupElt1 (I := I) (M := M) g s S, bochnerGroupElt2 (I := I) (M := M) g s S,
      bochnerGroupElt3 (I := I) (M := M) g s S, bochnerGroupElt4 (I := I) (M := M) g s S]
    with hcarr_def
  have hcarrint : ∀ (k : Fin 4) (a b : Fin N), Integrable
      (fun x : M => tensorInnerPointwise (I := I) (M := M) g 0 s x
        (TensorRSSpace.toModel (carr k (V a) (V b) x))
        (TensorRSSpace.toModel (bochnerGradSlot0 (I := I) (M := M) g s S (V b) x)))
      (riemannianVolumeMeasure (I := I) (M := M) g) := by
    intro k a b
    fin_cases k
    · exact hint1 a b
    · exact hint2 a b
    · exact hint3 a b
    · exact hint4 a b
  -- The combined per-`(a, b)` integrand is the `Fin 4`-sum of the carrier pairings.
  have hsplit : ∀ a b : Fin N,
      (∫ x, tensorInnerPointwise (I := I) (M := M) g 0 s x
          (TensorRSSpace.toModel
            (bochnerGroupElt1 (I := I) (M := M) g s S (V a) (V b) x +
              bochnerGroupElt2 (I := I) (M := M) g s S (V a) (V b) x +
              bochnerGroupElt3 (I := I) (M := M) g s S (V a) (V b) x +
              bochnerGroupElt4 (I := I) (M := M) g s S (V a) (V b) x))
          (TensorRSSpace.toModel (bochnerGradSlot0 (I := I) (M := M) g s S (V b) x))
        ∂(riemannianVolumeMeasure (I := I) (M := M) g)) =
      ∑ k : Fin 4,
        ∫ x, tensorInnerPointwise (I := I) (M := M) g 0 s x
            (TensorRSSpace.toModel (carr k (V a) (V b) x))
            (TensorRSSpace.toModel (bochnerGradSlot0 (I := I) (M := M) g s S (V b) x))
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
    intro a b
    rw [← MeasureTheory.integral_finset_sum Finset.univ (fun k _ => hcarrint k a b)]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    change tensorInnerPointwise (I := I) (M := M) g 0 s x
        (TensorRSSpace.toModel
          (bochnerGroupElt1 (I := I) (M := M) g s S (V a) (V b) x +
            bochnerGroupElt2 (I := I) (M := M) g s S (V a) (V b) x +
            bochnerGroupElt3 (I := I) (M := M) g s S (V a) (V b) x +
            bochnerGroupElt4 (I := I) (M := M) g s S (V a) (V b) x))
        (TensorRSSpace.toModel (bochnerGradSlot0 (I := I) (M := M) g s S (V b) x)) =
      ∑ k : Fin 4, tensorInnerPointwise (I := I) (M := M) g 0 s x
        (TensorRSSpace.toModel (carr k (V a) (V b) x))
        (TensorRSSpace.toModel (bochnerGradSlot0 (I := I) (M := M) g s S (V b) x))
    rw [Fin.sum_univ_four]
    simp only [hcarr_def, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_three]
    rw [TensorRSSpace.toModel_add, TensorRSSpace.toModel_add, TensorRSSpace.toModel_add,
      tensorInnerPointwise_add_left, tensorInnerPointwise_add_left,
      tensorInnerPointwise_add_left]
  -- Reassemble: the combined double sum equals `∑_k` of the group double sums.
  rw [show bochnerFoldGroupSum (I := I) (M := M) g s S V
        (bochnerGroupElt1 (I := I) (M := M) g s S) +
        bochnerFoldGroupSum (I := I) (M := M) g s S V
          (bochnerGroupElt2 (I := I) (M := M) g s S) +
        bochnerFoldGroupSum (I := I) (M := M) g s S V
          (bochnerGroupElt3 (I := I) (M := M) g s S) +
        bochnerFoldGroupSum (I := I) (M := M) g s S V
          (bochnerGroupElt4 (I := I) (M := M) g s S) =
      ∑ k : Fin 4, bochnerFoldGroupSum (I := I) (M := M) g s S V (carr k) from by
    rw [Fin.sum_univ_four]
    simp only [hcarr_def, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_three]]
  -- LHS combined double sum, split per `(a, b)` into the `Fin 4`-sum, reordered to the outside.
  rw [show bochnerFoldGroupSum (I := I) (M := M) g s S V
        (fun Va Vb x =>
          bochnerGroupElt1 (I := I) (M := M) g s S Va Vb x +
            bochnerGroupElt2 (I := I) (M := M) g s S Va Vb x +
            bochnerGroupElt3 (I := I) (M := M) g s S Va Vb x +
            bochnerGroupElt4 (I := I) (M := M) g s S Va Vb x) =
      ∑ a : Fin N, ∑ b : Fin N, ∑ k : Fin 4,
        ∫ x, tensorInnerPointwise (I := I) (M := M) g 0 s x
            (TensorRSSpace.toModel (carr k (V a) (V b) x))
            (TensorRSSpace.toModel (bochnerGradSlot0 (I := I) (M := M) g s S (V b) x))
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) from by
    rw [bochnerFoldGroupSum]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    refine Finset.sum_congr rfl (fun b _ => ?_)
    exact hsplit a b]
  rw [show (∑ k : Fin 4, bochnerFoldGroupSum (I := I) (M := M) g s S V (carr k)) =
      ∑ k : Fin 4, ∑ a : Fin N, ∑ b : Fin N,
        ∫ x, tensorInnerPointwise (I := I) (M := M) g 0 s x
            (TensorRSSpace.toModel (carr k (V a) (V b) x))
            (TensorRSSpace.toModel (bochnerGradSlot0 (I := I) (M := M) g s S (V b) x))
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) from by
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [bochnerFoldGroupSum]]
  -- The triple sum reorder `∑_a ∑_b ∑_k = ∑_k ∑_a ∑_b`.
  rw [Finset.sum_congr rfl (fun a (_ : a ∈ (Finset.univ : Finset (Fin N))) =>
    Finset.sum_comm (s := (Finset.univ : Finset (Fin N))) (t := (Finset.univ : Finset (Fin 4)))
      (f := fun b k => ∫ x, tensorInnerPointwise (I := I) (M := M) g 0 s x
        (TensorRSSpace.toModel (carr k (V a) (V b) x))
        (TensorRSSpace.toModel (bochnerGradSlot0 (I := I) (M := M) g s S (V b) x))
        ∂(riemannianVolumeMeasure (I := I) (M := M) g)))]
  rw [Finset.sum_comm]

set_option linter.unusedSectionVars false in
/-- **The admissible summed fold: the group-`2` + group-`3` + group-`4` double sum equals the
curvature cross-pairing minus the pure-Riemann trace.**  For a fixed Parseval frame family,
```
G₂ + G₃ + G₄ = ⟨pointwiseTensorCurv g s S, ∇S⟩_{L²} − ⟨GcurvSection g s S, ∇S⟩_{L²}.
```
This is the variance-admissible replacement of the former per-group folds (`G₃ = ricTrace`,
`G₂ + G₄ = operator residue`), which assigned individual gauge-invariant values to single groups and
are FALSE in dim ≥ 3 with a common cancelling error `±N` (`PROVE_REFUTED.md`, "Kernel per-group
VALUE-ASSIGNMENT family"); here the `±N` stays inside the sum and only the TRUE summed conclusion is
stated.  Sorry-free: the seven-term bridge `bochnerFold_sevenTermSum_eq_pointwiseTensorCurvPairing`
gives `⟨Curv S, ∇S⟩ = G₁ + G₂ + G₃ + G₄`, and the pointwise-Parseval group-`1` fold
`bochnerFold_group1_eq_GcurvSection` gives `G₁ = ⟨GcurvSection g s S, ∇S⟩`; no per-group value step
is used. -/
private theorem parsevalFrameSum_group2_add_group3_add_group4_eq_curv_sub_gcurv
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s)
    {N : ℕ} (V : Fin N → Π b : M, TangentSpace I b)
    (hV : ∀ a, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => (⟨b, V a b⟩ : TotalSpace E (TangentSpace I))))
    (hPar : ∀ (x : M) (u : TangentSpace I x),
      (∑ a : Fin N, g.inner x (V a x) u • V a x) = u) :
    bochnerFoldGroupSum (I := I) (M := M) g s S V
        (bochnerGroupElt2 (I := I) (M := M) g s S) +
      bochnerFoldGroupSum (I := I) (M := M) g s S V
        (bochnerGroupElt3 (I := I) (M := M) g s S) +
      bochnerFoldGroupSum (I := I) (M := M) g s S V
        (bochnerGroupElt4 (I := I) (M := M) g s S) =
      tensorL2Inner (I := I) (M := M) g 0 (s + 1)
          (pointwiseTensorCurv (I := I) (M := M) g s S).toFun
          (covGrad (I := I) (M := M) g 0 s S).toFun -
        tensorL2Inner (I := I) (M := M) g 0 (s + 1)
          (GcurvSection (I := I) (M := M) g s S).toFun
          (covGrad (I := I) (M := M) g 0 s S).toFun := by
  classical
  have hf5 := bochnerFold_sevenTermSum_eq_pointwiseTensorCurvPairing
    (I := I) (M := M) g s S V hV hPar
  have hf1 := bochnerFold_group1_eq_GcurvSection (I := I) (M := M) g s S V hV hPar
  linarith [hf5, hf1]

set_option linter.unusedSectionVars false in
/-- **The summed chain endpoint over the proven primitive: the group-`4` double sum minus the cross
pairing equals the curvature cross-pairing minus the pure-Riemann and Ricci traces.**  For a fixed
Parseval frame family,
```
G₄ − I₂ = ⟨Curv S, ∇S⟩_{L²} − ⟨GcurvSection g s S, ∇S⟩_{L²} − ⟨ricTraceSection g s S, ∇S⟩_{L²},
```
with `I₂ := ∑_a ∑_b ∫ ⟨R(V a, V b) S, ∇²_{V a, V b} S⟩` the curvature/Hessian cross pairing
(`crossHessianCc`, the genuine `tensorSecondCovDeriv` carrier, tensorial in both slots).
This is the re-glued summed chain of the rank-`0` Bochner kernel over the proven
primitive `D = −(G₁ + I₂)` (`parsevalFrameSum_diffCurvTrace_doubleSum_eq_neg_group1_add_crossPairing`):
the admissible summed fold (`G₂ + G₃ + G₄ = ⟨Curv⟩ − ⟨Gcurv⟩`), the variance-honest group-`3`
decomposition (`G₃ = bochnerFoldGroupSum (bochnerGroupElt3IiiIv) + ⟨ric, ∇S⟩`), the sorry-free
covariant-Leibniz split (`bochnerFoldGroupSum (bochnerGroupElt3IiiIv) = D − G₂ + G₁`), and the
primitive cancel `G₁`, `G₂`, and `D`, leaving exactly this difference identity.  Neither side
assigns a gauge-invariant value to a single group (the left is the difference combination whose
gauge variations cancel — the dim-`3`-confirmed content of the primitive).  Sorry-free. -/
private theorem parsevalFrameSum_group4_sub_crossPairing_eq_curv_sub_gcurv_sub_ricTrace
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s)
    {N : ℕ} (V : Fin N → Π b : M, TangentSpace I b)
    (hV : ∀ a, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => (⟨b, V a b⟩ : TotalSpace E (TangentSpace I))))
    (hPar : ∀ (x : M) (u : TangentSpace I x),
      (∑ a : Fin N, g.inner x (V a x) u • V a x) = u) :
    bochnerFoldGroupSum (I := I) (M := M) g s S V
        (bochnerGroupElt4 (I := I) (M := M) g s S) -
      (∑ a : Fin N, ∑ b : Fin N,
        ∫ x, tensorInnerScalar (I := I) (M := M) g 0 s
            (riemannSecCc (I := I) (M := M) g s S (hV a) (hV b)).toSection
            (crossHessianCc (I := I) (M := M) g s S (hV a) (hV b)).toSection x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g)) =
      tensorL2Inner (I := I) (M := M) g 0 (s + 1)
          (pointwiseTensorCurv (I := I) (M := M) g s S).toFun
          (covGrad (I := I) (M := M) g 0 s S).toFun -
        tensorL2Inner (I := I) (M := M) g 0 (s + 1)
          (GcurvSection (I := I) (M := M) g s S).toFun
          (covGrad (I := I) (M := M) g 0 s S).toFun -
        tensorL2Inner (I := I) (M := M) g 0 (s + 1)
          (ricTraceSection (I := I) (M := M) g s S).toFun
          (covGrad (I := I) (M := M) g 0 s S).toFun := by
  classical
  have hsum := parsevalFrameSum_group2_add_group3_add_group4_eq_curv_sub_gcurv
    (I := I) (M := M) g s S V hV hPar
  have h3 := bochnerFoldGroupSum_elt3_eq_iiiIvSum_add_ricTrace
    (I := I) (M := M) g s S V hV hPar
  have hsplit := bochnerFoldGroupSum_elt3IiiIv_eq_nablaDiffCurvTrace_split
    (I := I) (M := M) g s S V hV
  have hP := parsevalFrameSum_diffCurvTrace_doubleSum_eq_neg_group1_add_crossPairing
    (I := I) (M := M) g s S V hV hPar
  linarith [hsum, h3, hsplit, hP]






set_option linter.unusedSectionVars false in
/-- **The two-slot curry value of the genuine Hessian (fibre-bilinear form of
`tensorSecondCovDeriv`).** For smooth tangent fields `X, Y`, the unit-evaluated genuine second
covariant derivative `∇²_{X, Y} S (x)(unit)` equals the double leading-slot curry of the
second covariant gradient `∇²S = covGrad (covGrad S)` read at the *values* `(X x, Y x)`:
```
(∇²_{X, Y} S)(x)(unit) = curry (curry (∇²S(x)(unit)) (X x)) (Y x).
```
This is `tensorSecondCovDeriv_eq_covGrad_succ_twoSlotEval_genVal` (`GradientField`) packaged as a
`Tensor0SSpace s` identity through the leading-slot currying equivalence; it certifies that the
genuine Hessian is **tensorial (value-bilinear) in both direction slots**, the fact the
cometric-parallel antisymmetry consumes. -/
private lemma tensorSecondCovDeriv_unit_eq_twoSlotCurry
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s)
    {X Y : Π b : M, TangentSpace I b}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => (⟨b, X b⟩ : TotalSpace E (TangentSpace I))))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => (⟨b, Y b⟩ : TotalSpace E (TangentSpace I)))) (x : M) :
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
        tensorSecondCovDeriv (I := I) g 0 s X Y (fun y : M => S.toSection y) x)
        (unitZeroSec (I := I) (M := M) x) =
      tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x
        (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) (s + 1) x
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1 + 1) I x from
            (covGrad (I := I) (M := M) g 0 (s + 1)
              (covGrad (I := I) (M := M) g 0 s S)).toSection x)
            (unitZeroSec (I := I) (M := M) x))
          (X x))
        (Y x) := by
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro m
  rw [← tensorSecondCovDeriv_eq_covGrad_succ_twoSlotEval_genVal (I := I) (M := M) g s S
    hX hY x m]
  rw [TensorMultilinear.tensor0S_curry_apply_eval, TensorMultilinear.tensor0S_curry_apply_eval]

set_option linter.unusedSectionVars false in
/-- **The group-`4` family sum vanishes pointwise (the cometric-parallel kill of the symmetric
second-order pair).** For a fixed smooth Parseval frame family `V`, a fixed read direction
`V b`, and every point `x`, the family sum over `a` of the group-`4` carrier pairing
`⟨−∇²_{∇_{V b} V a, V a} S − ∇²_{V a, ∇_{V b} V a} S, ∇_{V b} S⟩` vanishes: the genuine Hessian
is value-bilinear in its two direction slots (`tensorSecondCovDeriv_unit_eq_twoSlotCurry`), so
the sum is the cometric-parallel covariant-derivative pair antisymmetry
`parsevalFrame_sum_bilin_covDeriv_pair_antisymm` (`∇(∑_a V_a ⊗ V_a) = ∇ g⁻¹ = 0`) contracted
against the Hessian/gradient bilinear form. -/
private lemma bochnerGroupElt4_pairing_familySum_eq_zero
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s)
    {N : ℕ} (V : Fin N → Π b : M, TangentSpace I b)
    (hV : ∀ a, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => (⟨b, V a b⟩ : TotalSpace E (TangentSpace I))))
    (hPar : ∀ (x : M) (u : TangentSpace I x),
      (∑ a : Fin N, g.inner x (V a x) u • V a x) = u) (b : Fin N) (x : M) :
    (∑ a : Fin N,
        tensorInnerPointwise (I := I) (M := M) g 0 s x
          (TensorRSSpace.toModel (bochnerGroupElt4 (I := I) (M := M) g s S (V a) (V b) x))
          (TensorRSSpace.toModel (bochnerGradSlot0 (I := I) (M := M) g s S (V b) x))) = 0 := by
  classical
  -- The two-slot curry of `∇²S(x)(unit)`, the value-bilinear Hessian kernel at `x`.
  set T2 : Tensor0SSpace (s + 1 + 1) I x :=
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1 + 1) I x from
      (covGrad (I := I) (M := M) g 0 (s + 1)
        (covGrad (I := I) (M := M) g 0 s S)).toSection x)
      (unitZeroSec (I := I) (M := M) x) with hT2_def
  -- The Hessian/gradient bilinear form on the tangent fibre.
  set B : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ :=
    LinearMap.mk₂ ℝ
      (fun u p => tensorInnerPointwise (I := I) (M := M) g 0 s x
        (TensorRSSpace.toModel (tensor0SAsRS (I := I) (M := M) x
          (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x
            (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) (s + 1) x T2 u) p)))
        (TensorRSSpace.toModel (bochnerGradSlot0 (I := I) (M := M) g s S (V b) x)))
      (fun u₁ u₂ p => by
        beta_reduce
        rw [map_add (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) (s + 1) x T2) u₁ u₂,
          show tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x
              (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) (s + 1) x T2 u₁ +
                tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) (s + 1) x T2 u₂) =
            tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x
                (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) (s + 1) x T2 u₁) +
              tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x
                (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) (s + 1) x T2 u₂) from
            map_add (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x) _ _,
          ContinuousLinearMap.add_apply, tensor0SAsRS_add (I := I) (M := M) s x,
          TensorRSSpace.toModel_add,
          tensorInnerPointwise_add_left (I := I) (M := M) g 0 s x])
      (fun c u p => by
        beta_reduce
        rw [map_smul (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) (s + 1) x T2) c u,
          show tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x
              (c • tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) (s + 1) x T2 u) =
            c • tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x
                (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) (s + 1) x T2 u) from
            map_smul (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x) c _,
          ContinuousLinearMap.smul_apply, tensor0SAsRS_smul (I := I) (M := M) s x,
          TensorRSSpace.toModel_smul,
          tensorInnerPointwise_smul_left (I := I) (M := M) g 0 s x, smul_eq_mul])
      (fun u p₁ p₂ => by
        beta_reduce
        rw [map_add (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x
            (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) (s + 1) x T2 u)) p₁ p₂,
          tensor0SAsRS_add (I := I) (M := M) s x, TensorRSSpace.toModel_add,
          tensorInnerPointwise_add_left (I := I) (M := M) g 0 s x])
      (fun c u p => by
        beta_reduce
        rw [map_smul (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x
            (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) (s + 1) x T2 u)) c p,
          tensor0SAsRS_smul (I := I) (M := M) s x, TensorRSSpace.toModel_smul,
          tensorInnerPointwise_smul_left (I := I) (M := M) g 0 s x, smul_eq_mul])
    with hB_def
  have hBval : ∀ u p : TangentSpace I x, B u p =
      tensorInnerPointwise (I := I) (M := M) g 0 s x
        (TensorRSSpace.toModel (tensor0SAsRS (I := I) (M := M) x
          (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x
            (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) (s + 1) x T2 u) p)))
        (TensorRSSpace.toModel (bochnerGradSlot0 (I := I) (M := M) g s S (V b) x)) :=
    fun u p => rfl
  -- Each group-`4` carrier pairing is the negated `B`-pair at `(∇_{V b} V a, V a)`.
  have hpt : ∀ a : Fin N,
      tensorInnerPointwise (I := I) (M := M) g 0 s x
          (TensorRSSpace.toModel (bochnerGroupElt4 (I := I) (M := M) g s S (V a) (V b) x))
          (TensorRSSpace.toModel (bochnerGradSlot0 (I := I) (M := M) g s S (V b) x)) =
        - (B ((LeviCivita (I := I) g).toFun (V a) x (V b x)) (V a x) +
            B (V a x) ((LeviCivita (I := I) g).toFun (V a) x (V b x))) := by
    intro a
    -- Smoothness of the frame-derivative field `y ↦ ∇_{V b} V a (y)`.
    have hNba : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
        (fun y : M => (⟨y, (LeviCivita (I := I) g).toFun (V a) y (V b y)⟩ :
          TotalSpace E (TangentSpace I))) :=
      covApply_contMDiff (cov := LeviCivita (I := I) g) (hV b) (hV a)
    have h1 := tensorSecondCovDeriv_unit_eq_twoSlotCurry (I := I) (M := M) g s S
      (X := fun y : M => (LeviCivita (I := I) g).toFun (V a) y (V b y)) (Y := V a)
      hNba (hV a) x
    have h2 := tensorSecondCovDeriv_unit_eq_twoSlotCurry (I := I) (M := M) g s S
      (X := V a) (Y := fun y : M => (LeviCivita (I := I) g).toFun (V a) y (V b y))
      (hV a) hNba x
    rw [show bochnerGroupElt4 (I := I) (M := M) g s S (V a) (V b) x =
        tensor0SAsRS (I := I) (M := M) x
          (- (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x
              (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) (s + 1) x T2
                ((LeviCivita (I := I) g).toFun (V a) x (V b x))) (V a x)) -
            tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x
              (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) (s + 1) x T2 (V a x))
              ((LeviCivita (I := I) g).toFun (V a) x (V b x))) from by
      rw [bochnerGroupElt4, h1, h2]]
    rw [show (- (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x
            (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) (s + 1) x T2
              ((LeviCivita (I := I) g).toFun (V a) x (V b x))) (V a x)) -
          tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x
            (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) (s + 1) x T2 (V a x))
            ((LeviCivita (I := I) g).toFun (V a) x (V b x))) =
        (-1 : ℝ) • (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x
            (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) (s + 1) x T2
              ((LeviCivita (I := I) g).toFun (V a) x (V b x))) (V a x)) +
          (-1 : ℝ) • (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x
            (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) (s + 1) x T2 (V a x))
            ((LeviCivita (I := I) g).toFun (V a) x (V b x))) from by
      rw [neg_one_smul, neg_one_smul]; abel]
    rw [tensor0SAsRS_add (I := I) (M := M) s x,
      tensor0SAsRS_smul (I := I) (M := M) s x, tensor0SAsRS_smul (I := I) (M := M) s x,
      TensorRSSpace.toModel_add, TensorRSSpace.toModel_smul, TensorRSSpace.toModel_smul,
      tensorInnerPointwise_add_left (I := I) (M := M) g 0 s x,
      tensorInnerPointwise_smul_left (I := I) (M := M) g 0 s x,
      tensorInnerPointwise_smul_left (I := I) (M := M) g 0 s x,
      hBval ((LeviCivita (I := I) g).toFun (V a) x (V b x)) (V a x),
      hBval (V a x) ((LeviCivita (I := I) g).toFun (V a) x (V b x))]
    ring
  rw [Finset.sum_congr rfl (fun a _ => hpt a), Finset.sum_neg_distrib,
    parsevalFrame_sum_bilin_covDeriv_pair_antisymm (I := I) (M := M) g V hV hPar
      (V b) x B, neg_zero]

set_option linter.unusedSectionVars false in
/-- **The group-`4` double sum vanishes (`G₄ = 0`).** For a fixed smooth Parseval frame family,
the group-`4` fold `bochnerFoldGroupSum (bochnerGroupElt4)` is zero: the symmetric second-order
carrier pair `−∇²_{∇_{V b} V a, V a} S − ∇²_{V a, ∇_{V b} V a} S` is built on the genuine
(value-bilinear) Hessian, so its family sum over `a` is killed pointwise by the
cometric-parallel covariant-derivative pair antisymmetry
(`bochnerGroupElt4_pairing_familySum_eq_zero`); the double-sum integral of a pointwise-zero
family is zero.  This is a frame-free *value* for `G₄` — admissible because it is pointwise
Parseval (a pointwise antisymmetry kill, not an integrated cancellation), exactly like the
surviving group-`1` fold. -/
private theorem bochnerFoldGroupSum_elt4_eq_zero
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s)
    {N : ℕ} (V : Fin N → Π b : M, TangentSpace I b)
    (hV : ∀ a, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => (⟨b, V a b⟩ : TotalSpace E (TangentSpace I))))
    (hPar : ∀ (x : M) (u : TangentSpace I x),
      (∑ a : Fin N, g.inner x (V a x) u • V a x) = u) :
    bochnerFoldGroupSum (I := I) (M := M) g s S V
      (bochnerGroupElt4 (I := I) (M := M) g s S) = 0 := by
  classical
  have hint : ∀ a b : Fin N, Integrable
      (fun x : M => tensorInnerPointwise (I := I) (M := M) g 0 s x
        (TensorRSSpace.toModel (bochnerGroupElt4 (I := I) (M := M) g s S (V a) (V b) x))
        (TensorRSSpace.toModel (bochnerGradSlot0 (I := I) (M := M) g s S (V b) x)))
      (riemannianVolumeMeasure (I := I) (M := M) g) := by
    intro a b
    refine (SmoothCcTensor.integrable_inner_cross (I := I) (M := M)
      (bochnerGroupElt4Cc (I := I) (M := M) g s S (hV a) (hV b))
      (bochnerGradSlot0Cc (I := I) (M := M) g s S (hV b))).congr
      (Filter.Eventually.of_forall (fun x => ?_))
    simp only [SmoothCcTensor.toFun_apply,
      bochnerGroupElt4Cc_toSection_eq (I := I) (M := M) g s S (hV a) (hV b) x,
      bochnerGradSlot0Cc_toSection_apply (I := I) (M := M) g s S (hV b) x]
  rw [bochnerFoldGroupSum, Finset.sum_comm]
  refine Finset.sum_eq_zero (fun b _ => ?_)
  rw [← MeasureTheory.integral_finset_sum Finset.univ (fun a _ => hint a b)]
  rw [show (∫ x, (∑ a : Fin N,
        tensorInnerPointwise (I := I) (M := M) g 0 s x
          (TensorRSSpace.toModel (bochnerGroupElt4 (I := I) (M := M) g s S (V a) (V b) x))
          (TensorRSSpace.toModel (bochnerGradSlot0 (I := I) (M := M) g s S (V b) x)))
      ∂(riemannianVolumeMeasure (I := I) (M := M) g)) =
      ∫ _x, (0 : ℝ) ∂(riemannianVolumeMeasure (I := I) (M := M) g) from
    MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun x =>
      bochnerGroupElt4_pairing_familySum_eq_zero (I := I) (M := M) g s S V hV hPar b x))]
  exact MeasureTheory.integral_zero _ _

set_option linter.unusedSectionVars false in
/-- **The per-`b` fold assembly.** For a fixed Parseval frame family and a named smooth
`(0, s + 1)`-tensor section `Named` whose slot-`0` `V b`-read is, at every point, the section
value of the single packaged carrier `Elt b`, the `L²` pairing of `Named` against `∇S` is the
single frame sum of the per-`b` carrier pairing integrals.  The per-`b` (carrier-sum-free)
variant of `fold_assembly`: the slot-`0` fixed-family Parseval expansion of the `(0, s + 1)`
pairing (`tensorInnerPointwise_succ_eq_parseval_sum_slot0`) plus the integral/sum interchange. -/
private lemma fold_assembly_perB
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s)
    {N : ℕ} (V : Fin N → Π b : M, TangentSpace I b)
    (hV : ∀ a, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => (⟨b, V a b⟩ : TotalSpace E (TangentSpace I))))
    (hPar : ∀ (x : M) (u : TangentSpace I x),
      (∑ a : Fin N, g.inner x (V a x) u • V a x) = u)
    (Named : SmoothCcTensor g 0 (s + 1)) (Elt : Fin N → SmoothCcTensor g 0 s)
    (hslot0 : ∀ (b : Fin N) (x : M),
      tensor0SAsRS (I := I) (M := M) x
          ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x
            ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from Named.toSection x)
              (unitZeroSec (I := I) (M := M) x))) (V b x)) =
        (Elt b).toSection x) :
    tensorL2Inner (I := I) (M := M) g 0 (s + 1) (Named).toFun
        (covGrad (I := I) (M := M) g 0 s S).toFun =
      ∑ b : Fin N,
        ∫ x, tensorInnerScalar (I := I) (M := M) g 0 s
            (Elt b).toSection (bochnerGradSlot0Cc (I := I) (M := M) g s S (hV b)).toSection x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  classical
  rw [show tensorL2Inner (I := I) (M := M) g 0 (s + 1) (Named).toFun
        (covGrad (I := I) (M := M) g 0 s S).toFun =
      ∫ x, (∑ b : Fin N,
          tensorInnerScalar (I := I) (M := M) g 0 s
            (Elt b).toSection (bochnerGradSlot0Cc (I := I) (M := M) g s S (hV b)).toSection x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) from ?_]
  · exact MeasureTheory.integral_finset_sum Finset.univ
      (fun b _ => SmoothCcTensor.integrable_inner_cross (I := I) (M := M)
        (Elt b) (bochnerGradSlot0Cc (I := I) (M := M) g s S (hV b)))
  · refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    change tensorInnerPointwise (I := I) (M := M) g 0 (s + 1) x (Named.toFun x)
        ((covGrad (I := I) (M := M) g 0 s S).toFun x) = _
    rw [show (Named).toFun x = TensorRSSpace.toModel (Named.toSection x) from rfl,
      show (covGrad (I := I) (M := M) g 0 s S).toFun x =
        TensorRSSpace.toModel ((covGrad (I := I) (M := M) g 0 s S).toSection x) from rfl]
    rw [tensorInnerPointwise_succ_eq_parseval_sum_slot0 (I := I) (M := M) g V hPar s x
      (Named.toSection x) ((covGrad (I := I) (M := M) g 0 s S).toSection x)]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [tensorInnerScalar_apply (I := I) (M := M) g 0 s, ← hslot0 b x]
    rfl

set_option linter.unusedSectionVars false in
/-- **The per-direction covariant integration by parts of a packaged `(0, s)` cross pairing.**
For smooth compactly-supported `(0, s)`-tensors `W, Z` and a smooth direction field `V b`,
```
∫ ⟨∇_{V b} W, Z⟩ = − ∫ ⟨W, ∇_{V b} Z⟩ − ∫ ⟨W, Z⟩ · divᵍ(V b),
```
the split of the self-contained per-direction covariant IBP
`integral_tensorInner_covDeriv_combined_eq_zero` through the first-slot engine bridge
`loweredFirstSlot_eq_covApply_inner` (both slots, the second through the `(0, s)`-pairing
symmetry), with each summand integrable as a `Cc` cross pairing or a continuous function on the
compact manifold. -/
private lemma integral_covApplyPair_IBP
    (g : SmoothRiemannianMetric I M) (s : ℕ) (W Z : SmoothCcTensor g 0 s)
    {Vb : Π b : M, TangentSpace I b}
    (hVb : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => (⟨b, Vb b⟩ : TotalSpace E (TangentSpace I)))) :
    (∫ x, tensorInnerScalar (I := I) (M := M) g 0 s
        (covApplyGenCc (I := I) (M := M) g s W hVb).toSection Z.toSection x
      ∂(riemannianVolumeMeasure (I := I) (M := M) g)) =
      - (∫ x, tensorInnerScalar (I := I) (M := M) g 0 s
          W.toSection (covApplyGenCc (I := I) (M := M) g s Z hVb).toSection x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g)) -
      (∫ x, tensorInnerScalar (I := I) (M := M) g 0 s W.toSection Z.toSection x *
          DifferentialGeometry.Integral.DivergenceTheorem.divergence_g (I := I) g
            ⟨fun y : M => Vb y, hVb⟩ x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g)) := by
  classical
  have heng := integral_tensorInner_covDeriv_combined_eq_zero (I := I) (M := M) g 0 s
    W.toSection Z.toSection ⟨fun y : M => Vb y, hVb⟩
  -- Pointwise identification of the three engine summands.
  have h1 : ∀ x : M,
      tensorInnerPointwise_0s (I := I) (M := M) (0 + s) g x
          (Tensor0SSpace.toModel
            (loweredCovDerivAlongVF (I := I) (M := M) g 0 s W.toSection
              ⟨fun y : M => Vb y, hVb⟩ x))
          (Tensor0SSpace.toModel
            (liftedTensorSection (I := I) (M := M) g 0 s Z.toSection x)) =
        tensorInnerScalar (I := I) (M := M) g 0 s
          (covApplyGenCc (I := I) (M := M) g s W hVb).toSection Z.toSection x := by
    intro x
    rw [tensorInnerScalar_apply (I := I) (M := M) g 0 s]
    exact loweredFirstSlot_eq_covApply_inner (I := I) (M := M) g s W Z hVb x
  have h2 : ∀ x : M,
      tensorInnerPointwise_0s (I := I) (M := M) (0 + s) g x
          (Tensor0SSpace.toModel
            (liftedTensorSection (I := I) (M := M) g 0 s W.toSection x))
          (Tensor0SSpace.toModel
            (loweredCovDerivAlongVF (I := I) (M := M) g 0 s Z.toSection
              ⟨fun y : M => Vb y, hVb⟩ x)) =
        tensorInnerScalar (I := I) (M := M) g 0 s
          W.toSection (covApplyGenCc (I := I) (M := M) g s Z hVb).toSection x := by
    intro x
    rw [tensorInnerPointwise_0s_symm (I := I) (M := M) g x (0 + s)]
    rw [tensorInnerScalar_apply (I := I) (M := M) g 0 s]
    rw [loweredFirstSlot_eq_covApply_inner (I := I) (M := M) g s Z W hVb x]
    exact tensorInnerPointwise_symm (I := I) (M := M) g 0 s x _ _
  have h3 : ∀ x : M,
      tensorInnerScalar (I := I) (M := M) g 0 s W.toSection Z.toSection x *
          DifferentialGeometry.Integral.DivergenceTheorem.divergence_g (I := I) g
            ⟨fun y : M => Vb y, hVb⟩ x =
        tensorInnerScalar (I := I) (M := M) g 0 s W.toSection Z.toSection x *
          DifferentialGeometry.Integral.DivergenceTheorem.divergence_g (I := I) g
            ⟨fun y : M => Vb y, hVb⟩ x := fun _ => rfl
  -- Integrability of the three summands.
  have hint1 : Integrable
      (fun x : M => tensorInnerScalar (I := I) (M := M) g 0 s
        (covApplyGenCc (I := I) (M := M) g s W hVb).toSection Z.toSection x)
      (riemannianVolumeMeasure (I := I) (M := M) g) :=
    SmoothCcTensor.integrable_inner_cross (I := I) (M := M)
      (covApplyGenCc (I := I) (M := M) g s W hVb) Z
  have hint2 : Integrable
      (fun x : M => tensorInnerScalar (I := I) (M := M) g 0 s
        W.toSection (covApplyGenCc (I := I) (M := M) g s Z hVb).toSection x)
      (riemannianVolumeMeasure (I := I) (M := M) g) :=
    SmoothCcTensor.integrable_inner_cross (I := I) (M := M)
      W (covApplyGenCc (I := I) (M := M) g s Z hVb)
  have hint3 : Integrable
      (fun x : M => tensorInnerScalar (I := I) (M := M) g 0 s W.toSection Z.toSection x *
        DifferentialGeometry.Integral.DivergenceTheorem.divergence_g (I := I) g
          ⟨fun y : M => Vb y, hVb⟩ x)
      (riemannianVolumeMeasure (I := I) (M := M) g) := by
    refine integrable_of_continuous_compactSpace (I := I) (M := M) g ?_
    exact ((tensorInnerScalar_contMDiff (I := I) (M := M) g 0 s
        W.toSection Z.toSection).continuous).mul
      ((DifferentialGeometry.Integral.DivergenceTheorem.divergence_g_contMDiff (I := I) g
        ⟨fun y : M => Vb y, hVb⟩).continuous)
  rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun x => by
    rw [h1 x, h2 x]))] at heng
  have h12 : Integrable
      (fun x : M => tensorInnerScalar (I := I) (M := M) g 0 s
          (covApplyGenCc (I := I) (M := M) g s W hVb).toSection Z.toSection x +
        tensorInnerScalar (I := I) (M := M) g 0 s
          W.toSection (covApplyGenCc (I := I) (M := M) g s Z hVb).toSection x)
      (riemannianVolumeMeasure (I := I) (M := M) g) := hint1.add hint2
  rw [MeasureTheory.integral_add h12 hint3,
    MeasureTheory.integral_add hint1 hint2] at heng
  linarith [heng]

set_option linter.unusedSectionVars false in
/-- **The slot-`0` `V b`-read of the spectator section `appCc (slotExtend Φ₀) (∇S)` is the
order-`0` curvature-operator action on the packaged directional gradient `∇_{V b} S`.**  This is
the unit-evaluated spectator law `appCc_slotExtend_curvOpField_covGrad_unit_eval` lifted to the
packaged carrier equality the per-`b` fold assembly consumes. -/
private lemma spectatorSlot0_eq_appCc_gradSlot
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s)
    {Vb : Π b : M, TangentSpace I b}
    (hVb : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => (⟨b, Vb b⟩ : TotalSpace E (TangentSpace I)))) (x : M) :
    tensor0SAsRS (I := I) (M := M) x
        ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
            (appCc (I := I) (M := M) g (s + 1) (s + 1)
              (slotExtend (I := I) (M := M) g s s (curvOpField (I := I) (M := M) g s))
              (covGrad (I := I) (M := M) g 0 s S)).toSection x)
            (unitZeroSec (I := I) (M := M) x))) (Vb x)) =
      (appCc (I := I) (M := M) g s s (curvOpField (I := I) (M := M) g s)
        (bochnerGradSlot0Cc (I := I) (M := M) g s S hVb)).toSection x := by
  classical
  apply tensorRSSpace_ext (𝕜 := ℝ) 0 s x
  intro d
  -- Left side: the wrap evaluates by scalar-rescaling of the curried value.
  rw [tensor0SAsRS_apply (I := I) (M := M) x _ d]
  -- Right side: the operator-field action evaluates fibrewise on the wrapped gradient slot.
  rw [appCc_toSection (I := I) (M := M) g s s (curvOpField (I := I) (M := M) g s)
    (bochnerGradSlot0Cc (I := I) (M := M) g s S hVb) x]
  rw [ContinuousLinearMap.comp_apply]
  rw [show (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
        (bochnerGradSlot0Cc (I := I) (M := M) g s S hVb).toSection x) d =
      tensor00Scalar (I := I) (M := M) x d •
        gradCurry0 (I := I) (M := M) g s S x (Vb x) from by
    rw [show (bochnerGradSlot0Cc (I := I) (M := M) g s S hVb).toSection x =
        tensor0SAsRS (I := I) (M := M) x
          (gradCurry0 (I := I) (M := M) g s S x (Vb x)) from rfl]
    exact tensor0SAsRS_apply (I := I) (M := M) x _ d]
  rw [ContinuousLinearMap.map_smul]
  congr 1

set_option linter.unusedSectionVars false in
/-- **The operator-field pairing three-term reduction (Green/B-rule normal form of the
differentiated-curvature pairing).** For a fixed smooth Parseval frame family, the frame-free
operator-field pairing `⟨appCc (covGrad Φ₀) S, ∇S⟩_{L²}` (`Φ₀ := curvOpField g s`) equals the
negated frame sum
```
−∑_b ∫ [ ⟨P, ∇_{V b}(∇_{V b} S)⟩ + ⟨P, ∇_{V b} S⟩·divᵍ(V b) + ⟨Φ₀(∇_{V b} S), ∇_{V b} S⟩ ],
```
with `P := appCc Φ₀ S` the order-`0` curvature trace.  This is the operator-field B-rule split
`tensorL2Inner_covGrad_appCc_eq_add` (isolating the spectator `appCc (slotExtend Φ₀)(∇S)`), the
per-`b` fold of both summands (`fold_assembly_perB`, the spectator slot-read
`spectatorSlot0_eq_appCc_gradSlot`), and the per-direction covariant integration by parts
`integral_covApplyPair_IBP` moving `∇_{V b}` off `P`. -/
private theorem tensorL2Inner_genuineDiffCurv_covGrad_eq_neg_threeTerm
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s)
    {N : ℕ} (V : Fin N → Π b : M, TangentSpace I b)
    (hV : ∀ a, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => (⟨b, V a b⟩ : TotalSpace E (TangentSpace I))))
    (hPar : ∀ (x : M) (u : TangentSpace I x),
      (∑ a : Fin N, g.inner x (V a x) u • V a x) = u) :
    tensorL2Inner (I := I) (M := M) g 0 (s + 1)
        (appCc (I := I) (M := M) g s (s + 1)
          (covGrad (I := I) (M := M) g s s (curvOpField (I := I) (M := M) g s)) S).toFun
        (covGrad (I := I) (M := M) g 0 s S).toFun =
      - ∑ b : Fin N,
        ((∫ x, tensorInnerScalar (I := I) (M := M) g 0 s
            (appCc (I := I) (M := M) g s s (curvOpField (I := I) (M := M) g s) S).toSection
            (covApplyGenCc (I := I) (M := M) g s
              (bochnerGradSlot0Cc (I := I) (M := M) g s S (hV b)) (hV b)).toSection x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g)) +
        (∫ x, tensorInnerScalar (I := I) (M := M) g 0 s
            (appCc (I := I) (M := M) g s s (curvOpField (I := I) (M := M) g s) S).toSection
            (bochnerGradSlot0Cc (I := I) (M := M) g s S (hV b)).toSection x *
            DifferentialGeometry.Integral.DivergenceTheorem.divergence_g (I := I) g
              ⟨fun y : M => V b y, hV b⟩ x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g)) +
        (∫ x, tensorInnerScalar (I := I) (M := M) g 0 s
            (appCc (I := I) (M := M) g s s (curvOpField (I := I) (M := M) g s)
              (bochnerGradSlot0Cc (I := I) (M := M) g s S (hV b))).toSection
            (bochnerGradSlot0Cc (I := I) (M := M) g s S (hV b)).toSection x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g))) := by
  classical
  set Φ₀ : SmoothCcTensor g s s := curvOpField (I := I) (M := M) g s with hΦ₀_def
  set P : SmoothCcTensor g 0 s := appCc (I := I) (M := M) g s s Φ₀ S with hP_def
  -- The B-rule split of `⟨∇(appCc Φ₀ S), ∇S⟩`.
  have hsplit := tensorL2Inner_covGrad_appCc_eq_add (I := I) (M := M) g s s Φ₀ S
    (covGrad (I := I) (M := M) g 0 s S)
  -- Fold the gradient-pairing summand per `b`.
  have hgradfold : tensorL2Inner (I := I) (M := M) g 0 (s + 1)
      (covGrad (I := I) (M := M) g 0 s P).toFun
      (covGrad (I := I) (M := M) g 0 s S).toFun =
      ∑ b : Fin N,
        ∫ x, tensorInnerScalar (I := I) (M := M) g 0 s
            (bochnerGradSlot0Cc (I := I) (M := M) g s P (hV b)).toSection
            (bochnerGradSlot0Cc (I := I) (M := M) g s S (hV b)).toSection x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) :=
    fold_assembly_perB (I := I) (M := M) g s S V hV hPar
      (covGrad (I := I) (M := M) g 0 s P)
      (fun b => bochnerGradSlot0Cc (I := I) (M := M) g s P (hV b))
      (fun b x => rfl)
  -- Fold the spectator summand per `b`.
  have hspecfold : tensorL2Inner (I := I) (M := M) g 0 (s + 1)
      (appCc (I := I) (M := M) g (s + 1) (s + 1)
        (slotExtend (I := I) (M := M) g s s Φ₀)
        (covGrad (I := I) (M := M) g 0 s S)).toFun
      (covGrad (I := I) (M := M) g 0 s S).toFun =
      ∑ b : Fin N,
        ∫ x, tensorInnerScalar (I := I) (M := M) g 0 s
            (appCc (I := I) (M := M) g s s Φ₀
              (bochnerGradSlot0Cc (I := I) (M := M) g s S (hV b))).toSection
            (bochnerGradSlot0Cc (I := I) (M := M) g s S (hV b)).toSection x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) :=
    fold_assembly_perB (I := I) (M := M) g s S V hV hPar
      (appCc (I := I) (M := M) g (s + 1) (s + 1)
        (slotExtend (I := I) (M := M) g s s Φ₀)
        (covGrad (I := I) (M := M) g 0 s S))
      (fun b => appCc (I := I) (M := M) g s s Φ₀
        (bochnerGradSlot0Cc (I := I) (M := M) g s S (hV b)))
      (fun b x => spectatorSlot0_eq_appCc_gradSlot (I := I) (M := M) g s S (hV b) x)
  -- Per-`b` IBP on the gradient pairing: `⟨∇_b P, ∇_b S⟩ = −⟨P, ∇_b(∇_b S)⟩ − ⟨P, ∇_b S⟩·div`.
  have hIBP : ∀ b : Fin N,
      (∫ x, tensorInnerScalar (I := I) (M := M) g 0 s
          (bochnerGradSlot0Cc (I := I) (M := M) g s P (hV b)).toSection
          (bochnerGradSlot0Cc (I := I) (M := M) g s S (hV b)).toSection x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g)) =
      - (∫ x, tensorInnerScalar (I := I) (M := M) g 0 s
          P.toSection (covApplyGenCc (I := I) (M := M) g s
            (bochnerGradSlot0Cc (I := I) (M := M) g s S (hV b)) (hV b)).toSection x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g)) -
      (∫ x, tensorInnerScalar (I := I) (M := M) g 0 s
          P.toSection (bochnerGradSlot0Cc (I := I) (M := M) g s S (hV b)).toSection x *
          DifferentialGeometry.Integral.DivergenceTheorem.divergence_g (I := I) g
            ⟨fun y : M => V b y, hV b⟩ x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g)) := by
    intro b
    have hcongr1 : (∫ x, tensorInnerScalar (I := I) (M := M) g 0 s
          (bochnerGradSlot0Cc (I := I) (M := M) g s P (hV b)).toSection
          (bochnerGradSlot0Cc (I := I) (M := M) g s S (hV b)).toSection x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g)) =
        (∫ x, tensorInnerScalar (I := I) (M := M) g 0 s
          (covApplyGenCc (I := I) (M := M) g s P (hV b)).toSection
          (bochnerGradSlot0Cc (I := I) (M := M) g s S (hV b)).toSection x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g)) := by
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
      rw [tensorInnerScalar_apply (I := I) (M := M) g 0 s,
        tensorInnerScalar_apply (I := I) (M := M) g 0 s]
      congr 1
      rw [bochnerGradSlot0Cc_toSection_apply (I := I) (M := M) g s P (hV b) x,
        bochnerGradSlot0_eq_covApply (I := I) (M := M) g s P (V b) x]
      rfl
    rw [hcongr1]
    exact integral_covApplyPair_IBP (I := I) (M := M) g s P
      (bochnerGradSlot0Cc (I := I) (M := M) g s S (hV b)) (hV b)
  -- Assemble.
  have hmain : tensorL2Inner (I := I) (M := M) g 0 (s + 1)
      (appCc (I := I) (M := M) g s (s + 1)
        (covGrad (I := I) (M := M) g s s Φ₀) S).toFun
      (covGrad (I := I) (M := M) g 0 s S).toFun =
      (∑ b : Fin N,
        ∫ x, tensorInnerScalar (I := I) (M := M) g 0 s
            (bochnerGradSlot0Cc (I := I) (M := M) g s P (hV b)).toSection
            (bochnerGradSlot0Cc (I := I) (M := M) g s S (hV b)).toSection x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g)) -
      (∑ b : Fin N,
        ∫ x, tensorInnerScalar (I := I) (M := M) g 0 s
            (appCc (I := I) (M := M) g s s Φ₀
              (bochnerGradSlot0Cc (I := I) (M := M) g s S (hV b))).toSection
            (bochnerGradSlot0Cc (I := I) (M := M) g s S (hV b)).toSection x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g)) := by
    rw [← hgradfold, ← hspecfold]
    linarith [hsplit]
  rw [hmain, Finset.sum_congr rfl (fun b _ => hIBP b)]
  rw [← Finset.sum_neg_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  ring

/-- **The swap-slot differentiated-curvature carrier (the second-Bianchi pivot).** The packaged smooth
`(0, s)`-tensor whose section value at `x` is the `tensor0SAsRS`-wrap of the differentiated
`(0, s)`-tensor curvature `nablaTensor0SCurv g s (V b)(V a)(V k) A x` (`A y := S.toSection y (unit)`),
with the **derivative direction `V b` in the gradient-pairing slot** and the antisymmetric pair
`(V a, V k)` in the curvature slots.  This is the slot-swapped sibling of the diagonal
`nablaDiffCurvTraceCc` carrier (derivative `V a`, pair `(V a, V b)`): the swap of the derivative slot
from the contracted direction to the gradient direction is exactly the content of the second
(differential) Bianchi identity `nablaTensor0SCurv_cyclic_eq_zero`. -/
private noncomputable def nablaCurvSwapCc (g : SmoothRiemannianMetric I M) (s : ℕ)
    (S : SmoothCcTensor g 0 s) {Vb Va Vk : Π b : M, TangentSpace I b}
    (hVb : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => (⟨b, Vb b⟩ : TotalSpace E (TangentSpace I))))
    (hVa : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => (⟨b, Va b⟩ : TotalSpace E (TangentSpace I))))
    (hVk : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => (⟨b, Vk b⟩ : TotalSpace E (TangentSpace I)))) : SmoothCcTensor g 0 s where
  toSection :=
    { toFun := fun x : M =>
        nablaRiemannSec (I := I) (LeviCivita (I := I) g) (tensorCov (I := I) g 0 s)
          Vb Va Vk (fun y : M => S.toSection y) x
      contMDiff_toFun := by
        have h1 : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 0 s ℝ E)) ∞
            (fun x : M => (⟨x, covApply (tensorCov (I := I) g 0 s) Vb
              (fun y : M => riemannSec (tensorCov (I := I) g 0 s) Va Vk
                (fun z : M => S.toSection z) y) x⟩ :
              TotalSpace (TensorRSModel 0 s ℝ E) (fun z : M => TensorRSSpace 0 s I z))) :=
          covApply_contMDiff (cov := tensorCov (I := I) g 0 s) hVb
            (riemannSec_contMDiff (cov := tensorCov (I := I) g 0 s) hVa hVk
              S.toSection.contMDiff)
        have h2 : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 0 s ℝ E)) ∞
            (fun x : M => (⟨x, riemannSec (tensorCov (I := I) g 0 s)
              (covApply (LeviCivita (I := I) g) Vb Va) Vk
              (fun z : M => S.toSection z) x⟩ :
              TotalSpace (TensorRSModel 0 s ℝ E) (fun z : M => TensorRSSpace 0 s I z))) :=
          riemannSec_contMDiff (cov := tensorCov (I := I) g 0 s)
            (covApply_contMDiff (cov := LeviCivita (I := I) g) hVb hVa) hVk
            S.toSection.contMDiff
        have h3 : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 0 s ℝ E)) ∞
            (fun x : M => (⟨x, riemannSec (tensorCov (I := I) g 0 s) Va
              (covApply (LeviCivita (I := I) g) Vb Vk)
              (fun z : M => S.toSection z) x⟩ :
              TotalSpace (TensorRSModel 0 s ℝ E) (fun z : M => TensorRSSpace 0 s I z))) :=
          riemannSec_contMDiff (cov := tensorCov (I := I) g 0 s) hVa
            (covApply_contMDiff (cov := LeviCivita (I := I) g) hVb hVk)
            S.toSection.contMDiff
        have h4 : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 0 s ℝ E)) ∞
            (fun x : M => (⟨x, riemannSec (tensorCov (I := I) g 0 s) Va Vk
              (covApply (tensorCov (I := I) g 0 s) Vb (fun y : M => S.toSection y)) x⟩ :
              TotalSpace (TensorRSModel 0 s ℝ E) (fun z : M => TensorRSSpace 0 s I z))) :=
          riemannSec_contMDiff (cov := tensorCov (I := I) g 0 s) hVa hVk
            (covApply_contMDiff (cov := tensorCov (I := I) g 0 s) hVb S.toSection.contMDiff)
        refine (((h1.sub_section h2).sub_section h3).sub_section h4).congr (fun x => ?_)
        rw [nablaRiemannSec_def]
        rfl }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

set_option linter.unusedSectionVars false in
/-- **The rank-`s` Parseval reduction of the three-term normal form to the second-Bianchi cross
pairing (genuine leaf — the algebraic Parseval expansion).** For a fixed smooth Parseval frame
family, the frame sum of the operator-field three-term normal form
`∑_b ∫ [⟨P, ∇_b(∇_b S)⟩ + ⟨P, ∇_b S⟩·divᵍ V_b + ⟨Φ₀(∇_b S), ∇_b S⟩]` (`P := appCc Φ₀ S`,
`Φ₀ := curvOpField g s`) equals the negated frame-summed second-Bianchi cross pairing
`−∑_a ∑_b ∑_k ∫ ⟨(∇_{V b} R^{(s)})(V a, V k) S, curry_{V k}(∇_{V b} S)⟩` built on the swap-slot
carrier `nablaCurvSwapCc` (derivative `V b`, curvature pair `(V a, V k)`), the slot-`k` read of the
directional gradient `∇_{V b} S`.  Expand the order-`0` curvature trace `P = appCc Φ₀ S =
pureRGenuineDiffOp g 0 s S` through the moving-frame value bridge
(`pureRGenuineDiffOp_zero_succ_toSection_unit_eval`, `parseval_family_sum_bilin_eq`), the curry-Leibniz
law (`tensorCovDerivAt_curryCc_eq`), the cometric-parallel pair antisymmetry
(`parsevalFrame_sum_bilin_covDeriv_pair_antisymm`), and the divergence/tension Parseval covariant trace
(`divergence_g_eq_parsevalFrame_trace`); the frame and tension corrections cancel after the full
Parseval `(a, k)` double sum.  It degenerates correctly at `s = 0` (the scalar bundle carries no
curvature, both sides `0`). -/
private theorem pureRGenuineDiffOp_pairing_eq_parseval_curry_sum
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s)
    {N : ℕ} (V : Fin N → Π b : M, TangentSpace I b)
    (hV : ∀ a, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => (⟨b, V a b⟩ : TotalSpace E (TangentSpace I))))
    (hPar : ∀ (x : M) (u : TangentSpace I x),
      (∑ a : Fin N, g.inner x (V a x) u • V a x) = u) :
    (∑ b : Fin N,
        ((∫ x, tensorInnerScalar (I := I) (M := M) g 0 s
            (appCc (I := I) (M := M) g s s (curvOpField (I := I) (M := M) g s) S).toSection
            (covApplyGenCc (I := I) (M := M) g s
              (bochnerGradSlot0Cc (I := I) (M := M) g s S (hV b)) (hV b)).toSection x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g)) +
        (∫ x, tensorInnerScalar (I := I) (M := M) g 0 s
            (appCc (I := I) (M := M) g s s (curvOpField (I := I) (M := M) g s) S).toSection
            (bochnerGradSlot0Cc (I := I) (M := M) g s S (hV b)).toSection x *
            DifferentialGeometry.Integral.DivergenceTheorem.divergence_g (I := I) g
              ⟨fun y : M => V b y, hV b⟩ x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g)) +
        (∫ x, tensorInnerScalar (I := I) (M := M) g 0 s
            (appCc (I := I) (M := M) g s s (curvOpField (I := I) (M := M) g s)
              (bochnerGradSlot0Cc (I := I) (M := M) g s S (hV b))).toSection
            (bochnerGradSlot0Cc (I := I) (M := M) g s S (hV b)).toSection x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g)))) =
      - (∑ a : Fin N, ∑ b : Fin N, ∑ k : Fin N,
          ∫ x, tensorInnerScalar (I := I) (M := M) g 0 s
              (nablaCurvSwapCc (I := I) (M := M) g s S (hV b) (hV a) (hV k)).toSection
              (bochnerGradSlot0Cc (I := I) (M := M) g s
                (bochnerGradSlot0Cc (I := I) (M := M) g s S (hV b)) (hV k)).toSection x
            ∂(riemannianVolumeMeasure (I := I) (M := M) g)) := by
  sorry

set_option linter.unusedSectionVars false in
/-- **The frame-summed second-Bianchi cross-pairing emission (genuine leaf — the headline Bianchi
content).** For a fixed smooth Parseval frame family, the frame sum of the swap-slot
differentiated-curvature cross pairing
`∑_a ∑_b ∑_k ∫ ⟨(∇_{V b} R^{(s)})(V a, V k) S, curry_{V k}(∇_{V b} S)⟩` equals the negated genuine
curvature/Hessian cross pairing
`−I₂ = −∑_a ∑_b ∫ ⟨R(V a, V b) S, ∇²_{V a, V b} S⟩`.  This is the genuine second (differential)
Bianchi emission: the cyclic vanishing `nablaTensor0SCurv_cyclic_eq_zero` rewrites the swap-slot
derivative `(∇_{V b} R)(V a, V k)` as `−(∇_{V a} R)(V k, V b) − (∇_{V k} R)(V b, V a)`, and the
per-direction covariant integration by parts together with the residue/Hessian Christoffel correction
(`residue_add_crossHessian_pointwise_eq`) and the Parseval covariant-derivative antisymmetries collapse
the frame triple sum to `−I₂` over the closed manifold. -/
private theorem parsevalFrameSum_bianchiCross_eq_neg_crossPairing
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s)
    {N : ℕ} (V : Fin N → Π b : M, TangentSpace I b)
    (hV : ∀ a, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => (⟨b, V a b⟩ : TotalSpace E (TangentSpace I))))
    (hPar : ∀ (x : M) (u : TangentSpace I x),
      (∑ a : Fin N, g.inner x (V a x) u • V a x) = u) :
    (∑ a : Fin N, ∑ b : Fin N, ∑ k : Fin N,
        ∫ x, tensorInnerScalar (I := I) (M := M) g 0 s
            (nablaCurvSwapCc (I := I) (M := M) g s S (hV b) (hV a) (hV k)).toSection
            (bochnerGradSlot0Cc (I := I) (M := M) g s
              (bochnerGradSlot0Cc (I := I) (M := M) g s S (hV b)) (hV k)).toSection x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g)) =
      - (∑ a : Fin N, ∑ b : Fin N,
          ∫ x, tensorInnerScalar (I := I) (M := M) g 0 s
              (riemannSecCc (I := I) (M := M) g s S (hV a) (hV b)).toSection
              (crossHessianCc (I := I) (M := M) g s S (hV a) (hV b)).toSection x
            ∂(riemannianVolumeMeasure (I := I) (M := M) g)) := by
  sorry

set_option linter.unusedSectionVars false in
/-- **The differentiated-curvature operator-field identification (posited primitive): the frame-free
operator-field pairing is the gauge-cancelling difference `G₄ − I₂`.**  For a fixed smooth Parseval
frame family `V a`, the global metric `L²` pairing of the differentiated-curvature operator-field
section `appCc (covGrad Φ₀) S` (`Φ₀ := curvOpField g s`, definitionally `genuineDiffCurvSection g s
S`, the `(∇R) S` trace) against `∇S := covGrad g 0 s S` equals the group-`4` double sum minus the
curvature/Hessian cross pairing:
```
⟨appCc (covGrad Φ₀) S, ∇S⟩_{L²} = G₄ − I₂,
I₂ := ∑_a ∑_b ∫ ⟨R(V a, V b) S, ∇²_{V a, V b} S⟩,
```
with `I₂` built on the **genuine Hessian** carrier `crossHessianCc` (`tensorSecondCovDeriv`,
tensorial in both direction slots).  The former iterated-derivative form (`secondCovApplyCc`,
`∇_{V a}(∇_{V b} S)`) was numerically REFUTED: its `I₂` is frame-variant by the missing
`∇_{∇_{V a} V b} S` correction, while this Hessian-based identity holds to `≤ 4e-15` in dims
`2` and `3`.

**Why this combination is admissible (not in the refuted per-group family).**  The left side is
frame-free, and by the summed chain endpoint
`parsevalFrameSum_group4_sub_crossPairing_eq_curv_sub_gcurv_sub_ricTrace` (sorry-free over the
proven primitive `D = −(G₁ + I₂)`) the right side equals the frame-free value `⟨Curv S, ∇S⟩ −
⟨GcurvSection, ∇S⟩ − ⟨ricTraceSection, ∇S⟩` — the gauge variations of `G₄` and `I₂` cancel inside
the difference, unlike the dim-≥-3-refuted per-group value assignments (`G₃ = ⟨ricTrace, ∇S⟩`,
`G₂ + G₄ = operator residue`; `PROVE_REFUTED.md`, "Kernel per-group VALUE-ASSIGNMENT family"),
which this statement does not transit.

**Route for the genuine proof (the body is an honest `sorry`; two reductions are PROVEN above).**
Two of the three legs are landed sorry-free in this file: the group-`4` fold vanishes outright
(`bochnerFoldGroupSum_elt4_eq_zero` — the genuine Hessian is value-bilinear in its direction
slots by `tensorSecondCovDeriv_unit_eq_twoSlotCurry`, so the cometric-parallel pair antisymmetry
kills the `a`-sum pointwise), and the left side reduces by the B-rule split and the per-direction
covariant IBP to the three-term normal form
`tensorL2Inner_genuineDiffCurv_covGrad_eq_neg_threeTerm`,
`LHS = −∑_b ∫ [⟨P, ∇_b(∇_b S)⟩ + ⟨P, ∇_b S⟩·divᵍ V_b + ⟨Φ₀(∇_b S), ∇_b S⟩]` with
`P := appCc Φ₀ S`.  The remaining content is the single integrated identity
`∑_b ∫ [⟨P, ∇_b∇_b S⟩ + ⟨P, ∇_b S⟩·divᵍ V_b + ⟨Φ₀(∇_b S), ∇_b S⟩] = I₂`: expand the `Φ₀`-pairings
through the rank-`s` Parseval value bridge (`pureRGenuineDiffOp_zero_succ_toSection_unit_eval` +
`parseval_family_sum_bilin_eq`, mirroring `gcurv_slot0_eq_parseval_sum_elt1` one rank down), apply
the curry-Leibniz law (`tensorCovDerivAt_curryCc_eq`), the cometric antisymmetry
(`parsevalFrame_sum_bilin_covDeriv_pair_antisymm`), and the tension/divergence kill
`∑_k [∇_{V_k} V_k + (divᵍ V_k)·V_k] = 0`, reducing to the integrated second-Bianchi cross
pairing `∑_{a,b,k} ∫ ⟨(∇_{V_b} R̃)(V_a, V_k)(curry_{V_a} S), curry_{V_k}(∇_{V_b} S)⟩ = −I₂`
(`R̃` the rank-`(s−1)` curvature endomorphism), which is the contracted-Bianchi emission
(`nablaTensor0SCurv_cyclic_eq_zero` + the per-direction IBP) — the same covariant-IBP genre as
the `D`-primitive, numerically consistent with it through the chain endpoint.  Consumers (the
frame-free corollary below, and through it the three-section curvature value of
`MovingFrameRemainderFrameSumBridge`) transitively depend on its `sorryAx`. -/
private theorem tensorL2Inner_genuineDiffCurv_covGrad_eq_group4_sub_crossPairing
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s)
    {N : ℕ} (V : Fin N → Π b : M, TangentSpace I b)
    (hV : ∀ a, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => (⟨b, V a b⟩ : TotalSpace E (TangentSpace I))))
    (hPar : ∀ (x : M) (u : TangentSpace I x),
      (∑ a : Fin N, g.inner x (V a x) u • V a x) = u) :
    tensorL2Inner (I := I) (M := M) g 0 (s + 1)
        (appCc (I := I) (M := M) g s (s + 1)
          (covGrad (I := I) (M := M) g s s (curvOpField (I := I) (M := M) g s)) S).toFun
        (covGrad (I := I) (M := M) g 0 s S).toFun =
      bochnerFoldGroupSum (I := I) (M := M) g s S V
          (bochnerGroupElt4 (I := I) (M := M) g s S) -
        (∑ a : Fin N, ∑ b : Fin N,
          ∫ x, tensorInnerScalar (I := I) (M := M) g 0 s
              (riemannSecCc (I := I) (M := M) g s S (hV a) (hV b)).toSection
              (crossHessianCc (I := I) (M := M) g s S (hV a) (hV b)).toSection x
            ∂(riemannianVolumeMeasure (I := I) (M := M) g)) := by
  classical
  have h3term := tensorL2Inner_genuineDiffCurv_covGrad_eq_neg_threeTerm
    (I := I) (M := M) g s S V hV hPar
  have hG4 := bochnerFoldGroupSum_elt4_eq_zero (I := I) (M := M) g s S V hV hPar
  have hC1 := pureRGenuineDiffOp_pairing_eq_parseval_curry_sum
    (I := I) (M := M) g s S V hV hPar
  have hC2 := parsevalFrameSum_bianchiCross_eq_neg_crossPairing
    (I := I) (M := M) g s S V hV hPar
  rw [hG4]
  linarith [h3term, hC1, hC2]

/-- **The frame-free differentiated-curvature pairing value: `⟨(∇R) S, ∇S⟩ = ⟨Curv S, ∇S⟩ −
⟨GcurvSection, ∇S⟩ − ⟨ricTraceSection, ∇S⟩` (sorry-free glue over the operator-field posit).**
The global metric `L²` pairing of the differentiated-curvature operator-field section
`appCc (covGrad Φ₀) S` (`Φ₀ := curvOpField g s`) against `∇S := covGrad g 0 s S` equals the
curvature cross-pairing minus the pure-Riemann and leading-slot Ricci traces:
```
⟨appCc (covGrad Φ₀) S, ∇S⟩_{L²}
  = ⟨pointwiseTensorCurv g s S, ∇S⟩_{L²} − ⟨GcurvSection g s S, ∇S⟩_{L²}
      − ⟨ricTraceSection g s S, ∇S⟩_{L²}.
```

Both sides are frame-free; the proof passes through a Parseval frame family witness
(`exists_smooth_parseval_frame_family`): the posited operator-field identification
`tensorL2Inner_genuineDiffCurv_covGrad_eq_group4_sub_crossPairing` reads the left side as the
gauge-cancelling difference `G₄ − I₂`, and the summed chain endpoint
`parsevalFrameSum_group4_sub_crossPairing_eq_curv_sub_gcurv_sub_ricTrace` (sorry-free over the
`D = −(G₁ + I₂)` primitive) evaluates that difference to the right side.  No per-group value
assignment is transited.  Consumers (the three-section curvature value
`bochnerWeitzenbock_threeSection_curvatureValue_posit` of `MovingFrameRemainderFrameSumBridge`)
transitively depend on the operator-field posit's `sorryAx`. -/
theorem tensorL2Inner_genuineDiffCurv_covGrad_eq_curv_sub_gcurv_sub_ricTrace
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) :
    tensorL2Inner (I := I) (M := M) g 0 (s + 1)
        (appCc (I := I) (M := M) g s (s + 1)
          (covGrad (I := I) (M := M) g s s (curvOpField (I := I) (M := M) g s)) S).toFun
        (covGrad (I := I) (M := M) g 0 s S).toFun =
      tensorL2Inner (I := I) (M := M) g 0 (s + 1)
          (pointwiseTensorCurv (I := I) (M := M) g s S).toFun
          (covGrad (I := I) (M := M) g 0 s S).toFun -
        tensorL2Inner (I := I) (M := M) g 0 (s + 1)
          (GcurvSection (I := I) (M := M) g s S).toFun
          (covGrad (I := I) (M := M) g 0 s S).toFun -
        tensorL2Inner (I := I) (M := M) g 0 (s + 1)
          (ricTraceSection (I := I) (M := M) g s S).toFun
          (covGrad (I := I) (M := M) g 0 s S).toFun := by
  classical
  obtain ⟨N, V, hV, hPar⟩ := exists_smooth_parseval_frame_family (I := I) (M := M) g
  have hOp := tensorL2Inner_genuineDiffCurv_covGrad_eq_group4_sub_crossPairing
    (I := I) (M := M) g s S V hV hPar
  have hChain := parsevalFrameSum_group4_sub_crossPairing_eq_curv_sub_gcurv_sub_ricTrace
    (I := I) (M := M) g s S V hV hPar
  linarith [hOp, hChain]

end Connection
end Integral
end DifferentialGeometry

end
