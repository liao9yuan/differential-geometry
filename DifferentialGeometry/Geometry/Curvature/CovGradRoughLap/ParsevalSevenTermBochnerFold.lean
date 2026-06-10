import DifferentialGeometry.Geometry.Connection.TensorNabla.OperatorFieldCovariantCalculus
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.FixedFieldThirdOrderCommutator
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.GradientSlotCurvatureSplit
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.BracketDivergenceForm
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.FrozenFramePureRCurvatureTower
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.RicciTraceCarrier
import DifferentialGeometry.Geometry.Curvature.FiberNormParseval.ParsevalLaplacianSlot0Expansion
import DifferentialGeometry.Geometry.Curvature.FiberNormParseval.ParsevalFrameField
import DifferentialGeometry.Geometry.Curvature.Bochner.PointwiseTensorBochner
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.GreenIdentityAndIBP.TensorConnLapGreenIntertwiner
import DifferentialGeometry.Geometry.Curvature.Order2Defect.GradientSlotLeibniz
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.OperatorFieldPairingIBP
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.ContractedBianchi
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.DifferentiatedSlotwiseCurvature
import DifferentialGeometry.Geometry.Connection.MetricCompatibility.TensorRSMetricCompatible

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
over the Parseval family `(a, b)` partitions those seven terms into four named carrier groups, each of which
evaluates to a concrete frame-free `L²` pairing (or to `0`):

* `bochnerFoldGroupSum1` (term i, `R(V a, V b)(∇_{V a} S)`) → the pure-Riemann gradient-field curvature
  bilinear `⟨pureRGenuineDiffOp g 0 (s + 1) (∇S), ∇S⟩_{L²}`;
* `bochnerFoldGroupSum3` (terms iii + iv − v) → the leading-slot Ricci-trace pairing
  `⟨ricTraceSection g s S, ∇S⟩_{L²}`;
* `bochnerFoldGroupSum2 + bochnerFoldGroupSum4` (term ii together with − term vi − term vii) → the
  operator-field integration-by-parts residue `−⟨appCc (slotExtend Φ₀) (∇S), ∇S⟩_{L²} +
  ⟨∇(pureRGenuineDiffOp g 0 s S), ∇S⟩_{L²}`.  The group-`2` summand `∇_{V a}(R(V a, V b) S)` does **not**
  vanish on its own: its `V a`-divergence has a nonzero residual, because the fixed Parseval frame is not
  pointwise covariantly divergence-free, so the single-slot divergence engine
  (`integral_tensorInner_covDeriv_combined_eq_zero`) only kills the *combined* three-term
  `∫(⟨∇_V W', Z⟩ + ⟨W', ∇_V Z⟩ + ⟨W', Z⟩ div_g V)`.  That combined residual is exactly the
  `−(⟨W', ∇_V Z⟩ + ⟨W', Z⟩ div_g V)` absorbed by the operator-field B-rule of the symmetric second-order
  pair (group `4`), so only the **combined** group-`2` + group-`4` value is the sound carrier-free residue.

The fifth fold `bochnerFold_sevenTermSum_eq_pointwiseTensorCurvPairing` is the fixed-Parseval-family bridge:
the sum of the four group double-sums equals the curvature cross-pairing `⟨pointwiseTensorCurv g s S, ∇S⟩_{L²}`
(through the rough-Laplacian Parseval trace `rawTensorConnLapSmooth_toSection_eq_parseval_secondCovDeriv_sum`,
the slot-`0` fibre Parseval expansion `tensorInnerPointwise_succ_eq_parseval_sum_slot0`, and the seven-term
carrier identity).

The four folds (`bochnerFold_group1_eq_GcurvSection`, `bochnerFold_group3_eq_ricTrace`,
`bochnerFold_group2_add_group4_eq_operatorResidue`, `bochnerFold_sevenTermSum_eq_pointwiseTensorCurvPairing`)
and the integrated extraction `parsevalFrameSum_integratedBochnerExtraction` are all assembled by glue (the
unified fold-`L²` assembly `fold_assembly`, the frame-summed covariant integration by parts
`bochnerFoldGroupSum_elt2_eq_residueSum`, the operator-field pairing split B-rule
`tensorL2Inner_covGrad_appCc_eq_add`, and the Parseval slot-`0` carrier split `bochnerSlot0Curv_eq_groupSum`).
The two genuine more-primitive curvature sub-identities of the rank-`0` Bochner deep root — the only `sorry`
bodies in this file — are the named Parseval-frame curvature bridges
`parsevalFrameTrace_ricSlot0_eq_sum_elt3` (the Bochner–Lichnerowicz Ricci / second-Bianchi frame-trace
slot-`0` identity, ATOM A's child) and `parsevalFrameSum_group2Residue_add_group4_eq_appCc_covGrad_curvOpField_BRIDGE`
(the differentiated-curvature operator-field action of the group-`2` IBP residue plus the group-`4`
second-order pair, ATOM B's child).  Both are GENERAL Parseval-frame curvature content that should be promoted
to a curvature file.  The integrated nullity `movingFrameNullity_diffCurvOpField_leaf`
(`DifferentiatedCurvatureOperatorFieldIdentification`) assembles over the folds; consumers transitively depend
on the two bridges' `sorryAx`.
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

/-- **The frame-free curvature operator field `Φ₀ s`.** The fixed smooth `(s, s)`-operator field whose
operator-field action recovers the order-`0` moving-frame pure-Riemann curvature endomorphism
`pureRGenuineDiffOp g 0 s W = appCc (Φ₀ s) W` (`exists_pureRGenuineDiffOp_base_appCc`); its fibre value
is the genuine `g`-metric curvature trace `W ↦ ∑ᵢ R(Bᵢ, ·) W`, frame-free (built from `g, R` alone). It
is the curvature coefficient whose covariant derivative carries the differentiated-curvature `(∇R)`
content. It is a pure `Classical.choose` definition (no downstream dependency), homed at the most-upstream
curvature node so the curvature line shares it. -/
noncomputable def curvOpField (g : SmoothRiemannianMetric I M) (s : ℕ) :
    SmoothCcTensor g (s + 0) (s + 0) :=
  (Classical.choose (exists_pureRGenuineDiffOp_base_appCc (I := I) (M := M) g)) s

/-- **The order-`0` curvature operator base spec for `curvOpField`.** The defining `Classical.choose`
specification: the operator-field action of the frame-free curvature operator field `Φ₀ s := curvOpField
g s` on a smooth compactly-supported `(0, s)`-tensor `S` recovers the order-`0` moving-frame pure-Riemann
curvature trace `pureRGenuineDiffOp g 0 s S`. This is the identity through which the differentiated
operator field `covGrad (Φ₀ s)` and its passenger-slot extension `slotExtend (Φ₀ s)` are identified with
the curvature-derivative content. -/
theorem appCc_curvOpField_eq_pureRGenuineDiffOp
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) :
    appCc (I := I) (M := M) g (s + 0) (s + 0) (curvOpField (I := I) (M := M) g s) S =
      pureRGenuineDiffOp (I := I) (M := M) g 0 s S :=
  (Classical.choose_spec (exists_pureRGenuineDiffOp_base_appCc (I := I) (M := M) g) s S).symm

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

/-- **The Parseval-frame Ricci-trace slot-`0` identity (the genuine Bochner–Lichnerowicz Ricci /
second-Bianchi frame-trace bridge).** For a fixed Parseval frame family `V a`, the slot-`0` `V b`-read of
the leading-slot Ricci-trace carrier `ricTraceSection g s S` is the Parseval-family sum over `a` of the
group-`3` carrier `R(∇_{V a} V b, V a) S + R(V b, ∇_{V a} V a) S − ∇_{R(V a, V b) V a} S`
(`bochnerGroupElt3`):
```
tensor0SAsRS x (slot0_{V b}(ricTraceSection g s S)(x)) = ∑_a bochnerGroupElt3 g s S (V a) (V b) x.
```

This is the genuine more-primitive Bochner–Lichnerowicz **Ricci** content of the group-`3` fold (`ATOM A`'s
deep child).  It is the Parseval-frame version of the orthonormal frame-trace second Bianchi: commuting the
leading gradient slot of `∇S` past the rough-Laplacian trace slots by the Ricci identity, the carrier whose
curvature derivative slot is summed over the frame folds — through the tensor-bundle second Bianchi
(`nablaTensor0SCurv_cyclic_eq_zero`, frame-independent), its frame-sum slot transfer
(`frame_sum_nablaTensor0SCurv_baseSlot_eval`), the frame-trace Ricci fold
(`nablaTensorCurv_frame_trace_eq_nablaRicci`), and the contracted second Bianchi
(`contracted_second_bianchi`), all converted from the orthonormal frame to the fixed Parseval family by the
bilinear trace identity `parseval_family_sum_bilin_eq` (the trace `∑_a R(V_a, ·)V_a = Ric` holds for *any*
Parseval frame because `∑_a V_a ⊗ V_a = g⁻¹`) — into the raised Ricci endomorphism's slot precomposition,
which is exactly `ricSlotOpFib` (`ricSlotOpFib_apply_eval`, `ricTraceSection_toSection`).  It is *false* for
an arbitrary carrier (the `s = 0` Bochner–Lichnerowicz litmus `∫ Ric(∇f, ∇f) = ‖Δ_∇ f‖² − ‖∇²f‖²` is nonzero
on a non-flat manifold), so it genuinely uses `R`, `Ric`, the Parseval reproduction `hPar`, and the
second-order frame structure.  The body is `sorry`; it is GENERAL Parseval-frame curvature content that
should be promoted to a curvature file.  Consumers transitively depend on its `sorryAx`. -/
private theorem parsevalFrameTrace_ricSlot0_eq_sum_elt3
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s)
    {N : ℕ} (V : Fin N → Π b : M, TangentSpace I b)
    (hV : ∀ a, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => (⟨b, V a b⟩ : TotalSpace E (TangentSpace I))))
    (hPar : ∀ (x : M) (u : TangentSpace I x),
      (∑ a : Fin N, g.inner x (V a x) u • V a x) = u) (b : Fin N) (x : M) :
    tensor0SAsRS (I := I) (M := M) x
        ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
            (ricTraceSection (I := I) (M := M) g s S).toSection x)
            (unitZeroSec (I := I) (M := M) x))) (V b x)) =
      ∑ a : Fin N, bochnerGroupElt3 (I := I) (M := M) g s S (V a) (V b) x :=
  sorry

/-- **The group-`3` Ricci-trace fold (terms iii + iv − v → leading-slot Ricci trace).** For a fixed
Parseval frame family, the group-`3` double sum equals the `L²` pairing of the leading-slot Ricci-trace
carrier `ricTraceSection g s S` against `∇S`:
```
bochnerFoldGroupSum g s S V (bochnerGroupElt3) = ⟨ricTraceSection g s S, ∇S⟩_{L²}.
```
Assembled by the unified fold-`L²` assembly `fold_assembly` (`Named := ricTraceSection g s S`,
`Elt := bochnerGroupElt3`) over the genuine more-primitive Parseval-frame Ricci-trace slot-`0` identity
`parsevalFrameTrace_ricSlot0_eq_sum_elt3` (the Bochner–Lichnerowicz Ricci / second-Bianchi frame-trace
content) and the carrier cross-integrability; consumers transitively depend on that identity's `sorryAx`. -/
private theorem bochnerFoldGroupSum_elt3_eq_ricTraceSection
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s)
    {N : ℕ} (V : Fin N → Π b : M, TangentSpace I b)
    (hV : ∀ a, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => (⟨b, V a b⟩ : TotalSpace E (TangentSpace I))))
    (hPar : ∀ (x : M) (u : TangentSpace I x),
      (∑ a : Fin N, g.inner x (V a x) u • V a x) = u) :
    bochnerFoldGroupSum (I := I) (M := M) g s S V
        (bochnerGroupElt3 (I := I) (M := M) g s S) =
      tensorL2Inner (I := I) (M := M) g 0 (s + 1)
        (ricTraceSection (I := I) (M := M) g s S).toFun
        (covGrad (I := I) (M := M) g 0 s S).toFun :=
  (fold_assembly (I := I) (M := M) g s S V hV hPar (ricTraceSection (I := I) (M := M) g s S)
    (bochnerGroupElt3 (I := I) (M := M) g s S)
    (fun b x => parsevalFrameTrace_ricSlot0_eq_sum_elt3 (I := I) (M := M) g s S V hV hPar b x)
    (fun a b => by
      have hib := SmoothCcTensor.integrable_inner_cross (I := I) (M := M)
        (bochnerGroupElt3Cc (I := I) (M := M) g s S (hV a) (hV b))
        (bochnerGradSlot0Cc (I := I) (M := M) g s S (hV b))
      refine hib.congr (Filter.Eventually.of_forall (fun x => ?_))
      simp only [SmoothCcTensor.toFun_apply,
        bochnerGroupElt3Cc_toSection_eq (I := I) (M := M) g s S (hV a) (hV b) x,
        bochnerGradSlot0Cc_toSection_apply (I := I) (M := M) g s S (hV b) x])).symm

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

/-- **The group-`2` IBP residue plus group-`4` second-order pair equals the differentiated-curvature
operator-field action (the genuine `∇R`-trace leaf, compact operator-field form).** For a fixed Parseval
frame family, the frame double sum of the group-`2` integration-by-parts residue `bochnerGroup2Residue`
(`= −(⟨R(V a, V b) S, ∇_{V a}(∇_{V b} S)⟩ + ⟨R(V a, V b) S, ∇_{V b} S⟩ · divᵍ (V a))`) plus the group-`4`
double sum (the symmetric second-order pair `−∇²_{∇_{V b} V a, V a} S − ∇²_{V a, ∇_{V b} V a} S` read
against `∇_{V b} S`) equals the single `L²` pairing of the differentiated curvature operator-field action
`appCc (covGrad Φ₀) S` of the frame-free curvature operator field `Φ₀ := curvOpField g s` against `∇S`:
```
(∑_b ∑_a ∫ bochnerGroup2Residue) + bochnerFoldGroupSum g s S V (bochnerGroupElt4)
  = ⟨appCc (covGrad (curvOpField g s)) S, ∇S⟩_{L²}.
```

This is the genuinely-deep `∇R`-trace content of the rank-`0` Bochner divergence root, in the compact
differentiated-curvature operator-field form (the genuine curvature-commutator leaf, *more primitive* than
its B-rule expansion `parsevalFrameSum_group2Residue_add_group4_eq_diffCurvTracePairing`, which transits it
through the operator-field pairing split `tensorL2Inner_covGrad_appCc_eq_add`).  The group-`2` covariant
derivative `∇_{V a}(·)` has already been integrated by parts off into the residue `bochnerGroup2Residue` by
the frame-summed engine (`bochnerFoldGroupSum_elt2_eq_residueSum`,
`integral_frameSummed_covDeriv_combined_eq_zero`); what remains is the genuine curvature-commutator
reorganization, *strictly closer to the tensor-bundle bedrock*: the residue's second covariant derivative
`∇_{V a}(∇_{V b} S)`, paired against `R(V a, V b) S`, plus the group-`4` symmetric pair, is reorganized
through the section-level Ricci identity `tensorSecondCovDeriv_antisymm_eq_riemannOp` and the frame-summed
differentiated tensor curvature transfer `frame_sum_nablaTensor0SCurv_baseSlot_eval` (the frame-independent
second Bianchi `nablaTensor0SCurv_cyclic_eq_zero` traced against the Parseval frame
`parseval_family_sum_bilin_eq`, `∑_a V_a ⊗ V_a = g⁻¹`) into the differentiated curvature coefficient
`(∇R) S = appCc (covGrad Φ₀) S` (`appCc_curvOpField_eq_pureRGenuineDiffOp`,
`nablaTensor0SCurv_apply_eval`).  It is *false* for an arbitrary section in place of the differentiated
curvature trace (the `(∇R) S` content is genuinely present), so it genuinely uses `R`, `∇R`, the Parseval
reproduction `hPar`, and the second-order frame structure.  The body is `sorry`; it is GENERAL
Parseval-frame curvature content that should be promoted to a curvature file.  Consumers transitively depend
on its `sorryAx`. -/
private theorem parsevalFrameSum_group2Residue_add_group4_eq_appCc_covGrad_curvOpField_BRIDGE
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s)
    {N : ℕ} (V : Fin N → Π b : M, TangentSpace I b)
    (hV : ∀ a, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => (⟨b, V a b⟩ : TotalSpace E (TangentSpace I))))
    (hPar : ∀ (x : M) (u : TangentSpace I x),
      (∑ a : Fin N, g.inner x (V a x) u • V a x) = u) :
    (∑ b : Fin N, ∑ a : Fin N,
        ∫ x, bochnerGroup2Residue (I := I) (M := M) g s S (V a) (V b)
            ⟨fun y : M => V a y, hV a⟩ x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g)) +
      bochnerFoldGroupSum (I := I) (M := M) g s S V
        (bochnerGroupElt4 (I := I) (M := M) g s S) =
      tensorL2Inner (I := I) (M := M) g 0 (s + 1)
        (appCc (I := I) (M := M) g s (s + 1)
          (covGrad (I := I) (M := M) g s s (curvOpField (I := I) (M := M) g s)) S).toFun
        (covGrad (I := I) (M := M) g 0 s S).toFun :=
  sorry

/-- **The differentiated-curvature reorganization, pre-split into the two operator-field pairings (the
B-rule normal form).** For a fixed Parseval frame family,
```
(∑_b ∑_a ∫ bochnerGroup2Residue) + bochnerFoldGroupSum g s S V (bochnerGroupElt4)
  = ⟨∇(pureRGenuineDiffOp g 0 s S), ∇S⟩_{L²} − ⟨appCc (slotExtend Φ₀) (∇S), ∇S⟩_{L²},   Φ₀ := curvOpField g s.
```
Assembled over the genuine more-primitive compact operator-field leaf
`parsevalFrameSum_group2Residue_add_group4_eq_appCc_covGrad_curvOpField_BRIDGE`
(`= ⟨appCc (covGrad Φ₀) S, ∇S⟩_{L²}`) by the operator-field pairing split (the B-rule)
`tensorL2Inner_covGrad_appCc_eq_add` (`Φ := Φ₀`, `W := S`, `T := ∇S`), whose left summand is the
differentiated-action pairing and whose order-`0` action `appCc Φ₀ S = pureRGenuineDiffOp g 0 s S`
(`appCc_curvOpField_eq_pureRGenuineDiffOp`) supplies the gradient-of-base term; rearranging isolates the
passenger-slot pairing on the right.  Consumers transitively depend on the compact leaf's `sorryAx`. -/
private theorem parsevalFrameSum_group2Residue_add_group4_eq_diffCurvTracePairing
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s)
    {N : ℕ} (V : Fin N → Π b : M, TangentSpace I b)
    (hV : ∀ a, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => (⟨b, V a b⟩ : TotalSpace E (TangentSpace I))))
    (hPar : ∀ (x : M) (u : TangentSpace I x),
      (∑ a : Fin N, g.inner x (V a x) u • V a x) = u) :
    (∑ b : Fin N, ∑ a : Fin N,
        ∫ x, bochnerGroup2Residue (I := I) (M := M) g s S (V a) (V b)
            ⟨fun y : M => V a y, hV a⟩ x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g)) +
      bochnerFoldGroupSum (I := I) (M := M) g s S V
        (bochnerGroupElt4 (I := I) (M := M) g s S) =
      tensorL2Inner (I := I) (M := M) g 0 (s + 1)
        (covGrad (I := I) (M := M) g 0 s
          (pureRGenuineDiffOp (I := I) (M := M) g 0 s S)).toFun
        (covGrad (I := I) (M := M) g 0 s S).toFun -
      tensorL2Inner (I := I) (M := M) g 0 (s + 1)
        (appCc (I := I) (M := M) g (s + 1) (s + 1)
          (slotExtend (I := I) (M := M) g s s (curvOpField (I := I) (M := M) g s))
          (covGrad (I := I) (M := M) g 0 s S)).toFun
        (covGrad (I := I) (M := M) g 0 s S).toFun := by
  classical
  rw [parsevalFrameSum_group2Residue_add_group4_eq_appCc_covGrad_curvOpField_BRIDGE
    (I := I) (M := M) g s S V hV hPar]
  have hbase : appCc (I := I) (M := M) g s s (curvOpField (I := I) (M := M) g s) S =
      pureRGenuineDiffOp (I := I) (M := M) g 0 s S :=
    appCc_curvOpField_eq_pureRGenuineDiffOp (I := I) (M := M) g s S
  have hsplit := tensorL2Inner_covGrad_appCc_eq_add (I := I) (M := M) g s s
    (curvOpField (I := I) (M := M) g s) S (covGrad (I := I) (M := M) g 0 s S)
  rw [hbase] at hsplit
  linarith [hsplit]

/-- **The genuine differentiated-curvature reorganization of the group-`2` IBP residue plus the
group-`4` second-order pair (the curvature-commutator root).** For a fixed Parseval frame family, the
frame double sum of the group-`2` integration-by-parts residue `bochnerGroup2Residue` (`= −(⟨R(V a, V b)
S, ∇_{V a}(∇_{V b} S)⟩ + ⟨R(V a, V b) S, ∇_{V b} S⟩ · divᵍ (V a))`) plus the group-`4` double sum (the
symmetric second-order pair `−∇²_{∇_{V b} V a, V a} S − ∇²_{V a, ∇_{V b} V a} S` read against `∇_{V b} S`)
equals the single `L²` pairing of the differentiated curvature operator-field action against `∇S`:
```
(∑_b ∑_a ∫ bochnerGroup2Residue) + bochnerFoldGroupSum g s S V (bochnerGroupElt4)
  = ⟨appCc (covGrad (curvOpField g s)) S, ∇S⟩_{L²}.
```

This is the genuinely-deep curvature content of the rank-`0` Bochner divergence root, *more primitive*
than its consumer: the group-`2` covariant derivative `∇_{V a}(·)` has already been integrated by parts
off into the residue `bochnerGroup2Residue` by the frame-summed engine
(`bochnerFoldGroupSum_elt2_eq_residueSum`, `integral_frameSummed_covDeriv_combined_eq_zero`).  It is the
B-rule *paired-and-collected* form of the operator-field normal form
`parsevalFrameSum_group2Residue_add_group4_eq_diffCurvTracePairing`: the operator-field covariant Leibniz
pairing split `tensorL2Inner_covGrad_appCc_eq_add` (`OperatorFieldPairingIBP`) and the order-`0` action
`appCc (curvOpField g s) S = pureRGenuineDiffOp g 0 s S` (`appCc_curvOpField_eq_pureRGenuineDiffOp`)
re-collect the gradient-of-base minus passenger-slot difference into the single differentiated-action
pairing `⟨appCc (covGrad (curvOpField g s)) S, ∇S⟩_{L²}`.  The genuine curvature content lives in the
normal form: the second covariant derivative `∇_{V a}(∇_{V b} S)` of the residue is reorganized against
`R(V a, V b) S` through the second-Bianchi / `riemannOp`-symmetry curvature commutator into the symmetric
group-`4` pattern plus the differentiated curvature coefficient `(∇R) S`, summed over the Parseval frame.
It is *false* for an arbitrary section in place of the differentiated curvature trace (the `(∇R) S` content
is genuinely present), so it genuinely uses `R`, the Parseval reproduction `hPar`, and the second-order
frame structure.  Consumers transitively depend on the normal form's `sorryAx`. -/
private theorem parsevalFrameSum_group2Residue_add_group4_eq_appCc_covGrad_curvOpField
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s)
    {N : ℕ} (V : Fin N → Π b : M, TangentSpace I b)
    (hV : ∀ a, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => (⟨b, V a b⟩ : TotalSpace E (TangentSpace I))))
    (hPar : ∀ (x : M) (u : TangentSpace I x),
      (∑ a : Fin N, g.inner x (V a x) u • V a x) = u) :
    (∑ b : Fin N, ∑ a : Fin N,
        ∫ x, bochnerGroup2Residue (I := I) (M := M) g s S (V a) (V b)
            ⟨fun y : M => V a y, hV a⟩ x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g)) +
      bochnerFoldGroupSum (I := I) (M := M) g s S V
        (bochnerGroupElt4 (I := I) (M := M) g s S) =
      tensorL2Inner (I := I) (M := M) g 0 (s + 1)
        (appCc (I := I) (M := M) g s (s + 1)
          (covGrad (I := I) (M := M) g s s (curvOpField (I := I) (M := M) g s)) S).toFun
        (covGrad (I := I) (M := M) g 0 s S).toFun :=
  parsevalFrameSum_group2Residue_add_group4_eq_appCc_covGrad_curvOpField_BRIDGE
    (I := I) (M := M) g s S V hV hPar

/-- **The group-`2` + group-`4` differentiated-curvature operator-field fold value (the `∇R`-trace fold,
canonical operator-field form).** For a fixed Parseval frame family, the sum of the group-`2` double sum
(the slot-`0` carrier `∇_{V a}(R(V a, V b) S)`) and the group-`4` double sum (the symmetric second-order
pair `−∇²_{∇_{V b} V a, V a} S − ∇²_{V a, ∇_{V b} V a} S`) equals the single `L²` pairing of the
differentiated curvature operator-field action against `∇S`:
```
bochnerFoldGroupSum g s S V (bochnerGroupElt2) + bochnerFoldGroupSum g s S V (bochnerGroupElt4)
  = ⟨appCc (covGrad (curvOpField g s)) S, ∇S⟩_{L²}.
```

This is the genuinely-deep `∇R`-trace content of the rank-`0` Bochner divergence root, in the canonical
differentiated-curvature operator-field form `⟨appCc (∇Φ₀) S, ∇S⟩` (`Φ₀ := curvOpField g s`).  Assembly
(TRANSIT, non-circular): the group-`2` covariant derivative `∇_{V a}(·)` is integrated by parts off into the
residue by the frame-summed engine (`bochnerFoldGroupSum_elt2_eq_residueSum`,
`integral_frameSummed_covDeriv_combined_eq_zero`), turning the group-`2` double sum `G₂` into the frame
double sum of the residue `bochnerGroup2Residue`; the curvature-commutator reorganization
`parsevalFrameSum_group2Residue_add_group4_eq_appCc_covGrad_curvOpField` (whose genuine `∇R`-trace content
is the more-primitive compact operator-field leaf
`parsevalFrameSum_group2Residue_add_group4_eq_appCc_covGrad_curvOpField_BRIDGE`) adds the group-`4`
symmetric second-order pair to obtain the differentiated-curvature operator-field action.  The genuine
content (`∇_{V a}(∇_{V b} S)` reorganized against `R(V a, V b) S` through the section-level Ricci identity /
frame-summed second-Bianchi tensor-curvature transfer into the differentiated curvature coefficient
`(∇R) S`, summed over the Parseval frame) lives in the compact leaf; it is *false* for an arbitrary section
in place of the differentiated curvature trace, so it genuinely uses `R`, `∇R`, `hPar`, and the second-order
frame structure.  Consumers transitively depend on the compact leaf's `sorryAx`. -/
private theorem parsevalFrameSum_group2_add_group4_eq_appCc_nablaCurvOpField
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s)
    {N : ℕ} (V : Fin N → Π b : M, TangentSpace I b)
    (hV : ∀ a, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => (⟨b, V a b⟩ : TotalSpace E (TangentSpace I))))
    (hPar : ∀ (x : M) (u : TangentSpace I x),
      (∑ a : Fin N, g.inner x (V a x) u • V a x) = u) :
    bochnerFoldGroupSum (I := I) (M := M) g s S V
        (bochnerGroupElt2 (I := I) (M := M) g s S) +
      bochnerFoldGroupSum (I := I) (M := M) g s S V
        (bochnerGroupElt4 (I := I) (M := M) g s S) =
      tensorL2Inner (I := I) (M := M) g 0 (s + 1)
        (appCc (I := I) (M := M) g s (s + 1)
          (covGrad (I := I) (M := M) g s s (curvOpField (I := I) (M := M) g s)) S).toFun
        (covGrad (I := I) (M := M) g 0 s S).toFun := by
  classical
  rw [bochnerFoldGroupSum_elt2_eq_residueSum (I := I) (M := M) g s S V hV]
  exact parsevalFrameSum_group2Residue_add_group4_eq_appCc_covGrad_curvOpField
    (I := I) (M := M) g s S V hV hPar

/-- **Combined fold 2 + 4 (term ii together with − term vi − term vii → operator-field IBP residue).** For
a fixed Parseval frame family, the sum of the group-`2` double sum (the slot-`0` carrier
`∇_{V a}(R(V a, V b) S)`) and the group-`4` double sum (the symmetric second-order pair
`−∇²_{∇_{V b} V a, V a} S − ∇²_{V a, ∇_{V b} V a} S`) equals the operator-field integration-by-parts residue
```
∑_a ∑_b ∫ ⟨[∇_{V a}(R(V a, V b) S) − ∇²_{∇_{V b} V a, V a} S − ∇²_{V a, ∇_{V b} V a} S]·slot0, slot0_{V b}(∇S)⟩
  = −⟨appCc (slotExtend Φ₀) (∇S), ∇S⟩_{L²} + ⟨∇(pureRGenuineDiffOp g 0 s S), ∇S⟩_{L²},
```
`Φ₀ := curvOpField g s`.

**Why the combination, not the two summands separately.** The group-`2` summand `∇_{V a}(R(V a, V b) S)`
does *not* integrate to `0` on its own: its `V a`-divergence has a nonzero residual, because the fixed
Parseval frame is not pointwise covariantly divergence-free (`div_g V a ≠ 0` pointwise — only the *frame*
trace is reproducing).  The single-slot divergence engine
`integral_tensorInner_covDeriv_combined_eq_zero` (`TensorConnLapLoweredIBP`,
`loweredCovDeriv_bracketChannel_combined_isDivergence`, `BracketDivergenceForm`) kills only the *combined*
three-term `∫(⟨∇_V W', Z⟩ + ⟨W', ∇_V Z⟩ + ⟨W', Z⟩ div_g V) = 0`, so the group-`2` total covariant divergence
leaves the residual `−(⟨W', ∇_V Z⟩ + ⟨W', Z⟩ div_g V)`.  That residual is exactly the lower-order content the
slot-extended operator-field B-rule of the symmetric second-order pair (group `4`) absorbs
(`tensorL2Inner_appCc_covGrad_covGrad_eq_neg`, `OperatorFieldPairingIBP`;
`tensorL2Inner_covGrad_eq_neg_tensorL2Inner_rawConnLap_gen`, the gradient-against-gradient Green identity),
so only the **combined** group-`2` + group-`4` value is the sound carrier-free residue.  The body is `sorry`;
consumers transitively depend on its `sorryAx`. -/
theorem bochnerFold_group2_add_group4_eq_operatorResidue
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s)
    {N : ℕ} (V : Fin N → Π b : M, TangentSpace I b)
    (hV : ∀ a, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => (⟨b, V a b⟩ : TotalSpace E (TangentSpace I))))
    (hPar : ∀ (x : M) (u : TangentSpace I x),
      (∑ a : Fin N, g.inner x (V a x) u • V a x) = u) :
    bochnerFoldGroupSum (I := I) (M := M) g s S V
        (bochnerGroupElt2 (I := I) (M := M) g s S) +
      bochnerFoldGroupSum (I := I) (M := M) g s S V
        (bochnerGroupElt4 (I := I) (M := M) g s S) =
      - tensorL2Inner (I := I) (M := M) g 0 (s + 1)
          (appCc (I := I) (M := M) g (s + 1) (s + 1)
            (slotExtend (I := I) (M := M) g s s (curvOpField (I := I) (M := M) g s))
            (covGrad (I := I) (M := M) g 0 s S)).toFun
          (covGrad (I := I) (M := M) g 0 s S).toFun
      + tensorL2Inner (I := I) (M := M) g 0 (s + 1)
          (covGrad (I := I) (M := M) g 0 s
            (pureRGenuineDiffOp (I := I) (M := M) g 0 s S)).toFun
          (covGrad (I := I) (M := M) g 0 s S).toFun := by
  classical
  have hbase : appCc (I := I) (M := M) g s s (curvOpField (I := I) (M := M) g s) S =
      pureRGenuineDiffOp (I := I) (M := M) g 0 s S :=
    appCc_curvOpField_eq_pureRGenuineDiffOp (I := I) (M := M) g s S
  rw [parsevalFrameSum_group2_add_group4_eq_appCc_nablaCurvOpField
    (I := I) (M := M) g s S V hV hPar]
  rw [tensorL2Inner_appCc_covGrad_covGrad_eq_neg (I := I) (M := M) g s
    (curvOpField (I := I) (M := M) g s) S]
  rw [hbase]
  rw [tensorL2Inner_covGrad_eq_neg_tensorL2Inner_rawTensorConnLapSmooth_rs (I := I) (M := M) g 0 s
    (pureRGenuineDiffOp (I := I) (M := M) g 0 s S) S]
  ring

/-- **Fold 5 (the fixed-Parseval-family bridge).** For a fixed Parseval frame family, the sum of the four
group double-sums equals the curvature cross-pairing
```
∑_{k=1}^{4} bochnerFoldGroupSum_k = ⟨pointwiseTensorCurv g s S, ∇S⟩_{L²}.
```
The genuine content is the fixed-family Parseval reduction: the rough Laplacian as the fixed-family trace of
second covariant derivatives (`rawTensorConnLapSmooth_toSection_eq_parseval_secondCovDeriv_sum`), the slot-`0`
fibre Parseval expansion of the `(0, s + 1)` pairing (`tensorInnerPointwise_succ_eq_parseval_sum_slot0`), and
the seven-term carrier identity (`secondCovDeriv_covGrad_sub_covGrad_secondCovDeriv_slot0_eq`,
`FixedFieldThirdOrderCommutator`) splitting the per-`(a, b)` integrand into the four carrier groups.  The body
is `sorry`; consumers transitively depend on its `sorryAx`. -/
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

/-- **Fold 3 (terms iii + iv − v → leading-slot Ricci trace).** For a fixed Parseval frame family, the
group-`3` double sum equals the `L²` pairing of the leading-slot Ricci-trace carrier `ricTraceSection g s S`
against `∇S`:
```
∑_a ∑_b ∫ ⟨[R(∇_{V a} V b, V a) S + R(V b, ∇_{V a} V a) S − ∇_{R(V a, V b) V a} S]·slot0, slot0_{V b}(∇S)⟩
  = ⟨ricTraceSection g s S, ∇S⟩_{L²}.
```
The genuine content is the second-Bianchi / frame-Ricci cyclic fold of the contracted slot into the raised
Ricci endomorphism (`contracted_second_bianchi`, `ricEndoRaisedFib_inner_eq_frame_trace`,
`ricTraceSection_apply_leadingSlot`, with the `riemannOp` symmetries) collapsed through the Parseval
reproduction; this is exactly the more-primitive posited Ricci leaf
`bochnerFoldGroupSum_elt3_eq_ricTraceSection`, of which this fold is the public re-export.  Consumers
transitively depend on that leaf's `sorryAx`. -/
theorem bochnerFold_group3_eq_ricTrace
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s)
    {N : ℕ} (V : Fin N → Π b : M, TangentSpace I b)
    (hV : ∀ a, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => (⟨b, V a b⟩ : TotalSpace E (TangentSpace I))))
    (hPar : ∀ (x : M) (u : TangentSpace I x),
      (∑ a : Fin N, g.inner x (V a x) u • V a x) = u) :
    bochnerFoldGroupSum (I := I) (M := M) g s S V
        (bochnerGroupElt3 (I := I) (M := M) g s S) =
      tensorL2Inner (I := I) (M := M) g 0 (s + 1)
        (ricTraceSection (I := I) (M := M) g s S).toFun
        (covGrad (I := I) (M := M) g 0 s S).toFun :=
  bochnerFoldGroupSum_elt3_eq_ricTraceSection (I := I) (M := M) g s S V hV hPar

/-- **The integrated tensor Bochner–Weitzenböck extraction (the genuine deep root, assembled non-circularly
from the more-primitive folds).** For a fixed Parseval frame family, the global metric `L²` pairing of the
order-`2` commutator defect `Curv S := pointwiseTensorCurv g s S` against `∇S := covGrad g 0 s S` splits
into the pure-Riemann curvature trace, the Bochner–Lichnerowicz Ricci trace, and the
differentiated-curvature (`∇R`) operator-field content:
```
⟨Curv S, ∇S⟩_{L²}
  = ⟨GcurvSection g s S, ∇S⟩_{L²} + ⟨ricTraceSection g s S, ∇S⟩_{L²}
      + ⟨∇(pureRGenuineDiffOp g 0 s S), ∇S⟩_{L²}
      − ⟨appCc (slotExtend Φ₀) (∇S), ∇S⟩_{L²},   Φ₀ := curvOpField g s.
```

This is the rank-`0` curvature line's **genuine integrated deep root**.  Assembly (TRANSIT, non-circular):
the seven-term bridge `bochnerFold_sevenTermSum_eq_pointwiseTensorCurvPairing` gives `⟨Curv S, ∇S⟩ =
G₁ + G₂ + G₃ + G₄`; the pure-Riemann fold `bochnerFold_group1_eq_GcurvSection` gives `G₁ = ⟨Gcurv, ∇S⟩`;
the genuine Ricci fold `bochnerFoldGroupSum_elt3_eq_ricTraceSection` gives `G₃ = ⟨ric, ∇S⟩`; and the
combined group-`2` + group-`4` operator residue `bochnerFold_group2_add_group4_eq_operatorResidue` gives
`G₂ + G₄ = −⟨appCc (slotExtend Φ₀)(∇S), ∇S⟩ + ⟨∇(pureRᵍ S), ∇S⟩`.  Adding the four assembles the split.
The genuine content lives in the posited primitives (`bochnerFoldGroupSum_elt3_eq_ricTraceSection` carries
the Ricci trace; the `∇R`-trace normal-form leaf
`parsevalFrameSum_group2Residue_add_group4_eq_diffCurvTracePairing`, which the operator residue transits,
carries the `∇R` trace); it is *false* for an arbitrary section in place of the curvature carriers (the
`s = 0` Bochner–Lichnerowicz litmus `∫ Ric(∇f, ∇f) = ‖Δ_∇ f‖² − ‖∇²f‖²` is nonzero on a non-flat manifold).
Consumers transitively depend on those primitives' `sorryAx`. -/
private theorem parsevalFrameSum_integratedBochnerExtraction
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s)
    {N : ℕ} (V : Fin N → Π b : M, TangentSpace I b)
    (hV : ∀ a, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => (⟨b, V a b⟩ : TotalSpace E (TangentSpace I))))
    (hPar : ∀ (x : M) (u : TangentSpace I x),
      (∑ a : Fin N, g.inner x (V a x) u • V a x) = u) :
    tensorL2Inner (I := I) (M := M) g 0 (s + 1)
        (pointwiseTensorCurv (I := I) (M := M) g s S).toFun
        (covGrad (I := I) (M := M) g 0 s S).toFun =
      tensorL2Inner (I := I) (M := M) g 0 (s + 1)
          (GcurvSection (I := I) (M := M) g s S).toFun
          (covGrad (I := I) (M := M) g 0 s S).toFun +
        tensorL2Inner (I := I) (M := M) g 0 (s + 1)
          (ricTraceSection (I := I) (M := M) g s S).toFun
          (covGrad (I := I) (M := M) g 0 s S).toFun +
        tensorL2Inner (I := I) (M := M) g 0 (s + 1)
          (covGrad (I := I) (M := M) g 0 s
            (pureRGenuineDiffOp (I := I) (M := M) g 0 s S)).toFun
          (covGrad (I := I) (M := M) g 0 s S).toFun -
        tensorL2Inner (I := I) (M := M) g 0 (s + 1)
          (appCc (I := I) (M := M) g (s + 1) (s + 1)
            (slotExtend (I := I) (M := M) g s s (curvOpField (I := I) (M := M) g s))
            (covGrad (I := I) (M := M) g 0 s S)).toFun
          (covGrad (I := I) (M := M) g 0 s S).toFun := by
  classical
  have hf5 := bochnerFold_sevenTermSum_eq_pointwiseTensorCurvPairing
    (I := I) (M := M) g s S V hV hPar
  have hf1 := bochnerFold_group1_eq_GcurvSection (I := I) (M := M) g s S V hV hPar
  have hf3 := bochnerFoldGroupSum_elt3_eq_ricTraceSection (I := I) (M := M) g s S V hV hPar
  have hf24 := bochnerFold_group2_add_group4_eq_operatorResidue
    (I := I) (M := M) g s S V hV hPar
  linarith [hf5, hf1, hf3, hf24]

end Connection
end Integral
end DifferentialGeometry

end
