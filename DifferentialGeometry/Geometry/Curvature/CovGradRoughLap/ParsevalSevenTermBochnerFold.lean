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

All four folds (`bochnerFold_group1_eq_GcurvSection`, `bochnerFold_group3_eq_ricTrace`,
`bochnerFold_group2_add_group4_eq_operatorResidue`, `bochnerFold_sevenTermSum_eq_pointwiseTensorCurvPairing`)
carry a `sorry` body — they are the genuine more-primitive sub-identities of the rank-`0` Bochner deep root;
the integrated nullity `movingFrameNullity_diffCurvOpField_leaf`
(`DifferentiatedCurvatureOperatorFieldIdentification`) assembles over them.  Consumers transitively depend on
their `sorryAx`.
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

/-- **Fold 1 (term i → pure-Riemann genuine curvature trace pairing).** For a fixed Parseval frame family,
the group-`1` double sum (the slot-`0` carrier `R(V a, V b)(∇_{V a} S)`) equals the `L²` pairing of the
concrete pure-Riemann genuine curvature section `GcurvSection g s S` against `∇S`:
```
∑_a ∑_b ∫ ⟨R(V a, V b)(∇_{V a} S)·slot0, slot0_{V b}(∇S)⟩ = ⟨GcurvSection g s S, ∇S⟩_{L²}.
```
The genuine content is the fixed-family Parseval reproduction of the moving-frame pure-Riemann trace value
(`pureRGenuineDiffOp_zero_succ_toSection_unit_eval`), folded back to the concrete section through
`pureRGenuineDiffOp0_eq_GcurvSection` (`pureRGenuineDiffOp g 0 (s + 1) (∇S) = GcurvSection g s S`).  The
body is `sorry`; consumers transitively depend on its `sorryAx`. -/
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
        (covGrad (I := I) (M := M) g 0 s S).toFun :=
  sorry

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
reproduction.  The body is `sorry`; consumers transitively depend on its `sorryAx`. -/
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
  sorry

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
          (covGrad (I := I) (M := M) g 0 s S).toFun :=
  sorry

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
          (bochnerGroupElt4 (I := I) (M := M) g s S) :=
  sorry

end Connection
end Integral
end DifferentialGeometry

end
