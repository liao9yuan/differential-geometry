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
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.DifferentiatedRicciEndomorphism
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.ParsevalFrameDiffCurvatureTrace
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
The group-`3` Ricci fold is an **integral** identity (the pointwise carrier identity is *false* for
`s > 0`): the group-`3` carrier `bochnerGroupElt3 = (iii + iv) − v` splits into the Ricci-direction part
`bochnerGroupElt3NegV` (term `−v`, whose frame sum over `a` is *pointwise* the leading-slot Ricci trace,
`parsevalFrameSum_ricSlot0_eq_sum_negV`, through the clean general-curvature self-trace identity
`parsevalFrame_sum_riemannOp_self_eq_neg_ricEndo`, `∑_a R(V_a, ·) V_a = −Ric`) and the frame-derivative
(tension-field) part `bochnerGroupElt3IiiIv` (terms `iii + iv`, whose frame double-sum integral *vanishes*
by the frame-summed second-Bianchi covariant integration by parts).  The two genuine more-primitive curvature
sub-identities of the rank-`0` Bochner deep root — the only `sorry` bodies in this file — are the named,
contracted-second-Bianchi Parseval-frame curvature cores reached after the covariant-Leibniz and B-rule
*system bridges* (both PROVEN):

* `parsevalFrameSum_nablaDiffCurvTrace_add_group1_eq_residue` — the **tension-field nullity core**: the
  differentiated-curvature trace double sum `∑ ⟨nablaDiffCurvTrace, ∇S⟩` plus the group-`1` double sum
  equals the group-`2` covariant integration-by-parts residue `∑ bochnerGroup2Residue`.  The tension-field
  nullity `parsevalFrameSum_tensionFieldCurvature_integral_eq_zero` (ATOM A's curvature content) is PROVEN
  on top of it through the covariant-Leibniz regrouping system bridge
  `bochnerFoldGroupSum_elt3IiiIv_eq_nablaDiffCurvTrace_split` (the carrier identity `nablaDiffCurvTrace =
  bochnerGroupElt3IiiIv + bochnerGroupElt2 − bochnerGroupElt1`, `nablaTensor0SCurv_def`) and the frame-summed
  covariant IBP `bochnerFoldGroupSum_elt2_eq_residueSum`.
* `parsevalFrameSum_group2Residue_add_group4_eq_appCc_nablaCurvOpField_core` — the **`∇R`-trace core**: the
  group-`2` IBP residue double sum plus the group-`4` double sum equals the differentiated-curvature
  operator-field action `⟨appCc (∇Φ₀) S, ∇S⟩` (`Φ₀ := curvOpField g s`), the compact operator-field form.
  The pre-split B-rule normal form `parsevalFrameSum_group2Residue_add_group4_eq_diffCurvSplit_core` (ATOM B's
  curvature content) is PROVEN on top of it through the operator-field B-rule re-collection
  `tensorL2Inner_covGrad_appCc_eq_add` / `appCc_curvOpField_eq_pureRGenuineDiffOp`.

Both cores are the genuinely-deep, frame-free, contracted-second-Bianchi `∇R`-trace content (the residue's
second covariant derivative `∇_{V a}(∇_{V b} S)` reorganized against `R(V a, V b) S` through the section-level
Ricci identity `tensorSecondCovDeriv_antisymm_eq_riemannOp` and the frame-summed differentiated tensor-curvature
transfer `frame_sum_nablaTensor0SCurv_baseSlot_eval` / `contracted_second_bianchi` into the differentiated
curvature coefficient `(∇R) S`); they are *coupled* through the shared group-`2` residue double sum.  Both are
GENERAL Parseval-frame curvature content that should be promoted to a curvature file.  The integrated nullity
`movingFrameNullity_diffCurvOpField_leaf` (`DifferentiatedCurvatureOperatorFieldIdentification`) assembles over
the folds; consumers transitively depend on the two cores' `sorryAx`.
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
whose Parseval-frame double-sum pairing against `∇S` collapses (through the contracted second Bianchi) to
the IBP residue that the tension-field nullity needs. -/
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
tension-field nullity.  It is general Parseval-frame curvature content. -/
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
`tensor0SCovariantDerivative s` world — through which the rank-`0` Bochner tension-field nullity root
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
tension-field nullity root `parsevalFrameSum_nablaDiffCurvTrace_add_group1_eq_residue` — onto the
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
    (hB : ∀ i, B i = ContMDiffSection.mk (smoothOrthoFrame (I := I) g x i)
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
    (hB : ∀ i, B i = ContMDiffSection.mk (smoothOrthoFrame (I := I) g x i)
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
of `D`, the integrand the integrated divergence-of-curvature nullity consumes. -/
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
/-- **The integrated second-Bianchi divergence-of-curvature identity (the genuine deep core of the
tension-field nullity — the single strictly-more-primitive integral identity to which the rank-`0`
Bochner tension-field divergence root reduces).**  For a fixed smooth Parseval frame family, the single
sum over `b` of the integral of the once-contracted second-Bianchi differentiated-Ricci frame triple sum
`tripleSum(b, x)` (the `ν₁ − ν₂` content of `parsevalDiagDiffCurv_pair_eq_nablaRicci_tripleSum`) equals
the group-`1` double sum minus the group-`2` double sum:
```
∑_b ∫ tripleSum(b, x) ∂μ = bochnerFoldGroupSum (bochnerGroupElt1) − bochnerFoldGroupSum (bochnerGroupElt2).
```
The consuming root `parsevalFrameSum_bochnerFold_tensionFieldDivergence_root` is reduced to *exactly this
identity*, sorry-free: the covariant-Leibniz split `bochnerFoldGroupSum_elt3IiiIv_eq_nablaDiffCurvTrace_split`
plus the `ν₁`-arm differentiated-Ricci read `nablaDiffCurvTrace_doubleSum_eq_neg_tripleSum_bSum`
(`D = − ∑_b ∫ tripleSum`) leave precisely `group3IiiIv_sum = (−∑_b∫tripleSum) − group2 + group1`, which
is `0` iff this identity holds.

**The genuine remaining content and the one missing primitive.**  Its `ν₂`-arm matches the group-`2`
frame-summed covariant integration by parts `bochnerFoldGroupSum_elt2_eq_residueSum`
(`integral_frameSummed_covDeriv_combined_eq_zero`) — the group-`2` residue `bochnerGroup2Residue` — and
its residual `∇V`-frame terms telescope through the Parseval covariant-derivative antisymmetry
`parsevalFrame_sum_covDeriv_inner_antisymm`.  The `ν₁`-arm, however, requires an **integrated
divergence-of-Ricci integration-by-parts bridge** equating `∑_b ∫ ⟨[the differentiated-Ricci `ν₁`
contraction against `S`], ∇_{V b} S⟩` with the group-`1` curvature-operator double sum
`∑_a ∑_b ∫ ⟨R(V a, V b)(∇_{V a} S), ∇_{V b} S⟩` — an `∫ ⟨∇_X Ric · T, ∇S⟩ = − ∫ ⟨Ric · T, ∇(∇S)⟩`-type
covariant IBP specialised to this Ricci contraction.  That divergence-of-Ricci IBP is a genuinely
*missing* strictly-more-primitive prerequisite: it occurs nowhere in `DifferentialGeometry/` nor in
Mathlib (verified by full-tree decl search for `nablaRicci` co-occurring with an integral, and by
`#leansearch`).  Re-expanding `tripleSum` through `nablaTensor0SCurv_def` lands back on
`bochnerGroupElt3IiiIv` and is circular, so it must be supplied as the new primitive, not unwound.
Stated integrated + frame-summed throughout (the two differentiated-Ricci arms each carry the
chart-unbounded `smoothExtensionTangent` ext-jet, so only this combined integrated object is sound).  It
is *false* for an arbitrary section in place of the differentiated-curvature content, so it genuinely
uses `R`, `∇R`, the Parseval reproduction `hPar`, and the frame's `∇V` structure.  Body `sorry`: the
single strictly-more-primitive transit posit of the rank-`0` Bochner tension-field divergence root. -/
private lemma parsevalFrameSum_tripleSum_bSum_eq_group1_sub_group2
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s)
    {N : ℕ} (V : Fin N → Π b : M, TangentSpace I b)
    (hV : ∀ a, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => (⟨b, V a b⟩ : TotalSpace E (TangentSpace I))))
    (hPar : ∀ (x : M) (u : TangentSpace I x),
      (∑ a : Fin N, g.inner x (V a x) u • V a x) = u) :
    (∑ b : Fin N,
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
          ∂(riemannianVolumeMeasure (I := I) (M := M) g)) =
      bochnerFoldGroupSum (I := I) (M := M) g s S V
          (bochnerGroupElt1 (I := I) (M := M) g s S) -
        bochnerFoldGroupSum (I := I) (M := M) g s S V
          (bochnerGroupElt2 (I := I) (M := M) g s S) := by
  sorry

set_option linter.unusedSectionVars false in
/-- **(Fact 1 of the combined second-Bianchi root — the integrated tension-field divergence
nullity.)**  For a fixed smooth Parseval frame family, the frame double sum of the integral of the
`(0, s)` pairing of the tension-field curvature carrier `bochnerGroupElt3IiiIv = R(∇_{V a} V b, V a) S
+ R(V b, ∇_{V a} V a) S` against the slot-`0` gradient `∇_{V b} S` vanishes — the integrated
divergence-of-curvature `div R` nullity: the `ν₁`-arm contracted second Bianchi
(`nablaCurvSec_diag_frame_trace_eq_nablaRicci_sub`) cancelling the `ν₂`-arm frame-summed covariant
integration by parts (`integral_frameSummed_covDeriv_combined_eq_zero`), the residual `∇V` terms
telescoping through the Parseval covariant-derivative antisymmetry
(`parsevalFrame_sum_covDeriv_inner_antisymm`).  Stated integrated + frame-summed + whole-tensor
throughout (the two differentiated-Ricci arms each separately carry the chart-unbounded
`smoothExtensionTangent` ext-jet, so only this combined integrated object is sound — the structural
law on the sibling combined root's docstring).  Non-vacuity: at `s = 0` the carrier reads the
curvature of a scalar and the fact degenerates to `0 = 0`, but the fact genuinely uses the carrier's
curvature antisymmetry, `hPar`, and the frame's `∇V` structure (an arbitrary non-curvature carrier
in its place does not integrate to zero).

The body is *not* `sorry`: it is reduced sorry-free to the single strictly-more-primitive integral
identity `parsevalFrameSum_tripleSum_bSum_eq_group1_sub_group2` (`∑_b ∫ tripleSum = group1 − group2`),
through the covariant-Leibniz split `bochnerFoldGroupSum_elt3IiiIv_eq_nablaDiffCurvTrace_split` and the
`ν₁`-arm differentiated-Ricci read `nablaDiffCurvTrace_doubleSum_eq_neg_tripleSum_bSum`. -/
private theorem parsevalFrameSum_bochnerFold_tensionFieldDivergence_root
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s)
    {N : ℕ} (V : Fin N → Π b : M, TangentSpace I b)
    (hV : ∀ a, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => (⟨b, V a b⟩ : TotalSpace E (TangentSpace I))))
    (hPar : ∀ (x : M) (u : TangentSpace I x),
      (∑ a : Fin N, g.inner x (V a x) u • V a x) = u) :
    bochnerFoldGroupSum (I := I) (M := M) g s S V
        (bochnerGroupElt3IiiIv (I := I) (M := M) g s S) = 0 := by
  classical
  -- The covariant-Leibniz regrouping: `group3IiiIv_sum = D − group2 + group1`, with `D` the
  -- differentiated-curvature trace double sum.
  have hsplit := bochnerFoldGroupSum_elt3IiiIv_eq_nablaDiffCurvTrace_split
    (I := I) (M := M) g s S V hV
  -- The `ν₁`-arm differentiated-Ricci read: `D = − ∑_b ∫ tripleSum(b, x)`.
  have hD := nablaDiffCurvTrace_doubleSum_eq_neg_tripleSum_bSum
    (I := I) (M := M) g s S V hV hPar
  rw [hD] at hsplit
  rw [hsplit]
  -- Remaining genuine content: `− ∑_b ∫ tripleSum − group2 + group1 = 0`, i.e. the integrated
  -- second-Bianchi divergence-of-curvature identity `∑_b ∫ tripleSum = group1 − group2`.
  have hkey := parsevalFrameSum_tripleSum_bSum_eq_group1_sub_group2
    (I := I) (M := M) g s S V hV hPar
  rw [hkey]
  ring

set_option linter.unusedSectionVars false in
/-- **(Fact 2 of the combined second-Bianchi root — the differentiated-curvature operator-field
identification.)**  For a fixed smooth Parseval frame family, the group-`2` double sum
`∑_a ∑_b ∫ ⟨∇_{V a}(R(V a, V b) S), ∇_{V b} S⟩` plus the symmetric second-order group-`4` double sum
equals the single `L²` pairing of the differentiated curvature operator-field action
`appCc (covGrad Φ₀) S` (`Φ₀ := curvOpField g s`, the frame-free `(∇R) S` field) against `∇S` — the
same combined integrated whole-tensor object as Fact 1 read as the operator-field action (Theorem B
`frame_sum_nablaTensor0SCurv_diag_baseSlot_eval`, the group-`4` second-order recombination
`tensorSecondCovDeriv_antisymm_eq_riemannOp`, and the operator-field Green pairing engines); stated
integrated + frame-summed throughout, never extracting a per-direction `M → E` quantity.
Non-vacuity (the `s = 0` Bochner–Lichnerowicz litmus): at `s = 0` the right side vanishes and the
fact forces `group2 + group4 = 0` at exactly the ricTrace value the classical scalar
Bochner–Lichnerowicz identity demands — nonzero on a non-flat manifold; dropping the curvature
content breaks the litmus.  Body `sorry`: the second independent deep atom of the rank-`0` Bochner
curvature line. -/
private theorem parsevalFrameSum_bochnerFold_operatorFieldIdentification_root
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
        (covGrad (I := I) (M := M) g 0 s S).toFun :=
  sorry

set_option linter.unusedSectionVars false in
/-- **The combined integrated second-Bianchi root of the rank-`0` Bochner fold**, assembled as the
pair of its two independent deep atoms `parsevalFrameSum_bochnerFold_tensionFieldDivergence_root`
(the integrated tension-field divergence nullity) and
`parsevalFrameSum_bochnerFold_operatorFieldIdentification_root` (the differentiated-curvature
operator-field identification); the structural law (why only combined, integrated, frame-summed
whole-tensor objects are sound here) and the non-vacuity litmuses live on the two atoms'
docstrings.  Consumers transitively depend on the two atoms' `sorryAx`. -/
private theorem parsevalFrameSum_bochnerFold_combined_secondBianchi_root
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s)
    {N : ℕ} (V : Fin N → Π b : M, TangentSpace I b)
    (hV : ∀ a, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => (⟨b, V a b⟩ : TotalSpace E (TangentSpace I))))
    (hPar : ∀ (x : M) (u : TangentSpace I x),
      (∑ a : Fin N, g.inner x (V a x) u • V a x) = u) :
    bochnerFoldGroupSum (I := I) (M := M) g s S V
        (bochnerGroupElt3IiiIv (I := I) (M := M) g s S) = 0 ∧
      bochnerFoldGroupSum (I := I) (M := M) g s S V
          (bochnerGroupElt2 (I := I) (M := M) g s S) +
        bochnerFoldGroupSum (I := I) (M := M) g s S V
          (bochnerGroupElt4 (I := I) (M := M) g s S) =
        tensorL2Inner (I := I) (M := M) g 0 (s + 1)
          (appCc (I := I) (M := M) g s (s + 1)
            (covGrad (I := I) (M := M) g s s (curvOpField (I := I) (M := M) g s)) S).toFun
          (covGrad (I := I) (M := M) g 0 s S).toFun :=
  ⟨parsevalFrameSum_bochnerFold_tensionFieldDivergence_root (I := I) (M := M) g s S V hV hPar,
    parsevalFrameSum_bochnerFold_operatorFieldIdentification_root (I := I) (M := M) g s S V hV hPar⟩

/-- **The integrated Parseval-frame diagonal differentiated-curvature trace pairing equals the
group-`2` minus group-`1` double sum (the genuine `nablaTensor0SCurv`-form curvature kernel of the
tension-field nullity).** For a fixed Parseval frame family `V a`, the frame double sum of the integral
over the closed manifold of the `(0, s)` fibre pairing of the `tensor0SAsRS`-wrap of the diagonal
differentiated `(0, s)`-tensor curvature object `nablaTensor0SCurv g s (V a) (V a) (V b) A`
(`A y := S.toSection y (unit)`) against the slot-`0` directional gradient `∇_{V b} S` equals the
group-`2` double sum minus the group-`1` double sum:
```
∑_a ∑_b ∫ ⟨tensor0SAsRS (nablaTensor0SCurv g s (V a) (V a) (V b) A), ∇_{V b} S⟩_g ∂μ
  = bochnerFoldGroupSum g s S V (bochnerGroupElt2) − bochnerFoldGroupSum g s S V (bochnerGroupElt1).
```

This is the genuine, irreducible, near-bedrock curvature kernel of the rank-`0` tension-field nullity,
re-expressed through the connectors (`nablaDiffCurvTraceCc_toSection_eq_tensor0SAsRS_nablaTensor0SCurv`,
`tensorInnerScalar_nablaDiffCurvTrace_eq_tensorInnerPointwise_nablaTensor0SCurv`) on the frame-free
**`nablaTensor0SCurv`** differentiated-curvature object — the form the now-committed Parseval =
orthonormal diagonal-trace bridge `parsevalFrame_eq_orthoFrame_diag_nablaTensor0SCurv`
(`CurvatureOperator.ParsevalFrameDiffCurvatureTrace`) acts on.  Through that bridge the diagonal
Parseval-frame trace `∑_a nablaTensor0SCurv g s (V a) (V a) (V b) A` becomes the orthonormal-frame
diagonal trace `∑_i nablaTensor0SCurv g s (B_i) (B_i) (V b) A`, which the slot-wise divergence-of-curvature
transfer `frame_sum_nablaTensor0SCurv_diag_baseSlot_eval` (`CurvatureOperator.DifferentiatedSlotwiseCurvature`)
folds into the first-slot divergence `∑_i (∇_{B_i} R)(B_i, ·)`, and the once-contracted second Bianchi
identity `nablaCurvSec_diag_frame_trace_eq_nablaRicci_sub` (`∑_i g((∇_{B_i} R)(B_i, Y) v, U) =
∇_U Ric(Y, v) − ∇_v Ric(U, Y)`) collapses onto the differentiated-Ricci content; the residual
frame-derivative `∇V` terms telescope to zero through the Parseval-frame covariant-derivative antisymmetry
`parsevalFrame_sum_covDeriv_inner_antisymm` and the frame-summed covariant integration-by-parts engine
`integral_frameSummed_covDeriv_combined_eq_zero`.  It is *false* for an arbitrary section in place of the
differentiated-curvature trace, so it genuinely uses `R`, `∇R`, the Parseval reproduction `hPar`, and the
frame's second-order (`∇V`) structure.  The proof transits the combined integrated second-Bianchi root
`parsevalFrameSum_bochnerFold_combined_secondBianchi_root` (fact 1, the tension-field nullity) through the
sorry-free carrier split `bochnerFoldGroupSum_elt3IiiIv_eq_nablaDiffCurvTrace_split` and the connector
`tensorInnerScalar_nablaDiffCurvTrace_eq_tensorInnerPointwise_nablaTensor0SCurv`; consumers transitively
depend on that root's `sorryAx`. -/
private theorem parsevalFrameSum_diagDiffCurvTrace_pairing_eq_group2_sub_group1
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s)
    {N : ℕ} (V : Fin N → Π b : M, TangentSpace I b)
    (hV : ∀ a, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => (⟨b, V a b⟩ : TotalSpace E (TangentSpace I))))
    (hPar : ∀ (x : M) (u : TangentSpace I x),
      (∑ a : Fin N, g.inner x (V a x) u • V a x) = u) :
    (∑ a : Fin N, ∑ b : Fin N,
        ∫ x, tensorInnerPointwise (I := I) (M := M) g 0 s x
            (TensorRSSpace.toModel
              (tensor0SAsRS (I := I) (M := M) x
                (nablaTensor0SCurv (I := I) g s ⟨fun b => V a b, hV a⟩ ⟨fun b => V a b, hV a⟩
                  ⟨fun y => V b y, hV b⟩
                  (fun y : M =>
                    (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace s I y from S.toSection y)
                      (unitZeroSec (I := I) (M := M) y)) x)))
            (TensorRSSpace.toModel (bochnerGradSlot0 (I := I) (M := M) g s S (V b) x))
          ∂(riemannianVolumeMeasure (I := I) (M := M) g)) =
      bochnerFoldGroupSum (I := I) (M := M) g s S V
          (bochnerGroupElt2 (I := I) (M := M) g s S) -
        bochnerFoldGroupSum (I := I) (M := M) g s S V
          (bochnerGroupElt1 (I := I) (M := M) g s S) := by
  classical
  -- The covariant-Leibniz regrouping (the sorry-free system bridge):
  -- `group3IiiIv_sum = D − group2_sum + group1_sum`, with `D := ∑_a ∑_b ∫ ⟨nablaDiffCurvTrace, ∇S⟩`.
  have hsplit := bochnerFoldGroupSum_elt3IiiIv_eq_nablaDiffCurvTrace_split
    (I := I) (M := M) g s S V hV
  -- The connector identifies the differentiated-curvature trace double sum `D` (the `tensorInnerScalar`
  -- form) with the diagonal `nablaTensor0SCurv` trace double sum `T` (the kernel LHS).
  have hD : (∑ a : Fin N, ∑ b : Fin N,
        ∫ x, tensorInnerScalar (I := I) (M := M) g 0 s
            (nablaDiffCurvTraceCc (I := I) (M := M) g s S (hV a) (hV b)).toSection
            (bochnerGradSlot0Cc (I := I) (M := M) g s S (hV b)).toSection x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g)) =
      ∑ a : Fin N, ∑ b : Fin N,
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
    refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    exact tensorInnerScalar_nablaDiffCurvTrace_eq_tensorInnerPointwise_nablaTensor0SCurv
      (I := I) (M := M) g s S (hV a) (hV b) x
  -- The genuine integrated second-Bianchi divergence nullity (fact 1 of the combined root):
  -- `group3IiiIv_sum = 0`.  With the split and the connector, `T = D = group2_sum − group1_sum`.
  have hbianchi :=
    (parsevalFrameSum_bochnerFold_combined_secondBianchi_root
      (I := I) (M := M) g s S V hV hPar).1
  rw [hbianchi] at hsplit
  rw [← hD]
  linarith [hsplit]

/-- **The frame-summed tension-field curvature pairing integrates to zero (the genuine deep curvature
root of the rank-`0` Bochner divergence: the integrated second-Bianchi covariant-divergence nullity).**
For a fixed Parseval frame family `V a`, the group-`3` tension-field carrier double sum vanishes:
```
bochnerFoldGroupSum g s S V (bochnerGroupElt3IiiIv) = 0,
```
i.e. `∑_a ∑_b ∫ ⟨R(∇_{V a} V b, V a) S + R(V b, ∇_{V a} V a) S, ∇_{V b} S⟩_g ∂μ = 0`.

**Why integrated, not pointwise.** The two tension-field curvature carriers `R(∇_{V a} V b, V a) S` and
`R(V b, ∇_{V a} V a) S` carry a frame derivative `∇V` in a curvature slot; they are generally nonzero and
frame-dependent pointwise (the fixed Parseval frame is not pointwise covariantly divergence-free, so the
`a`-sum does not vanish at a point).  They cancel only after integration: by the covariant-Leibniz
regrouping `bochnerFoldGroupSum_elt3IiiIv_eq_nablaDiffCurvTrace_split` (PROVEN above,
`nablaTensor0SCurv_def`) the tension-field double sum equals the differentiated-curvature trace double sum
`∑_a ∑_b ∫ ⟨nablaDiffCurvTrace, ∇_{V b} S⟩` minus the group-`2` plus the group-`1` double sums; reading the
differentiated-curvature trace through the connectors onto the frame-free `nablaTensor0SCurv` object
(`tensorInnerScalar_nablaDiffCurvTrace_eq_tensorInnerPointwise_nablaTensor0SCurv`) and invoking the genuine
`nablaTensor0SCurv`-form kernel `parsevalFrameSum_diagDiffCurvTrace_pairing_eq_group2_sub_group1` (the
diagonal differentiated-curvature trace pairing equals `group2 − group1`, the integrated second-Bianchi /
divergence-of-curvature content) makes the differentiated-curvature trace double sum equal
`group2 − group1`, so the whole tension-field double sum collapses to
`(group2 − group1) − group2 + group1 = 0`.  It is *false* for an arbitrary section in place of the
tension-field curvature trace, so it genuinely uses `R`, `∇R`, the Parseval reproduction `hPar`, and the
frame's second-order (`∇V`) structure (all carried by the kernel).  This is GENERAL Parseval-frame
curvature content; consumers transitively depend on the kernel's `sorryAx`. -/
private theorem parsevalFrameSum_tensionFieldCurvatureDivergence_eq_zero
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s)
    {N : ℕ} (V : Fin N → Π b : M, TangentSpace I b)
    (hV : ∀ a, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => (⟨b, V a b⟩ : TotalSpace E (TangentSpace I))))
    (hPar : ∀ (x : M) (u : TangentSpace I x),
      (∑ a : Fin N, g.inner x (V a x) u • V a x) = u) :
    bochnerFoldGroupSum (I := I) (M := M) g s S V
        (bochnerGroupElt3IiiIv (I := I) (M := M) g s S) = 0 := by
  classical
  -- The covariant-Leibniz regrouping of the tension-field carrier (the sorry-free system bridge):
  -- `group3IiiIv_sum = (∑_a ∑_b ∫ ⟨nablaDiffCurvTrace, ∇S⟩) − group2_sum + group1_sum`.
  have hsplit := bochnerFoldGroupSum_elt3IiiIv_eq_nablaDiffCurvTrace_split
    (I := I) (M := M) g s S V hV
  -- The connector identifies the per-`(a, b)` differentiated-curvature trace pairing with the
  -- `nablaTensor0SCurv`-form pairing, so the differentiated-curvature trace double sum `D` is the
  -- `nablaTensor0SCurv` diagonal-trace double sum of the kernel.
  have hD : (∑ a : Fin N, ∑ b : Fin N,
        ∫ x, tensorInnerScalar (I := I) (M := M) g 0 s
            (nablaDiffCurvTraceCc (I := I) (M := M) g s S (hV a) (hV b)).toSection
            (bochnerGradSlot0Cc (I := I) (M := M) g s S (hV b)).toSection x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g)) =
      ∑ a : Fin N, ∑ b : Fin N,
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
    refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    exact tensorInnerScalar_nablaDiffCurvTrace_eq_tensorInnerPointwise_nablaTensor0SCurv
      (I := I) (M := M) g s S (hV a) (hV b) x
  -- The genuine `nablaTensor0SCurv`-form curvature kernel: the diagonal differentiated-curvature trace
  -- pairing equals `group2 − group1` (the integrated second-Bianchi / divergence-of-curvature content,
  -- the form the Parseval = orthonormal bridge and Theorems A/B discharge).
  have hker := parsevalFrameSum_diagDiffCurvTrace_pairing_eq_group2_sub_group1
    (I := I) (M := M) g s S V hV hPar
  rw [hsplit, hD, hker]
  abel

/-- **The differentiated-curvature trace plus group-`1` pairing equals the group-`2` integration-by-parts
residue (the genuine contracted-second-Bianchi curvature core of the tension-field nullity).** For a fixed
Parseval frame family, the differentiated-curvature trace double sum
`∑_a ∑_b ∫ ⟨nablaDiffCurvTrace, ∇_{V b} S⟩` plus the group-`1` double sum
`bochnerFoldGroupSum (bochnerGroupElt1)` equals the group-`2` covariant integration-by-parts residue
`∑_b ∑_a ∫ bochnerGroup2Residue`:
```
(∑_a ∑_b ∫ ⟨nablaDiffCurvTrace, ∇_{V b} S⟩) + bochnerFoldGroupSum (bochnerGroupElt1)
  = ∑_b ∑_a ∫ bochnerGroup2Residue.
```

This is the genuinely-deep, frame-free curvature content of the tension-field nullity: the
differentiated-curvature trace `∑_a (∇_{V a} R^{(s)})(V a, V b)` collapses — through the frame-summed
differentiated tensor-curvature transfer (`frame_sum_nablaTensor0SCurv_baseSlot_eval`,
`nablaTensorCurv_frame_trace_eq_nablaRicci`) and the contracted second Bianchi (`contracted_second_bianchi`,
`div Ric = ½ d scal`) read over the Parseval frame (`parseval_family_sum_bilin_eq`) — onto exactly the
lower-order content that the group-`2` covariant derivative `∇_{V a}(R(V a, V b) S)` sheds when it is
integrated by parts off into the residue `bochnerGroup2Residue`.  It is *false* for an arbitrary section in
place of the differentiated-curvature trace (it genuinely uses `R`, `∇R`, the Parseval reproduction `hPar`,
and the frame's second-order `∇V` structure).  This is GENERAL Parseval-frame curvature content that should
be promoted to a curvature file; the body is `sorry` and consumers transitively depend on its `sorryAx`. -/
private theorem parsevalFrameSum_nablaDiffCurvTrace_add_group1_eq_residue
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
          ∂(riemannianVolumeMeasure (I := I) (M := M) g)) +
      bochnerFoldGroupSum (I := I) (M := M) g s S V
        (bochnerGroupElt1 (I := I) (M := M) g s S) =
      ∑ b : Fin N, ∑ a : Fin N,
        ∫ x, bochnerGroup2Residue (I := I) (M := M) g s S (V a) (V b)
            ⟨fun y : M => V a y, hV a⟩ x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  classical
  -- The covariant-Leibniz regrouping of the tension-field carrier (the sorry-free system bridge):
  -- `bochnerFoldGroupSum (bochnerGroupElt3IiiIv) = (∑_a ∑_b ∫ ⟨nablaDiffCurvTrace, ∇S⟩)
  --   − bochnerFoldGroupSum (bochnerGroupElt2) + bochnerFoldGroupSum (bochnerGroupElt1)`.
  have hsplit := bochnerFoldGroupSum_elt3IiiIv_eq_nablaDiffCurvTrace_split
    (I := I) (M := M) g s S V hV
  -- The group-`2` frame-summed covariant integration by parts (sorry-free):
  -- `bochnerFoldGroupSum (bochnerGroupElt2) = ∑_b ∑_a ∫ bochnerGroup2Residue`.
  have hresidue := bochnerFoldGroupSum_elt2_eq_residueSum (I := I) (M := M) g s S V hV
  -- The genuine contracted-second-Bianchi content: the frame-summed tension-field curvature pairing
  -- integrates to zero (`bochnerFoldGroupSum (bochnerGroupElt3IiiIv) = 0`).  Reading the carrier
  -- `bochnerGroupElt3IiiIv` through the `tensor0SAsRS`-unit packaging, its frame double-sum integral is
  -- the section/inner-scalar tension-field nullity, the genuine deep curvature root.
  have hbianchi :
      bochnerFoldGroupSum (I := I) (M := M) g s S V
          (bochnerGroupElt3IiiIv (I := I) (M := M) g s S) = 0 :=
    parsevalFrameSum_tensionFieldCurvatureDivergence_eq_zero (I := I) (M := M) g s S V hV hPar
  -- Eliminate the carrier-free residue: the differentiated-curvature trace plus group-`1` equals the
  -- group-`2` integration-by-parts residue.
  rw [hresidue] at hsplit
  linarith [hsplit, hbianchi]

/-- **The frame-summed tension-field curvature pairing integrates to zero (the genuine second-Bianchi
tension-field covariant-divergence nullity, `(0, s)`-inner-scalar form).** For a fixed Parseval frame
family `V a`, the frame double sum of the integral over the closed manifold of the `(0, s)`-metric inner
product of the packaged tension-field curvature carrier
`bochnerGroupElt3IiiIvCc = R(∇_{V a} V b, V a) S + R(V b, ∇_{V a} V a) S` against the directional gradient
`∇_{V b} S = bochnerGradSlot0Cc` vanishes:
```
∑_a ∑_b ∫ ⟨R(∇_{V a} V b, V a) S + R(V b, ∇_{V a} V a) S, ∇_{V b} S⟩_g ∂μ = 0.
```

This is the genuinely-deep, frame-free curvature core of the group-`3` Ricci fold (the only curvature
content of `bochnerGroupElt3IiiIv_frameSum_integral_eq_zero`, exposed at the section/inner-scalar level,
stripped of the `tensor0SAsRS`/`bochnerGradSlot0` curry wrappers).  The two tension-field curvature
carriers are generally nonzero and frame-dependent pointwise (the fixed Parseval frame is not pointwise
covariantly divergence-free), so the `a`-sum does not vanish at a point; they cancel only after
integration.  The cancellation is the frame-summed second Bianchi identity: writing the tension-field
curvature `R(∇_{V a} V b, V a) S + R(V b, ∇_{V a} V a) S` as the covariant Leibniz remainder
`∇_{V a}(R(V b, V a) S) − R(V b, V a)(∇_{V a} S) − (∇_{V a} R^{(s)})(V b, V a) S`
(`nablaTensor0SCurv_def`), the leading total-covariant-divergence term integrates against `∇_{V b} S`
to its frame-summed integration-by-parts residue (`integral_frameSummed_covDeriv_combined_eq_zero`), the
differentiated-curvature trace `∑_a (∇_{V a} R^{(s)})(V b, V a)` collapses through the contracted second
Bianchi (`nablaTensorCurv_frame_trace_eq_nablaRicci`, `contracted_second_bianchi`) summed over the
Parseval frame (`parseval_family_sum_bilin_eq`), and the residual curvature pairings cancel.  It is *false*
for an arbitrary section in place of the tension-field curvature trace, so it genuinely uses `R`, `∇R`, the
Parseval reproduction `hPar`, and the frame's second-order (`∇V`) structure.  This is GENERAL
Parseval-frame curvature content that should be promoted to a curvature file; the body is `sorry` and
consumers transitively depend on its `sorryAx`. -/
private theorem parsevalFrameSum_tensionFieldCurvature_integral_eq_zero
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s)
    {N : ℕ} (V : Fin N → Π b : M, TangentSpace I b)
    (hV : ∀ a, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => (⟨b, V a b⟩ : TotalSpace E (TangentSpace I))))
    (hPar : ∀ (x : M) (u : TangentSpace I x),
      (∑ a : Fin N, g.inner x (V a x) u • V a x) = u) :
    ∑ a : Fin N, ∑ b : Fin N,
        ∫ x, tensorInnerScalar (I := I) (M := M) g 0 s
            (bochnerGroupElt3IiiIvCc (I := I) (M := M) g s S (hV a) (hV b)).toSection
            (bochnerGradSlot0Cc (I := I) (M := M) g s S (hV b)).toSection x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) = 0 := by
  classical
  -- The inner-scalar double sum is the `bochnerFoldGroupSum` of the tension-field carrier
  -- `bochnerGroupElt3IiiIv` (`tensorInnerScalar` unfolds to the `tensorInnerPointwise (0, s)` pairing
  -- of the `Cc`-packaged carriers, reproduced pointwise).
  rw [show (∑ a : Fin N, ∑ b : Fin N,
        ∫ x, tensorInnerScalar (I := I) (M := M) g 0 s
            (bochnerGroupElt3IiiIvCc (I := I) (M := M) g s S (hV a) (hV b)).toSection
            (bochnerGradSlot0Cc (I := I) (M := M) g s S (hV b)).toSection x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g)) =
      bochnerFoldGroupSum (I := I) (M := M) g s S V
        (bochnerGroupElt3IiiIv (I := I) (M := M) g s S) from by
    refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    rw [tensorInnerScalar_apply (I := I) (M := M) g 0 s,
      bochnerGroupElt3IiiIvCc_toSection_eq (I := I) (M := M) g s S (hV a) (hV b) x,
      bochnerGradSlot0Cc_toSection_apply (I := I) (M := M) g s S (hV b) x]]
  -- The genuine deep curvature root: the frame-summed tension-field curvature pairing integrates to zero
  -- (`bochnerFoldGroupSum (bochnerGroupElt3IiiIv) = 0`), the contracted-second-Bianchi covariant-divergence
  -- nullity in raw-carrier form.
  exact parsevalFrameSum_tensionFieldCurvatureDivergence_eq_zero (I := I) (M := M) g s S V hV hPar

/-- **The frame-derivative (tension-field) part of the group-`3` carrier integrates to zero (the
frame-summed second-Bianchi covariant divergence).** For a fixed Parseval frame family, the frame double
sum of the integral of the `(iii + iv)` carrier `bochnerGroupElt3IiiIv`
(`= R(∇_{V a} V b, V a) S + R(V b, ∇_{V a} V a) S`) paired against the slot-`0` carrier `∇_{V b} S`
vanishes:
```
∑_a ∑_b ∫ ⟨bochnerGroupElt3IiiIv g s S (V a) (V b), slot0_{V b}(∇S)⟩ ∂μ = 0.
```

**Why integrated, not pointwise.** The two carriers carry a frame derivative `∇V` in a curvature slot;
they are generally nonzero and frame-dependent pointwise (the fixed Parseval frame is not pointwise
covariantly divergence-free, so `∑_a` of the tension-field curvature terms does not vanish at a point).
They cancel only after integration: the frame-summed second Bianchi identity rewrites the `(a)`-sum of the
two tension-field curvature terms as a total covariant divergence, whose integral over the closed manifold
is `0` (the frame-summed covariant integration-by-parts engine
`integral_frameSummed_covDeriv_combined_eq_zero`).  This is GENERAL Parseval-frame curvature content; the
body is `sorry` and consumers transitively depend on its `sorryAx`. -/
private theorem bochnerGroupElt3IiiIv_frameSum_integral_eq_zero
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s)
    {N : ℕ} (V : Fin N → Π b : M, TangentSpace I b)
    (hV : ∀ a, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => (⟨b, V a b⟩ : TotalSpace E (TangentSpace I))))
    (hPar : ∀ (x : M) (u : TangentSpace I x),
      (∑ a : Fin N, g.inner x (V a x) u • V a x) = u) :
    ∑ a : Fin N, ∑ b : Fin N,
        ∫ x, tensorInnerPointwise (I := I) (M := M) g 0 s x
            (TensorRSSpace.toModel (bochnerGroupElt3IiiIv (I := I) (M := M) g s S (V a) (V b) x))
            (TensorRSSpace.toModel (bochnerGradSlot0 (I := I) (M := M) g s S (V b) x))
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) = 0 := by
  classical
  -- The raw carrier double sum is the section/inner-scalar double sum of the bedrock-near curvature
  -- core `parsevalFrameSum_tensionFieldCurvature_integral_eq_zero`, term-by-term (`tensorInnerScalar`
  -- unfolds definitionally; the `Cc` packagings reproduce the raw carriers pointwise).
  refine Eq.trans ?_ (parsevalFrameSum_tensionFieldCurvature_integral_eq_zero
    (I := I) (M := M) g s S V hV hPar)
  refine Finset.sum_congr rfl (fun a _ => ?_)
  refine Finset.sum_congr rfl (fun b _ => ?_)
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
  rw [tensorInnerScalar_apply (I := I) (M := M) g 0 s,
    bochnerGroupElt3IiiIvCc_toSection_eq (I := I) (M := M) g s S (hV a) (hV b) x,
    bochnerGradSlot0Cc_toSection_apply (I := I) (M := M) g s S (hV b) x]

/-- **The group-`3` Ricci-trace fold (terms iii + iv − v → leading-slot Ricci trace).** For a fixed
Parseval frame family, the group-`3` double sum equals the `L²` pairing of the leading-slot Ricci-trace
carrier `ricTraceSection g s S` against `∇S`:
```
bochnerFoldGroupSum g s S V (bochnerGroupElt3) = ⟨ricTraceSection g s S, ∇S⟩_{L²}.
```

This is an **integral** identity, NOT a pointwise carrier identity: the group-`3` carrier
`bochnerGroupElt3 = (iii + iv) − v` splits into the Ricci-direction part `bochnerGroupElt3NegV` (term `−v`,
whose frame sum over `a` is *pointwise* the leading-slot Ricci trace of `∇S`,
`parsevalFrameSum_ricSlot0_eq_sum_negV`) and the frame-derivative (tension-field) part
`bochnerGroupElt3IiiIv` (terms `iii + iv`, whose frame double-sum integral *vanishes* only after the
frame-summed second-Bianchi covariant integration by parts,
`bochnerGroupElt3IiiIv_frameSum_integral_eq_zero`).  The pointwise carrier split is `false` for `s > 0`
(the tension-field terms do not cancel at a point), so the fold must be routed through the integral.

Assembly: the carrier double sum splits by `tensorInnerPointwise` additivity and `integral_sub` into the
`iii + iv` integral (`= 0`) plus the `−v` double sum, which `fold_assembly` (`Named := ricTraceSection
g s S`, `Elt := bochnerGroupElt3NegV`) collapses to `⟨ricTraceSection g s S, ∇S⟩_{L²}` over the *pointwise*
Ricci-direction hook `parsevalFrameSum_ricSlot0_eq_sum_negV`.  Consumers transitively depend on the
tension-field nullity's `sorryAx`. -/
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
        (covGrad (I := I) (M := M) g 0 s S).toFun := by
  classical
  -- Per-`(a, b)` integrability of the two sub-carrier integrands (the Cc cross-pairings).
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
  -- The pointwise carrier split, turned into a per-`(a, b)` integral split.
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
  -- The full group-`3` double sum splits as the `iii + iv` double sum plus the `−v` double sum.
  have hsplit : bochnerFoldGroupSum (I := I) (M := M) g s S V
        (bochnerGroupElt3 (I := I) (M := M) g s S) =
      (∑ a : Fin N, ∑ b : Fin N,
          ∫ x, tensorInnerPointwise (I := I) (M := M) g 0 s x
              (TensorRSSpace.toModel
                (bochnerGroupElt3IiiIv (I := I) (M := M) g s S (V a) (V b) x))
              (TensorRSSpace.toModel (bochnerGradSlot0 (I := I) (M := M) g s S (V b) x))
            ∂(riemannianVolumeMeasure (I := I) (M := M) g)) +
        bochnerFoldGroupSum (I := I) (M := M) g s S V
          (bochnerGroupElt3NegV (I := I) (M := M) g s S) := by
    rw [bochnerFoldGroupSum, bochnerFoldGroupSum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    exact hintegral a b
  rw [hsplit, bochnerGroupElt3IiiIv_frameSum_integral_eq_zero (I := I) (M := M) g s S V hV hPar,
    zero_add]
  -- The `−v` double sum collapses to the Ricci-trace pairing via the pointwise fold assembly.
  refine (fold_assembly (I := I) (M := M) g s S V hV hPar
    (ricTraceSection (I := I) (M := M) g s S)
    (bochnerGroupElt3NegV (I := I) (M := M) g s S)
    (fun b x => parsevalFrameSum_ricSlot0_eq_sum_negV (I := I) (M := M) g s S V hPar b x)
    (fun a b => hintNegV a b)).symm

/-- **The integrated Parseval-frame diagonal differentiated-curvature trace pairing plus the group-`1`
and group-`4` double sums equals the differentiated-curvature operator-field action (the genuine
`nablaTensor0SCurv`-form curvature-commutator kernel of the group-`2` + group-`4` root).** For a fixed
Parseval frame family, the frame double sum of the integral of the `(0, s)` fibre pairing of the
`tensor0SAsRS`-wrap of the diagonal differentiated `(0, s)`-tensor curvature object
`nablaTensor0SCurv g s (V a) (V a) (V b) A` (`A y := S.toSection y (unit)`) against `∇_{V b} S`, plus the
group-`1` double sum `bochnerFoldGroupSum (bochnerGroupElt1)` and the group-`4` double sum
`bochnerFoldGroupSum (bochnerGroupElt4)`, equals the single `L²` pairing of the differentiated curvature
operator-field action `appCc (covGrad Φ₀) S` (`Φ₀ := curvOpField g s`) against `∇S`:
```
(∑_a ∑_b ∫ ⟨tensor0SAsRS (nablaTensor0SCurv g s (V a) (V a) (V b) A), ∇_{V b} S⟩_g ∂μ)
  + bochnerFoldGroupSum g s S V (bochnerGroupElt1) + bochnerFoldGroupSum g s S V (bochnerGroupElt4)
  = ⟨appCc (covGrad (curvOpField g s)) S, ∇S⟩_{L²}.
```

This is the genuine, irreducible, near-bedrock curvature-commutator kernel of the rank-`0` Bochner
group-`2` + group-`4` root, re-expressed through the connectors on the frame-free **`nablaTensor0SCurv`**
differentiated-curvature object: the integrated identification of the frame-summed differentiated-curvature
trace `∑_a (∇_{V a} R^{(s)})(V a, V b) S` with the differentiated curvature operator-field action
`appCc (covGrad Φ₀) S` (`Φ₀ := curvOpField g s`, `appCc_curvOpField_eq_pureRGenuineDiffOp`,
`nablaTensor0SCurv_apply_eval`), with the group-`1` carrier `R(V a, V b)(∇_{V a} S)` and the symmetric
second-order group-`4` pair carried along.  The diagonal differentiated-curvature trace is the form the
now-committed Parseval = orthonormal diagonal-trace bridge
`parsevalFrame_eq_orthoFrame_diag_nablaTensor0SCurv` (`CurvatureOperator.ParsevalFrameDiffCurvatureTrace`)
acts on; through it the slot-wise divergence-of-curvature transfer
`frame_sum_nablaTensor0SCurv_diag_baseSlot_eval` and the once-contracted second Bianchi identity
`nablaCurvSec_diag_frame_trace_eq_nablaRicci_sub` fold the trace onto the differentiated-Ricci /
operator-field content, with the residual second-order pairs reorganized through the section Ricci identity
`tensorSecondCovDeriv_antisymm_eq_riemannOp` and integrated by parts
(`integral_frameSummed_covDeriv_combined_eq_zero`).  It is *false* for an arbitrary section in place of the
differentiated curvature trace (the `(∇R) S` content is genuinely present), so it genuinely uses `R`,
`∇R`, the Parseval reproduction `hPar`, and the second-order frame structure.  This is GENERAL
Parseval-frame curvature content that should be promoted to a curvature file; the body is `sorry` and
consumers transitively depend on its `sorryAx`. -/
private theorem parsevalFrameSum_diagDiffCurvTrace_add_group1_group4_eq_appCc_covGrad_curvOpField
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s)
    {N : ℕ} (V : Fin N → Π b : M, TangentSpace I b)
    (hV : ∀ a, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => (⟨b, V a b⟩ : TotalSpace E (TangentSpace I))))
    (hPar : ∀ (x : M) (u : TangentSpace I x),
      (∑ a : Fin N, g.inner x (V a x) u • V a x) = u) :
    (∑ a : Fin N, ∑ b : Fin N,
        ∫ x, tensorInnerPointwise (I := I) (M := M) g 0 s x
            (TensorRSSpace.toModel
              (tensor0SAsRS (I := I) (M := M) x
                (nablaTensor0SCurv (I := I) g s ⟨fun b => V a b, hV a⟩ ⟨fun b => V a b, hV a⟩
                  ⟨fun y => V b y, hV b⟩
                  (fun y : M =>
                    (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace s I y from S.toSection y)
                      (unitZeroSec (I := I) (M := M) y)) x)))
            (TensorRSSpace.toModel (bochnerGradSlot0 (I := I) (M := M) g s S (V b) x))
          ∂(riemannianVolumeMeasure (I := I) (M := M) g)) +
      bochnerFoldGroupSum (I := I) (M := M) g s S V
          (bochnerGroupElt1 (I := I) (M := M) g s S) +
        bochnerFoldGroupSum (I := I) (M := M) g s S V
          (bochnerGroupElt4 (I := I) (M := M) g s S) =
      tensorL2Inner (I := I) (M := M) g 0 (s + 1)
        (appCc (I := I) (M := M) g s (s + 1)
          (covGrad (I := I) (M := M) g s s (curvOpField (I := I) (M := M) g s)) S).toFun
        (covGrad (I := I) (M := M) g 0 s S).toFun := by
  classical
  -- The `nablaTensor0SCurv`-form tension-field nullity kernel (above): the diagonal trace double sum
  -- `T` equals `group2_sum − group1_sum`.
  have hk1 := parsevalFrameSum_diagDiffCurvTrace_pairing_eq_group2_sub_group1
    (I := I) (M := M) g s S V hV hPar
  -- The differentiated-curvature operator-field identification (fact 2 of the combined root):
  -- `group2_sum + group4_sum = ⟨appCc (covGrad Φ₀) S, ∇S⟩_{L²}`.
  have hk2 :=
    (parsevalFrameSum_bochnerFold_combined_secondBianchi_root
      (I := I) (M := M) g s S V hV hPar).2
  -- `T + group1_sum + group4_sum = (group2_sum − group1_sum) + group1_sum + group4_sum
  --   = group2_sum + group4_sum = ⟨appCc (covGrad Φ₀) S, ∇S⟩_{L²}`.
  linarith [hk1, hk2]

/-- **The group-`2` covariant-curvature divergence plus group-`4` second-order pair equals the
differentiated-curvature operator-field action (the genuine deep curvature-commutator root of the
rank-`0` Bochner divergence, raw-carrier form).** For a fixed Parseval frame family, the group-`2`
double sum `bochnerFoldGroupSum (bochnerGroupElt2)` (the frame-summed covariant derivative of the
curvature operator `∑_a ∇_{V a}(R(V a, V b) S)` paired against `∇_{V b} S`) plus the group-`4` double
sum (the symmetric second-order pair `−∇²_{∇_{V b} V a, V a} S − ∇²_{V a, ∇_{V b} V a} S` read against
`∇_{V b} S`) equals the single `L²` pairing of the differentiated curvature operator-field action
`appCc (covGrad Φ₀) S` (`Φ₀ := curvOpField g s`) against `∇S`:
```
bochnerFoldGroupSum g s S V (bochnerGroupElt2) + bochnerFoldGroupSum g s S V (bochnerGroupElt4)
  = ⟨appCc (covGrad (curvOpField g s)) S, ∇S⟩_{L²}.
```

This is the genuinely-deep curvature-commutator content of the rank-`0` Bochner divergence root.  The
group-`2` carrier reorganizes through the covariant-Leibniz regrouping
`bochnerFoldGroupSum_elt3IiiIv_eq_nablaDiffCurvTrace_split` (PROVEN above, `nablaTensor0SCurv_def`):
`group2_sum = D − group3IiiIv_sum + group1_sum`, where `D := ∑_a ∑_b ∫ ⟨nablaDiffCurvTrace, ∇_{V b} S⟩`;
the tension-field double sum vanishes (`parsevalFrameSum_tensionFieldCurvatureDivergence_eq_zero`,
ROOT1), so `group2_sum = D + group1_sum`; reading the differentiated-curvature trace through the connector
(`tensorInnerScalar_nablaDiffCurvTrace_eq_tensorInnerPointwise_nablaTensor0SCurv`) makes `D` the
diagonal `nablaTensor0SCurv` trace double sum, and the genuine `nablaTensor0SCurv`-form kernel
`parsevalFrameSum_diagDiffCurvTrace_add_group1_group4_eq_appCc_covGrad_curvOpField` (the diagonal
differentiated-curvature trace plus the group-`1` and group-`4` double sums equals the operator-field
`(∇R) S` action — the integrated second-Bianchi / divergence-of-curvature content the Parseval =
orthonormal bridge and Theorems A/B discharge) collapses the whole to
`⟨appCc (covGrad (curvOpField g s)) S, ∇S⟩_{L²}`.  It is *false* for an arbitrary section in place of the
differentiated curvature trace (the `(∇R) S` content is genuinely present), so it genuinely uses `R`,
`∇R`, the Parseval reproduction `hPar`, and the second-order frame structure (all carried by the kernel).
This is GENERAL Parseval-frame curvature content; consumers transitively depend on the kernel's `sorryAx`. -/
private theorem parsevalFrameSum_group2_add_group4_eq_diffCurvOpFieldAction
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
  -- The covariant-Leibniz regrouping of the tension-field carrier (the sorry-free system bridge):
  -- `group3IiiIv_sum = D − group2_sum + group1_sum`, hence `group2_sum = D − group3IiiIv_sum + group1_sum`.
  have hsplit := bochnerFoldGroupSum_elt3IiiIv_eq_nablaDiffCurvTrace_split
    (I := I) (M := M) g s S V hV
  -- The tension-field double sum vanishes (ROOT1).
  have hbianchi :
      bochnerFoldGroupSum (I := I) (M := M) g s S V
          (bochnerGroupElt3IiiIv (I := I) (M := M) g s S) = 0 :=
    parsevalFrameSum_tensionFieldCurvatureDivergence_eq_zero (I := I) (M := M) g s S V hV hPar
  -- The connector identifies the differentiated-curvature trace double sum `D` with the diagonal
  -- `nablaTensor0SCurv` trace double sum.
  have hD : (∑ a : Fin N, ∑ b : Fin N,
        ∫ x, tensorInnerScalar (I := I) (M := M) g 0 s
            (nablaDiffCurvTraceCc (I := I) (M := M) g s S (hV a) (hV b)).toSection
            (bochnerGradSlot0Cc (I := I) (M := M) g s S (hV b)).toSection x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g)) =
      ∑ a : Fin N, ∑ b : Fin N,
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
    refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    exact tensorInnerScalar_nablaDiffCurvTrace_eq_tensorInnerPointwise_nablaTensor0SCurv
      (I := I) (M := M) g s S (hV a) (hV b) x
  -- The genuine `nablaTensor0SCurv`-form curvature-commutator kernel: the diagonal differentiated-curvature
  -- trace `T` plus the group-`1` and group-`4` double sums equals the operator-field `(∇R) S` action.
  have hker := parsevalFrameSum_diagDiffCurvTrace_add_group1_group4_eq_appCc_covGrad_curvOpField
    (I := I) (M := M) g s S V hV hPar
  -- `group2_sum = D − group3IiiIv_sum + group1_sum = D + group1_sum` (ROOT1), `D = T` (connector), so
  -- `group2_sum + group4_sum = (T + group1_sum) + group4_sum = ⟨appCc (∇Φ₀) S, ∇S⟩` by the kernel.
  linarith [hsplit, hbianchi, hD, hker]

/-- **The group-`2` IBP residue plus group-`4` second-order pair equals the differentiated-curvature
operator-field action (the genuine `∇R`-trace curvature-commutator core, compact operator-field form).**
For a fixed Parseval frame family, the frame double sum of the group-`2` integration-by-parts residue
`bochnerGroup2Residue` plus the group-`4` double sum equals the single `L²` pairing of the differentiated
curvature operator-field action `appCc (∇Φ₀) S` (`Φ₀ := curvOpField g s`) against `∇S`:
```
(∑_b ∑_a ∫ bochnerGroup2Residue) + bochnerFoldGroupSum (bochnerGroupElt4)
  = ⟨appCc (covGrad (curvOpField g s)) S, ∇S⟩_{L²}.
```

This is the genuinely-deep curvature-commutator content of the rank-`0` Bochner divergence root, the
compact operator-field core of which the pre-split B-rule form
`parsevalFrameSum_group2Residue_add_group4_eq_diffCurvSplit_core` is the thin re-collection.  The group-`2`
covariant derivative `∇_{V a}(·)` has already been integrated by parts off into the residue
`bochnerGroup2Residue` by the frame-summed engine (`bochnerFoldGroupSum_elt2_eq_residueSum`,
`integral_frameSummed_covDeriv_combined_eq_zero`); what remains is the genuine curvature-commutator
reorganization, *strictly closer to the tensor-bundle bedrock*: the residue's second covariant derivative
`∇_{V a}(∇_{V b} S)`, paired against `R(V a, V b) S`, plus the group-`4` symmetric pair, is reorganized
through the section-level Ricci identity `tensorSecondCovDeriv_antisymm_eq_riemannOp` and the frame-summed
differentiated tensor curvature transfer `frame_sum_nablaTensor0SCurv_baseSlot_eval` (the frame-independent
second Bianchi `nablaTensor0SCurv_cyclic_eq_zero` traced against the Parseval frame
`parseval_family_sum_bilin_eq`, `∑_a V_a ⊗ V_a = g⁻¹`) into the differentiated curvature coefficient
`(∇R) S` (`appCc_curvOpField_eq_pureRGenuineDiffOp`, `nablaTensor0SCurv_apply_eval`).  It is *false* for an
arbitrary section in place of the differentiated curvature trace (the `(∇R) S` content is genuinely
present), so it genuinely uses `R`, `∇R`, the Parseval reproduction `hPar`, and the second-order frame
structure.  This is GENERAL Parseval-frame curvature content that should be promoted to a curvature file;
the body is `sorry` and consumers transitively depend on its `sorryAx`. -/
private theorem parsevalFrameSum_group2Residue_add_group4_eq_appCc_nablaCurvOpField_core
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
        (covGrad (I := I) (M := M) g 0 s S).toFun := by
  classical
  -- Undo the group-`2` frame-summed covariant integration by parts (sorry-free):
  -- `∑_b ∑_a ∫ bochnerGroup2Residue = bochnerFoldGroupSum (bochnerGroupElt2)`.
  rw [← bochnerFoldGroupSum_elt2_eq_residueSum (I := I) (M := M) g s S V hV]
  -- The genuine curvature-commutator content, in raw group-`2` + group-`4` carrier form: the
  -- frame-summed divergence of the curvature operator `∑_a ∇_{V a}(R(V a, V b) ·)` plus the symmetric
  -- second-order group-`4` pair equals the differentiated curvature operator-field action `(∇R) S`.
  -- This is the second-Bianchi / `riemannOp`-commutator collapse of the order-`2` carriers onto the
  -- single `(∇R)`-trace, the genuine deep curvature-commutator root.
  exact parsevalFrameSum_group2_add_group4_eq_diffCurvOpFieldAction
    (I := I) (M := M) g s S V hV hPar

/-- **The group-`2` IBP residue plus group-`4` second-order pair, pre-split into the two operator-field
pairings (the differentiated-curvature reorganization, B-rule normal form).** For a fixed Parseval frame
family, the frame double sum of the group-`2` integration-by-parts residue `bochnerGroup2Residue`
(`= −(⟨R(V a, V b) S, ∇_{V a}(∇_{V b} S)⟩ + ⟨R(V a, V b) S, ∇_{V b} S⟩ · divᵍ (V a))`) plus the group-`4`
double sum (the symmetric second-order pair `−∇²_{∇_{V b} V a, V a} S − ∇²_{V a, ∇_{V b} V a} S` read
against `∇_{V b} S`) equals the differentiated-curvature operator-field action, pre-split by the
operator-field covariant Leibniz B-rule into the gradient-of-base pairing minus the passenger-slot pairing:
```
(∑_b ∑_a ∫ bochnerGroup2Residue) + bochnerFoldGroupSum g s S V (bochnerGroupElt4)
  = ⟨∇(pureRGenuineDiffOp g 0 s S), ∇S⟩_{L²} − ⟨appCc (slotExtend Φ₀) (∇S), ∇S⟩_{L²},   Φ₀ := curvOpField g s.
```

This is the public pre-split form of the more-primitive compact operator-field core
`parsevalFrameSum_group2Residue_add_group4_eq_appCc_nablaCurvOpField_core` (which carries the genuine
curvature-commutator `∇R`-trace content); the pre-split is the thin B-rule re-collection of the same core.
The operator-field covariant Leibniz pairing split `tensorL2Inner_covGrad_appCc_eq_add` (`Φ := Φ₀`,
`W := S`, `T := ∇S`) reads `⟨∇(appCc Φ₀ S), ∇S⟩ = ⟨appCc (∇Φ₀) S, ∇S⟩ + ⟨appCc (slotExtend Φ₀)(∇S), ∇S⟩`,
and the order-`0` action `appCc Φ₀ S = pureRGenuineDiffOp g 0 s S` (`appCc_curvOpField_eq_pureRGenuineDiffOp`)
identifies the gradient-of-base term, so the core's `⟨appCc (∇Φ₀) S, ∇S⟩` re-collects to
`⟨∇(pureRᵍ S), ∇S⟩ − ⟨appCc (slotExtend Φ₀)(∇S), ∇S⟩`.  Consumers transitively depend on the core's
`sorryAx`. -/
private theorem parsevalFrameSum_group2Residue_add_group4_eq_diffCurvSplit_core
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
  -- B-rule re-collection of the compact operator-field core.  The operator-field covariant Leibniz split
  -- (`tensorL2Inner_covGrad_appCc_eq_add`) reads `⟨∇(appCc Φ₀ S), ∇S⟩` as the differentiated-action pairing
  -- `⟨appCc (∇Φ₀) S, ∇S⟩` plus the passenger-slot pairing; the order-`0` action `appCc Φ₀ S = pureRᵍ S`
  -- (`appCc_curvOpField_eq_pureRGenuineDiffOp`) supplies the gradient-of-base term.
  have hcore := parsevalFrameSum_group2Residue_add_group4_eq_appCc_nablaCurvOpField_core
    (I := I) (M := M) g s S V hV hPar
  have hbase : appCc (I := I) (M := M) g s s (curvOpField (I := I) (M := M) g s) S =
      pureRGenuineDiffOp (I := I) (M := M) g 0 s S :=
    appCc_curvOpField_eq_pureRGenuineDiffOp (I := I) (M := M) g s S
  have hsplit := tensorL2Inner_covGrad_appCc_eq_add (I := I) (M := M) g s s
    (curvOpField (I := I) (M := M) g s) S (covGrad (I := I) (M := M) g 0 s S)
  rw [hbase] at hsplit
  linarith [hcore, hsplit]

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
differentiated-curvature operator-field form.  It is the **thin B-rule re-collection** of the bedrock-near
pre-split core `parsevalFrameSum_group2Residue_add_group4_eq_diffCurvSplit_core` (the genuine
curvature-commutator content): the operator-field covariant Leibniz pairing split
`tensorL2Inner_covGrad_appCc_eq_add` (`Φ := Φ₀`, `W := S`, `T := ∇S`) reads
`⟨∇(appCc Φ₀ S), ∇S⟩ = ⟨appCc (∇Φ₀) S, ∇S⟩ + ⟨appCc (slotExtend Φ₀)(∇S), ∇S⟩`, and the order-`0` action
`appCc Φ₀ S = pureRGenuineDiffOp g 0 s S` (`appCc_curvOpField_eq_pureRGenuineDiffOp`) identifies the
gradient-of-base term, so the core's `⟨∇(pureRᵍ S), ∇S⟩ − ⟨appCc (slotExtend Φ₀)(∇S), ∇S⟩` re-collects to
`⟨appCc (covGrad Φ₀) S, ∇S⟩`.  Consumers transitively depend on the core's `sorryAx`. -/
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
        (covGrad (I := I) (M := M) g 0 s S).toFun := by
  classical
  -- B-rule re-collection of the bedrock-near pre-split core.  The operator-field covariant Leibniz
  -- split (`tensorL2Inner_covGrad_appCc_eq_add`) reads `⟨∇(appCc Φ₀ S), ∇S⟩` as the sum of the
  -- differentiated-action pairing `⟨appCc (∇Φ₀) S, ∇S⟩` and the passenger-slot pairing; the order-`0`
  -- action `appCc Φ₀ S = pureRᵍ S` (`appCc_curvOpField_eq_pureRGenuineDiffOp`) supplies the
  -- gradient-of-base term, so the core's `⟨∇pureRᵍ, ∇S⟩ − ⟨appCc (slotExtend Φ₀) ∇S, ∇S⟩` re-collects.
  have hcore := parsevalFrameSum_group2Residue_add_group4_eq_diffCurvSplit_core
    (I := I) (M := M) g s S V hV hPar
  have hbase : appCc (I := I) (M := M) g s s (curvOpField (I := I) (M := M) g s) S =
      pureRGenuineDiffOp (I := I) (M := M) g 0 s S :=
    appCc_curvOpField_eq_pureRGenuineDiffOp (I := I) (M := M) g s S
  have hsplit := tensorL2Inner_covGrad_appCc_eq_add (I := I) (M := M) g s s
    (curvOpField (I := I) (M := M) g s) S (covGrad (I := I) (M := M) g 0 s S)
  rw [hbase] at hsplit
  linarith [hcore, hsplit]

/-- **The differentiated-curvature reorganization, pre-split into the two operator-field pairings (the
B-rule normal form).** For a fixed Parseval frame family,
```
(∑_b ∑_a ∫ bochnerGroup2Residue) + bochnerFoldGroupSum g s S V (bochnerGroupElt4)
  = ⟨∇(pureRGenuineDiffOp g 0 s S), ∇S⟩_{L²} − ⟨appCc (slotExtend Φ₀) (∇S), ∇S⟩_{L²},   Φ₀ := curvOpField g s.
```
This is the public re-export of the bedrock-near pre-split core
`parsevalFrameSum_group2Residue_add_group4_eq_diffCurvSplit_core` (same value, pre-split form); the
compact operator-field form `…_eq_appCc_covGrad_curvOpField_BRIDGE` is itself the thin B-rule
re-collection of the same core (the operator-field pairing split `tensorL2Inner_covGrad_appCc_eq_add`
with order-`0` action `appCc Φ₀ S = pureRGenuineDiffOp g 0 s S`).  Consumers transitively depend on the
core's `sorryAx`. -/
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
        (covGrad (I := I) (M := M) g 0 s S).toFun :=
  parsevalFrameSum_group2Residue_add_group4_eq_diffCurvSplit_core
    (I := I) (M := M) g s S V hV hPar

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
