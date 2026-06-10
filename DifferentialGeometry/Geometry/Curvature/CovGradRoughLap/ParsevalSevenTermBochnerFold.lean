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
* `bochnerFoldGroupSum2` (term ii, `∇_{V a}(R(V a, V b) S)`) → `0` (a per-direction total covariant divergence
  over the closed manifold);
* `bochnerFoldGroupSum3` (terms iii + iv − v) → the leading-slot Ricci-trace pairing
  `⟨ricTraceSection g s S, ∇S⟩_{L²}`;
* `bochnerFoldGroupSum4` (− term vi − term vii, the symmetric second-order pair) → the operator-field
  integration-by-parts residue `−⟨appCc (slotExtend Φ₀) (∇S), ∇S⟩_{L²} + ⟨∇(pureRGenuineDiffOp g 0 s S),
  ∇S⟩_{L²}`.

The fifth fold `bochnerFold_sevenTermSum_eq_pointwiseTensorCurvPairing` is the fixed-Parseval-family bridge:
the sum of the four group double-sums equals the curvature cross-pairing `⟨pointwiseTensorCurv g s S, ∇S⟩_{L²}`
(through the rough-Laplacian Parseval trace `rawTensorConnLapSmooth_toSection_eq_parseval_secondCovDeriv_sum`,
the slot-`0` fibre Parseval expansion `tensorInnerPointwise_succ_eq_parseval_sum_slot0`, and the seven-term
carrier identity).

All five carry a `sorry` body — they are the genuine more-primitive sub-identities of the rank-`0` Bochner
deep root; the integrated nullity `movingFrameNullity_diffCurvOpField_leaf`
(`DifferentiatedCurvatureOperatorFieldIdentification`) assembles over them.  Consumers transitively depend on
their `sorryAx`.
-/

noncomputable section

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

/-- **Fold 2 (term ii → 0).** For a fixed Parseval frame family, the group-`2` double sum (the slot-`0`
carrier `∇_{V a}(R(V a, V b) S)`) vanishes: per fixed direction `V a` it is a total covariant divergence over
the closed manifold (`loweredCovDeriv_bracketChannel_combined_isDivergence`, `BracketDivergenceForm`;
lowered ↔ unlowered first slot `loweredCovDerivAlongVF_firstSlot_eq_lower_covApply`).  The body is `sorry`;
consumers transitively depend on its `sorryAx`. -/
theorem bochnerFold_group2_eq_zero
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s)
    {N : ℕ} (V : Fin N → Π b : M, TangentSpace I b)
    (hV : ∀ a, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => (⟨b, V a b⟩ : TotalSpace E (TangentSpace I))))
    (hPar : ∀ (x : M) (u : TangentSpace I x),
      (∑ a : Fin N, g.inner x (V a x) u • V a x) = u) :
    bochnerFoldGroupSum (I := I) (M := M) g s S V
        (bochnerGroupElt2 (I := I) (M := M) g s S) = 0 :=
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

/-- **Fold 4 (− term vi − term vii → operator-field IBP residue).** For a fixed Parseval frame family, the
group-`4` double sum (the symmetric second-order pair `−∇²_{∇_{V b} V a, V a} S − ∇²_{V a, ∇_{V b} V a} S`)
equals the operator-field integration-by-parts residue
```
∑_a ∑_b ∫ ⟨[− ∇²_{∇_{V b} V a, V a} S − ∇²_{V a, ∇_{V b} V a} S]·slot0, slot0_{V b}(∇S)⟩
  = −⟨appCc (slotExtend Φ₀) (∇S), ∇S⟩_{L²} + ⟨∇(pureRGenuineDiffOp g 0 s S), ∇S⟩_{L²},
```
`Φ₀ := curvOpField g s`.  The genuine content is the slot-extended operator-field B-rule paired against `∇S`
(`tensorL2Inner_covGrad_eq_neg_tensorL2Inner_rawConnLap_gen`, the gradient-against-gradient Green identity).
The body is `sorry`; consumers transitively depend on its `sorryAx`. -/
theorem bochnerFold_group4_eq_slotExtend_residue
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s)
    {N : ℕ} (V : Fin N → Π b : M, TangentSpace I b)
    (hV : ∀ a, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => (⟨b, V a b⟩ : TotalSpace E (TangentSpace I))))
    (hPar : ∀ (x : M) (u : TangentSpace I x),
      (∑ a : Fin N, g.inner x (V a x) u • V a x) = u) :
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
