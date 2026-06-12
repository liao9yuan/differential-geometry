import DifferentialGeometry.Geometry.Flow.RicciFlow.Pullback.Cartan.LieDerivSectionCartan
import DifferentialGeometry.Geometry.Connection.ConnectionDifferenceFieldJets
import DifferentialGeometry.Geometry.Connection.TensorNabla.VectorFieldCovariantGradientSlotTelescope
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.MetricContractionLeibnizGrid
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.QuadraticProductRfnsGrid
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CrossCorrectionParallelContraction
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.DeTurckCartanRfnsBilinearProduct
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CometricDoubleTraceParallelContraction
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.GagliardoNirenbergProductTwoArm
import DifferentialGeometry.Geometry.Connection.TensorNabla.VectorFieldCovariantGradientDifference
import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.SharpOrderRealizedJetEmbedding
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.PointwiseToL2Packaging

/-! # The covariant top/rest split of the symmetrised-lowered DeTurck-field difference

For a closed (compact, boundaryless) smooth Riemannian manifold `(M, g₀)` modelled on a real
inner-product space `E`, this file supplies the **deep gauge covariant-Leibniz content** of the Lie
half of the Ricci–DeTurck linearization: the order-`j` covariant top/rest split of the difference of
two metrics' symmetrised covariant lowerings of the DeTurck vector field,
`symLoweredDeTurckVFRetagG0 g₀ g₁ g_bg − symLoweredDeTurckVFRetagG0 g₀ g₂ g_bg`.

This is the **gauge analogue (parity-depth)** of the curvature half's connection-level
quadratic-Cross top/rest split `crossCorrectionSection_iteratedCovGrad_topRest_split`
(`ConnectionDifferenceFieldJets.lean`, itself a posited primitive), and rides the **same sorry-free
covariant-calculus engine**:

* the metric-contraction binomial covariant-Leibniz `rfns` grid of a `DiffBilinOp`
  (`DiffBilinOp.exists_rfns_iteratedCovGrad_singleSum_le`,
  `Analysis/Spectral/Tensor/CovGrad/MetricContractionLeibnizGrid.lean`);
* the parallel two-section bilinear-product `rfns` grid of an `RfnsBilinearProduct`
  (`RfnsBilinearProduct.exists_rfns_iteratedCovGrad_prod_diagGrid_le`,
  `Analysis/Spectral/Tensor/CovGrad/QuadraticProductRfnsGrid.lean`);
* the realized-Koszul jet domination `koszulCombSection_iteratedCovGrad_rfns_le` and the
  fibre-small-gated lowered connection-difference jet bound
  `exists_riemannianFiberNormSq_iteratedCovGrad_loweredConnDiff_le_jetSum`
  (`ConnectionDifferenceFieldJets.lean`).

## Why the difference splits this way

The DeTurck field `W = deTurckVF g g_bg` is the metric `g`-trace of the connection difference
`connDiff (g, g_bg)` (`deTurckVF_apply_eq`), a `g⁻¹·∂g`-type field.  `symLoweredDeTurckVF g g_bg` is
the symmetrised `g`-lowering of its covariant gradient `∇W` (`cartanRHSBilin`), so it is a
covariant-Faà-di-Bruno contraction of the metric jet, **order-`≤2` in the metric**: the value jet,
the first-derivative jets riding (through the `g₀`-lowered Koszul form) on the `w`-jets, and a genuine
quadratic-in-difference `D∘D` part from the bilinear connection-difference product of two independently
varying gauge fields.

The difference of two such contractions telescopes (one difference factor per term).  The **`Top`**
part collects the difference-factor `w := realizeSymmCcTensor g₀ (T₁ − T₂)` jets through the
rank-reducing contraction and the two-section bilinear-product grid (the high derivative landing on
either factor, folded with the fixed factor sup and the metric-built `≤2`-jet coefficient into the
family-uniform `Cd`); the **`Rest`** part keeps the top coefficient jet on the *fixed pair* `T₁, T₂`
against the difference's order-`a` chart-Sobolev `C⁰` mass (the supercritical embedding `ha`), with the
`(g₀, a, j)`-dependent cross coefficient `Cd` (a fixed universal cross constant is refuted by the `T²`
volume-scaling family — the embedding constant blows up as `vol(M) → 0`).

Unlike the curvature half — order-zero-immune (Palatini: `Γ(g₁) = Γ(g₂)` near `x` forces
`Ric(g₁) = Ric(g₂)` near `x`) — the Lie summand depends on the metric at **order zero** (the trace
weight `g⁻¹` and the value of the perturbation), so the difference arm is the **0-jet-inclusive**
order-`≤ j+2` covariant jet sum of `w`: the order-`0` jet `rfns(w)` is included.  A 0-jet-free arm is
Lean-refuted FALSE (the flat-`T²` counterexample documented at the leaf
`lieDerivDiff_connLevel_topRestSplit`). -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open Bundle Manifold Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry
namespace PDE
namespace DeTurck

open DifferentialGeometry
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.Pullback
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck in
/-- **The `g₀`-cometric lowering-slot pairing trace** of a `(0,2)`-coefficient `S` against a
`(0,2)`-carrier `T`: the section with fibre `(v, w) ↦ ∑ₖ S(♯b^k, w) · T(v, b_k)` — the
`g₀`-cometric single trace pairing `S`'s first slot against `T`'s second slot.  Built from the
proven parallel calculus: the bare tensor product, a slot permutation, the cometric double-trace
contraction, and a final slot swap. -/
private def loweringPairTrace (g₀ : SmoothRiemannianMetric I M)
    (S T : Integral.L2.SmoothCcTensor g₀ 0 2) : Integral.L2.SmoothCcTensor g₀ 0 2 :=
  permuteCcTensor (I := I) g₀ (Equiv.swap 0 1)
    (Integral.Connection.cometricDoubleTraceRecOp (I := I) g₀ 2 0
      (permuteCcTensor (I := I) g₀ c[(1 : Fin 4), 2, 3]
        ((Integral.Connection.bareTensorRfnsBilinearProduct (I := I) g₀ 2 2).prod
          (a := 0) (b := 0) S T)))

set_option linter.unusedSectionVars false in
/-- **The unit-model fibre value of the lowering-slot pairing trace**: the cometric frame sum
`∑ₖ Sₘ(♯b^k, v 1) · Tₘ(v 0, b_k)` of the two factors' unit-model values. -/
private theorem loweringPairTrace_unitModel_apply (g₀ : SmoothRiemannianMetric I M)
    (S T : Integral.L2.SmoothCcTensor g₀ 0 2) (x : M) (v : Fin 2 → TangentSpace I x) :
    Tensor0SBundle.Tensor0SSpace.toModel
        ((loweringPairTrace (I := I) g₀ S T).toSection x
          (ContinuousMultilinearMap.constOfIsEmpty ℝ
            (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))) v =
      ∑ k : Fin (Module.finrank ℝ E),
        Tensor0SBundle.Tensor0SSpace.toModel
            ((S.toSection x)
              (ContinuousMultilinearMap.constOfIsEmpty ℝ
                (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ)))
            ![(Integral.Connection.cometricReadingModel (I := I) g₀ x
                (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                  ((Module.finBasis ℝ E).cDualBasis k)) : TangentSpace I x), v 1] *
          Tensor0SBundle.Tensor0SSpace.toModel
            ((T.toSection x)
              (ContinuousMultilinearMap.constOfIsEmpty ℝ
                (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ)))
            ![v 0, ((Module.finBasis ℝ E) k : TangentSpace I x)] := by
  classical
  set U := (Integral.Connection.bareTensorRfnsBilinearProduct (I := I) g₀ 2 2).prod
    (a := 0) (b := 0) S T with hU
  set U' := permuteCcTensor (I := I) g₀ c[(1 : Fin 4), 2, 3] U with hU'
  set X := Integral.Connection.cometricDoubleTraceRecOp (I := I) g₀ 2 0 U' with hX
  -- Outer swap: read through the permuted unit model.
  have houter :
      Tensor0SBundle.Tensor0SSpace.toModel
          ((loweringPairTrace (I := I) g₀ S T).toSection x
            (ContinuousMultilinearMap.constOfIsEmpty ℝ
              (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))) v =
        Tensor0SBundle.Tensor0SSpace.toModel
          ((X.toSection x)
            (ContinuousMultilinearMap.constOfIsEmpty ℝ
              (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))) (v ∘ (Equiv.swap 0 1)) := by
    rw [show loweringPairTrace (I := I) g₀ S T =
        permuteCcTensor (I := I) g₀ (Equiv.swap 0 1) X from rfl]
    have hperm := permuteCcTensor_unitModel (I := I) g₀ (Equiv.swap 0 1) X x
    have happ := congrArg (fun (f : ContinuousMultilinearMap ℝ
        (fun _ : Fin 2 => TangentSpace I x) ℝ) => f v) hperm
    simp only [ContinuousMultilinearMap.domDomCongr_apply] at happ
    exact happ
  rw [houter]
  -- The trace fibre: post-composition by the cometric double-trace fibre operator.
  have htrace :
      (X.toSection x)
          (ContinuousMultilinearMap.constOfIsEmpty ℝ
            (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ)) =
        _root_.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck.cometricDoubleTraceFib
          (I := I) g₀ 2 x
          ((U'.toSection x)
            (ContinuousMultilinearMap.constOfIsEmpty ℝ
              (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))) := by
    rw [hX, Integral.Connection.cometricDoubleTraceRecOp_toSection]
    rfl
  rw [htrace,
    _root_.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck.cometricDoubleTraceFib_toModel]
  rw [_root_.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck.modelDoubleTrace_apply]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  -- The inner permutation and the bare product, at the traced tuple.
  have hinner :
      Tensor0SBundle.Tensor0SSpace.toModel
          ((U'.toSection x)
            (ContinuousMultilinearMap.constOfIsEmpty ℝ
              (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))) =
        ContinuousMultilinearMap.domDomCongr c[(1 : Fin 4), 2, 3]
          (Tensor0SBundle.Tensor0SSpace.toModel
            ((U.toSection x)
              (ContinuousMultilinearMap.constOfIsEmpty ℝ
                (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ)))) := by
    exact permuteCcTensor_unitModel (I := I) g₀ c[(1 : Fin 4), 2, 3] U x
  have hprodU :
      (U.toSection x)
          (ContinuousMultilinearMap.constOfIsEmpty ℝ
            (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ)) =
        ((Integral.Connection.bareTensorProdSection (I := I) g₀ S T).toSection x)
          (ContinuousMultilinearMap.constOfIsEmpty ℝ
            (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ)) := by
    rfl
  rw [hinner]
  rw [ContinuousMultilinearMap.domDomCongr_apply]
  rw [show (Tensor0SBundle.Tensor0SSpace.toModel
        ((U.toSection x)
          (ContinuousMultilinearMap.constOfIsEmpty ℝ
            (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ)))) =
      Bundle.continuousMultilinearMap.modelProduct (𝕜 := ℝ) (F := E) 2 2
        (Integral.Connection.bareUnitModel (I := I) g₀ S x)
        (Integral.Connection.bareUnitModel (I := I) g₀ T x) from by
    rw [hprodU]
    exact Integral.Connection.bareTensorProdSection_unitModel (I := I) g₀ S T x]
  rw [Bundle.continuousMultilinearMap.modelProduct_apply]
  congr 1
  · rw [Integral.Connection.bareUnitModel]
    congr 1
    funext i
    fin_cases i <;> rfl
  · rw [Integral.Connection.bareUnitModel]
    congr 1
    funext i
    fin_cases i <;> rfl

set_option linter.unusedSectionVars false in
/-- **The lowering-slot difference factors through the cometric pairing trace**: for realized
metrics `g₁, g₂` of `T₁, T₂`, the un-symmetrised half of the lowering-slot difference is the
`g₀`-cometric pairing trace of the realized metric difference `w = realizeSymm (T₁ − T₂)` against
the `g₀`-lowered fixed carrier (`gInner_sub_eq_ccTensorBilinSymm_sub` at the fibre, the cometric
frame reconstruction `sum_phi_cometric_inner_basis` undoing the lowering). -/
private theorem loweringSlotDiff_half_eq_pairTrace
    (g₀ g_bg : SmoothRiemannianMetric I M)
    (T₁ T₂ : Integral.L2.SmoothCcTensor g₀ 0 2) (g₁ g₂ : SmoothRiemannianMetric I M)
    (hr1 : ∀ (x : M) (v w : TangentSpace I x),
      g₁.inner x v w = g₀.inner x v w + ccTensorBilinSymm (I := I) g₀ T₁ x v w)
    (hr2 : ∀ (x : M) (v w : TangentSpace I x),
      g₂.inner x v w = g₀.inner x v w + ccTensorBilinSymm (I := I) g₀ T₂ x v w) :
    loweredCovGradDeTurckVFMixed (I := I) g₀ g₁ g₁ g₁ g_bg
        - loweredCovGradDeTurckVFMixed (I := I) g₀ g₂ g₁ g₁ g_bg =
      loweringPairTrace (I := I) g₀ (realizeSymmCcTensor (I := I) g₀ (T₁ - T₂))
        (loweredCovGradDeTurckVFMixed (I := I) g₀ g₀ g₁ g₁ g_bg) := by
  classical
  set w := realizeSymmCcTensor (I := I) g₀ (T₁ - T₂) with hw
  refine Integral.L2.SmoothCcTensor.ext ?_
  refine ContMDiffSection.ext (fun x => ?_)
  apply tensor0s_ext_unitZero (I := I) (M := M) (s := 2)
  apply Tensor0SBundle.Tensor0SSpace.toModel_injective
  refine ContinuousMultilinearMap.ext (fun v => ?_)
  have hunit : (unitZeroSec (I := I) (M := M) x : Tensor0SBundle.Tensor0SSpace 0 I x) =
      ContinuousMultilinearMap.constOfIsEmpty ℝ
        (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ) := rfl
  rw [hunit]
  -- LHS: the metric-difference pairing fibre.
  have hL :
      Tensor0SBundle.Tensor0SSpace.toModel
          (((loweredCovGradDeTurckVFMixed (I := I) g₀ g₁ g₁ g₁ g_bg
              - loweredCovGradDeTurckVFMixed (I := I) g₀ g₂ g₁ g₁ g_bg).toSection x)
            (ContinuousMultilinearMap.constOfIsEmpty ℝ
              (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))) v =
        ccTensorBilin (I := I) g₀ w x
          ((LeviCivita (I := I) g₁)
            (deTurckVF (I := I) g₁ g_bg : ∀ y : M, TangentSpace I y) x (v 0)) (v 1) := by
    rw [Integral.L2.SmoothCcTensor.toSection_sub, ContMDiffSection.coe_sub, Pi.sub_apply,
      ContinuousLinearMap.sub_apply, Tensor0SBundle.Tensor0SSpace.toModel_sub,
      ContinuousMultilinearMap.sub_apply,
      loweredCovGradDeTurckVFMixed_toModel_apply (I := I) g₀ g₁ g₁ g₁ g_bg x v,
      loweredCovGradDeTurckVFMixed_toModel_apply (I := I) g₀ g₂ g₁ g₁ g_bg x v,
      loweredCovGradDeTurckVFMixedBilin_apply, loweredCovGradDeTurckVFMixedBilin_apply]
    rw [gInner_sub_eq_ccTensorBilinSymm_sub (I := I) g₀ g₁ g₂ T₁ T₂ hr1 hr2 x _ (v 1)]
    rw [← realizeSymmCcTensor_ccTensorBilin_apply (I := I) g₀ (T₁ - T₂) x _ (v 1)]
  rw [hL, loweringPairTrace_unitModel_apply (I := I) g₀ w
    (loweredCovGradDeTurckVFMixed (I := I) g₀ g₀ g₁ g₁ g_bg) x v]
  -- RHS: the cometric frame sum reconstructs the raw covariant gradient slot.
  set D : TangentSpace I x := (LeviCivita (I := I) g₁)
    (deTurckVF (I := I) g₁ g_bg : ∀ y : M, TangentSpace I y) x (v 0) with hD
  set P : Fin (Module.finrank ℝ E) → TangentSpace I x := fun k =>
    Integral.Connection.cometricReadingModel (I := I) g₀ x
      (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
        ((Module.finBasis ℝ E).cDualBasis k)) with hP
  have hPdual : ∀ (k : Fin (Module.finrank ℝ E)) (u : TangentSpace I x),
      g₀.inner x (P k) u = (Module.finBasis ℝ E).repr (u : E) k := fun k u =>
    Integral.Connection.cometricReadingModel_dualBasis_inner (I := I) g₀ x k u
  have hsum := Integral.Connection.sum_phi_cometric_inner_basis (I := I) g₀ x P hPdual
    ((ccTensorBilin (I := I) g₀ w x).flip (v 1)) D
  simp only [ContinuousLinearMap.flip_apply] at hsum
  rw [← hsum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  congr 1
  · rw [ccTensorBilin_apply]
    rfl
  · rw [loweredCovGradDeTurckVFMixed_toModel_apply (I := I) g₀ g₀ g₁ g₁ g_bg x
      ![v 0, ((Module.finBasis ℝ E) k : TangentSpace I x)],
      loweredCovGradDeTurckVFMixedBilin_apply]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [hD]

/-- **(POSIT — the integrated two-arm `L²` bound of the LOWERING-slot difference.)**  The first
leg of the slot telescope `symLoweredDeTurckVFRetagG0_sub_eq_slotTelescope`
(`VectorFieldCovariantGradientSlotTelescope.lean`): the symmetrised section with un-symmetrised
fibre `(g₁ − g₂)(∇^{g₁}_v W₁, w)`, `W₁ = deTurckVF g₁ g_bg`.  The metric difference
`g₁ − g₂ = ccTensorBilinSymm g₀ (T₁ − T₂)` (via `hr1`/`hr2`) is **linear in the realized
difference** `w = realizeSymmCcTensor g₀ (T₁ − T₂)`, paired against the fixed `(g₁, g_bg)`-jet of
`∇^{g₁} W₁`; its order-`j` covariant gradient obeys the same integrated Hamilton/Moser two-arm
bound as the parent: a difference arm carrying the 0-jet-inclusive `w`-jets and a cross arm
keeping the fixed-pair `(T₁, T₂)` jets against the difference's `H^a` mass (supercritical `ha`).
Vanishes at `T₁ = T₂` realized (both arms `0`), so the bound is non-vacuous with both arms
genuinely present.  Its body is `sorry`: a posited deep child (consumers transitively depend on
`sorryAx`), the lowering-slot leg of the GN-product two-arm engine. -/
theorem deTurckVFLoweringSlotDiff_iteratedCovGrad_twoArm_le
    (g₀ g_bg : SmoothRiemannianMetric I M)
    (a : ℕ) (ha : 2 * a > Module.finrank ℝ E + 4)
    (B : ℝ) (hB : 0 ≤ B) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1 / 2) (j : ℕ) :
    ∃ Cd : ℝ, 0 ≤ Cd ∧
      ∀ (T₁ T₂ : Integral.L2.SmoothCcTensor g₀ 0 2)
        (g₁ g₂ : SmoothRiemannianMetric I M),
        (∀ (x : M) (v w : TangentSpace I x),
          g₁.inner x v w = g₀.inner x v w + ccTensorBilinSymm (I := I) g₀ T₁ x v w) →
        (∀ (x : M) (v w : TangentSpace I x),
          g₂.inner x v w = g₀.inner x v w + ccTensorBilinSymm (I := I) g₀ T₂ x v w) →
        gFibreOpBound (I := I) g₀ (fun y => ccTensorBilinSymm (I := I) g₀ T₁ y) δ →
        gFibreOpBound (I := I) g₀ (fun y => ccTensorBilinSymm (I := I) g₀ T₂ y) δ →
        ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (a + 2) T₁‖ ≤ B →
        ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (a + 2) T₂‖ ≤ B →
          ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 j
                (deTurckVFLoweringSlotDiff (I := I) g₀ g₁ g₂ g_bg)‖ ^ 2 ≤
            Cd * ∑ i ∈ Finset.range (j + 2 + 1),
                ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i
                    (realizeSymmCcTensor (I := I) g₀ (T₁ - T₂))‖ ^ 2
              + Cd * (∑ i ∈ Finset.range (j + 2 + 1),
                  (‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i T₁‖ ^ 2
                    + ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i T₂‖ ^ 2))
                * ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) a (T₁ - T₂)‖ ^ 2 :=
  sorry

/-- **(POSIT — the integrated two-arm `L²` bound of the CONNECTION-slot difference.)**  The second
leg of the slot telescope `symLoweredDeTurckVFRetagG0_sub_eq_slotTelescope`: the symmetrised
section with un-symmetrised fibre `g₂((∇^{g₁} − ∇^{g₂})_v W₁, w)`, `W₁ = deTurckVF g₁ g_bg`.  The
connection difference `∇^{g₁} − ∇^{g₂}` is the tensorial Christoffel-difference field of the pair
`(g₁, g₂)`, governed by the realized-Koszul jet algebra of `T₁ − T₂` (the `connDiff` engine of
`ConnectionDifferenceFieldJets.lean`), paired against the fixed field `W₁`; its order-`j`
covariant gradient obeys the same integrated two-arm bound: a difference arm in the
0-jet-inclusive `w`-jets and a cross arm on the fixed pair against the `H^a` mass.  Vanishes at
`T₁ = T₂` realized.  Its body is `sorry`: a posited deep child (consumers transitively depend on
`sorryAx`), the connection-slot leg of the GN-product two-arm engine. -/
theorem deTurckVFConnectionSlotDiff_iteratedCovGrad_twoArm_le
    (g₀ g_bg : SmoothRiemannianMetric I M)
    (a : ℕ) (ha : 2 * a > Module.finrank ℝ E + 4)
    (B : ℝ) (hB : 0 ≤ B) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1 / 2) (j : ℕ) :
    ∃ Cd : ℝ, 0 ≤ Cd ∧
      ∀ (T₁ T₂ : Integral.L2.SmoothCcTensor g₀ 0 2)
        (g₁ g₂ : SmoothRiemannianMetric I M),
        (∀ (x : M) (v w : TangentSpace I x),
          g₁.inner x v w = g₀.inner x v w + ccTensorBilinSymm (I := I) g₀ T₁ x v w) →
        (∀ (x : M) (v w : TangentSpace I x),
          g₂.inner x v w = g₀.inner x v w + ccTensorBilinSymm (I := I) g₀ T₂ x v w) →
        gFibreOpBound (I := I) g₀ (fun y => ccTensorBilinSymm (I := I) g₀ T₁ y) δ →
        gFibreOpBound (I := I) g₀ (fun y => ccTensorBilinSymm (I := I) g₀ T₂ y) δ →
        ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (a + 2) T₁‖ ≤ B →
        ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (a + 2) T₂‖ ≤ B →
          ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 j
                (deTurckVFConnectionSlotDiff (I := I) g₀ g₁ g₂ g_bg)‖ ^ 2 ≤
            Cd * ∑ i ∈ Finset.range (j + 2 + 1),
                ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i
                    (realizeSymmCcTensor (I := I) g₀ (T₁ - T₂))‖ ^ 2
              + Cd * (∑ i ∈ Finset.range (j + 2 + 1),
                  (‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i T₁‖ ^ 2
                    + ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i T₂‖ ^ 2))
                * ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) a (T₁ - T₂)‖ ^ 2 :=
  sorry

/-- **(POSIT — the integrated two-arm `L²` bound of the FIELD-slot difference.)**  The third leg
of the slot telescope `symLoweredDeTurckVFRetagG0_sub_eq_slotTelescope`: the symmetrised section
with un-symmetrised fibre `g₂(∇^{g₂}_v (W₁ − W₂), w)`, `Wᵢ = deTurckVF gᵢ g_bg`.  The field
difference `W₁ − W₂` is the inverse-Gram-weighted trace of the pair connection difference
(`deTurckVF_sub_apply_eq_trace_connDiff`, `VectorFieldCovariantGradientSection.lean`), the
realized-Koszul trace of `T₁ − T₂`; its `g₂`-covariant gradient lowered by `g₂` obeys the same
integrated two-arm bound: a 0-jet-inclusive difference arm in the `w`-jets and a cross arm on the
fixed pair against the `H^a` mass.  Vanishes at `T₁ = T₂` realized.  Its body is `sorry`: a
posited deep child (consumers transitively depend on `sorryAx`), the field-slot leg of the
GN-product two-arm engine. -/
theorem deTurckVFFieldSlotDiff_iteratedCovGrad_twoArm_le
    (g₀ g_bg : SmoothRiemannianMetric I M)
    (a : ℕ) (ha : 2 * a > Module.finrank ℝ E + 4)
    (B : ℝ) (hB : 0 ≤ B) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1 / 2) (j : ℕ) :
    ∃ Cd : ℝ, 0 ≤ Cd ∧
      ∀ (T₁ T₂ : Integral.L2.SmoothCcTensor g₀ 0 2)
        (g₁ g₂ : SmoothRiemannianMetric I M),
        (∀ (x : M) (v w : TangentSpace I x),
          g₁.inner x v w = g₀.inner x v w + ccTensorBilinSymm (I := I) g₀ T₁ x v w) →
        (∀ (x : M) (v w : TangentSpace I x),
          g₂.inner x v w = g₀.inner x v w + ccTensorBilinSymm (I := I) g₀ T₂ x v w) →
        gFibreOpBound (I := I) g₀ (fun y => ccTensorBilinSymm (I := I) g₀ T₁ y) δ →
        gFibreOpBound (I := I) g₀ (fun y => ccTensorBilinSymm (I := I) g₀ T₂ y) δ →
        ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (a + 2) T₁‖ ≤ B →
        ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (a + 2) T₂‖ ≤ B →
          ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 j
                (deTurckVFFieldSlotDiff (I := I) g₀ g₁ g₂ g_bg)‖ ^ 2 ≤
            Cd * ∑ i ∈ Finset.range (j + 2 + 1),
                ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i
                    (realizeSymmCcTensor (I := I) g₀ (T₁ - T₂))‖ ^ 2
              + Cd * (∑ i ∈ Finset.range (j + 2 + 1),
                  (‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i T₁‖ ^ 2
                    + ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i T₂‖ ^ 2))
                * ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) a (T₁ - T₂)‖ ^ 2 :=
  sorry

/-- **(P1b — GLUE over the slot telescope — the INTEGRATED two-arm `L²` bound of the symmetrised-lowered DeTurck-field
difference, with the 0-jet-inclusive `w`-jet difference arm.)**

The genuine deep covariant-gauge content of the Lie half, the **gauge analogue (parity-depth)** of the
curvature half's connection-level quadratic-Cross top/rest split
`crossCorrectionSection_iteratedCovGrad_topRest_split` (`ConnectionDifferenceFieldJets.lean`, itself a
posited primitive), applied to the difference of the two metrics' symmetrised covariant lowerings of
the DeTurck vector field
`diff := symLoweredDeTurckVFRetagG0 g₀ g₁ g_bg − symLoweredDeTurckVFRetagG0 g₀ g₂ g_bg` — the
**intrinsic, `∇W`-manifest representative** of the sealed `g₀`-retagged Lie-summand difference (via the
section-level Cartan identity `lieDerivRetagG0_eq_symLoweredRetagG0`).

For an anchor `g₀`, a flow background `g_bg`, an order `a`, a supercriticality hypothesis `ha`, a
uniform `H^{a+2}`-size bound `B ≥ 0`, fibre-smallness `δ < 1/2`, and **each gradient order `j`**,
there is a nonnegative constant `Cd = Cd(j)` (uniform over the perturbation family, but **per-order**:
the Lie-derivative nonlinearity doubles frequency content, so a `j`-uniform constant is refuted — on
flat `T²` a frequency-doubling perturbation family makes the left side grow like `2^{2j}ε⁴` against a
linearly-growing right side; the `4^p` moves into the Hamilton-tame constant family `C(p)`) such that
for any two `g₀`-fibre-small perturbations `T₁, T₂` with `H^{a+2}` norms `≤ B` and any two realized
metrics `g₁, g₂` of `T₁, T₂`, the squared metric `L²` norm of the order-`j` covariant gradient of
`diff` is dominated by the **integrated Hamilton/Moser two-arm sum**
```
‖∇^j diff‖² ≤ Cd · ∑_{i ≤ j+2} ‖∇^i w‖²
            + Cd · (∑_{i ≤ j+2} (‖∇^i T₁‖² + ‖∇^i T₂‖²)) · ‖(T₁ − T₂).toHs a‖²,
```
where `w := realizeSymmCcTensor g₀ (T₁ − T₂)` and `‖·‖` is the metric `L²` (semi)norm
(`‖S‖² = ∫ rfns(S) dμ`); the order-`0` jet `‖w‖²` is included.

**Why the cross arm carries the `(g₀, a, j)`-dependent `Cd`, not a fixed universal constant.**  An
earlier shape with a UNIVERSAL `(1/4)` cross-arm coefficient was refuted by the `T²` volume-scaling
family (see `PROVE_REFUTED.md`, "fixed (1/4) cross-arm"): the `H^a → C⁰` embedding constant hiding in
the boundary FdB cell (the value-level difference factor against the fixed pair's `(j+2)`-jet) is
`g₀`-dependent and unbounded as `vol(M) → 0`, so no `g₀`-uniform cross coefficient can hold.  The
corrected shape puts the statement's `(g₀, a, j)`-dependent constant `Cd` on the cross arm, mirroring
the PROVEN sibling `ricciLinearSection_covGrad_twoArm_l2Norm_le`
(`SegmentMetricCurvatureDifferenceCovJet.lean`).

**Why INTEGRATED, not pointwise.**  An earlier *pointwise* `rfns` per-`x` top/rest form (a `∇^j diff(x)
= Top + Rest` split with `rfns(Top)(x) ≤ Cd · ∑ rfns(∇^i w)(x)`) is **false** for the middle terms of
the covariant-Leibniz product at high frequency: when the differentiation order splits as `∇^p w ·
∇^{j+2−p} (fixed)` with both factors of order `≈ j/2`, neither factor is low-jet, so the on-disk
full-square `rfns` product grid cannot select the difference factor pointwise, and for `j > 2a` the
left side has frequency content `|ξ|^j` against a right side capped at `|ξ|^{2a}`.  This is
**Gagliardo–Nirenberg interpolation content** — true only after integration (the GN product inequality
trades a high jet of one factor for a low jet times an `L^∞`/`H^a` mass of the other, an `∫`-level
statement).  The bound is therefore stated at the integrated `L²`-norm-squared level, the form its
single consumer `exists_lieDerivDiff_faaDiBruno_moserTame_l2Norm_le` actually reads (no pointwise
splitting is consumed downstream — the former `riemannianFiberNormSq_add_le` recombiner only ever
recombined fibre norms into this integrated bound).

**Decomposition (the engine the proof rides).**  `symLoweredDeTurckVF g g_bg` is the symmetrised
`g`-lowering of `∇W`, `W = g`-trace of `connDiff (g, g_bg)` (`cartanRHSBilin`, `deTurckVF_apply_eq`),
so it is a covariant-Faà-di-Bruno contraction of the metric jet.  The difference telescopes one
difference factor per term: the linear-in-difference part carries the `w`-jets through the realized
Koszul form and the `g⁻¹`-trace contraction; the quadratic `D∘D` part is a bilinear product of two
independently varying gauge fields, whose `∇^j` covariant-Leibniz expansion is integrated by the
**Gagliardo–Nirenberg product two-arm engine**
`exists_integrated_iteratedCovGrad_diagonalProductGrid_twoArm_le`
(`Analysis/Spectral/Tensor/CovGrad/GagliardoNirenbergProductTwoArm.lean`): the difference-arm `Cd ·
∑ ‖∇^i w‖²` collects the high derivative on the difference factor `w` (with the fixed factor's `≤2`-jet
sup folded into `Cd`), and the cross arm `Cd · (∑ (‖∇^i T₁‖² + ‖∇^i T₂‖²)) · ‖(T₁ − T₂).toHs a‖²`
keeps the top coefficient jet on the *fixed pair* `T₁, T₂` in `L²` against the difference's order-`a`
chart-Sobolev `C⁰`/`L^∞` mass (the supercritical embedding `ha`).

**Non-vacuity.**  The difference arm carries the order-`0` value jet `‖w‖²` and the high derivative
`‖∇^{j+2} w‖²` (a zero `Cd` falsifying it whenever the difference is genuinely present), and the cross
arm carries **both** fixed-pair endpoints `T₁, T₂`.  At `g₁ = g₂` (so `T₁ = T₂` realized) the
difference vanishes (`lieDerivRetagG0_eq_symLoweredRetagG0` reduces it to the sealed Lie difference,
which vanishes by `lieDerivRetagG0_sub_toModel_eq`), `w = 0` and `‖(T₁ − T₂).toHs a‖ = 0`, so the bound
is `0 ≤ 0`.  NO value-bounded `Φ.op 0 2 w` shape, NO pointwise-`C^{>2}`-jet claim, NO
spectral-nonlinearity, NO Weyl dependence.

**Proof (glue).**  By the slot-telescope identity
`symLoweredDeTurckVFRetagG0_sub_eq_slotTelescope`
(`VectorFieldCovariantGradientSlotTelescope.lean`, PROVEN), the difference is the sum of the three
single-slot difference sections (lowering / connection / field).  Each slot carries the same
integrated two-arm bound (the three posited children
`deTurckVFLoweringSlotDiff_iteratedCovGrad_twoArm_le`,
`deTurckVFConnectionSlotDiff_iteratedCovGrad_twoArm_le`,
`deTurckVFFieldSlotDiff_iteratedCovGrad_twoArm_le` above, each `sorry`-posited — this theorem
transitively depends on their `sorryAx`); the assembly folds the norm-square of the three-term sum
(`‖X + Y + Z‖² ≤ 3(‖X‖² + ‖Y‖² + ‖Z‖²)`, the covariant gradient distributing by
`iteratedCovGrad_add`) and absorbs the `3` and the three constants into `Cd = 3(C₁ + C₂ + C₃)`. -/
theorem symLoweredDeTurckVF_iteratedCovGrad_topRest_split (g₀ g_bg : SmoothRiemannianMetric I M)
    (a : ℕ) (ha : 2 * a > Module.finrank ℝ E + 4)
    (B : ℝ) (hB : 0 ≤ B) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1 / 2) (j : ℕ) :
    ∃ Cd : ℝ, 0 ≤ Cd ∧
      ∀ (T₁ T₂ : Integral.L2.SmoothCcTensor g₀ 0 2)
        (g₁ g₂ : SmoothRiemannianMetric I M),
        (∀ (x : M) (v w : TangentSpace I x),
          g₁.inner x v w = g₀.inner x v w + ccTensorBilinSymm (I := I) g₀ T₁ x v w) →
        (∀ (x : M) (v w : TangentSpace I x),
          g₂.inner x v w = g₀.inner x v w + ccTensorBilinSymm (I := I) g₀ T₂ x v w) →
        gFibreOpBound (I := I) g₀ (fun y => ccTensorBilinSymm (I := I) g₀ T₁ y) δ →
        gFibreOpBound (I := I) g₀ (fun y => ccTensorBilinSymm (I := I) g₀ T₂ y) δ →
        ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (a + 2) T₁‖ ≤ B →
        ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (a + 2) T₂‖ ≤ B →
          ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 j
                (symLoweredDeTurckVFRetagG0 (I := I) g₀ g₁ g_bg
                    - symLoweredDeTurckVFRetagG0 (I := I) g₀ g₂ g_bg)‖ ^ 2 ≤
            Cd * ∑ i ∈ Finset.range (j + 2 + 1),
                ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i
                    (realizeSymmCcTensor (I := I) g₀ (T₁ - T₂))‖ ^ 2
              + Cd * (∑ i ∈ Finset.range (j + 2 + 1),
                  (‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i T₁‖ ^ 2
                    + ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i T₂‖ ^ 2))
                * ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) a (T₁ - T₂)‖ ^ 2 := by
  classical
  obtain ⟨C₁, hC₁, h₁⟩ := deTurckVFLoweringSlotDiff_iteratedCovGrad_twoArm_le (I := I)
    g₀ g_bg a ha B hB δ hδ0 hδ1 j
  obtain ⟨C₂, hC₂, h₂⟩ := deTurckVFConnectionSlotDiff_iteratedCovGrad_twoArm_le (I := I)
    g₀ g_bg a ha B hB δ hδ0 hδ1 j
  obtain ⟨C₃, hC₃, h₃⟩ := deTurckVFFieldSlotDiff_iteratedCovGrad_twoArm_le (I := I)
    g₀ g_bg a ha B hB δ hδ0 hδ1 j
  refine ⟨3 * (C₁ + C₂ + C₃), by positivity, ?_⟩
  intro T₁ T₂ g₁ g₂ hr1 hr2 hf1 hf2 hB1 hB2
  have e₁ := h₁ T₁ T₂ g₁ g₂ hr1 hr2 hf1 hf2 hB1 hB2
  have e₂ := h₂ T₁ T₂ g₁ g₂ hr1 hr2 hf1 hf2 hB1 hB2
  have e₃ := h₃ T₁ T₂ g₁ g₂ hr1 hr2 hf1 hf2 hB1 hB2
  rw [symLoweredDeTurckVFRetagG0_sub_eq_slotTelescope (I := I) g₀ g₁ g₂ g_bg,
    PDE.RicciFlow.iteratedCovGrad_add (I := I) g₀ 0 2 j _
      (deTurckVFFieldSlotDiff (I := I) g₀ g₁ g₂ g_bg),
    PDE.RicciFlow.iteratedCovGrad_add (I := I) g₀ 0 2 j
      (deTurckVFLoweringSlotDiff (I := I) g₀ g₁ g₂ g_bg)
      (deTurckVFConnectionSlotDiff (I := I) g₀ g₁ g₂ g_bg)]
  set X := PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 j
    (deTurckVFLoweringSlotDiff (I := I) g₀ g₁ g₂ g_bg) with hX
  set Y := PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 j
    (deTurckVFConnectionSlotDiff (I := I) g₀ g₁ g₂ g_bg) with hY
  set Z := PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 j
    (deTurckVFFieldSlotDiff (I := I) g₀ g₁ g₂ g_bg) with hZ
  have htri : ‖X + Y + Z‖ ^ 2 ≤ 3 * (‖X‖ ^ 2 + ‖Y‖ ^ 2 + ‖Z‖ ^ 2) := by
    have t₁ : ‖X + Y + Z‖ ≤ ‖X + Y‖ + ‖Z‖ := norm_add_le (X + Y) Z
    have t₂ : ‖X + Y‖ ≤ ‖X‖ + ‖Y‖ := norm_add_le X Y
    have t₃ : ‖X + Y + Z‖ ≤ ‖X‖ + ‖Y‖ + ‖Z‖ := by linarith
    have t₄ : ‖X + Y + Z‖ ^ 2 ≤ (‖X‖ + ‖Y‖ + ‖Z‖) ^ 2 := by
      have h0 : (0 : ℝ) ≤ ‖X + Y + Z‖ := norm_nonneg _
      nlinarith
    nlinarith [t₄, sq_nonneg (‖X‖ - ‖Y‖), sq_nonneg (‖Y‖ - ‖Z‖), sq_nonneg (‖X‖ - ‖Z‖)]
  have hA : (0 : ℝ) ≤ ∑ i ∈ Finset.range (j + 2 + 1),
      ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i
          (realizeSymmCcTensor (I := I) g₀ (T₁ - T₂))‖ ^ 2 :=
    Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hS : (0 : ℝ) ≤ ∑ i ∈ Finset.range (j + 2 + 1),
      (‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i T₁‖ ^ 2
        + ‖PDE.RicciFlow.iteratedCovGrad (I := I) g₀ 0 2 i T₂‖ ^ 2) :=
    Finset.sum_nonneg (fun i _ => by positivity)
  have hc : (0 : ℝ) ≤
      ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) a (T₁ - T₂)‖ ^ 2 :=
    sq_nonneg _
  refine le_trans htri ?_
  nlinarith [e₁, e₂, e₃, hA, hS, hc, mul_nonneg hC₁ hA, mul_nonneg hC₂ hA, mul_nonneg hC₃ hA,
    mul_nonneg (mul_nonneg hC₁ hS) hc, mul_nonneg (mul_nonneg hC₂ hS) hc,
    mul_nonneg (mul_nonneg hC₃ hS) hc]

end DeTurck
end PDE
end DifferentialGeometry

end
