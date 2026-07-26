import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.DeTurckLieCoeffL2JetBound
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.LieCorr0Split
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.MetricArmCoeffJetTower
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.RemainderCoeffPerOrderJetEnvelopes
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.DeTurckLieArm1CoeffL2JetBound

/-!
# `lieCorr0Field` realizedFam jet-L2 top-separated producer

The second genuinely-missing `C₀` constituent of the `Ψ₀` map
(`Ψ₀ = -2·arm0Field + deTurckLieCoeffField + lieCorr0Field`).  We produce the
`realizedFam` per-order and summed top-separated jet-L2 bounds for
`lieCorr0Field`, shape-matching the `deTurckLieCoeffField` siblings.

`lieCorr0Field` genuinely carries the top window `∇^{i+2}T` (RULING 2, not the
traceHessian pattern): via `lc0_decomp` it is
`lc0Insert + lc0VB + lc0AMix + lc0Riem`, and `lc0Insert` contains the base
insertion `lc0Insert g₀ g₁ g₀ = -deTurckLieDLbCoeffField g₀ g₁ g₀` whose
`∇^i` reaches `∇^{i+2}T` — its top-separation is inherited verbatim from the
committed DLb field producer at `g_bg := g₀` (`Ktop` R-free).  The remaining
four pieces are `∇²T`-free and land in the `R`-carrying `Kc`.
-/

noncomputable section

set_option autoImplicit false
set_option linter.style.setOption false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open MeasureTheory Set Filter Topology Bundle Manifold Tensor0SBundle ContinuousLinearMap
open scoped ENNReal NNReal BigOperators Manifold ContDiff

namespace DifferentialGeometry.Integral.Connection

open DifferentialGeometry
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
  (deTurckLieEndoArmField deTurckLieEndoArmField_toSection deTurckLieDLbFib
    reindexCoeffGen reindexCoeffGen_toSection reindexCoeffFibGen_apply
    domDomCongrFibRank domDomCongrFibRank_apply tensor0SProdKappaFib)
open DifferentialGeometry.PDE.DeTurck.RicciLinearization
  (realizedFam convexPerturbation convexPerturbation_gFibreOpBound realizedFam_inner_of_mem
    Icc_subset_realizedSmallSet)
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck
open LieCorr0Core

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

/-- The reanchoring endomorphism arm field and the DLb coefficient field are the
same object (both are `ofCLM (deTurckLieDLbFib g₁ g_bg)`). -/
private theorem endoArm_eq_dlb (g₀ g₁ g_bg : SmoothRiemannianMetric I M) :
    deTurckLieEndoArmField (I := I) (M := M) g₀ g₁ g_bg =
      deTurckLieDLbCoeffField (I := I) (M := M) g₀ g₁ g_bg := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [deTurckLieEndoArmField_toSection, deTurckLieDLbCoeffField_toSection]

/-- The base insertion piece is the negative of the DLb coefficient field.
Combines `insert_base` (at `g_bg := g₀`) with `endoArm_eq_dlb`; this routes
`lieCorr0Field`'s top window through the committed DLb producer. -/
private theorem lc0Insert_base_eq_neg_dlb (g₀ g₁ : SmoothRiemannianMetric I M) :
    lc0Insert (I := I) (M := M) g₀ g₁ g₀ =
      -deTurckLieDLbCoeffField (I := I) (M := M) g₀ g₁ g₀ := by
  have h := insert_base (I := I) (M := M) g₀ g₁ g₀
  rw [sub_self] at h
  rw [eq_neg_of_add_eq_zero_left h, endoArm_eq_dlb]

set_option linter.unusedVariables false in
/-- **Top piece.**  The base insertion piece inherits the DLb field producer's
top-separated bound at `g_bg := g₀` (`Ktop` R-free). -/
private theorem lc0InsertBase_realizedFam_perOrder_topSeparated
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ Ktop : ℝ, 0 ≤ Ktop ∧ ∃ Kc : ℕ → ℝ, (∀ i, 0 ≤ Kc i) ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (hδ'_le : δ' ≤ δ₀)
        (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ∀ (s : ℝ), s ∈ Set.Icc (0 : ℝ) 1 →
        ∀ (i : ℕ), i ≤ a →
          ‖iteratedCovGrad (I := I) g₀ 2 2 i
              (lc0Insert (I := I) (M := M) g₀
                (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀)‖ ^ 2 ≤
            Ktop * (‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T‖ ^ 2 +
              ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T'‖ ^ 2) +
            Kc i * (1 + ∑ j ∈ Finset.range (i + 3),
              (‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
                ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2)) := by
  obtain ⟨Ktop, hnn, Kc, hKcnn, h⟩ :=
    deTurckLieDLbCoeffField_realizedFam_jetL2_perOrder_topSeparated (I := I) (M := M) g₀ g₀ a
      ha_super hR hδ₀
  refine ⟨Ktop, hnn, Kc, hKcnn, ?_⟩
  intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball s hs i hi
  have hb := h T T' hδ_le hδ hδ'_le hδ' hTball hT'ball s hs i hi
  rw [lc0Insert_base_eq_neg_dlb, iteratedCovGrad_neg, norm_neg]
  exact hb

/-- Five-way squared triangle: `t ≤ a+b+c+d+e` (all nonneg) gives
`t² ≤ 5·(a²+b²+c²+d²+e²)`.  Used for the `lc0_decomp` five-summand assembly. -/
private theorem sq_le_five_add (t a b c d e : ℝ) (ht : 0 ≤ t)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e)
    (htri : t ≤ a + b + c + d + e) :
    t ^ 2 ≤ 5 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 + e ^ 2) := by
  have hsum : 0 ≤ a + b + c + d + e := by linarith
  nlinarith [mul_le_mul htri htri ht hsum, sq_nonneg (a - b), sq_nonneg (a - c),
    sq_nonneg (a - d), sq_nonneg (a - e), sq_nonneg (b - c), sq_nonneg (b - d),
    sq_nonneg (b - e), sq_nonneg (c - d), sq_nonneg (c - e), sq_nonneg (d - e)]

/-! ## The `lc0Riem` `Kc` atom

`lc0Riem g₀ g₁` is the fixed-curvature piece
`-traceStep(g₁, RiemPerm2) ∘ traceStep(g₀, RiemPerm1) ∘ prodKappa(lieCorr0RiemLoweredFib g₀)`.
Only the outer `g₁`-cometric double trace moves with `g₁`; everything to its right
depends on `g₀` alone.  We therefore write the piece as `appCcRS` of a live
`(4, 2)` cometric arm against a fixed `(2, 4)` passenger, and control the live arm
by the committed rank-`1` cometric envelope through `slotExtend`. -/

/-- Source-slot three-cycle `0 ↦ 1 ↦ 2 ↦ 0` relating the rank-`2` cometric double
trace to the passenger-extension of the rank-`1` one. -/
private def lc0RiemSrc : Equiv.Perm (Fin 4) :=
  ⟨![1, 2, 0, 3], ![2, 0, 1, 3], by decide, by decide⟩

/-- **Live arm.**  The moving cometric double trace at rank `2`, presented as a
`g₀`-based `(4, 2)` operator field built from the committed rank-`1` cast
`cometricCastG0`. -/
private noncomputable def lc0RiemLive (g₀ g₁ : SmoothRiemannianMetric I M) :
    SmoothCcTensor g₀ 4 2 :=
  reindexCoeffGen (I := I) (M := M) g₀ 4 2
    (slotExtend (I := I) (M := M) g₀ 3 1 (cometricCastG0 (I := I) g₀ g₁)) lc0RiemSrc

/-- The live arm's fibre is exactly the rank-`2` `g₁`-cometric double trace. -/
private theorem lc0RiemLive_toSec (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) :
    (show Tensor0SSpace 4 I x →L[ℝ] Tensor0SSpace 2 I x from
        (lc0RiemLive (I := I) (M := M) g₀ g₁).toSection x) =
      cometricDoubleTraceFib (I := I) g₁ 2 x := by
  classical
  apply ContinuousLinearMap.ext
  intro D
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro m
  rw [show (m : Fin 2 → E) = Fin.cons (m 0) (Fin.tail m) from (Fin.cons_self_tail m).symm]
  change Tensor0SSpace.toModel
      ((show Tensor0SSpace 4 I x →L[ℝ] Tensor0SSpace 2 I x from
        (reindexCoeffGen (I := I) (M := M) g₀ 4 2
          (slotExtend (I := I) (M := M) g₀ 3 1 (cometricCastG0 (I := I) g₀ g₁))
          lc0RiemSrc).toSection x) D) _ = _
  rw [reindexCoeffGen_toSection, reindexCoeffFibGen_apply, slotExtend_toSection,
    slotExtendFib_apply_eval]
  have hcast : (cometricCastG0 (I := I) g₀ g₁).toSection x
      = (cometricDoubleTraceField (I := I) g₁ 1).toSection x := rfl
  rw [hcast, cometricDoubleTraceField_toSection]
  simp only [cometricDoubleTraceFib_toModel, modelDoubleTrace_apply]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [TensorMultilinear.tensor0S_curry_apply_eval, Tensor0SSpace.toModel_ofModel,
    ContinuousMultilinearMap.domDomCongr_apply]
  refine congrArg _ ?_
  funext i
  fin_cases i <;> rfl

/-- The fixed passenger fibre: everything in `lieCorr0RiemFib` to the right of the
moving cometric double trace, including the outer slot permutation. -/
private noncomputable def lc0RiemPassFib (g₀ : SmoothRiemannianMetric I M) (x : M) :
    Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 4 I x :=
  (domDomCongrFibRank (I := I) 4 lieCorr0RiemPerm2 x).comp
    ((lieCorr0TraceStep (I := I) g₀ 4 lieCorr0RiemPerm1 x).comp
      (tensor0SProdKappaFib (I := I) (p := 2) (q := 4) x
        (lieCorr0RiemLoweredFib (I := I) g₀ x)))

private theorem lc0RiemPassFib_contMDiff (g₀ : SmoothRiemannianMetric I M) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 2 4 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel 2 4 ℝ E)
        (E := fun z : M => TensorRSSpace 2 4 I z) x
        (TensorRSSpace.ofCLM (lc0RiemPassFib (I := I) g₀ x))) := by
  classical
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (F₁ := Tensor0SModel 2 ℝ E) (V₁ := fun x : M => Tensor0SSpace 2 I x)
    (F₂ := Tensor0SModel 4 ℝ E) (V₂ := fun x : M => Tensor0SSpace 4 I x)
    (φ := fun x => lc0RiemPassFib (I := I) g₀ x)
  intro Y
  have hprod := lieCorr0_prod_section_contMDiff (I := I) (p := 2) (q := 4)
    (fun x => Y x) (fun x => lieCorr0RiemLoweredFib (I := I) g₀ x)
    Y.contMDiff (lieCorr0RiemLoweredFib_section_contMDiff (I := I) g₀)
  have htr1 := lieCorr0TraceStep_section_contMDiff (I := I) g₀ 4 lieCorr0RiemPerm1
    (fun x => tensor0SProdKappaFib (I := I) x (lieCorr0RiemLoweredFib (I := I) g₀ x) (Y x))
    hprod
  have hddc := lieCorr0_ddc_section_contMDiff (I := I) (d := 4) lieCorr0RiemPerm2
    (fun x => lieCorr0TraceStep (I := I) g₀ 4 lieCorr0RiemPerm1 x
      (tensor0SProdKappaFib (I := I) x (lieCorr0RiemLoweredFib (I := I) g₀ x) (Y x))) htr1
  refine hddc.congr (fun x => ?_)
  refine congrArg (fun t => TotalSpace.mk' (Tensor0SModel 4 ℝ E)
    (E := fun z : M => Tensor0SSpace 4 I z) x t) ?_
  rw [lc0RiemPassFib]
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, domDomCongrFibRank_apply]

/-- **Fixed passenger.**  The `g₀`-only `(2, 4)` operator field carrying the
curvature insertion and the background trace step of `lc0Riem`. -/
private noncomputable def lc0RiemPass (g₀ : SmoothRiemannianMetric I M) :
    SmoothCcTensor g₀ 2 4 where
  toSection :=
    { toFun := fun x : M =>
        (show TensorRSSpace 2 4 I x from
          TensorRSSpace.ofCLM (lc0RiemPassFib (I := I) g₀ x))
      contMDiff_toFun := lc0RiemPassFib_contMDiff (I := I) g₀ }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

/-- Fibrewise form of the two-arm factorization of the fixed-curvature piece. -/
private theorem lc0RiemFib_eq (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) :
    lieCorr0RiemFib (I := I) g₀ g₁ x =
      -((show Tensor0SSpace 4 I x →L[ℝ] Tensor0SSpace 2 I x from
            (lc0RiemLive (I := I) (M := M) g₀ g₁).toSection x).comp
        (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 4 I x from
            (lc0RiemPass (I := I) g₀).toSection x)) := by
  rw [lieCorr0RiemFib, lc0RiemLive_toSec, neg_one_smul]
  rfl

/-- **The `lc0Riem` two-arm factorization.**  The fixed-curvature piece is the
operator-field action of the live rank-`2` cometric arm on the fixed passenger. -/
private theorem lc0Riem_eq_app (g₀ g₁ : SmoothRiemannianMetric I M) :
    lc0Riem (I := I) (M := M) g₀ g₁ =
      -appCcRS (I := I) (M := M) g₀ 2 4 2
        (lc0RiemLive (I := I) (M := M) g₀ g₁) (lc0RiemPass (I := I) g₀) := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [SmoothCcTensor.toSection_neg, ContMDiffSection.coe_neg, Pi.neg_apply, appCcRS_toSection]
  exact lc0RiemFib_eq (I := I) (M := M) g₀ g₁ x

private theorem iteratedCovGrad_smul_real (g : SmoothRiemannianMetric I M) (r s j : ℕ) (c : ℝ)
    (w : SmoothCcTensor g r s) :
    iteratedCovGrad (I := I) g r s j (c • w) = c • iteratedCovGrad (I := I) g r s j w := by
  induction j with
  | zero => simp only [iteratedCovGrad_zero]
  | succ j ih => rw [iteratedCovGrad_succ, iteratedCovGrad_succ, ih,
      DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covGrad_smul]

/-- Pointwise: the live arm's jets are dominated by the jets of the committed
rank-`1` cometric cast, at the cost of one factor of the dimension. -/
private theorem lc0RiemLive_rfns_le (g₀ g₁ : SmoothRiemannianMetric I M) (m : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + m) x
        ((iteratedCovGrad (I := I) g₀ 4 2 m
          (lc0RiemLive (I := I) (M := M) g₀ g₁)).toSection x) ≤
      (Module.finrank ℝ E : ℝ) *
        riemannianFiberNormSq (I := I) (M := M) g₀ 3 (1 + m) x
          ((iteratedCovGrad (I := I) g₀ 3 1 m (cometricCastG0 (I := I) g₀ g₁)).toSection x) := by
  rw [lc0RiemLive, rfns_iteratedCovGrad_reindexCoeffGen_eq]
  exact rfns_iteratedCovGrad_slotExtend_le (I := I) (M := M) g₀ 3 1
    (cometricCastG0 (I := I) g₀ g₁) m x

/-- `L²` form of `lc0RiemLive_rfns_le`. -/
private theorem lc0RiemLive_l2_le (g₀ g₁ : SmoothRiemannianMetric I M) (m : ℕ) :
    ‖iteratedCovGrad (I := I) g₀ 4 2 m (lc0RiemLive (I := I) (M := M) g₀ g₁)‖ ^ 2 ≤
      (Module.finrank ℝ E : ℝ) *
        ‖iteratedCovGrad (I := I) g₀ 3 1 m (cometricCastG0 (I := I) g₀ g₁)‖ ^ 2 := by
  have hint : MeasureTheory.Integrable
      (fun x => (Module.finrank ℝ E : ℝ) *
        riemannianFiberNormSq (I := I) (M := M) g₀ 3 (1 + m) x
          ((iteratedCovGrad (I := I) g₀ 3 1 m (cometricCastG0 (I := I) g₀ g₁)).toSection x))
      (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
    (integrable_riemannianFiberNormSq_toSection (I := I) (M := M) g₀ 3 (1 + m)
      (iteratedCovGrad (I := I) g₀ 3 1 m (cometricCastG0 (I := I) g₀ g₁))).const_mul _
  have key := normSq_le_integral_of_pointwise_fiberNormSq_le_rs (I := I) (M := M) g₀ 4 (2 + m)
    (iteratedCovGrad (I := I) g₀ 4 2 m (lc0RiemLive (I := I) (M := M) g₀ g₁)) _ hint
    (fun x => lc0RiemLive_rfns_le (I := I) (M := M) g₀ g₁ m x)
  refine le_trans key (le_of_eq ?_)
  rw [MeasureTheory.integral_const_mul]
  refine congrArg _ ?_
  rw [← tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs (I := I) (M := M) g₀ 3 (1 + m)
      (iteratedCovGrad (I := I) g₀ 3 1 m (cometricCastG0 (I := I) g₀ g₁)),
    ← SmoothCcTensor.norm_def]

set_option linter.unusedVariables false in
/-- **`lc0Riem` `Kc` atom.**  The fixed-curvature piece of `lieCorr0Field` satisfies
the `realizedFam` per-order top-separated jet-`L²` bound with vanishing top constant:
its `∇^i` never reaches `∇^{i+2}T`, so all of it lands in the `R`-carrying `Kc`. -/
private theorem lc0Riem_realizedFam_perOrder_topSep
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ Ktop : ℝ, 0 ≤ Ktop ∧ ∃ Kc : ℕ → ℝ, (∀ i, 0 ≤ Kc i) ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (hδ'_le : δ' ≤ δ₀)
        (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ∀ (s : ℝ), s ∈ Set.Icc (0 : ℝ) 1 →
        ∀ (i : ℕ), i ≤ a →
          ‖iteratedCovGrad (I := I) g₀ 2 2 i
              (lc0Riem (I := I) (M := M) g₀
                (realizedFam (I := I) g₀ T T' hδ hδ' s))‖ ^ 2 ≤
            Ktop * (‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T‖ ^ 2 +
              ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T'‖ ^ 2) +
            Kc i * (1 + ∑ j ∈ Finset.range (i + 3),
              (‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
                ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2)) := by
  classical
  obtain ⟨Λ, F, hΛ_nn, hF_nn, hcom⟩ :=
    cometricDoubleTraceField_order0sup_jetL2_ballUniform_generic (I := I) (M := M) g₀ a
      ha_super hR hδ₀
  obtain ⟨KP, hKP_nn, hKP⟩ := exists_bound_riemannianFiberNormSq_smoothCcTensor
    (I := I) (M := M) g₀ 2 4 (lc0RiemPass (I := I) g₀)
  choose Cint hCint_nn hCint using
    (fun k : ℕ => exists_integrated_iteratedCovGrad_diagonalProductGrid_twoArm_rs_le
      (I := I) (M := M) g₀ 4 2 2 4 k)
  set fr : ℝ := (Module.finrank ℝ E : ℝ) with hfr
  have hfr_nn : (0 : ℝ) ≤ fr := Nat.cast_nonneg _
  set NPass : ℕ → ℝ := fun i => ∑ l ∈ Finset.range (i + 1),
    ‖iteratedCovGrad (I := I) g₀ 2 4 l (lc0RiemPass (I := I) g₀)‖ ^ 2 with hNPass
  have hNPass_nn : ∀ i, 0 ≤ NPass i := fun i =>
    Finset.sum_nonneg (fun l _ => sq_nonneg _)
  refine ⟨0, le_refl 0, fun i => appCcGdiag (E := E) i *
    (Cint i * (KP * (fr * F i) + fr * Λ ^ 2 * NPass i)), fun i => ?_, ?_⟩
  · exact mul_nonneg (appCcGdiag_nonneg (E := E) i)
      (mul_nonneg (hCint_nn i)
        (add_nonneg (mul_nonneg hKP_nn (mul_nonneg hfr_nn (hF_nn i)))
          (mul_nonneg (mul_nonneg hfr_nn (sq_nonneg Λ)) (hNPass_nn i))))
  intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball s hs i hi
  have hs0 : (0 : ℝ) ≤ s := hs.1
  have hs1 : s ≤ 1 := hs.2
  have h1ms : (0 : ℝ) ≤ 1 - s := by linarith
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le hδ₀
  have hδ'_lt : δ' < 1 := lt_of_le_of_lt hδ'_le hδ₀
  have hδP : gFibreOpBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (convexPerturbation (I := I) g₀ T T' s))
      ((1 - s) * δ' + s * δ) :=
    convexPerturbation_gFibreOpBound (I := I) (M := M) g₀ T T' hδ hδ' hs0 hs1
  have hδP_le : (1 - s) * δ' + s * δ ≤ δ₀ := by
    have e1 : (1 - s) * δ' ≤ (1 - s) * δ₀ := mul_le_mul_of_nonneg_left hδ'_le h1ms
    have e2 : s * δ ≤ s * δ₀ := mul_le_mul_of_nonneg_left hδ_le hs0
    have e3 : (1 - s) * δ₀ + s * δ₀ = δ₀ := by ring
    linarith [e1, e2, e3]
  have htie : ∀ (y : M) (v w : TangentSpace I y),
      (realizedFam (I := I) g₀ T T' hδ hδ' s).inner y v w =
        g₀.inner y v w +
          ccTensorBilinSymm (I := I) g₀ (convexPerturbation (I := I) g₀ T T' s) y v w :=
    fun y v w =>
      realizedFam_inner_of_mem (I := I) g₀ T T' hδ hδ'
        (Icc_subset_realizedSmallSet hδ_lt hδ'_lt hs) y v w
  have hPball : ∀ j : ℕ, j ≤ a + 2 →
      ‖iteratedCovGrad (I := I) g₀ 0 2 j (convexPerturbation (I := I) g₀ T T' s)‖ ≤ R := by
    intro j hj
    have heq : iteratedCovGrad (I := I) g₀ 0 2 j (convexPerturbation (I := I) g₀ T T' s)
        = (1 - s) • iteratedCovGrad (I := I) g₀ 0 2 j T'
          + s • iteratedCovGrad (I := I) g₀ 0 2 j T := by
      rw [show convexPerturbation (I := I) g₀ T T' s = (1 - s) • T' + s • T from rfl,
        iteratedCovGrad_add, iteratedCovGrad_smul_real, iteratedCovGrad_smul_real]
    rw [heq]
    calc ‖(1 - s) • iteratedCovGrad (I := I) g₀ 0 2 j T'
            + s • iteratedCovGrad (I := I) g₀ 0 2 j T‖
        ≤ ‖(1 - s) • iteratedCovGrad (I := I) g₀ 0 2 j T'‖
            + ‖s • iteratedCovGrad (I := I) g₀ 0 2 j T‖ := norm_add_le _ _
      _ = (1 - s) * ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖
            + s * ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ := by
          rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
            abs_of_nonneg h1ms, abs_of_nonneg hs0]
      _ ≤ (1 - s) * R + s * R :=
          add_le_add (mul_le_mul_of_nonneg_left (hT'ball j hj) h1ms)
            (mul_le_mul_of_nonneg_left (hTball j hj) hs0)
      _ = R := by ring
  obtain ⟨hsup0, hjet⟩ := hcom (realizedFam (I := I) g₀ T T' hδ hδ' s)
    (convexPerturbation (I := I) g₀ T T' s) hδP_le hδP htie hPball
  -- order-`0` fibre sup bounds for the two arms
  have hLsup : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x
      ((lc0RiemLive (I := I) (M := M) g₀
        (realizedFam (I := I) g₀ T T' hδ hδ' s)).toSection x) ≤
      Real.sqrt (fr * Λ ^ 2) ^ 2 := by
    intro x
    have h := lc0RiemLive_rfns_le (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T T' hδ hδ' s) 0 x
    rw [iteratedCovGrad_zero, iteratedCovGrad_zero] at h
    rw [Real.sq_sqrt (mul_nonneg hfr_nn (sq_nonneg Λ))]
    exact le_trans h (mul_le_mul_of_nonneg_left (hsup0 x) hfr_nn)
  have hPsup : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 2 4 x
      ((lc0RiemPass (I := I) g₀).toSection x) ≤ Real.sqrt KP ^ 2 := by
    intro x
    rw [Real.sq_sqrt hKP_nn]
    exact hKP x
  obtain ⟨hgrid_int, hgrid_bd⟩ := hCint i
    (lc0RiemLive (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' s))
    (lc0RiemPass (I := I) g₀) (Real.sqrt (fr * Λ ^ 2)) (Real.sqrt KP)
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) hLsup hPsup
  -- the live arm's jet-`L²` sum
  have hLsum : ∑ m ∈ Finset.range (i + 1),
      ‖iteratedCovGrad (I := I) g₀ 4 2 m
        (lc0RiemLive (I := I) (M := M) g₀
          (realizedFam (I := I) g₀ T T' hδ hδ' s))‖ ^ 2 ≤ fr * F i := by
    calc ∑ m ∈ Finset.range (i + 1),
          ‖iteratedCovGrad (I := I) g₀ 4 2 m
            (lc0RiemLive (I := I) (M := M) g₀
              (realizedFam (I := I) g₀ T T' hδ hδ' s))‖ ^ 2
        ≤ ∑ m ∈ Finset.range (i + 1), fr *
            ‖iteratedCovGrad (I := I) g₀ 3 1 m
              (cometricCastG0 (I := I) g₀
                (realizedFam (I := I) g₀ T T' hδ hδ' s))‖ ^ 2 :=
          Finset.sum_le_sum (fun m _ => lc0RiemLive_l2_le (I := I) (M := M) g₀ _ m)
      _ = fr * ∑ m ∈ Finset.range (i + 1),
            ‖iteratedCovGrad (I := I) g₀ 3 1 m
              (cometricCastG0 (I := I) g₀
                (realizedFam (I := I) g₀ T T' hδ hδ' s))‖ ^ 2 := by
          rw [Finset.mul_sum]
      _ ≤ fr * F i := mul_le_mul_of_nonneg_left (hjet i hi) hfr_nn
  -- pointwise product grid for the two-arm action, then integrate
  have hnorm : ‖iteratedCovGrad (I := I) g₀ 2 2 i
        (appCcRS (I := I) (M := M) g₀ 2 4 2
          (lc0RiemLive (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' s))
          (lc0RiemPass (I := I) g₀))‖ ^ 2 ≤
      appCcGdiag (E := E) i *
        (Cint i * (Real.sqrt KP ^ 2 * ∑ m ∈ Finset.range (i + 1),
            ‖iteratedCovGrad (I := I) g₀ 4 2 m
              (lc0RiemLive (I := I) (M := M) g₀
                (realizedFam (I := I) g₀ T T' hδ hδ' s))‖ ^ 2
          + Real.sqrt (fr * Λ ^ 2) ^ 2 * ∑ l ∈ Finset.range (i + 1),
            ‖iteratedCovGrad (I := I) g₀ 2 4 l (lc0RiemPass (I := I) g₀)‖ ^ 2)) := by
    have key := normSq_le_integral_of_pointwise_fiberNormSq_le_rs (I := I) (M := M) g₀ 2 (2 + i)
      (iteratedCovGrad (I := I) g₀ 2 2 i
        (appCcRS (I := I) (M := M) g₀ 2 4 2
          (lc0RiemLive (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' s))
          (lc0RiemPass (I := I) g₀))) _ (hgrid_int.const_mul (appCcGdiag (E := E) i))
      (fun x => rfns_iteratedCovGrad_appCcRS_diagonalProductGrid_rankLeft_le
        (I := I) (M := M) g₀ i 2 4 2
        (lc0RiemLive (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' s))
        (lc0RiemPass (I := I) g₀) x)
    refine le_trans key ?_
    rw [MeasureTheory.integral_const_mul]
    exact mul_le_mul_of_nonneg_left hgrid_bd (appCcGdiag_nonneg (E := E) i)
  -- assemble
  rw [lc0Riem_eq_app, iteratedCovGrad_neg, norm_neg]
  have hKPsq : Real.sqrt KP ^ 2 = KP := Real.sq_sqrt hKP_nn
  have hΛsq : Real.sqrt (fr * Λ ^ 2) ^ 2 = fr * Λ ^ 2 :=
    Real.sq_sqrt (mul_nonneg hfr_nn (sq_nonneg Λ))
  rw [hKPsq, hΛsq] at hnorm
  have hmid : appCcGdiag (E := E) i *
      (Cint i * (KP * ∑ m ∈ Finset.range (i + 1),
          ‖iteratedCovGrad (I := I) g₀ 4 2 m
            (lc0RiemLive (I := I) (M := M) g₀
              (realizedFam (I := I) g₀ T T' hδ hδ' s))‖ ^ 2
        + fr * Λ ^ 2 * NPass i)) ≤
      appCcGdiag (E := E) i * (Cint i * (KP * (fr * F i) + fr * Λ ^ 2 * NPass i)) := by
    refine mul_le_mul_of_nonneg_left ?_ (appCcGdiag_nonneg (E := E) i)
    refine mul_le_mul_of_nonneg_left ?_ (hCint_nn i)
    have hstep := mul_le_mul_of_nonneg_left hLsum hKP_nn
    linarith
  have hsum_nn : (0 : ℝ) ≤ ∑ j ∈ Finset.range (i + 3),
      (‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
        ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2) :=
    Finset.sum_nonneg (fun j _ => add_nonneg (sq_nonneg _) (sq_nonneg _))
  have hKc_nn : (0 : ℝ) ≤ appCcGdiag (E := E) i *
      (Cint i * (KP * (fr * F i) + fr * Λ ^ 2 * NPass i)) :=
    mul_nonneg (appCcGdiag_nonneg (E := E) i)
      (mul_nonneg (hCint_nn i)
        (add_nonneg (mul_nonneg hKP_nn (mul_nonneg hfr_nn (hF_nn i)))
          (mul_nonneg (mul_nonneg hfr_nn (sq_nonneg Λ)) (hNPass_nn i))))
  nlinarith [le_trans hnorm hmid, hsum_nn, hKc_nn]

/-! ## The `lc0Insert`-difference `Kc` atom (`lc0Insert g_bg − lc0Insert g₀`)

By `nEndo_diff` (`LieCorr0Split.lean:103`) the difference of insertion pieces is the
slot insertion of the endomorphism
`Endo = connDiff g₁ g₀ (deTurckVF g₁ g₀) − connDiff g₁ g₀ (deTurckVF g₁ g_bg)`,
i.e. the moving connection difference `connDiff g₁ g₀` contracted with the
deTurckVF-difference `Vdiff = deTurckVF g₁ g₀ − deTurckVF g₁ g_bg`.

Unlike `lc0Riem` (one live cometric factor on a fixed passenger), this piece has
**two live factors** whose product is an *interior-product contraction* — not the
operator *composition* that `appCcRS` and its product grid
(`rfns_iteratedCovGrad_appCcRS_diagonalProductGrid_rankLeft_le`) cover.  The tree
has no `clm_apply`/interior-product Leibniz jet grid, and the natural
committed home of the object,
`cometricRaise (wAlphaB) = slotInsert (connDiff·deTurckVF)` extracted from
`deTurckLieWEndoInsert_eq_cometricRaise`, lives entirely in the `private`
`wAlphaB`/`wOmega`/`wCA` machinery of `DeTurckVectorFieldL2JetBound.lean`.  The
`deTurckLieWEndo`-difference route is provably circular (it reduces `Endo` to
`Endo`).  So the per-order jet-`L²` `ballUniform` bound for this piece is a
genuine **missing engine** (see the same-name `.md`); it is isolated below in the
single `sorry` of `lc0InsertDiff_ballUniform`, and the top-separated atom is
proved from it with `Ktop = 0`. -/

set_option linter.unusedVariables false in
/-- **MISSING ENGINE (single `sorry`).**  Per-order `ballUniform` jet-`L²` bound for
the `lc0Insert`-difference piece.  Requires a jet-`L²` producer for the endomorphism
`connDiff g₁ g₀ (deTurckVF g₁ g₀ − deTurckVF g₁ g_bg)`, whose committed home is the
`private` `wAlphaB`/`wOmega`/`wCA` layer of `DeTurckVectorFieldL2JetBound.lean`
(exposed via a public `appCc(wCA, wOmega-difference)` producer, or a new
interior-product Leibniz jet grid).  This is the only gap in the atom below. -/
private theorem lc0InsertDiff_ballUniform
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ K : ℕ → ℝ, (∀ i, 0 ≤ K i) ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (hδ'_le : δ' ≤ δ₀)
        (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ∀ (i : ℕ), i ≤ a → ∀ (s : ℝ), s ∈ Set.Icc (0 : ℝ) 1 →
          ‖iteratedCovGrad (I := I) g₀ 2 2 i
              (lc0Insert (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg
                - lc0Insert (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀)‖ ^ 2
            ≤ K i := by
  sorry

set_option linter.unusedVariables false in
/-- **`lc0Insert`-difference `Kc` atom.**  Per-order top-separated jet-`L²` bound for
`lc0Insert g_bg − lc0Insert g₀` with vanishing top constant (`∇²T`-free: all of it
lands in the `R`-carrying `Kc`).  Proved from the `ballUniform` bound
`lc0InsertDiff_ballUniform` by the trivial `Ktop = 0` reshape (`K i ≤ K i·(1+low)`);
the `ballUniform` bound is the atom's single frontier `sorry`. -/
private theorem lc0InsertDiff_realizedFam_perOrder_topSep
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ Ktop : ℝ, 0 ≤ Ktop ∧ ∃ Kc : ℕ → ℝ, (∀ i, 0 ≤ Kc i) ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (hδ'_le : δ' ≤ δ₀)
        (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ∀ (s : ℝ), s ∈ Set.Icc (0 : ℝ) 1 →
        ∀ (i : ℕ), i ≤ a →
          ‖iteratedCovGrad (I := I) g₀ 2 2 i
              (lc0Insert (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg
                - lc0Insert (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀)‖ ^ 2 ≤
            Ktop * (‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T‖ ^ 2 +
              ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T'‖ ^ 2) +
            Kc i * (1 + ∑ j ∈ Finset.range (i + 3),
              (‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
                ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2)) := by
  obtain ⟨K, hK_nn, hK⟩ := lc0InsertDiff_ballUniform (I := I) (M := M) g₀ g_bg a ha_super hR hδ₀
  refine ⟨0, le_refl 0, K, hK_nn, ?_⟩
  intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball s hs i hi
  have hb := hK T T' hδ_le hδ hδ'_le hδ' hTball hT'ball i hi s hs
  have hlow_nn : (0 : ℝ) ≤ ∑ j ∈ Finset.range (i + 3),
      (‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
        ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2) :=
    Finset.sum_nonneg (fun j _ => add_nonneg (sq_nonneg _) (sq_nonneg _))
  nlinarith [hb, hK_nn i, hlow_nn, mul_nonneg (hK_nn i) hlow_nn]

#print axioms endoArm_eq_dlb
#print axioms lc0Insert_base_eq_neg_dlb
#print axioms lc0InsertBase_realizedFam_perOrder_topSeparated
#print axioms sq_le_five_add
#print axioms lc0Riem_realizedFam_perOrder_topSep
-- honest: the insert-diff atom depends on `sorryAx` via `lc0InsertDiff_ballUniform`
#print axioms lc0InsertDiff_realizedFam_perOrder_topSep

end DifferentialGeometry.Integral.Connection

end
