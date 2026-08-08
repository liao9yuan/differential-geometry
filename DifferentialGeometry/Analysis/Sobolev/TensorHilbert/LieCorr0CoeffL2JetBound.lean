import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.DeTurckLieCoeffL2JetBound
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.LieCorr0Split
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.MetricArmCoeffJetTower
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.RemainderCoeffPerOrderJetEnvelopes
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.DeTurckLieArm1CoeffL2JetBound
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.DeTurckVectorFieldL2JetBound
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.InteriorProductJetBound
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.SlotFreeCurvatureOperatorDerivative
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CurvatureCoefficientDifferenceJetTower.PairTrace

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
    reindexCoeffGen reindexCoeffGen_toSection reindexCoeffFibGen reindexCoeffFibGen_apply
    domDomCongrFibRank domDomCongrFibRank_apply tensor0SProdKappaFib
    tensor0SProdKappaFib_apply unitModel unitTensor
    metricConnDiffLoweredFib metricConnDiffLoweredFib_contMDiff
    metricConnDiffLoweredFib_toModel)
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
theorem endoArm_eq_dlb (g₀ g₁ g_bg : SmoothRiemannianMetric I M) :
    deTurckLieEndoArmField (I := I) (M := M) g₀ g₁ g_bg =
      deTurckLieDLbCoeffField (I := I) (M := M) g₀ g₁ g_bg := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [deTurckLieEndoArmField_toSection, deTurckLieDLbCoeffField_toSection]

/-- The base insertion piece is the negative of the DLb coefficient field.
Combines `insert_base` (at `g_bg := g₀`) with `endoArm_eq_dlb`; this routes
`lieCorr0Field`'s top window through the committed DLb producer. -/
theorem lc0Insert_base_eq_neg_dlb (g₀ g₁ : SmoothRiemannianMetric I M) :
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
noncomputable def lc0RiemLive (g₀ g₁ : SmoothRiemannianMetric I M) :
    SmoothCcTensor g₀ 4 2 :=
  reindexCoeffGen (I := I) (M := M) g₀ 4 2
    (slotExtend (I := I) (M := M) g₀ 3 1 (cometricCastG0 (I := I) g₀ g₁)) lc0RiemSrc

/-- The live arm's fibre is exactly the rank-`2` `g₁`-cometric double trace. -/
theorem lc0RiemLive_fiber (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) :
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
noncomputable def lc0RiemPass (g₀ : SmoothRiemannianMetric I M) :
    SmoothCcTensor g₀ 2 4 where
  toSection :=
    { toFun := fun x : M =>
        (show TensorRSSpace 2 4 I x from
          TensorRSSpace.ofCLM (lc0RiemPassFib (I := I) g₀ x))
      contMDiff_toFun := lc0RiemPassFib_contMDiff (I := I) g₀ }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

private lemma lc0RiemPass_sum
    (g : SmoothRiemannianMetric I M) (x : M)
    (D : Tensor0SSpace 2 I x) (v : Fin 4 → TangentSpace I x) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 4 I x from
          (lc0RiemPass (I := I) (M := M) g).toSection x) D) v =
      ∑ e : Fin (Module.finrank ℝ E),
        Tensor0SSpace.toModel D
            ![((smoothOrthoFrame (I := I) g x e x :
              TangentSpace I x) : E), (v 1 : E)] *
          g.inner x
            (riemannOp (LeviCivita (I := I) g) x
              (v 2) (v 3) (v 0))
            (smoothOrthoFrame (I := I) g x e x) := by
  classical
  set Y : Tensor0SSpace 6 I x :=
    domDomCongrFibRank (I := I) 6 lieCorr0RiemPerm1 x
      (tensor0SProdKappaFib (I := I) (p := 2) (q := 4) x
        (lieCorr0RiemLoweredFib (I := I) g x) D) with hY_def
  have hYval : ∀ w : Fin 6 → TangentSpace I x,
      Tensor0SSpace.toModel Y w =
        Tensor0SSpace.toModel D ![(w 1 : E), (w 5 : E)] *
          g.inner x
            (riemannOp (LeviCivita (I := I) g) x
              (w 2) (w 3) (w 4)) (w 0) := by
    intro w
    rw [hY_def, domDomCongrFibRank_apply,
      Tensor0SSpace.toModel_ofModel,
      ContinuousMultilinearMap.domDomCongr_apply,
      tensor0SProdKappaFib_apply,
      Tensor0SSpace.toModel_ofModel,
      Bundle.continuousMultilinearMap.modelProduct_apply]
    have hDargs :
        ((fun i : Fin 6 ↦ w (lieCorr0RiemPerm1 i)) ∘
            Fin.castAdd 4) =
          ![w 1, w 5] := by
      funext i
      fin_cases i <;> rfl
    have hRargs :
        ((fun i : Fin 6 ↦ w (lieCorr0RiemPerm1 i)) ∘
            Fin.natAdd 2) =
          ![w 2, w 3, w 4, w 0] := by
      funext i
      fin_cases i <;> rfl
    rw [hDargs, hRargs, lieCorr0RiemLoweredFib_toModel]
    simp
  change Tensor0SSpace.toModel
      (lc0RiemPassFib (I := I) g x D) v = _
  rw [lc0RiemPassFib, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply,
    domDomCongrFibRank_apply,
    Tensor0SSpace.toModel_ofModel,
    ContinuousMultilinearMap.domDomCongr_apply]
  have htop :
      (fun i : Fin 4 ↦ v (lieCorr0RiemPerm2 i)) =
        ![v 2, v 3, v 0, v 1] := by
    funext i
    fin_cases i <;> rfl
  rw [htop]
  rw [lieCorr0TraceStep, ContinuousLinearMap.comp_apply, ← hY_def]
  rw [cometricDoubleTraceFib_eq_orthoFrame_diag
    (I := I) g 4 x
    (mem_smoothOrthoFrameNbhd_self (I := I) (M := M) x) Y]
  rw [← Tensor0SSpace.toModelL_apply, map_sum,
    ContinuousMultilinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun e _ ↦ ?_)
  rw [Tensor0SSpace.toModelL_apply]
  rw [TensorMultilinear.tensor0S_curry_apply_eval
        (I := I) (M := M) (n := 4),
      TensorMultilinear.tensor0S_curry_apply_eval
        (I := I) (M := M) (n := 5)]
  rw [hYval]
  rfl

/-- The fixed Riemann passenger evaluates by inserting the curvature operator
in its first covariant passenger slot. -/
theorem lc0RiemPass_eval
    (g : SmoothRiemannianMetric I M) (x : M)
    (D : Tensor0SSpace 2 I x) (v : Fin 4 → TangentSpace I x) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 4 I x from
          (lc0RiemPass (I := I) (M := M) g).toSection x) D) v =
      Tensor0SSpace.toModel D
        ![((riemannOp (LeviCivita (I := I) g) x
          (v 2) (v 3) (v 0) : TangentSpace I x) : E), (v 1 : E)] := by
  classical
  rw [lc0RiemPass_sum]
  let Rv : TangentSpace I x :=
    riemannOp (LeviCivita (I := I) g) x (v 2) (v 3) (v 0)
  let B : Fin (Module.finrank ℝ E) → TangentSpace I x :=
    fun e ↦ smoothOrthoFrame (I := I) g x e x
  change
    (∑ e, Tensor0SSpace.toModel D
          ![(B e : E), (v 1 : E)] *
        g.inner x Rv (B e)) =
      Tensor0SSpace.toModel D
        ![(Rv : E), (v 1 : E)]
  have hpair (z : E) :
      (![z, (v 1 : E)] : Fin 2 → E) =
        Fin.cons z (fun _ : Fin 1 ↦ (v 1 : E)) := by
    funext i
    fin_cases i <;> rfl
  have hrep :
      Rv = ∑ e, g.inner x (B e) Rv • B e := by
    simpa only [B] using
      CurvatureCoefficientDifferenceJetTower.orthoFrame_center_repr
        (I := I) (M := M) g x Rv
  calc
    _ = ∑ e, g.inner x (B e) Rv *
          Tensor0SSpace.toModel D
            ![(B e : E), (v 1 : E)] := by
      refine Finset.sum_congr rfl (fun e _ ↦ ?_)
      rw [g.symm x Rv (B e), mul_comm]
    _ = ∑ e, g.inner x (B e) Rv *
          Tensor0SSpace.toModel D
            (Fin.cons (B e : E) (fun _ : Fin 1 ↦ (v 1 : E))) := by
      refine Finset.sum_congr rfl (fun e _ ↦ ?_)
      rw [hpair]
    _ = Tensor0SSpace.toModel D
          (Fin.cons
            (∑ e, g.inner x (B e) Rv • (B e : E))
            (fun _ : Fin 1 ↦ (v 1 : E))) :=
      (CurvatureCoefficientDifferenceJetTower.toModel_cons_sum_smul
        (E := E) x
        (Tensor0SSpace.toModel D)
        (Module.finrank ℝ E)
        (fun e ↦ g.inner x (B e) Rv)
        (fun e ↦ (B e : E))
        (fun _ : Fin 1 ↦ (v 1 : E))).symm
    _ = Tensor0SSpace.toModel D
          ![(∑ e, g.inner x (B e) Rv • (B e : E)), (v 1 : E)] := by
      rw [hpair]
    _ = _ := by
      rw [← hrep]

private lemma lc0RiemRF_eval
    (g : SmoothRiemannianMetric I M) (x : M)
    (D : Tensor0SSpace 2 I x) (v : Fin 4 → TangentSpace I x) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 4 I x from
          (rsDomDomCongrSection (I := I) (M := M) g 2 4
            lieCorr0VBPerm
            (reindexCoeffGen (I := I) (M := M) g 2 4
              (slotExtendIter (I := I) (M := M) g 1 3 1
                (slotFreeOpCc (I := I) (M := M) g 1))
              (Equiv.swap (0 : Fin 2) 1))).toSection x) D) v =
      -Tensor0SSpace.toModel D
        ![((riemannOp (LeviCivita (I := I) g) x
          (v 2) (v 3) (v 0) : TangentSpace I x) : E), (v 1 : E)] := by
  classical
  let Rv : TangentSpace I x :=
    riemannOp (LeviCivita (I := I) g) x (v 2) (v 3) (v 0)
  rw [rsDomDomCongrSection_toSection,
    toModel_rsDomDomCongr_apply,
    ContinuousMultilinearMap.domDomCongr_apply]
  have hout :
      (fun i : Fin 4 ↦ v (lieCorr0VBPerm i)) =
        ![v 1, v 2, v 3, v 0] := by
    funext i
    fin_cases i <;> rfl
  rw [hout]
  simp only [slotExtendIter, Nat.add_zero]
  set D' : Tensor0SSpace 2 I x :=
    Tensor0SSpace.ofModel (I := I) (x := x)
      (ContinuousMultilinearMap.domDomCongr
        (Equiv.swap (0 : Fin 2) 1)
        (Tensor0SSpace.toModel D)) with hD'_def
  have hreindex :
      ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 4 I x from
        (reindexCoeffGen (I := I) (M := M) g 2 4
          (slotExtend (I := I) (M := M) g 1 3
            (slotFreeOpCc (I := I) (M := M) g 1))
          (Equiv.swap (0 : Fin 2) 1)).toSection x) D) =
        slotExtendFib (I := I) (M := M) g 1 3 x
          (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 3 I x from
            (slotFreeOpCc (I := I) (M := M) g 1).toSection x) D' := by
    rw [hD'_def]
    exact reindexCoeffFibGen_apply
      (I := I) 2 4 (Equiv.swap (0 : Fin 2) 1) x _ D
  rw [hreindex]
  rw [show
    (![v 1, v 2, v 3, v 0] : Fin 4 → TangentSpace I x) =
      Fin.cons (v 1)
        (![v 2, v 3, v 0] : Fin 3 → TangentSpace I x) from by
    funext i
    fin_cases i <;> rfl]
  rw [slotExtendFib_apply_eval
    (I := I) (M := M) g 1 3 x
    (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 3 I x from
      (slotFreeOpCc (I := I) (M := M) g 1).toSection x)
    D' (v 1) (![v 2, v 3, v 0] : Fin 3 → E)]
  let A : Tensor0SSpace 1 I x :=
    tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x D' (v 1)
  let m : Fin 1 → TangentSpace I x := fun _ ↦ v 0
  have hcurv :
      (![v 2, v 3, v 0] : Fin 3 → TangentSpace I x) =
        Fin.cons (v 2) (Fin.cons (v 3) m) := by
    funext i
    fin_cases i <;> rfl
  have hpair :
      ![(Rv : E), (v 1 : E)] =
        Fin.cons (Rv : E) (fun _ : Fin 1 ↦ (v 1 : E)) := by
    funext i
    fin_cases i <;> rfl
  rw [hcurv, hpair]
  change
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 3 I x from
          (slotFreeOpCc (I := I) (M := M) g 1).toSection x) A)
        (Fin.cons (v 2) (Fin.cons (v 3) m)) =
      -Tensor0SSpace.toModel D
        (Fin.cons (Rv : E) (fun _ : Fin 1 ↦ (v 1 : E)))
  have hsf :
      Tensor0SSpace.toModel
          ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 3 I x from
            (slotFreeOpCc (I := I) (M := M) g 1).toSection x) A)
          (Fin.cons (v 2) (Fin.cons (v 3) m)) =
        -Tensor0SSpace.toModel A
          (Function.update m 0 Rv) := by
    rw [slotFreeOpCc_apply]
    simpa only [Fin.sum_univ_one] using
      slotFreeCurvOpFib_apply_eval
        (I := I) (M := M) g 1 x A (v 2) (v 3) m
  rw [hsf]
  have hupd :
      Function.update m (0 : Fin 1) Rv =
        fun _ : Fin 1 ↦ Rv := by
    funext i
    fin_cases i
    simp
  rw [hupd]
  change
    -Tensor0SSpace.toModel
        (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x
          D' (v 1))
        (fun _ : Fin 1 ↦ Rv) =
      -Tensor0SSpace.toModel D
        (Fin.cons (Rv : E) (fun _ : Fin 1 ↦ (v 1 : E)))
  rw [TensorMultilinear.tensor0S_curry_apply_eval
      (I := I) (M := M),
    hD'_def, Tensor0SSpace.toModel_ofModel,
    ContinuousMultilinearMap.domDomCongr_apply]
  congr 1
  apply congrArg (Tensor0SSpace.toModel D)
  funext i
  fin_cases i <;> rfl

/-- The fixed Riemann passenger is a source swap, one slot extension, and an
output permutation of the canonical rank-one free-slot curvature operator. -/
theorem lc0RiemPass_refold
    (g : SmoothRiemannianMetric I M) :
    lc0RiemPass (I := I) (M := M) g =
      -rsDomDomCongrSection (I := I) (M := M) g 2 4
        lieCorr0VBPerm
        (reindexCoeffGen (I := I) (M := M) g 2 4
          (slotExtendIter (I := I) (M := M) g 1 3 1
            (slotFreeOpCc (I := I) (M := M) g 1))
          (Equiv.swap (0 : Fin 2) 1)) := by
  classical
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [SmoothCcTensor.toSection_neg,
    ContMDiffSection.coe_neg, Pi.neg_apply]
  apply ContinuousLinearMap.ext
  intro D
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro v
  change Tensor0SSpace.toModel
      ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 4 I x from
        (lc0RiemPass (I := I) (M := M) g).toSection x) D) v =
    Tensor0SSpace.toModel
      (-((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 4 I x from
        (rsDomDomCongrSection (I := I) (M := M) g 2 4
          lieCorr0VBPerm
          (reindexCoeffGen (I := I) (M := M) g 2 4
            (slotExtendIter (I := I) (M := M) g 1 3 1
              (slotFreeOpCc (I := I) (M := M) g 1))
            (Equiv.swap (0 : Fin 2) 1))).toSection x) D)) v
  rw [Tensor0SSpace.toModel_neg,
    ContinuousMultilinearMap.neg_apply,
    lc0RiemPass_eval,
    lc0RiemRF_eval]
  ring

/-- Fibrewise form of the two-arm factorization of the fixed-curvature piece. -/
private theorem lc0RiemFib_eq (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) :
    lieCorr0RiemFib (I := I) g₀ g₁ x =
      -((show Tensor0SSpace 4 I x →L[ℝ] Tensor0SSpace 2 I x from
            (lc0RiemLive (I := I) (M := M) g₀ g₁).toSection x).comp
        (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 4 I x from
            (lc0RiemPass (I := I) g₀).toSection x)) := by
  rw [lieCorr0RiemFib, lc0RiemLive_fiber, neg_one_smul]
  rfl

/-- **The `lc0Riem` two-arm factorization.**  The fixed-curvature piece is the
operator-field action of the live rank-`2` cometric arm on the fixed passenger. -/
theorem lc0Riem_eq_app (g₀ g₁ : SmoothRiemannianMetric I M) :
    lc0Riem (I := I) (M := M) g₀ g₁ =
      -appCcRS (I := I) (M := M) g₀ 2 4 2
        (lc0RiemLive (I := I) (M := M) g₀ g₁) (lc0RiemPass (I := I) g₀) := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [SmoothCcTensor.toSection_neg, ContMDiffSection.coe_neg, Pi.neg_apply, appCcRS_toSection]
  exact lc0RiemFib_eq (I := I) (M := M) g₀ g₁ x

/-- Pointwise: the live arm's jets are dominated by the jets of the committed
rank-`1` cometric cast, at the cost of one factor of the dimension. -/
theorem lc0RiemLive_rfns_le (g₀ g₁ : SmoothRiemannianMetric I M) (m : ℕ) (x : M) :
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
theorem lc0RiemLive_l2_le (g₀ g₁ : SmoothRiemannianMetric I M) (m : ℕ) :
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
        iteratedCovGrad_add, iteratedCovGrad_smul, iteratedCovGrad_smul]
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

By `nEndo_diff` (`LieCorr0Split.lean:103`) the difference of insertion pieces is the `(2, 2)`
derivation insertion of the endomorphism
`connDiff g₁ g₀ (deTurckVF g₁ g₀) − connDiff g₁ g₀ (deTurckVF g₁ g_bg)`
= `connDiffDVFSection g₀ g₁ g₀ − connDiffDVFSection g₀ g₁ g_bg` (`endoDiffSection`).  Its
slot-`0` `(1, 1)` insertion is `cometricRaiseSlot0Field g₀ 0 (wAlphaB g₀ g₁ g₀ − wAlphaB g₀ g₁ g_bg)`
(producer HOIST `connDiffDVFInsert_eq_cometricRaise`).  Since `wAlphaB` is `∇²P`-free its jets are
`ballUniform` per order, so the `(1, 1)` object is bounded by the producer
`connDiffDVFInsertDiff_realizedFam_jetL2_perOrder_ballUniform` (crude triangle
`wAlphaB g₀ − wAlphaB g_bg`; the `wOmegaDiff_eq` cancellation is NOT needed for a `ballUniform`
bound).  Here we (a) prove the `(2, 2)` insert-difference is the slotInsert-sum of `endoDiffSection`
(`lc0InsDiff_eq`, mirroring `deTurckLieDLbCoeffField_eq_slotInsert_sum`), (b)
reduce it to the `(1, 1)` object `×4·finrank` (mirroring `normSq_iCG_dlbField_le`), and (c) chain the
producer bound to discharge the atom. -/

/-- Squared triangle over two summands (copied from `DeTurckLieCoeffL2JetBound`; the original is
`private`). -/
private theorem sq_le_two_add (t u v c1 c2 : ℝ) (ht : 0 ≤ t) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (htri : t ≤ u + v) (h1 : u ^ 2 ≤ c1) (h2 : v ^ 2 ≤ c2) : t ^ 2 ≤ 2 * (c1 + c2) := by
  have huv : 0 ≤ u + v := by linarith
  nlinarith [mul_le_mul htri htri ht huv, sq_nonneg (u - v), h1, h2, hu, hv]

set_option linter.unusedSectionVars false in
/-- Pointwise `rfns(∇^i X) ≤ c·rfns(∇^i Y)` upgrades to `‖∇^i X‖² ≤ c·‖∇^i Y‖²` (copied from
`DeTurckLieCoeffL2JetBound`; the original is `private`). -/
private theorem normSq_iCG_le_scaled (g₀ : SmoothRiemannianMetric I M)
    (X : SmoothCcTensor g₀ 2 2) (Y : SmoothCcTensor g₀ 1 1) (i : ℕ) (c : ℝ)
    (hpt : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
          ((iteratedCovGrad (I := I) g₀ 2 2 i X).toSection x) ≤
        c * riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + i) x
          ((iteratedCovGrad (I := I) g₀ 1 1 i Y).toSection x)) :
    ‖iteratedCovGrad (I := I) g₀ 2 2 i X‖ ^ 2 ≤
      c * ‖iteratedCovGrad (I := I) g₀ 1 1 i Y‖ ^ 2 := by
  have hF_int : MeasureTheory.Integrable
      (fun x => c * riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + i) x
        ((iteratedCovGrad (I := I) g₀ 1 1 i Y).toSection x))
      (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
    (integrable_riemannianFiberNormSq_toSection (I := I) (M := M) g₀ 1 (1 + i)
      (iteratedCovGrad (I := I) g₀ 1 1 i Y)).const_mul c
  have key := normSq_le_integral_of_pointwise_fiberNormSq_le_rs (I := I) (M := M) g₀ 2 (2 + i)
    (iteratedCovGrad (I := I) g₀ 2 2 i X)
    (fun x => c * riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + i) x
      ((iteratedCovGrad (I := I) g₀ 1 1 i Y).toSection x))
    hF_int (fun x => hpt x)
  refine le_trans key (le_of_eq ?_)
  rw [MeasureTheory.integral_const_mul]
  congr 1
  rw [SmoothCcTensor.norm_def (I := I) (M := M) (iteratedCovGrad (I := I) g₀ 1 1 i Y)]
  exact (tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs (I := I) (M := M) g₀ 1 (1 + i)
    (iteratedCovGrad (I := I) g₀ 1 1 i Y)).symm

/-- The `(1, 1)` endomorphism-difference section carried by the `lc0Insert`-difference:
`connDiffDVFSection g₀ g₁ g₀ − connDiffDVFSection g₀ g₁ g_bg`; equals `lieCorr0NEndo g_bg − g₀`
pointwise (`nEndo_diff`). -/
def endoDiffSection (g₀ g₁ g_bg : SmoothRiemannianMetric I M) :
    ContMDiffSection I (E →L[ℝ] E) ∞ (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x) :=
  connDiffDVFSection (I := I) (M := M) g₀ g₁ g₀ -
    connDiffDVFSection (I := I) (M := M) g₀ g₁ g_bg

/-- Pointwise: the endo-difference section is the `lieCorr0NEndo` difference (`nEndo_diff`). -/
private lemma endoDiffSection_apply (g₀ g₁ g_bg : SmoothRiemannianMetric I M) (x : M) :
    endoDiffSection (I := I) (M := M) g₀ g₁ g_bg x =
      lieCorr0NEndo (I := I) g₀ g₁ g_bg x - lieCorr0NEndo (I := I) g₀ g₁ g₀ x := by
  simp only [endoDiffSection, ContMDiffSection.coe_sub, Pi.sub_apply]
  exact (nEndo_diff (I := I) (M := M) g₀ g₁ g_bg x).symm

set_option linter.unusedSectionVars false in
/-- **Field identity.**  The `lc0Insert`-difference is the slotInsert-sum of the endo-difference
section (mirrors `deTurckLieDLbCoeffField_eq_slotInsert_sum`). -/
theorem lc0InsDiff_eq (g₀ g₁ g_bg : SmoothRiemannianMetric I M) :
    lc0Insert (I := I) (M := M) g₀ g₁ g_bg - lc0Insert (I := I) (M := M) g₀ g₁ g₀ =
      slotInsertEndoCc (I := I) (M := M) g₀ 1 (endoDiffSection (I := I) (M := M) g₀ g₁ g_bg)
        + reindexCoeffGen (I := I) (M := M) g₀ 2 2
            (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1)
              (slotInsertEndoCc (I := I) (M := M) g₀ 1
                (endoDiffSection (I := I) (M := M) g₀ g₁ g_bg)))
            (Equiv.swap (0 : Fin 2) 1) := by
  classical
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [SmoothCcTensor.toSection_add, ContMDiffSection.coe_add, Pi.add_apply]
  apply ContinuousLinearMap.ext
  intro D
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro m
  have hsum : (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        (slotInsertEndoCc (I := I) (M := M) g₀ 1
            (endoDiffSection (I := I) (M := M) g₀ g₁ g_bg)).toSection x
          + (reindexCoeffGen (I := I) (M := M) g₀ 2 2
              (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1)
                (slotInsertEndoCc (I := I) (M := M) g₀ 1
                  (endoDiffSection (I := I) (M := M) g₀ g₁ g_bg)))
              (Equiv.swap (0 : Fin 2) 1)).toSection x) D
      = (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
          (slotInsertEndoCc (I := I) (M := M) g₀ 1
            (endoDiffSection (I := I) (M := M) g₀ g₁ g_bg)).toSection x) D
        + (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
          (reindexCoeffGen (I := I) (M := M) g₀ 2 2
              (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1)
                (slotInsertEndoCc (I := I) (M := M) g₀ 1
                  (endoDiffSection (I := I) (M := M) g₀ g₁ g_bg)))
              (Equiv.swap (0 : Fin 2) 1)).toSection x) D := rfl
  change Tensor0SSpace.toModel
      ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        (lc0Insert (I := I) (M := M) g₀ g₁ g_bg -
          lc0Insert (I := I) (M := M) g₀ g₁ g₀).toSection x) D) m =
    Tensor0SSpace.toModel
      ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        (slotInsertEndoCc (I := I) (M := M) g₀ 1
            (endoDiffSection (I := I) (M := M) g₀ g₁ g_bg)).toSection x
          + (reindexCoeffGen (I := I) (M := M) g₀ 2 2
              (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1)
                (slotInsertEndoCc (I := I) (M := M) g₀ 1
                  (endoDiffSection (I := I) (M := M) g₀ g₁ g_bg)))
              (Equiv.swap (0 : Fin 2) 1)).toSection x) D) m
  rw [hsum, Tensor0SSpace.toModel_add, ContinuousMultilinearMap.add_apply]
  rw [show (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        (lc0Insert (I := I) (M := M) g₀ g₁ g_bg -
          lc0Insert (I := I) (M := M) g₀ g₁ g₀).toSection x) D
      = lieCorr0InsertFib (I := I) g₀ g₁ g_bg x D -
          lieCorr0InsertFib (I := I) g₀ g₁ g₀ x D from rfl]
  rw [Tensor0SSpace.toModel_sub, ContinuousMultilinearMap.sub_apply]
  rw [lieCorr0InsertFib_toModel (I := I) g₀ g₁ g_bg x D m,
    lieCorr0InsertFib_toModel (I := I) g₀ g₁ g₀ x D m]
  rw [show (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        (slotInsertEndoCc (I := I) (M := M) g₀ 1
          (endoDiffSection (I := I) (M := M) g₀ g₁ g_bg)).toSection x) D
      = slotInsertEndoFib (I := I) (M := M) 2 0 x
          (endoDiffSection (I := I) (M := M) g₀ g₁ g_bg x) D from rfl]
  rw [slotInsertEndoFib_apply_eval (I := I) (M := M) 2 0 x
    (endoDiffSection (I := I) (M := M) g₀ g₁ g_bg x) D m]
  rw [show (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        (reindexCoeffGen (I := I) (M := M) g₀ 2 2
            (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1)
              (slotInsertEndoCc (I := I) (M := M) g₀ 1
                (endoDiffSection (I := I) (M := M) g₀ g₁ g_bg)))
            (Equiv.swap (0 : Fin 2) 1)).toSection x) D
      = reindexCoeffFibGen (I := I) 2 2 (Equiv.swap (0 : Fin 2) 1) x
          (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
            (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1)
              (slotInsertEndoCc (I := I) (M := M) g₀ 1
                (endoDiffSection (I := I) (M := M) g₀ g₁ g_bg))).toSection x) D from rfl]
  rw [reindexCoeffFibGen_apply (I := I) 2 2 (Equiv.swap (0 : Fin 2) 1) x
    (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
      (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1)
        (slotInsertEndoCc (I := I) (M := M) g₀ 1
          (endoDiffSection (I := I) (M := M) g₀ g₁ g_bg))).toSection x) D]
  rw [show (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1)
          (slotInsertEndoCc (I := I) (M := M) g₀ 1
            (endoDiffSection (I := I) (M := M) g₀ g₁ g_bg))).toSection x)
      = (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
          rsDomDomCongr (I := I) (M := M) (Equiv.swap (0 : Fin 2) 1)
            ((slotInsertEndoCc (I := I) (M := M) g₀ 1
              (endoDiffSection (I := I) (M := M) g₀ g₁ g_bg)).toSection x)) from rfl]
  rw [toModel_rsDomDomCongr_apply (I := I) (M := M) (Equiv.swap (0 : Fin 2) 1)
    ((slotInsertEndoCc (I := I) (M := M) g₀ 1
      (endoDiffSection (I := I) (M := M) g₀ g₁ g_bg)).toSection x)
    (Tensor0SSpace.ofModel
      (ContinuousMultilinearMap.domDomCongr (Equiv.swap (0 : Fin 2) 1)
        (Tensor0SSpace.toModel D)))]
  rw [ContinuousMultilinearMap.domDomCongr_apply]
  rw [show (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        (slotInsertEndoCc (I := I) (M := M) g₀ 1
          (endoDiffSection (I := I) (M := M) g₀ g₁ g_bg)).toSection x)
        (Tensor0SSpace.ofModel
          (ContinuousMultilinearMap.domDomCongr (Equiv.swap (0 : Fin 2) 1)
            (Tensor0SSpace.toModel D)))
      = slotInsertEndoFib (I := I) (M := M) 2 0 x
          (endoDiffSection (I := I) (M := M) g₀ g₁ g_bg x)
          (Tensor0SSpace.ofModel
            (ContinuousMultilinearMap.domDomCongr (Equiv.swap (0 : Fin 2) 1)
              (Tensor0SSpace.toModel D))) from rfl]
  rw [slotInsertEndoFib_apply_eval (I := I) (M := M) 2 0 x
    (endoDiffSection (I := I) (M := M) g₀ g₁ g_bg x)
    (Tensor0SSpace.ofModel
      (ContinuousMultilinearMap.domDomCongr (Equiv.swap (0 : Fin 2) 1)
        (Tensor0SSpace.toModel D)))
    (fun i => m ((Equiv.swap (0 : Fin 2) 1) i))]
  rw [Tensor0SSpace.toModel_ofModel, ContinuousMultilinearMap.domDomCongr_apply]
  have harg : (fun k => Function.update (fun i => m ((Equiv.swap (0 : Fin 2) 1) i)) 0
        (endoDiffSection (I := I) (M := M) g₀ g₁ g_bg x
          ((fun i => m ((Equiv.swap (0 : Fin 2) 1) i)) 0))
        ((Equiv.swap (0 : Fin 2) 1) k))
      = Function.update m 1
          (endoDiffSection (I := I) (M := M) g₀ g₁ g_bg x (m 1)) := by
    funext k
    have hswap0 : (Equiv.swap (0 : Fin 2) 1) 0 = 1 := Equiv.swap_apply_left 0 1
    have hswap1 : (Equiv.swap (0 : Fin 2) 1) 1 = 0 := Equiv.swap_apply_right 0 1
    simp only [Function.update_apply]
    rw [hswap0, Equiv.swap_apply_self]
    have hcond : ((Equiv.swap (0 : Fin 2) 1) k = 0) = (k = 1) := by
      apply propext
      constructor
      · intro h
        have h2 := congrArg (Equiv.swap (0 : Fin 2) 1) h
        rwa [Equiv.swap_apply_self, hswap0] at h2
      · intro h
        rw [h, hswap1]
    simp only [hcond]
  rw [harg]
  rw [endoDiffSection_apply (I := I) (M := M) g₀ g₁ g_bg x]
  rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.sub_apply]
  rw [ContinuousMultilinearMap.map_update_sub, ContinuousMultilinearMap.map_update_sub]
  ring

set_option linter.unusedSectionVars false in
/-- **`(2, 2) → (1, 1)` reduction.**  The `lc0Insert`-difference jet is bounded by
`4·finrank` times the slot-`0` insert of `endoDiffSection` (mirrors `normSq_iCG_dlbField_le`). -/
theorem normSq_iCG_lc0InsertDiff_le (g₀ g₁ g_bg : SmoothRiemannianMetric I M) (i : ℕ) :
    ‖iteratedCovGrad (I := I) g₀ 2 2 i
        (lc0Insert (I := I) (M := M) g₀ g₁ g_bg -
          lc0Insert (I := I) (M := M) g₀ g₁ g₀)‖ ^ 2 ≤
      4 * (Module.finrank ℝ E : ℝ) *
        ‖iteratedCovGrad (I := I) g₀ 1 1 i
          (slotInsertEndoCc (I := I) (M := M) g₀ 0
            (endoDiffSection (I := I) (M := M) g₀ g₁ g_bg))‖ ^ 2 := by
  have hL2A : ‖iteratedCovGrad (I := I) g₀ 2 2 i
      (slotInsertEndoCc (I := I) (M := M) g₀ 1
        (endoDiffSection (I := I) (M := M) g₀ g₁ g_bg))‖ ^ 2 ≤
      (Module.finrank ℝ E : ℝ) *
        ‖iteratedCovGrad (I := I) g₀ 1 1 i
          (slotInsertEndoCc (I := I) (M := M) g₀ 0
            (endoDiffSection (I := I) (M := M) g₀ g₁ g_bg))‖ ^ 2 :=
    normSq_iCG_le_scaled (I := I) (M := M) g₀
      (slotInsertEndoCc (I := I) (M := M) g₀ 1 (endoDiffSection (I := I) (M := M) g₀ g₁ g_bg))
      (slotInsertEndoCc (I := I) (M := M) g₀ 0 (endoDiffSection (I := I) (M := M) g₀ g₁ g_bg))
      i (Module.finrank ℝ E : ℝ)
      (fun x => by
        have h := rfns_iteratedCovGrad_slotInsertEndoCc_le_endo (I := I) (M := M) g₀ 1
          (endoDiffSection (I := I) (M := M) g₀ g₁ g_bg) i x
        rwa [pow_one] at h)
  have hL2B : ‖iteratedCovGrad (I := I) g₀ 2 2 i
      (reindexCoeffGen (I := I) (M := M) g₀ 2 2
        (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1)
          (slotInsertEndoCc (I := I) (M := M) g₀ 1
            (endoDiffSection (I := I) (M := M) g₀ g₁ g_bg)))
        (Equiv.swap (0 : Fin 2) 1))‖ ^ 2 ≤
      (Module.finrank ℝ E : ℝ) *
        ‖iteratedCovGrad (I := I) g₀ 1 1 i
          (slotInsertEndoCc (I := I) (M := M) g₀ 0
            (endoDiffSection (I := I) (M := M) g₀ g₁ g_bg))‖ ^ 2 :=
    normSq_iCG_le_scaled (I := I) (M := M) g₀
      (reindexCoeffGen (I := I) (M := M) g₀ 2 2
        (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1)
          (slotInsertEndoCc (I := I) (M := M) g₀ 1
            (endoDiffSection (I := I) (M := M) g₀ g₁ g_bg)))
        (Equiv.swap (0 : Fin 2) 1))
      (slotInsertEndoCc (I := I) (M := M) g₀ 0 (endoDiffSection (I := I) (M := M) g₀ g₁ g_bg))
      i (Module.finrank ℝ E : ℝ)
      (fun x => by
        have heq := rfns_iteratedCovGrad_rsDomDomCongr_both_eq (I := I) (M := M) g₀ 2 2
          (Equiv.swap (0 : Fin 2) 1) (Equiv.swap (0 : Fin 2) 1)
          (slotInsertEndoCc (I := I) (M := M) g₀ 1
            (endoDiffSection (I := I) (M := M) g₀ g₁ g_bg)) i x
        have h := rfns_iteratedCovGrad_slotInsertEndoCc_le_endo (I := I) (M := M) g₀ 1
          (endoDiffSection (I := I) (M := M) g₀ g₁ g_bg) i x
        rw [pow_one] at h
        exact heq.trans_le h)
  have hgrad : iteratedCovGrad (I := I) g₀ 2 2 i
        (lc0Insert (I := I) (M := M) g₀ g₁ g_bg - lc0Insert (I := I) (M := M) g₀ g₁ g₀)
      = iteratedCovGrad (I := I) g₀ 2 2 i
          (slotInsertEndoCc (I := I) (M := M) g₀ 1
            (endoDiffSection (I := I) (M := M) g₀ g₁ g_bg))
        + iteratedCovGrad (I := I) g₀ 2 2 i
            (reindexCoeffGen (I := I) (M := M) g₀ 2 2
              (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1)
                (slotInsertEndoCc (I := I) (M := M) g₀ 1
                  (endoDiffSection (I := I) (M := M) g₀ g₁ g_bg)))
              (Equiv.swap (0 : Fin 2) 1)) := by
    rw [lc0InsDiff_eq (I := I) (M := M) g₀ g₁ g_bg, iteratedCovGrad_add]
  rw [hgrad]
  refine le_trans (sq_le_two_add _ _ _ _ _ (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
    (norm_add_le _ _) hL2A hL2B) (le_of_eq (by ring))

set_option linter.unusedVariables false in
/-- **Per-order `ballUniform` jet-`L²` bound for the `lc0Insert`-difference piece.**  Reduces the
`(2, 2)` insert-difference to the `(1, 1)` `endoDiffSection` insert (`normSq_iCG_lc0InsertDiff_le`)
and chains the producer bound (`connDiffDVFInsertDiff_realizedFam_jetL2_perOrder_ballUniform`).  No
`sorry`: the former "missing engine" is the producer's HOIST + `wAlphaB` bound. -/
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
  obtain ⟨K, hK_nn, hK⟩ :=
    connDiffDVFInsertDiff_realizedFam_jetL2_perOrder_ballUniform (I := I) (M := M) g₀ g_bg a
      ha_super hR hδ₀
  have hfr_nn : (0 : ℝ) ≤ 4 * (Module.finrank ℝ E : ℝ) := by positivity
  refine ⟨fun i => 4 * (Module.finrank ℝ E : ℝ) * K i,
    fun i => mul_nonneg hfr_nn (hK_nn i), ?_⟩
  intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball i hi s hs
  have hprod := hK T T' hδ_le hδ hδ'_le hδ' hTball hT'ball i hi s hs
  have hred := normSq_iCG_lc0InsertDiff_le (I := I) (M := M) g₀
    (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg i
  simp only [endoDiffSection] at hred
  refine le_trans hred ?_
  exact mul_le_mul_of_nonneg_left hprod hfr_nn

set_option linter.unusedVariables false in
/-- **`lc0Insert`-difference `Kc` atom.**  Per-order top-separated jet-`L²` bound for
`lc0Insert g_bg − lc0Insert g₀` with vanishing top constant (`∇²T`-free: all of it
lands in the `R`-carrying `Kc`).  Proved from the `ballUniform` bound
`lc0InsertDiff_ballUniform` by the trivial `Ktop = 0` reshape (`K i ≤ K i·(1+low)`).
Sorry-free: the former "missing engine" is the producer HOIST
`connDiffDVFInsert_eq_cometricRaise` + `wAlphaB` per-order bound. -/
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

/-! ## The `lc0VB` `Kc` atom (`2·traceStep(g₁) ∘ prodKappa(metricConnDiffLowered) ∘ ip(deTurckVF)`)

`lc0VB g₀ g₁` (`LieCorr0Core:144`) is the vector-bundle contraction piece
`2 · traceStep(g₁, VBPerm) ∘ prodKappa(metricConnDiffLoweredFib g₁ g₁ g₀)
     ∘ interior_product(deTurckVF g₁ g₀)`.  Unlike `lc0Riem` (fixed g₀-only
passenger) and `lc0Insert`-diff (the `wAlphaB` slot-insert hoist), it carries
**two moving arms** — the g₁-lowered connection difference `metricConnDiffLowered
g₁ g₁ g₀` and the DeTurck field `deTurckVF g₁ g₀` — so neither of the two banked
routes applies.  It is a genuine interior-product contraction whose deTurckVF is a
single field (no g₀↔g_bg difference ⟹ no cancellation à la atom 2).

**RECON VERDICT (route 3 — a real engine gap; see the `.md` note).**  The Arm1
template `deTurckLieArm1Coeff_realizedFam_jetL2_perOrder_ballUniform`
(`DeTurckLieArm1CoeffL2JetBound.lean`) has the same *shape*, and its generic
*kernel* transfers: `lieArm1_deTurckVF_cometric_trace` expresses
`deTurckVF g₁ gB` as the g₁-cometric trace of `connDiff g₁ gB` (generic in `gB`),
and the committed product grid `rfns_iteratedCovGrad_appCcRS_diagonalProductGrid_rankLeft_le`
+ integrator `exists_integrated_iteratedCovGrad_diagonalProductGrid_twoArm_rs_le`
bound any resulting `appCcRS` (both already used by `lc0Riem`).  But the *end-to-end*
fold does NOT transfer: Arm1's `deTurckLieArm1Coeff_eq_lieArm1Piece_sum` is a
~2000-line Arm1-specific identity whose live arm is `deTurckLieTraceCoeff`
(traceHessian), not `metricConnDiffLowered`; `lieArm1_slot2_vf_trace` is
slot-2-of-rank-3 specific; and `metricConnDiffLowered g₁ g₁ g₀` has **no reusable
jet producer** (Arm1's `lieArm1LoweredBgKappa`/`lieArm1_kappa_feed` are private and
field-specific).  A tree-wide grep confirms there is no committed generic
interior-product-fold engine.  So `lc0VB` needs a hand-built fibre identity
`lieCorr0VBFib = reindexCoeffGen(appCcRS g₀ p a b Φ W)` plus per-order producers
for both connDiff-family arms — analogous to Arm1's `lieArm1PsiB`/`lieArm1_psiB_feed`
chain, not a one-lemma reuse.  Stated here with ONE isolated `sorry` at the
`ballUniform` frontier (as atom 2's first session did). -/

/-- **The `lc0VB` moving passenger fibre.**  Everything in `lieCorr0VBFib` to the right of the
outer `g₁`-cometric double trace: the `VBPerm` reindex, the `metricConnDiffLowered` product, and
the `deTurckVF` interior product.  A `(2, 4)` operator field. -/
private noncomputable def lc0VBPassFib (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) :
    Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 4 I x :=
  (domDomCongrFibRank (I := I) 4 lieCorr0VBPerm x).comp
    ((tensor0SProdKappaFib (I := I) (p := 1) (q := 3) x
        (metricConnDiffLoweredFib (I := I) g₁ g₁ g₀ x)).comp
      (Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) 1 x
        ((PDE.DeTurck.deTurckVF (I := I) g₁ g₀ : Π b : M, TangentSpace I b) x)))

private theorem lc0VBPassFib_contMDiff (g₀ g₁ : SmoothRiemannianMetric I M) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 2 4 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel 2 4 ℝ E)
        (E := fun z : M => TensorRSSpace 2 4 I z) x
        (TensorRSSpace.ofCLM (lc0VBPassFib (I := I) g₀ g₁ x))) := by
  classical
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (F₁ := Tensor0SModel 2 ℝ E) (V₁ := fun x : M => Tensor0SSpace 2 I x)
    (F₂ := Tensor0SModel 4 ℝ E) (V₂ := fun x : M => Tensor0SSpace 4 I x)
    (φ := fun x => lc0VBPassFib (I := I) g₀ g₁ x)
  intro Y
  have hip : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 1 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SModel 1 ℝ E)
        (E := fun z : M => Tensor0SSpace 1 I z) x
        (Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) 1 x
          ((PDE.DeTurck.deTurckVF (I := I) g₁ g₀ : Π b : M, TangentSpace I b) x) (Y x))) :=
    (Tensor0SBundle.contract_Tensor0SField (𝕜 := ℝ) (I := I) (n := (∞ : WithTop ℕ∞)) 1 Y
      (PDE.DeTurck.deTurckVF (I := I) g₁ g₀)).contMDiff
  have hprod := lieCorr0_prod_section_contMDiff (I := I) (p := 1) (q := 3)
    (fun x => Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) 1 x
      ((PDE.DeTurck.deTurckVF (I := I) g₁ g₀ : Π b : M, TangentSpace I b) x) (Y x))
    (fun x => metricConnDiffLoweredFib (I := I) g₁ g₁ g₀ x)
    hip (metricConnDiffLoweredFib_contMDiff (I := I) g₁ g₁ g₀)
  have hddc := lieCorr0_ddc_section_contMDiff (I := I) (d := 4) lieCorr0VBPerm
    (fun x => tensor0SProdKappaFib (I := I) x (metricConnDiffLoweredFib (I := I) g₁ g₁ g₀ x)
      (Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) 1 x
        ((PDE.DeTurck.deTurckVF (I := I) g₁ g₀ : Π b : M, TangentSpace I b) x) (Y x)))
    hprod
  refine hddc.congr (fun x => ?_)
  refine congrArg (fun t => TotalSpace.mk' (Tensor0SModel 4 ℝ E)
    (E := fun z : M => Tensor0SSpace 4 I z) x t) ?_
  rw [lc0VBPassFib]
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, domDomCongrFibRank_apply]

/-- **The `lc0VB` moving passenger.**  The `(2, 4)` operator field carrying the `VBPerm` reindex,
the `metricConnDiffLowered` product, and the `deTurckVF` interior product.  Public for the
radius-free re-derivation (brick 4). -/
noncomputable def lc0VBPass (g₀ g₁ : SmoothRiemannianMetric I M) :
    SmoothCcTensor g₀ 2 4 where
  toSection :=
    { toFun := fun x : M =>
        (show TensorRSSpace 2 4 I x from
          TensorRSSpace.ofCLM (lc0VBPassFib (I := I) g₀ g₁ x))
      contMDiff_toFun := lc0VBPassFib_contMDiff (I := I) g₀ g₁ }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

/-- Fibrewise two-arm factorization: the live rank-`2` `g₁`-cometric double trace (shared with
`lc0Riem` via `lc0RiemLive`) acting on the moving passenger. -/
private theorem lc0VBFib_eq (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) :
    lieCorr0VBFib (I := I) g₀ g₁ x =
      (2 : ℝ) • ((show Tensor0SSpace 4 I x →L[ℝ] Tensor0SSpace 2 I x from
            (lc0RiemLive (I := I) (M := M) g₀ g₁).toSection x).comp
        (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 4 I x from
            (lc0VBPass (I := I) (M := M) g₀ g₁).toSection x)) := by
  rw [lieCorr0VBFib, lc0RiemLive_fiber]
  rfl

/-- **The `lc0VB` two-arm factorization.**  The vector-bundle contraction piece is `2 ·` the
operator-field action of the live rank-`2` cometric arm (reused from `lc0Riem`) on the moving
passenger `lc0VBPass`.  Public for the radius-free re-derivation (brick 4). -/
theorem lc0VB_eq_app (g₀ g₁ : SmoothRiemannianMetric I M) :
    lc0VB (I := I) (M := M) g₀ g₁ =
      (2 : ℝ) • appCcRS (I := I) (M := M) g₀ 2 4 2
        (lc0RiemLive (I := I) (M := M) g₀ g₁) (lc0VBPass (I := I) (M := M) g₀ g₁) := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [SmoothCcTensor.toSection_smul, ContMDiffSection.coe_smul, Pi.smul_apply, appCcRS_toSection]
  exact lc0VBFib_eq (I := I) (M := M) g₀ g₁ x

/-! ### `vbPass` discharge machinery: the two-arm split of the moving passenger

`lc0VBPass = [ddc(VBPerm) ∘ prodKappa(mcd)] ∘ ip(deTurckVF)`, split as
`appCcRS g₀ 2 1 4 vbMcdArm (ipLowCc g₀ (wOmega g₀ g₁ g₀))`:

* `vbMcdArm` is the `(1, 4)` head; its jets equal (`rfns_iteratedCovGrad_rs_eq_of_section_domDomCongr`
  + the `prodKappa = slotExtend` identity `vbPK_eq_slotExt`) the jets of
  `slotExtend (metricConnDiffLoweredCc g₀ g₁ g₀)`, hence reduce to the session-6 producer;
* the `ip` tail is the committed `ipLowCc` at `ω := wOmega g₀ g₁ g₀` (the `g₀`-lowered
  `deTurckVF g₁ g₀`, by `wOmega_unitModel_apply`), with jets from `wOmega`'s producer. -/

/-- The `(1, 4)` head of the moving passenger: the `VBPerm` reindex composed with the
`metricConnDiffLowered` product. -/
private noncomputable def vbMcdArmFib (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) :
    Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 4 I x :=
  (domDomCongrFibRank (I := I) 4 lieCorr0VBPerm x).comp
    (tensor0SProdKappaFib (I := I) (p := 1) (q := 3) x
      (metricConnDiffLoweredFib (I := I) g₁ g₁ g₀ x))

private theorem vbMcdArmFib_contMDiff (g₀ g₁ : SmoothRiemannianMetric I M) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 1 4 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel 1 4 ℝ E)
        (E := fun z : M => TensorRSSpace 1 4 I z) x
        (TensorRSSpace.ofCLM (vbMcdArmFib (I := I) g₀ g₁ x))) := by
  classical
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (F₁ := Tensor0SModel 1 ℝ E) (V₁ := fun x : M => Tensor0SSpace 1 I x)
    (F₂ := Tensor0SModel 4 ℝ E) (V₂ := fun x : M => Tensor0SSpace 4 I x)
    (φ := fun x => vbMcdArmFib (I := I) g₀ g₁ x)
  intro Y
  have hprod := lieCorr0_prod_section_contMDiff (I := I) (p := 1) (q := 3)
    (fun x => Y x) (fun x => metricConnDiffLoweredFib (I := I) g₁ g₁ g₀ x)
    Y.contMDiff (metricConnDiffLoweredFib_contMDiff (I := I) g₁ g₁ g₀)
  have hddc := lieCorr0_ddc_section_contMDiff (I := I) (d := 4) lieCorr0VBPerm
    (fun x => tensor0SProdKappaFib (I := I) x (metricConnDiffLoweredFib (I := I) g₁ g₁ g₀ x)
      (Y x)) hprod
  refine hddc.congr (fun x => ?_)
  refine congrArg (fun t => TotalSpace.mk' (Tensor0SModel 4 ℝ E)
    (E := fun z : M => Tensor0SSpace 4 I z) x t) ?_
  rw [vbMcdArmFib]
  rw [ContinuousLinearMap.comp_apply, domDomCongrFibRank_apply]

/-- The `(1, 4)` head of the `lc0VB` moving passenger (`VBPerm` reindex ∘ `metricConnDiffLowered`
product) as a smooth compactly-supported operator field.  Public for the radius-free
re-derivation (brick 4). -/
noncomputable def vbMcdArm (g₀ g₁ : SmoothRiemannianMetric I M) :
    SmoothCcTensor g₀ 1 4 where
  toSection :=
    { toFun := fun x : M =>
        (show TensorRSSpace 1 4 I x from
          TensorRSSpace.ofCLM (vbMcdArmFib (I := I) g₀ g₁ x))
      contMDiff_toFun := vbMcdArmFib_contMDiff (I := I) g₀ g₁ }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

/-- Leaf-local unit-model read of the `metricConnDiffLowered` arm (clone of the Arm1-private
`metricConnDiffLoweredCc_unitModel_apply` at `g_bg := g₀`). -/
private lemma vbMcd_unitModel (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (m : Fin 3 → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 3 (metricConnDiffLoweredCc (I := I) (M := M) g₀ g₁ g₀) x m =
      g₁.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (m 0) (m 1)) (m 2) := by
  rw [unitModel]
  rw [show (metricConnDiffLoweredCc (I := I) (M := M) g₀ g₁ g₀).toSection x
      (unitTensor (I := I) (M := M) x) =
      (MixedSection.eval₀ (F := E) (E := (TangentSpace I : M → Type _)) x).smulRight
          (metricConnDiffLoweredFib (I := I) g₁ g₁ g₀ x)
          (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))
      from rfl]
  rw [ContinuousLinearMap.smulRight_apply, MixedSection.eval₀_apply,
    ContinuousMultilinearMap.constOfIsEmpty_apply, one_smul]
  exact metricConnDiffLoweredFib_toModel (I := I) g₁ g₁ g₀ x m

set_option linter.unusedSectionVars false in
/-- Rank-`0` tensors are scalar multiples of the unit tensor (leaf-local clone). -/
private lemma vb_rank0_smul_unit (x : M) (c : Tensor0SSpace 0 I x) :
    c = Tensor0SSpace.toModel c (fun i : Fin 0 => i.elim0) •
      unitTensor (I := I) (M := M) x := by
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro v
  beta_reduce
  rw [Tensor0SSpace.toModel_smul, ContinuousMultilinearMap.smul_apply, smul_eq_mul]
  have h1 : Tensor0SSpace.toModel (unitTensor (I := I) (M := M) x) v = (1 : ℝ) := rfl
  rw [h1, mul_one]
  congr 1
  funext i
  exact i.elim0

/-- **The session-8 `prodKappa = slotExtend` identity** (Finding 1): the
`metricConnDiffLowered` product factor of `lc0VBPass` is the slot extension of the
`metricConnDiffLoweredCc` tensor. -/
private lemma vbPK_eq_slotExt (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (B : Tensor0SSpace 1 I x) :
    Tensor0SSpace.toModel
        (tensor0SProdKappaFib (I := I) (p := 1) (q := 3) x
          (metricConnDiffLoweredFib (I := I) g₁ g₁ g₀ x) B) =
      Tensor0SSpace.toModel
        (slotExtendFib (I := I) (M := M) g₀ 0 3 x
          (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
            (metricConnDiffLoweredCc (I := I) (M := M) g₀ g₁ g₀).toSection x) B) := by
  classical
  apply ContinuousMultilinearMap.ext
  intro u
  rw [show (u : Fin 4 → E) = Fin.cons (u 0) (Fin.tail u) from (Fin.cons_self_tail u).symm]
  rw [tensor0SProdKappaFib_apply, Tensor0SSpace.toModel_ofModel,
    Bundle.continuousMultilinearMap.modelProduct_apply]
  rw [slotExtendFib_apply_eval (I := I) (M := M) g₀ 0 3 x
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
      (metricConnDiffLoweredCc (I := I) (M := M) g₀ g₁ g₀).toSection x) B (u 0) (Fin.tail u)]
  have hc : tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 0 x B (u 0) =
      Tensor0SSpace.toModel B (fun _ : Fin 1 => u 0) • unitTensor (I := I) (M := M) x := by
    have h2 := vb_rank0_smul_unit (I := I) (M := M) x
      (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 0 x B (u 0))
    rw [h2]
    congr 1
    rw [TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M) (T := B) (v0 := u 0)
      (vs := fun i : Fin 0 => i.elim0)]
    congr 1
    funext k
    fin_cases k
    rfl
  rw [hc, ContinuousLinearMap.map_smul, Tensor0SSpace.toModel_smul,
    ContinuousMultilinearMap.smul_apply, smul_eq_mul]
  rw [show Tensor0SSpace.toModel
      ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
        (metricConnDiffLoweredCc (I := I) (M := M) g₀ g₁ g₀).toSection x)
        (unitTensor (I := I) (M := M) x)) (Fin.tail u) =
      unitModel (I := I) (M := M) g₀ 3 (metricConnDiffLoweredCc (I := I) (M := M) g₀ g₁ g₀) x
        (fun j => Fin.tail u j) from by rw [unitModel]]
  rw [vbMcd_unitModel (I := I) (M := M) g₀ g₁ x (fun j => Fin.tail u j)]
  have hcast : ((Fin.cons (u 0) (Fin.tail u) : Fin 4 → E) ∘ Fin.castAdd 3) =
      (fun _ : Fin 1 => u 0) := by
    funext i
    fin_cases i
    rfl
  have hnat : ((Fin.cons (u 0) (Fin.tail u) : Fin 4 → E) ∘ Fin.natAdd 1) = Fin.tail u := by
    funext j
    have hj : Fin.natAdd 1 j = Fin.succ j := by
      apply Fin.ext
      simp [Fin.natAdd, Fin.succ, Nat.add_comm]
    change Fin.cons (u 0) (Fin.tail u) (Fin.natAdd 1 j) = Fin.tail u j
    rw [hj, Fin.cons_succ]
  rw [hcast, hnat]
  rw [metricConnDiffLoweredFib_toModel (I := I) g₁ g₁ g₀ x (fun j => Fin.tail u j)]

/-- The head's jets read as an output-slot permutation of `slotExtend (mcdCc)`. -/
private lemma vbMcdArm_rel (g₀ g₁ : SmoothRiemannianMetric I M) :
    ∀ (y : M) (d : Tensor0SSpace 1 I y),
      Tensor0SSpace.toModel
          ((show Tensor0SSpace 1 I y →L[ℝ] Tensor0SSpace 4 I y from
            (vbMcdArm (I := I) (M := M) g₀ g₁).toSection y) d) =
        ContinuousMultilinearMap.domDomCongr lieCorr0VBPerm
          (Tensor0SSpace.toModel
            ((show Tensor0SSpace 1 I y →L[ℝ] Tensor0SSpace 4 I y from
              (slotExtend (I := I) (M := M) g₀ 0 3
                (metricConnDiffLoweredCc (I := I) (M := M) g₀ g₁ g₀)).toSection y) d)) := by
  intro y d
  rw [show ((show Tensor0SSpace 1 I y →L[ℝ] Tensor0SSpace 4 I y from
      (vbMcdArm (I := I) (M := M) g₀ g₁).toSection y) d) =
      domDomCongrFibRank (I := I) 4 lieCorr0VBPerm y
        (tensor0SProdKappaFib (I := I) (p := 1) (q := 3) y
          (metricConnDiffLoweredFib (I := I) g₁ g₁ g₀ y) d) from rfl]
  rw [domDomCongrFibRank_apply, Tensor0SSpace.toModel_ofModel]
  exact congrArg (ContinuousMultilinearMap.domDomCongr lieCorr0VBPerm)
    (vbPK_eq_slotExt (I := I) (M := M) g₀ g₁ y d)

/-- Pointwise: the head's jets are dominated by the `metricConnDiffLowered` jets. -/
lemma vbMcdArm_rfns_le (g₀ g₁ : SmoothRiemannianMetric I M) (m : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 1 (4 + m) x
        ((iteratedCovGrad (I := I) g₀ 1 4 m (vbMcdArm (I := I) (M := M) g₀ g₁)).toSection x) ≤
      (Module.finrank ℝ E : ℝ) *
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + m) x
          ((iteratedCovGrad (I := I) g₀ 0 3 m
            (metricConnDiffLoweredCc (I := I) (M := M) g₀ g₁ g₀)).toSection x) := by
  rw [rfns_iteratedCovGrad_rs_eq_of_section_domDomCongr (I := I) (M := M) g₀ 1 4
    lieCorr0VBPerm
    (slotExtend (I := I) (M := M) g₀ 0 3 (metricConnDiffLoweredCc (I := I) (M := M) g₀ g₁ g₀))
    (vbMcdArm (I := I) (M := M) g₀ g₁) (vbMcdArm_rel (I := I) (M := M) g₀ g₁) m x]
  exact rfns_iteratedCovGrad_slotExtend_le (I := I) (M := M) g₀ 0 3
    (metricConnDiffLoweredCc (I := I) (M := M) g₀ g₁ g₀) m x

/-- `L²` form of `vbMcdArm_rfns_le`. -/
lemma vbMcdArm_l2_le (g₀ g₁ : SmoothRiemannianMetric I M) (m : ℕ) :
    ‖iteratedCovGrad (I := I) g₀ 1 4 m (vbMcdArm (I := I) (M := M) g₀ g₁)‖ ^ 2 ≤
      (Module.finrank ℝ E : ℝ) *
        ‖iteratedCovGrad (I := I) g₀ 0 3 m
          (metricConnDiffLoweredCc (I := I) (M := M) g₀ g₁ g₀)‖ ^ 2 := by
  have hint : MeasureTheory.Integrable
      (fun x => (Module.finrank ℝ E : ℝ) *
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + m) x
          ((iteratedCovGrad (I := I) g₀ 0 3 m
            (metricConnDiffLoweredCc (I := I) (M := M) g₀ g₁ g₀)).toSection x))
      (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
    (integrable_riemannianFiberNormSq_toSection (I := I) (M := M) g₀ 0 (3 + m)
      (iteratedCovGrad (I := I) g₀ 0 3 m
        (metricConnDiffLoweredCc (I := I) (M := M) g₀ g₁ g₀))).const_mul _
  have key := normSq_le_integral_of_pointwise_fiberNormSq_le_rs (I := I) (M := M) g₀ 1 (4 + m)
    (iteratedCovGrad (I := I) g₀ 1 4 m (vbMcdArm (I := I) (M := M) g₀ g₁)) _ hint
    (fun x => vbMcdArm_rfns_le (I := I) (M := M) g₀ g₁ m x)
  refine le_trans key (le_of_eq ?_)
  rw [MeasureTheory.integral_const_mul]
  refine congrArg _ ?_
  rw [← tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs (I := I) (M := M) g₀ 0 (3 + m)
      (iteratedCovGrad (I := I) g₀ 0 3 m
        (metricConnDiffLoweredCc (I := I) (M := M) g₀ g₁ g₀)),
    ← SmoothCcTensor.norm_def]

/-- **The two-arm split of the moving passenger**: `lc0VBPass` is the operator-field action of
the `(1, 4)` head on the interior-product tail `ipLowCc (wOmega g₀ g₁ g₀)`.  Public for the
radius-free re-derivation (brick 4). -/
theorem vbSplit (g₀ g₁ : SmoothRiemannianMetric I M) :
    lc0VBPass (I := I) (M := M) g₀ g₁ =
      appCcRS (I := I) (M := M) g₀ 2 1 4 (vbMcdArm (I := I) (M := M) g₀ g₁)
        (ipLowCc (I := I) (M := M) g₀ (wOmega (I := I) (M := M) g₀ g₁ g₀)) := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [appCcRS_toSection]
  have hflat : ∀ z : TangentSpace I x,
      unitModel (I := I) (M := M) g₀ 1 (wOmega (I := I) (M := M) g₀ g₁ g₀) x
          (fun _ : Fin 1 => z) =
        g₀.inner x ((PDE.DeTurck.deTurckVF (I := I) g₁ g₀ :
          Π b : M, TangentSpace I b) x) z := by
    intro z
    rw [wOmega_unitModel_apply (I := I) (M := M) g₀ g₁ g₀ x z]
    rfl
  rw [ipLowCc_toSec_ip (I := I) (M := M) g₀ (wOmega (I := I) (M := M) g₀ g₁ g₀) x
    ((PDE.DeTurck.deTurckVF (I := I) g₁ g₀ : Π b : M, TangentSpace I b) x) hflat]
  rfl

set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
/-- **VBPass jet bound (discharged).**  The g₁-generic order-`0` fibre-norm sup + per-order
jet-`L²` sum bounds for the moving passenger `lc0VBPass g₀ g₁ = domDomCongr(VBPerm) ∘
prodKappa(metricConnDiffLoweredFib g₁ g₁ g₀) ∘ ip(deTurckVF g₁ g₀)`.  Via the two-arm split
`vbSplit` (`lc0VBPass = appCcRS g₀ 2 1 4 vbMcdArm (ipLowCc g₀ (wOmega g₀ g₁ g₀))`), the
product grid, and the two-arm integrator: the head's jets reduce to the session-6
`metricConnDiffLoweredCc` producer (output-permutation invariance + `slotExtend`), and the
interior-product tail's jets reduce through the committed `ipLowCc` engine to the `wOmega`
producer (the `g₀`-lowered `deTurckVF`). -/
private theorem vbPass_jetL2
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ (Λ : ℝ) (F : ℕ → ℝ), 0 ≤ Λ ∧ (∀ i, 0 ≤ F i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ≤ R) →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 2 4 x
            ((lc0VBPass (I := I) (M := M) g₀ g₁).toSection x) ≤ Λ) ∧
        ∀ (i : ℕ), i ≤ a →
          ∑ q ∈ Finset.range (i + 1),
            ‖iteratedCovGrad (I := I) g₀ 2 4 q (lc0VBPass (I := I) (M := M) g₀ g₁)‖ ^ 2 ≤ F i := by
  classical
  obtain ⟨Λmcd, Fmcd, hΛmcd_nn, hFmcd_nn, hmcd⟩ :=
    metricConnDiffLoweredCc_jetL2_ballUniform_generic (I := I) (M := M) g₀ g₀ a ha_super hR hδ₀
  obtain ⟨cip, hcip_nn, hcip⟩ := rfns_icg_ipLow_le (I := I) (M := M) g₀
  obtain ⟨cipL, hcipL_nn, hcipL⟩ := norm_icg_ipLow_le (I := I) (M := M) g₀
  obtain ⟨ΛΩ, FΩ, hΛΩ_nn, hFΩ_nn, hΩgen⟩ :=
    wOmega_lowOrder_jetL2_succ_generic (I := I) (M := M) g₀ g₀ a ha_super hR hδ₀
  choose CI hCI_nn hCI using
    (fun k : ℕ => exists_integrated_iteratedCovGrad_diagonalProductGrid_twoArm_rs_le
      (I := I) (M := M) g₀ 1 2 4 1 k)
  set n : ℝ := (Module.finrank ℝ E : ℝ) with hn
  have hn_nn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  set BS : ℝ := n * Λmcd with hBS
  set BT : ℝ := cip 0 * ΛΩ 0 with hBT
  have hBS_nn : 0 ≤ BS := mul_nonneg hn_nn hΛmcd_nn
  have hBT_nn : 0 ≤ BT := mul_nonneg (hcip_nn 0) (hΛΩ_nn 0)
  set F : ℕ → ℝ := fun i => ∑ q ∈ Finset.range (i + 1),
    appCcGdiag (E := E) q * (CI q * (BT * (n * Fmcd q)
      + BS * ∑ l ∈ Finset.range (q + 1), cipL l * FΩ l)) with hF_def
  have hF_nn : ∀ i, 0 ≤ F i := fun i => Finset.sum_nonneg (fun q _ =>
    mul_nonneg (appCcGdiag_nonneg (E := E) q) (mul_nonneg (hCI_nn q)
      (add_nonneg (mul_nonneg hBT_nn (mul_nonneg hn_nn (hFmcd_nn q)))
        (mul_nonneg hBS_nn (Finset.sum_nonneg (fun l _ =>
          mul_nonneg (hcipL_nn l) (hFΩ_nn l)))))))
  refine ⟨BS * BT, F, mul_nonneg hBS_nn hBT_nn, hF_nn, ?_⟩
  intro g₁ P δ hδ_le hδ htie hPball
  by_cases hM : Nonempty M
  · -- nonempty: derive `0 ≤ δ` from the fibre bound and feed the two producers
    obtain ⟨x0⟩ := hM
    have hδ0 : 0 ≤ δ := by
      haveI : Nontrivial E := Module.nontrivial_of_finrank_pos (R := ℝ) (M := E)
        (Nat.pos_of_ne_zero (NeZero.ne _))
      obtain ⟨v, hv⟩ := exists_ne (0 : E)
      have hgpos : 0 < g₀.inner x0 (show TangentSpace I x0 from v)
          (show TangentSpace I x0 from v) :=
        g₀.pos x0 (show TangentSpace I x0 from v) hv
      have hb := hδ x0 (show TangentSpace I x0 from v) (show TangentSpace I x0 from v)
      have h1 : 0 ≤ δ * Real.sqrt (g₀.inner x0 (show TangentSpace I x0 from v)
            (show TangentSpace I x0 from v)) *
          Real.sqrt (g₀.inner x0 (show TangentSpace I x0 from v)
            (show TangentSpace I x0 from v)) :=
        le_trans (abs_nonneg _) hb
      rw [mul_assoc, Real.mul_self_sqrt (le_of_lt hgpos)] at h1
      exact (mul_nonneg_iff_of_pos_right hgpos).mp h1
    obtain ⟨hmcd_sup, hmcd_jets⟩ := hmcd g₁ P htie hδ_le hδ0 hδ hPball
    obtain ⟨hΩ_sup, hΩ_jets⟩ := hΩgen g₁ P htie hδ_le hδ0 hδ hPball
    have hS_sup : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 1 4 x
        ((vbMcdArm (I := I) (M := M) g₀ g₁).toSection x) ≤ Real.sqrt BS ^ 2 := by
      intro x
      have h := vbMcdArm_rfns_le (I := I) (M := M) g₀ g₁ 0 x
      rw [iteratedCovGrad_zero, iteratedCovGrad_zero] at h
      rw [Real.sq_sqrt hBS_nn]
      exact le_trans h (mul_le_mul_of_nonneg_left (hmcd_sup x) hn_nn)
    have hT_sup : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 2 1 x
        ((ipLowCc (I := I) (M := M) g₀
          (wOmega (I := I) (M := M) g₀ g₁ g₀)).toSection x) ≤ Real.sqrt BT ^ 2 := by
      intro x
      have h := hcip (wOmega (I := I) (M := M) g₀ g₁ g₀) 0 x
      rw [iteratedCovGrad_zero] at h
      rw [Real.sq_sqrt hBT_nn]
      refine le_trans h ?_
      rw [Finset.sum_range_one]
      exact mul_le_mul_of_nonneg_left (hΩ_sup 0 (by omega) x) (hcip_nn 0)
    refine ⟨?_, ?_⟩
    · -- order-0 fibre sup for the passenger, via the product grid at order 0
      intro x
      rw [vbSplit (I := I) (M := M) g₀ g₁]
      have h := rfns_iteratedCovGrad_appCcRS_diagonalProductGrid_rankLeft_le
        (I := I) (M := M) g₀ 0 2 1 4 (vbMcdArm (I := I) (M := M) g₀ g₁)
        (ipLowCc (I := I) (M := M) g₀ (wOmega (I := I) (M := M) g₀ g₁ g₀)) x
      rw [appCcGdiag, pow_zero, one_mul, Finset.sum_range_one, Finset.sum_range_one] at h
      simp only [iteratedCovGrad_zero] at h
      refine le_trans h ?_
      have h1 := hS_sup x
      rw [Real.sq_sqrt hBS_nn] at h1
      have h2 := hT_sup x
      rw [Real.sq_sqrt hBT_nn] at h2
      exact mul_le_mul h1 h2
        (riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 2 1 x _) hBS_nn
    · -- per-order jet-`L²` sums
      intro i hi
      rw [vbSplit (I := I) (M := M) g₀ g₁]
      simp only [hF_def]
      refine Finset.sum_le_sum (fun q hq => ?_)
      have hq_le : q ≤ a := by
        rw [Finset.mem_range] at hq
        omega
      obtain ⟨hI_int, hI_le⟩ := hCI q (vbMcdArm (I := I) (M := M) g₀ g₁)
        (ipLowCc (I := I) (M := M) g₀ (wOmega (I := I) (M := M) g₀ g₁ g₀))
        (Real.sqrt BS) (Real.sqrt BT) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
        hS_sup hT_sup
      have key := normSq_le_integral_of_pointwise_fiberNormSq_le_rs (I := I) (M := M) g₀ 2 (4 + q)
        (iteratedCovGrad (I := I) g₀ 2 4 q
          (appCcRS (I := I) (M := M) g₀ 2 1 4 (vbMcdArm (I := I) (M := M) g₀ g₁)
            (ipLowCc (I := I) (M := M) g₀ (wOmega (I := I) (M := M) g₀ g₁ g₀)))) _
        (hI_int.const_mul (appCcGdiag (E := E) q))
        (fun x => rfns_iteratedCovGrad_appCcRS_diagonalProductGrid_rankLeft_le
          (I := I) (M := M) g₀ q 2 1 4 (vbMcdArm (I := I) (M := M) g₀ g₁)
          (ipLowCc (I := I) (M := M) g₀ (wOmega (I := I) (M := M) g₀ g₁ g₀)) x)
      refine le_trans key ?_
      rw [MeasureTheory.integral_const_mul]
      refine le_trans (mul_le_mul_of_nonneg_left hI_le (appCcGdiag_nonneg (E := E) q)) ?_
      rw [Real.sq_sqrt hBS_nn, Real.sq_sqrt hBT_nn]
      refine mul_le_mul_of_nonneg_left ?_ (appCcGdiag_nonneg (E := E) q)
      refine mul_le_mul_of_nonneg_left ?_ (hCI_nn q)
      refine add_le_add ?_ ?_
      · refine mul_le_mul_of_nonneg_left ?_ hBT_nn
        calc ∑ m ∈ Finset.range (q + 1),
              ‖iteratedCovGrad (I := I) g₀ 1 4 m (vbMcdArm (I := I) (M := M) g₀ g₁)‖ ^ 2
            ≤ ∑ m ∈ Finset.range (q + 1), n *
              ‖iteratedCovGrad (I := I) g₀ 0 3 m
                (metricConnDiffLoweredCc (I := I) (M := M) g₀ g₁ g₀)‖ ^ 2 :=
              Finset.sum_le_sum (fun m _ => vbMcdArm_l2_le (I := I) (M := M) g₀ g₁ m)
          _ = n * ∑ m ∈ Finset.range (q + 1),
              ‖iteratedCovGrad (I := I) g₀ 0 3 m
                (metricConnDiffLoweredCc (I := I) (M := M) g₀ g₁ g₀)‖ ^ 2 :=
              (Finset.mul_sum _ _ _).symm
          _ ≤ n * Fmcd q := mul_le_mul_of_nonneg_left (hmcd_jets q hq_le) hn_nn
      · refine mul_le_mul_of_nonneg_left ?_ hBS_nn
        refine Finset.sum_le_sum (fun l hl => ?_)
        have hl_le : l ≤ a + 1 := by
          rw [Finset.mem_range] at hl
          omega
        refine le_trans (hcipL (wOmega (I := I) (M := M) g₀ g₁ g₀) l) ?_
        exact mul_le_mul_of_nonneg_left (hΩ_jets l hl_le) (hcipL_nn l)
  · -- empty manifold: the sup is vacuous and every jet-`L²` norm vanishes
    haveI hEmpty : IsEmpty M := not_nonempty_iff.mp hM
    refine ⟨fun x => (hEmpty.false x).elim, ?_⟩
    intro i hi
    have hzero : ∀ q : ℕ,
        ‖iteratedCovGrad (I := I) g₀ 2 4 q (lc0VBPass (I := I) (M := M) g₀ g₁)‖ ^ 2 = 0 := by
      intro q
      rw [SmoothCcTensor.norm_def,
        tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs]
      exact MeasureTheory.integral_of_isEmpty
    rw [Finset.sum_congr rfl (fun q _ => hzero q), Finset.sum_const, smul_zero]
    exact hF_nn i

set_option linter.unusedVariables false in
/-- **Per-order `ballUniform` jet-`L²` bound for the `lc0VB` piece.**  Via the two-arm
factorization `lc0VB = 2 · appCcRS g₀ 2 4 2 lc0RiemLive lc0VBPass` (`lc0VB_eq_app`): the live arm
`lc0RiemLive` (reused from `lc0Riem`, the moving `g₁`-cometric double trace) is bounded by the
committed cometric double-trace envelope, and the moving passenger `lc0VBPass` by `vbPass_jetL2`;
the product grid + two-arm integrator combine them.  Carries the single `sorry` of `vbPass_jetL2`. -/
private theorem lc0VB_ballUniform
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
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
              (lc0VB (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' s))‖ ^ 2
            ≤ K i := by
  classical
  obtain ⟨Λ, F, hΛ_nn, hF_nn, hcom⟩ :=
    cometricDoubleTraceField_order0sup_jetL2_ballUniform_generic (I := I) (M := M) g₀ a
      ha_super hR hδ₀
  obtain ⟨ΛP, FP, hΛP_nn, hFP_nn, hvb⟩ := vbPass_jetL2 (I := I) (M := M) g₀ a ha_super hR hδ₀
  choose Cint hCint_nn hCint using
    (fun k : ℕ => exists_integrated_iteratedCovGrad_diagonalProductGrid_twoArm_rs_le
      (I := I) (M := M) g₀ 4 2 2 4 k)
  set fr : ℝ := (Module.finrank ℝ E : ℝ) with hfr
  have hfr_nn : (0 : ℝ) ≤ fr := Nat.cast_nonneg _
  refine ⟨fun i => 4 * (appCcGdiag (E := E) i *
    (Cint i * (ΛP * (fr * F i) + fr * Λ ^ 2 * FP i))), fun i => ?_, ?_⟩
  · refine mul_nonneg (by norm_num) (mul_nonneg (appCcGdiag_nonneg (E := E) i)
      (mul_nonneg (hCint_nn i) (add_nonneg
        (mul_nonneg hΛP_nn (mul_nonneg hfr_nn (hF_nn i)))
        (mul_nonneg (mul_nonneg hfr_nn (sq_nonneg Λ)) (hFP_nn i)))))
  intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball i hi s hs
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
        iteratedCovGrad_add, iteratedCovGrad_smul, iteratedCovGrad_smul]
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
  obtain ⟨hvbsup, hvbjet⟩ := hvb (realizedFam (I := I) g₀ T T' hδ hδ' s)
    (convexPerturbation (I := I) g₀ T T' s) hδP_le hδP htie hPball
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
      ((lc0VBPass (I := I) (M := M) g₀
        (realizedFam (I := I) g₀ T T' hδ hδ' s)).toSection x) ≤ Real.sqrt ΛP ^ 2 := by
    intro x
    rw [Real.sq_sqrt hΛP_nn]
    exact hvbsup x
  obtain ⟨hgrid_int, hgrid_bd⟩ := hCint i
    (lc0RiemLive (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' s))
    (lc0VBPass (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' s))
    (Real.sqrt (fr * Λ ^ 2)) (Real.sqrt ΛP)
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) hLsup hPsup
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
  have hnorm : ‖iteratedCovGrad (I := I) g₀ 2 2 i
        (appCcRS (I := I) (M := M) g₀ 2 4 2
          (lc0RiemLive (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' s))
          (lc0VBPass (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' s)))‖ ^ 2 ≤
      appCcGdiag (E := E) i *
        (Cint i * (Real.sqrt ΛP ^ 2 * ∑ m ∈ Finset.range (i + 1),
            ‖iteratedCovGrad (I := I) g₀ 4 2 m
              (lc0RiemLive (I := I) (M := M) g₀
                (realizedFam (I := I) g₀ T T' hδ hδ' s))‖ ^ 2
          + Real.sqrt (fr * Λ ^ 2) ^ 2 * ∑ l ∈ Finset.range (i + 1),
            ‖iteratedCovGrad (I := I) g₀ 2 4 l
              (lc0VBPass (I := I) (M := M) g₀
                (realizedFam (I := I) g₀ T T' hδ hδ' s))‖ ^ 2)) := by
    have key := normSq_le_integral_of_pointwise_fiberNormSq_le_rs (I := I) (M := M) g₀ 2 (2 + i)
      (iteratedCovGrad (I := I) g₀ 2 2 i
        (appCcRS (I := I) (M := M) g₀ 2 4 2
          (lc0RiemLive (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' s))
          (lc0VBPass (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' s))))
      _ (hgrid_int.const_mul (appCcGdiag (E := E) i))
      (fun x => rfns_iteratedCovGrad_appCcRS_diagonalProductGrid_rankLeft_le
        (I := I) (M := M) g₀ i 2 4 2
        (lc0RiemLive (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' s))
        (lc0VBPass (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' s)) x)
    refine le_trans key ?_
    rw [MeasureTheory.integral_const_mul]
    exact mul_le_mul_of_nonneg_left hgrid_bd (appCcGdiag_nonneg (E := E) i)
  -- assemble: ‖∇^i lc0VB‖² = 4·‖∇^i appCcRS‖² ≤ K i
  have hsmul : ‖iteratedCovGrad (I := I) g₀ 2 2 i
        (lc0VB (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' s))‖ ^ 2 =
      4 * ‖iteratedCovGrad (I := I) g₀ 2 2 i
        (appCcRS (I := I) (M := M) g₀ 2 4 2
          (lc0RiemLive (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' s))
          (lc0VBPass (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' s)))‖ ^ 2 := by
    rw [lc0VB_eq_app, iteratedCovGrad_smul, norm_smul, mul_pow]
    norm_num
  rw [hsmul]
  have hΛPsq : Real.sqrt ΛP ^ 2 = ΛP := Real.sq_sqrt hΛP_nn
  have hΛsq : Real.sqrt (fr * Λ ^ 2) ^ 2 = fr * Λ ^ 2 :=
    Real.sq_sqrt (mul_nonneg hfr_nn (sq_nonneg Λ))
  rw [hΛPsq, hΛsq] at hnorm
  have hmid : appCcGdiag (E := E) i *
      (Cint i * (ΛP * ∑ m ∈ Finset.range (i + 1),
          ‖iteratedCovGrad (I := I) g₀ 4 2 m
            (lc0RiemLive (I := I) (M := M) g₀
              (realizedFam (I := I) g₀ T T' hδ hδ' s))‖ ^ 2
        + fr * Λ ^ 2 * ∑ l ∈ Finset.range (i + 1),
          ‖iteratedCovGrad (I := I) g₀ 2 4 l
            (lc0VBPass (I := I) (M := M) g₀
              (realizedFam (I := I) g₀ T T' hδ hδ' s))‖ ^ 2)) ≤
      appCcGdiag (E := E) i * (Cint i * (ΛP * (fr * F i) + fr * Λ ^ 2 * FP i)) := by
    refine mul_le_mul_of_nonneg_left ?_ (appCcGdiag_nonneg (E := E) i)
    refine mul_le_mul_of_nonneg_left ?_ (hCint_nn i)
    have hA := mul_le_mul_of_nonneg_left hLsum hΛP_nn
    have hB := mul_le_mul_of_nonneg_left (hvbjet i hi)
      (mul_nonneg hfr_nn (sq_nonneg Λ))
    linarith [hA, hB]
  refine le_trans (mul_le_mul_of_nonneg_left (le_trans hnorm hmid) (by norm_num : (0:ℝ) ≤ 4)) ?_
  exact le_of_eq (by ring)

set_option linter.unusedVariables false in
/-- **`lc0VB` `Kc` atom.**  Per-order top-separated jet-`L²` bound for the
vector-bundle contraction piece with vanishing top constant (`∇²T`-free: all of it
lands in the `R`-carrying `Kc`).  Proved from `lc0VB_ballUniform` by the trivial
`Ktop = 0` reshape (`K i ≤ K i·(1 + low)`).  Carries the single `sorry` of
`lc0VB_ballUniform` until the interior-product fold engine lands. -/
private theorem lc0VB_realizedFam_perOrder_topSep
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
              (lc0VB (I := I) (M := M) g₀
                (realizedFam (I := I) g₀ T T' hδ hδ' s))‖ ^ 2 ≤
            Ktop * (‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T‖ ^ 2 +
              ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T'‖ ^ 2) +
            Kc i * (1 + ∑ j ∈ Finset.range (i + 3),
              (‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
                ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2)) := by
  obtain ⟨K, hK_nn, hK⟩ := lc0VB_ballUniform (I := I) (M := M) g₀ a ha_super hR hδ₀
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
#print axioms lc0InsertDiff_ballUniform
#print axioms lc0InsertDiff_realizedFam_perOrder_topSep
#print axioms lc0VB_eq_app
#print axioms vbPass_jetL2
#print axioms lc0VB_ballUniform
#print axioms lc0VB_realizedFam_perOrder_topSep

end DifferentialGeometry.Integral.Connection

end
