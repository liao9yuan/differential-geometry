import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.DeTurckLieArm1CoeffL2JetBound
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CurvatureCoefficientDifferenceJetTower
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.SlotPermJet
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.LieCorr0Split

/-!
# Operator-product refold for the mixed zeroth-order Lie correction

This leaf exposes only the exact five-factor operator product used by the
radius-free `lc0AMix` estimate.  It is independent of the unfinished broad
`LieCorr0LowJet` refold file.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Bundle Manifold Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck
open LieCorr0Core

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

/-- A moving cometric trace with a fixed permutation of its input slots. -/
def lc0TraceRF (g₀ g₁ : SmoothRiemannianMetric I M) (p : ℕ)
    (σ : Equiv.Perm (Fin (p + 2))) : SmoothCcTensor g₀ (p + 2) p :=
  reindexCoeffGen (I := I) (M := M) g₀ (p + 2) p
    (pureTrace (I := I) (M := M) g₀ g₁ p) σ

/-- The fibre of `lc0TraceRF` is the trace step in the canonical `lc0AMix` formula. -/
theorem lc0TraceRF_fiber (g₀ g₁ : SmoothRiemannianMetric I M) (p : ℕ)
    (σ : Equiv.Perm (Fin (p + 2))) (x : M) :
    (show Tensor0SSpace (p + 2) I x →L[ℝ] Tensor0SSpace p I x from
      (lc0TraceRF (I := I) (M := M) g₀ g₁ p σ).toSection x) =
      lieCorr0TraceStep (I := I) g₁ p σ x := by
  apply ContinuousLinearMap.ext
  intro D
  rw [show
      ((show Tensor0SSpace (p + 2) I x →L[ℝ] Tensor0SSpace p I x from
        (lc0TraceRF (I := I) (M := M) g₀ g₁ p σ).toSection x) D) =
        reindexCoeffFibGen (I := I) (p + 2) p σ x
          (show Tensor0SSpace (p + 2) I x →L[ℝ] Tensor0SSpace p I x from
            (pureTrace (I := I) (M := M) g₀ g₁ p).toSection x) D from rfl]
  rw [reindexCoeffFibGen_apply (I := I) (p + 2) p σ x _ D,
    pureTrace_toSection (I := I) (M := M) g₀ g₁ p x,
    lieCorr0TraceStep, ContinuousLinearMap.comp_apply]
  congr 1

set_option linter.unusedSectionVars false in
private lemma unitTensor_model (x : M) (m : Fin 0 → E) :
    Tensor0SSpace.toModel (unitTensor (I := I) (M := M) x) m = 1 := by
  rw [unitTensor, Tensor0SSpace.toModel_ofModel]
  rfl

private lemma curry_zero (x : M) (D : Tensor0SSpace 1 I x) (v₀ : E) :
    tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 0 x D v₀ =
      (Tensor0SSpace.toModel D (fun _ : Fin 1 => v₀)) •
        unitTensor (I := I) (M := M) x := by
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro m
  beta_reduce
  have h₁ : Tensor0SSpace.toModel
      (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 0 x D v₀) m =
      Tensor0SSpace.toModel D (Fin.cons v₀ m) :=
    TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M) (n := 0)
      (T := D) (v0 := v₀) (vs := m)
  rw [h₁, Tensor0SSpace.toModel_smul, ContinuousMultilinearMap.smul_apply,
    unitTensor_model (I := I) (M := M) x m, smul_eq_mul, mul_one]
  congr 1
  funext k
  refine Fin.cases ?_ (fun j => j.elim0) k
  rfl

set_option linter.unusedSectionVars false in
private lemma clm_unit_smul (x : M) (s : ℕ)
    (A : Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x) (c : ℝ) :
    A (c • unitTensor (I := I) (M := M) x) =
      c • A (unitTensor (I := I) (M := M) x) := A.map_smul c _

private lemma slotLift_23 (g₀ : SmoothRiemannianMetric I M)
    (K : SmoothCcTensor g₀ 0 3) (x : M) (D : Tensor0SSpace 2 I x) :
    (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 5 I x from
      (slotExtendIter (I := I) (M := M) g₀ 0 3 2 K).toSection x) D =
    tensor0SProdKappaFib (I := I) (p := 2) (q := 3) x
      ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from K.toSection x)
        (unitTensor (I := I) (M := M) x)) D := by
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro m
  beta_reduce
  set κ : Tensor0SSpace 3 I x :=
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from K.toSection x)
      (unitTensor (I := I) (M := M) x) with hκ
  have hLHS : Tensor0SSpace.toModel
      ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 5 I x from
        (slotExtendIter (I := I) (M := M) g₀ 0 3 2 K).toSection x) D) m =
      Tensor0SSpace.toModel D ![m 0, m 1] *
        Tensor0SSpace.toModel κ (fun j : Fin 3 => m (Fin.natAdd 2 j)) := by
    rw [show
        ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 5 I x from
          (slotExtendIter (I := I) (M := M) g₀ 0 3 2 K).toSection x) D) =
          slotExtendFib (I := I) (M := M) g₀ 1 4 x
            (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 4 I x from
              (slotExtendIter (I := I) (M := M) g₀ 0 3 1 K).toSection x) D
          from rfl]
    rw [show m = Fin.cons (m 0) (Fin.tail m) from (Fin.cons_self_tail m).symm]
    rw [slotExtendFib_apply_eval (I := I) (M := M) g₀ 1 4 x _ D
      (m 0) (Fin.tail m)]
    set D₁ : Tensor0SSpace 1 I x :=
      tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x D (m 0) with hD₁
    rw [show
        ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 4 I x from
          (slotExtendIter (I := I) (M := M) g₀ 0 3 1 K).toSection x) D₁) =
          slotExtendFib (I := I) (M := M) g₀ 0 3 x
            (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from K.toSection x) D₁
          from rfl]
    rw [show (Fin.tail m : Fin 4 → E) =
        Fin.cons (m 1) (fun j : Fin 3 => m (Fin.natAdd 2 j)) from by
      funext k
      fin_cases k <;> rfl]
    rw [slotExtendFib_apply_eval (I := I) (M := M) g₀ 0 3 x _ D₁
      (m 1) (fun j : Fin 3 => m (Fin.natAdd 2 j))]
    rw [curry_zero (I := I) (M := M) x D₁ (m 1)]
    rw [clm_unit_smul (I := I) (M := M) x 3 _ _]
    rw [← hκ, Tensor0SSpace.toModel_smul,
      ContinuousMultilinearMap.smul_apply, smul_eq_mul]
    have hD₁val : Tensor0SSpace.toModel D₁ (fun _ : Fin 1 => m 1) =
        Tensor0SSpace.toModel D ![m 0, m 1] := by
      rw [hD₁, TensorMultilinear.tensor0S_curry_apply_eval
        (I := I) (M := M) (n := 1) (T := D) (v0 := m 0)
        (vs := fun _ : Fin 1 => m 1)]
      congr 1
      funext k
      fin_cases k <;> rfl
    rw [hD₁val]
    first
      | rfl
      | (congr 1; first | rfl | (congr 1; funext k; fin_cases k <;> rfl))
  rw [hLHS, tensor0SProdKappaFib_apply (I := I) x κ D,
    Tensor0SSpace.toModel_ofModel,
    Bundle.continuousMultilinearMap.modelProduct_apply]
  congr 1
  all_goals
    first
      | rfl
      | (congr 1; funext k; fin_cases k <;> rfl)

private lemma slotLift_33 (g₀ : SmoothRiemannianMetric I M)
    (K : SmoothCcTensor g₀ 0 3) (x : M) (D : Tensor0SSpace 3 I x) :
    (show Tensor0SSpace 3 I x →L[ℝ] Tensor0SSpace 6 I x from
      (slotExtendIter (I := I) (M := M) g₀ 0 3 3 K).toSection x) D =
    tensor0SProdKappaFib (I := I) (p := 3) (q := 3) x
      ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from K.toSection x)
        (unitTensor (I := I) (M := M) x)) D := by
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro m
  beta_reduce
  set κ : Tensor0SSpace 3 I x :=
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from K.toSection x)
      (unitTensor (I := I) (M := M) x) with hκ
  have hLHS : Tensor0SSpace.toModel
      ((show Tensor0SSpace 3 I x →L[ℝ] Tensor0SSpace 6 I x from
        (slotExtendIter (I := I) (M := M) g₀ 0 3 3 K).toSection x) D) m =
      Tensor0SSpace.toModel D ![m 0, m 1, m 2] *
        Tensor0SSpace.toModel κ (fun j : Fin 3 => m (Fin.natAdd 3 j)) := by
    rw [show
        ((show Tensor0SSpace 3 I x →L[ℝ] Tensor0SSpace 6 I x from
          (slotExtendIter (I := I) (M := M) g₀ 0 3 3 K).toSection x) D) =
          slotExtendFib (I := I) (M := M) g₀ 2 5 x
            (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 5 I x from
              (slotExtendIter (I := I) (M := M) g₀ 0 3 2 K).toSection x) D
          from rfl]
    rw [show m = Fin.cons (m 0) (Fin.tail m) from (Fin.cons_self_tail m).symm]
    rw [slotExtendFib_apply_eval (I := I) (M := M) g₀ 2 5 x _ D
      (m 0) (Fin.tail m)]
    set D₂ : Tensor0SSpace 2 I x :=
      tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 2 x D (m 0) with hD₂
    rw [slotLift_23 (I := I) (M := M) g₀ K x D₂, ← hκ,
      tensor0SProdKappaFib_apply (I := I) x κ D₂,
      Tensor0SSpace.toModel_ofModel,
      Bundle.continuousMultilinearMap.modelProduct_apply]
    have hD₂val : Tensor0SSpace.toModel D₂
        ((Fin.tail m : Fin 5 → E) ∘ Fin.castAdd 3) =
        Tensor0SSpace.toModel D ![m 0, m 1, m 2] := by
      rw [hD₂, TensorMultilinear.tensor0S_curry_apply_eval
        (I := I) (M := M) (n := 2) (T := D) (v0 := m 0)
        (vs := (Fin.tail m : Fin 5 → E) ∘ Fin.castAdd 3)]
      congr 1
      funext k
      fin_cases k <;> rfl
    rw [hD₂val]
    first
      | rfl
      | (congr 2; funext j; fin_cases j <;> rfl)
  rw [hLHS, tensor0SProdKappaFib_apply (I := I) x κ D,
    Tensor0SSpace.toModel_ofModel,
    Bundle.continuousMultilinearMap.modelProduct_apply]
  congr 1
  all_goals
    first
      | rfl
      | (congr 1; funext k; fin_cases k <;> rfl)

private lemma mcd_fiber (g₀ g₁ gB : SmoothRiemannianMetric I M) (x : M) :
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
      (metricConnDiffLoweredCc (I := I) (M := M) g₀ g₁ gB).toSection x)
        (unitTensor (I := I) (M := M) x) =
      metricConnDiffLoweredFib (I := I) g₁ g₁ gB x := by
  rw [show
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
        (metricConnDiffLoweredCc (I := I) (M := M) g₀ g₁ gB).toSection x)
          (unitTensor (I := I) (M := M) x) =
        (MixedSection.eval₀ (F := E) (E := (TangentSpace I : M → Type _)) x).smulRight
          (metricConnDiffLoweredFib (I := I) g₁ g₁ gB x)
          (ContinuousMultilinearMap.constOfIsEmpty ℝ
            (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ)) from rfl]
  rw [ContinuousLinearMap.smulRight_apply, MixedSection.eval₀_apply,
    ContinuousMultilinearMap.constOfIsEmpty_apply, one_smul]

/-- One unsymmetrized half of the nested mixed connection correction. -/
def lc0AMixHalfRF (g₀ g₁ gB : SmoothRiemannianMetric I M)
    (σlast : Equiv.Perm (Fin 4)) : SmoothCcTensor g₀ 2 2 :=
  appCcRS (I := I) (M := M) g₀ 2 4 2
    (lc0TraceRF (I := I) (M := M) g₀ g₁ 2 σlast)
    (appCcRS (I := I) (M := M) g₀ 2 6 4
      (lc0TraceRF (I := I) (M := M) g₀ g₁ 4 lieCorr0AMixPerm1)
      (appCcRS (I := I) (M := M) g₀ 2 3 6
        (slotExtendIter (I := I) (M := M) g₀ 0 3 3
          (metricConnDiffLoweredCc (I := I) (M := M) g₀ g₁ gB))
        (appCcRS (I := I) (M := M) g₀ 2 5 3
          (lc0TraceRF (I := I) (M := M) g₀ g₁ 3 lieCorr0AMixPermQ)
          (slotExtendIter (I := I) (M := M) g₀ 0 3 2
            (metricConnDiffLoweredCc (I := I) (M := M) g₀ g₁ g₀)))))

/-- Input permutation that realizes swapping the two final output slots. -/
def lc0SwapPermRF : Equiv.Perm (Fin 4) :=
  ⟨![0, 1, 3, 2], ![0, 1, 3, 2], by decide, by decide⟩

private lemma swap_trace (g₁ : SmoothRiemannianMetric I M)
    (σ : Equiv.Perm (Fin 4)) (x : M) (Z : Tensor0SSpace 4 I x) :
    domDomCongrFibRank (I := I) 2 (Equiv.swap (0 : Fin 2) 1) x
      (lieCorr0TraceStep (I := I) g₁ 2 σ x Z) =
    lieCorr0TraceStep (I := I) g₁ 2 (lc0SwapPermRF * σ) x Z := by
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro w
  beta_reduce
  rw [domDomCongrFibRank_apply (I := I) 2 (Equiv.swap (0 : Fin 2) 1) x,
    Tensor0SSpace.toModel_ofModel, ContinuousMultilinearMap.domDomCongr_apply]
  rw [show lieCorr0TraceStep (I := I) g₁ 2 σ x Z =
      cometricDoubleTraceFib (I := I) g₁ 2 x
        (domDomCongrFibRank (I := I) 4 σ x Z) from rfl]
  rw [show lieCorr0TraceStep (I := I) g₁ 2 (lc0SwapPermRF * σ) x Z =
      cometricDoubleTraceFib (I := I) g₁ 2 x
        (domDomCongrFibRank (I := I) 4 (lc0SwapPermRF * σ) x Z) from rfl]
  rw [cometricDoubleTraceFib_toModel (I := I) g₁ 2 x,
    cometricDoubleTraceFib_toModel (I := I) g₁ 2 x]
  rw [modelDoubleTrace_apply (E := E) 2 (cometricLmodel (I := I) g₁ x),
    modelDoubleTrace_apply (E := E) 2 (cometricLmodel (I := I) g₁ x)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [domDomCongrFibRank_apply (I := I) 4 σ x Z,
    Tensor0SSpace.toModel_ofModel, ContinuousMultilinearMap.domDomCongr_apply]
  rw [domDomCongrFibRank_apply (I := I) 4 (lc0SwapPermRF * σ) x Z,
    Tensor0SSpace.toModel_ofModel, ContinuousMultilinearMap.domDomCongr_apply]
  congr 1
  funext i
  have hpt : ∀ t : Fin 4,
      (Fin.cons (cometricLmodel (I := I) g₁ x
          (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
            ((Module.finBasis ℝ E).cDualBasis k)))
        (Fin.cons ((Module.finBasis ℝ E) k)
          (fun j : Fin 2 => w ((Equiv.swap (0 : Fin 2) 1) j))) : Fin 4 → E) t =
      (Fin.cons (cometricLmodel (I := I) g₁ x
          (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
            ((Module.finBasis ℝ E).cDualBasis k)))
        (Fin.cons ((Module.finBasis ℝ E) k) w) : Fin 4 → E) (lc0SwapPermRF t) := by
    intro t
    fin_cases t <;> rfl
  rw [hpt (σ i)]
  rfl

/-- Symmetrized operator-product normal form of the mixed connection correction. -/
def lc0AMixFormRF (g₀ g₁ gB : SmoothRiemannianMetric I M) :
    SmoothCcTensor g₀ 2 2 :=
  (2 : ℝ) •
    (lc0AMixHalfRF (I := I) (M := M) g₀ g₁ gB lieCorr0AMixPerm2 +
      lc0AMixHalfRF (I := I) (M := M) g₀ g₁ gB
        (lc0SwapPermRF * lieCorr0AMixPerm2))

private lemma amixHalf_fiber (g₀ g₁ gB : SmoothRiemannianMetric I M)
    (σlast : Equiv.Perm (Fin 4)) (x : M) (D : Tensor0SSpace 2 I x) :
    (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
      (lc0AMixHalfRF (I := I) (M := M) g₀ g₁ gB σlast).toSection x) D =
    lieCorr0TraceStep (I := I) g₁ 2 σlast x
      (lieCorr0TraceStep (I := I) g₁ 4 lieCorr0AMixPerm1 x
        (tensor0SProdKappaFib (I := I) (p := 3) (q := 3) x
          (metricConnDiffLoweredFib (I := I) g₁ g₁ gB x)
          (lieCorr0TraceStep (I := I) g₁ 3 lieCorr0AMixPermQ x
            (tensor0SProdKappaFib (I := I) (p := 2) (q := 3) x
              (metricConnDiffLoweredFib (I := I) g₁ g₁ g₀ x) D)))) := by
  simp only [lc0AMixHalfRF, appCcRS_toSection, ContinuousLinearMap.comp_apply]
  rw [slotLift_23 (I := I) (M := M) g₀
    (metricConnDiffLoweredCc (I := I) (M := M) g₀ g₁ g₀) x D]
  rw [mcd_fiber (I := I) (M := M) g₀ g₁ g₀ x]
  rw [show
      (show Tensor0SSpace 5 I x →L[ℝ] Tensor0SSpace 3 I x from
        (lc0TraceRF (I := I) (M := M) g₀ g₁ 3 lieCorr0AMixPermQ).toSection x)
          (tensor0SProdKappaFib (I := I) (p := 2) (q := 3) x
            (metricConnDiffLoweredFib (I := I) g₁ g₁ g₀ x) D) =
      lieCorr0TraceStep (I := I) g₁ 3 lieCorr0AMixPermQ x
        (tensor0SProdKappaFib (I := I) (p := 2) (q := 3) x
          (metricConnDiffLoweredFib (I := I) g₁ g₁ g₀ x) D) from
    congrFun (congrArg DFunLike.coe
      (lc0TraceRF_fiber (I := I) (M := M) g₀ g₁ 3 lieCorr0AMixPermQ x)) _]
  rw [slotLift_33 (I := I) (M := M) g₀
    (metricConnDiffLoweredCc (I := I) (M := M) g₀ g₁ gB) x _]
  rw [mcd_fiber (I := I) (M := M) g₀ g₁ gB x]
  rw [show
      (show Tensor0SSpace 6 I x →L[ℝ] Tensor0SSpace 4 I x from
        (lc0TraceRF (I := I) (M := M) g₀ g₁ 4 lieCorr0AMixPerm1).toSection x)
          (tensor0SProdKappaFib (I := I) (p := 3) (q := 3) x
            (metricConnDiffLoweredFib (I := I) g₁ g₁ gB x)
            (lieCorr0TraceStep (I := I) g₁ 3 lieCorr0AMixPermQ x
              (tensor0SProdKappaFib (I := I) (p := 2) (q := 3) x
                (metricConnDiffLoweredFib (I := I) g₁ g₁ g₀ x) D))) =
      lieCorr0TraceStep (I := I) g₁ 4 lieCorr0AMixPerm1 x
        (tensor0SProdKappaFib (I := I) (p := 3) (q := 3) x
          (metricConnDiffLoweredFib (I := I) g₁ g₁ gB x)
          (lieCorr0TraceStep (I := I) g₁ 3 lieCorr0AMixPermQ x
            (tensor0SProdKappaFib (I := I) (p := 2) (q := 3) x
              (metricConnDiffLoweredFib (I := I) g₁ g₁ g₀ x) D))) from
    congrFun (congrArg DFunLike.coe
      (lc0TraceRF_fiber (I := I) (M := M) g₀ g₁ 4 lieCorr0AMixPerm1 x)) _]
  exact congrFun (congrArg DFunLike.coe
    (lc0TraceRF_fiber (I := I) (M := M) g₀ g₁ 2 σlast x)) _

private lemma amixForm_fiber (g₀ g₁ gB : SmoothRiemannianMetric I M) (x : M)
    (D : Tensor0SSpace 2 I x) :
    (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
      (lc0AMixFormRF (I := I) (M := M) g₀ g₁ gB).toSection x) D =
      lieCorr0AMixFib (I := I) g₀ g₁ gB x D := by
  have h₁ :
      (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        (lc0AMixFormRF (I := I) (M := M) g₀ g₁ gB).toSection x) D =
      (2 : ℝ) •
        ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
          (lc0AMixHalfRF (I := I) (M := M) g₀ g₁ gB
            lieCorr0AMixPerm2).toSection x) D +
        (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
          (lc0AMixHalfRF (I := I) (M := M) g₀ g₁ gB
            (lc0SwapPermRF * lieCorr0AMixPerm2)).toSection x) D) := rfl
  rw [h₁]
  rw [amixHalf_fiber (I := I) (M := M) g₀ g₁ gB lieCorr0AMixPerm2 x D]
  rw [amixHalf_fiber (I := I) (M := M) g₀ g₁ gB
    (lc0SwapPermRF * lieCorr0AMixPerm2) x D]
  rw [← swap_trace (I := I) (M := M) g₁ lieCorr0AMixPerm2 x _]
  rw [show lieCorr0AMixFib (I := I) g₀ g₁ gB x D =
      (2 : ℝ) • (lieCorr0AMixHalfFib (I := I) g₀ g₁ gB x D +
        domDomCongrFibRank (I := I) 2 (Equiv.swap 0 1) x
          (lieCorr0AMixHalfFib (I := I) g₀ g₁ gB x D)) from by
    rw [lieCorr0AMixFib, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply]]
  rfl

/-- The canonical mixed zeroth-order Lie correction equals its five-factor product form. -/
theorem amix_refold_rf (g₀ g₁ gB : SmoothRiemannianMetric I M) :
    lc0AMix (I := I) (M := M) g₀ g₁ gB =
      lc0AMixFormRF (I := I) (M := M) g₀ g₁ gB := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro D
  change lieCorr0AMixFib (I := I) g₀ g₁ gB x D = _
  exact (amixForm_fiber (I := I) (M := M) g₀ g₁ gB x D).symm

/-! ## Fixed-background difference -/

/-- The lowered connection-difference factor that remains after changing only
the fixed DeTurck background. -/
def lc0BgKappaRF (g₀ g₁ gB : SmoothRiemannianMetric I M) :
    SmoothCcTensor g₀ 0 3 :=
  metricConnDiffLoweredCc (I := I) (M := M) g₀ g₁ gB -
    metricConnDiffLoweredCc (I := I) (M := M) g₀ g₁ g₀

/-- One unsymmetrized half of the mixed correction after the fixed-background
difference has been moved into its lowered connection factor. -/
def lc0AMixBgHalfRF (g₀ g₁ gB : SmoothRiemannianMetric I M)
    (σ : Equiv.Perm (Fin 4)) : SmoothCcTensor g₀ 2 2 :=
  appCcRS (I := I) (M := M) g₀ 2 4 2
    (lc0TraceRF (I := I) (M := M) g₀ g₁ 2 σ)
    (appCcRS (I := I) (M := M) g₀ 2 6 4
      (lc0TraceRF (I := I) (M := M) g₀ g₁ 4 lieCorr0AMixPerm1)
      (appCcRS (I := I) (M := M) g₀ 2 3 6
        (slotExtendIter (I := I) (M := M) g₀ 0 3 3
          (lc0BgKappaRF (I := I) (M := M) g₀ g₁ gB))
        (appCcRS (I := I) (M := M) g₀ 2 5 3
          (lc0TraceRF (I := I) (M := M) g₀ g₁ 3 lieCorr0AMixPermQ)
          (slotExtendIter (I := I) (M := M) g₀ 0 3 2
            (metricConnDiffLoweredCc (I := I) (M := M) g₀ g₁ g₀)))))

/-- Changing the fixed background in one mixed half changes only its first
lowered connection factor. -/
theorem amix_half_bg_rf
    (g₀ g₁ gB : SmoothRiemannianMetric I M)
    (σ : Equiv.Perm (Fin 4)) :
    lc0AMixHalfRF (I := I) (M := M) g₀ g₁ gB σ -
        lc0AMixHalfRF (I := I) (M := M) g₀ g₁ g₀ σ =
      lc0AMixBgHalfRF (I := I) (M := M) g₀ g₁ gB σ := by
  unfold lc0AMixHalfRF lc0AMixBgHalfRF lc0BgKappaRF
  rw [← appCcRS_sub_right, ← appCcRS_sub_right,
    ← appCcRS_sub_left, ← slotIterSub]

/-- Exact fixed-background-difference factorization of the mixed zeroth-order
Lie correction. -/
theorem amix_bg_refold_rf
    (g₀ g₁ gB : SmoothRiemannianMetric I M) :
    lc0AMix (I := I) (M := M) g₀ g₁ gB -
        lc0AMix (I := I) (M := M) g₀ g₁ g₀ =
      (2 : ℝ) •
        (lc0AMixBgHalfRF (I := I) (M := M) g₀ g₁ gB lieCorr0AMixPerm2 +
          lc0AMixBgHalfRF (I := I) (M := M) g₀ g₁ gB
            (lc0SwapPermRF * lieCorr0AMixPerm2)) := by
  rw [amix_refold_rf (I := I) (M := M) g₀ g₁ gB,
    amix_refold_rf (I := I) (M := M) g₀ g₁ g₀]
  have h0 := amix_half_bg_rf (I := I) (M := M) g₀ g₁ gB lieCorr0AMixPerm2
  have h1 := amix_half_bg_rf (I := I) (M := M) g₀ g₁ gB
    (lc0SwapPermRF * lieCorr0AMixPerm2)
  simp only [lc0AMixFormRF]
  rw [show
      (2 : ℝ) •
          (lc0AMixHalfRF (I := I) (M := M) g₀ g₁ gB lieCorr0AMixPerm2 +
            lc0AMixHalfRF (I := I) (M := M) g₀ g₁ gB
              (lc0SwapPermRF * lieCorr0AMixPerm2)) -
        (2 : ℝ) •
          (lc0AMixHalfRF (I := I) (M := M) g₀ g₁ g₀ lieCorr0AMixPerm2 +
            lc0AMixHalfRF (I := I) (M := M) g₀ g₁ g₀
              (lc0SwapPermRF * lieCorr0AMixPerm2)) =
        (2 : ℝ) •
          ((lc0AMixHalfRF (I := I) (M := M) g₀ g₁ gB lieCorr0AMixPerm2 -
              lc0AMixHalfRF (I := I) (M := M) g₀ g₁ g₀ lieCorr0AMixPerm2) +
            (lc0AMixHalfRF (I := I) (M := M) g₀ g₁ gB
                (lc0SwapPermRF * lieCorr0AMixPerm2) -
              lc0AMixHalfRF (I := I) (M := M) g₀ g₁ g₀
                (lc0SwapPermRF * lieCorr0AMixPerm2))) by module,
    h0, h1]

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral
