import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.PrincipalLowRegCore
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.DeTurckVFEndoInsertTopSep
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderLowBaseAction
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderLowBaseA2
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckPrincipalCoeffIdentity

/-!
# Low-base second-order coefficient Lipschitz estimates

This module supplies the two-endpoint low-regularity estimates needed to
compare the canonical second-order coefficient in the intrinsic
Ricci--DeTurck remainder split.  The first brick identifies the geometric
moving-inverse insertion with the completed Neumann correction and transfers
the resolvent Lipschitz estimate back to smooth coefficient actions.
-/

noncomputable section

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert
open DifferentialGeometry.PDE.DeTurck.RicciLinearization
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E :=
  FiniteDimensional.complete ℝ E

set_option linter.unusedSectionVars false in
private theorem cc_toFun_ext
    (g : SmoothRiemannianMetric I M) {r s : ℕ}
    (A B : SmoothCcTensor g r s)
    (h : A.toFun = B.toFun) :
    A = B := by
  rcases A with ⟨⟨a, ha⟩, hA⟩
  rcases B with ⟨⟨b, hb⟩, hB⟩
  have hab : a = b := by
    funext x
    apply TensorRSSpace.toModel_injective
    exact congrFun h x
  subst b
  rfl

private noncomputable def fullSlot2
    (g gm : SmoothRiemannianMetric I M) : SmoothCcTensor g 2 2 :=
  slotInsertEndoCc (I := I) (M := M) g 1
    (fullRaisedEndoField (I := I) (M := M) g gm)

private noncomputable def perturbSlot2
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2) :
    SmoothCcTensor g 2 2 :=
  slotInsertEndoCc (I := I) (M := M) g 1
    (symmRaiseEndo (I := I) (M := M) g T)

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
private theorem insertSucc_eq_c2
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (Λ : ContMDiffSection I (E →L[ℝ] E) ∞
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)) :
    slotInsertEndoCc (I := I) (M := M) g (s + 1) Λ =
      reindexCoeffGen (I := I) (M := M) g (s + 2) (s + 2)
        (rsDomDomCongrSection (I := I) (M := M) g (s + 2) (s + 2)
          (Equiv.swap (0 : Fin (s + 2)) 1)
          (slotExtend (I := I) (M := M) g (s + 1) (s + 1)
            (slotInsertEndoCc (I := I) (M := M) g s Λ)))
        (Equiv.swap (0 : Fin (s + 2)) 1) := by
  classical
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro D
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro m
  change Tensor0SSpace.toModel
      ((show Tensor0SSpace (s + 2) I x →L[ℝ] Tensor0SSpace (s + 2) I x from
        (slotInsertEndoCc (I := I) (M := M) g (s + 1) Λ).toSection x) D) m =
    Tensor0SSpace.toModel
      ((show Tensor0SSpace (s + 2) I x →L[ℝ] Tensor0SSpace (s + 2) I x from
        (reindexCoeffGen (I := I) (M := M) g (s + 2) (s + 2)
          (rsDomDomCongrSection (I := I) (M := M) g (s + 2) (s + 2)
            (Equiv.swap (0 : Fin (s + 2)) 1)
            (slotExtend (I := I) (M := M) g (s + 1) (s + 1)
              (slotInsertEndoCc (I := I) (M := M) g s Λ)))
          (Equiv.swap (0 : Fin (s + 2)) 1)).toSection x) D) m
  rw [slotInsertEndoCc_toSection, slotInsertEndoFib_apply_eval]
  rw [reindexCoeffGen_toSection, reindexCoeffFibGen_apply,
    rsDomDomCongrSection_toSection, toModel_rsDomDomCongr_apply,
    ContinuousMultilinearMap.domDomCongr_apply, slotExtend_toSection]
  rw [show (fun k : Fin (s + 2) =>
      m ((Equiv.swap (0 : Fin (s + 2)) 1) k)) =
    Fin.cons (m 1) (fun j : Fin (s + 1) =>
      m ((Equiv.swap (0 : Fin (s + 2)) 1) (Fin.succ j))) from by
        funext k
        refine Fin.cases ?_ (fun j => ?_) k
        · simp only [Fin.cons_zero, Equiv.swap_apply_left]
        · simp only [Fin.cons_succ]]
  rw [slotExtendFib_apply_eval]
  rw [slotInsertEndoCc_toSection, slotInsertEndoFib_apply_eval,
    TensorMultilinear.tensor0S_curry_apply_eval,
    Tensor0SSpace.toModel_ofModel,
    ContinuousMultilinearMap.domDomCongr_apply]
  have hswap :
      (Equiv.swap (0 : Fin (s + 2)) 1) (Fin.succ (0 : Fin (s + 1))) = 0 := by
    rw [show (Fin.succ (0 : Fin (s + 1)) : Fin (s + 2)) = 1 from rfl,
      Equiv.swap_apply_right]
  rw [hswap]
  congr 1
  funext k
  refine Fin.cases ?_ (fun k₁ => ?_) k
  · rw [Equiv.swap_apply_left,
      show (1 : Fin (s + 2)) = Fin.succ (0 : Fin (s + 1)) from rfl,
      Fin.cons_succ, Function.update_self, Function.update_self]
  · refine Fin.cases ?_ (fun k₂ => ?_) k₁
    · have h10 : (1 : Fin (s + 2)) ≠ 0 := by
        rw [show (1 : Fin (s + 2)) =
          Fin.succ (0 : Fin (s + 1)) from rfl]
        exact Fin.succ_ne_zero _
      rw [show (Fin.succ (0 : Fin (s + 1)) : Fin (s + 2)) = 1 from rfl,
        Function.update_of_ne h10, Equiv.swap_apply_right, Fin.cons_zero]
    · have hne0 : (Fin.succ (Fin.succ k₂) : Fin (s + 2)) ≠ 0 :=
        Fin.succ_ne_zero _
      have hne1 : (Fin.succ (Fin.succ k₂) : Fin (s + 2)) ≠ 1 := by
        rw [show (1 : Fin (s + 2)) =
          Fin.succ (0 : Fin (s + 1)) from rfl]
        exact fun h => Fin.succ_ne_zero _ (Fin.succ_injective _ h)
      rw [Function.update_of_ne hne0,
        Equiv.swap_apply_of_ne_of_ne hne0 hne1, Fin.cons_succ,
        Function.update_of_ne (Fin.succ_ne_zero k₂)]
      change m (Fin.succ (Fin.succ k₂)) =
        m ((Equiv.swap (0 : Fin (s + 2)) 1)
          (Fin.succ (Fin.succ k₂)))
      rw [Equiv.swap_apply_of_ne_of_ne hne0 hne1]

set_option linter.unusedSectionVars false in
private theorem insertSucc_icg_sq
    (g : SmoothRiemannianMetric I M) (s i : ℕ)
    (Λ : ContMDiffSection I (E →L[ℝ] E) ∞
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)) :
    ‖iteratedCovGrad (I := I) g (s + 2) (s + 2) i
        (slotInsertEndoCc (I := I) (M := M) g (s + 1) Λ)‖ ^ 2 ≤
      (Module.finrank ℝ E : ℝ) *
        ‖iteratedCovGrad (I := I) g (s + 1) (s + 1) i
          (slotInsertEndoCc (I := I) (M := M) g s Λ)‖ ^ 2 := by
  let F : M → ℝ := fun x =>
    (Module.finrank ℝ E : ℝ) *
      riemannianFiberNormSq (I := I) (M := M) g
        (s + 1) ((s + 1) + i) x
        ((iteratedCovGrad (I := I) g (s + 1) (s + 1) i
          (slotInsertEndoCc (I := I) (M := M) g s Λ)).toSection x)
  have hF : MeasureTheory.Integrable F
      (riemannianVolumeMeasure (I := I) (M := M) g) := by
    dsimp only [F]
    exact (integrable_riemannianFiberNormSq_toSection
      (I := I) (M := M) g (s + 1) ((s + 1) + i)
      (iteratedCovGrad (I := I) g (s + 1) (s + 1) i
        (slotInsertEndoCc (I := I) (M := M) g s Λ))).const_mul _
  have hpt : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g
          (s + 2) ((s + 2) + i) x
          ((iteratedCovGrad (I := I) g (s + 2) (s + 2) i
            (slotInsertEndoCc (I := I) (M := M) g (s + 1) Λ)).toSection x) ≤
        F x := by
    intro x
    have heq :
        riemannianFiberNormSq (I := I) (M := M) g
            (s + 2) ((s + 2) + i) x
            ((iteratedCovGrad (I := I) g (s + 2) (s + 2) i
              (slotInsertEndoCc (I := I) (M := M) g
                (s + 1) Λ)).toSection x) =
          riemannianFiberNormSq (I := I) (M := M) g
            (s + 2) ((s + 2) + i) x
            ((iteratedCovGrad (I := I) g (s + 2) (s + 2) i
              (slotExtend (I := I) (M := M) g (s + 1) (s + 1)
                (slotInsertEndoCc (I := I) (M := M) g s Λ))).toSection x) := by
      rw [insertSucc_eq_c2 (I := I) (M := M) g s Λ]
      simpa only [Nat.add_assoc] using
        rfns_iteratedCovGrad_rsDomDomCongr_both_eq
          (I := I) (M := M) g (s + 2) (s + 2)
          (Equiv.swap (0 : Fin (s + 2)) 1)
          (Equiv.swap (0 : Fin (s + 2)) 1)
          (slotExtend (I := I) (M := M) g (s + 1) (s + 1)
            (slotInsertEndoCc (I := I) (M := M) g s Λ)) i x
    rw [heq]
    simpa only [F, Nat.add_assoc] using
      rfns_iteratedCovGrad_slotExtend_le
        (I := I) (M := M) g (s + 1) (s + 1)
        (slotInsertEndoCc (I := I) (M := M) g s Λ) i x
  have hsq := normSq_le_integral_of_pointwise_fiberNormSq_le_rs
    (I := I) (M := M) g (s + 2) ((s + 2) + i)
    (iteratedCovGrad (I := I) g (s + 2) (s + 2) i
      (slotInsertEndoCc (I := I) (M := M) g (s + 1) Λ))
    F hF hpt
  have hint :
      ∫ x, riemannianFiberNormSq (I := I) (M := M) g
          (s + 1) ((s + 1) + i) x
          ((iteratedCovGrad (I := I) g (s + 1) (s + 1) i
            (slotInsertEndoCc (I := I) (M := M) g s Λ)).toSection x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
      ‖iteratedCovGrad (I := I) g (s + 1) (s + 1) i
        (slotInsertEndoCc (I := I) (M := M) g s Λ)‖ ^ 2 := by
    rw [SmoothCcTensor.norm_def,
      tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs
        (I := I) (M := M) g (s + 1) ((s + 1) + i)]
  dsimp only [F] at hsq
  rw [MeasureTheory.integral_const_mul, hint] at hsq
  exact hsq

private noncomputable def c2JetSq
    (g : SmoothRiemannianMetric I M) {r s : ℕ}
    (A : SmoothCcTensor g r s) : ℝ :=
  ∑ j ∈ Finset.range 3,
    ‖iteratedCovGrad (I := I) g r s j A‖ ^ 2

private theorem insertSucc_jet_c2
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (Λ : ContMDiffSection I (E →L[ℝ] E) ∞
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)) :
    c2JetSq (I := I) (M := M) g
        (slotInsertEndoCc (I := I) (M := M) g (s + 1) Λ) ≤
      (Module.finrank ℝ E : ℝ) *
        c2JetSq (I := I) (M := M) g
          (slotInsertEndoCc (I := I) (M := M) g s Λ) := by
  unfold c2JetSq
  calc
    (∑ j ∈ Finset.range 3,
        ‖iteratedCovGrad (I := I) g (s + 2) (s + 2) j
          (slotInsertEndoCc (I := I) (M := M) g (s + 1) Λ)‖ ^ 2) ≤
      ∑ j ∈ Finset.range 3, (Module.finrank ℝ E : ℝ) *
        ‖iteratedCovGrad (I := I) g (s + 1) (s + 1) j
          (slotInsertEndoCc (I := I) (M := M) g s Λ)‖ ^ 2 := by
        exact Finset.sum_le_sum fun j _ =>
          insertSucc_icg_sq (I := I) (M := M) g s j Λ
    _ = (Module.finrank ℝ E : ℝ) *
        ∑ j ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g (s + 1) (s + 1) j
            (slotInsertEndoCc (I := I) (M := M) g s Λ)‖ ^ 2 := by
      rw [Finset.mul_sum]

private theorem insert3_jet_c2
    (g : SmoothRiemannianMetric I M)
    (Λ : ContMDiffSection I (E →L[ℝ] E) ∞
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)) :
    c2JetSq (I := I) (M := M) g
        (slotInsertEndoCc (I := I) (M := M) g 3 Λ) ≤
      (Module.finrank ℝ E : ℝ) ^ 2 *
        c2JetSq (I := I) (M := M) g
          (slotInsertEndoCc (I := I) (M := M) g 1 Λ) := by
  have hfr : (0 : ℝ) ≤ Module.finrank ℝ E := Nat.cast_nonneg _
  calc
    c2JetSq (I := I) (M := M) g
        (slotInsertEndoCc (I := I) (M := M) g 3 Λ) ≤
      (Module.finrank ℝ E : ℝ) *
        c2JetSq (I := I) (M := M) g
          (slotInsertEndoCc (I := I) (M := M) g 2 Λ) :=
      insertSucc_jet_c2 (I := I) (M := M) g 2 Λ
    _ ≤ (Module.finrank ℝ E : ℝ) *
        ((Module.finrank ℝ E : ℝ) *
          c2JetSq (I := I) (M := M) g
            (slotInsertEndoCc (I := I) (M := M) g 1 Λ)) :=
      mul_le_mul_of_nonneg_left
        (insertSucc_jet_c2 (I := I) (M := M) g 1 Λ) hfr
    _ = (Module.finrank ℝ E : ℝ) ^ 2 *
        c2JetSq (I := I) (M := M) g
          (slotInsertEndoCc (I := I) (M := M) g 1 Λ) := by ring

private theorem insert5_jet_c2
    (g : SmoothRiemannianMetric I M)
    (Λ : ContMDiffSection I (E →L[ℝ] E) ∞
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)) :
    c2JetSq (I := I) (M := M) g
        (slotInsertEndoCc (I := I) (M := M) g 5 Λ) ≤
      (Module.finrank ℝ E : ℝ) ^ 4 *
        c2JetSq (I := I) (M := M) g
          (slotInsertEndoCc (I := I) (M := M) g 1 Λ) := by
  have hfr : (0 : ℝ) ≤ Module.finrank ℝ E := Nat.cast_nonneg _
  calc
    c2JetSq (I := I) (M := M) g
        (slotInsertEndoCc (I := I) (M := M) g 5 Λ) ≤
      (Module.finrank ℝ E : ℝ) *
        c2JetSq (I := I) (M := M) g
          (slotInsertEndoCc (I := I) (M := M) g 4 Λ) :=
      insertSucc_jet_c2 (I := I) (M := M) g 4 Λ
    _ ≤ (Module.finrank ℝ E : ℝ) *
        ((Module.finrank ℝ E : ℝ) *
          c2JetSq (I := I) (M := M) g
            (slotInsertEndoCc (I := I) (M := M) g 3 Λ)) :=
      mul_le_mul_of_nonneg_left
        (insertSucc_jet_c2 (I := I) (M := M) g 3 Λ) hfr
    _ = (Module.finrank ℝ E : ℝ) ^ 2 *
        c2JetSq (I := I) (M := M) g
          (slotInsertEndoCc (I := I) (M := M) g 3 Λ) := by ring
    _ ≤ (Module.finrank ℝ E : ℝ) ^ 2 *
        ((Module.finrank ℝ E : ℝ) ^ 2 *
          c2JetSq (I := I) (M := M) g
            (slotInsertEndoCc (I := I) (M := M) g 1 Λ)) := by
      exact mul_le_mul_of_nonneg_left
        (insert3_jet_c2 (I := I) (M := M) g Λ)
        (sq_nonneg _)
    _ = (Module.finrank ℝ E : ℝ) ^ 4 *
        c2JetSq (I := I) (M := M) g
          (slotInsertEndoCc (I := I) (M := M) g 1 Λ) := by ring

set_option linter.unusedSectionVars false in
private theorem slot_icg_sq_c2
    (g : SmoothRiemannianMetric I M) (r s i : ℕ)
    (A : SmoothCcTensor g r s) :
    ‖iteratedCovGrad (I := I) g (r + 1) (s + 1) i
        (slotExtend (I := I) (M := M) g r s A)‖ ^ 2 ≤
      (Module.finrank ℝ E : ℝ) *
        ‖iteratedCovGrad (I := I) g r s i A‖ ^ 2 := by
  let F : M → ℝ := fun x =>
    (Module.finrank ℝ E : ℝ) *
      riemannianFiberNormSq (I := I) (M := M) g r (s + i) x
        ((iteratedCovGrad (I := I) g r s i A).toSection x)
  have hF : MeasureTheory.Integrable F
      (riemannianVolumeMeasure (I := I) (M := M) g) := by
    dsimp only [F]
    exact (integrable_riemannianFiberNormSq_toSection
      (I := I) (M := M) g r (s + i)
      (iteratedCovGrad (I := I) g r s i A)).const_mul _
  have hpt : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g
          (r + 1) ((s + 1) + i) x
          ((iteratedCovGrad (I := I) g (r + 1) (s + 1) i
            (slotExtend (I := I) (M := M) g r s A)).toSection x) ≤
        F x := by
    intro x
    simpa only [F, Nat.add_assoc] using
      rfns_iteratedCovGrad_slotExtend_le
        (I := I) (M := M) g r s A i x
  have hsq := normSq_le_integral_of_pointwise_fiberNormSq_le_rs
    (I := I) (M := M) g (r + 1) ((s + 1) + i)
    (iteratedCovGrad (I := I) g (r + 1) (s + 1) i
      (slotExtend (I := I) (M := M) g r s A))
    F hF hpt
  have hint :
      ∫ x, riemannianFiberNormSq (I := I) (M := M) g
          r (s + i) x
          ((iteratedCovGrad (I := I) g r s i A).toSection x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
      ‖iteratedCovGrad (I := I) g r s i A‖ ^ 2 := by
    rw [SmoothCcTensor.norm_def,
      tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs
        (I := I) (M := M) g r (s + i)]
  dsimp only [F] at hsq
  rw [MeasureTheory.integral_const_mul, hint] at hsq
  exact hsq

private theorem slot_jet_c2
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (A : SmoothCcTensor g r s) :
    c2JetSq (I := I) (M := M) g
        (slotExtend (I := I) (M := M) g r s A) ≤
      (Module.finrank ℝ E : ℝ) *
        c2JetSq (I := I) (M := M) g A := by
  unfold c2JetSq
  calc
    (∑ j ∈ Finset.range 3,
        ‖iteratedCovGrad (I := I) g (r + 1) (s + 1) j
          (slotExtend (I := I) (M := M) g r s A)‖ ^ 2) ≤
      ∑ j ∈ Finset.range 3, (Module.finrank ℝ E : ℝ) *
        ‖iteratedCovGrad (I := I) g r s j A‖ ^ 2 := by
      exact Finset.sum_le_sum fun j _ =>
        slot_icg_sq_c2 (I := I) (M := M) g r s j A
    _ = (Module.finrank ℝ E : ℝ) *
        ∑ j ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g r s j A‖ ^ 2 := by
      rw [Finset.mul_sum]

private theorem slot4_jet_c2
    (g : SmoothRiemannianMetric I M)
    (A : SmoothCcTensor g 0 2) :
    c2JetSq (I := I) (M := M) g
        (slotExtendIter (I := I) (M := M) g 0 2 4 A) ≤
      (Module.finrank ℝ E : ℝ) ^ 4 *
        c2JetSq (I := I) (M := M) g A := by
  change c2JetSq (I := I) (M := M) g
      (slotExtend (I := I) (M := M) g 3 5
        (slotExtend (I := I) (M := M) g 2 4
          (slotExtend (I := I) (M := M) g 1 3
            (slotExtend (I := I) (M := M) g 0 2 A)))) ≤ _
  have hfr : (0 : ℝ) ≤ Module.finrank ℝ E := Nat.cast_nonneg _
  calc
    _ ≤ (Module.finrank ℝ E : ℝ) *
        c2JetSq (I := I) (M := M) g
          (slotExtend (I := I) (M := M) g 2 4
            (slotExtend (I := I) (M := M) g 1 3
              (slotExtend (I := I) (M := M) g 0 2 A))) :=
      slot_jet_c2 (I := I) (M := M) g 3 5 _
    _ ≤ (Module.finrank ℝ E : ℝ) *
        ((Module.finrank ℝ E : ℝ) *
          c2JetSq (I := I) (M := M) g
            (slotExtend (I := I) (M := M) g 1 3
              (slotExtend (I := I) (M := M) g 0 2 A))) :=
      mul_le_mul_of_nonneg_left
        (slot_jet_c2 (I := I) (M := M) g 2 4 _) hfr
    _ ≤ (Module.finrank ℝ E : ℝ) *
        ((Module.finrank ℝ E : ℝ) *
          ((Module.finrank ℝ E : ℝ) *
            c2JetSq (I := I) (M := M) g
              (slotExtend (I := I) (M := M) g 0 2 A))) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left
          (slot_jet_c2 (I := I) (M := M) g 1 3 _) hfr) hfr
    _ ≤ (Module.finrank ℝ E : ℝ) *
        ((Module.finrank ℝ E : ℝ) *
          ((Module.finrank ℝ E : ℝ) *
            ((Module.finrank ℝ E : ℝ) *
              c2JetSq (I := I) (M := M) g A))) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left
            (slot_jet_c2 (I := I) (M := M) g 0 2 A) hfr) hfr) hfr
    _ = (Module.finrank ℝ E : ℝ) ^ 4 *
        c2JetSq (I := I) (M := M) g A := by ring

private theorem rsperm_sq_c2
    (g : SmoothRiemannianMetric I M) {r s : ℕ}
    (σ : Equiv.Perm (Fin s)) (A : SmoothCcTensor g r s) (i : ℕ) :
    ‖iteratedCovGrad (I := I) g r s i
        (rsDomDomCongrSection (I := I) (M := M) g r s σ A)‖ ^ 2 =
      ‖iteratedCovGrad (I := I) g r s i A‖ ^ 2 := by
  rw [SmoothCcTensor.norm_def,
    tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs,
    SmoothCcTensor.norm_def,
    tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs]
  refine MeasureTheory.integral_congr_ae
    (Filter.Eventually.of_forall fun x => ?_)
  exact rfns_iteratedCovGrad_rs_eq_of_section_domDomCongr
    (I := I) (M := M) g r s σ A
      (rsDomDomCongrSection (I := I) (M := M) g r s σ A)
      (fun y d => by
        rw [rsDomDomCongrSection_toSection,
          toModel_rsDomDomCongr_apply]) i x

private theorem rsperm_jet_c2
    (g : SmoothRiemannianMetric I M) {r s : ℕ}
    (σ : Equiv.Perm (Fin s)) (A : SmoothCcTensor g r s) :
    c2JetSq (I := I) (M := M) g
        (rsDomDomCongrSection (I := I) (M := M) g r s σ A) =
      c2JetSq (I := I) (M := M) g A := by
  unfold c2JetSq
  apply Finset.sum_congr rfl
  intro i _
  exact rsperm_sq_c2 (I := I) (M := M) g σ A i

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
private theorem rsperm_sub_c2
    (g : SmoothRiemannianMetric I M) {r s : ℕ}
    (σ : Equiv.Perm (Fin s)) (A B : SmoothCcTensor g r s) :
    rsDomDomCongrSection (I := I) (M := M) g r s σ (A - B) =
      rsDomDomCongrSection (I := I) (M := M) g r s σ A -
        rsDomDomCongrSection (I := I) (M := M) g r s σ B := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro D
  apply Tensor0SSpace.toModel_injective
  refine ContinuousMultilinearMap.ext (fun m => ?_)
  have hsub : ((A - B).toSection x) = A.toSection x - B.toSection x := by
    rw [SmoothCcTensor.toSection_sub]
    rfl
  have hsub₂ :
      ((rsDomDomCongrSection (I := I) (M := M) g r s σ A -
          rsDomDomCongrSection (I := I) (M := M) g r s σ B).toSection x) =
        (rsDomDomCongrSection (I := I) (M := M) g r s σ A).toSection x -
          (rsDomDomCongrSection (I := I) (M := M) g r s σ B).toSection x := by
    rw [SmoothCcTensor.toSection_sub]
    rfl
  rw [rsDomDomCongrSection_toSection, hsub, hsub₂]
  rw [rsDomDomCongrSection_toSection, rsDomDomCongrSection_toSection]
  have hfib : ∀ (Y : Tensor0SSpace s I x)
      (w : Fin s → TangentSpace I x),
      Tensor0SSpace.toModel Y w = (Y : Tensor0SSpace s I x) w :=
    fun _ _ => rfl
  rw [hfib, hfib]
  rw [rsDomDomCongr_apply_eval (I := I) (M := M) σ
    (A.toSection x - B.toSection x) D m]
  rw [show ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from
      rsDomDomCongr σ (A.toSection x) -
        rsDomDomCongr σ (B.toSection x)) D) =
      (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from
        rsDomDomCongr σ (A.toSection x)) D -
      (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from
        rsDomDomCongr σ (B.toSection x)) D from rfl]
  rw [show ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from
      (A.toSection x - B.toSection x : TensorRSSpace r s I x)) D) =
      (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from
        A.toSection x) D -
      (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from
        B.toSection x) D from rfl]
  rw [show ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from
      rsDomDomCongr σ (A.toSection x)) D -
        (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from
          rsDomDomCongr σ (B.toSection x)) D : Tensor0SSpace s I x) m =
      ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from
        rsDomDomCongr σ (A.toSection x)) D : Tensor0SSpace s I x) m -
      ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from
        rsDomDomCongr σ (B.toSection x)) D : Tensor0SSpace s I x) m from rfl]
  rw [rsDomDomCongr_apply_eval (I := I) (M := M) σ (A.toSection x) D m]
  rw [rsDomDomCongr_apply_eval (I := I) (M := M) σ (B.toSection x) D m]
  rfl

private theorem slot4_sub_c2
    (g : SmoothRiemannianMetric I M)
    (A B : SmoothCcTensor g 0 2) :
    slotExtendIter (I := I) (M := M) g 0 2 4 (A - B) =
      slotExtendIter (I := I) (M := M) g 0 2 4 A -
        slotExtendIter (I := I) (M := M) g 0 2 4 B := by
  change
    slotExtend (I := I) (M := M) g 3 5
        (slotExtend (I := I) (M := M) g 2 4
          (slotExtend (I := I) (M := M) g 1 3
            (slotExtend (I := I) (M := M) g 0 2 (A - B)))) =
      slotExtend (I := I) (M := M) g 3 5
          (slotExtend (I := I) (M := M) g 2 4
            (slotExtend (I := I) (M := M) g 1 3
              (slotExtend (I := I) (M := M) g 0 2 A))) -
        slotExtend (I := I) (M := M) g 3 5
          (slotExtend (I := I) (M := M) g 2 4
            (slotExtend (I := I) (M := M) g 1 3
              (slotExtend (I := I) (M := M) g 0 2 B)))
  rw [slotExtend_sub, slotExtend_sub, slotExtend_sub, slotExtend_sub]

private noncomputable def monoExtC2
    (g : SmoothRiemannianMetric I M) (σ : Equiv.Perm (Fin 4))
    (S : SmoothCcTensor g 0 2) : SmoothCcTensor g 4 6 :=
  rsDomDomCongrSection (I := I) (M := M) g 4 6
    (LowBaseInternal.monoPerm σ)
    (slotExtendIter (I := I) (M := M) g 0 2 4 S)

private theorem monoExt_sub_c2
    (g : SmoothRiemannianMetric I M) (σ : Equiv.Perm (Fin 4))
    (S R : SmoothCcTensor g 0 2) :
    monoExtC2 (I := I) (M := M) g σ (S - R) =
      monoExtC2 (I := I) (M := M) g σ S -
        monoExtC2 (I := I) (M := M) g σ R := by
  rw [monoExtC2, slot4_sub_c2, rsperm_sub_c2]
  rfl

private theorem monoExt_jet_c2
    (g : SmoothRiemannianMetric I M) (σ : Equiv.Perm (Fin 4))
    (S : SmoothCcTensor g 0 2) :
    c2JetSq (I := I) (M := M) g
        (monoExtC2 (I := I) (M := M) g σ S) ≤
      (Module.finrank ℝ E : ℝ) ^ 4 *
        c2JetSq (I := I) (M := M) g S := by
  rw [monoExtC2, rsperm_jet_c2]
  exact slot4_jet_c2 (I := I) (M := M) g S

private theorem raise_eq_rev
    (g gm : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      gm.inner y v w =
        g.inner y v w + ccTensorBilinSymm (I := I) g T y v w) :
    symmRaiseEndo (I := I) (M := M) g T =
      gInvDiffRaisedEndoField (I := I) gm g := by
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro v
  apply (metricFlatMap (I := I) g x).injective
  ext w
  rw [metricFlatMap_apply, metricFlatMap_apply]
  rw [symmRaiseEndo_apply, inner_symmRaiseEndo]
  rw [show gInvDiffRaisedEndoField (I := I) gm g x =
      gInvDiffRaisedEndo (I := I) gm g x from rfl]
  rw [inner_g1_gInvDiffRaisedEndo (I := I) gm g x v w]
  rw [htie x v w]
  ring

private theorem raised_cancel_lr
    (a b : SmoothRiemannianMetric I M) (x : M) :
    (gInvRaisedEndo (I := I) a b x).comp
        (gInvRaisedEndo (I := I) b a x) =
      ContinuousLinearMap.id ℝ (TangentSpace I x) := by
  apply ContinuousLinearMap.ext
  intro v
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
    gInvRaisedEndo_apply, gInvRaisedEndo_apply]
  rw [g0FlatCLM_inverseMetricSharpFib (I := I) a x
    (g0FlatCLM (I := I) b x v)]
  rw [inverseMetricSharpFib_g0FlatCLM (I := I) b x v]

private theorem raised_sub_factor
    (g gT gU : SmoothRiemannianMetric I M)
    (T U : SmoothCcTensor g 0 2)
    (hTtie : ∀ (y : M) (v w : TangentSpace I y),
      gT.inner y v w =
        g.inner y v w + ccTensorBilinSymm (I := I) g T y v w)
    (hUtie : ∀ (y : M) (v w : TangentSpace I y),
      gU.inner y v w =
        g.inner y v w + ccTensorBilinSymm (I := I) g U y v w)
    (x : M) :
    gInvRaisedEndo (I := I) g gT x -
        gInvRaisedEndo (I := I) g gU x =
      -((gInvRaisedEndo (I := I) g gT x).comp
        ((symmRaiseEndo (I := I) (M := M) g (T - U) x).comp
          (gInvRaisedEndo (I := I) g gU x))) := by
  let FT := gInvRaisedEndo (I := I) g gT x
  let FU := gInvRaisedEndo (I := I) g gU x
  let RT := gInvRaisedEndo (I := I) gT g x
  let RU := gInvRaisedEndo (I := I) gU g x
  let PT := symmRaiseEndo (I := I) (M := M) g T x
  let PU := symmRaiseEndo (I := I) (M := M) g U x
  let P := symmRaiseEndo (I := I) (M := M) g (T - U) x
  have hRT : RT = PT + 1 := by
    apply ContinuousLinearMap.ext
    intro v
    have hr := congrArg (fun F => F x)
      (raise_eq_rev (I := I) (M := M) g gT T hTtie)
    have hv := congrArg (fun L => L v) hr
    change gInvRaisedEndo (I := I) gT g x v = PT v + v
    rw [gInvRaisedEndo_eq_diff_add_id]
    exact congrArg (fun z => z + v) hv.symm
  have hRU : RU = PU + 1 := by
    apply ContinuousLinearMap.ext
    intro v
    have hr := congrArg (fun F => F x)
      (raise_eq_rev (I := I) (M := M) g gU U hUtie)
    have hv := congrArg (fun L => L v) hr
    change gInvRaisedEndo (I := I) gU g x v = PU v + v
    rw [gInvRaisedEndo_eq_diff_add_id]
    exact congrArg (fun z => z + v) hv.symm
  have hP : P = PT - PU := by
    have hs :
        symmRaiseEndo (I := I) (M := M) g (T - U) =
          symmRaiseEndo (I := I) (M := M) g T -
            symmRaiseEndo (I := I) (M := M) g U := by
      calc
        symmRaiseEndo (I := I) (M := M) g (T - U) =
            symmRaiseEndo (I := I) (M := M) g (T + (-1 : ℝ) • U) := by
              rw [neg_one_smul, sub_eq_add_neg]
        _ = symmRaiseEndo (I := I) (M := M) g T +
              symmRaiseEndo (I := I) (M := M) g ((-1 : ℝ) • U) := by
                rw [symmRaiseEndo_add]
        _ = symmRaiseEndo (I := I) (M := M) g T +
              (-1 : ℝ) • symmRaiseEndo (I := I) (M := M) g U := by
                rw [symmRaiseEndo_smul]
        _ = symmRaiseEndo (I := I) (M := M) g T -
              symmRaiseEndo (I := I) (M := M) g U := by
                simpa only [sub_eq_add_neg] using
                  congrArg
                    (fun z => symmRaiseEndo (I := I) (M := M) g T + z)
                    (neg_one_smul ℝ
                      (symmRaiseEndo (I := I) (M := M) g U))
    exact congrArg (fun F => F x) hs
  have hFTC : FT * RT = 1 := by
    simpa only [FT, RT, ContinuousLinearMap.mul_def] using
      raised_cancel_lr (I := I) (M := M) g gT x
  have hUCF : RU * FU = 1 := by
    simpa only [RU, FU, ContinuousLinearMap.mul_def] using
      raised_cancel_lr (I := I) (M := M) gU g x
  change FT - FU = -(FT.comp (P.comp FU))
  rw [show FT.comp (P.comp FU) = FT * P * FU by
    simp only [ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_assoc]]
  calc
    FT - FU = FT * (RU * FU) - (FT * RT) * FU := by
      rw [hUCF, hFTC, mul_one, one_mul]
    _ = FT * (RU - RT) * FU := by noncomm_ring
    _ = -(FT * P * FU) := by
      rw [hRT, hRU, hP]
      noncomm_ring

set_option backward.isDefEq.respectTransparency false in
private theorem invSlot_factor
    (g gT gU : SmoothRiemannianMetric I M)
    (T U : SmoothCcTensor g 0 2)
    (hTtie : ∀ (y : M) (v w : TangentSpace I y),
      gT.inner y v w =
        g.inner y v w + ccTensorBilinSymm (I := I) g T y v w)
    (hUtie : ∀ (y : M) (v w : TangentSpace I y),
      gU.inner y v w =
        g.inner y v w + ccTensorBilinSymm (I := I) g U y v w) :
    gInvDiffSlotCoeff (I := I) g gT -
        gInvDiffSlotCoeff (I := I) g gU =
      -appCcRS (I := I) (M := M) g 2 2 2
        (fullSlot2 (I := I) (M := M) g gU)
        (appCcRS (I := I) (M := M) g 2 2 2
          (perturbSlot2 (I := I) (M := M) g (T - U))
          (fullSlot2 (I := I) (M := M) g gT)) := by
  rw [gInvDiffSlotCoeff_eq_slotInsertEndoCc (I := I) g gT,
    gInvDiffSlotCoeff_eq_slotInsertEndoCc (I := I) g gU,
    ← slotInsertEndoCc_sub]
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [SmoothCcTensor.toSection_neg]
  simp only [ContMDiffSection.coe_neg, Pi.neg_apply]
  rw [appCcRS_toSection, appCcRS_toSection]
  simp only [fullSlot2, perturbSlot2, slotInsertEndoCc_toSection,
    fullRaisedEndoField_apply]
  rw [slotInsertFib_comp, slotInsertFib_comp]
  rw [ContMDiffSection.coe_sub, Pi.sub_apply]
  rw [show gInvDiffRaisedEndoField (I := I) g gT x =
      gInvDiffRaisedEndo (I := I) g gT x from rfl,
    show gInvDiffRaisedEndoField (I := I) g gU x =
      gInvDiffRaisedEndo (I := I) g gU x from rfl]
  have hinv :
      gInvDiffRaisedEndo (I := I) g gT x -
          gInvDiffRaisedEndo (I := I) g gU x =
        gInvRaisedEndo (I := I) g gT x -
          gInvRaisedEndo (I := I) g gU x := by
    apply ContinuousLinearMap.ext
    intro v
    simp only [ContinuousLinearMap.sub_apply,
      gInvRaisedEndo_eq_diff_add_id]
    abel
  rw [hinv]
  rw [raised_sub_factor (I := I) (M := M) g gT gU T U hTtie hUtie x]
  rw [show -((gInvRaisedEndo (I := I) g gT x).comp
        ((symmRaiseEndo (I := I) (M := M) g (T - U) x).comp
          (gInvRaisedEndo (I := I) g gU x))) =
      (-1 : ℝ) • ((gInvRaisedEndo (I := I) g gT x).comp
        ((symmRaiseEndo (I := I) (M := M) g (T - U) x).comp
          (gInvRaisedEndo (I := I) g gU x))) by rw [neg_one_smul],
    slotInsertEndoFib_smul_left, neg_one_smul]
  rw [ContinuousLinearMap.comp_assoc]

/-- The difference of the two inverse-metric rank-two coefficients factors
through fixed-background raising of the metric perturbation difference. -/
theorem invSlot_sub_factor
    (g gT gU : SmoothRiemannianMetric I M)
    (T U : SmoothCcTensor g 0 2)
    (hTtie : ∀ (y : M) (v w : TangentSpace I y),
      gT.inner y v w =
        g.inner y v w + ccTensorBilinSymm (I := I) g T y v w)
    (hUtie : ∀ (y : M) (v w : TangentSpace I y),
      gU.inner y v w =
        g.inner y v w + ccTensorBilinSymm (I := I) g U y v w) :
    gInvDiffSlotCoeff (I := I) g gT -
        gInvDiffSlotCoeff (I := I) g gU =
      -appCcRS (I := I) (M := M) g 2 2 2
        (slotInsertEndoCc (I := I) (M := M) g 1
          (fullRaisedEndoField (I := I) (M := M) g gU))
        (appCcRS (I := I) (M := M) g 2 2 2
          (slotInsertEndoCc (I := I) (M := M) g 1
            (symmRaiseEndo (I := I) (M := M) g (T - U)))
          (slotInsertEndoCc (I := I) (M := M) g 1
            (fullRaisedEndoField (I := I) (M := M) g gT))) := by
  simpa only [fullSlot2, perturbSlot2] using
    invSlot_factor (I := I) (M := M) g gT gU T U hTtie hUtie

private theorem perm_icg_norm_c2
    (g : SmoothRiemannianMetric I M) (σ : Equiv.Perm (Fin 2))
    (T : SmoothCcTensor g 0 2) (k : ℕ) :
    ‖iteratedCovGrad (I := I) g 0 2 k
        (domDomCongrSection (I := I) g σ T)‖ =
      ‖iteratedCovGrad (I := I) g 0 2 k T‖ := by
  classical
  set μ := riemannianVolumeMeasure (I := I) (M := M) g
  have hbridge : ∀ W : SmoothCcTensor g 0 2,
      ‖iteratedCovGrad (I := I) g 0 2 k W‖ ^ 2 =
        ∫ x, riemannianFiberNormSq (I := I) (M := M) g 0 (2 + k) x
          ((iteratedCovGrad (I := I) g 0 2 k W).toSection x) ∂μ := by
    intro W
    rw [SmoothCcTensor.norm_def (I := I) (M := M)
      (iteratedCovGrad (I := I) g 0 2 k W)]
    exact tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq
      (I := I) (M := M) g (2 + k)
        (iteratedCovGrad (I := I) g 0 2 k W)
  have hintegrand : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g 0 (2 + k) x
          ((iteratedCovGrad (I := I) g 0 2 k
            (domDomCongrSection (I := I) g σ T)).toSection x) =
        riemannianFiberNormSq (I := I) (M := M) g 0 (2 + k) x
          ((iteratedCovGrad (I := I) g 0 2 k T).toSection x) :=
    fun x => riemannianFiberNormSq_iteratedCovGrad_domDomCongrSection
      (I := I) (M := M) g (s := 2) σ T k x
  have hsq :
      ‖iteratedCovGrad (I := I) g 0 2 k
          (domDomCongrSection (I := I) g σ T)‖ ^ 2 =
        ‖iteratedCovGrad (I := I) g 0 2 k T‖ ^ 2 := by
    rw [hbridge (domDomCongrSection (I := I) g σ T), hbridge T]
    exact MeasureTheory.integral_congr_ae
      (Filter.Eventually.of_forall hintegrand)
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq

private theorem symm_icg_norm_c2
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2) (k : ℕ) :
    ‖iteratedCovGrad (I := I) g 0 2 k
        (symmS (I := I) (M := M) g T)‖ ≤
      ‖iteratedCovGrad (I := I) g 0 2 k T‖ := by
  classical
  let Tsw : SmoothCcTensor g 0 2 :=
    domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 2) 1) T
  have hiter :
      iteratedCovGrad (I := I) g 0 2 k
          (symmS (I := I) (M := M) g T) =
        (1 / 2 : ℝ) • iteratedCovGrad (I := I) g 0 2 k T +
          (1 / 2 : ℝ) • iteratedCovGrad (I := I) g 0 2 k Tsw := by
    dsimp only [Tsw]
    exact iteratedCovGrad_symmS_eq (I := I) (M := M) g T k
  rw [hiter]
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, norm_smul]
  have habs : ‖(1 / 2 : ℝ)‖ = 1 / 2 := by
    rw [Real.norm_eq_abs]
    norm_num
  rw [habs]
  have hperm :
      ‖iteratedCovGrad (I := I) g 0 2 k Tsw‖ =
        ‖iteratedCovGrad (I := I) g 0 2 k T‖ := by
    exact perm_icg_norm_c2 (I := I) (M := M) g
      (Equiv.swap (0 : Fin 2) 1) T k
  rw [hperm]
  linarith [norm_nonneg (iteratedCovGrad (I := I) g 0 2 k T)]

private theorem symm_jet_c2
    (g : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g 0 2) :
    c2JetSq (I := I) (M := M) g
        (symmS (I := I) (M := M) g T) ≤
      c2JetSq (I := I) (M := M) g T := by
  unfold c2JetSq
  exact Finset.sum_le_sum fun i _ =>
    pow_le_pow_left₀ (norm_nonneg _)
      (symm_icg_norm_c2 (I := I) (M := M) g T i) 2

set_option linter.unusedSectionVars false in
private theorem unitModel_sub_c2
    (g : SmoothRiemannianMetric I M)
    (A B : SmoothCcTensor g 0 2) (x : M) :
    unitModel (I := I) (M := M) g 2 (A - B) x =
      unitModel (I := I) (M := M) g 2 A x -
        unitModel (I := I) (M := M) g 2 B x := by
  simp only [unitModel]
  rfl

private theorem domperm_sub_c2
    (g : SmoothRiemannianMetric I M)
    (σ : Equiv.Perm (Fin 2)) (A B : SmoothCcTensor g 0 2) :
    domDomCongrSection (I := I) g σ (A - B) =
      domDomCongrSection (I := I) g σ A -
        domDomCongrSection (I := I) g σ B := by
  refine smoothCcTensor_ext_of_unitModel
    (I := I) (M := M) g (fun x => ?_)
  rw [domDomCongrSection_unitModel,
    unitModel_sub_c2 (I := I) (M := M) g A B x,
    unitModel_sub_c2 (I := I) (M := M) g
      (domDomCongrSection (I := I) g σ A)
      (domDomCongrSection (I := I) g σ B) x,
    domDomCongrSection_unitModel, domDomCongrSection_unitModel]
  refine ContinuousMultilinearMap.ext (fun w => ?_)
  rw [ContinuousMultilinearMap.domDomCongr_apply,
    ContinuousMultilinearMap.sub_apply,
    ContinuousMultilinearMap.sub_apply,
    ContinuousMultilinearMap.domDomCongr_apply,
    ContinuousMultilinearMap.domDomCongr_apply]

private theorem symmS_sub_c2
    (g : SmoothRiemannianMetric I M)
    (T U : SmoothCcTensor g 0 2) :
    symmS (I := I) (M := M) g (T - U) =
      symmS (I := I) (M := M) g T -
        symmS (I := I) (M := M) g U := by
  simp only [symmS]
  rw [domperm_sub_c2]
  module

private theorem jet3_smul_c2
    (g : SmoothRiemannianMetric I M) {r s : ℕ}
    (a : ℝ) (A : SmoothCcTensor g r s) :
    c2JetSq (I := I) (M := M) g (a • A) =
      a ^ 2 * c2JetSq (I := I) (M := M) g A := by
  unfold c2JetSq
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [iteratedCovGrad_smul, norm_smul, Real.norm_eq_abs]
  rw [mul_pow, sq_abs]

private theorem appCc_sub_right_c2
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (Φ : SmoothCcTensor g r s) (A B : SmoothCcTensor g 0 r) :
    appCc (I := I) (M := M) g r s Φ (A - B) =
      appCc (I := I) (M := M) g r s Φ A -
        appCc (I := I) (M := M) g r s Φ B := by
  rw [sub_eq_add_neg, appCc_add_right]
  rw [show -B = (-1 : ℝ) • B by simp, appCc_smul_right]
  module

private theorem insert1_icg_le
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) (i : ℕ)
    (Λ : ContMDiffSection I (E →L[ℝ] E) ∞
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)) :
    ‖iteratedCovGrad (I := I) g 2 2 i
        (slotInsertEndoCc (I := I) (M := M) g 1 Λ)‖ ≤
      3 * ‖iteratedCovGrad (I := I) g 1 1 i
        (slotInsertEndoCc (I := I) (M := M) g 0 Λ)‖ := by
  classical
  set F : M → ℝ := fun x => 3 *
    riemannianFiberNormSq (I := I) (M := M) g 1 (1 + i) x
      ((iteratedCovGrad (I := I) g 1 1 i
        (slotInsertEndoCc (I := I) (M := M) g 0 Λ)).toSection x)
  have hFint : MeasureTheory.Integrable F
      (riemannianVolumeMeasure (I := I) (M := M) g) := by
    dsimp only [F]
    exact (integrable_riemannianFiberNormSq_toSection
      (I := I) (M := M) g 1 (1 + i)
        (iteratedCovGrad (I := I) g 1 1 i
          (slotInsertEndoCc (I := I) (M := M) g 0 Λ))).const_mul _
  have hpt : ∀ x,
      riemannianFiberNormSq (I := I) (M := M) g 2 (2 + i) x
          ((iteratedCovGrad (I := I) g 2 2 i
            (slotInsertEndoCc (I := I) (M := M) g 1 Λ)).toSection x) ≤
        F x := by
    intro x
    have h := rfns_iteratedCovGrad_slotInsertEndoCc_le_endo
      (I := I) (M := M) g 1 Λ i x
    rw [hDim] at h
    norm_num at h
    simpa only [F, Nat.reduceAdd] using h
  have hsq := normSq_le_integral_of_pointwise_fiberNormSq_le_rs
    (I := I) (M := M) g 2 (2 + i)
      (iteratedCovGrad (I := I) g 2 2 i
        (slotInsertEndoCc (I := I) (M := M) g 1 Λ)) F hFint hpt
  have hint :
      ∫ x, riemannianFiberNormSq (I := I) (M := M) g 1 (1 + i) x
          ((iteratedCovGrad (I := I) g 1 1 i
            (slotInsertEndoCc (I := I) (M := M) g 0 Λ)).toSection x)
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
        ‖iteratedCovGrad (I := I) g 1 1 i
          (slotInsertEndoCc (I := I) (M := M) g 0 Λ)‖ ^ 2 := by
    rw [SmoothCcTensor.norm_def,
      tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs
        (I := I) (M := M) g 1 (1 + i)]
  rw [MeasureTheory.integral_const_mul, hint] at hsq
  refine le_of_sq_le_sq ?_
    (mul_nonneg (by norm_num) (norm_nonneg _))
  calc
    ‖iteratedCovGrad (I := I) g 2 2 i
        (slotInsertEndoCc (I := I) (M := M) g 1 Λ)‖ ^ 2
        ≤ 3 * ‖iteratedCovGrad (I := I) g 1 1 i
          (slotInsertEndoCc (I := I) (M := M) g 0 Λ)‖ ^ 2 := hsq
    _ ≤ (3 * ‖iteratedCovGrad (I := I) g 1 1 i
        (slotInsertEndoCc (I := I) (M := M) g 0 Λ)‖) ^ 2 := by
      nlinarith [sq_nonneg
        ‖iteratedCovGrad (I := I) g 1 1 i
          (slotInsertEndoCc (I := I) (M := M) g 0 Λ)‖]

private theorem perturbSlot2_icg_le
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2) (i : ℕ) :
    ‖iteratedCovGrad (I := I) g 2 2 i
        (perturbSlot2 (I := I) (M := M) g T)‖ ≤
      3 * ‖iteratedCovGrad (I := I) g 0 2 i T‖ := by
  let Λ := symmRaiseEndo (I := I) (M := M) g T
  have hslot := insert1_icg_le (I := I) (M := M) hDim g i Λ
  have hbase :
      ‖iteratedCovGrad (I := I) g 1 1 i
          (slotInsertEndoCc (I := I) (M := M) g 0 Λ)‖ ≤
        ‖iteratedCovGrad (I := I) g 0 2 i T‖ := by
    rw [show slotInsertEndoCc (I := I) (M := M) g 0 Λ =
        cometricRaiseSlot0Field (I := I) (M := M) g 0
          (domDomCongrSection (I := I) g
            (Equiv.swap (0 : Fin 2) 1)
            (symmS (I := I) (M := M) g T)) from by
      simpa only [Λ] using insert_symmRaise_eq (I := I) (M := M) g T]
    calc
      _ = ‖iteratedCovGrad (I := I) g 0 2 i
          (domDomCongrSection (I := I) g
            (Equiv.swap (0 : Fin 2) 1)
            (symmS (I := I) (M := M) g T))‖ := by
            simpa only [Nat.zero_add, Nat.reduceAdd] using
              norm_iCG_cometricRaiseSlot0Field_eq
                (I := I) (M := M) g 0
                (domDomCongrSection (I := I) g
                  (Equiv.swap (0 : Fin 2) 1)
                  (symmS (I := I) (M := M) g T)) i
      _ = ‖iteratedCovGrad (I := I) g 0 2 i
          (symmS (I := I) (M := M) g T)‖ :=
        perm_icg_norm_c2 (I := I) (M := M) g
          (Equiv.swap (0 : Fin 2) 1)
          (symmS (I := I) (M := M) g T) i
      _ ≤ _ := symm_icg_norm_c2 (I := I) (M := M) g T i
  exact hslot.trans
    (mul_le_mul_of_nonneg_left hbase (by norm_num))

private theorem fullField_decomp_c2
    (g gm : SmoothRiemannianMetric I M) :
    fullRaisedEndoField (I := I) (M := M) g gm =
      gInvDiffRaisedEndoField (I := I) g gm +
        fullRaisedEndoField (I := I) (M := M) g g := by
  apply ContMDiffSection.ext
  intro x
  rw [show ((gInvDiffRaisedEndoField (I := I) g gm +
      fullRaisedEndoField (I := I) (M := M) g g) x) =
      gInvDiffRaisedEndoField (I := I) g gm x +
        fullRaisedEndoField (I := I) (M := M) g g x from by
          rw [ContMDiffSection.coe_add]
          rfl]
  apply ContinuousLinearMap.ext
  intro v
  rw [fullRaisedEndoField_apply, ContinuousLinearMap.add_apply]
  rw [show gInvDiffRaisedEndoField (I := I) g gm x =
      gInvDiffRaisedEndo (I := I) g gm x from rfl]
  rw [fullRaisedEndoField_apply,
    gInvRaisedEndo_eq_diff_add_id (I := I) g gm x v]
  rw [show gInvRaisedEndo (I := I) g g x v = v from by
    rw [gInvRaisedEndo_apply, inverseMetricSharpFib_g0FlatCLM]]

private theorem fullSlot2_decomp
    (g gm : SmoothRiemannianMetric I M) :
    fullSlot2 (I := I) (M := M) g gm =
      gInvDiffSlotCoeff (I := I) g gm +
        fullSlot2 (I := I) (M := M) g g := by
  rw [fullSlot2, fullField_decomp_c2 (I := I) (M := M) g gm,
    slotInsertEndoCc_add,
    gInvDiffSlotCoeff_eq_slotInsertEndoCc (I := I) g gm]
  rfl

private theorem jet3_add_c2
    (g : SmoothRiemannianMetric I M) {r s : ℕ}
    (A B : SmoothCcTensor g r s) :
    (∑ j ∈ Finset.range 3,
        ‖iteratedCovGrad (I := I) g r s j (A + B)‖ ^ 2) ≤
      2 * ((∑ j ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g r s j A‖ ^ 2) +
        ∑ j ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g r s j B‖ ^ 2) := by
  calc
    (∑ j ∈ Finset.range 3,
        ‖iteratedCovGrad (I := I) g r s j (A + B)‖ ^ 2) ≤
        ∑ j ∈ Finset.range 3,
          2 * (‖iteratedCovGrad (I := I) g r s j A‖ ^ 2 +
            ‖iteratedCovGrad (I := I) g r s j B‖ ^ 2) := by
      refine Finset.sum_le_sum fun j _ => ?_
      rw [iteratedCovGrad_add]
      have htri := norm_add_le
        (iteratedCovGrad (I := I) g r s j A)
        (iteratedCovGrad (I := I) g r s j B)
      calc
        ‖iteratedCovGrad (I := I) g r s j A +
            iteratedCovGrad (I := I) g r s j B‖ ^ 2 ≤
            (‖iteratedCovGrad (I := I) g r s j A‖ +
              ‖iteratedCovGrad (I := I) g r s j B‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) htri 2
        _ ≤ 2 * (‖iteratedCovGrad (I := I) g r s j A‖ ^ 2 +
            ‖iteratedCovGrad (I := I) g r s j B‖ ^ 2) := by
          nlinarith [sq_nonneg
            (‖iteratedCovGrad (I := I) g r s j A‖ -
              ‖iteratedCovGrad (I := I) g r s j B‖)]
    _ = 2 * ((∑ j ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g r s j A‖ ^ 2) +
        ∑ j ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g r s j B‖ ^ 2) := by
      simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]

private theorem jet3_sub_c2
    (g : SmoothRiemannianMetric I M) {r s : ℕ}
    (A B : SmoothCcTensor g r s) :
    c2JetSq (I := I) (M := M) g (A - B) ≤
      2 * (c2JetSq (I := I) (M := M) g A +
        c2JetSq (I := I) (M := M) g B) := by
  have h := jet3_add_c2 (I := I) (M := M) g A (-B)
  simpa only [c2JetSq, sub_eq_add_neg, iteratedCovGrad_neg, norm_neg] using h

omit [BoundarylessManifold I M] in
private theorem jet3_nonneg_c2
    (g : SmoothRiemannianMetric I M) {r s : ℕ}
    (A : SmoothCcTensor g r s) :
    0 ≤ ∑ j ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g r s j A‖ ^ 2 :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

private theorem jet3_fiber_c2
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (A : SmoothCcTensor g r s) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g r s x
            (A.toSection x) ≤
          C ^ 2 * (∑ j ∈ Finset.range 3,
            ‖iteratedCovGrad (I := I) g r s j A‖ ^ 2) := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_riemannianFiberNorm_le_iteratedCovGrad_l2_jetSum_supercritical
      (I := I) (M := M) g r s
  refine ⟨C, hC, ?_⟩
  intro A x
  have hrange :
      Finset.range (Module.finrank ℝ E / 2 + 2) =
        Finset.range 3 := by
    rw [hDim]
  simpa only [hrange] using hbound A x

private theorem perturbSlot2_jet
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : SmoothCcTensor g 0 2,
      (∑ j ∈ Finset.range 3,
        ‖iteratedCovGrad (I := I) g 2 2 j
          (perturbSlot2 (I := I) (M := M) g T)‖ ^ 2) ≤
        (C * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖) ^ 2 := by
  obtain ⟨Chs, hChs, hhs⟩ := hs2_low2 (I := I) (M := M) g 2
  refine ⟨3 * Chs, mul_nonneg (by norm_num) hChs, ?_⟩
  intro T
  calc
    (∑ j ∈ Finset.range 3,
        ‖iteratedCovGrad (I := I) g 2 2 j
          (perturbSlot2 (I := I) (M := M) g T)‖ ^ 2) ≤
        ∑ j ∈ Finset.range 3,
          (3 * ‖iteratedCovGrad (I := I) g 0 2 j T‖) ^ 2 := by
      refine Finset.sum_le_sum fun j _ => ?_
      exact pow_le_pow_left₀ (norm_nonneg _)
        (perturbSlot2_icg_le (I := I) (M := M) hDim g T j) 2
    _ = 9 * (∑ j ∈ Finset.range 3,
        ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ ≤ 9 * (Chs *
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖) ^ 2 :=
      mul_le_mul_of_nonneg_left (hhs T) (by norm_num)
    _ = (3 * Chs *
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖) ^ 2 := by
      ring

/-- On a common small three-dimensional spectral `H2` ball, the rank-two
inverse-metric coefficient is Lipschitz in both its pointwise norm and its
first three covariant `L²` jets. -/
theorem invCoeff_h2_lip
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ C : ℝ, 0 < ρ ∧ 0 ≤ C ∧
      ∀ (T U : SmoothCcTensor g 0 2)
        (gT gU : SmoothRiemannianMetric I M),
        (∀ (y : M) (v w : TangentSpace I y),
          gT.inner y v w =
            g.inner y v w +
              ccTensorBilinSymm (I := I) g T y v w) →
        (∀ (y : M) (v w : TangentSpace I y),
          gU.inner y v w =
            g.inner y v w +
              ccTensorBilinSymm (I := I) g U y v w) →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ ≤ ρ →
        (∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g 2 2 x
              ((gInvDiffSlotCoeff (I := I) g gT -
                gInvDiffSlotCoeff (I := I) g gU).toSection x) ≤
            (C * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
              (T - U)‖) ^ 2) ∧
          (∑ j ∈ Finset.range 3,
            ‖iteratedCovGrad (I := I) g 2 2 j
              (gInvDiffSlotCoeff (I := I) g gT -
                gInvDiffSlotCoeff (I := I) g gU)‖ ^ 2) ≤
            (C * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
              (T - U)‖) ^ 2 := by
  classical
  obtain ⟨ρ, Cinv, hρ, hCinv, hinv⟩ :=
    inv_coeff_h2 (I := I) (M := M) hDim g
  obtain ⟨Cp, hCp, hpert⟩ :=
    perturbSlot2_jet (I := I) (M := M) hDim g
  obtain ⟨Cmul, hCmul, hmul⟩ :=
    appRS_h2_h2_h2 (I := I) (M := M) hDim g 2 2 2
  obtain ⟨Cpt, hCpt, hpoint⟩ :=
    jet3_fiber_c2 (I := I) (M := M) hDim g 2 2
  let J0 : ℝ := ∑ j ∈ Finset.range 3,
    ‖iteratedCovGrad (I := I) g 2 2 j
      (fullSlot2 (I := I) (M := M) g g)‖ ^ 2
  let B0 : ℝ := Real.sqrt J0
  let Z : ℝ := 2 * ((Cinv * ρ) ^ 2 + B0 ^ 2)
  let A : ℝ := Real.sqrt Z
  let C0 : ℝ := Cmul ^ 2 * Cp * A ^ 2
  let C : ℝ := (Cpt + 1) * C0
  have hJ0 : 0 ≤ J0 := by
    exact jet3_nonneg_c2 (I := I) (M := M) g
      (fullSlot2 (I := I) (M := M) g g)
  have hB0 : 0 ≤ B0 := Real.sqrt_nonneg _
  have hB0sq : B0 ^ 2 = J0 := by
    simpa only [B0] using Real.sq_sqrt hJ0
  have hZ : 0 ≤ Z := by
    dsimp only [Z]
    positivity
  have hA : 0 ≤ A := Real.sqrt_nonneg _
  have hAsq : A ^ 2 = Z := by
    simpa only [A] using Real.sq_sqrt hZ
  have hC0 : 0 ≤ C0 := by
    dsimp only [C0]
    positivity
  have hC : 0 ≤ C := by
    dsimp only [C]
    exact mul_nonneg
      (add_nonneg hCpt (by norm_num)) hC0
  refine ⟨ρ, C, hρ, hC, ?_⟩
  intro T U gT gU hTtie hUtie hT hU
  let NT : ℝ :=
    ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖
  let NU : ℝ :=
    ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖
  let N : ℝ :=
    ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U)‖
  have hNT : 0 ≤ NT := norm_nonneg _
  have hNU : 0 ≤ NU := norm_nonneg _
  have hN : 0 ≤ N := norm_nonneg _
  have hinvT :
      (∑ j ∈ Finset.range 3,
        ‖iteratedCovGrad (I := I) g 2 2 j
          (gInvDiffSlotCoeff (I := I) g gT)‖ ^ 2) ≤
        (Cinv * NT) ^ 2 := by
    simpa only [NT] using (hinv T gT hT hTtie).2
  have hinvU :
      (∑ j ∈ Finset.range 3,
        ‖iteratedCovGrad (I := I) g 2 2 j
          (gInvDiffSlotCoeff (I := I) g gU)‖ ^ 2) ≤
        (Cinv * NU) ^ 2 := by
    simpa only [NU] using (hinv U gU hU hUtie).2
  have hfullT :
      (∑ j ∈ Finset.range 3,
        ‖iteratedCovGrad (I := I) g 2 2 j
          (fullSlot2 (I := I) (M := M) g gT)‖ ^ 2) ≤ A ^ 2 := by
    rw [fullSlot2_decomp (I := I) (M := M) g gT]
    calc
      _ ≤ 2 * ((∑ j ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g 2 2 j
            (gInvDiffSlotCoeff (I := I) g gT)‖ ^ 2) +
          ∑ j ∈ Finset.range 3,
            ‖iteratedCovGrad (I := I) g 2 2 j
              (fullSlot2 (I := I) (M := M) g g)‖ ^ 2) :=
        jet3_add_c2 (I := I) (M := M) g _ _
      _ ≤ 2 * ((Cinv * NT) ^ 2 + J0) :=
        mul_le_mul_of_nonneg_left (add_le_add hinvT le_rfl)
          (by norm_num)
      _ ≤ 2 * ((Cinv * ρ) ^ 2 + B0 ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        rw [hB0sq]
        exact add_le_add
          (pow_le_pow_left₀ (mul_nonneg hCinv hNT)
            (mul_le_mul_of_nonneg_left hT hCinv) 2) le_rfl
      _ = A ^ 2 := by rw [hAsq]
  have hfullU :
      (∑ j ∈ Finset.range 3,
        ‖iteratedCovGrad (I := I) g 2 2 j
          (fullSlot2 (I := I) (M := M) g gU)‖ ^ 2) ≤ A ^ 2 := by
    rw [fullSlot2_decomp (I := I) (M := M) g gU]
    calc
      _ ≤ 2 * ((∑ j ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g 2 2 j
            (gInvDiffSlotCoeff (I := I) g gU)‖ ^ 2) +
          ∑ j ∈ Finset.range 3,
            ‖iteratedCovGrad (I := I) g 2 2 j
              (fullSlot2 (I := I) (M := M) g g)‖ ^ 2) :=
        jet3_add_c2 (I := I) (M := M) g _ _
      _ ≤ 2 * ((Cinv * NU) ^ 2 + J0) :=
        mul_le_mul_of_nonneg_left (add_le_add hinvU le_rfl)
          (by norm_num)
      _ ≤ 2 * ((Cinv * ρ) ^ 2 + B0 ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        rw [hB0sq]
        exact add_le_add
          (pow_le_pow_left₀ (mul_nonneg hCinv hNU)
            (mul_le_mul_of_nonneg_left hU hCinv) 2) le_rfl
      _ = A ^ 2 := by rw [hAsq]
  have hpert :
      (∑ j ∈ Finset.range 3,
        ‖iteratedCovGrad (I := I) g 2 2 j
          (perturbSlot2 (I := I) (M := M) g (T - U))‖ ^ 2) ≤
        (Cp * N) ^ 2 := by
    simpa only [N] using hpert (T - U)
  let Mid : SmoothCcTensor g 2 2 :=
    appCcRS (I := I) (M := M) g 2 2 2
      (perturbSlot2 (I := I) (M := M) g (T - U))
      (fullSlot2 (I := I) (M := M) g gT)
  have hMid :
      (∑ j ∈ Finset.range 3,
        ‖iteratedCovGrad (I := I) g 2 2 j Mid‖ ^ 2) ≤
        (Cmul * (Cp * N) * A) ^ 2 := by
    exact hmul
      (perturbSlot2 (I := I) (M := M) g (T - U))
      (fullSlot2 (I := I) (M := M) g gT)
      (Cp * N) A (mul_nonneg hCp hN) hA hpert hfullT
  let Out : SmoothCcTensor g 2 2 :=
    appCcRS (I := I) (M := M) g 2 2 2
      (fullSlot2 (I := I) (M := M) g gU) Mid
  have hOut :
      (∑ j ∈ Finset.range 3,
        ‖iteratedCovGrad (I := I) g 2 2 j Out‖ ^ 2) ≤
        (C0 * N) ^ 2 := by
    have hout0 := hmul
      (fullSlot2 (I := I) (M := M) g gU) Mid
      A (Cmul * (Cp * N) * A) hA
      (mul_nonneg (mul_nonneg hCmul (mul_nonneg hCp hN)) hA)
      hfullU hMid
    simpa only [C0, Out] using (show
      (Cmul * A * (Cmul * (Cp * N) * A)) ^ 2 =
        (C0 * N) ^ 2 by
          dsimp only [C0]
          ring ▸ hout0)
  let D : SmoothCcTensor g 2 2 :=
    gInvDiffSlotCoeff (I := I) g gT -
      gInvDiffSlotCoeff (I := I) g gU
  have hD :
      (∑ j ∈ Finset.range 3,
        ‖iteratedCovGrad (I := I) g 2 2 j D‖ ^ 2) ≤
        (C0 * N) ^ 2 := by
    dsimp only [D]
    rw [invSlot_sub_factor (I := I) (M := M)
      g gT gU T U hTtie hUtie]
    simpa only [Out, Mid, fullSlot2, perturbSlot2,
      iteratedCovGrad_neg, norm_neg] using hOut
  have hC0C : C0 ≤ C := by
    dsimp only [C]
    nlinarith [mul_nonneg hCpt hC0]
  have hCptC : Cpt * C0 ≤ C := by
    dsimp only [C]
    nlinarith
  have hjet :
      (∑ j ∈ Finset.range 3,
        ‖iteratedCovGrad (I := I) g 2 2 j D‖ ^ 2) ≤
        (C * N) ^ 2 := by
    exact hD.trans
      (pow_le_pow_left₀ (mul_nonneg hC0 hN)
        (mul_le_mul_of_nonneg_right hC0C hN) 2)
  refine ⟨?_, ?_⟩
  · intro x
    have hpt := hpoint D x
    calc
      riemannianFiberNormSq (I := I) (M := M) g 2 2 x
          (D.toSection x) ≤
        Cpt ^ 2 * (∑ j ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g 2 2 j D‖ ^ 2) := hpt
      _ ≤ Cpt ^ 2 * (C0 * N) ^ 2 :=
        mul_le_mul_of_nonneg_left hD (sq_nonneg Cpt)
      _ = (Cpt * C0 * N) ^ 2 := by ring
      _ ≤ (C * N) ^ 2 :=
        pow_le_pow_left₀
          (mul_nonneg (mul_nonneg hCpt hC0) hN)
          (mul_le_mul_of_nonneg_right hCptC hN) 2
  · simpa only [D, N] using hjet

set_option maxHeartbeats 1600000 in
private theorem trace24_h2_lip
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ C : ℝ, 0 < ρ ∧ 0 ≤ C ∧
      ∀ (T U : SmoothCcTensor g 0 2)
        (gT gU : SmoothRiemannianMetric I M),
        (∀ (y : M) (v w : TangentSpace I y),
          gT.inner y v w =
            g.inner y v w +
              ccTensorBilinSymm (I := I) g T y v w) →
        (∀ (y : M) (v w : TangentSpace I y),
          gU.inner y v w =
            g.inner y v w +
              ccTensorBilinSymm (I := I) g U y v w) →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ ≤ ρ →
        c2JetSq (I := I) (M := M) g
            (pureTrace (I := I) (M := M) g gT 2 -
              pureTrace (I := I) (M := M) g gU 2) ≤
          (C * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
            (T - U)‖) ^ 2 ∧
        c2JetSq (I := I) (M := M) g
            (pureTrace (I := I) (M := M) g gT 4 -
              pureTrace (I := I) (M := M) g gU 4) ≤
          (C * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
            (T - U)‖) ^ 2 := by
  classical
  obtain ⟨ρ, Cinv, hρ, hCinv, hinv⟩ :=
    invCoeff_h2_lip (I := I) (M := M) hDim g
  obtain ⟨C₂, hC₂, happ₂⟩ :=
    appRS_h2_h2_h2 (I := I) (M := M) hDim g 4 4 2
  obtain ⟨C₄, hC₄, happ₄⟩ :=
    appRS_h2_h2_h2 (I := I) (M := M) hDim g 6 6 4
  let F₂ : SmoothCcTensor g 4 2 :=
    cometricDoubleTraceField (I := I) g 2
  let F₄ : SmoothCcTensor g 6 4 :=
    cometricDoubleTraceField (I := I) g 4
  let J₂ : ℝ := c2JetSq (I := I) (M := M) g F₂
  let J₄ : ℝ := c2JetSq (I := I) (M := M) g F₄
  let A₂ : ℝ := Real.sqrt J₂
  let A₄ : ℝ := Real.sqrt J₄
  let K₂ : ℝ := C₂ * A₂ * (3 * Cinv)
  let K₄ : ℝ := C₄ * A₄ * (9 * Cinv)
  let C : ℝ := K₂ + K₄
  have hJ₂ : 0 ≤ J₂ := by
    exact jet3_nonneg_c2 (I := I) (M := M) g F₂
  have hJ₄ : 0 ≤ J₄ := by
    exact jet3_nonneg_c2 (I := I) (M := M) g F₄
  have hA₂ : 0 ≤ A₂ := Real.sqrt_nonneg _
  have hA₄ : 0 ≤ A₄ := Real.sqrt_nonneg _
  have hA₂sq : A₂ ^ 2 = J₂ := by
    simpa only [A₂] using Real.sq_sqrt hJ₂
  have hA₄sq : A₄ ^ 2 = J₄ := by
    simpa only [A₄] using Real.sq_sqrt hJ₄
  have hK₂ : 0 ≤ K₂ := by
    dsimp only [K₂]
    exact mul_nonneg (mul_nonneg hC₂ hA₂)
      (mul_nonneg (by norm_num) hCinv)
  have hK₄ : 0 ≤ K₄ := by
    dsimp only [K₄]
    exact mul_nonneg (mul_nonneg hC₄ hA₄)
      (mul_nonneg (by norm_num) hCinv)
  have hC : 0 ≤ C := add_nonneg hK₂ hK₄
  refine ⟨ρ, C, hρ, hC, ?_⟩
  intro T U gT gU hTtie hUtie hT hU
  let N : ℝ :=
    ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U)‖
  let Λ :=
    gInvDiffRaisedEndoField (I := I) g gT -
      gInvDiffRaisedEndoField (I := I) g gU
  let D₂ : SmoothCcTensor g 4 4 :=
    slotInsertEndoCc (I := I) (M := M) g 3 Λ
  let D₄ : SmoothCcTensor g 6 6 :=
    slotInsertEndoCc (I := I) (M := M) g 5 Λ
  have hN : 0 ≤ N := norm_nonneg _
  have hinvJet :
      c2JetSq (I := I) (M := M) g
          (gInvDiffSlotCoeff (I := I) g gT -
            gInvDiffSlotCoeff (I := I) g gU) ≤
        (Cinv * N) ^ 2 := by
    simpa only [c2JetSq, N] using
      (hinv T U gT gU hTtie hUtie hT hU).2
  have hslot1 :
      slotInsertEndoCc (I := I) (M := M) g 1 Λ =
        gInvDiffSlotCoeff (I := I) g gT -
          gInvDiffSlotCoeff (I := I) g gU := by
    dsimp only [Λ]
    rw [slotInsertEndoCc_sub,
      ← gInvDiffSlotCoeff_eq_slotInsertEndoCc (I := I) g gT,
      ← gInvDiffSlotCoeff_eq_slotInsertEndoCc (I := I) g gU]
  have hD₂ :
      c2JetSq (I := I) (M := M) g D₂ ≤
        (3 * Cinv * N) ^ 2 := by
    calc
      c2JetSq (I := I) (M := M) g D₂ ≤
          (Module.finrank ℝ E : ℝ) ^ 2 *
            c2JetSq (I := I) (M := M) g
              (slotInsertEndoCc (I := I) (M := M) g 1 Λ) := by
        simpa only [D₂] using
          insert3_jet_c2 (I := I) (M := M) g Λ
      _ = 9 * c2JetSq (I := I) (M := M) g
            (gInvDiffSlotCoeff (I := I) g gT -
              gInvDiffSlotCoeff (I := I) g gU) := by
        rw [hDim, hslot1]
        norm_num
      _ ≤ 9 * (Cinv * N) ^ 2 :=
        mul_le_mul_of_nonneg_left hinvJet (by norm_num)
      _ = (3 * Cinv * N) ^ 2 := by ring
  have hD₄ :
      c2JetSq (I := I) (M := M) g D₄ ≤
        (9 * Cinv * N) ^ 2 := by
    calc
      c2JetSq (I := I) (M := M) g D₄ ≤
          (Module.finrank ℝ E : ℝ) ^ 4 *
            c2JetSq (I := I) (M := M) g
              (slotInsertEndoCc (I := I) (M := M) g 1 Λ) := by
        simpa only [D₄] using
          insert5_jet_c2 (I := I) (M := M) g Λ
      _ = 81 * c2JetSq (I := I) (M := M) g
            (gInvDiffSlotCoeff (I := I) g gT -
              gInvDiffSlotCoeff (I := I) g gU) := by
        rw [hDim, hslot1]
        norm_num
      _ ≤ 81 * (Cinv * N) ^ 2 :=
        mul_le_mul_of_nonneg_left hinvJet (by norm_num)
      _ = (9 * Cinv * N) ^ 2 := by ring
  have htrace₂ :
      pureTrace (I := I) (M := M) g gT 2 -
          pureTrace (I := I) (M := M) g gU 2 =
        appCcRS (I := I) (M := M) g 4 4 2 F₂ D₂ := by
    rw [pureTrace_split (I := I) (M := M) g gT 2,
      pureTrace_split (I := I) (M := M) g gU 2]
    calc
      (appCcRS (I := I) (M := M) g 4 4 2 F₂
            (slotInsertEndoCc (I := I) (M := M) g 3
              (gInvDiffRaisedEndoField (I := I) g gT)) + F₂) -
          (appCcRS (I := I) (M := M) g 4 4 2 F₂
            (slotInsertEndoCc (I := I) (M := M) g 3
              (gInvDiffRaisedEndoField (I := I) g gU)) + F₂) =
        appCcRS (I := I) (M := M) g 4 4 2 F₂
            (slotInsertEndoCc (I := I) (M := M) g 3
              (gInvDiffRaisedEndoField (I := I) g gT)) -
          appCcRS (I := I) (M := M) g 4 4 2 F₂
            (slotInsertEndoCc (I := I) (M := M) g 3
              (gInvDiffRaisedEndoField (I := I) g gU)) := by abel
      _ = appCcRS (I := I) (M := M) g 4 4 2 F₂ D₂ := by
        rw [← appCcRS_sub_right]
        congr 1
        dsimp only [D₂, Λ]
        rw [slotInsertEndoCc_sub]
  have htrace₄ :
      pureTrace (I := I) (M := M) g gT 4 -
          pureTrace (I := I) (M := M) g gU 4 =
        appCcRS (I := I) (M := M) g 6 6 4 F₄ D₄ := by
    rw [pureTrace_split (I := I) (M := M) g gT 4,
      pureTrace_split (I := I) (M := M) g gU 4]
    calc
      (appCcRS (I := I) (M := M) g 6 6 4 F₄
            (slotInsertEndoCc (I := I) (M := M) g 5
              (gInvDiffRaisedEndoField (I := I) g gT)) + F₄) -
          (appCcRS (I := I) (M := M) g 6 6 4 F₄
            (slotInsertEndoCc (I := I) (M := M) g 5
              (gInvDiffRaisedEndoField (I := I) g gU)) + F₄) =
        appCcRS (I := I) (M := M) g 6 6 4 F₄
            (slotInsertEndoCc (I := I) (M := M) g 5
              (gInvDiffRaisedEndoField (I := I) g gT)) -
          appCcRS (I := I) (M := M) g 6 6 4 F₄
            (slotInsertEndoCc (I := I) (M := M) g 5
              (gInvDiffRaisedEndoField (I := I) g gU)) := by abel
      _ = appCcRS (I := I) (M := M) g 6 6 4 F₄ D₄ := by
        rw [← appCcRS_sub_right]
        congr 1
        dsimp only [D₄, Λ]
        rw [slotInsertEndoCc_sub]
  have hF₂ : c2JetSq (I := I) (M := M) g F₂ ≤ A₂ ^ 2 := by
    rw [hA₂sq]
  have hF₄ : c2JetSq (I := I) (M := M) g F₄ ≤ A₄ ^ 2 := by
    rw [hA₄sq]
  have hout₂ :
      c2JetSq (I := I) (M := M) g
          (pureTrace (I := I) (M := M) g gT 2 -
            pureTrace (I := I) (M := M) g gU 2) ≤
        (K₂ * N) ^ 2 := by
    rw [htrace₂]
    have h := happ₂ F₂ D₂ A₂ (3 * Cinv * N)
      hA₂ (mul_nonneg (mul_nonneg (by norm_num) hCinv) hN) hF₂ hD₂
    simpa only [c2JetSq, K₂] using
      (show (C₂ * A₂ * (3 * Cinv * N)) ^ 2 =
          (K₂ * N) ^ 2 by
        dsimp only [K₂]
        ring ▸ h)
  have hout₄ :
      c2JetSq (I := I) (M := M) g
          (pureTrace (I := I) (M := M) g gT 4 -
            pureTrace (I := I) (M := M) g gU 4) ≤
        (K₄ * N) ^ 2 := by
    rw [htrace₄]
    have h := happ₄ F₄ D₄ A₄ (9 * Cinv * N)
      hA₄ (mul_nonneg (mul_nonneg (by norm_num) hCinv) hN) hF₄ hD₄
    simpa only [c2JetSq, K₄] using
      (show (C₄ * A₄ * (9 * Cinv * N)) ^ 2 =
          (K₄ * N) ^ 2 by
        dsimp only [K₄]
        ring ▸ h)
  refine ⟨hout₂.trans ?_, hout₄.trans ?_⟩
  · exact pow_le_pow_left₀ (mul_nonneg hK₂ hN)
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hK₄) hN) 2
  · exact pow_le_pow_left₀ (mul_nonneg hK₄ hN)
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hK₂) hN) 2

set_option maxHeartbeats 1600000 in
private theorem pairTrace_h2_lip
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ C : ℝ, 0 < ρ ∧ 0 ≤ C ∧
      ∀ (T U : SmoothCcTensor g 0 2)
        (gT gU : SmoothRiemannianMetric I M),
        (∀ (y : M) (v w : TangentSpace I y),
          gT.inner y v w =
            g.inner y v w +
              ccTensorBilinSymm (I := I) g T y v w) →
        (∀ (y : M) (v w : TangentSpace I y),
          gU.inner y v w =
            g.inner y v w +
              ccTensorBilinSymm (I := I) g U y v w) →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ ≤ ρ →
        c2JetSq (I := I) (M := M) g
            (lieCovPair (I := I) (M := M) g gT -
              lieCovPair (I := I) (M := M) g gU) ≤
          (C * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
            (T - U)‖) ^ 2 := by
  classical
  obtain ⟨ρ, Ct, hρ, hCt, htrace⟩ :=
    trace24_h2_lip (I := I) (M := M) hDim g
  obtain ⟨Ca, hCa, happ⟩ :=
    appRS_h2_h2_h2 (I := I) (M := M) hDim g 6 4 2
  let P₂ : SmoothRiemannianMetric I M → SmoothCcTensor g 4 2 :=
    fun gm => pureTrace (I := I) (M := M) g gm 2
  let P₄ : SmoothRiemannianMetric I M → SmoothCcTensor g 6 4 :=
    fun gm => pureTrace (I := I) (M := M) g gm 4
  let J₂ : ℝ := c2JetSq (I := I) (M := M) g (P₂ g)
  let J₄ : ℝ := c2JetSq (I := I) (M := M) g (P₄ g)
  let Z₂ : ℝ := 2 * ((Ct * ρ) ^ 2 + J₂)
  let Z₄ : ℝ := 2 * ((Ct * ρ) ^ 2 + J₄)
  let B₂ : ℝ := Real.sqrt Z₂
  let B₄ : ℝ := Real.sqrt Z₄
  let K₁ : ℝ := Ca * Ct * B₄
  let K₂ : ℝ := Ca * B₂ * Ct
  let C : ℝ := 2 * (K₁ + K₂)
  have hJ₂ : 0 ≤ J₂ :=
    jet3_nonneg_c2 (I := I) (M := M) g (P₂ g)
  have hJ₄ : 0 ≤ J₄ :=
    jet3_nonneg_c2 (I := I) (M := M) g (P₄ g)
  have hZ₂ : 0 ≤ Z₂ := by
    dsimp only [Z₂]
    exact mul_nonneg (by norm_num)
      (add_nonneg (sq_nonneg (Ct * ρ)) hJ₂)
  have hZ₄ : 0 ≤ Z₄ := by
    dsimp only [Z₄]
    exact mul_nonneg (by norm_num)
      (add_nonneg (sq_nonneg (Ct * ρ)) hJ₄)
  have hB₂ : 0 ≤ B₂ := Real.sqrt_nonneg _
  have hB₄ : 0 ≤ B₄ := Real.sqrt_nonneg _
  have hB₂sq : B₂ ^ 2 = Z₂ := by
    simpa only [B₂] using Real.sq_sqrt hZ₂
  have hB₄sq : B₄ ^ 2 = Z₄ := by
    simpa only [B₄] using Real.sq_sqrt hZ₄
  have hK₁ : 0 ≤ K₁ := by
    dsimp only [K₁]
    exact mul_nonneg (mul_nonneg hCa hCt) hB₄
  have hK₂ : 0 ≤ K₂ := by
    dsimp only [K₂]
    exact mul_nonneg (mul_nonneg hCa hB₂) hCt
  have hC : 0 ≤ C :=
    mul_nonneg (by norm_num) (add_nonneg hK₁ hK₂)
  refine ⟨ρ, C, hρ, hC, ?_⟩
  intro T U gT gU hTtie hUtie hT hU
  let N : ℝ :=
    ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U)‖
  have hN : 0 ≤ N := norm_nonneg _
  have hzero_app : ∀ (y : M) (v w : TangentSpace I y),
      ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2) y v w = 0 := by
    intro y v w
    have hz : (0 : SmoothCcTensor g 0 2) =
        (0 : ℝ) • (0 : SmoothCcTensor g 0 2) :=
      (zero_smul ℝ _).symm
    rw [hz, ccTensorBilinSymm_smul]
    ring
  have hzero_tie : ∀ (y : M) (v w : TangentSpace I y),
      g.inner y v w =
        g.inner y v w +
          ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2) y v w := by
    intro y v w
    rw [hzero_app, add_zero]
  have hcc0 :
      ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
          (0 : SmoothCcTensor g 0 2) = 0 := by
    rw [show (0 : SmoothCcTensor g 0 2) =
      (0 : ℝ) • (0 : SmoothCcTensor g 0 2) by simp,
      ccTensorToHs_smul, zero_smul]
  have hzero_norm :
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
        (0 : SmoothCcTensor g 0 2)‖ ≤ ρ := by
    rw [hcc0, norm_zero]
    exact le_of_lt hρ
  have hbase
      (P : SmoothCcTensor g 0 2)
      (gm : SmoothRiemannianMetric I M)
      (htie : ∀ (y : M) (v w : TangentSpace I y),
        gm.inner y v w =
          g.inner y v w +
            ccTensorBilinSymm (I := I) g P y v w)
      (hP : ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) P‖ ≤ ρ) :
      c2JetSq (I := I) (M := M) g (P₂ gm - P₂ g) ≤
          (Ct * ρ) ^ 2 ∧
        c2JetSq (I := I) (M := M) g (P₄ gm - P₄ g) ≤
          (Ct * ρ) ^ 2 := by
    obtain ⟨h₂, h₄⟩ :=
      htrace P (0 : SmoothCcTensor g 0 2) gm g
        htie hzero_tie hP hzero_norm
    have hmul :
        Ct *
            ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
              (P - 0)‖ ≤
          Ct * ρ := by
      rw [sub_zero]
      exact mul_le_mul_of_nonneg_left hP hCt
    refine ⟨h₂.trans ?_, h₄.trans ?_⟩ <;>
      exact pow_le_pow_left₀
        (mul_nonneg hCt (norm_nonneg _)) hmul 2
  have hend₂
      (P : SmoothCcTensor g 0 2)
      (gm : SmoothRiemannianMetric I M)
      (htie : ∀ (y : M) (v w : TangentSpace I y),
        gm.inner y v w =
          g.inner y v w +
            ccTensorBilinSymm (I := I) g P y v w)
      (hP : ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) P‖ ≤ ρ) :
      c2JetSq (I := I) (M := M) g (P₂ gm) ≤ B₂ ^ 2 := by
    have hb := (hbase P gm htie hP).1
    rw [hB₂sq]
    calc
      c2JetSq (I := I) (M := M) g (P₂ gm) =
          c2JetSq (I := I) (M := M) g
            ((P₂ gm - P₂ g) + P₂ g) := by
        congr 1
        abel
      _ ≤ 2 * (c2JetSq (I := I) (M := M) g (P₂ gm - P₂ g) +
          c2JetSq (I := I) (M := M) g (P₂ g)) :=
        jet3_add_c2 (I := I) (M := M) g _ _
      _ ≤ 2 * ((Ct * ρ) ^ 2 + J₂) :=
        mul_le_mul_of_nonneg_left (add_le_add hb le_rfl)
          (by norm_num)
      _ = Z₂ := rfl
  have hend₄
      (P : SmoothCcTensor g 0 2)
      (gm : SmoothRiemannianMetric I M)
      (htie : ∀ (y : M) (v w : TangentSpace I y),
        gm.inner y v w =
          g.inner y v w +
            ccTensorBilinSymm (I := I) g P y v w)
      (hP : ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) P‖ ≤ ρ) :
      c2JetSq (I := I) (M := M) g (P₄ gm) ≤ B₄ ^ 2 := by
    have hb := (hbase P gm htie hP).2
    rw [hB₄sq]
    calc
      c2JetSq (I := I) (M := M) g (P₄ gm) =
          c2JetSq (I := I) (M := M) g
            ((P₄ gm - P₄ g) + P₄ g) := by
        congr 1
        abel
      _ ≤ 2 * (c2JetSq (I := I) (M := M) g (P₄ gm - P₄ g) +
          c2JetSq (I := I) (M := M) g (P₄ g)) :=
        jet3_add_c2 (I := I) (M := M) g _ _
      _ ≤ 2 * ((Ct * ρ) ^ 2 + J₄) :=
        mul_le_mul_of_nonneg_left (add_le_add hb le_rfl)
          (by norm_num)
      _ = Z₄ := rfl
  obtain ⟨hd₂, hd₄⟩ :=
    htrace T U gT gU hTtie hUtie hT hU
  let Q₁ : SmoothCcTensor g 6 2 :=
    appCcRS (I := I) (M := M) g 6 4 2
      (P₂ gT - P₂ gU) (P₄ gT)
  let Q₂ : SmoothCcTensor g 6 2 :=
    appCcRS (I := I) (M := M) g 6 4 2
      (P₂ gU) (P₄ gT - P₄ gU)
  have hQ₁ :
      c2JetSq (I := I) (M := M) g Q₁ ≤
        (K₁ * N) ^ 2 := by
    have h := happ (P₂ gT - P₂ gU) (P₄ gT)
      (Ct * N) B₄ (mul_nonneg hCt hN) hB₄
      (by simpa only [N] using hd₂)
      (hend₄ T gT hTtie hT)
    simpa only [c2JetSq, Q₁, K₁] using
      (show (Ca * (Ct * N) * B₄) ^ 2 =
          (K₁ * N) ^ 2 by
        dsimp only [K₁]
        ring ▸ h)
  have hQ₂ :
      c2JetSq (I := I) (M := M) g Q₂ ≤
        (K₂ * N) ^ 2 := by
    have h := happ (P₂ gU) (P₄ gT - P₄ gU)
      B₂ (Ct * N) hB₂ (mul_nonneg hCt hN)
      (hend₂ U gU hUtie hU)
      (by simpa only [N] using hd₄)
    simpa only [c2JetSq, Q₂, K₂] using
      (show (Ca * B₂ * (Ct * N)) ^ 2 =
          (K₂ * N) ^ 2 by
        dsimp only [K₂]
        ring ▸ h)
  have hpair :
      lieCovPair (I := I) (M := M) g gT -
          lieCovPair (I := I) (M := M) g gU =
        Q₁ + Q₂ := by
    rw [LowBaseInternal.pairTrace_eq (I := I) (M := M) g gT,
      LowBaseInternal.pairTrace_eq (I := I) (M := M) g gU]
    dsimp only [Q₁, Q₂, P₂, P₄]
    rw [appCcRS_sub_left, appCcRS_sub_right]
    abel
  rw [hpair]
  calc
    c2JetSq (I := I) (M := M) g (Q₁ + Q₂) ≤
        2 * (c2JetSq (I := I) (M := M) g Q₁ +
          c2JetSq (I := I) (M := M) g Q₂) :=
      jet3_add_c2 (I := I) (M := M) g Q₁ Q₂
    _ ≤ 2 * ((K₁ * N) ^ 2 + (K₂ * N) ^ 2) :=
      mul_le_mul_of_nonneg_left (add_le_add hQ₁ hQ₂) (by norm_num)
    _ ≤ (C * N) ^ 2 := by
      dsimp only [C]
      nlinarith [sq_nonneg (K₁ * N - K₂ * N),
        mul_nonneg (mul_nonneg hK₁ hN) (mul_nonneg hK₂ hN)]

set_option maxHeartbeats 1200000 in
private theorem pairTrace_h2_bdd
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ B : ℝ, 0 < ρ ∧ 0 ≤ B ∧
      ∀ (T : SmoothCcTensor g 0 2)
        (gT : SmoothRiemannianMetric I M),
        (∀ (y : M) (v w : TangentSpace I y),
          gT.inner y v w =
            g.inner y v w +
              ccTensorBilinSymm (I := I) g T y v w) →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρ →
        c2JetSq (I := I) (M := M) g
            (lieCovPair (I := I) (M := M) g gT) ≤ B ^ 2 := by
  obtain ⟨ρ, C, hρ, hC, hlip⟩ :=
    pairTrace_h2_lip (I := I) (M := M) hDim g
  let P : SmoothRiemannianMetric I M → SmoothCcTensor g 6 2 :=
    fun gm => lieCovPair (I := I) (M := M) g gm
  let J : ℝ := c2JetSq (I := I) (M := M) g (P g)
  let Z : ℝ := 2 * ((C * ρ) ^ 2 + J)
  let B : ℝ := Real.sqrt Z
  have hJ : 0 ≤ J := jet3_nonneg_c2 (I := I) (M := M) g (P g)
  have hZ : 0 ≤ Z := by
    dsimp only [Z]
    exact mul_nonneg (by norm_num)
      (add_nonneg (sq_nonneg (C * ρ)) hJ)
  have hB : 0 ≤ B := Real.sqrt_nonneg _
  have hBsq : B ^ 2 = Z := by
    simpa only [B] using Real.sq_sqrt hZ
  refine ⟨ρ, B, hρ, hB, ?_⟩
  intro T gT hTtie hT
  have hzero_app : ∀ (y : M) (v w : TangentSpace I y),
      ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2) y v w = 0 := by
    intro y v w
    have hz : (0 : SmoothCcTensor g 0 2) =
        (0 : ℝ) • (0 : SmoothCcTensor g 0 2) :=
      (zero_smul ℝ _).symm
    rw [hz, ccTensorBilinSymm_smul]
    ring
  have hzero_tie : ∀ (y : M) (v w : TangentSpace I y),
      g.inner y v w =
        g.inner y v w +
          ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2) y v w := by
    intro y v w
    rw [hzero_app, add_zero]
  have hcc0 :
      ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
          (0 : SmoothCcTensor g 0 2) = 0 := by
    rw [show (0 : SmoothCcTensor g 0 2) =
      (0 : ℝ) • (0 : SmoothCcTensor g 0 2) by simp,
      ccTensorToHs_smul, zero_smul]
  have hzero_norm :
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
        (0 : SmoothCcTensor g 0 2)‖ ≤ ρ := by
    rw [hcc0, norm_zero]
    exact le_of_lt hρ
  have hdiff :
      c2JetSq (I := I) (M := M) g (P gT - P g) ≤
        (C * ρ) ^ 2 := by
    have hraw := hlip T (0 : SmoothCcTensor g 0 2) gT g
      hTtie hzero_tie hT hzero_norm
    have hmul :
        C * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
              (T - 0)‖ ≤ C * ρ := by
      rw [sub_zero]
      exact mul_le_mul_of_nonneg_left hT hC
    exact hraw.trans
      (pow_le_pow_left₀
        (mul_nonneg hC (norm_nonneg _)) hmul 2)
  rw [hBsq]
  calc
    c2JetSq (I := I) (M := M) g (P gT) =
        c2JetSq (I := I) (M := M) g ((P gT - P g) + P g) := by
      congr 1
      abel
    _ ≤ 2 * (c2JetSq (I := I) (M := M) g (P gT - P g) +
        c2JetSq (I := I) (M := M) g (P g)) :=
      jet3_add_c2 (I := I) (M := M) g _ _
    _ ≤ 2 * ((C * ρ) ^ 2 + J) :=
      mul_le_mul_of_nonneg_left (add_le_add hdiff le_rfl) (by norm_num)
    _ = Z := rfl

set_option maxHeartbeats 1800000 in
private theorem curvMono_h2_lip
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ C : ℝ, 0 < ρ ∧ 0 ≤ C ∧
      ∀ (T U : SmoothCcTensor g 0 2)
        (gT gU : SmoothRiemannianMetric I M),
        (∀ (y : M) (v w : TangentSpace I y),
          gT.inner y v w =
            g.inner y v w +
              ccTensorBilinSymm (I := I) g T y v w) →
        (∀ (y : M) (v w : TangentSpace I y),
          gU.inner y v w =
            g.inner y v w +
              ccTensorBilinSymm (I := I) g U y v w) →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ ≤ ρ →
        ∀ (S R : SmoothCcTensor g 0 2)
          (σ : Equiv.Perm (Fin 4)) (A D : ℝ),
          0 ≤ A → 0 ≤ D →
          c2JetSq (I := I) (M := M) g S ≤ A ^ 2 →
          c2JetSq (I := I) (M := M) g (S - R) ≤ D ^ 2 →
          c2JetSq (I := I) (M := M) g
              (curvatureRefoldMonomialCoeffField
                  (I := I) (M := M) g gT
                  (ccTensorUnitValueSection (I := I) (M := M) g S)
                  (ccTensorUnitValueSection_contMDiff
                    (I := I) (M := M) g S) σ -
                curvatureRefoldMonomialCoeffField
                  (I := I) (M := M) g gU
                  (ccTensorUnitValueSection (I := I) (M := M) g R)
                  (ccTensorUnitValueSection_contMDiff
                    (I := I) (M := M) g R) σ) ≤
            (C * (A *
              ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
                (T - U)‖ + D)) ^ 2 := by
  obtain ⟨ρ₁, Cp, hρ₁, hCp, hpair⟩ :=
    pairTrace_h2_lip (I := I) (M := M) hDim g
  obtain ⟨ρ₂, Bp, hρ₂, hBp, hbpair⟩ :=
    pairTrace_h2_bdd (I := I) (M := M) hDim g
  obtain ⟨Ca, hCa, happ⟩ :=
    appRS_h2_h2_h2 (I := I) (M := M) hDim g 4 6 2
  let ρ : ℝ := min ρ₁ ρ₂
  let K₁ : ℝ := 9 * Ca * Cp
  let K₂ : ℝ := 9 * Ca * Bp
  let C : ℝ := 2 * (K₁ + K₂)
  have hρ : 0 < ρ := lt_min hρ₁ hρ₂
  have hK₁ : 0 ≤ K₁ :=
    mul_nonneg (mul_nonneg (by norm_num) hCa) hCp
  have hK₂ : 0 ≤ K₂ :=
    mul_nonneg (mul_nonneg (by norm_num) hCa) hBp
  have hC : 0 ≤ C :=
    mul_nonneg (by norm_num) (add_nonneg hK₁ hK₂)
  refine ⟨ρ, C, hρ, hC, ?_⟩
  intro T U gT gU hTtie hUtie hT hU S R σ A D hA hD hS hSR
  let N : ℝ :=
    ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U)‖
  let P : SmoothRiemannianMetric I M → SmoothCcTensor g 6 2 :=
    fun gm => lieCovPair (I := I) (M := M) g gm
  let X : SmoothCcTensor g 0 2 → SmoothCcTensor g 4 6 :=
    fun W => monoExtC2 (I := I) (M := M) g σ W
  let Q₁ : SmoothCcTensor g 4 2 :=
    appCcRS (I := I) (M := M) g 4 6 2
      (P gT - P gU) (X S)
  let Q₂ : SmoothCcTensor g 4 2 :=
    appCcRS (I := I) (M := M) g 4 6 2
      (P gU) (X S - X R)
  have hN : 0 ≤ N := norm_nonneg _
  have hT₁ :
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρ₁ :=
    hT.trans (min_le_left _ _)
  have hU₁ :
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ ≤ ρ₁ :=
    hU.trans (min_le_left _ _)
  have hU₂ :
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ ≤ ρ₂ :=
    hU.trans (min_le_right _ _)
  have hPdiff :
      c2JetSq (I := I) (M := M) g (P gT - P gU) ≤
        (Cp * N) ^ 2 := by
    simpa only [P, N] using
      hpair T U gT gU hTtie hUtie hT₁ hU₁
  have hPend :
      c2JetSq (I := I) (M := M) g (P gU) ≤ Bp ^ 2 := by
    simpa only [P] using hbpair U gU hUtie hU₂
  have hXS :
      c2JetSq (I := I) (M := M) g (X S) ≤ (9 * A) ^ 2 := by
    calc
      c2JetSq (I := I) (M := M) g (X S) ≤
          (Module.finrank ℝ E : ℝ) ^ 4 *
            c2JetSq (I := I) (M := M) g S := by
        simpa only [X] using
          monoExt_jet_c2 (I := I) (M := M) g σ S
      _ ≤ (Module.finrank ℝ E : ℝ) ^ 4 * A ^ 2 :=
        mul_le_mul_of_nonneg_left hS (pow_nonneg (Nat.cast_nonneg _) 4)
      _ = (9 * A) ^ 2 := by
        rw [hDim]
        norm_num
        ring
  have hXdiff :
      c2JetSq (I := I) (M := M) g (X S - X R) ≤
        (9 * D) ^ 2 := by
    rw [← monoExt_sub_c2 (I := I) (M := M) g σ S R]
    calc
      c2JetSq (I := I) (M := M) g
          (monoExtC2 (I := I) (M := M) g σ (S - R)) ≤
          (Module.finrank ℝ E : ℝ) ^ 4 *
            c2JetSq (I := I) (M := M) g (S - R) :=
        monoExt_jet_c2 (I := I) (M := M) g σ (S - R)
      _ ≤ (Module.finrank ℝ E : ℝ) ^ 4 * D ^ 2 :=
        mul_le_mul_of_nonneg_left hSR (pow_nonneg (Nat.cast_nonneg _) 4)
      _ = (9 * D) ^ 2 := by
        rw [hDim]
        norm_num
        ring
  have hQ₁ :
      c2JetSq (I := I) (M := M) g Q₁ ≤
        (K₁ * (A * N)) ^ 2 := by
    have h := happ (P gT - P gU) (X S)
      (Cp * N) (9 * A)
      (mul_nonneg hCp hN) (mul_nonneg (by norm_num) hA)
      hPdiff hXS
    simpa only [c2JetSq, Q₁] using
      (show (Ca * (Cp * N) * (9 * A)) ^ 2 =
          (K₁ * (A * N)) ^ 2 by
        dsimp only [K₁]
        ring ▸ h)
  have hQ₂ :
      c2JetSq (I := I) (M := M) g Q₂ ≤
        (K₂ * D) ^ 2 := by
    have h := happ (P gU) (X S - X R)
      Bp (9 * D) hBp (mul_nonneg (by norm_num) hD)
      hPend hXdiff
    simpa only [c2JetSq, Q₂] using
      (show (Ca * Bp * (9 * D)) ^ 2 =
          (K₂ * D) ^ 2 by
        dsimp only [K₂]
        ring ▸ h)
  have hmono :
      curvatureRefoldMonomialCoeffField
          (I := I) (M := M) g gT
          (ccTensorUnitValueSection (I := I) (M := M) g S)
          (ccTensorUnitValueSection_contMDiff (I := I) (M := M) g S) σ -
        curvatureRefoldMonomialCoeffField
          (I := I) (M := M) g gU
          (ccTensorUnitValueSection (I := I) (M := M) g R)
          (ccTensorUnitValueSection_contMDiff (I := I) (M := M) g R) σ =
        Q₁ + Q₂ := by
    rw [LowBaseInternal.curvMono_eq (I := I) (M := M) g gT S σ,
      LowBaseInternal.curvMono_eq (I := I) (M := M) g gU R σ]
    change
      appCcRS (I := I) (M := M) g 4 6 2 (P gT) (X S) -
          appCcRS (I := I) (M := M) g 4 6 2 (P gU) (X R) =
        Q₁ + Q₂
    dsimp only [Q₁, Q₂]
    rw [appCcRS_sub_left, appCcRS_sub_right]
    abel
  rw [hmono]
  calc
    c2JetSq (I := I) (M := M) g (Q₁ + Q₂) ≤
        2 * (c2JetSq (I := I) (M := M) g Q₁ +
          c2JetSq (I := I) (M := M) g Q₂) :=
      jet3_add_c2 (I := I) (M := M) g Q₁ Q₂
    _ ≤ 2 * ((K₁ * (A * N)) ^ 2 + (K₂ * D) ^ 2) :=
      mul_le_mul_of_nonneg_left (add_le_add hQ₁ hQ₂) (by norm_num)
    _ ≤ (C * (A * N + D)) ^ 2 := by
      have hx : 0 ≤ A * N := mul_nonneg hA hN
      have hxy : 0 ≤ A * N + D := add_nonneg hx hD
      have hK : 0 ≤ K₁ + K₂ := add_nonneg hK₁ hK₂
      have h₁ :
          K₁ * (A * N) ≤ (K₁ + K₂) * (A * N + D) := by
        calc
          K₁ * (A * N) ≤ (K₁ + K₂) * (A * N) :=
            mul_le_mul_of_nonneg_right
              (le_add_of_nonneg_right hK₂) hx
          _ ≤ (K₁ + K₂) * (A * N + D) :=
            mul_le_mul_of_nonneg_left
              (le_add_of_nonneg_right hD) hK
      have h₂ :
          K₂ * D ≤ (K₁ + K₂) * (A * N + D) := by
        calc
          K₂ * D ≤ (K₁ + K₂) * D :=
            mul_le_mul_of_nonneg_right
              (le_add_of_nonneg_left hK₁) hD
          _ ≤ (K₁ + K₂) * (A * N + D) := by
            nlinarith [mul_nonneg hK hx]
      have hs₁ := pow_le_pow_left₀
        (mul_nonneg hK₁ hx) h₁ 2
      have hs₂ := pow_le_pow_left₀
        (mul_nonneg hK₂ hD) h₂ 2
      dsimp only [C]
      calc
        2 * ((K₁ * (A * N)) ^ 2 + (K₂ * D) ^ 2) ≤
            2 * (((K₁ + K₂) * (A * N + D)) ^ 2 +
              ((K₁ + K₂) * (A * N + D)) ^ 2) :=
          mul_le_mul_of_nonneg_left (add_le_add hs₁ hs₂) (by norm_num)
        _ = (2 * (K₁ + K₂) * (A * N + D)) ^ 2 := by ring

set_option maxHeartbeats 1800000 in
/-- A fixed-background curvature-refold monomial is bounded on intrinsic
`H²` coefficient differences. -/
theorem curv_pair_h2
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (S R : SmoothCcTensor g 0 2) (σ : Equiv.Perm (Fin 4))
        (D : ℝ), 0 ≤ D →
        lowJetSq (I := I) (M := M) g 2 (S - R) ≤ D ^ 2 →
        lowJetSq (I := I) (M := M) g 2
            (curvatureRefoldMonomialCoeffField
                (I := I) (M := M) g g
                (ccTensorUnitValueSection (I := I) (M := M) g S)
                (ccTensorUnitValueSection_contMDiff
                  (I := I) (M := M) g S) σ -
              curvatureRefoldMonomialCoeffField
                (I := I) (M := M) g g
                (ccTensorUnitValueSection (I := I) (M := M) g R)
                (ccTensorUnitValueSection_contMDiff
                  (I := I) (M := M) g R) σ) ≤
          (C * D) ^ 2 := by
  obtain ⟨ρ, C, hρ, hC, hlip⟩ :=
    curvMono_h2_lip (I := I) (M := M) hDim g
  refine ⟨C, hC, ?_⟩
  intro S R σ D hD hSR
  change c2JetSq (I := I) (M := M) g (S - R) ≤ D ^ 2 at hSR
  change c2JetSq (I := I) (M := M) g
      (curvatureRefoldMonomialCoeffField
          (I := I) (M := M) g g
          (ccTensorUnitValueSection (I := I) (M := M) g S)
          (ccTensorUnitValueSection_contMDiff
            (I := I) (M := M) g S) σ -
        curvatureRefoldMonomialCoeffField
          (I := I) (M := M) g g
          (ccTensorUnitValueSection (I := I) (M := M) g R)
          (ccTensorUnitValueSection_contMDiff
            (I := I) (M := M) g R) σ) ≤ (C * D) ^ 2
  let A : ℝ := Real.sqrt (c2JetSq (I := I) (M := M) g S)
  have hA : 0 ≤ A := Real.sqrt_nonneg _
  have hS : c2JetSq (I := I) (M := M) g S ≤ A ^ 2 := by
    exact (Real.sq_sqrt
      (jet3_nonneg_c2 (I := I) (M := M) g S)).symm.le
  have hzero_app : ∀ (y : M) (v w : TangentSpace I y),
      ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2) y v w = 0 := by
    intro y v w
    have hz : (0 : SmoothCcTensor g 0 2) =
        (0 : ℝ) • (0 : SmoothCcTensor g 0 2) :=
      (zero_smul ℝ _).symm
    rw [hz, ccTensorBilinSymm_smul]
    ring
  have hzero_tie : ∀ (y : M) (v w : TangentSpace I y),
      g.inner y v w =
        g.inner y v w + ccTensorBilinSymm (I := I) g
          (0 : SmoothCcTensor g 0 2) y v w := by
    intro y v w
    rw [hzero_app, add_zero]
  have hcc0 :
      ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
          (0 : SmoothCcTensor g 0 2) = 0 := by
    rw [show (0 : SmoothCcTensor g 0 2) =
      (0 : ℝ) • (0 : SmoothCcTensor g 0 2) by simp,
      ccTensorToHs_smul, zero_smul]
  have hzero_norm :
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
        (0 : SmoothCcTensor g 0 2)‖ ≤ ρ := by
    rw [hcc0, norm_zero]
    exact le_of_lt hρ
  have hraw := hlip
    (0 : SmoothCcTensor g 0 2) (0 : SmoothCcTensor g 0 2) g g
    hzero_tie hzero_tie hzero_norm hzero_norm S R σ A D hA hD hS hSR
  simpa only [sub_self, hcc0, norm_zero, mul_zero, zero_add] using hraw

set_option maxHeartbeats 2400000 in
private theorem lieRefold_pair_lip
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ C : ℝ, 0 < ρ ∧ 0 ≤ C ∧
      ∀ (T U : SmoothCcTensor g 0 2) {δ : ℝ},
        (hδlt : δ < 1) →
        (hTδ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ) →
        (hUδ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g U) δ) →
        (hZδ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ) →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ ≤ ρ →
        ∀ {s : ℝ}, s ∈ Set.Icc (0 : ℝ) 1 →
          c2JetSq (I := I) (M := M) g
              (lieRefold2 (I := I) (M := M) g T hTδ hZδ s -
                lieRefold2 (I := I) (M := M) g U hUδ hZδ s) ≤
            (C * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
              (T - U)‖) ^ 2 := by
  obtain ⟨ρm, Cm, hρm, hCm, hmono⟩ :=
    curvMono_h2_lip (I := I) (M := M) hDim g
  obtain ⟨Chs, hChs, hhs⟩ :=
    hs2_low2 (I := I) (M := M) g 2
  let ρ : ℝ := min ρm 1
  let K : ℝ := Cm * Chs * (ρ + 1)
  let C : ℝ := 4 * K
  have hρ : 0 < ρ := lt_min hρm (by norm_num)
  have hρ0 : 0 ≤ ρ := le_of_lt hρ
  have hK : 0 ≤ K :=
    mul_nonneg (mul_nonneg hCm hChs)
      (add_nonneg hρ0 (by norm_num))
  have hC : 0 ≤ C := mul_nonneg (by norm_num) hK
  refine ⟨ρ, C, hρ, hC, ?_⟩
  intro T U δ hδlt hTδ hUδ hZδ hT hU s hs
  let N : ℝ :=
    ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U)‖
  let P : SmoothCcTensor g 0 2 :=
    convexPerturbation (I := I) g T 0 s
  let Q : SmoothCcTensor g 0 2 :=
    convexPerturbation (I := I) g U 0 s
  let gmT : SmoothRiemannianMetric I M :=
    realizedFam (I := I) g T 0 hTδ hZδ s
  let gmU : SmoothRiemannianMetric I M :=
    realizedFam (I := I) g U 0 hUδ hZδ s
  have hN : 0 ≤ N := norm_nonneg _
  have hsabs : ‖s‖ ≤ (1 : ℝ) := by
    rw [Real.norm_eq_abs, abs_of_nonneg hs.1]
    exact hs.2
  have hs_mem : s ∈ realizedSmallSet (δ := δ) (δ' := δ) :=
    Icc_subset_realizedSmallSet hδlt hδlt hs
  have hP_eq : P = s • T := by
    simp only [P, convexPerturbation, smul_zero, zero_add]
  have hQ_eq : Q = s • U := by
    simp only [Q, convexPerturbation, smul_zero, zero_add]
  have hPtie : ∀ (x : M) (v w : TangentSpace I x),
      gmT.inner x v w =
        g.inner x v w + ccTensorBilinSymm (I := I) g P x v w := by
    intro x v w
    exact realizedFam_inner_of_mem
      (I := I) g T 0 hTδ hZδ hs_mem x v w
  have hQtie : ∀ (x : M) (v w : TangentSpace I x),
      gmU.inner x v w =
        g.inner x v w + ccTensorBilinSymm (I := I) g Q x v w := by
    intro x v w
    exact realizedFam_inner_of_mem
      (I := I) g U 0 hUδ hZδ hs_mem x v w
  have hPnorm :
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) P‖ ≤ ρm := by
    rw [hP_eq, ccTensorToHs_smul, norm_smul]
    calc
      ‖s‖ *
          ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤
          1 * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ :=
        mul_le_mul_of_nonneg_right hsabs (norm_nonneg _)
      _ ≤ ρ := by simpa using hT
      _ ≤ ρm := min_le_left _ _
  have hQnorm :
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) Q‖ ≤ ρm := by
    rw [hQ_eq, ccTensorToHs_smul, norm_smul]
    calc
      ‖s‖ *
          ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ ≤
          1 * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ :=
        mul_le_mul_of_nonneg_right hsabs (norm_nonneg _)
      _ ≤ ρ := by simpa using hU
      _ ≤ ρm := min_le_left _ _
  have hPQ :
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (P - Q)‖ ≤ N := by
    have heq : P - Q = s • (T - U) := by
      rw [hP_eq, hQ_eq]
      module
    rw [heq, ccTensorToHs_smul, norm_smul]
    exact (mul_le_mul_of_nonneg_right hsabs hN).trans (by simp)
  let A : ℝ := Chs * ρ
  let D : ℝ := Chs * N
  have hA : 0 ≤ A := mul_nonneg hChs hρ0
  have hD : 0 ≤ D := mul_nonneg hChs hN
  have hsymmT :
      c2JetSq (I := I) (M := M) g
          (symmS (I := I) (M := M) g T) ≤ A ^ 2 := by
    calc
      c2JetSq (I := I) (M := M) g
          (symmS (I := I) (M := M) g T) ≤
          c2JetSq (I := I) (M := M) g T :=
        symm_jet_c2 (I := I) (M := M) g T
      _ ≤ (Chs *
          ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖) ^ 2 := by
        simpa only [c2JetSq] using hhs T
      _ ≤ (Chs * ρ) ^ 2 := by
        exact pow_le_pow_left₀
          (mul_nonneg hChs (norm_nonneg _))
          (mul_le_mul_of_nonneg_left hT hChs) 2
      _ = A ^ 2 := rfl
  have hsymmDiff :
      c2JetSq (I := I) (M := M) g
          (symmS (I := I) (M := M) g T -
            symmS (I := I) (M := M) g U) ≤ D ^ 2 := by
    rw [← symmS_sub_c2 (I := I) (M := M) g T U]
    calc
      c2JetSq (I := I) (M := M) g
          (symmS (I := I) (M := M) g (T - U)) ≤
          c2JetSq (I := I) (M := M) g (T - U) :=
        symm_jet_c2 (I := I) (M := M) g (T - U)
      _ ≤ (Chs * N) ^ 2 := by
        simpa only [c2JetSq, N] using hhs (T - U)
      _ = D ^ 2 := rfl
  let V : Fin 3 → SmoothCcTensor g 4 2 := fun i =>
    curvatureRefoldMonomialCoeffField (I := I) (M := M) g gmT
        (ccTensorUnitValueSection (I := I) (M := M) g
          (symmS (I := I) (M := M) g T))
        (ccTensorUnitValueSection_contMDiff (I := I) (M := M) g
          (symmS (I := I) (M := M) g T)) (lieRefoldQ i) -
      curvatureRefoldMonomialCoeffField (I := I) (M := M) g gmU
        (ccTensorUnitValueSection (I := I) (M := M) g
          (symmS (I := I) (M := M) g U))
        (ccTensorUnitValueSection_contMDiff (I := I) (M := M) g
          (symmS (I := I) (M := M) g U)) (lieRefoldQ i)
  let W : Fin 3 → SmoothCcTensor g 4 2 := fun i =>
    lieRefoldEps i • V i
  have hV (i : Fin 3) :
      c2JetSq (I := I) (M := M) g (V i) ≤ (K * N) ^ 2 := by
    have hraw := hmono P Q gmT gmU hPtie hQtie hPnorm hQnorm
      (symmS (I := I) (M := M) g T)
      (symmS (I := I) (M := M) g U)
      (lieRefoldQ i) A D hA hD hsymmT hsymmDiff
    have hinside :
        A *
            ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (P - Q)‖ +
              D ≤
          Chs * (ρ + 1) * N := by
      calc
        A *
              ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (P - Q)‖ +
            D ≤ A * N + D :=
          add_le_add (mul_le_mul_of_nonneg_left hPQ hA) le_rfl
        _ = Chs * (ρ + 1) * N := by
          dsimp only [A, D]
          ring
    have hmul :
        Cm * (A *
              ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (P - Q)‖ +
            D) ≤
          Cm * (Chs * (ρ + 1) * N) :=
      mul_le_mul_of_nonneg_left hinside hCm
    have hout := hraw.trans
      (pow_le_pow_left₀
        (mul_nonneg hCm (add_nonneg
          (mul_nonneg hA (norm_nonneg _)) hD)) hmul 2)
    simpa only [V] using
      (show (Cm * (Chs * (ρ + 1) * N)) ^ 2 =
          (K * N) ^ 2 by
        dsimp only [K]
        ring ▸ hout)
  have hW (i : Fin 3) :
      c2JetSq (I := I) (M := M) g (W i) ≤ (K * N) ^ 2 := by
    dsimp only [W]
    rw [jet3_smul_c2]
    have heps : lieRefoldEps i ^ 2 = (1 : ℝ) := by
      fin_cases i <;> norm_num [lieRefoldEps]
    rw [heps, one_mul]
    exact hV i
  have hrefold :
      lieRefold2 (I := I) (M := M) g T hTδ hZδ s -
          lieRefold2 (I := I) (M := M) g U hUδ hZδ s =
        s • (W 0 + W 1 + W 2) := by
    rw [lieRefold2, lieRefold2,
      deTurckLieCovDerivRefoldC2Family_eq_symmS_weight,
      deTurckLieCovDerivRefoldC2Family_eq_symmS_weight]
    simp only [Fin.sum_univ_three, W, V, gmT, gmU]
    module
  have h01 :
      c2JetSq (I := I) (M := M) g (W 0 + W 1) ≤
        4 * (K * N) ^ 2 := by
    calc
      c2JetSq (I := I) (M := M) g (W 0 + W 1) ≤
          2 * (c2JetSq (I := I) (M := M) g (W 0) +
            c2JetSq (I := I) (M := M) g (W 1)) :=
        jet3_add_c2 (I := I) (M := M) g (W 0) (W 1)
      _ ≤ 4 * (K * N) ^ 2 := by
        nlinarith [hW 0, hW 1]
  have hsum :
      c2JetSq (I := I) (M := M) g (W 0 + W 1 + W 2) ≤
        10 * (K * N) ^ 2 := by
    calc
      c2JetSq (I := I) (M := M) g (W 0 + W 1 + W 2) ≤
          2 * (c2JetSq (I := I) (M := M) g (W 0 + W 1) +
            c2JetSq (I := I) (M := M) g (W 2)) :=
        jet3_add_c2 (I := I) (M := M) g (W 0 + W 1) (W 2)
      _ ≤ 10 * (K * N) ^ 2 := by
        nlinarith [h01, hW 2]
  rw [hrefold, jet3_smul_c2]
  have hs2 : s ^ 2 ≤ (1 : ℝ) := by
    nlinarith [hs.1, hs.2]
  calc
    s ^ 2 * c2JetSq (I := I) (M := M) g (W 0 + W 1 + W 2) ≤
        c2JetSq (I := I) (M := M) g (W 0 + W 1 + W 2) :=
      mul_le_of_le_one_left
        (jet3_nonneg_c2 (I := I) (M := M) g (W 0 + W 1 + W 2)) hs2
    _ ≤ 10 * (K * N) ^ 2 := hsum
    _ ≤ (C * N) ^ 2 := by
      dsimp only [C]
      nlinarith [sq_nonneg (K * N)]

set_option maxHeartbeats 1200000 in
private theorem fullSlot_h2_bdd
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ B : ℝ, 0 < ρ ∧ 0 ≤ B ∧
      ∀ (T : SmoothCcTensor g 0 2)
        (gT : SmoothRiemannianMetric I M),
        (∀ (y : M) (v w : TangentSpace I y),
          gT.inner y v w =
            g.inner y v w +
              ccTensorBilinSymm (I := I) g T y v w) →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρ →
        c2JetSq (I := I) (M := M) g
            (fullSlot2 (I := I) (M := M) g gT) ≤ B ^ 2 := by
  obtain ⟨ρ, C, hρ, hC, hlip⟩ :=
    invCoeff_h2_lip (I := I) (M := M) hDim g
  let F : SmoothRiemannianMetric I M → SmoothCcTensor g 2 2 :=
    fun gm => fullSlot2 (I := I) (M := M) g gm
  let J : ℝ := c2JetSq (I := I) (M := M) g (F g)
  let Z : ℝ := 2 * ((C * ρ) ^ 2 + J)
  let B : ℝ := Real.sqrt Z
  have hJ : 0 ≤ J := jet3_nonneg_c2 (I := I) (M := M) g (F g)
  have hZ : 0 ≤ Z := by
    dsimp only [Z]
    exact mul_nonneg (by norm_num)
      (add_nonneg (sq_nonneg (C * ρ)) hJ)
  have hB : 0 ≤ B := Real.sqrt_nonneg _
  have hBsq : B ^ 2 = Z := by
    simpa only [B] using Real.sq_sqrt hZ
  refine ⟨ρ, B, hρ, hB, ?_⟩
  intro T gT hTtie hT
  have hzero_app : ∀ (y : M) (v w : TangentSpace I y),
      ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2) y v w = 0 := by
    intro y v w
    have hz : (0 : SmoothCcTensor g 0 2) =
        (0 : ℝ) • (0 : SmoothCcTensor g 0 2) :=
      (zero_smul ℝ _).symm
    rw [hz, ccTensorBilinSymm_smul]
    ring
  have hzero_tie : ∀ (y : M) (v w : TangentSpace I y),
      g.inner y v w =
        g.inner y v w +
          ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2) y v w := by
    intro y v w
    rw [hzero_app, add_zero]
  have hcc0 :
      ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
          (0 : SmoothCcTensor g 0 2) = 0 := by
    rw [show (0 : SmoothCcTensor g 0 2) =
      (0 : ℝ) • (0 : SmoothCcTensor g 0 2) by simp,
      ccTensorToHs_smul, zero_smul]
  have hzero_norm :
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
        (0 : SmoothCcTensor g 0 2)‖ ≤ ρ := by
    rw [hcc0, norm_zero]
    exact le_of_lt hρ
  have hraw := (hlip T (0 : SmoothCcTensor g 0 2) gT g
    hTtie hzero_tie hT hzero_norm).2
  have hmul :
      C * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
            (T - 0)‖ ≤ C * ρ := by
    rw [sub_zero]
    exact mul_le_mul_of_nonneg_left hT hC
  have hdiff :
      c2JetSq (I := I) (M := M) g (F gT - F g) ≤
        (C * ρ) ^ 2 := by
    have hd0 : gInvDiffSlotCoeff (I := I) g g = 0 := by
      have hself := fullSlot2_decomp (I := I) (M := M) g g
      have h :
          gInvDiffSlotCoeff (I := I) g g +
              fullSlot2 (I := I) (M := M) g g =
            0 + fullSlot2 (I := I) (M := M) g g := by
        simpa only [zero_add] using hself.symm
      exact add_right_cancel h
    have heq :
        F gT - F g =
          gInvDiffSlotCoeff (I := I) g gT -
            gInvDiffSlotCoeff (I := I) g g := by
      dsimp only [F]
      rw [fullSlot2_decomp (I := I) (M := M) g gT, hd0]
      module
    rw [heq]
    exact hraw.trans
      (pow_le_pow_left₀
        (mul_nonneg hC (norm_nonneg _)) hmul 2)
  rw [hBsq]
  calc
    c2JetSq (I := I) (M := M) g (F gT) =
        c2JetSq (I := I) (M := M) g ((F gT - F g) + F g) := by
      congr 1
      abel
    _ ≤ 2 * (c2JetSq (I := I) (M := M) g (F gT - F g) +
        c2JetSq (I := I) (M := M) g (F g)) :=
      jet3_add_c2 (I := I) (M := M) g _ _
    _ ≤ 2 * ((C * ρ) ^ 2 + J) :=
      mul_le_mul_of_nonneg_left (add_le_add hdiff le_rfl) (by norm_num)
    _ = Z := rfl

set_option maxHeartbeats 1800000 in
private theorem daWeight_pair_lip
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ C B : ℝ, 0 < ρ ∧ 0 ≤ C ∧ 0 ≤ B ∧
      ∀ (T U : SmoothCcTensor g 0 2)
        (gT gU : SmoothRiemannianMetric I M),
        (∀ (y : M) (v w : TangentSpace I y),
          gT.inner y v w =
            g.inner y v w +
              ccTensorBilinSymm (I := I) g T y v w) →
        (∀ (y : M) (v w : TangentSpace I y),
          gU.inner y v w =
            g.inner y v w +
              ccTensorBilinSymm (I := I) g U y v w) →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ ≤ ρ →
        c2JetSq (I := I) (M := M) g
            (LowBaseInternal.daWeight (I := I) (M := M) g gT T -
              LowBaseInternal.daWeight (I := I) (M := M) g gU U) ≤
          (C * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
            (T - U)‖) ^ 2 ∧
        c2JetSq (I := I) (M := M) g
            (LowBaseInternal.daWeight (I := I) (M := M) g gT T) ≤
          B ^ 2 := by
  obtain ⟨ρ₁, Ci, hρ₁, hCi, hinv⟩ :=
    invCoeff_h2_lip (I := I) (M := M) hDim g
  obtain ⟨ρ₂, Bf, hρ₂, hBf, hfull⟩ :=
    fullSlot_h2_bdd (I := I) (M := M) hDim g
  obtain ⟨Ca, hCa, happ⟩ :=
    appCc_h2_h2_h2 (I := I) (M := M) hDim g 2 2
  obtain ⟨Chs, hChs, hhs⟩ :=
    hs2_low2 (I := I) (M := M) g 2
  let ρ : ℝ := min ρ₁ ρ₂
  let K₁ : ℝ := Ca * Ci * (Chs * ρ)
  let K₂ : ℝ := Ca * Bf * Chs
  let C : ℝ := 2 * (K₁ + K₂)
  let B : ℝ := Ca * Bf * (Chs * ρ)
  have hρ : 0 < ρ := lt_min hρ₁ hρ₂
  have hρ0 : 0 ≤ ρ := le_of_lt hρ
  have hK₁ : 0 ≤ K₁ :=
    mul_nonneg (mul_nonneg hCa hCi) (mul_nonneg hChs hρ0)
  have hK₂ : 0 ≤ K₂ :=
    mul_nonneg (mul_nonneg hCa hBf) hChs
  have hC : 0 ≤ C :=
    mul_nonneg (by norm_num) (add_nonneg hK₁ hK₂)
  have hB : 0 ≤ B :=
    mul_nonneg (mul_nonneg hCa hBf) (mul_nonneg hChs hρ0)
  refine ⟨ρ, C, B, hρ, hC, hB, ?_⟩
  intro T U gT gU hTtie hUtie hT hU
  let N : ℝ :=
    ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U)‖
  let F : SmoothRiemannianMetric I M → SmoothCcTensor g 2 2 :=
    fun gm => fullSlot2 (I := I) (M := M) g gm
  let Q₁ : SmoothCcTensor g 0 2 :=
    appCc (I := I) (M := M) g 2 2 (F gT - F gU) T
  let Q₂ : SmoothCcTensor g 0 2 :=
    appCc (I := I) (M := M) g 2 2 (F gU) (T - U)
  have hN : 0 ≤ N := norm_nonneg _
  have hT₁ :
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρ₁ :=
    hT.trans (min_le_left _ _)
  have hU₁ :
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ ≤ ρ₁ :=
    hU.trans (min_le_left _ _)
  have hT₂ :
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρ₂ :=
    hT.trans (min_le_right _ _)
  have hU₂ :
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ ≤ ρ₂ :=
    hU.trans (min_le_right _ _)
  have hFdiff :
      c2JetSq (I := I) (M := M) g (F gT - F gU) ≤
        (Ci * N) ^ 2 := by
    have hraw := (hinv T U gT gU hTtie hUtie hT₁ hU₁).2
    have heq :
        F gT - F gU =
          gInvDiffSlotCoeff (I := I) g gT -
            gInvDiffSlotCoeff (I := I) g gU := by
      dsimp only [F]
      have hdecT := fullSlot2_decomp (I := I) (M := M) g gT
      have hdecU := fullSlot2_decomp (I := I) (M := M) g gU
      rw [hdecT, hdecU]
      abel
    rw [heq]
    simpa only [c2JetSq, N] using hraw
  have hFT :
      c2JetSq (I := I) (M := M) g (F gT) ≤ Bf ^ 2 := by
    simpa only [F] using hfull T gT hTtie hT₂
  have hFU :
      c2JetSq (I := I) (M := M) g (F gU) ≤ Bf ^ 2 := by
    simpa only [F] using hfull U gU hUtie hU₂
  have hTjet :
      c2JetSq (I := I) (M := M) g T ≤ (Chs * ρ) ^ 2 := by
    have hraw : c2JetSq (I := I) (M := M) g T ≤
        (Chs *
          ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖) ^ 2 := by
      simpa only [c2JetSq] using hhs T
    exact hraw.trans
      (pow_le_pow_left₀
        (mul_nonneg hChs (norm_nonneg _))
        (mul_le_mul_of_nonneg_left hT hChs) 2)
  have hDjet :
      c2JetSq (I := I) (M := M) g (T - U) ≤
        (Chs * N) ^ 2 := by
    simpa only [c2JetSq, N] using hhs (T - U)
  have hQ₁ :
      c2JetSq (I := I) (M := M) g Q₁ ≤
        (K₁ * N) ^ 2 := by
    have hraw := happ (F gT - F gU) T
      (Ci * N) (Chs * ρ)
      (mul_nonneg hCi hN) (mul_nonneg hChs hρ0)
      hFdiff hTjet
    simpa only [c2JetSq, Q₁] using
      (show (Ca * (Ci * N) * (Chs * ρ)) ^ 2 =
          (K₁ * N) ^ 2 by
        dsimp only [K₁]
        ring ▸ hraw)
  have hQ₂ :
      c2JetSq (I := I) (M := M) g Q₂ ≤
        (K₂ * N) ^ 2 := by
    have hraw := happ (F gU) (T - U)
      Bf (Chs * N) hBf (mul_nonneg hChs hN)
      hFU hDjet
    simpa only [c2JetSq, Q₂] using
      (show (Ca * Bf * (Chs * N)) ^ 2 =
          (K₂ * N) ^ 2 by
        dsimp only [K₂]
        ring ▸ hraw)
  have hweight :
      LowBaseInternal.daWeight (I := I) (M := M) g gT T -
          LowBaseInternal.daWeight (I := I) (M := M) g gU U =
        Q₁ + Q₂ := by
    change
      appCc (I := I) (M := M) g 2 2 (F gT) T -
          appCc (I := I) (M := M) g 2 2 (F gU) U =
        Q₁ + Q₂
    dsimp only [Q₁, Q₂]
    rw [appCc_sub_left, appCc_sub_right_c2]
    abel
  have hdiff :
      c2JetSq (I := I) (M := M) g
          (LowBaseInternal.daWeight (I := I) (M := M) g gT T -
            LowBaseInternal.daWeight (I := I) (M := M) g gU U) ≤
        (C * N) ^ 2 := by
    rw [hweight]
    calc
      c2JetSq (I := I) (M := M) g (Q₁ + Q₂) ≤
          2 * (c2JetSq (I := I) (M := M) g Q₁ +
            c2JetSq (I := I) (M := M) g Q₂) :=
        jet3_add_c2 (I := I) (M := M) g Q₁ Q₂
      _ ≤ 2 * ((K₁ * N) ^ 2 + (K₂ * N) ^ 2) :=
        mul_le_mul_of_nonneg_left (add_le_add hQ₁ hQ₂) (by norm_num)
      _ ≤ (C * N) ^ 2 := by
        dsimp only [C]
        nlinarith [sq_nonneg (K₁ * N - K₂ * N),
          mul_nonneg (mul_nonneg hK₁ hN) (mul_nonneg hK₂ hN)]
  have hend :
      c2JetSq (I := I) (M := M) g
          (LowBaseInternal.daWeight (I := I) (M := M) g gT T) ≤
        B ^ 2 := by
    change
      c2JetSq (I := I) (M := M) g
        (appCc (I := I) (M := M) g 2 2 (F gT) T) ≤ B ^ 2
    have hraw := happ (F gT) T Bf (Chs * ρ)
      hBf (mul_nonneg hChs hρ0) hFT hTjet
    simpa only [c2JetSq, B] using hraw
  exact ⟨by simpa only [N] using hdiff, hend⟩

set_option maxHeartbeats 1600000 in
private theorem daTrans_pair_lip
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ C : ℝ, 0 < ρ ∧ 0 ≤ C ∧
      ∀ (T U : SmoothCcTensor g 0 2)
        (gT gU : SmoothRiemannianMetric I M),
        (∀ (y : M) (v w : TangentSpace I y),
          gT.inner y v w =
            g.inner y v w +
              ccTensorBilinSymm (I := I) g T y v w) →
        (∀ (y : M) (v w : TangentSpace I y),
          gU.inner y v w =
            g.inner y v w +
              ccTensorBilinSymm (I := I) g U y v w) →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ ≤ ρ →
        c2JetSq (I := I) (M := M) g
            (LowBaseInternal.daTrans (I := I) (M := M) g gT T -
              LowBaseInternal.daTrans (I := I) (M := M) g gU U) ≤
          (C * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
            (T - U)‖) ^ 2 := by
  obtain ⟨ρw, Cw, Bw, hρw, hCw, hBw, hweight⟩ :=
    daWeight_pair_lip (I := I) (M := M) hDim g
  obtain ⟨ρm, Cm, hρm, hCm, hmono⟩ :=
    curvMono_h2_lip (I := I) (M := M) hDim g
  let K : ℝ := Cm * Cw
  let C : ℝ := 2 * K
  have hK : 0 ≤ K := mul_nonneg hCm hCw
  have hC : 0 ≤ C := mul_nonneg (by norm_num) hK
  refine ⟨ρw, C, hρw, hC, ?_⟩
  intro T U gT gU hTtie hUtie hT hU
  let N : ℝ :=
    ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U)‖
  let S : SmoothCcTensor g 0 2 :=
    LowBaseInternal.daWeight (I := I) (M := M) g gT T
  let R : SmoothCcTensor g 0 2 :=
    LowBaseInternal.daWeight (I := I) (M := M) g gU U
  let V : Equiv.Perm (Fin 4) → SmoothCcTensor g 4 2 := fun σ =>
    LowBaseInternal.daTransMono (I := I) (M := M) g gT T σ -
      LowBaseInternal.daTransMono (I := I) (M := M) g gU U σ
  have hN : 0 ≤ N := norm_nonneg _
  obtain ⟨hSR, hS⟩ := hweight T U gT gU hTtie hUtie hT hU
  have hzero_app : ∀ (y : M) (v w : TangentSpace I y),
      ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2) y v w = 0 := by
    intro y v w
    have hz : (0 : SmoothCcTensor g 0 2) =
        (0 : ℝ) • (0 : SmoothCcTensor g 0 2) :=
      (zero_smul ℝ _).symm
    rw [hz, ccTensorBilinSymm_smul]
    ring
  have hzero_tie : ∀ (y : M) (v w : TangentSpace I y),
      g.inner y v w =
        g.inner y v w +
          ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2) y v w := by
    intro y v w
    rw [hzero_app, add_zero]
  have hcc0 :
      ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
          (0 : SmoothCcTensor g 0 2) = 0 := by
    rw [show (0 : SmoothCcTensor g 0 2) =
      (0 : ℝ) • (0 : SmoothCcTensor g 0 2) by simp,
      ccTensorToHs_smul, zero_smul]
  have hzero_norm :
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
        (0 : SmoothCcTensor g 0 2)‖ ≤ ρm := by
    rw [hcc0, norm_zero]
    exact le_of_lt hρm
  have hV (σ : Equiv.Perm (Fin 4)) :
      c2JetSq (I := I) (M := M) g (V σ) ≤ (K * N) ^ 2 := by
    have hraw := hmono
      (0 : SmoothCcTensor g 0 2) (0 : SmoothCcTensor g 0 2)
      g g hzero_tie hzero_tie hzero_norm hzero_norm
      S R σ Bw (Cw * N) hBw (mul_nonneg hCw hN)
      (by simpa only [S] using hS)
      (by simpa only [S, R, N] using hSR)
    have hzero_diff :
        ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
            ((0 : SmoothCcTensor g 0 2) - 0) = 0 := by
      rw [sub_self, hcc0]
    rw [hzero_diff, norm_zero, mul_zero, zero_add] at hraw
    simpa only [V, LowBaseInternal.daTransMono] using
      (show (Cm * (Cw * N)) ^ 2 = (K * N) ^ 2 by
        dsimp only [K]
        ring ▸ hraw)
  have htrans :
      LowBaseInternal.daTrans (I := I) (M := M) g gT T -
          LowBaseInternal.daTrans (I := I) (M := M) g gU U =
        V LowBaseInternal.daPermA - V LowBaseInternal.daPermB := by
    simp only [LowBaseInternal.daTrans, V]
    abel
  rw [htrans]
  calc
    c2JetSq (I := I) (M := M) g
        (V LowBaseInternal.daPermA - V LowBaseInternal.daPermB) ≤
      2 * (c2JetSq (I := I) (M := M) g
          (V LowBaseInternal.daPermA) +
        c2JetSq (I := I) (M := M) g
          (V LowBaseInternal.daPermB)) :=
      jet3_sub_c2 (I := I) (M := M) g _ _
    _ ≤ 2 * ((K * N) ^ 2 + (K * N) ^ 2) :=
      mul_le_mul_of_nonneg_left
        (add_le_add (hV LowBaseInternal.daPermA)
          (hV LowBaseInternal.daPermB)) (by norm_num)
    _ = (C * N) ^ 2 := by
      dsimp only [C]
      ring

set_option maxHeartbeats 1200000 in
private theorem daTrans_h2_bdd
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ B : ℝ, 0 < ρ ∧ 0 ≤ B ∧
      ∀ (T : SmoothCcTensor g 0 2)
        (gT : SmoothRiemannianMetric I M),
        (∀ (y : M) (v w : TangentSpace I y),
          gT.inner y v w =
            g.inner y v w +
              ccTensorBilinSymm (I := I) g T y v w) →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρ →
        c2JetSq (I := I) (M := M) g
            (LowBaseInternal.daTrans (I := I) (M := M) g gT T) ≤
          B ^ 2 := by
  obtain ⟨ρ, C, hρ, hC, hlip⟩ :=
    daTrans_pair_lip (I := I) (M := M) hDim g
  let F : SmoothCcTensor g 4 2 :=
    LowBaseInternal.daTrans (I := I) (M := M) g g
      (0 : SmoothCcTensor g 0 2)
  let J : ℝ := c2JetSq (I := I) (M := M) g F
  let Z : ℝ := 2 * ((C * ρ) ^ 2 + J)
  let B : ℝ := Real.sqrt Z
  have hJ : 0 ≤ J := jet3_nonneg_c2 (I := I) (M := M) g F
  have hZ : 0 ≤ Z := by
    dsimp only [Z]
    exact mul_nonneg (by norm_num)
      (add_nonneg (sq_nonneg (C * ρ)) hJ)
  have hB : 0 ≤ B := Real.sqrt_nonneg _
  have hBsq : B ^ 2 = Z := by
    simpa only [B] using Real.sq_sqrt hZ
  refine ⟨ρ, B, hρ, hB, ?_⟩
  intro T gT hTtie hT
  have hzero_app : ∀ (y : M) (v w : TangentSpace I y),
      ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2) y v w = 0 := by
    intro y v w
    have hz : (0 : SmoothCcTensor g 0 2) =
        (0 : ℝ) • (0 : SmoothCcTensor g 0 2) :=
      (zero_smul ℝ _).symm
    rw [hz, ccTensorBilinSymm_smul]
    ring
  have hzero_tie : ∀ (y : M) (v w : TangentSpace I y),
      g.inner y v w =
        g.inner y v w +
          ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2) y v w := by
    intro y v w
    rw [hzero_app, add_zero]
  have hcc0 :
      ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
          (0 : SmoothCcTensor g 0 2) = 0 := by
    rw [show (0 : SmoothCcTensor g 0 2) =
      (0 : ℝ) • (0 : SmoothCcTensor g 0 2) by simp,
      ccTensorToHs_smul, zero_smul]
  have hzero_norm :
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
        (0 : SmoothCcTensor g 0 2)‖ ≤ ρ := by
    rw [hcc0, norm_zero]
    exact le_of_lt hρ
  have hraw := hlip T (0 : SmoothCcTensor g 0 2) gT g
    hTtie hzero_tie hT hzero_norm
  have hmul :
      C * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
            (T - 0)‖ ≤ C * ρ := by
    rw [sub_zero]
    exact mul_le_mul_of_nonneg_left hT hC
  have hdiff :
      c2JetSq (I := I) (M := M) g
          (LowBaseInternal.daTrans (I := I) (M := M) g gT T - F) ≤
        (C * ρ) ^ 2 := by
    exact hraw.trans
      (pow_le_pow_left₀
        (mul_nonneg hC (norm_nonneg _)) hmul 2)
  rw [hBsq]
  calc
    c2JetSq (I := I) (M := M) g
        (LowBaseInternal.daTrans (I := I) (M := M) g gT T) =
      c2JetSq (I := I) (M := M) g
        ((LowBaseInternal.daTrans (I := I) (M := M) g gT T - F) +
          F) := by
      congr 1
      abel
    _ ≤ 2 * (c2JetSq (I := I) (M := M) g
          (LowBaseInternal.daTrans (I := I) (M := M) g gT T - F) +
        c2JetSq (I := I) (M := M) g F) :=
      jet3_add_c2 (I := I) (M := M) g _ _
    _ ≤ 2 * ((C * ρ) ^ 2 + J) :=
      mul_le_mul_of_nonneg_left (add_le_add hdiff le_rfl) (by norm_num)
    _ = Z := rfl

private noncomputable def fullInsert2C2
    (g gm : SmoothRiemannianMetric I M) : SmoothCcTensor g 3 3 :=
  slotInsertEndoCc (I := I) (M := M) g 2
    (fullRaisedEndoField (I := I) (M := M) g gm)

private noncomputable def koszulOpC2
    (g : SmoothRiemannianMetric I M) : SmoothCcTensor g 3 3 :=
  (1 / 2 : ℝ) •
    (permCoeff (I := I) (M := M) g (Equiv.swap (0 : Fin 3) 2) +
      permCoeff (I := I) (M := M) g (finRotate 3) -
      permCoeff (I := I) (M := M) g (Equiv.swap (1 : Fin 3) 2))

set_option maxHeartbeats 1400000 in
private theorem fullInsert2_pair
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ C : ℝ, 0 < ρ ∧ 0 ≤ C ∧
      ∀ (T U : SmoothCcTensor g 0 2)
        (gT gU : SmoothRiemannianMetric I M),
        (∀ (y : M) (v w : TangentSpace I y),
          gT.inner y v w =
            g.inner y v w +
              ccTensorBilinSymm (I := I) g T y v w) →
        (∀ (y : M) (v w : TangentSpace I y),
          gU.inner y v w =
            g.inner y v w +
              ccTensorBilinSymm (I := I) g U y v w) →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ ≤ ρ →
        c2JetSq (I := I) (M := M) g
            (fullInsert2C2 (I := I) (M := M) g gT -
              fullInsert2C2 (I := I) (M := M) g gU) ≤
          (C * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
            (T - U)‖) ^ 2 := by
  obtain ⟨ρ, Ci, hρ, hCi, hinv⟩ :=
    invCoeff_h2_lip (I := I) (M := M) hDim g
  let C : ℝ := 3 * Ci
  have hC : 0 ≤ C := mul_nonneg (by norm_num) hCi
  refine ⟨ρ, C, hρ, hC, ?_⟩
  intro T U gT gU hTtie hUtie hT hU
  let N : ℝ :=
    ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U)‖
  let Λ : ContMDiffSection I (E →L[ℝ] E) ∞
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x) :=
    fullRaisedEndoField (I := I) (M := M) g gT -
      fullRaisedEndoField (I := I) (M := M) g gU
  have hN : 0 ≤ N := norm_nonneg _
  have hraw := (hinv T U gT gU hTtie hUtie hT hU).2
  have hslot₁ :
      slotInsertEndoCc (I := I) (M := M) g 1 Λ =
        gInvDiffSlotCoeff (I := I) g gT -
          gInvDiffSlotCoeff (I := I) g gU := by
    dsimp only [Λ]
    rw [slotInsertEndoCc_sub]
    change
      fullSlot2 (I := I) (M := M) g gT -
          fullSlot2 (I := I) (M := M) g gU =
        gInvDiffSlotCoeff (I := I) g gT -
          gInvDiffSlotCoeff (I := I) g gU
    have hdecT := fullSlot2_decomp (I := I) (M := M) g gT
    have hdecU := fullSlot2_decomp (I := I) (M := M) g gU
    rw [hdecT, hdecU]
    abel
  have hslot₂ :
      fullInsert2C2 (I := I) (M := M) g gT -
          fullInsert2C2 (I := I) (M := M) g gU =
        slotInsertEndoCc (I := I) (M := M) g 2 Λ := by
    dsimp only [fullInsert2C2, Λ]
    rw [slotInsertEndoCc_sub]
  rw [hslot₂]
  calc
    c2JetSq (I := I) (M := M) g
        (slotInsertEndoCc (I := I) (M := M) g 2 Λ) ≤
      3 * c2JetSq (I := I) (M := M) g
        (slotInsertEndoCc (I := I) (M := M) g 1 Λ) := by
      simpa only [hDim, Nat.cast_ofNat] using
        insertSucc_jet_c2 (I := I) (M := M) g 1 Λ
    _ = 3 * c2JetSq (I := I) (M := M) g
        (gInvDiffSlotCoeff (I := I) g gT -
          gInvDiffSlotCoeff (I := I) g gU) := by rw [hslot₁]
    _ ≤ 3 * (Ci * N) ^ 2 := by
      exact mul_le_mul_of_nonneg_left
        (by simpa only [c2JetSq, N] using hraw) (by norm_num)
    _ ≤ (C * N) ^ 2 := by
      dsimp only [C]
      nlinarith [sq_nonneg (Ci * N)]

set_option maxHeartbeats 1200000 in
private theorem fullInsert2_bdd
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ B : ℝ, 0 < ρ ∧ 0 ≤ B ∧
      ∀ (T : SmoothCcTensor g 0 2)
        (gT : SmoothRiemannianMetric I M),
        (∀ (y : M) (v w : TangentSpace I y),
          gT.inner y v w =
            g.inner y v w +
              ccTensorBilinSymm (I := I) g T y v w) →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρ →
        c2JetSq (I := I) (M := M) g
            (fullInsert2C2 (I := I) (M := M) g gT) ≤ B ^ 2 := by
  obtain ⟨ρ, C, hρ, hC, hlip⟩ :=
    fullInsert2_pair (I := I) (M := M) hDim g
  let F : SmoothCcTensor g 3 3 :=
    fullInsert2C2 (I := I) (M := M) g g
  let J : ℝ := c2JetSq (I := I) (M := M) g F
  let Z : ℝ := 2 * ((C * ρ) ^ 2 + J)
  let B : ℝ := Real.sqrt Z
  have hJ : 0 ≤ J := jet3_nonneg_c2 (I := I) (M := M) g F
  have hZ : 0 ≤ Z := by
    dsimp only [Z]
    exact mul_nonneg (by norm_num)
      (add_nonneg (sq_nonneg (C * ρ)) hJ)
  have hB : 0 ≤ B := Real.sqrt_nonneg _
  have hBsq : B ^ 2 = Z := by
    simpa only [B] using Real.sq_sqrt hZ
  refine ⟨ρ, B, hρ, hB, ?_⟩
  intro T gT hTtie hT
  have hzero_app : ∀ (y : M) (v w : TangentSpace I y),
      ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2) y v w = 0 := by
    intro y v w
    have hz : (0 : SmoothCcTensor g 0 2) =
        (0 : ℝ) • (0 : SmoothCcTensor g 0 2) :=
      (zero_smul ℝ _).symm
    rw [hz, ccTensorBilinSymm_smul]
    ring
  have hzero_tie : ∀ (y : M) (v w : TangentSpace I y),
      g.inner y v w =
        g.inner y v w +
          ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2) y v w := by
    intro y v w
    rw [hzero_app, add_zero]
  have hcc0 :
      ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
          (0 : SmoothCcTensor g 0 2) = 0 := by
    rw [show (0 : SmoothCcTensor g 0 2) =
      (0 : ℝ) • (0 : SmoothCcTensor g 0 2) by simp,
      ccTensorToHs_smul, zero_smul]
  have hzero_norm :
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
        (0 : SmoothCcTensor g 0 2)‖ ≤ ρ := by
    rw [hcc0, norm_zero]
    exact le_of_lt hρ
  have hraw := hlip T (0 : SmoothCcTensor g 0 2) gT g
    hTtie hzero_tie hT hzero_norm
  have hmul :
      C * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
            (T - 0)‖ ≤ C * ρ := by
    rw [sub_zero]
    exact mul_le_mul_of_nonneg_left hT hC
  have hdiff :
      c2JetSq (I := I) (M := M) g
          (fullInsert2C2 (I := I) (M := M) g gT - F) ≤
        (C * ρ) ^ 2 :=
    hraw.trans
      (pow_le_pow_left₀
        (mul_nonneg hC (norm_nonneg _)) hmul 2)
  rw [hBsq]
  calc
    c2JetSq (I := I) (M := M) g
        (fullInsert2C2 (I := I) (M := M) g gT) =
      c2JetSq (I := I) (M := M) g
        ((fullInsert2C2 (I := I) (M := M) g gT - F) + F) := by
      congr 1
      abel
    _ ≤ 2 * (c2JetSq (I := I) (M := M) g
          (fullInsert2C2 (I := I) (M := M) g gT - F) +
        c2JetSq (I := I) (M := M) g F) :=
      jet3_add_c2 (I := I) (M := M) g _ _
    _ ≤ 2 * ((C * ρ) ^ 2 + J) :=
      mul_le_mul_of_nonneg_left (add_le_add hdiff le_rfl) (by norm_num)
    _ = Z := rfl

set_option maxHeartbeats 1400000 in
private theorem connLow_pair
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ C : ℝ, 0 < ρ ∧ 0 ≤ C ∧
      ∀ (T U : SmoothCcTensor g 0 2)
        (gT gU : SmoothRiemannianMetric I M),
        (∀ (y : M) (v w : TangentSpace I y),
          gT.inner y v w =
            g.inner y v w +
              ccTensorBilinSymm (I := I) g T y v w) →
        (∀ (y : M) (v w : TangentSpace I y),
          gU.inner y v w =
            g.inner y v w +
              ccTensorBilinSymm (I := I) g U y v w) →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ ≤ ρ →
        c2JetSq (I := I) (M := M) g
            (LowBaseInternal.connLowOp (I := I) (M := M) g gT -
              LowBaseInternal.connLowOp (I := I) (M := M) g gU) ≤
          (C * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
            (T - U)‖) ^ 2 := by
  obtain ⟨ρ, Cf, hρ, hCf, hfull⟩ :=
    fullInsert2_pair (I := I) (M := M) hDim g
  obtain ⟨Ca, hCa, happ⟩ :=
    appRS_h2_h2_h2 (I := I) (M := M) hDim g 3 3 3
  let K : SmoothCcTensor g 3 3 :=
    koszulOpC2 (I := I) (M := M) g
  let P : SmoothCcTensor g 3 3 :=
    permCoeff (I := I) (M := M) g LowBaseInternal.lowPerm
  let JK : ℝ := c2JetSq (I := I) (M := M) g K
  let JP : ℝ := c2JetSq (I := I) (M := M) g P
  let AK : ℝ := Real.sqrt JK
  let AP : ℝ := Real.sqrt JP
  let C : ℝ := Ca ^ 2 * AP * Cf * AK
  have hJK : 0 ≤ JK := jet3_nonneg_c2 (I := I) (M := M) g K
  have hJP : 0 ≤ JP := jet3_nonneg_c2 (I := I) (M := M) g P
  have hAK : 0 ≤ AK := Real.sqrt_nonneg _
  have hAP : 0 ≤ AP := Real.sqrt_nonneg _
  have hAKsq : AK ^ 2 = JK := by
    simpa only [AK] using Real.sq_sqrt hJK
  have hAPsq : AP ^ 2 = JP := by
    simpa only [AP] using Real.sq_sqrt hJP
  have hC : 0 ≤ C := by
    dsimp only [C]
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (sq_nonneg Ca) hAP) hCf) hAK
  refine ⟨ρ, C, hρ, hC, ?_⟩
  intro T U gT gU hTtie hUtie hT hU
  let N : ℝ :=
    ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U)‖
  let D : SmoothCcTensor g 3 3 :=
    fullInsert2C2 (I := I) (M := M) g gT -
      fullInsert2C2 (I := I) (M := M) g gU
  let Mid : SmoothCcTensor g 3 3 :=
    appCcRS (I := I) (M := M) g 3 3 3 D K
  have hN : 0 ≤ N := norm_nonneg _
  have hD :
      c2JetSq (I := I) (M := M) g D ≤ (Cf * N) ^ 2 := by
    simpa only [D, N] using hfull T U gT gU hTtie hUtie hT hU
  have hK :
      c2JetSq (I := I) (M := M) g K ≤ AK ^ 2 := by
    rw [hAKsq]
  have hP :
      c2JetSq (I := I) (M := M) g P ≤ AP ^ 2 := by
    rw [hAPsq]
  have hMid :
      c2JetSq (I := I) (M := M) g Mid ≤
        (Ca * (Cf * N) * AK) ^ 2 := by
    exact happ D K (Cf * N) AK
      (mul_nonneg hCf hN) hAK hD hK
  have heq :
      LowBaseInternal.connLowOp (I := I) (M := M) g gT -
          LowBaseInternal.connLowOp (I := I) (M := M) g gU =
        appCcRS (I := I) (M := M) g 3 3 3 P Mid := by
    change
      appCcRS (I := I) (M := M) g 3 3 3 P
            (appCcRS (I := I) (M := M) g 3 3 3
              (fullInsert2C2 (I := I) (M := M) g gT) K) -
          appCcRS (I := I) (M := M) g 3 3 3 P
            (appCcRS (I := I) (M := M) g 3 3 3
              (fullInsert2C2 (I := I) (M := M) g gU) K) =
        appCcRS (I := I) (M := M) g 3 3 3 P Mid
    rw [← appCcRS_sub_right, ← appCcRS_sub_left]
  rw [heq]
  calc
    c2JetSq (I := I) (M := M) g
        (appCcRS (I := I) (M := M) g 3 3 3 P Mid) ≤
      (Ca * AP * (Ca * (Cf * N) * AK)) ^ 2 :=
        happ P Mid AP (Ca * (Cf * N) * AK)
          hAP
          (mul_nonneg (mul_nonneg hCa (mul_nonneg hCf hN)) hAK)
          hP hMid
    _ = (C * N) ^ 2 := by
      dsimp only [C]
      ring

set_option maxHeartbeats 1200000 in
private theorem connLow_bdd
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ B : ℝ, 0 < ρ ∧ 0 ≤ B ∧
      ∀ (T : SmoothCcTensor g 0 2)
        (gT : SmoothRiemannianMetric I M),
        (∀ (y : M) (v w : TangentSpace I y),
          gT.inner y v w =
            g.inner y v w +
              ccTensorBilinSymm (I := I) g T y v w) →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρ →
        c2JetSq (I := I) (M := M) g
            (LowBaseInternal.connLowOp (I := I) (M := M) g gT) ≤
          B ^ 2 := by
  obtain ⟨ρ, BF, hρ, hBF, hfull⟩ :=
    fullInsert2_bdd (I := I) (M := M) hDim g
  obtain ⟨Ca, hCa, happ⟩ :=
    appRS_h2_h2_h2 (I := I) (M := M) hDim g 3 3 3
  let K : SmoothCcTensor g 3 3 :=
    koszulOpC2 (I := I) (M := M) g
  let P : SmoothCcTensor g 3 3 :=
    permCoeff (I := I) (M := M) g LowBaseInternal.lowPerm
  let JK : ℝ := c2JetSq (I := I) (M := M) g K
  let JP : ℝ := c2JetSq (I := I) (M := M) g P
  let AK : ℝ := Real.sqrt JK
  let AP : ℝ := Real.sqrt JP
  let B : ℝ := Ca ^ 2 * AP * BF * AK
  have hJK : 0 ≤ JK := jet3_nonneg_c2 (I := I) (M := M) g K
  have hJP : 0 ≤ JP := jet3_nonneg_c2 (I := I) (M := M) g P
  have hAK : 0 ≤ AK := Real.sqrt_nonneg _
  have hAP : 0 ≤ AP := Real.sqrt_nonneg _
  have hAKsq : AK ^ 2 = JK := by
    simpa only [AK] using Real.sq_sqrt hJK
  have hAPsq : AP ^ 2 = JP := by
    simpa only [AP] using Real.sq_sqrt hJP
  have hB : 0 ≤ B := by
    dsimp only [B]
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (sq_nonneg Ca) hAP) hBF) hAK
  refine ⟨ρ, B, hρ, hB, ?_⟩
  intro T gT hTtie hT
  let F : SmoothCcTensor g 3 3 :=
    fullInsert2C2 (I := I) (M := M) g gT
  let Mid : SmoothCcTensor g 3 3 :=
    appCcRS (I := I) (M := M) g 3 3 3 F K
  have hF : c2JetSq (I := I) (M := M) g F ≤ BF ^ 2 := by
    simpa only [F] using hfull T gT hTtie hT
  have hK :
      c2JetSq (I := I) (M := M) g K ≤ AK ^ 2 := by
    rw [hAKsq]
  have hP :
      c2JetSq (I := I) (M := M) g P ≤ AP ^ 2 := by
    rw [hAPsq]
  have hMid :
      c2JetSq (I := I) (M := M) g Mid ≤
        (Ca * BF * AK) ^ 2 :=
    happ F K BF AK hBF hAK hF hK
  change c2JetSq (I := I) (M := M) g
      (appCcRS (I := I) (M := M) g 3 3 3 P Mid) ≤ B ^ 2
  calc
    _ ≤ (Ca * AP * (Ca * BF * AK)) ^ 2 :=
      happ P Mid AP (Ca * BF * AK) hAP
        (mul_nonneg (mul_nonneg hCa hBF) hAK) hP hMid
    _ = B ^ 2 := by
      dsimp only [B]
      ring

set_option maxHeartbeats 1400000 in
private theorem dagTop_pair
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ C : ℝ, 0 < ρ ∧ 0 ≤ C ∧
      ∀ (T U : SmoothCcTensor g 0 2)
        (gT gU : SmoothRiemannianMetric I M),
        (∀ (y : M) (v w : TangentSpace I y),
          gT.inner y v w =
            g.inner y v w +
              ccTensorBilinSymm (I := I) g T y v w) →
        (∀ (y : M) (v w : TangentSpace I y),
          gU.inner y v w =
            g.inner y v w +
              ccTensorBilinSymm (I := I) g U y v w) →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ ≤ ρ →
        c2JetSq (I := I) (M := M) g
            (LowBaseInternal.dagTopOp (I := I) (M := M) g gT -
              LowBaseInternal.dagTopOp (I := I) (M := M) g gU) ≤
          (C * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
            (T - U)‖) ^ 2 := by
  obtain ⟨ρ, Cc, hρ, hCc, hconn⟩ :=
    connLow_pair (I := I) (M := M) hDim g
  obtain ⟨Ca, hCa, happ⟩ :=
    appRS_h2_h2_h2 (I := I) (M := M) hDim g 4 4 4
  let P : SmoothCcTensor g 4 4 :=
    permCoeff (I := I) (M := M) g LowBaseInternal.daPermA
  let JP : ℝ := c2JetSq (I := I) (M := M) g P
  let AP : ℝ := Real.sqrt JP
  let C : ℝ := Ca * AP * (3 * Cc)
  have hJP : 0 ≤ JP := jet3_nonneg_c2 (I := I) (M := M) g P
  have hAP : 0 ≤ AP := Real.sqrt_nonneg _
  have hAPsq : AP ^ 2 = JP := by
    simpa only [AP] using Real.sq_sqrt hJP
  have hC : 0 ≤ C := by
    dsimp only [C]
    positivity
  refine ⟨ρ, C, hρ, hC, ?_⟩
  intro T U gT gU hTtie hUtie hT hU
  let N : ℝ :=
    ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U)‖
  let D : SmoothCcTensor g 3 3 :=
    LowBaseInternal.connLowOp (I := I) (M := M) g gT -
      LowBaseInternal.connLowOp (I := I) (M := M) g gU
  let S : SmoothCcTensor g 4 4 :=
    slotExtend (I := I) (M := M) g 3 3 D
  have hN : 0 ≤ N := norm_nonneg _
  have hD :
      c2JetSq (I := I) (M := M) g D ≤ (Cc * N) ^ 2 := by
    simpa only [D, N] using hconn T U gT gU hTtie hUtie hT hU
  have hS :
      c2JetSq (I := I) (M := M) g S ≤
        (3 * Cc * N) ^ 2 := by
    calc
      c2JetSq (I := I) (M := M) g S ≤
        3 * c2JetSq (I := I) (M := M) g D := by
          simpa only [S, hDim, Nat.cast_ofNat] using
            slot_jet_c2 (I := I) (M := M) g 3 3 D
      _ ≤ 3 * (Cc * N) ^ 2 :=
        mul_le_mul_of_nonneg_left hD (by norm_num)
      _ ≤ (3 * Cc * N) ^ 2 := by
        nlinarith [sq_nonneg (Cc * N)]
  have hP :
      c2JetSq (I := I) (M := M) g P ≤ AP ^ 2 := by
    rw [hAPsq]
  have heq :
      LowBaseInternal.dagTopOp (I := I) (M := M) g gT -
          LowBaseInternal.dagTopOp (I := I) (M := M) g gU =
        appCcRS (I := I) (M := M) g 4 4 4 P S := by
    change
      appCcRS (I := I) (M := M) g 4 4 4 P
            (slotExtend (I := I) (M := M) g 3 3
              (LowBaseInternal.connLowOp (I := I) (M := M) g gT)) -
          appCcRS (I := I) (M := M) g 4 4 4 P
            (slotExtend (I := I) (M := M) g 3 3
              (LowBaseInternal.connLowOp (I := I) (M := M) g gU)) =
        appCcRS (I := I) (M := M) g 4 4 4 P S
    rw [← appCcRS_sub_right, ← slotExtend_sub]
  rw [heq]
  calc
    c2JetSq (I := I) (M := M) g
        (appCcRS (I := I) (M := M) g 4 4 4 P S) ≤
      (Ca * AP * (3 * Cc * N)) ^ 2 :=
        happ P S AP (3 * Cc * N) hAP
          (mul_nonneg (mul_nonneg (by norm_num) hCc) hN) hP hS
    _ = (C * N) ^ 2 := by
      dsimp only [C]
      ring

set_option maxHeartbeats 1200000 in
private theorem dagTop_bdd
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ B : ℝ, 0 < ρ ∧ 0 ≤ B ∧
      ∀ (T : SmoothCcTensor g 0 2)
        (gT : SmoothRiemannianMetric I M),
        (∀ (y : M) (v w : TangentSpace I y),
          gT.inner y v w =
            g.inner y v w +
              ccTensorBilinSymm (I := I) g T y v w) →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρ →
        c2JetSq (I := I) (M := M) g
            (LowBaseInternal.dagTopOp (I := I) (M := M) g gT) ≤
          B ^ 2 := by
  obtain ⟨ρ, Bc, hρ, hBc, hconn⟩ :=
    connLow_bdd (I := I) (M := M) hDim g
  obtain ⟨Ca, hCa, happ⟩ :=
    appRS_h2_h2_h2 (I := I) (M := M) hDim g 4 4 4
  let P : SmoothCcTensor g 4 4 :=
    permCoeff (I := I) (M := M) g LowBaseInternal.daPermA
  let JP : ℝ := c2JetSq (I := I) (M := M) g P
  let AP : ℝ := Real.sqrt JP
  let B : ℝ := Ca * AP * (3 * Bc)
  have hJP : 0 ≤ JP := jet3_nonneg_c2 (I := I) (M := M) g P
  have hAP : 0 ≤ AP := Real.sqrt_nonneg _
  have hAPsq : AP ^ 2 = JP := by
    simpa only [AP] using Real.sq_sqrt hJP
  have hB : 0 ≤ B := by
    dsimp only [B]
    positivity
  refine ⟨ρ, B, hρ, hB, ?_⟩
  intro T gT hTtie hT
  let D : SmoothCcTensor g 3 3 :=
    LowBaseInternal.connLowOp (I := I) (M := M) g gT
  let S : SmoothCcTensor g 4 4 :=
    slotExtend (I := I) (M := M) g 3 3 D
  have hD :
      c2JetSq (I := I) (M := M) g D ≤ Bc ^ 2 := by
    simpa only [D] using hconn T gT hTtie hT
  have hS :
      c2JetSq (I := I) (M := M) g S ≤
        (3 * Bc) ^ 2 := by
    calc
      c2JetSq (I := I) (M := M) g S ≤
        3 * c2JetSq (I := I) (M := M) g D := by
          simpa only [S, hDim, Nat.cast_ofNat] using
            slot_jet_c2 (I := I) (M := M) g 3 3 D
      _ ≤ 3 * Bc ^ 2 :=
        mul_le_mul_of_nonneg_left hD (by norm_num)
      _ ≤ (3 * Bc) ^ 2 := by
        nlinarith [sq_nonneg Bc]
  have hP :
      c2JetSq (I := I) (M := M) g P ≤ AP ^ 2 := by
    rw [hAPsq]
  change c2JetSq (I := I) (M := M) g
      (appCcRS (I := I) (M := M) g 4 4 4 P S) ≤ B ^ 2
  calc
    _ ≤ (Ca * AP * (3 * Bc)) ^ 2 :=
      happ P S AP (3 * Bc) hAP
        (mul_nonneg (by norm_num) hBc) hP hS
    _ = B ^ 2 := rfl

private theorem daTrans_smul
    (g gm : SmoothRiemannianMetric I M)
    (s : ℝ) (T : SmoothCcTensor g 0 2) :
    LowBaseInternal.daTrans (I := I) (M := M) g gm (s • T) =
      s • LowBaseInternal.daTrans (I := I) (M := M) g gm T := by
  simp only [LowBaseInternal.daTrans, LowBaseInternal.daTransMono,
    LowBaseInternal.daWeight, appCc_smul_right,
    curvatureRefoldMonomialCoeffField_unitValue_smul]
  module

set_option linter.unusedSectionVars false in
set_option backward.isDefEq.respectTransparency false in
private theorem appCcRS_smul_left_c2
    (g : SmoothRiemannianMetric I M) (a b c : ℕ)
    (s : ℝ) (Φ : SmoothCcTensor g b c) (W : SmoothCcTensor g a b) :
    appCcRS (I := I) (M := M) g a b c (s • Φ) W =
      s • appCcRS (I := I) (M := M) g a b c Φ W := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [show ((s • appCcRS (I := I) (M := M) g a b c Φ W).toSection x) =
      s • (appCcRS (I := I) (M := M) g a b c Φ W).toSection x from by
    rw [SmoothCcTensor.toSection_smul]
    rfl]
  rw [appCcRS_toSection, appCcRS_toSection]
  rw [show ((s • Φ).toSection x : TensorRSSpace b c I x) =
      s • Φ.toSection x from by
    rw [SmoothCcTensor.toSection_smul]
    rfl]
  rw [ContinuousLinearMap.smul_comp]

set_option maxHeartbeats 2400000 in
private theorem ricciRad_pair
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ C : ℝ, 0 < ρ ∧ 0 ≤ C ∧
      ∀ (T U : SmoothCcTensor g 0 2) {δ : ℝ},
        δ < 1 →
        (hTδ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ) →
        (hUδ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g U) δ) →
        (hZδ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ) →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ ≤ ρ →
        ∀ {s : ℝ}, s ∈ Set.Icc (0 : ℝ) 1 →
          let gmT := realizedFam (I := I) g T 0 hTδ hZδ s
          let gmU := realizedFam (I := I) g U 0 hUδ hZδ s
          c2JetSq (I := I) (M := M) g
              ((-2 * s : ℝ) •
                  LowBaseInternal.ricciTop (I := I) (M := M) g gmT T -
                (-2 * s : ℝ) •
                  LowBaseInternal.ricciTop (I := I) (M := M) g gmU U) ≤
            (C * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
              (T - U)‖) ^ 2 := by
  obtain ⟨ρd, Cd, hρd, hCd, hdpair⟩ :=
    daTrans_pair_lip (I := I) (M := M) hDim g
  obtain ⟨ρdb, Bd, hρdb, hBd, hdbdd⟩ :=
    daTrans_h2_bdd (I := I) (M := M) hDim g
  obtain ⟨ρg, Cg, hρg, hCg, hgpair⟩ :=
    dagTop_pair (I := I) (M := M) hDim g
  obtain ⟨ρgb, Bg, hρgb, hBg, hgbdd⟩ :=
    dagTop_bdd (I := I) (M := M) hDim g
  obtain ⟨Ca, hCa, happ⟩ :=
    appRS_h2_h2_h2 (I := I) (M := M) hDim g 4 4 2
  let ρ : ℝ := min (min ρd ρdb) (min ρg ρgb)
  let K₁ : ℝ := Ca * Cd * Bg
  let K₂ : ℝ := Ca * Bd * Cg
  let C : ℝ := 4 * (K₁ + K₂)
  have hρ : 0 < ρ :=
    lt_min (lt_min hρd hρdb) (lt_min hρg hρgb)
  have hK₁ : 0 ≤ K₁ := mul_nonneg (mul_nonneg hCa hCd) hBg
  have hK₂ : 0 ≤ K₂ := mul_nonneg (mul_nonneg hCa hBd) hCg
  have hC : 0 ≤ C :=
    mul_nonneg (by norm_num) (add_nonneg hK₁ hK₂)
  refine ⟨ρ, C, hρ, hC, ?_⟩
  intro T U δ hδlt hTδ hUδ hZδ hT hU s hs
  let P : SmoothCcTensor g 0 2 := s • T
  let Q : SmoothCcTensor g 0 2 := s • U
  let gmT : SmoothRiemannianMetric I M :=
    realizedFam (I := I) g T 0 hTδ hZδ s
  let gmU : SmoothRiemannianMetric I M :=
    realizedFam (I := I) g U 0 hUδ hZδ s
  let DT : SmoothCcTensor g 4 2 :=
    LowBaseInternal.daTrans (I := I) (M := M) g gmT P
  let DU : SmoothCcTensor g 4 2 :=
    LowBaseInternal.daTrans (I := I) (M := M) g gmU Q
  let GT : SmoothCcTensor g 4 4 :=
    LowBaseInternal.dagTopOp (I := I) (M := M) g gmT
  let GU : SmoothCcTensor g 4 4 :=
    LowBaseInternal.dagTopOp (I := I) (M := M) g gmU
  let N : ℝ :=
    ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U)‖
  let Q₁ : SmoothCcTensor g 4 2 :=
    appCcRS (I := I) (M := M) g 4 4 2 (DT - DU) GT
  let Q₂ : SmoothCcTensor g 4 2 :=
    appCcRS (I := I) (M := M) g 4 4 2 DU (GT - GU)
  have hN : 0 ≤ N := norm_nonneg _
  have hsabs : ‖s‖ ≤ (1 : ℝ) := by
    rw [Real.norm_eq_abs, abs_of_nonneg hs.1]
    exact hs.2
  have hPρ :
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) P‖ ≤ ρ := by
    rw [show P = s • T from rfl, ccTensorToHs_smul, norm_smul]
    calc
      ‖s‖ * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤
          1 * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ :=
        mul_le_mul_of_nonneg_right hsabs (norm_nonneg _)
      _ ≤ ρ := by simpa using hT
  have hQρ :
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) Q‖ ≤ ρ := by
    rw [show Q = s • U from rfl, ccTensorToHs_smul, norm_smul]
    calc
      ‖s‖ * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ ≤
          1 * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ :=
        mul_le_mul_of_nonneg_right hsabs (norm_nonneg _)
      _ ≤ ρ := by simpa using hU
  have hPQ :
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (P - Q)‖ ≤ N := by
    have heq : P - Q = s • (T - U) := by
      dsimp only [P, Q]
      module
    rw [heq, ccTensorToHs_smul, norm_smul]
    exact (mul_le_mul_of_nonneg_right hsabs hN).trans (by simp)
  have hs_mem : s ∈ realizedSmallSet (δ := δ) (δ' := δ) :=
    Icc_subset_realizedSmallSet hδlt hδlt hs
  have hPtie : ∀ (x : M) (v w : TangentSpace I x),
      gmT.inner x v w =
        g.inner x v w + ccTensorBilinSymm (I := I) g P x v w := by
    intro x v w
    simpa only [gmT, P, convexPerturbation, smul_zero, zero_add] using
      realizedFam_inner_of_mem
        (I := I) g T 0 hTδ hZδ hs_mem x v w
  have hQtie : ∀ (x : M) (v w : TangentSpace I x),
      gmU.inner x v w =
        g.inner x v w + ccTensorBilinSymm (I := I) g Q x v w := by
    intro x v w
    simpa only [gmU, Q, convexPerturbation, smul_zero, zero_add] using
      realizedFam_inner_of_mem
        (I := I) g U 0 hUδ hZδ hs_mem x v w
  have hρd' : ρ ≤ ρd :=
    (min_le_left _ _).trans (min_le_left _ _)
  have hρdb' : ρ ≤ ρdb :=
    (min_le_left _ _).trans (min_le_right _ _)
  have hρg' : ρ ≤ ρg :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hρgb' : ρ ≤ ρgb :=
    (min_le_right _ _).trans (min_le_right _ _)
  have hDTraw :
      c2JetSq (I := I) (M := M) g (DT - DU) ≤
        (Cd * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
          (P - Q)‖) ^ 2 := by
    simpa only [DT, DU] using
      hdpair P Q gmT gmU hPtie hQtie
        (hPρ.trans hρd') (hQρ.trans hρd')
  have hDT :
      c2JetSq (I := I) (M := M) g (DT - DU) ≤
        (Cd * N) ^ 2 :=
    hDTraw.trans
      (pow_le_pow_left₀
        (mul_nonneg hCd (norm_nonneg _))
        (mul_le_mul_of_nonneg_left hPQ hCd) 2)
  have hGTraw :
      c2JetSq (I := I) (M := M) g (GT - GU) ≤
        (Cg * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
          (P - Q)‖) ^ 2 := by
    simpa only [GT, GU] using
      hgpair P Q gmT gmU hPtie hQtie
        (hPρ.trans hρg') (hQρ.trans hρg')
  have hGT :
      c2JetSq (I := I) (M := M) g (GT - GU) ≤
        (Cg * N) ^ 2 :=
    hGTraw.trans
      (pow_le_pow_left₀
        (mul_nonneg hCg (norm_nonneg _))
        (mul_le_mul_of_nonneg_left hPQ hCg) 2)
  have hDU :
      c2JetSq (I := I) (M := M) g DU ≤ Bd ^ 2 := by
    simpa only [DU] using
      hdbdd Q gmU hQtie (hQρ.trans hρdb')
  have hGTend :
      c2JetSq (I := I) (M := M) g GT ≤ Bg ^ 2 := by
    simpa only [GT] using
      hgbdd P gmT hPtie (hPρ.trans hρgb')
  have hQ₁ :
      c2JetSq (I := I) (M := M) g Q₁ ≤
        (K₁ * N) ^ 2 := by
    have hraw := happ (DT - DU) GT (Cd * N) Bg
      (mul_nonneg hCd hN) hBg hDT hGTend
    simpa only [Q₁] using
      (show (Ca * (Cd * N) * Bg) ^ 2 = (K₁ * N) ^ 2 by
        dsimp only [K₁]
        ring ▸ hraw)
  have hQ₂ :
      c2JetSq (I := I) (M := M) g Q₂ ≤
        (K₂ * N) ^ 2 := by
    have hraw := happ DU (GT - GU) Bd (Cg * N)
      hBd (mul_nonneg hCg hN) hDU hGT
    simpa only [Q₂] using
      (show (Ca * Bd * (Cg * N)) ^ 2 = (K₂ * N) ^ 2 by
        dsimp only [K₂]
        ring ▸ hraw)
  have hprod :
      appCcRS (I := I) (M := M) g 4 4 2 DT GT -
          appCcRS (I := I) (M := M) g 4 4 2 DU GU =
        Q₁ + Q₂ := by
    dsimp only [Q₁, Q₂]
    rw [appCcRS_sub_left, appCcRS_sub_right]
    abel
  have hricT :
      (-2 * s : ℝ) •
          LowBaseInternal.ricciTop (I := I) (M := M) g gmT T =
        (-2 : ℝ) •
          appCcRS (I := I) (M := M) g 4 4 2 DT GT := by
    dsimp only [LowBaseInternal.ricciTop, DT, GT, P]
    rw [daTrans_smul (I := I) (M := M) g gmT s T]
    rw [appCcRS_smul_left_c2]
    simp only [smul_smul]
  have hricU :
      (-2 * s : ℝ) •
          LowBaseInternal.ricciTop (I := I) (M := M) g gmU U =
        (-2 : ℝ) •
          appCcRS (I := I) (M := M) g 4 4 2 DU GU := by
    dsimp only [LowBaseInternal.ricciTop, DU, GU, Q]
    rw [daTrans_smul (I := I) (M := M) g gmU s U]
    rw [appCcRS_smul_left_c2]
    simp only [smul_smul]
  have hrad :
      (-2 * s : ℝ) •
            LowBaseInternal.ricciTop (I := I) (M := M) g gmT T -
          (-2 * s : ℝ) •
            LowBaseInternal.ricciTop (I := I) (M := M) g gmU U =
        (-2 : ℝ) • (Q₁ + Q₂) := by
    rw [hricT, hricU, ← smul_sub, hprod]
  change c2JetSq (I := I) (M := M) g
      ((-2 * s : ℝ) •
          LowBaseInternal.ricciTop (I := I) (M := M) g gmT T -
        (-2 * s : ℝ) •
          LowBaseInternal.ricciTop (I := I) (M := M) g gmU U) ≤
    (C * N) ^ 2
  rw [hrad, jet3_smul_c2]
  have hsum :
      c2JetSq (I := I) (M := M) g (Q₁ + Q₂) ≤
        (2 * (K₁ + K₂) * N) ^ 2 := by
    calc
      c2JetSq (I := I) (M := M) g (Q₁ + Q₂) ≤
          2 * (c2JetSq (I := I) (M := M) g Q₁ +
            c2JetSq (I := I) (M := M) g Q₂) :=
        jet3_add_c2 (I := I) (M := M) g Q₁ Q₂
      _ ≤ 2 * ((K₁ * N) ^ 2 + (K₂ * N) ^ 2) :=
        mul_le_mul_of_nonneg_left (add_le_add hQ₁ hQ₂) (by norm_num)
      _ ≤ (2 * (K₁ + K₂) * N) ^ 2 := by
        nlinarith [mul_nonneg hK₁ hN, mul_nonneg hK₂ hN,
          sq_nonneg (K₁ * N - K₂ * N)]
  calc
    (-2 : ℝ) ^ 2 * c2JetSq (I := I) (M := M) g (Q₁ + Q₂) ≤
        4 * (2 * (K₁ + K₂) * N) ^ 2 :=
      by
        have h := mul_le_mul_of_nonneg_left hsum (sq_nonneg (-2 : ℝ))
        norm_num at h ⊢
        exact h
    _ = (C * N) ^ 2 := by
      dsimp only [C]
      ring

/-- On a three-dimensional spectral `H2` ball, the smooth geometric
moving-inverse insertion is Lipschitz as a bounded operator on rank-four
spectral `H2` tensors. -/
theorem invGeomOp_lip
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ C : ℝ, 0 < ρ ∧ 0 ≤ C ∧
      ∀ (T U : SmoothCcTensor g 0 2)
        (gT gU : SmoothRiemannianMetric I M),
        (∀ (y : M) (v w : TangentSpace I y),
          gT.inner y v w =
            g.inner y v w +
              ccTensorBilinSymm (I := I) g T y v w) →
        (∀ (y : M) (v w : TangentSpace I y),
          gU.inner y v w =
            g.inner y v w +
              ccTensorBilinSymm (I := I) g U y v w) →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ ≤ ρ →
        ‖appHs (I := I) (M := M) g 4 4 2
              (slotInsertEndoCc (I := I) (M := M) g 3
                (gInvDiffRaisedEndoField (I := I) g gT)) -
            appHs (I := I) (M := M) g 4 4 2
              (slotInsertEndoCc (I := I) (M := M) g 3
                (gInvDiffRaisedEndoField (I := I) g gU))‖ ≤
          C * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T -
            ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ := by
  obtain ⟨ρLip, C, hρLip, hC, hLip⟩ :=
    invPerturbH2_lip (I := I) (M := M) hDim g
  obtain ⟨ρCore, _, hρCore, _, hCore⟩ :=
    invPerturbH2_norm (I := I) (M := M) hDim g
  let ρ : ℝ := min ρLip ρCore
  have hρ : 0 < ρ := lt_min hρLip hρCore
  refine ⟨ρ, C, hρ, hC, ?_⟩
  intro T U gT gU hTtie hUtie hT hU
  let TH2 :=
    ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T
  let UH2 :=
    ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U
  have hTLip : ‖TH2‖ ≤ ρLip :=
    hT.trans (min_le_left ρLip ρCore)
  have hULip : ‖UH2‖ ≤ ρLip :=
    hU.trans (min_le_left ρLip ρCore)
  have hTCore : ‖TH2‖ ≤ ρCore :=
    hT.trans (min_le_right ρLip ρCore)
  have hUCore : ‖UH2‖ ≤ ρCore :=
    hU.trans (min_le_right ρLip ρCore)
  have hTsmall :
      ‖perturbH2 (I := I) (M := M) g TH2‖ < 1 :=
    (hCore TH2 hTCore).1.trans_lt (by norm_num)
  have hUsmall :
      ‖perturbH2 (I := I) (M := M) g UH2‖ < 1 :=
    (hCore UH2 hUCore).1.trans_lt (by norm_num)
  have hTcore :=
    invPerturbH2_core (I := I) (M := M)
      hDim g gT T hTtie hTsmall
  have hUcore :=
    invPerturbH2_core (I := I) (M := M)
      hDim g gU U hUtie hUsmall
  rw [← hTcore, ← hUcore]
  exact hLip TH2 UH2 hTLip hULip

/-- On a three-dimensional spectral `H2` ball, the complete geometric
principal correction is Lipschitz as a bounded operator from `H4` to `H2`. -/
theorem principalGeom_lip
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ C : ℝ, 0 < ρ ∧ 0 ≤ C ∧
      ∀ (T U : SmoothCcTensor g 0 2)
        (gT gU : SmoothRiemannianMetric I M),
        (∀ (y : M) (v w : TangentSpace I y),
          gT.inner y v w =
            g.inner y v w +
              ccTensorBilinSymm (I := I) g T y v w) →
        (∀ (y : M) (v w : TangentSpace I y),
          gU.inner y v w =
            g.inner y v w +
              ccTensorBilinSymm (I := I) g U y v w) →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ ≤ ρ →
        ‖principalOpH2 (I := I) (M := M) g gT -
            principalOpH2 (I := I) (M := M) g gU‖ ≤
          C * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T -
            ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ := by
  obtain ⟨ρLip, C, hρLip, hC, hLip⟩ :=
    lowRegPrincipal_lip (I := I) (M := M) hDim g
  obtain ⟨ρCore, _, hρCore, _, hCore⟩ :=
    invPerturbH2_norm (I := I) (M := M) hDim g
  let ρ : ℝ := min ρLip ρCore
  have hρ : 0 < ρ := lt_min hρLip hρCore
  refine ⟨ρ, C, hρ, hC, ?_⟩
  intro T U gT gU hTtie hUtie hT hU
  let TH2 :=
    ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T
  let UH2 :=
    ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U
  have hTLip : ‖TH2‖ ≤ ρLip :=
    hT.trans (min_le_left ρLip ρCore)
  have hULip : ‖UH2‖ ≤ ρLip :=
    hU.trans (min_le_left ρLip ρCore)
  have hTCore : ‖TH2‖ ≤ ρCore :=
    hT.trans (min_le_right ρLip ρCore)
  have hUCore : ‖UH2‖ ≤ ρCore :=
    hU.trans (min_le_right ρLip ρCore)
  have hTsmall :
      ‖perturbH2 (I := I) (M := M) g TH2‖ < 1 :=
    (hCore TH2 hTCore).1.trans_lt (by norm_num)
  have hUsmall :
      ‖perturbH2 (I := I) (M := M) g UH2‖ < 1 :=
    (hCore UH2 hUCore).1.trans_lt (by norm_num)
  have hTcore :=
    lowRegPrincipal_core (I := I) (M := M)
      hDim g gT T hTtie hTsmall
  have hUcore :=
    lowRegPrincipal_core (I := I) (M := M)
      hDim g gU U hUtie hUsmall
  rw [← hTcore, ← hUcore]
  exact hLip TH2 UH2 hTLip hULip

private theorem reindex_jet_c2
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (A : SmoothCcTensor g r s) (ρ : Equiv.Perm (Fin r)) :
    c2JetSq (I := I) (M := M) g
        (reindexCoeffGen (I := I) (M := M) g r s A ρ) =
      c2JetSq (I := I) (M := M) g A := by
  unfold c2JetSq
  apply Finset.sum_congr rfl
  intro i _
  rw [iteratedCovGrad_reindexCoeffGen (I := I) (M := M) g r s A ρ i,
    norm_reindexCoeffGen_eq (I := I) (M := M) g r (s + i)]

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
private theorem reindex_sub_c2
    (g : SmoothRiemannianMetric I M)
    (A B : SmoothCcTensor g 4 2) (ρ : Equiv.Perm (Fin 4)) :
    reindexCoeffGen (I := I) (M := M) g 4 2 (A - B) ρ =
      reindexCoeffGen (I := I) (M := M) g 4 2 A ρ -
        reindexCoeffGen (I := I) (M := M) g 4 2 B ρ := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [SmoothCcTensor.toSection_sub, ContMDiffSection.coe_sub, Pi.sub_apply,
    reindexCoeffGen_toSection, reindexCoeffGen_toSection,
    reindexCoeffGen_toSection, SmoothCcTensor.toSection_sub,
    ContMDiffSection.coe_sub, Pi.sub_apply]
  apply ContinuousLinearMap.ext
  intro D
  rw [ContinuousLinearMap.sub_apply, reindexCoeffFibGen_apply,
    reindexCoeffFibGen_apply, reindexCoeffFibGen_apply,
    ContinuousLinearMap.sub_apply]

set_option linter.unusedSectionVars false in
set_option backward.isDefEq.respectTransparency false in
private theorem pure_eq_trace_c2
    (g gm : SmoothRiemannianMetric I M) :
    ricciArmPrincipalCoeffPure (I := I) (M := M) g gm =
      pureTrace (I := I) (M := M) g gm 2 := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [ricciArmPrincipalCoeffPure_toSection, pureTrace_toSection]

private theorem pcc_pair_eq
    (g gT gU : SmoothRiemannianMetric I M) :
    deTurckPrincipalCometricCoeff (I := I) (M := M) g gT -
        deTurckPrincipalCometricCoeff (I := I) (M := M) g gU =
      pureTrace (I := I) (M := M) g gT 2 -
        pureTrace (I := I) (M := M) g gU 2 := by
  rw [deTurckPrincipalCometricCoeff, deTurckPrincipalCometricCoeff,
    pure_eq_trace_c2 (I := I) (M := M) g gT,
    pure_eq_trace_c2 (I := I) (M := M) g g,
    pure_eq_trace_c2 (I := I) (M := M) g gU]
  abel

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 1600000 in
private lemma trace_base_eq
    (g gm : SmoothRiemannianMetric I M) :
    traceHessianCoeff (I := I) (M := M) g gm -
        traceHessianCoeff (I := I) (M := M) g g =
      reindexCoeffGen (I := I) (M := M) g 4 2
        (deTurckPrincipalCometricCoeff (I := I) (M := M) g gm)
        traceHessianSlotPerm := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [SmoothCcTensor.toSection_sub, ContMDiffSection.coe_sub, Pi.sub_apply,
    traceHessianCoeff_toSection, traceHessianCoeff_toSection,
    reindexCoeffGen_toSection]
  apply ContinuousLinearMap.ext
  intro D
  rw [ContinuousLinearMap.sub_apply, reindexCoeffFibGen_apply,
    deTurckPrincipalCometricCoeff_toSection_clm_eq,
    ContinuousLinearMap.sub_apply, traceHessianFib, traceHessianFib,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    domDomCongrFib_apply]

private noncomputable def pccDiff
    (g gT gU : SmoothRiemannianMetric I M) : SmoothCcTensor g 4 2 :=
  deTurckPrincipalCometricCoeff (I := I) (M := M) g gT -
    deTurckPrincipalCometricCoeff (I := I) (M := M) g gU

private noncomputable def traceDiff
    (g gT gU : SmoothRiemannianMetric I M) : SmoothCcTensor g 4 2 :=
  reindexCoeffGen (I := I) (M := M) g 4 2
    (pccDiff (I := I) (M := M) g gT gU) traceHessianSlotPerm

private noncomputable def ricci2Diff
    (g gT gU : SmoothRiemannianMetric I M) : SmoothCcTensor g 4 2 :=
  let D := pccDiff (I := I) (M := M) g gT gU
  reindexCoeffGen (I := I) (M := M) g 4 2 D koszulSlotPerm +
    reindexCoeffGen (I := I) (M := M) g 4 2
      (rsDomDomCongrSection (I := I) (M := M) g 4 2
        (Equiv.swap (0 : Fin 2) 1) D) koszulSlotPerm -
    D

private noncomputable def phiDiff
    (g gT gU : SmoothRiemannianMetric I M) : SmoothCcTensor g 4 2 :=
  let H := traceDiff (I := I) (M := M) g gT gU
  reindexCoeffGen (I := I) (M := M) g 4 2 H
      (traceHessianSlotPerm⁻¹ * deTurckLieArm2DivSlotPermA) +
    reindexCoeffGen (I := I) (M := M) g 4 2 H
      (traceHessianSlotPerm⁻¹ * deTurckLieArm2DivSlotPermAT) -
    ricci2Diff (I := I) (M := M) g gT gU

set_option linter.unusedSectionVars false in
private theorem sub_base_alg
    {V : Type*} [AddCommGroup V] (A B Z : V) :
    A - B = (A - Z) - (B - Z) := by
  abel

set_option linter.unusedSectionVars false in
private theorem pair_base_alg
    {V : Type*} [AddCommGroup V] (A B Z : V) :
    (A + A) - (B + B) =
      ((A - Z) + (A - Z)) - ((B - Z) + (B - Z)) := by
  abel

set_option linter.unusedSectionVars false in
private theorem tri_sub_alg
    {V : Type*} [AddCommGroup V] (A B C D E F : V) :
    (A + B - C) - (D + E - F) =
      (A - D) + (B - E) - (C - F) := by
  abel

set_option linter.unusedSectionVars false in
private theorem kernel_pair_alg
    {V : Type*} [AddCommGroup V]
    (AT BT AU BU K LT PT RT LU PU RU : V)
    (hT : AT + BT - K = LT + (PT - K) + RT)
    (hU : AU + BU - K = LU + (PU - K) + RU) :
    (AT + BT) - (AU + BU) =
      (LT - LU) + (PT - PU) + (RT - RU) := by
  calc
    (AT + BT) - (AU + BU) =
        (AT + BT - K) - (AU + BU - K) := by abel
    _ = (LT + (PT - K) + RT) -
        (LU + (PU - K) + RU) := by rw [hT, hU]
    _ = (LT - LU) + (PT - PU) + (RT - RU) := by abel

set_option maxHeartbeats 200000 in
private theorem phiMet_diff_eq
    (g g_bg gT gU : SmoothRiemannianMetric I M) :
    deTurckPhiMetTotal (I := I) (M := M) g g_bg gT -
        deTurckPhiMetTotal (I := I) (M := M) g g_bg gU =
      phiDiff (I := I) (M := M) g gT gU := by
  let PT := deTurckPrincipalCometricCoeff (I := I) (M := M) g gT
  let PU := deTurckPrincipalCometricCoeff (I := I) (M := M) g gU
  let D := pccDiff (I := I) (M := M) g gT gU
  let HT := traceHessianCoeff (I := I) (M := M) g gT
  let HU := traceHessianCoeff (I := I) (M := M) g gU
  let H0 := traceHessianCoeff (I := I) (M := M) g g
  let RT := ricciArmPrincipalCoeff (I := I) (M := M) g gT
  let RU := ricciArmPrincipalCoeff (I := I) (M := M) g gU
  let R0 := ricciArmPrincipalCoeff (I := I) (M := M) g g
  have hHT0 : HT - H0 =
      reindexCoeffGen (I := I) (M := M) g 4 2 PT
        traceHessianSlotPerm := by
    simpa only [HT, H0, PT] using
      trace_base_eq (I := I) (M := M) g gT
  have hHU0 : HU - H0 =
      reindexCoeffGen (I := I) (M := M) g 4 2 PU
        traceHessianSlotPerm := by
    simpa only [HU, H0, PU] using
      trace_base_eq (I := I) (M := M) g gU
  have hH : HT - HU =
      traceDiff (I := I) (M := M) g gT gU := by
    rw [sub_base_alg HT HU H0,
      hHT0, hHU0]
    rw [← reindex_sub_c2]
    rfl
  have hRT0 : (RT - R0) + (RT - R0) =
      reindexCoeffGen (I := I) (M := M) g 4 2 PT koszulSlotPerm +
        reindexCoeffGen (I := I) (M := M) g 4 2
          (rsDomDomCongrSection (I := I) (M := M) g 4 2
            (Equiv.swap (0 : Fin 2) 1) PT) koszulSlotPerm -
        PT := by
    simpa only [RT, R0, PT] using
      ricci2_pcc_eq (I := I) (M := M) g gT
  have hRU0 : (RU - R0) + (RU - R0) =
      reindexCoeffGen (I := I) (M := M) g 4 2 PU koszulSlotPerm +
        reindexCoeffGen (I := I) (M := M) g 4 2
          (rsDomDomCongrSection (I := I) (M := M) g 4 2
            (Equiv.swap (0 : Fin 2) 1) PU) koszulSlotPerm -
        PU := by
    simpa only [RU, R0, PU] using
      ricci2_pcc_eq (I := I) (M := M) g gU
  have hR : (RT + RT) - (RU + RU) =
      ricci2Diff (I := I) (M := M) g gT gU := by
    rw [pair_base_alg RT RU R0,
      hRT0, hRU0]
    dsimp only [ricci2Diff, D, pccDiff]
    rw [reindex_sub_c2, rsperm_sub_c2, reindex_sub_c2]
    exact tri_sub_alg _ _ _ _ _ _
  calc
    deTurckPhiMetTotal (I := I) (M := M) g g_bg gT -
          deTurckPhiMetTotal (I := I) (M := M) g g_bg gU =
        (reindexCoeffGen (I := I) (M := M) g 4 2 HT
            (traceHessianSlotPerm⁻¹ * deTurckLieArm2DivSlotPermA) -
          reindexCoeffGen (I := I) (M := M) g 4 2 HU
            (traceHessianSlotPerm⁻¹ * deTurckLieArm2DivSlotPermA)) +
        (reindexCoeffGen (I := I) (M := M) g 4 2 HT
            (traceHessianSlotPerm⁻¹ * deTurckLieArm2DivSlotPermAT) -
          reindexCoeffGen (I := I) (M := M) g 4 2 HU
            (traceHessianSlotPerm⁻¹ * deTurckLieArm2DivSlotPermAT)) -
        ((RT + RT) - (RU + RU)) := by
      rw [phiMet_reindex (I := I) (M := M) g g_bg gT,
        phiMet_reindex (I := I) (M := M) g g_bg gU]
      dsimp only [HT, HU, RT, RU]
      exact tri_sub_alg _ _ _ _ _ _
    _ =
        reindexCoeffGen (I := I) (M := M) g 4 2 (HT - HU)
            (traceHessianSlotPerm⁻¹ * deTurckLieArm2DivSlotPermA) +
          reindexCoeffGen (I := I) (M := M) g 4 2 (HT - HU)
            (traceHessianSlotPerm⁻¹ * deTurckLieArm2DivSlotPermAT) -
          ((RT + RT) - (RU + RU)) := by
      rw [reindex_sub_c2, reindex_sub_c2]
    _ = phiDiff (I := I) (M := M) g gT gU := by
      rw [hH, hR]
      rfl

set_option maxHeartbeats 400000 in
private theorem phiMet_pair_lip
    (hDim : Module.finrank ℝ E = 3)
    (g g_bg : SmoothRiemannianMetric I M) :
    ∃ ρ C : ℝ, 0 < ρ ∧ 0 ≤ C ∧
      ∀ (T U : SmoothCcTensor g 0 2)
        (gT gU : SmoothRiemannianMetric I M),
        (∀ (y : M) (v w : TangentSpace I y),
          gT.inner y v w =
            g.inner y v w + ccTensorBilinSymm (I := I) g T y v w) →
        (∀ (y : M) (v w : TangentSpace I y),
          gU.inner y v w =
            g.inner y v w + ccTensorBilinSymm (I := I) g U y v w) →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ ≤ ρ →
        c2JetSq (I := I) (M := M) g
            (deTurckPhiMetTotal (I := I) (M := M) g g_bg gT -
              deTurckPhiMetTotal (I := I) (M := M) g g_bg gU) ≤
          (C * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
            (T - U)‖) ^ 2 := by
  obtain ⟨ρ, Ct, hρ, hCt, htrace⟩ :=
    trace24_h2_lip (I := I) (M := M) hDim g
  let C : ℝ := 6 * Ct
  have hC : 0 ≤ C := mul_nonneg (by norm_num) hCt
  refine ⟨ρ, C, hρ, hC, ?_⟩
  intro T U gT gU hTtie hUtie hT hU
  let D := pccDiff (I := I) (M := M) g gT gU
  let Hc := traceDiff (I := I) (M := M) g gT gU
  let A := reindexCoeffGen (I := I) (M := M) g 4 2 Hc
    (traceHessianSlotPerm⁻¹ * deTurckLieArm2DivSlotPermA)
  let B := reindexCoeffGen (I := I) (M := M) g 4 2 Hc
    (traceHessianSlotPerm⁻¹ * deTurckLieArm2DivSlotPermAT)
  let R1 := reindexCoeffGen (I := I) (M := M) g 4 2 D koszulSlotPerm
  let R2 := reindexCoeffGen (I := I) (M := M) g 4 2
    (rsDomDomCongrSection (I := I) (M := M) g 4 2
      (Equiv.swap (0 : Fin 2) 1) D) koszulSlotPerm
  let R := R1 + R2 - D
  let N := ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U)‖
  have hN : 0 ≤ N := norm_nonneg _
  have hD :
      c2JetSq (I := I) (M := M) g D ≤ (Ct * N) ^ 2 := by
    have h := (htrace T U gT gU hTtie hUtie hT hU).1
    dsimp only [D, pccDiff]
    rw [pcc_pair_eq (I := I) (M := M) g gT gU]
    simpa only [N] using h
  have hHc :
      c2JetSq (I := I) (M := M) g Hc =
        c2JetSq (I := I) (M := M) g D := by
    dsimp only [Hc, traceDiff]
    exact reindex_jet_c2 (I := I) (M := M) g 4 2 D traceHessianSlotPerm
  have hA :
      c2JetSq (I := I) (M := M) g A =
        c2JetSq (I := I) (M := M) g D := by
    dsimp only [A]
    rw [reindex_jet_c2, hHc]
  have hB :
      c2JetSq (I := I) (M := M) g B =
        c2JetSq (I := I) (M := M) g D := by
    dsimp only [B]
    rw [reindex_jet_c2, hHc]
  have hR1 :
      c2JetSq (I := I) (M := M) g R1 =
        c2JetSq (I := I) (M := M) g D := by
    exact reindex_jet_c2 (I := I) (M := M) g 4 2 D koszulSlotPerm
  have hR2 :
      c2JetSq (I := I) (M := M) g R2 =
        c2JetSq (I := I) (M := M) g D := by
    dsimp only [R2]
    rw [reindex_jet_c2, rsperm_jet_c2]
  have hAB :
      c2JetSq (I := I) (M := M) g (A + B) ≤
        4 * c2JetSq (I := I) (M := M) g D := by
    calc
      _ ≤ 2 * (c2JetSq (I := I) (M := M) g A +
          c2JetSq (I := I) (M := M) g B) :=
        jet3_add_c2 (I := I) (M := M) g A B
      _ = 4 * c2JetSq (I := I) (M := M) g D := by
        rw [hA, hB]
        ring
  have hR12 :
      c2JetSq (I := I) (M := M) g (R1 + R2) ≤
        4 * c2JetSq (I := I) (M := M) g D := by
    calc
      _ ≤ 2 * (c2JetSq (I := I) (M := M) g R1 +
          c2JetSq (I := I) (M := M) g R2) :=
        jet3_add_c2 (I := I) (M := M) g R1 R2
      _ = 4 * c2JetSq (I := I) (M := M) g D := by
        rw [hR1, hR2]
        ring
  have hR :
      c2JetSq (I := I) (M := M) g R ≤
        10 * c2JetSq (I := I) (M := M) g D := by
    dsimp only [R]
    calc
      _ ≤ 2 * (c2JetSq (I := I) (M := M) g (R1 + R2) +
          c2JetSq (I := I) (M := M) g D) :=
        jet3_sub_c2 (I := I) (M := M) g (R1 + R2) D
      _ ≤ 2 * (4 * c2JetSq (I := I) (M := M) g D +
          c2JetSq (I := I) (M := M) g D) :=
        mul_le_mul_of_nonneg_left
          (add_le_add hR12 le_rfl) (by norm_num)
      _ = 10 * c2JetSq (I := I) (M := M) g D := by ring
  rw [phiMet_diff_eq (I := I) (M := M) g g_bg gT gU]
  change c2JetSq (I := I) (M := M) g (A + B - R) ≤
    (C * N) ^ 2
  calc
    c2JetSq (I := I) (M := M) g (A + B - R) ≤
        2 * (c2JetSq (I := I) (M := M) g (A + B) +
          c2JetSq (I := I) (M := M) g R) :=
      jet3_sub_c2 (I := I) (M := M) g (A + B) R
    _ ≤ 2 * (4 * c2JetSq (I := I) (M := M) g D +
        10 * c2JetSq (I := I) (M := M) g D) :=
      mul_le_mul_of_nonneg_left (add_le_add hAB hR) (by norm_num)
    _ = 28 * c2JetSq (I := I) (M := M) g D := by ring
    _ ≤ 28 * (Ct * N) ^ 2 :=
      mul_le_mul_of_nonneg_left hD (by norm_num)
    _ ≤ (C * N) ^ 2 := by
      dsimp only [C]
      nlinarith [mul_nonneg hCt hN]

private noncomputable def c2Kernel
    (g g_bg : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g 0 2) {δ : ℝ}
    (hTδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hZδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ) :
    ℝ → SmoothCcTensor g 4 2 :=
  fun s =>
    rhsRefoldTop (I := I) (M := M) g g_bg T hTδ hZδ s +
      LowBaseInternal.rhsSelfTop (I := I) (M := M) g T hTδ hZδ s

private theorem c2Kernel_joint
    (g g_bg : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g 0 2) {δ : ℝ}
    (hδlt : δ < 1)
    (hTδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hZδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ) :
    linearizedRicciThreeArmHjoint (I := I) (M := M) g 4
      (c2Kernel (I := I) (M := M) g g_bg T hTδ hZδ)
      (δ := δ) (δ' := δ) := by
  exact threeArmJoint_add (I := I) (M := M) g _ _
    (rhsRefoldTop_joint (I := I) (M := M)
      g g_bg T hδlt hTδ hZδ)
    (LowBaseInternal.selfTop_joint (I := I) (M := M)
      g T hTδ hZδ)

private theorem c2Kernel_pair_eq
    (g g_bg : SmoothRiemannianMetric I M)
    (T U : SmoothCcTensor g 0 2) {δ : ℝ}
    (hTδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hUδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g U) δ)
    (hZδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ)
    (s : ℝ) :
    let gmT := realizedFam (I := I) g T 0 hTδ hZδ s
    let gmU := realizedFam (I := I) g U 0 hUδ hZδ s
    c2Kernel (I := I) (M := M) g g_bg T hTδ hZδ s -
        c2Kernel (I := I) (M := M) g g_bg U hUδ hZδ s =
      (lieRefold2 (I := I) (M := M) g T hTδ hZδ s -
          lieRefold2 (I := I) (M := M) g U hUδ hZδ s) +
        (deTurckPhiMetTotal (I := I) (M := M) g g_bg gmT -
          deTurckPhiMetTotal (I := I) (M := M) g g_bg gmU) +
        ((-2 * s : ℝ) •
            LowBaseInternal.ricciTop (I := I) (M := M) g gmT T -
          (-2 * s : ℝ) •
            LowBaseInternal.ricciTop (I := I) (M := M) g gmU U) := by
  dsimp only
  apply kernel_pair_alg
    (K := deTurckPhiMetTotal (I := I) (M := M) g g_bg g)
  · exact LowBaseInternal.topKernel_eq
      (I := I) (M := M) g g_bg T hTδ hZδ s
  · exact LowBaseInternal.topKernel_eq
      (I := I) (M := M) g g_bg U hUδ hZδ s

/-- The canonical two-endpoint top coefficient is integrated from this
jointly smooth pointwise family difference. -/
noncomputable def c2Diff
    (g g_bg : SmoothRiemannianMetric I M)
    (T U : SmoothCcTensor g 0 2) {δ : ℝ}
    (hδlt : δ < 1)
    (hTδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hUδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g U) δ)
    (hZδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ) :
    SmoothCcTensor g 4 2 :=
  pathIntegralCoeffField (I := I) (M := M) g 4 2
    (fun s =>
      c2Kernel (I := I) (M := M) g g_bg T hTδ hZδ s -
        c2Kernel (I := I) (M := M) g g_bg U hUδ hZδ s)
    (realizedSmallSet (δ := δ) (δ' := δ))
    realizedSmallSet_isOpen
    (by
      rw [Set.uIcc_of_le zero_le_one]
      exact Icc_subset_realizedSmallSet hδlt hδlt)
    (threeArmJoint_sub (I := I) (M := M) g _ _
      (c2Kernel_joint (I := I) (M := M)
        g g_bg T hδlt hTδ hZδ)
      (c2Kernel_joint (I := I) (M := M)
        g g_bg U hδlt hUδ hZδ))

set_option maxHeartbeats 600000 in
set_option synthInstance.maxHeartbeats 1200000 in
/-- The difference of the canonical low-base second-order coefficients is the
path integral of the explicit two-endpoint top-family difference. -/
theorem lowC2_sub
    (g g_bg : SmoothRiemannianMetric I M)
    (T U : SmoothCcTensor g 0 2) {δ : ℝ}
    (hδlt : δ < 1)
    (hTδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hUδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g U) δ)
    (hZδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ) :
    (lowBaseData (I := I) (M := M)
        g g_bg T hδlt hTδ hZδ).C2 -
        (lowBaseData (I := I) (M := M)
          g g_bg U hδlt hUδ hZδ).C2 =
      c2Diff (I := I) (M := M)
        g g_bg T U hδlt hTδ hUδ hZδ := by
  classical
  letI : NormedAddCommGroup (TensorRSModel 4 2 ℝ E) :=
    Tensor0SBundle.tensorRSModel_normedAddCommGroup 4 2
  letI : NormedAddGroup (TensorRSModel 4 2 ℝ E) :=
    NormedAddCommGroup.toNormedAddGroup
  letI : ENormedAddMonoid (TensorRSModel 4 2 ℝ E) :=
    NormedAddGroup.toENormedAddMonoid
  letI : IsTopologicalAddGroup (TensorRSModel 4 2 ℝ E) :=
    SeminormedAddCommGroup.toIsTopologicalAddGroup
  rw [LowBaseInternal.c2_eq, LowBaseInternal.c2_eq]
  apply cc_toFun_ext (I := I) (M := M) g
  funext x
  have hSI : Set.uIcc (0 : ℝ) 1 ⊆
      realizedSmallSet (δ := δ) (δ' := δ) := by
    rw [Set.uIcc_of_le zero_le_one]
    exact Icc_subset_realizedSmallSet hδlt hδlt
  have hRTcont :=
    jointContMDiff_toModel_continuous_slice
      (I := I) g 4 2
      (rhsRefoldTop (I := I) (M := M) g g_bg T hTδ hZδ)
      (realizedSmallSet (δ := δ) (δ' := δ))
      (rhsRefoldTop_joint (I := I) (M := M)
        g g_bg T hδlt hTδ hZδ) x
  have hRUcont :=
    jointContMDiff_toModel_continuous_slice
      (I := I) g 4 2
      (rhsRefoldTop (I := I) (M := M) g g_bg U hUδ hZδ)
      (realizedSmallSet (δ := δ) (δ' := δ))
      (rhsRefoldTop_joint (I := I) (M := M)
        g g_bg U hδlt hUδ hZδ) x
  have hSTcont :=
    jointContMDiff_toModel_continuous_slice
      (I := I) g 4 2
      (LowBaseInternal.rhsSelfTop (I := I) (M := M) g T hTδ hZδ)
      (realizedSmallSet (δ := δ) (δ' := δ))
      (LowBaseInternal.selfTop_joint (I := I) (M := M)
        g T hTδ hZδ) x
  have hSUcont :=
    jointContMDiff_toModel_continuous_slice
      (I := I) g 4 2
      (LowBaseInternal.rhsSelfTop (I := I) (M := M) g U hUδ hZδ)
      (realizedSmallSet (δ := δ) (δ' := δ))
      (LowBaseInternal.selfTop_joint (I := I) (M := M)
        g U hUδ hZδ) x
  have hRTint : IntervalIntegrable
      (fun s : ℝ => TensorRSSpace.toModel
        ((rhsRefoldTop (I := I) (M := M)
          g g_bg T hTδ hZδ s).toSection x))
      MeasureTheory.volume 0 1 :=
    (hRTcont.mono hSI).intervalIntegrable
  have hRUint : IntervalIntegrable
      (fun s : ℝ => TensorRSSpace.toModel
        ((rhsRefoldTop (I := I) (M := M)
          g g_bg U hUδ hZδ s).toSection x))
      MeasureTheory.volume 0 1 :=
    (hRUcont.mono hSI).intervalIntegrable
  have hSTint : IntervalIntegrable
      (fun s : ℝ => TensorRSSpace.toModel
        ((LowBaseInternal.rhsSelfTop (I := I) (M := M)
          g T hTδ hZδ s).toSection x))
      MeasureTheory.volume 0 1 :=
    (hSTcont.mono hSI).intervalIntegrable
  have hSUint : IntervalIntegrable
      (fun s : ℝ => TensorRSSpace.toModel
        ((LowBaseInternal.rhsSelfTop (I := I) (M := M)
          g U hUδ hZδ s).toSection x))
      MeasureTheory.volume 0 1 :=
    (hSUcont.mono hSI).intervalIntegrable
  simp only [SmoothCcTensor.toFun_apply, LowBaseInternal.selfTopInt,
    rhsRefoldTopInt, c2Diff,
    c2Kernel, pathIntegralCoeffField_toModel,
    SmoothCcTensor.toSection_add, SmoothCcTensor.toSection_sub,
    ContMDiffSection.coe_add, ContMDiffSection.coe_sub,
    Pi.add_apply, Pi.sub_apply, TensorRSSpace.toModel_add,
    TensorRSSpace.toModel_sub]
  have hAddT := intervalIntegral.integral_add hRTint hSTint
  have hAddU := intervalIntegral.integral_add hRUint hSUint
  have hSub := intervalIntegral.integral_sub
    (hRTint.add hSTint) (hRUint.add hSUint)
  have hPair := congrArg₂
    (fun a b : TensorRSModel 4 2 ℝ E => a - b)
    hAddT.symm hAddU.symm
  calc
    _ = ((∫ s : ℝ in 0..1,
            TensorRSSpace.toModel
              ((rhsRefoldTop (I := I) (M := M)
                g g_bg T hTδ hZδ s).toSection x)) +
          (∫ s : ℝ in 0..1,
            TensorRSSpace.toModel
              ((LowBaseInternal.rhsSelfTop (I := I) (M := M)
                g T hTδ hZδ s).toSection x))) -
        ((∫ s : ℝ in 0..1,
            TensorRSSpace.toModel
              ((rhsRefoldTop (I := I) (M := M)
                g g_bg U hUδ hZδ s).toSection x)) +
          (∫ s : ℝ in 0..1,
            TensorRSSpace.toModel
              ((LowBaseInternal.rhsSelfTop (I := I) (M := M)
                g U hUδ hZδ s).toSection x))) := by
      abel
    _ = _ := hPair.trans hSub.symm

set_option maxHeartbeats 1000000 in
private theorem kernel_h2_lip
    (hDim : Module.finrank ℝ E = 3)
    (g g_bg : SmoothRiemannianMetric I M) :
    ∃ ρ C : ℝ, 0 < ρ ∧ 0 ≤ C ∧
      ∀ (T U : SmoothCcTensor g 0 2) {δ : ℝ},
        δ < 1 →
        (hTδ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ) →
        (hUδ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g U) δ) →
        (hZδ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ) →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ ≤ ρ →
        ∀ {s : ℝ}, s ∈ Set.Icc (0 : ℝ) 1 →
          c2JetSq (I := I) (M := M) g
              (c2Kernel (I := I) (M := M)
                  g g_bg T hTδ hZδ s -
                c2Kernel (I := I) (M := M)
                  g g_bg U hUδ hZδ s) ≤
            (C * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
              (T - U)‖) ^ 2 := by
  obtain ⟨ρl, Cl, hρl, hCl, hlie⟩ :=
    lieRefold_pair_lip (I := I) (M := M) hDim g
  obtain ⟨ρp, Cp, hρp, hCp, hphi⟩ :=
    phiMet_pair_lip (I := I) (M := M) hDim g g_bg
  obtain ⟨ρr, Cr, hρr, hCr, hricci⟩ :=
    ricciRad_pair (I := I) (M := M) hDim g
  let ρ : ℝ := min (min ρl ρp) ρr
  let K : ℝ := Cl + Cp + Cr
  let C : ℝ := 4 * K
  have hρ : 0 < ρ := lt_min (lt_min hρl hρp) hρr
  have hK : 0 ≤ K := add_nonneg (add_nonneg hCl hCp) hCr
  have hC : 0 ≤ C := mul_nonneg (by norm_num) hK
  refine ⟨ρ, C, hρ, hC, ?_⟩
  intro T U δ hδlt hTδ hUδ hZδ hT hU s hs
  let N : ℝ :=
    ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U)‖
  let P : SmoothCcTensor g 0 2 := s • T
  let Q : SmoothCcTensor g 0 2 := s • U
  let gmT : SmoothRiemannianMetric I M :=
    realizedFam (I := I) g T 0 hTδ hZδ s
  let gmU : SmoothRiemannianMetric I M :=
    realizedFam (I := I) g U 0 hUδ hZδ s
  let L : SmoothCcTensor g 4 2 :=
    lieRefold2 (I := I) (M := M) g T hTδ hZδ s -
      lieRefold2 (I := I) (M := M) g U hUδ hZδ s
  let Φ : SmoothCcTensor g 4 2 :=
    deTurckPhiMetTotal (I := I) (M := M) g g_bg gmT -
      deTurckPhiMetTotal (I := I) (M := M) g g_bg gmU
  let R : SmoothCcTensor g 4 2 :=
    (-2 * s : ℝ) •
        LowBaseInternal.ricciTop (I := I) (M := M) g gmT T -
      (-2 * s : ℝ) •
        LowBaseInternal.ricciTop (I := I) (M := M) g gmU U
  have hN : 0 ≤ N := norm_nonneg _
  have hsabs : ‖s‖ ≤ (1 : ℝ) := by
    rw [Real.norm_eq_abs, abs_of_nonneg hs.1]
    exact hs.2
  have hs_mem : s ∈ realizedSmallSet (δ := δ) (δ' := δ) :=
    Icc_subset_realizedSmallSet hδlt hδlt hs
  have hPtie : ∀ (x : M) (v w : TangentSpace I x),
      gmT.inner x v w =
        g.inner x v w + ccTensorBilinSymm (I := I) g P x v w := by
    intro x v w
    simpa only [gmT, P, convexPerturbation, smul_zero, zero_add] using
      realizedFam_inner_of_mem
        (I := I) g T 0 hTδ hZδ hs_mem x v w
  have hQtie : ∀ (x : M) (v w : TangentSpace I x),
      gmU.inner x v w =
        g.inner x v w + ccTensorBilinSymm (I := I) g Q x v w := by
    intro x v w
    simpa only [gmU, Q, convexPerturbation, smul_zero, zero_add] using
      realizedFam_inner_of_mem
        (I := I) g U 0 hUδ hZδ hs_mem x v w
  have hPnorm :
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) P‖ ≤ ρp := by
    rw [show P = s • T from rfl, ccTensorToHs_smul, norm_smul]
    calc
      ‖s‖ * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤
          1 * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ :=
        mul_le_mul_of_nonneg_right hsabs (norm_nonneg _)
      _ ≤ ρ := by simpa using hT
      _ ≤ ρp := (min_le_left _ _).trans (min_le_right _ _)
  have hQnorm :
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) Q‖ ≤ ρp := by
    rw [show Q = s • U from rfl, ccTensorToHs_smul, norm_smul]
    calc
      ‖s‖ * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ ≤
          1 * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ :=
        mul_le_mul_of_nonneg_right hsabs (norm_nonneg _)
      _ ≤ ρ := by simpa using hU
      _ ≤ ρp := (min_le_left _ _).trans (min_le_right _ _)
  have hPQ :
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (P - Q)‖ ≤ N := by
    have heq : P - Q = s • (T - U) := by
      dsimp only [P, Q]
      module
    rw [heq, ccTensorToHs_smul, norm_smul]
    exact (mul_le_mul_of_nonneg_right hsabs hN).trans (by simp)
  have hL : c2JetSq (I := I) (M := M) g L ≤ (Cl * N) ^ 2 := by
    simpa only [L, N] using
      hlie T U hδlt hTδ hUδ hZδ
        (hT.trans ((min_le_left _ _).trans (min_le_left _ _)))
        (hU.trans ((min_le_left _ _).trans (min_le_left _ _))) hs
  have hΦraw :
      c2JetSq (I := I) (M := M) g Φ ≤
        (Cp * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
          (P - Q)‖) ^ 2 := by
    simpa only [Φ] using
      hphi P Q gmT gmU hPtie hQtie hPnorm hQnorm
  have hΦ : c2JetSq (I := I) (M := M) g Φ ≤ (Cp * N) ^ 2 :=
    hΦraw.trans
      (pow_le_pow_left₀
        (mul_nonneg hCp (norm_nonneg _))
        (mul_le_mul_of_nonneg_left hPQ hCp) 2)
  have hR : c2JetSq (I := I) (M := M) g R ≤ (Cr * N) ^ 2 := by
    simpa only [R, gmT, gmU, N] using
      hricci T U hδlt hTδ hUδ hZδ
        (hT.trans (min_le_right _ _))
        (hU.trans (min_le_right _ _)) hs
  have hClK : Cl * N ≤ K * N := by
    apply mul_le_mul_of_nonneg_right _ hN
    dsimp only [K]
    linarith
  have hCpK : Cp * N ≤ K * N := by
    apply mul_le_mul_of_nonneg_right _ hN
    dsimp only [K]
    linarith
  have hCrK : Cr * N ≤ K * N := by
    apply mul_le_mul_of_nonneg_right _ hN
    dsimp only [K]
    linarith
  have hL' : c2JetSq (I := I) (M := M) g L ≤ (K * N) ^ 2 :=
    hL.trans (pow_le_pow_left₀ (mul_nonneg hCl hN) hClK 2)
  have hΦ' : c2JetSq (I := I) (M := M) g Φ ≤ (K * N) ^ 2 :=
    hΦ.trans (pow_le_pow_left₀ (mul_nonneg hCp hN) hCpK 2)
  have hR' : c2JetSq (I := I) (M := M) g R ≤ (K * N) ^ 2 :=
    hR.trans (pow_le_pow_left₀ (mul_nonneg hCr hN) hCrK 2)
  rw [c2Kernel_pair_eq (I := I) (M := M)
    g g_bg T U hTδ hUδ hZδ s]
  change c2JetSq (I := I) (M := M) g (L + Φ + R) ≤ (C * N) ^ 2
  calc
    c2JetSq (I := I) (M := M) g (L + Φ + R) ≤
        2 * (c2JetSq (I := I) (M := M) g (L + Φ) +
          c2JetSq (I := I) (M := M) g R) :=
      jet3_add_c2 (I := I) (M := M) g (L + Φ) R
    _ ≤ 2 * (2 * (c2JetSq (I := I) (M := M) g L +
          c2JetSq (I := I) (M := M) g Φ) +
        c2JetSq (I := I) (M := M) g R) := by
      exact mul_le_mul_of_nonneg_left
        (add_le_add
          (jet3_add_c2 (I := I) (M := M) g L Φ) le_rfl)
        (by norm_num)
    _ ≤ 2 * (2 * ((K * N) ^ 2 + (K * N) ^ 2) +
        (K * N) ^ 2) := by
      gcongr
    _ = 10 * (K * N) ^ 2 := by ring
    _ ≤ (4 * K * N) ^ 2 := by
      nlinarith [sq_nonneg (K * N)]
    _ = (C * N) ^ 2 := by
      dsimp only [C]

set_option maxHeartbeats 1000000 in
private theorem c2Diff_h2
    (hDim : Module.finrank ℝ E = 3)
    (g g_bg : SmoothRiemannianMetric I M) :
    ∃ ρ C : ℝ, 0 < ρ ∧ 0 ≤ C ∧
      ∀ (T U : SmoothCcTensor g 0 2) {δ : ℝ},
        (hδlt : δ < 1) →
        (hTδ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ) →
        (hUδ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g U) δ) →
        (hZδ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ) →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ ≤ ρ →
        lowJetSq (I := I) (M := M) g 2
            (c2Diff (I := I) (M := M)
              g g_bg T U (δ := δ) hδlt hTδ hUδ hZδ) ≤
          (C * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
            (T - U)‖) ^ 2 := by
  obtain ⟨ρ, C, hρ, hC, hkernel⟩ :=
    kernel_h2_lip (I := I) (M := M) hDim g g_bg
  refine ⟨ρ, C, hρ, hC, ?_⟩
  intro T U δ hδlt hTδ hUδ hZδ hT hU
  let Φ : ℝ → SmoothCcTensor g 4 2 := fun s =>
    c2Kernel (I := I) (M := M) g g_bg T hTδ hZδ s -
      c2Kernel (I := I) (M := M) g g_bg U hUδ hZδ s
  let S : Set ℝ := realizedSmallSet (δ := δ) (δ' := δ)
  let N : ℝ :=
    ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U)‖
  have hN : 0 ≤ N := norm_nonneg _
  have hCN : 0 ≤ C * N := mul_nonneg hC hN
  have hSI : Set.uIcc (0 : ℝ) 1 ⊆ S := by
    dsimp only [S]
    rw [Set.uIcc_of_le zero_le_one]
    exact Icc_subset_realizedSmallSet hδlt hδlt
  have hjoint :
      linearizedRicciThreeArmHjoint (I := I) (M := M) g 4 Φ
        (δ := δ) (δ' := δ) := by
    dsimp only [Φ]
    exact threeArmJoint_sub (I := I) (M := M) g _ _
      (c2Kernel_joint (I := I) (M := M)
        g g_bg T hδlt hTδ hZδ)
      (c2Kernel_joint (I := I) (M := M)
        g g_bg U hδlt hUδ hZδ)
  have hpath := path_jetL2_le (I := I) (M := M)
    g 4 2 2 Φ S realizedSmallSet_isOpen hSI hjoint
    (B := C * N) hCN
    (fun s hs => by
      simpa only [Φ, c2JetSq, N] using
        hkernel T U hδlt hTδ hUδ hZδ hT hU hs)
  simpa only [lowJetSq, c2Diff, Φ, S, N, Nat.reduceAdd] using hpath

set_option maxHeartbeats 1000000 in
/-- On a common spectral `H²` ball, the complete canonical second-order
coefficient is Lipschitz in both pointwise fibre norm and its intrinsic
coefficient `H²` jet. -/
theorem c2_pair_lip
    (hDim : Module.finrank ℝ E = 3)
    (g g_bg : SmoothRiemannianMetric I M) :
    ∃ ρ C : ℝ, 0 < ρ ∧ 0 ≤ C ∧
      ∀ (T U : SmoothCcTensor g 0 2) {δ : ℝ},
        (hδlt : δ < 1) →
        (hTδ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ) →
        (hUδ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g U) δ) →
        (hZδ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ) →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ ≤ ρ →
        let AT := lowBaseData (I := I) (M := M)
          g g_bg T hδlt hTδ hZδ
        let AU := lowBaseData (I := I) (M := M)
          g g_bg U hδlt hUδ hZδ
        (∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g 4 2 x
              ((AT.C2 - AU.C2).toSection x) ≤
            (C * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
              (T - U)‖) ^ 2) ∧
        lowJetSq (I := I) (M := M) g 2 (AT.C2 - AU.C2) ≤
          (C * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
            (T - U)‖) ^ 2 := by
  obtain ⟨ρ, C0, hρ, hC0, hdiff⟩ :=
    c2Diff_h2 (I := I) (M := M) hDim g g_bg
  obtain ⟨Cpt, hCpt, hpoint⟩ :=
    jet3_fiber_c2 (I := I) (M := M) hDim g 4 2
  let C : ℝ := (Cpt + 1) * C0
  have hC : 0 ≤ C :=
    mul_nonneg (add_nonneg hCpt (by norm_num)) hC0
  refine ⟨ρ, C, hρ, hC, ?_⟩
  intro T U δ hδlt hTδ hUδ hZδ hT hU
  dsimp only
  let D : SmoothCcTensor g 4 2 :=
    (lowBaseData (I := I) (M := M)
        g g_bg T hδlt hTδ hZδ).C2 -
      (lowBaseData (I := I) (M := M)
        g g_bg U hδlt hUδ hZδ).C2
  let N : ℝ :=
    ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U)‖
  have hN : 0 ≤ N := norm_nonneg _
  have hD_eq :
      D = c2Diff (I := I) (M := M)
        g g_bg T U hδlt hTδ hUδ hZδ := by
    exact lowC2_sub (I := I) (M := M)
      g g_bg T U hδlt hTδ hUδ hZδ
  have hDjet0 :
      lowJetSq (I := I) (M := M) g 2 D ≤ (C0 * N) ^ 2 := by
    rw [hD_eq]
    simpa only [N] using
      hdiff T U hδlt hTδ hUδ hZδ hT hU
  have hC0C : C0 ≤ C := by
    dsimp only [C]
    nlinarith [mul_nonneg hCpt hC0]
  have hptC : Cpt * C0 ≤ C := by
    dsimp only [C]
    ring_nf
    exact le_add_of_nonneg_right hC0
  have hjet :
      lowJetSq (I := I) (M := M) g 2 D ≤ (C * N) ^ 2 :=
    hDjet0.trans
      (pow_le_pow_left₀ (mul_nonneg hC0 hN)
        (mul_le_mul_of_nonneg_right hC0C hN) 2)
  refine ⟨?_, ?_⟩
  · intro x
    calc
      riemannianFiberNormSq (I := I) (M := M) g 4 2 x
          (D.toSection x) ≤
        Cpt ^ 2 * c2JetSq (I := I) (M := M) g D :=
          hpoint D x
      _ ≤ Cpt ^ 2 * (C0 * N) ^ 2 :=
        mul_le_mul_of_nonneg_left
          (by simpa only [lowJetSq, c2JetSq, Nat.reduceAdd] using hDjet0)
          (sq_nonneg Cpt)
      _ = (Cpt * C0 * N) ^ 2 := by ring
      _ ≤ (C * N) ^ 2 :=
        pow_le_pow_left₀
          (mul_nonneg (mul_nonneg hCpt hC0) hN)
          (mul_le_mul_of_nonneg_right hptC hN) 2
  · simpa only [D, N] using hjet

set_option maxHeartbeats 1000000 in
/-- On the same spectral `H²` ball, both adjacent-scale realizations of the
complete canonical second-order action are Lipschitz in the state. -/
theorem a2_pair_lip
    (hDim : Module.finrank ℝ E = 3)
    (g g_bg : SmoothRiemannianMetric I M) :
    ∃ ρ C : ℝ, 0 < ρ ∧ 0 ≤ C ∧
      ∀ (T U : SmoothCcTensor g 0 2) {δ : ℝ},
        (hδlt : δ < 1) →
        (hTδ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ) →
        (hUδ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g U) δ) →
        (hZδ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ) →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ ≤ ρ →
        let AT := lowBaseData (I := I) (M := M)
          g g_bg T hδlt hTδ hZδ
        let AU := lowBaseData (I := I) (M := M)
          g g_bg U hδlt hUδ hZδ
        ‖AT.a2Hi (I := I) (M := M) -
            AU.a2Hi (I := I) (M := M)‖ ≤
          C * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
            (T - U)‖ ∧
        ‖AT.a2Lo (I := I) (M := M) -
            AU.a2Lo (I := I) (M := M)‖ ≤
          C * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
            (T - U)‖ := by
  obtain ⟨ρ, C2, hρ, hC2, hc2⟩ :=
    c2_pair_lip (I := I) (M := M) hDim g g_bg
  obtain ⟨Ca, hCa, ha2⟩ :=
    a2_diff (I := I) (M := M) hDim g
  let C : ℝ := Ca * C2
  have hC : 0 ≤ C := mul_nonneg hCa hC2
  refine ⟨ρ, C, hρ, hC, ?_⟩
  intro T U δ hδlt hTδ hUδ hZδ hT hU
  dsimp only
  let AT : LowBaseActionData g :=
    lowBaseData (I := I) (M := M)
      g g_bg T hδlt hTδ hZδ
  let AU : LowBaseActionData g :=
    lowBaseData (I := I) (M := M)
      g g_bg U hδlt hUδ hZδ
  let N : ℝ :=
    ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U)‖
  have hN : 0 ≤ N := norm_nonneg _
  obtain ⟨hpoint, hjet⟩ :=
    hc2 T U hδlt hTδ hUδ hZδ hT hU
  have hR : 0 ≤ C2 * N := mul_nonneg hC2 hN
  obtain ⟨hHi, hLo⟩ :=
    ha2 AT AU (C2 * N) hR
      (by simpa only [AT, AU, N] using hpoint)
      (by simpa only [AT, AU, N] using hjet)
  refine ⟨hHi.trans_eq ?_, hLo.trans_eq ?_⟩
  · dsimp only [C]
    ring
  · dsimp only [C]
    ring

namespace LowBaseInternal

/-- The full moving Lie-covariant trace pair is locally Lipschitz on the
metric `H²` perturbation ball in its intrinsic coefficient `H²` jet. -/
theorem pairTrace_pair_h2
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ C : ℝ, 0 < ρ ∧ 0 ≤ C ∧
      ∀ (T U : SmoothCcTensor g 0 2)
        (gT gU : SmoothRiemannianMetric I M),
        (∀ (y : M) (v w : TangentSpace I y),
          gT.inner y v w =
            g.inner y v w +
              ccTensorBilinSymm (I := I) g T y v w) →
        (∀ (y : M) (v w : TangentSpace I y),
          gU.inner y v w =
            g.inner y v w +
              ccTensorBilinSymm (I := I) g U y v w) →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ ≤ ρ →
        lowJetSq (I := I) (M := M) g 2
            (lieCovPair (I := I) (M := M) g gT -
              lieCovPair (I := I) (M := M) g gU) ≤
          (C * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
            (T - U)‖) ^ 2 := by
  obtain ⟨ρ, C, hρ, hC, hpair⟩ :=
    pairTrace_h2_lip (I := I) (M := M) hDim g
  refine ⟨ρ, C, hρ, hC, ?_⟩
  intro T U gT gU hTtie hUtie hT hU
  simpa only [lowJetSq, c2JetSq, Nat.reduceAdd] using
    hpair T U gT gU hTtie hUtie hT hU

/-- On the same local metric ball, the full moving Lie-covariant trace pair
has a uniform intrinsic coefficient `H²` jet bound. -/
theorem pairTrace_bdd_h2
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ B : ℝ, 0 < ρ ∧ 0 ≤ B ∧
      ∀ (T : SmoothCcTensor g 0 2)
        (gT : SmoothRiemannianMetric I M),
        (∀ (y : M) (v w : TangentSpace I y),
          gT.inner y v w =
            g.inner y v w +
              ccTensorBilinSymm (I := I) g T y v w) →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρ →
        lowJetSq (I := I) (M := M) g 2
            (lieCovPair (I := I) (M := M) g gT) ≤ B ^ 2 := by
  obtain ⟨ρ, B, hρ, hB, hbdd⟩ :=
    pairTrace_h2_bdd (I := I) (M := M) hDim g
  refine ⟨ρ, B, hρ, hB, ?_⟩
  intro T gT hTtie hT
  simpa only [lowJetSq, c2JetSq, Nat.reduceAdd] using
    hbdd T gT hTtie hT

set_option maxHeartbeats 1600000 in
private theorem trace1_h2_lip
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ C : ℝ, 0 < ρ ∧ 0 ≤ C ∧
      ∀ (T U : SmoothCcTensor g 0 2)
        (gT gU : SmoothRiemannianMetric I M),
        (∀ (y : M) (v w : TangentSpace I y),
          gT.inner y v w =
            g.inner y v w +
              ccTensorBilinSymm (I := I) g T y v w) →
        (∀ (y : M) (v w : TangentSpace I y),
          gU.inner y v w =
            g.inner y v w +
              ccTensorBilinSymm (I := I) g U y v w) →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ ≤ ρ →
        c2JetSq (I := I) (M := M) g
            (pureTrace (I := I) (M := M) g gT 1 -
              pureTrace (I := I) (M := M) g gU 1) ≤
          (C * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
            (T - U)‖) ^ 2 := by
  classical
  obtain ⟨ρ, Cinv, hρ, hCinv, hinv⟩ :=
    invCoeff_h2_lip (I := I) (M := M) hDim g
  obtain ⟨C₁, hC₁, happ₁⟩ :=
    appRS_h2_h2_h2 (I := I) (M := M) hDim g 3 3 1
  let F₁ : SmoothCcTensor g 3 1 :=
    cometricDoubleTraceField (I := I) g 1
  let J₁ : ℝ := c2JetSq (I := I) (M := M) g F₁
  let A₁ : ℝ := Real.sqrt J₁
  let K₁ : ℝ := C₁ * A₁ * (2 * Cinv)
  have hJ₁ : 0 ≤ J₁ := by
    exact jet3_nonneg_c2 (I := I) (M := M) g F₁
  have hA₁ : 0 ≤ A₁ := Real.sqrt_nonneg _
  have hA₁sq : A₁ ^ 2 = J₁ := by
    simpa only [A₁] using Real.sq_sqrt hJ₁
  have hK₁ : 0 ≤ K₁ := by
    dsimp only [K₁]
    exact mul_nonneg (mul_nonneg hC₁ hA₁)
      (mul_nonneg (by norm_num) hCinv)
  refine ⟨ρ, K₁, hρ, hK₁, ?_⟩
  intro T U gT gU hTtie hUtie hT hU
  set N : ℝ :=
    ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U)‖
  let Λ :=
    gInvDiffRaisedEndoField (I := I) g gT -
      gInvDiffRaisedEndoField (I := I) g gU
  let D₁ : SmoothCcTensor g 3 3 :=
    slotInsertEndoCc (I := I) (M := M) g 2 Λ
  have hN : 0 ≤ N := norm_nonneg _
  have hinvJet :
      c2JetSq (I := I) (M := M) g
          (gInvDiffSlotCoeff (I := I) g gT -
            gInvDiffSlotCoeff (I := I) g gU) ≤
        (Cinv * N) ^ 2 := by
    simpa only [c2JetSq, N] using
      (hinv T U gT gU hTtie hUtie hT hU).2
  have hslot1 :
      slotInsertEndoCc (I := I) (M := M) g 1 Λ =
        gInvDiffSlotCoeff (I := I) g gT -
          gInvDiffSlotCoeff (I := I) g gU := by
    dsimp only [Λ]
    rw [slotInsertEndoCc_sub,
      ← gInvDiffSlotCoeff_eq_slotInsertEndoCc (I := I) g gT,
      ← gInvDiffSlotCoeff_eq_slotInsertEndoCc (I := I) g gU]
  have hD₁ :
      c2JetSq (I := I) (M := M) g D₁ ≤
        (2 * Cinv * N) ^ 2 := by
    calc
      c2JetSq (I := I) (M := M) g D₁ ≤
          (Module.finrank ℝ E : ℝ) *
            c2JetSq (I := I) (M := M) g
              (slotInsertEndoCc (I := I) (M := M) g 1 Λ) := by
        simpa only [D₁, Nat.reduceAdd] using
          insertSucc_jet_c2 (I := I) (M := M) g 1 Λ
      _ = 3 * c2JetSq (I := I) (M := M) g
            (gInvDiffSlotCoeff (I := I) g gT -
              gInvDiffSlotCoeff (I := I) g gU) := by
        rw [hDim, hslot1]
        norm_num
      _ ≤ 3 * (Cinv * N) ^ 2 :=
        mul_le_mul_of_nonneg_left hinvJet (by norm_num)
      _ ≤ (2 * Cinv * N) ^ 2 := by nlinarith [sq_nonneg (Cinv * N)]
  have htrace₁ :
      pureTrace (I := I) (M := M) g gT 1 -
          pureTrace (I := I) (M := M) g gU 1 =
        appCcRS (I := I) (M := M) g 3 3 1 F₁ D₁ := by
    rw [pureTrace_split (I := I) (M := M) g gT 1,
      pureTrace_split (I := I) (M := M) g gU 1]
    calc
      (appCcRS (I := I) (M := M) g 3 3 1 F₁
            (slotInsertEndoCc (I := I) (M := M) g 2
              (gInvDiffRaisedEndoField (I := I) g gT)) + F₁) -
          (appCcRS (I := I) (M := M) g 3 3 1 F₁
            (slotInsertEndoCc (I := I) (M := M) g 2
              (gInvDiffRaisedEndoField (I := I) g gU)) + F₁) =
        appCcRS (I := I) (M := M) g 3 3 1 F₁
            (slotInsertEndoCc (I := I) (M := M) g 2
              (gInvDiffRaisedEndoField (I := I) g gT)) -
          appCcRS (I := I) (M := M) g 3 3 1 F₁
            (slotInsertEndoCc (I := I) (M := M) g 2
              (gInvDiffRaisedEndoField (I := I) g gU)) := by abel
      _ = appCcRS (I := I) (M := M) g 3 3 1 F₁ D₁ := by
        rw [← appCcRS_sub_right]
        congr 1
        dsimp only [D₁, Λ]
        rw [slotInsertEndoCc_sub]
  have hF₁ : c2JetSq (I := I) (M := M) g F₁ ≤ A₁ ^ 2 := by
    rw [hA₁sq]
  rw [htrace₁]
  have h := happ₁ F₁ D₁ A₁ (2 * Cinv * N)
    hA₁ (mul_nonneg (mul_nonneg (by norm_num) hCinv) hN) hF₁ hD₁
  simpa only [c2JetSq, K₁] using
    (show (C₁ * A₁ * (2 * Cinv * N)) ^ 2 =
        (K₁ * N) ^ 2 by
      dsimp only [K₁]
      ring ▸ h)

/-- Two-state `H²` modulus of the moving one-slot trace coefficient. -/
theorem trace1_pair_h2
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ C : ℝ, 0 < ρ ∧ 0 ≤ C ∧
      ∀ (T U : SmoothCcTensor g 0 2)
        (gT gU : SmoothRiemannianMetric I M),
        (∀ (y : M) (v w : TangentSpace I y),
          gT.inner y v w =
            g.inner y v w +
              ccTensorBilinSymm (I := I) g T y v w) →
        (∀ (y : M) (v w : TangentSpace I y),
          gU.inner y v w =
            g.inner y v w +
              ccTensorBilinSymm (I := I) g U y v w) →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ ≤ ρ →
        lowJetSq (I := I) (M := M) g 2
            (pureTrace (I := I) (M := M) g gT 1 -
              pureTrace (I := I) (M := M) g gU 1) ≤
          (C * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
            (T - U)‖) ^ 2 := by
  obtain ⟨ρ, C, hρ, hC, htrace⟩ :=
    trace1_h2_lip (I := I) (M := M) hDim g
  refine ⟨ρ, C, hρ, hC, ?_⟩
  intro T U gT gU hTtie hUtie hT hU
  simpa only [lowJetSq, c2JetSq, Nat.reduceAdd] using
    htrace T U gT gU hTtie hUtie hT hU

/-- On the same local metric ball, the moving one-slot trace coefficient
has a uniform intrinsic `H²` jet bound. -/
theorem trace1_h2_bdd
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ B : ℝ, 0 < ρ ∧ 0 ≤ B ∧
      ∀ (T : SmoothCcTensor g 0 2)
        (gT : SmoothRiemannianMetric I M),
        (∀ (y : M) (v w : TangentSpace I y),
          gT.inner y v w =
            g.inner y v w +
              ccTensorBilinSymm (I := I) g T y v w) →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρ →
        lowJetSq (I := I) (M := M) g 2
            (pureTrace (I := I) (M := M) g gT 1) ≤ B ^ 2 := by
  obtain ⟨ρ, C, hρ, hC, hlip⟩ :=
    trace1_pair_h2 (I := I) (M := M) hDim g
  let P : SmoothRiemannianMetric I M → SmoothCcTensor g 3 1 :=
    fun gm => pureTrace (I := I) (M := M) g gm 1
  let J : ℝ := lowJetSq (I := I) (M := M) g 2 (P g)
  let Z : ℝ := 2 * ((C * ρ) ^ 2 + J)
  let B : ℝ := Real.sqrt Z
  have hJ : 0 ≤ J := by
    dsimp only [J, P]
    exact Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hZ : 0 ≤ Z := by
    dsimp only [Z]
    exact mul_nonneg (by norm_num)
      (add_nonneg (sq_nonneg (C * ρ)) hJ)
  have hB : 0 ≤ B := Real.sqrt_nonneg _
  have hBsq : B ^ 2 = Z := by
    simpa only [B] using Real.sq_sqrt hZ
  refine ⟨ρ, B, hρ, hB, ?_⟩
  intro T gT hTtie hT
  have hzero_app : ∀ (y : M) (v w : TangentSpace I y),
      ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2) y v w = 0 := by
    intro y v w
    have hz : (0 : SmoothCcTensor g 0 2) =
        (0 : ℝ) • (0 : SmoothCcTensor g 0 2) :=
      (zero_smul ℝ _).symm
    rw [hz, ccTensorBilinSymm_smul]
    ring
  have hzero_tie : ∀ (y : M) (v w : TangentSpace I y),
      g.inner y v w =
        g.inner y v w +
          ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2) y v w := by
    intro y v w
    rw [hzero_app, add_zero]
  have hcc0 :
      ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
          (0 : SmoothCcTensor g 0 2) = 0 := by
    rw [show (0 : SmoothCcTensor g 0 2) =
      (0 : ℝ) • (0 : SmoothCcTensor g 0 2) by simp,
      ccTensorToHs_smul, zero_smul]
  have hzero_norm :
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
        (0 : SmoothCcTensor g 0 2)‖ ≤ ρ := by
    rw [hcc0, norm_zero]
    exact le_of_lt hρ
  have hraw := hlip T (0 : SmoothCcTensor g 0 2) gT g
    hTtie hzero_tie hT hzero_norm
  have hmul :
      C * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - 0)‖ ≤
        C * ρ := by
    rw [sub_zero]
    exact mul_le_mul_of_nonneg_left hT hC
  have hdiff :
      lowJetSq (I := I) (M := M) g 2 (P gT - P g) ≤
        (C * ρ) ^ 2 := by
    exact hraw.trans
      (pow_le_pow_left₀
        (mul_nonneg hC (norm_nonneg _)) hmul 2)
  rw [hBsq]
  calc
    lowJetSq (I := I) (M := M) g 2 (P gT) =
        c2JetSq (I := I) (M := M) g ((P gT - P g) + P g) := by
      rw [show (P gT - P g) + P g = P gT by abel]
      rfl
    _ ≤ 2 * (c2JetSq (I := I) (M := M) g (P gT - P g) +
          c2JetSq (I := I) (M := M) g (P g)) :=
      jet3_add_c2 (I := I) (M := M) g _ _
    _ ≤ 2 * ((C * ρ) ^ 2 + J) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      simpa only [lowJetSq, c2JetSq, Nat.reduceAdd, J] using
        add_le_add hdiff le_rfl
    _ = Z := rfl

/-- The moving two-slot trace coefficient is locally Lipschitz from the
metric `H²` perturbation ball to its intrinsic coefficient `H²` jet. -/
private theorem insert4_jet_c2
    (g : SmoothRiemannianMetric I M)
    (Λ : ContMDiffSection I (E →L[ℝ] E) ∞
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)) :
    c2JetSq (I := I) (M := M) g
        (slotInsertEndoCc (I := I) (M := M) g 4 Λ) ≤
      (Module.finrank ℝ E : ℝ) ^ 3 *
        c2JetSq (I := I) (M := M) g
          (slotInsertEndoCc (I := I) (M := M) g 1 Λ) := by
  have hfr : (0 : ℝ) ≤ Module.finrank ℝ E := Nat.cast_nonneg _
  calc
    c2JetSq (I := I) (M := M) g
        (slotInsertEndoCc (I := I) (M := M) g 4 Λ) ≤
      (Module.finrank ℝ E : ℝ) *
        c2JetSq (I := I) (M := M) g
          (slotInsertEndoCc (I := I) (M := M) g 3 Λ) :=
      insertSucc_jet_c2 (I := I) (M := M) g 3 Λ
    _ ≤ (Module.finrank ℝ E : ℝ) *
        ((Module.finrank ℝ E : ℝ) ^ 2 *
          c2JetSq (I := I) (M := M) g
            (slotInsertEndoCc (I := I) (M := M) g 1 Λ)) :=
      mul_le_mul_of_nonneg_left
        (insert3_jet_c2 (I := I) (M := M) g Λ) hfr
    _ = (Module.finrank ℝ E : ℝ) ^ 3 *
        c2JetSq (I := I) (M := M) g
          (slotInsertEndoCc (I := I) (M := M) g 1 Λ) := by ring

set_option maxHeartbeats 1600000 in
private theorem trace3_h2_lip
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ C : ℝ, 0 < ρ ∧ 0 ≤ C ∧
      ∀ (T U : SmoothCcTensor g 0 2)
        (gT gU : SmoothRiemannianMetric I M),
        (∀ (y : M) (v w : TangentSpace I y),
          gT.inner y v w =
            g.inner y v w +
              ccTensorBilinSymm (I := I) g T y v w) →
        (∀ (y : M) (v w : TangentSpace I y),
          gU.inner y v w =
            g.inner y v w +
              ccTensorBilinSymm (I := I) g U y v w) →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ ≤ ρ →
        c2JetSq (I := I) (M := M) g
            (pureTrace (I := I) (M := M) g gT 3 -
              pureTrace (I := I) (M := M) g gU 3) ≤
          (C * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
            (T - U)‖) ^ 2 := by
  classical
  obtain ⟨ρ, Cinv, hρ, hCinv, hinv⟩ :=
    invCoeff_h2_lip (I := I) (M := M) hDim g
  obtain ⟨C₃, hC₃, happ₃⟩ :=
    appRS_h2_h2_h2 (I := I) (M := M) hDim g 5 5 3
  let F₃ : SmoothCcTensor g 5 3 :=
    cometricDoubleTraceField (I := I) g 3
  let J₃ : ℝ := c2JetSq (I := I) (M := M) g F₃
  let A₃ : ℝ := Real.sqrt J₃
  let K₃ : ℝ := C₃ * A₃ * (6 * Cinv)
  have hJ₃ : 0 ≤ J₃ := by
    exact jet3_nonneg_c2 (I := I) (M := M) g F₃
  have hA₃ : 0 ≤ A₃ := Real.sqrt_nonneg _
  have hA₃sq : A₃ ^ 2 = J₃ := by
    simpa only [A₃] using Real.sq_sqrt hJ₃
  have hK₃ : 0 ≤ K₃ := by
    dsimp only [K₃]
    exact mul_nonneg (mul_nonneg hC₃ hA₃)
      (mul_nonneg (by norm_num) hCinv)
  refine ⟨ρ, K₃, hρ, hK₃, ?_⟩
  intro T U gT gU hTtie hUtie hT hU
  set N : ℝ :=
    ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U)‖
  let Λ :=
    gInvDiffRaisedEndoField (I := I) g gT -
      gInvDiffRaisedEndoField (I := I) g gU
  let D₃ : SmoothCcTensor g 5 5 :=
    slotInsertEndoCc (I := I) (M := M) g 4 Λ
  have hN : 0 ≤ N := norm_nonneg _
  have hinvJet :
      c2JetSq (I := I) (M := M) g
          (gInvDiffSlotCoeff (I := I) g gT -
            gInvDiffSlotCoeff (I := I) g gU) ≤
        (Cinv * N) ^ 2 := by
    simpa only [c2JetSq, N] using
      (hinv T U gT gU hTtie hUtie hT hU).2
  have hslot1 :
      slotInsertEndoCc (I := I) (M := M) g 1 Λ =
        gInvDiffSlotCoeff (I := I) g gT -
          gInvDiffSlotCoeff (I := I) g gU := by
    dsimp only [Λ]
    rw [slotInsertEndoCc_sub,
      ← gInvDiffSlotCoeff_eq_slotInsertEndoCc (I := I) g gT,
      ← gInvDiffSlotCoeff_eq_slotInsertEndoCc (I := I) g gU]
  have hD₃ :
      c2JetSq (I := I) (M := M) g D₃ ≤
        (6 * Cinv * N) ^ 2 := by
    calc
      c2JetSq (I := I) (M := M) g D₃ ≤
          (Module.finrank ℝ E : ℝ) ^ 3 *
            c2JetSq (I := I) (M := M) g
              (slotInsertEndoCc (I := I) (M := M) g 1 Λ) := by
        simpa only [D₃] using
          insert4_jet_c2 (I := I) (M := M) g Λ
      _ = 27 * c2JetSq (I := I) (M := M) g
            (gInvDiffSlotCoeff (I := I) g gT -
              gInvDiffSlotCoeff (I := I) g gU) := by
        rw [hDim, hslot1]
        norm_num
      _ ≤ 27 * (Cinv * N) ^ 2 :=
        mul_le_mul_of_nonneg_left hinvJet (by norm_num)
      _ ≤ (6 * Cinv * N) ^ 2 := by nlinarith [sq_nonneg (Cinv * N)]
  have htrace₃ :
      pureTrace (I := I) (M := M) g gT 3 -
          pureTrace (I := I) (M := M) g gU 3 =
        appCcRS (I := I) (M := M) g 5 5 3 F₃ D₃ := by
    rw [pureTrace_split (I := I) (M := M) g gT 3,
      pureTrace_split (I := I) (M := M) g gU 3]
    calc
      (appCcRS (I := I) (M := M) g 5 5 3 F₃
            (slotInsertEndoCc (I := I) (M := M) g 4
              (gInvDiffRaisedEndoField (I := I) g gT)) + F₃) -
          (appCcRS (I := I) (M := M) g 5 5 3 F₃
            (slotInsertEndoCc (I := I) (M := M) g 4
              (gInvDiffRaisedEndoField (I := I) g gU)) + F₃) =
        appCcRS (I := I) (M := M) g 5 5 3 F₃
            (slotInsertEndoCc (I := I) (M := M) g 4
              (gInvDiffRaisedEndoField (I := I) g gT)) -
          appCcRS (I := I) (M := M) g 5 5 3 F₃
            (slotInsertEndoCc (I := I) (M := M) g 4
              (gInvDiffRaisedEndoField (I := I) g gU)) := by abel
      _ = appCcRS (I := I) (M := M) g 5 5 3 F₃ D₃ := by
        rw [← appCcRS_sub_right]
        congr 1
        dsimp only [D₃, Λ]
        rw [slotInsertEndoCc_sub]
  have hF₃ : c2JetSq (I := I) (M := M) g F₃ ≤ A₃ ^ 2 := by
    rw [hA₃sq]
  rw [htrace₃]
  have h := happ₃ F₃ D₃ A₃ (6 * Cinv * N)
    hA₃ (mul_nonneg (mul_nonneg (by norm_num) hCinv) hN) hF₃ hD₃
  simpa only [c2JetSq, K₃] using
    (show (C₃ * A₃ * (6 * Cinv * N)) ^ 2 =
        (K₃ * N) ^ 2 by
      dsimp only [K₃]
      ring ▸ h)

/-- Two-state `H²` modulus of the moving three-slot trace coefficient. -/
theorem trace3_pair_h2
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ C : ℝ, 0 < ρ ∧ 0 ≤ C ∧
      ∀ (T U : SmoothCcTensor g 0 2)
        (gT gU : SmoothRiemannianMetric I M),
        (∀ (y : M) (v w : TangentSpace I y),
          gT.inner y v w =
            g.inner y v w +
              ccTensorBilinSymm (I := I) g T y v w) →
        (∀ (y : M) (v w : TangentSpace I y),
          gU.inner y v w =
            g.inner y v w +
              ccTensorBilinSymm (I := I) g U y v w) →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ ≤ ρ →
        lowJetSq (I := I) (M := M) g 2
            (pureTrace (I := I) (M := M) g gT 3 -
              pureTrace (I := I) (M := M) g gU 3) ≤
          (C * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
            (T - U)‖) ^ 2 := by
  obtain ⟨ρ, C, hρ, hC, htrace⟩ :=
    trace3_h2_lip (I := I) (M := M) hDim g
  refine ⟨ρ, C, hρ, hC, ?_⟩
  intro T U gT gU hTtie hUtie hT hU
  simpa only [lowJetSq, c2JetSq, Nat.reduceAdd] using
    htrace T U gT gU hTtie hUtie hT hU

/-- On the same local metric ball, the moving three-slot trace coefficient
has a uniform intrinsic `H²` jet bound. -/
theorem trace3_h2_bdd
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ B : ℝ, 0 < ρ ∧ 0 ≤ B ∧
      ∀ (T : SmoothCcTensor g 0 2)
        (gT : SmoothRiemannianMetric I M),
        (∀ (y : M) (v w : TangentSpace I y),
          gT.inner y v w =
            g.inner y v w +
              ccTensorBilinSymm (I := I) g T y v w) →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρ →
        lowJetSq (I := I) (M := M) g 2
            (pureTrace (I := I) (M := M) g gT 3) ≤ B ^ 2 := by
  obtain ⟨ρ, C, hρ, hC, hlip⟩ :=
    trace3_pair_h2 (I := I) (M := M) hDim g
  let P : SmoothRiemannianMetric I M → SmoothCcTensor g 5 3 :=
    fun gm => pureTrace (I := I) (M := M) g gm 3
  let J : ℝ := lowJetSq (I := I) (M := M) g 2 (P g)
  let Z : ℝ := 2 * ((C * ρ) ^ 2 + J)
  let B : ℝ := Real.sqrt Z
  have hJ : 0 ≤ J := by
    dsimp only [J, P]
    exact Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hZ : 0 ≤ Z := by
    dsimp only [Z]
    exact mul_nonneg (by norm_num)
      (add_nonneg (sq_nonneg (C * ρ)) hJ)
  have hB : 0 ≤ B := Real.sqrt_nonneg _
  have hBsq : B ^ 2 = Z := by
    simpa only [B] using Real.sq_sqrt hZ
  refine ⟨ρ, B, hρ, hB, ?_⟩
  intro T gT hTtie hT
  have hzero_app : ∀ (y : M) (v w : TangentSpace I y),
      ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2) y v w = 0 := by
    intro y v w
    have hz : (0 : SmoothCcTensor g 0 2) =
        (0 : ℝ) • (0 : SmoothCcTensor g 0 2) :=
      (zero_smul ℝ _).symm
    rw [hz, ccTensorBilinSymm_smul]
    ring
  have hzero_tie : ∀ (y : M) (v w : TangentSpace I y),
      g.inner y v w =
        g.inner y v w +
          ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2) y v w := by
    intro y v w
    rw [hzero_app, add_zero]
  have hcc0 :
      ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
          (0 : SmoothCcTensor g 0 2) = 0 := by
    rw [show (0 : SmoothCcTensor g 0 2) =
      (0 : ℝ) • (0 : SmoothCcTensor g 0 2) by simp,
      ccTensorToHs_smul, zero_smul]
  have hzero_norm :
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
        (0 : SmoothCcTensor g 0 2)‖ ≤ ρ := by
    rw [hcc0, norm_zero]
    exact le_of_lt hρ
  have hraw := hlip T (0 : SmoothCcTensor g 0 2) gT g
    hTtie hzero_tie hT hzero_norm
  have hmul :
      C * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - 0)‖ ≤
        C * ρ := by
    rw [sub_zero]
    exact mul_le_mul_of_nonneg_left hT hC
  have hdiff :
      lowJetSq (I := I) (M := M) g 2 (P gT - P g) ≤
        (C * ρ) ^ 2 := by
    exact hraw.trans
      (pow_le_pow_left₀
        (mul_nonneg hC (norm_nonneg _)) hmul 2)
  rw [hBsq]
  calc
    lowJetSq (I := I) (M := M) g 2 (P gT) =
        c2JetSq (I := I) (M := M) g ((P gT - P g) + P g) := by
      rw [show (P gT - P g) + P g = P gT by abel]
      rfl
    _ ≤ 2 * (c2JetSq (I := I) (M := M) g (P gT - P g) +
          c2JetSq (I := I) (M := M) g (P g)) :=
      jet3_add_c2 (I := I) (M := M) g _ _
    _ ≤ 2 * ((C * ρ) ^ 2 + J) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      simpa only [lowJetSq, c2JetSq, Nat.reduceAdd, J] using
        add_le_add hdiff le_rfl
    _ = Z := rfl

theorem trace2_pair_h2
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ C : ℝ, 0 < ρ ∧ 0 ≤ C ∧
      ∀ (T U : SmoothCcTensor g 0 2)
        (gT gU : SmoothRiemannianMetric I M),
        (∀ (y : M) (v w : TangentSpace I y),
          gT.inner y v w =
            g.inner y v w +
              ccTensorBilinSymm (I := I) g T y v w) →
        (∀ (y : M) (v w : TangentSpace I y),
          gU.inner y v w =
            g.inner y v w +
              ccTensorBilinSymm (I := I) g U y v w) →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ ≤ ρ →
        lowJetSq (I := I) (M := M) g 2
            (pureTrace (I := I) (M := M) g gT 2 -
              pureTrace (I := I) (M := M) g gU 2) ≤
          (C * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
            (T - U)‖) ^ 2 := by
  obtain ⟨ρ, C, hρ, hC, htrace⟩ :=
    trace24_h2_lip (I := I) (M := M) hDim g
  refine ⟨ρ, C, hρ, hC, ?_⟩
  intro T U gT gU hTtie hUtie hT hU
  simpa only [lowJetSq, c2JetSq, Nat.reduceAdd] using
    (htrace T U gT gU hTtie hUtie hT hU).1

/-- On the same local metric ball, the moving two-slot trace coefficient
has a uniform intrinsic `H²` jet bound. -/
theorem trace2_h2_bdd
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ B : ℝ, 0 < ρ ∧ 0 ≤ B ∧
      ∀ (T : SmoothCcTensor g 0 2)
        (gT : SmoothRiemannianMetric I M),
        (∀ (y : M) (v w : TangentSpace I y),
          gT.inner y v w =
            g.inner y v w +
              ccTensorBilinSymm (I := I) g T y v w) →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρ →
        lowJetSq (I := I) (M := M) g 2
            (pureTrace (I := I) (M := M) g gT 2) ≤ B ^ 2 := by
  obtain ⟨ρ, C, hρ, hC, hlip⟩ :=
    trace2_pair_h2 (I := I) (M := M) hDim g
  let P : SmoothRiemannianMetric I M → SmoothCcTensor g 4 2 :=
    fun gm => pureTrace (I := I) (M := M) g gm 2
  let J : ℝ := lowJetSq (I := I) (M := M) g 2 (P g)
  let Z : ℝ := 2 * ((C * ρ) ^ 2 + J)
  let B : ℝ := Real.sqrt Z
  have hJ : 0 ≤ J := by
    dsimp only [J, P]
    exact Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hZ : 0 ≤ Z := by
    dsimp only [Z]
    exact mul_nonneg (by norm_num)
      (add_nonneg (sq_nonneg (C * ρ)) hJ)
  have hB : 0 ≤ B := Real.sqrt_nonneg _
  have hBsq : B ^ 2 = Z := by
    simpa only [B] using Real.sq_sqrt hZ
  refine ⟨ρ, B, hρ, hB, ?_⟩
  intro T gT hTtie hT
  have hzero_app : ∀ (y : M) (v w : TangentSpace I y),
      ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2) y v w = 0 := by
    intro y v w
    have hz : (0 : SmoothCcTensor g 0 2) =
        (0 : ℝ) • (0 : SmoothCcTensor g 0 2) :=
      (zero_smul ℝ _).symm
    rw [hz, ccTensorBilinSymm_smul]
    ring
  have hzero_tie : ∀ (y : M) (v w : TangentSpace I y),
      g.inner y v w =
        g.inner y v w +
          ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2) y v w := by
    intro y v w
    rw [hzero_app, add_zero]
  have hcc0 :
      ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
          (0 : SmoothCcTensor g 0 2) = 0 := by
    rw [show (0 : SmoothCcTensor g 0 2) =
      (0 : ℝ) • (0 : SmoothCcTensor g 0 2) by simp,
      ccTensorToHs_smul, zero_smul]
  have hzero_norm :
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
        (0 : SmoothCcTensor g 0 2)‖ ≤ ρ := by
    rw [hcc0, norm_zero]
    exact le_of_lt hρ
  have hraw := hlip T (0 : SmoothCcTensor g 0 2) gT g
    hTtie hzero_tie hT hzero_norm
  have hmul :
      C * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - 0)‖ ≤
        C * ρ := by
    rw [sub_zero]
    exact mul_le_mul_of_nonneg_left hT hC
  have hdiff :
      lowJetSq (I := I) (M := M) g 2 (P gT - P g) ≤
        (C * ρ) ^ 2 := by
    exact hraw.trans
      (pow_le_pow_left₀
        (mul_nonneg hC (norm_nonneg _)) hmul 2)
  rw [hBsq]
  calc
    lowJetSq (I := I) (M := M) g 2 (P gT) =
        c2JetSq (I := I) (M := M) g ((P gT - P g) + P g) := by
      rw [show (P gT - P g) + P g = P gT by abel]
      rfl
    _ ≤ 2 * (c2JetSq (I := I) (M := M) g (P gT - P g) +
          c2JetSq (I := I) (M := M) g (P g)) :=
      jet3_add_c2 (I := I) (M := M) g _ _
    _ ≤ 2 * ((C * ρ) ^ 2 + J) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      simpa only [lowJetSq, c2JetSq, Nat.reduceAdd, J] using
        add_le_add hdiff le_rfl
    _ = Z := rfl

/-- Two-state `H²` modulus of the moving four-slot trace coefficient. -/
theorem trace4_pair_h2
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ C : ℝ, 0 < ρ ∧ 0 ≤ C ∧
      ∀ (T U : SmoothCcTensor g 0 2)
        (gT gU : SmoothRiemannianMetric I M),
        (∀ (y : M) (v w : TangentSpace I y),
          gT.inner y v w =
            g.inner y v w +
              ccTensorBilinSymm (I := I) g T y v w) →
        (∀ (y : M) (v w : TangentSpace I y),
          gU.inner y v w =
            g.inner y v w +
              ccTensorBilinSymm (I := I) g U y v w) →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ ≤ ρ →
        lowJetSq (I := I) (M := M) g 2
            (pureTrace (I := I) (M := M) g gT 4 -
              pureTrace (I := I) (M := M) g gU 4) ≤
          (C * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
            (T - U)‖) ^ 2 := by
  obtain ⟨ρ, C, hρ, hC, htrace⟩ :=
    trace24_h2_lip (I := I) (M := M) hDim g
  refine ⟨ρ, C, hρ, hC, ?_⟩
  intro T U gT gU hTtie hUtie hT hU
  simpa only [lowJetSq, c2JetSq, Nat.reduceAdd] using
    (htrace T U gT gU hTtie hUtie hT hU).2

/-- On the same local metric ball, the moving four-slot trace coefficient
has a uniform intrinsic `H²` jet bound. -/
theorem trace4_h2_bdd
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ B : ℝ, 0 < ρ ∧ 0 ≤ B ∧
      ∀ (T : SmoothCcTensor g 0 2)
        (gT : SmoothRiemannianMetric I M),
        (∀ (y : M) (v w : TangentSpace I y),
          gT.inner y v w =
            g.inner y v w +
              ccTensorBilinSymm (I := I) g T y v w) →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρ →
        lowJetSq (I := I) (M := M) g 2
            (pureTrace (I := I) (M := M) g gT 4) ≤ B ^ 2 := by
  obtain ⟨ρ, C, hρ, hC, hlip⟩ :=
    trace4_pair_h2 (I := I) (M := M) hDim g
  let P : SmoothRiemannianMetric I M → SmoothCcTensor g 6 4 :=
    fun gm => pureTrace (I := I) (M := M) g gm 4
  let J : ℝ := lowJetSq (I := I) (M := M) g 2 (P g)
  let Z : ℝ := 2 * ((C * ρ) ^ 2 + J)
  let B : ℝ := Real.sqrt Z
  have hJ : 0 ≤ J := by
    dsimp only [J, P]
    exact Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hZ : 0 ≤ Z := by
    dsimp only [Z]
    exact mul_nonneg (by norm_num)
      (add_nonneg (sq_nonneg (C * ρ)) hJ)
  have hB : 0 ≤ B := Real.sqrt_nonneg _
  have hBsq : B ^ 2 = Z := by
    simpa only [B] using Real.sq_sqrt hZ
  refine ⟨ρ, B, hρ, hB, ?_⟩
  intro T gT hTtie hT
  have hzero_app : ∀ (y : M) (v w : TangentSpace I y),
      ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2) y v w = 0 := by
    intro y v w
    have hz : (0 : SmoothCcTensor g 0 2) =
        (0 : ℝ) • (0 : SmoothCcTensor g 0 2) :=
      (zero_smul ℝ _).symm
    rw [hz, ccTensorBilinSymm_smul]
    ring
  have hzero_tie : ∀ (y : M) (v w : TangentSpace I y),
      g.inner y v w =
        g.inner y v w +
          ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2) y v w := by
    intro y v w
    rw [hzero_app, add_zero]
  have hcc0 :
      ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
          (0 : SmoothCcTensor g 0 2) = 0 := by
    rw [show (0 : SmoothCcTensor g 0 2) =
      (0 : ℝ) • (0 : SmoothCcTensor g 0 2) by simp,
      ccTensorToHs_smul, zero_smul]
  have hzero_norm :
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
        (0 : SmoothCcTensor g 0 2)‖ ≤ ρ := by
    rw [hcc0, norm_zero]
    exact le_of_lt hρ
  have hraw := hlip T (0 : SmoothCcTensor g 0 2) gT g
    hTtie hzero_tie hT hzero_norm
  have hmul :
      C * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - 0)‖ ≤
        C * ρ := by
    rw [sub_zero]
    exact mul_le_mul_of_nonneg_left hT hC
  have hdiff :
      lowJetSq (I := I) (M := M) g 2 (P gT - P g) ≤
        (C * ρ) ^ 2 := by
    exact hraw.trans
      (pow_le_pow_left₀
        (mul_nonneg hC (norm_nonneg _)) hmul 2)
  rw [hBsq]
  calc
    lowJetSq (I := I) (M := M) g 2 (P gT) =
        c2JetSq (I := I) (M := M) g ((P gT - P g) + P g) := by
      rw [show (P gT - P g) + P g = P gT by abel]
      rfl
    _ ≤ 2 * (c2JetSq (I := I) (M := M) g (P gT - P g) +
          c2JetSq (I := I) (M := M) g (P g)) :=
      jet3_add_c2 (I := I) (M := M) g _ _
    _ ≤ 2 * ((C * ρ) ^ 2 + J) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      simpa only [lowJetSq, c2JetSq, Nat.reduceAdd, J] using
        add_le_add hdiff le_rfl
    _ = Z := rfl

/-- The low connection insertion coefficient is locally Lipschitz from the
metric `H²` perturbation ball to its intrinsic coefficient `H²` jet. -/
theorem connLow_pair_h2
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ C : ℝ, 0 < ρ ∧ 0 ≤ C ∧
      ∀ (T U : SmoothCcTensor g 0 2)
        (gT gU : SmoothRiemannianMetric I M),
        (∀ (y : M) (v w : TangentSpace I y),
          gT.inner y v w =
            g.inner y v w +
              ccTensorBilinSymm (I := I) g T y v w) →
        (∀ (y : M) (v w : TangentSpace I y),
          gU.inner y v w =
            g.inner y v w +
              ccTensorBilinSymm (I := I) g U y v w) →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ ≤ ρ →
        lowJetSq (I := I) (M := M) g 2
            (connLowOp (I := I) (M := M) g gT -
              connLowOp (I := I) (M := M) g gU) ≤
          (C * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
            (T - U)‖) ^ 2 := by
  obtain ⟨ρ, C, hρ, hC, hlip⟩ :=
    connLow_pair (I := I) (M := M) hDim g
  refine ⟨ρ, C, hρ, hC, ?_⟩
  intro T U gT gU hTtie hUtie hT hU
  simpa only [lowJetSq, c2JetSq, Nat.reduceAdd] using
    hlip T U gT gU hTtie hUtie hT hU

/-- On the same local metric ball, the low connection insertion coefficient
has a uniform intrinsic `H²` jet bound. -/
theorem connLow_h2_bdd
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ B : ℝ, 0 < ρ ∧ 0 ≤ B ∧
      ∀ (T : SmoothCcTensor g 0 2)
        (gT : SmoothRiemannianMetric I M),
        (∀ (y : M) (v w : TangentSpace I y),
          gT.inner y v w =
            g.inner y v w +
              ccTensorBilinSymm (I := I) g T y v w) →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρ →
        lowJetSq (I := I) (M := M) g 2
            (connLowOp (I := I) (M := M) g gT) ≤ B ^ 2 := by
  obtain ⟨ρ, B, hρ, hB, hbdd⟩ :=
    connLow_bdd (I := I) (M := M) hDim g
  refine ⟨ρ, B, hρ, hB, ?_⟩
  intro T gT hTtie hT
  simpa only [lowJetSq, c2JetSq, Nat.reduceAdd] using
    hbdd T gT hTtie hT

end LowBaseInternal

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
