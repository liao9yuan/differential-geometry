import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.ChartVelocityCovGradTransfer

noncomputable section

set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000

open Bundle Manifold Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators Matrix

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.DeTurck.RicciLinearization
open DifferentialGeometry.PDE.DeTurck.DeTurckLinearization
open DifferentialGeometry.Analysis.Laplacian.TensorRegularity
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

def order1ModelCovectorVectorL : Tensor0SBundle.Tensor0SModel 1 ℝ E →L[ℝ] E :=
  ∑ j : Fin (Module.finrank ℝ E),
    (ContinuousLinearMap.smulRight
      (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 1 => E) ℝ
        (fun _ : Fin 1 => (chartModelBasis E) j))
      ((chartModelBasis E) j) :
        Tensor0SBundle.Tensor0SModel 1 ℝ E →L[ℝ] E)

def order1ModelCovectorVector (α : Tensor0SBundle.Tensor0SModel 1 ℝ E) : E :=
  order1ModelCovectorVectorL (E := E) α

set_option linter.unusedSectionVars false in
lemma order1ModelCovectorVector_eq (α : Tensor0SBundle.Tensor0SModel 1 ℝ E) :
    order1ModelCovectorVector (E := E) α =
      ∑ j : Fin (Module.finrank ℝ E),
        (α (fun _ : Fin 1 => (chartModelBasis E) j)) • (chartModelBasis E) j := by
  classical
  rw [order1ModelCovectorVector, order1ModelCovectorVectorL, ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [ContinuousLinearMap.smulRight_apply, ContinuousMultilinearMap.apply_apply]

def order1Slot0ModelContract
    (α : Tensor0SBundle.Tensor0SModel 1 ℝ E) :
    Tensor0SBundle.Tensor0SModel 3 ℝ E →L[ℝ] Tensor0SBundle.Tensor0SModel 2 ℝ E :=
  model_interior_product (𝕜 := ℝ) (E := E) 2 (order1ModelCovectorVector (E := E) α)

set_option linter.unusedSectionVars false in
lemma order1Slot0ModelContract_apply_raw
    (α : Tensor0SBundle.Tensor0SModel 1 ℝ E)
    (D : Tensor0SBundle.Tensor0SModel 3 ℝ E) (w : Fin 2 → E) :
    order1Slot0ModelContract (E := E) α D w =
      D (Fin.cons (order1ModelCovectorVector (E := E) α) w) := by
  rw [order1Slot0ModelContract, model_interior_product]
  change (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin 3 => E) ℝ D
        (order1ModelCovectorVector (E := E) α)) w = _
  rw [continuousMultilinearCurryLeftEquiv_apply]

set_option linter.unusedSectionVars false in
private lemma cmm3_slot_sum_smul
    (f : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) ℝ)
    (s : Fin 3) (c : Fin (Module.finrank ℝ E) → ℝ)
    (u : Fin (Module.finrank ℝ E) → E) (base : Fin 3 → E) :
    f (Function.update base s
        (∑ i : Fin (Module.finrank ℝ E), c i • u i)) =
      ∑ i : Fin (Module.finrank ℝ E), c i * f (Function.update base s (u i)) := by
  classical
  have hsum : f (Function.update base s
        (∑ i : Fin (Module.finrank ℝ E), c i • u i)) =
      ∑ i : Fin (Module.finrank ℝ E),
        f (Function.update base s (c i • u i)) := by
    rw [show (∑ i : Fin (Module.finrank ℝ E), c i • u i) =
        ∑ i ∈ (Finset.univ : Finset (Fin (Module.finrank ℝ E))), c i • u i from rfl]
    exact f.toMultilinearMap.map_update_sum Finset.univ s (fun i => c i • u i) base
  rw [hsum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [f.map_update_smul, smul_eq_mul]

set_option linter.unusedSectionVars false in
@[simp] lemma order1Slot0ModelContract_apply
    (α : Tensor0SBundle.Tensor0SModel 1 ℝ E)
    (D : Tensor0SBundle.Tensor0SModel 3 ℝ E) (w : Fin 2 → E) :
    order1Slot0ModelContract (E := E) α D w =
      ∑ j : Fin (Module.finrank ℝ E),
        α (fun _ : Fin 1 => (chartModelBasis E) j) *
          D (Fin.cons ((chartModelBasis E) j) w) := by
  classical
  rw [order1Slot0ModelContract_apply_raw, order1ModelCovectorVector_eq]
  have hbase0 : (Fin.cons (∑ j : Fin (Module.finrank ℝ E),
        (α (fun _ : Fin 1 => (chartModelBasis E) j)) • (chartModelBasis E) j) w :
          Fin 3 → E) =
      Function.update ((Fin.cons (0 : E) w : Fin 3 → E)) 0
        (∑ j : Fin (Module.finrank ℝ E),
          (α (fun _ : Fin 1 => (chartModelBasis E) j)) • (chartModelBasis E) j) := by
    funext z
    refine Fin.cases ?_ ?_ z
    · simp
    · intro i; simp
  rw [hbase0]
  rw [cmm3_slot_sum_smul (E := E) D 0 (fun j => α (fun _ : Fin 1 => (chartModelBasis E) j))
    (fun j => (chartModelBasis E) j) ((Fin.cons (0 : E) w : Fin 3 → E))]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  congr 1
  have hcons : Function.update ((Fin.cons (0 : E) w : Fin 3 → E)) 0 ((chartModelBasis E) j) =
      Fin.cons ((chartModelBasis E) j) w := by
    funext z
    refine Fin.cases ?_ ?_ z
    · simp
    · intro i; simp
  rw [hcons]

def order1Slot0ContractFib (g₀ : SmoothRiemannianMetric I M)
    (c : SmoothCcTensor g₀ 0 1) (x : M) :
    Tensor0SBundle.Tensor0SSpace 3 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x :=
  (Tensor0SBundle.tensor0SSpace_continuousLinearEquiv (I := I) 2 x).symm.toContinuousLinearMap.comp
    ((order1Slot0ModelContract (E := E)
        (unitModel (I := I) (M := M) g₀ 1 c x)).comp
      (Tensor0SBundle.tensor0SSpace_continuousLinearEquiv (I := I) 3 x).toContinuousLinearMap)

set_option linter.unusedSectionVars false in
@[simp] lemma order1Slot0ContractFib_toModel (g₀ : SmoothRiemannianMetric I M)
    (c : SmoothCcTensor g₀ 0 1) (x : M)
    (D : Tensor0SBundle.Tensor0SSpace 3 I x) :
    Tensor0SBundle.Tensor0SSpace.toModel (order1Slot0ContractFib (I := I) (M := M) g₀ c x D) =
      order1Slot0ModelContract (E := E)
        (unitModel (I := I) (M := M) g₀ 1 c x)
        (Tensor0SBundle.Tensor0SSpace.toModel D) := by
  rw [order1Slot0ContractFib]
  change order1Slot0ModelContract (E := E) _
      (Tensor0SBundle.Tensor0SSpace.toModel D) = _
  rfl

private lemma order1_rawComponent_zero_eq_unitModel_chartBasis
    (g : SmoothRiemannianMetric I M) (s : ℕ) (W : SmoothCcTensor g 0 s) (α : M)
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    tensorChartComponentRaw (I := I) (M := M) g 0 s W α ![] Jdx α =
      unitModel (I := I) (M := M) g s W α
        (fun j : Fin s => (chartModelBasis E) (Jdx j)) := by
  classical
  rw [tensorChartComponentRaw_eq_chartFrame (I := I) (M := M) g 0 s W α
    (mem_chart_source H α) ![] Jdx]
  have hframe : chartFrameBasisModel (I := I) (M := M) α α 0 ![] =
      unitTensor (I := I) (M := M) α := by
    refine Tensor0SBundle.tensor0SSpace_ext 0 α (fun w => ?_)
    rw [chartFrameBasisModel_apply (I := I) (M := M) α α 0 ![] w]
    rw [Finset.prod_of_isEmpty]
    have hunit : unitTensor (I := I) (M := M) α w = (1 : ℝ) := rfl
    rw [hunit]
  rw [hframe]
  rw [unitModel]
  refine congrArg _ ?_
  funext j
  exact chartBasisVecFiber_self (I := I) (M := M) α (Jdx j)

set_option linter.unusedSectionVars false in
private lemma cmm3_eval_cons_chartBasis_repr
    (D : Tensor0SBundle.Tensor0SModel 3 ℝ E)
    (a : E) (v : Fin 2 → E) :
    D (Fin.cons a v) =
      ∑ i : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
        ((chartModelBasis E).repr (v 0)) i * ((chartModelBasis E).repr (v 1)) k *
          D (![a, (chartModelBasis E) i, (chartModelBasis E) k]) := by
  classical
  have hv0 : ∑ i : Fin (Module.finrank ℝ E),
        ((chartModelBasis E).repr (v 0)) i • (chartModelBasis E) i = v 0 :=
    (chartModelBasis E).sum_repr (v 0)
  have hv1 : ∑ k : Fin (Module.finrank ℝ E),
        ((chartModelBasis E).repr (v 1)) k • (chartModelBasis E) k = v 1 :=
    (chartModelBasis E).sum_repr (v 1)
  have hcons_eq : (Fin.cons a v : Fin 3 → E) = ![a, v 0, v 1] := by
    funext z; fin_cases z <;> rfl
  rw [hcons_eq]
  have hstep1 : D (![a, v 0, v 1]) =
      ∑ i : Fin (Module.finrank ℝ E),
        ((chartModelBasis E).repr (v 0)) i *
          D (![a, (chartModelBasis E) i, v 1]) := by
    have hupd : (![a, v 0, v 1] : Fin 3 → E) =
        Function.update (![a, (0 : E), v 1] : Fin 3 → E) 1
          (∑ i : Fin (Module.finrank ℝ E),
            ((chartModelBasis E).repr (v 0)) i • (chartModelBasis E) i) := by
      rw [hv0]; funext z; fin_cases z <;> simp
    rw [hupd, cmm3_slot_sum_smul (E := E) D 1
      (fun i => ((chartModelBasis E).repr (v 0)) i) (fun i => (chartModelBasis E) i)
      (![a, (0 : E), v 1] : Fin 3 → E)]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    have harg : Function.update (![a, (0 : E), v 1] : Fin 3 → E) 1 ((chartModelBasis E) i) =
        (![a, (chartModelBasis E) i, v 1] : Fin 3 → E) := by
      funext z; fin_cases z <;> simp
    rw [harg]
  rw [hstep1]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have hupd2 : (![a, (chartModelBasis E) i, v 1] : Fin 3 → E) =
      Function.update (![a, (chartModelBasis E) i, (0 : E)] : Fin 3 → E) 2
        (∑ k : Fin (Module.finrank ℝ E),
          ((chartModelBasis E).repr (v 1)) k • (chartModelBasis E) k) := by
    rw [hv1]; funext z; fin_cases z <;> simp
  rw [hupd2, cmm3_slot_sum_smul (E := E) D 2
    (fun k => ((chartModelBasis E).repr (v 1)) k) (fun k => (chartModelBasis E) k)
    (![a, (chartModelBasis E) i, (0 : E)] : Fin 3 → E)]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  have harg2 : Function.update (![a, (chartModelBasis E) i, (0 : E)] : Fin 3 → E) 2
        ((chartModelBasis E) k) =
      (![a, (chartModelBasis E) i, (chartModelBasis E) k] : Fin 3 → E) := by
    funext z; fin_cases z <;> simp
  rw [harg2]
  ring

theorem order1ChartTrace_eq_unitModel_order1Slot0ModelContract
    (g₀ : SmoothRiemannianMetric I M) (c : SmoothCcTensor g₀ 0 1)
    (S : SmoothCcTensor g₀ 0 2) (α : M)
    (v : Fin 2 → TangentSpace I α) :
    (∑ i : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
        ((chartModelBasis E).repr (v 0)) i * ((chartModelBasis E).repr (v 1)) k *
          (∑ j : Fin (Module.finrank ℝ E),
            (unitModel (I := I) (M := M) g₀ 1 c α (fun _ : Fin 1 => (chartModelBasis E) j)) *
              tensorChartComponentRaw (I := I) (M := M) g₀ 0 (2 + 1)
                (iteratedCovGrad (I := I) g₀ 0 2 1 S) α ![] ![j, i, k] α)) =
      order1Slot0ModelContract (E := E) (unitModel (I := I) (M := M) g₀ 1 c α)
        (unitModel (I := I) (M := M) g₀ 3 (iteratedCovGrad (I := I) g₀ 0 2 1 S) α) v := by
  classical
  set α₁ : Tensor0SBundle.Tensor0SModel 1 ℝ E := unitModel (I := I) (M := M) g₀ 1 c α with hα₁
  set Wm : Tensor0SBundle.Tensor0SModel 3 ℝ E :=
    unitModel (I := I) (M := M) g₀ 3 (iteratedCovGrad (I := I) g₀ 0 2 1 S) α with hWm
  have hcomp : ∀ j i k : Fin (Module.finrank ℝ E),
      tensorChartComponentRaw (I := I) (M := M) g₀ 0 (2 + 1)
          (iteratedCovGrad (I := I) g₀ 0 2 1 S) α ![] ![j, i, k] α =
        Wm (![(chartModelBasis E) j, (chartModelBasis E) i, (chartModelBasis E) k]) := by
    intro j i k
    rw [order1_rawComponent_zero_eq_unitModel_chartBasis (I := I) (M := M) g₀ (2 + 1)
      (iteratedCovGrad (I := I) g₀ 0 2 1 S) α ![j, i, k]]
    rw [hWm]
    congr 1
    funext m; fin_cases m <;> rfl
  rw [order1Slot0ModelContract_apply]
  have hRHS : (∑ j : Fin (Module.finrank ℝ E),
        α₁ (fun _ : Fin 1 => (chartModelBasis E) j) *
          Wm (Fin.cons ((chartModelBasis E) j) v)) =
      ∑ j : Fin (Module.finrank ℝ E),
        α₁ (fun _ : Fin 1 => (chartModelBasis E) j) *
          (∑ i : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
            ((chartModelBasis E).repr (v 0)) i * ((chartModelBasis E).repr (v 1)) k *
              Wm (![(chartModelBasis E) j, (chartModelBasis E) i, (chartModelBasis E) k])) := by
    refine Finset.sum_congr rfl (fun j _ => ?_)
    congr 1
    exact cmm3_eval_cons_chartBasis_repr (E := E) Wm ((chartModelBasis E) j) v
  rw [hRHS]
  set F : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
      Fin (Module.finrank ℝ E) → ℝ :=
    fun i k j =>
      ((chartModelBasis E).repr (v 0)) i * ((chartModelBasis E).repr (v 1)) k *
        (α₁ (fun _ : Fin 1 => (chartModelBasis E) j) *
          Wm (![(chartModelBasis E) j, (chartModelBasis E) i, (chartModelBasis E) k])) with hF
  have hLHS : (∑ i : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
        ((chartModelBasis E).repr (v 0)) i * ((chartModelBasis E).repr (v 1)) k *
          (∑ j : Fin (Module.finrank ℝ E),
            (α₁ (fun _ : Fin 1 => (chartModelBasis E) j)) *
              tensorChartComponentRaw (I := I) (M := M) g₀ 0 (2 + 1)
                (iteratedCovGrad (I := I) g₀ 0 2 1 S) α ![] ![j, i, k] α)) =
      ∑ i : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E), F i k j := by
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun k _ => ?_))
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [hF, hcomp j i k]
  have hRHS2 : (∑ j : Fin (Module.finrank ℝ E),
        α₁ (fun _ : Fin 1 => (chartModelBasis E) j) *
          (∑ i : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
            ((chartModelBasis E).repr (v 0)) i * ((chartModelBasis E).repr (v 1)) k *
              Wm (![(chartModelBasis E) j, (chartModelBasis E) i, (chartModelBasis E) k]))) =
      ∑ j : Fin (Module.finrank ℝ E),
        ∑ i : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E), F i k j := by
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [hF]; ring
  rw [hLHS, hRHS2]
  have hswap_kj : (∑ i : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E), F i k j) =
      ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        ∑ k : Fin (Module.finrank ℝ E), F i k j := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.sum_comm]
  rw [hswap_kj, Finset.sum_comm]

set_option linter.unusedSectionVars false in
theorem unitModel_appCc_eq_toSection_apply
    (g₀ : SmoothRiemannianMetric I M) (r : ℕ)
    (Φ : SmoothCcTensor g₀ r 2) (W : SmoothCcTensor g₀ 0 r) (x : M)
    (v : Fin 2 → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 2 (appCc (I := I) (M := M) g₀ r 2 Φ W) x v =
      Tensor0SBundle.Tensor0SSpace.toModel
        ((show Tensor0SBundle.Tensor0SSpace r I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x from
          Φ.toSection x)
          ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace r I x from
            W.toSection x) (unitTensor (I := I) (M := M) x))) v := by
  rw [unitModel, appCc_toSection]
  rfl

set_option linter.unusedSectionVars false in
theorem unitModel_appCc_order1_eq_order1Slot0ModelContract
    (g₀ : SmoothRiemannianMetric I M) (c : SmoothCcTensor g₀ 0 1)
    (Φ : SmoothCcTensor g₀ 3 2)
    (hΦ : Φ.toSection = fun x => (show Tensor0SBundle.TensorRSSpace 3 2 I x from
      order1Slot0ContractFib (I := I) (M := M) g₀ c x))
    (S : SmoothCcTensor g₀ 0 2) (x : M) (v : Fin 2 → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 2
        (appCc (I := I) (M := M) g₀ 3 2 Φ (iteratedCovGrad (I := I) g₀ 0 2 1 S)) x v =
      order1Slot0ModelContract (E := E) (unitModel (I := I) (M := M) g₀ 1 c x)
        (unitModel (I := I) (M := M) g₀ 3 (iteratedCovGrad (I := I) g₀ 0 2 1 S) x) v := by
  rw [unitModel_appCc_eq_toSection_apply (I := I) (M := M) g₀ 3 Φ
    (iteratedCovGrad (I := I) g₀ 0 2 1 S) x v]
  rw [hΦ]
  rw [order1Slot0ContractFib_toModel]
  rfl

theorem order1ChartTrace_eq_unitModel_appCc
    (g₀ : SmoothRiemannianMetric I M) (c : SmoothCcTensor g₀ 0 1)
    (Φ : SmoothCcTensor g₀ 3 2)
    (hΦ : Φ.toSection = fun x => (show Tensor0SBundle.TensorRSSpace 3 2 I x from
      order1Slot0ContractFib (I := I) (M := M) g₀ c x))
    (S : SmoothCcTensor g₀ 0 2) (α : M)
    (v : Fin 2 → TangentSpace I α) :
    (∑ i : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
        ((chartModelBasis E).repr (v 0)) i * ((chartModelBasis E).repr (v 1)) k *
          (∑ j : Fin (Module.finrank ℝ E),
            (unitModel (I := I) (M := M) g₀ 1 c α (fun _ : Fin 1 => (chartModelBasis E) j)) *
              tensorChartComponentRaw (I := I) (M := M) g₀ 0 (2 + 1)
                (iteratedCovGrad (I := I) g₀ 0 2 1 S) α ![] ![j, i, k] α)) =
      unitModel (I := I) (M := M) g₀ 2
        (appCc (I := I) (M := M) g₀ 3 2 Φ (iteratedCovGrad (I := I) g₀ 0 2 1 S)) α v := by
  rw [order1ChartTrace_eq_unitModel_order1Slot0ModelContract (I := I) (M := M) g₀ c S α v]
  rw [unitModel_appCc_order1_eq_order1Slot0ModelContract (I := I) (M := M) g₀ c Φ hΦ S α v]

set_option linter.unusedSectionVars false in
lemma order1Slot0ModelContract_symmAbsorbed
    (α : Tensor0SBundle.Tensor0SModel 1 ℝ E)
    (D : Tensor0SBundle.Tensor0SModel 3 ℝ E) (w : Fin 2 → E)
    (hD : ∀ a b c : E, D (![a, b, c]) = D (![a, c, b])) :
    order1Slot0ModelContract (E := E) α D (![w 0, w 1]) =
      order1Slot0ModelContract (E := E) α D (![w 1, w 0]) := by
  classical
  rw [order1Slot0ModelContract_apply, order1Slot0ModelContract_apply]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  congr 1
  have h0 : (Fin.cons ((chartModelBasis E) j) (![w 0, w 1] : Fin 2 → E) : Fin 3 → E) =
      ![(chartModelBasis E) j, w 0, w 1] := by
    funext z; fin_cases z <;> rfl
  have h1 : (Fin.cons ((chartModelBasis E) j) (![w 1, w 0] : Fin 2 → E) : Fin 3 → E) =
      ![(chartModelBasis E) j, w 1, w 0] := by
    funext z; fin_cases z <;> rfl
  rw [h0, h1, hD ((chartModelBasis E) j) (w 0) (w 1)]

def order1Slot0InteriorFib (x : M) (V : TangentSpace I x) :
    Tensor0SBundle.Tensor0SSpace 3 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x :=
  Tensor0SBundle.interior_product (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 2 x V

set_option linter.unusedSectionVars false in
@[simp] lemma order1Slot0InteriorFib_toModel (x : M) (V : TangentSpace I x)
    (D : Tensor0SBundle.Tensor0SSpace 3 I x) (w : Fin 2 → E) :
    Tensor0SBundle.Tensor0SSpace.toModel (order1Slot0InteriorFib (I := I) (M := M) x V D) w =
      Tensor0SBundle.Tensor0SSpace.toModel D (Fin.cons (V : E) w) := by
  rw [order1Slot0InteriorFib, Tensor0SBundle.interior_product]
  change (model_interior_product (𝕜 := ℝ) (E := E) 2 (V : E)
      (Tensor0SBundle.Tensor0SSpace.toModel D)) w = _
  rw [model_interior_product]
  change (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin 3 => E) ℝ
      (Tensor0SBundle.Tensor0SSpace.toModel D) (V : E)) w = _
  rw [continuousMultilinearCurryLeftEquiv_apply]

set_option linter.unusedSectionVars false in
theorem tensorChartComponentRaw_domDomCongrSection_swap
    (g : SmoothRiemannianMetric I M) (S : SmoothCcTensor g 0 2)
    (α : M) (a b : Fin (Module.finrank ℝ E)) {x : M}
    (hx : x ∈ (chartAt H α).source) :
    tensorChartComponentRaw (I := I) (M := M) g 0 2
        (domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 2) 1) S) α ![] ![a, b] x =
      tensorChartComponentRaw (I := I) (M := M) g 0 2 S α ![] ![b, a] x := by
  classical
  rw [tensorChartComponentRaw_eq_chartFrame (I := I) (M := M) g 0 2
      (domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 2) 1) S) α hx
      (![] : Fin 0 → Fin (Module.finrank ℝ E)) (![a, b] : Fin 2 → _)]
  rw [tensorChartComponentRaw_eq_chartFrame (I := I) (M := M) g 0 2
      S α hx (![] : Fin 0 → Fin (Module.finrank ℝ E)) (![b, a] : Fin 2 → _)]
  have hframe : chartFrameBasisModel (I := I) (M := M) α x 0
        (![] : Fin 0 → Fin (Module.finrank ℝ E)) =
      (ContinuousMultilinearMap.constOfIsEmpty ℝ
        (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ)) := by
    apply ContinuousMultilinearMap.ext
    intro v
    have h := chartFrameBasisModel_apply (I := I) (M := M) α x 0
      (![] : Fin 0 → Fin (Module.finrank ℝ E)) v
    rw [Fin.prod_univ_zero] at h
    rw [ContinuousMultilinearMap.constOfIsEmpty_apply]
    exact h
  rw [hframe]
  have hLHS :
      ((((domDomCongrSection (I := I) g (Equiv.swap (0:Fin 2) 1) S).toSection x)
          (ContinuousMultilinearMap.constOfIsEmpty ℝ
            (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))) fun j =>
          chartBasisVecFiber (I := I) α ((![a, b] : Fin 2 → _) j) x) =
        unitModel (I := I) (M := M) g 2
            (domDomCongrSection (I := I) g (Equiv.swap (0:Fin 2) 1) S) x
          (fun j => chartBasisVecFiber (I := I) α ((![a, b] : Fin 2 → _) j) x) := rfl
  have hRHS :
      ((((S).toSection x)
          (ContinuousMultilinearMap.constOfIsEmpty ℝ
            (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))) fun j =>
          chartBasisVecFiber (I := I) α ((![b, a] : Fin 2 → _) j) x) =
        unitModel (I := I) (M := M) g 2 S x
          (fun j => chartBasisVecFiber (I := I) α ((![b, a] : Fin 2 → _) j) x) := rfl
  rw [hLHS, hRHS]
  rw [domDomCongrSection_unitModel (I := I) g (Equiv.swap (0:Fin 2) 1) S x]
  rw [ContinuousMultilinearMap.domDomCongr_apply]
  congr 1
  funext j
  fin_cases j <;> simp [Equiv.swap_apply_left, Equiv.swap_apply_right]

set_option linter.unusedSectionVars false in
theorem tensorChartComponentRaw_symmS_eq_half_swap
    (g : SmoothRiemannianMetric I M) (S : SmoothCcTensor g 0 2)
    (α : M) (a b : Fin (Module.finrank ℝ E)) {x : M}
    (hx : x ∈ (chartAt H α).source) :
    tensorChartComponentRaw (I := I) (M := M) g 0 2
        (symmS (I := I) g S) α ![] ![a, b] x =
      (1 / 2 : ℝ) *
        (tensorChartComponentRaw (I := I) (M := M) g 0 2 S α ![] ![a, b] x +
          tensorChartComponentRaw (I := I) (M := M) g 0 2 S α ![] ![b, a] x) := by
  classical
  rw [symmS, tensorChartComponentRaw_smul (I := I) (M := M) g 0 2 (1 / 2 : ℝ)
      (S + domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 2) 1) S) α ![] ![a, b] x,
    tensorChartComponentRaw_add (I := I) (M := M) g 0 2 S
      (domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 2) 1) S) α ![] ![a, b] x,
    tensorChartComponentRaw_domDomCongrSection_swap (I := I) (M := M) g S α a b hx]
  rw [smul_eq_mul]

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
