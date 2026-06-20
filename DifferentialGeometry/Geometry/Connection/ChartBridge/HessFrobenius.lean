import DifferentialGeometry.Geometry.Connection.ChartBridge.Hessian

noncomputable section

open Bundle Manifold Set FiberBundle
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry
namespace Integral
namespace Connection

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [Module.Finite ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem

theorem chartHessFrobeniusSq_eq_frobeniusSqFun_hessFun_of_orthonormal
    (g : SmoothRiemannianMetric I M) (f : M → ℝ) (x : M)
    (h_orth : ∀ i j : Fin (Module.finrank ℝ E),
      chartInvGramMatrix (I := I) g x x i j = if i = j then (1 : ℝ) else 0) :
    chartHessFrobeniusSq (I := I) g f x =
      frobeniusSqFun (I := I) (M := M) (hessFun (I := I) g f) x := by
  classical
  rw [chartHessFrobeniusSq_def, frobeniusSqFun_hessFun]
  have hLHS_eq :
      (∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
        ∑ k : Fin (Module.finrank ℝ E),
        ∑ l : Fin (Module.finrank ℝ E),
          chartInvGramMatrix (I := I) g x x i k *
            chartInvGramMatrix (I := I) g x x j l *
              chartHessianTensor (I := I) g x f i j x *
                chartHessianTensor (I := I) g x f k l x) =
      (∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
        ∑ k : Fin (Module.finrank ℝ E),
        ∑ l : Fin (Module.finrank ℝ E),
          (if i = k then (1 : ℝ) else 0) *
            (if j = l then (1 : ℝ) else 0) *
              chartHessianTensor (I := I) g x f i j x *
                chartHessianTensor (I := I) g x f k l x) := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    refine Finset.sum_congr rfl (fun j _ => ?_)
    refine Finset.sum_congr rfl (fun k _ => ?_)
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [h_orth i k, h_orth j l]
  rw [hLHS_eq]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  refine Finset.sum_congr rfl (fun j _ => ?_)
  have hl : ∀ k : Fin (Module.finrank ℝ E),
      ∑ l : Fin (Module.finrank ℝ E),
        (if i = k then (1 : ℝ) else 0) *
          (if j = l then (1 : ℝ) else 0) *
            chartHessianTensor (I := I) g x f i j x *
              chartHessianTensor (I := I) g x f k l x =
        (if i = k then (1 : ℝ) else 0) *
          chartHessianTensor (I := I) g x f i j x *
          chartHessianTensor (I := I) g x f k j x := by
    intro k
    rw [Finset.sum_eq_single j]
    · rw [if_pos rfl]
      ring
    · intro l _ hlj
      have hjl : ¬ j = l := fun h => hlj h.symm
      rw [if_neg hjl]
      ring
    · intro hj
      exact absurd (Finset.mem_univ j) hj
  rw [show
      (∑ k : Fin (Module.finrank ℝ E),
        ∑ l : Fin (Module.finrank ℝ E),
          (if i = k then (1 : ℝ) else 0) *
            (if j = l then (1 : ℝ) else 0) *
              chartHessianTensor (I := I) g x f i j x *
                chartHessianTensor (I := I) g x f k l x) =
      ∑ k : Fin (Module.finrank ℝ E),
        (if i = k then (1 : ℝ) else 0) *
          chartHessianTensor (I := I) g x f i j x *
          chartHessianTensor (I := I) g x f k j x from
    Finset.sum_congr rfl (fun k _ => hl k)]
  rw [Finset.sum_eq_single i]
  · rw [if_pos rfl]
    ring
  · intro k _ hki
    have hik : ¬ i = k := fun h => hki h.symm
    rw [if_neg hik]
    ring
  · intro hi
    exact absurd (Finset.mem_univ i) hi

theorem chartHessFrobeniusSq_eq_metric_hessian_norm_sq [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (x : M)
    (h_orth : ∀ i j : Fin (Module.finrank ℝ E),
      chartInvGramMatrix (I := I) g x x i j = if i = j then (1 : ℝ) else 0) :
    chartHessFrobeniusSq (I := I) g f x =
      frobeniusSqFun (I := I) (M := M) (abstractHessianBilin (I := I) g f) x := by
  classical
  have h1 : chartHessFrobeniusSq (I := I) g f x =
      frobeniusSqFun (I := I) (M := M) (hessFun (I := I) g f) x :=
    chartHessFrobeniusSq_eq_frobeniusSqFun_hessFun_of_orthonormal
      (I := I) g f x h_orth
  have hM : chartHessianMatrixIdentity (I := I) g f x :=
    chartHessianMatrixIdentity_holds (I := I) g hf x
  have h2 : frobeniusSqFun (I := I) (M := M) (hessFun (I := I) g f) x =
      frobeniusSqFun (I := I) (M := M) (abstractHessianBilin (I := I) g f) x :=
    frobeniusSqFun_hessFun_eq_frobeniusSqFun_abstractHessianBilin_of_matrix_identity
      (I := I) g f x hM
  exact h1.trans h2

end Connection
end Integral
end DifferentialGeometry
