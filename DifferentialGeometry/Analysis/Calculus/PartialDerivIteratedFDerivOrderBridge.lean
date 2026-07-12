import DifferentialGeometry.Analysis.Calculus.IteratedFDerivProductDifferenceBound
import DifferentialGeometry.Analysis.Integration.DivergenceTheorem.LocalFormula


noncomputable section

open Set
open scoped Topology BigOperators ContDiff

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace IntrinsicSpectral
namespace DeTurckCoefficients

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

omit [InnerProductSpace ℝ E] in
lemma partialDeriv_contDiffOn_of_isOpen
    {u : E → ℝ} {s : Set E} (hs : IsOpen s) (hu : ContDiffOn ℝ ∞ u s)
    (i : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞ (partialDeriv (E := E) i u) s := by
  have hfderiv : ContDiffOn ℝ ∞ (fderiv ℝ u) s :=
    hu.fderiv_of_isOpen hs (by rw [ENat.coe_top_add_one])
  unfold partialDeriv
  exact hfderiv.clm_apply contDiffOn_const

omit [InnerProductSpace ℝ E] in
lemma partialDeriv_sub_eqOn
    {u v : E → ℝ} {s : Set E} (hs : IsOpen s)
    (hu : ContDiffOn ℝ ∞ u s) (hv : ContDiffOn ℝ ∞ v s)
    (i : Fin (Module.finrank ℝ E)) :
    EqOn (fun z => partialDeriv (E := E) i u z - partialDeriv (E := E) i v z)
      (partialDeriv (E := E) i (fun z => u z - v z)) s := by
  intro y hy
  have hdu : DifferentiableAt ℝ u y :=
    (hu.contDiffAt (hs.mem_nhds hy)).differentiableAt (by simp)
  have hdv : DifferentiableAt ℝ v y :=
    (hv.contDiffAt (hs.mem_nhds hy)).differentiableAt (by simp)
  simp only [partialDeriv]
  have hfd : fderiv ℝ (fun z => u z - v z) y = fderiv ℝ u y - fderiv ℝ v y := by
    have := fderiv_sub (𝕜 := ℝ) hdu hdv
    simpa using this
  rw [hfd, ContinuousLinearMap.sub_apply]

omit [InnerProductSpace ℝ E] in
lemma partialDeriv_eqOn_fderivWithin_apply
    {u : E → ℝ} {s : Set E} (hs : IsOpen s) (i : Fin (Module.finrank ℝ E)) :
    EqOn (partialDeriv (E := E) i u)
      (fun y => fderivWithin ℝ u s y ((chartModelBasis E) i)) s := by
  intro y hy
  simp only [partialDeriv, fderivWithin_of_isOpen hs hy]

omit [InnerProductSpace ℝ E] in
theorem norm_iteratedFDerivWithin_partialDeriv_le
    {u : E → ℝ} {s : Set E} (hs : IsOpen s)
    (hu : ContDiffOn ℝ ∞ u s) (i : Fin (Module.finrank ℝ E))
    (N : ℕ) {y : E} (hy : y ∈ s) :
    ‖iteratedFDerivWithin ℝ N (partialDeriv (E := E) i u) s y‖ ≤
      ‖(chartModelBasis E) i‖ * ‖iteratedFDerivWithin ℝ (N + 1) u s y‖ := by
  have hcongr :
      iteratedFDerivWithin ℝ N (partialDeriv (E := E) i u) s y =
        iteratedFDerivWithin ℝ N
          (fun z => fderivWithin ℝ u s z ((chartModelBasis E) i)) s y :=
    iteratedFDerivWithin_congr (partialDeriv_eqOn_fderivWithin_apply hs i) hy N
  rw [hcongr]
  have hfderiv : ContDiffOn ℝ ∞ (fderivWithin ℝ u s) s :=
    hu.fderivWithin (hs.uniqueDiffOn) (by rw [ENat.coe_top_add_one])
  have hclm := norm_iteratedFDerivWithin_clm_apply_const
    (f := fderivWithin ℝ u s) (c := (chartModelBasis E) i) (s := s) (x := y)
    (N := (⊤ : ℕ∞)) (n := N)
    (hfderiv.contDiffWithinAt hy) hs.uniqueDiffOn hy (by exact_mod_cast le_top)
  refine hclm.trans ?_
  have heq : ‖iteratedFDerivWithin ℝ N (fderivWithin ℝ u s) s y‖ =
      ‖iteratedFDerivWithin ℝ (N + 1) u s y‖ :=
    norm_iteratedFDerivWithin_fderivWithin hs.uniqueDiffOn hy
  rw [heq]

omit [InnerProductSpace ℝ E] in
theorem iteratedFDerivSeminorm_partialDeriv_le
    {u : E → ℝ} {s : Set E} (hs : IsOpen s)
    (hu : ContDiffOn ℝ ∞ u s) (i : Fin (Module.finrank ℝ E))
    (N : ℕ) {y : E} (hy : y ∈ s) :
    iteratedFDerivSeminorm N (partialDeriv (E := E) i u) s y ≤
      ‖(chartModelBasis E) i‖ * iteratedFDerivSeminorm (N + 1) u s y := by
  classical
  have hstep :
      iteratedFDerivSeminorm N (partialDeriv (E := E) i u) s y ≤
        ‖(chartModelBasis E) i‖ *
          ∑ l ∈ Finset.range (N + 1), ‖iteratedFDerivWithin ℝ (l + 1) u s y‖ := by
    unfold iteratedFDerivSeminorm
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun l _ => ?_
    exact norm_iteratedFDerivWithin_partialDeriv_le hs hu i l hy
  refine hstep.trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  unfold iteratedFDerivSeminorm
  have himg :
      ∑ l ∈ Finset.range (N + 1), ‖iteratedFDerivWithin ℝ (l + 1) u s y‖ =
        ∑ m ∈ (Finset.range (N + 1)).image (· + 1),
          ‖iteratedFDerivWithin ℝ m u s y‖ := by
    rw [Finset.sum_image (g := (· + 1))
      (f := fun m => ‖iteratedFDerivWithin ℝ m u s y‖)
      (by intro a _ b _ hab; simpa using hab)]
  rw [himg]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => norm_nonneg _)
  intro m hm
  rw [Finset.mem_image] at hm
  obtain ⟨l, hl, rfl⟩ := hm
  rw [Finset.mem_range] at hl ⊢
  omega

end DeTurckCoefficients
end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end
