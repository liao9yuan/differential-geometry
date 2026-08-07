import DifferentialGeometry.Topology.Morse.LevelSet
import DifferentialGeometry.Topology.Morse.Manifold

namespace DifferentialGeometry.Topology.Morse

open scoped Manifold Topology

noncomputable section

variable {m : ℕ} {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
variable (I : ModelWithCorners ℝ (MorseModel (m + 1)) H)

theorem fderiv_sublevelPullback_ne_zero [I.Boundaryless] [IsManifold I (⊤ : WithTop ℕ∞) M]
    (f : M → ℝ) (hf : ContMDiff I 𝓘(ℝ, ℝ) (⊤ : WithTop ℕ∞) f) (a : ℝ)
    (hreg : ∀ x : M, f x = a → ¬ IsCriticalPointAt I f x)
    {p : M} {y : MorseModel (m + 1)}
    (hy : f ((extChartAt I p).symm y) = a) (hyt : y ∈ (extChartAt I p).target) :
    fderiv ℝ (fun y : MorseModel (m + 1) => f ((extChartAt I p).symm y)) y ≠ 0 := by
  classical
  let q : M := (extChartAt I p).symm y
  have hq : f q = a := hy
  have hregq : ¬ IsCriticalPointAt I f q := hreg q hq
  have hψq : (extChartAt I p) q = y := (extChartAt I p).right_inv hyt
  have hleft : ((extChartAt I p).symm ∘ (extChartAt I p)) =ᶠ[nhds q] id := by
    have hsrc : q ∈ (extChartAt I p).source := (extChartAt I p).map_target hyt
    have hopen : IsOpen (extChartAt I p).source := isOpen_extChartAt_source (I := I) p
    exact Filter.eventuallyEq_of_mem (by simpa [q] using hopen.mem_nhds hsrc)
      (fun x hx => (extChartAt I p).left_inv hx)
  have hright : ((extChartAt I p) ∘ (extChartAt I p).symm) =ᶠ[nhds y] id := by
    exact Filter.eventuallyEq_of_mem ((isOpen_extChartAt_target (I := I) p).mem_nhds hyt)
      (fun x hx => (extChartAt I p).right_inv hx)
  have hσmd : MDifferentiableAt I 𝓘(ℝ, MorseModel (m + 1)) (extChartAt I p) q := by
    have hsrc : q ∈ (chartAt H p).source := by
      simpa [q, extChartAt_source (I := I)] using (extChartAt I p).map_target hyt
    exact (contMDiffAt_extChartAt' (I := I) (n := (↑(⊤ : ℕ∞) : WithTop ℕ∞)) (x := p)
      (by simpa [q] using hsrc)).mdifferentiableAt (by norm_num)
  have hτmd : MDifferentiableAt 𝓘(ℝ, MorseModel (m + 1)) I (extChartAt I p).symm y := by
    have hc : ContMDiffAt 𝓘(ℝ, MorseModel (m + 1)) I ((↑(⊤ : ℕ∞) : WithTop ℕ∞))
        (extChartAt I p).symm y := by
      have hon : ContMDiffOn 𝓘(ℝ, MorseModel (m + 1)) I ((↑(⊤ : ℕ∞) : WithTop ℕ∞))
          (extChartAt I p).symm (extChartAt I p).target :=
        contMDiffOn_extChartAt_symm (n := (↑(⊤ : ℕ∞) : WithTop ℕ∞)) p
      exact hon.contMDiffAt ((isOpen_extChartAt_target (I := I) p).mem_nhds hyt)
    exact hc.mdifferentiableAt (by norm_num)
  have hh : ContMDiffAt 𝓘(ℝ, MorseModel (m + 1)) 𝓘(ℝ, ℝ) ((↑(⊤ : ℕ∞) : WithTop ℕ∞))
      (f ∘ (extChartAt I p).symm) y := by
    have hc : ContMDiffAt 𝓘(ℝ, MorseModel (m + 1)) I ((↑(⊤ : ℕ∞) : WithTop ℕ∞))
        (extChartAt I p).symm y := by
      have hon : ContMDiffOn 𝓘(ℝ, MorseModel (m + 1)) I ((↑(⊤ : ℕ∞) : WithTop ℕ∞))
          (extChartAt I p).symm (extChartAt I p).target :=
        contMDiffOn_extChartAt_symm (n := (↑(⊤ : ℕ∞) : WithTop ℕ∞)) p
      exact hon.contMDiffAt ((isOpen_extChartAt_target (I := I) p).mem_nhds hyt)
    have hfq : ContMDiffAt I 𝓘(ℝ, ℝ) ((↑(⊤ : ℕ∞) : WithTop ℕ∞)) f q :=
      (hf q).of_le le_top
    exact ContMDiffAt.comp (x := y) (g := f) (f := (extChartAt I p).symm)
      (hg := hfq) (hf := hc)
  have htrans : IsCriticalPointAt I ((f ∘ (extChartAt I p).symm) ∘ (extChartAt I p)) q ↔
      fderiv ℝ (f ∘ (extChartAt I p).symm) y = 0 := by
    have htr := isCriticalPointAt_iff_fderiv_of_localInverse I (x := q) (σ := (extChartAt I p))
      (τ := (extChartAt I p).symm) (h := f ∘ (extChartAt I p).symm)
      (hleft := hleft) (hright := by
        rw [hψq]
        exact hright)
      (hσmd := hσmd) (hτmd := by
        rw [hψq]
        exact hτmd) (hh := by
          rw [hψq]
          exact hh)
    rw [hψq] at htr
    exact htr
  have hfuneq : (f ∘ (extChartAt I p).symm) ∘ (extChartAt I p) =ᶠ[nhds q] f := by
    have hsrc : q ∈ (extChartAt I p).source := (extChartAt I p).map_target hyt
    have hopen : IsOpen (extChartAt I p).source := isOpen_extChartAt_source (I := I) p
    exact Filter.eventuallyEq_of_mem (by simpa [q] using hopen.mem_nhds hsrc)
      (fun x hx => congrArg f ((extChartAt I p).left_inv hx))
  have hcrit_eq : IsCriticalPointAt I ((f ∘ (extChartAt I p).symm) ∘ (extChartAt I p)) q ↔
      IsCriticalPointAt I f q := by
    change mfderiv I 𝓘(ℝ, ℝ) ((f ∘ (extChartAt I p).symm) ∘ (extChartAt I p)) q = 0 ↔
      mfderiv I 𝓘(ℝ, ℝ) f q = 0
    exact Iff.of_eq (congrArg (fun L : TangentSpace I q →L[ℝ] ℝ => L = 0)
      (Filter.EventuallyEq.mfderiv_eq (I := I) (I' := 𝓘(ℝ, ℝ)) hfuneq))
  have hne : fderiv ℝ (f ∘ (extChartAt I p).symm) y ≠ 0 := by
    intro hzero
    have hcrit : IsCriticalPointAt I ((f ∘ (extChartAt I p).symm) ∘ (extChartAt I p)) q :=
      htrans.2 hzero
    exact hregq (hcrit_eq.mp hcrit)
  change fderiv ℝ (fun y : MorseModel (m + 1) => f ((extChartAt I p).symm y)) y ≠ 0
  simpa [q] using hne

noncomputable def sublevelPullback (f : M → ℝ) (p : M) : MorseModel (m + 1) → ℝ :=
  fun y => f ((extChartAt I p).symm y)

end

end DifferentialGeometry.Topology.Morse
