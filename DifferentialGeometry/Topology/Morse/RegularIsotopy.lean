import DifferentialGeometry.Topology.Morse.RegularVectorField
import DifferentialGeometry.Topology.Morse.RegularSublevel
import DifferentialGeometry.Analysis.ODE.CompactSupportFlow

namespace DifferentialGeometry.Topology.Morse

open Manifold Set
open scoped Manifold ContDiff Topology

noncomputable section

variable {m : ℕ} {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]

private theorem familyChartRep_contDiffOn
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} [I.Boundaryless]
    [IsManifold I (⊤ : WithTop ℕ∞) M] (F : M → ℝ → ℝ)
    (hF : ContMDiff (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : M × ℝ => F q.1 q.2)) (x₀ : M) :
    ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : MorseModel (m + 1) × ℝ => F ((extChartAt I x₀).symm q.1) q.2)
      ((extChartAt I x₀).target ×ˢ Set.univ) := by
  have hFOn : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : M × ℝ => F q.1 q.2) Set.univ := by
    intro x hx
    exact hF x
  have hc' : ContMDiffOn 𝓘(ℝ, MorseModel (m + 1) × ℝ) 𝓘(ℝ, ℝ)
      (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : MorseModel (m + 1) × ℝ =>
        F ((extChartAt I x₀).symm q.1) q.2)
      ((extChartAt I x₀).target ×ˢ Set.univ) := by
    have hraw := (contMDiffOn_iff_source_of_mem_maximalAtlas
      (I := I.prod 𝓘(ℝ, ℝ)) (I' := 𝓘(ℝ, ℝ))
      (f := fun q : M × ℝ => F q.1 q.2) (n := (↑(⊤ : ℕ∞) : WithTop ℕ∞))
      (e := chartAt (ModelProd H ℝ) (x₀, (0 : ℝ)))
      (IsManifold.chart_mem_maximalAtlas (M := M × ℝ) (x₀, (0 : ℝ)))
      (s := (chartAt H x₀).source ×ˢ Set.univ)
      (hs := by intro x hx; exact ⟨hx.1, trivial⟩)).1
      (hFOn.mono (by intro x hx; trivial))
    convert hraw using 1
    ext q
    constructor
    · rintro ⟨⟨hq1, hq2⟩, hq3⟩
      refine ⟨((chartAt H x₀).symm (I.symm q.1), q.2), ⟨?_, hq3⟩, ?_⟩
      · exact (chartAt H x₀).symm.mapsTo hq2
      · change (I (chartAt H x₀ ((chartAt H x₀).symm (I.symm q.1))), q.2) = q
        apply Prod.ext
        · ext i
          rw [show chartAt H x₀ ((chartAt H x₀).symm (I.symm q.1)) = I.symm q.1 by
            exact (chartAt H x₀).right_inv hq2]
          exact congrFun (I.right_inv (by simpa [ModelWithCorners.target_eq] using hq1)) i
        · rfl
    · rintro ⟨a, ha, hx⟩
      have hx1 : I (chartAt H x₀ a.1) = q.1 := congrArg Prod.fst hx
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · rw [← hx1]
        simp [ModelWithCorners.target_eq]
      · rw [← hx1]
        change I.symm (I (chartAt H x₀ a.1)) ∈ (chartAt H x₀).target
        simpa using (chartAt H x₀).mapsTo ha.1
      · trivial
  exact (contMDiffOn_iff_contDiffOn (𝕜 := ℝ) (E := MorseModel (m + 1) × ℝ) (E' := ℝ)
    (f := fun q : MorseModel (m + 1) × ℝ => F ((extChartAt I x₀).symm q.1) q.2)
    (s := (extChartAt I x₀).target ×ˢ Set.univ) (n := (↑(⊤ : ℕ∞) : WithTop ℕ∞))).1 hc'

end
end DifferentialGeometry.Topology.Morse
