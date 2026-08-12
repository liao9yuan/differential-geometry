import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.SmoothDependence.CompactTrajectory

namespace DifferentialGeometry.PDE.RicciFlow.ODE

open Set Function Filter Bundle Manifold
open scoped Topology Manifold ContDiff

noncomputable section

theorem exists_flow_compact_pairField {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E] {H : Type} [TopologicalSpace H]
    {M : Type} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [SigmaCompactSpace M]
    {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    [IsManifold I (⊤ : WithTop ℕ∞) M]
    (Vsusp : (q : M × ℝ) → TangentSpace (I.prod 𝓘(ℝ, ℝ)) q)
    (hVsuspsec : ContMDiff (I.prod 𝓘(ℝ, ℝ))
      ((I.prod 𝓘(ℝ, ℝ)).prod 𝓘(ℝ, E × ℝ)) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : M × ℝ => (⟨q, Vsusp q⟩ : TangentBundle (I.prod 𝓘(ℝ, ℝ)) (M × ℝ))))
    (t₀ : ℝ) {K : Set (M × ℝ)} (hK : IsCompact K) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ y ∈ K,
      ∃ U : Set (M × ℝ), IsOpen U ∧ y ∈ U ∧
        ∃ Φ : (M × ℝ) → ℝ → M × ℝ,
          (∀ z ∈ U, Φ z t₀ = z) ∧
          ContMDiffOn (𝓘(ℝ, ℝ).prod (I.prod 𝓘(ℝ, ℝ))) (I.prod 𝓘(ℝ, ℝ)) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
            (fun q : ℝ × (M × ℝ) => Φ q.2 q.1)
            (Set.Ioo (t₀ - ε) (t₀ + ε) ×ˢ U) ∧
          (∀ z ∈ U, ∀ t ∈ Set.Ioo (t₀ - ε) (t₀ + ε),
            HasMFDerivAt 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, ℝ)) (fun s : ℝ => Φ z s) t
              ((1 : ℝ →L[ℝ] ℝ).smulRight (Vsusp (Φ z t)))) := by
  let X : ℝ → ∀ p : M × ℝ, TangentSpace (I.prod 𝓘(ℝ, ℝ)) p := fun _ p => Vsusp p
  have hX : ContMDiff (𝓘(ℝ, ℝ).prod (I.prod 𝓘(ℝ, ℝ)))
      ((I.prod 𝓘(ℝ, ℝ)).prod 𝓘(ℝ, E × ℝ)) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : ℝ × (M × ℝ) => (TotalSpace.mk' (E × ℝ) q.2 (X q.1 q.2) :
        TangentBundle (I.prod 𝓘(ℝ, ℝ)) (M × ℝ))) := by
    have hsec : ContMDiff (𝓘(ℝ, ℝ).prod (I.prod 𝓘(ℝ, ℝ)))
        ((I.prod 𝓘(ℝ, ℝ)).prod 𝓘(ℝ, E × ℝ)) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
        (fun q : ℝ × (M × ℝ) => (TotalSpace.mk' (E × ℝ) q.2 (Vsusp q.2) :
          TangentBundle (I.prod 𝓘(ℝ, ℝ)) (M × ℝ))) := by
      exact hVsuspsec.comp (contMDiff_snd (I := 𝓘(ℝ, ℝ)) (J := I.prod 𝓘(ℝ, ℝ))
        (n := (↑(⊤ : ℕ∞) : WithTop ℕ∞)))
    simpa [X] using hsec
  exact exists_flow_compact (E := E × ℝ) (I := I.prod 𝓘(ℝ, ℝ)) (M := M × ℝ) X hX t₀ hK

end

end DifferentialGeometry.PDE.RicciFlow.ODE
