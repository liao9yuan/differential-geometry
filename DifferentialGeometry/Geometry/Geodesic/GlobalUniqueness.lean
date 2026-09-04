import DifferentialGeometry.Geometry.Geodesic.GlobalVectorField
import Mathlib.Geometry.Manifold.IntegralCurve.ExistUnique

noncomputable section

open Bundle Manifold Set Filter Function
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

variable [I.Boundaryless] [CompleteSpace E] [T2Space (TangentBundle I M)]

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] in
/-- Two integral curves of the global geodesic vector field that agree once on
an open preconnected time domain agree throughout that domain. -/
theorem gvf_eqOn
    (g : SmoothRiemannianMetric I M)
    {f₁ f₂ : ℝ → TangentBundle I M} {K : Set ℝ} {t₀ : ℝ}
    (hK_open : IsOpen K) (hK_conn : IsPreconnected K) (ht₀ : t₀ ∈ K)
    (hf₁_on : IsMIntegralCurveOn f₁ (geodesicVectorField (I := I) g) K)
    (hf₂_on : IsMIntegralCurveOn f₂ (geodesicVectorField (I := I) g) K)
    (ht₀_eq : f₁ t₀ = f₂ t₀) :
    Set.EqOn f₁ f₂ K := by
  classical
  set A : Set ℝ := {s ∈ K | f₁ s = f₂ s} with hA_def
  have ht₀_A : t₀ ∈ A := ⟨ht₀, ht₀_eq⟩
  have hf₁_cont : ContinuousOn f₁ K := hf₁_on.continuousOn
  have hf₂_cont : ContinuousOn f₂ K := hf₂_on.continuousOn
  have hA_rel_open : ∀ s ∈ A, ∃ U : Set ℝ, IsOpen U ∧ s ∈ U ∧ U ∩ K ⊆ A := by
    intro s hs_A
    obtain ⟨hs_K, hs_eq⟩ := hs_A
    have hK_nhds : K ∈ 𝓝 s := hK_open.mem_nhds hs_K
    have hf₁_at_s : IsMIntegralCurveAt f₁ (geodesicVectorField (I := I) g) s :=
      hf₁_on.isMIntegralCurveAt hK_nhds
    have hf₂_at_s : IsMIntegralCurveAt f₂ (geodesicVectorField (I := I) g) s :=
      hf₂_on.isMIntegralCurveAt hK_nhds
    have hsmooth1 :
        ContMDiffAt I.tangent I.tangent.tangent 1
          (fun p : TangentBundle I M =>
            (⟨p, geodesicVectorField (I := I) g p⟩ :
              TangentBundle I.tangent (TangentBundle I M)))
          (f₁ s) :=
      (geodesicVF_smooth (I := I) g).contMDiffAt.of_le
        (by exact_mod_cast (le_top : (1 : ℕ∞) ≤ ⊤))
    have heq_ev :=
      isMIntegralCurveAt_eventuallyEq_of_contMDiffAt_boundaryless
        (I := I.tangent) (M := TangentBundle I M)
        (v := geodesicVectorField (I := I) g)
        (γ := f₁) (γ' := f₂) (t₀ := s)
        hsmooth1 hf₁_at_s hf₂_at_s hs_eq
    rw [Filter.eventuallyEq_iff_exists_mem] at heq_ev
    obtain ⟨U₀, hU₀_nhds, hU₀_eq⟩ := heq_ev
    obtain ⟨U, hU_sub, hU_open, hs_U⟩ := _root_.mem_nhds_iff.mp hU₀_nhds
    refine ⟨U, hU_open, hs_U, ?_⟩
    intro s' hs'
    exact ⟨hs'.2, hU₀_eq (hU_sub hs'.1)⟩
  have hKnA_rel_open :
      ∀ s ∈ K \ A, ∃ U : Set ℝ, IsOpen U ∧ s ∈ U ∧ U ∩ K ⊆ K \ A := by
    intro s hs_KnA
    obtain ⟨hs_K, hs_nA⟩ := hs_KnA
    have hs_neq : f₁ s ≠ f₂ s := by
      intro h
      exact hs_nA ⟨hs_K, h⟩
    have hpair_cont : ContinuousAt (fun s : ℝ => (f₁ s, f₂ s)) s := by
      apply ContinuousAt.prodMk
      · exact (hf₁_cont.continuousWithinAt hs_K).continuousAt
          (hK_open.mem_nhds hs_K)
      · exact (hf₂_cont.continuousWithinAt hs_K).continuousAt
          (hK_open.mem_nhds hs_K)
    have hdiag_closed :
        IsClosed {q : TangentBundle I M × TangentBundle I M | q.1 = q.2} :=
      isClosed_diagonal
    have hndiag_open :
        IsOpen {q : TangentBundle I M × TangentBundle I M | q.1 ≠ q.2} :=
      hdiag_closed.isOpen_compl
    have hpreim : (fun s : ℝ => (f₁ s, f₂ s)) ⁻¹'
        {q : TangentBundle I M × TangentBundle I M | q.1 ≠ q.2} ∈ 𝓝 s :=
      hpair_cont.preimage_mem_nhds (hndiag_open.mem_nhds hs_neq)
    obtain ⟨U, hU_sub, hU_open, hs_U⟩ := _root_.mem_nhds_iff.mp hpreim
    refine ⟨U, hU_open, hs_U, ?_⟩
    intro s' hs'
    refine ⟨hs'.2, ?_⟩
    intro hs'_A
    exact (hU_sub hs'.1) hs'_A.2
  intro s hs_K
  by_contra h_neq
  have hs_KnA : s ∈ K \ A := ⟨hs_K, fun h => h_neq h.2⟩
  set U_A : Set ℝ := ⋃ (r : ℝ) (hrA : r ∈ A),
    Classical.choose (hA_rel_open r hrA) with hU_A_def
  have hU_A_open : IsOpen U_A := by
    apply isOpen_iUnion
    intro r
    apply isOpen_iUnion
    intro hrA
    exact (Classical.choose_spec (hA_rel_open r hrA)).1
  have hA_sub_U_A : A ⊆ U_A := by
    intro x hx
    simp only [hU_A_def, Set.mem_iUnion]
    exact ⟨x, hx, (Classical.choose_spec (hA_rel_open x hx)).2.1⟩
  have hU_A_inter_K_sub_A : U_A ∩ K ⊆ A := by
    intro x ⟨hx_U, hx_K⟩
    simp only [hU_A_def, Set.mem_iUnion] at hx_U
    obtain ⟨r, hr_A, hx_r⟩ := hx_U
    exact (Classical.choose_spec (hA_rel_open r hr_A)).2.2 ⟨hx_r, hx_K⟩
  set U_KnA : Set ℝ := ⋃ (r : ℝ) (hrKnA : r ∈ K \ A),
    Classical.choose (hKnA_rel_open r hrKnA) with hU_KnA_def
  have hU_KnA_open : IsOpen U_KnA := by
    apply isOpen_iUnion
    intro r
    apply isOpen_iUnion
    intro hrKnA
    exact (Classical.choose_spec (hKnA_rel_open r hrKnA)).1
  have hKnA_sub_U_KnA : K \ A ⊆ U_KnA := by
    intro x hx
    simp only [hU_KnA_def, Set.mem_iUnion]
    exact ⟨x, hx, (Classical.choose_spec (hKnA_rel_open x hx)).2.1⟩
  have hU_KnA_inter_K_sub_KnA : U_KnA ∩ K ⊆ K \ A := by
    intro x ⟨hx_U, hx_K⟩
    simp only [hU_KnA_def, Set.mem_iUnion] at hx_U
    obtain ⟨r, hr_KnA, hx_r⟩ := hx_U
    exact (Classical.choose_spec (hKnA_rel_open r hr_KnA)).2.2 ⟨hx_r, hx_K⟩
  have hK_cover : K ⊆ U_A ∪ U_KnA := by
    intro x hx_K
    by_cases hxA : x ∈ A
    · exact Or.inl (hA_sub_U_A hxA)
    · exact Or.inr (hKnA_sub_U_KnA ⟨hx_K, hxA⟩)
  have hcontra : (K ∩ (U_A ∩ U_KnA)).Nonempty :=
    hK_conn U_A U_KnA hU_A_open hU_KnA_open hK_cover
      ⟨t₀, ht₀, hA_sub_U_A ht₀_A⟩
      ⟨s, hs_K, hKnA_sub_U_KnA hs_KnA⟩
  obtain ⟨x, hx_K, hx_UA, hx_UKnA⟩ := hcontra
  have hxA : x ∈ A := hU_A_inter_K_sub_A ⟨hx_UA, hx_K⟩
  have hxKnA : x ∈ K \ A := hU_KnA_inter_K_sub_KnA ⟨hx_UKnA, hx_K⟩
  exact hxKnA.2 hxA

end Geodesic
end Riemannian
end Geometry
end DifferentialGeometry
