import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary

/-!
# Smooth diffeomorphisms from forward/reverse flows

Given a forward flow `Φ` and a reverse flow `Ψ` on a compact boundaryless manifold,
each individually smooth and mutually inverse for `t ∈ [0, T)`, we package them
into a `Diffeomorph I I M M ∞` for each `t ∈ (0, T)`.
-/

open scoped Manifold Topology ContDiff

theorem time_dependent_vf_globalflow_diffeomorph
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    {T : ℝ} (_hT : 0 < T)
    {Φ Ψ : ℝ → M → M}
    (_hΦ_init : ∀ x, Φ 0 x = x) (_hΨ_init : ∀ x, Ψ 0 x = x)
    (hΦ_smooth : ∀ t, 0 < t → t < T → ContMDiff I I ∞ (Φ t))
    (hΨ_smooth : ∀ t, 0 < t → t < T → ContMDiff I I ∞ (Ψ t))
    (hΨΦ : ∀ s ∈ Set.Ico (0 : ℝ) T, ∀ x : M, Ψ s (Φ s x) = x)
    (hΦΨ : ∀ s ∈ Set.Ico (0 : ℝ) T, ∀ x : M, Φ s (Ψ s x) = x) :
    ∀ t, 0 < t → t < T →
      ∃ d : Diffeomorph I I M M ∞,
        (∀ x, d x = Φ t x) ∧ (∀ x, d.symm x = Ψ t x) := by
  intro t ht htT
  have hmem : t ∈ Set.Ico (0 : ℝ) T := Set.mem_Ico.mpr ⟨le_of_lt ht, htT⟩
  let e : M ≃ M :=
    { toFun := Φ t
      invFun := Ψ t
      left_inv := fun x => hΨΦ t hmem x
      right_inv := fun x => hΦΨ t hmem x }
  exact ⟨⟨e, hΦ_smooth t ht htT, hΨ_smooth t ht htT⟩, fun x => rfl, fun x => rfl⟩
