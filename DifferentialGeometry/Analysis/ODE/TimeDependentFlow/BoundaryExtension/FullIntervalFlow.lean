import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.SmoothDependence.GlobalClosedManifold

/-!
# Full-interval flow of a globally smooth field on a closed manifold

The short-horizon flow engine `global_flow_jointContMDiffOn_on_closed_manifold` produces, anchored
at any time `t₀`, a jointly-`C∞` bare-velocity flow on a small window `Ioo (t₀ - T) (t₀ + T)`.
This file chains those windows into a single flow valid on *any* prescribed interval, by gluing a
freshly anchored window onto a running flow along the integral-curve uniqueness
`bare_integral_flow_eqOn_of_jointC1`.

The headline `global_flow_full_interval_on_closed_manifold` produces, for a globally jointly-`C∞`
field `X`, a flow `Φ : ℝ → M → M` with `Φ 0 = id`, jointly `C∞` on an open interval containing
`[0, T]`, and carrying the bare velocity `X t (Φ t x)` there.
-/

namespace DifferentialGeometry.PDE.RicciFlow.ODE

open Set Function Bundle
open scoped Manifold Topology ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [CompleteSpace E] [BoundarylessManifold I M] [I.Boundaryless] [T2Space M]

omit [CompactSpace M] [I.Boundaryless] in
/-- **One chaining step.** Suppose `Φ` is a flow valid on `Ioo lo hi`: it fixes the basepoint at
time `0`, is jointly `C∞` on `Ioo lo hi ×ˢ univ`, and carries the bare velocity of `X`.  Suppose
further that, anchored at some interior time `t₁ ∈ Ioo lo hi`, a window flow `Ψ : M → ℝ → M` of `X`
fixes its anchor (`Ψ p t₁ = p`), is jointly `C∞` on `Ioo (t₁ - r) (t₁ + r) ×ˢ univ`, and carries
the bare velocity there.  Then the glued flow

  `Φ' s x := if s < t₁ then Φ s x else Ψ (Φ t₁ x) s`

is valid on the longer interval `Ioo lo (t₁ + r)`, and agrees with `Φ` on `Ioo lo hi`.

The agreement on the overlap `Ioo (t₁ - r) hi` is integral-curve uniqueness
(`bare_integral_flow_eqOn_of_jointC1`): both `s ↦ Φ s x` and `s ↦ Ψ (Φ t₁ x) s` are bare integral
curves of `X` through the common point `Φ t₁ x` at time `t₁`.  Joint smoothness of the second piece
is `Ψ`'s smoothness pre-composed with the smooth map `(s, x) ↦ (s, Φ t₁ x)`; across the seam the
two pieces agree on a neighbourhood, so the glued map is locally one smooth piece. -/
theorem flowValid_chain_step
    (X : ℝ → ∀ x : M, TangentSpace I x)
    (hXC1 : AutonomizedFieldJointC1 (I := I) X)
    (Φ : ℝ → M → M) {lo hi : ℝ}
    (hΦ0 : ∀ x : M, Φ 0 x = x)
    (hΦsm : ContMDiffOn (𝓘(ℝ, ℝ).prod I) I ∞ (fun q : ℝ × M => Φ q.1 q.2)
      (Set.Ioo lo hi ×ˢ (Set.univ : Set M)))
    (hΦbare : ∀ t ∈ Set.Ioo lo hi, ∀ x : M,
      HasMFDerivAt 𝓘(ℝ, ℝ) I (fun s : ℝ => Φ s x) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (Φ t x))))
    {t₁ r : ℝ} (ht₁ : t₁ ∈ Set.Ioo lo hi) (h0t₁ : 0 < t₁) (hr : 0 < r)
    (hext : hi ≤ t₁ + r)
    (Ψ : M → ℝ → M)
    (hΨ0 : ∀ p : M, Ψ p t₁ = p)
    (hΨsm : ContMDiffOn (𝓘(ℝ, ℝ).prod I) I ∞ (fun q : ℝ × M => Ψ q.2 q.1)
      (Set.Ioo (t₁ - r) (t₁ + r) ×ˢ (Set.univ : Set M)))
    (hΨbare : ∀ p : M, ∀ t ∈ Set.Ioo (t₁ - r) (t₁ + r),
      HasMFDerivAt 𝓘(ℝ, ℝ) I (fun s : ℝ => Ψ p s) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (Ψ p t)))) :
    ∃ Φ' : ℝ → M → M,
      (∀ x : M, Φ' 0 x = x) ∧
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) I ∞ (fun q : ℝ × M => Φ' q.1 q.2)
        (Set.Ioo lo (t₁ + r) ×ˢ (Set.univ : Set M)) ∧
      (∀ t ∈ Set.Ioo lo (t₁ + r), ∀ x : M,
        HasMFDerivAt 𝓘(ℝ, ℝ) I (fun s : ℝ => Φ' s x) t
          ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (Φ' t x)))) ∧
      (∀ s ∈ Set.Ioo lo hi, ∀ x : M, Φ' s x = Φ s x) := by
  classical
  set Φ' : ℝ → M → M := fun s x => if s < t₁ then Φ s x else Ψ (Φ t₁ x) s with hΦ'_def
  have hlo_t₁ : lo < t₁ := ht₁.1
  have ht₁_hi : t₁ < hi := ht₁.2
  set a₀ : ℝ := max lo (t₁ - r) with ha₀
  have ha₀_lt_t₁ : a₀ < t₁ := max_lt hlo_t₁ (by linarith)
  have ha₀_ge_lo : lo ≤ a₀ := le_max_left _ _
  have ha₀_ge : t₁ - r ≤ a₀ := le_max_right _ _
  -- The reverse window flow `s ↦ Ψ (Φ t₁ x) s` carries the bare velocity of `X`.
  have hΨcurve_bare : ∀ x : M, ∀ t ∈ Set.Ioo (t₁ - r) (t₁ + r),
      HasMFDerivAt 𝓘(ℝ, ℝ) I (fun s : ℝ => Ψ (Φ t₁ x) s) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (Ψ (Φ t₁ x) t))) :=
    fun x t ht => hΨbare (Φ t₁ x) t ht
  -- Overlap: on `Ioo a₀ hi`, the running flow `Φ` and the reverse window agree.
  have hoverlap : ∀ x : M, ∀ s ∈ Set.Ioo a₀ hi, Φ s x = Ψ (Φ t₁ x) s := by
    intro x
    have ht₁_a₀hi : t₁ ∈ Set.Ioo a₀ hi := ⟨ha₀_lt_t₁, ht₁_hi⟩
    have hΦbare' : ∀ t ∈ Set.Ioo a₀ hi,
        HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun s : ℝ => Φ s x) (Set.Ioo a₀ hi) t
          ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (Φ t x))) := by
      intro t ht
      have htmem : t ∈ Set.Ioo lo hi :=
        ⟨lt_of_le_of_lt ha₀_ge_lo ht.1, ht.2⟩
      exact (hΦbare t htmem x).hasMFDerivWithinAt
    have hΨbare' : ∀ t ∈ Set.Ioo a₀ hi,
        HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun s : ℝ => Ψ (Φ t₁ x) s) (Set.Ioo a₀ hi) t
          ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (Ψ (Φ t₁ x) t))) := by
      intro t ht
      have htmem : t ∈ Set.Ioo (t₁ - r) (t₁ + r) :=
        ⟨lt_of_le_of_lt ha₀_ge ht.1, lt_of_lt_of_le ht.2 hext⟩
      exact (hΨcurve_bare x t htmem).hasMFDerivWithinAt
    have hstart : Φ t₁ x = Ψ (Φ t₁ x) t₁ := (hΨ0 (Φ t₁ x)).symm
    exact bare_integral_flow_eqOn_of_jointC1 (a := a₀) (b := hi) (t₀ := t₁)
      X hXC1 (fun s _ => Φ s x) (fun s _ => Ψ (Φ t₁ x) s) x x ht₁_a₀hi
      hΦbare' hΨbare' hstart
  -- On the window `Ioo a₀ (t₁ + r) ×ˢ univ`, the glued flow equals the smooth reverse window.
  have hΦ'_eq_Ψ : ∀ s ∈ Set.Ioo a₀ (t₁ + r), ∀ x : M, Φ' s x = Ψ (Φ t₁ x) s := by
    intro s hs x
    by_cases hlt : s < t₁
    · simp only [hΦ'_def, if_pos hlt]
      exact hoverlap x s ⟨hs.1, lt_trans hlt ht₁_hi⟩
    · simp only [hΦ'_def, if_neg hlt]
  -- On `Ioo lo t₁`, the glued flow equals the running flow.
  have hΦ'_eq_Φ_left : ∀ s ∈ Set.Ioo lo t₁, ∀ x : M, Φ' s x = Φ s x := by
    intro s hs x
    simp only [hΦ'_def, if_pos hs.2]
  have hΨsm' : ContMDiffOn (𝓘(ℝ, ℝ).prod I) I ∞ (fun q : ℝ × M => Ψ (Φ t₁ q.2) q.1)
      (Set.Ioo (t₁ - r) (t₁ + r) ×ˢ (Set.univ : Set M)) := by
    have hΦt₁ : ContMDiff I I ∞ (fun x : M => Φ t₁ x) := by
      intro x
      have hmem : ((t₁, x) : ℝ × M) ∈ Set.Ioo lo hi ×ˢ (Set.univ : Set M) :=
        ⟨ht₁, Set.mem_univ _⟩
      have hxsm : ContMDiffWithinAt (𝓘(ℝ, ℝ).prod I) I ∞ (fun q : ℝ × M => Φ q.1 q.2)
          (Set.Ioo lo hi ×ˢ (Set.univ : Set M)) (t₁, x) := hΦsm _ hmem
      have hpair : ContMDiffAt I (𝓘(ℝ, ℝ).prod I) ∞ (fun y : M => ((t₁, y) : ℝ × M)) x :=
        (contMDiffAt_const).prodMk contMDiffAt_id
      have hmaps : Set.MapsTo (fun y : M => ((t₁, y) : ℝ × M)) (Set.univ : Set M)
          (Set.Ioo lo hi ×ˢ (Set.univ : Set M)) := fun y _ => ⟨ht₁, Set.mem_univ _⟩
      have := (hxsm.comp x hpair.contMDiffWithinAt hmaps)
      simpa using this.contMDiffAt (by
        exact Filter.univ_mem)
    have hg : ContMDiff (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod I) ∞
        (fun q : ℝ × M => ((q.1, Φ t₁ q.2) : ℝ × M)) :=
      contMDiff_fst.prodMk (hΦt₁.comp contMDiff_snd)
    have hcomp := hΨsm.comp (hg.contMDiffOn (s := Set.Ioo (t₁ - r) (t₁ + r) ×ˢ (Set.univ : Set M)))
      (fun q hq => by exact ⟨hq.1, Set.mem_univ _⟩)
    refine hcomp.congr ?_
    intro q hq
    rfl
  refine ⟨Φ', ?_, ?_, ?_, ?_⟩
  · intro x
    have h0 : (0 : ℝ) < t₁ := h0t₁
    simp only [hΦ'_def, if_pos h0]
    exact hΦ0 x
  · -- Joint smoothness on `Ioo lo (t₁ + r) ×ˢ univ`.
    intro q hq
    obtain ⟨hq1, _⟩ := hq
    by_cases hlt : q.1 < t₁
    · -- near a left point, `Φ' = Φ`
      have hWopen : IsOpen (Set.Ioo lo t₁ ×ˢ (Set.univ : Set M)) := isOpen_Ioo.prod isOpen_univ
      have hqW : q ∈ Set.Ioo lo t₁ ×ˢ (Set.univ : Set M) := ⟨⟨hq1.1, hlt⟩, Set.mem_univ _⟩
      have hΦW : ContMDiffWithinAt (𝓘(ℝ, ℝ).prod I) I ∞ (fun q : ℝ × M => Φ q.1 q.2)
          (Set.Ioo lo t₁ ×ˢ (Set.univ : Set M)) q :=
        (hΦsm.mono (Set.prod_mono (Set.Ioo_subset_Ioo_right (le_of_lt ht₁_hi)) (subset_refl _))) q hqW
      have hcongr : ∀ q' ∈ Set.Ioo lo t₁ ×ˢ (Set.univ : Set M),
          (fun q : ℝ × M => Φ' q.1 q.2) q' = (fun q : ℝ × M => Φ q.1 q.2) q' := by
        rintro ⟨s, x⟩ ⟨hs, _⟩
        exact hΦ'_eq_Φ_left s hs x
      have hWnhds : Set.Ioo lo t₁ ×ˢ (Set.univ : Set M) ∈
          𝓝[Set.Ioo lo (t₁ + r) ×ˢ (Set.univ : Set M)] q :=
        mem_nhdsWithin_of_mem_nhds (hWopen.mem_nhds hqW)
      have hΦ'W : ContMDiffWithinAt (𝓘(ℝ, ℝ).prod I) I ∞ (fun q : ℝ × M => Φ' q.1 q.2)
          (Set.Ioo lo t₁ ×ˢ (Set.univ : Set M)) q := by
        refine hΦW.congr_of_eventuallyEq ?_ (hcongr q hqW)
        filter_upwards [self_mem_nhdsWithin] with q' hq' using hcongr q' hq'
      exact hΦ'W.mono_of_mem_nhdsWithin hWnhds
    · -- near a right point (`q.1 ≥ t₁`), `Φ' = Ψ(Φt₁·)`
      have hq1_a₀ : a₀ < q.1 := lt_of_lt_of_le ha₀_lt_t₁ (not_lt.mp hlt)
      have hWopen : IsOpen (Set.Ioo a₀ (t₁ + r) ×ˢ (Set.univ : Set M)) :=
        isOpen_Ioo.prod isOpen_univ
      have hqW : q ∈ Set.Ioo a₀ (t₁ + r) ×ˢ (Set.univ : Set M) :=
        ⟨⟨hq1_a₀, hq1.2⟩, Set.mem_univ _⟩
      have hsubΨ : Set.Ioo a₀ (t₁ + r) ×ˢ (Set.univ : Set M) ⊆
          Set.Ioo (t₁ - r) (t₁ + r) ×ˢ (Set.univ : Set M) :=
        Set.prod_mono (Set.Ioo_subset_Ioo_left ha₀_ge) (subset_refl _)
      have hΨW : ContMDiffWithinAt (𝓘(ℝ, ℝ).prod I) I ∞ (fun q : ℝ × M => Ψ (Φ t₁ q.2) q.1)
          (Set.Ioo a₀ (t₁ + r) ×ˢ (Set.univ : Set M)) q :=
        (hΨsm'.mono hsubΨ) q hqW
      have hcongr : ∀ q' ∈ Set.Ioo a₀ (t₁ + r) ×ˢ (Set.univ : Set M),
          (fun q : ℝ × M => Φ' q.1 q.2) q' = (fun q : ℝ × M => Ψ (Φ t₁ q.2) q.1) q' := by
        rintro ⟨s, x⟩ ⟨hs, _⟩
        exact hΦ'_eq_Ψ s hs x
      have hWnhds : Set.Ioo a₀ (t₁ + r) ×ˢ (Set.univ : Set M) ∈
          𝓝[Set.Ioo lo (t₁ + r) ×ˢ (Set.univ : Set M)] q :=
        mem_nhdsWithin_of_mem_nhds (hWopen.mem_nhds hqW)
      have hΦ'W : ContMDiffWithinAt (𝓘(ℝ, ℝ).prod I) I ∞ (fun q : ℝ × M => Φ' q.1 q.2)
          (Set.Ioo a₀ (t₁ + r) ×ˢ (Set.univ : Set M)) q := by
        refine hΨW.congr_of_eventuallyEq ?_ (hcongr q hqW)
        filter_upwards [self_mem_nhdsWithin] with q' hq' using hcongr q' hq'
      exact hΦ'W.mono_of_mem_nhdsWithin hWnhds
  · -- Bare velocity on `Ioo lo (t₁ + r)`.
    intro t ht x
    by_cases hlt : t < t₁
    · have hev : (fun s : ℝ => Φ' s x) =ᶠ[𝓝 t] (fun s : ℝ => Φ s x) := by
        have hmem : Set.Iio t₁ ∈ 𝓝 t := isOpen_Iio.mem_nhds hlt
        filter_upwards [hmem] with s hs
        simp only [hΦ'_def, if_pos (Set.mem_Iio.mp hs)]
      have hΦ't : Φ' t x = Φ t x := by simp only [hΦ'_def, if_pos hlt]
      have htmem : t ∈ Set.Ioo lo hi := ⟨ht.1, lt_trans hlt ht₁_hi⟩
      rw [hΦ't]
      exact (hΦbare t htmem x).congr_of_eventuallyEq hev
    · have hq1_a₀ : a₀ < t := lt_of_lt_of_le ha₀_lt_t₁ (not_lt.mp hlt)
      have hev : (fun s : ℝ => Φ' s x) =ᶠ[𝓝 t] (fun s : ℝ => Ψ (Φ t₁ x) s) := by
        have hmem : Set.Ioo a₀ (t₁ + r) ∈ 𝓝 t := isOpen_Ioo.mem_nhds ⟨hq1_a₀, ht.2⟩
        filter_upwards [hmem] with s hs
        exact hΦ'_eq_Ψ s hs x
      have hΦ't : Φ' t x = Ψ (Φ t₁ x) t := hΦ'_eq_Ψ t ⟨hq1_a₀, ht.2⟩ x
      have htmem : t ∈ Set.Ioo (t₁ - r) (t₁ + r) := ⟨lt_of_le_of_lt ha₀_ge hq1_a₀, ht.2⟩
      rw [hΦ't]
      exact (hΨcurve_bare x t htmem).congr_of_eventuallyEq hev
  · intro s hs x
    by_cases hlt : s < t₁
    · simp only [hΦ'_def, if_pos hlt]
    · simp only [hΦ'_def, if_neg hlt]
      have hsmem : s ∈ Set.Ioo a₀ hi :=
        ⟨lt_of_lt_of_le ha₀_lt_t₁ (not_lt.mp hlt), hs.2⟩
      exact (hoverlap x s hsmem).symm

end DifferentialGeometry.PDE.RicciFlow.ODE
