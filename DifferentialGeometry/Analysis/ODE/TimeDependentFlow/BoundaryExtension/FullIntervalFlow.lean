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

/-- A two-sided smooth bump on the closed interval `[lo, hi]`: it equals `1` on `Icc lo hi`
(indeed on the open `Ioo (lo - 1) (hi + 1)`) and vanishes outside `Icc (lo - 2) (hi + 2)`,
built from `Real.smoothTransition`.  Used to cut a globally smooth field down to one with
compact time support that still agrees with the original on `[lo, hi]`. -/
private noncomputable def fullIntervalBump (lo hi : ℝ) (s : ℝ) : ℝ :=
  Real.smoothTransition (s - (lo - 2)) * Real.smoothTransition ((hi + 2) - s)

private theorem fullIntervalBump_contDiff (lo hi : ℝ) :
    ContDiff ℝ ∞ (fullIntervalBump lo hi) := by
  unfold fullIntervalBump
  exact (Real.smoothTransition.contDiff.comp (by fun_prop)).mul
    (Real.smoothTransition.contDiff.comp (by fun_prop))

private theorem fullIntervalBump_eq_one (lo hi s : ℝ) (hs : s ∈ Set.Icc lo hi) :
    fullIntervalBump lo hi s = 1 := by
  unfold fullIntervalBump
  rw [Real.smoothTransition.one_of_one_le (by linarith [hs.1]),
    Real.smoothTransition.one_of_one_le (by linarith [hs.2]), mul_one]

private theorem fullIntervalBump_eq_zero (lo hi s : ℝ)
    (hs : s ∉ Set.Icc (lo - 2) (hi + 2)) : fullIntervalBump lo hi s = 0 := by
  unfold fullIntervalBump
  rw [Set.mem_Icc, not_and_or] at hs
  rcases hs with hlo | hhi
  · have : s < lo - 2 := lt_of_not_ge hlo
    rw [Real.smoothTransition.zero_of_nonpos (by linarith : s - (lo - 2) ≤ 0), zero_mul]
  · have : hi + 2 < s := lt_of_not_ge hhi
    rw [Real.smoothTransition.zero_of_nonpos (by linarith : (hi + 2) - s ≤ 0), mul_zero]

omit [FiniteDimensional ℝ E] [CompactSpace M] [CompleteSpace E] [BoundarylessManifold I M]
  [I.Boundaryless] [T2Space M] in
/-- The cut-off field `X̃ s x = fullIntervalBump lo hi s • X s x` is globally `C∞` whenever the
geometric field `X` is.  The fibre coordinate of a tangent-bundle trivialization is fibre-linear,
so the scalar commutes through it, reducing the goal to `ContMDiffAt.smul` of the (smooth) scalar
with the (smooth) fibre coordinate of `X`. -/
private theorem cutoffField_contMDiff
    (X : ℝ → ∀ x : M, TangentSpace I x)
    (hX : ContMDiff (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
      (fun q : ℝ × M => (TotalSpace.mk' E q.2 (X q.1 q.2) : TangentBundle I M)))
    (lo hi : ℝ) :
    ContMDiff (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
      (fun q : ℝ × M =>
        (TotalSpace.mk' E q.2 (fullIntervalBump lo hi q.1 • X q.1 q.2) : TangentBundle I M)) := by
  have hbump : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun q : ℝ × M => fullIntervalBump lo hi q.1) :=
    (fullIntervalBump_contDiff lo hi).contMDiff.comp contMDiff_fst
  intro q₀
  have hXat := hX q₀
  rw [Bundle.contMDiffAt_totalSpace] at hXat ⊢
  obtain ⟨hXproj, hXfib⟩ := hXat
  refine ⟨hXproj, ?_⟩
  set e := trivializationAt E (TangentSpace I) q₀.2 with he
  have hfib := (hbump q₀).smul hXfib
  have hmem : e.baseSet ∈ nhds q₀.2 :=
    e.open_baseSet.mem_nhds (FiberBundle.mem_baseSet_trivializationAt' q₀.2)
  have hpre : (fun q : ℝ × M => q.2) ⁻¹' e.baseSet ∈ nhds q₀ :=
    (continuous_snd.continuousAt) hmem
  refine hfib.congr_of_eventuallyEq ?_
  filter_upwards [hpre] with x hx
  simpa using (e.linear ℝ hx).2 (fullIntervalBump lo hi x.1) (X x.1 x.2)

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [CompactSpace M] [CompleteSpace E]
  [BoundarylessManifold I M] [I.Boundaryless] [T2Space M] in
/-- Where the field `Xt` vanishes along the straight line `s ↦ (pt.1 + s, pt.2)`, that line is an
integral curve of the autonomised field `autonomizedFlowVF Xt` (its velocity is `(1, 0)`).  Used
for points outside the compact time-support slab of a cut-off field. -/
private theorem trivialLine_isMIntegralCurveOn
    (Xt : ℝ → ∀ x : M, TangentSpace I x) (pt : ℝ × M) (S : Set ℝ)
    (hzero : ∀ s ∈ S, Xt (pt.1 + s) pt.2 = 0) :
    IsMIntegralCurveOn (fun s : ℝ => (pt.1 + s, pt.2)) (autonomizedFlowVF Xt) S := by
  intro t ht
  have htime : HasMFDerivWithinAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun s : ℝ => pt.1 + s) S t
      (1 : ℝ →L[ℝ] ℝ) := by
    have h1 := hasMFDerivWithinAt_const (I := 𝓘(ℝ, ℝ)) (I' := 𝓘(ℝ, ℝ)) pt.1 S t
    have h2 := hasMFDerivWithinAt_id (I := 𝓘(ℝ, ℝ)) S t
    have h3 := h1.add h2
    have hfun : ((fun _ : ℝ => pt.1) + id) = (fun s : ℝ => pt.1 + s) := by funext s; simp
    rw [hfun] at h3
    refine h3.congr_mfderiv ?_
    apply ContinuousLinearMap.ext; intro x
    show (0 : ℝ →L[ℝ] ℝ) x + ContinuousLinearMap.id ℝ ℝ x = (1 : ℝ →L[ℝ] ℝ) x
    simp
  have hsnd : HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun _ : ℝ => pt.2) S t
      (0 : TangentSpace 𝓘(ℝ, ℝ) t →L[ℝ] TangentSpace I pt.2) :=
    hasMFDerivWithinAt_const (I := 𝓘(ℝ, ℝ)) (I' := I) pt.2 S t
  have hprod := htime.prodMk hsnd
  have hCLM : ((1 : ℝ →L[ℝ] ℝ).smulRight (autonomizedFlowVF Xt (pt.1 + t, pt.2)))
      = (1 : ℝ →L[ℝ] ℝ).prod (0 : TangentSpace 𝓘(ℝ, ℝ) t →L[ℝ] TangentSpace I pt.2) := by
    apply ContinuousLinearMap.ext; intro r; apply Prod.ext
    · change r • (1 : ℝ) = r; simp
    · change r • Xt (pt.1 + t) pt.2 = (0 : TangentSpace I pt.2)
      rw [hzero t ht, smul_zero]
  rw [hCLM]; exact hprod

omit [CompactSpace M] in
/-- **Local existence uniform over a neighbourhood of starting points.** Applying the manifold
local-flow theorem `local_flow_jointSmooth_and_integralCurve` to the *autonomous* field
`autonomizedFlowVF Xt` on the product manifold `ℝ × M`, every point `pt : ℝ × M` has an open
neighbourhood `U ∋ pt` and a window radius `T > 0` such that every `q ∈ U` carries an integral
curve of `autonomizedFlowVF Xt` on `Ioo (-T) T` through `q` at parameter `0`. -/
private theorem autonomized_localUniform_curve
    (Xt : ℝ → ∀ x : M, TangentSpace I x)
    (hXt : ContMDiff (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
      (fun q : ℝ × M => (TotalSpace.mk' E q.2 (Xt q.1 q.2) : TangentBundle I M)))
    (pt : ℝ × M) :
    ∃ (U : Set (ℝ × M)) (_ : IsOpen U) (_ : pt ∈ U) (T : ℝ) (_ : 0 < T),
      ∀ q ∈ U, ∃ γ : ℝ → ℝ × M, γ 0 = q ∧
        IsMIntegralCurveOn γ (autonomizedFlowVF Xt) (Set.Ioo (-T) T) := by
  have hsm : ContMDiff (𝓘(ℝ, ℝ).prod (𝓘(ℝ, ℝ).prod I))
      ((𝓘(ℝ, ℝ).prod I).prod 𝓘(ℝ, ℝ × E)) ∞
      (fun q' : ℝ × (ℝ × M) =>
        (TotalSpace.mk' (ℝ × E) q'.2
          ((fun (_ : ℝ) (q : ℝ × M) => autonomizedFlowVF Xt q) q'.1 q'.2) :
          TangentBundle (𝓘(ℝ, ℝ).prod I) (ℝ × M))) :=
    (autonomizedFlowVF_section_contMDiff Xt hXt).comp contMDiff_snd
  obtain ⟨U, hU_open, hpt_U, T, hT_pos, Ψ, hΨinit, _hΨsm, hΨbare⟩ :=
    local_flow_jointSmooth_and_integralCurve
      (I := 𝓘(ℝ, ℝ).prod I) (M := ℝ × M)
      (fun (_ : ℝ) (q : ℝ × M) => autonomizedFlowVF Xt q) hsm 0 pt
  refine ⟨U, hU_open, hpt_U, T, hT_pos, fun q hq => ⟨fun s => Ψ q s, ?_, ?_⟩⟩
  · have := hΨinit q hq; simpa using this
  · intro t ht
    exact (hΨbare q hq t (by simpa using ht)).hasMFDerivWithinAt

/-- **Uniform-radius local existence on `ℝ × M`.** For a cut-off field `Xt` that vanishes outside
the compact time slab `Icc (lo - 2) (hi + 2)`, there is a single radius `ε > 0` such that *every*
point of `ℝ × M` carries an integral curve of `autonomizedFlowVF Xt` on `Ioo (-ε) ε`.  Over the
compact slab `Icc (lo - 3) (hi + 3) ×ˢ univ` a finite subcover by the neighbourhood windows of
`autonomized_localUniform_curve` gives a uniform radius; outside the slab the field vanishes along
the straight line, which is a global integral curve.  This is the uniform-time hypothesis consumed
by Mathlib's `exists_isMIntegralCurve_of_isMIntegralCurveOn`. -/
private theorem autonomized_uniform_localExistence
    (Xt : ℝ → ∀ x : M, TangentSpace I x)
    (hXt : ContMDiff (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
      (fun q : ℝ × M => (TotalSpace.mk' E q.2 (Xt q.1 q.2) : TangentBundle I M)))
    (lo hi : ℝ)
    (hvanish : ∀ s : ℝ, s ∉ Set.Icc (lo - 2) (hi + 2) → ∀ x : M, Xt s x = 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ pt : ℝ × M, ∃ γ : ℝ → ℝ × M, γ 0 = pt ∧
      IsMIntegralCurveOn γ (autonomizedFlowVF Xt) (Set.Ioo (-ε) ε) := by
  classical
  choose Uwin hUopen hUmem Twin hTpos hwin using autonomized_localUniform_curve Xt hXt
  have hK : IsCompact (Set.Icc (lo - 3) (hi + 3) ×ˢ (Set.univ : Set M)) :=
    isCompact_Icc.prod isCompact_univ
  have hcover : (Set.Icc (lo - 3) (hi + 3) ×ˢ (Set.univ : Set M)) ⊆ ⋃ pt, Uwin pt :=
    fun x _ => Set.mem_iUnion.mpr ⟨x, hUmem x⟩
  obtain ⟨sf, hsf⟩ := hK.elim_finite_subcover Uwin hUopen hcover
  set T₀ : ℝ := if h : sf.Nonempty then sf.inf' h Twin else 1 with hT₀
  have hT₀_pos : 0 < T₀ := by
    rw [hT₀]; split
    · next h => rw [Finset.lt_inf'_iff]; exact fun pt _ => hTpos pt
    · exact one_pos
  have hT₀_le : ∀ pt ∈ sf, T₀ ≤ Twin pt := by
    intro pt hpt; rw [hT₀]; split
    · next h => exact Finset.inf'_le _ hpt
    · next h => exact absurd ⟨pt, hpt⟩ h
  refine ⟨min 1 T₀, lt_min one_pos hT₀_pos, fun pt => ?_⟩
  by_cases hpt_slab : pt.1 ∈ Set.Icc (lo - 3) (hi + 3)
  · have hpt_K : pt ∈ Set.Icc (lo - 3) (hi + 3) ×ˢ (Set.univ : Set M) :=
      ⟨hpt_slab, Set.mem_univ _⟩
    have hmem := hsf hpt_K
    rw [Set.mem_iUnion₂] at hmem
    obtain ⟨pti, hpti_sf, hpt_Ui⟩ := hmem
    obtain ⟨γ, hγ0, hγcurve⟩ := hwin pti pt hpt_Ui
    refine ⟨γ, hγ0, hγcurve.mono ?_⟩
    have hle : min 1 T₀ ≤ Twin pti := le_trans (min_le_right _ _) (hT₀_le pti hpti_sf)
    exact Set.Ioo_subset_Ioo (by linarith) (by linarith)
  · refine ⟨fun s => (pt.1 + s, pt.2), by simp, ?_⟩
    apply trivialLine_isMIntegralCurveOn Xt pt
    intro s hs
    apply hvanish (pt.1 + s) ?_ pt.2
    rw [Set.mem_Ioo] at hs
    rw [Set.mem_Icc]
    rw [Set.mem_Icc, not_and_or] at hpt_slab
    have hs1 : |s| < 1 := lt_of_lt_of_le (abs_lt.mpr ⟨hs.1, hs.2⟩) (min_le_left _ _)
    rw [abs_lt] at hs1
    rintro ⟨hle1, hle2⟩
    rcases hpt_slab with hlow | hhigh
    · have : pt.1 < lo - 3 := lt_of_not_ge hlow
      linarith [hs1.1]
    · have : hi + 3 < pt.1 := lt_of_not_ge hhigh
      linarith [hs1.2]

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [CompactSpace M] [CompleteSpace E]
  [BoundarylessManifold I M] [I.Boundaryless] [T2Space M] in
/-- The time component of a *global* integral curve `c` of `autonomizedFlowVF Xt` whose value at
`0` has first coordinate `0` is the identity `(c s).1 = s`: the first component of the autonomised
velocity is the constant `1`, so `(c ·).1` solves `φ' = 1, φ 0 = 0`. -/
private theorem autonomized_time_comp_eq_self
    (Xt : ℝ → ∀ x : M, TangentSpace I x) (c : ℝ → ℝ × M)
    (hc : IsMIntegralCurve c (autonomizedFlowVF Xt)) (h0 : (c 0).1 = 0) :
    ∀ s, (c s).1 = s := by
  have hderiv : ∀ s, HasDerivAt (fun u => (c u).1) (1 : ℝ) s :=
    fun s => autonomizedFlow_fst_hasDerivAt Xt c s (hc s)
  intro s
  have hconst : ∀ u : ℝ, HasDerivAt (fun w => (c w).1 - w) (0 : ℝ) u :=
    fun u => by simpa using (hderiv u).sub (hasDerivAt_id u)
  have hkey : (fun w => (c w).1 - w) s = (fun w => (c w).1 - w) 0 :=
    is_const_of_deriv_eq_zero (fun u => (hconst u).differentiableAt) (fun u => (hconst u).deriv) s 0
  simp only at hkey; rw [h0] at hkey; linarith

omit [FiniteDimensional ℝ E] [CompactSpace M] [CompleteSpace E] [I.Boundaryless] in
/-- **Global bare flow of a globally `C∞` field, from uniform-radius local existence.** Given a
field `Xt` with jointly-`C¹` autonomisation and a uniform local-existence radius `ε`, Mathlib's
`exists_isMIntegralCurve_of_isMIntegralCurveOn` upgrades the local curves to *global* integral
curves of `autonomizedFlowVF Xt`; choosing the one through `(0, x)` and taking its spatial
component yields a flow `Φ` with `Φ 0 = id` carrying the bare velocity `Xt t (Φ t x)` at *every*
time `t : ℝ`.  (Joint smoothness in `(t, x)` is *not* produced here — that is a separate
obligation; see the headline.) -/
private theorem global_bareFlow_of_uniform_localExistence
    (Xt : ℝ → ∀ x : M, TangentSpace I x)
    (hXtC1 : AutonomizedFieldJointC1 (I := I) Xt)
    {ε : ℝ} (hε : 0 < ε)
    (huniform : ∀ pt : ℝ × M, ∃ γ : ℝ → ℝ × M, γ 0 = pt ∧
      IsMIntegralCurveOn γ (autonomizedFlowVF Xt) (Set.Ioo (-ε) ε)) :
    ∃ Φ : ℝ → M → M, (∀ x, Φ 0 x = x) ∧
      (∀ t : ℝ, ∀ x : M, HasMFDerivAt 𝓘(ℝ, ℝ) I (fun s => Φ s x) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight (Xt t (Φ t x)))) := by
  classical
  have hglobal := fun pt : ℝ × M =>
    exists_isMIntegralCurve_of_isMIntegralCurveOn (v := autonomizedFlowVF Xt)
      (fun p => hXtC1 p) hε huniform pt
  choose c hc0 hc using fun x : M => hglobal ((0 : ℝ), x)
  refine ⟨fun s x => (c x s).2, fun x => by simp [hc0 x], ?_⟩
  intro t x
  have htime : ∀ s, (c x s).1 = s :=
    autonomized_time_comp_eq_self Xt (c x) (hc x) (by rw [hc0 x])
  have hsnd := autonomizedFlow_snd_hasMFDerivAt Xt (c x) t (hc x t)
  rw [htime t] at hsnd
  exact hsnd

/-- **Full-interval flow of a globally smooth field on a closed manifold.**

For a globally jointly-`C∞` time-dependent field `X` on a closed manifold and any horizon
`T > 0`, there is a flow `Φ : ℝ → M → M` with `Φ 0 = id`, jointly `C∞` on an open interval
`Ioo lo hi ⊇ [0, T]` (with `lo < 0 < T < hi`), carrying the bare velocity `X t (Φ t x)`.

The construction (`lo := -1`, `hi := T + 1`) cuts `X` down to the field
`X̃ s x = fullIntervalBump (-1) (T+1) s • X s x`, which is globally `C∞` (`cutoffField_contMDiff`),
agrees with `X` on `[lo, hi]` (`fullIntervalBump_eq_one`), and has compact time support
(`fullIntervalBump_eq_zero`).  Applying the manifold local-flow theorem to the *autonomous* field
`(1, X̃)` on `ℝ × M`, a finite subcover of the compact slab `Icc (lo-3) (hi+3) ×ˢ univ` plus the
trivial straight-line curve outside it gives a uniform local-existence radius
(`autonomized_uniform_localExistence`); Mathlib's `exists_isMIntegralCurve_of_isMIntegralCurveOn`
then upgrades to global integral curves, whose spatial components form a flow `Φ` with `Φ 0 = id`
and the bare velocity `X̃ t (Φ t x) = X t (Φ t x)` on `[lo, hi]`
(`global_bareFlow_of_uniform_localExistence`).

The remaining `sorry` is the *joint* smoothness `ContMDiffOn … (Ioo lo hi ×ˢ univ)` ONLY.  This is
the global smooth-dependence-on-initial-conditions of the flow over a fixed time interval extending
past the arbitrary horizon `T`.  The manifold local-flow theorem supplies joint smoothness only on a
per-anchor window of positive but un-uniform-over-time radius; extending it to the fixed `(lo, hi)`
requires transporting smooth dependence over time (invertible flow slices or a global
smooth-dependence theorem), which is not available in the present library — the sibling
`interior_extends_anchor` (in `SmoothDependence/IntervalGlobalFlow.lean`) states exactly this
extension and is itself an unfilled `sorry`.  Everything except this single joint-smoothness
obligation is fully proven above. -/
theorem global_flow_full_interval_on_closed_manifold
    (X : ℝ → ∀ x : M, TangentSpace I x)
    (hX : ContMDiff (𝓘(ℝ,ℝ).prod I) (I.prod 𝓘(ℝ,E)) ∞
      (fun q : ℝ × M => (TotalSpace.mk' E q.2 (X q.1 q.2) : TangentBundle I M)))
    (T : ℝ) (hT : 0 < T) :
    ∃ (Φ : ℝ → M → M) (lo hi : ℝ), lo < 0 ∧ T < hi ∧ (∀ x, Φ 0 x = x) ∧
      ContMDiffOn (𝓘(ℝ,ℝ).prod I) I ∞ (fun q : ℝ × M => Φ q.1 q.2) (Set.Ioo lo hi ×ˢ Set.univ) ∧
      (∀ t ∈ Set.Ioo lo hi, ∀ x : M, HasMFDerivAt 𝓘(ℝ,ℝ) I (fun s => Φ s x) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (Φ t x)))) := by
  set Xt : ℝ → ∀ x : M, TangentSpace I x :=
    fun s x => fullIntervalBump (-1) (T + 1) s • X s x with hXt_def
  have hXt_sm : ContMDiff (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
      (fun q : ℝ × M => (TotalSpace.mk' E q.2 (Xt q.1 q.2) : TangentBundle I M)) :=
    cutoffField_contMDiff X hX (-1) (T + 1)
  have hXtC1 : AutonomizedFieldJointC1 (I := I) Xt :=
    autonomizedFieldJointC1_of_contMDiff Xt hXt_sm
  have hXt_eq : ∀ s ∈ Set.Icc (-1 : ℝ) (T + 1), ∀ x : M, Xt s x = X s x := by
    intro s hs x
    rw [hXt_def]
    simp only [fullIntervalBump_eq_one (-1) (T + 1) s hs, one_smul]
  have hvanish : ∀ s : ℝ, s ∉ Set.Icc (-1 - 2 : ℝ) (T + 1 + 2) → ∀ x : M, Xt s x = 0 := by
    intro s hs x
    rw [hXt_def]
    simp only [fullIntervalBump_eq_zero (-1) (T + 1) s hs, zero_smul]
  obtain ⟨ε, hε, huniform⟩ :=
    autonomized_uniform_localExistence Xt hXt_sm (-1) (T + 1) hvanish
  obtain ⟨Φ, hΦ0, hΦbare⟩ :=
    global_bareFlow_of_uniform_localExistence Xt hXtC1 hε huniform
  refine ⟨Φ, -1, T + 1, by norm_num, by linarith, hΦ0, ?_, ?_⟩
  · sorry
  · intro t ht x
    have htIcc : t ∈ Set.Icc (-1 : ℝ) (T + 1) := ⟨le_of_lt ht.1, le_of_lt ht.2⟩
    have hb := hΦbare t x
    rw [hXt_eq t htIcc (Φ t x)] at hb
    exact hb

end DifferentialGeometry.PDE.RicciFlow.ODE
