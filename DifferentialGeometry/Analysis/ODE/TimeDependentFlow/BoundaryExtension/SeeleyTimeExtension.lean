import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.SmoothInSpace.ChartOperator.ConventionBridge

/-!
# Smooth time-extension of a field smooth on a closed time slab

A time-dependent field `X` that is jointly `C∞` (as a tangent-bundle section) on the *closed*
time slab `Icc 0 T ×ˢ univ` is extended to a field `Xext` that is jointly `C∞` on all of
`ℝ × M` and agrees with `X` on `Icc 0 T`.  This is the Seeley/Whitney smooth-extension-across-a-
boundary statement at the level of the joint tangent-bundle section: unlike the merely-continuous
time-clamp `field_time_clamp_extension`, the extension is smooth across the slab endpoints
`t = 0` and `t = T`, so the autonomised flow field `(1, Xext)` is `C∞` on all of `ℝ × M`.

The construction is the standard Seeley reflection/extension applied in the time variable, fibre
by fibre over `M`; it is recorded here as an isolated deferred input (its body is a later wave's
work), so consumers transitively depend on `sorryAx`.
-/

namespace DifferentialGeometry.PDE.RicciFlow.ODE

open Set Function Bundle
open scoped Manifold Topology ContDiff
open DifferentialGeometry.Integral.Connection

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

set_option linter.unusedSectionVars false in
/-- **Per-chart Euclidean joint reading of a time-dependent section.** If the joint
tangent-bundle section of a family `X` is `ContMDiffOn` on the slab `s ×ˢ univ`, then for any
chart centre `α` its chart-Euclidean reading `(t, z) ↦ chartE_section_repr α (X t) z` (the
trivialised representation of `X t` through the canonical trivialization at `α`) is
`ContMDiffOn (𝓘(ℝ,ℝ).prod I) 𝓘(ℝ,E)` on `s ×ˢ (chartAt H α).source`.

This reads the joint section through the *fixed* trivialization at `α` via
`Bundle.Trivialization.contMDiffWithinAt_iff`, then identifies the fibre coordinate with
`chartE_section_repr` on the trivialization base set
(`chartE_section_repr_eq_trivialization_snd`). -/
theorem chartE_jointReading_contMDiffOn
    (X : ℝ → ∀ x : M, TangentSpace I x) (s : Set ℝ) (α : M)
    (hX : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
      (fun q : ℝ × M => (TotalSpace.mk' E q.2 (X q.1 q.2) : TangentBundle I M))
      (s ×ˢ (univ : Set M))) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, E) ∞
      (fun q : ℝ × M => chartE_section_repr (I := I) α (X q.1) q.2)
      (s ×ˢ (chartAt H α).source) := by
  set e : Trivialization E (π E (TangentSpace I : M → Type _)) :=
    trivializationAt E (TangentSpace I) α with he
  have hbase : (chartAt H α).source ⊆ e.baseSet := by
    rw [he, TangentBundle.trivializationAt_baseSet]
  have hmaps : Set.MapsTo
      (fun q : ℝ × M => (TotalSpace.mk' E q.2 (X q.1 q.2) : TangentBundle I M))
      (s ×ˢ (chartAt H α).source) e.source := by
    intro q hq
    rw [Trivialization.mem_source]
    exact hbase hq.2
  have hiff := e.contMDiffOn_iff (n := ∞) (IM := 𝓘(ℝ, ℝ).prod I) (IB := I)
    (f := fun q : ℝ × M => (TotalSpace.mk' E q.2 (X q.1 q.2) : TangentBundle I M)) hmaps
  have hfib : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, E) ∞
      (fun q : ℝ × M => (e (TotalSpace.mk' E q.2 (X q.1 q.2))).2)
      (s ×ˢ (chartAt H α).source) := (hiff.mp (hX.mono ?_)).2
  · refine hfib.congr ?_
    intro q hq
    have hq2 : q.2 ∈ e.baseSet := hbase hq.2
    rw [he] at hq2 ⊢
    exact chartE_section_repr_eq_trivialization_snd (I := I) α (X q.1) hq2
  · exact Set.prod_mono (subset_refl _) (subset_univ _)

set_option linter.unusedSectionVars false in
/-- **Partition-of-unity assembly of joint tangent-bundle sections.** Let `ρ` be a smooth
partition of unity on `M` (indexed by `ι`) subordinate to a family of open sets `U`. For each
index `i` let `Y i : ℝ → ∀ x, TangentSpace I x` be a time-dependent section whose joint
tangent-bundle section is `ContMDiffOn` on `univ ×ˢ U i`. Then the patched global section

  `Xext q.1 q.2 := ∑ᶠ i, ρ i q.2 • Y i q.1 q.2`

has a globally `ContMDiff` joint tangent-bundle section on `ℝ × M`.

The proof is pointwise: at `q₀ = (t₀, x₀)`, `Bundle.contMDiffAt_section` reduces to the fibre
coordinate through the trivialization at `x₀`. That coordinate is a *fixed* continuous-linear
map of the fibre on the base set, so it distributes over the (locally finite) `finsum` and the
scalars (`map_finsum`, `map_smul`), giving `∑ᶠ i, ρ i q.2 • (fibre coord of Y i)`. Each summand
is `(ρ i ∘ snd)` (a smooth scalar) times the fibre coordinate of `Y i`'s joint section, which is
smooth at `q₀` whenever `x₀ ∈ tsupport (ρ i) ⊆ U i` (the subordinacy gives `q.2 ∈ U i`); off the
support the scalar vanishes. `contMDiffAt_finsum` over the locally-finite family closes it. -/
theorem partitionOfUnity_assembled_section_contMDiff
    {ι : Type*} {ρ : SmoothPartitionOfUnity ι I M (univ : Set M)} {U : ι → Set M}
    (hsub : ρ.IsSubordinate U) (hU : ∀ i, IsOpen (U i))
    (Y : ι → ℝ → ∀ x : M, TangentSpace I x)
    (hY : ∀ i, ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
      (fun q : ℝ × M => (TotalSpace.mk' E q.2 (Y i q.1 q.2) : TangentBundle I M))
      ((univ : Set ℝ) ×ˢ U i)) :
    ContMDiff (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
      (fun q : ℝ × M =>
        (TotalSpace.mk' E q.2 (∑ᶠ i, ρ i q.2 • Y i q.1 q.2) : TangentBundle I M)) := by
  classical
  intro q₀
  rw [Bundle.contMDiffAt_totalSpace]
  refine ⟨contMDiffAt_snd, ?_⟩
  set x₀ : M := q₀.2 with hx₀
  set e := trivializationAt E (TangentSpace I) x₀ with he
  -- The locally finite family of summand fibre-coordinates, read through `e`.
  set g : ι → ℝ × M → E :=
    fun i q => e.continuousLinearMapAt ℝ q.2 (Y i q.1 q.2) with hg
  -- Each summand `(ρ i ∘ snd) • g i` is `C∞` at `q₀`.
  have hsummand : ∀ i, q₀ ∈ tsupport (fun q : ℝ × M => ρ i q.2) →
      ContMDiffAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, E) ∞ (g i) q₀ := by
    intro i hi
    -- `q₀.2 ∈ tsupport (ρ i) ⊆ U i`, so `Y i`'s joint section is smooth near `q₀`.
    have hx₀_supp : x₀ ∈ tsupport (ρ i) := by
      have hclosed : IsClosed ((fun q : ℝ × M => q.2) ⁻¹' tsupport (ρ i)) :=
        (isClosed_tsupport (ρ i)).preimage continuous_snd
      have hsubset : tsupport (fun q : ℝ × M => ρ i q.2) ⊆
          (fun q : ℝ × M => q.2) ⁻¹' tsupport (ρ i) := by
        refine closure_minimal (fun q hq => ?_) hclosed
        simp only [Function.mem_support, Set.mem_preimage] at hq ⊢
        exact subset_tsupport _ hq
      exact hsubset hi
    have hx₀_U : x₀ ∈ U i := hsub i hx₀_supp
    have hbase : x₀ ∈ e.baseSet := by
      rw [he, TangentBundle.trivializationAt_baseSet]
      exact mem_chart_source H x₀
    -- The joint section of `Y i` is `ContMDiffAt q₀` (open `univ ×ˢ U i`).
    have hopen : IsOpen ((univ : Set ℝ) ×ˢ U i) := isOpen_univ.prod (hU i)
    have hmem : q₀ ∈ (univ : Set ℝ) ×ˢ U i := ⟨mem_univ _, hx₀_U⟩
    have hYat : ContMDiffAt (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
        (fun q : ℝ × M => (TotalSpace.mk' E q.2 (Y i q.1 q.2) : TangentBundle I M)) q₀ :=
      (hY i q₀ hmem).contMDiffAt (hopen.mem_nhds hmem)
    -- Read its fibre coordinate through `e`.
    have hYat' : ContMDiffAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, E) ∞
        (fun q : ℝ × M => (e (TotalSpace.mk' E q.2 (Y i q.1 q.2))).2) q₀ := by
      have hsrc : (TotalSpace.mk' E q₀.2 (Y i q₀.1 q₀.2) : TangentBundle I M) ∈ e.source := by
        rw [Trivialization.mem_source]; exact hbase
      exact ((e.contMDiffAt_iff (n := ∞) (IM := 𝓘(ℝ, ℝ).prod I) (IB := I)
        (f := fun q : ℝ × M => (TotalSpace.mk' E q.2 (Y i q.1 q.2) : TangentBundle I M))
        hsrc).mp hYat).2
    -- `(e ⟨q.2, Y i q.1 q.2⟩).2 = e.continuousLinearMapAt ℝ q.2 (Y i q.1 q.2)` near `q₀`.
    refine hYat'.congr_of_eventuallyEq ?_
    have hpre : (fun q : ℝ × M => q.2) ⁻¹' e.baseSet ∈ 𝓝 q₀ :=
      (continuous_snd.continuousAt) (e.open_baseSet.mem_nhds hbase)
    filter_upwards [hpre] with q hq
    show g i q = (e (TotalSpace.mk' E q.2 (Y i q.1 q.2))).2
    rw [← chartE_section_repr_eq_trivialization_snd (I := I) x₀ (Y i q.1) hq]
    rfl
  -- The fibre coordinate of the assembled section equals `∑ᶠ i, ρ i q.2 • g i q` near `q₀`.
  have hfib_eq : (fun q : ℝ × M =>
      (e (TotalSpace.mk' E q.2 (∑ᶠ i, ρ i q.2 • Y i q.1 q.2))).2)
      =ᶠ[𝓝 q₀] (fun q : ℝ × M => ∑ᶠ i, ρ i q.2 • g i q) := by
    have hbase : x₀ ∈ e.baseSet := by
      rw [he, TangentBundle.trivializationAt_baseSet]; exact mem_chart_source H x₀
    have hpre : (fun q : ℝ × M => q.2) ⁻¹' e.baseSet ∈ 𝓝 q₀ :=
      (continuous_snd.continuousAt) (e.open_baseSet.mem_nhds hbase)
    filter_upwards [hpre] with q hq
    have hfin : (Function.support (fun i => ρ i q.2 • Y i q.1 q.2)).Finite :=
      (ρ.locallyFinite.point_finite q.2).subset (fun i hi => by
        simp only [Function.mem_support] at hi ⊢
        exact fun h => hi (by rw [h, zero_smul]))
    show (e (TotalSpace.mk' E q.2 (∑ᶠ i, ρ i q.2 • Y i q.1 q.2))).2 = ∑ᶠ i, ρ i q.2 • g i q
    have hcl : (e (TotalSpace.mk' E q.2 (∑ᶠ i, ρ i q.2 • Y i q.1 q.2))).2
        = e.continuousLinearMapAt ℝ q.2 (∑ᶠ i, ρ i q.2 • Y i q.1 q.2) :=
      (chartE_section_repr_eq_trivialization_snd (I := I) x₀
        (fun y => ∑ᶠ i, ρ i q.2 • Y i q.1 y) hq).symm
    rw [hcl, map_finsum (g := e.continuousLinearMapAt ℝ q.2) hfin]
    refine finsum_congr fun i => ?_
    rw [map_smul]
  show ContMDiffAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, E) ∞
    (fun q : ℝ × M => (e (TotalSpace.mk' E q.2 (∑ᶠ i, ρ i q.2 • Y i q.1 q.2))).2) q₀
  refine ContMDiffAt.congr_of_eventuallyEq ?_ hfib_eq
  -- The family `fun i q => ρ i q.2 • g i q` is locally finite (pulled back from `ρ` by `snd`).
  have hlf : LocallyFinite (fun i => Function.support (fun q : ℝ × M => ρ i q.2 • g i q)) := by
    have hpre : LocallyFinite
        (fun i => (Prod.snd : ℝ × M → M) ⁻¹' Function.support (ρ i)) :=
      ρ.locallyFinite.preimage_continuous (g := (Prod.snd : ℝ × M → M)) continuous_snd
    refine hpre.subset (fun i q hq => ?_)
    simp only [Function.mem_support, Set.mem_preimage] at hq ⊢
    exact fun h => hq (by rw [h, zero_smul])
  refine contMDiffAt_finsum hlf ?_
  intro i
  by_cases hi : q₀ ∈ tsupport (fun q : ℝ × M => ρ i q.2)
  · refine ContMDiffAt.smul ?_ (hsummand i hi)
    exact ((ρ i).contMDiff.comp contMDiff_snd).contMDiffAt
  · exact contMDiffAt_of_notMem (compl_subset_compl.mpr
      (tsupport_smul_subset_left (fun q : ℝ × M => ρ i q.2) (g i)) hi) ∞

/-- **Smooth time-extension across the slab endpoints.** A field `X` whose joint tangent-bundle
section is `C∞` on the closed time slab `Icc 0 T ×ˢ univ` admits a field `Xext` whose joint
section is `C∞` on all of `ℝ × M` and which agrees with `X` on `Icc 0 T`.

The body is a deferred Seeley/Whitney smooth-extension construction (filled by a later worker);
this theorem therefore transitively depends on `sorryAx`. -/
theorem seeley_time_extend
    (X : ℝ → ∀ x : M, TangentSpace I x) (T : ℝ) (hT : 0 < T)
    (hsmooth0 : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
      (fun q : ℝ × M => (TotalSpace.mk' E q.2 (X q.1 q.2) : TangentBundle I M))
      (Set.Icc 0 T ×ˢ univ)) :
    ∃ Xext : ℝ → ∀ x : M, TangentSpace I x,
      ContMDiff (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
        (fun q : ℝ × M => (TotalSpace.mk' E q.2 (Xext q.1 q.2) : TangentBundle I M)) ∧
      (∀ t ∈ Set.Icc 0 T, ∀ x : M, Xext t x = X t x) := sorry

end DifferentialGeometry.PDE.RicciFlow.ODE
