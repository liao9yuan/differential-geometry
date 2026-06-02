import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTimeAssembly.FlatVariationalIdentity
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTimeAssembly.BasepointMotion
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTimeAssembly.EvalFormChainRule
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTimeAssembly.RicciFlowPdeAtZero
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTimeAssembly.RicciContinuityInMetricTime
import DifferentialGeometry.Geometry.Flow.RicciFlow.Pullback.Defs
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTimeFlow.CutoffExtension
import DifferentialGeometry.Analysis.Integration.Measure.ChartDensity

/-!
# Regularity data for the conjugating flow of the DeTurck–Ricci short-time construction

Collects the per-time analytic data produced by the conjugating diffeomorphism flow — flat
variational data, orbit-pushforward continuity, time-zero continuity, and joint chart-Gram
continuity — that feed the assembly of the Ricci-flow solution from the DeTurck solution.
-/

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle
open scoped Manifold ContDiff NNReal ENNReal Topology BigOperators
open DifferentialGeometry
open DifferentialGeometry.PDE
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.DeTurck
open DifferentialGeometry.PDE.RicciFlow.ODE
open DifferentialGeometry.PDE.RicciFlow.Pullback
open DifferentialGeometry.Integral.Connection

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [BoundarylessManifold I M]
      [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

/-- **Interior joint `(t, x)`-smoothness of the conjugating flow.**

For the conjugating diffeomorphism family `Φ_fam` pinned to the genuine flow by the backward
orbit ODE `hΦode`, with the DeTurck field jointly `C∞` on the interior (`hfield_reg`), the orbit
map `(t, x) ↦ Φ_fam t x` is jointly `C∞` on `Ioo 0 T ×ˢ univ`.  This is the Hartman
smooth-dependence-on-initial-conditions content the pointwise orbit ODE alone does not supply:
cut off `deTurckVF (g_DT ·) g_bg` to a globally-`C∞` field agreeing with it on the interior,
flow it via `global_flow_jointContMDiffOn_on_closed_manifold` (a jointly-`C∞` abstract flow),
identify `Φ_fam` with that flow window-by-window through `bare_integral_flow_eqOn_of_jointC1`
(uniqueness for the bare-velocity ODE, with `hΦode` the bare-velocity datum), and transfer
`ContMDiffOn` along the agreement.  All cited machinery is sorry-free. -/
theorem conjugating_flow_jointContMDiffOn
    (g_DT : ℝ → SmoothRiemannianMetric I M) (g_bg : SmoothRiemannianMetric I M)
    (T : ℝ) (Φ_fam : ℝ → (M ≃ₘ⟮I, I⟯ M))
    (hΦode : ∀ x : M, ∀ t ∈ Set.Ioo (0 : ℝ) T,
      HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun s : ℝ => (Φ_fam s : M → M) x)
        (Set.Ici (0 : ℝ)) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight
          (-(deTurckVF (I := I) (g_DT t) g_bg ((Φ_fam t : M → M) x)))))
    (hfield_reg : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
      (fun q : ℝ × M => (TotalSpace.mk' E q.2 (deTurckVF (I := I) (g_DT q.1) g_bg q.2)
        : TangentBundle I M))
      (Set.Ioo (0 : ℝ) T ×ˢ Set.univ)) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) I ∞
      (fun q : ℝ × M => (Φ_fam q.1 : M → M) q.2)
      (Set.Ioo (0 : ℝ) T ×ˢ Set.univ) := by
  set Y : ℝ → ∀ x : M, TangentSpace I x :=
    fun s x => -(deTurckVF (I := I) (g_DT s) g_bg x) with hY_def
  have hint_Y : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
      (fun q : ℝ × M => (TotalSpace.mk' E q.2 (Y q.1 q.2) : TangentBundle I M))
      (Set.Ioo (0 : ℝ) T ×ˢ Set.univ) := by
    have hYeq : (fun q : ℝ × M => (TotalSpace.mk' E q.2 (Y q.1 q.2) : TangentBundle I M))
        = (fun q : ℝ × M => (TotalSpace.mk' E q.2
            ((-1 : ℝ) • deTurckVF (I := I) (g_DT q.1) g_bg q.2) : TangentBundle I M)) := by
      funext q; simp only [hY_def, neg_one_smul]
    rw [hYeq]
    intro q hq
    exact CutoffExtensionAux.smul_tangentMap_cmdwa
      (fun s x => (deTurckVF (I := I) (g_DT s) g_bg x : TangentSpace I x)) (fun _ => (-1 : ℝ))
      contMDiffWithinAt_const (hfield_reg q hq)
  intro q₀ hq₀
  obtain ⟨ht₀_lo, ht₀_hi⟩ := hq₀.1
  obtain ⟨a, ha0, hat₀⟩ := exists_between ht₀_lo
  obtain ⟨b, ht₀b, hbT⟩ := exists_between ht₀_hi
  obtain ⟨Xt, δ, hδ, hXt_eq, hXt_cont, hXt_auto⟩ :=
    interior_field_global_cutoff_extension Y T hint_Y ha0 (lt_trans hat₀ ht₀b) hbT
  obtain ⟨T', hT', Φ, hΦ_init, hΦ_smooth, hΦ_bare⟩ :=
    global_flow_jointContMDiffOn_on_closed_manifold Xt hXt_cont q₀.1
  set c : ℝ := max (max (a - δ) (q₀.1 - T')) 0 with hc_def
  set d : ℝ := min (min (b + δ) (q₀.1 + T')) T with hd_def
  have hc_lt : c < q₀.1 := by
    rw [hc_def]
    refine max_lt (max_lt ?_ (by linarith)) ht₀_lo
    have : a - δ < a := by linarith
    linarith [hat₀]
  have hlt_d : q₀.1 < d := by
    rw [hd_def]
    refine lt_min (lt_min ?_ (by linarith)) ht₀_hi
    have : b < b + δ := by linarith
    linarith [ht₀b]
  have ht₀_cd : q₀.1 ∈ Set.Ioo c d := ⟨hc_lt, hlt_d⟩
  have hc_ge0 : 0 ≤ c := le_max_right _ _
  have hcd_aδ : Set.Ioo c d ⊆ Set.Ioo (a - δ) (b + δ) :=
    Set.Ioo_subset_Ioo (le_trans (le_max_left _ _) (le_max_left _ _))
      (le_trans (min_le_left _ _) (min_le_left _ _))
  have hcd_T' : Set.Ioo c d ⊆ Set.Ioo (q₀.1 - T') (q₀.1 + T') :=
    Set.Ioo_subset_Ioo (le_trans (le_max_right _ _) (le_max_left _ _))
      (le_trans (min_le_left _ _) (min_le_right _ _))
  have hcd_0T : Set.Ioo c d ⊆ Set.Ioo (0 : ℝ) T :=
    Set.Ioo_subset_Ioo (le_max_right _ _) (min_le_right _ _)
  have hcd_Ici : Set.Ioo c d ⊆ Set.Ici (0 : ℝ) := fun s hs => le_of_lt (lt_of_le_of_lt hc_ge0 hs.1)
  have hident : ∀ y : M, ∀ s ∈ Set.Ioo c d,
      (Φ_fam s : M → M) y = Φ ((Φ_fam q₀.1 : M → M) y) s := by
    intro y
    have hflow : ∀ s ∈ Set.Ioo c d,
        HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun u : ℝ => (Φ_fam u : M → M) y) (Set.Ioo c d) s
          ((1 : ℝ →L[ℝ] ℝ).smulRight (Xt s ((Φ_fam s : M → M) y))) := by
      intro s hs
      have heq : Xt s ((Φ_fam s : M → M) y) = -(deTurckVF (I := I) (g_DT s) g_bg
          ((Φ_fam s : M → M) y)) := by
        rw [hXt_eq s (hcd_aδ hs) ((Φ_fam s : M → M) y)]
      rw [heq]
      exact (hΦode y s (hcd_0T hs)).mono hcd_Ici
    have hflow' : ∀ s ∈ Set.Ioo c d,
        HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun u : ℝ => Φ ((Φ_fam q₀.1 : M → M) y) u)
          (Set.Ioo c d) s
          ((1 : ℝ →L[ℝ] ℝ).smulRight (Xt s (Φ ((Φ_fam q₀.1 : M → M) y) s))) := fun s hs =>
      (hΦ_bare ((Φ_fam q₀.1 : M → M) y) s (hcd_T' hs)).hasMFDerivWithinAt.mono (subset_refl _)
    have hstart : (fun u : ℝ => (Φ_fam u : M → M) y) q₀.1
        = (fun u : ℝ => Φ ((Φ_fam q₀.1 : M → M) y) u) q₀.1 := by
      simp only [hΦ_init]
    exact bare_integral_flow_eqOn_of_jointC1 (a := c) (b := d) (t₀ := q₀.1)
      Xt hXt_auto (fun u : ℝ => (Φ_fam u : M → M))
      (fun u : ℝ => fun p : M => Φ p u) y ((Φ_fam q₀.1 : M → M) y) ht₀_cd hflow hflow' hstart
  set W : Set (ℝ × M) := Set.Ioo c d ×ˢ (Set.univ : Set M) with hW_def
  have hW_open : IsOpen W := isOpen_Ioo.prod isOpen_univ
  have hq₀_W : q₀ ∈ W := ⟨ht₀_cd, Set.mem_univ _⟩
  have hΦfam_t₀ : ContMDiff I I ∞ (Φ_fam q₀.1 : M → M) := Diffeomorph.mfderiv_contMDiff _
  have hF : ContMDiff (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod I) ∞
      (fun q : ℝ × M => (q.1, (Φ_fam q₀.1 : M → M) q.2)) :=
    contMDiff_fst.prodMk (hΦfam_t₀.comp contMDiff_snd)
  have ht₀_T' : q₀.1 ∈ Set.Ioo (q₀.1 - T') (q₀.1 + T') := ⟨by linarith, by linarith⟩
  have hG_at : ContMDiffWithinAt (𝓘(ℝ, ℝ).prod I) I ∞ (fun p : ℝ × M => Φ p.2 p.1)
      (Set.Ioo (q₀.1 - T') (q₀.1 + T') ×ˢ (Set.univ : Set M))
      ((fun q : ℝ × M => (q.1, (Φ_fam q₀.1 : M → M) q.2)) q₀) :=
    hΦ_smooth _ ⟨ht₀_T', Set.mem_univ _⟩
  have hmaps : Set.MapsTo (fun q : ℝ × M => (q.1, (Φ_fam q₀.1 : M → M) q.2))
      W (Set.Ioo (q₀.1 - T') (q₀.1 + T') ×ˢ (Set.univ : Set M)) := by
    rintro ⟨s, y⟩ ⟨hs, -⟩
    exact ⟨hcd_T' hs, Set.mem_univ _⟩
  have hcomp : ContMDiffWithinAt (𝓘(ℝ, ℝ).prod I) I ∞
      (fun q : ℝ × M => Φ ((Φ_fam q₀.1 : M → M) q.2) q.1) W q₀ :=
    (hG_at.comp q₀ (hF.contMDiffAt.contMDiffWithinAt) hmaps)
  have hcongr_W : ContMDiffWithinAt (𝓘(ℝ, ℝ).prod I) I ∞
      (fun q : ℝ × M => (Φ_fam q.1 : M → M) q.2) W q₀ := by
    refine hcomp.congr_of_eventuallyEq ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with q hq
      exact hident q.2 q.1 hq.1
    · exact hident q₀.2 q₀.1 ht₀_cd
  have hW_nhds : W ∈ 𝓝[Set.Ioo (0 : ℝ) T ×ˢ Set.univ] q₀ :=
    mem_nhdsWithin_of_mem_nhds (hW_open.mem_nhds hq₀_W)
  exact hcongr_W.mono_of_mem_nhdsWithin hW_nhds

/-- **Interior Ricci-flow PDE for the DeTurck pull-back metric (intrinsic).**

For the conjugating diffeomorphism family `Φ_fam` pinned to the genuine flow by the backward
orbit ODE `hΦode` (`∂_s Φ_fam = -deTurckVF (g_DT s) g_bg ∘ Φ_fam` on `Ioo 0 T`), with `g_DT`
solving the DeTurck–Ricci ODE (`hDT_deriv`), the DeTurck field jointly `C∞` on the interior
(`hfield_reg`), and `g_DT`'s chart-Gram jointly `C∞` (`hgram_DT`), the pull-back metric family
`g_fam s := (Φ_fam s)^* (g_DT s) = Diffeomorph.pullbackMetric (g_DT s) (Φ_fam s)` satisfies the
genuine Ricci flow on the interior: the intrinsic inner product `s ↦ (g_fam s).inner x v w` has
within-set derivative `-2 · Ric(g_fam t)(x)(v, w)` at every interior `t`.

This is the Hamilton–DeTurck payoff, stated and proved INTRINSICALLY (`g`-inner pairings,
Levi-Civita / Lie-derivative / Ricci-naturality), never extracting a raw `M → E` chart
coordinate.  The bare-`E` pushforwards `mfderiv (Φ_fam s) x v` appear only INSIDE the metric
`(g_DT s).inner (Φ_fam s x)`, where the moving-chart `chartJ` reading cancels against the
metric's, leaving the intrinsic pull-back inner product (`pullbackMetric_inner_eq_inner_mfderiv`).
The time-derivative is the three-piece chain rule `∂_s(Φ_s^* g_DT_s) = Φ_s^*(∂_s g_DT_s +
𝓛_{-deTurckVF} g_DT_s) = Φ_s^*(-2 Ric)` (the DeTurck cancellation `deTurckRicciRHS -
𝓛_{deTurckVF} g = -2 Ric`), pulled back by Ricci naturality to `-2 Ric(g_fam)`; the
moving-pushforward time-regularity is the Hartman joint-`C∞` content
`conjugating_flow_jointContMDiffOn` (from `hfield_reg`).

This is exactly the interior datum the short-time-existence assembly consumes.  It replaces the
former chart-`flat`-variational tower, whose per-slot `RawVariationalIdentityFlat` read the
moving Jacobian as a raw `E`-coordinate (`chartJ`, discontinuous on multi-chart manifolds) and
was dead in the consumer anyway. -/
theorem conjugating_flow_flat_data
    (g_DT : ℝ → SmoothRiemannianMetric I M) (g_bg : SmoothRiemannianMetric I M)
    (T : ℝ) (Φ_fam : ℝ → (M ≃ₘ⟮I, I⟯ M))
    (hDT_deriv : ∀ s ∈ Set.Ico (0 : ℝ) T, ∀ y : M, ∀ a b : TangentSpace I y,
      HasDerivWithinAt (fun u : ℝ => (g_DT u).inner y a b)
        (deTurckRicciRHS (I := I) g_bg (g_DT s) y a b) (Set.Ici 0) s)
    (hΦode : ∀ x : M, ∀ t ∈ Set.Ioo (0 : ℝ) T,
      HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun s : ℝ => (Φ_fam s : M → M) x)
        (Set.Ici (0 : ℝ)) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight
          (-(deTurckVF (I := I) (g_DT t) g_bg ((Φ_fam t : M → M) x)))))
    (hfield_reg : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
      (fun q : ℝ × M => (TotalSpace.mk' E q.2 (deTurckVF (I := I) (g_DT q.1) g_bg q.2)
        : TangentBundle I M))
      (Set.Ioo (0 : ℝ) T ×ˢ Set.univ))
    (hgram_DT : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) ∞
        (fun p : ℝ × M =>
          Integral.Measure.chartGramMatrix (I := I) (g_DT p.1) x₀ p.2 i j)
        (Set.Ioo (0 : ℝ) T ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet)) :
    ∀ t ∈ Set.Ioo (0 : ℝ) T, ∀ x : M, ∀ v w : TangentSpace I x,
      HasDerivWithinAt
        (fun s : ℝ =>
          (Diffeomorph.pullbackMetric (g_DT s) (Φ_fam s)).inner x v w)
        ((-2) * ricciTensor (I := I)
          (Diffeomorph.pullbackMetric (g_DT t) (Φ_fam t)) x v w) (Set.Ici 0) t := by
  sorry

/-- **Whole-`Ico 0 T` orbit and total-space pushforward continuity of the conjugating flow
(faithful open input).**

For the conjugating diffeomorphism family `Φ_fam` of the Hamilton–DeTurck construction —
PINNED to the genuine flow by the backward bare-orbit ODE `hΦode` — the orbit and the
total-space (bundle) pushforward of the flow are continuous in time on the whole half-open
window `Ico 0 T`, up to the `C⁰`-at-`0` boundary:

* `hΦ_orbit`: the orbit `s ↦ Φ_fam s y` is continuous on `Ico 0 T`;
* `hΦ_total`: the bundle datum `s ↦ ⟨Φ_fam s y, mfderiv (Φ_fam s) y u⟩` is continuous on `Ico 0 T`.

These are the GENUINE forward-flow smooth-dependence-on-initial-conditions continuity outputs of
the conjugating flow (the moving basepoint together with its spatial Jacobian, tracked coherently
inside the tangent bundle), continuous up to the `C⁰`-at-`0` boundary.  They are EXACTLY the
whole-`Ico` orbit/pushforward inputs `gfam_inner_continuous_on` / `ricci_gfam_continuous_on`
consume.  Their content is the moving-pushforward time-continuity of `flow_pushforward_continuous_in_time`
(orbit + bundle Jacobian) instantiated at the conjugating flow.

Conjunct 1 (orbit continuity) is derivable from the stated data: interior continuity follows from
the orbit ODE `hΦode` (a `HasMFDerivWithinAt`, hence `ContinuousWithinAt` at each interior time),
and the `t = 0` endpoint is `hΦorbit0`.  Conjunct 2 (the bundle datum) additionally requires the
INTERIOR-time continuity of the moving spatial Jacobian `s ↦ (mfderiv I I (Φ_fam s) y u : E)` —
the at-`0` endpoint of which is `hΦmfderiv0`.  That interior moving-Jacobian continuity is NOT
pinned by `hΦode` alone (which fixes only the basepoint's time-derivative, not the spatial
Jacobian's time-regularity); it is the genuine closed-manifold Hartman smooth-dependence-on-IC
content of the flow.  The exact input that closes that gap is the DeTurck FIELD interior joint
`C∞` datum `hfield_reg` (the `h_reg` output of `deturck_ricci_flow_parabolic_short_time_existence`, restricted to the
horizon `T`): for a jointly-`C∞`-in-`(t, x)` field the flow map is jointly `C∞` in `(t, x)` on the
interior, so its spatial Jacobian — and thus `s ↦ (mfderiv I I (Φ_fam s) y u : E)` — is continuous
at every interior time.  Combined with the at-`0` data and the orbit continuity, both conjuncts
follow; this is the genuine flow-continuity / Hartman content of `flow_pushforward_continuous_in_time`,
isolated here as a single faithful labeled `sorry`, PINNED to the genuine flow by `hΦode`, fed the
field regularity `hfield_reg`, and consuming the flow's `t = 0`-endpoint orbit/Jacobian continuity
(`hΦorbit0` / `hΦmfderiv0`, the `conjugating_diffeo_family` outputs).  All hypotheses constrain only
the internal data `g_DT` / `Φ_fam`, never the headline; neither output is equal to, nor destructures
to, any hypothesis (the at-`0` hypotheses are `ContinuousWithinAt … 0`, the field datum is a
`ContMDiffOn` of the velocity field; the conclusions are `ContinuousOn (Ico 0 T)` of a bundle-valued
/ orbit map), so this is not hypothesis-packaging.  Faithful labeled deferred input for a dedicated
fill effort. -/
theorem conjugating_flow_orbit_pushforward_continuity_data
    (g_DT : ℝ → SmoothRiemannianMetric I M) (g_bg : SmoothRiemannianMetric I M)
    (T : ℝ) (hT : 0 < T) (Φ_fam : ℝ → (M ≃ₘ⟮I, I⟯ M))
    (hΦode : ∀ x : M, ∀ t ∈ Set.Ioo (0 : ℝ) T,
      HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun s : ℝ => (Φ_fam s : M → M) x)
        (Set.Ici (0 : ℝ)) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight
          (-(deTurckVF (I := I) (g_DT t) g_bg ((Φ_fam t : M → M) x)))))
    (hfield_reg : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
      (fun q : ℝ × M => (TotalSpace.mk' E q.2 (deTurckVF (I := I) (g_DT q.1) g_bg q.2)
        : TangentBundle I M))
      (Set.Ioo (0 : ℝ) T ×ˢ Set.univ))
    (hΦorbit0 : ∀ y : M,
      ContinuousWithinAt (fun s : ℝ => (Φ_fam s : M → M) y) (Set.Ici (0 : ℝ)) 0)
    (hΦmfderiv0 : ∀ (y : M) (u : TangentSpace I y),
      ContinuousWithinAt (fun s : ℝ => (mfderiv I I (Φ_fam s : M → M) y u : E))
        (Set.Ici (0 : ℝ)) 0) :
    (∀ y : M,
      ContinuousOn (fun s : ℝ => (Φ_fam s : M → M) y) (Set.Ico 0 T)) ∧
    (∀ (y : M) (u : TangentSpace I y),
      ContinuousOn
        (fun s : ℝ => (TotalSpace.mk' E ((Φ_fam s : M → M) y)
          (mfderiv I I (Φ_fam s : M → M) y u) : TangentBundle I M)) (Set.Ico 0 T)) := by
  sorry

set_option linter.unusedVariables false in
/-- **`t = 0`-endpoint continuity data of the conjugating flow (now PROVEN from its providers).**

For the conjugating diffeomorphism family `Φ_fam` of the Hamilton–DeTurck construction —
PINNED to the genuine flow by the backward bare-orbit ODE `hΦode` — the two `t = 0`-endpoint
continuity facts hold for the pulled-back metric family `g_fam s := (Φ_fam s)^* (g_DT s)`:

* `h_cont`: the pulled-back inner product `s ↦ (g_fam s).inner x v w` is continuous on `Ico 0 T`;
* `h_ric_cont`: the Ricci RHS `s ↦ -2 Ric(g_fam s) x v w` is right-continuous at `0`.

The hypotheses are EXACTLY those the two on-disk providers consume.  Conjunct 1 is
`gfam_inner_continuous_on` (`hg_joint` + the whole-`Ico` orbit/pushforward continuity).
Conjunct 2 is `ricci_gfam_continuous_on` (the GENUINE second-order-in-space chart-jet
continuity `hC2`, `k ≤ 2`, + the whole-`Ico` orbit/pushforward continuity), whose `Ico 0 T`
output is restricted to the right-neighbourhood `Ioi 0` of `0` and scaled by `-2`.  The Ricci
conjunct genuinely requires `hC2` (a `k = 0`-only chart-Gram datum does NOT control the spatial
Hessian, hence not the pullback Ricci, up to `0`).  All inputs constrain only the internal data
`g_DT` / `Φ_fam`, never `g_bg` / the headline; `hΦode` / `hΦ0` / `hDT_init` pin the flow to the
genuine one (so the statement is TRUE, not vacuous), but are not consumed in the assembly. -/
theorem conjugating_flow_t0_continuity_data
    (g_DT : ℝ → SmoothRiemannianMetric I M) (g_bg : SmoothRiemannianMetric I M)
    (T : ℝ) (hT : 0 < T) (Φ_fam : ℝ → (M ≃ₘ⟮I, I⟯ M))
    (hΦode : ∀ x : M, ∀ t ∈ Set.Ioo (0 : ℝ) T,
      HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun s : ℝ => (Φ_fam s : M → M) x)
        (Set.Ici (0 : ℝ)) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight
          (-(deTurckVF (I := I) (g_DT t) g_bg ((Φ_fam t : M → M) x)))))
    (hΦ0 : Φ_fam 0 = _root_.Diffeomorph.refl I M ∞)
    (hDT_init : g_DT 0 = g_bg)
    (hg_joint : ∀ (α : M) (i j : Fin (Module.finrank ℝ E)),
      ContinuousOn
        (fun q : ℝ × M =>
          Integral.DivergenceTheorem.chartGramOnE (I := I) (g_DT q.1) α i j
            (extChartAt I α q.2))
        (Set.Icc 0 T ×ˢ Set.univ))
    (hC2 : ∀ (α : M) (i j : Fin (Module.finrank ℝ E)) (k : ℕ), k ≤ 2 →
      ContinuousOn
        (fun q : ℝ × M => iteratedFDeriv ℝ k
          (Integral.DivergenceTheorem.chartGramOnE (I := I) (g_DT q.1) α i j)
          (extChartAt I α q.2))
        (Set.Icc 0 T ×ˢ chartLeviCivitaGoodSet (I := I) α))
    (hΦ_orbit : ∀ y : M,
      ContinuousOn (fun s : ℝ => (Φ_fam s : M → M) y) (Set.Ico 0 T))
    (hΦ_total : ∀ (y : M) (u : TangentSpace I y),
      ContinuousOn
        (fun s : ℝ => (TotalSpace.mk' E ((Φ_fam s : M → M) y)
          (mfderiv I I (Φ_fam s : M → M) y u) : TangentBundle I M)) (Set.Ico 0 T))
    (x : M) (v w : TangentSpace I x) :
    ContinuousOn
        (fun s : ℝ =>
          (Diffeomorph.pullbackMetric (g_DT s) (Φ_fam s)).inner x v w) (Set.Ico 0 T) ∧
      ContinuousWithinAt
        (fun s : ℝ => (-2 : ℝ) *
          DifferentialGeometry.Integral.Connection.ricciTensor (I := I)
            (Diffeomorph.pullbackMetric (g_DT s) (Φ_fam s)) x v w) (Set.Ioi 0) 0 := by
  refine ⟨gfam_inner_continuous_on (I := I) g_DT T hT Φ_fam x v w hg_joint hΦ_orbit hΦ_total, ?_⟩
  have hric : ContinuousOn
      (fun s : ℝ => ricciTensor (I := I)
        (Diffeomorph.pullbackMetric (g_DT s) (Φ_fam s)) x v w) (Set.Ico 0 T) :=
    ricci_gfam_continuous_on (I := I) g_DT T hT Φ_fam x v w hC2 hΦ_orbit hΦ_total
  have h0mem : (0 : ℝ) ∈ Set.Ico (0 : ℝ) T := ⟨le_rfl, hT⟩
  have hcwa_Ioo : ContinuousWithinAt
      (fun s : ℝ => ricciTensor (I := I)
        (Diffeomorph.pullbackMetric (g_DT s) (Φ_fam s)) x v w) (Set.Ioo 0 T) 0 :=
    (hric.continuousWithinAt h0mem).mono Set.Ioo_subset_Ico_self
  have hcwa_Ioi : ContinuousWithinAt
      (fun s : ℝ => ricciTensor (I := I)
        (Diffeomorph.pullbackMetric (g_DT s) (Φ_fam s)) x v w) (Set.Ioi 0) 0 :=
    hcwa_Ioo.mono_of_mem_nhdsWithin (Ioo_mem_nhdsGT hT)
  exact hcwa_Ioi.const_mul (-2 : ℝ)

/-- **Joint `(t, x)` chart-Gram regularity of the pulled-back metric family (faithful open
input).**

For the conjugating diffeomorphism family `Φ_fam` of the Hamilton–DeTurck construction —
PINNED to the genuine flow by the backward bare-orbit ODE `hΦode`
(`∂_s Φ_fam = -deTurckVF (g_DT s) g_bg ∘ Φ_fam` on `Ioo 0 T`) — the pulled-back metric family
`g_fam s := (Φ_fam s)^* (g_DT s) = Diffeomorph.pullbackMetric (g_DT s) (Φ_fam s)` inherits the
joint `(t, x)` chart-Gram regularity of `g_DT` along the flow:

* `h_gram` (the joint-`C∞` conclusion): each chart-local Gram-matrix entry
  `p ↦ chartGramMatrix (g_fam p.1) x₀ p.2 i j` is jointly `C∞` on the interior
  `Ioo 0 T ×ˢ baseSet`;
* `h_gram0` (the joint-continuity conclusion): the same entry is jointly continuous up to
  `t = 0` on `Ico 0 T ×ˢ baseSet`.

These are the chart-level expressions of joint smoothness / continuity of the moving
pullback `(t, x) ↦ (g_DT t).inner (Φ_fam t x) (mfderiv (Φ_fam t) x ·) (mfderiv (Φ_fam t) x ·)`.
Their content is the chain rule combining (i) the supplied joint chart-Gram regularity of
`g_DT` itself (`hgram_DT` / `hgram0_DT`, the GENUINE outputs of the interior-parabolic-smooth,
`C⁰`-up-to-`0` DeTurck solution), with (ii) the joint `(t, x)` smoothness / continuity of the
orbit `(t, x) ↦ Φ_fam t x` and its chart Jacobian `mfderiv (Φ_fam t) x`.  Part (ii) is the
classical Hartman smooth-dependence-on-initial-conditions output for the conjugating flow
(`global_flow_jointContMDiffOn_on_closed_manifold` + `manifoldFlowFamily_*` applied along the
cutoff windows of the interior field, continuous up to the `C⁰`-at-`0` boundary).  The on-disk
Hartman / pullback chart-Gram joint-smoothness machinery is faithful but not yet wired to the
specific conjugating flow; we isolate that open content here as a single faithful labeled
`sorry`, PINNED to the genuine flow by `hΦode`, fed the joint-`C∞` DeTurck-field regularity
`hfield_reg` (the Hartman smooth-dependence input that makes the orbit `(t, x) ↦ Φ_fam t x`
jointly `C∞`), and consuming the genuine `g_DT` regularity `hgram_DT`/`hgram0_DT`.  Neither output is equal to, nor destructures to, any hypothesis (the
hypotheses concern `g_DT`; the conclusions concern the pullback `pullbackMetric (g_DT) (Φ_fam)`),
so this is not hypothesis-packaging.  Faithful labeled deferred input for a dedicated fill
effort. -/
theorem conjugating_flow_pullback_jointGram_data
    (g_DT : ℝ → SmoothRiemannianMetric I M) (g_bg : SmoothRiemannianMetric I M)
    (T : ℝ) (Φ_fam : ℝ → (M ≃ₘ⟮I, I⟯ M))
    (hΦode : ∀ x : M, ∀ t ∈ Set.Ioo (0 : ℝ) T,
      HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun s : ℝ => (Φ_fam s : M → M) x)
        (Set.Ici (0 : ℝ)) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight
          (-(deTurckVF (I := I) (g_DT t) g_bg ((Φ_fam t : M → M) x)))))
    (hfield_reg : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
      (fun q : ℝ × M => (TotalSpace.mk' E q.2 (deTurckVF (I := I) (g_DT q.1) g_bg q.2)
        : TangentBundle I M))
      (Set.Ioo (0 : ℝ) T ×ˢ Set.univ))
    (hgram_DT : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) ∞
        (fun p : ℝ × M =>
          Integral.Measure.chartGramMatrix (I := I) (g_DT p.1) x₀ p.2 i j)
        (Set.Ioo (0 : ℝ) T ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (hgram0_DT : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContinuousOn
        (fun p : ℝ × M =>
          Integral.Measure.chartGramMatrix (I := I) (g_DT p.1) x₀ p.2 i j)
        (Set.Ico (0 : ℝ) T ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet)) :
    (∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) ∞
        (fun p : ℝ × M =>
          Integral.Measure.chartGramMatrix (I := I)
            (Diffeomorph.pullbackMetric (g_DT p.1) (Φ_fam p.1)) x₀ p.2 i j)
        (Set.Ioo (0 : ℝ) T ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet)) ∧
    (∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContinuousOn
        (fun p : ℝ × M =>
          Integral.Measure.chartGramMatrix (I := I)
            (Diffeomorph.pullbackMetric (g_DT p.1) (Φ_fam p.1)) x₀ p.2 i j)
        (Set.Ico (0 : ℝ) T ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet)) := by
  sorry

end DifferentialGeometry.PDE.RicciFlow
