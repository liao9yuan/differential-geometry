import DifferentialGeometry.PDE.RicciFlow.ODE.TimeDependentFlow.ManifoldIntegralFlow
import DifferentialGeometry.PDE.RicciFlow.ODE.TimeDependentFlow.BareFlowFromJointC1
import DifferentialGeometry.PDE.RicciFlow.ODE.TimeDependentFlow.ManifoldFlowFamily
import DifferentialGeometry.PDE.RicciFlow.ODE.TimeDependentFlow.SmoothInSpace.BanachIC
import DifferentialGeometry.Analysis.ODE.FlowC1
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-!
## H3 — manifold-global joint smooth dependence (headline + pending children)

This file carries the manifold-level smooth-dependence theorems of the smooth-dependence
program: the H3 headline together with its pending proof-target children.
-/

noncomputable section
open Set Function Filter Metric Bundle
open scoped Topology NNReal ContDiff Manifold
open DifferentialGeometry.Analysis.ODE.Flow

namespace DifferentialGeometry.PDE.RicciFlow.ODE

section Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M] [T2Space M]


-- [H3: chartcoord-jointContDiffOn-pushforward-to-contMDiffOn]
theorem h3_manifoldFlow_contMDiffOn_of_jointContDiffOn
    (p₀ : M) (Φ_E : E × ℝ → E) {ρ T t₀ : ℝ}
    (U : Set M) (_hUopen : IsOpen U) (hUsub : U ⊆ (chartAt H p₀).source)
    (hUball : ∀ p ∈ U, I ((chartAt H p₀) p) ∈ Metric.ball (I ((chartAt H p₀) p₀)) ρ)
    (hΦE_smooth : ContDiffOn ℝ ∞ Φ_E
      (Metric.ball (I ((chartAt H p₀) p₀)) ρ ×ˢ Set.Ioo (t₀ - T) (t₀ + T)))
    (htgt : ∀ p ∈ U, ∀ s ∈ Set.Ioo (t₀ - T) (t₀ + T),
      Φ_E (I ((chartAt H p₀) p), s) ∈ (extChartAt I p₀).target) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) I ∞
      (fun q : ℝ × M => (extChartAt I p₀).symm (Φ_E (I ((chartAt H p₀) q.2), q.1)))
      (Set.Ioo (t₀ - T) (t₀ + T) ×ˢ U) := by
  set s : Set (ℝ × M) := Set.Ioo (t₀ - T) (t₀ + T) ×ˢ U with hs
  -- Step 1a: the chart coordinate of the second component is `C^∞` on `s`.
  have hcoord : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, E) ∞
      (fun q : ℝ × M => I ((chartAt H p₀) q.2)) s := by
    have hext : ContMDiffOn I 𝓘(ℝ, E) ∞ (extChartAt I p₀) (chartAt H p₀).source :=
      contMDiffOn_extChartAt
    have hcomp : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, E) ∞
        ((extChartAt I p₀) ∘ Prod.snd) s :=
      hext.comp contMDiffOn_snd (fun q hq => hUsub hq.2)
    -- `(extChartAt I p₀) ∘ Prod.snd = fun q => I ((chartAt H p₀) q.2)`.
    refine hcomp.congr ?_
    intro q _
    simp only [Function.comp_apply, extChartAt_coe, Function.comp_apply]
  -- Step 1b: assemble `h q = (I ((chartAt H p₀) q.2), q.1)` into the Euclidean model `E × ℝ`.
  have hh : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, E × ℝ) ∞
      (fun q : ℝ × M => (I ((chartAt H p₀) q.2), q.1)) s :=
    hcoord.prodMk_space contMDiffOn_fst
  -- Step 2: the hypothesis `hΦE_smooth` as a manifold-smoothness statement between model spaces.
  have hΦ : ContMDiffOn 𝓘(ℝ, E × ℝ) 𝓘(ℝ, E) ∞ Φ_E
      (Metric.ball (I ((chartAt H p₀) p₀)) ρ ×ˢ Set.Ioo (t₀ - T) (t₀ + T)) :=
    hΦE_smooth.contMDiffOn
  -- Step 3: compose `Φ_E` with `h`; the domain landing is from `hUball` and `q.1 ∈ Ioo`.
  have hΦh : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, E) ∞
      (fun q : ℝ × M => Φ_E (I ((chartAt H p₀) q.2), q.1)) s := by
    have hsub : s ⊆ (fun q : ℝ × M => (I ((chartAt H p₀) q.2), q.1)) ⁻¹'
        (Metric.ball (I ((chartAt H p₀) p₀)) ρ ×ˢ Set.Ioo (t₀ - T) (t₀ + T)) := by
      intro q hq
      rw [hs] at hq
      exact Set.mk_mem_prod (hUball q.2 hq.2) hq.1
    exact hΦ.comp hh hsub
  -- Step 4: post-compose with `(extChartAt I p₀).symm`; the landing is exactly `htgt`.
  have hsymm : ContMDiffOn 𝓘(ℝ, E) I ∞ (extChartAt I p₀).symm (extChartAt I p₀).target :=
    contMDiffOn_extChartAt_symm p₀
  have hsubtgt : s ⊆ (fun q : ℝ × M => Φ_E (I ((chartAt H p₀) q.2), q.1)) ⁻¹'
      (extChartAt I p₀).target := by
    intro q hq
    rw [hs] at hq
    exact htgt q.2 hq.2 q.1 hq.1
  exact hsymm.comp hΦh hsubtgt

-- C1 [H3 v3: chart-p₀ PUSHFORWARD field = X-section read in the FIXED trivialization at p₀, jointly C∞.
--  No moving chart: source=target=p₀, so this is literally the fixed-triv fiber component of the C∞ X-section.]
-- (`hρ : 0 < ρ` is a legitimate positivity hypothesis of the public signature; the B-route section
--  criterion proof does not happen to consume it, so the unused-variable linter is locally silenced
--  without altering the signature.)
set_option linter.unusedVariables false in
theorem chart_pushforward_field_jointContDiff
    (X : ℝ → ∀ x : M, TangentSpace I x)
    (hX : ContMDiff (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
      (fun q : ℝ × M => (TotalSpace.mk' E q.2 (X q.1 q.2) : TangentBundle I M)))
    (p₀ : M) {ρ : ℝ} (hρ : 0 < ρ)
    (hρ_sub : Metric.ball (extChartAt I p₀ p₀) ρ ⊆ (extChartAt I p₀).target) :
    ContDiffOn ℝ ∞
      (Function.uncurry (fun (s : ℝ) (c : E) =>
        ((trivializationAt E (TangentSpace I) p₀)
          (TotalSpace.mk' E ((extChartAt I p₀).symm c) (X s ((extChartAt I p₀).symm c)))).2))
      ((Set.univ : Set ℝ) ×ˢ Metric.ball (extChartAt I p₀ p₀) ρ) := by
  -- Abbreviations.
  set x₀ : E := extChartAt I p₀ p₀ with hx₀
  set e := trivializationAt E (TangentSpace I) p₀ with he
  set f : ℝ × M → TangentBundle I M :=
    fun q => (TotalSpace.mk' E q.2 (X q.1 q.2) : TangentBundle I M) with hf
  -- The base set on the manifold side: the chart-symm image of the Euclidean ball.
  set S : Set (ℝ × M) :=
    (Set.univ : Set ℝ) ×ˢ ((extChartAt I p₀).symm '' Metric.ball x₀ ρ) with hS
  -- (c1-fibre-input) restrict the globally-`ContMDiff` autonomised section `hX` to `S`.
  have hX_on : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞ f S := hX.contMDiffOn
  -- The `MapsTo` premise of the section criterion: every base point lies in the chart source,
  -- which is exactly `e.baseSet`/`e.source` (via hρ_sub + map_target of the extended chart).
  have hmaps : Set.MapsTo f S e.source := by
    rintro ⟨s, p⟩ hq
    obtain ⟨-, c, hc, rfl⟩ := hq
    have hcsrc : (extChartAt I p₀).symm c ∈ (chartAt H p₀).source := by
      have hmem : (extChartAt I p₀).symm c ∈ (extChartAt I p₀).source :=
        (extChartAt I p₀).map_target (hρ_sub hc)
      rwa [extChartAt_source] at hmem
    -- `f q ∈ e.source ⟺ (f q).proj ∈ (chartAt H p₀).source` by `trivializationAt_source`.
    rw [he, TangentBundle.trivializationAt_source]
    exact hcsrc
  -- (c1-section-reading-iff) `Bundle.Trivialization.contMDiffOn_iff` at the FIXED trivialization
  -- `e`, source manifold `ℝ × M`, model `𝓘(ℝ,ℝ).prod I`.  The `.mp.2` conjunct is the p₀-frame
  -- fibre reading, jointly `ContMDiffOn` into `𝓘(ℝ,E)` on `S`.
  have hreading : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, E) ∞
      (fun q : ℝ × M => (e (f q)).2) S :=
    ((e.contMDiffOn_iff hmaps).mp hX_on).2
  -- (c1-assemble) reindex the SOURCE from `ℝ × M` to `ℝ × E` by precomposing
  -- `Prod.map id (extChartAt I p₀).symm`, which is `ContMDiffOn` on `univ ×ˢ ball x₀ ρ`.
  have hsymm : ContMDiffOn 𝓘(ℝ, E) I ∞ (extChartAt I p₀).symm (Metric.ball x₀ ρ) :=
    (contMDiffOn_extChartAt_symm p₀).mono hρ_sub
  have hreindex :
      ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) (𝓘(ℝ, ℝ).prod I) ∞
        (Prod.map (id : ℝ → ℝ) (extChartAt I p₀).symm)
        ((Set.univ : Set ℝ) ×ˢ Metric.ball x₀ ρ) :=
    (contMDiffOn_id (I := 𝓘(ℝ, ℝ))).prodMap hsymm
  -- `Prod.map id symm` maps `univ ×ˢ ball x₀ ρ` into `S = univ ×ˢ (symm '' ball x₀ ρ)`.
  have hsub :
      ((Set.univ : Set ℝ) ×ˢ Metric.ball x₀ ρ) ⊆
        Prod.map (id : ℝ → ℝ) (extChartAt I p₀).symm ⁻¹' S := by
    rintro ⟨s, c⟩ ⟨-, hc⟩
    exact ⟨Set.mem_univ _, Set.mem_image_of_mem _ hc⟩
  -- Compose: the reading, read through the reindex, over `univ ×ˢ ball x₀ ρ`.
  have hcomp :
      ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞
        ((fun q : ℝ × M => (e (f q)).2) ∘ Prod.map (id : ℝ → ℝ) (extChartAt I p₀).symm)
        ((Set.univ : Set ℝ) ×ˢ Metric.ball x₀ ρ) :=
    hreading.comp hreindex hsub
  -- The composed function IS the target uncurried field (definitional), expressed via `e`.
  have hfun :
      ((fun q : ℝ × M => (e (f q)).2) ∘ Prod.map (id : ℝ → ℝ) (extChartAt I p₀).symm)
        = Function.uncurry (fun (s : ℝ) (c : E) =>
            (e (TotalSpace.mk' E ((extChartAt I p₀).symm c)
                (X s ((extChartAt I p₀).symm c)))).2) := by
    funext q
    rfl
  rw [hfun] at hcomp
  -- Transfer manifold `ContMDiffOn` → Euclidean `ContDiffOn`.  The target `ContDiffOn` is the
  -- Euclidean source-model image of a `ContMDiffOn` over `𝓘(ℝ, ℝ × E)`; reconcile the product
  -- model and the charted-space instance on the source `ℝ × E` so it matches `hcomp`'s `.prod`
  -- forms, then close.
  rw [← contMDiffOn_iff_contDiffOn, modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
  exact hcomp

-- C2 [H3 v3: cutoff globalization — multiply C1's field by a ContDiffBump supported in the chart target
--  to obtain a GLOBALLY-C∞ field on all of ℝ × E (the input exists_isLocalFlow_contDiffOn_top requires).]
theorem chart_pushforward_field_cutoff_globalContDiff [I.Boundaryless]
    (X : ℝ → ∀ x : M, TangentSpace I x)
    (hX : ContMDiff (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
      (fun q : ℝ × M => (TotalSpace.mk' E q.2 (X q.1 q.2) : TangentBundle I M)))
    (p₀ : M) {ρ : ℝ} (hρ : 0 < ρ)
    (hρ_sub : Metric.ball (extChartAt I p₀ p₀) ρ ⊆ (extChartAt I p₀).target) :
    ∃ (G : ℝ → E → E) (ρ' : ℝ), 0 < ρ' ∧ ρ' ≤ ρ ∧
      ContDiff ℝ ∞ (Function.uncurry G) ∧
      ∀ (s : ℝ), ∀ c ∈ Metric.ball (extChartAt I p₀ p₀) ρ',
        G s c = ((trivializationAt E (TangentSpace I) p₀)
          (TotalSpace.mk' E ((extChartAt I p₀).symm c) (X s ((extChartAt I p₀).symm c)))).2 := by
  -- Abbreviations: the chart centre `x₀` and the genuine trivialization-reading field `F`.
  set x₀ : E := extChartAt I p₀ p₀ with hx₀
  set F : ℝ → E → E := fun (s : ℝ) (c : E) =>
    ((trivializationAt E (TangentSpace I) p₀)
      (TotalSpace.mk' E ((extChartAt I p₀).symm c) (X s ((extChartAt I p₀).symm c)))).2 with hF
  -- (c1) `uncurry F` is jointly `C^∞` on the open box `univ ×ˢ ball x₀ ρ` (proven sibling).
  have hFsmooth : ContDiffOn ℝ ∞ (Function.uncurry F)
      ((Set.univ : Set ℝ) ×ˢ Metric.ball x₀ ρ) :=
    chart_pushforward_field_jointContDiff X hX p₀ hρ hρ_sub
  -- (c2-exists-bump-target-ball) A `ContDiffBump` at `x₀` whose outer closed ball is inside `ball x₀ ρ`,
  -- so the cutoff is supported in the region where `F` is smooth.
  set b : ContDiffBump x₀ :=
    { rIn := ρ / 4, rOut := ρ / 2, rIn_pos := by positivity, rIn_lt_rOut := by linarith } with hb
  have hb_rIn : b.rIn = ρ / 4 := rfl
  have hb_rOut : b.rOut = ρ / 2 := rfl
  have hclosed_sub : Metric.closedBall x₀ b.rOut ⊆ Metric.ball x₀ ρ := by
    rw [hb_rOut]; exact Metric.closedBall_subset_ball (by linarith)
  -- The cutoff field `G s c = b c • F s c`, and its uncurried form `Gu`.
  refine ⟨fun (s : ℝ) (c : E) => (b c) • F s c, b.rIn, b.rIn_pos, ?_, ?_, ?_⟩
  · -- `ρ' = rIn = ρ/4 ≤ ρ`.
    rw [hb_rIn]; linarith
  · -- (c2-cutoffField-contDiff) Global `C^∞` of `uncurry G : ℝ × E → E`.
    -- The uncurried field, rewritten as the explicit pointwise smul `fun q => b q.2 • F q.1 q.2`.
    have huncurry : Function.uncurry (fun (s : ℝ) (c : E) => (b c) • F s c)
        = fun q : ℝ × E => (b : E → ℝ) q.2 • F q.1 q.2 := by
      funext q; rfl
    rw [huncurry, contDiff_iff_contDiffAt]
    rintro ⟨s, c⟩
    by_cases hc : c ∈ Metric.closedBall x₀ b.rOut
    · -- Inside the support ball: product of the smooth bump (in the spatial slot) and `F`.
      have hc_ball : c ∈ Metric.ball x₀ ρ := hclosed_sub hc
      have hmem : ((s, c) : ℝ × E) ∈ (Set.univ : Set ℝ) ×ˢ Metric.ball x₀ ρ :=
        ⟨Set.mem_univ _, hc_ball⟩
      have hopen : IsOpen ((Set.univ : Set ℝ) ×ˢ Metric.ball x₀ ρ) :=
        isOpen_univ.prod Metric.isOpen_ball
      have hF_at : ContDiffAt ℝ ∞ (Function.uncurry F) (s, c) :=
        hFsmooth.contDiffAt (hopen.mem_nhds hmem)
      have hb_at : ContDiffAt ℝ ∞ (fun q : ℝ × E => (b : E → ℝ) q.2) (s, c) :=
        (b.contDiff.comp_contDiffAt (s, c) contDiffAt_snd)
      exact hb_at.smul hF_at
    · -- Outside the support ball: `b = 0` on a neighbourhood, so the field `≡ 0` there.
      rw [Metric.mem_closedBall] at hc
      have hdist : b.rOut < dist c x₀ := not_le.mp hc
      have hopen : IsOpen {q : ℝ × E | b.rOut < dist q.2 x₀} := by
        have hcont : Continuous (fun q : ℝ × E => dist q.2 x₀) :=
          (continuous_snd.dist continuous_const)
        exact hcont.isOpen_preimage _ isOpen_Ioi
      have hmem : ((s, c) : ℝ × E) ∈ {q : ℝ × E | b.rOut < dist q.2 x₀} := hdist
      refine ContDiffAt.congr_of_eventuallyEq (f := fun _ : ℝ × E => (0 : E))
        contDiffAt_const ?_
      refine Filter.eventuallyEq_of_mem (hopen.mem_nhds hmem) ?_
      intro q hq
      have hq' : b.rOut ≤ dist q.2 x₀ := le_of_lt hq
      have hb0 : (b : E → ℝ) q.2 = 0 := b.zero_of_le_dist hq'
      change (b : E → ℝ) q.2 • F q.1 q.2 = 0
      rw [hb0, zero_smul]
  · -- (c2-eq-on-inner-ball) On `ball x₀ rIn`, the bump equals `1`, so `G = F`.
    intro s c hc
    have hc_closed : c ∈ Metric.closedBall x₀ b.rIn :=
      Metric.ball_subset_closedBall hc
    have hb1 : (b : E → ℝ) c = 1 := b.one_of_mem_closedBall hc_closed
    change (b c) • F s c = F s c
    rw [hb1, one_smul]

-- A1 [H3 v4: orbit confinement to the AGREEMENT ball ρ' (where the cutoff field G = the genuine field F),
--  not merely the chart target — the round-3 fix. Tube argument; c4-* sub-nodes survive with target→ball ρ'.]
theorem chartflow_confined_to_agreementBall
    (p₀ : M) (Φ_E : E × ℝ → E) {ρ ρ' T t₀ : ℝ} (hρ' : 0 < ρ') (hρ'_le : ρ' ≤ ρ)
    (hT : 0 < T)
    (hΦE_cont : ContinuousOn Φ_E
      (Metric.ball (extChartAt I p₀ p₀) ρ ×ˢ Set.Ioo (t₀ - T) (t₀ + T)))
    (hinit : ∀ c ∈ Metric.ball (extChartAt I p₀ p₀) ρ, Φ_E (c, t₀) = c) :
    ∃ (ρ'' T' : ℝ), 0 < ρ'' ∧ 0 < T' ∧ ρ'' ≤ ρ' ∧ T' ≤ T ∧
      ∀ c ∈ Metric.ball (extChartAt I p₀ p₀) ρ'', ∀ s ∈ Set.Ioo (t₀ - T') (t₀ + T'),
        Φ_E (c, s) ∈ Metric.ball (extChartAt I p₀ p₀) ρ' := by
  set x₀ : E := extChartAt I p₀ p₀ with hx₀
  -- The ambient open domain on which `Φ_E` is continuous.
  set D : Set (E × ℝ) := Metric.ball x₀ ρ ×ˢ Set.Ioo (t₀ - T) (t₀ + T) with hD
  have hD_open : IsOpen D := (Metric.isOpen_ball).prod isOpen_Ioo
  -- Seed radius for the compact slice: strictly below the agreement radius `ρ'`.
  set ρseed : ℝ := ρ' / 2 with hρseed
  have hρseed_pos : 0 < ρseed := by rw [hρseed]; linarith
  have hρseed_lt : ρseed < ρ' := by rw [hρseed]; linarith
  -- `closedBall x₀ ρseed ⊆ ball x₀ ρ'` (the agreement ball) and `⊆ ball x₀ ρ` (the domain ball).
  have hseed_sub_ball' : Metric.closedBall x₀ ρseed ⊆ Metric.ball x₀ ρ' :=
    Metric.closedBall_subset_ball hρseed_lt
  have hseed_sub_ballρ : Metric.closedBall x₀ ρseed ⊆ Metric.ball x₀ ρ :=
    Metric.closedBall_subset_ball (lt_of_lt_of_le hρseed_lt hρ'_le)
  -- The open set: domain intersected with the preimage of the open agreement ball.
  set O : Set (E × ℝ) := D ∩ Φ_E ⁻¹' Metric.ball x₀ ρ' with hO
  have hO_open : IsOpen O :=
    hΦE_cont.isOpen_inter_preimage hD_open Metric.isOpen_ball
  -- `t₀` is interior to the time window.
  have ht₀_mem : t₀ ∈ Set.Ioo (t₀ - T) (t₀ + T) := ⟨by linarith, by linarith⟩
  -- The compact slice `closedBall x₀ ρseed ×ˢ {t₀}` lands inside `O`.
  have hslice_sub : Metric.closedBall x₀ ρseed ×ˢ ({t₀} : Set ℝ) ⊆ O := by
    rw [Set.prod_subset_iff]
    intro c hc s hs
    rw [Set.mem_singleton_iff] at hs
    subst hs
    have hc_ballρ : c ∈ Metric.ball x₀ ρ := hseed_sub_ballρ hc
    have hc_ball' : c ∈ Metric.ball x₀ ρ' := hseed_sub_ball' hc
    refine ⟨⟨hc_ballρ, ht₀_mem⟩, ?_⟩
    -- `Φ_E (c, t₀) = c ∈ ball x₀ ρ'` by `hinit`.
    rw [Set.mem_preimage, hinit c hc_ballρ]
    exact hc_ball'
  -- Generalized tube lemma: extract an open box `u ×ˢ v ⊆ O`.
  obtain ⟨u, v, hu_open, hv_open, hseed_u, ht₀_v, huv_sub⟩ :=
    generalized_tube_lemma (isCompact_closedBall x₀ ρseed) isCompact_singleton
      hO_open hslice_sub
  -- Read off a ball radius from the open `u` around `x₀`.
  have hx₀_u : x₀ ∈ u := hseed_u (Metric.mem_closedBall_self hρseed_pos.le)
  obtain ⟨ε, hε_pos, hε_sub⟩ := Metric.isOpen_iff.mp hu_open x₀ hx₀_u
  -- Read off an `Ioo` window from the open `v` around `t₀`.
  have ht₀_v' : t₀ ∈ v := ht₀_v (Set.mem_singleton t₀)
  obtain ⟨l, w, ht₀_lw, hlw_sub⟩ :=
    mem_nhds_iff_exists_Ioo_subset.mp (hv_open.mem_nhds ht₀_v')
  -- Time half-width `δ` with `Ioo (t₀-δ) (t₀+δ) ⊆ Ioo l w ⊆ v`.
  set δ : ℝ := min (t₀ - l) (w - t₀) with hδ
  have hδ_pos : 0 < δ := lt_min (by linarith [ht₀_lw.1]) (by linarith [ht₀_lw.2])
  have hIoo_δ_sub_v : Set.Ioo (t₀ - δ) (t₀ + δ) ⊆ v := by
    refine subset_trans (fun t ht => ?_) hlw_sub
    refine ⟨lt_of_le_of_lt ?_ ht.1, lt_of_lt_of_le ht.2 ?_⟩
    · have hle : δ ≤ t₀ - l := min_le_left _ _
      linarith
    · have hle : δ ≤ w - t₀ := min_le_right _ _
      linarith
  -- Output radii.
  refine ⟨min ε ρ', min δ T, ?_, ?_, min_le_right _ _, min_le_right _ _, ?_⟩
  · exact lt_min hε_pos hρ'
  · exact lt_min hδ_pos hT
  -- Confinement on the shrunken box.
  intro c hc s hs
  have hc_u : c ∈ u := by
    apply hε_sub
    rw [Metric.mem_ball] at hc ⊢
    exact lt_of_lt_of_le hc (min_le_left _ _)
  have hs_v : s ∈ v := by
    apply hIoo_δ_sub_v
    refine ⟨?_, ?_⟩
    · have hle : min δ T ≤ δ := min_le_left _ _
      have := hs.1; linarith
    · have hle : min δ T ≤ δ := min_le_left _ _
      have := hs.2; linarith
  -- `(c, s) ∈ u ×ˢ v ⊆ O`, whose preimage component is exactly the goal.
  have hcs_O : (c, s) ∈ O := huv_sub (Set.mk_mem_prod hc_u hs_v)
  exact hcs_O.2

-- A2 [H3 v4: G→F velocity swap + Icc→Ioo — the chart ODE of ΦE (flow of the CUTOFF field G) carries the
--  GENUINE field F on Ioo, since the orbit stays in the agreement ball ρ' (A1) where G=F. Template chartPhaseVFCutoff_eq_of_mem_closedBall (SmoothFlow.lean:236).]
theorem chartODE_genuineF_on_Ioo
    (p₀ : M) (G F : ℝ → E → E) (Φ_E : E × ℝ → E) {ρ'' ρ' T' t₀ : ℝ} (r : ℝ≥0) {tmin tmax : ℝ}
    (hρ''_le : ρ'' ≤ ρ')
    (hflow : IsLocalFlow G t₀ (extChartAt I p₀ p₀) r tmin tmax Φ_E)
    (hIoo_sub : Set.Ioo (t₀ - T') (t₀ + T') ⊆ Set.Icc tmin tmax)
    (hball_sub : Metric.ball (extChartAt I p₀ p₀) ρ' ⊆ Metric.closedBall (extChartAt I p₀ p₀) (r : ℝ))
    (hGF : ∀ (s : ℝ), ∀ y ∈ Metric.ball (extChartAt I p₀ p₀) ρ', G s y = F s y)
    (hconf : ∀ c ∈ Metric.ball (extChartAt I p₀ p₀) ρ'', ∀ s ∈ Set.Ioo (t₀ - T') (t₀ + T'),
        Φ_E (c, s) ∈ Metric.ball (extChartAt I p₀ p₀) ρ') :
    ∀ c ∈ Metric.ball (extChartAt I p₀ p₀) ρ'', ∀ t ∈ Set.Ioo (t₀ - T') (t₀ + T'),
      HasDerivWithinAt (fun s => Φ_E (c, s)) (F t (Φ_E (c, t))) (Set.Ioo (t₀ - T') (t₀ + T')) t := by
  intro c hc t ht
  -- The orbit start `c` lies in the Picard validity ball `closedBall r`:
  -- `ball ρ'' ⊆ ball ρ' ⊆ closedBall r` via `hρ''_le` and `hball_sub`.
  have hc_closed : c ∈ Metric.closedBall (extChartAt I p₀ p₀) (r : ℝ) :=
    hball_sub (Metric.ball_subset_ball hρ''_le hc)
  -- The flow `Φ_E (c, ·)` solves the CUTOFF ODE with velocity `G` on `Icc tmin tmax`.
  have hderiv_Icc :
      HasDerivWithinAt (fun s => Φ_E (c, s)) (G t (Φ_E (c, t)))
        (Set.Icc tmin tmax) t :=
    hflow.hasDerivWithinAt c hc_closed t (hIoo_sub ht)
  -- Restrict the derivative statement from `Icc` to the smaller set `Ioo`.
  have hderiv_Ioo :
      HasDerivWithinAt (fun s => Φ_E (c, s)) (G t (Φ_E (c, t)))
        (Set.Ioo (t₀ - T') (t₀ + T')) t :=
    hderiv_Icc.mono hIoo_sub
  -- The orbit stays in the agreement ball `ρ'` (by `hconf`), where `G = F`.
  have hGF_pt : G t (Φ_E (c, t)) = F t (Φ_E (c, t)) :=
    hGF t (Φ_E (c, t)) (hconf c hc t ht)
  -- Swap the velocity `G → F` by the pointwise equality.
  exact hGF_pt ▸ hderiv_Ioo

-- field-form-identity [H3 v5: the fixed-p₀-trivialization fibre reading EQUALS the chart-p₀ coordinate velocity
--  `tangentCoordChange I pt p₀ pt (X s pt)` (rfl-level via trivializationAt_apply + tangentCoordChange_def +
--  extChartAt = (chartAt).extend I). Supplies C6's `hF` hypothesis.]
theorem field_form_identity_trivreading_eq_chartvelocity
    (X : ℝ → ∀ x : M, TangentSpace I x) (p₀ : M) (s : ℝ) (c : E) :
    ((trivializationAt E (TangentSpace I) p₀)
        (TotalSpace.mk' E ((extChartAt I p₀).symm c) (X s ((extChartAt I p₀).symm c)))).2
      = tangentCoordChange I ((extChartAt I p₀).symm c) p₀ ((extChartAt I p₀).symm c)
          (X s ((extChartAt I p₀).symm c)) := rfl

-- [H3: pushforward→bare velocity cancellation (under chartflow-eq-bareflow-on-U)]
-- (The cancellation is a purely chart-theoretic chain-rule identity; the section-level instances
--  `[FiniteDimensional ℝ E] [BoundarylessManifold I M] [T2Space M]` are not consumed, so they are
--  explicitly omitted to keep the build warning-free without altering the public signature.)
omit [FiniteDimensional ℝ E] [BoundarylessManifold I M] [T2Space M] in
theorem pushforward_velocity_cancellation (p₀ q : M)
    (hq : q ∈ (extChartAt I p₀).source) (v : E) :
    (mfderivWithin 𝓘(ℝ, E) I (extChartAt I p₀).symm (Set.range I) (extChartAt I p₀ q))
        (tangentCoordChange I q p₀ q v) = v := by
  have hqq : q ∈ (extChartAt I q).source := mem_extChartAt_source q
  -- The transition `T = extChartAt p₀ ∘ (extChartAt q).symm`; it sends the chart-`q` centre to
  -- `extChartAt I p₀ q`.
  have hTc₀ : (extChartAt I p₀ ∘ ⇑(extChartAt I q).symm) (extChartAt I q q) = extChartAt I p₀ q := by
    simp only [Function.comp_apply, (extChartAt I q).left_inv hqq]
  -- Differentiability data: chart-`p₀` inverse (manifold-valued) and the transition (model-valued).
  have hg : MDifferentiableWithinAt 𝓘(ℝ, E) I (extChartAt I p₀).symm (Set.range I)
      (extChartAt I p₀ q) := mdifferentiableWithinAt_extChartAt_symm ((extChartAt I p₀).map_source hq)
  have hfd : HasFDerivWithinAt (extChartAt I p₀ ∘ ⇑(extChartAt I q).symm)
      (tangentCoordChange I q p₀ q) (Set.range I) (extChartAt I q q) :=
    hasFDerivWithinAt_tangentCoordChange (I := I) (x := q) (y := p₀) (z := q) ⟨hqq, hq⟩
  have hf : MDifferentiableWithinAt 𝓘(ℝ, E) 𝓘(ℝ, E)
      (extChartAt I p₀ ∘ ⇑(extChartAt I q).symm) (Set.range I) (extChartAt I q q) :=
    hfd.differentiableWithinAt.mdifferentiableWithinAt
  -- The transition lands in `range I` (its value is `I (chartAt H p₀ _)`).
  have hpre : Set.range I ⊆ (extChartAt I p₀ ∘ ⇑(extChartAt I q).symm) ⁻¹' Set.range I := by
    intro y _
    simp only [Set.mem_preimage, Function.comp_apply, extChartAt_coe]
    exact Set.mem_range_self _
  have hU : UniqueMDiffWithinAt 𝓘(ℝ, E) (Set.range I) (extChartAt I q q) :=
    (I.uniqueMDiffOn) _ (extChartAt_target_subset_range q (mem_extChartAt_target q))
  -- (vc-chain-rule-comp) The manifold chain rule for `(extChartAt p₀).symm ∘ T` at the chart-`q`
  -- centre, with the source point `T (centre) = extChartAt I p₀ q`.
  have hchain := mfderivWithin_comp_of_eq (I := 𝓘(ℝ, E)) (I' := 𝓘(ℝ, E)) (I'' := I)
    (g := (extChartAt I p₀).symm) (f := extChartAt I p₀ ∘ ⇑(extChartAt I q).symm)
    (s := Set.range I) (u := Set.range I) (x := extChartAt I q q)
    (y := extChartAt I p₀ q) hg hf hpre hU hTc₀
  -- (vc-roundtrip-eqOn) Near the centre (within `range I`), the round-trip `(extChartAt p₀).symm ∘ T`
  -- collapses to the chart-`q` inverse, so its within-derivative agrees with that of `(extChartAt q).symm`.
  have hAmem : (extChartAt I q).target ∩ (extChartAt I q).symm ⁻¹' (extChartAt I p₀).source
      ∈ 𝓝[Set.range I] (extChartAt I q q) := by
    refine Filter.inter_mem (extChartAt_target_mem_nhdsWithin q) ?_
    have hsrc : (extChartAt I p₀).source ∈ 𝓝 q :=
      (isOpen_extChartAt_source p₀).mem_nhds hq
    have hpre' := extChartAt_preimage_mem_nhdsWithin' (I := I) (x := q) (x' := q)
      (s := Set.univ) (t := (extChartAt I p₀).source) (mem_extChartAt_source q)
      (by simpa using hsrc)
    simpa only [Set.preimage_univ, Set.univ_inter] using hpre'
  have heqOn : ⇑(extChartAt I q).symm
      =ᶠ[𝓝[Set.range I] (extChartAt I q q)]
        ((extChartAt I p₀).symm ∘ (extChartAt I p₀ ∘ ⇑(extChartAt I q).symm)) := by
    filter_upwards [hAmem] with y hy
    obtain ⟨_, hy₂⟩ := hy
    simp only [Set.mem_preimage] at hy₂
    simp only [Function.comp_apply, (extChartAt I p₀).left_inv hy₂]
  have heqDeriv :
      mfderivWithin 𝓘(ℝ, E) I (extChartAt I q).symm (Set.range I) (extChartAt I q q)
        = mfderivWithin 𝓘(ℝ, E) I
            ((extChartAt I p₀).symm ∘ (extChartAt I p₀ ∘ ⇑(extChartAt I q).symm))
            (Set.range I) (extChartAt I q q) :=
    heqOn.mfderivWithin_eq
      (by simp only [Function.comp_apply, (extChartAt I q).left_inv hqq,
        (extChartAt I p₀).left_inv hq])
  -- (vc-collapse-to-id) The chart-`q` inverse has within-derivative the identity at its centre.
  have hid := mfderivWithin_range_extChartAt_symm (𝕜 := ℝ) (I := I) (x := q)
  -- (vc-tangentCoordChange-def) The model within-derivative of `T` IS `tangentCoordChange I q p₀ q`.
  have hTderiv :
      mfderivWithin 𝓘(ℝ, E) 𝓘(ℝ, E) (extChartAt I p₀ ∘ ⇑(extChartAt I q).symm)
        (Set.range I) (extChartAt I q q) = tangentCoordChange I q p₀ q := by
    rw [mfderivWithin_eq_fderivWithin]
    exact hfd.fderivWithin (hU.uniqueDiffWithinAt)
  -- Combine: `id = g' ∘L tangentCoordChange`, where `g'` is the named within-derivative.
  rw [heqDeriv, hchain, hTderiv] at hid
  -- Apply the inverse identity to `v`: `(g'.comp tcc) v = id v`, i.e. `g' (tcc v) = v`.
  have hv := congrArg (fun L => L v) hid
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] using hv

-- [H3 corrected decomposition: new pending child 7 — bare-velocity recovery via the pushforward chain rule]
-- (`hUsrc : U ⊆ (extChartAt I p₀).source` is a legitimate confinement hypothesis of the public
--  signature; the bare-velocity recovery derives the chart-source membership it needs pointwise from
--  `hconf` instead, so `hUsrc` is not consumed and the unused-variable linter is locally silenced
--  without altering the signature.)
set_option linter.unusedVariables false in
theorem chartflow_eq_bareflow_on_U
    (X : ℝ → ∀ x : M, TangentSpace I x) (p₀ : M)
    (F : ℝ → E → E) (ΦE : E × ℝ → E) (U : Set M) {a b : ℝ}
    (hchartODE : ∀ (p : M), p ∈ U → ∀ t ∈ Set.Ioo a b,
      HasDerivWithinAt (fun s => ΦE (extChartAt I p₀ p, s))
        (F t (ΦE (extChartAt I p₀ p, t))) (Set.Ioo a b) t)
    (hF : ∀ (s : ℝ) (c : E), F s c =
        tangentCoordChange I ((extChartAt I p₀).symm c) p₀
          ((extChartAt I p₀).symm c) (X s ((extChartAt I p₀).symm c)))
    (hconf : ∀ (p : M), p ∈ U → ∀ t ∈ Set.Ioo a b,
      ΦE (extChartAt I p₀ p, t) ∈ (extChartAt I p₀).target)
    (hUsrc : U ⊆ (extChartAt I p₀).source) :
    ∀ (p : M), p ∈ U → ∀ t ∈ Set.Ioo a b,
      HasMFDerivWithinAt 𝓘(ℝ, ℝ) I
        (fun s => (extChartAt I p₀).symm (ΦE (extChartAt I p₀ p, s)))
        (Set.Ioo a b) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight
          (X t ((extChartAt I p₀).symm (ΦE (extChartAt I p₀ p, t))))) := by
  intro p hp t ht
  -- The chart-coordinate trajectory of `p` and its model-space evaluation at `t`.
  set u : ℝ → E := fun s => ΦE (extChartAt I p₀ p, s) with hu
  -- The current chart-coordinate position lies in the chart target (from `hconf`).
  have htgt_t : u t ∈ (extChartAt I p₀).target := hconf p hp t ht
  -- The pulled-back manifold point at time `t`.
  set q : M := (extChartAt I p₀).symm (u t) with hq_def
  -- `q` lies in the chart source, and `extChartAt I p₀ q = u t` (round-trip on the target).
  have hq_src : q ∈ (extChartAt I p₀).source := (extChartAt I p₀).map_target htgt_t
  have hq_round : extChartAt I p₀ q = u t := (extChartAt I p₀).right_inv htgt_t
  -- Confinement: the chart-coordinate trajectory stays in `range I` for times near `t`
  -- within `Ioo a b`, since on all of `Ioo a b` it lands in the chart target ⊆ range I.
  have hconf_range : u ⁻¹' (Set.range I) ∈ 𝓝[Set.Ioo a b] t := by
    refine Filter.mem_of_superset self_mem_nhdsWithin ?_
    intro s hs
    exact extChartAt_target_subset_range p₀ (hconf p hp s hs)
  -- The chart-coordinate ODE for `p` at `t`, with chart velocity `F t (u t)`.
  have hd : HasDerivWithinAt u (F t (u t)) (Set.Ioo a b) t := hchartODE p hp t ht
  -- Transport the chart-coordinate ODE to the manifold via the project bridge: the manifold
  -- derivative has the TRANSPORTED velocity (chart pull-back of `F t (u t)`).
  have hbridge :
      HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun s => (extChartAt I p₀).symm (u s)) (Set.Ioo a b) t
        ((mfderivWithin 𝓘(ℝ, E) I (extChartAt I p₀).symm (Set.range I) (u t)) ∘L
          ((ContinuousLinearMap.id ℝ ℝ).smulRight (F t (u t)))) :=
    chartCoord_hasDerivWithinAt_to_manifold_hasMFDerivWithinAt
      (I := I) p₀ u (Set.Ioo a b) t (F t (u t)) htgt_t hconf_range hd
  -- The transported velocity collapses to the bare `X`-velocity.  Pin `F t (u t)` to the
  -- chart-`p₀` pushforward of `X t q` (the field-form identity `hF`), then cancel the
  -- pushforward against `mfderivWithin (extChartAt p₀).symm` (the centre identity).
  have hcancel :
      (mfderivWithin 𝓘(ℝ, E) I (extChartAt I p₀).symm (Set.range I) (u t)) (F t (u t))
        = X t q := by
    rw [hF t (u t)]
    -- `(extChartAt I p₀).symm (u t) = q`, so the field reduces to `tangentCoordChange I q p₀ q (X t q)`.
    rw [← hq_def, ← hq_round]
    exact pushforward_velocity_cancellation (I := I) p₀ q hq_src (X t q)
  -- Assemble: the transported velocity CLM equals the bare `(1).smulRight (X t q)`.
  have hvel :
      (mfderivWithin 𝓘(ℝ, E) I (extChartAt I p₀).symm (Set.range I) (u t)) ∘L
          ((ContinuousLinearMap.id ℝ ℝ).smulRight (F t (u t)))
        = (1 : ℝ →L[ℝ] ℝ).smulRight (X t q) :=
    ContinuousLinearMap.ext fun r => by
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply,
        ContinuousLinearMap.id_apply, ContinuousLinearMap.one_apply, map_smul, hcancel]
  -- Conclude: rewrite the headline bare velocity back to the bridge's transported form
  -- (`hvel.symm`); the function parts agree definitionally (`u s = ΦE (extChartAt I p₀ p, s)`).
  rw [← hvel]
  exact hbridge

-- H3 headline (v5: intrinsic jointly-smooth section input `hX`; `[I.Boundaryless]` added — needed by
--  isOpen_extChartAt_target / extChartAt_target_mem_nhds, NOT derivable from [BoundarylessManifold I M].)
theorem h3_local_flow_jointSmooth_and_integralCurve [CompleteSpace E] [I.Boundaryless]
    (X : ℝ → ∀ x : M, TangentSpace I x)
    (hX : ContMDiff (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
      (fun q : ℝ × M => (TotalSpace.mk' E q.2 (X q.1 q.2) : TangentBundle I M)))
    (t₀ : ℝ) (p₀ : M) :
    ∃ (U : Set M) (_hU : IsOpen U) (_hp₀ : p₀ ∈ U) (T : ℝ) (_hT : 0 < T)
      (Φ : M → ℝ → M),
      (∀ p ∈ U, Φ p t₀ = p) ∧
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) I ∞ (fun q : ℝ × M => Φ q.2 q.1)
        (Set.Ioo (t₀ - T) (t₀ + T) ×ˢ U) ∧
      (∀ p ∈ U, ∀ t ∈ Set.Ioo (t₀ - T) (t₀ + T),
        HasMFDerivAt 𝓘(ℝ, ℝ) I (fun s => Φ p s) t
          ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (Φ p t)))) := by
  -- The chart centre in the Euclidean model.
  set x₀ : E := extChartAt I p₀ p₀ with hx₀
  -- (chart-ball radius) `x₀` lies in the (open, by `[I.Boundaryless]`) extended-chart target,
  -- so there is a ball `ball x₀ ρ ⊆ target` on which the chart-pushforward field is defined.
  have hx₀_tgt : x₀ ∈ (extChartAt I p₀).target := by
    rw [hx₀]; exact (extChartAt I p₀).map_source (mem_extChartAt_source p₀)
  obtain ⟨ρ, hρ_pos, hρ_sub⟩ :=
    Metric.isOpen_iff.mp (isOpen_extChartAt_target p₀) x₀ hx₀_tgt
  -- (C2) Cutoff-globalize C1's chart-pushforward field `F` to a globally-`C∞` field `G`,
  -- agreeing with `F` on the inner ball `ball x₀ ρ'`.
  obtain ⟨G, ρ', hρ'_pos, hρ'_le, hG_smooth, hGF⟩ :=
    chart_pushforward_field_cutoff_globalContDiff X hX p₀ hρ_pos hρ_sub
  -- (C3) The Euclidean `C∞` flow of the cutoff field `G` at `(t₀, x₀)`: Picard radius `r`,
  -- horizon `ε`, and a joint-`ContDiffOn` smoothness radius `ρ_E ≤ r`, horizon `T_E ≤ ε`.
  obtain ⟨r, ε, hr_pos, hε_pos, ΦE, hflow, ρ_E, T_E, hρE_pos, hTE_pos, hρE_le_r, hTE_le_ε,
      hΦE_smooth⟩ :=
    exists_isLocalFlow_contDiffOn_top (f := G) (t₀ := t₀) (x₀ := x₀) hG_smooth
  -- (operative agreement radius) `ρ'ₒₚ := min ρ' ρ_E ≤ ρ_E ≤ r`, still inside the `G = F` ball.
  set ρ'ₒₚ : ℝ := min ρ' ρ_E with hρ'ₒₚ
  have hρ'ₒₚ_pos : 0 < ρ'ₒₚ := lt_min hρ'_pos hρE_pos
  have hρ'ₒₚ_le_ρ' : ρ'ₒₚ ≤ ρ' := min_le_left _ _
  have hρ'ₒₚ_le_ρE : ρ'ₒₚ ≤ ρ_E := min_le_right _ _
  have hρ'ₒₚ_le_r : ρ'ₒₚ ≤ (r : ℝ) := le_trans hρ'ₒₚ_le_ρE hρE_le_r
  -- A1 hasn't run yet, but the full seed-radius chain `ρ'' ≤ ρ'ₒₚ ≤ r` is recorded after A1.
  -- The Euclidean flow is continuous on `ball x₀ ρ_E ×ˢ Ioo (t₀ ± T_E)` (from `ContDiffOn`).
  have hΦE_cont : ContinuousOn ΦE
      (Metric.ball x₀ ρ_E ×ˢ Set.Ioo (t₀ - T_E) (t₀ + T_E)) :=
    hΦE_smooth.continuousOn
  -- The flow fixes initial data on `ball x₀ ρ_E` (⊆ `closedBall x₀ r`, by `ρ_E ≤ r`).
  have hinit_ρE : ∀ c ∈ Metric.ball x₀ ρ_E, ΦE (c, t₀) = c := by
    intro c hc
    have hc_cb : c ∈ Metric.closedBall x₀ (r : ℝ) :=
      Metric.ball_subset_closedBall (Metric.ball_subset_ball hρE_le_r hc)
    exact hflow.apply_initial c hc_cb
  -- (A1) Confine the orbit (started in `ball ρ''`) into the agreement ball `ρ'ₒₚ` on `Ioo (t₀ ± T')`.
  obtain ⟨ρ'', T', hρ''_pos, hT'_pos, hρ''_le, hT'_le, hconf⟩ :=
    chartflow_confined_to_agreementBall (I := I) p₀ ΦE
      (ρ := ρ_E) (ρ' := ρ'ₒₚ) (T := T_E) (t₀ := t₀)
      hρ'ₒₚ_pos hρ'ₒₚ_le_ρE hTE_pos hΦE_cont hinit_ρE
  -- Seed-radius cap into the Picard validity ball: `ρ'' ≤ ρ'ₒₚ ≤ r`.
  have hρ''_le_r : ρ'' ≤ (r : ℝ) := le_trans hρ''_le hρ'ₒₚ_le_r
  -- (A2) On the confined region the GENUINE field `F` drives the chart ODE on `Ioo (t₀ ± T')`,
  -- because `G = F` on `ball x₀ ρ'ₒₚ` (the orbit stays there).  Abbreviate the genuine field `F`.
  set F : ℝ → E → E := fun (s : ℝ) (c : E) =>
    ((trivializationAt E (TangentSpace I) p₀)
      (TotalSpace.mk' E ((extChartAt I p₀).symm c) (X s ((extChartAt I p₀).symm c)))).2 with hF
  -- The cutoff agreement `G = F` on the operative agreement ball `ball x₀ ρ'ₒₚ ⊆ ball x₀ ρ'`.
  have hGF_op : ∀ (s : ℝ), ∀ y ∈ Metric.ball x₀ ρ'ₒₚ, G s y = F s y := by
    intro s y hy
    have hy' : y ∈ Metric.ball x₀ ρ' := Metric.ball_subset_ball hρ'ₒₚ_le_ρ' hy
    exact hGF s y hy'
  -- The Picard validity ball contains the agreement ball: `ball x₀ ρ'ₒₚ ⊆ closedBall x₀ r`.
  have hball_sub : Metric.ball x₀ ρ'ₒₚ ⊆ Metric.closedBall x₀ (r : ℝ) := by
    intro y hy
    exact Metric.ball_subset_closedBall (Metric.ball_subset_ball hρ'ₒₚ_le_r hy)
  -- The time window `Ioo (t₀ ± T') ⊆ Icc (t₀ - ε) (t₀ + ε)` (the `IsLocalFlow` domain), via `T' ≤ ε`.
  have hT'_le_ε : T' ≤ ε := le_trans hT'_le hTE_le_ε
  have hIoo_sub : Set.Ioo (t₀ - T') (t₀ + T') ⊆ Set.Icc (t₀ - ε) (t₀ + ε) := by
    intro s hs
    exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
  -- A2 delivers the chart ODE with the genuine velocity `F` on the seed ball `ball x₀ ρ''`.
  have hchartODE_raw :
      ∀ c ∈ Metric.ball x₀ ρ'', ∀ t ∈ Set.Ioo (t₀ - T') (t₀ + T'),
        HasDerivWithinAt (fun s => ΦE (c, s)) (F t (ΦE (c, t)))
          (Set.Ioo (t₀ - T') (t₀ + T')) t :=
    chartODE_genuineF_on_Ioo (I := I) p₀ G F ΦE r
      (hρ''_le := hρ''_le) (hflow := hflow) (hIoo_sub := hIoo_sub)
      (hball_sub := hball_sub) (hGF := hGF_op) (hconf := hconf)
  -- (the open neighbourhood `U` and the manifold flow `Φ`)
  set U : Set M := (extChartAt I p₀).source ∩ (extChartAt I p₀) ⁻¹' (Metric.ball x₀ ρ'') with hU
  set Φ : M → ℝ → M := fun p s => (extChartAt I p₀).symm (ΦE (extChartAt I p₀ p, s)) with hΦ
  -- `U` is open: chart source ∩ continuous-preimage of an open ball.
  have hU_open : IsOpen U :=
    (continuousOn_extChartAt p₀).isOpen_inter_preimage
      (isOpen_extChartAt_source p₀) Metric.isOpen_ball
  -- `p₀ ∈ U`: it is in its own chart source, and `extChartAt I p₀ p₀ = x₀ ∈ ball x₀ ρ''`.
  have hp₀_U : p₀ ∈ U := by
    refine ⟨mem_extChartAt_source p₀, ?_⟩
    rw [Set.mem_preimage, ← hx₀]
    exact Metric.mem_ball_self hρ''_pos
  -- `U ⊆ source` and the chart membership facts on `U`.
  have hU_src : U ⊆ (extChartAt I p₀).source := Set.inter_subset_left
  have hU_ball : ∀ p ∈ U, extChartAt I p₀ p ∈ Metric.ball x₀ ρ'' := fun p hp => hp.2
  -- (chart-coordinate reindexing) the chart-`p₀` ODE rephrased over points `p ∈ U`.
  have hchartODE :
      ∀ (p : M), p ∈ U → ∀ t ∈ Set.Ioo (t₀ - T') (t₀ + T'),
        HasDerivWithinAt (fun s => ΦE (extChartAt I p₀ p, s))
          (F t (ΦE (extChartAt I p₀ p, t))) (Set.Ioo (t₀ - T') (t₀ + T')) t :=
    fun p hp t ht => hchartODE_raw (extChartAt I p₀ p) (hU_ball p hp) t ht
  -- (confinement to the chart target) on `U × Ioo` the orbit lands in `(extChartAt I p₀).target`.
  have hconf_tgt :
      ∀ (p : M), p ∈ U → ∀ t ∈ Set.Ioo (t₀ - T') (t₀ + T'),
        ΦE (extChartAt I p₀ p, t) ∈ (extChartAt I p₀).target := by
    intro p hp t ht
    have hmem : ΦE (extChartAt I p₀ p, t) ∈ Metric.ball x₀ ρ'ₒₚ :=
      hconf (extChartAt I p₀ p) (hU_ball p hp) t ht
    have hsub_ρ : Metric.ball x₀ ρ'ₒₚ ⊆ Metric.ball x₀ ρ :=
      Metric.ball_subset_ball (le_trans hρ'ₒₚ_le_ρ' hρ'_le)
    exact hρ_sub (hsub_ρ hmem)
  -- (field-form identity) supplies C6's `hF` hypothesis.
  have hF_id : ∀ (s : ℝ) (c : E), F s c =
      tangentCoordChange I ((extChartAt I p₀).symm c) p₀
        ((extChartAt I p₀).symm c) (X s ((extChartAt I p₀).symm c)) := by
    intro s c
    rw [hF]
    exact field_form_identity_trivreading_eq_chartvelocity X p₀ s c
  -- (C5) push the joint `ContDiffOn` flow through `(extChartAt I p₀).symm` to manifold `ContMDiffOn`.
  -- The chart-ball/coordinate hypotheses are stated via `I ((chartAt H p₀) ·)`; reconcile with
  -- `extChartAt I p₀ · = I ((chartAt H p₀) ·)` (`extChartAt_coe`).
  have hcoe : ∀ p : M, I ((chartAt H p₀) p) = extChartAt I p₀ p := by
    intro p; rw [extChartAt_coe]; rfl
  have hcoe₀ : I ((chartAt H p₀) p₀) = x₀ := by rw [hcoe, hx₀]
  have hContMDiffOn :
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) I ∞
        (fun q : ℝ × M => (extChartAt I p₀).symm (ΦE (I ((chartAt H p₀) q.2), q.1)))
        (Set.Ioo (t₀ - T') (t₀ + T') ×ˢ U) := by
    refine h3_manifoldFlow_contMDiffOn_of_jointContDiffOn (I := I) p₀ ΦE
      (ρ := ρ'ₒₚ) (T := T') (t₀ := t₀) U hU_open ?_ ?_ ?_ ?_
    · -- `U ⊆ (chartAt H p₀).source`.
      rw [← extChartAt_source (I := I)]; exact hU_src
    · -- `hUball`: chart coordinate of each `p ∈ U` lies in `ball (I (chartAt H p₀ p₀)) ρ'ₒₚ`.
      intro p hp
      rw [hcoe p, hcoe₀]
      exact Metric.ball_subset_ball hρ''_le (hU_ball p hp)
    · -- `hΦE_smooth` on `ball (I (chartAt H p₀ p₀)) ρ'ₒₚ ×ˢ Ioo (t₀ ± T')`.
      rw [hcoe₀]
      refine hΦE_smooth.mono (Set.prod_mono ?_ ?_)
      · exact Metric.ball_subset_ball hρ'ₒₚ_le_ρE
      · exact Set.Ioo_subset_Ioo (by linarith [hT'_le]) (by linarith [hT'_le])
    · -- `htgt`: the orbit lands in the chart target.
      intro p hp s hs
      rw [hcoe p]
      exact hconf_tgt p hp s hs
  -- Rephrase the `ContMDiffOn` to the `Φ`-form (`extChartAt I p₀ = I ∘ chartAt H p₀`).
  have hContMDiffOn' :
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) I ∞ (fun q : ℝ × M => Φ q.2 q.1)
        (Set.Ioo (t₀ - T') (t₀ + T') ×ˢ U) := by
    refine hContMDiffOn.congr ?_
    intro q _
    rw [hΦ, hcoe q.2]
  -- (C6) the bare-velocity `HasMFDerivWithinAt` on `U × Ioo`.
  have hbare_within :
      ∀ (p : M), p ∈ U → ∀ t ∈ Set.Ioo (t₀ - T') (t₀ + T'),
        HasMFDerivWithinAt 𝓘(ℝ, ℝ) I
          (fun s => (extChartAt I p₀).symm (ΦE (extChartAt I p₀ p, s)))
          (Set.Ioo (t₀ - T') (t₀ + T')) t
          ((1 : ℝ →L[ℝ] ℝ).smulRight
            (X t ((extChartAt I p₀).symm (ΦE (extChartAt I p₀ p, t))))) :=
    chartflow_eq_bareflow_on_U (I := I) X p₀ F ΦE U hchartODE hF_id hconf_tgt hU_src
  -- (C7) upgrade within→full: `Ioo (t₀ ± T') ∈ 𝓝 t`.
  have hbare :
      ∀ (p : M), p ∈ U → ∀ t ∈ Set.Ioo (t₀ - T') (t₀ + T'),
        HasMFDerivAt 𝓘(ℝ, ℝ) I (fun s => Φ p s) t
          ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (Φ p t))) := by
    intro p hp t ht
    have hnhds : Set.Ioo (t₀ - T') (t₀ + T') ∈ 𝓝 t :=
      isOpen_Ioo.mem_nhds ht
    have := (hbare_within p hp t ht).hasMFDerivAt hnhds
    rw [hΦ]; exact this
  -- (initial value) `Φ p t₀ = p` for `p ∈ U`, via `apply_initial` + chart left-inverse.
  have hΦinit : ∀ p ∈ U, Φ p t₀ = p := by
    intro p hp
    have hcb : extChartAt I p₀ p ∈ Metric.closedBall x₀ (r : ℝ) :=
      Metric.ball_subset_closedBall (Metric.ball_subset_ball hρ''_le_r (hU_ball p hp))
    change (extChartAt I p₀).symm (ΦE (extChartAt I p₀ p, t₀)) = p
    rw [hflow.apply_initial (extChartAt I p₀ p) hcb]
    exact (extChartAt I p₀).left_inv (hU_src hp)
  -- Package the headline.
  exact ⟨U, hU_open, hp₀_U, T', hT'_pos, Φ, hΦinit, hContMDiffOn', hbare⟩

-- Strengthened H3: additionally expose the chart-`p₀` Euclidean Picard flow `ΦE` as an
-- `IsLocalFlow` together with its joint `ContDiffOn` regularity and the chart realisation
-- `Φ p s = (extChartAt I p₀).symm (ΦE (extChartAt I p₀ p, s))` on `U × Ioo`.  This is the
-- interior-`t₀` chart Picard datum the moving-chart-local variational discharge consumes; the
-- manifold flow `Φ` is exactly the chart-symm reading of `ΦE`, so the realisation is definitional.
theorem h3_local_flow_chartIsLocalFlow_and_realisation [CompleteSpace E] [I.Boundaryless]
    (X : ℝ → ∀ x : M, TangentSpace I x)
    (hX : ContMDiff (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
      (fun q : ℝ × M => (TotalSpace.mk' E q.2 (X q.1 q.2) : TangentBundle I M)))
    (t₀ : ℝ) (p₀ : M) :
    ∃ (U : Set M) (_hU : IsOpen U) (_hp₀ : p₀ ∈ U) (T : ℝ) (_hT : 0 < T)
      (Φ : M → ℝ → M)
      (f : ℝ → E → E) (x₀ : E) (r : ℝ≥0) (ε : ℝ) (ΦE : E × ℝ → E),
      ContDiff ℝ ∞ (Function.uncurry f) ∧
      x₀ = extChartAt I p₀ p₀ ∧
      0 < (r : ℝ) ∧ 0 < ε ∧
      IsLocalFlow f t₀ x₀ r (t₀ - ε) (t₀ + ε) ΦE ∧
      (∃ (ρE TE : ℝ), 0 < ρE ∧ 0 < TE ∧
        ContDiffOn ℝ ∞ ΦE (Metric.ball x₀ ρE ×ˢ Set.Ioo (t₀ - TE) (t₀ + TE))) ∧
      (∀ p ∈ U, Φ p t₀ = p) ∧
      (∀ p ∈ U, ∀ s : ℝ,
        Φ p s = (extChartAt I p₀).symm (ΦE (extChartAt I p₀ p, s))) ∧
      (∀ p ∈ U, ∀ s ∈ Set.Ioo (t₀ - T) (t₀ + T),
        ΦE (extChartAt I p₀ p, s) ∈ (extChartAt I p₀).target) ∧
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) I ∞ (fun q : ℝ × M => Φ q.2 q.1)
        (Set.Ioo (t₀ - T) (t₀ + T) ×ˢ U) ∧
      (∀ p ∈ U, ∀ t ∈ Set.Ioo (t₀ - T) (t₀ + T),
        HasMFDerivAt 𝓘(ℝ, ℝ) I (fun s => Φ p s) t
          ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (Φ p t)))) := by
  -- The chart centre in the Euclidean model.
  set x₀ : E := extChartAt I p₀ p₀ with hx₀
  have hx₀_tgt : x₀ ∈ (extChartAt I p₀).target := by
    rw [hx₀]; exact (extChartAt I p₀).map_source (mem_extChartAt_source p₀)
  obtain ⟨ρ, hρ_pos, hρ_sub⟩ :=
    Metric.isOpen_iff.mp (isOpen_extChartAt_target p₀) x₀ hx₀_tgt
  obtain ⟨G, ρ', hρ'_pos, hρ'_le, hG_smooth, hGF⟩ :=
    chart_pushforward_field_cutoff_globalContDiff X hX p₀ hρ_pos hρ_sub
  obtain ⟨r, ε, hr_pos, hε_pos, ΦE, hflow, ρ_E, T_E, hρE_pos, hTE_pos, hρE_le_r, hTE_le_ε,
      hΦE_smooth⟩ :=
    exists_isLocalFlow_contDiffOn_top (f := G) (t₀ := t₀) (x₀ := x₀) hG_smooth
  set ρ'ₒₚ : ℝ := min ρ' ρ_E with hρ'ₒₚ
  have hρ'ₒₚ_pos : 0 < ρ'ₒₚ := lt_min hρ'_pos hρE_pos
  have hρ'ₒₚ_le_ρ' : ρ'ₒₚ ≤ ρ' := min_le_left _ _
  have hρ'ₒₚ_le_ρE : ρ'ₒₚ ≤ ρ_E := min_le_right _ _
  have hρ'ₒₚ_le_r : ρ'ₒₚ ≤ (r : ℝ) := le_trans hρ'ₒₚ_le_ρE hρE_le_r
  have hΦE_cont : ContinuousOn ΦE
      (Metric.ball x₀ ρ_E ×ˢ Set.Ioo (t₀ - T_E) (t₀ + T_E)) :=
    hΦE_smooth.continuousOn
  have hinit_ρE : ∀ c ∈ Metric.ball x₀ ρ_E, ΦE (c, t₀) = c := by
    intro c hc
    have hc_cb : c ∈ Metric.closedBall x₀ (r : ℝ) :=
      Metric.ball_subset_closedBall (Metric.ball_subset_ball hρE_le_r hc)
    exact hflow.apply_initial c hc_cb
  obtain ⟨ρ'', T', hρ''_pos, hT'_pos, hρ''_le, hT'_le, hconf⟩ :=
    chartflow_confined_to_agreementBall (I := I) p₀ ΦE
      (ρ := ρ_E) (ρ' := ρ'ₒₚ) (T := T_E) (t₀ := t₀)
      hρ'ₒₚ_pos hρ'ₒₚ_le_ρE hTE_pos hΦE_cont hinit_ρE
  have hρ''_le_r : ρ'' ≤ (r : ℝ) := le_trans hρ''_le hρ'ₒₚ_le_r
  set F : ℝ → E → E := fun (s : ℝ) (c : E) =>
    ((trivializationAt E (TangentSpace I) p₀)
      (TotalSpace.mk' E ((extChartAt I p₀).symm c) (X s ((extChartAt I p₀).symm c)))).2 with hF
  have hGF_op : ∀ (s : ℝ), ∀ y ∈ Metric.ball x₀ ρ'ₒₚ, G s y = F s y := by
    intro s y hy
    exact hGF s y (Metric.ball_subset_ball hρ'ₒₚ_le_ρ' hy)
  have hball_sub : Metric.ball x₀ ρ'ₒₚ ⊆ Metric.closedBall x₀ (r : ℝ) :=
    fun y hy => Metric.ball_subset_closedBall (Metric.ball_subset_ball hρ'ₒₚ_le_r hy)
  have hT'_le_ε : T' ≤ ε := le_trans hT'_le hTE_le_ε
  have hIoo_sub : Set.Ioo (t₀ - T') (t₀ + T') ⊆ Set.Icc (t₀ - ε) (t₀ + ε) :=
    fun s hs => ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hchartODE_raw :
      ∀ c ∈ Metric.ball x₀ ρ'', ∀ t ∈ Set.Ioo (t₀ - T') (t₀ + T'),
        HasDerivWithinAt (fun s => ΦE (c, s)) (F t (ΦE (c, t)))
          (Set.Ioo (t₀ - T') (t₀ + T')) t :=
    chartODE_genuineF_on_Ioo (I := I) p₀ G F ΦE r
      (hρ''_le := hρ''_le) (hflow := hflow) (hIoo_sub := hIoo_sub)
      (hball_sub := hball_sub) (hGF := hGF_op) (hconf := hconf)
  set U : Set M := (extChartAt I p₀).source ∩ (extChartAt I p₀) ⁻¹' (Metric.ball x₀ ρ'') with hU
  set Φ : M → ℝ → M := fun p s => (extChartAt I p₀).symm (ΦE (extChartAt I p₀ p, s)) with hΦ
  have hU_open : IsOpen U :=
    (continuousOn_extChartAt p₀).isOpen_inter_preimage
      (isOpen_extChartAt_source p₀) Metric.isOpen_ball
  have hp₀_U : p₀ ∈ U := by
    refine ⟨mem_extChartAt_source p₀, ?_⟩
    rw [Set.mem_preimage, ← hx₀]
    exact Metric.mem_ball_self hρ''_pos
  have hU_src : U ⊆ (extChartAt I p₀).source := Set.inter_subset_left
  have hU_ball : ∀ p ∈ U, extChartAt I p₀ p ∈ Metric.ball x₀ ρ'' := fun p hp => hp.2
  have hchartODE :
      ∀ (p : M), p ∈ U → ∀ t ∈ Set.Ioo (t₀ - T') (t₀ + T'),
        HasDerivWithinAt (fun s => ΦE (extChartAt I p₀ p, s))
          (F t (ΦE (extChartAt I p₀ p, t))) (Set.Ioo (t₀ - T') (t₀ + T')) t :=
    fun p hp t ht => hchartODE_raw (extChartAt I p₀ p) (hU_ball p hp) t ht
  have hconf_tgt :
      ∀ (p : M), p ∈ U → ∀ t ∈ Set.Ioo (t₀ - T') (t₀ + T'),
        ΦE (extChartAt I p₀ p, t) ∈ (extChartAt I p₀).target := by
    intro p hp t ht
    have hmem : ΦE (extChartAt I p₀ p, t) ∈ Metric.ball x₀ ρ'ₒₚ :=
      hconf (extChartAt I p₀ p) (hU_ball p hp) t ht
    exact hρ_sub (Metric.ball_subset_ball (le_trans hρ'ₒₚ_le_ρ' hρ'_le) hmem)
  have hF_id : ∀ (s : ℝ) (c : E), F s c =
      tangentCoordChange I ((extChartAt I p₀).symm c) p₀
        ((extChartAt I p₀).symm c) (X s ((extChartAt I p₀).symm c)) := by
    intro s c
    rw [hF]
    exact field_form_identity_trivreading_eq_chartvelocity X p₀ s c
  have hcoe : ∀ p : M, I ((chartAt H p₀) p) = extChartAt I p₀ p := by
    intro p; rw [extChartAt_coe]; rfl
  have hcoe₀ : I ((chartAt H p₀) p₀) = x₀ := by rw [hcoe, hx₀]
  have hContMDiffOn :
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) I ∞
        (fun q : ℝ × M => (extChartAt I p₀).symm (ΦE (I ((chartAt H p₀) q.2), q.1)))
        (Set.Ioo (t₀ - T') (t₀ + T') ×ˢ U) := by
    refine h3_manifoldFlow_contMDiffOn_of_jointContDiffOn (I := I) p₀ ΦE
      (ρ := ρ'ₒₚ) (T := T') (t₀ := t₀) U hU_open ?_ ?_ ?_ ?_
    · rw [← extChartAt_source (I := I)]; exact hU_src
    · intro p hp
      rw [hcoe p, hcoe₀]
      exact Metric.ball_subset_ball hρ''_le (hU_ball p hp)
    · rw [hcoe₀]
      refine hΦE_smooth.mono (Set.prod_mono ?_ ?_)
      · exact Metric.ball_subset_ball hρ'ₒₚ_le_ρE
      · exact Set.Ioo_subset_Ioo (by linarith [hT'_le]) (by linarith [hT'_le])
    · intro p hp s hs
      rw [hcoe p]
      exact hconf_tgt p hp s hs
  have hContMDiffOn' :
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) I ∞ (fun q : ℝ × M => Φ q.2 q.1)
        (Set.Ioo (t₀ - T') (t₀ + T') ×ˢ U) := by
    refine hContMDiffOn.congr ?_
    intro q _
    rw [hΦ, hcoe q.2]
  have hbare_within :
      ∀ (p : M), p ∈ U → ∀ t ∈ Set.Ioo (t₀ - T') (t₀ + T'),
        HasMFDerivWithinAt 𝓘(ℝ, ℝ) I
          (fun s => (extChartAt I p₀).symm (ΦE (extChartAt I p₀ p, s)))
          (Set.Ioo (t₀ - T') (t₀ + T')) t
          ((1 : ℝ →L[ℝ] ℝ).smulRight
            (X t ((extChartAt I p₀).symm (ΦE (extChartAt I p₀ p, t))))) :=
    chartflow_eq_bareflow_on_U (I := I) X p₀ F ΦE U hchartODE hF_id hconf_tgt hU_src
  have hbare :
      ∀ (p : M), p ∈ U → ∀ t ∈ Set.Ioo (t₀ - T') (t₀ + T'),
        HasMFDerivAt 𝓘(ℝ, ℝ) I (fun s => Φ p s) t
          ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (Φ p t))) := by
    intro p hp t ht
    have hnhds : Set.Ioo (t₀ - T') (t₀ + T') ∈ 𝓝 t := isOpen_Ioo.mem_nhds ht
    have := (hbare_within p hp t ht).hasMFDerivAt hnhds
    rw [hΦ]; exact this
  have hΦinit : ∀ p ∈ U, Φ p t₀ = p := by
    intro p hp
    have hcb : extChartAt I p₀ p ∈ Metric.closedBall x₀ (r : ℝ) :=
      Metric.ball_subset_closedBall (Metric.ball_subset_ball hρ''_le_r (hU_ball p hp))
    change (extChartAt I p₀).symm (ΦE (extChartAt I p₀ p, t₀)) = p
    rw [hflow.apply_initial (extChartAt I p₀ p) hcb]
    exact (extChartAt I p₀).left_inv (hU_src hp)
  -- The chart realisation `Φ p s = (extChartAt I p₀).symm (ΦE (extChartAt I p₀ p, s))` is `hΦ`.
  have hreal : ∀ p ∈ U, ∀ s : ℝ,
      Φ p s = (extChartAt I p₀).symm (ΦE (extChartAt I p₀ p, s)) := fun p _ s => rfl
  -- Package, exposing the chart Picard flow `ΦE` and its joint smoothness.
  exact ⟨U, hU_open, hp₀_U, T', hT'_pos, Φ, G, x₀, r, ε, ΦE, hG_smooth, rfl, hr_pos, hε_pos,
    hflow, ⟨ρ_E, T_E, hρE_pos, hTE_pos, hΦE_smooth⟩, hΦinit, hreal, hconf_tgt, hContMDiffOn',
    hbare⟩

end Manifold

end DifferentialGeometry.PDE.RicciFlow.ODE
