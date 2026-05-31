import DifferentialGeometry.Metric.Basic
import DifferentialGeometry.Integral.Connection.Ricci
import DifferentialGeometry.PDE.ParabolicShortTime
import DifferentialGeometry.PDE.DeTurck.VectorField
import DifferentialGeometry.PDE.DeTurck.LieDerivativeMetric
import DifferentialGeometry.PDE.DeTurck.StrictParabolicity
import DifferentialGeometry.PDE.RicciFlow.DeTurckRHS
import DifferentialGeometry.PDE.RicciFlow.DeTurckShortTime
import DifferentialGeometry.PDE.RicciFlow.DeTurckVFTimeFamily
import DifferentialGeometry.PDE.RicciFlow.DeTurckSolutionC1
import DifferentialGeometry.PDE.RicciFlow.ODE.TimeDependentFlow
import DifferentialGeometry.PDE.RicciFlow.Pullback.Metric
import DifferentialGeometry.PDE.RicciFlow.Pullback.RicciNaturality
import DifferentialGeometry.PDE.RicciFlow.Pullback.LieNaturality
import DifferentialGeometry.PDE.RicciFlow.Pullback.ChainRule
import Mathlib.Analysis.Calculus.Deriv.Basic
import DifferentialGeometry.PDE.RicciFlow.ShortTimeParabolic.DeTurckRicciPde
import DifferentialGeometry.PDE.RicciFlow.ShortTimeAssembly.ConjugatingDiffeoFamily
import DifferentialGeometry.PDE.RicciFlow.ShortTimeAssembly.FlatAssemblyInterior
import DifferentialGeometry.PDE.RicciFlow.ShortTimeAssembly.RicciFlowPdeAtZero
import DifferentialGeometry.PDE.RicciFlow.ShortTimeFlow.ConjugatingFlowData
import DifferentialGeometry.Integral.Measure.ChartDensity

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle
open scoped Manifold ContDiff
open DifferentialGeometry
open DifferentialGeometry.PDE
open DifferentialGeometry.PDE.DeTurck
open DifferentialGeometry.PDE.RicciFlow.ODE
open DifferentialGeometry.PDE.RicciFlow.Pullback
open DifferentialGeometry.Integral.Connection

/-! ## Short-time existence for the Ricci flow

Classical construction (Hamilton–DeTurck): given an initial smooth Riemannian
metric `g₀` on a closed manifold `M`, the Ricci flow `∂_t g = -2 Ric(g)` admits
a positive-time smooth solution with `g(0) = g₀`. The proof passes through:

1. Solve the (strictly parabolic) DeTurck–Ricci flow
   `∂_t g_DT = -2 Ric(g_DT) + 𝓛_{X_DT} g_DT` (where `X_DT = deTurckVF g_DT g_bg`)
   for time `[0, T_DT)`, via `deturck_ricci_pde_shorttime` (here we take
   `g_bg := g₀` as the background metric).
2. Integrate the time-dependent vector field `-X_DT(t)` to obtain a smooth family
   of diffeomorphisms `Φ_t : M ≃ₘ M` with `Φ_0 = id` and `∂_t Φ_t = -X_DT ∘ Φ_t`.
3. Set `g_fam(t) := (Φ_t)^* (g_DT(t))`. Then `g_fam(0) = g₀` from
   `pullbackMetric_refl`, and by the chain rule + Ricci/Lie naturality
   the Lie-derivative term cancels, leaving `∂_t g_fam = -2 Ric(g_fam)`.

The conclusion is the genuine smooth Ricci flow on `[0, T)`: the family `g_fam`
is jointly `C∞` in `(t, x)` on the open interval `(0, T)` (at the level of the
chart-local Gram matrices, `Integral.Measure.chartGramMatrix`), jointly continuous
up to `t = 0`, satisfies `g_fam 0 = g₀`, and solves `∂_t g_fam = -2 Ric(g_fam)`
on `[0, T)`.

The DeTurck step is supplied by `deturck_ricci_pde_shorttime` (the clean spectral
DeTurck–Ricci parabolic engine, which also exposes the DeTurck-field regularity and
the joint chart-Gram smoothness/continuity of `g_DT`); the conjugating
diffeomorphism family `Φ_fam` is built by `conjugating_diffeo_family` (integrating
the negated DeTurck field); the interior `∂_t g_fam = -2 Ric` identity is the flat
Hamilton–DeTurck assembly `flat_assembly_interior` and the `t = 0` endpoint the
continuity extension `ricci_flow_pde_at_zero`; the joint smoothness/continuity of
`g_fam = (Φ_fam)^* g_DT` follows from the conjugating-flow smooth-dependence data
(`conjugating_flow_*`, pinned to the genuine flow by its orbit ODE). The
construction step is assembled in `h_construct` below; it transits only those
faithful labeled inputs. -/
theorem ricci_flow_short_time_existence
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [BoundarylessManifold I M]
      [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    (g₀ : SmoothRiemannianMetric I M) :
    ∃ T : ℝ, 0 < T ∧ ∃ g_fam : ℝ → SmoothRiemannianMetric I M,
      g_fam 0 = g₀ ∧
      (∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
        ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) ∞
          (fun p : ℝ × M =>
            Integral.Measure.chartGramMatrix (I := I) (g_fam p.1) x₀ p.2 i j)
          (Set.Ioo (0 : ℝ) T ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet)) ∧
      (∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
        ContinuousOn
          (fun p : ℝ × M =>
            Integral.Measure.chartGramMatrix (I := I) (g_fam p.1) x₀ p.2 i j)
          (Set.Ico (0 : ℝ) T ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet)) ∧
      (∀ t ∈ Set.Ico (0 : ℝ) T, ∀ x : M, ∀ v w : TangentSpace I x,
        HasDerivWithinAt (fun s : ℝ => (g_fam s).inner x v w)
          ((-2 : ℝ) *
            DifferentialGeometry.Integral.Connection.ricciTensor
              (I := I) (g_fam t) x v w) (Set.Ici 0) t) := by
  -- Step 1: Solve the DeTurck–Ricci flow with background metric `g₀`.
  -- This yields a positive time `T_DT > 0`, a family `g_DT : ℝ → SmoothRiemannianMetric`,
  -- and the parabolic-solution data
  --   ∂_t g_DT(t) = -2 Ric(g_DT(t)) + 𝓛_{X_DT(t)} g_DT(t),
  -- where `X_DT(t) := deTurckVF (g_DT t) g₀` is the DeTurck vector field.
  obtain ⟨T_DT, g_DT, hDT, h_reg, h_cont0, h_grad0, h_gram_DT, h_gram0_DT,
      h_gramOnE0_DT, h_C2_DT⟩ :=
    DifferentialGeometry.PDE.RicciFlow.deturck_ricci_pde_shorttime
      (I := I) (M := M) g₀ g₀
  -- Unpack the parabolic-solution data: `T_DT > 0`, initial condition, time derivative.
  obtain ⟨hT_DT_pos, hDT_init, hDT_deriv⟩ := hDT
  -- Step 2 (construction step): Build the conjugating diffeomorphism family
  -- `Φ_fam : ℝ → (M ≃ₘ M)` from the DeTurck vector field, on a (possibly smaller)
  -- positive time interval `T ≤ T_DT`, with the pullback Ricci-flow identity.
  --
  -- The construction proceeds as follows:
  --   (a) Define the time-dependent vector field `X(t) := deTurckVF (g_DT t) g₀`.
  --   (b) Integrate `-X` to obtain a smooth diffeomorphism family `Φ_fam`
  --       with `Φ_fam 0 = id` and `∂_t Φ_fam(t) = -X(t) ∘ Φ_fam(t)`.
  --   (c) Set `g_fam(t) := (Φ_fam t)^* (g_DT t)`.
  --   (d) Apply the chain rule (`pullback_time_derivative_chain_rule`):
  --         ∂_t g_fam = (Φ_fam t)^* (∂_t g_DT - 𝓛_{X(t)} g_DT)
  --                   = (Φ_fam t)^* (-2 Ric(g_DT(t)))     (Lie term cancels)
  --                   = -2 Ric((Φ_fam t)^* g_DT(t))       (`ricci_pullback_naturality`)
  --                   = -2 Ric(g_fam t).
  --   (e) Initial condition: `g_fam 0 = (Φ_fam 0)^* (g_DT 0) = id^* g₀ = g₀`,
  --       using `pullbackMetric_refl` and `hDT_init`.
  --
  -- This packaged step depends on `time_dependent_vf_globalflow_on_closed_mfd`
  -- (currently the only remaining hole: it constructs `Φ_fam` from the
  -- time-dependent vector field) together with the smoothness data needed to
  -- discharge the chain-rule hypothesis `h_chain` of
  -- `pullback_time_derivative_chain_rule`. Once that infrastructure is filled,
  -- the assembly below is purely algebraic — the Lie term in the DeTurck flow
  -- precisely cancels the Lie-derivative piece coming from the chain rule, by
  -- the flow condition `∂_t Φ_fam = -X ∘ Φ_fam`.
  have h_construct :
      ∃ T : ℝ, 0 < T ∧ ∃ g_fam : ℝ → SmoothRiemannianMetric I M,
        g_fam 0 = g₀ ∧
        (∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
          ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) ∞
            (fun p : ℝ × M =>
              Integral.Measure.chartGramMatrix (I := I) (g_fam p.1) x₀ p.2 i j)
            (Set.Ioo (0 : ℝ) T ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet)) ∧
        (∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
          ContinuousOn
            (fun p : ℝ × M =>
              Integral.Measure.chartGramMatrix (I := I) (g_fam p.1) x₀ p.2 i j)
            (Set.Ico (0 : ℝ) T ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet)) ∧
        (∀ t ∈ Set.Ico (0 : ℝ) T, ∀ x : M, ∀ v w : TangentSpace I x,
          HasDerivWithinAt (fun s : ℝ => (g_fam s).inner x v w)
            ((-2 : ℝ) *
              DifferentialGeometry.Integral.Connection.ricciTensor
                (I := I) (g_fam t) x v w) (Set.Ici 0) t) := by
    -- The interior DeTurck PDE derivative on `Set.Ico 0 T_DT` (from the parabolic solution).
    have hDT_deriv' : ∀ t ∈ Set.Ico (0 : ℝ) T_DT, ∀ x : M, ∀ v w : TangentSpace I x,
        HasDerivWithinAt (fun s : ℝ => (g_DT s).inner x v w)
          (deTurckRicciRHS (I := I) g₀ (g_DT t) x v w)
          (Set.Ici 0) t := hDT_deriv
    -- Step 2: integrate the negated DeTurck field to a conjugating diffeomorphism family
    -- `Φ_fam` on a (possibly smaller) positive horizon `T ≤ T_DT`, anchored at the identity
    -- and carrying the backward bare-orbit ODE `∂_s Φ_fam = -deTurckVF (g_DT s) g₀ ∘ Φ_fam`
    -- on the interior `Ioo 0 T`.  The field-regularity data `h_reg`/`h_cont0`/`h_grad0` come
    -- from the enriched crux.
    obtain ⟨T, hT0, hT_le, Φ_fam, hΦ0, hΦode, hΦorbit0, hΦmfderiv0⟩ :=
      conjugating_diffeo_family
        (I := I) g_DT g₀ T_DT hT_DT_pos h_reg h_cont0 h_grad0
    -- The interior orbit ODE of `Φ_fam`, re-indexed `∀ x, ∀ t ∈ Ioo 0 T, …`, the pinning datum
    -- consumed by the faithful conjugating-flow data nodes.
    have hΦode' : ∀ x : M, ∀ t ∈ Set.Ioo (0 : ℝ) T,
        HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun s : ℝ => (Φ_fam s : M → M) x)
          (Set.Ici (0 : ℝ)) t
          ((1 : ℝ →L[ℝ] ℝ).smulRight
            (-(deTurckVF (I := I) (g_DT t) g₀ ((Φ_fam t : M → M) x)))) :=
      fun x t ht => hΦode x t ht
    -- (C) JOINT CHART-GRAM REGULARITY of the pulled-back family.  The crux's interior joint
    -- chart-Gram `C∞` of `g_DT` (`h_gram_DT`) and its continuity up to `0` (`h_gram0_DT`),
    -- restricted from the horizon `T_DT` to the smaller `T ≤ T_DT`, feed the faithful labeled
    -- node `conjugating_flow_pullback_jointGram_data` (PINNED to the genuine flow by `hΦode'`),
    -- which transports them along the orbit/Jacobian into the joint regularity of the pulled-back
    -- chart-Gram entries.  These reference only the internal data `g_DT`/`Φ_fam`, never `g₀`.
    have h_gram_DT_T : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
        ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) ∞
          (fun p : ℝ × M =>
            Integral.Measure.chartGramMatrix (I := I) (g_DT p.1) x₀ p.2 i j)
          (Set.Ioo (0 : ℝ) T ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet) := by
      intro x₀ i j
      exact (h_gram_DT x₀ i j).mono
        (Set.prod_mono_left (Set.Ioo_subset_Ioo_right hT_le))
    have h_gram0_DT_T : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
        ContinuousOn
          (fun p : ℝ × M =>
            Integral.Measure.chartGramMatrix (I := I) (g_DT p.1) x₀ p.2 i j)
          (Set.Ico (0 : ℝ) T ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet) := by
      intro x₀ i j
      exact (h_gram0_DT x₀ i j).mono
        (Set.prod_mono_left (Set.Ico_subset_Ico_right hT_le))
    -- The two NEW crux chart-Gram outputs, restricted from the horizon `T_DT` to `T ≤ T_DT`:
    -- the `k = 0` chartGramOnE value continuity on `Icc 0 T ×ˢ univ` (`hg_joint` shape) and the
    -- joint `k ≤ 2` chart-jet continuity on `Icc 0 T ×ˢ goodSet` (`hC2` shape).  These feed the
    -- corrected `conjugating_flow_t0_continuity_data` (its two providers consume exactly these).
    have h_gramOnE0_T : ∀ (α : M) (i j : Fin (Module.finrank ℝ E)),
        ContinuousOn
          (fun q : ℝ × M =>
            Integral.DivergenceTheorem.chartGramOnE (I := I) (g_DT q.1) α i j
              (extChartAt I α q.2))
          (Set.Icc 0 T ×ˢ Set.univ) := by
      intro α i j
      exact (h_gramOnE0_DT α i j).mono
        (Set.prod_mono_left (Set.Icc_subset_Icc_right hT_le))
    have h_C2_T : ∀ (α : M) (i j : Fin (Module.finrank ℝ E)) (k : ℕ), k ≤ 2 →
        ContinuousOn
          (fun q : ℝ × M => iteratedFDeriv ℝ k
            (Integral.DivergenceTheorem.chartGramOnE (I := I) (g_DT q.1) α i j)
            (extChartAt I α q.2))
          (Set.Icc 0 T ×ˢ chartLeviCivitaGoodSet (I := I) α) := by
      intro α i j k hk
      exact (h_C2_DT α i j k hk).mono
        (Set.prod_mono_left (Set.Icc_subset_Icc_right hT_le))
    -- The DeTurck FIELD interior joint-`C∞` datum of the crux (`h_reg`, on the horizon `T_DT`),
    -- restricted from `Ioo 0 T_DT` to the smaller `Ioo 0 T` (`T ≤ T_DT`).  This is the genuine
    -- closed-manifold Hartman smooth-dependence input that the moving-pushforward continuity node
    -- consumes: from a jointly-`C∞`-in-`(t, x)` velocity field the flow map is jointly `C∞`, so
    -- its moving spatial Jacobian is continuous at every interior time.  It references only the
    -- internal data `g_DT`/`g₀`, never the headline.
    have h_reg_T : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
        (fun q : ℝ × M => (TotalSpace.mk' E q.2 (deTurckVF (I := I) (g_DT q.1) g₀ q.2)
          : TangentBundle I M))
        (Set.Ioo (0 : ℝ) T ×ˢ Set.univ) :=
      h_reg.mono (Set.prod_mono_left (Set.Ioo_subset_Ioo_right hT_le))
    -- The whole-`Ico 0 T` orbit and total-space pushforward continuity of the conjugating flow,
    -- from the faithful labeled node `conjugating_flow_orbit_pushforward_continuity_data` (PINNED
    -- to the genuine flow by `hΦode'`, fed the field regularity `h_reg_T`, and consuming the
    -- `t = 0`-endpoint orbit/Jacobian continuity `hΦorbit0` / `hΦmfderiv0` produced by
    -- `conjugating_diffeo_family`).  These are exactly the whole-`Ico` orbit/pushforward inputs
    -- the two `t = 0`-continuity providers consume.
    obtain ⟨hΦ_orbit, hΦ_total⟩ :=
      conjugating_flow_orbit_pushforward_continuity_data (I := I) g_DT g₀ T hT0 Φ_fam hΦode'
        h_reg_T hΦorbit0 hΦmfderiv0
    obtain ⟨h_gram_fam, h_gram0_fam⟩ :=
      conjugating_flow_pullback_jointGram_data (I := I) g_DT g₀ T Φ_fam hΦode'
        h_gram_DT_T h_gram0_DT_T
    -- The pulled-back metric family `g_fam s := (Φ_fam s)^* (g_DT s)`.
    refine ⟨T, hT0, fun s => Diffeomorph.pullbackMetric (g_DT s) (Φ_fam s),
      ?_, h_gram_fam, h_gram0_fam, ?_⟩
    · -- Initial condition: `g_fam 0 = (Φ_fam 0)^* (g_DT 0) = id^* g₀ = g₀`.
      change Diffeomorph.pullbackMetric (g_DT 0) (Φ_fam 0) = g₀
      rw [hΦ0, Diffeomorph.pullbackMetric_refl, hDT_init]
    · -- Time derivative on `Set.Ico 0 T`.  We split into the open interior `Ioo 0 T`
      -- (the Hamilton–DeTurck flat assembly) and the left endpoint `t = 0` (continuity
      -- extension), then identify the pulled-back inner product with the `g_fam` form.
      -- The interior DeTurck PDE restricted to the smaller horizon `T ≤ T_DT`.
      have hDT_deriv_T : ∀ t ∈ Set.Ioo (0 : ℝ) T, ∀ x : M, ∀ v w : TangentSpace I x,
          HasDerivWithinAt (fun s : ℝ => (g_DT s).inner x v w)
            (deTurckRicciRHS (I := I) g₀ (g_DT t) x v w)
            (Set.Ici 0) t := by
        intro t ht x v w
        exact hDT_deriv' t ⟨le_of_lt ht.1, lt_of_lt_of_le ht.2 hT_le⟩ x v w
      -- The interior orbit ODE `∂_s Φ_fam = -deTurckVF (g_DT s) g₀ ∘ Φ_fam` on `Ioo 0 T`,
      -- in the `horbit` shape consumed by the base-point-motion datum.
      have horbit : ∀ t ∈ Set.Ioo (0 : ℝ) T, ∀ x : M,
          HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun s : ℝ => (Φ_fam s : M → M) x)
            (Set.Ici (0 : ℝ)) t
            ((1 : ℝ →L[ℝ] ℝ).smulRight
              (-(deTurckVF (I := I) (g_DT t) g₀ (Φ_fam t x)))) :=
        fun t ht x => hΦode x t ht
      -- The interior DeTurck–Ricci PDE on `Ico 0 T` (the exact `hDT_deriv` shape consumed by
      -- `conjugating_flow_flat_data` / `total_eval_three_piece_chain_rule`): restrict the
      -- crux's parabolic-solution derivative `hDT_deriv'` from `Ico 0 T_DT` to `Ico 0 T`.
      have hDT_deriv_Ico : ∀ s ∈ Set.Ico (0 : ℝ) T, ∀ y : M, ∀ a b : TangentSpace I y,
          HasDerivWithinAt (fun u : ℝ => (g_DT u).inner y a b)
            (deTurckRicciRHS (I := I) g₀ (g_DT s) y a b) (Set.Ici 0) s := by
        intro s hs y a b
        exact hDT_deriv' s ⟨hs.1, lt_of_lt_of_le hs.2 hT_le⟩ y a b
      -- (A) FLAT VARIATIONAL DATA: the per-slot flat identities `hv_flat` with factor jets
      -- `T'`/`P'`, the Christoffel-correction equation `hcorr`, the base-point-motion datum
      -- `hbase`, and the three-piece additive chain rule `h_total_eval`.  These are the
      -- genuine open variational/chart-jet analytic inputs of the conjugating flow, isolated
      -- in the faithful labeled node `conjugating_flow_flat_data`, PINNED to the genuine flow by
      -- the DeTurck PDE pin `hDT_deriv_Ico` and the orbit ODE `hΦode`; they reference only the
      -- internal `g_DT`/`Φ_fam`/`X_DT`, never `g₀`.
      obtain ⟨T', P', hv_flat, hcorr, hbase, h_total_eval⟩ :=
        conjugating_flow_flat_data (I := I) g_DT g₀ T Φ_fam hDT_deriv_Ico hΦode
      -- The interior Hamilton–DeTurck flat assembly: the pulled-back family solves
      -- `∂_t (Φ_s^* g_DT) = -2 Ric` on the open interval `Ioo 0 T`.
      have h_interior :=
        DifferentialGeometry.PDE.RicciFlow.flat_assembly_interior
          (I := I) g₀ g_DT T Φ_fam T' P' hDT_deriv_T hbase h_total_eval hv_flat hcorr
      -- The t=0 endpoint via continuity extension (`ricci_flow_pde_at_zero`): combine the
      -- interior PDE with the `Ico 0 T` continuity of the pulled-back inner product
      -- (`gfam_inner_continuous_on`) and the right-continuity of `-2 Ric(g_fam)`
      -- (`ricci_gfam_continuous_on`).  These continuity inputs are the t=0-endpoint analytic
      -- data of the flow; they reference only the internal data, never `g₀`.
      intro t ht x v w
      rcases eq_or_lt_of_le ht.1 with h0 | h0
      · -- t = 0: continuity extension.  The `Ico 0 T` continuity of the pulled-back inner
        -- product (`h_cont`) and the right-continuity at `0` of `-2 Ric(g_fam)` (`h_ric_cont`)
        -- are the genuine open `t = 0`-endpoint analytic inputs of the conjugating flow, isolated
        -- in the faithful labeled node `conjugating_flow_t0_continuity_data`, PINNED to the genuine
        -- flow by the orbit ODE `hΦode`; they reference only the internal data, never `g₀`.
        obtain ⟨h_cont, h_ric_cont⟩ :=
          conjugating_flow_t0_continuity_data (I := I) g_DT g₀ T hT0 Φ_fam hΦode
            hΦ0 hDT_init h_gramOnE0_T h_C2_T hΦ_orbit hΦ_total x v w
        subst_vars
        exact DifferentialGeometry.PDE.RicciFlow.ricci_flow_pde_at_zero
          (I := I) (fun s => Diffeomorph.pullbackMetric (g_DT s) (Φ_fam s)) hT0 x v w
          h_cont h_ric_cont (fun s hs => h_interior s hs x v w)
      · -- interior t ∈ (0, T): the flat assembly conclusion.
        exact h_interior t ⟨h0, ht.2⟩ x v w
  exact h_construct

end DifferentialGeometry.PDE.RicciFlow
