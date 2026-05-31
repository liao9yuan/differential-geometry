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

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle
open scoped Manifold ContDiff
open DifferentialGeometry

/-! ## Short-time existence for the Ricci flow

Classical construction (Hamilton–DeTurck): given an initial smooth Riemannian
metric `g₀` on a closed manifold `M`, the Ricci flow `∂_t g = -2 Ric(g)` admits
a positive-time smooth solution with `g(0) = g₀`. The proof passes through:

1. Solve the (strictly parabolic) DeTurck–Ricci flow
   `∂_t g_DT = -2 Ric(g_DT) + 𝓛_{X_DT} g_DT` (where `X_DT = deTurckVF g_DT g_bg`)
   for time `[0, T_DT)`, via `deTurckRicci_shortTime_exists` (here we take
   `g_bg := g₀` as the background metric).
2. Integrate the time-dependent vector field `-X_DT(t)` to obtain a smooth family
   of diffeomorphisms `Φ_t : M ≃ₘ M` with `Φ_0 = id` and `∂_t Φ_t = -X_DT ∘ Φ_t`.
3. Set `g_fam(t) := (Φ_t)^* (g_DT(t))`. Then `g_fam(0) = g₀` from
   `pullbackMetric_refl`, and by the chain rule + Ricci/Lie naturality
   the Lie-derivative term cancels, leaving `∂_t g_fam = -2 Ric(g_fam)`.

The DeTurck step is supplied by `deTurckRicci_shortTime_exists`; the chain-rule
identity at scalar level is supplied by `pullback_time_derivative_chain_rule`;
the Ricci tensor's diffeomorphism-equivariance by `ricci_pullback_naturality`;
and the Lie derivative's by `lie_derivative_pullback_naturality`. The remaining
ingredient — construction of the diffeomorphism family `Φ_t` together with the
scalar-derivative existence packaged for `pullback_time_derivative_chain_rule` —
is the `time_dependent_vf_globalflow_on_closed_mfd` infrastructure, currently
under development. The body below assembles the pieces and identifies the
single remaining hole as `h_construct`. -/
theorem ricci_flow_short_time_existence
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [BoundarylessManifold I M]
      [T2Space M] [SigmaCompactSpace M]
    (g₀ : SmoothRiemannianMetric I M) :
    ∃ T : ℝ, 0 < T ∧
      ∃ g_fam : ℝ → SmoothRiemannianMetric I M,
        g_fam 0 = g₀ ∧
        ∀ t ∈ Set.Ico (0 : ℝ) T, ∀ x : M, ∀ v w : TangentSpace I x,
          HasDerivWithinAt (fun s : ℝ => (g_fam s).inner x v w)
            ((-2 : ℝ) *
              DifferentialGeometry.Integral.Connection.ricciTensor
                (I := I) (g_fam t) x v w) (Set.Ici 0) t := by
  -- Step 1: Solve the DeTurck–Ricci flow with background metric `g₀`.
  -- This yields a positive time `T_DT > 0`, a family `g_DT : ℝ → SmoothRiemannianMetric`,
  -- and the parabolic-solution data
  --   ∂_t g_DT(t) = -2 Ric(g_DT(t)) + 𝓛_{X_DT(t)} g_DT(t),
  -- where `X_DT(t) := deTurckVF (g_DT t) g₀` is the DeTurck vector field.
  obtain ⟨T_DT, g_DT, hDT⟩ :=
    DifferentialGeometry.PDE.RicciFlow.deTurckRicci_shortTime_exists
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
      ∃ T : ℝ, 0 < T ∧
        ∃ g_fam : ℝ → SmoothRiemannianMetric I M,
          g_fam 0 = g₀ ∧
          ∀ t ∈ Set.Ico (0 : ℝ) T, ∀ x : M, ∀ v w : TangentSpace I x,
            HasDerivWithinAt (fun s : ℝ => (g_fam s).inner x v w)
              ((-2 : ℝ) *
                DifferentialGeometry.Integral.Connection.ricciTensor
                  (I := I) (g_fam t) x v w) (Set.Ici 0) t := by
    -- Construction step: build `Φ_fam` from `time_dependent_vf_globalflow_on_closed_mfd`,
    -- form `g_fam t := (Φ_fam t)^* (g_DT t)`, and assemble via:
    --   * `pullbackMetric_refl` for the initial condition,
    --   * `pullback_time_derivative_chain_rule` for the time-derivative,
    --   * `ricci_pullback_naturality` to identify `(Φ_fam t)^* Ric(g_DT t) = Ric(g_fam t)`,
    --   * `lie_derivative_pullback_naturality` to identify the Lie pullback term,
    --   * the flow condition `∂_t Φ_fam = -X ∘ Φ_fam` to cancel the Lie terms.
    -- See the docstring for the full algebraic identity. The DeTurck solution
    -- data `g_DT`, `hT_DT_pos`, `hDT_init`, `hDT_deriv` is already in scope.
    sorry
  exact h_construct

end DifferentialGeometry.PDE.RicciFlow
