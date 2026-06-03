import DifferentialGeometry.Geometry.Metric.Basic
import DifferentialGeometry.Analysis.Parabolic.DeTurckRicci.QuasilinearMetricShortTimeExistence
import DifferentialGeometry.Geometry.Flow.RicciFlow.DeTurckRHS
import DifferentialGeometry.Analysis.Parabolic.DeTurckRicci.RHSStrictParabolic
import DifferentialGeometry.Analysis.Parabolic.DeTurckRicci.RHSSmoothQuasilinear
import DifferentialGeometry.Analysis.Spectral.Intrinsic.ConnectionLaplacianMaximalRegularity
import DifferentialGeometry.Analysis.Spectral.Intrinsic.PointwiseDeriv
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.DeTurckInitialDataExistence

/-!
# Short-time existence for the Ricci–DeTurck flow

On a closed manifold, the DeTurck-modified Ricci right-hand side is strictly parabolic, so the
abstract quasilinear parabolic short-time existence theorem applies.  This file records the
resulting headline.

## Main results

* `deTurckRicci_shortTime_existence_of_closed` — for any initial metric `g₀` and background
  metric `g_bg` on a closed manifold there exist `T > 0` and a family `g_DT` solving the
  Ricci–DeTurck flow on `[0, T)` with `g_DT 0 = g₀`.
-/

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle
open scoped Manifold ContDiff
open DifferentialGeometry
open DifferentialGeometry.PDE

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

/-- **Short-time existence for the Ricci–DeTurck flow on a closed manifold.**

On a closed (compact, boundaryless) manifold `M`, for any smooth Riemannian
metric `g₀` and any background metric `g_bg`, there exist a positive time
`T > 0` and a family `g_DT : ℝ → SmoothRiemannianMetric I M` that solves the
Ricci–DeTurck flow `∂_t g = deTurckRicciRHS g_bg g` on `[0, T)` with initial
value `g_DT 0 = g₀`, in the sense of `IsQuasilinearMetricParabolicSolution`.

The right-hand side `deTurckRicciRHS g_bg g = -2 · Ric(g) + 𝓛_{W(g, g_bg)} g`
is the DeTurck-modified Ricci operator, where `W(g, g_bg)` is the DeTurck
vector field; this modification makes the otherwise only weakly-parabolic
Ricci flow strictly parabolic.

This is the genuine quasi-linear parabolic short-time existence for the concrete
DeTurck–Ricci operator. Its inputs are that `deTurckRicciRHS g_bg` is strictly
parabolic at every metric (`deTurckRicciRHS_isStrictlyParabolic_at_self`), has
smooth quasi-linear dependence on `(g, ∇g, ∇²g)`
(`deTurckRicciRHS_isSmoothQuasilinear`), and is value-symmetric
(`deTurckRicciRHS_symm` — this keeps the conclusion, a curve of symmetric metrics,
satisfiable).

The proof assembles the `IsQuasilinearMetricParabolicSolution` data from the
`g₀`-anchored interior parabolic existence input
`deturck_metric_pde_interior_at_initial`
(`Geometry/Flow/RicciFlow/ShortTime/DeTurckInitialDataExistence.lean`): that node
supplies the existence time `T`, the flow `g_DT` with `g_DT 0 = g₀`, the
continuity certificates up to `t = 0`, and the interior one-sided derivative on
`(0, T)`; this assembler closes the endpoint `t = 0` from the continuity
certificates by the standard one-sided derivative-limit argument and combines the
two into the closed-interval `Ico 0 T` statement. The interior-existence node is
the deferred classical analytic input (Banach fixed point on Duhamel iterates
seeded by the linearised analytic semigroup, anchored at the initial metric); it
remains `sorry`, so consumers transitively depend on `sorryAx`.

There is intentionally no abstract free-operator version: that statement is false
as written (the conclusion forces value-symmetry that a free operator binder does
not carry), so the existence content lives here, at the symmetric DeTurck operator. -/
theorem deTurckRicci_shortTime_existence_of_closed
    (g₀ g_bg : SmoothRiemannianMetric I M) :
    ∃ T : ℝ, ∃ g_DT : ℝ → SmoothRiemannianMetric I M,
      IsQuasilinearMetricParabolicSolution (I := I)
        (deTurckRicciRHS (I := I) g_bg) g₀ T g_DT := by
  obtain ⟨T, hT, g_DT, h0, h_cont, h_rhs_cont, h_interior⟩ :=
    deturck_metric_pde_interior_at_initial (I := I) g₀ g_bg
  refine ⟨T, g_DT, hT, h0, ?_⟩
  intro t ht x v w
  rcases eq_or_lt_of_le ht.1 with ht0 | ht0
  · -- endpoint `t = 0`: close the one-sided derivative from the continuity
    -- certificates by the standard derivative-limit argument.
    subst ht0
    set f : ℝ → ℝ := fun s : ℝ => (g_DT s).inner x v w with hf_def
    set rhs : ℝ → ℝ :=
      fun s : ℝ => deTurckRicciRHS (I := I) g_bg (g_DT s) x v w with hrhs_def
    have hHasDerivAt : ∀ t ∈ Set.Ioo (0 : ℝ) T, HasDerivAt f (rhs t) t := by
      intro t' ht'
      exact (h_interior t' ht' x v w).hasDerivAt (Ici_mem_nhds ht'.1)
    have f_diff : DifferentiableOn ℝ f (Set.Ioo (0 : ℝ) T) := by
      intro t' ht'
      exact ((hHasDerivAt t' ht').differentiableAt).differentiableWithinAt
    have f_lim : ContinuousWithinAt f (Set.Ioo (0 : ℝ) T) 0 :=
      ((h_cont x v w).continuousWithinAt (Set.left_mem_Icc.mpr hT.le)).mono
        Set.Ioo_subset_Icc_self
    have hs : Set.Ioo (0 : ℝ) T ∈ nhdsWithin (0 : ℝ) (Set.Ioi 0) := Ioo_mem_nhdsGT hT
    have hEqOn : Set.EqOn rhs (fun x => deriv f x) (Set.Ioo (0 : ℝ) T) := by
      intro t' ht'
      exact ((hHasDerivAt t' ht').deriv).symm
    have f_lim' : Filter.Tendsto (fun x => deriv f x) (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (nhds (deTurckRicciRHS (I := I) g_bg (g_DT 0) x v w)) := by
      have h_rhs_tendsto : Filter.Tendsto rhs (nhdsWithin (0 : ℝ) (Set.Ioi 0))
          (nhds (deTurckRicciRHS (I := I) g_bg (g_DT 0) x v w)) := h_rhs_cont x v w
      exact h_rhs_tendsto.congr' (hEqOn.eventuallyEq_of_mem hs)
    exact hasDerivWithinAt_Ici_of_tendsto_deriv f_diff f_lim hs f_lim'
  · -- interior `0 < t < T`
    exact h_interior t ⟨ht0, ht.2⟩ x v w

end DifferentialGeometry.PDE.RicciFlow
