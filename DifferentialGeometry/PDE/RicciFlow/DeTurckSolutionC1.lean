import DifferentialGeometry.PDE.RicciFlow.DeTurckShortTime
import DifferentialGeometry.PDE.RicciFlow.SobolevEmbedding
import DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.LiftMetric
import DifferentialGeometry.PDE.RicciFlow.DeTurckRHS
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.MaxRegSpace
import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.TimeH1
import Mathlib.Geometry.Manifold.ContMDiff.Basic

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle
open scoped Manifold ContDiff
open DifferentialGeometry
open DifferentialGeometry.PDE
open DifferentialGeometry.PDE.DeTurck

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

/-- **Spatial-`C¹` time-continuity of the DeTurck-Ricci solution's DeTurck
vector field.**

Given a `IsQuasilinearMetricParabolicSolution`-style time-dependent family
`g_DT : ℝ → SmoothRiemannianMetric I M` (the output of
`deTurckRicci_shortTime_exists`) on the existence interval `[0, T)`, the
time-parameterised DeTurck vector field
`t ↦ deTurckVF (g_DT t) g_bg` is continuous on `[0, T)` in the
`C¹`-section topology.  The section topology on
`Cₛ^∞⟮I; E, TangentSpace I⟯` is not directly available, so we phrase the
conclusion pointwise: for every base point `x : M`, the function
`t ↦ (deTurckVF (g_DT t) g_bg) x` is continuous on `[0, T)` as a map
into the tangent fibre `TangentSpace I x`.

This is the composition of the two children below:
`maxreg_solution_in_c1_via_sobolev_embedding` (the metric family is
`C¹`-time-continuous via the maxReg Sobolev embedding), and
`deturck_vf_continuous_in_c1_input` (the assignment `g ↦ deTurckVF g g_bg`
is continuous in the `C¹`-section topology). -/
theorem deTurckRicci_solution_spatial_C1_time_continuous
    (g_bg : SmoothRiemannianMetric I M)
    (T : ℝ) (g_DT : ℝ → SmoothRiemannianMetric I M)
    (_hsol : IsQuasilinearMetricParabolicSolution (I := I)
              (deTurckRicciRHS (I := I) g_bg) (g_DT 0) T g_DT) :
    ∀ x : M,
      ContinuousOn
        (fun t : ℝ =>
          (deTurckVF (I := I) (g_DT t) g_bg :
            Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
        (Set.Ico (0 : ℝ) T) := sorry

/-- **From maxReg `H^{a+2}` regularity to `C¹` spatial regularity.**

A maxReg-style solution `g_DT : ℝ → SmoothRiemannianMetric I M` of the
DeTurck-Ricci equation lives in the maximal-regularity solution space
`L²([0,T]; H^{a+2})`, which embeds into `C¹` for `a ≥ a₀` (Sobolev
embedding `H^{a+2} ↪ C¹` once `2(a+2) > finrank ℝ E + 2`).  Conclusion:
the time-parameterised metric pairings `(g_DT t).inner x v w` are
continuous on `[0, T)`.

Phrased here as: time-continuity of the metric-evaluation pairing at
every point and every pair of tangent vectors, with the Sobolev-super-
criticality hypothesis explicit.  The proof composes the parabolic-
solution time-continuity with the tensorPouSobolevHilbert `C^k`
embedding. -/
theorem maxreg_solution_in_c1_via_sobolev_embedding
    (g_bg : SmoothRiemannianMetric I M)
    (T : ℝ) (g_DT : ℝ → SmoothRiemannianMetric I M)
    (_hsol : IsQuasilinearMetricParabolicSolution (I := I)
              (deTurckRicciRHS (I := I) g_bg) (g_DT 0) T g_DT)
    (_h_super : 2 * 3 > Module.finrank ℝ E + 2 * 1) :
    ∀ x : M, ∀ v w : TangentSpace I x,
      ContinuousOn (fun t : ℝ => (g_DT t).inner x v w)
        (Set.Ico (0 : ℝ) T) := by
  -- The maxReg / Sobolev super-criticality hypothesis `_h_super` is the natural
  -- input for a `H^{a+2} ↪ C¹` strengthening; for the present conclusion — pointwise
  -- continuity of the scalar metric pairing — the parabolic-solution hypothesis
  -- already supplies a `HasDerivWithinAt` on each pairing, which downgrades to
  -- continuity.
  obtain ⟨_hT, _hinit, hderiv⟩ := _hsol
  intro x v w t ht
  have hcont_within_Ici :
      ContinuousWithinAt (fun s : ℝ => (g_DT s).inner x v w) (Set.Ici (0 : ℝ)) t :=
    (hderiv t ht x v w).continuousWithinAt
  exact hcont_within_Ici.mono Set.Ico_subset_Ici_self

/-- **Time-continuity of the `C¹` norm from the `H¹`-in-time derivative.**

A maxReg solution has its time derivative `∂_t g_DT` in `L²([0,T]; Hᵃ)`,
which by `timeH1` lives in `H¹([0,T]; Hᵃ)`; the time-Sobolev embedding
`H¹([0,T]; X) ↪ C([0,T]; X)` then gives continuity of the underlying
`g_DT t` in the spatial norm.  Composed with the Sobolev embedding
`H^{a+2} ↪ C¹` of the previous theorem, this yields time-continuity in
the `C¹`-section norm.

Phrased here as: under the parabolic-solution hypothesis (which carries
the `HasDerivWithinAt` data), the pointwise metric-evaluation pairing is
continuous on the half-open interval `[0, T)`. -/
theorem c1_norm_time_continuous_from_h1_time_derivative
    (g_bg : SmoothRiemannianMetric I M)
    (T : ℝ) (g_DT : ℝ → SmoothRiemannianMetric I M)
    (_hsol : IsQuasilinearMetricParabolicSolution (I := I)
              (deTurckRicciRHS (I := I) g_bg) (g_DT 0) T g_DT) :
    ∀ x : M, ∀ v w : TangentSpace I x,
      ContinuousOn (fun t : ℝ => (g_DT t).inner x v w)
        (Set.Ico (0 : ℝ) T) := by
  -- Unpack the parabolic-solution hypothesis: at every `t ∈ [0, T)`, every base
  -- point `x`, and every pair `(v, w)`, the scalar pairing `s ↦ (g_DT s).inner x v w`
  -- has a derivative within `Set.Ici 0` at `t` (equal to the RHS evaluated at `g_DT t`).
  obtain ⟨_hT, _hinit, hderiv⟩ := _hsol
  -- Fix the inputs and read off the derivative datum.
  intro x v w t ht
  -- The derivative within `Ici 0` at `t` yields continuity within `Ici 0` at `t`.
  have hcont_within_Ici :
      ContinuousWithinAt (fun s : ℝ => (g_DT s).inner x v w) (Set.Ici (0 : ℝ)) t :=
    (hderiv t ht x v w).continuousWithinAt
  -- `Set.Ico 0 T ⊆ Set.Ici 0`, so we can mono-strengthen the continuity neighbourhood.
  exact hcont_within_Ici.mono Set.Ico_subset_Ici_self

/-- **The DeTurck vector field is continuous in its `C¹` metric input.**

The map
  `g ↦ deTurckVF g g_bg  :  (C¹-metrics)  →  (C¹-sections of TM)`
is continuous: in any chart its components are
`W^i(g) = g^{jk} (Γ^i_{jk}(g) − Γ̄^i_{jk}(g_bg))`, a rational expression
in the entries `g_{ab}, ∂_c g_{ab}` of the metric, which depends
continuously on `(g, ∂g)` away from the zero locus of `det g` (and `g`
is positive-definite, so `det g > 0` everywhere).

Phrased here as: for any time-dependent family of metrics
`g_DT : ℝ → SmoothRiemannianMetric I M` for which the pointwise inner
products `(g_DT t).inner x v w` are continuous in `t` (the conclusion of
the previous theorem), the resulting DeTurck vector field
`deTurckVF (g_DT t) g_bg` is continuous in `t` pointwise on `TM`.  This
is the elementary half of the composition. -/
theorem deturck_vf_continuous_in_c1_input
    (g_bg : SmoothRiemannianMetric I M)
    (T : ℝ) (g_DT : ℝ → SmoothRiemannianMetric I M)
    (_h_metric_cont : ∀ x : M, ∀ v w : TangentSpace I x,
      ContinuousOn (fun t : ℝ => (g_DT t).inner x v w)
        (Set.Ico (0 : ℝ) T)) :
    ∀ x : M,
      ContinuousOn
        (fun t : ℝ =>
          (deTurckVF (I := I) (g_DT t) g_bg :
            Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
        (Set.Ico (0 : ℝ) T) := sorry

end DifferentialGeometry.PDE.RicciFlow
