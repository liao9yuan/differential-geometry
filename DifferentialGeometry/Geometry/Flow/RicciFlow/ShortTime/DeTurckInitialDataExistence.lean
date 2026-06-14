import DifferentialGeometry.Geometry.Metric.Basic
import DifferentialGeometry.Geometry.Flow.RicciFlow.DeTurckRHS

/-! # `g₀`-anchored DeTurck–Ricci interior parabolic existence

This file isolates the genuine analytic input the concrete DeTurck–Ricci
short-time existence leaf `deTurckRicci_shortTime_existence_of_closed`
(`Geometry/Flow/RicciFlow/DeTurckShortTime.lean`) consumes: existence of a
short-time DeTurck–Ricci flow whose spectral framework is anchored at the
*arbitrary* initial metric `g₀` (not at the flow background `g_bg`), so that the
flow starts exactly at `g₀` and is interior-regular up to the smooth initial
datum.

The interior-existence assembler `deturck_metric_pde_interior`
(`Geometry/Flow/RicciFlow/ShortTime/DeTurckRicciPde.lean`) couples the spectral
anchor to the flow background through a single metric argument, so it produces a
solution only for the diagonal case *anchor = background*. The headline needs the
decoupled case *anchor `g₀` ≠ background `g_bg`*; this file posits that decoupled
existence statement as the genuinely-open node. It lives upstream of the
interior/at-zero assemblers (which import the headline file), hence cannot cite
them.
-/

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle
open scoped Manifold ContDiff NNReal ENNReal Topology BigOperators
open DifferentialGeometry
open DifferentialGeometry.PDE
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.Measure

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [BoundarylessManifold I M]
      [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

/-- **`g₀`-anchored DeTurck–Ricci interior parabolic existence (genuine analytic input).**

For an arbitrary initial metric `g₀` and a flow background `g_bg` on a closed
manifold there exist a positive time `T` and a metric family `g_DT` such that:

* `g_DT 0 = g₀` (the spectral framework is anchored at `g₀`, so the perturbation
  carrier starts at zero and the flow begins exactly at the prescribed initial
  metric — this is what the realize framework anchored at `g_bg` cannot give for
  arbitrary `g₀`);
* every scalar component `s ↦ (g_DT s).inner x v w` is continuous on `[0, T]`
  (continuity up to the initial datum);
* the DeTurck–Ricci right-hand side `s ↦ deTurckRicciRHS g_bg (g_DT s) x v w`
  is continuous from the right at `t = 0`;
* on the open interior `(0, T)` the scalar components are one-sidedly
  differentiable with derivative the DeTurck–Ricci right-hand side at `g_DT t`.

This is the genuine, faithful interior parabolic-smoothing-plus-continuity input
for the strictly-parabolic, smooth-quasilinear DeTurck–Ricci flow from smooth
initial data, with the spectral framework anchored at `g₀`.

**HONEST CLASSICAL INPUT.** This is exactly the standard quasilinear strictly-parabolic
short-time existence + interior regularity that Chow–Knopf INVOKE (do not re-prove) in the
proof of Thm [Hamilton] (the DeTurck-modified flow is strictly parabolic, principal symbol
`σ[DQ](ζ) = |ζ|²·Id`; cf. Chow–Knopf, *The Ricci Flow: An Introduction*, Ch. "Short time
existence", eq. (Q-is-elliptic)). See Lieberman, *Second Order Parabolic Differential
Equations*, Ch. VIII (existence via fixed point) + interior regularity; Ladyzhenskaya–
Solonnikov–Uraltseva; Amann (maximal regularity). It is the open node;
the body is `sorry`, so consumers transitively depend on `sorryAx`.

It is **not** the short-time-existence conclusion: that conclusion is the
*one-sided derivative on the closed interval* `Ico 0 T` (including the endpoint
`t = 0`) packaged as `IsQuasilinearMetricParabolicSolution`. Here only the *open
interior* `Ioo 0 T` derivative is asserted; the endpoint `t = 0` is closed in the
consumer from the continuity certificates by the standard one-sided
derivative-limit argument. -/
theorem deturck_metric_pde_interior_at_initial
    (g₀ g_bg : SmoothRiemannianMetric I M) :
    ∃ T : ℝ, 0 < T ∧ ∃ g_DT : ℝ → SmoothRiemannianMetric I M,
      g_DT 0 = g₀ ∧
      (∀ (x : M) (v w : TangentSpace I x),
        ContinuousOn (fun s : ℝ => (g_DT s).inner x v w) (Set.Icc 0 T)) ∧
      (∀ (x : M) (v w : TangentSpace I x),
        ContinuousWithinAt
          (fun s : ℝ => deTurckRicciRHS (I := I) g_bg (g_DT s) x v w)
          (Set.Ioi 0) 0) ∧
      (∀ t ∈ Set.Ioo (0 : ℝ) T, ∀ (x : M) (v w : TangentSpace I x),
        HasDerivWithinAt (fun s : ℝ => (g_DT s).inner x v w)
          (deTurckRicciRHS (I := I) g_bg (g_DT t) x v w) (Set.Ici 0) t) :=
  sorry

end DifferentialGeometry.PDE.RicciFlow
