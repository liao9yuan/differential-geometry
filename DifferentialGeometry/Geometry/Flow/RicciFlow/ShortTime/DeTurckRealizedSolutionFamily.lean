import DifferentialGeometry.Analysis.Parabolic.DeTurckRicci.QuasilinearMetricShortTimeExistence
import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.TensorHsRealize
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.DeTurckRicciRHSSymmetric
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.DeTurckChartRegularityFromJoint
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.MildSolutionTimeH1

/-! # The realized DeTurck–Ricci solution family

The spectral maximal-regularity engine `deturck_mildsolution_timeh1` produces the
strong (`timeH1`) Duhamel solution `u` of the DeTurck–Ricci flow linearized about the
background, as a path in the tensor Sobolev scale `tensorHs g₀ 0 2 a`.  The interior
parabolic smoothing (`solField_into_all_tensorHs_interior`) places `u t` in `⋂_σ Hˢ`
for every interior time `t`, so — granting the smooth-representative gate
`SpectralSmoothRealizesAsSmooth` — each `u t` has a genuine `C∞` representative
`T_rep t : SmoothCcTensor g₀ 0 2`.  Realizing that representative as a metric
perturbation through `tensorSectionRealizeMetric g₀ (T_rep t)` produces the metric
family `g_DT t`, and the parabolic interior regularity makes the chart-Gram entries
jointly smooth.

This file packages the genuinely-deep classical analytic content as one named honest
input `realizedDeTurckFamily_exists` — the realized metric family `g_DT` together with
its representative family `T_rep`, the realize relation pinning the two, the
DeTurck–Ricci flow derivative, and the joint chart-Gram smoothness — from which the
master `deTurckRicci_solution_with_jointReg` (file `DeTurckInitialDataExistence.lean`)
assembles the `IsQuasilinearMetricParabolicSolution` flow by transporting the
perturbation-part derivative through the constant initial term.

The `sorry` carried by `realizedDeTurckFamily_exists` is the deferred classical input
(quasilinear strictly-parabolic short-time existence with interior regularity, in the
realized-representative form); consumers transitively depend on `sorryAx`. -/

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle
open scoped Manifold ContDiff NNReal ENNReal Topology BigOperators
open DifferentialGeometry
open DifferentialGeometry.PDE
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [BoundarylessManifold I M]
      [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

/-- **HONEST CLASSICAL INPUT — realized strictly-parabolic DeTurck–Ricci solution
family.**

For an initial metric `g₀` and a background metric `g_bg` on a closed Riemannian
manifold there are a positive time `T`, a metric family
`g_DT : ℝ → SmoothRiemannianMetric I M`, and a family of smooth compactly-supported
`(0,2)`-tensor representatives `T_rep : ℝ → SmoothCcTensor g₀ 0 2` such that:

* `g_DT 0 = g₀` — the family starts at the initial metric;
* `(g_DT t).inner = g₀.inner + ccTensorBilinSymm g₀ (T_rep t)` — `g_DT t` is the
  realize of the representative `T_rep t` as a metric perturbation of `g₀` (the
  realize relation, pinning `g_DT` to `T_rep`);
* the perturbation solves the DeTurck–Ricci flow: at every interior time
  `t ∈ [0, T)`, base point `x` and tangent pair `(v, w)`, the time-derivative of
  `s ↦ ccTensorBilinSymm g₀ (T_rep s) x v w` (the perturbation part of the realized
  inner product) within `[0, ∞)` equals the DeTurck–Ricci right-hand side
  `deTurckRicciRHS g_bg (g_DT t) x v w`;
* the chart-Gram entries of `g_DT` are jointly `C∞` up to `t = 0`
  (`JointChartGramSmooth`).

This is the classical quasilinear strictly-parabolic short-time existence with interior
regularity (Chow–Knopf, DeTurck's Step 1; Lieberman; Ladyzhenskaya–Solonnikov–Uraltseva;
Amann maximal regularity), expressed at the level of the `C∞` interior representatives
through which the metric family is realized.  The representative family is the spectral
maximal-regularity Duhamel solution of the flow linearized about `g₀`, smoothed in the
interior and lifted to `C∞` sections through the smooth-representative gate.

The metric family `g_DT` is presented directly, together with the representative
family `T_rep` and the realize relation `(g_DT t).inner = g₀.inner + ccTensorBilinSymm
g₀ (T_rep t)` that pins it to `T_rep` (so the conjuncts are non-vacuous and
solution-pinned: a degenerate `g_DT ≡ g₀` is excluded because it would force
`ccTensorBilinSymm g₀ (T_rep t) = 0` for all `t`, contradicting a non-trivial flow).
The data conjuncts are: the initial value `g_DT 0 = g₀` (the representative starts at
`0`), the realize relation, the DeTurck–Ricci flow derivative at every interior time,
and the joint chart-Gram smoothness up to `t = 0`.

The `sorry` is the deferred classical analytic existence; consumers transitively
depend on `sorryAx`. -/
theorem realizedDeTurckFamily_exists
    (g₀ g_bg : SmoothRiemannianMetric I M) :
    ∃ (T : ℝ) (g_DT : ℝ → SmoothRiemannianMetric I M)
        (T_rep : ℝ → SmoothCcTensor g₀ 0 2),
      0 < T ∧
      g_DT 0 = g₀ ∧
      (∀ (t : ℝ) (x : M) (v w : TangentSpace I x),
        (g_DT t).inner x v w =
          g₀.inner x v w + ccTensorBilinSymm (I := I) g₀ (T_rep t) x v w) ∧
      (∀ t ∈ Set.Ico (0 : ℝ) T, ∀ x : M, ∀ v w : TangentSpace I x,
        HasDerivWithinAt
          (fun s : ℝ => ccTensorBilinSymm (I := I) g₀ (T_rep s) x v w)
          (deTurckRicciRHS (I := I) g_bg (g_DT t) x v w)
          (Set.Ici 0) t) ∧
      JointChartGramSmooth (I := I) T g_DT :=
  sorry

end DifferentialGeometry.PDE.RicciFlow
