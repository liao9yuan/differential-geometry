import DifferentialGeometry.Analysis.Parabolic.DeTurckRicci.QuasilinearMetricShortTimeExistence
import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.TensorHsRealize
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.SobolevNonlinearityExistence
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckQuasilinearExistence
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.DeTurckRicciRHSSymmetric
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.DeTurckChartRegularityFromJoint
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.MildSolutionTimeH1
import DifferentialGeometry.Analysis.Spectral.Intrinsic.HeatSemigroup.SpectralSmoothRepresentativeRealize
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.PointwiseSpectralCoordinate
import DifferentialGeometry.Analysis.Spectral.Intrinsic.PointwiseDeriv

/-! # Jointly-smooth representative of the maximal-regularity DeTurck–Ricci solution

For the genuine second-order quasilinear spectral maximal-regularity Duhamel solution `u`
of the Ricci–DeTurck flow linearized about a closed background metric `g₀` — the Duhamel
image of its own genuinely-second-order Nemytskii forcing `gforce`, with zero initial
perturbation and trace `0` at `t = 0` — the smooth-initial-data parabolic solution is
**jointly `C∞` in `(t, x)` up to `t = 0`**.

This is the single classical parabolic-regularity fact behind the realized DeTurck–Ricci
family (Chow–Knopf, DeTurck's Step 1; Ladyzhenskaya–Solonnikov–Uraltseva; Amann maximal
regularity; the interior parabolic smoothing carried up to the smooth initial datum).  It
packages, on a positive smallness horizon `T₁ ≤ T`, a **single time-regular** family of
`C∞` representatives `F : ℝ → SmoothCcTensor g₀ 0 2` (uniformly `g₀`-fibre small with one
constant `δ < 1`) that carries simultaneously:

* `F 0 = 0` — the family starts at the zero initial perturbation;
* the interior `L²` pin tying `F t` to the solution value `u.toFun t` on the closed slab;
* the **Ricci–DeTurck flow derivative**: at every `t ∈ Ico 0 T₁`, base point `x`, and
  tangent pair `(v, w)`, the pointwise `[0, ∞)`-derivative of the perturbation part of the
  realized inner product `s ↦ ccTensorBilinSymm g₀ (F s) x v w` equals the intrinsic
  Ricci–DeTurck right-hand side `deTurckRicciRHS g_bg (g_DT t) x v w`, where
  `g_DT t = tensorSectionRealizeMetric g₀ (F t) hδ_lt (hδ t)`;
* the **joint chart-Gram interior regularity** `JointChartGramSmooth T₁ g_DT` — the
  chart-Gram entries of the realized metric family are jointly `C∞` up to `t = 0`.

The flow derivative is the classical pointwise reading of the maximal-regularity
`L²`-time-derivative of `u` (`maxRegDuhamelMap_timeDeriv_eq`, the connection Laplacian plus
the forcing, transported by `maxreg_l2deriv_to_pointwise_hasderivwithinat`), composed with
the supercritical-order-bounded chart-evaluation functional, realized pointwise to the
intrinsic Ricci–DeTurck remainder; the joint regularity is the standard parabolic interior
smoothing of the smooth initial datum read through the chart-Gram extraction.  The two are
NOT consequences of an `L²`-class pin plus `L²`-time continuity alone (the family must be
the genuinely smooth solution); the single hypothesis-set `hduh`/`hforce`/`htrace` pins the
family to the genuine engine solution `u`, so the statement is non-vacuous.

DEFERRED (honest `sorry`; consumers transitively depend on `sorryAx`).  This is the
recursion frontier — the genuine classical smooth-initial-data parabolic joint regularity,
to be discharged on its own. -/

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
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [BoundarylessManifold I M]
      [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

/-- **Jointly-smooth representative of the maximal-regularity DeTurck–Ricci solution
(the single deep classical parabolic-regularity leaf).**

For the genuine maximal-regularity Duhamel solution `u` of the Ricci–DeTurck flow about
`g₀` (the Duhamel image of its own forcing `gforce`, reproducing `deTurckSobolevNHa2`
a.e. along the order-`(a+2)` Duhamel field, with zero initial perturbation and trace `0`
at `t = 0`), there is a positive smallness horizon `T₁ ≤ T` and a single time-regular
family of `C∞` representatives `F`, uniformly `g₀`-fibre small with one `δ < 1`, that
carries the zero initial value, the interior `L²` pin to `u.toFun`, the intrinsic
Ricci–DeTurck pointwise flow derivative, and the joint chart-Gram interior regularity of
the realized metric family.  This is the classical smooth-initial-data parabolic joint
`C∞`-up-to-`t = 0` regularity.

DEFERRED (honest `sorry`; consumers transitively depend on `sorryAx`). -/
theorem maxreg_solution_jointly_smooth_representative
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) (ha_even : Even a)
    (ha_eq : a = 2 * Module.finrank ℝ E + 10)
    {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (hTT₀ : T ≤ (deTurckRicci_quasilinear_maxreg_solution
      (I := I) (M := M) g₀ g_bg a ha_super ha_even).choose)
    (u : MaxRegSolutionSpace (I := I) (M := M) (a : ℝ) T)
    (gforce : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T)
    (hduh : u = maxRegDuhamelMap (I := I) (M := M) (a : ℝ) hT hT1
      (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce)
    (hforce : gforce =ᵐ[timeMeasure T]
      (fun t => deTurckSobolevNHa2 (I := I) (M := M) g₀ g_bg a
        (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
          (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t)))
    (htrace : timeH1.trace0 _ T u = 0) :
    ∃ (T₁ : ℝ), 0 < T₁ ∧ T₁ ≤ T ∧
      ∃ (F : ℝ → SmoothCcTensor g₀ 0 2) (δ : ℝ) (hδ_lt : δ < 1)
        (hδ : ∀ t : ℝ, gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ (F t)) δ),
      F 0 = 0 ∧
      (∀ t ∈ Set.Icc (0 : ℝ) T₁,
        SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) (F t) =
          tensorHsToL2 (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
            (Nat.cast_nonneg a) (timeH1.toFun u t)) ∧
      (∀ t ∈ Set.Ico (0 : ℝ) T₁, ∀ x : M, ∀ v w : TangentSpace I x,
        HasDerivWithinAt
          (fun s : ℝ => ccTensorBilinSymm (I := I) g₀ (F s) x v w)
          (deTurckRicciRHS (I := I) g_bg
            (tensorSectionRealizeMetric (I := I) g₀ (F t) hδ_lt (hδ t)) x v w)
          (Set.Ici 0) t) ∧
      JointChartGramSmooth (I := I) T₁
        (fun t : ℝ => tensorSectionRealizeMetric (I := I) g₀ (F t) hδ_lt (hδ t)) :=
  sorry

end DifferentialGeometry.PDE.RicciFlow
