import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.UnifClassBounds

/-!
# The background-aware order-one solve package at one explicit packet

`IsLowSolveAt` (`ShortTime/UnifClassBounds.lean`) packages the diagonal
order-one solve -- the Ricci--DeTurck contraction run at `g₀` against itself --
at one explicit witness tuple.  The route-(c) widening (`ROUTE_C_PLAN.md`,
brick 1) reruns the rung chain with the DeTurck background freed to `g_bg`,
and the canonical two-metric inputs already exist: `LowRegBoundData` carries
the six numbers and the fibre threshold, `IsLowBoundsAt` the analytic
certificates at `(g₀, g_bg)`, and `IsLowSolveBg` the fixed-point output.

This file bundles those pieces, together with the closed-horizon cap in the
shape `lowreg_sol_of_data` consumes and the external radius cap, into the
single solve package `IsBgSolveAt` that the background rung chain takes as
input.  The lemmas in the `IsBgSolveAt` namespace project the bundle onto the
statements of `IsLowSolveAt`'s fields with the background slot freed to
`g_bg`, under the same names, so the downstream rung mirrors port
near-verbatim from the diagonal.
-/

noncomputable section

open Bundle Manifold MeasureTheory Set
open scoped Manifold Topology ContDiff ENNReal NNReal InnerProductSpace

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

/-- **The background-aware order-one solve package at one explicit packet.**

Background sibling of `IsLowSolveAt`.  Instead of restating the seventeen
diagonal fields it bundles the canonical two-metric pieces: the analytic
certificates `bounds : IsLowBoundsAt g₀ g_bg K`, the fixed-point output
`solve : IsLowSolveBg` for the solution `u` with forcing `gforce`, the
closed-horizon cap `hTτ` in the six-number shape that `lowreg_sol_of_data`
consumes, and the external radius cap `hcap` relating the closed state radius
to `Rcap`.  A producer that has run `lowreg_sol_of_data` on a horizon below
`lowregHorizon` obtains every field for free.  The projection lemmas in the
`IsBgSolveAt` namespace recover the diagonal field statements with the
DeTurck slot freed to `g_bg`. -/
structure IsBgSolveAt (g₀ g_bg : SmoothRiemannianMetric I M)
    (K : LowRegBoundData) {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (u : MaxRegSolutionSpace (I := I) (M := M) ((1 : ℕ) : ℝ) T)
    (gforce : timeL2
      (tensorHs (I := I) (M := M) g₀ 0 2 ((1 : ℕ) : ℝ)) T)
    (Rcap : ℝ) : Prop where
  /-- The analytic certificates of the packet `K` at `(g₀, g_bg)`. -/
  bounds : IsLowBoundsAt (I := I) (M := M) g₀ g_bg K
  /-- The fixed-point output for the solution `u` with forcing `gforce`. -/
  solve : IsLowSolveBg (I := I) (M := M) g₀ g_bg K bounds hT hT1 u gforce
  /-- The horizon is below the closed existence time of the packet `K`. -/
  hTτ : T ≤ lowregHorizon K.top K.base K.slope K.zeroBd K.outer K.realize
  /-- The closed state radius of the packet `K` is below the external cap. -/
  hcap : lowregStateRad K.top K.slope K.outer K.realize ≤ Rcap

namespace IsBgSolveAt

variable {g₀ g_bg : SmoothRiemannianMetric I M} {K : LowRegBoundData}
  {T : ℝ} {hT : 0 < T} {hT1 : T ≤ 1}
  {u : MaxRegSolutionSpace (I := I) (M := M) ((1 : ℕ) : ℝ) T}
  {gforce : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 ((1 : ℕ) : ℝ)) T}
  {Rcap : ℝ}

/-- The fibre threshold is below one; supplied by the packet `K` itself and
stated on the bundle so diagonal ports read verbatim. -/
theorem hδ (_h : IsBgSolveAt (I := I) (M := M) g₀ g_bg K hT hT1 u gforce Rcap) :
    K.threshold < 1 :=
  K.threshold_lt

/-- The top-arm coefficient is nonnegative; supplied by the packet `K`. -/
theorem hCtop
    (_h : IsBgSolveAt (I := I) (M := M) g₀ g_bg K hT hT1 u gforce Rcap) :
    0 ≤ K.top :=
  K.top_nonneg

/-- The high-size arm coefficient is nonnegative; supplied by the packet
`K`. -/
theorem hB1
    (_h : IsBgSolveAt (I := I) (M := M) g₀ g_bg K hT hT1 u gforce Rcap) :
    0 ≤ K.slope :=
  K.slope_nonneg

/-- The outer tame radius is positive; supplied by the packet `K`. -/
theorem hρ (_h : IsBgSolveAt (I := I) (M := M) g₀ g_bg K hT hT1 u gforce Rcap) :
    0 < K.outer :=
  K.outer_pos

/-- The realization radius is positive; supplied by the packet `K`. -/
theorem hP (_h : IsBgSolveAt (I := I) (M := M) g₀ g_bg K hT hT1 u gforce Rcap) :
    0 < K.realize :=
  K.realize_pos

/-- The metric realization bound of the packet on the radius `K.realize`. -/
theorem hreal
    (h : IsBgSolveAt (I := I) (M := M) g₀ g_bg K hT hT1 u gforce Rcap) :
    ∀ S : SmoothCcTensor g₀ 0 2,
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ (((1 : ℕ) : ℝ) + 1) S‖ ≤
          K.realize →
        gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ S) K.threshold :=
  h.bounds.hreal

/-- The fibre threshold is nonnegative. -/
theorem hδ0
    (h : IsBgSolveAt (I := I) (M := M) g₀ g_bg K hT hT1 u gforce Rcap) :
    0 ≤ K.threshold :=
  h.bounds.threshold_nonneg

/-- The fibre threshold is at most one third. -/
theorem hδ3
    (h : IsBgSolveAt (I := I) (M := M) g₀ g_bg K hT hT1 u gforce Rcap) :
    K.threshold ≤ 1 / 3 :=
  h.bounds.threshold_le_third

/-- Continuity of the smooth core of the nonlinearity at the realization used
by `lowregNfun`, with the background slot at `g_bg`. -/
theorem hcore
    (h : IsBgSolveAt (I := I) (M := M) g₀ g_bg K hT hT1 u gforce Rcap) :
    Continuous (coreN (I := I) (M := M) g₀ g_bg K.threshold_lt
      (lowregRealRad (I := I) (M := M) g₀
        (Ctop := K.top) (B1 := K.slope) (ρ := K.outer)
        K.realize_pos.le h.hreal)) :=
  h.bounds.core_cont

/-- The fixed lower-order arm coefficient is nonnegative; supplied by the
packet `K`. -/
theorem hB0
    (_h : IsBgSolveAt (I := I) (M := M) g₀ g_bg K hT hT1 u gforce Rcap) :
    0 ≤ K.base :=
  K.base_nonneg

/-- Continuity of the nonlinearity on the closed state ball, with the
background slot at `g_bg`. -/
theorem hcont
    (h : IsBgSolveAt (I := I) (M := M) g₀ g_bg K hT hT1 u gforce Rcap) :
    Continuous (lowregNfun (I := I) (M := M) g₀ g_bg K.threshold_lt
      K.top_nonneg K.slope_nonneg K.outer_pos K.realize_pos h.hreal) :=
  h.bounds.hcont

/-- The three-arm tame estimate for the nonlinearity on the closed state
ball, with the background slot at `g_bg` and the coefficients taken from the
packet `K`. -/
theorem htame
    (h : IsBgSolveAt (I := I) (M := M) g₀ g_bg K hT hT1 u gforce Rcap) :
    ∀ v w : lowerState (I := I) (M := M) g₀ 1
      (lowregStateRad K.top K.slope K.outer K.realize),
    ‖lowregNfun (I := I) (M := M) g₀ g_bg K.threshold_lt K.top_nonneg
          K.slope_nonneg K.outer_pos K.realize_pos h.hreal v -
        lowregNfun (I := I) (M := M) g₀ g_bg K.threshold_lt K.top_nonneg
          K.slope_nonneg K.outer_pos K.realize_pos h.hreal w‖ ≤
      K.top * lowregOuterRad K.top K.outer K.realize *
          ‖(v.1 : tensorHs (I := I) (M := M) g₀ 0 2
            (((1 : ℕ) : ℝ) + 2)) - w.1‖ +
        K.base *
          ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
            (show ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by linarith)
            ((v.1 : tensorHs (I := I) (M := M) g₀ 0 2
              (((1 : ℕ) : ℝ) + 2)) - w.1)‖ +
        K.slope *
            (‖(v.1 : tensorHs (I := I) (M := M) g₀ 0 2
              (((1 : ℕ) : ℝ) + 2))‖ +
              ‖(w.1 : tensorHs (I := I) (M := M) g₀ 0 2
                (((1 : ℕ) : ℝ) + 2))‖) *
          ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
            (show ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by linarith)
            ((v.1 : tensorHs (I := I) (M := M) g₀ 0 2
              (((1 : ℕ) : ℝ) + 2)) - w.1)‖ :=
  h.bounds.htame

/-- The nonlinearity at the zero state is bounded by the packet's zero-state
size `K.zeroBd`, with the background slot at `g_bg`. -/
theorem hzero
    (h : IsBgSolveAt (I := I) (M := M) g₀ g_bg K hT hT1 u gforce Rcap) :
    ‖lowregNfun (I := I) (M := M) g₀ g_bg K.threshold_lt K.top_nonneg
        K.slope_nonneg K.outer_pos K.realize_pos h.hreal
        ⟨0, zero_mem_lowerState (I := I) (M := M) g₀ 1
          (lowregStateRad_pos K.top_nonneg K.slope_nonneg K.outer_pos
            K.realize_pos).le⟩‖ ≤ K.zeroBd :=
  h.bounds.hzero

/-- The forcing ball: the forcing is bounded by a quarter of the closed state
radius of the packet `K`. -/
theorem hball
    (h : IsBgSolveAt (I := I) (M := M) g₀ g_bg K hT hT1 u gforce Rcap) :
    ‖gforce‖ ≤ lowregStateRad K.top K.slope K.outer K.realize / 4 :=
  h.solve.force_bound

/-- The a.e. Nemytskii identity: the forcing agrees almost everywhere with
the nonlinearity evaluated along its own zero-datum Duhamel field, with the
background slot at `g_bg`. -/
theorem hforce
    (h : IsBgSolveAt (I := I) (M := M) g₀ g_bg K hT hT1 u gforce Rcap) :
    gforce =ᵐ[timeMeasure T]
      (fun t => lowregNfun (I := I) (M := M) g₀ g_bg K.threshold_lt
        K.top_nonneg K.slope_nonneg K.outer_pos K.realize_pos h.hreal
        (aeSetLift (zero_mem_lowerState (I := I) (M := M) g₀ 1
            (lowregStateRad_pos K.top_nonneg K.slope_nonneg K.outer_pos
              K.realize_pos).le)
          (maxRegDuhamelSolField (I := I) (M := M) ((1 : ℕ) : ℝ) hT hT1
            (0 : tensorHs (I := I) (M := M) g₀ 0 2 (((1 : ℕ) : ℝ) + 2))
            gforce) t)) :=
  h.solve.force_eq

end IsBgSolveAt

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
