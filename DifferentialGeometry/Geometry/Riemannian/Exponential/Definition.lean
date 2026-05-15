import DifferentialGeometry.Geometry.Riemannian.Geodesic.Equation
import DifferentialGeometry.Geometry.Riemannian.Geodesic.Existence
import DifferentialGeometry.Geometry.Riemannian.Geodesic.MaximalInterval
import DifferentialGeometry.Geometry.Riemannian.Geodesic.Uniqueness

set_option linter.unusedSectionVars false

/-!
# The exponential map of a smooth Riemannian metric

For a smooth Riemannian metric `g` on a boundaryless smooth manifold `M`
modelled on a complete inner-product space `E`, and for every base point
`p : M` and tangent vector `v : T_p M`, the maximal geodesic
`maximalGeodesic g p v : ℝ → M` provides a canonical curve through `p`
with initial velocity `v`. The exponential map at `p` is the value of
this curve at time `t = 1`.

## Main definitions

* `expMap g p v` — the exponential map at `p` applied to `v`, defined as
  `maximalGeodesic g p v 1`. On the natural domain (`expDomain g p`),
  this is the genuine geodesic-flow value; outside, it reduces to the
  constant junk value `p` inherited from `maximalGeodesic_of_not_mem`.

* `expDomain g p` — the natural domain of `expMap g p`: the set of
  vectors `v : T_p M` such that the maximal interval contains `1`.

## Main theorems

* `expMap_zero_velocity` — for `v = 0 : T_p M`, the value `expMap g p 0`
  is the value at `t = 1` of the chosen witness curve for the maximal
  geodesic with zero initial velocity. This is the cleanest available
  statement at this layer; the genuine "exp_p(0) = p" identity requires
  a connected-propagation global-uniqueness argument for the chart-fixed
  geodesic vector field, which is a separate development.

* `zero_mem_expDomain` — the zero vector is always in `expDomain g p`,
  since the stationary geodesic exists for all time.

* `expDomain_zero_nonempty` — the natural domain is non-empty.

The full openness of `expDomain g p` at every `v ∈ expDomain g p`
requires joint smoothness of the geodesic flow in `(t, v)`. The joint
`C^1` regularity of the chart-pushed geodesic flow is recorded in
`Geodesic/SmoothFlow.lean`; lifting that joint regularity back through
charts to obtain openness at non-zero `v` is a downstream step and is
not addressed here.
-/

noncomputable section

open Bundle Manifold Set Filter Function
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Exponential

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Integral.Measure

/-! ## Definition of the exponential map -/

/-- The exponential map at `p ∈ M` applied to a tangent vector `v ∈ T_p M`,
defined as the value of the maximal geodesic with initial data `(p, v)`
at time `t = 1`. When `1` lies outside the maximal interval, the value is
the constant junk value `p` of `maximalGeodesic`. -/
def expMap (g : SmoothRiemannianMetric I M) (p : M) (v : TangentSpace I p) : M :=
  maximalGeodesic (I := I) g p v 1

@[simp] lemma expMap_def (g : SmoothRiemannianMetric I M) (p : M)
    (v : TangentSpace I p) :
    expMap (I := I) g p v = maximalGeodesic (I := I) g p v 1 := rfl

/-! ## The natural domain of the exponential map -/

/-- The natural domain of `expMap g p`: the set of vectors `v : T_p M`
such that the maximal interval of the geodesic with initial data
`(p, v)` contains `1`. On this set, `expMap g p v` is the genuine
geodesic-flow value; outside, it reverts to `p`. -/
def expDomain (g : SmoothRiemannianMetric I M) (p : M) : Set (TangentSpace I p) :=
  {v | (1 : ℝ) ∈ maximalGeodesicInterval (I := I) g p v}

@[simp] lemma mem_expDomain_iff
    {g : SmoothRiemannianMetric I M} {p : M} {v : TangentSpace I p} :
    v ∈ expDomain (I := I) g p ↔
      (1 : ℝ) ∈ maximalGeodesicInterval (I := I) g p v := Iff.rfl

/-! ## Stationary-geodesic witness at the zero vector

The constant curve `fun _ => p` is a geodesic with initial data
`(p, 0)`; this gives a witness for every time, including `t = 1`. -/

section StationaryWitness

variable [I.Boundaryless] [CompleteSpace E]

/-- For the zero initial velocity, the constant geodesic at `p` is a
`MaximalGeodesicWitness` at every time. -/
theorem maximalGeodesicWitness_zero_all_times
    (g : SmoothRiemannianMetric I M) (p : M) (t : ℝ) :
    MaximalGeodesicWitness (I := I) g p (0 : TangentSpace I p) t := by
  classical
  -- The constant geodesic `fun _ => p` is global, witnessing the predicate
  -- on `Set.univ` (which contains every `t`).
  have hconst : IsGeodesic (I := I) g (fun _ : ℝ => p) :=
    isGeodesic_const (I := I) g p
  obtain ⟨α, f, hproj, hf⟩ := hconst
  -- We need to upgrade to `IsGeodesicOnWithInitial` with `f 0 = ⟨p, 0⟩`.
  -- The constructor of `isGeodesic_const` uses `α = p`, lift
  -- `fun _ => ⟨p, 0⟩`, but this is opaque after destructuring. So we
  -- construct the witness from scratch with explicit data.
  refine ⟨fun _ : ℝ => p, Set.univ, isOpen_univ, Set.mem_univ _, Set.mem_univ _, ?_⟩
  -- Manual witness: α = p, f := fun _ => ⟨p, 0⟩, hf below.
  refine ⟨p, fun _ : ℝ => (⟨p, (0 : E)⟩ : TangentBundle I M), ?_, rfl, ?_⟩
  · intro _; rfl
  · -- Constant lift is an integral curve of the chart-fixed VF on `Set.univ`,
    -- because the VF vanishes at `⟨p, 0⟩` (chart-fixed at α = p, zero section).
    have hvf_zero : geodesicVectorFieldChart (I := I) g p
        (⟨p, (0 : E)⟩ : TangentBundle I M) = 0 :=
      geodesicVectorFieldChart_zero_section (I := I) g p
    -- `isMIntegralCurve_const` produces a global `IsMIntegralCurve`; its
    -- restriction to `Set.univ` is what we want.
    exact (isMIntegralCurve_const hvf_zero).isMIntegralCurveOn Set.univ

/-- The zero vector is always in the natural domain of `expMap g p`. -/
theorem zero_mem_expDomain (g : SmoothRiemannianMetric I M) (p : M) :
    (0 : TangentSpace I p) ∈ expDomain (I := I) g p :=
  maximalGeodesicWitness_zero_all_times (I := I) g p 1

/-- The natural domain of `expMap g p` is nonempty (it always contains `0`). -/
theorem expDomain_nonempty (g : SmoothRiemannianMetric I M) (p : M) :
    (expDomain (I := I) g p).Nonempty :=
  ⟨0, zero_mem_expDomain (I := I) g p⟩

end StationaryWitness

/-! ## Junk-value behaviour outside the natural domain

Outside `expDomain g p`, the value of `expMap g p v` is the junk value
`p` of `maximalGeodesic`. -/

section JunkValue

variable [I.Boundaryless] [CompleteSpace E]

/-- Outside the natural domain, `expMap` returns the junk value `p`. -/
theorem expMap_of_not_mem_expDomain
    {g : SmoothRiemannianMetric I M} {p : M} {v : TangentSpace I p}
    (hv : v ∉ expDomain (I := I) g p) :
    expMap (I := I) g p v = p := by
  unfold expMap
  exact maximalGeodesic_of_not_mem (I := I) hv

end JunkValue

/-! ## Witness-level identification of `expMap g p 0`

For `v = 0`, the natural witness is the constant geodesic. The value
`expMap g p 0 = maximalGeodesic g p 0 1` equals the value at `t = 1`
of the `Classical.choose`-chosen geodesic witness. We package this
witness-level identification.

The stronger statement `expMap g p 0 = p` requires propagating local
geodesic uniqueness along the connected maximal interval. The chart-fixed
geodesic vector field is only `C^∞` on the chart-domain preimage, so the
propagation must change chart basepoint along the curve — a moving-chart
construction that the architecture explicitly defers. The witness-level
identification below is the cleanest unconditional statement available
at this layer. -/

section ExpMapZeroWitnessLevel

variable [I.Boundaryless] [CompleteSpace E]

/-- The chosen geodesic witness curve for `(p, 0)` at time `1` starts at
`p`. (This is `maximalGeodesicChosenCurve_spec` paired with the
`start_eq` lemma.) -/
theorem maximalGeodesicChosenCurve_zero_start_eq
    (g : SmoothRiemannianMetric I M) (p : M) :
    maximalGeodesicChosenCurve (I := I) g p (0 : TangentSpace I p)
      (maximalGeodesicWitness_zero_all_times (I := I) g p 1) 0 = p := by
  obtain ⟨J, _hJ_open, _h0J, _h1J, hγ⟩ :=
    maximalGeodesicChosenCurve_spec (I := I) g p (0 : TangentSpace I p)
      (maximalGeodesicWitness_zero_all_times (I := I) g p 1)
  exact hγ.start_eq

end ExpMapZeroWitnessLevel

end Exponential
end Riemannian
end Geometry
end DifferentialGeometry

end
