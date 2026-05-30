import DifferentialGeometry.Geometry.Riemannian.HopfRinow
import DifferentialGeometry.Geometry.Riemannian.Geodesic.Equation
import DifferentialGeometry.Geometry.Riemannian.Geodesic.CrossVFReduction
import DifferentialGeometry.Geometry.Riemannian.Exponential.Definition

set_option linter.unusedSectionVars false

/-!
# The intrinsic exponential map of a complete Riemannian manifold

The chart-fixed exponential map `expMap g p v = maximalGeodesic g p v 1`
(`Exponential/Definition.lean`) follows the geodesic spray written in the single
chart at `p`.  That object is junk once the geodesic leaves `(chartAt H p).source`,
so on a multi-chart manifold `expMap g p v` reverts to `p` for large `v`.

For the metric-geometry program (e.g. the compactness/diameter theorems) one needs
the *intrinsic* exponential map: the value at `t = 1` of the **complete** geodesic
through `p` with initial velocity `v`, where "complete" means defined on all of `ℝ`
via the moving-foot geodesic predicate `IsGeodesic` (chart-independent).

## Main objects

* `exists_complete_geodesic_at_velocity` — existence of a two-sided complete
  geodesic `Γ : ℝ → M` with `Γ 0 = p` and launch velocity `v`.  Built from the
  local seed `exists_isGeodesicOn_Ioo_at_velocity` and the metric-completeness
  forward/backward extension `isGeodesicOn_Ici_of_complete`.
* `intrinsicGeodesic g p v : ℝ → M` — the chosen complete geodesic.
* `expMapIntrinsic g p v : M := intrinsicGeodesic g p v 1` — the intrinsic
  exponential map.

## Status of this file

The forward/backward completeness extension engine
`HopfRinow.isGeodesicOn_Ici_of_complete` is seeded by a geodesic on a
*left-unbounded* interval `Iio b₀`.  The local seed
`exists_isGeodesicOn_Ioo_at_velocity` only produces a geodesic on a *bounded*
interval `Ioo (-δ) δ`.  Bridging the two — an `Ioo`-seeded completeness engine,
or equivalently a two-sided complete-extension producer — is the single missing
analytic input recorded as the residual of
`exists_complete_geodesic_at_velocity` below.  The downstream definitions and
their specification lemmas are stated against that existential so that, once it
is discharged, the intrinsic exponential map is available with no further work.
-/

noncomputable section

open Bundle Manifold Set Filter Function
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Exponential

open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Geometry.Riemannian.HopfRinow
open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [Module.Finite ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]
variable [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]

/-! ## Two-sided geodesic completeness at a prescribed launch velocity

Throughout this section every declaration carries the completeness context
`[PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]` together
with `[IsContinuousRiemannianBundle E (fun x ↦ TangentSpace I x)]`.  The latter
binder, and the fibrewise `g`-inner product it depends on, can only be
synthesised once the project's competing fibre-norm instances
`Tensor0SBundle.tangentSpace_normedAddCommGroup` /
`Tensor0SBundle.tangentSpace_normedSpace` are locally removed (otherwise the
norm diamond hides the `RiemannianBundle`-derived inner product); hence the
`attribute [-instance] … in` prefix on every such declaration, mirroring the
pattern used throughout `HopfRinow`.
-/

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- **Two-sided geodesic completeness.**  On a complete Riemannian manifold,
for every base point `p` and tangent vector `v : T_p M` there is a geodesic
`Γ : ℝ → M` defined on all of `ℝ` with `Γ 0 = p` and launch velocity `v`
(`mfderiv Γ 0 1 = v`).

This is the chart-independent, genuinely complete object that the chart-fixed
`expMap` fails to provide: it follows the moving-foot geodesic equation at every
real time, so it remains valid after the geodesic leaves the home chart at `p`.

CONSTRUCTION (the intended axiom-clean route, see the file header for the single
missing producer):

* SEED: `HopfRinow.exists_isGeodesicOn_Ioo_at_velocity g p v` gives a local
  geodesic `η` on `Ioo (-δ) δ` with `η 0 = p` and `mfderiv η 0 1 = v`.
* FORWARD / BACKWARD: `HopfRinow.isGeodesicOn_Ici_of_complete` extends a geodesic
  on a half-line `Iio b₀` to a complete geodesic on `Ici 0`; applied to the seed
  and to its time-reversal `isGeodesic_comp_neg`, it yields the two halves.
* GLUE at `0`: `Geodesic.isGeodesicOn_glue_at_limit` assembles the halves into a
  geodesic on all of `ℝ`, preserving the value and velocity at `0`.

RESIDUAL: the seed lives on a bounded interval `Ioo (-δ) δ`, whereas
`isGeodesicOn_Ici_of_complete` requires a seed on the left-unbounded `Iio b₀`.
The bridge (an `Ioo`-seeded forward-completeness engine) is the single missing
analytic input; it is recorded as the body `sorry` of this stub. -/
theorem exists_complete_geodesic_at_velocity
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M) (p : M) (v : TangentSpace I p) :
    ∃ Γ : ℝ → M, IsGeodesic (I := I) g Γ ∧ Γ 0 = p ∧
      (mfderiv 𝓘(ℝ, ℝ) I Γ 0 (1 : ℝ) : E) = (v : E) := by
  sorry

/-! ## The intrinsic geodesic and exponential map -/

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- The intrinsic complete geodesic through `p` with launch velocity `v`,
chosen by `exists_complete_geodesic_at_velocity`. -/
def intrinsicGeodesic
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M) (p : M) (v : TangentSpace I p) : ℝ → M :=
  Classical.choose (exists_complete_geodesic_at_velocity (I := I) g p v)

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- The intrinsic geodesic is a geodesic on all of `ℝ`. -/
theorem intrinsicGeodesic_isGeodesic
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M) (p : M) (v : TangentSpace I p) :
    IsGeodesic (I := I) g (intrinsicGeodesic (I := I) g p v) :=
  (Classical.choose_spec (exists_complete_geodesic_at_velocity (I := I) g p v)).1

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- The intrinsic geodesic starts at `p` (value at `t = 0`). -/
@[simp] theorem intrinsicGeodesic_zero
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M) (p : M) (v : TangentSpace I p) :
    intrinsicGeodesic (I := I) g p v 0 = p :=
  (Classical.choose_spec (exists_complete_geodesic_at_velocity (I := I) g p v)).2.1

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- The launch velocity of the intrinsic geodesic at `t = 0` is `v`. -/
theorem intrinsicGeodesic_mfderiv_zero
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M) (p : M) (v : TangentSpace I p) :
    (mfderiv 𝓘(ℝ, ℝ) I (intrinsicGeodesic (I := I) g p v) 0 (1 : ℝ) : E)
      = (v : E) :=
  (Classical.choose_spec (exists_complete_geodesic_at_velocity (I := I) g p v)).2.2

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- The intrinsic exponential map at `p`: the value at `t = 1` of the complete
geodesic through `p` with launch velocity `v`.  Unlike the chart-fixed `expMap`,
this follows the geodesic across charts and is the object used by the
metric-geometry (compactness / diameter) theorems. -/
def expMapIntrinsic
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M) (p : M) (v : TangentSpace I p) : M :=
  intrinsicGeodesic (I := I) g p v 1

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
@[simp] theorem expMapIntrinsic_def
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M) (p : M) (v : TangentSpace I p) :
    expMapIntrinsic (I := I) g p v = intrinsicGeodesic (I := I) g p v 1 := rfl

/-! ## Time-regularity of the intrinsic geodesic

A geodesic on an open set, continuous there, is `C¹` in time
(`HopfRinow.isGeodesicOn_contMDiffOn_one`).  The intrinsic geodesic is a geodesic
on all of `ℝ`; its continuity is the regularity datum exposed by the construction
in `exists_complete_geodesic_at_velocity` (the assembled curve is a chart-by-chart
glue of genuine local geodesics, each continuous).  Pending that construction, the
continuity and hence the `C¹`-in-time regularity are recorded as stubs.
-/

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- Continuity of the intrinsic geodesic.  Provable once
`exists_complete_geodesic_at_velocity` is built from the (continuous) chart-glue
of local geodesics; recorded here as the regularity datum feeding the `C¹`-in-time
lemma below. -/
theorem intrinsicGeodesic_continuous
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M) (p : M) (v : TangentSpace I p) :
    Continuous (intrinsicGeodesic (I := I) g p v) := by
  sorry

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- The intrinsic geodesic is `C¹` in time on all of `ℝ`.  A geodesic, continuous
on the open set `Set.univ`, is `ContMDiffOn 𝓘(ℝ,ℝ) I 1` there by
`HopfRinow.isGeodesicOn_contMDiffOn_one`. -/
theorem intrinsicGeodesic_contMDiffOn
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M) (p : M) (v : TangentSpace I p) :
    ContMDiffOn 𝓘(ℝ, ℝ) I 1 (intrinsicGeodesic (I := I) g p v) Set.univ := by
  refine HopfRinow.isGeodesicOn_contMDiffOn_one (I := I) g isOpen_univ ?_ ?_
  · exact (intrinsicGeodesic_isGeodesic (I := I) g p v).isGeodesicOn Set.univ
  · exact (intrinsicGeodesic_continuous (I := I) g p v).continuousOn

end Exponential
end Riemannian
end Geometry
end DifferentialGeometry
