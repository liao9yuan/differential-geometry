import DifferentialGeometry.Metric.Basic
import DifferentialGeometry.Integral.Connection.Ricci
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.Existence
import DifferentialGeometry.PDE.DeTurck.Symbol
import DifferentialGeometry.PDE.RicciFlow.PrincipalSymbol
import Mathlib.Geometry.Manifold.MFDeriv.Basic

/-!
# Phase 7 — Parabolic existence: the engineering interface to Phase 8 (SKELETON)

This file is a *skeleton* for the Phase 7 deliverables. Statements are concrete
and self-contained, but the deeper sub-theorems are stubbed with `sorry` so
the chain can be assembled and downstream Phase 8 work can begin in parallel.

The endpoint is a quasi-linear short-time existence theorem for an
abstract second-order parabolic operator on smooth Riemannian metrics:
given any operator `F : SmoothRiemannianMetric I M → pointwiseBilin I` which
is strictly parabolic at the initial metric `g₀` and has the standard
smooth dependence on `(g, ∇g, ∇²g)`, there is a positive existence time
`T > 0` and a smooth-in-time family of Riemannian metrics
`g_fam : ℝ → SmoothRiemannianMetric I M` with `g_fam 0 = g₀` and
`∂_t g_fam(t) = F(g_fam(t))` for every `t ∈ [0, T)`.

Phase 8 (handled in a separate dispatch) consumes this endpoint by
instantiating `F` with the DeTurck-Ricci right-hand side
`g ↦ -2 Ric(g) + 𝓛_{X(g, g_bg)} g`, which is strictly parabolic by the
existing `deTurckSymbol_isStrictlyParabolic`.

## Layout

* `IsParabolicMetricRHS` — abstract data describing a parabolic operator
  on metrics together with its strict-parabolicity witness at the initial
  metric, suitable for plugging into `quasilinear_metric_parabolic_shortTime_exists`.
* `IsQuasilinearMetricParabolicSolution F g₀ T g_fam` — the equation
  `∂_t g_fam(t) = F(g_fam(t))` evaluated pointwise against tangent
  vectors, with the initial condition `g_fam 0 = g₀` and the existence
  time `T` recorded.
* `IsLinearTensorParabolicMildSolution` — the analogous predicate for the
  linear inhomogeneous tensor heat equation `∂_t u + L u = F(t)`,
  expressed via the Duhamel formula. Used internally as the linearisation
  of the quasi-linear case.

## Main theorems (skeleton, proofs are `sorry`)

* `linear_tensor_parabolic_shortTime_exists` — existence of a mild
  solution to the linear inhomogeneous tensor heat equation. The
  existing project lemma `tensor_linear_parabolic_existence`
  (`Analysis/Parabolic/TensorLinearParabolic.lean`) provides this under
  a chart-locality predicate; the predicate-free version is the target
  of Route Y. The skeleton states it predicate-free.
* `quasilinear_metric_parabolic_shortTime_exists` — the Phase 7 endpoint:
  short-time existence for `∂_t g = F(g)`, by Banach fixed point on
  Duhamel iterates seeded by the linearised semigroup.
-/

namespace DifferentialGeometry
namespace PDE

universe u v

open scoped Manifold ContDiff Topology
open Bundle MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-! ## Section A — Predicates -/

/-- A smooth family of Riemannian metrics `g_fam : ℝ → SmoothRiemannianMetric I M`
solves the quasi-linear parabolic PDE `∂_t g(t) = F(g(t))` on the time interval
`[0, T)` with initial value `g₀`, when the time derivative of the underlying
bilinear form `(g_fam s).inner x v w` at every base point `x` and tangent pair
`(v, w)` matches `F(g_fam(t)) x v w`.

The right-hand side `F` produces, for each metric `g`, a pointwise bilinear form
`F g : ∀ x, T_x M →L T_x M →L ℝ`. Phase 8 will instantiate `F` with the
DeTurck-Ricci right-hand side
`F(g) x v w = -2 ricciTensor g x v w + lieDerivMetric g (deTurckVF g g_bg) x v w`. -/
def IsQuasilinearMetricParabolicSolution
    (F : SmoothRiemannianMetric I M →
         (∀ x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ))
    (g₀ : SmoothRiemannianMetric I M) (T : ℝ)
    (g_fam : ℝ → SmoothRiemannianMetric I M) : Prop :=
  0 < T ∧ g_fam 0 = g₀ ∧
    ∀ t ∈ Set.Ico (0 : ℝ) T, ∀ x : M, ∀ v w : TangentSpace I x,
      HasDerivWithinAt (fun s : ℝ => (g_fam s).inner x v w)
                  (F (g_fam t) x v w) (Set.Ici 0) t

/-- An abstract strict-parabolicity hypothesis on an operator `F` at a metric `g`.

For the skeleton this is an opaque `Prop` placeholder; downstream callers
(notably Phase 8) supply concrete content by combining the existing
`deTurckSymbol_isStrictlyParabolic` (`PDE/DeTurck/StrictParabolicity.lean`) with
the linearisation infrastructure in `PDE/DeTurck/DeTurckLinearization/`. The
shape `Prop` is what `quasilinear_metric_parabolic_shortTime_exists` consumes. -/
def IsStrictlyParabolicMetricRHS
    (F : SmoothRiemannianMetric I M →
         (∀ x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ))
    (g : SmoothRiemannianMetric I M) : Prop :=
  ∃ σ : DifferentialGeometry.PDE.DeTurck.TensorSymbol (E := E) I M,
    DifferentialGeometry.PDE.RicciFlow.HasPrincipalSymbol F g σ

/-- A second-order parabolic operator `F` on metrics has *smooth quasi-linear
dependence on* the data `(g, ∇g, ∇²g)`. As an abstract Prop placeholder for the
skeleton; downstream the concrete content is "F factors through chart-coordinate
data as a smooth function of metric components and their first two derivatives,
strictly parabolic in the highest-order part". -/
def IsSmoothQuasilinearMetricRHS
    (F : SmoothRiemannianMetric I M →
         (∀ x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)) : Prop :=
  (∀ (g : SmoothRiemannianMetric I M) (α : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn I 𝓘(ℝ, ℝ) ∞
        (fun x => F g x
          (DifferentialGeometry.Integral.Measure.chartModelBasis E i)
          (DifferentialGeometry.Integral.Measure.chartModelBasis E j))
        (chartAt H α).source)
    ∧ ∀ g : SmoothRiemannianMetric I M, IsStrictlyParabolicMetricRHS F g

/-! ## Section B — The Phase 7 → Phase 8 endpoint (skeleton) -/

/-- **Phase 7 endpoint: short-time existence for a strictly parabolic
quasi-linear PDE on smooth Riemannian metrics over a closed manifold.**

For any smooth Riemannian metric `g₀` on a closed (compact, boundaryless)
manifold `M` and any operator `F` on smooth Riemannian metrics that is
strictly parabolic at `g₀` and has smooth quasi-linear dependence on
`(g, ∇g, ∇²g)`, the PDE `∂_t g = F(g)` admits a positive existence time
`T > 0` and a smooth-in-time solution `g_fam : ℝ → SmoothRiemannianMetric I M`
with `g_fam 0 = g₀`.

Phase 8 instantiates this with `F(g) := -2 Ric(g) + 𝓛_{X(g, g_bg)} g`
(the DeTurck-Ricci right-hand side). The strict-parabolicity witness for
that `F` is the existing `deTurckSymbol_isStrictlyParabolic`.

This is the **engineering interface between Phase 7 and Phase 8**.

**Proof outline (when filled in)**:
1. Linearise `F` at `g₀` to obtain a linear principal part
   `L g h = (DF)(g₀)(h)` plus a quasi-linear remainder.
2. The principal part is a second-order elliptic operator on
   `(0, 2)`-tensors with positive-definite symbol (by `IsStrictlyParabolicMetricRHS`).
3. Generate a bounded `C₀`-semigroup `S` from `L g₀` on the Hilbert
   completion (existing `tensorHeatSemigroup` after Route Y removes
   chart-locality predicates).
4. Apply `Analysis.Parabolic.QuasiLinear.Existence.semilinear_parabolic_existence`
   to the abstract Duhamel iteration with `S` and the non-linear
   remainder. This produces a mild solution `g_fam` on `[0, T]` with
   `T = 1 / (L + 1)` where `L` is the local Lipschitz constant of the
   remainder.
5. Smooth-in-time regularity follows from the bootstrap inside the
   maximal-regularity space (`Analysis/Parabolic/MaximalRegularity/`).

For the skeleton, the entire proof is `sorry`. -/
theorem quasilinear_metric_parabolic_shortTime_exists
    [CompactSpace M] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]
    (F : SmoothRiemannianMetric I M →
         (∀ x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ))
    (g₀ : SmoothRiemannianMetric I M)
    (_hParabolic : IsStrictlyParabolicMetricRHS (I := I) F g₀)
    (_hSmooth : IsSmoothQuasilinearMetricRHS (I := I) F) :
    ∃ T : ℝ, ∃ g_fam : ℝ → SmoothRiemannianMetric I M,
      IsQuasilinearMetricParabolicSolution (I := I) F g₀ T g_fam := by
  -- Skeleton: actual proof composes the linearisation, the linear-tensor
  -- existence below, and the abstract `semilinear_parabolic_existence`.
  sorry

/-! ## Section C — Auxiliary: linear inhomogeneous tensor heat equation -/

/-- A predicate stating that `u : ℝ → TensorL2 r s g` is the mild Duhamel solution
of the linear inhomogeneous tensor heat equation `∂_t u + L u = F(t)` with initial
value `u₀`, where `L` is the (operator generating the) semigroup `S`.

The Duhamel formula is `u(t) = S(t) u₀ + ∫₀ᵗ S(t - τ) (F τ) dτ`. Here we leave
the semigroup `S` and forcing `F` as abstract data so the predicate composes
with the existing `Analysis/Parabolic/QuasiLinear/Existence.lean` infrastructure. -/
def IsLinearTensorParabolicMildSolution
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (S : Analysis.Parabolic.QuasiLinear.BoundedC0Semigroup X) (u₀ : X)
    (F : ℝ → X) (T : ℝ) (u : ℝ → X) : Prop :=
  0 < T ∧ u 0 = u₀ ∧
    ContinuousOn u (Set.Icc 0 T) ∧
    ∀ t ∈ Set.Icc (0 : ℝ) T,
      u t = S t u₀ + ∫ τ in (0 : ℝ)..t, S (t - τ) (F τ)

/-- **Linear inhomogeneous tensor heat equation: mild solution exists** (SKELETON).

The existing project lemma `tensor_linear_parabolic_existence`
(`Analysis/Parabolic/TensorLinearParabolic.lean:525`) provides this under
the chart-locality predicate `HasLocallyConstantChartAt H M`. After Route Y,
the predicate is removed; the predicate-free statement is the target.

For the skeleton we keep the conclusion identical to the Duhamel form and stub
the proof. The underlying machinery — `tensorHeatSemigroup`, mild-solution
continuity, the Duhamel formula — is already in place. -/
theorem linear_tensor_parabolic_shortTime_exists
    [CompactSpace M] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (S : Analysis.Parabolic.QuasiLinear.BoundedC0Semigroup X) (u₀ : X)
    (F : ℝ → X) (_hF : Continuous F) :
    ∃ T : ℝ, ∃ u : ℝ → X,
      IsLinearTensorParabolicMildSolution S u₀ F T u := by
  -- Skeleton: actual proof uses `semilinear_parabolic_existence` with `N := 0`
  -- and forcing absorbed into the constant term, or directly the project's
  -- `tensorMildSolution`/`tensor_linear_parabolic_existence` once
  -- predicate-free.
  sorry

/-! ## Section D — Composition note

The skeleton's two `theorem`s are deliberately *both* stubbed at the
predicate-free public surface; the abstract existence machinery in
`Analysis/Parabolic/QuasiLinear/Existence.lean::semilinear_parabolic_existence`
(which is fully proved, no `sorry`) gives the underlying Duhamel /
Banach-fixed-point argument. To close `linear_tensor_parabolic_shortTime_exists`
the open work is purely the existing-infrastructure lift to a
predicate-free statement; `quasilinear_metric_parabolic_shortTime_exists`
additionally needs the linearisation + Banach fixed-point assembly. Both
are tracked downstream of Route Y completion. -/

end PDE
end DifferentialGeometry
