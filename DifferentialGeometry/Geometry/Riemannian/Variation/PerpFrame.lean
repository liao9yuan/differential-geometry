import DifferentialGeometry.Geometry.Riemannian.AlongCurve
import DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
import DifferentialGeometry.Geometry.Riemannian.Variation.ParallelTransport

/-!
# Parallel orthonormal perpendicular frame along a geodesic

For a `C^∞` unit-speed geodesic `γ : ℝ → M` on `Icc 0 L` with `L > 0`, this
file isolates the construction and supporting bridges for a parallel
orthonormal frame `e : Fin (finrank E - 1) → SectionAlongCurve I M γ` of the
`g`-orthogonal complement of the velocity `t ↦ dγ_t(1)`:

* `exists_parallel_orthonormal_perp_frame` — existence of the frame: each
  `e i` is differentiable, parallel along `γ` (moving-foot
  `chartCovDerivAlong g (γ t) γ (e i) t = 0`), the frame is `g`-orthonormal
  pointwise, and each `e i` is `g`-orthogonal to the velocity.
* `perp_to_velocity_preserved` — a parallel section that is `g`-orthogonal to
  the velocity at `t = 0` stays `g`-orthogonal to the velocity for all `t`.
* `chartCovDerivAlong_movingFoot_eq_zero_of_isParallelChart_centered` — the
  foot bridge from `IsParallelChart` to the moving-foot `chartCovDerivAlong`.

The foot identity relating a section's value to the inverse-trivialisation of
its chart representation is already available as `symmL_chartRepAt_self`
(`CovariantDerivativeAlong`), so it is consumed directly rather than restated here.
-/

noncomputable section

open Set Function Filter Bundle Manifold
open scoped Topology Manifold ContDiff ENNReal

namespace DifferentialGeometry.Geometry.Riemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Riemannian.AlongCurve
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Geometry.Riemannian.Variation

section PerpFrame

variable [I.Boundaryless] [CompleteSpace E] [T2Space (TangentBundle I M)]

/-- **Existence of a parallel orthonormal perpendicular frame.** For a `C^∞`
unit-speed geodesic `γ` on `Icc 0 L` (`L > 0`), there is a frame
`e : Fin (finrank E - 1) → SectionAlongCurve I M γ` such that each `e i` is
differentiable on `Icc 0 L`, parallel along `γ` (the moving-foot covariant
derivative `chartCovDerivAlong g (γ t) γ (e i) t` vanishes), the frame is
pointwise `g`-orthonormal, and each frame vector is `g`-orthogonal to the
velocity `dγ_t(1)`. This is the standalone form of the frame package consumed
in the Bonnet–Myers second-variation contradiction. -/
theorem exists_parallel_orthonormal_perp_frame
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ) (hgeo : IsGeodesic (I := I) g γ)
    {L : ℝ} (hL : 0 < L)
    (hUnit : ∀ t ∈ Set.Icc (0 : ℝ) L,
      g.inner (γ t) (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ) : E)
        (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ) : E) = 1) :
    ∃ e : Fin (Module.finrank ℝ E - 1) → SectionAlongCurve I M γ,
      (∀ i, ∀ t ∈ Set.Icc (0 : ℝ) L, DifferentiableAt ℝ (e i).toFun t) ∧
      (∀ i, ∀ t ∈ Set.Icc (0 : ℝ) L,
        chartCovDerivAlong (I := I) g (γ t) γ (e i).toFun t = 0) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) L, ∀ i j,
        g.inner (γ t) ((e i).toFun t) ((e j).toFun t) =
          if i = j then 1 else 0) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) L, ∀ i,
        g.inner (γ t) ((e i).toFun t) (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ) : E) = 0) :=
  sorry

/-- **Perpendicularity to the velocity is preserved.** If a section `V` along a
`C^∞` geodesic `γ` is parallel (the intrinsic covariant derivative
`covDerivAlong g γ V` vanishes on `Icc 0 L`) and `V 0` is `g`-orthogonal to the
velocity `dγ_0(1)` at the basepoint, then `V t` is `g`-orthogonal to the
velocity `dγ_t(1)` for every `t ∈ Icc 0 L`. The mechanism is constancy of the
chart-Gram inner product of two parallel sections (the velocity is itself
parallel on a geodesic) together with the velocity-equivalence keystone. -/
theorem perp_to_velocity_preserved
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ) (hgeo : IsGeodesic (I := I) g γ)
    {L : ℝ} (hL : 0 < L) (V : ∀ t, TangentSpace I (γ t))
    (hVpar : ∀ t ∈ Set.Icc (0 : ℝ) L, covDerivAlong (I := I) g γ V t = 0)
    (hPerp0 : g.inner (γ 0) (V 0) (mfderiv 𝓘(ℝ, ℝ) I γ 0 (1 : ℝ) : E) = 0) :
    ∀ t ∈ Set.Icc (0 : ℝ) L,
      g.inner (γ t) (V t) (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ) : E) = 0 :=
  sorry

/-- **Foot bridge: chart parallelism implies moving-foot covariant vanishing.**
If a section's `E`-valued representation `X` is parallel along `γ` in the chart
centred at the foot `γ t` (the predicate `IsParallelChart` for the foot-centred
chart curve velocity, on a neighbourhood `s` of `t`), then the moving-foot
chart-local covariant derivative `chartCovDerivAlong g (γ t) γ X t` vanishes. -/
theorem chartCovDerivAlong_movingFoot_eq_zero_of_isParallelChart_centered
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M) {X : ℝ → E} {s : Set ℝ} {t : ℝ}
    (hX : IsParallelChart (I := I) g (γ t) γ
      (fun τ => deriv (AlongCurve.chartCurve (I := I) (γ t) γ) τ) X s)
    (ht : t ∈ s) :
    chartCovDerivAlong (I := I) g (γ t) γ X t = 0 :=
  sorry

end PerpFrame

end DifferentialGeometry.Geometry.Riemannian

end
