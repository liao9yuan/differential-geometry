import DifferentialGeometry.Geometry.Comparison.InjectivityRadius
import DifferentialGeometry.Geometry.Comparison.NormalCoordinates
import DifferentialGeometry.Geometry.Coordinates.LocalDiffeoOpen
import DifferentialGeometry.Geometry.Exponential.GaussLemmaPullback

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Exponential ball diffeomorphism (MSM135 `lbl383` item 3a, assembly)

Two results:

* `IsLocalDiffeomorphOn.exists_diffeo_of_injOn` — the generic glue (listed as a
  TODO in Mathlib's `Geometry.Manifold.LocalDiffeomorph`): an **injective** local
  diffeomorphism on an open set restricts to a partial diffeomorphism onto its
  image.  The inverse is `Function.invFunOn`, which agrees near each image point
  with the smooth local inverse supplied by the local-diffeomorphism witness, so
  it is smooth by locality (`contMDiffOn_of_locally_contMDiffOn`).

* `exists_expBall_diffeo` — the Step A item-3a assembly: for `r` below the
  injectivity radius, `framedExpMap g p` restricts to a `C^1` partial
  diffeomorphism with source the Euclidean model ball `ball 0 r`. Through the
  chosen `g_p`-orthonormal frame this is exactly the intrinsic tangent ball.
  Injectivity is
  `injOn_expMap_ball_of_ofReal_lt_injRadius`; the local-diffeomorphism input on
  the ball (nonsingularity of `d exp` — the no-conjugate-points content, true
  below `c/√C₀` by the Jacobi/parallel-frame Grönwall estimate of the B0 route)
  is taken as a hypothesis here and is the B3 frontier of `ConvexBalls.md`.
-/

open Set Function Manifold
open scoped Topology Manifold ContDiff

noncomputable section

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian

section GenericGlue

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {H : Type*} [TopologicalSpace H]
  {G : Type*} [TopologicalSpace G]
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 F G}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N] {n : WithTop ℕ∞}

/-- **An injective local diffeomorphism is a diffeomorphism onto its image.**
If `f` is a local diffeomorphism on an open set `s` and injective there, it is
realised on `s` by a partial diffeomorphism with source `s` and target `f '' s`.
(Compatibility alias for the generic coordinates-layer glue.) -/
theorem exists_diffeo_of_injOn [Nonempty M]
    {f : M → N} {s : Set M} (hf : IsLocalDiffeomorphOn I J n f s)
    (hs : IsOpen s) (hinj : InjOn f s) :
    ∃ Φ : PartialDiffeomorph I J M N n,
      Φ.source = s ∧ Φ.target = f '' s ∧ EqOn Φ f s :=
  DifferentialGeometry.exists_diffeo_of_injOn hf hs hinj

end GenericGlue

section ExpBall

variable {E : Type*} [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [I.Boundaryless] [CompleteSpace E] [T2Space (TangentBundle I M)]

open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Riemannian.NormalCoordinates

/-- **MSM135 `lbl383` item 3a, assembly form.**  For `r` below the injectivity
radius at `p`, given the local-diffeomorphism input on the ball,
`framedExpMap g p` restricts to a `C^1` partial diffeomorphism with source
`Metric.ball (0 : E) r`. -/
theorem exists_expBall_diffeo
    (g : SmoothRiemannianMetric I M) (p : M) {r : ℝ}
    (hr : ENNReal.ofReal r < injRadius (I := I) g p)
    (hloc : IsLocalDiffeomorphOn 𝓘(ℝ, E) I 1
      (framedExpMap (I := I) g p)
      (Metric.ball (0 : E) r)) :
    ∃ Φ : PartialDiffeomorph 𝓘(ℝ, E) I E M 1,
      Φ.source = Metric.ball (0 : E) r ∧
      Φ.target = framedExpMap (I := I) g p '' Metric.ball (0 : E) r ∧
      EqOn Φ (framedExpMap (I := I) g p)
        (Metric.ball (0 : E) r) :=
  exists_diffeo_of_injOn hloc Metric.isOpen_ball
    (injOn_expMap_ball_of_ofReal_lt_injRadius (I := I) g p hr)

/-- **The nonsingularity input, discharged from framed normal coordinates.**
For `r ≤ expRadiusGp g p`, the framed exponential is a `C^1` local
diffeomorphism at every point of `Metric.ball 0 r`. The intrinsic radius and
`normalFrame_sqrt` place the corresponding tangent vector in the source of the
selected exponential partial diffeomorphism. -/
theorem exp_isLocalDiffeomorphOn_ball
    (g : SmoothRiemannianMetric I M) (p : M) {r : ℝ}
    (hr : r ≤ expRadiusGp (I := I) g p) :
    IsLocalDiffeomorphOn 𝓘(ℝ, E) I 1
      (framedExpMap (I := I) g p)
      (Metric.ball (0 : E) r) := by
  haveI : IsManifold I 1 M := by
    have h1 : (1 : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast (by decide : (1 : ℕ∞) ≤ ⊤)
    exact IsManifold.of_le h1
  rintro ⟨x, hx⟩
  rw [Metric.mem_ball, dist_zero_right] at hx
  have hxGp : ‖x‖ < expRadiusGp (I := I) g p := lt_of_lt_of_le hx hr
  have hxR : ‖normalFrame (I := I) g p x‖ <
      expMapC2Radius (I := I) g p := by
    apply norm_lt_expMapC2Radius_of_sqrt_inner_lt (I := I) g p
    simpa only [normalFrame_sqrt] using hxGp
  have hsrc : x ∈ (framedExpDiffeo (I := I) g p).source := by
    rw [framedExp_source]
    exact mem_expMapDiffeo_source_of_norm_lt_radius (I := I) g p hxR
  exact ⟨framedExpDiffeo (I := I) g p, hsrc,
    fun y hy => (framedExp_eq_expMap (I := I) g p hy).symm⟩

/-- **MSM135 `lbl383` item 3a, unconditional form.** For `r` below both the
injectivity radius and `expRadiusGp g p`, `framedExpMap g p` restricts to a
`C^1` partial diffeomorphism with source `Metric.ball 0 r`. -/
theorem exists_expBall_diffeo_of_lt
    (g : SmoothRiemannianMetric I M) (p : M) {r : ℝ}
    (hrinj : ENNReal.ofReal r < injRadius (I := I) g p)
    (hrC2 : r ≤ expRadiusGp (I := I) g p) :
    ∃ Φ : PartialDiffeomorph 𝓘(ℝ, E) I E M 1,
      Φ.source = Metric.ball (0 : E) r ∧
      Φ.target = framedExpMap (I := I) g p '' Metric.ball (0 : E) r ∧
      EqOn Φ (framedExpMap (I := I) g p)
        (Metric.ball (0 : E) r) :=
  exists_expBall_diffeo (I := I) g p hrinj (exp_isLocalDiffeomorphOn_ball (I := I) g p hrC2)

end ExpBall

end Riemannian
end Geometry
end DifferentialGeometry
