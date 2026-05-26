import DifferentialGeometry.Geometry.Riemannian.Exponential.Definition
import DifferentialGeometry.Geometry.Riemannian.Exponential.MfderivAtZero
import DifferentialGeometry.Geometry.Riemannian.NormalCoordinates
import DifferentialGeometry.Geometry.Riemannian.InjectivityRadius
import DifferentialGeometry.Geometry.Riemannian.Geodesic.Equation
import DifferentialGeometry.Geometry.Riemannian.Geodesic.Uniqueness
import DifferentialGeometry.Geometry.Riemannian.Geodesic.MaximalInterval
import DifferentialGeometry.Integral.Measure.ChartDensity
import Mathlib.Geometry.Manifold.Riemannian.PathELength

set_option linter.unusedSectionVars false

/-!
# Gauss's lemma and the radial-minimiser package

For a smooth Riemannian metric `g` on a boundaryless smooth manifold `M`,
this file packages the classical Gauss-lemma cluster:

* `gauss_lemma_pullback` — the pullback of `g` through `expMap g p` at
  a radial direction `v` evaluates to `⟪v, v⟫` on the `(v, v)` slot and
  to `0` on the `(v, w)` slot whenever `w` satisfies `⟪v, w⟫ = 0`.

* `subArc_of_minimizer_is_minimizer` — a sub-arc of a length-minimising
  curve is itself a length-minimiser between its restricted endpoints.

* `normalBall_radial_unique_minimizer` — inside a normal ball at `p`,
  every `C¹` curve from `p` to `expMap g p v` has `pathELength ≥ ‖v‖`,
  with equality only for a monotone radial reparametrisation.

* `local_radial_identification_of_minimizer` — at any interior parameter
  of a length-minimising curve there is a `δ`-neighbourhood on which the
  curve is a monotone radial geodesic in normal coordinates at `γ(t₀)`.

* `arclength_reparam_is_smooth_geodesic` — the global arclength
  reparametrisation of a length-minimiser is a smooth geodesic on the
  open parameter interval.

All five statements live below as `theorem ... := sorry` stubs.
-/

noncomputable section

open Set Function Filter Bundle Manifold
open scoped Topology Manifold ContDiff ENNReal

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Riemannian.Exponential

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

section GaussLemma

variable [I.Boundaryless] [CompleteSpace E] [T2Space (TangentBundle I M)]

/-! ## Gauss's lemma (pullback form)

The pullback of the Riemannian metric through `expMap g p` at a radial
direction `v` (inside the natural domain) preserves the radial inner
product and annihilates the radial/orthogonal cross term. We split the
two equalities into two theorems for clean downstream consumption. -/

/-- **Gauss's lemma (pullback form).** At every radial direction
`v ∈ expDomain g p`, the pullback of `g` through `expMap g p` evaluates
to `⟪v, v⟫` on the `(v, v)` slot, and annihilates the `(v, w)` slot for
every `w` orthogonal to `v` in the Euclidean inner product. -/
theorem gauss_lemma_pullback
    (g : SmoothRiemannianMetric I M) (p : M) {v : E}
    (hv : (show TangentSpace I p from v) ∈ expDomain (I := I) g p) :
    g.inner (expMap (I := I) g p (show TangentSpace I p from v))
        (mfderiv 𝓘(ℝ, E) I
          (fun u : E => expMap (I := I) g p (show TangentSpace I p from u)) v
          (show TangentSpace I p from v))
        (mfderiv 𝓘(ℝ, E) I
          (fun u : E => expMap (I := I) g p (show TangentSpace I p from u)) v
          (show TangentSpace I p from v)) =
      inner ℝ v v ∧
    ∀ {w : E}, inner ℝ v w = (0 : ℝ) →
      g.inner (expMap (I := I) g p (show TangentSpace I p from v))
          (mfderiv 𝓘(ℝ, E) I
            (fun u : E => expMap (I := I) g p (show TangentSpace I p from u)) v
            (show TangentSpace I p from v))
          (mfderiv 𝓘(ℝ, E) I
            (fun u : E => expMap (I := I) g p (show TangentSpace I p from u)) v
            (show TangentSpace I p from w)) =
        (0 : ℝ) := by
  sorry

end GaussLemma

section LengthBookkeeping

/-! ## Sub-arc of a minimiser is itself a minimiser

Pure metric bookkeeping built from
`Mathlib.Geometry.Manifold.Riemannian.PathELength`. -/

/-- **A sub-arc of a length-minimising `C¹` curve is itself a
length-minimiser between its restricted endpoints.** That is, if a
curve `γ : ℝ → M` realises `riemannianEDist I (γ a) (γ b) = pathELength I γ a b`
on `[a, b]`, then on every sub-interval `[s, t] ⊆ [a, b]` the sub-arc
realises `riemannianEDist I (γ s) (γ t) = pathELength I γ s t`. -/
theorem subArc_of_minimizer_is_minimizer
    {γ : ℝ → M} {a b s t : ℝ}
    (hγ : CMDiff[Icc a b] 1 γ)
    (hmin : riemannianEDist I (γ a) (γ b) = pathELength I γ a b)
    (hab : a ≤ b) (has : a ≤ s) (hst : s ≤ t) (htb : t ≤ b) :
    riemannianEDist I (γ s) (γ t) = pathELength I γ s t := by
  sorry

end LengthBookkeeping

section RadialUniqueMinimizer

variable [I.Boundaryless] [CompleteSpace E] [T2Space (TangentBundle I M)]

/-! ## Inside a normal ball the radial geodesic is the unique minimiser

Direct consequence of Gauss's lemma: the metric expansion
`‖γ'‖² = (γ'_r)² + ‖γ'_a‖²_a ≥ (γ'_r)²` integrates to give a length
lower bound `≥ ‖v‖`, with equality only for a monotone radial
reparametrisation. -/

/-- **Inside the normal ball, every `C¹` curve from `p` to `expMap g p v`
has length at least `‖v‖`.** This is the length lower bound delivered
by Gauss's lemma; the equality-case identification of the radial
geodesic as the unique minimiser is the content of the prose statement
and the assembly downstream. -/
theorem normalBall_radial_unique_minimizer
    (g : SmoothRiemannianMetric I M) (p : M) {v : E}
    (hv : (show TangentSpace I p from v) ∈ expDomain (I := I) g p)
    (hball : v ∈ (NormalCoordinates.normalChartAt (I := I) g p).target) :
    ENNReal.ofReal ‖v‖ ≤
      riemannianEDist I p
        (expMap (I := I) g p (show TangentSpace I p from v)) := by
  sorry

end RadialUniqueMinimizer

section LocalRadialIdentification

variable [I.Boundaryless] [CompleteSpace E] [T2Space (TangentBundle I M)]

/-! ## Local radial identification of a minimiser

At any interior parameter of a length-minimising curve, there is a
`δ`-neighbourhood on which the curve, after rescaling, is a monotone
radial geodesic in normal coordinates at `γ(t₀)`. -/

/-- **Local radial identification.** Let `γ : ℝ → M` be a
length-minimising `C¹` curve on `[a, b]`. At every interior parameter
`t₀ ∈ (a, b)` there is a `δ > 0` such that the sub-arc
`γ |[t₀ - δ, t₀ + δ]` is (after monotone rescaling) the radial geodesic
`s ↦ expMap g (γ t₀) (s • v)` in normal coordinates at `γ t₀`, for some
tangent vector `v : TangentSpace I (γ t₀)`. -/
theorem local_radial_identification_of_minimizer
    (g : SmoothRiemannianMetric I M) {γ : ℝ → M} {a b : ℝ}
    (hγ : CMDiff[Icc a b] 1 γ)
    (hmin : riemannianEDist I (γ a) (γ b) = pathELength I γ a b)
    (hab : a ≤ b) {t₀ : ℝ} (ht₀ : t₀ ∈ Ioo a b) :
    ∃ δ : ℝ, 0 < δ ∧ Icc (t₀ - δ) (t₀ + δ) ⊆ Icc a b ∧
      ∃ v : TangentSpace I (γ t₀), ∀ s : ℝ, s ∈ Icc (-δ) δ →
        γ (t₀ + s) = expMap (I := I) g (γ t₀) (s • v) := by
  sorry

end LocalRadialIdentification

section ArclengthReparam

variable [I.Boundaryless] [CompleteSpace E] [T2Space (TangentBundle I M)]

/-! ## Global arclength reparametrisation is a smooth geodesic

Each local piece is a smooth unit-speed radial geodesic; overlap
consistency from `Geodesic/Uniqueness.lean` glues them into a global
smooth geodesic on `(0, L)`. -/

/-- **The arclength reparametrisation of a length-minimiser is a smooth
geodesic.** Given a length-minimising `C¹` curve `γ : [a, b] → M`, there
exist `L ≥ 0` and an arclength reparametrisation `η : ℝ → M` defined on
`[0, L]` such that `η` is a smooth geodesic on the open interval
`(0, L)`. -/
theorem arclength_reparam_is_smooth_geodesic
    (g : SmoothRiemannianMetric I M) {γ : ℝ → M} {a b : ℝ}
    (hγ : CMDiff[Icc a b] 1 γ)
    (hmin : riemannianEDist I (γ a) (γ b) = pathELength I γ a b)
    (hab : a ≤ b) :
    ∃ (L : ℝ) (η : ℝ → M), 0 ≤ L ∧ η 0 = γ a ∧ η L = γ b ∧
      (∀ t ∈ Ioo (0 : ℝ) L,
        ContMDiffAt 𝓘(ℝ, ℝ) I ∞ η t) ∧
      (∀ t ∈ Ioo (0 : ℝ) L,
        DifferentialGeometry.Geometry.Riemannian.Geodesic.IsGeodesicAt
          (I := I) g η t) := by
  sorry

end ArclengthReparam

end Riemannian
end Geometry
end DifferentialGeometry
