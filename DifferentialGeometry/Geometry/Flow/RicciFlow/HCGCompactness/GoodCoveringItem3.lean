import DifferentialGeometry.Geometry.Comparison.ExpBallDiffeo
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.PointedRiemannian
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.GoodCoveringSeq

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# MSM135 Chapter 4 `lbl383` item 3 — per-manifold exp-ball diffeomorphism (B5 bridge)

The layer bridge from the Step A net (over `PointedRiemannianManifold`s `X.obj k`) to the
exponential ball diffeomorphism `exists_expBall_diffeo_of_lt` (`ExpBallDiffeo.lean`,
item 3a, unconditional): for a bundled pointed Riemannian manifold `Y`, a center `c : Y.M`,
and a radius `ρ` below both the injectivity radius and the `C²` radius of `Y.metric` at `c`,
the exponential map is a `C^1` partial diffeomorphism on `Metric.ball 0 ρ`.

This is the per-center half of `lbl383` item 3; the net-level instantiation (the radius
discipline `λ^α ≤ expMapC2Radius` — the book's "`D` large enough" choice — and the
universal clause over live centers) consumes this.
-/

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace HCGCompactness

open scoped Manifold ContDiff
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential

variable {E : Type uE} [NormedAddCommGroup E]
variable [InnerProductSpace Real E] [FiniteDimensional Real E]
variable [NeZero (Module.finrank Real E)] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable [I.Boundaryless]

/-- **`lbl383` item 3, per-manifold form.**  On a bundled pointed Riemannian manifold `Y`,
for a center `c` and radius `ρ ≤ expMapC2Radius Y.metric c` with
`ofReal ρ < injRadius Y.metric c`, the exponential map `expMap Y.metric c` restricts to a
`C^1` partial diffeomorphism with source `Metric.ball 0 ρ`.  The bundle's stored instances
(`Y.topology`, …, `Y.t2TangentBundle`) are installed locally; the nonsingularity input is
discharged inside `exists_expBall_diffeo_of_lt` from normal coordinates. -/
theorem PointedRiemannianManifold.exists_expBall_diffeo
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (c : Y.M) {ρ : Real} :
    letI := Y.topology
    letI := Y.charted
    letI := Y.smooth
    letI := Y.sigmaCompact
    letI := Y.t2
    letI := Y.t2TangentBundle
    ENNReal.ofReal ρ < injRadius (I := I) Y.metric c →
    ρ ≤ expMapC2Radius (I := I) Y.metric c →
      ∃ Φ : PartialDiffeomorph 𝓘(ℝ, E) I E Y.M 1,
        Φ.source = Metric.ball (0 : E) ρ ∧
        Φ.target = (fun v : E =>
          (expMap (I := I) Y.metric c (show TangentSpace I c from v) : Y.M)) ''
            Metric.ball (0 : E) ρ ∧
        Set.EqOn Φ (fun v : E =>
          (expMap (I := I) Y.metric c (show TangentSpace I c from v) : Y.M))
          (Metric.ball (0 : E) ρ) := by
  letI := Y.topology
  letI := Y.charted
  letI := Y.smooth
  letI := Y.sigmaCompact
  letI := Y.t2
  letI := Y.t2TangentBundle
  intro hinj hC2
  exact exists_expBall_diffeo_of_lt (I := I) Y.metric c hinj hC2

variable {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}

/-- **Honest-input (book "`D` large enough", `lbl391`/`lbl392`).**  At each live net center
`x_k^α`, the chosen item-3 ball radius `ρ k α` is below the exponential `C²` radius and the
injectivity radius of the realized metric `(X.obj k).metric`.  This is the §5 geometric
scale choice: the injectivity part follows from `InjRadiusDecayInput.decay` (for `D > 1`),
the `C²` part from the curvature-comparison `C²`-radius lower bound (the `lbl413`/§5
boundary).  `ProperMetricOn.realizes` identifies the net's `ms`-distance radii with the
Riemannian ones, so `ρ` is well-defined across the layer. -/
def Item3RadiusInput (hd : InjRadiusDecayInput (I := I) X) (D : Real)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k)) (ρ : Nat → Nat → Real) : Prop :=
  ∀ k α : Nat, ∀ c : (X.obj k).M, c ∈ seqCenter hd D P k α →
    letI := (X.obj k).topology
    letI := (X.obj k).charted
    letI := (X.obj k).smooth
    letI := (X.obj k).sigmaCompact
    letI := (X.obj k).t2
    letI := (X.obj k).t2TangentBundle
    ENNReal.ofReal (ρ k α) < injRadius (I := I) (X.obj k).metric c ∧
      ρ k α ≤ expMapC2Radius (I := I) (X.obj k).metric c

/-- **`lbl383` item 3, net-level producer.**  Given the radius-discipline input, every live
net center `x_k^α` carries the item-3 exponential ball diffeomorphism on `Metric.ball 0
(ρ k α)` of the realized metric `(X.obj k).metric`.  Reduces, per center, to the
per-manifold bridge `PointedRiemannianManifold.exists_expBall_diffeo`. -/
theorem exists_seqItem3Diffeo
    (hd : InjRadiusDecayInput (I := I) X) (D : Real)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k)) (ρ : Nat → Nat → Real)
    (hrad : Item3RadiusInput (I := I) hd D P ρ)
    (k α : Nat) (c : (X.obj k).M) (hc : c ∈ seqCenter hd D P k α) :
    letI := (X.obj k).topology
    letI := (X.obj k).charted
    letI := (X.obj k).smooth
    letI := (X.obj k).sigmaCompact
    letI := (X.obj k).t2
    letI := (X.obj k).t2TangentBundle
      ∃ Φ : PartialDiffeomorph 𝓘(ℝ, E) I E (X.obj k).M 1,
        Φ.source = Metric.ball (0 : E) (ρ k α) ∧
        Φ.target = (fun v : E =>
          (expMap (I := I) (X.obj k).metric c (show TangentSpace I c from v) :
            (X.obj k).M)) '' Metric.ball (0 : E) (ρ k α) ∧
        Set.EqOn Φ (fun v : E =>
          (expMap (I := I) (X.obj k).metric c (show TangentSpace I c from v) :
            (X.obj k).M))
          (Metric.ball (0 : E) (ρ k α)) :=
  (X.obj k).exists_expBall_diffeo c (hrad k α c hc).1 (hrad k α c hc).2

end HCGCompactness
end DifferentialGeometry
