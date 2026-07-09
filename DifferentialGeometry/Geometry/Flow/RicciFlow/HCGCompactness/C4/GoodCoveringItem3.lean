import DifferentialGeometry.Geometry.Comparison.ExpBallDiffeo
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.PointedRiemannian
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.GoodCoveringSeq

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

namespace Item3RadiusInput

/-- Reindex item-3 radius discipline along a subsequence. -/
theorem subseq (hd : InjRadiusDecayInput (I := I) X) (D : Real)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k)) (ρ : Nat → Nat → Real)
    (hrad : Item3RadiusInput (I := I) hd D P ρ) (f : Nat -> Nat) :
    Item3RadiusInput (I := I) (hd.subseq f) D (fun k => P (f k))
      (fun k α => ρ (f k) α) := by
  intro k α c hc
  have hc' : c ∈ seqCenter hd D P (f k) α := by
    simpa [seqCenter, InjRadiusDecayInput.subseq, InjRadiusDecayInput.lambda,
      InjRadiusDecayInput.mu, PointedRiemannianSeq.subseq] using hc
  simpa [InjRadiusDecayInput.subseq, PointedRiemannianSeq.subseq] using
    hrad (f k) α c hc'

end Item3RadiusInput

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

/-- **`lbl383`/`lbl427` `g_p`-scale honest input** (book-external; sibling of
`Item3RadiusInput`).  At every live net center `x_{L.φ n}^γ` the center-of-mass ball
scale `4 λ^γ` sits below the `g_p`-coercive radial normal radius `expRadiusGp` of the
realized metric.  This is the book's ball-scale choice (`lbl383`, applied at `lbl427`'s
convexity radius `r < min{inj/3, π/(6√K)}`; cf. chapter4.tex L1672 "by the choice of
balls in Lemma `lbl383` we can apply Proposition `lbl434`").  Like `Item3RadiusInput`
the comparison is a `§5`/`lbl413` curvature-comparison boundary and is un-provable
natively because `expMapC2Radius` — hence `expRadiusGp = √(g_p-coercive) · expMapC2Radius`
— is an opaque choice radius (the same uniform-radius-anchoring frontier as
`Item3RadiusInput`).  Stated `L`-relative with `L.lamInf` so the `unifHatCageSelfComp`
hypothesis `hR` (`4 * L.lamInf γ < expRadiusGp … (center γ)`) is a one-line
consequence at each live center. -/
def Item3GpScaleInput (hd : InjRadiusDecayInput (I := I) X) (D : Real)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData (I := I) hd D P) : Prop :=
  ∀ n γ : Nat, ∀ c : (X.obj (L.φ n)).M,
    seqCenter hd D P (L.φ n) γ = some c →
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
      letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
        (X.obj (L.φ n)).t2TangentBundle
      4 * L.lamInf γ < expRadiusGp (I := I) (X.obj (L.φ n)).metric c

/-- Reindex the `g_p`-scale input along a further subsequence: `L.subseq hψ` shares
`L`'s `lamInf` and reindexes `φ` by `ψ`, so the scale separation transports directly. -/
theorem Item3GpScaleInput.subseq (hd : InjRadiusDecayInput (I := I) X) (D : Real)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData (I := I) hd D P)
    (hgp : Item3GpScaleInput (I := I) hd D P L)
    {ψ : Nat → Nat} (hψ : StrictMono ψ) :
    Item3GpScaleInput (I := I) hd D P (L.subseq hψ) := by
  intro n γ c hc
  exact hgp (ψ n) γ c hc

end HCGCompactness
end DifferentialGeometry
