import DifferentialGeometry.Geometry.Riemannian.Variation.ParallelTransport
import DifferentialGeometry.Geometry.Riemannian.AlongCurve
import DifferentialGeometry.Geometry.Curvature.Riemann
import DifferentialGeometry.Integral.Connection.LeviCivita
import DifferentialGeometry.Integral.Connection.Curvature
import DifferentialGeometry.Integral.Connection.RicciIdentity
import DifferentialGeometry.Integral.Measure.ChartDensity
import Mathlib.Geometry.Manifold.ContMDiff.Defs
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# Fixed-chart variation identities

For a smooth two-parameter map `f : ℝ × ℝ → M`, with the basepoint of the
chart-local covariant derivative held at `f s t`, the mixed covariant
derivatives along the parameter directions commute (torsion-freeness) and
their commutator on a vector field `Y` along `f` equals the Riemann
curvature operator applied to `∂_s f`, `∂_t f`, `Y`.

Statements only — proofs are deferred.
-/

noncomputable section

open Set Function Filter Manifold Bundle
open scoped Topology Manifold ContDiff

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Variation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Riemannian.AlongCurve

/-! ## Smooth two-parameter variation -/

/-- A smooth two-parameter variation `f : ℝ → ℝ → M` is one whose
uncurried map `ℝ × ℝ → M` is jointly smooth. Since neither factor is a
manifold of positive geometric dimension carrying the project's
geometric structures, joint smoothness on `ℝ × ℝ` is admissible here. -/
def IsSmoothVariation
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    (f : ℝ → ℝ → M) : Prop :=
  ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) I ∞ (fun p : ℝ × ℝ => f p.1 p.2)

/-! ## Commutation of mixed covariant derivatives (fixed chart) -/

/-- Chart-bridge helper: for a smooth curve `g : ℝ → M` with
`g t₀ = α`, the manifold derivative of `g` at `t₀` applied to `1 : ℝ`,
viewed as an element of `E` via the canonical type synonym
`TangentSpace I (g t₀) := E`, coincides with the Fréchet derivative of
the chart-pulled-back curve `extChartAt I α ∘ g` at `t₀` applied to
`1 : ℝ`. The key input is `mfderiv_extChartAt_self`, which states that
`mfderiv I 𝓘(ℝ, E) (extChartAt I α) α` is the identity, combined with
the manifold chain rule. -/
private lemma mfderiv_eq_fderiv_extChartAt_at_basepoint
    (g : ℝ → M) (α : M) (t₀ : ℝ) (hg : MDifferentiableAt 𝓘(ℝ, ℝ) I g t₀)
    (hαβ : g t₀ = α) :
    (mfderiv 𝓘(ℝ, ℝ) I g t₀ (1 : ℝ) : E) =
      fderiv ℝ (fun u : ℝ => extChartAt I α (g u)) t₀ (1 : ℝ) := by
  classical
  -- `extChartAt I α` is `MDifferentiableAt` at `α = g t₀` (its source).
  have hext_mdiff : MDifferentiableAt I 𝓘(ℝ, E) (extChartAt I α) (g t₀) := by
    rw [hαβ]
    exact (contMDiffAt_extChartAt (I := I) (x := α) (n := 1)).mdifferentiableAt one_ne_zero
  -- Compose `extChartAt I α` with `g` at `t₀` via the manifold chain rule.
  have hcomp_mdiff : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E)
      (fun u : ℝ => extChartAt I α (g u)) t₀ := hext_mdiff.comp t₀ hg
  -- Manifold derivative of the composition is the composition of derivatives.
  have hchain :
      mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun u : ℝ => extChartAt I α (g u)) t₀
        = (mfderiv I 𝓘(ℝ, E) (extChartAt I α) (g t₀)).comp
            (mfderiv 𝓘(ℝ, ℝ) I g t₀) :=
    mfderiv_comp t₀ hext_mdiff hg
  -- At the basepoint `α`, `mfderiv (extChartAt I α) α = id`.
  have hself :
      mfderiv I 𝓘(ℝ, E) (extChartAt I α) α
        = ContinuousLinearMap.id ℝ E := mfderiv_extChartAt_self (I := I) (x := α)
  -- Convert the comp-id under `g t₀ = α`.
  rw [hαβ] at hchain
  rw [hself] at hchain
  -- Reduce `mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,E) F` to `fderiv ℝ F` for vector-space
  -- target via `mfderiv_eq_fderiv`.
  have hmfd_eq_fderiv :
      mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun u : ℝ => extChartAt I α (g u)) t₀
        = fderiv ℝ (fun u : ℝ => extChartAt I α (g u)) t₀ := mfderiv_eq_fderiv
  rw [hmfd_eq_fderiv] at hchain
  -- Apply both sides to `1 : ℝ`; the id-composition simplifies to the
  -- second factor.
  have happ := congrArg (fun L : ℝ →L[ℝ] E => L (1 : ℝ)) hchain
  exact happ.symm

/-- Fixed-chart variant of `commute_ds_dt`: the chart-local covariant
derivatives along the parameter directions of a smooth variation
commute when the chart basepoint is taken to be `f s t`.

**Mathematical sketch (partial; main proof deferred).** Unfolding
`chartCovDerivAlong`, both sides decompose as a deriv-of-section term
plus a Christoffel-contraction term. The Christoffel-contraction terms
agree by `chartChristoffelContraction_symm` together with the chart
bridge `mfderiv_eq_fderiv_extChartAt_at_basepoint` (above) applied at
the matching evaluation point. The residual identity is the
Schwarz-style swap of two `deriv`-of-`mfderiv` terms, which involves
the chart-transition Jacobian at the basepoint (since the `mfderiv`
trivialisation foot varies with the differentiation parameter). The
clean derivation of this residual identity from
`ContDiffAt.isSymmSndFDerivAt` applied to the chart-α-pushed map
`F (u, v) := extChartAt I (f s t) (f u v)`, modulo the chart-transition
correction, is the obligation for a follow-up step. -/
theorem commute_ds_dt_fixed_chart
    (g : SmoothRiemannianMetric I M) (f : ℝ → ℝ → M)
    (hf : IsSmoothVariation (I := I) f)
    (s t : ℝ) :
    chartCovDerivAlong (I := I) g (f s t) (fun u : ℝ => f u t)
      (fun u : ℝ => mfderiv (𝓘(ℝ, ℝ)) I (fun v : ℝ => f u v) t (1 : ℝ)) s
    = chartCovDerivAlong (I := I) g (f s t) (fun v : ℝ => f s v)
      (fun v : ℝ => mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f u v) s (1 : ℝ)) t := sorry

/-! ## Curvature identity on a variation (fixed chart) -/

/-- Fixed-chart variant of `curvature_identity_on_variation`: for a
vector field `Y` along a smooth two-parameter variation `f`, the
commutator of `∇_s` and `∇_t` taken with the chart basepoint pinned to
`f s t` equals the Riemann curvature operator applied to
`∂_s f`, `∂_t f`, and `Y`. -/
theorem curvature_identity_on_variation_fixed_chart
    (g : SmoothRiemannianMetric I M) (f : ℝ → ℝ → M)
    (hf : IsSmoothVariation (I := I) f)
    (Y : ℝ → ℝ → E) (s t : ℝ) :
    chartCovDerivAlong (I := I) g (f s t) (fun u : ℝ => f u t) (fun u : ℝ =>
        chartCovDerivAlong (I := I) g (f s t) (fun v : ℝ => f u v)
          (fun v : ℝ => Y u v) t) s
      - chartCovDerivAlong (I := I) g (f s t) (fun v : ℝ => f s v) (fun v : ℝ =>
        chartCovDerivAlong (I := I) g (f s t) (fun u : ℝ => f u v)
          (fun u : ℝ => Y u v) s) t
    = (DifferentialGeometry.Integral.Connection.riemannOp
        (DifferentialGeometry.Integral.Connection.LeviCivita
          (I := I) g) (f s t))
        (mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f u t) s (1 : ℝ))
        (mfderiv (𝓘(ℝ, ℝ)) I (fun v : ℝ => f s v) t (1 : ℝ))
        (Y s t) := sorry

end Variation
end Riemannian
end Geometry
end DifferentialGeometry

end
