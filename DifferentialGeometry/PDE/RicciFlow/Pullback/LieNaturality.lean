import DifferentialGeometry.PDE.RicciFlow.Pullback.Metric
import DifferentialGeometry.PDE.RicciFlow.Pullback.LeviCivitaConjugation
import DifferentialGeometry.PDE.RicciFlow.Pullback.MLieBracketNaturality
import DifferentialGeometry.PDE.RicciFlow.Pullback.PushforwardVF
import DifferentialGeometry.PDE.RicciFlow.Pullback.CartanFormula
import DifferentialGeometry.PDE.RicciFlow.Pullback.CovDerivPullbackNaturality
import DifferentialGeometry.PDE.DeTurck.LieDerivativeMetric

namespace DifferentialGeometry.PDE.RicciFlow.Pullback

open Bundle
open scoped Manifold ContDiff
open DifferentialGeometry
open DifferentialGeometry.PDE.DeTurck

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

/-- **Naturality of the Lie derivative of a metric along a diffeomorphism (pointwise).**

For a smooth Riemannian metric `g`, a diffeomorphism `Φ : M ≃ₘ⟮I, I⟯ M`, and a
smooth vector field `X` whose `Diffeomorph.pushforward Φ X` is also smooth, the
Lie derivative of the pullback metric along `X` equals — pointwise — the
Lie derivative of `g` along the pushforward `Φ_* X`, transported back along
`mfderiv I I Φ x` in both slots.

More precisely, packaging `X` and `Diffeomorph.pushforward Φ X` as
`Cₛ^∞`-sections via the supplied smoothness witnesses, the bundled
`(0,2)`-tensor field `𝓛_X (Φ^* g)` evaluated at `(v, w) ∈ (T_x M)²` coincides
with `𝓛_{Φ_* X} g` at `Φ x` evaluated on `(mfderiv I I Φ x v, mfderiv I I Φ x w)`.

This is the diffeomorphism-naturality of the Killing operator and underlies the
DeTurck pullback chain of identities. -/
theorem lie_derivative_pullback_naturality
    (g : SmoothRiemannianMetric I M)
    (Φ : M ≃ₘ⟮I, I⟯ M)
    (X : ∀ x : M, TangentSpace I x)
    (hX_smooth : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M => TotalSpace.mk' E (E := TangentSpace I) x (X x)))
    (hPush_smooth : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M => TotalSpace.mk' E (E := TangentSpace I) x
        (Diffeomorph.pushforward Φ X x)))
    (x : M) (v w : TangentSpace I x) :
    lieDerivMetric (I := I) (Diffeomorph.pullbackMetric g Φ)
        ⟨X, hX_smooth⟩ x v w
      = lieDerivMetric (I := I) g
          ⟨Diffeomorph.pushforward Φ X, hPush_smooth⟩ (Φ x)
            (mfderiv I I Φ x v) (mfderiv I I Φ x w) := sorry

/-- **Naturality of the Lie derivative of a metric along a diffeomorphism
(globally bundled form).**

The Lie-derivative naturality identity of `lie_derivative_pullback_naturality`,
phrased as a single equation of real numbers at an arbitrary base point: at every
`x : M` and every pair `(v, w) ∈ (T_x M)²` the Lie derivative of the pullback
metric along `X` (evaluated on `v, w`) equals the Lie derivative of `g` along
the pushforward `Φ_* X` (evaluated on `mfderiv I I Φ x v, mfderiv I I Φ x w`).
This is the bundled-tensor-field formulation that downstream callers (e.g. the
DeTurck flow conjugation) consume directly. -/
theorem assemble_lie_deriv_naturality
    (g : SmoothRiemannianMetric I M)
    (Φ : M ≃ₘ⟮I, I⟯ M)
    (X : ∀ x : M, TangentSpace I x)
    (hX_smooth : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M => TotalSpace.mk' E (E := TangentSpace I) x (X x)))
    (hPush_smooth : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M => TotalSpace.mk' E (E := TangentSpace I) x
        (Diffeomorph.pushforward Φ X x))) :
    ∀ x : M, ∀ v w : TangentSpace I x,
      lieDerivMetric (I := I) (Diffeomorph.pullbackMetric g Φ)
          ⟨X, hX_smooth⟩ x v w
        = lieDerivMetric (I := I) g
            ⟨Diffeomorph.pushforward Φ X, hPush_smooth⟩ (Φ x)
              (mfderiv I I Φ x v) (mfderiv I I Φ x w) :=
  fun x v w =>
    lie_derivative_pullback_naturality g Φ X hX_smooth hPush_smooth x v w

end DifferentialGeometry.PDE.RicciFlow.Pullback
