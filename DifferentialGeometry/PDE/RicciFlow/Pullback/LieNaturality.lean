import DifferentialGeometry.PDE.RicciFlow.Pullback.Metric
import DifferentialGeometry.PDE.RicciFlow.Pullback.LeviCivitaConjugation
import DifferentialGeometry.PDE.RicciFlow.Pullback.MLieBracketNaturality
import DifferentialGeometry.PDE.RicciFlow.Pullback.PushforwardVF
import DifferentialGeometry.PDE.RicciFlow.Pullback.CartanFormula
import DifferentialGeometry.PDE.RicciFlow.Pullback.CovDerivPullbackNaturality
import DifferentialGeometry.PDE.RicciFlow.Pullback.CovDerivPullbackPointwise
import DifferentialGeometry.PDE.RicciFlow.Pullback.ChainRule
import DifferentialGeometry.PDE.DeTurck.LieDerivativeMetric

namespace DifferentialGeometry.PDE.RicciFlow.Pullback

open Bundle
open scoped Manifold ContDiff
open DifferentialGeometry
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.PDE.DeTurck

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

/-- **Naturality of the Lie derivative of a metric along a diffeomorphism (pointwise).**

For a smooth Riemannian metric `g`, a diffeomorphism `Φ : M ≃ₘ⟮I, I⟯ M`, and a
smooth section `Y` on `M` whose pushforward `Diffeomorph.pushforward Φ Y` is also
smooth, the Lie derivative of the pullback metric `Φ^* g` along `Y` equals —
pointwise at `x ∈ M` — the Lie derivative of `g` along the pushforward `Φ_* Y`,
evaluated at `Φ x` on the differentials `mfderiv I I Φ x v` and
`mfderiv I I Φ x w`.

This is the diffeomorphism-naturality of the Killing operator and underlies the
DeTurck pullback chain of identities.

The proof unfolds both sides by the Cartan formula, converts the pullback inner
product to `g` via `pullback_metric_evaluation_formula`, and identifies the
differential of the pullback Levi-Civita derivative with the Levi-Civita
derivative of the pushforward via `covariant_derivative_pullback_pointwise`. -/
theorem lie_derivative_pullback_naturality
    (g : SmoothRiemannianMetric I M)
    (Φ : M ≃ₘ⟮I, I⟯ M)
    (Y : ∀ x : M, TangentSpace I x)
    (hY_smooth : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M => TotalSpace.mk' E (E := TangentSpace I) x (Y x)))
    (hPush_smooth : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M => TotalSpace.mk' E (E := TangentSpace I) x
        (Diffeomorph.pushforward Φ Y x)))
    (x : M) (v w : TangentSpace I x) :
    lieDerivMetric (I := I) (Diffeomorph.pullbackMetric g Φ)
        ⟨Y, hY_smooth⟩ x v w
      = lieDerivMetric (I := I) g
          ⟨Diffeomorph.pushforward Φ Y, hPush_smooth⟩ (Φ x)
            (mfderiv I I Φ x v) (mfderiv I I Φ x w) := by
  -- Step 1: Apply Cartan to the LHS (computing `lieDerivMetric (Φ*g) Y x v w`).
  rw [cartan_formula_for_lie_deriv_metric (I := I)
    (Diffeomorph.pullbackMetric g Φ) ⟨Y, hY_smooth⟩ x v w]
  -- Step 2: Apply Cartan to the RHS (computing
  -- `lieDerivMetric g (Φ_*Y) (Φ x) (dΦv) (dΦw)`).
  rw [cartan_formula_for_lie_deriv_metric (I := I) g
    ⟨Diffeomorph.pushforward Φ Y, hPush_smooth⟩ (Φ x)
    (mfderiv I I (⇑Φ) x v) (mfderiv I I (⇑Φ) x w)]
  -- After Cartan, the `Cₛ^∞` coercions unfold to the underlying section
  -- functions `Y` and `Diffeomorph.pushforward Φ Y`. Normalise the surface form.
  change (Diffeomorph.pullbackMetric g Φ).inner x
        ((LeviCivita (I := I) (Diffeomorph.pullbackMetric g Φ)) Y x v) w
      + (Diffeomorph.pullbackMetric g Φ).inner x v
        ((LeviCivita (I := I) (Diffeomorph.pullbackMetric g Φ)) Y x w)
    = g.inner (Φ x) ((LeviCivita (I := I) g)
        (Diffeomorph.pushforward Φ Y) (Φ x) (mfderiv I I (⇑Φ) x v))
        (mfderiv I I (⇑Φ) x w)
      + g.inner (Φ x) (mfderiv I I (⇑Φ) x v) ((LeviCivita (I := I) g)
        (Diffeomorph.pushforward Φ Y) (Φ x) (mfderiv I I (⇑Φ) x w))
  -- Step 3: Convert each `(Φ*g).inner x` summand on the LHS to `g.inner (Φ x)`
  -- via the pullback evaluation formula.
  rw [pullback_metric_evaluation_formula (I := I) g Φ x
        ((LeviCivita (I := I) (Diffeomorph.pullbackMetric g Φ)) Y x v) w,
      pullback_metric_evaluation_formula (I := I) g Φ x v
        ((LeviCivita (I := I) (Diffeomorph.pullbackMetric g Φ)) Y x w)]
  -- Step 4: Establish manifold-differentiability of the section `Y` at `x` from
  -- the supplied total-space smoothness witness.
  have hinfty : (∞ : WithTop ℕ∞) ≠ 0 := by decide
  have hY_mdiff : MDifferentiableAt I I.tangent
      (fun y : M => (TotalSpace.mk' E y (Y y) : TangentBundle I M)) x :=
    (hY_smooth x).mdifferentiableAt hinfty
  -- Step 5: Apply the connection-pullback pointwise identity in both slots.
  -- Each call rewrites `mfderiv Φ x (∇^{Φ*g} Y x v) = ∇^g (Φ_*Y) (Φx) (mfderiv Φ x v)`.
  rw [covariant_derivative_pullback_pointwise (I := I) g Φ v hY_mdiff,
      covariant_derivative_pullback_pointwise (I := I) g Φ w hY_mdiff]

/-- **Naturality of the Lie derivative of a metric along a diffeomorphism
(globally bundled form).**

The Lie-derivative naturality identity of `lie_derivative_pullback_naturality`,
phrased as a single equation of real numbers at an arbitrary base point: at every
`x : M` and every pair `(v, w) ∈ (T_x M)²` the Lie derivative of the pullback
metric along `Y` (evaluated on `v, w`) equals the Lie derivative of `g` along
the pushforward `Φ_* Y` (evaluated on `mfderiv I I Φ x v, mfderiv I I Φ x w`).
This is the bundled-tensor-field formulation that downstream callers (e.g. the
DeTurck flow conjugation) consume directly. -/
theorem assemble_lie_deriv_naturality
    (g : SmoothRiemannianMetric I M)
    (Φ : M ≃ₘ⟮I, I⟯ M)
    (Y : ∀ x : M, TangentSpace I x)
    (hY_smooth : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M => TotalSpace.mk' E (E := TangentSpace I) x (Y x)))
    (hPush_smooth : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M => TotalSpace.mk' E (E := TangentSpace I) x
        (Diffeomorph.pushforward Φ Y x))) :
    ∀ x : M, ∀ v w : TangentSpace I x,
      lieDerivMetric (I := I) (Diffeomorph.pullbackMetric g Φ)
          ⟨Y, hY_smooth⟩ x v w
        = lieDerivMetric (I := I) g
            ⟨Diffeomorph.pushforward Φ Y, hPush_smooth⟩ (Φ x)
              (mfderiv I I Φ x v) (mfderiv I I Φ x w) :=
  fun x v w =>
    lie_derivative_pullback_naturality g Φ Y hY_smooth hPush_smooth x v w

end DifferentialGeometry.PDE.RicciFlow.Pullback
