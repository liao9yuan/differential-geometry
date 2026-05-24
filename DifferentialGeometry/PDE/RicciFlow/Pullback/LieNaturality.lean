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
DeTurck pullback chain of identities.

PROOF OUTLINE / GAP.

The proof has a clean three-line skeleton, but each line consumes infrastructure
that is not yet available:

  (1) Apply `cartan_formula_for_lie_deriv_metric` to both sides:
      LHS = (Φ*g).inner x (∇^{Φ*g}_v X) w + (Φ*g).inner x v (∇^{Φ*g}_w X)
      RHS = g.inner (Φx) (∇^g_{dΦv} (Φ*X)) (dΦw)
            + g.inner (Φx) (dΦv) (∇^g_{dΦw} (Φ*X))

  (2) Apply `pullback_metric_evaluation_formula` to convert each `(Φ*g).inner x`
      on the LHS into `g.inner (Φx)` composed with `mfderiv I I Φ x`:
      (Φ*g).inner x (∇^{Φ*g}_v X) w = g.inner (Φx) (dΦ (∇^{Φ*g}_v X)) (dΦ w).

  (3) Identify each LHS summand with the corresponding RHS summand via the
      **connection-pullback naturality identity**
        dΦ (∇^{Φ*g}_v X) = ∇^g_{dΦ v} (Φ_* X)        (★)
      (and symmetrically with `w` in place of `v`).

Identity (★) is the genuine missing ingredient. It says that the Levi-Civita
connection of the pullback metric, transported by the differential `dΦ`, agrees
with the Levi-Civita connection of `g` applied to the pushforward vector field.
This is the "tensorial" statement of `levi_civita_pullback_conjugation`, which
holds at the level of bundled `CovariantDerivative`s by `rfl`
(`covariant_derivative_of_pullback_vf_naturality`) but whose pointwise
unfolding into (★) requires either:

  (a) A Koszul-uniqueness lemma in the concrete (chart-coordinate) framework
      — analogous to `levi_civita_uniqueness` at the Synthetic layer
      (`Synthetic/Geometry/Connection.lean`) but instantiated for
      `LeviCivita (I := I) g` and its pullback. The Synthetic version proves
      that any torsion-free metric-compatible connection equals the Levi-Civita
      connection; transferring this through the
      `Synthetic/Realization/LeviCivita.lean` bridge to obtain (★) for the
      concrete `CovariantDerivative` is straightforward in principle but
      requires building the matching pullback-by-conjugation data in the
      Synthetic instance and then unfolding the bridge, totalling roughly
      400–600 new lines of infrastructure.

  (b) A direct chart-coordinate proof, expanding both sides of (★) via
      `chart_christoffel_expansion_of_nabla_on_vf` (proven in
      `CartanFormula.lean`) and the Jacobian-of-`Φ` transformation rule for
      Christoffel symbols. This involves the substitution
        chartChristoffel (Φ*g) at chart-of-x =
          [Jacobian and Hessian of Φ contributions]
            + chartChristoffel g at chart-of-Φx pulled back through `dΦ`,
      which is the classical "Christoffel symbols transform as a connection"
      identity. Formalizing this from scratch is approximately 800–1200 lines
      of chart-coordinate calculation, including the chain rule for the second
      derivative of a chart change and the matrix algebra to recombine terms.

Path (a) is the cleaner mathematical formulation; path (b) is more elementary
but longer. Neither fits in 800 lines without first laying down the missing
infrastructure (Koszul uniqueness at the concrete level OR the Christoffel-
transformation lemma) in separate files. The 800-line cap and "no new
def : Prop / class / axiom" constraints prevent both within this single fill.

DOWNSTREAM EFFECT.

The DeTurck pullback chain currently consumes
`lie_derivative_pullback_naturality` as a single black-box identity. Once (★)
is supplied (via either path), the chain closes by Cartan + the pullback
evaluation formula in roughly 60 lines of straightforward symbol-pushing,
which is well within the budget for the *next* iteration. -/
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
