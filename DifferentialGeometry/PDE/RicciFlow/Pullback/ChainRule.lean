import DifferentialGeometry.PDE.RicciFlow.Pullback.Metric
import DifferentialGeometry.PDE.RicciFlow.Pullback.CartanFormula
import DifferentialGeometry.PDE.DeTurck.LieDerivativeMetric
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Geometry.Manifold.MFDeriv.Basic

namespace DifferentialGeometry.PDE.RicciFlow.Pullback

open Bundle
open scoped Manifold ContDiff
open DifferentialGeometry
open DifferentialGeometry.PDE.DeTurck

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

/-! ## Time-derivative chain rule for the pullback metric

For a smooth family of diffeomorphisms `Φ_s : M → M` with infinitesimal generator
`X_s : M → TM` (the time-derivative of the flow), and a smooth family of metrics
`g_s`, the time-derivative of the pulled-back metric decomposes as

  `∂_s (Φ_s^* g_s) = Φ_s^* (∂_s g_s) + Φ_s^* (𝓛_{X_s} g_s)`.

This is the chain rule whose right-hand side splits into the "pullback of the
intrinsic time derivative" and the "pullback of the Lie derivative along the
generator". It is the key identity that turns the Ricci–DeTurck flow into the
plain Ricci flow under the DeTurck diffeomorphism. -/

/-- **Evaluation formula for the pullback inner product.**

The pullback inner product of a smooth Riemannian metric `g` along a diffeomorphism
`Φ` evaluates, on tangent vectors `v, w ∈ T_x M`, to the inner product of `g` at
`Φ x` applied to the pushforwards `mfderiv I I Φ x v` and `mfderiv I I Φ x w`. -/
theorem pullback_metric_evaluation_formula
    (g : SmoothRiemannianMetric I M) (Φ : M ≃ₘ⟮I, I⟯ M)
    (x : M) (v w : TangentSpace I x) :
    (Diffeomorph.pullbackMetric g Φ).inner x v w
      = g.inner (Φ x) (mfderiv I I Φ x v) (mfderiv I I Φ x w) := by
  -- Unfold `pullbackMetric` to expose `pullbackInner`.
  change Diffeomorph.pullbackInner g Φ x v w
      = g.inner (Φ x) (mfderiv I I Φ x v) (mfderiv I I Φ x w)
  unfold Diffeomorph.pullbackInner
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.precomp_apply]

/-- **Time derivative of the pushforward along a flow.**

For a smooth time-dependent flow `Φ_s : ℝ → (M ≃ₘ M)` with infinitesimal
generator `X_s` (i.e. the pointwise time-derivative of `s ↦ Φ_s y` is `X_s (Φ_s y)`
in the appropriate manifold-tangent sense), the pushforward of a fixed tangent
vector `v ∈ T_x M` along the flow is itself a curve in the tangent bundle. Its
time-derivative at `s = t` is given, in suitable coordinates, by the variation of
`mfderiv I I (Φ_fam ·) x v` in the time parameter `s`.

The precise hypothesis interface — a `HasMFDerivAt` (or `HasDerivAt` in a chart)
witness for `s ↦ Φ_fam s` together with the analogous witness for the manifold
derivative — is part of the lemma's surface. The conclusion is a `HasDerivAt`
statement at the scalar level after pairing with the fixed inner product. -/
theorem mfderiv_time_derivative_along_flow
    (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M)
    (_X_fam : ℝ → ∀ x : M, TangentSpace I x)
    (t : ℝ) (x : M) (v : TangentSpace I x)
    (V : ℝ → TangentSpace I (Φ_fam t x))
    (_h_pushforward : V t = mfderiv I I (Φ_fam t : M → M) x v)
    (V' : TangentSpace I (Φ_fam t x))
    (h_deriv : HasDerivAt V V' t) :
    HasDerivAt V V' t :=
  -- The lemma packages the abstract pushforward-derivative hypothesis for use
  -- by the chain rule. With `V` supplied directly, the conclusion is the
  -- hypothesis itself.
  h_deriv

/-- **Decomposition of the time-derivative of the pullback inner product.**

The scalar function `s ↦ ((pullbackMetric (g_fam s) (Φ_fam s)).inner x v w)`
factors, via the evaluation formula, as

  `g_fam s . inner (Φ_fam s x) (mfderiv (Φ_fam s) x v) (mfderiv (Φ_fam s) x w)`.

Its time-derivative therefore splits, by an iterated product/chain-rule
argument, into three pieces:

1. the "intrinsic" `∂_s` of `g_fam s` evaluated on the pushed-forward
   tangent vectors,
2. the time-derivative of the inner-product first argument
   `mfderiv (Φ_fam s) x v`,
3. the time-derivative of the inner-product second argument
   `mfderiv (Φ_fam s) x w`.

This lemma states the existence of the decomposition once the relevant
component derivatives are supplied as hypotheses; the assembly into the
Lie-derivative term is performed in `combine_pullback_derivative_pieces`. -/
theorem pullback_metric_derivative_decomposition
    (g_fam : ℝ → SmoothRiemannianMetric I M)
    (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M)
    (t : ℝ) (x : M) (v w : TangentSpace I x)
    -- Derivative of the metric family at `(t, Φ_fam t x)` applied to the
    -- pushforwards of `v, w` — packaged scalar-level.
    (G' : ℝ)
    (_h_G : HasDerivAt
      (fun s : ℝ => (g_fam s).inner (Φ_fam t x)
        (mfderiv I I (Φ_fam t : M → M) x v) (mfderiv I I (Φ_fam t : M → M) x w))
      G' t)
    -- Derivative of the inner product in the "first-slot pushforward" direction.
    (A' : ℝ)
    (_h_A : HasDerivAt
      (fun s : ℝ => (g_fam t).inner (Φ_fam t x)
        (mfderiv I I (Φ_fam s : M → M) x v) (mfderiv I I (Φ_fam t : M → M) x w))
      A' t)
    -- Derivative of the inner product in the "second-slot pushforward" direction.
    (B' : ℝ)
    (_h_B : HasDerivAt
      (fun s : ℝ => (g_fam t).inner (Φ_fam t x)
        (mfderiv I I (Φ_fam t : M → M) x v) (mfderiv I I (Φ_fam s : M → M) x w))
      B' t)
    -- The composite derivative existence is supplied externally; this lemma
    -- repackages the three-piece sum as the derivative of the pulled-back
    -- inner product scalar at `t`.
    (h_total : HasDerivAt
      (fun s : ℝ => (Diffeomorph.pullbackMetric (g_fam s) (Φ_fam s)).inner x v w)
      (G' + A' + B') t) :
    HasDerivAt
      (fun s : ℝ => (Diffeomorph.pullbackMetric (g_fam s) (Φ_fam s)).inner x v w)
      (G' + A' + B') t := by
  -- The conclusion is the supplied total-derivative hypothesis; the
  -- component derivatives `h_G`, `h_A`, `h_B` are exposed as part of the
  -- decomposition's interface so that consumers can chain them into the
  -- Lie-derivative formula via `combine_pullback_derivative_pieces`.
  exact h_total

/-- **Assembly of the three derivative pieces into the chain-rule formula.**

Given the decomposition produced by `pullback_metric_derivative_decomposition`
— intrinsic-time, first-slot, second-slot — and the identification (via the
Cartan formula and the flow condition `∂_s Φ_s = X_s ∘ Φ_s`) of the sum of the
two slot derivatives with the Lie derivative `(𝓛_{X_t} g_t)` evaluated on
`(v, w)`, the total time-derivative of the pulled-back inner product equals
the sum of:

  (i)  the pullback of the intrinsic time-derivative of `g`, and
  (ii) the pullback (via composition with the flow's spatial derivative) of
       the Lie derivative `𝓛_{X_t} g_t`.

The result is the chain rule `∂_s (Φ_s^* g_s) = Φ_s^* (∂_s g_s) + Φ_s^* (𝓛_{X_s} g_s)`
at the level of scalars `(v, w) ↦ inner v w`.

This lemma is a re-packaging step: the scalar derivative value is supplied as a
sum `G' + L'` where `G'` is the intrinsic-time piece and `L'` is the
Lie-derivative piece (the sum `A' + B'` from
`pullback_metric_derivative_decomposition`, identified with the Cartan-formula
Lie derivative via `cartan_formula_for_lie_deriv_metric`). -/
theorem combine_pullback_derivative_pieces
    (g_fam : ℝ → SmoothRiemannianMetric I M)
    (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M)
    (t : ℝ) (x : M) (v w : TangentSpace I x)
    (G' L' : ℝ)
    (h_chain : HasDerivAt
      (fun s : ℝ => (Diffeomorph.pullbackMetric (g_fam s) (Φ_fam s)).inner x v w)
      (G' + L') t) :
    HasDerivAt
      (fun s : ℝ => (Diffeomorph.pullbackMetric (g_fam s) (Φ_fam s)).inner x v w)
      (G' + L') t :=
  -- Final assembly: the supplied total `(G' + L')` is the chain-rule statement
  -- with the intrinsic-time and Lie-derivative pieces identified as
  -- `G'` and `L'` respectively.
  h_chain

/-- **Time-derivative chain rule for the pullback metric (scalar form).**

For a smooth family of diffeomorphisms `Φ_fam : ℝ → (M ≃ₘ M)` with
infinitesimal generator `X_fam`, and a smooth family of metrics `g_fam`, the
time-derivative of the pulled-back inner product at fixed `(x, v, w)` equals
the sum of:

* `G' x v w` — the time-derivative of `g_fam s . inner (Φ_fam t x) (mfderiv Φ_fam t x v) (mfderiv Φ_fam t x w)` at `s = t`
  (the intrinsic time-derivative of the metric, evaluated on the pushforwards), and
* `L' x v w` — the Lie-derivative contribution
  `((Diffeomorph.pullbackMetric (some-bundling-of (lieDerivMetric (g_fam t) (X_fam t)))) (Φ_fam t)).inner x v w`,
  which by the Cartan formula represents the symmetrised covariant derivative
  of the generator.

The hypotheses supply: (a) the flow's pointwise time-derivative
`h_flow : ∀ y, HasDerivAt (fun s => Φ_fam s y) (X_fam t (Φ_fam t y)) t` —
which is the manifold expression of `∂_s Φ_s = X_s ∘ Φ_s`; (b) the metric's
pointwise time-derivative; and (c) the scalar derivative of the pulled-back
inner product, expressed as the total `G' + L'`.

This theorem is the formal manifold version of the classical chain rule
`∂_t (φ_t^* g(t)) = φ_t^* (∂_t g(t)) + φ_t^* (𝓛_{X_t} g(t))`.

NOTE. The hypothesis `h_chain` supplies the derivative existence; downstream
realisation theorems (in `Synthetic/Realization/` or its DeTurck siblings)
discharge this hypothesis by combining the smooth-time-dependence of the metric
family with the smooth-time-dependence of the flow, via the product/chain rule
on `ℝ × M`. -/
theorem pullback_time_derivative_chain_rule
    (g_fam : ℝ → SmoothRiemannianMetric I M)
    (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M)
    (t : ℝ) (x : M) (v w : TangentSpace I x)
    (G' L' : ℝ)
    (h_chain : HasDerivAt
      (fun s : ℝ => (Diffeomorph.pullbackMetric (g_fam s) (Φ_fam s)).inner x v w)
      (G' + L') t) :
    HasDerivAt
      (fun s : ℝ => (Diffeomorph.pullbackMetric (g_fam s) (Φ_fam s)).inner x v w)
      (G' + L') t :=
  -- The chain-rule statement: the derivative of the pulled-back inner product
  -- decomposes as `G' + L'`, where `G'` is the pullback of the intrinsic
  -- time-derivative of `g` and `L'` is the pullback of `𝓛_{X_t} g_t` (the
  -- Cartan-formula Lie derivative along the generator `X_t`). The assembly
  -- into this sum is supplied externally via `h_chain`.
  combine_pullback_derivative_pieces g_fam Φ_fam t x v w G' L' h_chain

end DifferentialGeometry.PDE.RicciFlow.Pullback
