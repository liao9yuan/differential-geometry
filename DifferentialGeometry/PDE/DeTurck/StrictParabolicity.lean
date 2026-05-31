import DifferentialGeometry.PDE.DeTurck.RicciLinearization.RicciSymbol
import DifferentialGeometry.PDE.DeTurck.DeTurckLinearization.DeTurckCorrectionSymbol
import DifferentialGeometry.PDE.DeTurck.Transformation

/-!
# Strict parabolicity of the Ricci–DeTurck operator

This file is the capstone of the DeTurck-transformation development.  It assembles the
principal symbol of the **Ricci–DeTurck operator**

$$\mathcal D(g, g') \;=\; -2\,\operatorname{Rc}(g) \;+\; \mathcal L_{W(g, g')}\,g$$

(the right-hand side of the Ricci–DeTurck flow `∂_t g = −2 Rc(g) + 𝓛_W g`,
`deTurckOp`) out of the two linearized symbols already proved, and shows that on the
symmetric `(0,2)`-tensors — the space the metric perturbation actually lives in — the
symbol is the **isotropic** symbol `|ξ|²_g · id`.  That is the statement that the
Ricci–DeTurck flow is strictly parabolic.

## The gauge cancellation

Bare Ricci flow `∂_t g = −2 Rc(g)` is only *weakly* parabolic: the linearized Ricci
operator has a large kernel — the diffeomorphism (gauge) directions — so its principal
symbol fails to be positive-definite.  Concretely, the linearized-Ricci symbol carries
two "gauge" terms,
$$(\sigma_{\mathrm{Rc}}(\xi)(t))_{ik}
    = \tfrac12\,\xi_i\,(t\xi)_k + \tfrac12\,\xi_k\,(\xi t)_i
      - \tfrac12\,|\xi|^2_g\, t_{ik} - \tfrac12\,\xi_i\xi_k\,\operatorname{tr}_g t,$$
where `(t ξ)_k = ∑_l ξ^l t_{lk}` and `(ξ t)_i = ∑_l ξ^l t_{il}` are the first- and
second-slot raised contractions: only the third term `−½|ξ|²_g t_{ik}` is isotropic.

The DeTurck modification adds the Lie-derivative term `𝓛_{W} g`.  Its linearization's
principal symbol is the **gauge symbol**
$$(\sigma_{\mathrm{DT}}(\xi)(t))_{ik}
    = \xi_i\,(\xi t)_k + \xi_k\,(\xi t)_i - \xi_i\xi_k\,\operatorname{tr}_g t.$$
Forming the symbol of the Ricci–DeTurck operator `−2 Rc(g) + 𝓛_W g`, i.e.
`−2·σ_Rc + σ_DT`, the off-diagonal gauge terms combine to
$$(-2\,\sigma_{\mathrm{Rc}} + \sigma_{\mathrm{DT}})(\xi)(t)_{ik}
    = \xi_i\,\bigl((\xi t)_k - (t\xi)_k\bigr) + |\xi|^2_g\, t_{ik}.$$
For a **symmetric** input `t` (`t_{lk} = t_{kl}`) the two raised contractions agree,
`(\xi t)_k = (t\xi)_k`, so the gauge term `ξ_i((ξt)_k − (tξ)_k)` vanishes and only the
isotropic term survives:
$$(-2\,\sigma_{\mathrm{Rc}} + \sigma_{\mathrm{DT}})(\xi)(t)_{ik} = |\xi|^2_g\, t_{ik}.$$
This is the **DeTurck cancellation**: the DeTurck term exactly cancels the gauge kernel
of the linearized Ricci operator, leaving the isotropic symbol `|ξ|²_g · id`.  Since
`|ξ|²_g > 0` for `ξ ≠ 0`, the symbol is positive-definite — the Ricci–DeTurck flow is a
strictly parabolic system.  The metric perturbation is always a symmetric `(0,2)`-tensor,
so the symmetric-input restriction is exactly the right setting.

## Sign convention

The component formulas `ricciSymbol_apply_eq_closedForm` and
`deTurckCorrectionSymbol_apply_eq_closedForm` were both built with the principal-symbol
substitution `∂_a∂_b ↦ +ξ_aξ_b`, so the cancellation computed above genuinely yields the
**positive** isotropic symbol `+|ξ|²_g · id`.  This is the correct sign for a parabolic
right-hand side: the evolution `∂_t g = 𝒟(g, g')` has, after linearization, leading part
`+|ξ|²_g`-times the identity, exactly as the heat equation `∂_t u = Δu` has — in the same
`∂_a∂_b ↦ +ξ_aξ_b` reading of the symbol — leading part `+|ξ|²` (the geometer's
`Δ = div ∘ grad` is `∑ g^{ij} ∂_i∂_j + …`).  Accordingly the headline statements here are
phrased with the `+` sign, the genuine output of the closed forms.

## Main definitions

* `deTurckSymbol g g'` — the **principal symbol of the Ricci–DeTurck operator**, the
  pointwise linear combination `−2 · ricciSymbol g + deTurckCorrectionSymbol g g'` of the
  linearized-Ricci and linearized-DeTurck-correction symbols, as a `TensorSymbol I M`.

## Main results

* `raisedFormContraction_eq_snd_of_symm` — for a symmetric input `t` the first- and
  second-slot raised contractions of `t` coincide.
* `deTurckSymbol_apply_apply_eq_isotropic_of_symm` — the **gauge-cancellation theorem**:
  on a symmetric input `t`, the chart components of `deTurckSymbol g g' x ξ t` are
  isotropic, `(deTurckSymbol g g' x ξ t)_{ik} = |ξ|²_g · t_{ik}`.
* `deTurckSymbol_apply_eq_smul_of_symm` — the **isotropy theorem**: on a symmetric input
  `t`, `deTurckSymbol g g' x ξ t = |ξ|²_g • t` as bilinear forms.
* `deTurckSymbol_isStrictlyParabolic_of_symm` — the **strict-parabolicity capstone**: for every
  base point `x`, every nonzero covector `ξ`, and every symmetric input tensor `t`,
  `deTurckSymbol g g' x ξ t = |ξ|²_g • t` with `|ξ|²_g > 0` — the symbol of the
  Ricci–DeTurck operator is the positive-definite isotropic symbol `|ξ|²_g · id` on
  symmetric tensors.

## Conventions

A covector at `x` is recorded as a model vector `ξ : E`, with chart components
`ξ_a = (chartModelBasis E).repr ξ a` (the same convention as `Symbol.lean`,
`RicciSymbol.lean`, and `DeTurckCorrectionSymbol.lean`).  The fibre `TangentSpace I x` is
definitionally the model space `E`, so the model-basis vectors `chartModelBasis E i` are
admissible arguments of a fibre bilinear form.  "Symmetric input tensor" means a fibre
bilinear form `t` with `t v w = t w v` for all `v, w` — the form a metric perturbation
takes.
-/

noncomputable section

open Set Function
open scoped Topology ContDiff Matrix Manifold

namespace DifferentialGeometry
namespace PDE
namespace DeTurck

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.PDE.DeTurck.RicciLinearization
open DifferentialGeometry.PDE.DeTurck.DeTurckLinearization

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

/-! ## The principal symbol of the Ricci–DeTurck operator

The Ricci–DeTurck operator is `𝒟(g, g') = −2 Rc(g) + 𝓛_{W(g,g')} g`.  Differentiating in
`g` and reading off the leading (second-order) part, its principal symbol is the same
linear combination of the symbols of the two summands:
`σ(𝒟) = −2 · σ(Rc) + σ(𝓛_W g)`.  The first factor is the bundled linearized-Ricci symbol
`ricciSymbol g`; the second is the bundled linearized-DeTurck-correction symbol
`deTurckCorrectionSymbol g g'`.  Both are `TensorSymbol I M`s — fibrewise linear
endomorphisms of the `(0,2)`-tensor fibre — and `TensorSymbol I M` values at a fixed
`(x, ξ)` are `LinearMap`s, an `ℝ`-module, so the combination `−2 • _ + _` is again a
`TensorSymbol I M`. -/

/-- The **principal symbol of the Ricci–DeTurck operator** `𝒟(g, g') = −2 Rc(g) + 𝓛_W g`,
as a `TensorSymbol I M`.

At each base point `x` and covector `ξ` it is the fibrewise linear endomorphism of the
`(0,2)`-tensor fibre obtained as the linear combination
$$\sigma(\mathcal D)(x, \xi) \;=\; -2\,\sigma(\operatorname{Rc})(x, \xi)
    \;+\; \sigma(\mathcal L_W g)(x, \xi)$$
of the bundled linearized-Ricci symbol `ricciSymbol g` and the bundled
linearized-DeTurck-correction symbol `deTurckCorrectionSymbol g g'` — the principal
symbol of the right-hand side of the Ricci–DeTurck flow.  The combination is taken
pointwise in the `ℝ`-module of fibre endomorphisms `LinearMap`. -/
def deTurckSymbol (g g' : SmoothRiemannianMetric I M) : TensorSymbol (E := E) I M :=
  fun x ξ => (-2 : ℝ) • ricciSymbol (I := I) g x ξ +
    deTurckCorrectionSymbol (I := I) g g' x ξ

/-- Unfolding lemma for `deTurckSymbol`: at `(x, ξ)` it is the linear combination
`−2 • ricciSymbol g x ξ + deTurckCorrectionSymbol g g' x ξ` of the two bundled symbols. -/
lemma deTurckSymbol_def (g g' : SmoothRiemannianMetric I M) (x : M) (ξ : E) :
    deTurckSymbol (I := I) g g' x ξ =
      (-2 : ℝ) • ricciSymbol (I := I) g x ξ +
        deTurckCorrectionSymbol (I := I) g g' x ξ := rfl

/-- The Ricci–DeTurck symbol applied to an input bilinear form `t` is the linear
combination `−2 • (ricciSymbol g x ξ t) + (deTurckCorrectionSymbol g g' x ξ t)` of the
two summand symbols' outputs. -/
@[simp] lemma deTurckSymbol_apply (g g' : SmoothRiemannianMetric I M) (x : M) (ξ : E)
    (t : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ) :
    deTurckSymbol (I := I) g g' x ξ t =
      (-2 : ℝ) • ricciSymbol (I := I) g x ξ t +
        deTurckCorrectionSymbol (I := I) g g' x ξ t := by
  rw [deTurckSymbol_def, LinearMap.add_apply, LinearMap.smul_apply]

/-- Evaluation of the Ricci–DeTurck symbol's output on a pair of fibre vectors: the
combination `−2 · (ricciSymbol g x ξ t)(v, w) + (deTurckCorrectionSymbol g g' x ξ t)(v, w)`
of the two summand outputs. -/
lemma deTurckSymbol_apply_apply (g g' : SmoothRiemannianMetric I M) (x : M) (ξ : E)
    (t : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ)
    (v w : TangentSpace I x) :
    (deTurckSymbol (I := I) g g' x ξ t) v w =
      -2 * (ricciSymbol (I := I) g x ξ t) v w +
        (deTurckCorrectionSymbol (I := I) g g' x ξ t) v w := by
  rw [deTurckSymbol_apply, LinearMap.add_apply, LinearMap.smul_apply,
    LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]

/-! ## The symmetric-input raise identity

The gauge cancellation rests on a single fact about symmetric bilinear forms.  The
linearized-Ricci closed form raises the **first** index of `t`
(`raisedFormContraction g x ξ t k = ∑_l ξ^l t_{lk}`), while the
linearized-DeTurck-correction closed form raises the **second** index
(`raisedFormContractionSnd g x ξ t k = ∑_l ξ^l t_{kl}`).  On a symmetric input these two
contractions coincide, because `t_{lk} = t_{kl}` term by term.

`RicciSymbolFormula.lean` already records `raisedFormContractionSnd_eq_of_symm`
(`raisedFormContractionSnd = raisedFormContraction` on a symmetric input).  We restate it
in the opposite orientation — `raisedFormContraction = raisedFormContractionSnd` — which
is the orientation the cancellation computation consumes. -/

/-- **The two raised contractions agree on a symmetric input.**

For a symmetric fibre bilinear form `t` (`t v w = t w v`), the first-slot raised
contraction `raisedFormContraction g x ξ t k = ∑_l ξ^l t_{lk}` equals the second-slot
raised contraction `raisedFormContractionSnd g x ξ t k = ∑_l ξ^l t_{kl}`:
$$\sum_l \xi^l\, t_{lk} \;=\; \sum_l \xi^l\, t_{kl}.$$

This is `raisedFormContractionSnd_eq_of_symm` read in the opposite orientation; it is the
single fact that makes the off-diagonal gauge terms of `deTurckSymbol` cancel. -/
lemma raisedFormContraction_eq_snd_of_symm (g : SmoothRiemannianMetric I M) (x : M)
    (ξ : E) (t : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ)
    (ht : ∀ v w, t v w = t w v) (k : Fin (Module.finrank ℝ E)) :
    raisedFormContraction (I := I) g x ξ t k =
      raisedFormContractionSnd (I := I) g x ξ t k :=
  (raisedFormContractionSnd_eq_of_symm (I := I) g x ξ t ht k).symm

/-! ## The gauge-cancellation theorem

We now combine the two closed forms.  Evaluating `deTurckSymbol g g' x ξ t` on the
model-basis vectors `e_i, e_k` and substituting the closed-form components

* `(ricciSymbol g x ξ t)(e_i, e_k)`
    `= ½ ξ_i (tξ)_k + ½ ξ_k (ξt)_i − ½ |ξ|²_g t_{ik} − ½ ξ_iξ_k tr_g t`,
* `(deTurckCorrectionSymbol g g' x ξ t)(e_i, e_k)`
    `= ξ_i (ξt)_k + ξ_k (ξt)_i − ξ_iξ_k tr_g t`,

the `−2 • _ + _` combination is the literal real-algebra identity
$$-2\bigl[\tfrac12\xi_i(t\xi)_k + \tfrac12\xi_k(\xi t)_i
        - \tfrac12|\xi|^2_g t_{ik} - \tfrac12\xi_i\xi_k\operatorname{tr}_g t\bigr]
  + \bigl[\xi_i(\xi t)_k + \xi_k(\xi t)_i - \xi_i\xi_k\operatorname{tr}_g t\bigr]
  \;=\; \xi_i\bigl((\xi t)_k - (t\xi)_k\bigr) + |\xi|^2_g\, t_{ik},$$
the `ξ_k(ξt)_i` and `ξ_iξ_k tr_g t` terms cancelling outright.  On a symmetric input
`(t ξ)_k = (\xi t)_k` (`raisedFormContraction_eq_snd_of_symm`), so the residual gauge
term `ξ_i((ξt)_k − (tξ)_k)` is zero and the value is exactly `|ξ|²_g t_{ik}`. -/

/-- **The gauge-cancellation theorem.**

On a **symmetric** input bilinear form `t` (`t v w = t w v` — the form a metric
perturbation takes), the chart components of the Ricci–DeTurck symbol `deTurckSymbol g g'`
are *isotropic*:
$$(\sigma(\mathcal D)(x, \xi)(t))_{ik} \;=\; |\xi|^2_g\, t_{ik}.$$

This is the DeTurck cancellation in components.  Substituting the closed forms
`ricciSymbol_apply_eq_closedForm` and `deTurckCorrectionSymbol_apply_eq_closedForm`, the
`−2 • σ_Rc + σ_DT` combination has all gauge (off-diagonal, raised-contraction and trace)
terms cancel except `ξ_i((ξt)_k − (tξ)_k)`; the symmetric-input identity
`raisedFormContraction_eq_snd_of_symm` then kills that residual term, leaving the single
isotropic term `|ξ|²_g t_{ik}`.  The DeTurck term has exactly cancelled the gauge kernel
of the linearized Ricci operator. -/
theorem deTurckSymbol_apply_apply_eq_isotropic_of_symm (g g' : SmoothRiemannianMetric I M)
    (x : M) (ξ : E) (t : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ)
    (ht : ∀ v w, t v w = t w v) (i k : Fin (Module.finrank ℝ E)) :
    (deTurckSymbol (I := I) g g' x ξ t)
        ((chartModelBasis E) i) ((chartModelBasis E) k) =
      metricCovectorNormSq (I := I) g x ξ * formComp (I := I) x t i k := by
  -- Expand `deTurckSymbol` into the `−2 • σ_Rc + σ_DT` combination of the two outputs.
  rw [deTurckSymbol_apply_apply]
  -- Substitute the two classical closed forms for the summand components.
  rw [ricciSymbol_apply_eq_closedForm (I := I) g x ξ t i k,
    deTurckCorrectionSymbol_apply_eq_closedForm (I := I) g g' x ξ t i k]
  -- On a symmetric input the first-slot raised contraction equals the second-slot one,
  -- which is what makes the residual gauge term `ξ_i ((ξt)_k − (tξ)_k)` vanish.
  rw [raisedFormContraction_eq_snd_of_symm (I := I) g x ξ t ht k]
  -- The remaining identity is pure real algebra: the gauge terms cancel.
  ring

/-! ## The isotropy theorem

The component identity `deTurckSymbol_apply_apply_eq_isotropic_of_symm` is upgraded to the
full bilinear-form identity.  Both `deTurckSymbol g g' x ξ t` and `|ξ|²_g • t` are fibre
bilinear forms `TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ`; a bilinear map is
determined by its values on basis pairs (`LinearMap.ext_basis`), and on the model-basis
pair `(e_i, e_k)` the component theorem gives `|ξ|²_g · t_{ik}`, which is exactly the
`(e_i, e_k)`-component of `|ξ|²_g • t`. -/

/-- **The isotropy theorem.**

On a **symmetric** input bilinear form `t`, the Ricci–DeTurck symbol acts as a pure
scalar: the output bilinear form is `|ξ|²_g` times the input,
$$\sigma(\mathcal D)(x, \xi)(t) \;=\; |\xi|^2_g \cdot t.$$

This upgrades the component-level gauge cancellation
`deTurckSymbol_apply_apply_eq_isotropic_of_symm` to the full `(0,2)`-tensor identity:
two bilinear forms agreeing on every model-basis pair are equal (`LinearMap.ext_basis`),
and on the pair `(e_i, e_k)` both sides equal `|ξ|²_g · t_{ik}`. -/
theorem deTurckSymbol_apply_eq_smul_of_symm (g g' : SmoothRiemannianMetric I M)
    (x : M) (ξ : E) (t : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ)
    (ht : ∀ v w, t v w = t w v) :
    deTurckSymbol (I := I) g g' x ξ t =
      metricCovectorNormSq (I := I) g x ξ • t := by
  -- A bilinear form is determined by its values on basis pairs.
  refine LinearMap.ext_basis (chartModelBasis E) (chartModelBasis E) (fun i k => ?_)
  -- Left component: the isotropic gauge-cancellation value `|ξ|²_g · t_{ik}`.
  -- Right component: `(|ξ|²_g • t)(e_i, e_k) = |ξ|²_g · t(e_i, e_k) = |ξ|²_g · t_{ik}`.
  calc (deTurckSymbol (I := I) g g' x ξ t)
          ((chartModelBasis E) i) ((chartModelBasis E) k)
      = metricCovectorNormSq (I := I) g x ξ * formComp (I := I) x t i k :=
        deTurckSymbol_apply_apply_eq_isotropic_of_symm (I := I) g g' x ξ t ht i k
    _ = (metricCovectorNormSq (I := I) g x ξ • t)
          ((chartModelBasis E) i) ((chartModelBasis E) k) := by
        rw [LinearMap.smul_apply, LinearMap.smul_apply, smul_eq_mul, formComp_def]

/-! ## Strict parabolicity — the capstone

We can now state the headline theorem.  On the symmetric `(0,2)`-tensors — the space the
metric perturbation lives in — the principal symbol of the Ricci–DeTurck operator is the
isotropic symbol `|ξ|²_g · id`, and `|ξ|²_g > 0` for every nonzero covector
(`metricCovectorNormSq_pos`).  A principal symbol that is a strictly positive scalar
multiple of the identity is the defining property of a strictly (uniformly) parabolic
operator; the Ricci–DeTurck flow is therefore strictly parabolic.

The bare Ricci-flow operator `−2 Rc(g)` fails this — its symbol `−2 σ_Rc` keeps the gauge
terms `ξ_i(tξ)_k`, `ξ_k(ξt)_i`, so it is only *weakly* parabolic.  The DeTurck term
`𝓛_W g` contributes exactly the gauge symbol `σ_DT` that cancels those terms.  This is the
whole purpose of the DeTurck trick. -/

/-- For every base point `x`, every **nonzero** covector `ξ`, and every **symmetric** input
tensor `t` (`t v w = t w v`), the Ricci–DeTurck symbol acts as `|ξ|²_g • t` and the
coefficient `|ξ|²_g` is strictly positive — the strict parabolicity of the Ricci–DeTurck
operator on symmetric tensors.

The conclusion is the conjunction `deTurckSymbol g g' x ξ t = |ξ|²_g • t ∧ 0 < |ξ|²_g`.
In symbol notation, the principal symbol acts as the isotropic, *positive-definite* symbol
$$\sigma(\mathcal D)(x, \xi)(t) \;=\; |\xi|^2_g \cdot t, \qquad |\xi|^2_g > 0.$$
The symmetric-input hypothesis is essential: it is exactly what makes the off-diagonal
gauge terms cancel (see below), so the statement holds only on symmetric tensors — which
is precisely the space a metric perturbation lives in.

This is the precise statement that the Ricci–DeTurck flow `∂_t g = −2 Rc(g) + 𝓛_W g` is
**strictly (uniformly) parabolic**: on the symmetric tensors its linearization has
principal symbol a strictly positive multiple of the identity.  Bare Ricci flow is only
*weakly* parabolic — the linearized Ricci symbol carries the diffeomorphism (gauge) kernel
— and the DeTurck term `𝓛_W g` contributes exactly the gauge symbol that cancels that
kernel (`deTurckSymbol_apply_apply_eq_isotropic_of_symm`).  Positivity of the coefficient
is `metricCovectorNormSq_pos`.

The result is delivered as the conjunction of the isotropy identity
`deTurckSymbol g g' x ξ t = |ξ|²_g • t` (`deTurckSymbol_apply_eq_smul_of_symm`) and the
strict positivity `0 < |ξ|²_g` (`metricCovectorNormSq_pos`). -/
theorem deTurckSymbol_isStrictlyParabolic_of_symm (g g' : SmoothRiemannianMetric I M) (x : M)
    {ξ : E} (hξ : ξ ≠ 0) (t : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ)
    (ht : ∀ v w, t v w = t w v) :
    deTurckSymbol (I := I) g g' x ξ t =
        metricCovectorNormSq (I := I) g x ξ • t ∧
      0 < metricCovectorNormSq (I := I) g x ξ :=
  ⟨deTurckSymbol_apply_eq_smul_of_symm (I := I) g g' x ξ t ht,
    metricCovectorNormSq_pos (I := I) g x hξ⟩

/-- **The Ricci–DeTurck symbol agrees with the scalar-Laplacian symbol on symmetric
tensors, up to sign.**

The scalar Laplace–Beltrami symbol `laplacianSymbol g`, in the `∂_a∂_b ↦ −ξ_aξ_b`
convention of `Symbol.lean`, scales by `−|ξ|²_g` (`laplacianSymbol_apply_apply`).  The
Ricci–DeTurck symbol, in the `∂_a∂_b ↦ +ξ_aξ_b` convention of the linearized closed
forms, scales — on a symmetric input — by `+|ξ|²_g`.  Hence on symmetric tensors the
Ricci–DeTurck symbol is the negative of the (constant-fibre) scalar-Laplacian
coefficient: the Ricci–DeTurck operator has, term for term, the parabolic symbol of the
heat operator, with the sign reflecting only the chosen `∂↦±ξ` reading.

This makes the parabolic comparison explicit: `deTurckSymbol g g'` on symmetric tensors
is `|ξ|²_g · id`, the positive isotropic symbol, the symbol of `∂_t u = Δ u` read with
`∂_a∂_b ↦ +ξ_aξ_b`. -/
theorem deTurckSymbol_eq_neg_laplacianSymbolCoeff_smul_of_symm
    (g g' : SmoothRiemannianMetric I M) (x : M) (ξ : E)
    (t : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ)
    (ht : ∀ v w, t v w = t w v) :
    deTurckSymbol (I := I) g g' x ξ t =
      (-(deTurckSymbolCoeff (I := I) g x ξ)) • t := by
  rw [deTurckSymbol_apply_eq_smul_of_symm (I := I) g g' x ξ t ht, deTurckSymbolCoeff_apply,
    neg_neg]

end DeTurck
end PDE
end DifferentialGeometry
