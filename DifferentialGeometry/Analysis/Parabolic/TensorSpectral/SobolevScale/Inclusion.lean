import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.SobolevScale.Defs

/-!
# Continuous inclusions of the spectral `Hˢ` Sobolev scale

For a closed Riemannian manifold `(M, g)` and ranks `(r, s)`, the
spectral Sobolev spaces `tensorHs g r s h_atlas σ` form a decreasing
scale: a larger exponent `σ` imposes faster decay of the eigenbasis
coordinates, so `Hˢ ⊆ Hᵗ` whenever `τ ≤ σ`. Concretely, since the
weight `(1 + λᵢ)^σ` is monotone in the exponent (the base is `≥ 1`),
weighted square-summability at `σ` implies it at any `τ ≤ σ`, and the
`Hᵗ` norm of a vector is bounded by its `Hˢ` norm.

This file constructs the continuous linear inclusion
`tensorHsInclusion`, proves it is a coordinate-preserving contraction
(operator norm `≤ 1`) and injective, establishes its functoriality
(identity at `τ = σ`, composition for `ρ ≤ τ ≤ σ`), and shows it is
compatible with the `L²` inclusion `tensorHsToL2`.

Finally, it proves that the finitely-supported coordinate families —
equivalently, finite linear combinations of the spectral basis vectors
`tensorHsBasisVec` — are **dense** in every `Hˢ`. The proof transports
the canonical finitely-supported `ℓ²` approximations along the
diagonal rescaling isometry `rescaleEquivL2`.

## Main definitions

* `tensorHsInclusion h_atlas hτσ` — the continuous linear inclusion
  `Hˢ →L[ℝ] Hᵗ` for `τ ≤ σ`.
* `tensorHsFiniteSupportSubmodule h_atlas σ` — the submodule of `Hˢ`
  of elements with finitely-supported coordinate family.

## Main results

* `tensorHsInclusion_coeff` — the inclusion preserves coordinates.
* `tensorHsInclusion_opNorm_le_one`, `tensorHsInclusion_norm_le` — it is
  a norm-non-increasing contraction.
* `tensorHsInclusion_injective` — it is injective.
* `tensorHsInclusion_refl`, `tensorHsInclusion_trans` — functoriality.
* `tensorHsToL2_comp_tensorHsInclusion` — the `L²` inclusion factors
  through any intermediate `Hᵗ`.
* `tensorHs_hasSum_smul_basisVec` — every `T ∈ Hˢ` is the unconditional
  sum `∑ᵢ (coeff i T) • bᵢ` of its spectral basis components.
* `tensorHsFiniteSupportSubmodule_dense` — the finitely-supported
  elements are dense in `Hˢ`.
-/

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorHeatEquation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

/-! ## File-local Borel-space instances on `E` and `M` -/

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

/-! ## Monotonicity of the Sobolev weight in the exponent -/

/-- The Sobolev weight `(1 + λᵢ)^σ` is monotone in the exponent: for
`τ ≤ σ` the base `1 + λᵢ ≥ 1` gives `(1 + λᵢ)^τ ≤ (1 + λᵢ)^σ`. -/
lemma tensorSobolevWeight_mono {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (i : TensorEigenIdx (I := I) (M := M) g r s) {τ σ : ℝ} (hτσ : τ ≤ σ) :
    tensorSobolevWeight (I := I) (M := M) i τ ≤
      tensorSobolevWeight (I := I) (M := M) i σ := by
  unfold tensorSobolevWeight
  exact Real.rpow_le_rpow_of_exponent_le
    (one_le_one_add_lambda (I := I) (M := M) i) hτσ

/-! ## The continuous inclusion `Hˢ → Hᵗ` for `τ ≤ σ`

The inclusion is the identity on coordinate families. Well-definedness
is exactly weight monotonicity: if `∑ᵢ (1+λᵢ)^σ cᵢ² < ∞` and `τ ≤ σ`,
then `(1+λᵢ)^τ ≤ (1+λᵢ)^σ` gives `∑ᵢ (1+λᵢ)^τ cᵢ² < ∞`. -/

namespace tensorHs

variable {g : SmoothRiemannianMetric I M} {r s : ℕ}
  {h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M}

/-- For `τ ≤ σ`, the coordinate family of an `Hˢ` element is
weighted-square-summable at the smaller exponent `τ`. -/
lemma weighted_summable_of_le {τ σ : ℝ} (hτσ : τ ≤ σ)
    (T : tensorHs (I := I) (M := M) g r s h_atlas σ) :
    Summable (fun i : TensorEigenIdx (I := I) (M := M) g r s =>
      tensorSobolevWeight (I := I) (M := M) i τ * (T.coeff i) ^ 2) := by
  refine Summable.of_nonneg_of_le ?_ ?_ T.weighted_summable
  · intro i
    have hw : 0 ≤ tensorSobolevWeight (I := I) (M := M) i τ :=
      tensorSobolevWeight_nonneg (I := I) (M := M) i τ
    positivity
  · intro i
    have hmono : tensorSobolevWeight (I := I) (M := M) i τ ≤
        tensorSobolevWeight (I := I) (M := M) i σ :=
      tensorSobolevWeight_mono (I := I) (M := M) i hτσ
    exact mul_le_mul_of_nonneg_right hmono (sq_nonneg _)

/-- The underlying function of the inclusion `Hˢ → Hᵗ` (`τ ≤ σ`): an
`Hˢ` element is sent to the `Hᵗ` element with the *same* coordinate
family. -/
def inclusionFun {τ σ : ℝ} (hτσ : τ ≤ σ)
    (T : tensorHs (I := I) (M := M) g r s h_atlas σ) :
    tensorHs (I := I) (M := M) g r s h_atlas τ where
  coeff := T.coeff
  weighted_summable := weighted_summable_of_le (I := I) (M := M) hτσ T

@[simp] lemma inclusionFun_coeff {τ σ : ℝ} (hτσ : τ ≤ σ)
    (T : tensorHs (I := I) (M := M) g r s h_atlas σ) :
    (inclusionFun (I := I) (M := M) hτσ T).coeff = T.coeff := rfl

/-- `inclusionFun` is additive. -/
lemma inclusionFun_add {τ σ : ℝ} (hτσ : τ ≤ σ)
    (S T : tensorHs (I := I) (M := M) g r s h_atlas σ) :
    inclusionFun (I := I) (M := M) hτσ (S + T) =
      inclusionFun (I := I) (M := M) hτσ S +
        inclusionFun (I := I) (M := M) hτσ T := by
  ext i
  simp only [inclusionFun_coeff, add_coeff]

/-- `inclusionFun` is `ℝ`-homogeneous. -/
lemma inclusionFun_smul {τ σ : ℝ} (hτσ : τ ≤ σ) (c : ℝ)
    (T : tensorHs (I := I) (M := M) g r s h_atlas σ) :
    inclusionFun (I := I) (M := M) hτσ (c • T) =
      c • inclusionFun (I := I) (M := M) hτσ T := by
  ext i
  simp only [inclusionFun_coeff, smul_coeff]

/-- For `τ ≤ σ`, the `Hᵗ` norm of `inclusionFun T` is bounded by the
`Hˢ` norm of `T`: the inclusion is norm-non-increasing. -/
lemma norm_inclusionFun_le {τ σ : ℝ} (hτσ : τ ≤ σ)
    (T : tensorHs (I := I) (M := M) g r s h_atlas σ) :
    ‖inclusionFun (I := I) (M := M) hτσ T‖ ≤ ‖T‖ := by
  -- Compare squared norms `∑ wᵗ cᵢ² ≤ ∑ wˢ cᵢ²` by weight monotonicity.
  have h_t_sq : ‖inclusionFun (I := I) (M := M) hτσ T‖ ^ 2 =
      ∑' i, tensorSobolevWeight (I := I) (M := M) i τ * (T.coeff i) ^ 2 := by
    have h := norm_sq_eq_tsum (I := I) (M := M)
      (inclusionFun (I := I) (M := M) hτσ T)
    rwa [inclusionFun_coeff] at h
  have h_s_sq : ‖T‖ ^ 2 =
      ∑' i, tensorSobolevWeight (I := I) (M := M) i σ * (T.coeff i) ^ 2 :=
    norm_sq_eq_tsum (I := I) (M := M) T
  have h_le_terms : ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
      tensorSobolevWeight (I := I) (M := M) i τ * (T.coeff i) ^ 2 ≤
        tensorSobolevWeight (I := I) (M := M) i σ * (T.coeff i) ^ 2 := by
    intro i
    exact mul_le_mul_of_nonneg_right
      (tensorSobolevWeight_mono (I := I) (M := M) i hτσ) (sq_nonneg _)
  have h_tsum_le :
      ∑' i, tensorSobolevWeight (I := I) (M := M) i τ * (T.coeff i) ^ 2 ≤
        ∑' i, tensorSobolevWeight (I := I) (M := M) i σ *
          (T.coeff i) ^ 2 :=
    Summable.tsum_le_tsum h_le_terms
      (weighted_summable_of_le (I := I) (M := M) hτσ T) T.weighted_summable
  have h_sq_le : ‖inclusionFun (I := I) (M := M) hτσ T‖ ^ 2 ≤ ‖T‖ ^ 2 := by
    rw [h_t_sq, h_s_sq]; exact h_tsum_le
  have h1 : 0 ≤ ‖inclusionFun (I := I) (M := M) hτσ T‖ := norm_nonneg _
  have h2 : 0 ≤ ‖T‖ := norm_nonneg T
  nlinarith [h_sq_le, h1, h2]

end tensorHs

/-- For `τ ≤ σ`, the continuous linear inclusion of the spectral
Sobolev space `Hˢ` into the larger space `Hᵗ`. It is the identity on
coordinate families, has operator norm at most `1` (the weight is
monotone in the exponent, making the inclusion a contraction), and is
injective. See `tensorHsInclusion_coeff`. -/
def tensorHsInclusion {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M) {τ σ : ℝ}
    (hτσ : τ ≤ σ) :
    tensorHs (I := I) (M := M) g r s h_atlas σ →L[ℝ]
      tensorHs (I := I) (M := M) g r s h_atlas τ :=
  LinearMap.mkContinuous
    { toFun := tensorHs.inclusionFun (I := I) (M := M) hτσ
      map_add' := tensorHs.inclusionFun_add (I := I) (M := M) hτσ
      map_smul' := fun c T =>
        tensorHs.inclusionFun_smul (I := I) (M := M) hτσ c T }
    1
    (fun T => by
      change ‖tensorHs.inclusionFun (I := I) (M := M) hτσ T‖ ≤ 1 * ‖T‖
      rw [one_mul]
      exact tensorHs.norm_inclusionFun_le (I := I) (M := M) hτσ T)

/-- `tensorHsInclusion` applied to `T` is the underlying
`inclusionFun T`. -/
@[simp] lemma tensorHsInclusion_apply {g : SmoothRiemannianMetric I M}
    {r s : ℕ} {h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M}
    {τ σ : ℝ} (hτσ : τ ≤ σ)
    (T : tensorHs (I := I) (M := M) g r s h_atlas σ) :
    tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s) h_atlas hτσ T =
      tensorHs.inclusionFun (I := I) (M := M) hτσ T := rfl

/-- The inclusion `Hˢ → Hᵗ` preserves the eigenbasis coordinate
family. -/
@[simp] theorem tensorHsInclusion_coeff {g : SmoothRiemannianMetric I M}
    {r s : ℕ} {h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M}
    {τ σ : ℝ} (hτσ : τ ≤ σ)
    (T : tensorHs (I := I) (M := M) g r s h_atlas σ) :
    (tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s) h_atlas hτσ T).coeff =
      T.coeff := rfl

/-- The eigenbasis coordinate of `tensorHsInclusion … T` at `i`. -/
@[simp] theorem tensorHsInclusion_coeff_apply
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    {h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M} {τ σ : ℝ}
    (hτσ : τ ≤ σ) (T : tensorHs (I := I) (M := M) g r s h_atlas σ)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    (tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s) h_atlas hτσ T).coeff i =
      T.coeff i := rfl

/-- The operator norm of the inclusion `Hˢ → Hᵗ` is at most `1` for
`τ ≤ σ`. -/
theorem tensorHsInclusion_opNorm_le_one {g : SmoothRiemannianMetric I M}
    {r s : ℕ} {h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M}
    {τ σ : ℝ} (hτσ : τ ≤ σ) :
    ‖tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s) h_atlas hτσ‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

/-- For `τ ≤ σ`, the inclusion is norm-non-increasing:
`‖incl T‖_{Hᵗ} ≤ ‖T‖_{Hˢ}`. -/
theorem tensorHsInclusion_norm_le {g : SmoothRiemannianMetric I M}
    {r s : ℕ} {h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M}
    {τ σ : ℝ} (hτσ : τ ≤ σ)
    (T : tensorHs (I := I) (M := M) g r s h_atlas σ) :
    ‖tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s) h_atlas hτσ T‖ ≤ ‖T‖ :=
  tensorHs.norm_inclusionFun_le (I := I) (M := M) hτσ T

/-- The inclusion `Hˢ → Hᵗ` is injective for `τ ≤ σ`. -/
theorem tensorHsInclusion_injective {g : SmoothRiemannianMetric I M}
    {r s : ℕ} {h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M}
    {τ σ : ℝ} (hτσ : τ ≤ σ) :
    Function.Injective
      (tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s) h_atlas hτσ) := by
  intro S T hST
  ext i
  have h := congrArg (fun U => tensorHs.coeff U i) hST
  simpa only [tensorHsInclusion_coeff] using h

/-! ## Functoriality of the inclusion -/

/-- The inclusion at the reflexive exponent `σ ≤ σ` is the identity
continuous linear map. -/
@[simp] theorem tensorHsInclusion_refl {g : SmoothRiemannianMetric I M}
    {r s : ℕ} {h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M}
    {σ : ℝ} :
    tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s) h_atlas (le_refl σ) =
      ContinuousLinearMap.id ℝ
        (tensorHs (I := I) (M := M) g r s h_atlas σ) := by
  refine ContinuousLinearMap.ext (fun T => ?_)
  refine tensorHs.ext ?_
  funext i
  rw [tensorHsInclusion_coeff_apply, ContinuousLinearMap.id_apply]

/-- Reflexive inclusion, applied form: `tensorHsInclusion … (le_refl σ)`
fixes every vector. -/
@[simp] theorem tensorHsInclusion_refl_apply
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    {h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M} {σ : ℝ}
    (T : tensorHs (I := I) (M := M) g r s h_atlas σ) :
    tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s) h_atlas (le_refl σ) T = T := by
  ext i
  simp only [tensorHsInclusion_coeff_apply]

/-- The inclusions compose: for `ρ ≤ τ ≤ σ`, the inclusion `Hˢ → Hᵖ` is
the composite `Hˢ → Hᵗ → Hᵖ`. -/
theorem tensorHsInclusion_trans {g : SmoothRiemannianMetric I M}
    {r s : ℕ} {h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M}
    {ρ τ σ : ℝ} (hρτ : ρ ≤ τ) (hτσ : τ ≤ σ) :
    tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s) h_atlas (hρτ.trans hτσ) =
      (tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s) h_atlas hρτ).comp
        (tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s) h_atlas hτσ) := by
  ext T i
  simp only [tensorHsInclusion_coeff_apply, ContinuousLinearMap.coe_comp',
    Function.comp_apply]

/-- The inclusions compose, applied form: for `ρ ≤ τ ≤ σ`, including
`Hˢ → Hᵖ` directly agrees with going through `Hᵗ`. -/
theorem tensorHsInclusion_trans_apply {g : SmoothRiemannianMetric I M}
    {r s : ℕ} {h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M}
    {ρ τ σ : ℝ} (hρτ : ρ ≤ τ) (hτσ : τ ≤ σ)
    (T : tensorHs (I := I) (M := M) g r s h_atlas σ) :
    tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s) h_atlas (hρτ.trans hτσ) T =
      tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s) h_atlas hρτ
        (tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s) h_atlas hτσ T) := by
  ext i
  simp only [tensorHsInclusion_coeff_apply]

/-! ## Compatibility with the `L²` inclusion `tensorHsToL2`

For `0 ≤ τ ≤ σ`, the inclusion `Hˢ → TensorL2` factors through any
intermediate `Hᵗ`: `tensorHsToL2 hτ ∘ tensorHsInclusion hτσ`
agrees with `tensorHsToL2 hσ`. Both sides are coordinate-preserving, so
they agree once the `L²` eigenbasis coordinates match. -/

/-- For `0 ≤ τ ≤ σ`, the `L²` inclusion of `Hˢ` factors through `Hᵗ`:
`tensorHsToL2 hτ ∘ tensorHsInclusion hτσ = tensorHsToL2 hσ`. -/
theorem tensorHsToL2_comp_tensorHsInclusion
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    {h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M} {τ σ : ℝ}
    (hτ : 0 ≤ τ) (hτσ : τ ≤ σ) :
    (tensorHsToL2 (I := I) (M := M) (g := g) (r := r) (s := s) h_atlas hτ).comp
        (tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s) h_atlas hτσ) =
      tensorHsToL2 (I := I) (M := M) (g := g) (r := r) (s := s) h_atlas (hτ.trans hτσ) := by
  -- Both `L²` images have the same eigenbasis coordinates; the
  -- eigenbasis representation is injective.
  ext T
  refine (tensorResolventHilbertEigenbasisSigma
    (I := I) (M := M) h_atlas).repr.injective ?_
  ext i
  have hlhs : ((tensorResolventHilbertEigenbasisSigma
        (I := I) (M := M) h_atlas).repr
      ((tensorHsToL2 (I := I) (M := M) (g := g) (r := r) (s := s) h_atlas hτ).comp
        (tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s) h_atlas hτσ) T)) i =
      T.coeff i := by
    have h := tensorHsToL2_tensorL2Coeff (I := I) (M := M) hτ
      (tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s) h_atlas hτσ T) i
    rw [tensorHsInclusion_coeff_apply] at h
    simpa only [ContinuousLinearMap.coe_comp', Function.comp_apply,
      tensorL2Coeff] using h
  have hrhs : ((tensorResolventHilbertEigenbasisSigma
        (I := I) (M := M) h_atlas).repr
      (tensorHsToL2 (I := I) (M := M) (g := g) (r := r) (s := s) h_atlas (hτ.trans hτσ) T)) i =
      T.coeff i := by
    have h := tensorHsToL2_tensorL2Coeff (I := I) (M := M)
      (hτ.trans hτσ) T i
    simpa only [tensorL2Coeff] using h
  rw [hlhs, hrhs]

/-- For `0 ≤ τ ≤ σ`, the `L²` inclusion of `Hˢ` factors through `Hᵗ`,
applied form. -/
theorem tensorHsToL2_tensorHsInclusion {g : SmoothRiemannianMetric I M}
    {r s : ℕ} {h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M}
    {τ σ : ℝ} (hτ : 0 ≤ τ) (hτσ : τ ≤ σ)
    (T : tensorHs (I := I) (M := M) g r s h_atlas σ) :
    tensorHsToL2 (I := I) (M := M) (g := g) (r := r) (s := s) h_atlas hτ
        (tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s) h_atlas hτσ T) =
      tensorHsToL2 (I := I) (M := M) (g := g) (r := r) (s := s) h_atlas (hτ.trans hτσ) T := by
  have h := tensorHsToL2_comp_tensorHsInclusion (I := I) (M := M)
    (g := g) (r := r) (s := s) (h_atlas := h_atlas) hτ hτσ
  exact congrArg (fun L => L T) h

/-- For `0 ≤ σ`, the `L²` inclusion `tensorHsToL2` factors as the
inclusion `Hˢ → H⁰` followed by the isometric identification
`H⁰ ≃ₗᵢ TensorL2`. -/
theorem tensorHsZeroEquivL2_comp_tensorHsInclusion_zero
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    {h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M} {σ : ℝ}
    (hσ : 0 ≤ σ) (T : tensorHs (I := I) (M := M) g r s h_atlas σ) :
    tensorHsZeroEquivL2 (I := I) (M := M) h_atlas
        (tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s) h_atlas hσ T) =
      tensorHsToL2 (I := I) (M := M) (g := g) (r := r) (s := s) h_atlas hσ T := by
  -- Compare `L²` eigenbasis coordinates: both equal `T.coeff`.
  refine (tensorResolventHilbertEigenbasisSigma
    (I := I) (M := M) h_atlas).repr.injective ?_
  ext i
  have hlhs : ((tensorResolventHilbertEigenbasisSigma
        (I := I) (M := M) h_atlas).repr
      (tensorHsZeroEquivL2 (I := I) (M := M) h_atlas
        (tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s) h_atlas hσ T))) i =
      T.coeff i := by
    have h := tensorHsZeroEquivL2_tensorL2Coeff (I := I) (M := M)
      h_atlas (tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s) h_atlas hσ T) i
    rw [tensorHsInclusion_coeff_apply] at h
    simpa only [tensorL2Coeff] using h
  have hrhs : ((tensorResolventHilbertEigenbasisSigma
        (I := I) (M := M) h_atlas).repr
      (tensorHsToL2 (I := I) (M := M) (g := g) (r := r) (s := s) h_atlas hσ T)) i = T.coeff i := by
    have h := tensorHsToL2_tensorL2Coeff (I := I) (M := M) hσ T i
    simpa only [tensorL2Coeff] using h
  rw [hlhs, hrhs]

/-! ## The submodule of finitely-supported elements

A coordinate family with finite support is weighted-square-summable for
every exponent (see `tensorHsOfFiniteSupport`). The set of such
elements is a linear subspace of `Hˢ`, and below it is shown dense. -/

namespace tensorHs

variable {g : SmoothRiemannianMetric I M} {r s : ℕ}
  {h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M} {σ : ℝ}

/-- The submodule of `Hˢ` consisting of elements whose eigenbasis
coordinate family has finite support. Equivalently, the span of the
spectral basis vectors `tensorHsBasisVec`; see
`tensorHsFiniteSupportSubmodule_eq_span`. -/
def finiteSupportSubmodule (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (σ : ℝ) :
    Submodule ℝ (tensorHs (I := I) (M := M) g r s h_atlas σ) where
  carrier := {T | (Function.support T.coeff).Finite}
  add_mem' := by
    intro S T hS hT
    refine Set.Finite.subset (hS.union hT) ?_
    intro i hi
    simp only [Function.mem_support, add_coeff, ne_eq] at hi
    by_contra hcon
    simp only [Set.mem_union, Function.mem_support, ne_eq, not_or,
      not_not] at hcon
    exact hi (by rw [hcon.1, hcon.2, add_zero])
  zero_mem' := by
    simp only [Set.mem_setOf_eq, zero_coeff]
    refine Set.finite_empty.subset ?_
    intro i hi
    simp only [Function.mem_support, ne_eq, not_true_eq_false] at hi
  smul_mem' := by
    intro c T hT
    refine Set.Finite.subset hT ?_
    intro i hi
    simp only [Function.mem_support, smul_coeff, ne_eq] at hi
    simp only [Function.mem_support, ne_eq]
    intro hcon
    exact hi (by rw [hcon, mul_zero])

@[simp] lemma mem_finiteSupportSubmodule
    {h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M} {σ : ℝ}
    (T : tensorHs (I := I) (M := M) g r s h_atlas σ) :
    T ∈ finiteSupportSubmodule (I := I) (M := M) (g := g) (r := r) (s := s) h_atlas σ ↔
      (Function.support T.coeff).Finite := Iff.rfl

end tensorHs

/-! ## Density of finitely-supported eigenvectors in `Hˢ`

Every `T ∈ Hˢ` is the unconditional sum of its spectral basis
components `(coeff i T) • bᵢ`. The proof transports the canonical
finitely-supported `ℓ²` approximations (`lp.hasSum_single`) along the
diagonal rescaling isometric equivalence `rescaleEquivL2`. Density of
the finitely-supported submodule is then immediate. -/

namespace tensorHs

variable {g : SmoothRiemannianMetric I M} {r s : ℕ}
  {h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M} {σ : ℝ}

open scoped Classical in
/-- The rescaling isometry carries the spectral basis component
`(coeff i T) • bᵢ` to the canonical `ℓ²` unit family
`lp.single 2 i (√(1+λᵢ)^σ · coeff i T)`. -/
lemma rescaleEquivL2_smul_basisVec
    (T : tensorHs (I := I) (M := M) g r s h_atlas σ)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    rescaleEquivL2 (I := I) (M := M) (h_atlas := h_atlas) (σ := σ)
        (T.coeff i • tensorHsBasisVec (I := I) (M := M) (g := g) (r := r) (s := s) h_atlas σ i) =
      lp.single 2 i
        (Real.sqrt (tensorSobolevWeight (I := I) (M := M) i σ) *
          T.coeff i) := by
  classical
  apply lp.ext
  funext j
  rw [rescaleEquivL2_apply, lp.single_apply]
  simp only [smul_coeff, tensorHsBasisVec_coeff]
  by_cases h : j = i
  · subst h; simp
  · simp [h]

/-- Every `T ∈ Hˢ` is the unconditional sum of its spectral basis
components: `T = ∑ᵢ (coeff i T) • bᵢ`, where `bᵢ = tensorHsBasisVec`.
The proof transports the canonical finitely-supported `ℓ²`
approximation `lp.hasSum_single` of `rescaleEquivL2 T` back along the
diagonal rescaling isometry. -/
theorem hasSum_smul_basisVec
    (T : tensorHs (I := I) (M := M) g r s h_atlas σ) :
    HasSum (fun i : TensorEigenIdx (I := I) (M := M) g r s =>
      T.coeff i • tensorHsBasisVec (I := I) (M := M) (g := g) (r := r) (s := s) h_atlas σ i) T := by
  classical
  -- Transport `HasSum` along the continuous-linear-equiv `rescaleEquivL2`:
  -- it suffices to prove the `HasSum` of the *image* family in `ℓ²`.
  rw [← ContinuousLinearEquiv.hasSum'
    (e := (rescaleEquivL2 (I := I) (M := M)
      (h_atlas := h_atlas) (σ := σ)).toContinuousLinearEquiv)]
  -- The image of `(coeff i T) • bᵢ` is the canonical `ℓ²` unit family,
  -- whose sum is `rescaleEquivL2 T` by `lp.hasSum_single`.
  have h_l2 : HasSum
      (fun i : TensorEigenIdx (I := I) (M := M) g r s =>
        lp.single 2 i
          (Real.sqrt (tensorSobolevWeight (I := I) (M := M) i σ) *
            T.coeff i))
      (rescaleEquivL2 (I := I) (M := M)
        (h_atlas := h_atlas) (σ := σ) T) := by
    have h := lp.hasSum_single (α := TensorEigenIdx (I := I) (M := M) g r s)
      (E := fun _ => ℝ) (p := 2) (by norm_num)
      (rescaleEquivL2 (I := I) (M := M)
        (h_atlas := h_atlas) (σ := σ) T)
    refine h.congr_fun (fun i => ?_)
    rw [rescaleEquivL2_apply]
  refine h_l2.congr_fun (fun i => ?_)
  rw [LinearIsometryEquiv.coe_toContinuousLinearEquiv,
    rescaleEquivL2_smul_basisVec]

/-- Every `T ∈ Hˢ` is the limit of the finite partial sums of its
spectral basis expansion: the finitely-supported elements (the span of
`tensorHsBasisVec`) are dense in `Hˢ`. Stated as `T` lying in the
topological closure of the finitely-supported submodule. -/
theorem mem_closure_finiteSupportSubmodule
    (T : tensorHs (I := I) (M := M) g r s h_atlas σ) :
    T ∈ closure
      (finiteSupportSubmodule (I := I) (M := M) (g := g) (r := r) (s := s) h_atlas σ :
        Set (tensorHs (I := I) (M := M) g r s h_atlas σ)) := by
  classical
  -- `T` is the limit of finite partial sums of `T.coeff i • bᵢ`, each
  -- of which has finite support, hence lies in the submodule.
  refine mem_closure_of_tendsto
    (hasSum_smul_basisVec (I := I) (M := M) T) ?_
  refine Filter.Eventually.of_forall (fun u => ?_)
  refine Submodule.sum_mem _ (fun i _ => ?_)
  -- `T.coeff i • bᵢ` has support contained in `{i}`.
  refine Submodule.smul_mem _ _ ?_
  rw [mem_finiteSupportSubmodule]
  refine Set.Finite.subset (Set.finite_singleton i) ?_
  intro j hj
  simp only [Function.mem_support, tensorHsBasisVec_coeff, ne_eq,
    ite_eq_right_iff, one_ne_zero, imp_false, not_not] at hj
  simpa using hj

end tensorHs

/-- The finitely-supported elements form a dense submodule of `Hˢ`:
their topological closure is the whole space. Equivalently, the span of
the spectral basis vectors `tensorHsBasisVec` is dense — this is what
lets bounded operators be extended from finite linear combinations of
eigenvectors to all of `Hˢ`. -/
theorem tensorHsFiniteSupportSubmodule_topologicalClosure
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    {h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M} {σ : ℝ} :
    (tensorHs.finiteSupportSubmodule (I := I) (M := M) (g := g) (r := r) (s := s)
        h_atlas σ).topologicalClosure = ⊤ := by
  rw [eq_top_iff]
  intro T _
  rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe]
  exact tensorHs.mem_closure_finiteSupportSubmodule (I := I) (M := M) T

/-- The set of finitely-supported elements of `Hˢ` is dense. -/
theorem tensorHsFiniteSupportSubmodule_dense
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    {h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M} {σ : ℝ} :
    Dense (tensorHs.finiteSupportSubmodule (I := I) (M := M) (g := g) (r := r) (s := s)
      h_atlas σ :
      Set (tensorHs (I := I) (M := M) g r s h_atlas σ)) := by
  rw [Submodule.dense_iff_topologicalClosure_eq_top]
  exact tensorHsFiniteSupportSubmodule_topologicalClosure
    (I := I) (M := M) (g := g) (r := r) (s := s)

/-- The set of elements of `Hˢ` with finitely-supported coordinate
family is dense, stated directly on the predicate. -/
theorem tensorHs_dense_finiteSupport {g : SmoothRiemannianMetric I M}
    {r s : ℕ} {h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M}
    {σ : ℝ} :
    Dense {T : tensorHs (I := I) (M := M) g r s h_atlas σ |
      (Function.support T.coeff).Finite} :=
  tensorHsFiniteSupportSubmodule_dense (I := I) (M := M) (g := g) (r := r) (s := s)

/-- The span of the spectral basis vectors `tensorHsBasisVec` is dense
in `Hˢ`: every `Hˢ` element is approximated in `Hˢ`-norm by finite
linear combinations of eigenvectors. -/
theorem tensorHsBasisVec_span_dense {g : SmoothRiemannianMetric I M}
    {r s : ℕ} {h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M}
    {σ : ℝ} :
    Dense (Submodule.span ℝ
      (Set.range (tensorHsBasisVec (I := I) (M := M) (g := g) (r := r) (s := s) h_atlas σ)) :
      Set (tensorHs (I := I) (M := M) g r s h_atlas σ)) := by
  classical
  -- The span of the basis vectors equals the finitely-supported
  -- submodule, which is dense.
  refine tensorHsFiniteSupportSubmodule_dense (I := I) (M := M) (g := g) (r := r) (s := s)
    |>.mono ?_
  intro T hT
  -- `T` finitely supported ⇒ `T = ∑_{i ∈ s} (coeff i) • bᵢ` over its
  -- (finite) support `s`, hence in the span.
  rw [SetLike.mem_coe, tensorHs.mem_finiteSupportSubmodule] at hT
  classical
  have h_eq : T = ∑ i ∈ hT.toFinset,
      T.coeff i • tensorHsBasisVec (I := I) (M := M) (g := g) (r := r) (s := s) h_atlas σ i := by
    refine tensorHs.ext ?_
    funext j
    -- Read off the `j`-th coordinate of the finite sum.
    have h_sum : (∑ i ∈ hT.toFinset,
          T.coeff i • tensorHsBasisVec (I := I) (M := M)
            h_atlas σ i).coeff j =
        ∑ i ∈ hT.toFinset,
          (if j = i then T.coeff i else 0) := by
      induction hT.toFinset using Finset.induction with
      | empty => simp
      | insert a t ha ih =>
          rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih,
            tensorHs.add_coeff]
          simp only [tensorHs.smul_coeff, tensorHsBasisVec_coeff,
            mul_ite, mul_one, mul_zero]
    rw [h_sum]
    -- The summand vanishes except at `i = j`, where it is `T.coeff j`.
    rw [Finset.sum_eq_single j]
    · simp
    · intro i _ hij
      simp [Ne.symm hij]
    · intro hj
      -- `j ∉ support` forces `T.coeff j = 0`.
      have hzero : T.coeff j = 0 := by
        by_contra hne
        exact hj (hT.mem_toFinset.mpr (Function.mem_support.mpr hne))
      simp [hzero]
  rw [h_eq]
  refine Submodule.sum_mem _ (fun i _ => ?_)
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

/-! ## Sanity tests -/

example {g : SmoothRiemannianMetric I M} {r s : ℕ}
    {h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M} {τ σ : ℝ}
    (hτσ : τ ≤ σ) :
    tensorHs (I := I) (M := M) g r s h_atlas σ →L[ℝ]
      tensorHs (I := I) (M := M) g r s h_atlas τ :=
  tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s) h_atlas hτσ

example {g : SmoothRiemannianMetric I M} {r s : ℕ}
    {h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M} {σ : ℝ} :
    Dense {T : tensorHs (I := I) (M := M) g r s h_atlas σ |
      (Function.support T.coeff).Finite} :=
  tensorHs_dense_finiteSupport (I := I) (M := M)

end TensorHeatEquation
end Parabolic
end Analysis
end DifferentialGeometry

end
