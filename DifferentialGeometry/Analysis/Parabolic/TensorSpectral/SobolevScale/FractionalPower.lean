import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.SobolevScale.Inclusion

/-!
# Fractional powers `(1 − Δ_∇)^θ` on the spectral Sobolev scale

For a closed Riemannian manifold `(M, g)` and ranks `(r, s)`, the
shifted rough Laplacian `1 − Δ_∇` acts diagonally on the eigenbasis
`tensorResolventHilbertEigenbasisSigma`: it multiplies the `i`-th
coordinate by `1 + λᵢ`, where `λᵢ ≥ 0` is the connection-Laplacian
eigenvalue. Its real fractional power `(1 − Δ_∇)^θ` is therefore the
spectral multiplier sending the coordinate family `c` to
`i ↦ (1 + λᵢ)^θ · cᵢ`.

This file builds `(1 − Δ_∇)^θ` as an operator on the spectral `Hˢ`
Sobolev scale and shows it shifts the scale **isometrically**.

## Scale-shift convention

The `Hˢ` norm weights the *squared* coordinate by `(1 + λᵢ)^σ`. With
the coordinate-multiplier convention above, if `T ∈ Hˢ` has coordinates
`cᵢ` then `(1 − Δ_∇)^θ T` has coordinates `(1 + λᵢ)^θ · cᵢ`, and

  `‖(1 − Δ_∇)^θ T‖²_{H^{σ−2θ}}`
    `= ∑ᵢ (1 + λᵢ)^{σ−2θ} · ((1 + λᵢ)^θ cᵢ)²`
    `= ∑ᵢ (1 + λᵢ)^σ · cᵢ²`
    `= ‖T‖²_{Hˢ}`.

Hence `(1 − Δ_∇)^θ` is an **isometric isomorphism `Hˢ ≃ H^{σ−2θ}`**:
the scale drops by exactly `2θ` (not `θ`), because the norm squares the
coordinate. This is the convention used throughout the file:
`tensorFractionalPower θ` lands in `H^{σ − 2*θ}`. The companion
operator that shifts the scale by *exactly* `s` is `tensorLambdaPower s`
(the "`Λˢ`" of the scale), defined as `tensorFractionalPower (s/2)`; see
`tensorLambdaPower_target` for its scale.

## Main definitions

* `tensorFractionalPower h_atlas θ` — the continuous linear operator
  `(1 − Δ_∇)^θ : Hˢ →L[ℝ] H^{σ−2θ}` multiplying coordinate `i` by
  `(1 + λᵢ)^θ`.
* `tensorFractionalPowerEquiv h_atlas θ σ` — the same map packaged as
  a linear isometric equivalence `Hˢ ≃ₗᵢ[ℝ] H^{σ−2θ}`; its inverse is
  `(1 − Δ_∇)^{−θ}`.
* `tensorLambdaPower h_atlas s` — the scale shift by exactly `s`,
  `Λˢ := (1 − Δ_∇)^{s/2} : Hˢ →L[ℝ] H^{σ−s}`.

## Main results

* `tensorFractionalPower_coeff` — the coordinate formula
  `((1−Δ)^θ T).coeff i = (1+λᵢ)^θ · T.coeff i`.
* `tensorFractionalPower_norm` — the isometry
  `‖(1−Δ)^θ T‖_{H^{σ−2θ}} = ‖T‖_{Hˢ}`.
* `tensorFractionalPower_comp`, `tensorFractionalPower_zero` — the group
  law `(1−Δ)^θ ∘ (1−Δ)^φ = (1−Δ)^{θ+φ}` and `(1−Δ)^0 = id`.
* `tensorFractionalPowerEquiv_symm` — the inverse is `(1−Δ)^{−θ}`.
* `tensorHsInclusion_comp_tensorFractionalPower`,
  `tensorFractionalPower_comp_tensorHsInclusion` — interaction with the
  Sobolev-scale inclusion.
* `tensorHsEquivOfFractionalPower` — any two scales `Hˢ`, `Hᵗ` are
  mutually isometrically isomorphic, realised by a fractional power.
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

/-! ## Transporting `Hˢ` elements along an equality of exponents

The carrier `tensorHs g r s h_atlas σ` depends on `σ` only through
the summability witness; the coordinate family `coeff` lives in the
`σ`-independent type `TensorEigenIdx g r s → ℝ`. When two exponents are
propositionally equal, `tensorHs.cast` rebuilds an element with the same
coordinates at the other exponent — used below to make the fractional
powers' target scales line up definitionally. -/

namespace tensorHs

variable {g : SmoothRiemannianMetric I M} {r s : ℕ}
  {h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M}

/-- Transport an `Hˢ` element along an equality `σ = τ` of exponents:
the coordinate family is unchanged, only the index of the Sobolev space
is rewritten. -/
def cast {σ τ : ℝ} (h : σ = τ)
    (T : tensorHs (I := I) (M := M) g r s h_atlas σ) :
    tensorHs (I := I) (M := M) g r s h_atlas τ where
  coeff := T.coeff
  weighted_summable := by
    subst h; exact T.weighted_summable

@[simp] lemma cast_coeff {σ τ : ℝ} (h : σ = τ)
    (T : tensorHs (I := I) (M := M) g r s h_atlas σ)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    (cast (I := I) (M := M) h T).coeff i = T.coeff i := rfl

@[simp] lemma cast_coeff_fun {σ τ : ℝ} (h : σ = τ)
    (T : tensorHs (I := I) (M := M) g r s h_atlas σ) :
    (cast (I := I) (M := M) h T).coeff = T.coeff := rfl

/-- `cast` along the reflexive equality is the identity. -/
@[simp] lemma cast_rfl {σ : ℝ}
    (T : tensorHs (I := I) (M := M) g r s h_atlas σ) :
    cast (I := I) (M := M) (rfl : σ = σ) T = T := rfl

/-- `cast` is additive. -/
lemma cast_add {σ τ : ℝ} (h : σ = τ)
    (S T : tensorHs (I := I) (M := M) g r s h_atlas σ) :
    cast (I := I) (M := M) h (S + T) =
      cast (I := I) (M := M) h S + cast (I := I) (M := M) h T := by
  ext i
  simp only [cast_coeff, add_coeff]

/-- `cast` is `ℝ`-homogeneous. -/
lemma cast_smul {σ τ : ℝ} (h : σ = τ) (c : ℝ)
    (T : tensorHs (I := I) (M := M) g r s h_atlas σ) :
    cast (I := I) (M := M) h (c • T) =
      c • cast (I := I) (M := M) h T := by
  ext i
  simp only [cast_coeff, smul_coeff]

/-- `cast` preserves the norm: the squared norm `∑ (1+λ)^σ cᵢ²` only
depends on the exponent through `σ`, and `σ = τ`. -/
lemma norm_cast {σ τ : ℝ} (h : σ = τ)
    (T : tensorHs (I := I) (M := M) g r s h_atlas σ) :
    ‖cast (I := I) (M := M) h T‖ = ‖T‖ := by
  subst h; rfl

/-- `cast` along an equality `σ = τ` packaged as a linear isometric
equivalence `Hˢ ≃ₗᵢ[ℝ] Hᵗ`. -/
def castEquiv {σ τ : ℝ} (h : σ = τ) :
    tensorHs (I := I) (M := M) g r s h_atlas σ ≃ₗᵢ[ℝ]
      tensorHs (I := I) (M := M) g r s h_atlas τ where
  toFun := cast (I := I) (M := M) h
  invFun := cast (I := I) (M := M) h.symm
  map_add' := cast_add (I := I) (M := M) h
  map_smul' := cast_smul (I := I) (M := M) h
  left_inv T := by ext i; simp only [cast_coeff]
  right_inv T := by ext i; simp only [cast_coeff]
  norm_map' := norm_cast (I := I) (M := M) h

@[simp] lemma castEquiv_coeff {σ τ : ℝ} (h : σ = τ)
    (T : tensorHs (I := I) (M := M) g r s h_atlas σ)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    (castEquiv (I := I) (M := M) h T).coeff i = T.coeff i := rfl

end tensorHs

/-! ## Multiplicativity of the Sobolev weight in the exponent

The weight `(1 + λᵢ)^σ` is an `rpow` with base `1 + λᵢ ≥ 1 > 0`, so it
satisfies the exponent-addition law. These are the only spectral facts
the fractional power needs. -/

namespace tensorHs

variable {g : SmoothRiemannianMetric I M} {r s : ℕ}
  {h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M}

/-- The Sobolev weight is additive in the exponent:
`(1 + λᵢ)^{σ+τ} = (1 + λᵢ)^σ · (1 + λᵢ)^τ`. -/
lemma tensorSobolevWeight_add (i : TensorEigenIdx (I := I) (M := M) g r s)
    (σ τ : ℝ) :
    tensorSobolevWeight (I := I) (M := M) i (σ + τ) =
      tensorSobolevWeight (I := I) (M := M) i σ *
        tensorSobolevWeight (I := I) (M := M) i τ := by
  unfold tensorSobolevWeight
  exact Real.rpow_add
    (lt_of_lt_of_le one_pos (one_le_one_add_lambda (I := I) (M := M) i)) σ τ

/-- The Sobolev weight at a negated exponent is the inverse of the
weight: `(1 + λᵢ)^{-σ} = ((1 + λᵢ)^σ)⁻¹`. -/
lemma tensorSobolevWeight_neg (i : TensorEigenIdx (I := I) (M := M) g r s)
    (σ : ℝ) :
    tensorSobolevWeight (I := I) (M := M) i (-σ) =
      (tensorSobolevWeight (I := I) (M := M) i σ)⁻¹ := by
  unfold tensorSobolevWeight
  exact Real.rpow_neg
    (le_trans zero_le_one (one_le_one_add_lambda (I := I) (M := M) i)) σ

/-- The Sobolev weight at exponent `σ - τ` is `(1+λ)^σ / (1+λ)^τ`. -/
lemma tensorSobolevWeight_sub (i : TensorEigenIdx (I := I) (M := M) g r s)
    (σ τ : ℝ) :
    tensorSobolevWeight (I := I) (M := M) i (σ - τ) =
      tensorSobolevWeight (I := I) (M := M) i σ *
        (tensorSobolevWeight (I := I) (M := M) i τ)⁻¹ := by
  rw [sub_eq_add_neg, tensorSobolevWeight_add (I := I) (M := M),
    tensorSobolevWeight_neg (I := I) (M := M)]

end tensorHs

/-! ## The fractional-power coordinate family

The fractional power multiplies coordinate `i` by `(1 + λᵢ)^θ`. The key
algebraic fact is that this carries the `Hˢ` weighting to the
`H^{σ−2θ}` weighting:

  `(1 + λᵢ)^{σ−2θ} · ((1 + λᵢ)^θ · cᵢ)² = (1 + λᵢ)^σ · cᵢ²`. -/

namespace tensorHs

variable {g : SmoothRiemannianMetric I M} {r s : ℕ}
  {h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M}

/-- The pointwise weight-transfer identity behind the fractional power:
weighting the `θ`-rescaled coordinate at exponent `σ − 2θ` recovers the
original `Hˢ` weighting at exponent `σ`. -/
lemma fractionalPower_weight_term (i : TensorEigenIdx (I := I) (M := M) g r s)
    (θ σ : ℝ) (c : ℝ) :
    tensorSobolevWeight (I := I) (M := M) i (σ - 2 * θ) *
        (tensorSobolevWeight (I := I) (M := M) i θ * c) ^ 2 =
      tensorSobolevWeight (I := I) (M := M) i σ * c ^ 2 := by
  have hw_pos : 0 < tensorSobolevWeight (I := I) (M := M) i θ :=
    tensorSobolevWeight_pos (I := I) (M := M) i θ
  -- `(σ - 2θ) + (θ + θ) = σ`, so the two `θ`-weights and the
  -- `(σ-2θ)`-weight collapse to the `σ`-weight.
  have hsum : (σ - 2 * θ) + (θ + θ) = σ := by ring
  calc
    tensorSobolevWeight (I := I) (M := M) i (σ - 2 * θ) *
          (tensorSobolevWeight (I := I) (M := M) i θ * c) ^ 2
        = tensorSobolevWeight (I := I) (M := M) i (σ - 2 * θ) *
            (tensorSobolevWeight (I := I) (M := M) i θ *
              tensorSobolevWeight (I := I) (M := M) i θ) * c ^ 2 := by
          ring
    _ = tensorSobolevWeight (I := I) (M := M) i (σ - 2 * θ) *
            tensorSobolevWeight (I := I) (M := M) i (θ + θ) * c ^ 2 := by
          rw [tensorSobolevWeight_add (I := I) (M := M) i θ θ]
    _ = tensorSobolevWeight (I := I) (M := M) i
            ((σ - 2 * θ) + (θ + θ)) * c ^ 2 := by
          rw [tensorSobolevWeight_add (I := I) (M := M) i (σ - 2 * θ)
            (θ + θ)]
    _ = tensorSobolevWeight (I := I) (M := M) i σ * c ^ 2 := by
          rw [hsum]

/-- For `T ∈ Hˢ`, the `θ`-rescaled coordinate family
`i ↦ (1 + λᵢ)^θ · T.coeff i` is weighted-square-summable at the shifted
exponent `σ − 2θ`. -/
lemma fractionalPower_weighted_summable {σ : ℝ} (θ : ℝ)
    (T : tensorHs (I := I) (M := M) g r s h_atlas σ) :
    Summable (fun i : TensorEigenIdx (I := I) (M := M) g r s =>
      tensorSobolevWeight (I := I) (M := M) i (σ - 2 * θ) *
        (tensorSobolevWeight (I := I) (M := M) i θ * T.coeff i) ^ 2) := by
  have h_eq :
      (fun i : TensorEigenIdx (I := I) (M := M) g r s =>
        tensorSobolevWeight (I := I) (M := M) i (σ - 2 * θ) *
          (tensorSobolevWeight (I := I) (M := M) i θ * T.coeff i) ^ 2) =
      (fun i => tensorSobolevWeight (I := I) (M := M) i σ *
          (T.coeff i) ^ 2) := by
    funext i
    exact fractionalPower_weight_term (I := I) (M := M) i θ σ (T.coeff i)
  rw [h_eq]
  exact T.weighted_summable

/-- The underlying function of the fractional power `(1 − Δ_∇)^θ`: it
sends `T ∈ Hˢ` to the element of `H^{σ−2θ}` whose `i`-th coordinate is
`(1 + λᵢ)^θ · T.coeff i`. -/
def fractionalPowerFun {σ : ℝ} (θ : ℝ)
    (T : tensorHs (I := I) (M := M) g r s h_atlas σ) :
    tensorHs (I := I) (M := M) g r s h_atlas (σ - 2 * θ) where
  coeff i := tensorSobolevWeight (I := I) (M := M) i θ * T.coeff i
  weighted_summable := fractionalPower_weighted_summable (I := I) (M := M) θ T

@[simp] lemma fractionalPowerFun_coeff {σ : ℝ} (θ : ℝ)
    (T : tensorHs (I := I) (M := M) g r s h_atlas σ)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    (fractionalPowerFun (I := I) (M := M) θ T).coeff i =
      tensorSobolevWeight (I := I) (M := M) i θ * T.coeff i := rfl

/-- The fractional power is additive. -/
lemma fractionalPowerFun_add {σ : ℝ} (θ : ℝ)
    (S T : tensorHs (I := I) (M := M) g r s h_atlas σ) :
    fractionalPowerFun (I := I) (M := M) θ (S + T) =
      fractionalPowerFun (I := I) (M := M) θ S +
        fractionalPowerFun (I := I) (M := M) θ T := by
  ext i
  simp only [fractionalPowerFun_coeff, add_coeff]
  ring

/-- The fractional power is `ℝ`-homogeneous. -/
lemma fractionalPowerFun_smul {σ : ℝ} (θ : ℝ) (c : ℝ)
    (T : tensorHs (I := I) (M := M) g r s h_atlas σ) :
    fractionalPowerFun (I := I) (M := M) θ (c • T) =
      c • fractionalPowerFun (I := I) (M := M) θ T := by
  ext i
  simp only [fractionalPowerFun_coeff, smul_coeff]
  ring

/-- The fractional power is norm-preserving: the `H^{σ−2θ}` norm of
`fractionalPowerFun θ T` equals the `Hˢ` norm of `T`. -/
lemma norm_fractionalPowerFun {σ : ℝ} (θ : ℝ)
    (T : tensorHs (I := I) (M := M) g r s h_atlas σ) :
    ‖fractionalPowerFun (I := I) (M := M) θ T‖ = ‖T‖ := by
  -- Compare squared norms: term-by-term they agree by the weight
  -- transfer identity, hence so do the `tsum`s.
  have h_target_sq : ‖fractionalPowerFun (I := I) (M := M) θ T‖ ^ 2 =
      ∑' i, tensorSobolevWeight (I := I) (M := M) i (σ - 2 * θ) *
        (tensorSobolevWeight (I := I) (M := M) i θ * T.coeff i) ^ 2 := by
    have h := norm_sq_eq_tsum (I := I) (M := M)
      (fractionalPowerFun (I := I) (M := M) θ T)
    simpa only [fractionalPowerFun_coeff] using h
  have h_source_sq : ‖T‖ ^ 2 =
      ∑' i, tensorSobolevWeight (I := I) (M := M) i σ * (T.coeff i) ^ 2 :=
    norm_sq_eq_tsum (I := I) (M := M) T
  have h_terms : ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
      tensorSobolevWeight (I := I) (M := M) i (σ - 2 * θ) *
          (tensorSobolevWeight (I := I) (M := M) i θ * T.coeff i) ^ 2 =
        tensorSobolevWeight (I := I) (M := M) i σ * (T.coeff i) ^ 2 :=
    fun i => fractionalPower_weight_term (I := I) (M := M) i θ σ (T.coeff i)
  have h_sq_eq : ‖fractionalPowerFun (I := I) (M := M) θ T‖ ^ 2 =
      ‖T‖ ^ 2 := by
    rw [h_target_sq, h_source_sq]
    exact tsum_congr h_terms
  have h1 : 0 ≤ ‖fractionalPowerFun (I := I) (M := M) θ T‖ := norm_nonneg _
  have h2 : 0 ≤ ‖T‖ := norm_nonneg T
  have := congrArg Real.sqrt h_sq_eq
  rwa [Real.sqrt_sq h1, Real.sqrt_sq h2] at this

end tensorHs

/-! ## The fractional power as a continuous linear operator -/

/-- The fractional power `(1 − Δ_∇)^θ` of the shifted rough Laplacian,
as a continuous linear operator on the spectral Sobolev scale. It
multiplies the `i`-th eigenbasis coordinate by `(1 + λᵢ)^θ`, where
`λᵢ ≥ 0` is the connection-Laplacian eigenvalue.

Because the `Hˢ` norm squares the coordinate, the operator shifts the
scale by `2θ`: it maps `Hˢ` isometrically to `H^{σ−2θ}`. See
`tensorFractionalPower_coeff` for the coordinate formula and
`tensorFractionalPower_norm` for the isometry. -/
def tensorFractionalPower {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M) (θ : ℝ) {σ : ℝ} :
    tensorHs (I := I) (M := M) g r s h_atlas σ →L[ℝ]
      tensorHs (I := I) (M := M) g r s h_atlas (σ - 2 * θ) :=
  LinearMap.mkContinuous
    { toFun := tensorHs.fractionalPowerFun (I := I) (M := M) θ
      map_add' := tensorHs.fractionalPowerFun_add (I := I) (M := M) θ
      map_smul' := fun c T =>
        tensorHs.fractionalPowerFun_smul (I := I) (M := M) θ c T }
    1
    (fun T => by
      change ‖tensorHs.fractionalPowerFun (I := I) (M := M) θ T‖ ≤ 1 * ‖T‖
      rw [one_mul]
      exact le_of_eq (tensorHs.norm_fractionalPowerFun (I := I) (M := M) θ T))

/-- `tensorFractionalPower` applied to `T` is the underlying
`fractionalPowerFun T`. -/
@[simp] lemma tensorFractionalPower_apply {g : SmoothRiemannianMetric I M}
    {r s : ℕ} {h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M} {σ : ℝ}
    (θ : ℝ) (T : tensorHs (I := I) (M := M) g r s h_atlas σ) :
    tensorFractionalPower (I := I) (M := M) (g := g) (r := r) (s := s) h_atlas θ T =
      tensorHs.fractionalPowerFun (I := I) (M := M) θ T := rfl

/-- The coordinate formula for the fractional power: `(1 − Δ_∇)^θ`
multiplies the `i`-th coordinate by `(1 + λᵢ)^θ`. -/
@[simp] theorem tensorFractionalPower_coeff {g : SmoothRiemannianMetric I M}
    {r s : ℕ} {h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M} {σ : ℝ}
    (θ : ℝ) (T : tensorHs (I := I) (M := M) g r s h_atlas σ)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    (tensorFractionalPower (I := I) (M := M) (g := g) (r := r) (s := s) h_atlas θ T).coeff i =
      tensorSobolevWeight (I := I) (M := M) i θ * T.coeff i := rfl

/-- The operator norm of the fractional power is at most `1`. (It is in
fact an isometry; see `tensorFractionalPower_norm`.) -/
theorem tensorFractionalPower_opNorm_le_one {g : SmoothRiemannianMetric I M}
    {r s : ℕ} {h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M} {σ : ℝ}
    (θ : ℝ) :
    ‖tensorFractionalPower (I := I) (M := M) (g := g) (r := r) (s := s) (σ := σ) h_atlas θ‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

/-- The fractional power `(1 − Δ_∇)^θ` is an isometry: the `H^{σ−2θ}`
norm of `(1 − Δ_∇)^θ T` equals the `Hˢ` norm of `T`. -/
theorem tensorFractionalPower_norm {g : SmoothRiemannianMetric I M}
    {r s : ℕ} {h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M} {σ : ℝ}
    (θ : ℝ) (T : tensorHs (I := I) (M := M) g r s h_atlas σ) :
    ‖tensorFractionalPower (I := I) (M := M) (g := g) (r := r) (s := s) h_atlas θ T‖ = ‖T‖ :=
  tensorHs.norm_fractionalPowerFun (I := I) (M := M) θ T

/-- The fractional power preserves the `Hˢ` inner product: it is an
isometric linear map, hence inner-product preserving. -/
theorem tensorFractionalPower_inner {g : SmoothRiemannianMetric I M}
    {r s : ℕ} {h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M} {σ : ℝ}
    (θ : ℝ) (S T : tensorHs (I := I) (M := M) g r s h_atlas σ) :
    (inner ℝ (tensorFractionalPower (I := I) (M := M) (g := g) (r := r) (s := s) h_atlas θ S)
        (tensorFractionalPower (I := I) (M := M) (g := g) (r := r) (s := s) h_atlas θ T) : ℝ) =
      inner ℝ S T := by
  -- The weighted inner-product series match term-by-term:
  -- `(1+λ)^{σ-2θ}·((1+λ)^θ a)·((1+λ)^θ b) = (1+λ)^σ·a·b`.
  rw [tensorHs.inner_def, tensorHs.inner_def]
  refine tsum_congr (fun i => ?_)
  simp only [tensorFractionalPower_coeff]
  have hsum : (σ - 2 * θ) + (θ + θ) = σ := by ring
  calc
    tensorSobolevWeight (I := I) (M := M) i (σ - 2 * θ) *
          (tensorSobolevWeight (I := I) (M := M) i θ * S.coeff i *
            (tensorSobolevWeight (I := I) (M := M) i θ * T.coeff i))
        = tensorSobolevWeight (I := I) (M := M) i (σ - 2 * θ) *
            (tensorSobolevWeight (I := I) (M := M) i θ *
              tensorSobolevWeight (I := I) (M := M) i θ) *
            (S.coeff i * T.coeff i) := by ring
    _ = tensorSobolevWeight (I := I) (M := M) i (σ - 2 * θ) *
            tensorSobolevWeight (I := I) (M := M) i (θ + θ) *
            (S.coeff i * T.coeff i) := by
          rw [← tensorHs.tensorSobolevWeight_add (I := I) (M := M) i θ θ]
    _ = tensorSobolevWeight (I := I) (M := M) i
            ((σ - 2 * θ) + (θ + θ)) * (S.coeff i * T.coeff i) := by
          rw [← tensorHs.tensorSobolevWeight_add (I := I) (M := M)
            i (σ - 2 * θ) (θ + θ)]
    _ = tensorSobolevWeight (I := I) (M := M) i σ *
          (S.coeff i * T.coeff i) := by rw [hsum]

/-! ## The group law `(1 − Δ_∇)^θ ∘ (1 − Δ_∇)^φ = (1 − Δ_∇)^{θ+φ}`

The fractional powers form a one-parameter group: composition adds the
exponents and the zeroth power is the identity. Diagrammatically, the
scales line up — `(1−Δ)^φ : Hˢ → H^{σ−2φ}` then
`(1−Δ)^θ : H^{σ−2φ} → H^{σ−2φ−2θ} = H^{σ−2(θ+φ)}`. -/

/-- The fractional power at exponent `0` fixes the coordinate family:
the weight `(1 + λᵢ)^0 = 1`. The target scale is `σ − 2·0`, so this is
stated as an equality of coordinate families. -/
@[simp] theorem tensorFractionalPower_zero_coeff
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    {h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M} {σ : ℝ}
    (T : tensorHs (I := I) (M := M) g r s h_atlas σ)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    (tensorFractionalPower (I := I) (M := M) (g := g) (r := r) (s := s) h_atlas (0 : ℝ) T).coeff i =
      T.coeff i := by
  rw [tensorFractionalPower_coeff, tensorSobolevWeight_zero, one_mul]

/-- The fractional power at exponent `0` is the identity, modulo the
definitional scale rewrite `σ − 2·0 = σ`: it sends `T` to
`tensorHs.cast` of `T`. -/
theorem tensorFractionalPower_zero
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    {h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M} {σ : ℝ}
    (T : tensorHs (I := I) (M := M) g r s h_atlas σ) :
    tensorFractionalPower (I := I) (M := M) (g := g) (r := r) (s := s) h_atlas (0 : ℝ) T =
      tensorHs.cast (I := I) (M := M) (h_atlas := h_atlas)
        (by ring : σ = σ - 2 * 0) T := by
  refine tensorHs.ext ?_
  funext i
  rw [tensorFractionalPower_zero_coeff, tensorHs.cast_coeff]

/-- The group law for fractional powers, applied form: composing
`(1 − Δ_∇)^θ` after `(1 − Δ_∇)^φ` yields `(1 − Δ_∇)^{θ+φ}`. The
intermediate scale is `H^{σ−2φ}` and the final scale is
`H^{σ−2(θ+φ)}`. -/
theorem tensorFractionalPower_add_apply {g : SmoothRiemannianMetric I M}
    {r s : ℕ} {h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M} {σ : ℝ}
    (θ φ : ℝ) (T : tensorHs (I := I) (M := M) g r s h_atlas σ) :
    tensorFractionalPower (I := I) (M := M) (g := g) (r := r) (s := s) h_atlas θ
        (tensorFractionalPower (I := I) (M := M) (g := g) (r := r) (s := s) h_atlas φ T) =
      (tensorHs.cast (I := I) (M := M) (h_atlas := h_atlas)
        (by ring :
          σ - 2 * (θ + φ) = (σ - 2 * φ) - 2 * θ))
        (tensorFractionalPower (I := I) (M := M) (g := g) (r := r) (s := s) h_atlas (θ + φ) T) := by
  refine tensorHs.ext ?_
  funext i
  rw [tensorFractionalPower_coeff, tensorFractionalPower_coeff,
    tensorHs.cast_coeff, tensorFractionalPower_coeff,
    tensorHs.tensorSobolevWeight_add (I := I) (M := M) i θ φ]
  ring

/-! ## The fractional power as a linear isometric equivalence

`(1 − Δ_∇)^θ` is invertible, with inverse `(1 − Δ_∇)^{−θ}`. Packaged as
a `LinearIsometryEquiv`, it realises the abstract fact that the spectral
Sobolev spaces `Hˢ` and `H^{σ−2θ}` are isometrically isomorphic. The
inversion identity is `(1+λ)^θ · ((1+λ)^{−θ} · c) = c`. -/

/-- The fractional power `(1 − Δ_∇)^θ` packaged as a linear isometric
equivalence `Hˢ ≃ₗᵢ[ℝ] H^{σ−2θ}`. The forward map is the spectral
multiplier by `(1 + λᵢ)^θ`; its inverse is `(1 − Δ_∇)^{−θ}`, the
multiplier by `(1 + λᵢ)^{−θ}`. See `tensorFractionalPowerEquiv_symm`. -/
def tensorFractionalPowerEquiv {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M) (θ σ : ℝ) :
    tensorHs (I := I) (M := M) g r s h_atlas σ ≃ₗᵢ[ℝ]
      tensorHs (I := I) (M := M) g r s h_atlas (σ - 2 * θ) where
  toFun := tensorHs.fractionalPowerFun (I := I) (M := M) θ
  invFun T :=
    tensorHs.cast (I := I) (M := M) (h_atlas := h_atlas)
      (by ring : σ - 2 * θ - 2 * (-θ) = σ)
      (tensorHs.fractionalPowerFun (I := I) (M := M) (-θ) T)
  map_add' := tensorHs.fractionalPowerFun_add (I := I) (M := M) θ
  map_smul' := fun c T =>
    tensorHs.fractionalPowerFun_smul (I := I) (M := M) θ c T
  left_inv T := by
    refine tensorHs.ext ?_
    funext i
    simp only [tensorHs.cast_coeff, tensorHs.fractionalPowerFun_coeff,
      tensorHs.tensorSobolevWeight_neg (I := I) (M := M) i θ]
    have hw_pos : 0 < tensorSobolevWeight (I := I) (M := M) i θ :=
      tensorSobolevWeight_pos (I := I) (M := M) i θ
    rw [← mul_assoc, inv_mul_cancel₀ hw_pos.ne', one_mul]
  right_inv T := by
    refine tensorHs.ext ?_
    funext i
    simp only [tensorHs.fractionalPowerFun_coeff, tensorHs.cast_coeff,
      tensorHs.tensorSobolevWeight_neg (I := I) (M := M) i θ]
    have hw_pos : 0 < tensorSobolevWeight (I := I) (M := M) i θ :=
      tensorSobolevWeight_pos (I := I) (M := M) i θ
    rw [← mul_assoc, mul_inv_cancel₀ hw_pos.ne', one_mul]
  norm_map' T := tensorHs.norm_fractionalPowerFun (I := I) (M := M) θ T

/-- `tensorFractionalPowerEquiv` applied to `T` is the underlying
`fractionalPowerFun T`; it agrees with `tensorFractionalPower`. -/
@[simp] theorem tensorFractionalPowerEquiv_apply
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    {h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M} (θ σ : ℝ)
    (T : tensorHs (I := I) (M := M) g r s h_atlas σ) :
    tensorFractionalPowerEquiv (I := I) (M := M) h_atlas θ σ T =
      tensorFractionalPower (I := I) (M := M) (g := g) (r := r) (s := s) h_atlas θ T := rfl

/-- The coordinate formula for the fractional-power equivalence. -/
@[simp] theorem tensorFractionalPowerEquiv_coeff
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    {h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M} (θ σ : ℝ)
    (T : tensorHs (I := I) (M := M) g r s h_atlas σ)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    (tensorFractionalPowerEquiv (I := I) (M := M) h_atlas θ σ T).coeff i =
      tensorSobolevWeight (I := I) (M := M) i θ * T.coeff i := rfl

/-- The fractional-power equivalence at exponent `θ`, regarded as a
continuous linear map (via its `ContinuousLinearEquiv`), is the operator
`tensorFractionalPower`. -/
theorem tensorFractionalPowerEquiv_toContinuousLinearMap
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    {h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M} (θ σ : ℝ) :
    (tensorFractionalPowerEquiv (I := I) (M := M) (g := g) (r := r) (s := s)
        h_atlas θ σ).toContinuousLinearEquiv.toContinuousLinearMap =
      tensorFractionalPower (I := I) (M := M) (g := g) (r := r) (s := s) (σ := σ) h_atlas θ := by
  refine ContinuousLinearMap.ext (fun T => ?_)
  rfl

/-- The inverse of the fractional-power equivalence is `(1 − Δ_∇)^{−θ}`:
inverting `(1 − Δ_∇)^θ` is the same as raising to the negated exponent.
The cast records the definitional scale `σ − 2θ − 2(−θ) = σ`. -/
theorem tensorFractionalPowerEquiv_symm {g : SmoothRiemannianMetric I M}
    {r s : ℕ} {h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M}
    (θ σ : ℝ) (T : tensorHs (I := I) (M := M) g r s h_atlas (σ - 2 * θ)) :
    (tensorFractionalPowerEquiv (I := I) (M := M) h_atlas θ σ).symm T =
      tensorHs.cast (I := I) (M := M) (h_atlas := h_atlas)
        (by ring : σ - 2 * θ - 2 * (-θ) = σ)
        (tensorFractionalPower (I := I) (M := M) (g := g) (r := r) (s := s) h_atlas (-θ) T) := rfl

/-- The fractional-power equivalence is an isometry, in norm form. -/
theorem tensorFractionalPowerEquiv_norm {g : SmoothRiemannianMetric I M}
    {r s : ℕ} {h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M}
    (θ σ : ℝ) (T : tensorHs (I := I) (M := M) g r s h_atlas σ) :
    ‖tensorFractionalPowerEquiv (I := I) (M := M) h_atlas θ σ T‖ = ‖T‖ :=
  tensorHs.norm_fractionalPowerFun (I := I) (M := M) θ T

/-! ## The scale shift `Λˢ` by exactly `s`

`tensorFractionalPower θ` shifts the scale by `2θ`. The companion
operator that shifts by *exactly* `s` is `Λˢ := (1 − Δ_∇)^{s/2}`,
multiplying the coordinate by `(1 + λᵢ)^{s/2}`. It maps `Hˢ`
isometrically to `H^{σ−s}`. Concretely it is `tensorFractionalPower`
at exponent `s/2`, with the target scale `σ − 2·(s/2)` rewritten to the
on-the-nose `σ − s`. -/

namespace tensorHs

variable {g : SmoothRiemannianMetric I M} {r s : ℕ}
  {h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M}

/-- For `T ∈ Hˢ`, the `(sh/2)`-rescaled coordinate family is
weighted-square-summable at the exponent `σ − sh`. (This is the
`σ − 2·(sh/2) = σ − sh` repackaging of `fractionalPower_weighted_summable`.) -/
lemma lambdaPower_weighted_summable {σ : ℝ} (sh : ℝ)
    (T : tensorHs (I := I) (M := M) g r s h_atlas σ) :
    Summable (fun i : TensorEigenIdx (I := I) (M := M) g r s =>
      tensorSobolevWeight (I := I) (M := M) i (σ - sh) *
        (tensorSobolevWeight (I := I) (M := M) i (sh / 2) *
          T.coeff i) ^ 2) := by
  have h := fractionalPower_weighted_summable (I := I) (M := M)
    (σ := σ) (sh / 2) T
  have heq : σ - 2 * (sh / 2) = σ - sh := by ring
  rwa [heq] at h

/-- The underlying function of the scale shift `Λˢ`: it multiplies the
`i`-th coordinate by `(1 + λᵢ)^{sh/2}` and lands in `H^{σ−sh}`. -/
def lambdaPowerFun {σ : ℝ} (sh : ℝ)
    (T : tensorHs (I := I) (M := M) g r s h_atlas σ) :
    tensorHs (I := I) (M := M) g r s h_atlas (σ - sh) where
  coeff i := tensorSobolevWeight (I := I) (M := M) i (sh / 2) * T.coeff i
  weighted_summable := lambdaPower_weighted_summable (I := I) (M := M) sh T

@[simp] lemma lambdaPowerFun_coeff {σ : ℝ} (sh : ℝ)
    (T : tensorHs (I := I) (M := M) g r s h_atlas σ)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    (lambdaPowerFun (I := I) (M := M) sh T).coeff i =
      tensorSobolevWeight (I := I) (M := M) i (sh / 2) * T.coeff i := rfl

/-- The scale shift is additive. -/
lemma lambdaPowerFun_add {σ : ℝ} (sh : ℝ)
    (S T : tensorHs (I := I) (M := M) g r s h_atlas σ) :
    lambdaPowerFun (I := I) (M := M) sh (S + T) =
      lambdaPowerFun (I := I) (M := M) sh S +
        lambdaPowerFun (I := I) (M := M) sh T := by
  ext i
  simp only [lambdaPowerFun_coeff, add_coeff]
  ring

/-- The scale shift is `ℝ`-homogeneous. -/
lemma lambdaPowerFun_smul {σ : ℝ} (sh : ℝ) (c : ℝ)
    (T : tensorHs (I := I) (M := M) g r s h_atlas σ) :
    lambdaPowerFun (I := I) (M := M) sh (c • T) =
      c • lambdaPowerFun (I := I) (M := M) sh T := by
  ext i
  simp only [lambdaPowerFun_coeff, smul_coeff]
  ring

/-- The scale shift is norm-preserving. -/
lemma norm_lambdaPowerFun {σ : ℝ} (sh : ℝ)
    (T : tensorHs (I := I) (M := M) g r s h_atlas σ) :
    ‖lambdaPowerFun (I := I) (M := M) sh T‖ = ‖T‖ := by
  have h_target_sq : ‖lambdaPowerFun (I := I) (M := M) sh T‖ ^ 2 =
      ∑' i, tensorSobolevWeight (I := I) (M := M) i (σ - sh) *
        (tensorSobolevWeight (I := I) (M := M) i (sh / 2) *
          T.coeff i) ^ 2 := by
    have h := norm_sq_eq_tsum (I := I) (M := M)
      (lambdaPowerFun (I := I) (M := M) sh T)
    simpa only [lambdaPowerFun_coeff] using h
  have h_source_sq : ‖T‖ ^ 2 =
      ∑' i, tensorSobolevWeight (I := I) (M := M) i σ * (T.coeff i) ^ 2 :=
    norm_sq_eq_tsum (I := I) (M := M) T
  have h_terms : ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
      tensorSobolevWeight (I := I) (M := M) i (σ - sh) *
          (tensorSobolevWeight (I := I) (M := M) i (sh / 2) *
            T.coeff i) ^ 2 =
        tensorSobolevWeight (I := I) (M := M) i σ * (T.coeff i) ^ 2 := by
    intro i
    have h := fractionalPower_weight_term (I := I) (M := M)
      i (sh / 2) σ (T.coeff i)
    have heq : σ - 2 * (sh / 2) = σ - sh := by ring
    rwa [heq] at h
  have h_sq_eq : ‖lambdaPowerFun (I := I) (M := M) sh T‖ ^ 2 = ‖T‖ ^ 2 := by
    rw [h_target_sq, h_source_sq]
    exact tsum_congr h_terms
  have h1 : 0 ≤ ‖lambdaPowerFun (I := I) (M := M) sh T‖ := norm_nonneg _
  have h2 : 0 ≤ ‖T‖ := norm_nonneg T
  have := congrArg Real.sqrt h_sq_eq
  rwa [Real.sqrt_sq h1, Real.sqrt_sq h2] at this

end tensorHs

/-- The scale-shift operator `Λˢ := (1 − Δ_∇)^{s/2}`: it multiplies the
`i`-th coordinate by `(1 + λᵢ)^{s/2}` and shifts the Sobolev scale by
*exactly* `s`, mapping `Hˢ` isometrically to `H^{σ−s}`. (See
`tensorLambdaPower_eq_fractionalPower` for its identification with
`tensorFractionalPower (s/2)`.) -/
def tensorLambdaPower {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M) (sh : ℝ) {σ : ℝ} :
    tensorHs (I := I) (M := M) g r s h_atlas σ →L[ℝ]
      tensorHs (I := I) (M := M) g r s h_atlas (σ - sh) :=
  LinearMap.mkContinuous
    { toFun := tensorHs.lambdaPowerFun (I := I) (M := M) sh
      map_add' := tensorHs.lambdaPowerFun_add (I := I) (M := M) sh
      map_smul' := fun c T =>
        tensorHs.lambdaPowerFun_smul (I := I) (M := M) sh c T }
    1
    (fun T => by
      change ‖tensorHs.lambdaPowerFun (I := I) (M := M) sh T‖ ≤ 1 * ‖T‖
      rw [one_mul]
      exact le_of_eq (tensorHs.norm_lambdaPowerFun (I := I) (M := M) sh T))

/-- `tensorLambdaPower` applied to `T` is the underlying
`lambdaPowerFun T`. -/
@[simp] lemma tensorLambdaPower_apply {g : SmoothRiemannianMetric I M}
    {r s : ℕ} {h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M} {σ : ℝ}
    (sh : ℝ) (T : tensorHs (I := I) (M := M) g r s h_atlas σ) :
    tensorLambdaPower (I := I) (M := M) (g := g) (r := r) (s := s) h_atlas sh T =
      tensorHs.lambdaPowerFun (I := I) (M := M) sh T := rfl

/-- The coordinate formula for the scale shift: `Λˢ` multiplies the
`i`-th coordinate by `(1 + λᵢ)^{s/2}`. -/
@[simp] theorem tensorLambdaPower_coeff {g : SmoothRiemannianMetric I M}
    {r s : ℕ} {h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M} {σ : ℝ}
    (sh : ℝ) (T : tensorHs (I := I) (M := M) g r s h_atlas σ)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    (tensorLambdaPower (I := I) (M := M) (g := g) (r := r) (s := s) h_atlas sh T).coeff i =
      tensorSobolevWeight (I := I) (M := M) i (sh / 2) * T.coeff i := rfl

/-- The scale shift `Λˢ` is an isometry: `‖Λˢ T‖_{H^{σ−s}} = ‖T‖_{Hˢ}`. -/
theorem tensorLambdaPower_norm {g : SmoothRiemannianMetric I M}
    {r s : ℕ} {h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M} {σ : ℝ}
    (sh : ℝ) (T : tensorHs (I := I) (M := M) g r s h_atlas σ) :
    ‖tensorLambdaPower (I := I) (M := M) (g := g) (r := r) (s := s) h_atlas sh T‖ = ‖T‖ :=
  tensorHs.norm_lambdaPowerFun (I := I) (M := M) sh T

/-- The operator norm of the scale shift is at most `1` (it is an
isometry; see `tensorLambdaPower_norm`). -/
theorem tensorLambdaPower_opNorm_le_one {g : SmoothRiemannianMetric I M}
    {r s : ℕ} {h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M} {σ : ℝ}
    (sh : ℝ) :
    ‖tensorLambdaPower (I := I) (M := M) (g := g) (r := r) (s := s) (σ := σ) h_atlas sh‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

/-- The scale shift `Λˢ` is the fractional power `(1 − Δ_∇)^{s/2}`,
modulo the definitional scale rewrite `σ − 2·(s/2) = σ − s`: applied to
`T`, both produce the coordinate family `i ↦ (1 + λᵢ)^{s/2} · T.coeff i`. -/
theorem tensorLambdaPower_eq_fractionalPower
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    {h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M} {σ : ℝ}
    (sh : ℝ) (T : tensorHs (I := I) (M := M) g r s h_atlas σ) :
    tensorLambdaPower (I := I) (M := M) (g := g) (r := r) (s := s) h_atlas sh T =
      tensorHs.cast (I := I) (M := M) (h_atlas := h_atlas)
        (by ring : σ - 2 * (sh / 2) = σ - sh)
        (tensorFractionalPower (I := I) (M := M) (g := g) (r := r) (s := s) h_atlas (sh / 2) T) := by
  refine tensorHs.ext ?_
  funext i
  rw [tensorLambdaPower_coeff, tensorHs.cast_coeff,
    tensorFractionalPower_coeff]

/-- The scale shift at `sh = 0` fixes the coordinate family. The target
scale is `σ − 0`, so this is stated coordinatewise. -/
@[simp] theorem tensorLambdaPower_zero_coeff
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    {h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M} {σ : ℝ}
    (T : tensorHs (I := I) (M := M) g r s h_atlas σ)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    (tensorLambdaPower (I := I) (M := M) (g := g) (r := r) (s := s) h_atlas (0 : ℝ) T).coeff i =
      T.coeff i := by
  rw [tensorLambdaPower_coeff, zero_div, tensorSobolevWeight_zero, one_mul]

/-! ## Interaction with the Sobolev-scale inclusion

The fractional power and the scale inclusion `tensorHsInclusion`
(`Hˢ ↪ Hᵗ` for `τ ≤ σ`) both act on coordinate families, so they
commute: applying `(1 − Δ_∇)^θ` then including, or including then
applying `(1 − Δ_∇)^θ`, gives the same coordinate family. -/

/-- The fractional power commutes with the Sobolev-scale inclusion: for
`τ ≤ σ`, including `Hˢ ↪ Hᵗ` then applying `(1 − Δ_∇)^θ` agrees with
applying `(1 − Δ_∇)^θ` then including `H^{σ−2θ} ↪ H^{τ−2θ}`. Both routes
multiply the coordinate by `(1 + λᵢ)^θ` without touching the index. -/
theorem tensorFractionalPower_tensorHsInclusion
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    {h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M} {τ σ : ℝ}
    (θ : ℝ) (hτσ : τ ≤ σ)
    (T : tensorHs (I := I) (M := M) g r s h_atlas σ) :
    tensorFractionalPower (I := I) (M := M) (g := g) (r := r) (s := s) h_atlas θ
        (tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s) h_atlas hτσ T) =
      tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s) h_atlas
        (sub_le_sub_right hτσ (2 * θ))
        (tensorFractionalPower (I := I) (M := M) (g := g) (r := r) (s := s) h_atlas θ T) := by
  refine tensorHs.ext ?_
  funext i
  rw [tensorFractionalPower_coeff, tensorHsInclusion_coeff_apply,
    tensorHsInclusion_coeff_apply, tensorFractionalPower_coeff]

/-- The fractional power commutes with the Sobolev-scale inclusion, in
operator form: `(1 − Δ_∇)^θ ∘ ι_{τ≤σ} = ι_{τ−2θ ≤ σ−2θ} ∘ (1 − Δ_∇)^θ`
as continuous linear maps `Hˢ → H^{τ−2θ}`. -/
theorem tensorFractionalPower_comp_tensorHsInclusion
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    {h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M} {τ σ : ℝ}
    (θ : ℝ) (hτσ : τ ≤ σ) :
    (tensorFractionalPower (I := I) (M := M) (g := g) (r := r) (s := s) h_atlas θ).comp
        (tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s) h_atlas hτσ) =
      (tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s) h_atlas
          (sub_le_sub_right hτσ (2 * θ))).comp
        (tensorFractionalPower (I := I) (M := M) (σ := σ)
          h_atlas θ) := by
  refine ContinuousLinearMap.ext (fun T => ?_)
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
  exact tensorFractionalPower_tensorHsInclusion (I := I) (M := M) θ hτσ T

/-! ## The Sobolev scales are mutually isometrically isomorphic

A direct corollary of the fractional-power equivalence: for any two
exponents `σ`, `τ`, the spectral Sobolev spaces `Hˢ` and `Hᵗ` are
isometrically isomorphic. The isomorphism is `(1 − Δ_∇)^{(σ−τ)/2}`,
which by the scale convention drops the scale by exactly `σ − τ`. -/

/-- For any two exponents `σ` and `τ`, the spectral Sobolev spaces `Hˢ`
and `Hᵗ` are isometrically isomorphic. The witnessing equivalence is the
fractional power `(1 − Δ_∇)^{(σ−τ)/2}`: it multiplies the coordinate by
`(1 + λᵢ)^{(σ−τ)/2}` and shifts the scale from `σ` to
`σ − (σ−τ) = τ`. -/
def tensorHsEquivOfFractionalPower {g : SmoothRiemannianMetric I M}
    {r s : ℕ} (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (σ τ : ℝ) :
    tensorHs (I := I) (M := M) g r s h_atlas σ ≃ₗᵢ[ℝ]
      tensorHs (I := I) (M := M) g r s h_atlas τ :=
  (tensorFractionalPowerEquiv (I := I) (M := M) h_atlas
    ((σ - τ) / 2) σ).trans
    (tensorHs.castEquiv (I := I) (M := M) (h_atlas := h_atlas)
      (by ring : σ - 2 * ((σ - τ) / 2) = τ))

/-- The coordinate formula for the inter-scale isometry: it multiplies
the `i`-th coordinate by `(1 + λᵢ)^{(σ−τ)/2}`. -/
@[simp] theorem tensorHsEquivOfFractionalPower_coeff
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    {h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M} (σ τ : ℝ)
    (T : tensorHs (I := I) (M := M) g r s h_atlas σ)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    (tensorHsEquivOfFractionalPower (I := I) (M := M) h_atlas σ τ T).coeff
        i =
      tensorSobolevWeight (I := I) (M := M) i ((σ - τ) / 2) * T.coeff i := by
  unfold tensorHsEquivOfFractionalPower
  rw [LinearIsometryEquiv.trans_apply]
  change (tensorHs.castEquiv (I := I) (M := M) (h_atlas := h_atlas) _
    (tensorFractionalPowerEquiv (I := I) (M := M) h_atlas
      ((σ - τ) / 2) σ T)).coeff i = _
  rw [tensorHs.castEquiv_coeff, tensorFractionalPowerEquiv_coeff]

/-- The inter-scale isometry is norm-preserving: `‖·‖_{Hᵗ} = ‖·‖_{Hˢ}`.
This is the precise sense in which all the spectral Sobolev spaces are
"the same" Hilbert space, with the eigen-coordinates merely reweighted. -/
theorem tensorHsEquivOfFractionalPower_norm
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    {h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M} (σ τ : ℝ)
    (T : tensorHs (I := I) (M := M) g r s h_atlas σ) :
    ‖tensorHsEquivOfFractionalPower (I := I) (M := M) h_atlas σ τ T‖ =
      ‖T‖ :=
  (tensorHsEquivOfFractionalPower (I := I) (M := M)
    h_atlas σ τ).norm_map T

/-! ## Sanity tests -/

example {g : SmoothRiemannianMetric I M} {r s : ℕ}
    {h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M} (θ : ℝ) {σ : ℝ} :
    tensorHs (I := I) (M := M) g r s h_atlas σ →L[ℝ]
      tensorHs (I := I) (M := M) g r s h_atlas (σ - 2 * θ) :=
  tensorFractionalPower (I := I) (M := M) (g := g) (r := r) (s := s) h_atlas θ

example {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M) (θ σ : ℝ) :
    tensorHs (I := I) (M := M) g r s h_atlas σ ≃ₗᵢ[ℝ]
      tensorHs (I := I) (M := M) g r s h_atlas (σ - 2 * θ) :=
  tensorFractionalPowerEquiv (I := I) (M := M) h_atlas θ σ

example {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M) (σ τ : ℝ) :
    tensorHs (I := I) (M := M) g r s h_atlas σ ≃ₗᵢ[ℝ]
      tensorHs (I := I) (M := M) g r s h_atlas τ :=
  tensorHsEquivOfFractionalPower (I := I) (M := M) h_atlas σ τ

end TensorHeatEquation
end Parabolic
end Analysis
end DifferentialGeometry

end
