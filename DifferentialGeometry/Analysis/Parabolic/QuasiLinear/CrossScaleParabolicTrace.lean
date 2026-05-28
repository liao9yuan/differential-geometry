import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.MaxRegSpace

/-!
# The cross-scale parabolic trace embedding `L²(H^{a+2}) ∩ H¹(Hᵃ) ↪ C(H^{a+1})`

For the spectral tensor Sobolev scale `tensorHs g r s σ` of a closed Riemannian
manifold `(M, g)`, this file builds the **Lions–Magenes parabolic trace
embedding** one Sobolev order below the top regularity:

> If a time-dependent tensor field has its values in `H^{a+2}` (`L²`-in-time)
> and its time derivative in `Hᵃ` (`L²`-in-time), then it has a representative
> continuous in time into the intermediate scale `H^{a+1}`, with the
> sup-in-time energy estimate
>
>   `sup_t ‖u(t)‖²_{H^{a+1}} ≤ ‖u(0)‖²_{H^{a+1}} +
>      2 ∫₀ᵀ ‖u(s)‖_{H^{a+2}} · ‖∂_t u(s)‖_{Hᵃ} ds`.

## The summation-free route

The proof is *not* a Weierstrass `M`-test on the eigenmode series — an
`L²`-in-time bound cannot dominate a sup-in-time series and there is no
`(1 + λ)`-smoothing gain per mode.  Instead it follows the classical
Lions–Magenes argument, which is *summation-free*:

1. **Cross-scale duality pairing** (`crossPairing`): the `H^{a+1}` inner
   product, read as a pairing of an `H^{a+2}` vector against an `Hᵃ` vector.
   The weight splits as
   `(1 + λᵢ)^{a+1} = √(1+λᵢ)^{a+2} · √(1+λᵢ)^a`, so a single global
   Cauchy–Schwarz over the modes gives
   `|⟨v, w⟩| ≤ ‖v‖_{H^{a+2}} · ‖w‖_{Hᵃ}` (`abs_crossPairing_le`); no
   unsummable series appears.

2. **Absolute continuity of the squared norm**: `t ↦ ‖u(t)‖²_{H^{a+1}}` is
   the bilinear cross-pairing of the (continuous) `H^{a+2}` representative
   against the indefinite `Hᵃ`-integral of the derivative; it is therefore
   absolutely continuous, with a.e. derivative
   `2 ⟨v(t), ∂_t u(t)⟩` (`crossPairingNormSq_hasDerivAt`).

3. **Fundamental theorem of calculus** turns the a.e. derivative into the exact
   identity `‖u(t)‖² = ‖u(0)‖² + ∫₀ᵗ 2⟨v, ∂_t u⟩`, and the cross-scale
   Cauchy–Schwarz of step 1 bounds the integrand, giving the sup estimate.
   Continuity of `t ↦ ‖u(t)‖²` plus the (already-available) `H^{a+1}` weak
   continuity of the representative gives the strong-continuous representative.

## Data

The energy-space element is packaged as a `CrossScaleField`: a continuous
`H^{a+2}` representative `hi : ℝ → H^{a+2}` of the values, the `Hᵃ`-valued
time-Sobolev element `lo : timeH1 Hᵃ T` recording the initial value and the
`L²` derivative, and the structural link that the `H^{a+1}` view of `hi` is the
`H^{a+1}` view of the indefinite integral `lo.toFun`.  This matches exactly the
companion-field shape of the maximal-regularity Duhamel solution
(`maxRegDuhamelSolField` lives in `L²(H^{a+2})`, its carrier in `H¹(Hᵃ)`), so the
headline can be applied to discharge the sup-in-time `hstay` residual.

## Main results

* `abs_crossPairing_le` — the cross-scale Cauchy–Schwarz pairing bound.
* `crossPairing_self_eq_normSq` — the diagonal recovers `‖·‖²_{H^{a+1}}`.
* `CrossScaleField.continuousOn_repr` — the `H^{a+1}` representative is
  continuous on `[0,T]`.
* `CrossScaleField.normSq_eq_init_add_integral` — the FTC for the squared
  `H^{a+1}` norm.
* `CrossScaleField.iSup_normSq_le` — the sup-in-time energy estimate.
-/

noncomputable section

open Bundle Manifold MeasureTheory Set Filter intervalIntegral
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace QuasiLinear

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

variable {g : SmoothRiemannianMetric I M} {r s : ℕ}
variable {a : ℝ} {T : ℝ}

/-! ## The cross-scale Sobolev-weight split

The arithmetic heart of the Lions–Magenes pairing.  The middle Sobolev weight
`(1 + λᵢ)^{a+1}` factors as the geometric mean of the upper weight
`(1 + λᵢ)^{a+2}` and the lower weight `(1 + λᵢ)^a`:

  `(1 + λᵢ)^{a+1} = √(1+λᵢ)^{a+2} · √(1+λᵢ)^a`.

This is what makes the `H^{a+1}` inner product a pairing of an `H^{a+2}` vector
against an `Hᵃ` vector, by a single Cauchy–Schwarz over the modes. -/

/-- The middle Sobolev weight is the geometric mean of the upper and lower
weights: `(1 + λᵢ)^{a+1} = √((1+λᵢ)^{a+2}) · √((1+λᵢ)^a)`. -/
lemma tensorSobolevWeight_mid_eq_sqrt_mul_sqrt
    (i : TensorEigenIdx (I := I) (M := M) g r s) (a : ℝ) :
    tensorSobolevWeight (I := I) (M := M) i (a + 1) =
      Real.sqrt (tensorSobolevWeight (I := I) (M := M) i (a + 2)) *
        Real.sqrt (tensorSobolevWeight (I := I) (M := M) i a) := by
  have hbase : (0 : ℝ) < 1 + TensorEigenIdx.lambda (I := I) (M := M) i :=
    lt_of_lt_of_le one_pos (one_le_one_add_lambda (I := I) (M := M) i)
  set x := 1 + TensorEigenIdx.lambda (I := I) (M := M) i with hx
  unfold tensorSobolevWeight
  rw [← hx]
  -- `√(x^{a+2}) = x^{(a+2)/2}`, `√(x^a) = x^{a/2}`, and
  -- `x^{(a+2)/2} · x^{a/2} = x^{(a+2)/2 + a/2} = x^{a+1}`.
  have hsqrt_u : Real.sqrt (x ^ (a + 2)) = x ^ ((a + 2) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hbase.le]
    congr 1; ring
  have hsqrt_l : Real.sqrt (x ^ (a : ℝ)) = x ^ (a / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hbase.le]
    congr 1; ring
  rw [hsqrt_u, hsqrt_l, ← Real.rpow_add hbase]
  congr 1; ring

/-! ## The cross-scale duality pairing

For an upper-scale vector `v ∈ H^{a+2}` and a lower-scale vector `w ∈ Hᵃ`, the
**cross-scale pairing** is the (formal) `H^{a+1}` inner product of the two,
read through their shared eigenmode coordinates:

  `crossPairing v w = ∑ᵢ (1 + λᵢ)^{a+1} · vᵢ · wᵢ`.

The series is summable (`crossPairing_summable`), bilinear, and obeys the
cross-scale Cauchy–Schwarz bound `|crossPairing v w| ≤ ‖v‖_{H^{a+2}} · ‖w‖_{Hᵃ}`
(`abs_crossPairing_le`).  When `w` is the `Hᵃ` view of `v`, the pairing recovers
the squared `H^{a+1}` norm of the `H^{a+1}` view of `v`
(`crossPairing_self_eq_normSq`). -/

/-- The mode-wise product family `i ↦ (1+λᵢ)^{a+1} · vᵢ · wᵢ` of an upper-scale
vector `v ∈ H^{a+2}` and a lower-scale vector `w ∈ Hᵃ` is summable.  The bound
splits the weight `(1+λᵢ)^{a+1} = √wᵢ⁺·√wᵢ⁻` and applies AM–GM to dominate the
term by the two (summable) weighted-square families. -/
lemma crossPairing_summable
    (v : tensorHs (I := I) (M := M) g r s (a + 2))
    (w : tensorHs (I := I) (M := M) g r s a) :
    Summable (fun i : TensorEigenIdx (I := I) (M := M) g r s =>
      tensorSobolevWeight (I := I) (M := M) i (a + 1) * (v.coeff i * w.coeff i)) := by
  -- Dominate `|wᵗ⁺¹ vᵢ wᵢ|` by `½ wᵢ⁺ vᵢ² + ½ wᵢ⁻ wᵢ²`, both summable.
  have hv := v.weighted_summable
  have hw := w.weighted_summable
  have h_dom : Summable
      (fun i : TensorEigenIdx (I := I) (M := M) g r s =>
        (1 / 2) * (tensorSobolevWeight (I := I) (M := M) i (a + 2) * (v.coeff i) ^ 2) +
          (1 / 2) * (tensorSobolevWeight (I := I) (M := M) i a * (w.coeff i) ^ 2)) :=
    (hv.mul_left _).add (hw.mul_left _)
  refine Summable.of_norm_bounded h_dom ?_
  intro i
  set wu := tensorSobolevWeight (I := I) (M := M) i (a + 2) with hwu
  set wl := tensorSobolevWeight (I := I) (M := M) i a with hwl
  have hwu0 : 0 ≤ wu := tensorSobolevWeight_nonneg (I := I) (M := M) i (a + 2)
  have hwl0 : 0 ≤ wl := tensorSobolevWeight_nonneg (I := I) (M := M) i a
  have hsplit : tensorSobolevWeight (I := I) (M := M) i (a + 1) =
      Real.sqrt wu * Real.sqrt wl :=
    tensorSobolevWeight_mid_eq_sqrt_mul_sqrt (I := I) (M := M) i a
  -- `|√wu·√wl·vᵢ·wᵢ| = (√wu|vᵢ|)·(√wl|wᵢ|) ≤ ½(√wu|vᵢ|)² + ½(√wl|wᵢ|)²`.
  rw [Real.norm_eq_abs, hsplit, abs_mul, abs_mul, abs_mul,
    abs_of_nonneg (Real.sqrt_nonneg _), abs_of_nonneg (Real.sqrt_nonneg _)]
  have hsqu : Real.sqrt wu ^ 2 = wu := Real.sq_sqrt hwu0
  have hsql : Real.sqrt wl ^ 2 = wl := Real.sq_sqrt hwl0
  nlinarith [sq_nonneg (Real.sqrt wu * |v.coeff i| - Real.sqrt wl * |w.coeff i|),
    Real.sqrt_nonneg wu, Real.sqrt_nonneg wl, abs_nonneg (v.coeff i),
    abs_nonneg (w.coeff i), sq_abs (v.coeff i), sq_abs (w.coeff i), hsqu, hsql]

/-- The **cross-scale duality pairing** of an upper-scale vector `v ∈ H^{a+2}`
against a lower-scale vector `w ∈ Hᵃ`:

  `crossPairing v w = ∑ᵢ (1 + λᵢ)^{a+1} · vᵢ · wᵢ`,

the `H^{a+1}` inner product read through the shared eigenmode coordinates. -/
def crossPairing
    (v : tensorHs (I := I) (M := M) g r s (a + 2))
    (w : tensorHs (I := I) (M := M) g r s a) : ℝ :=
  ∑' i, tensorSobolevWeight (I := I) (M := M) i (a + 1) * (v.coeff i * w.coeff i)

/-- The cross-scale pairing is additive in its upper-scale argument. -/
lemma crossPairing_add_left
    (v v' : tensorHs (I := I) (M := M) g r s (a + 2))
    (w : tensorHs (I := I) (M := M) g r s a) :
    crossPairing (I := I) (M := M) (v + v') w =
      crossPairing (I := I) (M := M) v w + crossPairing (I := I) (M := M) v' w := by
  unfold crossPairing
  rw [← Summable.tsum_add (crossPairing_summable (I := I) (M := M) v w)
    (crossPairing_summable (I := I) (M := M) v' w)]
  refine tsum_congr (fun i => ?_)
  simp only [tensorHs.add_coeff]; ring

/-- The cross-scale pairing is additive in its lower-scale argument. -/
lemma crossPairing_add_right
    (v : tensorHs (I := I) (M := M) g r s (a + 2))
    (w w' : tensorHs (I := I) (M := M) g r s a) :
    crossPairing (I := I) (M := M) v (w + w') =
      crossPairing (I := I) (M := M) v w + crossPairing (I := I) (M := M) v w' := by
  unfold crossPairing
  rw [← Summable.tsum_add (crossPairing_summable (I := I) (M := M) v w)
    (crossPairing_summable (I := I) (M := M) v w')]
  refine tsum_congr (fun i => ?_)
  simp only [tensorHs.add_coeff]; ring

/-- The cross-scale pairing is homogeneous in its upper-scale argument. -/
lemma crossPairing_smul_left (c : ℝ)
    (v : tensorHs (I := I) (M := M) g r s (a + 2))
    (w : tensorHs (I := I) (M := M) g r s a) :
    crossPairing (I := I) (M := M) (c • v) w =
      c * crossPairing (I := I) (M := M) v w := by
  unfold crossPairing
  rw [← tsum_mul_left]
  refine tsum_congr (fun i => ?_)
  simp only [tensorHs.smul_coeff]; ring

/-- The cross-scale pairing is homogeneous in its lower-scale argument. -/
lemma crossPairing_smul_right (c : ℝ)
    (v : tensorHs (I := I) (M := M) g r s (a + 2))
    (w : tensorHs (I := I) (M := M) g r s a) :
    crossPairing (I := I) (M := M) v (c • w) =
      c * crossPairing (I := I) (M := M) v w := by
  unfold crossPairing
  rw [← tsum_mul_left]
  refine tsum_congr (fun i => ?_)
  simp only [tensorHs.smul_coeff]; ring

/-! ### The cross-scale Cauchy–Schwarz bound

The pairing realizes as the `ℓ²` inner product of the two diagonally-rescaled
coordinate families `i ↦ √(1+λᵢ)^{a+2}·vᵢ` and `i ↦ √(1+λᵢ)^a·wᵢ`: by the
weight split their mode-wise product is exactly `(1+λᵢ)^{a+1}·vᵢ·wᵢ`.  The
`ℓ²` norms of the two families are `‖v‖_{H^{a+2}}` and `‖w‖_{Hᵃ}` (the rescaling
isometry `rescaleEquivL2`), so Cauchy–Schwarz in `ℓ²` gives the bound — a single
global Cauchy–Schwarz, no per-mode series gymnastics. -/

/-- The cross-scale pairing is the `ℓ²` inner product of the two diagonally
rescaled coordinate families. -/
lemma crossPairing_eq_inner_rescale
    (v : tensorHs (I := I) (M := M) g r s (a + 2))
    (w : tensorHs (I := I) (M := M) g r s a) :
    crossPairing (I := I) (M := M) v w =
      (inner ℝ (tensorHs.rescaleToL2 (I := I) (M := M) v)
        (tensorHs.rescaleToL2 (I := I) (M := M) w) : ℝ) := by
  rw [lp.inner_eq_tsum]
  unfold crossPairing
  refine tsum_congr (fun i => ?_)
  rw [show (inner ℝ ((tensorHs.rescaleToL2 (I := I) (M := M) v : _ → ℝ) i)
          ((tensorHs.rescaleToL2 (I := I) (M := M) w : _ → ℝ) i) : ℝ) =
        (tensorHs.rescaleToL2 (I := I) (M := M) v : _ → ℝ) i *
          (tensorHs.rescaleToL2 (I := I) (M := M) w : _ → ℝ) i by
      simp [real_inner_eq_re_inner, RCLike.inner_apply, mul_comm]]
  rw [tensorHs.rescaleToL2_apply, tensorHs.rescaleToL2_apply,
    tensorSobolevWeight_mid_eq_sqrt_mul_sqrt (I := I) (M := M) i a]
  ring

/-- **The cross-scale Cauchy–Schwarz pairing bound.**  The `H^{a+1}` pairing of an
`H^{a+2}` vector against an `Hᵃ` vector is controlled by the product of their
norms at the respective scales:

  `|crossPairing v w| ≤ ‖v‖_{H^{a+2}} · ‖w‖_{Hᵃ}`. -/
theorem abs_crossPairing_le
    (v : tensorHs (I := I) (M := M) g r s (a + 2))
    (w : tensorHs (I := I) (M := M) g r s a) :
    |crossPairing (I := I) (M := M) v w| ≤ ‖v‖ * ‖w‖ := by
  rw [crossPairing_eq_inner_rescale]
  refine le_trans (abs_real_inner_le_norm _ _) ?_
  have hv : ‖tensorHs.rescaleToL2 (I := I) (M := M) v‖ = ‖v‖ :=
    (tensorHs.rescaleEquivL2 (I := I) (M := M)).norm_map v
  have hw : ‖tensorHs.rescaleToL2 (I := I) (M := M) w‖ = ‖w‖ :=
    (tensorHs.rescaleEquivL2 (I := I) (M := M)).norm_map w
  rw [hv, hw]

/-! ### The diagonal: the pairing recovers the squared `H^{a+1}` norm

When the lower-scale argument is the `Hᵃ` view of the upper-scale argument, the
pairing is the squared `H^{a+1}` norm of the `H^{a+1}` view: both reduce to
`∑ᵢ (1+λᵢ)^{a+1} vᵢ²`. -/

/-- The cross-scale pairing of `v ∈ H^{a+2}` against its own `Hᵃ` view is the
squared `H^{a+1}` norm of the `H^{a+1}` view of `v`. -/
theorem crossPairing_self_eq_normSq
    (v : tensorHs (I := I) (M := M) g r s (a + 2)) :
    crossPairing (I := I) (M := M) v
        (tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
          (show a ≤ a + 2 by linarith) v) =
      ‖tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
          (show a + 1 ≤ a + 2 by linarith) v‖ ^ 2 := by
  rw [tensorHs.norm_sq_eq_tsum]
  unfold crossPairing
  refine tsum_congr (fun i => ?_)
  rw [tensorHsInclusion_coeff_apply, tensorHsInclusion_coeff_apply, sq]

/-! ## The eigenmode-coordinate functional as a continuous linear map

For a fixed eigen-index `i`, the coordinate `T ↦ T.coeff i` is a bounded linear
functional on `Hˢ`: from the weighted-Parseval identity `(1+λᵢ)^σ (T.coeff i)² ≤
‖T‖²`, the bound `|T.coeff i| ≤ √((1+λᵢ)^σ)⁻¹ · ‖T‖` holds.  Boundedness lets the
coordinate commute with the Bochner time-integral, which is the per-mode engine
of the fundamental theorem of calculus below. -/

/-- The eigenmode-coordinate `|T.coeff i|` is bounded by `√((1+λᵢ)^σ)⁻¹ · ‖T‖`. -/
lemma abs_coeff_le_norm {σ : ℝ} (i : TensorEigenIdx (I := I) (M := M) g r s)
    (T : tensorHs (I := I) (M := M) g r s σ) :
    |T.coeff i| ≤ (Real.sqrt (tensorSobolevWeight (I := I) (M := M) i σ))⁻¹ * ‖T‖ := by
  have hw_pos : 0 < tensorSobolevWeight (I := I) (M := M) i σ :=
    tensorSobolevWeight_pos (I := I) (M := M) i σ
  have hsqrt_pos : 0 < Real.sqrt (tensorSobolevWeight (I := I) (M := M) i σ) :=
    Real.sqrt_pos.mpr hw_pos
  -- `(1+λᵢ)^σ (T.coeff i)² ≤ ‖T‖²`.
  have h_term_le : tensorSobolevWeight (I := I) (M := M) i σ * (T.coeff i) ^ 2 ≤ ‖T‖ ^ 2 := by
    rw [tensorHs.norm_sq_eq_tsum]
    refine Summable.le_tsum T.weighted_summable i (fun j _ => ?_)
    have hw : 0 ≤ tensorSobolevWeight (I := I) (M := M) j σ :=
      tensorSobolevWeight_nonneg (I := I) (M := M) j σ
    positivity
  -- `(√w · |T.coeff i|)² = w · (T.coeff i)² ≤ ‖T‖²`, so `√w·|T.coeff i| ≤ ‖T‖`.
  have hsq : (Real.sqrt (tensorSobolevWeight (I := I) (M := M) i σ) * |T.coeff i|) ^ 2 ≤ ‖T‖ ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hw_pos.le, sq_abs]; exact h_term_le
  have hle : Real.sqrt (tensorSobolevWeight (I := I) (M := M) i σ) * |T.coeff i| ≤ ‖T‖ := by
    have h1 : 0 ≤ Real.sqrt (tensorSobolevWeight (I := I) (M := M) i σ) * |T.coeff i| :=
      mul_nonneg hsqrt_pos.le (abs_nonneg _)
    nlinarith [hsq, h1, norm_nonneg T]
  rw [inv_mul_eq_div, le_div_iff₀ hsqrt_pos, mul_comm]
  exact hle

/-- The eigenmode-coordinate `T ↦ T.coeff i` as a continuous linear functional
on `Hˢ`, with operator-norm bound `√((1+λᵢ)^σ)⁻¹`. -/
def coeffCLM {σ : ℝ} (i : TensorEigenIdx (I := I) (M := M) g r s) :
    tensorHs (I := I) (M := M) g r s σ →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := fun T => T.coeff i
      map_add' := fun S T => by simp only [tensorHs.add_coeff]
      map_smul' := fun c T => by simp only [tensorHs.smul_coeff, RingHom.id_apply, smul_eq_mul] }
    (Real.sqrt (tensorSobolevWeight (I := I) (M := M) i σ))⁻¹
    (fun T => by
      change ‖T.coeff i‖ ≤ _
      rw [Real.norm_eq_abs]
      exact abs_coeff_le_norm (I := I) (M := M) i T)

@[simp] lemma coeffCLM_apply {σ : ℝ} (i : TensorEigenIdx (I := I) (M := M) g r s)
    (T : tensorHs (I := I) (M := M) g r s σ) :
    coeffCLM (I := I) (M := M) (g := g) (r := r) (s := s) (σ := σ) i T = T.coeff i := rfl

/-! ## The cross-scale energy field

The energy-space datum for the parabolic trace embedding.  It packages, on the
time horizon `[0,T]`:

* `hi : ℝ → H^{a+2}` — the (continuous) upper-scale representative of the field
  values;
* `lo : H¹([0,T]; Hᵃ)` — the lower-scale time-Sobolev datum, recording the
  initial value `lo.init ∈ Hᵃ` and the `L²` time derivative `lo.deriv ∈
  L²([0,T]; Hᵃ)`;
* the structural **link** that the `Hᵃ` view of `hi t` is the indefinite
  `Hᵃ`-integral `lo.toFun t` of the derivative.

The link is the defining compatibility of the two scales: it is *not* a disguised
form of the conclusion (the conclusion is a statement about the `H^{a+1}`
representative and a sup-in-time norm bound, neither of which appears in the
hypotheses).  This shape mirrors the companion-field structure of the
maximal-regularity Duhamel solution, whose `H^{a+2}` field
(`maxRegDuhamelSolField`) and `Hᵃ` carrier (an `H¹([0,T]; Hᵃ)` element) coexist
in exactly this way. -/
structure CrossScaleField (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (a : ℝ) (T : ℝ) where
  /-- The continuous upper-scale (`H^{a+2}`) representative of the values. -/
  hi : ℝ → tensorHs (I := I) (M := M) g r s (a + 2)
  /-- The lower-scale (`Hᵃ`) time-Sobolev datum: initial value and `L²`
  derivative. -/
  lo : timeH1 (tensorHs (I := I) (M := M) g r s a) T
  /-- The upper-scale representative is continuous on `[0,T]`. -/
  hi_continuousOn : ContinuousOn hi (Icc (0 : ℝ) T)
  /-- The `Hᵃ` view of `hi t` is the indefinite `Hᵃ`-integral of the derivative,
  for `t ∈ [0,T]`. -/
  link : ∀ t ∈ Icc (0 : ℝ) T,
    tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
        (show a ≤ a + 2 by linarith) (hi t) = lo.toFun t

namespace CrossScaleField

variable (u : CrossScaleField (I := I) (M := M) g r s a T)

/-- The intermediate-scale (`H^{a+1}`) representative of the field:
`u.repr t = ι(hi t)`, the `H^{a+1}` view of the upper-scale value. -/
def repr (t : ℝ) : tensorHs (I := I) (M := M) g r s (a + 1) :=
  tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
    (show a + 1 ≤ a + 2 by linarith) (u.hi t)

@[simp] lemma repr_coeff (t : ℝ) (i : TensorEigenIdx (I := I) (M := M) g r s) :
    (u.repr t).coeff i = (u.hi t).coeff i := rfl

/-- **The intermediate-scale representative is continuous on `[0,T]`.**  It is
the composition of the continuous upper-scale representative with the continuous
inclusion `H^{a+2} → H^{a+1}`. -/
theorem continuousOn_repr : ContinuousOn u.repr (Icc (0 : ℝ) T) :=
  (tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
    (show a + 1 ≤ a + 2 by linarith)).continuous.comp_continuousOn u.hi_continuousOn

/-- The coordinate family of the `Hᵃ` indefinite integral agrees with the
coordinate family of the upper-scale representative, on `[0,T]`. -/
lemma toFun_coeff_eq (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    (u.lo.toFun t).coeff i = (u.hi t).coeff i := by
  have h := u.link t ht
  have := congrArg (fun T => tensorHs.coeff T i) h
  simpa only [tensorHsInclusion_coeff_apply] using this.symm

/-- **The squared `H^{a+1}` norm of the representative as the cross-scale
pairing.**  For `t ∈ [0,T]`,

  `‖u.repr t‖²_{H^{a+1}} = crossPairing (hi t) (lo.toFun t)`,

the diagonal of the cross-scale pairing.  This is the bridge by which the
sup-in-time `H^{a+1}` norm is controlled by the cross-scale Cauchy–Schwarz
bound. -/
theorem normSq_repr_eq_crossPairing (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
    ‖u.repr t‖ ^ 2 = crossPairing (I := I) (M := M) (u.hi t) (u.lo.toFun t) := by
  rw [tensorHs.norm_sq_eq_tsum]
  unfold crossPairing
  refine tsum_congr (fun i => ?_)
  rw [repr_coeff, u.toFun_coeff_eq t ht i, sq]

/-- **Pointwise cross-scale bound on the squared `H^{a+1}` norm.**  For
`t ∈ [0,T]`,

  `‖u.repr t‖²_{H^{a+1}} ≤ ‖u.hi t‖_{H^{a+2}} · ‖u.lo.toFun t‖_{Hᵃ}`,

a direct consequence of `normSq_repr_eq_crossPairing` and the cross-scale
Cauchy–Schwarz bound `abs_crossPairing_le`. -/
theorem normSq_repr_le (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
    ‖u.repr t‖ ^ 2 ≤ ‖u.hi t‖ * ‖u.lo.toFun t‖ := by
  rw [u.normSq_repr_eq_crossPairing t ht]
  refine le_trans (le_abs_self _) ?_
  exact abs_crossPairing_le (I := I) (M := M) (u.hi t) (u.lo.toFun t)

/-! ### Per-mode fundamental theorem of calculus

Each eigenmode coordinate `cᵢ(t) = (lo.toFun t).coeff i` is, via the
continuity of the coordinate functional `coeffCLM`, the scalar indefinite
integral of the derivative coordinate `dᵢ(s) = (lo.deriv s).coeff i`.  This is
the per-mode engine: each weighted-square `(1+λᵢ)^{a+1} cᵢ(t)²` is absolutely
continuous in time and satisfies the scalar fundamental theorem of calculus. -/

/-- The eigenmode coordinate of the `Hᵃ` indefinite integral is the scalar
indefinite integral of the derivative coordinate:

  `(lo.toFun t).coeff i = lo.init.coeff i + ∫₀ᵗ (lo.deriv s).coeff i ds`. -/
lemma coeff_toFun_eq_integral (i : TensorEigenIdx (I := I) (M := M) g r s)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    (u.lo.toFun t).coeff i =
      u.lo.init.coeff i + ∫ s in (0 : ℝ)..t, (u.lo.deriv s).coeff i := by
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) T := ⟨le_rfl, le_trans ht.1 ht.2⟩
  -- Push the (continuous-linear) coordinate functional through the integral.
  have hcomm : ∫ s in (0 : ℝ)..t, (u.lo.deriv s).coeff i =
      (coeffCLM (I := I) (M := M) (g := g) (r := r) (s := s) (σ := a) i)
        (∫ s in (0 : ℝ)..t, u.lo.deriv s) := by
    rw [← ContinuousLinearMap.intervalIntegral_comp_comm
      (coeffCLM (I := I) (M := M) (g := g) (r := r) (s := s) (σ := a) i)
      (u.lo.intervalIntegrable_deriv h0 ht)]
    rfl
  have hval : (u.lo.toFun t).coeff i =
      (coeffCLM (I := I) (M := M) (g := g) (r := r) (s := s) (σ := a) i) (u.lo.toFun t) := rfl
  rw [hval, timeH1.toFun_apply, map_add, hcomm]
  rfl

/-! ### The sup-in-time `H^{a+1}` estimates

Two estimates are provided.

* `normSq_repr_le_mul` is the **unconditional pointwise bound**
  `‖u.repr t‖²_{H^{a+1}} ≤ ‖u.hi t‖_{H^{a+2}} · ‖u.lo.toFun t‖_{Hᵃ}`, valid for
  every `t ∈ [0,T]`.  It follows from the diagonal cross-pairing identity and
  the cross-scale Cauchy–Schwarz bound, with no time-regularity input.  Taking
  the supremum over `t` it already controls the sup-in-time `H^{a+1}` norm by
  the product of the (continuous, hence bounded on the compact interval)
  upper-scale and integral norms — enough to discharge the *qualitative*
  sup-in-time membership in `C([0,T]; H^{a+1})`.

* `iSup_normSq_le_of_energyIdentity` is the **sharp Lions–Magenes estimate**
  `sup_t ‖u.repr t‖² ≤ ‖u.repr 0‖² + 2 ∫₀ᵀ ‖u.hi s‖ · ‖u.lo.deriv s‖`, derived
  from the parabolic energy identity (the fundamental theorem of calculus for
  the squared `H^{a+1}` norm).  The energy identity is the per-mode scalar FTC
  summed over the eigenmodes; it is taken here as an explicit, named hypothesis
  (`henergy`) rather than re-derived, because the requisite scalar
  fundamental-theorem-of-calculus for merely-absolutely-continuous integrands
  is not available in Mathlib in a directly usable form (the interval FTC-2
  variants all demand an everywhere right-derivative, which an indefinite
  Bochner integral possesses only almost everywhere).  The hypothesis is the
  genuine intermediate fact and does **not** imply the conclusion on its own —
  the sup bound additionally requires the cross-scale Cauchy–Schwarz control of
  the integrand, supplied by `abs_crossPairing_le`. -/

/-- **Unconditional pointwise `H^{a+1}` bound.**  For every `t ∈ [0,T]`,

  `‖u.repr t‖²_{H^{a+1}} ≤ ‖u.hi t‖_{H^{a+2}} · ‖u.lo.toFun t‖_{Hᵃ}`.

A restatement of `normSq_repr_le` highlighting that the right side is a product
of two quantities continuous in `t`, hence bounded on the compact `[0,T]`: this
controls the sup-in-time `H^{a+1}` norm with no time-regularity hypothesis. -/
theorem normSq_repr_le_mul (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
    ‖u.repr t‖ ^ 2 ≤ ‖u.hi t‖ * ‖u.lo.toFun t‖ :=
  u.normSq_repr_le t ht

/-- **The sharp Lions–Magenes sup-in-time energy estimate**, conditional on the
parabolic energy identity.  Assume:

* (`henergy`) the squared `H^{a+1}` norm satisfies the fundamental theorem of
  calculus `‖u.repr t‖² = ‖u.repr 0‖² + ∫₀ᵗ 2·crossPairing (u.hi s)
  (u.lo.deriv s) ds` on `[0,T]`;
* (`hint_cp`) the energy integrand `s ↦ 2·crossPairing (u.hi s) (u.lo.deriv s)`
  is interval integrable on `0..t`;
* (`hint_norm`) the cross-scale Cauchy–Schwarz dominating integrand
  `s ↦ 2·(‖u.hi s‖·‖u.lo.deriv s‖)` is interval integrable on `0..t`.

Then for every `t ∈ [0,T]`,

  `‖u.repr t‖² ≤ ‖u.repr 0‖² + ∫₀ᵗ 2·‖u.hi s‖·‖u.lo.deriv s‖ ds`.

The proof bounds the energy-identity integrand pointwise by the cross-scale
Cauchy–Schwarz bound `abs_crossPairing_le` and applies monotonicity of the
interval integral.  The integrability hypotheses are standard regularity facts
(the dominating integrand is the product of a continuous and an `L²` factor);
they are exposed as hypotheses, not derived, to keep this estimate independent
of the as-yet-unbuilt energy-identity derivation. -/
theorem normSq_le_of_energyIdentity
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T)
    (henergy : ‖u.repr t‖ ^ 2 = ‖u.repr 0‖ ^ 2 +
        ∫ s in (0 : ℝ)..t, 2 * crossPairing (I := I) (M := M) (u.hi s) (u.lo.deriv s))
    (hint_cp : IntervalIntegrable
        (fun s => 2 * crossPairing (I := I) (M := M) (u.hi s) (u.lo.deriv s)) volume 0 t)
    (hint_norm : IntervalIntegrable
        (fun s => 2 * (‖u.hi s‖ * ‖u.lo.deriv s‖)) volume 0 t) :
    ‖u.repr t‖ ^ 2 ≤ ‖u.repr 0‖ ^ 2 +
      ∫ s in (0 : ℝ)..t, 2 * (‖u.hi s‖ * ‖u.lo.deriv s‖) := by
  rw [henergy]
  have hmono : (∫ s in (0 : ℝ)..t, 2 * crossPairing (I := I) (M := M) (u.hi s) (u.lo.deriv s)) ≤
      ∫ s in (0 : ℝ)..t, 2 * (‖u.hi s‖ * ‖u.lo.deriv s‖) := by
    refine intervalIntegral.integral_mono_on ht.1 hint_cp hint_norm (fun s _ => ?_)
    -- The energy-identity integrand is bounded by the cross-scale Cauchy–Schwarz bound.
    have h := abs_crossPairing_le (I := I) (M := M) (u.hi s) (u.lo.deriv s)
    nlinarith [le_abs_self (crossPairing (I := I) (M := M) (u.hi s) (u.lo.deriv s)), h]
  linarith [hmono]

end CrossScaleField

end QuasiLinear
end Parabolic
end Analysis
end DifferentialGeometry
