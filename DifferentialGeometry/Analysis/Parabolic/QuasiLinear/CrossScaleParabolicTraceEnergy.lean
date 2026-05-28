import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.CrossScaleParabolicTrace
import DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.CompactSAResolventIntrinsic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

/-!
# The parabolic energy identity and the unconditional cross-scale trace estimate

This file discharges the parabolic **energy identity** for a `CrossScaleField`
and, composing it with the cross-scale Cauchy–Schwarz bound already established,
turns the conditional Lions–Magenes sup estimate into an **unconditional** sharp
sup-in-time bound on the intermediate-scale representative.

## The two genuine sub-lemmas

1. **Scalar absolutely-continuous fundamental theorem of calculus, squared**
   (`sq_eq_init_add_integral_of_intervalIntegrable`).  For an indefinite
   integral `c t = c₀ + ∫₀ᵗ d s` of an interval-integrable `d`, the square
   satisfies `c t ² = c₀ ² + ∫₀ᵗ 2 · c s · d s ds`.  Mathlib has no packaged
   FTC-2 for merely-a.e.-differentiable integrands, but it *does* have the
   fundamental theorem of calculus and the product (integration-by-parts) rule
   for **absolutely continuous** functions
   (`AbsolutelyContinuousOnInterval.integral_deriv_mul_eq_sub`).  Since `c` is an
   indefinite integral it is absolutely continuous
   (`IntervalIntegrable.absolutelyContinuousOnInterval_intervalIntegral`); the
   product rule applied to `f = g = c` gives the squared identity, after
   replacing the (a.e.-existing) derivative `deriv c` by `d` via the Lebesgue
   differentiation theorem.

2. **Mode-sum / time-integral interchange**
   (`tsum_intervalIntegral_energyIntegrand_eq`).  The squared `H^{a+1}` norm is
   the eigenmode tsum of the per-mode weighted squares, and the energy identity is
   the tsum over modes of the per-mode scalar identity.  The sum over the
   (countable) eigenmodes commutes with the time integral by
   `MeasureTheory.integral_tsum`; the dominating series is summable because the
   cross-scale weight split bounds the integrand pointwise in time by
   `‖u.hi s‖²_{H^{a+2}} + ‖u.lo.deriv s‖²_{Hᵃ}`, both time-integrable.

## Main results

* `CrossScaleField.energyIdentity` — the parabolic energy identity
  `‖u.repr t‖² = ‖u.repr 0‖² + ∫₀ᵗ 2·crossPairing (u.hi s) (u.lo.deriv s) ds`.
* `CrossScaleField.normSq_repr_le_init_add_integral` — the **unconditional** sharp
  Lions–Magenes energy estimate
  `‖u.repr t‖² ≤ ‖u.repr 0‖² + ∫₀ᵗ 2·‖u.hi s‖·‖u.lo.deriv s‖ ds`, valid for every
  `t ∈ [0,T]`; taking the supremum over `t` (the right side is monotone in `t`)
  gives the sup-in-time bound by the full `∫₀ᵀ` integral.
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
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

variable {g : SmoothRiemannianMetric I M} {r s : ℕ}
variable {a : ℝ} {T : ℝ}

/-! ## Sub-lemma 1: the scalar absolutely-continuous FTC for the square

For an indefinite integral `c t = c₀ + ∫₀ᵗ d s` of an interval-integrable
function `d`, the square satisfies the fundamental theorem of calculus
`c t² = c₀² + ∫₀ᵗ 2·c s·d s ds`. -/

/-- **Scalar absolutely-continuous FTC-2 for the square.**  Let `d : ℝ → ℝ` be
interval integrable on `0..t` (with `0 ≤ t`), let `c₀ : ℝ`, and set
`c τ = c₀ + ∫ s in 0..τ, d s`.  Then

  `c t ^ 2 = c 0 ^ 2 + ∫ s in 0..t, 2 * c s * d s`.

The proof builds the absolute continuity of `c` (an affine shift of an
indefinite integral), applies the product rule
`AbsolutelyContinuousOnInterval.integral_deriv_mul_eq_sub` with `f = g = c`, and
replaces the a.e.-existing derivative `deriv c` by `d` using the Lebesgue
differentiation theorem `IntervalIntegrable.ae_hasDerivAt_integral`. -/
theorem sq_eq_init_add_integral_of_intervalIntegrable
    {d : ℝ → ℝ} {t c₀ : ℝ} (ht : 0 ≤ t)
    (hd : IntervalIntegrable d volume 0 t) :
    (c₀ + ∫ s in (0 : ℝ)..t, d s) ^ 2 =
      (c₀ + ∫ s in (0 : ℝ)..(0 : ℝ), d s) ^ 2 +
        ∫ s in (0 : ℝ)..t, 2 * (c₀ + ∫ r in (0 : ℝ)..s, d r) * d s := by
  -- The indefinite integral with the initial shift.
  let c : ℝ → ℝ := fun τ => c₀ + ∫ s in (0 : ℝ)..τ, d s
  have hcval : ∀ τ, c τ = c₀ + ∫ s in (0 : ℝ)..τ, d s := fun _ => rfl
  -- `c` is absolutely continuous on `[0,t]`: a constant plus an indefinite integral.
  have h0mem : (0 : ℝ) ∈ uIcc (0 : ℝ) t := by
    rw [uIcc_of_le ht]; exact ⟨le_rfl, ht⟩
  have hac_int : AbsolutelyContinuousOnInterval
      (fun τ => ∫ s in (0 : ℝ)..τ, d s) 0 t :=
    hd.absolutelyContinuousOnInterval_intervalIntegral h0mem
  have hac_const : AbsolutelyContinuousOnInterval (fun _ : ℝ => c₀) 0 t :=
    (LipschitzWith.const c₀).lipschitzOnWith.absolutelyContinuousOnInterval
  have hac_c : AbsolutelyContinuousOnInterval c 0 t := by
    have := hac_const.add hac_int
    simpa only [c, Pi.add_apply] using this
  -- The product rule for absolutely continuous functions, with `f = g = c`.
  have hprod := AbsolutelyContinuousOnInterval.integral_deriv_mul_eq_sub hac_c hac_c
  -- The a.e. derivative of `c` on `0..t` is `d`.
  have hae_deriv : ∀ᵐ x, x ∈ uIcc (0 : ℝ) t → deriv c x = d x := by
    filter_upwards [hd.ae_hasDerivAt_integral] with x hx hxmem
    have hxd : HasDerivAt (fun τ => ∫ s in (0 : ℝ)..τ, d s) (d x) x :=
      hx hxmem 0 h0mem
    have hc : HasDerivAt c (d x) x := by
      have := (hasDerivAt_const x c₀).add hxd
      simpa only [c, zero_add] using this
    exact hc.deriv
  -- Rewrite the product-rule integrand `deriv c · c + c · deriv c` as `2 · c · d`.
  have hcongr : (∫ x in (0 : ℝ)..t, deriv c x * c x + c x * deriv c x) =
      ∫ x in (0 : ℝ)..t, 2 * c x * d x := by
    refine intervalIntegral.integral_congr_ae ?_
    have hmono : uIoc (0 : ℝ) t ⊆ uIcc (0 : ℝ) t := uIoc_subset_uIcc
    have hae' : ∀ᵐ x ∂(volume.restrict (uIoc (0 : ℝ) t)),
        x ∈ uIcc (0 : ℝ) t → deriv c x = d x :=
      ae_restrict_of_ae hae_deriv
    rw [ae_restrict_iff' measurableSet_uIoc] at hae'
    filter_upwards [hae'] with x hx hxmem
    have hxd : deriv c x = d x := hx hxmem (uIoc_subset_uIcc hxmem)
    rw [hxd]; ring
  -- Assemble: `c t² - c 0² = ∫ 2·c·d`.  `hprod : ∫ 2·c·d = c t · c t - c 0 · c 0`.
  rw [hcongr] at hprod
  have hgoal : (c₀ + ∫ s in (0 : ℝ)..t, d s) * (c₀ + ∫ s in (0 : ℝ)..t, d s) -
      (c₀ + ∫ s in (0 : ℝ)..(0 : ℝ), d s) * (c₀ + ∫ s in (0 : ℝ)..(0 : ℝ), d s) =
      ∫ x in (0 : ℝ)..t, 2 * (c₀ + ∫ r in (0 : ℝ)..x, d r) * d x := by
    have heq : (∫ x in (0 : ℝ)..t, 2 * c x * d x) =
        ∫ x in (0 : ℝ)..t, 2 * (c₀ + ∫ r in (0 : ℝ)..x, d r) * d x :=
      intervalIntegral.integral_congr (fun x _ => by rw [hcval x])
    rw [← heq, ← hprod]
  nlinarith [hgoal]

/-! ## Per-mode coordinate functions and their measurability

For a fixed eigen-index `i`, the time-`H^{a+1}` representative's mode coordinate
`s ↦ (u.hi s).coeff i` is continuous on `[0,T]`, and the derivative coordinate
`s ↦ (u.lo.deriv s).coeff i` is the (measurable) composition of the bounded
coordinate functional with the `L²` derivative. -/

namespace CrossScaleField

variable (u : CrossScaleField (I := I) (M := M) g r s a T)

/-- The eigenmode coordinate of the derivative `s ↦ (u.lo.deriv s).coeff i` is
the composition of the continuous coordinate functional `coeffCLM i` with the
`L²` derivative, hence strongly measurable for the restricted Lebesgue measure
on `[0,T]`. -/
lemma aestronglyMeasurable_deriv_coeff
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    AEStronglyMeasurable (fun τ => (u.lo.deriv τ).coeff i)
      (volume.restrict (Set.Icc (0 : ℝ) T)) := by
  have hmeas : AEStronglyMeasurable (fun τ => u.lo.deriv τ) (timeMeasure T) :=
    Lp.aestronglyMeasurable u.lo.deriv
  have hcomp :
      AEStronglyMeasurable
        (fun τ => coeffCLM (I := I) (M := M) (g := g) (r := r) (s := s) (σ := a) i
          (u.lo.deriv τ)) (timeMeasure T) :=
    (coeffCLM (I := I) (M := M) (g := g) (r := r) (s := s) (σ := a)
      i).continuous.comp_aestronglyMeasurable hmeas
  simpa only [coeffCLM_apply] using hcomp

/-- The eigenmode coordinate of the derivative is interval integrable on `0..t`
for `t ∈ [0,T]`: it is the composition of the bounded functional `coeffCLM i`
with the interval-integrable `L²` derivative. -/
lemma intervalIntegrable_deriv_coeff
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    IntervalIntegrable (fun τ => (u.lo.deriv τ).coeff i) volume 0 t := by
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) T := ⟨le_rfl, le_trans ht.1 ht.2⟩
  have hbase : IntervalIntegrable (fun τ => u.lo.deriv τ) volume 0 t :=
    u.lo.intervalIntegrable_deriv h0 ht
  have hcomp : IntervalIntegrable
      (fun τ => coeffCLM (I := I) (M := M) (g := g) (r := r) (s := s) (σ := a)
        i (u.lo.deriv τ)) volume 0 t :=
    intervalIntegrable_iff.mpr
      ((coeffCLM (I := I) (M := M) (g := g) (r := r) (s := s) (σ := a) i).integrable_comp
        (intervalIntegrable_iff.mp hbase))
  simpa only [coeffCLM_apply] using hcomp

/-- The eigenmode coordinate of the indefinite integral coordinate equals the
scalar indefinite integral, in the explicit `(c₀ + ∫) ` shape consumed by the
scalar FTC.  This restates `coeff_toFun_eq_integral` and `toFun_coeff_eq`. -/
lemma hi_coeff_eq_init_add_integral
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    (u.hi t).coeff i =
      u.lo.init.coeff i + ∫ s in (0 : ℝ)..t, (u.lo.deriv s).coeff i := by
  rw [← u.toFun_coeff_eq t ht i, u.coeff_toFun_eq_integral i ht]

/-! ## The per-mode parabolic energy identity

Each weighted-square mode coordinate satisfies the scalar FTC-2 for the square,
scaled by the (constant-in-time) Sobolev weight. -/

/-- **Per-mode energy identity.**  For each eigenmode `i` and `t ∈ [0,T]`,

  `wᵢ^{a+1} · (u.hi t).coeff i ² = wᵢ^{a+1} · (u.hi 0).coeff i ² +
      ∫₀ᵗ 2 wᵢ^{a+1} · (u.hi s).coeff i · (u.lo.deriv s).coeff i ds`.

This is the scalar absolutely-continuous FTC-2
(`sq_eq_init_add_integral_of_intervalIntegrable`) applied to the mode coordinate
`cᵢ`, multiplied through by the time-independent weight `wᵢ^{a+1}`. -/
theorem perMode_energyIdentity
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    tensorSobolevWeight (I := I) (M := M) i (a + 1) * ((u.hi t).coeff i) ^ 2 =
      tensorSobolevWeight (I := I) (M := M) i (a + 1) * ((u.hi 0).coeff i) ^ 2 +
        ∫ s in (0 : ℝ)..t,
          2 * (tensorSobolevWeight (I := I) (M := M) i (a + 1) *
            ((u.hi s).coeff i * (u.lo.deriv s).coeff i)) := by
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) T := ⟨le_rfl, le_trans ht.1 ht.2⟩
  set w := tensorSobolevWeight (I := I) (M := M) i (a + 1) with hw_def
  set c₀ := u.lo.init.coeff i with hc₀
  set d : ℝ → ℝ := fun s => (u.lo.deriv s).coeff i with hd_def
  -- The scalar FTC-2 for the square of the indefinite integral.
  have hscalar := sq_eq_init_add_integral_of_intervalIntegrable (c₀ := c₀) (d := d)
    ht.1 (u.intervalIntegrable_deriv_coeff i ht)
  -- Identify `(u.hi t).coeff i` with the indefinite integral `c₀ + ∫₀ᵗ d`.
  have hcoeff_t : (u.hi t).coeff i = c₀ + ∫ s in (0 : ℝ)..t, d s :=
    u.hi_coeff_eq_init_add_integral i ht
  have hcoeff_0 : (u.hi 0).coeff i = c₀ + ∫ s in (0 : ℝ)..(0 : ℝ), d s :=
    u.hi_coeff_eq_init_add_integral i h0
  rw [hcoeff_t, hcoeff_0]
  -- Multiply the scalar identity by the constant weight `w`.
  rw [hscalar, mul_add]
  congr 1
  -- Pull the constant `w` inside the integral and rearrange the integrand, replacing
  -- the indefinite integral `c₀ + ∫₀ˣ d` by `(u.hi x).coeff i` at each interior `x`.
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr (fun x hx => ?_)
  rw [uIcc_of_le ht.1] at hx
  have hxmem : x ∈ Icc (0 : ℝ) T := ⟨hx.1, le_trans hx.2 ht.2⟩
  have hxcoeff : c₀ + ∫ r in (0 : ℝ)..x, d r = (u.hi x).coeff i :=
    (u.hi_coeff_eq_init_add_integral i hxmem).symm
  rw [hxcoeff]
  ring

/-! ## Sub-lemma 2: the mode-sum / time-integral interchange

The energy integrand `2·crossPairing (u.hi s) (u.lo.deriv s)` is the tsum over
the (countable) eigenmodes of the per-mode integrands.  Summing the per-mode
energy identities and interchanging the time integral with the mode sum yields
the parabolic energy identity. -/

/-- The countability of the eigen-index type, supplied unconditionally by the
intrinsic resolvent-compactness witness. -/
private lemma countable_eigenIdx :
    Countable (TensorEigenIdx (I := I) (M := M) g r s) :=
  DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.countable_tensorEigenIdx_ofCompact
    (I := I) (M := M) (g := g) (r := r) (s := s)
    (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M) g r s)

/-- The per-mode energy integrand, as a function of `(mode, time)`:

  `Fᵢ(s) = 2 wᵢ^{a+1} · (u.hi s).coeff i · (u.lo.deriv s).coeff i`. -/
private def energyIntegrand
    (i : TensorEigenIdx (I := I) (M := M) g r s) (s : ℝ) : ℝ :=
  2 * (tensorSobolevWeight (I := I) (M := M) i (a + 1) *
    ((u.hi s).coeff i * (u.lo.deriv s).coeff i))

/-- The mode-tsum of the per-mode energy integrand is twice the cross-pairing of
the upper-scale value against the derivative. -/
private lemma tsum_energyIntegrand_eq (s : ℝ) :
    ∑' i, u.energyIntegrand i s =
      2 * crossPairing (I := I) (M := M) (u.hi s) (u.lo.deriv s) := by
  unfold energyIntegrand crossPairing
  rw [← tsum_mul_left]

/-- Pointwise-in-time domination of the absolute per-mode energy integrand by the
cross-scale Cauchy–Schwarz split bound: for every `s`,

  `∑'ᵢ |Fᵢ(s)| ≤ ‖u.hi s‖²_{H^{a+2}} + ‖u.lo.deriv s‖²_{Hᵃ}`. -/
private lemma tsum_abs_energyIntegrand_le (s : ℝ) :
    ∑' i, |u.energyIntegrand i s| ≤ ‖u.hi s‖ ^ 2 + ‖u.lo.deriv s‖ ^ 2 := by
  -- Per-mode bound `|Fᵢ(s)| ≤ wᵢ⁺·(u.hi s).coeff i ² + wᵢ⁻·(u.lo.deriv s).coeff i ²`
  -- via the weight split `wᵢ^{a+1} = √wᵢ⁺·√wᵢ⁻` and AM–GM.
  have hterm : ∀ i, |u.energyIntegrand i s| ≤
      tensorSobolevWeight (I := I) (M := M) i (a + 2) * ((u.hi s).coeff i) ^ 2 +
        tensorSobolevWeight (I := I) (M := M) i a * ((u.lo.deriv s).coeff i) ^ 2 := by
    intro i
    unfold energyIntegrand
    set wu := tensorSobolevWeight (I := I) (M := M) i (a + 2) with hwu
    set wl := tensorSobolevWeight (I := I) (M := M) i a with hwl
    have hwu0 : 0 ≤ wu := tensorSobolevWeight_nonneg (I := I) (M := M) i (a + 2)
    have hwl0 : 0 ≤ wl := tensorSobolevWeight_nonneg (I := I) (M := M) i a
    have hsplit : tensorSobolevWeight (I := I) (M := M) i (a + 1) =
        Real.sqrt wu * Real.sqrt wl :=
      tensorSobolevWeight_mid_eq_sqrt_mul_sqrt (I := I) (M := M) i a
    rw [hsplit, abs_mul, abs_mul, abs_mul, abs_mul,
      show |(2 : ℝ)| = 2 from by norm_num,
      abs_of_nonneg (Real.sqrt_nonneg _), abs_of_nonneg (Real.sqrt_nonneg _)]
    have hsqu : Real.sqrt wu ^ 2 = wu := Real.sq_sqrt hwu0
    have hsql : Real.sqrt wl ^ 2 = wl := Real.sq_sqrt hwl0
    nlinarith [sq_nonneg (Real.sqrt wu * |(u.hi s).coeff i| -
        Real.sqrt wl * |(u.lo.deriv s).coeff i|),
      Real.sqrt_nonneg wu, Real.sqrt_nonneg wl, abs_nonneg ((u.hi s).coeff i),
      abs_nonneg ((u.lo.deriv s).coeff i), sq_abs ((u.hi s).coeff i),
      sq_abs ((u.lo.deriv s).coeff i), hsqu, hsql]
  -- The dominating family is summable and its tsum is `‖u.hi s‖² + ‖u.lo.deriv s‖²`.
  have hsumu : Summable (fun i =>
      tensorSobolevWeight (I := I) (M := M) i (a + 2) * ((u.hi s).coeff i) ^ 2) :=
    (u.hi s).weighted_summable
  have hsuml : Summable (fun i =>
      tensorSobolevWeight (I := I) (M := M) i a * ((u.lo.deriv s).coeff i) ^ 2) :=
    (u.lo.deriv s).weighted_summable
  have hsum_dom : Summable (fun i =>
      tensorSobolevWeight (I := I) (M := M) i (a + 2) * ((u.hi s).coeff i) ^ 2 +
        tensorSobolevWeight (I := I) (M := M) i a * ((u.lo.deriv s).coeff i) ^ 2) :=
    hsumu.add hsuml
  have hsummable_abs : Summable (fun i => |u.energyIntegrand i s|) :=
    Summable.of_nonneg_of_le (fun i => abs_nonneg _) hterm hsum_dom
  calc
    ∑' i, |u.energyIntegrand i s|
        ≤ ∑' i, (tensorSobolevWeight (I := I) (M := M) i (a + 2) * ((u.hi s).coeff i) ^ 2 +
            tensorSobolevWeight (I := I) (M := M) i a * ((u.lo.deriv s).coeff i) ^ 2) :=
          hsummable_abs.tsum_le_tsum hterm hsum_dom
    _ = (∑' i, tensorSobolevWeight (I := I) (M := M) i (a + 2) * ((u.hi s).coeff i) ^ 2) +
          ∑' i, tensorSobolevWeight (I := I) (M := M) i a * ((u.lo.deriv s).coeff i) ^ 2 :=
          hsumu.tsum_add hsuml
    _ = ‖u.hi s‖ ^ 2 + ‖u.lo.deriv s‖ ^ 2 := by
          rw [← tensorHs.norm_sq_eq_tsum, ← tensorHs.norm_sq_eq_tsum]

/-! ### Integrability of the dominating bound and the per-mode integrands -/

/-- The upper-scale squared norm `s ↦ ‖u.hi s‖²` is integrable on `[0,T]`:
`u.hi` is continuous on the compact `[0,T]`, hence so is its squared norm. -/
private lemma integrableOn_normSq_hi :
    IntegrableOn (fun s => ‖u.hi s‖ ^ 2) (Set.Icc (0 : ℝ) T) volume := by
  refine ContinuousOn.integrableOn_Icc ?_
  exact (continuous_pow 2).comp_continuousOn (continuous_norm.comp_continuousOn u.hi_continuousOn)

/-- The lower-scale derivative squared norm `s ↦ ‖u.lo.deriv s‖²` is integrable on
`[0,T]`: the `L²` derivative is square-integrable for the time measure. -/
private lemma integrableOn_normSq_deriv :
    IntegrableOn (fun s => ‖u.lo.deriv s‖ ^ 2) (Set.Icc (0 : ℝ) T) volume := by
  have hLp : MemLp (fun s => u.lo.deriv s) 2 (timeMeasure T) := Lp.memLp u.lo.deriv
  have hint := hLp.integrable_norm_rpow (by norm_num) (by norm_num)
  -- `‖·‖ ^ (2 : ℝ≥0∞).toReal = ‖·‖ ^ 2`.
  have hpow : (fun x => ‖u.lo.deriv x‖ ^ (2 : ℝ≥0∞).toReal) =
      (fun x => ‖u.lo.deriv x‖ ^ 2) := by
    funext x
    rw [show ((2 : ℝ≥0∞).toReal) = (2 : ℝ) by norm_num,
      show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [hpow] at hint
  exact hint

/-- The dominating bound `s ↦ ‖u.hi s‖² + ‖u.lo.deriv s‖²` is integrable on `[0,T]`. -/
private lemma integrableOn_bound :
    IntegrableOn (fun s => ‖u.hi s‖ ^ 2 + ‖u.lo.deriv s‖ ^ 2) (Set.Icc (0 : ℝ) T) volume :=
  u.integrableOn_normSq_hi.add u.integrableOn_normSq_deriv

/-- Each per-mode energy integrand `s ↦ Fᵢ s` is integrable on `Ioc 0 t` for
`t ∈ [0,T]`: it is the (constant-scaled) product of the continuous, bounded
factor `s ↦ (u.hi s).coeff i` with the interval-integrable derivative coordinate
`s ↦ (u.lo.deriv s).coeff i`. -/
private lemma integrableOn_energyIntegrand
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    IntegrableOn (u.energyIntegrand i) (Set.Ioc (0 : ℝ) t) volume := by
  -- The continuous, bounded factor `τ ↦ (u.hi τ).coeff i` on `[0,T]`.
  have hcoeff_cont : ContinuousOn (fun τ => (u.hi τ).coeff i) (Set.Icc (0 : ℝ) T) := by
    have hcomp : ContinuousOn
        (fun τ => coeffCLM (I := I) (M := M) (g := g) (r := r) (s := s) (σ := a + 2) i
          (u.hi τ)) (Set.Icc (0 : ℝ) T) :=
      (coeffCLM (I := I) (M := M) (g := g) (r := r) (s := s) (σ := a + 2)
        i).continuous.comp_continuousOn u.hi_continuousOn
    simpa only [coeffCLM_apply] using hcomp
  -- Integrability of `τ ↦ (u.lo.deriv τ).coeff i` on `Ioc 0 t`.
  have hderiv_int : IntegrableOn (fun τ => (u.lo.deriv τ).coeff i)
      (Set.Ioc (0 : ℝ) t) volume := by
    have h := u.intervalIntegrable_deriv_coeff i ht
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le ht.1] at h
    exact h
  -- The product is integrable: bounded continuous factor times integrable factor.
  have hsubIcc : Set.Ioc (0 : ℝ) t ⊆ Set.Icc (0 : ℝ) t :=
    fun x hx => ⟨le_of_lt hx.1, hx.2⟩
  have hcoeff_cont_t : ContinuousOn (fun τ => (u.hi τ).coeff i) (Set.Icc (0 : ℝ) t) :=
    hcoeff_cont.mono (fun x hx => ⟨hx.1, le_trans hx.2 ht.2⟩)
  have hprod : IntegrableOn
      (fun τ => (u.hi τ).coeff i * (u.lo.deriv τ).coeff i) (Set.Ioc (0 : ℝ) t) volume :=
    MeasureTheory.IntegrableOn.continuousOn_mul_of_subset hcoeff_cont_t hderiv_int
      isCompact_Icc measurableSet_Ioc hsubIcc
  -- Scale by the constant `2 wᵢ^{a+1}`.
  have heq : (u.energyIntegrand i) = fun τ =>
      (2 * tensorSobolevWeight (I := I) (M := M) i (a + 1)) *
        ((u.hi τ).coeff i * (u.lo.deriv τ).coeff i) := by
    funext τ; unfold energyIntegrand; ring
  rw [heq]
  exact hprod.const_mul _

/-- The absolute per-mode energy integrand family `i ↦ |Fᵢ(s)|` is summable at
each time `s` (the same AM–GM domination as `tsum_abs_energyIntegrand_le`). -/
private lemma summable_abs_energyIntegrand (s : ℝ) :
    Summable (fun i => |u.energyIntegrand i s|) := by
  have hterm : ∀ i, |u.energyIntegrand i s| ≤
      tensorSobolevWeight (I := I) (M := M) i (a + 2) * ((u.hi s).coeff i) ^ 2 +
        tensorSobolevWeight (I := I) (M := M) i a * ((u.lo.deriv s).coeff i) ^ 2 := by
    intro i
    unfold energyIntegrand
    set wu := tensorSobolevWeight (I := I) (M := M) i (a + 2) with hwu
    set wl := tensorSobolevWeight (I := I) (M := M) i a with hwl
    have hwu0 : 0 ≤ wu := tensorSobolevWeight_nonneg (I := I) (M := M) i (a + 2)
    have hwl0 : 0 ≤ wl := tensorSobolevWeight_nonneg (I := I) (M := M) i a
    have hsplit : tensorSobolevWeight (I := I) (M := M) i (a + 1) =
        Real.sqrt wu * Real.sqrt wl :=
      tensorSobolevWeight_mid_eq_sqrt_mul_sqrt (I := I) (M := M) i a
    rw [hsplit, abs_mul, abs_mul, abs_mul, abs_mul,
      show |(2 : ℝ)| = 2 from by norm_num,
      abs_of_nonneg (Real.sqrt_nonneg _), abs_of_nonneg (Real.sqrt_nonneg _)]
    have hsqu : Real.sqrt wu ^ 2 = wu := Real.sq_sqrt hwu0
    have hsql : Real.sqrt wl ^ 2 = wl := Real.sq_sqrt hwl0
    nlinarith [sq_nonneg (Real.sqrt wu * |(u.hi s).coeff i| -
        Real.sqrt wl * |(u.lo.deriv s).coeff i|),
      Real.sqrt_nonneg wu, Real.sqrt_nonneg wl, abs_nonneg ((u.hi s).coeff i),
      abs_nonneg ((u.lo.deriv s).coeff i), sq_abs ((u.hi s).coeff i),
      sq_abs ((u.lo.deriv s).coeff i), hsqu, hsql]
  exact Summable.of_nonneg_of_le (fun i => abs_nonneg _) hterm
    ((u.hi s).weighted_summable.add (u.lo.deriv s).weighted_summable)

/-! ### The interchange of the mode sum and the time integral -/

/-- **Mode-sum / time-integral interchange.**  For `t ∈ [0,T]`, the sum over the
eigenmodes of the per-mode time integrals equals the time integral of the
mode-sum:

  `∑'ᵢ ∫₀ᵗ Fᵢ s ds = ∫₀ᵗ ∑'ᵢ Fᵢ s ds`.

The eigen-index type is countable (intrinsic resolvent compactness), each `Fᵢ` is
time-integrable on `Ioc 0 t`, and the dominating series `∑'ᵢ ∫ |Fᵢ|` is summable
because `∑'ᵢ |Fᵢ s| ≤ ‖u.hi s‖² + ‖u.lo.deriv s‖²` is time-integrable. -/
theorem tsum_intervalIntegral_energyIntegrand_eq
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    ∑' i, (∫ s in (0 : ℝ)..t, u.energyIntegrand i s) =
      ∫ s in (0 : ℝ)..t, ∑' i, u.energyIntegrand i s := by
  haveI : Countable (TensorEigenIdx (I := I) (M := M) g r s) := CrossScaleField.countable_eigenIdx (I := I) (M := M) (g := g) (r := r) (s := s)
  set μ : Measure ℝ := volume.restrict (Set.Ioc (0 : ℝ) t) with hμ
  -- Per-mode integrability for the restricted measure.
  have hF_int : ∀ i, Integrable (u.energyIntegrand i) μ := fun i =>
    u.integrableOn_energyIntegrand i ht
  -- The dominating bound, integrable on `Ioc 0 t`.
  have hsub : Set.Ioc (0 : ℝ) t ⊆ Set.Icc (0 : ℝ) T :=
    fun x hx => ⟨le_of_lt hx.1, le_trans hx.2 ht.2⟩
  have hbound_int : Integrable (fun s => ‖u.hi s‖ ^ 2 + ‖u.lo.deriv s‖ ^ 2) μ :=
    u.integrableOn_bound.mono_set hsub
  -- Summability of `i ↦ ∫ ‖Fᵢ‖ ∂μ` via the partial-sum bound.
  have hF_sum : Summable (fun i => ∫ s, ‖u.energyIntegrand i s‖ ∂μ) := by
    refine summable_of_sum_le (c := ∫ s, (‖u.hi s‖ ^ 2 + ‖u.lo.deriv s‖ ^ 2) ∂μ)
      (fun i => integral_nonneg (fun s => norm_nonneg _)) ?_
    intro S
    -- `∑_{i∈S} ∫ ‖Fᵢ‖ = ∫ ∑_{i∈S} ‖Fᵢ‖ ≤ ∫ bound`.
    have hfin_int : ∀ i ∈ S, Integrable (fun s => ‖u.energyIntegrand i s‖) μ :=
      fun i _ => (hF_int i).norm
    rw [← MeasureTheory.integral_finset_sum S hfin_int]
    refine integral_mono_of_nonneg ?_ hbound_int ?_
    · exact ae_of_all _ (fun s => Finset.sum_nonneg (fun i _ => norm_nonneg _))
    · refine ae_of_all _ (fun s => ?_)
      calc ∑ i ∈ S, ‖u.energyIntegrand i s‖
          = ∑ i ∈ S, |u.energyIntegrand i s| := by
            refine Finset.sum_congr rfl (fun i _ => ?_); rw [Real.norm_eq_abs]
        _ ≤ ∑' i, |u.energyIntegrand i s| :=
            (u.summable_abs_energyIntegrand s).sum_le_tsum S (fun i _ => abs_nonneg _)
        _ ≤ ‖u.hi s‖ ^ 2 + ‖u.lo.deriv s‖ ^ 2 := u.tsum_abs_energyIntegrand_le s
  -- The interchange, transported through `∫₀ᵗ = ∫ over Ioc 0 t` (since `0 ≤ t`).
  have hinterchange :=
    MeasureTheory.integral_tsum_of_summable_integral_norm hF_int hF_sum
  rw [intervalIntegral.integral_of_le ht.1]
  rw [show (∫ s in Set.Ioc (0 : ℝ) t, ∑' i, u.energyIntegrand i s ∂volume) =
        ∫ s, ∑' i, u.energyIntegrand i s ∂μ from rfl]
  rw [← hinterchange]
  refine tsum_congr (fun i => ?_)
  rw [intervalIntegral.integral_of_le ht.1]

/-! ### The parabolic energy identity -/

/-- **The parabolic energy identity.**  For `t ∈ [0,T]`,

  `‖u.repr t‖²_{H^{a+1}} = ‖u.repr 0‖²_{H^{a+1}} +
      ∫₀ᵗ 2·crossPairing (u.hi s) (u.lo.deriv s) ds`.

This is the eigenmode tsum of the per-mode scalar fundamental theorem of calculus
(`perMode_energyIdentity`), with the mode sum and the time integral interchanged
(`tsum_intervalIntegral_energyIntegrand_eq`).  No regularity hypothesis beyond the
`CrossScaleField` data is required. -/
theorem energyIdentity {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    ‖u.repr t‖ ^ 2 = ‖u.repr 0‖ ^ 2 +
      ∫ s in (0 : ℝ)..t, 2 * crossPairing (I := I) (M := M) (u.hi s) (u.lo.deriv s) := by
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) T := ⟨le_rfl, le_trans ht.1 ht.2⟩
  -- The two squared norms as weighted-square tsums over modes.
  have hnorm_t : ‖u.repr t‖ ^ 2 =
      ∑' i, tensorSobolevWeight (I := I) (M := M) i (a + 1) * ((u.hi t).coeff i) ^ 2 := by
    rw [tensorHs.norm_sq_eq_tsum]; refine tsum_congr (fun i => ?_); rw [repr_coeff]
  have hnorm_0 : ‖u.repr 0‖ ^ 2 =
      ∑' i, tensorSobolevWeight (I := I) (M := M) i (a + 1) * ((u.hi 0).coeff i) ^ 2 := by
    rw [tensorHs.norm_sq_eq_tsum]; refine tsum_congr (fun i => ?_); rw [repr_coeff]
  -- The two weighted-square families are summable, as are the per-mode integrals.
  have hsum_init : Summable
      (fun i => tensorSobolevWeight (I := I) (M := M) i (a + 1) * ((u.hi 0).coeff i) ^ 2) := by
    have := (u.repr 0).weighted_summable
    simpa only [repr_coeff] using this
  have hsum_int : Summable (fun i => ∫ s in (0 : ℝ)..t, u.energyIntegrand i s) := by
    have hsummable_norm : Summable (fun i =>
        ∫ s, ‖u.energyIntegrand i s‖ ∂(volume.restrict (Set.Ioc (0 : ℝ) t))) := by
      haveI : Countable (TensorEigenIdx (I := I) (M := M) g r s) := CrossScaleField.countable_eigenIdx (I := I) (M := M) (g := g) (r := r) (s := s)
      have hsub : Set.Ioc (0 : ℝ) t ⊆ Set.Icc (0 : ℝ) T :=
        fun x hx => ⟨le_of_lt hx.1, le_trans hx.2 ht.2⟩
      have hbound_int : Integrable (fun s => ‖u.hi s‖ ^ 2 + ‖u.lo.deriv s‖ ^ 2)
          (volume.restrict (Set.Ioc (0 : ℝ) t)) :=
        u.integrableOn_bound.mono_set hsub
      -- Reuse the summability witness from the interchange proof.
      refine summable_of_sum_le
        (c := ∫ s, (‖u.hi s‖ ^ 2 + ‖u.lo.deriv s‖ ^ 2) ∂(volume.restrict (Set.Ioc (0 : ℝ) t)))
        (fun i => integral_nonneg (fun s => norm_nonneg _)) ?_
      intro S
      have hfin_int : ∀ i ∈ S, Integrable (fun s => ‖u.energyIntegrand i s‖)
          (volume.restrict (Set.Ioc (0 : ℝ) t)) :=
        fun i _ => (u.integrableOn_energyIntegrand i ht).norm
      rw [← MeasureTheory.integral_finset_sum S hfin_int]
      refine integral_mono_of_nonneg ?_ hbound_int ?_
      · exact ae_of_all _ (fun s => Finset.sum_nonneg (fun i _ => norm_nonneg _))
      · refine ae_of_all _ (fun s => ?_)
        calc ∑ i ∈ S, ‖u.energyIntegrand i s‖
            = ∑ i ∈ S, |u.energyIntegrand i s| := by
              refine Finset.sum_congr rfl (fun i _ => ?_); rw [Real.norm_eq_abs]
          _ ≤ ∑' i, |u.energyIntegrand i s| :=
              (u.summable_abs_energyIntegrand s).sum_le_tsum S (fun i _ => abs_nonneg _)
          _ ≤ ‖u.hi s‖ ^ 2 + ‖u.lo.deriv s‖ ^ 2 := u.tsum_abs_energyIntegrand_le s
    -- `∫₀ᵗ Fᵢ = ∫ over Ioc 0 t` and `|∫| ≤ ∫|·|`, so the integral family is summable.
    refine hsummable_norm.of_norm_bounded ?_
    intro i
    rw [intervalIntegral.integral_of_le ht.1, Real.norm_eq_abs]
    have heq : (∫ s in Set.Ioc (0 : ℝ) t, u.energyIntegrand i s ∂volume) =
        ∫ s, u.energyIntegrand i s ∂(volume.restrict (Set.Ioc (0 : ℝ) t)) := rfl
    rw [heq]
    refine (MeasureTheory.abs_integral_le_integral_abs).trans (le_of_eq ?_)
    refine integral_congr_ae (ae_of_all _ (fun s => ?_))
    exact (Real.norm_eq_abs _).symm
  -- Assemble: `‖u.repr t‖² = ∑'ᵢ [wᵢ⁺¹ cᵢ(0)² + ∫₀ᵗ Fᵢ]`.
  rw [hnorm_t]
  have hpermode : (fun i => tensorSobolevWeight (I := I) (M := M) i (a + 1) *
      ((u.hi t).coeff i) ^ 2) =
      (fun i => (tensorSobolevWeight (I := I) (M := M) i (a + 1) * ((u.hi 0).coeff i) ^ 2) +
        ∫ s in (0 : ℝ)..t, u.energyIntegrand i s) := by
    funext i
    rw [u.perMode_energyIdentity i ht]
    rfl
  rw [hpermode, hsum_init.tsum_add hsum_int, ← hnorm_0,
    u.tsum_intervalIntegral_energyIntegrand_eq ht]
  congr 1
  refine intervalIntegral.integral_congr (fun s _ => ?_)
  rw [u.tsum_energyIntegrand_eq s]

/-! ### The unconditional sharp Lions–Magenes sup-in-time estimate -/

/-- **Unconditional sharp Lions–Magenes sup-in-time energy estimate.**  For
`t ∈ [0,T]`,

  `‖u.repr t‖²_{H^{a+1}} ≤ ‖u.repr 0‖²_{H^{a+1}} +
      2 ∫₀ᵗ ‖u.hi s‖_{H^{a+2}} · ‖u.lo.deriv s‖_{Hᵃ} ds`.

This is the energy identity (`energyIdentity`) with its integrand controlled by
the cross-scale Cauchy–Schwarz bound `abs_crossPairing_le`; both the energy
integrand and the dominating product integrand are interval integrable, so the
conditional estimate `normSq_le_of_energyIdentity` applies with the energy
identity discharged unconditionally. -/
theorem normSq_repr_le_init_add_integral {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    ‖u.repr t‖ ^ 2 ≤ ‖u.repr 0‖ ^ 2 +
      ∫ s in (0 : ℝ)..t, 2 * (‖u.hi s‖ * ‖u.lo.deriv s‖) := by
  -- Interval integrability of the dominating product integrand `2·‖u.hi‖·‖u.lo.deriv‖`.
  have hsub : Set.Ioc (0 : ℝ) t ⊆ Set.Icc (0 : ℝ) T :=
    fun x hx => ⟨le_of_lt hx.1, le_trans hx.2 ht.2⟩
  have hprod_int : IntegrableOn (fun s => ‖u.hi s‖ * ‖u.lo.deriv s‖)
      (Set.Ioc (0 : ℝ) t) volume := by
    have hcont : ContinuousOn (fun s => ‖u.hi s‖) (Set.Icc (0 : ℝ) t) :=
      (continuous_norm.comp_continuousOn u.hi_continuousOn).mono
        (fun x hx => ⟨hx.1, le_trans hx.2 ht.2⟩)
    have hderiv_norm_int : IntegrableOn (fun s => ‖u.lo.deriv s‖) (Set.Ioc (0 : ℝ) t) volume :=
      ((TimeSobolev.integrableOn u.lo.deriv).mono_set hsub).norm
    exact MeasureTheory.IntegrableOn.continuousOn_mul_of_subset hcont hderiv_norm_int
      isCompact_Icc measurableSet_Ioc (fun x hx => ⟨le_of_lt hx.1, hx.2⟩)
  have hint_norm : IntervalIntegrable
      (fun s => 2 * (‖u.hi s‖ * ‖u.lo.deriv s‖)) volume 0 t := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le ht.1]
    exact hprod_int.const_mul 2
  -- Interval integrability of the energy integrand `2·crossPairing`, dominated by the
  -- product integrand via the cross-scale Cauchy–Schwarz bound `abs_crossPairing_le`.
  have hint_cp : IntervalIntegrable
      (fun s => 2 * crossPairing (I := I) (M := M) (u.hi s) (u.lo.deriv s)) volume 0 t := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le ht.1]
    set μ : Measure ℝ := volume.restrict (Set.Ioc (0 : ℝ) t) with hμ
    -- Measurability: `crossPairing = ⟪rescaleToL2 (u.hi ·), rescaleToL2 (u.lo.deriv ·)⟫`,
    -- inner product of a continuous and a measurable map.
    have hmeas : AEStronglyMeasurable
        (fun s => 2 * crossPairing (I := I) (M := M) (u.hi s) (u.lo.deriv s)) μ := by
      have hcongr : (fun s => 2 * crossPairing (I := I) (M := M) (u.hi s) (u.lo.deriv s)) =
          fun s => 2 * (inner ℝ (tensorHs.rescaleToL2 (I := I) (M := M) (u.hi s))
            (tensorHs.rescaleToL2 (I := I) (M := M) (u.lo.deriv s)) : ℝ) := by
        funext s; rw [crossPairing_eq_inner_rescale]
      rw [hcongr]
      have hhi : AEStronglyMeasurable
          (fun s => tensorHs.rescaleToL2 (I := I) (M := M) (u.hi s)) μ := by
        have hcont : ContinuousOn
            (fun s => tensorHs.rescaleToL2 (I := I) (M := M) (u.hi s)) (Set.Icc (0 : ℝ) T) :=
          (tensorHs.rescaleEquivL2 (I := I) (M := M)).continuous.comp_continuousOn
            u.hi_continuousOn
        exact (hcont.mono hsub).aestronglyMeasurable measurableSet_Ioc
      have hlo : AEStronglyMeasurable
          (fun s => tensorHs.rescaleToL2 (I := I) (M := M) (u.lo.deriv s)) μ := by
        have hbase : AEStronglyMeasurable (fun s => u.lo.deriv s) μ :=
          (Lp.aestronglyMeasurable u.lo.deriv).mono_measure
            (Measure.restrict_mono hsub le_rfl)
        exact (tensorHs.rescaleEquivL2 (I := I) (M := M)).continuous.comp_aestronglyMeasurable hbase
      exact (AEStronglyMeasurable.inner hhi hlo).const_mul 2
    -- Domination by the product integrand.
    refine Integrable.mono' (hprod_int.const_mul 2) hmeas (ae_of_all _ (fun s => ?_))
    rw [Real.norm_eq_abs, abs_mul, show |(2 : ℝ)| = 2 from by norm_num]
    have hcs := abs_crossPairing_le (I := I) (M := M) (u.hi s) (u.lo.deriv s)
    nlinarith [hcs, abs_nonneg (crossPairing (I := I) (M := M) (u.hi s) (u.lo.deriv s)),
      mul_nonneg (norm_nonneg (u.hi s)) (norm_nonneg (u.lo.deriv s))]
  -- Apply the conditional estimate with the unconditional energy identity.
  exact u.normSq_le_of_energyIdentity ht (u.energyIdentity ht) hint_cp hint_norm

end CrossScaleField

end QuasiLinear
end Parabolic
end Analysis
end DifferentialGeometry
