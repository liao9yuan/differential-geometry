import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.TensorHsRealize
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.RicciConnection
import DifferentialGeometry.Analysis.Parabolic.DeTurckLinearization.MetricFamilyChartLinearization
import DifferentialGeometry.Geometry.Connection.ChartBridge.Ricci
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# The mean-value (FTC) core for the Ricci-tensor difference of two realized metrics

For a closed smooth Riemannian manifold `(M, g₀)` and two endpoint perturbation tensor
sections `T, T' : SmoothCcTensor g₀ 0 2`, both `g₀`-fibre small with constant `< 1`, this
file builds the **mean-value (fundamental theorem of calculus) reduction** of the Ricci-arm
difference
$$\operatorname{Ric}(g_1)_{x}(v, w) - \operatorname{Ric}(g_1')_{x}(v, w)
    = \int_0^1 \bigl(D\!\operatorname{Ric}\bigr)_{g_s}[T - T']_x(v, w)\, ds,$$
where `g₁ = realize(g₀, T)`, `g₁' = realize(g₀, T')`, and `g_s = realize(g₀, (1-s)·T' + s·T)`
is the straight-line metric path joining them through the convex combination of the two
perturbations.  The integrand is the **linearized Ricci operator** `linearizedRicciAt g_s`
applied to the perturbation velocity `T - T'`.

This replaces the single-endpoint Palatini telescope (which leaves un-capturable
two-endpoint cross terms) with the classical mean-value identity: the difference of a
nonlinear functional at two points is the integral of its derivative along any path joining
them.

## Contents

* `convexPerturbation g₀ T T' s` — the convex-combination perturbation
  `(1 - s)·T' + s·T : SmoothCcTensor g₀ 0 2`, with endpoint identities at `s = 0, 1`.
* `convexPerturbation_gFibreOpBound` — the convex-combination smallness bound: on `[0,1]`
  the perturbation `convexPerturbation g₀ T T' s` is `g₀`-fibre bounded by the convex
  combination `(1 - s)·δ' + s·δ < 1`, so the realized metric path is positive-definite.
* `realizedMetricPath g₀ T T' hδ_lt hδ hδ'_lt hδ' s` — the realized metric path
  `realize(g₀, convexPerturbation g₀ T T' s)` for `s ∈ [0,1]`, with endpoint identities
  `path 0 = realize T'`, `path 1 = realize T`.
* `linearizedRicciAt g₀ T T' x v w s₀` — the linearized Ricci operator at the path metric
  `g_{s₀}` in the perturbation direction `T - T'`, defined as the `s`-derivative of the
  Ricci tensor along the (re-anchored) realized path.
* `hasDerivAt_ricciTensor_realizedMetricPath` (posited child) — the path `s`-derivative of
  the realized Ricci tensor, identified with `linearizedRicciAt` at each `s₀ ∈ [0,1]`, with
  interval-integrability of the integrand.  This is the deep mean-value derivative content
  (the metric-derivative of the curvature functional equals the linearized Ricci operator).
* `ricciTensor_realized_sub_eq_integral_linearizedRicci` — the FTC headline: the realized
  Ricci-arm difference equals `∫₀¹ linearizedRicciAt g_s (T - T') ds`.
-/

noncomputable section

set_option linter.style.setOption false
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 800000

open Set Function MeasureTheory intervalIntegral Bundle Tensor0SBundle
open scoped Topology Manifold BigOperators ContDiff Matrix

namespace DifferentialGeometry
namespace PDE
namespace DeTurck
namespace RicciLinearization

open DifferentialGeometry
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurckCoefficients

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

/-! ### Additivity of the symmetric extraction (mirroring `ccTensorBilinSymm_smul`) -/

/-- The underlying multilinear field `ccTensorMultilinear` is additive in the tensor
section. -/
theorem ccTensorMultilinear_add (g : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g 0 2) (x : M) :
    (ccTensorMultilinear (I := I) g (T + T') x : Tensor0SSpace 2 I x)
      = (ccTensorMultilinear (I := I) g T x : Tensor0SSpace 2 I x)
        + (ccTensorMultilinear (I := I) g T' x : Tensor0SSpace 2 I x) := by
  unfold ccTensorMultilinear
  rw [SmoothCcTensor.toSection_add]
  rfl

/-- The model value `ccTensorModel` is additive in the tensor section. -/
theorem ccTensorModel_add (g : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g 0 2) (x : M) :
    ccTensorModel (I := I) g (T + T') x =
      ccTensorModel (I := I) g T x + ccTensorModel (I := I) g T' x := by
  unfold ccTensorModel
  rw [ccTensorMultilinear_add, Tensor0SSpace.toModel_add]

/-- The symmetrized extraction is additive in the tensor section. -/
theorem ccTensorBilinSymm_add (g : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g 0 2) (x : M) (v w : TangentSpace I x) :
    ccTensorBilinSymm (I := I) g (T + T') x v w =
      ccTensorBilinSymm (I := I) g T x v w + ccTensorBilinSymm (I := I) g T' x v w := by
  simp only [ccTensorBilinSymm_apply, ccTensorBilin_apply, ccTensorModel_add,
    ContinuousMultilinearMap.add_apply]
  ring

/-! ### The convex-combination perturbation and its smallness bound -/

/-- The **convex-combination perturbation** `(1 - s)·T' + s·T` of two endpoint
perturbation tensor sections, as a `SmoothCcTensor g₀ 0 2`.  As `s` runs over `[0,1]` this
traces the straight line in perturbation space from `T'` (at `s = 0`) to `T` (at `s = 1`). -/
def convexPerturbation (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2) (s : ℝ) : SmoothCcTensor g₀ 0 2 :=
  (1 - s) • T' + s • T

@[simp] lemma convexPerturbation_zero (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2) :
    convexPerturbation (I := I) g₀ T T' 0 = T' := by
  simp [convexPerturbation]

@[simp] lemma convexPerturbation_one (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2) :
    convexPerturbation (I := I) g₀ T T' 1 = T := by
  simp [convexPerturbation]

/-- The fibre form of the convex perturbation is the convex combination of the two endpoint
fibre forms. -/
lemma ccTensorBilinSymm_convexPerturbation (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2) (s : ℝ) (x : M) (v w : TangentSpace I x) :
    ccTensorBilinSymm (I := I) g₀ (convexPerturbation (I := I) g₀ T T' s) x v w =
      (1 - s) * ccTensorBilinSymm (I := I) g₀ T' x v w +
        s * ccTensorBilinSymm (I := I) g₀ T x v w := by
  rw [convexPerturbation, ccTensorBilinSymm_add, ccTensorBilinSymm_smul,
    ccTensorBilinSymm_smul]

/-- **Convex-combination smallness bound.**  If `T` is `g₀`-fibre bounded by `δ` and `T'`
by `δ'`, then the convex perturbation `(1 - s)·T' + s·T` is `g₀`-fibre bounded by the convex
combination `(1 - s)·δ' + s·δ` for every `s ∈ [0,1]`. -/
theorem convexPerturbation_gFibreOpBound (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    gFibreOpBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (convexPerturbation (I := I) g₀ T T' s))
      ((1 - s) * δ' + s * δ) := by
  intro x v w
  have hsqv : (0 : ℝ) ≤ Real.sqrt (g₀.inner x v v) := Real.sqrt_nonneg _
  have hsqw : (0 : ℝ) ≤ Real.sqrt (g₀.inner x w w) := Real.sqrt_nonneg _
  have hprod : (0 : ℝ) ≤ Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x w w) :=
    mul_nonneg hsqv hsqw
  have h1ms : (0 : ℝ) ≤ 1 - s := by linarith
  have hbT := hδ x v w
  have hbT' := hδ' x v w
  rw [ccTensorBilinSymm_convexPerturbation]
  calc
    |(1 - s) * ccTensorBilinSymm (I := I) g₀ T' x v w +
        s * ccTensorBilinSymm (I := I) g₀ T x v w|
        ≤ |(1 - s) * ccTensorBilinSymm (I := I) g₀ T' x v w| +
            |s * ccTensorBilinSymm (I := I) g₀ T x v w| := abs_add_le _ _
    _ = (1 - s) * |ccTensorBilinSymm (I := I) g₀ T' x v w| +
            s * |ccTensorBilinSymm (I := I) g₀ T x v w| := by
        rw [abs_mul, abs_mul, abs_of_nonneg h1ms, abs_of_nonneg hs0]
    _ ≤ (1 - s) * (δ' * Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x w w)) +
            s * (δ * Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x w w)) := by
        gcongr
    _ = ((1 - s) * δ' + s * δ) * Real.sqrt (g₀.inner x v v) *
            Real.sqrt (g₀.inner x w w) := by ring

/-- For `s ∈ [0,1]` the convex smallness constant `(1 - s)·δ' + s·δ` is `< 1` whenever both
`δ, δ' < 1`. -/
theorem convex_smallConstant_lt_one {δ δ' : ℝ} (hδ_lt : δ < 1) (hδ'_lt : δ' < 1)
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    (1 - s) * δ' + s * δ < 1 := by
  have h1ms : (0 : ℝ) ≤ 1 - s := by linarith
  nlinarith [mul_nonneg h1ms (le_of_lt (by linarith : (0 : ℝ) < 1 - δ')),
    mul_nonneg hs0 (le_of_lt (by linarith : (0 : ℝ) < 1 - δ))]

/-! ### The realized metric path -/

/-- **The realized metric path** `s ↦ realize(g₀, (1 - s)·T' + s·T)` for `s ∈ [0,1]`.
The convex-combination smallness bound (`convexPerturbation_gFibreOpBound`,
`convex_smallConstant_lt_one`) guarantees that the convex perturbation stays `g₀`-fibre
small with constant `< 1`, so each `realizedMetricPath … s` is a genuine positive-definite
`SmoothRiemannianMetric I M`.  At `s = 0` it is `realize(g₀, T')` and at `s = 1` it is
`realize(g₀, T)` (`realizedMetricPath_zero_inner`, `realizedMetricPath_one_inner`). -/
def realizedMetricPath (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    SmoothRiemannianMetric I M :=
  tensorSectionRealizeMetric (I := I) g₀ (convexPerturbation (I := I) g₀ T T' s)
    (convex_smallConstant_lt_one hδ_lt hδ'_lt hs0 hs1)
    (convexPerturbation_gFibreOpBound (I := I) g₀ T T' hδ hδ' hs0 hs1)

/-- The realized metric path is fibrewise `g₀ + ` the convex perturbation form. -/
theorem realizedMetricPath_inner (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (x : M) (v w : TangentSpace I x) :
    (realizedMetricPath (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' hs0 hs1).inner x v w =
      g₀.inner x v w +
        ccTensorBilinSymm (I := I) g₀ (convexPerturbation (I := I) g₀ T T' s) x v w := by
  rw [realizedMetricPath, tensorSectionRealizeMetric_inner]

/-! ### Endpoint metric equalities -/

/-- **Metric extensionality through the fibre inner product.**  Two smooth Riemannian
metrics with the same fibrewise inner product are equal (the remaining structure fields are
propositions, hence proof-irrelevant). -/
theorem riemannianMetric_eq_of_inner (g g' : SmoothRiemannianMetric I M)
    (h : ∀ (b : M) (v w : TangentSpace I b), g.inner b v w = g'.inner b v w) :
    g = g' := by
  have hinner : g.inner = g'.inner := by
    funext b
    exact ContinuousLinearMap.ext fun v => ContinuousLinearMap.ext fun w => h b v w
  cases g; cases g'
  congr

/-- The clamped path metric at a parameter `s ∈ [0,1]` (clamped to `max 0 (min s 1)`) is the
genuine path metric at `s`. -/
private lemma clamp_eq_of_mem_Icc {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    max 0 (min s 1) = s := by
  obtain ⟨hs0, hs1⟩ := hs
  rw [min_eq_left hs1, max_eq_right hs0]

/-! ### The linearized Ricci operator along the path and the FTC -/

/-- **The scalar realized Ricci value along the path** as a function of `s ∈ ℝ`, used as the
`f` of the fundamental theorem of calculus.  For `s` outside `[0,1]` the path metric is not
defined, so the value is the path metric clamped to the nearest endpoint; on `[0,1]` it is
the genuine realized Ricci value `Ric(g_s)_x(v, w)`. -/
def realizedRicciPathValue (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (v w : TangentSpace I x) (s : ℝ) : ℝ :=
  ricciTensor (I := I)
    (realizedMetricPath (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ'
      (le_max_left 0 (min s 1)) (by
        have : min s 1 ≤ 1 := min_le_right s 1
        exact max_le (zero_le_one) this)) x v w

/-- The path-value at `s = 1` equals the realized Ricci tensor of `realize(g₀, T)`. -/
theorem realizedRicciPathValue_one (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (v w : TangentSpace I x) :
    realizedRicciPathValue (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x v w 1 =
      ricciTensor (I := I) (tensorSectionRealizeMetric (I := I) g₀ T hδ_lt hδ) x v w := by
  rw [realizedRicciPathValue]
  have hmetric :
      realizedMetricPath (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ'
          (le_max_left 0 (min (1 : ℝ) 1))
          (max_le (zero_le_one) (le_trans (min_le_right (1 : ℝ) 1) (le_refl 1))) =
        tensorSectionRealizeMetric (I := I) g₀ T hδ_lt hδ := by
    refine riemannianMetric_eq_of_inner _ _ (fun b u z => ?_)
    rw [realizedMetricPath_inner, tensorSectionRealizeMetric_inner,
      ccTensorBilinSymm_convexPerturbation]
    have : max (0 : ℝ) (min 1 1) = 1 := by norm_num
    rw [this]; ring
  rw [hmetric]

/-- The path-value at `s = 0` equals the realized Ricci tensor of `realize(g₀, T')`. -/
theorem realizedRicciPathValue_zero (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (v w : TangentSpace I x) :
    realizedRicciPathValue (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x v w 0 =
      ricciTensor (I := I) (tensorSectionRealizeMetric (I := I) g₀ T' hδ'_lt hδ') x v w := by
  rw [realizedRicciPathValue]
  have hmetric :
      realizedMetricPath (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ'
          (le_max_left 0 (min (0 : ℝ) 1))
          (max_le (zero_le_one) (le_trans (min_le_right (0 : ℝ) 1) (le_refl 1))) =
        tensorSectionRealizeMetric (I := I) g₀ T' hδ'_lt hδ' := by
    refine riemannianMetric_eq_of_inner _ _ (fun b u z => ?_)
    rw [realizedMetricPath_inner, tensorSectionRealizeMetric_inner,
      ccTensorBilinSymm_convexPerturbation]
    have : max (0 : ℝ) (min 0 1) = 0 := by norm_num
    rw [this]; ring
  rw [hmetric]

/-- **The linearized Ricci operator at the path metric `g_{s₀}` in direction `T - T'`.**
By definition it is the `s`-derivative of the realized Ricci value along the path at `s₀`;
this is the genuine differential `D\!\operatorname{Ric}_{g_{s₀}}[T - T']_x(v, w)` of the
Ricci tensor functional in the metric-perturbation direction `T - T'`.  It is the integrand
of the mean-value reduction. -/
def linearizedRicciAt (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (v w : TangentSpace I x) (s₀ : ℝ) : ℝ :=
  deriv (realizedRicciPathValue (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x v w) s₀

/-! ### abs-value smallness, valid on a neighborhood of `[0,1]` -/

theorem convexPerturbation_gFibreOpBound_abs (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (s : ℝ) :
    gFibreOpBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (convexPerturbation (I := I) g₀ T T' s))
      (|1 - s| * δ' + |s| * δ) := by
  intro x v w
  have hbT := hδ x v w
  have hbT' := hδ' x v w
  rw [ccTensorBilinSymm_convexPerturbation]
  calc
    |(1 - s) * ccTensorBilinSymm (I := I) g₀ T' x v w +
        s * ccTensorBilinSymm (I := I) g₀ T x v w|
        ≤ |(1 - s) * ccTensorBilinSymm (I := I) g₀ T' x v w| +
            |s * ccTensorBilinSymm (I := I) g₀ T x v w| := abs_add_le _ _
    _ = |1 - s| * |ccTensorBilinSymm (I := I) g₀ T' x v w| +
            |s| * |ccTensorBilinSymm (I := I) g₀ T x v w| := by rw [abs_mul, abs_mul]
    _ ≤ |1 - s| * (δ' * Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x w w)) +
            |s| * (δ * Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x w w)) := by
        have ha1 : (0:ℝ) ≤ |1 - s| := abs_nonneg _
        have ha2 : (0:ℝ) ≤ |s| := abs_nonneg _
        gcongr
    _ = (|1 - s| * δ' + |s| * δ) * Real.sqrt (g₀.inner x v v) *
            Real.sqrt (g₀.inner x w w) := by ring

theorem abs_convex_smallConstant_lt_one {δ δ' : ℝ} (hδ_lt : δ < 1) (hδ'_lt : δ' < 1)
    {s : ℝ} (hs : s ∈ Set.Icc (0:ℝ) 1) :
    |1 - s| * δ' + |s| * δ < 1 := by
  obtain ⟨h0, h1⟩ := hs
  rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 - s), abs_of_nonneg h0]
  nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 1 - s) (by linarith : (0:ℝ) < 1 - δ').le,
    mul_nonneg h0 (by linarith : (0:ℝ) < 1 - δ).le]

/-! ### The open realized metric family -/

/-- The realized metric of the convex perturbation at any `s` whose abs-convex smallness
constant is `< 1`. -/
def realizedMetricPathOpen (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (s : ℝ) (hs : |1 - s| * δ' + |s| * δ < 1) :
    SmoothRiemannianMetric I M :=
  tensorSectionRealizeMetric (I := I) g₀ (convexPerturbation (I := I) g₀ T T' s)
    hs (convexPerturbation_gFibreOpBound_abs (I := I) g₀ T T' hδ hδ' s)

theorem realizedMetricPathOpen_inner (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (s : ℝ) (hs : |1 - s| * δ' + |s| * δ < 1) (x : M) (v w : TangentSpace I x) :
    (realizedMetricPathOpen (I := I) g₀ T T' hδ hδ' s hs).inner x v w =
      g₀.inner x v w +
        ccTensorBilinSymm (I := I) g₀ (convexPerturbation (I := I) g₀ T T' s) x v w := by
  rw [realizedMetricPathOpen, tensorSectionRealizeMetric_inner]

/-! ### Generic joint `(s,y)`-smoothness tower -/

private lemma gen_joint_partialDeriv
    (Ψ : ℝ → E → ℝ) (q : Fin (Module.finrank ℝ E)) {s₀ : ℝ} {y₀ : E}
    (hΨ : ContDiffAt ℝ ∞ (fun r : ℝ × E => Ψ r.1 r.2) (s₀, y₀)) :
    ContDiffAt ℝ ∞
      (fun p : ℝ × E => partialDeriv (E := E) q (fun y => Ψ p.1 y) p.2) (s₀, y₀) := by
  have hf : ContDiffAt ℝ ∞
      (Function.uncurry (fun (p : ℝ × E) (y : E) => Ψ p.1 y))
      ((s₀, y₀), (fun p : ℝ × E => p.2) (s₀, y₀)) := by
    have huncurry : (Function.uncurry (fun (p : ℝ × E) (y : E) => Ψ p.1 y)) =
        (fun r : ℝ × E => Ψ r.1 r.2) ∘ (fun z : (ℝ × E) × E => (z.1.1, z.2)) := by
      funext z; rfl
    rw [huncurry]
    refine hΨ.comp ((s₀, y₀), y₀) ?_
    exact (contDiffAt_fst.comp ((s₀, y₀), y₀) contDiffAt_fst).prodMk contDiffAt_snd
  have hg : ContDiffAt ℝ ∞ (fun p : ℝ × E => p.2) (s₀, y₀) := contDiffAt_snd
  have hfd := ContDiffAt.fderiv hf hg (le_refl _)
  exact (ContinuousLinearMap.apply ℝ ℝ (chartModelBasis E q)).contDiff.contDiffAt.comp (s₀, y₀) hfd

variable (gfam : ℝ → SmoothRiemannianMetric I M) (α : M)

/-- Hypothesis bundle: joint Gram C∞ at every base point with `s₀ ∈ S`, `y₀` chart-interior;
plus positive-definiteness of the path Gram over the chart base set for `s₀ ∈ S`. -/
def GenJointGram (S : Set ℝ) : Prop :=
  (∀ (i j : Fin (Module.finrank ℝ E)) {s₀ : ℝ} {y₀ : E}, s₀ ∈ S →
      y₀ ∈ interior (extChartAt I α).target →
      ContDiffAt ℝ ∞ (fun p : ℝ × E => chartGramOnE (I := I) (gfam p.1) α i j p.2) (s₀, y₀)) ∧
  (∀ {s₀ : ℝ}, s₀ ∈ S →
      ∀ {x : M}, x ∈ (trivializationAt E (TangentSpace I) α).baseSet →
      0 < (chartGramMatrix (I := I) (gfam s₀) α x).det)

private lemma gen_joint_invGram {S : Set ℝ} (hG : GenJointGram (I := I) gfam α S)
    (k l : Fin (Module.finrank ℝ E)) {s₀ : ℝ} {y₀ : E} (hs : s₀ ∈ S)
    (hy : y₀ ∈ interior (extChartAt I α).target) :
    ContDiffAt ℝ ∞
      (fun p : ℝ × E => chartInvGramOnE (I := I) (gfam p.1) α k l p.2) (s₀, y₀) := by
  classical
  have hGentry : ∀ a b : Fin (Module.finrank ℝ E),
      ContDiffAt ℝ ∞
        (fun p : ℝ × E => chartGramMatrix (I := I) (gfam p.1) α
          ((extChartAt I α).symm p.2) a b) (s₀, y₀) := by
    intro a b
    have := hG.1 a b hs hy
    simpa only [chartGramOnE_def] using this
  have hdet : ContDiffAt ℝ ∞
      (fun p : ℝ × E => (chartGramMatrix (I := I) (gfam p.1) α
        ((extChartAt I α).symm p.2)).det) (s₀, y₀) := by
    have hdet_eq : (fun p : ℝ × E => (chartGramMatrix (I := I) (gfam p.1) α
          ((extChartAt I α).symm p.2)).det) =
        (fun p : ℝ × E => ∑ σ : Equiv.Perm (Fin (Module.finrank ℝ E)),
          (Equiv.Perm.sign σ : ℝ) *
            ∏ kk, chartGramMatrix (I := I) (gfam p.1) α
              ((extChartAt I α).symm p.2) (σ kk) kk) := by
      funext p; rw [Matrix.det_apply]; simp [Units.smul_def]
    rw [hdet_eq]
    refine ContDiffAt.sum (fun σ _ => ?_)
    refine contDiffAt_const.mul ?_
    exact contDiffAt_prod (fun kk _ => hGentry (σ kk) kk)
  have hx_base : (extChartAt I α).symm y₀ ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    have hy_t : y₀ ∈ (extChartAt I α).target := interior_subset hy
    have hsource : (extChartAt I α).symm y₀ ∈ (extChartAt I α).source :=
      (extChartAt I α).map_target hy_t
    rw [extChartAt_source_eq_chartAt_source (I := I)] at hsource
    exact hsource
  have hdet_ne : (chartGramMatrix (I := I) (gfam (s₀, y₀).1) α
      ((extChartAt I α).symm (s₀, y₀).2)).det ≠ 0 := ne_of_gt (hG.2 hs hx_base)
  have hadj : ∀ kk ll : Fin (Module.finrank ℝ E),
      ContDiffAt ℝ ∞
        (fun p : ℝ × E => (chartGramMatrix (I := I) (gfam p.1) α
          ((extChartAt I α).symm p.2)).adjugate kk ll) (s₀, y₀) := by
    intro kk ll
    have hexp : (fun p : ℝ × E => (chartGramMatrix (I := I) (gfam p.1) α
          ((extChartAt I α).symm p.2)).adjugate kk ll) =
        (fun p : ℝ × E => ∑ σ : Equiv.Perm (Fin (Module.finrank ℝ E)),
          (Equiv.Perm.sign σ : ℝ) *
            ∏ m, (chartGramMatrix (I := I) (gfam p.1) α
                ((extChartAt I α).symm p.2)).updateRow ll
                (Pi.single kk (1 : ℝ)) (σ m) m) := by
      funext p; rw [Matrix.adjugate_apply, Matrix.det_apply]; simp [Units.smul_def]
    rw [hexp]
    refine ContDiffAt.sum (fun σ _ => ?_)
    refine contDiffAt_const.mul ?_
    refine contDiffAt_prod (fun m _ => ?_)
    by_cases hσm : σ m = ll
    · have heq : (fun p : ℝ × E => (chartGramMatrix (I := I) (gfam p.1) α
          ((extChartAt I α).symm p.2)).updateRow ll (Pi.single kk (1 : ℝ)) (σ m) m) =
          (fun _ : ℝ × E => (Pi.single (M := fun _ : Fin (Module.finrank ℝ E) => ℝ) kk
            (1 : ℝ)) m) := by
        funext p; rw [hσm, Matrix.updateRow_self]
      rw [heq]; exact contDiffAt_const
    · have heq : (fun p : ℝ × E => (chartGramMatrix (I := I) (gfam p.1) α
          ((extChartAt I α).symm p.2)).updateRow ll (Pi.single kk (1 : ℝ)) (σ m) m) =
          (fun p : ℝ × E => chartGramMatrix (I := I) (gfam p.1) α
            ((extChartAt I α).symm p.2) (σ m) m) := by
        funext p; rw [Matrix.updateRow_ne hσm]
      rw [heq]; exact hGentry (σ m) m
  have hcongr : (fun p : ℝ × E => chartInvGramOnE (I := I) (gfam p.1) α k l p.2) =
      (fun p : ℝ × E => ((chartGramMatrix (I := I) (gfam p.1) α
          ((extChartAt I α).symm p.2)).det)⁻¹ *
        (chartGramMatrix (I := I) (gfam p.1) α ((extChartAt I α).symm p.2)).adjugate k l) := by
    funext p
    rw [chartInvGramOnE_def]
    change (chartGramMatrix (I := I) (gfam p.1) α ((extChartAt I α).symm p.2))⁻¹ k l = _
    rw [Matrix.inv_def]
    change (Ring.inverse (chartGramMatrix (I := I) (gfam p.1) α
            ((extChartAt I α).symm p.2)).det •
            (chartGramMatrix (I := I) (gfam p.1) α ((extChartAt I α).symm p.2)).adjugate) k l = _
    rw [Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv]
  rw [hcongr]
  exact ((contDiffAt_inv _ hdet_ne).comp (s₀, y₀) hdet).mul (hadj k l)

private lemma gen_joint_gramBracket {S : Set ℝ} (hG : GenJointGram (I := I) gfam α S)
    (i j l : Fin (Module.finrank ℝ E)) {s₀ : ℝ} {y₀ : E} (hs : s₀ ∈ S)
    (hy : y₀ ∈ interior (extChartAt I α).target) :
    ContDiffAt ℝ ∞
      (fun r : ℝ × E => gramBracket (I := I) (gfam r.1) α i j l r.2) (s₀, y₀) := by
  have heq : (fun r : ℝ × E => gramBracket (I := I) (gfam r.1) α i j l r.2) =
      (fun r : ℝ × E =>
        partialDeriv (E := E) i (fun y => chartGramOnE (I := I) (gfam r.1) α l j y) r.2 +
          partialDeriv (E := E) j (fun y => chartGramOnE (I := I) (gfam r.1) α l i y) r.2 -
          partialDeriv (E := E) l (fun y => chartGramOnE (I := I) (gfam r.1) α i j y) r.2) := by
    funext r; rw [gramBracket]
  rw [heq]
  exact ((gen_joint_partialDeriv (fun s y => chartGramOnE (I := I) (gfam s) α l j y) i
      (hG.1 l j hs hy)).add
    (gen_joint_partialDeriv (fun s y => chartGramOnE (I := I) (gfam s) α l i y) j
      (hG.1 l i hs hy))).sub
    (gen_joint_partialDeriv (fun s y => chartGramOnE (I := I) (gfam s) α i j y) l
      (hG.1 i j hs hy))

private lemma gen_joint_christoffel {S : Set ℝ} (hG : GenJointGram (I := I) gfam α S)
    (i j k : Fin (Module.finrank ℝ E)) {s₀ : ℝ} {y₀ : E} (hs : s₀ ∈ S)
    (hy : y₀ ∈ interior (extChartAt I α).target) :
    ContDiffAt ℝ ∞
      (fun r : ℝ × E => chartChristoffel (I := I) (gfam r.1) α i j k r.2) (s₀, y₀) := by
  have heq : (fun r : ℝ × E => chartChristoffel (I := I) (gfam r.1) α i j k r.2) =
      (fun r : ℝ × E => (1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
        chartInvGramOnE (I := I) (gfam r.1) α k l r.2 *
          gramBracket (I := I) (gfam r.1) α i j l r.2) := by
    funext r; rw [chartChristoffel_eq_sum_invGramOnE_bracket]
  rw [heq]
  refine contDiffAt_const.mul (ContDiffAt.sum (fun l _ => ?_))
  exact (gen_joint_invGram (I := I) gfam α hG k l hs hy).mul
    (gen_joint_gramBracket (I := I) gfam α hG i j l hs hy)

private lemma gen_joint_partial_christoffel {S : Set ℝ} (hG : GenJointGram (I := I) gfam α S)
    (m i j k : Fin (Module.finrank ℝ E)) {s₀ : ℝ} {y₀ : E} (hs : s₀ ∈ S)
    (hy : y₀ ∈ interior (extChartAt I α).target) :
    ContDiffAt ℝ ∞
      (fun r : ℝ × E =>
        partialDeriv (E := E) m (fun y => chartChristoffel (I := I) (gfam r.1) α i j k y) r.2)
      (s₀, y₀) :=
  gen_joint_partialDeriv (fun s y => chartChristoffel (I := I) (gfam s) α i j k y) m
    (gen_joint_christoffel (I := I) gfam α hG i j k hs hy)

private lemma gen_joint_riemann {S : Set ℝ} (hG : GenJointGram (I := I) gfam α S)
    (i j k l : Fin (Module.finrank ℝ E)) {s₀ : ℝ} {y₀ : E} (hs : s₀ ∈ S)
    (hy : y₀ ∈ interior (extChartAt I α).target) :
    ContDiffAt ℝ ∞
      (fun r : ℝ × E => chartRiemannTensor (I := I) (gfam r.1) α i j k l r.2) (s₀, y₀) := by
  have heq : (fun r : ℝ × E => chartRiemannTensor (I := I) (gfam r.1) α i j k l r.2) =
      (fun r : ℝ × E =>
        partialDeriv (E := E) j (fun y => chartChristoffel (I := I) (gfam r.1) α i k l y) r.2 -
          partialDeriv (E := E) k (fun y => chartChristoffel (I := I) (gfam r.1) α i j l y) r.2 +
          (∑ m : Fin (Module.finrank ℝ E),
            (chartChristoffel (I := I) (gfam r.1) α j m l r.2 *
                chartChristoffel (I := I) (gfam r.1) α i k m r.2 -
              chartChristoffel (I := I) (gfam r.1) α k m l r.2 *
                chartChristoffel (I := I) (gfam r.1) α i j m r.2))) := by
    funext r; rw [chartRiemannTensor_def]
  rw [heq]
  refine ((gen_joint_partial_christoffel (I := I) gfam α hG j i k l hs hy).sub
    (gen_joint_partial_christoffel (I := I) gfam α hG k i j l hs hy)).add ?_
  refine ContDiffAt.sum (fun m _ => ?_)
  exact ((gen_joint_christoffel (I := I) gfam α hG j m l hs hy).mul
      (gen_joint_christoffel (I := I) gfam α hG i k m hs hy)).sub
    ((gen_joint_christoffel (I := I) gfam α hG k m l hs hy).mul
      (gen_joint_christoffel (I := I) gfam α hG i j m hs hy))

private lemma gen_joint_ricci {S : Set ℝ} (hG : GenJointGram (I := I) gfam α S)
    (i k : Fin (Module.finrank ℝ E)) {s₀ : ℝ} {y₀ : E} (hs : s₀ ∈ S)
    (hy : y₀ ∈ interior (extChartAt I α).target) :
    ContDiffAt ℝ ∞
      (fun r : ℝ × E => chartRicciTensor (I := I) (gfam r.1) α i k r.2) (s₀, y₀) := by
  have heq : (fun r : ℝ × E => chartRicciTensor (I := I) (gfam r.1) α i k r.2) =
      (fun r : ℝ × E => ∑ j : Fin (Module.finrank ℝ E),
        chartRiemannTensor (I := I) (gfam r.1) α i j k j r.2) := by
    funext r; rw [chartRicciTensor_def]
  rw [heq]
  exact ContDiffAt.sum (fun j _ => gen_joint_riemann (I := I) gfam α hG i j k j hs hy)

/-! ### The keystone: GenJointGram for the realized open family -/

/-- The open `s`-set where the abs-convex smallness holds. -/
def realizedSmallSet {δ δ' : ℝ} : Set ℝ := {s : ℝ | |1 - s| * δ' + |s| * δ < 1}

theorem realizedSmallSet_isOpen {δ δ' : ℝ} :
    IsOpen (realizedSmallSet (δ := δ) (δ' := δ')) := by
  have hcont : Continuous (fun s : ℝ => |1 - s| * δ' + |s| * δ) := by fun_prop
  exact isOpen_lt hcont continuous_const

theorem Icc_subset_realizedSmallSet {δ δ' : ℝ} (hδ_lt : δ < 1) (hδ'_lt : δ' < 1) :
    Set.Icc (0:ℝ) 1 ⊆ realizedSmallSet (δ := δ) (δ' := δ') :=
  fun _ hs => abs_convex_smallConstant_lt_one hδ_lt hδ'_lt hs

/-- The total realized family (junk-extended off the small set by `g₀`). -/
def realizedFam (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (s : ℝ) : SmoothRiemannianMetric I M :=
  if h : |1 - s| * δ' + |s| * δ < 1 then
    realizedMetricPathOpen (I := I) g₀ T T' hδ hδ' s h
  else g₀

theorem realizedFam_inner_of_mem (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    {s : ℝ} (hs : s ∈ realizedSmallSet (δ := δ) (δ' := δ')) (x : M) (v w : TangentSpace I x) :
    (realizedFam (I := I) g₀ T T' hδ hδ' s).inner x v w =
      g₀.inner x v w +
        ccTensorBilinSymm (I := I) g₀ (convexPerturbation (I := I) g₀ T T' s) x v w := by
  rw [realizedFam, dif_pos (Set.mem_setOf.mp hs), realizedMetricPathOpen_inner]

/-- On the small set the realized-family chart Gram is the convex combination of the two
endpoint realized-metric chart Grams. -/
theorem realizedFam_chartGramOnE (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    {s : ℝ} (hs : s ∈ realizedSmallSet (δ := δ) (δ' := δ'))
    (α : M) (i j : Fin (Module.finrank ℝ E)) (y : E) :
    chartGramOnE (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) α i j y =
      (1 - s) *
          chartGramOnE (I := I) (tensorSectionRealizeMetric (I := I) g₀ T' hδ'_lt hδ') α i j y +
        s * chartGramOnE (I := I) (tensorSectionRealizeMetric (I := I) g₀ T hδ_lt hδ) α i j y := by
  rw [chartGramOnE_def, chartGramOnE_def, chartGramOnE_def, chartGramMatrix_apply,
    chartGramMatrix_apply, chartGramMatrix_apply,
    realizedFam_inner_of_mem (I := I) g₀ T T' hδ hδ' hs,
    tensorSectionRealizeMetric_inner, tensorSectionRealizeMetric_inner,
    ccTensorBilinSymm_convexPerturbation]
  ring

theorem realizedFam_genJointGram (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (α : M) :
    GenJointGram (I := I) (realizedFam (I := I) g₀ T T' hδ hδ') α
      (realizedSmallSet (δ := δ) (δ' := δ')) := by
  refine ⟨?_, ?_⟩
  · intro i j s₀ y₀ hs hy
    have hSopen : IsOpen (realizedSmallSet (δ := δ) (δ' := δ')) := realizedSmallSet_isOpen
    set F : E → ℝ :=
      chartGramOnE (I := I) (tensorSectionRealizeMetric (I := I) g₀ T' hδ'_lt hδ') α i j with hF
    set G : E → ℝ :=
      chartGramOnE (I := I) (tensorSectionRealizeMetric (I := I) g₀ T hδ_lt hδ) α i j with hG
    have heq : (fun p : ℝ × E =>
          chartGramOnE (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' p.1) α i j p.2)
        =ᶠ[nhds (s₀, y₀)] (fun p : ℝ × E => (1 - p.1) * F p.2 + p.1 * G p.2) := by
      have hmem : (realizedSmallSet (δ := δ) (δ' := δ')) ×ˢ (Set.univ : Set E) ∈ nhds (s₀, y₀) :=
        (hSopen.prod isOpen_univ).mem_nhds ⟨hs, Set.mem_univ _⟩
      filter_upwards [hmem] with p hp
      exact realizedFam_chartGramOnE (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' hp.1 α i j p.2
    refine ContDiffAt.congr_of_eventuallyEq ?_ heq
    have hFc : ContDiffAt ℝ ∞ (fun p : ℝ × E => F p.2) (s₀, y₀) :=
      (((chartGramOnE_contDiffOn (I := I) _ α i j).mono interior_subset).contDiffAt
        (isOpen_interior.mem_nhds hy)).comp (s₀, y₀) contDiffAt_snd
    have hGc : ContDiffAt ℝ ∞ (fun p : ℝ × E => G p.2) (s₀, y₀) :=
      (((chartGramOnE_contDiffOn (I := I) _ α i j).mono interior_subset).contDiffAt
        (isOpen_interior.mem_nhds hy)).comp (s₀, y₀) contDiffAt_snd
    exact ((contDiffAt_const.sub contDiffAt_fst).mul hFc).add (contDiffAt_fst.mul hGc)
  · intro s₀ _ x hx
    exact chartGramMatrix_det_pos (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s₀) α hx

/-! ### s-slice smoothness of the chart Ricci along the realized family -/

/-- The s-slice of the joint chart-Ricci smoothness: `s ↦ chartRicciTensor (gfam s) α i k y₀`
is `ContDiffAt ℝ ∞` at every `s₀ ∈ S` (chart-interior `y₀`). -/
private lemma gen_s_contDiffAt_ricci (gfam : ℝ → SmoothRiemannianMetric I M) (α : M)
    {S : Set ℝ} (hG : GenJointGram (I := I) gfam α S)
    (i k : Fin (Module.finrank ℝ E)) {s₀ : ℝ} {y₀ : E} (hs : s₀ ∈ S)
    (hy : y₀ ∈ interior (extChartAt I α).target) :
    ContDiffAt ℝ ∞ (fun s : ℝ => chartRicciTensor (I := I) (gfam s) α i k y₀) s₀ := by
  have hjoint := gen_joint_ricci (I := I) gfam α hG i k hs hy
  have hcomp : (fun s : ℝ => chartRicciTensor (I := I) (gfam s) α i k y₀) =
      (fun p : ℝ × E => chartRicciTensor (I := I) (gfam p.1) α i k p.2) ∘
        (fun s : ℝ => (s, y₀)) := by funext s; rfl
  rw [hcomp]
  exact hjoint.comp s₀ ((contDiffAt_id).prodMk contDiffAt_const)

/-- For `s` in the small set, the realized family metric equals the genuine realized metric
path metric (same fibre inner product). -/
theorem realizedMetricPath_eq_realizedFam (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (hmem : s ∈ realizedSmallSet (δ := δ) (δ' := δ')) :
    realizedMetricPath (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' hs0 hs1 =
      realizedFam (I := I) g₀ T T' hδ hδ' s := by
  refine riemannianMetric_eq_of_inner _ _ (fun b u z => ?_)
  rw [realizedMetricPath_inner, realizedFam_inner_of_mem (I := I) g₀ T T' hδ hδ' hmem]

/-! ### The realized Ricci value as a chart sum + differentiability -/

/-- The chart-sum form of the realized Ricci path value (valid on the small set, off the
clamp), as a `C^∞`-in-`s` scalar function. -/
def realizedRicciChartSum (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (v w : TangentSpace I x) (s : ℝ) : ℝ :=
  ∑ i, ∑ k,
    ((chartModelBasis E).repr v) k * ((chartModelBasis E).repr w) i *
      chartRicciTensor (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x i k
        (extChartAt I x x)

theorem realizedRicciChartSum_contDiffAt (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (v w : TangentSpace I x) {s₀ : ℝ}
    (hs : s₀ ∈ realizedSmallSet (δ := δ) (δ' := δ')) :
    ContDiffAt ℝ ∞ (realizedRicciChartSum (I := I) g₀ T T' hδ hδ' x v w) s₀ := by
  have hG := realizedFam_genJointGram (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x
  have hy : (extChartAt I x x) ∈ interior (extChartAt I x).target :=
    extChartAt_target_subset_interior_of_boundaryless (I := I) x (mem_extChartAt_target x)
  unfold realizedRicciChartSum
  refine ContDiffAt.sum (fun i _ => ContDiffAt.sum (fun k _ => ?_))
  exact contDiffAt_const.mul (gen_s_contDiffAt_ricci (I := I) _ x hG i k hs hy)

/-- On `Icc 0 1`, the (clamped) realized Ricci path value equals the chart-sum form. -/
theorem realizedRicciPathValue_eq_chartSum_on_Icc (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (v w : TangentSpace I x) {s : ℝ} (hs : s ∈ Set.Icc (0:ℝ) 1) :
    realizedRicciPathValue (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x v w s =
      realizedRicciChartSum (I := I) g₀ T T' hδ hδ' x v w s := by
  obtain ⟨h0, h1⟩ := hs
  have hmem : s ∈ realizedSmallSet (δ := δ) (δ' := δ') :=
    abs_convex_smallConstant_lt_one hδ_lt hδ'_lt ⟨h0, h1⟩
  have hclamp : max 0 (min s 1) = s := by rw [min_eq_left h1, max_eq_right h0]
  rw [realizedRicciPathValue]
  have hmetric :
      realizedMetricPath (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ'
          (le_max_left 0 (min s 1))
          (max_le (zero_le_one) (le_trans (min_le_right s 1) (le_refl 1))) =
        realizedFam (I := I) g₀ T T' hδ hδ' s := by
    refine riemannianMetric_eq_of_inner _ _ (fun b u z => ?_)
    rw [realizedMetricPath_inner, realizedFam_inner_of_mem (I := I) g₀ T T' hδ hδ' hmem,
      hclamp]
  rw [hmetric]
  -- now intrinsic Ricci = chart sum via the bridge
  rw [realizedRicciChartSum]
  exact ricciTensor_eq_chartRicciSwap_of_basis_identity (I := I)
    (realizedFam (I := I) g₀ T T' hδ hδ' s) x
    (chartRiemannBasisIdentity_holds (I := I) _ x) v w

/-! ### Differentiability and integrability, closing the FTC child -/

/-- `realizedRicciPathValue` is differentiable at every `s₀ ∈ Ioo 0 1`. -/
theorem realizedRicciPathValue_differentiableAt_Ioo (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (v w : TangentSpace I x) {s₀ : ℝ} (hs₀ : s₀ ∈ Set.Ioo (0:ℝ) 1) :
    DifferentiableAt ℝ
      (realizedRicciPathValue (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x v w) s₀ := by
  have heq : realizedRicciPathValue (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x v w
      =ᶠ[nhds s₀] realizedRicciChartSum (I := I) g₀ T T' hδ hδ' x v w := by
    filter_upwards [isOpen_Ioo.mem_nhds hs₀] with s hs
    exact realizedRicciPathValue_eq_chartSum_on_Icc (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x v w
      (Set.mem_Icc_of_Ioo hs)
  have hmem : s₀ ∈ realizedSmallSet (δ := δ) (δ' := δ') :=
    abs_convex_smallConstant_lt_one hδ_lt hδ'_lt ⟨hs₀.1.le, hs₀.2.le⟩
  exact ((realizedRicciChartSum_contDiffAt (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x v w
    hmem).differentiableAt (by simp)).congr_of_eventuallyEq heq

/-- On `Ioo 0 1`, the linearized Ricci integrand equals the derivative of the chart-sum. -/
theorem linearizedRicciAt_eq_deriv_chartSum_on_Ioo (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (v w : TangentSpace I x) {s : ℝ} (hs : s ∈ Set.Ioo (0:ℝ) 1) :
    linearizedRicciAt (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x v w s =
      deriv (realizedRicciChartSum (I := I) g₀ T T' hδ hδ' x v w) s := by
  have heq : realizedRicciPathValue (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x v w
      =ᶠ[nhds s] realizedRicciChartSum (I := I) g₀ T T' hδ hδ' x v w := by
    filter_upwards [isOpen_Ioo.mem_nhds hs] with t ht
    exact realizedRicciPathValue_eq_chartSum_on_Icc (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x v w
      (Set.mem_Icc_of_Ioo ht)
  rw [linearizedRicciAt]
  exact Filter.EventuallyEq.deriv_eq heq

/-- The derivative of the chart-sum is continuous on the open small set. -/
theorem deriv_realizedRicciChartSum_continuousOn (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (v w : TangentSpace I x) :
    ContinuousOn (deriv (realizedRicciChartSum (I := I) g₀ T T' hδ hδ' x v w))
      (realizedSmallSet (δ := δ) (δ' := δ')) := by
  have hcd : ContDiffOn ℝ ∞ (realizedRicciChartSum (I := I) g₀ T T' hδ hδ' x v w)
      (realizedSmallSet (δ := δ) (δ' := δ')) := fun s hs =>
    (realizedRicciChartSum_contDiffAt (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x v w
      hs).contDiffWithinAt
  exact hcd.continuousOn_deriv_of_isOpen realizedSmallSet_isOpen (by exact_mod_cast le_top)

/-- The linearized Ricci integrand is interval-integrable on `[0,1]`. -/
theorem linearizedRicciAt_intervalIntegrable (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (v w : TangentSpace I x) :
    IntervalIntegrable
      (linearizedRicciAt (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x v w)
      MeasureTheory.volume 0 1 := by
  -- the chart-sum derivative is interval-integrable (continuous on Icc 0 1)
  have hcont : ContinuousOn (deriv (realizedRicciChartSum (I := I) g₀ T T' hδ hδ' x v w))
      (Set.Icc (0:ℝ) 1) :=
    (deriv_realizedRicciChartSum_continuousOn (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x v w).mono
      (Icc_subset_realizedSmallSet hδ_lt hδ'_lt)
  have hii : IntervalIntegrable
      (deriv (realizedRicciChartSum (I := I) g₀ T T' hδ hδ' x v w))
      MeasureTheory.volume 0 1 :=
    hcont.intervalIntegrable_of_Icc zero_le_one
  -- swap to linearizedRicciAt: they agree a.e. on Ι 0 1 = Ioc 0 1 (differ only at {1})
  refine hii.congr_ae ?_
  have hsub : Set.Ioo (0:ℝ) 1 ⊆
      {s | deriv (realizedRicciChartSum (I := I) g₀ T T' hδ hδ' x v w) s =
        linearizedRicciAt (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x v w s} := by
    intro s hs
    exact (linearizedRicciAt_eq_deriv_chartSum_on_Ioo (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x v w
      hs).symm
  have hnull : (MeasureTheory.volume.restrict (Set.uIoc (0:ℝ) 1)) (Set.Ioo (0:ℝ) 1)ᶜ = 0 := by
    rw [Set.uIoc_of_le zero_le_one]
    rw [MeasureTheory.Measure.restrict_apply (measurableSet_Ioo.compl)]
    have hsub1 : (Set.Ioo (0:ℝ) 1)ᶜ ∩ Set.Ioc 0 1 ⊆ {1} := by
      intro t ht
      obtain ⟨htc, ht0, ht1⟩ := ht
      rw [Set.mem_compl_iff, Set.mem_Ioo, not_and_or, not_lt, not_lt] at htc
      rcases htc with h | h
      · exact absurd ht0 (not_lt.mpr h)
      · exact (le_antisymm ht1 h) ▸ rfl
    exact MeasureTheory.measure_mono_null hsub1 (by simp)
  refine MeasureTheory.measure_mono_null (fun s hs => ?_) hnull
  exact fun hs' => hs (hsub hs')

/-- `realizedRicciPathValue` is continuous on `Icc 0 1`. -/
theorem realizedRicciPathValue_continuousOn_Icc (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (v w : TangentSpace I x) :
    ContinuousOn (realizedRicciPathValue (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x v w)
      (Set.Icc (0:ℝ) 1) := by
  refine ContinuousOn.congr
    (f := realizedRicciChartSum (I := I) g₀ T T' hδ hδ' x v w) ?_ ?_
  · exact fun s hs =>
      (realizedRicciChartSum_contDiffAt (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x v w
        (Icc_subset_realizedSmallSet hδ_lt hδ'_lt hs)).continuousAt.continuousWithinAt
  · intro s hs
    exact realizedRicciPathValue_eq_chartSum_on_Icc (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ'
      x v w hs


/-- **The path `s`-derivative of the realized Ricci tensor.**

For the realized metric path `g_s = realize(g₀, (1 - s)·T' + s·T)` joining `realize(g₀, T')`
to `realize(g₀, T)`, the scalar `s ↦ Ric(g_s)_x(v, w)` has, at every interior parameter
`s₀ ∈ (0,1)`, the derivative `linearizedRicciAt g_s (T - T')_x(v, w)` (the linearized Ricci
operator at the path metric in the perturbation direction), and the derivative is
interval-integrable on `[0,1]`.

The interior parameter range `(0,1)` (rather than the closed `[0,1]`) is forced by the
endpoint clamp in `realizedRicciPathValue`: outside `[0,1]` the value is constant in `s`, so
the clamped scalar is only one-sided differentiable at the endpoints; the genuine `s`-derivative
extends continuously to `[0,1]` and the FTC reduction uses the open-interval form
`integral_eq_sub_of_hasDerivAt_of_le` together with continuity on `[0,1]`
(`realizedRicciPathValue_continuousOn_Icc`).

This is the **mean-value content**: via the intrinsic↔chart Ricci bridge
(`ricciTensor_eq_chartRicciSwap_of_basis_identity`) the path Ricci value equals a fixed linear
combination of chart Ricci tensors of the path metric, and the realized chart Gram is affine
in `s` × smooth in `y`, so the joint `(s,y)`-smoothness of the whole chart Christoffel→Riemann
polynomial (`realizedRicciChartSum_contDiffAt`) makes `s ↦ Ric(g_s)_x(v, w)` `C^∞` in `s` on a
neighbourhood of `[0,1]`, hence differentiable with continuous (integrable) derivative. -/
theorem hasDerivAt_ricciTensor_realizedMetricPath (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (v w : TangentSpace I x) :
    (∀ s₀ ∈ Set.Ioo (0 : ℝ) 1,
        HasDerivAt
          (realizedRicciPathValue (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x v w)
          (linearizedRicciAt (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x v w s₀) s₀) ∧
      IntervalIntegrable
        (linearizedRicciAt (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x v w)
        MeasureTheory.volume 0 1 := by
  refine ⟨fun s₀ hs₀ => ?_, ?_⟩
  · rw [linearizedRicciAt]
    exact (realizedRicciPathValue_differentiableAt_Ioo (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ'
      x v w hs₀).hasDerivAt
  · exact linearizedRicciAt_intervalIntegrable (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x v w

/-- **The mean-value (FTC) reduction of the realized Ricci-arm difference.**

For two endpoint perturbation tensor sections `T, T' : SmoothCcTensor g₀ 0 2`, both
`g₀`-fibre small with constant `< 1`, the difference of the two realized Ricci tensors
equals the integral over `[0,1]` of the linearized Ricci operator along the straight-line
metric path joining `realize(g₀, T')` to `realize(g₀, T)`, applied to the perturbation
velocity `T - T'`:
$$\operatorname{Ric}(g_1)_x(v, w) - \operatorname{Ric}(g_1')_x(v, w)
    = \int_0^1 \bigl(D\!\operatorname{Ric}\bigr)_{g_s}[T - T']_x(v, w)\, ds.$$

This is the mean-value foundation that the Ricci-arm rebuild consumes in place of the
single-endpoint Palatini telescope: the difference is recovered as the integral of the
genuine metric-derivative (linearized Ricci) along a path, with no two-endpoint cross
terms. -/
theorem ricciTensor_realized_sub_eq_integral_linearizedRicci
    (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (v w : TangentSpace I x) :
    ricciTensor (I := I) (tensorSectionRealizeMetric (I := I) g₀ T hδ_lt hδ) x v w -
        ricciTensor (I := I) (tensorSectionRealizeMetric (I := I) g₀ T' hδ'_lt hδ') x v w =
      ∫ s in (0 : ℝ)..1,
        linearizedRicciAt (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x v w s := by
  obtain ⟨hderiv, hint⟩ :=
    hasDerivAt_ricciTensor_realizedMetricPath (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x v w
  have hcont := realizedRicciPathValue_continuousOn_Icc (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x v w
  have hFTC :
      ∫ s in (0 : ℝ)..1,
          linearizedRicciAt (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x v w s =
        realizedRicciPathValue (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x v w 1 -
          realizedRicciPathValue (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x v w 0 :=
    integral_eq_sub_of_hasDerivAt_of_le zero_le_one hcont hderiv hint
  rw [hFTC, realizedRicciPathValue_one, realizedRicciPathValue_zero]

end RicciLinearization
end DeTurck
end PDE
end DifferentialGeometry
