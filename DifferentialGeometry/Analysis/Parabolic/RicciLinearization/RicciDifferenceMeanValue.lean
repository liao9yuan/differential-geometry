import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.TensorHsRealize
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.RicciConnection
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

open Set Function MeasureTheory intervalIntegral Bundle Tensor0SBundle
open scoped Topology Manifold BigOperators ContDiff

namespace DifferentialGeometry
namespace PDE
namespace DeTurck
namespace RicciLinearization

open DifferentialGeometry
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization

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

/-- **The path `s`-derivative of the realized Ricci tensor (posited mean-value child).**

For the realized metric path `g_s = realize(g₀, (1 - s)·T' + s·T)` joining `realize(g₀, T')`
to `realize(g₀, T)`, the scalar `s ↦ Ric(g_s)_x(v, w)` has, at every `s₀ ∈ [0,1]`, the
derivative `linearizedRicciAt g_s (T - T')_x(v, w)` (the linearized Ricci operator at the
path metric in the perturbation direction), and the derivative is interval-integrable on
`[0,1]`.

This packages the **deep mean-value content**: the metric-derivative of the Ricci-tensor
curvature functional along the realized path equals the linearized Ricci operator, plus the
regularity (continuity / integrability) of that derivative along the path.  It is the
analytic heart that the chart Ricci-linearization tower (`chartRicciSecondOrderPart`,
`chartRicciFirstOrderRemainder`, `hasDerivAt_chartRicciTensor`) supplies at `s = 0` and that
the re-anchored path supplies at general `s₀`; producing it requires the intrinsic↔chart
Ricci bridge (`ricciTensor_eq_chartRicciSwap_of_basis_identity`) at each path metric, the
re-anchoring of the chart linearization at `g_{s₀}`, and the smoothness of the realized
chart Gram in `(s, y)`.  It is posited here as a precise child to be discharged by recursing
into those covariant/chart bridges. -/
theorem hasDerivAt_ricciTensor_realizedMetricPath (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (v w : TangentSpace I x) :
    (∀ s₀ ∈ Set.Icc (0 : ℝ) 1,
        HasDerivAt
          (realizedRicciPathValue (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x v w)
          (linearizedRicciAt (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x v w s₀) s₀) ∧
      IntervalIntegrable
        (linearizedRicciAt (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x v w)
        MeasureTheory.volume 0 1 := by
  sorry

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
  have hFTC :
      ∫ s in (0 : ℝ)..1,
          linearizedRicciAt (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x v w s =
        realizedRicciPathValue (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x v w 1 -
          realizedRicciPathValue (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x v w 0 := by
    refine integral_eq_sub_of_hasDerivAt (fun s hs => ?_) hint
    exact hderiv s (by rwa [Set.uIcc_of_le (zero_le_one)] at hs)
  rw [hFTC, realizedRicciPathValue_one, realizedRicciPathValue_zero]

end RicciLinearization
end DeTurck
end PDE
end DifferentialGeometry
