import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import RicciFlower.HCGCompactness.BoundedGeometry
import RicciFlower.HCGCompactness.PointedConvergence

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Bounds Propagated From One Time

This file starts the MSM135 Chapter 3 "convergence at all times from
convergence at one time" layer.  The definitions here are fixed-domain
predicates, intended for the pulled-back metrics on a common source domain.

Raw bound predicates are stated on an arbitrary set `K`.  Compactness of `K`
is required only by the final theorem-facing input package, because compactness
is used by the analytic propagation theorem rather than by the pointwise
meaning of the inequalities.
-/

noncomputable section

universe u uE uH

namespace RicciFlower
namespace HCGCompactness

open scoped Manifold ContDiff

section ScalarLogDerivative

/-- Convert a bound on the change of logarithms into two-sided exponential
ratio bounds for positive scalars. -/
theorem exp_bounds_of_abs_log_sub_le
    {fa fb R : Real}
    (hfa : 0 < fa) (hfb : 0 < fb)
    (hlog : |Real.log fb - Real.log fa| <= R) :
    Real.exp (-R) * fa <= fb /\ fb <= Real.exp R * fa := by
  have hlow : -R <= Real.log fb - Real.log fa := (abs_le.mp hlog).1
  have hhigh : Real.log fb - Real.log fa <= R := (abs_le.mp hlog).2
  have hratio_pos : 0 < fb / fa := div_pos hfb hfa
  constructor
  · have hlog_ratio : -R <= Real.log (fb / fa) := by
      simpa [Real.log_div hfb.ne' hfa.ne'] using hlow
    have hratio_lower : Real.exp (-R) <= fb / fa :=
      (Real.le_log_iff_exp_le hratio_pos).mp hlog_ratio
    calc
      Real.exp (-R) * fa <= (fb / fa) * fa :=
        mul_le_mul_of_nonneg_right hratio_lower (le_of_lt hfa)
      _ = fb := by
        field_simp [hfa.ne']
  · have hlog_ratio : Real.log (fb / fa) <= R := by
      simpa [Real.log_div hfb.ne' hfa.ne'] using hhigh
    have hratio_upper : fb / fa <= Real.exp R :=
      (Real.log_le_iff_le_exp hratio_pos).mp hlog_ratio
    calc
      fb = (fb / fa) * fa := by
        field_simp [hfa.ne']
      _ <= Real.exp R * fa :=
        mul_le_mul_of_nonneg_right hratio_upper (le_of_lt hfa)

/-- Scalar logarithmic-derivative estimate used in MSM135 Lemma 3.11.  If
`|f' / f| <= Lambda` along the interval and `f` stays positive, then the values
of `f` at the endpoints differ by at most the exponential factor
`exp (Lambda * |b - a|)`. -/
theorem exp_bounds_of_log_deriv_bound
    (f f' : Real -> Real) {a b Lambda : Real}
    (hf_pos : forall s : Real, s ∈ Set.uIcc a b -> 0 < f s)
    (hf_deriv :
      forall s : Real, s ∈ Set.uIcc a b -> HasDerivAt f (f' s) s)
    (hbound :
      forall s : Real, s ∈ Set.uIcc a b -> |f' s / f s| <= Lambda) :
    Real.exp (-Lambda * |b - a|) * f a <= f b /\
      f b <= Real.exp (Lambda * |b - a|) * f a := by
  have hlog_deriv :
      forall s : Real, s ∈ Set.uIcc a b ->
        HasDerivWithinAt (fun y : Real => Real.log (f y)) (f' s / f s)
          (Set.uIcc a b) s := by
    intro s hs
    exact ((hf_deriv s hs).log (ne_of_gt (hf_pos s hs))).hasDerivWithinAt
  have hnorm_bound :
      forall s : Real, s ∈ Set.uIcc a b -> ‖f' s / f s‖ <= Lambda := by
    intro s hs
    simpa only [Real.norm_eq_abs] using hbound s hs
  have hdist :=
    (convex_uIcc a b).norm_image_sub_le_of_norm_hasDerivWithin_le
      hlog_deriv hnorm_bound Set.left_mem_uIcc Set.right_mem_uIcc
  have hlog :
      |Real.log (f b) - Real.log (f a)| <= Lambda * |b - a| := by
    simpa [Real.norm_eq_abs] using hdist
  simpa [neg_mul] using
    exp_bounds_of_abs_log_sub_le (hf_pos a Set.left_mem_uIcc)
      (hf_pos b Set.right_mem_uIcc) hlog

/-- Vector-valued endpoint estimate used in the Christoffel part of MSM135
Lemma 3.11: a uniform derivative bound on the interval controls the change
from the initial time. -/
theorem norm_le_initial_add_deriv_bound
    {F : Type*} [NormedAddCommGroup F] [NormedSpace Real F]
    (f f' : Real -> F) {a b L : Real}
    (hf_deriv :
      forall s : Real, s ∈ Set.uIcc a b -> HasDerivAt f (f' s) s)
    (hbound :
      forall s : Real, s ∈ Set.uIcc a b -> ‖f' s‖ <= L) :
    ‖f b‖ <= L * |b - a| + ‖f a‖ := by
  have hderivWithin :
      forall s : Real, s ∈ Set.uIcc a b ->
        HasDerivWithinAt f (f' s) (Set.uIcc a b) s := by
    intro s hs
    exact (hf_deriv s hs).hasDerivWithinAt
  have hdist :=
    (convex_uIcc a b).norm_image_sub_le_of_norm_hasDerivWithin_le
      hderivWithin hbound Set.left_mem_uIcc Set.right_mem_uIcc
  have hsub : ‖f b - f a‖ <= L * |b - a| := by
    simpa [Real.norm_eq_abs] using hdist
  calc
    ‖f b‖ = ‖(f b - f a) + f a‖ := by rw [sub_add_cancel]
    _ <= ‖f b - f a‖ + ‖f a‖ := norm_add_le _ _
    _ <= L * |b - a| + ‖f a‖ := by
      simpa [add_comm, add_left_comm, add_assoc] using
        add_le_add_right hsub ‖f a‖

end ScalarLogDerivative

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [Module.Finite Real E] [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}

section FixedDomain

variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
variable [T2Space M] [IsManifold I ∞ M] [SigmaCompactSpace M]

/-- Uniform equivalence of two metrics on a set `K`.

This is the raw pointwise inequality.  Compactness of `K` is deliberately not
part of this definition; theorem-facing packages add it when MSM135 uses a
compact set. -/
def MetricUniformEquivalentOn
    (K : Set M)
    (gRef h : SmoothRiemannianMetric I M)
    (C : Real) : Prop :=
  1 <= C /\
    forall x : M, x ∈ K ->
      forall v : TangentSpace I x,
        C⁻¹ * gRef.inner x v v <= h.inner x v v /\
          h.inner x v v <= C * gRef.inner x v v

/-- Uniform equivalence on a fixed time window for a sequence of metrics. -/
def MetricUniformEquivalentOnWindow
    (K : Set M) (β ψ : Real)
    (gRef : SmoothRiemannianMetric I M)
    (gSeq : Nat -> Real -> SmoothRiemannianMetric I M)
    (B : Real -> Real) : Prop :=
  forall i : Nat, forall t : Real, t ∈ Set.Icc β ψ ->
    MetricUniformEquivalentOn (I := I) K gRef (gSeq i t) (B t)

/-- The exponential factor appearing in MSM135 Lemma 3.11, equation (3.3),
once a Ricci quadratic bound with coefficient `A` is available. -/
def metricEquivalenceFactor (C A t t0 : Real) : Real :=
  C * Real.exp (2 * A * |t - t0|)

/-- Pointwise norm `|nabla^a h|_g` for a single metric tensor `h`, with
covariant derivatives and tensor norm taken using the background metric
`gRef`. -/
noncomputable def metricCovDerivNorm
    (a : Nat) (h gRef : SmoothRiemannianMetric I M) (x : M) : Real :=
  Real.sqrt
    (Tensor0SBundle.normSq0S (I := I) gRef x (a + 2)
      (metricCovDeriv (I := I) h gRef a x))

/-- Raw supremum of `|nabla^a h|_g` over `a <= p` and `x in K`.

This is a low-level supremum, analogous to `metricDerivNormSupOn`; callers
should use it through theorem-facing packages that supply compactness and
boundedness hypotheses. -/
noncomputable def metricCovDerivNormSupOn
    (K : Set M) (p : Nat)
    (h gRef : SmoothRiemannianMetric I M) : Real :=
  sSup {r : Real |
    exists a : Nat, a <= p ∧
      exists x : M, x ∈ K ∧
        metricCovDerivNorm (I := I) a h gRef x = r}

/-- Bound on the fixed-background covariant derivatives of one metric on `K`.
This raw bound predicate does not assume `K` is compact. -/
def MetricCovDerivBoundOn
    (K : Set M) (p : Nat)
    (h gRef : SmoothRiemannianMetric I M)
    (C : Real) : Prop :=
  metricCovDerivNormSupOn (I := I) K p h gRef <= C

/-- Bounds on all fixed-background covariant metric derivatives for a sequence
at one time.  The MSM135 hypothesis only uses positive derivative orders, so
the order condition is explicit. -/
def MetricCovDerivBoundsAtTimeOn
    (K : Set M) (t0 : Real)
    (gSeq : Nat -> Real -> SmoothRiemannianMetric I M)
    (gRef : SmoothRiemannianMetric I M)
    (C : Nat -> Real) : Prop :=
  forall i p : Nat, 0 < p ->
    MetricCovDerivBoundOn (I := I) K p (gSeq i t0) gRef (C p)

/-- Bounds on all fixed-background covariant metric derivatives throughout a
time window. -/
def MetricCovDerivBoundsOnWindow
    (K : Set M) (β ψ : Real)
    (gSeq : Nat -> Real -> SmoothRiemannianMetric I M)
    (gRef : SmoothRiemannianMetric I M)
    (C : Nat -> Real) : Prop :=
  forall i : Nat, forall t : Real, t ∈ Set.Icc β ψ ->
    forall p : Nat, MetricCovDerivBoundOn (I := I) K p (gSeq i t) gRef (C p)

/-- Bound on `|nabla^p Rm(h)|_h` over `K`, using the Levi-Civita connection and
norm of the metric `h`. -/
def CurvDerivBoundOn
    (K : Set M) (p : Nat)
    (h : SmoothRiemannianMetric I M)
    (C : Real) : Prop :=
  forall x : M, x ∈ K -> curvDerivNorm (I := I) p h x <= C

/-- Compact-window curvature-derivative bounds for a sequence of metrics.
This raw predicate does not itself require `K` to be compact. -/
def CurvDerivBoundOnWindow
    (K : Set M) (β ψ : Real)
    (gSeq : Nat -> Real -> SmoothRiemannianMetric I M)
    (p : Nat) (C : Real) : Prop :=
  forall i : Nat, forall t : Real, t ∈ Set.Icc β ψ ->
    CurvDerivBoundOn (I := I) K p (gSeq i t) C

/-- Curvature-derivative bounds of every spatial order on a time window. -/
def CurvDerivBoundsOnWindow
    (K : Set M) (β ψ : Real)
    (gSeq : Nat -> Real -> SmoothRiemannianMetric I M)
    (C : Nat -> Real) : Prop :=
  forall p : Nat, CurvDerivBoundOnWindow (I := I) K β ψ gSeq p (C p)

/-- A concrete quadratic bound for a family of two-tensors against a metric
family on a time window.  For Ricci flow, the tensor family will be `Rc(g_i(t))`
and this is the input needed for the metric-equivalence part of Lemma 3.11. -/
def TwoTensorQuadBoundOnWindow
    (K : Set M) (β ψ : Real)
    (gSeq : Nat -> Real -> SmoothRiemannianMetric I M)
    (T :
      forall _i : Nat, Real -> forall x : M,
        Tensor0SBundle.Tensor0SSpace (𝕜 := Real) (E := E) (H := H)
          (I := I) (M := M) 2 x)
    (A : Real) : Prop :=
  0 <= A /\
    forall i : Nat, forall t : Real, t ∈ Set.Icc β ψ ->
      forall x : M, x ∈ K ->
        forall v : TangentSpace I x,
          |T i t x (Realized.vec2 (I := I) v v)| <=
            A * (gSeq i t).inner x v v

/-- Concrete logarithmic-derivative input for the metric-equivalence part of
MSM135 Lemma 3.11.

For Ricci flow, `T i t` is the Ricci tensor of `g_i(t)`, and the metric
derivative field records
`d/dt g_i(t)(v,v) = -2 T_i(t)(v,v)`.  The integrability field records the
textbook integral route; the current proof below uses the equivalent mean-value
form of the same logarithmic-derivative estimate. -/
structure MetricLogDerivativeInput
    (K : Set M) (β ψ t0 : Real)
    (gSeq : Nat -> Real -> SmoothRiemannianMetric I M)
    (T :
      forall _i : Nat, Real -> forall x : M,
        Tensor0SBundle.Tensor0SSpace (𝕜 := Real) (E := E) (H := H)
          (I := I) (M := M) 2 x)
    (A : Real) : Prop where
  quad_bound : TwoTensorQuadBoundOnWindow (I := I) K β ψ gSeq T A
  metric_deriv :
    forall i : Nat, forall x : M, x ∈ K ->
      forall v : TangentSpace I x, v ≠ 0 ->
        forall t : Real, t ∈ Set.Icc β ψ ->
          HasDerivAt
            (fun s : Real => (gSeq i s).inner x v v)
            ((-2 : Real) * T i t x (Realized.vec2 (I := I) v v))
            t
  log_integrable :
    forall i : Nat, forall x : M, x ∈ K ->
      forall v : TangentSpace I x, v ≠ 0 ->
        forall t : Real, t ∈ Set.Icc β ψ ->
          IntervalIntegrable
            (fun s : Real =>
              ((-2 : Real) * T i s x (Realized.vec2 (I := I) v v)) /
                (gSeq i s).inner x v v)
            MeasureTheory.volume t0 t

private theorem metric_factor_one_le
    {C A t t0 : Real}
    (hC : 1 <= C) (hA : 0 <= A) :
    1 <= metricEquivalenceFactor C A t t0 := by
  have harg_nonneg : 0 <= 2 * A * |t - t0| := by
    nlinarith [hA, abs_nonneg (t - t0)]
  have hexp : 1 <= Real.exp (2 * A * |t - t0|) :=
    Real.one_le_exp harg_nonneg
  have hprod : 0 <= (C - 1) * (Real.exp (2 * A * |t - t0|) - 1) :=
    mul_nonneg (sub_nonneg.mpr hC) (sub_nonneg.mpr hexp)
  rw [metricEquivalenceFactor]
  nlinarith

private theorem metric_factor_inv_mul
    {C A t t0 g : Real}
    (hC : 1 <= C) :
    (metricEquivalenceFactor C A t t0)⁻¹ * g =
      Real.exp (-(2 * A) * |t - t0|) * (C⁻¹ * g) := by
  have hCne : C ≠ 0 := by nlinarith
  rw [metricEquivalenceFactor,
    show -(2 * A) * |t - t0| = -(2 * A * |t - t0|) by ring,
    Real.exp_neg]
  field_simp [hCne, Real.exp_ne_zero]

private theorem metric_factor_mul
    {C A t t0 g : Real} :
    Real.exp ((2 * A) * |t - t0|) * (C * g) =
      metricEquivalenceFactor C A t t0 * g := by
  rw [metricEquivalenceFactor]
  ring

/-- MSM135 Lemma 3.11, equation (3.3): a logarithmic derivative bound for
the fixed-vector metric quadratic form propagates metric equivalence from
`t0` to the whole time window. -/
theorem metricUniformEquivalentOnWindow_of_logDerivativeInput
    (K : Set M) (β ψ t0 C A : Real)
    (gRef : SmoothRiemannianMetric I M)
    (gSeq : Nat -> Real -> SmoothRiemannianMetric I M)
    (T :
      forall _i : Nat, Real -> forall x : M,
        Tensor0SBundle.Tensor0SSpace (𝕜 := Real) (E := E) (H := H)
          (I := I) (M := M) 2 x)
    (ht0 : t0 ∈ Set.Icc β ψ)
    (hC : 1 <= C)
    (hequiv0 :
      forall i : Nat,
        MetricUniformEquivalentOn (I := I) K gRef (gSeq i t0) C)
    (hlog : MetricLogDerivativeInput (I := I) K β ψ t0 gSeq T A) :
    MetricUniformEquivalentOnWindow (I := I) K β ψ gRef gSeq
      (fun t : Real => metricEquivalenceFactor C A t t0) := by
  intro i t ht
  refine ⟨metric_factor_one_le hC hlog.quad_bound.1, ?_⟩
  intro x hx v
  by_cases hv : v = 0
  · subst v
    simp
  have hwindow : Set.uIcc t0 t ⊆ Set.Icc β ψ :=
    Set.uIcc_subset_Icc ht0 ht
  let f : Real -> Real := fun s => (gSeq i s).inner x v v
  let f' : Real -> Real :=
    fun s => (-2 : Real) * T i s x (Realized.vec2 (I := I) v v)
  have hf_pos : forall s : Real, s ∈ Set.uIcc t0 t -> 0 < f s := by
    intro s _hs
    exact (gSeq i s).pos x v hv
  have hf_deriv :
      forall s : Real, s ∈ Set.uIcc t0 t -> HasDerivAt f (f' s) s := by
    intro s hs
    exact hlog.metric_deriv i x hx v hv s (hwindow hs)
  have hA : 0 <= A := hlog.quad_bound.1
  have hbound :
      forall s : Real, s ∈ Set.uIcc t0 t -> |f' s / f s| <= 2 * A := by
    intro s hs
    have hswin : s ∈ Set.Icc β ψ := hwindow hs
    have hquad := hlog.quad_bound.2 i s hswin x hx v
    have hden_pos : 0 < f s := hf_pos s hs
    have hnum :
        |(-2 : Real) * T i s x (Realized.vec2 (I := I) v v)| <=
          2 * (A * f s) := by
      calc
        |(-2 : Real) * T i s x (Realized.vec2 (I := I) v v)|
            = 2 * |T i s x (Realized.vec2 (I := I) v v)| := by
              rw [abs_mul]
              norm_num
        _ <= 2 * (A * f s) :=
              mul_le_mul_of_nonneg_left hquad (by norm_num)
    calc
      |f' s / f s|
          = |f' s| / f s := by
            rw [abs_div, abs_of_pos hden_pos]
      _ <= (2 * (A * f s)) / f s :=
            div_le_div_of_nonneg_right hnum (le_of_lt hden_pos)
      _ = 2 * A := by
            field_simp [hden_pos.ne']
  have hscalar :
      Real.exp (-(2 * A) * |t - t0|) * f t0 <= f t /\
        f t <= Real.exp ((2 * A) * |t - t0|) * f t0 :=
    exp_bounds_of_log_deriv_bound f f' hf_pos hf_deriv hbound
  have h0 := (hequiv0 i).2 x hx v
  constructor
  · have hlow0 : C⁻¹ * gRef.inner x v v <= f t0 := h0.1
    have hlow_exp :
        Real.exp (-(2 * A) * |t - t0|) *
            (C⁻¹ * gRef.inner x v v) <=
          Real.exp (-(2 * A) * |t - t0|) * f t0 :=
      mul_le_mul_of_nonneg_left hlow0 (le_of_lt (Real.exp_pos _))
    calc
      (metricEquivalenceFactor C A t t0)⁻¹ * gRef.inner x v v
          = Real.exp (-(2 * A) * |t - t0|) *
              (C⁻¹ * gRef.inner x v v) :=
            metric_factor_inv_mul hC
      _ <= Real.exp (-(2 * A) * |t - t0|) * f t0 := hlow_exp
      _ <= f t := hscalar.1
  · have hhigh0 : f t0 <= C * gRef.inner x v v := h0.2
    have hhigh_exp :
        Real.exp ((2 * A) * |t - t0|) * f t0 <=
          Real.exp ((2 * A) * |t - t0|) *
            (C * gRef.inner x v v) :=
      mul_le_mul_of_nonneg_left hhigh0 (le_of_lt (Real.exp_pos _))
    calc
      f t <= Real.exp ((2 * A) * |t - t0|) * f t0 := hscalar.2
      _ <= Real.exp ((2 * A) * |t - t0|) *
          (C * gRef.inner x v v) := hhigh_exp
      _ = metricEquivalenceFactor C A t t0 * gRef.inner x v v :=
          metric_factor_mul

/-- The compact theorem-facing hypotheses in MSM135 Lemma 3.11.

The raw bound predicates above do not require compactness.  This input package
does: it represents a compact set `K`, equivalence and metric-derivative
bounds at `t0`, and curvature-derivative bounds on `K x [β, ψ]`. -/
structure MetricAllTimesBoundsInput
    (K : Set M) (β ψ t0 : Real)
    (gSeq : Nat -> Real -> SmoothRiemannianMetric I M)
    (gRef : SmoothRiemannianMetric I M) where
  compact : IsCompact K
  t0_mem : t0 ∈ Set.Icc β ψ
  equivC : Real
  equiv_at_t0 :
    forall i : Nat,
      MetricUniformEquivalentOn (I := I) K gRef (gSeq i t0) equivC
  metricC : Nat -> Real
  metricC_nonneg : forall p : Nat, 0 <= metricC p
  metric_at_t0 :
    MetricCovDerivBoundsAtTimeOn (I := I) K t0 gSeq gRef metricC
  curvC : Nat -> Real
  curvC_nonneg : forall p : Nat, 0 <= curvC p
  curv_on_window :
    CurvDerivBoundsOnWindow (I := I) K β ψ gSeq curvC

/-- The spatial part of the expected conclusion of MSM135 Lemma 3.11.

The full mixed time-spatial derivative conclusion is not stated here yet,
because the project still needs a canonical tensor-valued API for
`partial_t^q nabla^p g(t)`. -/
structure MetricAllTimesSpatialConclusion
    (K : Set M) (β ψ : Real)
    (gSeq : Nat -> Real -> SmoothRiemannianMetric I M)
    (gRef : SmoothRiemannianMetric I M) where
  B : Real -> Real
  equiv_on_window :
    MetricUniformEquivalentOnWindow (I := I) K β ψ gRef gSeq B
  metricC : Nat -> Real
  metric_on_window :
    MetricCovDerivBoundsOnWindow (I := I) K β ψ gSeq gRef metricC

end FixedDomain

end HCGCompactness
end RicciFlower
