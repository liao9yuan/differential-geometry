import DifferentialGeometry.Geometry.Comparison.Variation.ParallelTransport
import DifferentialGeometry.Geometry.Comparison.Variation.FixedChartIdentities
import DifferentialGeometry.Geometry.Connection.ParallelTransport.AlongCurve
import DifferentialGeometry.Geometry.Connection.ParallelTransport.CovariantDerivativeAlong
import DifferentialGeometry.Geometry.Connection.ParallelTransport.MFDerivAlongCurve
import DifferentialGeometry.Geometry.Geodesic.Equation
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Curvature
import DifferentialGeometry.Geometry.Connection.LeviCivita.Defs
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.RicciIdentity
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.RicciConnection
import DifferentialGeometry.Geometry.Metric.TensorInner.TangentRiemannian
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Topology.VectorBundle.Riemannian
import Mathlib.Topology.Compactness.Compact

set_option linter.unusedSectionVars false

/-!
# Arc length and the regularity of speed

This file packages the arc-length functional and the analytic regularity of
the speed of a smooth two-parameter variation `f : ℝ → ℝ → M`, the foundation
on which the first and second variation of length are built:

* `arcLength g η a b` — the real-valued arc length of a curve `η` on `[a, b]`;
* the speed-squared `speedSq g f s t` of the slice `t ↦ f s t` and its
  identification with the chart-coordinate Gram quadratic form;
* smoothness and continuity of the total-space partial-`t` velocity and of the
  metric inner product of parameter-dependent tangent vectors;
* continuity of the speed-squared in the parameter `(s, t)`;
* a uniform positive lower bound for the speed on a neighbourhood of `s = 0`
  along a regular variation whose central curve is unit-speed.
-/

noncomputable section

open Set Function Filter Manifold Bundle MeasureTheory intervalIntegral
open scoped Topology Manifold ContDiff

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Variation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Riemannian.AlongCurve
open DifferentialGeometry.Geometry.Riemannian.Geodesic

/-- Real-valued arc length of a curve `η : ℝ → M` on `[a, b]` against
the smooth Riemannian metric `g`. The integrand is the speed
`‖η'(t)‖_g = √ g.inner (η t) (η'(t)) (η'(t))`, computed via the
manifold derivative `mfderiv (𝓘(ℝ, ℝ)) I η t (1 : ℝ)`. The integral is
the interval integral on `[a, b]`. -/
def arcLength (g : SmoothRiemannianMetric I M) (η : ℝ → M) (a b : ℝ) : ℝ :=
  ∫ t in a..b,
    Real.sqrt
      (g.inner (η t)
        (mfderiv (𝓘(ℝ, ℝ)) I η t (1 : ℝ))
        (mfderiv (𝓘(ℝ, ℝ)) I η t (1 : ℝ)))

/-- Pointwise speed-squared along a smooth two-parameter variation
`f : ℝ → ℝ → M`, viewed as a function of `(s, t) ∈ ℝ × ℝ`. Auxiliary
definition used to state the unit-speed-at-`s = 0` hypothesis of
`speed_positivity_on_regular_variation`. -/
def speedSq
    (g : SmoothRiemannianMetric I M) (f : ℝ → ℝ → M) (s t : ℝ) : ℝ :=
  g.inner (f s t)
    (mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f s u) t (1 : ℝ))
    (mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f s u) t (1 : ℝ))

/-- The arc length of the slice `t ↦ f s t` on `[0, L]` is the interval
integral of the square root of the speed-squared `speedSq g f s t`. This is
definitional: the `arcLength` integrand is `√(g.inner (f s t) (∂_t f) (∂_t f))`,
and `speedSq g f s t` is exactly that inner product. -/
lemma arcLength_slice_eq_integral_sqrt_speedSq
    (g : SmoothRiemannianMetric I M) (f : ℝ → ℝ → M) (s L : ℝ) :
    arcLength (I := I) g (fun t : ℝ => f s t) 0 L
      = ∫ t in (0 : ℝ)..L, Real.sqrt (speedSq (I := I) g f s t) := by
  rfl

/-- **Moving-foot speed-as-chartGram bridge.** The speed-squared
`speedSq g f s t` of the slice `t ↦ f s t`, defined through the manifold
velocity `mfderiv (fun u ↦ f s u) t 1`, equals the chart-coordinate Gram
quadratic form `chartGramAlongCurve g (f s t) (fun v ↦ f s v) D D t`, where
`D v := fderiv ℝ (extChartAt I (f s t) ∘ (fun w ↦ f s w)) v 1` is the
chart-coordinate velocity section in the chart *pinned at the foot* `f s t`.

The foot of the chart coincides with the basepoint `f s t`, so at the diagonal
the moving-foot manifold velocity equals, after applying the inverse
trivialisation, the chart-coordinate velocity; there is no transition-Jacobian
obstruction. The proof first rewrites the raw `mfderiv`-velocity as
`triv.symmL (f s t) (D t)` (the chart-coordinate bridge
`raw_mfderiv_eq_symmL_apply_fderiv`), then identifies the `g`-inner product with
the Gram bilinear form (`inner_eq_chartGramOnE_bilinear_on_baseSet`), and finally
reconciles `chartGramMatrix g (f s t) (f s t)` with
`chartGramOnE g (f s t) · · (extChartAt I (f s t) (f s t))` via the chart
round-trip `(extChartAt I α).symm (extChartAt I α α) = α`. -/
private lemma speedSq_eq_chartGramAlongCurve
    (g : SmoothRiemannianMetric I M) (f : ℝ → ℝ → M)
    (hf : IsSmoothVariation (I := I) f) (s t : ℝ) :
    speedSq (I := I) g f s t
      = chartGramAlongCurve (I := I) g (f s t) (fun v : ℝ => f s v)
          (fun v : ℝ =>
            fderiv ℝ (fun w : ℝ => extChartAt I (f s t) (f s w)) v (1 : ℝ))
          (fun v : ℝ =>
            fderiv ℝ (fun w : ℝ => extChartAt I (f s t) (f s w)) v (1 : ℝ))
          t := by
  classical
  set α : M := f s t with hα
  set D : ℝ → E := fun v : ℝ =>
    fderiv ℝ (fun w : ℝ => extChartAt I α (f s w)) v (1 : ℝ) with hD
  have hslice : ContMDiff (𝓘(ℝ, ℝ)) I (8 : ℕ) (fun u : ℝ => f s u) := by
    have hincl : ContMDiff (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) (8 : ℕ)
        (fun u : ℝ => (s, u)) :=
      contMDiff_const.prodMk contMDiff_id
    exact (hf : ContMDiff _ _ _ _).comp hincl
  have hsrc : (fun u : ℝ => f s u) t ∈ (chartAt H α).source := by
    change f s t ∈ (chartAt H α).source
    rw [hα]; exact mem_chart_source H (f s t)
  have hraw :
      (mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f s u) t (1 : ℝ) : E)
        = (trivializationAt E (TangentSpace I) α).symmL ℝ
            ((fun u : ℝ => f s u) t) (D t) := by
    have h := MFDerivAlongCurve.raw_mfderiv_eq_symmL_apply_fderiv_of_mdifferentiableAt
      (I := I) (M := M)
      (γ := fun u : ℝ => f s u) (hslice.mdifferentiableAt (by norm_num)) α hsrc
    have hcomp : ((extChartAt I α) ∘ (fun u : ℝ => f s u))
        = (fun w : ℝ => extChartAt I α (f s w)) := rfl
    rw [hcomp] at h
    rw [h]
  have hbase : (fun u : ℝ => f s u) t = α := by rw [hα]
  rw [show speedSq (I := I) g f s t
        = g.inner α
            ((trivializationAt E (TangentSpace I) α).symmL ℝ α (D t))
            ((trivializationAt E (TangentSpace I) α).symmL ℝ α (D t)) from by
      unfold speedSq
      rw [hraw, hbase]]
  rw [inner_eq_chartGramOnE_bilinear_on_baseSet (I := I) g α (D t) (D t)]
  rw [chartGramAlongCurve_def]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  have hroundtrip :
      DifferentialGeometry.Integral.DivergenceTheorem.chartGramOnE (I := I) g α i j
          (chartCurve (I := I) α (fun v : ℝ => f s v) t)
        = chartGramMatrix (I := I) g α α i j := by
    rw [chartCurve_def]
    change chartGramMatrix (I := I) g α
        ((extChartAt I α).symm (extChartAt I α (f s t))) i j
      = chartGramMatrix (I := I) g α α i j
    rw [hα] at *
    rw [extChartAt_to_inv]
  rw [hroundtrip]

/-- The partial-`t` derivative of a smooth two-parameter variation, evaluated
at `(s, t)` with the unit input vector `1 : ℝ`, coincides with the directional
derivative of the uncurried map at `(s, t)` along `(0, 1) : ℝ × ℝ`. -/
private lemma mfderiv_partial_t_eq
    (f : ℝ → ℝ → M) (hf : IsSmoothVariation (I := I) f) (s t : ℝ) :
    (mfderiv (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) I (fun p : ℝ × ℝ => f p.1 p.2) (s, t))
      ((0, 1) : ℝ × ℝ)
    = (mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f s u) t) (1 : ℝ) := by
  have hf_mdiff :
      MDifferentiableAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) I (fun q : ℝ × ℝ => f q.1 q.2)
        (s, t) :=
    (hf : ContMDiff _ _ _ _).mdifferentiableAt (by simp)
  have hpartials :=
    mfderiv_prod_eq_add_comp (I := 𝓘(ℝ, ℝ)) (I' := 𝓘(ℝ, ℝ)) (I'' := I)
      (f := fun q : ℝ × ℝ => f q.1 q.2) (p := (s, t)) hf_mdiff
  conv_lhs => rw [hpartials]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_comp',
    Function.comp_apply, id_eq]
  change ((mfderiv (𝓘(ℝ, ℝ)) I (fun z : ℝ => f z t) s) (0 : ℝ)) +
      ((mfderiv (𝓘(ℝ, ℝ)) I (fun z : ℝ => f s z) t) (1 : ℝ)) =
    (mfderiv (𝓘(ℝ, ℝ)) I (fun z : ℝ => f s z) t) (1 : ℝ)
  have hzero : (mfderiv (𝓘(ℝ, ℝ)) I (fun z : ℝ => f z t) s) (0 : ℝ) = 0 :=
    ContinuousLinearMap.map_zero _
  rw [hzero, zero_add]

/-- The total-space `TM`-valued partial-`t` velocity of a smooth two-parameter
variation is continuous in the parameter `(s, t)`. Smoothness into the total
space `TM` decomposes via `Bundle.contMDiffAt_totalSpace` into smoothness of
the projection `(s, t) ↦ f s t` (immediate from joint smoothness) and
smoothness of the chart-trivialisation-projected fiber value, which is a
mfderiv-applied-to-a-smooth-vector formula handled by
`ContMDiffAt.mfderiv_apply`. -/
lemma velocity_totalSpace_contMDiff
    (f : ℝ → ℝ → M) (hf : IsSmoothVariation (I := I) f) :
    ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, E)) (7 : ℕ)
      (fun p : ℝ × ℝ =>
        (TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
          (f p.1 p.2) (mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f p.1 u) p.2 (1 : ℝ)) :
            TangentBundle I M)) := by
  classical
  have hf_uncurry : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) I (8 : ℕ)
      (fun p : ℝ × ℝ => f p.1 p.2) := hf
  intro p₀
  rw [Bundle.contMDiffAt_totalSpace]
  refine ⟨(hf_uncurry.contMDiffAt).of_le (by exact_mod_cast (by norm_num : (7 : ℕ) ≤ 8)), ?_⟩
  have hF_smooth : ContMDiffAt
      ((𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)).prod (𝓘(ℝ, ℝ))) I (8 : ℕ)
      (Function.uncurry (fun q : ℝ × ℝ => fun u : ℝ => f q.1 u))
      (p₀, p₀.2) := by
    have : (Function.uncurry (fun q : ℝ × ℝ => fun u : ℝ => f q.1 u))
        = fun r : (ℝ × ℝ) × ℝ => f r.1.1 r.2 := rfl
    rw [this]
    have hproj : ContMDiff ((𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)).prod (𝓘(ℝ, ℝ)))
        (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) (8 : ℕ)
        (fun r : (ℝ × ℝ) × ℝ => (r.1.1, r.2)) :=
      contMDiff_fst.fst.prodMk contMDiff_snd
    exact (hf_uncurry.comp hproj).contMDiffAt
  have hg_smooth : ContMDiffAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ)) (7 : ℕ)
      (fun q : ℝ × ℝ => q.2) p₀ := contMDiffAt_snd
  have hg₁_smooth : ContMDiffAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) (7 : ℕ)
      (id : ℝ × ℝ → ℝ × ℝ) p₀ := contMDiffAt_id
  have hg₂_smooth : ContMDiffAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ)) (7 : ℕ)
      (fun _ : ℝ × ℝ => (1 : ℝ)) p₀ := contMDiffAt_const
  have h_smooth_mfd := ContMDiffAt.mfderiv_apply
    (I := 𝓘(ℝ, ℝ)) (I' := I)
    (f := fun q : ℝ × ℝ => fun u : ℝ => f q.1 u)
    (g := fun q : ℝ × ℝ => q.2)
    (g₁ := id) (g₂ := fun _ : ℝ × ℝ => (1 : ℝ))
    (x₀ := p₀) (n := (8 : ℕ)) (m := (7 : ℕ))
    hF_smooth hg_smooth hg₁_smooth hg₂_smooth (by exact_mod_cast (by norm_num : (7 : ℕ) + 1 ≤ 8))
  have hf_cts : Continuous (fun p : ℝ × ℝ => f p.1 p.2) := hf_uncurry.continuous
  have h_baseSet_open : IsOpen
      ((fun p : ℝ × ℝ => f p.1 p.2) ⁻¹'
        (trivializationAt E (TangentSpace I) (f p₀.1 p₀.2)).baseSet) :=
    (Trivialization.open_baseSet _).preimage hf_cts
  have hp₀_in : p₀ ∈
      (fun p : ℝ × ℝ => f p.1 p.2) ⁻¹'
        (trivializationAt E (TangentSpace I) (f p₀.1 p₀.2)).baseSet :=
    mem_baseSet_trivializationAt E (TangentSpace I) (f p₀.1 p₀.2)
  have h_nhds : ((fun p : ℝ × ℝ => f p.1 p.2) ⁻¹'
      (trivializationAt E (TangentSpace I) (f p₀.1 p₀.2)).baseSet) ∈ nhds p₀ :=
    h_baseSet_open.mem_nhds hp₀_in
  have h_eq : ∀ᶠ p in nhds p₀,
      (trivializationAt E (TangentSpace I) (f p₀.1 p₀.2)
            ⟨f p.1 p.2, mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f p.1 u) p.2 (1 : ℝ)⟩).2
        = inTangentCoordinates 𝓘(ℝ, ℝ) I (fun q : ℝ × ℝ => q.2)
            (fun q : ℝ × ℝ => f q.1 q.2)
            (fun q : ℝ × ℝ => mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f q.1 u) q.2)
            p₀ p (1 : ℝ) := by
    filter_upwards [h_nhds] with p hp
    symm
    unfold inTangentCoordinates
    change ((trivializationAt E (TangentSpace I) (f p₀.1 p₀.2)).continuousLinearMapAt ℝ
              (f p.1 p.2)
            ∘L (mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f p.1 u) p.2)
            ∘L ((trivializationAt ℝ (TangentSpace
                  (𝓘(ℝ, ℝ) : ModelWithCorners ℝ ℝ ℝ)) p₀.2).symmL ℝ p.2 : ℝ →L[ℝ] ℝ))
            (1 : ℝ)
          = _
    rw [TangentBundle.symmL_model_space]
    change ((trivializationAt E (TangentSpace I) (f p₀.1 p₀.2)).continuousLinearMapAt ℝ
            (f p.1 p.2))
          (mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f p.1 u) p.2 (1 : ℝ))
        = _
    change ((trivializationAt E (TangentSpace I) (f p₀.1 p₀.2)).linearMapAt ℝ
            (f p.1 p.2))
          (mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f p.1 u) p.2 (1 : ℝ))
        = _
    rw [Trivialization.coe_linearMapAt_of_mem _ hp]
  change ContMDiffAt _ 𝓘(ℝ, E) (7 : ℕ)
      (fun p : ℝ × ℝ => (trivializationAt E (TangentSpace I) (f p₀.1 p₀.2)
        ⟨f p.1 p.2, mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f p.1 u) p.2 (1 : ℝ)⟩).2) p₀
  exact h_smooth_mfd.congr_of_eventuallyEq h_eq

/-- The total-space `TM`-valued partial-`t` velocity of a smooth two-parameter
variation is continuous in the parameter `(s, t)`. Immediate corollary of the
smoothness of this total-space velocity (`velocity_totalSpace_contMDiff`). -/
private lemma velocity_totalSpace_continuous
    (f : ℝ → ℝ → M) (hf : IsSmoothVariation (I := I) f) :
    Continuous (fun p : ℝ × ℝ =>
      (TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
        (f p.1 p.2) (mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f p.1 u) p.2 (1 : ℝ)) :
          TangentBundle I M)) :=
  (velocity_totalSpace_contMDiff (I := I) (M := M) f hf).continuous

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- Continuity of the metric inner product of two parameter-dependent tangent
vectors at a moving base point. The base map `b : ℝ × ℝ → M` and the
parameter-indexed sections `v, w : ∀ p, TangentSpace I (b p)` are presented
through their total-space continuity, mirroring the boundaryless tangent-bundle
diamond-handling pattern from `TangentRiemannian.lean`. -/
private lemma continuous_g_inner_along_param
    (g : SmoothRiemannianMetric I M)
    {b : ℝ × ℝ → M} {v w : ∀ p : ℝ × ℝ, TangentSpace I (b p)}
    (hv : Continuous (fun p : ℝ × ℝ => TotalSpace.mk' E
      (E := (TangentSpace I : M → Type _)) (b p) (v p)))
    (hw : Continuous (fun p : ℝ × ℝ => TotalSpace.mk' E
      (E := (TangentSpace I : M → Type _)) (b p) (w p))) :
    Continuous (fun p : ℝ × ℝ => g.inner (b p) (v p) (w p)) := by
  letI cg : Bundle.ContinuousRiemannianMetric E (TangentSpace I : M → Type _) :=
    g.toContinuousRiemannianMetric
  letI rb : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨cg.toRiemannianMetric⟩
  have h := Continuous.inner_bundle (F := E) (B := M)
    (E := (TangentSpace I : M → Type _)) (b := b) (v := v) (w := w) hv hw
  refine h.congr ?_
  intro p
  rfl

/-- Continuity in `(s, t)` of the speed-squared of a smooth two-parameter
variation. -/
lemma speedSq_continuous
    (g : SmoothRiemannianMetric I M) (f : ℝ → ℝ → M)
    (hf : IsSmoothVariation (I := I) f) :
    Continuous (fun p : ℝ × ℝ => speedSq (I := I) g f p.1 p.2) := by
  have hvel := velocity_totalSpace_continuous (I := I) (M := M) f hf
  exact continuous_g_inner_along_param (I := I) (M := M) g hvel hvel

/-- On a small neighbourhood of `s = 0`, the speed `‖∂_t f(s, t)‖_g`
of a regular smooth variation `f` whose central curve is unit-speed
on `[0, L]` admits a uniform positive lower bound on `[0, L]`.

**Hypotheses**.

* `hf` — joint smoothness of the variation `f : ℝ × ℝ → M`. Without
  this, the speed function `(s, t) ↦ √g(∂_t f, ∂_t f)` need not be
  continuous and the conclusion fails (counter-example: piecewise
  variations with abrupt direction reversals at non-zero `s`).
* `hf0` — the central curve `t ↦ f 0 t` is unit-speed on the compact
  parameter interval `[0, L]`. Without unit-speed at `t = 0`, the
  speed at `(0, t)` could vanish on a subset of `[0, L]`, falsifying
  the conclusion (counter-example: a variation reparameterising the
  central curve to vanishing speed).

Both hypotheses are genuine geometric / analytic preconditions that a
working mathematician would expect on any second-variation-of-arc-length
statement involving a regular variation. -/
theorem speed_positivity_on_regular_variation
    (g : SmoothRiemannianMetric I M) (f : ℝ → ℝ → M) (L : ℝ)
    (hf : IsSmoothVariation (I := I) f)
    (hf0 : ∀ t ∈ Set.Icc (0 : ℝ) L, speedSq (I := I) g f 0 t = 1) :
    ∃ δ > (0 : ℝ), ∃ c > (0 : ℝ), ∀ s ∈ Set.Ioo (-δ) δ, ∀ t ∈ Set.Icc 0 L,
      c ≤ Real.sqrt
        (g.inner (f s t)
          (mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f s u) t (1 : ℝ))
          (mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f s u) t (1 : ℝ))) := by
  classical
  have hsq_cont : Continuous (fun p : ℝ × ℝ => speedSq (I := I) g f p.1 p.2) :=
    speedSq_continuous (I := I) (M := M) g f hf
  have hS_open : IsOpen
      ((fun p : ℝ × ℝ => speedSq (I := I) g f p.1 p.2) ⁻¹' Set.Ioi (1 / 4 : ℝ)) :=
    isOpen_Ioi.preimage hsq_cont
  have hZ_in_S :
      ({0} : Set ℝ) ×ˢ Set.Icc (0 : ℝ) L ⊆
        (fun p : ℝ × ℝ => speedSq (I := I) g f p.1 p.2) ⁻¹' Set.Ioi (1 / 4 : ℝ) := by
    intro p hp
    rcases hp with ⟨hp1, hp2⟩
    have hp1' : p.1 = 0 := hp1
    have hsq : speedSq (I := I) g f p.1 p.2 = 1 := by
      rw [hp1']; exact hf0 _ hp2
    change (1 / 4 : ℝ) < speedSq (I := I) g f p.1 p.2
    rw [hsq]; norm_num
  have hZ1_compact : IsCompact ({0} : Set ℝ) := isCompact_singleton
  have hZ2_compact : IsCompact (Set.Icc (0 : ℝ) L) := isCompact_Icc
  obtain ⟨U, V, hU_open, _hV_open, h0_in_U, hL_in_V, hUV_in_S⟩ :=
    generalized_tube_lemma hZ1_compact hZ2_compact hS_open hZ_in_S
  have h0_in_U' : (0 : ℝ) ∈ U := h0_in_U rfl
  rcases Metric.isOpen_iff.mp hU_open 0 h0_in_U' with ⟨δ, δ_pos, hball_U⟩
  refine ⟨δ, δ_pos, (1 / 2 : ℝ), by norm_num, ?_⟩
  intro s hs t ht
  have hs_in_U : s ∈ U := by
    apply hball_U
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt]
    exact hs
  have ht_in_V : t ∈ V := hL_in_V ht
  have h_st_in_S : speedSq (I := I) g f s t > (1 / 4 : ℝ) :=
    hUV_in_S (Set.mk_mem_prod hs_in_U ht_in_V)
  have h_speedSq_nonneg : (0 : ℝ) ≤ speedSq (I := I) g f s t :=
    le_of_lt (by linarith : (0 : ℝ) < speedSq (I := I) g f s t)
  change (1 / 2 : ℝ) ≤ Real.sqrt (speedSq (I := I) g f s t)
  have h_quarter_eq : Real.sqrt (1 / 4) = 1 / 2 := by
    rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  calc (1 / 2 : ℝ) = Real.sqrt (1 / 4) := h_quarter_eq.symm
    _ ≤ Real.sqrt (speedSq (I := I) g f s t) :=
      Real.sqrt_le_sqrt (le_of_lt h_st_in_S)

end Variation
end Riemannian
end Geometry
end DifferentialGeometry

end
