import DifferentialGeometry.Geometry.Riemannian.Variation.ParallelTransport
import DifferentialGeometry.Geometry.Riemannian.Variation.FixedChartIdentities
import DifferentialGeometry.Geometry.Riemannian.AlongCurve
import DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
import DifferentialGeometry.Geometry.Riemannian.MFDerivAlongCurve
import DifferentialGeometry.Geometry.Riemannian.Geodesic.Equation
import DifferentialGeometry.Integral.Connection.Curvature
import DifferentialGeometry.Integral.Connection.LeviCivita
import DifferentialGeometry.Integral.Connection.RicciIdentity
import DifferentialGeometry.Integral.Connection.Ricci
import DifferentialGeometry.Tensor.RSTensor.TangentRiemannian
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
# Arc length, first and second variation of length, index form

This file packages the analytic content of the second variation of
arc length along a smooth two-parameter variation `f : ℝ × ℝ → M`:

* `arcLength g η a b` — the real-valued arc length of a curve `η`
  on a closed interval `[a, b]`;
* speed positivity on a regular variation;
* commutation of mixed covariant derivatives along a smooth
  two-parameter map (Schwarz / torsion-freeness);
* the Riemann-curvature identity on a variation;
* the first and second variation formulas;
* the index form `indexForm g γ a b V W`;
* the consequence that, along a minimising geodesic with endpoint-fixed
  smooth variation field, the index form is non-negative.

Statements only — proofs are deferred.
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

/-! ## Arc length functional -/

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

/-! ## Speed positivity on a regular variation -/

/-- Pointwise speed-squared along a smooth two-parameter variation
`f : ℝ → ℝ → M`, viewed as a function of `(s, t) ∈ ℝ × ℝ`. Auxiliary
definition used to state the unit-speed-at-`s = 0` hypothesis of
`speed_positivity_on_regular_variation`. -/
private def speedSq
    (g : SmoothRiemannianMetric I M) (f : ℝ → ℝ → M) (s t : ℝ) : ℝ :=
  g.inner (f s t)
    (mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f s u) t (1 : ℝ))
    (mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f s u) t (1 : ℝ))

/-- The arc length of the slice `t ↦ f s t` on `[0, L]` is the interval
integral of the square root of the speed-squared `speedSq g f s t`. This is
definitional: the `arcLength` integrand is `√(g.inner (f s t) (∂_t f) (∂_t f))`,
and `speedSq g f s t` is exactly that inner product. -/
private lemma arcLength_slice_eq_integral_sqrt_speedSq
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
  -- Abbreviation for the foot and the chart-coordinate velocity section.
  set α : M := f s t with hα
  set D : ℝ → E := fun v : ℝ =>
    fderiv ℝ (fun w : ℝ => extChartAt I α (f s w)) v (1 : ℝ) with hD
  -- The slice `t ↦ f s t` is smooth: it is the joint map precomposed with
  -- the smooth inclusion `u ↦ (s, u)`.
  have hslice : ContMDiff (𝓘(ℝ, ℝ)) I ∞ (fun u : ℝ => f s u) := by
    have hincl : ContMDiff (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) ∞
        (fun u : ℝ => (s, u)) :=
      contMDiff_const.prodMk contMDiff_id
    exact (hf : ContMDiff _ _ _ _).comp hincl
  -- The foot lies in its own chart source.
  have hsrc : (fun u : ℝ => f s u) t ∈ (chartAt H α).source := by
    change f s t ∈ (chartAt H α).source
    rw [hα]; exact mem_chart_source H (f s t)
  -- The raw mfderiv-velocity, in the chart pinned at `α = f s t`, is the inverse
  -- trivialisation applied to the chart-coordinate velocity `D t`.
  have hraw :
      (mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f s u) t (1 : ℝ) : E)
        = (trivializationAt E (TangentSpace I) α).symmL ℝ
            ((fun u : ℝ => f s u) t) (D t) := by
    have h := MFDerivAlongCurve.raw_mfderiv_eq_symmL_apply_fderiv (I := I) (M := M)
      (γ := fun u : ℝ => f s u) hslice α hsrc
    -- The composite `extChartAt I α ∘ (fun u => f s u)` is the foot-pinned slice.
    have hcomp : ((extChartAt I α) ∘ (fun u : ℝ => f s u))
        = (fun w : ℝ => extChartAt I α (f s w)) := rfl
    rw [hcomp] at h
    rw [h]
  -- The base point of the slice at `t` is `α`.
  have hbase : (fun u : ℝ => f s u) t = α := by rw [hα]
  -- Unfold `speedSq`, rewrite both velocity arguments by `hraw`, then apply the
  -- inner-product-as-Gram bridge at `x = α`.
  rw [show speedSq (I := I) g f s t
        = g.inner α
            ((trivializationAt E (TangentSpace I) α).symmL ℝ α (D t))
            ((trivializationAt E (TangentSpace I) α).symmL ℝ α (D t)) from by
      unfold speedSq
      rw [hraw, hbase]]
  rw [inner_eq_chartGramOnE_bilinear_on_baseSet (I := I) g α (D t) (D t)]
  -- Identify the Gram-matrix sum with `chartGramAlongCurve`.
  rw [chartGramAlongCurve_def]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  -- `chartCurve α (fun v => f s v) t = extChartAt I α (f s t) = extChartAt I α α`,
  -- and `chartGramOnE g α i j (extChartAt I α α) = chartGramMatrix g α α i j`
  -- by the chart round-trip.
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
  -- After substituting `hpartials`, evaluate at `(0, 1)`.
  conv_lhs => rw [hpartials]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_comp',
    Function.comp_apply, id_eq]
  -- Goal: `(mfderiv (fun z => f z t) s) ((fst _ _ _) (0,1)) +
  --        (mfderiv (fun z => f s z) t) ((snd _ _ _) (0,1)) = (mfderiv (fun z => f s z) t) 1`
  -- `fst (0, 1) = 0` and `snd (0, 1) = 1` are definitional.
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
private lemma velocity_totalSpace_contMDiff
    (f : ℝ → ℝ → M) (hf : IsSmoothVariation (I := I) f) :
    ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, E)) ∞
      (fun p : ℝ × ℝ =>
        (TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
          (f p.1 p.2) (mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f p.1 u) p.2 (1 : ℝ)) :
            TangentBundle I M)) := by
  classical
  -- Joint smoothness of `f : ℝ × ℝ → M` as a curried map.
  have hf_uncurry : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) I ∞
      (fun p : ℝ × ℝ => f p.1 p.2) := hf
  -- We use `Bundle.contMDiffAt_totalSpace`: smooth into a total space decomposes
  -- into smooth projection + smooth trivialisation-applied fiber value.
  -- Reduce to pointwise smoothness.
  intro p₀
  rw [Bundle.contMDiffAt_totalSpace]
  refine ⟨hf_uncurry.contMDiffAt, ?_⟩
  -- We need: `ContMDiffAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) ∞
  --   (fun p => (trivializationAt E (TangentSpace I) (f p₀.1 p₀.2)
  --       ⟨f p.1 p.2, mfderiv (fun u => f p.1 u) p.2 1⟩).2) p₀`.
  -- Set up `ContMDiffAt.mfderiv_apply`:
  --   F : ℝ × ℝ → ℝ → M, F q u = f q.1 u
  --   g : ℝ × ℝ → ℝ, g q = q.2
  --   g₁ = id, g₂ = const 1
  have hF_smooth : ContMDiffAt
      ((𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)).prod (𝓘(ℝ, ℝ))) I ∞
      (Function.uncurry (fun q : ℝ × ℝ => fun u : ℝ => f q.1 u))
      (p₀, p₀.2) := by
    -- `Function.uncurry (fun q u => f q.1 u) = fun r : (ℝ × ℝ) × ℝ => f r.1.1 r.2`.
    have : (Function.uncurry (fun q : ℝ × ℝ => fun u : ℝ => f q.1 u))
        = fun r : (ℝ × ℝ) × ℝ => f r.1.1 r.2 := rfl
    rw [this]
    -- Compose: r ↦ (r.1.1, r.2) ↦ f r.1.1 r.2.
    have hproj : ContMDiff ((𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)).prod (𝓘(ℝ, ℝ)))
        (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) ∞
        (fun r : (ℝ × ℝ) × ℝ => (r.1.1, r.2)) :=
      contMDiff_fst.fst.prodMk contMDiff_snd
    exact (hf_uncurry.comp hproj).contMDiffAt
  have hg_smooth : ContMDiffAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ)) ∞
      (fun q : ℝ × ℝ => q.2) p₀ := contMDiffAt_snd
  have hg₁_smooth : ContMDiffAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) ∞
      (id : ℝ × ℝ → ℝ × ℝ) p₀ := contMDiffAt_id
  have hg₂_smooth : ContMDiffAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ)) ∞
      (fun _ : ℝ × ℝ => (1 : ℝ)) p₀ := contMDiffAt_const
  -- Apply mfderiv_apply with m = ∞, n = ∞.
  have h_smooth_mfd := ContMDiffAt.mfderiv_apply
    (I := 𝓘(ℝ, ℝ)) (I' := I)
    (f := fun q : ℝ × ℝ => fun u : ℝ => f q.1 u)
    (g := fun q : ℝ × ℝ => q.2)
    (g₁ := id) (g₂ := fun _ : ℝ × ℝ => (1 : ℝ))
    (x₀ := p₀) (n := ∞) (m := ∞)
    hF_smooth hg_smooth hg₁_smooth hg₂_smooth (by simp)
  -- `h_smooth_mfd` gives smoothness of
  --   `fun x => inTangentCoordinates 𝓘(ℝ, ℝ) I (fun q => q.2)
  --       (fun q => f q.1 q.2) (fun q => mfderiv 𝓘(ℝ,ℝ) I (fun u => f q.1 u) q.2)
  --       (id p₀) (id x) ((fun _ => 1) x)`
  -- which simplifies to
  --   `inTangentCoordinates 𝓘(ℝ, ℝ) I _ (fun q => f q.1 q.2) (fun q => mfderiv ...) p₀ x 1`.
  -- The source-side `inTangentCoordinates` is trivial (source = ℝ = model).
  -- We need to show this equals our trivialisation-applied fiber value.
  -- The result `inCoordinates F E F' E' x₀ x y₀ y ϕ` for source-model-space
  -- collapses to `(target_triv).continuousLinearMapAt y .comp ϕ`.
  -- For our case: source = ℝ (model space), so the source CLM equiv = identity.
  -- The trivialisation-applied fiber is precisely
  --   `(trivializationAt E (TangentSpace I) (f p₀.1 p₀.2)).continuousLinearMapAt ℝ
  --       (f p.1 p.2) (mfderiv (fun u => f p.1 u) p.2)`,
  -- applied to `(1 : ℝ)`.
  -- Bridge: show the two expressions agree eventually near `p₀`.
  -- Step 1: a neighbourhood of `p₀` where `f p.1 p.2 ∈ baseSet`.
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
  -- Step 2: the bridge identity on this neighbourhood.
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
  -- Step 3: transport smoothness through the equality.
  change ContMDiffAt _ 𝓘(ℝ, E) ∞
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
private lemma speedSq_continuous
    (g : SmoothRiemannianMetric I M) (f : ℝ → ℝ → M)
    (hf : IsSmoothVariation (I := I) f) :
    Continuous (fun p : ℝ × ℝ => speedSq (I := I) g f p.1 p.2) := by
  -- The TotalSpace partial-`t` velocity is continuous in (s, t).
  have hvel := velocity_totalSpace_continuous (I := I) (M := M) f hf
  -- Apply the parametric inner-product continuity with v = w = velocity.
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
  -- Continuity of `speedSq` in `(s, t)`.
  have hsq_cont : Continuous (fun p : ℝ × ℝ => speedSq (I := I) g f p.1 p.2) :=
    speedSq_continuous (I := I) (M := M) g f hf
  -- The open set `S := speedSq⁻¹ (Set.Ioi (1 / 4))` is open in `ℝ × ℝ`.
  have hS_open : IsOpen
      ((fun p : ℝ × ℝ => speedSq (I := I) g f p.1 p.2) ⁻¹' Set.Ioi (1 / 4 : ℝ)) :=
    isOpen_Ioi.preimage hsq_cont
  -- The compact set `{0} ×ˢ [0, L]` lies in `S`, because speedSq = 1 > 1/4 there.
  have hZ_in_S :
      ({0} : Set ℝ) ×ˢ Set.Icc (0 : ℝ) L ⊆
        (fun p : ℝ × ℝ => speedSq (I := I) g f p.1 p.2) ⁻¹' Set.Ioi (1 / 4 : ℝ) := by
    intro p hp
    rcases hp with ⟨hp1, hp2⟩
    -- `p.1 = 0` and `p.2 ∈ [0, L]`, so speedSq p.1 p.2 = 1 > 1/4.
    have hp1' : p.1 = 0 := hp1
    have hsq : speedSq (I := I) g f p.1 p.2 = 1 := by
      rw [hp1']; exact hf0 _ hp2
    change (1 / 4 : ℝ) < speedSq (I := I) g f p.1 p.2
    rw [hsq]; norm_num
  -- Compactness of `{0}` and `[0, L]`.
  have hZ1_compact : IsCompact ({0} : Set ℝ) := isCompact_singleton
  have hZ2_compact : IsCompact (Set.Icc (0 : ℝ) L) := isCompact_Icc
  -- Tube lemma: a product open neighbourhood `U × V ⊇ {0} ×ˢ [0, L]` lies in `S`.
  obtain ⟨U, V, hU_open, _hV_open, h0_in_U, hL_in_V, hUV_in_S⟩ :=
    generalized_tube_lemma hZ1_compact hZ2_compact hS_open hZ_in_S
  -- Extract `δ > 0` with `Ioo (-δ) δ ⊆ U`.
  have h0_in_U' : (0 : ℝ) ∈ U := h0_in_U rfl
  rcases Metric.isOpen_iff.mp hU_open 0 h0_in_U' with ⟨δ, δ_pos, hball_U⟩
  refine ⟨δ, δ_pos, (1 / 2 : ℝ), by norm_num, ?_⟩
  intro s hs t ht
  -- We have `s ∈ Ioo (-δ) δ ⊆ Metric.ball 0 δ ⊆ U` and `t ∈ Icc 0 L ⊆ V`.
  have hs_in_U : s ∈ U := by
    apply hball_U
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt]
    exact hs
  have ht_in_V : t ∈ V := hL_in_V ht
  have h_st_in_S : speedSq (I := I) g f s t > (1 / 4 : ℝ) :=
    hUV_in_S (Set.mk_mem_prod hs_in_U ht_in_V)
  -- Conclude: `sqrt(speedSq) ≥ 1/2`.
  have h_speedSq_nonneg : (0 : ℝ) ≤ speedSq (I := I) g f s t :=
    le_of_lt (by linarith : (0 : ℝ) < speedSq (I := I) g f s t)
  -- The conclusion uses `g.inner` form, which equals `speedSq` by definition.
  change (1 / 2 : ℝ) ≤ Real.sqrt (speedSq (I := I) g f s t)
  -- `sqrt` is monotone; `sqrt(1/4) = 1/2`.
  have h_quarter_eq : Real.sqrt (1 / 4) = 1 / 2 := by
    rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  calc (1 / 2 : ℝ) = Real.sqrt (1 / 4) := h_quarter_eq.symm
    _ ≤ Real.sqrt (speedSq (I := I) g f s t) :=
      Real.sqrt_le_sqrt (le_of_lt h_st_in_S)


/-! ## Index form -/

/-- The pointwise **integrand** of the second-variation index form,
on intrinsic bundle-valued sections `V, W : ∀ t, TangentSpace I (γ t)`:
`⟨∇_t V, ∇_t W⟩_g - ⟨R(V, γ') γ', W⟩_g`, where `∇_t` is the *intrinsic*
covariant derivative `covDerivAlong g γ · t` (valued in `T_{γ t} M`),
not the chart-`(γ t)`-coordinate moving-foot operator. Extracting this
as a named definition lets downstream lemmas avoid unfolding the inner
`let`-binders, which was a source of `whnf` heartbeat blow-up. -/
def indexFormIntegrand [Module.Finite ℝ E] [IsManifold I ∞ M]
    (g : SmoothRiemannianMetric I M)
    (γ : ℝ → M) (V W : ∀ t, TangentSpace I (γ t)) (t : ℝ) : ℝ :=
  let nablaV : TangentSpace I (γ t) :=
    DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong.covDerivAlong
      (I := I) g γ V t
  let nablaW : TangentSpace I (γ t) :=
    DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong.covDerivAlong
      (I := I) g γ W t
  let gammaPrime : TangentSpace I (γ t) := mfderiv (𝓘(ℝ, ℝ)) I γ t (1 : ℝ)
  let riem : TangentSpace I (γ t) :=
    (DifferentialGeometry.Integral.Connection.riemannOp
        (DifferentialGeometry.Integral.Connection.LeviCivita
          (I := I) g) (γ t))
      (V t) gammaPrime gammaPrime
  g.inner (γ t) nablaV nablaW - g.inner (γ t) riem (W t)

/-- The second-variation **index form** of a smooth curve `γ : ℝ → M`
on the interval `[a, b]`, evaluated on two intrinsic bundle-valued
sections `V, W : ∀ t, TangentSpace I (γ t)` along `γ`:
`I_γ(V, W) := ∫_a^b (⟨∇_t V, ∇_t W⟩_g - ⟨R(V, γ') γ', W⟩_g) dt`,
with the intrinsic covariant derivative `∇_t`. -/
def indexForm (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (a b : ℝ) (V W : ∀ t, TangentSpace I (γ t)) : ℝ :=
  ∫ t in a..b, indexFormIntegrand (I := I) g γ V W t

/-- Unfolded form of `indexForm` as an integral of the named
integrand. -/
lemma indexForm_eq_intervalIntegral
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (a b : ℝ) (V W : ∀ t, TangentSpace I (γ t)) :
    indexForm (I := I) g γ a b V W =
      ∫ t in a..b, indexFormIntegrand (I := I) g γ V W t := rfl

/-! ## Minimiser implies index form is non-negative -/

/-- A length-minimising unit-speed geodesic `γ : [0, L] → M` realises
a local minimum of arc length on endpoint-fixed smooth variations;
consequently the index form is non-negative on every endpoint-fixed
smooth variation field `V`. -/
theorem minimiser_implies_second_variation_nonneg
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M) (L : ℝ) (V : ℝ → E)
    (_hγ : IsGeodesicOn (I := I) g γ (Set.Icc 0 L))
    (_hmin : ∀ η : ℝ → M, ContMDiffOn 𝓘(ℝ, ℝ) I 1 η (Set.Icc 0 L) →
      η 0 = γ 0 → η L = γ L →
      arcLength (I := I) g γ 0 L ≤ arcLength (I := I) g η 0 L)
    (_hUnit : ∀ t ∈ Set.Icc (0 : ℝ) L,
      g.inner (γ t)
          (mfderiv (𝓘(ℝ, ℝ)) I γ t (1 : ℝ))
          (mfderiv (𝓘(ℝ, ℝ)) I γ t (1 : ℝ)) = 1)
    (_hVperp : ∀ t ∈ Set.Icc (0 : ℝ) L,
      g.inner (γ t) (V t) (mfderiv (𝓘(ℝ, ℝ)) I γ t (1 : ℝ)) = 0)
    (_hV0 : V 0 = 0) (_hVL : V L = 0) :
    0 ≤ indexForm (I := I) g γ 0 L V V := sorry

/-! ## Moving-foot metric compatibility for the speed-squared -/

/-- **Metric compatibility for the moving-foot speed-squared.** For a smooth
two-parameter variation `f`, the `s`-derivative at `s = 0` of the slice
speed-squared `speedSq g f s t` is `2 ⟨∇_s ∂_t f, ∂_t f⟩_g`, where the
transverse covariant derivative `∇_s ∂_t f` is `covDerivAlong` of the
longitudinal-velocity section `s ↦ ∂_t f(s, t)` along the transverse curve
`s ↦ f s t`, evaluated at `s = 0`, and `∂_t f|_{s = 0}` is the longitudinal
velocity of the central curve. This is the Leibniz / metric-compatibility step
underlying the first variation of arc length. -/
theorem S1_moving_foot_metric_compatibility
    (g : SmoothRiemannianMetric I M) (f : ℝ → ℝ → M) (t : ℝ)
    (hf : IsSmoothVariation (I := I) f) :
    HasDerivAt (fun s : ℝ => speedSq (I := I) g f s t)
      (2 * g.inner (f 0 t)
        (DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong.covDerivAlong
          (I := I) g (fun s : ℝ => f s t)
          (fun s : ℝ => mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f s u) t (1 : ℝ)) 0)
        (mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f 0 u) t (1 : ℝ))) 0 := by
  classical
  open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong in
  -- Abbreviations: the fixed foot `α = f 0 t`, the transverse curve
  -- `γ s = f s t`, the longitudinal-velocity section `Vsec`, and its
  -- chart-`α`-coordinate `V s = fderiv (extChartAt α (f s ·)) t 1`.
  set α : M := f 0 t with hα
  set γ : ℝ → M := fun s : ℝ => f s t with hγ
  set Vsec : ∀ s : ℝ, TangentSpace I (γ s) :=
    fun s : ℝ => mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f s u) t (1 : ℝ) with hVsec
  set V : ℝ → E :=
    fun s : ℝ => fderiv ℝ (fun v : ℝ => extChartAt I α (f s v)) t (1 : ℝ) with hV
  -- The chart-pulled-back variation `F (u, v) := extChartAt α (f u v)` is
  -- `C²` at `(0, t)` (foot pinned at `α = f 0 t`).
  have hF2 : ContDiffAt ℝ 2
      (fun p : ℝ × ℝ => extChartAt I α (f p.1 p.2)) (0, t) := by
    have hext : ContMDiffAt I 𝓘(ℝ, E) ∞ (extChartAt I α) (f 0 t) :=
      contMDiffAt_extChartAt (I := I) (x := α)
    have hcomp : ContMDiffAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) ∞
        (fun p : ℝ × ℝ => extChartAt I α (f p.1 p.2)) (0, t) :=
      hext.comp (0, t) hf.contMDiffAt
    have key : ContDiffAt ℝ ∞
        (fun p : ℝ × ℝ => extChartAt I α (f p.1 p.2)) (0, t) := by
      rw [← contMDiffAt_iff_contDiffAt, modelWithCornersSelf_prod,
        ← chartedSpaceSelf_prod]
      exact hcomp
    exact key.of_le (by decide)
  -- Smoothness of the transverse curve `γ = fun s => f s t`.
  have hγ_smooth : ContMDiff (𝓘(ℝ, ℝ)) I ∞ γ := by
    have hincl : ContMDiff (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) ∞
        (fun s : ℝ => (s, t)) :=
      contMDiff_id.prodMk contMDiff_const
    exact (hf : ContMDiff _ _ _ _).comp hincl
  -- Smoothness of each longitudinal slice `fun u => f s u` (used to bridge
  -- the chart-`α`-coordinate of `mfderiv` to a Fréchet derivative).
  have hslice : ∀ s : ℝ, ContMDiff (𝓘(ℝ, ℝ)) I ∞ (fun u : ℝ => f s u) := by
    intro s
    have hincl : ContMDiff (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) ∞
        (fun u : ℝ => (s, u)) :=
      contMDiff_const.prodMk contMDiff_id
    exact (hf : ContMDiff _ _ _ _).comp hincl
  -- The set on which `f s t` lies in the chart source at `α`; it is an open
  -- neighborhood of `s = 0` (since `f 0 t = α ∈ source`).
  set S : Set ℝ := γ ⁻¹' (chartAt H α).source with hS
  have hS_open : IsOpen S := by
    have hsrc_open : IsOpen (chartAt H α).source := (chartAt H α).open_source
    exact (hγ_smooth.continuous.isOpen_preimage _ hsrc_open)
  have h0S : (0 : ℝ) ∈ S := by
    change γ 0 ∈ (chartAt H α).source
    change f 0 t ∈ (chartAt H α).source
    rw [hα]; exact mem_chart_source H (f 0 t)
  have hS_nhds : S ∈ nhds (0 : ℝ) := hS_open.mem_nhds h0S
  -- `chartRepAt γ Vsec 0` (the section feeding `covDerivAlong`) coincides with
  -- `V` on `S`: both equal the chart-`α`-coordinate of the longitudinal
  -- velocity, via `chartCoord_mfderiv_along_curve_eq_fderiv`.
  have hVeq_chartRep : ∀ s ∈ S, V s =
      DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong.chartRepAt
        (I := I) γ Vsec 0 s := by
    intro s hs
    have hsrc : (fun u : ℝ => f s u) t ∈ (chartAt H α).source := hs
    have hbridge := MFDerivAlongCurve.chartCoord_mfderiv_along_curve_eq_fderiv
      (I := I) (M := M) (γ := fun u : ℝ => f s u) (hslice s) α (t := t) hsrc
    -- `chartRepAt γ Vsec 0 s = CLMat_{γ 0}(γ s)(Vsec s)`; `γ 0 = α`.
    change V s =
      (trivializationAt E (TangentSpace I) (γ 0)).continuousLinearMapAt ℝ (γ s)
        (Vsec s)
    rw [hV]
    have hγ0 : γ 0 = α := by rw [hγ, hα]
    rw [hγ0]
    -- `(extChartAt α ∘ (fun u => f s u)) = fun v => extChartAt α (f s v)`.
    have hcompfun : ((extChartAt I α) ∘ (fun u : ℝ => f s u))
        = (fun v : ℝ => extChartAt I α (f s v)) := rfl
    rw [hcompfun] at hbridge
    exact hbridge.symm
  -- `V` has a derivative at `0` (the `s`-partial of the `t`-partial of `F`).
  have hV_hasDerivAt : HasDerivAt V
      (fderiv ℝ (fderiv ℝ (fun p : ℝ × ℝ => extChartAt I α (f p.1 p.2)))
        (0, t) (1, 0) (0, 1)) 0 := by
    rw [hV]
    exact Aux2.hasDerivAt_partial_snd (fun u v => extChartAt I α (f u v)) 0 t hF2
  -- `chartCurve α γ s = extChartAt α (f s t)`; it has a derivative at `0`.
  have hchartCurve_eq : AlongCurve.chartCurve (I := I) α γ
      = fun s : ℝ => extChartAt I α (f s t) := by
    funext s; rw [AlongCurve.chartCurve_def, hγ]
  have hF1diff : DifferentiableAt ℝ
      (fun p : ℝ × ℝ => extChartAt I α (f p.1 p.2)) (0, t) :=
    (hF2.of_le one_le_two).differentiableAt one_ne_zero
  have hu_hasDerivAt : HasDerivAt (AlongCurve.chartCurve (I := I) α γ)
      (fderiv ℝ (fun p : ℝ × ℝ => extChartAt I α (f p.1 p.2)) (0, t) (1, 0)) 0 := by
    rw [hchartCurve_eq]
    exact Aux2.hasDerivAt_slice_fst (fun u v => extChartAt I α (f u v)) 0 t hF1diff
  -- `chartCurve α γ 0 = extChartAt α α` lies in the interior of the target.
  have hmem : AlongCurve.chartCurve (I := I) α γ 0 ∈
      interior (extChartAt I α).target := by
    have hxsrc : γ 0 ∈ (extChartAt I α).source := by
      rw [extChartAt_source]
      change f 0 t ∈ (chartAt H α).source
      rw [hα]; exact mem_chart_source H (f 0 t)
    have hxtarget : AlongCurve.chartCurve (I := I) α γ 0 ∈ (extChartAt I α).target :=
      (extChartAt I α).map_source hxsrc
    exact DifferentialGeometry.Integral.DivergenceTheorem.extChartAt_target_subset_interior_of_boundaryless
      (I := I) α hxtarget
  -- Apply the covariant product rule (`V = W`) to differentiate the Gram form.
  have hbase := AlongCurve.chartGramAlongCurve_hasDerivAt_covariant
    (I := I) g α γ V V
    (uPrime := fun _ =>
      fderiv ℝ (fun p : ℝ × ℝ => extChartAt I α (f p.1 p.2)) (0, t) (1, 0))
    (Vprime := fun _ =>
      fderiv ℝ (fderiv ℝ (fun p : ℝ × ℝ => extChartAt I α (f p.1 p.2)))
        (0, t) (1, 0) (0, 1))
    (Wprime := fun _ =>
      fderiv ℝ (fderiv ℝ (fun p : ℝ × ℝ => extChartAt I α (f p.1 p.2)))
        (0, t) (1, 0) (0, 1))
    hu_hasDerivAt hmem hV_hasDerivAt hV_hasDerivAt
  -- Transfer the derivative from `chartGramAlongCurve g α γ V V` to `speedSq`
  -- via the eventual identity on `S`.
  have hspeed_eq : (fun s : ℝ => speedSq (I := I) g f s t)
      =ᶠ[nhds (0 : ℝ)] (fun s : ℝ => AlongCurve.chartGramAlongCurve (I := I) g α γ V V s) := by
    filter_upwards [hS_nhds] with s hs
    -- Foot `f s t` is in the base set and chart source at `α`.
    have hsrc : f s t ∈ (chartAt H α).source := hs
    have hbase_set : f s t ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
      rw [TangentBundle.trivializationAt_baseSet]; exact hsrc
    have hxsrc : f s t ∈ (extChartAt I α).source := by rw [extChartAt_source]; exact hsrc
    -- `speedSq g f s t = g.inner (f s t) (Vsec s) (Vsec s)` by definition.
    have hsq : speedSq (I := I) g f s t = g.inner (f s t) (Vsec s) (Vsec s) := rfl
    rw [hsq]
    -- Expand `g.inner` in the chart frame at `α` via `g_inner_eq_chart_sum`.
    rw [DifferentialGeometry.Integral.Connection.g_inner_eq_chart_sum
      (I := I) g α hbase_set hxsrc (Vsec s) (Vsec s)]
    -- The chart-coordinate of `Vsec s` is `V s` on `S`.
    have hVcoord :
        (trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ (f s t) (Vsec s)
          = V s := by
      have := hVeq_chartRep s hs
      rw [this]
      change _ = (trivializationAt E (TangentSpace I) (γ 0)).continuousLinearMapAt ℝ (γ s) (Vsec s)
      have hγ0 : γ 0 = α := by rw [hγ, hα]
      have hγs : γ s = f s t := rfl
      rw [hγ0, hγs]
    -- Identify the chart sum with `chartGramAlongCurve`.
    rw [AlongCurve.chartGramAlongCurve_def]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    -- `extChartAt α (f s t) = chartCurve α γ s`; reorder factors.
    have hchart : extChartAt I α (f s t) = AlongCurve.chartCurve (I := I) α γ s := by
      rw [AlongCurve.chartCurve_def, hγ]
    rw [hchart]
    rw [show (chartModelBasis E).repr
            ((trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ (f s t)
              (Vsec s)) i
          = chartCoord (E := E) i (V s) from by rw [hVcoord]; rfl,
       show (chartModelBasis E).repr
            ((trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ (f s t)
              (Vsec s)) j
          = chartCoord (E := E) j (V s) from by rw [hVcoord]; rfl]
    ring
  -- The derivative of `speedSq` is the engine's derivative value.
  have hderiv := hbase.congr_of_eventuallyEq hspeed_eq
  -- Identify the engine value with `2 * g.inner (f 0 t) (covDerivAlong …) (∂_t f)`.
  convert hderiv using 1
  -- Abbreviate the curve point at `0`: `u0 = extChartAt α α`.
  set u0 : E := AlongCurve.chartCurve (I := I) α γ 0 with hu0
  set DV : E :=
    fderiv ℝ (fderiv ℝ (fun p : ℝ × ℝ => extChartAt I α (f p.1 p.2)))
        (0, t) (1, 0) (0, 1)
      + chartChristoffelContraction (I := I) g α
          (fderiv ℝ (fun p : ℝ × ℝ => extChartAt I α (f p.1 p.2)) (0, t) (1, 0))
          (V 0) u0 with hDV
  -- The covariant-corrected vector `DV` is the chart-`α`-coordinate (at the foot
  -- `γ 0 = α`) of the intrinsic covariant derivative `covDerivAlong g γ Vsec 0`.
  have hγ0 : γ 0 = α := by rw [hγ, hα]
  have hbase_set0 : α ∈ (trivializationAt E (TangentSpace I) α).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) α
  -- `DV = chartCovDerivAlong g α γ (chartRepAt γ Vsec 0) 0`.
  have hDV_eq :
      DV = chartCovDerivAlong (I := I) g α γ
        (DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong.chartRepAt
          (I := I) γ Vsec 0) 0 := by
    rw [chartCovDerivAlong_def, hDV]
    have hVder0 : V 0 =
        DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong.chartRepAt
          (I := I) γ Vsec 0 0 := hVeq_chartRep 0 h0S
    have huPrime0 : deriv (AlongCurve.chartCurve (I := I) α γ) 0
          = fderiv ℝ (fun p : ℝ × ℝ => extChartAt I α (f p.1 p.2)) (0, t) (1, 0) :=
      hu_hasDerivAt.deriv
    -- `chartRepAt γ Vsec 0` has the same derivative as `V` at `0` (they agree on `S`).
    have hrepDeriv : deriv
          (DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong.chartRepAt
            (I := I) γ Vsec 0) 0
        = fderiv ℝ (fderiv ℝ (fun p : ℝ × ℝ => extChartAt I α (f p.1 p.2)))
            (0, t) (1, 0) (0, 1) := by
      have hrep_hasDeriv :
          HasDerivAt
            (DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong.chartRepAt
              (I := I) γ Vsec 0)
            (fderiv ℝ (fderiv ℝ (fun p : ℝ × ℝ => extChartAt I α (f p.1 p.2)))
              (0, t) (1, 0) (0, 1)) 0 := by
        refine hV_hasDerivAt.congr_of_eventuallyEq ?_
        filter_upwards [hS_nhds] with s hs
        exact (hVeq_chartRep s hs).symm
      exact hrep_hasDeriv.deriv
    rw [hrepDeriv, huPrime0, hVder0]
  -- Push `DV` to the intrinsic covariant derivative at the foot.
  have hDV_intrinsic :
      DV = (trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ α
          (DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong.covDerivAlong
            (I := I) g γ Vsec 0) := by
    rw [hDV_eq]
    have hcc := DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong.covDerivAlong_chartCoord
      (I := I) g γ Vsec 0
    rw [hγ0] at hcc
    exact hcc.symm
  -- The chart-`α`-coordinate of `Vsec 0` is `V 0`.
  have hVsec0_coord :
      (trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ α (Vsec 0) = V 0 := by
    have hcoord := hVeq_chartRep 0 h0S
    rw [hcoord]
    change _ = (trivializationAt E (TangentSpace I) (γ 0)).continuousLinearMapAt ℝ (γ 0) (Vsec 0)
    rw [hγ0]
  -- `DifferentialGeometry.Integral.DivergenceTheorem.chartGramOnE g α l j u0 = chartGramMatrix g α α l j` (chart round-trip).
  have hu0_eq : u0 = extChartAt I α α := by
    rw [hu0, AlongCurve.chartCurve_def, hγ, hα]
  have hGram_eq : ∀ l j : Fin (Module.finrank ℝ E),
      DifferentialGeometry.Integral.DivergenceTheorem.chartGramOnE (I := I) g α l j u0 = chartGramMatrix (I := I) g α α l j := by
    intro l j
    rw [DifferentialGeometry.Integral.DivergenceTheorem.chartGramOnE_def, hu0_eq, (extChartAt I α).left_inv (mem_extChartAt_source α)]
  -- The two-term engine value is `2 ⟨covDerivAlong, Vsec 0⟩`.  Each term is the
  -- chart-Gram bilinear form, which equals the `g`-inner product at `α` after the
  -- inverse trivialisation round-trip.
  -- The inner product `g.inner α (covDerivAlong) (Vsec 0)` as a chart sum.
  have hinner_sum :
      g.inner α
          (DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong.covDerivAlong
            (I := I) g γ Vsec 0)
          (Vsec 0)
        = ∑ l : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
            DifferentialGeometry.Integral.DivergenceTheorem.chartGramOnE (I := I) g α l j u0 * chartCoord (E := E) l DV
              * chartCoord (E := E) j (V 0) := by
    -- Recover the tangent vectors from their chart-`α`-coordinates `DV`, `V 0`.
    have hrt1 : (trivializationAt E (TangentSpace I) α).symmL ℝ α DV
        = DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong.covDerivAlong
            (I := I) g γ Vsec 0 := by
      rw [hDV_intrinsic]
      exact (trivializationAt E (TangentSpace I) α).symmL_continuousLinearMapAt
        (R := ℝ) hbase_set0 _
    have hrt2 : (trivializationAt E (TangentSpace I) α).symmL ℝ α (V 0) = Vsec 0 := by
      rw [← hVsec0_coord]
      exact (trivializationAt E (TangentSpace I) α).symmL_continuousLinearMapAt
        (R := ℝ) hbase_set0 _
    rw [← hrt1, ← hrt2,
      AlongCurve.inner_eq_chartGramOnE_bilinear_on_baseSet (I := I) g α DV (V 0)]
    refine Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun j _ => ?_))
    rw [hGram_eq l j]
  -- Assemble: target `= 2 * inner`, engine `= T1 + T2`, with `T1 = T2 = inner`.
  rw [hinner_sum]
  -- The engine RHS is `T1 + T2`; both equal the chart sum above (`V = W = V`),
  -- the second being a relabelling.  Expand and reconcile by `ring`/`sum_comm`.
  have hT2 :
      (∑ i : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
          DifferentialGeometry.Integral.DivergenceTheorem.chartGramOnE (I := I) g α i l u0 * chartCoord (E := E) i (V 0)
            * chartCoord (E := E) l DV)
        = ∑ l : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
            DifferentialGeometry.Integral.DivergenceTheorem.chartGramOnE (I := I) g α l j u0 * chartCoord (E := E) l DV
              * chartCoord (E := E) j (V 0) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun i _ => ?_))
    rw [DifferentialGeometry.Integral.DivergenceTheorem.chartGramOnE_symm (I := I) g α i l u0]
    ring
  -- Now match `2 * (chart sum) = T1 + T2`.
  change (2 : ℝ) * (∑ l, ∑ j, DifferentialGeometry.Integral.DivergenceTheorem.chartGramOnE (I := I) g α l j u0
        * chartCoord (E := E) l DV * chartCoord (E := E) j (V 0))
      = (∑ l, ∑ j, DifferentialGeometry.Integral.DivergenceTheorem.chartGramOnE (I := I) g α l j u0
          * chartCoord (E := E) l DV * chartCoord (E := E) j (V 0))
        + (∑ i, ∑ l, DifferentialGeometry.Integral.DivergenceTheorem.chartGramOnE (I := I) g α i l u0
            * chartCoord (E := E) i (V 0) * chartCoord (E := E) l DV)
  rw [hT2]; ring

/-! ## Differentiation under the interval integral of the speed -/

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- The speed-squared `speedSq g f s t` is jointly `C^∞` in the parameter
`(s, t)`. The total-space partial-`t` velocity is smooth in `(s, t)`
(`velocity_totalSpace_contMDiff`), and the Riemannian inner product of two
smooth bundle sections is a smooth scalar function (`ContMDiff.inner_bundle`);
the model spaces `ℝ × ℝ` and `ℝ` are trivial, so `ContMDiff` is `ContDiff`. -/
private lemma speedSq_contDiff
    (g : SmoothRiemannianMetric I M) (f : ℝ → ℝ → M)
    (hf : IsSmoothVariation (I := I) f) :
    ContDiff ℝ ∞ (fun p : ℝ × ℝ => speedSq (I := I) g f p.1 p.2) := by
  have hvel := velocity_totalSpace_contMDiff (I := I) (M := M) f hf
  letI rb : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hinner := ContMDiff.inner_bundle (F := E) (B := M)
    (E := (TangentSpace I : M → Type _))
    (b := fun p : ℝ × ℝ => f p.1 p.2)
    (v := fun p : ℝ × ℝ => mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f p.1 u) p.2 (1 : ℝ))
    (w := fun p : ℝ × ℝ => mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f p.1 u) p.2 (1 : ℝ))
    hvel hvel
  have hcm : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × ℝ => speedSq (I := I) g f p.1 p.2) := by
    refine hinner.congr ?_; intro p; rfl
  rw [← contMDiff_iff_contDiff, modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
  exact hcm

/-- **Differentiation under the interval integral for the arc-length speed.**
For a smooth two-parameter variation `f` whose central curve is unit-speed on
`[0, L]`, the `s`-derivative at `s = 0` of the slice arc-length integrand
`∫₀^L √(speedSq g f s t) dt` equals the interval integral of the pointwise
`s`-derivative of `√(speedSq)`. By the chain rule and
`S1_moving_foot_metric_compatibility`, the pointwise derivative is
`(2 ⟨∇_s ∂_t f, ∂_t f⟩_g) / (2 √(speedSq g f 0 t))`. The unit-speed hypothesis
at `s = 0` guarantees positivity of the speed on `[0, L]`, so the square-root is
differentiable there; the full domination / measurability hypotheses are
supplied to the Mathlib differentiation-under-the-integral engine inside the
proof. -/
theorem S2_diff_under_interval_integral
    (g : SmoothRiemannianMetric I M) (f : ℝ → ℝ → M) (L : ℝ)
    (_hf : IsSmoothVariation (I := I) f) (_hL : 0 < L)
    (_hUnit : ∀ t ∈ Set.Icc (0 : ℝ) L, speedSq (I := I) g f 0 t = 1) :
    HasDerivAt
      (fun s : ℝ => ∫ t in (0 : ℝ)..L, Real.sqrt (speedSq (I := I) g f s t))
      (∫ t in (0 : ℝ)..L,
        (2 * g.inner (f 0 t)
          (DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong.covDerivAlong
            (I := I) g (fun s : ℝ => f s t)
            (fun s : ℝ => mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f s u) t (1 : ℝ)) 0)
          (mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f 0 u) t (1 : ℝ)))
          / (2 * Real.sqrt (speedSq (I := I) g f 0 t)))
      0 := by
  classical
  -- Abbreviations: the speed-squared `Φ`, its uncurried form `G`, and the
  -- pointwise `s`-derivative-at-`0` value `D` (the target numerator).
  set Φ : ℝ → ℝ → ℝ := fun s t => speedSq (I := I) g f s t with hΦdef
  set G : ℝ × ℝ → ℝ := fun p : ℝ × ℝ => Φ p.1 p.2 with hG
  set D : ℝ → ℝ := fun t : ℝ =>
    2 * g.inner (f 0 t)
      (DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong.covDerivAlong
        (I := I) g (fun s : ℝ => f s t)
        (fun s : ℝ => mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f s u) t (1 : ℝ)) 0)
      (mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f 0 u) t (1 : ℝ)) with hDdef
  -- (1) `Φ = speedSq` is jointly `C^∞` in `(s, t)` (`speedSq_contDiff`).
  have hΦ : ContDiff ℝ ∞ G := by
    rw [hG, hΦdef]; exact speedSq_contDiff (I := I) (M := M) g f _hf
  have hΦcont : Continuous G := hΦ.continuous
  -- (2) The pointwise `s`-derivative of `Φ(·, t)` at `s = 0` is `D t`
  -- (`S1_moving_foot_metric_compatibility`).
  have hD : ∀ t : ℝ, HasDerivAt (fun s : ℝ => Φ s t) (D t) 0 := by
    intro t
    have := S1_moving_foot_metric_compatibility (I := I) g f t _hf
    simpa only [hΦdef, hDdef] using this
  -- The `s`-partial of the jointly-`C^∞` `G` is `fderiv G (0, t) (1, 0)`, and by
  -- uniqueness of derivatives it agrees with `D`; this gives continuity of `D`.
  have hΦdiff : ∀ p : ℝ × ℝ, DifferentiableAt ℝ G p :=
    fun p => (hΦ.differentiable (by simp)).differentiableAt
  have hslice_deriv : ∀ s t : ℝ,
      HasDerivAt (fun u : ℝ => Φ u t) (fderiv ℝ G (s, t) (1, 0)) s := by
    intro s t
    have := Aux2.hasDerivAt_slice_fst (fun u v => Φ u v) s t (hΦdiff (s, t))
    simpa only [hG] using this
  have hD_eq : ∀ t : ℝ, D t = fderiv ℝ G (0, t) (1, 0) := by
    intro t
    exact (hD t).unique (hslice_deriv 0 t)
  have hpartial_cont : Continuous (fun p : ℝ × ℝ => fderiv ℝ G p (1, 0)) := by
    have hc : Continuous (fun p : ℝ × ℝ => fderiv ℝ G p) :=
      hΦ.continuous_fderiv (by simp)
    exact hc.clm_apply continuous_const
  have hDcont : Continuous D := by
    have : Continuous (fun t : ℝ => fderiv ℝ G (0, t) (1, 0)) :=
      hpartial_cont.comp (continuous_const.prodMk continuous_id)
    exact this.congr (fun t => (hD_eq t).symm)
  -- (3) Positivity: the central curve is unit-speed on `[0, L]`, so near `s = 0`
  -- the speed `√(Φ s t)` has a uniform positive lower bound `c0` on `[0, L]`.
  have hpos : ∃ δ > (0 : ℝ), ∃ c0 > (0 : ℝ), ∀ s ∈ Set.Ioo (-δ) δ,
      ∀ t ∈ Set.Icc (0 : ℝ) L, c0 ≤ Real.sqrt (Φ s t) := by
    obtain ⟨δ, hδ, c, hc, hbnd⟩ :=
      speed_positivity_on_regular_variation (I := I) (M := M) g f L _hf _hUnit
    -- `hbnd` gives `c ≤ √(g.inner ...)`; that inner product is `Φ s t = speedSq` by
    -- definition.
    exact ⟨δ, hδ, c, hc, fun s hs t ht => hbnd s hs t ht⟩
  -- (4) Differentiate under the interval integral via the Mathlib engine.
  obtain ⟨δ, hδ, c0, hc0, hposΦ⟩ := hpos
  set δ' : ℝ := δ / 2 with hδ'
  have hδ'pos : 0 < δ' := by positivity
  have hδ'lt : δ' < δ := by simp only [hδ']; linarith
  set Kset : Set (ℝ × ℝ) := Set.Icc (-δ') δ' ×ˢ Set.Icc 0 L with hKset
  have hKcompact : IsCompact Kset := (isCompact_Icc).prod isCompact_Icc
  have hKne : Kset.Nonempty :=
    ⟨(0, 0), ⟨⟨by linarith, le_of_lt hδ'pos⟩, ⟨le_refl 0, le_of_lt _hL⟩⟩⟩
  obtain ⟨pm, hpmKset, hpmMax⟩ := hKcompact.exists_isMaxOn hKne
    ((continuous_norm.comp hpartial_cont).continuousOn)
  set K1 : ℝ := ‖fderiv ℝ G pm (1, 0)‖ with hK1
  have hK1nonneg : 0 ≤ K1 := norm_nonneg _
  -- Uniform positive lower bound `c0` for the speed on the compact box `Kset`.
  have hsqrtlb : ∀ s ∈ Set.Icc (-δ') δ', ∀ t ∈ Set.Icc (0 : ℝ) L,
      c0 ≤ Real.sqrt (Φ s t) := by
    intro s hs t ht
    refine hposΦ s ?_ t ht
    rcases hs with ⟨h1, h2⟩
    exact ⟨by linarith, by linarith⟩
  -- The slice speed-squared is nonzero on the box (`√(Φ s t) ≥ c0 > 0`).
  have hΦne : ∀ s ∈ Set.Icc (-δ') δ', ∀ t ∈ Set.Icc (0 : ℝ) L, Φ s t ≠ 0 := by
    intro s hs t ht hcontra
    have hsqrt0 : Real.sqrt (Φ s t) = 0 := by rw [hcontra, Real.sqrt_zero]
    have := hsqrtlb s hs t ht
    rw [hsqrt0] at this; linarith
  -- The Lipschitz constant on the box: `K1 / (2 c0)`.
  set C0 : ℝ := K1 / (2 * c0) with hC0
  have hC0nonneg : 0 ≤ C0 := by positivity
  -- Uniform Lipschitz bound of the slice `s ↦ √(Φ s t)` on `[-δ', δ']`.
  have hlip : ∀ t ∈ Set.Icc (0 : ℝ) L,
      LipschitzOnWith C0.toNNReal (fun s => Real.sqrt (Φ s t))
        (Set.Icc (-δ') δ') := by
    intro t ht
    apply Convex.lipschitzOnWith_of_nnnorm_deriv_le (𝕜 := ℝ) _ _ (convex_Icc _ _)
    · intro s hs
      exact ((hslice_deriv s t).sqrt (hΦne s hs t ht)).differentiableAt
    · intro s hs
      have hderiv_eq : deriv (fun u : ℝ => Real.sqrt (Φ u t)) s
          = fderiv ℝ G (s, t) (1, 0) / (2 * Real.sqrt (Φ s t)) :=
        ((hslice_deriv s t).sqrt (hΦne s hs t ht)).deriv
      have hnum_le : ‖fderiv ℝ G (s, t) (1, 0)‖ ≤ K1 :=
        hpmMax (⟨hs, ht⟩ : (s, t) ∈ Kset)
      have hden_ge : 2 * c0 ≤ 2 * Real.sqrt (Φ s t) := by
        have := hsqrtlb s hs t ht; linarith
      have hden_pos : (0 : ℝ) < 2 * Real.sqrt (Φ s t) := by
        have := hsqrtlb s hs t ht; linarith
      have hnorm_le : ‖deriv (fun u : ℝ => Real.sqrt (Φ u t)) s‖ ≤ C0 := by
        rw [hderiv_eq, norm_div, Real.norm_eq_abs (2 * Real.sqrt (Φ s t)),
          abs_of_nonneg (le_of_lt hden_pos), hC0,
          div_le_div_iff₀ hden_pos (by linarith : (0 : ℝ) < 2 * c0)]
        calc ‖fderiv ℝ G (s, t) (1, 0)‖ * (2 * c0)
              ≤ K1 * (2 * c0) :=
                mul_le_mul_of_nonneg_right hnum_le (by positivity)
          _ ≤ K1 * (2 * Real.sqrt (Φ s t)) :=
                mul_le_mul_of_nonneg_left hden_ge hK1nonneg
      have h1 : ‖deriv (fun u : ℝ => Real.sqrt (Φ u t)) s‖₊
          = Real.toNNReal ‖deriv (fun u : ℝ => Real.sqrt (Φ u t)) s‖ := by
        rw [Real.toNNReal_of_nonneg (norm_nonneg _)]; rfl
      rw [h1]; exact Real.toNNReal_le_toNNReal hnorm_le
  -- The interval-integral differentiation engine.
  set Ffun : ℝ → ℝ → ℝ := fun s t => Real.sqrt (Φ s t) with hFfun
  set Ffun' : ℝ → ℝ := fun t => D t / (2 * Real.sqrt (Φ 0 t)) with hFfun'
  have hFcont : ∀ s : ℝ, Continuous (Ffun s) := fun s =>
    Real.continuous_sqrt.comp (hΦcont.comp (continuous_const.prodMk continuous_id))
  have key := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_lip
    (μ := volume) (a := (0 : ℝ)) (b := L) (F := Ffun) (F' := Ffun') (x₀ := (0 : ℝ))
    (bound := fun _ => C0) (s := Set.Ioo (-δ') δ')
    (Ioo_mem_nhds (by linarith) hδ'pos)
    (Filter.Eventually.of_forall (fun x => (hFcont x).aestronglyMeasurable))
    ((hFcont 0).intervalIntegrable 0 L)
    (by
      -- `Ffun'` is continuous on `Ioc 0 L` (nonzero denominator there).
      have hden_cont : Continuous (fun t : ℝ => 2 * Real.sqrt (Φ 0 t)) :=
        continuous_const.mul (Real.continuous_sqrt.comp
          (hΦcont.comp (continuous_const.prodMk continuous_id)))
      have hcoon : ContinuousOn Ffun' (Set.Ioc (0 : ℝ) L) := by
        apply ContinuousOn.div hDcont.continuousOn hden_cont.continuousOn
        intro t ht
        have htIcc : t ∈ Set.Icc (0 : ℝ) L := ⟨le_of_lt ht.1, ht.2⟩
        have h0 : (0 : ℝ) ∈ Set.Icc (-δ') δ' := ⟨by linarith, le_of_lt hδ'pos⟩
        have hsqrt_pos : (0 : ℝ) < Real.sqrt (Φ 0 t) := by
          have := hsqrtlb 0 h0 t htIcc; linarith
        exact ne_of_gt (by linarith)
      rw [Set.uIoc_of_le (le_of_lt _hL)]
      exact hcoon.aestronglyMeasurable measurableSet_Ioc)
    (by
      -- Lipschitz bound a.e. on `Ι 0 L`.
      apply Filter.Eventually.of_forall
      intro t ht
      rw [Set.uIoc_of_le (le_of_lt _hL)] at ht
      have htIcc : t ∈ Set.Icc (0 : ℝ) L := ⟨le_of_lt ht.1, ht.2⟩
      have hnn : Real.nnabs C0 = C0.toNNReal := by
        ext; simp [Real.coe_nnabs, Real.coe_toNNReal _ hC0nonneg,
          abs_of_nonneg hC0nonneg]
      rw [hnn]
      exact (hlip t htIcc).mono Set.Ioo_subset_Icc_self)
    (_root_.intervalIntegrable_const)
    (by
      -- Pointwise derivative at `0` for a.e. `t ∈ Ι 0 L`.
      apply Filter.Eventually.of_forall
      intro t ht
      rw [Set.uIoc_of_le (le_of_lt _hL)] at ht
      have htIcc : t ∈ Set.Icc (0 : ℝ) L := ⟨le_of_lt ht.1, ht.2⟩
      have h0 : (0 : ℝ) ∈ Set.Icc (-δ') δ' := ⟨by linarith, le_of_lt hδ'pos⟩
      exact (hD t).sqrt (hΦne 0 h0 t htIcc))
  exact key.2

/-! ## Metric compatibility for two distinct sections -/

omit [T2Space M] [SigmaCompactSpace M] in
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong in
/-- **Metric compatibility (Leibniz rule) for the `g`-inner product of two
sections along a curve, `C²`-level hypotheses.** For a curve `γ` continuous at
`t₀` whose pinned chart-`(γ t₀)`-coordinate trajectory `chartCurve (γ t₀) γ` is
differentiable at `t₀`, and two sections `V, W : ∀ t, TangentSpace I (γ t)`
whose pinned chart-`(γ t₀)`-coordinate representations are differentiable at
`t₀`, the `t`-derivative of `t ↦ g.inner (γ t) (V t) (W t)` at `t₀` equals
`⟨∇_t V, W⟩_g + ⟨V, ∇_t W⟩_g`, where `∇_t` is the intrinsic covariant
derivative `covDerivAlong g γ · t₀`. This is the genuine metric-compatibility
identity (`∇g = 0`), proved by pinning the chart at the foot `γ t₀`,
identifying the inner product with the chart-Gram bilinear form, and applying
the covariant product rule `chartGramAlongCurve_hasDerivAt_covariant`.

The hypotheses are the minimal regularity the proof consumes: continuity of `γ`
at `t₀` (for the chart-source neighbourhood) and differentiability of the
chart trajectory and the two chart-reps at `t₀`. The smooth-curve form
`metric_compat_hasDerivAt_inner` is a wrapper supplying these from
`ContMDiff … ∞ γ`. -/
lemma metric_compat_hasDerivAt_inner_of_chartCurveDeriv
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (V W : ∀ t, TangentSpace I (γ t)) (t₀ : ℝ)
    (hγ_cont : ContinuousAt γ t₀)
    (hγ_chartDeriv :
      DifferentiableAt ℝ (chartCurve (I := I) (γ t₀) γ) t₀)
    (hVdiff : DifferentiableAt ℝ (chartRepAt (I := I) γ V t₀) t₀)
    (hWdiff : DifferentiableAt ℝ (chartRepAt (I := I) γ W t₀) t₀) :
    HasDerivAt (fun s : ℝ => g.inner (γ s) (V s) (W s))
      (g.inner (γ t₀) (covDerivAlong (I := I) g γ V t₀) (W t₀)
        + g.inner (γ t₀) (V t₀) (covDerivAlong (I := I) g γ W t₀)) t₀ := by
  classical
  set α : M := γ t₀ with hα_def
  set Vrep : ℝ → E := chartRepAt (I := I) γ V t₀ with hVrep_def
  set Wrep : ℝ → E := chartRepAt (I := I) γ W t₀ with hWrep_def
  -- The foot `γ t₀ = α` is in the base set of its own trivialisation; that base
  -- set is open, so `γ s` lands in it for `s` near `t₀` (by continuity of `γ` at `t₀`).
  have hbase_t₀ : γ t₀ ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]; exact mem_chart_source H (γ t₀)
  have hbaseSet_open : IsOpen (trivializationAt E (TangentSpace I) α).baseSet :=
    (trivializationAt E (TangentSpace I) α).open_baseSet
  have hsrc_mem : {s : ℝ | γ s ∈ (trivializationAt E (TangentSpace I) α).baseSet} ∈ 𝓝 t₀ :=
    hγ_cont (hbaseSet_open.mem_nhds hbase_t₀)
  -- Round trips for `V` and `W` near `t₀`.
  have hVround : ∀ s ∈ {s : ℝ | γ s ∈ (trivializationAt E (TangentSpace I) α).baseSet},
      (trivializationAt E (TangentSpace I) α).symmL ℝ (γ s) (Vrep s) = V s := by
    intro s hs
    simpa [hVrep_def, chartRepAt_apply] using
      (trivializationAt E (TangentSpace I) α).symmL_continuousLinearMapAt (R := ℝ) hs (V s)
  have hWround : ∀ s ∈ {s : ℝ | γ s ∈ (trivializationAt E (TangentSpace I) α).baseSet},
      (trivializationAt E (TangentSpace I) α).symmL ℝ (γ s) (Wrep s) = W s := by
    intro s hs
    simpa [hWrep_def, chartRepAt_apply] using
      (trivializationAt E (TangentSpace I) α).symmL_continuousLinearMapAt (R := ℝ) hs (W s)
  -- `f s := g.inner (γ s) (V s) (W s)` agrees with the chart-Gram form near `t₀`.
  set f : ℝ → ℝ := fun s => g.inner (γ s) (V s) (W s) with hf_def
  have hf_eq : f =ᶠ[𝓝 t₀]
      fun s => AlongCurve.chartGramAlongCurve (I := I) g α γ Vrep Wrep s := by
    filter_upwards [hsrc_mem] with s hs
    have hVs := hVround s hs
    have hWs := hWround s hs
    have hfs : f s = g.inner (γ s)
        ((trivializationAt E (TangentSpace I) α).symmL ℝ (γ s) (Vrep s))
        ((trivializationAt E (TangentSpace I) α).symmL ℝ (γ s) (Wrep s)) := by
      rw [hf_def]; rw [hVs, hWs]
    rw [hfs, inner_eq_chartGramOnE_bilinear_on_baseSet (I := I) g α (Vrep s) (Wrep s)]
    rw [AlongCurve.chartGramAlongCurve_def]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    have hinv : (extChartAt I α).symm (chartCurve (I := I) α γ s) = γ s := by
      rw [chartCurve_def]
      refine (extChartAt I α).left_inv ?_
      rw [extChartAt_source_eq_chartAt_source (I := I)]
      rw [TangentBundle.trivializationAt_baseSet] at hs
      exact hs
    rw [DifferentialGeometry.Integral.DivergenceTheorem.chartGramOnE_def, hinv]
  -- The chart trajectory has the prescribed velocity at `t₀`, in the interior of the target.
  have hu_hasDerivAt : HasDerivAt (chartCurve (I := I) α γ)
      (deriv (chartCurve (I := I) α γ) t₀) t₀ :=
    hγ_chartDeriv.hasDerivAt
  have hmem_int : chartCurve (I := I) α γ t₀ ∈ interior (extChartAt I α).target := by
    have hxsrc : γ t₀ ∈ (extChartAt I α).source := by
      rw [extChartAt_source]; exact mem_chart_source H (γ t₀)
    exact DifferentialGeometry.Integral.DivergenceTheorem.extChartAt_target_subset_interior_of_boundaryless
      (I := I) α ((extChartAt I α).map_source hxsrc)
  have hVrep_hasDerivAt : HasDerivAt Vrep (deriv Vrep t₀) t₀ := hVdiff.hasDerivAt
  have hWrep_hasDerivAt : HasDerivAt Wrep (deriv Wrep t₀) t₀ := hWdiff.hasDerivAt
  -- The covariant product rule (`chartGramAlongCurve_hasDerivAt_covariant`).
  have hgram := AlongCurve.chartGramAlongCurve_hasDerivAt_covariant (I := I) g α γ Vrep Wrep
    (uPrime := fun _ => deriv (chartCurve (I := I) α γ) t₀)
    (Vprime := fun _ => deriv Vrep t₀)
    (Wprime := fun _ => deriv Wrep t₀)
    hu_hasDerivAt hmem_int hVrep_hasDerivAt hWrep_hasDerivAt
  -- The covariant-correction-augmented chart velocities are the chart-coordinates
  -- of the intrinsic covariant derivatives.
  have hbase_set0 : α ∈ (trivializationAt E (TangentSpace I) α).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) α
  -- `deriv Vrep t₀ + Christoffel(...) = chartCovDerivAlong g α γ Vrep t₀`.
  have hDVchart :
      deriv Vrep t₀ +
        chartChristoffelContraction (I := I) g α
          (deriv (chartCurve (I := I) α γ) t₀) (Vrep t₀)
          (chartCurve (I := I) α γ t₀)
        = chartCovDerivAlong (I := I) g α γ Vrep t₀ := by
    rw [chartCovDerivAlong_def]
  have hDWchart :
      deriv Wrep t₀ +
        chartChristoffelContraction (I := I) g α
          (deriv (chartCurve (I := I) α γ) t₀) (Wrep t₀)
          (chartCurve (I := I) α γ t₀)
        = chartCovDerivAlong (I := I) g α γ Wrep t₀ := by
    rw [chartCovDerivAlong_def]
  -- The chart-`α`-coordinate of `covDerivAlong g γ V t₀` is `chartCovDerivAlong g α γ Vrep t₀`.
  have hDV_eq : (trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ α
        (covDerivAlong (I := I) g γ V t₀)
      = chartCovDerivAlong (I := I) g α γ Vrep t₀ := by
    have := covDerivAlong_chartCoord (I := I) g γ V t₀
    rw [hα_def, hVrep_def]; exact this
  have hDW_eq : (trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ α
        (covDerivAlong (I := I) g γ W t₀)
      = chartCovDerivAlong (I := I) g α γ Wrep t₀ := by
    have := covDerivAlong_chartCoord (I := I) g γ W t₀
    rw [hα_def, hWrep_def]; exact this
  -- The chart-`α`-coordinates of `V t₀`, `W t₀` are `Vrep t₀`, `Wrep t₀`.
  have hVt₀_coord : (trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ α (V t₀) = Vrep t₀ := by
    rw [hVrep_def, chartRepAt_apply, hα_def]
  have hWt₀_coord : (trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ α (W t₀) = Wrep t₀ := by
    rw [hWrep_def, chartRepAt_apply, hα_def]
  -- Round trips: recover the four tangent vectors from their chart-`α`-coordinates.
  have hrtV : (trivializationAt E (TangentSpace I) α).symmL ℝ α (Vrep t₀) = V t₀ := by
    rw [← hVt₀_coord]
    exact (trivializationAt E (TangentSpace I) α).symmL_continuousLinearMapAt (R := ℝ) hbase_set0 _
  have hrtW : (trivializationAt E (TangentSpace I) α).symmL ℝ α (Wrep t₀) = W t₀ := by
    rw [← hWt₀_coord]
    exact (trivializationAt E (TangentSpace I) α).symmL_continuousLinearMapAt (R := ℝ) hbase_set0 _
  have hrtDV : (trivializationAt E (TangentSpace I) α).symmL ℝ α
        (chartCovDerivAlong (I := I) g α γ Vrep t₀)
      = covDerivAlong (I := I) g γ V t₀ := by
    rw [← hDV_eq]
    exact (trivializationAt E (TangentSpace I) α).symmL_continuousLinearMapAt (R := ℝ) hbase_set0 _
  have hrtDW : (trivializationAt E (TangentSpace I) α).symmL ℝ α
        (chartCovDerivAlong (I := I) g α γ Wrep t₀)
      = covDerivAlong (I := I) g γ W t₀ := by
    rw [← hDW_eq]
    exact (trivializationAt E (TangentSpace I) α).symmL_continuousLinearMapAt (R := ℝ) hbase_set0 _
  -- `u0 = chartCurve α γ t₀ = extChartAt α α`, and `chartGramOnE … u0 = chartGramMatrix … α`.
  set u0 : E := chartCurve (I := I) α γ t₀ with hu0_def
  have hu0_eq : u0 = extChartAt I α α := by
    rw [hu0_def, chartCurve_def, hα_def]
  have hGram_eq : ∀ l j : Fin (Module.finrank ℝ E),
      DifferentialGeometry.Integral.DivergenceTheorem.chartGramOnE (I := I) g α l j u0
        = chartGramMatrix (I := I) g α α l j := by
    intro l j
    rw [DifferentialGeometry.Integral.DivergenceTheorem.chartGramOnE_def, hu0_eq,
      (extChartAt I α).left_inv (mem_extChartAt_source α)]
  -- The two inner products as chart-Gram bilinear sums.
  have hinnerDV :
      g.inner α (covDerivAlong (I := I) g γ V t₀) (W t₀)
        = ∑ l : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
            DifferentialGeometry.Integral.DivergenceTheorem.chartGramOnE (I := I) g α l j u0
              * chartCoord (E := E) l (chartCovDerivAlong (I := I) g α γ Vrep t₀)
              * chartCoord (E := E) j (Wrep t₀) := by
    rw [← hrtDV, ← hrtW, inner_eq_chartGramOnE_bilinear_on_baseSet (I := I) g α _ _]
    refine Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun j _ => ?_))
    rw [hGram_eq l j]
  have hinnerDW :
      g.inner α (V t₀) (covDerivAlong (I := I) g γ W t₀)
        = ∑ i : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
            DifferentialGeometry.Integral.DivergenceTheorem.chartGramOnE (I := I) g α i l u0
              * chartCoord (E := E) i (Vrep t₀)
              * chartCoord (E := E) l (chartCovDerivAlong (I := I) g α γ Wrep t₀) := by
    rw [← hrtV, ← hrtDW, inner_eq_chartGramOnE_bilinear_on_baseSet (I := I) g α _ _]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun l _ => ?_))
    rw [hGram_eq i l]
  -- Assemble: transfer the derivative through `hf_eq` and match the engine value.
  refine (hgram.congr_of_eventuallyEq hf_eq).congr_deriv ?_
  rw [hinnerDV, hinnerDW]
  -- The engine derivative value: substitute the covariant-corrected chart velocities.
  -- Both `hDVchart`/`hDWchart` rewrite the chart-covariant value into the explicit
  -- (deriv + Christoffel) form appearing in the engine; rewrite the RHS backwards.
  simp only [← hDVchart, ← hDWchart]

open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong in
/-- **Metric compatibility (Leibniz rule) for the `g`-inner product of two
sections along a smooth curve.** Smooth-curve wrapper of
`metric_compat_hasDerivAt_inner_of_chartCurveDeriv`: from `ContMDiff … ∞ γ` it
supplies continuity of `γ` at `t₀` and differentiability of the chart trajectory
`chartCurve (γ t₀) γ` at `t₀`. -/
private lemma metric_compat_hasDerivAt_inner
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (V W : ∀ t, TangentSpace I (γ t)) (t₀ : ℝ)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ)
    (hVdiff : DifferentiableAt ℝ (chartRepAt (I := I) γ V t₀) t₀)
    (hWdiff : DifferentiableAt ℝ (chartRepAt (I := I) γ W t₀) t₀) :
    HasDerivAt (fun s : ℝ => g.inner (γ s) (V s) (W s))
      (g.inner (γ t₀) (covDerivAlong (I := I) g γ V t₀) (W t₀)
        + g.inner (γ t₀) (V t₀) (covDerivAlong (I := I) g γ W t₀)) t₀ := by
  -- The chart trajectory `chartCurve (γ t₀) γ = extChartAt (γ t₀) ∘ γ` is `C^∞`,
  -- hence differentiable at `t₀`.
  have hchartDeriv : DifferentiableAt ℝ (chartCurve (I := I) (γ t₀) γ) t₀ := by
    have hmdiff : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ ((extChartAt I (γ t₀)) ∘ γ) t₀ := by
      have hφ : ContMDiffAt I 𝓘(ℝ, E) ∞ (extChartAt I (γ t₀)) (γ t₀) :=
        contMDiffAt_extChartAt (I := I) (x := γ t₀) (n := ∞)
      exact hφ.comp t₀ (hγ.contMDiffAt)
    exact (contMDiffAt_iff_contDiffAt.mp hmdiff).differentiableAt (by simp)
  exact metric_compat_hasDerivAt_inner_of_chartCurveDeriv (I := I) g γ V W t₀
    hγ.continuous.continuousAt hchartDeriv hVdiff hWdiff

/-! ## Intrinsic commutation of mixed covariant derivatives -/

open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong in
/-- **Intrinsic mixed-covariant commutation at the central curve.** For a smooth
two-parameter variation `f`, the transverse covariant derivative of the
longitudinal velocity at `s = 0` equals the longitudinal covariant derivative of
the transverse (variation-field) velocity, both viewed as intrinsic
`covDerivAlong` vectors at the common foot `f 0 t`:
`∇_s ∂_t f|_{s = 0} = ∇_t ∂_s f|_{s = 0}`. This is the intrinsic lift of
`commute_ds_dt_fixed_chart`: both sides have foot `f 0 t`, and their chart-`(f 0 t)`
coordinate representations are exactly the two sections of the fixed-chart
commutation lemma. -/
private lemma commute_ds_dt_intrinsic
    (g : SmoothRiemannianMetric I M) (f : ℝ → ℝ → M)
    (hf : IsSmoothVariation (I := I) f) (t : ℝ) :
    covDerivAlong (I := I) g (fun s : ℝ => f s t)
        (fun s : ℝ => mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f s u) t (1 : ℝ)) 0
      = covDerivAlong (I := I) g (fun v : ℝ => f 0 v)
        (fun v : ℝ => mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f u v) 0 (1 : ℝ)) t := by
  classical
  set α : M := f 0 t with hα
  -- Smoothness of the longitudinal/transverse slices of `f`.
  have hslice_u : ∀ s : ℝ, ContMDiff (𝓘(ℝ, ℝ)) I ∞ (fun u : ℝ => f s u) := by
    intro s
    have hincl : ContMDiff (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) ∞ (fun u : ℝ => (s, u)) :=
      contMDiff_const.prodMk contMDiff_id
    exact (hf : ContMDiff _ _ _ _).comp hincl
  have hslice_v : ∀ v : ℝ, ContMDiff (𝓘(ℝ, ℝ)) I ∞ (fun u : ℝ => f u v) := by
    intro v
    have hincl : ContMDiff (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) ∞ (fun u : ℝ => (u, v)) :=
      contMDiff_id.prodMk contMDiff_const
    exact (hf : ContMDiff _ _ _ _).comp hincl
  have htransverse : ContMDiff (𝓘(ℝ, ℝ)) I ∞ (fun s : ℝ => f s t) := hslice_v t
  have hcentral : ContMDiff (𝓘(ℝ, ℝ)) I ∞ (fun v : ℝ => f 0 v) := hslice_u 0
  -- The two intrinsic covariant derivatives unfold at the common foot `α = f 0 t`.
  -- LHS foot: `(fun s => f s t) 0 = f 0 t = α`.  RHS foot: `(fun v => f 0 v) t = f 0 t = α`.
  rw [covDerivAlong_def, covDerivAlong_def]
  -- The foot points coincide; align the `symmL` basepoints.
  have hfootL : (fun s : ℝ => f s t) 0 = α := by rw [hα]
  have hfootR : (fun v : ℝ => f 0 v) t = α := by rw [hα]
  -- It suffices to show the two chart-`α`-coordinate covariant derivatives agree;
  -- they are the two sides of `commute_ds_dt_fixed_chart`.
  -- Chart-rep of the LHS transverse section equals the fixed-chart LHS section near `0`.
  set repL : ℝ → E := chartRepAt (I := I) (fun s : ℝ => f s t)
    (fun s : ℝ => mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f s u) t (1 : ℝ)) 0 with hrepL
  set repR : ℝ → E := chartRepAt (I := I) (fun v : ℝ => f 0 v)
    (fun v : ℝ => mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f u v) 0 (1 : ℝ)) t with hrepR
  set secL : ℝ → E :=
    fun s : ℝ => fderiv ℝ (fun v : ℝ => extChartAt I α (f s v)) t (1 : ℝ) with hsecL
  set secR : ℝ → E :=
    fun v : ℝ => fderiv ℝ (fun u : ℝ => extChartAt I α (f u v)) 0 (1 : ℝ) with hsecR
  -- `repL =ᶠ secL` near `0`: on the open set where `f s t` is in the chart source at `α`.
  have hopenL : IsOpen {s : ℝ | f s t ∈ (chartAt H α).source} :=
    htransverse.continuous.isOpen_preimage _ (chartAt H α).open_source
  have h0L : (0 : ℝ) ∈ {s : ℝ | f s t ∈ (chartAt H α).source} := by
    change f 0 t ∈ (chartAt H α).source; rw [hα]; exact mem_chart_source H (f 0 t)
  have hrepL_eq : repL =ᶠ[𝓝 (0 : ℝ)] secL := by
    filter_upwards [hopenL.mem_nhds h0L] with s hs
    have hsrc : (fun u : ℝ => f s u) t ∈ (chartAt H α).source := hs
    have hbridge := MFDerivAlongCurve.chartCoord_mfderiv_along_curve_eq_fderiv
      (I := I) (M := M) (γ := fun u : ℝ => f s u) (hslice_u s) α (t := t) hsrc
    change (trivializationAt E (TangentSpace I) ((fun s : ℝ => f s t) 0)).continuousLinearMapAt ℝ
        ((fun s : ℝ => f s t) s) (mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f s u) t (1 : ℝ))
      = fderiv ℝ (fun v : ℝ => extChartAt I α (f s v)) t (1 : ℝ)
    rw [hfootL]
    -- `(extChartAt α ∘ (fun u => f s u)) = fun v => extChartAt α (f s v)`.
    have hcompfun : ((extChartAt I α) ∘ (fun u : ℝ => f s u))
        = (fun v : ℝ => extChartAt I α (f s v)) := rfl
    rw [hcompfun] at hbridge
    exact hbridge
  -- `repR =ᶠ secR` near `t`.
  have hopenR : IsOpen {v : ℝ | f 0 v ∈ (chartAt H α).source} :=
    hcentral.continuous.isOpen_preimage _ (chartAt H α).open_source
  have h0R : t ∈ {v : ℝ | f 0 v ∈ (chartAt H α).source} := by
    change f 0 t ∈ (chartAt H α).source; rw [hα]; exact mem_chart_source H (f 0 t)
  have hrepR_eq : repR =ᶠ[𝓝 t] secR := by
    filter_upwards [hopenR.mem_nhds h0R] with v hv
    have hsrc : (fun u : ℝ => f u v) 0 ∈ (chartAt H α).source := hv
    have hbridge := MFDerivAlongCurve.chartCoord_mfderiv_along_curve_eq_fderiv
      (I := I) (M := M) (γ := fun u : ℝ => f u v) (hslice_v v) α (t := 0) hsrc
    change (trivializationAt E (TangentSpace I) ((fun v : ℝ => f 0 v) t)).continuousLinearMapAt ℝ
        ((fun v : ℝ => f 0 v) v) (mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f u v) 0 (1 : ℝ))
      = fderiv ℝ (fun u : ℝ => extChartAt I α (f u v)) 0 (1 : ℝ)
    rw [hfootR]
    have hcompfun : ((extChartAt I α) ∘ (fun u : ℝ => f u v))
        = (fun u : ℝ => extChartAt I α (f u v)) := rfl
    rw [hcompfun] at hbridge
    exact hbridge
  -- The chart-`α`-coordinate covariant derivatives, transported through the
  -- eventual equalities, are the two sides of `commute_ds_dt_fixed_chart`.
  have hchartL : chartCovDerivAlong (I := I) g ((fun s : ℝ => f s t) 0) (fun s : ℝ => f s t) repL 0
      = chartCovDerivAlong (I := I) g α (fun s : ℝ => f s t) secL 0 := by
    rw [hfootL, chartCovDerivAlong_def, chartCovDerivAlong_def, hrepL_eq.deriv_eq,
      hrepL_eq.eq_of_nhds]
  have hchartR : chartCovDerivAlong (I := I) g ((fun v : ℝ => f 0 v) t) (fun v : ℝ => f 0 v) repR t
      = chartCovDerivAlong (I := I) g α (fun v : ℝ => f 0 v) secR t := by
    rw [hfootR, chartCovDerivAlong_def, chartCovDerivAlong_def, hrepR_eq.deriv_eq,
      hrepR_eq.eq_of_nhds]
  -- The chart-curves `chartCurve α (fun s => f s t)` and `chartCurve α (fun v => f 0 v)`
  -- match the implicit curves in `commute_ds_dt_fixed_chart` (the chart basepoint is `α`).
  have hcommute := commute_ds_dt_fixed_chart (I := I) g f hf 0 t
  -- `commute_ds_dt_fixed_chart` at `(0, t)` has basepoint `f 0 t = α`.
  rw [show f (0 : ℝ) t = α from hα] at hcommute
  -- The fixed-chart commutation sections are exactly `secL` and `secR`.
  -- LHS section: `fun u => fderiv (fun v => extChartAt α (f u v)) t 1` evaluated as a curve in
  -- the first parameter — equals `secL`.
  have hcommute' :
      chartCovDerivAlong (I := I) g α (fun s : ℝ => f s t) secL 0
        = chartCovDerivAlong (I := I) g α (fun v : ℝ => f 0 v) secR t :=
    hcommute
  -- Assemble: the goal (after `covDerivAlong_def` × 2) is
  --   symmL (f s t at 0) (chartCovDerivAlong … repL 0) = symmL (f 0 v at t) (chartCovDerivAlong … repR t).
  -- `hchartL`/`hchartR` rewrite the chart-covariant values, and `hcommute'` closes them.
  rw [hchartL, hchartR]
  -- Now both `symmL` basepoints are `f 0 t = α`; apply `hcommute'`.
  rw [hcommute']

omit [T2Space M] [SigmaCompactSpace M] in
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong in
/-- **Intrinsic mixed-covariant commutation at the central curve, `C²`-level
hypotheses.** For a two-parameter map `f : ℝ → ℝ → M` whose chart-`(f 0 t)`-pullback
is `ContDiffAt ℝ 2` at `(0, t)` and whose longitudinal / transverse slices are
`ContMDiffAt 𝓘(ℝ, ℝ) I 2` at the relevant points, the transverse covariant
derivative of the longitudinal velocity at `s = 0` equals the longitudinal
covariant derivative of the transverse (variation-field) velocity, both viewed as
intrinsic `covDerivAlong` vectors at the common foot `f 0 t`:
`∇_s ∂_t f|_{s = 0} = ∇_t ∂_s f|_{s = 0}`.

This is the `C²`-relaxed sibling of `commute_ds_dt_intrinsic`: the only changes are
(i) the chain-rule bridge specialises to the `MDifferentiableAt`-level
`chartCoord_mfderiv_along_curve_eq_fderiv_of_mdifferentiableAt`, and (ii) the
fixed-chart commutation is supplied directly by `commute_ds_dt_fixed_chart_C2`
(rather than through the `IsSmoothVariation` wrapper). It is the form consumed by
the radial geodesic variation behind Gauss's lemma, whose variation is jointly
`C²` but not known to be jointly `C^∞`. -/
theorem commute_ds_dt_intrinsic_C2
    (g : SmoothRiemannianMetric I M) (f : ℝ → ℝ → M) (t : ℝ)
    (hF2 : ContDiffAt ℝ 2 (fun p : ℝ × ℝ => extChartAt I (f 0 t) (f p.1 p.2)) (0, t))
    (hslice_u : ∀ᶠ s in 𝓝 (0 : ℝ), ContMDiffAt 𝓘(ℝ, ℝ) I 2 (fun u : ℝ => f s u) t)
    (hslice_v : ∀ᶠ v in 𝓝 t, ContMDiffAt 𝓘(ℝ, ℝ) I 2 (fun u : ℝ => f u v) 0)
    (htransverse_cont : ContinuousAt (fun s : ℝ => f s t) 0)
    (hcentral_cont : ContinuousAt (fun v : ℝ => f 0 v) t) :
    covDerivAlong (I := I) g (fun s : ℝ => f s t)
        (fun s : ℝ => mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f s u) t (1 : ℝ)) 0
      = covDerivAlong (I := I) g (fun v : ℝ => f 0 v)
        (fun v : ℝ => mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f u v) 0 (1 : ℝ)) t := by
  classical
  set α : M := f 0 t with hα
  rw [covDerivAlong_def, covDerivAlong_def]
  have hfootL : (fun s : ℝ => f s t) 0 = α := by rw [hα]
  have hfootR : (fun v : ℝ => f 0 v) t = α := by rw [hα]
  set repL : ℝ → E := chartRepAt (I := I) (fun s : ℝ => f s t)
    (fun s : ℝ => mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f s u) t (1 : ℝ)) 0 with hrepL
  set repR : ℝ → E := chartRepAt (I := I) (fun v : ℝ => f 0 v)
    (fun v : ℝ => mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f u v) 0 (1 : ℝ)) t with hrepR
  set secL : ℝ → E :=
    fun s : ℝ => fderiv ℝ (fun v : ℝ => extChartAt I α (f s v)) t (1 : ℝ) with hsecL
  set secR : ℝ → E :=
    fun v : ℝ => fderiv ℝ (fun u : ℝ => extChartAt I α (f u v)) 0 (1 : ℝ) with hsecR
  -- `repL =ᶠ secL` near `0`, via the `MDifferentiableAt` chain-rule bridge.
  have hsrcL_nhds : {s : ℝ | f s t ∈ (chartAt H α).source} ∈ 𝓝 (0 : ℝ) := by
    refine htransverse_cont.preimage_mem_nhds ?_
    rw [hα]; exact (chartAt H α).open_source.mem_nhds (mem_chart_source H (f 0 t))
  have hrepL_eq : repL =ᶠ[𝓝 (0 : ℝ)] secL := by
    filter_upwards [hsrcL_nhds, hslice_u] with s hs hslice_u_s
    have hsrc : (fun u : ℝ => f s u) t ∈ (chartAt H α).source := hs
    have hmdiff : MDifferentiableAt 𝓘(ℝ, ℝ) I (fun u : ℝ => f s u) t :=
      hslice_u_s.mdifferentiableAt (by decide)
    have hbridge :=
      MFDerivAlongCurve.chartCoord_mfderiv_along_curve_eq_fderiv_of_mdifferentiableAt
        (I := I) (M := M) (γ := fun u : ℝ => f s u) hmdiff α (t := t) hsrc
    change (trivializationAt E (TangentSpace I) ((fun s : ℝ => f s t) 0)).continuousLinearMapAt ℝ
        ((fun s : ℝ => f s t) s) (mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f s u) t (1 : ℝ))
      = fderiv ℝ (fun v : ℝ => extChartAt I α (f s v)) t (1 : ℝ)
    rw [hfootL]
    have hcompfun : ((extChartAt I α) ∘ (fun u : ℝ => f s u))
        = (fun v : ℝ => extChartAt I α (f s v)) := rfl
    rw [hcompfun] at hbridge
    exact hbridge
  -- `repR =ᶠ secR` near `t`.
  have hsrcR_nhds : {v : ℝ | f 0 v ∈ (chartAt H α).source} ∈ 𝓝 t := by
    refine hcentral_cont.preimage_mem_nhds ?_
    rw [hα]; exact (chartAt H α).open_source.mem_nhds (mem_chart_source H (f 0 t))
  have hrepR_eq : repR =ᶠ[𝓝 t] secR := by
    filter_upwards [hsrcR_nhds, hslice_v] with v hv hslice_v_v
    have hsrc : (fun u : ℝ => f u v) 0 ∈ (chartAt H α).source := hv
    have hmdiff : MDifferentiableAt 𝓘(ℝ, ℝ) I (fun u : ℝ => f u v) 0 :=
      hslice_v_v.mdifferentiableAt (by decide)
    have hbridge :=
      MFDerivAlongCurve.chartCoord_mfderiv_along_curve_eq_fderiv_of_mdifferentiableAt
        (I := I) (M := M) (γ := fun u : ℝ => f u v) hmdiff α (t := 0) hsrc
    change (trivializationAt E (TangentSpace I) ((fun v : ℝ => f 0 v) t)).continuousLinearMapAt ℝ
        ((fun v : ℝ => f 0 v) v) (mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f u v) 0 (1 : ℝ))
      = fderiv ℝ (fun u : ℝ => extChartAt I α (f u v)) 0 (1 : ℝ)
    rw [hfootR]
    have hcompfun : ((extChartAt I α) ∘ (fun u : ℝ => f u v))
        = (fun u : ℝ => extChartAt I α (f u v)) := rfl
    rw [hcompfun] at hbridge
    exact hbridge
  -- Transport the chart-`α`-coordinate covariant derivatives through the eventual
  -- equalities; the resulting values are the two sides of `commute_ds_dt_fixed_chart_C2`.
  have hchartL : chartCovDerivAlong (I := I) g ((fun s : ℝ => f s t) 0) (fun s : ℝ => f s t) repL 0
      = chartCovDerivAlong (I := I) g α (fun s : ℝ => f s t) secL 0 := by
    rw [hfootL, chartCovDerivAlong_def, chartCovDerivAlong_def, hrepL_eq.deriv_eq,
      hrepL_eq.eq_of_nhds]
  have hchartR : chartCovDerivAlong (I := I) g ((fun v : ℝ => f 0 v) t) (fun v : ℝ => f 0 v) repR t
      = chartCovDerivAlong (I := I) g α (fun v : ℝ => f 0 v) secR t := by
    rw [hfootR, chartCovDerivAlong_def, chartCovDerivAlong_def, hrepR_eq.deriv_eq,
      hrepR_eq.eq_of_nhds]
  have hcommute := commute_ds_dt_fixed_chart_C2 (I := I) g f 0 t (by rw [← hα]; exact hF2)
  rw [show f (0 : ℝ) t = α from hα] at hcommute
  have hcommute' :
      chartCovDerivAlong (I := I) g α (fun s : ℝ => f s t) secL 0
        = chartCovDerivAlong (I := I) g α (fun v : ℝ => f 0 v) secR t :=
    hcommute
  rw [hchartL, hchartR]
  rw [hcommute']

/-! ## Differentiability of the variation-field and velocity chart-reps -/

/-- The chart-pulled variation `(u, v) ↦ extChartAt I α (f u v)` is jointly `C^∞`
at any `(s₀, t₀)` whose foot `f s₀ t₀` lies in the chart source at `α`. -/
private lemma chartPulled_contDiffAt_infty
    (f : ℝ → ℝ → M) (hf : IsSmoothVariation (I := I) f) (α : M) (s₀ t₀ : ℝ)
    (hsrc : f s₀ t₀ ∈ (chartAt H α).source) :
    ContDiffAt ℝ ∞ (fun p : ℝ × ℝ => extChartAt I α (f p.1 p.2)) (s₀, t₀) := by
  have hext : ContMDiffAt I 𝓘(ℝ, E) ∞ (extChartAt I α) (f s₀ t₀) :=
    contMDiffAt_extChartAt' (I := I) (x := α) hsrc
  have hcomp : ContMDiffAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) ∞
      (fun p : ℝ × ℝ => extChartAt I α (f p.1 p.2)) (s₀, t₀) :=
    hext.comp (s₀, t₀) hf.contMDiffAt
  rw [← contMDiffAt_iff_contDiffAt, modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
  exact hcomp

open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong in
/-- **Differentiability of the variation-field chart-rep along the central
curve.** For a smooth variation `f`, the pinned chart-`(f 0 t₀)`-coordinate
representation of the variation field `v ↦ ∂_s f|_{s = 0}(v)` is differentiable
at `t₀`. The chart-rep agrees, near `t₀`, with the smooth partial Fréchet
derivative `v ↦ fderiv (fun u => extChartAt I (f 0 t₀) (f u v)) 0 1`. -/
private lemma variationField_chartRep_differentiableAt
    (_g : SmoothRiemannianMetric I M) (f : ℝ → ℝ → M)
    (hf : IsSmoothVariation (I := I) f) (t₀ : ℝ) :
    DifferentiableAt ℝ
      (chartRepAt (I := I) (fun v : ℝ => f 0 v)
        (fun v : ℝ => mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f u v) 0 (1 : ℝ)) t₀) t₀ := by
  classical
  set α : M := f 0 t₀ with hα
  have hslice_v : ∀ v : ℝ, ContMDiff (𝓘(ℝ, ℝ)) I ∞ (fun u : ℝ => f u v) := by
    intro v
    have hincl : ContMDiff (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) ∞ (fun u : ℝ => (u, v)) :=
      contMDiff_id.prodMk contMDiff_const
    exact (hf : ContMDiff _ _ _ _).comp hincl
  have hcentral : ContMDiff (𝓘(ℝ, ℝ)) I ∞ (fun v : ℝ => f 0 v) := by
    have hincl : ContMDiff (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) ∞ (fun v : ℝ => ((0 : ℝ), v)) :=
      contMDiff_const.prodMk contMDiff_id
    exact (hf : ContMDiff _ _ _ _).comp hincl
  -- The smooth model section `v ↦ fderiv (fun u => extChartAt α (f u v)) 0 1`.
  set sec : ℝ → E := fun v : ℝ => fderiv ℝ (fun u : ℝ => extChartAt I α (f u v)) 0 (1 : ℝ)
    with hsec
  -- It is `C^∞` at `t₀`: partial fderiv of a jointly-smooth map, then `eval at 1`.
  have hsec_cdiff : ContDiffAt ℝ ∞ sec t₀ := by
    -- `(v, u) ↦ extChartAt α (f u v)` is jointly `C^∞` at `(t₀, 0)`.
    have hsrc0 : f 0 t₀ ∈ (chartAt H α).source := by rw [hα]; exact mem_chart_source H (f 0 t₀)
    have hjoint : ContDiffAt ℝ ∞
        (Function.uncurry (fun v u : ℝ => extChartAt I α (f u v))) (t₀, (0 : ℝ)) := by
      have h := chartPulled_contDiffAt_infty (I := I) f hf α 0 t₀ hsrc0
      -- swap the two coordinates: `(v, u) ↦ extChartAt α (f u v)`.
      have hswap : ContDiffAt ℝ ∞
          ((fun p : ℝ × ℝ => extChartAt I α (f p.1 p.2)) ∘ (fun q : ℝ × ℝ => (q.2, q.1)))
          (t₀, (0 : ℝ)) :=
        h.comp (t₀, (0 : ℝ)) ((contDiffAt_snd).prodMk (contDiffAt_fst))
      exact hswap
    have hg0 : ContDiffAt ℝ ∞ (fun _ : ℝ => (0 : ℝ)) t₀ := contDiffAt_const
    have hpartial : ContDiffAt ℝ ∞
        (fun v : ℝ => fderiv ℝ (fun u : ℝ => extChartAt I α (f u v)) ((fun _ : ℝ => (0:ℝ)) v)) t₀ :=
      ContDiffAt.fderiv (𝕜 := ℝ)
        (f := fun v u : ℝ => extChartAt I α (f u v)) (g := fun _ : ℝ => (0 : ℝ))
        hjoint hg0 (by simp)
    -- Apply the evaluation-at-1 CLM.
    have heval : ContDiffAt ℝ ∞
        (fun v : ℝ => (ContinuousLinearMap.apply ℝ E (1 : ℝ))
          (fderiv ℝ (fun u : ℝ => extChartAt I α (f u v)) 0)) t₀ :=
      (ContinuousLinearMap.apply ℝ E (1 : ℝ)).contDiff.contDiffAt.comp t₀ hpartial
    exact heval
  -- The chart-rep agrees with `sec` near `t₀`.
  have hopen : IsOpen {v : ℝ | f 0 v ∈ (chartAt H α).source} :=
    hcentral.continuous.isOpen_preimage _ (chartAt H α).open_source
  have h0 : t₀ ∈ {v : ℝ | f 0 v ∈ (chartAt H α).source} := by
    change f 0 t₀ ∈ (chartAt H α).source; rw [hα]; exact mem_chart_source H (f 0 t₀)
  have heq : (chartRepAt (I := I) (fun v : ℝ => f 0 v)
      (fun v : ℝ => mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f u v) 0 (1 : ℝ)) t₀)
        =ᶠ[𝓝 t₀] sec := by
    filter_upwards [hopen.mem_nhds h0] with v hv
    have hsrc : (fun u : ℝ => f u v) 0 ∈ (chartAt H α).source := hv
    have hbridge := MFDerivAlongCurve.chartCoord_mfderiv_along_curve_eq_fderiv
      (I := I) (M := M) (γ := fun u : ℝ => f u v) (hslice_v v) α (t := 0) hsrc
    change (trivializationAt E (TangentSpace I) ((fun v : ℝ => f 0 v) t₀)).continuousLinearMapAt ℝ
        ((fun v : ℝ => f 0 v) v) (mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f u v) 0 (1 : ℝ)) = sec v
    rw [hsec, show (fun v : ℝ => f 0 v) t₀ = α from hα.symm]
    have hcompfun : ((extChartAt I α) ∘ (fun u : ℝ => f u v))
        = (fun u : ℝ => extChartAt I α (f u v)) := rfl
    rw [hcompfun] at hbridge
    exact hbridge
  exact (heq.differentiableAt_iff).mpr (hsec_cdiff.differentiableAt (by simp))

open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong in
/-- **Differentiability of the velocity chart-rep along the central curve.** For
a smooth variation `f`, the pinned chart-`(f 0 t₀)`-coordinate representation of
the velocity field `v ↦ ∂_t f|_{s = 0}(v)` is differentiable at `t₀`. -/
private lemma velocityField_chartRep_differentiableAt
    (_g : SmoothRiemannianMetric I M) (f : ℝ → ℝ → M)
    (hf : IsSmoothVariation (I := I) f) (t₀ : ℝ) :
    DifferentiableAt ℝ
      (chartRepAt (I := I) (fun v : ℝ => f 0 v)
        (fun v : ℝ => mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f 0 u) v (1 : ℝ)) t₀) t₀ := by
  classical
  set α : M := f 0 t₀ with hα
  have hcentral : ContMDiff (𝓘(ℝ, ℝ)) I ∞ (fun v : ℝ => f 0 v) := by
    have hincl : ContMDiff (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) ∞ (fun v : ℝ => ((0 : ℝ), v)) :=
      contMDiff_const.prodMk contMDiff_id
    exact (hf : ContMDiff _ _ _ _).comp hincl
  -- The smooth model section `v ↦ fderiv (extChartAt α ∘ (f 0 ·)) v 1`, which is
  -- the velocity of the `C^∞` chart curve.
  set sec : ℝ → E := fun v : ℝ => fderiv ℝ (fun w : ℝ => extChartAt I α (f 0 w)) v (1 : ℝ)
    with hsec
  have hchartcurve_cdiff : ContDiffAt ℝ ∞ (fun w : ℝ => extChartAt I α (f 0 w)) t₀ := by
    have hext : ContMDiffAt I 𝓘(ℝ, E) ∞ (extChartAt I α) (f 0 t₀) :=
      contMDiffAt_extChartAt (I := I) (x := α)
    have hcomp : ContMDiffAt (𝓘(ℝ, ℝ)) 𝓘(ℝ, E) ∞ (fun w : ℝ => extChartAt I α (f 0 w)) t₀ :=
      hext.comp t₀ hcentral.contMDiffAt
    exact contMDiffAt_iff_contDiffAt.mp hcomp
  -- the chart curve is `C^∞` on a neighbourhood, so its `fderiv` (hence the
  -- eval-at-1 section `sec`) is `C^∞`.
  have hsec_cdiff : ContDiffAt ℝ ∞ sec t₀ := by
    have hfd : ContDiffAt ℝ ∞ (fderiv ℝ (fun w : ℝ => extChartAt I α (f 0 w))) t₀ :=
      hchartcurve_cdiff.fderiv_right (by simp)
    have heval : ContDiffAt ℝ ∞
        (fun v : ℝ => (ContinuousLinearMap.apply ℝ E (1 : ℝ))
          (fderiv ℝ (fun w : ℝ => extChartAt I α (f 0 w)) v)) t₀ :=
      (ContinuousLinearMap.apply ℝ E (1 : ℝ)).contDiff.contDiffAt.comp t₀ hfd
    exact heval
  -- The chart-rep agrees with `sec` near `t₀`.
  have hopen : IsOpen {v : ℝ | f 0 v ∈ (chartAt H α).source} :=
    hcentral.continuous.isOpen_preimage _ (chartAt H α).open_source
  have h0 : t₀ ∈ {v : ℝ | f 0 v ∈ (chartAt H α).source} := by
    change f 0 t₀ ∈ (chartAt H α).source; rw [hα]; exact mem_chart_source H (f 0 t₀)
  have heq : (chartRepAt (I := I) (fun v : ℝ => f 0 v)
      (fun v : ℝ => mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f 0 u) v (1 : ℝ)) t₀)
        =ᶠ[𝓝 t₀] sec := by
    filter_upwards [hopen.mem_nhds h0] with v hv
    have hsrc : (fun w : ℝ => f 0 w) v ∈ (chartAt H α).source := hv
    have hbridge := MFDerivAlongCurve.chartCoord_mfderiv_along_curve_eq_fderiv
      (I := I) (M := M) (γ := fun w : ℝ => f 0 w) hcentral α (t := v) hsrc
    change (trivializationAt E (TangentSpace I) ((fun v : ℝ => f 0 v) t₀)).continuousLinearMapAt ℝ
        ((fun v : ℝ => f 0 v) v) (mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f 0 u) v (1 : ℝ)) = sec v
    rw [hsec, show (fun v : ℝ => f 0 v) t₀ = α from hα.symm]
    have hcompfun : ((extChartAt I α) ∘ (fun w : ℝ => f 0 w))
        = (fun w : ℝ => extChartAt I α (f 0 w)) := rfl
    rw [hcompfun] at hbridge
    exact hbridge
  exact (heq.differentiableAt_iff).mpr (hsec_cdiff.differentiableAt (by simp))

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- Smoothness of the scalar `t ↦ g.inner (γ t) (v t) (w t)` for a base curve
`γ` and two sections `v, w` along `γ`, presented through their total-space
smoothness. The `ContMDiff` analogue of `continuousOn_g_inner_along_curve`; the
tangent-space norm-instance diamond is resolved by the disabled instances. -/
private lemma g_inner_along_curve_contMDiff
    (g : SmoothRiemannianMetric I M)
    {γ : ℝ → M} {v w : ∀ t : ℝ, TangentSpace I (γ t)}
    (hv : ContMDiff (𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, E)) ∞ (fun t : ℝ => (TotalSpace.mk' E
      (E := (TangentSpace I : M → Type _)) (γ t) (v t) : TangentBundle I M)))
    (hw : ContMDiff (𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, E)) ∞ (fun t : ℝ => (TotalSpace.mk' E
      (E := (TangentSpace I : M → Type _)) (γ t) (w t) : TangentBundle I M))) :
    ContDiff ℝ ∞ (fun t : ℝ => g.inner (γ t) (v t) (w t)) := by
  letI rb : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hinner := ContMDiff.inner_bundle (F := E) (B := M)
    (E := (TangentSpace I : M → Type _)) (b := γ) (v := v) (w := w) hv hw
  have hcm : ContMDiff (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ)) ∞ (fun t : ℝ => g.inner (γ t) (v t) (w t)) := by
    refine hinner.congr (fun t => ?_); rfl
  rw [← contMDiff_iff_contDiff]; exact hcm

/-! ## First variation of arc length -/

/-- The first variation of arc length: for a smooth endpoint-fixed
variation `f` of a unit-speed curve `γ := f 0`, the derivative of
`s ↦ arcLength g (f s ·) 0 L` at `s = 0` equals minus the integral
of `⟨V, ∇_t γ'⟩_g`, where `V := ∂_s f|_{s = 0}` is the variation
field. (The boundary contribution vanishes for endpoint-fixed
variations and is omitted.) -/
theorem first_variation_formula
    (g : SmoothRiemannianMetric I M) (f : ℝ → ℝ → M) (L : ℝ)
    (hf : IsSmoothVariation (I := I) f) (hL : 0 < L)
    (hfix0 : ∀ s : ℝ, f s 0 = f 0 0) (hfixL : ∀ s : ℝ, f s L = f 0 L)
    (hUnit : ∀ t ∈ Set.Icc (0 : ℝ) L,
      g.inner (f 0 t)
          (mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f 0 u) t (1 : ℝ))
          (mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f 0 u) t (1 : ℝ)) = 1) :
    HasDerivAt (fun s : ℝ => arcLength (I := I) g (fun t : ℝ => f s t) 0 L)
      (- ∫ t in (0 : ℝ)..L,
        g.inner (f 0 t)
          (mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f u t) 0 (1 : ℝ))
          (DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong.covDerivAlong
            (I := I) g (fun v : ℝ => f 0 v)
            (fun v : ℝ =>
              mfderiv (𝓘(ℝ, ℝ)) I (fun w : ℝ => f 0 w) v (1 : ℝ)) t)) 0 := by
  classical
  open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong in
  -- Abbreviations: central curve `γ`, variation field `V`, central velocity `γ'`.
  set γ : ℝ → M := fun v : ℝ => f 0 v with hγ_def
  set V : ∀ t : ℝ, TangentSpace I (γ t) :=
    fun t : ℝ => mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f u t) 0 (1 : ℝ) with hV_def
  set γ' : ∀ t : ℝ, TangentSpace I (γ t) :=
    fun t : ℝ => mfderiv (𝓘(ℝ, ℝ)) I (fun w : ℝ => f 0 w) t (1 : ℝ) with hγ'_def
  -- (0) The unit-speed hypothesis rewritten as `speedSq g f 0 t = 1` on `[0, L]`.
  have hUnit' : ∀ t ∈ Set.Icc (0 : ℝ) L, speedSq (I := I) g f 0 t = 1 := by
    intro t ht; exact hUnit t ht
  -- (1) The arc-length slice is the integral of `√(speedSq)`.
  have harc : (fun s : ℝ => arcLength (I := I) g (fun t : ℝ => f s t) 0 L)
      = (fun s : ℝ => ∫ t in (0 : ℝ)..L, Real.sqrt (speedSq (I := I) g f s t)) := by
    funext s; exact arcLength_slice_eq_integral_sqrt_speedSq (I := I) g f s L
  rw [harc]
  -- (2) Differentiate under the integral (`S2`).
  have hS2 := S2_diff_under_interval_integral (I := I) g f L hf hL hUnit'
  -- (3) The `S2` derivative value equals `∫₀ᴸ ⟨∇_t V, γ'⟩` after using `√(speedSq) = 1`
  -- and the intrinsic commutation `∇_s ∂_t f = ∇_t V`.
  have hsqrt1 : ∀ t ∈ Set.Icc (0 : ℝ) L, Real.sqrt (speedSq (I := I) g f 0 t) = 1 := by
    intro t ht; rw [hUnit' t ht, Real.sqrt_one]
  -- The `S2` integrand simplifies to `⟨∇_t V, γ'⟩` on `[0, L]`.
  have hintegrand_eq : Set.EqOn
      (fun t : ℝ =>
        (2 * g.inner (f 0 t)
          (covDerivAlong (I := I) g (fun s : ℝ => f s t)
            (fun s : ℝ => mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f s u) t (1 : ℝ)) 0)
          (mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f 0 u) t (1 : ℝ)))
          / (2 * Real.sqrt (speedSq (I := I) g f 0 t)))
      (fun t : ℝ => g.inner (γ t) (covDerivAlong (I := I) g γ V t) (γ' t))
      (Set.uIcc 0 L) := by
    intro t ht
    rw [Set.uIcc_of_le (le_of_lt hL)] at ht
    simp only []
    rw [hsqrt1 t ht, mul_one]
    -- `∇_s ∂_t f|₀ = ∇_t V` by `commute_ds_dt_intrinsic`.
    have hcomm := commute_ds_dt_intrinsic (I := I) g f hf t
    -- `covDerivAlong g γ V t` is the RHS of the commutation.
    rw [show covDerivAlong (I := I) g (fun s : ℝ => f s t)
          (fun s : ℝ => mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f s u) t (1 : ℝ)) 0
        = covDerivAlong (I := I) g γ V t from by
      rw [hcomm, hγ_def, hV_def]]
    rw [hγ'_def, hγ_def]
    ring
  rw [intervalIntegral.integral_congr hintegrand_eq] at hS2
  -- (4) Integration by parts via metric compatibility (`metric_compat_hasDerivAt_inner`).
  -- The boundary function `h t := ⟨V t, γ' t⟩` has derivative `⟨∇_t V, γ'⟩ + ⟨V, ∇_t γ'⟩`.
  have hγ_smooth : ContMDiff (𝓘(ℝ, ℝ)) I ∞ γ := by
    have hincl : ContMDiff (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) ∞ (fun v : ℝ => ((0 : ℝ), v)) :=
      contMDiff_const.prodMk contMDiff_id
    exact (hf : ContMDiff _ _ _ _).comp hincl
  -- Chart-rep differentiability of `V` and `γ'` at every `t₀`.
  have hVdiff : ∀ t₀ : ℝ, DifferentiableAt ℝ (chartRepAt (I := I) γ V t₀) t₀ := by
    intro t₀; rw [hγ_def, hV_def]
    exact variationField_chartRep_differentiableAt (I := I) g f hf t₀
  have hγ'diff : ∀ t₀ : ℝ, DifferentiableAt ℝ (chartRepAt (I := I) γ γ' t₀) t₀ := by
    intro t₀; rw [hγ_def, hγ'_def]
    exact velocityField_chartRep_differentiableAt (I := I) g f hf t₀
  -- The boundary derivative everywhere on `[0, L]`.
  have hbdry : ∀ t ∈ Set.uIcc (0 : ℝ) L,
      HasDerivAt (fun s : ℝ => g.inner (γ s) (V s) (γ' s))
        (g.inner (γ t) (covDerivAlong (I := I) g γ V t) (γ' t)
          + g.inner (γ t) (V t) (covDerivAlong (I := I) g γ γ' t)) t := by
    intro t _ht
    exact metric_compat_hasDerivAt_inner (I := I) g γ V γ' t hγ_smooth (hVdiff t) (hγ'diff t)
  -- The boundary values vanish: `V 0 = V L = 0` (endpoints fixed).
  have hV0 : V 0 = 0 := by
    change mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f u 0) 0 (1 : ℝ) = 0
    have hconst : (fun u : ℝ => f u 0) = (fun _ : ℝ => f 0 0) := by funext u; exact hfix0 u
    rw [hconst, mfderiv_const]; rfl
  have hVL : V L = 0 := by
    change mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f u L) 0 (1 : ℝ) = 0
    have hconst : (fun u : ℝ => f u L) = (fun _ : ℝ => f 0 L) := by funext u; exact hfixL u
    rw [hconst, mfderiv_const]; rfl
  -- Interval-integrability of the boundary derivative `hbd'`.
  -- `hbd := ⟨V, γ'⟩` is `C^∞` (inner product of two smooth sections), so
  -- `deriv hbd` is continuous; and `hbd' = deriv hbd` by `hbdry`.
  set hbd : ℝ → ℝ := fun s : ℝ => g.inner (γ s) (V s) (γ' s) with hbd_def
  set hbd' : ℝ → ℝ := fun t : ℝ =>
    g.inner (γ t) (covDerivAlong (I := I) g γ V t) (γ' t)
      + g.inner (γ t) (V t) (covDerivAlong (I := I) g γ γ' t) with hbd'_def
  -- Total-space smoothness of `V` (swapped variation) and `γ'`.
  have hfswap : IsSmoothVariation (I := I) (fun a b : ℝ => f b a) := by
    have hswapmap : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) ∞
        (fun q : ℝ × ℝ => (q.2, q.1)) := contMDiff_snd.prodMk contMDiff_fst
    exact (hf : ContMDiff _ _ _ _).comp hswapmap
  have hVtotal : ContMDiff (𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, E)) ∞ (fun t : ℝ =>
      (TotalSpace.mk' E (E := (TangentSpace I : M → Type _)) (γ t) (V t) : TangentBundle I M)) := by
    have hbase := velocity_totalSpace_contMDiff (I := I) (M := M) (fun a b : ℝ => f b a) hfswap
    have hcomp := hbase.comp
      (contMDiff_id.prodMk contMDiff_const : ContMDiff (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) ∞
        (fun t : ℝ => (t, (0 : ℝ))))
    refine hcomp.congr (fun t => ?_)
    rfl
  have hγ'total : ContMDiff (𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, E)) ∞ (fun t : ℝ =>
      (TotalSpace.mk' E (E := (TangentSpace I : M → Type _)) (γ t) (γ' t) : TangentBundle I M)) := by
    have hbase := velocity_totalSpace_contMDiff (I := I) (M := M) f hf
    have hcomp := hbase.comp
      (contMDiff_const.prodMk contMDiff_id : ContMDiff (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) ∞
        (fun t : ℝ => ((0 : ℝ), t)))
    refine hcomp.congr (fun t => ?_)
    rfl
  -- `hbd` is `C^∞`.
  have hbd_contdiff : ContDiff ℝ ∞ hbd :=
    g_inner_along_curve_contMDiff (I := I) (M := M) g hVtotal hγ'total
  -- `deriv hbd` is continuous, and `hbd' = deriv hbd`.
  have hderiv_cont : Continuous (deriv hbd) := hbd_contdiff.continuous_deriv (by simp)
  have hbd'_eq_deriv : ∀ t : ℝ, hbd' t = deriv hbd t := by
    intro t
    have hd : HasDerivAt hbd (hbd' t) t := by
      have := metric_compat_hasDerivAt_inner (I := I) g γ V γ' t hγ_smooth (hVdiff t) (hγ'diff t)
      exact this
    exact (hd.deriv).symm
  have hbd'_cont : Continuous hbd' := by
    refine hderiv_cont.congr (fun t => (hbd'_eq_deriv t).symm)
  have hbd'_int : IntervalIntegrable hbd' MeasureTheory.volume 0 L :=
    hbd'_cont.continuousOn.intervalIntegrable
  -- (5) FTC: `∫₀ᴸ hbd' = hbd L - hbd 0 = 0` (boundary values vanish since `V 0 = V L = 0`).
  have hFTC : (∫ t in (0 : ℝ)..L, hbd' t) = hbd L - hbd 0 := by
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t ht => ?_) hbd'_int
    exact metric_compat_hasDerivAt_inner (I := I) g γ V γ' t hγ_smooth (hVdiff t) (hγ'diff t)
  have hbdL0 : hbd L = 0 := by
    change g.inner (γ L) (V L) (γ' L) = 0
    rw [hVL, map_zero, ContinuousLinearMap.zero_apply]
  have hbd00 : hbd 0 = 0 := by
    change g.inner (γ 0) (V 0) (γ' 0) = 0
    rw [hV0, map_zero, ContinuousLinearMap.zero_apply]
  rw [hbdL0, hbd00, sub_zero] at hFTC
  -- (6) `A t := ⟨∇_t V, γ'⟩` is continuous: it equals `½ ∂_s speedSq|₀`, the
  -- partial derivative of the jointly-`C^∞` speed-squared (`S1`/`S2` reasoning).
  set A : ℝ → ℝ := fun t : ℝ => g.inner (γ t) (covDerivAlong (I := I) g γ V t) (γ' t)
    with hA_def
  -- `A t = ½ D2num t` where `D2num t := 2 ⟨∇_s ∂_t f|₀, ∂_t f⟩` is the `S1` numerator.
  set D2num : ℝ → ℝ := fun t : ℝ =>
    2 * g.inner (f 0 t)
      (covDerivAlong (I := I) g (fun s : ℝ => f s t)
        (fun s : ℝ => mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f s u) t (1 : ℝ)) 0)
      (mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f 0 u) t (1 : ℝ)) with hD2num_def
  -- `D2num` is continuous: it is the partial `s`-derivative of the jointly-`C^∞`
  -- speed-squared `G := fun p => speedSq g f p.1 p.2` at `(0, t)`.
  have hG : ContDiff ℝ ∞ (fun p : ℝ × ℝ => speedSq (I := I) g f p.1 p.2) :=
    speedSq_contDiff (I := I) (M := M) g f hf
  have hD2num_eq : ∀ t : ℝ,
      D2num t = fderiv ℝ (fun p : ℝ × ℝ => speedSq (I := I) g f p.1 p.2) (0, t) (1, 0) := by
    intro t
    have hS1 := S1_moving_foot_metric_compatibility (I := I) g f t hf
    have hslice : HasDerivAt
        (fun u : ℝ => (fun p : ℝ × ℝ => speedSq (I := I) g f p.1 p.2) (u, t))
        (fderiv ℝ (fun p : ℝ × ℝ => speedSq (I := I) g f p.1 p.2) (0, t) (1, 0)) 0 := by
      have hdiff : DifferentiableAt ℝ (fun p : ℝ × ℝ => speedSq (I := I) g f p.1 p.2) (0, t) :=
        (hG.differentiable (by simp)).differentiableAt
      have := Aux2.hasDerivAt_slice_fst
        (fun u v : ℝ => speedSq (I := I) g f u v) 0 t hdiff
      simpa using this
    have hS1' : HasDerivAt
        (fun u : ℝ => (fun p : ℝ × ℝ => speedSq (I := I) g f p.1 p.2) (u, t)) (D2num t) 0 := by
      simpa [hD2num_def] using hS1
    exact hS1'.unique hslice
  have hD2num_cont : Continuous D2num := by
    have hc : Continuous (fun p : ℝ × ℝ => fderiv ℝ (fun q : ℝ × ℝ =>
        speedSq (I := I) g f q.1 q.2) p) := hG.continuous_fderiv (by simp)
    have hcapp : Continuous (fun p : ℝ × ℝ => fderiv ℝ (fun q : ℝ × ℝ =>
        speedSq (I := I) g f q.1 q.2) p (1, 0)) := hc.clm_apply continuous_const
    have : Continuous (fun t : ℝ =>
        fderiv ℝ (fun q : ℝ × ℝ => speedSq (I := I) g f q.1 q.2) (0, t) (1, 0)) :=
      hcapp.comp (continuous_const.prodMk continuous_id)
    exact this.congr (fun t => (hD2num_eq t).symm)
  -- `A t = ½ D2num t` (via the intrinsic commutation `∇_s ∂_t f = ∇_t V`).
  have hA_eq_half : ∀ t : ℝ, A t = D2num t / 2 := by
    intro t
    change g.inner (γ t) (covDerivAlong (I := I) g γ V t) (γ' t)
      = (2 * g.inner (f 0 t)
          (covDerivAlong (I := I) g (fun s : ℝ => f s t)
            (fun s : ℝ => mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f s u) t (1 : ℝ)) 0)
          (mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f 0 u) t (1 : ℝ))) / 2
    have hcomm := commute_ds_dt_intrinsic (I := I) g f hf t
    rw [show covDerivAlong (I := I) g γ V t
        = covDerivAlong (I := I) g (fun s : ℝ => f s t)
            (fun s : ℝ => mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f s u) t (1 : ℝ)) 0 from by
      rw [hγ_def, hV_def]; rw [hcomm]]
    rw [hγ'_def, hγ_def]; ring
  have hA_cont : Continuous A := by
    have : A = (fun t : ℝ => D2num t / 2) := by funext t; exact hA_eq_half t
    rw [this]; exact hD2num_cont.div_const 2
  have hA_int : IntervalIntegrable A MeasureTheory.volume 0 L :=
    hA_cont.continuousOn.intervalIntegrable
  -- (7) `B t := ⟨V, ∇_t γ'⟩ = hbd' t - A t` is continuous, hence integrable.
  set B : ℝ → ℝ := fun t : ℝ => g.inner (γ t) (V t) (covDerivAlong (I := I) g γ γ' t)
    with hB_def
  have hB_eq : ∀ t : ℝ, B t = hbd' t - A t := by
    intro t; rw [hB_def, hbd'_def, hA_def]; ring
  have hB_cont : Continuous B := by
    have : B = (fun t : ℝ => hbd' t - A t) := by funext t; exact hB_eq t
    rw [this]; exact hbd'_cont.sub hA_cont
  have hB_int : IntervalIntegrable B MeasureTheory.volume 0 L :=
    hB_cont.continuousOn.intervalIntegrable
  -- (8) `∫ hbd' = ∫ A + ∫ B = 0`, so `∫ A = -∫ B`.
  have hsplit : (∫ t in (0 : ℝ)..L, hbd' t)
      = (∫ t in (0 : ℝ)..L, A t) + (∫ t in (0 : ℝ)..L, B t) := by
    rw [← intervalIntegral.integral_add hA_int hB_int]
  rw [hsplit] at hFTC
  -- `∫ A = -∫ B`.
  have hAB : (∫ t in (0 : ℝ)..L, A t) = - (∫ t in (0 : ℝ)..L, B t) := by linarith [hFTC]
  -- (9) The `S2` derivative value is `∫ A`; the target is `-∫ B`.
  -- `hS2 : HasDerivAt (∫√speedSq) (∫ A) 0`; rewrite the value to `-∫ B = target`.
  have hS2A : HasDerivAt
      (fun s : ℝ => ∫ t in (0 : ℝ)..L, Real.sqrt (speedSq (I := I) g f s t))
      (∫ t in (0 : ℝ)..L, A t) 0 := hS2
  rw [hAB] at hS2A
  -- The target value is `-∫ B`; rewrite `B` to the target integrand.
  exact hS2A

/-- **Free-endpoint first variation of arc length.** Same setup as
`first_variation_formula` but without the endpoint-fixed hypotheses: for a smooth
unit-speed variation `f` of `γ := f 0`, the derivative of
`s ↦ arcLength g (f s ·) 0 L` at `s = 0` equals the boundary term
`⟨V L, γ' L⟩ - ⟨V 0, γ' 0⟩` minus the integral of `⟨V, ∇_t γ'⟩_g`, where
`V t := ∂_s f|_{s = 0}` is the variation field and `γ' t := ∂_t (f 0)` is the
central velocity. (When the endpoints are fixed, `V 0 = V L = 0` and the boundary
term vanishes, recovering `first_variation_formula`.) -/
theorem first_variation_formula_free_endpoint
    (g : SmoothRiemannianMetric I M) (f : ℝ → ℝ → M) (L : ℝ)
    (hf : IsSmoothVariation (I := I) f) (hL : 0 < L)
    (hUnit : ∀ t ∈ Set.Icc (0 : ℝ) L,
      g.inner (f 0 t)
          (mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f 0 u) t (1 : ℝ))
          (mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f 0 u) t (1 : ℝ)) = 1) :
    HasDerivAt (fun s : ℝ => arcLength (I := I) g (fun t : ℝ => f s t) 0 L)
      ( (g.inner (f 0 L)
          (mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f u L) 0 (1 : ℝ))
          (mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f 0 u) L (1 : ℝ))
         - g.inner (f 0 0)
          (mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f u 0) 0 (1 : ℝ))
          (mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f 0 u) 0 (1 : ℝ)))
        - ∫ t in (0 : ℝ)..L,
          g.inner (f 0 t)
            (mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f u t) 0 (1 : ℝ))
            (DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong.covDerivAlong
              (I := I) g (fun v : ℝ => f 0 v)
              (fun v : ℝ =>
                mfderiv (𝓘(ℝ, ℝ)) I (fun w : ℝ => f 0 w) v (1 : ℝ)) t)) 0 := by
  classical
  open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong in
  -- Abbreviations: central curve `γ`, variation field `V`, central velocity `γ'`.
  set γ : ℝ → M := fun v : ℝ => f 0 v with hγ_def
  set V : ∀ t : ℝ, TangentSpace I (γ t) :=
    fun t : ℝ => mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f u t) 0 (1 : ℝ) with hV_def
  set γ' : ∀ t : ℝ, TangentSpace I (γ t) :=
    fun t : ℝ => mfderiv (𝓘(ℝ, ℝ)) I (fun w : ℝ => f 0 w) t (1 : ℝ) with hγ'_def
  -- (0) The unit-speed hypothesis rewritten as `speedSq g f 0 t = 1` on `[0, L]`.
  have hUnit' : ∀ t ∈ Set.Icc (0 : ℝ) L, speedSq (I := I) g f 0 t = 1 := by
    intro t ht; exact hUnit t ht
  -- (1) The arc-length slice is the integral of `√(speedSq)`.
  have harc : (fun s : ℝ => arcLength (I := I) g (fun t : ℝ => f s t) 0 L)
      = (fun s : ℝ => ∫ t in (0 : ℝ)..L, Real.sqrt (speedSq (I := I) g f s t)) := by
    funext s; exact arcLength_slice_eq_integral_sqrt_speedSq (I := I) g f s L
  rw [harc]
  -- (2) Differentiate under the integral (`S2`).
  have hS2 := S2_diff_under_interval_integral (I := I) g f L hf hL hUnit'
  -- (3) The `S2` derivative value equals `∫₀ᴸ ⟨∇_t V, γ'⟩` after using `√(speedSq) = 1`
  -- and the intrinsic commutation `∇_s ∂_t f = ∇_t V`.
  have hsqrt1 : ∀ t ∈ Set.Icc (0 : ℝ) L, Real.sqrt (speedSq (I := I) g f 0 t) = 1 := by
    intro t ht; rw [hUnit' t ht, Real.sqrt_one]
  -- The `S2` integrand simplifies to `⟨∇_t V, γ'⟩` on `[0, L]`.
  have hintegrand_eq : Set.EqOn
      (fun t : ℝ =>
        (2 * g.inner (f 0 t)
          (covDerivAlong (I := I) g (fun s : ℝ => f s t)
            (fun s : ℝ => mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f s u) t (1 : ℝ)) 0)
          (mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f 0 u) t (1 : ℝ)))
          / (2 * Real.sqrt (speedSq (I := I) g f 0 t)))
      (fun t : ℝ => g.inner (γ t) (covDerivAlong (I := I) g γ V t) (γ' t))
      (Set.uIcc 0 L) := by
    intro t ht
    rw [Set.uIcc_of_le (le_of_lt hL)] at ht
    simp only []
    rw [hsqrt1 t ht, mul_one]
    -- `∇_s ∂_t f|₀ = ∇_t V` by `commute_ds_dt_intrinsic`.
    have hcomm := commute_ds_dt_intrinsic (I := I) g f hf t
    -- `covDerivAlong g γ V t` is the RHS of the commutation.
    rw [show covDerivAlong (I := I) g (fun s : ℝ => f s t)
          (fun s : ℝ => mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f s u) t (1 : ℝ)) 0
        = covDerivAlong (I := I) g γ V t from by
      rw [hcomm, hγ_def, hV_def]]
    rw [hγ'_def, hγ_def]
    ring
  rw [intervalIntegral.integral_congr hintegrand_eq] at hS2
  -- (4) Integration by parts via metric compatibility (`metric_compat_hasDerivAt_inner`).
  -- The boundary function `h t := ⟨V t, γ' t⟩` has derivative `⟨∇_t V, γ'⟩ + ⟨V, ∇_t γ'⟩`.
  have hγ_smooth : ContMDiff (𝓘(ℝ, ℝ)) I ∞ γ := by
    have hincl : ContMDiff (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) ∞ (fun v : ℝ => ((0 : ℝ), v)) :=
      contMDiff_const.prodMk contMDiff_id
    exact (hf : ContMDiff _ _ _ _).comp hincl
  -- Chart-rep differentiability of `V` and `γ'` at every `t₀`.
  have hVdiff : ∀ t₀ : ℝ, DifferentiableAt ℝ (chartRepAt (I := I) γ V t₀) t₀ := by
    intro t₀; rw [hγ_def, hV_def]
    exact variationField_chartRep_differentiableAt (I := I) g f hf t₀
  have hγ'diff : ∀ t₀ : ℝ, DifferentiableAt ℝ (chartRepAt (I := I) γ γ' t₀) t₀ := by
    intro t₀; rw [hγ_def, hγ'_def]
    exact velocityField_chartRep_differentiableAt (I := I) g f hf t₀
  -- The boundary derivative everywhere on `[0, L]`.
  have hbdry : ∀ t ∈ Set.uIcc (0 : ℝ) L,
      HasDerivAt (fun s : ℝ => g.inner (γ s) (V s) (γ' s))
        (g.inner (γ t) (covDerivAlong (I := I) g γ V t) (γ' t)
          + g.inner (γ t) (V t) (covDerivAlong (I := I) g γ γ' t)) t := by
    intro t _ht
    exact metric_compat_hasDerivAt_inner (I := I) g γ V γ' t hγ_smooth (hVdiff t) (hγ'diff t)
  -- Interval-integrability of the boundary derivative `hbd'`.
  -- `hbd := ⟨V, γ'⟩` is `C^∞` (inner product of two smooth sections), so
  -- `deriv hbd` is continuous; and `hbd' = deriv hbd` by `hbdry`.
  set hbd : ℝ → ℝ := fun s : ℝ => g.inner (γ s) (V s) (γ' s) with hbd_def
  set hbd' : ℝ → ℝ := fun t : ℝ =>
    g.inner (γ t) (covDerivAlong (I := I) g γ V t) (γ' t)
      + g.inner (γ t) (V t) (covDerivAlong (I := I) g γ γ' t) with hbd'_def
  -- Total-space smoothness of `V` (swapped variation) and `γ'`.
  have hfswap : IsSmoothVariation (I := I) (fun a b : ℝ => f b a) := by
    have hswapmap : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) ∞
        (fun q : ℝ × ℝ => (q.2, q.1)) := contMDiff_snd.prodMk contMDiff_fst
    exact (hf : ContMDiff _ _ _ _).comp hswapmap
  have hVtotal : ContMDiff (𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, E)) ∞ (fun t : ℝ =>
      (TotalSpace.mk' E (E := (TangentSpace I : M → Type _)) (γ t) (V t) : TangentBundle I M)) := by
    have hbase := velocity_totalSpace_contMDiff (I := I) (M := M) (fun a b : ℝ => f b a) hfswap
    have hcomp := hbase.comp
      (contMDiff_id.prodMk contMDiff_const : ContMDiff (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) ∞
        (fun t : ℝ => (t, (0 : ℝ))))
    refine hcomp.congr (fun t => ?_)
    rfl
  have hγ'total : ContMDiff (𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, E)) ∞ (fun t : ℝ =>
      (TotalSpace.mk' E (E := (TangentSpace I : M → Type _)) (γ t) (γ' t) : TangentBundle I M)) := by
    have hbase := velocity_totalSpace_contMDiff (I := I) (M := M) f hf
    have hcomp := hbase.comp
      (contMDiff_const.prodMk contMDiff_id : ContMDiff (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) ∞
        (fun t : ℝ => ((0 : ℝ), t)))
    refine hcomp.congr (fun t => ?_)
    rfl
  -- `hbd` is `C^∞`.
  have hbd_contdiff : ContDiff ℝ ∞ hbd :=
    g_inner_along_curve_contMDiff (I := I) (M := M) g hVtotal hγ'total
  -- `deriv hbd` is continuous, and `hbd' = deriv hbd`.
  have hderiv_cont : Continuous (deriv hbd) := hbd_contdiff.continuous_deriv (by simp)
  have hbd'_eq_deriv : ∀ t : ℝ, hbd' t = deriv hbd t := by
    intro t
    have hd : HasDerivAt hbd (hbd' t) t := by
      have := metric_compat_hasDerivAt_inner (I := I) g γ V γ' t hγ_smooth (hVdiff t) (hγ'diff t)
      exact this
    exact (hd.deriv).symm
  have hbd'_cont : Continuous hbd' := by
    refine hderiv_cont.congr (fun t => (hbd'_eq_deriv t).symm)
  have hbd'_int : IntervalIntegrable hbd' MeasureTheory.volume 0 L :=
    hbd'_cont.continuousOn.intervalIntegrable
  -- (5) FTC: `∫₀ᴸ hbd' = hbd L - hbd 0`.  The boundary term is *kept*.
  have hFTC : (∫ t in (0 : ℝ)..L, hbd' t) = hbd L - hbd 0 := by
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t ht => ?_) hbd'_int
    exact metric_compat_hasDerivAt_inner (I := I) g γ V γ' t hγ_smooth (hVdiff t) (hγ'diff t)
  -- (6) `A t := ⟨∇_t V, γ'⟩` is continuous: it equals `½ ∂_s speedSq|₀`, the
  -- partial derivative of the jointly-`C^∞` speed-squared (`S1`/`S2` reasoning).
  set A : ℝ → ℝ := fun t : ℝ => g.inner (γ t) (covDerivAlong (I := I) g γ V t) (γ' t)
    with hA_def
  -- `A t = ½ D2num t` where `D2num t := 2 ⟨∇_s ∂_t f|₀, ∂_t f⟩` is the `S1` numerator.
  set D2num : ℝ → ℝ := fun t : ℝ =>
    2 * g.inner (f 0 t)
      (covDerivAlong (I := I) g (fun s : ℝ => f s t)
        (fun s : ℝ => mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f s u) t (1 : ℝ)) 0)
      (mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f 0 u) t (1 : ℝ)) with hD2num_def
  -- `D2num` is continuous: it is the partial `s`-derivative of the jointly-`C^∞`
  -- speed-squared `G := fun p => speedSq g f p.1 p.2` at `(0, t)`.
  have hG : ContDiff ℝ ∞ (fun p : ℝ × ℝ => speedSq (I := I) g f p.1 p.2) :=
    speedSq_contDiff (I := I) (M := M) g f hf
  have hD2num_eq : ∀ t : ℝ,
      D2num t = fderiv ℝ (fun p : ℝ × ℝ => speedSq (I := I) g f p.1 p.2) (0, t) (1, 0) := by
    intro t
    have hS1 := S1_moving_foot_metric_compatibility (I := I) g f t hf
    have hslice : HasDerivAt
        (fun u : ℝ => (fun p : ℝ × ℝ => speedSq (I := I) g f p.1 p.2) (u, t))
        (fderiv ℝ (fun p : ℝ × ℝ => speedSq (I := I) g f p.1 p.2) (0, t) (1, 0)) 0 := by
      have hdiff : DifferentiableAt ℝ (fun p : ℝ × ℝ => speedSq (I := I) g f p.1 p.2) (0, t) :=
        (hG.differentiable (by simp)).differentiableAt
      have := Aux2.hasDerivAt_slice_fst
        (fun u v : ℝ => speedSq (I := I) g f u v) 0 t hdiff
      simpa using this
    have hS1' : HasDerivAt
        (fun u : ℝ => (fun p : ℝ × ℝ => speedSq (I := I) g f p.1 p.2) (u, t)) (D2num t) 0 := by
      simpa [hD2num_def] using hS1
    exact hS1'.unique hslice
  have hD2num_cont : Continuous D2num := by
    have hc : Continuous (fun p : ℝ × ℝ => fderiv ℝ (fun q : ℝ × ℝ =>
        speedSq (I := I) g f q.1 q.2) p) := hG.continuous_fderiv (by simp)
    have hcapp : Continuous (fun p : ℝ × ℝ => fderiv ℝ (fun q : ℝ × ℝ =>
        speedSq (I := I) g f q.1 q.2) p (1, 0)) := hc.clm_apply continuous_const
    have : Continuous (fun t : ℝ =>
        fderiv ℝ (fun q : ℝ × ℝ => speedSq (I := I) g f q.1 q.2) (0, t) (1, 0)) :=
      hcapp.comp (continuous_const.prodMk continuous_id)
    exact this.congr (fun t => (hD2num_eq t).symm)
  -- `A t = ½ D2num t` (via the intrinsic commutation `∇_s ∂_t f = ∇_t V`).
  have hA_eq_half : ∀ t : ℝ, A t = D2num t / 2 := by
    intro t
    change g.inner (γ t) (covDerivAlong (I := I) g γ V t) (γ' t)
      = (2 * g.inner (f 0 t)
          (covDerivAlong (I := I) g (fun s : ℝ => f s t)
            (fun s : ℝ => mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f s u) t (1 : ℝ)) 0)
          (mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f 0 u) t (1 : ℝ))) / 2
    have hcomm := commute_ds_dt_intrinsic (I := I) g f hf t
    rw [show covDerivAlong (I := I) g γ V t
        = covDerivAlong (I := I) g (fun s : ℝ => f s t)
            (fun s : ℝ => mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f s u) t (1 : ℝ)) 0 from by
      rw [hγ_def, hV_def]; rw [hcomm]]
    rw [hγ'_def, hγ_def]; ring
  have hA_cont : Continuous A := by
    have : A = (fun t : ℝ => D2num t / 2) := by funext t; exact hA_eq_half t
    rw [this]; exact hD2num_cont.div_const 2
  have hA_int : IntervalIntegrable A MeasureTheory.volume 0 L :=
    hA_cont.continuousOn.intervalIntegrable
  -- (7) `B t := ⟨V, ∇_t γ'⟩ = hbd' t - A t` is continuous, hence integrable.
  set B : ℝ → ℝ := fun t : ℝ => g.inner (γ t) (V t) (covDerivAlong (I := I) g γ γ' t)
    with hB_def
  have hB_eq : ∀ t : ℝ, B t = hbd' t - A t := by
    intro t; rw [hB_def, hbd'_def, hA_def]; ring
  have hB_cont : Continuous B := by
    have : B = (fun t : ℝ => hbd' t - A t) := by funext t; exact hB_eq t
    rw [this]; exact hbd'_cont.sub hA_cont
  have hB_int : IntervalIntegrable B MeasureTheory.volume 0 L :=
    hB_cont.continuousOn.intervalIntegrable
  -- (8) `∫ hbd' = ∫ A + ∫ B = hbd L - hbd 0`, so `∫ A = (hbd L - hbd 0) - ∫ B`.
  have hsplit : (∫ t in (0 : ℝ)..L, hbd' t)
      = (∫ t in (0 : ℝ)..L, A t) + (∫ t in (0 : ℝ)..L, B t) := by
    rw [← intervalIntegral.integral_add hA_int hB_int]
  rw [hsplit] at hFTC
  -- `∫ A = (hbd L - hbd 0) - ∫ B`.
  have hAB : (∫ t in (0 : ℝ)..L, A t) = (hbd L - hbd 0) - (∫ t in (0 : ℝ)..L, B t) := by
    linarith [hFTC]
  -- (9) The `S2` derivative value is `∫ A`; rewrite it to `(hbd L - hbd 0) - ∫ B`,
  -- which is the target boundary-plus-integral value.
  have hS2A : HasDerivAt
      (fun s : ℝ => ∫ t in (0 : ℝ)..L, Real.sqrt (speedSq (I := I) g f s t))
      (∫ t in (0 : ℝ)..L, A t) 0 := hS2
  rw [hAB] at hS2A
  -- `hbd L - hbd 0 = ⟨V L, γ' L⟩ - ⟨V 0, γ' 0⟩`, the target boundary term, and
  -- `∫ B` is the target integral; both fold definitionally to the goal.
  exact hS2A

/-! ## First variation vanishes along a geodesic -/

/-- For a unit-speed geodesic `γ` and any endpoint-fixed smooth
variation `f` whose central curve is `γ`, the first variation of
arc length at `s = 0` vanishes. -/
theorem first_variation_vanishes_for_geodesic
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M) (f : ℝ → ℝ → M) (L : ℝ)
    (hf : IsSmoothVariation (I := I) f) (hL : 0 < L)
    (hγ : IsGeodesicOn (I := I) g γ (Set.Icc 0 L)) (hfc : ∀ t : ℝ, f 0 t = γ t)
    (hfix0 : ∀ s : ℝ, f s 0 = γ 0) (hfixL : ∀ s : ℝ, f s L = γ L)
    (hUnit : ∀ t ∈ Set.Icc (0 : ℝ) L,
      g.inner (γ t)
          (mfderiv (𝓘(ℝ, ℝ)) I γ t (1 : ℝ))
          (mfderiv (𝓘(ℝ, ℝ)) I γ t (1 : ℝ)) = 1) :
    HasDerivAt (fun s : ℝ => arcLength (I := I) g (fun t : ℝ => f s t) 0 L)
      0 0 := by
  classical
  open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong in
  -- The central curve `f 0 ·` coincides with `γ`.
  have hfγ : (fun v : ℝ => f 0 v) = γ := by funext v; exact hfc v
  -- Apply the first variation formula; its value is `-∫ ⟨V, ∇_t γ'⟩`.
  have hfv := first_variation_formula (I := I) g f L hf hL
    (fun s => by rw [hfix0 s, ← hfc 0]) (fun s => by rw [hfixL s, ← hfc L])
    (by
      intro t ht
      rw [hfc t, hfγ]; exact hUnit t ht)
  -- The integrand `⟨V, ∇_t γ'⟩` vanishes on `[0, L]`: `γ` is a geodesic, so
  -- `∇_t γ' = covDerivAlong g γ γ' = 0`.
  have hsmooth_central : ContMDiff (𝓘(ℝ, ℝ)) I ∞ (fun v : ℝ => f 0 v) := by
    have hincl : ContMDiff (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) ∞ (fun v : ℝ => ((0 : ℝ), v)) :=
      contMDiff_const.prodMk contMDiff_id
    exact (hf : ContMDiff _ _ _ _).comp hincl
  have hγ_smooth : ContMDiff (𝓘(ℝ, ℝ)) I ∞ γ := hfγ ▸ hsmooth_central
  -- `covDerivAlong g (f 0 ·) γ' t = 0` for `t ∈ [0, L]`.
  have haccel0 : ∀ t ∈ Set.Icc (0 : ℝ) L,
      covDerivAlong (I := I) g (fun v : ℝ => f 0 v)
        (fun v : ℝ => mfderiv (𝓘(ℝ, ℝ)) I (fun w : ℝ => f 0 w) v (1 : ℝ)) t = 0 := by
    intro t ht
    have hgeo : HasGeodesicEquationAt (I := I) g γ t := hγ t ht
    have hzero : covDerivAlong (I := I) g γ
        (fun s => (mfderiv 𝓘(ℝ, ℝ) I γ s : ℝ →L[ℝ] _) (1 : ℝ)) t = 0 :=
      (covDerivAlong_velocity_eq_zero_iff_hasGeodesicEquationAt (I := I) g γ t hγ_smooth).mpr hgeo
    rw [hfγ]; exact hzero
  -- Hence the integrand vanishes on `[0, L]`, so the integral is `0`.
  have hint0 : (∫ t in (0 : ℝ)..L,
      g.inner (f 0 t)
        (mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f u t) 0 (1 : ℝ))
        (covDerivAlong (I := I) g (fun v : ℝ => f 0 v)
          (fun v : ℝ => mfderiv (𝓘(ℝ, ℝ)) I (fun w : ℝ => f 0 w) v (1 : ℝ)) t)) = 0 := by
    have hcongr : (∫ t in (0 : ℝ)..L,
        g.inner (f 0 t)
          (mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f u t) 0 (1 : ℝ))
          (covDerivAlong (I := I) g (fun v : ℝ => f 0 v)
            (fun v : ℝ => mfderiv (𝓘(ℝ, ℝ)) I (fun w : ℝ => f 0 w) v (1 : ℝ)) t))
        = ∫ _t in (0 : ℝ)..L, (0 : ℝ) := by
      refine intervalIntegral.integral_congr (fun t ht => ?_)
      rw [Set.uIcc_of_le (le_of_lt hL)] at ht
      rw [haccel0 t ht, map_zero]
    rw [hcongr, intervalIntegral.integral_zero]
  -- The first-variation value is `-0 = 0`.
  rw [hint0, neg_zero] at hfv
  exact hfv

/-! ## Intrinsic curvature commutation on a variation -/

open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong in
/-- **Chart-coordinate of the intrinsic covariant derivative, in any foot chart.**
For a `C^∞` curve `γ`, a section `V` along `γ` whose canonical foot-chart
representation is differentiable at `t`, and any basepoint `β` with `γ t` in its
chart source, the chart-`β`-coordinate of the intrinsic covariant derivative
`covDerivAlong g γ V t` is the chart-`β` covariant derivative of the
chart-`β`-coordinate representation `chartRepAtBase β γ V`.

This is the forward companion of `covDerivAlong_chart_foot_invariance`: applying
the forward chart-`β` coordinate map `continuousLinearMapAt β (γ t)` to that
lemma's identity (and using `continuousLinearMapAt ∘ symmL = id` on the base set)
produces the chart-`β` covariant derivative directly. -/
private lemma chartCoord_covDerivAlong_eq_chartCovDerivAlong_chartRepAtBase
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M) (V : ∀ t, TangentSpace I (γ t))
    (t : ℝ) (β : M)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ) (hβ : γ t ∈ (chartAt H β).source)
    (hV : DifferentiableAt ℝ (chartRepAt (I := I) γ V t) t) :
    (trivializationAt E (TangentSpace I) β).continuousLinearMapAt ℝ (γ t)
        (covDerivAlong (I := I) g γ V t)
      = chartCovDerivAlong (I := I) g β γ (chartRepAtBase (I := I) β γ V) t := by
  have hinv := covDerivAlong_chart_foot_invariance (I := I) g γ V t β hγ hβ hV
  rw [← hinv]
  have hmem : γ t ∈ (trivializationAt E (TangentSpace I) β).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]; exact hβ
  exact (trivializationAt E (TangentSpace I) β).continuousLinearMapAt_symmL (R := ℝ) hmem _

open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong in
/-- **Differentiability of the velocity chart-rep along an arbitrary slice.** For a
smooth variation `f` and any `u`, the pinned chart-`(f u t₀)`-coordinate
representation of the longitudinal velocity field `v ↦ ∂_t f|_{(u, v)}` is
differentiable at `t₀`. This is `velocityField_chartRep_differentiableAt`
transported to the slice `f u ·` via the reparametrisation `(a, b) ↦ f (u + a) b`,
whose central slice at `a = 0` is `f u ·`. -/
private lemma slice_velocityField_chartRep_differentiableAt
    (g : SmoothRiemannianMetric I M) (f : ℝ → ℝ → M)
    (hf : IsSmoothVariation (I := I) f) (u t₀ : ℝ) :
    DifferentiableAt ℝ
      (chartRepAt (I := I) (fun v : ℝ => f u v)
        (fun v : ℝ => mfderiv (𝓘(ℝ, ℝ)) I (fun w : ℝ => f u w) v (1 : ℝ)) t₀) t₀ := by
  have hf' : IsSmoothVariation (I := I) (fun a b : ℝ => f (u + a) b) := by
    have hcomp : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) ∞
        (fun p : ℝ × ℝ => (u + p.1, p.2)) :=
      (contMDiff_const.add contMDiff_fst).prodMk contMDiff_snd
    exact (hf : ContMDiff _ _ _ _).comp hcomp
  have h := velocityField_chartRep_differentiableAt (I := I) g (fun a b : ℝ => f (u + a) b) hf' t₀
  have hrw : (fun a b : ℝ => f (u + a) b) = (fun a b : ℝ => f (u + a) b) := rfl
  -- `(fun a b => f (u+a) b) 0 = fun v => f (u+0) v`; rewrite `u + 0` to `u`.
  have hval : (u + 0 : ℝ) = u := add_zero u
  rw [hval] at h
  exact h

open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong in
/-- **Differentiability of the longitudinal-velocity chart-rep along a transverse
slice.** For a smooth variation `f` and any `v`, the pinned chart-`(f 0 v)`-
coordinate representation of the longitudinal velocity field `u ↦ ∂_t f|_{(u, v)}`
(read along the transverse slice `f · v`) is differentiable at `0`. Near `0` it
agrees with the partial Fréchet derivative `u ↦ fderiv_w (extChartAt (f 0 v)
(f u w)) v 1` of the jointly-`C^∞` chart-pull `(u, w) ↦ extChartAt (f 0 v) (f u w)`,
which is `C^∞` in `u`. -/
private lemma slice_longitudinalField_transverse_chartRep_differentiableAt
    (_g : SmoothRiemannianMetric I M) (f : ℝ → ℝ → M)
    (hf : IsSmoothVariation (I := I) f) (v : ℝ) :
    DifferentiableAt ℝ
      (chartRepAt (I := I) (fun u : ℝ => f u v)
        (fun u : ℝ => mfderiv (𝓘(ℝ, ℝ)) I (fun w : ℝ => f u w) v (1 : ℝ)) 0) 0 := by
  classical
  set α : M := f 0 v with hα
  have hslice_u : ∀ s : ℝ, ContMDiff (𝓘(ℝ, ℝ)) I ∞ (fun w : ℝ => f s w) := by
    intro s
    have hincl : ContMDiff (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) ∞ (fun w : ℝ => (s, w)) :=
      contMDiff_const.prodMk contMDiff_id
    exact (hf : ContMDiff _ _ _ _).comp hincl
  have htransverse : ContMDiff (𝓘(ℝ, ℝ)) I ∞ (fun u : ℝ => f u v) := by
    have hincl : ContMDiff (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) ∞ (fun u : ℝ => (u, v)) :=
      contMDiff_id.prodMk contMDiff_const
    exact (hf : ContMDiff _ _ _ _).comp hincl
  -- The smooth model section: `u ↦ fderiv_w (extChartAt α (f u w)) v 1`.
  set sec : ℝ → E := fun u : ℝ => fderiv ℝ (fun w : ℝ => extChartAt I α (f u w)) v (1 : ℝ)
    with hsec
  -- It is `C^∞` at `0`: the partial fderiv (in `w` at `v`) of the jointly-smooth chart-pull,
  -- evaluated at `1`, varying `u`.
  have hsec_cdiff : ContDiffAt ℝ ∞ sec 0 := by
    have hsrc0 : f 0 v ∈ (chartAt H α).source := by rw [hα]; exact mem_chart_source H (f 0 v)
    have hjoint : ContDiffAt ℝ ∞
        (Function.uncurry (fun u w : ℝ => extChartAt I α (f u w))) (0, v) := by
      have h := chartPulled_contDiffAt_infty (I := I) f hf α 0 v hsrc0
      exact h
    have hgv : ContDiffAt ℝ ∞ (fun _ : ℝ => v) 0 := contDiffAt_const
    have hpartial : ContDiffAt ℝ ∞
        (fun u : ℝ => fderiv ℝ (fun w : ℝ => extChartAt I α (f u w)) ((fun _ : ℝ => v) u)) 0 :=
      ContDiffAt.fderiv (𝕜 := ℝ)
        (f := fun u w : ℝ => extChartAt I α (f u w)) (g := fun _ : ℝ => v)
        hjoint hgv (by rw [show (∞ : WithTop ℕ∞) + 1 = ∞ from rfl])
    exact (ContinuousLinearMap.apply ℝ E (1 : ℝ)).contDiff.contDiffAt.comp 0 hpartial
  -- The chart-rep agrees with `sec` near `0`.
  have hopen : IsOpen {u : ℝ | f u v ∈ (chartAt H α).source} :=
    htransverse.continuous.isOpen_preimage _ (chartAt H α).open_source
  have h0 : (0 : ℝ) ∈ {u : ℝ | f u v ∈ (chartAt H α).source} := by
    show f 0 v ∈ (chartAt H α).source; rw [hα]; exact mem_chart_source H (f 0 v)
  have heq : (chartRepAt (I := I) (fun u : ℝ => f u v)
      (fun u : ℝ => mfderiv (𝓘(ℝ, ℝ)) I (fun w : ℝ => f u w) v (1 : ℝ)) 0)
        =ᶠ[𝓝 (0 : ℝ)] sec := by
    filter_upwards [hopen.mem_nhds h0] with u hu
    have hsrc : (fun w : ℝ => f u w) v ∈ (chartAt H α).source := hu
    have hbridge := MFDerivAlongCurve.chartCoord_mfderiv_along_curve_eq_fderiv
      (I := I) (M := M) (γ := fun w : ℝ => f u w) (hslice_u u) α (t := v) hsrc
    change (trivializationAt E (TangentSpace I) ((fun u : ℝ => f u v) 0)).continuousLinearMapAt ℝ
        ((fun u : ℝ => f u v) u) (mfderiv (𝓘(ℝ, ℝ)) I (fun w : ℝ => f u w) v (1 : ℝ)) = sec u
    rw [hsec, show (fun u : ℝ => f u v) 0 = α from hα.symm]
    have hcompfun : ((extChartAt I α) ∘ (fun w : ℝ => f u w))
        = (fun w : ℝ => extChartAt I α (f u w)) := rfl
    rw [hcompfun] at hbridge
    exact hbridge
  exact (heq.differentiableAt_iff).mpr (hsec_cdiff.differentiableAt (by simp))

open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong in
/-- **Joint `C²`-regularity of the chart-`(f 0 t)`-coordinate longitudinal velocity.**
The function `(u, v) ↦ φ_{f 0 t}(∂_t f|_{(u, v)})`, i.e. the chart-`(f 0 t)`-
coordinate of the longitudinal velocity `∂_t f`, is `C²` jointly at `(0, t)`. Near
`(0, t)` it agrees with the partial Fréchet derivative
`(u, v) ↦ fderiv_w (extChartAt (f 0 t) (f u w)) v 1` of the jointly-`C^∞`
chart-pull `(u, v) ↦ extChartAt (f 0 t) (f u v)`, which is `C^∞`. -/
private lemma chartCoord_longitudinalVelocity_contDiffAt
    (f : ℝ → ℝ → M) (hf : IsSmoothVariation (I := I) f) (t : ℝ) :
    ContDiffAt ℝ 2 (fun p : ℝ × ℝ =>
        (trivializationAt E (TangentSpace I) (f 0 t)).continuousLinearMapAt ℝ (f p.1 p.2)
          (mfderiv (𝓘(ℝ, ℝ)) I (fun w : ℝ => f p.1 w) p.2 (1 : ℝ))) (0, t) := by
  classical
  set β : M := f 0 t with hβ
  -- Joint `C^∞` of the chart-pull `F (u, v) := extChartAt β (f u v)` near `(0, t)`.
  have hsrc0 : f 0 t ∈ (chartAt H β).source := by rw [hβ]; exact mem_chart_source H (f 0 t)
  have hF : ContDiffAt ℝ ∞ (fun p : ℝ × ℝ => extChartAt I β (f p.1 p.2)) (0, t) :=
    chartPulled_contDiffAt_infty (I := I) f hf β 0 t hsrc0
  -- The model section: `Ymodel p := fderiv F p (0, 1)`, jointly `C^∞`, hence `C²`.
  have hfd : ContDiffAt ℝ ∞ (fderiv ℝ (fun q : ℝ × ℝ => extChartAt I β (f q.1 q.2))) (0, t) :=
    hF.fderiv_right (m := ∞) (by rw [show (∞ : WithTop ℕ∞) + 1 = ∞ from rfl])
  have hYmodel : ContDiffAt ℝ 2 (fun p : ℝ × ℝ =>
      fderiv ℝ (fun q : ℝ × ℝ => extChartAt I β (f q.1 q.2)) p (0, 1)) (0, t) :=
    ((ContinuousLinearMap.apply ℝ E ((0, 1) : ℝ × ℝ)).contDiff.contDiffAt.comp (0, t)
      hfd).of_le (by norm_cast)
  -- Slice smoothness for the bridge `chartCoord_mfderiv_along_curve_eq_fderiv`.
  have hslice_u : ∀ s : ℝ, ContMDiff (𝓘(ℝ, ℝ)) I ∞ (fun w : ℝ => f s w) := by
    intro s
    have hincl : ContMDiff (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) ∞ (fun w : ℝ => (s, w)) :=
      contMDiff_const.prodMk contMDiff_id
    exact (hf : ContMDiff _ _ _ _).comp hincl
  -- The chart-pull is jointly continuous (from `hF`), so `f u v ∈ source β` is open
  -- in `(u, v)` and holds near `(0, t)`.
  have hf_cont : Continuous (fun p : ℝ × ℝ => f p.1 p.2) := hf.continuous
  have hopen : IsOpen {p : ℝ × ℝ | f p.1 p.2 ∈ (chartAt H β).source} :=
    hf_cont.isOpen_preimage _ (chartAt H β).open_source
  have hmem0 : (0, t) ∈ {p : ℝ × ℝ | f p.1 p.2 ∈ (chartAt H β).source} := by
    show f 0 t ∈ (chartAt H β).source; exact hsrc0
  -- On that open neighbourhood, the goal function agrees with `Ymodel`.
  have heq : (fun p : ℝ × ℝ =>
      (trivializationAt E (TangentSpace I) β).continuousLinearMapAt ℝ (f p.1 p.2)
        (mfderiv (𝓘(ℝ, ℝ)) I (fun w : ℝ => f p.1 w) p.2 (1 : ℝ)))
        =ᶠ[𝓝 (0, t)]
      (fun p : ℝ × ℝ => fderiv ℝ (fun q : ℝ × ℝ => extChartAt I β (f q.1 q.2)) p (0, 1)) := by
    filter_upwards [hopen.mem_nhds hmem0] with p hp
    have hsrc : (fun w : ℝ => f p.1 w) p.2 ∈ (chartAt H β).source := hp
    have hbridge := MFDerivAlongCurve.chartCoord_mfderiv_along_curve_eq_fderiv
      (I := I) (M := M) (γ := fun w : ℝ => f p.1 w) (hslice_u p.1) β (t := p.2) hsrc
    -- `(extChartAt β ∘ (f p.1 ·)) = fun w => extChartAt β (f p.1 w)`, and its `fderiv 1`
    -- equals the joint partial fderiv `fderiv F p (0, 1)`.
    have hcompfun : ((extChartAt I β) ∘ (fun w : ℝ => f p.1 w))
        = (fun w : ℝ => extChartAt I β (f p.1 w)) := rfl
    rw [hcompfun] at hbridge
    rw [hbridge]
    -- Convert the slice fderiv to the joint partial fderiv at `p` via the inclusion
    -- chain rule `w ↦ (p.1, w)`.
    have hdiffJoint : DifferentiableAt ℝ (fun q : ℝ × ℝ => extChartAt I β (f q.1 q.2)) p := by
      have hC1 : ContDiffAt ℝ 1 (fun q : ℝ × ℝ => extChartAt I β (f q.1 q.2)) p :=
        (chartPulled_contDiffAt_infty (I := I) f hf β p.1 p.2 hsrc).of_le (by norm_cast)
      exact hC1.differentiableAt (by simp)
    have hincl : HasFDerivAt (fun w : ℝ => (p.1, w)) (ContinuousLinearMap.inr ℝ ℝ ℝ) p.2 :=
      hasFDerivAt_prodMk_right p.1 p.2
    have hG : HasFDerivAt (fun q : ℝ × ℝ => extChartAt I β (f q.1 q.2))
        (fderiv ℝ (fun q : ℝ × ℝ => extChartAt I β (f q.1 q.2)) p) p :=
      hdiffJoint.hasFDerivAt
    have hch := hG.comp p.2 hincl
    have hcompfun2 : (fun w : ℝ => extChartAt I β (f p.1 w))
        = (fun q : ℝ × ℝ => extChartAt I β (f q.1 q.2)) ∘ (fun w : ℝ => (p.1, w)) := rfl
    rw [hcompfun2, hch.fderiv]
    simp [ContinuousLinearMap.inr]
  exact hYmodel.congr_of_eventuallyEq heq

open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong in
/-- **Intrinsic curvature commutation on a smooth variation.** For a smooth
two-parameter variation `f`, the commutator of the transverse and longitudinal
covariant derivatives of the longitudinal velocity field `∂_t f`, evaluated at the
central curve `s = 0`, equals the Riemann curvature operator of the Levi-Civita
connection applied to the transverse velocity `V := ∂_s f|_{s = 0}`, the
longitudinal velocity `γ' := ∂_t f|_{s = 0}`, and `γ'`:
`∇_s ∇_t (∂_t f) − ∇_t ∇_s (∂_t f) = R(V, γ') γ'`, with all covariant derivatives
the intrinsic `covDerivAlong` at the common foot `f 0 t`.

The two transverse/longitudinal derivative orders are pinned at the moving feet
`f s t` and `f 0 v` respectively, so the second-order commutator mixes a chart at
the outer foot `f s t` with the inner covariant derivative living in the moving
foot chart. `covDerivAlong_chart_foot_invariance` re-expresses every nested
intrinsic covariant derivative in the single common chart `f 0 t`, where the
already-proven chart-level identity
`curvature_identity_on_variation_fixed_chart` applies; the round-trip identities
at the foot then transport back to the intrinsic answer.

The hypotheses `houterL`/`houterR` are the genuine regularity assumptions that the
nested covariant-derivative fields vary differentiably in chart coordinates (the
same hypothesis class that `covDerivAlong_chart_foot_invariance` itself consumes);
they are not restatements of the conclusion. -/
private theorem commute_ds_dt_curvature
    (g : SmoothRiemannianMetric I M) (f : ℝ → ℝ → M)
    (hf : IsSmoothVariation (I := I) f) (t : ℝ)
    (houterL : DifferentiableAt ℝ (chartRepAt (I := I) (fun s : ℝ => f s t)
        (fun s : ℝ => covDerivAlong (I := I) g (fun v : ℝ => f s v)
          (fun v : ℝ => mfderiv (𝓘(ℝ, ℝ)) I (fun w : ℝ => f s w) v (1 : ℝ)) t) 0) 0)
    (houterR : DifferentiableAt ℝ (chartRepAt (I := I) (fun v : ℝ => f 0 v)
        (fun v : ℝ => covDerivAlong (I := I) g (fun u : ℝ => f u v)
          (fun u : ℝ => mfderiv (𝓘(ℝ, ℝ)) I (fun w : ℝ => f u w) v (1 : ℝ)) 0) t) t) :
    covDerivAlong (I := I) g (fun s : ℝ => f s t)
        (fun s : ℝ => covDerivAlong (I := I) g (fun v : ℝ => f s v)
          (fun v : ℝ => mfderiv (𝓘(ℝ, ℝ)) I (fun w : ℝ => f s w) v (1 : ℝ)) t) 0
      - covDerivAlong (I := I) g (fun v : ℝ => f 0 v)
        (fun v : ℝ => covDerivAlong (I := I) g (fun u : ℝ => f u v)
          (fun u : ℝ => mfderiv (𝓘(ℝ, ℝ)) I (fun w : ℝ => f u w) v (1 : ℝ)) 0) t
      = (DifferentialGeometry.Integral.Connection.riemannOp
          (DifferentialGeometry.Integral.Connection.LeviCivita (I := I) g) (f 0 t))
          (mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f u t) 0 (1 : ℝ))
          (mfderiv (𝓘(ℝ, ℝ)) I (fun w : ℝ => f 0 w) t (1 : ℝ))
          (mfderiv (𝓘(ℝ, ℝ)) I (fun w : ℝ => f 0 w) t (1 : ℝ)) := by
  classical
  set β : M := f 0 t with hβ
  -- Slice smoothness.
  have hslice_u : ∀ s : ℝ, ContMDiff (𝓘(ℝ, ℝ)) I ∞ (fun w : ℝ => f s w) := by
    intro s
    have hincl : ContMDiff (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) ∞ (fun w : ℝ => (s, w)) :=
      contMDiff_const.prodMk contMDiff_id
    exact (hf : ContMDiff _ _ _ _).comp hincl
  have hslice_v : ∀ v : ℝ, ContMDiff (𝓘(ℝ, ℝ)) I ∞ (fun w : ℝ => f w v) := by
    intro v
    have hincl : ContMDiff (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) ∞ (fun w : ℝ => (w, v)) :=
      contMDiff_id.prodMk contMDiff_const
    exact (hf : ContMDiff _ _ _ _).comp hincl
  have htransverse : ContMDiff (𝓘(ℝ, ℝ)) I ∞ (fun s : ℝ => f s t) := hslice_v t
  have hcentral : ContMDiff (𝓘(ℝ, ℝ)) I ∞ (fun v : ℝ => f 0 v) := hslice_u 0
  -- Abbreviation for the longitudinal velocity section `∂_t f`.
  set velT : ℝ → ℝ → E :=
    fun s v => mfderiv (𝓘(ℝ, ℝ)) I (fun w : ℝ => f s w) v (1 : ℝ) with hvelT
  -- The chart-`β`-coordinate of the longitudinal velocity, the `Y` of the fixed-chart
  -- curvature identity. Both inner orders of the commutator differentiate the SAME field
  -- `∂_t f`, so both use this single section `Y`.
  set Y : ℝ → ℝ → E := fun u v =>
    (trivializationAt E (TangentSpace I) β).continuousLinearMapAt ℝ (f u v) (velT u v) with hY
  -- `Y u ·` is the chart-`β`-coordinate representation of `∂_t f` along the slice `f u ·`.
  have hY_chartRepAtBase_u : ∀ u : ℝ,
      (fun v : ℝ => Y u v)
        = chartRepAtBase (I := I) β (fun w : ℝ => f u w) (fun w : ℝ => velT u w) := by
    intro u; funext v; rw [hY, chartRepAtBase_apply]
  -- `Y · v` is the chart-`β`-coordinate representation of `∂_t f` along the slice `f · v`.
  have hY_chartRepAtBase_v : ∀ v : ℝ,
      (fun u : ℝ => Y u v)
        = chartRepAtBase (I := I) β (fun w : ℝ => f w v) (fun w : ℝ => velT w v) := by
    intro v; funext u; rw [hY, chartRepAtBase_apply]
  -- `Y` is jointly `C²` at `(0, t)`.
  have hY_C2 : ContDiffAt ℝ 2 (fun p : ℝ × ℝ => Y p.1 p.2) (0, t) :=
    chartCoord_longitudinalVelocity_contDiffAt (I := I) f hf t
  -- The fixed-chart curvature identity for `Y` at `(0, t)`.
  have hfixed := curvature_identity_on_variation_fixed_chart (I := I) g f hf Y 0 t hY_C2
  -- (A) Open neighbourhood facts: `f s t ∈ source β` near `s = 0`, `f 0 v ∈ source β` near `v = t`.
  have hsrcβ : f 0 t ∈ (chartAt H β).source := by rw [hβ]; exact mem_chart_source H (f 0 t)
  have hopenL : IsOpen {s : ℝ | f s t ∈ (chartAt H β).source} :=
    htransverse.continuous.isOpen_preimage _ (chartAt H β).open_source
  have h0L : (0 : ℝ) ∈ {s : ℝ | f s t ∈ (chartAt H β).source} := hsrcβ
  have hopenR : IsOpen {v : ℝ | f 0 v ∈ (chartAt H β).source} :=
    hcentral.continuous.isOpen_preimage _ (chartAt H β).open_source
  have h0R : t ∈ {v : ℝ | f 0 v ∈ (chartAt H β).source} := hsrcβ
  -- The longitudinal velocity along the slice `f · v`, as a transverse-velocity field
  -- (the slice differentiability discharger needs the velocity field of `f w v` in `v`; but
  -- here the inner field is `w ↦ velT w v = ∂_t f`, differentiated transversally, whose
  -- chart-rep differentiability is supplied below from `Y`'s joint `C²`).
  -- (B) Inner bridges (conditional on the foot lying in `source β`):
  --   the fixed-chart inner expression is the chart-`β`-coordinate of the intrinsic inner.
  have hinnerL : ∀ s : ℝ, f s t ∈ (chartAt H β).source →
      chartCovDerivAlong (I := I) g β (fun v : ℝ => f s v) (fun v : ℝ => Y s v) t
        = (trivializationAt E (TangentSpace I) β).continuousLinearMapAt ℝ (f s t)
            (covDerivAlong (I := I) g (fun v : ℝ => f s v) (fun v : ℝ => velT s v) t) := by
    intro s hs
    rw [hY_chartRepAtBase_u s]
    exact (chartCoord_covDerivAlong_eq_chartCovDerivAlong_chartRepAtBase (I := I) g
      (fun w : ℝ => f s w) (fun w : ℝ => velT s w) t β (hslice_u s) hs
      (slice_velocityField_chartRep_differentiableAt (I := I) g f hf s t)).symm
  -- The right inner field `u ↦ velT u v = ∂_t f` along `f · v` has differentiable chart-rep at `0`.
  have hinnerR_diff : ∀ v : ℝ, DifferentiableAt ℝ
      (chartRepAt (I := I) (fun u : ℝ => f u v) (fun u : ℝ => velT u v) 0) 0 := fun v =>
    slice_longitudinalField_transverse_chartRep_differentiableAt (I := I) g f hf v
  have hinnerR : ∀ v : ℝ, f 0 v ∈ (chartAt H β).source →
      chartCovDerivAlong (I := I) g β (fun u : ℝ => f u v) (fun u : ℝ => Y u v) 0
        = (trivializationAt E (TangentSpace I) β).continuousLinearMapAt ℝ (f 0 v)
            (covDerivAlong (I := I) g (fun u : ℝ => f u v) (fun u : ℝ => velT u v) 0) := by
    intro v hv
    rw [hY_chartRepAtBase_v v]
    exact (chartCoord_covDerivAlong_eq_chartCovDerivAlong_chartRepAtBase (I := I) g
      (fun w : ℝ => f w v) (fun w : ℝ => velT w v) 0 β (hslice_v v) hv (hinnerR_diff v)).symm
  -- (C) The outer sections agree, near the basepoint, with the fixed-chart inner sections.
  set innerL : ∀ s : ℝ, TangentSpace I ((fun s : ℝ => f s t) s) :=
    fun s => covDerivAlong (I := I) g (fun v : ℝ => f s v) (fun v : ℝ => velT s v) t with hinnerL_def
  set innerR : ∀ v : ℝ, TangentSpace I ((fun v : ℝ => f 0 v) v) :=
    fun v => covDerivAlong (I := I) g (fun u : ℝ => f u v) (fun u : ℝ => velT u v) 0 with hinnerR_def
  have hrepL_eq : chartRepAt (I := I) (fun s : ℝ => f s t) innerL 0
      =ᶠ[𝓝 (0 : ℝ)]
        (fun s : ℝ => chartCovDerivAlong (I := I) g β (fun v : ℝ => f s v) (fun v : ℝ => Y s v) t) := by
    filter_upwards [hopenL.mem_nhds h0L] with s hs
    rw [chartRepAt_apply]
    -- The chart-rep foot `(fun s => f s t) 0 = f 0 t = β`; expose `innerL` and reverse `hinnerL`.
    show (trivializationAt E (TangentSpace I) β).continuousLinearMapAt ℝ (f s t) (innerL s) = _
    rw [hinnerL_def, ← hinnerL s hs]
  have hrepR_eq : chartRepAt (I := I) (fun v : ℝ => f 0 v) innerR t
      =ᶠ[𝓝 t]
        (fun v : ℝ => chartCovDerivAlong (I := I) g β (fun u : ℝ => f u v) (fun u : ℝ => Y u v) 0) := by
    filter_upwards [hopenR.mem_nhds h0R] with v hv
    rw [chartRepAt_apply]
    show (trivializationAt E (TangentSpace I) β).continuousLinearMapAt ℝ (f 0 v) (innerR v) = _
    rw [hinnerR_def, ← hinnerR v hv]
  -- (D) Outer bridges.
  have houterL_bridge :
      (trivializationAt E (TangentSpace I) β).continuousLinearMapAt ℝ ((fun s : ℝ => f s t) 0)
          (covDerivAlong (I := I) g (fun s : ℝ => f s t) innerL 0)
        = chartCovDerivAlong (I := I) g β (fun s : ℝ => f s t)
            (fun s : ℝ => chartCovDerivAlong (I := I) g β (fun v : ℝ => f s v)
              (fun v : ℝ => Y s v) t) 0 := by
    rw [chartCoord_covDerivAlong_eq_chartCovDerivAlong_chartRepAtBase (I := I) g
      (fun s : ℝ => f s t) innerL 0 β htransverse (by rw [hβ] at hsrcβ ⊢; exact hsrcβ) houterL]
    rw [show chartRepAtBase (I := I) β (fun s : ℝ => f s t) innerL
        = chartRepAt (I := I) (fun s : ℝ => f s t) innerL 0 from
      chartRepAtBase_foot (I := I) (fun s : ℝ => f s t) innerL 0]
    rw [chartCovDerivAlong_def, chartCovDerivAlong_def, hrepL_eq.deriv_eq, hrepL_eq.eq_of_nhds]
  have houterR_bridge :
      (trivializationAt E (TangentSpace I) β).continuousLinearMapAt ℝ ((fun v : ℝ => f 0 v) t)
          (covDerivAlong (I := I) g (fun v : ℝ => f 0 v) innerR t)
        = chartCovDerivAlong (I := I) g β (fun v : ℝ => f 0 v)
            (fun v : ℝ => chartCovDerivAlong (I := I) g β (fun u : ℝ => f u v)
              (fun u : ℝ => Y u v) 0) t := by
    rw [chartCoord_covDerivAlong_eq_chartCovDerivAlong_chartRepAtBase (I := I) g
      (fun v : ℝ => f 0 v) innerR t β hcentral (by rw [hβ] at hsrcβ ⊢; exact hsrcβ) houterR]
    rw [show chartRepAtBase (I := I) β (fun v : ℝ => f 0 v) innerR
        = chartRepAt (I := I) (fun v : ℝ => f 0 v) innerR t from
      chartRepAtBase_foot (I := I) (fun v : ℝ => f 0 v) innerR t]
    rw [chartCovDerivAlong_def, chartCovDerivAlong_def, hrepR_eq.deriv_eq, hrepR_eq.eq_of_nhds]
  -- (E) Assemble: round-trip at the foot, then apply the fixed-chart identity.
  have hfootOuterL : (fun s : ℝ => f s t) 0 = β := by rw [hβ]
  have hfootOuterR : (fun v : ℝ => f 0 v) t = β := by rw [hβ]
  have hmemβ : β ∈ (trivializationAt E (TangentSpace I) β).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) β
  have hLeft : covDerivAlong (I := I) g (fun s : ℝ => f s t) innerL 0
      = (trivializationAt E (TangentSpace I) β).symmL ℝ β
          (chartCovDerivAlong (I := I) g β (fun s : ℝ => f s t)
            (fun s : ℝ => chartCovDerivAlong (I := I) g β (fun v : ℝ => f s v)
              (fun v : ℝ => Y s v) t) 0) := by
    rw [← houterL_bridge, hfootOuterL]
    exact ((trivializationAt E (TangentSpace I) β).symmL_continuousLinearMapAt
      (R := ℝ) hmemβ _).symm
  have hRight : covDerivAlong (I := I) g (fun v : ℝ => f 0 v) innerR t
      = (trivializationAt E (TangentSpace I) β).symmL ℝ β
          (chartCovDerivAlong (I := I) g β (fun v : ℝ => f 0 v)
            (fun v : ℝ => chartCovDerivAlong (I := I) g β (fun u : ℝ => f u v)
              (fun u : ℝ => Y u v) 0) t) := by
    rw [← houterR_bridge, hfootOuterR]
    exact ((trivializationAt E (TangentSpace I) β).symmL_continuousLinearMapAt
      (R := ℝ) hmemβ _).symm
  -- The goal's LHS sections are `innerL`, `innerR` (defeq).
  show covDerivAlong (I := I) g (fun s : ℝ => f s t) innerL 0
      - covDerivAlong (I := I) g (fun v : ℝ => f 0 v) innerR t = _
  rw [hLeft, hRight, ← map_sub]
  -- Apply the fixed-chart curvature identity: the commutator equals `riemannOp` on `Y 0 t`.
  rw [hfixed]
  -- Convert the three remaining mismatches:
  -- (i) `symmL_β β = id` at the foot (round trip);
  -- (ii) `Y 0 t = mfderiv (f 0 ·) t 1` (foot `clmAt = id`, `velT 0 t = mfderiv`);
  -- (iii) the two `fderiv` tangent slots equal the corresponding `mfderiv` fibre vectors.
  -- Foot membership in `source (f 0 t)`.
  have hfoot_src : f 0 t ∈ (chartAt H (f 0 t)).source := mem_chart_source H (f 0 t)
  -- At the foot, the forward and inverse trivialisation coordinate maps are the identity.
  have hfoot_clm : ∀ x : TangentSpace I (f 0 t),
      (trivializationAt E (TangentSpace I) (f 0 t)).continuousLinearMapAt ℝ (f 0 t) x = x := by
    intro x
    rw [TangentBundle.continuousLinearMapAt_trivializationAt_eq_core (I := I) hfoot_src]
    exact (tangentBundleCore I M).coordChange_self (achart H (f 0 t)) (f 0 t)
      (mem_achart_source H (f 0 t)) x
  have hfoot_symmL : ∀ x : TangentSpace I (f 0 t),
      (trivializationAt E (TangentSpace I) (f 0 t)).symmL ℝ (f 0 t) x = x := by
    intro x
    rw [TangentBundle.symmL_trivializationAt_eq_core (I := I) hfoot_src]
    exact (tangentBundleCore I M).coordChange_self (achart H (f 0 t)) (f 0 t)
      (mem_achart_source H (f 0 t)) x
  -- (iii) `fderiv (extChartAt (f 0 t) (f · t)) 0 1 = mfderiv (f · t) 0 1`.
  have hslotS : (fderiv ℝ (fun u : ℝ => extChartAt I (f 0 t) (f u t)) 0 (1 : ℝ))
      = (mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f u t) 0 (1 : ℝ) : E) := by
    have hbridge := MFDerivAlongCurve.chartCoord_mfderiv_along_curve_eq_fderiv
      (I := I) (M := M) (γ := fun u : ℝ => f u t) (hslice_v t) (f 0 t) (t := 0)
      (by show f 0 t ∈ (chartAt H (f 0 t)).source; exact hfoot_src)
    have hcompfun : ((extChartAt I (f 0 t)) ∘ (fun u : ℝ => f u t))
        = (fun u : ℝ => extChartAt I (f 0 t) (f u t)) := rfl
    rw [hcompfun, hfoot_clm] at hbridge
    exact hbridge.symm
  have hslotT : (fderiv ℝ (fun v : ℝ => extChartAt I (f 0 t) (f 0 v)) t (1 : ℝ))
      = (mfderiv (𝓘(ℝ, ℝ)) I (fun w : ℝ => f 0 w) t (1 : ℝ) : E) := by
    have hbridge := MFDerivAlongCurve.chartCoord_mfderiv_along_curve_eq_fderiv
      (I := I) (M := M) (γ := fun w : ℝ => f 0 w) (hslice_u 0) (f 0 t) (t := t)
      (by show f 0 t ∈ (chartAt H (f 0 t)).source; exact hfoot_src)
    have hcompfun : ((extChartAt I (f 0 t)) ∘ (fun w : ℝ => f 0 w))
        = (fun w : ℝ => extChartAt I (f 0 t) (f 0 w)) := rfl
    rw [hcompfun, hfoot_clm] at hbridge
    exact hbridge.symm
  -- (ii) `Y 0 t = mfderiv (f 0 ·) t 1`.
  have hYft : Y 0 t = (mfderiv (𝓘(ℝ, ℝ)) I (fun w : ℝ => f 0 w) t (1 : ℝ) : E) := by
    rw [hY]
    show (trivializationAt E (TangentSpace I) β).continuousLinearMapAt ℝ (f 0 t) (velT 0 t)
      = mfderiv (𝓘(ℝ, ℝ)) I (fun w : ℝ => f 0 w) t (1 : ℝ)
    rw [hβ, hfoot_clm]
  -- Rewrite the two tangent slots and the fibre slot, then collapse `symmL_β β` at the foot.
  rw [hslotS, hslotT, hYft]
  rw [show (trivializationAt E (TangentSpace I) β).symmL ℝ β
        = (trivializationAt E (TangentSpace I) (f 0 t)).symmL ℝ (f 0 t) from by rw [hβ]]
  rw [hfoot_symmL]

/-! ## First variation at a general parameter value -/

open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong in
/-- **Affine-shift covariance of the intrinsic covariant derivative along a
curve.** Reparametrising the base curve `γ` and the section `V` by the affine
shift `a ↦ c + a` translates the covariant derivative: evaluating the
reparametrised covariant derivative at `a = 0` recovers the original covariant
derivative at the parameter `c`. The chart pinned at the foot `γ c` is the same
on both sides, and `deriv` is invariant under the domain translation
(`deriv_comp_const_add`), so the chart-local covariant derivative agrees term by
term. -/
private lemma covDerivAlong_const_add_shift
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (V : ∀ s : ℝ, TangentSpace I (γ s)) (c : ℝ) :
    covDerivAlong (I := I) g (fun a : ℝ => γ (c + a))
        (fun a : ℝ => V (c + a)) 0
      = covDerivAlong (I := I) g γ V c := by
  classical
  -- The shifted curve and section reduce at `a = 0` to the original foot `γ c`.
  have hfoot : γ (c + 0) = γ c := by rw [add_zero]
  -- The chart-rep of the shifted section is the shift of the chart-rep.
  have hrep : chartRepAt (I := I) (fun a : ℝ => γ (c + a)) (fun a : ℝ => V (c + a)) 0
      = (fun a : ℝ => chartRepAt (I := I) γ V c (c + a)) := by
    funext a
    rw [chartRepAt_apply, chartRepAt_apply]
    -- The forward chart maps coincide: foot `(fun a => γ (c+a)) 0 = γ c`,
    -- and the running point `(fun a => γ (c+a)) a = γ (c+a)`.
    simp only [add_zero]
  -- The chart trajectory of the shifted curve is the shift of the chart trajectory.
  have hcurve : chartCurve (I := I) (γ c) (fun a : ℝ => γ (c + a))
      = (fun a : ℝ => chartCurve (I := I) (γ c) γ (c + a)) := by
    funext a; rw [chartCurve_def, chartCurve_def]
  -- The two chart-local covariant derivatives agree, in the common chart at `γ c`.
  have hchart : chartCovDerivAlong (I := I) g (γ c) (fun a : ℝ => γ (c + a))
        (chartRepAt (I := I) (fun a : ℝ => γ (c + a)) (fun a : ℝ => V (c + a)) 0) 0
      = chartCovDerivAlong (I := I) g (γ c) γ (chartRepAt (I := I) γ V c) c := by
    rw [chartCovDerivAlong_def, chartCovDerivAlong_def, hrep, hcurve]
    -- The two `deriv`s translate (`deriv_comp_const_add`); values at `0` map to `c`.
    rw [deriv_comp_const_add (chartRepAt (I := I) γ V c) c 0,
        deriv_comp_const_add (chartCurve (I := I) (γ c) γ) c 0]
    simp only [add_zero]
  -- Both unfold to `symmL` at the common foot; transport along `hfoot`, `hchart`.
  rw [covDerivAlong_def, covDerivAlong_def]
  rw [hfoot]
  rw [hchart]

/-- **Local positive lower bound for the speed near a regular parameter value.**
For a smooth two-parameter variation `f` whose slice `t ↦ f s₀ t` is regular
(positive speed) on the compact interval `[0, L]`, there is an open
neighbourhood `Ioo (s₀ - δ) (s₀ + δ)` of `s₀` and a uniform positive constant
`c` with `c ≤ √(speedSq g f s t)` for every `(s, t)` in that neighbourhood times
`[0, L]`. This is the regularity hypothesis underlying differentiation under the
arc-length integral away from the central unit-speed curve. The proof takes the
compact minimum of the (continuous, positive) speed-squared on `{s₀} ×ˢ [0, L]`
and applies the tube lemma in the open superlevel set. -/
private theorem speed_positivity_near
    (g : SmoothRiemannianMetric I M) (f : ℝ → ℝ → M) (L s₀ : ℝ)
    (hf : IsSmoothVariation (I := I) f)
    (hpos : ∀ t ∈ Set.Icc (0 : ℝ) L, 0 < speedSq (I := I) g f s₀ t) :
    ∃ δ > (0 : ℝ), ∃ c > (0 : ℝ),
      ∀ s ∈ Set.Ioo (s₀ - δ) (s₀ + δ), ∀ t ∈ Set.Icc 0 L,
        c ≤ Real.sqrt (speedSq (I := I) g f s t) := by
  classical
  -- Continuity of `speedSq` in `(s, t)`.
  have hsq_cont : Continuous (fun p : ℝ × ℝ => speedSq (I := I) g f p.1 p.2) :=
    speedSq_continuous (I := I) (M := M) g f hf
  -- A uniform positive lower bound `m` for `speedSq g f s₀ ·` on the compact `[0, L]`.
  have hslice_cont : ContinuousOn (fun t : ℝ => speedSq (I := I) g f s₀ t) (Set.Icc 0 L) :=
    (hsq_cont.comp (continuous_const.prodMk continuous_id)).continuousOn
  obtain ⟨m, hm⟩ : ∃ m : ℝ, 0 < m ∧ ∀ t ∈ Set.Icc (0 : ℝ) L, m ≤ speedSq (I := I) g f s₀ t := by
    rcases (Set.eq_empty_or_nonempty (Set.Icc (0 : ℝ) L)) with hEmpty | hNe
    · refine ⟨1, one_pos, fun t ht => ?_⟩
      rw [hEmpty] at ht
      exact ((Set.mem_empty_iff_false t).mp ht).elim
    · obtain ⟨tm, htm_mem, htm_min⟩ :=
        isCompact_Icc.exists_isMinOn hNe hslice_cont
      exact ⟨speedSq (I := I) g f s₀ tm, hpos tm htm_mem, fun t ht => htm_min ht⟩
  obtain ⟨m_pos, hm_lb⟩ := hm
  -- The open superlevel set `S := speedSq⁻¹ (Ioi (m/2))` contains `{s₀} ×ˢ [0, L]`.
  have hS_open : IsOpen
      ((fun p : ℝ × ℝ => speedSq (I := I) g f p.1 p.2) ⁻¹' Set.Ioi (m / 2 : ℝ)) :=
    isOpen_Ioi.preimage hsq_cont
  have hZ_in_S :
      ({s₀} : Set ℝ) ×ˢ Set.Icc (0 : ℝ) L ⊆
        (fun p : ℝ × ℝ => speedSq (I := I) g f p.1 p.2) ⁻¹' Set.Ioi (m / 2 : ℝ) := by
    intro p hp
    rcases hp with ⟨hp1, hp2⟩
    have hp1' : p.1 = s₀ := hp1
    change (m / 2 : ℝ) < speedSq (I := I) g f p.1 p.2
    rw [hp1']
    have := hm_lb p.2 hp2
    linarith
  -- Tube lemma: a product neighbourhood `U × V ⊇ {s₀} ×ˢ [0, L]` lies in `S`.
  obtain ⟨U, V, hU_open, _hV_open, hs₀_in_U, hL_in_V, hUV_in_S⟩ :=
    generalized_tube_lemma isCompact_singleton (isCompact_Icc (a := (0 : ℝ)) (b := L))
      hS_open hZ_in_S
  have hs₀_in_U' : s₀ ∈ U := hs₀_in_U rfl
  rcases Metric.isOpen_iff.mp hU_open s₀ hs₀_in_U' with ⟨δ, δ_pos, hball_U⟩
  refine ⟨δ, δ_pos, Real.sqrt (m / 2), Real.sqrt_pos.mpr (by linarith), ?_⟩
  intro s hs t ht
  have hs_in_U : s ∈ U := by
    apply hball_U
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    rcases hs with ⟨h1, h2⟩
    constructor <;> linarith
  have ht_in_V : t ∈ V := hL_in_V ht
  have h_st_in_S : speedSq (I := I) g f s t > (m / 2 : ℝ) :=
    hUV_in_S (Set.mk_mem_prod hs_in_U ht_in_V)
  exact Real.sqrt_le_sqrt (le_of_lt h_st_in_S)

/-- **Differentiation under the interval integral for the arc-length speed, at a
general parameter value `s₀`.** For a smooth two-parameter variation `f` whose
slice `t ↦ f s₀ t` is regular (positive speed) on `[0, L]`, the `s`-derivative
at `s = s₀` of the slice arc-length integrand `∫₀^L √(speedSq g f s t) dt` equals
the interval integral of the pointwise `s`-derivative of `√(speedSq)`. By the
chain rule and `S1_moving_foot_metric_compatibility` reindexed at `s₀` through
the parameter shift, the pointwise derivative is
`(∂_s speedSq g f s₀ t) / (2 √(speedSq g f s₀ t))`. The regularity hypothesis at
`s₀` guarantees positivity of the speed on `[0, L]` and on a neighbourhood of
`s₀`, supplying the domination / Lipschitz data the Mathlib differentiation
engine consumes. This is the positivity-based generalisation of
`S2_diff_under_interval_integral` away from the unit-speed central curve. -/
private theorem S2_diff_under_interval_integral_general
    (g : SmoothRiemannianMetric I M) (f : ℝ → ℝ → M) (L s₀ : ℝ)
    (hf : IsSmoothVariation (I := I) f) (hL : 0 < L)
    (hpos : ∀ t ∈ Set.Icc (0 : ℝ) L, 0 < speedSq (I := I) g f s₀ t) :
    HasDerivAt
      (fun s : ℝ => ∫ t in (0 : ℝ)..L, Real.sqrt (speedSq (I := I) g f s t))
      (∫ t in (0 : ℝ)..L,
        fderiv ℝ (fun p : ℝ × ℝ => speedSq (I := I) g f p.1 p.2) (s₀, t) (1, 0)
          / (2 * Real.sqrt (speedSq (I := I) g f s₀ t)))
      s₀ := by
  classical
  -- Abbreviations: the speed-squared `Φ` and its uncurried form `G`.
  set Φ : ℝ → ℝ → ℝ := fun s t => speedSq (I := I) g f s t with hΦdef
  set G : ℝ × ℝ → ℝ := fun p : ℝ × ℝ => Φ p.1 p.2 with hG
  -- (1) `Φ = speedSq` is jointly `C^∞`.
  have hΦ : ContDiff ℝ ∞ G := by
    rw [hG, hΦdef]; exact speedSq_contDiff (I := I) (M := M) g f hf
  have hΦcont : Continuous G := hΦ.continuous
  -- (2) The pointwise `s`-derivative of the slice `Φ(·, t)` is `fderiv G (·, t) (1,0)`.
  have hΦdiff : ∀ p : ℝ × ℝ, DifferentiableAt ℝ G p :=
    fun p => (hΦ.differentiable (by simp)).differentiableAt
  have hslice_deriv : ∀ s t : ℝ,
      HasDerivAt (fun u : ℝ => Φ u t) (fderiv ℝ G (s, t) (1, 0)) s := by
    intro s t
    have := Aux2.hasDerivAt_slice_fst (fun u v => Φ u v) s t (hΦdiff (s, t))
    simpa only [hG] using this
  set Dnum : ℝ → ℝ := fun t : ℝ => fderiv ℝ G (s₀, t) (1, 0) with hDnum
  -- Continuity of the partial derivative `Dnum`.
  have hpartial_cont : Continuous (fun p : ℝ × ℝ => fderiv ℝ G p (1, 0)) := by
    have hc : Continuous (fun p : ℝ × ℝ => fderiv ℝ G p) :=
      hΦ.continuous_fderiv (by simp)
    exact hc.clm_apply continuous_const
  have hDcont : Continuous Dnum := by
    have : Continuous (fun t : ℝ => fderiv ℝ G (s₀, t) (1, 0)) :=
      hpartial_cont.comp (continuous_const.prodMk continuous_id)
    exact this
  -- (3) Positivity on a neighbourhood `Ioo (s₀-δ) (s₀+δ)` of `s₀`.
  obtain ⟨δ, hδ, c0, hc0, hposΦ⟩ :=
    speed_positivity_near (I := I) (M := M) g f L s₀ hf hpos
  set δ' : ℝ := δ / 2 with hδ'
  have hδ'pos : 0 < δ' := by positivity
  have hδ'lt : δ' < δ := by simp only [hδ']; linarith
  set Kset : Set (ℝ × ℝ) := Set.Icc (s₀ - δ') (s₀ + δ') ×ˢ Set.Icc 0 L with hKset
  have hKcompact : IsCompact Kset := (isCompact_Icc).prod isCompact_Icc
  have hKne : Kset.Nonempty :=
    ⟨(s₀, 0), ⟨⟨by linarith, by linarith⟩, ⟨le_refl 0, le_of_lt hL⟩⟩⟩
  obtain ⟨pm, hpmKset, hpmMax⟩ := hKcompact.exists_isMaxOn hKne
    ((continuous_norm.comp hpartial_cont).continuousOn)
  set K1 : ℝ := ‖fderiv ℝ G pm (1, 0)‖ with hK1
  have hK1nonneg : 0 ≤ K1 := norm_nonneg _
  -- Uniform positive lower bound `c0` for the speed on the compact box.
  have hsqrtlb : ∀ s ∈ Set.Icc (s₀ - δ') (s₀ + δ'), ∀ t ∈ Set.Icc (0 : ℝ) L,
      c0 ≤ Real.sqrt (Φ s t) := by
    intro s hs t ht
    refine hposΦ s ?_ t ht
    rcases hs with ⟨h1, h2⟩
    exact ⟨by linarith, by linarith⟩
  have hΦne : ∀ s ∈ Set.Icc (s₀ - δ') (s₀ + δ'), ∀ t ∈ Set.Icc (0 : ℝ) L, Φ s t ≠ 0 := by
    intro s hs t ht hcontra
    have hsqrt0 : Real.sqrt (Φ s t) = 0 := by rw [hcontra, Real.sqrt_zero]
    have := hsqrtlb s hs t ht
    rw [hsqrt0] at this; linarith
  -- The Lipschitz constant on the box.
  set C0 : ℝ := K1 / (2 * c0) with hC0
  have hC0nonneg : 0 ≤ C0 := by positivity
  -- Uniform Lipschitz bound of the slice `s ↦ √(Φ s t)` on `[s₀-δ', s₀+δ']`.
  have hlip : ∀ t ∈ Set.Icc (0 : ℝ) L,
      LipschitzOnWith C0.toNNReal (fun s => Real.sqrt (Φ s t))
        (Set.Icc (s₀ - δ') (s₀ + δ')) := by
    intro t ht
    apply Convex.lipschitzOnWith_of_nnnorm_deriv_le (𝕜 := ℝ) _ _ (convex_Icc _ _)
    · intro s hs
      exact ((hslice_deriv s t).sqrt (hΦne s hs t ht)).differentiableAt
    · intro s hs
      have hderiv_eq : deriv (fun u : ℝ => Real.sqrt (Φ u t)) s
          = fderiv ℝ G (s, t) (1, 0) / (2 * Real.sqrt (Φ s t)) :=
        ((hslice_deriv s t).sqrt (hΦne s hs t ht)).deriv
      have hnum_le : ‖fderiv ℝ G (s, t) (1, 0)‖ ≤ K1 :=
        hpmMax (⟨hs, ht⟩ : (s, t) ∈ Kset)
      have hden_ge : 2 * c0 ≤ 2 * Real.sqrt (Φ s t) := by
        have := hsqrtlb s hs t ht; linarith
      have hden_pos : (0 : ℝ) < 2 * Real.sqrt (Φ s t) := by
        have := hsqrtlb s hs t ht; linarith
      have hnorm_le : ‖deriv (fun u : ℝ => Real.sqrt (Φ u t)) s‖ ≤ C0 := by
        rw [hderiv_eq, norm_div, Real.norm_eq_abs (2 * Real.sqrt (Φ s t)),
          abs_of_nonneg (le_of_lt hden_pos), hC0,
          div_le_div_iff₀ hden_pos (by linarith : (0 : ℝ) < 2 * c0)]
        calc ‖fderiv ℝ G (s, t) (1, 0)‖ * (2 * c0)
              ≤ K1 * (2 * c0) :=
                mul_le_mul_of_nonneg_right hnum_le (by positivity)
          _ ≤ K1 * (2 * Real.sqrt (Φ s t)) :=
                mul_le_mul_of_nonneg_left hden_ge hK1nonneg
      have h1 : ‖deriv (fun u : ℝ => Real.sqrt (Φ u t)) s‖₊
          = Real.toNNReal ‖deriv (fun u : ℝ => Real.sqrt (Φ u t)) s‖ := by
        rw [Real.toNNReal_of_nonneg (norm_nonneg _)]; rfl
      rw [h1]; exact Real.toNNReal_le_toNNReal hnorm_le
  -- The interval-integral differentiation engine.
  set Ffun : ℝ → ℝ → ℝ := fun s t => Real.sqrt (Φ s t) with hFfun
  set Ffun' : ℝ → ℝ := fun t => Dnum t / (2 * Real.sqrt (Φ s₀ t)) with hFfun'
  have hFcont : ∀ s : ℝ, Continuous (Ffun s) := fun s =>
    Real.continuous_sqrt.comp (hΦcont.comp (continuous_const.prodMk continuous_id))
  have key := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_lip
    (μ := volume) (a := (0 : ℝ)) (b := L) (F := Ffun) (F' := Ffun') (x₀ := s₀)
    (bound := fun _ => C0) (s := Set.Ioo (s₀ - δ') (s₀ + δ'))
    (Ioo_mem_nhds (by linarith) (by linarith))
    (Filter.Eventually.of_forall (fun x => (hFcont x).aestronglyMeasurable))
    ((hFcont s₀).intervalIntegrable 0 L)
    (by
      have hden_cont : Continuous (fun t : ℝ => 2 * Real.sqrt (Φ s₀ t)) :=
        continuous_const.mul (Real.continuous_sqrt.comp
          (hΦcont.comp (continuous_const.prodMk continuous_id)))
      have hcoon : ContinuousOn Ffun' (Set.Ioc (0 : ℝ) L) := by
        apply ContinuousOn.div hDcont.continuousOn hden_cont.continuousOn
        intro t ht
        have htIcc : t ∈ Set.Icc (0 : ℝ) L := ⟨le_of_lt ht.1, ht.2⟩
        have h0 : s₀ ∈ Set.Icc (s₀ - δ') (s₀ + δ') := ⟨by linarith, by linarith⟩
        have hsqrt_pos : (0 : ℝ) < Real.sqrt (Φ s₀ t) := by
          have := hsqrtlb s₀ h0 t htIcc; linarith
        exact ne_of_gt (by linarith)
      rw [Set.uIoc_of_le (le_of_lt hL)]
      exact hcoon.aestronglyMeasurable measurableSet_Ioc)
    (by
      apply Filter.Eventually.of_forall
      intro t ht
      rw [Set.uIoc_of_le (le_of_lt hL)] at ht
      have htIcc : t ∈ Set.Icc (0 : ℝ) L := ⟨le_of_lt ht.1, ht.2⟩
      have hnn : Real.nnabs C0 = C0.toNNReal := by
        ext; simp [Real.coe_nnabs, Real.coe_toNNReal _ hC0nonneg,
          abs_of_nonneg hC0nonneg]
      rw [hnn]
      exact (hlip t htIcc).mono Set.Ioo_subset_Icc_self)
    (_root_.intervalIntegrable_const)
    (by
      apply Filter.Eventually.of_forall
      intro t ht
      rw [Set.uIoc_of_le (le_of_lt hL)] at ht
      have htIcc : t ∈ Set.Icc (0 : ℝ) L := ⟨le_of_lt ht.1, ht.2⟩
      have h0 : s₀ ∈ Set.Icc (s₀ - δ') (s₀ + δ') := ⟨by linarith, by linarith⟩
      exact (hslice_deriv s₀ t).sqrt (hΦne s₀ h0 t htIcc))
  exact key.2

/-- **First variation of arc length at a general parameter value `s₀`.** For a
smooth two-parameter variation `f` whose slice `t ↦ f s₀ t` is regular (positive
speed) on `[0, L]`, the derivative of `s' ↦ arcLength g (f s' ·) 0 L` at `s = s₀`
is the interval integral of `g(∇_s ∂_t f, ∂_t f) / √(speedSq g f s₀ t)`, the
transverse covariant derivative of the longitudinal velocity paired against the
longitudinal velocity, divided by the slice speed. Unlike
`first_variation_formula`, this holds at *any* regular `s₀`, where the slice is
neither unit-speed nor a geodesic; it is obtained by differentiating
`∫₀^L √(speedSq)` under the integral (`S2_diff_under_interval_integral_general`)
and identifying the pointwise `s`-derivative of `speedSq` through the
parameter-shifted metric-compatibility identity. -/
theorem first_variation_general_s
    (g : SmoothRiemannianMetric I M) (f : ℝ → ℝ → M) (L s₀ : ℝ)
    (hf : IsSmoothVariation (I := I) f) (hL : 0 < L)
    (hpos : ∀ t ∈ Set.Icc (0 : ℝ) L, 0 < speedSq (I := I) g f s₀ t) :
    HasDerivAt (fun s' : ℝ => arcLength (I := I) g (fun t : ℝ => f s' t) 0 L)
      (∫ t in (0 : ℝ)..L,
        g.inner (f s₀ t)
          (DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong.covDerivAlong
            (I := I) g (fun s : ℝ => f s t)
            (fun s : ℝ => mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f s u) t (1 : ℝ)) s₀)
          (mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f s₀ u) t (1 : ℝ))
          / Real.sqrt (speedSq (I := I) g f s₀ t))
      s₀ := by
  classical
  open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong in
  -- (1) The arc-length slice is the integral of `√(speedSq)`.
  have harc : (fun s' : ℝ => arcLength (I := I) g (fun t : ℝ => f s' t) 0 L)
      = (fun s' : ℝ => ∫ t in (0 : ℝ)..L, Real.sqrt (speedSq (I := I) g f s' t)) := by
    funext s'; exact arcLength_slice_eq_integral_sqrt_speedSq (I := I) g f s' L
  rw [harc]
  -- (2) Differentiate under the integral (general `s₀`).
  have hS2 := S2_diff_under_interval_integral_general (I := I) g f L s₀ hf hL hpos
  -- (3) Rewrite the `S2` integrand into the target form.
  -- The parameter-shifted metric-compatibility identity:
  -- `∂_s speedSq g f s₀ t = 2 g(∇_s ∂_t f, ∂_t f)` at `s = s₀`.
  -- Apply `S1_moving_foot_metric_compatibility` to the shifted variation
  -- `f' a b := f (s₀ + a) b`; the chain rule transports the derivative to `s₀`.
  set fsh : ℝ → ℝ → M := fun a b : ℝ => f (s₀ + a) b with hfsh
  have hfsh_smooth : IsSmoothVariation (I := I) fsh := by
    have hshift : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) ∞
        (fun q : ℝ × ℝ => (s₀ + q.1, q.2)) :=
      (contMDiff_const.add contMDiff_fst).prodMk contMDiff_snd
    exact (hf : ContMDiff _ _ _ _).comp hshift
  -- The partial `s`-derivative of `speedSq g f · t` at `s₀` equals the `S1`
  -- numerator for the shifted variation at `a = 0`, by uniqueness of derivatives.
  have hG_diff : ∀ p : ℝ × ℝ, DifferentiableAt ℝ
      (fun q : ℝ × ℝ => speedSq (I := I) g f q.1 q.2) p :=
    fun p => ((speedSq_contDiff (I := I) (M := M) g f hf).differentiable
      (by simp)).differentiableAt
  have hintegrand_eq : Set.EqOn
      (fun t : ℝ =>
        fderiv ℝ (fun p : ℝ × ℝ => speedSq (I := I) g f p.1 p.2) (s₀, t) (1, 0)
          / (2 * Real.sqrt (speedSq (I := I) g f s₀ t)))
      (fun t : ℝ =>
        g.inner (f s₀ t)
          (covDerivAlong (I := I) g (fun s : ℝ => f s t)
            (fun s : ℝ => mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f s u) t (1 : ℝ)) s₀)
          (mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f s₀ u) t (1 : ℝ))
          / Real.sqrt (speedSq (I := I) g f s₀ t))
      (Set.uIcc 0 L) := by
    intro t _ht
    simp only []
    -- The slice `a ↦ speedSq g f (s₀+a) t` has derivative `fderiv G (s₀,t) (1,0)`.
    have hslice_f : HasDerivAt
        (fun a : ℝ => speedSq (I := I) g f (s₀ + a) t)
        (fderiv ℝ (fun p : ℝ × ℝ => speedSq (I := I) g f p.1 p.2) (s₀, t) (1, 0)) 0 := by
      -- chain rule: `a ↦ s₀ + a` has derivative `1` at `0`, and `u ↦ speedSq f u t`
      -- has derivative `fderiv G (s₀, t) (1, 0)` at `s₀ = s₀ + 0`.
      have hslice0 : HasDerivAt (fun u : ℝ => speedSq (I := I) g f u t)
          (fderiv ℝ (fun p : ℝ × ℝ => speedSq (I := I) g f p.1 p.2) (s₀, t) (1, 0)) (s₀ + 0) := by
        rw [add_zero]
        exact Aux2.hasDerivAt_slice_fst
          (fun u v : ℝ => speedSq (I := I) g f u v) s₀ t (hG_diff (s₀, t))
      have hshift : HasDerivAt (fun a : ℝ => s₀ + a) (1 : ℝ) 0 := by
        simpa using (hasDerivAt_id (0 : ℝ)).const_add s₀
      have hcomp := hslice0.comp 0 hshift
      simpa using hcomp
    -- The `S1` numerator for the shifted variation: `∂_a speedSq fsh a t|₀`.
    have hS1 := S1_moving_foot_metric_compatibility (I := I) g fsh t hfsh_smooth
    -- `speedSq g fsh a t = speedSq g f (s₀+a) t` by definition of `fsh`.
    have hspeed_shift : ∀ a : ℝ, speedSq (I := I) g fsh a t
        = speedSq (I := I) g f (s₀ + a) t := fun a => rfl
    have hS1' : HasDerivAt (fun a : ℝ => speedSq (I := I) g f (s₀ + a) t)
        (2 * g.inner (fsh 0 t)
          (covDerivAlong (I := I) g (fun a : ℝ => fsh a t)
            (fun a : ℝ => mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => fsh a u) t (1 : ℝ)) 0)
          (mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => fsh 0 u) t (1 : ℝ))) 0 := by
      have heq : (fun a : ℝ => speedSq (I := I) g fsh a t)
          = (fun a : ℝ => speedSq (I := I) g f (s₀ + a) t) := by
        funext a; exact hspeed_shift a
      rw [heq] at hS1; exact hS1
    -- Uniqueness: the two derivative values agree.
    have hval := hS1'.unique hslice_f
    -- `fsh 0 t = f s₀ t`, and the `S1` numerator transports the shifted covariant
    -- derivative back to the genuine one at `s₀`.
    have hfoot0 : fsh 0 t = f s₀ t := by rw [hfsh]; simp
    -- The shifted covariant derivative equals the `s₀`-covariant derivative:
    -- `covDerivAlong g (fun a => fsh a t) (∂_t (fsh a ·)) 0
    --    = covDerivAlong g (fun s => f s t) (∂_t (f s ·)) s₀`.
    have hcov_shift :
        covDerivAlong (I := I) g (fun a : ℝ => fsh a t)
            (fun a : ℝ => mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => fsh a u) t (1 : ℝ)) 0
          = covDerivAlong (I := I) g (fun s : ℝ => f s t)
            (fun s : ℝ => mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f s u) t (1 : ℝ)) s₀ := by
      -- The transverse curves agree by reindex `a ↦ s₀ + a`; `covDerivAlong`
      -- commutes with the affine shift of the parameter (chain rule at `0` vs `s₀`).
      have := covDerivAlong_const_add_shift (I := I) g (fun s : ℝ => f s t)
        (fun s : ℝ => mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f s u) t (1 : ℝ)) s₀
      -- The shifted curve `fun a => (fun s => f s t) (s₀ + a)` is defeq to
      -- `fun a => fsh a t`, and the shifted section is defeq to the variation field.
      exact this
    rw [← hval]
    -- Convert `2 * N / (2 * D) = N / D`.
    rw [hfoot0, hcov_shift]
    have hsh_velT : ∀ u : ℝ, (fun u' : ℝ => fsh 0 u') u = (fun u' : ℝ => f s₀ u') u := by
      intro u; rw [hfsh]; simp
    have hsh_velT_fun : (fun u : ℝ => fsh 0 u) = (fun u : ℝ => f s₀ u) := by
      funext u; rw [hfsh]; simp
    rw [hsh_velT_fun]
    -- `2 * N / (2 * √φ) = N / √φ`.
    rw [mul_div_mul_left _ _ (by norm_num : (2 : ℝ) ≠ 0)]
  rw [intervalIntegral.integral_congr hintegrand_eq] at hS2
  exact hS2

/-! ## Second variation derivation -/

/-- The **second variation of arc length** for a unit-speed geodesic
`γ` and an endpoint-fixed smooth variation `f` of `γ` with variation
field `V := ∂_s f|_{s = 0}`:
`d²/ds²|_{s = 0} arcLength g (f s ·) 0 L = indexForm g γ 0 L V V`. -/
theorem second_variation_derivation
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M) (f : ℝ → ℝ → M) (L : ℝ)
    (V : ℝ → E)
    (hf : IsSmoothVariation (I := I) f) (hL : 0 < L)
    (hγ : IsGeodesicOn (I := I) g γ (Set.Icc 0 L)) (hfc : ∀ t : ℝ, f 0 t = γ t)
    (hVeq : ∀ t : ℝ, V t = mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f u t) 0 (1 : ℝ))
    (hUnit : ∀ t ∈ Set.Icc (0 : ℝ) L,
      g.inner (γ t)
          (mfderiv (𝓘(ℝ, ℝ)) I γ t (1 : ℝ))
          (mfderiv (𝓘(ℝ, ℝ)) I γ t (1 : ℝ)) = 1)
    (hfix0 : ∀ s : ℝ, f s 0 = γ 0) (hfixL : ∀ s : ℝ, f s L = γ L)
    (hVperp : ∀ t : ℝ,
      g.inner (γ t) (V t) (mfderiv (𝓘(ℝ, ℝ)) I γ t (1 : ℝ)) = 0) :
    HasDerivAt
      (fun s : ℝ => deriv
        (fun s' : ℝ => arcLength (I := I) g (fun t : ℝ => f s' t) 0 L) s)
      (indexForm (I := I) g γ 0 L V V) 0 := sorry

/-! ## Construction of a smooth variation with prescribed variation field -/

/-- **Exponential-map construction of a smooth endpoint-fixed variation.**
Given a smooth curve `γ` and a smooth `E`-valued variation field `V` vanishing
at the endpoints `0` and `L`, there is a smooth two-parameter variation `f`
whose central curve is `γ`, whose `s`-velocity at `s = 0` realises `V`
(`∂_s f|_{s = 0} = V`), and which keeps both endpoints fixed
(`f s 0 = γ 0` and `f s L = γ L` for every `s`). The construction follows the
geodesic exponential map of the field, `f s t := exp_{γ t}(s · V t)`. -/
theorem S5_exp_variation_construction
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M) (V : ℝ → E) (L : ℝ)
    (_hγ : ContMDiff (𝓘(ℝ, ℝ)) I ∞ γ) (_hV : ContDiff ℝ ∞ V)
    (_hV0 : V 0 = 0) (_hVL : V L = 0) :
    ∃ f : ℝ → ℝ → M,
      IsSmoothVariation (I := I) f ∧
      (∀ t : ℝ, f 0 t = γ t) ∧
      (∀ t : ℝ,
        (mfderiv (𝓘(ℝ, ℝ)) I (fun s : ℝ => f s t) 0 (1 : ℝ) : E) = V t) ∧
      (∀ s : ℝ, f s 0 = γ 0) ∧ (∀ s : ℝ, f s L = γ L) := sorry

/-! ## Interval-integrability of the index-form integrand -/

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
omit [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
/-- Continuity on a set `s ⊆ ℝ` of the scalar `t ↦ g.inner (γ t) (v t) (w t)`
for a base curve `γ` and two sections `v, w` along `γ` presented through their
total-space continuity. Mirrors `continuous_g_inner_along_param` in its
`ContinuousOn` form over a single-parameter base curve. The diamond between
the project's tangent-space norm instances and the `RiemannianBundle`-derived
ones is resolved locally; the scalar `ℝ`-valued conclusion is independent of
the disabled instances. -/
lemma continuousOn_g_inner_along_curve
    (g : SmoothRiemannianMetric I M)
    {γ : ℝ → M} {v w : ∀ t : ℝ, TangentSpace I (γ t)} {s : Set ℝ}
    (hv : ContinuousOn (fun t : ℝ => TotalSpace.mk' E
      (E := (TangentSpace I : M → Type _)) (γ t) (v t)) s)
    (hw : ContinuousOn (fun t : ℝ => TotalSpace.mk' E
      (E := (TangentSpace I : M → Type _)) (γ t) (w t)) s) :
    ContinuousOn (fun t : ℝ => g.inner (γ t) (v t) (w t)) s := by
  letI cg : Bundle.ContinuousRiemannianMetric E (TangentSpace I : M → Type _) :=
    g.toContinuousRiemannianMetric
  letI rb : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨cg.toRiemannianMetric⟩
  have h := ContinuousOn.inner_bundle (F := E) (B := M)
    (E := (TangentSpace I : M → Type _)) (b := γ) (v := v) (w := w)
    (s := s) hv hw
  refine h.congr ?_
  intro t _ht
  rfl

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 4000000 in
set_option maxSynthPendingDepth 4 in
/-- **Interval-integrability of the index-form integrand on the
sine-modulated parallel frame.** For a `C¹` unit-speed geodesic `γ` on `[0, L]`
(`L > 0`) and a differentiable, parallel, orthonormal frame `e` of the
perpendicular subspace along `γ`, each sine-modulated section
`t ↦ sin(π t / L) · e i` makes the index-form integrand interval-integrable on
`[0, L]`. The integrand is continuous on the compact interval: it is built from
the smooth chart Christoffels, the `C¹` curve `γ`, the smooth sine factor, and
the differentiable frame `e`. -/
theorem indexFormIntegrand_intervalIntegrable
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M) (L : ℝ) (_hL : 0 < L)
    (_hγ_C1 : ContMDiffOn (𝓘(ℝ, ℝ)) I 1 γ (Set.Icc 0 L))
    (_hγ_geoOn : IsGeodesicOn (I := I) g γ (Set.Icc 0 L))
    (_hγ_unit : ∀ t ∈ Set.Icc (0 : ℝ) L,
      g.inner (γ t)
          (mfderiv (𝓘(ℝ, ℝ)) I γ t (1 : ℝ))
          (mfderiv (𝓘(ℝ, ℝ)) I γ t (1 : ℝ)) = 1)
    (e : Fin (Module.finrank ℝ E - 1) → SectionAlongCurve I M γ)
    (_heDiff : ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) L,
      DifferentiableAt ℝ
        (DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong.chartRepAt
          (I := I) γ (e i).toFun t) t)
    (_hParallel : ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) L,
      DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong.covDerivAlong
        (I := I) g γ (e i).toFun t = 0)
    (_hON : ∀ t ∈ Set.Icc (0 : ℝ) L, ∀ i j,
      g.inner (γ t) ((e i).toFun t) ((e j).toFun t) = if i = j then 1 else 0)
    (_hPerp : ∀ t ∈ Set.Icc (0 : ℝ) L, ∀ i,
      g.inner (γ t) ((e i).toFun t) (mfderiv (𝓘(ℝ, ℝ)) I γ t (1 : ℝ)) = 0) :
    ∀ i : Fin (Module.finrank ℝ E - 1),
      IntervalIntegrable
        (fun t : ℝ => indexFormIntegrand (I := I) g γ
          ((SectionAlongCurve.smulFun
            (fun s => Real.sin (Real.pi * s / L)) (e i)).toFun)
          ((SectionAlongCurve.smulFun
            (fun s => Real.sin (Real.pi * s / L)) (e i)).toFun) t)
        MeasureTheory.volume 0 L := by
  intro i
  classical
  set c : ℝ → ℝ := fun s => Real.sin (Real.pi * s / L) with hc_def
  have hL_nn : (0 : ℝ) ≤ L := le_of_lt _hL
  -- The sine factor `c` is `C^∞`, so it and its derivative are continuous.
  have hc_contdiff : ContDiff ℝ ∞ c :=
    Real.contDiff_sin.comp ((contDiff_const.mul contDiff_id).div_const _)
  have hc_cont : Continuous c := hc_contdiff.continuous
  have hderiv_c_cont : Continuous (deriv c) := hc_contdiff.continuous_deriv (by simp)
  have hc_diff : ∀ t, DifferentiableAt ℝ c t :=
    fun t => hc_contdiff.differentiable (by simp) t
  -- (1) Total-space continuity of the parallel frame section `e i` on `[0, L]`.
  have he_total : ContinuousOn
      (fun t : ℝ => (TotalSpace.mk' E (γ t) ((e i).toFun t) : TangentBundle I M))
      (Set.Icc 0 L) :=
    DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong.sectionAlongCurve_continuousOn_totalSpace_of_contMDiffOn
      (I := I) γ (e i).toFun _hγ_C1 (fun t ht => _heDiff i t ht)
  -- (2) Continuity of `A t := g.inner (γ t) (e i t) (e i t)` on `[0, L]`.
  have hA : ContinuousOn (fun t : ℝ => g.inner (γ t) ((e i).toFun t) ((e i).toFun t))
      (Set.Icc 0 L) :=
    continuousOn_g_inner_along_curve (I := I) (M := M) g he_total he_total
  -- (3) Within-set velocity total-space continuity (via `tangentMapWithin`).
  have hUnique : UniqueMDiffOn 𝓘(ℝ, ℝ) (Set.Icc (0 : ℝ) L) := by
    intro u hu
    rw [uniqueMDiffWithinAt_iff_uniqueDiffWithinAt]
    exact (uniqueDiffOn_Icc _hL) u hu
  have hTan := _hγ_C1.continuousOn_tangentMapWithin (le_refl 1) hUnique
  have hLift : Continuous (fun u : ℝ =>
      (⟨u, (1 : ℝ)⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ)) := by
    have h_homeo :
        Continuous ((tangentBundleModelSpaceHomeomorph 𝓘(ℝ, ℝ)).symm :
          ModelProd ℝ ℝ → TangentBundle 𝓘(ℝ, ℝ) ℝ) :=
      (tangentBundleModelSpaceHomeomorph 𝓘(ℝ, ℝ)).symm.continuous
    exact h_homeo.comp (continuous_id.prodMk continuous_const)
  have hMaps : Set.MapsTo
      (fun u : ℝ => (⟨u, (1 : ℝ)⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ))
      (Set.Icc (0 : ℝ) L) (Bundle.TotalSpace.proj ⁻¹' (Set.Icc (0 : ℝ) L)) := by
    intro u hu
    simpa using hu
  have hVW : ContinuousOn
      (fun t : ℝ =>
        (TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
          (γ t)
          (mfderivWithin 𝓘(ℝ, ℝ) I γ (Set.Icc (0 : ℝ) L) t (1 : ℝ)) :
            TangentBundle I M))
      (Set.Icc (0 : ℝ) L) := by
    have hComp : ContinuousOn
        (fun t : ℝ => tangentMapWithin 𝓘(ℝ, ℝ) I γ (Set.Icc (0 : ℝ) L)
          (⟨t, (1 : ℝ)⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ))
        (Set.Icc (0 : ℝ) L) :=
      hTan.comp hLift.continuousOn hMaps
    exact hComp.congr (fun t _ => rfl)
  -- (4)+(5) Riemann operator section continuity composed with `γ`, then peeled
  -- by `clm_bundle_apply` on the three vector slots (intermediate hom-bundle
  -- types inferred under the pinned `E`-fibre total-space goal):
  -- `t ↦ ⟨γ t, riemannOp (γ t) (e i t) (γ'within t) (γ'within t)⟩`.
  have hR3 : ContinuousOn
      (fun t : ℝ => (TotalSpace.mk' E
        (E := (TangentSpace I : M → Type _))
        (γ t)
        (DifferentialGeometry.Integral.Connection.riemannOp
          (DifferentialGeometry.Integral.Connection.LeviCivita (I := I) g) (γ t)
          ((e i).toFun t)
          (mfderivWithin 𝓘(ℝ, ℝ) I γ (Set.Icc (0 : ℝ) L) t (1 : ℝ))
          (mfderivWithin 𝓘(ℝ, ℝ) I γ (Set.Icc (0 : ℝ) L) t (1 : ℝ)))))
      (Set.Icc 0 L) :=
    ((((DifferentialGeometry.Integral.Connection.riemannOp_section_continuous
        (I := I) g).comp_continuousOn
        (s := Set.Icc (0 : ℝ) L) _hγ_C1.continuousOn).clm_bundle_apply
        he_total).clm_bundle_apply hVW).clm_bundle_apply hVW
  -- (6) Continuity of the curvature scalar `B t := g.inner (γ t) (riemannOp …) (e i t)`.
  have hB : ContinuousOn
      (fun t : ℝ => g.inner (γ t)
        (DifferentialGeometry.Integral.Connection.riemannOp
          (DifferentialGeometry.Integral.Connection.LeviCivita (I := I) g) (γ t)
          ((e i).toFun t)
          (mfderivWithin 𝓘(ℝ, ℝ) I γ (Set.Icc (0 : ℝ) L) t (1 : ℝ))
          (mfderivWithin 𝓘(ℝ, ℝ) I γ (Set.Icc (0 : ℝ) L) t (1 : ℝ)))
        ((e i).toFun t))
      (Set.Icc 0 L) :=
    continuousOn_g_inner_along_curve (I := I) (M := M) g hR3 he_total
  -- (7) The combined integrand, in `mfderivWithin` form, is continuous.
  have hIntW : IntervalIntegrable
      (fun t : ℝ =>
        (deriv c t * deriv c t) * g.inner (γ t) ((e i).toFun t) ((e i).toFun t)
        - (c t * c t) * g.inner (γ t)
            (DifferentialGeometry.Integral.Connection.riemannOp
              (DifferentialGeometry.Integral.Connection.LeviCivita (I := I) g) (γ t)
              ((e i).toFun t)
              (mfderivWithin 𝓘(ℝ, ℝ) I γ (Set.Icc (0 : ℝ) L) t (1 : ℝ))
              (mfderivWithin 𝓘(ℝ, ℝ) I γ (Set.Icc (0 : ℝ) L) t (1 : ℝ)))
            ((e i).toFun t))
      MeasureTheory.volume 0 L := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hL_nn]
    refine ContinuousOn.sub ?_ ?_
    · exact ((hderiv_c_cont.mul hderiv_c_cont).continuousOn).mul hA
    · exact ((hc_cont.mul hc_cont).continuousOn).mul hB
  -- (8) Transfer to the `indexFormIntegrand` (`mfderiv`) form by a.e.-equality on
  -- the co-null interior `Ioo 0 L`, where `mfderivWithin = mfderiv`.
  refine hIntW.congr_ae ?_
  have hIoo_ae : ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.uIoc (0 : ℝ) L)),
      t ∈ Set.Ioo (0 : ℝ) L := by
    rw [Set.uIoc_of_le hL_nn, ← MeasureTheory.restrict_Ioo_eq_restrict_Ioc]
    exact MeasureTheory.ae_restrict_mem measurableSet_Ioo
  filter_upwards [hIoo_ae] with t ht
  have htIcc : t ∈ Set.Icc (0 : ℝ) L := ⟨le_of_lt ht.1, le_of_lt ht.2⟩
  have hmem : Set.Icc (0 : ℝ) L ∈ nhds t := Icc_mem_nhds ht.1 ht.2
  change (deriv c t * deriv c t) * g.inner (γ t) ((e i).toFun t) ((e i).toFun t)
      - (c t * c t) * g.inner (γ t)
          (DifferentialGeometry.Integral.Connection.riemannOp
            (DifferentialGeometry.Integral.Connection.LeviCivita (I := I) g) (γ t)
            ((e i).toFun t)
            (mfderivWithin 𝓘(ℝ, ℝ) I γ (Set.Icc (0 : ℝ) L) t (1 : ℝ))
            (mfderivWithin 𝓘(ℝ, ℝ) I γ (Set.Icc (0 : ℝ) L) t (1 : ℝ)))
          ((e i).toFun t)
    = indexFormIntegrand (I := I) g γ
        ((SectionAlongCurve.smulFun c (e i)).toFun)
        ((SectionAlongCurve.smulFun c (e i)).toFun) t
  rw [mfderivWithin_of_mem_nhds hmem]
  -- The covariant-derivative slot carries the unapplied section
  -- `(smulFun c (e i)).toFun = fun s => c s • (e i).toFun s`; the parallel,
  -- sine-modulated covariant derivative is `(deriv c t) • (e i t)`.
  have hnabla :
      DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong.covDerivAlong
        (I := I) g γ (SectionAlongCurve.smulFun c (e i)).toFun t
        = deriv c t • (e i).toFun t := by
    have key :=
      DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong.covDerivAlong_smulFun
        (I := I) g γ c (e i).toFun t (hc_diff t) (_heDiff i t htIcc)
    rw [_hParallel i t htIcc, smul_zero, add_zero] at key
    exact key
  -- Bilinearity of `g.inner` and ℝ-linearity of `riemannOp`'s first vector slot,
  -- phrased through `TangentSpace I (γ t)`-typed vectors so `map_smul` sees the
  -- fibre module smul (definitionally equal to the model-space `E` smul).
  have hfac1 : g.inner (γ t) (deriv c t • (e i).toFun t) (deriv c t • (e i).toFun t)
      = (deriv c t * deriv c t) * g.inner (γ t) ((e i).toFun t) ((e i).toFun t) := by
    have key : ∀ (x : TangentSpace I (γ t)) (a : ℝ),
        g.inner (γ t) (a • x) (a • x) = (a * a) * g.inner (γ t) x x := by
      intro x a
      simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
      ring
    exact key ((e i).toFun t) (deriv c t)
  have hfac2 : g.inner (γ t)
      (DifferentialGeometry.Integral.Connection.riemannOp
        (DifferentialGeometry.Integral.Connection.LeviCivita (I := I) g) (γ t)
        (c t • (e i).toFun t)
        (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ)) (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ)))
      (c t • (e i).toFun t)
      = (c t * c t) * g.inner (γ t)
          (DifferentialGeometry.Integral.Connection.riemannOp
            (DifferentialGeometry.Integral.Connection.LeviCivita (I := I) g) (γ t)
            ((e i).toFun t)
            (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ)) (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ)))
          ((e i).toFun t) := by
    have key : ∀ (x w : TangentSpace I (γ t)) (a : ℝ),
        g.inner (γ t)
          (DifferentialGeometry.Integral.Connection.riemannOp
            (DifferentialGeometry.Integral.Connection.LeviCivita (I := I) g) (γ t)
            (a • x) w w) (a • x)
          = (a * a) * g.inner (γ t)
              (DifferentialGeometry.Integral.Connection.riemannOp
                (DifferentialGeometry.Integral.Connection.LeviCivita (I := I) g) (γ t)
                x w w) x := by
      intro x w a
      simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
      ring
    exact key ((e i).toFun t) (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ)) (c t)
  -- Unfold the integrand and substitute the three identities.
  unfold indexFormIntegrand
  simp only [SectionAlongCurve.smulFun_toFun]
  rw [hnabla, hfac1, hfac2]

end Variation
end Riemannian
end Geometry
end DifferentialGeometry

end
