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


/-! ## First variation of arc length -/

/-- The first variation of arc length: for a smooth endpoint-fixed
variation `f` of a unit-speed curve `γ := f 0`, the derivative of
`s ↦ arcLength g (f s ·) 0 L` at `s = 0` equals minus the integral
of `⟨V, ∇_t γ'⟩_g`, where `V := ∂_s f|_{s = 0}` is the variation
field. (The boundary contribution vanishes for endpoint-fixed
variations and is omitted.) -/
theorem first_variation_formula
    (g : SmoothRiemannianMetric I M) (f : ℝ → ℝ → M) (L : ℝ)
    (_hfix0 : ∀ s : ℝ, f s 0 = f 0 0) (_hfixL : ∀ s : ℝ, f s L = f 0 L)
    (_hUnit : ∀ t ∈ Set.Icc (0 : ℝ) L,
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
              mfderiv (𝓘(ℝ, ℝ)) I (fun w : ℝ => f 0 w) v (1 : ℝ)) t)) 0 := sorry

/-! ## First variation vanishes along a geodesic -/

/-- For a unit-speed geodesic `γ` and any endpoint-fixed smooth
variation `f` whose central curve is `γ`, the first variation of
arc length at `s = 0` vanishes. -/
theorem first_variation_vanishes_for_geodesic
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M) (f : ℝ → ℝ → M) (L : ℝ)
    (_hγ : IsGeodesicOn (I := I) g γ (Set.Icc 0 L)) (_hf : ∀ t : ℝ, f 0 t = γ t)
    (_hfix0 : ∀ s : ℝ, f s 0 = γ 0) (_hfixL : ∀ s : ℝ, f s L = γ L)
    (_hUnit : ∀ t ∈ Set.Icc (0 : ℝ) L,
      g.inner (γ t)
          (mfderiv (𝓘(ℝ, ℝ)) I γ t (1 : ℝ))
          (mfderiv (𝓘(ℝ, ℝ)) I γ t (1 : ℝ)) = 1) :
    HasDerivAt (fun s : ℝ => arcLength (I := I) g (fun t : ℝ => f s t) 0 L)
      0 0 := sorry

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

/-! ## Second variation derivation -/

/-- The **second variation of arc length** for a unit-speed geodesic
`γ` and an endpoint-fixed smooth variation `f` of `γ` with variation
field `V := ∂_s f|_{s = 0}`:
`d²/ds²|_{s = 0} arcLength g (f s ·) 0 L = indexForm g γ 0 L V V`. -/
theorem second_variation_derivation
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M) (f : ℝ → ℝ → M) (L : ℝ)
    (V : ℝ → E)
    (_hγ : IsGeodesicOn (I := I) g γ (Set.Icc 0 L)) (_hf : ∀ t : ℝ, f 0 t = γ t)
    (_hV : ∀ t : ℝ, V t = mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f u t) 0 (1 : ℝ))
    (_hUnit : ∀ t ∈ Set.Icc (0 : ℝ) L,
      g.inner (γ t)
          (mfderiv (𝓘(ℝ, ℝ)) I γ t (1 : ℝ))
          (mfderiv (𝓘(ℝ, ℝ)) I γ t (1 : ℝ)) = 1)
    (_hfix0 : ∀ s : ℝ, f s 0 = γ 0) (_hfixL : ∀ s : ℝ, f s L = γ L)
    (_hVperp : ∀ t : ℝ,
      g.inner (γ t) (V t) (mfderiv (𝓘(ℝ, ℝ)) I γ t (1 : ℝ)) = 0) :
    HasDerivAt
      (fun s : ℝ => deriv
        (fun s' : ℝ => arcLength (I := I) g (fun t : ℝ => f s' t) 0 L) s)
      (indexForm (I := I) g γ 0 L V V) 0 := sorry

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
    show γ 0 ∈ (chartAt H α).source
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
    show V s =
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
      show _ = (trivializationAt E (TangentSpace I) (γ 0)).continuousLinearMapAt ℝ (γ s) (Vsec s)
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
    show _ = (trivializationAt E (TangentSpace I) (γ 0)).continuousLinearMapAt ℝ (γ 0) (Vsec 0)
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
  show (2 : ℝ) * (∑ l, ∑ j, DifferentialGeometry.Integral.DivergenceTheorem.chartGramOnE (I := I) g α l j u0
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
    (_heDiff : ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) L, DifferentiableAt ℝ (e i).toFun t)
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
        MeasureTheory.volume 0 L := sorry

end Variation
end Riemannian
end Geometry
end DifferentialGeometry

end
