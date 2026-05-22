import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.MaxRegSpace
import Mathlib.Topology.MetricSpace.Contracting

/-!
# Strong existence for the abstract quasi-linear tensor heat equation

For a closed Riemannian manifold `(M, g)`, ranks `(r, s)`, a Sobolev exponent
`a ≥ 0` and a time horizon `0 < T ≤ 1`, this file proves the **abstract
quasi-linear strong-existence theorem**: for a nonlinearity
`N : H^{a+2} → Hᵃ` which is Lipschitz with a small enough constant, the
quasi-linear tensor heat equation

  `∂_t u = Δ_∇ u + N(u)`,  `u(0) = u₀`,

has a strong solution on `[0,T]`.  The solution is produced by a Banach
fixed-point argument built on the maximal-regularity machinery.

## The forcing-space fixed point

A strong solution of `∂_t u = Δ_∇ u + N(u)`, `u(0) = u₀`, is the affine Duhamel
image `u = maxRegDuhamelMap … u₀ g` of a forcing term `g` that reproduces
`N(u)`: the equation `g = N ∘ (field of u)` is the fixed-point equation.  The
fixed point is taken **on the forcing space** `L²([0,T]; Hᵃ)`, not on the
solution space.  The solution space carries the `H¹`-graph norm, which does not
control the `H^{a+2}` spatial field of a strong solution; a contraction phrased
on the solution space would therefore fail.  The forcing-space route avoids
this: the contraction is measured purely in `L²([0,T]; Hᵃ)`, and the
two-derivative gain of maximal regularity is used only as a *bound* (via
`maximalRegularityOp_norm_Ha2_le`) inside the contraction estimate.

Concretely, the fixed-point map on `L²([0,T]; Hᵃ)` is

  `Φ(g) := N ∘ (maxRegDuhamelSolField … u₀ g)`,

i.e.: take the forcing `g`, form the Duhamel solution's `H^{a+2}`-valued field
`maxRegDuhamelSolField … u₀ g`, then apply `N` pointwise in time.  A fixed point
`g⋆ = Φ(g⋆)` yields the strong solution `u⋆ = maxRegDuhamelMap … u₀ g⋆`, which
satisfies `g⋆ = N ∘ (field of u⋆)`, hence `∂_t u⋆ = Δ_∇ u⋆ + N(field of u⋆)`.

## The Nemytskii operator

Pointwise composition with `N` lifts to a map of time-`L²` spaces

  `nemytskii hN : L²([0,T]; H^{a+2}) → L²([0,T]; Hᵃ)`,  `f ↦ N ∘ f`,

Lipschitz with the **same** constant `L`.  Membership in `L²` holds because `N`
is Lipschitz: `‖N x‖ ≤ ‖N 0‖ + L‖x‖`, so `N ∘ f` is square-integrable whenever
`f` is and the time measure is finite (`N` need not fix `0`).  The Lipschitz
bound is the pointwise estimate `‖N x − N y‖ ≤ L‖x − y‖` integrated in time.

## Main definitions

* `nemytskii hN` — the Nemytskii (pointwise-composition) operator
  `L²([0,T]; H^{a+2}) → L²([0,T]; Hᵃ)`, `f ↦ N ∘ f`.
* `quasilinearDuhamelMap h_atlas a hT hT1 u₀ hN` — the forcing-space
  fixed-point map `Φ` of the quasi-linear equation.

## Main results

* `nemytskii_coeFn` — `nemytskii hN f` is represented a.e. by `t ↦ N (f t)`.
* `nemytskii_lipschitzWith` — `nemytskii hN` is Lipschitz with constant `L`.
* `maximalRegularitySolField_sub` — additivity of the maximal-regularity
  solution field, the algebraic input to the contraction estimate.
* `quasilinearDuhamelMap_contracting` — `Φ` is a contraction with constant
  `(L : ℝ)·(1 + T)` whenever `2·L < 1` (then `(L : ℝ)·(1 + T) < 1`).
* `quasilinear_strong_existence` — **the headline theorem**: for `0 < T ≤ 1`,
  `N` Lipschitz with `2·L < 1`, there is a strong solution `u` of
  `∂_t u = Δ_∇ u + N(u)`, `u(0) = u₀`, in the maximal-regularity solution
  space.
* `quasilinear_strong_unique` — the strong solution produced by the fixed-point
  construction is unique.
-/

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
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
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

variable {g : SmoothRiemannianMetric I M} {r s : ℕ}
  {h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M}
variable {a : ℝ} {T : ℝ}

/-! ## The Nemytskii operator

For a Lipschitz nonlinearity `N : H^{a+2} → Hᵃ`, pointwise composition with `N`
sends a time-`L²` field to a time-`L²` field with the same Lipschitz constant.
The two analytic facts behind the construction are:

* **`L²`-membership.**  `N` Lipschitz gives `‖N x‖ ≤ ‖N 0‖ + L‖x‖`; for a
  square-integrable `f` on the finite time interval the bound makes `N ∘ f`
  square-integrable.  `N` need not fix `0`, so the membership is obtained by
  splitting `N` into the `0`-fixing Lipschitz part `x ↦ N x − N 0` and the
  constant `N 0`.
* **The Lipschitz bound.**  The pointwise estimate `‖N x − N y‖ ≤ L‖x − y‖`,
  squared and integrated in time, yields `‖N∘f − N∘f'‖²_{L²} ≤ L²‖f − f'‖²`. -/

section Nemytskii

variable {L : ℝ≥0}
  {N : tensorHs (I := I) (M := M) g r s (a + 2) →
    tensorHs (I := I) (M := M) g r s a}

/-- The pointwise composition `t ↦ N (f t)` of a Lipschitz nonlinearity `N` with
a time-`L²` field `f ∈ L²([0,T]; H^{a+2})` is itself square-integrable for the
(finite) time measure: it is the sum of the `0`-fixing Lipschitz part
`t ↦ N (f t) − N 0` (square-integrable by `LipschitzWith.comp_memLp`) and the
constant `N 0` (square-integrable on a finite measure space). -/
theorem memLp_comp_nemytskii (hN : LipschitzWith L N)
    (f : timeL2 (tensorHs (I := I) (M := M) g r s (a + 2)) T) :
    MemLp (fun t => N (f t)) 2 (timeMeasure T) := by
  -- The `0`-fixing Lipschitz part `Ñ x = N x − N 0`, with constant `L` (the
  -- constant function is Lipschitz with constant `0`, and `L + 0 = L`).
  have hshift : LipschitzWith L (fun x => N x - N 0) := by
    have hsubL := hN.sub (LipschitzWith.const (N 0))
    rwa [add_zero] at hsubL
  have hshift0 : (fun x => N x - N 0) (0 : tensorHs (I := I) (M := M) g r s
      (a + 2)) = 0 := by simp
  -- `Ñ ∘ ⇑f` is `MemLp` by `LipschitzWith.comp_memLp`.
  have hcomp : MemLp ((fun x => N x - N 0) ∘ fun t => f t) 2 (timeMeasure T) :=
    hshift.comp_memLp hshift0 (Lp.memLp f)
  -- The constant `N 0` is `MemLp` on the finite time measure.
  have hconst : MemLp (fun _ : ℝ => N 0) 2 (timeMeasure T) :=
    memLp_const (N 0)
  -- `N (f t) = (N (f t) − N 0) + N 0`, so `MemLp` transfers along this equality.
  have hsum : MemLp (fun t => (N (f t) - N 0) + N 0) 2 (timeMeasure T) :=
    hcomp.add hconst
  have hfun : (fun t => N (f t)) =
      fun t => (N (f t) - N 0) + N 0 := by
    funext t; abel
  rw [hfun]
  exact hsum

/-- **The Nemytskii operator.**  For a Lipschitz nonlinearity `N : H^{a+2} →
Hᵃ`, this is the pointwise-composition map

  `nemytskii hN : L²([0,T]; H^{a+2}) → L²([0,T]; Hᵃ)`,  `f ↦ N ∘ f`,

sending a time-`L²` field `f` to the time-`L²` field represented by `t ↦ N (f
t)`.  The output lands in `L²` because `N` is Lipschitz (`memLp_comp_nemytskii`)
and the underlying function agrees a.e. with `t ↦ N (f t)`
(`nemytskii_coeFn`). -/
def nemytskii (hN : LipschitzWith L N) :
    timeL2 (tensorHs (I := I) (M := M) g r s (a + 2)) T →
      timeL2 (tensorHs (I := I) (M := M) g r s a) T :=
  fun f => (memLp_comp_nemytskii (I := I) (M := M) hN f).toLp (fun t => N (f t))

/-- `nemytskii hN f` is represented almost everywhere by the pointwise
composition `t ↦ N (f t)`. -/
theorem nemytskii_coeFn (hN : LipschitzWith L N)
    (f : timeL2 (tensorHs (I := I) (M := M) g r s (a + 2)) T) :
    nemytskii (I := I) (M := M) hN f =ᵐ[timeMeasure T] fun t => N (f t) :=
  (memLp_comp_nemytskii (I := I) (M := M) hN f).coeFn_toLp

/-- **The pointwise-in-time contraction estimate of the Nemytskii operator.**
For two time-`L²` fields `f, f'` the squared `L²` distance of their Nemytskii
images is bounded by `L²` times the squared `L²` distance of the fields:

  `‖nemytskii hN f − nemytskii hN f'‖² ≤ L²·‖f − f'‖²`.

This is the pointwise Lipschitz estimate `‖N (f t) − N (f' t)‖ ≤ L·‖f t − f' t‖`
squared and integrated in time. -/
theorem nemytskii_dist_sq_le (hN : LipschitzWith L N)
    (f f' : timeL2 (tensorHs (I := I) (M := M) g r s (a + 2)) T) :
    ‖nemytskii (I := I) (M := M) hN f - nemytskii (I := I) (M := M) hN f'‖ ^ 2 ≤
      (L : ℝ) ^ 2 * ‖f - f'‖ ^ 2 := by
  -- Both norms are integrals of pointwise squared norms over `[0,T]`.
  rw [TimeSobolev.norm_sq_eq_integral, TimeSobolev.norm_sq_eq_integral,
    ← MeasureTheory.integral_const_mul]
  -- The difference of Nemytskii images is a.e. `t ↦ N (f t) − N (f' t)`.
  have hdiff : ⇑(nemytskii (I := I) (M := M) hN f -
        nemytskii (I := I) (M := M) hN f') =ᵐ[timeMeasure T]
      fun t => N (f t) - N (f' t) := by
    have hsub := Lp.coeFn_sub (nemytskii (I := I) (M := M) hN f)
      (nemytskii (I := I) (M := M) hN f')
    have hf := nemytskii_coeFn (I := I) (M := M) hN f
    have hf' := nemytskii_coeFn (I := I) (M := M) hN f'
    filter_upwards [hsub, hf, hf'] with t ht htf htf'
    rw [ht, Pi.sub_apply, htf, htf']
  -- The difference of the two fields is a.e. `t ↦ f t − f' t`.
  have hfdiff : ⇑(f - f') =ᵐ[timeMeasure T] fun t => f t - f' t :=
    Lp.coeFn_sub f f'
  -- Square-integrability of the pointwise squared norm of the field difference.
  have hint_fdiff : Integrable (fun t => ‖(f - f') t‖ ^ 2) (timeMeasure T) :=
    (memLp_two_iff_integrable_sq_norm
      (Lp.aestronglyMeasurable (f - f'))).mp (Lp.memLp (f - f'))
  -- Integrand-wise pointwise bound `‖N(f t)−N(f' t)‖² ≤ L²‖f t−f' t‖²`, then
  -- integrate the inequality.
  refine integral_mono_ae ?_ ?_ ?_
  · -- `t ↦ ‖(nemytskii f − nemytskii f') t‖²` is integrable.
    exact (memLp_two_iff_integrable_sq_norm
      (Lp.aestronglyMeasurable (nemytskii (I := I) (M := M) hN f -
        nemytskii (I := I) (M := M) hN f'))).mp
      (Lp.memLp (nemytskii (I := I) (M := M) hN f -
        nemytskii (I := I) (M := M) hN f'))
  · -- `t ↦ L²·‖(f − f') t‖²` is integrable.
    exact hint_fdiff.const_mul ((L : ℝ) ^ 2)
  · -- The pointwise inequality, holding almost everywhere.
    filter_upwards [hdiff, hfdiff] with t ht htf
    rw [ht]
    have hlip : ‖N (f t) - N (f' t)‖ ≤ (L : ℝ) * ‖f t - f' t‖ := by
      rw [← dist_eq_norm, ← dist_eq_norm]
      exact hN.dist_le_mul (f t) (f' t)
    have hnn : 0 ≤ ‖N (f t) - N (f' t)‖ := norm_nonneg _
    have hsq : ‖N (f t) - N (f' t)‖ ^ 2 ≤ ((L : ℝ) * ‖f t - f' t‖) ^ 2 := by
      have hrhs_nn : 0 ≤ (L : ℝ) * ‖f t - f' t‖ :=
        mul_nonneg L.coe_nonneg (norm_nonneg _)
      nlinarith [hlip, hnn, hrhs_nn]
    calc ‖N (f t) - N (f' t)‖ ^ 2
        ≤ ((L : ℝ) * ‖f t - f' t‖) ^ 2 := hsq
      _ = (L : ℝ) ^ 2 * ‖(f - f') t‖ ^ 2 := by rw [htf, mul_pow]

/-- **The Nemytskii operator is Lipschitz with the same constant.**  For a
Lipschitz nonlinearity `N : H^{a+2} → Hᵃ` with constant `L`, the Nemytskii
operator `nemytskii hN : L²([0,T]; H^{a+2}) → L²([0,T]; Hᵃ)` is Lipschitz with
the same constant `L`: pointwise composition does not enlarge the Lipschitz
constant.  This is the squared estimate `nemytskii_dist_sq_le` after taking
square roots. -/
theorem nemytskii_lipschitzWith (hN : LipschitzWith L N) :
    LipschitzWith L (nemytskii (I := I) (M := M) (T := T) hN) := by
  refine LipschitzWith.of_dist_le_mul (fun f f' => ?_)
  rw [dist_eq_norm, dist_eq_norm]
  -- Take square roots of the squared Lipschitz estimate.
  have hsq := nemytskii_dist_sq_le (I := I) (M := M) hN f f'
  have hrhs_nn : 0 ≤ (L : ℝ) * ‖f - f'‖ := mul_nonneg L.coe_nonneg (norm_nonneg _)
  have hsq' : ‖nemytskii (I := I) (M := M) hN f -
        nemytskii (I := I) (M := M) hN f'‖ ^ 2 ≤ ((L : ℝ) * ‖f - f'‖) ^ 2 := by
    rw [mul_pow]; exact hsq
  have h := Real.sqrt_le_sqrt hsq'
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq hrhs_nn] at h

end Nemytskii

/-! ## Additivity of the maximal-regularity solution field

The maximal-regularity solution field `maximalRegularitySolField` — the
`H^{a+2}`-valued Duhamel solution of `∂_t u = Δ_∇ u + f`, `u(0) = 0` — is
additive in the forcing term.  Like the time-derivative field
(`maximalRegularityDerivField_add`), additivity holds mode by mode: the per-mode
solution coordinate `solModeCoeff` is the composition of the linear maps
`timeModeCoeff` and `perModeConvL2`.  This is the algebraic identity that lets
the homogeneous part cancel in the difference of two Duhamel images. -/

/-- The maximal-regularity solution field is additive in the forcing term:
`maximalRegularitySolField (f + f') = maximalRegularitySolField f +
maximalRegularitySolField f'`. -/
theorem maximalRegularitySolField_add (hT : 0 ≤ T)
    (f f' : timeL2 (tensorHs (I := I) (M := M) g r s a) T) :
    maximalRegularitySolField (I := I) (M := M) h_atlas a hT (f + f') =
      maximalRegularitySolField (I := I) (M := M) h_atlas a hT f +
        maximalRegularitySolField (I := I) (M := M) h_atlas a hT f' := by
  refine timeModeCoeff_injective (I := I) (M := M) h_atlas (fun i => ?_)
  rw [maximalRegularitySolField_timeModeCoeff (I := I) (M := M) (a := a)
      hT (f + f') i,
    timeModeCoeff_add (I := I) (M := M),
    maximalRegularitySolField_timeModeCoeff (I := I) (M := M) (a := a) hT f i,
    maximalRegularitySolField_timeModeCoeff (I := I) (M := M) (a := a) hT f' i]
  -- `solModeCoeff` is the linear `perModeConvL2` of the linear `timeModeCoeff`.
  rw [solModeCoeff, solModeCoeff, solModeCoeff,
    timeModeCoeff_add (I := I) (M := M), map_add]

/-- The maximal-regularity solution field commutes with subtraction of forcing
terms: `maximalRegularitySolField (f − f') = maximalRegularitySolField f −
maximalRegularitySolField f'`.  This is the form consumed by the contraction
estimate: it identifies the difference of two Duhamel solution fields (after the
homogeneous part has cancelled) with the solution field of the difference. -/
theorem maximalRegularitySolField_sub (hT : 0 ≤ T)
    (f f' : timeL2 (tensorHs (I := I) (M := M) g r s a) T) :
    maximalRegularitySolField (I := I) (M := M) h_atlas a hT (f - f') =
      maximalRegularitySolField (I := I) (M := M) h_atlas a hT f -
        maximalRegularitySolField (I := I) (M := M) h_atlas a hT f' := by
  have hadd := maximalRegularitySolField_add (I := I) (M := M)
    (h_atlas := h_atlas) (a := a) hT (f - f') f'
  rw [sub_add_cancel] at hadd
  rw [hadd, add_sub_cancel_right]

/-! ## The `H^{a+2}`-field contraction estimate of the affine Duhamel map

For a fixed initial datum the homogeneous part of the affine Duhamel map cancels
in a difference of two `H^{a+2}`-valued fields, leaving the difference of the
maximal-regularity solution fields.  The two-derivative-gain bound
`maximalRegularityOp_norm_Ha2_le` (`‖·‖ ≤ (1 + T)‖·‖`) then controls it by the
`L²([0,T]; Hᵃ)` distance of the forcings.  This is the estimate the
forcing-space fixed point feeds through the Nemytskii operator. -/

/-- **The `H^{a+2}`-field difference of the affine Duhamel map equals the
maximal-regularity solution field of the difference of the forcings.**  For a
fixed initial datum the homogeneous-flow field cancels:

  `maxRegDuhamelSolField … u₀ g − maxRegDuhamelSolField … u₀ g'
    = maximalRegularitySolField (g − g')`. -/
theorem maxRegDuhamelSolField_sub (hT : 0 < T) (hT1 : T ≤ 1)
    (u₀ : tensorHs (I := I) (M := M) g r s (a + 2))
    (gforce gforce' : timeL2 (tensorHs (I := I) (M := M) g r s a) T) :
    maxRegDuhamelSolField (I := I) (M := M) h_atlas a hT hT1 u₀ gforce -
        maxRegDuhamelSolField (I := I) (M := M) h_atlas a hT hT1 u₀ gforce' =
      maximalRegularitySolField (I := I) (M := M) h_atlas a hT.le
        (gforce - gforce') := by
  rw [maximalRegularitySolField_sub (I := I) (M := M) (h_atlas := h_atlas)
    (a := a) hT.le gforce gforce']
  -- The homogeneous-flow fields cancel; only the solution fields survive.
  rw [maxRegDuhamelSolField, maxRegDuhamelSolField]
  abel

/-- **The `H^{a+2}`-field contraction estimate of the affine Duhamel map.**  For
a fixed initial datum `u₀` and two forcing terms `g, g' ∈ L²([0,T]; Hᵃ)`,

  `‖maxRegDuhamelSolField … u₀ g − maxRegDuhamelSolField … u₀ g'‖_{L²(H^{a+2})}
    ≤ (1 + T)·‖g − g'‖_{L²(Hᵃ)}`.

The homogeneous part cancels in the difference (`maxRegDuhamelSolField_sub`),
leaving `maximalRegularitySolField (g − g')`, whose `L²([0,T]; H^{a+2})` norm is
bounded by `(1 + T)·‖g − g'‖` (the two-derivative-gain maximal-regularity
estimate `maximalRegularityOp_norm_Ha2_le`). -/
theorem maxRegDuhamelSolField_dist_le (hT : 0 < T) (hT1 : T ≤ 1)
    (u₀ : tensorHs (I := I) (M := M) g r s (a + 2))
    (gforce gforce' : timeL2 (tensorHs (I := I) (M := M) g r s a) T) :
    ‖maxRegDuhamelSolField (I := I) (M := M) h_atlas a hT hT1 u₀ gforce -
        maxRegDuhamelSolField (I := I) (M := M) h_atlas a hT hT1 u₀ gforce'‖ ≤
      (1 + T) * ‖gforce - gforce'‖ := by
  rw [maxRegDuhamelSolField_sub (I := I) (M := M) (h_atlas := h_atlas)
    (a := a) hT hT1 u₀ gforce gforce']
  exact maximalRegularityOp_norm_Ha2_le (I := I) (M := M) (h_atlas := h_atlas)
    (a := a) hT hT1 (gforce - gforce')

/-! ## The forcing-space fixed-point map

The quasi-linear Duhamel map `Φ(g) = N ∘ (maxRegDuhamelSolField … u₀ g)`: it
sends a forcing `g ∈ L²([0,T]; Hᵃ)` to the pointwise composition of `N` with the
`H^{a+2}`-valued Duhamel solution field of `g`.  A fixed point `g⋆ = Φ(g⋆)`
reproduces the nonlinearity, `g⋆ = N ∘ (field of the Duhamel solution)`, and the
associated Duhamel image is a strong solution of the quasi-linear equation. -/

section FixedPoint

/-- **The forcing-space fixed-point map of the quasi-linear equation.**  For an
initial datum `u₀ ∈ H^{a+2}` and a Lipschitz nonlinearity `N`,

  `quasilinearDuhamelMap … u₀ hN (g) := N ∘ (maxRegDuhamelSolField … u₀ g)`,

a self-map of the forcing space `L²([0,T]; Hᵃ)`.  It first forms the
`H^{a+2}`-valued Duhamel solution field of the forcing `g`, then applies the
Nemytskii operator (pointwise composition with `N`).  A fixed point `g⋆ = Φ(g⋆)`
is a forcing term reproducing `N(u)` along its own Duhamel solution; the
quasi-linear strong solution is the Duhamel image of `g⋆`. -/
def quasilinearDuhamelMap (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (a : ℝ) {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (u₀ : tensorHs (I := I) (M := M) g r s (a + 2))
    {L : ℝ≥0}
    {N : tensorHs (I := I) (M := M) g r s (a + 2) →
      tensorHs (I := I) (M := M) g r s a}
    (hN : LipschitzWith L N) :
    timeL2 (tensorHs (I := I) (M := M) g r s a) T →
      timeL2 (tensorHs (I := I) (M := M) g r s a) T :=
  fun gforce => nemytskii (I := I) (M := M) hN
    (maxRegDuhamelSolField (I := I) (M := M) h_atlas a hT hT1 u₀ gforce)

@[simp] theorem quasilinearDuhamelMap_apply (hT : 0 < T) (hT1 : T ≤ 1)
    (u₀ : tensorHs (I := I) (M := M) g r s (a + 2))
    {L : ℝ≥0}
    {N : tensorHs (I := I) (M := M) g r s (a + 2) →
      tensorHs (I := I) (M := M) g r s a}
    (hN : LipschitzWith L N)
    (gforce : timeL2 (tensorHs (I := I) (M := M) g r s a) T) :
    quasilinearDuhamelMap (I := I) (M := M) h_atlas a hT hT1 u₀ hN gforce =
      nemytskii (I := I) (M := M) hN
        (maxRegDuhamelSolField (I := I) (M := M) h_atlas a hT hT1 u₀ gforce) :=
  rfl

/-- **The Lipschitz bound of the forcing-space fixed-point map.**  For a fixed
initial datum `u₀` and two forcing terms `g, g' ∈ L²([0,T]; Hᵃ)`,

  `‖Φ(g) − Φ(g')‖ ≤ (L : ℝ)·(1 + T)·‖g − g'‖`.

The Nemytskii operator contributes the Lipschitz factor `L`
(`nemytskii_lipschitzWith`); the `H^{a+2}`-field contraction estimate
`maxRegDuhamelSolField_dist_le` contributes the factor `(1 + T)`. -/
theorem quasilinearDuhamelMap_dist_le (hT : 0 < T) (hT1 : T ≤ 1)
    (u₀ : tensorHs (I := I) (M := M) g r s (a + 2))
    {L : ℝ≥0}
    {N : tensorHs (I := I) (M := M) g r s (a + 2) →
      tensorHs (I := I) (M := M) g r s a}
    (hN : LipschitzWith L N)
    (gforce gforce' : timeL2 (tensorHs (I := I) (M := M) g r s a) T) :
    dist (quasilinearDuhamelMap (I := I) (M := M) h_atlas a hT hT1 u₀ hN gforce)
        (quasilinearDuhamelMap (I := I) (M := M) h_atlas a hT hT1 u₀ hN
          gforce') ≤
      (L : ℝ) * (1 + T) * dist gforce gforce' := by
  -- The Nemytskii Lipschitz step.
  have hnem := (nemytskii_lipschitzWith (I := I) (M := M) hN).dist_le_mul
    (maxRegDuhamelSolField (I := I) (M := M) h_atlas a hT hT1 u₀ gforce)
    (maxRegDuhamelSolField (I := I) (M := M) h_atlas a hT hT1 u₀ gforce')
  -- The `H^{a+2}`-field contraction step, in `dist` form.
  have hfield : dist
      (maxRegDuhamelSolField (I := I) (M := M) h_atlas a hT hT1 u₀ gforce)
      (maxRegDuhamelSolField (I := I) (M := M) h_atlas a hT hT1 u₀ gforce') ≤
        (1 + T) * dist gforce gforce' := by
    rw [dist_eq_norm, dist_eq_norm]
    exact maxRegDuhamelSolField_dist_le (I := I) (M := M)
      (h_atlas := h_atlas) (a := a) hT hT1 u₀ gforce gforce'
  -- Chain the two estimates.
  calc dist
        (quasilinearDuhamelMap (I := I) (M := M) h_atlas a hT hT1 u₀ hN gforce)
        (quasilinearDuhamelMap (I := I) (M := M) h_atlas a hT hT1 u₀ hN
          gforce')
      ≤ (L : ℝ) * dist
          (maxRegDuhamelSolField (I := I) (M := M) h_atlas a hT hT1 u₀ gforce)
          (maxRegDuhamelSolField (I := I) (M := M) h_atlas a hT hT1 u₀
            gforce') := hnem
    _ ≤ (L : ℝ) * ((1 + T) * dist gforce gforce') :=
        mul_le_mul_of_nonneg_left hfield L.coe_nonneg
    _ = (L : ℝ) * (1 + T) * dist gforce gforce' := by ring

/-- The contraction constant `(L : ℝ)·(1 + T)` is `< 1` whenever `2·L < 1` and
`T ≤ 1`: from `T ≤ 1` one has `1 + T ≤ 2`, so `(L : ℝ)·(1 + T) ≤ 2·L < 1`. -/
theorem quasilinear_contraction_const_lt_one {L : ℝ≥0} {T : ℝ} (hT1 : T ≤ 1)
    (hL : 2 * (L : ℝ) < 1) :
    (L : ℝ) * (1 + T) < 1 := by
  have hLnn : (0 : ℝ) ≤ (L : ℝ) := L.coe_nonneg
  have h1T : (1 : ℝ) + T ≤ 2 := by linarith
  calc (L : ℝ) * (1 + T) ≤ (L : ℝ) * 2 :=
        mul_le_mul_of_nonneg_left h1T hLnn
    _ = 2 * (L : ℝ) := by ring
    _ < 1 := hL

/-- **The forcing-space fixed-point map is a contraction.**  For a fixed initial
datum `u₀`, a Lipschitz nonlinearity `N` with constant `L`, and `0 < T ≤ 1` with
the smallness hypothesis `2·L < 1`, the quasi-linear Duhamel map `Φ` is a
`ContractingWith` self-map of the forcing space `L²([0,T]; Hᵃ)` with contraction
constant `(L : ℝ)·(1 + T)`.

The contraction constant is `< 1` by `quasilinear_contraction_const_lt_one`; the
`LipschitzWith` property is the global `dist` bound
`quasilinearDuhamelMap_dist_le`. -/
theorem quasilinearDuhamelMap_contracting (hT : 0 < T) (hT1 : T ≤ 1)
    (u₀ : tensorHs (I := I) (M := M) g r s (a + 2))
    {L : ℝ≥0}
    {N : tensorHs (I := I) (M := M) g r s (a + 2) →
      tensorHs (I := I) (M := M) g r s a}
    (hN : LipschitzWith L N) (hL : 2 * (L : ℝ) < 1) :
    ContractingWith
      ⟨(L : ℝ) * (1 + T),
        mul_nonneg L.coe_nonneg (by linarith [hT.le])⟩
      (quasilinearDuhamelMap (I := I) (M := M) h_atlas a hT hT1 u₀ hN) := by
  refine ⟨?_, ?_⟩
  · -- The contraction constant is `< 1` as an element of `ℝ≥0`.
    rw [← NNReal.coe_lt_coe]
    simpa using quasilinear_contraction_const_lt_one
      (L := L) (T := T) hT1 hL
  · -- `LipschitzWith` from the global `dist` bound.
    refine LipschitzWith.of_dist_le_mul (fun gforce gforce' => ?_)
    have h := quasilinearDuhamelMap_dist_le (I := I) (M := M)
      (h_atlas := h_atlas) (a := a) hT hT1 u₀ hN gforce gforce'
    -- The `ℝ≥0` contraction constant coerces to `(L : ℝ)·(1 + T)`.
    simpa only [NNReal.coe_mk] using h

end FixedPoint

/-! ## Strong existence and uniqueness

The headline theorem.  Under the smallness hypothesis `2·L < 1` the
forcing-space map `Φ` is a contraction; the Banach fixed-point theorem
(`ContractingWith.fixedPoint`) supplies a unique fixed point `g⋆`, and the
affine Duhamel image `u⋆ = maxRegDuhamelMap … u₀ g⋆` is the strong solution.
The fixed-point equation `g⋆ = N ∘ (field of u⋆)` is exactly what converts the
linear equation `∂_t u⋆ = Δ_∇ u⋆ + g⋆` (`maxRegDuhamelMap_timeDeriv_eq`) into
the quasi-linear equation `∂_t u⋆ = Δ_∇ u⋆ + N(field of u⋆)`. -/

/-- **Strong existence for the quasi-linear tensor heat equation.**

For a closed Riemannian manifold `(M, g)`, ranks `(r, s)`, a Sobolev exponent
`a ≥ 0`, an initial datum `u₀ ∈ H^{a+2}`, a time horizon `0 < T ≤ 1`, and a
nonlinearity `N : H^{a+2} → Hᵃ` Lipschitz with constant `L` satisfying the
smallness hypothesis `2·L < 1`, there is a **strong solution** `u` in the
maximal-regularity solution space `H¹([0,T]; Hᵃ)` of the quasi-linear tensor
heat equation

  `∂_t u = Δ_∇ u + N(u)`,  `u(0) = u₀`.

The solution is exhibited together with its forcing term `gforce` — the
`L²([0,T]; Hᵃ)` element reproducing the nonlinearity along the solution's own
Duhamel field.  Precisely, the data `u, gforce` satisfy:

* `u = maxRegDuhamelMap … u₀ gforce` — `u` is the affine Duhamel image of
  `gforce` (so its `H^{a+2}`-valued field is `maxRegDuhamelSolField … u₀
  gforce`);
* `gforce = nemytskii hN (maxRegDuhamelSolField … u₀ gforce)` — the fixed-point
  equation: the forcing reproduces `N` applied to the solution field, i.e.
  `gforce = N(field of u)`;
* `timeH1.trace0 _ _ u = tensorHsInclusion h_atlas _ u₀` — the initial value
  is `u₀` (taken in `Hᵃ` via the spectral inclusion `H^{a+2} ↪ Hᵃ`);
* `timeH1.timeDeriv _ _ u = timeScaleLaplacian h_atlas a (field of u) +
  nemytskii hN (field of u)` — **the equation**: the time derivative equals the
  rough Laplacian of the `H^{a+2}`-valued solution field plus the Nemytskii
  nonlinearity applied to that same field, `∂_t u = Δ_∇ u + N(u)`.

The solution is the affine Duhamel image of the unique fixed point of the
forcing-space contraction `quasilinearDuhamelMap`. -/
theorem quasilinear_strong_existence {L : ℝ≥0}
    {N : tensorHs (I := I) (M := M) g r s (a + 2) →
      tensorHs (I := I) (M := M) g r s a}
    (hT : 0 < T) (hT1 : T ≤ 1)
    (u₀ : tensorHs (I := I) (M := M) g r s (a + 2))
    (hN : LipschitzWith L N) (hL : 2 * (L : ℝ) < 1) :
    ∃ (u : MaxRegSolutionSpace (I := I) (M := M) h_atlas a T)
      (gforce : timeL2 (tensorHs (I := I) (M := M) g r s a) T),
      u = maxRegDuhamelMap (I := I) (M := M) h_atlas a hT hT1 u₀ gforce ∧
        gforce = nemytskii (I := I) (M := M) hN
            (maxRegDuhamelSolField (I := I) (M := M) h_atlas a hT hT1 u₀
              gforce) ∧
        TimeSobolev.timeH1.trace0 _ T u =
            tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
              (show a ≤ a + 2 by linarith) u₀ ∧
        TimeSobolev.timeH1.timeDeriv _ T u =
          timeScaleLaplacian (I := I) (M := M) h_atlas a
              (maxRegDuhamelSolField (I := I) (M := M) h_atlas a hT hT1 u₀
                gforce) +
            nemytskii (I := I) (M := M) hN
              (maxRegDuhamelSolField (I := I) (M := M) h_atlas a hT hT1 u₀
                gforce) := by
  -- The forcing-space map is a contraction; take its Banach fixed point.
  have hcontr := quasilinearDuhamelMap_contracting (I := I) (M := M)
    (h_atlas := h_atlas) (a := a) hT hT1 u₀ hN hL
  set gStar := ContractingWith.fixedPoint
    (quasilinearDuhamelMap (I := I) (M := M) h_atlas a hT hT1 u₀ hN) hcontr
    with hgStar_def
  -- The fixed-point equation `Φ(gStar) = gStar`, i.e. `gStar = N ∘ (field)`.
  have hgStar_fix :
      quasilinearDuhamelMap (I := I) (M := M) h_atlas a hT hT1 u₀ hN gStar =
        gStar :=
    ContractingWith.fixedPoint_isFixedPt hcontr
  have hgStar_eq : gStar = nemytskii (I := I) (M := M) hN
      (maxRegDuhamelSolField (I := I) (M := M) h_atlas a hT hT1 u₀ gStar) := by
    rw [← quasilinearDuhamelMap_apply (I := I) (M := M) (a := a) hT hT1 u₀ hN
      gStar, hgStar_fix]
  -- The strong solution is the affine Duhamel image of the fixed point.
  refine ⟨maxRegDuhamelMap (I := I) (M := M) h_atlas a hT hT1 u₀ gStar,
    gStar, rfl, hgStar_eq, ?_, ?_⟩
  · -- Initial condition: the trace of the Duhamel image is `u₀`.
    exact maxRegDuhamelMap_trace0 (I := I) (M := M) (a := a) (T := T)
      hT hT1 u₀ gStar
  · -- The equation `∂_t u = Δ_∇ (field) + N(field)`: the linear heat-equation
    -- lemma gives `∂_t u = Δ_∇ (field) + gStar`, and the fixed-point equation
    -- rewrites the trailing forcing `gStar` as the Nemytskii nonlinearity.
    rw [maxRegDuhamelMap_timeDeriv_eq (I := I) (M := M) (a := a) (T := T)
      hT hT1 u₀ gStar]
    exact congrArg₂ (· + ·) rfl hgStar_eq

/-- **Uniqueness of the quasi-linear strong solution.**

The strong solution produced by the forcing-space fixed-point construction is
unique: any two forcing terms `g₁, g₂ ∈ L²([0,T]; Hᵃ)` that both solve the
fixed-point equation

  `gᵢ = nemytskii hN (maxRegDuhamelSolField … u₀ gᵢ)`

coincide.  Consequently the strong solutions `maxRegDuhamelMap … u₀ gᵢ` they
generate are equal.

This is uniqueness of the Banach fixed point of the contraction
`quasilinearDuhamelMap`: a forcing term solving the fixed-point equation is by
definition a fixed point of `Φ`, and a contraction has a unique fixed point. -/
theorem quasilinear_strong_unique {L : ℝ≥0}
    {N : tensorHs (I := I) (M := M) g r s (a + 2) →
      tensorHs (I := I) (M := M) g r s a}
    (hT : 0 < T) (hT1 : T ≤ 1)
    (u₀ : tensorHs (I := I) (M := M) g r s (a + 2))
    (hN : LipschitzWith L N) (hL : 2 * (L : ℝ) < 1)
    {gforce₁ gforce₂ : timeL2 (tensorHs (I := I) (M := M) g r s a) T}
    (hg₁ : gforce₁ = nemytskii (I := I) (M := M) hN
      (maxRegDuhamelSolField (I := I) (M := M) h_atlas a hT hT1 u₀ gforce₁))
    (hg₂ : gforce₂ = nemytskii (I := I) (M := M) hN
      (maxRegDuhamelSolField (I := I) (M := M) h_atlas a hT hT1 u₀ gforce₂)) :
    gforce₁ = gforce₂ ∧
      maxRegDuhamelMap (I := I) (M := M) h_atlas a hT hT1 u₀ gforce₁ =
        maxRegDuhamelMap (I := I) (M := M) h_atlas a hT hT1 u₀ gforce₂ := by
  -- The forcing-space map is a contraction.
  have hcontr := quasilinearDuhamelMap_contracting (I := I) (M := M)
    (h_atlas := h_atlas) (a := a) hT hT1 u₀ hN hL
  -- Both forcings are fixed points of the contraction `Φ`.
  have hfix₁ :
      Function.IsFixedPt
        (quasilinearDuhamelMap (I := I) (M := M) h_atlas a hT hT1 u₀ hN)
        gforce₁ := by
    change quasilinearDuhamelMap (I := I) (M := M) h_atlas a hT hT1 u₀ hN
        gforce₁ = gforce₁
    rw [quasilinearDuhamelMap_apply (I := I) (M := M) (a := a) hT hT1 u₀ hN
      gforce₁]
    exact hg₁.symm
  have hfix₂ :
      Function.IsFixedPt
        (quasilinearDuhamelMap (I := I) (M := M) h_atlas a hT hT1 u₀ hN)
        gforce₂ := by
    change quasilinearDuhamelMap (I := I) (M := M) h_atlas a hT hT1 u₀ hN
        gforce₂ = gforce₂
    rw [quasilinearDuhamelMap_apply (I := I) (M := M) (a := a) hT hT1 u₀ hN
      gforce₂]
    exact hg₂.symm
  -- Uniqueness of the Banach fixed point identifies the two forcings.
  have hgeq : gforce₁ = gforce₂ := by
    rw [ContractingWith.fixedPoint_unique hcontr hfix₁,
      ContractingWith.fixedPoint_unique hcontr hfix₂]
  exact ⟨hgeq, by rw [hgeq]⟩

end QuasiLinear
end Parabolic
end Analysis
end DifferentialGeometry

end
