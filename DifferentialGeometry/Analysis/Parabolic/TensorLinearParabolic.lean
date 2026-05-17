import DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.SemigroupTimeRegularity
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Duhamel mild solution of the inhomogeneous tensor heat equation on `L²`

For a closed Riemannian manifold `(M, g)`, ranks `(r, s)`, and a uniform
tensor Sobolev bound `h_atlas`, given an initial datum
`T_0 : TensorL2 r s g` and a continuous forcing term
`F : ℝ → TensorL2 r s g`, the **Duhamel mild solution** of the
inhomogeneous tensor heat equation
`∂_t T = Δ_∇ T + F`, `T(0) = T_0`, is

  `T(t) := tensorHeatSemigroup g r s h_atlas t T_0
           + ∫_0^t tensorHeatSemigroup g r s h_atlas (t - τ) (F τ) dτ`,

where the second summand is a Bochner-valued interval integral on `[0, t]`.

This file constructs `tensorMildSolution` and establishes the initial
value and the integrability of the Duhamel integrand.

## Main definitions

* `tensorMildSolution g r s h_atlas T_0 F t` — the Duhamel formula.

## Main results

* `tensorMildSolution_zero` — `tensorMildSolution _ _ _ _ T_0 F 0 = T_0`.
* `tensorIntegrable_heatSemigroup_apply_F` — the Duhamel integrand
  `τ ↦ tensorHeatSemigroup g r s h_atlas (t - τ) (F τ)` is
  interval-integrable on `[0, t]` whenever `F` is continuous and
  `0 ≤ t`.
-/

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Geometry

/-! ## File-local Borel-space instances on `E` and `M` -/

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

/-! ## Definition of the tensor mild solution -/

/-- The Duhamel mild solution of the inhomogeneous tensor heat equation
`∂_t T = Δ_∇ T + F`, `T(0) = T_0`, on the closed Riemannian manifold
`(M, g)` for ranks `(r, s)`. -/
noncomputable def tensorMildSolution
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : HasLocallyConstantChartAt H M)
    (T_0 : TensorL2 r s g)
    (F : ℝ → TensorL2 r s g)
    (t : ℝ) :
    TensorL2 r s g :=
  tensorHeatSemigroup (I := I) (M := M) g r s h_atlas t T_0 +
    ∫ τ in (0 : ℝ)..t,
      tensorHeatSemigroup (I := I) (M := M) g r s h_atlas (t - τ) (F τ)

/-! ## Initial condition -/

/-- At `t = 0` the tensor mild solution recovers the initial datum. -/
theorem tensorMildSolution_zero
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (h_atlas : HasLocallyConstantChartAt H M)
    (T_0 : TensorL2 r s g) (F : ℝ → TensorL2 r s g) :
    tensorMildSolution (I := I) (M := M) g r s h_atlas T_0 F 0 = T_0 := by
  unfold tensorMildSolution
  rw [intervalIntegral.integral_same, add_zero]
  rw [tensorHeatSemigroup_zero (I := I) (M := M) h_atlas]
  rfl

/-! ## Integrability of the integrand on `[0, t]` -/

/-- The Duhamel integrand `τ ↦ tensorHeatSemigroup g r s h_atlas (t - τ) (F τ)`
is interval-integrable on `[0, t]` for `t ≥ 0` and continuous `F`. -/
private lemma tensorIntegrable_heatSemigroup_apply_F
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (h_atlas : HasLocallyConstantChartAt H M)
    {F : ℝ → TensorL2 r s g} (hF : Continuous F) {t : ℝ} (ht : 0 ≤ t) :
    IntervalIntegrable
      (fun τ : ℝ =>
        tensorHeatSemigroup (I := I) (M := M) g r s h_atlas (t - τ) (F τ))
      MeasureTheory.volume 0 t := by
  have h_cont :=
    tensorHeatSemigroup_apply_F_continuous
      (I := I) (M := M) h_atlas hF t
  have h_uIcc : Set.uIcc (0 : ℝ) t = Set.Icc 0 t := Set.uIcc_of_le ht
  rw [← h_uIcc] at h_cont
  exact h_cont.intervalIntegrable

/-! ## Linearity in the data

The Duhamel mild solution decomposes naturally as the sum of the homogeneous
and inhomogeneous parts:
`tensorMildSolution g r s h_atlas T_0 F t =
  tensorMildSolution g r s h_atlas T_0 0 t +
  tensorMildSolution g r s h_atlas 0 F t`.
We express the linearity in the initial datum and in the forcing term using
this splitting. -/

/-- Linearity of the tensor mild solution in the initial datum: additivity.
The contribution of the additional initial datum `V_0` enters as the
homogeneous part `tensorMildSolution g r s h_atlas V_0 0`. -/
theorem tensorMildSolution_add_initial
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (h_atlas : HasLocallyConstantChartAt H M)
    (T_0 V_0 : TensorL2 r s g)
    (F : ℝ → TensorL2 r s g) (t : ℝ) :
    tensorMildSolution (I := I) (M := M) g r s h_atlas (T_0 + V_0) F t =
      tensorMildSolution (I := I) (M := M) g r s h_atlas T_0 F t +
        tensorMildSolution (I := I) (M := M) g r s h_atlas V_0
          (fun _ => 0) t := by
  unfold tensorMildSolution
  -- The Duhamel integral with zero forcing vanishes.
  have h_zero_int :
      ∫ τ in (0 : ℝ)..t,
          tensorHeatSemigroup (I := I) (M := M) g r s h_atlas (t - τ)
            (0 : TensorL2 r s g) =
        (0 : TensorL2 r s g) := by
    have h_eq : (fun τ : ℝ =>
        tensorHeatSemigroup (I := I) (M := M) g r s h_atlas (t - τ)
          (0 : TensorL2 r s g)) =
        (fun _ : ℝ => (0 : TensorL2 r s g)) := by
      funext τ
      rw [(tensorHeatSemigroup
        (I := I) (M := M) g r s h_atlas (t - τ)).map_zero]
    rw [h_eq, intervalIntegral.integral_zero]
  rw [h_zero_int, add_zero]
  -- The heat semigroup splits additively on the initial datum.
  have h_add : tensorHeatSemigroup
      (I := I) (M := M) g r s h_atlas t (T_0 + V_0) =
      tensorHeatSemigroup (I := I) (M := M) g r s h_atlas t T_0 +
        tensorHeatSemigroup (I := I) (M := M) g r s h_atlas t V_0 := by
    rw [(tensorHeatSemigroup (I := I) (M := M) g r s h_atlas t).map_add]
  rw [h_add]
  abel

/-- Linearity of the tensor mild solution in the initial datum: scalar
homogeneity. The forcing-term contribution stays unscaled; only the
heat-semigroup part scales with `c`. -/
theorem tensorMildSolution_smul_initial
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (h_atlas : HasLocallyConstantChartAt H M)
    (c : ℝ) (T_0 : TensorL2 r s g)
    (F : ℝ → TensorL2 r s g) (t : ℝ) :
    tensorMildSolution (I := I) (M := M) g r s h_atlas (c • T_0) F t =
      c • tensorMildSolution (I := I) (M := M) g r s h_atlas T_0
            (fun _ => 0) t +
        tensorMildSolution (I := I) (M := M) g r s h_atlas 0 F t := by
  unfold tensorMildSolution
  -- The Duhamel integral with zero forcing vanishes.
  have h_zero_int :
      ∫ τ in (0 : ℝ)..t,
          tensorHeatSemigroup (I := I) (M := M) g r s h_atlas (t - τ)
            (0 : TensorL2 r s g) =
        (0 : TensorL2 r s g) := by
    have h_eq : (fun τ : ℝ =>
        tensorHeatSemigroup (I := I) (M := M) g r s h_atlas (t - τ)
          (0 : TensorL2 r s g)) =
        (fun _ : ℝ => (0 : TensorL2 r s g)) := by
      funext τ
      rw [(tensorHeatSemigroup
        (I := I) (M := M) g r s h_atlas (t - τ)).map_zero]
    rw [h_eq, intervalIntegral.integral_zero]
  -- Heat semigroup applied to the zero initial datum is zero.
  have h_heat_zero :
      tensorHeatSemigroup (I := I) (M := M) g r s h_atlas t
          (0 : TensorL2 r s g) = 0 := by
    rw [(tensorHeatSemigroup (I := I) (M := M) g r s h_atlas t).map_zero]
  rw [h_zero_int, add_zero, h_heat_zero, zero_add]
  rw [(tensorHeatSemigroup (I := I) (M := M) g r s h_atlas t).map_smul]

/-- Linearity of the tensor mild solution in the forcing term: additivity
(with the homogeneous-initial-datum splitting). -/
theorem tensorMildSolution_add_forcing
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (h_atlas : HasLocallyConstantChartAt H M)
    (T_0 : TensorL2 r s g)
    (F G : ℝ → TensorL2 r s g) (hF : Continuous F) (hG : Continuous G)
    {t : ℝ} (ht : 0 ≤ t) :
    tensorMildSolution (I := I) (M := M) g r s h_atlas T_0
        (fun τ => F τ + G τ) t =
      tensorMildSolution (I := I) (M := M) g r s h_atlas T_0 F t +
        tensorMildSolution (I := I) (M := M) g r s h_atlas 0 G t := by
  unfold tensorMildSolution
  -- Heat semigroup on the zero initial datum is zero.
  have h_heat_zero :
      tensorHeatSemigroup (I := I) (M := M) g r s h_atlas t
          (0 : TensorL2 r s g) = 0 := by
    rw [(tensorHeatSemigroup (I := I) (M := M) g r s h_atlas t).map_zero]
  rw [h_heat_zero, zero_add]
  -- The integrand splits additively.
  have h_split : ∀ τ,
      tensorHeatSemigroup (I := I) (M := M) g r s h_atlas (t - τ)
          (F τ + G τ) =
        tensorHeatSemigroup (I := I) (M := M) g r s h_atlas (t - τ) (F τ) +
          tensorHeatSemigroup (I := I) (M := M) g r s h_atlas (t - τ)
            (G τ) := by
    intro τ
    rw [(tensorHeatSemigroup
      (I := I) (M := M) g r s h_atlas (t - τ)).map_add]
  have h_eq_fun :
      (fun τ : ℝ =>
          tensorHeatSemigroup (I := I) (M := M) g r s h_atlas (t - τ)
            (F τ + G τ)) =
        (fun τ : ℝ =>
          tensorHeatSemigroup (I := I) (M := M) g r s h_atlas (t - τ)
              (F τ) +
            tensorHeatSemigroup (I := I) (M := M) g r s h_atlas (t - τ)
              (G τ)) := by
    funext τ; exact h_split τ
  rw [h_eq_fun]
  rw [intervalIntegral.integral_add
    (tensorIntegrable_heatSemigroup_apply_F
      (I := I) (M := M) h_atlas hF ht)
    (tensorIntegrable_heatSemigroup_apply_F
      (I := I) (M := M) h_atlas hG ht)]
  abel

/-! ## Continuity in `t` on `[0, ∞)`

The continuity proof uses a clipped representation of the integrand.
The integrand `(t, τ) ↦ tensorHeatSemigroup g r s h_atlas (t - τ) (F τ)`
is not jointly continuous on `ℝ × ℝ` (it has a jump along `t = τ`, since
the tensor heat semigroup is set to `0` for negative time). However, the
clipped variant

  `tensorClippedKernel (t, τ) :=
      tensorHeatSemigroup g r s h_atlas (max 0 (t - τ)) (F τ)`

is jointly continuous everywhere, and on the relevant domain `τ ∈ [0, t]`
with `t ≥ 0` we have `max 0 (t - τ) = t - τ`, so the two integrands give
the same integral. We then apply Mathlib's parametric interval-integral
continuity result to the clipped form. -/

/-- The clipped Duhamel kernel:
`tensorHeatSemigroup g r s h_atlas (max 0 (t - τ)) (F τ)`. Globally
jointly continuous in `(t, τ)`, and equal to the Duhamel integrand on
`τ ∈ [0, t]` for `t ≥ 0`. -/
private noncomputable def tensorClippedKernel
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : HasLocallyConstantChartAt H M)
    (F : ℝ → TensorL2 r s g) (t τ : ℝ) : TensorL2 r s g :=
  tensorHeatSemigroup (I := I) (M := M) g r s h_atlas (max 0 (t - τ)) (F τ)

/-- Joint continuity of the clipped Duhamel kernel. -/
private lemma continuous_tensorClippedKernel
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (h_atlas : HasLocallyConstantChartAt H M)
    {F : ℝ → TensorL2 r s g} (hF : Continuous F) :
    Continuous
      (Function.uncurry
        (tensorClippedKernel (I := I) (M := M) g r s h_atlas F)) := by
  -- Continuity at every point `(t₀, τ₀)` using the
  -- bounded-+-strong-continuity decomposition.
  refine continuous_iff_continuousAt.mpr (fun ⟨t₀, τ₀⟩ => ?_)
  -- `σ₀ := max 0 (t₀ - τ₀) ≥ 0`.
  set σ₀ : ℝ := max 0 (t₀ - τ₀) with hσ₀_def
  have hσ₀_nn : 0 ≤ σ₀ := le_max_left _ _
  set K : ℝ × ℝ → TensorL2 r s g :=
    Function.uncurry (tensorClippedKernel (I := I) (M := M) g r s h_atlas F)
    with hK_def
  -- Bound for `(t, τ)`:
  --   `‖K (t,τ) − K (t₀,τ₀)‖
  --      ≤ ‖F τ − F τ₀‖
  --      + ‖e^{σ(t,τ)Δ_∇} (F τ₀) − e^{σ₀Δ_∇} (F τ₀)‖`
  -- where `σ(t,τ) := max 0 (t − τ)`.
  have h_bound : ∀ p : ℝ × ℝ,
      ‖K p - K (t₀, τ₀)‖ ≤
        ‖F p.2 - F τ₀‖ +
        ‖tensorHeatSemigroup (I := I) (M := M) g r s h_atlas
              (max 0 (p.1 - p.2)) (F τ₀) -
            tensorHeatSemigroup
              (I := I) (M := M) g r s h_atlas σ₀ (F τ₀)‖ := by
    rintro ⟨t, τ⟩
    have hσ_nn : 0 ≤ max 0 (t - τ) := le_max_left _ _
    have h_decomp : K (t, τ) - K (t₀, τ₀) =
        tensorHeatSemigroup
            (I := I) (M := M) g r s h_atlas (max 0 (t - τ))
            (F τ - F τ₀) +
          (tensorHeatSemigroup
              (I := I) (M := M) g r s h_atlas (max 0 (t - τ)) (F τ₀) -
            tensorHeatSemigroup
              (I := I) (M := M) g r s h_atlas σ₀ (F τ₀)) := by
      change tensorHeatSemigroup
            (I := I) (M := M) g r s h_atlas (max 0 (t - τ)) (F τ) -
          tensorHeatSemigroup
            (I := I) (M := M) g r s h_atlas σ₀ (F τ₀) = _
      rw [(tensorHeatSemigroup
        (I := I) (M := M) g r s h_atlas (max 0 (t - τ))).map_sub]
      abel
    rw [h_decomp]
    have h_norm_sum :=
      norm_add_le
        (tensorHeatSemigroup
          (I := I) (M := M) g r s h_atlas (max 0 (t - τ)) (F τ - F τ₀))
        (tensorHeatSemigroup
            (I := I) (M := M) g r s h_atlas (max 0 (t - τ)) (F τ₀) -
          tensorHeatSemigroup
            (I := I) (M := M) g r s h_atlas σ₀ (F τ₀))
    have h_first_bound :
        ‖tensorHeatSemigroup
            (I := I) (M := M) g r s h_atlas (max 0 (t - τ))
            (F τ - F τ₀)‖ ≤ ‖F τ - F τ₀‖ := by
      have h_op :=
        tensorHeatSemigroup_opNorm_le_one
          (I := I) (M := M) (g := g) (r := r) (s := s)
          (h_atlas := h_atlas) (max 0 (t - τ))
      have h_le := ContinuousLinearMap.le_opNorm
        (tensorHeatSemigroup
          (I := I) (M := M) g r s h_atlas (max 0 (t - τ))) (F τ - F τ₀)
      have h_nn : 0 ≤ ‖F τ - F τ₀‖ := norm_nonneg _
      calc ‖tensorHeatSemigroup
              (I := I) (M := M) g r s h_atlas (max 0 (t - τ))
              (F τ - F τ₀)‖
          ≤ ‖tensorHeatSemigroup
              (I := I) (M := M) g r s h_atlas (max 0 (t - τ))‖ *
              ‖F τ - F τ₀‖ := h_le
        _ ≤ 1 * ‖F τ - F τ₀‖ := mul_le_mul_of_nonneg_right h_op h_nn
        _ = ‖F τ - F τ₀‖ := one_mul _
    linarith [h_norm_sum]
  -- RHS → 0 as `(t, τ) → (t₀, τ₀)`.
  have h_rhs_to_zero :
      Tendsto (fun p : ℝ × ℝ =>
          ‖F p.2 - F τ₀‖ +
          ‖tensorHeatSemigroup (I := I) (M := M) g r s h_atlas
                (max 0 (p.1 - p.2)) (F τ₀) -
              tensorHeatSemigroup
                (I := I) (M := M) g r s h_atlas σ₀ (F τ₀)‖)
        (𝓝 (t₀, τ₀)) (𝓝 0) := by
    have h_F_compose :
        Tendsto (fun p : ℝ × ℝ => F p.2) (𝓝 (t₀, τ₀)) (𝓝 (F τ₀)) :=
      hF.continuousAt.tendsto.comp continuous_snd.continuousAt.tendsto
    have h_term1 :
        Tendsto (fun p : ℝ × ℝ => ‖F p.2 - F τ₀‖)
          (𝓝 (t₀, τ₀)) (𝓝 0) := by
      have h_diff : Tendsto (fun p : ℝ × ℝ => F p.2 - F τ₀)
          (𝓝 (t₀, τ₀)) (𝓝 0) := by
        have := h_F_compose.sub (tendsto_const_nhds (x := F τ₀))
        simpa using this
      have := h_diff.norm
      simpa using this
    have h_max_cont :
        Continuous (fun p : ℝ × ℝ => max 0 (p.1 - p.2)) := by
      have h_sub : Continuous (fun p : ℝ × ℝ => p.1 - p.2) :=
        continuous_fst.sub continuous_snd
      exact continuous_const.max h_sub
    have h_max_to_σ₀ :
        Tendsto (fun p : ℝ × ℝ => max 0 (p.1 - p.2))
          (𝓝 (t₀, τ₀)) (𝓝 σ₀) :=
      h_max_cont.continuousAt
    have h_max_into_Ici :
        ∀ᶠ p : ℝ × ℝ in 𝓝 (t₀, τ₀),
          max 0 (p.1 - p.2) ∈ Set.Ici (0 : ℝ) :=
      Eventually.of_forall
        (fun _ => Set.mem_Ici.mpr (le_max_left _ _))
    have h_max_to_σ₀_within :
        Tendsto (fun p : ℝ × ℝ => max 0 (p.1 - p.2))
          (𝓝 (t₀, τ₀)) (𝓝[Set.Ici (0 : ℝ)] σ₀) := by
      rw [tendsto_nhdsWithin_iff]
      exact ⟨h_max_to_σ₀, h_max_into_Ici⟩
    have h_strong :=
      tensorHeatSemigroup_continuous_on_nonneg
        (I := I) (M := M) h_atlas (F τ₀) σ₀
        (Set.mem_Ici.mpr hσ₀_nn)
    have h_compose :
        Tendsto (fun p : ℝ × ℝ =>
            tensorHeatSemigroup (I := I) (M := M) g r s h_atlas
              (max 0 (p.1 - p.2)) (F τ₀))
          (𝓝 (t₀, τ₀))
          (𝓝 (tensorHeatSemigroup
              (I := I) (M := M) g r s h_atlas σ₀ (F τ₀))) :=
      h_strong.tendsto.comp h_max_to_σ₀_within
    have h_term2 :
        Tendsto (fun p : ℝ × ℝ =>
            ‖tensorHeatSemigroup (I := I) (M := M) g r s h_atlas
                (max 0 (p.1 - p.2)) (F τ₀) -
              tensorHeatSemigroup
                (I := I) (M := M) g r s h_atlas σ₀ (F τ₀)‖)
          (𝓝 (t₀, τ₀)) (𝓝 0) := by
      have h_diff : Tendsto (fun p : ℝ × ℝ =>
          tensorHeatSemigroup (I := I) (M := M) g r s h_atlas
              (max 0 (p.1 - p.2)) (F τ₀) -
            tensorHeatSemigroup
              (I := I) (M := M) g r s h_atlas σ₀ (F τ₀))
          (𝓝 (t₀, τ₀)) (𝓝 0) := by
        have := h_compose.sub (tendsto_const_nhds
          (x := tensorHeatSemigroup
            (I := I) (M := M) g r s h_atlas σ₀ (F τ₀)))
        simpa using this
      have := h_diff.norm
      simpa using this
    have := h_term1.add h_term2
    simpa using this
  -- Squeeze.
  have h_diff_to_zero :
      Tendsto (fun p : ℝ × ℝ => K p - K (t₀, τ₀))
        (𝓝 (t₀, τ₀)) (𝓝 0) :=
    squeeze_zero_norm h_bound h_rhs_to_zero
  have h_target :
      Tendsto K (𝓝 (t₀, τ₀)) (𝓝 (K (t₀, τ₀))) := by
    have h_added := h_diff_to_zero.add
      (tendsto_const_nhds (x := K (t₀, τ₀)))
    simpa using h_added
  exact h_target

/-- The tensor mild solution is continuous on `[0, ∞)`. -/
theorem tensorMildSolution_continuous
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (h_atlas : HasLocallyConstantChartAt H M)
    (T_0 : TensorL2 r s g)
    {F : ℝ → TensorL2 r s g} (hF : Continuous F) :
    ContinuousOn
      (fun t : ℝ =>
        tensorMildSolution (I := I) (M := M) g r s h_atlas T_0 F t)
      (Set.Ici (0 : ℝ)) := by
  -- The first term `tensorHeatSemigroup g r s h_atlas t T_0` is
  -- `ContinuousOn [0, ∞)`.
  have h_first_cont :=
    tensorHeatSemigroup_continuous_on_nonneg
      (I := I) (M := M) h_atlas T_0
  -- For the second term, replace the original integrand with the clipped
  -- one on `t ≥ 0`. Then the clipped integrand is jointly continuous, and
  -- the parametric interval-integral continuity lemma gives continuity
  -- in `t`.
  have h_clip_eq : ∀ t : ℝ, 0 ≤ t →
      tensorMildSolution (I := I) (M := M) g r s h_atlas T_0 F t =
        tensorHeatSemigroup (I := I) (M := M) g r s h_atlas t T_0 +
          ∫ τ in (0 : ℝ)..t,
            tensorClippedKernel
              (I := I) (M := M) g r s h_atlas F t τ := by
    intro t ht
    unfold tensorMildSolution
    congr 1
    -- The integrals coincide on `[0, t]` because `t − τ ≥ 0` there.
    apply intervalIntegral.integral_congr
    intro τ hτ
    -- `τ ∈ Set.uIcc 0 t = Set.Icc 0 t` since `0 ≤ t`.
    rw [Set.uIcc_of_le ht] at hτ
    have h_t_minus_τ_nn : 0 ≤ t - τ := sub_nonneg.mpr hτ.2
    change tensorHeatSemigroup
        (I := I) (M := M) g r s h_atlas (t - τ) (F τ) =
      tensorClippedKernel (I := I) (M := M) g r s h_atlas F t τ
    unfold tensorClippedKernel
    rw [max_eq_right h_t_minus_τ_nn]
  -- Continuity of `t ↦ ∫ τ in 0..t, tensorClippedKernel … t τ`.
  have h_kernel_cont :=
    continuous_tensorClippedKernel
      (I := I) (M := M) h_atlas hF
  have h_int_cont :
      Continuous (fun t : ℝ =>
        ∫ τ in (0 : ℝ)..t,
          tensorClippedKernel
            (I := I) (M := M) g r s h_atlas F t τ) := by
    have h :=
      intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
        (μ := MeasureTheory.volume) (a₀ := (0 : ℝ))
        (f := tensorClippedKernel
          (I := I) (M := M) g r s h_atlas F)
        h_kernel_cont (s := id) (continuous_id)
    exact h
  intro t₀ ht₀
  have h_t₀_nn : 0 ≤ t₀ := Set.mem_Ici.mp ht₀
  -- Continuity of the clipped form at every `t₀ ≥ 0`.
  have h_clipped_cont : ContinuousWithinAt
      (fun t : ℝ =>
        tensorHeatSemigroup (I := I) (M := M) g r s h_atlas t T_0 +
          ∫ τ in (0 : ℝ)..t,
            tensorClippedKernel
              (I := I) (M := M) g r s h_atlas F t τ)
      (Set.Ici (0 : ℝ)) t₀ := by
    have h1 := h_first_cont t₀ ht₀
    have h2 : ContinuousWithinAt (fun t : ℝ =>
        ∫ τ in (0 : ℝ)..t,
          tensorClippedKernel
            (I := I) (M := M) g r s h_atlas F t τ)
        (Set.Ici (0 : ℝ)) t₀ := h_int_cont.continuousWithinAt
    exact h1.add h2
  -- The original `tensorMildSolution` is eventually equal to the clipped
  -- form on `Ici 0`.
  apply h_clipped_cont.congr_of_eventuallyEq
  · -- Eventual equality on `Ici 0`.
    rw [Filter.eventuallyEq_iff_exists_mem]
    refine ⟨Set.Ici (0 : ℝ), self_mem_nhdsWithin, ?_⟩
    intro t ht
    exact h_clip_eq t (Set.mem_Ici.mp ht)
  · -- Equality at `t₀`.
    exact h_clip_eq t₀ h_t₀_nn

/-! ## Existence of a Duhamel mild solution

Bundling the initial condition (`tensorMildSolution_zero`), the
continuity on `[0, ∞)` (`tensorMildSolution_continuous`), and the
defining Duhamel formula, we obtain the existence statement for the
inhomogeneous tensor heat equation on the closed Riemannian manifold
`(M, g)`. -/

/-- Existence of a Duhamel mild solution of the inhomogeneous tensor
heat equation `∂_t T = Δ_∇ T + F`, `T(0) = T_0`, on a closed
Riemannian manifold `(M, g)` for ranks `(r, s)`. The solution is
continuous on `[0, ∞)`, satisfies the initial condition, and is given
by the Duhamel formula
`S t = e^{tΔ_∇} T_0 + ∫_0^t e^{(t-τ)Δ_∇} (F τ) dτ`. -/
theorem tensor_linear_parabolic_existence
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : HasLocallyConstantChartAt H M)
    (T_0 : TensorL2 r s g)
    {F : ℝ → TensorL2 r s g} (hF : Continuous F) :
    ∃ S : ℝ → TensorL2 r s g,
      ContinuousOn S (Set.Ici (0 : ℝ)) ∧ S 0 = T_0 ∧
      ∀ t : ℝ, S t = tensorHeatSemigroup g r s h_atlas t T_0 +
        ∫ τ in (0 : ℝ)..t,
          tensorHeatSemigroup g r s h_atlas (t - τ) (F τ) := by
  refine ⟨tensorMildSolution (I := I) (M := M) g r s h_atlas T_0 F,
    ?_, ?_, ?_⟩
  · -- Continuity on `[0, ∞)`.
    exact tensorMildSolution_continuous
      (I := I) (M := M) h_atlas T_0 hF
  · -- Initial condition `S 0 = T_0`.
    exact tensorMildSolution_zero
      (I := I) (M := M) h_atlas T_0 F
  · -- Duhamel formula at every `t`.
    intro t
    rfl

end Parabolic
end Analysis
end DifferentialGeometry

end

section Sanity

#print axioms
  DifferentialGeometry.Analysis.Parabolic.tensorMildSolution

#print axioms
  DifferentialGeometry.Analysis.Parabolic.tensorMildSolution_zero

#print axioms
  DifferentialGeometry.Analysis.Parabolic.tensorMildSolution_add_initial

#print axioms
  DifferentialGeometry.Analysis.Parabolic.tensorMildSolution_smul_initial

#print axioms
  DifferentialGeometry.Analysis.Parabolic.tensorMildSolution_add_forcing

#print axioms
  DifferentialGeometry.Analysis.Parabolic.tensorMildSolution_continuous

#print axioms
  DifferentialGeometry.Analysis.Parabolic.tensor_linear_parabolic_existence

end Sanity
