import DifferentialGeometry.Analysis.HeatEquation.Semigroup
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Duhamel mild solution of the inhomogeneous heat equation on `L²`

For a closed Riemannian manifold `(M, g)`, given an initial datum
`u_0 : Lp ℝ 2 μ_g` and a continuous forcing term `f : ℝ → Lp ℝ 2 μ_g`,
the **Duhamel mild solution** of the inhomogeneous heat equation
`∂_t u = Δ_g u + f`, `u(0) = u_0`, is the function

  `u(t) := heatSemigroup g t u_0 + ∫_0^t heatSemigroup g (t - s) (f s) ds`,

where the second summand is a Bochner-valued interval integral on `[0, t]`.

This file constructs `mildSolution` and establishes its basic properties:
the initial value, linearity in the data, continuity in time, and the
homogeneous reduction `f ≡ 0 ⟹ u = e^{tΔ} u_0`.

## Main definitions

* `mildSolution g u_0 f t` — the Duhamel formula.

## Main results

* `heatSemigroup_continuous_at_pos` — strong continuity at `t₀ > 0`.
* `heatSemigroup_continuous_on_nonneg` — strong continuity on `[0, ∞)`.
* `heatSemigroup_apply_f_continuous` — continuity of
  `s ↦ heatSemigroup g (t - s) (f s)` on `[0, t]`.
* `mildSolution_zero` — `mildSolution g u_0 f 0 = u_0`.
* `mildSolution_add_initial`, `mildSolution_smul_initial`,
  `mildSolution_add_forcing` — linearity in the data.
* `mildSolution_continuous` — continuity on `[0, ∞)`.
* `mildSolution_zero_forcing` — homogeneous reduction.
-/

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace HeatEquation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Laplacian

/-! ## File-local Borel-space instances on `E` and `M` -/

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

variable [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]

/-! ## Strong continuity of the heat semigroup at every nonneg time

We upgrade `heatSemigroup_continuous_at_zero` (right-limit at `0`) to a
two-sided continuity statement at every interior nonneg time, then package
both into a single `ContinuousOn` on `[0, ∞)`. The key contractive estimate
is

  `‖heatSemigroup g t v − heatSemigroup g t₀ v‖ ≤
      ‖heatSemigroup g |t − t₀| v − v‖`,

which holds for all `t, t₀ ≥ 0`: write the larger of `t, t₀` as the sum of
the smaller and `|t - t₀|`, apply the semigroup law, and use contractivity. -/

/-- Contractive comparison estimate: for `t, t₀ ≥ 0`,
`‖heatSemigroup g t v − heatSemigroup g t₀ v‖ ≤
  ‖heatSemigroup g |t − t₀| v − v‖`. -/
private lemma norm_heatSemigroup_sub_le_heatSemigroup_diff
    (g : SmoothRiemannianMetric I M)
    {t t₀ : ℝ} (ht : 0 ≤ t) (ht₀ : 0 ≤ t₀)
    (v : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) :
    ‖heatSemigroup (I := I) (M := M) g t v -
        heatSemigroup (I := I) (M := M) g t₀ v‖ ≤
      ‖heatSemigroup (I := I) (M := M) g |t - t₀| v - v‖ := by
  rcases le_or_gt t₀ t with h | h
  · -- Case t ≥ t₀: use t = t₀ + (t - t₀).
    have h_diff_nn : 0 ≤ t - t₀ := sub_nonneg.mpr h
    have h_abs : |t - t₀| = t - t₀ := abs_of_nonneg h_diff_nn
    have h_law :
        heatSemigroup (I := I) (M := M) g t =
          (heatSemigroup (I := I) (M := M) g t₀).comp
            (heatSemigroup (I := I) (M := M) g (t - t₀)) := by
      have h_add := heatSemigroup_add (I := I) (M := M) g ht₀ h_diff_nn
      have h_eq : t₀ + (t - t₀) = t := by ring
      rw [h_eq] at h_add
      exact h_add
    have h_apply :
        heatSemigroup (I := I) (M := M) g t v =
          heatSemigroup (I := I) (M := M) g t₀
            (heatSemigroup (I := I) (M := M) g (t - t₀) v) := by
      rw [h_law]; rfl
    rw [h_apply]
    have h_sub_eq :
        heatSemigroup (I := I) (M := M) g t₀
            (heatSemigroup (I := I) (M := M) g (t - t₀) v) -
          heatSemigroup (I := I) (M := M) g t₀ v =
        heatSemigroup (I := I) (M := M) g t₀
          (heatSemigroup (I := I) (M := M) g (t - t₀) v - v) := by
      rw [← (heatSemigroup (I := I) (M := M) g t₀).map_sub]
    rw [h_sub_eq]
    have h_norm_le :
        ‖heatSemigroup (I := I) (M := M) g t₀
            (heatSemigroup (I := I) (M := M) g (t - t₀) v - v)‖ ≤
          ‖heatSemigroup (I := I) (M := M) g t₀‖ *
            ‖heatSemigroup (I := I) (M := M) g (t - t₀) v - v‖ :=
      ContinuousLinearMap.le_opNorm _ _
    have h_op_le_one :
        ‖heatSemigroup (I := I) (M := M) g t₀‖ ≤ 1 :=
      heatSemigroup_opNorm_le_one (I := I) (M := M) g ht₀
    have h_norm_nn :
        0 ≤ ‖heatSemigroup (I := I) (M := M) g (t - t₀) v - v‖ := norm_nonneg _
    calc ‖heatSemigroup (I := I) (M := M) g t₀
              (heatSemigroup (I := I) (M := M) g (t - t₀) v - v)‖
        ≤ ‖heatSemigroup (I := I) (M := M) g t₀‖ *
            ‖heatSemigroup (I := I) (M := M) g (t - t₀) v - v‖ := h_norm_le
      _ ≤ 1 * ‖heatSemigroup (I := I) (M := M) g (t - t₀) v - v‖ := by
            exact mul_le_mul_of_nonneg_right h_op_le_one h_norm_nn
      _ = ‖heatSemigroup (I := I) (M := M) g (t - t₀) v - v‖ := one_mul _
      _ = ‖heatSemigroup (I := I) (M := M) g |t - t₀| v - v‖ := by rw [h_abs]
  · -- Case t < t₀: symmetric, use t₀ = t + (t₀ - t).
    have h_diff_nn : 0 ≤ t₀ - t := sub_nonneg.mpr h.le
    have h_abs : |t - t₀| = t₀ - t := by
      rw [abs_sub_comm, abs_of_nonneg h_diff_nn]
    have h_law :
        heatSemigroup (I := I) (M := M) g t₀ =
          (heatSemigroup (I := I) (M := M) g t).comp
            (heatSemigroup (I := I) (M := M) g (t₀ - t)) := by
      have h_add := heatSemigroup_add (I := I) (M := M) g ht h_diff_nn
      have h_eq : t + (t₀ - t) = t₀ := by ring
      rw [h_eq] at h_add
      exact h_add
    have h_apply :
        heatSemigroup (I := I) (M := M) g t₀ v =
          heatSemigroup (I := I) (M := M) g t
            (heatSemigroup (I := I) (M := M) g (t₀ - t) v) := by
      rw [h_law]; rfl
    rw [h_apply]
    have h_sub_eq :
        heatSemigroup (I := I) (M := M) g t v -
          heatSemigroup (I := I) (M := M) g t
            (heatSemigroup (I := I) (M := M) g (t₀ - t) v) =
        heatSemigroup (I := I) (M := M) g t
          (v - heatSemigroup (I := I) (M := M) g (t₀ - t) v) := by
      rw [← (heatSemigroup (I := I) (M := M) g t).map_sub]
    rw [h_sub_eq]
    have h_norm_le :
        ‖heatSemigroup (I := I) (M := M) g t
            (v - heatSemigroup (I := I) (M := M) g (t₀ - t) v)‖ ≤
          ‖heatSemigroup (I := I) (M := M) g t‖ *
            ‖v - heatSemigroup (I := I) (M := M) g (t₀ - t) v‖ :=
      ContinuousLinearMap.le_opNorm _ _
    have h_op_le_one :
        ‖heatSemigroup (I := I) (M := M) g t‖ ≤ 1 :=
      heatSemigroup_opNorm_le_one (I := I) (M := M) g ht
    have h_norm_nn :
        0 ≤ ‖v - heatSemigroup (I := I) (M := M) g (t₀ - t) v‖ := norm_nonneg _
    have h_norm_swap :
        ‖v - heatSemigroup (I := I) (M := M) g (t₀ - t) v‖ =
          ‖heatSemigroup (I := I) (M := M) g (t₀ - t) v - v‖ := by
      rw [norm_sub_rev]
    calc ‖heatSemigroup (I := I) (M := M) g t
              (v - heatSemigroup (I := I) (M := M) g (t₀ - t) v)‖
        ≤ ‖heatSemigroup (I := I) (M := M) g t‖ *
            ‖v - heatSemigroup (I := I) (M := M) g (t₀ - t) v‖ := h_norm_le
      _ ≤ 1 * ‖v - heatSemigroup (I := I) (M := M) g (t₀ - t) v‖ := by
            exact mul_le_mul_of_nonneg_right h_op_le_one h_norm_nn
      _ = ‖heatSemigroup (I := I) (M := M) g (t₀ - t) v - v‖ := by
            rw [one_mul, h_norm_swap]
      _ = ‖heatSemigroup (I := I) (M := M) g |t - t₀| v - v‖ := by rw [h_abs]

/-- Strong continuity of the heat semigroup at every interior nonneg time
`t₀ > 0`. -/
theorem heatSemigroup_continuous_at_pos
    (g : SmoothRiemannianMetric I M) {t₀ : ℝ} (ht₀ : 0 < t₀)
    (v : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) :
    Filter.Tendsto (fun t : ℝ => heatSemigroup (I := I) (M := M) g t v)
        (𝓝 t₀) (𝓝 (heatSemigroup (I := I) (M := M) g t₀ v)) := by
  -- It suffices to show the difference tends to 0.
  rw [show (𝓝 (heatSemigroup (I := I) (M := M) g t₀ v)) =
      𝓝 (0 + heatSemigroup (I := I) (M := M) g t₀ v) by rw [zero_add]]
  have h_diff_to_zero :
      Tendsto (fun t : ℝ =>
          heatSemigroup (I := I) (M := M) g t v -
            heatSemigroup (I := I) (M := M) g t₀ v) (𝓝 t₀) (𝓝 0) := by
    -- Bound: norm ≤ ‖heatSemigroup g |t - t₀| v - v‖.
    have h_pos_nhds : Set.Ioi (0 : ℝ) ∈ 𝓝 t₀ := Ioi_mem_nhds ht₀
    have h_bound_event : ∀ᶠ t : ℝ in 𝓝 t₀,
        ‖heatSemigroup (I := I) (M := M) g t v -
            heatSemigroup (I := I) (M := M) g t₀ v‖ ≤
          ‖heatSemigroup (I := I) (M := M) g |t - t₀| v - v‖ := by
      filter_upwards [h_pos_nhds] with t ht_pos
      exact norm_heatSemigroup_sub_le_heatSemigroup_diff
        (I := I) (M := M) g (le_of_lt ht_pos) ht₀.le v
    -- Bound tends to 0.
    have h_abs_to_zero : Tendsto (fun t : ℝ => |t - t₀|) (𝓝 t₀) (𝓝 0) := by
      have h_sub : Tendsto (fun t : ℝ => t - t₀) (𝓝 t₀) (𝓝 (0 : ℝ)) := by
        have : Tendsto (fun t : ℝ => t - t₀) (𝓝 t₀) (𝓝 (t₀ - t₀)) :=
          Filter.Tendsto.sub tendsto_id tendsto_const_nhds
        simpa using this
      have := h_sub.abs
      simpa using this
    -- |t - t₀| → 0+ in the within filter at 0 from above.
    have h_abs_to_zero_within :
        Tendsto (fun t : ℝ => |t - t₀|) (𝓝 t₀) (𝓝[≥] (0 : ℝ)) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨h_abs_to_zero, ?_⟩
      exact Eventually.of_forall (fun t => Set.mem_Ici.mpr (abs_nonneg _))
    -- Compose with strong continuity at 0+.
    have h_strong :=
      heatSemigroup_continuous_at_zero (I := I) (M := M) g v
    have h_compose :
        Tendsto (fun t : ℝ =>
            heatSemigroup (I := I) (M := M) g |t - t₀| v) (𝓝 t₀) (𝓝 v) :=
      h_strong.comp h_abs_to_zero_within
    have h_diff_to_zero' :
        Tendsto (fun t : ℝ =>
            heatSemigroup (I := I) (M := M) g |t - t₀| v - v)
            (𝓝 t₀) (𝓝 0) := by
      have := h_compose.sub (tendsto_const_nhds (x := v))
      simpa using this
    have h_norm_to_zero :
        Tendsto (fun t : ℝ =>
            ‖heatSemigroup (I := I) (M := M) g |t - t₀| v - v‖)
            (𝓝 t₀) (𝓝 0) := by
      have := h_diff_to_zero'.norm
      simpa using this
    exact squeeze_zero_norm' h_bound_event h_norm_to_zero
  -- Add the constant `heatSemigroup g t₀ v` back.
  have h_added := h_diff_to_zero.add (tendsto_const_nhds
    (x := heatSemigroup (I := I) (M := M) g t₀ v))
  simpa using h_added

/-- `ContinuousOn` packaging on `[0, ∞)`: combine right-continuity at `0`
and two-sided continuity at every `t₀ > 0`. -/
theorem heatSemigroup_continuous_on_nonneg
    (g : SmoothRiemannianMetric I M)
    (v : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) :
    ContinuousOn (fun t : ℝ => heatSemigroup (I := I) (M := M) g t v)
        (Set.Ici (0 : ℝ)) := by
  intro t₀ ht₀
  rcases lt_or_eq_of_le (Set.mem_Ici.mp ht₀) with ht_pos | ht_eq
  · -- Interior point: use the two-sided result.
    have h := heatSemigroup_continuous_at_pos (I := I) (M := M) g ht_pos v
    exact h.mono_left nhdsWithin_le_nhds
  · -- Boundary point t₀ = 0: use right-continuity.
    subst ht_eq
    have h := heatSemigroup_continuous_at_zero (I := I) (M := M) g v
    rw [ContinuousWithinAt]
    have h_zero : heatSemigroup (I := I) (M := M) g 0 v = v := by
      rw [heatSemigroup_zero (I := I) (M := M) g]
      rfl
    rw [h_zero]
    -- 𝓝[Set.Ici 0] 0 = 𝓝[≥] 0.
    exact h

/-! ## Continuity of `s ↦ heatSemigroup g (t - s) (f s)` on `[0, t]`

For continuous `f : ℝ → Lp ℝ 2 μ_g` and `t ≥ 0`, the integrand of the
Duhamel formula is continuous on `[0, t]`. The proof splits the difference

  `‖h_{t-s} (f s) − h_{t-s₀} (f s₀)‖`
  `  ≤ ‖h_{t-s} (f s − f s₀)‖ + ‖(h_{t-s} − h_{t-s₀})(f s₀)‖`
  `  ≤ ‖f s − f s₀‖ + ‖h_{t-s} (f s₀) − h_{t-s₀} (f s₀)‖`

using contractivity for `t − s ≥ 0` and strong continuity of the heat
semigroup at `t − s₀ ≥ 0`. -/

theorem heatSemigroup_apply_f_continuous
    (g : SmoothRiemannianMetric I M)
    {f : ℝ → Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)}
    (hf : Continuous f) (t : ℝ) :
    ContinuousOn
      (fun s : ℝ => heatSemigroup (I := I) (M := M) g (t - s) (f s))
      (Set.Icc 0 t) := by
  intro s₀ hs₀
  have hs₀_le : s₀ ≤ t := hs₀.2
  have h_diff_nn : 0 ≤ t - s₀ := sub_nonneg.mpr hs₀_le
  -- We bound the norm of the difference at s by:
  --   ‖f s - f s₀‖ + ‖heatSemigroup g (t-s) (f s₀) - heatSemigroup g (t-s₀) (f s₀)‖.
  rw [ContinuousWithinAt]
  rw [show (𝓝 (heatSemigroup (I := I) (M := M) g (t - s₀) (f s₀))) =
      𝓝 (0 + heatSemigroup (I := I) (M := M) g (t - s₀) (f s₀)) by rw [zero_add]]
  have h_diff_to_zero :
      Tendsto
        (fun s : ℝ =>
          heatSemigroup (I := I) (M := M) g (t - s) (f s) -
            heatSemigroup (I := I) (M := M) g (t - s₀) (f s₀))
        (𝓝[Set.Icc 0 t] s₀) (𝓝 0) := by
    -- Term A := heatSemigroup g (t - s) (f s) - heatSemigroup g (t - s) (f s₀) → 0.
    have h_termA :
        Tendsto
          (fun s : ℝ =>
            heatSemigroup (I := I) (M := M) g (t - s) (f s) -
              heatSemigroup (I := I) (M := M) g (t - s) (f s₀))
          (𝓝[Set.Icc 0 t] s₀) (𝓝 0) := by
      have h_diff_eq : ∀ s,
          heatSemigroup (I := I) (M := M) g (t - s) (f s) -
            heatSemigroup (I := I) (M := M) g (t - s) (f s₀) =
          heatSemigroup (I := I) (M := M) g (t - s) (f s - f s₀) := by
        intro s
        rw [← (heatSemigroup (I := I) (M := M) g (t - s)).map_sub]
      have h_norm_le_event :
          ∀ᶠ s in 𝓝[Set.Icc 0 t] s₀,
            ‖heatSemigroup (I := I) (M := M) g (t - s) (f s) -
              heatSemigroup (I := I) (M := M) g (t - s) (f s₀)‖ ≤
            ‖f s - f s₀‖ := by
        rw [Filter.eventually_iff_exists_mem]
        refine ⟨Set.Icc 0 t, self_mem_nhdsWithin, ?_⟩
        intro s hs
        rw [h_diff_eq]
        have h_t_minus_s_nn : 0 ≤ t - s := sub_nonneg.mpr hs.2
        have h_op_le :=
          heatSemigroup_opNorm_le_one (I := I) (M := M) g h_t_minus_s_nn
        have h_le := ContinuousLinearMap.le_opNorm
          (heatSemigroup (I := I) (M := M) g (t - s)) (f s - f s₀)
        have h_nn : 0 ≤ ‖f s - f s₀‖ := norm_nonneg _
        calc ‖heatSemigroup (I := I) (M := M) g (t - s) (f s - f s₀)‖
            ≤ ‖heatSemigroup (I := I) (M := M) g (t - s)‖ * ‖f s - f s₀‖ := h_le
          _ ≤ 1 * ‖f s - f s₀‖ := mul_le_mul_of_nonneg_right h_op_le h_nn
          _ = ‖f s - f s₀‖ := one_mul _
      -- Now show ‖f s - f s₀‖ → 0.
      have h_f_to_f₀ : Tendsto f (𝓝[Set.Icc 0 t] s₀) (𝓝 (f s₀)) :=
        (hf.continuousAt.continuousWithinAt : ContinuousWithinAt f (Set.Icc 0 t) s₀)
      have h_f_diff_to_zero :
          Tendsto (fun s : ℝ => f s - f s₀) (𝓝[Set.Icc 0 t] s₀) (𝓝 0) := by
        have := h_f_to_f₀.sub (tendsto_const_nhds (x := f s₀))
        simpa using this
      have h_norm_to_zero :
          Tendsto (fun s : ℝ => ‖f s - f s₀‖) (𝓝[Set.Icc 0 t] s₀) (𝓝 0) := by
        have := h_f_diff_to_zero.norm
        simpa using this
      exact squeeze_zero_norm' h_norm_le_event h_norm_to_zero
    -- Term B := heatSemigroup g (t - s) (f s₀) - heatSemigroup g (t - s₀) (f s₀) → 0.
    have h_termB :
        Tendsto
          (fun s : ℝ =>
            heatSemigroup (I := I) (M := M) g (t - s) (f s₀) -
              heatSemigroup (I := I) (M := M) g (t - s₀) (f s₀))
          (𝓝[Set.Icc 0 t] s₀) (𝓝 0) := by
      -- Use the contractive comparison lemma:
      -- ‖heatSemigroup g (t-s) v - heatSemigroup g (t-s₀) v‖ ≤
      --   ‖heatSemigroup g |(t-s) - (t-s₀)| v - v‖ = ‖heatSemigroup g |s₀ - s| v - v‖.
      have h_norm_le_event :
          ∀ᶠ s in 𝓝[Set.Icc 0 t] s₀,
            ‖heatSemigroup (I := I) (M := M) g (t - s) (f s₀) -
              heatSemigroup (I := I) (M := M) g (t - s₀) (f s₀)‖ ≤
            ‖heatSemigroup (I := I) (M := M) g |s₀ - s| (f s₀) - f s₀‖ := by
        rw [Filter.eventually_iff_exists_mem]
        refine ⟨Set.Icc 0 t, self_mem_nhdsWithin, ?_⟩
        intro s hs
        have h_t_minus_s_nn : 0 ≤ t - s := sub_nonneg.mpr hs.2
        have h := norm_heatSemigroup_sub_le_heatSemigroup_diff
          (I := I) (M := M) g h_t_minus_s_nn h_diff_nn (f s₀)
        have h_abs_eq : |(t - s) - (t - s₀)| = |s₀ - s| := by
          have : (t - s) - (t - s₀) = s₀ - s := by ring
          rw [this]
        rw [h_abs_eq] at h
        exact h
      -- Show ‖heatSemigroup g |s₀ - s| (f s₀) - f s₀‖ → 0 as s → s₀.
      have h_abs_to_zero :
          Tendsto (fun s : ℝ => |s₀ - s|) (𝓝 s₀) (𝓝 0) := by
        have h_sub : Tendsto (fun s : ℝ => s₀ - s) (𝓝 s₀) (𝓝 (0 : ℝ)) := by
          have : Tendsto (fun s : ℝ => s₀ - s) (𝓝 s₀) (𝓝 (s₀ - s₀)) :=
            Filter.Tendsto.sub tendsto_const_nhds tendsto_id
          simpa using this
        have := h_sub.abs
        simpa using this
      have h_abs_to_zero_within :
          Tendsto (fun s : ℝ => |s₀ - s|) (𝓝 s₀) (𝓝[≥] (0 : ℝ)) := by
        rw [tendsto_nhdsWithin_iff]
        refine ⟨h_abs_to_zero, ?_⟩
        exact Eventually.of_forall (fun _ => Set.mem_Ici.mpr (abs_nonneg _))
      have h_strong :=
        heatSemigroup_continuous_at_zero (I := I) (M := M) g (f s₀)
      have h_compose :
          Tendsto (fun s : ℝ =>
              heatSemigroup (I := I) (M := M) g |s₀ - s| (f s₀))
            (𝓝 s₀) (𝓝 (f s₀)) :=
        h_strong.comp h_abs_to_zero_within
      have h_compose_diff :
          Tendsto (fun s : ℝ =>
              heatSemigroup (I := I) (M := M) g |s₀ - s| (f s₀) - f s₀)
            (𝓝 s₀) (𝓝 0) := by
        have := h_compose.sub (tendsto_const_nhds (x := f s₀))
        simpa using this
      have h_norm_to_zero :
          Tendsto (fun s : ℝ =>
              ‖heatSemigroup (I := I) (M := M) g |s₀ - s| (f s₀) - f s₀‖)
            (𝓝 s₀) (𝓝 0) := by
        have := h_compose_diff.norm
        simpa using this
      have h_norm_to_zero_within :
          Tendsto (fun s : ℝ =>
              ‖heatSemigroup (I := I) (M := M) g |s₀ - s| (f s₀) - f s₀‖)
            (𝓝[Set.Icc 0 t] s₀) (𝓝 0) := h_norm_to_zero.mono_left nhdsWithin_le_nhds
      exact squeeze_zero_norm' h_norm_le_event h_norm_to_zero_within
    -- Combine: A + B → 0.
    have h_sum := h_termA.add h_termB
    -- The total difference equals A + B.
    have h_total_eq : ∀ s,
        heatSemigroup (I := I) (M := M) g (t - s) (f s) -
          heatSemigroup (I := I) (M := M) g (t - s₀) (f s₀) =
        (heatSemigroup (I := I) (M := M) g (t - s) (f s) -
            heatSemigroup (I := I) (M := M) g (t - s) (f s₀)) +
        (heatSemigroup (I := I) (M := M) g (t - s) (f s₀) -
            heatSemigroup (I := I) (M := M) g (t - s₀) (f s₀)) := by
      intro s; abel
    have h_eq_fun :
        (fun s : ℝ =>
          heatSemigroup (I := I) (M := M) g (t - s) (f s) -
            heatSemigroup (I := I) (M := M) g (t - s₀) (f s₀)) =
        (fun s : ℝ =>
          (heatSemigroup (I := I) (M := M) g (t - s) (f s) -
              heatSemigroup (I := I) (M := M) g (t - s) (f s₀)) +
          (heatSemigroup (I := I) (M := M) g (t - s) (f s₀) -
              heatSemigroup (I := I) (M := M) g (t - s₀) (f s₀))) := by
      funext s; exact h_total_eq s
    rw [h_eq_fun]
    have := h_sum
    simpa using this
  -- Add back the constant.
  have h_added := h_diff_to_zero.add (tendsto_const_nhds
    (x := heatSemigroup (I := I) (M := M) g (t - s₀) (f s₀)))
  simpa using h_added

/-! ## Definition of the mild solution -/

/-- The Duhamel mild solution of the inhomogeneous heat equation
`∂_t u = Δ_g u + f`, `u(0) = u_0`, on the closed Riemannian manifold
`(M, g)`. -/
noncomputable def mildSolution
    (g : SmoothRiemannianMetric I M)
    (u_0 : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g))
    (f : ℝ → Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g))
    (t : ℝ) :
    Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) :=
  heatSemigroup (I := I) (M := M) g t u_0 +
    ∫ s in (0 : ℝ)..t, heatSemigroup (I := I) (M := M) g (t - s) (f s)

/-! ## Initial condition -/

/-- At `t = 0` the mild solution recovers the initial datum. -/
theorem mildSolution_zero
    (g : SmoothRiemannianMetric I M)
    (u_0 : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g))
    (f : ℝ → Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) :
    mildSolution (I := I) (M := M) g u_0 f 0 = u_0 := by
  unfold mildSolution
  rw [intervalIntegral.integral_same, add_zero]
  rw [heatSemigroup_zero (I := I) (M := M) g]
  rfl

/-! ## Integrability of the integrand on `[0, t]` -/

/-- The integrand `s ↦ heatSemigroup g (t - s) (f s)` is interval-integrable
on `[0, t]` for `t ≥ 0` and continuous `f`. -/
private lemma integrable_heatSemigroup_apply_f
    (g : SmoothRiemannianMetric I M)
    {f : ℝ → Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)}
    (hf : Continuous f) {t : ℝ} (ht : 0 ≤ t) :
    IntervalIntegrable
      (fun s : ℝ => heatSemigroup (I := I) (M := M) g (t - s) (f s))
      MeasureTheory.volume 0 t := by
  have h_cont := heatSemigroup_apply_f_continuous (I := I) (M := M) g hf t
  have h_uIcc : Set.uIcc (0 : ℝ) t = Set.Icc 0 t := Set.uIcc_of_le ht
  rw [← h_uIcc] at h_cont
  exact h_cont.intervalIntegrable

/-! ## Linearity in the data

The mild solution decomposes naturally as the sum of the homogeneous and
inhomogeneous parts: `mildSolution g u_0 f t = mildSolution g u_0 0 t +
mildSolution g 0 f t`. We express the linearity in the initial datum and in
the forcing term using this splitting (the alternative bilinear formulation
requires both arguments to add simultaneously, which is more cumbersome). -/

/-- Linearity of the mild solution in the initial datum: additivity.
The contribution of the additional initial datum `v_0` enters as the
homogeneous part `mildSolution g v_0 0`. -/
theorem mildSolution_add_initial
    (g : SmoothRiemannianMetric I M)
    (u_0 v_0 : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g))
    (f : ℝ → Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g))
    (t : ℝ) :
    mildSolution (I := I) (M := M) g (u_0 + v_0) f t =
      mildSolution (I := I) (M := M) g u_0 f t +
        mildSolution (I := I) (M := M) g v_0 (fun _ => 0) t := by
  unfold mildSolution
  -- Compute integrals: ∫ ... 0 = 0.
  have h_zero_int :
      ∫ s in (0 : ℝ)..t, heatSemigroup (I := I) (M := M) g (t - s) (0 :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) =
      (0 : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) := by
    have h_eq : (fun s : ℝ =>
        heatSemigroup (I := I) (M := M) g (t - s) (0 :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g))) =
        (fun _ : ℝ => (0 : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g))) := by
      funext s
      rw [(heatSemigroup (I := I) (M := M) g (t - s)).map_zero]
    rw [h_eq, intervalIntegral.integral_zero]
  rw [h_zero_int, add_zero]
  -- Heat semigroup splits.
  have h_add : heatSemigroup (I := I) (M := M) g t (u_0 + v_0) =
      heatSemigroup (I := I) (M := M) g t u_0 +
        heatSemigroup (I := I) (M := M) g t v_0 := by
    rw [(heatSemigroup (I := I) (M := M) g t).map_add]
  rw [h_add]
  abel

/-- Linearity of the mild solution in the initial datum: scalar homogeneity.
The forcing-term contribution stays unscaled; only the heat-semigroup part
scales with `c`. -/
theorem mildSolution_smul_initial
    (g : SmoothRiemannianMetric I M)
    (c : ℝ) (u_0 : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g))
    (f : ℝ → Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g))
    (t : ℝ) :
    mildSolution (I := I) (M := M) g (c • u_0) f t =
      c • mildSolution (I := I) (M := M) g u_0 (fun _ => 0) t +
        mildSolution (I := I) (M := M) g 0 f t := by
  unfold mildSolution
  -- Compute c • mildSolution g u_0 0 t = c • heatSemigroup g t u_0 + 0.
  have h_zero_int :
      ∫ s in (0 : ℝ)..t, heatSemigroup (I := I) (M := M) g (t - s) (0 :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) =
      (0 : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) := by
    have h_eq : (fun s : ℝ =>
        heatSemigroup (I := I) (M := M) g (t - s) (0 :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g))) =
        (fun _ : ℝ => (0 : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g))) := by
      funext s
      rw [(heatSemigroup (I := I) (M := M) g (t - s)).map_zero]
    rw [h_eq, intervalIntegral.integral_zero]
  -- Heat-semigroup applied to (0 : Lp) is 0.
  have h_heat_zero : heatSemigroup (I := I) (M := M) g t (0 :
      Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) = 0 := by
    rw [(heatSemigroup (I := I) (M := M) g t).map_zero]
  rw [h_zero_int, add_zero, h_heat_zero, zero_add]
  rw [(heatSemigroup (I := I) (M := M) g t).map_smul]

/-- Linearity of the mild solution in the forcing term: additivity (with the
homogeneous-initial-datum splitting). -/
theorem mildSolution_add_forcing
    (g : SmoothRiemannianMetric I M)
    (u_0 : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g))
    (f h : ℝ → Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g))
    (hf : Continuous f) (hh : Continuous h)
    {t : ℝ} (ht : 0 ≤ t) :
    mildSolution (I := I) (M := M) g u_0 (fun s => f s + h s) t =
      mildSolution (I := I) (M := M) g u_0 f t +
        mildSolution (I := I) (M := M) g 0 h t := by
  unfold mildSolution
  -- heatSemigroup g t 0 = 0.
  have h_heat_zero : heatSemigroup (I := I) (M := M) g t (0 :
      Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) = 0 := by
    rw [(heatSemigroup (I := I) (M := M) g t).map_zero]
  rw [h_heat_zero, zero_add]
  -- The integrand splits.
  have h_split : ∀ s,
      heatSemigroup (I := I) (M := M) g (t - s) (f s + h s) =
        heatSemigroup (I := I) (M := M) g (t - s) (f s) +
          heatSemigroup (I := I) (M := M) g (t - s) (h s) := by
    intro s
    rw [(heatSemigroup (I := I) (M := M) g (t - s)).map_add]
  have h_eq_fun :
      (fun s : ℝ => heatSemigroup (I := I) (M := M) g (t - s) (f s + h s)) =
      (fun s : ℝ =>
        heatSemigroup (I := I) (M := M) g (t - s) (f s) +
          heatSemigroup (I := I) (M := M) g (t - s) (h s)) := by
    funext s; exact h_split s
  rw [h_eq_fun]
  rw [intervalIntegral.integral_add
    (integrable_heatSemigroup_apply_f (I := I) (M := M) g hf ht)
    (integrable_heatSemigroup_apply_f (I := I) (M := M) g hh ht)]
  abel

/-! ## Continuity in `t`

The continuity proof uses a clipped representation of the integrand.
The integrand `(t, s) ↦ heatSemigroup g (t - s) (f s)` is not jointly
continuous on `ℝ × ℝ` (it has a jump along `t = s`, since the heat
semigroup is set to `0` for negative time). However, the clipped variant

  `clippedKernel (t, s) := heatSemigroup g (max 0 (t - s)) (f s)`

is jointly continuous everywhere, and on the relevant domain `s ∈ [0, t]`
with `t ≥ 0` we have `max 0 (t - s) = t - s`, so the two integrands give
the same integral. We then apply Mathlib's parametric interval-integral
continuity result to the clipped form. -/

/-- The clipped kernel: `heatSemigroup g (max 0 (t - s)) (f s)`. Globally
jointly continuous in `(t, s)`, and equal to the Duhamel integrand on
`s ∈ [0, t]` for `t ≥ 0`. -/
private noncomputable def clippedKernel
    (g : SmoothRiemannianMetric I M)
    (f : ℝ → Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g))
    (t s : ℝ) : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) :=
  heatSemigroup (I := I) (M := M) g (max 0 (t - s)) (f s)

/-- Joint continuity of the clipped kernel. -/
private lemma continuous_clippedKernel
    (g : SmoothRiemannianMetric I M)
    {f : ℝ → Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)}
    (hf : Continuous f) :
    Continuous
      (Function.uncurry (clippedKernel (I := I) (M := M) g f)) := by
  -- Continuity at every (t₀, s₀) using the bounded-+-strong-continuity decomposition.
  refine continuous_iff_continuousAt.mpr (fun ⟨t₀, s₀⟩ => ?_)
  -- τ₀ := max 0 (t₀ - s₀) ≥ 0.
  set τ₀ : ℝ := max 0 (t₀ - s₀) with hτ₀_def
  have hτ₀_nn : 0 ≤ τ₀ := le_max_left _ _
  set K : ℝ × ℝ → Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) :=
    Function.uncurry (clippedKernel (I := I) (M := M) g f) with hK_def
  -- Bound for (t, s):
  --   ‖K (t,s) - K (t₀,s₀)‖ ≤ ‖f s - f s₀‖
  --     + ‖h_{τ(t,s)} (f s₀) - h_{τ₀} (f s₀)‖
  -- where τ(t,s) := max 0 (t - s).
  have h_bound : ∀ p : ℝ × ℝ,
      ‖K p - K (t₀, s₀)‖ ≤
        ‖f p.2 - f s₀‖ +
        ‖heatSemigroup (I := I) (M := M) g (max 0 (p.1 - p.2)) (f s₀) -
          heatSemigroup (I := I) (M := M) g τ₀ (f s₀)‖ := by
    rintro ⟨t, s⟩
    have hτ_nn : 0 ≤ max 0 (t - s) := le_max_left _ _
    have h_decomp : K (t, s) - K (t₀, s₀) =
        heatSemigroup (I := I) (M := M) g (max 0 (t - s)) (f s - f s₀) +
        (heatSemigroup (I := I) (M := M) g (max 0 (t - s)) (f s₀) -
          heatSemigroup (I := I) (M := M) g τ₀ (f s₀)) := by
      change heatSemigroup (I := I) (M := M) g (max 0 (t - s)) (f s) -
            heatSemigroup (I := I) (M := M) g τ₀ (f s₀) = _
      rw [(heatSemigroup (I := I) (M := M) g (max 0 (t - s))).map_sub]
      abel
    rw [h_decomp]
    have h_norm_sum :=
      norm_add_le
        (heatSemigroup (I := I) (M := M) g (max 0 (t - s)) (f s - f s₀))
        (heatSemigroup (I := I) (M := M) g (max 0 (t - s)) (f s₀) -
          heatSemigroup (I := I) (M := M) g τ₀ (f s₀))
    have h_first_bound :
        ‖heatSemigroup (I := I) (M := M) g (max 0 (t - s)) (f s - f s₀)‖ ≤
          ‖f s - f s₀‖ := by
      have h_op := heatSemigroup_opNorm_le_one (I := I) (M := M) g hτ_nn
      have h_le := ContinuousLinearMap.le_opNorm
        (heatSemigroup (I := I) (M := M) g (max 0 (t - s))) (f s - f s₀)
      have h_nn : 0 ≤ ‖f s - f s₀‖ := norm_nonneg _
      calc ‖heatSemigroup (I := I) (M := M) g (max 0 (t - s)) (f s - f s₀)‖
          ≤ ‖heatSemigroup (I := I) (M := M) g (max 0 (t - s))‖ *
              ‖f s - f s₀‖ := h_le
        _ ≤ 1 * ‖f s - f s₀‖ := mul_le_mul_of_nonneg_right h_op h_nn
        _ = ‖f s - f s₀‖ := one_mul _
    linarith [h_norm_sum]
  -- RHS → 0.
  have h_rhs_to_zero :
      Tendsto (fun p : ℝ × ℝ =>
          ‖f p.2 - f s₀‖ +
          ‖heatSemigroup (I := I) (M := M) g (max 0 (p.1 - p.2)) (f s₀) -
            heatSemigroup (I := I) (M := M) g τ₀ (f s₀)‖)
        (𝓝 (t₀, s₀)) (𝓝 0) := by
    have h_f_compose :
        Tendsto (fun p : ℝ × ℝ => f p.2) (𝓝 (t₀, s₀)) (𝓝 (f s₀)) :=
      hf.continuousAt.tendsto.comp continuous_snd.continuousAt.tendsto
    have h_term1 :
        Tendsto (fun p : ℝ × ℝ => ‖f p.2 - f s₀‖) (𝓝 (t₀, s₀)) (𝓝 0) := by
      have h_diff : Tendsto (fun p : ℝ × ℝ => f p.2 - f s₀)
          (𝓝 (t₀, s₀)) (𝓝 0) := by
        have := h_f_compose.sub (tendsto_const_nhds (x := f s₀))
        simpa using this
      have := h_diff.norm
      simpa using this
    have h_max_cont : Continuous (fun p : ℝ × ℝ => max 0 (p.1 - p.2)) := by
      have h_sub : Continuous (fun p : ℝ × ℝ => p.1 - p.2) :=
        continuous_fst.sub continuous_snd
      exact continuous_const.max h_sub
    have h_max_to_τ₀ :
        Tendsto (fun p : ℝ × ℝ => max 0 (p.1 - p.2)) (𝓝 (t₀, s₀)) (𝓝 τ₀) :=
      h_max_cont.continuousAt
    have h_max_into_Ici :
        ∀ᶠ p : ℝ × ℝ in 𝓝 (t₀, s₀), max 0 (p.1 - p.2) ∈ Set.Ici (0 : ℝ) :=
      Eventually.of_forall (fun _ => Set.mem_Ici.mpr (le_max_left _ _))
    have h_max_to_τ₀_within :
        Tendsto (fun p : ℝ × ℝ => max 0 (p.1 - p.2))
          (𝓝 (t₀, s₀)) (𝓝[Set.Ici (0 : ℝ)] τ₀) := by
      rw [tendsto_nhdsWithin_iff]
      exact ⟨h_max_to_τ₀, h_max_into_Ici⟩
    have h_strong :=
      heatSemigroup_continuous_on_nonneg (I := I) (M := M) g (f s₀) τ₀
        (Set.mem_Ici.mpr hτ₀_nn)
    have h_compose :
        Tendsto (fun p : ℝ × ℝ =>
            heatSemigroup (I := I) (M := M) g (max 0 (p.1 - p.2)) (f s₀))
          (𝓝 (t₀, s₀))
          (𝓝 (heatSemigroup (I := I) (M := M) g τ₀ (f s₀))) :=
      h_strong.tendsto.comp h_max_to_τ₀_within
    have h_term2 :
        Tendsto (fun p : ℝ × ℝ =>
            ‖heatSemigroup (I := I) (M := M) g (max 0 (p.1 - p.2)) (f s₀) -
              heatSemigroup (I := I) (M := M) g τ₀ (f s₀)‖)
          (𝓝 (t₀, s₀)) (𝓝 0) := by
      have h_diff : Tendsto (fun p : ℝ × ℝ =>
          heatSemigroup (I := I) (M := M) g (max 0 (p.1 - p.2)) (f s₀) -
            heatSemigroup (I := I) (M := M) g τ₀ (f s₀))
          (𝓝 (t₀, s₀)) (𝓝 0) := by
        have := h_compose.sub
          (tendsto_const_nhds (x := heatSemigroup (I := I) (M := M) g τ₀ (f s₀)))
        simpa using this
      have := h_diff.norm
      simpa using this
    have := h_term1.add h_term2
    simpa using this
  -- Squeeze.
  have h_diff_to_zero :
      Tendsto (fun p : ℝ × ℝ => K p - K (t₀, s₀)) (𝓝 (t₀, s₀)) (𝓝 0) :=
    squeeze_zero_norm h_bound h_rhs_to_zero
  have h_target :
      Tendsto K (𝓝 (t₀, s₀)) (𝓝 (K (t₀, s₀))) := by
    have h_added := h_diff_to_zero.add (tendsto_const_nhds (x := K (t₀, s₀)))
    simpa using h_added
  exact h_target

/-- The mild solution is continuous on `[0, ∞)`. -/
theorem mildSolution_continuous
    (g : SmoothRiemannianMetric I M)
    (u_0 : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g))
    {f : ℝ → Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)}
    (hf : Continuous f) :
    ContinuousOn (mildSolution (I := I) (M := M) g u_0 f) (Set.Ici (0 : ℝ)) := by
  -- The first term `heatSemigroup g t u_0` is ContinuousOn `[0, ∞)`.
  have h_first_cont :=
    heatSemigroup_continuous_on_nonneg (I := I) (M := M) g u_0
  -- For the second term, replace the original integrand with the clipped one
  -- on `t ≥ 0`. Then the clipped integrand is jointly continuous, and the
  -- Mathlib parametric interval-integral lemma gives continuity in `t`.
  have h_clip_eq : ∀ t : ℝ, 0 ≤ t →
      mildSolution (I := I) (M := M) g u_0 f t =
        heatSemigroup (I := I) (M := M) g t u_0 +
          ∫ s in (0 : ℝ)..t, clippedKernel (I := I) (M := M) g f t s := by
    intro t ht
    unfold mildSolution
    congr 1
    -- The integrals coincide on [0, t] because t - s ≥ 0 there.
    apply intervalIntegral.integral_congr
    intro s hs
    -- s ∈ Set.uIcc 0 t = Set.Icc 0 t since 0 ≤ t.
    rw [Set.uIcc_of_le ht] at hs
    have h_t_minus_s_nn : 0 ≤ t - s := sub_nonneg.mpr hs.2
    change heatSemigroup (I := I) (M := M) g (t - s) (f s) =
      clippedKernel (I := I) (M := M) g f t s
    unfold clippedKernel
    rw [max_eq_right h_t_minus_s_nn]
  -- Continuity of t ↦ ∫ s in 0..t, clippedKernel g f t s.
  have h_kernel_cont := continuous_clippedKernel (I := I) (M := M) g hf
  have h_int_cont :
      Continuous (fun t : ℝ =>
        ∫ s in (0 : ℝ)..t, clippedKernel (I := I) (M := M) g f t s) := by
    have h := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
      (μ := MeasureTheory.volume) (a₀ := (0 : ℝ))
      (f := clippedKernel (I := I) (M := M) g f) h_kernel_cont
      (s := id) (continuous_id)
    exact h
  intro t₀ ht₀
  have h_t₀_nn : 0 ≤ t₀ := Set.mem_Ici.mp ht₀
  -- Continuity of the clipped form at every t₀.
  have h_clipped_cont : ContinuousWithinAt
      (fun t : ℝ =>
        heatSemigroup (I := I) (M := M) g t u_0 +
          ∫ s in (0 : ℝ)..t, clippedKernel (I := I) (M := M) g f t s)
      (Set.Ici (0 : ℝ)) t₀ := by
    have h1 := h_first_cont t₀ ht₀
    have h2 : ContinuousWithinAt (fun t : ℝ =>
        ∫ s in (0 : ℝ)..t, clippedKernel (I := I) (M := M) g f t s)
        (Set.Ici (0 : ℝ)) t₀ := h_int_cont.continuousWithinAt
    exact h1.add h2
  -- Show the original mildSolution is eventually equal to the clipped form on Ici 0.
  apply h_clipped_cont.congr_of_eventuallyEq
  · -- Eventual equality on `Ici 0`.
    rw [Filter.eventuallyEq_iff_exists_mem]
    refine ⟨Set.Ici (0 : ℝ), self_mem_nhdsWithin, ?_⟩
    intro t ht
    exact h_clip_eq t (Set.mem_Ici.mp ht)
  · -- Equality at `t₀`.
    exact h_clip_eq t₀ h_t₀_nn

/-! ## Homogeneous reduction -/

/-- With `f ≡ 0`, the mild solution reduces to `heatSemigroup g t u_0`. -/
theorem mildSolution_zero_forcing
    (g : SmoothRiemannianMetric I M)
    (u_0 : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g))
    (t : ℝ) :
    mildSolution (I := I) (M := M) g u_0 (fun _ => 0) t =
      heatSemigroup (I := I) (M := M) g t u_0 := by
  unfold mildSolution
  have h_zero_int :
      ∫ s in (0 : ℝ)..t, heatSemigroup (I := I) (M := M) g (t - s) (0 :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) =
      (0 : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) := by
    have h_eq : (fun s : ℝ =>
        heatSemigroup (I := I) (M := M) g (t - s) (0 :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g))) =
        (fun _ : ℝ => (0 : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g))) := by
      funext s
      rw [(heatSemigroup (I := I) (M := M) g (t - s)).map_zero]
    rw [h_eq, intervalIntegral.integral_zero]
  rw [h_zero_int, add_zero]

end HeatEquation
end Analysis
end DifferentialGeometry

end
