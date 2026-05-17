import DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.SemigroupLaw

/-!
# Tensor heat semigroup: time-continuity on `[0, ∞)`

For a closed Riemannian manifold `(M, g)`, ranks `(r, s)`, and a uniform
tensor Sobolev bound `h_atlas`, this file upgrades the right-limit
strong continuity at `0` (`tensorHeatSemigroup_continuous_at_zero`) to a
full strong-continuity statement on the entire half-line `[0, ∞)`, and
shows that the Duhamel-type integrand
`s ↦ tensorHeatSemigroup g r s h_atlas (t - s) (F s)` is continuous
on `[0, t]` whenever the data `F : ℝ → TensorL2 r s g` is continuous.

## Main results

* `tensorHeatSemigroup_continuous_at_pos` — two-sided strong continuity
  at every interior nonneg time `t > 0`, in the form `ContinuousAt`.
* `tensorHeatSemigroup_continuous_on_nonneg` — `ContinuousOn` on
  `[0, ∞)` packaging right-continuity at `0` and two-sided continuity
  at every `t > 0`.
* `tensorHeatSemigroup_apply_F_continuous` — continuity on `[0, t]` of
  the Duhamel integrand `s ↦ e^{(t-s)Δ_∇} (F s)` for any continuous
  data `F`.

## Strategy

All three results are derived from the contractive comparison
`‖e^{tΔ_∇} v − e^{t₀Δ_∇} v‖ ≤ ‖e^{|t − t₀|Δ_∇} v − v‖`, valid for
`t, t₀ ≥ 0`. The bound is obtained from the semigroup law
`tensorHeatSemigroup_add` and the operator-norm contraction
`tensorHeatSemigroup_opNorm_le_one`. Combined with
`tensorHeatSemigroup_continuous_at_zero`, the squeeze theorem yields
strong continuity at every interior nonneg time. The Duhamel-integrand
result splits the difference into a `‖F s − F s₀‖`-term (controlled by
contraction and continuity of `F`) and a semigroup-time-difference term
(controlled by the previous strong-continuity statement).
-/

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorHeatEquation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Geometry

/-! ## File-local Borel-space instances on `E` and `M` -/

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

/-! ## Contractive comparison

For any `t, t₀ ≥ 0`, the difference
`e^{tΔ_∇} v − e^{t₀Δ_∇} v` has norm bounded by
`‖e^{|t − t₀|Δ_∇} v − v‖`. Write the larger of `t, t₀` as the sum of
the smaller and `|t − t₀|`, apply the semigroup law, and use
contractivity. -/

/-- Contractive comparison estimate: for `t, t₀ ≥ 0`,
`‖tensorHeatSemigroup g r s h_atlas t T − tensorHeatSemigroup g r s h_atlas t₀ T‖
  ≤ ‖tensorHeatSemigroup g r s h_atlas |t − t₀| T − T‖`. -/
private lemma norm_tensorHeatSemigroup_sub_le_tensorHeatSemigroup_diff
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (h_atlas : HasLocallyConstantChartAt H M)
    {t t₀ : ℝ} (ht : 0 ≤ t) (ht₀ : 0 ≤ t₀)
    (T : TensorL2 r s g) :
    ‖tensorHeatSemigroup (I := I) (M := M) g r s h_atlas t T -
        tensorHeatSemigroup (I := I) (M := M) g r s h_atlas t₀ T‖ ≤
      ‖tensorHeatSemigroup (I := I) (M := M) g r s h_atlas |t - t₀| T - T‖ := by
  rcases le_or_gt t₀ t with h | h
  · -- Case t ≥ t₀: use t = t₀ + (t - t₀).
    have h_diff_nn : 0 ≤ t - t₀ := sub_nonneg.mpr h
    have h_abs : |t - t₀| = t - t₀ := abs_of_nonneg h_diff_nn
    have h_law :
        tensorHeatSemigroup (I := I) (M := M) g r s h_atlas t =
          (tensorHeatSemigroup (I := I) (M := M) g r s h_atlas t₀).comp
            (tensorHeatSemigroup (I := I) (M := M) g r s h_atlas (t - t₀)) := by
      have h_add :=
        tensorHeatSemigroup_add (I := I) (M := M)
          (g := g) (r := r) (s := s) h_atlas ht₀ h_diff_nn
      have h_eq : t₀ + (t - t₀) = t := by ring
      rw [h_eq] at h_add
      exact h_add
    have h_apply :
        tensorHeatSemigroup (I := I) (M := M) g r s h_atlas t T =
          tensorHeatSemigroup (I := I) (M := M) g r s h_atlas t₀
            (tensorHeatSemigroup
              (I := I) (M := M) g r s h_atlas (t - t₀) T) := by
      rw [h_law]; rfl
    rw [h_apply]
    have h_sub_eq :
        tensorHeatSemigroup (I := I) (M := M) g r s h_atlas t₀
            (tensorHeatSemigroup
              (I := I) (M := M) g r s h_atlas (t - t₀) T) -
          tensorHeatSemigroup (I := I) (M := M) g r s h_atlas t₀ T =
        tensorHeatSemigroup (I := I) (M := M) g r s h_atlas t₀
          (tensorHeatSemigroup
            (I := I) (M := M) g r s h_atlas (t - t₀) T - T) := by
      rw [← (tensorHeatSemigroup
        (I := I) (M := M) g r s h_atlas t₀).map_sub]
    rw [h_sub_eq]
    have h_norm_le :
        ‖tensorHeatSemigroup (I := I) (M := M) g r s h_atlas t₀
            (tensorHeatSemigroup
              (I := I) (M := M) g r s h_atlas (t - t₀) T - T)‖ ≤
          ‖tensorHeatSemigroup (I := I) (M := M) g r s h_atlas t₀‖ *
            ‖tensorHeatSemigroup
              (I := I) (M := M) g r s h_atlas (t - t₀) T - T‖ :=
      ContinuousLinearMap.le_opNorm _ _
    have h_op_le_one :
        ‖tensorHeatSemigroup (I := I) (M := M) g r s h_atlas t₀‖ ≤ 1 :=
      tensorHeatSemigroup_opNorm_le_one (I := I) (M := M) (h_atlas := h_atlas) t₀
    have h_norm_nn :
        0 ≤ ‖tensorHeatSemigroup
            (I := I) (M := M) g r s h_atlas (t - t₀) T - T‖ := norm_nonneg _
    calc ‖tensorHeatSemigroup (I := I) (M := M) g r s h_atlas t₀
              (tensorHeatSemigroup
                (I := I) (M := M) g r s h_atlas (t - t₀) T - T)‖
        ≤ ‖tensorHeatSemigroup (I := I) (M := M) g r s h_atlas t₀‖ *
            ‖tensorHeatSemigroup
              (I := I) (M := M) g r s h_atlas (t - t₀) T - T‖ := h_norm_le
      _ ≤ 1 * ‖tensorHeatSemigroup
              (I := I) (M := M) g r s h_atlas (t - t₀) T - T‖ := by
            exact mul_le_mul_of_nonneg_right h_op_le_one h_norm_nn
      _ = ‖tensorHeatSemigroup
              (I := I) (M := M) g r s h_atlas (t - t₀) T - T‖ := one_mul _
      _ = ‖tensorHeatSemigroup
              (I := I) (M := M) g r s h_atlas |t - t₀| T - T‖ := by rw [h_abs]
  · -- Case t < t₀: symmetric, use t₀ = t + (t₀ - t).
    have h_diff_nn : 0 ≤ t₀ - t := sub_nonneg.mpr h.le
    have h_abs : |t - t₀| = t₀ - t := by
      rw [abs_sub_comm, abs_of_nonneg h_diff_nn]
    have h_law :
        tensorHeatSemigroup (I := I) (M := M) g r s h_atlas t₀ =
          (tensorHeatSemigroup (I := I) (M := M) g r s h_atlas t).comp
            (tensorHeatSemigroup
              (I := I) (M := M) g r s h_atlas (t₀ - t)) := by
      have h_add :=
        tensorHeatSemigroup_add (I := I) (M := M)
          (g := g) (r := r) (s := s) h_atlas ht h_diff_nn
      have h_eq : t + (t₀ - t) = t₀ := by ring
      rw [h_eq] at h_add
      exact h_add
    have h_apply :
        tensorHeatSemigroup (I := I) (M := M) g r s h_atlas t₀ T =
          tensorHeatSemigroup (I := I) (M := M) g r s h_atlas t
            (tensorHeatSemigroup
              (I := I) (M := M) g r s h_atlas (t₀ - t) T) := by
      rw [h_law]; rfl
    rw [h_apply]
    have h_sub_eq :
        tensorHeatSemigroup (I := I) (M := M) g r s h_atlas t T -
          tensorHeatSemigroup (I := I) (M := M) g r s h_atlas t
            (tensorHeatSemigroup
              (I := I) (M := M) g r s h_atlas (t₀ - t) T) =
        tensorHeatSemigroup (I := I) (M := M) g r s h_atlas t
          (T - tensorHeatSemigroup
            (I := I) (M := M) g r s h_atlas (t₀ - t) T) := by
      rw [← (tensorHeatSemigroup
        (I := I) (M := M) g r s h_atlas t).map_sub]
    rw [h_sub_eq]
    have h_norm_le :
        ‖tensorHeatSemigroup (I := I) (M := M) g r s h_atlas t
            (T - tensorHeatSemigroup
              (I := I) (M := M) g r s h_atlas (t₀ - t) T)‖ ≤
          ‖tensorHeatSemigroup (I := I) (M := M) g r s h_atlas t‖ *
            ‖T - tensorHeatSemigroup
              (I := I) (M := M) g r s h_atlas (t₀ - t) T‖ :=
      ContinuousLinearMap.le_opNorm _ _
    have h_op_le_one :
        ‖tensorHeatSemigroup (I := I) (M := M) g r s h_atlas t‖ ≤ 1 :=
      tensorHeatSemigroup_opNorm_le_one (I := I) (M := M) (h_atlas := h_atlas) t
    have h_norm_nn :
        0 ≤ ‖T - tensorHeatSemigroup
            (I := I) (M := M) g r s h_atlas (t₀ - t) T‖ := norm_nonneg _
    have h_norm_swap :
        ‖T - tensorHeatSemigroup
            (I := I) (M := M) g r s h_atlas (t₀ - t) T‖ =
          ‖tensorHeatSemigroup
            (I := I) (M := M) g r s h_atlas (t₀ - t) T - T‖ := by
      rw [norm_sub_rev]
    calc ‖tensorHeatSemigroup (I := I) (M := M) g r s h_atlas t
              (T - tensorHeatSemigroup
                (I := I) (M := M) g r s h_atlas (t₀ - t) T)‖
        ≤ ‖tensorHeatSemigroup (I := I) (M := M) g r s h_atlas t‖ *
            ‖T - tensorHeatSemigroup
              (I := I) (M := M) g r s h_atlas (t₀ - t) T‖ := h_norm_le
      _ ≤ 1 * ‖T - tensorHeatSemigroup
              (I := I) (M := M) g r s h_atlas (t₀ - t) T‖ := by
            exact mul_le_mul_of_nonneg_right h_op_le_one h_norm_nn
      _ = ‖tensorHeatSemigroup
              (I := I) (M := M) g r s h_atlas (t₀ - t) T - T‖ := by
            rw [one_mul, h_norm_swap]
      _ = ‖tensorHeatSemigroup
              (I := I) (M := M) g r s h_atlas |t - t₀| T - T‖ := by rw [h_abs]

/-! ## Two-sided strong continuity at `t > 0` -/

/-- Strong continuity of the tensor heat semigroup at every interior
nonneg time `t > 0`, formulated as `ContinuousAt`. -/
theorem tensorHeatSemigroup_continuous_at_pos
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (h_atlas : HasLocallyConstantChartAt H M)
    {t : ℝ} (ht : 0 < t) (T : TensorL2 r s g) :
    ContinuousAt
      (fun u : ℝ => tensorHeatSemigroup
        (I := I) (M := M) g r s h_atlas u T) t := by
  -- Unfold `ContinuousAt` to `Tendsto`.
  change Filter.Tendsto
      (fun u : ℝ => tensorHeatSemigroup
        (I := I) (M := M) g r s h_atlas u T)
      (𝓝 t)
      (𝓝 (tensorHeatSemigroup (I := I) (M := M) g r s h_atlas t T))
  -- It suffices to show the difference tends to 0.
  rw [show (𝓝 (tensorHeatSemigroup (I := I) (M := M) g r s h_atlas t T)) =
      𝓝 (0 +
        tensorHeatSemigroup (I := I) (M := M) g r s h_atlas t T) by rw [zero_add]]
  have h_diff_to_zero :
      Tendsto (fun u : ℝ =>
          tensorHeatSemigroup (I := I) (M := M) g r s h_atlas u T -
            tensorHeatSemigroup
              (I := I) (M := M) g r s h_atlas t T) (𝓝 t) (𝓝 0) := by
    -- Bound: norm ≤ ‖tensorHeatSemigroup g r s h_atlas |u - t| T - T‖.
    have h_pos_nhds : Set.Ioi (0 : ℝ) ∈ 𝓝 t := Ioi_mem_nhds ht
    have h_bound_event : ∀ᶠ u : ℝ in 𝓝 t,
        ‖tensorHeatSemigroup (I := I) (M := M) g r s h_atlas u T -
            tensorHeatSemigroup
              (I := I) (M := M) g r s h_atlas t T‖ ≤
          ‖tensorHeatSemigroup
            (I := I) (M := M) g r s h_atlas |u - t| T - T‖ := by
      filter_upwards [h_pos_nhds] with u hu_pos
      exact norm_tensorHeatSemigroup_sub_le_tensorHeatSemigroup_diff
        (I := I) (M := M) h_atlas (le_of_lt hu_pos) ht.le T
    -- |u - t| → 0 in the within filter at 0 from above.
    have h_abs_to_zero : Tendsto (fun u : ℝ => |u - t|) (𝓝 t) (𝓝 0) := by
      have h_sub : Tendsto (fun u : ℝ => u - t) (𝓝 t) (𝓝 (0 : ℝ)) := by
        have : Tendsto (fun u : ℝ => u - t) (𝓝 t) (𝓝 (t - t)) :=
          Filter.Tendsto.sub tendsto_id tendsto_const_nhds
        simpa using this
      have := h_sub.abs
      simpa using this
    have h_abs_to_zero_within :
        Tendsto (fun u : ℝ => |u - t|) (𝓝 t) (𝓝[≥] (0 : ℝ)) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨h_abs_to_zero, ?_⟩
      exact Eventually.of_forall (fun _ => Set.mem_Ici.mpr (abs_nonneg _))
    -- Compose with strong continuity at 0+.
    have h_strong :=
      tensorHeatSemigroup_continuous_at_zero (I := I) (M := M) h_atlas T
    have h_compose :
        Tendsto (fun u : ℝ =>
            tensorHeatSemigroup
              (I := I) (M := M) g r s h_atlas |u - t| T) (𝓝 t) (𝓝 T) :=
      h_strong.comp h_abs_to_zero_within
    have h_diff_to_zero' :
        Tendsto (fun u : ℝ =>
            tensorHeatSemigroup
              (I := I) (M := M) g r s h_atlas |u - t| T - T)
            (𝓝 t) (𝓝 0) := by
      have := h_compose.sub (tendsto_const_nhds (x := T))
      simpa using this
    have h_norm_to_zero :
        Tendsto (fun u : ℝ =>
            ‖tensorHeatSemigroup
              (I := I) (M := M) g r s h_atlas |u - t| T - T‖)
            (𝓝 t) (𝓝 0) := by
      have := h_diff_to_zero'.norm
      simpa using this
    exact squeeze_zero_norm' h_bound_event h_norm_to_zero
  -- Add the constant `tensorHeatSemigroup g r s h_atlas t T` back.
  have h_added := h_diff_to_zero.add (tendsto_const_nhds
    (x := tensorHeatSemigroup (I := I) (M := M) g r s h_atlas t T))
  simpa using h_added

/-! ## `ContinuousOn` packaging on `[0, ∞)` -/

/-- Strong continuity of the tensor heat semigroup on `[0, ∞)`: combine
right-continuity at `0` with two-sided continuity at every `t > 0`. -/
theorem tensorHeatSemigroup_continuous_on_nonneg
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (h_atlas : HasLocallyConstantChartAt H M)
    (T : TensorL2 r s g) :
    ContinuousOn
      (fun u : ℝ => tensorHeatSemigroup
        (I := I) (M := M) g r s h_atlas u T)
      (Set.Ici (0 : ℝ)) := by
  intro t ht
  rcases lt_or_eq_of_le (Set.mem_Ici.mp ht) with ht_pos | ht_eq
  · -- Interior point: use the two-sided result.
    have h := tensorHeatSemigroup_continuous_at_pos
      (I := I) (M := M) h_atlas ht_pos T
    exact h.continuousWithinAt
  · -- Boundary point t = 0: use right-continuity.
    subst ht_eq
    have h_zero :
        tensorHeatSemigroup (I := I) (M := M) g r s h_atlas 0 T = T := by
      rw [tensorHeatSemigroup_zero (I := I) (M := M) h_atlas]
      rfl
    rw [ContinuousWithinAt, h_zero]
    -- `𝓝[Set.Ici 0] 0 = 𝓝[≥] 0`, which matches `continuous_at_zero`.
    exact tensorHeatSemigroup_continuous_at_zero
      (I := I) (M := M) h_atlas T

/-! ## Continuity of the Duhamel integrand

For continuous `F : ℝ → TensorL2 r s g` and `t : ℝ`, the integrand
`s ↦ tensorHeatSemigroup g r s h_atlas (t - s) (F s)` is continuous on
`[0, t]`. The proof splits the difference

  `‖e^{(t-s)Δ_∇} (F s) − e^{(t-s₀)Δ_∇} (F s₀)‖`
  `  ≤ ‖e^{(t-s)Δ_∇} (F s − F s₀)‖ + ‖(e^{(t-s)Δ_∇} − e^{(t-s₀)Δ_∇}) (F s₀)‖`
  `  ≤ ‖F s − F s₀‖ + ‖e^{(t-s)Δ_∇} (F s₀) − e^{(t-s₀)Δ_∇} (F s₀)‖`

using contractivity for `t − s ≥ 0` and strong continuity of the heat
semigroup at `t − s₀ ≥ 0`. -/

/-- Continuity of the Duhamel-type integrand
`s ↦ tensorHeatSemigroup g r s h_atlas (t - s) (F s)` on `[0, t]`,
where `F : ℝ → TensorL2 r s g` is continuous. -/
theorem tensorHeatSemigroup_apply_F_continuous
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (h_atlas : HasLocallyConstantChartAt H M)
    {F : ℝ → TensorL2 r s g} (hF : Continuous F) (t : ℝ) :
    ContinuousOn
      (fun u : ℝ =>
        tensorHeatSemigroup (I := I) (M := M) g r s h_atlas (t - u) (F u))
      (Set.Icc 0 t) := by
  intro s₀ hs₀
  have hs₀_le : s₀ ≤ t := hs₀.2
  have h_diff_nn : 0 ≤ t - s₀ := sub_nonneg.mpr hs₀_le
  rw [ContinuousWithinAt]
  rw [show (𝓝 (tensorHeatSemigroup
        (I := I) (M := M) g r s h_atlas (t - s₀) (F s₀))) =
      𝓝 (0 + tensorHeatSemigroup
        (I := I) (M := M) g r s h_atlas (t - s₀) (F s₀)) by rw [zero_add]]
  have h_diff_to_zero :
      Tendsto
        (fun u : ℝ =>
          tensorHeatSemigroup
              (I := I) (M := M) g r s h_atlas (t - u) (F u) -
            tensorHeatSemigroup
              (I := I) (M := M) g r s h_atlas (t - s₀) (F s₀))
        (𝓝[Set.Icc 0 t] s₀) (𝓝 0) := by
    -- Term A := e^{(t-u)Δ_∇} (F u) - e^{(t-u)Δ_∇} (F s₀) → 0.
    have h_termA :
        Tendsto
          (fun u : ℝ =>
            tensorHeatSemigroup
                (I := I) (M := M) g r s h_atlas (t - u) (F u) -
              tensorHeatSemigroup
                (I := I) (M := M) g r s h_atlas (t - u) (F s₀))
          (𝓝[Set.Icc 0 t] s₀) (𝓝 0) := by
      have h_diff_eq : ∀ u,
          tensorHeatSemigroup
              (I := I) (M := M) g r s h_atlas (t - u) (F u) -
            tensorHeatSemigroup
              (I := I) (M := M) g r s h_atlas (t - u) (F s₀) =
          tensorHeatSemigroup
            (I := I) (M := M) g r s h_atlas (t - u) (F u - F s₀) := by
        intro u
        rw [← (tensorHeatSemigroup
          (I := I) (M := M) g r s h_atlas (t - u)).map_sub]
      have h_norm_le_event :
          ∀ᶠ u in 𝓝[Set.Icc 0 t] s₀,
            ‖tensorHeatSemigroup
                (I := I) (M := M) g r s h_atlas (t - u) (F u) -
              tensorHeatSemigroup
                (I := I) (M := M) g r s h_atlas (t - u) (F s₀)‖ ≤
            ‖F u - F s₀‖ := by
        rw [Filter.eventually_iff_exists_mem]
        refine ⟨Set.Icc 0 t, self_mem_nhdsWithin, ?_⟩
        intro u hu
        rw [h_diff_eq]
        have h_t_minus_u_nn : 0 ≤ t - u := sub_nonneg.mpr hu.2
        have h_op_le :=
          tensorHeatSemigroup_opNorm_le_one
            (I := I) (M := M) (g := g) (r := r) (s := s)
            (h_atlas := h_atlas) (t - u)
        have h_le := ContinuousLinearMap.le_opNorm
          (tensorHeatSemigroup
            (I := I) (M := M) g r s h_atlas (t - u)) (F u - F s₀)
        have h_nn : 0 ≤ ‖F u - F s₀‖ := norm_nonneg _
        calc ‖tensorHeatSemigroup
              (I := I) (M := M) g r s h_atlas (t - u) (F u - F s₀)‖
            ≤ ‖tensorHeatSemigroup
                (I := I) (M := M) g r s h_atlas (t - u)‖ *
                ‖F u - F s₀‖ := h_le
          _ ≤ 1 * ‖F u - F s₀‖ := mul_le_mul_of_nonneg_right h_op_le h_nn
          _ = ‖F u - F s₀‖ := one_mul _
      -- Show ‖F u - F s₀‖ → 0.
      have h_F_to_F₀ : Tendsto F (𝓝[Set.Icc 0 t] s₀) (𝓝 (F s₀)) :=
        (hF.continuousAt.continuousWithinAt : ContinuousWithinAt F (Set.Icc 0 t) s₀)
      have h_F_diff_to_zero :
          Tendsto (fun u : ℝ => F u - F s₀) (𝓝[Set.Icc 0 t] s₀) (𝓝 0) := by
        have := h_F_to_F₀.sub (tendsto_const_nhds (x := F s₀))
        simpa using this
      have h_norm_to_zero :
          Tendsto (fun u : ℝ => ‖F u - F s₀‖) (𝓝[Set.Icc 0 t] s₀) (𝓝 0) := by
        have := h_F_diff_to_zero.norm
        simpa using this
      exact squeeze_zero_norm' h_norm_le_event h_norm_to_zero
    -- Term B := e^{(t-u)Δ_∇} (F s₀) - e^{(t-s₀)Δ_∇} (F s₀) → 0.
    have h_termB :
        Tendsto
          (fun u : ℝ =>
            tensorHeatSemigroup
                (I := I) (M := M) g r s h_atlas (t - u) (F s₀) -
              tensorHeatSemigroup
                (I := I) (M := M) g r s h_atlas (t - s₀) (F s₀))
          (𝓝[Set.Icc 0 t] s₀) (𝓝 0) := by
      -- Use the contractive comparison lemma:
      -- ‖e^{(t-u)Δ_∇} v - e^{(t-s₀)Δ_∇} v‖
      --   ≤ ‖e^{|(t-u) - (t-s₀)|Δ_∇} v - v‖
      --   = ‖e^{|s₀ - u|Δ_∇} v - v‖.
      have h_norm_le_event :
          ∀ᶠ u in 𝓝[Set.Icc 0 t] s₀,
            ‖tensorHeatSemigroup
                (I := I) (M := M) g r s h_atlas (t - u) (F s₀) -
              tensorHeatSemigroup
                (I := I) (M := M) g r s h_atlas (t - s₀) (F s₀)‖ ≤
            ‖tensorHeatSemigroup
              (I := I) (M := M) g r s h_atlas |s₀ - u| (F s₀) - F s₀‖ := by
        rw [Filter.eventually_iff_exists_mem]
        refine ⟨Set.Icc 0 t, self_mem_nhdsWithin, ?_⟩
        intro u hu
        have h_t_minus_u_nn : 0 ≤ t - u := sub_nonneg.mpr hu.2
        have h := norm_tensorHeatSemigroup_sub_le_tensorHeatSemigroup_diff
          (I := I) (M := M) h_atlas h_t_minus_u_nn h_diff_nn (F s₀)
        have h_abs_eq : |(t - u) - (t - s₀)| = |s₀ - u| := by
          have : (t - u) - (t - s₀) = s₀ - u := by ring
          rw [this]
        rw [h_abs_eq] at h
        exact h
      -- Show ‖e^{|s₀ - u|Δ_∇} (F s₀) - F s₀‖ → 0 as u → s₀.
      have h_abs_to_zero :
          Tendsto (fun u : ℝ => |s₀ - u|) (𝓝 s₀) (𝓝 0) := by
        have h_sub : Tendsto (fun u : ℝ => s₀ - u) (𝓝 s₀) (𝓝 (0 : ℝ)) := by
          have : Tendsto (fun u : ℝ => s₀ - u) (𝓝 s₀) (𝓝 (s₀ - s₀)) :=
            Filter.Tendsto.sub tendsto_const_nhds tendsto_id
          simpa using this
        have := h_sub.abs
        simpa using this
      have h_abs_to_zero_within :
          Tendsto (fun u : ℝ => |s₀ - u|) (𝓝 s₀) (𝓝[≥] (0 : ℝ)) := by
        rw [tendsto_nhdsWithin_iff]
        refine ⟨h_abs_to_zero, ?_⟩
        exact Eventually.of_forall (fun _ => Set.mem_Ici.mpr (abs_nonneg _))
      have h_strong :=
        tensorHeatSemigroup_continuous_at_zero
          (I := I) (M := M) h_atlas (F s₀)
      have h_compose :
          Tendsto (fun u : ℝ =>
              tensorHeatSemigroup
                (I := I) (M := M) g r s h_atlas |s₀ - u| (F s₀))
            (𝓝 s₀) (𝓝 (F s₀)) :=
        h_strong.comp h_abs_to_zero_within
      have h_compose_diff :
          Tendsto (fun u : ℝ =>
              tensorHeatSemigroup
                (I := I) (M := M) g r s h_atlas |s₀ - u| (F s₀) - F s₀)
            (𝓝 s₀) (𝓝 0) := by
        have := h_compose.sub (tendsto_const_nhds (x := F s₀))
        simpa using this
      have h_norm_to_zero :
          Tendsto (fun u : ℝ =>
              ‖tensorHeatSemigroup
                (I := I) (M := M) g r s h_atlas |s₀ - u| (F s₀) - F s₀‖)
            (𝓝 s₀) (𝓝 0) := by
        have := h_compose_diff.norm
        simpa using this
      have h_norm_to_zero_within :
          Tendsto (fun u : ℝ =>
              ‖tensorHeatSemigroup
                (I := I) (M := M) g r s h_atlas |s₀ - u| (F s₀) - F s₀‖)
            (𝓝[Set.Icc 0 t] s₀) (𝓝 0) :=
        h_norm_to_zero.mono_left nhdsWithin_le_nhds
      exact squeeze_zero_norm' h_norm_le_event h_norm_to_zero_within
    -- Combine: A + B → 0.
    have h_sum := h_termA.add h_termB
    -- The total difference equals A + B.
    have h_total_eq : ∀ u,
        tensorHeatSemigroup
            (I := I) (M := M) g r s h_atlas (t - u) (F u) -
          tensorHeatSemigroup
            (I := I) (M := M) g r s h_atlas (t - s₀) (F s₀) =
        (tensorHeatSemigroup
            (I := I) (M := M) g r s h_atlas (t - u) (F u) -
          tensorHeatSemigroup
            (I := I) (M := M) g r s h_atlas (t - u) (F s₀)) +
        (tensorHeatSemigroup
            (I := I) (M := M) g r s h_atlas (t - u) (F s₀) -
          tensorHeatSemigroup
            (I := I) (M := M) g r s h_atlas (t - s₀) (F s₀)) := by
      intro u; abel
    have h_eq_fun :
        (fun u : ℝ =>
          tensorHeatSemigroup
              (I := I) (M := M) g r s h_atlas (t - u) (F u) -
            tensorHeatSemigroup
              (I := I) (M := M) g r s h_atlas (t - s₀) (F s₀)) =
        (fun u : ℝ =>
          (tensorHeatSemigroup
              (I := I) (M := M) g r s h_atlas (t - u) (F u) -
            tensorHeatSemigroup
              (I := I) (M := M) g r s h_atlas (t - u) (F s₀)) +
          (tensorHeatSemigroup
              (I := I) (M := M) g r s h_atlas (t - u) (F s₀) -
            tensorHeatSemigroup
              (I := I) (M := M) g r s h_atlas (t - s₀) (F s₀))) := by
      funext u; exact h_total_eq u
    rw [h_eq_fun]
    have := h_sum
    simpa using this
  -- Add back the constant.
  have h_added := h_diff_to_zero.add (tendsto_const_nhds
    (x := tensorHeatSemigroup
      (I := I) (M := M) g r s h_atlas (t - s₀) (F s₀)))
  simpa using h_added

end TensorHeatEquation
end Parabolic
end Analysis
end DifferentialGeometry

end

/-! ## Axiom audit -/

section Sanity

#print axioms
  DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorHeatSemigroup_continuous_at_pos

#print axioms
  DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorHeatSemigroup_continuous_on_nonneg

#print axioms
  DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorHeatSemigroup_apply_F_continuous

end Sanity
