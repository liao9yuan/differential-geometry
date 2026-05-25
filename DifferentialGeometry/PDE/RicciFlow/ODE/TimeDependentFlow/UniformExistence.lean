import DifferentialGeometry.PDE.RicciFlow.ODE.TimeDependentFlow.PointwiseLocal
import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary

namespace DifferentialGeometry.PDE.RicciFlow.ODE

open Bundle
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

/--
Per-base-point chart-α-coord neighborhood and flow data, as produced by
`time_dependent_vf_chart_local_picard_with_lipschitz`. Recorded as a single
structure so that the uniform-existence theorem can take per-α data as a
function `M → ChartLocalPicardData` and extract a uniform horizon by a
compactness / finite-subcover argument.

* `T` is the per-α positive time horizon.
* `r` is the per-α positive chart-coord radius around `I ((chartAt H α) α)`.
* `flow` is the chart-coord local flow `E → ℝ → E`; only its values for
  initial points `y` in the closed ball of radius `r` are constrained.
-/
structure ChartLocalPicardData
    (X : ℝ → ∀ x : M, TangentSpace I x) (α : M) where
  /-- Positive time horizon for the chart-α-local flow. -/
  T : ℝ
  T_pos : 0 < T
  /-- Positive chart-coord radius around `I ((chartAt H α) α)`. -/
  r : ℝ
  r_pos : 0 < r
  /-- Chart-α-coord flow `E → ℝ → E`. -/
  flow : E → ℝ → E
  /-- Initial condition and ODE on the closed ball of radius `r` for time
  `[0, T]`. -/
  flow_spec : ∀ y ∈ Metric.closedBall (I ((chartAt H α) α)) r,
    flow y 0 = y ∧
    ∀ t ∈ Set.Icc (0 : ℝ) T,
      HasDerivWithinAt (flow y)
        ((X t ((chartAt H α).symm (I.symm (flow y t)))) : E)
        (Set.Icc (0 : ℝ) T) t

/--
The chart-α-coord open neighborhood associated to `ChartLocalPicardData` for
`X` at `α`: the pull-back of the open ball of radius `data.r` around
`I ((chartAt H α) α)` under the chart map, intersected with the chart
source. By construction, every point `x` in this set has chart image
`(chartAt H α) x` whose model embedding `I _` lies in the open `r`-ball,
hence in the closed `r`-ball used by `flow_spec`.

For convenience this is `open` in `M` (the intersection of an open chart
source with the pre-image of an open set under a continuous restriction)
and contains `α`.
-/
def ChartLocalPicardData.U
    {X : ℝ → ∀ x : M, TangentSpace I x} {α : M}
    (data : ChartLocalPicardData X α) : Set M :=
  (chartAt H α).source ∩
    ((chartAt H α) ⁻¹' (I ⁻¹' Metric.ball (I ((chartAt H α) α)) data.r))

lemma ChartLocalPicardData.isOpen_U
    {X : ℝ → ∀ x : M, TangentSpace I x} {α : M}
    (data : ChartLocalPicardData X α) : IsOpen data.U := by
  -- Open chart source intersected with pre-image of an open set under the
  -- continuous restriction of the chart.
  unfold ChartLocalPicardData.U
  have h₁ : IsOpen (chartAt H α).source := (chartAt H α).open_source
  have h₂ : IsOpen (I ⁻¹' Metric.ball (I ((chartAt H α) α)) data.r) :=
    Metric.isOpen_ball.preimage I.continuous_toFun
  have h₃ : ContinuousOn (chartAt H α) (chartAt H α).source :=
    (chartAt H α).continuousOn
  exact h₃.isOpen_inter_preimage h₁ h₂

lemma ChartLocalPicardData.mem_U_self
    {X : ℝ → ∀ x : M, TangentSpace I x} {α : M}
    (data : ChartLocalPicardData X α) : α ∈ data.U := by
  unfold ChartLocalPicardData.U
  refine ⟨mem_chart_source H α, ?_⟩
  -- `I ((chartAt H α) α) ∈ ball _ data.r` since the centre lies in the open ball.
  exact Metric.mem_ball_self data.r_pos

/--
Uniform existence-time on a closed manifold from per-base-point chart-α-local
Picard data: given chart-α-coord local flows at every base point (with
per-α positive time horizon `Tα` and chart-coord radius `rα`), compactness
of `M` lets us extract a finite cover by the chart-α-coord open
neighborhoods and take the minimum of the horizons. The conclusion is a
single uniform `T > 0`, a finite set `S ⊆ M` of base points whose
chart-α-coord open neighborhoods cover `M`, and per-α chart-α-coord local
flows on `[0, T]` with the right-handed ODE in chart coordinates.

This is the chart-cover form of "uniform existence time": it deliberately
avoids the manifold-flow form (`HasMFDerivWithinAt` on `M`) to side-step
chart-at-`y` convention issues; the downstream `Glue` step assembles a
single global flow from these per-α chart-coord flows via a Grönwall
uniqueness argument in chart coordinates.
-/
theorem time_dependent_vf_uniform_existence_time_on_closed_mfd
    (X : ℝ → ∀ x : M, TangentSpace I x)
    (hper : ∀ α : M, ChartLocalPicardData X α) :
    ∃ T : ℝ, 0 < T ∧
      ∃ S : Finset M, (⋃ α ∈ S, (hper α).U) = (Set.univ : Set M) ∧
        ∃ flow : M → E → ℝ → E,
          ∀ α ∈ S,
            ∀ y ∈ Metric.closedBall (I ((chartAt H α) α)) (hper α).r,
              flow α y 0 = y ∧
              ∀ t ∈ Set.Icc (0 : ℝ) T,
                HasDerivWithinAt (flow α y)
                  ((X t ((chartAt H α).symm (I.symm (flow α y t)))) : E)
                  (Set.Icc (0 : ℝ) T) t := by
  -- Step 1: extract a finite open subcover of `M` by the per-α open
  -- neighborhoods `(hper α).U`.
  have hCompact : IsCompact (Set.univ : Set M) := isCompact_univ
  have hOpenU : ∀ α : M, IsOpen ((hper α).U) := fun α => (hper α).isOpen_U
  have hCover : (Set.univ : Set M) ⊆ ⋃ α : M, (hper α).U := by
    intro x _
    refine Set.mem_iUnion.mpr ⟨x, ?_⟩
    exact (hper x).mem_U_self
  obtain ⟨S, hS⟩ :=
    hCompact.elim_finite_subcover (fun α : M => (hper α).U) hOpenU hCover
  -- `hS : Set.univ ⊆ ⋃ α ∈ S, (hper α).U`; together with `subset_univ` this
  -- gives equality.
  have hCoverEq : (⋃ α ∈ S, (hper α).U) = (Set.univ : Set M) := by
    apply Set.eq_univ_of_univ_subset
    exact hS
  -- Step 2: take a uniform horizon `T = min` of the per-α horizons over `S`.
  -- If `S` is empty, the cover equality forces `M` to be empty, in which
  -- case we use any positive `T` (we pick `T = 1`).
  rcases Finset.eq_empty_or_nonempty S with hSempty | hSnonempty
  · -- Empty case: `M = ∅`, take `T = 1`.
    refine ⟨1, by norm_num, S, hCoverEq, fun _ _ _ => 0, ?_⟩
    -- `α ∈ S` is impossible since `S = ∅`.
    intro α hα
    rw [hSempty] at hα
    exact absurd hα (Finset.notMem_empty α)
  · -- Non-empty case: take `T = min_{α ∈ S} (hper α).T`.
    -- Pick `T` as the minimum of `(hper α).T` over `α ∈ S`, using
    -- `Finset.min'` and positivity.
    let Tmin : ℝ := S.image (fun α : M => (hper α).T) |>.min' (by
      rw [Finset.image_nonempty]; exact hSnonempty)
    have hTmin_pos : 0 < Tmin := by
      -- `Tmin = (hper α₀).T` for some `α₀ ∈ S`; positivity comes from
      -- `(hper α₀).T_pos`.
      have hmem : Tmin ∈ S.image (fun α : M => (hper α).T) :=
        Finset.min'_mem _ _
      rcases Finset.mem_image.mp hmem with ⟨α₀, _, hα₀_eq⟩
      rw [← hα₀_eq]
      exact (hper α₀).T_pos
    have hTmin_le : ∀ α ∈ S, Tmin ≤ (hper α).T := by
      intro α hα
      apply Finset.min'_le
      exact Finset.mem_image.mpr ⟨α, hα, rfl⟩
    -- Construct the per-α flow: for `α ∈ S`, use `(hper α).flow`; otherwise
    -- arbitrary (since the conclusion only quantifies over `α ∈ S`).
    refine ⟨Tmin, hTmin_pos, S, hCoverEq, fun α => (hper α).flow, ?_⟩
    intro α hα y hy
    -- Specialise `(hper α).flow_spec` at `y`.
    obtain ⟨hinit, hflow⟩ := (hper α).flow_spec y hy
    refine ⟨hinit, ?_⟩
    intro t ht
    -- `t ∈ [0, Tmin] ⊆ [0, (hper α).T]`.
    have ht' : t ∈ Set.Icc (0 : ℝ) (hper α).T :=
      ⟨ht.1, ht.2.trans (hTmin_le α hα)⟩
    have hderiv := hflow t ht'
    -- Restrict the derivative-within from `Icc 0 (hper α).T` down to
    -- `Icc 0 Tmin` (since the smaller interval is a subset and `t` lies in
    -- the smaller one).
    have hsub : Set.Icc (0 : ℝ) Tmin ⊆ Set.Icc (0 : ℝ) (hper α).T := by
      intro s hs
      exact ⟨hs.1, hs.2.trans (hTmin_le α hα)⟩
    exact hderiv.mono hsub

end DifferentialGeometry.PDE.RicciFlow.ODE
