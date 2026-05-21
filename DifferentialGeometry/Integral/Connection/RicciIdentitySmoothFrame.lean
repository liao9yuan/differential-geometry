import DifferentialGeometry.Integral.Connection.RicciIdentity
import DifferentialGeometry.Integral.Connection.ChartMetric
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Geometry.Manifold.BumpFunction

/-!
# Smooth orthonormal local frame from the chart frame

This file builds a smooth Gram-Schmidt orthonormalisation of the chart-basis
frame `chartBasisVec g α` from `Integral.Measure.ChartDensity` against the
Riemannian inner product `g.inner`. The output is a smooth tangent-bundle
section family `smoothOrthoFrame g α : Fin n → Π b : M, TangentSpace I b`
whose fibres at `α` are `g`-orthonormal.

## Strategy

The chart-basis vectors `chartBasisVec α i` are `C^∞` only on the
trivialization base set, which equals the chart source `(chartAt H α).source`.
A hand-rolled Gram-Schmidt orthonormalisation against the Riemannian inner
product `g.inner b`, indexed by `Fin (Module.finrank ℝ E)`, produces a fiber
function `chartFrameNormFiber g α b i ∈ T_b M`. To upgrade to a globally
smooth tangent section, we multiply by a smooth bump function
`chartBumpAt α : M → ℝ` whose support is contained in the chart source and
whose value is `1` on a smaller neighbourhood of `α`. The resulting global
section `smoothOrthoFrame g α i` is identically zero off the chart source and
equals the un-bumped Gram-Schmidt frame on the bump-equals-`1` neighbourhood.

The downstream consumer is the heart-of-Bochner trace identity, which feeds
the orthonormal frame into the conditional `heart_of_bochner_of_inner_form`.
The re-packaging is exposed at the end of this file.
-/

noncomputable section

open Bundle Manifold Set FiberBundle NormedSpace Filter
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry
namespace Integral
namespace Connection

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem

/-! ## Stage 1: hand-rolled `g`-Gram-Schmidt of the chart frame, fiberwise

For a fixed point `b : M`, we recursively build the orthonormalised basis
`chartFrameNormFiber g α b i ∈ T_b M`, with `i : Fin (Module.finrank ℝ E)`.

The recursion uses Lean's well-founded recursion on `i.val`: each step
references earlier fiber-values, and termination is by strict decrease of the
index. -/

/-- The normalised Gram-Schmidt vector for the chart frame, in a fixed fiber
`b`.  Defined by well-founded recursion on `i.val`. -/
private noncomputable def chartFrameNormFiber
    (g : SmoothRiemannianMetric I M) (α : M) (b : M)
    (i : Fin (Module.finrank ℝ E)) : TangentSpace I b :=
  -- Aggregate the inner products against all earlier outputs
  -- (indices `< i.val`).
  let v : TangentSpace I b := chartBasisVecFiber (I := I) α i b
  let raw : TangentSpace I b :=
    v - ∑ j : Fin i.val,
      (g.inner b v
          (chartFrameNormFiber g α b
            ⟨j.val, lt_trans j.isLt i.isLt⟩)) •
        chartFrameNormFiber g α b
          ⟨j.val, lt_trans j.isLt i.isLt⟩
  (Real.sqrt (g.inner b raw raw))⁻¹ • raw
termination_by i.val
decreasing_by exact j.isLt

/-- The normalised Gram-Schmidt vector for the chart frame as a section in
`b`: `chartFrameNorm g α i b ∈ T_b M`. -/
noncomputable def chartFrameNorm
    (g : SmoothRiemannianMetric I M) (α : M)
    (i : Fin (Module.finrank ℝ E)) (b : M) : TangentSpace I b :=
  chartFrameNormFiber (I := I) g α b i

/-- The unnormalised Gram-Schmidt vector at index `i`, in a fixed fiber `b`:
$$
  \mathrm{raw}_i(b) := v_i(b) - \sum_{j < i}
      \langle v_i(b), e_j(b)\rangle_g \, e_j(b),
$$
where `v_i(b) = chartBasisVecFiber α i b` and
`e_j(b) = chartFrameNormFiber g α b j`. -/
private noncomputable def chartFrameRawFiber
    (g : SmoothRiemannianMetric I M) (α : M) (b : M)
    (i : Fin (Module.finrank ℝ E)) : TangentSpace I b :=
  chartBasisVecFiber (I := I) α i b -
    ∑ j : Fin i.val,
      (g.inner b (chartBasisVecFiber (I := I) α i b)
          (chartFrameNormFiber (I := I) g α b
            ⟨j.val, lt_trans j.isLt i.isLt⟩)) •
        chartFrameNormFiber (I := I) g α b
          ⟨j.val, lt_trans j.isLt i.isLt⟩

/-- Recursive expansion of `chartFrameNormFiber`: at index `i`, the normalised
vector is `(Real.sqrt (g.inner b raw raw))⁻¹ • raw`. -/
private lemma chartFrameNormFiber_eq
    (g : SmoothRiemannianMetric I M) (α : M) (b : M)
    (i : Fin (Module.finrank ℝ E)) :
    chartFrameNormFiber (I := I) g α b i =
      (Real.sqrt (g.inner b
          (chartFrameRawFiber (I := I) g α b i)
          (chartFrameRawFiber (I := I) g α b i)))⁻¹ •
        chartFrameRawFiber (I := I) g α b i := by
  unfold chartFrameNormFiber chartFrameRawFiber
  rfl

/-- At the zeroth index, the unnormalised Gram-Schmidt vector reduces to the
chart-basis vector itself. -/
private lemma chartFrameRawFiber_at_zero
    (g : SmoothRiemannianMetric I M) (α : M) (b : M) :
    chartFrameRawFiber (I := I) g α b ⟨0, NeZero.pos _⟩ =
      chartBasisVecFiber (I := I) α ⟨0, NeZero.pos _⟩ b := by
  unfold chartFrameRawFiber
  -- The sum is over `Fin 0`, which is empty.
  simp

/-- At the zeroth index, the normalised Gram-Schmidt vector is the
chart-basis vector divided by its `g`-norm. -/
private lemma chartFrameNormFiber_at_zero
    (g : SmoothRiemannianMetric I M) (α : M) (b : M) :
    chartFrameNormFiber (I := I) g α b ⟨0, NeZero.pos _⟩ =
      (Real.sqrt
          (g.inner b
            (chartBasisVecFiber (I := I) α ⟨0, NeZero.pos _⟩ b)
            (chartBasisVecFiber (I := I) α ⟨0, NeZero.pos _⟩ b)))⁻¹ •
        chartBasisVecFiber (I := I) α ⟨0, NeZero.pos _⟩ b := by
  rw [chartFrameNormFiber_eq, chartFrameRawFiber_at_zero]

/-- At a base-set point and at the zeroth index, the normalised Gram-Schmidt
vector is `g`-unit-norm. -/
private lemma chartFrameNormFiber_at_zero_norm
    (g : SmoothRiemannianMetric I M) (α : M) {b : M}
    (hb : b ∈ (trivializationAt E (TangentSpace I) α).baseSet) :
    g.inner b
        (chartFrameNormFiber (I := I) g α b ⟨0, NeZero.pos _⟩)
        (chartFrameNormFiber (I := I) g α b ⟨0, NeZero.pos _⟩) = 1 := by
  classical
  rw [chartFrameNormFiber_at_zero]
  set v : TangentSpace I b :=
    chartBasisVecFiber (I := I) α ⟨0, NeZero.pos _⟩ b with hv_def
  -- The chart frame is linearly independent at `b`, so `v ≠ 0`.
  have hv_ne_zero : v ≠ 0 := by
    have hLI := chartBasisFamily_linearIndependent (I := I) α hb
    -- Linear independence ⇒ each individual vector is nonzero (they form a basis,
    -- so each indexed vector is nonzero).
    intro hv0
    have : (1 : ℝ) • v = 0 := by rw [one_smul]; exact hv0
    -- Use `LinearIndependent.ne_zero` directly.
    have h := hLI.ne_zero (i := ⟨0, NeZero.pos _⟩)
    exact h hv0
  -- `g.inner b v v > 0`.
  have hpos : 0 < g.inner b v v := g.pos b v hv_ne_zero
  set N : ℝ := g.inner b v v with hN_def
  set s : ℝ := Real.sqrt N with hs_def
  have hs_pos : 0 < s := Real.sqrt_pos.mpr hpos
  have hs_ne : s ≠ 0 := ne_of_gt hs_pos
  -- `g.inner b (s⁻¹ • v) (s⁻¹ • v) = (s⁻¹) * (s⁻¹) * g.inner b v v = (s⁻¹)^2 * N`.
  have hexpand :
      g.inner b (s⁻¹ • v) (s⁻¹ • v) = s⁻¹ * (s⁻¹ * N) := by
    -- `g.inner b (s⁻¹ • v) = s⁻¹ • g.inner b v` (by linearity of the outer CLM).
    have h_outer : g.inner b (s⁻¹ • v) = s⁻¹ • g.inner b v := by
      rw [map_smul]
    rw [h_outer]
    -- `(s⁻¹ • g.inner b v) (s⁻¹ • v) = s⁻¹ * g.inner b v (s⁻¹ • v)`.
    rw [ContinuousLinearMap.smul_apply, smul_eq_mul]
    -- `g.inner b v (s⁻¹ • v) = s⁻¹ * g.inner b v v`.
    rw [show g.inner b v (s⁻¹ • v) = s⁻¹ * g.inner b v v from by
      rw [map_smul]; rfl]
  rw [hexpand]
  -- Now `s⁻¹ * (s⁻¹ * N) = s⁻² * N = (sqrt N)⁻² * N`.
  -- We use `Real.sq_sqrt` (i.e., `sqrt N ^ 2 = N` for N ≥ 0).
  have hs_sq : s * s = N := by
    rw [hs_def]; exact Real.mul_self_sqrt (le_of_lt hpos)
  -- Goal: `s⁻¹ * (s⁻¹ * N) = 1`.
  have h1 : s⁻¹ * (s⁻¹ * N) = (s * s)⁻¹ * N := by
    rw [mul_inv]; ring
  rw [h1, hs_sq]
  exact inv_mul_cancel₀ (ne_of_gt hpos)

/-! ## Stage 2: bump-cutoff to produce a global section

The chart-frame normalised Gram-Schmidt is `C^∞` only on the chart source.
To produce a globally smooth tangent-bundle section, we multiply by a smooth
bump function centred at `α` whose support lies inside the chart source. -/

/-- A canonical smooth bump function centred at `α`. It is `1` on a
neighbourhood of `α` and supported in `(chartAt H α).source` (the
trivialization base set at `α`). The existence is guaranteed by
`SmoothBumpFunction.instNonempty`. -/
private noncomputable def chartBumpAt (α : M) : SmoothBumpFunction I α :=
  Classical.arbitrary (SmoothBumpFunction I α)

/-- **Smooth orthonormal frame**. The `i`-th tangent-bundle section of a
smooth `g`-orthonormal local frame attached to the base point `α`. On the
neighbourhood of `α` where the chart bump function `chartBumpAt α` equals `1`,
this section equals the `g`-Gram-Schmidt orthonormalisation of the chart
basis frame. Off the support of the bump (which is contained in the chart
source), the section is zero.

The fiber-by-fiber definition uses the chart bump function multiplied by the
chart-frame normalised Gram-Schmidt step. -/
noncomputable def smoothOrthoFrame
    (g : SmoothRiemannianMetric I M) (α : M)
    (i : Fin (Module.finrank ℝ E)) :
    Π b : M, TangentSpace I b :=
  fun b => (chartBumpAt (I := I) (M := M) α : M → ℝ) b •
    chartFrameNorm (I := I) g α i b

/-! ## Stage 3: the open neighbourhood of `α` on which the frame is
orthonormal -/

/-- The open subset of `M` on which `smoothOrthoFrame g α` is guaranteed to
be a `g`-orthonormal smooth basis: the (open) set where the chart bump
function equals `1`. -/
noncomputable def smoothOrthoFrameNbhd (α : M) : Set M :=
  {b : M | (chartBumpAt (I := I) (M := M) α : M → ℝ) b = 1}

/-- The neighbourhood `smoothOrthoFrameNbhd α` is in the filter `𝓝 α`. -/
lemma smoothOrthoFrameNbhd_mem_nhds (α : M) :
    smoothOrthoFrameNbhd (I := I) (M := M) α ∈ 𝓝 α := by
  classical
  exact (chartBumpAt (I := I) (M := M) α).eventuallyEq_one

/-- The centre `α` belongs to `smoothOrthoFrameNbhd α`. -/
lemma mem_smoothOrthoFrameNbhd_self (α : M) :
    α ∈ smoothOrthoFrameNbhd (I := I) (M := M) α := by
  classical
  change (chartBumpAt (I := I) (M := M) α : M → ℝ) α = 1
  exact (chartBumpAt (I := I) (M := M) α).eq_one

/-- On the neighbourhood `smoothOrthoFrameNbhd α`, the smooth orthonormal
frame agrees with the un-bumped Gram-Schmidt step. -/
lemma smoothOrthoFrame_eq_on_nbhd
    (g : SmoothRiemannianMetric I M) (α : M)
    (i : Fin (Module.finrank ℝ E)) {b : M}
    (hb : b ∈ smoothOrthoFrameNbhd (I := I) (M := M) α) :
    smoothOrthoFrame (I := I) g α i b =
      chartFrameNorm (I := I) g α i b := by
  classical
  unfold smoothOrthoFrame
  have hb1 : (chartBumpAt (I := I) (M := M) α : M → ℝ) b = 1 := hb
  rw [hb1, one_smul]

/-- The neighbourhood `smoothOrthoFrameNbhd α` is contained in the chart
source `(chartAt H α).source` (hence in the trivialization base set at `α`). -/
lemma smoothOrthoFrameNbhd_subset_chartAt_source (α : M) :
    smoothOrthoFrameNbhd (I := I) (M := M) α ⊆ (chartAt H α).source := by
  classical
  intro b hb
  -- `b ∈ smoothOrthoFrameNbhd α` means the bump value at `b` equals `1`. Since the bump's
  -- support is contained in the chart source, `b` is in the chart source.
  have hb1 : (chartBumpAt (I := I) (M := M) α : M → ℝ) b = 1 := hb
  have hsupp : b ∈ Function.support (chartBumpAt (I := I) (M := M) α : M → ℝ) := by
    change (chartBumpAt (I := I) (M := M) α : M → ℝ) b ≠ 0
    rw [hb1]; exact one_ne_zero
  exact (chartBumpAt (I := I) (M := M) α).support_subset_source hsupp

/-- The neighbourhood `smoothOrthoFrameNbhd α` is contained in the
trivialization base set `(trivializationAt E (TangentSpace I) α).baseSet`. -/
lemma smoothOrthoFrameNbhd_subset_baseSet (α : M) :
    smoothOrthoFrameNbhd (I := I) (M := M) α ⊆
      (trivializationAt E (TangentSpace I) α).baseSet := by
  intro b hb
  rw [trivializationAt_baseSet_eq_chartAt_source]
  exact smoothOrthoFrameNbhd_subset_chartAt_source (I := I) (M := M) α hb

/-! ## Stage 3a: orthonormality, smoothness, and basis property of the smooth
orthonormal frame, on the open neighbourhood `smoothOrthoFrameNbhd α ∩ baseSet`

These properties hold at every `b` in the open neighbourhood
`smoothOrthoFrameNbhd α`, by combining the un-bumped Gram-Schmidt frame's
properties with `smoothOrthoFrame_eq_on_nbhd`. Each property is stated with
the hypothesis that the un-bumped Gram-Schmidt frame already satisfies the
corresponding property at `b` (which holds at every `b` in the chart source by
the definition of Gram-Schmidt against a linearly independent input — see
`chartBasisFamily_linearIndependent`).

The hypothesis-bearing form lets the consumer plug in either the Gram-Schmidt
construction's internal proof of orthonormality / linear-independence (when
the construction's recursion is fully unfolded) or an alternative
characterisation (e.g. via the chart Gram matrix). -/

/-- **Smooth orthonormal frame: orthonormality at `b`** (hypothesis-bearing).
Given the orthonormality of the un-bumped Gram-Schmidt frame at `b ∈
smoothOrthoFrameNbhd α`, the smooth orthonormal frame is orthonormal at `b`.

The hypothesis `hOrth` is the orthonormality of `chartFrameNorm g α i b` and
`chartFrameNorm g α j b` at the point `b`, which is automatic by the
Gram-Schmidt construction whenever the input chart frame is linearly
independent at `b` (i.e., `b ∈ baseSet`). -/
theorem smoothOrthoFrame_orthonormal_of_chartFrameNorm
    (g : SmoothRiemannianMetric I M) (α : M)
    {b : M} (hb : b ∈ smoothOrthoFrameNbhd (I := I) (M := M) α)
    (i j : Fin (Module.finrank ℝ E))
    (hOrth : g.inner b
        (chartFrameNorm (I := I) g α i b)
        (chartFrameNorm (I := I) g α j b) = if i = j then 1 else 0) :
    g.inner b
        (smoothOrthoFrame (I := I) g α i b)
        (smoothOrthoFrame (I := I) g α j b) = if i = j then 1 else 0 := by
  rw [smoothOrthoFrame_eq_on_nbhd (I := I) g α i hb,
      smoothOrthoFrame_eq_on_nbhd (I := I) g α j hb]
  exact hOrth

/-- The base case of the orthonormality of `chartFrameNorm`: at index `0` and
at any base-set point `b`, the zeroth Gram-Schmidt vector is `g`-unit-norm. -/
theorem chartFrameNorm_at_zero_norm_one
    (g : SmoothRiemannianMetric I M) (α : M)
    {b : M} (hb : b ∈ (trivializationAt E (TangentSpace I) α).baseSet) :
    g.inner b
        (chartFrameNorm (I := I) g α ⟨0, NeZero.pos _⟩ b)
        (chartFrameNorm (I := I) g α ⟨0, NeZero.pos _⟩ b) = 1 := by
  unfold chartFrameNorm
  exact chartFrameNormFiber_at_zero_norm (I := I) g α hb

/-! ## Chart-equality propagation

If two centres `α₁, α₂ : M` have the same `chartAt H` chart, then the
trivializations on the tangent bundle agree pointwise. Since the chart-frame
Gram-Schmidt construction depends on the chart centre only through its
trivialization, the resulting frames at any base point agree as well. -/

/-- If `chartAt H α₁ = chartAt H α₂`, the `chartBasisVecFiber` values agree
pointwise. -/
theorem chartBasisVecFiber_eq_of_chartAt_eq
    {α₁ α₂ : M} (h : chartAt H α₁ = chartAt H α₂)
    (i : Fin (Module.finrank ℝ E)) (x : M) :
    chartBasisVecFiber (I := I) α₁ i x = chartBasisVecFiber (I := I) α₂ i x := by
  classical
  -- `trivializationAt E (TangentSpace I) α = ...localTriv (achart H α)`,
  -- and `achart H α₁ = achart H α₂` follows from `chartAt H α₁ = chartAt H α₂`.
  unfold chartBasisVecFiber
  have h_triv : trivializationAt E (TangentSpace I) α₁ =
      trivializationAt E (TangentSpace I) α₂ := by
    rw [TangentBundle.trivializationAt_eq_localTriv (I := I) α₁,
        TangentBundle.trivializationAt_eq_localTriv (I := I) α₂]
    congr 1
    apply Subtype.ext
    change (chartAt H α₁ : OpenPartialHomeomorph M H) = (chartAt H α₂ : OpenPartialHomeomorph M H)
    exact h
  rw [h_triv]

/-- Strong induction package: under `chartAt H α₁ = chartAt H α₂`, the raw and
normalised Gram-Schmidt vectors at any base point `b` and any index `i.val ≤ k`
agree between `α = α₁` and `α = α₂`. -/
private theorem chartFrame_eq_of_chartAt_eq_strong
    (g : SmoothRiemannianMetric I M) {α₁ α₂ : M}
    (h : chartAt H α₁ = chartAt H α₂) (b : M) :
    ∀ k : ℕ, ∀ i : Fin (Module.finrank ℝ E), i.val ≤ k →
      chartFrameRawFiber (I := I) g α₁ b i =
        chartFrameRawFiber (I := I) g α₂ b i ∧
      chartFrameNormFiber (I := I) g α₁ b i =
        chartFrameNormFiber (I := I) g α₂ b i := by
  classical
  intro k
  induction k with
  | zero =>
    intro i hi_le
    have hi_val : i.val = 0 := Nat.le_zero.mp hi_le
    have hi_eq : i = ⟨0, NeZero.pos _⟩ := Fin.ext hi_val
    subst hi_eq
    refine ⟨?_, ?_⟩
    · rw [chartFrameRawFiber_at_zero, chartFrameRawFiber_at_zero,
          chartBasisVecFiber_eq_of_chartAt_eq (I := I) (H := H) (M := M) h]
    · rw [chartFrameNormFiber_at_zero, chartFrameNormFiber_at_zero,
          chartBasisVecFiber_eq_of_chartAt_eq (I := I) (H := H) (M := M) h]
  | succ k ih =>
    intro i hi_le
    by_cases hi_lt : i.val ≤ k
    · exact ih i hi_lt
    · have hi_eq : i.val = k + 1 := by omega
      have ih_below : ∀ j : Fin (Module.finrank ℝ E), j.val < i.val →
          chartFrameNormFiber (I := I) g α₁ b j =
            chartFrameNormFiber (I := I) g α₂ b j := by
        intro j hj
        have hj_le : j.val ≤ k := by omega
        exact (ih j hj_le).2
      have h_raw : chartFrameRawFiber (I := I) g α₁ b i =
          chartFrameRawFiber (I := I) g α₂ b i := by
        unfold chartFrameRawFiber
        rw [chartBasisVecFiber_eq_of_chartAt_eq (I := I) (H := H) (M := M) h]
        congr 1
        apply Finset.sum_congr rfl
        intro j' _
        have hlift : (⟨j'.val, lt_trans j'.isLt i.isLt⟩ :
            Fin (Module.finrank ℝ E)).val < i.val := j'.isLt
        rw [ih_below ⟨j'.val, lt_trans j'.isLt i.isLt⟩ hlift]
      refine ⟨h_raw, ?_⟩
      rw [chartFrameNormFiber_eq, chartFrameNormFiber_eq, h_raw]

/-- If `chartAt H α₁ = chartAt H α₂`, then `chartFrameNorm g α₁ i b =
chartFrameNorm g α₂ i b`. -/
theorem chartFrameNorm_eq_of_chartAt_eq
    (g : SmoothRiemannianMetric I M) {α₁ α₂ : M}
    (h : chartAt H α₁ = chartAt H α₂)
    (i : Fin (Module.finrank ℝ E)) (b : M) :
    chartFrameNorm (I := I) g α₁ i b = chartFrameNorm (I := I) g α₂ i b := by
  classical
  unfold chartFrameNorm
  exact (chartFrame_eq_of_chartAt_eq_strong (I := I) g h b i.val i (le_refl _)).2

/-! ## Stage 3b: inductive orthonormality of the un-bumped Gram-Schmidt frame

The inductive Gram-Schmidt step preserves orthogonality and unit length on
`baseSet`. The proof goes by strong induction on the index `i`, using the
linear independence of the chart frame at base-set points to show that the
"raw" Gram-Schmidt vector `chartFrameRawFiber g α b i` is non-zero (and hence
its `g`-norm is positive).

The key intermediate step is the "span identity": the span of
`{e_0(b), …, e_i(b)}` equals the span of `{v_0(b), …, v_i(b)}`, where `v_k =
chartBasisVecFiber α k` and `e_k = chartFrameNormFiber g α b k`. -/

/-- A bilinear-distribution lemma: the inner product of a vector against a
finite sum equals the sum of the inner products. -/
private lemma g_inner_sum_right
    (g : SmoothRiemannianMetric I M) (b : M)
    (v : TangentSpace I b)
    {ι : Type*} (s : Finset ι) (w : ι → TangentSpace I b)
    (c : ι → ℝ) :
    g.inner b v (∑ k ∈ s, c k • w k) = ∑ k ∈ s, c k * g.inner b v (w k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s has ih =>
    rw [Finset.sum_insert has, Finset.sum_insert has]
    rw [show ((g.inner b) v) (c a • w a + ∑ x ∈ s, c x • w x) =
        ((g.inner b) v) (c a • w a) + ((g.inner b) v) (∑ x ∈ s, c x • w x) from by
      rw [map_add]]
    rw [show ((g.inner b) v) (c a • w a) = c a * ((g.inner b) v) (w a) from by
      rw [map_smul]; rfl]
    rw [ih]

/-- A bilinear-distribution lemma in the left slot. -/
private lemma g_inner_sum_left
    (g : SmoothRiemannianMetric I M) (b : M)
    {ι : Type*} (s : Finset ι) (v : ι → TangentSpace I b)
    (c : ι → ℝ) (w : TangentSpace I b) :
    g.inner b (∑ k ∈ s, c k • v k) w = ∑ k ∈ s, c k * g.inner b (v k) w := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s has ih =>
    rw [Finset.sum_insert has, Finset.sum_insert has]
    rw [show ((g.inner b) (c a • v a + ∑ x ∈ s, c x • v x)) =
        ((g.inner b) (c a • v a)) + ((g.inner b) (∑ x ∈ s, c x • v x)) from by
      rw [map_add]]
    rw [ContinuousLinearMap.add_apply]
    rw [show ((g.inner b) (c a • v a)) w = c a * ((g.inner b) (v a)) w from by
      rw [map_smul]; rfl]
    rw [ih]

set_option maxHeartbeats 4000000 in
/-- The strong-induction package for the orthonormality of `chartFrameNormFiber`.
The conclusion bundles three facts at every `i ≤ k`:

1. `chartFrameRawFiber g α b i ≠ 0`;
2. for all `j < i`, `g.inner b (chartFrameNormFiber g α b j)
                              (chartFrameNormFiber g α b i) = 0`;
3. `g.inner b (chartFrameNormFiber g α b i) (chartFrameNormFiber g α b i) = 1`.

We package them together to thread the strong-induction hypothesis cleanly. -/
private theorem chartFrameNormFiber_orth_strong_aux
    (g : SmoothRiemannianMetric I M) (α : M) {b : M}
    (hb : b ∈ (trivializationAt E (TangentSpace I) α).baseSet) :
    ∀ k : ℕ, ∀ i : Fin (Module.finrank ℝ E), i.val ≤ k →
      chartFrameRawFiber (I := I) g α b i ≠ 0 ∧
      (∀ j : Fin (Module.finrank ℝ E), j.val < i.val →
        g.inner b
            (chartFrameNormFiber (I := I) g α b j)
            (chartFrameNormFiber (I := I) g α b i) = 0) ∧
      g.inner b
          (chartFrameNormFiber (I := I) g α b i)
          (chartFrameNormFiber (I := I) g α b i) = 1 := by
  classical
  -- The chart-basis family is linearly independent at `b`; record once.
  have hLI : LinearIndependent ℝ
      (fun i : Fin (Module.finrank ℝ E) =>
        chartBasisVecFiber (I := I) α i b) :=
    chartBasisFamily_linearIndependent (I := I) α hb
  -- Strong induction on `k`, with the bound `i.val ≤ k`.
  intro k
  induction k with
  | zero =>
    intro i hi_le
    -- `i.val ≤ 0` ⇒ `i.val = 0`.
    have hi_val : i.val = 0 := Nat.le_zero.mp hi_le
    have hi_eq : i = ⟨0, NeZero.pos _⟩ := by
      apply Fin.ext
      exact hi_val
    subst hi_eq
    refine ⟨?_, ?_, ?_⟩
    · -- raw_0 = v_0 ≠ 0 (because v_0 is part of a linearly independent family)
      rw [chartFrameRawFiber_at_zero]
      exact hLI.ne_zero ⟨0, NeZero.pos _⟩
    · intro j hj
      simp at hj
    · exact chartFrameNormFiber_at_zero_norm (I := I) g α hb
  | succ k ih =>
    intro i hi_le
    by_cases hi_lt : i.val ≤ k
    · -- i.val ≤ k: apply IH directly
      exact ih i hi_lt
    · -- i.val = k + 1
      have hi_eq : i.val = k + 1 := by omega
      -- For every `j < i.val`, `j.val ≤ k`, so we have the IH at `j`.
      -- Establish basic IH access at all earlier indices.
      have ih_below : ∀ j : Fin (Module.finrank ℝ E), j.val < i.val →
          chartFrameRawFiber (I := I) g α b j ≠ 0 ∧
          (∀ j' : Fin (Module.finrank ℝ E), j'.val < j.val →
            g.inner b
                (chartFrameNormFiber (I := I) g α b j')
                (chartFrameNormFiber (I := I) g α b j) = 0) ∧
          g.inner b
              (chartFrameNormFiber (I := I) g α b j)
              (chartFrameNormFiber (I := I) g α b j) = 1 := by
        intro j hj
        have hj_le : j.val ≤ k := by omega
        exact ih j hj_le
      -- Step 1: orthogonality of raw_i to each e_j with j.val < i.val.
      -- `raw_i = v_i - ∑_{m < i.val} ⟨v_i, e_m⟩ • e_m`.
      -- We compute `⟨e_j, raw_i⟩` for `j.val < i.val`:
      -- `⟨e_j, raw_i⟩ = ⟨e_j, v_i⟩ - ∑_{m < i.val} ⟨v_i, e_m⟩ * ⟨e_j, e_m⟩
      --              = ⟨e_j, v_i⟩ - ⟨v_i, e_j⟩ (only m = j survives)
      --              = ⟨e_j, v_i⟩ - ⟨e_j, v_i⟩ (by symmetry of g.inner)
      --              = 0
      have horth_raw : ∀ j : Fin (Module.finrank ℝ E), j.val < i.val →
          g.inner b
              (chartFrameNormFiber (I := I) g α b j)
              (chartFrameRawFiber (I := I) g α b i) = 0 := by
        intro j hj_lt
        -- We expand `g.inner b e_j raw_i` step by step.
        rw [show chartFrameRawFiber (I := I) g α b i =
            chartBasisVecFiber (I := I) α i b -
              ∑ j' : Fin i.val,
                (g.inner b (chartBasisVecFiber (I := I) α i b)
                    (chartFrameNormFiber (I := I) g α b
                      ⟨j'.val, lt_trans j'.isLt i.isLt⟩)) •
                  chartFrameNormFiber (I := I) g α b
                    ⟨j'.val, lt_trans j'.isLt i.isLt⟩ from rfl]
        -- Apply the bilinear-form's linearity to the subtraction.
        rw [show ((g.inner b) (chartFrameNormFiber (I := I) g α b j))
              (chartBasisVecFiber (I := I) α i b -
                ∑ j' : Fin i.val,
                  (g.inner b (chartBasisVecFiber (I := I) α i b)
                      (chartFrameNormFiber (I := I) g α b
                        ⟨j'.val, lt_trans j'.isLt i.isLt⟩)) •
                    chartFrameNormFiber (I := I) g α b
                      ⟨j'.val, lt_trans j'.isLt i.isLt⟩) =
            ((g.inner b) (chartFrameNormFiber (I := I) g α b j))
              (chartBasisVecFiber (I := I) α i b) -
            ((g.inner b) (chartFrameNormFiber (I := I) g α b j))
              (∑ j' : Fin i.val,
                (g.inner b (chartBasisVecFiber (I := I) α i b)
                    (chartFrameNormFiber (I := I) g α b
                      ⟨j'.val, lt_trans j'.isLt i.isLt⟩)) •
                  chartFrameNormFiber (I := I) g α b
                    ⟨j'.val, lt_trans j'.isLt i.isLt⟩) from by
          rw [map_sub]]
        -- Distribute over the sum.
        rw [g_inner_sum_right (I := I) g b
            (chartFrameNormFiber (I := I) g α b j)
            (Finset.univ : Finset (Fin i.val))
            (fun j' => chartFrameNormFiber (I := I) g α b
              ⟨j'.val, lt_trans j'.isLt i.isLt⟩)
            (fun j' => g.inner b
              (chartBasisVecFiber (I := I) α i b)
              (chartFrameNormFiber (I := I) g α b
                ⟨j'.val, lt_trans j'.isLt i.isLt⟩))]
        -- We now compute the sum: only the `j' = j` term survives.
        -- For `j' ≠ ⟨j.val, hj_lt⟩` (i.e. j'.val ≠ j.val), the inner product
        -- `⟨e_j, e_⟨j'.val,_⟩⟩` is zero by IH (orthogonality of distinct e's).
        -- For `j' = ⟨j.val, hj_lt⟩`, the term equals
        --   `⟨v_i, e_j⟩ * ⟨e_j, e_j⟩ = ⟨v_i, e_j⟩ * 1 = ⟨v_i, e_j⟩
        --   = ⟨e_j, v_i⟩ (by g.symm)`.
        -- So the sum equals `⟨e_j, v_i⟩`, and the goal becomes `⟨e_j, v_i⟩ - ⟨e_j, v_i⟩ = 0`.
        have hsum_eq :
            ∑ j' ∈ (Finset.univ : Finset (Fin i.val)),
                g.inner b
                    (chartBasisVecFiber (I := I) α i b)
                    (chartFrameNormFiber (I := I) g α b
                      ⟨j'.val, lt_trans j'.isLt i.isLt⟩) *
                  g.inner b
                    (chartFrameNormFiber (I := I) g α b j)
                    (chartFrameNormFiber (I := I) g α b
                      ⟨j'.val, lt_trans j'.isLt i.isLt⟩) =
              g.inner b
                (chartFrameNormFiber (I := I) g α b j)
                (chartBasisVecFiber (I := I) α i b) := by
          -- Pick out the unique term j' with j'.val = j.val.
          have hj_in_fin : j.val < i.val := hj_lt
          set j_inFin : Fin i.val := ⟨j.val, hj_in_fin⟩
          have hsingleton :
              ∑ j' ∈ (Finset.univ : Finset (Fin i.val)),
                  g.inner b
                      (chartBasisVecFiber (I := I) α i b)
                      (chartFrameNormFiber (I := I) g α b
                        ⟨j'.val, lt_trans j'.isLt i.isLt⟩) *
                    g.inner b
                      (chartFrameNormFiber (I := I) g α b j)
                      (chartFrameNormFiber (I := I) g α b
                        ⟨j'.val, lt_trans j'.isLt i.isLt⟩) =
                g.inner b
                    (chartBasisVecFiber (I := I) α i b)
                    (chartFrameNormFiber (I := I) g α b
                      ⟨j_inFin.val, lt_trans j_inFin.isLt i.isLt⟩) *
                  g.inner b
                    (chartFrameNormFiber (I := I) g α b j)
                    (chartFrameNormFiber (I := I) g α b
                      ⟨j_inFin.val, lt_trans j_inFin.isLt i.isLt⟩) := by
            rw [Finset.sum_eq_single j_inFin]
            · intro j' _ hj'
              -- For j' ≠ j_inFin, j'.val ≠ j.val.
              have hj'_neq : j'.val ≠ j.val := fun h => hj' (Fin.ext h)
              -- `⟨e_j, e_⟨j'.val,_⟩⟩ = 0` by IH symmetry.
              -- We have to use the IH at the *larger* index (between j.val and j'.val).
              by_cases hcompare : j'.val < j.val
              · -- j'.val < j.val, so use IH at index j (which has j.val ≤ k).
                have hIH_j := ih_below j hj_lt
                have hzero := hIH_j.2.1 ⟨j'.val, lt_trans hcompare j.isLt⟩ hcompare
                rw [show (g.inner b
                    (chartFrameNormFiber (I := I) g α b j)
                    (chartFrameNormFiber (I := I) g α b
                      ⟨j'.val, lt_trans j'.isLt i.isLt⟩)) =
                  g.inner b
                    (chartFrameNormFiber (I := I) g α b
                      ⟨j'.val, lt_trans hcompare j.isLt⟩)
                    (chartFrameNormFiber (I := I) g α b j) from by
                  rw [g.symm]]
                rw [hzero, mul_zero]
              · -- j.val < j'.val (since j'.val ≠ j.val).
                have hcompare_le : j.val ≤ j'.val := Nat.le_of_not_lt hcompare
                have hcompare' : j.val < j'.val := lt_of_le_of_ne hcompare_le hj'_neq.symm
                -- Use IH at index ⟨j'.val, _⟩ (which has j'.val ≤ k).
                have hj'_in : (⟨j'.val, lt_trans j'.isLt i.isLt⟩ :
                  Fin (Module.finrank ℝ E)).val < i.val := j'.isLt
                have hIH_j' := ih_below ⟨j'.val, lt_trans j'.isLt i.isLt⟩ hj'_in
                have hzero := hIH_j'.2.1 j hcompare'
                rw [hzero, mul_zero]
            · intro h
              exact absurd (Finset.mem_univ j_inFin) h
          rw [hsingleton]
          -- Now use the IH at j: `⟨e_j, e_j⟩ = 1`.
          have hIH_j := ih_below j hj_lt
          have hjj_unit : g.inner b
              (chartFrameNormFiber (I := I) g α b j)
              (chartFrameNormFiber (I := I) g α b j) = 1 := hIH_j.2.2
          -- Note that j_inFin.val = j.val, so `chartFrameNormFiber g α b ⟨j_inFin.val, _⟩` =
          -- `chartFrameNormFiber g α b j` (definitional equality after `Fin.ext`).
          have hj_eq : (⟨j_inFin.val, lt_trans j_inFin.isLt i.isLt⟩ :
              Fin (Module.finrank ℝ E)) = j := by
            apply Fin.ext
            rfl
          rw [hj_eq, hjj_unit, mul_one, g.symm]
        rw [hsum_eq]
        -- Goal: `g.inner b e_j v_i - g.inner b e_j v_i = 0`. Wait, we had distributed.
        -- After distribution, LHS is
        --   `g.inner b e_j v_i - ∑ ... = g.inner b e_j v_i - g.inner b e_j v_i = 0`.
        -- We just need to confirm the sign. Let's verify:
        -- After distribution, our goal is: `(g.inner b e_j v_i) - (∑ ...) = 0`.
        -- And `hsum_eq` gives us that the sum equals `g.inner b e_j v_i`.
        -- So LHS = `g.inner b e_j v_i - g.inner b e_j v_i = 0`. Good.
        ring
      -- Step 2: `chartFrameRawFiber g α b i ≠ 0`.
      -- Argument: `raw_i = v_i - π` where `π` is in `span(e_0,...,e_{i-1})`.
      -- If raw_i = 0, then `v_i = π ∈ span(e_0,...,e_{i-1})`. By the span identity
      -- (e_j's span the same as v_0,...,v_{j-1}+v_j by induction), π is in
      -- `span(v_0,...,v_{i-1})`. So `v_i ∈ span(v_0,...,v_{i-1})`, contradicting
      -- linear independence of `chartBasisFamily`.
      --
      -- We prove this by contradiction.
      have hraw_ne : chartFrameRawFiber (I := I) g α b i ≠ 0 := by
        intro hraw_zero
        -- raw_i = 0, so v_i = ∑_{j<i.val} ⟨v_i, e_j⟩ • e_j.
        have hv_eq : chartBasisVecFiber (I := I) α i b =
            ∑ j' : Fin i.val,
              (g.inner b (chartBasisVecFiber (I := I) α i b)
                (chartFrameNormFiber (I := I) g α b
                  ⟨j'.val, lt_trans j'.isLt i.isLt⟩)) •
                chartFrameNormFiber (I := I) g α b
                  ⟨j'.val, lt_trans j'.isLt i.isLt⟩ := by
          have h_eq : chartBasisVecFiber (I := I) α i b -
              ∑ j' : Fin i.val,
                (g.inner b (chartBasisVecFiber (I := I) α i b)
                    (chartFrameNormFiber (I := I) g α b
                      ⟨j'.val, lt_trans j'.isLt i.isLt⟩)) •
                  chartFrameNormFiber (I := I) g α b
                    ⟨j'.val, lt_trans j'.isLt i.isLt⟩ = 0 := by
            simpa [chartFrameRawFiber] using hraw_zero
          exact sub_eq_zero.mp h_eq
        -- Now compute `⟨e_j, v_i⟩` two ways for some `j < i.val`. Actually a
        -- cleaner contradiction: take `⟨v_i, v_i⟩ > 0` (since v_i ≠ 0) and
        -- compute the inner product against the sum representation. We just
        -- show v_i is in span(e_0,...,e_{i-1}), then construct an explicit
        -- linear dependency among v_0,...,v_i.
        --
        -- Each e_j is itself a linear combination of v_0,...,v_j (by the
        -- recursive definition), with coefficient on v_j being
        -- `1/sqrt(g.inner b raw_j raw_j) ≠ 0`.
        -- So v_i ∈ span(e_0,...,e_{i-1}) ⊆ span(v_0,...,v_{i-1}).
        -- This contradicts linear independence.
        -- We build the span chain by a separate auxiliary; here we use a
        -- direct linear algebra argument via induction on j.
        --
        -- Below: we use the `LinearIndependent.linearCombination_ne` lemma
        -- — actually, more directly, we extract a linear dependency.
        --
        -- Define a linear combination explicitly. For each `m : Fin (Module.finrank ℝ E)`,
        -- set `c m := if m = i then -1 else (coefficient of v_m in the sum
        --   representation of v_i, after expanding each e_j)`.
        -- Then `∑_m c_m • v_m = 0`, and `c i = -1 ≠ 0`, contradicting LI.
        --
        -- Building this constructive linear combination is straightforward but
        -- requires recursive bookkeeping. We prove it via the `mem_span` API.
        --
        -- For tractability, we take a different approach: use that the e_j
        -- inductively lie in `span(v_0, …, v_j)`, hence
        -- `v_i ∈ span(e_0,…,e_{i-1}) ⊆ span(v_0,…,v_{i-1}) =: U`. Then
        -- `v_i ∉ U` by linear independence (this is Mathlib's
        -- `LinearIndependent.notMem_span_image`).
        --
        -- The recursive span chain: `e_j ∈ span(v_0,…,v_j)` is the inductive
        -- consequence of the Gram-Schmidt formula plus the IH that
        -- `e_0,…,e_{j-1} ∈ span(v_0,…,v_{j-1})`.
        have h_e_in_span_v : ∀ k : ℕ, ∀ m : Fin (Module.finrank ℝ E),
            m.val ≤ k → m.val < i.val →
            chartFrameNormFiber (I := I) g α b m ∈
              Submodule.span ℝ
                ((fun n : Fin i.val =>
                  chartBasisVecFiber (I := I) α
                    ⟨n.val, lt_trans n.isLt i.isLt⟩ b) ''
                  Set.univ) := by
          intro kk
          induction kk with
          | zero =>
            intro m hm_le hm_lt
            have hm_val : m.val = 0 := Nat.le_zero.mp hm_le
            have hm_eq : m = ⟨0, NeZero.pos _⟩ := by
              apply Fin.ext
              exact hm_val
            subst hm_eq
            -- e_0 = (1/sqrt(...)) • v_0, and v_0 is in the span.
            rw [chartFrameNormFiber_at_zero]
            -- The span contains v_0. We need 0 < i.val to construct a
            -- `Fin i.val` index for v_0.
            have h0_in_fin : (0 : ℕ) < i.val := hm_lt
            apply Submodule.smul_mem
            apply Submodule.subset_span
            refine ⟨⟨0, h0_in_fin⟩, ?_, rfl⟩
            exact Set.mem_univ _
          | succ kk ih_kk =>
            intro m hm_le hm_lt
            by_cases hcase : m.val ≤ kk
            · exact ih_kk m hcase hm_lt
            · -- m.val = kk + 1
              have hm_eq : m.val = kk + 1 := by omega
              -- e_m = (1/sqrt(...)) • raw_m, where raw_m = v_m - ∑_{j<m.val} ⟨v_m, e_j⟩ • e_j.
              -- Each e_j (j<m.val) is in span by IH; v_m is in span; so e_m is in span.
              rw [chartFrameNormFiber_eq]
              apply Submodule.smul_mem
              -- raw_m = v_m - ∑_{j<m.val} ⟨v_m, e_j⟩ • e_j.
              unfold chartFrameRawFiber
              apply Submodule.sub_mem
              · -- v_m is in the span.
                apply Submodule.subset_span
                refine ⟨⟨m.val, hm_lt⟩, ?_, ?_⟩
                · exact Set.mem_univ _
                · rfl
              · -- The sum: each term is a scalar multiple of `e_⟨j.val,_⟩`,
                -- and `e_⟨j.val,_⟩` is in the span by IH.
                apply Submodule.sum_mem
                intro j _
                apply Submodule.smul_mem
                have hj_in_fin : j.val < i.val := lt_trans j.isLt hm_lt
                have hj_le_kk : j.val ≤ kk := by
                  have : j.val < m.val := j.isLt
                  omega
                have hj_lt_total : j.val < Module.finrank ℝ E :=
                  lt_trans hj_in_fin i.isLt
                exact ih_kk ⟨j.val, hj_lt_total⟩ hj_le_kk hj_in_fin
        -- Now show v_i is in the span of v_0,...,v_{i-1}.
        have hvi_in_span : chartBasisVecFiber (I := I) α i b ∈
            Submodule.span ℝ
              ((fun n : Fin i.val =>
                chartBasisVecFiber (I := I) α
                  ⟨n.val, lt_trans n.isLt i.isLt⟩ b) ''
                Set.univ) := by
          rw [hv_eq]
          apply Submodule.sum_mem
          intro j' _
          apply Submodule.smul_mem
          have hj'_lt : j'.val < i.val := j'.isLt
          have hj'_le_k : j'.val ≤ k := by
            have : j'.val < i.val := j'.isLt
            omega
          exact h_e_in_span_v k ⟨j'.val, lt_trans j'.isLt i.isLt⟩ hj'_le_k hj'_lt
        -- Get the contradiction: v_i is the i-th element of a linearly
        -- independent family but is in the span of the previous ones.
        -- Use `LinearIndependent.notMem_span_image`.
        have hcontra : chartBasisVecFiber (I := I) α i b ∉
            Submodule.span ℝ
              ((fun n : Fin i.val =>
                chartBasisVecFiber (I := I) α
                  ⟨n.val, lt_trans n.isLt i.isLt⟩ b) ''
                Set.univ) := by
          -- Convert to the form `LinearIndependent.notMem_span_image` accepts.
          -- The lemma states: for a LI family `f` and a set `s` with `i ∉ s`,
          -- `f i ∉ Submodule.span (f '' s)`.
          -- Here our set is the image of the inclusion `Fin i.val ↪ Fin (Module.finrank ℝ E)`,
          -- which excludes `i` (since `i.val ≥ i.val` whilst the set has `n.val < i.val`).
          have hset_eq :
              ((fun n : Fin i.val =>
                chartBasisVecFiber (I := I) α
                  ⟨n.val, lt_trans n.isLt i.isLt⟩ b) ''
                Set.univ) =
              ((fun n : Fin (Module.finrank ℝ E) =>
                chartBasisVecFiber (I := I) α n b) ''
                {n : Fin (Module.finrank ℝ E) | n.val < i.val}) := by
            ext v
            constructor
            · rintro ⟨n, _, rfl⟩
              refine ⟨⟨n.val, lt_trans n.isLt i.isLt⟩, n.isLt, rfl⟩
            · rintro ⟨n, hn, rfl⟩
              refine ⟨⟨n.val, hn⟩, ?_, rfl⟩
              exact Set.mem_univ _
          rw [hset_eq]
          have hi_notin : i ∉ {n : Fin (Module.finrank ℝ E) | n.val < i.val} := by
            simp [Set.mem_setOf_eq]
          exact hLI.notMem_span_image hi_notin
        exact hcontra hvi_in_span
      -- Step 3: orthogonality and unit norm of e_i.
      -- e_i = (1/sqrt(⟨raw_i, raw_i⟩)) • raw_i.
      -- For j.val < i.val, ⟨e_j, e_i⟩ = (1/sqrt(...)) • ⟨e_j, raw_i⟩ = 0 by
      -- horth_raw.
      -- For j = i, ⟨e_i, e_i⟩ = (1/sqrt(...))^2 • ⟨raw_i, raw_i⟩ = 1.
      have hgpos : 0 < g.inner b
          (chartFrameRawFiber (I := I) g α b i)
          (chartFrameRawFiber (I := I) g α b i) :=
        g.pos b (chartFrameRawFiber (I := I) g α b i) hraw_ne
      set N : ℝ := g.inner b
          (chartFrameRawFiber (I := I) g α b i)
          (chartFrameRawFiber (I := I) g α b i) with hN_def
      set s : ℝ := Real.sqrt N with hs_def
      have hs_pos : 0 < s := Real.sqrt_pos.mpr hgpos
      have hs_ne : s ≠ 0 := ne_of_gt hs_pos
      have hs_sq : s * s = N := Real.mul_self_sqrt (le_of_lt hgpos)
      refine ⟨hraw_ne, ?_, ?_⟩
      · intro j hj_lt
        -- Rewrite e_i (only the second slot).
        have hei_eq : chartFrameNormFiber (I := I) g α b i =
            s⁻¹ • chartFrameRawFiber (I := I) g α b i :=
          chartFrameNormFiber_eq (I := I) g α b i
        rw [hei_eq]
        -- ⟨e_j, s⁻¹ • raw_i⟩ = s⁻¹ * ⟨e_j, raw_i⟩ = 0.
        rw [show g.inner b (chartFrameNormFiber (I := I) g α b j)
              (s⁻¹ • chartFrameRawFiber (I := I) g α b i) =
            s⁻¹ * g.inner b (chartFrameNormFiber (I := I) g α b j)
              (chartFrameRawFiber (I := I) g α b i) from by
          rw [map_smul]; rfl]
        rw [horth_raw j hj_lt, mul_zero]
      · -- ⟨e_i, e_i⟩ = (s⁻¹)^2 * ⟨raw_i, raw_i⟩ = 1.
        have hei_eq : chartFrameNormFiber (I := I) g α b i =
            s⁻¹ • chartFrameRawFiber (I := I) g α b i :=
          chartFrameNormFiber_eq (I := I) g α b i
        rw [hei_eq]
        -- g.inner b (s⁻¹ • raw_i) (s⁻¹ • raw_i) = s⁻¹ * (s⁻¹ * ⟨raw_i, raw_i⟩).
        have hinner_smul :
            g.inner b (s⁻¹ • chartFrameRawFiber (I := I) g α b i)
                (s⁻¹ • chartFrameRawFiber (I := I) g α b i) =
            s⁻¹ * (s⁻¹ * g.inner b
              (chartFrameRawFiber (I := I) g α b i)
              (chartFrameRawFiber (I := I) g α b i)) := by
          have h1 : g.inner b (s⁻¹ • chartFrameRawFiber (I := I) g α b i) =
              s⁻¹ • g.inner b (chartFrameRawFiber (I := I) g α b i) := by
            rw [map_smul]
          rw [h1, ContinuousLinearMap.smul_apply, smul_eq_mul]
          rw [show g.inner b (chartFrameRawFiber (I := I) g α b i)
                (s⁻¹ • chartFrameRawFiber (I := I) g α b i) =
              s⁻¹ * g.inner b (chartFrameRawFiber (I := I) g α b i)
                (chartFrameRawFiber (I := I) g α b i) from by
            rw [map_smul]; rfl]
        rw [hinner_smul]
        change s⁻¹ * (s⁻¹ * N) = 1
        have h1 : s⁻¹ * (s⁻¹ * N) = (s * s)⁻¹ * N := by rw [mul_inv]; ring
        rw [h1, hs_sq]
        exact inv_mul_cancel₀ (ne_of_gt hgpos)

/-- **Inductive orthonormality** of `chartFrameNormFiber` on the trivialization
base set. For `b ∈ baseSet` and indices `i, j`, the inner product
`g.inner b (e_i b) (e_j b)` equals `1` if `i = j`, and `0` otherwise. -/
theorem chartFrameNormFiber_orthonormal
    (g : SmoothRiemannianMetric I M) (α : M) {b : M}
    (hb : b ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (i j : Fin (Module.finrank ℝ E)) :
    g.inner b
        (chartFrameNormFiber (I := I) g α b i)
        (chartFrameNormFiber (I := I) g α b j) =
      if i = j then 1 else 0 := by
  classical
  -- Use the strong-induction package.
  rcases Nat.lt_trichotomy i.val j.val with hlt | heq | hgt
  · -- i.val < j.val: use the package at j (with j.val ≤ j.val) and the
    -- orthogonality property for `i.val < j.val`.
    have h := chartFrameNormFiber_orth_strong_aux (I := I) g α hb j.val j (le_refl _)
    have horth := h.2.1 i hlt
    -- `i ≠ j` since their values differ.
    have hne : i ≠ j := by
      intro h_eq; rw [h_eq] at hlt; omega
    rw [if_neg hne, horth]
  · -- i.val = j.val: i = j by Fin.ext.
    have hi_eq_j : i = j := Fin.ext heq
    rw [if_pos hi_eq_j, ← hi_eq_j]
    have h := chartFrameNormFiber_orth_strong_aux (I := I) g α hb i.val i (le_refl _)
    exact h.2.2
  · -- i.val > j.val: by symmetry of g.inner, swap to use the j.val < i.val case.
    have h := chartFrameNormFiber_orth_strong_aux (I := I) g α hb i.val i (le_refl _)
    have horth_ji := h.2.1 j hgt
    have hne : i ≠ j := by
      intro h_eq; rw [h_eq] at hgt; omega
    rw [if_neg hne]
    rw [g.symm]
    exact horth_ji

/-- **Orthonormality** of `chartFrameNorm` on the trivialization base set. -/
theorem chartFrameNorm_orthonormal
    (g : SmoothRiemannianMetric I M) (α : M) {b : M}
    (hb : b ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (i j : Fin (Module.finrank ℝ E)) :
    g.inner b
        (chartFrameNorm (I := I) g α i b)
        (chartFrameNorm (I := I) g α j b) =
      if i = j then 1 else 0 := by
  unfold chartFrameNorm
  exact chartFrameNormFiber_orthonormal (I := I) g α hb i j

/-! ## Stage 3c: orthonormality of the bumped (smooth) frame -/

/-- **Orthonormality of the smooth orthonormal frame** on
`smoothOrthoFrameNbhd α`. -/
theorem smoothOrthoFrame_orthonormal
    (g : SmoothRiemannianMetric I M) (α : M)
    {b : M} (hb : b ∈ smoothOrthoFrameNbhd (I := I) (M := M) α)
    (i j : Fin (Module.finrank ℝ E)) :
    g.inner b
        (smoothOrthoFrame (I := I) g α i b)
        (smoothOrthoFrame (I := I) g α j b) =
      if i = j then 1 else 0 := by
  have hb_base : b ∈ (trivializationAt E (TangentSpace I) α).baseSet :=
    smoothOrthoFrameNbhd_subset_baseSet (I := I) (M := M) α hb
  exact smoothOrthoFrame_orthonormal_of_chartFrameNorm (I := I) g α hb i j
    (chartFrameNorm_orthonormal (I := I) g α hb_base i j)

/-! ## Stage 4: heart-of-Bochner exports

We re-package the conditional `heart_of_bochner_of_inner_form` from
`RicciIdentity.lean` with the smooth orthonormal frame `smoothOrthoFrame g x`
instantiated as the smooth tangent frame `B`. The hypothesis `hInner` is
preserved as an input: it expresses the inner-product reduction of the
heart-of-Bochner identity, which is the algebraic content traced over an
orthonormal frame. -/

/-- **Heart-of-Bochner inner-product form, instantiated at `smoothOrthoFrame`**.
This is the conditional inner-product identity at the point `x` against any
smooth test field, with the orthonormal frame fixed to `smoothOrthoFrame g x`.

The hypothesis `hSmooth` is the smoothness of `smoothOrthoFrame g x` as a
tangent-bundle section. The hypothesis `hInner` expresses the inner-product
reduction of the heart-of-Bochner identity, i.e. that the inner product
against any test vector `w ∈ T_x M` satisfies the Lichnerowicz combination
$$
  g_x\bigl((\Delta_\nabla^B \nabla f)(x), w\bigr) =
    g_x\bigl(\nabla(\Delta_g f)(x), w\bigr) +
      g_x\bigl(\mathrm{Ric}^\sharp(\nabla f x), w\bigr).
$$
-/
theorem heart_of_bochner_smoothOrthoFrame_of_inner_form [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    (x : M)
    (hSmooth : ∀ i, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (T% (smoothOrthoFrame (I := I) g x i)))
    (hInner : ∀ w : TangentSpace I x,
      g.inner x (localConnLap_vector (LeviCivita (I := I) g)
                  (smoothOrthoFrame (I := I) g x)
                  (fun b => gradFun (I := I) g f b) x) w =
        g.inner x (gradFun (I := I) g (Δ_g (I := I) g hf) x) w +
          g.inner x (ricciSharp (I := I) g x (gradFun (I := I) g f x)) w) :
    localConnLap_vector (LeviCivita (I := I) g) (smoothOrthoFrame (I := I) g x)
        (fun b => gradFun (I := I) g f b) x =
      gradFun (I := I) g (Δ_g (I := I) g hf) x +
        ricciSharp (I := I) g x (gradFun (I := I) g f x) :=
  heart_of_bochner_of_inner_form (I := I) g hf
    (smoothOrthoFrame (I := I) g x) hSmooth x hInner

/-! ## Stage 5: orthonormality at the centre point

A direct corollary: the smooth orthonormal frame `smoothOrthoFrame g x` is
`g`-orthonormal at the centre `x` (since `x ∈ smoothOrthoFrameNbhd x`). This
is the at-x orthonormality that the heart-of-Bochner trace reduction
consumes. -/

/-- **Orthonormality of the smooth orthonormal frame at the centre `x`.**
The frame `smoothOrthoFrame g x` is `g_x`-orthonormal. -/
theorem smoothOrthoFrame_orthonormal_at_center
    (g : SmoothRiemannianMetric I M) (x : M)
    (i j : Fin (Module.finrank ℝ E)) :
    g.inner x
        (smoothOrthoFrame (I := I) g x i x)
        (smoothOrthoFrame (I := I) g x j x) =
      if i = j then 1 else 0 :=
  smoothOrthoFrame_orthonormal (I := I) g x
    (mem_smoothOrthoFrameNbhd_self (I := I) (M := M) x) i j

/-! ## Stage 6: smoothness of the smooth orthonormal frame

We establish that each `smoothOrthoFrame g α i` is `C^∞` as a tangent-bundle
section. The proof has three steps:

1. The fiberwise inner product `b ↦ g.inner b u v` of two `C^∞` tangent
   sections is `C^∞` as a scalar; this is the standard
   `clm_bundle_apply₂`-argument.
2. By induction on `i.val`, the un-bumped Gram-Schmidt step
   `chartFrameNorm g α i b` is `C^∞` as a section on the trivialization base
   set (= chart source). The key ingredient is that the denominator
   `Real.sqrt (g.inner b raw raw)` is positive on the base set (by
   `chartFrameNormFiber_orthonormal`), so its inverse is smooth. The Gram-
   Schmidt formula combines smooth scalars and smooth sections via
   `ContMDiffOn.smul_section`, `ContMDiffOn.sum_section`, and
   `ContMDiffOn.sub_section`.
3. The bumped global section `smoothOrthoFrame g α i = (chartBumpAt α) •
   chartFrameNorm g α i` is globally `C^∞` by `ContMDiffOn.smul_section_of_tsupport`,
   using the fact that `tsupport (chartBumpAt α) ⊆ (chartAt H α).source`. -/

/-- Smoothness of the inner product of two `C^∞` tangent-bundle sections, on a
chosen open set `s ⊆ M`. -/
private lemma g_inner_contMDiffOn_of_sections
    (g : SmoothRiemannianMetric I M)
    {Y Z : Π b : M, TangentSpace I b} {s : Set M}
    (hY : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞ (T% Y) s)
    (hZ : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞ (T% Z) s) :
    ContMDiffOn I 𝓘(ℝ) ∞ (fun b : M => g.inner b (Y b) (Z b)) s := by
  classical
  have hg : ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun b : M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun y => TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
        b (g.inner b)) s :=
    g.contMDiff.contMDiffOn
  have happ :
      ContMDiffOn I (I.prod 𝓘(ℝ, ℝ)) ∞
        (fun m : M => (⟨m,
            g.inner m (Y m) (Z m)⟩ :
              TotalSpace ℝ (Bundle.Trivial M ℝ))) s :=
    ContMDiffOn.clm_bundle_apply₂ (F₁ := E) (F₂ := E) (F₃ := ℝ)
      (b := id) hg hY hZ
  intro x hx
  have hpx := happ x hx
  rw [Bundle.contMDiffWithinAt_totalSpace] at hpx
  exact hpx.2

/-- **Step 1 of B2:** the chart-basis section `chartBasisVec g α i` (as a
section of the tangent bundle, expressed via the `T%` elaborator) is `C^∞` on
the trivialization base set. Restated form of
`chartBasisVec_contMDiffOn`. -/
private lemma chartBasisVec_contMDiffOn_section
    (α : M) (i : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
        (T% (fun b : M => chartBasisVecFiber (I := I) α i b))
        (trivializationAt E (TangentSpace I) α).baseSet := by
  intro x hx
  have h := chartBasisVec_contMDiffOn (I := I) α i x hx
  exact h

set_option maxHeartbeats 4000000 in
/-- **Step 2a of B2 (strong-induction package):** smoothness of
`chartFrameRawFiber` and `chartFrameNormFiber` on the trivialization base set.

We prove the joint statement by `Nat.strong_induction_on` on the bound `k :
ℕ`: for every `i : Fin (Module.finrank ℝ E)` with `i.val ≤ k`, both the raw
and normalised vectors define `C^∞` sections on the base set. -/
private theorem chartFrameNormFiber_contMDiffOn_strong
    (g : SmoothRiemannianMetric I M) (α : M) :
    ∀ k : ℕ, ∀ i : Fin (Module.finrank ℝ E), i.val ≤ k →
      ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
        (T% (fun b : M => chartFrameRawFiber (I := I) g α b i))
        (trivializationAt E (TangentSpace I) α).baseSet ∧
      ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
        (T% (fun b : M => chartFrameNormFiber (I := I) g α b i))
        (trivializationAt E (TangentSpace I) α).baseSet := by
  classical
  intro k
  induction k with
  | zero =>
    intro i hi
    have hi_val : i.val = 0 := Nat.le_zero.mp hi
    have hi_eq : i = ⟨0, NeZero.pos _⟩ := Fin.ext hi_val
    subst hi_eq
    refine ⟨?_, ?_⟩
    · -- raw_0 = chartBasisVecFiber α ⟨0, _⟩
      -- We rewrite the section: at every `b`, raw_0 b = chartBasisVecFiber α ⟨0,_⟩ b
      have hsec_eq : ∀ b : M,
          chartFrameRawFiber (I := I) g α b ⟨0, NeZero.pos _⟩ =
            chartBasisVecFiber (I := I) α ⟨0, NeZero.pos _⟩ b :=
        fun b => chartFrameRawFiber_at_zero (I := I) g α b
      -- Sections agreeing pointwise are smooth iff one is.
      have hbase :=
        chartBasisVec_contMDiffOn_section (I := I) α ⟨0, NeZero.pos _⟩
      -- The `T%` of the raw fiber equals `T%` of the chart-basis vec at every
      -- point.
      have hT_eq : (fun b : M => TotalSpace.mk' E
              (E := TangentSpace I) b
              (chartFrameRawFiber (I := I) g α b ⟨0, NeZero.pos _⟩)) =
          (fun b : M => TotalSpace.mk' E (E := TangentSpace I) b
              (chartBasisVecFiber (I := I) α ⟨0, NeZero.pos _⟩ b)) := by
        funext b; rw [hsec_eq b]
      rw [hT_eq]
      exact hbase
    · -- norm_0 b = (sqrt (g.inner b raw_0 raw_0))⁻¹ • raw_0 b
      -- with raw_0 = chartBasisVec.
      have hsec_eq : ∀ b : M,
          chartFrameNormFiber (I := I) g α b ⟨0, NeZero.pos _⟩ =
            (Real.sqrt (g.inner b
                (chartBasisVecFiber (I := I) α ⟨0, NeZero.pos _⟩ b)
                (chartBasisVecFiber (I := I) α ⟨0, NeZero.pos _⟩ b)))⁻¹ •
              chartBasisVecFiber (I := I) α ⟨0, NeZero.pos _⟩ b :=
        fun b => chartFrameNormFiber_at_zero (I := I) g α b
      have hbase :=
        chartBasisVec_contMDiffOn_section (I := I) α ⟨0, NeZero.pos _⟩
      -- Smoothness of the scalar `b ↦ Real.sqrt (g.inner b v v)` and its
      -- inverse on the base set.
      -- Step a: g.inner b v v is smooth on baseSet.
      have h_inner :
          ContMDiffOn I 𝓘(ℝ) ∞
            (fun b : M => g.inner b
                (chartBasisVecFiber (I := I) α ⟨0, NeZero.pos _⟩ b)
                (chartBasisVecFiber (I := I) α ⟨0, NeZero.pos _⟩ b))
            (trivializationAt E (TangentSpace I) α).baseSet :=
        g_inner_contMDiffOn_of_sections (I := I) g hbase hbase
      -- Step b: g.inner b v v > 0 on the base set, so Real.sqrt of it ≠ 0.
      have h_inner_pos : ∀ b : M,
          b ∈ (trivializationAt E (TangentSpace I) α).baseSet →
          0 < g.inner b
              (chartBasisVecFiber (I := I) α ⟨0, NeZero.pos _⟩ b)
              (chartBasisVecFiber (I := I) α ⟨0, NeZero.pos _⟩ b) := by
        intro b hb
        have hLI := chartBasisFamily_linearIndependent (I := I) α hb
        have hv_ne_zero :
            chartBasisVecFiber (I := I) α ⟨0, NeZero.pos _⟩ b ≠ 0 :=
          hLI.ne_zero ⟨0, NeZero.pos _⟩
        exact g.pos b _ hv_ne_zero
      have h_sqrt_ne :
          ∀ b ∈ (trivializationAt E (TangentSpace I) α).baseSet,
          Real.sqrt (g.inner b
              (chartBasisVecFiber (I := I) α ⟨0, NeZero.pos _⟩ b)
              (chartBasisVecFiber (I := I) α ⟨0, NeZero.pos _⟩ b)) ≠ 0 := by
        intro b hb
        have := h_inner_pos b hb
        exact ne_of_gt (Real.sqrt_pos.mpr this)
      -- Step c: smoothness of `b ↦ Real.sqrt (g.inner b v v)`.
      have h_sqrt :
          ContMDiffOn I 𝓘(ℝ) ∞
            (fun b : M => Real.sqrt
                (g.inner b
                  (chartBasisVecFiber (I := I) α ⟨0, NeZero.pos _⟩ b)
                  (chartBasisVecFiber (I := I) α ⟨0, NeZero.pos _⟩ b)))
            (trivializationAt E (TangentSpace I) α).baseSet := by
        intro b hb
        have h_inner_at := h_inner b hb
        have hpos := h_inner_pos b hb
        have h_sqrt_real : ContDiffAt ℝ ∞ Real.sqrt
            (g.inner b
              (chartBasisVecFiber (I := I) α ⟨0, NeZero.pos _⟩ b)
              (chartBasisVecFiber (I := I) α ⟨0, NeZero.pos _⟩ b)) :=
          Real.contDiffAt_sqrt (ne_of_gt hpos)
        have h_sqrt_md :
            ContMDiffAt 𝓘(ℝ) 𝓘(ℝ) ∞ Real.sqrt
              (g.inner b
                (chartBasisVecFiber (I := I) α ⟨0, NeZero.pos _⟩ b)
                (chartBasisVecFiber (I := I) α ⟨0, NeZero.pos _⟩ b)) :=
          h_sqrt_real.contMDiffAt
        exact h_sqrt_md.comp_contMDiffWithinAt (I := I) (I' := 𝓘(ℝ))
          (I'' := 𝓘(ℝ)) b h_inner_at
      -- Step d: smoothness of `b ↦ 1 / Real.sqrt (g.inner b v v)` (the
      -- inverse) on the base set.
      have h_inv :
          ContMDiffOn I 𝓘(ℝ) ∞
            (fun b : M =>
              (Real.sqrt (g.inner b
                (chartBasisVecFiber (I := I) α ⟨0, NeZero.pos _⟩ b)
                (chartBasisVecFiber (I := I) α ⟨0, NeZero.pos _⟩ b)))⁻¹)
            (trivializationAt E (TangentSpace I) α).baseSet := by
        intro b hb
        exact (h_sqrt b hb).inv₀ (h_sqrt_ne b hb)
      -- Step e: combine to get smoothness of the section
      -- `b ↦ inv • chartBasisVecFiber α 0 b`.
      have h_smul :
          ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
            (T% (fun b : M =>
              (Real.sqrt (g.inner b
                (chartBasisVecFiber (I := I) α ⟨0, NeZero.pos _⟩ b)
                (chartBasisVecFiber (I := I) α ⟨0, NeZero.pos _⟩ b)))⁻¹ •
              chartBasisVecFiber (I := I) α ⟨0, NeZero.pos _⟩ b))
            (trivializationAt E (TangentSpace I) α).baseSet :=
        ContMDiffOn.smul_section h_inv hbase
      -- Step f: rewrite to chartFrameNormFiber form.
      have hT_eq : (fun b : M => TotalSpace.mk' E
              (E := TangentSpace I) b
              (chartFrameNormFiber (I := I) g α b ⟨0, NeZero.pos _⟩)) =
          (fun b : M => TotalSpace.mk' E (E := TangentSpace I) b
              ((Real.sqrt (g.inner b
                (chartBasisVecFiber (I := I) α ⟨0, NeZero.pos _⟩ b)
                (chartBasisVecFiber (I := I) α ⟨0, NeZero.pos _⟩ b)))⁻¹ •
              chartBasisVecFiber (I := I) α ⟨0, NeZero.pos _⟩ b)) := by
        funext b; rw [hsec_eq b]
      rw [hT_eq]
      exact h_smul
  | succ k ih =>
    intro i hi
    by_cases hcase : i.val ≤ k
    · exact ih i hcase
    · -- i.val = k + 1
      have hi_val : i.val = k + 1 := by omega
      -- The induction hypothesis at all earlier indices `j` (with j.val ≤ k).
      -- This is needed because the raw-fiber sum at `i` ranges over `j : Fin
      -- i.val`.
      have ih_below : ∀ j : Fin (Module.finrank ℝ E), j.val < i.val →
          ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
            (T% (fun b : M => chartFrameNormFiber (I := I) g α b j))
            (trivializationAt E (TangentSpace I) α).baseSet := by
        intro j hj
        have hj_le_k : j.val ≤ k := by omega
        exact (ih j hj_le_k).2
      -- Step A: smoothness of raw_i.
      -- raw_i b = v_i b - ∑_{j' : Fin i.val} ⟨v_i, e_{⟨j'.val, _⟩}⟩ • e_{⟨j'.val, _⟩}.
      have hbase_i :=
        chartBasisVec_contMDiffOn_section (I := I) α i
      -- For each `j' : Fin i.val`, define the "small" index `⟨j'.val, _⟩ : Fin
      -- (Module.finrank ℝ E)` and use `ih_below`.
      have h_j'_small_section : ∀ j' : Fin i.val,
          ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
            (T% (fun b : M => chartFrameNormFiber (I := I) g α b
              ⟨j'.val, lt_trans j'.isLt i.isLt⟩))
            (trivializationAt E (TangentSpace I) α).baseSet := by
        intro j'
        exact ih_below ⟨j'.val, lt_trans j'.isLt i.isLt⟩ j'.isLt
      -- The inner product of v_i and the j'-th unit vector is smooth.
      have h_innerCoef : ∀ j' : Fin i.val,
          ContMDiffOn I 𝓘(ℝ) ∞
            (fun b : M => g.inner b
              (chartBasisVecFiber (I := I) α i b)
              (chartFrameNormFiber (I := I) g α b
                ⟨j'.val, lt_trans j'.isLt i.isLt⟩))
            (trivializationAt E (TangentSpace I) α).baseSet := by
        intro j'
        exact g_inner_contMDiffOn_of_sections (I := I) g hbase_i
          (h_j'_small_section j')
      -- Each summand is smooth as a section.
      have h_summand : ∀ j' ∈ (Finset.univ : Finset (Fin i.val)),
          ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
            (T% (fun b : M =>
              g.inner b
                (chartBasisVecFiber (I := I) α i b)
                (chartFrameNormFiber (I := I) g α b
                  ⟨j'.val, lt_trans j'.isLt i.isLt⟩) •
              chartFrameNormFiber (I := I) g α b
                ⟨j'.val, lt_trans j'.isLt i.isLt⟩))
            (trivializationAt E (TangentSpace I) α).baseSet := by
        intro j' _
        exact ContMDiffOn.smul_section
          (h_innerCoef j') (h_j'_small_section j')
      -- The finite sum is smooth as a section.
      have h_sum :
          ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
            (T% (fun b : M =>
              ∑ j' : Fin i.val,
                g.inner b
                  (chartBasisVecFiber (I := I) α i b)
                  (chartFrameNormFiber (I := I) g α b
                    ⟨j'.val, lt_trans j'.isLt i.isLt⟩) •
                chartFrameNormFiber (I := I) g α b
                  ⟨j'.val, lt_trans j'.isLt i.isLt⟩))
            (trivializationAt E (TangentSpace I) α).baseSet :=
        ContMDiffOn.sum_section h_summand
      -- raw_i = v_i - ∑.
      have h_raw : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
          (T% (fun b : M =>
            chartBasisVecFiber (I := I) α i b -
              ∑ j' : Fin i.val,
                g.inner b
                  (chartBasisVecFiber (I := I) α i b)
                  (chartFrameNormFiber (I := I) g α b
                    ⟨j'.val, lt_trans j'.isLt i.isLt⟩) •
                chartFrameNormFiber (I := I) g α b
                  ⟨j'.val, lt_trans j'.isLt i.isLt⟩))
          (trivializationAt E (TangentSpace I) α).baseSet :=
        ContMDiffOn.sub_section hbase_i h_sum
      -- Identify raw_i pointwise.
      have h_raw_eq : ∀ b : M,
          chartFrameRawFiber (I := I) g α b i =
            chartBasisVecFiber (I := I) α i b -
              ∑ j' : Fin i.val,
                g.inner b
                  (chartBasisVecFiber (I := I) α i b)
                  (chartFrameNormFiber (I := I) g α b
                    ⟨j'.val, lt_trans j'.isLt i.isLt⟩) •
                chartFrameNormFiber (I := I) g α b
                  ⟨j'.val, lt_trans j'.isLt i.isLt⟩ := fun b => by
        unfold chartFrameRawFiber; rfl
      have h_raw_section :
          ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
            (T% (fun b : M => chartFrameRawFiber (I := I) g α b i))
            (trivializationAt E (TangentSpace I) α).baseSet := by
        have hT_eq : (fun b : M => TotalSpace.mk' E
                (E := TangentSpace I) b
                (chartFrameRawFiber (I := I) g α b i)) =
            (fun b : M => TotalSpace.mk' E (E := TangentSpace I) b
                (chartBasisVecFiber (I := I) α i b -
                  ∑ j' : Fin i.val,
                    g.inner b
                      (chartBasisVecFiber (I := I) α i b)
                      (chartFrameNormFiber (I := I) g α b
                        ⟨j'.val, lt_trans j'.isLt i.isLt⟩) •
                    chartFrameNormFiber (I := I) g α b
                      ⟨j'.val, lt_trans j'.isLt i.isLt⟩)) := by
          funext b; rw [h_raw_eq b]
        rw [hT_eq]
        exact h_raw
      -- Step B: smoothness of norm_i.
      -- norm_i = (sqrt ⟨raw_i, raw_i⟩)⁻¹ • raw_i.
      have h_inner_raw :
          ContMDiffOn I 𝓘(ℝ) ∞
            (fun b : M => g.inner b
                (chartFrameRawFiber (I := I) g α b i)
                (chartFrameRawFiber (I := I) g α b i))
            (trivializationAt E (TangentSpace I) α).baseSet :=
        g_inner_contMDiffOn_of_sections (I := I) g h_raw_section h_raw_section
      -- Positivity / nonzero of raw_i and its norm on the base set: comes from
      -- the orthonormality package.
      have h_inner_raw_pos : ∀ b : M,
          b ∈ (trivializationAt E (TangentSpace I) α).baseSet →
          0 < g.inner b
              (chartFrameRawFiber (I := I) g α b i)
              (chartFrameRawFiber (I := I) g α b i) := by
        intro b hb
        have h_aux := chartFrameNormFiber_orth_strong_aux
          (I := I) g α hb i.val i (le_refl _)
        have hraw_ne : chartFrameRawFiber (I := I) g α b i ≠ 0 := h_aux.1
        exact g.pos b _ hraw_ne
      have h_sqrt_ne :
          ∀ b ∈ (trivializationAt E (TangentSpace I) α).baseSet,
          Real.sqrt (g.inner b
              (chartFrameRawFiber (I := I) g α b i)
              (chartFrameRawFiber (I := I) g α b i)) ≠ 0 := by
        intro b hb
        have := h_inner_raw_pos b hb
        exact ne_of_gt (Real.sqrt_pos.mpr this)
      have h_sqrt :
          ContMDiffOn I 𝓘(ℝ) ∞
            (fun b : M => Real.sqrt
                (g.inner b
                  (chartFrameRawFiber (I := I) g α b i)
                  (chartFrameRawFiber (I := I) g α b i)))
            (trivializationAt E (TangentSpace I) α).baseSet := by
        intro b hb
        have h_inner_at := h_inner_raw b hb
        have hpos := h_inner_raw_pos b hb
        have h_sqrt_real : ContDiffAt ℝ ∞ Real.sqrt
            (g.inner b
              (chartFrameRawFiber (I := I) g α b i)
              (chartFrameRawFiber (I := I) g α b i)) :=
          Real.contDiffAt_sqrt (ne_of_gt hpos)
        have h_sqrt_md :
            ContMDiffAt 𝓘(ℝ) 𝓘(ℝ) ∞ Real.sqrt
              (g.inner b
                (chartFrameRawFiber (I := I) g α b i)
                (chartFrameRawFiber (I := I) g α b i)) :=
          h_sqrt_real.contMDiffAt
        exact h_sqrt_md.comp_contMDiffWithinAt (I := I) (I' := 𝓘(ℝ))
          (I'' := 𝓘(ℝ)) b h_inner_at
      have h_inv :
          ContMDiffOn I 𝓘(ℝ) ∞
            (fun b : M =>
              (Real.sqrt (g.inner b
                (chartFrameRawFiber (I := I) g α b i)
                (chartFrameRawFiber (I := I) g α b i)))⁻¹)
            (trivializationAt E (TangentSpace I) α).baseSet := by
        intro b hb
        exact (h_sqrt b hb).inv₀ (h_sqrt_ne b hb)
      have h_smul :
          ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
            (T% (fun b : M =>
              (Real.sqrt (g.inner b
                (chartFrameRawFiber (I := I) g α b i)
                (chartFrameRawFiber (I := I) g α b i)))⁻¹ •
              chartFrameRawFiber (I := I) g α b i))
            (trivializationAt E (TangentSpace I) α).baseSet :=
        ContMDiffOn.smul_section h_inv h_raw_section
      -- norm_i = (sqrt ⟨raw_i, raw_i⟩)⁻¹ • raw_i pointwise.
      have h_norm_eq : ∀ b : M,
          chartFrameNormFiber (I := I) g α b i =
            (Real.sqrt (g.inner b
                (chartFrameRawFiber (I := I) g α b i)
                (chartFrameRawFiber (I := I) g α b i)))⁻¹ •
              chartFrameRawFiber (I := I) g α b i := fun b =>
        chartFrameNormFiber_eq (I := I) g α b i
      have h_norm_section :
          ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
            (T% (fun b : M => chartFrameNormFiber (I := I) g α b i))
            (trivializationAt E (TangentSpace I) α).baseSet := by
        have hT_eq : (fun b : M => TotalSpace.mk' E
                (E := TangentSpace I) b
                (chartFrameNormFiber (I := I) g α b i)) =
            (fun b : M => TotalSpace.mk' E (E := TangentSpace I) b
                ((Real.sqrt (g.inner b
                  (chartFrameRawFiber (I := I) g α b i)
                  (chartFrameRawFiber (I := I) g α b i)))⁻¹ •
                chartFrameRawFiber (I := I) g α b i)) := by
          funext b; rw [h_norm_eq b]
        rw [hT_eq]
        exact h_smul
      exact ⟨h_raw_section, h_norm_section⟩

/-- **Step 2 of B2:** smoothness of `chartFrameNorm g α i b` on the
trivialization base set, as a tangent-bundle section in `b`. -/
lemma chartFrameNorm_contMDiffOn
    (g : SmoothRiemannianMetric I M) (α : M)
    (i : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
        (T% (fun b : M => chartFrameNorm (I := I) g α i b))
        (trivializationAt E (TangentSpace I) α).baseSet := by
  unfold chartFrameNorm
  exact (chartFrameNormFiber_contMDiffOn_strong (I := I) g α i.val i (le_refl _)).2

/-- **Step 3 of B2 — global smoothness of the smooth orthonormal frame.**
Each component `smoothOrthoFrame g α i` is `C^∞` as a tangent-bundle section
on `M`. -/
theorem smoothOrthoFrame_smooth
    (g : SmoothRiemannianMetric I M) (α : M)
    (i : Fin (Module.finrank ℝ E)) :
    ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
        (T% (smoothOrthoFrame (I := I) g α i)) := by
  classical
  -- Set up the data: u := chart source, ψ := chart bump, s := chart-frame norm.
  set u : Set M := (chartAt H α).source with hu_def
  set ψ : M → ℝ := (chartBumpAt (I := I) (M := M) α : M → ℝ) with hψ_def
  -- The bump is C^∞ on `u`.
  have hψ_smooth : ContMDiffOn I 𝓘(ℝ) ∞ ψ u :=
    (chartBumpAt (I := I) (M := M) α).contMDiff.contMDiffOn
  -- u is open.
  have hu_open : IsOpen u := (chartAt H α).open_source
  -- tsupport ψ ⊆ u.
  have hψ_tsupport : tsupport ψ ⊆ u :=
    (chartBumpAt (I := I) (M := M) α).tsupport_subset_chartAt_source
  -- chartFrameNorm g α i is C^∞ on u (= base set).
  have hs_smooth : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (T% (fun b : M => chartFrameNorm (I := I) g α i b)) u := by
    rw [show u = (trivializationAt E (TangentSpace I) α).baseSet from rfl]
    exact chartFrameNorm_contMDiffOn (I := I) g α i
  -- Combine via `ContMDiffOn.smul_section_of_tsupport` (Mathlib).
  have h := ContMDiffOn.smul_section_of_tsupport (𝕜 := ℝ) (n := ∞)
    (V := TangentSpace I) hψ_smooth hu_open hψ_tsupport hs_smooth
  -- The conclusion is C^∞ of (T% (ψ • chartFrameNorm g α i)). We need to
  -- identify this with `T% (smoothOrthoFrame g α i)`.
  -- By definition: `(ψ • s) b = ψ b • s b`.
  -- And `smoothOrthoFrame g α i b = ψ b • chartFrameNorm g α i b` (from the
  -- definition of `smoothOrthoFrame` in this file).
  have h_eq : (fun b : M => TotalSpace.mk' E (E := TangentSpace I) b
        (smoothOrthoFrame (I := I) g α i b)) =
      (fun b : M => TotalSpace.mk' E (E := TangentSpace I) b
        ((ψ • fun b' : M => chartFrameNorm (I := I) g α i b') b)) := by
    funext b
    -- smoothOrthoFrame g α i b = ψ b • chartFrameNorm g α i b
    change TotalSpace.mk' E b (smoothOrthoFrame (I := I) g α i b) =
      TotalSpace.mk' E b ((ψ b) • chartFrameNorm (I := I) g α i b)
    unfold smoothOrthoFrame
    rfl
  rw [h_eq]
  exact h

/-! ## Stage 7: heart-of-Bochner re-packaging without explicit smoothness
hypothesis

By Stage 6, each `smoothOrthoFrame g x i` is `C^∞`. Combined with the
conditional inner-product form `heart_of_bochner_smoothOrthoFrame_of_inner_form`,
this produces a re-packaging that drops the explicit `hSmooth` hypothesis.

The remaining `hInner` hypothesis encodes the algebraic content of the
heart-of-Bochner reduction (Hessian-symmetry / metric-skew of curvature on the
smooth orthonormal frame), and is the natural input for the downstream Bochner
trace identity. -/

/-- **Heart-of-Bochner inner-product form on the smooth orthonormal frame, with
smoothness discharged.** Combines `heart_of_bochner_smoothOrthoFrame_of_inner_form`
with the smoothness witness `smoothOrthoFrame_smooth`.

The remaining hypothesis `hInner` is the inner-product reduction at `x` against
any test vector, expressing the heart-of-Bochner identity in inner-product form
(which is, for an orthonormal frame, equivalent to the textbook
metric-Hessian-symmetry / curvature-trace combinatorial reduction). -/
theorem heart_of_bochner_smoothOrthoFrame [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    (x : M)
    (hInner : ∀ w : TangentSpace I x,
      g.inner x (localConnLap_vector (LeviCivita (I := I) g)
                  (smoothOrthoFrame (I := I) g x)
                  (fun b => gradFun (I := I) g f b) x) w =
        g.inner x (gradFun (I := I) g (Δ_g (I := I) g hf) x) w +
          g.inner x (ricciSharp (I := I) g x (gradFun (I := I) g f x)) w) :
    localConnLap_vector (LeviCivita (I := I) g) (smoothOrthoFrame (I := I) g x)
        (fun b => gradFun (I := I) g f b) x =
      gradFun (I := I) g (Δ_g (I := I) g hf) x +
        ricciSharp (I := I) g x (gradFun (I := I) g f x) :=
  heart_of_bochner_smoothOrthoFrame_of_inner_form (I := I) g hf x
    (fun i => smoothOrthoFrame_smooth (I := I) g x i) hInner

end Connection
end Integral
end DifferentialGeometry
