import DifferentialGeometry.Geometry.Riemannian.Exponential.Definition
import DifferentialGeometry.Geometry.Riemannian.Exponential.MfderivAtZero
import DifferentialGeometry.Geometry.Riemannian.NormalCoordinates
import DifferentialGeometry.Geometry.Riemannian.InjectivityRadius
import DifferentialGeometry.Geometry.Riemannian.Geodesic.Equation
import DifferentialGeometry.Geometry.Riemannian.Geodesic.Uniqueness
import DifferentialGeometry.Geometry.Riemannian.Geodesic.MaximalInterval
import DifferentialGeometry.Integral.Measure.ChartDensity
import Mathlib.Geometry.Manifold.Riemannian.PathELength

set_option linter.unusedSectionVars false

/-!
# Gauss's lemma and the radial-minimiser package

For a smooth Riemannian metric `g` on a boundaryless smooth manifold `M`,
this file packages the classical Gauss-lemma cluster:

* `gauss_lemma_pullback` — the pullback of `g` through `expMap g p` at
  a radial direction `v` evaluates to `⟪v, v⟫` on the `(v, v)` slot and
  to `0` on the `(v, w)` slot whenever `w` satisfies `⟪v, w⟫ = 0`.

* `subArc_of_minimizer_is_minimizer` — a sub-arc of a length-minimising
  curve is itself a length-minimiser between its restricted endpoints.

* `normalBall_radial_unique_minimizer` — inside a normal ball at `p`,
  every `C¹` curve from `p` to `expMap g p v` has `pathELength ≥ ‖v‖`,
  with equality only for a monotone radial reparametrisation.

* `local_radial_identification_of_minimizer` — at any interior parameter
  of a length-minimising curve there is a `δ`-neighbourhood on which the
  curve is a monotone radial geodesic in normal coordinates at `γ(t₀)`.

* `arclength_reparam_is_smooth_geodesic` — the global arclength
  reparametrisation of a length-minimiser is a smooth geodesic on the
  open parameter interval.

All five statements live below as `theorem ... := sorry` stubs.
-/

noncomputable section

open Set Function Filter Bundle Manifold
open scoped Topology Manifold ContDiff ENNReal

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Riemannian.Exponential

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

section GaussLemma

variable [I.Boundaryless] [CompleteSpace E] [T2Space (TangentBundle I M)]

/-! ## Gauss's lemma (pullback form)

The pullback of the Riemannian metric through `expMap g p` at a radial
direction `v` (inside the natural domain) preserves the radial inner
product and annihilates the radial/orthogonal cross term. We split the
two equalities into two theorems for clean downstream consumption. -/

/-- **Gauss's lemma (pullback form).** At every radial direction
`v ∈ expDomain g p`, the pullback of `g` through `expMap g p` evaluates
to `g_p(v, v)` on the `(v, v)` slot, and annihilates the `(v, w)` slot
for every `w` that is `g_p`-orthogonal to `v`. The orthogonality and
the target value are stated in the abstract metric `g.inner p`; the
model-space Euclidean inner product `inner ℝ` on `E` is unrelated to
`g.inner p` in general (its appearance in earlier skeleton drafts was a
defect: the classical Gauss lemma is intrinsic to `g`). -/
theorem gauss_lemma_pullback
    (g : SmoothRiemannianMetric I M) (p : M) {v : E}
    (hv : (show TangentSpace I p from v) ∈ expDomain (I := I) g p) :
    g.inner (expMap (I := I) g p (show TangentSpace I p from v))
        (mfderiv 𝓘(ℝ, E) I
          (fun u : E => expMap (I := I) g p (show TangentSpace I p from u)) v
          (show TangentSpace I p from v))
        (mfderiv 𝓘(ℝ, E) I
          (fun u : E => expMap (I := I) g p (show TangentSpace I p from u)) v
          (show TangentSpace I p from v)) =
      g.inner p v v ∧
    ∀ {w : E}, g.inner p v w = (0 : ℝ) →
      g.inner (expMap (I := I) g p (show TangentSpace I p from v))
          (mfderiv 𝓘(ℝ, E) I
            (fun u : E => expMap (I := I) g p (show TangentSpace I p from u)) v
            (show TangentSpace I p from v))
          (mfderiv 𝓘(ℝ, E) I
            (fun u : E => expMap (I := I) g p (show TangentSpace I p from u)) v
            (show TangentSpace I p from w)) =
        (0 : ℝ) := by
  sorry

end GaussLemma

section LengthBookkeeping

/-! ## Sub-arc of a minimiser is itself a minimiser

Pure metric bookkeeping built from
`Mathlib.Geometry.Manifold.Riemannian.PathELength`. -/

set_option linter.unusedVariables false in
/-- **A sub-arc of a length-minimising `C¹` curve is itself a
length-minimiser between its restricted endpoints.** That is, if a
curve `γ : ℝ → M` realises `riemannianEDist I (γ a) (γ b) = pathELength I γ a b`
on `[a, b]`, then on every sub-interval `[s, t] ⊆ [a, b]` the sub-arc
realises `riemannianEDist I (γ s) (γ t) = pathELength I γ s t`.
The hypothesis `hfin` records finiteness of the parent length: it is what
allows cancelling `pathELength I γ a s + pathELength I γ t b` from the
`ENNReal` squeeze. -/
theorem subArc_of_minimizer_is_minimizer
    {γ : ℝ → M} {a b s t : ℝ}
    (hγ : CMDiff[Icc a b] 1 γ)
    (hmin : riemannianEDist I (γ a) (γ b) = pathELength I γ a b)
    (hfin : pathELength I γ a b ≠ ⊤)
    (hab : a ≤ b) (has : a ≤ s) (hst : s ≤ t) (htb : t ≤ b) :
    riemannianEDist I (γ s) (γ t) = pathELength I γ s t := by
  -- Abbreviations.
  set L_left := pathELength I γ a s with hL_left_def
  set L_mid := pathELength I γ s t with hL_mid_def
  set L_right := pathELength I γ t b with hL_right_def
  -- Restrict smoothness to each sub-interval.
  have h_ast : a ≤ t := has.trans hst
  have h_sb : s ≤ b := hst.trans htb
  have hγ_as : CMDiff[Icc a s] 1 γ := hγ.mono (Icc_subset_Icc le_rfl h_sb)
  have hγ_st : CMDiff[Icc s t] 1 γ := hγ.mono (Icc_subset_Icc has htb)
  have hγ_tb : CMDiff[Icc t b] 1 γ := hγ.mono (Icc_subset_Icc h_ast le_rfl)
  -- Path additivity: L_left + L_mid + L_right = pathELength I γ a b.
  have hadd_left : L_left + L_mid = pathELength I γ a t :=
    pathELength_add (γ := γ) (I := I) has hst
  have hadd_total : pathELength I γ a t + L_right = pathELength I γ a b :=
    pathELength_add (γ := γ) (I := I) h_ast htb
  have hpath_total : L_left + L_mid + L_right = pathELength I γ a b := by
    rw [hadd_left, hadd_total]
  -- Sub-arc lengths are ≤ parent length, hence finite.
  have hL_left_finite : L_left ≠ ⊤ := by
    have hle : L_left ≤ pathELength I γ a b := by
      rw [← hpath_total]
      have h₁ : L_left ≤ L_left + L_mid := le_self_add
      exact h₁.trans le_self_add
    exact ne_top_of_le_ne_top hfin hle
  have hL_right_finite : L_right ≠ ⊤ := by
    have hle : L_right ≤ pathELength I γ a b := by
      rw [← hpath_total]
      exact le_add_self
    exact ne_top_of_le_ne_top hfin hle
  -- Distance ≤ length on each sub-arc.
  have hD_left : riemannianEDist I (γ a) (γ s) ≤ L_left :=
    riemannianEDist_le_pathELength hγ_as rfl rfl has
  have hD_right : riemannianEDist I (γ t) (γ b) ≤ L_right :=
    riemannianEDist_le_pathELength hγ_tb rfl rfl htb
  have hD_mid_le : riemannianEDist I (γ s) (γ t) ≤ L_mid :=
    riemannianEDist_le_pathELength hγ_st rfl rfl hst
  -- Triangle inequality (twice) on `(γ a) → (γ s) → (γ t) → (γ b)`.
  have htri₁ : riemannianEDist I (γ a) (γ b) ≤
      riemannianEDist I (γ a) (γ t) + riemannianEDist I (γ t) (γ b) :=
    riemannianEDist_triangle
  have htri₂ : riemannianEDist I (γ a) (γ t) ≤
      riemannianEDist I (γ a) (γ s) + riemannianEDist I (γ s) (γ t) :=
    riemannianEDist_triangle
  have htri_combined : riemannianEDist I (γ a) (γ b) ≤
      riemannianEDist I (γ a) (γ s) + riemannianEDist I (γ s) (γ t)
        + riemannianEDist I (γ t) (γ b) :=
    htri₁.trans (add_le_add htri₂ le_rfl)
  -- Bound the parent length by the squeezed sum.
  have hpath_le : pathELength I γ a b ≤
      L_left + riemannianEDist I (γ s) (γ t) + L_right := by
    have := htri_combined
    rw [hmin] at this
    refine this.trans ?_
    exact add_le_add (add_le_add hD_left le_rfl) hD_right
  -- Combine to obtain the squeeze on the middle term.
  have hsqueeze : L_left + L_mid + L_right
        ≤ L_left + riemannianEDist I (γ s) (γ t) + L_right := by
    calc L_left + L_mid + L_right = pathELength I γ a b := hpath_total
      _ ≤ L_left + riemannianEDist I (γ s) (γ t) + L_right := hpath_le
  -- Cancel `L_left` and `L_right` from the squeeze using their finiteness.
  -- Rearranging both sides as `L_left + L_right + L_mid` etc.
  have hsqueeze' : L_left + L_right + L_mid
        ≤ L_left + L_right + riemannianEDist I (γ s) (γ t) := by
    have heq₁ : L_left + L_mid + L_right = L_left + L_right + L_mid := by ring
    have heq₂ : L_left + riemannianEDist I (γ s) (γ t) + L_right
                  = L_left + L_right + riemannianEDist I (γ s) (γ t) := by ring
    rw [heq₁, heq₂] at hsqueeze
    exact hsqueeze
  have hL_lr_finite : L_left + L_right ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨hL_left_finite, hL_right_finite⟩
  have hmid_le_D : L_mid ≤ riemannianEDist I (γ s) (γ t) :=
    (ENNReal.add_le_add_iff_left hL_lr_finite).mp hsqueeze'
  -- Anti-symmetry between `L_mid ≤ D_mid` and `D_mid ≤ L_mid` finishes the proof.
  exact le_antisymm hD_mid_le hmid_le_D

end LengthBookkeeping

section RadialUniqueMinimizer

variable [I.Boundaryless] [CompleteSpace E] [T2Space (TangentBundle I M)]

/-! ## Inside a normal ball the radial geodesic is the unique minimiser

Direct consequence of Gauss's lemma: the metric expansion
`‖γ'‖² = (γ'_r)² + ‖γ'_a‖²_a ≥ (γ'_r)²` integrates to give a length
lower bound `≥ ‖v‖`, with equality only for a monotone radial
reparametrisation. -/

/-- **Inside the normal ball, every `C¹` curve from `p` to `expMap g p v`
has length at least the `g_p`-norm of `v`.** This is the length lower
bound delivered by Gauss's lemma; the equality-case identification of
the radial geodesic as the unique minimiser is the content of the prose
statement and the assembly downstream. The lower bound uses the
`g`-norm `√(g_p(v,v))`, not the model-space Euclidean norm `‖v‖_E`
(which has no a-priori relation to `g_p`). -/
theorem normalBall_radial_unique_minimizer
    (g : SmoothRiemannianMetric I M) (p : M) {v : E}
    (hv : (show TangentSpace I p from v) ∈ expDomain (I := I) g p)
    (hball : v ∈ (NormalCoordinates.normalChartAt (I := I) g p).target) :
    ENNReal.ofReal (Real.sqrt (g.inner p v v)) ≤
      riemannianEDist I p
        (expMap (I := I) g p (show TangentSpace I p from v)) := by
  -- The classical Gauss-lemma length lower bound. We reduce to the
  -- forall-greater formulation of `riemannianEDist` as an infimum.
  -- For every `r` strictly larger than the distance, there is a smooth
  -- path `γ : [0, 1] → M` from `p` to `exp_p v` of `pathELength < r`.
  -- The Gauss-lemma curve-length lower bound (the orthogonal-decomposition
  -- argument inside a normal ball: pull back `γ` through normal
  -- coordinates, decompose the velocity into a radial and orthogonal
  -- part, and integrate) then forces `√(g_p(v,v)) ≤ pathELength γ`.
  -- Combining yields `√(g_p(v,v)) ≤ r` for every such `r`, which by
  -- forall-greater gives `√(g_p(v,v)) ≤ riemannianEDist`.
  --
  -- The curve-length lower bound (Gauss-lemma consequence inside a
  -- normal ball) is the substantive geometric content; isolating it as
  -- a named auxiliary fact captures the precise statement to be filled
  -- once `gauss_lemma_pullback` (still `sorry` above) is available.
  set q := expMap (I := I) g p (show TangentSpace I p from v) with hq_def
  -- The curve-length lower bound inside a normal ball, restated so it
  -- can be quantified over candidate paths produced by the infimum.
  have curveLengthLowerBound :
      ∀ {γ : ℝ → M} {a b : ℝ},
        a ≤ b → γ a = p → γ b = q → CMDiff[Set.Icc a b] 1 γ →
        (∀ t ∈ Set.Icc a b,
          γ t ∈ (NormalCoordinates.normalChartAt (I := I) g p).source) →
        ENNReal.ofReal (Real.sqrt (g.inner p v v)) ≤
          pathELength I γ a b := by
    -- This is the Gauss-lemma length lower bound: orthogonal
    -- decomposition of `γ'` against the radial direction (via
    -- `gauss_lemma_pullback`) plus a `∫|r(t)| ≥ |∫r(t)|`-style
    -- integral inequality.
    sorry
  -- Now combine with the infimum characterisation of `riemannianEDist`.
  refine le_of_forall_gt (fun r hr => ?_)
  -- For every `r > riemannianEDist I p q`, get a path from `p` to `q`
  -- of length `< r`.
  rcases exists_lt_locally_constant_of_riemannianEDist_lt hr
      (a := (0 : ℝ)) (b := (1 : ℝ)) zero_lt_one with
    ⟨γ, hγ0, hγ1, hγ_smooth, hγ_len, _, _⟩
  -- The lower bound holds for this path provided it stays inside the
  -- normal-ball source. Combining this lower bound (via
  -- `curveLengthLowerBound`, isolated above) with `hγ_len < r` yields
  -- `√(g_p(v,v)) < r`, hence the desired forall-greater conclusion.
  -- The "stays inside the normal ball" hypothesis is genuine: a path
  -- exiting the normal ball can have arbitrarily small length while
  -- the endpoints are still inside, by the Gauss-lemma argument it is
  -- handled by truncating at the first exit (so the radial bound
  -- applies on the truncated piece). We state and consume this
  -- in-ball hypothesis as a self-contained intermediate step.
  have hγ_inBall :
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        γ t ∈ (NormalCoordinates.normalChartAt (I := I) g p).source := by
    -- Truncation argument: if `γ` leaves the normal ball, replace it
    -- by its initial in-ball segment plus an angle-correction; the
    -- length only decreases. This is the standard Gauss-lemma
    -- handling of paths that "escape" the normal chart's source.
    sorry
  have hγ1' : γ 1 = q := by simp [hq_def, hγ1]
  have hlb : ENNReal.ofReal (Real.sqrt (g.inner p v v)) ≤
      pathELength I γ (0 : ℝ) 1 :=
    curveLengthLowerBound zero_le_one hγ0 hγ1'
      hγ_smooth.contMDiffOn hγ_inBall
  exact lt_of_le_of_lt hlb hγ_len

end RadialUniqueMinimizer

section LocalRadialIdentification

variable [I.Boundaryless] [CompleteSpace E] [T2Space (TangentBundle I M)]

/-! ## Local radial identification of a minimiser

At any interior parameter of a length-minimising curve, there is a
`δ`-neighbourhood on which the curve, after rescaling, is a monotone
radial geodesic in normal coordinates at `γ(t₀)`. -/

/-- **Local radial identification.** Let `γ : ℝ → M` be a
length-minimising `C¹` curve on `[a, b]`. At every interior parameter
`t₀ ∈ (a, b)` there is a `δ > 0` such that the sub-arc
`γ |[t₀ - δ, t₀ + δ]` is (after monotone rescaling) the radial geodesic
`s ↦ expMap g (γ t₀) (s • v)` in normal coordinates at `γ t₀`, for some
tangent vector `v : TangentSpace I (γ t₀)`. -/
theorem local_radial_identification_of_minimizer
    (g : SmoothRiemannianMetric I M) {γ : ℝ → M} {a b : ℝ}
    (hγ : CMDiff[Icc a b] 1 γ)
    (hmin : riemannianEDist I (γ a) (γ b) = pathELength I γ a b)
    (hab : a ≤ b) {t₀ : ℝ} (ht₀ : t₀ ∈ Ioo a b) :
    ∃ δ : ℝ, 0 < δ ∧ Icc (t₀ - δ) (t₀ + δ) ⊆ Icc a b ∧
      ∃ v : TangentSpace I (γ t₀), ∀ s : ℝ, s ∈ Icc (-δ) δ →
        γ (t₀ + s) = expMap (I := I) g (γ t₀) (s • v) := by
  -- Extract interior-room data from `ht₀ : t₀ ∈ Ioo a b`.
  obtain ⟨ha_lt, hb_lt⟩ := ht₀
  have hδ_left_pos : 0 < t₀ - a := sub_pos.mpr ha_lt
  have hδ_right_pos : 0 < b - t₀ := sub_pos.mpr hb_lt
  -- Choose `δ := min (t₀ - a) (b - t₀) / 2`. Halving gives room on both
  -- sides while keeping `δ > 0`.
  set δ := min (t₀ - a) (b - t₀) / 2 with hδ_def
  have hmin_pos : 0 < min (t₀ - a) (b - t₀) := lt_min hδ_left_pos hδ_right_pos
  have hδ_pos : 0 < δ := by
    rw [hδ_def]; exact half_pos hmin_pos
  -- The interval bound `Icc (t₀ - δ) (t₀ + δ) ⊆ Icc a b`.
  have hδ_le_left : δ ≤ t₀ - a := by
    rw [hδ_def]
    have h₁ : min (t₀ - a) (b - t₀) ≤ t₀ - a := min_le_left _ _
    have h₂ : min (t₀ - a) (b - t₀) / 2 ≤ min (t₀ - a) (b - t₀) := by
      exact half_le_self hmin_pos.le
    exact h₂.trans h₁
  have hδ_le_right : δ ≤ b - t₀ := by
    rw [hδ_def]
    have h₁ : min (t₀ - a) (b - t₀) ≤ b - t₀ := min_le_right _ _
    have h₂ : min (t₀ - a) (b - t₀) / 2 ≤ min (t₀ - a) (b - t₀) := by
      exact half_le_self hmin_pos.le
    exact h₂.trans h₁
  have h_lower : a ≤ t₀ - δ := by linarith
  have h_upper : t₀ + δ ≤ b := by linarith
  have h_subset : Icc (t₀ - δ) (t₀ + δ) ⊆ Icc a b :=
    Icc_subset_Icc h_lower h_upper
  -- The witness `v : TangentSpace I (γ t₀)` and the radial identification
  -- `γ(t₀ + s) = expMap g (γ t₀) (s • v)` for `s ∈ [-δ, δ]` is the
  -- equality case of the Gauss-lemma minimiser identification. The
  -- proof composes `subArc_of_minimizer_is_minimizer` (with `hfin`
  -- derived from `hmin` plus `riemannianEDist ≤ pathELength`) followed
  -- by the equality case of `normalBall_radial_unique_minimizer`
  -- (currently a length lower bound; the equality case sits as a
  -- pending substep upstream). We isolate the existence of the witness
  -- as an intermediate claim consumed below.
  have hwitness :
      ∃ v : TangentSpace I (γ t₀), ∀ s : ℝ, s ∈ Icc (-δ) δ →
        γ (t₀ + s) = expMap (I := I) g (γ t₀) (s • v) := by
    -- The sub-arc on `[t₀ - δ, t₀ + δ]` is itself a minimiser (via
    -- `subArc_of_minimizer_is_minimizer`); inside the normal chart at
    -- `γ t₀` the equality case of `normalBall_radial_unique_minimizer`
    -- forces the sub-arc to coincide with a radial geodesic. The
    -- explicit construction of `v` from this equality case is the
    -- remaining substep, pending the upstream equality-case fill.
    sorry
  -- Package the choice of `δ`, the room subset, and the witness.
  exact ⟨δ, hδ_pos, h_subset, hwitness⟩

end LocalRadialIdentification

section ArclengthReparam

variable [I.Boundaryless] [CompleteSpace E] [T2Space (TangentBundle I M)]

/-! ## Global arclength reparametrisation is a smooth geodesic

Each local piece is a smooth unit-speed radial geodesic; overlap
consistency from `Geodesic/Uniqueness.lean` glues them into a global
smooth geodesic on `(0, L)`. -/

/-- **The arclength reparametrisation of a length-minimiser is a smooth
geodesic.** Given a length-minimising `C¹` curve `γ : [a, b] → M`, there
exist `L ≥ 0` and an arclength reparametrisation `η : ℝ → M` defined on
`[0, L]` such that `η` is a smooth geodesic on the open interval
`(0, L)`. -/
theorem arclength_reparam_is_smooth_geodesic
    (g : SmoothRiemannianMetric I M) {γ : ℝ → M} {a b : ℝ}
    (hγ : CMDiff[Icc a b] 1 γ)
    (hmin : riemannianEDist I (γ a) (γ b) = pathELength I γ a b)
    (hab : a ≤ b) :
    ∃ (L : ℝ) (η : ℝ → M), 0 ≤ L ∧ η 0 = γ a ∧ η L = γ b ∧
      (∀ t ∈ Ioo (0 : ℝ) L,
        ContMDiffAt 𝓘(ℝ, ℝ) I ∞ η t) ∧
      (∀ t ∈ Ioo (0 : ℝ) L,
        DifferentialGeometry.Geometry.Riemannian.Geodesic.IsGeodesicAt
          (I := I) g η t) := by
  -- Split on whether the parameter interval is degenerate.
  rcases eq_or_lt_of_le hab with hab_eq | hab_lt
  · -- Degenerate case `a = b`: the curve has a single point `γ a`. Take
    -- `L = 0` and the constant curve `η = fun _ ↦ γ a`. The two universal
    -- quantifiers range over `Ioo 0 0 = ∅`, hence are vacuous, and the
    -- endpoint equalities reduce to `γ a = γ a` and `γ a = γ b` (the latter
    -- by `hab_eq`).
    refine ⟨0, fun _ : ℝ => γ a, le_refl 0, rfl, ?_, ?_, ?_⟩
    · -- `η L = η 0 = γ a = γ b` since `a = b`.
      simp [hab_eq]
    · intro t ht
      -- `Ioo 0 0 = ∅`, so `t ∈ Ioo 0 0` is a contradiction.
      simp at ht
    · intro t ht
      simp at ht
  · -- Nondegenerate case `a < b`: this is the substantive arclength
    -- reparametrisation, requiring `local_radial_identification_of_minimizer`
    -- (still a `sorry` in this file) plus a global gluing argument via
    -- geodesic uniqueness. The construction is: pull the arclength parameter
    -- `s : [a, b] → [0, L]` through the local radial-geodesic identification
    -- on each `δ`-neighbourhood, then glue using the chart-flow uniqueness
    -- in `Geodesic/Uniqueness.lean`. We leave this branch as a `sorry` until
    -- the local-radial identification lemma is filled and the global
    -- gluing infrastructure is built.
    sorry

end ArclengthReparam

end Riemannian
end Geometry
end DifferentialGeometry
