import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Topology.DenseEmbedding
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.UniformSpace.CompleteSeparated

/-!
# Continuous extension of a locally Lipschitz map off a dense core

A map defined only on a dense *core* -- smooth tensors inside a completed
Sobolev space, say -- rarely satisfies a global Lipschitz estimate: the honest
estimate is Lipschitz on bounded pieces of the core only, with a constant that
grows with the bound.  Such a map still extends continuously to the ambient
space, because a Lipschitz map is uniformly continuous on each bounded piece
and therefore pushes Cauchy filters to Cauchy filters.

Two faces are provided.

* The *subset* face `cont_extend_lip`: a map on a dense subset `D` of a
  pseudometric space, Lipschitz on every ball about a fixed centre, has a
  continuous `Dense.extend`.
* The *dense range* face `cont_extend_pair`, `extend_pair_apply`,
  `exists_extend_pair`: the core is an arbitrary index type `ι` sent into a
  seminormed space `X` by a map `j` with dense range, and the input estimate is
  the pairwise bound `‖f v - f w‖ ≤ K_R * ‖j v - j w‖` for `‖j v‖, ‖j w‖ ≤ R`.
  This is the face a Sobolev application meets, where the core carries no
  useful topology of its own and the estimate is read on the core index.

`norm_extend_le` transports a pointwise envelope `‖f v‖ ≤ Φ ‖j v‖` from the
core to all of `X`, and `exists_extend_le` bundles it with the extension.
Only continuity of `Φ` is used; monotonicity is not needed.

The conclusion is `Continuous`, never `LipschitzWith`: with an `R`-dependent
constant there is no global Lipschitz bound to extend.  Compare
`DifferentialGeometry.Analysis.Parabolic.QuasiLinear.dense_lipschitz`, which
extends a *global* Lipschitz constant, and `dense_cont_on_balls` in
`TensorMaximalRegularity/TameForcingFixedPoint.lean`, which is the subset face
`cont_extend_lip` stated one layer higher; that copy should eventually be
re-derived from this file.

Mathlib has no form of this statement: its Lipschitz extension theorems
(`LipschitzOnWith.extend_real`, `.extend_pi`, `.extend_lp_infty`,
`.extend_finite_dimension`) extend off an *arbitrary* subset but only into
special codomains, whereas here the codomain is an arbitrary complete normed
space and density does the work.  The engine is Mathlib's
`IsDenseInducing.continuous_extend_of_cauchy`.
-/

noncomputable section

open Filter Set
open scoped NNReal Topology

namespace DifferentialGeometry.Analysis

/-! ## The subset face -/

/-- A map on a subset which is Lipschitz on every ball about a fixed ambient
centre is continuous.  Only local Lipschitz control is used. -/
theorem cont_of_lipBalls {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    {D : Set X} (F : D → Y) (x₀ : X)
    (hball : ∀ R : ℝ, ∃ K : ℝ≥0,
      LipschitzOnWith K F {x : D | dist (x : X) x₀ ≤ R}) :
    Continuous F := by
  rw [continuous_iff_continuousAt]
  intro x
  obtain ⟨K, hK⟩ := hball (dist (x : X) x₀ + 1)
  refine hK.continuousOn.continuousAt ?_
  have hmem : Metric.closedBall x₀ (dist (x : X) x₀ + 1) ∈ 𝓝 (x : X) :=
    Metric.closedBall_mem_nhds_of_mem
      (by simpa only [Metric.mem_ball] using lt_add_one (dist (x : X) x₀))
  exact continuous_subtype_val.continuousAt.preimage_mem_nhds hmem

/-- A map on a dense subset which is Lipschitz on every ball about a fixed
ambient centre has a continuous dense extension.  Global Lipschitz control is
not required, so the conclusion is continuity and not a Lipschitz bound. -/
theorem cont_extend_lip {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    [CompleteSpace Y] [T0Space Y] {D : Set X} (hD : Dense D) (F : D → Y) (x₀ : X)
    (hball : ∀ R : ℝ, ∃ K : ℝ≥0,
      LipschitzOnWith K F {x : D | dist (x : X) x₀ ≤ R}) :
    Continuous (Dense.extend hD F) := by
  apply hD.isDenseInducing_val.continuous_extend_of_cauchy
  intro x
  let l : Filter D := comap ((↑) : D → X) (𝓝 x)
  have hl : Cauchy l :=
    cauchy_nhds.comap'
      (le_of_eq isUniformEmbedding_subtype_val.isUniformInducing.comap_uniformity)
      (hD.comap_val_nhds_neBot x)
  let R : ℝ := dist x x₀ + 1
  let S : Set D := {d | dist (d : X) x₀ ≤ R}
  obtain ⟨K, hK⟩ := hball R
  have hclosed : Metric.closedBall x₀ R ∈ 𝓝 x :=
    Metric.closedBall_mem_nhds_of_mem
      (by simpa only [Metric.mem_ball, R] using lt_add_one (dist x x₀))
  have hlS : l ≤ 𝓟 S := by
    rw [le_principal_iff]
    have hpre : ((↑) : D → X) ⁻¹' Metric.closedBall x₀ R ∈ l :=
      preimage_mem_comap hclosed
    simpa only [S, Metric.mem_closedBall, Set.mem_setOf_eq] using hpre
  exact hl.map_of_le hK.uniformContinuousOn hlS

/-! ## The dense range face -/

/-- A core estimate which is Lipschitz on bounded pieces forces the core map to
be constant on the fibres of `j`, so it descends to the range of `j`. -/
theorem eq_of_lipPair {ι X Y : Type*} [SeminormedAddCommGroup X]
    [NormedAddCommGroup Y] {j : ι → X} {f : ι → Y}
    (hpair : ∀ R : ℝ, ∃ K : ℝ, ∀ v w : ι, ‖j v‖ ≤ R → ‖j w‖ ≤ R →
      ‖f v - f w‖ ≤ K * ‖j v - j w‖)
    {v w : ι} (h : j v = j w) : f v = f w := by
  obtain ⟨K, hK⟩ := hpair ‖j v‖
  have hle := hK v w le_rfl (by rw [← h])
  rw [h, sub_self, norm_zero, mul_zero] at hle
  exact sub_eq_zero.mp (norm_le_zero_iff.mp hle)

/-- The pairwise core estimate, read on the range of `j`, is the ball-Lipschitz
input of `cont_of_lipBalls` and `cont_extend_lip`. -/
private theorem lipBalls_of_pair {ι X Y : Type*} [SeminormedAddCommGroup X]
    [NormedAddCommGroup Y] {j : ι → X} (F : ↥(Set.range j) → Y) (f : ι → Y)
    (hval : ∀ v : ι, F ⟨j v, ⟨v, rfl⟩⟩ = f v)
    (hpair : ∀ R : ℝ, ∃ K : ℝ, ∀ v w : ι, ‖j v‖ ≤ R → ‖j w‖ ≤ R →
      ‖f v - f w‖ ≤ K * ‖j v - j w‖) :
    ∀ R : ℝ, ∃ K : ℝ≥0,
      LipschitzOnWith K F {x : ↥(Set.range j) | dist (x : X) 0 ≤ R} := by
  intro R
  obtain ⟨K, hK⟩ := hpair R
  refine ⟨⟨max K 0, le_max_right _ _⟩, ?_⟩
  rw [lipschitzOnWith_iff_dist_le_mul]
  intro x hx y hy
  obtain ⟨v, hv⟩ := x.2
  obtain ⟨w, hw⟩ := y.2
  have hvR : ‖j v‖ ≤ R := by
    have hx' : dist (x : X) 0 ≤ R := hx
    rwa [dist_zero_right, ← hv] at hx'
  have hwR : ‖j w‖ ≤ R := by
    have hy' : dist (y : X) 0 ≤ R := hy
    rwa [dist_zero_right, ← hw] at hy'
  have hxv : x = ⟨j v, ⟨v, rfl⟩⟩ := Subtype.ext hv.symm
  have hyw : y = ⟨j w, ⟨w, rfl⟩⟩ := Subtype.ext hw.symm
  rw [hxv, hyw, hval, hval]
  simp only [Subtype.dist_eq, dist_eq_norm, NNReal.coe_mk]
  exact (hK v w hvR hwR).trans
    (mul_le_mul_of_nonneg_right (le_max_left K 0) (norm_nonneg _))

/-- **Dense extension of a locally Lipschitz core map.**  Let `j : ι → X` have
dense range in a seminormed space `X`, and let `f : ι → Y` take values in a
complete normed space and satisfy, on each ball `‖j v‖ ≤ R`, a Lipschitz
estimate `‖f v - f w‖ ≤ K_R * ‖j v - j w‖` with an `R`-dependent constant.
Then any map `F` on the range of `j` realizing `f` has a continuous dense
extension to all of `X`.

The extension is Mathlib's `Dense.extend`, so this applies verbatim to an
operator already *defined* as a dense extension of its smooth-core value; see
`extend_pair_apply` for the value on the core and `exists_extend_pair` for the
version that produces the extension itself. -/
theorem cont_extend_pair {ι X Y : Type*} [SeminormedAddCommGroup X]
    [NormedAddCommGroup Y] [CompleteSpace Y] {j : ι → X} (hj : DenseRange j)
    (F : ↥(Set.range j) → Y) (f : ι → Y)
    (hval : ∀ v : ι, F ⟨j v, ⟨v, rfl⟩⟩ = f v)
    (hpair : ∀ R : ℝ, ∃ K : ℝ, ∀ v w : ι, ‖j v‖ ≤ R → ‖j w‖ ≤ R →
      ‖f v - f w‖ ≤ K * ‖j v - j w‖) :
    Continuous (Dense.extend hj F) :=
  cont_extend_lip hj F 0 (lipBalls_of_pair F f hval hpair)

/-- The dense extension of `cont_extend_pair` takes the value `f v` at `j v`.
This is the `_apply` face of `cont_extend_pair`. -/
theorem extend_pair_apply {ι X Y : Type*} [SeminormedAddCommGroup X]
    [NormedAddCommGroup Y] {j : ι → X} (hj : DenseRange j)
    (F : ↥(Set.range j) → Y) (f : ι → Y)
    (hval : ∀ v : ι, F ⟨j v, ⟨v, rfl⟩⟩ = f v)
    (hpair : ∀ R : ℝ, ∃ K : ℝ, ∀ v w : ι, ‖j v‖ ≤ R → ‖j w‖ ≤ R →
      ‖f v - f w‖ ≤ K * ‖j v - j w‖)
    (v : ι) : Dense.extend hj F (j v) = f v :=
  (Dense.extend_eq hj (cont_of_lipBalls F 0 (lipBalls_of_pair F f hval hpair))
    ⟨j v, ⟨v, rfl⟩⟩).trans (hval v)

/-- `cont_extend_pair` in existence form, for a caller who has not already
named the extension: a core map that is Lipschitz on each ball of the core
extends to a continuous map on the ambient space agreeing with it on the
core. -/
theorem exists_extend_pair {ι X Y : Type*} [SeminormedAddCommGroup X]
    [NormedAddCommGroup Y] [CompleteSpace Y] {j : ι → X} (hj : DenseRange j)
    (f : ι → Y)
    (hpair : ∀ R : ℝ, ∃ K : ℝ, ∀ v w : ι, ‖j v‖ ≤ R → ‖j w‖ ≤ R →
      ‖f v - f w‖ ≤ K * ‖j v - j w‖) :
    ∃ F : X → Y, Continuous F ∧ ∀ v : ι, F (j v) = f v := by
  classical
  have hval : ∀ v : ι, (f ∘ Set.rangeSplitting j) ⟨j v, ⟨v, rfl⟩⟩ = f v := by
    intro v
    exact eq_of_lipPair hpair (Set.apply_rangeSplitting j ⟨j v, ⟨v, rfl⟩⟩)
  exact ⟨Dense.extend hj (f ∘ Set.rangeSplitting j),
    cont_extend_pair hj _ f hval hpair,
    fun v => extend_pair_apply hj _ f hval hpair v⟩

/-! ## Norm transport -/

/-- A pointwise envelope on the core passes to a continuous extension: if
`‖f v‖ ≤ Φ ‖j v‖` on the core and `F` is a continuous map agreeing with `f`
there, then `‖F x‖ ≤ Φ ‖x‖` on all of `X`.  Only continuity of `Φ` is used. -/
theorem norm_extend_le {ι X Y : Type*} [SeminormedAddCommGroup X]
    [SeminormedAddCommGroup Y] {j : ι → X} (hj : DenseRange j) {f : ι → Y}
    {F : X → Y} {Φ : ℝ → ℝ} (hF : Continuous F) (hΦ : Continuous Φ)
    (hval : ∀ v : ι, F (j v) = f v) (hbd : ∀ v : ι, ‖f v‖ ≤ Φ ‖j v‖) (x : X) :
    ‖F x‖ ≤ Φ ‖x‖ := by
  refine hj.induction_on x (isClosed_le hF.norm (hΦ.comp continuous_norm)) ?_
  intro v
  rw [hval v]
  exact hbd v

/-- The packaged form consumed downstream: a core map which is Lipschitz on
each ball of the core and obeys a continuous envelope there extends to a
continuous map on the whole space obeying the same envelope everywhere. -/
theorem exists_extend_le {ι X Y : Type*} [SeminormedAddCommGroup X]
    [NormedAddCommGroup Y] [CompleteSpace Y] {j : ι → X} (hj : DenseRange j)
    (f : ι → Y) {Φ : ℝ → ℝ} (hΦ : Continuous Φ)
    (hpair : ∀ R : ℝ, ∃ K : ℝ, ∀ v w : ι, ‖j v‖ ≤ R → ‖j w‖ ≤ R →
      ‖f v - f w‖ ≤ K * ‖j v - j w‖)
    (hbd : ∀ v : ι, ‖f v‖ ≤ Φ ‖j v‖) :
    ∃ F : X → Y, Continuous F ∧ (∀ v : ι, F (j v) = f v) ∧
      ∀ x : X, ‖F x‖ ≤ Φ ‖x‖ := by
  obtain ⟨F, hFc, hFv⟩ := exists_extend_pair hj f hpair
  exact ⟨F, hFc, hFv, fun x => norm_extend_le hj hFc hΦ hFv hbd x⟩

end DifferentialGeometry.Analysis

end
