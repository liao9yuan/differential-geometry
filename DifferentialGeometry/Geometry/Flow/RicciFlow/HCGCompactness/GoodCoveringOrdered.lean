import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.MetricSpace.ProperSpace
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.GoodCovering

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# MSM135 Chapter 4 §2 Step A — faithful (book-ordered) net, abstract core

The book's distance-ordered greedy net (MSM135 L897–955) is built here **abstractly in
a proper metric space** `[MetricSpace M] [ProperSpace M]`, using Mathlib's clean metric
API (`infDist`, `isCompact_closedBall`).  This avoids the `ℝ≥0∞`/`toReal` friction of
the Riemannian emetric.  The greedy minimiser `r^α = d(S^α,O)` is then a *genuine*
theorem (`exists_min_dist_base`, from `ProperSpace`), not a black box.

The single geometric black box — that a complete pointed Riemannian manifold is a proper
metric space under its Riemannian distance (Hopf–Rinow) — is deferred to the
instantiation layer (separate, not in this abstract core).
-/

noncomputable section

namespace DifferentialGeometry
namespace HCGCompactness
namespace OrderedNet

open Metric Set

variable {M : Type*} [MetricSpace M] [ProperSpace M]

/-- The available set (book `S^α`): points whose `λ`-ball `B(x, λ(d(x,O)))` misses the
forbidden open set `U` (the union of previously chosen balls). -/
def availSet (O : M) (lam : ℝ → ℝ) (U : Set M) : Set M :=
  {x | Disjoint (Metric.ball x (lam (dist x O))) U}

/-- `S^α` is closed (book: "balls open ⟹ `S^α` closed").  For nonempty `U`,
`availSet = {x | λ(d(x,O)) ≤ infDist x U}`, which is closed by continuity of both sides. -/
theorem isClosed_availSet (O : M) {lam : ℝ → ℝ} (hlam : Continuous lam) (U : Set M) :
    IsClosed (availSet O lam U) := by
  rcases U.eq_empty_or_nonempty with rfl | hUne
  · have : availSet O lam (∅ : Set M) = Set.univ := by ext x; simp [availSet]
    rw [this]; exact isClosed_univ
  have hset : availSet O lam U = {x | lam (dist x O) ≤ Metric.infDist x U} := by
    ext x
    simp only [availSet, Set.mem_setOf_eq, Set.disjoint_left, Metric.mem_ball]
    constructor
    · intro h
      rw [Metric.le_infDist hUne]
      intro y hy
      rw [dist_comm x y]
      exact not_lt.mp (fun hlt => h hlt hy)
    · intro hle a ha haU
      have hax : Metric.infDist x U ≤ dist a x := by
        rw [dist_comm a x]; exact Metric.infDist_le_dist_of_mem haU
      linarith [le_trans hle hax]
  rw [hset]
  exact isClosed_le (hlam.comp (continuous_id.dist continuous_const))
    (Metric.continuous_infDist_pt U)

/-- In a proper metric space, the distance to a fixed point `O` attains its minimum over
any nonempty closed set `S`.  This is the greedy-net minimiser `r^α = d(S^α,O)`: a
minimising point exists in the compact slice `S ∩ closedBall O (d(s₀,O))`. -/
theorem exists_min_dist_base (O : M) {S : Set M} (hScl : IsClosed S) (hSne : S.Nonempty) :
    ∃ x ∈ S, ∀ y ∈ S, dist x O ≤ dist y O := by
  obtain ⟨s₀, hs₀⟩ := hSne
  have hcpt : IsCompact (S ∩ Metric.closedBall O (dist s₀ O)) :=
    (isCompact_closedBall O (dist s₀ O)).inter_left hScl
  have hne : (S ∩ Metric.closedBall O (dist s₀ O)).Nonempty :=
    ⟨s₀, hs₀, Metric.mem_closedBall.mpr le_rfl⟩
  obtain ⟨x, ⟨hxS, hxball⟩, hxmin⟩ :=
    hcpt.exists_isMinOn hne ((continuous_id.dist continuous_const).continuousOn)
  refine ⟨x, hxS, fun y hyS => ?_⟩
  by_cases hy : y ∈ Metric.closedBall O (dist s₀ O)
  · exact hxmin ⟨hyS, hy⟩
  · rw [Metric.mem_closedBall, not_le] at hy
    have hx_le : dist x O ≤ dist s₀ O := Metric.mem_closedBall.mp hxball
    linarith

/-- The forbidden region after choosing `prior`: the union of their `λ`-balls. -/
def forbidden (O : M) (lam : ℝ → ℝ) (prior : List M) : Set M :=
  ⋃ c ∈ prior, Metric.ball c (lam (dist c O))

open Classical in
/-- The book's greedy ordered net (MSM135 L897–955) as an accumulating list of centers:
`x^0 = O`, each step appends the `d(·,O)`-minimiser of `availSet` over the prior balls,
stopping (the list stays put) once `availSet` is empty. -/
def netList (O : M) (lam : ℝ → ℝ) (hlam : Continuous lam) : ℕ → List M
  | 0 => [O]
  | (α + 1) =>
      if h : (availSet O lam (forbidden O lam (netList O lam hlam α))).Nonempty then
        netList O lam hlam α ++
          [(exists_min_dist_base O
              (isClosed_availSet O hlam (forbidden O lam (netList O lam hlam α))) h).choose]
      else netList O lam hlam α

theorem O_mem_netList (O : M) (lam : ℝ → ℝ) (hlam : Continuous lam) (α : ℕ) :
    O ∈ netList O lam hlam α := by
  induction α with
  | zero => simp [netList]
  | succ α ih =>
      rw [netList]
      split_ifs with h
      · exact List.mem_append_left _ ih
      · exact ih

/-- When `availSet` is nonempty at step `α`, `netList (α+1)` appends a center lying in
`availSet` (its `λ`-ball misses every prior ball) and minimising `d(·,O)` there. -/
theorem netList_succ_spec (O : M) (lam : ℝ → ℝ) (hlam : Continuous lam) (α : ℕ)
    (h : (availSet O lam (forbidden O lam (netList O lam hlam α))).Nonempty) :
    ∃ x, netList O lam hlam (α + 1) = netList O lam hlam α ++ [x] ∧
      x ∈ availSet O lam (forbidden O lam (netList O lam hlam α)) ∧
      (∀ y ∈ availSet O lam (forbidden O lam (netList O lam hlam α)), dist x O ≤ dist y O) := by
  classical
  refine ⟨(exists_min_dist_base O
      (isClosed_availSet O hlam (forbidden O lam (netList O lam hlam α))) h).choose, ?_,
      (exists_min_dist_base O
        (isClosed_availSet O hlam (forbidden O lam (netList O lam hlam α))) h).choose_spec.1,
      (exists_min_dist_base O
        (isClosed_availSet O hlam (forbidden O lam (netList O lam hlam α))) h).choose_spec.2⟩
  rw [netList, dif_pos h]

/-- The `λ`-balls of a list of centers are pairwise disjoint. -/
def ballsDisjoint (O : M) (lam : ℝ → ℝ) (l : List M) : Prop :=
  l.Pairwise fun a b =>
    Disjoint (Metric.ball a (lam (dist a O))) (Metric.ball b (lam (dist b O)))

/-- MSM135 net packing property: the `λ`-balls of the greedy net are pairwise disjoint.
By induction: the appended center lies in `availSet`, so its ball misses every prior ball. -/
theorem netList_ballsDisjoint (O : M) (lam : ℝ → ℝ) (hlam : Continuous lam) (α : ℕ) :
    ballsDisjoint O lam (netList O lam hlam α) := by
  classical
  induction α with
  | zero => exact List.pairwise_singleton _ _
  | succ α ih =>
      by_cases h : (availSet O lam (forbidden O lam (netList O lam hlam α))).Nonempty
      · obtain ⟨x, hxeq, hxavail, _⟩ := netList_succ_spec O lam hlam α h
        rw [ballsDisjoint, hxeq]
        refine List.pairwise_append.mpr ⟨ih, List.pairwise_singleton _ _, ?_⟩
        intro a ha b hb
        rw [List.mem_singleton] at hb
        subst hb
        simp only [availSet, Set.mem_setOf_eq, forbidden,
          Set.disjoint_iUnion_right] at hxavail
        exact (hxavail a ha).symm
      · rw [ballsDisjoint, netList, dif_neg h]; exact ih

@[simp] theorem netList_zero (O : M) (lam : ℝ → ℝ) (hlam : Continuous lam) :
    netList O lam hlam 0 = [O] := rfl

theorem netList_succ_stop (O : M) (lam : ℝ → ℝ) (hlam : Continuous lam) (α : ℕ)
    (h : ¬ (availSet O lam (forbidden O lam (netList O lam hlam α))).Nonempty) :
    netList O lam hlam (α + 1) = netList O lam hlam α := by
  rw [netList, dif_neg h]

theorem mem_netList_succ (O : M) (lam : ℝ → ℝ) (hlam : Continuous lam) (α : ℕ)
    {a : M} (ha : a ∈ netList O lam hlam α) : a ∈ netList O lam hlam (α + 1) := by
  classical
  by_cases h : (availSet O lam (forbidden O lam (netList O lam hlam α))).Nonempty
  · obtain ⟨x, hxeq, -, -⟩ := netList_succ_spec O lam hlam α h
    rw [hxeq]
    exact List.mem_append_left _ ha
  · rw [netList_succ_stop O lam hlam α h]
    exact ha

/-- A point outside `availSet` has its `λ`-ball meeting the `λ`-ball of some listed
center. -/
theorem meets_of_not_avail (O : M) (lam : ℝ → ℝ) {l : List M} {p : M}
    (hp : p ∉ availSet O lam (forbidden O lam l)) :
    ∃ c ∈ l,
      ¬ Disjoint (Metric.ball p (lam (dist p O))) (Metric.ball c (lam (dist c O))) := by
  simp only [availSet, Set.mem_setOf_eq, forbidden, Set.disjoint_iUnion_right,
    not_forall] at hp
  obtain ⟨c, hc, hmeet⟩ := hp
  exact ⟨c, hc, hmeet⟩

/-- If the meeting center is no farther from `O` than `p`, the meeting upgrades to the
book's doubled-ball estimate `dist p c < 2λ(d(c,O))` (using that `λ` is antitone). -/
theorem dist_lt_two_lam {lam : ℝ → ℝ} (hanti : Antitone lam) {O p c : M}
    (hcd : dist c O ≤ dist p O)
    (hmeet : ¬ Disjoint (Metric.ball p (lam (dist p O))) (Metric.ball c (lam (dist c O)))) :
    dist p c < 2 * lam (dist c O) := by
  obtain ⟨q, hqp, hqc⟩ := Set.not_disjoint_iff.mp hmeet
  rw [Metric.mem_ball] at hqp hqc
  have hl : lam (dist p O) ≤ lam (dist c O) := hanti hcd
  have ht : dist p c ≤ dist p q + dist q c := dist_triangle p q c
  rw [dist_comm q p] at hqp
  linarith

/-- MSM135 `lbl387` cover core (book L974–1004): if the greedy net at stage `α` has
stopped (`availSet = ∅`), or has already chosen a center farther from `O` than `p`,
then `p` lies within `2λ(d(c,O))` of some center `c` with `d(c,O) ≤ d(p,O)`.  This is
the pointwise form of the book's doubled-ball cover `B(O,r) ⊆ ⋃ B(x^α, 2λ[r^α])`,
with the exact factor `2`; the book's minimality reductio is the `hxmin`/`hpastα`
case analysis. -/
theorem netList_cover (O : M) {lam : ℝ → ℝ} (hlam : Continuous lam) (hanti : Antitone lam)
    (p : M) :
    ∀ α : ℕ,
      (availSet O lam (forbidden O lam (netList O lam hlam α)) = ∅ ∨
        ∃ c ∈ netList O lam hlam α, dist p O < dist c O) →
      ∃ c ∈ netList O lam hlam α,
        dist c O ≤ dist p O ∧ dist p c < 2 * lam (dist c O) := by
  intro α
  induction α with
  | zero =>
      intro hpast
      rcases hpast with hemp | ⟨c, hc, hlt⟩
      · have hp : p ∉ availSet O lam (forbidden O lam (netList O lam hlam 0)) := by
          simp [hemp]
        obtain ⟨c, hc, hmeet⟩ := meets_of_not_avail O lam hp
        rw [netList_zero, List.mem_singleton] at hc
        subst hc
        have hcd : dist O O ≤ dist p O := by
          rw [dist_self]; exact dist_nonneg
        exact ⟨O, by simp, hcd, dist_lt_two_lam hanti hcd hmeet⟩
      · rw [netList_zero, List.mem_singleton] at hc
        subst hc
        rw [dist_self] at hlt
        exact absurd hlt (not_lt.mpr dist_nonneg)
  | succ α ih =>
      intro hpast
      by_cases hpastα : ∃ c ∈ netList O lam hlam α, dist p O < dist c O
      · obtain ⟨c, hc, hcd, hcb⟩ := ih (Or.inr hpastα)
        exact ⟨c, mem_netList_succ O lam hlam α hc, hcd, hcb⟩
      · push_neg at hpastα
        by_cases h : (availSet O lam (forbidden O lam (netList O lam hlam α))).Nonempty
        · obtain ⟨x, hxeq, hxavail, hxmin⟩ := netList_succ_spec O lam hlam α h
          by_cases hxs : dist p O < dist x O
          · have hp : p ∉ availSet O lam (forbidden O lam (netList O lam hlam α)) :=
              fun hp => absurd (hxmin p hp) (not_le.mpr hxs)
            obtain ⟨c, hc, hmeet⟩ := meets_of_not_avail O lam hp
            have hcd : dist c O ≤ dist p O := hpastα c hc
            refine ⟨c, ?_, hcd, dist_lt_two_lam hanti hcd hmeet⟩
            rw [hxeq]
            exact List.mem_append_left _ hc
          · push_neg at hxs
            rcases hpast with hemp | ⟨c, hc, hlt⟩
            · have hp :
                  p ∉ availSet O lam (forbidden O lam (netList O lam hlam (α + 1))) := by
                simp [hemp]
              obtain ⟨c, hc, hmeet⟩ := meets_of_not_avail O lam hp
              have hcd : dist c O ≤ dist p O := by
                rw [hxeq, List.mem_append] at hc
                rcases hc with hc | hc
                · exact hpastα c hc
                · rw [List.mem_singleton] at hc
                  subst hc
                  exact hxs
              exact ⟨c, hc, hcd, dist_lt_two_lam hanti hcd hmeet⟩
            · rw [hxeq, List.mem_append] at hc
              rcases hc with hc | hc
              · exact absurd hlt (not_lt.mpr (hpastα c hc))
              · rw [List.mem_singleton] at hc
                subst hc
                exact absurd hlt (not_lt.mpr hxs)
        · have hemp := Set.not_nonempty_iff_eq_empty.mp h
          have hp : p ∉ availSet O lam (forbidden O lam (netList O lam hlam α)) := by
            simp [hemp]
          obtain ⟨c, hc, hmeet⟩ := meets_of_not_avail O lam hp
          have hcd : dist c O ≤ dist p O := hpastα c hc
          refine ⟨c, ?_, hcd, dist_lt_two_lam hanti hcd hmeet⟩
          rw [netList_succ_stop O lam hlam α h]
          exact hc

end OrderedNet
end HCGCompactness
end DifferentialGeometry
