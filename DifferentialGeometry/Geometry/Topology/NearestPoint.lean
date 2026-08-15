import Mathlib.Topology.LocallyClosed
import Mathlib.Topology.MetricSpace.HausdorffDistance

open Set Topology

theorem IsLocallyClosed.exists_dist_min {Y : Type*}
    [MetricSpace Y] [ProperSpace Y] {S : Set Y}
    (hS : IsLocallyClosed S) {p : Y} (hp : p ∈ S) :
    ∃ r : ℝ, 0 < r ∧ ∀ {q : Y}, q ∈ Metric.ball p r →
      ∃ z ∈ S, IsMinOn (fun y ↦ dist q y) S z := by
  rcases hS with ⟨O, Z, hO, hZ, rfl⟩
  obtain ⟨ε, hε, hεO⟩ := Metric.isOpen_iff.mp hO p hp.1
  refine ⟨ε / 2, half_pos hε, ?_⟩
  intro q hq
  obtain ⟨z, hzZ, hdist⟩ :=
    hZ.exists_infDist_eq_dist (show Z.Nonempty from ⟨p, hp.2⟩) q
  have hqz : dist q z ≤ dist q p := by
    rw [← hdist]
    exact Metric.infDist_le_dist_of_mem hp.2
  have hzball : z ∈ Metric.ball p ε := by
    rw [Metric.mem_ball]
    calc
      dist z p ≤ dist z q + dist q p := dist_triangle z q p
      _ = dist q z + dist q p := by rw [dist_comm z q]
      _ ≤ dist q p + dist q p := add_le_add hqz le_rfl
      _ < ε := by linarith [Metric.mem_ball.mp hq]
  refine ⟨z, ⟨hεO hzball, hzZ⟩, ?_⟩
  intro y hy
  change dist q z ≤ dist q y
  rw [← hdist]
  exact Metric.infDist_le_dist_of_mem hy.2
