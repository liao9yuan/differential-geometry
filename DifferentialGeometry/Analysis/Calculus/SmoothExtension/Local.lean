import Mathlib.Analysis.Calculus.BumpFunction.Basic
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations

namespace DifferentialGeometry
namespace Analysis

open Filter Set
open scoped ContDiff

noncomputable section

theorem exists_smooth_extension {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (n : ℕ) (f : E → ℝ)
    (hf : ∃ r : ℝ, 0 < r ∧ ContDiffOn ℝ n f (Metric.ball (0 : E) r)) :
    ∃ g : E → ℝ, ContDiff ℝ n g ∧ g =ᶠ[nhds (0 : E)] f := by
  rcases hf with ⟨r, hr, hfOn⟩
  let φ : ContDiffBump (0 : E) :=
    { rIn := r / 4, rOut := r / 2, rIn_pos := by positivity, rIn_lt_rOut := by linarith }
  let g : E → ℝ := fun x => φ x * f x
  have hφ0 : (φ : E → ℝ) =ᶠ[nhds (0 : E)] (fun _ : E => (1 : ℝ)) := φ.eventuallyEq_one
  have hgEq : g =ᶠ[nhds (0 : E)] f := by
    dsimp [g]
    filter_upwards [hφ0] with x hx
    simp [hx]
  have hgSmooth : ContDiff ℝ n g := by
    have hContDiffOn : ContDiffOn ℝ n g Set.univ := by
      rw [isOpen_univ.contDiffOn_iff]
      intro x hxuniv
      by_cases hx : x ∈ Metric.ball (0 : E) r
      · have hφat : ContDiffAt ℝ n (fun y : E => (φ : E → ℝ) y) x :=
          ((φ.contDiff (n := (n : ℕ∞))) : ContDiff ℝ n (φ : E → ℝ)).contDiffAt
        have hfat : ContDiffAt ℝ n f x := by
          have hmp : ∀ ⦃a : E⦄, a ∈ Metric.ball (0 : E) r → ContDiffAt ℝ n f a :=
            (IsOpen.contDiffOn_iff (Metric.isOpen_ball : IsOpen (Metric.ball (0 : E) r))).mp hfOn
          exact hmp hx
        exact ContDiffAt.mul hφat hfat
      · have hxr : r ≤ dist x 0 := by
          have hnot : ¬ dist 0 x < r := by simpa [Metric.mem_ball] using hx
          have hle : r ≤ dist 0 x := not_lt.mp hnot
          simpa [dist_comm] using hle
        have hdist : φ.rOut ≤ dist x 0 := by
          have hle : φ.rOut ≤ r := by dsimp [φ]; nlinarith [hr]
          exact le_trans hle hxr
        have hzero_near : ∀ᶠ y in nhds x, (φ : E → ℝ) y = 0 := by
          have hε : 0 < dist x 0 - φ.rOut := by
            dsimp [φ]
            nlinarith [hr, hxr]
          have hmem : Metric.ball x ((dist x 0 - φ.rOut) / 2) ∈ nhds x :=
            Metric.ball_mem_nhds x (by positivity)
          filter_upwards [hmem] with y hy
          apply (φ.zero_of_le_dist : φ.rOut ≤ dist y 0 → (φ : E → ℝ) y = 0)
          have hyx : dist y x < (dist x 0 - φ.rOut) / 2 := (Metric.mem_ball.mp hy)
          have htri : dist x 0 ≤ dist x y + dist y 0 := dist_triangle x y 0
          linarith [htri, hyx, dist_comm y x]
        have hgzero : g =ᶠ[nhds x] (fun _ : E => (0 : ℝ)) := by
          dsimp [g]
          filter_upwards [hzero_near] with y hy
          simp [hy]
        exact (contDiffAt_const : ContDiffAt ℝ n (fun _ : E => (0 : ℝ)) x).congr_of_eventuallyEq hgzero
    exact (contDiffOn_univ (𝕜 := ℝ) (n := (n : ℕ∞)) (f := g)).mp hContDiffOn
  exact ⟨g, hgSmooth, hgEq⟩

theorem exists_smooth_extension_smooth {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (f : E → ℝ)
    (hf : ∃ r : ℝ, 0 < r ∧
      ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) f (Metric.ball (0 : E) r)) :
    ∃ g : E → ℝ, ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) g ∧ g =ᶠ[nhds (0 : E)] f := by
  rcases hf with ⟨r, hr, hfOn⟩
  let φ : ContDiffBump (0 : E) :=
    { rIn := r / 4, rOut := r / 2, rIn_pos := by positivity, rIn_lt_rOut := by linarith }
  let g : E → ℝ := fun x => φ x * f x
  have hφ0 : (φ : E → ℝ) =ᶠ[nhds (0 : E)] (fun _ : E => (1 : ℝ)) := φ.eventuallyEq_one
  have hgEq : g =ᶠ[nhds (0 : E)] f := by
    dsimp [g]
    filter_upwards [hφ0] with x hx
    simp [hx]
  have hgSmooth : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) g := by
    have hContDiffOn : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) g Set.univ := by
      rw [isOpen_univ.contDiffOn_iff]
      intro x hxuniv
      by_cases hx : x ∈ Metric.ball (0 : E) r
      · have hφat : ContDiffAt ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (fun y : E => (φ : E → ℝ) y) x :=
          (φ.contDiff (n := (⊤ : ℕ∞))).contDiffAt
        have hfat : ContDiffAt ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) f x := by
          have hmp : ∀ ⦃a : E⦄, a ∈ Metric.ball (0 : E) r →
              ContDiffAt ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) f a :=
            (IsOpen.contDiffOn_iff (Metric.isOpen_ball : IsOpen (Metric.ball (0 : E) r))).mp hfOn
          exact hmp hx
        exact ContDiffAt.mul hφat hfat
      · have hxr : r ≤ dist x 0 := by
          have hnot : ¬ dist 0 x < r := by simpa [Metric.mem_ball] using hx
          have hle : r ≤ dist 0 x := not_lt.mp hnot
          simpa [dist_comm] using hle
        have hdist : φ.rOut ≤ dist x 0 := by
          have hle : φ.rOut ≤ r := by dsimp [φ]; nlinarith [hr]
          exact le_trans hle hxr
        have hzero_near : ∀ᶠ y in nhds x, (φ : E → ℝ) y = 0 := by
          have hε : 0 < dist x 0 - φ.rOut := by
            dsimp [φ]
            nlinarith [hr, hxr]
          have hmem : Metric.ball x ((dist x 0 - φ.rOut) / 2) ∈ nhds x :=
            Metric.ball_mem_nhds x (by positivity)
          filter_upwards [hmem] with y hy
          apply (φ.zero_of_le_dist : φ.rOut ≤ dist y 0 → (φ : E → ℝ) y = 0)
          have hyx : dist y x < (dist x 0 - φ.rOut) / 2 := (Metric.mem_ball.mp hy)
          have htri : dist x 0 ≤ dist x y + dist y 0 := dist_triangle x y 0
          linarith [htri, hyx, dist_comm y x]
        have hgzero : g =ᶠ[nhds x] (fun _ : E => (0 : ℝ)) := by
          dsimp [g]
          filter_upwards [hzero_near] with y hy
          simp [hy]
        exact (contDiffAt_const : ContDiffAt ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
          (fun _ : E => (0 : ℝ)) x).congr_of_eventuallyEq hgzero
    exact (contDiffOn_univ (𝕜 := ℝ) (n := (↑(⊤ : ℕ∞) : WithTop ℕ∞)) (f := g)).mp hContDiffOn
  exact ⟨g, hgSmooth, hgEq⟩

end

end Analysis
end DifferentialGeometry
