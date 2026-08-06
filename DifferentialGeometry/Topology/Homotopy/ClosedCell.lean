import DifferentialGeometry.Topology.Attachment.Defs
import DifferentialGeometry.Topology.Homotopy.DeformationRetract
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Topology.UnitInterval

namespace DifferentialGeometry.Topology.Homotopy

open ContinuousMap
open unitInterval

def radialStep (n : ℕ) (t : I) (x : ClosedCell n) : ClosedCell n :=
  ⟨(1 - (t : ℝ)) • (x : EuclideanSpace ℝ (Fin n)), by
    have ht₀ : 0 ≤ 1 - (t : ℝ) := unitInterval.one_minus_nonneg t
    have hnorm : ‖(1 - (t : ℝ)) • (x : EuclideanSpace ℝ (Fin n))‖ =
        (1 - (t : ℝ)) * ‖(x : EuclideanSpace ℝ (Fin n))‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht₀]
    rw [hnorm]
    exact mul_le_one₀ (unitInterval.one_minus_le_one t) (norm_nonneg _) x.2⟩

@[simp]
theorem radialStep_zero (n : ℕ) (x : ClosedCell n) : radialStep n 0 x = x := by
  apply Subtype.ext
  simp [radialStep]

@[simp]
theorem radialStep_one (n : ℕ) (x : ClosedCell n) : radialStep n 1 x = closedCellCenter n := by
  apply Subtype.ext
  simp [radialStep, closedCellCenter]

@[simp]
theorem radialStep_center (n : ℕ) (t : I) :
    radialStep n t (closedCellCenter n) = closedCellCenter n := by
  apply Subtype.ext
  simp [radialStep, closedCellCenter]

theorem radialStep_norm (n : ℕ) (t : I) (x : ClosedCell n) :
    ‖(radialStep n t x : EuclideanSpace ℝ (Fin n))‖ =
      (1 - (t : ℝ)) * ‖(x : EuclideanSpace ℝ (Fin n))‖ := by
  simp [radialStep, norm_smul, Real.norm_eq_abs, unitInterval.one_minus_nonneg t]

theorem continuous_radialStep (n : ℕ) :
    Continuous (fun p : I × ClosedCell n => radialStep n p.1 p.2) := by
  exact Continuous.subtype_mk
    (((continuous_const.sub continuous_subtype_val).comp continuous_fst).smul
      (continuous_subtype_val.comp continuous_snd))
    (by
      intro p
      have ht₀ : 0 ≤ 1 - (p.1 : ℝ) := unitInterval.one_minus_nonneg p.1
      have hnorm : ‖(1 - (p.1 : ℝ)) • (p.2 : EuclideanSpace ℝ (Fin n))‖ =
          (1 - (p.1 : ℝ)) * ‖(p.2 : EuclideanSpace ℝ (Fin n))‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht₀]
      simpa using hnorm.trans_le
        (mul_le_one₀ (unitInterval.one_minus_le_one p.1) (norm_nonneg _) p.2.2))

theorem continuous_radialStep_left (n : ℕ) (t : I) : Continuous (radialStep n t) :=
  (continuous_radialStep n).comp (continuous_const.prodMk continuous_id)

def closedCellRetract (n : ℕ) : StrongDeformationRetract ({closedCellCenter n} : Set (ClosedCell n)) where
  retraction := ⟨fun _ => ⟨closedCellCenter n, rfl⟩, continuous_const⟩
  homotopy := {
    toHomotopy := {
      toContinuousMap := ⟨fun p : I × ClosedCell n => radialStep n p.1 p.2, continuous_radialStep n⟩
      map_zero_left := by
        intro x
        simp
      map_one_left := by
        intro x
        simp
    }
    prop' := by
      intro t x hx
      simp at hx
      simp [hx]
  }

@[simp]
theorem closedCellRetract_retraction_apply (n : ℕ) (x : ClosedCell n) :
    ((closedCellRetract n).retraction x : ClosedCell n) = closedCellCenter n := by
  rfl

@[simp]
theorem closedCellRetract_homotopy_apply (n : ℕ) (t : I) (x : ClosedCell n) :
    (closedCellRetract n).homotopy (t, x) = radialStep n t x := by
  rfl

end DifferentialGeometry.Topology.Homotopy
