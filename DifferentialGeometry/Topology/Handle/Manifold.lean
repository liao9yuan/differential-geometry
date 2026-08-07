import DifferentialGeometry.Topology.Attachment.Defs
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Geometry.Manifold.IsManifold.Basic

namespace DifferentialGeometry.Topology.Handle

open scoped Manifold Topology

noncomputable section

noncomputable def closedCellPermute {n : ℕ} (e : Fin n ≃ Fin n) :
    EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n) :=
  (EuclideanSpace.basisFun (Fin n) ℝ).reindex e |>.repr

theorem closedCellPermute_apply {n : ℕ} (e : Fin n ≃ Fin n) (x : EuclideanSpace ℝ (Fin n))
    (j : Fin n) : closedCellPermute e x j = x (e.symm j) := by
  change ((EuclideanSpace.basisFun (Fin n) ℝ).reindex e).repr x j = x (e.symm j)
  rw [OrthonormalBasis.repr_apply_apply]
  rw [OrthonormalBasis.reindex_apply]
  exact EuclideanSpace.basisFun_inner (Fin n) ℝ x (e.symm j)

theorem closedCellPermute_norm {n : ℕ} (e : Fin n ≃ Fin n) (x : EuclideanSpace ℝ (Fin n)) :
    ‖closedCellPermute e x‖ = ‖x‖ := by
  exact (closedCellPermute e).norm_map x

theorem closedCellPermute_zero {n : ℕ} (e : Fin n ≃ Fin n) :
    closedCellPermute e 0 = 0 := by
  ext j
  simp

theorem closedCellPermute_inv {n : ℕ} (e : Fin n ≃ Fin n) (x : EuclideanSpace ℝ (Fin n)) :
    closedCellPermute e.symm (closedCellPermute e x) = x := by
  ext j
  rw [closedCellPermute_apply, closedCellPermute_apply]
  simp

theorem closedCellPermute_inv' {n : ℕ} (e : Fin n ≃ Fin n) (x : EuclideanSpace ℝ (Fin n)) :
    closedCellPermute e (closedCellPermute e.symm x) = x := by
  simpa [Equiv.symm_symm] using closedCellPermute_inv e.symm x

theorem closedCellPermute_coord_ne_zero {n : ℕ} (e : Fin (n + 1) ≃ Fin (n + 1))
    {s : ℝ} {x : EuclideanSpace ℝ (Fin (n + 1))}
    (hx : 0 < s * (closedCellPermute e x) (0)) :
    (closedCellPermute e x) (0) ≠ 0 := by
  intro h0
  rw [h0] at hx
  have : s * 0 = (0 : ℝ) := by ring
  rw [this] at hx
  norm_num at hx

theorem closedCellCoord_norm_le_norm {n : ℕ} (x : EuclideanSpace ℝ (Fin (n + 1))) :
    ‖x (0)‖ ≤ ‖x‖ :=
  PiLp.norm_apply_le x (0)

theorem closedCellPermute_symm_eq {n : ℕ} (e : Fin n ≃ Fin n) :
    (closedCellPermute e).symm = closedCellPermute e.symm := by
  apply LinearIsometryEquiv.ext
  intro x
  apply (closedCellPermute e).injective
  calc
    (closedCellPermute e) ((closedCellPermute e).symm x) = x :=
      (closedCellPermute e).apply_symm_apply x
    _ = (closedCellPermute e) (closedCellPermute e.symm x) :=
      by simpa using (closedCellPermute_inv e.symm x).symm

theorem closedCellPermute_symm_apply {n : ℕ} (e : Fin n ≃ Fin n) (x : EuclideanSpace ℝ (Fin n))
    (j : Fin n) : (closedCellPermute e).symm x j = x (e j) := by
  rw [closedCellPermute_symm_eq e]
  rw [closedCellPermute_apply]
  simp [Equiv.symm_symm]

theorem closedCellPermute_swap_zero {n : ℕ} [NeZero n] (i : Fin n)
    (x : EuclideanSpace ℝ (Fin n)) :
    closedCellPermute (Equiv.swap i ⟨0, NeZero.pos n⟩) x ⟨0, NeZero.pos n⟩ = x i := by
  rw [closedCellPermute_apply]
  change x ((Equiv.swap i ⟨0, NeZero.pos n⟩).symm ⟨0, NeZero.pos n⟩) = x i
  rw [Equiv.symm_swap]
  simp

noncomputable def closedCellTail (n : ℕ) (x : EuclideanSpace ℝ (Fin (n + 1))) :
    EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 fun j : Fin n => x (Fin.succ j)

theorem closedCellTail_apply (n : ℕ) (x : EuclideanSpace ℝ (Fin (n + 1))) (j : Fin n) :
    closedCellTail n x j = x (Fin.succ j) := rfl

noncomputable def closedCellModelTail (n : ℕ) (y : EuclideanSpace ℝ (Fin (n + 1))) :
    EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 fun j : Fin n => y (Fin.succ j)

theorem closedCellModelTail_apply (n : ℕ) (y : EuclideanSpace ℝ (Fin (n + 1))) (j : Fin n) :
    closedCellModelTail n y j = y (Fin.succ j) := rfl

theorem closedCellTail_norm_sq (n : ℕ) (x : EuclideanSpace ℝ (Fin (n + 1))) :
    ‖closedCellTail n x‖ ^ 2 = ∑ j : Fin n, (x (Fin.succ j)) ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp [closedCellTail]

noncomputable def closedCellCons (n : ℕ) (t : ℝ) (v : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin (n + 1)) :=
  WithLp.toLp 2 (fun j : Fin (n + 1) => Fin.cases t (fun j' : Fin n => v j') j)

theorem closedCellCons_apply_zero (n : ℕ) (t : ℝ) (v : EuclideanSpace ℝ (Fin n)) :
    closedCellCons n t v (0) = t := by
  simp [closedCellCons]

theorem closedCellCons_apply_succ (n : ℕ) (t : ℝ) (v : EuclideanSpace ℝ (Fin n))
    (j : Fin n) : closedCellCons n t v (Fin.succ j) = v j := by
  simp [closedCellCons]

theorem closedCellCons_norm_sq (n : ℕ) (t : ℝ) (v : EuclideanSpace ℝ (Fin n)) :
    ‖closedCellCons n t v‖ ^ 2 = t ^ 2 + ‖v‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_succ]
  simp only [closedCellCons, Fin.cases_zero, Fin.cases_succ]
  rw [EuclideanSpace.real_norm_sq_eq]

theorem closedCellCons_tail (n : ℕ) (t : ℝ) (v : EuclideanSpace ℝ (Fin n)) :
    closedCellTail n (closedCellCons n t v) = v := by
  ext j
  rw [closedCellTail_apply, closedCellCons_apply_succ]

theorem closedCellCons_eq_cons (n : ℕ) (t : ℝ) (v : EuclideanSpace ℝ (Fin n)) :
    closedCellCons n t v = WithLp.toLp 2 (Fin.cons t (WithLp.ofLp v)) := by
  ext j
  cases j using Fin.cases with
  | zero => simp [closedCellCons]
  | succ j' => simp [closedCellCons]

def closedCellSign (σ : Bool) : ℝ := if σ then 1 else -1

theorem closedCellSign_ne_zero (σ : Bool) : closedCellSign σ ≠ 0 := by
  cases σ <;> norm_num [closedCellSign]

theorem closedCellSign_sq (σ : Bool) : closedCellSign σ ^ 2 = 1 := by
  cases σ <;> norm_num [closedCellSign, pow_two]

theorem closedCellSign_mul_self (σ : Bool) : closedCellSign σ * closedCellSign σ = 1 := by
  cases σ <;> norm_num [closedCellSign]

noncomputable def closedCellShiftSucc (n : ℕ) (c : ℝ) (x : EuclideanSpace ℝ (Fin (n + 1))) :
    EuclideanSpace ℝ (Fin (n + 1)) :=
  WithLp.toLp 2 (fun j : Fin (n + 1) =>
    if _ : j = (0) then x (0) + c else x j)

theorem closedCellShiftSucc_apply_zero (n : ℕ) (c : ℝ) (x : EuclideanSpace ℝ (Fin (n + 1))) :
    closedCellShiftSucc n c x (0) = x (0) + c := by
  simp [closedCellShiftSucc]

theorem closedCellShiftSucc_apply_succ (n : ℕ) (c : ℝ) (x : EuclideanSpace ℝ (Fin (n + 1)))
    (j : Fin n) : closedCellShiftSucc n c x (Fin.succ j) = x (Fin.succ j) := by
  simp [closedCellShiftSucc, Fin.succ_ne_zero]

theorem closedCellShiftSucc_apply_of_ne {n : ℕ} (c : ℝ) (x : EuclideanSpace ℝ (Fin (n + 1)))
    {j : Fin (n + 1)} (hj : j ≠ (0)) :
    closedCellShiftSucc n c x j = x j := by
  dsimp [closedCellShiftSucc]
  change (if _ : j = (0) then x (0) + c else x j) = x j
  exact dif_neg hj

theorem closedCellShiftSucc_eq_add {n : ℕ} (c : ℝ) (x : EuclideanSpace ℝ (Fin (n + 1))) :
    closedCellShiftSucc n c x = x + c • (EuclideanSpace.basisFun (Fin (n + 1)) ℝ
      (0)) := by
  ext j
  by_cases hj : j = (0)
  · subst j
    rw [closedCellShiftSucc_apply_zero]
    simp [EuclideanSpace.basisFun_apply]
  · have hj' : j ≠ (0) := hj
    rw [closedCellShiftSucc_apply_of_ne c x hj']
    change x j = x j + c * ((EuclideanSpace.basisFun (Fin (n + 1)) ℝ (0)) j)
    rw [EuclideanSpace.basisFun_apply, PiLp.single_apply]
    rw [if_neg hj']
    ring

theorem closedCellShiftSucc_neg (n : ℕ) (c : ℝ) (x : EuclideanSpace ℝ (Fin (n + 1))) :
    closedCellShiftSucc n (-c) (closedCellShiftSucc n c x) = x := by
  ext j
  by_cases hj : j = (0)
  · subst j
    rw [closedCellShiftSucc_apply_zero, closedCellShiftSucc_apply_zero]
    ring
  · have hnot : j ≠ (0) := hj
    rw [closedCellShiftSucc_apply_of_ne (-c) (closedCellShiftSucc n c x) hnot]
    exact closedCellShiftSucc_apply_of_ne c x hnot

theorem closedCellShiftSucc_neg' (n : ℕ) (c : ℝ) (x : EuclideanSpace ℝ (Fin (n + 1))) :
    closedCellShiftSucc n c (closedCellShiftSucc n (-c) x) = x := by
  ext j
  by_cases hj : j = (0)
  · subst j
    rw [closedCellShiftSucc_apply_zero, closedCellShiftSucc_apply_zero]
    ring
  · have hnot : j ≠ (0) := hj
    rw [closedCellShiftSucc_apply_of_ne c (closedCellShiftSucc n (-c) x) hnot]
    exact closedCellShiftSucc_apply_of_ne (-c) x hnot

noncomputable def closedCellProject {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) : ClosedCell n :=
  if h : ‖x‖ ≤ 1 then ⟨x, h⟩ else ⟨(1 / ‖x‖) • x, by
    have hxpos : 0 < ‖x‖ := lt_of_not_ge (fun hle0 : ‖x‖ ≤ 0 => h (le_trans hle0 (by norm_num)))
    have hnorm : ‖(1 / ‖x‖) • x‖ = 1 := by
      rw [norm_smul]
      rw [Real.norm_eq_abs, abs_of_nonneg (one_div_nonneg.mpr (le_of_lt hxpos))]
      rw [div_eq_mul_inv]
      rw [one_mul]
      exact inv_mul_cancel₀ (ne_of_gt hxpos)
    rw [hnorm]⟩

theorem closedCellProject_of_mem {n : ℕ} {x : EuclideanSpace ℝ (Fin n)} (hx : ‖x‖ ≤ 1) :
    closedCellProject x = ⟨x, hx⟩ := by
  simp [closedCellProject, hx]

noncomputable def closedCellInteriorChartValue (n : ℕ) (x : ClosedCell (n + 1)) :
    EuclideanHalfSpace (n + 1) :=
  ⟨closedCellShiftSucc n 1 x.1, by
    rw [closedCellShiftSucc_apply_zero]
    have hle : ‖x.1 (0)‖ ≤ 1 :=
      le_trans (PiLp.norm_apply_le x.1 (0)) (by
        change ‖x.1‖ ≤ 1
        exact x.2)
    have hlt : -1 ≤ x.1 (0) := (abs_le.mp (by simpa using hle)).1
    linarith⟩

theorem closedCellInteriorChartValue_coe (n : ℕ) (x : ClosedCell (n + 1)) :
    (closedCellInteriorChartValue n x).1 =
      closedCellShiftSucc n 1 x.1 := rfl

theorem closedCellSplit_norm_sq (n : ℕ) (x : EuclideanSpace ℝ (Fin (n + 1))) :
    ‖x‖ ^ 2 = (x (0)) ^ 2 + ‖closedCellTail n x‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_succ]
  have htail : ‖closedCellTail n x‖ ^ 2 = ∑ j : Fin n, (x (Fin.succ j)) ^ 2 := by
    simpa [closedCellTail] using (EuclideanSpace.real_norm_sq_eq (closedCellTail n x))
  rw [htail]

theorem closedCellSign_mul_abs {σ : Bool} {a : ℝ} (h : 0 < closedCellSign σ * a) :
    closedCellSign σ * |a| = a := by
  cases σ with
  | true =>
      have ha : 0 < a := by simpa [closedCellSign] using h
      have hsign : closedCellSign true = (1 : ℝ) := rfl
      rw [hsign, abs_of_pos ha, one_mul]
  | false =>
      have hneg : 0 < -a := by simpa [closedCellSign] using h
      have ha : a < 0 := by linarith
      have hsign : closedCellSign false = (-1 : ℝ) := rfl
      rw [hsign, abs_of_neg ha]
      ring

noncomputable def closedCellInteriorChart (n : ℕ) :
    OpenPartialHomeomorph (ClosedCell (n + 1)) (EuclideanHalfSpace (n + 1)) where
  source := {x : ClosedCell (n + 1) | ‖x.1‖ < 1}
  target := {y : EuclideanHalfSpace (n + 1) | ‖closedCellShiftSucc n (-1) y.1‖ < 1}
  toFun := closedCellInteriorChartValue n
  invFun := fun y => closedCellProject (closedCellShiftSucc n (-1) y.1)
  map_source' := by
    intro x hx
    change ‖closedCellShiftSucc n (-1) (closedCellInteriorChartValue n x).1‖ < 1
    rw [closedCellInteriorChartValue_coe]
    rw [closedCellShiftSucc_neg n 1 x.1]
    exact hx
  map_target' := by
    intro y hy
    change ‖(closedCellProject (closedCellShiftSucc n (-1) y.1)).1‖ < 1
    rw [closedCellProject_of_mem (le_of_lt hy)]
    exact hy
  left_inv' := by
    intro x hx
    apply Subtype.ext
    change (closedCellProject (closedCellShiftSucc n (-1) (closedCellInteriorChartValue n x).1)).1 = x.1
    rw [closedCellInteriorChartValue_coe]
    rw [closedCellShiftSucc_neg n 1 x.1]
    rw [closedCellProject_of_mem (le_of_lt hx)]
  right_inv' := by
    intro y hy
    apply Subtype.ext
    change (closedCellInteriorChartValue n (closedCellProject (closedCellShiftSucc n (-1) y.1))).1 = y.1
    rw [closedCellInteriorChartValue_coe]
    rw [closedCellProject_of_mem (le_of_lt hy)]
    rw [closedCellShiftSucc_neg' n 1 y.1]
  open_source := by
    have hcont : Continuous (fun x : ClosedCell (n + 1) => ‖x.1‖) :=
      continuous_norm.comp continuous_subtype_val
    exact (isOpen_Iio : IsOpen (Set.Iio (1 : ℝ))).preimage hcont
  open_target := by
    have hcont : Continuous (fun y : EuclideanHalfSpace (n + 1) =>
        ‖closedCellShiftSucc n (-1) y.1‖) := by
      have hlin : Continuous (fun y : EuclideanSpace ℝ (Fin (n + 1)) =>
          closedCellShiftSucc n (-1) y) := by
        have hc : Continuous (fun y : EuclideanSpace ℝ (Fin (n + 1)) =>
            y + (-1 : ℝ) • (EuclideanSpace.basisFun (Fin (n + 1)) ℝ (0))) :=
          continuous_id.add continuous_const
        simpa [closedCellShiftSucc_eq_add] using hc
      exact continuous_norm.comp (hlin.comp continuous_subtype_val)
    exact (isOpen_Iio : IsOpen (Set.Iio (1 : ℝ))).preimage hcont
  continuousOn_toFun := by
    have hcont : Continuous (fun x : ClosedCell (n + 1) =>
        closedCellShiftSucc n 1 x.1) := by
      have hc : Continuous (fun x : EuclideanSpace ℝ (Fin (n + 1)) =>
          x + (1 : ℝ) • (EuclideanSpace.basisFun (Fin (n + 1)) ℝ (0))) :=
        continuous_id.add continuous_const
      have hlin' : Continuous (fun x : EuclideanSpace ℝ (Fin (n + 1)) =>
          closedCellShiftSucc n 1 x) := by
        simpa [closedCellShiftSucc_eq_add] using hc
      exact hlin'.comp continuous_subtype_val
    exact (Continuous.subtype_mk hcont (fun x => by
      change 0 ≤ (closedCellShiftSucc n 1 x.1)
        (0)
      rw [closedCellShiftSucc_apply_zero]
      have hle : ‖x.1 (0)‖ ≤ 1 :=
        le_trans (PiLp.norm_apply_le x.1
          (0)) (by
            change ‖x.1‖ ≤ 1
            exact x.2)
      have hlt : -1 ≤ x.1 (0) :=
        (abs_le.mp (by simpa using hle)).1
      linarith)).continuousOn
  continuousOn_invFun := by
    refine continuousOn_iff_continuous_restrict.mpr ?_
    have hlin : Continuous (fun y : EuclideanSpace ℝ (Fin (n + 1)) =>
        closedCellShiftSucc n (-1) y) := by
      have hlin : Continuous (fun y : EuclideanSpace ℝ (Fin (n + 1)) =>
          y + (-1 : ℝ) • (EuclideanSpace.basisFun (Fin (n + 1)) ℝ (0))) :=
        continuous_id.add continuous_const
      simpa [closedCellShiftSucc_eq_add] using hlin
    have hlin' : Continuous (fun y : {y : EuclideanHalfSpace (n + 1) |
        ‖closedCellShiftSucc n (-1) y.1‖ < 1} =>
        closedCellShiftSucc n (-1) (Subtype.val (Subtype.val y))) :=
      hlin.comp (continuous_subtype_val.comp continuous_subtype_val)
    exact Continuous.congr (Continuous.subtype_mk hlin' (fun y => by
      exact le_of_lt y.2)) (fun y => by
      change ⟨closedCellShiftSucc n (-1) (Subtype.val (Subtype.val y)), le_of_lt y.2⟩ =
        closedCellProject (closedCellShiftSucc n (-1) (Subtype.val (Subtype.val y)))
      exact (closedCellProject_of_mem (le_of_lt y.2)).symm)

theorem closedCellCons_split (n : ℕ) (x : EuclideanSpace ℝ (Fin (n + 1))) :
    closedCellCons n (x (0)) (closedCellTail n x) = x := by
  ext j
  refine Fin.cases ?zero ?succ j
  · simp [closedCellCons]
  · intro j'
    rw [closedCellCons_apply_succ]
    rfl


noncomputable def closedCellBoundaryChartValue (n : ℕ) (e : Fin (n + 1) ≃ Fin (n + 1))
    (x : ClosedCell (n + 1)) : EuclideanHalfSpace (n + 1) :=
  ⟨closedCellCons n (1 - ‖x.1‖ ^ 2) (closedCellTail n (closedCellPermute e x.1)), by
    rw [closedCellCons_apply_zero]
    have hsq : ‖x.1‖ ^ 2 ≤ 1 := by
      nlinarith [norm_nonneg x.1, x.2]
    linarith⟩

theorem closedCellBoundaryChartValue_coe (n : ℕ) (e : Fin (n + 1) ≃ Fin (n + 1))
    (x : ClosedCell (n + 1)) :
    (closedCellBoundaryChartValue n e x).1 =
      closedCellCons n (1 - ‖x.1‖ ^ 2) (closedCellTail n (closedCellPermute e x.1)) := rfl

noncomputable def closedCellBoundaryInvValue (n : ℕ) (e : Fin (n + 1) ≃ Fin (n + 1))
    (s : ℝ) (y : EuclideanSpace ℝ (Fin (n + 1))) : EuclideanSpace ℝ (Fin (n + 1)) :=
  closedCellPermute e.symm (closedCellCons n
    (s * Real.sqrt (1 - y (0) - ‖closedCellTail n y‖ ^ 2)) (closedCellTail n y))

theorem closedCellBoundaryInvValue_norm_sq {n : ℕ} (e : Fin (n + 1) ≃ Fin (n + 1))
    {s : ℝ} (hs : s ^ 2 = 1) (y : EuclideanSpace ℝ (Fin (n + 1)))
    (hpos : 0 < 1 - y (0) - ‖closedCellTail n y‖ ^ 2) :
    ‖closedCellBoundaryInvValue n e s y‖ ^ 2 = 1 - y (0) := by
  dsimp [closedCellBoundaryInvValue]
  rw [closedCellPermute_norm]
  rw [closedCellCons_norm_sq]
  have hsqrt : (s * Real.sqrt (1 - y (0) - ‖closedCellTail n y‖ ^ 2)) ^ 2 =
      1 - y (0) - ‖closedCellTail n y‖ ^ 2 := by
    rw [mul_pow, hs, one_mul]
    rw [Real.sq_sqrt (le_of_lt hpos)]
  change (s * Real.sqrt (1 - y (0) - ‖closedCellTail n y‖ ^ 2)) ^ 2 +
      ‖closedCellTail n y‖ ^ 2 = 1 - y (0)
  rw [hsqrt]
  ring

theorem closedCellBoundaryInvValue_norm_le_one {n : ℕ} (e : Fin (n + 1) ≃ Fin (n + 1))
    {s : ℝ} (hs : s ^ 2 = 1) (y : EuclideanSpace ℝ (Fin (n + 1)))
    (hpos : 0 < 1 - y (0) - ‖closedCellTail n y‖ ^ 2)
    (ht0 : 0 ≤ y (0)) :
    ‖closedCellBoundaryInvValue n e s y‖ ≤ 1 := by
  have hsq := closedCellBoundaryInvValue_norm_sq e hs y hpos
  have hle : ‖closedCellBoundaryInvValue n e s y‖ ^ 2 ≤ 1 ^ 2 := by
    rw [hsq]
    nlinarith
  exact (abs_le.mp (by simpa using sq_le_sq.mp hle)).2

noncomputable def closedCellBoundaryChart (n : ℕ) (i : Fin (n + 1)) (σ : Bool) :
    OpenPartialHomeomorph (ClosedCell (n + 1)) (EuclideanHalfSpace (n + 1)) := by
  let e : Fin (n + 1) ≃ Fin (n + 1) := Equiv.swap i (0)
  let s : ℝ := closedCellSign σ
  have hs : s ^ 2 = 1 := by
    dsimp [s]
    exact closedCellSign_sq σ
  have hss : s * s = 1 := by
    dsimp [s]
    exact closedCellSign_mul_self σ
  refine
    { source := {x : ClosedCell (n + 1) |
        0 < s * (closedCellPermute e x.1) (0)}
      target := {y : EuclideanHalfSpace (n + 1) |
        y.1 (0) < 1 ∧
          0 < 1 - y.1 (0) - ‖closedCellTail n y.1‖ ^ 2}
      toFun := closedCellBoundaryChartValue n e
      invFun := fun y => closedCellProject (closedCellBoundaryInvValue n e s y.1)
      map_source' := ?_
      map_target' := ?_
      left_inv' := ?_
      right_inv' := ?_
      open_source := ?_
      open_target := ?_
      continuousOn_toFun := ?_
      continuousOn_invFun := ?_ }
  · intro x hx
    change 0 < s * (closedCellPermute e x.1) (0) at hx
    change (closedCellBoundaryChartValue n e x).1 (0) < 1 ∧
      0 < 1 - (closedCellBoundaryChartValue n e x).1 (0) -
        ‖closedCellTail n (closedCellBoundaryChartValue n e x).1‖ ^ 2
    rw [closedCellBoundaryChartValue_coe]
    rw [closedCellCons_apply_zero, closedCellCons_tail]
    constructor
    · have hx0 : (closedCellPermute e x.1) (0) ≠ 0 :=
        closedCellPermute_coord_ne_zero e hx
      have hxpos : 0 < ‖x.1‖ := by
        have hle : ‖(closedCellPermute e x.1) (0)‖ ≤ ‖x.1‖ := by
          calc
            ‖(closedCellPermute e x.1) (0)‖ ≤ ‖closedCellPermute e x.1‖ :=
              closedCellCoord_norm_le_norm (closedCellPermute e x.1)
            _ = ‖x.1‖ := closedCellPermute_norm e x.1
        have habs : 0 < |(closedCellPermute e x.1) (0)| := abs_pos.mpr hx0
        have hpos : 0 < ‖(closedCellPermute e x.1) (0)‖ := by
          simpa using habs
        exact lt_of_lt_of_le hpos hle
      have hsq : 0 < ‖x.1‖ ^ 2 := by positivity
      linarith
    · have hx0 : (closedCellPermute e x.1) (0) ≠ 0 :=
        closedCellPermute_coord_ne_zero e hx
      have hsplit := closedCellSplit_norm_sq n (closedCellPermute e x.1)
      rw [closedCellPermute_norm] at hsplit
      have hmain : 1 - (1 - ‖x.1‖ ^ 2) - ‖closedCellTail n (closedCellPermute e x.1)‖ ^ 2 =
          ((closedCellPermute e x.1) (0)) ^ 2 := by
        have hring : 1 - (1 - ‖x.1‖ ^ 2) - ‖closedCellTail n (closedCellPermute e x.1)‖ ^ 2 =
            ‖x.1‖ ^ 2 - ‖closedCellTail n (closedCellPermute e x.1)‖ ^ 2 := by ring
        rw [hring]
        rw [hsplit]
        ring
      rw [hmain]
      exact sq_pos_of_ne_zero hx0
  · intro y hy
    change 0 < s * (closedCellPermute e (closedCellProject
        (closedCellBoundaryInvValue n e s y.1)).1) (0)
    have hzle : ‖closedCellBoundaryInvValue n e s y.1‖ ≤ 1 :=
      closedCellBoundaryInvValue_norm_le_one e hs y.1 hy.2 y.2
    rw [closedCellProject_of_mem hzle]
    change 0 < s * (closedCellPermute e (closedCellBoundaryInvValue n e s y.1))
      (0)
    dsimp [closedCellBoundaryInvValue]
    rw [closedCellPermute_inv']
    rw [closedCellCons_apply_zero]
    change 0 < s * (s * Real.sqrt (1 - y.1 (0) - ‖closedCellTail n y.1‖ ^ 2))
    rw [← mul_assoc, hss, one_mul]
    exact Real.sqrt_pos.2 hy.2
  · intro x hx
    change 0 < s * (closedCellPermute e x.1) (0) at hx
    apply Subtype.ext
    change (closedCellProject (closedCellBoundaryInvValue n e s
        (closedCellBoundaryChartValue n e x).1)).1 = x.1
    have hzle : ‖closedCellBoundaryInvValue n e s (closedCellBoundaryChartValue n e x).1‖ ≤ 1 := by
      rw [closedCellBoundaryChartValue_coe]
      dsimp [closedCellBoundaryInvValue]
      rw [closedCellPermute_norm]
      rw [closedCellCons_apply_zero, closedCellCons_tail]
      have hsq : ‖closedCellCons n (s * Real.sqrt (1 - (1 - ‖x.1‖ ^ 2) -
          ‖closedCellTail n (closedCellPermute e x.1)‖ ^ 2))
          (closedCellTail n (closedCellPermute e x.1))‖ ^ 2 ≤ 1 := by
        rw [closedCellCons_norm_sq]
        have hx0 : (closedCellPermute e x.1) (0) ≠ 0 :=
          closedCellPermute_coord_ne_zero e hx
        have hsplit := closedCellSplit_norm_sq n (closedCellPermute e x.1)
        rw [closedCellPermute_norm] at hsplit
        have hmain : 1 - (1 - ‖x.1‖ ^ 2) - ‖closedCellTail n (closedCellPermute e x.1)‖ ^ 2 =
            ((closedCellPermute e x.1) (0)) ^ 2 := by
          have hring : 1 - (1 - ‖x.1‖ ^ 2) - ‖closedCellTail n (closedCellPermute e x.1)‖ ^ 2 =
              ‖x.1‖ ^ 2 - ‖closedCellTail n (closedCellPermute e x.1)‖ ^ 2 := by ring
          rw [hring]
          rw [hsplit]
          ring
        have hsqrt : (s * Real.sqrt (1 - (1 - ‖x.1‖ ^ 2) -
            ‖closedCellTail n (closedCellPermute e x.1)‖ ^ 2)) ^ 2 =
            1 - (1 - ‖x.1‖ ^ 2) - ‖closedCellTail n (closedCellPermute e x.1)‖ ^ 2 := by
          rw [mul_pow, hs, one_mul]
          rw [Real.sq_sqrt (le_of_lt (by rw [hmain]; exact sq_pos_of_ne_zero hx0))]
        change (s * Real.sqrt (1 - (1 - ‖x.1‖ ^ 2) -
            ‖closedCellTail n (closedCellPermute e x.1)‖ ^ 2)) ^ 2 +
            ‖closedCellTail n (closedCellPermute e x.1)‖ ^ 2 ≤ 1
        rw [hsqrt]
        nlinarith [norm_nonneg x.1, x.2]
      have hzn : 0 ≤ ‖closedCellBoundaryInvValue n e s (closedCellBoundaryChartValue n e x).1‖ := norm_nonneg _
      nlinarith
    rw [closedCellProject_of_mem hzle]
    change (closedCellBoundaryInvValue n e s (closedCellBoundaryChartValue n e x).1) = x.1
    rw [closedCellBoundaryChartValue_coe]
    dsimp [closedCellBoundaryInvValue]
    rw [closedCellCons_apply_zero, closedCellCons_tail]
    have hx0 : (closedCellPermute e x.1) (0) ≠ 0 :=
      closedCellPermute_coord_ne_zero e hx
    have hsplit := closedCellSplit_norm_sq n (closedCellPermute e x.1)
    rw [closedCellPermute_norm] at hsplit
    have hmain : 1 - (1 - ‖x.1‖ ^ 2) - ‖closedCellTail n (closedCellPermute e x.1)‖ ^ 2 =
        ((closedCellPermute e x.1) (0)) ^ 2 := by
      have hring : 1 - (1 - ‖x.1‖ ^ 2) - ‖closedCellTail n (closedCellPermute e x.1)‖ ^ 2 =
          ‖x.1‖ ^ 2 - ‖closedCellTail n (closedCellPermute e x.1)‖ ^ 2 := by ring
      rw [hring]
      rw [hsplit]
      ring
    have hsqrt : s * Real.sqrt (1 - (1 - ‖x.1‖ ^ 2) -
        ‖closedCellTail n (closedCellPermute e x.1)‖ ^ 2) =
        (closedCellPermute e x.1) (0) := by
      rw [hmain]
      rw [Real.sqrt_sq_eq_abs]
      exact closedCellSign_mul_abs hx
    rw [hsqrt]
    change (closedCellPermute e.symm (closedCellCons n ((closedCellPermute e x.1) (0))
        (closedCellTail n (closedCellPermute e x.1)))) = x.1
    rw [closedCellCons_split n (closedCellPermute e x.1)]
    exact closedCellPermute_inv e x.1
  · intro y hy
    apply Subtype.ext
    change (closedCellBoundaryChartValue n e (closedCellProject
        (closedCellBoundaryInvValue n e s y.1))).1 = y.1
    rw [closedCellBoundaryChartValue_coe]
    have hzle : ‖closedCellBoundaryInvValue n e s y.1‖ ≤ 1 :=
      closedCellBoundaryInvValue_norm_le_one e hs y.1 hy.2 y.2
    rw [closedCellProject_of_mem hzle]
    dsimp [closedCellBoundaryInvValue]
    rw [closedCellPermute_inv']
    rw [closedCellCons_tail]
    have hnorm : ‖closedCellPermute e.symm (closedCellCons n
        (s * Real.sqrt (1 - y.1 (0) - ‖closedCellTail n y.1‖ ^ 2))
          (closedCellTail n y.1))‖ ^ 2 = 1 - y.1 (0) :=
      closedCellBoundaryInvValue_norm_sq e hs y.1 hy.2
    have hmain : 1 - ‖closedCellPermute e.symm (closedCellCons n
        (s * Real.sqrt (1 - y.1 (0) - ‖closedCellTail n y.1‖ ^ 2))
          (closedCellTail n y.1))‖ ^ 2 = y.1 (0) := by
      rw [hnorm]
      ring
    rw [hmain]
    exact closedCellCons_split n y.1
  · have hcont : Continuous (fun x : ClosedCell (n + 1) =>
        s * (closedCellPermute e x.1) (0)) := by
      have hlin : Continuous (fun x : EuclideanSpace ℝ (Fin (n + 1)) =>
          closedCellPermute e x) := (closedCellPermute e).continuous
      have hc : Continuous (fun x : EuclideanSpace ℝ (Fin (n + 1)) =>
          (closedCellPermute e x) (0)) := by
        have hlin' : Continuous (fun x : EuclideanSpace ℝ (Fin (n + 1)) =>
            WithLp.ofLp (closedCellPermute e x)) :=
          (PiLp.continuous_ofLp 2 (fun _ : Fin (n + 1) => ℝ)).comp hlin
        exact (continuous_apply (0 : Fin (n + 1))).comp hlin'
      exact continuous_const.mul (hc.comp continuous_subtype_val)
    exact (isOpen_Ioi (a := (0 : ℝ))).preimage hcont
  · have hcont1 : Continuous (fun y : EuclideanHalfSpace (n + 1) =>
        y.1 (0)) :=
      (continuous_apply (0 : Fin (n + 1))).comp
        ((PiLp.continuous_ofLp 2 (fun _ : Fin (n + 1) => ℝ)).comp continuous_subtype_val)
    have htail : Continuous (fun y : EuclideanHalfSpace (n + 1) =>
        closedCellTail n y.1) := by
      unfold closedCellTail
      fun_prop
    have hcont2 : Continuous (fun y : EuclideanHalfSpace (n + 1) =>
        1 - y.1 (0) - ‖closedCellTail n y.1‖ ^ 2) :=
      (continuous_const.sub hcont1).sub ((continuous_norm.comp htail).pow 2)
    exact ((isOpen_Iio (a := (1 : ℝ))).preimage hcont1).inter
      ((isOpen_Ioi (a := (0 : ℝ))).preimage hcont2)
  · have hcont : Continuous (fun x : ClosedCell (n + 1) =>
        closedCellCons n (1 - ‖x.1‖ ^ 2) (closedCellTail n (closedCellPermute e x.1))) := by
      have hlin : Continuous (fun x : EuclideanSpace ℝ (Fin (n + 1)) =>
          closedCellPermute e x) := (closedCellPermute e).continuous
      have htail : Continuous (fun x : EuclideanSpace ℝ (Fin (n + 1)) =>
          closedCellTail n x) := by
        unfold closedCellTail
        fun_prop
      have hcons : Continuous (fun x : EuclideanSpace ℝ (Fin (n + 1)) =>
          closedCellCons n (1 - ‖x‖ ^ 2) (closedCellTail n x)) := by
        have hfin : Continuous (fun x : EuclideanSpace ℝ (Fin (n + 1)) =>
            (Fin.cons (1 - ‖x‖ ^ 2) (WithLp.ofLp (closedCellTail n x)) : Fin (n + 1) → ℝ)) := by
          refine Continuous.finCons (A := fun _ : Fin (n + 1) => ℝ) ?_ ?_
          · fun_prop
          · have htail' : Continuous (fun x : EuclideanSpace ℝ (Fin (n + 1)) =>
                WithLp.ofLp (closedCellTail n x)) :=
              (PiLp.continuous_ofLp (p := 2) (β := fun _ : Fin n => ℝ)).comp htail
            exact htail'
        simpa [closedCellCons_eq_cons] using
          (PiLp.continuous_toLp (p := 2) (β := fun _ : Fin (n + 1) => ℝ)).comp hfin
      exact Continuous.congr (hcons.comp (hlin.comp continuous_subtype_val)) (fun x => by
        change closedCellCons n (1 - ‖closedCellPermute e x.1‖ ^ 2)
            (closedCellTail n (closedCellPermute e x.1)) =
          closedCellCons n (1 - ‖x.1‖ ^ 2) (closedCellTail n (closedCellPermute e x.1))
        congr 1
        rw [closedCellPermute_norm])
    exact (Continuous.subtype_mk hcont (fun x => by
      change 0 ≤ (closedCellCons n (1 - ‖x.1‖ ^ 2)
          (closedCellTail n (closedCellPermute e x.1))) (0)
      rw [closedCellCons_apply_zero]
      have hsq : ‖x.1‖ ^ 2 ≤ 1 := by
        nlinarith [norm_nonneg x.1, x.2]
      linarith)).continuousOn
  · refine continuousOn_iff_continuous_restrict.mpr ?_
    have hlin : Continuous (fun y : EuclideanSpace ℝ (Fin (n + 1)) =>
        closedCellBoundaryInvValue n e s y) := by
      dsimp [closedCellBoundaryInvValue]
      have hperm : Continuous (fun y : EuclideanSpace ℝ (Fin (n + 1)) =>
          closedCellPermute e.symm y) := (closedCellPermute e.symm).continuous
      have hcons : Continuous (fun y : EuclideanSpace ℝ (Fin (n + 1)) =>
          closedCellCons n (s * Real.sqrt (1 - y (0) - ‖closedCellTail n y‖ ^ 2))
            (closedCellTail n y)) := by
        have htail : Continuous (fun y : EuclideanSpace ℝ (Fin (n + 1)) =>
            closedCellTail n y) := by
          unfold closedCellTail
          fun_prop
        have hsqrt : Continuous (fun y : EuclideanSpace ℝ (Fin (n + 1)) =>
            Real.sqrt (1 - y (0) - ‖closedCellTail n y‖ ^ 2)) := by
          have harg : Continuous (fun y : EuclideanSpace ℝ (Fin (n + 1)) =>
              1 - y (0) - ‖closedCellTail n y‖ ^ 2) :=
            let hc0 : Continuous (fun y : EuclideanSpace ℝ (Fin (n + 1)) => y (0)) :=
              (continuous_apply (0 : Fin (n + 1))).comp
                (PiLp.continuous_ofLp (p := 2) (β := fun _ : Fin (n + 1) => ℝ))
            (continuous_const.sub hc0).sub ((continuous_norm.comp htail).pow 2)
          exact Real.continuous_sqrt.comp harg
        have hfin : Continuous (fun y : EuclideanSpace ℝ (Fin (n + 1)) =>
            (Fin.cons (s * Real.sqrt (1 - y (0) - ‖closedCellTail n y‖ ^ 2))
              (WithLp.ofLp (closedCellTail n y)) : Fin (n + 1) → ℝ)) := by
          refine Continuous.finCons ?_ ?_
          · exact (continuous_const.mul hsqrt)
          · have htail' : Continuous (fun y : EuclideanSpace ℝ (Fin (n + 1)) =>
                WithLp.ofLp (closedCellTail n y)) :=
              (PiLp.continuous_ofLp (p := 2) (β := fun _ : Fin n => ℝ)).comp htail
            exact htail'
        simpa [closedCellCons_eq_cons] using
          (PiLp.continuous_toLp (p := 2) (β := fun _ : Fin (n + 1) => ℝ)).comp hfin
      exact hperm.comp hcons
    have hlin' : Continuous (fun y : {y : EuclideanHalfSpace (n + 1) |
        y.1 (0) < 1 ∧
          0 < 1 - y.1 (0) - ‖closedCellTail n y.1‖ ^ 2} =>
        closedCellBoundaryInvValue n e s (Subtype.val (Subtype.val y))) :=
      hlin.comp (continuous_subtype_val.comp continuous_subtype_val)
    exact Continuous.congr (Continuous.subtype_mk hlin' (fun y => by
      exact closedCellBoundaryInvValue_norm_le_one e hs
        (Subtype.val (Subtype.val y)) y.2.2 (Subtype.val y).2)) (fun y => by
      change ⟨closedCellBoundaryInvValue n e s (Subtype.val (Subtype.val y)),
          closedCellBoundaryInvValue_norm_le_one e hs
            (Subtype.val (Subtype.val y)) y.2.2 (Subtype.val y).2⟩ =
        closedCellProject (closedCellBoundaryInvValue n e s (Subtype.val (Subtype.val y)))
      exact (closedCellProject_of_mem (closedCellBoundaryInvValue_norm_le_one e hs
        (Subtype.val (Subtype.val y)) y.2.2 (Subtype.val y).2)).symm)



theorem closedCellSign_mul_pos {a : ℝ} (ha : a ≠ 0) :
    0 < (if 0 < a then (1 : ℝ) else -1) * a := by
  by_cases hapos : 0 < a
  · simp [hapos]
  · have hneg : a < 0 := lt_of_le_of_ne (le_of_not_gt hapos) ha
    simp [hapos, hneg]

theorem closedCell_exists_coord_ne_zero {m : ℕ} (x : EuclideanSpace ℝ (Fin (m + 1)))
    (hx : 1 ≤ ‖x‖) : ∃ i : Fin (m + 1), x i ≠ 0 := by
  by_contra h
  have hx0 : x = 0 := by
    ext i
    by_contra hi
    exact h ⟨i, hi⟩
  rw [hx0, norm_zero] at hx
  norm_num at hx

theorem closedCellPermute_swap_apply {m : ℕ} (i : Fin (m + 1)) (x : EuclideanSpace ℝ (Fin (m + 1))) :
    (closedCellPermute (Equiv.swap i (0 : Fin (m + 1))) x) (0 : Fin (m + 1)) = x i := by
  rw [closedCellPermute_apply]
  change x.1 ((Equiv.swap i (0 : Fin (m + 1))).symm (0 : Fin (m + 1))) = x.1 i
  simp [Equiv.symm_swap, Equiv.swap_apply_right]

theorem closedCellSign_decide {a : ℝ} :
    closedCellSign (0 < a) = if 0 < a then (1 : ℝ) else -1 := by
  by_cases h : 0 < a
  · simp [h, closedCellSign]
  · simp [h, closedCellSign]

theorem mem_closedCellInteriorChart_source (n : ℕ) (x : ClosedCell (n + 1)) (hx : ‖x.1‖ < 1) :
    x ∈ (closedCellInteriorChart n).source := hx

theorem mem_closedCellBoundaryChart_source {m : ℕ} (x : ClosedCell (m + 1)) {i : Fin (m + 1)}
    (hi : x.1 i ≠ 0) :
    x ∈ (closedCellBoundaryChart m i (0 < x.1 i)).source := by
  change 0 < closedCellSign (0 < x.1 i) * (closedCellPermute (Equiv.swap i (0 : Fin (m + 1)))
    x.1) (0 : Fin (m + 1))
  rw [closedCellPermute_swap_apply]
  rw [closedCellSign_decide]
  exact closedCellSign_mul_pos hi

noncomputable def closedCellChartAt {m : ℕ} (x : ClosedCell (m + 1)) :
    OpenPartialHomeomorph (ClosedCell (m + 1)) (EuclideanHalfSpace (m + 1)) :=
  if hx : ‖x.1‖ < 1 then closedCellInteriorChart m
  else
    let i : Fin (m + 1) := Classical.choose (closedCell_exists_coord_ne_zero x.1 (by
      have hle : ‖x.1‖ ≤ 1 := x.2
      have hnot : ¬ ‖x.1‖ < 1 := hx
      linarith))
    closedCellBoundaryChart m i (0 < x.1 i)

@[reducible]
noncomputable def closedCellChartedSpaceSucc (m : ℕ) :
    ChartedSpace (EuclideanHalfSpace (m + 1)) (ClosedCell (m + 1)) where
  atlas := Set.range closedCellChartAt
  chartAt := closedCellChartAt
  mem_chart_source := by
    intro x
    by_cases hx : ‖x.1‖ < 1
    · rw [closedCellChartAt, dif_pos hx]
      exact hx
    · rw [closedCellChartAt, dif_neg hx]
      have hne : x.1 (Classical.choose (closedCell_exists_coord_ne_zero x.1 (by
          have hle : ‖x.1‖ ≤ 1 := x.2
          have hnot : ¬ ‖x.1‖ < 1 := hx
          linarith))) ≠ 0 :=
        (Classical.choose_spec (closedCell_exists_coord_ne_zero x.1 (by
          have hle : ‖x.1‖ ≤ 1 := x.2
          have hnot : ¬ ‖x.1‖ < 1 := hx
          linarith)))
      exact mem_closedCellBoundaryChart_source x hne
  chart_mem_atlas := fun x => ⟨x, rfl⟩

theorem closedCellCons_contDiff {m : ℕ} :
    ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × EuclideanSpace ℝ (Fin m) =>
      closedCellCons m p.1 p.2) := by
  rw [show (fun p : ℝ × EuclideanSpace ℝ (Fin m) => closedCellCons m p.1 p.2) =
      WithLp.toLp 2 ∘ (fun p : ℝ × EuclideanSpace ℝ (Fin m) =>
        Fin.cons p.1 (WithLp.ofLp p.2)) from by
    funext p
    exact closedCellCons_eq_cons m p.1 p.2]
  have hfin : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × EuclideanSpace ℝ (Fin m) =>
      (Fin.cons p.1 (WithLp.ofLp p.2) : Fin (m + 1) → ℝ)) := by
    rw [show (fun p : ℝ × EuclideanSpace ℝ (Fin m) => Fin.cons p.1 (WithLp.ofLp p.2)) =
        fun p j => (Fin.cases p.1 (fun j' : Fin m => (WithLp.ofLp p.2 : Fin m → ℝ) j') j : ℝ) from by
      funext p
      ext j
      by_cases hj : j = (0 : Fin (m + 1))
      · subst j
        rfl
      · have hsucc : ∃ j' : Fin m, Fin.succ j' = j := Fin.exists_succ_eq.mpr hj
        rcases hsucc with ⟨j', rfl⟩
        rfl]
    exact contDiff_pi' (fun j => by
      by_cases hj : j = (0 : Fin (m + 1))
      · subst j
        change ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × EuclideanSpace ℝ (Fin m) => p.1)
        exact contDiff_fst
      · have hsucc : ∃ j' : Fin m, Fin.succ j' = j := Fin.exists_succ_eq.mpr hj
        rcases hsucc with ⟨j', rfl⟩
        change ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × EuclideanSpace ℝ (Fin m) => (WithLp.ofLp p.2) j')
        fun_prop)
  let htoLp : (Fin (m + 1) → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin (m + 1)) :=
    { toLinearMap := (WithLp.linearEquiv 2 ℝ (Fin (m + 1) → ℝ)).symm.toLinearMap
      cont := PiLp.continuous_toLp (p := 2) (β := fun _ : Fin (m + 1) => ℝ) }
  have hfun : ⇑htoLp = (WithLp.toLp 2 : (Fin (m + 1) → ℝ) → EuclideanSpace ℝ (Fin (m + 1))) := by
    dsimp [htoLp]
    change ⇑(WithLp.linearEquiv 2 ℝ (Fin (m + 1) → ℝ)).symm = WithLp.toLp 2
    exact WithLp.coe_symm_linearEquiv 2 ℝ (Fin (m + 1) → ℝ)
  simpa [hfun] using htoLp.contDiff.comp hfin

theorem closedCellShiftSucc_contDiff {m : ℕ} (c : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x : EuclideanSpace ℝ (Fin (m + 1)) => closedCellShiftSucc m c x) := by
  have hlin : ContDiff ℝ (⊤ : ℕ∞) (fun x : EuclideanSpace ℝ (Fin (m + 1)) =>
      x + c • (EuclideanSpace.basisFun (Fin (m + 1)) ℝ (0 : Fin (m + 1)))) :=
    contDiff_id.add contDiff_const
  simpa [closedCellShiftSucc_eq_add] using hlin

theorem closedCellPermute_contDiff {m : ℕ} (e : Fin (m + 1) ≃ Fin (m + 1)) :
    ContDiff ℝ (⊤ : ℕ∞) (closedCellPermute e) := by
  exact (closedCellPermute e).toContinuousLinearEquiv.contDiff

theorem closedCellTail_contDiff {m : ℕ} :
    ContDiff ℝ (⊤ : ℕ∞) (fun x : EuclideanSpace ℝ (Fin (m + 1)) => closedCellTail m x) := by
  unfold closedCellTail
  fun_prop

theorem closedCellCons_contDiffOn_left {m : ℕ} :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun x : EuclideanSpace ℝ (Fin (m + 1)) =>
      closedCellCons m (1 - ‖x‖ ^ 2) (closedCellTail m x)) Set.univ := by
  have hcons : ContDiff ℝ (⊤ : ℕ∞) (fun x : EuclideanSpace ℝ (Fin (m + 1)) =>
      closedCellCons m (1 - ‖x‖ ^ 2) (closedCellTail m x)) := by
    -- (1 - ‖x‖^2, tail x) ↦ cons
    have hpair : ContDiff ℝ (⊤ : ℕ∞) (fun x : EuclideanSpace ℝ (Fin (m + 1)) =>
        (1 - ‖x‖ ^ 2, closedCellTail m x)) := by
      have hnorm : ContDiff ℝ (⊤ : ℕ∞) (fun x : EuclideanSpace ℝ (Fin (m + 1)) => 1 - ‖x‖ ^ 2) := by
        exact (contDiff_const.sub (contDiff_norm_sq ℝ))
      exact hnorm.prodMk (closedCellTail_contDiff (m := m))
    have hcons' : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × EuclideanSpace ℝ (Fin m) =>
        closedCellCons m p.1 p.2) := closedCellCons_contDiff
    -- compose hcons' with hpair
    have hcomp : ContDiff ℝ (⊤ : ℕ∞)
        (fun x : EuclideanSpace ℝ (Fin (m + 1)) =>
          closedCellCons m (1 - ‖x‖ ^ 2) (closedCellTail m x)) := by
      simpa using hcons'.comp hpair
    exact hcomp
  exact hcons.contDiffOn

theorem closedCellInteriorBoundaryTransition_contDiff {m : ℕ} (i : Fin (m + 1)) :
    ContDiff ℝ (⊤ : ℕ∞) (fun y : EuclideanSpace ℝ (Fin (m + 1)) =>
      closedCellCons m (1 - ‖closedCellShiftSucc m (-1) y‖ ^ 2)
        (closedCellTail m (closedCellPermute (Equiv.swap i (0 : Fin (m + 1)))
          (closedCellShiftSucc m (-1) y)))) := by
  have hshift : ContDiff ℝ (⊤ : ℕ∞) (fun y : EuclideanSpace ℝ (Fin (m + 1)) =>
      closedCellShiftSucc m (-1) y) := closedCellShiftSucc_contDiff (-1)
  have hperm : ContDiff ℝ (⊤ : ℕ∞) (closedCellPermute (Equiv.swap i (0 : Fin (m + 1)))) :=
    closedCellPermute_contDiff (Equiv.swap i (0 : Fin (m + 1)))
  have hnorm : ContDiff ℝ (⊤ : ℕ∞) (fun y : EuclideanSpace ℝ (Fin (m + 1)) =>
      1 - ‖closedCellShiftSucc m (-1) y‖ ^ 2) := by
    exact (contDiff_const.sub ((contDiff_norm_sq ℝ).comp hshift))
  have htail : ContDiff ℝ (⊤ : ℕ∞) (fun y : EuclideanSpace ℝ (Fin (m + 1)) =>
      closedCellTail m (closedCellPermute (Equiv.swap i (0 : Fin (m + 1)))
        (closedCellShiftSucc m (-1) y))) := by
    exact (closedCellTail_contDiff (m := m)).comp (hperm.comp hshift)
  have hpair : ContDiff ℝ (⊤ : ℕ∞) (fun y : EuclideanSpace ℝ (Fin (m + 1)) =>
      (1 - ‖closedCellShiftSucc m (-1) y‖ ^ 2,
        closedCellTail m (closedCellPermute (Equiv.swap i (0 : Fin (m + 1)))
          (closedCellShiftSucc m (-1) y)))) :=
    hnorm.prodMk htail
  simpa using (closedCellCons_contDiff (m := m)).comp hpair

end

end DifferentialGeometry.Topology.Handle
