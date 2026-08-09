import DifferentialGeometry.Topology.Morse.Defs
import DifferentialGeometry.Topology.Morse.LocalNormalForm
import DifferentialGeometry.Topology.Attachment.Union
import DifferentialGeometry.Topology.Handle.Defs
import Mathlib.Topology.Homotopy.Basic
import Mathlib.Topology.Homotopy.Equiv

namespace DifferentialGeometry.Topology.Morse

open Filter
open DifferentialGeometry.Topology.Handle
open scoped Topology

noncomputable section

namespace CellAttachment

def negIdx {n k : ℕ} (hk : k ≤ n) (i : Fin k) : Fin n :=
  Fin.castLE hk i

def posIdx {n k : ℕ} (hk : k ≤ n) (j : Fin (n - k)) : Fin n :=
  ⟨k + j, by omega⟩

def morseNormalForm {n k : ℕ} (hk : k ≤ n) (c : ℝ) (y : MorseModel n) : ℝ :=
  c + (1 / 2) * (∑ i : Fin k, - (y (negIdx hk i)) ^ 2 +
    ∑ j : Fin (n - k), (y (posIdx hk j)) ^ 2)

def cellMap {n k : ℕ} (r : ℝ) (x : EuclideanSpace ℝ (Fin k)) :
    MorseModel n :=
  fun i => if h : i.val < k then r * x ⟨i.val, h⟩ else 0

theorem cellMap_negIdx {n k : ℕ} (hk : k ≤ n) (ε : ℝ)
    (x : EuclideanSpace ℝ (Fin k)) (i : Fin k) :
    cellMap ε x (negIdx hk i) = ε * x i := by
  dsimp [cellMap, negIdx]
  simp [i.isLt]

theorem cellMap_posIdx {n k : ℕ} (hk : k ≤ n) (ε : ℝ)
    (x : EuclideanSpace ℝ (Fin k)) (j : Fin (n - k)) :
    cellMap ε x (posIdx hk j) = 0 := by
  dsimp [cellMap, posIdx]
  rw [dif_neg]
  omega

theorem morseNormalForm_cellMap {n k : ℕ} (hk : k ≤ n) (c ε : ℝ)
    (x : EuclideanSpace ℝ (Fin k)) :
    morseNormalForm hk c (cellMap ε x) = c + (1 / 2) * (-(ε ^ 2) * ‖x‖ ^ 2) := by
  dsimp [morseNormalForm]
  have hneg : (∑ i : Fin k, - (cellMap ε x (negIdx hk i)) ^ 2) = -(ε ^ 2) * ‖x‖ ^ 2 := by
    calc
      (∑ i : Fin k, - (cellMap ε x (negIdx hk i)) ^ 2)
          = ∑ i : Fin k, - (ε * x i) ^ 2 := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [cellMap_negIdx]
      _ = -(ε ^ 2) * ∑ i : Fin k, (x i) ^ 2 := by
        rw [Finset.sum_neg_distrib]
        rw [Finset.mul_sum]
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro i hi
        rw [mul_pow]
        ring
      _ = -(ε ^ 2) * ‖x‖ ^ 2 := by
        congr 1
        exact (EuclideanSpace.real_norm_sq_eq x).symm
  have hpos : (∑ j : Fin (n - k), (cellMap ε x (posIdx hk j)) ^ 2) = 0 := by
    simp [cellMap_posIdx]
  rw [hneg, hpos]
  ring

def attachMap {n k : ℕ} (hk : k ≤ n) (c ε : ℝ) (hε : 0 ≤ ε) (x : CellBoundary k) :
    sublevel (morseNormalForm hk c) (c - ε) :=
  ⟨cellMap (Real.sqrt (2 * ε)) (x : EuclideanSpace ℝ (Fin k)), by
    have hnorm : ‖(x : EuclideanSpace ℝ (Fin k))‖ = 1 := x.2
    have hf : morseNormalForm hk c (cellMap (Real.sqrt (2 * ε)) (x : EuclideanSpace ℝ (Fin k))) =
        c + (1 / 2) * (-((Real.sqrt (2 * ε)) ^ 2) * ‖(x : EuclideanSpace ℝ (Fin k))‖ ^ 2) := by
      rw [morseNormalForm_cellMap]
    have hsq : (Real.sqrt (2 * ε)) ^ 2 = 2 * ε := by
      rw [Real.sq_sqrt (by positivity : 0 ≤ 2 * ε)]
    have hle : c + (1 / 2) * (-((Real.sqrt (2 * ε)) ^ 2) * ‖(x : EuclideanSpace ℝ (Fin k))‖ ^ 2) ≤ c - ε := by
      rw [hsq, hnorm]
      ring_nf
      exact le_rfl
    simpa [sublevel] using hf.trans_le hle⟩

theorem cellMap_mem_sublevel_upper {n k : ℕ} (hk : k ≤ n) (c ε : ℝ)
    (x : ClosedCell k) (hε : 0 ≤ ε) :
    cellMap (Real.sqrt (2 * ε)) (x : EuclideanSpace ℝ (Fin k)) ∈
      sublevel (morseNormalForm hk c) (c + ε) := by
  change morseNormalForm hk c (cellMap (Real.sqrt (2 * ε)) (x : EuclideanSpace ℝ (Fin k))) ≤ c + ε
  have hnorm : ‖(x : EuclideanSpace ℝ (Fin k))‖ ≤ 1 := x.2
  have hf := morseNormalForm_cellMap hk c (Real.sqrt (2 * ε)) (x : EuclideanSpace ℝ (Fin k))
  rw [hf]
  have hsq : (Real.sqrt (2 * ε)) ^ 2 = 2 * ε := by
    rw [Real.sq_sqrt (by positivity : 0 ≤ 2 * ε)]
  have hle : (1 / 2 : ℝ) * (-((Real.sqrt (2 * ε)) ^ 2) * ‖(x : EuclideanSpace ℝ (Fin k))‖ ^ 2) ≤ ε := by
    rw [hsq]
    nlinarith [sq_nonneg ‖(x : EuclideanSpace ℝ (Fin k))‖]
  linarith

def negPart {n k : ℕ} (hk : k ≤ n) (y : MorseModel n) : EuclideanSpace ℝ (Fin k) :=
  WithLp.toLp 2 (fun i : Fin k => y (negIdx hk i))

def posPart {n k : ℕ} (hk : k ≤ n) (y : MorseModel n) : EuclideanSpace ℝ (Fin (n - k)) :=
  WithLp.toLp 2 (fun j : Fin (n - k) => y (posIdx hk j))

theorem negPart_top {n : ℕ} (y : MorseModel n) :
    (negPart (le_rfl : n ≤ n) y : EuclideanSpace ℝ (Fin n)) = y := by
  funext i
  rfl

theorem posPart_top {n : ℕ} (y : MorseModel n) :
    posPart (le_rfl : n ≤ n) y = (0 : EuclideanSpace ℝ (Fin (n - n))) := by
  ext i
  have hn : n - n = 0 := Nat.sub_self n
  have hi : i.1 < 0 := by simpa [hn] using i.isLt
  exact False.elim (Nat.not_lt_zero i.1 hi)

theorem negPart_bot {n : ℕ} (y : MorseModel n) :
    negPart (zero_le n) y = (0 : EuclideanSpace ℝ (Fin 0)) := by
  ext i
  exact False.elim (Nat.not_lt_zero i.1 i.isLt)

theorem posPart_bot {n : ℕ} (y : MorseModel n) :
    (posPart (zero_le n) y : EuclideanSpace ℝ (Fin n)) = y := by
  ext i
  simp [posPart, posIdx]

def recombine {n k : ℕ} (hk : k ≤ n) (a : EuclideanSpace ℝ (Fin k))
    (b : EuclideanSpace ℝ (Fin (n - k))) : MorseModel n :=
  fun i => if h : i.val < k then a ⟨i.val, h⟩ else b ⟨i.val - k, by
    have hkle : k ≤ i.val := le_of_not_gt h
    have hi : i.val < n := i.isLt
    omega⟩

theorem recombine_negPart {n k : ℕ} (hk : k ≤ n) (a : EuclideanSpace ℝ (Fin k))
    (b : EuclideanSpace ℝ (Fin (n - k))) (i : Fin k) :
    recombine hk a b (negIdx hk i) = a i := by
  dsimp [recombine, negIdx]
  simp [i.isLt]

theorem recombine_posPart {n k : ℕ} (hk : k ≤ n) (a : EuclideanSpace ℝ (Fin k))
    (b : EuclideanSpace ℝ (Fin (n - k))) (j : Fin (n - k)) :
    recombine hk a b (posIdx hk j) = b j := by
  dsimp [recombine, posIdx]
  rw [dif_neg (by omega : ¬ k + (j : ℕ) < k)]
  apply congrArg b.ofLp
  apply Fin.ext
  simp

theorem recombine_top {n : ℕ} (a : EuclideanSpace ℝ (Fin n))
    (b : EuclideanSpace ℝ (Fin (n - n))) :
    recombine (le_rfl : n ≤ n) a b = a := by
  funext i
  dsimp [recombine]
  rw [dif_pos i.isLt]

theorem recombine_bot {n : ℕ} (a : EuclideanSpace ℝ (Fin 0))
    (b : EuclideanSpace ℝ (Fin n)) :
    recombine (zero_le n) a b = b := by
  funext i
  dsimp [recombine]

theorem recombine_decompose {n k : ℕ} (hk : k ≤ n) (y : MorseModel n) :
    recombine hk (negPart hk y) (posPart hk y) = y := by
  funext i
  by_cases h : i.val < k
  · have hi : i = negIdx hk ⟨i.val, h⟩ := by
      apply Fin.ext
      rfl
    calc
      recombine hk (negPart hk y) (posPart hk y) i
          = recombine hk (negPart hk y) (posPart hk y) (negIdx hk ⟨i.val, h⟩) := by rw [← hi]
      _ = negPart hk y ⟨i.val, h⟩ := recombine_negPart hk (negPart hk y) (posPart hk y) ⟨i.val, h⟩
      _ = y i := by
        have hi' : negIdx hk ⟨i.val, h⟩ = i := hi.symm
        change y (negIdx hk ⟨i.val, h⟩) = y i
        rw [hi']
  · have hi : i = posIdx hk ⟨i.val - k, by
        have hkle : k ≤ i.val := le_of_not_gt h
        have hi' : i.val < n := i.isLt
        omega⟩ := by
      apply Fin.ext
      have hkle : k ≤ i.val := le_of_not_gt h
      change ↑i = k + (↑i - k)
      rw [Nat.add_sub_of_le hkle]
    calc
      recombine hk (negPart hk y) (posPart hk y) i
          = recombine hk (negPart hk y) (posPart hk y) (posIdx hk ⟨i.val - k, _⟩) := by
            rw [← hi]
      _ = posPart hk y ⟨i.val - k, _⟩ := recombine_posPart hk (negPart hk y) (posPart hk y) ⟨i.val - k, _⟩
      _ = y i := by
        have hi' : posIdx hk ⟨i.val - k, _⟩ = i := hi.symm
        change y (posIdx hk ⟨i.val - k, _⟩) = y i
        rw [hi']

theorem negPart_cellMap_apply {n k : ℕ} (hk : k ≤ n) (ε : ℝ)
    (u : EuclideanSpace ℝ (Fin k)) (i : Fin k) :
    negPart hk (cellMap ε u) i = ε * u i := by
  dsimp [negPart, cellMap, negIdx]
  simp [i.isLt]

theorem negPart_cellMap_norm_sq {n k : ℕ} (hk : k ≤ n) (ε : ℝ)
    (u : EuclideanSpace ℝ (Fin k)) :
    ‖negPart hk (cellMap ε u)‖ ^ 2 = ε ^ 2 * ‖u‖ ^ 2 := by
  calc
    ‖negPart hk (cellMap ε u)‖ ^ 2
        = ∑ i : Fin k, (negPart hk (cellMap ε u) i) ^ 2 := by
          rw [EuclideanSpace.real_norm_sq_eq (negPart hk (cellMap ε u))]
    _ = ∑ i : Fin k, (ε * u i) ^ 2 := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [negPart_cellMap_apply]
    _ = ε ^ 2 * ∑ i : Fin k, (u i) ^ 2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [mul_pow]
    _ = ε ^ 2 * ‖u‖ ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq u]

theorem morseNormalForm_recombine {n k : ℕ} (hk : k ≤ n) (c ε : ℝ)
    (u : EuclideanSpace ℝ (Fin k)) (v : EuclideanSpace ℝ (Fin (n - k))) :
    morseNormalForm hk c (recombine hk (negPart hk (cellMap ε u)) v) =
      c + (1 / 2) * (-(ε ^ 2) * ‖u‖ ^ 2 + ‖v‖ ^ 2) := by
  dsimp [morseNormalForm]
  have hneg : (∑ i : Fin k, - (recombine hk (negPart hk (cellMap ε u)) v (negIdx hk i)) ^ 2) =
      -(ε ^ 2) * ‖u‖ ^ 2 := by
    calc
      (∑ i : Fin k, - (recombine hk (negPart hk (cellMap ε u)) v (negIdx hk i)) ^ 2)
          = ∑ i : Fin k, - (negPart hk (cellMap ε u) i) ^ 2 := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [recombine_negPart]
      _ = -((ε ^ 2) * ‖u‖ ^ 2) := by
        rw [Finset.sum_neg_distrib]
        congr 1
        rw [← EuclideanSpace.real_norm_sq_eq (negPart hk (cellMap ε u))]
        exact negPart_cellMap_norm_sq hk ε u
      _ = -(ε ^ 2) * ‖u‖ ^ 2 := by
        ring
  have hpos : (∑ j : Fin (n - k),
      (recombine hk (negPart hk (cellMap ε u)) v (posIdx hk j)) ^ 2) = ‖v‖ ^ 2 := by
    calc
      (∑ j : Fin (n - k), (recombine hk (negPart hk (cellMap ε u)) v (posIdx hk j)) ^ 2)
          = ∑ j : Fin (n - k), (v j) ^ 2 := by
            apply Finset.sum_congr rfl
            intro j hj
            rw [recombine_posPart]
      _ = ‖v‖ ^ 2 := by
        exact (EuclideanSpace.real_norm_sq_eq v).symm
  rw [hneg, hpos]

theorem morseNormalForm_recombine_cellMap {n k : ℕ} (hk : k ≤ n) (c ε : ℝ) (hε : 0 ≤ ε)
    (u : EuclideanSpace ℝ (Fin k)) (v : EuclideanSpace ℝ (Fin (n - k))) :
    morseNormalForm hk c (recombine hk (negPart hk (cellMap (Real.sqrt (2 * ε)) u)) v) =
      c + (1 / 2) * (-(2 * ε) * ‖u‖ ^ 2 + ‖v‖ ^ 2) := by
  rw [morseNormalForm_recombine hk c (Real.sqrt (2 * ε)) u v]
  have hsq : (Real.sqrt (2 * ε)) ^ 2 = 2 * ε := by
    rw [Real.sq_sqrt (by positivity : 0 ≤ 2 * ε)]
  rw [hsq]

theorem morseNormalForm_cocoreMap_boundary {n k : ℕ} (hk : k ≤ n) (c ε : ℝ) (hε : 0 ≤ ε)
    (u : EuclideanSpace ℝ (Fin k)) (hu : ‖u‖ = 1)
    (v : EuclideanSpace ℝ (Fin (n - k))) :
    morseNormalForm hk c (recombine hk (negPart hk (cellMap (Real.sqrt (2 * ε)) u)) v) =
      c - ε + (1 / 2) * ‖v‖ ^ 2 := by
  have hval := morseNormalForm_recombine_cellMap hk c ε hε u v
  rw [hval, hu]
  ring

theorem morseNormalForm_recombine_scaled {n k : ℕ} (hk : k ≤ n) (c ε r : ℝ) (hε : 0 ≤ ε)
    (u : EuclideanSpace ℝ (Fin k)) (v : EuclideanSpace ℝ (Fin (n - k))) :
    morseNormalForm hk c (recombine hk (negPart hk (cellMap (Real.sqrt (2 * ε)) u)) (r • v)) =
      c + (1 / 2) * (-(2 * ε) * ‖u‖ ^ 2 + r ^ 2 * ‖v‖ ^ 2) := by
  rw [morseNormalForm_recombine_cellMap hk c ε hε u (r • v)]
  have hnorm : ‖(r • v : EuclideanSpace ℝ (Fin (n - k)))‖ ^ 2 = r ^ 2 * ‖v‖ ^ 2 := by
    rw [norm_smul]
    rw [Real.norm_eq_abs]
    rw [mul_pow]
    rw [sq_abs]
  rw [hnorm]

theorem morseNormalForm_split {n k : ℕ} (hk : k ≤ n) (c : ℝ) (y : MorseModel n) :
    morseNormalForm hk c y =
      c + (1 / 2) * (‖posPart hk y‖ ^ 2 - ‖negPart hk y‖ ^ 2) := by
  dsimp [morseNormalForm]
  have hneg : (∑ i : Fin k, - (y (negIdx hk i)) ^ 2) = -‖negPart hk y‖ ^ 2 := by
    calc
      (∑ i : Fin k, - (y (negIdx hk i)) ^ 2) = -(∑ i : Fin k, (negPart hk y i) ^ 2) := by
        rw [Finset.sum_neg_distrib]
        congr 1
      _ = -‖negPart hk y‖ ^ 2 := by
        rw [EuclideanSpace.real_norm_sq_eq (negPart hk y)]
  have hpos : (∑ j : Fin (n - k), (y (posIdx hk j)) ^ 2) = ‖posPart hk y‖ ^ 2 := by
    calc
      (∑ j : Fin (n - k), (y (posIdx hk j)) ^ 2)
          = ∑ j : Fin (n - k), (posPart hk y j) ^ 2 := by
            apply Finset.sum_congr rfl
            intro j hj
            rfl
      _ = ‖posPart hk y‖ ^ 2 := by
        exact (EuclideanSpace.real_norm_sq_eq (posPart hk y)).symm
  rw [hneg, hpos]
  ring_nf

def spineMap {n k : ℕ} (hk : k ≤ n) (y : MorseModel n) : MorseModel n :=
  recombine hk (negPart hk y) 0

theorem spineMap_split {n k : ℕ} (hk : k ≤ n) (c : ℝ) (y : MorseModel n) :
    morseNormalForm hk c (spineMap hk y) = c - (1 / 2) * ‖negPart hk y‖ ^ 2 := by
  have hneg : negPart hk (spineMap hk y) = negPart hk y := by
    ext i
    dsimp [spineMap, negPart]
    rw [recombine_negPart]
  have hpos : posPart hk (spineMap hk y) = 0 := by
    ext j
    dsimp [spineMap, posPart]
    rw [recombine_posPart]
    simp
  rw [morseNormalForm_split hk c (spineMap hk y), hpos, hneg]
  simp
  ring_nf

theorem spineMap_mem_lower {n k : ℕ} (hk : k ≤ n) (c ε : ℝ)
    {y : MorseModel n} (hy : 2 * ε ≤ ‖negPart hk y‖ ^ 2) :
    spineMap hk y ∈ sublevel (morseNormalForm hk c) (c - ε) := by
  change morseNormalForm hk c (spineMap hk y) ≤ c - ε
  rw [spineMap_split]
  nlinarith [sq_nonneg ‖negPart hk y‖]

theorem spineMap_mem_cell {n k : ℕ} (hk : k ≤ n) (ε : ℝ) (hε : 0 < ε)
    {y : MorseModel n} (hy : ‖negPart hk y‖ ^ 2 ≤ 2 * ε) :
    spineMap hk y ∈ Set.range (fun x : ClosedCell k => cellMap (Real.sqrt (2 * ε)) (x : EuclideanSpace ℝ (Fin k))) := by
  have hr : 0 < Real.sqrt (2 * ε) := by
    exact Real.sqrt_pos.2 (by positivity : 0 < 2 * ε)
  let x : ClosedCell k :=
    ⟨(Real.sqrt (2 * ε))⁻¹ • negPart hk y, by
      have hnorm : ‖negPart hk y‖ ≤ Real.sqrt (2 * ε) := by
        have hsq : ‖negPart hk y‖ ^ 2 ≤ (Real.sqrt (2 * ε)) ^ 2 := by
          rw [Real.sq_sqrt (by positivity : 0 ≤ 2 * ε)]
          exact hy
        have habs := (sq_le_sq.mp hsq)
        simpa [abs_of_nonneg] using habs
      rw [norm_smul]
      have habs : |(Real.sqrt (2 * ε))⁻¹| = (Real.sqrt (2 * ε))⁻¹ := by
        rw [abs_of_pos]
        positivity
      rw [Real.norm_eq_abs, habs]
      have h1 : (Real.sqrt (2 * ε))⁻¹ * ‖negPart hk y‖ ≤
          (Real.sqrt (2 * ε))⁻¹ * Real.sqrt (2 * ε) := by
        exact mul_le_mul_of_nonneg_left hnorm (inv_nonneg.mpr (le_of_lt hr))
      have h2 : (Real.sqrt (2 * ε))⁻¹ * Real.sqrt (2 * ε) = 1 := by
        rw [inv_mul_cancel₀ hr.ne']
      rwa [h2] at h1⟩
  refine ⟨x, ?_⟩
  ext i
  by_cases hi : i.val < k
  · have hi' : i = negIdx hk ⟨i.val, hi⟩ := by
      apply Fin.ext
      rfl
    calc
      cellMap (Real.sqrt (2 * ε)) (x : EuclideanSpace ℝ (Fin k)) i
          = cellMap (Real.sqrt (2 * ε)) (x : EuclideanSpace ℝ (Fin k)) (negIdx hk ⟨i.val, hi⟩) := by rw [← hi']
      _ = Real.sqrt (2 * ε) * (x : EuclideanSpace ℝ (Fin k)) ⟨i.val, hi⟩ :=
        cellMap_negIdx hk (Real.sqrt (2 * ε)) (x : EuclideanSpace ℝ (Fin k)) ⟨i.val, hi⟩
      _ = Real.sqrt (2 * ε) * ((Real.sqrt (2 * ε))⁻¹ * negPart hk y ⟨i.val, hi⟩) := by
        dsimp [x]
      _ = negPart hk y ⟨i.val, hi⟩ := by
        field_simp [hr.ne']
      _ = recombine hk (negPart hk y) 0 (negIdx hk ⟨i.val, hi⟩) := by
        rw [recombine_negPart]
      _ = recombine hk (negPart hk y) 0 i := by
        exact congrArg (recombine hk (negPart hk y) 0) hi'.symm
  · have hi' : i = posIdx hk ⟨i.val - k, by
        have hkle : k ≤ i.val := le_of_not_gt hi
        have hii : i.val < n := i.isLt
        omega⟩ := by
      apply Fin.ext
      have hkle : k ≤ i.val := le_of_not_gt hi
      change ↑i = k + (↑i - k)
      rw [Nat.add_sub_of_le hkle]
    calc
      cellMap (Real.sqrt (2 * ε)) (x : EuclideanSpace ℝ (Fin k)) i
          = cellMap (Real.sqrt (2 * ε)) (x : EuclideanSpace ℝ (Fin k)) (posIdx hk ⟨i.val - k, _⟩) := by rw [← hi']
      _ = 0 := cellMap_posIdx hk (Real.sqrt (2 * ε)) (x : EuclideanSpace ℝ (Fin k)) ⟨i.val - k, _⟩
      _ = recombine hk (negPart hk y) 0 (posIdx hk ⟨i.val - k, _⟩) := by
        rw [recombine_posPart]
        rfl
      _ = recombine hk (negPart hk y) 0 i := by
        exact congrArg (recombine hk (negPart hk y) 0) hi'.symm

noncomputable def lowerCellUnion {n k : ℕ} (hk : k ≤ n) (c ε : ℝ) : Set (MorseModel n) :=
  sublevel (morseNormalForm hk c) (c - ε) ∪
    Set.range (fun x : ClosedCell k => cellMap (Real.sqrt (2 * ε)) (x : EuclideanSpace ℝ (Fin k)))

abbrev upperSublevel {n k : ℕ} (hk : k ≤ n) (c ε : ℝ) : Type :=
  SublevelSpace (morseNormalForm hk c) (c + ε)

abbrev lowerUnion {n k : ℕ} (hk : k ≤ n) (c ε : ℝ) : Type :=
  {y : MorseModel n // y ∈ lowerCellUnion hk c ε}

theorem spineMap_mem_union {n k : ℕ} (hk : k ≤ n) (c ε : ℝ) (hε : 0 < ε)
    (y : MorseModel n) :
    spineMap hk y ∈ lowerCellUnion hk c ε := by
  dsimp [lowerCellUnion]
  by_cases h : 2 * ε ≤ ‖negPart hk y‖ ^ 2
  · exact Or.inl (spineMap_mem_lower hk c ε h)
  · exact Or.inr (spineMap_mem_cell hk ε hε (le_of_not_ge h))

def cellAttachmentMap {n k : ℕ} (hk : k ≤ n) (c ε : ℝ) (hε : 0 < ε) :
    upperSublevel hk c ε → lowerUnion hk c ε :=
  fun y =>
    ⟨spineMap hk y.1, spineMap_mem_union hk c ε hε y.1⟩

theorem cellAttachmentInclusion_mem {n k : ℕ} (hk : k ≤ n) (c ε : ℝ) (hε : 0 ≤ ε)
    (z : lowerUnion hk c ε) :
    z.1 ∈ sublevel (morseNormalForm hk c) (c + ε) := by
  change morseNormalForm hk c z.1 ≤ c + ε
  rcases z.2 with hz | ⟨x, hx⟩
  · have hle : morseNormalForm hk c z.1 ≤ c - ε := by simpa [sublevel] using hz
    linarith
  · rw [← hx]
    simpa [sublevel] using (cellMap_mem_sublevel_upper hk c ε (⟨x, x.2⟩ : ClosedCell k) hε)

def cellAttachmentInclusion {n k : ℕ} (hk : k ≤ n) (c ε : ℝ) (hε : 0 ≤ ε) :
    lowerUnion hk c ε → upperSublevel hk c ε :=
  fun z =>
    ⟨z.1, cellAttachmentInclusion_mem hk c ε hε z⟩

def cellRetractionStep {n k : ℕ} (hk : k ≤ n) (t : ℝ) (y : MorseModel n) : MorseModel n :=
  recombine hk (negPart hk y) (t • posPart hk y)

theorem cellRetractionStep_decompose {n k : ℕ} (hk : k ≤ n) (y : MorseModel n) :
    cellRetractionStep hk 1 y = y := by
  dsimp [cellRetractionStep]
  rw [one_smul]
  exact recombine_decompose hk y

theorem cellRetractionStep_spine {n k : ℕ} (hk : k ≤ n) (y : MorseModel n) :
    cellRetractionStep hk 0 y = spineMap hk y := by
  dsimp [cellRetractionStep, spineMap]
  rw [zero_smul]

theorem cellRetractionStep_level {n k : ℕ} (hk : k ≤ n) (c : ℝ) {t : ℝ}
    (_ht0 : 0 ≤ t) (_ht1 : t ≤ 1) (y : MorseModel n) :
    morseNormalForm hk c (cellRetractionStep hk t y) =
      c + (1 / 2) * (t ^ 2 * ‖posPart hk y‖ ^ 2 - ‖negPart hk y‖ ^ 2) := by
  have hneg : negPart hk (cellRetractionStep hk t y) = negPart hk y := by
    ext i
    dsimp [cellRetractionStep, negPart]
    rw [recombine_negPart]
  have hpos : posPart hk (cellRetractionStep hk t y) = t • posPart hk y := by
    ext j
    dsimp [cellRetractionStep, posPart]
    rw [recombine_posPart]
    simp
  rw [morseNormalForm_split hk c (cellRetractionStep hk t y), hpos, hneg]
  rw [norm_smul, mul_pow]
  rw [Real.norm_eq_abs, sq_abs]

theorem cellRetractionStep_mem_upper {n k : ℕ} (hk : k ≤ n) (c ε : ℝ) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) {y : MorseModel n} (hy : y ∈ sublevel (morseNormalForm hk c) (c + ε)) :
    cellRetractionStep hk t y ∈ sublevel (morseNormalForm hk c) (c + ε) := by
  change morseNormalForm hk c (cellRetractionStep hk t y) ≤ c + ε
  rw [cellRetractionStep_level hk c ht0 ht1 y]
  have hle : t ^ 2 ≤ 1 := by nlinarith [sq_nonneg t, ht0, ht1]
  have hy' : morseNormalForm hk c y ≤ c + ε := by simpa [sublevel] using hy
  have hsplit := morseNormalForm_split hk c y
  rw [hsplit] at hy'
  nlinarith [sq_nonneg ‖negPart hk y‖, sq_nonneg ‖posPart hk y‖]

def cellRetractionHomotopyFun {n k : ℕ} (hk : k ≤ n) (c ε : ℝ) :
    Set.Icc (0 : ℝ) 1 × upperSublevel hk c ε → upperSublevel hk c ε :=
  fun p =>
    ⟨cellRetractionStep hk (p.1 : ℝ) p.2.1,
      cellRetractionStep_mem_upper hk c ε (t := p.1.1) (y := p.2.1) p.1.2.1 p.1.2.2 p.2.2⟩

theorem cellRetractionHomotopy_zero {n k : ℕ} (hk : k ≤ n) (c ε : ℝ) (hε : 0 < ε)
    (y : upperSublevel hk c ε) :
    cellRetractionHomotopyFun hk c ε (⟨0, by norm_num⟩, y) =
      cellAttachmentInclusion hk c ε (le_of_lt hε) (cellAttachmentMap hk c ε hε y) := by
  apply Subtype.ext
  dsimp [cellRetractionHomotopyFun, cellAttachmentInclusion, cellAttachmentMap]
  exact cellRetractionStep_spine hk y.1

theorem cellRetractionHomotopy_one {n k : ℕ} (hk : k ≤ n) (c ε : ℝ)
    (y : upperSublevel hk c ε) :
    cellRetractionHomotopyFun hk c ε (⟨1, by norm_num⟩, y) = y := by
  apply Subtype.ext
  dsimp [cellRetractionHomotopyFun]
  exact cellRetractionStep_decompose hk y.1

def cellInclusionStepFun {n k : ℕ} (hk : k ≤ n) (c ε : ℝ) :
    Set.Icc (0 : ℝ) 1 × lowerUnion hk c ε → lowerUnion hk c ε :=
  fun p =>
    ⟨cellRetractionStep hk (p.1 : ℝ) p.2.1, by
      rcases p.2.2 with hz | ⟨x, hx⟩
      · left
        change morseNormalForm hk c (cellRetractionStep hk (p.1 : ℝ) p.2.1) ≤ c - ε
        rw [cellRetractionStep_level hk c p.1.2.1 p.1.2.2 p.2.1]
        have hz' : morseNormalForm hk c p.2.1 ≤ c - ε := by simpa [sublevel] using hz
        have hsplit := morseNormalForm_split hk c p.2.1
        rw [hsplit] at hz'
        have hle : (p.1 : ℝ) ^ 2 ≤ 1 := by nlinarith [sq_nonneg (p.1 : ℝ), p.1.2.1, p.1.2.2]
        nlinarith [sq_nonneg ‖negPart hk p.2.1‖, sq_nonneg ‖posPart hk p.2.1‖]
      · right
        have hposz : posPart hk p.2.1 = 0 := by
          ext j
          rw [← hx]
          dsimp [posPart]
          exact cellMap_posIdx hk (Real.sqrt (2 * ε)) (x : EuclideanSpace ℝ (Fin k)) j
        have hstep : cellRetractionStep hk (p.1 : ℝ) p.2.1 = p.2.1 := by
          calc
            cellRetractionStep hk (p.1 : ℝ) p.2.1
                = recombine hk (negPart hk p.2.1) ((p.1 : ℝ) • posPart hk p.2.1) := rfl
            _ = recombine hk (negPart hk p.2.1) 0 := by rw [hposz, smul_zero]
            _ = recombine hk (negPart hk p.2.1) (posPart hk p.2.1) := by rw [hposz]
            _ = p.2.1 := recombine_decompose hk p.2.1
        rw [hstep]
        exact ⟨x, hx⟩⟩

theorem cellInclusionStep_mem {n k : ℕ} (hk : k ≤ n) (c ε : ℝ)
    (t : Set.Icc (0 : ℝ) 1) (z : lowerUnion hk c ε) :
    cellRetractionStep hk (t : ℝ) z.1 ∈ lowerCellUnion hk c ε := by
  dsimp [lowerCellUnion]
  rcases z.2 with hz | ⟨x, hx⟩
  · left
    change morseNormalForm hk c (cellRetractionStep hk (t : ℝ) z.1) ≤ c - ε
    rw [cellRetractionStep_level hk c t.2.1 t.2.2 z.1]
    have hz' : morseNormalForm hk c z.1 ≤ c - ε := by simpa [sublevel] using hz
    have hsplit := morseNormalForm_split hk c z.1
    rw [hsplit] at hz'
    have hle : (t : ℝ) ^ 2 ≤ 1 := by nlinarith [sq_nonneg (t : ℝ), t.2.1, t.2.2]
    nlinarith [sq_nonneg ‖negPart hk z.1‖, sq_nonneg ‖posPart hk z.1‖]
  · right
    have hposz : posPart hk z.1 = 0 := by
      ext j
      rw [← hx]
      dsimp [posPart]
      exact cellMap_posIdx hk (Real.sqrt (2 * ε)) (x : EuclideanSpace ℝ (Fin k)) j
    have hstep : cellRetractionStep hk (t : ℝ) z.1 = z.1 := by
      calc
        cellRetractionStep hk (t : ℝ) z.1
            = recombine hk (negPart hk z.1) ((t : ℝ) • posPart hk z.1) := rfl
        _ = recombine hk (negPart hk z.1) 0 := by rw [hposz, smul_zero]
        _ = recombine hk (negPart hk z.1) (posPart hk z.1) := by rw [hposz]
        _ = z.1 := recombine_decompose hk z.1
    rw [hstep]
    exact ⟨x, hx⟩

theorem cellInclusionStep_zero {n k : ℕ} (hk : k ≤ n) (c ε : ℝ) (hε : 0 < ε)
    (z : lowerUnion hk c ε) :
    cellInclusionStepFun hk c ε (⟨0, by norm_num⟩, z) =
      cellAttachmentMap hk c ε hε (cellAttachmentInclusion hk c ε (le_of_lt hε) z) := by
  apply Subtype.ext
  dsimp [cellInclusionStepFun, cellAttachmentMap, cellAttachmentInclusion]
  exact cellRetractionStep_spine hk z.1

theorem cellInclusionStep_one {n k : ℕ} (hk : k ≤ n) (c ε : ℝ)
    (z : lowerUnion hk c ε) :
    cellInclusionStepFun hk c ε (⟨1, by norm_num⟩, z) = z := by
  apply Subtype.ext
  dsimp [cellInclusionStepFun]
  exact cellRetractionStep_decompose hk z.1

theorem continuous_negPart {n k : ℕ} (hk : k ≤ n) :
    Continuous (fun y : MorseModel n => negPart hk y) := by
  dsimp [negPart]
  have hpi : Continuous (fun y : MorseModel n => (fun i : Fin k => y (negIdx hk i))) :=
    continuous_pi (fun i => continuous_apply (negIdx hk i))
  exact (PiLp.continuous_toLp (p := (2 : ENNReal)) (β := fun _ : Fin k => ℝ)).comp hpi

theorem continuous_posPart {n k : ℕ} (hk : k ≤ n) :
    Continuous (fun y : MorseModel n => posPart hk y) := by
  dsimp [posPart]
  have hpi : Continuous (fun y : MorseModel n => (fun j : Fin (n - k) => y (posIdx hk j))) :=
    continuous_pi (fun j => continuous_apply (posIdx hk j))
  exact (PiLp.continuous_toLp (p := (2 : ENNReal)) (β := fun _ : Fin (n - k) => ℝ)).comp hpi

theorem continuous_recombine {n k : ℕ} (hk : k ≤ n) :
    Continuous (fun p : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin (n - k)) =>
      recombine hk p.1 p.2) := by
  rw [continuous_iff_continuousAt]
  intro p
  rw [continuousAt_pi]
  intro i
  by_cases hi : i.val < k
  · have hfun : (fun q : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin (n - k)) =>
        recombine hk q.1 q.2 i) = fun q => q.1 ⟨i.val, hi⟩ := by
      funext q
      dsimp [recombine]
      rw [dif_pos hi]
    rw [hfun]
    exact (PiLp.continuous_apply (p := (2 : ENNReal)) (β := fun _ : Fin k => ℝ)
      ⟨i.val, hi⟩).continuousAt.comp continuous_fst.continuousAt
  · have hproof : i.val - k < n - k := by
      have hkle : k ≤ i.val := le_of_not_gt hi
      have hii : i.val < n := i.isLt
      omega
    have hfun : (fun q : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin (n - k)) =>
        recombine hk q.1 q.2 i) = fun q => q.2 ⟨i.val - k, hproof⟩ := by
      funext q
      dsimp [recombine]
      rw [dif_neg hi]
    rw [hfun]
    exact (PiLp.continuous_apply (p := (2 : ENNReal)) (β := fun _ : Fin (n - k) => ℝ)
      ⟨i.val - k, hproof⟩).continuousAt.comp continuous_snd.continuousAt

theorem continuous_cellRetractionStep {n k : ℕ} (hk : k ≤ n) :
    Continuous (fun p : Set.Icc (0 : ℝ) 1 × MorseModel n =>
      cellRetractionStep hk (p.1 : ℝ) p.2) := by
  dsimp [cellRetractionStep]
  have hneg' : Continuous (fun p : Set.Icc (0 : ℝ) 1 × MorseModel n => negPart hk p.2) :=
    (continuous_negPart hk).comp continuous_snd
  have hpair1 : Continuous (fun p : Set.Icc (0 : ℝ) 1 × MorseModel n =>
      ((p.1 : ℝ), posPart hk p.2)) :=
    (continuous_subtype_val.comp continuous_fst).prodMk
      ((continuous_posPart hk).comp continuous_snd)
  have hsmul : Continuous (fun p : ℝ × EuclideanSpace ℝ (Fin (n - k)) => p.1 • p.2) :=
    continuous_smul
  have hpos' : Continuous (fun p : Set.Icc (0 : ℝ) 1 × MorseModel n =>
      (p.1 : ℝ) • posPart hk p.2) := hsmul.comp hpair1
  have hcomp : Continuous (fun p : Set.Icc (0 : ℝ) 1 × MorseModel n =>
      (negPart hk p.2, (p.1 : ℝ) • posPart hk p.2)) := by
    exact hneg'.prodMk hpos'
  exact continuous_recombine hk |>.comp hcomp

theorem continuous_spineMap {n k : ℕ} (hk : k ≤ n) :
    Continuous (fun y : MorseModel n => spineMap hk y) := by
  dsimp [spineMap]
  exact continuous_recombine hk |>.comp ((continuous_negPart hk).prodMk continuous_const)

theorem continuous_cellMap {n k : ℕ} (r : ℝ) :
    Continuous (fun x : ClosedCell k => (cellMap r (x : EuclideanSpace ℝ (Fin k)) : MorseModel n)) := by
  rw [continuous_iff_continuousAt]
  intro x
  rw [continuousAt_pi]
  intro i
  by_cases hi : i.val < k
  · have hfun : (fun q : ClosedCell k => cellMap r (q : EuclideanSpace ℝ (Fin k)) i) =
        fun q : ClosedCell k => r * (q : EuclideanSpace ℝ (Fin k)) ⟨i.val, hi⟩ := by
      funext q
      dsimp [cellMap]
      rw [dif_pos hi]
    rw [hfun]
    exact ((continuous_const.mul (PiLp.continuous_apply (p := (2 : ENNReal)) (β := fun _ : Fin k => ℝ)
      ⟨i.val, hi⟩)).comp continuous_subtype_val).continuousAt
  · have hfun : (fun q : ClosedCell k => cellMap r (q : EuclideanSpace ℝ (Fin k)) i) =
      fun _ => 0 := by
      funext q
      dsimp [cellMap]
      rw [dif_neg hi]
    rw [hfun]
    exact continuous_const.continuousAt

theorem cellMap_injective {n k : ℕ} (hk : k ≤ n) (ε : ℝ) (hε : 0 < ε) :
    Function.Injective (fun x : ClosedCell k =>
      (cellMap (Real.sqrt (2 * ε)) (x : EuclideanSpace ℝ (Fin k)) : MorseModel n)) := by
  intro x y hxy
  apply Subtype.ext
  ext i
  have hx : cellMap (Real.sqrt (2 * ε)) (x : EuclideanSpace ℝ (Fin k)) (negIdx hk i) =
      cellMap (Real.sqrt (2 * ε)) (y : EuclideanSpace ℝ (Fin k)) (negIdx hk i) := by
    exact congrFun hxy (negIdx hk i)
  rw [cellMap_negIdx, cellMap_negIdx] at hx
  have hr : Real.sqrt (2 * ε) ≠ 0 := by
    exact (Real.sqrt_pos.2 (by positivity : 0 < 2 * ε)).ne'
  exact mul_left_cancel₀ hr hx

theorem cellInterior_disjoint {n k : ℕ} (hk : k ≤ n) (c ε : ℝ) (hε : 0 < ε) :
    Disjoint ((fun x : ClosedCell k => cellMap (Real.sqrt (2 * ε)) (x : EuclideanSpace ℝ (Fin k))) ''
      Set.range (cellInteriorInclusion k))
      (sublevel (morseNormalForm hk c) (c - ε)) := by
  rw [Set.disjoint_left]
  intro y hyA hyB
  rcases hyA with ⟨x, hx, hxy⟩
  rcases hx with ⟨z, hz⟩
  have hxlt : ‖(x : EuclideanSpace ℝ (Fin k))‖ < 1 := by
    have hzval : (x : EuclideanSpace ℝ (Fin k)) = (z : EuclideanSpace ℝ (Fin k)) := by
      simpa [cellInteriorInclusion] using
        (congrArg (fun w : ClosedCell k => (w : EuclideanSpace ℝ (Fin k))) hz).symm
    rw [hzval]
    exact z.2
  have hf : morseNormalForm hk c y = c + (1 / 2) * (-((Real.sqrt (2 * ε)) ^ 2) * ‖(x : EuclideanSpace ℝ (Fin k))‖ ^ 2) := by
    rw [← hxy]
    exact morseNormalForm_cellMap hk c (Real.sqrt (2 * ε)) (x : EuclideanSpace ℝ (Fin k))
  have hsq : (Real.sqrt (2 * ε)) ^ 2 = 2 * ε := by
    rw [Real.sq_sqrt (by positivity : 0 ≤ 2 * ε)]
  have hgt : c - ε < morseNormalForm hk c y := by
    rw [hf, hsq]
    have hxlt2 : ‖(x : EuclideanSpace ℝ (Fin k))‖ ^ 2 < 1 := by
      have habs : |‖(x : EuclideanSpace ℝ (Fin k))‖| < |(1 : ℝ)| := by
        simpa [abs_of_nonneg, abs_one] using hxlt
      simpa using (sq_lt_sq.mpr habs)
    nlinarith [hxlt2, hε]
  have hle : morseNormalForm hk c y ≤ c - ε := by simpa [sublevel] using hyB
  linarith

theorem isClosed_sublevel_normalForm {n k : ℕ} (hk : k ≤ n) (c a : ℝ) :
    IsClosed (sublevel (morseNormalForm hk c) a) := by
  have hcont : Continuous (morseNormalForm hk c) := by
    rw [show morseNormalForm hk c = fun y => c + (1 / 2) * (‖posPart hk y‖ ^ 2 - ‖negPart hk y‖ ^ 2) by
      funext y
      exact morseNormalForm_split hk c y]
    have hposc : Continuous (fun y : MorseModel n => ‖posPart hk y‖ ^ 2) :=
      (continuous_norm.comp (continuous_posPart hk)).pow 2
    have hnegc : Continuous (fun y : MorseModel n => ‖negPart hk y‖ ^ 2) :=
      (continuous_norm.comp (continuous_negPart hk)).pow 2
    exact (continuous_const.add ((continuous_const.mul (hposc.sub hnegc))))
  exact (isClosed_Iic.preimage hcont)

instance closedCellCompactSpace (k : ℕ) : CompactSpace (ClosedCell k) := by
  let f : ClosedCell k → Metric.closedBall (0 : EuclideanSpace ℝ (Fin k)) 1 :=
    fun x => ⟨(x : EuclideanSpace ℝ (Fin k)), by simpa [Metric.mem_closedBall, dist_eq_norm] using x.2⟩
  let g : Metric.closedBall (0 : EuclideanSpace ℝ (Fin k)) 1 → ClosedCell k :=
    fun y => ⟨(y : EuclideanSpace ℝ (Fin k)), by
      have hy : ‖(y : EuclideanSpace ℝ (Fin k))‖ ≤ 1 := by
        have hmem : dist (y : EuclideanSpace ℝ (Fin k)) 0 ≤ 1 := y.2
        simpa [dist_eq_norm] using hmem
      exact hy⟩
  let e : ClosedCell k ≃ₜ Metric.closedBall (0 : EuclideanSpace ℝ (Fin k)) 1 :=
    { toEquiv :=
        { toFun := f
          invFun := g
          left_inv := by intro x; apply Subtype.ext; rfl
          right_inv := by intro y; apply Subtype.ext; rfl }
      continuous_toFun := by
        have hcomp : (fun x : ClosedCell k =>
            ((f x : Metric.closedBall (0 : EuclideanSpace ℝ (Fin k)) 1) : EuclideanSpace ℝ (Fin k))) =
            fun x : ClosedCell k => (x : EuclideanSpace ℝ (Fin k)) := by
          funext x
          rfl
        exact (Topology.IsInducing.subtypeVal.continuous_iff).2 (by
          change Continuous (fun x : ClosedCell k =>
            ((f x : Metric.closedBall (0 : EuclideanSpace ℝ (Fin k)) 1) : EuclideanSpace ℝ (Fin k)))
          rw [hcomp]
          exact continuous_subtype_val)
      continuous_invFun := by
        have hcomp : (fun y : Metric.closedBall (0 : EuclideanSpace ℝ (Fin k)) 1 =>
            ((g y : ClosedCell k) : EuclideanSpace ℝ (Fin k))) =
            fun y : Metric.closedBall (0 : EuclideanSpace ℝ (Fin k)) 1 => (y : EuclideanSpace ℝ (Fin k)) := by
          funext y
          rfl
        exact (Topology.IsInducing.subtypeVal.continuous_iff).2 (by
          change Continuous (fun y : Metric.closedBall (0 : EuclideanSpace ℝ (Fin k)) 1 =>
            ((g y : ClosedCell k) : EuclideanSpace ℝ (Fin k)))
          rw [hcomp]
          exact continuous_subtype_val) }
  exact e.symm.compactSpace

theorem continuous_cellAttachmentMap {n k : ℕ} (hk : k ≤ n) (c ε : ℝ) (hε : 0 < ε) :
    Continuous (cellAttachmentMap hk c ε hε) := by
  have h : Continuous (fun y : upperSublevel hk c ε => spineMap hk y.1) :=
    (continuous_spineMap hk).comp continuous_subtype_val
  have hcomp : (fun y : upperSublevel hk c ε =>
      ((cellAttachmentMap hk c ε hε y : lowerUnion hk c ε) : MorseModel n)) =
      fun y => spineMap hk y.1 := by
    funext y
    rfl
  exact (Topology.IsInducing.subtypeVal.continuous_iff).2 (by simpa [hcomp] using h)

theorem continuous_cellAttachmentInclusion {n k : ℕ} (hk : k ≤ n) (c ε : ℝ) (hε : 0 ≤ ε) :
    Continuous (cellAttachmentInclusion hk c ε hε) := by
  have hcomp : (fun z : lowerUnion hk c ε =>
      ((cellAttachmentInclusion hk c ε hε z : upperSublevel hk c ε) : MorseModel n)) =
      fun z : lowerUnion hk c ε => (z : MorseModel n) := by
    funext z
    rfl
  exact (Topology.IsInducing.subtypeVal.continuous_iff).2
    (by simpa [hcomp] using
      (continuous_subtype_val : Continuous (fun z : lowerUnion hk c ε => (z : MorseModel n))))

theorem continuous_cellRetractionHomotopyFun {n k : ℕ} (hk : k ≤ n) (c ε : ℝ) :
    Continuous (cellRetractionHomotopyFun hk c ε) := by
  have hpair : Continuous (fun p : Set.Icc (0 : ℝ) 1 × upperSublevel hk c ε =>
      (p.1, p.2.1)) :=
    continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)
  have h : Continuous (fun p : Set.Icc (0 : ℝ) 1 × upperSublevel hk c ε =>
      cellRetractionStep hk (p.1 : ℝ) p.2.1) :=
    continuous_cellRetractionStep hk |>.comp hpair
  have hcomp : (fun p : Set.Icc (0 : ℝ) 1 × upperSublevel hk c ε =>
      ((cellRetractionHomotopyFun hk c ε p : upperSublevel hk c ε) : MorseModel n)) =
      fun p => cellRetractionStep hk (p.1 : ℝ) p.2.1 := by
    funext p
    rfl
  exact (Topology.IsInducing.subtypeVal.continuous_iff).2 (by simpa [hcomp] using h)

theorem continuous_cellInclusionStepFun {n k : ℕ} (hk : k ≤ n) (c ε : ℝ) :
    Continuous (cellInclusionStepFun hk c ε) := by
  have hpair : Continuous (fun p : Set.Icc (0 : ℝ) 1 × lowerUnion hk c ε =>
      (p.1, p.2.1)) :=
    continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)
  have h : Continuous (fun p : Set.Icc (0 : ℝ) 1 × lowerUnion hk c ε =>
      cellRetractionStep hk (p.1 : ℝ) p.2.1) :=
    continuous_cellRetractionStep hk |>.comp hpair
  have hcomp : (fun p : Set.Icc (0 : ℝ) 1 × lowerUnion hk c ε =>
      ((cellInclusionStepFun hk c ε p : lowerUnion hk c ε) : MorseModel n)) =
      fun p => cellRetractionStep hk (p.1 : ℝ) p.2.1 := by
    funext p
    rfl
  exact (Topology.IsInducing.subtypeVal.continuous_iff).2 (by simpa [hcomp] using h)

private noncomputable def cellAttachmentMapC {n k : ℕ} (hk : k ≤ n) (c ε : ℝ) (hε : 0 < ε) :
    C(upperSublevel hk c ε, lowerUnion hk c ε) :=
  ⟨cellAttachmentMap hk c ε hε, continuous_cellAttachmentMap hk c ε hε⟩

private noncomputable def cellAttachmentInclusionC {n k : ℕ} (hk : k ≤ n) (c ε : ℝ) (hε : 0 ≤ ε) :
    C(lowerUnion hk c ε, upperSublevel hk c ε) :=
  ⟨cellAttachmentInclusion hk c ε hε, continuous_cellAttachmentInclusion hk c ε hε⟩

noncomputable def cellRetractionHomotopy {n k : ℕ} (hk : k ≤ n) (c ε : ℝ) (hε : 0 < ε) :
    ContinuousMap.Homotopy
      ((cellAttachmentInclusionC hk c ε (le_of_lt hε)).comp (cellAttachmentMapC hk c ε hε))
      (ContinuousMap.id (upperSublevel hk c ε)) where
  toFun := ContinuousMap.mk (cellRetractionHomotopyFun hk c ε) (continuous_cellRetractionHomotopyFun hk c ε)
  map_zero_left := by
    intro y
    exact cellRetractionHomotopy_zero hk c ε hε y
  map_one_left := by
    intro y
    exact cellRetractionHomotopy_one hk c ε y

noncomputable def cellInclusionHomotopy {n k : ℕ} (hk : k ≤ n) (c ε : ℝ) (hε : 0 < ε) :
    ContinuousMap.Homotopy
      ((cellAttachmentMapC hk c ε hε).comp (cellAttachmentInclusionC hk c ε (le_of_lt hε)))
      (ContinuousMap.id (lowerUnion hk c ε)) where
  toFun := ContinuousMap.mk (cellInclusionStepFun hk c ε) (continuous_cellInclusionStepFun hk c ε)
  map_zero_left := by
    intro z
    exact cellInclusionStep_zero hk c ε hε z
  map_one_left := by
    intro z
    exact cellInclusionStep_one hk c ε z

noncomputable def cellAttachmentHomotopyEquiv {n k : ℕ} (hk : k ≤ n) (c ε : ℝ) (hε : 0 < ε) :
    ContinuousMap.HomotopyEquiv (upperSublevel hk c ε) (lowerUnion hk c ε) where
  toFun := cellAttachmentMapC hk c ε hε
  invFun := cellAttachmentInclusionC hk c ε (le_of_lt hε)
  left_inv := ⟨cellRetractionHomotopy hk c ε hε⟩
  right_inv := ⟨cellInclusionHomotopy hk c ε hε⟩

noncomputable def cellAttachmentAdjunctionHomeo {n k : ℕ} (hk : k ≤ n) (c ε : ℝ) (hε : 0 < ε) :
    CellAdjunctionSpace k (attachMap hk c ε (le_of_lt hε)) ≃ₜ lowerUnion hk c ε := by
  refine cellAdjunctionHomeomorphUnionImage (n := k) (φ := attachMap hk c ε (le_of_lt hε))
    (c := fun x : ClosedCell k => cellMap (Real.sqrt (2 * ε)) (x : EuclideanSpace ℝ (Fin k)))
    ?hφ ?hc ?hcont ?hinterior ?hclosed
  · intro b
    rfl
  · exact cellMap_injective hk ε hε
  · exact continuous_cellMap (Real.sqrt (2 * ε))
  · exact cellInterior_disjoint hk c ε hε
  · exact isClosed_sublevel_normalForm hk c (c - ε)

noncomputable def cellAttachmentModel {n k : ℕ} (hk : k ≤ n) (c ε : ℝ) (hε : 0 < ε) :
    ContinuousMap.HomotopyEquiv (upperSublevel hk c ε)
      (CellAdjunctionSpace k (attachMap hk c ε (le_of_lt hε))) :=
  (cellAttachmentHomotopyEquiv hk c ε hε).trans
    (cellAttachmentAdjunctionHomeo hk c ε hε).symm.toHomotopyEquiv

abbrev morseNorm (n : ℕ) (y : MorseModel n) : ℝ :=
  ‖(WithLp.toLp 2 y : EuclideanSpace ℝ (Fin n))‖

theorem morseNorm_piNorm_le {n : ℕ} (y : MorseModel n) : ‖y‖ ≤ morseNorm n y := by
  exact (pi_norm_le_iff_of_nonneg (ι := Fin n) (x := y) (r := morseNorm n y)
      (norm_nonneg _)).mpr (by
    intro i
    have h := PiLp.norm_apply_le (p := 2) (x := WithLp.toLp 2 y) i
    simpa [morseNorm] using h)

theorem sum_split_fin {n k : ℕ} (hk : k ≤ n) (f : Fin n → ℝ) :
    (∑ i : Fin n, f i) =
      (∑ i : Fin k, f (negIdx hk i)) + (∑ j : Fin (n - k), f (posIdx hk j)) := by
  let e : Sum (Fin k) (Fin (n - k)) ≃ Fin n :=
    { toFun := Sum.elim (negIdx hk) (posIdx hk)
      invFun := fun z => if h : z.val < k then Sum.inl ⟨z.val, h⟩ else Sum.inr ⟨z.val - k, by
        have hkle : k ≤ z.val := le_of_not_gt h
        have hz : z.val < n := z.isLt
        omega⟩
      left_inv := by
        intro s
        cases s with
        | inl i =>
            simp [negIdx]
        | inr j =>
            simp [posIdx]
      right_inv := by
        intro z
        by_cases h : z.val < k
        · simp [h, negIdx]
        · apply Fin.ext
          simp [h, posIdx]
          omega }
  calc
    (∑ i : Fin n, f i) = ∑ s : Sum (Fin k) (Fin (n - k)), f (e s) := by
      symm
      exact Fintype.sum_equiv e (fun s : Sum (Fin k) (Fin (n - k)) => f (e s))
        (fun i : Fin n => f i) (by intro s; rfl)
    _ = (∑ i : Fin k, f (e (Sum.inl i))) + (∑ j : Fin (n - k), f (e (Sum.inr j))) := by
      rw [Fintype.sum_sum_type]
    _ = (∑ i : Fin k, f (negIdx hk i)) + (∑ j : Fin (n - k), f (posIdx hk j)) := by
      simp [e]

private theorem morseNorm_sq_recombine {n k : ℕ} (hk : k ≤ n)
    (a : EuclideanSpace ℝ (Fin k)) (b : EuclideanSpace ℝ (Fin (n - k))) :
    morseNorm n (recombine hk a b) ^ 2 = ‖a‖ ^ 2 + ‖b‖ ^ 2 := by
  have h1 : morseNorm n (recombine hk a b) ^ 2 = ∑ i : Fin n, ((recombine hk a b) i) ^ 2 := by
    simpa [morseNorm] using (EuclideanSpace.real_norm_sq_eq (WithLp.toLp 2 (recombine hk a b)))
  have h2 : ‖a‖ ^ 2 = ∑ i : Fin k, (a i) ^ 2 := by
    simpa using (EuclideanSpace.real_norm_sq_eq a)
  have h3 : ‖b‖ ^ 2 = ∑ j : Fin (n - k), (b j) ^ 2 := by
    simpa using (EuclideanSpace.real_norm_sq_eq b)
  rw [h1, h2, h3]
  rw [sum_split_fin hk (fun i : Fin n => ((recombine hk a b) i) ^ 2)]
  congr 1
  · apply Finset.sum_congr rfl
    intro i hi
    rw [recombine_negPart]
  · apply Finset.sum_congr rfl
    intro j hj
    rw [recombine_posPart]

private theorem morseNorm_le_of_sq_le {n : ℕ} {y z : MorseModel n}
    (h : morseNorm n y ^ 2 ≤ morseNorm n z ^ 2) : morseNorm n y ≤ morseNorm n z := by
  have habs := sq_le_sq.mp h
  have h1 : |morseNorm n y| = morseNorm n y := abs_of_nonneg (norm_nonneg _)
  have h2 : |morseNorm n z| = morseNorm n z := abs_of_nonneg (norm_nonneg _)
  simpa [h1, h2] using habs

theorem norm_spineMap_le {n k : ℕ} (hk : k ≤ n) (y : MorseModel n) :
    morseNorm n (spineMap hk y) ≤ morseNorm n y := by
  apply morseNorm_le_of_sq_le
  rw [show spineMap hk y = recombine hk (negPart hk y) 0 by rfl]
  rw [morseNorm_sq_recombine hk (negPart hk y) (0 : EuclideanSpace ℝ (Fin (n - k)))]
  conv_rhs => rw [← recombine_decompose hk y]
  rw [morseNorm_sq_recombine hk (negPart hk y) (posPart hk y)]
  have hz : ‖(0 : EuclideanSpace ℝ (Fin (n - k)))‖ ^ 2 = 0 := by simp
  nlinarith [sq_nonneg ‖posPart hk y‖, hz]

theorem norm_cellRetractionStep_le {n k : ℕ} (hk : k ≤ n) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (y : MorseModel n) : morseNorm n (cellRetractionStep hk t y) ≤ morseNorm n y := by
  apply morseNorm_le_of_sq_le
  rw [show cellRetractionStep hk t y = recombine hk (negPart hk y) (t • posPart hk y) by rfl]
  rw [morseNorm_sq_recombine hk (negPart hk y) (t • posPart hk y)]
  conv_rhs => rw [← recombine_decompose hk y]
  rw [morseNorm_sq_recombine hk (negPart hk y) (posPart hk y)]
  have ht2 : t ^ 2 ≤ 1 := by nlinarith [sq_nonneg t, ht0, ht1]
  have hts : ‖t • posPart hk y‖ ^ 2 ≤ ‖posPart hk y‖ ^ 2 := by
    calc
      ‖t • posPart hk y‖ ^ 2 = ‖t‖ ^ 2 * ‖posPart hk y‖ ^ 2 := by
        rw [norm_smul, mul_pow]
      _ = t ^ 2 * ‖posPart hk y‖ ^ 2 := by
        rw [Real.norm_eq_abs, abs_of_nonneg ht0]
      _ ≤ 1 * ‖posPart hk y‖ ^ 2 := by
        exact mul_le_mul_of_nonneg_right ht2 (sq_nonneg _)
      _ = ‖posPart hk y‖ ^ 2 := by rw [one_mul]
  nlinarith [sq_nonneg ‖negPart hk y‖]

theorem norm_cellMap_le {n k : ℕ} (hk : k ≤ n) (ε R : ℝ) (hR : Real.sqrt (2 * ε) ≤ R)
    (x : EuclideanSpace ℝ (Fin k)) (hx : ‖x‖ ≤ 1) : morseNorm n (cellMap (Real.sqrt (2 * ε)) x) ≤ R := by
  have hsq : morseNorm n (cellMap (Real.sqrt (2 * ε)) x) ^ 2 ≤ (Real.sqrt (2 * ε)) ^ 2 := by
    have h1 : morseNorm n (cellMap (Real.sqrt (2 * ε)) x) ^ 2 =
        ∑ i : Fin n, ((cellMap (Real.sqrt (2 * ε)) x) i) ^ 2 := by
      simpa [morseNorm] using
        (EuclideanSpace.real_norm_sq_eq (WithLp.toLp 2 (cellMap (Real.sqrt (2 * ε)) x)))
    rw [h1]
    rw [sum_split_fin hk (fun i : Fin n => ((cellMap (Real.sqrt (2 * ε)) x) i) ^ 2)]
    have hneg : (∑ i : Fin k, ((cellMap (Real.sqrt (2 * ε)) x) (negIdx hk i)) ^ 2) ≤
        (Real.sqrt (2 * ε)) ^ 2 * ‖x‖ ^ 2 := by
      calc
        (∑ i : Fin k, ((cellMap (Real.sqrt (2 * ε)) x) (negIdx hk i)) ^ 2)
            = (∑ i : Fin k, (Real.sqrt (2 * ε) * x i) ^ 2) := by
              apply Finset.sum_congr rfl
              intro i hi
              rw [cellMap_negIdx]
        _ ≤ (Real.sqrt (2 * ε)) ^ 2 * ‖x‖ ^ 2 := by
          rw [EuclideanSpace.real_norm_sq_eq x]
          rw [Finset.mul_sum]
          apply Finset.sum_le_sum
          intro i hi
          exact le_of_eq (mul_pow (Real.sqrt (2 * ε)) (x i) 2)
    have hpos : (∑ j : Fin (n - k), ((cellMap (Real.sqrt (2 * ε)) x) (posIdx hk j)) ^ 2) = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      rw [cellMap_posIdx]
      norm_num
    have hx2 : ‖x‖ ^ 2 ≤ 1 := by
      rw [pow_two]
      simpa using (mul_le_mul hx hx (norm_nonneg x) (zero_le_one))
    rw [hpos]
    have hx : (Real.sqrt (2 * ε)) ^ 2 * ‖x‖ ^ 2 ≤ (Real.sqrt (2 * ε)) ^ 2 := by
      simpa using (mul_le_mul_of_nonneg_left hx2 (sq_nonneg (Real.sqrt (2 * ε))))
    nlinarith [hneg, hx, hx2]
  have hnorm : morseNorm n (cellMap (Real.sqrt (2 * ε)) x) ≤ Real.sqrt (2 * ε) := by
    calc
      morseNorm n (cellMap (Real.sqrt (2 * ε)) x)
          = |morseNorm n (cellMap (Real.sqrt (2 * ε)) x)| := by
            rw [abs_of_nonneg (norm_nonneg _)]
      _ ≤ |Real.sqrt (2 * ε)| := sq_le_sq.mp hsq
      _ = Real.sqrt (2 * ε) := abs_of_nonneg (Real.sqrt_nonneg (2 * ε))
  exact le_trans hnorm hR

theorem morseNorm_sq_eq_negPart_add_posPart {n k : ℕ} (hk : k ≤ n) (y : MorseModel n) :
    morseNorm n y ^ 2 = ‖negPart hk y‖ ^ 2 + ‖posPart hk y‖ ^ 2 := by
  have h1 : morseNorm n y ^ 2 = ∑ i : Fin n, (y i) ^ 2 := by
    dsimp [morseNorm]
    simpa using (EuclideanSpace.real_norm_sq_eq (WithLp.toLp 2 y : EuclideanSpace ℝ (Fin n)))
  have h2 : ‖negPart hk y‖ ^ 2 = ∑ i : Fin k, (negPart hk y i) ^ 2 := by
    simpa using (EuclideanSpace.real_norm_sq_eq (negPart hk y))
  have h3 : ‖posPart hk y‖ ^ 2 = ∑ j : Fin (n - k), (posPart hk y j) ^ 2 := by
    simpa using (EuclideanSpace.real_norm_sq_eq (posPart hk y))
  rw [h1, h2, h3]
  rw [sum_split_fin hk (fun i : Fin n => (y i) ^ 2)]
  have hk_eq : (∑ i : Fin k, (y (negIdx hk i)) ^ 2) = ∑ i : Fin k, (negPart hk y i) ^ 2 := by
    apply Finset.sum_congr rfl
    intro i hi
    rfl
  have hp_eq : (∑ j : Fin (n - k), (y (posIdx hk j)) ^ 2) =
      ∑ j : Fin (n - k), (posPart hk y j) ^ 2 := by
    apply Finset.sum_congr rfl
    intro j hj
    rfl
  rw [hk_eq, hp_eq]

theorem norm_negPart_cellMap {n k : ℕ} (hk : k ≤ n) (r : ℝ)
    (u : EuclideanSpace ℝ (Fin k)) :
    ‖negPart hk (cellMap r u)‖ ^ 2 = r ^ 2 * ‖u‖ ^ 2 := by
  have hsum : (∑ i : Fin k, (negPart hk (cellMap r u) i) ^ 2) = r ^ 2 * ∑ i : Fin k, (u i) ^ 2 := by
    calc
      (∑ i : Fin k, (negPart hk (cellMap r u) i) ^ 2)
          = ∑ i : Fin k, ((cellMap r u) (negIdx hk i)) ^ 2 := by
            apply Finset.sum_congr rfl
            intro i hi
            rfl
      _ = ∑ i : Fin k, (r * u i) ^ 2 := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [cellMap_negIdx]
      _ = r ^ 2 * ∑ i : Fin k, (u i) ^ 2 := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i hi
            rw [mul_pow]
  calc
    ‖negPart hk (cellMap r u)‖ ^ 2 = ∑ i : Fin k, (negPart hk (cellMap r u) i) ^ 2 := by
      simpa using (EuclideanSpace.real_norm_sq_eq (negPart hk (cellMap r u)))
    _ = r ^ 2 * ∑ i : Fin k, (u i) ^ 2 := hsum
    _ = r ^ 2 * ‖u‖ ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq u]

theorem negPart_recombine {n k : ℕ} (hk : k ≤ n) (a : EuclideanSpace ℝ (Fin k))
    (b : EuclideanSpace ℝ (Fin (n - k))) :
    negPart hk (recombine hk a b) = a := by
  ext i
  simpa using (recombine_negPart hk a b i)

theorem posPart_recombine {n k : ℕ} (hk : k ≤ n) (a : EuclideanSpace ℝ (Fin k))
    (b : EuclideanSpace ℝ (Fin (n - k))) :
    posPart hk (recombine hk a b) = b := by
  ext j
  simpa using (recombine_posPart hk a b j)

theorem recombine_contDiff {n k : ℕ} (hk : k ≤ n) (r ε : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞)
      (fun p : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin (n - k)) =>
        recombine hk (negPart hk (cellMap (Real.sqrt (2 * ε)) p.1)) (r • p.2)) := by
  rw [contDiff_pi]
  intro i
  by_cases hi : i.val < k
  · have hcomp : (fun p : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin (n - k)) =>
        recombine hk (negPart hk (cellMap (Real.sqrt (2 * ε)) p.1)) (r • p.2) i) =
        fun p : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin (n - k)) =>
          Real.sqrt (2 * ε) * p.1 ⟨i.val, hi⟩ := by
      funext p
      have hrew : recombine hk (negPart hk (cellMap (Real.sqrt (2 * ε)) p.1)) (r • p.2) i =
          (negPart hk (cellMap (Real.sqrt (2 * ε)) p.1)) ⟨i.val, hi⟩ := by
        dsimp [recombine]
        rw [dif_pos hi]
      rw [hrew]
      exact negPart_cellMap_apply hk (Real.sqrt (2 * ε)) p.1 ⟨i.val, hi⟩
    rw [hcomp]
    fun_prop
  · have hcomp : (fun p : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin (n - k)) =>
        recombine hk (negPart hk (cellMap (Real.sqrt (2 * ε)) p.1)) (r • p.2) i) =
        fun p : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin (n - k)) =>
          r * p.2 ⟨i.val - k, by
            have hkle : k ≤ i.val := le_of_not_gt hi
            have hi' : i.val < n := i.isLt
            omega⟩ := by
      funext p
      dsimp [recombine]
      rw [dif_neg hi]
    rw [hcomp]
    fun_prop

theorem recombine_contDiff_cocore {n k : ℕ} (hk : k ≤ n) (r ε : ℝ) (hε : 0 < ε) :
    ContDiff ℝ (⊤ : ℕ∞)
      (fun p : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin (n - k)) =>
        recombine hk (negPart hk (cellMap (Real.sqrt (2 * ε + r ^ 2 * ‖p.2‖ ^ 2)) p.1)) (r • p.2)) := by
  rw [contDiff_pi]
  intro i
  by_cases hi : i.val < k
  · have hcomp : (fun p : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin (n - k)) =>
        recombine hk (negPart hk (cellMap (Real.sqrt (2 * ε + r ^ 2 * ‖p.2‖ ^ 2)) p.1)) (r • p.2) i) =
        fun p : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin (n - k)) =>
          Real.sqrt (2 * ε + r ^ 2 * ‖p.2‖ ^ 2) * p.1 ⟨i.val, hi⟩ := by
      funext p
      have hrew : recombine hk (negPart hk (cellMap (Real.sqrt (2 * ε + r ^ 2 * ‖p.2‖ ^ 2)) p.1))
            (r • p.2) i = (negPart hk (cellMap (Real.sqrt (2 * ε + r ^ 2 * ‖p.2‖ ^ 2)) p.1))
            ⟨i.val, hi⟩ := by
        dsimp [recombine]
        rw [dif_pos hi]
      rw [hrew]
      exact negPart_cellMap_apply hk (Real.sqrt (2 * ε + r ^ 2 * ‖p.2‖ ^ 2)) p.1 ⟨i.val, hi⟩
    rw [hcomp]
    have harg : ContDiff ℝ (⊤ : ℕ∞)
        (fun p : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin (n - k)) =>
          2 * ε + r ^ 2 * ‖p.2‖ ^ 2) := by
      have hnorm2 : ContDiff ℝ (⊤ : ℕ∞)
          (fun p : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin (n - k)) =>
            ‖p.2‖ ^ 2) := (contDiff_norm_sq ℝ).comp contDiff_snd
      exact contDiff_const.add (contDiff_const.mul hnorm2)
    have hsqrt : ContDiff ℝ (⊤ : ℕ∞)
        (fun p : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin (n - k)) =>
          Real.sqrt (2 * ε + r ^ 2 * ‖p.2‖ ^ 2)) :=
      harg.sqrt (by intro p; positivity)
    have hcoord : ContDiff ℝ (⊤ : ℕ∞)
        (fun p : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin (n - k)) =>
          p.1 ⟨i.val, hi⟩) := by
      fun_prop
    exact hsqrt.mul hcoord
  · have hcomp : (fun p : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin (n - k)) =>
        recombine hk (negPart hk (cellMap (Real.sqrt (2 * ε + r ^ 2 * ‖p.2‖ ^ 2)) p.1)) (r • p.2) i) =
        fun p : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin (n - k)) =>
          r * p.2 ⟨i.val - k, by
            have hkle : k ≤ i.val := le_of_not_gt hi
            have hi' : i.val < n := i.isLt
            omega⟩ := by
      funext p
      dsimp [recombine]
      rw [dif_neg hi]
    rw [hcomp]
    fun_prop

theorem morseNorm_recombine_sq {n k : ℕ} (hk : k ≤ n) (a : EuclideanSpace ℝ (Fin k))
    (b : EuclideanSpace ℝ (Fin (n - k))) :
    morseNorm n (recombine hk a b) ^ 2 = ‖a‖ ^ 2 + ‖b‖ ^ 2 := by
  rw [morseNorm_sq_eq_negPart_add_posPart hk (recombine hk a b)]
  rw [negPart_recombine, posPart_recombine]

theorem morseNorm_recombine_cellMap_bound {n k : ℕ} (hk : k ≤ n) (ε r : ℝ) (hε : 0 ≤ ε)
    (u : EuclideanSpace ℝ (Fin k)) (hu : ‖u‖ = 1)
    (v : EuclideanSpace ℝ (Fin (n - k))) (hv : ‖v‖ ≤ 1) :
    morseNorm n (recombine hk (negPart hk (cellMap (Real.sqrt (2 * ε)) u)) (r • v)) ≤
      Real.sqrt (2 * ε + r ^ 2) := by
  have hsq : morseNorm n (recombine hk (negPart hk (cellMap (Real.sqrt (2 * ε)) u)) (r • v)) ^ 2 ≤
      2 * ε + r ^ 2 := by
    rw [morseNorm_recombine_sq hk (negPart hk (cellMap (Real.sqrt (2 * ε)) u)) (r • v)]
    have h1 : ‖negPart hk (cellMap (Real.sqrt (2 * ε)) u)‖ ^ 2 ≤ 2 * ε := by
      have hnorm := norm_negPart_cellMap hk (Real.sqrt (2 * ε)) u
      rw [hnorm, hu]
      have hsq : (Real.sqrt (2 * ε)) ^ 2 = 2 * ε := by
        rw [Real.sq_sqrt (by positivity : 0 ≤ 2 * ε)]
      rw [hsq]
      nlinarith [sq_nonneg ε]
    have h2 : ‖r • v‖ ^ 2 ≤ r ^ 2 := by
      have hnorm : ‖r • v‖ ^ 2 = r ^ 2 * ‖v‖ ^ 2 := by
        rw [norm_smul]
        rw [Real.norm_eq_abs]
        rw [mul_pow]
        rw [sq_abs]
      rw [hnorm]
      have hv2 : ‖v‖ ^ 2 ≤ 1 := by
        have hneg : -1 ≤ ‖v‖ := by linarith [norm_nonneg v]
        exact (sq_le_sq' hneg hv).trans_eq (by norm_num : (1 : ℝ) ^ 2 = 1)
      nlinarith [hv2, sq_nonneg r]
    nlinarith
  have hnn : 0 ≤ morseNorm n (recombine hk (negPart hk (cellMap (Real.sqrt (2 * ε)) u)) (r • v)) :=
    norm_nonneg _
  have hns : 0 ≤ Real.sqrt (2 * ε + r ^ 2) := Real.sqrt_nonneg _
  have hsq' : morseNorm n (recombine hk (negPart hk (cellMap (Real.sqrt (2 * ε)) u)) (r • v)) ^ 2 ≤
      (Real.sqrt (2 * ε + r ^ 2)) ^ 2 := by
    rwa [Real.sq_sqrt (by positivity : 0 ≤ 2 * ε + r ^ 2)]
  exact le_of_sq_le_sq hsq' hns

theorem negPart_cellMap_injective {n k : ℕ} (hk : k ≤ n) (ε : ℝ) (hε : 0 < ε) :
    Function.Injective (fun u : CellBoundary k =>
      negPart hk (cellMap (Real.sqrt (2 * ε)) (u : EuclideanSpace ℝ (Fin k)))) := by
  intro u v h
  have hneg : ∀ i : Fin k,
      (cellMap (Real.sqrt (2 * ε)) (u : EuclideanSpace ℝ (Fin k)) (negIdx hk i)) =
        cellMap (Real.sqrt (2 * ε)) (v : EuclideanSpace ℝ (Fin k)) (negIdx hk i) := by
    intro i
    exact congrArg (fun w : EuclideanSpace ℝ (Fin k) => w i) h
  have hcore : ∀ i : Fin n,
      (cellMap (Real.sqrt (2 * ε)) (u : EuclideanSpace ℝ (Fin k))) i =
        (cellMap (Real.sqrt (2 * ε)) (v : EuclideanSpace ℝ (Fin k))) i := by
    intro i
    by_cases hi : i.val < k
    · have hni : negIdx hk ⟨i.val, hi⟩ = i := by
        ext
        rfl
      calc
        (cellMap (Real.sqrt (2 * ε)) (u : EuclideanSpace ℝ (Fin k))) i
            = (cellMap (Real.sqrt (2 * ε)) (u : EuclideanSpace ℝ (Fin k))) (negIdx hk ⟨i.val, hi⟩) := by
              rw [hni]
        _ = (cellMap (Real.sqrt (2 * ε)) (v : EuclideanSpace ℝ (Fin k))) (negIdx hk ⟨i.val, hi⟩) :=
              hneg ⟨i.val, hi⟩
        _ = (cellMap (Real.sqrt (2 * ε)) (v : EuclideanSpace ℝ (Fin k))) i := by
              rw [hni]
    · have hpos : ∃ j : Fin (n - k), posIdx hk j = i := by
        refine ⟨⟨i.val - k, by omega⟩, ?_⟩
        dsimp [posIdx]
        apply Fin.ext
        simp
        omega
      rcases hpos with ⟨j, rfl⟩
      simp [cellMap_posIdx]
  have hcellmap : (cellMap (Real.sqrt (2 * ε)) (u : EuclideanSpace ℝ (Fin k)) : MorseModel n) =
      (cellMap (Real.sqrt (2 * ε)) (v : EuclideanSpace ℝ (Fin k)) : MorseModel n) := by
    funext i
    exact hcore i
  have hu : (⟨u, le_of_eq u.2⟩ : ClosedCell k) = ⟨v, le_of_eq v.2⟩ := by
    exact (cellMap_injective hk ε hε) hcellmap
  apply Subtype.ext
  simpa [cellBoundaryInclusion] using congrArg (fun z : ClosedCell k => (z : EuclideanSpace ℝ (Fin k))) hu

theorem recombine_injective {n k : ℕ} (hk : k ≤ n) :
    Function.Injective (fun p : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin (n - k)) =>
      recombine hk p.1 p.2) := by
  intro p q h
  apply Prod.ext
  · have hneg := congrArg (negPart hk) h
    simpa [negPart_recombine] using hneg
  · have hpos := congrArg (posPart hk) h
    simpa [posPart_recombine] using hpos

theorem recombine_cellMap_injective {n k : ℕ} (hk : k ≤ n) (ε r : ℝ) (hε : 0 < ε) (hr : r ≠ 0) :
    Function.Injective (fun p : CellBoundary k × ClosedCell (n - k) =>
      recombine hk (negPart hk (cellMap (Real.sqrt (2 * ε)) (p.1 : EuclideanSpace ℝ (Fin k))))
        (r • (p.2 : EuclideanSpace ℝ (Fin (n - k))))) := by
  intro p q h
  have h1 : (negPart hk (cellMap (Real.sqrt (2 * ε)) (p.1 : EuclideanSpace ℝ (Fin k))),
        r • (p.2 : EuclideanSpace ℝ (Fin (n - k)))) =
      (negPart hk (cellMap (Real.sqrt (2 * ε)) (q.1 : EuclideanSpace ℝ (Fin k))),
        r • (q.2 : EuclideanSpace ℝ (Fin (n - k)))) := by
    exact recombine_injective hk h
  apply Prod.ext
  · exact negPart_cellMap_injective hk ε hε (congrArg Prod.fst h1)
  · have hcocore := congrArg Prod.snd h1
    apply Subtype.ext
    exact (smul_right_injective (EuclideanSpace ℝ (Fin (n - k))) (r := r) hr) hcocore

theorem recombine_cellMap_cocore_injective {n k : ℕ} (hk : k ≤ n) (ε r : ℝ) (hε : 0 < ε)
    (hr : r ≠ 0) :
    Function.Injective (fun p : CellBoundary k × ClosedCell (n - k) =>
      recombine hk (negPart hk (cellMap (Real.sqrt (2 * ε + r ^ 2 * ‖(p.2 : EuclideanSpace ℝ (Fin (n - k)))‖ ^ 2))
          (p.1 : EuclideanSpace ℝ (Fin k)))) (r • (p.2 : EuclideanSpace ℝ (Fin (n - k))))) := by
  intro p q h
  have hneg : negPart hk (cellMap (Real.sqrt (2 * ε + r ^ 2 * ‖(p.2 : EuclideanSpace ℝ (Fin (n - k)))‖ ^ 2))
        (p.1 : EuclideanSpace ℝ (Fin k))) =
      negPart hk (cellMap (Real.sqrt (2 * ε + r ^ 2 * ‖(q.2 : EuclideanSpace ℝ (Fin (n - k)))‖ ^ 2))
        (q.1 : EuclideanSpace ℝ (Fin k))) := by
    have h' := congrArg (negPart hk) h
    simpa [negPart_recombine] using h'
  have hpos : r • (p.2 : EuclideanSpace ℝ (Fin (n - k))) = r • (q.2 : EuclideanSpace ℝ (Fin (n - k))) := by
    have h' := congrArg (posPart hk) h
    simpa [posPart_recombine] using h'
  have hw : (p.2 : EuclideanSpace ℝ (Fin (n - k))) = (q.2 : EuclideanSpace ℝ (Fin (n - k))) :=
    (smul_right_injective (EuclideanSpace ℝ (Fin (n - k))) (r := r) hr) hpos
  have hrad : Real.sqrt (2 * ε + r ^ 2 * ‖(p.2 : EuclideanSpace ℝ (Fin (n - k)))‖ ^ 2) =
      Real.sqrt (2 * ε + r ^ 2 * ‖(q.2 : EuclideanSpace ℝ (Fin (n - k)))‖ ^ 2) := by
    rw [hw]
  have hinj : Function.Injective (fun u : CellBoundary k =>
      negPart hk (cellMap (Real.sqrt (2 * ε + r ^ 2 * ‖(p.2 : EuclideanSpace ℝ (Fin (n - k)))‖ ^ 2))
        (u : EuclideanSpace ℝ (Fin k)))) := by
    intro u v huv
    apply Subtype.ext
    ext i
    have hc := congrArg (fun w : EuclideanSpace ℝ (Fin k) => w i) huv
    have h1 : Real.sqrt (2 * ε + r ^ 2 * ‖(p.2 : EuclideanSpace ℝ (Fin (n - k)))‖ ^ 2) *
          (u : EuclideanSpace ℝ (Fin k)) i =
        Real.sqrt (2 * ε + r ^ 2 * ‖(p.2 : EuclideanSpace ℝ (Fin (n - k)))‖ ^ 2) *
          (v : EuclideanSpace ℝ (Fin k)) i := by
      simpa [negPart_cellMap_apply] using hc
    exact (mul_left_cancel₀ (by positivity) h1)
  apply Prod.ext
  · exact hinj (by
      rwa [← hrad] at hneg)
  · apply Subtype.ext
    exact hw

noncomputable def modelFlow {n k : ℕ} (hk : k ≤ n) (t : ℝ) (y : MorseModel n) : MorseModel n :=
  recombine hk (negPart hk y) ((Real.sqrt (1 - 2 * t / ‖posPart hk y‖ ^ 2)) • posPart hk y)

theorem modelFlow_zero {n k : ℕ} (hk : k ≤ n) (y : MorseModel n) :
    modelFlow hk 0 y = y := by
  dsimp [modelFlow]
  have hsq : Real.sqrt (1 - 2 * 0 / ‖posPart hk y‖ ^ 2) = 1 := by norm_num
  rw [hsq, one_smul]
  exact recombine_decompose hk y

theorem modelFlow_f_sub {n k : ℕ} (hk : k ≤ n) (c t : ℝ) (y : MorseModel n)
    (ht0 : 0 ≤ t) (ht : t ≤ ‖posPart hk y‖ ^ 2 / 2) :
    morseNormalForm hk c (modelFlow hk t y) = morseNormalForm hk c y - t := by
  let a : EuclideanSpace ℝ (Fin k) := negPart hk y
  let b : EuclideanSpace ℝ (Fin (n - k)) := posPart hk y
  have hsq : 0 ≤ 1 - 2 * t / ‖b‖ ^ 2 := by
    have hb2 : 0 ≤ ‖b‖ ^ 2 := sq_nonneg ‖b‖
    have hdiv : 2 * t / ‖b‖ ^ 2 ≤ 1 := by
      by_cases hb : ‖b‖ = 0
      · have ht' : t = 0 := by
          rw [hb] at ht
          exact le_antisymm (by simpa using ht) ht0
        rw [ht', hb]
        norm_num
      · have hbpos : 0 < ‖b‖ := lt_of_le_of_ne (norm_nonneg b) (Ne.symm hb)
        have hb2pos : 0 < ‖b‖ ^ 2 := sq_pos_of_pos hbpos
        rw [div_le_one hb2pos]
        nlinarith [ht, hb2pos, ht0]
    nlinarith [hdiv, ht0]
  have hnorm : ‖(Real.sqrt (1 - 2 * t / ‖b‖ ^ 2) • b)‖ ^ 2 = ‖b‖ ^ 2 - 2 * t := by
    rw [norm_smul]
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    rw [mul_pow]
    rw [Real.sq_sqrt hsq]
    by_cases hb2 : ‖b‖ ^ 2 = 0
    · have ht0' : t = 0 := by
        have hle : t ≤ 0 := by
          rw [hb2] at ht
          simpa using ht
        linarith
      have hb0 : b = 0 := norm_eq_zero.mp (sq_eq_zero_iff.mp hb2)
      rw [ht0', hb0]
      simp
    · rw [sub_mul, one_mul]
      rw [div_mul_cancel₀ (2 * t) hb2]
  have hnf : morseNormalForm hk c (modelFlow hk t y) =
      c + (1 / 2) * (-‖a‖ ^ 2 + ‖Real.sqrt (1 - 2 * t / ‖b‖ ^ 2) • b‖ ^ 2) := by
    dsimp [modelFlow, a, b]
    have hcid : negPart hk (cellMap 1 (negPart hk y)) = negPart hk y := by
      ext i
      rw [negPart_cellMap_apply]
      simp
    have hrec := morseNormalForm_recombine hk c 1 (negPart hk y)
      (Real.sqrt (1 - 2 * t / ‖posPart hk y‖ ^ 2) • posPart hk y)
    rw [hcid] at hrec
    have h1 : (1 : ℝ) ^ 2 * ‖negPart hk y‖ ^ 2 = ‖negPart hk y‖ ^ 2 := by ring
    simpa [h1] using hrec
  have hnfy : morseNormalForm hk c y = c + (1 / 2) * (-‖a‖ ^ 2 + ‖b‖ ^ 2) := by
    dsimp [morseNormalForm, a, b]
    congr 1
    rw [show (∑ i : Fin k, - (y (negIdx hk i)) ^ 2) = -(∑ i : Fin k, (y (negIdx hk i)) ^ 2) by
      rw [Finset.sum_neg_distrib]]
    rw [show (∑ i : Fin k, (y (negIdx hk i)) ^ 2) = ‖negPart hk y‖ ^ 2 by
      rw [EuclideanSpace.real_norm_sq_eq (negPart hk y)]
      apply Finset.sum_congr rfl
      intro i hi
      change (y (negIdx hk i)) ^ 2 = ((negPart hk y).ofLp i) ^ 2
      rfl]
    rw [show (∑ j : Fin (n - k), (y (posIdx hk j)) ^ 2) = ‖posPart hk y‖ ^ 2 by
      rw [EuclideanSpace.real_norm_sq_eq (posPart hk y)]
      apply Finset.sum_congr rfl
      intro j hj
      change (y (posIdx hk j)) ^ 2 = ((posPart hk y).ofLp j) ^ 2
      rfl]
  rw [hnf, hnfy, hnorm]
  ring

theorem modelFlow_norm_le {n k : ℕ} (hk : k ≤ n) (t : ℝ) (y : MorseModel n)
    (ht0 : 0 ≤ t) (ht : t ≤ ‖posPart hk y‖ ^ 2 / 2) :
    morseNorm n (modelFlow hk t y) ≤ morseNorm n y := by
  apply le_of_sq_le_sq
  · let a : EuclideanSpace ℝ (Fin k) := negPart hk y
    let b : EuclideanSpace ℝ (Fin (n - k)) := posPart hk y
    have hsq : 0 ≤ 1 - 2 * t / ‖b‖ ^ 2 := by
      have hdiv : 2 * t / ‖b‖ ^ 2 ≤ 1 := by
        by_cases hb : ‖b‖ = 0
        · have ht' : t = 0 := by
            rw [hb] at ht
            exact le_antisymm (by simpa using ht) ht0
          rw [ht', hb]
          norm_num
        · have hbpos : 0 < ‖b‖ := lt_of_le_of_ne (norm_nonneg b) (Ne.symm hb)
          have hb2pos : 0 < ‖b‖ ^ 2 := sq_pos_of_pos hbpos
          rw [div_le_one hb2pos]
          nlinarith [ht, hb2pos, ht0]
      nlinarith [hdiv, ht0, sq_nonneg ‖b‖]
    have hnorm2 : ‖(Real.sqrt (1 - 2 * t / ‖b‖ ^ 2) • b)‖ ^ 2 = ‖b‖ ^ 2 - 2 * t := by
      rw [norm_smul]
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
      rw [mul_pow]
      rw [Real.sq_sqrt hsq]
      by_cases hb2 : ‖b‖ ^ 2 = 0
      · have ht0' : t = 0 := by
          have hle : t ≤ 0 := by
            rw [hb2] at ht
            simpa using ht
          linarith
        have hb0 : b = 0 := norm_eq_zero.mp (sq_eq_zero_iff.mp hb2)
        rw [ht0', hb0]
        simp
      · rw [sub_mul, one_mul]
        rw [div_mul_cancel₀ (2 * t) hb2]
    have hmain : morseNorm n (modelFlow hk t y) ^ 2 ≤ morseNorm n y ^ 2 := by
      rw [morseNorm_sq_eq_negPart_add_posPart hk (modelFlow hk t y)]
      rw [morseNorm_sq_eq_negPart_add_posPart hk y]
      dsimp [modelFlow]
      rw [negPart_recombine]
      rw [posPart_recombine]
      have hnorm2' : ‖(Real.sqrt (1 - 2 * t / ‖posPart hk y‖ ^ 2) • posPart hk y)‖ ^ 2 =
          ‖posPart hk y‖ ^ 2 - 2 * t := by
        simpa [a, b] using hnorm2
      nlinarith [hnorm2', ht0]
    exact hmain
  · exact norm_nonneg _

theorem modelFlow_negPart {n k : ℕ} (hk : k ≤ n) (t : ℝ) (y : MorseModel n) :
    negPart hk (modelFlow hk t y) = negPart hk y := by
  dsimp [modelFlow]
  rw [negPart_recombine]

theorem modelFlow_posPart {n k : ℕ} (hk : k ≤ n) (t : ℝ) (y : MorseModel n) :
    posPart hk (modelFlow hk t y) =
      (Real.sqrt (1 - 2 * t / ‖posPart hk y‖ ^ 2)) • posPart hk y := by
  dsimp [modelFlow]
  rw [posPart_recombine]

theorem modelFlow_posPart_norm_sq {n k : ℕ} (hk : k ≤ n) (t : ℝ) (y : MorseModel n)
    (ht0 : 0 ≤ t) (ht : t ≤ ‖posPart hk y‖ ^ 2 / 2) :
    ‖posPart hk (modelFlow hk t y)‖ ^ 2 = ‖posPart hk y‖ ^ 2 - 2 * t := by
  rw [modelFlow_posPart]
  rw [norm_smul]
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  rw [mul_pow]
  have hsq : 0 ≤ 1 - 2 * t / ‖posPart hk y‖ ^ 2 := by
    have hdiv : 2 * t / ‖posPart hk y‖ ^ 2 ≤ 1 := by
      by_cases hb : ‖posPart hk y‖ = 0
      · have ht' : t = 0 := by
          rw [hb] at ht
          exact le_antisymm (by simpa using ht) ht0
        rw [ht', hb]
        norm_num
      · have hbpos : 0 < ‖posPart hk y‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hb)
        have hb2pos : 0 < ‖posPart hk y‖ ^ 2 := sq_pos_of_pos hbpos
        rw [div_le_one hb2pos]
        nlinarith [ht, hb2pos, ht0]
    nlinarith [hdiv, ht0]
  rw [Real.sq_sqrt hsq]
  by_cases hb2 : ‖posPart hk y‖ ^ 2 = 0
  · have ht0' : t = 0 := by
      have hle : t ≤ 0 := by
        rw [hb2] at ht
        simpa using ht
      linarith
    have hb0 : posPart hk y = 0 := norm_eq_zero.mp (sq_eq_zero_iff.mp hb2)
    rw [ht0', hb0]
    simp
  · rw [sub_mul, one_mul]
    rw [div_mul_cancel₀ (2 * t) hb2]

theorem modelFlow_up_posPart_norm_sq {n k : ℕ} (hk : k ≤ n) (t : ℝ) (y : MorseModel n)
    (ht0 : 0 ≤ t) (hy : 0 < ‖posPart hk y‖) :
    ‖posPart hk (modelFlow hk (-t) y)‖ ^ 2 = ‖posPart hk y‖ ^ 2 + 2 * t := by
  rw [modelFlow_posPart]
  rw [norm_smul]
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  rw [mul_pow]
  have hsq : 0 ≤ 1 - 2 * (-t) / ‖posPart hk y‖ ^ 2 := by
    have hb2pos : 0 < ‖posPart hk y‖ ^ 2 := sq_pos_of_pos hy
    have h2t : 0 ≤ 2 * t := by positivity
    have hdiv : 0 ≤ 2 * t / ‖posPart hk y‖ ^ 2 := div_nonneg h2t (le_of_lt hb2pos)
    rw [show 1 - 2 * (-t) / ‖posPart hk y‖ ^ 2 = 1 + 2 * t / ‖posPart hk y‖ ^ 2 by ring]
    linarith
  rw [Real.sq_sqrt hsq]
  have hb2 : ‖posPart hk y‖ ^ 2 ≠ 0 := by
    exact ne_of_gt (sq_pos_of_pos hy)
  rw [show 1 - 2 * (-t) / ‖posPart hk y‖ ^ 2 =
      1 + 2 * t / ‖posPart hk y‖ ^ 2 by ring]
  rw [add_mul, one_mul]
  rw [div_mul_cancel₀ (2 * t) hb2]

theorem modelFlow_f_add {n k : ℕ} (hk : k ≤ n) (c t : ℝ) (y : MorseModel n)
    (ht0 : 0 ≤ t) (hy : 0 < ‖posPart hk y‖) :
    morseNormalForm hk c (modelFlow hk (-t) y) = morseNormalForm hk c y + t := by
  let a : EuclideanSpace ℝ (Fin k) := negPart hk y
  let b : EuclideanSpace ℝ (Fin (n - k)) := posPart hk y
  have hnorm : ‖(Real.sqrt (1 - 2 * (-t) / ‖b‖ ^ 2) • b)‖ ^ 2 = ‖b‖ ^ 2 + 2 * t := by
    rw [norm_smul]
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    rw [mul_pow]
    have hsq : 0 ≤ 1 - 2 * (-t) / ‖b‖ ^ 2 := by
      have hb2pos : 0 < ‖b‖ ^ 2 := sq_pos_of_pos hy
      have h2t : 0 ≤ 2 * t := by positivity
      have hdiv : 0 ≤ 2 * t / ‖b‖ ^ 2 := div_nonneg h2t (le_of_lt hb2pos)
      rw [show 1 - 2 * (-t) / ‖b‖ ^ 2 = 1 + 2 * t / ‖b‖ ^ 2 by ring]
      linarith
    rw [Real.sq_sqrt hsq]
    rw [show 1 - 2 * (-t) / ‖b‖ ^ 2 = 1 + 2 * t / ‖b‖ ^ 2 by ring]
    have hb2 : ‖b‖ ^ 2 ≠ 0 := by
      exact ne_of_gt (sq_pos_of_pos hy)
    rw [add_mul, one_mul]
    rw [div_mul_cancel₀ (2 * t) hb2]
  have hval : morseNormalForm hk c (modelFlow hk (-t) y) =
      c + (1 / 2) * (-‖a‖ ^ 2 + (‖b‖ ^ 2 + 2 * t)) := by
    have hsplit := morseNormalForm_split hk c (modelFlow hk (-t) y)
    rw [hsplit]
    rw [modelFlow_negPart]
    rw [modelFlow_posPart]
    rw [hnorm]
    ring
  have hfy : morseNormalForm hk c y = c + (1 / 2) * (‖b‖ ^ 2 - ‖a‖ ^ 2) := by
    have hsplit := morseNormalForm_split hk c y
    rw [hsplit]
  rw [hval, hfy]
  ring

theorem modelFlow_rev {n k : ℕ} (hk : k ≤ n) (t : ℝ) (y : MorseModel n)
    (ht0 : 0 ≤ t) (ht : 2 * t < ‖posPart hk y‖ ^ 2) :
    modelFlow hk (-t) (modelFlow hk t y) = y := by
  let b : EuclideanSpace ℝ (Fin (n - k)) := posPart hk y
  have hBpos : 0 < ‖b‖ ^ 2 := by
    nlinarith [ht0, ht, sq_nonneg ‖b‖]
  have hBsubPos : 0 < ‖b‖ ^ 2 - 2 * t := by
    nlinarith [ht]
  have hnonneg : 0 ≤ 1 - 2 * t / ‖b‖ ^ 2 := by
    have hdiv : 2 * t / ‖b‖ ^ 2 ≤ 1 := by
      rw [div_le_one hBpos]
      nlinarith [ht]
    nlinarith [hdiv, ht0]
  have hplus : 0 ≤ 1 + 2 * t / (‖b‖ ^ 2 - 2 * t) := by positivity
  have hsq : (Real.sqrt (1 + 2 * t / (‖b‖ ^ 2 - 2 * t)) *
      Real.sqrt (1 - 2 * t / ‖b‖ ^ 2)) ^ 2 = 1 := by
    rw [mul_pow]
    rw [Real.sq_sqrt hplus]
    rw [Real.sq_sqrt hnonneg]
    have h1 : 1 + 2 * t / (‖b‖ ^ 2 - 2 * t) = ‖b‖ ^ 2 / (‖b‖ ^ 2 - 2 * t) := by
      have hmain : (1 + 2 * t / (‖b‖ ^ 2 - 2 * t)) * (‖b‖ ^ 2 - 2 * t) = ‖b‖ ^ 2 := by
        rw [add_mul, one_mul]
        rw [div_mul_cancel₀ (2 * t) (ne_of_gt hBsubPos)]
        ring
      exact ((div_eq_iff (ne_of_gt hBsubPos)).mpr hmain.symm).symm
    have h2 : 1 - 2 * t / ‖b‖ ^ 2 = (‖b‖ ^ 2 - 2 * t) / ‖b‖ ^ 2 := by
      have hmain : (1 - 2 * t / ‖b‖ ^ 2) * ‖b‖ ^ 2 = ‖b‖ ^ 2 - 2 * t := by
        rw [sub_mul, one_mul]
        rw [div_mul_cancel₀ (2 * t) (ne_of_gt hBpos)]
      exact ((div_eq_iff (ne_of_gt hBpos)).mpr hmain.symm).symm
    rw [h1, h2]
    field_simp [ne_of_gt hBsubPos, ne_of_gt hBpos]
    have hBnorm : 0 < ‖b‖ :=
      lt_of_le_of_ne (norm_nonneg b) (Ne.symm (sq_pos_iff.mp hBpos))
    exact div_self (ne_of_gt hBnorm)
  have hnonneg' : 0 ≤ Real.sqrt (1 + 2 * t / (‖b‖ ^ 2 - 2 * t)) *
      Real.sqrt (1 - 2 * t / ‖b‖ ^ 2) := by positivity
  have hscalar : Real.sqrt (1 + 2 * t / (‖b‖ ^ 2 - 2 * t)) *
      Real.sqrt (1 - 2 * t / ‖b‖ ^ 2) = 1 := by
    have hsq' : (Real.sqrt (1 + 2 * t / (‖b‖ ^ 2 - 2 * t)) *
        Real.sqrt (1 - 2 * t / ‖b‖ ^ 2)) ^ 2 = (1 : ℝ) ^ 2 := by
      simpa using hsq
    exact (sq_eq_sq_iff_eq_or_eq_neg.mp hsq').resolve_right (by nlinarith [hnonneg'])
  calc
    modelFlow hk (-t) (modelFlow hk t y) =
        recombine hk (negPart hk (modelFlow hk (-t) (modelFlow hk t y)))
          (posPart hk (modelFlow hk (-t) (modelFlow hk t y))) :=
      (recombine_decompose hk (modelFlow hk (-t) (modelFlow hk t y))).symm
    _ = recombine hk (negPart hk y) (posPart hk y) := by
      congr 1
      · rw [modelFlow_negPart, modelFlow_negPart]
      · change posPart hk (modelFlow hk (-t) (modelFlow hk t y)) = b
        rw [modelFlow_posPart]
        rw [modelFlow_posPart_norm_sq hk t y ht0 (by nlinarith [ht])]
        rw [modelFlow_posPart]
        rw [smul_smul]
        have hrew : 1 - 2 * (-t) / (‖b‖ ^ 2 - 2 * t) =
            1 + 2 * t / (‖b‖ ^ 2 - 2 * t) := by ring
        rw [hrew, hscalar, one_smul]
    _ = y := recombine_decompose hk y

def modelHandleMap {n k : ℕ} (hk : k ≤ n) (ε r : ℝ)
    (p : StandardHandle k (n - k)) : MorseModel n :=
  recombine hk
    ((Real.sqrt (2 * ε + r ^ 2 * ‖(p.2 : EuclideanSpace ℝ (Fin (n - k)))‖ ^ 2)) •
      (p.1 : EuclideanSpace ℝ (Fin k)))
    (r • (p.2 : EuclideanSpace ℝ (Fin (n - k))))

theorem negPart_cellMap_smul {n k : ℕ} (hk : k ≤ n) (ε : ℝ)
    (u : EuclideanSpace ℝ (Fin k)) :
    negPart hk (cellMap ε u) = ε • u := by
  ext i
  rw [negPart_cellMap_apply]
  rfl

theorem modelHandleMap_negPart {n k : ℕ} (hk : k ≤ n) (ε r : ℝ)
    (p : StandardHandle k (n - k)) :
    negPart hk (modelHandleMap hk ε r p) =
      (Real.sqrt (2 * ε + r ^ 2 * ‖(p.2 : EuclideanSpace ℝ (Fin (n - k)))‖ ^ 2)) •
        (p.1 : EuclideanSpace ℝ (Fin k)) := by
  dsimp [modelHandleMap]
  rw [negPart_recombine]

theorem modelHandleMap_posPart {n k : ℕ} (hk : k ≤ n) (ε r : ℝ)
    (p : StandardHandle k (n - k)) :
    posPart hk (modelHandleMap hk ε r p) =
      r • (p.2 : EuclideanSpace ℝ (Fin (n - k))) := by
  dsimp [modelHandleMap]
  rw [posPart_recombine]

theorem modelHandleMap_f_value {n k : ℕ} (hk : k ≤ n) (c ε r : ℝ) (hε : 0 ≤ ε)
    (p : StandardHandle k (n - k)) :
    morseNormalForm hk c (modelHandleMap hk ε r p) =
      c + (1 / 2) *
        (-((2 * ε + r ^ 2 * ‖(p.2 : EuclideanSpace ℝ (Fin (n - k)))‖ ^ 2) *
            ‖(p.1 : EuclideanSpace ℝ (Fin k))‖ ^ 2) +
          r ^ 2 * ‖(p.2 : EuclideanSpace ℝ (Fin (n - k)))‖ ^ 2) := by
  dsimp [modelHandleMap]
  rw [← negPart_cellMap_smul hk]
  have hrec := morseNormalForm_recombine hk c
    (Real.sqrt (2 * ε + r ^ 2 * ‖(p.2 : EuclideanSpace ℝ (Fin (n - k)))‖ ^ 2))
    (p.1 : EuclideanSpace ℝ (Fin k)) (r • (p.2 : EuclideanSpace ℝ (Fin (n - k))))
  rw [hrec]
  have hsq : (Real.sqrt (2 * ε + r ^ 2 * ‖(p.2 : EuclideanSpace ℝ (Fin (n - k)))‖ ^ 2)) ^ 2 =
      2 * ε + r ^ 2 * ‖(p.2 : EuclideanSpace ℝ (Fin (n - k)))‖ ^ 2 := by
    rw [Real.sq_sqrt (by positivity : 0 ≤ 2 * ε + r ^ 2 * ‖(p.2 : EuclideanSpace ℝ (Fin (n - k)))‖ ^ 2)]
  have hnorm : ‖(r • (p.2 : EuclideanSpace ℝ (Fin (n - k))) : EuclideanSpace ℝ (Fin (n - k)))‖ ^ 2 =
      r ^ 2 * ‖(p.2 : EuclideanSpace ℝ (Fin (n - k)))‖ ^ 2 := by
    rw [norm_smul]
    rw [Real.norm_eq_abs]
    rw [mul_pow]
    rw [sq_abs]
  rw [hsq, hnorm]
  nlinarith

theorem modelHandleMap_f_sub {n k : ℕ} (hk : k ≤ n) (c ε r : ℝ) (hε : 0 ≤ ε)
    (p : StandardHandle k (n - k)) :
    morseNormalForm hk c (modelHandleMap hk ε r p) - (c - ε) =
      (1 / 2) * (2 * ε + r ^ 2 * ‖(p.2 : EuclideanSpace ℝ (Fin (n - k)))‖ ^ 2) *
        (1 - ‖(p.1 : EuclideanSpace ℝ (Fin k))‖ ^ 2) := by
  have hval := modelHandleMap_f_value hk c ε r hε p
  rw [hval]
  ring

theorem modelHandleMap_f_ge {n k : ℕ} (hk : k ≤ n) (c ε r : ℝ) (hε : 0 ≤ ε)
    (p : StandardHandle k (n - k)) :
    c - ε ≤ morseNormalForm hk c (modelHandleMap hk ε r p) := by
  rw [← sub_nonneg]
  rw [modelHandleMap_f_sub hk c ε r hε]
  have hnonneg : 0 ≤ 2 * ε + r ^ 2 * ‖(p.2 : EuclideanSpace ℝ (Fin (n - k)))‖ ^ 2 := by positivity
  have hle : ‖(p.1 : EuclideanSpace ℝ (Fin k))‖ ^ 2 ≤ 1 := by
    have hneg : -1 ≤ ‖(p.1 : EuclideanSpace ℝ (Fin k))‖ := by
      linarith [norm_nonneg (p.1 : EuclideanSpace ℝ (Fin k))]
    exact (sq_le_sq' hneg p.1.2).trans_eq (by norm_num : (1 : ℝ) ^ 2 = 1)
  nlinarith [hnonneg, hle]

theorem modelHandleMap_f_le {n k : ℕ} (hk : k ≤ n) (c ε r : ℝ) (hε : 0 ≤ ε)
    (p : StandardHandle k (n - k)) :
    morseNormalForm hk c (modelHandleMap hk ε r p) ≤ c + r ^ 2 / 2 := by
  rw [modelHandleMap_f_value hk c ε r hε p]
  have hx : 0 ≤ ‖(p.1 : EuclideanSpace ℝ (Fin k))‖ ^ 2 := sq_nonneg _
  have hw : ‖(p.2 : EuclideanSpace ℝ (Fin (n - k)))‖ ^ 2 ≤ 1 := by
    have hneg : -1 ≤ ‖(p.2 : EuclideanSpace ℝ (Fin (n - k)))‖ := by
      linarith [norm_nonneg (p.2 : EuclideanSpace ℝ (Fin (n - k)))]
    exact (sq_le_sq' hneg p.2.2).trans_eq (by norm_num : (1 : ℝ) ^ 2 = 1)
  have hnonneg : 0 ≤ (2 * ε + r ^ 2 * ‖(p.2 : EuclideanSpace ℝ (Fin (n - k)))‖ ^ 2) *
      ‖(p.1 : EuclideanSpace ℝ (Fin k))‖ ^ 2 := by positivity
  have hwle : r ^ 2 * ‖(p.2 : EuclideanSpace ℝ (Fin (n - k)))‖ ^ 2 ≤ r ^ 2 := by
    simpa using (mul_le_mul_of_nonneg_left hw (sq_nonneg r))
  nlinarith [hnonneg, hwle]

theorem modelHandleMap_f_eq_lower_iff {n k : ℕ} (hk : k ≤ n) (c ε r : ℝ) (hε : 0 < ε)
    (p : StandardHandle k (n - k)) :
    morseNormalForm hk c (modelHandleMap hk ε r p) = c - ε ↔
      ‖(p.1 : EuclideanSpace ℝ (Fin k))‖ = 1 := by
  rw [← sub_eq_zero]
  rw [modelHandleMap_f_sub hk c ε r (le_of_lt hε)]
  constructor
  · intro h
    have hmain : (1 / 2 : ℝ) * (2 * ε + r ^ 2 * ‖(p.2 : EuclideanSpace ℝ (Fin (n - k)))‖ ^ 2) ≠ 0 := by
      positivity
    have hzero : 1 - ‖(p.1 : EuclideanSpace ℝ (Fin k))‖ ^ 2 = 0 :=
      (mul_eq_zero.mp h).resolve_left hmain
    have hsq : ‖(p.1 : EuclideanSpace ℝ (Fin k))‖ ^ 2 = 1 := by linarith
    rcases sq_eq_one_iff.mp hsq with h1 | h2
    · exact h1
    · linarith [norm_nonneg (p.1 : EuclideanSpace ℝ (Fin k))]
  · intro h
    rw [h]
    ring

theorem modelHandleMap_f_boundary {n k : ℕ} (hk : k ≤ n) (c ε r : ℝ)
    (hε : 0 ≤ ε) (u : CellBoundary k) (w : ClosedCell (n - k)) :
    morseNormalForm hk c (modelHandleMap hk ε r (cellBoundaryInclusion k u, w)) = c - ε := by
  rw [modelHandleMap_f_value hk c ε r hε]
  simp only [cellBoundaryInclusion]
  rw [u.2]
  ring

theorem modelHandleMap_norm_le {n k : ℕ} (hk : k ≤ n) (ε r : ℝ) (hε : 0 ≤ ε)
    (p : StandardHandle k (n - k)) :
    morseNorm n (modelHandleMap hk ε r p) ≤ Real.sqrt (2 * ε + 2 * r ^ 2) := by
  apply le_of_sq_le_sq
  · change morseNorm n (recombine hk
      ((Real.sqrt (2 * ε + r ^ 2 * ‖(p.2 : EuclideanSpace ℝ (Fin (n - k)))‖ ^ 2)) •
        (p.1 : EuclideanSpace ℝ (Fin k)))
      (r • (p.2 : EuclideanSpace ℝ (Fin (n - k))))) ^ 2 ≤
      (Real.sqrt (2 * ε + 2 * r ^ 2)) ^ 2
    rw [morseNorm_recombine_sq hk
      ((Real.sqrt (2 * ε + r ^ 2 * ‖(p.2 : EuclideanSpace ℝ (Fin (n - k)))‖ ^ 2)) •
        (p.1 : EuclideanSpace ℝ (Fin k)))
      (r • (p.2 : EuclideanSpace ℝ (Fin (n - k))))]
    have h1 : ‖((Real.sqrt (2 * ε + r ^ 2 * ‖(p.2 : EuclideanSpace ℝ (Fin (n - k)))‖ ^ 2)) •
        (p.1 : EuclideanSpace ℝ (Fin k)))‖ ^ 2 ≤ 2 * ε + r ^ 2 := by
      rw [norm_smul]
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
      rw [mul_pow]
      rw [Real.sq_sqrt (by positivity : 0 ≤ 2 * ε + r ^ 2 * ‖(p.2 : EuclideanSpace ℝ (Fin (n - k)))‖ ^ 2)]
      have hx : ‖(p.1 : EuclideanSpace ℝ (Fin k))‖ ^ 2 ≤ 1 := by
        have hneg : -1 ≤ ‖(p.1 : EuclideanSpace ℝ (Fin k))‖ := by
          linarith [norm_nonneg (p.1 : EuclideanSpace ℝ (Fin k))]
        exact (sq_le_sq' hneg p.1.2).trans_eq (by norm_num : (1 : ℝ) ^ 2 = 1)
      have hw : ‖(p.2 : EuclideanSpace ℝ (Fin (n - k)))‖ ^ 2 ≤ 1 := by
        have hneg : -1 ≤ ‖(p.2 : EuclideanSpace ℝ (Fin (n - k)))‖ := by
          linarith [norm_nonneg (p.2 : EuclideanSpace ℝ (Fin (n - k)))]
        exact (sq_le_sq' hneg p.2.2).trans_eq (by norm_num : (1 : ℝ) ^ 2 = 1)
      have hcore : (2 * ε + r ^ 2 * ‖(p.2 : EuclideanSpace ℝ (Fin (n - k)))‖ ^ 2) *
          ‖(p.1 : EuclideanSpace ℝ (Fin k))‖ ^ 2 ≤
          2 * ε + r ^ 2 * ‖(p.2 : EuclideanSpace ℝ (Fin (n - k)))‖ ^ 2 := by
        simpa using mul_le_mul_of_nonneg_left hx
          (by positivity : 0 ≤ 2 * ε + r ^ 2 * ‖(p.2 : EuclideanSpace ℝ (Fin (n - k)))‖ ^ 2)
      have hA : 2 * ε + r ^ 2 * ‖(p.2 : EuclideanSpace ℝ (Fin (n - k)))‖ ^ 2 ≤ 2 * ε + r ^ 2 := by
        nlinarith [hw, sq_nonneg r]
      exact le_trans hcore hA
    have h2 : ‖(r • (p.2 : EuclideanSpace ℝ (Fin (n - k))) : EuclideanSpace ℝ (Fin (n - k)))‖ ^ 2 ≤ r ^ 2 := by
      rw [norm_smul]
      rw [Real.norm_eq_abs]
      rw [mul_pow]
      rw [sq_abs]
      have hw : ‖(p.2 : EuclideanSpace ℝ (Fin (n - k)))‖ ^ 2 ≤ 1 := by
        have hneg : -1 ≤ ‖(p.2 : EuclideanSpace ℝ (Fin (n - k)))‖ := by
          linarith [norm_nonneg (p.2 : EuclideanSpace ℝ (Fin (n - k)))]
        exact (sq_le_sq' hneg p.2.2).trans_eq (by norm_num : (1 : ℝ) ^ 2 = 1)
      nlinarith [hw]
    have hR2 : 2 * ε + 2 * r ^ 2 ≤ (Real.sqrt (2 * ε + 2 * r ^ 2)) ^ 2 := by
      rw [Real.sq_sqrt (by positivity : 0 ≤ 2 * ε + 2 * r ^ 2)]
    nlinarith [h1, h2, hR2]
  · exact Real.sqrt_nonneg _

theorem modelHandleMap_injective {n k : ℕ} (hk : k ≤ n) (ε r : ℝ) (hε : 0 < ε)
    (hr : r ≠ 0) :
    Function.Injective (modelHandleMap hk ε r) := by
  intro p q h
  have hneg := congrArg (negPart hk) h
  have hpos := congrArg (posPart hk) h
  simp only [modelHandleMap_negPart, modelHandleMap_posPart] at hneg hpos
  have hw : (p.2 : EuclideanSpace ℝ (Fin (n - k))) = (q.2 : EuclideanSpace ℝ (Fin (n - k))) :=
    (smul_right_injective (EuclideanSpace ℝ (Fin (n - k))) (r := r) hr) hpos
  have hscale : Real.sqrt (2 * ε + r ^ 2 * ‖(p.2 : EuclideanSpace ℝ (Fin (n - k)))‖ ^ 2) =
      Real.sqrt (2 * ε + r ^ 2 * ‖(q.2 : EuclideanSpace ℝ (Fin (n - k)))‖ ^ 2) := by
    rw [hw]
  have hneg' : (Real.sqrt (2 * ε + r ^ 2 * ‖(q.2 : EuclideanSpace ℝ (Fin (n - k)))‖ ^ 2)) •
        (p.1 : EuclideanSpace ℝ (Fin k)) =
      (Real.sqrt (2 * ε + r ^ 2 * ‖(q.2 : EuclideanSpace ℝ (Fin (n - k)))‖ ^ 2)) •
        (q.1 : EuclideanSpace ℝ (Fin k)) := by
    simpa [hscale] using hneg
  have hu : (p.1 : EuclideanSpace ℝ (Fin k)) = (q.1 : EuclideanSpace ℝ (Fin k)) :=
    (smul_right_injective (EuclideanSpace ℝ (Fin k))
      (r := Real.sqrt (2 * ε + r ^ 2 * ‖(q.2 : EuclideanSpace ℝ (Fin (n - k)))‖ ^ 2)) (by positivity))
      hneg'
  apply Prod.ext
  · apply Subtype.ext
    exact hu
  · apply Subtype.ext
    exact hw

theorem modelHandleMap_attachingRegion {n k : ℕ} (hk : k ≤ n) (ε r : ℝ)
    (u : CellBoundary k) (w : ClosedCell (n - k)) :
    modelHandleMap hk ε r (cellBoundaryInclusion k u, w) =
      recombine hk (negPart hk (cellMap (Real.sqrt (2 * ε + r ^ 2 * ‖(w : EuclideanSpace ℝ (Fin (n - k)))‖ ^ 2))
        (u : EuclideanSpace ℝ (Fin k)))) (r • (w : EuclideanSpace ℝ (Fin (n - k)))) := by
  dsimp [modelHandleMap, cellBoundaryInclusion]
  rw [negPart_cellMap_smul]

def modelHandle {n k : ℕ} (hk : k ≤ n) (ε r : ℝ) : Set (MorseModel n) :=
  {y : MorseModel n | ‖posPart hk y‖ ^ 2 ≤ r ^ 2 ∧
    ‖negPart hk y‖ ^ 2 ≤ ‖posPart hk y‖ ^ 2 + 2 * ε}

theorem modelHandleMap_mem {n k : ℕ} (hk : k ≤ n) (ε r : ℝ) (hε : 0 ≤ ε)
    (p : StandardHandle k (n - k)) :
    modelHandleMap hk ε r p ∈ modelHandle hk ε r := by
  dsimp [modelHandle]
  constructor
  · rw [modelHandleMap_posPart]
    rw [norm_smul]
    rw [Real.norm_eq_abs]
    rw [mul_pow]
    rw [sq_abs]
    have hw : ‖(p.2 : EuclideanSpace ℝ (Fin (n - k)))‖ ^ 2 ≤ 1 := by
      have hneg : -1 ≤ ‖(p.2 : EuclideanSpace ℝ (Fin (n - k)))‖ := by
        linarith [norm_nonneg (p.2 : EuclideanSpace ℝ (Fin (n - k)))]
      exact (sq_le_sq' hneg p.2.2).trans_eq (by norm_num : (1 : ℝ) ^ 2 = 1)
    nlinarith [hw]
  · rw [modelHandleMap_posPart, modelHandleMap_negPart]
    rw [norm_smul]
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    rw [mul_pow]
    rw [Real.sq_sqrt (by positivity : 0 ≤ 2 * ε + r ^ 2 * ‖(p.2 : EuclideanSpace ℝ (Fin (n - k)))‖ ^ 2)]
    rw [norm_smul]
    rw [Real.norm_eq_abs]
    rw [mul_pow]
    rw [sq_abs]
    have hx : ‖(p.1 : EuclideanSpace ℝ (Fin k))‖ ^ 2 ≤ 1 := by
      have hneg : -1 ≤ ‖(p.1 : EuclideanSpace ℝ (Fin k))‖ := by
        linarith [norm_nonneg (p.1 : EuclideanSpace ℝ (Fin k))]
      exact (sq_le_sq' hneg p.1.2).trans_eq (by norm_num : (1 : ℝ) ^ 2 = 1)
    have hw : ‖(p.2 : EuclideanSpace ℝ (Fin (n - k)))‖ ^ 2 ≤ 1 := by
      have hneg : -1 ≤ ‖(p.2 : EuclideanSpace ℝ (Fin (n - k)))‖ := by
        linarith [norm_nonneg (p.2 : EuclideanSpace ℝ (Fin (n - k)))]
      exact (sq_le_sq' hneg p.2.2).trans_eq (by norm_num : (1 : ℝ) ^ 2 = 1)
    have hcore : (2 * ε + r ^ 2 * ‖(p.2 : EuclideanSpace ℝ (Fin (n - k)))‖ ^ 2) *
        ‖(p.1 : EuclideanSpace ℝ (Fin k))‖ ^ 2 ≤
        2 * ε + r ^ 2 * ‖(p.2 : EuclideanSpace ℝ (Fin (n - k)))‖ ^ 2 := by
      simpa using mul_le_mul_of_nonneg_left hx
        (by positivity : 0 ≤ 2 * ε + r ^ 2 * ‖(p.2 : EuclideanSpace ℝ (Fin (n - k)))‖ ^ 2)
    nlinarith [hcore]

theorem mem_modelHandle {n k : ℕ} (hk : k ≤ n) (ε r : ℝ) (hε : 0 < ε) (hr : r ≠ 0)
    (y : MorseModel n) :
    y ∈ modelHandle hk ε r ↔
      ∃ p : StandardHandle k (n - k), modelHandleMap hk ε r p = y := by
  constructor
  · intro hy
    dsimp [modelHandle] at hy
    rcases hy with ⟨hb, ha⟩
    let a : EuclideanSpace ℝ (Fin k) := negPart hk y
    let b : EuclideanSpace ℝ (Fin (n - k)) := posPart hk y
    have hscale : 0 < Real.sqrt (2 * ε + ‖b‖ ^ 2) := by
      have hpos : 0 < 2 * ε + ‖b‖ ^ 2 := by positivity
      exact Real.sqrt_pos.2 hpos
    let x : EuclideanSpace ℝ (Fin k) := (Real.sqrt (2 * ε + ‖b‖ ^ 2))⁻¹ • a
    have hx' : ‖x‖ ^ 2 ≤ 1 := by
      dsimp [x]
      rw [norm_smul]
      rw [Real.norm_eq_abs]
      rw [mul_pow]
      rw [sq_abs]
      rw [inv_pow]
      rw [Real.sq_sqrt (by positivity : 0 ≤ 2 * ε + ‖b‖ ^ 2)]
      rw [mul_comm]
      rw [← div_eq_mul_inv]
      rw [div_le_one (by positivity : 0 < 2 * ε + ‖b‖ ^ 2)]
      nlinarith [ha]
    have hxle : ‖x‖ ≤ 1 := by
      exact le_of_sq_le_sq (by simpa using hx') (by norm_num)
    let w : EuclideanSpace ℝ (Fin (n - k)) := r⁻¹ • b
    have hw' : ‖w‖ ^ 2 ≤ 1 := by
      dsimp [w]
      rw [norm_smul]
      rw [Real.norm_eq_abs]
      rw [mul_pow]
      rw [sq_abs]
      rw [inv_pow]
      rw [mul_comm]
      rw [← div_eq_mul_inv]
      rw [div_le_one (sq_pos_of_ne_zero hr)]
      exact hb
    have hwle : ‖w‖ ≤ 1 := by
      exact le_of_sq_le_sq (by simpa using hw') (by norm_num)
    have hw2 : r ^ 2 * ‖w‖ ^ 2 = ‖b‖ ^ 2 := by
      dsimp [w]
      calc
        r ^ 2 * ‖(r⁻¹ • b : EuclideanSpace ℝ (Fin (n - k)))‖ ^ 2 =
            r ^ 2 * ((r⁻¹) ^ 2 * ‖b‖ ^ 2) := by
              rw [norm_smul]
              rw [Real.norm_eq_abs]
              rw [mul_pow]
              rw [sq_abs]
        _ = (r ^ 2 * (r ^ 2)⁻¹) * ‖b‖ ^ 2 := by
          rw [inv_pow]
          ring
        _ = ‖b‖ ^ 2 := by
          rw [mul_inv_cancel₀ (pow_ne_zero 2 hr), one_mul]
    have hcore_eq : Real.sqrt (2 * ε + r ^ 2 * ‖w‖ ^ 2) =
        Real.sqrt (2 * ε + ‖b‖ ^ 2) := by
      rw [hw2]
    have hcore_scale : Real.sqrt (2 * ε + ‖b‖ ^ 2) *
        (Real.sqrt (2 * ε + ‖b‖ ^ 2))⁻¹ = 1 := by
      exact mul_inv_cancel₀ (ne_of_gt hscale)
    have hsmul1 : (Real.sqrt (2 * ε + ‖b‖ ^ 2)) •
        ((Real.sqrt (2 * ε + ‖b‖ ^ 2))⁻¹ • a) = a := by
      rw [smul_smul]
      rw [hcore_scale, one_smul]
    have hsmul2 : r • (r⁻¹ • b) = b := by
      rw [smul_smul]
      rw [mul_inv_cancel₀ hr, one_smul]
    refine ⟨(⟨x, hxle⟩, ⟨w, hwle⟩), ?_⟩
    dsimp [modelHandleMap, x, w]
    rw [hcore_eq]
    rw [hsmul1, hsmul2]
    change recombine hk (negPart hk y) (posPart hk y) = y
    exact recombine_decompose hk y
  · intro hp
    rcases hp with ⟨p, rfl⟩
    exact modelHandleMap_mem hk ε r (le_of_lt hε) p

theorem modelHandle_meets_lower_sublevel {n k : ℕ} (hk : k ≤ n) (c ε r : ℝ) (hε : 0 < ε)
    (hr : r ≠ 0) :
    modelHandle hk ε r ∩ sublevel (morseNormalForm hk c) (c - ε) =
      Set.range (fun p : CellBoundary k × ClosedCell (n - k) =>
        modelHandleMap hk ε r (cellBoundaryInclusion k p.1, p.2)) := by
  ext y
  constructor
  · intro hy
    rcases hy with ⟨hyh, hyl⟩
    have hmem := (mem_modelHandle hk ε r hε hr y).1 hyh
    rcases hmem with ⟨p, hp⟩
    have hf : morseNormalForm hk c y = c - ε := by
      apply le_antisymm
      · change y ∈ sublevel (morseNormalForm hk c) (c - ε)
        exact hyl
      · rw [← hp]
        exact modelHandleMap_f_ge hk c ε r (le_of_lt hε) p
    have hx : ‖(p.1 : EuclideanSpace ℝ (Fin k))‖ = 1 := by
      have hpf := modelHandleMap_f_eq_lower_iff hk c ε r hε p
      exact hpf.1 (by simpa [hp] using hf)
    refine ⟨(⟨(p.1 : EuclideanSpace ℝ (Fin k)), hx⟩, p.2), ?_⟩
    have hpi : (cellBoundaryInclusion k ⟨(p.1 : EuclideanSpace ℝ (Fin k)), hx⟩ : ClosedCell k) = p.1 := by
      apply Subtype.ext
      rfl
    simpa [hpi] using hp
  · intro hy
    rcases hy with ⟨p, hp⟩
    constructor
    · rw [← hp]
      exact modelHandleMap_mem hk ε r (le_of_lt hε) (cellBoundaryInclusion k p.1, p.2)
    · rw [← hp]
      change morseNormalForm hk c (modelHandleMap hk ε r (cellBoundaryInclusion k p.1, p.2)) ≤ c - ε
      rw [modelHandleMap_f_boundary hk c ε r (le_of_lt hε) p.1 p.2]

theorem modelFlow_modelHandle_mem_attachingRegion {n k : ℕ} (hk : k ≤ n) (c ε r : ℝ)
    (hε : 0 < ε) (hr : r ≠ 0) (y : MorseModel n) (hy : y ∈ modelHandle hk ε r)
    (hflow : morseNormalForm hk c y - (c - ε) ≤ ‖posPart hk y‖ ^ 2 / 2) :
    modelFlow hk (morseNormalForm hk c y - (c - ε)) y ∈
      modelHandle hk ε r ∩ sublevel (morseNormalForm hk c) (c - ε) := by
  let t : ℝ := morseNormalForm hk c y - (c - ε)
  have ht0 : 0 ≤ t := by
    dsimp [t]
    rcases (mem_modelHandle hk ε r hε hr y).1 hy with ⟨p, hp⟩
    rw [← hp]
    rw [← sub_nonneg]
    rw [modelHandleMap_f_sub hk c ε r (le_of_lt hε) p]
    have hnonneg : 0 ≤ 2 * ε + r ^ 2 * ‖(p.2 : EuclideanSpace ℝ (Fin (n - k)))‖ ^ 2 := by positivity
    have hle : ‖(p.1 : EuclideanSpace ℝ (Fin k))‖ ^ 2 ≤ 1 := by
      have hneg : -1 ≤ ‖(p.1 : EuclideanSpace ℝ (Fin k))‖ := by
        linarith [norm_nonneg (p.1 : EuclideanSpace ℝ (Fin k))]
      exact (sq_le_sq' hneg p.1.2).trans_eq (by norm_num : (1 : ℝ) ^ 2 = 1)
    nlinarith [hnonneg, hle]
  have hf : morseNormalForm hk c (modelFlow hk t y) = c - ε := by
    rw [modelFlow_f_sub hk c t y ht0 hflow]
    dsimp [t]
    ring
  constructor
  · rcases hy with ⟨hb, ha⟩
    dsimp [modelHandle]
    rw [modelFlow_negPart]
    have hpos := modelFlow_posPart_norm_sq hk t y ht0 hflow
    rw [hpos]
    constructor
    · nlinarith [hb, ht0]
    · have hmain : ‖negPart hk y‖ ^ 2 = ‖posPart hk y‖ ^ 2 - 2 * t + 2 * ε := by
        dsimp [t]
        have hsplit := morseNormalForm_split hk c y
        rw [hsplit]
        ring
      rw [hmain]
  · change morseNormalForm hk c (modelFlow hk t y) ≤ c - ε
    rw [hf]

noncomputable def smoothCap (ε r δ : ℝ) (t : ℝ) : ℝ :=
  r ^ 2 + (t - 2 * ε - r ^ 2) * Real.smoothTransition ((t - (r ^ 2 + 2 * ε - δ)) / (2 * δ))

theorem smoothCap_contDiff (ε r δ : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (smoothCap ε r δ) := by
  have hcomp : ContDiff ℝ (⊤ : ℕ∞)
      (fun t : ℝ => r ^ 2 + (t - 2 * ε - r ^ 2) * Real.smoothTransition
        ((t - (r ^ 2 + 2 * ε - δ)) / (2 * δ))) := by
    fun_prop
  simpa [smoothCap] using hcomp

theorem smoothCap_lower {ε r δ t : ℝ} (hδ : 0 < δ) (ht : t ≤ r ^ 2 + 2 * ε - δ) :
    smoothCap ε r δ t = r ^ 2 := by
  dsimp [smoothCap]
  have harg : (t - (r ^ 2 + 2 * ε - δ)) / (2 * δ) ≤ 0 := by
    have hden : 0 < 2 * δ := by positivity
    exact (div_le_iff₀ hden).2 (by nlinarith [ht])
  rw [Real.smoothTransition.zero_of_nonpos harg]
  ring

theorem smoothCap_upper {ε r δ t : ℝ} (hδ : 0 < δ) (ht : r ^ 2 + 2 * ε + δ ≤ t) :
    smoothCap ε r δ t = t - 2 * ε := by
  dsimp [smoothCap]
  have harg : 1 ≤ (t - (r ^ 2 + 2 * ε - δ)) / (2 * δ) := by
    have hden : 0 < 2 * δ := by positivity
    exact (le_div_iff₀ hden).2 (by nlinarith [ht])
  rw [Real.smoothTransition.one_of_one_le harg]
  ring

theorem smoothCap_pos {ε r δ t : ℝ} (hδ0 : 0 < δ) (hδr : δ < r ^ 2) :
    0 < smoothCap ε r δ t := by
  by_cases ht₁ : t ≤ r ^ 2 + 2 * ε - δ
  · rw [smoothCap_lower hδ0 ht₁]
    nlinarith
  · by_cases ht₂ : r ^ 2 + 2 * ε + δ ≤ t
    · rw [smoothCap_upper hδ0 ht₂]
      nlinarith [ht₂]
    · have hmid : r ^ 2 + 2 * ε - δ < t ∧ t < r ^ 2 + 2 * ε + δ := by
        constructor <;> linarith
      dsimp [smoothCap]
      have hτ : 0 ≤ Real.smoothTransition ((t - (r ^ 2 + 2 * ε - δ)) / (2 * δ)) :=
        Real.smoothTransition.nonneg _
      have hτle : Real.smoothTransition ((t - (r ^ 2 + 2 * ε - δ)) / (2 * δ)) ≤ 1 :=
        Real.smoothTransition.le_one _
      have hneg : r ^ 2 + 2 * ε - δ - 2 * ε - r ^ 2 ≤ t - 2 * ε - r ^ 2 := by
        nlinarith [hmid.1]
      have hlo : r ^ 2 + (t - 2 * ε - r ^ 2) * Real.smoothTransition
          ((t - (r ^ 2 + 2 * ε - δ)) / (2 * δ)) ≥ r ^ 2 - δ := by
        have hdelta : t - 2 * ε - r ^ 2 ≥ -δ := by
          nlinarith [hmid.1]
        nlinarith [hτ, hτle, hdelta]
      nlinarith [hlo, hδr]

noncomputable def modelAttachedFunction {n k : ℕ} (hk : k ≤ n) (c ε r δ : ℝ) (y : MorseModel n) : ℝ :=
  c + (1 / 2) * (‖posPart hk y‖ ^ (2 : ℕ) - smoothCap ε r δ (‖negPart hk y‖ ^ (2 : ℕ)))

noncomputable def modelAttachedRegion {n k : ℕ} (hk : k ≤ n) (ε r δ : ℝ) : Set (MorseModel n) :=
  {y : MorseModel n | ‖posPart hk y‖ ^ (2 : ℕ) ≤ smoothCap ε r δ (‖negPart hk y‖ ^ (2 : ℕ))}

theorem modelAttachedRegion_eq_sublevel {n k : ℕ} (hk : k ≤ n) (c ε r δ : ℝ) :
    modelAttachedRegion hk ε r δ = sublevel (modelAttachedFunction hk c ε r δ) c := by
  ext y
  change ‖posPart hk y‖ ^ 2 ≤ smoothCap ε r δ (‖negPart hk y‖ ^ 2) ↔
    c + (1 / 2) * (‖posPart hk y‖ ^ 2 - smoothCap ε r δ (‖negPart hk y‖ ^ 2)) ≤ c
  constructor
  · intro h
    nlinarith
  · intro h
    nlinarith

theorem modelAttachedRegion_iff_sublevel {n k : ℕ} (hk : k ≤ n) (c ε r δ : ℝ) (y : MorseModel n) :
    y ∈ modelAttachedRegion hk ε r δ ↔ modelAttachedFunction hk c ε r δ y ≤ c := by
  have heq : (y ∈ modelAttachedRegion hk ε r δ) =
      (y ∈ sublevel (modelAttachedFunction hk c ε r δ) c) :=
    congrArg (fun s : Set (MorseModel n) => y ∈ s)
      (modelAttachedRegion_eq_sublevel hk c ε r δ)
  rw [show (y ∈ sublevel (modelAttachedFunction hk c ε r δ) c) =
      (modelAttachedFunction hk c ε r δ y ≤ c) from rfl] at heq
  exact Iff.of_eq heq

theorem contDiff_modelAttachedFunction {n k : ℕ} (hk : k ≤ n) (c ε r δ : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (modelAttachedFunction hk c ε r δ) := by
  have hnormNeg : ContDiff ℝ (⊤ : ℕ∞) (fun y : MorseModel n => ‖negPart hk y‖ ^ 2) := by
    rw [show (fun y : MorseModel n => ‖negPart hk y‖ ^ 2) =
        fun y : MorseModel n => ∑ i : Fin k, (negPart hk y i) ^ 2 by
      funext y
      exact EuclideanSpace.real_norm_sq_eq (negPart hk y)]
    fun_prop
  have hnormPos : ContDiff ℝ (⊤ : ℕ∞) (fun y : MorseModel n => ‖posPart hk y‖ ^ 2) := by
    rw [show (fun y : MorseModel n => ‖posPart hk y‖ ^ 2) =
        fun y : MorseModel n => ∑ j : Fin (n - k), (posPart hk y j) ^ 2 by
      funext y
      exact EuclideanSpace.real_norm_sq_eq (posPart hk y)]
    fun_prop
  have hcap : ContDiff ℝ (⊤ : ℕ∞)
      (fun y : MorseModel n => smoothCap ε r δ (‖negPart hk y‖ ^ 2)) :=
    (smoothCap_contDiff ε r δ).comp hnormNeg
  have hmain : ContDiff ℝ (⊤ : ℕ∞)
      (fun y : MorseModel n => c + (1 / 2) * (‖posPart hk y‖ ^ 2 - smoothCap ε r δ (‖negPart hk y‖ ^ 2))) := by
    exact (contDiff_const.add ((contDiff_const.mul (hnormPos.sub hcap))))
  change ContDiff ℝ (⊤ : ℕ∞)
    (fun y : MorseModel n => c + (1 / 2) * (‖posPart hk y‖ ^ 2 - smoothCap ε r δ (‖negPart hk y‖ ^ 2)))
  exact hmain

theorem smoothCap_nonneg {ε r δ t : ℝ} (hδ0 : 0 < δ) (hδr : δ < r ^ 2) :
    0 ≤ smoothCap ε r δ t :=
  le_of_lt (smoothCap_pos hδ0 hδr)

noncomputable def modelAttachedStretch {n k : ℕ} (hk : k ≤ n) (ε r δ : ℝ)
    (y : MorseModel n) : MorseModel n :=
  recombine hk (negPart hk y)
    ((Real.sqrt (smoothCap ε r δ (‖negPart hk y‖ ^ 2) / (‖negPart hk y‖ ^ 2 + r ^ 2))) •
      posPart hk y)

noncomputable def modelAttachedUnstretch {n k : ℕ} (hk : k ≤ n) (ε r δ : ℝ)
    (y : MorseModel n) : MorseModel n :=
  recombine hk (negPart hk y)
    ((Real.sqrt ((‖negPart hk y‖ ^ 2 + r ^ 2) / smoothCap ε r δ (‖negPart hk y‖ ^ 2))) •
      posPart hk y)

theorem modelAttachedStretch_negPart {n k : ℕ} (hk : k ≤ n) (ε r δ : ℝ) (y : MorseModel n) :
    negPart hk (modelAttachedStretch hk ε r δ y) = negPart hk y := by
  dsimp [modelAttachedStretch]
  rw [negPart_recombine]

theorem modelAttachedStretch_posPart {n k : ℕ} (hk : k ≤ n) (ε r δ : ℝ) (y : MorseModel n) :
    posPart hk (modelAttachedStretch hk ε r δ y) =
      (Real.sqrt (smoothCap ε r δ (‖negPart hk y‖ ^ 2) / (‖negPart hk y‖ ^ 2 + r ^ 2))) •
        posPart hk y := by
  dsimp [modelAttachedStretch]
  rw [posPart_recombine]

theorem modelAttachedStretch_negPart_norm_sq {n k : ℕ} (hk : k ≤ n) (ε r δ : ℝ)
    (y : MorseModel n) :
    ‖negPart hk (modelAttachedStretch hk ε r δ y)‖ ^ (2 : ℕ) = ‖negPart hk y‖ ^ (2 : ℕ) := by
  have hne : ‖negPart hk (modelAttachedStretch hk ε r δ y)‖ = ‖negPart hk y‖ := by
    exact congrArg (norm : EuclideanSpace ℝ (Fin k) → ℝ)
      (modelAttachedStretch_negPart hk ε r δ y)
  simp [hne]

theorem modelAttachedUnstretch_negPart {n k : ℕ} (hk : k ≤ n) (ε r δ : ℝ) (y : MorseModel n) :
    negPart hk (modelAttachedUnstretch hk ε r δ y) = negPart hk y := by
  dsimp [modelAttachedUnstretch]
  rw [negPart_recombine]

theorem modelAttachedUnstretch_negPart_norm_sq {n k : ℕ} (hk : k ≤ n) (ε r δ : ℝ)
    (y : MorseModel n) :
    ‖negPart hk (modelAttachedUnstretch hk ε r δ y)‖ ^ (2 : ℕ) = ‖negPart hk y‖ ^ (2 : ℕ) := by
  have hne : ‖negPart hk (modelAttachedUnstretch hk ε r δ y)‖ = ‖negPart hk y‖ := by
    exact congrArg (norm : EuclideanSpace ℝ (Fin k) → ℝ)
      (modelAttachedUnstretch_negPart hk ε r δ y)
  simp [hne]

theorem modelAttachedUnstretch_posPart {n k : ℕ} (hk : k ≤ n) (ε r δ : ℝ) (y : MorseModel n) :
    posPart hk (modelAttachedUnstretch hk ε r δ y) =
      (Real.sqrt ((‖negPart hk y‖ ^ 2 + r ^ 2) / smoothCap ε r δ (‖negPart hk y‖ ^ 2))) •
        posPart hk y := by
  dsimp [modelAttachedUnstretch]
  rw [posPart_recombine]

theorem modelAttachedStretch_posPart_norm_sq {n k : ℕ} (hk : k ≤ n) (ε r δ : ℝ)
    (hδ0 : 0 < δ) (hδr : δ < r ^ 2) (y : MorseModel n) :
    ‖posPart hk (modelAttachedStretch hk ε r δ y)‖ ^ 2 =
      (smoothCap ε r δ (‖negPart hk y‖ ^ 2) / (‖negPart hk y‖ ^ 2 + r ^ 2)) *
        ‖posPart hk y‖ ^ 2 := by
  rw [modelAttachedStretch_posPart]
  rw [norm_smul]
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  rw [mul_pow]
  rw [Real.sq_sqrt (div_nonneg (smoothCap_nonneg hδ0 hδr)
    (by positivity : 0 ≤ ‖negPart hk y‖ ^ 2 + r ^ 2))]

theorem modelAttachedUnstretch_posPart_norm_sq {n k : ℕ} (hk : k ≤ n) (ε r δ : ℝ)
    (hδ0 : 0 < δ) (hδr : δ < r ^ 2) (y : MorseModel n) :
    ‖posPart hk (modelAttachedUnstretch hk ε r δ y)‖ ^ 2 =
      ((‖negPart hk y‖ ^ 2 + r ^ 2) / smoothCap ε r δ (‖negPart hk y‖ ^ 2)) *
        ‖posPart hk y‖ ^ 2 := by
  rw [modelAttachedUnstretch_posPart]
  rw [norm_smul]
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  rw [mul_pow]
  rw [Real.sq_sqrt (div_nonneg (by positivity : 0 ≤ ‖negPart hk y‖ ^ 2 + r ^ 2)
    (smoothCap_nonneg hδ0 hδr))]

theorem modelAttachedStretch_mem {n k : ℕ} (hk : k ≤ n) (ε r δ : ℝ)
    (hδ0 : 0 < δ) (hδr : δ < r ^ 2) (hr : r ≠ 0)
    (y : MorseModel n) (hy : ‖posPart hk y‖ ^ 2 ≤ ‖negPart hk y‖ ^ 2 + r ^ 2) :
    modelAttachedStretch hk ε r δ y ∈ modelAttachedRegion hk ε r δ := by
  dsimp [modelAttachedRegion]
  have hneg' : ‖negPart hk (modelAttachedStretch hk ε r δ y)‖ ^ (2 : ℕ) = ‖negPart hk y‖ ^ (2 : ℕ) :=
    modelAttachedStretch_negPart_norm_sq hk ε r δ y
  have hden : 0 < ‖negPart hk y‖ ^ 2 + r ^ 2 := by
    have hr2 : 0 < r ^ 2 := sq_pos_of_ne_zero hr
    nlinarith [sq_nonneg (‖negPart hk y‖ : ℝ)]
  have hnonneg : 0 ≤ smoothCap ε r δ (‖negPart hk y‖ ^ 2) / (‖negPart hk y‖ ^ 2 + r ^ 2) := by
    exact div_nonneg (smoothCap_nonneg hδ0 hδr) (le_of_lt hden)
  have hmain : (smoothCap ε r δ (‖negPart hk y‖ ^ 2) / (‖negPart hk y‖ ^ 2 + r ^ 2)) *
        ‖posPart hk y‖ ^ 2 ≤ smoothCap ε r δ (‖negPart hk y‖ ^ 2) := by
    have hle' : (smoothCap ε r δ (‖negPart hk y‖ ^ 2) / (‖negPart hk y‖ ^ 2 + r ^ 2)) *
          ‖posPart hk y‖ ^ 2 ≤
        (smoothCap ε r δ (‖negPart hk y‖ ^ 2) / (‖negPart hk y‖ ^ 2 + r ^ 2)) *
          (‖negPart hk y‖ ^ 2 + r ^ 2) :=
      mul_le_mul_of_nonneg_left hy hnonneg
    rwa [div_mul_cancel₀ (smoothCap ε r δ (‖negPart hk y‖ ^ 2)) (ne_of_gt hden)] at hle'
  calc
    ‖posPart hk (modelAttachedStretch hk ε r δ y)‖ ^ 2
        = (smoothCap ε r δ (‖negPart hk y‖ ^ 2) / (‖negPart hk y‖ ^ 2 + r ^ 2)) *
            ‖posPart hk y‖ ^ 2 :=
      modelAttachedStretch_posPart_norm_sq hk ε r δ hδ0 hδr y
    _ ≤ smoothCap ε r δ (‖negPart hk y‖ ^ 2) := hmain
    _ = smoothCap ε r δ (‖negPart hk (modelAttachedStretch hk ε r δ y)‖ ^ 2) :=
      congrArg (smoothCap ε r δ) hneg'.symm

theorem modelAttachedUnstretch_mem {n k : ℕ} (hk : k ≤ n) (ε r δ : ℝ) (hδ0 : 0 < δ)
    (hδr : δ < r ^ 2) (y : MorseModel n) (hy : y ∈ modelAttachedRegion hk ε r δ) :
    ‖posPart hk (modelAttachedUnstretch hk ε r δ y)‖ ^ 2 ≤ ‖negPart hk y‖ ^ 2 + r ^ 2 := by
  dsimp [modelAttachedRegion] at hy
  have hnorm := modelAttachedUnstretch_posPart_norm_sq hk ε r δ hδ0 hδr y
  rw [hnorm]
  have hs : 0 < smoothCap ε r δ (‖negPart hk y‖ ^ 2) :=
    smoothCap_pos (ε := ε) (r := r) (δ := δ) (t := ‖negPart hk y‖ ^ 2) hδ0 hδr
  have hnonneg : 0 ≤ (‖negPart hk y‖ ^ 2 + r ^ 2) / smoothCap ε r δ (‖negPart hk y‖ ^ 2) := by
    exact div_nonneg (by positivity : 0 ≤ ‖negPart hk y‖ ^ 2 + r ^ 2) (le_of_lt hs)
  have hmain : ((‖negPart hk y‖ ^ 2 + r ^ 2) / smoothCap ε r δ (‖negPart hk y‖ ^ 2)) *
        ‖posPart hk y‖ ^ 2 ≤ ‖negPart hk y‖ ^ 2 + r ^ 2 := by
    have hle' : ((‖negPart hk y‖ ^ 2 + r ^ 2) / smoothCap ε r δ (‖negPart hk y‖ ^ 2)) *
          ‖posPart hk y‖ ^ 2 ≤
        ((‖negPart hk y‖ ^ 2 + r ^ 2) / smoothCap ε r δ (‖negPart hk y‖ ^ 2)) *
          smoothCap ε r δ (‖negPart hk y‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hy hnonneg
    rwa [div_mul_cancel₀ (‖negPart hk y‖ ^ 2 + r ^ 2) (ne_of_gt hs)] at hle'
  exact hmain

theorem modelAttachedUnstretch_stretch {n k : ℕ} (hk : k ≤ n) (ε r δ : ℝ)
    (hδ0 : 0 < δ) (hδr : δ < r ^ 2) (hr : r ≠ 0) (y : MorseModel n) :
    modelAttachedUnstretch hk ε r δ (modelAttachedStretch hk ε r δ y) = y := by
  let s : ℝ := smoothCap ε r δ (‖negPart hk y‖ ^ 2)
  let t : ℝ := ‖negPart hk y‖ ^ 2
  have hs : 0 < s := by
    dsimp [s]
    exact smoothCap_pos (ε := ε) (r := r) (δ := δ) (t := ‖negPart hk y‖ ^ 2) hδ0 hδr
  have ht : 0 < t + r ^ 2 := by
    dsimp [t]
    have hr2 : 0 < r ^ 2 := sq_pos_of_ne_zero hr
    nlinarith [sq_nonneg (‖negPart hk y‖ : ℝ)]
  have hnonneg1 : 0 ≤ s / (t + r ^ 2) := div_nonneg (le_of_lt hs) (le_of_lt ht)
  have hnonneg2 : 0 ≤ (t + r ^ 2) / s := div_nonneg (le_of_lt ht) (le_of_lt hs)
  have hsq : (Real.sqrt (s / (t + r ^ 2)) * Real.sqrt ((t + r ^ 2) / s)) ^ 2 = 1 := by
    rw [mul_pow]
    rw [Real.sq_sqrt hnonneg1]
    rw [Real.sq_sqrt hnonneg2]
    field_simp [ne_of_gt hs, ne_of_gt ht]
  have hnonneg' : 0 ≤ Real.sqrt (s / (t + r ^ 2)) * Real.sqrt ((t + r ^ 2) / s) := by positivity
  have hscalar : Real.sqrt (s / (t + r ^ 2)) * Real.sqrt ((t + r ^ 2) / s) = 1 := by
    have hsq' : (Real.sqrt (s / (t + r ^ 2)) * Real.sqrt ((t + r ^ 2) / s)) ^ 2 = (1 : ℝ) ^ 2 := by
      simpa using hsq
    exact (sq_eq_sq_iff_eq_or_eq_neg.mp hsq').resolve_right (by nlinarith [hnonneg'])
  calc
    modelAttachedUnstretch hk ε r δ (modelAttachedStretch hk ε r δ y) =
        recombine hk (negPart hk (modelAttachedUnstretch hk ε r δ (modelAttachedStretch hk ε r δ y)))
          (posPart hk (modelAttachedUnstretch hk ε r δ (modelAttachedStretch hk ε r δ y))) :=
      (recombine_decompose hk (modelAttachedUnstretch hk ε r δ (modelAttachedStretch hk ε r δ y))).symm
    _ = recombine hk (negPart hk y) (posPart hk y) := by
      congr 1
      · simp [modelAttachedUnstretch_negPart, modelAttachedStretch_negPart]
      · have hneg : ‖negPart hk (modelAttachedStretch hk ε r δ y)‖ ^ 2 = t := by
          dsimp [t]
          exact modelAttachedStretch_negPart_norm_sq hk ε r δ y
        have hpos1 : posPart hk (modelAttachedStretch hk ε r δ y) =
            Real.sqrt (s / (t + r ^ 2)) • posPart hk y := by
          dsimp [s, t]
          exact modelAttachedStretch_posPart hk ε r δ y
        have hpos2 : posPart hk (modelAttachedUnstretch hk ε r δ (modelAttachedStretch hk ε r δ y)) =
            Real.sqrt ((t + r ^ 2) / s) • posPart hk (modelAttachedStretch hk ε r δ y) := by
          dsimp [s, t]
          rw [modelAttachedUnstretch_posPart]
          rw [hneg]
        rw [hpos2, hpos1, smul_smul, mul_comm, hscalar, one_smul]
    _ = y := recombine_decompose hk y

theorem modelAttachedStretch_unstretch {n k : ℕ} (hk : k ≤ n) (ε r δ : ℝ)
    (hδ0 : 0 < δ) (hδr : δ < r ^ 2) (hr : r ≠ 0) (y : MorseModel n) :
    modelAttachedStretch hk ε r δ (modelAttachedUnstretch hk ε r δ y) = y := by
  let s : ℝ := smoothCap ε r δ (‖negPart hk y‖ ^ 2)
  let t : ℝ := ‖negPart hk y‖ ^ 2
  have hs : 0 < s := by
    dsimp [s]
    exact smoothCap_pos (ε := ε) (r := r) (δ := δ) (t := ‖negPart hk y‖ ^ 2) hδ0 hδr
  have ht : 0 < t + r ^ 2 := by
    dsimp [t]
    have hr2 : 0 < r ^ 2 := sq_pos_of_ne_zero hr
    nlinarith [sq_nonneg (‖negPart hk y‖ : ℝ)]
  have hnonneg1 : 0 ≤ s / (t + r ^ 2) := div_nonneg (le_of_lt hs) (le_of_lt ht)
  have hnonneg2 : 0 ≤ (t + r ^ 2) / s := div_nonneg (le_of_lt ht) (le_of_lt hs)
  have hsq : (Real.sqrt (s / (t + r ^ 2)) * Real.sqrt ((t + r ^ 2) / s)) ^ 2 = 1 := by
    rw [mul_pow]
    rw [Real.sq_sqrt hnonneg1]
    rw [Real.sq_sqrt hnonneg2]
    field_simp [ne_of_gt hs, ne_of_gt ht]
  have hnonneg' : 0 ≤ Real.sqrt (s / (t + r ^ 2)) * Real.sqrt ((t + r ^ 2) / s) := by positivity
  have hscalar : Real.sqrt (s / (t + r ^ 2)) * Real.sqrt ((t + r ^ 2) / s) = 1 := by
    have hsq' : (Real.sqrt (s / (t + r ^ 2)) * Real.sqrt ((t + r ^ 2) / s)) ^ 2 = (1 : ℝ) ^ 2 := by
      simpa using hsq
    exact (sq_eq_sq_iff_eq_or_eq_neg.mp hsq').resolve_right (by nlinarith [hnonneg'])
  calc
    modelAttachedStretch hk ε r δ (modelAttachedUnstretch hk ε r δ y) =
        recombine hk (negPart hk (modelAttachedStretch hk ε r δ (modelAttachedUnstretch hk ε r δ y)))
          (posPart hk (modelAttachedStretch hk ε r δ (modelAttachedUnstretch hk ε r δ y))) :=
      (recombine_decompose hk (modelAttachedStretch hk ε r δ (modelAttachedUnstretch hk ε r δ y))).symm
    _ = recombine hk (negPart hk y) (posPart hk y) := by
      congr 1
      · simp [modelAttachedStretch_negPart, modelAttachedUnstretch_negPart]
      · have hneg : ‖negPart hk (modelAttachedUnstretch hk ε r δ y)‖ ^ 2 = t := by
          dsimp [t]
          exact modelAttachedUnstretch_negPart_norm_sq hk ε r δ y
        have hpos1 : posPart hk (modelAttachedUnstretch hk ε r δ y) =
            Real.sqrt ((t + r ^ 2) / s) • posPart hk y := by
          dsimp [s, t]
          exact modelAttachedUnstretch_posPart hk ε r δ y
        have hpos2 : posPart hk (modelAttachedStretch hk ε r δ (modelAttachedUnstretch hk ε r δ y)) =
            Real.sqrt (s / (t + r ^ 2)) • posPart hk (modelAttachedUnstretch hk ε r δ y) := by
          dsimp [s, t]
          rw [modelAttachedStretch_posPart]
          rw [hneg]
        rw [hpos2, hpos1, smul_smul, hscalar, one_smul]
    _ = y := recombine_decompose hk y

theorem contDiff_modelAttachedStretch {n k : ℕ} (hk : k ≤ n) (ε r δ : ℝ)
    (hδ0 : 0 < δ) (hδr : δ < r ^ 2) (hr : r ≠ 0) :
    ContDiff ℝ (⊤ : ℕ∞) (modelAttachedStretch hk ε r δ) := by
  have hnormNeg : ContDiff ℝ (⊤ : ℕ∞) (fun y : MorseModel n => ‖negPart hk y‖ ^ 2) := by
    rw [show (fun y : MorseModel n => ‖negPart hk y‖ ^ 2) =
        fun y : MorseModel n => ∑ i : Fin k, (negPart hk y i) ^ 2 by
      funext y
      exact EuclideanSpace.real_norm_sq_eq (negPart hk y)]
    fun_prop
  have hcap : ContDiff ℝ (⊤ : ℕ∞)
      (fun y : MorseModel n => smoothCap ε r δ (‖negPart hk y‖ ^ 2)) :=
    (smoothCap_contDiff ε r δ).comp hnormNeg
  have hden : ContDiff ℝ (⊤ : ℕ∞)
      (fun y : MorseModel n => ‖negPart hk y‖ ^ 2 + r ^ 2) := by
    exact hnormNeg.add (contDiff_const : ContDiff ℝ (⊤ : ℕ∞) (fun _ : MorseModel n => r ^ 2))
  have hden_pos : ∀ y : MorseModel n, 0 < ‖negPart hk y‖ ^ 2 + r ^ 2 := by
    intro y
    have hr2 : 0 < r ^ 2 := sq_pos_of_ne_zero hr
    nlinarith [sq_nonneg (‖negPart hk y‖ : ℝ)]
  have harg : ContDiff ℝ (⊤ : ℕ∞)
      (fun y : MorseModel n => smoothCap ε r δ (‖negPart hk y‖ ^ 2) / (‖negPart hk y‖ ^ 2 + r ^ 2)) :=
    hcap.div hden (by intro y; exact ne_of_gt (hden_pos y))
  have hsqrt : ContDiff ℝ (⊤ : ℕ∞)
      (fun y : MorseModel n => Real.sqrt (smoothCap ε r δ (‖negPart hk y‖ ^ 2) /
        (‖negPart hk y‖ ^ 2 + r ^ 2))) :=
    harg.sqrt (by
      intro y
      exact ne_of_gt (div_pos (smoothCap_pos (ε := ε) (r := r) (δ := δ)
        (t := ‖negPart hk y‖ ^ 2) hδ0 hδr) (hden_pos y)))
  rw [contDiff_pi]
  intro i
  by_cases hi : i.val < k
  · have hcomp : (fun y : MorseModel n => modelAttachedStretch hk ε r δ y i) =
        fun y : MorseModel n => y (negIdx hk ⟨i.val, hi⟩) := by
      funext y
      dsimp [modelAttachedStretch]
      rw [recombine, dif_pos hi]
      rfl
    rw [hcomp]
    fun_prop
  · have hcomp : (fun y : MorseModel n => modelAttachedStretch hk ε r δ y i) =
        fun y : MorseModel n =>
          Real.sqrt (smoothCap ε r δ (‖negPart hk y‖ ^ 2) / (‖negPart hk y‖ ^ 2 + r ^ 2)) *
            y (posIdx hk ⟨i.val - k, by
              have hkle : k ≤ i.val := le_of_not_gt hi
              have hi' : i.val < n := i.isLt
              omega⟩) := by
      funext y
      dsimp [modelAttachedStretch]
      rw [recombine, dif_neg hi]
      rfl
    rw [hcomp]
    have hcoord : ContDiff ℝ (⊤ : ℕ∞)
        (fun y : MorseModel n => y (posIdx hk ⟨i.val - k, by
          have hkle : k ≤ i.val := le_of_not_gt hi
          have hi' : i.val < n := i.isLt
          omega⟩)) := by
      fun_prop
    exact hsqrt.mul hcoord

theorem contDiff_modelAttachedUnstretch {n k : ℕ} (hk : k ≤ n) (ε r δ : ℝ)
    (hδ0 : 0 < δ) (hδr : δ < r ^ 2) (hr : r ≠ 0) :
    ContDiff ℝ (⊤ : ℕ∞) (modelAttachedUnstretch hk ε r δ) := by
  have hnormNeg : ContDiff ℝ (⊤ : ℕ∞) (fun y : MorseModel n => ‖negPart hk y‖ ^ 2) := by
    rw [show (fun y : MorseModel n => ‖negPart hk y‖ ^ 2) =
        fun y : MorseModel n => ∑ i : Fin k, (negPart hk y i) ^ 2 by
      funext y
      exact EuclideanSpace.real_norm_sq_eq (negPart hk y)]
    fun_prop
  have hcap : ContDiff ℝ (⊤ : ℕ∞)
      (fun y : MorseModel n => smoothCap ε r δ (‖negPart hk y‖ ^ 2)) :=
    (smoothCap_contDiff ε r δ).comp hnormNeg
  have hden : ContDiff ℝ (⊤ : ℕ∞)
      (fun y : MorseModel n => ‖negPart hk y‖ ^ 2 + r ^ 2) := by
    exact hnormNeg.add (contDiff_const : ContDiff ℝ (⊤ : ℕ∞) (fun _ : MorseModel n => r ^ 2))
  have hden_pos : ∀ y : MorseModel n, 0 < ‖negPart hk y‖ ^ 2 + r ^ 2 := by
    intro y
    have hr2 : 0 < r ^ 2 := sq_pos_of_ne_zero hr
    nlinarith [sq_nonneg (‖negPart hk y‖ : ℝ)]
  have hcap_pos : ∀ y : MorseModel n, 0 < smoothCap ε r δ (‖negPart hk y‖ ^ 2) := by
    intro y
    exact smoothCap_pos (ε := ε) (r := r) (δ := δ) (t := ‖negPart hk y‖ ^ 2) hδ0 hδr
  have harg : ContDiff ℝ (⊤ : ℕ∞)
      (fun y : MorseModel n => (‖negPart hk y‖ ^ 2 + r ^ 2) /
        smoothCap ε r δ (‖negPart hk y‖ ^ 2)) :=
    hden.div hcap (by intro y; exact ne_of_gt (hcap_pos y))
  have hsqrt : ContDiff ℝ (⊤ : ℕ∞)
      (fun y : MorseModel n => Real.sqrt ((‖negPart hk y‖ ^ 2 + r ^ 2) /
        smoothCap ε r δ (‖negPart hk y‖ ^ 2))) :=
    harg.sqrt (by
      intro y
      exact ne_of_gt (div_pos (hden_pos y) (hcap_pos y)))
  rw [contDiff_pi]
  intro i
  by_cases hi : i.val < k
  · have hcomp : (fun y : MorseModel n => modelAttachedUnstretch hk ε r δ y i) =
        fun y : MorseModel n => y (negIdx hk ⟨i.val, hi⟩) := by
      funext y
      dsimp [modelAttachedUnstretch]
      rw [recombine, dif_pos hi]
      rfl
    rw [hcomp]
    fun_prop
  · have hcomp : (fun y : MorseModel n => modelAttachedUnstretch hk ε r δ y i) =
        fun y : MorseModel n =>
          Real.sqrt ((‖negPart hk y‖ ^ 2 + r ^ 2) / smoothCap ε r δ (‖negPart hk y‖ ^ 2)) *
            y (posIdx hk ⟨i.val - k, by
              have hkle : k ≤ i.val := le_of_not_gt hi
              have hi' : i.val < n := i.isLt
              omega⟩) := by
      funext y
      dsimp [modelAttachedUnstretch]
      rw [recombine, dif_neg hi]
      rfl
    rw [hcomp]
    have hcoord : ContDiff ℝ (⊤ : ℕ∞)
        (fun y : MorseModel n => y (posIdx hk ⟨i.val - k, by
          have hkle : k ≤ i.val := le_of_not_gt hi
          have hi' : i.val < n := i.isLt
          omega⟩)) := by
      fun_prop
    exact hsqrt.mul hcoord

theorem modelAttachedRegion_contains_handleBelt {n k : ℕ} (hk : k ≤ n) (ε r δ : ℝ)
    (hδ0 : 0 < δ) (y : MorseModel n)
    (hy₁ : ‖negPart hk y‖ ^ 2 ≤ r ^ 2 + 2 * ε - δ)
    (hy₂ : ‖posPart hk y‖ ^ 2 ≤ r ^ 2) :
    y ∈ modelAttachedRegion hk ε r δ := by
  dsimp [modelAttachedRegion]
  rw [smoothCap_lower hδ0 hy₁]
  exact hy₂

theorem modelAttachedRegion_contains_lowerBelt {n k : ℕ} (hk : k ≤ n) (ε r δ : ℝ)
    (y : MorseModel n)
    (hy₁ : ‖negPart hk y‖ ^ 2 ≤ r ^ 2 + 2 * ε)
    (hy₂ : ‖posPart hk y‖ ^ 2 ≤ ‖negPart hk y‖ ^ 2 - 2 * ε) :
    y ∈ modelAttachedRegion hk ε r δ := by
  dsimp [modelAttachedRegion]
  have hs : smoothCap ε r δ (‖negPart hk y‖ ^ 2) ≥ ‖negPart hk y‖ ^ 2 - 2 * ε := by
    dsimp [smoothCap]
    have hτ : Real.smoothTransition
        ((‖negPart hk y‖ ^ 2 - (r ^ 2 + 2 * ε - δ)) / (2 * δ)) ≤ 1 :=
      Real.smoothTransition.le_one _
    have hcoef : ‖negPart hk y‖ ^ 2 - 2 * ε - r ^ 2 ≤ 0 := by nlinarith [hy₁]
    have hτsub : Real.smoothTransition
        ((‖negPart hk y‖ ^ 2 - (r ^ 2 + 2 * ε - δ)) / (2 * δ)) - 1 ≤ 0 := by
      linarith [hτ]
    have hmul : 0 ≤ (‖negPart hk y‖ ^ 2 - 2 * ε - r ^ 2) *
        (Real.smoothTransition ((‖negPart hk y‖ ^ 2 - (r ^ 2 + 2 * ε - δ)) / (2 * δ)) - 1) :=
      mul_nonneg_of_nonpos_of_nonpos hcoef hτsub
    nlinarith [hmul]
  nlinarith [hy₂, hs]

theorem modelAttachedRegion_upperBelt_eq_lower {n k : ℕ} (hk : k ≤ n) (ε r δ : ℝ)
    (hδ0 : 0 < δ) (y : MorseModel n)
    (hy : r ^ 2 + 2 * ε + δ ≤ ‖negPart hk y‖ ^ 2) :
    y ∈ modelAttachedRegion hk ε r δ ↔ ‖posPart hk y‖ ^ 2 ≤ ‖negPart hk y‖ ^ 2 - 2 * ε := by
  dsimp [modelAttachedRegion]
  rw [smoothCap_upper hδ0 hy]

theorem modelHandleMap_mem_upper {n k : ℕ} (hk : k ≤ n) (c ε r : ℝ) (hε : 0 ≤ ε)
    (p : StandardHandle k (n - k)) :
    modelHandleMap hk ε r p ∈ sublevel (morseNormalForm hk c) (c + r ^ 2 / 2) := by
  change morseNormalForm hk c (modelHandleMap hk ε r p) ≤ c + r ^ 2 / 2
  exact modelHandleMap_f_le hk c ε r hε p

theorem modelHandleMap_mem_lower_iff {n k : ℕ} (hk : k ≤ n) (c ε r : ℝ) (hε : 0 < ε)
    (p : StandardHandle k (n - k)) :
    modelHandleMap hk ε r p ∈ sublevel (morseNormalForm hk c) (c - ε) ↔
      ‖(p.1 : EuclideanSpace ℝ (Fin k))‖ = 1 := by
  change morseNormalForm hk c (modelHandleMap hk ε r p) ≤ c - ε ↔
    ‖(p.1 : EuclideanSpace ℝ (Fin k))‖ = 1
  constructor
  · intro hle
    have heq : morseNormalForm hk c (modelHandleMap hk ε r p) = c - ε :=
      le_antisymm hle (modelHandleMap_f_ge hk c ε r (le_of_lt hε) p)
    exact (modelHandleMap_f_eq_lower_iff hk c ε r hε p).1 heq
  · intro hx
    have heq : morseNormalForm hk c (modelHandleMap hk ε r p) = c - ε :=
      (modelHandleMap_f_eq_lower_iff hk c ε r hε p).2 hx
    exact le_of_eq heq

theorem morseNormalForm_split_ge {n k : ℕ} (hk : k ≤ n) (c ε : ℝ) (y : MorseModel n) :
    c - ε ≤ morseNormalForm hk c y ↔
      ‖negPart hk y‖ ^ 2 ≤ ‖posPart hk y‖ ^ 2 + 2 * ε := by
  rw [morseNormalForm_split]
  constructor <;> intro h <;> nlinarith

theorem modelHandle_eq_inter {n k : ℕ} (hk : k ≤ n) (c ε r : ℝ) (hr : 0 ≤ r) :
    modelHandle hk ε r =
      {y : MorseModel n | ‖posPart hk y‖ ≤ r} ∩
        {y : MorseModel n | c - ε ≤ morseNormalForm hk c y} := by
  ext y
  constructor
  · intro hy
    constructor
    · have hy1 := hy.1
      have hsq := (sq_le_sq).1 hy1
      simpa [abs_of_nonneg (norm_nonneg (posPart hk y)), abs_of_nonneg hr] using hsq
    · change c - ε ≤ morseNormalForm hk c y
      rw [morseNormalForm_split_ge]
      exact hy.2
  · intro hy
    constructor
    · exact (sq_le_sq).2 (by
        simpa [abs_of_nonneg (norm_nonneg (posPart hk y)), abs_of_nonneg hr] using hy.1)
    · have hy2 : c - ε ≤ morseNormalForm hk c y := by
        change c - ε ≤ morseNormalForm hk c y
        exact hy.2
      rw [morseNormalForm_split_ge] at hy2
      exact hy2

theorem modelHandleMap_range {n k : ℕ} (hk : k ≤ n) (ε r : ℝ) (hε : 0 < ε) (hr : 0 < r) :
    Set.range (modelHandleMap hk ε r) = modelHandle hk ε r := by
  ext y
  constructor
  · intro hy
    rcases hy with ⟨p, hp⟩
    rw [← hp]
    exact modelHandleMap_mem hk ε r (le_of_lt hε) p
  · intro hy
    let w : EuclideanSpace ℝ (Fin (n - k)) := (r⁻¹) • (posPart hk y)
    let s : ℝ := Real.sqrt (2 * ε + r ^ 2 * ‖w‖ ^ 2)
    let u : EuclideanSpace ℝ (Fin k) := s⁻¹ • (negPart hk y)
    have hwle : ‖w‖ ≤ 1 := by
      dsimp [w]
      rw [norm_smul, Real.norm_eq_abs]
      have hpos : 0 ≤ r⁻¹ := inv_nonneg.mpr (le_of_lt hr)
      rw [abs_of_nonneg hpos]
      have hle : ‖posPart hk y‖ ≤ r := by
        have hsq := (sq_le_sq).1 hy.1
        have hnr : 0 ≤ r := le_of_lt hr
        simpa [abs_of_nonneg (norm_nonneg (posPart hk y)), abs_of_nonneg hnr] using hsq
      have hmul : r⁻¹ * ‖posPart hk y‖ ≤ r⁻¹ * r :=
        mul_le_mul_of_nonneg_left hle hpos
      have hc : r⁻¹ * r = 1 := by
        exact inv_mul_cancel₀ (ne_of_gt hr)
      nlinarith
    have hule : ‖u‖ ≤ 1 := by
      dsimp [u, s]
      have hs0 : 0 < Real.sqrt (2 * ε + r ^ 2 * ‖w‖ ^ 2) := by
        positivity
      rw [norm_smul, Real.norm_eq_abs]
      have hpos : 0 ≤ (Real.sqrt (2 * ε + r ^ 2 * ‖w‖ ^ 2))⁻¹ :=
        inv_nonneg.mpr (le_of_lt hs0)
      rw [abs_of_nonneg hpos]
      have hw2 : r ^ 2 * ‖w‖ ^ 2 = ‖posPart hk y‖ ^ 2 := by
        have hrw : r • w = posPart hk y := by
          dsimp [w]
          rw [smul_smul]
          have hrr : r * r⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt hr)
          rw [hrr]
          simp
        have hnorm : ‖r • w‖ ^ 2 = ‖posPart hk y‖ ^ 2 := by rw [hrw]
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (le_of_lt hr)] at hnorm
        simpa [mul_pow] using hnorm
      have hneg2 : ‖negPart hk y‖ ^ 2 ≤ 2 * ε + ‖posPart hk y‖ ^ 2 := by
        nlinarith [hy.2]
      have hsq2 : ‖negPart hk y‖ ^ 2 ≤ (Real.sqrt (2 * ε + r ^ 2 * ‖w‖ ^ 2)) ^ 2 := by
        rw [Real.sq_sqrt (by positivity : 0 ≤ 2 * ε + r ^ 2 * ‖w‖ ^ 2)]
        nlinarith [hw2, hneg2]
      have hsq3 : ‖negPart hk y‖ ≤ Real.sqrt (2 * ε + r ^ 2 * ‖w‖ ^ 2) := by
        simpa [abs_of_nonneg (norm_nonneg (negPart hk y)),
          abs_of_nonneg (Real.sqrt_nonneg (2 * ε + r ^ 2 * ‖w‖ ^ 2))] using (sq_le_sq).1 hsq2
      have hs : (Real.sqrt (2 * ε + r ^ 2 * ‖w‖ ^ 2))⁻¹ * ‖negPart hk y‖ ≤ 1 := by
        rw [mul_comm]
        rw [← div_eq_mul_inv]
        exact (div_le_one hs0).2 (by simpa using hsq3)
      exact hs
    refine ⟨((⟨u, hule⟩ : ClosedCell k), (⟨w, hwle⟩ : ClosedCell (n - k))), ?_⟩
    dsimp [modelHandleMap]
    rw [← recombine_decompose hk y]
    congr 1
    · dsimp [u, s]
      rw [smul_smul]
      have hsc : Real.sqrt (2 * ε + r ^ 2 * ‖w‖ ^ 2) ≠ 0 := by
        positivity
      field_simp [hsc]
      simp
    · dsimp [w]
      rw [smul_smul]
      have hrr : r * r⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt hr)
      rw [hrr]
      simp

theorem lowerUnion_modelHandle {m k : ℕ} (hk : k ≤ m + 1) (c ε r : ℝ) (hr : 0 ≤ r) :
    (sublevel (morseNormalForm hk c) (c - ε) : Set (MorseModel (m + 1))) ∪ modelHandle hk ε r =
      (sublevel (morseNormalForm hk c) (c - ε) : Set (MorseModel (m + 1))) ∪
        {y : MorseModel (m + 1) | ‖posPart hk y‖ ≤ r} := by
  rw [modelHandle_eq_inter hk c ε r hr]
  ext y
  constructor <;> intro hy
  · rcases hy with hy | hy
    · exact Or.inl hy
    · exact Or.inr hy.1
  · rcases hy with hy | hy
    · exact Or.inl hy
    · by_cases hl : y ∈ sublevel (morseNormalForm hk c) (c - ε)
      · exact Or.inl hl
      · right
        constructor
        · exact hy
        · change c - ε ≤ morseNormalForm hk c y
          rw [morseNormalForm_split_ge]
          have hnot : c - ε < morseNormalForm hk c y := lt_of_not_ge hl
          have hineq : ‖negPart hk y‖ ^ 2 < ‖posPart hk y‖ ^ 2 + 2 * ε := by
            rw [morseNormalForm_split] at hnot
            nlinarith
          exact le_of_lt hineq

theorem modelAttachedStretch_equiv {n k : ℕ} (hk : k ≤ n) (c ε r δ : ℝ)
    (hδ0 : 0 < δ) (hδr : δ < r ^ 2) (hr : r ≠ 0) :
    (∀ y : MorseModel n,
        morseNormalForm hk c y ≤ c + r ^ 2 / 2 →
          modelAttachedStretch hk ε r δ y ∈ modelAttachedRegion hk ε r δ) ∧
    (∀ y : MorseModel n,
        y ∈ modelAttachedRegion hk ε r δ →
          morseNormalForm hk c (modelAttachedUnstretch hk ε r δ y) ≤ c + r ^ 2 / 2) ∧
    (∀ y : MorseModel n,
        morseNormalForm hk c y ≤ c + r ^ 2 / 2 →
          modelAttachedUnstretch hk ε r δ (modelAttachedStretch hk ε r δ y) = y) ∧
    (∀ y : MorseModel n,
        y ∈ modelAttachedRegion hk ε r δ →
          modelAttachedStretch hk ε r δ (modelAttachedUnstretch hk ε r δ y) = y) ∧
    ContDiff ℝ (⊤ : ℕ∞) (modelAttachedStretch hk ε r δ) ∧
    ContDiff ℝ (⊤ : ℕ∞) (modelAttachedUnstretch hk ε r δ) := by
  constructor
  · intro y hy
    have hle : ‖posPart hk y‖ ^ 2 ≤ ‖negPart hk y‖ ^ 2 + r ^ 2 := by
      have hf : morseNormalForm hk c y = c + (1 / 2) * (‖posPart hk y‖ ^ 2 - ‖negPart hk y‖ ^ 2) := by
        exact morseNormalForm_split hk c y
      nlinarith [hy, hf]
    exact modelAttachedStretch_mem hk ε r δ hδ0 hδr hr y hle
  constructor
  · intro y hy
    have hnorm : ‖posPart hk (modelAttachedUnstretch hk ε r δ y)‖ ^ 2 ≤ ‖negPart hk y‖ ^ 2 + r ^ 2 :=
      modelAttachedUnstretch_mem hk ε r δ hδ0 hδr y hy
    have hf : morseNormalForm hk c (modelAttachedUnstretch hk ε r δ y) =
        c + (1 / 2) * (‖posPart hk (modelAttachedUnstretch hk ε r δ y)‖ ^ 2 -
          ‖negPart hk (modelAttachedUnstretch hk ε r δ y)‖ ^ 2) :=
      morseNormalForm_split hk c (modelAttachedUnstretch hk ε r δ y)
    have hneg : ‖negPart hk (modelAttachedUnstretch hk ε r δ y)‖ ^ 2 = ‖negPart hk y‖ ^ 2 :=
      modelAttachedUnstretch_negPart_norm_sq hk ε r δ y
    rw [hf, hneg]
    nlinarith [hnorm]
  constructor
  · intro y hy
    exact modelAttachedUnstretch_stretch hk ε r δ hδ0 hδr hr y
  constructor
  · intro y hy
    exact modelAttachedStretch_unstretch hk ε r δ hδ0 hδr hr y
  constructor
  · exact contDiff_modelAttachedStretch hk ε r δ hδ0 hδr hr
  · exact contDiff_modelAttachedUnstretch hk ε r δ hδ0 hδr hr

theorem modelAttachedFunction_stretch_boundary {n k : ℕ} (hk : k ≤ n) (c ε r δ : ℝ)
    (hδ0 : 0 < δ) (hδr : δ < r ^ 2) (hr : r ≠ 0) (y : MorseModel n)
    (hy : morseNormalForm hk c y = c + r ^ 2 / 2) :
    modelAttachedFunction hk c ε r δ (modelAttachedStretch hk ε r δ y) = c := by
  have hle : ‖posPart hk y‖ ^ 2 ≤ ‖negPart hk y‖ ^ 2 + r ^ 2 := by
    have hf : morseNormalForm hk c y = c + (1 / 2) * (‖posPart hk y‖ ^ 2 - ‖negPart hk y‖ ^ 2) := by
      exact morseNormalForm_split hk c y
    nlinarith [hy, hf]
  have hmain : (smoothCap ε r δ (‖negPart hk y‖ ^ 2) / (‖negPart hk y‖ ^ 2 + r ^ 2)) *
        ‖posPart hk y‖ ^ 2 = smoothCap ε r δ (‖negPart hk y‖ ^ 2) := by
    have hpos : 0 < ‖negPart hk y‖ ^ 2 + r ^ 2 := by
      have hr2 : 0 < r ^ 2 := sq_pos_of_ne_zero hr
      nlinarith [sq_nonneg (‖negPart hk y‖ : ℝ)]
    have hratio : (‖posPart hk y‖ ^ 2) / (‖negPart hk y‖ ^ 2 + r ^ 2) = 1 := by
      have hf : morseNormalForm hk c y = c + (1 / 2) * (‖posPart hk y‖ ^ 2 - ‖negPart hk y‖ ^ 2) := by
        exact morseNormalForm_split hk c y
      have hmain' : ‖posPart hk y‖ ^ 2 = ‖negPart hk y‖ ^ 2 + r ^ 2 := by
        nlinarith [hy, hf]
      field_simp [ne_of_gt hpos]
      nlinarith [hmain']
    have hmain'' : ‖posPart hk y‖ ^ 2 = ‖negPart hk y‖ ^ 2 + r ^ 2 := by
      have hf : morseNormalForm hk c y = c + (1 / 2) * (‖posPart hk y‖ ^ 2 - ‖negPart hk y‖ ^ 2) := by
        exact morseNormalForm_split hk c y
      nlinarith [hy, hf]
    calc
      (smoothCap ε r δ (‖negPart hk y‖ ^ 2) / (‖negPart hk y‖ ^ 2 + r ^ 2)) *
          ‖posPart hk y‖ ^ 2
          = (smoothCap ε r δ (‖negPart hk y‖ ^ 2) / (‖negPart hk y‖ ^ 2 + r ^ 2)) *
              (‖negPart hk y‖ ^ 2 + r ^ 2) := by rw [hmain'']
      _ = smoothCap ε r δ (‖negPart hk y‖ ^ 2) := by
        field_simp [ne_of_gt hpos]
  have hposSq : ‖posPart hk (modelAttachedStretch hk ε r δ y)‖ ^ 2 =
      smoothCap ε r δ (‖negPart hk (modelAttachedStretch hk ε r δ y)‖ ^ 2) := by
    rw [modelAttachedStretch_posPart_norm_sq hk ε r δ hδ0 hδr y]
    rw [modelAttachedStretch_negPart_norm_sq hk ε r δ y]
    exact hmain
  have hnegSq : ‖negPart hk (modelAttachedStretch hk ε r δ y)‖ ^ 2 =
      ‖negPart hk y‖ ^ 2 := modelAttachedStretch_negPart_norm_sq hk ε r δ y
  dsimp [modelAttachedFunction]
  rw [hposSq]
  rw [hnegSq]
  ring

theorem modelAttachedFunction_unstretch_boundary {n k : ℕ} (hk : k ≤ n) (c ε r δ : ℝ)
    (hδ0 : 0 < δ) (hδr : δ < r ^ 2) (y : MorseModel n)
    (hy : y ∈ modelAttachedRegion hk ε r δ)
    (hb : modelAttachedFunction hk c ε r δ y = c) :
    morseNormalForm hk c (modelAttachedUnstretch hk ε r δ y) = c + r ^ 2 / 2 := by
  have hmem : ‖posPart hk (modelAttachedUnstretch hk ε r δ y)‖ ^ 2 ≤
      ‖negPart hk y‖ ^ 2 + r ^ 2 := modelAttachedUnstretch_mem hk ε r δ hδ0 hδr y hy
  have hposSq : ‖posPart hk (modelAttachedUnstretch hk ε r δ y)‖ ^ 2 =
      ((‖negPart hk y‖ ^ 2 + r ^ 2) / smoothCap ε r δ (‖negPart hk y‖ ^ 2)) *
        ‖posPart hk y‖ ^ 2 := modelAttachedUnstretch_posPart_norm_sq hk ε r δ hδ0 hδr y
  have hnegSq : ‖negPart hk (modelAttachedUnstretch hk ε r δ y)‖ ^ 2 =
      ‖negPart hk y‖ ^ 2 := modelAttachedUnstretch_negPart_norm_sq hk ε r δ y
  have hcap : smoothCap ε r δ (‖negPart hk y‖ ^ 2) > 0 :=
    smoothCap_pos (ε := ε) (r := r) (δ := δ) (t := ‖negPart hk y‖ ^ 2) hδ0 hδr
  have hmain : ((‖negPart hk y‖ ^ 2 + r ^ 2) / smoothCap ε r δ (‖negPart hk y‖ ^ 2)) *
        ‖posPart hk y‖ ^ 2 = ‖negPart hk y‖ ^ 2 + r ^ 2 := by
    have hf : modelAttachedFunction hk c ε r δ y = c + (1 / 2) *
        (‖posPart hk y‖ ^ 2 - smoothCap ε r δ (‖negPart hk y‖ ^ 2)) := rfl
    have hle' : ‖posPart hk y‖ ^ 2 ≤ smoothCap ε r δ (‖negPart hk y‖ ^ 2) := by
      dsimp [modelAttachedRegion] at hy
      exact hy
    have hmain'' : ‖posPart hk y‖ ^ 2 = smoothCap ε r δ (‖negPart hk y‖ ^ 2) := by
      nlinarith [hb, hf, hle']
    calc
      ((‖negPart hk y‖ ^ 2 + r ^ 2) / smoothCap ε r δ (‖negPart hk y‖ ^ 2)) *
          ‖posPart hk y‖ ^ 2
          = ((‖negPart hk y‖ ^ 2 + r ^ 2) / smoothCap ε r δ (‖negPart hk y‖ ^ 2)) *
              smoothCap ε r δ (‖negPart hk y‖ ^ 2) := by rw [hmain'']
      _ = ‖negPart hk y‖ ^ 2 + r ^ 2 := by
        field_simp [ne_of_gt hcap]
  have hf : morseNormalForm hk c (modelAttachedUnstretch hk ε r δ y) =
      c + (1 / 2) * (‖posPart hk (modelAttachedUnstretch hk ε r δ y)‖ ^ 2 -
        ‖negPart hk (modelAttachedUnstretch hk ε r δ y)‖ ^ 2) :=
    morseNormalForm_split hk c (modelAttachedUnstretch hk ε r δ y)
  rw [hf, hposSq, hnegSq, hmain]
  ring

theorem modelAttachedFunction_stretch_strict {n k : ℕ} (hk : k ≤ n) (c ε r δ : ℝ)
    (hδ0 : 0 < δ) (hδr : δ < r ^ 2) (hr : r ≠ 0) (y : MorseModel n)
    (hy : morseNormalForm hk c y < c + r ^ 2 / 2) :
    modelAttachedFunction hk c ε r δ (modelAttachedStretch hk ε r δ y) < c := by
  have hle : ‖posPart hk y‖ ^ 2 ≤ ‖negPart hk y‖ ^ 2 + r ^ 2 := by
    have hf : morseNormalForm hk c y = c + (1 / 2) * (‖posPart hk y‖ ^ 2 - ‖negPart hk y‖ ^ 2) := by
      exact morseNormalForm_split hk c y
    nlinarith [hy, hf]
  have hmain : (smoothCap ε r δ (‖negPart hk y‖ ^ 2) / (‖negPart hk y‖ ^ 2 + r ^ 2)) *
        ‖posPart hk y‖ ^ 2 < smoothCap ε r δ (‖negPart hk y‖ ^ 2) := by
    have hpos : 0 < ‖negPart hk y‖ ^ 2 + r ^ 2 := by
      have hr2 : 0 < r ^ 2 := sq_pos_of_ne_zero hr
      nlinarith [sq_nonneg (‖negPart hk y‖ : ℝ)]
    have hcap : 0 < smoothCap ε r δ (‖negPart hk y‖ ^ 2) :=
      smoothCap_pos (ε := ε) (r := r) (δ := δ) (t := ‖negPart hk y‖ ^ 2) hδ0 hδr
    have hratio : (‖posPart hk y‖ ^ 2) / (‖negPart hk y‖ ^ 2 + r ^ 2) < 1 := by
      have hf : morseNormalForm hk c y = c + (1 / 2) * (‖posPart hk y‖ ^ 2 - ‖negPart hk y‖ ^ 2) := by
        exact morseNormalForm_split hk c y
      have hmain' : ‖posPart hk y‖ ^ 2 < ‖negPart hk y‖ ^ 2 + r ^ 2 := by
        nlinarith [hy, hf]
      rw [div_lt_iff₀ hpos]
      nlinarith [hmain']
    have hmul : smoothCap ε r δ (‖negPart hk y‖ ^ 2) * (‖posPart hk y‖ ^ 2 / (‖negPart hk y‖ ^ 2 + r ^ 2)) <
        smoothCap ε r δ (‖negPart hk y‖ ^ 2) := by
      simpa using (mul_lt_mul_of_pos_left hratio hcap)
    calc
      (smoothCap ε r δ (‖negPart hk y‖ ^ 2) / (‖negPart hk y‖ ^ 2 + r ^ 2)) *
          ‖posPart hk y‖ ^ 2
          = smoothCap ε r δ (‖negPart hk y‖ ^ 2) *
              (‖posPart hk y‖ ^ 2 / (‖negPart hk y‖ ^ 2 + r ^ 2)) := by
            field_simp [ne_of_gt hpos]
      _ < smoothCap ε r δ (‖negPart hk y‖ ^ 2) := hmul
  have hposSq : ‖posPart hk (modelAttachedStretch hk ε r δ y)‖ ^ 2 <
      smoothCap ε r δ (‖negPart hk (modelAttachedStretch hk ε r δ y)‖ ^ 2) := by
    rw [modelAttachedStretch_posPart_norm_sq hk ε r δ hδ0 hδr y]
    rw [modelAttachedStretch_negPart_norm_sq hk ε r δ y]
    exact hmain
  have hnegSq : ‖negPart hk (modelAttachedStretch hk ε r δ y)‖ ^ 2 =
      ‖negPart hk y‖ ^ 2 := modelAttachedStretch_negPart_norm_sq hk ε r δ y
  dsimp [modelAttachedFunction]
  rw [hnegSq]
  have hsub : ‖posPart hk (modelAttachedStretch hk ε r δ y)‖ ^ 2 -
      smoothCap ε r δ (‖negPart hk y‖ ^ 2) < 0 := by
    have : ‖posPart hk (modelAttachedStretch hk ε r δ y)‖ ^ 2 <
        smoothCap ε r δ (‖negPart hk y‖ ^ 2) := by
      simpa [hnegSq] using hposSq
    nlinarith
  nlinarith [hsub]

theorem modelAttachedFunction_unstretch_strict {n k : ℕ} (hk : k ≤ n) (c ε r δ : ℝ)
    (hδ0 : 0 < δ) (hδr : δ < r ^ 2) (y : MorseModel n)
    (hy : y ∈ modelAttachedRegion hk ε r δ)
    (hb : modelAttachedFunction hk c ε r δ y < c) :
    morseNormalForm hk c (modelAttachedUnstretch hk ε r δ y) < c + r ^ 2 / 2 := by
  have hmem : ‖posPart hk (modelAttachedUnstretch hk ε r δ y)‖ ^ 2 ≤
      ‖negPart hk y‖ ^ 2 + r ^ 2 := modelAttachedUnstretch_mem hk ε r δ hδ0 hδr y hy
  have hposSq : ‖posPart hk (modelAttachedUnstretch hk ε r δ y)‖ ^ 2 =
      ((‖negPart hk y‖ ^ 2 + r ^ 2) / smoothCap ε r δ (‖negPart hk y‖ ^ 2)) *
        ‖posPart hk y‖ ^ 2 := modelAttachedUnstretch_posPart_norm_sq hk ε r δ hδ0 hδr y
  have hnegSq : ‖negPart hk (modelAttachedUnstretch hk ε r δ y)‖ ^ 2 =
      ‖negPart hk y‖ ^ 2 := modelAttachedUnstretch_negPart_norm_sq hk ε r δ y
  have hcap : smoothCap ε r δ (‖negPart hk y‖ ^ 2) > 0 :=
    smoothCap_pos (ε := ε) (r := r) (δ := δ) (t := ‖negPart hk y‖ ^ 2) hδ0 hδr
  have hmain : ((‖negPart hk y‖ ^ 2 + r ^ 2) / smoothCap ε r δ (‖negPart hk y‖ ^ 2)) *
        ‖posPart hk y‖ ^ 2 < ‖negPart hk y‖ ^ 2 + r ^ 2 := by
    have hf : modelAttachedFunction hk c ε r δ y = c + (1 / 2) *
        (‖posPart hk y‖ ^ 2 - smoothCap ε r δ (‖negPart hk y‖ ^ 2)) := rfl
    have hle' : ‖posPart hk y‖ ^ 2 < smoothCap ε r δ (‖negPart hk y‖ ^ 2) := by
      nlinarith [hb, hf]
    have hratio : ‖posPart hk y‖ ^ 2 / smoothCap ε r δ (‖negPart hk y‖ ^ 2) < 1 := by
      rw [div_lt_iff₀ hcap]
      nlinarith [hle']
    have hden : 0 < ‖negPart hk y‖ ^ 2 + r ^ 2 := by
      nlinarith [sq_nonneg (‖negPart hk y‖ : ℝ)]
    have hmul : (‖posPart hk y‖ ^ 2 / smoothCap ε r δ (‖negPart hk y‖ ^ 2)) *
        (‖negPart hk y‖ ^ 2 + r ^ 2) < 1 * (‖negPart hk y‖ ^ 2 + r ^ 2) := by
      exact mul_lt_mul_of_pos_right hratio hden
    calc
      ((‖negPart hk y‖ ^ 2 + r ^ 2) / smoothCap ε r δ (‖negPart hk y‖ ^ 2)) *
          ‖posPart hk y‖ ^ 2
          = (‖posPart hk y‖ ^ 2 / smoothCap ε r δ (‖negPart hk y‖ ^ 2)) *
              (‖negPart hk y‖ ^ 2 + r ^ 2) := by
            field_simp [ne_of_gt hcap]
      _ < ‖negPart hk y‖ ^ 2 + r ^ 2 := by
        simpa using hmul
  have hf : morseNormalForm hk c (modelAttachedUnstretch hk ε r δ y) =
      c + (1 / 2) * (‖posPart hk (modelAttachedUnstretch hk ε r δ y)‖ ^ 2 -
        ‖negPart hk (modelAttachedUnstretch hk ε r δ y)‖ ^ 2) :=
    morseNormalForm_split hk c (modelAttachedUnstretch hk ε r δ y)
  rw [hf, hposSq, hnegSq]
  nlinarith [hmain]

noncomputable def coordClm {n : ℕ} (i : Fin n) : MorseModel n →L[ℝ] ℝ :=
  { toFun := fun y => y i
    map_add' := by intro x y; rfl
    map_smul' := by intro a x; rfl
    cont := continuous_apply i }

theorem coordClm_apply {n : ℕ} (i : Fin n) (y : MorseModel n) :
    coordClm i y = y i := rfl

theorem fderiv_coord_sq {n : ℕ} (i : Fin n) (y w : MorseModel n) :
    fderiv ℝ (fun y : MorseModel n => (y i) ^ 2) y w =
      2 * (y i) * (w i) := by
  let L : MorseModel n →L[ℝ] ℝ := coordClm i
  have hL : fderiv ℝ (fun y : MorseModel n => L y) y = L := L.fderiv
  have hproj : fderiv ℝ (fun y : MorseModel n => y i) y = L := by
    change fderiv ℝ (fun y : MorseModel n => L y) y = L
    exact hL
  have hpow : fderiv ℝ (fun z : ℝ => z ^ 2) (y i) =
      (2 * y i) • (1 : ℝ →L[ℝ] ℝ) := by
    simpa using (fderiv_pow (𝕜 := ℝ) (f := fun z : ℝ => z) (n := 2) (x := y i)
      differentiableAt_id)
  have hfun : (fun y : MorseModel n => (y i) ^ 2) =
      (fun z : ℝ => z ^ 2) ∘ (fun y : MorseModel n => L y) := by
    funext y
    change (y i) ^ 2 = (fun z : ℝ => z ^ 2) (L y)
    rfl
  calc
    fderiv ℝ (fun y : MorseModel n => (y i) ^ 2) y w
        = fderiv ℝ ((fun z : ℝ => z ^ 2) ∘ (fun y : MorseModel n => L y)) y w := by
          rw [hfun]
    _ = (fderiv ℝ (fun z : ℝ => z ^ 2) (L y) ∘ₗ fderiv ℝ (fun y : MorseModel n => L y) y) w := by
          exact congrArg (fun φ : MorseModel n →L[ℝ] ℝ => φ w)
            (fderiv_comp (x := y) (hg := (differentiableAt_id (x := L y)).pow 2)
              (hf := L.differentiableAt))
    _ = 2 * (y i) * (w i) := by
          simp [coordClm, L, hproj]
          ring

theorem fderiv_posPart_normSq {n k : ℕ} (hk : k ≤ n) (y w : MorseModel n) :
    fderiv ℝ (fun y : MorseModel n => ‖posPart hk y‖ ^ 2) y w =
      2 * ∑ j : Fin (n - k), (posPart hk y j) * (posPart hk w j) := by
  have hfun : (fun y : MorseModel n => ‖posPart hk y‖ ^ 2) =
      ∑ j ∈ (Finset.univ : Finset (Fin (n - k))),
        (fun y : MorseModel n => (posPart hk y j) ^ 2) := by
    funext y
    rw [EuclideanSpace.real_norm_sq_eq (posPart hk y)]
    rw [Finset.sum_apply]
  rw [hfun]
  rw [fderiv_sum]
  · rw [ContinuousLinearMap.coe_sum']
    rw [Finset.sum_apply]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (by
      intro j hj
      have hcoord := fderiv_coord_sq (posIdx hk j) y w
      simpa [posPart, mul_assoc] using hcoord)
  · intro j hj
    exact ((coordClm (posIdx hk j)).differentiableAt.pow 2)

theorem fderiv_negPart_normSq {n k : ℕ} (hk : k ≤ n) (y w : MorseModel n) :
    fderiv ℝ (fun y : MorseModel n => ‖negPart hk y‖ ^ 2) y w =
      2 * ∑ i : Fin k, (negPart hk y i) * (negPart hk w i) := by
  have hfun : (fun y : MorseModel n => ‖negPart hk y‖ ^ 2) =
      ∑ i ∈ (Finset.univ : Finset (Fin k)),
        (fun y : MorseModel n => (negPart hk y i) ^ 2) := by
    funext y
    rw [EuclideanSpace.real_norm_sq_eq (negPart hk y)]
    rw [Finset.sum_apply]
  rw [hfun]
  rw [fderiv_sum]
  · rw [ContinuousLinearMap.coe_sum']
    rw [Finset.sum_apply]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (by
      intro i hi
      have hcoord : fderiv ℝ (fun y : MorseModel n => (y (negIdx hk i)) ^ 2) y w =
          2 * (y (negIdx hk i)) * (w (negIdx hk i)) := fderiv_coord_sq (negIdx hk i) y w
      simpa [negPart, mul_assoc] using hcoord)
  · intro i hi
    exact ((coordClm (negIdx hk i)).differentiableAt.pow 2)

theorem fderiv_posPart_normSq_self {n k : ℕ} (hk : k ≤ n) (y : MorseModel n) :
    fderiv ℝ (fun y : MorseModel n => ‖posPart hk y‖ ^ 2) y
      (recombine hk (0 : EuclideanSpace ℝ (Fin k)) (posPart hk y)) = 2 * ‖posPart hk y‖ ^ 2 := by
  rw [fderiv_posPart_normSq]
  have hw : posPart hk (recombine hk (0 : EuclideanSpace ℝ (Fin k)) (posPart hk y)) =
      posPart hk y :=
    posPart_recombine hk (0 : EuclideanSpace ℝ (Fin k)) (posPart hk y)
  rw [hw]
  have hsum : ∑ j : Fin (n - k), (posPart hk y j) * (posPart hk y j) =
      ‖posPart hk y‖ ^ 2 := by
    have hn := EuclideanSpace.real_norm_sq_eq (posPart hk y)
    rw [hn]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [hsum]

theorem fderiv_negPart_normSq_zero_direction {n k : ℕ} (hk : k ≤ n) (y : MorseModel n) :
    fderiv ℝ (fun y : MorseModel n => ‖negPart hk y‖ ^ 2) y
      (recombine hk (0 : EuclideanSpace ℝ (Fin k)) (posPart hk y)) = 0 := by
  rw [fderiv_negPart_normSq]
  have hw : negPart hk (recombine hk (0 : EuclideanSpace ℝ (Fin k)) (posPart hk y)) =
      (0 : EuclideanSpace ℝ (Fin k)) :=
    negPart_recombine hk (0 : EuclideanSpace ℝ (Fin k)) (posPart hk y)
  rw [hw]
  simp

theorem contDiff_negPart_normSq {n k : ℕ} (hk : k ≤ n) :
    ContDiff ℝ (⊤ : ℕ∞) (fun y : MorseModel n => ‖negPart hk y‖ ^ 2) := by
  rw [show (fun y : MorseModel n => ‖negPart hk y‖ ^ 2) =
      fun y : MorseModel n => ∑ i : Fin k, (negPart hk y i) ^ 2 by
    funext y
    exact EuclideanSpace.real_norm_sq_eq (negPart hk y)]
  fun_prop

theorem contDiff_posPart_normSq {n k : ℕ} (hk : k ≤ n) :
    ContDiff ℝ (⊤ : ℕ∞) (fun y : MorseModel n => ‖posPart hk y‖ ^ 2) := by
  rw [show (fun y : MorseModel n => ‖posPart hk y‖ ^ 2) =
      fun y : MorseModel n => ∑ j : Fin (n - k), (posPart hk y j) ^ 2 by
    funext y
    exact EuclideanSpace.real_norm_sq_eq (posPart hk y)]
  fun_prop

theorem fderiv_negPart_normSq_self {n k : ℕ} (hk : k ≤ n) (y : MorseModel n) :
    fderiv ℝ (fun y : MorseModel n => ‖negPart hk y‖ ^ 2) y
      (recombine hk (negPart hk y) (0 : EuclideanSpace ℝ (Fin (n - k)))) =
      2 * ‖negPart hk y‖ ^ 2 := by
  rw [fderiv_negPart_normSq]
  have hw : negPart hk (recombine hk (negPart hk y) (0 : EuclideanSpace ℝ (Fin (n - k)))) =
      negPart hk y :=
    negPart_recombine hk (negPart hk y) (0 : EuclideanSpace ℝ (Fin (n - k)))
  rw [hw]
  have hsum : ∑ i : Fin k, (negPart hk y i) * (negPart hk y i) =
      ‖negPart hk y‖ ^ 2 := by
    have hn := EuclideanSpace.real_norm_sq_eq (negPart hk y)
    rw [hn]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hsum]

theorem fderiv_posPart_normSq_zero_direction {n k : ℕ} (hk : k ≤ n) (y : MorseModel n) :
    fderiv ℝ (fun y : MorseModel n => ‖posPart hk y‖ ^ 2) y
      (recombine hk (negPart hk y) (0 : EuclideanSpace ℝ (Fin (n - k)))) = 0 := by
  rw [fderiv_posPart_normSq]
  have hw : posPart hk (recombine hk (negPart hk y) (0 : EuclideanSpace ℝ (Fin (n - k)))) =
      (0 : EuclideanSpace ℝ (Fin (n - k))) :=
    posPart_recombine hk (negPart hk y) (0 : EuclideanSpace ℝ (Fin (n - k)))
  rw [hw]
  simp

theorem fderiv_morseNormalForm_ne_zero_lower {n k : ℕ} (hk : k ≤ n) (c a : ℝ) (ha : 0 < a)
    (y : MorseModel n) (hy : morseNormalForm hk c y = c - a) :
    fderiv ℝ (morseNormalForm hk c) y ≠ 0 := by
  have hsplit : morseNormalForm hk c y = c + (1 / 2) * (‖posPart hk y‖ ^ 2 - ‖negPart hk y‖ ^ 2) :=
    morseNormalForm_split hk c y
  have hneg : 0 < ‖negPart hk y‖ ^ 2 := by
    have hmain : ‖negPart hk y‖ ^ 2 = ‖posPart hk y‖ ^ 2 + 2 * a := by
      nlinarith [hy, hsplit, ha]
    nlinarith [hmain, ha, sq_nonneg (‖posPart hk y‖ : ℝ)]
  have hdiff : DifferentiableAt ℝ (fun z : MorseModel n => ‖posPart hk z‖ ^ 2) y := by
    exact (contDiff_posPart_normSq hk).differentiable (by
      exact_mod_cast (ne_top_of_lt zero_lt_one).symm) |>.differentiableAt
  have hdiffNeg : DifferentiableAt ℝ (fun z : MorseModel n => ‖negPart hk z‖ ^ 2) y := by
    exact (contDiff_negPart_normSq hk).differentiable (by
      exact_mod_cast (ne_top_of_lt zero_lt_one).symm) |>.differentiableAt
  have hfderiv : fderiv ℝ (morseNormalForm hk c) y =
      (1 / 2 : ℝ) • (fderiv ℝ (fun z : MorseModel n => ‖posPart hk z‖ ^ 2) y -
        fderiv ℝ (fun z : MorseModel n => ‖negPart hk z‖ ^ 2) y) := by
    have hmain : (fun z : MorseModel n =>
        c + (1 / 2) * (‖posPart hk z‖ ^ 2 - ‖negPart hk z‖ ^ 2)) =
        morseNormalForm hk c := by
      funext z
      exact (morseNormalForm_split hk c z).symm
    rw [← hmain]
    rw [fderiv_const_add]
    have hsub : DifferentiableAt ℝ (fun z : MorseModel n =>
        ‖posPart hk z‖ ^ 2 - ‖negPart hk z‖ ^ 2) y := hdiff.sub hdiffNeg
    have hmul : fderiv ℝ (fun z : MorseModel n =>
        (1 / 2 : ℝ) * (‖posPart hk z‖ ^ 2 - ‖negPart hk z‖ ^ 2)) y =
        (1 / 2 : ℝ) • fderiv ℝ (fun z : MorseModel n =>
          ‖posPart hk z‖ ^ 2 - ‖negPart hk z‖ ^ 2) y :=
      fderiv_const_mul hsub (1 / 2 : ℝ)
    rw [hmul]
    congr 1
    exact fderiv_sub (f := fun z : MorseModel n => ‖posPart hk z‖ ^ 2)
      (g := fun z : MorseModel n => ‖negPart hk z‖ ^ 2)
      (hf := hdiff) (hg := hdiffNeg)
  intro hzero
  have hw : fderiv ℝ (morseNormalForm hk c) y
      (recombine hk (negPart hk y) (0 : EuclideanSpace ℝ (Fin (n - k)))) = 0 := by
    exact congrArg (fun L : MorseModel n →L[ℝ] ℝ =>
      L (recombine hk (negPart hk y) (0 : EuclideanSpace ℝ (Fin (n - k))))) hzero
  rw [hfderiv] at hw
  have hd : (fderiv ℝ (fun z : MorseModel n => ‖posPart hk z‖ ^ 2) y)
      (recombine hk (negPart hk y) (0 : EuclideanSpace ℝ (Fin (n - k)))) = 0 :=
    fderiv_posPart_normSq_zero_direction hk y
  have hdNeg : (fderiv ℝ (fun z : MorseModel n => ‖negPart hk z‖ ^ 2) y)
      (recombine hk (negPart hk y) (0 : EuclideanSpace ℝ (Fin (n - k)))) =
      2 * ‖negPart hk y‖ ^ 2 :=
    fderiv_negPart_normSq_self hk y
  rw [ContinuousLinearMap.smul_apply] at hw
  rw [ContinuousLinearMap.sub_apply] at hw
  rw [hd, hdNeg] at hw
  have hw' : (1 / 2 : ℝ) * (0 - 2 * ‖negPart hk y‖ ^ 2) = 0 := by
    simpa using hw
  nlinarith

theorem fderiv_morseNormalForm_ne_zero {n k : ℕ} (hk : k ≤ n) (c a : ℝ) (ha : 0 < a)
    (y : MorseModel n) (hy : morseNormalForm hk c y = c + a) :
    fderiv ℝ (morseNormalForm hk c) y ≠ 0 := by
  have hsplit : morseNormalForm hk c y = c + (1 / 2) * (‖posPart hk y‖ ^ 2 - ‖negPart hk y‖ ^ 2) :=
    morseNormalForm_split hk c y
  have hpos : 0 < ‖posPart hk y‖ ^ 2 := by
    have hmain : ‖posPart hk y‖ ^ 2 = ‖negPart hk y‖ ^ 2 + 2 * a := by
      nlinarith [hy, hsplit, ha]
    nlinarith [hmain, ha, sq_nonneg (‖negPart hk y‖ : ℝ)]
  have hdiff : DifferentiableAt ℝ (fun z : MorseModel n => ‖posPart hk z‖ ^ 2) y := by
    exact (contDiff_posPart_normSq hk).differentiable (by
      exact_mod_cast (ne_top_of_lt zero_lt_one).symm) |>.differentiableAt
  have hdiffNeg : DifferentiableAt ℝ (fun z : MorseModel n => ‖negPart hk z‖ ^ 2) y := by
    exact (contDiff_negPart_normSq hk).differentiable (by
      exact_mod_cast (ne_top_of_lt zero_lt_one).symm) |>.differentiableAt
  have hfderiv : fderiv ℝ (morseNormalForm hk c) y =
      (1 / 2 : ℝ) • (fderiv ℝ (fun z : MorseModel n => ‖posPart hk z‖ ^ 2) y -
        fderiv ℝ (fun z : MorseModel n => ‖negPart hk z‖ ^ 2) y) := by
    have hmain : (fun z : MorseModel n =>
        c + (1 / 2) * (‖posPart hk z‖ ^ 2 - ‖negPart hk z‖ ^ 2)) =
        morseNormalForm hk c := by
      funext z
      exact (morseNormalForm_split hk c z).symm
    rw [← hmain]
    rw [fderiv_const_add]
    have hsub : DifferentiableAt ℝ (fun z : MorseModel n =>
        ‖posPart hk z‖ ^ 2 - ‖negPart hk z‖ ^ 2) y := hdiff.sub hdiffNeg
    have hmul : fderiv ℝ (fun z : MorseModel n =>
        (1 / 2 : ℝ) * (‖posPart hk z‖ ^ 2 - ‖negPart hk z‖ ^ 2)) y =
        (1 / 2 : ℝ) • fderiv ℝ (fun z : MorseModel n =>
          ‖posPart hk z‖ ^ 2 - ‖negPart hk z‖ ^ 2) y :=
      fderiv_const_mul hsub (1 / 2 : ℝ)
    rw [hmul]
    congr 1
    exact fderiv_sub (f := fun z : MorseModel n => ‖posPart hk z‖ ^ 2)
      (g := fun z : MorseModel n => ‖negPart hk z‖ ^ 2)
      (hf := hdiff) (hg := hdiffNeg)
  intro hzero
  have hw : fderiv ℝ (morseNormalForm hk c) y
      (recombine hk (0 : EuclideanSpace ℝ (Fin k)) (posPart hk y)) = 0 := by
    exact congrArg (fun L : MorseModel n →L[ℝ] ℝ =>
      L (recombine hk (0 : EuclideanSpace ℝ (Fin k)) (posPart hk y))) hzero
  rw [hfderiv] at hw
  have hd : (fderiv ℝ (fun z : MorseModel n => ‖posPart hk z‖ ^ 2) y)
      (recombine hk (0 : EuclideanSpace ℝ (Fin k)) (posPart hk y)) = 2 * ‖posPart hk y‖ ^ 2 :=
    fderiv_posPart_normSq_self hk y
  have hdNeg : (fderiv ℝ (fun z : MorseModel n => ‖negPart hk z‖ ^ 2) y)
      (recombine hk (0 : EuclideanSpace ℝ (Fin k)) (posPart hk y)) = 0 :=
    fderiv_negPart_normSq_zero_direction hk y
  rw [ContinuousLinearMap.smul_apply] at hw
  rw [ContinuousLinearMap.sub_apply] at hw
  rw [hd, hdNeg] at hw
  have hw' : (1 / 2 : ℝ) * (2 * ‖posPart hk y‖ ^ 2) = 0 := by
    simpa using hw
  nlinarith

theorem fderiv_cap_negPart_zero_direction {n k : ℕ} (hk : k ≤ n) (ε r δ : ℝ)
    (y : MorseModel n) :
    fderiv ℝ (fun y : MorseModel n => smoothCap ε r δ (‖negPart hk y‖ ^ 2)) y
      (recombine hk (0 : EuclideanSpace ℝ (Fin k)) (posPart hk y)) = 0 := by
  have hcapDiff : DifferentiableAt ℝ (smoothCap ε r δ) (‖negPart hk y‖ ^ 2) :=
    (smoothCap_contDiff ε r δ).differentiable (by
      exact_mod_cast (ne_top_of_lt zero_lt_one).symm) |>.differentiableAt
  have hinnerDiff : DifferentiableAt ℝ (fun y : MorseModel n => ‖negPart hk y‖ ^ 2) y :=
    (contDiff_negPart_normSq hk).differentiable (by
      exact_mod_cast (ne_top_of_lt zero_lt_one).symm) |>.differentiableAt
  have hcomp : fderiv ℝ (fun y : MorseModel n => smoothCap ε r δ (‖negPart hk y‖ ^ 2)) y =
      (fderiv ℝ (smoothCap ε r δ) (‖negPart hk y‖ ^ 2)).comp
        (fderiv ℝ (fun y : MorseModel n => ‖negPart hk y‖ ^ 2) y) :=
    fderiv_comp (x := y) (f := fun y : MorseModel n => ‖negPart hk y‖ ^ 2)
      (g := smoothCap ε r δ) (hg := hcapDiff) (hf := hinnerDiff)
  calc
    fderiv ℝ (fun y : MorseModel n => smoothCap ε r δ (‖negPart hk y‖ ^ 2)) y
        (recombine hk (0 : EuclideanSpace ℝ (Fin k)) (posPart hk y))
        = ((fderiv ℝ (smoothCap ε r δ) (‖negPart hk y‖ ^ 2)).comp
            (fderiv ℝ (fun y : MorseModel n => ‖negPart hk y‖ ^ 2) y))
            (recombine hk (0 : EuclideanSpace ℝ (Fin k)) (posPart hk y)) := by
          rw [hcomp]
    _ = 0 := by
          simp [fderiv_negPart_normSq_zero_direction hk y]

theorem fderiv_modelAttachedFunction_direction {n k : ℕ} (hk : k ≤ n) (c ε r δ : ℝ)
    (y : MorseModel n) :
    fderiv ℝ (modelAttachedFunction hk c ε r δ) y
      (recombine hk (0 : EuclideanSpace ℝ (Fin k)) (posPart hk y)) = ‖posPart hk y‖ ^ 2 := by
  have hdiffPos : DifferentiableAt ℝ (fun y : MorseModel n => ‖posPart hk y‖ ^ 2) y :=
    (contDiff_posPart_normSq hk).differentiable (by
      exact_mod_cast (ne_top_of_lt zero_lt_one).symm) |>.differentiableAt
  have hdiffCap : DifferentiableAt ℝ (fun y : MorseModel n =>
      smoothCap ε r δ (‖negPart hk y‖ ^ 2)) y :=
    ((smoothCap_contDiff ε r δ).comp (contDiff_negPart_normSq hk)).differentiable (by
      exact_mod_cast (ne_top_of_lt zero_lt_one).symm) |>.differentiableAt
  have hderiv : fderiv ℝ (modelAttachedFunction hk c ε r δ) y =
      (1 / 2 : ℝ) • (fderiv ℝ (fun y : MorseModel n => ‖posPart hk y‖ ^ 2) y -
        fderiv ℝ (fun y : MorseModel n => smoothCap ε r δ (‖negPart hk y‖ ^ 2)) y) := by
    unfold modelAttachedFunction
    rw [fderiv_const_add]
    rw [fderiv_const_mul]
    · exact congrArg (fun L : MorseModel n →L[ℝ] ℝ => (1 / 2 : ℝ) • L)
        (fderiv_sub (f := fun y : MorseModel n => ‖posPart hk y‖ ^ 2)
          (g := fun y : MorseModel n => smoothCap ε r δ (‖negPart hk y‖ ^ 2))
          (hf := hdiffPos) (hg := hdiffCap))
    · exact hdiffPos.sub hdiffCap
  calc
    fderiv ℝ (modelAttachedFunction hk c ε r δ) y
        (recombine hk (0 : EuclideanSpace ℝ (Fin k)) (posPart hk y))
        = ((1 / 2 : ℝ) • (fderiv ℝ (fun y : MorseModel n => ‖posPart hk y‖ ^ 2) y -
            fderiv ℝ (fun y : MorseModel n => smoothCap ε r δ (‖negPart hk y‖ ^ 2)) y))
            (recombine hk (0 : EuclideanSpace ℝ (Fin k)) (posPart hk y)) := by
          rw [hderiv]
    _ = ‖posPart hk y‖ ^ 2 := by
          simp [fderiv_posPart_normSq_self hk y, fderiv_cap_negPart_zero_direction hk ε r δ y]

theorem fderiv_modelAttachedFunction_ne_zero {n k : ℕ} (hk : k ≤ n) (c ε r δ : ℝ)
    (hδ0 : 0 < δ) (hδr : δ < r ^ 2) (y : MorseModel n)
    (hy : modelAttachedFunction hk c ε r δ y = c) :
    fderiv ℝ (modelAttachedFunction hk c ε r δ) y ≠ 0 := by
  have hpos : 0 < ‖posPart hk y‖ ^ 2 := by
    have hcap : 0 < smoothCap ε r δ (‖negPart hk y‖ ^ 2) :=
      smoothCap_pos (ε := ε) (r := r) (δ := δ) (t := ‖negPart hk y‖ ^ 2) hδ0 hδr
    have hmain : ‖posPart hk y‖ ^ 2 = smoothCap ε r δ (‖negPart hk y‖ ^ 2) := by
      have hf : modelAttachedFunction hk c ε r δ y = c + (1 / 2) *
          (‖posPart hk y‖ ^ 2 - smoothCap ε r δ (‖negPart hk y‖ ^ 2)) := rfl
      nlinarith [hy, hf]
    rw [hmain]
    exact hcap
  intro h
  have hw : fderiv ℝ (modelAttachedFunction hk c ε r δ) y
      (recombine hk (0 : EuclideanSpace ℝ (Fin k)) (posPart hk y)) = 0 := by
    exact congrArg (fun L : MorseModel n →L[ℝ] ℝ =>
      L (recombine hk (0 : EuclideanSpace ℝ (Fin k)) (posPart hk y))) h
  rw [fderiv_modelAttachedFunction_direction hk c ε r δ y] at hw
  nlinarith [hw, hpos]

abbrev ballUpperSublevel {n k : ℕ} (hk : k ≤ n) (c ε R : ℝ) : Type :=
  {y : MorseModel n // y ∈ sublevel (morseNormalForm hk c) (c + ε) ∧ morseNorm n y ≤ R}

abbrev ballLowerUnion {n k : ℕ} (hk : k ≤ n) (c ε R : ℝ) : Type :=
  {y : MorseModel n //
    (y ∈ sublevel (morseNormalForm hk c) (c - ε) ∧ morseNorm n y ≤ R) ∨
      y ∈ Set.range (fun x : ClosedCell k => cellMap (Real.sqrt (2 * ε)) (x : EuclideanSpace ℝ (Fin k)))}

theorem mem_ballLowerUnion_iff {n k : ℕ} (hk : k ≤ n) (c ε R : ℝ)
    (hR : Real.sqrt (2 * ε) ≤ R) (y : MorseModel n) :
    y ∈ lowerCellUnion hk c ε ∧ morseNorm n y ≤ R ↔
      (y ∈ sublevel (morseNormalForm hk c) (c - ε) ∧ morseNorm n y ≤ R) ∨
        y ∈ Set.range (fun x : ClosedCell k => cellMap (Real.sqrt (2 * ε)) (x : EuclideanSpace ℝ (Fin k))) := by
  constructor
  · rintro ⟨h | ⟨x, hx⟩, hb⟩
    · exact Or.inl ⟨h, hb⟩
    · exact Or.inr ⟨x, hx⟩
  · rintro (h | ⟨x, hx⟩)
    · exact ⟨Or.inl h.1, h.2⟩
    · rw [← hx]
      exact ⟨Or.inr ⟨x, rfl⟩, norm_cellMap_le hk ε R hR (x : EuclideanSpace ℝ (Fin k)) x.2⟩

theorem norm_le_of_mem_ballLowerUnion {n k : ℕ} (hk : k ≤ n) (c ε R : ℝ)
    (hR : Real.sqrt (2 * ε) ≤ R) {y : MorseModel n}
    (h : (y ∈ sublevel (morseNormalForm hk c) (c - ε) ∧ morseNorm n y ≤ R) ∨
      y ∈ Set.range (fun x : ClosedCell k => cellMap (Real.sqrt (2 * ε)) (x : EuclideanSpace ℝ (Fin k)))) :
    morseNorm n y ≤ R := by
  rcases h with h | ⟨x, hx⟩
  · exact h.2
  · rw [← hx]
    exact norm_cellMap_le hk ε R hR (x : EuclideanSpace ℝ (Fin k)) x.2

def ballCellAttachmentMap {n k : ℕ} (hk : k ≤ n) (c ε R : ℝ) (hε : 0 < ε)
    (y : ballUpperSublevel hk c ε R) : ballLowerUnion hk c ε R :=
  ⟨spineMap hk y.1, by
    rcases spineMap_mem_union hk c ε hε y.1 with h | ⟨x, hx⟩
    · exact Or.inl ⟨h, le_trans (norm_spineMap_le hk y.1) y.2.2⟩
    · exact Or.inr ⟨x, hx⟩⟩

def ballCellAttachmentInclusion {n k : ℕ} (hk : k ≤ n) (c ε R : ℝ) (hε : 0 ≤ ε)
    (hR : Real.sqrt (2 * ε) ≤ R) (z : ballLowerUnion hk c ε R) : ballUpperSublevel hk c ε R :=
  ⟨z.1, by
    constructor
    · exact cellAttachmentInclusion_mem hk c ε hε ⟨z.1, by
        rcases z.2 with h | ⟨x, hx⟩
        · exact Or.inl h.1
        · exact Or.inr ⟨x, hx⟩⟩
    · exact norm_le_of_mem_ballLowerUnion hk c ε R hR z.2⟩

def ballCellRetractionHomotopyFun {n k : ℕ} (hk : k ≤ n) (c ε R : ℝ) :
    Set.Icc (0 : ℝ) 1 × ballUpperSublevel hk c ε R → ballUpperSublevel hk c ε R :=
  fun p =>
    ⟨cellRetractionStep hk (p.1 : ℝ) p.2.1,
      ⟨cellRetractionStep_mem_upper hk c ε (t := p.1.1) (y := p.2.1) p.1.2.1 p.1.2.2 p.2.2.1,
        le_trans (norm_cellRetractionStep_le hk p.1.2.1 p.1.2.2 p.2.1) p.2.2.2⟩⟩

def ballCellInclusionStepFun {n k : ℕ} (hk : k ≤ n) (c ε R : ℝ) (hR : Real.sqrt (2 * ε) ≤ R) :
    Set.Icc (0 : ℝ) 1 × ballLowerUnion hk c ε R → ballLowerUnion hk c ε R :=
  fun p =>
    ⟨cellRetractionStep hk (p.1 : ℝ) p.2.1, by
      have hmem : cellRetractionStep hk (p.1 : ℝ) p.2.1 ∈ lowerCellUnion hk c ε :=
        cellInclusionStep_mem hk c ε p.1 ⟨p.2.1, by
          rcases p.2.2 with h | ⟨x, hx⟩
          · exact Or.inl h.1
          · exact Or.inr ⟨x, hx⟩⟩
      rcases hmem with h | ⟨x, hx⟩
      · exact Or.inl ⟨h, le_trans (norm_cellRetractionStep_le hk p.1.2.1 p.1.2.2 p.2.1)
          (norm_le_of_mem_ballLowerUnion hk c ε R hR p.2.2)⟩
      · exact Or.inr ⟨x, hx⟩⟩

theorem ballCellRetractionHomotopy_zero {n k : ℕ} (hk : k ≤ n) (c ε R : ℝ) (hε : 0 < ε)
    (hR : Real.sqrt (2 * ε) ≤ R) (y : ballUpperSublevel hk c ε R) :
    ballCellRetractionHomotopyFun hk c ε R (⟨0, by norm_num⟩, y) =
      ballCellAttachmentInclusion hk c ε R (le_of_lt hε) hR (ballCellAttachmentMap hk c ε R hε y) := by
  apply Subtype.ext
  dsimp [ballCellRetractionHomotopyFun, ballCellAttachmentInclusion, ballCellAttachmentMap]
  exact cellRetractionStep_spine hk y.1

theorem ballCellRetractionHomotopy_one {n k : ℕ} (hk : k ≤ n) (c ε R : ℝ)
    (y : ballUpperSublevel hk c ε R) :
    ballCellRetractionHomotopyFun hk c ε R (⟨1, by norm_num⟩, y) = y := by
  apply Subtype.ext
  dsimp [ballCellRetractionHomotopyFun]
  exact cellRetractionStep_decompose hk y.1

theorem ballCellInclusionStep_zero {n k : ℕ} (hk : k ≤ n) (c ε R : ℝ) (hε : 0 < ε)
    (hR : Real.sqrt (2 * ε) ≤ R) (z : ballLowerUnion hk c ε R) :
    ballCellInclusionStepFun hk c ε R hR (⟨0, by norm_num⟩, z) =
      ballCellAttachmentMap hk c ε R hε (ballCellAttachmentInclusion hk c ε R (le_of_lt hε) hR z) := by
  apply Subtype.ext
  dsimp [ballCellInclusionStepFun, ballCellAttachmentMap, ballCellAttachmentInclusion]
  exact cellRetractionStep_spine hk z.1

theorem ballCellInclusionStep_one {n k : ℕ} (hk : k ≤ n) (c ε R : ℝ) (hR : Real.sqrt (2 * ε) ≤ R)
    (z : ballLowerUnion hk c ε R) :
    ballCellInclusionStepFun hk c ε R hR (⟨1, by norm_num⟩, z) = z := by
  apply Subtype.ext
  dsimp [ballCellInclusionStepFun]
  exact cellRetractionStep_decompose hk z.1

theorem continuous_ballCellAttachmentMap {n k : ℕ} (hk : k ≤ n) (c ε R : ℝ) (hε : 0 < ε) :
    Continuous (ballCellAttachmentMap hk c ε R hε) := by
  have h : Continuous (fun y : ballUpperSublevel hk c ε R => spineMap hk y.1) :=
    (continuous_spineMap hk).comp continuous_subtype_val
  have hcomp : (fun y : ballUpperSublevel hk c ε R =>
      ((ballCellAttachmentMap hk c ε R hε y : ballLowerUnion hk c ε R) : MorseModel n)) =
      fun y => spineMap hk y.1 := by
    funext y
    rfl
  exact (Topology.IsInducing.subtypeVal.continuous_iff).2 (by simpa [hcomp] using h)

theorem continuous_ballCellAttachmentInclusion {n k : ℕ} (hk : k ≤ n) (c ε R : ℝ) (hε : 0 ≤ ε)
    (hR : Real.sqrt (2 * ε) ≤ R) : Continuous (ballCellAttachmentInclusion hk c ε R hε hR) := by
  have hcomp : (fun z : ballLowerUnion hk c ε R =>
      ((ballCellAttachmentInclusion hk c ε R hε hR z : ballUpperSublevel hk c ε R) : MorseModel n)) =
      fun z : ballLowerUnion hk c ε R => (z : MorseModel n) := by
    funext z
    rfl
  exact (Topology.IsInducing.subtypeVal.continuous_iff).2
    (by simpa [hcomp] using
      (continuous_subtype_val : Continuous (fun z : ballLowerUnion hk c ε R => (z : MorseModel n))))

theorem continuous_ballCellRetractionHomotopyFun {n k : ℕ} (hk : k ≤ n) (c ε R : ℝ) :
    Continuous (ballCellRetractionHomotopyFun hk c ε R) := by
  have hpair : Continuous (fun p : Set.Icc (0 : ℝ) 1 × ballUpperSublevel hk c ε R =>
      (p.1, p.2.1)) :=
    continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)
  have h : Continuous (fun p : Set.Icc (0 : ℝ) 1 × ballUpperSublevel hk c ε R =>
      cellRetractionStep hk (p.1 : ℝ) p.2.1) :=
    continuous_cellRetractionStep hk |>.comp hpair
  have hcomp : (fun p : Set.Icc (0 : ℝ) 1 × ballUpperSublevel hk c ε R =>
      ((ballCellRetractionHomotopyFun hk c ε R p : ballUpperSublevel hk c ε R) : MorseModel n)) =
      fun p => cellRetractionStep hk (p.1 : ℝ) p.2.1 := by
    funext p
    rfl
  exact (Topology.IsInducing.subtypeVal.continuous_iff).2 (by simpa [hcomp] using h)

theorem continuous_ballCellInclusionStepFun {n k : ℕ} (hk : k ≤ n) (c ε R : ℝ)
    (hR : Real.sqrt (2 * ε) ≤ R) : Continuous (ballCellInclusionStepFun hk c ε R hR) := by
  have hpair : Continuous (fun p : Set.Icc (0 : ℝ) 1 × ballLowerUnion hk c ε R =>
      (p.1, p.2.1)) :=
    continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)
  have h : Continuous (fun p : Set.Icc (0 : ℝ) 1 × ballLowerUnion hk c ε R =>
      cellRetractionStep hk (p.1 : ℝ) p.2.1) :=
    continuous_cellRetractionStep hk |>.comp hpair
  have hcomp : (fun p : Set.Icc (0 : ℝ) 1 × ballLowerUnion hk c ε R =>
      ((ballCellInclusionStepFun hk c ε R hR p : ballLowerUnion hk c ε R) : MorseModel n)) =
      fun p => cellRetractionStep hk (p.1 : ℝ) p.2.1 := by
    funext p
    rfl
  exact (Topology.IsInducing.subtypeVal.continuous_iff).2 (by simpa [hcomp] using h)

private noncomputable def ballCellAttachmentMapC {n k : ℕ} (hk : k ≤ n) (c ε R : ℝ) (hε : 0 < ε) :
    C(ballUpperSublevel hk c ε R, ballLowerUnion hk c ε R) :=
  ⟨ballCellAttachmentMap hk c ε R hε, continuous_ballCellAttachmentMap hk c ε R hε⟩

private noncomputable def ballCellAttachmentInclusionC {n k : ℕ} (hk : k ≤ n) (c ε R : ℝ) (hε : 0 ≤ ε)
    (hR : Real.sqrt (2 * ε) ≤ R) : C(ballLowerUnion hk c ε R, ballUpperSublevel hk c ε R) :=
  ⟨ballCellAttachmentInclusion hk c ε R hε hR, continuous_ballCellAttachmentInclusion hk c ε R hε hR⟩

noncomputable def ballCellRetractionHomotopy {n k : ℕ} (hk : k ≤ n) (c ε R : ℝ) (hε : 0 < ε)
    (hR : Real.sqrt (2 * ε) ≤ R) :
    ContinuousMap.Homotopy
      ((ballCellAttachmentInclusionC hk c ε R (le_of_lt hε) hR).comp
        (ballCellAttachmentMapC hk c ε R hε))
      (ContinuousMap.id (ballUpperSublevel hk c ε R)) where
  toFun := ContinuousMap.mk (ballCellRetractionHomotopyFun hk c ε R)
    (continuous_ballCellRetractionHomotopyFun hk c ε R)
  map_zero_left := by
    intro y
    exact ballCellRetractionHomotopy_zero hk c ε R hε hR y
  map_one_left := by
    intro y
    exact ballCellRetractionHomotopy_one hk c ε R y

noncomputable def ballCellInclusionHomotopy {n k : ℕ} (hk : k ≤ n) (c ε R : ℝ) (hε : 0 < ε)
    (hR : Real.sqrt (2 * ε) ≤ R) :
    ContinuousMap.Homotopy
      ((ballCellAttachmentMapC hk c ε R hε).comp
        (ballCellAttachmentInclusionC hk c ε R (le_of_lt hε) hR))
      (ContinuousMap.id (ballLowerUnion hk c ε R)) where
  toFun := ContinuousMap.mk (ballCellInclusionStepFun hk c ε R hR)
    (continuous_ballCellInclusionStepFun hk c ε R hR)
  map_zero_left := by
    intro z
    exact ballCellInclusionStep_zero hk c ε R hε hR z
  map_one_left := by
    intro z
    exact ballCellInclusionStep_one hk c ε R hR z

noncomputable def ballCellAttachmentHomotopyEquiv {n k : ℕ} (hk : k ≤ n) (c ε R : ℝ) (hε : 0 < ε)
    (hR : Real.sqrt (2 * ε) ≤ R) :
    ContinuousMap.HomotopyEquiv (ballUpperSublevel hk c ε R) (ballLowerUnion hk c ε R) where
  toFun := ballCellAttachmentMapC hk c ε R hε
  invFun := ballCellAttachmentInclusionC hk c ε R (le_of_lt hε) hR
  left_inv := ⟨ballCellRetractionHomotopy hk c ε R hε hR⟩
  right_inv := ⟨ballCellInclusionHomotopy hk c ε R hε hR⟩

def ballAttachMap {n k : ℕ} (hk : k ≤ n) (c ε R : ℝ) (hε : 0 ≤ ε) (hR : Real.sqrt (2 * ε) ≤ R)
    (x : CellBoundary k) : {y : MorseModel n // y ∈ sublevel (morseNormalForm hk c) (c - ε) ∧ morseNorm n y ≤ R} :=
  ⟨cellMap (Real.sqrt (2 * ε)) (x : EuclideanSpace ℝ (Fin k)), by
    constructor
    · change morseNormalForm hk c (cellMap (Real.sqrt (2 * ε)) (x : EuclideanSpace ℝ (Fin k))) ≤ c - ε
      have hf := morseNormalForm_cellMap hk c (Real.sqrt (2 * ε)) (x : EuclideanSpace ℝ (Fin k))
      rw [hf]
      have hnorm : ‖(x : EuclideanSpace ℝ (Fin k))‖ = 1 := x.2
      have hsq : (Real.sqrt (2 * ε)) ^ 2 = 2 * ε := by
        rw [Real.sq_sqrt (by positivity : 0 ≤ 2 * ε)]
      rw [hsq, hnorm]
      linarith
    · exact norm_cellMap_le hk ε R hR (x : EuclideanSpace ℝ (Fin k)) (le_of_eq x.2)⟩

noncomputable def ballCellAdjunctionHomeo {n k : ℕ} (hk : k ≤ n) (c ε R : ℝ) (hε : 0 < ε)
    (hR : Real.sqrt (2 * ε) ≤ R) :
    CellAdjunctionSpace k (ballAttachMap hk c ε R (le_of_lt hε) hR) ≃ₜ ballLowerUnion hk c ε R := by
  refine cellAdjunctionHomeomorphUnionImage (n := k) (φ := ballAttachMap hk c ε R (le_of_lt hε) hR)
    (c := fun x : ClosedCell k => cellMap (Real.sqrt (2 * ε)) (x : EuclideanSpace ℝ (Fin k)))
    ?hφ ?hc ?hcont ?hinterior ?hclosed
  · intro b
    rfl
  · exact cellMap_injective hk ε hε
  · exact continuous_cellMap (Real.sqrt (2 * ε))
  · rw [Set.disjoint_left]
    intro y hyA hyB
    exact (Set.disjoint_left.mp (cellInterior_disjoint hk c ε hε)) hyA hyB.1
  · have hclosed : IsClosed {y : MorseModel n |
        y ∈ sublevel (morseNormalForm hk c) (c - ε) ∧ morseNorm n y ≤ R} := by
      have hcont : Continuous (fun y : MorseModel n => morseNorm n y) :=
        continuous_norm.comp (PiLp.continuous_toLp 2 (fun _ : Fin n => ℝ))
      exact (isClosed_sublevel_normalForm hk c (c - ε)).inter (isClosed_Iic.preimage hcont)
    exact hclosed

noncomputable def ballCellAttachmentModel {n k : ℕ} (hk : k ≤ n) (c ε R : ℝ) (hε : 0 < ε)
    (hR : Real.sqrt (2 * ε) ≤ R) :
    ContinuousMap.HomotopyEquiv (ballUpperSublevel hk c ε R)
      (CellAdjunctionSpace k (ballAttachMap hk c ε R (le_of_lt hε) hR)) :=
  (ballCellAttachmentHomotopyEquiv hk c ε R hε hR).trans
    (ballCellAdjunctionHomeo hk c ε R hε hR).symm.toHomotopyEquiv

theorem exists_reindexEquiv {n k : ℕ} (hk : k ≤ n) (w : Fin n → ℝ)
    (hw : ∀ i, w i = -1 ∨ w i = 1) (hcard : {i : Fin n | w i < 0}.ncard = k) :
    ∃ σe : Fin n ≃ Fin n,
      (∀ i : Fin k, w (σe (negIdx hk i)) = -1) ∧
      (∀ j : Fin (n - k), w (σe (posIdx hk j)) = 1) := by
  let negs : Finset (Fin n) := Finset.univ.filter (fun i => w i = -1)
  let poss : Finset (Fin n) := Finset.univ.filter (fun i => w i = 1)
  have hneg_card : negs.card = k := by
    have hset : {i : Fin n | w i < 0} = {i : Fin n | w i = -1} := by
      ext i
      constructor
      · intro hi
        rcases hw i with h | h
        · exact h
        · exfalso
          norm_num [h] at hi
      · intro hi
        change w i < 0
        rw [hi]
        norm_num
    have hcard' : ({i : Fin n | w i = -1} : Set (Fin n)).ncard = k := by
      simpa [hset] using hcard
    have hto : ({i : Fin n | w i = -1} : Set (Fin n)).toFinset = negs := by
      ext i
      simp [negs]
    have hncard := Set.ncard_eq_toFinset_card ({i : Fin n | w i = -1} : Set (Fin n)) (Set.toFinite _)
    have hto' : (Set.toFinite ({i : Fin n | w i = -1} : Set (Fin n))).toFinset = negs := by
      ext i
      simp [negs]
    rw [← hto']
    exact hncard.symm.trans hcard'
  have hdisj : Disjoint negs poss := by
    rw [Finset.disjoint_left]
    intro i hi hp
    have h1 : w i = -1 := (Finset.mem_filter.mp hi).2
    have h2 : w i = 1 := (Finset.mem_filter.mp hp).2
    linarith
  have hpos_card : poss.card = n - k := by
    have hunion : negs ∪ poss = Finset.univ := by
      ext i
      rcases hw i with h | h
      · simp [negs, poss, h]
      · simp [negs, poss, h]
    have hcard' : negs.card + poss.card = n := by
      rw [← Finset.card_union_of_disjoint hdisj, hunion, Finset.card_univ, Fintype.card_fin]
    omega
  let e0 : Sum (Fin k) (Fin (n - k)) ≃ Fin n :=
    { toFun := Sum.elim (negIdx hk) (posIdx hk)
      invFun := fun z => if h : z.val < k then Sum.inl ⟨z.val, h⟩ else Sum.inr ⟨z.val - k, by
        have hkle : k ≤ z.val := le_of_not_gt h
        have hz : z.val < n := z.isLt
        omega⟩
      left_inv := by
        intro s
        cases s with
        | inl i => simp [negIdx]
        | inr j => simp [posIdx]
      right_inv := by
        intro z
        by_cases h : z.val < k
        · simp [h, negIdx]
        · apply Fin.ext
          simp [h, posIdx]
          omega }
  let e1 : Sum (Fin k) (Fin (n - k)) ≃ Fin n :=
    { toFun := Sum.elim (fun i : Fin k => ((negs.orderIsoOfFin hneg_card) i : Fin n))
        (fun j : Fin (n - k) => ((poss.orderIsoOfFin hpos_card) j : Fin n))
      invFun := fun z => if h : z ∈ negs then
          Sum.inl ((negs.orderIsoOfFin hneg_card).symm ⟨z, h⟩)
        else
          Sum.inr ((poss.orderIsoOfFin hpos_card).symm ⟨z, by
            have hne : w z ≠ -1 := by
              intro hz
              exact h (by simp [negs, hz])
            rcases hw z with hwz | hwz
            · exact (hne hwz).elim
            · simp [poss, hwz]⟩)
      left_inv := by
        intro s
        cases s with
        | inl i =>
            have hmem : ((negs.orderIsoOfFin hneg_card) i : Fin n) ∈ negs :=
              ((negs.orderIsoOfFin hneg_card) i).2
            have hmem' : negs.orderEmbOfFin hneg_card i ∈ negs := by
              rw [← Finset.coe_orderIsoOfFin_apply]
              exact hmem
            dsimp
            rw [dif_pos hmem']
            apply congrArg Sum.inl
            exact (negs.orderIsoOfFin hneg_card).symm_apply_apply i
        | inr j =>
            have hmem : ((poss.orderIsoOfFin hpos_card) j : Fin n) ∈ poss :=
              ((poss.orderIsoOfFin hpos_card) j).2
            have hnot : ((poss.orderIsoOfFin hpos_card) j : Fin n) ∉ negs := by
              exact (Finset.disjoint_left.mp (Disjoint.symm hdisj)) hmem
            have hnot' : poss.orderEmbOfFin hpos_card j ∉ negs := by
              rw [← Finset.coe_orderIsoOfFin_apply]
              exact hnot
            dsimp
            rw [dif_neg hnot']
            apply congrArg Sum.inr
            convert (poss.orderIsoOfFin hpos_card).symm_apply_apply j using 1
      right_inv := by
        intro z
        by_cases h : z ∈ negs
        · dsimp
          rw [dif_pos h]
          exact congrArg (fun w : negs => (w : Fin n))
            ((negs.orderIsoOfFin hneg_card).apply_symm_apply ⟨z, h⟩)
        · have hposs' : z ∈ poss := by
            have hne : w z ≠ -1 := by
              intro hz
              exact h (by simp [negs, hz])
            rcases hw z with hwz | hwz
            · exact (hne hwz).elim
            · simp [poss, hwz]
          dsimp
          rw [dif_neg h]
          exact congrArg (fun w : poss => (w : Fin n))
            ((poss.orderIsoOfFin hpos_card).apply_symm_apply ⟨z, hposs'⟩) }
  refine ⟨e0.symm.trans e1, ?_, ?_⟩
  · intro i
    have hz : e0.symm (negIdx hk i) = Sum.inl i := by
      dsimp [e0]
      simp [negIdx]
    change w (e1 (e0.symm (negIdx hk i))) = -1
    rw [hz]
    change w ((negs.orderIsoOfFin hneg_card) i : Fin n) = -1
    exact (Finset.mem_filter.mp ((negs.orderIsoOfFin hneg_card) i).2).2
  · intro j
    have hz : e0.symm (posIdx hk j) = Sum.inr j := by
      dsimp [e0]
      simp [posIdx]
    change w (e1 (e0.symm (posIdx hk j))) = 1
    rw [hz]
    change w ((poss.orderIsoOfFin hpos_card) j : Fin n) = 1
    exact (Finset.mem_filter.mp ((poss.orderIsoOfFin hpos_card) j).2).2

theorem w_sum_reindexed {n k : ℕ} (hk : k ≤ n) (w : Fin n → ℝ)
    (σe : Fin n ≃ Fin n) (hwneg : ∀ i : Fin k, w (σe (negIdx hk i)) = -1)
    (hwpos : ∀ j : Fin (n - k), w (σe (posIdx hk j)) = 1) (y : MorseModel n) :
    (∑ i : Fin n, w i * (y (σe.symm i)) ^ 2) =
      (∑ i : Fin k, - (y (negIdx hk i)) ^ 2) + (∑ j : Fin (n - k), (y (posIdx hk j)) ^ 2) := by
  calc
    (∑ i : Fin n, w i * (y (σe.symm i)) ^ 2)
        = ∑ j : Fin n, w (σe j) * (y j) ^ 2 := by
          symm
          exact Fintype.sum_equiv σe
            (fun j : Fin n => w (σe j) * (y j) ^ 2)
            (fun i : Fin n => w i * (y (σe.symm i)) ^ 2)
            (by intro j; simp)
    _ = (∑ i : Fin k, - (y (negIdx hk i)) ^ 2) + (∑ j : Fin (n - k), (y (posIdx hk j)) ^ 2) := by
      rw [sum_split_fin hk (fun j : Fin n => w (σe j) * (y j) ^ 2)]
      congr 1
      · apply Finset.sum_congr rfl
        intro i hi
        rw [hwneg i]
        ring
      · apply Finset.sum_congr rfl
        intro j hj
        rw [hwpos j]
        simp

def addHomeo (n : ℕ) (a : MorseModel n) : MorseModel n ≃ₜ MorseModel n where
  toFun := fun z => a + z
  invFun := fun z => z - a
  left_inv := by intro z; simp
  right_inv := by intro z; simp
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

def reindexHomeo {n : ℕ} (σe : Fin n ≃ Fin n) : MorseModel n ≃ₜ MorseModel n where
  toFun := fun y => y ∘ σe.symm
  invFun := fun y => y ∘ σe
  left_inv := by
    intro y
    funext i
    simp
  right_inv := by
    intro y
    funext i
    simp
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

theorem supNorm_le_morseNorm {n : ℕ} (y : MorseModel n) : ‖y‖ ≤ morseNorm n y := by
  rw [Pi.norm_def]
  exact_mod_cast (Finset.sup_le (s := Finset.univ) (f := fun i : Fin n => ‖y i‖₊)
    (a := ⟨morseNorm n y, norm_nonneg _⟩) (by
      intro i hi
      exact PiLp.norm_apply_le (x := (WithLp.toLp 2 y : EuclideanSpace ℝ (Fin n))) i))

noncomputable def modelSharpUnionBound (ε r : ℝ) (t : ℝ) : ℝ :=
  max (r ^ 2) (t - 2 * ε)

noncomputable def modelSharpUnionRound {n k : ℕ} (hk : k ≤ n) (ε r δ : ℝ)
    (y : MorseModel n) : MorseModel n :=
  recombine hk (negPart hk y)
    ((Real.sqrt (smoothCap ε r δ (‖negPart hk y‖ ^ 2) /
        modelSharpUnionBound ε r (‖negPart hk y‖ ^ 2))) • posPart hk y)

noncomputable def modelSharpUnionUnround {n k : ℕ} (hk : k ≤ n) (ε r δ : ℝ)
    (y : MorseModel n) : MorseModel n :=
  recombine hk (negPart hk y)
    ((Real.sqrt (modelSharpUnionBound ε r (‖negPart hk y‖ ^ 2) /
        smoothCap ε r δ (‖negPart hk y‖ ^ 2))) • posPart hk y)

theorem modelSharpUnionBound_pos {ε r t : ℝ} (hr : r ≠ 0) : 0 < modelSharpUnionBound ε r t := by
  dsimp [modelSharpUnionBound]
  exact lt_of_lt_of_le (sq_pos_of_ne_zero hr) (le_max_left (r ^ 2) (t - 2 * ε))

theorem modelSharpUnionRound_posPart_norm_sq {n k : ℕ} (hk : k ≤ n) (ε r δ : ℝ)
    (hδ0 : 0 < δ) (hδr : δ < r ^ 2) (y : MorseModel n) :
    ‖posPart hk (modelSharpUnionRound hk ε r δ y)‖ ^ 2 =
      smoothCap ε r δ (‖negPart hk y‖ ^ 2) / modelSharpUnionBound ε r (‖negPart hk y‖ ^ 2) *
        ‖posPart hk y‖ ^ 2 := by
  dsimp [modelSharpUnionRound]
  rw [posPart_recombine]
  rw [norm_smul]
  rw [Real.norm_eq_abs]
  have hsc : 0 < smoothCap ε r δ (‖negPart hk y‖ ^ 2) := smoothCap_pos hδ0 hδr
  have hB : 0 < modelSharpUnionBound ε r (‖negPart hk y‖ ^ 2) :=
    modelSharpUnionBound_pos (hr := by
      intro h
      rw [h] at hδr
      nlinarith [hδ0, hδr])
  rw [abs_of_nonneg (Real.sqrt_nonneg _)]
  rw [mul_pow]
  rw [Real.sq_sqrt (by positivity : 0 ≤ smoothCap ε r δ (‖negPart hk y‖ ^ 2) /
    modelSharpUnionBound ε r (‖negPart hk y‖ ^ 2))]

theorem modelSharpUnionUnround_posPart_norm_sq {n k : ℕ} (hk : k ≤ n) (ε r δ : ℝ)
    (hδ0 : 0 < δ) (hδr : δ < r ^ 2) (hr : r ≠ 0) (y : MorseModel n) :
    ‖posPart hk (modelSharpUnionUnround hk ε r δ y)‖ ^ 2 =
      modelSharpUnionBound ε r (‖negPart hk y‖ ^ 2) / smoothCap ε r δ (‖negPart hk y‖ ^ 2) *
        ‖posPart hk y‖ ^ 2 := by
  dsimp [modelSharpUnionUnround]
  rw [posPart_recombine]
  rw [norm_smul]
  rw [Real.norm_eq_abs]
  rw [abs_of_nonneg (Real.sqrt_nonneg _)]
  rw [mul_pow]
  rw [Real.sq_sqrt (by
    exact div_nonneg (le_of_lt (modelSharpUnionBound_pos (hr := hr)))
      (le_of_lt (smoothCap_pos hδ0 hδr)))]

theorem modelSharpUnionRound_mem_attached {n k : ℕ} (hk : k ≤ n) (c ε r δ : ℝ)
    (hδ0 : 0 < δ) (hδr : δ < r ^ 2)
    {y : MorseModel n} (hy : y ∈ (sublevel (morseNormalForm hk c) (c - ε) : Set (MorseModel n)) ∪
      modelHandle hk ε r) :
    modelSharpUnionRound hk ε r δ y ∈ modelAttachedRegion hk ε r δ := by
  dsimp [modelAttachedRegion]
  rw [modelSharpUnionRound_posPart_norm_sq hk ε r δ hδ0 hδr y]
  dsimp [modelSharpUnionRound]
  rw [negPart_recombine]
  have hB : ‖posPart hk y‖ ^ 2 ≤ modelSharpUnionBound ε r (‖negPart hk y‖ ^ 2) := by
    rcases hy with hl | hh
    · have hf : morseNormalForm hk c y ≤ c - ε := by simpa [sublevel] using hl
      rw [morseNormalForm_split] at hf
      dsimp [modelSharpUnionBound]
      exact le_trans (by nlinarith) (le_max_right (r ^ 2) (‖negPart hk y‖ ^ 2 - 2 * ε))
    · rcases hh with ⟨hp, hn⟩
      dsimp [modelSharpUnionBound]
      exact le_trans hp (le_max_left (r ^ 2) (‖negPart hk y‖ ^ 2 - 2 * ε))
  have hsc_pos : 0 < smoothCap ε r δ (‖negPart hk y‖ ^ 2) := smoothCap_pos hδ0 hδr
  have hB_pos : 0 < modelSharpUnionBound ε r (‖negPart hk y‖ ^ 2) := by
    exact modelSharpUnionBound_pos (hr := by
      intro h
      rw [h] at hδr
      nlinarith [hδ0, hδr])
  have hmain : smoothCap ε r δ (‖negPart hk y‖ ^ 2) / modelSharpUnionBound ε r (‖negPart hk y‖ ^ 2) *
      ‖posPart hk y‖ ^ 2 ≤ smoothCap ε r δ (‖negPart hk y‖ ^ 2) := by
    have hle' : ‖posPart hk y‖ ^ 2 / modelSharpUnionBound ε r (‖negPart hk y‖ ^ 2) ≤ 1 :=
      (div_le_one hB_pos).2 hB
    calc
      smoothCap ε r δ (‖negPart hk y‖ ^ 2) / modelSharpUnionBound ε r (‖negPart hk y‖ ^ 2) *
          ‖posPart hk y‖ ^ 2
          = smoothCap ε r δ (‖negPart hk y‖ ^ 2) *
            (‖posPart hk y‖ ^ 2 / modelSharpUnionBound ε r (‖negPart hk y‖ ^ 2)) := by ring
      _ ≤ smoothCap ε r δ (‖negPart hk y‖ ^ 2) * 1 :=
        mul_le_mul_of_nonneg_left hle' (le_of_lt hsc_pos)
      _ = smoothCap ε r δ (‖negPart hk y‖ ^ 2) := by ring
  exact hmain

theorem modelSharpUnionUnround_posPart_le_bound {n k : ℕ} (hk : k ≤ n) (ε r δ : ℝ)
    (hδ0 : 0 < δ) (hδr : δ < r ^ 2)
    {y : MorseModel n} (hy : y ∈ modelAttachedRegion hk ε r δ) :
    ‖posPart hk (modelSharpUnionUnround hk ε r δ y)‖ ^ 2 ≤
      modelSharpUnionBound ε r (‖negPart hk y‖ ^ 2) := by
  rw [modelSharpUnionUnround_posPart_norm_sq hk ε r δ hδ0 hδr
    (by intro h; rw [h] at hδr; nlinarith [hδ0, hδr]) y]
  dsimp [modelAttachedRegion] at hy
  have hB_pos : 0 < modelSharpUnionBound ε r (‖negPart hk y‖ ^ 2) := by
    exact modelSharpUnionBound_pos (hr := by
      intro h
      rw [h] at hδr
      nlinarith [hδ0, hδr])
  have hsc_pos : 0 < smoothCap ε r δ (‖negPart hk y‖ ^ 2) := smoothCap_pos hδ0 hδr
  have hle' : ‖posPart hk y‖ ^ 2 / smoothCap ε r δ (‖negPart hk y‖ ^ 2) ≤ 1 := by
    exact (div_le_one hsc_pos).2 hy
  calc
    modelSharpUnionBound ε r (‖negPart hk y‖ ^ 2) / smoothCap ε r δ (‖negPart hk y‖ ^ 2) *
        ‖posPart hk y‖ ^ 2
        = modelSharpUnionBound ε r (‖negPart hk y‖ ^ 2) *
          (‖posPart hk y‖ ^ 2 / smoothCap ε r δ (‖negPart hk y‖ ^ 2)) := by ring
    _ ≤ modelSharpUnionBound ε r (‖negPart hk y‖ ^ 2) * 1 :=
      mul_le_mul_of_nonneg_left hle' (le_of_lt hB_pos)
    _ = modelSharpUnionBound ε r (‖negPart hk y‖ ^ 2) := by ring

theorem modelSharpUnionUnround_mem_sharpUnion {n k : ℕ} (hk : k ≤ n) (c ε r δ : ℝ)
    (hδ0 : 0 < δ) (hδr : δ < r ^ 2)
    {y : MorseModel n} (hy : y ∈ modelAttachedRegion hk ε r δ) :
    modelSharpUnionUnround hk ε r δ y ∈
      (sublevel (morseNormalForm hk c) (c - ε) : Set (MorseModel n)) ∪ modelHandle hk ε r := by
  let z : MorseModel n := modelSharpUnionUnround hk ε r δ y
  have hpos_le : ‖posPart hk z‖ ^ 2 ≤ modelSharpUnionBound ε r (‖negPart hk y‖ ^ 2) := by
    simpa [z] using modelSharpUnionUnround_posPart_le_bound hk ε r δ hδ0 hδr hy
  have hneg_eq : ‖negPart hk z‖ ^ 2 = ‖negPart hk y‖ ^ 2 := by
    dsimp [z, modelSharpUnionUnround]
    rw [negPart_recombine]
  by_cases hl : z ∈ sublevel (morseNormalForm hk c) (c - ε)
  · exact Or.inl hl
  · right
    constructor
    · change ‖posPart hk z‖ ^ 2 ≤ r ^ 2
      have hposgt : ‖negPart hk y‖ ^ 2 - 2 * ε < ‖posPart hk z‖ ^ 2 := by
        have hmem : ¬ (z ∈ sublevel (morseNormalForm hk c) (c - ε)) := hl
        have hf : ¬ morseNormalForm hk c z ≤ c - ε := by
          intro hh
          exact hmem (by simpa [sublevel] using hh)
        have hnot : c - ε < morseNormalForm hk c z := lt_of_not_ge hf
        rw [morseNormalForm_split] at hnot
        nlinarith
      have hmax : modelSharpUnionBound ε r (‖negPart hk y‖ ^ 2) ≠ ‖negPart hk y‖ ^ 2 - 2 * ε := by
        intro hh
        have : ‖posPart hk z‖ ^ 2 ≤ ‖negPart hk y‖ ^ 2 - 2 * ε := by simpa [hh] using hpos_le
        nlinarith
      have hnotle : modelSharpUnionBound ε r (‖negPart hk y‖ ^ 2) = r ^ 2 := by
        dsimp [modelSharpUnionBound]
        exact max_eq_left (by
          by_contra hh
          have : max (r ^ 2) (‖negPart hk y‖ ^ 2 - 2 * ε) = ‖negPart hk y‖ ^ 2 - 2 * ε :=
            max_eq_right (le_of_lt (lt_of_not_ge hh))
          exact hmax this)
      exact le_trans (by simpa [hnotle] using hpos_le) (le_of_eq hnotle)
    · change ‖negPart hk z‖ ^ 2 ≤ ‖posPart hk z‖ ^ 2 + 2 * ε
      rw [hneg_eq]
      have hnot : c - ε < morseNormalForm hk c z := by
        have hmem : ¬ (z ∈ sublevel (morseNormalForm hk c) (c - ε)) := hl
        have hf : ¬ morseNormalForm hk c z ≤ c - ε := by
          intro hh
          exact hmem (by simpa [sublevel] using hh)
        exact lt_of_not_ge hf
      rw [morseNormalForm_split] at hnot
      have hineq : ‖negPart hk y‖ ^ 2 < ‖posPart hk z‖ ^ 2 + 2 * ε := by
        nlinarith
      exact le_of_lt hineq

private lemma sqrt_div_mul_sqrt_div (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    Real.sqrt (a / b) * Real.sqrt (b / a) = 1 := by
  have h1 : (Real.sqrt (a / b) * Real.sqrt (b / a)) ^ 2 = 1 := by
    rw [mul_pow]
    rw [Real.sq_sqrt (div_nonneg (le_of_lt ha) (le_of_lt hb))]
    rw [Real.sq_sqrt (div_nonneg (le_of_lt hb) (le_of_lt ha))]
    field_simp [ne_of_gt ha, ne_of_gt hb]
  rcases (sq_eq_one_iff.mp h1) with h | h
  · exact h
  · have hnon : (0 : ℝ) ≤ Real.sqrt (a / b) * Real.sqrt (b / a) := by positivity
    nlinarith

theorem modelSharpUnionRound_unround {n k : ℕ} (hk : k ≤ n) (ε r δ : ℝ)
    (hδ0 : 0 < δ) (hδr : δ < r ^ 2) {z : MorseModel n} :
    modelSharpUnionRound hk ε r δ (modelSharpUnionUnround hk ε r δ z) = z := by
  let t : ℝ := ‖negPart hk z‖ ^ 2
  let sc : ℝ := smoothCap ε r δ t
  let B : ℝ := modelSharpUnionBound ε r t
  have hsc : 0 < sc := by
    dsimp [sc, t]
    exact smoothCap_pos hδ0 hδr
  have hB : 0 < B := by
    dsimp [B, t]
    exact modelSharpUnionBound_pos (hr := by
      intro h
      rw [h] at hδr
      nlinarith [hδ0, hδr])
  calc
    modelSharpUnionRound hk ε r δ (modelSharpUnionUnround hk ε r δ z)
        = recombine hk (negPart hk z) (posPart hk z) := by
          dsimp [modelSharpUnionRound, modelSharpUnionUnround, sc, B, t]
          rw [negPart_recombine, posPart_recombine]
          congr 1
          rw [smul_smul]
          rw [sqrt_div_mul_sqrt_div sc B hsc hB]
          simp
    _ = z := recombine_decompose hk z

theorem modelSharpUnionUnround_round {n k : ℕ} (hk : k ≤ n) (ε r δ : ℝ)
    (hδ0 : 0 < δ) (hδr : δ < r ^ 2) {y : MorseModel n} :
    modelSharpUnionUnround hk ε r δ (modelSharpUnionRound hk ε r δ y) = y := by
  let t : ℝ := ‖negPart hk y‖ ^ 2
  let sc : ℝ := smoothCap ε r δ t
  let B : ℝ := modelSharpUnionBound ε r t
  have hsc : 0 < sc := by
    dsimp [sc, t]
    exact smoothCap_pos hδ0 hδr
  have hB : 0 < B := by
    dsimp [B, t]
    exact modelSharpUnionBound_pos (hr := by
      intro h
      rw [h] at hδr
      nlinarith [hδ0, hδr])
  calc
    modelSharpUnionUnround hk ε r δ (modelSharpUnionRound hk ε r δ y)
        = recombine hk (negPart hk y) (posPart hk y) := by
          dsimp [modelSharpUnionUnround, modelSharpUnionRound, sc, B, t]
          rw [negPart_recombine, posPart_recombine]
          congr 1
          rw [smul_smul]
          rw [sqrt_div_mul_sqrt_div B sc hB hsc]
          simp
    _ = y := recombine_decompose hk y

theorem modelSharpUnionRound_eq_self_of_negPart_large {n k : ℕ} (hk : k ≤ n) (ε r δ : ℝ)
    (hδ0 : 0 < δ) (hδr : δ < r ^ 2)
    {y : MorseModel n} (ht : r ^ 2 + 2 * ε + δ ≤ ‖negPart hk y‖ ^ 2) :
    modelSharpUnionRound hk ε r δ y = y := by
  have hsc : smoothCap ε r δ (‖negPart hk y‖ ^ 2) = ‖negPart hk y‖ ^ 2 - 2 * ε := by
    exact smoothCap_upper hδ0 ht
  have hB : modelSharpUnionBound ε r (‖negPart hk y‖ ^ 2) = ‖negPart hk y‖ ^ 2 - 2 * ε := by
    dsimp [modelSharpUnionBound]
    exact max_eq_right (by nlinarith [ht, hδ0])
  calc
    modelSharpUnionRound hk ε r δ y = recombine hk (negPart hk y) (posPart hk y) := by
      dsimp [modelSharpUnionRound]
      rw [hsc, hB]
      congr 1
      have hne : ‖negPart hk y‖ ^ 2 - 2 * ε ≠ 0 := by nlinarith [ht, hδ0]
      have hratio : (‖negPart hk y‖ ^ 2 - 2 * ε) / (‖negPart hk y‖ ^ 2 - 2 * ε) = 1 := by
        field_simp [hne]
      rw [hratio, Real.sqrt_one]
      simp
    _ = y := recombine_decompose hk y

theorem modelSharpUnionUnround_eq_self_of_negPart_large {n k : ℕ} (hk : k ≤ n) (ε r δ : ℝ)
    (hδ0 : 0 < δ) (hδr : δ < r ^ 2)
    {y : MorseModel n} (ht : r ^ 2 + 2 * ε + δ ≤ ‖negPart hk y‖ ^ 2) :
    modelSharpUnionUnround hk ε r δ y = y := by
  have hsc : smoothCap ε r δ (‖negPart hk y‖ ^ 2) = ‖negPart hk y‖ ^ 2 - 2 * ε := by
    exact smoothCap_upper hδ0 ht
  have hB : modelSharpUnionBound ε r (‖negPart hk y‖ ^ 2) = ‖negPart hk y‖ ^ 2 - 2 * ε := by
    dsimp [modelSharpUnionBound]
    exact max_eq_right (by nlinarith [ht, hδ0])
  calc
    modelSharpUnionUnround hk ε r δ y = recombine hk (negPart hk y) (posPart hk y) := by
      dsimp [modelSharpUnionUnround]
      rw [hsc, hB]
      congr 1
      have hne : ‖negPart hk y‖ ^ 2 - 2 * ε ≠ 0 := by nlinarith [ht, hδ0]
      have hratio : (‖negPart hk y‖ ^ 2 - 2 * ε) / (‖negPart hk y‖ ^ 2 - 2 * ε) = 1 := by
        field_simp [hne]
      rw [hratio, Real.sqrt_one]
      simp
    _ = y := recombine_decompose hk y

theorem modelSharpUnionRound_eq_self_of_deep {n k : ℕ} (hk : k ≤ n) (c ε r δ η : ℝ)
    (hδ0 : 0 < δ) (hδr : δ < r ^ 2)
    {y : MorseModel n} (hη : r ^ 2 + δ ≤ 2 * η)
    (hy : morseNormalForm hk c y ≤ c - ε - η) :
    modelSharpUnionRound hk ε r δ y = y := by
  have ht : r ^ 2 + 2 * ε + δ ≤ ‖negPart hk y‖ ^ 2 := by
    rw [morseNormalForm_split] at hy
    have h : ‖posPart hk y‖ ^ 2 ≤ ‖negPart hk y‖ ^ 2 - 2 * ε - 2 * η := by nlinarith
    nlinarith [h, hη]
  exact modelSharpUnionRound_eq_self_of_negPart_large hk ε r δ hδ0 hδr ht

theorem modelSharpUnionRound_morseNorm_le {n k : ℕ} (hk : k ≤ n) (ε r δ : ℝ)
    (hδ0 : 0 < δ) (hδr : δ < r ^ 2) (y : MorseModel n) :
    morseNorm n (modelSharpUnionRound hk ε r δ y) ≤ morseNorm n y := by
  have hsq : morseNorm n (modelSharpUnionRound hk ε r δ y) ^ 2 ≤ morseNorm n y ^ 2 := by
    dsimp [modelSharpUnionRound]
    rw [morseNorm_recombine_sq hk (negPart hk y)
      (Real.sqrt (smoothCap ε r δ (‖negPart hk y‖ ^ 2) / modelSharpUnionBound ε r (‖negPart hk y‖ ^ 2)) •
        posPart hk y)]
    have hnorm_y : morseNorm n y ^ 2 = ‖negPart hk y‖ ^ 2 + ‖posPart hk y‖ ^ 2 := by
      rw [← recombine_decompose hk y]
      rw [morseNorm_recombine_sq hk (negPart hk y) (posPart hk y)]
      simp [negPart_recombine, posPart_recombine]
    rw [hnorm_y]
    have hsc_le : smoothCap ε r δ (‖negPart hk y‖ ^ 2) ≤ modelSharpUnionBound ε r (‖negPart hk y‖ ^ 2) := by
      dsimp [modelSharpUnionBound]
      by_cases hle : ‖negPart hk y‖ ^ 2 - 2 * ε ≤ r ^ 2
      · have hmax : max (r ^ 2) (‖negPart hk y‖ ^ 2 - 2 * ε) = r ^ 2 := max_eq_left hle
        rw [hmax]
        dsimp [smoothCap]
        have hst0 : 0 ≤ Real.smoothTransition ((‖negPart hk y‖ ^ 2 - (r ^ 2 + 2 * ε - δ)) / (2 * δ)) :=
          Real.smoothTransition.nonneg _
        nlinarith
      · have hmax : max (r ^ 2) (‖negPart hk y‖ ^ 2 - 2 * ε) = ‖negPart hk y‖ ^ 2 - 2 * ε :=
          max_eq_right (le_of_not_ge hle)
        rw [hmax]
        dsimp [smoothCap]
        have hst1 : Real.smoothTransition ((‖negPart hk y‖ ^ 2 - (r ^ 2 + 2 * ε - δ)) / (2 * δ)) ≤ 1 :=
          Real.smoothTransition.le_one _
        nlinarith
    have hsq1 : ‖Real.sqrt (smoothCap ε r δ (‖negPart hk y‖ ^ 2) / modelSharpUnionBound ε r (‖negPart hk y‖ ^ 2)) •
        posPart hk y‖ ^ 2 ≤ ‖posPart hk y‖ ^ 2 := by
      rw [norm_smul]
      rw [Real.norm_eq_abs]
      rw [abs_of_nonneg (Real.sqrt_nonneg _)]
      rw [mul_pow]
      rw [Real.sq_sqrt (by
        have hBpos : 0 < modelSharpUnionBound ε r (‖negPart hk y‖ ^ 2) := by
          exact modelSharpUnionBound_pos (hr := by
            intro h
            rw [h] at hδr
            nlinarith [hδ0, hδr])
        exact div_nonneg (le_of_lt (smoothCap_pos hδ0 hδr)) (le_of_lt hBpos))]
      have hle' : smoothCap ε r δ (‖negPart hk y‖ ^ 2) / modelSharpUnionBound ε r (‖negPart hk y‖ ^ 2) ≤ 1 := by
        exact (div_le_one (by
          exact modelSharpUnionBound_pos (hr := by
            intro h
            rw [h] at hδr
            nlinarith [hδ0, hδr]))).2 hsc_le
      nlinarith [hle', sq_nonneg (smoothCap ε r δ (‖negPart hk y‖ ^ 2) /
        modelSharpUnionBound ε r (‖negPart hk y‖ ^ 2))]
    nlinarith [hsq1]
  have habs : |morseNorm n (modelSharpUnionRound hk ε r δ y)| ≤ |morseNorm n y| := sq_le_sq.mp hsq
  rwa [abs_of_nonneg (norm_nonneg _), abs_of_nonneg (norm_nonneg _)] at habs

theorem modelSharpUnionUnround_norm_sq_le {n k : ℕ} (hk : k ≤ n) (ε r δ : ℝ)
    (hδ0 : 0 < δ) (hδr : δ < r ^ 2) (hr : r ≠ 0)
    {y : MorseModel n} (hy : y ∈ modelAttachedRegion hk ε r δ) :
    morseNorm n (modelSharpUnionUnround hk ε r δ y) ^ 2 ≤
      ‖negPart hk y‖ ^ 2 + modelSharpUnionBound ε r (‖negPart hk y‖ ^ 2) := by
  dsimp [modelSharpUnionUnround]
  rw [morseNorm_recombine_sq hk (negPart hk y)
    (Real.sqrt (modelSharpUnionBound ε r (‖negPart hk y‖ ^ 2) / smoothCap ε r δ (‖negPart hk y‖ ^ 2)) •
      posPart hk y)]
  rw [norm_smul]
  rw [Real.norm_eq_abs]
  rw [abs_of_nonneg (Real.sqrt_nonneg _)]
  rw [mul_pow]
  rw [Real.sq_sqrt (by
    have hsc : 0 < smoothCap ε r δ (‖negPart hk y‖ ^ 2) := smoothCap_pos hδ0 hδr
    have hB : 0 < modelSharpUnionBound ε r (‖negPart hk y‖ ^ 2) :=
      modelSharpUnionBound_pos hr
    exact div_nonneg (le_of_lt hB) (le_of_lt hsc))]
  have hle : ‖posPart hk y‖ ^ 2 ≤ smoothCap ε r δ (‖negPart hk y‖ ^ 2) := by
    dsimp [modelAttachedRegion] at hy
    exact hy
  have hmain : modelSharpUnionBound ε r (‖negPart hk y‖ ^ 2) / smoothCap ε r δ (‖negPart hk y‖ ^ 2) *
      ‖posPart hk y‖ ^ 2 ≤ modelSharpUnionBound ε r (‖negPart hk y‖ ^ 2) := by
    have hsc : 0 < smoothCap ε r δ (‖negPart hk y‖ ^ 2) := smoothCap_pos hδ0 hδr
    have hB : 0 < modelSharpUnionBound ε r (‖negPart hk y‖ ^ 2) := modelSharpUnionBound_pos hr
    have hle' : ‖posPart hk y‖ ^ 2 / smoothCap ε r δ (‖negPart hk y‖ ^ 2) ≤ 1 :=
      (div_le_one hsc).2 hle
    calc
      modelSharpUnionBound ε r (‖negPart hk y‖ ^ 2) / smoothCap ε r δ (‖negPart hk y‖ ^ 2) *
          ‖posPart hk y‖ ^ 2
          = modelSharpUnionBound ε r (‖negPart hk y‖ ^ 2) *
            (‖posPart hk y‖ ^ 2 / smoothCap ε r δ (‖negPart hk y‖ ^ 2)) := by ring
      _ ≤ modelSharpUnionBound ε r (‖negPart hk y‖ ^ 2) * 1 :=
        mul_le_mul_of_nonneg_left hle' (le_of_lt hB)
      _ = modelSharpUnionBound ε r (‖negPart hk y‖ ^ 2) := by ring
  nlinarith

theorem norm_negPart_le_morseNorm {n k : ℕ} (hk : k ≤ n) (y : MorseModel n) :
    ‖negPart hk y‖ ≤ morseNorm n y := by
  have hsq : ‖negPart hk y‖ ^ 2 ≤ morseNorm n y ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq (negPart hk y)]
    rw [EuclideanSpace.real_norm_sq_eq (WithLp.toLp 2 y : EuclideanSpace ℝ (Fin n))]
    have hinj : Function.Injective (negIdx hk) := Fin.castLE_injective hk
    have hinjOn : Set.InjOn (negIdx hk) (↑(Finset.univ : Finset (Fin k))) := by
      intro a ha b hb hab
      exact hinj hab
    let img : Finset (Fin n) := Finset.image (negIdx hk) (Finset.univ : Finset (Fin k))
    have hsum : (∑ i : Fin k, ((negPart hk y).ofLp i) ^ 2) ≤
        ∑ j : Fin n, ((WithLp.toLp 2 y).ofLp j) ^ 2 := by
      calc
        (∑ i : Fin k, ((negPart hk y).ofLp i) ^ 2) = ∑ i : Fin k, (y (negIdx hk i)) ^ 2 := by
          apply Finset.sum_congr rfl
          intro i hi
          simp [negPart]
        _ = ∑ j ∈ img, (y j) ^ 2 := by
          dsimp [img]
          rw [Finset.sum_image hinjOn]
        _ ≤ ∑ j : Fin n, ((WithLp.toLp 2 y).ofLp j) ^ 2 := by
          have hrew : (∑ j : Fin n, ((WithLp.toLp 2 y).ofLp j) ^ 2) = ∑ j : Fin n, (y j) ^ 2 := by
            apply Finset.sum_congr rfl
            intro j hj
            simp
          rw [hrew]
          exact Finset.sum_le_sum_of_subset_of_nonneg
            (by intro x hx; exact Finset.mem_univ x)
            (by intro x hx hx0; positivity)
    exact hsum
  have habs : |‖negPart hk y‖| ≤ |morseNorm n y| := sq_le_sq.mp hsq
  rwa [abs_of_nonneg (norm_nonneg _), abs_of_nonneg (norm_nonneg _)] at habs

theorem continuous_modelSharpUnionRound {n k : ℕ} (hk : k ≤ n) (ε r δ : ℝ)
    (hδ0 : 0 < δ) (hδr : δ < r ^ 2) :
    Continuous (modelSharpUnionRound hk ε r δ) := by
  let hlfun : MorseModel n → ℝ := fun y =>
    Real.sqrt (smoothCap ε r δ (‖negPart hk y‖ ^ 2) /
      modelSharpUnionBound ε r (‖negPart hk y‖ ^ 2))
  have hl : Continuous hlfun := by
    have hsc : Continuous (fun y : MorseModel n => smoothCap ε r δ (‖negPart hk y‖ ^ 2)) :=
      (smoothCap_contDiff ε r δ).continuous.comp ((continuous_norm.comp (continuous_negPart hk)).pow 2)
    have hB : Continuous (fun y : MorseModel n => modelSharpUnionBound ε r (‖negPart hk y‖ ^ 2)) :=
      (continuous_const.max
        (((continuous_norm.comp (continuous_negPart hk)).pow 2).sub continuous_const))
    have hBpos : ∀ y : MorseModel n, 0 < modelSharpUnionBound ε r (‖negPart hk y‖ ^ 2) := fun y =>
      modelSharpUnionBound_pos (hr := by
        intro h
        rw [h] at hδr
        nlinarith [hδ0, hδr])
    simpa [hlfun] using (Real.continuous_sqrt.comp (hsc.div hB (fun y => ne_of_gt (hBpos y))))
  have hpair : Continuous (fun y : MorseModel n =>
      (negPart hk y, hlfun y • posPart hk y)) :=
    (continuous_negPart hk).prodMk (hl.smul (continuous_posPart hk))
  have hmain : Continuous (fun y : MorseModel n =>
      recombine hk (negPart hk y) (hlfun y • posPart hk y)) :=
    (continuous_recombine hk).comp hpair
  refine hmain.congr ?_
  intro y
  rfl

theorem continuous_modelSharpUnionUnround {n k : ℕ} (hk : k ≤ n) (ε r δ : ℝ)
    (hδ0 : 0 < δ) (hδr : δ < r ^ 2) :
    Continuous (modelSharpUnionUnround hk ε r δ) := by
  let hmfun : MorseModel n → ℝ := fun y =>
    Real.sqrt (modelSharpUnionBound ε r (‖negPart hk y‖ ^ 2) /
      smoothCap ε r δ (‖negPart hk y‖ ^ 2))
  have hm : Continuous hmfun := by
    have hsc : Continuous (fun y : MorseModel n => smoothCap ε r δ (‖negPart hk y‖ ^ 2)) :=
      (smoothCap_contDiff ε r δ).continuous.comp ((continuous_norm.comp (continuous_negPart hk)).pow 2)
    have hB : Continuous (fun y : MorseModel n => modelSharpUnionBound ε r (‖negPart hk y‖ ^ 2)) :=
      (continuous_const.max
        (((continuous_norm.comp (continuous_negPart hk)).pow 2).sub continuous_const))
    have hscpos : ∀ y : MorseModel n, 0 < smoothCap ε r δ (‖negPart hk y‖ ^ 2) := fun y =>
      smoothCap_pos hδ0 hδr
    simpa [hmfun] using (Real.continuous_sqrt.comp (hB.div hsc (fun y => ne_of_gt (hscpos y))))
  have hpair : Continuous (fun y : MorseModel n =>
      (negPart hk y, hmfun y • posPart hk y)) :=
    (continuous_negPart hk).prodMk (hm.smul (continuous_posPart hk))
  have hmain : Continuous (fun y : MorseModel n =>
      recombine hk (negPart hk y) (hmfun y • posPart hk y)) :=
    (continuous_recombine hk).comp hpair
  refine hmain.congr ?_
  intro y
  rfl

noncomputable def modelSharpUnionRoundingHomeo {n k : ℕ} (hk : k ≤ n) (c ε r δ : ℝ)
    (hδ0 : 0 < δ) (hδr : δ < r ^ 2) :
    {y : MorseModel n // y ∈ (sublevel (morseNormalForm hk c) (c - ε) : Set (MorseModel n)) ∪
      modelHandle hk ε r} ≃ₜ
      {y : MorseModel n // y ∈ modelAttachedRegion hk ε r δ} where
  toFun := fun y => ⟨modelSharpUnionRound hk ε r δ y.1,
    modelSharpUnionRound_mem_attached hk c ε r δ hδ0 hδr y.2⟩
  invFun := fun z => ⟨modelSharpUnionUnround hk ε r δ z.1,
    modelSharpUnionUnround_mem_sharpUnion hk c ε r δ hδ0 hδr z.2⟩
  left_inv := by
    intro z
    apply Subtype.ext
    change modelSharpUnionUnround hk ε r δ (modelSharpUnionRound hk ε r δ z.1) = z.1
    exact modelSharpUnionUnround_round hk ε r δ hδ0 hδr (y := z.1)
  right_inv := by
    intro y
    apply Subtype.ext
    change modelSharpUnionRound hk ε r δ (modelSharpUnionUnround hk ε r δ y.1) = y.1
    exact modelSharpUnionRound_unround hk ε r δ hδ0 hδr (z := y.1)
  continuous_toFun := Continuous.subtype_mk
    ((continuous_modelSharpUnionRound hk ε r δ hδ0 hδr).comp continuous_subtype_val) (by
      intro y
      exact modelSharpUnionRound_mem_attached hk c ε r δ hδ0 hδr y.2)
  continuous_invFun := Continuous.subtype_mk
    ((continuous_modelSharpUnionUnround hk ε r δ hδ0 hδr).comp continuous_subtype_val) (by
      intro z
      exact modelSharpUnionUnround_mem_sharpUnion hk c ε r δ hδ0 hδr z.2)

noncomputable def modelAttachedRegionEquivUpper {n k : ℕ} (hk : k ≤ n) (c ε r δ : ℝ)
    (hδ0 : 0 < δ) (hδr : δ < r ^ 2) (hr : r ≠ 0) :
    {y : MorseModel n // y ∈ modelAttachedRegion hk ε r δ} ≃ₜ
      {y : MorseModel n // morseNormalForm hk c y ≤ c + r ^ 2 / 2} where
  toFun := fun y => ⟨modelAttachedUnstretch hk ε r δ y.1,
    (modelAttachedStretch_equiv hk c ε r δ hδ0 hδr hr).2.1 y.1 y.2⟩
  invFun := fun z => ⟨modelAttachedStretch hk ε r δ z.1,
    (modelAttachedStretch_equiv hk c ε r δ hδ0 hδr hr).1 z.1 z.2⟩
  left_inv := by
    intro y
    apply Subtype.ext
    exact (modelAttachedStretch_equiv hk c ε r δ hδ0 hδr hr).2.2.2.1 y.1 y.2
  right_inv := by
    intro z
    apply Subtype.ext
    exact (modelAttachedStretch_equiv hk c ε r δ hδ0 hδr hr).2.2.1 z.1 z.2
  continuous_toFun := Continuous.subtype_mk
    ((modelAttachedStretch_equiv hk c ε r δ hδ0 hδr hr).2.2.2.2.2.continuous.comp
      continuous_subtype_val) (by
        intro y
        exact (modelAttachedStretch_equiv hk c ε r δ hδ0 hδr hr).2.1 y.1 y.2)
  continuous_invFun := Continuous.subtype_mk
    ((modelAttachedStretch_equiv hk c ε r δ hδ0 hδr hr).2.2.2.2.1.continuous.comp
      continuous_subtype_val) (by
        intro z
        exact (modelAttachedStretch_equiv hk c ε r δ hδ0 hδr hr).1 z.1 z.2)

noncomputable def modelSharpUnionToUpperHomeo {n k : ℕ} (hk : k ≤ n) (c ε r δ : ℝ)
    (hδ0 : 0 < δ) (hδr : δ < r ^ 2) :
    {y : MorseModel n // y ∈ (sublevel (morseNormalForm hk c) (c - ε) : Set (MorseModel n)) ∪
      modelHandle hk ε r} ≃ₜ
      {y : MorseModel n // morseNormalForm hk c y ≤ c + r ^ 2 / 2} :=
  (modelSharpUnionRoundingHomeo hk c ε r δ hδ0 hδr).trans
    (modelAttachedRegionEquivUpper hk c ε r δ hδ0 hδr (by
      intro h
      rw [h] at hδr
      nlinarith [hδ0, hδr]))

end CellAttachment

end
end DifferentialGeometry.Topology.Morse
