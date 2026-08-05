import DifferentialGeometry.Topology.Morse.Defs
import DifferentialGeometry.Topology.Morse.LocalNormalForm
import DifferentialGeometry.Topology.Attachment.Union
import Mathlib.Topology.Homotopy.Basic
import Mathlib.Topology.Homotopy.Equiv

namespace DifferentialGeometry.Topology.Morse

open Filter
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

def cellMap {n k : ℕ} (_hk : k ≤ n) (r : ℝ) (x : EuclideanSpace ℝ (Fin k)) :
    MorseModel n :=
  fun i => if h : i.val < k then r * x ⟨i.val, h⟩ else 0

theorem cellMap_negIdx {n k : ℕ} (hk : k ≤ n) (ε : ℝ)
    (x : EuclideanSpace ℝ (Fin k)) (i : Fin k) :
    cellMap hk ε x (negIdx hk i) = ε * x i := by
  dsimp [cellMap, negIdx]
  simp [i.isLt]

theorem cellMap_posIdx {n k : ℕ} (hk : k ≤ n) (ε : ℝ)
    (x : EuclideanSpace ℝ (Fin k)) (j : Fin (n - k)) :
    cellMap hk ε x (posIdx hk j) = 0 := by
  dsimp [cellMap, posIdx]
  rw [dif_neg]
  omega

theorem morseNormalForm_cellMap {n k : ℕ} (hk : k ≤ n) (c ε : ℝ)
    (x : EuclideanSpace ℝ (Fin k)) :
    morseNormalForm hk c (cellMap hk ε x) = c + (1 / 2) * (-(ε ^ 2) * ‖x‖ ^ 2) := by
  dsimp [morseNormalForm]
  have hneg : (∑ i : Fin k, - (cellMap hk ε x (negIdx hk i)) ^ 2) = -(ε ^ 2) * ‖x‖ ^ 2 := by
    calc
      (∑ i : Fin k, - (cellMap hk ε x (negIdx hk i)) ^ 2)
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
  have hpos : (∑ j : Fin (n - k), (cellMap hk ε x (posIdx hk j)) ^ 2) = 0 := by
    simp [cellMap_posIdx]
  rw [hneg, hpos]
  ring

def attachMap {n k : ℕ} (hk : k ≤ n) (c ε : ℝ) (hε : 0 ≤ ε) (x : CellBoundary k) :
    sublevel (morseNormalForm hk c) (c - ε) :=
  ⟨cellMap hk (Real.sqrt (2 * ε)) (x : EuclideanSpace ℝ (Fin k)), by
    have hnorm : ‖(x : EuclideanSpace ℝ (Fin k))‖ = 1 := x.2
    have hf : morseNormalForm hk c (cellMap hk (Real.sqrt (2 * ε)) (x : EuclideanSpace ℝ (Fin k))) =
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
    cellMap hk (Real.sqrt (2 * ε)) (x : EuclideanSpace ℝ (Fin k)) ∈
      sublevel (morseNormalForm hk c) (c + ε) := by
  change morseNormalForm hk c (cellMap hk (Real.sqrt (2 * ε)) (x : EuclideanSpace ℝ (Fin k))) ≤ c + ε
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
  -- spine = (y⁻, 0): negPart unchanged, posPart = 0
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
    spineMap hk y ∈ Set.range (fun x : ClosedCell k => cellMap hk (Real.sqrt (2 * ε)) (x : EuclideanSpace ℝ (Fin k))) := by
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
      cellMap hk (Real.sqrt (2 * ε)) (x : EuclideanSpace ℝ (Fin k)) i
          = cellMap hk (Real.sqrt (2 * ε)) (x : EuclideanSpace ℝ (Fin k)) (negIdx hk ⟨i.val, hi⟩) := by rw [← hi']
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
      cellMap hk (Real.sqrt (2 * ε)) (x : EuclideanSpace ℝ (Fin k)) i
          = cellMap hk (Real.sqrt (2 * ε)) (x : EuclideanSpace ℝ (Fin k)) (posIdx hk ⟨i.val - k, _⟩) := by rw [← hi']
      _ = 0 := cellMap_posIdx hk (Real.sqrt (2 * ε)) (x : EuclideanSpace ℝ (Fin k)) ⟨i.val - k, _⟩
      _ = recombine hk (negPart hk y) 0 (posIdx hk ⟨i.val - k, _⟩) := by
        rw [recombine_posPart]
        rfl
      _ = recombine hk (negPart hk y) 0 i := by
        exact congrArg (recombine hk (negPart hk y) 0) hi'.symm

noncomputable def lowerCellUnion {n k : ℕ} (hk : k ≤ n) (c ε : ℝ) : Set (MorseModel n) :=
  sublevel (morseNormalForm hk c) (c - ε) ∪
    Set.range (fun x : ClosedCell k => cellMap hk (Real.sqrt (2 * ε)) (x : EuclideanSpace ℝ (Fin k)))

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
  -- negPart (step) = negPart y; posPart (step) = t • posPart y
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
  -- ‖t • posPart y‖² = t² ‖posPart y‖²
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
  -- (t, y) ↦ recombine (negPart y) (t • posPart y)
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

theorem continuous_cellMap {n k : ℕ} (hk : k ≤ n) (r : ℝ) :
    Continuous (fun x : ClosedCell k => cellMap hk r (x : EuclideanSpace ℝ (Fin k))) := by
  rw [continuous_iff_continuousAt]
  intro x
  rw [continuousAt_pi]
  intro i
  by_cases hi : i.val < k
  · -- cellMap r x i = r * x i
    have hfun : (fun q : ClosedCell k => cellMap hk r (q : EuclideanSpace ℝ (Fin k)) i) =
        fun q : ClosedCell k => r * (q : EuclideanSpace ℝ (Fin k)) ⟨i.val, hi⟩ := by
      funext q
      dsimp [cellMap]
      rw [dif_pos hi]
    rw [hfun]
    exact ((continuous_const.mul (PiLp.continuous_apply (p := (2 : ENNReal)) (β := fun _ : Fin k => ℝ)
      ⟨i.val, hi⟩)).comp continuous_subtype_val).continuousAt
  · have hfun : (fun q : ClosedCell k => cellMap hk r (q : EuclideanSpace ℝ (Fin k)) i) =
      fun _ => 0 := by
      funext q
      dsimp [cellMap]
      rw [dif_neg hi]
    rw [hfun]
    exact continuous_const.continuousAt

theorem cellMap_injective {n k : ℕ} (hk : k ≤ n) (ε : ℝ) (hε : 0 < ε) :
    Function.Injective (fun x : ClosedCell k =>
      cellMap hk (Real.sqrt (2 * ε)) (x : EuclideanSpace ℝ (Fin k))) := by
  intro x y hxy
  apply Subtype.ext
  ext i
  have hx : cellMap hk (Real.sqrt (2 * ε)) (x : EuclideanSpace ℝ (Fin k)) (negIdx hk i) =
      cellMap hk (Real.sqrt (2 * ε)) (y : EuclideanSpace ℝ (Fin k)) (negIdx hk i) := by
    exact congrFun hxy (negIdx hk i)
  rw [cellMap_negIdx, cellMap_negIdx] at hx
  have hr : Real.sqrt (2 * ε) ≠ 0 := by
    exact (Real.sqrt_pos.2 (by positivity : 0 < 2 * ε)).ne'
  exact mul_left_cancel₀ hr hx

theorem cellInterior_disjoint {n k : ℕ} (hk : k ≤ n) (c ε : ℝ) (hε : 0 < ε) :
    Disjoint ((fun x : ClosedCell k => cellMap hk (Real.sqrt (2 * ε)) (x : EuclideanSpace ℝ (Fin k))) ''
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
  -- the normal form is continuous
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

noncomputable def cellAttachmentMapC {n k : ℕ} (hk : k ≤ n) (c ε : ℝ) (hε : 0 < ε) :
    C(upperSublevel hk c ε, lowerUnion hk c ε) :=
  ⟨cellAttachmentMap hk c ε hε, continuous_cellAttachmentMap hk c ε hε⟩

noncomputable def cellAttachmentInclusionC {n k : ℕ} (hk : k ≤ n) (c ε : ℝ) (hε : 0 ≤ ε) :
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
    (c := fun x : ClosedCell k => cellMap hk (Real.sqrt (2 * ε)) (x : EuclideanSpace ℝ (Fin k)))
    ?hφ ?hc ?hcont ?hinterior ?hclosed
  · intro b
    rfl
  · exact cellMap_injective hk ε hε
  · exact continuous_cellMap hk (Real.sqrt (2 * ε))
  · exact cellInterior_disjoint hk c ε hε
  · exact isClosed_sublevel_normalForm hk c (c - ε)

noncomputable def cellAttachmentModel {n k : ℕ} (hk : k ≤ n) (c ε : ℝ) (hε : 0 < ε) :
    ContinuousMap.HomotopyEquiv (upperSublevel hk c ε)
      (CellAdjunctionSpace k (attachMap hk c ε (le_of_lt hε))) :=
  (cellAttachmentHomotopyEquiv hk c ε hε).trans
    (cellAttachmentAdjunctionHomeo hk c ε hε).symm.toHomotopyEquiv

abbrev morseNorm (n : ℕ) (y : MorseModel n) : ℝ :=
  ‖(WithLp.toLp 2 y : EuclideanSpace ℝ (Fin n))‖

private theorem sum_split_fin {n k : ℕ} (hk : k ≤ n) (f : Fin n → ℝ) :
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
    (x : EuclideanSpace ℝ (Fin k)) (hx : ‖x‖ ≤ 1) : morseNorm n (cellMap hk (Real.sqrt (2 * ε)) x) ≤ R := by
  have hsq : morseNorm n (cellMap hk (Real.sqrt (2 * ε)) x) ^ 2 ≤ (Real.sqrt (2 * ε)) ^ 2 := by
    have h1 : morseNorm n (cellMap hk (Real.sqrt (2 * ε)) x) ^ 2 =
        ∑ i : Fin n, ((cellMap hk (Real.sqrt (2 * ε)) x) i) ^ 2 := by
      simpa [morseNorm] using
        (EuclideanSpace.real_norm_sq_eq (WithLp.toLp 2 (cellMap hk (Real.sqrt (2 * ε)) x)))
    rw [h1]
    rw [sum_split_fin hk (fun i : Fin n => ((cellMap hk (Real.sqrt (2 * ε)) x) i) ^ 2)]
    have hneg : (∑ i : Fin k, ((cellMap hk (Real.sqrt (2 * ε)) x) (negIdx hk i)) ^ 2) ≤
        (Real.sqrt (2 * ε)) ^ 2 * ‖x‖ ^ 2 := by
      calc
        (∑ i : Fin k, ((cellMap hk (Real.sqrt (2 * ε)) x) (negIdx hk i)) ^ 2)
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
    have hpos : (∑ j : Fin (n - k), ((cellMap hk (Real.sqrt (2 * ε)) x) (posIdx hk j)) ^ 2) = 0 := by
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
  have hnorm : morseNorm n (cellMap hk (Real.sqrt (2 * ε)) x) ≤ Real.sqrt (2 * ε) := by
    calc
      morseNorm n (cellMap hk (Real.sqrt (2 * ε)) x)
          = |morseNorm n (cellMap hk (Real.sqrt (2 * ε)) x)| := by
            rw [abs_of_nonneg (norm_nonneg _)]
      _ ≤ |Real.sqrt (2 * ε)| := sq_le_sq.mp hsq
      _ = Real.sqrt (2 * ε) := abs_of_nonneg (Real.sqrt_nonneg (2 * ε))
  exact le_trans hnorm hR

abbrev ballUpperSublevel {n k : ℕ} (hk : k ≤ n) (c ε R : ℝ) : Type :=
  {y : MorseModel n // y ∈ sublevel (morseNormalForm hk c) (c + ε) ∧ morseNorm n y ≤ R}

abbrev ballLowerUnion {n k : ℕ} (hk : k ≤ n) (c ε R : ℝ) : Type :=
  {y : MorseModel n //
    (y ∈ sublevel (morseNormalForm hk c) (c - ε) ∧ morseNorm n y ≤ R) ∨
      y ∈ Set.range (fun x : ClosedCell k => cellMap hk (Real.sqrt (2 * ε)) (x : EuclideanSpace ℝ (Fin k)))}

theorem mem_ballLowerUnion_iff {n k : ℕ} (hk : k ≤ n) (c ε R : ℝ)
    (hR : Real.sqrt (2 * ε) ≤ R) (y : MorseModel n) :
    y ∈ lowerCellUnion hk c ε ∧ morseNorm n y ≤ R ↔
      (y ∈ sublevel (morseNormalForm hk c) (c - ε) ∧ morseNorm n y ≤ R) ∨
        y ∈ Set.range (fun x : ClosedCell k => cellMap hk (Real.sqrt (2 * ε)) (x : EuclideanSpace ℝ (Fin k))) := by
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
      y ∈ Set.range (fun x : ClosedCell k => cellMap hk (Real.sqrt (2 * ε)) (x : EuclideanSpace ℝ (Fin k)))) :
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

noncomputable def ballCellAttachmentMapC {n k : ℕ} (hk : k ≤ n) (c ε R : ℝ) (hε : 0 < ε) :
    C(ballUpperSublevel hk c ε R, ballLowerUnion hk c ε R) :=
  ⟨ballCellAttachmentMap hk c ε R hε, continuous_ballCellAttachmentMap hk c ε R hε⟩

noncomputable def ballCellAttachmentInclusionC {n k : ℕ} (hk : k ≤ n) (c ε R : ℝ) (hε : 0 ≤ ε)
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
  ⟨cellMap hk (Real.sqrt (2 * ε)) (x : EuclideanSpace ℝ (Fin k)), by
    constructor
    · change morseNormalForm hk c (cellMap hk (Real.sqrt (2 * ε)) (x : EuclideanSpace ℝ (Fin k))) ≤ c - ε
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
    (c := fun x : ClosedCell k => cellMap hk (Real.sqrt (2 * ε)) (x : EuclideanSpace ℝ (Fin k)))
    ?hφ ?hc ?hcont ?hinterior ?hclosed
  · intro b
    rfl
  · exact cellMap_injective hk ε hε
  · exact continuous_cellMap hk (Real.sqrt (2 * ε))
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

end CellAttachment

end
end DifferentialGeometry.Topology.Morse
