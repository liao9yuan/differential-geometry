import DifferentialGeometry.Topology.Morse.CellAttachment
import DifferentialGeometry.Topology.Homotopy.EquivUnder
import DifferentialGeometry.Topology.Morse.Flow
import DifferentialGeometry.Topology.Morse.Manifold
import DifferentialGeometry.Topology.Morse.ModifiedFunction
import DifferentialGeometry.Topology.Morse.NoCriticalValues
import Mathlib.Topology.MetricSpace.Bounded

namespace DifferentialGeometry.Topology.Morse

open Manifold
open DifferentialGeometry.Topology
open DifferentialGeometry.Analysis.ODE
open scoped Topology Manifold ContDiff

noncomputable section

namespace ManifoldCellAttachment

open CellAttachment

private def openPartialHomeomorphSourceHomeo {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (ψ : OpenPartialHomeomorph X Y) : ψ.source ≃ₜ ψ.target :=
  { toFun := fun x => ⟨ψ x, ψ.map_source x.2⟩
    invFun := fun y => ⟨ψ.symm y, ψ.map_target y.2⟩
    left_inv := by
      intro x
      apply Subtype.ext
      exact ψ.left_inv x.2
    right_inv := by
      intro y
      apply Subtype.ext
      exact ψ.right_inv y.2
    continuous_toFun := by
      exact (Topology.IsInducing.subtypeVal.continuous_iff).2
        (continuousOn_iff_continuous_restrict.mp ψ.continuousOn_toFun)
    continuous_invFun := by
      exact (Topology.IsInducing.subtypeVal.continuous_iff).2
        (continuousOn_iff_continuous_restrict.mp ψ.continuousOn_invFun) }

private def subtypeSubtypeOfSubset {X : Type} [TopologicalSpace X] {s t : Set X} (hst : s ⊆ t) :
    {x : X // x ∈ s} ≃ₜ {x : {x : X // x ∈ t} // x.1 ∈ s} where
  toFun := fun x => ⟨⟨x.1, hst x.2⟩, x.2⟩
  invFun := fun x => ⟨x.1.1, x.2⟩
  left_inv := by intro x; rfl
  right_inv := by intro x; rfl
  continuous_toFun := by
    fun_prop
  continuous_invFun := by
    fun_prop

private def subtypeSubtypeValHomeo {X : Type} [TopologicalSpace X] {s t : Set X} (ht : t ⊆ s) :
    {x : {y : X // y ∈ s} // x.1 ∈ t} ≃ₜ {x : X // x ∈ t} where
  toFun := fun x => ⟨x.1.1, x.2⟩
  invFun := fun x => ⟨⟨x.1, ht x.2⟩, x.2⟩
  left_inv := by intro x; rfl
  right_inv := by intro x; rfl
  continuous_toFun := by
    fun_prop
  continuous_invFun := by
    fun_prop

private def homeoRestrictPred {A B : Type} [TopologicalSpace A] [TopologicalSpace B] (h : A ≃ₜ B)
    (p : A → Prop) (q : B → Prop) (hpq : ∀ a, p a ↔ q (h a)) :
    {a : A // p a} ≃ₜ {b : B // q b} where
  toFun := fun a => ⟨h a.1, (hpq a.1).1 a.2⟩
  invFun := fun b => ⟨h.symm b.1, (hpq (h.symm b.1)).2 (by
    have hb : q b.1 := b.2
    have hround : h (h.symm b.1) = b.1 := h.apply_symm_apply b.1
    simpa [hround] using hb)⟩
  left_inv := by
    intro a
    apply Subtype.ext
    exact h.symm_apply_apply a.1
  right_inv := by
    intro b
    apply Subtype.ext
    exact h.apply_symm_apply b.1
  continuous_toFun := by
    fun_prop
  continuous_invFun := by
    fun_prop

private def subtypeAndNestedHomeo {X : Type} [TopologicalSpace X] (p q : X → Prop) :
    {x : X // p x ∧ q x} ≃ₜ {x : {x : X // p x} // q x.1} where
  toFun := fun x => ⟨⟨x.1, x.2.1⟩, x.2.2⟩
  invFun := fun x => ⟨x.1.1, ⟨x.1.2, x.2⟩⟩
  left_inv := by intro x; rfl
  right_inv := by intro x; rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

private def andSwapHomeo {X : Type} [TopologicalSpace X] (p q : X → Prop) :
    {x : X // p x ∧ q x} ≃ₜ {x : X // q x ∧ p x} where
  toFun := fun x => ⟨x.1, ⟨x.2.2, x.2.1⟩⟩
  invFun := fun x => ⟨x.1, ⟨x.2.2, x.2.1⟩⟩
  left_inv := by intro x; rfl
  right_inv := by intro x; rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

private def subtypeSetHomeo {X : Type} [TopologicalSpace X] {s t : Set X} (h : s = t) :
    {x : X // x ∈ s} ≃ₜ {x : X // x ∈ t} where
  toFun := fun x => ⟨x.1, by rw [← h]; exact x.2⟩
  invFun := fun x => ⟨x.1, by rw [h]; exact x.2⟩
  left_inv := by intro x; rfl
  right_inv := by intro x; rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop


structure MorseChart (n k : ℕ) (hk : k ≤ n) (c : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    (I : ModelWithCorners ℝ (MorseModel n) H) (f : M → ℝ) where
  p : M
  R : ℝ
  R' : ℝ
  ε : ℝ
  χ : OpenPartialHomeomorph (MorseModel n) M
  hχ0 : χ 0 = p
  hRpos : 0 < R
  hR'pos : 0 < R'
  hεpos : 0 < ε
  hεR : Real.sqrt (2 * ε) ≤ R
  hnorm : ∀ y : MorseModel n, morseNorm n y ≤ R → f (χ y) = morseNormalForm hk c y
  hχsrc : ∀ y : MorseModel n, morseNorm n y ≤ R → y ∈ χ.source
  hχon : ContMDiffOn 𝓘(ℝ, MorseModel n) I (↑(⊤ : ℕ∞) : WithTop ℕ∞) χ
    (Metric.ball (0 : MorseModel n) R')
  hχsymmOn : ContMDiffOn I 𝓘(ℝ, MorseModel n) (↑(⊤ : ℕ∞) : WithTop ℕ∞) χ.symm
    (χ '' Metric.ball (0 : MorseModel n) R')

noncomputable def morseChart {n : ℕ} {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M]
    [ChartedSpace H M] (I : ModelWithCorners ℝ (MorseModel n) H) [I.Boundaryless]
    [IsManifold I (⊤ : WithTop ℕ∞) M] (f : M → ℝ) (hf : ContMDiff I 𝓘(ℝ, ℝ) (⊤ : WithTop ℕ∞) f)
    (p : M) (c : ℝ) (k : ℕ) (hk : k ≤ n)
    (hnd : IsNondegenerateCriticalPointAt I f p)
    (hindex : sigNeg (chartHessianAt (g := fun y => f ((extChartAt I p).symm y)) (extChartAt I p p)) = k)
    (hfp : f p = c) : MorseChart n k hk c I f := by
  let hdata := morse_lemma I f hf p k hk hnd hindex
  let R : ℝ := Classical.choose hdata
  have hR : 0 < R ∧ ∃ χ : OpenPartialHomeomorph (MorseModel n) M,
      (0 : MorseModel n) ∈ χ.source ∧ p ∈ χ.target ∧ χ 0 = p ∧
      (∀ y : MorseModel n, morseNorm n y ≤ R → y ∈ χ.source) ∧
      (∀ y : MorseModel n, morseNorm n y ≤ R → f (χ y) = morseNormalForm hk (f p) y) ∧
      ContMDiffAt 𝓘(ℝ, MorseModel n) I (↑(⊤ : ℕ∞) : WithTop ℕ∞) χ 0 ∧
      ContMDiffAt I 𝓘(ℝ, MorseModel n) (↑(⊤ : ℕ∞) : WithTop ℕ∞) χ.symm p ∧
      ∃ R' : ℝ, 0 < R' ∧
        ContMDiffOn 𝓘(ℝ, MorseModel n) I (↑(⊤ : ℕ∞) : WithTop ℕ∞) χ (Metric.ball (0 : MorseModel n) R') ∧
        ContMDiffOn I 𝓘(ℝ, MorseModel n) (↑(⊤ : ℕ∞) : WithTop ℕ∞) χ.symm
          (χ '' Metric.ball (0 : MorseModel n) R') := Classical.choose_spec hdata
  rcases hR with ⟨hRpos, hχ⟩
  let χ : OpenPartialHomeomorph (MorseModel n) M := Classical.choose hχ
  have hχspec : (0 : MorseModel n) ∈ χ.source ∧ p ∈ χ.target ∧ χ 0 = p ∧
      (∀ y : MorseModel n, morseNorm n y ≤ R → y ∈ χ.source) ∧
      (∀ y : MorseModel n, morseNorm n y ≤ R → f (χ y) = morseNormalForm hk (f p) y) ∧
      ContMDiffAt 𝓘(ℝ, MorseModel n) I (↑(⊤ : ℕ∞) : WithTop ℕ∞) χ 0 ∧
      ContMDiffAt I 𝓘(ℝ, MorseModel n) (↑(⊤ : ℕ∞) : WithTop ℕ∞) χ.symm p ∧
      ∃ R' : ℝ, 0 < R' ∧
        ContMDiffOn 𝓘(ℝ, MorseModel n) I (↑(⊤ : ℕ∞) : WithTop ℕ∞) χ (Metric.ball (0 : MorseModel n) R') ∧
        ContMDiffOn I 𝓘(ℝ, MorseModel n) (↑(⊤ : ℕ∞) : WithTop ℕ∞) χ.symm
          (χ '' Metric.ball (0 : MorseModel n) R') := Classical.choose_spec hχ
  rcases hχspec with ⟨hχ0src, hχ0tgt, hχ0val, hχsrc, hnorm0, hχmd, hχsmd, htail⟩
  let R' : ℝ := Classical.choose htail
  have hR'tail : 0 < R' ∧
      ContMDiffOn 𝓘(ℝ, MorseModel n) I (↑(⊤ : ℕ∞) : WithTop ℕ∞) χ (Metric.ball (0 : MorseModel n) R') ∧
      ContMDiffOn I 𝓘(ℝ, MorseModel n) (↑(⊤ : ℕ∞) : WithTop ℕ∞) χ.symm
        (χ '' Metric.ball (0 : MorseModel n) R') := Classical.choose_spec htail
  rcases hR'tail with ⟨hR'pos, hχon, hχsymmOn⟩
  have hnorm : ∀ y : MorseModel n, morseNorm n y ≤ R → f (χ y) = morseNormalForm hk c y := by
    intro y hy
    rw [← hfp]
    exact hnorm0 y hy
  let ε : ℝ := R ^ 2 / 4
  have hεpos : 0 < ε := by dsimp [ε]; positivity
  have hεR : Real.sqrt (2 * ε) ≤ R := by
    dsimp [ε]
    have hRnonneg : 0 ≤ R := le_of_lt hRpos
    have hsq : (Real.sqrt (2 * (R ^ 2 / 4))) ^ 2 ≤ R ^ 2 := by
      rw [Real.sq_sqrt (by positivity : 0 ≤ 2 * (R ^ 2 / 4))]
      ring_nf
      nlinarith [sq_nonneg R]
    have habs := sq_le_sq.mp hsq
    calc
      Real.sqrt (2 * (R ^ 2 / 4)) = |Real.sqrt (2 * (R ^ 2 / 4))| :=
        (abs_of_nonneg (Real.sqrt_nonneg _)).symm
      _ ≤ |R| := habs
      _ = R := abs_of_nonneg hRnonneg
  exact MorseChart.mk p R R' ε χ hχ0val hRpos hR'pos hεpos hεR hnorm hχsrc hχon hχsymmOn

def cellEmbedding {n k : ℕ} (hk : k ≤ n) (c : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ (MorseModel n) H} {f : M → ℝ}
    (data : MorseChart n k hk c I f) : ClosedCell k → M :=
  fun x => data.χ (cellMap (Real.sqrt (2 * data.ε)) (x : EuclideanSpace ℝ (Fin k)))

def cellImage {n k : ℕ} (hk : k ≤ n) (c : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ (MorseModel n) H} {f : M → ℝ}
    (data : MorseChart n k hk c I f) : Set M :=
  Set.range (cellEmbedding hk c data)

def cellAttachingMap {n k : ℕ} (hk : k ≤ n) (c : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ (MorseModel n) H} {f : M → ℝ}
    (data : MorseChart n k hk c I f) :
    C(CellBoundary k, {x : M // x ∈ sublevel f (c - data.ε)}) :=
  ContinuousMap.mk (fun b => ⟨data.χ (cellMap (Real.sqrt (2 * data.ε)) (b : EuclideanSpace ℝ (Fin k))), by
    change f (data.χ (cellMap (Real.sqrt (2 * data.ε)) (b : EuclideanSpace ℝ (Fin k)))) ≤ c - data.ε
    have hn := data.hnorm (cellMap (Real.sqrt (2 * data.ε)) (b : EuclideanSpace ℝ (Fin k))) (by
      exact norm_cellMap_le hk data.ε data.R data.hεR (b : EuclideanSpace ℝ (Fin k)) (le_of_eq b.2))
    rw [hn]
    have hf := morseNormalForm_cellMap hk c (Real.sqrt (2 * data.ε)) (b : EuclideanSpace ℝ (Fin k))
    rw [hf]
    have hnorm1 : ‖(b : EuclideanSpace ℝ (Fin k))‖ = 1 := b.2
    have hsq : (Real.sqrt (2 * data.ε)) ^ 2 = 2 * data.ε := by
      rw [Real.sq_sqrt (by exact mul_nonneg (by norm_num) (le_of_lt data.hεpos))]
    rw [hsq, hnorm1]
    linarith⟩) (by
    have hcellCont : Continuous (fun b : CellBoundary k =>
        (cellMap (Real.sqrt (2 * data.ε)) (b : EuclideanSpace ℝ (Fin k)) : MorseModel n)) := by
      have hbcont : Continuous (cellBoundaryInclusion k) := by
        exact Continuous.subtype_mk continuous_subtype_val (by intro x; exact le_of_eq x.2)
      have hcell' : Continuous (fun x : ClosedCell k =>
          (cellMap (Real.sqrt (2 * data.ε)) (x : EuclideanSpace ℝ (Fin k)) : MorseModel n)) :=
        continuous_cellMap (Real.sqrt (2 * data.ε))
      have hcomp := hcell'.comp hbcont
      simpa using hcomp
    have hmap : Set.MapsTo (fun b : CellBoundary k =>
        (cellMap (Real.sqrt (2 * data.ε)) (b : EuclideanSpace ℝ (Fin k)) : MorseModel n))
        Set.univ data.χ.source := by
      intro b hb
      exact data.hχsrc (cellMap (Real.sqrt (2 * data.ε)) (b : EuclideanSpace ℝ (Fin k))) (by
        exact norm_cellMap_le hk data.ε data.R data.hεR (b : EuclideanSpace ℝ (Fin k)) (le_of_eq b.2))
    have hχcont : ContinuousOn data.χ ((fun b : CellBoundary k =>
        (cellMap (Real.sqrt (2 * data.ε)) (b : EuclideanSpace ℝ (Fin k)) : MorseModel n)) '' Set.univ) :=
      data.χ.continuousOn_toFun.mono (by
        intro z hz
        rcases hz with ⟨b, hb, hbz⟩
        rw [← hbz]
        exact hmap trivial)
    have hcont : Continuous (fun b : CellBoundary k =>
        data.χ (cellMap (Real.sqrt (2 * data.ε)) (b : EuclideanSpace ℝ (Fin k)))) := by
      have hstep := ContinuousOn.comp' hχcont hcellCont.continuousOn (Set.mapsTo_image
        (fun b : CellBoundary k =>
          (cellMap (Real.sqrt (2 * data.ε)) (b : EuclideanSpace ℝ (Fin k)) : MorseModel n))
        Set.univ)
      exact (continuousOn_univ.mp hstep)
    exact Continuous.subtype_mk hcont (by
      intro b
      change f (data.χ (cellMap (Real.sqrt (2 * data.ε)) (b : EuclideanSpace ℝ (Fin k)))) ≤ c - data.ε
      have hn := data.hnorm (cellMap (Real.sqrt (2 * data.ε)) (b : EuclideanSpace ℝ (Fin k))) (by
        exact norm_cellMap_le hk data.ε data.R data.hεR (b : EuclideanSpace ℝ (Fin k)) (le_of_eq b.2))
      rw [hn]
      have hf := morseNormalForm_cellMap hk c (Real.sqrt (2 * data.ε)) (b : EuclideanSpace ℝ (Fin k))
      rw [hf]
      have hnorm1 : ‖(b : EuclideanSpace ℝ (Fin k))‖ = 1 := b.2
      have hsq : (Real.sqrt (2 * data.ε)) ^ 2 = 2 * data.ε := by
        rw [Real.sq_sqrt (by exact mul_nonneg (by norm_num) (le_of_lt data.hεpos))]
      rw [hsq, hnorm1]
      linarith))

noncomputable def cellAdjunctionSpaceHomeomorphLowerUnion {n : ℕ} {H : Type}
    [TopologicalSpace H] {M : Type} [TopologicalSpace M]
    [ChartedSpace H M] [T2Space M] (I : ModelWithCorners ℝ (MorseModel n) H) [I.Boundaryless]
    [IsManifold I (⊤ : WithTop ℕ∞) M] (f : M → ℝ) (hf : ContMDiff I 𝓘(ℝ, ℝ) (⊤ : WithTop ℕ∞) f)
    (c : ℝ) (k : ℕ) (hk : k ≤ n)
    (data : MorseChart n k hk c I f) :
    CellAdjunctionSpace k (cellAttachingMap hk c data) ≃ₜ
      {x : M // x ∈ sublevel f (c - data.ε) ∪ cellImage hk c data} := by
  let E : Set M := cellImage hk c data
  let c' : ClosedCell k → M := cellEmbedding hk c data
  let φ : CellBoundary k → {x : M // x ∈ sublevel f (c - data.ε)} := cellAttachingMap hk c data
  have hAdj : CellAdjunctionSpace k φ ≃ₜ
      {x : M // x ∈ sublevel f (c - data.ε) ∪ Set.range c'} := by
    refine cellAdjunctionHomeomorphUnionImage (n := k) (φ := φ) (c := c') ?hφ ?hc ?hcont ?hinterior ?hclosed
    · intro b
      rfl
    · intro x y hxy
      have hx : cellMap (Real.sqrt (2 * data.ε)) (x : EuclideanSpace ℝ (Fin k)) ∈
          {y : MorseModel n | morseNorm n y ≤ data.R} := by
        exact norm_cellMap_le hk data.ε data.R data.hεR (x : EuclideanSpace ℝ (Fin k)) x.2
      have hy : cellMap (Real.sqrt (2 * data.ε)) (y : EuclideanSpace ℝ (Fin k)) ∈
          {y : MorseModel n | morseNorm n y ≤ data.R} := by
        exact norm_cellMap_le hk data.ε data.R data.hεR (y : EuclideanSpace ℝ (Fin k)) y.2
      have hχ : (cellMap (Real.sqrt (2 * data.ε)) (x : EuclideanSpace ℝ (Fin k)) : MorseModel n) =
          (cellMap (Real.sqrt (2 * data.ε)) (y : EuclideanSpace ℝ (Fin k)) : MorseModel n) := by
        exact data.χ.injOn (data.hχsrc _ hx) (data.hχsrc _ hy) (by
          simpa [c', cellEmbedding] using hxy)
      exact cellMap_injective hk data.ε data.hεpos hχ
    · have hc'cont : Continuous (fun x : ClosedCell k =>
          (cellMap (Real.sqrt (2 * data.ε)) (x : EuclideanSpace ℝ (Fin k)) : MorseModel n)) :=
        continuous_cellMap (Real.sqrt (2 * data.ε))
      have hmap : Set.MapsTo (fun x : ClosedCell k =>
          cellMap (Real.sqrt (2 * data.ε)) (x : EuclideanSpace ℝ (Fin k))) Set.univ data.χ.source := by
        intro x hx
        exact data.hχsrc (cellMap (Real.sqrt (2 * data.ε)) (x : EuclideanSpace ℝ (Fin k)))
          (norm_cellMap_le hk data.ε data.R data.hεR (x : EuclideanSpace ℝ (Fin k)) x.2)
      have hcont : ContinuousOn (fun x : ClosedCell k =>
          data.χ (cellMap (Real.sqrt (2 * data.ε)) (x : EuclideanSpace ℝ (Fin k)))) Set.univ :=
        data.χ.continuousOn_toFun.comp hc'cont.continuousOn hmap
      change Continuous (fun x : ClosedCell k =>
        data.χ (cellMap (Real.sqrt (2 * data.ε)) (x : EuclideanSpace ℝ (Fin k))))
      exact (continuousOn_univ.mp hcont)
    · rw [Set.disjoint_left]
      intro x hxA hxB
      rcases hxA with ⟨y, hy, hxy⟩
      rcases hy with ⟨z, hz⟩
      have hfz : f x ≤ c - data.ε := by simpa [sublevel] using hxB
      have hxeq : x = data.χ (cellMap (Real.sqrt (2 * data.ε)) (z : EuclideanSpace ℝ (Fin k))) := by
        rw [← hxy]
        have hzval : (y : EuclideanSpace ℝ (Fin k)) = (z : EuclideanSpace ℝ (Fin k)) := by
          simpa [cellInteriorInclusion] using
            (congrArg (fun w : ClosedCell k => (w : EuclideanSpace ℝ (Fin k))) hz).symm
        dsimp [c', cellEmbedding]
        simp [hzval]
      have hfz' : f x = morseNormalForm hk c (cellMap (Real.sqrt (2 * data.ε)) (z : EuclideanSpace ℝ (Fin k))) := by
        rw [hxeq]
        rw [data.hnorm (cellMap (Real.sqrt (2 * data.ε)) (z : EuclideanSpace ℝ (Fin k))) (by
          exact norm_cellMap_le hk data.ε data.R data.hεR (z : EuclideanSpace ℝ (Fin k)) (le_of_lt z.2))]
      have hnot : ¬ morseNormalForm hk c (cellMap (Real.sqrt (2 * data.ε)) (z : EuclideanSpace ℝ (Fin k))) ≤
          c - data.ε := by
        intro hn
        have hmem : (cellMap (Real.sqrt (2 * data.ε)) (z : EuclideanSpace ℝ (Fin k)) : MorseModel n) ∈
            (fun x : ClosedCell k => (cellMap (Real.sqrt (2 * data.ε)) (x : EuclideanSpace ℝ (Fin k)) : MorseModel n)) ''
              Set.range (cellInteriorInclusion k) := by
          refine ⟨cellInteriorInclusion k z, ?_, rfl⟩
          exact Set.mem_range.mpr ⟨z, rfl⟩
        exact (Set.disjoint_left.mp (cellInterior_disjoint hk c data.ε data.hεpos)) hmem hn
      exact hnot (by rw [← hfz']; exact hfz)
    · exact isClosed_Iic.preimage hf.continuous
  exact hAdj

open Classical in
def morseModifiedFunction {n k : ℕ} (hk : k ≤ n) (c ε δ R : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    (χ : OpenPartialHomeomorph (MorseModel n) M) (f : M → ℝ) (x : M) : ℝ :=
  if x ∈ χ.target then
    if χ.symm x ∈ {y : MorseModel n | morseNorm n y ≤ R} then
      modifiedNormalForm hk c ε δ (χ.symm x)
    else f x
  else f x

private lemma continuousOn_morseModifiedChartRep {n : ℕ} {H : Type} [TopologicalSpace H]
    {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    (χ : OpenPartialHomeomorph (MorseModel n) M) :
    ContinuousOn (fun x : M => morseNorm n (χ.symm x)) χ.target := by
  have hnorm : Continuous (fun y : MorseModel n => morseNorm n y) := by
    dsimp [morseNorm]
    exact continuous_norm.comp (PiLp.continuous_toLp (p := (2 : ENNReal)) (β := fun _ : Fin n => ℝ))
  simpa [Function.comp_def] using
    (ContinuousOn.comp (hnorm.continuousOn : ContinuousOn (fun y : MorseModel n => morseNorm n y) Set.univ)
      χ.continuousOn_invFun (by intro x hx; trivial))

private lemma isOpen_morseModifiedRegion_lt {n : ℕ} {H : Type} [TopologicalSpace H]
    {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    (χ : OpenPartialHomeomorph (MorseModel n) M) (a : ℝ) :
    IsOpen {x : M | x ∈ χ.target ∧ morseNorm n (χ.symm x) < a} := by
  have hset : {x : M | x ∈ χ.target ∧ morseNorm n (χ.symm x) < a} =
      χ.target ∩ (fun x : M => morseNorm n (χ.symm x)) ⁻¹' {y : ℝ | y < a} := by
    ext x
    simp
  rw [hset]
  exact (continuousOn_morseModifiedChartRep (H := H) χ).isOpen_inter_preimage χ.open_target
    (isOpen_lt continuous_id continuous_const)

private lemma isOpen_morseModifiedRegion_gt {n : ℕ} {H : Type} [TopologicalSpace H]
    {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    (χ : OpenPartialHomeomorph (MorseModel n) M) (a : ℝ) :
    IsOpen {x : M | x ∈ χ.target ∧ a < morseNorm n (χ.symm x) ^ 2} := by
  have hset : {x : M | x ∈ χ.target ∧ a < morseNorm n (χ.symm x) ^ 2} =
      χ.target ∩ (fun x : M => morseNorm n (χ.symm x) ^ 2) ⁻¹' {y : ℝ | a < y} := by
    ext x
    simp
  rw [hset]
  have hcontSq : ContinuousOn (fun x : M => morseNorm n (χ.symm x) ^ 2) χ.target := by
    have hc := continuousOn_morseModifiedChartRep (H := H) χ
    simpa [pow_two] using (ContinuousOn.mul hc hc)
  exact hcontSq.isOpen_inter_preimage χ.open_target (isOpen_lt continuous_const continuous_id)

theorem contMDiff_morseModifiedFunction {n k : ℕ} (hk : k ≤ n) (c ε δ R rΦ : ℝ)
    (hε : 0 < ε) (hδ : 0 < δ) (hR : 4 * ε + 9 * δ ^ 2 / 4 < R ^ 2)
    (hΦr : 4 * ε + 9 * δ ^ 2 / 4 < rΦ ^ 2) (hRpos : 0 < R) (hΦpos : 0 < rΦ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    (I : ModelWithCorners ℝ (MorseModel n) H) [I.Boundaryless]
    [IsManifold I (⊤ : WithTop ℕ∞) M] [T2Space M] (f : M → ℝ)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) (⊤ : WithTop ℕ∞) f)
    (χ : OpenPartialHomeomorph (MorseModel n) M)
    (hnorm : ∀ y : MorseModel n, morseNorm n y ≤ R → f (χ y) = morseNormalForm hk c y)
    (hχsrc : ∀ y : MorseModel n, morseNorm n y ≤ R → y ∈ χ.source)
    (hχsymmOn : ContMDiffOn I 𝓘(ℝ, MorseModel n) (↑(⊤ : ℕ∞) : WithTop ℕ∞) χ.symm
      (χ '' Metric.ball (0 : MorseModel n) rΦ)) :
    ContMDiff I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (morseModifiedFunction (H := H) (M := M) hk c ε δ R χ f) := by
  let g : M → ℝ := morseModifiedFunction (H := H) (M := M) hk c ε δ R χ f
  let ball : Set (MorseModel n) := {y : MorseModel n | morseNorm n y ≤ R}
  have hballComp : IsCompact ball := by
    have hclosed : IsClosed ball := by
      have hcont : Continuous (fun y : MorseModel n => morseNorm n y) := by
        simpa [ball, morseNorm] using
          (continuous_norm.comp (PiLp.continuous_toLp (p := (2 : ENNReal)) (β := fun _ : Fin n => ℝ)))
      have hpre : IsClosed ((fun y : MorseModel n => morseNorm n y) ⁻¹' Set.Iic R) :=
        by simpa using (hcont.continuousOn.preimage_isClosed_of_isClosed isClosed_univ isClosed_Iic)
      simpa [ball] using hpre
    have hbounded : Bornology.IsBounded ball := by
      rw [Metric.isBounded_iff]
      refine ⟨2 * R, ?_⟩
      intro x hx y hy
      have hx' : ‖x‖ ≤ R := le_trans (supNorm_le_morseNorm x) hx
      have hy' : ‖y‖ ≤ R := le_trans (supNorm_le_morseNorm y) hy
      rw [dist_eq_norm]
      exact le_trans (norm_sub_le x y) (by nlinarith [hx', hy'])
    exact Metric.isCompact_iff_isClosed_bounded.2 ⟨hclosed, hbounded⟩
  have hχballClosed : IsClosed (χ '' ball) := by
    have hmap : Set.MapsTo χ ball χ.target := by intro y hy; exact χ.map_source (hχsrc y hy)
    have hcont : ContinuousOn χ ball := χ.continuousOn_toFun.mono hχsrc
    exact (hballComp.image_of_continuousOn hcont).isClosed
  classical
  have hfInfty : ContMDiff I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) f :=
    hf.of_le (le_top : (↑(⊤ : ℕ∞) : WithTop ℕ∞) ≤ (⊤ : WithTop ℕ∞))
  intro x
  by_cases hx : x ∈ χ.target
  · by_cases hball : morseNorm n (χ.symm x) < min R rΦ
    · have hy : χ.symm x ∈ Metric.ball (0 : MorseModel n) rΦ := by
        have hlt : morseNorm n (χ.symm x) < rΦ := lt_of_lt_of_le hball (min_le_right R rΦ)
        have hsup : ‖χ.symm x‖ ≤ morseNorm n (χ.symm x) := supNorm_le_morseNorm (χ.symm x)
        rw [Metric.mem_ball, dist_zero_right]
        exact lt_of_le_of_lt hsup hlt
      have hxball : x ∈ χ '' Metric.ball (0 : MorseModel n) rΦ := by
        refine ⟨χ.symm x, hy, ?_⟩
        exact χ.right_inv hx
      have hmdAt : ContMDiffAt I 𝓘(ℝ, MorseModel n) (↑(⊤ : ℕ∞) : WithTop ℕ∞) χ.symm x := by
        have hopen : IsOpen (χ '' (Metric.ball (0 : MorseModel n) rΦ ∩ χ.source)) := by
          exact χ.isOpen_image_of_subset_source (IsOpen.inter Metric.isOpen_ball χ.open_source)
            (by intro y hy; exact hy.2)
        have hpre : χ.symm x ∈ Metric.ball (0 : MorseModel n) rΦ ∩ χ.source :=
          ⟨hy, χ.map_target hx⟩
        have hxball' : x ∈ χ '' (Metric.ball (0 : MorseModel n) rΦ ∩ χ.source) :=
          ⟨χ.symm x, hpre, χ.right_inv hx⟩
        have hballNhds : χ '' Metric.ball (0 : MorseModel n) rΦ ∈ nhds x :=
          Filter.mem_of_superset (hopen.mem_nhds hxball') (by
            intro z hz
            exact Set.image_mono (by intro y hy; exact hy.1) hz)
        exact (hχsymmOn x hxball).contMDiffAt hballNhds
      have hmdModified : ContMDiffAt I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
          (fun z : M => modifiedNormalForm hk c ε δ (χ.symm z)) x := by
        have hgAt : ContMDiffAt 𝓘(ℝ, MorseModel n) 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
            (modifiedNormalForm hk c ε δ) (χ.symm x) :=
          (contDiff_modifiedNormalForm hk c ε δ hδ).contMDiff.contMDiffAt
        exact ContMDiffAt.comp (x := x) (g := modifiedNormalForm hk c ε δ) (f := χ.symm)
          (hg := hgAt) (hf := hmdAt)
      have hS₁mem : {x : M | x ∈ χ.target ∧ morseNorm n (χ.symm x) < min R rΦ} ∈ nhds x :=
        (isOpen_morseModifiedRegion_lt (H := H) χ (min R rΦ)).mem_nhds ⟨hx, hball⟩
      have hagree : g =ᶠ[nhds x] (fun z : M => modifiedNormalForm hk c ε δ (χ.symm z)) := by
        refine Filter.eventuallyEq_of_mem hS₁mem ?_
        intro z hz
        dsimp [g, morseModifiedFunction]
        rw [if_pos hz.1]
        have hle : morseNorm n (χ.symm z) ≤ R := le_of_lt (lt_of_lt_of_le hz.2 (min_le_left R rΦ))
        rw [if_pos hle]
      exact (ContMDiffAt.congr_of_eventuallyEq hmdModified hagree)
    · have hmin_nonneg : 0 ≤ min R rΦ := le_min (le_of_lt hRpos) (le_of_lt hΦpos)
      have hge : min R rΦ ≤ morseNorm n (χ.symm x) := le_of_not_gt hball
      have hge' : min (R ^ 2) (rΦ ^ 2) ≤ morseNorm n (χ.symm x) ^ 2 := by
        have hsq : (min R rΦ) ^ 2 ≤ morseNorm n (χ.symm x) ^ 2 := by
          simpa [pow_two] using (mul_self_le_mul_self hmin_nonneg hge)
        have hmin_sq : min (R ^ 2) (rΦ ^ 2) ≤ (min R rΦ) ^ 2 := by
          by_cases hr : R ≤ rΦ
          · rw [min_eq_left hr, min_eq_left (sq_le_sq.mpr (by
              have h1 : |R| = R := abs_of_nonneg (le_of_lt hRpos)
              have h2 : |rΦ| = rΦ := abs_of_nonneg (le_of_lt hΦpos)
              rw [h1, h2]
              exact hr))]
          · have hlt : rΦ < R := lt_of_not_ge hr
            rw [min_eq_right (sq_le_sq.mpr (by
              have h1 : |rΦ| = rΦ := abs_of_nonneg (le_of_lt hΦpos)
              have h2 : |R| = R := abs_of_nonneg (le_of_lt hRpos)
              rw [h1, h2]
              exact le_of_lt hlt)), min_eq_right (le_of_lt hlt)]
        exact le_trans hmin_sq hsq
      have hthr : 4 * ε + 9 * δ ^ 2 / 4 < min (R ^ 2) (rΦ ^ 2) := by
        exact lt_min (by nlinarith [hR]) (by nlinarith [hΦr])
      have hgt : 4 * ε + 9 * δ ^ 2 / 4 < morseNorm n (χ.symm x) ^ 2 := by
        nlinarith [hthr, hge']
      have hS₂mem : {x : M | x ∈ χ.target ∧ 4 * ε + 9 * δ ^ 2 / 4 < morseNorm n (χ.symm x) ^ 2} ∈ nhds x :=
        (isOpen_morseModifiedRegion_gt (H := H) χ (4 * ε + 9 * δ ^ 2 / 4)).mem_nhds ⟨hx, hgt⟩
      have hagree : g =ᶠ[nhds x] f := by
        refine Filter.eventuallyEq_of_mem hS₂mem ?_
        intro z hz
        dsimp [g, morseModifiedFunction]
        rw [if_pos hz.1]
        by_cases hle : morseNorm n (χ.symm z) ≤ R
        · rw [if_pos hle]
          have hmod : modifiedNormalForm hk c ε δ (χ.symm z) = morseNormalForm hk c (χ.symm z) :=
            modifiedNormalForm_eq_of_modulation_zero hk c ε δ
              (modMu_mul_modGamma_eq_zero_of_norm_gt hk ε δ hε hδ hz.2)
          rw [hmod]
          simpa [χ.right_inv hz.1] using (hnorm (χ.symm z) hle).symm
        · rw [if_neg hle]
      exact (ContMDiffAt.congr_of_eventuallyEq (hfInfty x) hagree)
  · have houtside : {x : M | x ∉ χ '' ball} ∈ nhds x := by
      exact (isOpen_compl_iff.mpr hχballClosed).mem_nhds (by
        intro hxmem
        rcases hxmem with ⟨y, hy, hyx⟩
        exact hx (by
          have : y ∈ χ.source := hχsrc y hy
          rw [← hyx]
          exact χ.map_source this))
    have hagree : g =ᶠ[nhds x] f := by
      refine Filter.eventuallyEq_of_mem houtside ?_
      intro z hz
      dsimp [g, morseModifiedFunction]
      by_cases hzt : z ∈ χ.target
      · rw [if_pos hzt]
        have hle' : ¬ morseNorm n (χ.symm z) ≤ R := by
          intro hle
          apply hz
          exact ⟨χ.symm z, hle, χ.right_inv hzt⟩
        rw [if_neg hle']
      · rw [if_neg hzt]
    exact (ContMDiffAt.congr_of_eventuallyEq (hfInfty x) hagree)

theorem sublevel_upper_identity_morseModifiedFunction {n k : ℕ} (hk : k ≤ n) (c ε δ R : ℝ)
    (hε : 0 < ε) (hδ : 0 < δ) (hδε : 9 * δ ^ 2 < 4 * ε)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    (χ : OpenPartialHomeomorph (MorseModel n) M) (f : M → ℝ)
    (hnorm : ∀ y : MorseModel n, morseNorm n y ≤ R → f (χ y) = morseNormalForm hk c y) :
    {x : M | morseModifiedFunction (H := H) (M := M) hk c ε δ R χ f x ≤ c + ε} =
      sublevel f (c + ε) := by
  ext x
  constructor
  · intro hx
    by_cases hxt : x ∈ χ.target
    · by_cases hb : morseNorm n (χ.symm x) ≤ R
      · have hg : morseModifiedFunction (H := H) (M := M) hk c ε δ R χ f x =
            modifiedNormalForm hk c ε δ (χ.symm x) := by
          simp [morseModifiedFunction, hxt, hb]
        have hmod : modifiedNormalForm hk c ε δ (χ.symm x) ≤ c + ε := by
          rw [← hg]
          exact hx
        have hup := modifiedNormalForm_sublevel_upper hk c ε δ hε hδ hδε
        have hf : morseNormalForm hk c (χ.symm x) ≤ c + ε := (Set.ext_iff.mp hup (χ.symm x)).1 hmod
        change f x ≤ c + ε
        rw [← χ.right_inv hxt]
        rw [hnorm (χ.symm x) hb]
        exact hf
      · change f x ≤ c + ε
        simpa [morseModifiedFunction, hxt, hb] using hx
    · change f x ≤ c + ε
      simpa [morseModifiedFunction, hxt] using hx
  · intro hx
    by_cases hxt : x ∈ χ.target
    · by_cases hb : morseNorm n (χ.symm x) ≤ R
      · dsimp [morseModifiedFunction]
        rw [if_pos hxt, if_pos hb]
        exact le_trans (modifiedNormalForm_le_f hk c ε δ hε (χ.symm x)) (by
          rw [← hnorm (χ.symm x) hb]
          rw [χ.right_inv hxt]
          exact hx)
      · dsimp [morseModifiedFunction]
        rw [if_pos hxt, if_neg hb]
        exact hx
    · dsimp [morseModifiedFunction]
      rw [if_neg hxt]
      exact hx

private lemma isClosed_chartBallImage {n : ℕ} {H : Type} [TopologicalSpace H] {M : Type}
    [TopologicalSpace M] [T2Space M] (χ : OpenPartialHomeomorph (MorseModel n) M) (R : ℝ)
    (hχsrc : ∀ y : MorseModel n, morseNorm n y ≤ R → y ∈ χ.source) :
    IsClosed (χ '' {y : MorseModel n | morseNorm n y ≤ R}) := by
  let ball : Set (MorseModel n) := {y : MorseModel n | morseNorm n y ≤ R}
  have hclosed : IsClosed ball := by
    have hcont : Continuous (fun y : MorseModel n => morseNorm n y) := by
      simpa [ball, morseNorm] using
        (continuous_norm.comp (PiLp.continuous_toLp (p := (2 : ENNReal)) (β := fun _ : Fin n => ℝ)))
    have hpre : IsClosed ((fun y : MorseModel n => morseNorm n y) ⁻¹' Set.Iic R) :=
      by simpa using (hcont.continuousOn.preimage_isClosed_of_isClosed isClosed_univ isClosed_Iic)
    simpa [ball] using hpre
  have hbounded : Bornology.IsBounded ball := by
    rw [Metric.isBounded_iff]
    refine ⟨2 * R, ?_⟩
    intro x hx y hy
    have hx' : ‖x‖ ≤ R := le_trans (supNorm_le_morseNorm x) hx
    have hy' : ‖y‖ ≤ R := le_trans (supNorm_le_morseNorm y) hy
    rw [dist_eq_norm]
    exact le_trans (norm_sub_le x y) (by nlinarith [hx', hy'])
  have hballComp : IsCompact ball := Metric.isCompact_iff_isClosed_bounded.2 ⟨hclosed, hbounded⟩
  have hmap : Set.MapsTo χ ball χ.target := by intro y hy; exact χ.map_source (hχsrc y hy)
  have hcont : ContinuousOn χ ball := χ.continuousOn_toFun.mono hχsrc
  exact (hballComp.image_of_continuousOn hcont).isClosed

theorem morseModifiedFunction_le_f {n k : ℕ} (hk : k ≤ n) (c ε δ R : ℝ) (hε : 0 < ε)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    (χ : OpenPartialHomeomorph (MorseModel n) M) (f : M → ℝ)
    (hnorm : ∀ y : MorseModel n, morseNorm n y ≤ R → f (χ y) = morseNormalForm hk c y) :
    ∀ x : M, morseModifiedFunction (H := H) (M := M) hk c ε δ R χ f x ≤ f x := by
  intro x
  by_cases hxt : x ∈ χ.target
  · by_cases hb : morseNorm n (χ.symm x) ≤ R
    · dsimp [morseModifiedFunction]
      rw [if_pos hxt, if_pos hb]
      exact le_trans (modifiedNormalForm_le_f hk c ε δ hε (χ.symm x)) (by
        rw [← hnorm (χ.symm x) hb]
        rw [χ.right_inv hxt])
    · dsimp [morseModifiedFunction]
      rw [if_pos hxt, if_neg hb]
  · dsimp [morseModifiedFunction]
    rw [if_neg hxt]

theorem isCompact_strip_morseModifiedFunction {n k : ℕ} (hk : k ≤ n) (c ε δ R a : ℝ)
    (hε : 0 < ε) (hδ : 0 < δ) (hδε : 9 * δ ^ 2 < 4 * ε) (hεa : ε ≤ a)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    [T2Space M] (χ : OpenPartialHomeomorph (MorseModel n) M) (f : M → ℝ)
    (hf : Continuous f)
    (hnorm : ∀ y : MorseModel n, morseNorm n y ≤ R → f (χ y) = morseNormalForm hk c y)
    (hg : Continuous (morseModifiedFunction (H := H) (M := M) hk c ε δ R χ f))
    (hcomp : IsCompact (f ⁻¹' Set.Icc (c - a) (c + a))) :
    IsCompact ((morseModifiedFunction (H := H) (M := M) hk c ε δ R χ f) ⁻¹'
      Set.Icc (c - ε) (c + ε)) := by
  let g : M → ℝ := morseModifiedFunction (H := H) (M := M) hk c ε δ R χ f
  have hle : ∀ x : M, g x ≤ f x := by
    intro x
    exact morseModifiedFunction_le_f (H := H) (M := M) hk c ε δ R hε χ f hnorm x
  have hup : {x : M | g x ≤ c + ε} = sublevel f (c + ε) :=
    sublevel_upper_identity_morseModifiedFunction (H := H) (M := M) hk c ε δ R hε hδ hδε χ f hnorm
  have hsub : g ⁻¹' Set.Icc (c - ε) (c + ε) ⊆ f ⁻¹' Set.Icc (c - ε) (c + ε) := by
    intro x hx
    constructor
    · exact le_trans hx.1 (hle x)
    · have hg2 : g x ≤ c + ε := hx.2
      have hmem : x ∈ sublevel f (c + ε) := by
        rw [← hup]
        exact hg2
      exact hmem
  have hfsub : f ⁻¹' Set.Icc (c - ε) (c + ε) ⊆ f ⁻¹' Set.Icc (c - a) (c + a) := by
    intro x hx
    constructor
    · exact le_trans (by linarith) hx.1
    · exact le_trans hx.2 (by linarith)
  have hfcomp : IsCompact (f ⁻¹' Set.Icc (c - ε) (c + ε)) :=
    hcomp.of_isClosed_subset (isClosed_Icc.preimage hf) hfsub
  exact hfcomp.of_isClosed_subset (isClosed_Icc.preimage hg) hsub

theorem no_critical_point_morseModifiedFunction {n k : ℕ} (hk : k ≤ n) (c ε δ R rΦ a : ℝ)
    (hε : 0 < ε) (hδ : 0 < δ) (hδε : 9 * δ ^ 2 < 4 * ε)
    (hR : 4 * ε + 9 * δ ^ 2 / 4 < R ^ 2)
    (hΦr : 4 * ε + 9 * δ ^ 2 / 4 < rΦ ^ 2) (hRpos : 0 < R) (hΦpos : 0 < rΦ)
    (hεa : ε ≤ a)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
    (I : ModelWithCorners ℝ (MorseModel n) H) (f : M → ℝ) (p : M)
    (χ : OpenPartialHomeomorph (MorseModel n) M)
    (hχ0 : χ 0 = p)
    (hnorm : ∀ y : MorseModel n, morseNorm n y ≤ R → f (χ y) = morseNormalForm hk c y)
    (hχsrc : ∀ y : MorseModel n, morseNorm n y ≤ R → y ∈ χ.source)
    (hχsymmOn : ContMDiffOn I 𝓘(ℝ, MorseModel n) (↑(⊤ : ℕ∞) : WithTop ℕ∞) χ.symm
      (χ '' Metric.ball (0 : MorseModel n) rΦ))
    (hχon : ContMDiffOn 𝓘(ℝ, MorseModel n) I (↑(⊤ : ℕ∞) : WithTop ℕ∞) χ
      (Metric.ball (0 : MorseModel n) rΦ))
    (hreg : ∀ x : M, f x ∈ Set.Icc (c - a) (c + a) → x = p ∨ ¬ IsCriticalPointAt I f x)
    {x : M} (hx : morseModifiedFunction (H := H) (M := M) hk c ε δ R χ f x ∈
      Set.Icc (c - ε) (c + ε)) :
    ¬ IsCriticalPointAt I (morseModifiedFunction (H := H) (M := M) hk c ε δ R χ f) x := by
  let g : M → ℝ := morseModifiedFunction (H := H) (M := M) hk c ε δ R χ f
  let ball : Set (MorseModel n) := {y : MorseModel n | morseNorm n y ≤ R}
  change g x ∈ Set.Icc (c - ε) (c + ε) at hx
  have hχballClosed : IsClosed (χ '' ball) := by
    simpa [ball] using isClosed_chartBallImage (H := H) (M := M) χ R hχsrc
  classical
  intro hcrit
  change IsCriticalPointAt I g x at hcrit
  change mfderiv I 𝓘(ℝ, ℝ) g x = 0 at hcrit
  have hfval : f x ∈ Set.Icc (c - a) (c + a) := by
    have hle : g x ≤ f x :=
      morseModifiedFunction_le_f (H := H) (M := M) hk c ε δ R hε χ f hnorm x
    have hup : {x : M | g x ≤ c + ε} = sublevel f (c + ε) :=
      sublevel_upper_identity_morseModifiedFunction (H := H) (M := M) hk c ε δ R hε hδ hδε χ f hnorm
    constructor
    · exact le_trans (le_trans (by linarith) hx.1) hle
    · have hmem : x ∈ sublevel f (c + ε) := by
        rw [← hup]
        exact hx.2
      exact le_trans hmem (by linarith)
  rcases hreg x hfval with hxp | hfreg
  · exfalso
    have h0norm : morseNorm n (0 : MorseModel n) = 0 := by
      dsimp [morseNorm]
      simp
    have h0src : (0 : MorseModel n) ∈ χ.source := hχsrc 0 (by
      rw [h0norm]
      exact le_of_lt hRpos)
    have hgp : g p = c - 3 / 2 * ε := by
      rw [← hχ0]
      dsimp [g, morseModifiedFunction]
      rw [if_pos (χ.map_source h0src)]
      have hinner : morseNorm n (χ.symm (χ 0)) ≤ R := by
        rw [χ.left_inv h0src]
        rw [h0norm]
        exact le_of_lt hRpos
      rw [if_pos hinner]
      rw [χ.left_inv h0src]
      exact modifiedNormalForm_zero hk c ε δ hε hδ
    have hlt : g p < c - ε := by linarith
    have hx1 : c - ε ≤ g p := by simpa [hxp] using hx.1
    exact (not_lt_of_ge hx1) hlt
  · by_cases hxball : x ∈ χ '' ball
    · by_cases hbig : 4 * ε + 9 * δ ^ 2 / 4 < morseNorm n (χ.symm x) ^ 2
      · have hxt : x ∈ χ.target := by
          rcases hxball with ⟨y, hy, hxy⟩
          rw [← hxy]
          exact χ.map_source (hχsrc y hy)
        have hO₂mem : {x : M | x ∈ χ.target ∧ 4 * ε + 9 * δ ^ 2 / 4 < morseNorm n (χ.symm x) ^ 2} ∈
            nhds x :=
          (isOpen_morseModifiedRegion_gt (H := H) χ (4 * ε + 9 * δ ^ 2 / 4)).mem_nhds ⟨hxt, hbig⟩
        have hagree : g =ᶠ[nhds x] f := by
          refine Filter.eventuallyEq_of_mem hO₂mem ?_
          intro z hz
          dsimp [g, morseModifiedFunction]
          rw [if_pos hz.1]
          by_cases hle : morseNorm n (χ.symm z) ≤ R
          · rw [if_pos hle]
            have hmod : modifiedNormalForm hk c ε δ (χ.symm z) = morseNormalForm hk c (χ.symm z) :=
              modifiedNormalForm_eq_of_modulation_zero hk c ε δ
                (modMu_mul_modGamma_eq_zero_of_norm_gt hk ε δ hε hδ hz.2)
            rw [hmod]
            simpa [χ.right_inv hz.1] using (hnorm (χ.symm z) hle).symm
          · rw [if_neg hle]
        have hcritf : IsCriticalPointAt I f x := by
          have hmd : mfderiv I 𝓘(ℝ, ℝ) f x = mfderiv I 𝓘(ℝ, ℝ) g x :=
            Filter.EventuallyEq.mfderiv_eq (I := I) (I' := 𝓘(ℝ, ℝ)) hagree.symm
          change mfderiv I 𝓘(ℝ, ℝ) f x = 0
          rw [hmd]
          exact hcrit
        exact hfreg hcritf
      · have hxt : x ∈ χ.target := by
          rcases hxball with ⟨y, hy, hxy⟩
          rw [← hxy]
          exact χ.map_source (hχsrc y hy)
        have hnorm_le : morseNorm n (χ.symm x) ^ 2 ≤ 4 * ε + 9 * δ ^ 2 / 4 := le_of_not_gt hbig
        have hRlt : morseNorm n (χ.symm x) < R := by
          have hsq : morseNorm n (χ.symm x) ^ 2 < R ^ 2 :=
            lt_of_le_of_lt hnorm_le (by nlinarith [hR])
          have habs := sq_lt_sq.mp hsq
          rwa [abs_of_nonneg (norm_nonneg _), abs_of_nonneg (le_of_lt hRpos)] at habs
        have hΦlt : morseNorm n (χ.symm x) < rΦ := by
          have hsq : morseNorm n (χ.symm x) ^ 2 < rΦ ^ 2 :=
            lt_of_le_of_lt hnorm_le (by nlinarith [hΦr])
          have habs := sq_lt_sq.mp hsq
          rwa [abs_of_nonneg (norm_nonneg _), abs_of_nonneg (le_of_lt hΦpos)] at habs
        have hO₃mem : {x : M | x ∈ χ.target ∧ morseNorm n (χ.symm x) < R} ∩
            {x : M | x ∈ χ.target ∧ morseNorm n (χ.symm x) < rΦ} ∈ nhds x :=
          (IsOpen.inter (isOpen_morseModifiedRegion_lt (H := H) χ R)
            (isOpen_morseModifiedRegion_lt (H := H) χ rΦ)).mem_nhds ⟨⟨hxt, hRlt⟩, ⟨hxt, hΦlt⟩⟩
        have hagree : g =ᶠ[nhds x] (fun z : M => modifiedNormalForm hk c ε δ (χ.symm z)) := by
          refine Filter.eventuallyEq_of_mem hO₃mem ?_
          intro z hz
          dsimp [g, morseModifiedFunction]
          rw [if_pos hz.1.1]
          rw [if_pos (le_of_lt hz.1.2)]
        have hy' : χ.symm x ∈ Metric.ball (0 : MorseModel n) rΦ := by
          have hsup : ‖χ.symm x‖ ≤ morseNorm n (χ.symm x) := supNorm_le_morseNorm (χ.symm x)
          rw [Metric.mem_ball, dist_zero_right]
          exact lt_of_le_of_lt hsup hΦlt
        have hleft : (χ ∘ χ.symm) =ᶠ[nhds x] id := by
          refine Filter.eventuallyEq_of_mem (χ.open_target.mem_nhds hxt) ?_
          intro z hz
          exact χ.right_inv hz
        have hright : (χ.symm ∘ χ) =ᶠ[nhds (χ.symm x)] id := by
          have hy'' : χ.symm x ∈ Metric.ball (0 : MorseModel n) rΦ ∩ χ.source :=
            ⟨hy', hχsrc (χ.symm x) (le_of_lt hRlt)⟩
          have hmem : Metric.ball (0 : MorseModel n) rΦ ∩ χ.source ∈ nhds (χ.symm x) :=
            (IsOpen.inter Metric.isOpen_ball χ.open_source).mem_nhds hy''
          refine Filter.eventuallyEq_of_mem hmem ?_
          intro z hz
          exact χ.left_inv hz.2
        have hσmd : MDifferentiableAt I 𝓘(ℝ, MorseModel n) χ.symm x := by
          have hxball' : x ∈ χ '' Metric.ball (0 : MorseModel n) rΦ := by
            refine ⟨χ.symm x, hy', ?_⟩
            exact χ.right_inv hxt
          have hopen : IsOpen (χ '' (Metric.ball (0 : MorseModel n) rΦ ∩ χ.source)) := by
            exact χ.isOpen_image_of_subset_source (IsOpen.inter Metric.isOpen_ball χ.open_source)
              (by intro y hy; exact hy.2)
          have hpre : χ.symm x ∈ Metric.ball (0 : MorseModel n) rΦ ∩ χ.source :=
            ⟨hy', hχsrc (χ.symm x) (le_of_lt hRlt)⟩
          have hxball'' : x ∈ χ '' (Metric.ball (0 : MorseModel n) rΦ ∩ χ.source) :=
            ⟨χ.symm x, hpre, χ.right_inv hxt⟩
          have hballNhds : χ '' Metric.ball (0 : MorseModel n) rΦ ∈ nhds x :=
            Filter.mem_of_superset (hopen.mem_nhds hxball'') (by
              intro z hz
              exact Set.image_mono (by intro y hy; exact hy.1) hz)
          exact ((hχsymmOn x hxball').contMDiffAt hballNhds).mdifferentiableAt (by norm_num)
        have hτmd : MDifferentiableAt 𝓘(ℝ, MorseModel n) I χ (χ.symm x) := by
          exact ((hχon (χ.symm x) hy').contMDiffAt (Metric.isOpen_ball.mem_nhds hy')).mdifferentiableAt
            (by norm_num)
        have hh : ContMDiffAt 𝓘(ℝ, MorseModel n) 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
            (modifiedNormalForm hk c ε δ) (χ.symm x) :=
          (contDiff_modifiedNormalForm hk c ε δ hδ).contMDiff.contMDiffAt
        have htrans := isCriticalPointAt_iff_fderiv_of_localInverse (I := I)
          (σ := χ.symm) (τ := χ) (h := modifiedNormalForm hk c ε δ)
          hleft hright hσmd hτmd hh
        have hstrip : modifiedNormalForm hk c ε δ (χ.symm x) ∈ Set.Icc (c - ε) (c + ε) := by
          have hgx : g x = modifiedNormalForm hk c ε δ (χ.symm x) := hagree.eq_of_nhds
          rw [← hgx]
          exact hx
        have hcrit' : IsCriticalPointAt I (fun z : M => modifiedNormalForm hk c ε δ (χ.symm z)) x := by
          have hmd : mfderiv I 𝓘(ℝ, ℝ) (fun z : M => modifiedNormalForm hk c ε δ (χ.symm z)) x =
              mfderiv I 𝓘(ℝ, ℝ) g x :=
            Filter.EventuallyEq.mfderiv_eq (I := I) (I' := 𝓘(ℝ, ℝ)) hagree.symm
          change mfderiv I 𝓘(ℝ, ℝ) (fun z : M => modifiedNormalForm hk c ε δ (χ.symm z)) x = 0
          rw [hmd]
          exact hcrit
        have hfd : fderiv ℝ (modifiedNormalForm hk c ε δ) (χ.symm x) = 0 := htrans.1 hcrit'
        exact (modifiedNormalForm_no_critical_point_in_strip hk c ε δ hε hδ hstrip) hfd
    · have houtside : {x : M | x ∉ χ '' ball} ∈ nhds x := by
        exact (isOpen_compl_iff.mpr hχballClosed).mem_nhds hxball
      have hagree : g =ᶠ[nhds x] f := by
        refine Filter.eventuallyEq_of_mem houtside ?_
        intro z hz
        dsimp [g, morseModifiedFunction]
        by_cases hzt : z ∈ χ.target
        · rw [if_pos hzt]
          have hle' : ¬ morseNorm n (χ.symm z) ≤ R := by
            intro hle
            apply hz
            exact ⟨χ.symm z, hle, χ.right_inv hzt⟩
          rw [if_neg hle']
        · rw [if_neg hzt]
      have hcritf : IsCriticalPointAt I f x := by
        have hmd : mfderiv I 𝓘(ℝ, ℝ) f x = mfderiv I 𝓘(ℝ, ℝ) g x :=
          Filter.EventuallyEq.mfderiv_eq (I := I) (I' := 𝓘(ℝ, ℝ)) hagree.symm
        change mfderiv I 𝓘(ℝ, ℝ) f x = 0
        rw [hmd]
        exact hcrit
      exact hfreg hcritf

open Classical in
noncomputable def morseModifiedRetraction {n k : ℕ} (hk : k ≤ n) (c ε R : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M]
    (χ : OpenPartialHomeomorph (MorseModel n) M) (x : M) : M :=
  if x ∈ χ '' {y : MorseModel n | morseNorm n y ≤ R} then
    χ (modifiedCollarRetraction hk c ε (χ.symm x))
  else x

open Classical in
noncomputable def morseModifiedRetractionHomotopy {n k : ℕ} (hk : k ≤ n) (c ε R : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M]
    (χ : OpenPartialHomeomorph (MorseModel n) M) (t : ℝ) (x : M) : M :=
  if x ∈ χ '' {y : MorseModel n | morseNorm n y ≤ R} then
    χ (modifiedCollarHomotopy hk c ε t (χ.symm x))
  else x

theorem continuousOn_morseModifiedRetraction {n k : ℕ} (hk : k ≤ n) (c ε δ R : ℝ)
    (hε : 0 < ε) (hδ : 0 < δ) (hR : 4 * ε + 9 * δ ^ 2 / 4 < R ^ 2) (hRpos : 0 < R)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
    (χ : OpenPartialHomeomorph (MorseModel n) M) (f : M → ℝ)
    (hg : Continuous (morseModifiedFunction (H := H) (M := M) hk c ε δ R χ f))
    (hχsrc : ∀ y : MorseModel n, morseNorm n y ≤ R → y ∈ χ.source) :
    ContinuousOn (morseModifiedRetraction (H := H) (M := M) hk c ε R χ)
      {x : M | morseModifiedFunction (H := H) (M := M) hk c ε δ R χ f x ≤ c - ε} := by
  let g : M → ℝ := morseModifiedFunction (H := H) (M := M) hk c ε δ R χ f
  let ball : Set (MorseModel n) := {y : MorseModel n | morseNorm n y ≤ R}
  let C₁ : Set M := χ '' ball
  let S₁ : Set M := {x : M | g x ≤ c - ε} ∩ C₁
  let S₂ : Set M := {x : M | g x ≤ c - ε} ∩ {x : M | x ∉ χ '' {y : MorseModel n | morseNorm n y < R}}
  have hC₁closed : IsClosed C₁ := by
    simpa [C₁, ball] using isClosed_chartBallImage (H := H) (M := M) χ R hχsrc
  have hIntOpen : IsOpen (χ '' {y : MorseModel n | morseNorm n y < R}) := by
    have hcont : Continuous (fun y : MorseModel n => morseNorm n y) := by
      simpa [morseNorm] using
        (continuous_norm.comp (PiLp.continuous_toLp (p := (2 : ENNReal)) (β := fun _ : Fin n => ℝ)))
    exact χ.isOpen_image_of_subset_source (isOpen_lt hcont continuous_const)
      (by intro y hy; exact hχsrc y (le_of_lt hy))
  have hS₁closed : IsClosed S₁ := by
    dsimp [S₁]
    exact IsClosed.inter (isClosed_le hg continuous_const) hC₁closed
  have hS₂closed : IsClosed S₂ := by
    dsimp [S₂]
    exact IsClosed.inter (isClosed_le hg continuous_const) (isClosed_compl_iff.mpr hIntOpen)
  have hC₁target : C₁ ⊆ χ.target := by
    intro x hx
    rcases hx with ⟨y, hy, hxy⟩
    rw [← hxy]
    exact χ.map_source (hχsrc y hy)
  have hgx_eq (x : M) (hx : x ∈ C₁) :
      g x = modifiedNormalForm hk c ε δ (χ.symm x) := by
    rcases hx with ⟨y, hy, hxy⟩
    dsimp [g, morseModifiedFunction]
    rw [← hxy, if_pos (χ.map_source (hχsrc y hy)), χ.left_inv (hχsrc y hy)]
    rw [if_pos (by simpa [ball] using hy)]
  have hnormBoundary : ∀ x : M, x ∈ {x : M | g x ≤ c - ε} → x ∈ C₁ →
      x ∉ χ '' {y : MorseModel n | morseNorm n y < R} →
      morseNormalForm hk c (χ.symm x) ≤ c - ε := by
    intro x hxA hxC hxbound
    rcases hxC with ⟨y, hy, hxy⟩
    have hyR : morseNorm n y = R := by
      by_contra hne
      have hlt : morseNorm n y < R := lt_of_le_of_ne hy hne
      apply hxbound
      exact ⟨y, hlt, hxy⟩
    have hsymm : χ.symm x = y := by
      rw [← hxy]
      exact χ.left_inv (hχsrc y hy)
    have hmod : modifiedNormalForm hk c ε δ y ≤ c - ε := by
      have hgx : g x = modifiedNormalForm hk c ε δ y := by
        rw [← hsymm]
        exact hgx_eq x ⟨y, hy, hxy⟩
      rw [← hgx]
      exact hxA
    by_contra hf
    have hmu : modMu ε (‖negPart hk y‖ ^ 2) * modGamma δ ‖posPart hk y‖ ≠ 0 := by
      intro h0
      have hmod' : modifiedNormalForm hk c ε δ y = morseNormalForm hk c y :=
        modifiedNormalForm_eq_of_modulation_zero hk c ε δ h0
      have : morseNormalForm hk c y ≤ c - ε := by
        rw [← hmod']
        exact hmod
      exact hf (by simpa [hsymm] using this)
    have hnorm_le : morseNorm n y ^ 2 ≤ 4 * ε + 9 * δ ^ 2 / 4 := by
      by_contra hnot
      have hgt : 4 * ε + 9 * δ ^ 2 / 4 < morseNorm n y ^ 2 := lt_of_not_ge hnot
      exact hmu (modMu_mul_modGamma_eq_zero_of_norm_gt hk ε δ hε hδ hgt)
    have hcontra : morseNorm n y ^ 2 < R ^ 2 := lt_of_le_of_lt hnorm_le hR
    have hsqR : morseNorm n y ^ 2 = R ^ 2 := by nlinarith [hyR]
    exact (not_lt_of_ge (le_of_eq hsqR.symm)) hcontra
  have hfix_boundary : ∀ x : M, x ∈ {x : M | g x ≤ c - ε} → x ∈ C₁ →
      x ∉ χ '' {y : MorseModel n | morseNorm n y < R} →
      modifiedCollarRetraction hk c ε (χ.symm x) = χ.symm x := by
    intro x hxA hxC hxbound
    dsimp [modifiedCollarRetraction]
    rw [if_pos (hnormBoundary x hxA hxC hxbound)]
  have hretrOn : ContinuousOn (fun x : M => modifiedCollarRetraction hk c ε (χ.symm x)) S₁ := by
    have hχsymm : ContinuousOn χ.symm S₁ := χ.continuousOn_invFun.mono (by
      intro x hx
      exact hC₁target hx.2)
    have hmap : Set.MapsTo χ.symm S₁
        {y : MorseModel n | modifiedNormalForm hk c ε δ y ≤ c - ε} := by
      intro x hx
      change modifiedNormalForm hk c ε δ (χ.symm x) ≤ c - ε
      rw [← hgx_eq x hx.2]
      exact hx.1
    simpa [Function.comp_def] using
      ((continuousOn_modifiedCollarRetraction_sublevel hk c ε δ).comp hχsymm hmap)
  have hretrImg : Set.MapsTo (fun x : M => modifiedCollarRetraction hk c ε (χ.symm x)) S₁ χ.source := by
    intro x hx
    have hy : morseNorm n (χ.symm x) ≤ R := by
      rcases hx.2 with ⟨y, hy, hxy⟩
      have hsymm : χ.symm x = y := by
        rw [← hxy]
        exact χ.left_inv (hχsrc y hy)
      rw [hsymm]
      exact hy
    have hle := morseNorm_modifiedCollarHomotopy_le hk c ε (by norm_num : (0 : ℝ) ≤ 1)
      (by norm_num : (1 : ℝ) ≤ 1) (χ.symm x)
    have h1 : modifiedCollarHomotopy hk c ε 1 (χ.symm x) = modifiedCollarRetraction hk c ε (χ.symm x) :=
      modifiedCollarHomotopy_one hk c ε (χ.symm x)
    exact hχsrc (modifiedCollarRetraction hk c ε (χ.symm x)) (by
      simpa [h1] using (le_trans hle hy))
  have hretrOn' : ContinuousOn (fun x : M => χ (modifiedCollarRetraction hk c ε (χ.symm x))) S₁ := by
    have hχsrc' : ContinuousOn χ ((fun x : M => modifiedCollarRetraction hk c ε (χ.symm x)) '' S₁) :=
      χ.continuousOn_toFun.mono (by
        intro z hz
        rcases hz with ⟨x, hx, hxz⟩
        rw [← hxz]
        exact hretrImg hx)
    exact ContinuousOn.comp' hχsrc' hretrOn (Set.mapsTo_image
      (fun x : M => modifiedCollarRetraction hk c ε (χ.symm x)) S₁)
  have hcontS₁ : ContinuousOn (morseModifiedRetraction (H := H) (M := M) hk c ε R χ) S₁ := by
    have hEq : Set.EqOn (fun x : M => χ (modifiedCollarRetraction hk c ε (χ.symm x)))
        (morseModifiedRetraction (H := H) (M := M) hk c ε R χ) S₁ := by
      intro x hx
      dsimp [morseModifiedRetraction]
      rw [if_pos hx.2]
    exact ContinuousOn.congr hretrOn' hEq.symm
  have hcontS₂ : ContinuousOn (morseModifiedRetraction (H := H) (M := M) hk c ε R χ) S₂ := by
    have hEq : Set.EqOn (fun x : M => x)
        (morseModifiedRetraction (H := H) (M := M) hk c ε R χ) S₂ := by
      intro x hx
      dsimp [morseModifiedRetraction]
      by_cases hxC : x ∈ C₁
      · rw [if_pos hxC]
        have hfix := hfix_boundary x hx.1 hxC (by
          intro hmem
          exact hx.2 hmem)
        have hsymm : χ (χ.symm x) = x := by
          exact χ.right_inv (hC₁target hxC)
        rw [hfix]
        exact hsymm.symm
      · rw [if_neg hxC]
    exact ContinuousOn.congr continuousOn_id hEq.symm
  have hcover : S₁ ∪ S₂ = {x : M | g x ≤ c - ε} := by
    ext x
    constructor
    · intro hx
      rcases hx with hx | hx
      · exact hx.1
      · exact hx.1
    · intro hx
      by_cases hxC : x ∈ C₁
      · by_cases hxint : x ∈ χ '' {y : MorseModel n | morseNorm n y < R}
        · exact Or.inl ⟨hx, hxC⟩
        · exact Or.inr ⟨hx, hxint⟩
      · exact Or.inr ⟨hx, by intro hmem; exact hxC (by
          rcases hmem with ⟨y, hy, hxy⟩
          exact ⟨y, (by simpa [ball] using (le_of_lt hy)), hxy⟩)⟩
  have hcont : ContinuousOn (morseModifiedRetraction (H := H) (M := M) hk c ε R χ)
      (S₁ ∪ S₂) :=
    ContinuousOn.union_of_isClosed hcontS₁ hcontS₂ hS₁closed hS₂closed
  change ContinuousOn (morseModifiedRetraction (H := H) (M := M) hk c ε R χ)
    {x : M | g x ≤ c - ε}
  rwa [← hcover]

theorem continuousOn_morseModifiedRetractionHomotopy {n k : ℕ} (hk : k ≤ n) (c ε δ R : ℝ)
    (hε : 0 < ε) (hδ : 0 < δ) (hR : 4 * ε + 9 * δ ^ 2 / 4 < R ^ 2) (hRpos : 0 < R)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
    (χ : OpenPartialHomeomorph (MorseModel n) M) (f : M → ℝ)
    (hg : Continuous (morseModifiedFunction (H := H) (M := M) hk c ε δ R χ f))
    (hχsrc : ∀ y : MorseModel n, morseNorm n y ≤ R → y ∈ χ.source) :
    ContinuousOn (fun p : Set.Icc (0 : ℝ) 1 × M =>
      morseModifiedRetractionHomotopy (H := H) (M := M) hk c ε R χ (1 - (p.1 : ℝ)) p.2)
      ((Set.univ : Set (Set.Icc (0 : ℝ) 1)) ×ˢ
        {x : M | morseModifiedFunction (H := H) (M := M) hk c ε δ R χ f x ≤ c - ε}) := by
  let g : M → ℝ := morseModifiedFunction (H := H) (M := M) hk c ε δ R χ f
  let ball : Set (MorseModel n) := {y : MorseModel n | morseNorm n y ≤ R}
  let C₁ : Set M := χ '' ball
  let S₁ : Set M := {x : M | g x ≤ c - ε} ∩ C₁
  let S₂ : Set M := {x : M | g x ≤ c - ε} ∩ {x : M | x ∉ χ '' {y : MorseModel n | morseNorm n y < R}}
  let P₁ : Set (Set.Icc (0 : ℝ) 1 × M) := Set.univ ×ˢ S₁
  let P₂ : Set (Set.Icc (0 : ℝ) 1 × M) := Set.univ ×ˢ S₂
  have hC₁closed : IsClosed C₁ := by
    simpa [C₁, ball] using isClosed_chartBallImage (H := H) (M := M) χ R hχsrc
  have hIntOpen : IsOpen (χ '' {y : MorseModel n | morseNorm n y < R}) := by
    have hcont : Continuous (fun y : MorseModel n => morseNorm n y) := by
      simpa [morseNorm] using
        (continuous_norm.comp (PiLp.continuous_toLp (p := (2 : ENNReal)) (β := fun _ : Fin n => ℝ)))
    exact χ.isOpen_image_of_subset_source (isOpen_lt hcont continuous_const)
      (by intro y hy; exact hχsrc y (le_of_lt hy))
  have hS₁closed : IsClosed S₁ := by
    dsimp [S₁]
    exact IsClosed.inter (isClosed_le hg continuous_const) hC₁closed
  have hS₂closed : IsClosed S₂ := by
    dsimp [S₂]
    exact IsClosed.inter (isClosed_le hg continuous_const) (isClosed_compl_iff.mpr hIntOpen)
  have hP₁closed : IsClosed P₁ := isClosed_univ.prod hS₁closed
  have hP₂closed : IsClosed P₂ := isClosed_univ.prod hS₂closed
  have hC₁target : C₁ ⊆ χ.target := by
    intro x hx
    rcases hx with ⟨y, hy, hxy⟩
    rw [← hxy]
    exact χ.map_source (hχsrc y hy)
  have hgx_eq (x : M) (hx : x ∈ C₁) :
      g x = modifiedNormalForm hk c ε δ (χ.symm x) := by
    rcases hx with ⟨y, hy, hxy⟩
    dsimp [g, morseModifiedFunction]
    rw [← hxy, if_pos (χ.map_source (hχsrc y hy)), χ.left_inv (hχsrc y hy)]
    rw [if_pos (by simpa [ball] using hy)]
  have hnormBoundary : ∀ x : M, x ∈ {x : M | g x ≤ c - ε} → x ∈ C₁ →
      x ∉ χ '' {y : MorseModel n | morseNorm n y < R} →
      morseNormalForm hk c (χ.symm x) ≤ c - ε := by
    intro x hxA hxC hxbound
    rcases hxC with ⟨y, hy, hxy⟩
    have hyR : morseNorm n y = R := by
      by_contra hne
      have hlt : morseNorm n y < R := lt_of_le_of_ne hy hne
      apply hxbound
      exact ⟨y, hlt, hxy⟩
    have hsymm : χ.symm x = y := by
      rw [← hxy]
      exact χ.left_inv (hχsrc y hy)
    have hmod : modifiedNormalForm hk c ε δ y ≤ c - ε := by
      have hgx : g x = modifiedNormalForm hk c ε δ y := by
        rw [← hsymm]
        exact hgx_eq x ⟨y, hy, hxy⟩
      rw [← hgx]
      exact hxA
    by_contra hf
    have hmu : modMu ε (‖negPart hk y‖ ^ 2) * modGamma δ ‖posPart hk y‖ ≠ 0 := by
      intro h0
      have hmod' : modifiedNormalForm hk c ε δ y = morseNormalForm hk c y :=
        modifiedNormalForm_eq_of_modulation_zero hk c ε δ h0
      have : morseNormalForm hk c y ≤ c - ε := by
        rw [← hmod']
        exact hmod
      exact hf (by simpa [hsymm] using this)
    have hnorm_le : morseNorm n y ^ 2 ≤ 4 * ε + 9 * δ ^ 2 / 4 := by
      by_contra hnot
      have hgt : 4 * ε + 9 * δ ^ 2 / 4 < morseNorm n y ^ 2 := lt_of_not_ge hnot
      exact hmu (modMu_mul_modGamma_eq_zero_of_norm_gt hk ε δ hε hδ hgt)
    have hcontra : morseNorm n y ^ 2 < R ^ 2 := lt_of_le_of_lt hnorm_le hR
    have hsqR : morseNorm n y ^ 2 = R ^ 2 := by nlinarith [hyR]
    exact (not_lt_of_ge (le_of_eq hsqR.symm)) hcontra
  have hfix_homotopy : ∀ x : M, x ∈ {x : M | g x ≤ c - ε} → x ∈ C₁ →
      x ∉ χ '' {y : MorseModel n | morseNorm n y < R} → ∀ t : ℝ,
      modifiedCollarHomotopy hk c ε t (χ.symm x) = χ.symm x := by
    intro x hxA hxC hxbound t
    dsimp [modifiedCollarHomotopy]
    rw [if_pos (hnormBoundary x hxA hxC hxbound)]
  have hχsymmOnP₁ : ContinuousOn (fun p : Set.Icc (0 : ℝ) 1 × M => χ.symm p.2) P₁ := by
    have hmap : Set.MapsTo (fun p : Set.Icc (0 : ℝ) 1 × M => p.2) P₁ χ.target := by
      intro p hp
      exact hC₁target hp.2.2
    have hproj : ContinuousOn (fun p : Set.Icc (0 : ℝ) 1 × M => p.2) P₁ :=
      (continuous_snd.continuousOn : ContinuousOn (fun p : Set.Icc (0 : ℝ) 1 × M => p.2)
        (Set.univ : Set (Set.Icc (0 : ℝ) 1 × M))).mono (by intro p hp; trivial)
    exact ContinuousOn.comp' χ.continuousOn_invFun hproj hmap
  have hreparam : Continuous (fun p : Set.Icc (0 : ℝ) 1 × M =>
      (⟨1 - (p.1 : ℝ), by linarith [p.1.2.2], by linarith [p.1.2.1]⟩ : Set.Icc (0 : ℝ) 1)) := by
    exact Continuous.subtype_mk
      (f := fun p : Set.Icc (0 : ℝ) 1 × M => 1 - (p.1 : ℝ))
      (continuous_const.sub (continuous_subtype_val.comp continuous_fst))
      (by intro p; exact ⟨by linarith [p.1.2.2], by linarith [p.1.2.1]⟩)
  have hstep : ContinuousOn (fun p : Set.Icc (0 : ℝ) 1 × M =>
      modifiedCollarHomotopy hk c ε (1 - (p.1 : ℝ)) (χ.symm p.2)) P₁ := by
    let reparamFun : Set.Icc (0 : ℝ) 1 × M → Set.Icc (0 : ℝ) 1 := fun p =>
      ⟨1 - (p.1 : ℝ), by linarith [p.1.2.2], by linarith [p.1.2.1]⟩
    have hpair : ContinuousOn (fun p : Set.Icc (0 : ℝ) 1 × M =>
        (reparamFun p, χ.symm p.2)) P₁ :=
      hreparam.continuousOn.prodMk hχsymmOnP₁
    have hmap : Set.MapsTo (fun p : Set.Icc (0 : ℝ) 1 × M =>
        (reparamFun p, χ.symm p.2)) P₁
        ((Set.univ : Set (Set.Icc (0 : ℝ) 1)) ×ˢ
          {y : MorseModel n | modifiedNormalForm hk c ε δ y ≤ c - ε}) := by
      intro p hp
      have hg : modifiedNormalForm hk c ε δ (χ.symm p.2) ≤ c - ε := by
        rw [← hgx_eq p.2 hp.2.2]
        exact hp.2.1
      exact ⟨trivial, hg⟩
    simpa [Function.comp_def] using
      ((continuousOn_modifiedCollarHomotopy_sublevel hk c ε δ).comp hpair hmap)
  have hstepImg : Set.MapsTo (fun p : Set.Icc (0 : ℝ) 1 × M =>
      modifiedCollarHomotopy hk c ε (1 - (p.1 : ℝ)) (χ.symm p.2)) P₁ χ.source := by
    intro p hp
    have ht0 : 0 ≤ 1 - (p.1 : ℝ) := by linarith [p.1.2.2]
    have ht1 : 1 - (p.1 : ℝ) ≤ 1 := by linarith [p.1.2.1]
    have hy : morseNorm n (χ.symm p.2) ≤ R := by
      rcases hp.2.2 with ⟨y, hy, hxy⟩
      have hsymm : χ.symm p.2 = y := by
        rw [← hxy]
        exact χ.left_inv (hχsrc y hy)
      rw [hsymm]
      exact hy
    have hle := morseNorm_modifiedCollarHomotopy_le hk c ε ht0 ht1 (χ.symm p.2)
    exact hχsrc (modifiedCollarHomotopy hk c ε (1 - (p.1 : ℝ)) (χ.symm p.2)) (le_trans hle hy)
  have hstep' : ContinuousOn (fun p : Set.Icc (0 : ℝ) 1 × M =>
      χ (modifiedCollarHomotopy hk c ε (1 - (p.1 : ℝ)) (χ.symm p.2))) P₁ := by
    have hχ' : ContinuousOn χ ((fun p : Set.Icc (0 : ℝ) 1 × M =>
        modifiedCollarHomotopy hk c ε (1 - (p.1 : ℝ)) (χ.symm p.2)) '' P₁) :=
      χ.continuousOn_toFun.mono (by
        intro z hz
        rcases hz with ⟨p, hp, hpz⟩
        rw [← hpz]
        exact hstepImg hp)
    exact ContinuousOn.comp' hχ' hstep (Set.mapsTo_image
      (fun p : Set.Icc (0 : ℝ) 1 × M =>
        modifiedCollarHomotopy hk c ε (1 - (p.1 : ℝ)) (χ.symm p.2)) P₁)
  have hcontP₁ : ContinuousOn (fun p : Set.Icc (0 : ℝ) 1 × M =>
      morseModifiedRetractionHomotopy (H := H) (M := M) hk c ε R χ (1 - (p.1 : ℝ)) p.2) P₁ := by
    have hEq : Set.EqOn (fun p : Set.Icc (0 : ℝ) 1 × M =>
        χ (modifiedCollarHomotopy hk c ε (1 - (p.1 : ℝ)) (χ.symm p.2)))
        (fun p : Set.Icc (0 : ℝ) 1 × M =>
          morseModifiedRetractionHomotopy (H := H) (M := M) hk c ε R χ (1 - (p.1 : ℝ)) p.2) P₁ := by
      intro p hp
      dsimp [morseModifiedRetractionHomotopy]
      rw [if_pos hp.2.2]
    exact ContinuousOn.congr hstep' hEq.symm
  have hcontP₂ : ContinuousOn (fun p : Set.Icc (0 : ℝ) 1 × M =>
      morseModifiedRetractionHomotopy (H := H) (M := M) hk c ε R χ (1 - (p.1 : ℝ)) p.2) P₂ := by
    have hEq : Set.EqOn (fun p : Set.Icc (0 : ℝ) 1 × M => p.2)
        (fun p : Set.Icc (0 : ℝ) 1 × M =>
          morseModifiedRetractionHomotopy (H := H) (M := M) hk c ε R χ (1 - (p.1 : ℝ)) p.2) P₂ := by
      intro p hp
      dsimp [morseModifiedRetractionHomotopy]
      by_cases hC : p.2 ∈ C₁
      · rw [if_pos hC]
        have hfix := hfix_homotopy p.2 hp.2.1 hC (by intro hmem; exact hp.2.2 hmem)
          (1 - (p.1 : ℝ))
        have hsymm : χ (χ.symm p.2) = p.2 := χ.right_inv (hC₁target hC)
        rw [hfix]
        exact hsymm.symm
      · rw [if_neg hC]
    have hproj : ContinuousOn (fun p : Set.Icc (0 : ℝ) 1 × M => p.2) P₂ :=
      (continuous_snd.continuousOn : ContinuousOn (fun p : Set.Icc (0 : ℝ) 1 × M => p.2)
        (Set.univ : Set (Set.Icc (0 : ℝ) 1 × M))).mono (by intro p hp; trivial)
    exact ContinuousOn.congr hproj hEq.symm
  have hcover : P₁ ∪ P₂ = Set.univ ×ˢ {x : M | g x ≤ c - ε} := by
    ext p
    constructor
    · intro hp
      rcases hp with hp | hp
      · exact ⟨trivial, hp.2.1⟩
      · exact ⟨trivial, hp.2.1⟩
    · intro hp
      by_cases hC : p.2 ∈ C₁
      · by_cases hint : p.2 ∈ χ '' {y : MorseModel n | morseNorm n y < R}
        · exact Or.inl ⟨trivial, ⟨hp.2, hC⟩⟩
        · exact Or.inr ⟨trivial, ⟨hp.2, hint⟩⟩
      · exact Or.inr ⟨trivial, ⟨hp.2, by intro hmem; exact hC (by
          rcases hmem with ⟨y, hy, hxy⟩
          exact ⟨y, (by simpa [ball] using (le_of_lt hy)), hxy⟩)⟩⟩
  have hcont : ContinuousOn (fun p : Set.Icc (0 : ℝ) 1 × M =>
      morseModifiedRetractionHomotopy (H := H) (M := M) hk c ε R χ (1 - (p.1 : ℝ)) p.2)
      (P₁ ∪ P₂) :=
    ContinuousOn.union_of_isClosed hcontP₁ hcontP₂ hP₁closed hP₂closed
  change ContinuousOn (fun p : Set.Icc (0 : ℝ) 1 × M =>
      morseModifiedRetractionHomotopy (H := H) (M := M) hk c ε R χ (1 - (p.1 : ℝ)) p.2)
      (Set.univ ×ˢ {x : M | g x ≤ c - ε})
  rwa [← hcover]

theorem morseModifiedRetractionHomotopy_zero {n k : ℕ} (hk : k ≤ n) (c ε R : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M]
    (χ : OpenPartialHomeomorph (MorseModel n) M)
    (hχsrc : ∀ y : MorseModel n, morseNorm n y ≤ R → y ∈ χ.source) (x : M) :
    morseModifiedRetractionHomotopy (H := H) (M := M) hk c ε R χ 0 x = x := by
  by_cases hC : x ∈ χ '' {y : MorseModel n | morseNorm n y ≤ R}
  · dsimp [morseModifiedRetractionHomotopy]
    rw [if_pos hC]
    have hxt : x ∈ χ.target := by
      rcases hC with ⟨y, hy, hxy⟩
      rw [← hxy]
      exact χ.map_source (hχsrc y hy)
    rw [modifiedCollarHomotopy_zero]
    exact χ.right_inv hxt
  · dsimp [morseModifiedRetractionHomotopy]
    rw [if_neg hC]

theorem morseModifiedRetractionHomotopy_one {n k : ℕ} (hk : k ≤ n) (c ε R : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M]
    (χ : OpenPartialHomeomorph (MorseModel n) M) (x : M) :
    morseModifiedRetractionHomotopy (H := H) (M := M) hk c ε R χ 1 x =
      morseModifiedRetraction (H := H) (M := M) hk c ε R χ x := by
  by_cases hC : x ∈ χ '' {y : MorseModel n | morseNorm n y ≤ R}
  · dsimp [morseModifiedRetractionHomotopy, morseModifiedRetraction]
    rw [if_pos hC, if_pos hC]
    rw [modifiedCollarHomotopy_one]
  · dsimp [morseModifiedRetractionHomotopy, morseModifiedRetraction]
    rw [if_neg hC, if_neg hC]

theorem morseModifiedRetraction_mem_lowerUnion {n k : ℕ} (hk : k ≤ n) (c ε δ R : ℝ)
    (hε : 0 < ε)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    (χ : OpenPartialHomeomorph (MorseModel n) M) (f : M → ℝ)
    (hnorm : ∀ y : MorseModel n, morseNorm n y ≤ R → f (χ y) = morseNormalForm hk c y)
    (hχsrc : ∀ y : MorseModel n, morseNorm n y ≤ R → y ∈ χ.source)
    {x : M} (hx : morseModifiedFunction (H := H) (M := M) hk c ε δ R χ f x ≤ c - ε) :
    morseModifiedRetraction (H := H) (M := M) hk c ε R χ x ∈
      sublevel f (c - ε) ∪ χ '' (Set.range (fun z : ClosedCell k =>
        cellMap (Real.sqrt (2 * ε)) (z : EuclideanSpace ℝ (Fin k)))) := by
  let g : M → ℝ := morseModifiedFunction (H := H) (M := M) hk c ε δ R χ f
  let ball : Set (MorseModel n) := {y : MorseModel n | morseNorm n y ≤ R}
  change g x ≤ c - ε at hx
  by_cases hC : x ∈ χ '' ball
  · rcases hC with ⟨y, hy, hxy⟩
    have hsymm : χ.symm x = y := by
      rw [← hxy]
      exact χ.left_inv (hχsrc y hy)
    have hmod : modifiedNormalForm hk c ε δ y ≤ c - ε := by
      have hgx : g x = modifiedNormalForm hk c ε δ y := by
        rw [← hsymm]
        dsimp [g, morseModifiedFunction]
        rw [← hxy, if_pos (χ.map_source (hχsrc y hy)), χ.left_inv (hχsrc y hy)]
        rw [if_pos (by simpa [ball] using hy)]
      rw [← hgx]
      exact hx
    have hzmem := modifiedCollarRetraction_mem_lowerCellUnion hk c ε hε y
    have hleNorm : morseNorm n (modifiedCollarRetraction hk c ε y) ≤ morseNorm n y := by
      have h1 := morseNorm_modifiedCollarHomotopy_le hk c ε (by norm_num : (0 : ℝ) ≤ 1)
        (by norm_num : (1 : ℝ) ≤ 1) y
      simpa [modifiedCollarHomotopy_one hk c ε y] using h1
    have hleR : morseNorm n (modifiedCollarRetraction hk c ε y) ≤ R := le_trans hleNorm hy
    dsimp [morseModifiedRetraction]
    rw [hsymm]
    rw [if_pos ⟨y, hy, hxy⟩]
    rcases hzmem with hzlow | hzcell
    · have hfz : f (χ (modifiedCollarRetraction hk c ε y)) ≤ c - ε := by
        rw [hnorm (modifiedCollarRetraction hk c ε y) hleR]
        exact hzlow
      exact Or.inl hfz
    · rcases hzcell with ⟨u, hu⟩
      exact Or.inr ⟨modifiedCollarRetraction hk c ε y, ⟨u, hu⟩, rfl⟩
  · dsimp [morseModifiedRetraction]
    rw [if_neg hC]
    have hgx : g x = f x := by
      dsimp [g, morseModifiedFunction]
      by_cases hxt : x ∈ χ.target
      · rw [if_pos hxt]
        have hle' : ¬ morseNorm n (χ.symm x) ≤ R := by
          intro hle
          apply hC
          exact ⟨χ.symm x, hle, χ.right_inv hxt⟩
        rw [if_neg hle']
      · rw [if_neg hxt]
    exact Or.inl (by
      change f x ≤ c - ε
      rw [← hgx]
      exact hx)

theorem morseModifiedRetractionHomotopy_mem_sublevel {n k : ℕ} (hk : k ≤ n) (c ε δ R : ℝ)
    (hε : 0 < ε) (hδ : 0 < δ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    (χ : OpenPartialHomeomorph (MorseModel n) M) (f : M → ℝ)
    (hχsrc : ∀ y : MorseModel n, morseNorm n y ≤ R → y ∈ χ.source)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) {x : M}
    (hx : morseModifiedFunction (H := H) (M := M) hk c ε δ R χ f x ≤ c - ε) :
    morseModifiedFunction (H := H) (M := M) hk c ε δ R χ f
      (morseModifiedRetractionHomotopy (H := H) (M := M) hk c ε R χ t x) ≤ c - ε := by
  let g : M → ℝ := morseModifiedFunction (H := H) (M := M) hk c ε δ R χ f
  let ball : Set (MorseModel n) := {y : MorseModel n | morseNorm n y ≤ R}
  change g x ≤ c - ε at hx
  by_cases hC : x ∈ χ '' ball
  · rcases hC with ⟨y, hy, hxy⟩
    have hsymm : χ.symm x = y := by
      rw [← hxy]
      exact χ.left_inv (hχsrc y hy)
    have hmod : modifiedNormalForm hk c ε δ y ≤ c - ε := by
      have hgx : g x = modifiedNormalForm hk c ε δ y := by
        rw [← hsymm]
        dsimp [g, morseModifiedFunction]
        rw [← hxy, if_pos (χ.map_source (hχsrc y hy)), χ.left_inv (hχsrc y hy)]
        rw [if_pos (by simpa [ball] using hy)]
      rw [← hgx]
      exact hx
    have hnormLe : morseNorm n (modifiedCollarHomotopy hk c ε t y) ≤ R :=
      le_trans (morseNorm_modifiedCollarHomotopy_le hk c ε ht0 ht1 y) hy
    have hval : morseModifiedFunction (H := H) (M := M) hk c ε δ R χ f
        (morseModifiedRetractionHomotopy (H := H) (M := M) hk c ε R χ t x) =
        modifiedNormalForm hk c ε δ (modifiedCollarHomotopy hk c ε t y) := by
      have hzsrc : modifiedCollarHomotopy hk c ε t y ∈ χ.source :=
        hχsrc (modifiedCollarHomotopy hk c ε t y) hnormLe
      dsimp [morseModifiedRetractionHomotopy]
      rw [if_pos ⟨y, hy, hxy⟩]
      rw [hsymm]
      dsimp [morseModifiedFunction]
      rw [if_pos (χ.map_source hzsrc)]
      rw [χ.left_inv hzsrc]
      rw [if_pos (by simpa [ball] using hnormLe)]
    rw [hval]
    exact modifiedCollarHomotopy_mem_sublevel hk c ε δ hε hδ ht0 ht1 hmod
  · dsimp [morseModifiedRetractionHomotopy]
    rw [if_neg hC]
    exact hx

theorem lowerUnionCellImage_subset_modifiedSublevel {n k : ℕ} (hk : k ≤ n) (c ε δ R : ℝ)
    (hε : 0 < ε) (hδ : 0 < δ) (hεR : Real.sqrt (2 * ε) ≤ R)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    (χ : OpenPartialHomeomorph (MorseModel n) M) (f : M → ℝ)
    (hnorm : ∀ y : MorseModel n, morseNorm n y ≤ R → f (χ y) = morseNormalForm hk c y)
    (hχsrc : ∀ y : MorseModel n, morseNorm n y ≤ R → y ∈ χ.source) :
    {x : M | x ∈ sublevel f (c - ε) ∪ χ '' (Set.range (fun z : ClosedCell k =>
      cellMap (Real.sqrt (2 * ε)) (z : EuclideanSpace ℝ (Fin k))))} ⊆
    {x : M | morseModifiedFunction (H := H) (M := M) hk c ε δ R χ f x ≤ c - ε} := by
  let g : M → ℝ := morseModifiedFunction (H := H) (M := M) hk c ε δ R χ f
  intro x hx
  change g x ≤ c - ε
  rcases hx with hflow | hcell
  · have hle : g x ≤ f x := morseModifiedFunction_le_f (H := H) (M := M) hk c ε δ R hε χ f hnorm x
    exact le_trans hle hflow
  · rcases hcell with ⟨y, hy, hxy⟩
    rcases hy with ⟨u, hu⟩
    have hyb : morseNorm n y ≤ R := by
      rw [← hu]
      exact norm_cellMap_le hk ε R hεR (u : EuclideanSpace ℝ (Fin k)) u.2
    have hysrc : y ∈ χ.source := hχsrc y hyb
    have hgx : g x = modifiedNormalForm hk c ε δ y := by
      dsimp [g, morseModifiedFunction]
      rw [← hxy, if_pos (χ.map_source hysrc), χ.left_inv hysrc, if_pos hyb]
    rw [hgx]
    rw [← hu]
    exact modifiedNormalForm_cell_mem_lower hk c ε δ hε hδ u

theorem morseModifiedRetraction_eq_self_of_mem_lowerUnion {n k : ℕ} (hk : k ≤ n) (c ε R : ℝ)
    (hε : 0 < ε) (hεR : Real.sqrt (2 * ε) ≤ R)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    (χ : OpenPartialHomeomorph (MorseModel n) M) (f : M → ℝ)
    (hnorm : ∀ y : MorseModel n, morseNorm n y ≤ R → f (χ y) = morseNormalForm hk c y)
    (hχsrc : ∀ y : MorseModel n, morseNorm n y ≤ R → y ∈ χ.source)
    {x : M}
    (hx : x ∈ sublevel f (c - ε) ∪ χ '' (Set.range (fun z : ClosedCell k =>
      cellMap (Real.sqrt (2 * ε)) (z : EuclideanSpace ℝ (Fin k))))) :
    morseModifiedRetraction (H := H) (M := M) hk c ε R χ x = x := by
  let ball : Set (MorseModel n) := {y : MorseModel n | morseNorm n y ≤ R}
  rcases hx with hflow | hcell
  · by_cases hC : x ∈ χ '' ball
    · rcases hC with ⟨y, hy, hxy⟩
      have hfy : morseNormalForm hk c y ≤ c - ε := by
        have hfx : f (χ y) ≤ c - ε := by
          simpa [hxy] using hflow
        rwa [hnorm y hy] at hfx
      have hsymm : χ.symm x = y := by
        rw [← hxy]
        exact χ.left_inv (hχsrc y hy)
      dsimp [morseModifiedRetraction]
      rw [if_pos ⟨y, hy, hxy⟩]
      dsimp [modifiedCollarRetraction]
      rw [if_pos (by simpa [hsymm] using hfy)]
      exact χ.right_inv (by
        rw [← hxy]
        exact χ.map_source (hχsrc y hy))
    · dsimp [morseModifiedRetraction]
      rw [if_neg hC]
  · rcases hcell with ⟨y, hy, hxy⟩
    have hyCell : y ∈ Set.range (fun z : ClosedCell k =>
        cellMap (Real.sqrt (2 * ε)) (z : EuclideanSpace ℝ (Fin k))) := hy
    rcases hy with ⟨u, hu⟩
    have hyb : morseNorm n y ≤ R := by
      rw [← hu]
      exact norm_cellMap_le hk ε R hεR (u : EuclideanSpace ℝ (Fin k)) u.2
    have hfix : modifiedCollarRetraction hk c ε y = y := by
      have h1 := modifiedCollarHomotopy_fix_cell hk c ε hε (t := 1) hyCell
      simpa [modifiedCollarHomotopy_one hk c ε y] using h1
    have hsymm : χ.symm x = y := by
      rw [← hxy]
      exact χ.left_inv (hχsrc y hyb)
    dsimp [morseModifiedRetraction]
    rw [if_pos ⟨y, hyb, hxy⟩]
    rw [hsymm, hfix]
    exact hxy

noncomputable def morseModifiedLowerSublevelHomotopyEquiv {n k : ℕ} (hk : k ≤ n) (c ε δ R : ℝ)
    (hε : 0 < ε) (hδ : 0 < δ) (hR : 4 * ε + 9 * δ ^ 2 / 4 < R ^ 2) (hRpos : 0 < R)
    (hεR : Real.sqrt (2 * ε) ≤ R)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
    (χ : OpenPartialHomeomorph (MorseModel n) M) (f : M → ℝ)
    (hg : Continuous (morseModifiedFunction (H := H) (M := M) hk c ε δ R χ f))
    (hnorm : ∀ y : MorseModel n, morseNorm n y ≤ R → f (χ y) = morseNormalForm hk c y)
    (hχsrc : ∀ y : MorseModel n, morseNorm n y ≤ R → y ∈ χ.source) :
    ContinuousMap.HomotopyEquiv
      (SublevelSpace (morseModifiedFunction (H := H) (M := M) hk c ε δ R χ f) (c - ε))
      {x : M // x ∈ sublevel f (c - ε) ∪ χ '' (Set.range (fun z : ClosedCell k =>
        cellMap (Real.sqrt (2 * ε)) (z : EuclideanSpace ℝ (Fin k))))} := by
  let cellRange : Set (MorseModel n) := Set.range (fun z : ClosedCell k =>
    cellMap (Real.sqrt (2 * ε)) (z : EuclideanSpace ℝ (Fin k)))
  let A : Type := SublevelSpace (morseModifiedFunction (H := H) (M := M) hk c ε δ R χ f) (c - ε)
  let B : Type := {x : M // x ∈ sublevel f (c - ε) ∪ χ '' cellRange}
  have hretrCont : Continuous (fun x : SublevelSpace (morseModifiedFunction (H := H) (M := M)
      hk c ε δ R χ f) (c - ε) =>
      morseModifiedRetraction (H := H) (M := M) hk c ε R χ x.1) := by
    have hcont := continuousOn_morseModifiedRetraction (H := H) (M := M) hk c ε δ R hε hδ hR hRpos
      χ f hg hχsrc
    exact (continuousOn_iff_continuous_restrict).1 (by
      simpa [SublevelSpace, sublevel] using hcont)
  let toFun : C(SublevelSpace (morseModifiedFunction (H := H) (M := M) hk c ε δ R χ f) (c - ε),
      {x : M // x ∈ sublevel f (c - ε) ∪ χ '' cellRange}) :=
    ContinuousMap.mk
      (fun x : SublevelSpace (morseModifiedFunction (H := H) (M := M) hk c ε δ R χ f) (c - ε) =>
        ⟨morseModifiedRetraction (H := H) (M := M) hk c ε R χ x.1,
          morseModifiedRetraction_mem_lowerUnion (H := H) (M := M) hk c ε δ R hε χ f hnorm hχsrc x.2⟩)
      (by
        exact Continuous.subtype_mk hretrCont (by
          intro x
          exact morseModifiedRetraction_mem_lowerUnion (H := H) (M := M) hk c ε δ R hε χ f hnorm hχsrc x.2))
  let invFun : C({x : M // x ∈ sublevel f (c - ε) ∪ χ '' cellRange},
      SublevelSpace (morseModifiedFunction (H := H) (M := M) hk c ε δ R χ f) (c - ε)) :=
    ContinuousMap.mk
      (fun x : {x : M // x ∈ sublevel f (c - ε) ∪ χ '' cellRange} =>
        ⟨x.1, (lowerUnionCellImage_subset_modifiedSublevel (H := H) (M := M) hk c ε δ R hε hδ hεR
          χ f hnorm hχsrc) x.2⟩)
      (by
        exact Continuous.subtype_mk continuous_subtype_val (by
          intro x
          exact lowerUnionCellImage_subset_modifiedSublevel (H := H) (M := M) hk c ε δ R hε hδ hεR
            χ f hnorm hχsrc x.2))
  let leftHomo : ContinuousMap.Homotopy (invFun.comp toFun)
      (ContinuousMap.id (SublevelSpace (morseModifiedFunction (H := H) (M := M) hk c ε δ R χ f)
        (c - ε))) :=
    { toFun := ContinuousMap.mk
        (fun p : Set.Icc (0 : ℝ) 1 × SublevelSpace (morseModifiedFunction (H := H) (M := M)
            hk c ε δ R χ f) (c - ε) =>
          (⟨morseModifiedRetractionHomotopy (H := H) (M := M) hk c ε R χ (1 - (p.1 : ℝ)) p.2.1,
            by
              have ht0 : 0 ≤ 1 - (p.1 : ℝ) := by exact sub_nonneg.mpr p.1.2.2
              have ht1 : 1 - (p.1 : ℝ) ≤ 1 := by
                exact sub_le_self (a := (1 : ℝ)) (b := (p.1 : ℝ)) p.1.2.1
              exact morseModifiedRetractionHomotopy_mem_sublevel (H := H) (M := M) hk c ε δ R hε hδ
                χ f hχsrc ht0 ht1 p.2.2⟩ :
            SublevelSpace (morseModifiedFunction (H := H) (M := M) hk c ε δ R χ f) (c - ε)))
        (by
          have hcontH : Continuous (fun p : Set.Icc (0 : ℝ) 1 ×
              SublevelSpace (morseModifiedFunction (H := H) (M := M) hk c ε δ R χ f) (c - ε) =>
              morseModifiedRetractionHomotopy (H := H) (M := M) hk c ε R χ (1 - (p.1 : ℝ)) p.2.1) := by
            have hcont := continuousOn_morseModifiedRetractionHomotopy (H := H) (M := M)
              hk c ε δ R hε hδ hR hRpos χ f hg hχsrc
            have hembed : Continuous (fun p : Set.Icc (0 : ℝ) 1 ×
                SublevelSpace (morseModifiedFunction (H := H) (M := M) hk c ε δ R χ f) (c - ε) =>
                (p.1, p.2.1)) := by
              fun_prop
            have hmem : ∀ p : Set.Icc (0 : ℝ) 1 ×
                SublevelSpace (morseModifiedFunction (H := H) (M := M) hk c ε δ R χ f) (c - ε),
                (p.1, p.2.1) ∈ (Set.univ : Set (Set.Icc (0 : ℝ) 1)) ×ˢ
                  {x : M | morseModifiedFunction (H := H) (M := M) hk c ε δ R χ f x ≤ c - ε} := by
              intro p
              exact ⟨trivial, by simp [sublevel]⟩
            simpa [Function.comp_def] using (hcont.comp_continuous hembed hmem)
          exact Continuous.subtype_mk
            (p := fun x : M => x ∈ sublevel (morseModifiedFunction (H := H) (M := M) hk c ε δ R χ f)
              (c - ε))
            hcontH (by
            intro p
            change morseModifiedFunction (H := H) (M := M) hk c ε δ R χ f
              (morseModifiedRetractionHomotopy (H := H) (M := M) hk c ε R χ (1 - (p.1 : ℝ)) p.2.1) ≤
              c - ε
            have ht0 : 0 ≤ 1 - (p.1 : ℝ) := by exact sub_nonneg.mpr p.1.2.2
            have ht1 : 1 - (p.1 : ℝ) ≤ 1 := by
              exact sub_le_self (a := (1 : ℝ)) (b := (p.1 : ℝ)) p.1.2.1
            exact morseModifiedRetractionHomotopy_mem_sublevel (H := H) (M := M) hk c ε δ R hε hδ
              χ f hχsrc ht0 ht1 p.2.2))
      map_zero_left := by
        intro x
        apply Subtype.ext
        simpa [toFun, invFun] using
          (morseModifiedRetractionHomotopy_one (H := H) (M := M) hk c ε R χ x.1)
      map_one_left := by
        intro x
        apply Subtype.ext
        simpa [toFun, invFun] using
          (morseModifiedRetractionHomotopy_zero (H := H) (M := M) hk c ε R χ hχsrc x.1) }
  let rightHomo : ContinuousMap.Homotopy (toFun.comp invFun)
      (ContinuousMap.id {x : M // x ∈ sublevel f (c - ε) ∪ χ '' cellRange}) :=
    { toFun := ContinuousMap.mk
        (fun p : Set.Icc (0 : ℝ) 1 × {x : M // x ∈ sublevel f (c - ε) ∪ χ '' cellRange} => p.2)
        (by fun_prop)
      map_zero_left := by
        intro x
        apply Subtype.ext
        simpa [toFun, invFun] using
          ((morseModifiedRetraction_eq_self_of_mem_lowerUnion (H := H) (M := M) hk c ε R hε hεR
            χ f hnorm hχsrc x.2).symm)
      map_one_left := by
        intro x
        rfl }
  exact { toFun := toFun, invFun := invFun, left_inv := ⟨leftHomo⟩, right_inv := ⟨rightHomo⟩ }

theorem morseModifiedLowerSublevelHomotopyEquiv_lower {n k : ℕ} (hk : k ≤ n) (c ε δ R : ℝ)
    (hε : 0 < ε) (hδ : 0 < δ) (hR : 4 * ε + 9 * δ ^ 2 / 4 < R ^ 2) (hRpos : 0 < R)
    (hεR : Real.sqrt (2 * ε) ≤ R)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
    (χ : OpenPartialHomeomorph (MorseModel n) M) (f : M → ℝ)
    (hg : Continuous (morseModifiedFunction (H := H) (M := M) hk c ε δ R χ f))
    (hnorm : ∀ y : MorseModel n, morseNorm n y ≤ R → f (χ y) = morseNormalForm hk c y)
    (hχsrc : ∀ y : MorseModel n, morseNorm n y ≤ R → y ∈ χ.source) :
    (∀ x : SublevelSpace f (c - ε),
      ((morseModifiedLowerSublevelHomotopyEquiv hk c ε δ R hε hδ hR hRpos hεR χ f hg hnorm hχsrc).toFun
        ⟨x.1, le_trans (morseModifiedFunction_le_f (H := H) (M := M) hk c ε δ R hε χ f hnorm x.1)
          (by change f x.1 ≤ c - ε; exact x.2)⟩).1 = x.1) ∧
    (∀ x : SublevelSpace f (c - ε),
      ((morseModifiedLowerSublevelHomotopyEquiv hk c ε δ R hε hδ hR hRpos hεR χ f hg hnorm hχsrc).invFun
        ⟨x.1, Or.inl x.2⟩).1 = x.1) := by
  constructor
  · intro x
    change morseModifiedRetraction (H := H) (M := M) hk c ε R χ x.1 = x.1
    exact (morseModifiedRetraction_eq_self_of_mem_lowerUnion (H := H) (M := M) hk c ε R hε hεR
      χ f hnorm hχsrc (Or.inl x.2))
  · intro x
    change x.1 = x.1
    rfl

noncomputable def sublevelCellAdjunctionBaseCommutingHomotopyEquivOfMorseChartAndDiffeomorph {n : ℕ} {H : Type}
    [TopologicalSpace H] {M : Type} [TopologicalSpace M]
    [ChartedSpace H M] [T2Space M] (I : ModelWithCorners ℝ (MorseModel n) H) [I.Boundaryless]
    [IsManifold I (⊤ : WithTop ℕ∞) M] (f : M → ℝ) (hf : ContMDiff I 𝓘(ℝ, ℝ) (⊤ : WithTop ℕ∞) f)
    (c : ℝ) (k : ℕ) (hk : k ≤ n)
    (data : MorseChart n k hk c I f)
    (g : M → ℝ) (hg : ContMDiff I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) g)
    (hg_le : ∀ x : M, g x ≤ f x)
    (hlow : ContinuousMap.HomotopyEquiv (SublevelSpace g (c - data.ε))
      {x : M // x ∈ sublevel f (c - data.ε) ∪ data.χ '' (Set.range (fun z : ClosedCell k =>
        cellMap (Real.sqrt (2 * data.ε)) (z : EuclideanSpace ℝ (Fin k))))})
    (hcell : cellImage hk c data = data.χ '' (Set.range (fun z : ClosedCell k =>
      cellMap (Real.sqrt (2 * data.ε)) (z : EuclideanSpace ℝ (Fin k)))))
    (hlow_lower : ∀ x : SublevelSpace f (c - data.ε),
      ((hlow.toFun ⟨x.1, le_trans (hg_le x.1) (by change f x.1 ≤ c - data.ε; exact x.2)⟩).1 : M) =
        x.1)
    (hlow_inv_lower : ∀ x : SublevelSpace f (c - data.ε),
      ((hlow.invFun ⟨x.1, Or.inl x.2⟩).1 : M) = x.1)
    (hgup : {x : M | g x ≤ c + data.ε} = sublevel f (c + data.ε))
    (v : (x : M) → TangentSpace I x)
    (hv : ContMDiff I (I.prod 𝓘(ℝ, MorseModel n)) ∞
      (fun x : M => (⟨x, v x⟩ : TangentBundle I M)))
    (hsupp : IsCompact (tsupport v))
    (hcomplete : ∀ x : M, ∃ γ : ℝ → M, γ 0 = x ∧ IsMIntegralCurve γ v)
    (hrate : ∀ x,
      -1 ≤ (NormedSpace.fromTangentSpace (g x)) ((mfderiv I 𝓘(ℝ, ℝ) g x) (v x)) ∧
      (NormedSpace.fromTangentSpace (g x)) ((mfderiv I 𝓘(ℝ, ℝ) g x) (v x)) ≤ 0)
    (Φ : Diffeomorph I I M M (↑(⊤ : ℕ∞) : WithTop ℕ∞))
    (hflow : Φ.toEquiv '' sublevel g (c - data.ε) = sublevel g (c + data.ε))
    (htie : ∀ x : M, Φ.toEquiv x = curveAt v hcomplete x (c - data.ε - (c + data.ε))) :
    {e : DifferentialGeometry.Topology.Homotopy.BaseCommutingHomotopyEquiv
        (B := SublevelSpace f (c - data.ε)) (X := SublevelSpace f (c + data.ε))
        (Y := CellAdjunctionSpace k (cellAttachingMap hk c data)) //
      e.toBase = sublevelInclusion f (by linarith [data.hεpos]) ∧
      e.fromBase = ContinuousMap.mk
        (adjunctionLower (i := cellBoundaryInclusion k) (cellAttachingMap hk c data))
        (continuous_adjunctionLower (i := cellBoundaryInclusion k) (cellAttachingMap hk c data))} := by
  let E : Set M := cellImage hk c data
  let φ : C(CellBoundary k, SublevelSpace f (c - data.ε)) := cellAttachingMap hk c data
  let U₀ : Set M := data.χ '' (Set.range (fun z : ClosedCell k =>
    cellMap (Real.sqrt (2 * data.ε)) (z : EuclideanSpace ℝ (Fin k))))
  have hset : sublevel f (c - data.ε) ∪ U₀ = sublevel f (c - data.ε) ∪ E := by
    simp [E, U₀, hcell]
  let hcast : {x : M // x ∈ sublevel f (c - data.ε) ∪ U₀} ≃ₜ
      {x : M // x ∈ sublevel f (c - data.ε) ∪ E} := subtypeSetHomeo hset
  let hAdj : CellAdjunctionSpace k φ ≃ₜ {x : M // x ∈ sublevel f (c - data.ε) ∪ E} := by
    simpa [E, φ] using (cellAdjunctionSpaceHomeomorphLowerUnion (I := I) (hf := hf) (data := data))
  have hflow' : Φ.toEquiv '' sublevel g (c - data.ε) = sublevel f (c + data.ε) := by
    change (Φ.toEquiv '' {x : M | g x ≤ c - data.ε}) = {x : M | g x ≤ c + data.ε} at hflow
    rw [hgup] at hflow
    exact hflow
  let hflowHomeo : SublevelSpace g (c - data.ε) ≃ₜ SublevelSpace f (c + data.ε) :=
    { toEquiv :=
        { toFun := fun x : SublevelSpace g (c - data.ε) => ⟨Φ.toEquiv x.1, by
            rw [← hflow']
            exact ⟨x.1, x.2, rfl⟩⟩
          invFun := fun y : SublevelSpace f (c + data.ε) => ⟨Φ.toEquiv.symm y.1, by
            have hy' : y.1 ∈ Φ.toEquiv '' sublevel g (c - data.ε) := by
              have hmem : y.1 ∈ sublevel f (c + data.ε) := y.2
              exact hflow'.symm ▸ hmem
            rcases hy' with ⟨z, hz, hzΦ⟩
            have hz' : Φ.toEquiv.symm y.1 = z := by
              rw [← hzΦ]
              exact Φ.toEquiv.left_inv z
            change g (Φ.toEquiv.symm y.1) ≤ c - data.ε
            simpa [hz'] using hz⟩
          left_inv := by
            intro x
            apply Subtype.ext
            exact Φ.toEquiv.left_inv x.1
          right_inv := by
            intro y
            apply Subtype.ext
            exact Φ.toEquiv.right_inv y.1 }
      continuous_toFun := by
        have hc : Continuous (fun x : SublevelSpace g (c - data.ε) => Φ.toEquiv x.1) :=
          Φ.contMDiff_toFun.continuous.comp continuous_subtype_val
        exact Continuous.subtype_mk hc (by intro x; rw [← hflow']; exact ⟨x.1, x.2, rfl⟩)
      continuous_invFun := by
        have hc : Continuous (fun y : SublevelSpace f (c + data.ε) => Φ.toEquiv.symm y.1) :=
          Φ.contMDiff_invFun.continuous.comp continuous_subtype_val
        exact Continuous.subtype_mk hc (by intro y; exact (by
          have hy' : y.1 ∈ Φ.toEquiv '' sublevel g (c - data.ε) := by
            have hmem : y.1 ∈ sublevel f (c + data.ε) := y.2
            exact hflow'.symm ▸ hmem
          rcases hy' with ⟨z, hz, hzΦ⟩
          have hz' : Φ.toEquiv.symm y.1 = z := by
            rw [← hzΦ]
            exact Φ.toEquiv.left_inv z
          change g (Φ.toEquiv.symm y.1) ≤ c - data.ε
          simpa [hz'] using hz)) }
  let hlowE : ContinuousMap.HomotopyEquiv (SublevelSpace g (c - data.ε))
      {x : M // x ∈ sublevel f (c - data.ε) ∪ E} :=
    hlow.trans hcast.toHomotopyEquiv
  let hAdjE : ContinuousMap.HomotopyEquiv
      {x : M // x ∈ sublevel f (c - data.ε) ∪ E}
      (CellAdjunctionSpace k φ) := hAdj.symm.toHomotopyEquiv
  let e : ContinuousMap.HomotopyEquiv (SublevelSpace f (c + data.ε))
      (CellAdjunctionSpace k φ) :=
    (hlowE.symm.trans hflowHomeo.toHomotopyEquiv).symm.trans hAdjE
  let ι : C(SublevelSpace f (c - data.ε), SublevelSpace f (c + data.ε)) :=
    sublevelInclusion f (by linarith [data.hεpos])
  let ι₀ : C(SublevelSpace f (c - data.ε), SublevelSpace g (c - data.ε)) :=
    ContinuousMap.mk (fun x => ⟨x.1, le_trans (hg_le x.1) (by change f x.1 ≤ c - data.ε; exact x.2)⟩)
      (by exact Continuous.subtype_mk continuous_subtype_val (by
        intro x
        exact le_trans (hg_le x.1) (by change f x.1 ≤ c - data.ε; exact x.2)))
  let j : C(SublevelSpace f (c - data.ε), CellAdjunctionSpace k φ) :=
    ContinuousMap.mk (adjunctionLower (i := cellBoundaryInclusion k) φ)
      (continuous_adjunctionLower (i := cellBoundaryInclusion k) φ)
  have hAdjLower : ∀ x : SublevelSpace f (c - data.ε),
      hAdj (adjunctionLower (i := cellBoundaryInclusion k) φ x) = ⟨x.1, Or.inl x.2⟩ := by
    intro x
    change adjunctionRealization (sublevel f (c - data.ε)) (cellBoundaryInclusion k)
      (cellEmbedding hk c data)
      (fun b : CellBoundary k => cellAttachingMap hk c data b) (by intro b; rfl)
      (adjunctionLower (i := cellBoundaryInclusion k) (cellAttachingMap hk c data) x) =
      ⟨x.1, Or.inl x.2⟩
    exact adjunctionRealization_lower (i := cellBoundaryInclusion k)
      (c := cellEmbedding hk c data) (by intro b; rfl) x
  have hv1 : ContMDiff I (I.prod 𝓘(ℝ, MorseModel n)) (1 : WithTop ℕ∞)
      (fun x : M => (⟨x, v x⟩ : TangentBundle I M)) :=
    hv.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ ∞)
  have hflowJoint : Continuous (fun p : ℝ × M => curveAt v hcomplete p.2 p.1) :=
    continuous_globalFlow_of_compactSupport v hv hsupp
  have hrate_flow : ∀ x : M, ∀ s : ℝ, 0 ≤ s → g x - s ≤ g (curveAt v hcomplete x s) ∧
      g (curveAt v hcomplete x s) ≤ g x := by
    intro x s hs
    have hrb := f_rate_bounds_of_integralCurve g hg v hrate
      (hγ := curveAt_integralCurve v hcomplete x) (t := s) hs
    simpa [curveAt_zero v hcomplete x] using hrb
  let t2 : ℝ := 2 * data.ε
  have ht2pos : 0 < t2 := by dsimp [t2]; nlinarith [data.hεpos]
  have ht2_def : t2 = c + data.ε - (c - data.ε) := by dsimp [t2]; ring
  have htie_neg : ∀ y : M, Φ.toEquiv y = curveAt v hcomplete y (-t2) := by
    intro y
    have h := htie y
    have hsub : c - data.ε - (c + data.ε) = -t2 := by dsimp [t2]; ring
    rwa [hsub] at h
  have htie_inv : ∀ y : M, Φ.toEquiv.symm y = curveAt v hcomplete y t2 := by
    intro y
    have hΦ : Φ.toEquiv (curveAt v hcomplete y t2) = y := by
      rw [htie_neg (curveAt v hcomplete y t2)]
      have hh := curveAt_add v hv1 hcomplete y t2 (-t2)
      rw [show t2 + -t2 = 0 by ring] at hh
      rw [← hh]
      exact curveAt_zero v hcomplete y
    have hh2 := congrArg Φ.toEquiv.symm hΦ
    rw [← hh2]
    exact Φ.toEquiv.left_inv (curveAt v hcomplete y t2)
  let hflowHomo : ContinuousMap.Homotopy
      ((hflowHomeo.symm : C(SublevelSpace f (c + data.ε), SublevelSpace g (c - data.ε))).comp ι) ι₀ :=
    let hmap : C(Set.Icc (0 : ℝ) 1 × SublevelSpace f (c - data.ε),
        SublevelSpace g (c - data.ε)) :=
      ContinuousMap.mk
        (fun p : Set.Icc (0 : ℝ) 1 × SublevelSpace f (c - data.ε) =>
          ⟨curveAt v hcomplete p.2.1 (t2 * (1 - (p.1 : ℝ))), by
            have hs : 0 ≤ t2 * (1 - (p.1 : ℝ)) := by
              nlinarith [p.1.2.2, ht2pos]
            have hb := (hrate_flow p.2.1 (t2 * (1 - (p.1 : ℝ))) hs).2
            change g (curveAt v hcomplete p.2.1 (t2 * (1 - (p.1 : ℝ)))) ≤ c - data.ε
            exact le_trans hb (le_trans (hg_le p.2.1)
              (by change f p.2.1 ≤ c - data.ε; exact p.2.2))⟩)
        (by
          have hreparam : Continuous (fun p : Set.Icc (0 : ℝ) 1 × SublevelSpace f (c - data.ε) =>
              (t2 * (1 - (p.1 : ℝ)), p.2.1)) := by
            fun_prop
          have hmain : Continuous (fun p : Set.Icc (0 : ℝ) 1 × SublevelSpace f (c - data.ε) =>
              curveAt v hcomplete p.2.1 (t2 * (1 - (p.1 : ℝ)))) := by
            have hc := hflowJoint.comp hreparam
            simpa [Function.comp_def] using hc
          exact Continuous.subtype_mk hmain (by
            intro p
            have hs : 0 ≤ t2 * (1 - (p.1 : ℝ)) := by
              nlinarith [p.1.2.2, ht2pos]
            have hb := (hrate_flow p.2.1 (t2 * (1 - (p.1 : ℝ))) hs).2
            change g (curveAt v hcomplete p.2.1 (t2 * (1 - (p.1 : ℝ)))) ≤ c - data.ε
            exact le_trans hb (le_trans (hg_le p.2.1)
              (by change f p.2.1 ≤ c - data.ε; exact p.2.2))))
    { toFun := hmap
      map_zero_left := by
        intro x
        apply Subtype.ext
        change curveAt v hcomplete x.1 (t2 * (1 - (0 : ℝ))) =
          (hflowHomeo.symm (ι x)).1
        simp only [t2, sub_zero, mul_one]
        have hsymm : (hflowHomeo.symm (ι x)).1 = Φ.toEquiv.symm x.1 := by
          rfl
        rw [hsymm]
        exact (htie_inv x.1).symm
      map_one_left := by
        intro x
        apply Subtype.ext
        change curveAt v hcomplete x.1 (t2 * (1 - (1 : ℝ))) = x.1
        simp [curveAt_zero v hcomplete x.1] }
  have hlow_fix_map : hlowE.toFun.comp ι₀ = ⟨fun x => ⟨x.1, Or.inl x.2⟩, by
      exact Continuous.subtype_mk continuous_subtype_val (by intro x; exact Or.inl x.2)⟩ := by
    ext x
    change (hcast.toFun (hlow.toFun (ι₀ x))).1 = x.1
    dsimp [hcast, subtypeSetHomeo]
    exact hlow_lower x
  have hlow_inv_map : hlowE.invFun.comp ⟨fun x => ⟨x.1, Or.inl x.2⟩, by
      exact Continuous.subtype_mk continuous_subtype_val (by intro x; exact Or.inl x.2)⟩ = ι₀ := by
    ext x
    change (hlow.invFun (hcast.invFun ⟨x.1, Or.inl x.2⟩)).1 = x.1
    dsimp [hcast, subtypeSetHomeo]
    simpa using (hlow_inv_lower x)
  have hAdj_map : hAdjE.toFun.comp ⟨fun x => ⟨x.1, Or.inl x.2⟩, by
      exact Continuous.subtype_mk continuous_subtype_val (by intro x; exact Or.inl x.2)⟩ = j := by
    ext x
    change hAdj.symm ⟨x.1, Or.inl x.2⟩ = adjunctionLower (i := cellBoundaryInclusion k) φ x
    have hb : hAdj.symm ⟨x.1, Or.inl x.2⟩ =
        adjunctionLower (i := cellBoundaryInclusion k) φ ⟨x.1, x.2⟩ := by
      have hleft := hAdj.left_inv (adjunctionLower (i := cellBoundaryInclusion k) φ ⟨x.1, x.2⟩)
      simpa [hAdjLower ⟨x.1, x.2⟩] using hleft
    rw [hb]
  let leftHomo : ContinuousMap.Homotopy (e.toFun.comp ι) j := by
    have hstep := (ContinuousMap.Homotopy.refl (hAdjE.toFun.comp hlowE.toFun)).comp hflowHomo
    refine hstep.cast ?_ ?_
    · ext x
      rfl
    · change hAdjE.toFun.comp (hlowE.toFun.comp ι₀) = j
      rw [hlow_fix_map]
      exact hAdj_map
  let rightHomo : ContinuousMap.Homotopy (e.invFun.comp j) ι := by
    have hstep := (ContinuousMap.Homotopy.refl
      (hflowHomeo : C(SublevelSpace g (c - data.ε), SublevelSpace f (c + data.ε)))).comp hflowHomo
    have hright_id : (hflowHomeo : C(SublevelSpace g (c - data.ε), SublevelSpace f (c + data.ε))).comp
        ((hflowHomeo.symm : C(SublevelSpace f (c + data.ε), SublevelSpace g (c - data.ε))).comp ι) = ι := by
      ext x
      exact congrArg Subtype.val (hflowHomeo.right_inv (ι x))
    refine (hstep.cast hright_id ?_).symm
    · ext x
      change (hflowHomeo.toFun (ι₀ x)).1 = (e.invFun (j x)).1
      have h1 : (e.invFun (j x)).1 = (hflowHomeo.toFun (hlowE.invFun (hAdj (j x)))).1 := by
        rfl
      rw [h1]
      have h2 : hAdj (j x) = ⟨x.1, Or.inl x.2⟩ := by
        change hAdj (adjunctionLower (i := cellBoundaryInclusion k) φ x) = ⟨x.1, Or.inl x.2⟩
        exact hAdjLower x
      rw [h2]
      change Φ.toEquiv x.1 = Φ.toEquiv (hlow.invFun ⟨x.1, Or.inl x.2⟩).1
      exact congrArg Φ.toEquiv (hlow_inv_lower x).symm
  exact
    ⟨{ toBase := ι
       fromBase := j
       toHomotopyEquiv := e
       left_comm := leftHomo
       right_comm := rightHomo }, by
      exact ⟨by rfl, by rfl⟩⟩

theorem one_critical_point_cell_attachment {n : ℕ} {H : Type} [TopologicalSpace H] {M : Type}
    [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [SigmaCompactSpace M]
    (I : ModelWithCorners ℝ (MorseModel n) H) [I.Boundaryless]
    [IsManifold I (⊤ : WithTop ℕ∞) M] (f : M → ℝ)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) (⊤ : WithTop ℕ∞) f)
    (p : M) (c : ℝ) (k : ℕ) (hk : k ≤ n)
    (hnd : IsNondegenerateCriticalPointAt I f p)
    (hindex : sigNeg (chartHessianAt (g := fun y => f ((extChartAt I p).symm y)) (extChartAt I p p)) = k)
    (hfp : f p = c)
    (a : ℝ) (ha : 0 < a)
    (hcompact : IsCompact (f ⁻¹' Set.Icc (c - a) (c + a)))
    (hunique : ∀ x : M, f x ∈ Set.Icc (c - a) (c + a) →
      x = p ∨ ¬ IsCriticalPointAt I f x) :
    ∃ ε : ℝ, ∃ hε : 0 < ε, ε ≤ a ∧
    ∃ φ : C(CellBoundary k, SublevelSpace f (c - ε)),
      ∃ e : DifferentialGeometry.Topology.Homotopy.BaseCommutingHomotopyEquiv
        (B := SublevelSpace f (c - ε)) (X := SublevelSpace f (c + ε))
        (Y := CellAdjunctionSpace k φ),
        e.toBase = sublevelInclusion f (by linarith [hε]) ∧
        e.fromBase = ContinuousMap.mk
          (adjunctionLower (i := cellBoundaryInclusion k) φ)
          (continuous_adjunctionLower (i := cellBoundaryInclusion k) φ) := by
  rcases morse_lemma I f hf p k hk hnd hindex with
    ⟨R, hRpos, χ, hχ0src, hχ0tgt, hχ0val, hχsrc, hnorm0, hχmd, hχsmd,
      R', hR'pos, hχon, hχsymmOn⟩
  have hnorm : ∀ y : MorseModel n, morseNorm n y ≤ R → f (χ y) = morseNormalForm hk c y := by
    intro y hy
    rw [← hfp]
    exact hnorm0 y hy
  let ε₀ : ℝ := min a (min (R ^ 2) (R' ^ 2)) / 16
  let δ₀ : ℝ := Real.sqrt ε₀ / 4
  have hminpos : 0 < min a (min (R ^ 2) (R' ^ 2)) := by
    exact lt_min ha (lt_min (sq_pos_of_pos hRpos) (sq_pos_of_pos hR'pos))
  have hε₀ : 0 < ε₀ := by
    dsimp [ε₀]
    positivity
  have hδ₀ : 0 < δ₀ := by
    dsimp [δ₀]
    have hsqrt : 0 < Real.sqrt ε₀ := Real.sqrt_pos.2 hε₀
    nlinarith
  have hεa : ε₀ ≤ a := by
    dsimp [ε₀]
    have h1 : min a (min (R ^ 2) (R' ^ 2)) / 16 ≤ min a (min (R ^ 2) (R' ^ 2)) := by
      exact div_le_self (le_of_lt hminpos) (by norm_num : (1 : ℝ) ≤ 16)
    exact le_trans h1 (min_le_left a (min (R ^ 2) (R' ^ 2)))
  have hεmin : ε₀ ≤ min (R ^ 2) (R' ^ 2) / 16 := by
    dsimp [ε₀]
    have hle := min_le_right a (min (R ^ 2) (R' ^ 2))
    have hdiv : min a (min (R ^ 2) (R' ^ 2)) / 16 ≤ min (R ^ 2) (R' ^ 2) / 16 := by
      exact div_le_div_of_nonneg_right hle (by norm_num : (0 : ℝ) ≤ 16)
    exact hdiv
  have hsqδ : δ₀ ^ 2 = ε₀ / 16 := by
    dsimp [δ₀]
    rw [div_pow]
    rw [Real.sq_sqrt (le_of_lt hε₀)]
    ring
  have hR' : 4 * ε₀ + 9 * δ₀ ^ 2 / 4 < R ^ 2 := by
    rw [hsqδ]
    have hbound : 4 * ε₀ + 9 * (ε₀ / 16) / 4 ≤ 265 * (min (R ^ 2) (R' ^ 2) / 16) / 64 := by
      nlinarith [hεmin]
    have h265 : 265 * (min (R ^ 2) (R' ^ 2) / 16) / 64 < R ^ 2 := by
      have h1 : min (R ^ 2) (R' ^ 2) ≤ R ^ 2 := min_le_left (R ^ 2) (R' ^ 2)
      nlinarith [h1, sq_pos_of_pos hRpos]
    exact lt_of_le_of_lt hbound h265
  have hΦr : 4 * ε₀ + 9 * δ₀ ^ 2 / 4 < R' ^ 2 := by
    rw [hsqδ]
    have hbound : 4 * ε₀ + 9 * (ε₀ / 16) / 4 ≤ 265 * (min (R ^ 2) (R' ^ 2) / 16) / 64 := by
      nlinarith [hεmin]
    have h265 : 265 * (min (R ^ 2) (R' ^ 2) / 16) / 64 < R' ^ 2 := by
      have h1 : min (R ^ 2) (R' ^ 2) ≤ R' ^ 2 := min_le_right (R ^ 2) (R' ^ 2)
      nlinarith [h1, sq_pos_of_pos hR'pos]
    exact lt_of_le_of_lt hbound h265
  have hδε : 9 * δ₀ ^ 2 < 4 * ε₀ := by
    rw [hsqδ]
    nlinarith [hε₀]
  have hεR : Real.sqrt (2 * ε₀) ≤ R := by
    have hsq : (Real.sqrt (2 * ε₀)) ^ 2 ≤ R ^ 2 := by
      rw [Real.sq_sqrt (by positivity : 0 ≤ 2 * ε₀)]
      have hle : 2 * ε₀ ≤ R ^ 2 := by
        have h1 : ε₀ ≤ R ^ 2 / 16 := le_trans hεmin (by
          have hle' := min_le_left (R ^ 2) (R' ^ 2)
          nlinarith)
        nlinarith [h1]
      nlinarith [hle]
    have hnonneg : 0 ≤ Real.sqrt (2 * ε₀) := Real.sqrt_nonneg _
    have habs := sq_le_sq.mp hsq
    rwa [abs_of_nonneg hnonneg, abs_of_nonneg (le_of_lt hRpos)] at habs
  let data : MorseChart n k hk c I f :=
    { p := p, R := R, R' := R', ε := ε₀, χ := χ, hχ0 := hχ0val, hRpos := hRpos,
      hR'pos := hR'pos, hεpos := hε₀, hεR := hεR, hnorm := hnorm, hχsrc := hχsrc,
      hχon := hχon, hχsymmOn := hχsymmOn }
  let g : M → ℝ := morseModifiedFunction (H := H) (M := M) hk c ε₀ δ₀ R χ f
  have hgmd : ContMDiff I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) g := by
    dsimp [g]
    exact contMDiff_morseModifiedFunction (H := H) (M := M) hk c ε₀ δ₀ R R' hε₀ hδ₀
      hR' hΦr hRpos hR'pos I f hf χ hnorm hχsrc hχsymmOn
  have hg : Continuous g := hgmd.continuous
  have hg_le : ∀ x : M, g x ≤ f x := by
    intro x
    dsimp [g]
    exact morseModifiedFunction_le_f (H := H) (M := M) hk c ε₀ δ₀ R hε₀ χ f hnorm x
  let hlow0 : ContinuousMap.HomotopyEquiv (SublevelSpace (morseModifiedFunction (H := H) (M := M)
      hk c ε₀ δ₀ R χ f) (c - ε₀))
      {x : M // x ∈ sublevel f (c - ε₀) ∪ χ '' (Set.range (fun z : ClosedCell k =>
        cellMap (Real.sqrt (2 * ε₀)) (z : EuclideanSpace ℝ (Fin k))))} :=
    morseModifiedLowerSublevelHomotopyEquiv (H := H) (M := M) hk c ε₀ δ₀ R hε₀ hδ₀ hR' hRpos hεR
      χ f hg hnorm hχsrc
  have hcell : cellImage hk c data = χ '' (Set.range (fun z : ClosedCell k =>
      cellMap (Real.sqrt (2 * ε₀)) (z : EuclideanSpace ℝ (Fin k)))) := by
    change Set.range (fun z : ClosedCell k =>
        χ (cellMap (Real.sqrt (2 * ε₀)) (z : EuclideanSpace ℝ (Fin k)))) =
      χ '' (Set.range (fun z : ClosedCell k =>
        cellMap (Real.sqrt (2 * ε₀)) (z : EuclideanSpace ℝ (Fin k))))
    exact Set.range_comp (g := fun y : MorseModel n => χ y)
      (f := fun z : ClosedCell k => cellMap (Real.sqrt (2 * ε₀)) (z : EuclideanSpace ℝ (Fin k)))
  have hlow_lower : ∀ x : SublevelSpace f (c - ε₀),
      ((hlow0.toFun ⟨x.1, le_trans (hg_le x.1) (by change f x.1 ≤ c - ε₀; exact x.2)⟩).1 : M) =
        x.1 := by
    intro x
    have hfix := morseModifiedLowerSublevelHomotopyEquiv_lower (H := H) (M := M) hk c ε₀ δ₀ R
      hε₀ hδ₀ hR' hRpos hεR χ f hg hnorm hχsrc
    simpa [hlow0, g] using (hfix.1 x)
  have hlow_inv_lower : ∀ x : SublevelSpace f (c - ε₀),
      ((hlow0.invFun ⟨x.1, Or.inl x.2⟩).1 : M) = x.1 := by
    intro x
    have hfix := morseModifiedLowerSublevelHomotopyEquiv_lower (H := H) (M := M) hk c ε₀ δ₀ R
      hε₀ hδ₀ hR' hRpos hεR χ f hg hnorm hχsrc
    simpa [hlow0, g] using (hfix.2 x)
  have hgup : {x : M | g x ≤ c + ε₀} = sublevel f (c + ε₀) := by
    dsimp [g]
    exact sublevel_upper_identity_morseModifiedFunction (H := H) (M := M) hk c ε₀ δ₀ R hε₀ hδ₀
      hδε χ f hnorm
  have hcompactG : IsCompact (g ⁻¹' Set.Icc (c - ε₀) (c + ε₀)) := by
    dsimp [g]
    exact isCompact_strip_morseModifiedFunction (H := H) (M := M) hk c ε₀ δ₀ R a hε₀ hδ₀ hδε hεa
      χ f hf.continuous hnorm hg hcompact
  have hregularG : ∀ x : M, x ∈ g ⁻¹' Set.Icc (c - ε₀) (c + ε₀) →
      ¬ IsCriticalPointAt I g x := by
    intro x hx
    dsimp [g] at hx ⊢
    exact no_critical_point_morseModifiedFunction (H := H) (M := M) hk c ε₀ δ₀ R R' a hε₀ hδ₀ hδε
      hR' hΦr hRpos hR'pos hεa I f p χ hχ0val hnorm hχsrc hχsymmOn hχon hunique hx
  rcases no_critical_value_transport (f := g) hgmd (by linarith : c - ε₀ ≤ c + ε₀) hcompactG hregularG with
    ⟨v, Φ, hv, hsupp, hrate, hcomplete, hflow, htie⟩
  rcases sublevelCellAdjunctionBaseCommutingHomotopyEquivOfMorseChartAndDiffeomorph (I := I) (hf := hf)
      (f := f) (c := c) (k := k) (hk := hk) (data := data) (g := g) hgmd hg_le hlow0
      hcell hlow_lower hlow_inv_lower hgup v hv hsupp hcomplete hrate Φ hflow htie with
    ⟨hunder, hlaws⟩
  rcases hlaws with ⟨htoBase, hfromBase⟩
  refine ⟨ε₀, hε₀, hεa, cellAttachingMap hk c data, ?_⟩
  refine ⟨hunder, ?_, ?_⟩
  · exact htoBase
  · exact hfromBase

end ManifoldCellAttachment

end
end DifferentialGeometry.Topology.Morse
