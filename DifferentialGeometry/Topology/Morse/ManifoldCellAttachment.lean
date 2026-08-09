import DifferentialGeometry.Topology.Morse.CellAttachment
import DifferentialGeometry.Topology.Morse.HandleAttachment
import DifferentialGeometry.Topology.Handle.Attachment
import DifferentialGeometry.Topology.Handle.Manifold
import DifferentialGeometry.Topology.Handle.Retraction
import DifferentialGeometry.Topology.Homotopy.DeformationRetract
import DifferentialGeometry.Topology.Homotopy.EquivUnder
import DifferentialGeometry.Topology.Morse.Flow
import DifferentialGeometry.Topology.Morse.Manifold
import DifferentialGeometry.Topology.Morse.ModifiedFunction
import DifferentialGeometry.Topology.Morse.NoCriticalValues
import DifferentialGeometry.Topology.Morse.RegularSublevel
import Mathlib.Topology.MetricSpace.Bounded

namespace DifferentialGeometry.Topology.Morse

open Manifold
open DifferentialGeometry.Topology
open DifferentialGeometry.Topology.Handle
open DifferentialGeometry.Topology.Homotopy
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

def subtypeSetHomeomorph {X : Type} [TopologicalSpace X] {s t : Set X} (h : s = t) :
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

noncomputable def cocoreAttachingMap {n k : ℕ} (hk : k ≤ n) (c ε r δ : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ (MorseModel n) H} [I.Boundaryless]
    [IsManifold I (⊤ : WithTop ℕ∞) M] [T2Space M] {f : M → ℝ}
    (data : MorseChart n k hk c I f)
    (hε : 0 ≤ ε) (hδ : r ^ 2 / 2 < δ) (hεr : Real.sqrt (2 * ε + r ^ 2) ≤ data.R)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) f)
    (v : (x : M) → TangentSpace I x)
    (hdfOn : ∀ x ∈ f ⁻¹' Set.Icc (c - ε) (c + δ),
      (NormedSpace.fromTangentSpace (f x)) ((mfderiv I 𝓘(ℝ, ℝ) f x) (v x)) = -1)
    (hrate : ∀ x, -1 ≤ (NormedSpace.fromTangentSpace (f x)) ((mfderiv I 𝓘(ℝ, ℝ) f x) (v x)) ∧
      (NormedSpace.fromTangentSpace (f x)) ((mfderiv I 𝓘(ℝ, ℝ) f x) (v x)) ≤ 0)
    (hcomplete : ∀ x : M, ∃ γ : ℝ → M, γ 0 = x ∧ IsMIntegralCurve γ v) :
    CellBoundary k × ClosedCell (n - k) → LevelSetSpace f (c - ε) :=
  fun p =>
    let u : EuclideanSpace ℝ (Fin k) := p.1
    let w : EuclideanSpace ℝ (Fin (n - k)) := p.2
    let y : MorseModel n := recombine hk (negPart hk (cellMap (Real.sqrt (2 * ε)) u)) (r • w)
    let x : M := data.χ y
    let T : ℝ := r ^ 2 * ‖w‖ ^ 2 / 2
    ⟨curveAt v hcomplete x T, by
      have hnormb : morseNorm n y ≤ data.R := by
        exact le_trans (morseNorm_recombine_cellMap_bound hk ε r hε u p.1.2 w p.2.2) hεr
      have hy : y ∈ data.χ.source := data.hχsrc y hnormb
      have hTge : 0 ≤ T := by
        dsimp [T]
        positivity
      have hval : f x = c - ε + T := by
        have hnorm := data.hnorm y hnormb
        have hrecomb := morseNormalForm_recombine_cellMap hk c ε hε u (r • w)
        rw [hnorm]
        rw [hrecomb]
        have hnorm2 : ‖(r • w : EuclideanSpace ℝ (Fin (n - k)))‖ ^ 2 = r ^ 2 * ‖w‖ ^ 2 := by
          rw [norm_smul]
          rw [Real.norm_eq_abs]
          rw [mul_pow]
          rw [sq_abs]
        rw [hnorm2, p.1.2]
        dsimp [T]
        ring_nf
      have hw : ‖w‖ ^ 2 ≤ 1 := by
        have hneg : -1 ≤ ‖w‖ := by linarith [norm_nonneg w]
        exact (sq_le_sq' hneg p.2.2).trans_eq (by norm_num : (1 : ℝ) ^ 2 = 1)
      have hTle : T < δ := by
        dsimp [T]
        nlinarith [hδ, hw, sq_nonneg r]
      have hstart : x ∈ f ⁻¹' Set.Icc (c - ε) (c + δ) := by
        change c - ε ≤ f x ∧ f x ≤ c + δ
        rw [hval]
        constructor
        · linarith [hTge]
        · linarith
      have hstayFwd : ∀ s ∈ Set.Icc (0 : ℝ) T, curveAt v hcomplete x s ∈ f ⁻¹' Set.Icc (c - ε) (c + δ) := by
        intro s hs
        have hrb := f_rate_bounds_of_integralCurve f hf v hrate
          (hγ := curveAt_integralCurve v hcomplete x) (t := s) hs.1
        have hrb' : c - ε + T - s ≤ f (curveAt v hcomplete x s) ∧
            f (curveAt v hcomplete x s) ≤ c - ε + T := by
          simpa [curveAt_zero v hcomplete x, hval] using hrb
        change c - ε ≤ f (curveAt v hcomplete x s) ∧ f (curveAt v hcomplete x s) ≤ c + δ
        constructor
        · linarith [hs.2]
        · linarith [hTle]
      have hEq := f_eq_sub_of_integralCurve_on_strip f hf v hdfOn
        (hγ := curveAt_integralCurve v hcomplete x) (t := T) hTge hstayFwd
      change f (curveAt v hcomplete x T) = c - ε
      rw [hEq, curveAt_zero v hcomplete x, hval]
      ring_nf⟩

theorem cocoreAttachingMap_value {n k : ℕ} (hk : k ≤ n) (c ε r δ : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ (MorseModel n) H} [I.Boundaryless]
    [IsManifold I (⊤ : WithTop ℕ∞) M] [T2Space M] {f : M → ℝ}
    (data : MorseChart n k hk c I f)
    (hε : 0 ≤ ε) (hδ : r ^ 2 / 2 < δ) (hεr : Real.sqrt (2 * ε + r ^ 2) ≤ data.R)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) f)
    (v : (x : M) → TangentSpace I x)
    (hdfOn : ∀ x ∈ f ⁻¹' Set.Icc (c - ε) (c + δ),
      (NormedSpace.fromTangentSpace (f x)) ((mfderiv I 𝓘(ℝ, ℝ) f x) (v x)) = -1)
    (hrate : ∀ x, -1 ≤ (NormedSpace.fromTangentSpace (f x)) ((mfderiv I 𝓘(ℝ, ℝ) f x) (v x)) ∧
      (NormedSpace.fromTangentSpace (f x)) ((mfderiv I 𝓘(ℝ, ℝ) f x) (v x)) ≤ 0)
    (hcomplete : ∀ x : M, ∃ γ : ℝ → M, γ 0 = x ∧ IsMIntegralCurve γ v)
    (p : CellBoundary k × ClosedCell (n - k)) :
    f ((cocoreAttachingMap hk c ε r δ data hε hδ hεr hf v hdfOn hrate hcomplete p).1) = c - ε := by
  change f (curveAt v hcomplete (data.χ
    (recombine hk (negPart hk (cellMap (Real.sqrt (2 * ε)) (p.1 : EuclideanSpace ℝ (Fin k))))
      (r • (p.2 : EuclideanSpace ℝ (Fin (n - k))))))
    (r ^ 2 * ‖(p.2 : EuclideanSpace ℝ (Fin (n - k)))‖ ^ 2 / 2)) = c - ε
  let u : EuclideanSpace ℝ (Fin k) := p.1
  let w : EuclideanSpace ℝ (Fin (n - k)) := p.2
  let y : MorseModel n := recombine hk (negPart hk (cellMap (Real.sqrt (2 * ε)) u)) (r • w)
  let x : M := data.χ y
  let T : ℝ := r ^ 2 * ‖w‖ ^ 2 / 2
  have hnormb : morseNorm n y ≤ data.R := by
    exact le_trans (morseNorm_recombine_cellMap_bound hk ε r hε u p.1.2 w p.2.2) hεr
  have hTge : 0 ≤ T := by
    dsimp [T]
    positivity
  have hval : f x = c - ε + T := by
    have hnorm := data.hnorm y hnormb
    have hrecomb := morseNormalForm_recombine_cellMap hk c ε hε u (r • w)
    rw [hnorm]
    rw [hrecomb]
    have hnorm2 : ‖(r • w : EuclideanSpace ℝ (Fin (n - k)))‖ ^ 2 = r ^ 2 * ‖w‖ ^ 2 := by
      rw [norm_smul]
      rw [Real.norm_eq_abs]
      rw [mul_pow]
      rw [sq_abs]
    rw [hnorm2, p.1.2]
    dsimp [T]
    ring_nf
  have hw : ‖w‖ ^ 2 ≤ 1 := by
    have hneg : -1 ≤ ‖w‖ := by linarith [norm_nonneg w]
    exact (sq_le_sq' hneg p.2.2).trans_eq (by norm_num : (1 : ℝ) ^ 2 = 1)
  have hTle : T < δ := by
    dsimp [T]
    nlinarith [hδ, hw, sq_nonneg r]
  have hstayFwd : ∀ s ∈ Set.Icc (0 : ℝ) T, curveAt v hcomplete x s ∈ f ⁻¹' Set.Icc (c - ε) (c + δ) := by
    intro s hs
    have hrb := f_rate_bounds_of_integralCurve f hf v hrate
      (hγ := curveAt_integralCurve v hcomplete x) (t := s) hs.1
    have hrb' : c - ε + T - s ≤ f (curveAt v hcomplete x s) ∧
        f (curveAt v hcomplete x s) ≤ c - ε + T := by
      simpa [curveAt_zero v hcomplete x, hval] using hrb
    change c - ε ≤ f (curveAt v hcomplete x s) ∧ f (curveAt v hcomplete x s) ≤ c + δ
    constructor
    · linarith [hs.2]
    · linarith [hTle]
  have hEq := f_eq_sub_of_integralCurve_on_strip f hf v hdfOn
    (hγ := curveAt_integralCurve v hcomplete x) (t := T) hTge hstayFwd
  change f (curveAt v hcomplete x T) = c - ε
  rw [hEq, curveAt_zero v hcomplete x, hval]
  ring_nf

theorem attachingRegionContMDiff_of {n k : ℕ}
    (F : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin (n - k)) → MorseModel n)
    (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    [NeZero k] [NeZero (n - k)] :
    @ContMDiff ℝ _
      (EuclideanSpace ℝ (Fin (k - 1)) × EuclideanSpace ℝ (Fin ((n - k - 1) + 1))) _ _
      (ModelProd (EuclideanSpace ℝ (Fin (k - 1))) (EuclideanHalfSpace ((n - k - 1) + 1))) _
      ((𝓡 (k - 1)).prod (modelWithCornersEuclideanHalfSpace ((n - k - 1) + 1)))
      (AttachingRegion k (n - k)) _ (attachingRegionChartedSpace k (n - k))
      (MorseModel n) _ _ (MorseModel n) _
      (𝓘(ℝ, MorseModel n)) (MorseModel n) _ _
      (⊤ : ℕ∞)
      (fun p : AttachingRegion k (n - k) =>
        F ((p.1 : EuclideanSpace ℝ (Fin k)), (p.2 : EuclideanSpace ℝ (Fin (n - k))))) := by
  classical
  letI : ChartedSpace (EuclideanSpace ℝ (Fin (k - 1))) (CellBoundary k) :=
    cellBoundaryChartedSpace k
  letI : ChartedSpace (EuclideanHalfSpace ((n - k - 1) + 1)) (ClosedCell (n - k)) :=
    closedCellChartedSpace (n - k)
  letI : ChartedSpace (EuclideanHalfSpace ((n - k - 1) + 1)) (ClosedCell ((n - k - 1) + 1)) :=
    closedCellChartedSpaceSucc (n - k - 1)
  letI : IsManifold (𝓡 (k - 1)) (⊤ : ℕ∞) (CellBoundary k) := cellBoundaryIsManifold k
  letI : IsManifold (modelWithCornersEuclideanHalfSpace ((n - k - 1) + 1)) (⊤ : ℕ∞)
      (ClosedCell ((n - k - 1) + 1)) := closedCellIsManifold (n - k - 1)
  letI : IsManifold (modelWithCornersEuclideanHalfSpace ((n - k - 1) + 1)) (⊤ : ℕ∞)
      (ClosedCell (n - k)) :=
    isManifoldOfHomeomorph (modelWithCornersEuclideanHalfSpace ((n - k - 1) + 1))
      (closedCellReindexHomeo (n - k))
  have h1 : ContMDiff (𝓡 (k - 1)) (𝓘(ℝ, EuclideanSpace ℝ (Fin k))) (⊤ : ℕ∞)
      (fun u : CellBoundary k => (u : EuclideanSpace ℝ (Fin k))) :=
    cellBoundaryInclusion_contMDiff k
  have h2 : ContMDiff (modelWithCornersEuclideanHalfSpace ((n - k - 1) + 1))
      (𝓘(ℝ, EuclideanSpace ℝ (Fin (n - k)))) (⊤ : ℕ∞)
      (fun v : ClosedCell (n - k) => (v : EuclideanSpace ℝ (Fin (n - k)))) :=
    closedCellInclusion_contMDiff_of (n - k)
  have hprod : ContMDiff ((𝓡 (k - 1)).prod (modelWithCornersEuclideanHalfSpace ((n - k - 1) + 1)))
      ((𝓘(ℝ, EuclideanSpace ℝ (Fin k))).prod (𝓘(ℝ, EuclideanSpace ℝ (Fin (n - k))))) (⊤ : ℕ∞)
      (fun p : AttachingRegion k (n - k) =>
        ((p.1 : EuclideanSpace ℝ (Fin k)), (p.2 : EuclideanSpace ℝ (Fin (n - k))))) := by
    exact ContMDiff.prodMap h1 h2
  have hF' : ContMDiff ((𝓘(ℝ, EuclideanSpace ℝ (Fin k))).prod
        (𝓘(ℝ, EuclideanSpace ℝ (Fin (n - k)))))
      (𝓘(ℝ, MorseModel n)) (⊤ : ℕ∞)
      (fun q : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin (n - k)) => F q) := by
    rw [contMDiff_iff]
    constructor
    · exact hF.continuous
    · intro x y
      apply hF.contDiffOn.congr
      intro q hq
      simp [extChartAt, Function.comp_def, OpenPartialHomeomorph.refl_prod_refl]
      rfl
  have hfun : (fun p : AttachingRegion k (n - k) =>
        F ((p.1 : EuclideanSpace ℝ (Fin k)), (p.2 : EuclideanSpace ℝ (Fin (n - k))))) =
      (fun q : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin (n - k)) => F q) ∘
        (fun p : AttachingRegion k (n - k) =>
          ((p.1 : EuclideanSpace ℝ (Fin k)), (p.2 : EuclideanSpace ℝ (Fin (n - k))))) := by
    funext p
    rfl
  rw [hfun]
  exact hF'.comp hprod

theorem attachingRegionRecombine_contMDiff {n k : ℕ} (hk : k ≤ n) (r ε : ℝ)
    [NeZero k] [NeZero (n - k)] :
    @ContMDiff ℝ _
      (EuclideanSpace ℝ (Fin (k - 1)) × EuclideanSpace ℝ (Fin ((n - k - 1) + 1))) _ _
      (ModelProd (EuclideanSpace ℝ (Fin (k - 1))) (EuclideanHalfSpace ((n - k - 1) + 1))) _
      ((𝓡 (k - 1)).prod (modelWithCornersEuclideanHalfSpace ((n - k - 1) + 1)))
      (AttachingRegion k (n - k)) _ (attachingRegionChartedSpace k (n - k))
      (MorseModel n) _ _ (MorseModel n) _
      (𝓘(ℝ, MorseModel n)) (MorseModel n) _ _
      (⊤ : ℕ∞)
      (fun p : AttachingRegion k (n - k) =>
        recombine hk (negPart hk (cellMap (Real.sqrt (2 * ε)) (p.1 : EuclideanSpace ℝ (Fin k))))
          (r • (p.2 : EuclideanSpace ℝ (Fin (n - k))))) := by
  classical
  letI : ChartedSpace (EuclideanSpace ℝ (Fin (k - 1))) (CellBoundary k) :=
    cellBoundaryChartedSpace k
  letI : ChartedSpace (EuclideanHalfSpace ((n - k - 1) + 1)) (ClosedCell (n - k)) :=
    closedCellChartedSpace (n - k)
  letI : ChartedSpace (EuclideanHalfSpace ((n - k - 1) + 1)) (ClosedCell ((n - k - 1) + 1)) :=
    closedCellChartedSpaceSucc (n - k - 1)
  letI : IsManifold (𝓡 (k - 1)) (⊤ : ℕ∞) (CellBoundary k) := cellBoundaryIsManifold k
  letI : IsManifold (modelWithCornersEuclideanHalfSpace ((n - k - 1) + 1)) (⊤ : ℕ∞)
      (ClosedCell ((n - k - 1) + 1)) := closedCellIsManifold (n - k - 1)
  letI : IsManifold (modelWithCornersEuclideanHalfSpace ((n - k - 1) + 1)) (⊤ : ℕ∞)
      (ClosedCell (n - k)) :=
    isManifoldOfHomeomorph (modelWithCornersEuclideanHalfSpace ((n - k - 1) + 1))
      (closedCellReindexHomeo (n - k))
  have h1 : ContMDiff (𝓡 (k - 1)) (𝓘(ℝ, EuclideanSpace ℝ (Fin k))) (⊤ : ℕ∞)
      (fun u : CellBoundary k => (u : EuclideanSpace ℝ (Fin k))) :=
    cellBoundaryInclusion_contMDiff k
  have h2 : ContMDiff (modelWithCornersEuclideanHalfSpace ((n - k - 1) + 1))
      (𝓘(ℝ, EuclideanSpace ℝ (Fin (n - k)))) (⊤ : ℕ∞)
      (fun v : ClosedCell (n - k) => (v : EuclideanSpace ℝ (Fin (n - k)))) :=
    closedCellInclusion_contMDiff_of (n - k)
  have hprod : ContMDiff ((𝓡 (k - 1)).prod (modelWithCornersEuclideanHalfSpace ((n - k - 1) + 1)))
      ((𝓘(ℝ, EuclideanSpace ℝ (Fin k))).prod (𝓘(ℝ, EuclideanSpace ℝ (Fin (n - k))))) (⊤ : ℕ∞)
      (fun p : AttachingRegion k (n - k) =>
        ((p.1 : EuclideanSpace ℝ (Fin k)), (p.2 : EuclideanSpace ℝ (Fin (n - k))))) := by
    exact ContMDiff.prodMap h1 h2
  have hF : ContMDiff ((𝓘(ℝ, EuclideanSpace ℝ (Fin k))).prod
        (𝓘(ℝ, EuclideanSpace ℝ (Fin (n - k)))))
      (𝓘(ℝ, MorseModel n)) (⊤ : ℕ∞)
      (fun q : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin (n - k)) =>
        recombine hk (negPart hk (cellMap (Real.sqrt (2 * ε)) q.1)) (r • q.2)) := by
    rw [contMDiff_iff]
    constructor
    · exact (recombine_contDiff hk r ε).continuous
    · intro x y
      apply (recombine_contDiff hk r ε).contDiffOn.congr
      intro q hq
      simp [extChartAt, Function.comp_def, OpenPartialHomeomorph.refl_prod_refl]
      rfl
  have hfun : (fun p : AttachingRegion k (n - k) =>
        recombine hk (negPart hk (cellMap (Real.sqrt (2 * ε)) (p.1 : EuclideanSpace ℝ (Fin k))))
          (r • (p.2 : EuclideanSpace ℝ (Fin (n - k))))) =
      (fun q : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin (n - k)) =>
        recombine hk (negPart hk (cellMap (Real.sqrt (2 * ε)) q.1)) (r • q.2)) ∘
        (fun p : AttachingRegion k (n - k) =>
          ((p.1 : EuclideanSpace ℝ (Fin k)), (p.2 : EuclideanSpace ℝ (Fin (n - k))))) := by
    funext p
    rfl
  rw [hfun]
  exact hF.comp hprod

theorem contMDiff_cocoreAttachingMap {m k : ℕ} (hk : k ≤ m + 1) (c ε r δ : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} [I.Boundaryless]
    [IsManifold I (⊤ : WithTop ℕ∞) M] [T2Space M] {f : M → ℝ}
    (data : MorseChart (m + 1) k hk c I f)
    (hε : 0 ≤ ε) (hδ : r ^ 2 / 2 < δ) (hεr : Real.sqrt (2 * ε + r ^ 2) ≤ data.R)
    (hRltR' : data.R < data.R')
    (hf : ContMDiff I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) f)
    (hreg : ∀ x : M, f x = c - ε → ¬ IsCriticalPointAt I f x)
    (v : (x : M) → TangentSpace I x)
    (hv : ContMDiff I (I.prod 𝓘(ℝ, MorseModel (m + 1))) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : M => (⟨x, v x⟩ : TangentBundle I M)))
    (hsupp : IsCompact (tsupport v))
    (hdfOn : ∀ x ∈ f ⁻¹' Set.Icc (c - ε) (c + δ),
      (NormedSpace.fromTangentSpace (f x)) ((mfderiv I 𝓘(ℝ, ℝ) f x) (v x)) = -1)
    (hrate : ∀ x, -1 ≤ (NormedSpace.fromTangentSpace (f x)) ((mfderiv I 𝓘(ℝ, ℝ) f x) (v x)) ∧
      (NormedSpace.fromTangentSpace (f x)) ((mfderiv I 𝓘(ℝ, ℝ) f x) (v x)) ≤ 0)
    (hcomplete : ∀ x : M, ∃ γ : ℝ → M, γ 0 = x ∧ IsMIntegralCurve γ v)
    [NeZero k] [NeZero (m + 1 - k)] :
    @ContMDiff ℝ _
      (EuclideanSpace ℝ (Fin (k - 1)) × EuclideanSpace ℝ (Fin ((m + 1 - k - 1) + 1))) _ _
      (ModelProd (EuclideanSpace ℝ (Fin (k - 1))) (EuclideanHalfSpace ((m + 1 - k - 1) + 1))) _
      ((𝓡 (k - 1)).prod (modelWithCornersEuclideanHalfSpace ((m + 1 - k - 1) + 1)))
      (AttachingRegion k (m + 1 - k)) _ (attachingRegionChartedSpace k (m + 1 - k))
      (MorseModel m) _ _ (MorseModel m) _
      (𝓘(ℝ, MorseModel m)) (LevelSetSpace f (c - ε)) _
      (manifoldLevelSetChartedSpace I f (c - ε) hf hreg)
      (⊤ : ℕ∞)
      (cocoreAttachingMap hk c ε r δ data hε hδ hεr hf v hdfOn hrate hcomplete) := by
  classical
  letI : ChartedSpace (EuclideanSpace ℝ (Fin (k - 1))) (CellBoundary k) :=
    cellBoundaryChartedSpace k
  letI : ChartedSpace (EuclideanHalfSpace ((m + 1 - k - 1) + 1)) (ClosedCell (m + 1 - k)) :=
    closedCellChartedSpace (m + 1 - k)
  letI : ChartedSpace (EuclideanHalfSpace ((m + 1 - k - 1) + 1)) (ClosedCell ((m + 1 - k - 1) + 1)) :=
    closedCellChartedSpaceSucc (m + 1 - k - 1)
  letI : IsManifold (𝓡 (k - 1)) (⊤ : ℕ∞) (CellBoundary k) := cellBoundaryIsManifold k
  letI : IsManifold (modelWithCornersEuclideanHalfSpace ((m + 1 - k - 1) + 1)) (⊤ : ℕ∞)
      (ClosedCell ((m + 1 - k - 1) + 1)) := closedCellIsManifold (m + 1 - k - 1)
  letI : IsManifold (modelWithCornersEuclideanHalfSpace ((m + 1 - k - 1) + 1)) (⊤ : ℕ∞)
      (ClosedCell (m + 1 - k)) :=
    isManifoldOfHomeomorph (modelWithCornersEuclideanHalfSpace ((m + 1 - k - 1) + 1))
      (closedCellReindexHomeo (m + 1 - k))
  letI : ChartedSpace (ModelProd (EuclideanSpace ℝ (Fin (k - 1)))
      (EuclideanHalfSpace ((m + 1 - k - 1) + 1))) (AttachingRegion k (m + 1 - k)) :=
    attachingRegionChartedSpace k (m + 1 - k)
  letI : ChartedSpace (MorseModel m) (LevelSetSpace f (c - ε)) :=
    manifoldLevelSetChartedSpace I f (c - ε) hf hreg
  let Iatt : ModelWithCorners ℝ
      (EuclideanSpace ℝ (Fin (k - 1)) × EuclideanSpace ℝ (Fin ((m + 1 - k - 1) + 1)))
      (ModelProd (EuclideanSpace ℝ (Fin (k - 1))) (EuclideanHalfSpace ((m + 1 - k - 1) + 1))) :=
    (𝓡 (k - 1)).prod (modelWithCornersEuclideanHalfSpace ((m + 1 - k - 1) + 1))
  letI : IsManifold Iatt (⊤ : ℕ∞) (AttachingRegion k (m + 1 - k)) :=
    attachingRegionIsManifold k (m + 1 - k)
  have hrecomb : ContMDiff Iatt (𝓘(ℝ, MorseModel (m + 1))) (⊤ : ℕ∞)
      (fun p : AttachingRegion k (m + 1 - k) =>
        recombine hk (negPart hk (cellMap (Real.sqrt (2 * ε)) (p.1 : EuclideanSpace ℝ (Fin k))))
          (r • (p.2 : EuclideanSpace ℝ (Fin (m + 1 - k))))) := by
    simpa [Iatt] using (attachingRegionRecombine_contMDiff hk r ε)
  have hrecombOn : ContMDiffOn Iatt (𝓘(ℝ, MorseModel (m + 1))) (⊤ : ℕ∞)
      (fun p : AttachingRegion k (m + 1 - k) =>
        recombine hk (negPart hk (cellMap (Real.sqrt (2 * ε)) (p.1 : EuclideanSpace ℝ (Fin k))))
          (r • (p.2 : EuclideanSpace ℝ (Fin (m + 1 - k))))) Set.univ := by
    rw [contMDiffOn_univ]
    exact hrecomb
  have hball : ∀ p : AttachingRegion k (m + 1 - k),
      recombine hk (negPart hk (cellMap (Real.sqrt (2 * ε)) (p.1 : EuclideanSpace ℝ (Fin k))))
          (r • (p.2 : EuclideanSpace ℝ (Fin (m + 1 - k)))) ∈
        Metric.ball (0 : MorseModel (m + 1)) data.R' := by
    intro p
    have hnormb : morseNorm (m + 1)
        (recombine hk (negPart hk (cellMap (Real.sqrt (2 * ε)) (p.1 : EuclideanSpace ℝ (Fin k))))
          (r • (p.2 : EuclideanSpace ℝ (Fin (m + 1 - k))))) ≤ data.R := by
      exact le_trans (morseNorm_recombine_cellMap_bound hk ε r hε (p.1 : EuclideanSpace ℝ (Fin k))
        p.1.2 (p.2 : EuclideanSpace ℝ (Fin (m + 1 - k))) p.2.2) hεr
    have hlt : ‖(recombine hk (negPart hk (cellMap (Real.sqrt (2 * ε)) (p.1 : EuclideanSpace ℝ (Fin k))))
          (r • (p.2 : EuclideanSpace ℝ (Fin (m + 1 - k)))))‖ < data.R' :=
      lt_of_le_of_lt (morseNorm_piNorm_le (recombine hk (negPart hk (cellMap (Real.sqrt (2 * ε))
        (p.1 : EuclideanSpace ℝ (Fin k)))) (r • (p.2 : EuclideanSpace ℝ (Fin (m + 1 - k))))))
        (lt_of_le_of_lt hnormb hRltR')
    simpa [Metric.mem_ball, dist_eq_norm] using hlt
  have hχ : ContMDiffOn Iatt I (⊤ : ℕ∞)
      (fun p : AttachingRegion k (m + 1 - k) =>
        data.χ (recombine hk (negPart hk (cellMap (Real.sqrt (2 * ε)) (p.1 : EuclideanSpace ℝ (Fin k))))
          (r • (p.2 : EuclideanSpace ℝ (Fin (m + 1 - k)))))) Set.univ := by
    refine data.hχon.comp hrecombOn ?_
    intro p hp
    exact hball p
  have hT : ContMDiff Iatt (𝓘(ℝ, ℝ)) (⊤ : ℕ∞)
      (fun p : AttachingRegion k (m + 1 - k) =>
        r ^ 2 * ‖(p.2 : EuclideanSpace ℝ (Fin (m + 1 - k)))‖ ^ 2 / 2) := by
    have hT' : ContMDiff (modelWithCornersEuclideanHalfSpace ((m + 1 - k - 1) + 1))
        (𝓘(ℝ, ℝ)) (⊤ : ℕ∞)
        (fun v : ClosedCell (m + 1 - k) =>
          r ^ 2 * ‖(v : EuclideanSpace ℝ (Fin (m + 1 - k)))‖ ^ 2 / 2) := by
      have hinc : ContMDiff (modelWithCornersEuclideanHalfSpace ((m + 1 - k - 1) + 1))
          (𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1 - k)))) (⊤ : ℕ∞)
          (fun v : ClosedCell (m + 1 - k) => (v : EuclideanSpace ℝ (Fin (m + 1 - k)))) :=
        closedCellInclusion_contMDiff_of (m + 1 - k)
      have hnorm : ContDiff ℝ (⊤ : ℕ∞) (fun w : EuclideanSpace ℝ (Fin (m + 1 - k)) =>
          r ^ 2 * ‖w‖ ^ 2 / 2) := by
        have hnorm2 : ContDiff ℝ (⊤ : ℕ∞) (fun w : EuclideanSpace ℝ (Fin (m + 1 - k)) =>
            ‖w‖ ^ 2) := contDiff_norm_sq ℝ
        simpa [div_eq_mul_inv] using (contDiff_const.mul hnorm2).mul contDiff_const
      exact (contMDiff_iff_contDiff.mpr hnorm).comp hinc
    have hsnd : ContMDiff Iatt (modelWithCornersEuclideanHalfSpace ((m + 1 - k - 1) + 1))
        (⊤ : ℕ∞)
        (fun p : AttachingRegion k (m + 1 - k) => p.2) := by
      simpa [Iatt] using (contMDiff_snd (I := 𝓡 (k - 1))
        (J := modelWithCornersEuclideanHalfSpace ((m + 1 - k - 1) + 1))
        (n := (⊤ : ℕ∞)))
    exact hT'.comp hsnd
  have hpair : ContMDiff Iatt ((𝓘(ℝ, ℝ)).prod I) (⊤ : ℕ∞)
      (fun p : AttachingRegion k (m + 1 - k) =>
        (r ^ 2 * ‖(p.2 : EuclideanSpace ℝ (Fin (m + 1 - k)))‖ ^ 2 / 2,
          data.χ (recombine hk (negPart hk (cellMap (Real.sqrt (2 * ε)) (p.1 : EuclideanSpace ℝ (Fin k))))
            (r • (p.2 : EuclideanSpace ℝ (Fin (m + 1 - k))))))) := by
    have hχ' : ContMDiff Iatt I (⊤ : ℕ∞)
        (fun p : AttachingRegion k (m + 1 - k) =>
          data.χ (recombine hk (negPart hk (cellMap (Real.sqrt (2 * ε)) (p.1 : EuclideanSpace ℝ (Fin k))))
            (r • (p.2 : EuclideanSpace ℝ (Fin (m + 1 - k)))))) := by
      rw [← contMDiffOn_univ]
      exact hχ
    exact ContMDiff.prodMk hT hχ'
  have hflow : ContMDiff ((𝓘(ℝ, ℝ)).prod I) I (⊤ : ℕ∞)
      (fun q : ℝ × M =>
        curveAt v (exists_globalIntegralCurve_of_compactSupport v hv hsupp) q.2 q.1) :=
    contMDiff_globalFlow_joint_of_compactSupport (E := MorseModel (m + 1)) (I := I)
      (v := v) (hv := hv) (hsupp := hsupp)
  have hflowComp : ContMDiff Iatt I (⊤ : ℕ∞)
      (fun p : AttachingRegion k (m + 1 - k) =>
        curveAt v (exists_globalIntegralCurve_of_compactSupport v hv hsupp)
          (data.χ (recombine hk (negPart hk (cellMap (Real.sqrt (2 * ε)) (p.1 : EuclideanSpace ℝ (Fin k))))
            (r • (p.2 : EuclideanSpace ℝ (Fin (m + 1 - k))))))
          (r ^ 2 * ‖(p.2 : EuclideanSpace ℝ (Fin (m + 1 - k)))‖ ^ 2 / 2)) :=
    hflow.comp hpair
  have hwitness : ∀ p : AttachingRegion k (m + 1 - k),
      curveAt v hcomplete (data.χ (recombine hk (negPart hk (cellMap (Real.sqrt (2 * ε))
            (p.1 : EuclideanSpace ℝ (Fin k)))) (r • (p.2 : EuclideanSpace ℝ (Fin (m + 1 - k))))))
          (r ^ 2 * ‖(p.2 : EuclideanSpace ℝ (Fin (m + 1 - k)))‖ ^ 2 / 2) =
      curveAt v (exists_globalIntegralCurve_of_compactSupport v hv hsupp)
          (data.χ (recombine hk (negPart hk (cellMap (Real.sqrt (2 * ε))
            (p.1 : EuclideanSpace ℝ (Fin k)))) (r • (p.2 : EuclideanSpace ℝ (Fin (m + 1 - k))))))
          (r ^ 2 * ‖(p.2 : EuclideanSpace ℝ (Fin (m + 1 - k)))‖ ^ 2 / 2) := by
    intro p
    exact curveAt_hcomplete_irrel (E := MorseModel (m + 1)) (I := I) v
      (hv := (hv.of_le (show (1 : WithTop ℕ∞) ≤ (⊤ : ℕ∞) by
        exact_mod_cast (le_top : (1 : ℕ∞) ≤ (⊤ : ℕ∞))))) hcomplete
      (exists_globalIntegralCurve_of_compactSupport v hv hsupp)
      (data.χ (recombine hk (negPart hk (cellMap (Real.sqrt (2 * ε))
        (p.1 : EuclideanSpace ℝ (Fin k)))) (r • (p.2 : EuclideanSpace ℝ (Fin (m + 1 - k))))))
      (r ^ 2 * ‖(p.2 : EuclideanSpace ℝ (Fin (m + 1 - k)))‖ ^ 2 / 2)
  have hflowComp' : ContMDiff Iatt I (⊤ : ℕ∞)
      (fun p : AttachingRegion k (m + 1 - k) =>
        curveAt v hcomplete (data.χ (recombine hk (negPart hk (cellMap (Real.sqrt (2 * ε))
              (p.1 : EuclideanSpace ℝ (Fin k)))) (r • (p.2 : EuclideanSpace ℝ (Fin (m + 1 - k))))))
          (r ^ 2 * ‖(p.2 : EuclideanSpace ℝ (Fin (m + 1 - k)))‖ ^ 2 / 2)) := by
    refine hflowComp.congr ?_
    intro p
    exact (hwitness p).symm
  have hFa : ∀ p : AttachingRegion k (m + 1 - k),
      f (curveAt v hcomplete (data.χ (recombine hk (negPart hk (cellMap (Real.sqrt (2 * ε))
              (p.1 : EuclideanSpace ℝ (Fin k)))) (r • (p.2 : EuclideanSpace ℝ (Fin (m + 1 - k))))))
          (r ^ 2 * ‖(p.2 : EuclideanSpace ℝ (Fin (m + 1 - k)))‖ ^ 2 / 2)) = c - ε := by
    intro p
    simpa [cocoreAttachingMap] using (cocoreAttachingMap_value hk c ε r δ data hε hδ hεr hf v
      hdfOn hrate hcomplete p)
  have hfac : ContMDiff Iatt (𝓘(ℝ, MorseModel m)) (⊤ : ℕ∞)
      (fun p : AttachingRegion k (m + 1 - k) =>
        (⟨curveAt v hcomplete (data.χ (recombine hk (negPart hk (cellMap (Real.sqrt (2 * ε))
                (p.1 : EuclideanSpace ℝ (Fin k)))) (r • (p.2 : EuclideanSpace ℝ (Fin (m + 1 - k))))))
            (r ^ 2 * ‖(p.2 : EuclideanSpace ℝ (Fin (m + 1 - k)))‖ ^ 2 / 2), hFa p⟩ :
          LevelSetSpace f (c - ε))) :=
    contMDiff_levelSet_factor I f (c - ε) hf hreg
      (IX := Iatt) (F := fun p : AttachingRegion k (m + 1 - k) =>
        curveAt v hcomplete (data.χ (recombine hk (negPart hk (cellMap (Real.sqrt (2 * ε))
            (p.1 : EuclideanSpace ℝ (Fin k)))) (r • (p.2 : EuclideanSpace ℝ (Fin (m + 1 - k))))))
          (r ^ 2 * ‖(p.2 : EuclideanSpace ℝ (Fin (m + 1 - k)))‖ ^ 2 / 2))
      (hF := hflowComp') (hFa := hFa)
  refine hfac.congr ?_
  intro p
  apply Subtype.ext
  rfl

noncomputable def cocoreModelPoint {n k : ℕ} (hk : k ≤ n) (ε r : ℝ)
    (p : CellBoundary k × ClosedCell (n - k)) : MorseModel n :=
  recombine hk (negPart hk (cellMap (Real.sqrt (2 * ε + r ^ 2 * ‖(p.2 : EuclideanSpace ℝ (Fin (n - k)))‖ ^ 2))
      (p.1 : EuclideanSpace ℝ (Fin k)))) (r • (p.2 : EuclideanSpace ℝ (Fin (n - k))))

theorem cocoreModelPoint_norm_le {n k : ℕ} (hk : k ≤ n) (ε r : ℝ) (hε : 0 ≤ ε)
    (p : CellBoundary k × ClosedCell (n - k)) :
    morseNorm n (cocoreModelPoint hk ε r p) ≤ Real.sqrt (2 * ε + 2 * r ^ 2) := by
  apply le_of_sq_le_sq
  · change morseNorm n (recombine hk (negPart hk (cellMap (Real.sqrt (2 * ε + r ^ 2 * ‖(p.2 : EuclideanSpace ℝ (Fin (n - k)))‖ ^ 2))
        (p.1 : EuclideanSpace ℝ (Fin k)))) (r • (p.2 : EuclideanSpace ℝ (Fin (n - k))))) ^ 2 ≤
      (Real.sqrt (2 * ε + 2 * r ^ 2)) ^ 2
    rw [morseNorm_recombine_sq hk (negPart hk (cellMap (Real.sqrt (2 * ε + r ^ 2 * ‖(p.2 : EuclideanSpace ℝ (Fin (n - k)))‖ ^ 2))
      (p.1 : EuclideanSpace ℝ (Fin k)))) (r • (p.2 : EuclideanSpace ℝ (Fin (n - k))))]
    have h1 : ‖negPart hk (cellMap (Real.sqrt (2 * ε + r ^ 2 * ‖(p.2 : EuclideanSpace ℝ (Fin (n - k)))‖ ^ 2))
        (p.1 : EuclideanSpace ℝ (Fin k)))‖ ^ 2 = 2 * ε + r ^ 2 * ‖(p.2 : EuclideanSpace ℝ (Fin (n - k)))‖ ^ 2 := by
      have h := negPart_cellMap_norm_sq hk (Real.sqrt (2 * ε + r ^ 2 * ‖(p.2 : EuclideanSpace ℝ (Fin (n - k)))‖ ^ 2))
        (p.1 : EuclideanSpace ℝ (Fin k))
      rw [h]
      rw [Real.sq_sqrt (by positivity : 0 ≤ 2 * ε + r ^ 2 * ‖(p.2 : EuclideanSpace ℝ (Fin (n - k)))‖ ^ 2)]
      rw [p.1.2]
      ring
    have h2 : ‖(r • (p.2 : EuclideanSpace ℝ (Fin (n - k))) : EuclideanSpace ℝ (Fin (n - k)))‖ ^ 2 =
        r ^ 2 * ‖(p.2 : EuclideanSpace ℝ (Fin (n - k)))‖ ^ 2 := by
      rw [norm_smul]
      rw [Real.norm_eq_abs]
      rw [mul_pow]
      rw [sq_abs]
    rw [h1, h2]
    have hw : ‖(p.2 : EuclideanSpace ℝ (Fin (n - k)))‖ ^ 2 ≤ 1 := by
      have hneg : -1 ≤ ‖(p.2 : EuclideanSpace ℝ (Fin (n - k)))‖ := by
        linarith [norm_nonneg (p.2 : EuclideanSpace ℝ (Fin (n - k)))]
      exact (sq_le_sq' hneg p.2.2).trans_eq (by norm_num : (1 : ℝ) ^ 2 = 1)
    have hR2 : 2 * ε + 2 * r ^ 2 ≤ (Real.sqrt (2 * ε + 2 * r ^ 2)) ^ 2 := by
      rw [Real.sq_sqrt (by positivity : 0 ≤ 2 * ε + 2 * r ^ 2)]
    nlinarith [hw, sq_nonneg r, hR2]
  · exact Real.sqrt_nonneg _

theorem cocoreModelPoint_surjective_levelSet {n k : ℕ} (hk : k ≤ n) (c ε R : ℝ)
    (hε : 0 < ε) (hR : 0 ≤ R) (hRε : 2 * ε < R ^ 2)
    (y : MorseModel n) (hy : morseNormalForm hk c y = c - ε) (hnorm : morseNorm n y ≤ R) :
    ∃ p : CellBoundary k × ClosedCell (n - k),
      cocoreModelPoint hk ε (Real.sqrt ((R ^ 2 - 2 * ε) / 2)) p = y := by
  let a : EuclideanSpace ℝ (Fin k) := negPart hk y
  let b : EuclideanSpace ℝ (Fin (n - k)) := posPart hk y
  let r : ℝ := Real.sqrt ((R ^ 2 - 2 * ε) / 2)
  have hnormForm : morseNormalForm hk c y = c + (1 / 2) * (-‖a‖ ^ 2 + ‖b‖ ^ 2) := by
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
  have hle : morseNorm n y ^ 2 ≤ R ^ 2 := by
    exact sq_le_sq.mpr (by
      rw [abs_of_nonneg (norm_nonneg _), abs_of_nonneg hR]
      exact hnorm)
  have hnormSq : ‖a‖ ^ 2 + ‖b‖ ^ 2 ≤ R ^ 2 := by
    have hle' : ‖negPart hk y‖ ^ 2 + ‖posPart hk y‖ ^ 2 ≤ R ^ 2 := by
      rw [morseNorm_sq_eq_negPart_add_posPart hk y] at hle
      exact hle
    simpa [a, b] using hle'
  have hrel : ‖a‖ ^ 2 = ‖b‖ ^ 2 + 2 * ε := by
    rw [hnormForm] at hy
    nlinarith
  have hb : ‖b‖ ^ 2 ≤ r ^ 2 := by
    dsimp [r]
    have h1 : 0 ≤ (R ^ 2 - 2 * ε) / 2 := by
      nlinarith [hRε, sq_nonneg R]
    rw [Real.sq_sqrt h1]
    nlinarith [hnormSq, hrel]
  have ha0 : ‖a‖ ≠ 0 := by
    have hpos : 0 < ‖a‖ := by
      have hsq : 0 < ‖a‖ ^ 2 := by nlinarith [hrel, hε, sq_nonneg ‖b‖]
      exact lt_of_le_of_ne (norm_nonneg a) (Ne.symm (sq_pos_iff.mp hsq))
    exact ne_of_gt hpos
  have hpos_a : 0 < ‖a‖ := lt_of_le_of_ne (norm_nonneg a) (Ne.symm ha0)
  have hr : 0 < r := by
    dsimp [r]
    exact Real.sqrt_pos.mpr (by nlinarith [hRε])
  let u : CellBoundary k := ⟨(‖a‖)⁻¹ • a, by
    simpa [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hpos_a.le)] using
      (inv_mul_cancel₀ ha0)⟩
  let w : ClosedCell (n - k) := ⟨r⁻¹ • b, by
    rw [norm_smul]
    rw [Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (le_of_lt hr))]
    have hb' : ‖b‖ ≤ r := le_of_sq_le_sq hb (le_of_lt hr)
    have hm : r⁻¹ * ‖b‖ ≤ 1 := by
      calc
        r⁻¹ * ‖b‖ ≤ r⁻¹ * r := mul_le_mul_of_nonneg_left hb' (inv_nonneg.mpr (le_of_lt hr))
        _ = 1 := inv_mul_cancel₀ (ne_of_gt hr)
    simpa using hm⟩
  refine ⟨(u, w), ?_⟩
  change recombine hk (negPart hk (cellMap (Real.sqrt (2 * ε + r ^ 2 * ‖(w : EuclideanSpace ℝ (Fin (n - k)))‖ ^ 2))
      (u : EuclideanSpace ℝ (Fin k)))) (r • (w : EuclideanSpace ℝ (Fin (n - k)))) = y
  have hrw : (r • (w : EuclideanSpace ℝ (Fin (n - k)))) = b := by
    dsimp [w]
    rw [smul_smul, mul_inv_cancel₀ (ne_of_gt hr), one_smul]
  have hw : ‖(w : EuclideanSpace ℝ (Fin (n - k)))‖ = r⁻¹ * ‖b‖ := by
    dsimp [w]
    rw [norm_smul]
    rw [Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (le_of_lt hr))]
  have hs : Real.sqrt (2 * ε + r ^ 2 * ‖(w : EuclideanSpace ℝ (Fin (n - k)))‖ ^ 2) = ‖a‖ := by
    have hsqb : r ^ 2 * (r⁻¹ * ‖b‖) ^ 2 = ‖b‖ ^ 2 := by
      calc
        r ^ 2 * (r⁻¹ * ‖b‖) ^ 2 = (r ^ 2 * r⁻¹ ^ 2) * ‖b‖ ^ 2 := by ring
        _ = ‖b‖ ^ 2 := by
          have hri : r ^ 2 * r⁻¹ ^ 2 = 1 := by
            rw [← mul_pow, mul_inv_cancel₀ (ne_of_gt hr), one_pow]
          rw [hri, one_mul]
    have hsq : 2 * ε + r ^ 2 * ‖(w : EuclideanSpace ℝ (Fin (n - k)))‖ ^ 2 = ‖a‖ ^ 2 := by
      rw [hw]
      rw [hsqb]
      nlinarith [hrel]
    rw [hsq]
    exact Real.sqrt_sq (norm_nonneg a)
  have hna : negPart hk (cellMap (Real.sqrt (2 * ε + r ^ 2 * ‖(w : EuclideanSpace ℝ (Fin (n - k)))‖ ^ 2))
      (u : EuclideanSpace ℝ (Fin k))) = a := by
    ext i
    rw [negPart_cellMap_apply]
    rw [hs]
    dsimp [u]
    rw [← mul_assoc, mul_inv_cancel₀ ha0, one_mul]
  rw [hna, hrw, ← recombine_decompose hk y]

theorem modelFlow_levelSet_cover {n k : ℕ} (hk : k ≤ n) (c ε R : ℝ)
    (hε : 0 < ε) (hR : 0 ≤ R) (hRε : 2 * ε < R ^ 2)
    (z : MorseModel n)
    (hz : c - ε ≤ morseNormalForm hk c z)
    (hτ : 2 * (morseNormalForm hk c z - (c - ε)) ≤ ‖posPart hk z‖ ^ 2)
    (hnorm : morseNorm n z ≤ R) :
    ∃ p : CellBoundary k × ClosedCell (n - k),
      modelFlow hk (morseNormalForm hk c z - (c - ε)) z =
        cocoreModelPoint hk ε (Real.sqrt ((R ^ 2 - 2 * ε) / 2)) p := by
  let τ : ℝ := morseNormalForm hk c z - (c - ε)
  let w : MorseModel n := modelFlow hk τ z
  have hτ0 : 0 ≤ τ := by
    dsimp [τ]
    linarith
  have hτ' : τ ≤ ‖posPart hk z‖ ^ 2 / 2 := by
    dsimp [τ]
    nlinarith [hτ]
  have hwf : morseNormalForm hk c w = c - ε := by
    dsimp [w]
    rw [modelFlow_f_sub hk c τ z hτ0 hτ']
    dsimp [τ]
    ring
  have hwnorm : morseNorm n w ≤ R := by
    dsimp [w]
    exact le_trans (modelFlow_norm_le hk τ z hτ0 hτ') hnorm
  rcases cocoreModelPoint_surjective_levelSet hk c ε R hε hR hRε w hwf hwnorm with ⟨p, hp⟩
  refine ⟨p, ?_⟩
  simpa [w] using hp.symm

theorem modelHandle_meets_sublevel_eq_cocoreAttachingRange {n k : ℕ} (hk : k ≤ n)
    (c ε r : ℝ) (hε : 0 < ε) (hr : r ≠ 0) :
    modelHandle hk ε r ∩ sublevel (morseNormalForm hk c) (c - ε) =
      Set.range (fun p : CellBoundary k × ClosedCell (n - k) => cocoreModelPoint hk ε r p) := by
  rw [modelHandle_meets_lower_sublevel hk c ε r hε hr]
  ext y
  constructor
  · intro hy
    rcases hy with ⟨p, hp⟩
    exact ⟨p, by simpa [cocoreModelPoint, modelHandleMap_attachingRegion] using hp⟩
  · intro hy
    rcases hy with ⟨p, hp⟩
    exact ⟨p, by simpa [cocoreModelPoint, modelHandleMap_attachingRegion] using hp⟩

theorem negPart_cocoreModelPoint {n k : ℕ} (hk : k ≤ n) (ε r : ℝ)
    (p : CellBoundary k × ClosedCell (n - k)) :
    negPart hk (cocoreModelPoint hk ε r p) =
      negPart hk (cellMap (Real.sqrt (2 * ε + r ^ 2 * ‖(p.2 : EuclideanSpace ℝ (Fin (n - k)))‖ ^ 2))
        (p.1 : EuclideanSpace ℝ (Fin k))) := by
  dsimp [cocoreModelPoint]
  rw [negPart_recombine]

theorem posPart_cocoreModelPoint {n k : ℕ} (hk : k ≤ n) (ε r : ℝ)
    (p : CellBoundary k × ClosedCell (n - k)) :
    posPart hk (cocoreModelPoint hk ε r p) = r • (p.2 : EuclideanSpace ℝ (Fin (n - k))) := by
  dsimp [cocoreModelPoint]
  rw [posPart_recombine]

theorem morseNormalForm_cocoreModelPoint {n k : ℕ} (hk : k ≤ n) (c ε r : ℝ)
    (hε : 0 ≤ ε) (p : CellBoundary k × ClosedCell (n - k)) :
    morseNormalForm hk c (cocoreModelPoint hk ε r p) = c - ε := by
  dsimp [cocoreModelPoint]
  rw [← modelHandleMap_attachingRegion hk ε r p.1 p.2]
  exact modelHandleMap_f_boundary hk c ε r hε p.1 p.2

theorem modelFlow_levelSet_collar_cover {n k : ℕ} (hk : k ≤ n) (c ε R : ℝ)
    (hε : 0 < ε) (hR : 0 ≤ R) (hRε : 2 * ε < R ^ 2)
    (z : MorseModel n)
    (hz : c - ε ≤ morseNormalForm hk c z)
    (hτ : 2 * (morseNormalForm hk c z - (c - ε)) < ‖posPart hk z‖ ^ 2)
    (hnorm : morseNorm n z ≤ R) :
    ∃ p : CellBoundary k × ClosedCell (n - k),
      z = modelFlow hk (-(morseNormalForm hk c z - (c - ε)))
        (cocoreModelPoint hk ε (Real.sqrt ((R ^ 2 - 2 * ε) / 2)) p) := by
  let τ : ℝ := morseNormalForm hk c z - (c - ε)
  have hτ0 : 0 ≤ τ := by
    dsimp [τ]
    linarith
  have hτle : 2 * (morseNormalForm hk c z - (c - ε)) ≤ ‖posPart hk z‖ ^ 2 := by
    nlinarith [hτ]
  rcases modelFlow_levelSet_cover hk c ε R hε hR hRε z hz hτle hnorm with ⟨p, hp⟩
  refine ⟨p, ?_⟩
  have hrev : modelFlow hk (-τ) (modelFlow hk τ z) = z := modelFlow_rev hk τ z hτ0 hτ
  have hflow : modelFlow hk (-τ) (modelFlow hk τ z) =
      modelFlow hk (-τ) (cocoreModelPoint hk ε (Real.sqrt ((R ^ 2 - 2 * ε) / 2)) p) := by
    exact congrArg (fun w : MorseModel n => modelFlow hk (-τ) w) hp
  simpa [τ] using (hflow.symm.trans hrev).symm

noncomputable def modelHandleCollarMap {n k : ℕ} (hk : k ≤ n) (ε r : ℝ)
    (p : CellBoundary k × ClosedCell (n - k)) (s : ℝ) : MorseModel n :=
  modelFlow hk (-s) (cocoreModelPoint hk ε r p)

theorem modelHandleCollarMap_negPart {n k : ℕ} (hk : k ≤ n) (ε r : ℝ)
    (p : CellBoundary k × ClosedCell (n - k)) (s : ℝ) :
    negPart hk (modelHandleCollarMap hk ε r p s) = negPart hk (cocoreModelPoint hk ε r p) := by
  dsimp [modelHandleCollarMap]
  rw [modelFlow_negPart]

theorem modelHandleCollarMap_posPart {n k : ℕ} (hk : k ≤ n) (ε r : ℝ)
    (p : CellBoundary k × ClosedCell (n - k)) (s : ℝ) :
    posPart hk (modelHandleCollarMap hk ε r p s) =
      (Real.sqrt (1 + 2 * s / ‖posPart hk (cocoreModelPoint hk ε r p)‖ ^ 2)) •
        posPart hk (cocoreModelPoint hk ε r p) := by
  dsimp [modelHandleCollarMap]
  rw [modelFlow_posPart]
  congr 1
  ring_nf

theorem modelHandleCollarMap_f_value {n k : ℕ} (hk : k ≤ n) (c ε r s : ℝ)
    (p : CellBoundary k × ClosedCell (n - k)) (hε : 0 ≤ ε) (hs0 : 0 ≤ s) (hr : r ≠ 0)
    (hw : 0 < ‖(p.2 : EuclideanSpace ℝ (Fin (n - k)))‖) :
    morseNormalForm hk c (modelHandleCollarMap hk ε r p s) = c - ε + s := by
  dsimp [modelHandleCollarMap]
  rw [modelFlow_f_add hk c s (cocoreModelPoint hk ε r p) hs0]
  · rw [morseNormalForm_cocoreModelPoint hk c ε r hε p]
  · rw [posPart_cocoreModelPoint]
    rw [norm_smul]
    rw [Real.norm_eq_abs]
    exact mul_pos (abs_pos.mpr hr) (by positivity)

theorem modelHandleCollarMap_posPart_norm_sq {n k : ℕ} (hk : k ≤ n) (ε r s : ℝ)
    (p : CellBoundary k × ClosedCell (n - k)) (hs0 : 0 ≤ s) (hr : r ≠ 0)
    (hw : 0 < ‖(p.2 : EuclideanSpace ℝ (Fin (n - k)))‖) :
    ‖posPart hk (modelHandleCollarMap hk ε r p s)‖ ^ 2 =
      r ^ 2 * ‖(p.2 : EuclideanSpace ℝ (Fin (n - k)))‖ ^ 2 + 2 * s := by
  dsimp [modelHandleCollarMap]
  rw [modelFlow_up_posPart_norm_sq hk s (cocoreModelPoint hk ε r p) hs0]
  · rw [posPart_cocoreModelPoint]
    rw [norm_smul]
    rw [Real.norm_eq_abs]
    rw [mul_pow]
    rw [sq_abs]
  · rw [posPart_cocoreModelPoint]
    rw [norm_smul]
    rw [Real.norm_eq_abs]
    exact mul_pos (abs_pos.mpr hr) (by positivity)

theorem modelHandleCollarMap_mem_sublevel {n k : ℕ} (hk : k ≤ n) (c ε r s b : ℝ)
    (p : CellBoundary k × ClosedCell (n - k)) (hε : 0 ≤ ε) (hs0 : 0 ≤ s) (hs1 : s ≤ r ^ 2 / 2)
    (hb : c - ε + r ^ 2 / 2 ≤ b) (hr : r ≠ 0)
    (hw : 0 < ‖(p.2 : EuclideanSpace ℝ (Fin (n - k)))‖) :
    modelHandleCollarMap hk ε r p s ∈ sublevel (morseNormalForm hk c) b := by
  change morseNormalForm hk c (modelHandleCollarMap hk ε r p s) ≤ b
  rw [modelHandleCollarMap_f_value hk c ε r s p hε hs0 hr hw]
  nlinarith [hs1, hb]

theorem modelHandleCollarMap_mem_lower_iff {n k : ℕ} (hk : k ≤ n) (c ε r s : ℝ)
    (p : CellBoundary k × ClosedCell (n - k)) (hε : 0 ≤ ε) (hs0 : 0 ≤ s)
    (hr : r ≠ 0) (hw : 0 < ‖(p.2 : EuclideanSpace ℝ (Fin (n - k)))‖) :
    modelHandleCollarMap hk ε r p s ∈ sublevel (morseNormalForm hk c) (c - ε) ↔ s = 0 := by
  constructor
  · intro hq
    have hval := modelHandleCollarMap_f_value hk c ε r s p hε hs0 hr hw
    change morseNormalForm hk c (modelHandleCollarMap hk ε r p s) ≤ c - ε at hq
    rw [hval] at hq
    nlinarith [hs0, hq]
  · intro hs
    change morseNormalForm hk c (modelHandleCollarMap hk ε r p s) ≤ c - ε
    rw [modelHandleCollarMap_f_value hk c ε r s p hε hs0 hr hw, hs]
    norm_num

theorem modelHandleCollarMap_attachingRegion {n k : ℕ} (hk : k ≤ n) (ε r : ℝ)
    (p : CellBoundary k × ClosedCell (n - k)) :
    modelHandleCollarMap hk ε r p 0 = cocoreModelPoint hk ε r p := by
  dsimp [modelHandleCollarMap]
  norm_num
  rw [modelFlow_zero]

noncomputable def cocoreAttachingEmbedding {n k : ℕ} (hk : k ≤ n) (c ε r : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ (MorseModel n) H} {f : M → ℝ}
    (data : MorseChart n k hk c I f)
    (hε : 0 < ε) (hεr : Real.sqrt (2 * ε + 2 * r ^ 2) ≤ data.R) :
    CellBoundary k × ClosedCell (n - k) → LevelSetSpace f (c - ε) :=
  fun p =>
    let y : MorseModel n := cocoreModelPoint hk ε r p
    ⟨data.χ y, by
      have hnormb : morseNorm n y ≤ data.R := by
        exact le_trans (cocoreModelPoint_norm_le hk ε r (le_of_lt hε) p) hεr
      change f (data.χ y) = c - ε
      rw [data.hnorm y hnormb]
      change morseNormalForm hk c (cocoreModelPoint hk ε r p) = c - ε
      dsimp [cocoreModelPoint]
      have hrecomb := morseNormalForm_recombine hk c (Real.sqrt (2 * ε + r ^ 2 * ‖(p.2 : EuclideanSpace ℝ (Fin (n - k)))‖ ^ 2))
        (p.1 : EuclideanSpace ℝ (Fin k)) (r • (p.2 : EuclideanSpace ℝ (Fin (n - k))))
      rw [hrecomb]
      have hsq : (Real.sqrt (2 * ε + r ^ 2 * ‖(p.2 : EuclideanSpace ℝ (Fin (n - k)))‖ ^ 2)) ^ 2 =
          2 * ε + r ^ 2 * ‖(p.2 : EuclideanSpace ℝ (Fin (n - k)))‖ ^ 2 := by
        rw [Real.sq_sqrt (by positivity : 0 ≤ 2 * ε + r ^ 2 * ‖(p.2 : EuclideanSpace ℝ (Fin (n - k)))‖ ^ 2)]
      have hnorm2 : ‖(r • (p.2 : EuclideanSpace ℝ (Fin (n - k))) : EuclideanSpace ℝ (Fin (n - k)))‖ ^ 2 =
          r ^ 2 * ‖(p.2 : EuclideanSpace ℝ (Fin (n - k)))‖ ^ 2 := by
        rw [norm_smul]
        rw [Real.norm_eq_abs]
        rw [mul_pow]
        rw [sq_abs]
      rw [hsq, hnorm2, p.1.2]
      ring_nf⟩

theorem cocoreModelPoint_core_eq {n k : ℕ} (hk : k ≤ n) (ε r : ℝ)
    (b : CellBoundary k) :
    cocoreModelPoint hk ε r (b, (⟨(0 : EuclideanSpace ℝ (Fin (n - k))), by simp⟩ : ClosedCell (n - k))) =
      cellMap (Real.sqrt (2 * ε)) (b : EuclideanSpace ℝ (Fin k)) := by
  dsimp [cocoreModelPoint]
  have hsqrt : Real.sqrt (2 * ε + r ^ 2 * ‖(0 : EuclideanSpace ℝ (Fin (n - k)))‖ ^ 2) =
      Real.sqrt (2 * ε) := by
    simp
  rw [hsqrt]
  rw [smul_zero]
  have hz : (0 : EuclideanSpace ℝ (Fin (n - k))) =
      posPart hk (cellMap (Real.sqrt (2 * ε)) (b : EuclideanSpace ℝ (Fin k))) := by
    ext i
    change 0 = cellMap (Real.sqrt (2 * ε)) (b : EuclideanSpace ℝ (Fin k)) (posIdx hk i)
    exact (cellMap_posIdx hk (Real.sqrt (2 * ε)) (b : EuclideanSpace ℝ (Fin k)) i).symm
  rw [hz]
  exact recombine_decompose hk (cellMap (Real.sqrt (2 * ε)) (b : EuclideanSpace ℝ (Fin k)))

theorem cocoreAttachingEmbedding_value {n k : ℕ} (hk : k ≤ n) (c ε r : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ (MorseModel n) H} {f : M → ℝ}
    (data : MorseChart n k hk c I f)
    (hε : 0 < ε) (hεr : Real.sqrt (2 * ε + 2 * r ^ 2) ≤ data.R)
    (p : CellBoundary k × ClosedCell (n - k)) :
    f ((cocoreAttachingEmbedding hk c ε r data hε hεr p).1) = c - ε := by
  exact (cocoreAttachingEmbedding hk c ε r data hε hεr p).2

theorem contMDiff_cocoreAttachingEmbedding {m k : ℕ} (hk : k ≤ m + 1) (c ε r : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} [I.Boundaryless]
    [IsManifold I (⊤ : WithTop ℕ∞) M] [T2Space M] {f : M → ℝ}
    (data : MorseChart (m + 1) k hk c I f)
    (hε : 0 < ε) (hεr : Real.sqrt (2 * ε + 2 * r ^ 2) ≤ data.R)
    (hεr' : Real.sqrt (2 * ε + 2 * r ^ 2) < data.R')
    (hf : ContMDiff I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) f)
    (hreg : ∀ x : M, f x = c - ε → ¬ IsCriticalPointAt I f x)
    [NeZero k] [NeZero (m + 1 - k)] :
    @ContMDiff ℝ _
      (EuclideanSpace ℝ (Fin (k - 1)) × EuclideanSpace ℝ (Fin ((m + 1 - k - 1) + 1))) _ _
      (ModelProd (EuclideanSpace ℝ (Fin (k - 1))) (EuclideanHalfSpace ((m + 1 - k - 1) + 1))) _
      ((𝓡 (k - 1)).prod (modelWithCornersEuclideanHalfSpace ((m + 1 - k - 1) + 1)))
      (AttachingRegion k (m + 1 - k)) _ (attachingRegionChartedSpace k (m + 1 - k))
      (MorseModel m) _ _ (MorseModel m) _
      (𝓘(ℝ, MorseModel m)) (LevelSetSpace f (c - ε)) _
      (manifoldLevelSetChartedSpace I f (c - ε) hf hreg)
      (⊤ : ℕ∞)
      (cocoreAttachingEmbedding hk c ε r data hε hεr) := by
  classical
  letI : ChartedSpace (EuclideanSpace ℝ (Fin (k - 1))) (CellBoundary k) :=
    cellBoundaryChartedSpace k
  letI : ChartedSpace (EuclideanHalfSpace ((m + 1 - k - 1) + 1)) (ClosedCell (m + 1 - k)) :=
    closedCellChartedSpace (m + 1 - k)
  letI : ChartedSpace (EuclideanHalfSpace ((m + 1 - k - 1) + 1)) (ClosedCell ((m + 1 - k - 1) + 1)) :=
    closedCellChartedSpaceSucc (m + 1 - k - 1)
  letI : IsManifold (𝓡 (k - 1)) (⊤ : ℕ∞) (CellBoundary k) := cellBoundaryIsManifold k
  letI : IsManifold (modelWithCornersEuclideanHalfSpace ((m + 1 - k - 1) + 1)) (⊤ : ℕ∞)
      (ClosedCell ((m + 1 - k - 1) + 1)) := closedCellIsManifold (m + 1 - k - 1)
  letI : IsManifold (modelWithCornersEuclideanHalfSpace ((m + 1 - k - 1) + 1)) (⊤ : ℕ∞)
      (ClosedCell (m + 1 - k)) :=
    isManifoldOfHomeomorph (modelWithCornersEuclideanHalfSpace ((m + 1 - k - 1) + 1))
      (closedCellReindexHomeo (m + 1 - k))
  letI : ChartedSpace (ModelProd (EuclideanSpace ℝ (Fin (k - 1)))
      (EuclideanHalfSpace ((m + 1 - k - 1) + 1))) (AttachingRegion k (m + 1 - k)) :=
    attachingRegionChartedSpace k (m + 1 - k)
  letI : ChartedSpace (MorseModel m) (LevelSetSpace f (c - ε)) :=
    manifoldLevelSetChartedSpace I f (c - ε) hf hreg
  let Iatt : ModelWithCorners ℝ
      (EuclideanSpace ℝ (Fin (k - 1)) × EuclideanSpace ℝ (Fin ((m + 1 - k - 1) + 1)))
      (ModelProd (EuclideanSpace ℝ (Fin (k - 1))) (EuclideanHalfSpace ((m + 1 - k - 1) + 1))) :=
    (𝓡 (k - 1)).prod (modelWithCornersEuclideanHalfSpace ((m + 1 - k - 1) + 1))
  letI : IsManifold Iatt (⊤ : ℕ∞) (AttachingRegion k (m + 1 - k)) :=
    attachingRegionIsManifold k (m + 1 - k)
  have hrecomb : ContMDiff Iatt (𝓘(ℝ, MorseModel (m + 1))) (⊤ : ℕ∞)
      (fun p : AttachingRegion k (m + 1 - k) =>
        cocoreModelPoint hk ε r p) := by
    simpa [Iatt, cocoreModelPoint] using (attachingRegionContMDiff_of
      (F := fun q : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin (m + 1 - k)) =>
        recombine hk (negPart hk (cellMap (Real.sqrt (2 * ε + r ^ 2 * ‖q.2‖ ^ 2)) q.1)) (r • q.2))
      (recombine_contDiff_cocore hk r ε hε))
  have hrecombOn : ContMDiffOn Iatt (𝓘(ℝ, MorseModel (m + 1))) (⊤ : ℕ∞)
      (fun p : AttachingRegion k (m + 1 - k) => cocoreModelPoint hk ε r p) Set.univ := by
    rw [contMDiffOn_univ]
    exact hrecomb
  have hball : ∀ p : AttachingRegion k (m + 1 - k),
      cocoreModelPoint hk ε r p ∈ Metric.ball (0 : MorseModel (m + 1)) data.R' := by
    intro p
    have hlt : ‖cocoreModelPoint hk ε r p‖ < data.R' :=
      lt_of_le_of_lt (morseNorm_piNorm_le (cocoreModelPoint hk ε r p))
        (lt_of_le_of_lt (cocoreModelPoint_norm_le hk ε r (le_of_lt hε) p) hεr')
    simpa [Metric.mem_ball, dist_eq_norm] using hlt
  have hχ : ContMDiffOn Iatt I (⊤ : ℕ∞)
      (fun p : AttachingRegion k (m + 1 - k) => data.χ (cocoreModelPoint hk ε r p)) Set.univ := by
    refine data.hχon.comp hrecombOn ?_
    intro p hp
    exact hball p
  have hχ' : ContMDiff Iatt I (⊤ : ℕ∞)
      (fun p : AttachingRegion k (m + 1 - k) => data.χ (cocoreModelPoint hk ε r p)) := by
    rw [← contMDiffOn_univ]
    exact hχ
  have hFa : ∀ p : AttachingRegion k (m + 1 - k),
      f (data.χ (cocoreModelPoint hk ε r p)) = c - ε := by
    intro p
    simpa [cocoreAttachingEmbedding, cocoreModelPoint] using
      (cocoreAttachingEmbedding_value hk c ε r data hε hεr p)
  have hfac : ContMDiff Iatt (𝓘(ℝ, MorseModel m)) (⊤ : ℕ∞)
      (fun p : AttachingRegion k (m + 1 - k) =>
        (⟨data.χ (cocoreModelPoint hk ε r p), hFa p⟩ : LevelSetSpace f (c - ε))) :=
    contMDiff_levelSet_factor I f (c - ε) hf hreg
      (IX := Iatt) (F := fun p : AttachingRegion k (m + 1 - k) => data.χ (cocoreModelPoint hk ε r p))
      (hF := hχ') (hFa := hFa)
  refine hfac.congr ?_
  intro p
  apply Subtype.ext
  rfl

theorem cocoreAttachingEmbedding_injective {n k : ℕ} (hk : k ≤ n) (c ε r : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ (MorseModel n) H} {f : M → ℝ}
    (data : MorseChart n k hk c I f)
    (hε : 0 < ε) (hr : r ≠ 0) (hεr : Real.sqrt (2 * ε + 2 * r ^ 2) ≤ data.R) :
    Function.Injective (cocoreAttachingEmbedding hk c ε r data hε hεr) := by
  intro p q h
  have hχ : data.χ (cocoreModelPoint hk ε r p) = data.χ (cocoreModelPoint hk ε r q) := by
    have hz := congrArg (fun z : LevelSetSpace f (c - ε) => z.1) h
    simpa [cocoreAttachingEmbedding, cocoreModelPoint] using hz
  have hnormb : ∀ x : CellBoundary k × ClosedCell (n - k),
      morseNorm n (cocoreModelPoint hk ε r x) ≤ data.R := by
    intro x
    exact le_trans (cocoreModelPoint_norm_le hk ε r (le_of_lt hε) x) hεr
  have hsrc_p : cocoreModelPoint hk ε r p ∈ data.χ.source :=
    data.hχsrc (cocoreModelPoint hk ε r p) (hnormb p)
  have hsrc_q : cocoreModelPoint hk ε r q ∈ data.χ.source :=
    data.hχsrc (cocoreModelPoint hk ε r q) (hnormb q)
  have hy : cocoreModelPoint hk ε r p = cocoreModelPoint hk ε r q :=
    data.χ.injOn hsrc_p hsrc_q hχ
  exact (recombine_cellMap_cocore_injective hk ε r hε hr) hy

theorem isClosedEmbedding_cocoreAttachingEmbedding {m k : ℕ} (hk : k ≤ m + 1) (c ε r : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} [I.Boundaryless]
    [IsManifold I (⊤ : WithTop ℕ∞) M] [T2Space M] {f : M → ℝ}
    (data : MorseChart (m + 1) k hk c I f)
    (hε : 0 < ε) (hr : r ≠ 0) (hεr : Real.sqrt (2 * ε + 2 * r ^ 2) ≤ data.R)
    (hεr' : Real.sqrt (2 * ε + 2 * r ^ 2) < data.R')
    (hf : ContMDiff I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) f)
    (hreg : ∀ x : M, f x = c - ε → ¬ IsCriticalPointAt I f x)
    [NeZero k] [NeZero (m + 1 - k)] :
    Topology.IsClosedEmbedding (cocoreAttachingEmbedding hk c ε r data hε hεr) := by
  letI : ChartedSpace (MorseModel m) (LevelSetSpace f (c - ε)) :=
    manifoldLevelSetChartedSpace I f (c - ε) hf hreg
  exact (contMDiff_cocoreAttachingEmbedding hk c ε r data hε hεr hεr' hf hreg).continuous.isClosedEmbedding
    (cocoreAttachingEmbedding_injective hk c ε r data hε hr hεr)

noncomputable def handleCollarMap {m k : ℕ} (hk : k ≤ m + 1) (c ε r : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} [I.Boundaryless]
    [IsManifold I (⊤ : WithTop ℕ∞) M] [T2Space M] {f : M → ℝ}
    (data : MorseChart (m + 1) k hk c I f)
    (hε : 0 < ε) (hεr : Real.sqrt (2 * ε + 2 * r ^ 2) ≤ data.R)
    (v : (x : M) → TangentSpace I x)
    (hcomplete : ∀ x : M, ∃ γ : ℝ → M, γ 0 = x ∧ IsMIntegralCurve γ v) :
    AttachingRegion k (m + 1 - k) × Set.Icc (0 : ℝ) 1 → M :=
  fun q =>
    curveAt v hcomplete (cocoreAttachingEmbedding hk c ε r data hε hεr q.1).1
      (-(r ^ 2 * (1 - (q.2 : ℝ)) / 2))

theorem handleCollarMap_value {m k : ℕ} (hk : k ≤ m + 1) (c ε r δ : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} [I.Boundaryless]
    [IsManifold I (⊤ : WithTop ℕ∞) M] [T2Space M] {f : M → ℝ}
    (data : MorseChart (m + 1) k hk c I f)
    (hε : 0 < ε) (hεr : Real.sqrt (2 * ε + 2 * r ^ 2) ≤ data.R)
    (hδ : r ^ 2 / 2 < δ)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) f)
    (v : (x : M) → TangentSpace I x)
    (hdfOn : ∀ x ∈ f ⁻¹' Set.Icc (c - ε) (c + δ),
      (NormedSpace.fromTangentSpace (f x)) ((mfderiv I 𝓘(ℝ, ℝ) f x) (v x)) = -1)
    (hrate : ∀ x, -1 ≤ (NormedSpace.fromTangentSpace (f x)) ((mfderiv I 𝓘(ℝ, ℝ) f x) (v x)) ∧
      (NormedSpace.fromTangentSpace (f x)) ((mfderiv I 𝓘(ℝ, ℝ) f x) (v x)) ≤ 0)
    (hcomplete : ∀ x : M, ∃ γ : ℝ → M, γ 0 = x ∧ IsMIntegralCurve γ v)
    (q : AttachingRegion k (m + 1 - k) × Set.Icc (0 : ℝ) 1) :
    f (handleCollarMap hk c ε r data hε hεr v hcomplete q) =
      c - ε + r ^ 2 * (1 - (q.2 : ℝ)) / 2 := by
  let s : ℝ := r ^ 2 * (1 - (q.2 : ℝ)) / 2
  let x : M := (cocoreAttachingEmbedding hk c ε r data hε hεr q.1).1
  have hs0 : 0 ≤ s := by
    dsimp [s]
    have h1 : 0 ≤ 1 - (q.2 : ℝ) := sub_nonneg.mpr q.2.property.2
    exact div_nonneg (mul_nonneg (sq_nonneg r) h1) (by norm_num)
  have hx : f x = c - ε := cocoreAttachingEmbedding_value hk c ε r data hε hεr q.1
  have hstay : ∀ t ∈ Set.Icc (0 : ℝ) s,
      curveAt v hcomplete x (-t) ∈ f ⁻¹' Set.Icc (c - ε) (c + δ) := by
    intro t ht
    have hrb := f_rate_bounds_of_integralCurve_back f hf v hrate
      (hγ := curveAt_integralCurve v hcomplete x) (t := t) ht.1
    have hlo : c - ε ≤ f (curveAt v hcomplete x (-t)) := by
      have hb := hrb.1
      simpa [curveAt_zero v hcomplete x, hx] using hb
    have hhi : f (curveAt v hcomplete x (-t)) ≤ c + δ := by
      have hb := hrb.2
      have hb' : f (curveAt v hcomplete x (-t)) ≤ f x + t := by
        simpa [curveAt_zero v hcomplete x] using hb
      have htle : t ≤ s := ht.2
      have hsle : c - ε + s ≤ c + δ := by
        have hs : s ≤ r ^ 2 / 2 := by
          dsimp [s]
          have h1 : 0 ≤ 1 - (q.2 : ℝ) := sub_nonneg.mpr q.2.property.2
          have h1' : 0 ≤ (q.2 : ℝ) := q.2.property.1
          nlinarith [sq_nonneg r, h1, h1']
        nlinarith [hδ, hs, hε]
      nlinarith [hx, hb', htle, hsle]
    change c - ε ≤ f (curveAt v hcomplete x (-t)) ∧ f (curveAt v hcomplete x (-t)) ≤ c + δ
    exact ⟨hlo, hhi⟩
  have hEq := f_add_of_integralCurve_back f hf v hdfOn
    (hγ := curveAt_integralCurve v hcomplete x) (t := s) hs0 hstay
  change f (curveAt v hcomplete x (-s)) = c - ε + r ^ 2 * (1 - (q.2 : ℝ)) / 2
  rw [hEq]
  rw [curveAt_zero v hcomplete x, hx]

theorem contMDiff_handleCollarMap {m k : ℕ} (hk : k ≤ m + 1) (c ε r : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} [I.Boundaryless]
    [IsManifold I (⊤ : WithTop ℕ∞) M] [T2Space M] {f : M → ℝ}
    (data : MorseChart (m + 1) k hk c I f)
    (hε : 0 < ε) (hεr : Real.sqrt (2 * ε + 2 * r ^ 2) ≤ data.R) (hRltR' : data.R < data.R')
    (hf : ContMDiff I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) f)
    (hreg : ∀ x : M, f x = c - ε → ¬ IsCriticalPointAt I f x)
    (v : (x : M) → TangentSpace I x)
    (hv : ContMDiff I (I.prod 𝓘(ℝ, MorseModel (m + 1))) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : M => (⟨x, v x⟩ : TangentBundle I M)))
    (hsupp : IsCompact (tsupport v))
    (hcomplete : ∀ x : M, ∃ γ : ℝ → M, γ 0 = x ∧ IsMIntegralCurve γ v)
    [NeZero k] [NeZero (m + 1 - k)] :
    @ContMDiff ℝ _
      ((EuclideanSpace ℝ (Fin (k - 1)) × EuclideanSpace ℝ (Fin ((m + 1 - k - 1) + 1))) ×
        EuclideanSpace ℝ (Fin 1)) _ _
      (ModelProd (ModelProd (EuclideanSpace ℝ (Fin (k - 1)))
        (EuclideanHalfSpace ((m + 1 - k - 1) + 1))) (EuclideanHalfSpace 1)) _
      (((𝓡 (k - 1)).prod (modelWithCornersEuclideanHalfSpace ((m + 1 - k - 1) + 1))).prod
        (modelWithCornersEuclideanHalfSpace 1))
      (AttachingRegion k (m + 1 - k) × Set.Icc (0 : ℝ) 1) _
      (prodChartedSpace (ModelProd (EuclideanSpace ℝ (Fin (k - 1)))
        (EuclideanHalfSpace ((m + 1 - k - 1) + 1))) (AttachingRegion k (m + 1 - k))
        (EuclideanHalfSpace 1) (Set.Icc (0 : ℝ) 1))
      (MorseModel (m + 1)) _ _ H _
      I M _ _
      (⊤ : ℕ∞)
      (handleCollarMap hk c ε r data hε hεr v hcomplete) := by
  classical
  letI : ChartedSpace (MorseModel m) (LevelSetSpace f (c - ε)) :=
    manifoldLevelSetChartedSpace I f (c - ε) hf hreg
  letI : ChartedSpace (EuclideanSpace ℝ (Fin (k - 1))) (CellBoundary k) :=
    cellBoundaryChartedSpace k
  letI : ChartedSpace (EuclideanHalfSpace ((m + 1 - k - 1) + 1)) (ClosedCell (m + 1 - k)) :=
    closedCellChartedSpace (m + 1 - k)
  letI : ChartedSpace (EuclideanHalfSpace ((m + 1 - k - 1) + 1)) (ClosedCell ((m + 1 - k - 1) + 1)) :=
    closedCellChartedSpaceSucc (m + 1 - k - 1)
  letI : IsManifold (𝓡 (k - 1)) (⊤ : ℕ∞) (CellBoundary k) := cellBoundaryIsManifold k
  letI : IsManifold (modelWithCornersEuclideanHalfSpace ((m + 1 - k - 1) + 1)) (⊤ : ℕ∞)
      (ClosedCell ((m + 1 - k - 1) + 1)) := closedCellIsManifold (m + 1 - k - 1)
  letI : IsManifold (modelWithCornersEuclideanHalfSpace ((m + 1 - k - 1) + 1)) (⊤ : ℕ∞)
      (ClosedCell (m + 1 - k)) :=
    isManifoldOfHomeomorph (modelWithCornersEuclideanHalfSpace ((m + 1 - k - 1) + 1))
      (closedCellReindexHomeo (m + 1 - k))
  let Iatt : ModelWithCorners ℝ
      (EuclideanSpace ℝ (Fin (k - 1)) × EuclideanSpace ℝ (Fin ((m + 1 - k - 1) + 1)))
      (ModelProd (EuclideanSpace ℝ (Fin (k - 1))) (EuclideanHalfSpace ((m + 1 - k - 1) + 1))) :=
    (𝓡 (k - 1)).prod (modelWithCornersEuclideanHalfSpace ((m + 1 - k - 1) + 1))
  letI : IsManifold Iatt (⊤ : ℕ∞) (AttachingRegion k (m + 1 - k)) :=
    attachingRegionIsManifold k (m + 1 - k)
  have hφ : ContMDiff Iatt I (⊤ : ℕ∞) (fun p : AttachingRegion k (m + 1 - k) =>
      (cocoreAttachingEmbedding hk c ε r data hε hεr p).1) := by
    have hφ' : ContMDiff Iatt (𝓘(ℝ, MorseModel m)) (⊤ : ℕ∞)
        (cocoreAttachingEmbedding hk c ε r data hε hεr) := by
      simpa [Iatt] using (contMDiff_cocoreAttachingEmbedding hk c ε r data hε hεr
        (lt_of_le_of_lt hεr hRltR') hf hreg)
    have hinc : ContMDiff (𝓘(ℝ, MorseModel m)) I (⊤ : ℕ∞)
        (fun x : LevelSetSpace f (c - ε) => x.1) :=
      contMDiff_levelSetInclusion I f (c - ε) hf hreg
    exact hinc.comp hφ'
  have hlin : ContDiff ℝ (⊤ : ℕ∞) (fun z : ℝ => -(r ^ 2 * (1 - z) / 2)) := by
    fun_prop
  have hcoe : ContMDiff (𝓡∂ 1) (𝓘(ℝ, ℝ)) (⊤ : ℕ∞)
      (fun z : Set.Icc (0 : ℝ) 1 => (z : ℝ)) :=
    contMDiff_subtype_coe_Icc (x := 0) (y := 1) (n := (⊤ : ℕ∞))
  have hsnd : ContMDiff (Iatt.prod (𝓡∂ 1)) (𝓡∂ 1) (⊤ : ℕ∞)
      (fun q : AttachingRegion k (m + 1 - k) × Set.Icc (0 : ℝ) 1 => q.2) :=
    contMDiff_snd (I := Iatt) (J := 𝓡∂ 1) (n := (⊤ : ℕ∞))
  have hT : ContMDiff (Iatt.prod (𝓡∂ 1)) (𝓘(ℝ, ℝ)) (⊤ : ℕ∞)
      (fun q : AttachingRegion k (m + 1 - k) × Set.Icc (0 : ℝ) 1 =>
        -(r ^ 2 * (1 - (q.2 : ℝ)) / 2)) :=
    (contMDiff_iff_contDiff.mpr hlin).comp (hcoe.comp hsnd)
  have hfst : ContMDiff (Iatt.prod (𝓡∂ 1)) Iatt (⊤ : ℕ∞)
      (fun q : AttachingRegion k (m + 1 - k) × Set.Icc (0 : ℝ) 1 => q.1) :=
    contMDiff_fst (I := Iatt) (J := 𝓡∂ 1) (n := (⊤ : ℕ∞))
  have hφ1 : ContMDiff (Iatt.prod (𝓡∂ 1)) I (⊤ : ℕ∞)
      (fun q : AttachingRegion k (m + 1 - k) × Set.Icc (0 : ℝ) 1 =>
        (cocoreAttachingEmbedding hk c ε r data hε hεr q.1).1) :=
    hφ.comp hfst
  have hpair : ContMDiff (Iatt.prod (𝓡∂ 1)) ((𝓘(ℝ, ℝ)).prod I) (⊤ : ℕ∞)
      (fun q : AttachingRegion k (m + 1 - k) × Set.Icc (0 : ℝ) 1 =>
        (-(r ^ 2 * (1 - (q.2 : ℝ)) / 2),
          (cocoreAttachingEmbedding hk c ε r data hε hεr q.1).1)) :=
    ContMDiff.prodMk hT hφ1
  have hflow0 : ContMDiff ((𝓘(ℝ, ℝ)).prod I) I (⊤ : ℕ∞)
      (fun q : ℝ × M => curveAt v (exists_globalIntegralCurve_of_compactSupport v hv hsupp) q.2 q.1) :=
    contMDiff_globalFlow_joint_of_compactSupport (E := MorseModel (m + 1)) (I := I)
      (v := v) (hv := hv) (hsupp := hsupp)
  have hflow : ContMDiff ((𝓘(ℝ, ℝ)).prod I) I (⊤ : ℕ∞)
      (fun q : ℝ × M => curveAt v hcomplete q.2 q.1) := by
    refine hflow0.congr ?_
    intro q
    exact curveAt_hcomplete_irrel (E := MorseModel (m + 1)) (I := I) v
      (hv := (hv.of_le (show (1 : WithTop ℕ∞) ≤ (⊤ : ℕ∞) by
        exact_mod_cast (le_top : (1 : ℕ∞) ≤ (⊤ : ℕ∞)))))
      (exists_globalIntegralCurve_of_compactSupport v hv hsupp) hcomplete q.2 q.1
  have hmain : ContMDiff (Iatt.prod (𝓡∂ 1)) I (⊤ : ℕ∞)
      (fun q : AttachingRegion k (m + 1 - k) × Set.Icc (0 : ℝ) 1 =>
        curveAt v hcomplete (cocoreAttachingEmbedding hk c ε r data hε hεr q.1).1
          (-(r ^ 2 * (1 - (q.2 : ℝ)) / 2))) :=
    hflow.comp hpair
  refine hmain.congr ?_
  intro q
  rfl

theorem handleCollarMap_injective {m k : ℕ} (hk : k ≤ m + 1) (c ε r δ : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} [I.Boundaryless]
    [IsManifold I (⊤ : WithTop ℕ∞) M] [T2Space M] {f : M → ℝ}
    (data : MorseChart (m + 1) k hk c I f)
    (hε : 0 < ε) (hr : r ≠ 0) (hεr : Real.sqrt (2 * ε + 2 * r ^ 2) ≤ data.R)
    (hδ : r ^ 2 / 2 < δ)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) f)
    (v : (x : M) → TangentSpace I x)
    (hv : ContMDiff I (I.prod 𝓘(ℝ, MorseModel (m + 1))) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : M => (⟨x, v x⟩ : TangentBundle I M)))
    (hdfOn : ∀ x ∈ f ⁻¹' Set.Icc (c - ε) (c + δ),
      (NormedSpace.fromTangentSpace (f x)) ((mfderiv I 𝓘(ℝ, ℝ) f x) (v x)) = -1)
    (hrate : ∀ x, -1 ≤ (NormedSpace.fromTangentSpace (f x)) ((mfderiv I 𝓘(ℝ, ℝ) f x) (v x)) ∧
      (NormedSpace.fromTangentSpace (f x)) ((mfderiv I 𝓘(ℝ, ℝ) f x) (v x)) ≤ 0)
    (hcomplete : ∀ x : M, ∃ γ : ℝ → M, γ 0 = x ∧ IsMIntegralCurve γ v) :
    Function.Injective (handleCollarMap hk c ε r data hε hεr v hcomplete) := by
  intro q q' h
  let s : ℝ := r ^ 2 * (1 - (q.2 : ℝ)) / 2
  let s' : ℝ := r ^ 2 * (1 - (q'.2 : ℝ)) / 2
  let x : M := (cocoreAttachingEmbedding hk c ε r data hε hεr q.1).1
  let x' : M := (cocoreAttachingEmbedding hk c ε r data hε hεr q'.1).1
  have hs0 : 0 ≤ s := by
    dsimp [s]
    have h1 : 0 ≤ 1 - (q.2 : ℝ) := sub_nonneg.mpr q.2.property.2
    exact div_nonneg (mul_nonneg (sq_nonneg r) h1) (by norm_num)
  have hs0' : 0 ≤ s' := by
    dsimp [s']
    have h1 : 0 ≤ 1 - (q'.2 : ℝ) := sub_nonneg.mpr q'.2.property.2
    exact div_nonneg (mul_nonneg (sq_nonneg r) h1) (by norm_num)
  have hfz : f (curveAt v hcomplete x (-s)) = c - ε + s := by
    have hval := handleCollarMap_value hk c ε r δ data hε hεr hδ hf v hdfOn hrate hcomplete q
    change f (curveAt v hcomplete (cocoreAttachingEmbedding hk c ε r data hε hεr q.1).1
        (-(r ^ 2 * (1 - (q.2 : ℝ)) / 2))) = c - ε + r ^ 2 * (1 - (q.2 : ℝ)) / 2 at hval
    dsimp [x, s] at hval ⊢
    exact hval
  have hfz' : f (curveAt v hcomplete x' (-s')) = c - ε + s' := by
    have hval := handleCollarMap_value hk c ε r δ data hε hεr hδ hf v hdfOn hrate hcomplete q'
    change f (curveAt v hcomplete (cocoreAttachingEmbedding hk c ε r data hε hεr q'.1).1
        (-(r ^ 2 * (1 - (q'.2 : ℝ)) / 2))) = c - ε + r ^ 2 * (1 - (q'.2 : ℝ)) / 2 at hval
    dsimp [x', s'] at hval ⊢
    exact hval
  have hcong := congrArg f h
  have hcong' : f (curveAt v hcomplete x (-s)) = f (curveAt v hcomplete x' (-s')) := by
    change f (handleCollarMap hk c ε r data hε hεr v hcomplete q) =
      f (handleCollarMap hk c ε r data hε hεr v hcomplete q') at hcong
    exact hcong
  have hq : (q.2 : ℝ) = (q'.2 : ℝ) := by
    rw [hfz, hfz'] at hcong'
    have hcancel : r ^ 2 / 2 ≠ 0 := div_ne_zero (pow_ne_zero 2 hr) (by norm_num)
    have hmul : (r ^ 2 / 2) * (1 - (q.2 : ℝ)) = (r ^ 2 / 2) * (1 - (q'.2 : ℝ)) := by
      dsimp [s, s'] at hcong'
      nlinarith
    have hsub : 1 - (q.2 : ℝ) = 1 - (q'.2 : ℝ) := mul_left_cancel₀ hcancel hmul
    linarith
  have hfs : s = s' := by
    dsimp [s, s']
    rw [hq]
  have hv1 : ContMDiff I (I.prod 𝓘(ℝ, MorseModel (m + 1))) (1 : WithTop ℕ∞)
      (fun x : M => (⟨x, v x⟩ : TangentBundle I M)) :=
    hv.of_le (show (1 : WithTop ℕ∞) ≤ (⊤ : ℕ∞) by
      exact_mod_cast (le_top : (1 : ℕ∞) ≤ (⊤ : ℕ∞)))
  have hback : curveAt v hcomplete (curveAt v hcomplete x (-s)) s = x := by
    have h1 := curveAt_add v hv1 hcomplete x (-s) s
    rw [show (-s) + s = 0 by ring, curveAt_zero v hcomplete x] at h1
    exact h1.symm
  have hback' : curveAt v hcomplete (curveAt v hcomplete x' (-s')) s' = x' := by
    have h1 := curveAt_add v hv1 hcomplete x' (-s') s'
    rw [show (-s') + s' = 0 by ring, curveAt_zero v hcomplete x'] at h1
    exact h1.symm
  have hx : x = x' := by
    have hc := congrArg (fun z : M => curveAt v hcomplete z s) h
    have hc' : curveAt v hcomplete (curveAt v hcomplete x (-s)) s =
        curveAt v hcomplete (curveAt v hcomplete x' (-s')) s := by
      change curveAt v hcomplete (handleCollarMap hk c ε r data hε hεr v hcomplete q) s =
        curveAt v hcomplete (handleCollarMap hk c ε r data hε hεr v hcomplete q') s at hc
      exact hc
    have hback'' : curveAt v hcomplete (curveAt v hcomplete x' (-s)) s = x' := by
      simpa [hfs.symm] using hback'
    rw [hback] at hc'
    rw [← hfs] at hc'
    rw [hback''] at hc'
    exact hc'
  apply Prod.ext
  · have hφ : (cocoreAttachingEmbedding hk c ε r data hε hεr q.1) =
        (cocoreAttachingEmbedding hk c ε r data hε hεr q'.1) := by
      apply Subtype.ext
      change x = x'
      exact hx
    exact cocoreAttachingEmbedding_injective hk c ε r data hε hr hεr hφ
  · apply Subtype.ext
    exact hq

theorem handleCollarMap_attachingRegion {m k : ℕ} (hk : k ≤ m + 1) (c ε r : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} [I.Boundaryless]
    [IsManifold I (⊤ : WithTop ℕ∞) M] [T2Space M] {f : M → ℝ}
    (data : MorseChart (m + 1) k hk c I f)
    (hε : 0 < ε) (hεr : Real.sqrt (2 * ε + 2 * r ^ 2) ≤ data.R)
    (v : (x : M) → TangentSpace I x)
    (hcomplete : ∀ x : M, ∃ γ : ℝ → M, γ 0 = x ∧ IsMIntegralCurve γ v)
    (p : AttachingRegion k (m + 1 - k)) :
    handleCollarMap hk c ε r data hε hεr v hcomplete (p, (⟨1, by norm_num⟩ : Set.Icc (0 : ℝ) 1)) =
      (cocoreAttachingEmbedding hk c ε r data hε hεr p).1 := by
  simp [handleCollarMap, curveAt_zero v hcomplete]

theorem handleCollarMap_mem_lower {m k : ℕ} (hk : k ≤ m + 1) (c ε r δ : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} [I.Boundaryless]
    [IsManifold I (⊤ : WithTop ℕ∞) M] [T2Space M] {f : M → ℝ}
    (data : MorseChart (m + 1) k hk c I f)
    (hε : 0 < ε) (hr : r ≠ 0) (hεr : Real.sqrt (2 * ε + 2 * r ^ 2) ≤ data.R)
    (hδ : r ^ 2 / 2 < δ)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) f)
    (v : (x : M) → TangentSpace I x)
    (hdfOn : ∀ x ∈ f ⁻¹' Set.Icc (c - ε) (c + δ),
      (NormedSpace.fromTangentSpace (f x)) ((mfderiv I 𝓘(ℝ, ℝ) f x) (v x)) = -1)
    (hrate : ∀ x, -1 ≤ (NormedSpace.fromTangentSpace (f x)) ((mfderiv I 𝓘(ℝ, ℝ) f x) (v x)) ∧
      (NormedSpace.fromTangentSpace (f x)) ((mfderiv I 𝓘(ℝ, ℝ) f x) (v x)) ≤ 0)
    (hcomplete : ∀ x : M, ∃ γ : ℝ → M, γ 0 = x ∧ IsMIntegralCurve γ v)
    (q : AttachingRegion k (m + 1 - k) × Set.Icc (0 : ℝ) 1)
    (hρ : (q.2 : ℝ) < 1) :
    handleCollarMap hk c ε r data hε hεr v hcomplete q ∉ sublevel f (c - ε) := by
  intro hq
  have hval := handleCollarMap_value hk c ε r δ data hε hεr hδ hf v hdfOn hrate hcomplete q
  change f (handleCollarMap hk c ε r data hε hεr v hcomplete q) ≤ c - ε at hq
  rw [hval] at hq
  have hpos : 0 < r ^ 2 * (1 - (q.2 : ℝ)) / 2 := by
    have hr2 : 0 < r ^ 2 := sq_pos_of_ne_zero hr
    have h1 : 0 < 1 - (q.2 : ℝ) := sub_pos.mpr hρ
    positivity
  nlinarith

theorem handleCollarMap_mem_sublevel {m k : ℕ} (hk : k ≤ m + 1) (c ε r δ : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} [I.Boundaryless]
    [IsManifold I (⊤ : WithTop ℕ∞) M] [T2Space M] {f : M → ℝ}
    (data : MorseChart (m + 1) k hk c I f)
    (hε : 0 < ε) (hεr : Real.sqrt (2 * ε + 2 * r ^ 2) ≤ data.R)
    (hδ : r ^ 2 / 2 < δ)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) f)
    (v : (x : M) → TangentSpace I x)
    (hdfOn : ∀ x ∈ f ⁻¹' Set.Icc (c - ε) (c + δ),
      (NormedSpace.fromTangentSpace (f x)) ((mfderiv I 𝓘(ℝ, ℝ) f x) (v x)) = -1)
    (hrate : ∀ x, -1 ≤ (NormedSpace.fromTangentSpace (f x)) ((mfderiv I 𝓘(ℝ, ℝ) f x) (v x)) ∧
      (NormedSpace.fromTangentSpace (f x)) ((mfderiv I 𝓘(ℝ, ℝ) f x) (v x)) ≤ 0)
    (hcomplete : ∀ x : M, ∃ γ : ℝ → M, γ 0 = x ∧ IsMIntegralCurve γ v)
    (b : ℝ) (hb : c - ε + r ^ 2 / 2 ≤ b)
    (q : AttachingRegion k (m + 1 - k) × Set.Icc (0 : ℝ) 1) :
    handleCollarMap hk c ε r data hε hεr v hcomplete q ∈ sublevel f b := by
  have hval := handleCollarMap_value hk c ε r δ data hε hεr hδ hf v hdfOn hrate hcomplete q
  change f (handleCollarMap hk c ε r data hε hεr v hcomplete q) ≤ b
  rw [hval]
  have hs : r ^ 2 * (1 - (q.2 : ℝ)) / 2 ≤ r ^ 2 / 2 := by
    have h1 : 0 ≤ 1 - (q.2 : ℝ) := sub_nonneg.mpr q.2.property.2
    have h1' : 0 ≤ (q.2 : ℝ) := q.2.property.1
    nlinarith [sq_nonneg r, h1, h1']
  nlinarith [hb, hs]

theorem handleCollarMap_mem_lower_iff {m k : ℕ} (hk : k ≤ m + 1) (c ε r δ : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} [I.Boundaryless]
    [IsManifold I (⊤ : WithTop ℕ∞) M] [T2Space M] {f : M → ℝ}
    (data : MorseChart (m + 1) k hk c I f)
    (hε : 0 < ε) (hr : r ≠ 0) (hεr : Real.sqrt (2 * ε + 2 * r ^ 2) ≤ data.R)
    (hδ : r ^ 2 / 2 < δ)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) f)
    (v : (x : M) → TangentSpace I x)
    (hdfOn : ∀ x ∈ f ⁻¹' Set.Icc (c - ε) (c + δ),
      (NormedSpace.fromTangentSpace (f x)) ((mfderiv I 𝓘(ℝ, ℝ) f x) (v x)) = -1)
    (hrate : ∀ x, -1 ≤ (NormedSpace.fromTangentSpace (f x)) ((mfderiv I 𝓘(ℝ, ℝ) f x) (v x)) ∧
      (NormedSpace.fromTangentSpace (f x)) ((mfderiv I 𝓘(ℝ, ℝ) f x) (v x)) ≤ 0)
    (hcomplete : ∀ x : M, ∃ γ : ℝ → M, γ 0 = x ∧ IsMIntegralCurve γ v)
    (q : AttachingRegion k (m + 1 - k) × Set.Icc (0 : ℝ) 1) :
    handleCollarMap hk c ε r data hε hεr v hcomplete q ∈ sublevel f (c - ε) ↔
      (q.2 : ℝ) = 1 := by
  constructor
  · intro hq
    have hval := handleCollarMap_value hk c ε r δ data hε hεr hδ hf v hdfOn hrate hcomplete q
    change f (handleCollarMap hk c ε r data hε hεr v hcomplete q) ≤ c - ε at hq
    rw [hval] at hq
    have hr2 : 0 < r ^ 2 := sq_pos_of_ne_zero hr
    have hle : 1 - (q.2 : ℝ) ≤ 0 := by
      have h0 : r ^ 2 * (1 - (q.2 : ℝ)) / 2 ≤ 0 := by nlinarith
      nlinarith
    have hge : 1 ≤ (q.2 : ℝ) := by nlinarith
    exact le_antisymm q.2.property.2 hge
  · intro hρ
    have hval := handleCollarMap_value hk c ε r δ data hε hεr hδ hf v hdfOn hrate hcomplete q
    change f (handleCollarMap hk c ε r data hε hεr v hcomplete q) ≤ c - ε
    rw [hval]
    rw [hρ]
    norm_num

theorem isClosedEmbedding_handleCollarMap {m k : ℕ} (hk : k ≤ m + 1) (c ε r δ : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} [I.Boundaryless]
    [IsManifold I (⊤ : WithTop ℕ∞) M] [T2Space M] {f : M → ℝ}
    (data : MorseChart (m + 1) k hk c I f)
    (hε : 0 < ε) (hr : r ≠ 0) (hεr : Real.sqrt (2 * ε + 2 * r ^ 2) ≤ data.R)
    (hRltR' : data.R < data.R') (hδ : r ^ 2 / 2 < δ)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) f)
    (hreg : ∀ x : M, f x = c - ε → ¬ IsCriticalPointAt I f x)
    (v : (x : M) → TangentSpace I x)
    (hv : ContMDiff I (I.prod 𝓘(ℝ, MorseModel (m + 1))) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : M => (⟨x, v x⟩ : TangentBundle I M)))
    (hsupp : IsCompact (tsupport v))
    (hdfOn : ∀ x ∈ f ⁻¹' Set.Icc (c - ε) (c + δ),
      (NormedSpace.fromTangentSpace (f x)) ((mfderiv I 𝓘(ℝ, ℝ) f x) (v x)) = -1)
    (hrate : ∀ x, -1 ≤ (NormedSpace.fromTangentSpace (f x)) ((mfderiv I 𝓘(ℝ, ℝ) f x) (v x)) ∧
      (NormedSpace.fromTangentSpace (f x)) ((mfderiv I 𝓘(ℝ, ℝ) f x) (v x)) ≤ 0)
    (hcomplete : ∀ x : M, ∃ γ : ℝ → M, γ 0 = x ∧ IsMIntegralCurve γ v)
    [NeZero k] [NeZero (m + 1 - k)] :
    Topology.IsClosedEmbedding (handleCollarMap hk c ε r data hε hεr v hcomplete) := by
  exact (contMDiff_handleCollarMap hk c ε r data hε hεr hRltR' hf hreg v hv hsupp hcomplete).continuous.isClosedEmbedding
    (handleCollarMap_injective hk c ε r δ data hε hr hεr hδ hf v hv hdfOn hrate hcomplete)

theorem standardHandleContMDiff_of {n k : ℕ}
    (F : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin (n - k)) → MorseModel n)
    (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    [NeZero k] [NeZero (n - k)] :
    @ContMDiff ℝ _
      (EuclideanSpace ℝ (Fin ((k - 1) + 1)) × EuclideanSpace ℝ (Fin (((n - k - 1) + 1)))) _ _
      (ModelProd (EuclideanHalfSpace ((k - 1) + 1)) (EuclideanHalfSpace ((n - k - 1) + 1))) _
      ((modelWithCornersEuclideanHalfSpace ((k - 1) + 1)).prod
        (modelWithCornersEuclideanHalfSpace ((n - k - 1) + 1)))
      (StandardHandle k (n - k)) _ (standardHandleChartedSpace k (n - k))
      (MorseModel n) _ _ (MorseModel n) _
      (𝓘(ℝ, MorseModel n)) (MorseModel n) _ _
      (⊤ : ℕ∞)
      (fun p : StandardHandle k (n - k) =>
        F ((p.1 : EuclideanSpace ℝ (Fin k)), (p.2 : EuclideanSpace ℝ (Fin (n - k))))) := by
  classical
  letI : ChartedSpace (EuclideanHalfSpace ((k - 1) + 1)) (ClosedCell k) :=
    closedCellChartedSpace k
  letI : ChartedSpace (EuclideanHalfSpace ((n - k - 1) + 1)) (ClosedCell (n - k)) :=
    closedCellChartedSpace (n - k)
  have h1 : ContMDiff (modelWithCornersEuclideanHalfSpace ((k - 1) + 1))
      (𝓘(ℝ, EuclideanSpace ℝ (Fin k))) (⊤ : ℕ∞)
      (fun u : ClosedCell k => (u : EuclideanSpace ℝ (Fin k))) :=
    closedCellInclusion_contMDiff_of k
  have h2 : ContMDiff (modelWithCornersEuclideanHalfSpace ((n - k - 1) + 1))
      (𝓘(ℝ, EuclideanSpace ℝ (Fin (n - k)))) (⊤ : ℕ∞)
      (fun v : ClosedCell (n - k) => (v : EuclideanSpace ℝ (Fin (n - k)))) :=
    closedCellInclusion_contMDiff_of (n - k)
  have hprod : ContMDiff ((modelWithCornersEuclideanHalfSpace ((k - 1) + 1)).prod
        (modelWithCornersEuclideanHalfSpace ((n - k - 1) + 1)))
      ((𝓘(ℝ, EuclideanSpace ℝ (Fin k))).prod (𝓘(ℝ, EuclideanSpace ℝ (Fin (n - k))))) (⊤ : ℕ∞)
      (fun p : StandardHandle k (n - k) =>
        ((p.1 : EuclideanSpace ℝ (Fin k)), (p.2 : EuclideanSpace ℝ (Fin (n - k))))) := by
    exact ContMDiff.prodMap h1 h2
  have hF' : ContMDiff ((𝓘(ℝ, EuclideanSpace ℝ (Fin k))).prod
        (𝓘(ℝ, EuclideanSpace ℝ (Fin (n - k)))))
      (𝓘(ℝ, MorseModel n)) (⊤ : ℕ∞)
      (fun q : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin (n - k)) => F q) := by
    rw [contMDiff_iff]
    constructor
    · exact hF.continuous
    · intro x y
      apply hF.contDiffOn.congr
      intro q hq
      simp [extChartAt, Function.comp_def, OpenPartialHomeomorph.refl_prod_refl]
      rfl
  have hfun : (fun p : StandardHandle k (n - k) =>
        F ((p.1 : EuclideanSpace ℝ (Fin k)), (p.2 : EuclideanSpace ℝ (Fin (n - k))))) =
      (fun q : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin (n - k)) => F q) ∘
        (fun p : StandardHandle k (n - k) =>
          ((p.1 : EuclideanSpace ℝ (Fin k)), (p.2 : EuclideanSpace ℝ (Fin (n - k))))) := by
    funext p
    rfl
  rw [hfun]
  exact hF'.comp hprod

theorem standardHandleZeroContMDiff_of {n : ℕ}
    (F : EuclideanSpace ℝ (Fin 0) × EuclideanSpace ℝ (Fin n) → MorseModel n)
    (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    [NeZero n] :
    @ContMDiff ℝ _
      (EuclideanSpace ℝ (Fin 0) × EuclideanSpace ℝ (Fin ((n - 1) + 1))) _ _
      (ModelProd (EuclideanSpace ℝ (Fin 0)) (EuclideanHalfSpace ((n - 1) + 1))) _
      ((𝓘(ℝ, EuclideanSpace ℝ (Fin 0))).prod (modelWithCornersEuclideanHalfSpace ((n - 1) + 1)))
      (StandardHandle 0 n) _ (standardHandleZeroChartedSpace n)
      (MorseModel n) _ _ (MorseModel n) _
      (𝓘(ℝ, MorseModel n)) (MorseModel n) _ _
      (⊤ : ℕ∞)
      (fun p : StandardHandle 0 n =>
        F ((p.1 : EuclideanSpace ℝ (Fin 0)), (p.2 : EuclideanSpace ℝ (Fin n)))) := by
  classical
  letI : ChartedSpace (EuclideanSpace ℝ (Fin 0)) (ClosedCell 0) :=
    closedCellZeroChartedSpace
  letI : ChartedSpace (EuclideanHalfSpace ((n - 1) + 1)) (ClosedCell n) :=
    closedCellChartedSpace n
  have h1 : ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin 0))) (𝓘(ℝ, EuclideanSpace ℝ (Fin 0)))
      (⊤ : ℕ∞)
      (fun u : ClosedCell 0 => (u : EuclideanSpace ℝ (Fin 0))) :=
    closedCellZeroInclusion_contMDiff
  have h2 : ContMDiff (modelWithCornersEuclideanHalfSpace ((n - 1) + 1))
      (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (⊤ : ℕ∞)
      (fun v : ClosedCell n => (v : EuclideanSpace ℝ (Fin n))) :=
    closedCellInclusion_contMDiff_of n
  have hprod : ContMDiff ((𝓘(ℝ, EuclideanSpace ℝ (Fin 0))).prod
        (modelWithCornersEuclideanHalfSpace ((n - 1) + 1)))
      ((𝓘(ℝ, EuclideanSpace ℝ (Fin 0))).prod (𝓘(ℝ, EuclideanSpace ℝ (Fin n)))) (⊤ : ℕ∞)
      (fun p : StandardHandle 0 n =>
        ((p.1 : EuclideanSpace ℝ (Fin 0)), (p.2 : EuclideanSpace ℝ (Fin n)))) := by
    exact ContMDiff.prodMap h1 h2
  have hF' : ContMDiff ((𝓘(ℝ, EuclideanSpace ℝ (Fin 0))).prod
        (𝓘(ℝ, EuclideanSpace ℝ (Fin n))))
      (𝓘(ℝ, MorseModel n)) (⊤ : ℕ∞)
      (fun q : EuclideanSpace ℝ (Fin 0) × EuclideanSpace ℝ (Fin n) => F q) := by
    rw [contMDiff_iff]
    constructor
    · exact hF.continuous
    · intro x y
      apply hF.contDiffOn.congr
      intro q hq
      simp [extChartAt, Function.comp_def, OpenPartialHomeomorph.refl_prod_refl]
      rfl
  have hfun : (fun p : StandardHandle 0 n =>
        F ((p.1 : EuclideanSpace ℝ (Fin 0)), (p.2 : EuclideanSpace ℝ (Fin n)))) =
      (fun q : EuclideanSpace ℝ (Fin 0) × EuclideanSpace ℝ (Fin n) => F q) ∘
        (fun p : StandardHandle 0 n =>
          ((p.1 : EuclideanSpace ℝ (Fin 0)), (p.2 : EuclideanSpace ℝ (Fin n)))) := by
    funext p
    rfl
  rw [hfun]
  exact hF'.comp hprod

theorem modelHandleMap_contDiff {n k : ℕ} (hk : k ≤ n) (r ε : ℝ) (hε : 0 < ε) :
    ContDiff ℝ (⊤ : ℕ∞)
      (fun p : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin (n - k)) =>
        recombine hk ((Real.sqrt (2 * ε + r ^ 2 * ‖p.2‖ ^ 2)) • p.1) (r • p.2)) := by
  have hrew : (fun p : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin (n - k)) =>
        recombine hk ((Real.sqrt (2 * ε + r ^ 2 * ‖p.2‖ ^ 2)) • p.1) (r • p.2)) =
      fun p : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin (n - k)) =>
        recombine hk (negPart hk (cellMap (Real.sqrt (2 * ε + r ^ 2 * ‖p.2‖ ^ 2)) p.1)) (r • p.2) := by
    funext p
    rw [negPart_cellMap_smul hk]
  rw [hrew]
  exact recombine_contDiff_cocore hk r ε hε

noncomputable def handleEmbedding {n k : ℕ} (hk : k ≤ n) (c ε r : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ (MorseModel n) H} {f : M → ℝ}
    (data : MorseChart n k hk c I f) :
    StandardHandle k (n - k) → M :=
  fun p => data.χ (modelHandleMap hk ε r p)

theorem handleEmbedding_f_value {n k : ℕ} (hk : k ≤ n) (c ε r : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ (MorseModel n) H} {f : M → ℝ}
    (data : MorseChart n k hk c I f)
    (hε : 0 ≤ ε) (hεr : Real.sqrt (2 * ε + 2 * r ^ 2) ≤ data.R)
    (p : StandardHandle k (n - k)) :
    f (handleEmbedding hk c ε r data p) = morseNormalForm hk c (modelHandleMap hk ε r p) := by
  change f (data.χ (modelHandleMap hk ε r p)) = morseNormalForm hk c (modelHandleMap hk ε r p)
  rw [data.hnorm (modelHandleMap hk ε r p) (le_trans (modelHandleMap_norm_le hk ε r hε p) hεr)]

theorem handleEmbedding_attachingRegion {n k : ℕ} (hk : k ≤ n) (c ε r : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ (MorseModel n) H} {f : M → ℝ}
    (data : MorseChart n k hk c I f)
    (hε : 0 < ε) (hεr : Real.sqrt (2 * ε + 2 * r ^ 2) ≤ data.R)
    (p : AttachingRegion k (n - k)) :
    handleEmbedding hk c ε r data (attachingInclusion k (n - k) p) =
      (cocoreAttachingEmbedding hk c ε r data hε hεr p).1 := by
  dsimp [handleEmbedding, cocoreAttachingEmbedding, attachingInclusion]
  change data.χ (modelHandleMap hk ε r (cellBoundaryInclusion k p.1, p.2)) =
    data.χ (cocoreModelPoint hk ε r p)
  rw [modelHandleMap_attachingRegion]
  rfl

theorem handleEmbedding_mem_lower_iff {n k : ℕ} (hk : k ≤ n) (c ε r : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ (MorseModel n) H} {f : M → ℝ}
    (data : MorseChart n k hk c I f)
    (hε : 0 < ε) (hεr : Real.sqrt (2 * ε + 2 * r ^ 2) ≤ data.R)
    (p : StandardHandle k (n - k)) :
    handleEmbedding hk c ε r data p ∈ sublevel f (c - ε) ↔
      ‖(p.1 : EuclideanSpace ℝ (Fin k))‖ = 1 := by
  change f (handleEmbedding hk c ε r data p) ≤ c - ε ↔
    ‖(p.1 : EuclideanSpace ℝ (Fin k))‖ = 1
  rw [handleEmbedding_f_value hk c ε r data (le_of_lt hε) hεr p]
  constructor
  · intro hle
    have heq : morseNormalForm hk c (modelHandleMap hk ε r p) = c - ε :=
      le_antisymm hle (modelHandleMap_f_ge hk c ε r (le_of_lt hε) p)
    exact (modelHandleMap_f_eq_lower_iff hk c ε r hε p).1 heq
  · intro hx
    have heq : morseNormalForm hk c (modelHandleMap hk ε r p) = c - ε :=
      (modelHandleMap_f_eq_lower_iff hk c ε r hε p).2 hx
    exact le_of_eq heq

theorem handleEmbedding_mem_sublevel {n k : ℕ} (hk : k ≤ n) (c ε r b : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ (MorseModel n) H} {f : M → ℝ}
    (data : MorseChart n k hk c I f)
    (hε : 0 ≤ ε) (hεr : Real.sqrt (2 * ε + 2 * r ^ 2) ≤ data.R)
    (hb : c + r ^ 2 / 2 ≤ b) (p : StandardHandle k (n - k)) :
    handleEmbedding hk c ε r data p ∈ sublevel f b := by
  change f (handleEmbedding hk c ε r data p) ≤ b
  rw [handleEmbedding_f_value hk c ε r data hε hεr p]
  exact le_trans (modelHandleMap_f_le hk c ε r hε p) hb

theorem handleEmbedding_injective {n k : ℕ} (hk : k ≤ n) (c ε r : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ (MorseModel n) H} {f : M → ℝ}
    (data : MorseChart n k hk c I f)
    (hε : 0 < ε) (hr : r ≠ 0) (hεr : Real.sqrt (2 * ε + 2 * r ^ 2) ≤ data.R) :
    Function.Injective (handleEmbedding hk c ε r data) := by
  intro p q h
  have hχ : data.χ (modelHandleMap hk ε r p) = data.χ (modelHandleMap hk ε r q) := by
    simpa [handleEmbedding] using h
  have hnormb : ∀ x : StandardHandle k (n - k),
      morseNorm n (modelHandleMap hk ε r x) ≤ data.R := by
    intro x
    exact le_trans (modelHandleMap_norm_le hk ε r (le_of_lt hε) x) hεr
  have hsrc_p : modelHandleMap hk ε r p ∈ data.χ.source :=
    data.hχsrc (modelHandleMap hk ε r p) (hnormb p)
  have hsrc_q : modelHandleMap hk ε r q ∈ data.χ.source :=
    data.hχsrc (modelHandleMap hk ε r q) (hnormb q)
  have hy : modelHandleMap hk ε r p = modelHandleMap hk ε r q :=
    data.χ.injOn hsrc_p hsrc_q hχ
  exact modelHandleMap_injective hk ε r hε hr hy

theorem contMDiff_handleEmbedding {m k : ℕ} (hk : k ≤ m + 1) (c ε r : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} [I.Boundaryless]
    [IsManifold I (⊤ : WithTop ℕ∞) M] [T2Space M] {f : M → ℝ}
    (data : MorseChart (m + 1) k hk c I f)
    (hε : 0 < ε) (hεr : Real.sqrt (2 * ε + 2 * r ^ 2) ≤ data.R)
    (hRltR' : data.R < data.R')
    [NeZero k] [NeZero (m + 1 - k)] :
    @ContMDiff ℝ _
      (EuclideanSpace ℝ (Fin ((k - 1) + 1)) × EuclideanSpace ℝ (Fin (((m + 1 - k - 1) + 1)))) _ _
      (ModelProd (EuclideanHalfSpace ((k - 1) + 1)) (EuclideanHalfSpace ((m + 1 - k - 1) + 1))) _
      ((modelWithCornersEuclideanHalfSpace ((k - 1) + 1)).prod
        (modelWithCornersEuclideanHalfSpace ((m + 1 - k - 1) + 1)))
      (StandardHandle k (m + 1 - k)) _ (standardHandleChartedSpace k (m + 1 - k))
      (MorseModel (m + 1)) _ _ H _ I M _ _
      (⊤ : ℕ∞)
      (handleEmbedding hk c ε r data) := by
  classical
  letI : ChartedSpace (EuclideanHalfSpace ((k - 1) + 1)) (ClosedCell k) :=
    closedCellChartedSpace k
  letI : ChartedSpace (EuclideanHalfSpace ((m + 1 - k - 1) + 1)) (ClosedCell (m + 1 - k)) :=
    closedCellChartedSpace (m + 1 - k)
  have hrecomb : ContMDiff ((modelWithCornersEuclideanHalfSpace ((k - 1) + 1)).prod
        (modelWithCornersEuclideanHalfSpace ((m + 1 - k - 1) + 1)))
      (𝓘(ℝ, MorseModel (m + 1))) (⊤ : ℕ∞)
      (fun p : StandardHandle k (m + 1 - k) => modelHandleMap hk ε r p) := by
    exact standardHandleContMDiff_of
      (F := fun q : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin (m + 1 - k)) =>
        recombine hk ((Real.sqrt (2 * ε + r ^ 2 * ‖q.2‖ ^ 2)) • q.1) (r • q.2))
      (modelHandleMap_contDiff hk r ε hε)
  have hrecombOn : ContMDiffOn ((modelWithCornersEuclideanHalfSpace ((k - 1) + 1)).prod
        (modelWithCornersEuclideanHalfSpace ((m + 1 - k - 1) + 1)))
      (𝓘(ℝ, MorseModel (m + 1))) (⊤ : ℕ∞)
      (fun p : StandardHandle k (m + 1 - k) => modelHandleMap hk ε r p) Set.univ := by
    rw [contMDiffOn_univ]
    exact hrecomb
  have hball : ∀ p : StandardHandle k (m + 1 - k),
      modelHandleMap hk ε r p ∈ Metric.ball (0 : MorseModel (m + 1)) data.R' := by
    intro p
    have hnormb : morseNorm (m + 1) (modelHandleMap hk ε r p) ≤ data.R := by
      exact le_trans (modelHandleMap_norm_le hk ε r (le_of_lt hε) p) hεr
    have hlt : ‖modelHandleMap hk ε r p‖ < data.R' :=
      lt_of_le_of_lt (morseNorm_piNorm_le (modelHandleMap hk ε r p)) (lt_of_le_of_lt hnormb hRltR')
    simpa [Metric.mem_ball, dist_eq_norm] using hlt
  have hχ : ContMDiffOn ((modelWithCornersEuclideanHalfSpace ((k - 1) + 1)).prod
        (modelWithCornersEuclideanHalfSpace ((m + 1 - k - 1) + 1)))
      I (⊤ : ℕ∞)
      (fun p : StandardHandle k (m + 1 - k) => data.χ (modelHandleMap hk ε r p)) Set.univ := by
    refine data.hχon.comp hrecombOn ?_
    intro p hp
    exact hball p
  have hχ' : ContMDiff ((modelWithCornersEuclideanHalfSpace ((k - 1) + 1)).prod
        (modelWithCornersEuclideanHalfSpace ((m + 1 - k - 1) + 1)))
      I (⊤ : ℕ∞)
      (fun p : StandardHandle k (m + 1 - k) => data.χ (modelHandleMap hk ε r p)) := by
    rw [← contMDiffOn_univ]
    exact hχ
  exact hχ'.congr (by intro p; rfl)

theorem contMDiff_zeroHandleEmbedding {m : ℕ} (c ε r : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} [I.Boundaryless]
    [IsManifold I (⊤ : WithTop ℕ∞) M] [T2Space M] {f : M → ℝ}
    (data : MorseChart (m + 1) 0 (zero_le (m + 1)) c I f)
    (hε : 0 < ε) (hεr : Real.sqrt (2 * ε + 2 * r ^ 2) ≤ data.R)
    (hRltR' : data.R < data.R')
    [NeZero (m + 1)] :
    @ContMDiff ℝ _
      (EuclideanSpace ℝ (Fin 0) × EuclideanSpace ℝ (Fin (((m + 1 - 1) + 1)))) _ _
      (ModelProd (EuclideanSpace ℝ (Fin 0)) (EuclideanHalfSpace ((m + 1 - 1) + 1))) _
      ((𝓘(ℝ, EuclideanSpace ℝ (Fin 0))).prod (modelWithCornersEuclideanHalfSpace ((m + 1 - 1) + 1)))
      (StandardHandle 0 (m + 1)) _ (standardHandleZeroChartedSpace (m + 1))
      (MorseModel (m + 1)) _ _ H _ I M _ _
      (⊤ : ℕ∞)
      (handleEmbedding (zero_le (m + 1)) c ε r data) := by
  classical
  letI : ChartedSpace (EuclideanSpace ℝ (Fin 0)) (ClosedCell 0) :=
    closedCellZeroChartedSpace
  letI : ChartedSpace (EuclideanHalfSpace ((m + 1 - 1) + 1)) (ClosedCell (m + 1)) :=
    closedCellChartedSpace (m + 1)
  have hrecomb : ContMDiff ((𝓘(ℝ, EuclideanSpace ℝ (Fin 0))).prod
        (modelWithCornersEuclideanHalfSpace ((m + 1 - 1) + 1)))
      (𝓘(ℝ, MorseModel (m + 1))) (⊤ : ℕ∞)
      (fun p : StandardHandle 0 (m + 1) => modelHandleMap (zero_le (m + 1)) ε r p) := by
    exact standardHandleZeroContMDiff_of
      (F := fun q : EuclideanSpace ℝ (Fin 0) × EuclideanSpace ℝ (Fin (m + 1)) =>
        recombine (zero_le (m + 1)) ((Real.sqrt (2 * ε + r ^ 2 * ‖q.2‖ ^ 2)) • q.1) (r • q.2))
      (modelHandleMap_contDiff (zero_le (m + 1)) r ε hε)
  have hrecombOn : ContMDiffOn ((𝓘(ℝ, EuclideanSpace ℝ (Fin 0))).prod
        (modelWithCornersEuclideanHalfSpace ((m + 1 - 1) + 1)))
      (𝓘(ℝ, MorseModel (m + 1))) (⊤ : ℕ∞)
      (fun p : StandardHandle 0 (m + 1) => modelHandleMap (zero_le (m + 1)) ε r p) Set.univ := by
    rw [contMDiffOn_univ]
    exact hrecomb
  have hball : ∀ p : StandardHandle 0 (m + 1),
      modelHandleMap (zero_le (m + 1)) ε r p ∈ Metric.ball (0 : MorseModel (m + 1)) data.R' := by
    intro p
    have hnormb : morseNorm (m + 1) (modelHandleMap (zero_le (m + 1)) ε r p) ≤ data.R := by
      exact le_trans (modelHandleMap_norm_le (zero_le (m + 1)) ε r (le_of_lt hε) p) hεr
    have hlt : ‖modelHandleMap (zero_le (m + 1)) ε r p‖ < data.R' :=
      lt_of_le_of_lt (morseNorm_piNorm_le (modelHandleMap (zero_le (m + 1)) ε r p))
        (lt_of_le_of_lt hnormb hRltR')
    simpa [Metric.mem_ball, dist_eq_norm] using hlt
  have hχ : ContMDiffOn ((𝓘(ℝ, EuclideanSpace ℝ (Fin 0))).prod
        (modelWithCornersEuclideanHalfSpace ((m + 1 - 1) + 1)))
      I (⊤ : ℕ∞)
      (fun p : StandardHandle 0 (m + 1) => data.χ (modelHandleMap (zero_le (m + 1)) ε r p))
      Set.univ := by
    refine data.hχon.comp hrecombOn ?_
    intro p hp
    exact hball p
  have hχ' : ContMDiff ((𝓘(ℝ, EuclideanSpace ℝ (Fin 0))).prod
        (modelWithCornersEuclideanHalfSpace ((m + 1 - 1) + 1)))
      I (⊤ : ℕ∞)
      (fun p : StandardHandle 0 (m + 1) => data.χ (modelHandleMap (zero_le (m + 1)) ε r p)) := by
    rw [← contMDiffOn_univ]
    exact hχ
  exact hχ'.congr (by intro p; rfl)

theorem isClosedEmbedding_handleEmbedding {m k : ℕ} (hk : k ≤ m + 1) (c ε r : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} [I.Boundaryless]
    [IsManifold I (⊤ : WithTop ℕ∞) M] [T2Space M] {f : M → ℝ}
    (data : MorseChart (m + 1) k hk c I f)
    (hε : 0 < ε) (hr : r ≠ 0) (hεr : Real.sqrt (2 * ε + 2 * r ^ 2) ≤ data.R)
    (hRltR' : data.R < data.R')
    [NeZero k] [NeZero (m + 1 - k)] :
    Topology.IsClosedEmbedding (handleEmbedding hk c ε r data) := by
  letI : ChartedSpace (ModelProd (EuclideanHalfSpace ((k - 1) + 1))
      (EuclideanHalfSpace ((m + 1 - k - 1) + 1))) (StandardHandle k (m + 1 - k)) :=
    standardHandleChartedSpace k (m + 1 - k)
  exact (contMDiff_handleEmbedding hk c ε r data hε hεr hRltR').continuous.isClosedEmbedding
    (handleEmbedding_injective hk c ε r data hε hr hεr)

theorem isClosedEmbedding_zeroHandleEmbedding {m : ℕ} (c ε r : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} [I.Boundaryless]
    [IsManifold I (⊤ : WithTop ℕ∞) M] [T2Space M] {f : M → ℝ}
    (data : MorseChart (m + 1) 0 (zero_le (m + 1)) c I f)
    (hε : 0 < ε) (hr : r ≠ 0) (hεr : Real.sqrt (2 * ε + 2 * r ^ 2) ≤ data.R)
    (hRltR' : data.R < data.R')
    [NeZero (m + 1)] :
    Topology.IsClosedEmbedding (handleEmbedding (zero_le (m + 1)) c ε r data) := by
  letI : ChartedSpace (ModelProd (EuclideanSpace ℝ (Fin 0))
      (EuclideanHalfSpace ((m + 1 - 1) + 1))) (StandardHandle 0 (m + 1)) :=
    standardHandleZeroChartedSpace (m + 1)
  exact (contMDiff_zeroHandleEmbedding c ε r data hε hεr hRltR').continuous.isClosedEmbedding
    (handleEmbedding_injective (zero_le (m + 1)) c ε r data hε hr hεr)

theorem closedCellContMDiff_of {n : ℕ}
    (F : EuclideanSpace ℝ (Fin n) → MorseModel n)
    (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    [NeZero n] :
    @ContMDiff ℝ _
      (EuclideanSpace ℝ (Fin ((n - 1) + 1))) _ _
      (EuclideanHalfSpace ((n - 1) + 1)) _ (modelWithCornersEuclideanHalfSpace ((n - 1) + 1))
      (ClosedCell n) _ (closedCellChartedSpace n)
      (MorseModel n) _ _ (MorseModel n) _
      (𝓘(ℝ, MorseModel n)) (MorseModel n) _ _
      (⊤ : ℕ∞)
      (fun x : ClosedCell n => F (x : EuclideanSpace ℝ (Fin n))) := by
  classical
  letI : ChartedSpace (EuclideanHalfSpace ((n - 1) + 1)) (ClosedCell n) :=
    closedCellChartedSpace n
  have h1 : ContMDiff (modelWithCornersEuclideanHalfSpace ((n - 1) + 1))
      (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (⊤ : ℕ∞)
      (fun u : ClosedCell n => (u : EuclideanSpace ℝ (Fin n))) :=
    closedCellInclusion_contMDiff_of n
  have hF' : ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (𝓘(ℝ, MorseModel n)) (⊤ : ℕ∞)
      (fun q : EuclideanSpace ℝ (Fin n) => F q) := by
    rw [contMDiff_iff]
    constructor
    · exact hF.continuous
    · intro x y
      apply hF.contDiffOn.congr
      intro q hq
      simp [extChartAt]
  have hfun : (fun x : ClosedCell n => F (x : EuclideanSpace ℝ (Fin n))) =
      (fun q : EuclideanSpace ℝ (Fin n) => F q) ∘
        (fun x : ClosedCell n => (x : EuclideanSpace ℝ (Fin n))) := by
    funext x
    rfl
  rw [hfun]
  exact hF'.comp h1

noncomputable def topHandleEmbedding {m : ℕ} (c ε : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} {f : M → ℝ}
    (data : MorseChart (m + 1) (m + 1) (le_rfl : m + 1 ≤ m + 1) c I f) :
    ClosedCell (m + 1) → M :=
  fun x => data.χ ((Real.sqrt (2 * ε)) • (x : EuclideanSpace ℝ (Fin (m + 1))))

theorem morseNorm_top_smul {m : ℕ} (ε : ℝ) (x : ClosedCell (m + 1)) :
    morseNorm (m + 1) ((Real.sqrt (2 * ε)) • (x : EuclideanSpace ℝ (Fin (m + 1)))) ≤
      Real.sqrt (2 * ε) := by
  have hx : ‖(x : EuclideanSpace ℝ (Fin (m + 1)))‖ ≤ 1 := x.2
  have hnorm : morseNorm (m + 1) ((Real.sqrt (2 * ε)) • (x : EuclideanSpace ℝ (Fin (m + 1)))) =
      ‖(Real.sqrt (2 * ε)) • (x : EuclideanSpace ℝ (Fin (m + 1)))‖ := by
    simp [morseNorm]
  rw [hnorm]
  rw [norm_smul]
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  simpa using (mul_le_mul_of_nonneg_left hx (Real.sqrt_nonneg (2 * ε)))

theorem topHandleEmbedding_f_value {m : ℕ} (c ε : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} {f : M → ℝ}
    (data : MorseChart (m + 1) (m + 1) (le_rfl : m + 1 ≤ m + 1) c I f)
    (hε : 0 ≤ ε) (hεr : Real.sqrt (2 * ε) ≤ data.R)
    (x : ClosedCell (m + 1)) :
    f (topHandleEmbedding c ε data x) =
      c - ε * ‖(x : EuclideanSpace ℝ (Fin (m + 1)))‖ ^ 2 := by
  change f (data.χ ((Real.sqrt (2 * ε)) • (x : EuclideanSpace ℝ (Fin (m + 1))))) =
    c - ε * ‖(x : EuclideanSpace ℝ (Fin (m + 1)))‖ ^ 2
  rw [data.hnorm ((Real.sqrt (2 * ε)) • (x : EuclideanSpace ℝ (Fin (m + 1))))
    (le_trans (morseNorm_top_smul ε x) hεr)]
  · rw [morseNormalForm_split (le_rfl : m + 1 ≤ m + 1) c
      ((Real.sqrt (2 * ε)) • (x : EuclideanSpace ℝ (Fin (m + 1))))]
    have hpos : posPart (le_rfl : m + 1 ≤ m + 1)
        ((Real.sqrt (2 * ε)) • (x : EuclideanSpace ℝ (Fin (m + 1)))) =
        (0 : EuclideanSpace ℝ (Fin (m + 1 - (m + 1)))) :=
      posPart_top _
    have hnormNeg : ‖negPart (le_rfl : m + 1 ≤ m + 1)
        ((Real.sqrt (2 * ε)) • (x : EuclideanSpace ℝ (Fin (m + 1))))‖ ^ 2 =
        ‖(Real.sqrt (2 * ε)) • (x : EuclideanSpace ℝ (Fin (m + 1)))‖ ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq]
      rw [EuclideanSpace.real_norm_sq_eq ((Real.sqrt (2 * ε)) • (x : EuclideanSpace ℝ (Fin (m + 1))))]
      apply Finset.sum_congr rfl
      intro i hi
      rw [negPart_top]
      rfl
    have hnormSmul : ‖(Real.sqrt (2 * ε)) • (x : EuclideanSpace ℝ (Fin (m + 1)))‖ ^ 2 =
        2 * ε * ‖(x : EuclideanSpace ℝ (Fin (m + 1)))‖ ^ 2 := by
      rw [norm_smul]
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
      rw [mul_pow]
      rw [Real.sq_sqrt (by positivity : 0 ≤ 2 * ε)]
    rw [hpos, hnormNeg, hnormSmul]
    simp
    ring

theorem topHandleEmbedding_mem_lower_iff {m : ℕ} (c ε : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} {f : M → ℝ}
    (data : MorseChart (m + 1) (m + 1) (le_rfl : m + 1 ≤ m + 1) c I f)
    (hε : 0 < ε) (hεr : Real.sqrt (2 * ε) ≤ data.R)
    (x : ClosedCell (m + 1)) :
    topHandleEmbedding c ε data x ∈ sublevel f (c - ε) ↔
      ‖(x : EuclideanSpace ℝ (Fin (m + 1)))‖ = 1 := by
  change f (topHandleEmbedding c ε data x) ≤ c - ε ↔
    ‖(x : EuclideanSpace ℝ (Fin (m + 1)))‖ = 1
  rw [topHandleEmbedding_f_value c ε data (le_of_lt hε) hεr x]
  constructor
  · intro hle
    have hx : ‖(x : EuclideanSpace ℝ (Fin (m + 1)))‖ ≤ 1 := x.2
    have hsq : 1 ≤ ‖(x : EuclideanSpace ℝ (Fin (m + 1)))‖ ^ 2 := by
      nlinarith [hε, hle]
    have hsq' : ‖(x : EuclideanSpace ℝ (Fin (m + 1)))‖ ^ 2 ≤ 1 := by
      have hneg : -1 ≤ ‖(x : EuclideanSpace ℝ (Fin (m + 1)))‖ := by
        linarith [norm_nonneg (x : EuclideanSpace ℝ (Fin (m + 1)))]
      exact (sq_le_sq' hneg hx).trans_eq (by norm_num : (1 : ℝ) ^ 2 = 1)
    have hx2 : ‖(x : EuclideanSpace ℝ (Fin (m + 1)))‖ ^ 2 = 1 := le_antisymm hsq' hsq
    rcases sq_eq_one_iff.mp hx2 with h1 | h2
    · exact h1
    · linarith [norm_nonneg (x : EuclideanSpace ℝ (Fin (m + 1)))]
  · intro hx
    have hsq : ‖(x : EuclideanSpace ℝ (Fin (m + 1)))‖ ^ 2 = 1 := by
      rw [hx]
      norm_num
    rw [hsq]
    norm_num

theorem topHandleEmbedding_mem_sublevel {m : ℕ} (c ε b : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} {f : M → ℝ}
    (data : MorseChart (m + 1) (m + 1) (le_rfl : m + 1 ≤ m + 1) c I f)
    (hε : 0 ≤ ε) (hεr : Real.sqrt (2 * ε) ≤ data.R)
    (hb : c ≤ b) (x : ClosedCell (m + 1)) :
    topHandleEmbedding c ε data x ∈ sublevel f b := by
  change f (topHandleEmbedding c ε data x) ≤ b
  rw [topHandleEmbedding_f_value c ε data hε hεr x]
  have hx : 0 ≤ ‖(x : EuclideanSpace ℝ (Fin (m + 1)))‖ ^ 2 := sq_nonneg _
  nlinarith [hx, hε, hb]

theorem topHandleEmbedding_attachingRegion {m : ℕ} (c ε r : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} {f : M → ℝ}
    (data : MorseChart (m + 1) (m + 1) (le_rfl : m + 1 ≤ m + 1) c I f)
    (hε : 0 < ε) (hεr : Real.sqrt (2 * ε + 2 * r ^ 2) ≤ data.R)
    (u : CellBoundary (m + 1)) :
    topHandleEmbedding c ε data (cellBoundaryInclusion (m + 1) u) =
      (cocoreAttachingEmbedding (le_rfl : m + 1 ≤ m + 1) c ε r data hε hεr
        (u, ⟨0, by simp⟩)).1 := by
  dsimp [topHandleEmbedding, cocoreAttachingEmbedding]
  change data.χ ((Real.sqrt (2 * ε)) • (u : EuclideanSpace ℝ (Fin (m + 1)))) =
    data.χ (cocoreModelPoint (le_rfl : m + 1 ≤ m + 1) ε r
      (u, ⟨0, by simp⟩))
  dsimp [cocoreModelPoint]
  rw [negPart_cellMap_smul (le_rfl : m + 1 ≤ m + 1)]
  rw [recombine_top]
  congr 1
  rw [show 2 * ε + r ^ 2 * ‖(0 : EuclideanSpace ℝ (Fin (m + 1 - (m + 1))))‖ ^ 2 = 2 * ε by
    simp]
  simp

theorem topHandleEmbedding_injective {m : ℕ} (c ε : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} {f : M → ℝ}
    (data : MorseChart (m + 1) (m + 1) (le_rfl : m + 1 ≤ m + 1) c I f)
    (hε : 0 < ε) (hεr : Real.sqrt (2 * ε) ≤ data.R) :
    Function.Injective (topHandleEmbedding c ε data) := by
  intro x y h
  have hχ : data.χ ((Real.sqrt (2 * ε)) • (x : EuclideanSpace ℝ (Fin (m + 1)))) =
      data.χ ((Real.sqrt (2 * ε)) • (y : EuclideanSpace ℝ (Fin (m + 1)))) := by
    simpa [topHandleEmbedding] using h
  have hnormb : ∀ z : ClosedCell (m + 1),
      morseNorm (m + 1) ((Real.sqrt (2 * ε)) • (z : EuclideanSpace ℝ (Fin (m + 1)))) ≤ data.R := by
    intro z
    exact le_trans (morseNorm_top_smul ε z) hεr
  have hsrc_x : ((Real.sqrt (2 * ε)) • (x : EuclideanSpace ℝ (Fin (m + 1))) : MorseModel (m + 1)) ∈
      data.χ.source :=
    data.hχsrc _ (hnormb x)
  have hsrc_y : ((Real.sqrt (2 * ε)) • (y : EuclideanSpace ℝ (Fin (m + 1))) : MorseModel (m + 1)) ∈
      data.χ.source :=
    data.hχsrc _ (hnormb y)
  have hy : ((Real.sqrt (2 * ε)) • (x : EuclideanSpace ℝ (Fin (m + 1))) : MorseModel (m + 1)) =
      ((Real.sqrt (2 * ε)) • (y : EuclideanSpace ℝ (Fin (m + 1))) : MorseModel (m + 1)) :=
    data.χ.injOn hsrc_x hsrc_y hχ
  have hsqrt : Real.sqrt (2 * ε) ≠ 0 := by
    exact Real.sqrt_ne_zero'.mpr (by positivity)
  apply Subtype.ext
  have hf : ((x : EuclideanSpace ℝ (Fin (m + 1))).ofLp) =
      ((y : EuclideanSpace ℝ (Fin (m + 1))).ofLp) :=
    (smul_right_injective (Fin (m + 1) → ℝ) (r := Real.sqrt (2 * ε)) hsqrt) hy
  ext i
  exact congrFun hf i

theorem contMDiff_topHandleEmbedding {m : ℕ} (c ε : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} [I.Boundaryless]
    [IsManifold I (⊤ : WithTop ℕ∞) M] [T2Space M] {f : M → ℝ}
    (data : MorseChart (m + 1) (m + 1) (le_rfl : m + 1 ≤ m + 1) c I f)
    (hεr : Real.sqrt (2 * ε) ≤ data.R)
    (hRltR' : data.R < data.R')
    [NeZero (m + 1)] :
    @ContMDiff ℝ _
      (EuclideanSpace ℝ (Fin (((m + 1 - 1) + 1)))) _ _
      (EuclideanHalfSpace ((m + 1 - 1) + 1)) _ (modelWithCornersEuclideanHalfSpace ((m + 1 - 1) + 1))
      (ClosedCell (m + 1)) _ (closedCellChartedSpace (m + 1))
      (MorseModel (m + 1)) _ _ H _ I M _ _
      (⊤ : ℕ∞)
      (topHandleEmbedding c ε data) := by
  classical
  letI : ChartedSpace (EuclideanHalfSpace ((m + 1 - 1) + 1)) (ClosedCell (m + 1)) :=
    closedCellChartedSpace (m + 1)
  have hrecomb : ContMDiff (modelWithCornersEuclideanHalfSpace ((m + 1 - 1) + 1))
      (𝓘(ℝ, MorseModel (m + 1))) (⊤ : ℕ∞)
      (fun x : ClosedCell (m + 1) =>
        ((Real.sqrt (2 * ε)) • (x : EuclideanSpace ℝ (Fin (m + 1))) : MorseModel (m + 1))) := by
    exact closedCellContMDiff_of
      (F := fun q : EuclideanSpace ℝ (Fin (m + 1)) =>
        ((Real.sqrt (2 * ε)) • q : MorseModel (m + 1)))
      (by fun_prop)
  have hrecombOn : ContMDiffOn (modelWithCornersEuclideanHalfSpace ((m + 1 - 1) + 1))
      (𝓘(ℝ, MorseModel (m + 1))) (⊤ : ℕ∞)
      (fun x : ClosedCell (m + 1) =>
        ((Real.sqrt (2 * ε)) • (x : EuclideanSpace ℝ (Fin (m + 1))) : MorseModel (m + 1)))
      Set.univ := by
    rw [contMDiffOn_univ]
    exact hrecomb
  have hball : ∀ x : ClosedCell (m + 1),
      ((Real.sqrt (2 * ε)) • (x : EuclideanSpace ℝ (Fin (m + 1))) : MorseModel (m + 1)) ∈
      Metric.ball (0 : MorseModel (m + 1)) data.R' := by
    intro x
    have hnormb : morseNorm (m + 1)
        ((Real.sqrt (2 * ε)) • (x : EuclideanSpace ℝ (Fin (m + 1)))) ≤ data.R := by
      exact le_trans (morseNorm_top_smul ε x) hεr
    have hlt : ‖((Real.sqrt (2 * ε)) • (x : EuclideanSpace ℝ (Fin (m + 1))) : MorseModel (m + 1))‖ < data.R' :=
      lt_of_le_of_lt (morseNorm_piNorm_le
        ((Real.sqrt (2 * ε)) • (x : EuclideanSpace ℝ (Fin (m + 1)))))
        (lt_of_le_of_lt hnormb hRltR')
    simpa [Metric.mem_ball, dist_eq_norm] using hlt
  have hχ : ContMDiffOn (modelWithCornersEuclideanHalfSpace ((m + 1 - 1) + 1))
      I (⊤ : ℕ∞)
      (fun x : ClosedCell (m + 1) =>
        data.χ ((Real.sqrt (2 * ε)) • (x : EuclideanSpace ℝ (Fin (m + 1))))) Set.univ := by
    refine data.hχon.comp hrecombOn ?_
    intro x hx
    exact hball x
  have hχ' : ContMDiff (modelWithCornersEuclideanHalfSpace ((m + 1 - 1) + 1))
      I (⊤ : ℕ∞)
      (fun x : ClosedCell (m + 1) =>
        data.χ ((Real.sqrt (2 * ε)) • (x : EuclideanSpace ℝ (Fin (m + 1))))) := by
    rw [← contMDiffOn_univ]
    exact hχ
  exact hχ'.congr (by intro x; rfl)

theorem isClosedEmbedding_topHandleEmbedding {m : ℕ} (c ε : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} [I.Boundaryless]
    [IsManifold I (⊤ : WithTop ℕ∞) M] [T2Space M] {f : M → ℝ}
    (data : MorseChart (m + 1) (m + 1) (le_rfl : m + 1 ≤ m + 1) c I f)
    (hε : 0 < ε) (hεr : Real.sqrt (2 * ε) ≤ data.R)
    (hRltR' : data.R < data.R')
    [NeZero (m + 1)] :
    Topology.IsClosedEmbedding (topHandleEmbedding c ε data) := by
  letI : ChartedSpace (EuclideanHalfSpace ((m + 1 - 1) + 1)) (ClosedCell (m + 1)) :=
    closedCellChartedSpace (m + 1)
  exact (contMDiff_topHandleEmbedding c ε data hεr hRltR').continuous.isClosedEmbedding
    (topHandleEmbedding_injective c ε data hε hεr)

theorem morse_smooth_handle_attachment {m k : ℕ} (hk : k ≤ m + 1) (c ε r δ : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
    (I : ModelWithCorners ℝ (MorseModel (m + 1)) H) [I.Boundaryless]
    [IsManifold I (⊤ : WithTop ℕ∞) M] (f : M → ℝ)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) f)
    (data : MorseChart (m + 1) k hk c I f)
    (hε : 0 < ε) (hr : r ≠ 0) (hδ : r ^ 2 / 2 < δ)
    (hεr : Real.sqrt (2 * ε + 2 * r ^ 2) ≤ data.R)
    (hRltR' : data.R < data.R')
    (hreg : ∀ x : M, f x = c - ε → ¬ IsCriticalPointAt I f x)
    (v : (x : M) → TangentSpace I x)
    (hv : ContMDiff I (I.prod 𝓘(ℝ, MorseModel (m + 1))) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : M => (⟨x, v x⟩ : TangentBundle I M)))
    (hsupp : IsCompact (tsupport v))
    (hcomplete : ∀ x : M, ∃ γ : ℝ → M, γ 0 = x ∧ IsMIntegralCurve γ v)
    (hdfOn : ∀ x ∈ f ⁻¹' Set.Icc (c - ε) (c + δ),
      (NormedSpace.fromTangentSpace (f x)) ((mfderiv I 𝓘(ℝ, ℝ) f x) (v x)) = -1)
    (hrate : ∀ x, -1 ≤ (NormedSpace.fromTangentSpace (f x)) ((mfderiv I 𝓘(ℝ, ℝ) f x) (v x)) ∧
      (NormedSpace.fromTangentSpace (f x)) ((mfderiv I 𝓘(ℝ, ℝ) f x) (v x)) ≤ 0)
    [NeZero k] [NeZero (m + 1 - k)] :
    ∃ φ : StandardHandle k (m + 1 - k) → M,
      φ = handleEmbedding hk c ε r data ∧
      @ContMDiff ℝ _
        (EuclideanSpace ℝ (Fin ((k - 1) + 1)) × EuclideanSpace ℝ (Fin (((m + 1 - k - 1) + 1)))) _ _
        (ModelProd (EuclideanHalfSpace ((k - 1) + 1)) (EuclideanHalfSpace ((m + 1 - k - 1) + 1))) _
        ((modelWithCornersEuclideanHalfSpace ((k - 1) + 1)).prod
          (modelWithCornersEuclideanHalfSpace ((m + 1 - k - 1) + 1)))
        (StandardHandle k (m + 1 - k)) _ (standardHandleChartedSpace k (m + 1 - k))
        (MorseModel (m + 1)) _ _ H _ I M _ _
        (⊤ : ℕ∞)
        φ ∧
      Topology.IsClosedEmbedding φ ∧
      (∀ p : StandardHandle k (m + 1 - k),
        f (φ p) = morseNormalForm hk c (modelHandleMap hk ε r p)) ∧
      (∀ p : AttachingRegion k (m + 1 - k),
        φ (attachingInclusion k (m + 1 - k) p) =
          (cocoreAttachingEmbedding hk c ε r data hε hεr p).1) ∧
      (∀ p : StandardHandle k (m + 1 - k), φ p ∈ sublevel f (c + r ^ 2 / 2)) ∧
      (∀ p : StandardHandle k (m + 1 - k),
        φ p ∈ sublevel f (c - ε) ↔ ‖(p.1 : EuclideanSpace ℝ (Fin k))‖ = 1) ∧
      Topology.IsClosedEmbedding (handleCollarMap hk c ε r data hε hεr v hcomplete) ∧
      (∀ q : AttachingRegion k (m + 1 - k) × Set.Icc (0 : ℝ) 1,
        f (handleCollarMap hk c ε r data hε hεr v hcomplete q) =
          c - ε + r ^ 2 * (1 - (q.2 : ℝ)) / 2) ∧
      (∀ q : AttachingRegion k (m + 1 - k) × Set.Icc (0 : ℝ) 1,
        handleCollarMap hk c ε r data hε hεr v hcomplete q ∈ sublevel f (c - ε) ↔
          (q.2 : ℝ) = 1) := by
  refine ⟨handleEmbedding hk c ε r data, rfl, ?_, ?_⟩
  · exact contMDiff_handleEmbedding hk c ε r data hε hεr hRltR'
  constructor
  · exact isClosedEmbedding_handleEmbedding hk c ε r data hε hr hεr hRltR'
  constructor
  · intro p
    exact handleEmbedding_f_value hk c ε r data (le_of_lt hε) hεr p
  constructor
  · intro p
    exact handleEmbedding_attachingRegion hk c ε r data hε hεr p
  constructor
  · intro p
    exact handleEmbedding_mem_sublevel hk c ε r (c + r ^ 2 / 2) data (le_of_lt hε) hεr
      (le_rfl : c + r ^ 2 / 2 ≤ c + r ^ 2 / 2) p
  constructor
  · intro p
    exact handleEmbedding_mem_lower_iff hk c ε r data hε hεr p
  constructor
  · exact isClosedEmbedding_handleCollarMap hk c ε r δ data hε hr hεr hRltR' hδ hf hreg
      v hv hsupp hdfOn hrate hcomplete
  constructor
  · intro q
    exact handleCollarMap_value hk c ε r δ data hε hεr hδ hf v hdfOn hrate hcomplete q
  · intro q
    exact handleCollarMap_mem_lower_iff hk c ε r δ data hε hr hεr hδ hf v hdfOn hrate hcomplete q

theorem morse_smooth_handle_attachment_zero {m : ℕ} (c ε r : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
    (I : ModelWithCorners ℝ (MorseModel (m + 1)) H) [I.Boundaryless]
    [IsManifold I (⊤ : WithTop ℕ∞) M] (f : M → ℝ)
    (data : MorseChart (m + 1) 0 (zero_le (m + 1)) c I f)
    (hε : 0 < ε) (hr : r ≠ 0)
    (hεr : Real.sqrt (2 * ε + 2 * r ^ 2) ≤ data.R)
    (hRltR' : data.R < data.R')
    [NeZero (m + 1)] :
    ∃ φ : StandardHandle 0 (m + 1) → M,
      φ = handleEmbedding (zero_le (m + 1)) c ε r data ∧
      @ContMDiff ℝ _
        (EuclideanSpace ℝ (Fin 0) × EuclideanSpace ℝ (Fin (((m + 1 - 1) + 1)))) _ _
        (ModelProd (EuclideanSpace ℝ (Fin 0)) (EuclideanHalfSpace ((m + 1 - 1) + 1))) _
        ((𝓘(ℝ, EuclideanSpace ℝ (Fin 0))).prod (modelWithCornersEuclideanHalfSpace ((m + 1 - 1) + 1)))
        (StandardHandle 0 (m + 1)) _ (standardHandleZeroChartedSpace (m + 1))
        (MorseModel (m + 1)) _ _ H _ I M _ _
        (⊤ : ℕ∞)
        φ ∧
      Topology.IsClosedEmbedding φ ∧
      (∀ p : StandardHandle 0 (m + 1),
        f (φ p) = morseNormalForm (zero_le (m + 1)) c (modelHandleMap (zero_le (m + 1)) ε r p)) ∧
      (∀ p : AttachingRegion 0 (m + 1),
        φ (attachingInclusion 0 (m + 1) p) =
          (cocoreAttachingEmbedding (zero_le (m + 1)) c ε r data hε hεr p).1) ∧
      (∀ p : StandardHandle 0 (m + 1), φ p ∈ sublevel f (c + r ^ 2 / 2)) ∧
      (∀ p : StandardHandle 0 (m + 1),
        φ p ∈ sublevel f (c - ε) ↔ ‖(p.1 : EuclideanSpace ℝ (Fin 0))‖ = 1) := by
  refine ⟨handleEmbedding (zero_le (m + 1)) c ε r data, rfl, ?_, ?_⟩
  · exact contMDiff_zeroHandleEmbedding c ε r data hε hεr hRltR'
  constructor
  · exact isClosedEmbedding_zeroHandleEmbedding c ε r data hε hr hεr hRltR'
  constructor
  · intro p
    exact handleEmbedding_f_value (zero_le (m + 1)) c ε r data (le_of_lt hε) hεr p
  constructor
  · intro p
    rcases p with ⟨u, w⟩
    have hu : (u : EuclideanSpace ℝ (Fin 0)) = 0 := Subsingleton.elim _ _
    have hn : ‖(u : EuclideanSpace ℝ (Fin 0))‖ = 1 := u.2
    rw [hu] at hn
    norm_num at hn
  constructor
  · intro p
    exact handleEmbedding_mem_sublevel (zero_le (m + 1)) c ε r (c + r ^ 2 / 2) data (le_of_lt hε) hεr
      (le_rfl : c + r ^ 2 / 2 ≤ c + r ^ 2 / 2) p
  · intro p
    exact handleEmbedding_mem_lower_iff (zero_le (m + 1)) c ε r data hε hεr p

theorem morse_smooth_handle_attachment_top {m : ℕ} (c ε r : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
    (I : ModelWithCorners ℝ (MorseModel (m + 1)) H) [I.Boundaryless]
    [IsManifold I (⊤ : WithTop ℕ∞) M] (f : M → ℝ)
    (data : MorseChart (m + 1) (m + 1) (le_rfl : m + 1 ≤ m + 1) c I f)
    (hε : 0 < ε)
    (hεr : Real.sqrt (2 * ε + 2 * r ^ 2) ≤ data.R)
    (hRltR' : data.R < data.R')
    [NeZero (m + 1)] :
    ∃ φ : ClosedCell (m + 1) → M,
      φ = topHandleEmbedding c ε data ∧
      @ContMDiff ℝ _
        (EuclideanSpace ℝ (Fin (((m + 1 - 1) + 1)))) _ _
        (EuclideanHalfSpace ((m + 1 - 1) + 1)) _ (modelWithCornersEuclideanHalfSpace ((m + 1 - 1) + 1))
        (ClosedCell (m + 1)) _ (closedCellChartedSpace (m + 1))
        (MorseModel (m + 1)) _ _ H _ I M _ _
        (⊤ : ℕ∞)
        φ ∧
      Topology.IsClosedEmbedding φ ∧
      (∀ x : ClosedCell (m + 1),
        f (φ x) = c - ε * ‖(x : EuclideanSpace ℝ (Fin (m + 1)))‖ ^ 2) ∧
      (∀ u : CellBoundary (m + 1),
        φ (cellBoundaryInclusion (m + 1) u) =
          (cocoreAttachingEmbedding (le_rfl : m + 1 ≤ m + 1) c ε r data hε hεr
            (u, ⟨0, by simp⟩)).1) ∧
      (∀ x : ClosedCell (m + 1), φ x ∈ sublevel f (c + r ^ 2 / 2)) ∧
      (∀ x : ClosedCell (m + 1),
        φ x ∈ sublevel f (c - ε) ↔ ‖(x : EuclideanSpace ℝ (Fin (m + 1)))‖ = 1) := by
  have hεr' : Real.sqrt (2 * ε) ≤ data.R := by
    exact le_trans (Real.sqrt_le_sqrt (by nlinarith [sq_nonneg r])) hεr
  refine ⟨topHandleEmbedding c ε data, rfl, ?_, ?_⟩
  · exact contMDiff_topHandleEmbedding c ε data hεr' hRltR'
  constructor
  · exact isClosedEmbedding_topHandleEmbedding c ε data hε hεr' hRltR'
  constructor
  · intro x
    exact topHandleEmbedding_f_value c ε data (le_of_lt hε) hεr' x
  constructor
  · intro u
    exact topHandleEmbedding_attachingRegion c ε r data hε hεr u
  constructor
  · intro x
    exact topHandleEmbedding_mem_sublevel c ε (c + r ^ 2 / 2) data (le_of_lt hε) hεr'
      (by nlinarith [sq_nonneg r]) x
  · intro x
    exact topHandleEmbedding_mem_lower_iff c ε data hε hεr' x

theorem handleEmbedding_continuous {n k : ℕ} (hk : k ≤ n) (c ε r : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ (MorseModel n) H} {f : M → ℝ}
    (data : MorseChart n k hk c I f)
    (hε : 0 < ε) (hεr : Real.sqrt (2 * ε + 2 * r ^ 2) ≤ data.R) :
    Continuous (handleEmbedding hk c ε r data) := by
  have hproj : Continuous (fun p : StandardHandle k (n - k) =>
      ((p.1 : EuclideanSpace ℝ (Fin k)), (p.2 : EuclideanSpace ℝ (Fin (n - k))))) := by
    fun_prop
  have hmmap : Continuous (fun p : StandardHandle k (n - k) =>
      (modelHandleMap hk ε r p : MorseModel n)) := by
    have h := (modelHandleMap_contDiff hk r ε hε).continuous.comp hproj
    simpa [modelHandleMap] using h
  have hmap : Set.MapsTo (fun p : StandardHandle k (n - k) =>
      (modelHandleMap hk ε r p : MorseModel n)) Set.univ data.χ.source := by
    intro p hp
    exact data.hχsrc (modelHandleMap hk ε r p)
      (le_trans (modelHandleMap_norm_le hk ε r (le_of_lt hε) p) hεr)
  have hcontOn : ContinuousOn (fun p : StandardHandle k (n - k) =>
      data.χ (modelHandleMap hk ε r p)) Set.univ :=
    data.χ.continuousOn_toFun.comp hmmap.continuousOn hmap
  change Continuous (fun p : StandardHandle k (n - k) => data.χ (modelHandleMap hk ε r p))
  exact (continuousOn_univ.mp hcontOn)

noncomputable def handleAttachingMap {n k : ℕ} (hk : k ≤ n) (c ε r : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ (MorseModel n) H} {f : M → ℝ}
    (data : MorseChart n k hk c I f)
    (hε : 0 < ε) (hεr : Real.sqrt (2 * ε + 2 * r ^ 2) ≤ data.R) :
    C(CellBoundary k, SublevelSpace f (c - ε)) :=
  ContinuousMap.mk
    (fun u : CellBoundary k =>
      ⟨handleEmbedding hk c ε r data
        (attachingInclusion k (n - k) (attachingSphereInclusionAttachingRegion k (n - k) u)), by
        exact (handleEmbedding_mem_lower_iff hk c ε r data hε hεr
          (attachingInclusion k (n - k) (attachingSphereInclusionAttachingRegion k (n - k) u))).2 u.2⟩)
    (by
      have hcont : Continuous (fun u : CellBoundary k =>
          handleEmbedding hk c ε r data
            (attachingInclusion k (n - k) (attachingSphereInclusionAttachingRegion k (n - k) u))) := by
        have hinc : Continuous (fun u : CellBoundary k =>
            (attachingInclusion k (n - k) (attachingSphereInclusionAttachingRegion k (n - k) u) :
              StandardHandle k (n - k))) := by
          dsimp [attachingInclusion, attachingSphereInclusionAttachingRegion]
          have hb : Continuous (cellBoundaryInclusion k) := by
            exact Continuous.subtype_mk continuous_subtype_val (by intro x; exact le_of_eq x.2)
          exact hb.prodMk continuous_const
        exact (handleEmbedding_continuous hk c ε r data hε hεr).comp hinc
      exact Continuous.subtype_mk hcont (by
        intro u
        exact (handleEmbedding_mem_lower_iff hk c ε r data hε hεr
          (attachingInclusion k (n - k) (attachingSphereInclusionAttachingRegion k (n - k) u))).2 u.2))

theorem handleAttachingMap_spine {n k : ℕ} (hk : k ≤ n) (c ε r : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ (MorseModel n) H} {f : M → ℝ}
    (data : MorseChart n k hk c I f)
    (hε : 0 < ε) (hεr : Real.sqrt (2 * ε + 2 * r ^ 2) ≤ data.R)
    (u : CellBoundary k) :
    (handleAttachingMap hk c ε r data hε hεr u).1 =
      (cocoreAttachingEmbedding hk c ε r data hε hεr (u, closedCellCenter (n - k))).1 := by
  change handleEmbedding hk c ε r data
    (attachingInclusion k (n - k) (attachingSphereInclusionAttachingRegion k (n - k) u)) =
    (cocoreAttachingEmbedding hk c ε r data hε hεr (u, closedCellCenter (n - k))).1
  simpa [attachingSphereInclusionAttachingRegion, attachingInclusion] using
    (handleEmbedding_attachingRegion hk c ε r data hε hεr (u, closedCellCenter (n - k)))

theorem contMDiff_modelAttachedStretch_sublevel {m k : ℕ} (hk : k ≤ m + 1) (c ε r δ : ℝ)
    (hδ0 : 0 < δ) (hδr : δ < r ^ 2) (hr : r ≠ 0)
    (hcs₁ : ChartedSpace (MorseHalfSpace m)
        (SublevelSpace (CellAttachment.morseNormalForm hk c) (c + r ^ 2 / 2)) :=
      sublevelChartedSpace (m := m) (CellAttachment.morseNormalForm hk c)
        (c + r ^ 2 / 2) (CellAttachment.contDiff_morseNormalForm hk c)
        (fun y hy => CellAttachment.fderiv_morseNormalForm_ne_zero hk c (r ^ 2 / 2) (by positivity) y hy))
    (hcs₂ : ChartedSpace (MorseHalfSpace m)
        (SublevelSpace (CellAttachment.modelAttachedFunction hk c ε r δ) c) :=
      sublevelChartedSpace (m := m) (CellAttachment.modelAttachedFunction hk c ε r δ) c
        (CellAttachment.contDiff_modelAttachedFunction hk c ε r δ)
        (CellAttachment.fderiv_modelAttachedFunction_ne_zero hk c ε r δ hδ0 hδr))
    (hchart₁ : ∀ y : SublevelSpace (CellAttachment.morseNormalForm hk c) (c + r ^ 2 / 2),
      hcs₁.chartAt y =
        (if h : CellAttachment.morseNormalForm hk c y.1 = c + r ^ 2 / 2 then
          sublevelBoundaryChart (CellAttachment.morseNormalForm hk c) (c + r ^ 2 / 2) y h
            (CellAttachment.contDiff_morseNormalForm hk c)
            (CellAttachment.fderiv_morseNormalForm_ne_zero hk c (r ^ 2 / 2) (by positivity) y.1 h)
        else sublevelInteriorChart (CellAttachment.morseNormalForm hk c) (c + r ^ 2 / 2) y
          (lt_of_le_of_ne (show CellAttachment.morseNormalForm hk c y.1 ≤ c + r ^ 2 / 2 from y.2) h)
          (CellAttachment.contDiff_morseNormalForm hk c)) := by
      intro y
      rfl)
    (hchart₂ : ∀ y : SublevelSpace (CellAttachment.modelAttachedFunction hk c ε r δ) c,
      hcs₂.chartAt y =
        (if h : CellAttachment.modelAttachedFunction hk c ε r δ y.1 = c then
          sublevelBoundaryChart (CellAttachment.modelAttachedFunction hk c ε r δ) c y h
            (CellAttachment.contDiff_modelAttachedFunction hk c ε r δ)
            (CellAttachment.fderiv_modelAttachedFunction_ne_zero hk c ε r δ hδ0 hδr y.1 h)
        else sublevelInteriorChart (CellAttachment.modelAttachedFunction hk c ε r δ) c y
          (lt_of_le_of_ne (show CellAttachment.modelAttachedFunction hk c ε r δ y.1 ≤ c from y.2) h)
          (CellAttachment.contDiff_modelAttachedFunction hk c ε r δ)) := by
      intro y
      rfl) :
    ContMDiff (morseModelWithCornersHalfSpace m) (morseModelWithCornersHalfSpace m) (⊤ : ℕ∞)
      (fun y : SublevelSpace (CellAttachment.morseNormalForm hk c) (c + r ^ 2 / 2) =>
        (⟨CellAttachment.modelAttachedStretch hk ε r δ y.1,
          (by
            have hm : CellAttachment.modelAttachedStretch hk ε r δ y.1 ∈
                CellAttachment.modelAttachedRegion hk ε r δ :=
              (CellAttachment.modelAttachedStretch_equiv hk c ε r δ hδ0 hδr hr).1 y.1 y.2
            exact (by
              rw [← CellAttachment.modelAttachedRegion_eq_sublevel hk c ε r δ]
              exact hm))⟩ :
          SublevelSpace (CellAttachment.modelAttachedFunction hk c ε r δ) c)) := by
  exact contMDiff_sublevelMap (m := m) (CellAttachment.morseNormalForm hk c)
    (CellAttachment.modelAttachedFunction hk c ε r δ)
    (c + r ^ 2 / 2) c (CellAttachment.contDiff_morseNormalForm hk c)
    (CellAttachment.contDiff_modelAttachedFunction hk c ε r δ)
    (fun y hy => CellAttachment.fderiv_morseNormalForm_ne_zero hk c (r ^ 2 / 2) (by positivity) y hy)
    (CellAttachment.fderiv_modelAttachedFunction_ne_zero hk c ε r δ hδ0 hδr)
    (CellAttachment.modelAttachedStretch hk ε r δ)
    (CellAttachment.contDiff_modelAttachedStretch hk ε r δ hδ0 hδr hr)
    (fun y hy => by
      have hmem : CellAttachment.modelAttachedStretch hk ε r δ y ∈
          CellAttachment.modelAttachedRegion hk ε r δ :=
        (CellAttachment.modelAttachedStretch_equiv hk c ε r δ hδ0 hδr hr).1 y hy
      have hsub : CellAttachment.modelAttachedStretch hk ε r δ y ∈
          sublevel (CellAttachment.modelAttachedFunction hk c ε r δ) c := by
        rw [← CellAttachment.modelAttachedRegion_eq_sublevel hk c ε r δ]
        exact hmem
      change CellAttachment.modelAttachedFunction hk c ε r δ
        (CellAttachment.modelAttachedStretch hk ε r δ y) ≤ c
      simpa [sublevel] using hsub)
    (fun y hy => CellAttachment.modelAttachedFunction_stretch_boundary hk c ε r δ hδ0 hδr hr y hy)
    (fun y hy => CellAttachment.modelAttachedFunction_stretch_strict hk c ε r δ hδ0 hδr hr y hy)
    (hcs₁ := hcs₁)
    (hcs₂ := hcs₂)
    (hchart₁ := hchart₁)
    (hchart₂ := hchart₂)

theorem contMDiff_modelAttachedUnstretch_sublevel {m k : ℕ} (hk : k ≤ m + 1) (c ε r δ : ℝ)
    (hδ0 : 0 < δ) (hδr : δ < r ^ 2)
    (hcs₁ : ChartedSpace (MorseHalfSpace m)
        (SublevelSpace (CellAttachment.modelAttachedFunction hk c ε r δ) c) :=
      sublevelChartedSpace (m := m) (CellAttachment.modelAttachedFunction hk c ε r δ) c
        (CellAttachment.contDiff_modelAttachedFunction hk c ε r δ)
        (CellAttachment.fderiv_modelAttachedFunction_ne_zero hk c ε r δ hδ0 hδr))
    (hcs₂ : ChartedSpace (MorseHalfSpace m)
        (SublevelSpace (CellAttachment.morseNormalForm hk c) (c + r ^ 2 / 2)) :=
      sublevelChartedSpace (m := m) (CellAttachment.morseNormalForm hk c)
        (c + r ^ 2 / 2) (CellAttachment.contDiff_morseNormalForm hk c)
        (fun y hy => CellAttachment.fderiv_morseNormalForm_ne_zero hk c (r ^ 2 / 2)
          (by
            have hz : (0 : ℝ) < r ^ 2 := sq_pos_of_ne_zero (by
              intro hr0'
              exact (lt_irrefl (0 : ℝ)) (by
                have hlt : δ < 0 := by
                  rw [hr0', zero_pow two_ne_zero] at hδr
                  exact hδr
                linarith [hδ0, hlt]))
            exact div_pos hz (by norm_num)) y hy))
    (hchart₁ : ∀ y : SublevelSpace (CellAttachment.modelAttachedFunction hk c ε r δ) c,
      hcs₁.chartAt y =
        (if h : CellAttachment.modelAttachedFunction hk c ε r δ y.1 = c then
          sublevelBoundaryChart (CellAttachment.modelAttachedFunction hk c ε r δ) c y h
            (CellAttachment.contDiff_modelAttachedFunction hk c ε r δ)
            (CellAttachment.fderiv_modelAttachedFunction_ne_zero hk c ε r δ hδ0 hδr y.1 h)
        else sublevelInteriorChart (CellAttachment.modelAttachedFunction hk c ε r δ) c y
          (lt_of_le_of_ne (show CellAttachment.modelAttachedFunction hk c ε r δ y.1 ≤ c from y.2) h)
          (CellAttachment.contDiff_modelAttachedFunction hk c ε r δ)) := by
      intro y
      rfl)
    (hchart₂ : ∀ y : SublevelSpace (CellAttachment.morseNormalForm hk c) (c + r ^ 2 / 2),
      hcs₂.chartAt y =
        (if h : CellAttachment.morseNormalForm hk c y.1 = c + r ^ 2 / 2 then
          sublevelBoundaryChart (CellAttachment.morseNormalForm hk c) (c + r ^ 2 / 2) y h
            (CellAttachment.contDiff_morseNormalForm hk c)
            (CellAttachment.fderiv_morseNormalForm_ne_zero hk c (r ^ 2 / 2)
              (by
                have hz : (0 : ℝ) < r ^ 2 := sq_pos_of_ne_zero (by
                  intro hr0'
                  exact (lt_irrefl (0 : ℝ)) (by
                    have hlt : δ < 0 := by
                      rw [hr0', zero_pow two_ne_zero] at hδr
                      exact hδr
                    linarith [hδ0, hlt]))
                exact div_pos hz (by norm_num)) y.1 h)
        else sublevelInteriorChart (CellAttachment.morseNormalForm hk c) (c + r ^ 2 / 2) y
          (lt_of_le_of_ne (show CellAttachment.morseNormalForm hk c y.1 ≤ c + r ^ 2 / 2 from y.2) h)
          (CellAttachment.contDiff_morseNormalForm hk c)) := by
      intro y
      rfl) :
    ContMDiff (morseModelWithCornersHalfSpace m) (morseModelWithCornersHalfSpace m) (⊤ : ℕ∞)
      (fun y : SublevelSpace (CellAttachment.modelAttachedFunction hk c ε r δ) c =>
        (⟨CellAttachment.modelAttachedUnstretch hk ε r δ y.1,
          (by
            have hm : CellAttachment.morseNormalForm hk c
                (CellAttachment.modelAttachedUnstretch hk ε r δ y.1) ≤ c + r ^ 2 / 2 :=
              by
                have hz : (0 : ℝ) < r ^ 2 := sq_pos_of_ne_zero (by
                  intro hr0'
                  exact (lt_irrefl (0 : ℝ)) (by
                    have hlt : δ < 0 := by
                      rw [hr0', zero_pow two_ne_zero] at hδr
                      exact hδr
                    linarith [hδ0, hlt]))
                exact (CellAttachment.modelAttachedStretch_equiv hk c ε r δ hδ0 hδr
                  (by
                    intro hr0'
                    exact (ne_of_gt hz) (by
                      rw [hr0', zero_pow two_ne_zero]))).2.1 y.1
                  (by
                    exact (CellAttachment.modelAttachedRegion_iff_sublevel hk c ε r δ y.1).mpr y.2)
            exact hm)⟩ :
          SublevelSpace (CellAttachment.morseNormalForm hk c) (c + r ^ 2 / 2))) := by
  letI := hcs₁
  letI := hcs₂
  let hr : r ≠ 0 := by
    intro hr0
    have hz : (0 : ℝ) < r ^ 2 := sq_pos_of_ne_zero (by
      intro hr0'
      exact (lt_irrefl (0 : ℝ)) (by
        have hlt : δ < 0 := by
          rw [hr0', zero_pow two_ne_zero] at hδr
          exact hδr
        linarith [hδ0, hlt]))
    exact (ne_of_gt hz) (by
      rw [hr0, zero_pow two_ne_zero])
  exact contMDiff_sublevelMap (m := m) (CellAttachment.modelAttachedFunction hk c ε r δ)
    (CellAttachment.morseNormalForm hk c) c (c + r ^ 2 / 2)
    (CellAttachment.contDiff_modelAttachedFunction hk c ε r δ)
    (CellAttachment.contDiff_morseNormalForm hk c)
    (CellAttachment.fderiv_modelAttachedFunction_ne_zero hk c ε r δ hδ0 hδr)
    (fun y hy => CellAttachment.fderiv_morseNormalForm_ne_zero hk c (r ^ 2 / 2)
      (by
        have hz : (0 : ℝ) < r ^ 2 := sq_pos_of_ne_zero (by
          intro hr0'
          exact (lt_irrefl (0 : ℝ)) (by
            have hlt : δ < 0 := by
              rw [hr0', zero_pow two_ne_zero] at hδr
              exact hδr
            linarith [hδ0, hlt]))
        exact div_pos hz (by norm_num)) y hy)
    (CellAttachment.modelAttachedUnstretch hk ε r δ)
    (CellAttachment.contDiff_modelAttachedUnstretch hk ε r δ hδ0 hδr hr)
    (fun y hy => (CellAttachment.modelAttachedStretch_equiv hk c ε r δ hδ0 hδr hr).2.1 y
      ((CellAttachment.modelAttachedRegion_iff_sublevel hk c ε r δ y).mpr hy))
    (fun y hy => CellAttachment.modelAttachedFunction_unstretch_boundary hk c ε r δ hδ0 hδr y
      ((CellAttachment.modelAttachedRegion_iff_sublevel hk c ε r δ y).mpr (le_of_eq hy)) hy)
    (fun y hy => CellAttachment.modelAttachedFunction_unstretch_strict hk c ε r δ hδ0 hδr y
      ((CellAttachment.modelAttachedRegion_iff_sublevel hk c ε r δ y).mpr (le_of_lt hy)) hy)
    (hcs₁ := hcs₁)
    (hcs₂ := hcs₂)
    (hchart₁ := hchart₁)
    (hchart₂ := hchart₂)

noncomputable def modelAttachedSublevelDiffeomorph {m k : ℕ} (hk : k ≤ m + 1) (c ε r δ : ℝ)
    (hδ0 : 0 < δ) (hδr : δ < r ^ 2) (hr : r ≠ 0)
    (hcs₁ : ChartedSpace (MorseHalfSpace m)
        (SublevelSpace (CellAttachment.morseNormalForm hk c) (c + r ^ 2 / 2)) :=
      sublevelChartedSpace (m := m) (CellAttachment.morseNormalForm hk c)
        (c + r ^ 2 / 2) (CellAttachment.contDiff_morseNormalForm hk c)
        (fun y hy => CellAttachment.fderiv_morseNormalForm_ne_zero hk c (r ^ 2 / 2) (by positivity) y hy))
    (hcs₂ : ChartedSpace (MorseHalfSpace m)
        (SublevelSpace (CellAttachment.modelAttachedFunction hk c ε r δ) c) :=
      sublevelChartedSpace (m := m) (CellAttachment.modelAttachedFunction hk c ε r δ) c
        (CellAttachment.contDiff_modelAttachedFunction hk c ε r δ)
        (CellAttachment.fderiv_modelAttachedFunction_ne_zero hk c ε r δ hδ0 hδr))
    (hchart₁ : ∀ y : SublevelSpace (CellAttachment.morseNormalForm hk c) (c + r ^ 2 / 2),
      hcs₁.chartAt y =
        (if h : CellAttachment.morseNormalForm hk c y.1 = c + r ^ 2 / 2 then
          sublevelBoundaryChart (CellAttachment.morseNormalForm hk c) (c + r ^ 2 / 2) y h
            (CellAttachment.contDiff_morseNormalForm hk c)
            (CellAttachment.fderiv_morseNormalForm_ne_zero hk c (r ^ 2 / 2) (by positivity) y.1 h)
        else sublevelInteriorChart (CellAttachment.morseNormalForm hk c) (c + r ^ 2 / 2) y
          (lt_of_le_of_ne (show CellAttachment.morseNormalForm hk c y.1 ≤ c + r ^ 2 / 2 from y.2) h)
          (CellAttachment.contDiff_morseNormalForm hk c)) := by
      intro y
      rfl)
    (hchart₂ : ∀ y : SublevelSpace (CellAttachment.modelAttachedFunction hk c ε r δ) c,
      hcs₂.chartAt y =
        (if h : CellAttachment.modelAttachedFunction hk c ε r δ y.1 = c then
          sublevelBoundaryChart (CellAttachment.modelAttachedFunction hk c ε r δ) c y h
            (CellAttachment.contDiff_modelAttachedFunction hk c ε r δ)
            (CellAttachment.fderiv_modelAttachedFunction_ne_zero hk c ε r δ hδ0 hδr y.1 h)
        else sublevelInteriorChart (CellAttachment.modelAttachedFunction hk c ε r δ) c y
          (lt_of_le_of_ne (show CellAttachment.modelAttachedFunction hk c ε r δ y.1 ≤ c from y.2) h)
          (CellAttachment.contDiff_modelAttachedFunction hk c ε r δ)) := by
      intro y
      rfl) :
    SublevelSpace (CellAttachment.morseNormalForm hk c) (c + r ^ 2 / 2) ≃ₘ⟮
      morseModelWithCornersHalfSpace m, morseModelWithCornersHalfSpace m⟯
      SublevelSpace (CellAttachment.modelAttachedFunction hk c ε r δ) c where
  toEquiv :=
    { toFun := fun y => (⟨CellAttachment.modelAttachedStretch hk ε r δ y.1,
        (by
          have hm : CellAttachment.modelAttachedStretch hk ε r δ y.1 ∈
              CellAttachment.modelAttachedRegion hk ε r δ :=
            (CellAttachment.modelAttachedStretch_equiv hk c ε r δ hδ0 hδr hr).1 y.1 y.2
          have hsub : CellAttachment.modelAttachedStretch hk ε r δ y.1 ∈
              sublevel (CellAttachment.modelAttachedFunction hk c ε r δ) c := by
            rw [← CellAttachment.modelAttachedRegion_eq_sublevel hk c ε r δ]
            exact hm
          exact hsub)⟩ :
        SublevelSpace (CellAttachment.modelAttachedFunction hk c ε r δ) c)
      invFun := fun y => (⟨CellAttachment.modelAttachedUnstretch hk ε r δ y.1,
        (CellAttachment.modelAttachedStretch_equiv hk c ε r δ hδ0 hδr hr).2.1 y.1
          ((CellAttachment.modelAttachedRegion_iff_sublevel hk c ε r δ y.1).mpr y.2)⟩ :
        SublevelSpace (CellAttachment.morseNormalForm hk c) (c + r ^ 2 / 2))
      left_inv := by
        intro y
        apply Subtype.ext
        exact CellAttachment.modelAttachedUnstretch_stretch hk ε r δ hδ0 hδr hr y.1
      right_inv := by
        intro y
        apply Subtype.ext
        exact CellAttachment.modelAttachedStretch_unstretch hk ε r δ hδ0 hδr hr y.1 }
  contMDiff_toFun := by
    simpa using (contMDiff_modelAttachedStretch_sublevel (hk := hk) (c := c) (ε := ε) (r := r)
      (δ := δ) (hδ0 := hδ0) (hδr := hδr) (hr := hr) (hcs₁ := hcs₁) (hcs₂ := hcs₂)
      (hchart₁ := hchart₁) (hchart₂ := hchart₂))
  contMDiff_invFun := by
    simpa using (contMDiff_modelAttachedUnstretch_sublevel (hk := hk) (c := c) (ε := ε) (r := r)
      (δ := δ) (hδ0 := hδ0) (hδr := hδr) (hcs₁ := hcs₂) (hcs₂ := hcs₁)
      (hchart₁ := hchart₂) (hchart₂ := hchart₁))

theorem modelAttachedSublevelIsManifold {m k : ℕ} (hk : k ≤ m + 1) (c ε r δ : ℝ)
    (hδ0 : 0 < δ) (hδr : δ < r ^ 2) :
    @IsManifold ℝ _ (MorseModel (m + 1)) _ _ (MorseHalfSpace m) _
      (morseModelWithCornersHalfSpace m) (⊤ : ℕ∞)
      (SublevelSpace (CellAttachment.modelAttachedFunction hk c ε r δ) c) _
      (sublevelChartedSpace (m := m) (CellAttachment.modelAttachedFunction hk c ε r δ) c
        (CellAttachment.contDiff_modelAttachedFunction hk c ε r δ)
        (CellAttachment.fderiv_modelAttachedFunction_ne_zero hk c ε r δ hδ0 hδr)) :=
  sublevelIsManifold (m := m) (CellAttachment.modelAttachedFunction hk c ε r δ) c
    (CellAttachment.contDiff_modelAttachedFunction hk c ε r δ)
    (CellAttachment.fderiv_modelAttachedFunction_ne_zero hk c ε r δ hδ0 hδr)

abbrev morseLowerSublevel {m k : ℕ} (hk : k ≤ m + 1) (c ε : ℝ) : Type :=
  SublevelSpace (CellAttachment.morseNormalForm hk c) (c - ε)

abbrev morseUpperSublevel {m k : ℕ} (hk : k ≤ m + 1) (c r : ℝ) : Type :=
  SublevelSpace (CellAttachment.morseNormalForm hk c) (c + r ^ 2 / 2)

abbrev morseHandleSublevel {m k : ℕ} (hk : k ≤ m + 1) (c ε r δ : ℝ) : Type :=
  SublevelSpace (CellAttachment.modelAttachedFunction hk c ε r δ) c

theorem morseLowerSublevel_mem_upper {m k : ℕ} (hk : k ≤ m + 1) (c ε r : ℝ)
    (hε : 0 ≤ ε) (a : morseLowerSublevel hk c ε) :
    CellAttachment.morseNormalForm hk c a.1 ≤ c + r ^ 2 / 2 := by
  have hle : CellAttachment.morseNormalForm hk c a.1 ≤ c - ε := by
    change a.1 ∈ sublevel (CellAttachment.morseNormalForm hk c) (c - ε)
    exact a.2
  have hr2 : 0 ≤ r ^ 2 := sq_nonneg r
  nlinarith [hε, hr2]

theorem morseUpperSublevel_mem_stretch_handle {m k : ℕ} (hk : k ≤ m + 1) (c ε r δ : ℝ)
    (hδ0 : 0 < δ) (hδr : δ < r ^ 2) (hr : r ≠ 0) (u : morseUpperSublevel hk c r) :
    CellAttachment.modelAttachedStretch hk ε r δ u.1 ∈
      sublevel (CellAttachment.modelAttachedFunction hk c ε r δ) c := by
  change CellAttachment.modelAttachedFunction hk c ε r δ
    (CellAttachment.modelAttachedStretch hk ε r δ u.1) ≤ c
  exact (CellAttachment.modelAttachedRegion_iff_sublevel hk c ε r δ
    (CellAttachment.modelAttachedStretch hk ε r δ u.1)).mp
    ((CellAttachment.modelAttachedStretch_equiv hk c ε r δ hδ0 hδr hr).1 u.1 (by
      exact u.2))

noncomputable def morseHandleGlueMap {m k : ℕ} (hk : k ≤ m + 1) (c ε r δ : ℝ)
    (hε : 0 ≤ ε) (hδ0 : 0 < δ) (hδr : δ < r ^ 2) (hr : r ≠ 0) :
    morseLowerSublevel hk c ε → morseHandleSublevel hk c ε r δ :=
  fun a => ⟨CellAttachment.modelAttachedStretch hk ε r δ a.1, by
    change CellAttachment.modelAttachedFunction hk c ε r δ
      (CellAttachment.modelAttachedStretch hk ε r δ a.1) ≤ c
    exact (CellAttachment.modelAttachedRegion_iff_sublevel hk c ε r δ
      (CellAttachment.modelAttachedStretch hk ε r δ a.1)).mp
      ((CellAttachment.modelAttachedStretch_equiv hk c ε r δ hδ0 hδr hr).1 a.1
        (morseLowerSublevel_mem_upper hk c ε r hε a))⟩

abbrev morseAttachedSpace {m k : ℕ} (hk : k ≤ m + 1) (c ε r δ : ℝ)
    (hε : 0 ≤ ε) (hδ0 : 0 < δ) (hδr : δ < r ^ 2) (hr : r ≠ 0) : Type :=
  DifferentialGeometry.Topology.AdjunctionSpace
    (i := fun a : morseLowerSublevel hk c ε => a)
    (φ := morseHandleGlueMap hk c ε r δ hε hδ0 hδr hr)

theorem cocoreModelPoint_eq_modelHandleMap {n k : ℕ} (hk : k ≤ n) (ε r : ℝ)
    (u : CellBoundary k) (w : ClosedCell (n - k)) :
    cocoreModelPoint hk ε r (u, w) =
      modelHandleMap hk ε r (cellBoundaryInclusion k u, w) := by
  dsimp [cocoreModelPoint]
  rw [modelHandleMap_attachingRegion]

noncomputable def morseAttachingMap {m k : ℕ} (hk : k ≤ m + 1) (c ε r : ℝ)
    (hε : 0 < ε) : AttachingRegion k (m + 1 - k) → morseLowerSublevel hk c ε :=
  fun p => ⟨cocoreModelPoint hk ε r p, le_of_eq (morseNormalForm_cocoreModelPoint hk c ε r (le_of_lt hε) p)⟩

abbrev morseStandardHandleSpace {m k : ℕ} (hk : k ≤ m + 1) (c ε r : ℝ)
    (hε : 0 < ε) : Type :=
  Handle.AdjunctionSpace k (m + 1 - k) (morseAttachingMap hk c ε r hε)

theorem morseAttachingMap_eq_modelHandleMap {m k : ℕ} (hk : k ≤ m + 1) (c ε r : ℝ)
    (hε : 0 < ε) (a : AttachingRegion k (m + 1 - k)) :
    (morseAttachingMap hk c ε r hε a : MorseModel (m + 1)) =
      modelHandleMap hk ε r (attachingInclusion k (m + 1 - k) a) := by
  rcases a with ⟨u, w⟩
  dsimp [morseAttachingMap, attachingInclusion]
  exact cocoreModelPoint_eq_modelHandleMap hk ε r u w

theorem isClosed_morseLowerSublevel {m k : ℕ} (hk : k ≤ m + 1) (c ε : ℝ) :
    IsClosed (sublevel (morseNormalForm hk c) (c - ε) : Set (MorseModel (m + 1))) := by
  have hcont : Continuous (morseNormalForm hk c) := (contDiff_morseNormalForm hk c).continuous
  change IsClosed ((morseNormalForm hk c) ⁻¹' Set.Iic (c - ε))
  exact isClosed_Iic.preimage hcont

theorem disjoint_modelHandleMap_lower {m k : ℕ} (hk : k ≤ m + 1) (c ε r : ℝ) (hε : 0 < ε) :
    Disjoint (modelHandleMap hk ε r '' (Set.univ \ attachingRegion k (m + 1 - k)))
      (sublevel (morseNormalForm hk c) (c - ε) : Set (MorseModel (m + 1))) := by
  rw [Set.disjoint_left]
  intro y hys hyt
  rcases hys with ⟨p, hp, hpy⟩
  have hiff := (modelHandleMap_mem_lower_iff hk c ε r hε p).mp (by simpa [hpy] using hyt)
  have hreg : p ∈ attachingRegion k (m + 1 - k) := by
    dsimp [attachingRegion]
    exact hiff
  exact hp.2 hreg

theorem continuous_modelHandleMap {n k : ℕ} (hk : k ≤ n) (ε r : ℝ) :
    Continuous (modelHandleMap hk ε r) := by
  have hpair : Continuous (fun p : StandardHandle k (n - k) =>
      ((Real.sqrt (2 * ε + r ^ 2 * ‖(p.2 : EuclideanSpace ℝ (Fin (n - k)))‖ ^ 2)) •
        (p.1 : EuclideanSpace ℝ (Fin k)),
       r • (p.2 : EuclideanSpace ℝ (Fin (n - k))))) := by
    fun_prop
  have hrec : Continuous (fun p : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin (n - k)) =>
      recombine hk p.1 p.2) := continuous_recombine hk
  have hstep := hrec.comp hpair
  simpa [modelHandleMap, Function.comp_def] using hstep

noncomputable def morseStandardHandleHomeoUnion {m k : ℕ} (hk : k ≤ m + 1) (c ε r : ℝ)
    (hε : 0 < ε) (hr : r ≠ 0) :
    morseStandardHandleSpace hk c ε r hε ≃ₜ
      {y : MorseModel (m + 1) //
        y ∈ sublevel (morseNormalForm hk c) (c - ε) ∪ Set.range (modelHandleMap hk ε r)} :=
  Handle.adjunctionHomeomorphUnionImage (φ := morseAttachingMap hk c ε r hε)
    (c := modelHandleMap hk ε r)
    (morseAttachingMap_eq_modelHandleMap hk c ε r hε)
    (modelHandleMap_injective hk ε r hε hr)
    (continuous_modelHandleMap hk ε r)
    (disjoint_modelHandleMap_lower hk c ε r hε)
    (isClosed_morseLowerSublevel hk c ε)

noncomputable def morseStandardHandleHomeoBounded {m k : ℕ} (hk : k ≤ m + 1) (c ε r : ℝ)
    (hε : 0 < ε) (hr : 0 < r) :
    morseStandardHandleSpace hk c ε r hε ≃ₜ
      {y : MorseModel (m + 1) //
        y ∈ sublevel (morseNormalForm hk c) (c - ε) ∪
          {y : MorseModel (m + 1) | ‖posPart hk y‖ ≤ r}} :=
  (morseStandardHandleHomeoUnion hk c ε r hε (ne_of_gt hr)).trans (subtypeSetHomeomorph (by
    rw [modelHandleMap_range hk ε r hε hr]
    exact lowerUnion_modelHandle hk c ε r (le_of_lt hr)))

noncomputable def morseAttachedToUpperFun {m k : ℕ} (hk : k ≤ m + 1) (c ε r δ : ℝ)
    (hε : 0 ≤ ε) (hδ0 : 0 < δ) (hδr : δ < r ^ 2) (hr : r ≠ 0) :
    morseLowerSublevel hk c ε ⊕ morseHandleSublevel hk c ε r δ → morseUpperSublevel hk c r :=
  Sum.elim
    (fun a : morseLowerSublevel hk c ε =>
      (⟨a.1, morseLowerSublevel_mem_upper hk c ε r hε a⟩ : morseUpperSublevel hk c r))
    (fun b : morseHandleSublevel hk c ε r δ =>
      (⟨CellAttachment.modelAttachedUnstretch hk ε r δ b.1, by
        change CellAttachment.morseNormalForm hk c
          (CellAttachment.modelAttachedUnstretch hk ε r δ b.1) ≤ c + r ^ 2 / 2
        exact (CellAttachment.modelAttachedStretch_equiv hk c ε r δ hδ0 hδr hr).2.1 b.1
          ((CellAttachment.modelAttachedRegion_iff_sublevel hk c ε r δ b.1).mpr b.2)⟩ :
        morseUpperSublevel hk c r))

private theorem morseAttachedToUpperFun_rel {m k : ℕ} (hk : k ≤ m + 1) (c ε r δ : ℝ)
    (hε : 0 ≤ ε) (hδ0 : 0 < δ) (hδr : δ < r ^ 2) (hr : r ≠ 0) :
    ∀ a b : morseLowerSublevel hk c ε ⊕ morseHandleSublevel hk c ε r δ,
      DifferentialGeometry.Topology.adjunctionRel
        (i := fun a : morseLowerSublevel hk c ε => a)
        (φ := morseHandleGlueMap hk c ε r δ hε hδ0 hδr hr) a b →
      morseAttachedToUpperFun hk c ε r δ hε hδ0 hδr hr a =
        morseAttachedToUpperFun hk c ε r δ hε hδ0 hδr hr b := by
  intro a b hab
  rcases hab with ⟨x, hx | hx⟩
  · rcases hx with ⟨ha, hb⟩
    subst a
    subst b
    apply Subtype.ext
    dsimp
    exact (CellAttachment.modelAttachedUnstretch_stretch hk ε r δ hδ0 hδr hr x.1).symm
  · rcases hx with ⟨hb, ha⟩
    subst a
    subst b
    apply Subtype.ext
    dsimp
    exact CellAttachment.modelAttachedUnstretch_stretch hk ε r δ hδ0 hδr hr x.1

noncomputable def morseAttachedToUpper {m k : ℕ} (hk : k ≤ m + 1) (c ε r δ : ℝ)
    (hε : 0 ≤ ε) (hδ0 : 0 < δ) (hδr : δ < r ^ 2) (hr : r ≠ 0) :
    morseAttachedSpace hk c ε r δ hε hδ0 hδr hr → morseUpperSublevel hk c r :=
  Quot.lift (morseAttachedToUpperFun hk c ε r δ hε hδ0 hδr hr)
    (morseAttachedToUpperFun_rel hk c ε r δ hε hδ0 hδr hr)

theorem morseAttachedToUpper_lower {m k : ℕ} (hk : k ≤ m + 1) (c ε r δ : ℝ)
    (hε : 0 ≤ ε) (hδ0 : 0 < δ) (hδr : δ < r ^ 2) (hr : r ≠ 0)
    (a : morseLowerSublevel hk c ε) :
    morseAttachedToUpper hk c ε r δ hε hδ0 hδr hr
      (DifferentialGeometry.Topology.adjunctionCell
        (i := fun a : morseLowerSublevel hk c ε => a)
        (morseHandleGlueMap hk c ε r δ hε hδ0 hδr hr) a) =
      (⟨a.1, morseLowerSublevel_mem_upper hk c ε r hε a⟩ : morseUpperSublevel hk c r) := by
  exact Quot.lift_mk (morseAttachedToUpperFun hk c ε r δ hε hδ0 hδr hr)
    (morseAttachedToUpperFun_rel hk c ε r δ hε hδ0 hδr hr) (Sum.inl a)

theorem morseAttachedToUpper_handle {m k : ℕ} (hk : k ≤ m + 1) (c ε r δ : ℝ)
    (hε : 0 ≤ ε) (hδ0 : 0 < δ) (hδr : δ < r ^ 2) (hr : r ≠ 0)
    (b : morseHandleSublevel hk c ε r δ) :
    morseAttachedToUpper hk c ε r δ hε hδ0 hδr hr
      (DifferentialGeometry.Topology.adjunctionLower
        (morseHandleGlueMap hk c ε r δ hε hδ0 hδr hr) b) =
      (⟨CellAttachment.modelAttachedUnstretch hk ε r δ b.1, by
        change CellAttachment.morseNormalForm hk c
          (CellAttachment.modelAttachedUnstretch hk ε r δ b.1) ≤ c + r ^ 2 / 2
        exact (CellAttachment.modelAttachedStretch_equiv hk c ε r δ hδ0 hδr hr).2.1 b.1
          ((CellAttachment.modelAttachedRegion_iff_sublevel hk c ε r δ b.1).mpr b.2)⟩ :
        morseUpperSublevel hk c r) := by
  exact Quot.lift_mk (morseAttachedToUpperFun hk c ε r δ hε hδ0 hδr hr)
    (morseAttachedToUpperFun_rel hk c ε r δ hε hδ0 hδr hr) (Sum.inr b)

noncomputable def morseUpperToAttached {m k : ℕ} (hk : k ≤ m + 1) (c ε r δ : ℝ)
    (hε : 0 ≤ ε) (hδ0 : 0 < δ) (hδr : δ < r ^ 2) (hr : r ≠ 0) :
    morseUpperSublevel hk c r → morseAttachedSpace hk c ε r δ hε hδ0 hδr hr :=
  fun u => DifferentialGeometry.Topology.adjunctionLower
    (morseHandleGlueMap hk c ε r δ hε hδ0 hδr hr)
    ⟨CellAttachment.modelAttachedStretch hk ε r δ u.1,
      morseUpperSublevel_mem_stretch_handle hk c ε r δ hδ0 hδr hr u⟩

theorem morseUpperToAttached_left_inv {m k : ℕ} (hk : k ≤ m + 1) (c ε r δ : ℝ)
    (hε : 0 ≤ ε) (hδ0 : 0 < δ) (hδr : δ < r ^ 2) (hr : r ≠ 0) :
    Function.LeftInverse (morseUpperToAttached hk c ε r δ hε hδ0 hδr hr)
      (morseAttachedToUpper hk c ε r δ hε hδ0 hδr hr) := by
  intro x
  rcases Quot.exists_rep x with ⟨z, rfl⟩
  cases z with
  | inl a =>
      have hmem : CellAttachment.modelAttachedStretch hk ε r δ a.1 ∈
          sublevel (CellAttachment.modelAttachedFunction hk c ε r δ) c :=
        morseUpperSublevel_mem_stretch_handle hk c ε r δ hδ0 hδr hr
          (⟨a.1, morseLowerSublevel_mem_upper hk c ε r hε a⟩ : morseUpperSublevel hk c r)
      change morseUpperToAttached hk c ε r δ hε hδ0 hδr hr
        (morseAttachedToUpper hk c ε r δ hε hδ0 hδr hr
          (DifferentialGeometry.Topology.adjunctionCell
            (i := fun a : morseLowerSublevel hk c ε => a)
            (morseHandleGlueMap hk c ε r δ hε hδ0 hδr hr) a)) =
        DifferentialGeometry.Topology.adjunctionCell
          (i := fun a : morseLowerSublevel hk c ε => a)
          (morseHandleGlueMap hk c ε r δ hε hδ0 hδr hr) a
      rw [morseAttachedToUpper_lower hk c ε r δ hε hδ0 hδr hr a]
      dsimp [morseUpperToAttached]
      apply Quot.sound
      refine ⟨a, Or.inr ?_⟩
      constructor <;> rfl
  | inr b =>
      change morseUpperToAttached hk c ε r δ hε hδ0 hδr hr
        (morseAttachedToUpper hk c ε r δ hε hδ0 hδr hr
          (DifferentialGeometry.Topology.adjunctionLower
            (morseHandleGlueMap hk c ε r δ hε hδ0 hδr hr) b)) =
        DifferentialGeometry.Topology.adjunctionLower
          (morseHandleGlueMap hk c ε r δ hε hδ0 hδr hr) b
      rw [morseAttachedToUpper_handle hk c ε r δ hε hδ0 hδr hr b]
      apply congrArg (fun t : morseHandleSublevel hk c ε r δ =>
        DifferentialGeometry.Topology.adjunctionLower
          (morseHandleGlueMap hk c ε r δ hε hδ0 hδr hr) t)
      apply Subtype.ext
      exact CellAttachment.modelAttachedStretch_unstretch hk ε r δ hδ0 hδr hr b.1

theorem morseUpperToAttached_right_inv {m k : ℕ} (hk : k ≤ m + 1) (c ε r δ : ℝ)
    (hε : 0 ≤ ε) (hδ0 : 0 < δ) (hδr : δ < r ^ 2) (hr : r ≠ 0) :
    Function.RightInverse (morseUpperToAttached hk c ε r δ hε hδ0 hδr hr)
      (morseAttachedToUpper hk c ε r δ hε hδ0 hδr hr) := by
  intro u
  dsimp [morseUpperToAttached]
  rw [morseAttachedToUpper_handle hk c ε r δ hε hδ0 hδr hr]
  apply Subtype.ext
  exact CellAttachment.modelAttachedUnstretch_stretch hk ε r δ hδ0 hδr hr u.1

theorem continuous_morseAttachedToUpper {m k : ℕ} (hk : k ≤ m + 1) (c ε r δ : ℝ)
    (hε : 0 ≤ ε) (hδ0 : 0 < δ) (hδr : δ < r ^ 2) (hr : r ≠ 0) :
    Continuous (morseAttachedToUpper hk c ε r δ hε hδ0 hδr hr) := by
  dsimp [morseAttachedToUpper]
  refine continuous_quot_lift (morseAttachedToUpperFun_rel hk c ε r δ hε hδ0 hδr hr) ?_
  dsimp [morseAttachedToUpperFun]
  exact Continuous.sumElim
    (Continuous.subtype_mk continuous_subtype_val (by
      intro a
      change CellAttachment.morseNormalForm hk c a.1 ≤ c + r ^ 2 / 2
      exact morseLowerSublevel_mem_upper hk c ε r hε a))
    (Continuous.subtype_mk
      ((CellAttachment.contDiff_modelAttachedUnstretch hk ε r δ hδ0 hδr hr).continuous.comp
        continuous_subtype_val)
      (by
        intro b
        change CellAttachment.morseNormalForm hk c
          (CellAttachment.modelAttachedUnstretch hk ε r δ b.1) ≤ c + r ^ 2 / 2
        exact (CellAttachment.modelAttachedStretch_equiv hk c ε r δ hδ0 hδr hr).2.1 b.1
          ((CellAttachment.modelAttachedRegion_iff_sublevel hk c ε r δ b.1).mpr b.2)))

theorem continuous_morseUpperToAttached {m k : ℕ} (hk : k ≤ m + 1) (c ε r δ : ℝ)
    (hε : 0 ≤ ε) (hδ0 : 0 < δ) (hδr : δ < r ^ 2) (hr : r ≠ 0) :
    Continuous (morseUpperToAttached hk c ε r δ hε hδ0 hδr hr) := by
  exact Continuous.comp
    (continuous_adjunctionLower (i := fun a : morseLowerSublevel hk c ε => a)
      (φ := morseHandleGlueMap hk c ε r δ hε hδ0 hδr hr))
    (Continuous.subtype_mk
      ((CellAttachment.contDiff_modelAttachedStretch hk ε r δ hδ0 hδr hr).continuous.comp
        continuous_subtype_val)
      (fun u => morseUpperSublevel_mem_stretch_handle hk c ε r δ hδ0 hδr hr u))

noncomputable def morseAttachedHomeoUpper {m k : ℕ} (hk : k ≤ m + 1) (c ε r δ : ℝ)
    (hε : 0 ≤ ε) (hδ0 : 0 < δ) (hδr : δ < r ^ 2) (hr : r ≠ 0) :
    morseAttachedSpace hk c ε r δ hε hδ0 hδr hr ≃ₜ morseUpperSublevel hk c r where
  toFun := morseAttachedToUpper hk c ε r δ hε hδ0 hδr hr
  invFun := morseUpperToAttached hk c ε r δ hε hδ0 hδr hr
  left_inv := morseUpperToAttached_left_inv hk c ε r δ hε hδ0 hδr hr
  right_inv := morseUpperToAttached_right_inv hk c ε r δ hε hδ0 hδr hr
  continuous_toFun := continuous_morseAttachedToUpper hk c ε r δ hε hδ0 hδr hr
  continuous_invFun := continuous_morseUpperToAttached hk c ε r δ hε hδ0 hδr hr

@[reducible]
noncomputable def morseUpperChartedSpace {m k : ℕ} (hk : k ≤ m + 1) (c r : ℝ) (hr : r ≠ 0) :
    ChartedSpace (MorseHalfSpace m) (morseUpperSublevel hk c r) :=
  sublevelChartedSpace (m := m) (CellAttachment.morseNormalForm hk c) (c + r ^ 2 / 2)
    (CellAttachment.contDiff_morseNormalForm hk c)
    (fun y hy => CellAttachment.fderiv_morseNormalForm_ne_zero hk c (r ^ 2 / 2) (by positivity) y hy)

theorem morseUpperIsManifold {m k : ℕ} (hk : k ≤ m + 1) (c r : ℝ) (hr : r ≠ 0) :
    @IsManifold ℝ _ (MorseModel (m + 1)) _ _ (MorseHalfSpace m) _
      (morseModelWithCornersHalfSpace m) (⊤ : ℕ∞)
      (morseUpperSublevel hk c r) _ (morseUpperChartedSpace hk c r hr) :=
  sublevelIsManifold (m := m) (CellAttachment.morseNormalForm hk c) (c + r ^ 2 / 2)
    (CellAttachment.contDiff_morseNormalForm hk c)
    (fun y hy => CellAttachment.fderiv_morseNormalForm_ne_zero hk c (r ^ 2 / 2) (by positivity) y hy)

noncomputable def morseAttachedHomeoRounded {m k : ℕ} (hk : k ≤ m + 1) (c ε r δ : ℝ)
    (hε : 0 ≤ ε) (hδ0 : 0 < δ) (hδr : δ < r ^ 2) (hr : r ≠ 0) :
    morseAttachedSpace hk c ε r δ hε hδ0 hδr hr ≃ₜ
      SublevelSpace (CellAttachment.modelAttachedFunction hk c ε r δ) c := by
  classical
  letI : ChartedSpace (MorseHalfSpace m) (morseUpperSublevel hk c r) :=
    morseUpperChartedSpace hk c r hr
  letI : ChartedSpace (MorseHalfSpace m)
      (SublevelSpace (CellAttachment.modelAttachedFunction hk c ε r δ) c) :=
    sublevelChartedSpace (m := m) (CellAttachment.modelAttachedFunction hk c ε r δ) c
      (CellAttachment.contDiff_modelAttachedFunction hk c ε r δ)
      (CellAttachment.fderiv_modelAttachedFunction_ne_zero hk c ε r δ hδ0 hδr)
  exact (morseAttachedHomeoUpper hk c ε r δ hε hδ0 hδr hr).trans
    (modelAttachedSublevelDiffeomorph hk c ε r δ hδ0 hδr hr).toHomeomorph

@[reducible]
noncomputable def morseAttachedChartedSpace {m k : ℕ} (hk : k ≤ m + 1) (c ε r δ : ℝ)
    (hε : 0 ≤ ε) (hδ0 : 0 < δ) (hδr : δ < r ^ 2) (hr : r ≠ 0) :
    ChartedSpace (MorseHalfSpace m) (morseAttachedSpace hk c ε r δ hε hδ0 hδr hr) :=
  by
    letI : ChartedSpace (MorseHalfSpace m)
        (SublevelSpace (CellAttachment.modelAttachedFunction hk c ε r δ) c) :=
      sublevelChartedSpace (m := m) (CellAttachment.modelAttachedFunction hk c ε r δ) c
        (CellAttachment.contDiff_modelAttachedFunction hk c ε r δ)
        (CellAttachment.fderiv_modelAttachedFunction_ne_zero hk c ε r δ hδ0 hδr)
    exact chartedSpaceOfHomeomorph (morseAttachedHomeoRounded hk c ε r δ hε hδ0 hδr hr)

theorem morseAttachedIsManifoldNatural {m k : ℕ} (hk : k ≤ m + 1) (c ε r δ : ℝ)
    (hε : 0 ≤ ε) (hδ0 : 0 < δ) (hδr : δ < r ^ 2) (hr : r ≠ 0) :
    @IsManifold ℝ _ (MorseModel (m + 1)) _ _ (MorseHalfSpace m) _
      (morseModelWithCornersHalfSpace m) (⊤ : ℕ∞)
      (morseAttachedSpace hk c ε r δ hε hδ0 hδr hr) _
      (morseAttachedChartedSpace hk c ε r δ hε hδ0 hδr hr) := by
  classical
  letI : ChartedSpace (MorseHalfSpace m)
      (SublevelSpace (CellAttachment.modelAttachedFunction hk c ε r δ) c) :=
    sublevelChartedSpace (m := m) (CellAttachment.modelAttachedFunction hk c ε r δ) c
      (CellAttachment.contDiff_modelAttachedFunction hk c ε r δ)
      (CellAttachment.fderiv_modelAttachedFunction_ne_zero hk c ε r δ hδ0 hδr)
  have hmani : @IsManifold ℝ _ (MorseModel (m + 1)) _ _ (MorseHalfSpace m) _
      (morseModelWithCornersHalfSpace m) (⊤ : ℕ∞)
      (SublevelSpace (CellAttachment.modelAttachedFunction hk c ε r δ) c) _ _ :=
    sublevelIsManifold (m := m) (CellAttachment.modelAttachedFunction hk c ε r δ) c
      (CellAttachment.contDiff_modelAttachedFunction hk c ε r δ)
      (CellAttachment.fderiv_modelAttachedFunction_ne_zero hk c ε r δ hδ0 hδr)
  letI := hmani
  exact isManifoldOfHomeomorph (morseModelWithCornersHalfSpace m)
    (morseAttachedHomeoRounded hk c ε r δ hε hδ0 hδr hr)

noncomputable def morseAttachedDiffeomorphUpperNatural {m k : ℕ} (hk : k ≤ m + 1) (c ε r δ : ℝ)
    (hε : 0 ≤ ε) (hδ0 : 0 < δ) (hδr : δ < r ^ 2) (hr : r ≠ 0) :
    @Diffeomorph ℝ _ (MorseModel (m + 1)) _ _ (MorseModel (m + 1)) _ _
      (MorseHalfSpace m) _ (MorseHalfSpace m) _ (morseModelWithCornersHalfSpace m)
      (morseModelWithCornersHalfSpace m)
      (morseAttachedSpace hk c ε r δ hε hδ0 hδr hr) _
      (morseAttachedChartedSpace hk c ε r δ hε hδ0 hδr hr)
      (morseUpperSublevel hk c r) _ (morseUpperChartedSpace hk c r hr)
      (⊤ : ℕ∞) := by
  classical
  letI : ChartedSpace (MorseHalfSpace m) (morseAttachedSpace hk c ε r δ hε hδ0 hδr hr) :=
    morseAttachedChartedSpace hk c ε r δ hε hδ0 hδr hr
  letI : ChartedSpace (MorseHalfSpace m) (morseUpperSublevel hk c r) :=
    morseUpperChartedSpace hk c r hr
  letI : ChartedSpace (MorseHalfSpace m)
      (SublevelSpace (CellAttachment.modelAttachedFunction hk c ε r δ) c) :=
    sublevelChartedSpace (m := m) (CellAttachment.modelAttachedFunction hk c ε r δ) c
      (CellAttachment.contDiff_modelAttachedFunction hk c ε r δ)
      (CellAttachment.fderiv_modelAttachedFunction_ne_zero hk c ε r δ hδ0 hδr)
  have hmani : @IsManifold ℝ _ (MorseModel (m + 1)) _ _ (MorseHalfSpace m) _
      (morseModelWithCornersHalfSpace m) (⊤ : ℕ∞)
      (SublevelSpace (CellAttachment.modelAttachedFunction hk c ε r δ) c) _ _ :=
    sublevelIsManifold (m := m) (CellAttachment.modelAttachedFunction hk c ε r δ) c
      (CellAttachment.contDiff_modelAttachedFunction hk c ε r δ)
      (CellAttachment.fderiv_modelAttachedFunction_ne_zero hk c ε r δ hδ0 hδr)
  letI := hmani
  let H : morseAttachedSpace hk c ε r δ hε hδ0 hδr hr ≃ₜ
      SublevelSpace (CellAttachment.modelAttachedFunction hk c ε r δ) c :=
    morseAttachedHomeoRounded hk c ε r δ hε hδ0 hδr hr
  have hH : ContMDiff (morseModelWithCornersHalfSpace m) (morseModelWithCornersHalfSpace m) (⊤ : ℕ∞)
      (fun z : morseAttachedSpace hk c ε r δ hε hδ0 hδr hr => H z) :=
    contMDiff_homeomorph_of_chartedSpaceOfHomeomorph H (morseModelWithCornersHalfSpace m) (⊤ : ℕ∞)
  have hHs : ContMDiff (morseModelWithCornersHalfSpace m) (morseModelWithCornersHalfSpace m) (⊤ : ℕ∞)
      (fun r : SublevelSpace (CellAttachment.modelAttachedFunction hk c ε r δ) c => H.symm r) :=
    contMDiff_homeomorph_symm_of_chartedSpaceOfHomeomorph H (morseModelWithCornersHalfSpace m) (⊤ : ℕ∞)
  let D0 : SublevelSpace (CellAttachment.morseNormalForm hk c) (c + r ^ 2 / 2) ≃ₘ⟮
      morseModelWithCornersHalfSpace m, morseModelWithCornersHalfSpace m⟯
      SublevelSpace (CellAttachment.modelAttachedFunction hk c ε r δ) c :=
    modelAttachedSublevelDiffeomorph hk c ε r δ hδ0 hδr hr
  have hD0 : ContMDiff (morseModelWithCornersHalfSpace m) (morseModelWithCornersHalfSpace m) (⊤ : ℕ∞)
      (fun y : morseUpperSublevel hk c r => D0 y) :=
    D0.contMDiff_toFun
  have hD0s : ContMDiff (morseModelWithCornersHalfSpace m) (morseModelWithCornersHalfSpace m) (⊤ : ℕ∞)
      (fun r : SublevelSpace (CellAttachment.modelAttachedFunction hk c ε r δ) c => D0.symm r) :=
    D0.contMDiff_invFun
  refine
    { toEquiv := (morseAttachedHomeoUpper hk c ε r δ hε hδ0 hδr hr).toEquiv
      contMDiff_toFun := ?_
      contMDiff_invFun := ?_ }
  · have hcomp : ContMDiff (morseModelWithCornersHalfSpace m)
        (morseModelWithCornersHalfSpace m) (⊤ : ℕ∞)
        (fun z : morseAttachedSpace hk c ε r δ hε hδ0 hδr hr => D0.symm (H z)) :=
      hD0s.comp hH
    refine hcomp.congr ?_
    intro z
    apply Subtype.ext
    have hrel : D0.symm (H z) = morseAttachedHomeoUpper hk c ε r δ hε hδ0 hδr hr z := by
      dsimp [H]
      change D0.toEquiv.symm (D0.toEquiv (morseAttachedHomeoUpper hk c ε r δ hε hδ0 hδr hr z)) =
        morseAttachedHomeoUpper hk c ε r δ hε hδ0 hδr hr z
      exact D0.toEquiv.symm_apply_apply (morseAttachedHomeoUpper hk c ε r δ hε hδ0 hδr hr z)
    exact congrArg Subtype.val hrel.symm
  · have hcomp : ContMDiff (morseModelWithCornersHalfSpace m)
        (morseModelWithCornersHalfSpace m) (⊤ : ℕ∞)
        (fun y : morseUpperSublevel hk c r => H.symm (D0 y)) :=
      hHs.comp hD0
    refine hcomp.congr ?_
    intro y
    have hrel : H.symm (D0 y) = (morseAttachedHomeoUpper hk c ε r δ hε hδ0 hδr hr).symm y := by
      dsimp [H]
      have hz : D0.toHomeomorph.symm (D0 y) = y := by
        change D0.toEquiv.symm (D0.toEquiv y) = y
        exact D0.toEquiv.symm_apply_apply y
      change (morseAttachedHomeoUpper hk c ε r δ hε hδ0 hδr hr).symm
        (D0.toHomeomorph.symm (D0 y)) = (morseAttachedHomeoUpper hk c ε r δ hε hδ0 hδr hr).symm y
      rw [hz]
    exact hrel.symm

@[reducible]
noncomputable def morseLowerChartedSpace {m k : ℕ} (hk : k ≤ m + 1) (c ε : ℝ) (hε : 0 < ε) :
    ChartedSpace (MorseHalfSpace m) (morseLowerSublevel hk c ε) :=
  sublevelChartedSpace (m := m) (CellAttachment.morseNormalForm hk c) (c - ε)
    (CellAttachment.contDiff_morseNormalForm hk c)
    (fun y hy => CellAttachment.fderiv_morseNormalForm_ne_zero_lower hk c ε hε y hy)

theorem contMDiff_morseLowerInclusion {m k : ℕ} (hk : k ≤ m + 1) (c ε r δ : ℝ)
    (hε : 0 < ε) (hδ0 : 0 < δ) (hδr : δ < r ^ 2) (hr : r ≠ 0) :
    @ContMDiff ℝ _ (MorseModel (m + 1)) _ _ (MorseHalfSpace m) _
      (morseModelWithCornersHalfSpace m) (morseLowerSublevel hk c ε) _
      (morseLowerChartedSpace hk c ε hε)
      (MorseModel (m + 1)) _ _ (MorseHalfSpace m) _
      (morseModelWithCornersHalfSpace m)
      (morseAttachedSpace hk c ε r δ (le_of_lt hε) hδ0 hδr hr) _
      (morseAttachedChartedSpace hk c ε r δ (le_of_lt hε) hδ0 hδr hr)
      (⊤ : ℕ∞)
      (fun a => DifferentialGeometry.Topology.adjunctionCell
        (i := fun a : morseLowerSublevel hk c ε => a)
        (morseHandleGlueMap hk c ε r δ (le_of_lt hε) hδ0 hδr hr) a) := by
  classical
  letI : ChartedSpace (MorseHalfSpace m) (morseLowerSublevel hk c ε) :=
    morseLowerChartedSpace hk c ε hε
  letI : ChartedSpace (MorseHalfSpace m) (morseUpperSublevel hk c r) :=
    morseUpperChartedSpace hk c r hr
  letI : ChartedSpace (MorseHalfSpace m)
      (morseAttachedSpace hk c ε r δ (le_of_lt hε) hδ0 hδr hr) :=
    morseAttachedChartedSpace hk c ε r δ (le_of_lt hε) hδ0 hδr hr
  letI : IsManifold (morseModelWithCornersHalfSpace m) (⊤ : ℕ∞) (morseUpperSublevel hk c r) :=
    morseUpperIsManifold hk c r hr
  have hinc : ContMDiff (morseModelWithCornersHalfSpace m)
      (morseModelWithCornersHalfSpace m) (⊤ : ℕ∞)
      (fun a : morseLowerSublevel hk c ε =>
        (⟨a.1, morseLowerSublevel_mem_upper hk c ε r (le_of_lt hε) a⟩ :
          morseUpperSublevel hk c r)) :=
    contMDiff_sublevelInclusion (m := m) (CellAttachment.morseNormalForm hk c)
      (c - ε) (c + r ^ 2 / 2)
      (by
        have hr2 : 0 ≤ r ^ 2 := sq_nonneg r
        nlinarith [hε, hr2])
      (CellAttachment.contDiff_morseNormalForm hk c)
      (fun y hy => CellAttachment.fderiv_morseNormalForm_ne_zero_lower hk c ε hε y hy)
      (fun y hy => CellAttachment.fderiv_morseNormalForm_ne_zero hk c (r ^ 2 / 2) (by positivity) y hy)
      (hcs₁ := morseLowerChartedSpace hk c ε hε) (hcs₂ := morseUpperChartedSpace hk c r hr)
  have hsymm : ContMDiff (morseModelWithCornersHalfSpace m)
      (morseModelWithCornersHalfSpace m) (⊤ : ℕ∞)
      ((morseAttachedHomeoUpper hk c ε r δ (le_of_lt hε) hδ0 hδr hr).symm) :=
    by
      letI : ChartedSpace (MorseHalfSpace m)
          (SublevelSpace (CellAttachment.modelAttachedFunction hk c ε r δ) c) :=
        sublevelChartedSpace (m := m) (CellAttachment.modelAttachedFunction hk c ε r δ) c
          (CellAttachment.contDiff_modelAttachedFunction hk c ε r δ)
          (CellAttachment.fderiv_modelAttachedFunction_ne_zero hk c ε r δ hδ0 hδr)
      have hmani : @IsManifold ℝ _ (MorseModel (m + 1)) _ _ (MorseHalfSpace m) _
          (morseModelWithCornersHalfSpace m) (⊤ : ℕ∞)
          (SublevelSpace (CellAttachment.modelAttachedFunction hk c ε r δ) c) _ _ :=
        sublevelIsManifold (m := m) (CellAttachment.modelAttachedFunction hk c ε r δ) c
          (CellAttachment.contDiff_modelAttachedFunction hk c ε r δ)
          (CellAttachment.fderiv_modelAttachedFunction_ne_zero hk c ε r δ hδ0 hδr)
      letI := hmani
      let H : morseAttachedSpace hk c ε r δ (le_of_lt hε) hδ0 hδr hr ≃ₜ
          SublevelSpace (CellAttachment.modelAttachedFunction hk c ε r δ) c :=
        morseAttachedHomeoRounded hk c ε r δ (le_of_lt hε) hδ0 hδr hr
      have hHs : ContMDiff (morseModelWithCornersHalfSpace m)
          (morseModelWithCornersHalfSpace m) (⊤ : ℕ∞)
          (fun r : SublevelSpace (CellAttachment.modelAttachedFunction hk c ε r δ) c => H.symm r) :=
        contMDiff_homeomorph_symm_of_chartedSpaceOfHomeomorph H
          (morseModelWithCornersHalfSpace m) (⊤ : ℕ∞)
      let D0 : SublevelSpace (CellAttachment.morseNormalForm hk c) (c + r ^ 2 / 2) ≃ₘ⟮
          morseModelWithCornersHalfSpace m, morseModelWithCornersHalfSpace m⟯
          SublevelSpace (CellAttachment.modelAttachedFunction hk c ε r δ) c :=
        modelAttachedSublevelDiffeomorph hk c ε r δ hδ0 hδr hr
      have hD0 : ContMDiff (morseModelWithCornersHalfSpace m)
          (morseModelWithCornersHalfSpace m) (⊤ : ℕ∞)
          (fun y : morseUpperSublevel hk c r => D0 y) :=
        D0.contMDiff_toFun
      have hcomp' : ContMDiff (morseModelWithCornersHalfSpace m)
          (morseModelWithCornersHalfSpace m) (⊤ : ℕ∞)
          (fun y : morseUpperSublevel hk c r => H.symm (D0 y)) :=
        hHs.comp hD0
      refine hcomp'.congr ?_
      intro y
      have hrel : H.symm (D0 y) = (morseAttachedHomeoUpper hk c ε r δ (le_of_lt hε) hδ0 hδr hr).symm y := by
        dsimp [H]
        have hz : D0.toHomeomorph.symm (D0 y) = y := by
          change D0.toEquiv.symm (D0.toEquiv y) = y
          exact D0.toEquiv.symm_apply_apply y
        change (morseAttachedHomeoUpper hk c ε r δ (le_of_lt hε) hδ0 hδr hr).symm
          (D0.toHomeomorph.symm (D0 y)) = (morseAttachedHomeoUpper hk c ε r δ (le_of_lt hε) hδ0 hδr hr).symm y
        rw [hz]
      exact hrel.symm
  have hcomp : ContMDiff (morseModelWithCornersHalfSpace m)
      (morseModelWithCornersHalfSpace m) (⊤ : ℕ∞)
      (fun a : morseLowerSublevel hk c ε =>
        (morseAttachedHomeoUpper hk c ε r δ (le_of_lt hε) hδ0 hδr hr).symm
          (⟨a.1, morseLowerSublevel_mem_upper hk c ε r (le_of_lt hε) a⟩ :
            morseUpperSublevel hk c r)) :=
    hsymm.comp hinc
  refine hcomp.congr ?_
  intro a
  apply Quot.sound
  refine ⟨a, Or.inl ?_⟩
  constructor <;> rfl

theorem morseAttachedIsManifold {m k : ℕ} (hk : k ≤ m + 1) (c ε r δ : ℝ)
    (hε : 0 ≤ ε) (hδ0 : 0 < δ) (hδr : δ < r ^ 2) (hr : r ≠ 0) :
    @IsManifold ℝ _ (MorseModel (m + 1)) _ _ (MorseHalfSpace m) _
      (morseModelWithCornersHalfSpace m) (⊤ : ℕ∞)
      (morseAttachedSpace hk c ε r δ hε hδ0 hδr hr) _
      (morseAttachedChartedSpace hk c ε r δ hε hδ0 hδr hr) := by
  exact morseAttachedIsManifoldNatural hk c ε r δ hε hδ0 hδr hr

noncomputable def morseAttachedDiffeomorphUpper {m k : ℕ} (hk : k ≤ m + 1) (c ε r δ : ℝ)
    (hε : 0 ≤ ε) (hδ0 : 0 < δ) (hδr : δ < r ^ 2) (hr : r ≠ 0) :
    @Diffeomorph ℝ _ (MorseModel (m + 1)) _ _ (MorseModel (m + 1)) _ _
      (MorseHalfSpace m) _ (MorseHalfSpace m) _ (morseModelWithCornersHalfSpace m)
      (morseModelWithCornersHalfSpace m)
      (morseAttachedSpace hk c ε r δ hε hδ0 hδr hr) _
      (morseAttachedChartedSpace hk c ε r δ hε hδ0 hδr hr)
      (morseUpperSublevel hk c r) _ (morseUpperChartedSpace hk c r hr)
      (⊤ : ℕ∞) :=
  morseAttachedDiffeomorphUpperNatural hk c ε r δ hε hδ0 hδr hr

noncomputable def morseAttachedDiffeomorphModifiedSublevel {m k : ℕ} (hk : k ≤ m + 1)
    (c ε r δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) (hδr : δ < r ^ 2) (hr : r ≠ 0) :
    @Diffeomorph ℝ _ (MorseModel (m + 1)) _ _ (MorseModel (m + 1)) _ _
      (MorseHalfSpace m) _ (MorseHalfSpace m) _ (morseModelWithCornersHalfSpace m)
      (morseModelWithCornersHalfSpace m)
      (morseAttachedSpace hk c ε r δ (le_of_lt hε) hδ hδr hr) _
      (morseAttachedChartedSpace hk c ε r δ (le_of_lt hε) hδ hδr hr)
      (SublevelSpace (CellAttachment.modifiedNormalForm hk c ε δ) (c - ε)) _
      (sublevelChartedSpace (m := m) (CellAttachment.modifiedNormalForm hk c ε δ) (c - ε)
        (CellAttachment.contDiff_modifiedNormalForm hk c ε δ hδ)
        (fun y hy => CellAttachment.modifiedNormalForm_no_critical_point_in_strip hk c ε δ hε hδ
          ⟨le_of_eq hy.symm, by linarith⟩))
      (⊤ : ℕ∞) := by
  classical
  letI : ChartedSpace (MorseHalfSpace m) (morseAttachedSpace hk c ε r δ (le_of_lt hε) hδ hδr hr) :=
    morseAttachedChartedSpace hk c ε r δ (le_of_lt hε) hδ hδr hr
  letI : ChartedSpace (MorseHalfSpace m) (morseUpperSublevel hk c r) :=
    morseUpperChartedSpace hk c r hr
  letI : ChartedSpace (MorseHalfSpace m)
      (SublevelSpace (CellAttachment.modifiedNormalForm hk c ε δ) (c - ε)) :=
    sublevelChartedSpace (m := m) (CellAttachment.modifiedNormalForm hk c ε δ) (c - ε)
      (CellAttachment.contDiff_modifiedNormalForm hk c ε δ hδ)
      (fun y hy => CellAttachment.modifiedNormalForm_no_critical_point_in_strip hk c ε δ hε hδ
        ⟨le_of_eq hy.symm, by linarith⟩)
  exact Diffeomorph.trans
    (morseAttachedDiffeomorphUpper hk c ε r δ (le_of_lt hε) hδ hδr hr)
    (CellAttachment.modelModifiedSublevelDiffeomorph hk c ε r δ hε hδ hr).symm

noncomputable def morseHandleEmbeddingAttached {m k : ℕ} (hk : k ≤ m + 1) (c ε r δ : ℝ)
    (hε : 0 ≤ ε) (hδ0 : 0 < δ) (hδr : δ < r ^ 2) (hr : r ≠ 0) :
    StandardHandle k (m + 1 - k) → morseAttachedSpace hk c ε r δ hε hδ0 hδr hr :=
  fun p => DifferentialGeometry.Topology.adjunctionLower
    (morseHandleGlueMap hk c ε r δ hε hδ0 hδr hr)
    ⟨CellAttachment.modelAttachedStretch hk ε r δ (CellAttachment.modelHandleMap hk ε r p),
      morseUpperSublevel_mem_stretch_handle hk c ε r δ hδ0 hδr hr
        ⟨CellAttachment.modelHandleMap hk ε r p,
          CellAttachment.modelHandleMap_mem_upper hk c ε r hε p⟩⟩

theorem morseAttachedToUpper_handleEmbedding {m k : ℕ} (hk : k ≤ m + 1) (c ε r δ : ℝ)
    (hε : 0 ≤ ε) (hδ0 : 0 < δ) (hδr : δ < r ^ 2) (hr : r ≠ 0)
    (p : StandardHandle k (m + 1 - k)) :
    morseAttachedToUpper hk c ε r δ hε hδ0 hδr hr
      (morseHandleEmbeddingAttached hk c ε r δ hε hδ0 hδr hr p) =
      (⟨CellAttachment.modelHandleMap hk ε r p,
        CellAttachment.modelHandleMap_mem_upper hk c ε r hε p⟩ : morseUpperSublevel hk c r) := by
  dsimp [morseHandleEmbeddingAttached]
  rw [morseAttachedToUpper_handle hk c ε r δ hε hδ0 hδr hr]
  apply Subtype.ext
  exact CellAttachment.modelAttachedUnstretch_stretch hk ε r δ hδ0 hδr hr
    (CellAttachment.modelHandleMap hk ε r p)

theorem sq_sqrt_two_mul (ε : ℝ) (hε : 0 ≤ ε) : (Real.sqrt (2 * ε)) ^ 2 = 2 * ε := by
  rw [Real.sq_sqrt (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hε)]

theorem morseAttachedHomotopyEquivCellAdjunction {m k : ℕ} (hk : k ≤ m + 1) (c ε δ : ℝ)
    (hε : 0 < ε) (hδ0 : 0 < δ) (hδr : δ < 2 * ε) :
    Nonempty (ContinuousMap.HomotopyEquiv
      (morseAttachedSpace hk c ε (Real.sqrt (2 * ε)) δ (le_of_lt hε) hδ0
        ((sq_sqrt_two_mul ε (le_of_lt hε)).symm ▸ hδr)
        (ne_of_gt (Real.sqrt_pos.2 (mul_pos zero_lt_two hε))))
      (CellAdjunctionSpace k (CellAttachment.attachMap hk c ε (le_of_lt hε)))) := by
  let r : ℝ := Real.sqrt (2 * ε)
  let hr : r ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (mul_pos zero_lt_two hε))
  have hr₀sq : r ^ 2 = 2 * ε := by
    dsimp [r]
    rw [Real.sq_sqrt (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (le_of_lt hε))]
  have hδr' : δ < r ^ 2 := by
    rw [hr₀sq]
    exact hδr
  let hUpper : morseUpperSublevel hk c r ≃ₜ upperSublevel hk c ε :=
    subtypeSetHomeomorph (by
      have hlevel : c + r ^ 2 / 2 = c + ε := by
        rw [hr₀sq]
        ring
      exact congrArg (sublevel (CellAttachment.morseNormalForm hk c)) hlevel)
  refine ⟨(morseAttachedHomeoUpper hk c ε r δ (le_of_lt hε) hδ0 hδr' hr).toHomotopyEquiv.trans ?_⟩
  exact (hUpper.toHomotopyEquiv.trans (CellAttachment.cellAttachmentModel hk c ε hε))

def morseAttachedDiffeomorphRelative {m k : ℕ} (hk : k ≤ m + 1) (c ε r δ : ℝ)
    (hε : 0 ≤ ε) (hδ0 : 0 < δ) (hδr : δ < r ^ 2) (hr : r ≠ 0)
    (hcs₁ : ChartedSpace (MorseHalfSpace m) (morseAttachedSpace hk c ε r δ hε hδ0 hδr hr) :=
      morseAttachedChartedSpace hk c ε r δ hε hδ0 hδr hr)
    (hcs₂ : ChartedSpace (MorseHalfSpace m) (morseUpperSublevel hk c r) :=
      morseUpperChartedSpace hk c r hr)
    (Ψ : @Diffeomorph ℝ _ (MorseModel (m + 1)) _ _ (MorseModel (m + 1)) _ _
      (MorseHalfSpace m) _ (MorseHalfSpace m) _ (morseModelWithCornersHalfSpace m)
      (morseModelWithCornersHalfSpace m)
      (morseAttachedSpace hk c ε r δ hε hδ0 hδr hr) _ hcs₁
      (morseUpperSublevel hk c r) _ hcs₂ (⊤ : ℕ∞)) : Prop := by
  letI : ChartedSpace (MorseHalfSpace m) (morseAttachedSpace hk c ε r δ hε hδ0 hδr hr) := hcs₁
  letI : ChartedSpace (MorseHalfSpace m) (morseUpperSublevel hk c r) := hcs₂
  exact
    (∀ a : morseLowerSublevel hk c ε,
      Ψ.toEquiv (DifferentialGeometry.Topology.adjunctionCell
        (i := fun a : morseLowerSublevel hk c ε => a)
        (morseHandleGlueMap hk c ε r δ hε hδ0 hδr hr) a) =
      (⟨a.1, morseLowerSublevel_mem_upper hk c ε r hε a⟩ : morseUpperSublevel hk c r)) ∧
    (∀ p : StandardHandle k (m + 1 - k),
      Ψ.toEquiv (morseHandleEmbeddingAttached hk c ε r δ hε hδ0 hδr hr p) =
      (⟨CellAttachment.modelHandleMap hk ε r p,
        CellAttachment.modelHandleMap_mem_upper hk c ε r hε p⟩ :
        morseUpperSublevel hk c r))

theorem morseHandleEmbeddingAttached_attaching {m k : ℕ} (hk : k ≤ m + 1) (c ε r δ : ℝ)
    (hε : 0 ≤ ε) (hδ0 : 0 < δ) (hδr : δ < r ^ 2) (hr : r ≠ 0)
    (p : AttachingRegion k (m + 1 - k)) :
    morseHandleEmbeddingAttached hk c ε r δ hε hδ0 hδr hr
        (attachingInclusion k (m + 1 - k) p) =
      DifferentialGeometry.Topology.adjunctionCell
        (i := fun a : morseLowerSublevel hk c ε => a)
        (morseHandleGlueMap hk c ε r δ hε hδ0 hδr hr)
        ⟨CellAttachment.modelHandleMap hk ε r (attachingInclusion k (m + 1 - k) p),
          by
            change CellAttachment.morseNormalForm hk c
              (CellAttachment.modelHandleMap hk ε r (cellBoundaryInclusion k p.1, p.2)) ≤ c - ε
            rw [CellAttachment.modelHandleMap_f_boundary hk c ε r hε p.1 p.2]⟩ := by
  dsimp [morseHandleEmbeddingAttached]
  apply Quot.sound
  refine ⟨(⟨CellAttachment.modelHandleMap hk ε r (attachingInclusion k (m + 1 - k) p), by
    change CellAttachment.morseNormalForm hk c
      (CellAttachment.modelHandleMap hk ε r (cellBoundaryInclusion k p.1, p.2)) ≤ c - ε
    rw [CellAttachment.modelHandleMap_f_boundary hk c ε r hε p.1 p.2]⟩ :
      morseLowerSublevel hk c ε), Or.inr ?_⟩
  constructor <;> rfl

theorem morse_smooth_handle_attachment_cell {m k : ℕ} (hk : k ≤ m + 1) (c ε r : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
    (I : ModelWithCorners ℝ (MorseModel (m + 1)) H) [I.Boundaryless]
    [IsManifold I (⊤ : WithTop ℕ∞) M] (f : M → ℝ)
    (data : MorseChart (m + 1) k hk c I f)
    (hε : 0 < ε) (hr : r ≠ 0) (hεr : Real.sqrt (2 * ε + 2 * r ^ 2) ≤ data.R)
    (hεr' : Real.sqrt (2 * ε + 2 * r ^ 2) < data.R')
    (hf : ContMDiff I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) f)
    (hreg : ∀ x : M, f x = c - ε → ¬ IsCriticalPointAt I f x)
    [NeZero k] [NeZero (m + 1 - k)] :
    ∃ φ : AttachingRegion k (m + 1 - k) → LevelSetSpace f (c - ε),
      @ContMDiff ℝ _
        (EuclideanSpace ℝ (Fin (k - 1)) × EuclideanSpace ℝ (Fin ((m + 1 - k - 1) + 1))) _ _
        (ModelProd (EuclideanSpace ℝ (Fin (k - 1))) (EuclideanHalfSpace ((m + 1 - k - 1) + 1))) _
        ((𝓡 (k - 1)).prod (modelWithCornersEuclideanHalfSpace ((m + 1 - k - 1) + 1)))
        (AttachingRegion k (m + 1 - k)) _ (attachingRegionChartedSpace k (m + 1 - k))
        (MorseModel m) _ _ (MorseModel m) _
        (𝓘(ℝ, MorseModel m)) (LevelSetSpace f (c - ε)) _
        (manifoldLevelSetChartedSpace I f (c - ε) hf hreg)
        (⊤ : ℕ∞)
        φ ∧
      Topology.IsClosedEmbedding φ ∧
      ∀ p : AttachingRegion k (m + 1 - k),
        (φ p).1 = (cocoreAttachingEmbedding hk c ε r data hε hεr p).1 := by
  refine ⟨cocoreAttachingEmbedding hk c ε r data hε hεr, ?_, ?_, ?_⟩
  · exact contMDiff_cocoreAttachingEmbedding hk c ε r data hε hεr hεr' hf hreg
  · exact isClosedEmbedding_cocoreAttachingEmbedding hk c ε r data hε hr hεr hεr' hf hreg
  · intro p
    rfl

noncomputable def morseAttachingEmbedding {m k : ℕ} (hk : k ≤ m + 1) (c ε r : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} {f : M → ℝ}
    (data : MorseChart (m + 1) k hk c I f)
    (hε : 0 < ε) (hεr : Real.sqrt (2 * ε + 2 * r ^ 2) ≤ data.R) :
    AttachingRegion k (m + 1 - k) → SublevelSpace f (c - ε) :=
  fun p => ⟨(cocoreAttachingEmbedding hk c ε r data hε hεr p).1,
    le_of_eq (cocoreAttachingEmbedding_value hk c ε r data hε hεr p)⟩

theorem morseAttachingEmbedding_value {m k : ℕ} (hk : k ≤ m + 1) (c ε r : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} {f : M → ℝ}
    (data : MorseChart (m + 1) k hk c I f)
    (hε : 0 < ε) (hεr : Real.sqrt (2 * ε + 2 * r ^ 2) ≤ data.R)
    (p : AttachingRegion k (m + 1 - k)) :
    f (morseAttachingEmbedding hk c ε r data hε hεr p).1 = c - ε := by
  dsimp [morseAttachingEmbedding]
  exact cocoreAttachingEmbedding_value hk c ε r data hε hεr p

theorem morseAttachingEmbedding_eq_handleEmbedding {m k : ℕ} (hk : k ≤ m + 1) (c ε r : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} {f : M → ℝ}
    (data : MorseChart (m + 1) k hk c I f)
    (hε : 0 < ε) (hεr : Real.sqrt (2 * ε + 2 * r ^ 2) ≤ data.R)
    (a : AttachingRegion k (m + 1 - k)) :
    (morseAttachingEmbedding hk c ε r data hε hεr a : M) =
      handleEmbedding hk c ε r data (attachingInclusion k (m + 1 - k) a) := by
  dsimp [morseAttachingEmbedding]
  exact (handleEmbedding_attachingRegion hk c ε r data hε hεr a).symm

theorem morseAttachingEmbedding_injective {m k : ℕ} (hk : k ≤ m + 1) (c ε r : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} {f : M → ℝ}
    (data : MorseChart (m + 1) k hk c I f)
    (hε : 0 < ε) (hr : r ≠ 0) (hεr : Real.sqrt (2 * ε + 2 * r ^ 2) ≤ data.R) :
    Function.Injective (morseAttachingEmbedding hk c ε r data hε hεr) := by
  intro p q h
  have h' : (cocoreAttachingEmbedding hk c ε r data hε hεr p).1 =
      (cocoreAttachingEmbedding hk c ε r data hε hεr q).1 := by
    change (morseAttachingEmbedding hk c ε r data hε hεr p).1 =
      (morseAttachingEmbedding hk c ε r data hε hεr q).1
    exact congrArg Subtype.val h
  exact cocoreAttachingEmbedding_injective hk c ε r data hε hr hεr (Subtype.ext h')

theorem contMDiff_morseAttachingEmbedding {m k : ℕ} (hk : k ≤ m + 1) (c ε r : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} [I.Boundaryless]
    [IsManifold I (⊤ : WithTop ℕ∞) M] {f : M → ℝ}
    (data : MorseChart (m + 1) k hk c I f)
    (hε : 0 < ε) (hεr : Real.sqrt (2 * ε + 2 * r ^ 2) ≤ data.R)
    (hεr' : Real.sqrt (2 * ε + 2 * r ^ 2) < data.R')
    (hf : ContMDiff I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) f)
    (hreg : ∀ x : M, f x = c - ε → ¬ IsCriticalPointAt I f x)
    [NeZero k] [NeZero (m + 1 - k)] :
    @ContMDiff ℝ _
      (EuclideanSpace ℝ (Fin (k - 1)) × EuclideanSpace ℝ (Fin ((m + 1 - k - 1) + 1))) _ _
      (ModelProd (EuclideanSpace ℝ (Fin (k - 1))) (EuclideanHalfSpace ((m + 1 - k - 1) + 1))) _
      ((𝓡 (k - 1)).prod (modelWithCornersEuclideanHalfSpace ((m + 1 - k - 1) + 1)))
      (AttachingRegion k (m + 1 - k)) _ (attachingRegionChartedSpace k (m + 1 - k))
      (MorseModel (m + 1)) _ _ (MorseHalfSpace m) _
      (morseModelWithCornersHalfSpace m) (SublevelSpace f (c - ε)) _
      (manifoldSublevelChartedSpace I f (c - ε) hf hreg)
      (⊤ : ℕ∞)
      (morseAttachingEmbedding hk c ε r data hε hεr) := by
  classical
  letI : ChartedSpace (MorseHalfSpace m) (SublevelSpace f (c - ε)) :=
    manifoldSublevelChartedSpace I f (c - ε) hf hreg
  letI : ChartedSpace (MorseModel m) (LevelSetSpace f (c - ε)) :=
    manifoldLevelSetChartedSpace I f (c - ε) hf hreg
  have hφ₀ : @ContMDiff ℝ _
      (EuclideanSpace ℝ (Fin (k - 1)) × EuclideanSpace ℝ (Fin ((m + 1 - k - 1) + 1))) _ _
      (ModelProd (EuclideanSpace ℝ (Fin (k - 1))) (EuclideanHalfSpace ((m + 1 - k - 1) + 1))) _
      ((𝓡 (k - 1)).prod (modelWithCornersEuclideanHalfSpace ((m + 1 - k - 1) + 1)))
      (AttachingRegion k (m + 1 - k)) _ (attachingRegionChartedSpace k (m + 1 - k))
      (MorseModel m) _ _ (MorseModel m) _
      (𝓘(ℝ, MorseModel m)) (LevelSetSpace f (c - ε)) _
      (manifoldLevelSetChartedSpace I f (c - ε) hf hreg)
      (⊤ : ℕ∞)
      (cocoreAttachingEmbedding hk c ε r data hε hεr) :=
    contMDiff_cocoreAttachingEmbedding hk c ε r data hε hεr hεr' hf hreg
  have hinc : ContMDiff (𝓘(ℝ, MorseModel m)) (morseModelWithCornersHalfSpace m)
      (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : LevelSetSpace f (c - ε) =>
        (⟨x.1, (le_of_eq x.2 : f x.1 ≤ c - ε)⟩ : SublevelSpace f (c - ε))) :=
    contMDiff_levelSetSublevelInclusion (I := I) f (c - ε) hf hreg
  have hcomp := hinc.comp hφ₀
  refine hcomp.congr ?_
  intro p
  apply Subtype.ext
  rfl

theorem isClosedEmbedding_morseAttachingEmbedding {m k : ℕ} (hk : k ≤ m + 1) (c ε r : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} [I.Boundaryless]
    [IsManifold I (⊤ : WithTop ℕ∞) M] [T2Space M] {f : M → ℝ}
    (data : MorseChart (m + 1) k hk c I f)
    (hε : 0 < ε) (hr : r ≠ 0) (hεr : Real.sqrt (2 * ε + 2 * r ^ 2) ≤ data.R)
    (hεr' : Real.sqrt (2 * ε + 2 * r ^ 2) < data.R')
    (hf : ContMDiff I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) f)
    (hreg : ∀ x : M, f x = c - ε → ¬ IsCriticalPointAt I f x)
    [NeZero k] [NeZero (m + 1 - k)] :
    Topology.IsClosedEmbedding (morseAttachingEmbedding hk c ε r data hε hεr) := by
  letI : ChartedSpace (MorseHalfSpace m) (SublevelSpace f (c - ε)) :=
    manifoldSublevelChartedSpace I f (c - ε) hf hreg
  exact (contMDiff_morseAttachingEmbedding hk c ε r data hε hεr hεr' hf hreg).continuous.isClosedEmbedding
    (morseAttachingEmbedding_injective hk c ε r data hε hr hεr)

structure MorseSmoothAttachingEmbedding {m k : ℕ} (hk : k ≤ m + 1) (c ε r : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} [I.Boundaryless]
    [IsManifold I (⊤ : WithTop ℕ∞) M] [T2Space M] {f : M → ℝ}
    (data : MorseChart (m + 1) k hk c I f)
    (hε : 0 < ε) (hεr : Real.sqrt (2 * ε + 2 * r ^ 2) ≤ data.R)
    (hεr' : Real.sqrt (2 * ε + 2 * r ^ 2) < data.R')
    (hf : ContMDiff I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) f)
    (hreg : ∀ x : M, f x = c - ε → ¬ IsCriticalPointAt I f x)
    [NeZero k] [NeZero (m + 1 - k)] where
  toFun : AttachingRegion k (m + 1 - k) → SublevelSpace f (c - ε)
  contMDiff : @ContMDiff ℝ _
    (EuclideanSpace ℝ (Fin (k - 1)) × EuclideanSpace ℝ (Fin ((m + 1 - k - 1) + 1))) _ _
    (ModelProd (EuclideanSpace ℝ (Fin (k - 1))) (EuclideanHalfSpace ((m + 1 - k - 1) + 1))) _
    ((𝓡 (k - 1)).prod (modelWithCornersEuclideanHalfSpace ((m + 1 - k - 1) + 1)))
    (AttachingRegion k (m + 1 - k)) _ (attachingRegionChartedSpace k (m + 1 - k))
    (MorseModel (m + 1)) _ _ (MorseHalfSpace m) _
    (morseModelWithCornersHalfSpace m) (SublevelSpace f (c - ε)) _
    (manifoldSublevelChartedSpace I f (c - ε) hf hreg)
    (⊤ : ℕ∞)
    toFun
  injective : Function.Injective toFun
  closedEmbedding : Topology.IsClosedEmbedding toFun
  boundary : ∀ p : AttachingRegion k (m + 1 - k), f (toFun p).1 = c - ε

noncomputable def morseSmoothAttachingEmbedding {m k : ℕ} (hk : k ≤ m + 1) (c ε r : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} [I.Boundaryless]
    [IsManifold I (⊤ : WithTop ℕ∞) M] [T2Space M] {f : M → ℝ}
    (data : MorseChart (m + 1) k hk c I f)
    (hε : 0 < ε) (hr : r ≠ 0) (hεr : Real.sqrt (2 * ε + 2 * r ^ 2) ≤ data.R)
    (hεr' : Real.sqrt (2 * ε + 2 * r ^ 2) < data.R')
    (hf : ContMDiff I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) f)
    (hreg : ∀ x : M, f x = c - ε → ¬ IsCriticalPointAt I f x)
    [NeZero k] [NeZero (m + 1 - k)] :
    MorseSmoothAttachingEmbedding hk c ε r data hε hεr hεr' hf hreg :=
  { toFun := morseAttachingEmbedding hk c ε r data hε hεr
    contMDiff := contMDiff_morseAttachingEmbedding hk c ε r data hε hεr hεr' hf hreg
    injective := morseAttachingEmbedding_injective hk c ε r data hε hr hεr
    closedEmbedding := isClosedEmbedding_morseAttachingEmbedding hk c ε r data hε hr hεr hεr' hf hreg
    boundary := morseAttachingEmbedding_value hk c ε r data hε hεr }

noncomputable def morseHandleAdjunctionHomeoUnion {m k : ℕ} (hk : k ≤ m + 1) (c ε r : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} {f : M → ℝ}
    (data : MorseChart (m + 1) k hk c I f)
    (hε : 0 < ε) (hr : r ≠ 0) (hεr : Real.sqrt (2 * ε + 2 * r ^ 2) ≤ data.R)
    (hcont : Continuous f) :
    Handle.AdjunctionSpace k (m + 1 - k) (morseAttachingEmbedding hk c ε r data hε hεr) ≃ₜ
      {x : M // x ∈ sublevel f (c - ε) ∪ Set.range (handleEmbedding hk c ε r data)} :=
  Handle.adjunctionHomeomorphUnionImage
    (φ := morseAttachingEmbedding hk c ε r data hε hεr)
    (c := handleEmbedding hk c ε r data)
    (morseAttachingEmbedding_eq_handleEmbedding hk c ε r data hε hεr)
    (handleEmbedding_injective hk c ε r data hε hr hεr)
    (handleEmbedding_continuous hk c ε r data hε hεr)
    (by
      rw [Set.disjoint_left]
      intro y hys hyt
      rcases hys with ⟨p, hp, hpy⟩
      have hiff := (handleEmbedding_mem_lower_iff hk c ε r data hε hεr p).mp (by
        simpa [hpy] using hyt)
      have hreg : p ∈ attachingRegion k (m + 1 - k) := by
        dsimp [attachingRegion]
        exact hiff
      exact hp.2 hreg)
    (by
      exact isClosed_Iic.preimage hcont)

theorem morseHandleAdjunctionHomeoUnion_lower {m k : ℕ} (hk : k ≤ m + 1) (c ε r : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} {f : M → ℝ}
    (data : MorseChart (m + 1) k hk c I f)
    (hε : 0 < ε) (hr : r ≠ 0) (hεr : Real.sqrt (2 * ε + 2 * r ^ 2) ≤ data.R)
    (hcont : Continuous f) (x : SublevelSpace f (c - ε)) :
    morseHandleAdjunctionHomeoUnion hk c ε r data hε hr hεr hcont
      (Handle.lower (morseAttachingEmbedding hk c ε r data hε hεr) x) =
      ⟨x.1, Or.inl x.2⟩ := by
  exact Handle.adjunctionHomeomorphUnionImage_lower
    (φ := morseAttachingEmbedding hk c ε r data hε hεr)
    (c := handleEmbedding hk c ε r data)
    (morseAttachingEmbedding_eq_handleEmbedding hk c ε r data hε hεr)
    (handleEmbedding_injective hk c ε r data hε hr hεr)
    (handleEmbedding_continuous hk c ε r data hε hεr)
    (by
      rw [Set.disjoint_left]
      intro y hys hyt
      rcases hys with ⟨p, hp, hpy⟩
      have hiff := (handleEmbedding_mem_lower_iff hk c ε r data hε hεr p).mp (by
        simpa [hpy] using hyt)
      have hreg : p ∈ attachingRegion k (m + 1 - k) := by
        dsimp [attachingRegion]
        exact hiff
      exact hp.2 hreg)
    (by
      exact isClosed_Iic.preimage hcont) x

noncomputable def morseBeltLowerSet {m k : ℕ} (hk : k ≤ m + 1) (c ε : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} {f : M → ℝ}
    (data : MorseChart (m + 1) k hk c I f) : Set (SublevelSpace f (c - ε)) :=
  {x | x.1 ∈ data.χ '' {y : MorseModel (m + 1) | morseNorm (m + 1) y < data.R}}

noncomputable def morseBeltSumSet {m k : ℕ} (hk : k ≤ m + 1) (c ε : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} {f : M → ℝ}
    (data : MorseChart (m + 1) k hk c I f) :
    Set (StandardHandle k (m + 1 - k) ⊕ SublevelSpace f (c - ε)) :=
  (Sum.inl '' Set.univ : Set (StandardHandle k (m + 1 - k) ⊕ SublevelSpace f (c - ε))) ∪
    Sum.inr '' morseBeltLowerSet hk c ε data

noncomputable def morseBeltSet {m k : ℕ} (hk : k ≤ m + 1) (c ε r : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} {f : M → ℝ}
    (data : MorseChart (m + 1) k hk c I f)
    (hε : 0 < ε) (hεr : Real.sqrt (2 * ε + 2 * r ^ 2) ≤ data.R) :
    Set (Handle.AdjunctionSpace k (m + 1 - k) (morseAttachingEmbedding hk c ε r data hε hεr)) :=
  (Handle.lower (morseAttachingEmbedding hk c ε r data hε hεr)) '' morseBeltLowerSet hk c ε data ∪
    (Handle.cell (morseAttachingEmbedding hk c ε r data hε hεr)) '' Set.univ

private theorem morseAttachingEmbedding_mem_lowerBelt {m k : ℕ} (hk : k ≤ m + 1) (c ε r : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} {f : M → ℝ}
    (data : MorseChart (m + 1) k hk c I f)
    (hε : 0 < ε) (hεr' : Real.sqrt (2 * ε + 2 * r ^ 2) < data.R)
    (p : AttachingRegion k (m + 1 - k)) :
    morseAttachingEmbedding hk c ε r data hε (le_of_lt hεr') p ∈ morseBeltLowerSet hk c ε data := by
  dsimp [morseBeltLowerSet]
  refine ⟨cocoreModelPoint hk ε r p, ?_, ?_⟩
  · exact lt_of_le_of_lt (cocoreModelPoint_norm_le hk ε r (le_of_lt hε) p) hεr'
  · change data.χ (cocoreModelPoint hk ε r p) =
      (morseAttachingEmbedding hk c ε r data hε (le_of_lt hεr') p).1
    rfl

private theorem morseBeltLowerMap_mem {m k : ℕ} (hk : k ≤ m + 1) (c ε r : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} {f : M → ℝ}
    (data : MorseChart (m + 1) k hk c I f)
    (hε : 0 < ε)
    (x : SublevelSpace f (c - ε)) (hx : x ∈ morseBeltLowerSet hk c ε data) :
    morseNormalForm hk c (data.χ.symm x.1) ≤ c + r ^ 2 / 2 := by
  rcases hx with ⟨y, hy, hxy⟩
  have hsrc : y ∈ data.χ.source := data.hχsrc y (le_of_lt hy)
  have hsymm : data.χ.symm x.1 = y := by
    rw [← hxy]
    exact data.χ.left_inv hsrc
  rw [hsymm]
  have hf : f (data.χ y) = morseNormalForm hk c y := data.hnorm y (le_of_lt hy)
  have hle : morseNormalForm hk c y ≤ c - ε := by
    rw [← hf]
    rw [hxy]
    exact x.2
  have hr2 : 0 ≤ r ^ 2 := sq_nonneg r
  nlinarith

theorem isOpen_chiBallImage {n : ℕ} {M : Type} [TopologicalSpace M]
    (χ : OpenPartialHomeomorph (MorseModel n) M) (R : ℝ)
    (hsrc : ∀ y : MorseModel n, morseNorm n y < R → y ∈ χ.source) :
    IsOpen (χ '' {y : MorseModel n | morseNorm n y < R}) := by
  have hnorm : Continuous (fun y : MorseModel n => morseNorm n y) := by
    dsimp [morseNorm]
    exact continuous_norm.comp (PiLp.continuous_toLp (p := (2 : ENNReal)) (β := fun _ : Fin n => ℝ))
  let U : Set (MorseModel n) := {y : MorseModel n | morseNorm n y < R}
  have hU : IsOpen U := isOpen_lt hnorm continuous_const
  rw [isOpen_iff_mem_nhds]
  intro y hy
  rcases hy with ⟨x, hx, rfl⟩
  have hxsrc : x ∈ χ.source := hsrc x hx
  have hmem : χ.symm (χ x) ∈ U := by
    have hl := χ.left_inv hxsrc
    simpa [U, hl] using hx
  have hcontAt : ContinuousAt χ.symm (χ x) := by
    have hw : ContinuousWithinAt χ.symm χ.target (χ x) :=
      χ.continuousOn_invFun (χ x) (χ.map_source hxsrc)
    exact hw.continuousAt (IsOpen.mem_nhds χ.open_target (χ.map_source hxsrc))
  have hpre : χ.symm ⁻¹' U ∈ nhds (χ x) :=
    hcontAt.preimage_mem_nhds (IsOpen.mem_nhds hU hmem)
  refine Filter.mem_of_superset (Filter.inter_mem hpre (IsOpen.mem_nhds χ.open_target (χ.map_source hxsrc))) ?_
  intro w hw
  rcases hw with ⟨hwsymm, hwtgt⟩
  exact ⟨χ.symm w, hwsymm, χ.right_inv hwtgt⟩

theorem isOpen_morseBeltLowerSet {m k : ℕ} (hk : k ≤ m + 1) (c ε : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} {f : M → ℝ}
    (data : MorseChart (m + 1) k hk c I f) :
    IsOpen (morseBeltLowerSet hk c ε data) := by
  have hUopen : IsOpen (data.χ '' {y : MorseModel (m + 1) | morseNorm (m + 1) y < data.R}) :=
    isOpen_chiBallImage data.χ data.R (fun y hy => data.hχsrc y (le_of_lt hy))
  change IsOpen {x : SublevelSpace f (c - ε) | x.1 ∈
    data.χ '' {y : MorseModel (m + 1) | morseNorm (m + 1) y < data.R}}
  exact continuous_subtype_val.isOpen_preimage
    (data.χ '' {y : MorseModel (m + 1) | morseNorm (m + 1) y < data.R}) hUopen

theorem isOpen_morseBeltCellSet {m k : ℕ} (hk : k ≤ m + 1) (c ε r : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} {f : M → ℝ}
    (data : MorseChart (m + 1) k hk c I f) :
    IsOpen {d : StandardHandle k (m + 1 - k) |
      morseNorm (m + 1) (modelHandleMap hk ε r d) < data.R} := by
  have hnorm : Continuous (fun y : MorseModel (m + 1) => morseNorm (m + 1) y) := by
    dsimp [morseNorm]
    exact continuous_norm.comp (PiLp.continuous_toLp (p := (2 : ENNReal)) (β := fun _ : Fin (m + 1) => ℝ))
  have hpre : IsOpen {d : StandardHandle k (m + 1 - k) |
      morseNorm (m + 1) (modelHandleMap hk ε r d) < data.R} :=
    (isOpen_lt hnorm continuous_const).preimage (continuous_modelHandleMap hk ε r)
  exact hpre

noncomputable def morseBeltOpenSet {m k : ℕ} (hk : k ≤ m + 1) (c ε r : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} {f : M → ℝ}
    (data : MorseChart (m + 1) k hk c I f)
    (hε : 0 < ε) (hεr : Real.sqrt (2 * ε + 2 * r ^ 2) ≤ data.R) :
    Set (Handle.AdjunctionSpace k (m + 1 - k) (morseAttachingEmbedding hk c ε r data hε hεr)) :=
  (Handle.lower (morseAttachingEmbedding hk c ε r data hε hεr)) '' morseBeltLowerSet hk c ε data ∪
    (Handle.cell (morseAttachingEmbedding hk c ε r data hε hεr)) ''
      {d : StandardHandle k (m + 1 - k) | morseNorm (m + 1) (modelHandleMap hk ε r d) < data.R}

private theorem morseBeltAtt_in_cell {m k : ℕ} (hk : k ≤ m + 1) (c ε r : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} {f : M → ℝ}
    (data : MorseChart (m + 1) k hk c I f)
    (hε : 0 < ε) (hεr : Real.sqrt (2 * ε + 2 * r ^ 2) ≤ data.R)
    (a : AttachingRegion k (m + 1 - k))
    (ha : morseAttachingEmbedding hk c ε r data hε hεr a ∈ morseBeltLowerSet hk c ε data) :
    morseNorm (m + 1) (modelHandleMap hk ε r (attachingInclusion k (m + 1 - k) a)) < data.R := by
  dsimp [morseBeltLowerSet] at ha
  rcases ha with ⟨y, hy, hxy⟩
  have hφ : (morseAttachingEmbedding hk c ε r data hε hεr a).1 =
      data.χ (modelHandleMap hk ε r (attachingInclusion k (m + 1 - k) a)) := by
    exact morseAttachingEmbedding_eq_handleEmbedding hk c ε r data hε hεr a
  have hχ : data.χ y = data.χ (modelHandleMap hk ε r (attachingInclusion k (m + 1 - k) a)) := by
    rw [hxy, hφ]
  have hy' : y = modelHandleMap hk ε r (attachingInclusion k (m + 1 - k) a) := by
    apply data.χ.injOn
    · exact data.hχsrc y (le_of_lt hy)
    · exact data.hχsrc (modelHandleMap hk ε r (attachingInclusion k (m + 1 - k) a))
        (le_trans (modelHandleMap_norm_le hk ε r (le_of_lt hε) (attachingInclusion k (m + 1 - k) a)) hεr)
    · exact hχ
  rw [← hy']
  exact hy

private theorem morseBeltCell_in_lower {m k : ℕ} (hk : k ≤ m + 1) (c ε r : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} {f : M → ℝ}
    (data : MorseChart (m + 1) k hk c I f)
    (hε : 0 < ε) (hεr : Real.sqrt (2 * ε + 2 * r ^ 2) ≤ data.R)
    (a : AttachingRegion k (m + 1 - k))
    (ha : morseNorm (m + 1) (modelHandleMap hk ε r (attachingInclusion k (m + 1 - k) a)) < data.R) :
    morseAttachingEmbedding hk c ε r data hε hεr a ∈ morseBeltLowerSet hk c ε data := by
  dsimp [morseBeltLowerSet]
  refine ⟨modelHandleMap hk ε r (attachingInclusion k (m + 1 - k) a), ha, ?_⟩
  exact (morseAttachingEmbedding_eq_handleEmbedding hk c ε r data hε hεr a).symm

private theorem morseBeltEqvGen_mem {m k : ℕ} (hk : k ≤ m + 1) (c ε r : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} {f : M → ℝ}
    (data : MorseChart (m + 1) k hk c I f)
    (hε : 0 < ε) (hεr : Real.sqrt (2 * ε + 2 * r ^ 2) ≤ data.R)
    (s z : StandardHandle k (m + 1 - k) ⊕ SublevelSpace f (c - ε))
    (h : Relation.EqvGen (DifferentialGeometry.Topology.adjunctionRel (attachingInclusion k (m + 1 - k))
      (morseAttachingEmbedding hk c ε r data hε hεr)) s z) :
    (s ∈ (Sum.inr '' morseBeltLowerSet hk c ε data : Set
      (StandardHandle k (m + 1 - k) ⊕ SublevelSpace f (c - ε))) ∪
        Sum.inl '' {d : StandardHandle k (m + 1 - k) |
          morseNorm (m + 1) (modelHandleMap hk ε r d) < data.R}) ↔
      (z ∈ (Sum.inr '' morseBeltLowerSet hk c ε data : Set
        (StandardHandle k (m + 1 - k) ⊕ SublevelSpace f (c - ε))) ∪
          Sum.inl '' {d : StandardHandle k (m + 1 - k) |
            morseNorm (m + 1) (modelHandleMap hk ε r d) < data.R}) := by
  let A : Set (StandardHandle k (m + 1 - k) ⊕ SublevelSpace f (c - ε)) :=
    (Sum.inr '' morseBeltLowerSet hk c ε data : Set
      (StandardHandle k (m + 1 - k) ⊕ SublevelSpace f (c - ε))) ∪
      Sum.inl '' {d : StandardHandle k (m + 1 - k) |
        morseNorm (m + 1) (modelHandleMap hk ε r d) < data.R}
  change s ∈ A ↔ z ∈ A
  have hrel : ∀ x y : StandardHandle k (m + 1 - k) ⊕ SublevelSpace f (c - ε),
      DifferentialGeometry.Topology.adjunctionRel (attachingInclusion k (m + 1 - k))
        (morseAttachingEmbedding hk c ε r data hε hεr) x y → (x ∈ A ↔ y ∈ A) := by
    intro x y hxy
    rcases hxy with ⟨a, ha | ha⟩
    · rcases ha with ⟨hx, hy⟩
      have hxAmem : x ∈ A ↔
          morseNorm (m + 1) (modelHandleMap hk ε r (attachingInclusion k (m + 1 - k) a)) < data.R := by
        rw [hx]
        simp [A]
      have hyAmem : y ∈ A ↔
          morseAttachingEmbedding hk c ε r data hε hεr a ∈ morseBeltLowerSet hk c ε data := by
        rw [hy]
        simp [A]
      have hiffVW : (morseNorm (m + 1) (modelHandleMap hk ε r (attachingInclusion k (m + 1 - k) a)) < data.R) ↔
          morseAttachingEmbedding hk c ε r data hε hεr a ∈ morseBeltLowerSet hk c ε data := by
        constructor
        · intro hV
          exact morseBeltCell_in_lower hk c ε r data hε hεr a hV
        · intro hW
          exact morseBeltAtt_in_cell hk c ε r data hε hεr a hW
      exact hxAmem.trans (hiffVW.trans hyAmem.symm)
    · rcases ha with ⟨hy, hx⟩
      have hxAmem : x ∈ A ↔
          morseAttachingEmbedding hk c ε r data hε hεr a ∈ morseBeltLowerSet hk c ε data := by
        rw [hx]
        simp [A]
      have hyAmem : y ∈ A ↔
          morseNorm (m + 1) (modelHandleMap hk ε r (attachingInclusion k (m + 1 - k) a)) < data.R := by
        rw [hy]
        simp [A]
      have hiffVW : (morseNorm (m + 1) (modelHandleMap hk ε r (attachingInclusion k (m + 1 - k) a)) < data.R) ↔
          morseAttachingEmbedding hk c ε r data hε hεr a ∈ morseBeltLowerSet hk c ε data := by
        constructor
        · intro hV
          exact morseBeltCell_in_lower hk c ε r data hε hεr a hV
        · intro hW
          exact morseBeltAtt_in_cell hk c ε r data hε hεr a hW
      exact hxAmem.trans (hiffVW.symm.trans hyAmem.symm)
  exact Relation.EqvGen.recOn (motive := fun a b _ => a ∈ A ↔ b ∈ A) h
    (rel := fun x y hxy => hrel x y hxy)
    (refl := fun x => Iff.rfl)
    (symm := fun x y hxy h => h.symm)
    (trans := fun x y z hxy hyz h1 h2 => h1.trans h2)

theorem isOpen_morseBeltOpenSet {m k : ℕ} (hk : k ≤ m + 1) (c ε r : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} {f : M → ℝ}
    (data : MorseChart (m + 1) k hk c I f)
    (hε : 0 < ε) (hεr : Real.sqrt (2 * ε + 2 * r ^ 2) ≤ data.R) :
    IsOpen (morseBeltOpenSet hk c ε r data hε hεr) := by
  let A : Set (StandardHandle k (m + 1 - k) ⊕ SublevelSpace f (c - ε)) :=
    (Sum.inr '' morseBeltLowerSet hk c ε data : Set
      (StandardHandle k (m + 1 - k) ⊕ SublevelSpace f (c - ε))) ∪
      Sum.inl '' {d : StandardHandle k (m + 1 - k) |
        morseNorm (m + 1) (modelHandleMap hk ε r d) < data.R}
  have hS : morseBeltOpenSet hk c ε r data hε hεr =
      (fun z : StandardHandle k (m + 1 - k) ⊕ SublevelSpace f (c - ε) =>
        DifferentialGeometry.Topology.adjunctionMk (attachingInclusion k (m + 1 - k))
          (morseAttachingEmbedding hk c ε r data hε hεr) z) '' A := by
    dsimp [morseBeltOpenSet, A, Handle.lower, adjunctionLower, Handle.cell, adjunctionCell]
    rw [Set.image_union, Set.image_image, Set.image_image]
    rfl
  have hpre : (fun s : StandardHandle k (m + 1 - k) ⊕ SublevelSpace f (c - ε) =>
      DifferentialGeometry.Topology.adjunctionMk (attachingInclusion k (m + 1 - k))
        (morseAttachingEmbedding hk c ε r data hε hεr) s) ⁻¹'
      morseBeltOpenSet hk c ε r data hε hεr = A := by
    ext s
    constructor
    · intro hs
      rcases (by simpa [hS] using hs : ∃ z ∈ A,
        DifferentialGeometry.Topology.adjunctionMk (attachingInclusion k (m + 1 - k))
          (morseAttachingEmbedding hk c ε r data hε hεr) z =
          DifferentialGeometry.Topology.adjunctionMk (attachingInclusion k (m + 1 - k))
            (morseAttachingEmbedding hk c ε r data hε hεr) s) with ⟨z, hz, hsz⟩
      have hgen : Relation.EqvGen (DifferentialGeometry.Topology.adjunctionRel
          (attachingInclusion k (m + 1 - k))
          (morseAttachingEmbedding hk c ε r data hε hεr)) s z := Quot.eq.mp hsz.symm
      exact (morseBeltEqvGen_mem hk c ε r data hε hεr s z hgen).mpr hz
    · intro hs
      rcases hs with hs | hs
      · rcases hs with ⟨x, hx, rfl⟩
        change DifferentialGeometry.Topology.adjunctionMk (attachingInclusion k (m + 1 - k))
          (morseAttachingEmbedding hk c ε r data hε hεr) (Sum.inr x) ∈
          morseBeltOpenSet hk c ε r data hε hεr
        dsimp [morseBeltOpenSet]
        exact Or.inl ⟨x, hx, rfl⟩
      · rcases hs with ⟨d, hd, rfl⟩
        change DifferentialGeometry.Topology.adjunctionMk (attachingInclusion k (m + 1 - k))
          (morseAttachingEmbedding hk c ε r data hε hεr) (Sum.inl d) ∈
          morseBeltOpenSet hk c ε r data hε hεr
        dsimp [morseBeltOpenSet]
        exact Or.inr ⟨d, hd, rfl⟩
  have hq : Topology.IsQuotientMap (fun s : StandardHandle k (m + 1 - k) ⊕ SublevelSpace f (c - ε) =>
      DifferentialGeometry.Topology.adjunctionMk (attachingInclusion k (m + 1 - k))
        (morseAttachingEmbedding hk c ε r data hε hεr) s) :=
    isQuotientMap_adjunctionMk (attachingInclusion k (m + 1 - k))
      (morseAttachingEmbedding hk c ε r data hε hεr)
  rw [← hq.isOpen_preimage]
  rw [hpre]
  have hW : IsOpen (Sum.inr '' morseBeltLowerSet hk c ε data : Set
      (StandardHandle k (m + 1 - k) ⊕ SublevelSpace f (c - ε))) := by
    rw [isOpen_sum_iff]
    constructor
    · have heq : Sum.inl ⁻¹' (Sum.inr '' morseBeltLowerSet hk c ε data : Set
          (StandardHandle k (m + 1 - k) ⊕ SublevelSpace f (c - ε))) = ∅ := by
        ext x
        constructor
        · intro hx
          rcases hx with ⟨y, hy, hxy⟩
          cases hxy
        · intro hx
          exact False.elim hx
      rw [heq]
      exact isOpen_empty
    · have heq : Sum.inr ⁻¹' (Sum.inr '' morseBeltLowerSet hk c ε data : Set
          (StandardHandle k (m + 1 - k) ⊕ SublevelSpace f (c - ε))) =
          morseBeltLowerSet hk c ε data := by
        ext x
        constructor
        · intro hx
          rcases hx with ⟨y, hy, hxy⟩
          have hy' : y = x := Sum.inr.inj hxy
          simpa [hy'] using hy
        · intro hx
          exact ⟨x, hx, rfl⟩
      rw [heq]
      exact isOpen_morseBeltLowerSet hk c ε data
  have hV : IsOpen (Sum.inl '' {d : StandardHandle k (m + 1 - k) |
      morseNorm (m + 1) (modelHandleMap hk ε r d) < data.R} : Set
      (StandardHandle k (m + 1 - k) ⊕ SublevelSpace f (c - ε))) := by
    rw [isOpen_sum_iff]
    constructor
    · have heq : Sum.inl ⁻¹' (Sum.inl '' {d : StandardHandle k (m + 1 - k) |
          morseNorm (m + 1) (modelHandleMap hk ε r d) < data.R} : Set
          (StandardHandle k (m + 1 - k) ⊕ SublevelSpace f (c - ε))) =
          {d : StandardHandle k (m + 1 - k) |
            morseNorm (m + 1) (modelHandleMap hk ε r d) < data.R} := by
        ext x
        constructor
        · intro hx
          rcases hx with ⟨y, hy, hxy⟩
          have hy' : y = x := Sum.inl.inj hxy
          simpa [hy'] using hy
        · intro hx
          exact ⟨x, hx, rfl⟩
      rw [heq]
      exact isOpen_morseBeltCellSet hk c ε r data
    · have heq : Sum.inr ⁻¹' (Sum.inl '' {d : StandardHandle k (m + 1 - k) |
          morseNorm (m + 1) (modelHandleMap hk ε r d) < data.R} : Set
          (StandardHandle k (m + 1 - k) ⊕ SublevelSpace f (c - ε))) = ∅ := by
        ext x
        constructor
        · intro hx
          rcases hx with ⟨y, hy, hxy⟩
          cases hxy
        · intro hx
          exact False.elim hx
      rw [heq]
      exact isOpen_empty
  exact IsOpen.union hW hV

theorem morseBeltOpenSet_subset_beltSet {m k : ℕ} (hk : k ≤ m + 1) (c ε r : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} {f : M → ℝ}
    (data : MorseChart (m + 1) k hk c I f)
    (hε : 0 < ε) (hεr : Real.sqrt (2 * ε + 2 * r ^ 2) ≤ data.R) :
    morseBeltOpenSet hk c ε r data hε hεr ⊆ morseBeltSet hk c ε r data hε hεr := by
  intro z hz
  rcases hz with hz | hz
  · rcases hz with ⟨x, hx, rfl⟩
    exact Or.inl ⟨x, hx, rfl⟩
  · rcases hz with ⟨d, hd, rfl⟩
    exact Or.inr ⟨d, trivial, rfl⟩

noncomputable def morseBeltMap {m k : ℕ} (hk : k ≤ m + 1) (c ε r : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} {f : M → ℝ}
    (data : MorseChart (m + 1) k hk c I f)
    (hε : 0 < ε) (hεr' : Real.sqrt (2 * ε + 2 * r ^ 2) < data.R)
    (z : {z' : Handle.AdjunctionSpace k (m + 1 - k)
      (morseAttachingEmbedding hk c ε r data hε (le_of_lt hεr')) // z' ∈ morseBeltSet hk c ε r data hε (le_of_lt hεr')}) :
    morseUpperSublevel hk c r :=
  by
  classical
  exact Quot.liftOn z.1
    (fun s : StandardHandle k (m + 1 - k) ⊕ SublevelSpace f (c - ε) =>
      match s with
      | Sum.inl d =>
          (⟨modelHandleMap hk ε r d, modelHandleMap_mem_upper hk c ε r (le_of_lt hε) d⟩ :
            morseUpperSublevel hk c r)
      | Sum.inr x =>
          if hx : x ∈ morseBeltLowerSet hk c ε data then
            (⟨data.χ.symm x.1, morseBeltLowerMap_mem hk c ε r data hε x hx⟩ :
              morseUpperSublevel hk c r)
          else
            (⟨0, by
              change morseNormalForm hk c 0 ≤ c + r ^ 2 / 2
              have h0 : morseNormalForm hk c 0 = c := by
                dsimp [morseNormalForm]
                simp
              rw [h0]
              have hr2 : 0 ≤ r ^ 2 := sq_nonneg r
              nlinarith⟩ : morseUpperSublevel hk c r))
    (by
      intro a b hab
      rcases hab with ⟨p, hp | hp⟩
      · rcases hp with ⟨ha, hb⟩
        subst a
        subst b
        have hsymm : data.χ.symm (morseAttachingEmbedding hk c ε r data hε (le_of_lt hεr') p).1 =
            modelHandleMap hk ε r (attachingInclusion k (m + 1 - k) p) := by
          have hb' : (morseAttachingEmbedding hk c ε r data hε (le_of_lt hεr') p).1 ∈
              data.χ '' {y : MorseModel (m + 1) | morseNorm (m + 1) y ≤ data.R} := by
            refine ⟨cocoreModelPoint hk ε r p, ?_, ?_⟩
            · exact le_trans (cocoreModelPoint_norm_le hk ε r (le_of_lt hε) p) (le_of_lt hεr')
            · change data.χ (cocoreModelPoint hk ε r p) =
                (morseAttachingEmbedding hk c ε r data hε (le_of_lt hεr') p).1
              rfl
          rcases hb' with ⟨y, hy, hxy⟩
          have hsrc : y ∈ data.χ.source := data.hχsrc y hy
          have hsymm' : data.χ.symm (morseAttachingEmbedding hk c ε r data hε (le_of_lt hεr') p).1 = y := by
            calc
              data.χ.symm (morseAttachingEmbedding hk c ε r data hε (le_of_lt hεr') p).1 =
                  data.χ.symm (data.χ y) := by
                congr 1
                exact hxy.symm
              _ = y := data.χ.left_inv hsrc
          have hmain : y = modelHandleMap hk ε r (attachingInclusion k (m + 1 - k) p) := by
            apply data.χ.injOn hsrc
            · exact data.hχsrc (modelHandleMap hk ε r (attachingInclusion k (m + 1 - k) p))
                (le_trans (modelHandleMap_norm_le hk ε r (le_of_lt hε)
                  (attachingInclusion k (m + 1 - k) p)) (le_of_lt hεr'))
            · calc
                data.χ y = (morseAttachingEmbedding hk c ε r data hε (le_of_lt hεr') p).1 := by
                  exact hxy
                _ = data.χ (modelHandleMap hk ε r (attachingInclusion k (m + 1 - k) p)) := by
                  exact morseAttachingEmbedding_eq_handleEmbedding hk c ε r data hε (le_of_lt hεr') p
          rw [hsymm', hmain]
        apply Subtype.ext
        dsimp
        have hpφ : morseAttachingEmbedding hk c ε r data hε (le_of_lt hεr') p ∈
            morseBeltLowerSet hk c ε data :=
          morseAttachingEmbedding_mem_lowerBelt hk c ε r data hε hεr' p
        simp [hpφ]
        simpa using hsymm.symm
      · rcases hp with ⟨hb, ha⟩
        subst a
        subst b
        have hsymm : data.χ.symm (morseAttachingEmbedding hk c ε r data hε (le_of_lt hεr') p).1 =
            modelHandleMap hk ε r (attachingInclusion k (m + 1 - k) p) := by
          have hb' : (morseAttachingEmbedding hk c ε r data hε (le_of_lt hεr') p).1 ∈
              data.χ '' {y : MorseModel (m + 1) | morseNorm (m + 1) y ≤ data.R} := by
            refine ⟨cocoreModelPoint hk ε r p, ?_, ?_⟩
            · exact le_trans (cocoreModelPoint_norm_le hk ε r (le_of_lt hε) p) (le_of_lt hεr')
            · change data.χ (cocoreModelPoint hk ε r p) =
                (morseAttachingEmbedding hk c ε r data hε (le_of_lt hεr') p).1
              rfl
          rcases hb' with ⟨y, hy, hxy⟩
          have hsrc : y ∈ data.χ.source := data.hχsrc y hy
          have hsymm' : data.χ.symm (morseAttachingEmbedding hk c ε r data hε (le_of_lt hεr') p).1 = y := by
            calc
              data.χ.symm (morseAttachingEmbedding hk c ε r data hε (le_of_lt hεr') p).1 =
                  data.χ.symm (data.χ y) := by
                congr 1
                exact hxy.symm
              _ = y := data.χ.left_inv hsrc
          have hmain : y = modelHandleMap hk ε r (attachingInclusion k (m + 1 - k) p) := by
            apply data.χ.injOn hsrc
            · exact data.hχsrc (modelHandleMap hk ε r (attachingInclusion k (m + 1 - k) p))
                (le_trans (modelHandleMap_norm_le hk ε r (le_of_lt hε)
                  (attachingInclusion k (m + 1 - k) p)) (le_of_lt hεr'))
            · calc
                data.χ y = (morseAttachingEmbedding hk c ε r data hε (le_of_lt hεr') p).1 := by
                  exact hxy
                _ = data.χ (modelHandleMap hk ε r (attachingInclusion k (m + 1 - k) p)) := by
                  exact morseAttachingEmbedding_eq_handleEmbedding hk c ε r data hε (le_of_lt hεr') p
          rw [hsymm', hmain]
        apply Subtype.ext
        dsimp
        have hpφ : morseAttachingEmbedding hk c ε r data hε (le_of_lt hεr') p ∈
            morseBeltLowerSet hk c ε data :=
          morseAttachingEmbedding_mem_lowerBelt hk c ε r data hε hεr' p
        simp [hpφ]
        simpa using hsymm)

theorem morseBeltMap_cell {m k : ℕ} (hk : k ≤ m + 1) (c ε r : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} {f : M → ℝ}
    (data : MorseChart (m + 1) k hk c I f)
    (hε : 0 < ε) (hεr' : Real.sqrt (2 * ε + 2 * r ^ 2) < data.R)
    (d : StandardHandle k (m + 1 - k)) :
    (morseBeltMap hk c ε r data hε hεr'
      ⟨Handle.cell (morseAttachingEmbedding hk c ε r data hε (le_of_lt hεr')) d,
        Or.inr ⟨d, trivial, rfl⟩⟩ : MorseModel (m + 1)) =
      modelHandleMap hk ε r d := by
  dsimp [morseBeltMap]
  rfl

theorem morseBeltMap_lower {m k : ℕ} (hk : k ≤ m + 1) (c ε r : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} {f : M → ℝ}
    (data : MorseChart (m + 1) k hk c I f)
    (hε : 0 < ε) (hεr' : Real.sqrt (2 * ε + 2 * r ^ 2) < data.R)
    (x : SublevelSpace f (c - ε)) (hx : x ∈ morseBeltLowerSet hk c ε data) :
    (morseBeltMap hk c ε r data hε hεr'
      ⟨Handle.lower (morseAttachingEmbedding hk c ε r data hε (le_of_lt hεr')) x,
        Or.inl ⟨x, hx, rfl⟩⟩ : MorseModel (m + 1)) =
      data.χ.symm x.1 := by
  dsimp [morseBeltMap, Handle.lower, adjunctionLower, adjunctionMk, Quot.liftOn]
  simp [hx]

noncomputable def morseBeltMapOnOpen {m k : ℕ} (hk : k ≤ m + 1) (c ε r : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} {f : M → ℝ}
    (data : MorseChart (m + 1) k hk c I f)
    (hε : 0 < ε) (hεr' : Real.sqrt (2 * ε + 2 * r ^ 2) < data.R)
    (z : {z' : Handle.AdjunctionSpace k (m + 1 - k)
      (morseAttachingEmbedding hk c ε r data hε (le_of_lt hεr')) //
        z' ∈ morseBeltOpenSet hk c ε r data hε (le_of_lt hεr')}) :
    morseUpperSublevel hk c r :=
  morseBeltMap hk c ε r data hε hεr' ⟨z.1,
    morseBeltOpenSet_subset_beltSet hk c ε r data hε (le_of_lt hεr') z.2⟩

theorem morseBeltMapOnOpen_cell {m k : ℕ} (hk : k ≤ m + 1) (c ε r : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} {f : M → ℝ}
    (data : MorseChart (m + 1) k hk c I f)
    (hε : 0 < ε) (hεr' : Real.sqrt (2 * ε + 2 * r ^ 2) < data.R)
    (d : StandardHandle k (m + 1 - k))
    (hd : morseNorm (m + 1) (modelHandleMap hk ε r d) < data.R) :
    (morseBeltMapOnOpen hk c ε r data hε hεr'
      ⟨Handle.cell (morseAttachingEmbedding hk c ε r data hε (le_of_lt hεr')) d,
        Or.inr ⟨d, hd, rfl⟩⟩ : MorseModel (m + 1)) =
      modelHandleMap hk ε r d := by
  dsimp [morseBeltMapOnOpen]
  exact morseBeltMap_cell hk c ε r data hε hεr' d

theorem morseBeltMapOnOpen_lower {m k : ℕ} (hk : k ≤ m + 1) (c ε r : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} {f : M → ℝ}
    (data : MorseChart (m + 1) k hk c I f)
    (hε : 0 < ε) (hεr' : Real.sqrt (2 * ε + 2 * r ^ 2) < data.R)
    (x : SublevelSpace f (c - ε)) (hx : x ∈ morseBeltLowerSet hk c ε data) :
    (morseBeltMapOnOpen hk c ε r data hε hεr'
      ⟨Handle.lower (morseAttachingEmbedding hk c ε r data hε (le_of_lt hεr')) x,
        Or.inl ⟨x, hx, rfl⟩⟩ : MorseModel (m + 1)) =
      data.χ.symm x.1 := by
  dsimp [morseBeltMapOnOpen]
  exact morseBeltMap_lower hk c ε r data hε hεr' x hx

noncomputable def morseBeltMapExt {m k : ℕ} (hk : k ≤ m + 1) (c ε r : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} {f : M → ℝ}
    (data : MorseChart (m + 1) k hk c I f)
    (hε : 0 < ε) (hεr' : Real.sqrt (2 * ε + 2 * r ^ 2) < data.R)
    (z : Handle.AdjunctionSpace k (m + 1 - k)
      (morseAttachingEmbedding hk c ε r data hε (le_of_lt hεr'))) :
    morseUpperSublevel hk c r :=
  by
  classical
  exact if hz : z ∈ morseBeltOpenSet hk c ε r data hε (le_of_lt hεr') then
    morseBeltMapOnOpen hk c ε r data hε hεr' ⟨z, hz⟩
  else
    (⟨0, by
      change morseNormalForm hk c 0 ≤ c + r ^ 2 / 2
      have h0 : morseNormalForm hk c 0 = c := by
        dsimp [morseNormalForm]
        simp
      rw [h0]
      have hr2 : 0 ≤ r ^ 2 := sq_nonneg r
      nlinarith⟩ : morseUpperSublevel hk c r)

theorem morseBeltMapExt_on_open {m k : ℕ} (hk : k ≤ m + 1) (c ε r : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} {f : M → ℝ}
    (data : MorseChart (m + 1) k hk c I f)
    (hε : 0 < ε) (hεr' : Real.sqrt (2 * ε + 2 * r ^ 2) < data.R)
    (z : {z' : Handle.AdjunctionSpace k (m + 1 - k)
      (morseAttachingEmbedding hk c ε r data hε (le_of_lt hεr')) //
        z' ∈ morseBeltOpenSet hk c ε r data hε (le_of_lt hεr')}) :
    morseBeltMapExt hk c ε r data hε hεr' z.1 = morseBeltMapOnOpen hk c ε r data hε hεr' z := by
  dsimp [morseBeltMapExt]
  rw [dif_pos z.2]

theorem morseBeltOpenSet_preimage {m k : ℕ} (hk : k ≤ m + 1) (c ε r : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} {f : M → ℝ}
    (data : MorseChart (m + 1) k hk c I f)
    (hε : 0 < ε) (hεr' : Real.sqrt (2 * ε + 2 * r ^ 2) < data.R) :
    (fun s : StandardHandle k (m + 1 - k) ⊕ SublevelSpace f (c - ε) =>
      DifferentialGeometry.Topology.adjunctionMk (attachingInclusion k (m + 1 - k))
        (morseAttachingEmbedding hk c ε r data hε (le_of_lt hεr')) s) ⁻¹'
      morseBeltOpenSet hk c ε r data hε (le_of_lt hεr') =
    (Sum.inr '' morseBeltLowerSet hk c ε data : Set
      (StandardHandle k (m + 1 - k) ⊕ SublevelSpace f (c - ε))) ∪
      Sum.inl '' {d : StandardHandle k (m + 1 - k) |
        morseNorm (m + 1) (modelHandleMap hk ε r d) < data.R} := by
  let A : Set (StandardHandle k (m + 1 - k) ⊕ SublevelSpace f (c - ε)) :=
    (Sum.inr '' morseBeltLowerSet hk c ε data : Set
      (StandardHandle k (m + 1 - k) ⊕ SublevelSpace f (c - ε))) ∪
      Sum.inl '' {d : StandardHandle k (m + 1 - k) |
        morseNorm (m + 1) (modelHandleMap hk ε r d) < data.R}
  change (fun s : StandardHandle k (m + 1 - k) ⊕ SublevelSpace f (c - ε) =>
      DifferentialGeometry.Topology.adjunctionMk (attachingInclusion k (m + 1 - k))
        (morseAttachingEmbedding hk c ε r data hε (le_of_lt hεr')) s) ⁻¹'
      morseBeltOpenSet hk c ε r data hε (le_of_lt hεr') = A
  have hS : morseBeltOpenSet hk c ε r data hε (le_of_lt hεr') =
      (fun z : StandardHandle k (m + 1 - k) ⊕ SublevelSpace f (c - ε) =>
        DifferentialGeometry.Topology.adjunctionMk (attachingInclusion k (m + 1 - k))
          (morseAttachingEmbedding hk c ε r data hε (le_of_lt hεr')) z) '' A := by
    dsimp [A, morseBeltOpenSet, Handle.lower, adjunctionLower, Handle.cell, adjunctionCell]
    rw [Set.image_union, Set.image_image, Set.image_image]
    rfl
  ext s
  constructor
  · intro hs
    rcases (by simpa [hS] using hs : ∃ z ∈ A,
      DifferentialGeometry.Topology.adjunctionMk (attachingInclusion k (m + 1 - k))
        (morseAttachingEmbedding hk c ε r data hε (le_of_lt hεr')) z =
        DifferentialGeometry.Topology.adjunctionMk (attachingInclusion k (m + 1 - k))
          (morseAttachingEmbedding hk c ε r data hε (le_of_lt hεr')) s) with ⟨z, hz, hsz⟩
    have hgen : Relation.EqvGen (DifferentialGeometry.Topology.adjunctionRel
        (attachingInclusion k (m + 1 - k))
        (morseAttachingEmbedding hk c ε r data hε (le_of_lt hεr'))) s z := Quot.eq.mp hsz.symm
    exact (morseBeltEqvGen_mem hk c ε r data hε (le_of_lt hεr') s z hgen).mpr hz
  · intro hs
    rcases hs with hs | hs
    · rcases hs with ⟨x, hx, rfl⟩
      dsimp [morseBeltOpenSet]
      exact Or.inl ⟨x, hx, rfl⟩
    · rcases hs with ⟨d, hd, rfl⟩
      dsimp [morseBeltOpenSet]
      exact Or.inr ⟨d, hd, rfl⟩

private lemma continuous_codRestrict_iff {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    {p : Y → Prop} (f : X → Y) (h : ∀ x, p (f x)) :
    Continuous (fun x : X => (⟨f x, h x⟩ : Subtype p)) ↔ Continuous f := by
  constructor
  · intro hc
    exact continuous_subtype_val.comp hc
  · intro hf
    rw [continuous_iff_continuousAt]
    intro x
    rw [ContinuousAt, tendsto_subtype_rng]
    simpa using hf.continuousAt

private lemma continuousOn_quotient_lift_open {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z] {q : X → Y} (hq : Topology.IsQuotientMap q) {f : X → Z} {g : Y → Z}
    (hfg : ∀ x, g (q x) = f x) {A : Set X} {B : Set Y} (hA : A = q ⁻¹' B)
    (hf : ContinuousOn f A) (hB : IsOpen B) : ContinuousOn g B := by
  have hqcont : Continuous q := hq.continuous
  have hAopen : IsOpen A := by
    rw [hA]
    exact IsOpen.preimage hqcont hB
  rw [continuousOn_iff_continuous_restrict]
  rw [continuous_def]
  intro V hV
  have hpre : IsOpen (g ⁻¹' V ∩ B) := by
    have hqpre : IsOpen (q ⁻¹' (g ⁻¹' V ∩ B)) := by
      have hset : q ⁻¹' (g ⁻¹' V ∩ B) = f ⁻¹' V ∩ A := by
        ext x
        constructor
        · intro hx
          change q x ∈ g ⁻¹' V ∩ B at hx
          rcases hx with ⟨hxg, hxB⟩
          constructor
          · change f x ∈ V
            rw [← hfg x]
            exact hxg
          · rw [hA]
            change q x ∈ B
            exact hxB
        · intro hx
          rcases hx with ⟨hxf, hxA⟩
          constructor
          · change g (q x) ∈ V
            rw [hfg x]
            exact hxf
          · rwa [hA] at hxA
      rw [hset]
      have hpreV : IsOpen (f ⁻¹' V ∩ A) := by
        rw [isOpen_iff_mem_nhds]
        intro x hx
        rcases hx with ⟨hxf, hxA⟩
        have hcontAt : ContinuousAt f x :=
          (hf x hxA).continuousAt (IsOpen.mem_nhds hAopen hxA)
        have hpreV' : f ⁻¹' V ∈ nhds x :=
          hcontAt.preimage_mem_nhds (IsOpen.mem_nhds hV hxf)
        exact Filter.inter_mem hpreV' (IsOpen.mem_nhds hAopen hxA)
      exact hpreV
    exact (hq.isOpen_preimage).mp hqpre
  -- the preimage under B.restrict g is open in the subspace B
  have hsub : IsOpen {z : {y : Y // y ∈ B} | g z.1 ∈ V} := by
    -- {z : B | g z ∈ V} = (inclusion)⁻¹ (g ⁻¹' V ∩ B) — open in B since g ⁻¹' V ∩ B open
    have heq : {z : {y : Y // y ∈ B} | g z.1 ∈ V} = (Subtype.val : {y : Y // y ∈ B} → Y) ⁻¹' (g ⁻¹' V ∩ B) := by
      ext z
      constructor
      · intro hz
        exact ⟨hz, z.2⟩
      · intro hz
        rcases hz with ⟨hzg, hzB⟩
        exact hzg
    rw [heq]
    exact IsOpen.preimage continuous_subtype_val hpre
  exact hsub

theorem continuous_morseBeltMapOnOpen {m k : ℕ} (hk : k ≤ m + 1) (c ε r : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} {f : M → ℝ}
    (data : MorseChart (m + 1) k hk c I f)
    (hε : 0 < ε) (hεr' : Real.sqrt (2 * ε + 2 * r ^ 2) < data.R) :
    Continuous (morseBeltMapOnOpen hk c ε r data hε hεr') := by
  let q : StandardHandle k (m + 1 - k) ⊕ SublevelSpace f (c - ε) →
      Handle.AdjunctionSpace k (m + 1 - k)
        (morseAttachingEmbedding hk c ε r data hε (le_of_lt hεr')) :=
    fun s => DifferentialGeometry.Topology.adjunctionMk (attachingInclusion k (m + 1 - k))
      (morseAttachingEmbedding hk c ε r data hε (le_of_lt hεr')) s
  let A : Set (StandardHandle k (m + 1 - k) ⊕ SublevelSpace f (c - ε)) :=
    (Sum.inr '' morseBeltLowerSet hk c ε data : Set
      (StandardHandle k (m + 1 - k) ⊕ SublevelSpace f (c - ε))) ∪
      Sum.inl '' {d : StandardHandle k (m + 1 - k) |
        morseNorm (m + 1) (modelHandleMap hk ε r d) < data.R}
  let B : Set (Handle.AdjunctionSpace k (m + 1 - k)
      (morseAttachingEmbedding hk c ε r data hε (le_of_lt hεr'))) :=
    morseBeltOpenSet hk c ε r data hε (le_of_lt hεr')
  let g := morseBeltMapExt hk c ε r data hε hεr'
  have hB : IsOpen B := isOpen_morseBeltOpenSet hk c ε r data hε (le_of_lt hεr')
  have hq : Topology.IsQuotientMap q := by
    dsimp [q]
    exact isQuotientMap_adjunctionMk (attachingInclusion k (m + 1 - k))
      (morseAttachingEmbedding hk c ε r data hε (le_of_lt hεr'))
  have hpre : q ⁻¹' B = A := by
    dsimp [q, B, A]
    exact morseBeltOpenSet_preimage hk c ε r data hε hεr'
  have hcoord₁ : Continuous (fun s : StandardHandle k (m + 1 - k) ⊕ SublevelSpace f (c - ε) =>
      Sum.elim (fun _ : StandardHandle k (m + 1 - k) => (data.χ 0 : M))
        (fun x : SublevelSpace f (c - ε) => (x.1 : M)) s) := by
    exact Continuous.sumElim continuous_const continuous_subtype_val
  have hmain₁ : ContinuousOn (fun s : StandardHandle k (m + 1 - k) ⊕ SublevelSpace f (c - ε) =>
      data.χ.symm (Sum.elim (fun _ : StandardHandle k (m + 1 - k) => (data.χ 0 : M))
        (fun x : SublevelSpace f (c - ε) => (x.1 : M)) s))
      (Sum.inr '' morseBeltLowerSet hk c ε data) := by
    refine ContinuousOn.comp data.χ.continuousOn_invFun hcoord₁.continuousOn ?_
    intro s hs
    rcases hs with ⟨x, hx, hxy⟩
    rw [← hxy]
    rcases hx with ⟨y, hy, hxy'⟩
    simpa [hxy'] using data.χ.map_source (data.hχsrc y (le_of_lt hy))
  have hf₁ : ContinuousOn (fun s => (g (q s) : MorseModel (m + 1)))
      (Sum.inr '' morseBeltLowerSet hk c ε data : Set
        (StandardHandle k (m + 1 - k) ⊕ SublevelSpace f (c - ε))) := by
    refine (continuousOn_congr (s := (Sum.inr '' morseBeltLowerSet hk c ε data : Set
        (StandardHandle k (m + 1 - k) ⊕ SublevelSpace f (c - ε))))
      (g := fun s => (g (q s) : MorseModel (m + 1)))
      (f := fun s : StandardHandle k (m + 1 - k) ⊕ SublevelSpace f (c - ε) =>
        data.χ.symm (Sum.elim (fun _ : StandardHandle k (m + 1 - k) => (data.χ 0 : M))
          (fun x : SublevelSpace f (c - ε) => (x.1 : M)) s)) ?_).mpr hmain₁
    intro s hs
    rcases hs with ⟨x, hx, hxy⟩
    rw [← hxy]
    change (morseBeltMapExt hk c ε r data hε hεr'
      (DifferentialGeometry.Topology.adjunctionMk (attachingInclusion k (m + 1 - k))
        (morseAttachingEmbedding hk c ε r data hε (le_of_lt hεr')) (Sum.inr x)) :
        MorseModel (m + 1)) = data.χ.symm x.1
    rw [morseBeltMapExt_on_open hk c ε r data hε hεr' ⟨_, by
      exact Or.inl ⟨x, hx, rfl⟩⟩]
    exact morseBeltMapOnOpen_lower hk c ε r data hε hεr' x hx
  have hcoord₂ : Continuous (fun s : StandardHandle k (m + 1 - k) ⊕ SublevelSpace f (c - ε) =>
      Sum.elim (fun d : StandardHandle k (m + 1 - k) => modelHandleMap hk ε r d)
        (fun _ : SublevelSpace f (c - ε) => (0 : MorseModel (m + 1))) s) := by
    exact Continuous.sumElim (continuous_modelHandleMap hk ε r) continuous_const
  have hf₂ : ContinuousOn (fun s => (g (q s) : MorseModel (m + 1)))
      (Sum.inl '' {d : StandardHandle k (m + 1 - k) |
        morseNorm (m + 1) (modelHandleMap hk ε r d) < data.R} : Set
        (StandardHandle k (m + 1 - k) ⊕ SublevelSpace f (c - ε))) := by
    refine (continuousOn_congr (s := (Sum.inl '' {d : StandardHandle k (m + 1 - k) |
        morseNorm (m + 1) (modelHandleMap hk ε r d) < data.R} : Set
        (StandardHandle k (m + 1 - k) ⊕ SublevelSpace f (c - ε))))
      (g := fun s => (g (q s) : MorseModel (m + 1)))
      (f := fun s : StandardHandle k (m + 1 - k) ⊕ SublevelSpace f (c - ε) =>
        Sum.elim (fun d : StandardHandle k (m + 1 - k) => modelHandleMap hk ε r d)
          (fun _ : SublevelSpace f (c - ε) => (0 : MorseModel (m + 1))) s) ?_).mpr
        hcoord₂.continuousOn
    intro s hs
    rcases hs with ⟨d, hd, hxy⟩
    rw [← hxy]
    change (morseBeltMapExt hk c ε r data hε hεr'
      (DifferentialGeometry.Topology.adjunctionMk (attachingInclusion k (m + 1 - k))
        (morseAttachingEmbedding hk c ε r data hε (le_of_lt hεr')) (Sum.inl d)) :
        MorseModel (m + 1)) = modelHandleMap hk ε r d
    rw [morseBeltMapExt_on_open hk c ε r data hε hεr' ⟨_, by
      exact Or.inr ⟨d, hd, rfl⟩⟩]
    exact morseBeltMapOnOpen_cell hk c ε r data hε hεr' d hd
  have hW : IsOpen (Sum.inr '' morseBeltLowerSet hk c ε data : Set
      (StandardHandle k (m + 1 - k) ⊕ SublevelSpace f (c - ε))) := by
    rw [isOpen_sum_iff]
    constructor
    · have heq : Sum.inl ⁻¹' (Sum.inr '' morseBeltLowerSet hk c ε data : Set
          (StandardHandle k (m + 1 - k) ⊕ SublevelSpace f (c - ε))) = ∅ := by
        ext x
        constructor
        · intro hx
          rcases hx with ⟨y, hy, hxy⟩
          cases hxy
        · intro hx
          exact False.elim hx
      rw [heq]
      exact isOpen_empty
    · have heq : Sum.inr ⁻¹' (Sum.inr '' morseBeltLowerSet hk c ε data : Set
          (StandardHandle k (m + 1 - k) ⊕ SublevelSpace f (c - ε))) =
          morseBeltLowerSet hk c ε data := by
        ext x
        constructor
        · intro hx
          rcases hx with ⟨y, hy, hxy⟩
          have hy' : y = x := Sum.inr.inj hxy
          simpa [hy'] using hy
        · intro hx
          exact ⟨x, hx, rfl⟩
      rw [heq]
      exact isOpen_morseBeltLowerSet hk c ε data
  have hV : IsOpen (Sum.inl '' {d : StandardHandle k (m + 1 - k) |
      morseNorm (m + 1) (modelHandleMap hk ε r d) < data.R} : Set
      (StandardHandle k (m + 1 - k) ⊕ SublevelSpace f (c - ε))) := by
    rw [isOpen_sum_iff]
    constructor
    · have heq : Sum.inl ⁻¹' (Sum.inl '' {d : StandardHandle k (m + 1 - k) |
          morseNorm (m + 1) (modelHandleMap hk ε r d) < data.R} : Set
          (StandardHandle k (m + 1 - k) ⊕ SublevelSpace f (c - ε))) =
          {d : StandardHandle k (m + 1 - k) |
            morseNorm (m + 1) (modelHandleMap hk ε r d) < data.R} := by
        ext x
        constructor
        · intro hx
          rcases hx with ⟨y, hy, hxy⟩
          have hy' : y = x := Sum.inl.inj hxy
          simpa [hy'] using hy
        · intro hx
          exact ⟨x, hx, rfl⟩
      rw [heq]
      exact isOpen_morseBeltCellSet hk c ε r data
    · have heq : Sum.inr ⁻¹' (Sum.inl '' {d : StandardHandle k (m + 1 - k) |
          morseNorm (m + 1) (modelHandleMap hk ε r d) < data.R} : Set
          (StandardHandle k (m + 1 - k) ⊕ SublevelSpace f (c - ε))) = ∅ := by
        ext x
        constructor
        · intro hx
          rcases hx with ⟨y, hy, hxy⟩
          cases hxy
        · intro hx
          exact False.elim hx
      rw [heq]
      exact isOpen_empty
  have hf : ContinuousOn (fun s => (g (q s) : MorseModel (m + 1))) A := by
    dsimp [A]
    exact hf₁.union_of_isOpen hf₂ hW hV
  have hcontExt : ContinuousOn (fun z => (g z : MorseModel (m + 1))) B :=
    continuousOn_quotient_lift_open hq (fun x => rfl) hpre.symm hf hB
  have hres : Continuous (fun z : {z' : Handle.AdjunctionSpace k (m + 1 - k)
      (morseAttachingEmbedding hk c ε r data hε (le_of_lt hεr')) // z' ∈ B} =>
      (g z.1 : MorseModel (m + 1))) := by
    rw [continuousOn_iff_continuous_restrict] at hcontExt
    simpa [Set.restrict] using hcontExt
  have hcont : Continuous (fun z : {z' : Handle.AdjunctionSpace k (m + 1 - k)
      (morseAttachingEmbedding hk c ε r data hε (le_of_lt hεr')) // z' ∈ B} =>
      (morseBeltMapOnOpen hk c ε r data hε hεr' z : MorseModel (m + 1))) := by
    refine hres.congr ?_
    intro z
    exact congrArg (fun y : morseUpperSublevel hk c r => (y : MorseModel (m + 1)))
      (morseBeltMapExt_on_open hk c ε r data hε hεr' z)
  exact (continuous_codRestrict_iff
    (fun z : {z' : Handle.AdjunctionSpace k (m + 1 - k)
      (morseAttachingEmbedding hk c ε r data hε (le_of_lt hεr')) // z' ∈ B} =>
      (morseBeltMapOnOpen hk c ε r data hε hεr' z : MorseModel (m + 1)))
    (fun z => (morseBeltMapOnOpen hk c ε r data hε hεr' z).2)).mpr hcont

theorem morseBeltMapOnOpen_inr {m k : ℕ} (hk : k ≤ m + 1) (c ε r : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} {f : M → ℝ}
    (data : MorseChart (m + 1) k hk c I f)
    (hε : 0 < ε) (hεr' : Real.sqrt (2 * ε + 2 * r ^ 2) < data.R)
    (x : SublevelSpace f (c - ε))
    (hz : DifferentialGeometry.Topology.adjunctionMk (attachingInclusion k (m + 1 - k))
      (morseAttachingEmbedding hk c ε r data hε (le_of_lt hεr')) (Sum.inr x) ∈
      morseBeltOpenSet hk c ε r data hε (le_of_lt hεr')) :
    (morseBeltMapOnOpen hk c ε r data hε hεr'
      ⟨DifferentialGeometry.Topology.adjunctionMk (attachingInclusion k (m + 1 - k))
        (morseAttachingEmbedding hk c ε r data hε (le_of_lt hεr')) (Sum.inr x), hz⟩ :
        MorseModel (m + 1)) = data.χ.symm x.1 := by
  have hx : x ∈ morseBeltLowerSet hk c ε data := by
    have hmem : Sum.inr x ∈ (fun s : StandardHandle k (m + 1 - k) ⊕ SublevelSpace f (c - ε) =>
        DifferentialGeometry.Topology.adjunctionMk (attachingInclusion k (m + 1 - k))
          (morseAttachingEmbedding hk c ε r data hε (le_of_lt hεr')) s) ⁻¹'
        morseBeltOpenSet hk c ε r data hε (le_of_lt hεr') := by
      exact hz
    rw [morseBeltOpenSet_preimage hk c ε r data hε hεr'] at hmem
    rcases hmem with hmem | hmem
    · rcases hmem with ⟨x', hx', hxx'⟩
      have hx'eq : x' = x := Sum.inr.inj hxx'
      simpa [hx'eq] using hx'
    · rcases hmem with ⟨d, hd, hdi⟩
      cases hdi
  have heq : (⟨DifferentialGeometry.Topology.adjunctionMk (attachingInclusion k (m + 1 - k))
        (morseAttachingEmbedding hk c ε r data hε (le_of_lt hεr')) (Sum.inr x), hz⟩ :
        {z' : Handle.AdjunctionSpace k (m + 1 - k)
          (morseAttachingEmbedding hk c ε r data hε (le_of_lt hεr')) //
            z' ∈ morseBeltOpenSet hk c ε r data hε (le_of_lt hεr')}) =
      ⟨Handle.lower (morseAttachingEmbedding hk c ε r data hε (le_of_lt hεr')) x,
        Or.inl ⟨x, hx, rfl⟩⟩ := by
    apply Subtype.ext
    rfl
  simpa [heq] using (morseBeltMapOnOpen_lower hk c ε r data hε hεr' x hx)

theorem morseBeltMapOnOpen_inl {m k : ℕ} (hk : k ≤ m + 1) (c ε r : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} {f : M → ℝ}
    (data : MorseChart (m + 1) k hk c I f)
    (hε : 0 < ε) (hεr' : Real.sqrt (2 * ε + 2 * r ^ 2) < data.R)
    (d : StandardHandle k (m + 1 - k))
    (hz : DifferentialGeometry.Topology.adjunctionMk (attachingInclusion k (m + 1 - k))
      (morseAttachingEmbedding hk c ε r data hε (le_of_lt hεr')) (Sum.inl d) ∈
      morseBeltOpenSet hk c ε r data hε (le_of_lt hεr')) :
    (morseBeltMapOnOpen hk c ε r data hε hεr'
      ⟨DifferentialGeometry.Topology.adjunctionMk (attachingInclusion k (m + 1 - k))
        (morseAttachingEmbedding hk c ε r data hε (le_of_lt hεr')) (Sum.inl d), hz⟩ :
        MorseModel (m + 1)) = modelHandleMap hk ε r d := by
  have hd : morseNorm (m + 1) (modelHandleMap hk ε r d) < data.R := by
    have hmem : Sum.inl d ∈ (fun s : StandardHandle k (m + 1 - k) ⊕ SublevelSpace f (c - ε) =>
        DifferentialGeometry.Topology.adjunctionMk (attachingInclusion k (m + 1 - k))
          (morseAttachingEmbedding hk c ε r data hε (le_of_lt hεr')) s) ⁻¹'
        morseBeltOpenSet hk c ε r data hε (le_of_lt hεr') := by
      exact hz
    rw [morseBeltOpenSet_preimage hk c ε r data hε hεr'] at hmem
    rcases hmem with hmem | hmem
    · rcases hmem with ⟨x, hx, hxi⟩
      cases hxi
    · rcases hmem with ⟨d', hd', hdd'⟩
      have hd'eq : d' = d := Sum.inl.inj hdd'
      simpa [hd'eq] using hd'
  have heq : (⟨DifferentialGeometry.Topology.adjunctionMk (attachingInclusion k (m + 1 - k))
        (morseAttachingEmbedding hk c ε r data hε (le_of_lt hεr')) (Sum.inl d), hz⟩ :
        {z' : Handle.AdjunctionSpace k (m + 1 - k)
          (morseAttachingEmbedding hk c ε r data hε (le_of_lt hεr')) //
            z' ∈ morseBeltOpenSet hk c ε r data hε (le_of_lt hεr')}) =
      ⟨Handle.cell (morseAttachingEmbedding hk c ε r data hε (le_of_lt hεr')) d,
        Or.inr ⟨d, hd, rfl⟩⟩ := by
    apply Subtype.ext
    rfl
  simpa [heq] using (morseBeltMapOnOpen_cell hk c ε r data hε hεr' d hd)

theorem morseHandleAdjunctionHomeoUnion_cell {m k : ℕ} (hk : k ≤ m + 1) (c ε r : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} {f : M → ℝ}
    (data : MorseChart (m + 1) k hk c I f)
    (hε : 0 < ε) (hr : r ≠ 0) (hεr : Real.sqrt (2 * ε + 2 * r ^ 2) ≤ data.R)
    (hcont : Continuous f) (d : StandardHandle k (m + 1 - k)) :
    morseHandleAdjunctionHomeoUnion hk c ε r data hε hr hεr hcont
      (Handle.cell (morseAttachingEmbedding hk c ε r data hε hεr) d) =
      ⟨handleEmbedding hk c ε r data d, Or.inr ⟨d, rfl⟩⟩ := by
  exact Handle.adjunctionHomeomorphUnionImage_cell
    (φ := morseAttachingEmbedding hk c ε r data hε hεr)
    (c := handleEmbedding hk c ε r data)
    (morseAttachingEmbedding_eq_handleEmbedding hk c ε r data hε hεr)
    (handleEmbedding_injective hk c ε r data hε hr hεr)
    (handleEmbedding_continuous hk c ε r data hε hεr)
    (by
      rw [Set.disjoint_left]
      intro y hys hyt
      rcases hys with ⟨p, hp, hpy⟩
      have hiff := (handleEmbedding_mem_lower_iff hk c ε r data hε hεr p).mp (by
        simpa [hpy] using hyt)
      have hreg : p ∈ attachingRegion k (m + 1 - k) := by
        dsimp [attachingRegion]
        exact hiff
      exact hp.2 hreg)
    (by
      exact isClosed_Iic.preimage hcont) d

theorem morseHandleAdjunctionHomeoUnion_beltMap {m k : ℕ} (hk : k ≤ m + 1) (c ε r : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} {f : M → ℝ}
    (data : MorseChart (m + 1) k hk c I f)
    (hε : 0 < ε) (hr : r ≠ 0) (hεr' : Real.sqrt (2 * ε + 2 * r ^ 2) < data.R)
    (hcont : Continuous f)
    (z : {z' : Handle.AdjunctionSpace k (m + 1 - k)
      (morseAttachingEmbedding hk c ε r data hε (le_of_lt hεr')) //
        z' ∈ morseBeltOpenSet hk c ε r data hε (le_of_lt hεr')}) :
    (morseHandleAdjunctionHomeoUnion hk c ε r data hε hr (le_of_lt hεr') hcont z.1).1 =
      data.χ (morseBeltMapOnOpen hk c ε r data hε hεr' z) := by
  rcases Quot.exists_rep z.1 with ⟨s, hs⟩
  cases s with
  | inl d =>
      have hz' : DifferentialGeometry.Topology.adjunctionMk (attachingInclusion k (m + 1 - k))
          (morseAttachingEmbedding hk c ε r data hε (le_of_lt hεr')) (Sum.inl d) ∈
          morseBeltOpenSet hk c ε r data hε (le_of_lt hεr') := by
        simpa [← hs] using z.2
      have hzeq : z = ⟨DifferentialGeometry.Topology.adjunctionMk
          (attachingInclusion k (m + 1 - k))
          (morseAttachingEmbedding hk c ε r data hε (le_of_lt hεr')) (Sum.inl d), hz'⟩ := by
        apply Subtype.ext
        simpa using hs.symm
      rw [hzeq]
      change (morseHandleAdjunctionHomeoUnion hk c ε r data hε hr (le_of_lt hεr') hcont
          (Handle.cell (morseAttachingEmbedding hk c ε r data hε (le_of_lt hεr')) d)).1 =
        data.χ (morseBeltMapOnOpen hk c ε r data hε hεr'
          ⟨DifferentialGeometry.Topology.adjunctionMk (attachingInclusion k (m + 1 - k))
            (morseAttachingEmbedding hk c ε r data hε (le_of_lt hεr')) (Sum.inl d), hz'⟩)
      rw [morseHandleAdjunctionHomeoUnion_cell hk c ε r data hε hr (le_of_lt hεr') hcont d]
      change handleEmbedding hk c ε r data d =
        data.χ (morseBeltMapOnOpen hk c ε r data hε hεr'
          ⟨DifferentialGeometry.Topology.adjunctionMk (attachingInclusion k (m + 1 - k))
            (morseAttachingEmbedding hk c ε r data hε (le_of_lt hεr')) (Sum.inl d), hz'⟩)
      rw [morseBeltMapOnOpen_inl hk c ε r data hε hεr' d hz']
      rfl
  | inr x =>
      have hz' : DifferentialGeometry.Topology.adjunctionMk (attachingInclusion k (m + 1 - k))
          (morseAttachingEmbedding hk c ε r data hε (le_of_lt hεr')) (Sum.inr x) ∈
          morseBeltOpenSet hk c ε r data hε (le_of_lt hεr') := by
        simpa [← hs] using z.2
      have hzeq : z = ⟨DifferentialGeometry.Topology.adjunctionMk
          (attachingInclusion k (m + 1 - k))
          (morseAttachingEmbedding hk c ε r data hε (le_of_lt hεr')) (Sum.inr x), hz'⟩ := by
        apply Subtype.ext
        simpa using hs.symm
      rw [hzeq]
      change (morseHandleAdjunctionHomeoUnion hk c ε r data hε hr (le_of_lt hεr') hcont
          (Handle.lower (morseAttachingEmbedding hk c ε r data hε (le_of_lt hεr')) x)).1 =
        data.χ (morseBeltMapOnOpen hk c ε r data hε hεr'
          ⟨DifferentialGeometry.Topology.adjunctionMk (attachingInclusion k (m + 1 - k))
            (morseAttachingEmbedding hk c ε r data hε (le_of_lt hεr')) (Sum.inr x), hz'⟩)
      rw [morseHandleAdjunctionHomeoUnion_lower hk c ε r data hε hr (le_of_lt hεr') hcont x]
      change x.1 =
        data.χ (morseBeltMapOnOpen hk c ε r data hε hεr'
          ⟨DifferentialGeometry.Topology.adjunctionMk (attachingInclusion k (m + 1 - k))
            (morseAttachingEmbedding hk c ε r data hε (le_of_lt hεr')) (Sum.inr x), hz'⟩)
      rw [morseBeltMapOnOpen_inr hk c ε r data hε hεr' x hz']
      have hx : x ∈ morseBeltLowerSet hk c ε data := by
        have hmem : Sum.inr x ∈ (fun s : StandardHandle k (m + 1 - k) ⊕ SublevelSpace f (c - ε) =>
            DifferentialGeometry.Topology.adjunctionMk (attachingInclusion k (m + 1 - k))
              (morseAttachingEmbedding hk c ε r data hε (le_of_lt hεr')) s) ⁻¹'
            morseBeltOpenSet hk c ε r data hε (le_of_lt hεr') := by
          exact hz'
        rw [morseBeltOpenSet_preimage hk c ε r data hε hεr'] at hmem
        rcases hmem with hmem | hmem
        · rcases hmem with ⟨x', hx', hxx'⟩
          have hx'eq : x' = x := Sum.inr.inj hxx'
          simpa [hx'eq] using hx'
        · rcases hmem with ⟨d, hd, hdi⟩
          cases hdi
      have hxtgt : x.1 ∈ data.χ.target := by
        rcases hx with ⟨y, hy, hxy⟩
        simpa [hxy] using data.χ.map_source (data.hχsrc y (le_of_lt hy))
      exact (data.χ.right_inv hxtgt).symm

theorem morseBeltMapOnOpen_injective {m k : ℕ} (hk : k ≤ m + 1) (c ε r : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} {f : M → ℝ}
    (data : MorseChart (m + 1) k hk c I f)
    (hε : 0 < ε) (hr : r ≠ 0) (hεr' : Real.sqrt (2 * ε + 2 * r ^ 2) < data.R)
    (hcont : Continuous f) :
    Function.Injective (morseBeltMapOnOpen hk c ε r data hε hεr') := by
  intro z w h
  let H : Handle.AdjunctionSpace k (m + 1 - k)
      (morseAttachingEmbedding hk c ε r data hε (le_of_lt hεr')) ≃ₜ
      {x : M // x ∈ sublevel f (c - ε) ∪ Set.range (handleEmbedding hk c ε r data)} :=
    morseHandleAdjunctionHomeoUnion hk c ε r data hε hr (le_of_lt hεr') hcont
  have hval : (morseBeltMapOnOpen hk c ε r data hε hεr' z : MorseModel (m + 1)) =
      (morseBeltMapOnOpen hk c ε r data hε hεr' w : MorseModel (m + 1)) := by
    exact congrArg Subtype.val h
  have hχ : data.χ (morseBeltMapOnOpen hk c ε r data hε hεr' z) =
      data.χ (morseBeltMapOnOpen hk c ε r data hε hεr' w) := by
    exact congrArg data.χ hval
  have hu : (H z.1).1 = (H w.1).1 := by
    dsimp [H]
    rw [morseHandleAdjunctionHomeoUnion_beltMap hk c ε r data hε hr hεr' hcont z,
      morseHandleAdjunctionHomeoUnion_beltMap hk c ε r data hε hr hεr' hcont w]
    exact hχ
  have hH : H z.1 = H w.1 := by
    apply Subtype.ext
    exact hu
  have hzw : z.1 = w.1 := H.injective hH
  exact Subtype.ext hzw

noncomputable def morseBeltImage {m k : ℕ} (hk : k ≤ m + 1) (c ε r : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} {f : M → ℝ}
    (data : MorseChart (m + 1) k hk c I f) :
    Set (morseUpperSublevel hk c r) :=
  {y : morseUpperSublevel hk c r |
    morseNorm (m + 1) y.1 < data.R ∧
      (morseNormalForm hk c y.1 ≤ c - ε ∨ y.1 ∈ modelHandle hk ε r)}

theorem morseBeltMapOnOpen_mem_image {m k : ℕ} (hk : k ≤ m + 1) (c ε r : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} {f : M → ℝ}
    (data : MorseChart (m + 1) k hk c I f)
    (hε : 0 < ε) (hεr' : Real.sqrt (2 * ε + 2 * r ^ 2) < data.R)
    (z : {z' : Handle.AdjunctionSpace k (m + 1 - k)
      (morseAttachingEmbedding hk c ε r data hε (le_of_lt hεr')) //
        z' ∈ morseBeltOpenSet hk c ε r data hε (le_of_lt hεr')}) :
    morseBeltMapOnOpen hk c ε r data hε hεr' z ∈ morseBeltImage hk c ε r data := by
  rcases Quot.exists_rep z.1 with ⟨s, hs⟩
  cases s with
  | inl d =>
      have hz' : DifferentialGeometry.Topology.adjunctionMk (attachingInclusion k (m + 1 - k))
          (morseAttachingEmbedding hk c ε r data hε (le_of_lt hεr')) (Sum.inl d) ∈
          morseBeltOpenSet hk c ε r data hε (le_of_lt hεr') := by
        simpa [← hs] using z.2
      have hd : morseNorm (m + 1) (modelHandleMap hk ε r d) < data.R := by
        have hmem : Sum.inl d ∈ (fun s : StandardHandle k (m + 1 - k) ⊕ SublevelSpace f (c - ε) =>
            DifferentialGeometry.Topology.adjunctionMk (attachingInclusion k (m + 1 - k))
              (morseAttachingEmbedding hk c ε r data hε (le_of_lt hεr')) s) ⁻¹'
            morseBeltOpenSet hk c ε r data hε (le_of_lt hεr') := by
          exact hz'
        rw [morseBeltOpenSet_preimage hk c ε r data hε hεr'] at hmem
        rcases hmem with hmem | hmem
        · rcases hmem with ⟨x, hx, hxi⟩
          cases hxi
        · rcases hmem with ⟨d', hd', hdd'⟩
          have hd'eq : d' = d := Sum.inl.inj hdd'
          simpa [hd'eq] using hd'
      have hzeq : z = ⟨DifferentialGeometry.Topology.adjunctionMk
          (attachingInclusion k (m + 1 - k))
          (morseAttachingEmbedding hk c ε r data hε (le_of_lt hεr')) (Sum.inl d), hz'⟩ := by
        apply Subtype.ext
        simpa using hs.symm
      rw [hzeq]
      change morseNorm (m + 1) (morseBeltMapOnOpen hk c ε r data hε hεr'
          ⟨DifferentialGeometry.Topology.adjunctionMk (attachingInclusion k (m + 1 - k))
            (morseAttachingEmbedding hk c ε r data hε (le_of_lt hεr')) (Sum.inl d), hz'⟩ :
            MorseModel (m + 1)) < data.R ∧
        (morseNormalForm hk c (morseBeltMapOnOpen hk c ε r data hε hεr'
          ⟨DifferentialGeometry.Topology.adjunctionMk (attachingInclusion k (m + 1 - k))
            (morseAttachingEmbedding hk c ε r data hε (le_of_lt hεr')) (Sum.inl d), hz'⟩ :
              MorseModel (m + 1)) ≤ c - ε ∨
          (morseBeltMapOnOpen hk c ε r data hε hεr'
            ⟨DifferentialGeometry.Topology.adjunctionMk (attachingInclusion k (m + 1 - k))
              (morseAttachingEmbedding hk c ε r data hε (le_of_lt hεr')) (Sum.inl d), hz'⟩ :
              MorseModel (m + 1)) ∈ modelHandle hk ε r)
      rw [morseBeltMapOnOpen_inl hk c ε r data hε hεr' d hz']
      exact ⟨hd, Or.inr (modelHandleMap_mem hk ε r (le_of_lt hε) d)⟩
  | inr x =>
      have hz' : DifferentialGeometry.Topology.adjunctionMk (attachingInclusion k (m + 1 - k))
          (morseAttachingEmbedding hk c ε r data hε (le_of_lt hεr')) (Sum.inr x) ∈
          morseBeltOpenSet hk c ε r data hε (le_of_lt hεr') := by
        simpa [← hs] using z.2
      have hx : x ∈ morseBeltLowerSet hk c ε data := by
        have hmem : Sum.inr x ∈ (fun s : StandardHandle k (m + 1 - k) ⊕ SublevelSpace f (c - ε) =>
            DifferentialGeometry.Topology.adjunctionMk (attachingInclusion k (m + 1 - k))
              (morseAttachingEmbedding hk c ε r data hε (le_of_lt hεr')) s) ⁻¹'
            morseBeltOpenSet hk c ε r data hε (le_of_lt hεr') := by
          exact hz'
        rw [morseBeltOpenSet_preimage hk c ε r data hε hεr'] at hmem
        rcases hmem with hmem | hmem
        · rcases hmem with ⟨x', hx', hxx'⟩
          have hx'eq : x' = x := Sum.inr.inj hxx'
          simpa [hx'eq] using hx'
        · rcases hmem with ⟨d, hd, hdi⟩
          cases hdi
      have hzeq : z = ⟨DifferentialGeometry.Topology.adjunctionMk
          (attachingInclusion k (m + 1 - k))
          (morseAttachingEmbedding hk c ε r data hε (le_of_lt hεr')) (Sum.inr x), hz'⟩ := by
        apply Subtype.ext
        simpa using hs.symm
      rw [hzeq]
      change morseNorm (m + 1) (morseBeltMapOnOpen hk c ε r data hε hεr'
          ⟨DifferentialGeometry.Topology.adjunctionMk (attachingInclusion k (m + 1 - k))
            (morseAttachingEmbedding hk c ε r data hε (le_of_lt hεr')) (Sum.inr x), hz'⟩ :
            MorseModel (m + 1)) < data.R ∧
        (morseNormalForm hk c (morseBeltMapOnOpen hk c ε r data hε hεr'
          ⟨DifferentialGeometry.Topology.adjunctionMk (attachingInclusion k (m + 1 - k))
            (morseAttachingEmbedding hk c ε r data hε (le_of_lt hεr')) (Sum.inr x), hz'⟩ :
              MorseModel (m + 1)) ≤ c - ε ∨
          (morseBeltMapOnOpen hk c ε r data hε hεr'
            ⟨DifferentialGeometry.Topology.adjunctionMk (attachingInclusion k (m + 1 - k))
              (morseAttachingEmbedding hk c ε r data hε (le_of_lt hεr')) (Sum.inr x), hz'⟩ :
              MorseModel (m + 1)) ∈ modelHandle hk ε r)
      rcases hx with ⟨y, hy, hxy⟩
      have hsymm : data.χ.symm x.1 = y := by
        rw [← hxy]
        exact data.χ.left_inv (data.hχsrc y (le_of_lt hy))
      have hmNF : morseNormalForm hk c (data.χ.symm x.1) ≤ c - ε := by
        rw [hsymm]
        rw [← data.hnorm y (le_of_lt hy), hxy]
        exact x.2
      rw [morseBeltMapOnOpen_inr hk c ε r data hε hεr' x hz']
      exact ⟨by rw [hsymm]; exact hy, Or.inl hmNF⟩

theorem morseBeltMapOnOpen_image_subset {m k : ℕ} (hk : k ≤ m + 1) (c ε r : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} {f : M → ℝ}
    (data : MorseChart (m + 1) k hk c I f)
    (hε : 0 < ε) (hεr' : Real.sqrt (2 * ε + 2 * r ^ 2) < data.R) (hr : 0 < r)
    (y : morseUpperSublevel hk c r) (hy : y ∈ morseBeltImage hk c ε r data) :
    ∃ z : {z' : Handle.AdjunctionSpace k (m + 1 - k)
      (morseAttachingEmbedding hk c ε r data hε (le_of_lt hεr')) //
        z' ∈ morseBeltOpenSet hk c ε r data hε (le_of_lt hεr')},
      morseBeltMapOnOpen hk c ε r data hε hεr' z = y := by
  rcases hy with ⟨hnorm, hy'⟩
  rcases hy' with hy' | hy'
  · have hsrc : y.1 ∈ data.χ.source := data.hχsrc y.1 (le_of_lt hnorm)
    have hsub : f (data.χ y.1) ≤ c - ε := by
      rw [data.hnorm y.1 (le_of_lt hnorm)]
      exact hy'
    let x : SublevelSpace f (c - ε) := ⟨data.χ y.1, hsub⟩
    have hx : x ∈ morseBeltLowerSet hk c ε data := by
      dsimp [morseBeltLowerSet, x]
      exact ⟨y.1, hnorm, rfl⟩
    refine ⟨⟨Handle.lower (morseAttachingEmbedding hk c ε r data hε (le_of_lt hεr')) x,
      Or.inl ⟨x, hx, rfl⟩⟩, ?_⟩
    apply Subtype.ext
    change (morseBeltMapOnOpen hk c ε r data hε hεr'
      ⟨Handle.lower (morseAttachingEmbedding hk c ε r data hε (le_of_lt hεr')) x,
        Or.inl ⟨x, hx, rfl⟩⟩ : MorseModel (m + 1)) = y.1
    rw [morseBeltMapOnOpen_lower hk c ε r data hε hεr' x hx]
    dsimp [x]
    exact data.χ.left_inv hsrc
  · rw [← modelHandleMap_range hk ε r hε hr] at hy'
    rcases hy' with ⟨d, hd⟩
    have hd' : morseNorm (m + 1) (modelHandleMap hk ε r d) < data.R := by
      rw [hd]
      exact hnorm
    refine ⟨⟨Handle.cell (morseAttachingEmbedding hk c ε r data hε (le_of_lt hεr')) d,
      Or.inr ⟨d, hd', rfl⟩⟩, ?_⟩
    apply Subtype.ext
    change (morseBeltMapOnOpen hk c ε r data hε hεr'
      ⟨Handle.cell (morseAttachingEmbedding hk c ε r data hε (le_of_lt hεr')) d,
        Or.inr ⟨d, hd', rfl⟩⟩ : MorseModel (m + 1)) = y.1
    rw [morseBeltMapOnOpen_cell hk c ε r data hε hεr' d hd']
    exact hd

theorem morseBeltMapOnOpen_range {m k : ℕ} (hk : k ≤ m + 1) (c ε r : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} {f : M → ℝ}
    (data : MorseChart (m + 1) k hk c I f)
    (hε : 0 < ε) (hεr' : Real.sqrt (2 * ε + 2 * r ^ 2) < data.R) (hr : 0 < r) :
    Set.range (morseBeltMapOnOpen hk c ε r data hε hεr') =
      morseBeltImage hk c ε r data := by
  ext y
  constructor
  · intro hy
    rcases hy with ⟨z, rfl⟩
    exact morseBeltMapOnOpen_mem_image hk c ε r data hε hεr' z
  · intro hy
    exact morseBeltMapOnOpen_image_subset hk c ε r data hε hεr' hr y hy

noncomputable def morseModelHandleMapHomeo {m k : ℕ} (hk : k ≤ m + 1) (ε r : ℝ)
    (hε : 0 < ε) (hr : 0 < r) :
    StandardHandle k (m + 1 - k) ≃ₜ {y : MorseModel (m + 1) // y ∈ modelHandle hk ε r} := by
  let f : StandardHandle k (m + 1 - k) ≃ {y : MorseModel (m + 1) // y ∈ modelHandle hk ε r} :=
    Equiv.ofBijective (fun p : StandardHandle k (m + 1 - k) =>
      ⟨modelHandleMap hk ε r p, modelHandleMap_mem hk ε r (le_of_lt hε) p⟩)
      (by
        constructor
        · intro p q h
          apply modelHandleMap_injective hk ε r hε (ne_of_gt hr)
          exact congrArg Subtype.val h
        · intro y
          have hy : y.1 ∈ Set.range (modelHandleMap hk ε r) := by
            simpa [← modelHandleMap_range hk ε r hε hr] using y.2
          rcases hy with ⟨p, hp⟩
          exact ⟨p, Subtype.ext hp⟩)
  have hfcont : Continuous f := by
    dsimp [f]
    exact Continuous.subtype_mk (continuous_modelHandleMap hk ε r) (fun p =>
      modelHandleMap_mem hk ε r (le_of_lt hε) p)
  exact Continuous.homeoOfEquivCompactToT2 (f := f) hfcont

theorem morseModelHandleMapHomeo_apply {m k : ℕ} (hk : k ≤ m + 1) (ε r : ℝ)
    (hε : 0 < ε) (hr : 0 < r) (p : StandardHandle k (m + 1 - k)) :
    (morseModelHandleMapHomeo hk ε r hε hr p : MorseModel (m + 1)) =
      modelHandleMap hk ε r p := by
  rfl

theorem morseModelHandleMapHomeo_symm_apply {m k : ℕ} (hk : k ≤ m + 1) (ε r : ℝ)
    (hε : 0 < ε) (hr : 0 < r) (y : {y : MorseModel (m + 1) // y ∈ modelHandle hk ε r}) :
    modelHandleMap hk ε r ((morseModelHandleMapHomeo hk ε r hε hr).symm y) = y.1 := by
  exact congrArg Subtype.val ((morseModelHandleMapHomeo hk ε r hε hr).apply_symm_apply y)

noncomputable def closedCellClamp (n : ℕ) (x : EuclideanSpace ℝ (Fin n)) : ClosedCell n :=
  ⟨(max ‖x‖ 1)⁻¹ • x, by
    have hpos : 0 < max ‖x‖ 1 := lt_of_lt_of_le zero_lt_one (le_max_right ‖x‖ 1)
    have hle : ‖x‖ ≤ max ‖x‖ 1 := le_max_left ‖x‖ 1
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (le_of_lt hpos))]
    rw [mul_comm, ← div_eq_mul_inv]
    exact (div_le_one hpos).mpr hle⟩

theorem continuous_closedCellClamp (n : ℕ) : Continuous (closedCellClamp n) := by
  refine Continuous.subtype_mk ?_ (fun x => by
    have hpos : 0 < max ‖x‖ 1 := lt_of_lt_of_le zero_lt_one (le_max_right ‖x‖ 1)
    have hle : ‖x‖ ≤ max ‖x‖ 1 := le_max_left ‖x‖ 1
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (le_of_lt hpos))]
    rw [mul_comm, ← div_eq_mul_inv]
    exact (div_le_one hpos).mpr hle)
  have hf : Continuous (fun x : EuclideanSpace ℝ (Fin n) => (max ‖x‖ 1)⁻¹) := by
    refine Continuous.inv₀ ?_ (fun x => ?_)
    · exact continuous_norm.max continuous_const
    · exact ne_of_gt (lt_of_lt_of_le zero_lt_one (le_max_right ‖x‖ 1))
  exact hf.smul continuous_id

noncomputable def modelHandleMapRawSymm {n k : ℕ} (hk : k ≤ n) (ε r : ℝ)
    (y : MorseModel n) : StandardHandle k (n - k) :=
  (closedCellClamp k ((Real.sqrt (2 * ε + ‖posPart hk y‖ ^ 2))⁻¹ • negPart hk y),
    closedCellClamp (n - k) (r⁻¹ • posPart hk y))

theorem continuous_modelHandleMapRawSymm {n k : ℕ} (hk : k ≤ n) (ε r : ℝ) (hε : 0 < ε) :
    Continuous (modelHandleMapRawSymm hk ε r) := by
  change Continuous (fun y : MorseModel n =>
    (closedCellClamp k ((Real.sqrt (2 * ε + ‖posPart hk y‖ ^ 2))⁻¹ • negPart hk y),
      closedCellClamp (n - k) (r⁻¹ • posPart hk y)))
  refine Continuous.prodMk ?_ ?_
  · exact (continuous_closedCellClamp k).comp (by
      have hsqrt : Continuous (fun y : MorseModel n =>
          (Real.sqrt (2 * ε + ‖posPart hk y‖ ^ 2))⁻¹) := by
        refine Continuous.inv₀ ?_ (fun y => ?_)
        · exact Real.continuous_sqrt.comp (by
            have hnorm : Continuous (fun y : MorseModel n => ‖posPart hk y‖) :=
              continuous_norm.comp (continuous_posPart hk)
            have hpow : Continuous (fun y : MorseModel n => ‖posPart hk y‖ ^ 2) := hnorm.pow 2
            exact (continuous_const.add hpow : Continuous (fun y : MorseModel n =>
              2 * ε + ‖posPart hk y‖ ^ 2)))
        · exact ne_of_gt (by positivity : 0 < Real.sqrt (2 * ε + ‖posPart hk y‖ ^ 2))
      exact hsqrt.smul (continuous_negPart hk))
  · exact (continuous_closedCellClamp (n - k)).comp (by
      have hscalar : Continuous (fun _ : MorseModel n => (r⁻¹ : ℝ)) := continuous_const
      exact hscalar.smul (continuous_posPart hk))

theorem modelHandleMapRawSymm_map {n k : ℕ} (hk : k ≤ n) (ε r : ℝ)
    (hε : 0 < ε) (hr : 0 < r) (y : MorseModel n) (hy : y ∈ modelHandle hk ε r) :
    modelHandleMap hk ε r (modelHandleMapRawSymm hk ε r y) = y := by
  have hbnd₀ : ‖posPart hk y‖ ≤ r := by
    have h := (sq_le_sq.mp hy.1)
    simpa [abs_of_nonneg (norm_nonneg (posPart hk y)), abs_of_nonneg (le_of_lt hr)] using h
  have hbnd₁ : ‖(r⁻¹ • posPart hk y : EuclideanSpace ℝ (Fin (n - k)))‖ ≤ 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (le_of_lt hr))]
    rw [mul_comm, ← div_eq_mul_inv]
    exact (div_le_one hr).mpr hbnd₀
  have hbnd₂ : ‖negPart hk y‖ ≤ Real.sqrt (2 * ε + ‖posPart hk y‖ ^ 2) := by
    have h : |‖negPart hk y‖| ≤ |Real.sqrt (2 * ε + ‖posPart hk y‖ ^ 2)| := by
      exact sq_le_sq.mp (by
        rw [Real.sq_sqrt (by positivity : 0 ≤ 2 * ε + ‖posPart hk y‖ ^ 2)]
        nlinarith [hy.2])
    simpa [abs_of_nonneg (norm_nonneg (negPart hk y)), abs_of_nonneg (Real.sqrt_nonneg _)] using h
  have hbnd₂' : ‖(Real.sqrt (2 * ε + ‖posPart hk y‖ ^ 2))⁻¹ • negPart hk y‖ ≤ 1 := by
    rw [norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr (by positivity : 0 ≤ Real.sqrt (2 * ε + ‖posPart hk y‖ ^ 2)))]
    rw [mul_comm, ← div_eq_mul_inv]
    exact (div_le_one (by positivity : 0 < Real.sqrt (2 * ε + ‖posPart hk y‖ ^ 2))).mpr hbnd₂
  have hb : closedCellClamp (n - k) (r⁻¹ • posPart hk y) =
      (⟨r⁻¹ • posPart hk y, by exact hbnd₁⟩ : ClosedCell (n - k)) := by
    apply Subtype.ext
    dsimp [closedCellClamp]
    have hmax : max ‖(r⁻¹ • posPart hk y : EuclideanSpace ℝ (Fin (n - k)))‖ 1 = 1 := by
      rw [max_eq_right hbnd₁]
    rw [hmax, inv_one, one_smul]
  have ha : closedCellClamp k ((Real.sqrt (2 * ε + ‖posPart hk y‖ ^ 2))⁻¹ • negPart hk y) =
      (⟨(Real.sqrt (2 * ε + ‖posPart hk y‖ ^ 2))⁻¹ • negPart hk y, by exact hbnd₂'⟩ : ClosedCell k) := by
    apply Subtype.ext
    dsimp [closedCellClamp]
    have hmax : max ‖((Real.sqrt (2 * ε + ‖posPart hk y‖ ^ 2))⁻¹ • negPart hk y :
        EuclideanSpace ℝ (Fin k))‖ 1 = 1 := by
      rw [max_eq_right hbnd₂']
    rw [hmax, inv_one, one_smul]
  dsimp [modelHandleMapRawSymm]
  rw [hb, ha]
  dsimp [modelHandleMap]
  have hsqrt : Real.sqrt (2 * ε + r ^ 2 * ‖(r⁻¹ • posPart hk y : EuclideanSpace ℝ (Fin (n - k)))‖ ^ 2) =
      Real.sqrt (2 * ε + ‖posPart hk y‖ ^ 2) := by
    congr 1
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (le_of_lt hr))]
    field_simp [ne_of_gt hr]
  rw [hsqrt]
  have hscalar₁ : Real.sqrt (2 * ε + ‖posPart hk y‖ ^ 2) •
        ((Real.sqrt (2 * ε + ‖posPart hk y‖ ^ 2))⁻¹ • negPart hk y) = negPart hk y := by
    rw [smul_smul]
    rw [mul_inv_cancel₀ (ne_of_gt (by positivity : 0 < Real.sqrt (2 * ε + ‖posPart hk y‖ ^ 2)))]
    rw [one_smul]
  have hscalar₂ : r • (r⁻¹ • posPart hk y) = posPart hk y := by
    rw [smul_smul, mul_inv_cancel₀ (ne_of_gt hr), one_smul]
  rw [hscalar₁, hscalar₂]
  exact recombine_decompose hk y

noncomputable def modelHandleCoreSet {n k : ℕ} (hk : k ≤ n) (ε r : ℝ) :
    Set {y : MorseModel n // y ∈ modelHandle hk ε r} :=
  {y : {y : MorseModel n // y ∈ modelHandle hk ε r} |
    y.1 ∈ modelHandleMap hk ε r '' (coreDisk k (n - k) : Set (StandardHandle k (n - k)))}

noncomputable def modelHandleCoreMap {n k : ℕ} (hk : k ≤ n) (ε r : ℝ)
    (y : MorseModel n) : MorseModel n :=
  modelHandleMap hk ε r ((coreRetract k (n - k)).retraction (modelHandleMapRawSymm hk ε r y))

noncomputable def modelHandleCoreHomotopyValue {n k : ℕ} (hk : k ≤ n) (ε r : ℝ)
    (q : unitInterval × MorseModel n) : MorseModel n :=
  modelHandleMap hk ε r ((coreRetract k (n - k)).homotopy (q.1, modelHandleMapRawSymm hk ε r q.2))

theorem modelHandleCoreHomotopyValue_zero {n k : ℕ} (hk : k ≤ n) (ε r : ℝ)
    (hε : 0 < ε) (hr : 0 < r) (y : MorseModel n) (hy : y ∈ modelHandle hk ε r) :
    modelHandleCoreHomotopyValue hk ε r (0, y) = y := by
  have hh : modelHandleCoreHomotopyValue hk ε r (0, y) =
      modelHandleMap hk ε r (modelHandleMapRawSymm hk ε r y) := by
    dsimp [modelHandleCoreHomotopyValue]
    exact congrArg (modelHandleMap hk ε r)
      ((coreRetract k (n - k)).homotopy.map_zero_left (modelHandleMapRawSymm hk ε r y))
  rw [hh]
  exact modelHandleMapRawSymm_map hk ε r hε hr y hy

theorem modelHandleCoreHomotopyValue_one {n k : ℕ} (hk : k ≤ n) (ε r : ℝ)
    (y : MorseModel n) :
    modelHandleCoreHomotopyValue hk ε r (1, y) = modelHandleCoreMap hk ε r y := by
  have hh : modelHandleCoreHomotopyValue hk ε r (1, y) =
      modelHandleMap hk ε r ((coreRetract k (n - k)).retraction (modelHandleMapRawSymm hk ε r y) : StandardHandle k (n - k)) := by
    dsimp [modelHandleCoreHomotopyValue]
    exact congrArg (modelHandleMap hk ε r)
      ((coreRetract k (n - k)).homotopy.map_one_left (modelHandleMapRawSymm hk ε r y))
  dsimp [modelHandleCoreMap]
  rw [hh]

theorem continuous_modelHandleCoreHomotopyValue {n k : ℕ} (hk : k ≤ n) (ε r : ℝ)
    (hε : 0 < ε) :
    Continuous (modelHandleCoreHomotopyValue hk ε r) := by
  change Continuous (fun q : unitInterval × MorseModel n =>
    modelHandleMap hk ε r ((coreRetract k (n - k)).homotopy (q.1, modelHandleMapRawSymm hk ε r q.2)))
  have hsnd : Continuous (fun q : unitInterval × MorseModel n => modelHandleMapRawSymm hk ε r q.2) :=
    (continuous_modelHandleMapRawSymm hk ε r hε).comp continuous_snd
  have hpair : Continuous (fun q : unitInterval × MorseModel n =>
      (q.1, modelHandleMapRawSymm hk ε r q.2)) :=
    continuous_fst.prodMk hsnd
  have hstep : Continuous (fun q : unitInterval × MorseModel n =>
      ((coreRetract k (n - k)).homotopy (q.1, modelHandleMapRawSymm hk ε r q.2) : StandardHandle k (n - k))) := by
    have hcoerce : Continuous (fun d : StandardHandle k (n - k) => d) := continuous_id
    exact hcoerce.comp ((coreRetract k (n - k)).homotopy.continuous.comp hpair)
  exact (continuous_modelHandleMap hk ε r).comp hstep

theorem modelHandleCoreMapRawSymm_eq {n k : ℕ} (hk : k ≤ n) (ε r : ℝ)
    (hε : 0 < ε) (hr : 0 < r) (d : StandardHandle k (n - k)) :
    modelHandleMapRawSymm hk ε r (modelHandleMap hk ε r d) = d := by
  have hmem : modelHandleMap hk ε r d ∈ modelHandle hk ε r :=
    modelHandleMap_mem hk ε r (le_of_lt hε) d
  have hback : modelHandleMap hk ε r (modelHandleMapRawSymm hk ε r (modelHandleMap hk ε r d)) =
      modelHandleMap hk ε r d :=
    modelHandleMapRawSymm_map hk ε r hε hr (modelHandleMap hk ε r d) hmem
  exact modelHandleMap_injective hk ε r hε (ne_of_gt hr) (by
    exact hback)

theorem modelHandleCoreHomotopyValue_fixed {n k : ℕ} (hk : k ≤ n) (ε r : ℝ)
    (hε : 0 < ε) (hr : 0 < r) (t : unitInterval) (y : MorseModel n)
    (hy : y ∈ modelHandleMap hk ε r '' (coreDisk k (n - k) : Set (StandardHandle k (n - k)))) :
    modelHandleCoreHomotopyValue hk ε r (t, y) = y := by
  rcases hy with ⟨d, hd, hdy⟩
  have hraw : modelHandleMapRawSymm hk ε r y = d := by
    rw [← hdy]
    exact modelHandleCoreMapRawSymm_eq hk ε r hε hr d
  have hfix : (coreRetract k (n - k)).homotopy (t, d) = d := by
    exact (coreRetract k (n - k)).homotopy.eq_fst t (by
      exact hd)
  dsimp [modelHandleCoreHomotopyValue]
  rw [hraw, hfix, hdy]

noncomputable def modelHandleCoreRetraction {n k : ℕ} (hk : k ≤ n) (ε r : ℝ)
    (hε : 0 < ε) :
    C({y : MorseModel n // y ∈ modelHandle hk ε r},
      {y : {y : MorseModel n // y ∈ modelHandle hk ε r} // y ∈ modelHandleCoreSet hk ε r}) := by
  let X : Type := {y : MorseModel n // y ∈ modelHandle hk ε r}
  have hmem : ∀ y : X, modelHandleCoreMap hk ε r y.1 ∈ modelHandle hk ε r := by
    intro y
    dsimp [modelHandleCoreMap]
    exact modelHandleMap_mem hk ε r (le_of_lt hε)
      ((coreRetract k (n - k)).retraction (modelHandleMapRawSymm hk ε r y.1))
  have hcore : ∀ y : X, modelHandleCoreMap hk ε r y.1 ∈
      modelHandleMap hk ε r '' (coreDisk k (n - k) : Set (StandardHandle k (n - k))) := by
    intro y
    dsimp [modelHandleCoreMap]
    refine ⟨(coreRetract k (n - k)).retraction (modelHandleMapRawSymm hk ε r y.1), ?_, rfl⟩
    exact ((coreRetract k (n - k)).retraction (modelHandleMapRawSymm hk ε r y.1)).2
  have hcont : Continuous (fun y : X => modelHandleCoreMap hk ε r y.1) := by
    have hinner : Continuous (fun y : X =>
        ((coreRetract k (n - k)).retraction (modelHandleMapRawSymm hk ε r y.1) : StandardHandle k (n - k))) := by
      have hcoerce : Continuous (fun d : coreDisk k (n - k) => (d : StandardHandle k (n - k))) :=
        continuous_subtype_val
      exact hcoerce.comp (((coreRetract k (n - k)).retraction.continuous.comp
        (continuous_modelHandleMapRawSymm hk ε r hε)).comp continuous_subtype_val)
    exact (continuous_modelHandleMap hk ε r).comp hinner
  exact ContinuousMap.mk (fun y : X => ⟨⟨modelHandleCoreMap hk ε r y.1, hmem y⟩, hcore y⟩)
    (Continuous.subtype_mk (Continuous.subtype_mk hcont hmem) hcore)

theorem modelHandleMap_core_eq_cellMap {n k : ℕ} (hk : k ≤ n) (ε r : ℝ)
    (x : ClosedCell k) :
    modelHandleMap hk ε r (x, (⟨(0 : EuclideanSpace ℝ (Fin (n - k))), by simp⟩ : ClosedCell (n - k))) =
      cellMap (Real.sqrt (2 * ε)) (x : EuclideanSpace ℝ (Fin k)) := by
  have hsqrt : Real.sqrt (2 * ε + r ^ 2 * ‖(0 : EuclideanSpace ℝ (Fin (n - k)))‖ ^ 2) =
      Real.sqrt (2 * ε) := by
    simp
  dsimp [modelHandleMap, cellMap]
  rw [hsqrt]
  ext i
  by_cases h : i.val < k
  · simp [cellMap, h, recombine]
  · simp [cellMap, h, recombine]

theorem modelHandleMap_coreDisk_image_eq {n k : ℕ} (hk : k ≤ n) (ε r : ℝ) :
    modelHandleMap hk ε r '' (coreDisk k (n - k) : Set (StandardHandle k (n - k))) =
      Set.range (fun x : ClosedCell k => cellMap (Real.sqrt (2 * ε)) (x : EuclideanSpace ℝ (Fin k))) := by
  ext y
  constructor
  · intro hy
    rcases hy with ⟨d, hd, hdy⟩
    have hx0 : (d.2 : EuclideanSpace ℝ (Fin (n - k))) = 0 := by
      have hx0' : d.2 = closedCellCenter (n - k) := by
        simpa [coreDisk] using hd
      have hval : (closedCellCenter (n - k) : EuclideanSpace ℝ (Fin (n - k))) = 0 := rfl
      simp [hx0', hval]
    let x : ClosedCell k := d.1
    have hd_eq : d = (x, closedCellCenter (n - k)) := by
      apply Prod.ext
      · rfl
      · apply Subtype.ext
        exact hx0
    refine ⟨x, ?_⟩
    calc
      cellMap (Real.sqrt (2 * ε)) (x : EuclideanSpace ℝ (Fin k)) = modelHandleMap hk ε r d := by
        rw [hd_eq]
        exact (modelHandleMap_core_eq_cellMap hk ε r x).symm
      _ = y := hdy
  · intro hy
    rcases hy with ⟨x, hx⟩
    let d : StandardHandle k (n - k) :=
      (x, (⟨(0 : EuclideanSpace ℝ (Fin (n - k))), by simp⟩ : ClosedCell (n - k)))
    refine ⟨d, ?_, ?_⟩
    · dsimp [d, coreDisk, closedCellCenter]
    · dsimp [d]
      exact (modelHandleMap_core_eq_cellMap hk ε r x).trans hx

noncomputable def modelHandleCoreHomotopy {n k : ℕ} (hk : k ≤ n) (ε r : ℝ)
    (hε : 0 < ε) (hr : 0 < r) :
    ContinuousMap.HomotopyRel (ContinuousMap.id {y : MorseModel n // y ∈ modelHandle hk ε r})
      (((ContinuousMap.id {y : MorseModel n // y ∈ modelHandle hk ε r}).restrict (modelHandleCoreSet hk ε r)).comp
        (modelHandleCoreRetraction hk ε r hε)) (modelHandleCoreSet hk ε r) := by
  let X : Type := {y : MorseModel n // y ∈ modelHandle hk ε r}
  let A : Set X := modelHandleCoreSet hk ε r
  let H : C(unitInterval × X, X) := by
    refine ⟨fun q => ⟨modelHandleCoreHomotopyValue hk ε r (q.1, q.2.1), ?_⟩, ?_⟩
    · dsimp [modelHandleCoreHomotopyValue]
      exact modelHandleMap_mem hk ε r (le_of_lt hε)
        ((coreRetract k (n - k)).homotopy (q.1, modelHandleMapRawSymm hk ε r q.2.1))
    · have hcont : Continuous (fun q : unitInterval × X => modelHandleCoreHomotopyValue hk ε r (q.1, q.2.1)) := by
        have hstep := continuous_modelHandleCoreHomotopyValue hk ε r hε
        have hpair : Continuous (fun q : unitInterval × X => (q.1, q.2.1)) :=
          continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)
        exact hstep.comp hpair
      exact Continuous.subtype_mk hcont (fun q => by
        dsimp [modelHandleCoreHomotopyValue]
        exact modelHandleMap_mem hk ε r (le_of_lt hε)
          ((coreRetract k (n - k)).homotopy (q.1, modelHandleMapRawSymm hk ε r q.2.1)))
  refine ⟨⟨H, ?_, ?_⟩, ?_⟩
  · intro x
    apply Subtype.ext
    change modelHandleCoreHomotopyValue hk ε r (0, x.1) = x.1
    exact modelHandleCoreHomotopyValue_zero hk ε r hε hr x.1 x.2
  · intro x
    apply Subtype.ext
    change modelHandleCoreHomotopyValue hk ε r (1, x.1) = (modelHandleCoreRetraction hk ε r hε x : X).1
    dsimp [modelHandleCoreRetraction, modelHandleCoreMap]
    exact modelHandleCoreHomotopyValue_one hk ε r x.1
  · intro t x hx
    apply Subtype.ext
    change modelHandleCoreHomotopyValue hk ε r (t, x.1) = x.1
    exact modelHandleCoreHomotopyValue_fixed hk ε r hε hr t x.1 (by
      exact hx)

noncomputable def modelHandleCoreRetract {n k : ℕ} (hk : k ≤ n) (ε r : ℝ)
    (hε : 0 < ε) (hr : 0 < r) :
    StrongDeformationRetract (modelHandleCoreSet hk ε r) where
  retraction := modelHandleCoreRetraction hk ε r hε
  homotopy := modelHandleCoreHomotopy hk ε r hε hr

theorem modelHandleMapRawSymm_eq_symm {m k : ℕ} (hk : k ≤ m + 1) (ε r : ℝ)
    (hε : 0 < ε) (hr : 0 < r) (y : MorseModel (m + 1)) (hy : y ∈ modelHandle hk ε r) :
    modelHandleMapRawSymm hk ε r y =
      (morseModelHandleMapHomeo hk ε r hε hr).symm ⟨y, hy⟩ := by
  apply modelHandleMap_injective hk ε r hε (ne_of_gt hr)
  rw [modelHandleMapRawSymm_map hk ε r hε hr y hy]
  exact (morseModelHandleMapHomeo_symm_apply hk ε r hε hr ⟨y, hy⟩).symm

noncomputable def morseBeltCellMapClamped {m k : ℕ} (hk : k ≤ m + 1) (c ε r : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} {f : M → ℝ}
    (data : MorseChart (m + 1) k hk c I f)
    (hε : 0 < ε) (hεr' : Real.sqrt (2 * ε + 2 * r ^ 2) < data.R)
    (y : {y' : morseUpperSublevel hk c r // y' ∈ morseBeltImage hk c ε r data}) :
    {z : Handle.AdjunctionSpace k (m + 1 - k)
      (morseAttachingEmbedding hk c ε r data hε (le_of_lt hεr')) //
        z ∈ morseBeltOpenSet hk c ε r data hε (le_of_lt hεr')} := by
  let d : StandardHandle k (m + 1 - k) := modelHandleMapRawSymm hk ε r (y.1 : MorseModel (m + 1))
  have hd : morseNorm (m + 1) (modelHandleMap hk ε r d) < data.R := by
    dsimp [d]
    exact lt_of_le_of_lt (modelHandleMap_norm_le hk ε r (le_of_lt hε)
      (modelHandleMapRawSymm hk ε r (y.1 : MorseModel (m + 1)))) hεr'
  exact ⟨Handle.cell (morseAttachingEmbedding hk c ε r data hε (le_of_lt hεr')) d,
    Or.inr ⟨d, hd, rfl⟩⟩

theorem continuous_morseBeltCellMapClamped {m k : ℕ} (hk : k ≤ m + 1) (c ε r : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} {f : M → ℝ}
    (data : MorseChart (m + 1) k hk c I f)
    (hε : 0 < ε) (hεr' : Real.sqrt (2 * ε + 2 * r ^ 2) < data.R) :
    Continuous (morseBeltCellMapClamped hk c ε r data hε hεr') := by
  have hproj : Continuous (fun y : {y' : morseUpperSublevel hk c r // y' ∈ morseBeltImage hk c ε r data} =>
      (y.1 : MorseModel (m + 1))) := by
    exact continuous_subtype_val.comp continuous_subtype_val
  have hraw : Continuous (modelHandleMapRawSymm hk ε r) := by
    dsimp [modelHandleMapRawSymm]
    refine Continuous.prodMk ?_ ?_
    · exact (continuous_closedCellClamp k).comp (by
        have hsqrt : Continuous (fun y : MorseModel (m + 1) =>
            (Real.sqrt (2 * ε + ‖posPart hk y‖ ^ 2))⁻¹) := by
          refine Continuous.inv₀ ?_ (fun y => ?_)
          · exact Real.continuous_sqrt.comp (by
              have hnorm : Continuous (fun y : MorseModel (m + 1) => ‖posPart hk y‖) :=
                continuous_norm.comp (continuous_posPart hk)
              have hpow : Continuous (fun y : MorseModel (m + 1) => ‖posPart hk y‖ ^ 2) := hnorm.pow 2
              exact (continuous_const.add hpow : Continuous (fun y : MorseModel (m + 1) =>
                2 * ε + ‖posPart hk y‖ ^ 2)))
          · exact ne_of_gt (by positivity : 0 < Real.sqrt (2 * ε + ‖posPart hk y‖ ^ 2))
        exact hsqrt.smul (continuous_negPart hk))
    · exact (continuous_closedCellClamp (m + 1 - k)).comp (by
        have hscalar : Continuous (fun _ : MorseModel (m + 1) => (r⁻¹ : ℝ)) := continuous_const
        exact hscalar.smul (continuous_posPart hk))
  have hmain : Continuous (fun y : {y' : morseUpperSublevel hk c r // y' ∈ morseBeltImage hk c ε r data} =>
      Handle.cell (morseAttachingEmbedding hk c ε r data hε (le_of_lt hεr'))
        (modelHandleMapRawSymm hk ε r (y.1 : MorseModel (m + 1)))) := by
    exact (continuous_cell (morseAttachingEmbedding hk c ε r data hε (le_of_lt hεr'))).comp (hraw.comp hproj)
  exact Continuous.subtype_mk hmain (fun y => Or.inr ⟨modelHandleMapRawSymm hk ε r (y.1 : MorseModel (m + 1)), by
    exact lt_of_le_of_lt (modelHandleMap_norm_le hk ε r (le_of_lt hε)
      (modelHandleMapRawSymm hk ε r (y.1 : MorseModel (m + 1)))) hεr', rfl⟩)

noncomputable def morseBeltMapOnOpen_inv {m k : ℕ} (hk : k ≤ m + 1) (c ε r : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} {f : M → ℝ}
    (data : MorseChart (m + 1) k hk c I f)
    (hε : 0 < ε) (hεr' : Real.sqrt (2 * ε + 2 * r ^ 2) < data.R) (hr : 0 < r)
    (y : {y' : morseUpperSublevel hk c r // y' ∈ morseBeltImage hk c ε r data}) :
    {z : Handle.AdjunctionSpace k (m + 1 - k)
      (morseAttachingEmbedding hk c ε r data hε (le_of_lt hεr')) //
        z ∈ morseBeltOpenSet hk c ε r data hε (le_of_lt hεr')} := by
  classical
  by_cases hy' : morseNormalForm hk c (y.1 : MorseModel (m + 1)) ≤ c - ε
  · have hsrc : (y.1 : MorseModel (m + 1)) ∈ data.χ.source :=
      data.hχsrc (y.1 : MorseModel (m + 1)) (le_of_lt y.2.1)
    have hsub : f (data.χ (y.1 : MorseModel (m + 1))) ≤ c - ε := by
      rw [data.hnorm (y.1 : MorseModel (m + 1)) (le_of_lt y.2.1)]
      exact hy'
    let x : SublevelSpace f (c - ε) := ⟨data.χ (y.1 : MorseModel (m + 1)), hsub⟩
    have hx : x ∈ morseBeltLowerSet hk c ε data := by
      dsimp [morseBeltLowerSet, x]
      exact ⟨(y.1 : MorseModel (m + 1)), y.2.1, rfl⟩
    exact ⟨Handle.lower (morseAttachingEmbedding hk c ε r data hε (le_of_lt hεr')) x,
      Or.inl ⟨x, hx, rfl⟩⟩
  · have hcell : (y.1 : MorseModel (m + 1)) ∈ modelHandle hk ε r := by
      rcases y.2.2 with hlow | hc'
      · exact False.elim (hy' hlow)
      · exact hc'
    let d : StandardHandle k (m + 1 - k) :=
      (morseModelHandleMapHomeo hk ε r hε hr).symm ⟨(y.1 : MorseModel (m + 1)), hcell⟩
    have hd : morseNorm (m + 1) (modelHandleMap hk ε r d) < data.R := by
      dsimp [d]
      rw [morseModelHandleMapHomeo_symm_apply hk ε r hε hr]
      exact y.2.1
    exact ⟨Handle.cell (morseAttachingEmbedding hk c ε r data hε (le_of_lt hεr')) d,
      Or.inr ⟨d, hd, rfl⟩⟩

theorem morseBeltMapOnOpen_right_inv {m k : ℕ} (hk : k ≤ m + 1) (c ε r : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} {f : M → ℝ}
    (data : MorseChart (m + 1) k hk c I f)
    (hε : 0 < ε) (hεr' : Real.sqrt (2 * ε + 2 * r ^ 2) < data.R) (hr : 0 < r)
    (y : {y' : morseUpperSublevel hk c r // y' ∈ morseBeltImage hk c ε r data}) :
    morseBeltMapOnOpen hk c ε r data hε hεr' (morseBeltMapOnOpen_inv hk c ε r data hε hεr' hr y) =
      y := by
  classical
  dsimp [morseBeltMapOnOpen_inv]
  by_cases hy' : morseNormalForm hk c (y.1 : MorseModel (m + 1)) ≤ c - ε
  · rw [dif_pos hy']
    let x : SublevelSpace f (c - ε) := ⟨data.χ (y.1 : MorseModel (m + 1)), by
      change f (data.χ (y.1 : MorseModel (m + 1))) ≤ c - ε
      rw [data.hnorm (y.1 : MorseModel (m + 1)) (le_of_lt y.2.1)]
      exact hy'⟩
    have hx : x ∈ morseBeltLowerSet hk c ε data := by
      dsimp [morseBeltLowerSet, x]
      exact ⟨(y.1 : MorseModel (m + 1)), y.2.1, rfl⟩
    apply Subtype.ext
    change (morseBeltMapOnOpen hk c ε r data hε hεr'
      ⟨Handle.lower (morseAttachingEmbedding hk c ε r data hε (le_of_lt hεr'))
        x, Or.inl ⟨x, hx, rfl⟩⟩ :
          MorseModel (m + 1)) = (y.1 : MorseModel (m + 1))
    rw [morseBeltMapOnOpen_lower hk c ε r data hε hεr' x hx]
    dsimp [x]
    exact data.χ.left_inv (data.hχsrc (y.1 : MorseModel (m + 1)) (le_of_lt y.2.1))
  · rw [dif_neg hy']
    have hc' : (y.1 : MorseModel (m + 1)) ∈ modelHandle hk ε r := by
      rcases y.2.2 with hlow | hc'
      · exact False.elim (hy' hlow)
      · exact hc'
    let d : StandardHandle k (m + 1 - k) :=
      (morseModelHandleMapHomeo hk ε r hε hr).symm ⟨(y.1 : MorseModel (m + 1)), hc'⟩
    have hd : morseNorm (m + 1) (modelHandleMap hk ε r d) < data.R := by
      dsimp [d]
      rw [morseModelHandleMapHomeo_symm_apply hk ε r hε hr]
      exact y.2.1
    apply Subtype.ext
    change (morseBeltMapOnOpen hk c ε r data hε hεr'
      ⟨Handle.cell (morseAttachingEmbedding hk c ε r data hε (le_of_lt hεr')) d,
        Or.inr ⟨d, hd, rfl⟩⟩ :
          MorseModel (m + 1)) = (y.1 : MorseModel (m + 1))
    rw [morseBeltMapOnOpen_cell hk c ε r data hε hεr' d hd]
    dsimp [d]
    exact morseModelHandleMapHomeo_symm_apply hk ε r hε hr
      ⟨(y.1 : MorseModel (m + 1)), hc'⟩

theorem morseBeltMapOnOpen_left_inv {m k : ℕ} (hk : k ≤ m + 1) (c ε r : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} {f : M → ℝ}
    (data : MorseChart (m + 1) k hk c I f)
    (hε : 0 < ε) (hεr' : Real.sqrt (2 * ε + 2 * r ^ 2) < data.R) (hr : 0 < r)
    (hcont : Continuous f)
    (z : {z' : Handle.AdjunctionSpace k (m + 1 - k)
      (morseAttachingEmbedding hk c ε r data hε (le_of_lt hεr')) //
        z' ∈ morseBeltOpenSet hk c ε r data hε (le_of_lt hεr')}) :
    morseBeltMapOnOpen_inv hk c ε r data hε hεr' hr
      ⟨morseBeltMapOnOpen hk c ε r data hε hεr' z,
        morseBeltMapOnOpen_mem_image hk c ε r data hε hεr' z⟩ = z := by
  apply morseBeltMapOnOpen_injective hk c ε r data hε (ne_of_gt hr) hεr' hcont
  simpa using (morseBeltMapOnOpen_right_inv hk c ε r data hε hεr' hr
    ⟨morseBeltMapOnOpen hk c ε r data hε hεr' z,
      morseBeltMapOnOpen_mem_image hk c ε r data hε hεr' z⟩)

noncomputable def morseBeltLowerMap {m k : ℕ} (hk : k ≤ m + 1) (c ε r : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} {f : M → ℝ}
    (data : MorseChart (m + 1) k hk c I f)
    (hε : 0 < ε) (hεr' : Real.sqrt (2 * ε + 2 * r ^ 2) < data.R)
    (y : {y' : morseUpperSublevel hk c r // y' ∈ morseBeltImage hk c ε r data})
    (hy : morseNormalForm hk c (y.1 : MorseModel (m + 1)) ≤ c - ε) :
    {z : Handle.AdjunctionSpace k (m + 1 - k)
      (morseAttachingEmbedding hk c ε r data hε (le_of_lt hεr')) //
        z ∈ morseBeltOpenSet hk c ε r data hε (le_of_lt hεr')} :=
  ⟨Handle.lower (morseAttachingEmbedding hk c ε r data hε (le_of_lt hεr'))
    (⟨data.χ (y.1 : MorseModel (m + 1)), by
      change f (data.χ (y.1 : MorseModel (m + 1))) ≤ c - ε
      rw [data.hnorm (y.1 : MorseModel (m + 1)) (le_of_lt y.2.1)]
      exact hy⟩ : SublevelSpace f (c - ε)),
    Or.inl ⟨⟨data.χ (y.1 : MorseModel (m + 1)), by
      change f (data.χ (y.1 : MorseModel (m + 1))) ≤ c - ε
      rw [data.hnorm (y.1 : MorseModel (m + 1)) (le_of_lt y.2.1)]
      exact hy⟩, by
        dsimp [morseBeltLowerSet]
        exact ⟨(y.1 : MorseModel (m + 1)), y.2.1, rfl⟩, rfl⟩⟩

noncomputable def morseBeltCellMap {m k : ℕ} (hk : k ≤ m + 1) (c ε r : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} {f : M → ℝ}
    (data : MorseChart (m + 1) k hk c I f)
    (hε : 0 < ε) (hεr' : Real.sqrt (2 * ε + 2 * r ^ 2) < data.R) (hr : 0 < r)
    (y : {y' : morseUpperSublevel hk c r // y' ∈ morseBeltImage hk c ε r data})
    (hy : (y.1 : MorseModel (m + 1)) ∈ modelHandle hk ε r) :
    {z : Handle.AdjunctionSpace k (m + 1 - k)
      (morseAttachingEmbedding hk c ε r data hε (le_of_lt hεr')) //
        z ∈ morseBeltOpenSet hk c ε r data hε (le_of_lt hεr')} := by
  let d : StandardHandle k (m + 1 - k) :=
    (morseModelHandleMapHomeo hk ε r hε hr).symm ⟨(y.1 : MorseModel (m + 1)), hy⟩
  have hd : morseNorm (m + 1) (modelHandleMap hk ε r d) < data.R := by
    dsimp [d]
    rw [morseModelHandleMapHomeo_symm_apply hk ε r hε hr]
    exact y.2.1
  exact ⟨Handle.cell (morseAttachingEmbedding hk c ε r data hε (le_of_lt hεr')) d,
    Or.inr ⟨d, hd, rfl⟩⟩

theorem morseBeltMapOnOpen_inv_eq_lower {m k : ℕ} (hk : k ≤ m + 1) (c ε r : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} {f : M → ℝ}
    (data : MorseChart (m + 1) k hk c I f)
    (hε : 0 < ε) (hεr' : Real.sqrt (2 * ε + 2 * r ^ 2) < data.R) (hr : 0 < r)
    (y : {y' : morseUpperSublevel hk c r // y' ∈ morseBeltImage hk c ε r data})
    (hy : morseNormalForm hk c (y.1 : MorseModel (m + 1)) ≤ c - ε) :
    morseBeltMapOnOpen_inv hk c ε r data hε hεr' hr y =
      morseBeltLowerMap hk c ε r data hε hεr' y hy := by
  classical
  dsimp [morseBeltMapOnOpen_inv, morseBeltLowerMap]
  rw [dif_pos hy]

theorem continuousOn_morseBeltMapOnOpen_inv_lower {m k : ℕ} (hk : k ≤ m + 1) (c ε r : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} {f : M → ℝ}
    (data : MorseChart (m + 1) k hk c I f)
    (hε : 0 < ε) (hεr' : Real.sqrt (2 * ε + 2 * r ^ 2) < data.R) (hr : 0 < r) :
    ContinuousOn (morseBeltMapOnOpen_inv hk c ε r data hε hεr' hr)
      {y : {y' : morseUpperSublevel hk c r // y' ∈ morseBeltImage hk c ε r data} |
        morseNormalForm hk c (y.1 : MorseModel (m + 1)) ≤ c - ε} := by
  let S : Set {y' : morseUpperSublevel hk c r // y' ∈ morseBeltImage hk c ε r data} :=
    {y : {y' : morseUpperSublevel hk c r // y' ∈ morseBeltImage hk c ε r data} |
      morseNormalForm hk c (y.1 : MorseModel (m + 1)) ≤ c - ε}
  let g : S → {z : Handle.AdjunctionSpace k (m + 1 - k)
      (morseAttachingEmbedding hk c ε r data hε (le_of_lt hεr')) //
        z ∈ morseBeltOpenSet hk c ε r data hε (le_of_lt hεr')} :=
    fun y => morseBeltLowerMap hk c ε r data hε hεr'
      (y : {y' : morseUpperSublevel hk c r // y' ∈ morseBeltImage hk c ε r data}) y.2
  have hmain : Continuous (fun y : S => data.χ (y.1.1 : MorseModel (m + 1))) := by
    have hinner : Continuous (fun y : S => (y.1.1 : MorseModel (m + 1))) := by
      exact continuous_subtype_val.comp (continuous_subtype_val.comp continuous_subtype_val)
    have hmaps : Set.MapsTo (fun y : S => (y.1.1 : MorseModel (m + 1))) Set.univ data.χ.source := by
      intro y hy
      exact data.hχsrc (y.1.1 : MorseModel (m + 1)) (le_of_lt y.1.2.1)
    exact (continuousOn_univ.mp (data.χ.continuousOn_toFun.comp hinner.continuousOn hmaps))
  have hmain2 : Continuous (fun y : S =>
      Handle.lower (morseAttachingEmbedding hk c ε r data hε (le_of_lt hεr'))
        (⟨data.χ (y.1.1 : MorseModel (m + 1)), by
          change f (data.χ (y.1.1 : MorseModel (m + 1))) ≤ c - ε
          rw [data.hnorm (y.1.1 : MorseModel (m + 1)) (le_of_lt y.1.2.1)]
          exact y.2⟩ : SublevelSpace f (c - ε))) := by
    exact (continuous_lower (morseAttachingEmbedding hk c ε r data hε (le_of_lt hεr'))).comp
      (Continuous.subtype_mk hmain (fun y => by
        change f (data.χ (y.1.1 : MorseModel (m + 1))) ≤ c - ε
        rw [data.hnorm (y.1.1 : MorseModel (m + 1)) (le_of_lt y.1.2.1)]
        exact y.2))
  have hg : Continuous g := by
    dsimp [g]
    exact Continuous.subtype_mk hmain2 (fun y => Or.inl ⟨⟨data.χ (y.1.1 : MorseModel (m + 1)), by
      change f (data.χ (y.1.1 : MorseModel (m + 1))) ≤ c - ε
      rw [data.hnorm (y.1.1 : MorseModel (m + 1)) (le_of_lt y.1.2.1)]
      exact y.2⟩, by
        dsimp [morseBeltLowerSet]
        exact ⟨(y.1.1 : MorseModel (m + 1)), y.1.2.1, rfl⟩, rfl⟩)
  have hmain : ContinuousOn (fun y : S =>
      morseBeltMapOnOpen_inv hk c ε r data hε hεr' hr
        (y : {y' : morseUpperSublevel hk c r // y' ∈ morseBeltImage hk c ε r data})) Set.univ := by
    refine (continuousOn_congr (s := Set.univ)
      (g := fun y : S => morseBeltMapOnOpen_inv hk c ε r data hε hεr' hr
        (y : {y' : morseUpperSublevel hk c r // y' ∈ morseBeltImage hk c ε r data}))
      (f := g) ?_).mpr hg.continuousOn
    intro y hy
    dsimp [g]
    exact morseBeltMapOnOpen_inv_eq_lower hk c ε r data hε hεr' hr
      (y : {y' : morseUpperSublevel hk c r // y' ∈ morseBeltImage hk c ε r data}) y.2
  rw [continuousOn_iff_continuous_restrict]
  simpa [S] using (continuousOn_univ.mp hmain)

theorem morseBeltMapOnOpen_inv_eq_cell_strict {m k : ℕ} (hk : k ≤ m + 1) (c ε r : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} {f : M → ℝ}
    (data : MorseChart (m + 1) k hk c I f)
    (hε : 0 < ε) (hεr' : Real.sqrt (2 * ε + 2 * r ^ 2) < data.R) (hr : 0 < r)
    (y : {y' : morseUpperSublevel hk c r // y' ∈ morseBeltImage hk c ε r data})
    (hy : (y.1 : MorseModel (m + 1)) ∈ modelHandle hk ε r)
    (hgt : c - ε < morseNormalForm hk c (y.1 : MorseModel (m + 1))) :
    morseBeltMapOnOpen_inv hk c ε r data hε hεr' hr y =
      morseBeltCellMap hk c ε r data hε hεr' hr y hy := by
  classical
  dsimp [morseBeltMapOnOpen_inv, morseBeltCellMap]
  rw [dif_neg (not_le_of_gt hgt)]

theorem morseBeltCellMap_eq_lower {m k : ℕ} (hk : k ≤ m + 1) (c ε r : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} {f : M → ℝ}
    (data : MorseChart (m + 1) k hk c I f)
    (hε : 0 < ε) (hεr' : Real.sqrt (2 * ε + 2 * r ^ 2) < data.R) (hr : 0 < r)
    (y : {y' : morseUpperSublevel hk c r // y' ∈ morseBeltImage hk c ε r data})
    (hy : (y.1 : MorseModel (m + 1)) ∈ modelHandle hk ε r)
    (hbound : morseNormalForm hk c (y.1 : MorseModel (m + 1)) = c - ε) :
    morseBeltCellMap hk c ε r data hε hεr' hr y hy =
      morseBeltLowerMap hk c ε r data hε hεr' y (le_of_eq hbound) := by
  let d : StandardHandle k (m + 1 - k) :=
    (morseModelHandleMapHomeo hk ε r hε hr).symm ⟨(y.1 : MorseModel (m + 1)), hy⟩
  have hd : morseNorm (m + 1) (modelHandleMap hk ε r d) < data.R := by
    dsimp [d]
    rw [morseModelHandleMapHomeo_symm_apply hk ε r hε hr]
    exact y.2.1
  have hy' : (y.1 : MorseModel (m + 1)) ∈ Set.range (modelHandleMap hk ε r) := by
    simpa [← modelHandleMap_range hk ε r hε hr] using hy
  rcases hy' with ⟨d₀, hd₀⟩
  have hd₀n : ‖(d₀.1 : EuclideanSpace ℝ (Fin k))‖ = 1 := by
    have hf : morseNormalForm hk c (modelHandleMap hk ε r d₀) = c - ε := by
      rw [hd₀]
      exact hbound
    exact (modelHandleMap_f_eq_lower_iff hk c ε r hε d₀).1 hf
  let u₀ : CellBoundary k := ⟨(d₀.1 : EuclideanSpace ℝ (Fin k)), hd₀n⟩
  let a₀ : AttachingRegion k (m + 1 - k) := (u₀, d₀.2)
  have hd₀i : d₀ = attachingInclusion k (m + 1 - k) a₀ := by
    dsimp [a₀, u₀]
    apply Prod.ext
    · apply Subtype.ext
      rfl
    · rfl
  have hd_eq : d = d₀ := by
    dsimp [d]
    calc
      (morseModelHandleMapHomeo hk ε r hε hr).symm ⟨(y.1 : MorseModel (m + 1)), hy⟩ =
          (morseModelHandleMapHomeo hk ε r hε hr).symm
            ⟨modelHandleMap hk ε r d₀, modelHandleMap_mem hk ε r (le_of_lt hε) d₀⟩ := by
        congr 1
        apply Subtype.ext
        exact hd₀.symm
      _ = (morseModelHandleMapHomeo hk ε r hε hr).symm
            ((morseModelHandleMapHomeo hk ε r hε hr) d₀) := by
        rfl
      _ = d₀ := (morseModelHandleMapHomeo hk ε r hε hr).symm_apply_apply d₀
  have hφ : (morseAttachingEmbedding hk c ε r data hε (le_of_lt hεr') a₀ : M) =
      data.χ (y.1 : MorseModel (m + 1)) := by
    rw [morseAttachingEmbedding_eq_handleEmbedding hk c ε r data hε (le_of_lt hεr') a₀]
    change data.χ (modelHandleMap hk ε r (attachingInclusion k (m + 1 - k) a₀)) =
      data.χ (y.1 : MorseModel (m + 1))
    simp [← hd₀i, hd₀]
  have hcell : Handle.cell (morseAttachingEmbedding hk c ε r data hε (le_of_lt hεr')) d =
      Handle.lower (morseAttachingEmbedding hk c ε r data hε (le_of_lt hεr'))
        (⟨data.χ (y.1 : MorseModel (m + 1)), by
          change f (data.χ (y.1 : MorseModel (m + 1))) ≤ c - ε
          rw [data.hnorm (y.1 : MorseModel (m + 1)) (le_of_lt y.2.1)]
          exact le_of_eq hbound⟩ : SublevelSpace f (c - ε)) := by
    calc
      Handle.cell (morseAttachingEmbedding hk c ε r data hε (le_of_lt hεr')) d =
          Handle.cell (morseAttachingEmbedding hk c ε r data hε (le_of_lt hεr'))
            (attachingInclusion k (m + 1 - k) a₀) := by
        rw [hd_eq, hd₀i]
      _ = Handle.lower (morseAttachingEmbedding hk c ε r data hε (le_of_lt hεr'))
            (morseAttachingEmbedding hk c ε r data hε (le_of_lt hεr') a₀) := by
        simpa using (adjunction_coherence
          (i := attachingInclusion k (m + 1 - k))
          (φ := morseAttachingEmbedding hk c ε r data hε (le_of_lt hεr')) a₀)
      _ = Handle.lower (morseAttachingEmbedding hk c ε r data hε (le_of_lt hεr'))
            (⟨data.χ (y.1 : MorseModel (m + 1)), by
              change f (data.χ (y.1 : MorseModel (m + 1))) ≤ c - ε
              rw [data.hnorm (y.1 : MorseModel (m + 1)) (le_of_lt y.2.1)]
              exact le_of_eq hbound⟩ : SublevelSpace f (c - ε)) := by
        congr 1
        apply Subtype.ext
        exact hφ
  apply Subtype.ext
  dsimp [morseBeltCellMap, morseBeltLowerMap]
  exact hcell

noncomputable def morseBeltCellMapExt {m k : ℕ} (hk : k ≤ m + 1) (c ε r : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} {f : M → ℝ}
    (data : MorseChart (m + 1) k hk c I f)
    (hε : 0 < ε) (hεr' : Real.sqrt (2 * ε + 2 * r ^ 2) < data.R) (hr : 0 < r)
    (y : {y' : morseUpperSublevel hk c r // y' ∈ morseBeltImage hk c ε r data}) :
    {z : Handle.AdjunctionSpace k (m + 1 - k)
      (morseAttachingEmbedding hk c ε r data hε (le_of_lt hεr')) //
        z ∈ morseBeltOpenSet hk c ε r data hε (le_of_lt hεr')} := by
  classical
  by_cases hy : (y.1 : MorseModel (m + 1)) ∈ modelHandle hk ε r
  · exact morseBeltCellMap hk c ε r data hε hεr' hr y hy
  · have hlow : morseNormalForm hk c (y.1 : MorseModel (m + 1)) ≤ c - ε := by
      rcases y.2.2 with hlow | hcell
      · exact hlow
      · exact False.elim (hy hcell)
    exact morseBeltLowerMap hk c ε r data hε hεr' y hlow

theorem morseBeltCellMapExt_eq_clamped {m k : ℕ} (hk : k ≤ m + 1) (c ε r : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} {f : M → ℝ}
    (data : MorseChart (m + 1) k hk c I f)
    (hε : 0 < ε) (hεr' : Real.sqrt (2 * ε + 2 * r ^ 2) < data.R) (hr : 0 < r)
    (y : {y' : morseUpperSublevel hk c r // y' ∈ morseBeltImage hk c ε r data})
    (hgt : c - ε < morseNormalForm hk c (y.1 : MorseModel (m + 1))) :
    morseBeltCellMapExt hk c ε r data hε hεr' hr y =
      morseBeltCellMapClamped hk c ε r data hε hεr' y := by
  have hmem : (y.1 : MorseModel (m + 1)) ∈ modelHandle hk ε r := by
    rcases y.2.2 with hlow | hcell
    · exact False.elim ((not_le_of_gt hgt) hlow)
    · exact hcell
  dsimp [morseBeltCellMapExt, morseBeltCellMapClamped, morseBeltCellMap]
  rw [dif_pos hmem]
  apply Subtype.ext
  change Handle.cell (morseAttachingEmbedding hk c ε r data hε (le_of_lt hεr'))
      ((morseModelHandleMapHomeo hk ε r hε hr).symm ⟨(y.1 : MorseModel (m + 1)), hmem⟩) =
    Handle.cell (morseAttachingEmbedding hk c ε r data hε (le_of_lt hεr'))
      (modelHandleMapRawSymm hk ε r (y.1 : MorseModel (m + 1)))
  rw [← modelHandleMapRawSymm_eq_symm hk ε r hε hr (y.1 : MorseModel (m + 1)) hmem]

theorem morseBeltCellMapExt_eq_clamped_boundary {m k : ℕ} (hk : k ≤ m + 1) (c ε r : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} {f : M → ℝ}
    (data : MorseChart (m + 1) k hk c I f)
    (hε : 0 < ε) (hεr' : Real.sqrt (2 * ε + 2 * r ^ 2) < data.R) (hr : 0 < r)
    (y : {y' : morseUpperSublevel hk c r // y' ∈ morseBeltImage hk c ε r data})
    (hy : (y.1 : MorseModel (m + 1)) ∈ modelHandle hk ε r) :
    morseBeltCellMapExt hk c ε r data hε hεr' hr y =
      morseBeltCellMapClamped hk c ε r data hε hεr' y := by
  dsimp [morseBeltCellMapExt, morseBeltCellMapClamped, morseBeltCellMap]
  rw [dif_pos hy]
  apply Subtype.ext
  change Handle.cell (morseAttachingEmbedding hk c ε r data hε (le_of_lt hεr'))
      ((morseModelHandleMapHomeo hk ε r hε hr).symm ⟨(y.1 : MorseModel (m + 1)), hy⟩) =
    Handle.cell (morseAttachingEmbedding hk c ε r data hε (le_of_lt hεr'))
      (modelHandleMapRawSymm hk ε r (y.1 : MorseModel (m + 1)))
  rw [← modelHandleMapRawSymm_eq_symm hk ε r hε hr (y.1 : MorseModel (m + 1)) hy]

theorem morseBeltCellMapExt_eq_lower {m k : ℕ} (hk : k ≤ m + 1) (c ε r : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} {f : M → ℝ}
    (data : MorseChart (m + 1) k hk c I f)
    (hε : 0 < ε) (hεr' : Real.sqrt (2 * ε + 2 * r ^ 2) < data.R) (hr : 0 < r)
    (y : {y' : morseUpperSublevel hk c r // y' ∈ morseBeltImage hk c ε r data})
    (hbound : morseNormalForm hk c (y.1 : MorseModel (m + 1)) = c - ε) :
    morseBeltCellMapExt hk c ε r data hε hεr' hr y =
      morseBeltLowerMap hk c ε r data hε hεr' y (le_of_eq hbound) := by
  classical
  dsimp [morseBeltCellMapExt]
  by_cases hy : (y.1 : MorseModel (m + 1)) ∈ modelHandle hk ε r
  · rw [dif_pos hy]
    exact morseBeltCellMap_eq_lower hk c ε r data hε hεr' hr y hy hbound
  · rw [dif_neg hy]

theorem morseBeltMapOnOpen_inv_eq_cellMapExt {m k : ℕ} (hk : k ≤ m + 1) (c ε r : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} {f : M → ℝ}
    (data : MorseChart (m + 1) k hk c I f)
    (hε : 0 < ε) (hεr' : Real.sqrt (2 * ε + 2 * r ^ 2) < data.R) (hr : 0 < r)
    (y : {y' : morseUpperSublevel hk c r // y' ∈ morseBeltImage hk c ε r data}) :
    morseBeltMapOnOpen_inv hk c ε r data hε hεr' hr y =
      morseBeltCellMapExt hk c ε r data hε hεr' hr y := by
  classical
  by_cases hle : morseNormalForm hk c (y.1 : MorseModel (m + 1)) ≤ c - ε
  · by_cases hy : (y.1 : MorseModel (m + 1)) ∈ modelHandle hk ε r
    · have hge : c - ε ≤ morseNormalForm hk c (y.1 : MorseModel (m + 1)) := by
        have hmem : (y.1 : MorseModel (m + 1)) ∈
            ({z : MorseModel (m + 1) | ‖posPart hk z‖ ≤ r} ∩
              {z : MorseModel (m + 1) | c - ε ≤ morseNormalForm hk c z}) := by
          simpa [modelHandle_eq_inter hk c ε r (le_of_lt hr)] using hy
        exact hmem.2
      have hb : morseNormalForm hk c (y.1 : MorseModel (m + 1)) = c - ε := le_antisymm hle hge
      calc
        morseBeltMapOnOpen_inv hk c ε r data hε hεr' hr y =
            morseBeltLowerMap hk c ε r data hε hεr' y hle :=
          morseBeltMapOnOpen_inv_eq_lower hk c ε r data hε hεr' hr y hle
        _ = morseBeltLowerMap hk c ε r data hε hεr' y (le_of_eq hb) := by
          rfl
        _ = morseBeltCellMapExt hk c ε r data hε hεr' hr y :=
          (morseBeltCellMapExt_eq_lower hk c ε r data hε hεr' hr y hb).symm
    · have hlow' : morseNormalForm hk c (y.1 : MorseModel (m + 1)) ≤ c - ε := by
        rcases y.2.2 with hlow | hcell
        · exact hlow
        · exact False.elim (hy hcell)
      calc
        morseBeltMapOnOpen_inv hk c ε r data hε hεr' hr y =
            morseBeltLowerMap hk c ε r data hε hεr' y hle :=
          morseBeltMapOnOpen_inv_eq_lower hk c ε r data hε hεr' hr y hle
        _ = morseBeltCellMapExt hk c ε r data hε hεr' hr y := by
          dsimp [morseBeltCellMapExt]
          rw [dif_neg hy]
  · have hgt : c - ε < morseNormalForm hk c (y.1 : MorseModel (m + 1)) := lt_of_not_ge hle
    have hy : (y.1 : MorseModel (m + 1)) ∈ modelHandle hk ε r := by
      rcases y.2.2 with hlow | hcell
      · exact False.elim (hle hlow)
      · exact hcell
    calc
      morseBeltMapOnOpen_inv hk c ε r data hε hεr' hr y =
          morseBeltCellMap hk c ε r data hε hεr' hr y hy :=
        morseBeltMapOnOpen_inv_eq_cell_strict hk c ε r data hε hεr' hr y hy hgt
      _ = morseBeltCellMapExt hk c ε r data hε hεr' hr y := by
        dsimp [morseBeltCellMapExt]
        rw [dif_pos hy]

theorem continuousOn_morseBeltCellMapExt_cell {m k : ℕ} (hk : k ≤ m + 1) (c ε r : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} {f : M → ℝ}
    (data : MorseChart (m + 1) k hk c I f)
    (hε : 0 < ε) (hεr' : Real.sqrt (2 * ε + 2 * r ^ 2) < data.R) (hr : 0 < r) :
    ContinuousOn (morseBeltCellMapExt hk c ε r data hε hεr' hr)
      {y : {y' : morseUpperSublevel hk c r // y' ∈ morseBeltImage hk c ε r data} |
        c - ε < morseNormalForm hk c (y.1 : MorseModel (m + 1))} := by
  let S : Set {y' : morseUpperSublevel hk c r // y' ∈ morseBeltImage hk c ε r data} :=
    {y : {y' : morseUpperSublevel hk c r // y' ∈ morseBeltImage hk c ε r data} |
      c - ε < morseNormalForm hk c (y.1 : MorseModel (m + 1))}
  let g : S → {z : Handle.AdjunctionSpace k (m + 1 - k)
      (morseAttachingEmbedding hk c ε r data hε (le_of_lt hεr')) //
        z ∈ morseBeltOpenSet hk c ε r data hε (le_of_lt hεr')} :=
    fun y => ⟨Handle.cell (morseAttachingEmbedding hk c ε r data hε (le_of_lt hεr'))
      ((morseModelHandleMapHomeo hk ε r hε hr).symm ⟨(y.1.1 : MorseModel (m + 1)), by
        rcases y.1.2.2 with hlow | hcell
        · exact False.elim ((not_le_of_gt y.2) hlow)
        · exact hcell⟩),
      Or.inr ⟨(morseModelHandleMapHomeo hk ε r hε hr).symm ⟨(y.1.1 : MorseModel (m + 1)), by
        rcases y.1.2.2 with hlow | hcell
        · exact False.elim ((not_le_of_gt y.2) hlow)
        · exact hcell⟩, by
          dsimp
          rw [morseModelHandleMapHomeo_symm_apply hk ε r hε hr]
          exact y.1.2.1, rfl⟩⟩
  have hmain : Continuous (fun y : S => (y.1.1 : MorseModel (m + 1))) := by
    exact continuous_subtype_val.comp (continuous_subtype_val.comp continuous_subtype_val)
  have hsymm : Continuous (fun y : S =>
      (morseModelHandleMapHomeo hk ε r hε hr).symm ⟨(y.1.1 : MorseModel (m + 1)), by
        rcases y.1.2.2 with hlow | hcell
        · exact False.elim ((not_le_of_gt y.2) hlow)
        · exact hcell⟩) := by
    exact (morseModelHandleMapHomeo hk ε r hε hr).symm.continuous.comp
      (Continuous.subtype_mk hmain (fun y => by
        rcases y.1.2.2 with hlow | hcell
        · exact False.elim ((not_le_of_gt y.2) hlow)
        · exact hcell))
  have hg : Continuous g := by
    dsimp [g]
    exact Continuous.subtype_mk ((continuous_cell (morseAttachingEmbedding hk c ε r data hε (le_of_lt hεr'))).comp hsymm)
      (fun y => Or.inr ⟨(morseModelHandleMapHomeo hk ε r hε hr).symm ⟨(y.1.1 : MorseModel (m + 1)), by
        rcases y.1.2.2 with hlow | hcell
        · exact False.elim ((not_le_of_gt y.2) hlow)
        · exact hcell⟩, by
          dsimp
          rw [morseModelHandleMapHomeo_symm_apply hk ε r hε hr]
          exact y.1.2.1, rfl⟩)
  have hmain2 : ContinuousOn (fun y : S =>
      morseBeltCellMapExt hk c ε r data hε hεr' hr (y : {y' : morseUpperSublevel hk c r // y' ∈ morseBeltImage hk c ε r data})) Set.univ := by
    refine (continuousOn_congr (s := Set.univ)
      (g := fun y : S => morseBeltCellMapExt hk c ε r data hε hεr' hr
        (y : {y' : morseUpperSublevel hk c r // y' ∈ morseBeltImage hk c ε r data}))
      (f := g) ?_).mpr hg.continuousOn
    intro y hy
    dsimp [g]
    have hmem : (y.1.1 : MorseModel (m + 1)) ∈ modelHandle hk ε r := by
      rcases y.1.2.2 with hlow | hcell
      · exact False.elim ((not_le_of_gt y.2) hlow)
      · exact hcell
    dsimp [morseBeltCellMapExt]
    rw [dif_pos hmem]
    rfl
  rw [continuousOn_iff_continuous_restrict]
  simpa [S] using (continuousOn_univ.mp hmain2)

theorem continuousOn_morseBeltCellMapExt_lower {m k : ℕ} (hk : k ≤ m + 1) (c ε r : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} {f : M → ℝ}
    (data : MorseChart (m + 1) k hk c I f)
    (hε : 0 < ε) (hεr' : Real.sqrt (2 * ε + 2 * r ^ 2) < data.R) (hr : 0 < r) :
    ContinuousOn (morseBeltCellMapExt hk c ε r data hε hεr' hr)
      {y : {y' : morseUpperSublevel hk c r // y' ∈ morseBeltImage hk c ε r data} |
        morseNormalForm hk c (y.1 : MorseModel (m + 1)) < c - ε} := by
  let S : Set {y' : morseUpperSublevel hk c r // y' ∈ morseBeltImage hk c ε r data} :=
    {y : {y' : morseUpperSublevel hk c r // y' ∈ morseBeltImage hk c ε r data} |
      morseNormalForm hk c (y.1 : MorseModel (m + 1)) < c - ε}
  let g : S → {z : Handle.AdjunctionSpace k (m + 1 - k)
      (morseAttachingEmbedding hk c ε r data hε (le_of_lt hεr')) //
        z ∈ morseBeltOpenSet hk c ε r data hε (le_of_lt hεr')} :=
    fun y => morseBeltLowerMap hk c ε r data hε hεr' y.1 (le_of_lt y.2)
  have hmain : Continuous (fun y : S => data.χ (y.1.1 : MorseModel (m + 1))) := by
    have hinner : Continuous (fun y : S => (y.1.1 : MorseModel (m + 1))) := by
      exact continuous_subtype_val.comp (continuous_subtype_val.comp continuous_subtype_val)
    have hmaps : Set.MapsTo (fun y : S => (y.1.1 : MorseModel (m + 1))) Set.univ data.χ.source := by
      intro y hy
      exact data.hχsrc (y.1.1 : MorseModel (m + 1)) (le_of_lt y.1.2.1)
    exact (continuousOn_univ.mp (data.χ.continuousOn_toFun.comp hinner.continuousOn hmaps))
  have hmain2 : Continuous (fun y : S =>
      Handle.lower (morseAttachingEmbedding hk c ε r data hε (le_of_lt hεr'))
        (⟨data.χ (y.1.1 : MorseModel (m + 1)), by
          change f (data.χ (y.1.1 : MorseModel (m + 1))) ≤ c - ε
          rw [data.hnorm (y.1.1 : MorseModel (m + 1)) (le_of_lt y.1.2.1)]
          exact le_of_lt y.2⟩ : SublevelSpace f (c - ε))) := by
    exact (continuous_lower (morseAttachingEmbedding hk c ε r data hε (le_of_lt hεr'))).comp
      (Continuous.subtype_mk hmain (fun y => by
        change f (data.χ (y.1.1 : MorseModel (m + 1))) ≤ c - ε
        rw [data.hnorm (y.1.1 : MorseModel (m + 1)) (le_of_lt y.1.2.1)]
        exact le_of_lt y.2))
  have hg : Continuous g := by
    dsimp [g]
    exact Continuous.subtype_mk hmain2 (fun y => Or.inl ⟨⟨data.χ (y.1.1 : MorseModel (m + 1)), by
      change f (data.χ (y.1.1 : MorseModel (m + 1))) ≤ c - ε
      rw [data.hnorm (y.1.1 : MorseModel (m + 1)) (le_of_lt y.1.2.1)]
      exact le_of_lt y.2⟩, by
        dsimp [morseBeltLowerSet]
        exact ⟨(y.1.1 : MorseModel (m + 1)), y.1.2.1, rfl⟩, rfl⟩)
  have hmain3 : ContinuousOn (fun y : S =>
      morseBeltCellMapExt hk c ε r data hε hεr' hr (y : {y' : morseUpperSublevel hk c r // y' ∈ morseBeltImage hk c ε r data})) Set.univ := by
    refine (continuousOn_congr (s := Set.univ)
      (g := fun y : S => morseBeltCellMapExt hk c ε r data hε hεr' hr
        (y : {y' : morseUpperSublevel hk c r // y' ∈ morseBeltImage hk c ε r data}))
      (f := g) ?_).mpr hg.continuousOn
    intro y hy
    dsimp [g]
    have hnot : ¬ (y.1.1 : MorseModel (m + 1)) ∈ modelHandle hk ε r := by
      intro hcell
      have hge : c - ε ≤ morseNormalForm hk c (y.1.1 : MorseModel (m + 1)) := by
        have hmem : (y.1.1 : MorseModel (m + 1)) ∈
            ({z : MorseModel (m + 1) | ‖posPart hk z‖ ≤ r} ∩
              {z : MorseModel (m + 1) | c - ε ≤ morseNormalForm hk c z}) := by
          simpa [modelHandle_eq_inter hk c ε r (le_of_lt hr)] using hcell
        exact hmem.2
      exact (not_lt_of_ge hge) y.2
    dsimp [morseBeltCellMapExt]
    rw [dif_neg hnot]
  rw [continuousOn_iff_continuous_restrict]
  simpa [S] using (continuousOn_univ.mp hmain3)

theorem continuousOn_morseBeltCellMapExt_le {m k : ℕ} (hk : k ≤ m + 1) (c ε r : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} {f : M → ℝ}
    (data : MorseChart (m + 1) k hk c I f)
    (hε : 0 < ε) (hεr' : Real.sqrt (2 * ε + 2 * r ^ 2) < data.R) (hr : 0 < r) :
    ContinuousOn (morseBeltCellMapExt hk c ε r data hε hεr' hr)
      {y : {y' : morseUpperSublevel hk c r // y' ∈ morseBeltImage hk c ε r data} |
        morseNormalForm hk c (y.1 : MorseModel (m + 1)) ≤ c - ε} := by
  let S : Set {y' : morseUpperSublevel hk c r // y' ∈ morseBeltImage hk c ε r data} :=
    {y : {y' : morseUpperSublevel hk c r // y' ∈ morseBeltImage hk c ε r data} |
      morseNormalForm hk c (y.1 : MorseModel (m + 1)) ≤ c - ε}
  let g : S → {z : Handle.AdjunctionSpace k (m + 1 - k)
      (morseAttachingEmbedding hk c ε r data hε (le_of_lt hεr')) //
        z ∈ morseBeltOpenSet hk c ε r data hε (le_of_lt hεr')} :=
    fun y => morseBeltLowerMap hk c ε r data hε hεr' y.1 y.2
  have hmain : Continuous (fun y : S => data.χ (y.1.1 : MorseModel (m + 1))) := by
    have hinner : Continuous (fun y : S => (y.1.1 : MorseModel (m + 1))) := by
      exact continuous_subtype_val.comp (continuous_subtype_val.comp continuous_subtype_val)
    have hmaps : Set.MapsTo (fun y : S => (y.1.1 : MorseModel (m + 1))) Set.univ data.χ.source := by
      intro y hy
      exact data.hχsrc (y.1.1 : MorseModel (m + 1)) (le_of_lt y.1.2.1)
    exact (continuousOn_univ.mp (data.χ.continuousOn_toFun.comp hinner.continuousOn hmaps))
  have hmain2 : Continuous (fun y : S =>
      Handle.lower (morseAttachingEmbedding hk c ε r data hε (le_of_lt hεr'))
        (⟨data.χ (y.1.1 : MorseModel (m + 1)), by
          change f (data.χ (y.1.1 : MorseModel (m + 1))) ≤ c - ε
          rw [data.hnorm (y.1.1 : MorseModel (m + 1)) (le_of_lt y.1.2.1)]
          exact y.2⟩ : SublevelSpace f (c - ε))) := by
    exact (continuous_lower (morseAttachingEmbedding hk c ε r data hε (le_of_lt hεr'))).comp
      (Continuous.subtype_mk hmain (fun y => by
        change f (data.χ (y.1.1 : MorseModel (m + 1))) ≤ c - ε
        rw [data.hnorm (y.1.1 : MorseModel (m + 1)) (le_of_lt y.1.2.1)]
        exact y.2))
  have hg : Continuous g := by
    dsimp [g]
    exact Continuous.subtype_mk hmain2 (fun y => Or.inl ⟨⟨data.χ (y.1.1 : MorseModel (m + 1)), by
      change f (data.χ (y.1.1 : MorseModel (m + 1))) ≤ c - ε
      rw [data.hnorm (y.1.1 : MorseModel (m + 1)) (le_of_lt y.1.2.1)]
      exact y.2⟩, by
        dsimp [morseBeltLowerSet]
        exact ⟨(y.1.1 : MorseModel (m + 1)), y.1.2.1, rfl⟩, rfl⟩)
  have hmain3 : ContinuousOn (fun y : S =>
      morseBeltCellMapExt hk c ε r data hε hεr' hr (y : {y' : morseUpperSublevel hk c r // y' ∈ morseBeltImage hk c ε r data})) Set.univ := by
    refine (continuousOn_congr (s := Set.univ)
      (g := fun y : S => morseBeltCellMapExt hk c ε r data hε hεr' hr
        (y : {y' : morseUpperSublevel hk c r // y' ∈ morseBeltImage hk c ε r data}))
      (f := g) ?_).mpr hg.continuousOn
    intro y hy
    dsimp [g]
    by_cases hy' : (y.1.1 : MorseModel (m + 1)) ∈ modelHandle hk ε r
    · have hge : c - ε ≤ morseNormalForm hk c (y.1.1 : MorseModel (m + 1)) := by
        have hmem : (y.1.1 : MorseModel (m + 1)) ∈
            ({z : MorseModel (m + 1) | ‖posPart hk z‖ ≤ r} ∩
              {z : MorseModel (m + 1) | c - ε ≤ morseNormalForm hk c z}) := by
          simpa [modelHandle_eq_inter hk c ε r (le_of_lt hr)] using hy'
        exact hmem.2
      have hb : morseNormalForm hk c (y.1.1 : MorseModel (m + 1)) = c - ε := le_antisymm y.2 hge
      have heq : morseBeltCellMapExt hk c ε r data hε hεr' hr
            (y : {y' : morseUpperSublevel hk c r // y' ∈ morseBeltImage hk c ε r data}) =
          morseBeltLowerMap hk c ε r data hε hεr'
            (y : {y' : morseUpperSublevel hk c r // y' ∈ morseBeltImage hk c ε r data}) y.2 := by
        simpa using (morseBeltCellMapExt_eq_lower hk c ε r data hε hεr' hr
          (y : {y' : morseUpperSublevel hk c r // y' ∈ morseBeltImage hk c ε r data}) hb)
      simpa [g] using heq
    · have hlow' : morseNormalForm hk c (y.1.1 : MorseModel (m + 1)) ≤ c - ε := by
        rcases y.1.2.2 with hlow | hcell
        · exact hlow
        · exact False.elim (hy' hcell)
      dsimp [morseBeltCellMapExt]
      rw [dif_neg hy']
  rw [continuousOn_iff_continuous_restrict]
  simpa [S] using (continuousOn_univ.mp hmain3)

theorem continuous_morseBeltCellMapExt {m k : ℕ} (hk : k ≤ m + 1) (c ε r : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} {f : M → ℝ}
    (data : MorseChart (m + 1) k hk c I f)
    (hε : 0 < ε) (hεr' : Real.sqrt (2 * ε + 2 * r ^ 2) < data.R) (hr : 0 < r) :
    Continuous (morseBeltCellMapExt hk c ε r data hε hεr' hr) := by
  rw [continuous_iff_continuousAt]
  intro y₀
  have hunion : Set.univ =
      ({y : {y' : morseUpperSublevel hk c r // y' ∈ morseBeltImage hk c ε r data} |
        c - ε < morseNormalForm hk c (y.1 : MorseModel (m + 1))} : Set
          {y' : morseUpperSublevel hk c r // y' ∈ morseBeltImage hk c ε r data}) ∪
        {y : {y' : morseUpperSublevel hk c r // y' ∈ morseBeltImage hk c ε r data} |
          morseNormalForm hk c (y.1 : MorseModel (m + 1)) ≤ c - ε} := by
    ext y
    constructor
    · intro hy
      by_cases h : c - ε < morseNormalForm hk c (y.1 : MorseModel (m + 1))
      · exact Or.inl h
      · exact Or.inr (not_lt.mp h)
    · intro hy
      trivial
  by_cases hb : morseNormalForm hk c (y₀.1 : MorseModel (m + 1)) = c - ε
  · by_cases hy₀ : (y₀.1 : MorseModel (m + 1)) ∈ modelHandle hk ε r
    · rw [← continuousWithinAt_univ, hunion, continuousWithinAt_union]
      constructor
      · have hcongr : (morseBeltCellMapExt hk c ε r data hε hεr' hr) =ᶠ[
            nhdsWithin y₀ {y : {y' : morseUpperSublevel hk c r // y' ∈ morseBeltImage hk c ε r data} |
              c - ε < morseNormalForm hk c (y.1 : MorseModel (m + 1))}]
            (morseBeltCellMapClamped hk c ε r data hε hεr') := by
          filter_upwards [self_mem_nhdsWithin] with y hy
          exact morseBeltCellMapExt_eq_clamped hk c ε r data hε hεr' hr y hy
        have hval : morseBeltCellMapExt hk c ε r data hε hεr' hr y₀ =
            morseBeltCellMapClamped hk c ε r data hε hεr' y₀ := by
          exact morseBeltCellMapExt_eq_clamped_boundary hk c ε r data hε hεr' hr y₀ hy₀
        exact (Filter.EventuallyEq.congr_continuousWithinAt hcongr hval).mpr
          (continuous_morseBeltCellMapClamped hk c ε r data hε hεr').continuousAt.continuousWithinAt
      · exact (continuousOn_morseBeltCellMapExt_le hk c ε r data hε hεr' hr) y₀ (le_of_eq hb)
    · rw [← continuousWithinAt_univ, hunion, continuousWithinAt_union]
      constructor
      · have hbot : nhdsWithin y₀ {y : {y' : morseUpperSublevel hk c r // y' ∈ morseBeltImage hk c ε r data} |
            c - ε < morseNormalForm hk c (y.1 : MorseModel (m + 1))} = ⊥ := by
          rw [← notMem_closure_iff_nhdsWithin_eq_bot]
          intro hycl
          have hsub : {y : {y' : morseUpperSublevel hk c r // y' ∈ morseBeltImage hk c ε r data} |
                c - ε < morseNormalForm hk c (y.1 : MorseModel (m + 1))} ⊆
              {y : {y' : morseUpperSublevel hk c r // y' ∈ morseBeltImage hk c ε r data} |
                (y.1 : MorseModel (m + 1)) ∈ modelHandle hk ε r} := by
            intro y hy
            rcases y.2.2 with hlow | hcell
            · exact False.elim ((not_le_of_gt hy) hlow)
            · exact hcell
          have hclosed : IsClosed {y : {y' : morseUpperSublevel hk c r // y' ∈ morseBeltImage hk c ε r data} |
              (y.1 : MorseModel (m + 1)) ∈ modelHandle hk ε r} := by
            have hcl : IsClosed (modelHandle hk ε r : Set (MorseModel (m + 1))) := by
              rw [modelHandle_eq_inter hk c ε r (le_of_lt hr)]
              exact IsClosed.inter (isClosed_le (continuous_norm.comp (continuous_posPart hk)) continuous_const)
                (isClosed_le continuous_const (CellAttachment.contDiff_morseNormalForm hk c).continuous)
            exact hcl.preimage (continuous_subtype_val.comp continuous_subtype_val)
          exact hy₀ (hclosed.closure_subset_iff.mpr hsub hycl)
        simp [ContinuousWithinAt, hbot]
      · exact (continuousOn_morseBeltCellMapExt_le hk c ε r data hε hεr' hr) y₀ (le_of_eq hb)
  · by_cases hgt : c - ε < morseNormalForm hk c (y₀.1 : MorseModel (m + 1))
    · exact (continuousOn_morseBeltCellMapExt_cell hk c ε r data hε hεr' hr) y₀ hgt |>.continuousAt
        (IsOpen.mem_nhds (isOpen_lt continuous_const
          ((CellAttachment.contDiff_morseNormalForm hk c).continuous.comp
            (continuous_subtype_val.comp continuous_subtype_val))) hgt)
    · have hlt : morseNormalForm hk c (y₀.1 : MorseModel (m + 1)) < c - ε := by
        exact lt_of_le_of_ne (not_lt.mp hgt) hb
      exact (continuousOn_morseBeltCellMapExt_lower hk c ε r data hε hεr' hr) y₀ hlt |>.continuousAt
        (IsOpen.mem_nhds (isOpen_lt
          ((CellAttachment.contDiff_morseNormalForm hk c).continuous.comp
            (continuous_subtype_val.comp continuous_subtype_val)) continuous_const) hlt)

theorem continuous_morseBeltMapOnOpen_inv {m k : ℕ} (hk : k ≤ m + 1) (c ε r : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} {f : M → ℝ}
    (data : MorseChart (m + 1) k hk c I f)
    (hε : 0 < ε) (hεr' : Real.sqrt (2 * ε + 2 * r ^ 2) < data.R) (hr : 0 < r) :
    Continuous (morseBeltMapOnOpen_inv hk c ε r data hε hεr' hr) := by
  refine continuous_morseBeltCellMapExt hk c ε r data hε hεr' hr |>.congr ?_
  intro y
  exact (morseBeltMapOnOpen_inv_eq_cellMapExt hk c ε r data hε hεr' hr y).symm

noncomputable def morseBeltMapHomeoImage {m k : ℕ} (hk : k ≤ m + 1) (c ε r : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} {f : M → ℝ}
    (data : MorseChart (m + 1) k hk c I f)
    (hε : 0 < ε) (hεr' : Real.sqrt (2 * ε + 2 * r ^ 2) < data.R) (hr : 0 < r)
    (hcont : Continuous f) :
    {z : Handle.AdjunctionSpace k (m + 1 - k)
      (morseAttachingEmbedding hk c ε r data hε (le_of_lt hεr')) //
        z ∈ morseBeltOpenSet hk c ε r data hε (le_of_lt hεr')} ≃ₜ
      {y : morseUpperSublevel hk c r // y ∈ morseBeltImage hk c ε r data} where
  toFun := fun z => ⟨morseBeltMapOnOpen hk c ε r data hε hεr' z,
    morseBeltMapOnOpen_mem_image hk c ε r data hε hεr' z⟩
  invFun := morseBeltMapOnOpen_inv hk c ε r data hε hεr' hr
  left_inv := fun z => morseBeltMapOnOpen_left_inv hk c ε r data hε hεr' hr hcont z
  right_inv := fun y => by
    apply Subtype.ext
    simpa using (morseBeltMapOnOpen_right_inv hk c ε r data hε hεr' hr y)
  continuous_toFun := Continuous.subtype_mk (continuous_morseBeltMapOnOpen hk c ε r data hε hεr')
    (fun z => morseBeltMapOnOpen_mem_image hk c ε r data hε hεr' z)
  continuous_invFun := continuous_morseBeltMapOnOpen_inv hk c ε r data hε hεr' hr

noncomputable def morseHandleAdjunctionToUpperSublevelFun {m k : ℕ} (hk : k ≤ m + 1) (c ε r : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} {f : M → ℝ}
    (data : MorseChart (m + 1) k hk c I f)
    (hε : 0 < ε) (hεr' : Real.sqrt (2 * ε + 2 * r ^ 2) < data.R) :
    StandardHandle k (m + 1 - k) ⊕ SublevelSpace f (c - ε) → SublevelSpace f (c + r ^ 2 / 2) :=
  Sum.elim
    (fun d : StandardHandle k (m + 1 - k) => ⟨data.χ (modelHandleMap hk ε r d), by
        change f (data.χ (modelHandleMap hk ε r d)) ≤ c + r ^ 2 / 2
        rw [data.hnorm (modelHandleMap hk ε r d) (le_trans (modelHandleMap_norm_le hk ε r (le_of_lt hε) d) (le_of_lt hεr'))]
        exact modelHandleMap_f_le hk c ε r (le_of_lt hε) d⟩)
    (fun x : SublevelSpace f (c - ε) => ⟨x.1, by
        change f x.1 ≤ c + r ^ 2 / 2
        have hr2 : 0 ≤ r ^ 2 / 2 := div_nonneg (sq_nonneg r) (by norm_num)
        exact le_trans x.2 (by linarith [hε, hr2])⟩)

theorem morseHandleAdjunctionToUpperSublevelFun_rel {m k : ℕ} (hk : k ≤ m + 1) (c ε r : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} {f : M → ℝ}
    (data : MorseChart (m + 1) k hk c I f)
    (hε : 0 < ε) (hεr' : Real.sqrt (2 * ε + 2 * r ^ 2) < data.R)
    (a b : StandardHandle k (m + 1 - k) ⊕ SublevelSpace f (c - ε))
    (hab : DifferentialGeometry.Topology.adjunctionRel (attachingInclusion k (m + 1 - k))
      (morseAttachingEmbedding hk c ε r data hε (le_of_lt hεr')) a b) :
    morseHandleAdjunctionToUpperSublevelFun hk c ε r data hε hεr' a =
      morseHandleAdjunctionToUpperSublevelFun hk c ε r data hε hεr' b := by
  rcases hab with ⟨p, hp | hp⟩
  · rcases hp with ⟨ha, hb⟩
    subst a
    subst b
    apply Subtype.ext
    change data.χ (modelHandleMap hk ε r (attachingInclusion k (m + 1 - k) p)) =
      (morseAttachingEmbedding hk c ε r data hε (le_of_lt hεr') p).1
    exact (morseAttachingEmbedding_eq_handleEmbedding hk c ε r data hε (le_of_lt hεr') p).symm
  · rcases hp with ⟨hb, ha⟩
    subst a
    subst b
    apply Subtype.ext
    change (morseAttachingEmbedding hk c ε r data hε (le_of_lt hεr') p).1 =
      data.χ (modelHandleMap hk ε r (attachingInclusion k (m + 1 - k) p))
    exact (morseAttachingEmbedding_eq_handleEmbedding hk c ε r data hε (le_of_lt hεr') p)

noncomputable def morseHandleAdjunctionToUpperSublevel {m k : ℕ} (hk : k ≤ m + 1) (c ε r : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} {f : M → ℝ}
    (data : MorseChart (m + 1) k hk c I f)
    (hε : 0 < ε) (hεr' : Real.sqrt (2 * ε + 2 * r ^ 2) < data.R) :
    Handle.AdjunctionSpace k (m + 1 - k) (morseAttachingEmbedding hk c ε r data hε (le_of_lt hεr')) →
      SublevelSpace f (c + r ^ 2 / 2) :=
  Quot.lift (morseHandleAdjunctionToUpperSublevelFun hk c ε r data hε hεr')
    (morseHandleAdjunctionToUpperSublevelFun_rel hk c ε r data hε hεr')

theorem morseHandleAdjunctionToUpperSublevel_cell {m k : ℕ} (hk : k ≤ m + 1) (c ε r : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} {f : M → ℝ}
    (data : MorseChart (m + 1) k hk c I f)
    (hε : 0 < ε) (hεr' : Real.sqrt (2 * ε + 2 * r ^ 2) < data.R)
    (d : StandardHandle k (m + 1 - k)) :
    (morseHandleAdjunctionToUpperSublevel hk c ε r data hε hεr'
      (Handle.cell (morseAttachingEmbedding hk c ε r data hε (le_of_lt hεr')) d) : M) =
      data.χ (modelHandleMap hk ε r d) := by
  rfl

theorem morseHandleAdjunctionToUpperSublevel_lower {m k : ℕ} (hk : k ≤ m + 1) (c ε r : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} {f : M → ℝ}
    (data : MorseChart (m + 1) k hk c I f)
    (hε : 0 < ε) (hεr' : Real.sqrt (2 * ε + 2 * r ^ 2) < data.R)
    (x : SublevelSpace f (c - ε)) :
    (morseHandleAdjunctionToUpperSublevel hk c ε r data hε hεr'
      (Handle.lower (morseAttachingEmbedding hk c ε r data hε (le_of_lt hεr')) x) : M) = x.1 := by
  rfl

theorem continuous_morseHandleAdjunctionToUpperSublevel {m k : ℕ} (hk : k ≤ m + 1) (c ε r : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} {f : M → ℝ}
    (data : MorseChart (m + 1) k hk c I f)
    (hε : 0 < ε) (hεr' : Real.sqrt (2 * ε + 2 * r ^ 2) < data.R) :
    Continuous (morseHandleAdjunctionToUpperSublevel hk c ε r data hε hεr') := by
  have hcell : Continuous (fun d : StandardHandle k (m + 1 - k) =>
      (⟨data.χ (modelHandleMap hk ε r d), by
        change f (data.χ (modelHandleMap hk ε r d)) ≤ c + r ^ 2 / 2
        rw [data.hnorm (modelHandleMap hk ε r d) (le_trans (modelHandleMap_norm_le hk ε r (le_of_lt hε) d) (le_of_lt hεr'))]
        exact modelHandleMap_f_le hk c ε r (le_of_lt hε) d⟩ : SublevelSpace f (c + r ^ 2 / 2))) := by
    have hmain : Continuous (fun d : StandardHandle k (m + 1 - k) =>
        data.χ (modelHandleMap hk ε r d)) := by
      have hmaps : Set.MapsTo (fun d : StandardHandle k (m + 1 - k) =>
          modelHandleMap hk ε r d) Set.univ data.χ.source := by
        intro d hd
        exact data.hχsrc (modelHandleMap hk ε r d)
          (le_trans (modelHandleMap_norm_le hk ε r (le_of_lt hε) d) (le_of_lt hεr'))
      exact (continuousOn_univ.mp (data.χ.continuousOn_toFun.comp (continuous_modelHandleMap hk ε r).continuousOn hmaps))
    exact Continuous.subtype_mk hmain (fun d => by
      change f (data.χ (modelHandleMap hk ε r d)) ≤ c + r ^ 2 / 2
      rw [data.hnorm (modelHandleMap hk ε r d) (le_trans (modelHandleMap_norm_le hk ε r (le_of_lt hε) d) (le_of_lt hεr'))]
      exact modelHandleMap_f_le hk c ε r (le_of_lt hε) d)
  have hlower : Continuous (fun x : SublevelSpace f (c - ε) =>
      (⟨x.1, by
        change f x.1 ≤ c + r ^ 2 / 2
        have hr2 : 0 ≤ r ^ 2 / 2 := div_nonneg (sq_nonneg r) (by norm_num)
        exact le_trans x.2 (by linarith [hε, hr2])⟩ : SublevelSpace f (c + r ^ 2 / 2))) := by
    exact Continuous.subtype_mk continuous_subtype_val (fun x => by
      change f x.1 ≤ c + r ^ 2 / 2
      have hr2 : 0 ≤ r ^ 2 / 2 := div_nonneg (sq_nonneg r) (by norm_num)
      exact le_trans x.2 (by linarith [hε, hr2]))
  refine continuous_quot_lift (morseHandleAdjunctionToUpperSublevelFun_rel hk c ε r data hε hεr') ?_
  dsimp [morseHandleAdjunctionToUpperSublevelFun]
  exact Continuous.sumElim hcell hlower

theorem morseHandleAdjunctionToUpperSublevel_injective {m k : ℕ} (hk : k ≤ m + 1) (c ε r : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} {f : M → ℝ}
    (data : MorseChart (m + 1) k hk c I f)
    (hε : 0 < ε) (hr : r ≠ 0) (hεr' : Real.sqrt (2 * ε + 2 * r ^ 2) < data.R)
    (hcont : Continuous f) :
    Function.Injective (morseHandleAdjunctionToUpperSublevel hk c ε r data hε hεr') := by
  let H : Handle.AdjunctionSpace k (m + 1 - k)
      (morseAttachingEmbedding hk c ε r data hε (le_of_lt hεr')) ≃ₜ
      {x : M // x ∈ sublevel f (c - ε) ∪ Set.range (handleEmbedding hk c ε r data)} :=
    morseHandleAdjunctionHomeoUnion hk c ε r data hε hr (le_of_lt hεr') hcont
  have hfact : ∀ z : Handle.AdjunctionSpace k (m + 1 - k)
      (morseAttachingEmbedding hk c ε r data hε (le_of_lt hεr')),
      morseHandleAdjunctionToUpperSublevel hk c ε r data hε hεr' z =
        ⟨(H z).1, by
          rcases (H z).2 with hlow | hcell
          · change f (H z).1 ≤ c + r ^ 2 / 2
            have hr2 : 0 ≤ r ^ 2 / 2 := div_nonneg (sq_nonneg r) (by norm_num)
            exact le_trans hlow (by linarith [hε, hr2])
          · rcases hcell with ⟨d, hd⟩
            change f (H z).1 ≤ c + r ^ 2 / 2
            rw [← hd]
            rw [handleEmbedding_f_value hk c ε r data (le_of_lt hε) (le_of_lt hεr') d]
            exact modelHandleMap_f_le hk c ε r (le_of_lt hε) d⟩ := by
    intro z
    rcases Quot.exists_rep z with ⟨s, hs⟩
    cases s with
    | inl d =>
        apply Subtype.ext
        rw [← hs]
        change (morseHandleAdjunctionToUpperSublevel hk c ε r data hε hεr'
          (Handle.cell (morseAttachingEmbedding hk c ε r data hε (le_of_lt hεr')) d) : M) =
          (morseHandleAdjunctionHomeoUnion hk c ε r data hε hr (le_of_lt hεr') hcont
            (Handle.cell (morseAttachingEmbedding hk c ε r data hε (le_of_lt hεr')) d)).1
        rw [morseHandleAdjunctionToUpperSublevel_cell hk c ε r data hε hεr' d]
        rw [morseHandleAdjunctionHomeoUnion_cell hk c ε r data hε hr (le_of_lt hεr') hcont d]
        rfl
    | inr x =>
        apply Subtype.ext
        rw [← hs]
        change (morseHandleAdjunctionToUpperSublevel hk c ε r data hε hεr'
          (Handle.lower (morseAttachingEmbedding hk c ε r data hε (le_of_lt hεr')) x) : M) =
          (morseHandleAdjunctionHomeoUnion hk c ε r data hε hr (le_of_lt hεr') hcont
            (Handle.lower (morseAttachingEmbedding hk c ε r data hε (le_of_lt hεr')) x)).1
        rw [morseHandleAdjunctionToUpperSublevel_lower hk c ε r data hε hεr' x]
        rw [morseHandleAdjunctionHomeoUnion_lower hk c ε r data hε hr (le_of_lt hεr') hcont x]
  intro z w h
  apply H.injective
  apply Subtype.ext
  have hz := congrArg Subtype.val (hfact z)
  have hw := congrArg Subtype.val (hfact w)
  have hval := congrArg Subtype.val h
  exact hz.symm.trans (hval.trans hw)

noncomputable def morseHandleAdjunctionImage {m k : ℕ} (hk : k ≤ m + 1) (c ε r : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} {f : M → ℝ}
    (data : MorseChart (m + 1) k hk c I f) :
    Set (SublevelSpace f (c + r ^ 2 / 2)) :=
  {y : SublevelSpace f (c + r ^ 2 / 2) |
    f y.1 ≤ c - ε ∨ y.1 ∈ data.χ '' (modelHandle hk ε r : Set (MorseModel (m + 1)))}

theorem morseHandleAdjunctionToUpperSublevel_mem_image {m k : ℕ} (hk : k ≤ m + 1) (c ε r : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} {f : M → ℝ}
    (data : MorseChart (m + 1) k hk c I f)
    (hε : 0 < ε) (hεr' : Real.sqrt (2 * ε + 2 * r ^ 2) < data.R)
    (z : Handle.AdjunctionSpace k (m + 1 - k)
      (morseAttachingEmbedding hk c ε r data hε (le_of_lt hεr'))) :
    morseHandleAdjunctionToUpperSublevel hk c ε r data hε hεr' z ∈
      morseHandleAdjunctionImage hk c ε r data := by
  rcases Quot.exists_rep z with ⟨s, hs⟩
  cases s with
  | inl d =>
      have hz : z = Handle.cell (morseAttachingEmbedding hk c ε r data hε (le_of_lt hεr')) d := by
        simpa using hs.symm
      rw [hz]
      dsimp [morseHandleAdjunctionImage]
      refine Or.inr ?_
      refine ⟨modelHandleMap hk ε r d, modelHandleMap_mem hk ε r (le_of_lt hε) d, ?_⟩
      rw [← morseHandleAdjunctionToUpperSublevel_cell hk c ε r data hε hεr' d]
  | inr x =>
      have hz : z = Handle.lower (morseAttachingEmbedding hk c ε r data hε (le_of_lt hεr')) x := by
        simpa using hs.symm
      rw [hz]
      dsimp [morseHandleAdjunctionImage]
      exact Or.inl (by
        change f (morseHandleAdjunctionToUpperSublevel hk c ε r data hε hεr'
          (Handle.lower (morseAttachingEmbedding hk c ε r data hε (le_of_lt hεr')) x)).1 ≤ c - ε
        rw [morseHandleAdjunctionToUpperSublevel_lower hk c ε r data hε hεr' x]
        exact x.2)

theorem morseHandleAdjunctionToUpperSublevel_image_subset {m k : ℕ} (hk : k ≤ m + 1) (c ε r : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} {f : M → ℝ}
    (data : MorseChart (m + 1) k hk c I f)
    (hε : 0 < ε) (hεr' : Real.sqrt (2 * ε + 2 * r ^ 2) < data.R) (hr : 0 < r)
    (y : SublevelSpace f (c + r ^ 2 / 2))
    (hy : y ∈ morseHandleAdjunctionImage hk c ε r data) :
    ∃ z : Handle.AdjunctionSpace k (m + 1 - k)
      (morseAttachingEmbedding hk c ε r data hε (le_of_lt hεr')),
      morseHandleAdjunctionToUpperSublevel hk c ε r data hε hεr' z = y := by
  rcases hy with hy | hy
  · refine ⟨Handle.lower (morseAttachingEmbedding hk c ε r data hε (le_of_lt hεr'))
      (⟨y.1, hy⟩ : SublevelSpace f (c - ε)), ?_⟩
    apply Subtype.ext
    rw [morseHandleAdjunctionToUpperSublevel_lower hk c ε r data hε hεr' ⟨y.1, hy⟩]
  · rcases hy with ⟨w, hw, hwy⟩
    have hw' : w ∈ Set.range (modelHandleMap hk ε r) := by
      simpa [← modelHandleMap_range hk ε r hε hr] using hw
    rcases hw' with ⟨d, hd⟩
    refine ⟨Handle.cell (morseAttachingEmbedding hk c ε r data hε (le_of_lt hεr')) d, ?_⟩
    apply Subtype.ext
    change (morseHandleAdjunctionToUpperSublevel hk c ε r data hε hεr'
      (Handle.cell (morseAttachingEmbedding hk c ε r data hε (le_of_lt hεr')) d) : M) = y.1
    rw [morseHandleAdjunctionToUpperSublevel_cell hk c ε r data hε hεr' d]
    rw [hd]
    rw [hwy]

theorem morseHandleAdjunctionToUpperSublevel_range {m k : ℕ} (hk : k ≤ m + 1) (c ε r : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} {f : M → ℝ}
    (data : MorseChart (m + 1) k hk c I f)
    (hε : 0 < ε) (hεr' : Real.sqrt (2 * ε + 2 * r ^ 2) < data.R) (hr : 0 < r) :
    Set.range (morseHandleAdjunctionToUpperSublevel hk c ε r data hε hεr') =
      morseHandleAdjunctionImage hk c ε r data := by
  ext y
  constructor
  · intro hy
    rcases hy with ⟨z, rfl⟩
    exact morseHandleAdjunctionToUpperSublevel_mem_image hk c ε r data hε hεr' z
  · intro hy
    exact morseHandleAdjunctionToUpperSublevel_image_subset hk c ε r data hε hεr' hr y hy

noncomputable def morseHandleAdjunctionToUpperSublevelInv {m k : ℕ} (hk : k ≤ m + 1) (c ε r : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} {f : M → ℝ}
    (data : MorseChart (m + 1) k hk c I f)
    (hε : 0 < ε) (hεr' : Real.sqrt (2 * ε + 2 * r ^ 2) < data.R) (hr : 0 < r)
    (y : {y' : SublevelSpace f (c + r ^ 2 / 2) // y' ∈ morseHandleAdjunctionImage hk c ε r data}) :
    Handle.AdjunctionSpace k (m + 1 - k) (morseAttachingEmbedding hk c ε r data hε (le_of_lt hεr')) := by
  classical
  by_cases hlow : f y.1 ≤ c - ε
  · exact Handle.lower (morseAttachingEmbedding hk c ε r data hε (le_of_lt hεr')) ⟨y.1, hlow⟩
  · have hcell : (y.1 : M) ∈ data.χ '' (modelHandle hk ε r : Set (MorseModel (m + 1))) := by
      by_contra hnot
      exact hlow (by
        rcases y.2 with hlow' | hcell
        · exact hlow'
        · exact False.elim (hnot hcell))
    let w : MorseModel (m + 1) := Classical.choose hcell
    have hw : w ∈ modelHandle hk ε r := (Classical.choose_spec hcell).1
    have hw' : w ∈ Set.range (modelHandleMap hk ε r) := by
      simpa [← modelHandleMap_range hk ε r hε hr] using hw
    let d : StandardHandle k (m + 1 - k) := Classical.choose hw'
    exact Handle.cell (morseAttachingEmbedding hk c ε r data hε (le_of_lt hεr')) d

theorem morseHandleAdjunctionToUpperSublevel_right_inv {m k : ℕ} (hk : k ≤ m + 1) (c ε r : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} {f : M → ℝ}
    (data : MorseChart (m + 1) k hk c I f)
    (hε : 0 < ε) (hεr' : Real.sqrt (2 * ε + 2 * r ^ 2) < data.R) (hr : 0 < r)
    (y : {y' : SublevelSpace f (c + r ^ 2 / 2) // y' ∈ morseHandleAdjunctionImage hk c ε r data}) :
    morseHandleAdjunctionToUpperSublevel hk c ε r data hε hεr'
      (morseHandleAdjunctionToUpperSublevelInv hk c ε r data hε hεr' hr y) = y := by
  classical
  dsimp [morseHandleAdjunctionToUpperSublevelInv]
  by_cases hlow : f y.1 ≤ c - ε
  · rw [dif_pos hlow]
    apply Subtype.ext
    rw [morseHandleAdjunctionToUpperSublevel_lower hk c ε r data hε hεr' ⟨y.1, hlow⟩]
  · rw [dif_neg hlow]
    have hcell : (y.1 : M) ∈ data.χ '' (modelHandle hk ε r : Set (MorseModel (m + 1))) := by
      rcases y.2 with hlow' | hcell
      · exact False.elim (hlow hlow')
      · exact hcell
    let w : MorseModel (m + 1) := Classical.choose hcell
    have hw : w ∈ modelHandle hk ε r := (Classical.choose_spec hcell).1
    have hwy : data.χ w = (y.1 : M) := (Classical.choose_spec hcell).2
    have hw' : w ∈ Set.range (modelHandleMap hk ε r) := by
      simpa [← modelHandleMap_range hk ε r hε hr] using hw
    let d : StandardHandle k (m + 1 - k) := Classical.choose hw'
    have hd : modelHandleMap hk ε r d = w := Classical.choose_spec hw'
    apply Subtype.ext
    change (morseHandleAdjunctionToUpperSublevel hk c ε r data hε hεr'
      (Handle.cell (morseAttachingEmbedding hk c ε r data hε (le_of_lt hεr')) d) : M) = y.1
    rw [morseHandleAdjunctionToUpperSublevel_cell hk c ε r data hε hεr' d]
    rw [hd]
    rw [hwy]

theorem morseHandleAdjunctionToUpperSublevel_left_inv {m k : ℕ} (hk : k ≤ m + 1) (c ε r : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} {f : M → ℝ}
    (data : MorseChart (m + 1) k hk c I f)
    (hε : 0 < ε) (hεr' : Real.sqrt (2 * ε + 2 * r ^ 2) < data.R) (hr : 0 < r)
    (hcont : Continuous f)
    (z : Handle.AdjunctionSpace k (m + 1 - k)
      (morseAttachingEmbedding hk c ε r data hε (le_of_lt hεr'))) :
    morseHandleAdjunctionToUpperSublevelInv hk c ε r data hε hεr' hr
      ⟨morseHandleAdjunctionToUpperSublevel hk c ε r data hε hεr' z,
        morseHandleAdjunctionToUpperSublevel_mem_image hk c ε r data hε hεr' z⟩ = z := by
  apply morseHandleAdjunctionToUpperSublevel_injective hk c ε r data hε (ne_of_gt hr) hεr' hcont
  exact morseHandleAdjunctionToUpperSublevel_right_inv hk c ε r data hε hεr' hr
    ⟨morseHandleAdjunctionToUpperSublevel hk c ε r data hε hεr' z,
      morseHandleAdjunctionToUpperSublevel_mem_image hk c ε r data hε hεr' z⟩

theorem morseHandleAdjunctionInv_eq_cell_coherence {m k : ℕ} (hk : k ≤ m + 1) (c ε r : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} {f : M → ℝ}
    (data : MorseChart (m + 1) k hk c I f)
    (hε : 0 < ε) (hεr' : Real.sqrt (2 * ε + 2 * r ^ 2) < data.R) (hr : 0 < r)
    (y : {y' : SublevelSpace f (c + r ^ 2 / 2) // y' ∈ morseHandleAdjunctionImage hk c ε r data})
    (hy : (y.1 : M) ∈ data.χ '' (modelHandle hk ε r : Set (MorseModel (m + 1))))
    (hbound : f (y.1 : M) ≤ c - ε) :
    morseHandleAdjunctionToUpperSublevelInv hk c ε r data hε hεr' hr y =
      Handle.cell (morseAttachingEmbedding hk c ε r data hε (le_of_lt hεr'))
        (modelHandleMapRawSymm hk ε r (data.χ.symm (y.1 : M))) := by
  rcases hy with ⟨w, hw, hwy⟩
  have hw' : w ∈ Set.range (modelHandleMap hk ε r) := by
    simpa [← modelHandleMap_range hk ε r hε hr] using hw
  rcases hw' with ⟨d, hd⟩
  have hbound' : morseNorm (m + 1) w ≤ data.R := by
    rw [← hd]
    exact le_trans (modelHandleMap_norm_le hk ε r (le_of_lt hε) d) (le_of_lt hεr')
  have hsrc : w ∈ data.χ.source := data.hχsrc w hbound'
  have hsymm : data.χ.symm (y.1 : M) = w := by
    rw [← hwy]
    exact data.χ.left_inv hsrc
  have hmNF : morseNormalForm hk c w = c - ε := by
    have hle : morseNormalForm hk c w ≤ c - ε := by
      rw [← data.hnorm w hbound', hwy]
      exact hbound
    have hge : c - ε ≤ morseNormalForm hk c w := by
      have hmem : w ∈ ({z : MorseModel (m + 1) | ‖posPart hk z‖ ≤ r} ∩
          {z : MorseModel (m + 1) | c - ε ≤ morseNormalForm hk c z}) := by
        simpa [modelHandle_eq_inter hk c ε r (le_of_lt hr)] using hw
      exact hmem.2
    exact le_antisymm hle hge
  have hd₁ : ‖(d.1 : EuclideanSpace ℝ (Fin k))‖ = 1 := by
    have hnf : morseNormalForm hk c (modelHandleMap hk ε r d) ≤ c - ε := by
      rw [hd]
      exact le_of_eq hmNF
    exact (modelHandleMap_mem_lower_iff hk c ε r hε d).1 hnf
  let u₀ : CellBoundary k := ⟨(d.1 : EuclideanSpace ℝ (Fin k)), hd₁⟩
  let p : AttachingRegion k (m + 1 - k) := (u₀, d.2)
  have hdi : d = attachingInclusion k (m + 1 - k) p := by
    dsimp [p, u₀]
    apply Prod.ext
    · apply Subtype.ext
      rfl
    · rfl
  have hraw : modelHandleMapRawSymm hk ε r w = attachingInclusion k (m + 1 - k) p := by
    rw [modelHandleMapRawSymm_eq_symm hk ε r hε hr w hw]
    apply modelHandleMap_injective hk ε r hε (ne_of_gt hr)
    calc
      modelHandleMap hk ε r ((morseModelHandleMapHomeo hk ε r hε hr).symm ⟨w, hw⟩) = w :=
        morseModelHandleMapHomeo_symm_apply hk ε r hε hr ⟨w, hw⟩
      _ = modelHandleMap hk ε r (attachingInclusion k (m + 1 - k) p) := by
        rw [← hd, ← hdi]
  have hφ : (morseAttachingEmbedding hk c ε r data hε (le_of_lt hεr') p : M) = (y.1 : M) := by
    rw [morseAttachingEmbedding_eq_handleEmbedding hk c ε r data hε (le_of_lt hεr') p]
    change data.χ (modelHandleMap hk ε r (attachingInclusion k (m + 1 - k) p)) = (y.1 : M)
    rw [← hdi]
    rw [hd]
    exact hwy
  dsimp [morseHandleAdjunctionToUpperSublevelInv]
  rw [dif_pos hbound]
  rw [hsymm, hraw]
  calc
    Handle.lower (morseAttachingEmbedding hk c ε r data hε (le_of_lt hεr')) ⟨(y.1 : M), hbound⟩ =
        Handle.lower (morseAttachingEmbedding hk c ε r data hε (le_of_lt hεr'))
          (morseAttachingEmbedding hk c ε r data hε (le_of_lt hεr') p) := by
      congr 1
      apply Subtype.ext
      exact hφ.symm
    _ = Handle.cell (morseAttachingEmbedding hk c ε r data hε (le_of_lt hεr'))
          (attachingInclusion k (m + 1 - k) p) := by
      simpa using (adjunction_coherence (i := attachingInclusion k (m + 1 - k))
        (φ := morseAttachingEmbedding hk c ε r data hε (le_of_lt hεr')) p).symm

theorem morseHandleAdjunctionInv_eq_cell_strict {m k : ℕ} (hk : k ≤ m + 1) (c ε r : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} {f : M → ℝ}
    (data : MorseChart (m + 1) k hk c I f)
    (hε : 0 < ε) (hεr' : Real.sqrt (2 * ε + 2 * r ^ 2) < data.R) (hr : 0 < r)
    (y : {y' : SublevelSpace f (c + r ^ 2 / 2) // y' ∈ morseHandleAdjunctionImage hk c ε r data})
    (hy : (y.1 : M) ∈ data.χ '' (modelHandle hk ε r : Set (MorseModel (m + 1))))
    (hnot : ¬ f (y.1 : M) ≤ c - ε) :
    morseHandleAdjunctionToUpperSublevelInv hk c ε r data hε hεr' hr y =
      Handle.cell (morseAttachingEmbedding hk c ε r data hε (le_of_lt hεr'))
        (modelHandleMapRawSymm hk ε r (data.χ.symm (y.1 : M))) := by
  let w : MorseModel (m + 1) := Classical.choose hy
  have hw : w ∈ modelHandle hk ε r := (Classical.choose_spec hy).1
  have hwy : data.χ w = (y.1 : M) := (Classical.choose_spec hy).2
  have hsrc : w ∈ data.χ.source := by
    rcases (by simpa [← modelHandleMap_range hk ε r hε hr] using hw :
      ∃ d : StandardHandle k (m + 1 - k), modelHandleMap hk ε r d = w) with ⟨d, hd⟩
    exact data.hχsrc w (by
      rw [← hd]
      exact le_trans (modelHandleMap_norm_le hk ε r (le_of_lt hε) d) (le_of_lt hεr'))
  have hsymm : data.χ.symm (y.1 : M) = w := by
    rw [← hwy]
    exact data.χ.left_inv hsrc
  have hw' : w ∈ Set.range (modelHandleMap hk ε r) := by
    simpa [← modelHandleMap_range hk ε r hε hr] using hw
  have hraw : Classical.choose hw' = modelHandleMapRawSymm hk ε r w := by
    apply modelHandleMap_injective hk ε r hε (ne_of_gt hr)
    rw [Classical.choose_spec hw', modelHandleMapRawSymm_map hk ε r hε hr w hw]
  dsimp [morseHandleAdjunctionToUpperSublevelInv]
  rw [dif_neg hnot]
  change Handle.cell (morseAttachingEmbedding hk c ε r data hε (le_of_lt hεr'))
      (Classical.choose hw') =
    Handle.cell (morseAttachingEmbedding hk c ε r data hε (le_of_lt hεr'))
      (modelHandleMapRawSymm hk ε r (data.χ.symm (y.1 : M)))
  rw [hsymm, hraw]

theorem continuousOn_morseHandleAdjunctionInv_cell {m k : ℕ} (hk : k ≤ m + 1) (c ε r : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} {f : M → ℝ}
    (data : MorseChart (m + 1) k hk c I f)
    (hε : 0 < ε) (hεr' : Real.sqrt (2 * ε + 2 * r ^ 2) < data.R) (hr : 0 < r) :
    ContinuousOn (morseHandleAdjunctionToUpperSublevelInv hk c ε r data hε hεr' hr)
      {y : {y' : SublevelSpace f (c + r ^ 2 / 2) // y' ∈ morseHandleAdjunctionImage hk c ε r data} |
        (y.1 : M) ∈ data.χ '' (modelHandle hk ε r : Set (MorseModel (m + 1)))} := by
  let S : Set {y' : SublevelSpace f (c + r ^ 2 / 2) // y' ∈ morseHandleAdjunctionImage hk c ε r data} :=
    {y : {y' : SublevelSpace f (c + r ^ 2 / 2) // y' ∈ morseHandleAdjunctionImage hk c ε r data} |
      (y.1 : M) ∈ data.χ '' (modelHandle hk ε r : Set (MorseModel (m + 1)))}
  let g : S → Handle.AdjunctionSpace k (m + 1 - k)
      (morseAttachingEmbedding hk c ε r data hε (le_of_lt hεr')) :=
    fun y => Handle.cell (morseAttachingEmbedding hk c ε r data hε (le_of_lt hεr'))
      (modelHandleMapRawSymm hk ε r (data.χ.symm (y.1 : M)))
  have hproj : Continuous (fun y : S => (y.1 : M)) := by
    exact continuous_subtype_val.comp (continuous_subtype_val.comp continuous_subtype_val)
  have hχ : Continuous (fun y : S => data.χ.symm (y.1 : M)) := by
    have hmaps : Set.MapsTo (fun y : S => (y.1 : M)) Set.univ data.χ.target := by
      intro y hy
      rcases y.2 with ⟨w, hw, hwy⟩
      simpa [hwy] using data.χ.map_source (data.hχsrc w (by
        rcases (by simpa [← modelHandleMap_range hk ε r hε hr] using hw :
          ∃ d : StandardHandle k (m + 1 - k), modelHandleMap hk ε r d = w) with ⟨d, hd⟩
        rw [← hd]
        exact le_trans (modelHandleMap_norm_le hk ε r (le_of_lt hε) d) (le_of_lt hεr')))
    exact (continuousOn_univ.mp (data.χ.continuousOn_invFun.comp hproj.continuousOn hmaps))
  have hmain : Continuous (fun y : S =>
      Handle.cell (morseAttachingEmbedding hk c ε r data hε (le_of_lt hεr'))
        (modelHandleMapRawSymm hk ε r (data.χ.symm (y.1 : M)))) := by
    exact (continuous_cell (morseAttachingEmbedding hk c ε r data hε (le_of_lt hεr'))).comp
      (by
        have hraw : Continuous (modelHandleMapRawSymm hk ε r) := by
          dsimp [modelHandleMapRawSymm]
          refine Continuous.prodMk ?_ ?_
          · exact (continuous_closedCellClamp k).comp (by
              have hsqrt : Continuous (fun y : MorseModel (m + 1) =>
                  (Real.sqrt (2 * ε + ‖posPart hk y‖ ^ 2))⁻¹) := by
                refine Continuous.inv₀ ?_ (fun y => ?_)
                · exact Real.continuous_sqrt.comp (by
                    have hnorm : Continuous (fun y : MorseModel (m + 1) => ‖posPart hk y‖) :=
                      continuous_norm.comp (continuous_posPart hk)
                    have hpow : Continuous (fun y : MorseModel (m + 1) => ‖posPart hk y‖ ^ 2) := hnorm.pow 2
                    exact (continuous_const.add hpow : Continuous (fun y : MorseModel (m + 1) =>
                      2 * ε + ‖posPart hk y‖ ^ 2)))
                · exact ne_of_gt (by positivity : 0 < Real.sqrt (2 * ε + ‖posPart hk y‖ ^ 2))
              exact hsqrt.smul (continuous_negPart hk))
          · exact (continuous_closedCellClamp (m + 1 - k)).comp (by
              have hscalar : Continuous (fun _ : MorseModel (m + 1) => (r⁻¹ : ℝ)) := continuous_const
              exact hscalar.smul (continuous_posPart hk))
        exact hraw.comp hχ)
  have hg : Continuous g := by
    dsimp [g]
    exact hmain
  have hmain2 : ContinuousOn (fun y : S =>
      morseHandleAdjunctionToUpperSublevelInv hk c ε r data hε hεr' hr
        (y : {y' : SublevelSpace f (c + r ^ 2 / 2) // y' ∈ morseHandleAdjunctionImage hk c ε r data})) Set.univ := by
    refine (continuousOn_congr (s := Set.univ)
      (g := fun y : S => morseHandleAdjunctionToUpperSublevelInv hk c ε r data hε hεr' hr
        (y : {y' : SublevelSpace f (c + r ^ 2 / 2) // y' ∈ morseHandleAdjunctionImage hk c ε r data}))
      (f := g) ?_).mpr hg.continuousOn
    intro y hy
    dsimp [g]
    by_cases hlow : f (y.1 : M) ≤ c - ε
    · exact morseHandleAdjunctionInv_eq_cell_coherence hk c ε r data hε hεr' hr
        (y : {y' : SublevelSpace f (c + r ^ 2 / 2) // y' ∈ morseHandleAdjunctionImage hk c ε r data}) y.2 hlow
    · exact morseHandleAdjunctionInv_eq_cell_strict hk c ε r data hε hεr' hr
        (y : {y' : SublevelSpace f (c + r ^ 2 / 2) // y' ∈ morseHandleAdjunctionImage hk c ε r data}) y.2 hlow
  rw [continuousOn_iff_continuous_restrict]
  simpa [S] using (continuousOn_univ.mp hmain2)

theorem continuousOn_morseHandleAdjunctionInv_lower {m k : ℕ} (hk : k ≤ m + 1) (c ε r : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} {f : M → ℝ}
    (data : MorseChart (m + 1) k hk c I f)
    (hε : 0 < ε) (hεr' : Real.sqrt (2 * ε + 2 * r ^ 2) < data.R) (hr : 0 < r) :
    ContinuousOn (morseHandleAdjunctionToUpperSublevelInv hk c ε r data hε hεr' hr)
      {y : {y' : SublevelSpace f (c + r ^ 2 / 2) // y' ∈ morseHandleAdjunctionImage hk c ε r data} |
        f (y.1 : M) ≤ c - ε} := by
  let S : Set {y' : SublevelSpace f (c + r ^ 2 / 2) // y' ∈ morseHandleAdjunctionImage hk c ε r data} :=
    {y : {y' : SublevelSpace f (c + r ^ 2 / 2) // y' ∈ morseHandleAdjunctionImage hk c ε r data} |
      f (y.1 : M) ≤ c - ε}
  let g : S → Handle.AdjunctionSpace k (m + 1 - k)
      (morseAttachingEmbedding hk c ε r data hε (le_of_lt hεr')) :=
    fun y => Handle.lower (morseAttachingEmbedding hk c ε r data hε (le_of_lt hεr'))
      (⟨(y.1 : M), y.2⟩ : SublevelSpace f (c - ε))
  have hproj : Continuous (fun y : S => (y.1 : M)) := by
    exact continuous_subtype_val.comp (continuous_subtype_val.comp continuous_subtype_val)
  have hg : Continuous g := by
    dsimp [g]
    exact (continuous_lower (morseAttachingEmbedding hk c ε r data hε (le_of_lt hεr'))).comp
      (Continuous.subtype_mk hproj (fun y => y.2))
  have hmain2 : ContinuousOn (fun y : S =>
      morseHandleAdjunctionToUpperSublevelInv hk c ε r data hε hεr' hr
        (y : {y' : SublevelSpace f (c + r ^ 2 / 2) // y' ∈ morseHandleAdjunctionImage hk c ε r data})) Set.univ := by
    refine (continuousOn_congr (s := Set.univ)
      (g := fun y : S => morseHandleAdjunctionToUpperSublevelInv hk c ε r data hε hεr' hr
        (y : {y' : SublevelSpace f (c + r ^ 2 / 2) // y' ∈ morseHandleAdjunctionImage hk c ε r data}))
      (f := g) ?_).mpr hg.continuousOn
    intro y hy
    dsimp [g]
    dsimp [morseHandleAdjunctionToUpperSublevelInv]
    have hcond : f (y.1 : M) ≤ c - ε := y.2
    rw [dif_pos hcond]
  rw [continuousOn_iff_continuous_restrict]
  simpa [S] using (continuousOn_univ.mp hmain2)

theorem continuous_morseHandleAdjunctionInv {m k : ℕ} (hk : k ≤ m + 1) (c ε r : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} {f : M → ℝ}
    (data : MorseChart (m + 1) k hk c I f)
    (hε : 0 < ε) (hεr' : Real.sqrt (2 * ε + 2 * r ^ 2) < data.R) (hr : 0 < r)
    (hcont : Continuous f) :
    Continuous (morseHandleAdjunctionToUpperSublevelInv hk c ε r data hε hεr' hr) := by
  let S₁ : Set {y' : SublevelSpace f (c + r ^ 2 / 2) // y' ∈ morseHandleAdjunctionImage hk c ε r data} :=
    {y : {y' : SublevelSpace f (c + r ^ 2 / 2) // y' ∈ morseHandleAdjunctionImage hk c ε r data} |
      f (y.1 : M) ≤ c - ε}
  let S₂ : Set {y' : SublevelSpace f (c + r ^ 2 / 2) // y' ∈ morseHandleAdjunctionImage hk c ε r data} :=
    {y : {y' : SublevelSpace f (c + r ^ 2 / 2) // y' ∈ morseHandleAdjunctionImage hk c ε r data} |
      (y.1 : M) ∈ data.χ '' (modelHandle hk ε r : Set (MorseModel (m + 1)))}
  have hsrc_all : ∀ w ∈ modelHandle hk ε r, w ∈ data.χ.source := by
    intro w hw
    rcases (by simpa [← modelHandleMap_range hk ε r hε hr] using hw :
      ∃ d : StandardHandle k (m + 1 - k), modelHandleMap hk ε r d = w) with ⟨d, hd⟩
    exact data.hχsrc w (by
      rw [← hd]
      exact le_trans (modelHandleMap_norm_le hk ε r (le_of_lt hε) d) (le_of_lt hεr'))
  have hclosed₁ : IsClosed S₁ := by
    dsimp [S₁]
    exact IsClosed.preimage (hcont.comp (continuous_subtype_val.comp continuous_subtype_val))
      (isClosed_Iic (a := c - ε))
  have hclosed₂ : IsClosed S₂ := by
    have hcomp : IsCompact (data.χ '' (modelHandle hk ε r : Set (MorseModel (m + 1)))) := by
      have hcomp' : IsCompact (modelHandle hk ε r : Set (MorseModel (m + 1))) := by
        rw [← modelHandleMap_range hk ε r hε hr]
        simpa using (IsCompact.image isCompact_univ (continuous_modelHandleMap hk ε r))
      exact IsCompact.image_of_continuousOn hcomp' (data.χ.continuousOn_toFun.mono (fun w hw => hsrc_all w hw))
    dsimp [S₂]
    exact IsClosed.preimage (continuous_subtype_val.comp continuous_subtype_val)
      hcomp.isClosed
  have hunion : Set.univ = S₁ ∪ S₂ := by
    ext y
    constructor
    · intro hy
      rcases y.2 with h₁ | h₂
      · exact Or.inl h₁
      · exact Or.inr h₂
    · intro hy
      trivial
  exact continuousOn_univ.mp (by
    rw [hunion]
    exact (continuousOn_morseHandleAdjunctionInv_lower hk c ε r data hε hεr' hr).union_of_isClosed
      (continuousOn_morseHandleAdjunctionInv_cell hk c ε r data hε hεr' hr) hclosed₁ hclosed₂)

noncomputable def morseHandleAdjunctionHomeoImage {m k : ℕ} (hk : k ≤ m + 1) (c ε r : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} {f : M → ℝ}
    (data : MorseChart (m + 1) k hk c I f)
    (hε : 0 < ε) (hεr' : Real.sqrt (2 * ε + 2 * r ^ 2) < data.R) (hr : 0 < r)
    (hcont : Continuous f) :
    Handle.AdjunctionSpace k (m + 1 - k) (morseAttachingEmbedding hk c ε r data hε (le_of_lt hεr')) ≃ₜ
      {y : SublevelSpace f (c + r ^ 2 / 2) // y ∈ morseHandleAdjunctionImage hk c ε r data} where
  toFun := fun z => ⟨morseHandleAdjunctionToUpperSublevel hk c ε r data hε hεr' z,
    morseHandleAdjunctionToUpperSublevel_mem_image hk c ε r data hε hεr' z⟩
  invFun := morseHandleAdjunctionToUpperSublevelInv hk c ε r data hε hεr' hr
  left_inv := fun z => morseHandleAdjunctionToUpperSublevel_left_inv hk c ε r data hε hεr' hr hcont z
  right_inv := fun y => by
    apply Subtype.ext
    simpa using (morseHandleAdjunctionToUpperSublevel_right_inv hk c ε r data hε hεr' hr y)
  continuous_toFun := Continuous.subtype_mk (continuous_morseHandleAdjunctionToUpperSublevel hk c ε r data hε hεr')
    (fun z => morseHandleAdjunctionToUpperSublevel_mem_image hk c ε r data hε hεr' z)
  continuous_invFun := continuous_morseHandleAdjunctionInv hk c ε r data hε hεr' hr hcont

noncomputable def morseTopCapPreimage {n k : ℕ} (hk : k ≤ n) (ε r : ℝ)
    (w : MorseModel n) : StandardHandle k (n - k) :=
  (closedCellClamp k ((Real.sqrt (2 * ε + r ^ 2))⁻¹ •
      (if _hu : ‖negPart hk w‖ = 0 then 0 else
        Real.sqrt (‖negPart hk w‖ ^ 2 + r ^ 2 - ‖posPart hk w‖ ^ 2) •
          (‖negPart hk w‖⁻¹ • negPart hk w))),
    closedCellClamp (n - k) (‖posPart hk w‖⁻¹ • posPart hk w))

noncomputable def morseTopCapPushdown {n k : ℕ} (hk : k ≤ n) (r : ℝ)
    (w : MorseModel n) : MorseModel n :=
  recombine hk
    (if _hu : ‖negPart hk w‖ = 0 then 0 else
      Real.sqrt (‖negPart hk w‖ ^ 2 + r ^ 2 - ‖posPart hk w‖ ^ 2) •
        (‖negPart hk w‖⁻¹ • negPart hk w))
    (r • (‖posPart hk w‖⁻¹ • posPart hk w))

theorem morseTopCapPushdown_mem_modelHandle {n k : ℕ} (hk : k ≤ n) (c ε r : ℝ)
    (hε : 0 < ε) (hr : 0 < r) (w : MorseModel n)
    (hup : morseNormalForm hk c w ≤ c + r ^ 2 / 2)
    (hgt : c - ε < morseNormalForm hk c w)
    (hout : r < ‖posPart hk w‖) :
    morseTopCapPushdown hk r w ∈ modelHandle hk ε r := by
  have hpos : 0 < ‖posPart hk w‖ := lt_trans hr hout
  have hv : ‖posPart hk (morseTopCapPushdown hk r w)‖ = r := by
    dsimp [morseTopCapPushdown]
    rw [posPart_recombine]
    have hvhat : ‖(‖posPart hk w‖⁻¹ • posPart hk w : EuclideanSpace ℝ (Fin (n - k)))‖ = 1 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (le_of_lt hpos))]
      rw [mul_comm, ← div_eq_mul_inv]
      exact div_self (ne_of_gt hpos)
    rw [norm_smul, hvhat]
    rw [Real.norm_eq_abs, abs_of_nonneg (le_of_lt hr), mul_one]
  change ‖posPart hk (morseTopCapPushdown hk r w)‖ ^ 2 ≤ r ^ 2 ∧
    ‖negPart hk (morseTopCapPushdown hk r w)‖ ^ 2 ≤ ‖posPart hk (morseTopCapPushdown hk r w)‖ ^ 2 + 2 * ε
  constructor
  · rw [hv, sq]
  · have hu : ‖negPart hk (morseTopCapPushdown hk r w)‖ ^ 2 ≤ r ^ 2 + 2 * ε := by
      dsimp [morseTopCapPushdown]
      rw [negPart_recombine]
      by_cases hu0 : ‖negPart hk w‖ = 0
      · rw [if_pos hu0, norm_zero, zero_pow (by norm_num : 2 ≠ 0)]
        positivity
      · have hne : negPart hk w ≠ 0 := fun h => hu0 (by simpa using (norm_eq_zero.mpr h))
        have hsqrt_nonneg : 0 ≤ ‖negPart hk w‖ ^ 2 + r ^ 2 - ‖posPart hk w‖ ^ 2 := by
          have hnf : ‖posPart hk w‖ ^ 2 - ‖negPart hk w‖ ^ 2 ≤ r ^ 2 := by
            have hsplit := morseNormalForm_split hk c w
            rw [hsplit] at hup
            nlinarith
          nlinarith
        have hle : ‖negPart hk w‖ ^ 2 + r ^ 2 - ‖posPart hk w‖ ^ 2 ≤ r ^ 2 + 2 * ε := by
          have hnf : ‖negPart hk w‖ ^ 2 - ‖posPart hk w‖ ^ 2 < 2 * ε := by
            have hsplit := morseNormalForm_split hk c w
            rw [hsplit] at hgt
            nlinarith
          nlinarith
        have hunit : ‖‖negPart hk w‖⁻¹ • negPart hk w‖ = 1 := by
          simpa using (norm_smul_inv_norm hne)
        rw [if_neg hu0]
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
          hunit, mul_one]
        rw [Real.sq_sqrt hsqrt_nonneg]
        exact hle
    rw [hv, sq]
    nlinarith [hε]

noncomputable def morseCollarTopLevel {m k : ℕ} (hk : k ≤ m + 1) (c ε r : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} {f : M → ℝ}
    {f₀ : M → ℝ} (data : MorseChart (m + 1) k hk c I f₀)
    (x : LevelSetSpace f (c - ε)) : ℝ :=
  by
  classical
  exact if hx : x.1 ∈ data.χ '' {y : MorseModel (m + 1) | morseNorm (m + 1) y < data.R} then
    max 0 ((r ^ 2 - ‖posPart hk (data.χ.symm x.1)‖ ^ 2) / 2)
  else 0

def morseCollarChartSet {m k : ℕ} (hk : k ≤ m + 1) (c ε _r : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} {f : M → ℝ}
    {f₀ : M → ℝ} (data : MorseChart (m + 1) k hk c I f₀) :
    Set (LevelSetSpace f (c - ε)) :=
  {x : LevelSetSpace f (c - ε) | x.1 ∈ data.χ '' {y : MorseModel (m + 1) |
    morseNorm (m + 1) y < data.R}}

theorem morseCollarTopLevel_eq_on_chart {m k : ℕ} (hk : k ≤ m + 1) (c ε r : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} {f : M → ℝ}
    {f₀ : M → ℝ} (data : MorseChart (m + 1) k hk c I f₀)
    (x : LevelSetSpace f (c - ε)) (hx : x ∈ morseCollarChartSet hk c ε r data) :
    morseCollarTopLevel hk c ε r data x =
      max 0 ((r ^ 2 - ‖posPart hk (data.χ.symm x.1)‖ ^ 2) / 2) := by
  dsimp [morseCollarTopLevel, morseCollarChartSet] at hx ⊢
  rw [if_pos hx]

theorem morseCollarTopLevel_eq_zero {m k : ℕ} (hk : k ≤ m + 1) (c ε r : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} {f : M → ℝ}
    {f₀ : M → ℝ} (data : MorseChart (m + 1) k hk c I f₀)
    (x : LevelSetSpace f (c - ε))
    (hx : x.1 ∉ data.χ '' {y : MorseModel (m + 1) | morseNorm (m + 1) y < data.R}) :
    morseCollarTopLevel hk c ε r data x = 0 := by
  dsimp [morseCollarTopLevel]
  rw [if_neg hx]

theorem morseCollarTopLevel_nonneg {m k : ℕ} (hk : k ≤ m + 1) (c ε r : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} {f : M → ℝ}
    {f₀ : M → ℝ} (data : MorseChart (m + 1) k hk c I f₀)
    (x : LevelSetSpace f (c - ε)) :
    0 ≤ morseCollarTopLevel hk c ε r data x := by
  by_cases hx : x.1 ∈ data.χ '' {y : MorseModel (m + 1) | morseNorm (m + 1) y < data.R}
  · rw [morseCollarTopLevel_eq_on_chart hk c ε r data x hx]
    exact le_max_left 0 ((r ^ 2 - ‖posPart hk (data.χ.symm x.1)‖ ^ 2) / 2)
  · rw [morseCollarTopLevel_eq_zero hk c ε r data x hx]

theorem morseCollarTopLevel_le {m k : ℕ} (hk : k ≤ m + 1) (c ε r : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} {f : M → ℝ}
    {f₀ : M → ℝ} (data : MorseChart (m + 1) k hk c I f₀)
    (x : LevelSetSpace f (c - ε)) :
    morseCollarTopLevel hk c ε r data x ≤ r ^ 2 / 2 := by
  by_cases hx : x.1 ∈ data.χ '' {y : MorseModel (m + 1) | morseNorm (m + 1) y < data.R}
  · rw [morseCollarTopLevel_eq_on_chart hk c ε r data x hx]
    exact max_le (div_nonneg (sq_nonneg r) (by norm_num)) (by
      have hpos : 0 ≤ ‖posPart hk (data.χ.symm x.1)‖ ^ 2 := sq_nonneg _
      nlinarith [hpos])
  · rw [morseCollarTopLevel_eq_zero hk c ε r data x hx]
    exact div_nonneg (sq_nonneg r) (by norm_num)

theorem isOpen_morseCollarChartSet {m k : ℕ} (hk : k ≤ m + 1) (c ε r : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} {f : M → ℝ}
    {f₀ : M → ℝ} (data : MorseChart (m + 1) k hk c I f₀) :
    IsOpen (morseCollarChartSet hk c ε r data : Set (LevelSetSpace f (c - ε))) := by
  have hnorm : Continuous (fun y : MorseModel (m + 1) => morseNorm (m + 1) y) := by
    dsimp [morseNorm]
    exact continuous_norm.comp (PiLp.continuous_toLp (p := (2 : ENNReal))
      (β := fun _ : Fin (m + 1) => ℝ))
  have hU : IsOpen {y : MorseModel (m + 1) | morseNorm (m + 1) y < data.R} :=
    isOpen_lt hnorm continuous_const
  have hχopen : IsOpen (data.χ '' {y : MorseModel (m + 1) | morseNorm (m + 1) y < data.R}) :=
    isOpen_chiBallImage data.χ data.R (fun y hy => data.hχsrc y (le_of_lt hy))
  dsimp [morseCollarChartSet]
  exact hχopen.preimage continuous_subtype_val

theorem morseCollarTopLevel_eq_zero_of_posPart_norm {m k : ℕ} (hk : k ≤ m + 1) (c ε r : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} {f : M → ℝ}
    {f₀ : M → ℝ} (data : MorseChart (m + 1) k hk c I f₀)
    (x : LevelSetSpace f (c - ε))
    (hx : x.1 ∈ data.χ '' {y : MorseModel (m + 1) | morseNorm (m + 1) y < data.R})
    (hpos : r ^ 2 ≤ ‖posPart hk (data.χ.symm x.1)‖ ^ 2) :
    morseCollarTopLevel hk c ε r data x = 0 := by
  rw [morseCollarTopLevel_eq_on_chart hk c ε r data x hx]
  have hle : (r ^ 2 - ‖posPart hk (data.χ.symm x.1)‖ ^ 2) / 2 ≤ 0 := by
    nlinarith [hpos]
  exact max_eq_left hle

theorem isCompact_morseCollarClosedBall (m : ℕ) (R : ℝ) :
    IsCompact ({y : MorseModel (m + 1) | morseNorm (m + 1) y ≤ R}) := by
  have hnorm : Continuous (fun y : MorseModel (m + 1) => morseNorm (m + 1) y) := by
    dsimp [morseNorm]
    exact continuous_norm.comp (PiLp.continuous_toLp (p := (2 : ENNReal))
      (β := fun _ : Fin (m + 1) => ℝ))
  have hclosed : IsClosed {y : MorseModel (m + 1) | morseNorm (m + 1) y ≤ R} :=
    isClosed_le hnorm continuous_const
  have hsub : {y : MorseModel (m + 1) | morseNorm (m + 1) y ≤ R} ⊆
      Metric.closedBall (0 : MorseModel (m + 1)) R := by
    intro y hy
    simpa [Metric.mem_closedBall, dist_eq_norm, sub_zero] using
      (le_trans (supNorm_le_morseNorm y) hy)
  exact (isCompact_closedBall (0 : MorseModel (m + 1)) R).of_isClosed_subset hclosed hsub

noncomputable def morseCollarChartBallHomeo {m k : ℕ} (hk : k ≤ m + 1) (c : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H}
    {f₀ : M → ℝ} (data : MorseChart (m + 1) k hk c I f₀) :
    {y : MorseModel (m + 1) | morseNorm (m + 1) y ≤ data.R} ≃ₜ
      (data.χ '' {y : MorseModel (m + 1) | morseNorm (m + 1) y ≤ data.R}) := by
  letI : CompactSpace {y : MorseModel (m + 1) | morseNorm (m + 1) y ≤ data.R} :=
    (isCompact_iff_compactSpace (s := {y : MorseModel (m + 1) | morseNorm (m + 1) y ≤ data.R})).mp
      (isCompact_morseCollarClosedBall (m := m) data.R)
  let e : {y : MorseModel (m + 1) | morseNorm (m + 1) y ≤ data.R} ≃
      (data.χ '' {y : MorseModel (m + 1) | morseNorm (m + 1) y ≤ data.R}) :=
    { toFun := fun y => ⟨data.χ y.1, ⟨y.1, y.2, rfl⟩⟩
      invFun := fun z => ⟨data.χ.symm z.1, by
        rcases z.2 with ⟨w, hw, hwz⟩
        have hsrc : w ∈ data.χ.source := data.hχsrc w hw
        have hz : data.χ.symm z.1 = w := by
          rw [← hwz]
          exact data.χ.left_inv hsrc
        rw [hz]
        exact hw⟩
      left_inv := by
        intro y
        apply Subtype.ext
        exact data.χ.left_inv (data.hχsrc y.1 y.2)
      right_inv := by
        intro z
        apply Subtype.ext
        rcases z.2 with ⟨w, hw, hwz⟩
        have hsrc : w ∈ data.χ.source := data.hχsrc w hw
        change data.χ (data.χ.symm z.1) = z.1
        rw [← hwz]
        exact data.χ.right_inv (data.χ.map_source hsrc) }
  exact Continuous.homeoOfEquivCompactToT2 (f := e) (by
    have hcont : Continuous (fun y : {y : MorseModel (m + 1) | morseNorm (m + 1) y ≤ data.R} =>
        data.χ y.1) := by
      have hcont' : ContinuousOn data.χ {y : MorseModel (m + 1) | morseNorm (m + 1) y ≤ data.R} := by
        exact data.χ.continuousOn_toFun.mono (fun y hy => data.hχsrc y hy)
      exact continuousOn_univ.mp (hcont'.comp continuous_subtype_val.continuousOn (by
        intro y hy
        exact y.2))
    exact Continuous.subtype_mk hcont (fun y => ⟨y.1, y.2, rfl⟩))

theorem eventually_morseCollarTopLevel_eq_zero_of_chartBoundary {m k : ℕ} (hk : k ≤ m + 1)
    (c ε r : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} {f : M → ℝ}
    (data : MorseChart (m + 1) k hk c I f)
    (hε : 0 < ε)
    (hεr : Real.sqrt (2 * ε + 2 * r ^ 2) < data.R)
    (x : LevelSetSpace f (c - ε))
    (hx : x.1 ∉ data.χ '' {y : MorseModel (m + 1) | morseNorm (m + 1) y < data.R})
    (hcl : x.1 ∈ closure (data.χ '' {y : MorseModel (m + 1) | morseNorm (m + 1) y < data.R})) :
    ∀ᶠ y in nhds x, morseCollarTopLevel hk c ε r data y = 0 := by
  let S : Set M := data.χ '' {y : MorseModel (m + 1) | morseNorm (m + 1) y ≤ data.R}
  have hmem : x.1 ∈ S := by
    have hclosed : IsClosed S := by
      have hcomp : IsCompact ({y : MorseModel (m + 1) | morseNorm (m + 1) y ≤ data.R}) :=
        isCompact_morseCollarClosedBall (m := m) data.R
      have hsrc : ∀ y ∈ ({y : MorseModel (m + 1) | morseNorm (m + 1) y ≤ data.R} :
          Set (MorseModel (m + 1))), y ∈ data.χ.source := by
        intro y hy
        exact data.hχsrc y hy
      exact IsCompact.image_of_continuousOn hcomp (data.χ.continuousOn_toFun.mono
        (fun y hy => hsrc y hy)) |>.isClosed
    have hsub : data.χ '' {y : MorseModel (m + 1) | morseNorm (m + 1) y < data.R} ⊆ S := by
      intro y hy
      rcases hy with ⟨w, hw, hwy⟩
      exact ⟨w, (show morseNorm (m + 1) w ≤ data.R from le_of_lt hw), hwy⟩
    exact ((closure_mono hsub).trans hclosed.closure_subset) hcl
  let φ : {y : MorseModel (m + 1) | morseNorm (m + 1) y ≤ data.R} ≃ₜ
      (data.χ '' {y : MorseModel (m + 1) | morseNorm (m + 1) y ≤ data.R}) :=
    morseCollarChartBallHomeo (hk := hk) (c := c) (data := data)
  let O : Set {y : MorseModel (m + 1) | morseNorm (m + 1) y ≤ data.R} :=
    {y : {y : MorseModel (m + 1) | morseNorm (m + 1) y ≤ data.R} |
      Real.sqrt (2 * ε + 2 * r ^ 2) < morseNorm (m + 1) y.1}
  have hO : O ∈ nhds (φ.invFun ⟨x.1, hmem⟩) := by
    have hlt : Real.sqrt (2 * ε + 2 * r ^ 2) < morseNorm (m + 1) (φ.invFun ⟨x.1, hmem⟩).1 := by
      have hwR : data.R ≤ morseNorm (m + 1) (φ.invFun ⟨x.1, hmem⟩).1 := by
        by_contra hnot
        have hwlt : morseNorm (m + 1) (φ.invFun ⟨x.1, hmem⟩).1 < data.R := lt_of_not_ge hnot
        have hwχ : data.χ ((φ.invFun ⟨x.1, hmem⟩).1) = x.1 := by
          exact congrArg Subtype.val (φ.right_inv ⟨x.1, hmem⟩)
        exact hx ⟨(φ.invFun ⟨x.1, hmem⟩).1, hwlt, hwχ⟩
      have hle : morseNorm (m + 1) (φ.invFun ⟨x.1, hmem⟩).1 ≤ data.R :=
        (φ.invFun ⟨x.1, hmem⟩).2
      have hnorm : morseNorm (m + 1) (φ.invFun ⟨x.1, hmem⟩).1 = data.R :=
        le_antisymm hle hwR
      rw [hnorm]
      exact hεr
    exact IsOpen.mem_nhds (isOpen_lt continuous_const (by
      dsimp [morseNorm]
      exact (continuous_norm.comp (PiLp.continuous_toLp (p := (2 : ENNReal))
        (β := fun _ : Fin (m + 1) => ℝ))).comp continuous_subtype_val)) hlt
  have hpre : φ.invFun ⁻¹' O ∈ nhds (⟨x.1, hmem⟩ : S) :=
    φ.continuous_invFun.continuousAt.preimage_mem_nhds hO
  rcases (mem_nhds_subtype S ⟨x.1, hmem⟩ (φ.invFun ⁻¹' O)).mp hpre with ⟨u, hu, husub⟩
  refine Filter.mem_of_superset
    (continuous_subtype_val.continuousAt.preimage_mem_nhds hu) (by
      intro y hy
      by_cases hychart : y.1 ∈ data.χ '' {z : MorseModel (m + 1) | morseNorm (m + 1) z < data.R}
      · have hyimage : y.1 ∈ S := by
          rcases hychart with ⟨w, hw, hwy⟩
          exact ⟨w, (show morseNorm (m + 1) w ≤ data.R from le_of_lt hw), hwy⟩
        have hO' : φ.invFun ⟨y.1, hyimage⟩ ∈ O := by
          exact husub (by
            change y.1 ∈ u
            simpa using hy)
        change morseCollarTopLevel hk c ε r data y = 0
        rw [morseCollarTopLevel_eq_on_chart hk c ε r data y hychart]
        have hwbig : Real.sqrt (2 * ε + 2 * r ^ 2) < morseNorm (m + 1) (data.χ.symm y.1) := by
          have hφ : (φ.invFun ⟨y.1, hyimage⟩).1 = data.χ.symm y.1 := by
            dsimp [φ]
            rfl
          change Real.sqrt (2 * ε + 2 * r ^ 2) < morseNorm (m + 1) (φ.invFun ⟨y.1, hyimage⟩).1 at hO'
          rw [hφ] at hO'
          exact hO'
        have hpos : r ^ 2 ≤ ‖posPart hk (data.χ.symm y.1)‖ ^ 2 := by
          rcases hychart with ⟨w, hw, hwy⟩
          have hsrc : w ∈ data.χ.source := data.hχsrc w (le_of_lt hw)
          have hsymm : data.χ.symm y.1 = w := by
            rw [← hwy]
            exact data.χ.left_inv hsrc
          rw [hsymm]
          have hlevel : morseNormalForm hk c w = c - ε := by
            rw [← data.hnorm w (le_of_lt hw), hwy]
            exact y.2
          have hsplit := morseNormalForm_split hk c w
          have hnorm2 : morseNorm (m + 1) w ^ 2 = ‖posPart hk w‖ ^ 2 + ‖negPart hk w‖ ^ 2 := by
            simpa [add_comm] using (morseNorm_sq_eq_negPart_add_posPart hk w)
          have hle : ‖posPart hk w‖ ^ 2 - ‖negPart hk w‖ ^ 2 = -2 * ε := by
            rw [hsplit] at hlevel
            nlinarith [hlevel]
          have hR2 : 2 * ε + 2 * r ^ 2 < morseNorm (m + 1) w ^ 2 := by
            have habs : |Real.sqrt (2 * ε + 2 * r ^ 2)| < |morseNorm (m + 1) w| := by
              rw [abs_of_nonneg (Real.sqrt_nonneg _), abs_of_nonneg (norm_nonneg _)]
              simpa [hsymm] using hwbig
            have hsq : (Real.sqrt (2 * ε + 2 * r ^ 2)) ^ 2 < morseNorm (m + 1) w ^ 2 :=
              (sq_lt_sq).mpr habs
            rwa [Real.sq_sqrt (by nlinarith [hε, sq_nonneg r])] at hsq
          nlinarith [hle, hnorm2, hR2]
        have hle0 : (r ^ 2 - ‖posPart hk (data.χ.symm y.1)‖ ^ 2) / 2 ≤ 0 := by
          nlinarith [hpos]
        exact max_eq_left hle0
      · change morseCollarTopLevel hk c ε r data y = 0
        exact morseCollarTopLevel_eq_zero hk c ε r data y hychart)

theorem continuous_morseCollarTopLevel {m k : ℕ} (hk : k ≤ m + 1) (c ε r : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} {f : M → ℝ}
    (data : MorseChart (m + 1) k hk c I f)
    (hε : 0 < ε)
    (hεr : Real.sqrt (2 * ε + 2 * r ^ 2) < data.R) :
    Continuous (morseCollarTopLevel hk c ε r data : LevelSetSpace f (c - ε) → ℝ) := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : x.1 ∈ data.χ '' {y : MorseModel (m + 1) | morseNorm (m + 1) y < data.R}
  · have hsrc : x.1 ∈ data.χ.target := by
      rcases hx with ⟨w, hw, hwx⟩
      rw [← hwx]
      exact data.χ.map_source (data.hχsrc w (le_of_lt hw))
    have hsymm : ContinuousAt data.χ.symm x.1 := by
      exact (data.χ.continuousOn_invFun x.1 hsrc).continuousAt
        (IsOpen.mem_nhds data.χ.open_target hsrc)
    have h1 : ContinuousAt (fun y : LevelSetSpace f (c - ε) => data.χ.symm y.1) x :=
      hsymm.comp continuous_subtype_val.continuousAt
    have h2 : ContinuousAt (fun y : LevelSetSpace f (c - ε) =>
        ‖posPart hk (data.χ.symm y.1)‖ ^ 2) x := by
      exact ((continuous_norm.continuousAt.comp (continuous_posPart hk).continuousAt).comp h1).pow 2
    have hf : ContinuousAt (fun y : LevelSetSpace f (c - ε) =>
        (r ^ 2 - ‖posPart hk (data.χ.symm y.1)‖ ^ 2) / 2) x := by
      exact (continuousAt_const.sub h2).div continuousAt_const (by norm_num : (2 : ℝ) ≠ 0)
    have hg : ContinuousAt (fun y : LevelSetSpace f (c - ε) =>
        max 0 ((r ^ 2 - ‖posPart hk (data.χ.symm y.1)‖ ^ 2) / 2)) x :=
      continuousAt_const.max hf
    refine hg.congr_of_eventuallyEq ?_
    have hxopen : x ∈ morseCollarChartSet hk c ε r data := hx
    exact Filter.mem_of_superset ((isOpen_morseCollarChartSet hk c ε r data).mem_nhds hxopen) (by
      intro y hy
      change morseCollarTopLevel hk c ε r data y =
        max 0 ((r ^ 2 - ‖posPart hk (data.χ.symm y.1)‖ ^ 2) / 2)
      exact morseCollarTopLevel_eq_on_chart hk c ε r data y hy)
  · have hzero : morseCollarTopLevel hk c ε r data x = 0 :=
      morseCollarTopLevel_eq_zero hk c ε r data x hx
    change Filter.Tendsto (morseCollarTopLevel hk c ε r data) (nhds x)
      (nhds (morseCollarTopLevel hk c ε r data x))
    rw [hzero]
    exact Metric.tendsto_nhds.mpr (by
      intro δ hδ
      by_cases hcl : x.1 ∈ closure (data.χ '' {y : MorseModel (m + 1) |
          morseNorm (m + 1) y < data.R})
      · exact Filter.mem_of_superset
          (eventually_morseCollarTopLevel_eq_zero_of_chartBoundary (hk := hk) (c := c) (ε := ε)
            (r := r) (data := data) (hε := hε) (hεr := hεr) x hx hcl) (by
            intro y hy
            change morseCollarTopLevel hk c ε r data y = 0 at hy
            change dist (morseCollarTopLevel hk c ε r data y) 0 < δ
            rw [hy]
            simpa [Real.dist_eq] using hδ)
      · have hopen : IsOpen (closure (data.χ '' {y : MorseModel (m + 1) |
            morseNorm (m + 1) y < data.R}))ᶜ :=
          (isClosed_closure).isOpen_compl
        refine Filter.mem_of_superset
          (continuous_subtype_val.continuousAt.preimage_mem_nhds (hopen.mem_nhds hcl)) (by
            intro y hy
            have hychart : y.1 ∉ data.χ '' {z : MorseModel (m + 1) |
                morseNorm (m + 1) z < data.R} := by
              intro hyc
              exact hy (subset_closure hyc)
            change dist (morseCollarTopLevel hk c ε r data y) 0 < δ
            rw [morseCollarTopLevel_eq_zero (hk := hk) (c := c) (ε := ε) (r := r)
              (data := data) y hychart]
            simpa [Real.dist_eq] using hδ))

noncomputable def morseCollarLevelMap {m k : ℕ} (hk : k ≤ m + 1) (c ε r η : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} {f : M → ℝ}
    {f₀ : M → ℝ} (data : MorseChart (m + 1) k hk c I f₀)
    (x : LevelSetSpace f (c - ε)) (σ : ℝ) : ℝ :=
  -η + (morseCollarTopLevel hk c ε r data x + η) * (σ + η) / (r ^ 2 / 2 + ε + η)

theorem morseCollarLevelMap_boundary {m k : ℕ} (hk : k ≤ m + 1) (c ε r η : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} {f : M → ℝ}
    {f₀ : M → ℝ} (data : MorseChart (m + 1) k hk c I f₀)
    (x : LevelSetSpace f (c - ε)) :
    morseCollarLevelMap hk c ε r η data x (-η) = -η := by
  dsimp [morseCollarLevelMap]
  ring

theorem morseCollarLevelMap_top {m k : ℕ} (hk : k ≤ m + 1) (c ε r η : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} {f : M → ℝ}
    {f₀ : M → ℝ} (data : MorseChart (m + 1) k hk c I f₀)
    (hε : 0 < ε) (hη : 0 < η) (x : LevelSetSpace f (c - ε)) :
    morseCollarLevelMap hk c ε r η data x (r ^ 2 / 2 + ε) =
      morseCollarTopLevel hk c ε r data x := by
  dsimp [morseCollarLevelMap]
  have hden : r ^ 2 / 2 + ε + η ≠ 0 := by positivity
  calc
    -η + (morseCollarTopLevel hk c ε r data x + η) * (r ^ 2 / 2 + ε + η) / (r ^ 2 / 2 + ε + η)
        = -η + (morseCollarTopLevel hk c ε r data x + η) := by
          rw [div_eq_mul_inv, mul_assoc, mul_inv_cancel₀ hden, mul_one]
    _ = morseCollarTopLevel hk c ε r data x := by ring

theorem continuous_morseCollarLevelMap {m k : ℕ} (hk : k ≤ m + 1) (c ε r η : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} {f : M → ℝ}
    {f₀ : M → ℝ} (data : MorseChart (m + 1) k hk c I f₀)
    (hε : 0 < ε) (hη : 0 < η)
    (hTopCont : Continuous (morseCollarTopLevel hk c ε r data : LevelSetSpace f (c - ε) → ℝ)) :
    Continuous (fun p : LevelSetSpace f (c - ε) × ℝ =>
      morseCollarLevelMap hk c ε r η data p.1 p.2) := by
  dsimp [morseCollarLevelMap]
  have htop : Continuous (fun p : LevelSetSpace f (c - ε) × ℝ =>
      morseCollarTopLevel hk c ε r data p.1) :=
    hTopCont.comp continuous_fst
  have hσ : Continuous (fun p : LevelSetSpace f (c - ε) × ℝ => p.2) := continuous_snd
  have hden : Continuous (fun _ : LevelSetSpace f (c - ε) × ℝ => r ^ 2 / 2 + ε + η) := continuous_const
  have hconstη : Continuous (fun _ : LevelSetSpace f (c - ε) × ℝ => η) := continuous_const
  have hconstnegη : Continuous (fun _ : LevelSetSpace f (c - ε) × ℝ => -η) := continuous_const
  have hden0 : ∀ p : LevelSetSpace f (c - ε) × ℝ, r ^ 2 / 2 + ε + η ≠ 0 := by
    intro p
    positivity
  have hmain : Continuous (fun p : LevelSetSpace f (c - ε) × ℝ =>
      (morseCollarTopLevel hk c ε r data p.1 + η) * (p.2 + η) / (r ^ 2 / 2 + ε + η)) := by
    exact (((htop.add hconstη).mul (hσ.add hconstη)).div hden hden0)
  exact hconstnegη.add hmain

theorem morseCollarFlow_levelValue {n : ℕ} {H : Type} [TopologicalSpace H] {M : Type}
    [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
    (I : ModelWithCorners ℝ (MorseModel n) H) [I.Boundaryless]
    [IsManifold I (⊤ : WithTop ℕ∞) M] (f : M → ℝ) (c ε r η : ℝ)
    (hε : 0 < ε)
    (hη : 0 ≤ η)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) f)
    (v : (x : M) → TangentSpace I x)
    (hv : ContMDiff I (I.prod 𝓘(ℝ, MorseModel n)) ∞
      (fun x : M => (⟨x, v x⟩ : TangentBundle I M)))
    (hsupp : IsCompact (tsupport v))
    (hdfOn : ∀ x ∈ f ⁻¹' Set.Icc (c - ε - η) (c + r ^ 2 / 2),
      (NormedSpace.fromTangentSpace (f x)) ((mfderiv I 𝓘(ℝ, ℝ) f x) (v x)) = -1)
    (hrate : ∀ x,
      -1 ≤ (NormedSpace.fromTangentSpace (f x)) ((mfderiv I 𝓘(ℝ, ℝ) f x) (v x)) ∧
      (NormedSpace.fromTangentSpace (f x)) ((mfderiv I 𝓘(ℝ, ℝ) f x) (v x)) ≤ 0)
    {y : M} (hy : f y ∈ Set.Icc (c - ε - η) (c + r ^ 2 / 2)) :
    f (curveAt v (exists_globalIntegralCurve_of_compactSupport v hv hsupp) y (f y - c + ε)) = c - ε := by
  let hcomplete : ∀ x : M, ∃ γ : ℝ → M, γ 0 = x ∧ IsMIntegralCurve γ v :=
    exists_globalIntegralCurve_of_compactSupport v hv hsupp
  let σ : ℝ := f y - c + ε
  have hσ : σ ∈ Set.Icc (-η) (r ^ 2 / 2 + ε) := by
    dsimp [σ]
    constructor <;> linarith [hy.1, hy.2]
  by_cases hσ0 : 0 ≤ σ
  · have hstay : ∀ s ∈ Set.Icc (0 : ℝ) σ, curveAt v hcomplete y s ∈ f ⁻¹' Set.Icc (c - ε - η) (c + r ^ 2 / 2) := by
      intro s hs
      have hrb := f_rate_bounds_of_integralCurve f hf v hrate
        (hγ := curveAt_integralCurve v hcomplete y) (t := s) hs.1
      have hlo : c - ε - η ≤ f (curveAt v hcomplete y s) := by
        have hle : c - ε - η ≤ f y - s := by
          have hsle : s ≤ σ := hs.2
          have hσeq : σ = f y - c + ε := rfl
          nlinarith [hy.1, hsle, hσeq, hη]
        exact le_trans hle (by simpa [curveAt_zero v hcomplete y] using hrb.1)
      have hhi : f (curveAt v hcomplete y s) ≤ c + r ^ 2 / 2 := by
        exact le_trans (by simpa [curveAt_zero v hcomplete y] using hrb.2) hy.2
      change c - ε - η ≤ f (curveAt v hcomplete y s) ∧ f (curveAt v hcomplete y s) ≤ c + r ^ 2 / 2
      exact ⟨hlo, hhi⟩
    have heq := f_eq_sub_of_integralCurve_on_strip (I := I) f hf v hdfOn
      (hγ := curveAt_integralCurve v hcomplete y) (t := σ) hσ0 hstay
    have hmain : f (curveAt v hcomplete y σ) = f y - σ := by
      simpa [curveAt_zero v hcomplete y] using heq
    dsimp [σ] at hmain ⊢
    linarith
  · have hback : f (curveAt v hcomplete y σ) = f y - σ := by
      let s : ℝ := -σ
      have hs0 : 0 ≤ s := by dsimp [s]; linarith
      have hstay : ∀ t ∈ Set.Icc (0 : ℝ) s,
          curveAt v hcomplete y (-t) ∈ f ⁻¹' Set.Icc (c - ε - η) (c + r ^ 2 / 2) := by
        intro t ht
        have hrb := f_rate_bounds_of_integralCurve_back f hf v hrate
          (hγ := curveAt_integralCurve v hcomplete y) (t := t) ht.1
        have hlo : c - ε - η ≤ f (curveAt v hcomplete y (-t)) := by
          exact le_trans hy.1 (by simpa [curveAt_zero v hcomplete y] using hrb.1)
        have hhi : f (curveAt v hcomplete y (-t)) ≤ c + r ^ 2 / 2 := by
          have htle : t ≤ -σ := ht.2
          have hσeq : σ = f y - c + ε := rfl
          have hσeq' : -σ = c - ε - f y := by rw [hσeq]; ring
          have hle : f y + t ≤ c - ε := by
            have htle' : t ≤ c - ε - f y := by
              rw [← hσeq']
              exact htle
            linarith [htle']
          exact le_trans (le_trans (by simpa [curveAt_zero v hcomplete y] using hrb.2) hle)
            (by nlinarith [hε, sq_nonneg r])
        change c - ε - η ≤ f (curveAt v hcomplete y (-t)) ∧ f (curveAt v hcomplete y (-t)) ≤ c + r ^ 2 / 2
        exact ⟨hlo, hhi⟩
      have heq := f_add_of_integralCurve_back (I := I) f hf v hdfOn
        (hγ := curveAt_integralCurve v hcomplete y) (t := s) hs0 hstay
      have hmain : f (curveAt v hcomplete y (-s)) = f y + s := by
        simpa [curveAt_zero v hcomplete y] using heq
      have hneg : -s = σ := by dsimp [s]; ring
      have hmain' : f (curveAt v hcomplete y σ) = f y - σ := by
        simpa [hneg] using hmain
      have hσeq : σ = f y - c + ε := rfl
      nlinarith [hmain', hσeq]
    have hσeq : σ = f y - c + ε := rfl
    nlinarith [hback, hσeq]

theorem morseCollarFlow_valueOnStrip {n : ℕ} {H : Type} [TopologicalSpace H] {M : Type}
    [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
    (I : ModelWithCorners ℝ (MorseModel n) H) [I.Boundaryless]
    [IsManifold I (⊤ : WithTop ℕ∞) M] (f : M → ℝ) (c ε r η : ℝ)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) f)
    (v : (x : M) → TangentSpace I x)
    (hv : ContMDiff I (I.prod 𝓘(ℝ, MorseModel n)) ∞
      (fun x : M => (⟨x, v x⟩ : TangentBundle I M)))
    (hsupp : IsCompact (tsupport v))
    (hdfOn : ∀ x ∈ f ⁻¹' Set.Icc (c - ε - η) (c + r ^ 2 / 2),
      (NormedSpace.fromTangentSpace (f x)) ((mfderiv I 𝓘(ℝ, ℝ) f x) (v x)) = -1)
    (hrate : ∀ x,
      -1 ≤ (NormedSpace.fromTangentSpace (f x)) ((mfderiv I 𝓘(ℝ, ℝ) f x) (v x)) ∧
      (NormedSpace.fromTangentSpace (f x)) ((mfderiv I 𝓘(ℝ, ℝ) f x) (v x)) ≤ 0)
    {y : M} (hy : f y ∈ Set.Icc (c - ε - η) (c + r ^ 2 / 2))
    {t : ℝ} (ht : f y - (c + r ^ 2 / 2) ≤ t) (ht' : t ≤ f y - (c - ε - η)) :
    f (curveAt v (exists_globalIntegralCurve_of_compactSupport v hv hsupp) y t) = f y - t := by
  let hcomplete : ∀ x : M, ∃ γ : ℝ → M, γ 0 = x ∧ IsMIntegralCurve γ v :=
    exists_globalIntegralCurve_of_compactSupport v hv hsupp
  by_cases ht0 : 0 ≤ t
  · have hstay : ∀ s ∈ Set.Icc (0 : ℝ) t, curveAt v hcomplete y s ∈ f ⁻¹' Set.Icc (c - ε - η) (c + r ^ 2 / 2) := by
      intro s hs
      have hrb := f_rate_bounds_of_integralCurve f hf v hrate
        (hγ := curveAt_integralCurve v hcomplete y) (t := s) hs.1
      have hlo : c - ε - η ≤ f (curveAt v hcomplete y s) := by
        have hle : c - ε - η ≤ f y - s := by
          have hsle : s ≤ t := hs.2
          have htge : f y - t ≤ f y - s := by linarith
          linarith [hy.1, ht, htge]
        exact le_trans hle (by simpa [curveAt_zero v hcomplete y] using hrb.1)
      have hhi : f (curveAt v hcomplete y s) ≤ c + r ^ 2 / 2 := by
        exact le_trans (by simpa [curveAt_zero v hcomplete y] using hrb.2) hy.2
      change c - ε - η ≤ f (curveAt v hcomplete y s) ∧ f (curveAt v hcomplete y s) ≤ c + r ^ 2 / 2
      exact ⟨hlo, hhi⟩
    have heq := f_eq_sub_of_integralCurve_on_strip (I := I) f hf v hdfOn
      (hγ := curveAt_integralCurve v hcomplete y) (t := t) ht0 hstay
    simpa [curveAt_zero v hcomplete y] using heq
  · let s : ℝ := -t
    have hs0 : 0 ≤ s := by dsimp [s]; linarith
    have hstay : ∀ u ∈ Set.Icc (0 : ℝ) s, curveAt v hcomplete y (-u) ∈ f ⁻¹' Set.Icc (c - ε - η) (c + r ^ 2 / 2) := by
      intro u hu
      have hrb := f_rate_bounds_of_integralCurve_back f hf v hrate
        (hγ := curveAt_integralCurve v hcomplete y) (t := u) hu.1
      have hlo : c - ε - η ≤ f (curveAt v hcomplete y (-u)) := by
        exact le_trans hy.1 (by simpa [curveAt_zero v hcomplete y] using hrb.1)
      have hhi : f (curveAt v hcomplete y (-u)) ≤ c + r ^ 2 / 2 := by
        have hule : u ≤ -t := by simpa [s] using hu.2
        have htle : f y + u ≤ f y - t := by
          linarith
        have hmain : f (curveAt v hcomplete y (-u)) ≤ f y + u := by
          simpa [curveAt_zero v hcomplete y] using hrb.2
        have hb : f y - t ≤ c + r ^ 2 / 2 := by linarith [ht']
        linarith
      change c - ε - η ≤ f (curveAt v hcomplete y (-u)) ∧ f (curveAt v hcomplete y (-u)) ≤ c + r ^ 2 / 2
      exact ⟨hlo, hhi⟩
    have heq := f_add_of_integralCurve_back (I := I) f hf v hdfOn
      (hγ := curveAt_integralCurve v hcomplete y) (t := s) hs0 hstay
    have hmain : f (curveAt v hcomplete y (-s)) = f y + s := by
      simpa [curveAt_zero v hcomplete y] using heq
    have hneg : -s = t := by dsimp [s]; ring
    have hmain' : f (curveAt v hcomplete y t) = f y - t := by
      simpa [hneg] using hmain
    exact hmain'

theorem morseCollarLevelMap_mem {m k : ℕ} (hk : k ≤ m + 1) (c ε r η : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} {f : M → ℝ}
    {f₀ : M → ℝ} (data : MorseChart (m + 1) k hk c I f₀)
    (hε : 0 < ε) (hη : 0 ≤ η)
    (x : LevelSetSpace f (c - ε)) (σ : ℝ)
    (hσ : σ ∈ Set.Icc (-η) (r ^ 2 / 2 + ε)) :
    morseCollarLevelMap hk c ε r η data x σ ∈ Set.Icc (-η) (r ^ 2 / 2) := by
  dsimp [morseCollarLevelMap]
  have hT : 0 ≤ morseCollarTopLevel hk c ε r data x :=
    morseCollarTopLevel_nonneg hk c ε r data x
  have hTle : morseCollarTopLevel hk c ε r data x ≤ r ^ 2 / 2 :=
    morseCollarTopLevel_le hk c ε r data x
  have hden : 0 < r ^ 2 / 2 + ε + η := by
    have h1 : 0 ≤ r ^ 2 / 2 := div_nonneg (sq_nonneg r) (by norm_num)
    have h2 : 0 < ε + η := by nlinarith [hε, hη]
    nlinarith [h1, h2]
  have hσlo : -η ≤ σ := hσ.1
  have hσhi : σ ≤ r ^ 2 / 2 + ε := hσ.2
  constructor
  · have hnum : 0 ≤ (morseCollarTopLevel hk c ε r data x + η) * (σ + η) := by
      have h1 : 0 ≤ morseCollarTopLevel hk c ε r data x + η := by nlinarith [hT, hη]
      have h2 : 0 ≤ σ + η := by nlinarith [hσlo, hη]
      exact mul_nonneg h1 h2
    have hdiv : 0 ≤ (morseCollarTopLevel hk c ε r data x + η) * (σ + η) / (r ^ 2 / 2 + ε + η) :=
      div_nonneg hnum (le_of_lt hden)
    nlinarith
  · have hnumle : (morseCollarTopLevel hk c ε r data x + η) * (σ + η) ≤
      (r ^ 2 / 2 + η) * (r ^ 2 / 2 + ε + η) := by
      have h1 : morseCollarTopLevel hk c ε r data x + η ≤ r ^ 2 / 2 + η := by
        nlinarith [hTle, hη]
      have h2 : 0 ≤ σ + η := by nlinarith [hσlo, hη]
      have h3 : σ + η ≤ r ^ 2 / 2 + ε + η := by nlinarith [hσhi]
      have h4 : 0 ≤ r ^ 2 / 2 + ε + η := le_of_lt hden
      nlinarith [h1, h2, h3, h4, hTle, hT, hη]
    have hmain : -η + (morseCollarTopLevel hk c ε r data x + η) * (σ + η) / (r ^ 2 / 2 + ε + η) ≤
        r ^ 2 / 2 := by
      have hsub : (morseCollarTopLevel hk c ε r data x + η) * (σ + η) / (r ^ 2 / 2 + ε + η) ≤
          r ^ 2 / 2 + η := by
        exact (div_le_iff₀ hden).mpr hnumle
      linarith
    exact hmain

theorem morseCollarLevelMap_le_top {m k : ℕ} (hk : k ≤ m + 1) (c ε r η : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} {f : M → ℝ}
    {f₀ : M → ℝ} (data : MorseChart (m + 1) k hk c I f₀)
    (hε : 0 < ε) (hη : 0 ≤ η)
    (x : LevelSetSpace f (c - ε)) (σ : ℝ)
    (hσ : σ ∈ Set.Icc (-η) (r ^ 2 / 2 + ε)) :
    morseCollarLevelMap hk c ε r η data x σ ≤ morseCollarTopLevel hk c ε r data x := by
  dsimp [morseCollarLevelMap]
  have hden : 0 < r ^ 2 / 2 + ε + η := by
    have h1 : 0 ≤ r ^ 2 / 2 := div_nonneg (sq_nonneg r) (by norm_num)
    nlinarith [h1, hε, hη]
  have hσ' : σ + η ≤ r ^ 2 / 2 + ε + η := by nlinarith [hσ.2]
  have hT : 0 ≤ morseCollarTopLevel hk c ε r data x := morseCollarTopLevel_nonneg hk c ε r data x
  have hnumle : (morseCollarTopLevel hk c ε r data x + η) * (σ + η) ≤
      (morseCollarTopLevel hk c ε r data x + η) * (r ^ 2 / 2 + ε + η) := by
    exact mul_le_mul_of_nonneg_left hσ' (by nlinarith [hT, hη])
  have hdivle : (morseCollarTopLevel hk c ε r data x + η) * (σ + η) / (r ^ 2 / 2 + ε + η) ≤
      morseCollarTopLevel hk c ε r data x + η := by
    exact (div_le_iff₀ hden).mpr (by nlinarith [hnumle])
  nlinarith [hdivle]

theorem morseCollarLevelMap_nonpos_of_top_zero {m k : ℕ} (hk : k ≤ m + 1) (c ε r η : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} {f : M → ℝ}
    {f₀ : M → ℝ} (data : MorseChart (m + 1) k hk c I f₀)
    (hε : 0 < ε) (hη : 0 ≤ η)
    (x : LevelSetSpace f (c - ε)) (σ : ℝ)
    (hσ : σ ∈ Set.Icc (-η) (r ^ 2 / 2 + ε))
    (hTop : morseCollarTopLevel hk c ε r data x = 0) :
    morseCollarLevelMap hk c ε r η data x σ ≤ 0 := by
  dsimp [morseCollarLevelMap]
  rw [hTop]
  have hden : 0 < r ^ 2 / 2 + ε + η := by
    have h1 : 0 ≤ r ^ 2 / 2 := div_nonneg (sq_nonneg r) (by norm_num)
    nlinarith [h1, hε, hη]
  have hσ' : σ + η ≤ r ^ 2 / 2 + ε + η := by nlinarith [hσ.2]
  have hnumle : (0 + η) * (σ + η) ≤ (0 + η) * (r ^ 2 / 2 + ε + η) := by
    exact mul_le_mul_of_nonneg_left hσ' (by simpa using hη)
  have hdivle : (0 + η) * (σ + η) / (r ^ 2 / 2 + ε + η) ≤ 0 + η := by
    exact (div_le_iff₀ hden).mpr (by nlinarith [hnumle])
  linarith

noncomputable def morseCollarMap {m k : ℕ} (hk : k ≤ m + 1) (c ε r η : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} [I.Boundaryless]
    [IsManifold I (⊤ : WithTop ℕ∞) M] {f : M → ℝ}
    {f₀ : M → ℝ} (data : MorseChart (m + 1) k hk c I f₀)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) f)
    (hε : 0 < ε) (hη : 0 ≤ η)
    (v : (x : M) → TangentSpace I x)
    (hv : ContMDiff I (I.prod 𝓘(ℝ, MorseModel (m + 1))) ∞
      (fun x : M => (⟨x, v x⟩ : TangentBundle I M)))
    (hsupp : IsCompact (tsupport v))
    (hdfOn : ∀ x ∈ f ⁻¹' Set.Icc (c - ε - η) (c + r ^ 2 / 2),
      (NormedSpace.fromTangentSpace (f x)) ((mfderiv I 𝓘(ℝ, ℝ) f x) (v x)) = -1)
    (hrate : ∀ x,
      -1 ≤ (NormedSpace.fromTangentSpace (f x)) ((mfderiv I 𝓘(ℝ, ℝ) f x) (v x)) ∧
      (NormedSpace.fromTangentSpace (f x)) ((mfderiv I 𝓘(ℝ, ℝ) f x) (v x)) ≤ 0)
    (y : SublevelSpace f (c + r ^ 2 / 2)) : M :=
  by
  classical
  exact if hlow : f y.1 ≤ c - ε - η then y.1 else
    let σ : ℝ := f y.1 - c + ε
    let x : LevelSetSpace f (c - ε) := ⟨curveAt v
      (exists_globalIntegralCurve_of_compactSupport v hv hsupp) y.1 σ, by
      simpa [σ] using (morseCollarFlow_levelValue (I := I) f c ε r η hε hη hf v hv hsupp
        hdfOn hrate (by
          constructor
          · exact le_of_not_ge hlow
          · exact y.2) )⟩
    curveAt v (exists_globalIntegralCurve_of_compactSupport v hv hsupp) x.1
      (-morseCollarLevelMap hk c ε r η data x σ)

theorem morseCollarMap_of_low {m k : ℕ} (hk : k ≤ m + 1) (c ε r η : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} [I.Boundaryless]
    [IsManifold I (⊤ : WithTop ℕ∞) M] {f : M → ℝ}
    {f₀ : M → ℝ} (data : MorseChart (m + 1) k hk c I f₀)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) f)
    (hε : 0 < ε) (hη : 0 ≤ η)
    (v : (x : M) → TangentSpace I x)
    (hv : ContMDiff I (I.prod 𝓘(ℝ, MorseModel (m + 1))) ∞
      (fun x : M => (⟨x, v x⟩ : TangentBundle I M)))
    (hsupp : IsCompact (tsupport v))
    (hdfOn : ∀ x ∈ f ⁻¹' Set.Icc (c - ε - η) (c + r ^ 2 / 2),
      (NormedSpace.fromTangentSpace (f x)) ((mfderiv I 𝓘(ℝ, ℝ) f x) (v x)) = -1)
    (hrate : ∀ x,
      -1 ≤ (NormedSpace.fromTangentSpace (f x)) ((mfderiv I 𝓘(ℝ, ℝ) f x) (v x)) ∧
      (NormedSpace.fromTangentSpace (f x)) ((mfderiv I 𝓘(ℝ, ℝ) f x) (v x)) ≤ 0)
    (y : SublevelSpace f (c + r ^ 2 / 2))
    (hy : f y.1 ≤ c - ε - η) :
    morseCollarMap hk c ε r η data hf hε hη v hv hsupp hdfOn hrate y = y.1 := by
  dsimp [morseCollarMap]
  rw [dif_pos hy]

theorem morseCollarMap_of_strip {m k : ℕ} (hk : k ≤ m + 1) (c ε r η : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} [I.Boundaryless]
    [IsManifold I (⊤ : WithTop ℕ∞) M] {f : M → ℝ}
    {f₀ : M → ℝ} (data : MorseChart (m + 1) k hk c I f₀)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) f)
    (hε : 0 < ε) (hη : 0 ≤ η)
    (v : (x : M) → TangentSpace I x)
    (hv : ContMDiff I (I.prod 𝓘(ℝ, MorseModel (m + 1))) ∞
      (fun x : M => (⟨x, v x⟩ : TangentBundle I M)))
    (hsupp : IsCompact (tsupport v))
    (hdfOn : ∀ x ∈ f ⁻¹' Set.Icc (c - ε - η) (c + r ^ 2 / 2),
      (NormedSpace.fromTangentSpace (f x)) ((mfderiv I 𝓘(ℝ, ℝ) f x) (v x)) = -1)
    (hrate : ∀ x,
      -1 ≤ (NormedSpace.fromTangentSpace (f x)) ((mfderiv I 𝓘(ℝ, ℝ) f x) (v x)) ∧
      (NormedSpace.fromTangentSpace (f x)) ((mfderiv I 𝓘(ℝ, ℝ) f x) (v x)) ≤ 0)
    (y : SublevelSpace f (c + r ^ 2 / 2))
    (hy : c - ε - η ≤ f y.1) :
    morseCollarMap hk c ε r η data hf hε hη v hv hsupp hdfOn hrate y =
      curveAt v (exists_globalIntegralCurve_of_compactSupport v hv hsupp) y.1
        (f y.1 - c + ε - morseCollarLevelMap hk c ε r η data
          (⟨curveAt v (exists_globalIntegralCurve_of_compactSupport v hv hsupp) y.1 (f y.1 - c + ε), by
            exact (morseCollarFlow_levelValue (I := I) f c ε r η hε hη hf v hv hsupp hdfOn hrate (by
              constructor
              · exact hy
              · exact y.2))⟩) (f y.1 - c + ε)) := by
  dsimp [morseCollarMap]
  by_cases hstrict : c - ε - η < f y.1
  · rw [dif_neg (not_le_of_gt hstrict)]
    have hv1 : ContMDiff I (I.prod 𝓘(ℝ, MorseModel (m + 1))) (1 : WithTop ℕ∞)
        (fun x : M => (⟨x, v x⟩ : TangentBundle I M)) :=
      hv.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ ∞)
    let hcomplete : ∀ x : M, ∃ γ : ℝ → M, γ 0 = x ∧ IsMIntegralCurve γ v :=
      exists_globalIntegralCurve_of_compactSupport v hv hsupp
    let σ : ℝ := f y.1 - c + ε
    let L : ℝ := morseCollarLevelMap hk c ε r η data
      (⟨curveAt v hcomplete y.1 σ, by
        exact (morseCollarFlow_levelValue (I := I) f c ε r η hε hη hf v hv hsupp hdfOn hrate (by
          constructor
          · exact hy
          · exact y.2))⟩) σ
    have hh := curveAt_add v hv1 hcomplete y.1 σ (-L)
    have hz : σ + (-L) = σ - L := by ring
    rw [hz] at hh
    simpa [σ, L] using hh.symm
  · have hle : f y.1 ≤ c - ε - η := le_of_not_gt hstrict
    rw [dif_pos hle]
    have htime : f y.1 - c + ε - morseCollarLevelMap hk c ε r η data
        (⟨curveAt v (exists_globalIntegralCurve_of_compactSupport v hv hsupp) y.1 (f y.1 - c + ε), by
          exact (morseCollarFlow_levelValue (I := I) f c ε r η hε hη hf v hv hsupp hdfOn hrate (by
            constructor
            · exact hy
            · exact y.2))⟩) (f y.1 - c + ε) = 0 := by
      dsimp [morseCollarLevelMap]
      have hσ : f y.1 - c + ε = -η := by linarith
      have hσ0 : f y.1 - c + ε + η = 0 := by linarith
      simp [hσ]
    rw [htime]
    exact (curveAt_zero v (exists_globalIntegralCurve_of_compactSupport v hv hsupp) y.1).symm

theorem morseCollarMap_value {m k : ℕ} (hk : k ≤ m + 1) (c ε r η : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} [I.Boundaryless]
    [IsManifold I (⊤ : WithTop ℕ∞) M] {f : M → ℝ}
    {f₀ : M → ℝ} (data : MorseChart (m + 1) k hk c I f₀)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) f)
    (hε : 0 < ε) (hη : 0 < η)
    (v : (x : M) → TangentSpace I x)
    (hv : ContMDiff I (I.prod 𝓘(ℝ, MorseModel (m + 1))) ∞
      (fun x : M => (⟨x, v x⟩ : TangentBundle I M)))
    (hsupp : IsCompact (tsupport v))
    (hdfOn : ∀ x ∈ f ⁻¹' Set.Icc (c - ε - η) (c + r ^ 2 / 2),
      (NormedSpace.fromTangentSpace (f x)) ((mfderiv I 𝓘(ℝ, ℝ) f x) (v x)) = -1)
    (hrate : ∀ x,
      -1 ≤ (NormedSpace.fromTangentSpace (f x)) ((mfderiv I 𝓘(ℝ, ℝ) f x) (v x)) ∧
      (NormedSpace.fromTangentSpace (f x)) ((mfderiv I 𝓘(ℝ, ℝ) f x) (v x)) ≤ 0)
    (y : SublevelSpace f (c + r ^ 2 / 2))
    (hy : c - ε - η ≤ f y.1) :
    f (morseCollarMap hk c ε r η data hf hε (le_of_lt hη) v hv hsupp hdfOn hrate y) =
      c - ε + morseCollarLevelMap hk c ε r η data
        (⟨curveAt v (exists_globalIntegralCurve_of_compactSupport v hv hsupp) y.1 (f y.1 - c + ε), by
          exact (morseCollarFlow_levelValue (I := I) f c ε r η hε (le_of_lt hη) hf v hv hsupp hdfOn hrate (by
            constructor
            · exact hy
            · exact y.2))⟩) (f y.1 - c + ε) := by
  let hcomplete : ∀ x : M, ∃ γ : ℝ → M, γ 0 = x ∧ IsMIntegralCurve γ v :=
    exists_globalIntegralCurve_of_compactSupport v hv hsupp
  let σ : ℝ := f y.1 - c + ε
  let L : ℝ := morseCollarLevelMap hk c ε r η data
    (⟨curveAt v hcomplete y.1 σ, by
      exact (morseCollarFlow_levelValue (I := I) f c ε r η hε (le_of_lt hη) hf v hv hsupp hdfOn hrate (by
        constructor
        · exact hy
        · exact y.2))⟩) σ
  have hmap : morseCollarMap hk c ε r η data hf hε (le_of_lt hη) v hv hsupp hdfOn hrate y =
      curveAt v hcomplete y.1 (σ - L) := by
    simpa [σ, L] using (morseCollarMap_of_strip hk c ε r η data hf hε (le_of_lt hη) v hv hsupp
      hdfOn hrate y hy)
  have hσ : σ ∈ Set.Icc (-η) (r ^ 2 / 2 + ε) := by
    dsimp [σ]
    change f y.1 - c + ε ∈ Set.Icc (-η) (r ^ 2 / 2 + ε)
    constructor
    · linarith [hy]
    · change f y.1 - c + ε ≤ r ^ 2 / 2 + ε
      have hy2 : f y.1 ≤ c + r ^ 2 / 2 := y.2
      linarith
  have hLmem : L ∈ Set.Icc (-η) (r ^ 2 / 2) := by
    dsimp [L]
    exact morseCollarLevelMap_mem hk c ε r η data hε (le_of_lt hη) _ σ hσ
  have ht : f y.1 - (c + r ^ 2 / 2) ≤ σ - L := by
    have hLle : L ≤ r ^ 2 / 2 := hLmem.2
    dsimp [σ]
    nlinarith [hε, hLle]
  have ht' : σ - L ≤ f y.1 - (c - ε - η) := by
    have hLge : -η ≤ L := hLmem.1
    dsimp [σ]
    nlinarith [hLge]
  have hval : f (curveAt v hcomplete y.1 (σ - L)) = f y.1 - (σ - L) :=
    morseCollarFlow_valueOnStrip (I := I) f c ε r η hf v hv hsupp hdfOn hrate
      (by
        constructor
        · exact hy
        · exact y.2) ht ht'
  rw [hmap]
  rw [hval]
  dsimp [σ, L]
  linarith

theorem morseCollarMap_mem_lower_of_top_zero {m k : ℕ} (hk : k ≤ m + 1) (c ε r η : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} [I.Boundaryless]
    [IsManifold I (⊤ : WithTop ℕ∞) M] {f : M → ℝ}
    {f₀ : M → ℝ} (data : MorseChart (m + 1) k hk c I f₀)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) f)
    (hε : 0 < ε) (hη : 0 < η)
    (v : (x : M) → TangentSpace I x)
    (hv : ContMDiff I (I.prod 𝓘(ℝ, MorseModel (m + 1))) ∞
      (fun x : M => (⟨x, v x⟩ : TangentBundle I M)))
    (hsupp : IsCompact (tsupport v))
    (hdfOn : ∀ x ∈ f ⁻¹' Set.Icc (c - ε - η) (c + r ^ 2 / 2),
      (NormedSpace.fromTangentSpace (f x)) ((mfderiv I 𝓘(ℝ, ℝ) f x) (v x)) = -1)
    (hrate : ∀ x,
      -1 ≤ (NormedSpace.fromTangentSpace (f x)) ((mfderiv I 𝓘(ℝ, ℝ) f x) (v x)) ∧
      (NormedSpace.fromTangentSpace (f x)) ((mfderiv I 𝓘(ℝ, ℝ) f x) (v x)) ≤ 0)
    (y : SublevelSpace f (c + r ^ 2 / 2))
    (hy : c - ε - η ≤ f y.1)
    (hTop : morseCollarTopLevel hk c ε r data
      (⟨curveAt v (exists_globalIntegralCurve_of_compactSupport v hv hsupp) y.1 (f y.1 - c + ε), by
        exact (morseCollarFlow_levelValue (I := I) f c ε r η hε (le_of_lt hη) hf v hv hsupp hdfOn hrate (by
          constructor
          · exact hy
          · exact y.2))⟩) = 0) :
    f (morseCollarMap hk c ε r η data hf hε (le_of_lt hη) v hv hsupp hdfOn hrate y) ≤ c - ε := by
  have hval := morseCollarMap_value hk c ε r η data hf hε hη v hv hsupp hdfOn hrate y hy
  have hσ : f y.1 - c + ε ∈ Set.Icc (-η) (r ^ 2 / 2 + ε) := by
    change f y.1 - c + ε ∈ Set.Icc (-η) (r ^ 2 / 2 + ε)
    constructor
    · linarith [hy]
    · change f y.1 - c + ε ≤ r ^ 2 / 2 + ε
      have hy2 : f y.1 ≤ c + r ^ 2 / 2 := by
        change f y.1 ≤ c + r ^ 2 / 2
        exact y.2
      nlinarith [hy2]
  have hL := morseCollarLevelMap_nonpos_of_top_zero hk c ε r η data hε (le_of_lt hη)
    (⟨curveAt v (exists_globalIntegralCurve_of_compactSupport v hv hsupp) y.1 (f y.1 - c + ε), by
      exact (morseCollarFlow_levelValue (I := I) f c ε r η hε (le_of_lt hη) hf v hv hsupp hdfOn hrate (by
        constructor
        · exact hy
        · exact y.2))⟩) (f y.1 - c + ε) hσ hTop
  rw [hval]
  nlinarith

theorem morseCollarMap_mem_handle_of_chart {m k : ℕ} (hk : k ≤ m + 1) (c ε r η : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} [I.Boundaryless]
    [IsManifold I (⊤ : WithTop ℕ∞) M] {f : M → ℝ}
    {f₀ : M → ℝ} (data : MorseChart (m + 1) k hk c I f₀)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) f)
    (hε : 0 < ε) (hη : 0 < η)
    (v : (x : M) → TangentSpace I x)
    (hv : ContMDiff I (I.prod 𝓘(ℝ, MorseModel (m + 1))) ∞
      (fun x : M => (⟨x, v x⟩ : TangentBundle I M)))
    (hsupp : IsCompact (tsupport v))
    (hdfOn : ∀ x ∈ f ⁻¹' Set.Icc (c - ε - η) (c + r ^ 2 / 2),
      (NormedSpace.fromTangentSpace (f x)) ((mfderiv I 𝓘(ℝ, ℝ) f x) (v x)) = -1)
    (hrate : ∀ x,
      -1 ≤ (NormedSpace.fromTangentSpace (f x)) ((mfderiv I 𝓘(ℝ, ℝ) f x) (v x)) ∧
      (NormedSpace.fromTangentSpace (f x)) ((mfderiv I 𝓘(ℝ, ℝ) f x) (v x)) ≤ 0)
    (hf₀ : ∀ y : MorseModel (m + 1), morseNorm (m + 1) y ≤ data.R → f (data.χ y) = f₀ (data.χ y))
    (hflowChart : ∀ y : MorseModel (m + 1), y ∈ data.χ.source →
      ∀ t : ℝ, curveAt v (exists_globalIntegralCurve_of_compactSupport v hv hsupp) (data.χ y) t =
        data.χ (modelFlow hk t y))
    (y : SublevelSpace f (c + r ^ 2 / 2))
    (hy : c - ε - η ≤ f y.1)
    (hxball : curveAt v (exists_globalIntegralCurve_of_compactSupport v hv hsupp) y.1
        (f y.1 - c + ε) ∈ data.χ '' {y : MorseModel (m + 1) | morseNorm (m + 1) y < data.R})
    (hpos : 0 < ‖posPart hk (data.χ.symm (curveAt v
        (exists_globalIntegralCurve_of_compactSupport v hv hsupp) y.1 (f y.1 - c + ε)))‖)
    (hr2 : ‖posPart hk (data.χ.symm (curveAt v
        (exists_globalIntegralCurve_of_compactSupport v hv hsupp) y.1 (f y.1 - c + ε)))‖ ^ 2 ≤ r ^ 2)
    (hL0 : 0 ≤ morseCollarLevelMap hk c ε r η data
      (⟨curveAt v (exists_globalIntegralCurve_of_compactSupport v hv hsupp) y.1 (f y.1 - c + ε), by
        exact (morseCollarFlow_levelValue (I := I) f c ε r η hε (le_of_lt hη) hf v hv hsupp hdfOn hrate (by
          constructor
          · exact hy
          · exact y.2))⟩) (f y.1 - c + ε)) :
    morseCollarMap hk c ε r η data hf hε (le_of_lt hη) v hv hsupp hdfOn hrate y ∈
      data.χ '' (modelHandle hk ε r : Set (MorseModel (m + 1))) := by
  let hcomplete : ∀ x : M, ∃ γ : ℝ → M, γ 0 = x ∧ IsMIntegralCurve γ v :=
    exists_globalIntegralCurve_of_compactSupport v hv hsupp
  let σ : ℝ := f y.1 - c + ε
  let x : LevelSetSpace f (c - ε) := ⟨curveAt v hcomplete y.1 σ, by
    simpa [σ] using (morseCollarFlow_levelValue (I := I) f c ε r η hε (le_of_lt hη) hf v hv hsupp
      hdfOn hrate (by
        constructor
        · exact hy
        · exact y.2))⟩
  let L : ℝ := morseCollarLevelMap hk c ε r η data x σ
  have hv1 : ContMDiff I (I.prod 𝓘(ℝ, MorseModel (m + 1))) (1 : WithTop ℕ∞)
      (fun x : M => (⟨x, v x⟩ : TangentBundle I M)) :=
    hv.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ ∞)
  have hmap : morseCollarMap hk c ε r η data hf hε (le_of_lt hη) v hv hsupp hdfOn hrate y =
      curveAt v hcomplete x.1 (-L) := by
    have hmap' : morseCollarMap hk c ε r η data hf hε (le_of_lt hη) v hv hsupp hdfOn hrate y =
        curveAt v hcomplete y.1 (σ - L) := by
      simpa [σ, L] using (morseCollarMap_of_strip hk c ε r η data hf hε (le_of_lt hη) v hv hsupp
        hdfOn hrate y hy)
    rw [hmap']
    have hh := curveAt_add v hv1 hcomplete y.1 σ (-L)
    have hz : σ + (-L) = σ - L := by ring
    rw [hz] at hh
    simpa [x] using hh
  have hxball' : x.1 ∈ data.χ '' {y : MorseModel (m + 1) | morseNorm (m + 1) y < data.R} := by
    simpa [x, σ] using hxball
  let z : MorseModel (m + 1) := data.χ.symm x.1
  have hnormz : morseNorm (m + 1) z ≤ data.R := by
    rcases hxball' with ⟨w, hw, hwx⟩
    have hsrc0 : w ∈ data.χ.source := data.hχsrc w (le_of_lt hw)
    dsimp [z]
    have hsymm : data.χ.symm x.1 = w := by
      rw [← hwx]
      exact data.χ.left_inv hsrc0
    rw [hsymm]
    exact le_of_lt hw
  have hχz : data.χ z = x.1 := by
    dsimp [z]
    exact data.χ.right_inv (by
      rcases hxball' with ⟨w, hw, hwx⟩
      have hsrc0 : w ∈ data.χ.source := data.hχsrc w (le_of_lt hw)
      rw [← hwx]
      exact data.χ.map_source hsrc0)
  have hzlevel : morseNormalForm hk c z = c - ε := by
    have hfx : f x.1 = c - ε := x.2
    have hfz : f x.1 = morseNormalForm hk c z := by
      rw [← hχz]
      rw [hf₀ z hnormz]
      rw [data.hnorm z hnormz]
    rw [← hfz]
    exact hfx
  have hsrcx : z ∈ data.χ.source := data.hχsrc z hnormz
  have hflow := hflowChart z hsrcx (-L)
  have himg : curveAt v hcomplete x.1 (-L) = data.χ (modelFlow hk (-L) z) := by
    rw [← hχz]
    exact hflow
  rw [hmap]
  rw [himg]
  refine ⟨modelFlow hk (-L) z, ?_, rfl⟩
  have hL0' : 0 ≤ L := by
    simpa [L, x, σ] using hL0
  have hpos' : 0 < ‖posPart hk z‖ := by
    simpa [z, x, σ] using hpos
  have hLle : L ≤ (r ^ 2 - ‖posPart hk z‖ ^ 2) / 2 := by
    have hσ : σ ∈ Set.Icc (-η) (r ^ 2 / 2 + ε) := by
      dsimp [σ]
      change f y.1 - c + ε ∈ Set.Icc (-η) (r ^ 2 / 2 + ε)
      constructor
      · linarith [hy]
      · have hy2 : f y.1 ≤ c + r ^ 2 / 2 := by
          change f y.1 ≤ c + r ^ 2 / 2
          exact y.2
        nlinarith
    have hLtop := morseCollarLevelMap_le_top hk c ε r η data hε (le_of_lt hη) x σ hσ
    have hTop : morseCollarTopLevel hk c ε r data x = (r ^ 2 - ‖posPart hk z‖ ^ 2) / 2 := by
      have hchart : x ∈ morseCollarChartSet hk c ε r data := by
        dsimp [morseCollarChartSet]
        simpa [x, σ] using hxball
      have htop := morseCollarTopLevel_eq_on_chart hk c ε r data x hchart
      have hnonneg : 0 ≤ (r ^ 2 - ‖posPart hk z‖ ^ 2) / 2 := by
        have hr2' : ‖posPart hk z‖ ^ 2 ≤ r ^ 2 := by
          simpa [z, x, σ] using hr2
        nlinarith
      rw [htop]
      have hmax : max 0 ((r ^ 2 - ‖posPart hk z‖ ^ 2) / 2) = (r ^ 2 - ‖posPart hk z‖ ^ 2) / 2 :=
        max_eq_right hnonneg
      rw [hmax]
    rw [hTop] at hLtop
    exact hLtop
  exact modelFlow_mem_handle_of_up_le hk c ε r hzlevel hL0' hLle hpos'

theorem morseCollarMap_mem_sharpUnion {m k : ℕ} (hk : k ≤ m + 1) (c ε r η : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} [I.Boundaryless]
    [IsManifold I (⊤ : WithTop ℕ∞) M] {f : M → ℝ}
    {f₀ : M → ℝ} (data : MorseChart (m + 1) k hk c I f₀)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) f)
    (hε : 0 < ε) (hη : 0 < η) (hr : 0 < r)
    (v : (x : M) → TangentSpace I x)
    (hv : ContMDiff I (I.prod 𝓘(ℝ, MorseModel (m + 1))) ∞
      (fun x : M => (⟨x, v x⟩ : TangentBundle I M)))
    (hsupp : IsCompact (tsupport v))
    (hdfOn : ∀ x ∈ f ⁻¹' Set.Icc (c - ε - η) (c + r ^ 2 / 2),
      (NormedSpace.fromTangentSpace (f x)) ((mfderiv I 𝓘(ℝ, ℝ) f x) (v x)) = -1)
    (hrate : ∀ x,
      -1 ≤ (NormedSpace.fromTangentSpace (f x)) ((mfderiv I 𝓘(ℝ, ℝ) f x) (v x)) ∧
      (NormedSpace.fromTangentSpace (f x)) ((mfderiv I 𝓘(ℝ, ℝ) f x) (v x)) ≤ 0)
    (hf₀ : ∀ y : MorseModel (m + 1), morseNorm (m + 1) y ≤ data.R → f (data.χ y) = f₀ (data.χ y))
    (hflowChart : ∀ y : MorseModel (m + 1), y ∈ data.χ.source →
      ∀ t : ℝ, curveAt v (exists_globalIntegralCurve_of_compactSupport v hv hsupp) (data.χ y) t =
        data.χ (modelFlow hk t y))
    (y : SublevelSpace f (c + r ^ 2 / 2)) :
    morseCollarMap hk c ε r η data hf hε (le_of_lt hη) v hv hsupp hdfOn hrate y ∈
      sublevel f (c - ε) ∪ Set.range (handleEmbedding hk c ε r data) := by
  by_cases hlow : f y.1 ≤ c - ε - η
  · have hm := morseCollarMap_of_low hk c ε r η data hf hε (le_of_lt hη) v hv hsupp hdfOn hrate y hlow
    rw [hm]
    exact Or.inl (by change f y.1 ≤ c - ε; nlinarith [hlow, hε, hη])
  · have hnotlow : c - ε - η < f y.1 := lt_of_not_ge hlow
    have hy : c - ε - η ≤ f y.1 := le_of_lt hnotlow
    let hcomplete : ∀ x : M, ∃ γ : ℝ → M, γ 0 = x ∧ IsMIntegralCurve γ v :=
      exists_globalIntegralCurve_of_compactSupport v hv hsupp
    let σ : ℝ := f y.1 - c + ε
    let x : LevelSetSpace f (c - ε) := ⟨curveAt v hcomplete y.1 σ, by
      simpa [σ] using (morseCollarFlow_levelValue (I := I) f c ε r η hε (le_of_lt hη) hf v hv hsupp
        hdfOn hrate (by
          constructor
          · exact hy
          · exact y.2))⟩
    let L : ℝ := morseCollarLevelMap hk c ε r η data x σ
    by_cases hTop0 : morseCollarTopLevel hk c ε r data x = 0
    · have hmem := morseCollarMap_mem_lower_of_top_zero hk c ε r η data hf hε hη v hv hsupp hdfOn hrate
        y hy hTop0
      exact Or.inl hmem
    · have hToppos : 0 < morseCollarTopLevel hk c ε r data x := by
        have hT0 := morseCollarTopLevel_nonneg hk c ε r data x
        exact lt_of_le_of_ne hT0 (Ne.symm hTop0)
      have hxball : x.1 ∈ data.χ '' {y : MorseModel (m + 1) | morseNorm (m + 1) y < data.R} := by
        by_contra hx
        have hz := morseCollarTopLevel_eq_zero hk c ε r data x hx
        exact (ne_of_gt hToppos) hz
      have hchart : x ∈ morseCollarChartSet hk c ε r data := by
        dsimp [morseCollarChartSet]
        exact hxball
      have htop := morseCollarTopLevel_eq_on_chart hk c ε r data x hchart
      let z : MorseModel (m + 1) := data.χ.symm x.1
      have hr2 : ‖posPart hk z‖ ^ 2 ≤ r ^ 2 := by
        have htop' : 0 < max 0 ((r ^ 2 - ‖posPart hk z‖ ^ 2) / 2) := by
          rw [← htop]
          exact hToppos
        have hA : 0 < (r ^ 2 - ‖posPart hk z‖ ^ 2) / 2 := by
          by_contra hA
          have hmax : max 0 ((r ^ 2 - ‖posPart hk z‖ ^ 2) / 2) = 0 := by
            exact max_eq_left (le_of_not_gt hA)
          nlinarith [htop', hmax]
        nlinarith
      by_cases hpos : 0 < ‖posPart hk z‖
      · by_cases hL0 : 0 ≤ L
        · have hmem := morseCollarMap_mem_handle_of_chart hk c ε r η data hf hε hη v hv hsupp hdfOn hrate
            hf₀ hflowChart y hy hxball hpos hr2 (by simpa [L, x, σ] using hL0)
          have hrange : Set.range (handleEmbedding hk c ε r data) =
              data.χ '' (modelHandle hk ε r : Set (MorseModel (m + 1))) := by
            change Set.range (data.χ ∘ modelHandleMap hk ε r) =
              data.χ '' (modelHandle hk ε r : Set (MorseModel (m + 1)))
            rw [Set.range_comp]
            rw [modelHandleMap_range hk ε r hε hr]
          rw [hrange]
          exact Or.inr hmem
        · have hval := morseCollarMap_value hk c ε r η data hf hε hη v hv hsupp hdfOn hrate y hy
          have hLneg : L < 0 := lt_of_not_ge hL0
          have hlt : f (morseCollarMap hk c ε r η data hf hε (le_of_lt hη) v hv hsupp hdfOn hrate y) < c - ε := by
            rw [hval]
            nlinarith
          exact Or.inl (le_of_lt hlt)
      · have hzpos0 : ‖posPart hk z‖ = 0 := le_antisymm (le_of_not_gt hpos) (norm_nonneg _)
        have hnormz : morseNorm (m + 1) z ≤ data.R := by
          rcases hxball with ⟨w, hw, hwx⟩
          have hsrc0 : w ∈ data.χ.source := data.hχsrc w (le_of_lt hw)
          dsimp [z]
          have hsymm : data.χ.symm x.1 = w := by
            rw [← hwx]
            exact data.χ.left_inv hsrc0
          rw [hsymm]
          exact le_of_lt hw
        have hχz : data.χ z = x.1 := by
          dsimp [z]
          exact data.χ.right_inv (by
            rcases hxball with ⟨w, hw, hwx⟩
            have hsrc0 : w ∈ data.χ.source := data.hχsrc w (le_of_lt hw)
            rw [← hwx]
            exact data.χ.map_source hsrc0)
        have hzlevel : morseNormalForm hk c z = c - ε := by
          have hfx : f x.1 = c - ε := x.2
          have hfz : f x.1 = morseNormalForm hk c z := by
            rw [← hχz]
            rw [hf₀ z hnormz]
            rw [data.hnorm z hnormz]
          rw [← hfz]
          exact hfx
        have hzhandle : z ∈ modelHandle hk ε r := by
          dsimp [modelHandle]
          constructor
          · have hzpos0' : ‖posPart hk z‖ ^ 2 = 0 := by nlinarith [hzpos0]
            nlinarith [hzpos0', sq_nonneg r]
          · have hzsplit := morseNormalForm_split hk c z
            have hnegeq : ‖negPart hk z‖ ^ 2 = ‖posPart hk z‖ ^ 2 + 2 * ε := by
              nlinarith [hzsplit, hzlevel]
            nlinarith [hzpos0, hnegeq]
        have hxhandle : x.1 ∈ data.χ '' (modelHandle hk ε r : Set (MorseModel (m + 1))) := by
          refine ⟨z, hzhandle, ?_⟩
          exact hχz
        have hflowstuck : modelFlow hk (-L) z = z := by
          dsimp [modelFlow]
          have hzpos0' : posPart hk z = 0 := norm_eq_zero.mp hzpos0
          rw [hzpos0']
          simp only [norm_zero, smul_zero]
          rw [← hzpos0']
          exact recombine_decompose hk z
        have hsrcx : z ∈ data.χ.source := data.hχsrc z hnormz
        have hflow := hflowChart z hsrcx (-L)
        have himg : curveAt v hcomplete x.1 (-L) = data.χ (modelFlow hk (-L) z) := by
          rw [← hχz]
          exact hflow
        have hmap : morseCollarMap hk c ε r η data hf hε (le_of_lt hη) v hv hsupp hdfOn hrate y =
            curveAt v hcomplete x.1 (-L) := by
          have hv1 : ContMDiff I (I.prod 𝓘(ℝ, MorseModel (m + 1))) (1 : WithTop ℕ∞)
              (fun x : M => (⟨x, v x⟩ : TangentBundle I M)) :=
            hv.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ ∞)
          have hmap' : morseCollarMap hk c ε r η data hf hε (le_of_lt hη) v hv hsupp hdfOn hrate y =
              curveAt v hcomplete y.1 (σ - L) := by
            simpa [σ, L] using (morseCollarMap_of_strip hk c ε r η data hf hε (le_of_lt hη) v hv hsupp
              hdfOn hrate y hy)
          rw [hmap']
          have hh := curveAt_add v hv1 hcomplete y.1 σ (-L)
          have hz : σ + (-L) = σ - L := by ring
          rw [hz] at hh
          simpa [x] using hh
        rw [hmap]
        rw [himg]
        rw [hflowstuck]
        rw [hχz]
        have hrange : Set.range (handleEmbedding hk c ε r data) =
            data.χ '' (modelHandle hk ε r : Set (MorseModel (m + 1))) := by
          change Set.range (data.χ ∘ modelHandleMap hk ε r) =
            data.χ '' (modelHandle hk ε r : Set (MorseModel (m + 1)))
          rw [Set.range_comp]
          rw [modelHandleMap_range hk ε r hε hr]
        rw [hrange]
        exact Or.inr (by exact hxhandle)

theorem modelFlow_isMIntegralCurveOn {n k : ℕ} (hk : k ≤ n) (y : MorseModel n) :
    IsMIntegralCurveOn (I := 𝓘(ℝ, MorseModel n)) (fun t : ℝ => modelFlow hk t y)
      (modelFlowField hk) {t : ℝ | posPart hk (modelFlow hk t y) ≠ 0} := by
  intro t ht
  have hder := hasDerivAt_modelFlow hk t y ht
  rw [hasDerivAt_iff_hasFDerivAt, ← hasMFDerivAt_iff_hasFDerivAt] at hder
  exact hder.hasMFDerivWithinAt

theorem morseFlowInChart {m k : ℕ} (hk : k ≤ m + 1) (c : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} [I.Boundaryless]
    [IsManifold I (⊤ : WithTop ℕ∞) M] {f : M → ℝ}
    (data : MorseChart (m + 1) k hk c I f)
    (v : (x : M) → TangentSpace I x)
    (hv : ContMDiff I (I.prod 𝓘(ℝ, MorseModel (m + 1))) ∞
      (fun x : M => (⟨x, v x⟩ : TangentBundle I M)))
    (hsupp : IsCompact (tsupport v))
    (hchartField : ∀ z : MorseModel (m + 1), ‖z‖ < data.R' →
      v (data.χ z) = mfderiv 𝓘(ℝ, MorseModel (m + 1)) I data.χ z (modelFlowField hk z))
    (y : MorseModel (m + 1))
    {a b : ℝ} (ha : a < 0) (hb : 0 < b)
    (hstay : ∀ t ∈ Set.Ioo a b, ‖modelFlow hk t y‖ < data.R')
    (hpos : ∀ t ∈ Set.Ioo a b, posPart hk (modelFlow hk t y) ≠ 0) :
    ∀ t ∈ Set.Ioo a b,
      curveAt v (exists_globalIntegralCurve_of_compactSupport v hv hsupp) (data.χ y) t =
        data.χ (modelFlow hk t y) := by
  let hcomplete : ∀ x : M, ∃ γ : ℝ → M, γ 0 = x ∧ IsMIntegralCurve γ v :=
    exists_globalIntegralCurve_of_compactSupport v hv hsupp
  let γ : ℝ → M := curveAt v hcomplete (data.χ y)
  let β : ℝ → M := fun t => data.χ (modelFlow hk t y)
  have hγcur : IsMIntegralCurve γ v := curveAt_integralCurve v hcomplete (data.χ y)
  have hγOn : IsMIntegralCurveOn γ v (Set.Ioo a b) := hγcur.isMIntegralCurveOn _
  have hβOn : IsMIntegralCurveOn β v (Set.Ioo a b) := by
    intro t ht
    have hα : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, MorseModel (m + 1))
        (fun s : ℝ => modelFlow hk s y) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight (modelFlowField hk (modelFlow hk t y))) := by
      have hder := hasDerivAt_modelFlow hk t y (hpos t ht)
      rw [hasDerivAt_iff_hasFDerivAt, ← hasMFDerivAt_iff_hasFDerivAt] at hder
      exact hder
    have hball : modelFlow hk t y ∈ Metric.ball (0 : MorseModel (m + 1)) data.R' := by
      exact Metric.mem_ball.mpr (by
        simpa [dist_zero_right] using (hstay t ht))
    have hχat : ContMDiffAt 𝓘(ℝ, MorseModel (m + 1)) I (↑(⊤ : ℕ∞) : WithTop ℕ∞) data.χ
        (modelFlow hk t y) :=
      data.hχon.contMDiffAt (Metric.isOpen_ball.mem_nhds hball)
    have hχder : HasMFDerivAt 𝓘(ℝ, MorseModel (m + 1)) I data.χ (modelFlow hk t y)
        (mfderiv 𝓘(ℝ, MorseModel (m + 1)) I data.χ (modelFlow hk t y)) := by
      have hmd := hχat.mdifferentiableAt (by simp)
      exact hmd.hasMFDerivAt
    have hcomp := hχder.comp t hα
    have hlineq : (mfderiv 𝓘(ℝ, MorseModel (m + 1)) I data.χ (modelFlow hk t y)).comp
        ((1 : ℝ →L[ℝ] ℝ).smulRight (modelFlowField hk (modelFlow hk t y))) =
        (1 : ℝ →L[ℝ] ℝ).smulRight (v (data.χ (modelFlow hk t y))) := by
      apply ContinuousLinearMap.ext
      intro s
      rw [ContinuousLinearMap.comp_apply]
      simp only [ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.one_apply, map_smul]
      rw [← hchartField (modelFlow hk t y) (hstay t ht)]
    have hβder : HasMFDerivAt 𝓘(ℝ, ℝ) I β t
        ((1 : ℝ →L[ℝ] ℝ).smulRight (v (β t))) := by
      dsimp [β]
      exact hcomp.congr_mfderiv hlineq
    exact hβder.hasMFDerivWithinAt
  have hzero : γ 0 = β 0 := by
    dsimp [γ, β]
    rw [curveAt_zero v hcomplete (data.χ y)]
    rw [modelFlow_zero]
  have hv1 : ContMDiff I (I.prod 𝓘(ℝ, MorseModel (m + 1))) (1 : WithTop ℕ∞)
      (fun x : M => (⟨x, v x⟩ : TangentBundle I M)) :=
    hv.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ ∞)
  have ht₀ : (0 : ℝ) ∈ Set.Ioo a b := by constructor <;> linarith
  have hEq := isMIntegralCurveOn_Ioo_eqOn_of_contMDiff_boundaryless (t₀ := 0)
    (a := a) (b := b) ht₀ hv1 hγOn hβOn hzero
  intro t ht
  exact hEq ht


noncomputable def morseCompressLevel (c ε δ : ℝ) (t : ℝ) : ℝ :=
  if t ≤ c - ε - δ then t else c - ε - δ + (t - c + ε + δ) * δ / (2 * ε + δ)

noncomputable def morseCompressTime (c ε δ : ℝ) (t : ℝ) : ℝ :=
  t - morseCompressLevel c ε δ t

noncomputable def morseUncompressLevel (c ε δ : ℝ) (s : ℝ) : ℝ :=
  if s ≤ c - ε - δ then s else c - ε - δ + (s - c + ε + δ) * (2 * ε + δ) / δ

theorem morseCompressLevel_fixed {c ε δ t : ℝ} (ht : t ≤ c - ε - δ) :
    morseCompressLevel c ε δ t = t := by
  dsimp [morseCompressLevel]
  rw [if_pos ht]

theorem morseCompressTime_zero {c ε δ t : ℝ} (ht : t ≤ c - ε - δ) :
    morseCompressTime c ε δ t = 0 := by
  dsimp [morseCompressTime]
  rw [morseCompressLevel_fixed ht]
  ring

theorem morseCompressLevel_top {c ε δ : ℝ} (hδ : 0 < δ) (hε : 0 < ε) :
    morseCompressLevel c ε δ (c + ε) = c - ε := by
  dsimp [morseCompressLevel]
  rw [if_neg]
  · field_simp [hδ.ne', hε.ne']
    ring
  · nlinarith

theorem morseCompressLevel_strictMono {c ε δ : ℝ} (hδ : 0 < δ) (hε : 0 < ε)
    {t₁ t₂ : ℝ} (ht₁ : c - ε - δ < t₁) (hlt : t₁ < t₂) :
    morseCompressLevel c ε δ t₁ < morseCompressLevel c ε δ t₂ := by
  dsimp [morseCompressLevel]
  rw [if_neg (not_le_of_gt ht₁)]
  have ht₂' : c - ε - δ < t₂ := lt_of_le_of_lt (le_of_lt ht₁) hlt
  rw [if_neg (not_le_of_gt ht₂')]
  have hden : 0 < 2 * ε + δ := by nlinarith [hε, hδ]
  have hmain : (t₁ - c + ε + δ) * δ / (2 * ε + δ) < (t₂ - c + ε + δ) * δ / (2 * ε + δ) := by
    have hmul : (t₁ - c + ε + δ) * δ * (2 * ε + δ) < (t₂ - c + ε + δ) * δ * (2 * ε + δ) := by
      exact mul_lt_mul_of_pos_right
        (mul_lt_mul_of_pos_right (by nlinarith) hδ) hden
    exact (div_lt_div_iff₀ hden hden).mpr hmul
  nlinarith

theorem morseUncompressLevel_compressLevel {c ε δ t : ℝ} (hδ : 0 < δ) (hε : 0 < ε) :
    morseUncompressLevel c ε δ (morseCompressLevel c ε δ t) = t := by
  by_cases htle : t ≤ c - ε - δ
  · rw [morseCompressLevel_fixed htle]
    dsimp [morseUncompressLevel]
    rw [if_pos htle]
  · have htgt : c - ε - δ < t := lt_of_not_ge htle
    dsimp [morseCompressLevel, morseUncompressLevel]
    rw [if_neg (not_le_of_gt htgt)]
    have htop : c - ε - δ < c - ε - δ + (t - c + ε + δ) * δ / (2 * ε + δ) := by
      have hden : 0 < 2 * ε + δ := by nlinarith [hε, hδ]
      have hpos : 0 < (t - c + ε + δ) * δ / (2 * ε + δ) := by
        have hnum : 0 < (t - c + ε + δ) * δ := by nlinarith [hδ, htgt]
        exact div_pos hnum hden
      nlinarith
    rw [if_neg (not_le_of_gt htop)]
    field_simp [hδ.ne', hε.ne']
    ring

theorem morseCompressLevel_uncompressLevel {c ε δ s : ℝ} (hδ : 0 < δ) (hε : 0 < ε) :
    morseCompressLevel c ε δ (morseUncompressLevel c ε δ s) = s := by
  by_cases hsle : s ≤ c - ε - δ
  · dsimp [morseUncompressLevel]
    rw [if_pos hsle]
    rw [morseCompressLevel_fixed hsle]
  · have hsgt : c - ε - δ < s := lt_of_not_ge hsle
    dsimp [morseCompressLevel, morseUncompressLevel]
    rw [if_neg (not_le_of_gt hsgt)]
    have htop : c - ε - δ < c - ε - δ + (s - c + ε + δ) * (2 * ε + δ) / δ := by
      have hnum : 0 < (s - c + ε + δ) * (2 * ε + δ) := by nlinarith [hsgt, hε, hδ]
      have hpos : 0 < (s - c + ε + δ) * (2 * ε + δ) / δ := div_pos hnum hδ
      nlinarith
    rw [if_neg (not_le_of_gt htop)]
    field_simp [hδ.ne', hε.ne']
    ring


theorem morseUncompressLevel_fixed {c ε δ s : ℝ} (hs : s ≤ c - ε - δ) :
    morseUncompressLevel c ε δ s = s := by
  dsimp [morseUncompressLevel]
  rw [if_pos hs]

theorem morseUncompressLevel_top {c ε δ : ℝ} (hδ : 0 < δ) :
    morseUncompressLevel c ε δ (c - ε) = c + ε := by
  dsimp [morseUncompressLevel]
  rw [if_neg]
  · field_simp [hδ.ne']
    ring
  · nlinarith

theorem morseUncompressLevel_strictMono {c ε δ : ℝ} (hδ : 0 < δ) (hε : 0 < ε)
    {s₁ s₂ : ℝ} (hs₁ : c - ε - δ < s₁) (hlt : s₁ < s₂) :
    morseUncompressLevel c ε δ s₁ < morseUncompressLevel c ε δ s₂ := by
  dsimp [morseUncompressLevel]
  rw [if_neg (not_le_of_gt hs₁)]
  have hs₂ : c - ε - δ < s₂ := lt_of_le_of_lt (le_of_lt hs₁) hlt
  rw [if_neg (not_le_of_gt hs₂)]
  have hden : 0 < δ := hδ
  have hmain : (s₁ - c + ε + δ) * (2 * ε + δ) / δ < (s₂ - c + ε + δ) * (2 * ε + δ) / δ := by
    have hmul : (s₁ - c + ε + δ) * (2 * ε + δ) * δ < (s₂ - c + ε + δ) * (2 * ε + δ) * δ := by
      exact mul_lt_mul_of_pos_right
        (mul_lt_mul_of_pos_right (by nlinarith) (by nlinarith [hε, hδ])) hden
    exact (div_lt_div_iff₀ hden hden).mpr hmul
  nlinarith

theorem morseExpandTime {c ε δ : ℝ} (hδ : 0 < δ) {t : ℝ}
    (ht : c - ε - δ < t) :
    t - morseUncompressLevel c ε δ t = -(t - c + ε + δ) * (2 * ε) / δ := by
  dsimp [morseUncompressLevel]
  rw [if_neg (not_le_of_gt ht)]
  field_simp [hδ.ne']
  ring


noncomputable def morseFarCutoffPos (r ε' : ℝ) (s : ℝ) : ℝ :=
  Real.smoothTransition ((s - r) / ε')

theorem morseFarCutoffPos_zero {r ε' s : ℝ} (hε' : 0 < ε') (hs : s ≤ r) :
    morseFarCutoffPos r ε' s = 0 := by
  dsimp [morseFarCutoffPos]
  have harg : (s - r) / ε' ≤ 0 := by
    exact div_nonpos_of_nonpos_of_nonneg (by linarith) (le_of_lt hε')
  rw [Real.smoothTransition.zero_of_nonpos harg]

theorem morseFarCutoffPos_one {r ε' s : ℝ} (hε' : 0 < ε') (hs : r + ε' ≤ s) :
    morseFarCutoffPos r ε' s = 1 := by
  dsimp [morseFarCutoffPos]
  have harg : 1 ≤ (s - r) / ε' := (one_le_div hε').mpr (by nlinarith)
  rw [Real.smoothTransition.one_of_one_le harg]

noncomputable def morseFarCutoffNorm (R₀ R₁ : ℝ) (u : ℝ) : ℝ :=
  Real.smoothTransition ((u - R₀) / (R₁ - R₀))

theorem morseFarCutoffNorm_zero {R₀ R₁ u : ℝ} (hR : R₀ < R₁) (hu : u ≤ R₀) :
    morseFarCutoffNorm R₀ R₁ u = 0 := by
  dsimp [morseFarCutoffNorm]
  have harg : (u - R₀) / (R₁ - R₀) ≤ 0 := by
    exact div_nonpos_of_nonpos_of_nonneg (by linarith) (by nlinarith)
  rw [Real.smoothTransition.zero_of_nonpos harg]

theorem morseFarCutoffNorm_one {R₀ R₁ u : ℝ} (hR : R₀ < R₁) (hu : R₁ ≤ u) :
    morseFarCutoffNorm R₀ R₁ u = 1 := by
  dsimp [morseFarCutoffNorm]
  have harg : 1 ≤ (u - R₀) / (R₁ - R₀) := (one_le_div (by nlinarith : 0 < R₁ - R₀)).mpr (by nlinarith)
  rw [Real.smoothTransition.one_of_one_le harg]

noncomputable def morseFarCutoff {m k : ℕ} (hk : k ≤ m + 1) (c : ℝ) (r ε' R₀ R₁ : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} {f : M → ℝ}
    (data : MorseChart (m + 1) k hk c I f) (x : M) : ℝ := by
  classical
  exact if x ∈ data.χ.target then
    max (morseFarCutoffPos r ε' (‖posPart hk (data.χ.symm x)‖))
      (morseFarCutoffNorm R₀ R₁ (morseNorm (m + 1) (data.χ.symm x)))
  else 1

theorem morseFarCutoff_mem {m k : ℕ} (hk : k ≤ m + 1) (c : ℝ) (r ε' R₀ R₁ : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} {f : M → ℝ}
    (data : MorseChart (m + 1) k hk c I f) (x : M) :
    morseFarCutoff hk c r ε' R₀ R₁ data x ∈ Set.Icc (0 : ℝ) 1 := by
  by_cases hx : x ∈ data.χ.target
  · dsimp [morseFarCutoff]
    rw [if_pos hx]
    have hp : morseFarCutoffPos r ε' (‖posPart hk (data.χ.symm x)‖) ∈ Set.Icc (0 : ℝ) 1 := by
      constructor
      · exact Real.smoothTransition.nonneg _
      · exact Real.smoothTransition.le_one _
    have hn : morseFarCutoffNorm R₀ R₁ (morseNorm (m + 1) (data.χ.symm x)) ∈ Set.Icc (0 : ℝ) 1 := by
      constructor
      · exact Real.smoothTransition.nonneg _
      · exact Real.smoothTransition.le_one _
    constructor
    · exact le_max_of_le_left hp.1
    · exact max_le hp.2 hn.2
  · dsimp [morseFarCutoff]
    rw [if_neg hx]
    simp

theorem morseFarCutoff_eq_zero {m k : ℕ} (hk : k ≤ m + 1) (c : ℝ) (r ε' R₀ R₁ : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} {f : M → ℝ}
    (data : MorseChart (m + 1) k hk c I f) {x : M} (hx : x ∈ data.χ.target)
    (hr : ‖posPart hk (data.χ.symm x)‖ ≤ r) (hR : morseNorm (m + 1) (data.χ.symm x) ≤ R₀)
    (hε' : 0 < ε') (hR0 : R₀ < R₁) :
    morseFarCutoff hk c r ε' R₀ R₁ data x = 0 := by
  dsimp [morseFarCutoff]
  rw [if_pos hx]
  have hp := morseFarCutoffPos_zero (r := r) (ε' := ε') (s := ‖posPart hk (data.χ.symm x)‖) hε' hr
  have hn := morseFarCutoffNorm_zero (R₀ := R₀) (R₁ := R₁) (u := morseNorm (m + 1) (data.χ.symm x)) hR0 hR
  rw [hp, hn]
  simp

theorem morseFarCutoff_eq_one {m k : ℕ} (hk : k ≤ m + 1) (c : ℝ) (r ε' R₀ R₁ : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} {f : M → ℝ}
    (data : MorseChart (m + 1) k hk c I f) {x : M}
    (hr : x ∈ data.χ.target → r + ε' ≤ ‖posPart hk (data.χ.symm x)‖)
    (hR : x ∈ data.χ.target → R₁ ≤ morseNorm (m + 1) (data.χ.symm x))
    (hε' : 0 < ε') (hR0 : R₀ < R₁) :
    morseFarCutoff hk c r ε' R₀ R₁ data x = 1 := by
  by_cases hx : x ∈ data.χ.target
  · dsimp [morseFarCutoff]
    rw [if_pos hx]
    have hp := morseFarCutoffPos_one (r := r) (ε' := ε') (s := ‖posPart hk (data.χ.symm x)‖) hε' (hr hx)
    have hn := morseFarCutoffNorm_one (R₀ := R₀) (R₁ := R₁) (u := morseNorm (m + 1) (data.χ.symm x)) hR0 (hR hx)
    rw [hp, hn]
    simp
  · dsimp [morseFarCutoff]
    rw [if_neg hx]


theorem morseCollarLevelMap_injective_of_level {m k : ℕ} (hk : k ≤ m + 1) (c ε r η : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} {f : M → ℝ}
    {f₀ : M → ℝ} (data : MorseChart (m + 1) k hk c I f₀)
    (hε : 0 < ε) (hη : 0 < η)
    (x : LevelSetSpace f (c - ε)) (σ₁ σ₂ : ℝ)
    (_hσ₁ : σ₁ ∈ Set.Icc (-η) (r ^ 2 / 2 + ε))
    (_hσ₂ : σ₂ ∈ Set.Icc (-η) (r ^ 2 / 2 + ε))
    (h : morseCollarLevelMap hk c ε r η data x σ₁ = morseCollarLevelMap hk c ε r η data x σ₂) :
    σ₁ = σ₂ := by
  have hT : 0 ≤ morseCollarTopLevel hk c ε r data x :=
    morseCollarTopLevel_nonneg hk c ε r data x
  have hden : r ^ 2 / 2 + ε + η ≠ 0 := by positivity
  have hTη : morseCollarTopLevel hk c ε r data x + η ≠ 0 := by
    have : 0 < morseCollarTopLevel hk c ε r data x + η := by nlinarith [hT, hη]
    exact ne_of_gt this
  dsimp [morseCollarLevelMap] at h
  have hstep : (morseCollarTopLevel hk c ε r data x + η) * (σ₁ + η) / (r ^ 2 / 2 + ε + η) =
      (morseCollarTopLevel hk c ε r data x + η) * (σ₂ + η) / (r ^ 2 / 2 + ε + η) := by
    linarith
  have hcancel : σ₁ + η = σ₂ + η := by
    have hstep' := (div_eq_iff hden).mp hstep
    field_simp [hden] at hstep'
    exact hstep'
  linarith

theorem morseCollarLevelMap_surjective {m k : ℕ} (hk : k ≤ m + 1) (c ε r η : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} {f : M → ℝ}
    {f₀ : M → ℝ} (data : MorseChart (m + 1) k hk c I f₀)
    (hε : 0 < ε) (hη : 0 < η)
    (x : LevelSetSpace f (c - ε)) (t : ℝ)
    (ht : t ∈ Set.Icc (-η) (morseCollarTopLevel hk c ε r data x)) :
    ∃ σ ∈ Set.Icc (-η) (r ^ 2 / 2 + ε), morseCollarLevelMap hk c ε r η data x σ = t := by
  have hT : 0 ≤ morseCollarTopLevel hk c ε r data x :=
    morseCollarTopLevel_nonneg hk c ε r data x
  have hTη : 0 < morseCollarTopLevel hk c ε r data x + η := by nlinarith [hT, hη]
  have hden : r ^ 2 / 2 + ε + η ≠ 0 := by positivity
  let σ : ℝ := -η + (t + η) * (r ^ 2 / 2 + ε + η) / (morseCollarTopLevel hk c ε r data x + η)
  refine ⟨σ, ?_, ?_⟩
  · constructor
    · dsimp [σ]
      have h1 : 0 ≤ (t + η) * (r ^ 2 / 2 + ε + η) / (morseCollarTopLevel hk c ε r data x + η) := by
        have h1' : 0 ≤ t + η := by nlinarith [ht.1, hη]
        have h2' : 0 < r ^ 2 / 2 + ε + η := by positivity
        exact div_nonneg (mul_nonneg h1' (le_of_lt h2')) (le_of_lt hTη)
      nlinarith
    · dsimp [σ]
      have h1 : t ≤ morseCollarTopLevel hk c ε r data x := ht.2
      have hTle : morseCollarTopLevel hk c ε r data x ≤ r ^ 2 / 2 :=
        morseCollarTopLevel_le hk c ε r data x
      have hnum : (t + η) * (r ^ 2 / 2 + ε + η) ≤
          (morseCollarTopLevel hk c ε r data x + η) * (r ^ 2 / 2 + ε + η) := by
        have h1' : t + η ≤ morseCollarTopLevel hk c ε r data x + η := by nlinarith [h1, hη]
        have h2' : 0 ≤ r ^ 2 / 2 + ε + η := by positivity
        exact mul_le_mul_of_nonneg_right h1' h2'
      have hdiv : (t + η) * (r ^ 2 / 2 + ε + η) / (morseCollarTopLevel hk c ε r data x + η) ≤
          r ^ 2 / 2 + ε + η := by
        exact (div_le_iff₀ hTη).mpr (by
          nlinarith [hnum])
      have hmain : -η + (t + η) * (r ^ 2 / 2 + ε + η) / (morseCollarTopLevel hk c ε r data x + η) ≤
          r ^ 2 / 2 + ε := by
        nlinarith [hdiv]
      exact hmain
  · dsimp [morseCollarLevelMap, σ]
    have hmain : -η + (morseCollarTopLevel hk c ε r data x + η) *
        ((-η + (t + η) * (r ^ 2 / 2 + ε + η) / (morseCollarTopLevel hk c ε r data x + η)) + η) /
          (r ^ 2 / 2 + ε + η) = t := by
      field_simp [show r ^ 2 / 2 + ε + η ≠ 0 by positivity, ne_of_gt hTη]
      ring
    exact hmain

theorem morseHandlePoint_f_mem {m k : ℕ} (hk : k ≤ m + 1) (c ε r : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} {f : M → ℝ}
    (data : MorseChart (m + 1) k hk c I f)
    (hε : 0 < ε) (hr : 0 < r) (hεr : Real.sqrt (2 * ε + 2 * r ^ 2) < data.R)
    (w : MorseModel (m + 1)) (hw : w ∈ modelHandle hk ε r) :
    f (data.χ w) ∈ Set.Icc (c - ε) (c + r ^ 2 / 2) := by
  have hrange : w ∈ Set.range (modelHandleMap hk ε r) := by
    rw [← modelHandleMap_range hk ε r hε hr] at hw
    exact hw
  rcases hrange with ⟨d, hd⟩
  have hsrc : w ∈ data.χ.source := data.hχsrc w (by
    rw [← hd]
    exact le_trans (modelHandleMap_norm_le hk ε r (le_of_lt hε) d) (le_of_lt hεr))
  rw [data.hnorm w (by
    rw [← hd]
    exact le_trans (modelHandleMap_norm_le hk ε r (le_of_lt hε) d) (le_of_lt hεr))]
  rw [← hd]
  constructor
  · have hmem : c - ε ≤ morseNormalForm hk c w := by
      rw [modelHandle_eq_inter hk c ε r (le_of_lt hr)] at hw
      exact hw.2
    rw [← hd] at hmem
    exact hmem
  · exact modelHandleMap_f_le hk c ε r (le_of_lt hε) d

noncomputable def morseCollarFlowBase {m k : ℕ} (_hk : k ≤ m + 1) (c ε r η : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} [I.Boundaryless]
    [IsManifold I (⊤ : WithTop ℕ∞) M] {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) f)
    (hε : 0 < ε) (hη : 0 < η)
    (v : (x : M) → TangentSpace I x)
    (hv : ContMDiff I (I.prod 𝓘(ℝ, MorseModel (m + 1))) ∞
      (fun x : M => (⟨x, v x⟩ : TangentBundle I M)))
    (hsupp : IsCompact (tsupport v))
    (hdfOn : ∀ x ∈ f ⁻¹' Set.Icc (c - ε - η) (c + r ^ 2 / 2),
      (NormedSpace.fromTangentSpace (f x)) ((mfderiv I 𝓘(ℝ, ℝ) f x) (v x)) = -1)
    (hrate : ∀ x,
      -1 ≤ (NormedSpace.fromTangentSpace (f x)) ((mfderiv I 𝓘(ℝ, ℝ) f x) (v x)) ∧
      (NormedSpace.fromTangentSpace (f x)) ((mfderiv I 𝓘(ℝ, ℝ) f x) (v x)) ≤ 0)
    (z : M) (hz : f z ∈ Set.Icc (c - ε - η) (c + r ^ 2 / 2)) : LevelSetSpace f (c - ε) :=
  ⟨curveAt v (exists_globalIntegralCurve_of_compactSupport v hv hsupp) z (f z - c + ε), by
    exact (morseCollarFlow_levelValue (I := I) f c ε r η hε (le_of_lt hη) hf v hv hsupp hdfOn
      hrate hz)⟩

theorem morseCollarTopLevel_ge_flowTime_of_handlePoint {m k : ℕ} (hk : k ≤ m + 1) (c ε r η : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} [I.Boundaryless]
    [IsManifold I (⊤ : WithTop ℕ∞) M] {f : M → ℝ}
    (data : MorseChart (m + 1) k hk c I f)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) f)
    (hε : 0 < ε) (hη : 0 < η) (hr : 0 < r) (hr2 : r ^ 2 = 2 * ε)
    (hεr' : Real.sqrt (2 * ε + 2 * r ^ 2) < data.R)
    (v : (x : M) → TangentSpace I x)
    (hv : ContMDiff I (I.prod 𝓘(ℝ, MorseModel (m + 1))) ∞
      (fun x : M => (⟨x, v x⟩ : TangentBundle I M)))
    (hsupp : IsCompact (tsupport v))
    (hdfOn : ∀ x ∈ f ⁻¹' Set.Icc (c - ε - η) (c + r ^ 2 / 2),
      (NormedSpace.fromTangentSpace (f x)) ((mfderiv I 𝓘(ℝ, ℝ) f x) (v x)) = -1)
    (hrate : ∀ x,
      -1 ≤ (NormedSpace.fromTangentSpace (f x)) ((mfderiv I 𝓘(ℝ, ℝ) f x) (v x)) ∧
      (NormedSpace.fromTangentSpace (f x)) ((mfderiv I 𝓘(ℝ, ℝ) f x) (v x)) ≤ 0)
    (hflowChart : ∀ y : MorseModel (m + 1), y ∈ data.χ.source →
      ∀ t : ℝ, curveAt v (exists_globalIntegralCurve_of_compactSupport v hv hsupp) (data.χ y) t =
        data.χ (modelFlow hk t y))
    (w : MorseModel (m + 1)) (hw : w ∈ modelHandle hk ε r)
    (hwneg : 2 * ε ≤ ‖negPart hk w‖ ^ 2) :
    morseCollarTopLevel hk c ε r data
      (morseCollarFlowBase hk c ε r η hf hε hη v hv hsupp hdfOn hrate (data.χ w)
        (by
          have hmem := morseHandlePoint_f_mem hk c ε r data hε hr hεr' w hw
          constructor
          · nlinarith [hmem.1, hη]
          · exact hmem.2)) ≥
      f (data.χ w) - c + ε := by
  let hcomplete : ∀ x : M, ∃ γ : ℝ → M, γ 0 = x ∧ IsMIntegralCurve γ v :=
    exists_globalIntegralCurve_of_compactSupport v hv hsupp
  let σ' : ℝ := f (data.χ w) - c + ε
  have hmem : f (data.χ w) ∈ Set.Icc (c - ε) (c + r ^ 2 / 2) :=
    morseHandlePoint_f_mem hk c ε r data hε hr hεr' w hw
  have hσ0 : 0 ≤ σ' := by
    dsimp [σ']
    nlinarith [hmem.1]
  have hrange : w ∈ Set.range (modelHandleMap hk ε r) := by
    rw [← modelHandleMap_range hk ε r hε hr] at hw
    exact hw
  rcases hrange with ⟨d, hd⟩
  have hwle : morseNorm (m + 1) w ≤ Real.sqrt (2 * ε + 2 * r ^ 2) := by
    rw [← hd]
    exact modelHandleMap_norm_le hk ε r (le_of_lt hε) d
  have hsrcw : w ∈ data.χ.source := data.hχsrc w (le_trans hwle (le_of_lt hεr'))
  have hfw : f (data.χ w) = morseNormalForm hk c w := data.hnorm w (le_trans hwle (le_of_lt hεr'))
  have hσ'eq : σ' = ε + (‖posPart hk w‖ ^ 2 - ‖negPart hk w‖ ^ 2) / 2 := by
    dsimp [σ']
    rw [hfw]
    rw [morseNormalForm_split hk c w]
    ring
  have hσposle : σ' ≤ ‖posPart hk w‖ ^ 2 / 2 := by
    rw [hσ'eq]
    nlinarith [hwneg]
  let x : LevelSetSpace f (c - ε) :=
    morseCollarFlowBase hk c ε r η hf hε hη v hv hsupp hdfOn hrate (data.χ w)
      (by
        have hmem := morseHandlePoint_f_mem hk c ε r data hε hr hεr' w hw
        constructor
        · nlinarith [hmem.1, hη]
        · exact hmem.2)
  have hxeq : x.1 = data.χ (modelFlow hk σ' w) := by
    dsimp [x, morseCollarFlowBase, σ']
    exact hflowChart w hsrcw (f (data.χ w) - c + ε)
  have hflowle : morseNorm (m + 1) (modelFlow hk σ' w) ≤ morseNorm (m + 1) w :=
    modelFlow_norm_le hk σ' w hσ0 hσposle
  have hsrcflow : modelFlow hk σ' w ∈ data.χ.source := data.hχsrc (modelFlow hk σ' w)
    (le_trans hflowle (le_trans hwle (le_of_lt hεr')))
  have hchart : x ∈ morseCollarChartSet hk c ε r data := by
    dsimp [morseCollarChartSet]
    refine ⟨modelFlow hk σ' w, ?_, hxeq.symm⟩
    exact lt_of_le_of_lt hflowle (lt_of_le_of_lt hwle hεr')
  have htop := morseCollarTopLevel_eq_on_chart hk c ε r data x hchart
  have hz' : data.χ.symm x.1 = modelFlow hk σ' w := by
    rw [hxeq]
    exact data.χ.left_inv hsrcflow
  have hpossq : ‖posPart hk (modelFlow hk σ' w)‖ ^ 2 = ‖posPart hk w‖ ^ 2 - 2 * σ' :=
    modelFlow_posPart_norm_sq hk σ' w hσ0 hσposle
  have hpossq' : ‖posPart hk (modelFlow hk σ' w)‖ ^ 2 = ‖negPart hk w‖ ^ 2 - 2 * ε := by
    rw [hpossq]
    rw [hσ'eq]
    ring
  have htopval : morseCollarTopLevel hk c ε r data x = 2 * ε - ‖negPart hk w‖ ^ 2 / 2 := by
    rw [htop]
    rw [hz']
    rw [hpossq']
    rw [hr2]
    have harg : 0 ≤ (2 * ε - (‖negPart hk w‖ ^ 2 - 2 * ε)) / 2 := by
      have hnegle : ‖negPart hk w‖ ^ 2 ≤ r ^ 2 + 2 * ε := by
        have hposle : ‖posPart hk w‖ ^ 2 ≤ r ^ 2 := hw.1
        nlinarith [hw.2, hposle]
      nlinarith [hnegle, hr2]
    rw [max_eq_right harg]
    ring
  rw [htopval]
  change 2 * ε - ‖negPart hk w‖ ^ 2 / 2 ≥ σ'
  rw [hσ'eq]
  have hposle : ‖posPart hk w‖ ^ 2 ≤ r ^ 2 := hw.1
  rw [hr2] at hposle
  nlinarith

theorem morseCollarMap_surj_on_image {m k : ℕ} (hk : k ≤ m + 1) (c ε r η : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} [I.Boundaryless]
    [IsManifold I (⊤ : WithTop ℕ∞) M] {f : M → ℝ}
    {f₀ : M → ℝ} (data : MorseChart (m + 1) k hk c I f₀)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) f)
    (hε : 0 < ε) (hη : 0 < η)
    (v : (x : M) → TangentSpace I x)
    (hv : ContMDiff I (I.prod 𝓘(ℝ, MorseModel (m + 1))) ∞
      (fun x : M => (⟨x, v x⟩ : TangentBundle I M)))
    (hsupp : IsCompact (tsupport v))
    (hdfOn : ∀ x ∈ f ⁻¹' Set.Icc (c - ε - η) (c + r ^ 2 / 2),
      (NormedSpace.fromTangentSpace (f x)) ((mfderiv I 𝓘(ℝ, ℝ) f x) (v x)) = -1)
    (hrate : ∀ x,
      -1 ≤ (NormedSpace.fromTangentSpace (f x)) ((mfderiv I 𝓘(ℝ, ℝ) f x) (v x)) ∧
      (NormedSpace.fromTangentSpace (f x)) ((mfderiv I 𝓘(ℝ, ℝ) f x) (v x)) ≤ 0)
    (hHandleInterval : ∀ (w : MorseModel (m + 1)), w ∈ modelHandle hk ε r → f (data.χ w) ∈ Set.Icc (c - ε - η) (c + r ^ 2 / 2))
    (hHandleUpper : ∀ (w : MorseModel (m + 1)), w ∈ modelHandle hk ε r → f (data.χ w) ≤ c + r ^ 2 / 2)
    (hflowTop : ∀ (w : MorseModel (m + 1)) (hw : w ∈ modelHandle hk ε r),
      morseCollarTopLevel hk c ε r data
        (morseCollarFlowBase hk c ε r η hf hε hη v hv hsupp hdfOn hrate (data.χ w)
          (hHandleInterval w hw)) ≥
        f (data.χ w) - c + ε) :
    ∀ z : M, (f z ≤ c - ε ∨ z ∈ data.χ '' (modelHandle hk ε r : Set (MorseModel (m + 1)))) →
      ∃ y : SublevelSpace f (c + r ^ 2 / 2),
        morseCollarMap hk c ε r η data hf hε (le_of_lt hη) v hv hsupp hdfOn hrate y = z := by
  intro z hz
  by_cases hzlow : f z ≤ c - ε - η
  · refine ⟨⟨z, ?_⟩, ?_⟩
    · change f z ≤ c + r ^ 2 / 2
      nlinarith [hzlow, hε, hη]
    · exact morseCollarMap_of_low hk c ε r η data hf hε (le_of_lt hη) v hv hsupp hdfOn hrate ⟨z, by
        change f z ≤ c + r ^ 2 / 2
        nlinarith [hzlow, hε, hη]⟩ hzlow
  · have hzgt : c - ε - η < f z := lt_of_not_ge hzlow
    have hzsub : f z ≤ c + r ^ 2 / 2 := by
      rcases hz with hzlow' | hzh
      · nlinarith [hzlow', hε, hη]
      · rcases hzh with ⟨w, hw, hwz⟩
        rw [← hwz]
        exact hHandleUpper w hw
    let hcomplete : ∀ x : M, ∃ γ : ℝ → M, γ 0 = x ∧ IsMIntegralCurve γ v :=
      exists_globalIntegralCurve_of_compactSupport v hv hsupp
    have hv1 : ContMDiff I (I.prod 𝓘(ℝ, MorseModel (m + 1))) (1 : WithTop ℕ∞)
        (fun x : M => (⟨x, v x⟩ : TangentBundle I M)) :=
      hv.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ ∞)
    let σ' : ℝ := f z - c + ε
    let x : LevelSetSpace f (c - ε) := morseCollarFlowBase hk c ε r η hf hε hη v hv hsupp hdfOn hrate z (by
      constructor
      · exact le_of_lt hzgt
      · exact hzsub)
    have hT : morseCollarTopLevel hk c ε r data x ≥ σ' := by
      rcases hz with hzlow' | hzh
      · have hσ'le : σ' ≤ 0 := by dsimp [σ']; linarith [hzlow']
        exact le_trans hσ'le (morseCollarTopLevel_nonneg hk c ε r data x)
      · rcases hzh with ⟨w, hw, hwz⟩
        have hxeq : x = morseCollarFlowBase hk c ε r η hf hε hη v hv hsupp hdfOn hrate (data.χ w)
            (hHandleInterval w hw) := by
          apply Subtype.ext
          dsimp [x, morseCollarFlowBase]
          rw [← hwz]
        have hw' : σ' = f (data.χ w) - c + ε := by
          dsimp [σ']
          rw [← hwz]
        rw [hxeq, hw']
        exact hflowTop w hw
    have hσexists := morseCollarLevelMap_surjective hk c ε r η data hε hη x σ' (by
      constructor
      · dsimp [σ']
        linarith [hzgt]
      · exact hT)
    rcases hσexists with ⟨σ, hσmem, hσeq⟩
    have hx : f x.1 = c - ε := x.2
    have hx' : f x.1 ∈ Set.Icc (c - ε - η) (c + r ^ 2 / 2) := by
      constructor
      · nlinarith [hx, hη]
      · nlinarith [hx, hε, hη]
    have hval : f (curveAt v hcomplete x.1 (-σ)) = c - ε + σ := by
      have hval0 : f (curveAt v hcomplete x.1 (-σ)) = f x.1 - (-σ) :=
        morseCollarFlow_valueOnStrip (I := I) f c ε r η hf v hv hsupp hdfOn hrate hx'
          (by linarith [hx, hσmem.2]) (by linarith [hx, hσmem.1])
      rw [hx] at hval0
      simpa [sub_neg_eq_add] using hval0
    let y : SublevelSpace f (c + r ^ 2 / 2) := ⟨curveAt v hcomplete x.1 (-σ), by
      change f (curveAt v hcomplete x.1 (-σ)) ≤ c + r ^ 2 / 2
      nlinarith [hval, hσmem.2]⟩
    refine ⟨y, ?_⟩
    have hy : c - ε - η ≤ f y.1 := by
      change c - ε - η ≤ f (curveAt v hcomplete x.1 (-σ))
      nlinarith [hval, hσmem.1]
    have hmap' := morseCollarMap_of_strip hk c ε r η data hf hε (le_of_lt hη) v hv hsupp hdfOn hrate y hy
    have hfval : f y.1 = c - ε + σ := by
      change f (curveAt v hcomplete x.1 (-σ)) = c - ε + σ
      exact hval
    have hxeq : ⟨curveAt v hcomplete y.1 (f y.1 - c + ε), by
        exact (morseCollarFlow_levelValue (I := I) f c ε r η hε (le_of_lt hη) hf v hv hsupp hdfOn hrate (by
          constructor
          · exact hy
          · exact y.2))⟩ = x := by
      apply Subtype.ext
      change curveAt v hcomplete y.1 (f y.1 - c + ε) = x.1
      have hy1 : y.1 = curveAt v hcomplete x.1 (-σ) := rfl
      have hstep : curveAt v hcomplete (curveAt v hcomplete x.1 (-σ)) σ = curveAt v hcomplete x.1 0 := by
        have hh := curveAt_add v hv1 hcomplete x.1 (-σ) σ
        have hsum : -σ + σ = 0 := by ring
        rw [hsum] at hh
        exact hh.symm
      rw [hy1, hfval]
      have htime_arg : c - ε + σ - c + ε = σ := by ring
      rw [htime_arg, hstep]
      exact curveAt_zero v hcomplete x.1
    have hfσ : f y.1 - c + ε = σ := by
      rw [hfval]
      ring
    have hL : morseCollarLevelMap hk c ε r η data
        (⟨curveAt v hcomplete y.1 (f y.1 - c + ε), by
          exact (morseCollarFlow_levelValue (I := I) f c ε r η hε (le_of_lt hη) hf v hv hsupp hdfOn hrate (by
            constructor
            · exact hy
            · exact y.2))⟩) (f y.1 - c + ε) = σ' := by
      rw [hxeq]
      rw [hfσ]
      exact hσeq
    have htime : f y.1 - c + ε - morseCollarLevelMap hk c ε r η data
        (⟨curveAt v hcomplete y.1 (f y.1 - c + ε), by
          exact (morseCollarFlow_levelValue (I := I) f c ε r η hε (le_of_lt hη) hf v hv hsupp hdfOn hrate (by
            constructor
            · exact hy
            · exact y.2))⟩) (f y.1 - c + ε) = σ - σ' := by
      conv_lhs =>
        congr
        · rw [hfσ]
        · rw [hL]
    have hz' : curveAt v hcomplete x.1 (-σ') = z := by
      have hh := curveAt_add v hv1 hcomplete z σ' (-σ')
      have hsum : σ' + (-σ') = 0 := by ring
      rw [hsum] at hh
      have hx' : curveAt v hcomplete z σ' = x.1 := rfl
      rw [hx'] at hh
      simpa [curveAt_zero v hcomplete z] using hh.symm
    rw [hmap']
    have hflow : curveAt v hcomplete y.1 (σ - σ') = z := by
      have hy1 : y.1 = curveAt v hcomplete x.1 (-σ) := rfl
      rw [hy1]
      have hh := curveAt_add v hv1 hcomplete x.1 (-σ) (σ - σ')
      have hsum : -σ + (σ - σ') = -σ' := by ring
      rw [hsum] at hh
      rw [← hh]
      exact hz'
    change curveAt v hcomplete y.1 (f y.1 - c + ε - morseCollarLevelMap hk c ε r η data
      (⟨curveAt v hcomplete y.1 (f y.1 - c + ε), by
        exact (morseCollarFlow_levelValue (I := I) f c ε r η hε (le_of_lt hη) hf v hv hsupp hdfOn hrate (by
          constructor
          · exact hy
          · exact y.2))⟩) (f y.1 - c + ε)) = z
    rw [htime]
    exact hflow

theorem morseCollarMap_injective {m k : ℕ} (hk : k ≤ m + 1) (c ε r η : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} [I.Boundaryless]
    [IsManifold I (⊤ : WithTop ℕ∞) M] {f : M → ℝ}
    {f₀ : M → ℝ} (data : MorseChart (m + 1) k hk c I f₀)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) f)
    (hε : 0 < ε) (hη : 0 < η)
    (v : (x : M) → TangentSpace I x)
    (hv : ContMDiff I (I.prod 𝓘(ℝ, MorseModel (m + 1))) ∞
      (fun x : M => (⟨x, v x⟩ : TangentBundle I M)))
    (hsupp : IsCompact (tsupport v))
    (hdfOn : ∀ x ∈ f ⁻¹' Set.Icc (c - ε - η) (c + r ^ 2 / 2),
      (NormedSpace.fromTangentSpace (f x)) ((mfderiv I 𝓘(ℝ, ℝ) f x) (v x)) = -1)
    (hrate : ∀ x,
      -1 ≤ (NormedSpace.fromTangentSpace (f x)) ((mfderiv I 𝓘(ℝ, ℝ) f x) (v x)) ∧
      (NormedSpace.fromTangentSpace (f x)) ((mfderiv I 𝓘(ℝ, ℝ) f x) (v x)) ≤ 0) :
    Function.Injective (morseCollarMap hk c ε r η data hf hε (le_of_lt hη) v hv hsupp hdfOn hrate) := by
  let hcomplete : ∀ x : M, ∃ γ : ℝ → M, γ 0 = x ∧ IsMIntegralCurve γ v :=
    exists_globalIntegralCurve_of_compactSupport v hv hsupp
  have hv1 : ContMDiff I (I.prod 𝓘(ℝ, MorseModel (m + 1))) (1 : WithTop ℕ∞)
      (fun x : M => (⟨x, v x⟩ : TangentBundle I M)) :=
    hv.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ ∞)
  intro y₁ y₂ h
  by_cases h₁ : f y₁.1 ≤ c - ε - η
  · by_cases h₂ : f y₂.1 ≤ c - ε - η
    · apply Subtype.ext
      have hy₁ : morseCollarMap hk c ε r η data hf hε (le_of_lt hη) v hv hsupp hdfOn hrate y₁ = y₁.1 :=
        morseCollarMap_of_low hk c ε r η data hf hε (le_of_lt hη) v hv hsupp hdfOn hrate y₁ h₁
      have hy₂ : morseCollarMap hk c ε r η data hf hε (le_of_lt hη) v hv hsupp hdfOn hrate y₂ = y₂.1 :=
        morseCollarMap_of_low hk c ε r η data hf hε (le_of_lt hη) v hv hsupp hdfOn hrate y₂ h₂
      exact hy₁.symm.trans (h.trans hy₂)
    · have hz : f (morseCollarMap hk c ε r η data hf hε (le_of_lt hη) v hv hsupp hdfOn hrate y₂) =
        f y₁.1 := by
        rw [← h]
        exact congrArg f (morseCollarMap_of_low hk c ε r η data hf hε (le_of_lt hη) v hv hsupp hdfOn hrate y₁ h₁)
      have hzlow : f (morseCollarMap hk c ε r η data hf hε (le_of_lt hη) v hv hsupp hdfOn hrate y₂) ≤
          c - ε - η := by
        rw [hz]
        exact h₁
      have hznonlow : c - ε - η < f y₂.1 := by
        exact lt_of_not_ge h₂
      have hzval := morseCollarMap_value hk c ε r η data hf hε hη v hv hsupp hdfOn hrate y₂ (le_of_lt hznonlow)
      have hL : morseCollarLevelMap hk c ε r η data
          (⟨curveAt v hcomplete y₂.1 (f y₂.1 - c + ε), by
            exact (morseCollarFlow_levelValue (I := I) f c ε r η hε (le_of_lt hη) hf v hv hsupp hdfOn hrate (by
              constructor
              · exact le_of_lt hznonlow
              · exact y₂.2))⟩) (f y₂.1 - c + ε) = -η := by
        have hmem : morseCollarLevelMap hk c ε r η data
            (⟨curveAt v hcomplete y₂.1 (f y₂.1 - c + ε), by
              exact (morseCollarFlow_levelValue (I := I) f c ε r η hε (le_of_lt hη) hf v hv hsupp hdfOn hrate (by
                constructor
                · exact le_of_lt hznonlow
                · exact y₂.2))⟩) (f y₂.1 - c + ε) ∈ Set.Icc (-η) (r ^ 2 / 2) := by
          exact morseCollarLevelMap_mem hk c ε r η data hε (le_of_lt hη) _ (f y₂.1 - c + ε) (by
            have hy2 : f y₂.1 ≤ c + r ^ 2 / 2 := y₂.2
            have hlo : -η ≤ f y₂.1 - c + ε := by linarith [hznonlow]
            have hhi : f y₂.1 - c + ε ≤ r ^ 2 / 2 + ε := by linarith [hy2]
            exact ⟨hlo, hhi⟩)
        have hle : c - ε + morseCollarLevelMap hk c ε r η data
            (⟨curveAt v hcomplete y₂.1 (f y₂.1 - c + ε), by
              exact (morseCollarFlow_levelValue (I := I) f c ε r η hε (le_of_lt hη) hf v hv hsupp hdfOn hrate (by
                constructor
                · exact le_of_lt hznonlow
                · exact y₂.2))⟩) (f y₂.1 - c + ε) ≤ c - ε - η := by
          rw [← hzval]
          exact hzlow
        have hLle : morseCollarLevelMap hk c ε r η data
            (⟨curveAt v hcomplete y₂.1 (f y₂.1 - c + ε), by
              exact (morseCollarFlow_levelValue (I := I) f c ε r η hε (le_of_lt hη) hf v hv hsupp hdfOn hrate (by
                constructor
                · exact le_of_lt hznonlow
                · exact y₂.2))⟩) (f y₂.1 - c + ε) ≤ -η := by
          nlinarith [hle, hmem.1]
        exact le_antisymm hLle hmem.1
      have hσ : f y₂.1 - c + ε = -η := by
        have hy2 : f y₂.1 ≤ c + r ^ 2 / 2 := y₂.2
        have hσmem : f y₂.1 - c + ε ∈ Set.Icc (-η) (r ^ 2 / 2 + ε) := by
          constructor
          · linarith [hznonlow]
          · linarith [hy2]
        by_contra hnot
        have hlt : -η < f y₂.1 - c + ε := lt_of_not_ge (by
          intro hge
          have hlow : -η ≤ f y₂.1 - c + ε := by linarith [hznonlow]
          exact hnot (le_antisymm hge hlow))
        have hmono := morseCollarLevelMap_injective_of_level hk c ε r η data hε hη
          (⟨curveAt v hcomplete y₂.1 (f y₂.1 - c + ε), by
            exact (morseCollarFlow_levelValue (I := I) f c ε r η hε (le_of_lt hη) hf v hv hsupp hdfOn hrate (by
              constructor
              · exact le_of_lt hznonlow
              · exact y₂.2))⟩) (f y₂.1 - c + ε) (-η)
          hσmem (by
            have hy2' : f y₂.1 ≤ c + r ^ 2 / 2 := y₂.2
            constructor <;> linarith)
        have hL' : morseCollarLevelMap hk c ε r η data
            (⟨curveAt v hcomplete y₂.1 (f y₂.1 - c + ε), by
              exact (morseCollarFlow_levelValue (I := I) f c ε r η hε (le_of_lt hη) hf v hv hsupp hdfOn hrate (by
                constructor
                · exact le_of_lt hznonlow
                · exact y₂.2))⟩) (f y₂.1 - c + ε) ≠ -η := by
          intro heq
          have hbnd : morseCollarLevelMap hk c ε r η data
              (⟨curveAt v hcomplete y₂.1 (f y₂.1 - c + ε), by
                exact (morseCollarFlow_levelValue (I := I) f c ε r η hε (le_of_lt hη) hf v hv hsupp hdfOn hrate (by
                  constructor
                  · exact le_of_lt hznonlow
                  · exact y₂.2))⟩) (-η) = -η :=
            morseCollarLevelMap_boundary hk c ε r η data _
          have hσeq : f y₂.1 - c + ε = -η := hmono (heq.trans hbnd.symm)
          exact hnot hσeq
        exact hL' hL
      have hy : y₂.1 = y₁.1 := by
        have hmap₁ : morseCollarMap hk c ε r η data hf hε (le_of_lt hη) v hv hsupp hdfOn hrate y₁ = y₁.1 :=
          morseCollarMap_of_low hk c ε r η data hf hε (le_of_lt hη) v hv hsupp hdfOn hrate y₁ h₁
        have hmap₂ : morseCollarMap hk c ε r η data hf hε (le_of_lt hη) v hv hsupp hdfOn hrate y₂ =
            curveAt v hcomplete y₂.1
              (f y₂.1 - c + ε - morseCollarLevelMap hk c ε r η data
                (⟨curveAt v hcomplete y₂.1 (f y₂.1 - c + ε), by
                  exact (morseCollarFlow_levelValue (I := I) f c ε r η hε (le_of_lt hη) hf v hv hsupp hdfOn hrate (by
                    constructor
                    · exact le_of_lt hznonlow
                    · exact y₂.2))⟩) (f y₂.1 - c + ε)) :=
          morseCollarMap_of_strip hk c ε r η data hf hε (le_of_lt hη) v hv hsupp hdfOn hrate y₂ (le_of_lt hznonlow)
        have hmain : y₁.1 = curveAt v hcomplete y₂.1
            (f y₂.1 - c + ε - morseCollarLevelMap hk c ε r η data
              (⟨curveAt v hcomplete y₂.1 (f y₂.1 - c + ε), by
                exact (morseCollarFlow_levelValue (I := I) f c ε r η hε (le_of_lt hη) hf v hv hsupp hdfOn hrate (by
                  constructor
                  · exact le_of_lt hznonlow
                  · exact y₂.2))⟩) (f y₂.1 - c + ε)) :=
          hmap₁.symm.trans (h.trans hmap₂)
        have htime : f y₂.1 - c + ε - morseCollarLevelMap hk c ε r η data
            (⟨curveAt v hcomplete y₂.1 (f y₂.1 - c + ε), by
              exact (morseCollarFlow_levelValue (I := I) f c ε r η hε (le_of_lt hη) hf v hv hsupp hdfOn hrate (by
                constructor
                · exact le_of_lt hznonlow
                · exact y₂.2))⟩) (f y₂.1 - c + ε) = 0 := by
          dsimp [morseCollarLevelMap]
          have hσ0 : f y₂.1 - c + ε + η = 0 := by linarith [hσ]
          simp [hσ]
        rw [htime] at hmain
        rw [curveAt_zero] at hmain
        exact hmain.symm
      apply Subtype.ext
      exact hy.symm
  · by_cases h₂ : f y₂.1 ≤ c - ε - η
    · have h' : morseCollarMap hk c ε r η data hf hε (le_of_lt hη) v hv hsupp hdfOn hrate y₂ =
          morseCollarMap hk c ε r η data hf hε (le_of_lt hη) v hv hsupp hdfOn hrate y₁ := h.symm
      apply Subtype.ext
      have hz : f (morseCollarMap hk c ε r η data hf hε (le_of_lt hη) v hv hsupp hdfOn hrate y₁) =
          f y₂.1 := by
        rw [← h']
        exact congrArg f (morseCollarMap_of_low hk c ε r η data hf hε (le_of_lt hη) v hv hsupp hdfOn hrate y₂ h₂)
      have hznonlow : c - ε - η < f y₁.1 := by
        exact lt_of_not_ge h₁
      have hzval := morseCollarMap_value hk c ε r η data hf hε hη v hv hsupp hdfOn hrate y₁ (le_of_lt hznonlow)
      have hL : morseCollarLevelMap hk c ε r η data
          (⟨curveAt v hcomplete y₁.1 (f y₁.1 - c + ε), by
            exact (morseCollarFlow_levelValue (I := I) f c ε r η hε (le_of_lt hη) hf v hv hsupp hdfOn hrate (by
              constructor
              · exact le_of_lt hznonlow
              · exact y₁.2))⟩) (f y₁.1 - c + ε) = -η := by
        have hmem : morseCollarLevelMap hk c ε r η data
            (⟨curveAt v hcomplete y₁.1 (f y₁.1 - c + ε), by
              exact (morseCollarFlow_levelValue (I := I) f c ε r η hε (le_of_lt hη) hf v hv hsupp hdfOn hrate (by
                constructor
                · exact le_of_lt hznonlow
                · exact y₁.2))⟩) (f y₁.1 - c + ε) ∈ Set.Icc (-η) (r ^ 2 / 2) := by
          exact morseCollarLevelMap_mem hk c ε r η data hε (le_of_lt hη) _ (f y₁.1 - c + ε) (by
            have hy2 : f y₁.1 ≤ c + r ^ 2 / 2 := y₁.2
            have hlo : -η ≤ f y₁.1 - c + ε := by linarith [hznonlow]
            have hhi : f y₁.1 - c + ε ≤ r ^ 2 / 2 + ε := by linarith [hy2]
            exact ⟨hlo, hhi⟩)
        have hzle : f (morseCollarMap hk c ε r η data hf hε (le_of_lt hη) v hv hsupp hdfOn hrate y₁) ≤
            c - ε - η := by
          rw [hz]
          exact h₂
        have hle : c - ε + morseCollarLevelMap hk c ε r η data
            (⟨curveAt v hcomplete y₁.1 (f y₁.1 - c + ε), by
              exact (morseCollarFlow_levelValue (I := I) f c ε r η hε (le_of_lt hη) hf v hv hsupp hdfOn hrate (by
                constructor
                · exact le_of_lt hznonlow
                · exact y₁.2))⟩) (f y₁.1 - c + ε) ≤ c - ε - η := by
          rw [← hzval]
          exact hzle
        have hLle : morseCollarLevelMap hk c ε r η data
            (⟨curveAt v hcomplete y₁.1 (f y₁.1 - c + ε), by
              exact (morseCollarFlow_levelValue (I := I) f c ε r η hε (le_of_lt hη) hf v hv hsupp hdfOn hrate (by
                constructor
                · exact le_of_lt hznonlow
                · exact y₁.2))⟩) (f y₁.1 - c + ε) ≤ -η := by
          nlinarith [hle, hmem.1]
        exact le_antisymm hLle hmem.1
      have hσ : f y₁.1 - c + ε = -η := by
        have hy2 : f y₁.1 ≤ c + r ^ 2 / 2 := y₁.2
        have hσmem : f y₁.1 - c + ε ∈ Set.Icc (-η) (r ^ 2 / 2 + ε) := by
          constructor
          · linarith [hznonlow]
          · linarith [hy2]
        by_contra hnot
        have hlt : -η < f y₁.1 - c + ε := lt_of_not_ge (by
          intro hge
          have hlow : -η ≤ f y₁.1 - c + ε := by linarith [hznonlow]
          exact hnot (le_antisymm hge hlow))
        have hmono := morseCollarLevelMap_injective_of_level hk c ε r η data hε hη
          (⟨curveAt v hcomplete y₁.1 (f y₁.1 - c + ε), by
            exact (morseCollarFlow_levelValue (I := I) f c ε r η hε (le_of_lt hη) hf v hv hsupp hdfOn hrate (by
              constructor
              · exact le_of_lt hznonlow
              · exact y₁.2))⟩) (f y₁.1 - c + ε) (-η)
          hσmem (by
            have hy2' : f y₁.1 ≤ c + r ^ 2 / 2 := y₁.2
            constructor <;> linarith)
        have hL' : morseCollarLevelMap hk c ε r η data
            (⟨curveAt v hcomplete y₁.1 (f y₁.1 - c + ε), by
              exact (morseCollarFlow_levelValue (I := I) f c ε r η hε (le_of_lt hη) hf v hv hsupp hdfOn hrate (by
                constructor
                · exact le_of_lt hznonlow
                · exact y₁.2))⟩) (f y₁.1 - c + ε) ≠ -η := by
          intro heq
          have hbnd : morseCollarLevelMap hk c ε r η data
              (⟨curveAt v hcomplete y₁.1 (f y₁.1 - c + ε), by
                exact (morseCollarFlow_levelValue (I := I) f c ε r η hε (le_of_lt hη) hf v hv hsupp hdfOn hrate (by
                  constructor
                  · exact le_of_lt hznonlow
                  · exact y₁.2))⟩) (-η) = -η :=
            morseCollarLevelMap_boundary hk c ε r η data _
          have hσeq : f y₁.1 - c + ε = -η := hmono (heq.trans hbnd.symm)
          exact hnot hσeq
        exact hL' hL
      have hy : y₁.1 = y₂.1 := by
        have hmap₁ : morseCollarMap hk c ε r η data hf hε (le_of_lt hη) v hv hsupp hdfOn hrate y₁ =
            curveAt v hcomplete y₁.1
              (f y₁.1 - c + ε - morseCollarLevelMap hk c ε r η data
                (⟨curveAt v hcomplete y₁.1 (f y₁.1 - c + ε), by
                  exact (morseCollarFlow_levelValue (I := I) f c ε r η hε (le_of_lt hη) hf v hv hsupp hdfOn hrate (by
                    constructor
                    · exact le_of_lt hznonlow
                    · exact y₁.2))⟩) (f y₁.1 - c + ε)) :=
          morseCollarMap_of_strip hk c ε r η data hf hε (le_of_lt hη) v hv hsupp hdfOn hrate y₁ (le_of_lt hznonlow)
        have hmap₂ : morseCollarMap hk c ε r η data hf hε (le_of_lt hη) v hv hsupp hdfOn hrate y₂ = y₂.1 :=
          morseCollarMap_of_low hk c ε r η data hf hε (le_of_lt hη) v hv hsupp hdfOn hrate y₂ h₂
        have hmain : curveAt v hcomplete y₁.1
            (f y₁.1 - c + ε - morseCollarLevelMap hk c ε r η data
              (⟨curveAt v hcomplete y₁.1 (f y₁.1 - c + ε), by
                exact (morseCollarFlow_levelValue (I := I) f c ε r η hε (le_of_lt hη) hf v hv hsupp hdfOn hrate (by
                  constructor
                  · exact le_of_lt hznonlow
                  · exact y₁.2))⟩) (f y₁.1 - c + ε)) = y₂.1 :=
          hmap₁.symm.trans (h'.symm.trans hmap₂)
        have htime : f y₁.1 - c + ε - morseCollarLevelMap hk c ε r η data
            (⟨curveAt v hcomplete y₁.1 (f y₁.1 - c + ε), by
              exact (morseCollarFlow_levelValue (I := I) f c ε r η hε (le_of_lt hη) hf v hv hsupp hdfOn hrate (by
                constructor
                · exact le_of_lt hznonlow
                · exact y₁.2))⟩) (f y₁.1 - c + ε) = 0 := by
          dsimp [morseCollarLevelMap]
          have hσ0 : f y₁.1 - c + ε + η = 0 := by linarith [hσ]
          simp [hσ]
        rw [htime] at hmain
        rw [curveAt_zero] at hmain
        exact hmain
      exact hy
    · -- both strip: the orbit argument
      have h₁' : c - ε - η < f y₁.1 := lt_of_not_ge h₁
      have h₂' : c - ε - η < f y₂.1 := lt_of_not_ge h₂
      let σ₁ : ℝ := f y₁.1 - c + ε
      let σ₂ : ℝ := f y₂.1 - c + ε
      let x₁ : LevelSetSpace f (c - ε) := ⟨curveAt v hcomplete y₁.1 σ₁, by
        exact (morseCollarFlow_levelValue (I := I) f c ε r η hε (le_of_lt hη) hf v hv hsupp hdfOn hrate (by
          constructor
          · exact le_of_lt h₁'
          · exact y₁.2))⟩
      let x₂ : LevelSetSpace f (c - ε) := ⟨curveAt v hcomplete y₂.1 σ₂, by
        exact (morseCollarFlow_levelValue (I := I) f c ε r η hε (le_of_lt hη) hf v hv hsupp hdfOn hrate (by
          constructor
          · exact le_of_lt h₂'
          · exact y₂.2))⟩
      let L₁ : ℝ := morseCollarLevelMap hk c ε r η data x₁ σ₁
      let L₂ : ℝ := morseCollarLevelMap hk c ε r η data x₂ σ₂
      have hz : f (morseCollarMap hk c ε r η data hf hε (le_of_lt hη) v hv hsupp hdfOn hrate y₁) =
          c - ε + L₁ := by
        simpa [σ₁, x₁, L₁] using (morseCollarMap_value hk c ε r η data hf hε hη v hv hsupp hdfOn hrate y₁ (le_of_lt h₁'))
      have hz' : f (morseCollarMap hk c ε r η data hf hε (le_of_lt hη) v hv hsupp hdfOn hrate y₂) =
          c - ε + L₂ := by
        simpa [σ₂, x₂, L₂] using (morseCollarMap_value hk c ε r η data hf hε hη v hv hsupp hdfOn hrate y₂ (le_of_lt h₂'))
      have hL : L₁ = L₂ := by
        have hfz : f (morseCollarMap hk c ε r η data hf hε (le_of_lt hη) v hv hsupp hdfOn hrate y₁) =
            f (morseCollarMap hk c ε r η data hf hε (le_of_lt hη) v hv hsupp hdfOn hrate y₂) := congrArg f h
        nlinarith [hz, hz', hfz]
      have hmap₁ : morseCollarMap hk c ε r η data hf hε (le_of_lt hη) v hv hsupp hdfOn hrate y₁ =
          curveAt v hcomplete y₁.1 (σ₁ - L₁) := by
        simpa [σ₁, x₁, L₁] using (morseCollarMap_of_strip hk c ε r η data hf hε (le_of_lt hη) v hv hsupp hdfOn hrate y₁ (le_of_lt h₁'))
      have hmap₂ : morseCollarMap hk c ε r η data hf hε (le_of_lt hη) v hv hsupp hdfOn hrate y₂ =
          curveAt v hcomplete y₂.1 (σ₂ - L₂) := by
        simpa [σ₂, x₂, L₂] using (morseCollarMap_of_strip hk c ε r η data hf hε (le_of_lt hη) v hv hsupp hdfOn hrate y₂ (le_of_lt h₂'))
      let z : M := morseCollarMap hk c ε r η data hf hε (le_of_lt hη) v hv hsupp hdfOn hrate y₁
      have hz₁ : curveAt v hcomplete y₁.1 (σ₁ - L₁) = z := by
        rw [← hmap₁]
      have hz₂ : curveAt v hcomplete y₂.1 (σ₂ - L₂) = z := by
        exact hmap₂.symm.trans h.symm
      have hbase : x₁.1 = x₂.1 := by
        have hy₁inv : y₁.1 = curveAt v hcomplete z (L₁ - σ₁) := by
          have hh := curveAt_add v hv1 hcomplete y₁.1 (σ₁ - L₁) (L₁ - σ₁)
          have hsum : (σ₁ - L₁) + (L₁ - σ₁) = 0 := by ring
          rw [hsum] at hh
          rw [hz₁] at hh
          simpa [curveAt_zero v hcomplete y₁.1] using hh
        have hy₂inv : y₂.1 = curveAt v hcomplete z (L₂ - σ₂) := by
          have hh := curveAt_add v hv1 hcomplete y₂.1 (σ₂ - L₂) (L₂ - σ₂)
          have hsum : (σ₂ - L₂) + (L₂ - σ₂) = 0 := by ring
          rw [hsum] at hh
          rw [hz₂] at hh
          simpa [curveAt_zero v hcomplete y₂.1] using hh
        have hx₁ : curveAt v hcomplete y₁.1 σ₁ = curveAt v hcomplete z L₁ := by
          have hh := curveAt_add v hv1 hcomplete z (L₁ - σ₁) σ₁
          have hsum : (L₁ - σ₁) + σ₁ = L₁ := by ring
          rw [hsum] at hh
          rw [← hy₁inv] at hh
          exact hh.symm
        have hx₂ : curveAt v hcomplete y₂.1 σ₂ = curveAt v hcomplete z L₂ := by
          have hh := curveAt_add v hv1 hcomplete z (L₂ - σ₂) σ₂
          have hsum : (L₂ - σ₂) + σ₂ = L₂ := by ring
          rw [hsum] at hh
          rw [← hy₂inv] at hh
          exact hh.symm
        have hx₁' : curveAt v hcomplete y₁.1 σ₁ = curveAt v hcomplete z L₂ := by
          rw [hL] at hx₁
          exact hx₁
        change curveAt v hcomplete y₁.1 σ₁ = curveAt v hcomplete y₂.1 σ₂
        exact hx₁'.trans hx₂.symm
      have hx : x₁ = x₂ := by
        apply Subtype.ext
        exact hbase
      have hσeq : σ₁ = σ₂ := by
        have hσ₁mem : σ₁ ∈ Set.Icc (-η) (r ^ 2 / 2 + ε) := by
          dsimp [σ₁]
          have hy2₁ : f y₁.1 ≤ c + r ^ 2 / 2 := y₁.2
          constructor
          · linarith [h₁']
          · linarith [hy2₁]
        have hσ₂mem : σ₂ ∈ Set.Icc (-η) (r ^ 2 / 2 + ε) := by
          dsimp [σ₂]
          have hy2₂ : f y₂.1 ≤ c + r ^ 2 / 2 := y₂.2
          constructor
          · linarith [h₂']
          · linarith [hy2₂]
        have hLL : morseCollarLevelMap hk c ε r η data x₁ σ₁ = morseCollarLevelMap hk c ε r η data x₁ σ₂ := by
          dsimp [L₁, L₂] at hL
          rw [← hx] at hL
          exact hL
        exact morseCollarLevelMap_injective_of_level hk c ε r η data hε hη x₁ σ₁ σ₂ hσ₁mem hσ₂mem hLL
      have hy : y₁.1 = y₂.1 := by
        have hy₁inv : y₁.1 = curveAt v hcomplete z (L₁ - σ₁) := by
          have hh := curveAt_add v hv1 hcomplete y₁.1 (σ₁ - L₁) (L₁ - σ₁)
          have hsum : (σ₁ - L₁) + (L₁ - σ₁) = 0 := by ring
          rw [hsum] at hh
          rw [hz₁] at hh
          simpa [curveAt_zero v hcomplete y₁.1] using hh
        have hy₂inv : y₂.1 = curveAt v hcomplete z (L₂ - σ₂) := by
          have hh := curveAt_add v hv1 hcomplete y₂.1 (σ₂ - L₂) (L₂ - σ₂)
          have hsum : (σ₂ - L₂) + (L₂ - σ₂) = 0 := by ring
          rw [hsum] at hh
          rw [hz₂] at hh
          simpa [curveAt_zero v hcomplete y₂.1] using hh
        rw [hy₁inv, hy₂inv, hL, hσeq]
      apply Subtype.ext
      exact hy

theorem continuous_morseCollarMap {m k : ℕ} (hk : k ≤ m + 1) (c ε r η : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} [I.Boundaryless]
    [IsManifold I (⊤ : WithTop ℕ∞) M] {f : M → ℝ}
    {f₀ : M → ℝ} (data : MorseChart (m + 1) k hk c I f₀)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) f)
    (hε : 0 < ε) (hη : 0 < η)
    (hTopCont : Continuous (morseCollarTopLevel hk c ε r data : LevelSetSpace f (c - ε) → ℝ))
    (v : (x : M) → TangentSpace I x)
    (hv : ContMDiff I (I.prod 𝓘(ℝ, MorseModel (m + 1))) ∞
      (fun x : M => (⟨x, v x⟩ : TangentBundle I M)))
    (hsupp : IsCompact (tsupport v))
    (hdfOn : ∀ x ∈ f ⁻¹' Set.Icc (c - ε - η) (c + r ^ 2 / 2),
      (NormedSpace.fromTangentSpace (f x)) ((mfderiv I 𝓘(ℝ, ℝ) f x) (v x)) = -1)
    (hrate : ∀ x,
      -1 ≤ (NormedSpace.fromTangentSpace (f x)) ((mfderiv I 𝓘(ℝ, ℝ) f x) (v x)) ∧
      (NormedSpace.fromTangentSpace (f x)) ((mfderiv I 𝓘(ℝ, ℝ) f x) (v x)) ≤ 0) :
    Continuous (morseCollarMap hk c ε r η data hf hε (le_of_lt hη) v hv hsupp hdfOn hrate) := by
  let hcomplete : ∀ x : M, ∃ γ : ℝ → M, γ 0 = x ∧ IsMIntegralCurve γ v :=
    exists_globalIntegralCurve_of_compactSupport v hv hsupp
  have hv1 : ContMDiff I (I.prod 𝓘(ℝ, MorseModel (m + 1))) (1 : WithTop ℕ∞)
      (fun x : M => (⟨x, v x⟩ : TangentBundle I M)) :=
    hv.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ ∞)
  let S₁ : Set (SublevelSpace f (c + r ^ 2 / 2)) :=
    {y : SublevelSpace f (c + r ^ 2 / 2) | f y.1 ≤ c - ε - η}
  let S₂ : Set (SublevelSpace f (c + r ^ 2 / 2)) :=
    {y : SublevelSpace f (c + r ^ 2 / 2) | c - ε - η ≤ f y.1}
  have hclosed₁ : IsClosed S₁ := by
    dsimp [S₁]
    exact IsClosed.preimage (hf.continuous.comp continuous_subtype_val) (isClosed_Iic (a := c - ε - η))
  have hclosed₂ : IsClosed S₂ := by
    dsimp [S₂]
    exact IsClosed.preimage (hf.continuous.comp continuous_subtype_val) (isClosed_Ici (a := c - ε - η))
  have hσ : Continuous (fun y : SublevelSpace f (c + r ^ 2 / 2) => f y.1 - c + ε) := by
    simpa [sub_eq_add_neg, neg_sub, add_assoc, add_comm, add_left_comm] using
      ((hf.continuous.comp continuous_subtype_val).sub
        (continuous_const : Continuous (fun _ : SublevelSpace f (c + r ^ 2 / 2) => c - ε)))
  have hxmain : Continuous (fun y : SublevelSpace f (c + r ^ 2 / 2) =>
      curveAt v hcomplete y.1 (f y.1 - c + ε)) := by
    have hjoint : Continuous (fun p : ℝ × M => curveAt v hcomplete p.2 p.1) :=
      (contMDiff_globalFlow_joint_of_compactSupport v hv hsupp).continuous
    have hpair : Continuous (fun y : SublevelSpace f (c + r ^ 2 / 2) =>
        (f y.1 - c + ε, y.1)) :=
      hσ.prodMk continuous_subtype_val
    exact hjoint.comp hpair
  let g : S₂ → LevelSetSpace f (c - ε) :=
    fun y => ⟨curveAt v hcomplete y.1.1 (f y.1.1 - c + ε), by
      exact (morseCollarFlow_levelValue (I := I) f c ε r η hε (le_of_lt hη) hf v hv hsupp hdfOn hrate (by
        constructor
        · exact y.2
        · exact y.1.2))⟩
  have hg : Continuous g := by
    dsimp [g]
    exact Continuous.subtype_mk (hxmain.comp continuous_subtype_val) (fun y => by
      exact (morseCollarFlow_levelValue (I := I) f c ε r η hε (le_of_lt hη) hf v hv hsupp hdfOn hrate (by
        constructor
        · exact y.2
        · exact y.1.2)))
  have hσS₂ : Continuous (fun y : S₂ => f y.1.1 - c + ε) :=
    hσ.comp continuous_subtype_val
  have hLmain : Continuous (fun y : S₂ =>
      morseCollarLevelMap hk c ε r η data (g y) (f y.1.1 - c + ε)) := by
    have hinner : Continuous (fun y : S₂ => (g y, f y.1.1 - c + ε)) := hg.prodMk hσS₂
    exact (continuous_morseCollarLevelMap hk c ε r η data hε hη hTopCont).comp hinner
  have hflowFormula : Continuous (fun y : S₂ =>
      curveAt v hcomplete y.1.1
        (f y.1.1 - c + ε - morseCollarLevelMap hk c ε r η data (g y) (f y.1.1 - c + ε))) := by
    have hjoint : Continuous (fun p : ℝ × M => curveAt v hcomplete p.2 p.1) :=
      (contMDiff_globalFlow_joint_of_compactSupport v hv hsupp).continuous
    have htime : Continuous (fun y : S₂ =>
        f y.1.1 - c + ε - morseCollarLevelMap hk c ε r η data (g y) (f y.1.1 - c + ε)) :=
      hσS₂.sub hLmain
    have hpair : Continuous (fun y : S₂ =>
        (f y.1.1 - c + ε - morseCollarLevelMap hk c ε r η data (g y) (f y.1.1 - c + ε), y.1.1)) :=
      htime.prodMk (continuous_subtype_val.comp continuous_subtype_val)
    exact hjoint.comp hpair
  have hflowOn : ContinuousOn (morseCollarMap hk c ε r η data hf hε (le_of_lt hη) v hv hsupp hdfOn hrate) S₂ := by
    rw [continuousOn_iff_continuous_restrict]
    exact continuousOn_univ.mp (by
      refine (continuousOn_congr (s := Set.univ)
        (f := fun y : S₂ => curveAt v hcomplete y.1.1
          (f y.1.1 - c + ε - morseCollarLevelMap hk c ε r η data (g y) (f y.1.1 - c + ε)))
        (g := fun y : S₂ => morseCollarMap hk c ε r η data hf hε (le_of_lt hη) v hv hsupp hdfOn hrate
          (y : SublevelSpace f (c + r ^ 2 / 2))) ?_).mpr hflowFormula.continuousOn
      intro y hy
      exact (morseCollarMap_of_strip hk c ε r η data hf hε (le_of_lt hη) v hv hsupp hdfOn hrate
        (y : SublevelSpace f (c + r ^ 2 / 2)) y.2))
  have hidOn : ContinuousOn (morseCollarMap hk c ε r η data hf hε (le_of_lt hη) v hv hsupp hdfOn hrate) S₁ := by
    exact (continuous_subtype_val.continuousOn.congr (s := S₁)
      (g := (morseCollarMap hk c ε r η data hf hε (le_of_lt hη) v hv hsupp hdfOn hrate)))
      (fun y hy => (morseCollarMap_of_low hk c ε r η data hf hε (le_of_lt hη) v hv hsupp hdfOn hrate
        (y : SublevelSpace f (c + r ^ 2 / 2)) hy))
  have hunion : Set.univ = S₁ ∪ S₂ := by
    ext y
    simpa [S₁, S₂, sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using
      (le_total (f y.1) (c - ε - η))
  exact continuousOn_univ.mp (by
    rw [hunion]
    exact hidOn.union_of_isClosed hflowOn hclosed₁ hclosed₂)

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

theorem cocoreAttachingEmbedding_core_eq_cellAttachingMap {n k : ℕ} (hk : k ≤ n) (c r : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ (MorseModel n) H} {f : M → ℝ}
    (data : MorseChart n k hk c I f)
    (hεr : Real.sqrt (2 * data.ε + 2 * r ^ 2) ≤ data.R)
    (b : CellBoundary k) :
    (cocoreAttachingEmbedding hk c data.ε r data (data.hεpos) hεr
        (b, (⟨(0 : EuclideanSpace ℝ (Fin (n - k))), by simp⟩ : ClosedCell (n - k)))).1 =
      (cellAttachingMap hk c data b).1 := by
  dsimp [cocoreAttachingEmbedding, cellAttachingMap]
  congr 1
  exact cocoreModelPoint_core_eq hk data.ε r b

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

theorem range_handleEmbedding {m k : ℕ} (hk : k ≤ m + 1) (c ε r : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H}
    {f₀ : M → ℝ} (data : MorseChart (m + 1) k hk c I f₀)
    (hε : 0 < ε) (hr : 0 < r) :
    Set.range (handleEmbedding hk c ε r data) =
      data.χ '' (modelHandle hk ε r : Set (MorseModel (m + 1))) := by
  change Set.range (data.χ ∘ modelHandleMap hk ε r) =
    data.χ '' (modelHandle hk ε r : Set (MorseModel (m + 1)))
  rw [Set.range_comp]
  rw [modelHandleMap_range hk ε r hε hr]

noncomputable def morseCollarLevelMapInv {m k : ℕ} (hk : k ≤ m + 1) (c ε r η : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} {f : M → ℝ}
    {f₀ : M → ℝ} (data : MorseChart (m + 1) k hk c I f₀)
    (x : LevelSetSpace f (c - ε)) (t : ℝ) : ℝ :=
  -η + (t + η) * (r ^ 2 / 2 + ε + η) / (morseCollarTopLevel hk c ε r data x + η)

theorem morseCollarLevelMapInv_mem {m k : ℕ} (hk : k ≤ m + 1) (c ε r η : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} {f : M → ℝ}
    {f₀ : M → ℝ} (data : MorseChart (m + 1) k hk c I f₀)
    (hε : 0 < ε) (hη : 0 < η)
    (x : LevelSetSpace f (c - ε)) (t : ℝ)
    (ht : t ∈ Set.Icc (-η) (morseCollarTopLevel hk c ε r data x)) :
    morseCollarLevelMapInv hk c ε r η data x t ∈ Set.Icc (-η) (r ^ 2 / 2 + ε) := by
  have hT : 0 ≤ morseCollarTopLevel hk c ε r data x :=
    morseCollarTopLevel_nonneg hk c ε r data x
  have hTη : 0 < morseCollarTopLevel hk c ε r data x + η := by nlinarith [hT, hη]
  have hden : 0 < r ^ 2 / 2 + ε + η := by positivity
  constructor
  · dsimp [morseCollarLevelMapInv]
    have h1 : 0 ≤ (t + η) * (r ^ 2 / 2 + ε + η) / (morseCollarTopLevel hk c ε r data x + η) := by
      have h1' : 0 ≤ t + η := by nlinarith [ht.1, hη]
      exact div_nonneg (mul_nonneg h1' (le_of_lt hden)) (le_of_lt hTη)
    nlinarith
  · dsimp [morseCollarLevelMapInv]
    have h1 : t ≤ morseCollarTopLevel hk c ε r data x := ht.2
    have hTle : morseCollarTopLevel hk c ε r data x ≤ r ^ 2 / 2 :=
      morseCollarTopLevel_le hk c ε r data x
    have hnum : (t + η) * (r ^ 2 / 2 + ε + η) ≤
        (morseCollarTopLevel hk c ε r data x + η) * (r ^ 2 / 2 + ε + η) := by
      have h1' : t + η ≤ morseCollarTopLevel hk c ε r data x + η := by nlinarith [h1, hη]
      exact mul_le_mul_of_nonneg_right h1' (le_of_lt hden)
    have hdiv : (t + η) * (r ^ 2 / 2 + ε + η) / (morseCollarTopLevel hk c ε r data x + η) ≤
        r ^ 2 / 2 + ε + η := by
      exact (div_le_iff₀ hTη).mpr (by nlinarith [hnum])
    nlinarith [hdiv]

theorem morseCollarLevelMapInv_levelMap {m k : ℕ} (hk : k ≤ m + 1) (c ε r η : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} {f : M → ℝ}
    {f₀ : M → ℝ} (data : MorseChart (m + 1) k hk c I f₀)
    (hε : 0 < ε) (hη : 0 < η) (x : LevelSetSpace f (c - ε)) (t : ℝ) :
    morseCollarLevelMap hk c ε r η data x (morseCollarLevelMapInv hk c ε r η data x t) = t := by
  dsimp [morseCollarLevelMap, morseCollarLevelMapInv]
  have hT : 0 ≤ morseCollarTopLevel hk c ε r data x :=
    morseCollarTopLevel_nonneg hk c ε r data x
  have hTη : morseCollarTopLevel hk c ε r data x + η ≠ 0 := by positivity
  have hden : r ^ 2 / 2 + ε + η ≠ 0 := by positivity
  field_simp [hTη, hden]
  ring

theorem continuous_morseCollarLevelMapInv {m k : ℕ} (hk : k ≤ m + 1) (c ε r η : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} {f : M → ℝ}
    {f₀ : M → ℝ} (data : MorseChart (m + 1) k hk c I f₀)
    (hη : 0 < η)
    (hTopCont : Continuous (morseCollarTopLevel hk c ε r data : LevelSetSpace f (c - ε) → ℝ)) :
    Continuous (fun p : LevelSetSpace f (c - ε) × ℝ =>
      morseCollarLevelMapInv hk c ε r η data p.1 p.2) := by
  dsimp [morseCollarLevelMapInv]
  have hT : Continuous (fun p : LevelSetSpace f (c - ε) × ℝ =>
      morseCollarTopLevel hk c ε r data p.1) :=
    hTopCont.comp continuous_fst
  have hden : ∀ p : LevelSetSpace f (c - ε) × ℝ,
      morseCollarTopLevel hk c ε r data p.1 + η ≠ 0 := by
    intro p
    have hTp : 0 ≤ morseCollarTopLevel hk c ε r data p.1 :=
      morseCollarTopLevel_nonneg hk c ε r data p.1
    positivity
  have hnum : Continuous (fun p : LevelSetSpace f (c - ε) × ℝ =>
      (p.2 + η) * (r ^ 2 / 2 + ε + η)) := by
    fun_prop
  have hmain : Continuous (fun p : LevelSetSpace f (c - ε) × ℝ =>
      (p.2 + η) * (r ^ 2 / 2 + ε + η) / (morseCollarTopLevel hk c ε r data p.1 + η)) := by
    exact hnum.div (hT.add continuous_const) hden
  simpa [add_comm] using hmain.const_add (-η)

theorem morseCollarMap_flow_eq {m k : ℕ} (hk : k ≤ m + 1) (c ε r η : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} [I.Boundaryless]
    [IsManifold I (⊤ : WithTop ℕ∞) M] {f : M → ℝ}
    {f₀ : M → ℝ} (data : MorseChart (m + 1) k hk c I f₀)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) f)
    (hε : 0 < ε) (hη : 0 < η)
    (v : (x : M) → TangentSpace I x)
    (hv : ContMDiff I (I.prod 𝓘(ℝ, MorseModel (m + 1))) ∞
      (fun x : M => (⟨x, v x⟩ : TangentBundle I M)))
    (hsupp : IsCompact (tsupport v))
    (hdfOn : ∀ x ∈ f ⁻¹' Set.Icc (c - ε - η) (c + r ^ 2 / 2),
      (NormedSpace.fromTangentSpace (f x)) ((mfderiv I 𝓘(ℝ, ℝ) f x) (v x)) = -1)
    (hrate : ∀ x,
      -1 ≤ (NormedSpace.fromTangentSpace (f x)) ((mfderiv I 𝓘(ℝ, ℝ) f x) (v x)) ∧
      (NormedSpace.fromTangentSpace (f x)) ((mfderiv I 𝓘(ℝ, ℝ) f x) (v x)) ≤ 0)
    (x : LevelSetSpace f (c - ε)) (σ σ' : ℝ)
    (hσmem : σ ∈ Set.Icc (-η) (r ^ 2 / 2 + ε))
    (hσeq : morseCollarLevelMap hk c ε r η data x σ = σ')
    (y : SublevelSpace f (c + r ^ 2 / 2))
    (hy : c - ε - η ≤ f y.1)
    (hyx : y.1 = curveAt v (exists_globalIntegralCurve_of_compactSupport v hv hsupp) x.1 (-σ))
    (z : M)
    (hzx : curveAt v (exists_globalIntegralCurve_of_compactSupport v hv hsupp) x.1 (-σ') = z) :
    morseCollarMap hk c ε r η data hf hε (le_of_lt hη) v hv hsupp hdfOn hrate y = z := by
  let hcomplete : ∀ x : M, ∃ γ : ℝ → M, γ 0 = x ∧ IsMIntegralCurve γ v :=
    exists_globalIntegralCurve_of_compactSupport v hv hsupp
  have hv1 : ContMDiff I (I.prod 𝓘(ℝ, MorseModel (m + 1))) (1 : WithTop ℕ∞)
      (fun x : M => (⟨x, v x⟩ : TangentBundle I M)) :=
    hv.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ ∞)
  have hx : f x.1 = c - ε := x.2
  have hx' : f x.1 ∈ Set.Icc (c - ε - η) (c + r ^ 2 / 2) := by
    constructor
    · nlinarith [hx, hη]
    · nlinarith [hx, hε, hη]
  have hval : f (curveAt v hcomplete x.1 (-σ)) = c - ε + σ := by
    have hval0 : f (curveAt v hcomplete x.1 (-σ)) = f x.1 - (-σ) :=
      morseCollarFlow_valueOnStrip (I := I) f c ε r η hf v hv hsupp hdfOn hrate hx'
        (by linarith [hx, hσmem.2]) (by linarith [hx, hσmem.1])
    rw [hx] at hval0
    simpa [sub_neg_eq_add] using hval0
  have hfval : f (curveAt v hcomplete x.1 (-σ)) = c - ε + σ := hval
  have hmap' := morseCollarMap_of_strip hk c ε r η data hf hε (le_of_lt hη) v hv hsupp hdfOn hrate y hy
  have hxeq : ⟨curveAt v hcomplete y.1 (f y.1 - c + ε), by
      exact (morseCollarFlow_levelValue (I := I) f c ε r η hε (le_of_lt hη) hf v hv hsupp hdfOn hrate (by
        constructor
        · exact hy
        · exact y.2))⟩ = x := by
    apply Subtype.ext
    change curveAt v hcomplete y.1 (f y.1 - c + ε) = x.1
    rw [hyx, hfval]
    have htime_arg : c - ε + σ - c + ε = σ := by ring
    rw [htime_arg]
    have hstep : curveAt v hcomplete (curveAt v hcomplete x.1 (-σ)) σ = curveAt v hcomplete x.1 0 := by
      have hh := curveAt_add v hv1 hcomplete x.1 (-σ) σ
      have hsum : -σ + σ = 0 := by ring
      rw [hsum] at hh
      exact hh.symm
    rw [hstep]
    exact curveAt_zero v hcomplete x.1
  have hfσ : f y.1 - c + ε = σ := by
    rw [hyx, hfval]
    ring
  have hL : morseCollarLevelMap hk c ε r η data
      (⟨curveAt v hcomplete y.1 (f y.1 - c + ε), by
        exact (morseCollarFlow_levelValue (I := I) f c ε r η hε (le_of_lt hη) hf v hv hsupp hdfOn hrate (by
          constructor
          · exact hy
          · exact y.2))⟩) (f y.1 - c + ε) = σ' := by
    rw [hxeq]
    rw [hfσ]
    exact hσeq
  have htime : f y.1 - c + ε - morseCollarLevelMap hk c ε r η data
      (⟨curveAt v hcomplete y.1 (f y.1 - c + ε), by
        exact (morseCollarFlow_levelValue (I := I) f c ε r η hε (le_of_lt hη) hf v hv hsupp hdfOn hrate (by
          constructor
          · exact hy
          · exact y.2))⟩) (f y.1 - c + ε) = σ - σ' := by
    conv_lhs =>
      congr
      · rw [hfσ]
      · rw [hL]
  have hflow : curveAt v hcomplete y.1 (σ - σ') = z := by
    rw [hyx]
    have hh := curveAt_add v hv1 hcomplete x.1 (-σ) (σ - σ')
    have hsum : -σ + (σ - σ') = -σ' := by ring
    rw [hsum] at hh
    rw [← hh]
    exact hzx
  rw [hmap']
  change curveAt v hcomplete y.1 (f y.1 - c + ε - morseCollarLevelMap hk c ε r η data
    (⟨curveAt v hcomplete y.1 (f y.1 - c + ε), by
      exact (morseCollarFlow_levelValue (I := I) f c ε r η hε (le_of_lt hη) hf v hv hsupp hdfOn hrate (by
        constructor
        · exact hy
        · exact y.2))⟩) (f y.1 - c + ε)) = z
  rw [htime]
  exact hflow

theorem morseCollarMap_surj_on_union {m k : ℕ} (hk : k ≤ m + 1) (c ε r η : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} [I.Boundaryless]
    [IsManifold I (⊤ : WithTop ℕ∞) M] {f : M → ℝ}
    {f₀ : M → ℝ} (data : MorseChart (m + 1) k hk c I f₀)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) f)
    (hε : 0 < ε) (hη : 0 < η)
    (v : (x : M) → TangentSpace I x)
    (hv : ContMDiff I (I.prod 𝓘(ℝ, MorseModel (m + 1))) ∞
      (fun x : M => (⟨x, v x⟩ : TangentBundle I M)))
    (hsupp : IsCompact (tsupport v))
    (hdfOn : ∀ x ∈ f ⁻¹' Set.Icc (c - ε - η) (c + r ^ 2 / 2),
      (NormedSpace.fromTangentSpace (f x)) ((mfderiv I 𝓘(ℝ, ℝ) f x) (v x)) = -1)
    (hrate : ∀ x,
      -1 ≤ (NormedSpace.fromTangentSpace (f x)) ((mfderiv I 𝓘(ℝ, ℝ) f x) (v x)) ∧
      (NormedSpace.fromTangentSpace (f x)) ((mfderiv I 𝓘(ℝ, ℝ) f x) (v x)) ≤ 0)
    (hHandleInterval : ∀ (w : MorseModel (m + 1)), w ∈ modelHandle hk ε r → f (data.χ w) ∈ Set.Icc (c - ε - η) (c + r ^ 2 / 2))
    (hHandleUpper : ∀ (w : MorseModel (m + 1)), w ∈ modelHandle hk ε r → f (data.χ w) ≤ c + r ^ 2 / 2)
    (hflowTop : ∀ (w : MorseModel (m + 1)) (hw : w ∈ modelHandle hk ε r),
      morseCollarTopLevel hk c ε r data
        (morseCollarFlowBase hk c ε r η hf hε hη v hv hsupp hdfOn hrate (data.χ w)
          (hHandleInterval w hw)) ≥
        f (data.χ w) - c + ε)
    (z : {x : M // x ∈ sublevel f (c - ε) ∪ Set.range (handleEmbedding hk c ε r data)}) :
    ∃ y : SublevelSpace f (c + r ^ 2 / 2),
      morseCollarMap hk c ε r η data hf hε (le_of_lt hη) v hv hsupp hdfOn hrate y = z.1 := by
  exact morseCollarMap_surj_on_image hk c ε r η data hf hε hη v hv hsupp hdfOn hrate hHandleInterval hHandleUpper hflowTop
    z.1 (by
      rcases z.2 with hlow | hcell
      · exact Or.inl hlow
      · rcases hcell with ⟨d, hd⟩
        refine Or.inr ⟨modelHandleMap hk ε r d,
          modelHandleMap_mem hk ε r (le_of_lt hε) d, ?_⟩
        rw [← hd]
        rfl)

noncomputable def morseCollarPreimageStrip {m k : ℕ} (hk : k ≤ m + 1) (c ε r η : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} [I.Boundaryless]
    [IsManifold I (⊤ : WithTop ℕ∞) M] {f : M → ℝ}
    {f₀ : M → ℝ} (data : MorseChart (m + 1) k hk c I f₀)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) f)
    (hε : 0 < ε) (hη : 0 < η)
    (v : (x : M) → TangentSpace I x)
    (hv : ContMDiff I (I.prod 𝓘(ℝ, MorseModel (m + 1))) ∞
      (fun x : M => (⟨x, v x⟩ : TangentBundle I M)))
    (hsupp : IsCompact (tsupport v))
    (hdfOn : ∀ x ∈ f ⁻¹' Set.Icc (c - ε - η) (c + r ^ 2 / 2),
      (NormedSpace.fromTangentSpace (f x)) ((mfderiv I 𝓘(ℝ, ℝ) f x) (v x)) = -1)
    (hrate : ∀ x,
      -1 ≤ (NormedSpace.fromTangentSpace (f x)) ((mfderiv I 𝓘(ℝ, ℝ) f x) (v x)) ∧
      (NormedSpace.fromTangentSpace (f x)) ((mfderiv I 𝓘(ℝ, ℝ) f x) (v x)) ≤ 0)
    (hHandleInterval : ∀ (w : MorseModel (m + 1)), w ∈ modelHandle hk ε r → f (data.χ w) ∈ Set.Icc (c - ε - η) (c + r ^ 2 / 2))
    (hHandleUpper : ∀ (w : MorseModel (m + 1)), w ∈ modelHandle hk ε r → f (data.χ w) ≤ c + r ^ 2 / 2)
    (hflowTop : ∀ (w : MorseModel (m + 1)) (hw : w ∈ modelHandle hk ε r),
      morseCollarTopLevel hk c ε r data
        (morseCollarFlowBase hk c ε r η hf hε hη v hv hsupp hdfOn hrate (data.χ w)
          (hHandleInterval w hw)) ≥
        f (data.χ w) - c + ε)
    (z : {x : M // x ∈ sublevel f (c - ε) ∪ Set.range (handleEmbedding hk c ε r data)})
    (hz : c - ε - η ≤ f z.1) : SublevelSpace f (c + r ^ 2 / 2) := by
  let σ' : ℝ := f z.1 - c + ε
  have hsub : f z.1 ≤ c + r ^ 2 / 2 := by
    rcases z.2 with hlow | hcell
    · have hr2 : 0 ≤ r ^ 2 / 2 := div_nonneg (sq_nonneg r) (by norm_num)
      have hlow' : f z.1 ≤ c - ε := by simpa [sublevel] using hlow
      nlinarith [hlow', hε, hr2]
    · rcases hcell with ⟨d, hd⟩
      rw [← hd]
      exact hHandleUpper (modelHandleMap hk ε r d) (modelHandleMap_mem hk ε r (le_of_lt hε) d)
  let x : LevelSetSpace f (c - ε) := morseCollarFlowBase hk c ε r η hf hε hη v hv hsupp hdfOn hrate z.1 (by
    constructor
    · exact hz
    · exact hsub)
  have hT : morseCollarTopLevel hk c ε r data x ≥ σ' := by
    rcases z.2 with hlow | hcell
    · have hlow' : f z.1 ≤ c - ε := by simpa [sublevel] using hlow
      have hσ'le : σ' ≤ 0 := by dsimp [σ']; linarith
      exact le_trans hσ'le (morseCollarTopLevel_nonneg hk c ε r data x)
    · rcases hcell with ⟨d, hd⟩
      have hxeq : x = morseCollarFlowBase hk c ε r η hf hε hη v hv hsupp hdfOn hrate
          (data.χ (modelHandleMap hk ε r d))
          (hHandleInterval (modelHandleMap hk ε r d)
            (modelHandleMap_mem hk ε r (le_of_lt hε) d)) := by
        apply Subtype.ext
        dsimp [x, morseCollarFlowBase]
        rw [← hd]
        rfl
      have hw' : σ' = f (data.χ (modelHandleMap hk ε r d)) - c + ε := by
        dsimp [σ']
        rw [← hd]
        rfl
      rw [hxeq, hw']
      exact hflowTop (modelHandleMap hk ε r d) (modelHandleMap_mem hk ε r (le_of_lt hε) d)
  have hσmem : morseCollarLevelMapInv hk c ε r η data x σ' ∈ Set.Icc (-η) (r ^ 2 / 2 + ε) := by
    exact morseCollarLevelMapInv_mem hk c ε r η data hε hη x σ' (by
      constructor
      · dsimp [σ']
        linarith
      · exact hT)
  let σ : ℝ := morseCollarLevelMapInv hk c ε r η data x σ'
  have hxval : f x.1 = c - ε := x.2
  have hx' : f x.1 ∈ Set.Icc (c - ε - η) (c + r ^ 2 / 2) := by
    constructor
    · nlinarith [hxval, hη]
    · nlinarith [hxval, hε, hη]
  have hval : f (curveAt v (exists_globalIntegralCurve_of_compactSupport v hv hsupp) x.1 (-σ)) =
      c - ε + σ := by
    have hval0 : f (curveAt v (exists_globalIntegralCurve_of_compactSupport v hv hsupp) x.1 (-σ)) =
        f x.1 - (-σ) :=
      morseCollarFlow_valueOnStrip (I := I) f c ε r η hf v hv hsupp hdfOn hrate hx'
        (by linarith [hxval, hσmem.2]) (by linarith [hxval, hσmem.1])
    rw [hxval] at hval0
    simpa [sub_neg_eq_add] using hval0
  refine ⟨curveAt v (exists_globalIntegralCurve_of_compactSupport v hv hsupp) x.1 (-σ), ?_⟩
  change f (curveAt v (exists_globalIntegralCurve_of_compactSupport v hv hsupp) x.1 (-σ)) ≤
    c + r ^ 2 / 2
  dsimp [σ]
  nlinarith [hval, hσmem.2]

noncomputable def morseCollarPreimage {m k : ℕ} (hk : k ≤ m + 1) (c ε r η : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} [I.Boundaryless]
    [IsManifold I (⊤ : WithTop ℕ∞) M] {f : M → ℝ}
    {f₀ : M → ℝ} (data : MorseChart (m + 1) k hk c I f₀)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) f)
    (hε : 0 < ε) (hη : 0 < η)
    (v : (x : M) → TangentSpace I x)
    (hv : ContMDiff I (I.prod 𝓘(ℝ, MorseModel (m + 1))) ∞
      (fun x : M => (⟨x, v x⟩ : TangentBundle I M)))
    (hsupp : IsCompact (tsupport v))
    (hdfOn : ∀ x ∈ f ⁻¹' Set.Icc (c - ε - η) (c + r ^ 2 / 2),
      (NormedSpace.fromTangentSpace (f x)) ((mfderiv I 𝓘(ℝ, ℝ) f x) (v x)) = -1)
    (hrate : ∀ x,
      -1 ≤ (NormedSpace.fromTangentSpace (f x)) ((mfderiv I 𝓘(ℝ, ℝ) f x) (v x)) ∧
      (NormedSpace.fromTangentSpace (f x)) ((mfderiv I 𝓘(ℝ, ℝ) f x) (v x)) ≤ 0)
    (hHandleInterval : ∀ (w : MorseModel (m + 1)), w ∈ modelHandle hk ε r → f (data.χ w) ∈ Set.Icc (c - ε - η) (c + r ^ 2 / 2))
    (hHandleUpper : ∀ (w : MorseModel (m + 1)), w ∈ modelHandle hk ε r → f (data.χ w) ≤ c + r ^ 2 / 2)
    (hflowTop : ∀ (w : MorseModel (m + 1)) (hw : w ∈ modelHandle hk ε r),
      morseCollarTopLevel hk c ε r data
        (morseCollarFlowBase hk c ε r η hf hε hη v hv hsupp hdfOn hrate (data.χ w)
          (hHandleInterval w hw)) ≥
        f (data.χ w) - c + ε)
    (z : {x : M // x ∈ sublevel f (c - ε) ∪ Set.range (handleEmbedding hk c ε r data)}) :
    SublevelSpace f (c + r ^ 2 / 2) :=
  Classical.choose (morseCollarMap_surj_on_union hk c ε r η data hf hε hη v hv hsupp hdfOn hrate
    hHandleInterval hHandleUpper hflowTop z)

theorem morseCollarPreimage_collarMap {m k : ℕ} (hk : k ≤ m + 1) (c ε r η : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} [I.Boundaryless]
    [IsManifold I (⊤ : WithTop ℕ∞) M] {f : M → ℝ}
    {f₀ : M → ℝ} (data : MorseChart (m + 1) k hk c I f₀)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) f)
    (hε : 0 < ε) (hη : 0 < η)
    (v : (x : M) → TangentSpace I x)
    (hv : ContMDiff I (I.prod 𝓘(ℝ, MorseModel (m + 1))) ∞
      (fun x : M => (⟨x, v x⟩ : TangentBundle I M)))
    (hsupp : IsCompact (tsupport v))
    (hdfOn : ∀ x ∈ f ⁻¹' Set.Icc (c - ε - η) (c + r ^ 2 / 2),
      (NormedSpace.fromTangentSpace (f x)) ((mfderiv I 𝓘(ℝ, ℝ) f x) (v x)) = -1)
    (hrate : ∀ x,
      -1 ≤ (NormedSpace.fromTangentSpace (f x)) ((mfderiv I 𝓘(ℝ, ℝ) f x) (v x)) ∧
      (NormedSpace.fromTangentSpace (f x)) ((mfderiv I 𝓘(ℝ, ℝ) f x) (v x)) ≤ 0)
    (hHandleInterval : ∀ (w : MorseModel (m + 1)), w ∈ modelHandle hk ε r → f (data.χ w) ∈ Set.Icc (c - ε - η) (c + r ^ 2 / 2))
    (hHandleUpper : ∀ (w : MorseModel (m + 1)), w ∈ modelHandle hk ε r → f (data.χ w) ≤ c + r ^ 2 / 2)
    (hflowTop : ∀ (w : MorseModel (m + 1)) (hw : w ∈ modelHandle hk ε r),
      morseCollarTopLevel hk c ε r data
        (morseCollarFlowBase hk c ε r η hf hε hη v hv hsupp hdfOn hrate (data.χ w)
          (hHandleInterval w hw)) ≥
        f (data.χ w) - c + ε)
    (z : {x : M // x ∈ sublevel f (c - ε) ∪ Set.range (handleEmbedding hk c ε r data)}) :
    morseCollarMap hk c ε r η data hf hε (le_of_lt hη) v hv hsupp hdfOn hrate
      (morseCollarPreimage hk c ε r η data hf hε hη v hv hsupp hdfOn hrate hHandleInterval hHandleUpper hflowTop z) = z.1 := by
  exact Classical.choose_spec (morseCollarMap_surj_on_union hk c ε r η data hf hε hη v hv hsupp
    hdfOn hrate hHandleInterval hHandleUpper hflowTop z)

theorem morseCollarPreimage_eq_low {m k : ℕ} (hk : k ≤ m + 1) (c ε r η : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} [I.Boundaryless]
    [IsManifold I (⊤ : WithTop ℕ∞) M] {f : M → ℝ}
    {f₀ : M → ℝ} (data : MorseChart (m + 1) k hk c I f₀)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) f)
    (hε : 0 < ε) (hη : 0 < η)
    (v : (x : M) → TangentSpace I x)
    (hv : ContMDiff I (I.prod 𝓘(ℝ, MorseModel (m + 1))) ∞
      (fun x : M => (⟨x, v x⟩ : TangentBundle I M)))
    (hsupp : IsCompact (tsupport v))
    (hdfOn : ∀ x ∈ f ⁻¹' Set.Icc (c - ε - η) (c + r ^ 2 / 2),
      (NormedSpace.fromTangentSpace (f x)) ((mfderiv I 𝓘(ℝ, ℝ) f x) (v x)) = -1)
    (hrate : ∀ x,
      -1 ≤ (NormedSpace.fromTangentSpace (f x)) ((mfderiv I 𝓘(ℝ, ℝ) f x) (v x)) ∧
      (NormedSpace.fromTangentSpace (f x)) ((mfderiv I 𝓘(ℝ, ℝ) f x) (v x)) ≤ 0)
    (hHandleInterval : ∀ (w : MorseModel (m + 1)), w ∈ modelHandle hk ε r → f (data.χ w) ∈ Set.Icc (c - ε - η) (c + r ^ 2 / 2))
    (hHandleUpper : ∀ (w : MorseModel (m + 1)), w ∈ modelHandle hk ε r → f (data.χ w) ≤ c + r ^ 2 / 2)
    (hflowTop : ∀ (w : MorseModel (m + 1)) (hw : w ∈ modelHandle hk ε r),
      morseCollarTopLevel hk c ε r data
        (morseCollarFlowBase hk c ε r η hf hε hη v hv hsupp hdfOn hrate (data.χ w)
          (hHandleInterval w hw)) ≥
        f (data.χ w) - c + ε)
    (z : {x : M // x ∈ sublevel f (c - ε) ∪ Set.range (handleEmbedding hk c ε r data)})
    (hz : f z.1 ≤ c - ε - η) :
    morseCollarPreimage hk c ε r η data hf hε hη v hv hsupp hdfOn hrate hHandleInterval hHandleUpper hflowTop z = ⟨z.1, by
      change f z.1 ≤ c + r ^ 2 / 2
      nlinarith [hz, hε, hη]⟩ := by
  have hmap : morseCollarMap hk c ε r η data hf hε (le_of_lt hη) v hv hsupp hdfOn hrate
      (morseCollarPreimage hk c ε r η data hf hε hη v hv hsupp hdfOn hrate hHandleInterval hHandleUpper hflowTop z) = z.1 :=
    morseCollarPreimage_collarMap hk c ε r η data hf hε hη v hv hsupp hdfOn hrate hHandleInterval hHandleUpper hflowTop z
  have hlow : morseCollarMap hk c ε r η data hf hε (le_of_lt hη) v hv hsupp hdfOn hrate
      ⟨z.1, by
        change f z.1 ≤ c + r ^ 2 / 2
        nlinarith [hz, hε, hη]⟩ = z.1 :=
    morseCollarMap_of_low hk c ε r η data hf hε (le_of_lt hη) v hv hsupp hdfOn hrate
      ⟨z.1, by
        change f z.1 ≤ c + r ^ 2 / 2
        nlinarith [hz, hε, hη]⟩ hz
  exact (morseCollarMap_injective hk c ε r η data hf hε hη v hv hsupp hdfOn hrate) (by
    rw [hmap, hlow])

theorem morseCollarPreimage_eq_strip {m k : ℕ} (hk : k ≤ m + 1) (c ε r η : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} [I.Boundaryless]
    [IsManifold I (⊤ : WithTop ℕ∞) M] {f : M → ℝ}
    {f₀ : M → ℝ} (data : MorseChart (m + 1) k hk c I f₀)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) f)
    (hε : 0 < ε) (hη : 0 < η)
    (v : (x : M) → TangentSpace I x)
    (hv : ContMDiff I (I.prod 𝓘(ℝ, MorseModel (m + 1))) ∞
      (fun x : M => (⟨x, v x⟩ : TangentBundle I M)))
    (hsupp : IsCompact (tsupport v))
    (hdfOn : ∀ x ∈ f ⁻¹' Set.Icc (c - ε - η) (c + r ^ 2 / 2),
      (NormedSpace.fromTangentSpace (f x)) ((mfderiv I 𝓘(ℝ, ℝ) f x) (v x)) = -1)
    (hrate : ∀ x,
      -1 ≤ (NormedSpace.fromTangentSpace (f x)) ((mfderiv I 𝓘(ℝ, ℝ) f x) (v x)) ∧
      (NormedSpace.fromTangentSpace (f x)) ((mfderiv I 𝓘(ℝ, ℝ) f x) (v x)) ≤ 0)
    (hHandleInterval : ∀ (w : MorseModel (m + 1)), w ∈ modelHandle hk ε r → f (data.χ w) ∈ Set.Icc (c - ε - η) (c + r ^ 2 / 2))
    (hHandleUpper : ∀ (w : MorseModel (m + 1)), w ∈ modelHandle hk ε r → f (data.χ w) ≤ c + r ^ 2 / 2)
    (hflowTop : ∀ (w : MorseModel (m + 1)) (hw : w ∈ modelHandle hk ε r),
      morseCollarTopLevel hk c ε r data
        (morseCollarFlowBase hk c ε r η hf hε hη v hv hsupp hdfOn hrate (data.χ w)
          (hHandleInterval w hw)) ≥
        f (data.χ w) - c + ε)
    (z : {x : M // x ∈ sublevel f (c - ε) ∪ Set.range (handleEmbedding hk c ε r data)})
    (hz : c - ε - η ≤ f z.1) :
    morseCollarPreimage hk c ε r η data hf hε hη v hv hsupp hdfOn hrate hHandleInterval hHandleUpper hflowTop z =
      morseCollarPreimageStrip hk c ε r η data hf hε hη v hv hsupp hdfOn hrate hHandleInterval hHandleUpper hflowTop z hz := by
  have hmap : morseCollarMap hk c ε r η data hf hε (le_of_lt hη) v hv hsupp hdfOn hrate
      (morseCollarPreimage hk c ε r η data hf hε hη v hv hsupp hdfOn hrate hHandleInterval hHandleUpper hflowTop z) = z.1 :=
    morseCollarPreimage_collarMap hk c ε r η data hf hε hη v hv hsupp hdfOn hrate hHandleInterval hHandleUpper hflowTop z
  have hstr : morseCollarMap hk c ε r η data hf hε (le_of_lt hη) v hv hsupp hdfOn hrate
      (morseCollarPreimageStrip hk c ε r η data hf hε hη v hv hsupp hdfOn hrate hHandleInterval hHandleUpper hflowTop z hz) =
      z.1 := by
    let σ' : ℝ := f z.1 - c + ε
    have hsub : f z.1 ≤ c + r ^ 2 / 2 := by
      rcases z.2 with hlow | hcell
      · have hr2 : 0 ≤ r ^ 2 / 2 := div_nonneg (sq_nonneg r) (by norm_num)
        have hlow' : f z.1 ≤ c - ε := by simpa [sublevel] using hlow
        nlinarith [hlow', hε, hr2]
      · rcases hcell with ⟨d, hd⟩
        rw [← hd]
        exact hHandleUpper (modelHandleMap hk ε r d) (modelHandleMap_mem hk ε r (le_of_lt hε) d)
    let x : LevelSetSpace f (c - ε) := morseCollarFlowBase hk c ε r η hf hε hη v hv hsupp hdfOn hrate
      z.1 (by
        constructor
        · exact hz
        · exact hsub)
    have hT : morseCollarTopLevel hk c ε r data x ≥ σ' := by
      rcases z.2 with hlow | hcell
      · have hlow' : f z.1 ≤ c - ε := by simpa [sublevel] using hlow
        have hσ'le : σ' ≤ 0 := by dsimp [σ']; linarith
        exact le_trans hσ'le (morseCollarTopLevel_nonneg hk c ε r data x)
      · rcases hcell with ⟨d, hd⟩
        have hxeq : x = morseCollarFlowBase hk c ε r η hf hε hη v hv hsupp hdfOn hrate
            (data.χ (modelHandleMap hk ε r d))
            (hHandleInterval (modelHandleMap hk ε r d)
              (modelHandleMap_mem hk ε r (le_of_lt hε) d)) := by
          apply Subtype.ext
          dsimp [x, morseCollarFlowBase]
          rw [← hd]
          rfl
        have hw' : σ' = f (data.χ (modelHandleMap hk ε r d)) - c + ε := by
          dsimp [σ']
          rw [← hd]
          rfl
        rw [hxeq, hw']
        exact hflowTop (modelHandleMap hk ε r d) (modelHandleMap_mem hk ε r (le_of_lt hε) d)
    have hσmem : morseCollarLevelMapInv hk c ε r η data x σ' ∈ Set.Icc (-η) (r ^ 2 / 2 + ε) := by
      exact morseCollarLevelMapInv_mem hk c ε r η data hε hη x σ' (by
        constructor
        · dsimp [σ']
          linarith
        · exact hT)
    let σ : ℝ := morseCollarLevelMapInv hk c ε r η data x σ'
    have hσeq : morseCollarLevelMap hk c ε r η data x σ = σ' := by
      exact morseCollarLevelMapInv_levelMap hk c ε r η data hε hη x σ'
    have hxval : f x.1 = c - ε := x.2
    have hx' : f x.1 ∈ Set.Icc (c - ε - η) (c + r ^ 2 / 2) := by
      constructor
      · nlinarith [hxval, hη]
      · nlinarith [hxval, hε, hη]
    have hval : f (curveAt v (exists_globalIntegralCurve_of_compactSupport v hv hsupp) x.1 (-σ)) =
        c - ε + σ := by
      have hval0 : f (curveAt v (exists_globalIntegralCurve_of_compactSupport v hv hsupp) x.1 (-σ)) =
          f x.1 - (-σ) :=
        morseCollarFlow_valueOnStrip (I := I) f c ε r η hf v hv hsupp hdfOn hrate hx'
          (by linarith [hxval, hσmem.2]) (by linarith [hxval, hσmem.1])
      rw [hxval] at hval0
      simpa [sub_neg_eq_add] using hval0
    have hy : c - ε - η ≤ f (morseCollarPreimageStrip hk c ε r η data hf hε hη v hv hsupp hdfOn
        hrate hHandleInterval hHandleUpper hflowTop z hz).1 := by
      change c - ε - η ≤ f (curveAt v (exists_globalIntegralCurve_of_compactSupport v hv hsupp) x.1 (-σ))
      dsimp [σ]
      nlinarith [hval, hσmem.1]
    have hyx : (morseCollarPreimageStrip hk c ε r η data hf hε hη v hv hsupp hdfOn hrate
        hHandleInterval hHandleUpper hflowTop z hz).1 = curveAt v (exists_globalIntegralCurve_of_compactSupport v hv hsupp) x.1 (-σ) := by
      dsimp [morseCollarPreimageStrip, σ, x, σ']
    have hzx : curveAt v (exists_globalIntegralCurve_of_compactSupport v hv hsupp) x.1 (-σ') = z.1 := by
      have hh := curveAt_add v (hv.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ ∞))
        (exists_globalIntegralCurve_of_compactSupport v hv hsupp) z.1 σ' (-σ')
      have hsum : σ' + (-σ') = 0 := by ring
      rw [hsum] at hh
      have hx' : curveAt v (exists_globalIntegralCurve_of_compactSupport v hv hsupp) z.1 σ' = x.1 := by
        dsimp [x, morseCollarFlowBase, σ']
      rw [hx'] at hh
      simpa [curveAt_zero v (exists_globalIntegralCurve_of_compactSupport v hv hsupp) z.1] using hh.symm
    exact morseCollarMap_flow_eq hk c ε r η data hf hε hη v hv hsupp hdfOn hrate x σ σ' hσmem hσeq
      (morseCollarPreimageStrip hk c ε r η data hf hε hη v hv hsupp hdfOn hrate hHandleInterval hHandleUpper hflowTop z hz)
      hy hyx z.1 hzx
  exact (morseCollarMap_injective hk c ε r η data hf hε hη v hv hsupp hdfOn hrate) (by
    rw [hmap, hstr])

theorem morseCollarPreimage_eq {m k : ℕ} (hk : k ≤ m + 1) (c ε r η : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} [I.Boundaryless]
    [IsManifold I (⊤ : WithTop ℕ∞) M] {f : M → ℝ}
    {f₀ : M → ℝ} (data : MorseChart (m + 1) k hk c I f₀)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) f)
    (hε : 0 < ε) (hη : 0 < η)
    (v : (x : M) → TangentSpace I x)
    (hv : ContMDiff I (I.prod 𝓘(ℝ, MorseModel (m + 1))) ∞
      (fun x : M => (⟨x, v x⟩ : TangentBundle I M)))
    (hsupp : IsCompact (tsupport v))
    (hdfOn : ∀ x ∈ f ⁻¹' Set.Icc (c - ε - η) (c + r ^ 2 / 2),
      (NormedSpace.fromTangentSpace (f x)) ((mfderiv I 𝓘(ℝ, ℝ) f x) (v x)) = -1)
    (hrate : ∀ x,
      -1 ≤ (NormedSpace.fromTangentSpace (f x)) ((mfderiv I 𝓘(ℝ, ℝ) f x) (v x)) ∧
      (NormedSpace.fromTangentSpace (f x)) ((mfderiv I 𝓘(ℝ, ℝ) f x) (v x)) ≤ 0)
    (hHandleInterval : ∀ (w : MorseModel (m + 1)), w ∈ modelHandle hk ε r → f (data.χ w) ∈ Set.Icc (c - ε - η) (c + r ^ 2 / 2))
    (hHandleUpper : ∀ (w : MorseModel (m + 1)), w ∈ modelHandle hk ε r → f (data.χ w) ≤ c + r ^ 2 / 2)
    (hflowTop : ∀ (w : MorseModel (m + 1)) (hw : w ∈ modelHandle hk ε r),
      morseCollarTopLevel hk c ε r data
        (morseCollarFlowBase hk c ε r η hf hε hη v hv hsupp hdfOn hrate (data.χ w)
          (hHandleInterval w hw)) ≥
        f (data.χ w) - c + ε)
    (hflowMem : ∀ y : SublevelSpace f (c + r ^ 2 / 2),
      morseCollarMap hk c ε r η data hf hε (le_of_lt hη) v hv hsupp hdfOn hrate y ∈
        sublevel f (c - ε) ∪ Set.range (handleEmbedding hk c ε r data))
    (y : SublevelSpace f (c + r ^ 2 / 2)) :
    morseCollarPreimage hk c ε r η data hf hε hη v hv hsupp hdfOn hrate hHandleInterval hHandleUpper hflowTop
      ⟨morseCollarMap hk c ε r η data hf hε (le_of_lt hη) v hv hsupp hdfOn hrate y, hflowMem y⟩ = y := by
  have hmap : morseCollarMap hk c ε r η data hf hε (le_of_lt hη) v hv hsupp hdfOn hrate
      (morseCollarPreimage hk c ε r η data hf hε hη v hv hsupp hdfOn hrate hHandleInterval hHandleUpper hflowTop
        ⟨morseCollarMap hk c ε r η data hf hε (le_of_lt hη) v hv hsupp hdfOn hrate y, hflowMem y⟩) =
      morseCollarMap hk c ε r η data hf hε (le_of_lt hη) v hv hsupp hdfOn hrate y := by
    exact morseCollarPreimage_collarMap hk c ε r η data hf hε hη v hv hsupp hdfOn hrate hHandleInterval hHandleUpper hflowTop
      ⟨morseCollarMap hk c ε r η data hf hε (le_of_lt hη) v hv hsupp hdfOn hrate y, hflowMem y⟩
  exact (morseCollarMap_injective hk c ε r η data hf hε hη v hv hsupp hdfOn hrate) hmap

noncomputable def morseCollarPreimageOnStrip {m k : ℕ} (hk : k ≤ m + 1) (c ε r η : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} [I.Boundaryless]
    [IsManifold I (⊤ : WithTop ℕ∞) M] {f : M → ℝ}
    {f₀ : M → ℝ} (data : MorseChart (m + 1) k hk c I f₀)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) f)
    (hε : 0 < ε) (hη : 0 < η)
    (v : (x : M) → TangentSpace I x)
    (hv : ContMDiff I (I.prod 𝓘(ℝ, MorseModel (m + 1))) ∞
      (fun x : M => (⟨x, v x⟩ : TangentBundle I M)))
    (hsupp : IsCompact (tsupport v))
    (hdfOn : ∀ x ∈ f ⁻¹' Set.Icc (c - ε - η) (c + r ^ 2 / 2),
      (NormedSpace.fromTangentSpace (f x)) ((mfderiv I 𝓘(ℝ, ℝ) f x) (v x)) = -1)
    (hrate : ∀ x,
      -1 ≤ (NormedSpace.fromTangentSpace (f x)) ((mfderiv I 𝓘(ℝ, ℝ) f x) (v x)) ∧
      (NormedSpace.fromTangentSpace (f x)) ((mfderiv I 𝓘(ℝ, ℝ) f x) (v x)) ≤ 0)
    (hHandleInterval : ∀ (w : MorseModel (m + 1)), w ∈ modelHandle hk ε r → f (data.χ w) ∈ Set.Icc (c - ε - η) (c + r ^ 2 / 2))
    (hHandleUpper : ∀ (w : MorseModel (m + 1)), w ∈ modelHandle hk ε r → f (data.χ w) ≤ c + r ^ 2 / 2)
    (hflowTop : ∀ (w : MorseModel (m + 1)) (hw : w ∈ modelHandle hk ε r),
      morseCollarTopLevel hk c ε r data
        (morseCollarFlowBase hk c ε r η hf hε hη v hv hsupp hdfOn hrate (data.χ w)
          (hHandleInterval w hw)) ≥
        f (data.χ w) - c + ε)
    (z : {x : {y : M // y ∈ sublevel f (c - ε) ∪ Set.range (handleEmbedding hk c ε r data)} //
      c - ε - η ≤ f x.1}) : SublevelSpace f (c + r ^ 2 / 2) :=
  morseCollarPreimageStrip hk c ε r η data hf hε hη v hv hsupp hdfOn hrate hHandleInterval hHandleUpper hflowTop z.1 z.2

theorem continuous_morseCollarPreimageOnStrip {m k : ℕ} (hk : k ≤ m + 1) (c ε r η : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} [I.Boundaryless]
    [IsManifold I (⊤ : WithTop ℕ∞) M] {f : M → ℝ}
    {f₀ : M → ℝ} (data : MorseChart (m + 1) k hk c I f₀)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) f)
    (hε : 0 < ε) (hη : 0 < η)
    (v : (x : M) → TangentSpace I x)
    (hv : ContMDiff I (I.prod 𝓘(ℝ, MorseModel (m + 1))) ∞
      (fun x : M => (⟨x, v x⟩ : TangentBundle I M)))
    (hsupp : IsCompact (tsupport v))
    (hdfOn : ∀ x ∈ f ⁻¹' Set.Icc (c - ε - η) (c + r ^ 2 / 2),
      (NormedSpace.fromTangentSpace (f x)) ((mfderiv I 𝓘(ℝ, ℝ) f x) (v x)) = -1)
    (hrate : ∀ x,
      -1 ≤ (NormedSpace.fromTangentSpace (f x)) ((mfderiv I 𝓘(ℝ, ℝ) f x) (v x)) ∧
      (NormedSpace.fromTangentSpace (f x)) ((mfderiv I 𝓘(ℝ, ℝ) f x) (v x)) ≤ 0)
    (hHandleInterval : ∀ (w : MorseModel (m + 1)), w ∈ modelHandle hk ε r → f (data.χ w) ∈ Set.Icc (c - ε - η) (c + r ^ 2 / 2))
    (hHandleUpper : ∀ (w : MorseModel (m + 1)), w ∈ modelHandle hk ε r → f (data.χ w) ≤ c + r ^ 2 / 2)
    (hflowTop : ∀ (w : MorseModel (m + 1)) (hw : w ∈ modelHandle hk ε r),
      morseCollarTopLevel hk c ε r data
        (morseCollarFlowBase hk c ε r η hf hε hη v hv hsupp hdfOn hrate (data.χ w)
          (hHandleInterval w hw)) ≥
        f (data.χ w) - c + ε)
    (hTopCont : Continuous (morseCollarTopLevel hk c ε r data : LevelSetSpace f (c - ε) → ℝ))
    (hcont : Continuous f) :
    Continuous (morseCollarPreimageOnStrip hk c ε r η data hf hε hη v hv hsupp hdfOn hrate hHandleInterval hHandleUpper hflowTop) := by
  let S : Type := {x : {y : M // y ∈ sublevel f (c - ε) ∪ Set.range (handleEmbedding hk c ε r data)} //
      c - ε - η ≤ f x.1}
  let hcomplete : ∀ x : M, ∃ γ : ℝ → M, γ 0 = x ∧ IsMIntegralCurve γ v :=
    exists_globalIntegralCurve_of_compactSupport v hv hsupp
  have hflowCont : Continuous (fun p : ℝ × M => curveAt v hcomplete p.2 p.1) :=
    continuous_globalFlow_of_compactSupport v hv hsupp
  have hsubUnion : ∀ z : S, f z.1.1 ≤ c + r ^ 2 / 2 := by
    intro z
    rcases z.1.2 with hlow | hcell
    · have hr2 : 0 ≤ r ^ 2 / 2 := div_nonneg (sq_nonneg r) (by norm_num)
      have hlow' : f z.1.1 ≤ c - ε := by simpa [sublevel] using hlow
      nlinarith [hlow', hε, hr2]
    · rcases hcell with ⟨d, hd⟩
      rw [← hd]
      exact hHandleUpper (modelHandleMap hk ε r d) (modelHandleMap_mem hk ε r (le_of_lt hε) d)
  let base : S → LevelSetSpace f (c - ε) :=
    fun z => morseCollarFlowBase hk c ε r η hf hε hη v hv hsupp hdfOn hrate z.1.1 (by
      constructor
      · exact z.2
      · exact hsubUnion z)
  have hbaseCont : Continuous base := by
    change Continuous (fun z : S => (⟨curveAt v hcomplete z.1.1 (f z.1.1 - c + ε),
      (morseCollarFlowBase hk c ε r η hf hε hη v hv hsupp hdfOn hrate z.1.1 (by
        constructor
        · exact z.2
        · exact hsubUnion z)).2⟩ : LevelSetSpace f (c - ε)))
    refine Continuous.subtype_mk ?_ (fun z => (base z).2)
    have hfz : Continuous (fun z : S => f z.1.1) :=
      hcont.comp (continuous_subtype_val.comp continuous_subtype_val)
    have hstep : Continuous (fun z : S => (f z.1.1 - c + ε, z.1.1)) := by
      exact ((hfz.sub continuous_const).add continuous_const).prodMk
        (continuous_subtype_val.comp continuous_subtype_val)
    simpa [base] using hflowCont.comp hstep
  have hσ' : Continuous (fun z : S => f z.1.1 - c + ε) := by
    exact ((hcont.comp (continuous_subtype_val.comp continuous_subtype_val)).sub continuous_const).add
      continuous_const
  have hσ : Continuous (fun z : S =>
      morseCollarLevelMapInv hk c ε r η data (base z) (f z.1.1 - c + ε)) := by
    have hinv := continuous_morseCollarLevelMapInv hk c ε r η data hη hTopCont
    have hpair : Continuous (fun z : S => (base z, f z.1.1 - c + ε)) :=
      hbaseCont.prodMk hσ'
    exact hinv.comp hpair
  have hval : Continuous (fun z : S =>
      curveAt v hcomplete (base z).1 (-morseCollarLevelMapInv hk c ε r η data (base z) (f z.1.1 - c + ε))) := by
    have hpair : Continuous (fun z : S =>
        (-morseCollarLevelMapInv hk c ε r η data (base z) (f z.1.1 - c + ε), (base z).1)) :=
      hσ.neg.prodMk (continuous_subtype_val.comp hbaseCont)
    exact hflowCont.comp hpair
  have hmain : Continuous (fun z : S => (morseCollarPreimageOnStrip hk c ε r η data hf hε hη
      v hv hsupp hdfOn hrate hHandleInterval hHandleUpper hflowTop z).1) := by
    refine hval.congr ?_
    intro z
    dsimp [morseCollarPreimageOnStrip, morseCollarPreimageStrip, base, morseCollarFlowBase]
  exact Continuous.subtype_mk hmain (fun z => (morseCollarPreimageOnStrip hk c ε r η data hf hε hη
    v hv hsupp hdfOn hrate hHandleInterval hHandleUpper hflowTop z).2)

theorem continuousOn_morseCollarPreimage_lower {m k : ℕ} (hk : k ≤ m + 1) (c ε r η : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} [I.Boundaryless]
    [IsManifold I (⊤ : WithTop ℕ∞) M] {f : M → ℝ}
    {f₀ : M → ℝ} (data : MorseChart (m + 1) k hk c I f₀)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) f)
    (hε : 0 < ε) (hη : 0 < η)
    (v : (x : M) → TangentSpace I x)
    (hv : ContMDiff I (I.prod 𝓘(ℝ, MorseModel (m + 1))) ∞
      (fun x : M => (⟨x, v x⟩ : TangentBundle I M)))
    (hsupp : IsCompact (tsupport v))
    (hdfOn : ∀ x ∈ f ⁻¹' Set.Icc (c - ε - η) (c + r ^ 2 / 2),
      (NormedSpace.fromTangentSpace (f x)) ((mfderiv I 𝓘(ℝ, ℝ) f x) (v x)) = -1)
    (hrate : ∀ x,
      -1 ≤ (NormedSpace.fromTangentSpace (f x)) ((mfderiv I 𝓘(ℝ, ℝ) f x) (v x)) ∧
      (NormedSpace.fromTangentSpace (f x)) ((mfderiv I 𝓘(ℝ, ℝ) f x) (v x)) ≤ 0)
    (hHandleInterval : ∀ (w : MorseModel (m + 1)), w ∈ modelHandle hk ε r → f (data.χ w) ∈ Set.Icc (c - ε - η) (c + r ^ 2 / 2))
    (hHandleUpper : ∀ (w : MorseModel (m + 1)), w ∈ modelHandle hk ε r → f (data.χ w) ≤ c + r ^ 2 / 2)
    (hflowTop : ∀ (w : MorseModel (m + 1)) (hw : w ∈ modelHandle hk ε r),
      morseCollarTopLevel hk c ε r data
        (morseCollarFlowBase hk c ε r η hf hε hη v hv hsupp hdfOn hrate (data.χ w)
          (hHandleInterval w hw)) ≥
        f (data.χ w) - c + ε) :
    ContinuousOn (fun z : {x : M // x ∈ sublevel f (c - ε) ∪ Set.range (handleEmbedding hk c ε r data)} =>
      morseCollarPreimage hk c ε r η data hf hε hη v hv hsupp hdfOn hrate hHandleInterval hHandleUpper hflowTop z)
      {z : {x : M // x ∈ sublevel f (c - ε) ∪ Set.range (handleEmbedding hk c ε r data)} |
        f z.1 ≤ c - ε - η} := by
  let S₁ : Set {x : M // x ∈ sublevel f (c - ε) ∪ Set.range (handleEmbedding hk c ε r data)} :=
    {z : {x : M // x ∈ sublevel f (c - ε) ∪ Set.range (handleEmbedding hk c ε r data)} |
      f z.1 ≤ c - ε - η}
  rw [continuousOn_iff_continuous_restrict]
  change Continuous (fun z : {x : {y : M // y ∈ sublevel f (c - ε) ∪ Set.range (handleEmbedding hk c ε r data)} //
      f x.1 ≤ c - ε - η} => morseCollarPreimage hk c ε r η data hf hε hη v hv hsupp hdfOn hrate
        hHandleInterval hHandleUpper hflowTop z.1)
  have hcongr : (fun z : {x : {y : M // y ∈ sublevel f (c - ε) ∪ Set.range (handleEmbedding hk c ε r data)} //
        f x.1 ≤ c - ε - η} => morseCollarPreimage hk c ε r η data hf hε hη v hv hsupp hdfOn hrate
        hHandleInterval hHandleUpper hflowTop z.1) =
      fun z : {x : {y : M // y ∈ sublevel f (c - ε) ∪ Set.range (handleEmbedding hk c ε r data)} //
        f x.1 ≤ c - ε - η} => (⟨z.1.1, by
          change f z.1.1 ≤ c + r ^ 2 / 2
          have hr2 : 0 ≤ r ^ 2 / 2 := div_nonneg (sq_nonneg r) (by norm_num)
          nlinarith [z.2, hε, hη, hr2]⟩ : SublevelSpace f (c + r ^ 2 / 2)) := by
    funext z
    exact morseCollarPreimage_eq_low hk c ε r η data hf hε hη v hv hsupp hdfOn hrate hHandleInterval hHandleUpper hflowTop z.1 z.2
  rw [hcongr]
  exact Continuous.subtype_mk (continuous_subtype_val.comp continuous_subtype_val) (fun z => by
    change f z.1.1 ≤ c + r ^ 2 / 2
    have hr2 : 0 ≤ r ^ 2 / 2 := div_nonneg (sq_nonneg r) (by norm_num)
    nlinarith [z.2, hε, hη, hr2])

theorem continuousOn_morseCollarPreimage_strip {m k : ℕ} (hk : k ≤ m + 1) (c ε r η : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} [I.Boundaryless]
    [IsManifold I (⊤ : WithTop ℕ∞) M] {f : M → ℝ}
    {f₀ : M → ℝ} (data : MorseChart (m + 1) k hk c I f₀)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) f)
    (hε : 0 < ε) (hη : 0 < η)
    (v : (x : M) → TangentSpace I x)
    (hv : ContMDiff I (I.prod 𝓘(ℝ, MorseModel (m + 1))) ∞
      (fun x : M => (⟨x, v x⟩ : TangentBundle I M)))
    (hsupp : IsCompact (tsupport v))
    (hdfOn : ∀ x ∈ f ⁻¹' Set.Icc (c - ε - η) (c + r ^ 2 / 2),
      (NormedSpace.fromTangentSpace (f x)) ((mfderiv I 𝓘(ℝ, ℝ) f x) (v x)) = -1)
    (hrate : ∀ x,
      -1 ≤ (NormedSpace.fromTangentSpace (f x)) ((mfderiv I 𝓘(ℝ, ℝ) f x) (v x)) ∧
      (NormedSpace.fromTangentSpace (f x)) ((mfderiv I 𝓘(ℝ, ℝ) f x) (v x)) ≤ 0)
    (hHandleInterval : ∀ (w : MorseModel (m + 1)), w ∈ modelHandle hk ε r → f (data.χ w) ∈ Set.Icc (c - ε - η) (c + r ^ 2 / 2))
    (hHandleUpper : ∀ (w : MorseModel (m + 1)), w ∈ modelHandle hk ε r → f (data.χ w) ≤ c + r ^ 2 / 2)
    (hflowTop : ∀ (w : MorseModel (m + 1)) (hw : w ∈ modelHandle hk ε r),
      morseCollarTopLevel hk c ε r data
        (morseCollarFlowBase hk c ε r η hf hε hη v hv hsupp hdfOn hrate (data.χ w)
          (hHandleInterval w hw)) ≥
        f (data.χ w) - c + ε)
    (hTopCont : Continuous (morseCollarTopLevel hk c ε r data : LevelSetSpace f (c - ε) → ℝ))
    (hcont : Continuous f) :
    ContinuousOn (fun z : {x : M // x ∈ sublevel f (c - ε) ∪ Set.range (handleEmbedding hk c ε r data)} =>
      morseCollarPreimage hk c ε r η data hf hε hη v hv hsupp hdfOn hrate hHandleInterval hHandleUpper hflowTop z)
      {z : {x : M // x ∈ sublevel f (c - ε) ∪ Set.range (handleEmbedding hk c ε r data)} |
        c - ε - η ≤ f z.1} := by
  rw [continuousOn_iff_continuous_restrict]
  change Continuous (fun z : {x : {y : M // y ∈ sublevel f (c - ε) ∪ Set.range (handleEmbedding hk c ε r data)} //
      c - ε - η ≤ f x.1} => morseCollarPreimage hk c ε r η data hf hε hη v hv hsupp hdfOn hrate
        hHandleInterval hHandleUpper hflowTop z.1)
  have hcongr : (fun z : {x : {y : M // y ∈ sublevel f (c - ε) ∪ Set.range (handleEmbedding hk c ε r data)} //
        c - ε - η ≤ f x.1} => morseCollarPreimage hk c ε r η data hf hε hη v hv hsupp hdfOn hrate
        hHandleInterval hHandleUpper hflowTop z.1) =
      fun z : {x : {y : M // y ∈ sublevel f (c - ε) ∪ Set.range (handleEmbedding hk c ε r data)} //
        c - ε - η ≤ f x.1} => morseCollarPreimageOnStrip hk c ε r η data hf hε hη v hv hsupp
          hdfOn hrate hHandleInterval hHandleUpper hflowTop ⟨z.1, z.2⟩ := by
    funext z
    exact morseCollarPreimage_eq_strip hk c ε r η data hf hε hη v hv hsupp hdfOn hrate hHandleInterval hHandleUpper hflowTop
      z.1 z.2
  rw [hcongr]
  simpa using (continuous_morseCollarPreimageOnStrip hk c ε r η data hf hε hη
    v hv hsupp hdfOn hrate hHandleInterval hHandleUpper hflowTop hTopCont hcont)

theorem continuous_morseCollarPreimage {m k : ℕ} (hk : k ≤ m + 1) (c ε r η : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} [I.Boundaryless]
    [IsManifold I (⊤ : WithTop ℕ∞) M] {f : M → ℝ}
    {f₀ : M → ℝ} (data : MorseChart (m + 1) k hk c I f₀)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) f)
    (hε : 0 < ε) (hη : 0 < η)
    (v : (x : M) → TangentSpace I x)
    (hv : ContMDiff I (I.prod 𝓘(ℝ, MorseModel (m + 1))) ∞
      (fun x : M => (⟨x, v x⟩ : TangentBundle I M)))
    (hsupp : IsCompact (tsupport v))
    (hdfOn : ∀ x ∈ f ⁻¹' Set.Icc (c - ε - η) (c + r ^ 2 / 2),
      (NormedSpace.fromTangentSpace (f x)) ((mfderiv I 𝓘(ℝ, ℝ) f x) (v x)) = -1)
    (hrate : ∀ x,
      -1 ≤ (NormedSpace.fromTangentSpace (f x)) ((mfderiv I 𝓘(ℝ, ℝ) f x) (v x)) ∧
      (NormedSpace.fromTangentSpace (f x)) ((mfderiv I 𝓘(ℝ, ℝ) f x) (v x)) ≤ 0)
    (hHandleInterval : ∀ (w : MorseModel (m + 1)), w ∈ modelHandle hk ε r → f (data.χ w) ∈ Set.Icc (c - ε - η) (c + r ^ 2 / 2))
    (hHandleUpper : ∀ (w : MorseModel (m + 1)), w ∈ modelHandle hk ε r → f (data.χ w) ≤ c + r ^ 2 / 2)
    (hflowTop : ∀ (w : MorseModel (m + 1)) (hw : w ∈ modelHandle hk ε r),
      morseCollarTopLevel hk c ε r data
        (morseCollarFlowBase hk c ε r η hf hε hη v hv hsupp hdfOn hrate (data.χ w)
          (hHandleInterval w hw)) ≥
        f (data.χ w) - c + ε)
    (hTopCont : Continuous (morseCollarTopLevel hk c ε r data : LevelSetSpace f (c - ε) → ℝ))
    (hcont : Continuous f) :
    Continuous (morseCollarPreimage hk c ε r η data hf hε hη v hv hsupp hdfOn hrate hHandleInterval hHandleUpper hflowTop) := by
  let S : Type := {x : M // x ∈ sublevel f (c - ε) ∪ Set.range (handleEmbedding hk c ε r data)}
  let S₁ : Set S := {z : S | f z.1 ≤ c - ε - η}
  let S₂ : Set S := {z : S | c - ε - η ≤ f z.1}
  have hclosed₁ : IsClosed S₁ := by
    dsimp [S₁]
    exact IsClosed.preimage (hcont.comp continuous_subtype_val) (isClosed_Iic (a := c - ε - η))
  have hclosed₂ : IsClosed S₂ := by
    dsimp [S₂]
    exact IsClosed.preimage (hcont.comp continuous_subtype_val) (isClosed_Ici (a := c - ε - η))
  have hunion : Set.univ = S₁ ∪ S₂ := by
    ext z
    constructor
    · intro hz
      by_cases h : f z.1 ≤ c - ε - η
      · exact Or.inl h
      · exact Or.inr (le_of_lt (lt_of_not_ge h))
    · intro hz
      trivial
  exact continuousOn_univ.mp (by
    rw [hunion]
    refine (continuousOn_morseCollarPreimage_lower hk c ε r η data hf hε hη v hv hsupp hdfOn
      hrate hHandleInterval hHandleUpper hflowTop).union_of_isClosed
      (continuousOn_morseCollarPreimage_strip hk c ε r η data hf hε hη v hv hsupp hdfOn hrate
        hHandleInterval hHandleUpper hflowTop hTopCont hcont) hclosed₁ hclosed₂)

noncomputable def morseCollarHomeoUnion {m k : ℕ} (hk : k ≤ m + 1) (c ε r η : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} [I.Boundaryless]
    [IsManifold I (⊤ : WithTop ℕ∞) M] {f : M → ℝ}
    {f₀ : M → ℝ} (data : MorseChart (m + 1) k hk c I f₀)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) f)
    (hε : 0 < ε) (hη : 0 < η)
    (v : (x : M) → TangentSpace I x)
    (hv : ContMDiff I (I.prod 𝓘(ℝ, MorseModel (m + 1))) ∞
      (fun x : M => (⟨x, v x⟩ : TangentBundle I M)))
    (hsupp : IsCompact (tsupport v))
    (hdfOn : ∀ x ∈ f ⁻¹' Set.Icc (c - ε - η) (c + r ^ 2 / 2),
      (NormedSpace.fromTangentSpace (f x)) ((mfderiv I 𝓘(ℝ, ℝ) f x) (v x)) = -1)
    (hrate : ∀ x,
      -1 ≤ (NormedSpace.fromTangentSpace (f x)) ((mfderiv I 𝓘(ℝ, ℝ) f x) (v x)) ∧
      (NormedSpace.fromTangentSpace (f x)) ((mfderiv I 𝓘(ℝ, ℝ) f x) (v x)) ≤ 0)
    (hHandleInterval : ∀ (w : MorseModel (m + 1)), w ∈ modelHandle hk ε r → f (data.χ w) ∈ Set.Icc (c - ε - η) (c + r ^ 2 / 2))
    (hHandleUpper : ∀ (w : MorseModel (m + 1)), w ∈ modelHandle hk ε r → f (data.χ w) ≤ c + r ^ 2 / 2)
    (hflowTop : ∀ (w : MorseModel (m + 1)) (hw : w ∈ modelHandle hk ε r),
      morseCollarTopLevel hk c ε r data
        (morseCollarFlowBase hk c ε r η hf hε hη v hv hsupp hdfOn hrate (data.χ w)
          (hHandleInterval w hw)) ≥
        f (data.χ w) - c + ε)
    (hTopCont : Continuous (morseCollarTopLevel hk c ε r data : LevelSetSpace f (c - ε) → ℝ))
    (hflowMem : ∀ y : SublevelSpace f (c + r ^ 2 / 2),
      morseCollarMap hk c ε r η data hf hε (le_of_lt hη) v hv hsupp hdfOn hrate y ∈
        sublevel f (c - ε) ∪ Set.range (handleEmbedding hk c ε r data))
    (hcont : Continuous f) :
    SublevelSpace f (c + r ^ 2 / 2) ≃ₜ
      {x : M // x ∈ sublevel f (c - ε) ∪ Set.range (handleEmbedding hk c ε r data)} where
  toFun := fun y => ⟨morseCollarMap hk c ε r η data hf hε (le_of_lt hη) v hv hsupp hdfOn hrate y,
    hflowMem y⟩
  invFun := morseCollarPreimage hk c ε r η data hf hε hη v hv hsupp hdfOn hrate hHandleInterval hHandleUpper hflowTop
  left_inv := by
    intro y
    exact morseCollarPreimage_eq hk c ε r η data hf hε hη v hv hsupp hdfOn hrate hHandleInterval hHandleUpper hflowTop
      hflowMem y
  right_inv := by
    intro z
    apply Subtype.ext
    exact morseCollarPreimage_collarMap hk c ε r η data hf hε hη v hv hsupp hdfOn hrate hHandleInterval hHandleUpper hflowTop z
  continuous_toFun := Continuous.subtype_mk
    (continuous_morseCollarMap hk c ε r η data hf hε hη hTopCont v hv hsupp hdfOn hrate) (fun y => hflowMem y)
  continuous_invFun := continuous_morseCollarPreimage hk c ε r η data hf hε hη v hv hsupp hdfOn
    hrate hHandleInterval hHandleUpper hflowTop hTopCont hcont

theorem morseCollarHomeoUnion_low {m k : ℕ} (hk : k ≤ m + 1) (c ε r η : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} [I.Boundaryless]
    [IsManifold I (⊤ : WithTop ℕ∞) M] {f : M → ℝ}
    {f₀ : M → ℝ} (data : MorseChart (m + 1) k hk c I f₀)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) f)
    (hε : 0 < ε) (hη : 0 < η)
    (v : (x : M) → TangentSpace I x)
    (hv : ContMDiff I (I.prod 𝓘(ℝ, MorseModel (m + 1))) ∞
      (fun x : M => (⟨x, v x⟩ : TangentBundle I M)))
    (hsupp : IsCompact (tsupport v))
    (hdfOn : ∀ x ∈ f ⁻¹' Set.Icc (c - ε - η) (c + r ^ 2 / 2),
      (NormedSpace.fromTangentSpace (f x)) ((mfderiv I 𝓘(ℝ, ℝ) f x) (v x)) = -1)
    (hrate : ∀ x,
      -1 ≤ (NormedSpace.fromTangentSpace (f x)) ((mfderiv I 𝓘(ℝ, ℝ) f x) (v x)) ∧
      (NormedSpace.fromTangentSpace (f x)) ((mfderiv I 𝓘(ℝ, ℝ) f x) (v x)) ≤ 0)
    (hHandleInterval : ∀ (w : MorseModel (m + 1)), w ∈ modelHandle hk ε r → f (data.χ w) ∈ Set.Icc (c - ε - η) (c + r ^ 2 / 2))
    (hHandleUpper : ∀ (w : MorseModel (m + 1)), w ∈ modelHandle hk ε r → f (data.χ w) ≤ c + r ^ 2 / 2)
    (hflowTop : ∀ (w : MorseModel (m + 1)) (hw : w ∈ modelHandle hk ε r),
      morseCollarTopLevel hk c ε r data
        (morseCollarFlowBase hk c ε r η hf hε hη v hv hsupp hdfOn hrate (data.χ w)
          (hHandleInterval w hw)) ≥
        f (data.χ w) - c + ε)
    (hTopCont : Continuous (morseCollarTopLevel hk c ε r data : LevelSetSpace f (c - ε) → ℝ))
    (hflowMem : ∀ y : SublevelSpace f (c + r ^ 2 / 2),
      morseCollarMap hk c ε r η data hf hε (le_of_lt hη) v hv hsupp hdfOn hrate y ∈
        sublevel f (c - ε) ∪ Set.range (handleEmbedding hk c ε r data))
    (hcont : Continuous f)
    (x : {x : M // x ∈ sublevel f (c - ε - η)}) :
    (morseCollarHomeoUnion hk c ε r η data hf hε hη v hv hsupp hdfOn hrate hHandleInterval hHandleUpper hflowTop hTopCont hflowMem hcont)
      ⟨x.1, by
        change f x.1 ≤ c + r ^ 2 / 2
        have hr2 : 0 ≤ r ^ 2 / 2 := div_nonneg (sq_nonneg r) (by norm_num)
        have hx' : f x.1 ≤ c - ε - η := by
          change x.1 ∈ sublevel f (c - ε - η)
          exact x.2
        nlinarith [hx', hε, hη, hr2]⟩ = ⟨x.1, Or.inl (by
          change f x.1 ≤ c - ε
          have hx' : f x.1 ≤ c - ε - η := by
            change x.1 ∈ sublevel f (c - ε - η)
            exact x.2
          linarith)⟩ := by
  have hx' : f x.1 ≤ c - ε - η := by
    change x.1 ∈ sublevel f (c - ε - η)
    exact x.2
  apply Subtype.ext
  change morseCollarMap hk c ε r η data hf hε (le_of_lt hη) v hv hsupp hdfOn hrate
    ⟨x.1, by
      change f x.1 ≤ c + r ^ 2 / 2
      have hr2 : 0 ≤ r ^ 2 / 2 := div_nonneg (sq_nonneg r) (by norm_num)
      nlinarith [hx', hε, hη, hr2]⟩ = x.1
  exact morseCollarMap_of_low hk c ε r η data hf hε (le_of_lt hη) v hv hsupp hdfOn hrate
    ⟨x.1, by
      change f x.1 ≤ c + r ^ 2 / 2
      have hr2 : 0 ≤ r ^ 2 / 2 := div_nonneg (sq_nonneg r) (by norm_num)
      nlinarith [hx', hε, hη, hr2]⟩ hx'

noncomputable def morseHandleAdjunctionHomeoUpper {m k : ℕ} (hk : k ≤ m + 1) (c ε r η : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} [I.Boundaryless]
    [IsManifold I (⊤ : WithTop ℕ∞) M] {f : M → ℝ}
    (data : MorseChart (m + 1) k hk c I f)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) f)
    (hε : 0 < ε) (hr : 0 < r) (hη : 0 < η)
    (hεr : Real.sqrt (2 * ε + 2 * r ^ 2) < data.R)
    (v : (x : M) → TangentSpace I x)
    (hv : ContMDiff I (I.prod 𝓘(ℝ, MorseModel (m + 1))) ∞
      (fun x : M => (⟨x, v x⟩ : TangentBundle I M)))
    (hsupp : IsCompact (tsupport v))
    (hdfOn : ∀ x ∈ f ⁻¹' Set.Icc (c - ε - η) (c + r ^ 2 / 2),
      (NormedSpace.fromTangentSpace (f x)) ((mfderiv I 𝓘(ℝ, ℝ) f x) (v x)) = -1)
    (hrate : ∀ x,
      -1 ≤ (NormedSpace.fromTangentSpace (f x)) ((mfderiv I 𝓘(ℝ, ℝ) f x) (v x)) ∧
      (NormedSpace.fromTangentSpace (f x)) ((mfderiv I 𝓘(ℝ, ℝ) f x) (v x)) ≤ 0)
    (hHandleInterval : ∀ (w : MorseModel (m + 1)), w ∈ modelHandle hk ε r → f (data.χ w) ∈ Set.Icc (c - ε - η) (c + r ^ 2 / 2))
    (hHandleUpper : ∀ (w : MorseModel (m + 1)), w ∈ modelHandle hk ε r → f (data.χ w) ≤ c + r ^ 2 / 2)
    (hflowTop : ∀ (w : MorseModel (m + 1)) (hw : w ∈ modelHandle hk ε r),
      morseCollarTopLevel hk c ε r data
        (morseCollarFlowBase hk c ε r η hf hε hη v hv hsupp hdfOn hrate (data.χ w)
          (hHandleInterval w hw)) ≥
        f (data.χ w) - c + ε)
    (hTopCont : Continuous (morseCollarTopLevel hk c ε r data : LevelSetSpace f (c - ε) → ℝ))
    (hflowMem : ∀ y : SublevelSpace f (c + r ^ 2 / 2),
      morseCollarMap hk c ε r η data hf hε (le_of_lt hη) v hv hsupp hdfOn hrate y ∈
        sublevel f (c - ε) ∪ Set.range (handleEmbedding hk c ε r data))
    (hcont : Continuous f) :
    Handle.AdjunctionSpace k (m + 1 - k) (morseAttachingEmbedding hk c ε r data hε (le_of_lt hεr)) ≃ₜ
      SublevelSpace f (c + r ^ 2 / 2) :=
  (morseHandleAdjunctionHomeoUnion hk c ε r data hε (ne_of_gt hr) (le_of_lt hεr) hcont).trans
    (morseCollarHomeoUnion hk c ε r η data hf hε hη v hv hsupp hdfOn hrate hHandleInterval hHandleUpper hflowTop hTopCont hflowMem hcont).symm

theorem morseHandleAdjunctionHomeoUpper_lower {m k : ℕ} (hk : k ≤ m + 1) (c ε r η : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} [I.Boundaryless]
    [IsManifold I (⊤ : WithTop ℕ∞) M] {f : M → ℝ}
    (data : MorseChart (m + 1) k hk c I f)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) f)
    (hε : 0 < ε) (hr : 0 < r) (hη : 0 < η)
    (hεr : Real.sqrt (2 * ε + 2 * r ^ 2) < data.R)
    (v : (x : M) → TangentSpace I x)
    (hv : ContMDiff I (I.prod 𝓘(ℝ, MorseModel (m + 1))) ∞
      (fun x : M => (⟨x, v x⟩ : TangentBundle I M)))
    (hsupp : IsCompact (tsupport v))
    (hdfOn : ∀ x ∈ f ⁻¹' Set.Icc (c - ε - η) (c + r ^ 2 / 2),
      (NormedSpace.fromTangentSpace (f x)) ((mfderiv I 𝓘(ℝ, ℝ) f x) (v x)) = -1)
    (hrate : ∀ x,
      -1 ≤ (NormedSpace.fromTangentSpace (f x)) ((mfderiv I 𝓘(ℝ, ℝ) f x) (v x)) ∧
      (NormedSpace.fromTangentSpace (f x)) ((mfderiv I 𝓘(ℝ, ℝ) f x) (v x)) ≤ 0)
    (hHandleInterval : ∀ (w : MorseModel (m + 1)), w ∈ modelHandle hk ε r → f (data.χ w) ∈ Set.Icc (c - ε - η) (c + r ^ 2 / 2))
    (hHandleUpper : ∀ (w : MorseModel (m + 1)), w ∈ modelHandle hk ε r → f (data.χ w) ≤ c + r ^ 2 / 2)
    (hflowTop : ∀ (w : MorseModel (m + 1)) (hw : w ∈ modelHandle hk ε r),
      morseCollarTopLevel hk c ε r data
        (morseCollarFlowBase hk c ε r η hf hε hη v hv hsupp hdfOn hrate (data.χ w)
          (hHandleInterval w hw)) ≥
        f (data.χ w) - c + ε)
    (hTopCont : Continuous (morseCollarTopLevel hk c ε r data : LevelSetSpace f (c - ε) → ℝ))
    (hflowMem : ∀ y : SublevelSpace f (c + r ^ 2 / 2),
      morseCollarMap hk c ε r η data hf hε (le_of_lt hη) v hv hsupp hdfOn hrate y ∈
        sublevel f (c - ε) ∪ Set.range (handleEmbedding hk c ε r data))
    (hcont : Continuous f)
    (x : {x : M // x ∈ sublevel f (c - ε - η)}) :
    (morseHandleAdjunctionHomeoUpper hk c ε r η data hf hε hr hη hεr v hv hsupp hdfOn hrate hHandleInterval hHandleUpper hflowTop hTopCont
      hflowMem hcont) (Handle.lower (morseAttachingEmbedding hk c ε r data hε (le_of_lt hεr))
        ⟨x.1, by
          change f x.1 ≤ c - ε
          have hx' : f x.1 ≤ c - ε - η := by
            change x.1 ∈ sublevel f (c - ε - η)
            exact x.2
          exact le_trans hx' (by linarith)⟩) = ⟨x.1, by
            change f x.1 ≤ c + r ^ 2 / 2
            have hr2 : 0 ≤ r ^ 2 / 2 := div_nonneg (sq_nonneg r) (by norm_num)
            have hx' : f x.1 ≤ c - ε - η := by
              change x.1 ∈ sublevel f (c - ε - η)
              exact x.2
            nlinarith [hx', hε, hη, hr2]⟩ := by
  have hx' : f x.1 ≤ c - ε - η := by
    change x.1 ∈ sublevel f (c - ε - η)
    exact x.2
  dsimp [morseHandleAdjunctionHomeoUpper]
  rw [morseHandleAdjunctionHomeoUnion_lower hk c ε r data hε (ne_of_gt hr) (le_of_lt hεr) hcont
    ⟨x.1, by
      change f x.1 ≤ c - ε
      exact le_trans hx' (by linarith)⟩]
  simpa [morseCollarHomeoUnion] using (morseCollarPreimage_eq_low hk c ε r η data hf hε hη v hv
    hsupp hdfOn hrate hHandleInterval hHandleUpper hflowTop ⟨x.1, Or.inl (by
      exact le_trans hx' (by linarith))⟩ hx')

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

theorem modifiedSublevel_subset_lower_union_modelHandle {n k : ℕ} (hk : k ≤ n)
    (c ε δ r : ℝ) (hε : 0 < ε) (hδ : 0 < δ) (hr : 3 * δ / 2 ≤ r) :
    {y : MorseModel n | modifiedNormalForm hk c ε δ y ≤ c - ε} ⊆
      {y : MorseModel n | morseNormalForm hk c y ≤ c - ε} ∪ modelHandle hk ε r := by
  intro y hy
  change modifiedNormalForm hk c ε δ y ≤ c - ε at hy
  by_cases hf : morseNormalForm hk c y ≤ c - ε
  · exact Or.inl hf
  · have hgt : c - ε < morseNormalForm hk c y := lt_of_not_ge hf
    have hsplit := morseNormalForm_split hk c y
    have hneg_le : ‖negPart hk y‖ ^ 2 ≤ ‖posPart hk y‖ ^ 2 + 2 * ε := by
      nlinarith [hsplit, hgt]
    have hdip : 0 < modMu ε (‖negPart hk y‖ ^ 2) * modGamma δ ‖posPart hk y‖ := by
      have hsplitM := modifiedNormalForm_split hk c ε δ y
      have hnonneg : 0 ≤ modMu ε (‖negPart hk y‖ ^ 2) * modGamma δ ‖posPart hk y‖ := by
        exact mul_nonneg (modMu_nonneg (le_of_lt hε)) (modGamma_nonneg δ ‖posPart hk y‖)
      have hdip' : modMu ε (‖negPart hk y‖ ^ 2) * modGamma δ ‖posPart hk y‖ ≥
          morseNormalForm hk c y - (c - ε) := by
        nlinarith [hy, hsplitM, hsplit]
      nlinarith [hnonneg, hdip', hgt]
    have hmu_pos : 0 < modMu ε (‖negPart hk y‖ ^ 2) := by
      have hg_nonneg : 0 ≤ modGamma δ ‖posPart hk y‖ := modGamma_nonneg δ ‖posPart hk y‖
      have hg_pos : 0 < modGamma δ ‖posPart hk y‖ := by
        by_contra hg0
        have hg0' : modGamma δ ‖posPart hk y‖ = 0 := le_antisymm (not_lt.mp hg0) hg_nonneg
        rw [hg0', mul_zero] at hdip
        linarith
      have hmu_nonneg : 0 ≤ modMu ε (‖negPart hk y‖ ^ 2) := modMu_nonneg (le_of_lt hε)
      by_contra hmu0
      have hmu0' : modMu ε (‖negPart hk y‖ ^ 2) = 0 := le_antisymm (not_lt.mp hmu0) hmu_nonneg
      rw [hmu0', zero_mul] at hdip
      linarith
    have hg_pos : 0 < modGamma δ ‖posPart hk y‖ := by
      have hg_nonneg : 0 ≤ modGamma δ ‖posPart hk y‖ := modGamma_nonneg δ ‖posPart hk y‖
      by_contra hg0
      have hg0' : modGamma δ ‖posPart hk y‖ = 0 := le_antisymm (not_lt.mp hg0) hg_nonneg
      rw [hg0', mul_zero] at hdip
      linarith
    have hneg_lt : ‖negPart hk y‖ ^ 2 < 4 * ε := by
      by_contra hnot
      have hle : 4 * ε ≤ ‖negPart hk y‖ ^ 2 := le_of_not_gt hnot
      have hz := modMu_zero hε hle
      rw [hz] at hmu_pos
      linarith
    have hpos_lt : ‖posPart hk y‖ < 3 * δ / 2 := by
      by_contra hnot
      have hle : 3 * δ / 2 ≤ ‖posPart hk y‖ := le_of_not_gt hnot
      have hz := modGamma_zero hδ hle
      rw [hz] at hg_pos
      linarith
    have hpos_norm : 0 ≤ ‖posPart hk y‖ := norm_nonneg _
    have hpos_le : ‖posPart hk y‖ ^ 2 ≤ r ^ 2 := by
      nlinarith [hpos_lt, hr, hpos_norm]
    exact Or.inr (by
      dsimp [modelHandle]
      constructor
      · exact hpos_le
      · exact hneg_le)


theorem modifiedSublevel_union_modelHandle_eq {n k : ℕ} (hk : k ≤ n) (c ε δ r : ℝ)
    (hε : 0 < ε) (hδ : 0 < δ) (hr : 3 * δ / 2 ≤ r) :
    {y : MorseModel n | modifiedNormalForm hk c ε δ y ≤ c - ε} ∪ modelHandle hk ε r =
      {y : MorseModel n | morseNormalForm hk c y ≤ c - ε} ∪ modelHandle hk ε r := by
  ext y
  constructor
  · intro hy
    rcases hy with hmod | hh
    · by_cases hf : morseNormalForm hk c y ≤ c - ε
      · exact Or.inl hf
      · exact (modifiedSublevel_subset_lower_union_modelHandle hk c ε δ r hε hδ hr (by
          exact hmod))
    · exact Or.inr hh
  · intro hy
    rcases hy with hf | hh
    · exact Or.inl (le_trans (modifiedNormalForm_le_f hk c ε δ hε y) hf)
    · exact Or.inr hh


theorem modifiedNormalForm_eq_of_norm_large {n k : ℕ} (hk : k ≤ n) (c ε δ r : ℝ)
    (hε : 0 < ε) (hδ : 0 < δ) (hr : r ^ 2 ≥ ε + 9 * δ ^ 2 / 8) (y : MorseModel n)
    (hy : 2 * ε + 2 * r ^ 2 ≤ morseNorm n y ^ 2) :
    modifiedNormalForm hk c ε δ y = morseNormalForm hk c y := by
  have hsplit := modifiedNormalForm_split hk c ε δ y
  rw [hsplit, morseNormalForm_split]
  have hnorm : morseNorm n y ^ 2 = ‖negPart hk y‖ ^ 2 + ‖posPart hk y‖ ^ 2 := by
    simpa [add_comm] using (morseNorm_sq_eq_negPart_add_posPart hk y)
  by_cases hpos : 3 * δ / 2 ≤ ‖posPart hk y‖
  · have hg : modGamma δ ‖posPart hk y‖ = 0 := modGamma_zero hδ hpos
    simp [hg]
  · have hpos_lt : ‖posPart hk y‖ < 3 * δ / 2 := lt_of_not_ge hpos
    have hpos_lt_sq : ‖posPart hk y‖ ^ 2 ≤ (3 * δ / 2) ^ 2 := by
      have hlt : ‖posPart hk y‖ ^ 2 < (3 * δ / 2) ^ 2 := by
        rw [sq_lt_sq]
        rw [abs_of_nonneg (norm_nonneg _), abs_of_nonneg (by positivity : 0 ≤ 3 * δ / 2)]
        exact hpos_lt
      exact le_of_lt hlt
    have hB : (3 * δ / 2) ^ 2 = 9 * δ ^ 2 / 4 := by ring
    have hpos_lt_sq' : ‖posPart hk y‖ ^ 2 ≤ 9 * δ ^ 2 / 4 := by
      rw [hB] at hpos_lt_sq
      exact hpos_lt_sq
    have hle : 2 * ε + 2 * r ^ 2 ≤ ‖negPart hk y‖ ^ 2 + ‖posPart hk y‖ ^ 2 := by
      rw [hnorm] at hy
      exact hy
    have hneg : 4 * ε ≤ ‖negPart hk y‖ ^ 2 := by
      have h1 : 2 * ε + 2 * r ^ 2 - 9 * δ ^ 2 / 4 ≤ ‖negPart hk y‖ ^ 2 := by
        nlinarith [hle, hpos_lt_sq']
      have h2 : 4 * ε ≤ 2 * ε + 2 * r ^ 2 - 9 * δ ^ 2 / 4 := by
        have h4 : 2 * r ^ 2 ≥ 2 * ε + 9 * δ ^ 2 / 4 := by
          nlinarith [hr]
        nlinarith
      nlinarith [h1, h2]
    have hmu : modMu ε (‖negPart hk y‖ ^ 2) = 0 := modMu_zero hε hneg
    simp [hmu]

theorem eventually_morseCollarTopLevel_eq_zero_of_chartBoundary_modified {m k : ℕ} (hk : k ≤ m + 1)
    (c ε δ r : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} {f : M → ℝ}
    (data : MorseChart (m + 1) k hk c I f)
    (hε : 0 < ε) (hδ : 0 < δ)
    (hr : r ^ 2 ≥ ε + 9 * δ ^ 2 / 8)
    (hεr : Real.sqrt (2 * ε + 2 * r ^ 2) < data.R)
    (x : LevelSetSpace (morseModifiedFunction (H := H) (M := M) hk c ε δ data.R data.χ f) (c - ε))
    (hx : x.1 ∉ data.χ '' {y : MorseModel (m + 1) | morseNorm (m + 1) y < data.R})
    (hcl : x.1 ∈ closure (data.χ '' {y : MorseModel (m + 1) | morseNorm (m + 1) y < data.R})) :
    ∀ᶠ y in nhds x, morseCollarTopLevel hk c ε r data y = 0 := by
  let S : Set M := data.χ '' {y : MorseModel (m + 1) | morseNorm (m + 1) y ≤ data.R}
  have hmem : x.1 ∈ S := by
    have hclosed : IsClosed S := by
      have hcomp : IsCompact ({y : MorseModel (m + 1) | morseNorm (m + 1) y ≤ data.R}) :=
        isCompact_morseCollarClosedBall (m := m) data.R
      have hsrc : ∀ y ∈ ({y : MorseModel (m + 1) | morseNorm (m + 1) y ≤ data.R} :
          Set (MorseModel (m + 1))), y ∈ data.χ.source := by
        intro y hy
        exact data.hχsrc y hy
      exact IsCompact.image_of_continuousOn hcomp (data.χ.continuousOn_toFun.mono
        (fun y hy => hsrc y hy)) |>.isClosed
    have hsub : data.χ '' {y : MorseModel (m + 1) | morseNorm (m + 1) y < data.R} ⊆ S := by
      intro y hy
      rcases hy with ⟨w, hw, hwy⟩
      exact ⟨w, (show morseNorm (m + 1) w ≤ data.R from le_of_lt hw), hwy⟩
    exact ((closure_mono hsub).trans hclosed.closure_subset) hcl
  let φ : {y : MorseModel (m + 1) | morseNorm (m + 1) y ≤ data.R} ≃ₜ
      (data.χ '' {y : MorseModel (m + 1) | morseNorm (m + 1) y ≤ data.R}) :=
    morseCollarChartBallHomeo (hk := hk) (c := c) (data := data)
  let O : Set {y : MorseModel (m + 1) | morseNorm (m + 1) y ≤ data.R} :=
    {y : {y : MorseModel (m + 1) | morseNorm (m + 1) y ≤ data.R} |
      Real.sqrt (2 * ε + 2 * r ^ 2) < morseNorm (m + 1) y.1}
  have hO : O ∈ nhds (φ.invFun ⟨x.1, hmem⟩) := by
    have hlt : Real.sqrt (2 * ε + 2 * r ^ 2) < morseNorm (m + 1) (φ.invFun ⟨x.1, hmem⟩).1 := by
      have hwR : data.R ≤ morseNorm (m + 1) (φ.invFun ⟨x.1, hmem⟩).1 := by
        by_contra hnot
        have hwlt : morseNorm (m + 1) (φ.invFun ⟨x.1, hmem⟩).1 < data.R := lt_of_not_ge hnot
        have hwχ : data.χ ((φ.invFun ⟨x.1, hmem⟩).1) = x.1 := by
          exact congrArg Subtype.val (φ.right_inv ⟨x.1, hmem⟩)
        exact hx ⟨(φ.invFun ⟨x.1, hmem⟩).1, hwlt, hwχ⟩
      have hle : morseNorm (m + 1) (φ.invFun ⟨x.1, hmem⟩).1 ≤ data.R :=
        (φ.invFun ⟨x.1, hmem⟩).2
      have hnorm : morseNorm (m + 1) (φ.invFun ⟨x.1, hmem⟩).1 = data.R :=
        le_antisymm hle hwR
      rw [hnorm]
      exact hεr
    exact IsOpen.mem_nhds (isOpen_lt continuous_const (by
      dsimp [morseNorm]
      exact (continuous_norm.comp (PiLp.continuous_toLp (p := (2 : ENNReal))
        (β := fun _ : Fin (m + 1) => ℝ))).comp continuous_subtype_val)) hlt
  have hpre : φ.invFun ⁻¹' O ∈ nhds (⟨x.1, hmem⟩ : S) :=
    φ.continuous_invFun.continuousAt.preimage_mem_nhds hO
  rcases (mem_nhds_subtype S ⟨x.1, hmem⟩ (φ.invFun ⁻¹' O)).mp hpre with ⟨u, hu, husub⟩
  refine Filter.mem_of_superset
    (continuous_subtype_val.continuousAt.preimage_mem_nhds hu) (by
      intro y hy
      by_cases hychart : y.1 ∈ data.χ '' {z : MorseModel (m + 1) | morseNorm (m + 1) z < data.R}
      · have hyimage : y.1 ∈ S := by
          rcases hychart with ⟨w, hw, hwy⟩
          exact ⟨w, (show morseNorm (m + 1) w ≤ data.R from le_of_lt hw), hwy⟩
        have hO' : φ.invFun ⟨y.1, hyimage⟩ ∈ O := by
          exact husub (by
            change y.1 ∈ u
            simpa using hy)
        change morseCollarTopLevel hk c ε r data y = 0
        rw [morseCollarTopLevel_eq_on_chart hk c ε r data y hychart]
        have hwbig : Real.sqrt (2 * ε + 2 * r ^ 2) < morseNorm (m + 1) (data.χ.symm y.1) := by
          have hφ : (φ.invFun ⟨y.1, hyimage⟩).1 = data.χ.symm y.1 := by
            dsimp [φ]
            rfl
          change Real.sqrt (2 * ε + 2 * r ^ 2) < morseNorm (m + 1) (φ.invFun ⟨y.1, hyimage⟩).1 at hO'
          rw [hφ] at hO'
          exact hO'
        have hpos : r ^ 2 ≤ ‖posPart hk (data.χ.symm y.1)‖ ^ 2 := by
          rcases hychart with ⟨w, hw, hwy⟩
          have hsrc : w ∈ data.χ.source := data.hχsrc w (le_of_lt hw)
          have hsymm : data.χ.symm y.1 = w := by
            rw [← hwy]
            exact data.χ.left_inv hsrc
          rw [hsymm]
          have hlevel : morseNormalForm hk c w = c - ε := by
            have hg : morseModifiedFunction (H := H) (M := M) hk c ε δ data.R data.χ f (data.χ w) = c - ε := by
              rw [hwy]
              exact y.2
            have hgmod : morseModifiedFunction (H := H) (M := M) hk c ε δ data.R data.χ f (data.χ w) =
                modifiedNormalForm hk c ε δ w := by
              dsimp [morseModifiedFunction]
              rw [if_pos (data.χ.map_source (data.hχsrc w (le_of_lt hw)))]
              rw [data.χ.left_inv (data.hχsrc w (le_of_lt hw))]
              rw [if_pos (le_of_lt hw)]
            have hbig : 2 * ε + 2 * r ^ 2 ≤ morseNorm (m + 1) w ^ 2 := by
              have habs : |Real.sqrt (2 * ε + 2 * r ^ 2)| < |morseNorm (m + 1) w| := by
                rw [abs_of_nonneg (Real.sqrt_nonneg _), abs_of_nonneg (norm_nonneg _)]
                simpa [hsymm] using hwbig
              have hsq : (Real.sqrt (2 * ε + 2 * r ^ 2)) ^ 2 < morseNorm (m + 1) w ^ 2 :=
                (sq_lt_sq).mpr habs
              rw [Real.sq_sqrt (by nlinarith [hε, sq_nonneg r])] at hsq
              exact le_of_lt hsq
            have hmod : modifiedNormalForm hk c ε δ w = morseNormalForm hk c w :=
              modifiedNormalForm_eq_of_norm_large hk c ε δ r hε hδ hr w hbig
            rw [hgmod, hmod] at hg
            exact hg
          have hsplit := morseNormalForm_split hk c w
          have hnorm2 : morseNorm (m + 1) w ^ 2 = ‖posPart hk w‖ ^ 2 + ‖negPart hk w‖ ^ 2 := by
            simpa [add_comm] using (morseNorm_sq_eq_negPart_add_posPart hk w)
          have hle : ‖posPart hk w‖ ^ 2 - ‖negPart hk w‖ ^ 2 = -2 * ε := by
            rw [hsplit] at hlevel
            nlinarith [hlevel]
          have hR2 : 2 * ε + 2 * r ^ 2 < morseNorm (m + 1) w ^ 2 := by
            have habs : |Real.sqrt (2 * ε + 2 * r ^ 2)| < |morseNorm (m + 1) w| := by
              rw [abs_of_nonneg (Real.sqrt_nonneg _), abs_of_nonneg (norm_nonneg _)]
              simpa [hsymm] using hwbig
            have hsq : (Real.sqrt (2 * ε + 2 * r ^ 2)) ^ 2 < morseNorm (m + 1) w ^ 2 :=
              (sq_lt_sq).mpr habs
            rwa [Real.sq_sqrt (by nlinarith [hε, sq_nonneg r])] at hsq
          nlinarith [hle, hnorm2, hR2]
        have hle0 : (r ^ 2 - ‖posPart hk (data.χ.symm y.1)‖ ^ 2) / 2 ≤ 0 := by
          nlinarith [hpos]
        exact max_eq_left hle0
      · change morseCollarTopLevel hk c ε r data y = 0
        exact morseCollarTopLevel_eq_zero hk c ε r data y hychart)

theorem continuous_morseCollarTopLevel_modified {m k : ℕ} (hk : k ≤ m + 1) (c ε δ r : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} {f : M → ℝ}
    (data : MorseChart (m + 1) k hk c I f)
    (hε : 0 < ε) (hδ : 0 < δ)
    (hr : r ^ 2 ≥ ε + 9 * δ ^ 2 / 8)
    (hεr : Real.sqrt (2 * ε + 2 * r ^ 2) < data.R) :
    Continuous (morseCollarTopLevel hk c ε r data :
      LevelSetSpace (morseModifiedFunction (H := H) (M := M) hk c ε δ data.R data.χ f) (c - ε) → ℝ) := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : x.1 ∈ data.χ '' {y : MorseModel (m + 1) | morseNorm (m + 1) y < data.R}
  · have hsrc : x.1 ∈ data.χ.target := by
      rcases hx with ⟨w, hw, hwx⟩
      rw [← hwx]
      exact data.χ.map_source (data.hχsrc w (le_of_lt hw))
    have hsymm : ContinuousAt data.χ.symm x.1 := by
      exact (data.χ.continuousOn_invFun x.1 hsrc).continuousAt
        (IsOpen.mem_nhds data.χ.open_target hsrc)
    have h1 : ContinuousAt (fun y : LevelSetSpace (morseModifiedFunction (H := H) (M := M) hk c ε δ data.R data.χ f) (c - ε) => data.χ.symm y.1) x :=
      hsymm.comp continuous_subtype_val.continuousAt
    have h2 : ContinuousAt (fun y : LevelSetSpace (morseModifiedFunction (H := H) (M := M) hk c ε δ data.R data.χ f) (c - ε) =>
        ‖posPart hk (data.χ.symm y.1)‖ ^ 2) x := by
      exact ((continuous_norm.continuousAt.comp (continuous_posPart hk).continuousAt).comp h1).pow 2
    have hf : ContinuousAt (fun y : LevelSetSpace (morseModifiedFunction (H := H) (M := M) hk c ε δ data.R data.χ f) (c - ε) =>
        (r ^ 2 - ‖posPart hk (data.χ.symm y.1)‖ ^ 2) / 2) x := by
      exact (continuousAt_const.sub h2).div continuousAt_const (by norm_num : (2 : ℝ) ≠ 0)
    have hg : ContinuousAt (fun y : LevelSetSpace (morseModifiedFunction (H := H) (M := M) hk c ε δ data.R data.χ f) (c - ε) =>
        max 0 ((r ^ 2 - ‖posPart hk (data.χ.symm y.1)‖ ^ 2) / 2)) x :=
      continuousAt_const.max hf
    refine hg.congr_of_eventuallyEq ?_
    have hxopen : x ∈ morseCollarChartSet hk c ε r data := hx
    exact Filter.mem_of_superset ((isOpen_morseCollarChartSet hk c ε r data).mem_nhds hxopen) (by
      intro y hy
      change morseCollarTopLevel hk c ε r data y =
        max 0 ((r ^ 2 - ‖posPart hk (data.χ.symm y.1)‖ ^ 2) / 2)
      exact morseCollarTopLevel_eq_on_chart hk c ε r data y hy)
  · have hzero : morseCollarTopLevel hk c ε r data x = 0 :=
      morseCollarTopLevel_eq_zero hk c ε r data x hx
    change Filter.Tendsto (morseCollarTopLevel hk c ε r data) (nhds x)
      (nhds (morseCollarTopLevel hk c ε r data x))
    rw [hzero]
    exact Metric.tendsto_nhds.mpr (by
      intro δm hδm
      by_cases hcl : x.1 ∈ closure (data.χ '' {y : MorseModel (m + 1) |
          morseNorm (m + 1) y < data.R})
      · exact Filter.mem_of_superset
          (eventually_morseCollarTopLevel_eq_zero_of_chartBoundary_modified (hk := hk) (c := c) (ε := ε) (δ := δ) (hδ := hδ) (hr := hr)
            (r := r) (data := data) (hε := hε) (hεr := hεr) x hx hcl) (by
            intro y hy
            change morseCollarTopLevel hk c ε r data y = 0 at hy
            change dist (morseCollarTopLevel hk c ε r data y) 0 < δm
            rw [hy]
            simpa [Real.dist_eq] using hδm)
      · have hopen : IsOpen (closure (data.χ '' {y : MorseModel (m + 1) |
            morseNorm (m + 1) y < data.R}))ᶜ :=
          (isClosed_closure).isOpen_compl
        refine Filter.mem_of_superset
          (continuous_subtype_val.continuousAt.preimage_mem_nhds (hopen.mem_nhds hcl)) (by
            intro y hy
            have hychart : y.1 ∉ data.χ '' {z : MorseModel (m + 1) |
                morseNorm (m + 1) z < data.R} := by
              intro hyc
              exact hy (subset_closure hyc)
            change dist (morseCollarTopLevel hk c ε r data y) 0 < δm
            rw [morseCollarTopLevel_eq_zero (hk := hk) (c := c) (ε := ε) (r := r)
              (data := data) y hychart]
            simpa [Real.dist_eq] using hδm))

theorem morseModifiedSublevel_union_handleImage_eq {n k : ℕ} (hk : k ≤ n) (c ε δ r R : ℝ)
    (hε : 0 < ε) (hδ : 0 < δ) (hr : 3 * δ / 2 ≤ r)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    (χ : OpenPartialHomeomorph (MorseModel n) M) (f : M → ℝ)
    (hnorm : ∀ y : MorseModel n, morseNorm n y ≤ R → f (χ y) = morseNormalForm hk c y)
    (hχsrc : ∀ y : MorseModel n, morseNorm n y ≤ R → y ∈ χ.source) :
    {x : M | morseModifiedFunction (H := H) (M := M) hk c ε δ R χ f x ≤ c - ε} ∪
        χ '' (modelHandle hk ε r : Set (MorseModel n)) =
      {x : M | f x ≤ c - ε} ∪ χ '' (modelHandle hk ε r : Set (MorseModel n)) := by
  let g : M → ℝ := morseModifiedFunction (H := H) (M := M) hk c ε δ R χ f
  ext x
  constructor
  · intro hx
    rcases hx with hg | hh
    · by_cases hC : x ∈ χ '' {y : MorseModel n | morseNorm n y ≤ R}
      · rcases hC with ⟨y, hy, hxy⟩
        have hsymm : χ.symm x = y := by
          rw [← hxy]
          exact χ.left_inv (hχsrc y hy)
        have hgx : g x = modifiedNormalForm hk c ε δ y := by
          dsimp [g, morseModifiedFunction]
          rw [← hxy, if_pos (χ.map_source (hχsrc y hy)), χ.left_inv (hχsrc y hy)]
          rw [if_pos (by simpa using hy)]
        have hmod : modifiedNormalForm hk c ε δ y ≤ c - ε := by
          rw [← hgx]
          exact hg
        have hmem : y ∈ {y : MorseModel n | morseNormalForm hk c y ≤ c - ε} ∪
            (modelHandle hk ε r : Set (MorseModel n)) :=
          modifiedSublevel_subset_lower_union_modelHandle hk c ε δ r hε hδ hr (by
            exact hmod)
        rcases hmem with hlow | hh
        · have hfx : f x ≤ c - ε := by
            rw [← hxy]
            rw [hnorm y hy]
            exact hlow
          exact Or.inl hfx
        · exact Or.inr (by
            rw [← hxy]
            exact ⟨y, hh, rfl⟩)
      · have hgx : g x = f x := by
          dsimp [g, morseModifiedFunction]
          by_cases hxt : x ∈ χ.target
          · rw [if_pos hxt]
            have hnot : ¬ morseNorm n (χ.symm x) ≤ R := by
              intro hle
              apply hC
              exact ⟨χ.symm x, hle, χ.right_inv hxt⟩
            rw [if_neg hnot]
          · rw [if_neg hxt]
        exact Or.inl (by
          change f x ≤ c - ε
          rw [← hgx]
          exact hg)
    · exact Or.inr hh
  · intro hx
    rcases hx with hf | hh
    · exact Or.inl (le_trans (morseModifiedFunction_le_f (H := H) (M := M) hk c ε δ R hε χ f hnorm x) hf)
    · exact Or.inr hh

noncomputable def morseHandleAttachmentHomeoUpper {m k : ℕ} (hk : k ≤ m + 1) (c ε r δ η : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} [I.Boundaryless]
    [IsManifold I (⊤ : WithTop ℕ∞) M] {f : M → ℝ}
    (data : MorseChart (m + 1) k hk c I f)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) f)
    (hε : 0 < ε) (hδ : 0 < δ) (hη : 0 < η)
    (hεr' : Real.sqrt (2 * ε + 2 * r ^ 2) < data.R)
    (hδε : 9 * δ ^ 2 < 4 * ε)
    (hr2 : r ^ 2 = 2 * ε)
    (hrδ : 3 * δ / 2 ≤ r)
    (g : M → ℝ) (hg_eq : g = morseModifiedFunction (H := H) (M := M) hk c ε δ data.R data.χ f)
    (hg : ContMDiff I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) g)
    (v : (x : M) → TangentSpace I x)
    (hv : ContMDiff I (I.prod 𝓘(ℝ, MorseModel (m + 1))) ∞
      (fun x : M => (⟨x, v x⟩ : TangentBundle I M)))
    (hsupp : IsCompact (tsupport v))
    (hdfOn : ∀ x ∈ g ⁻¹' Set.Icc (c - ε - η) (c + r ^ 2 / 2),
      (NormedSpace.fromTangentSpace (g x)) ((mfderiv I 𝓘(ℝ, ℝ) g x) (v x)) = -1)
    (hrate : ∀ x,
      -1 ≤ (NormedSpace.fromTangentSpace (g x)) ((mfderiv I 𝓘(ℝ, ℝ) g x) (v x)) ∧
      (NormedSpace.fromTangentSpace (g x)) ((mfderiv I 𝓘(ℝ, ℝ) g x) (v x)) ≤ 0)
    (hHandleInterval : ∀ (w : MorseModel (m + 1)), w ∈ modelHandle hk ε r →
      g (data.χ w) ∈ Set.Icc (c - ε - η) (c + r ^ 2 / 2))
    (hHandleUpper : ∀ (w : MorseModel (m + 1)), w ∈ modelHandle hk ε r →
      g (data.χ w) ≤ c + r ^ 2 / 2)
    (hflowTop : ∀ (w : MorseModel (m + 1)) (hw : w ∈ modelHandle hk ε r),
      morseCollarTopLevel hk c ε r data
        (morseCollarFlowBase hk c ε r η hg hε hη v hv hsupp hdfOn hrate (data.χ w)
          (hHandleInterval w hw)) ≥
        g (data.χ w) - c + ε)
    (hflowMem : ∀ y : SublevelSpace g (c + r ^ 2 / 2),
      morseCollarMap hk c ε r η data hg hε (le_of_lt hη) v hv hsupp hdfOn hrate y ∈
        sublevel g (c - ε) ∪ Set.range (handleEmbedding hk c ε r data)) :
    Handle.AdjunctionSpace k (m + 1 - k) (morseAttachingEmbedding hk c ε r data hε (le_of_lt hεr')) ≃ₜ
      SublevelSpace f (c + r ^ 2 / 2) := by
  let hcontf : Continuous f := hf.continuous
  have hrpos : 0 < r := by nlinarith [hδ, hrδ]
  have hr' : r ^ 2 ≥ ε + 9 * δ ^ 2 / 8 := by
    rw [hr2]
    nlinarith [hδε, hε, sq_nonneg δ]
  have hTopCont : Continuous (morseCollarTopLevel hk c ε r data :
      LevelSetSpace (morseModifiedFunction (H := H) (M := M) hk c ε δ data.R data.χ f) (c - ε) → ℝ) :=
    continuous_morseCollarTopLevel_modified hk c ε δ r data hε hδ hr' hεr'
  have hTopContg : Continuous (morseCollarTopLevel hk c ε r data : LevelSetSpace g (c - ε) → ℝ) := by
    change Continuous (morseCollarTopLevel hk c ε r data : {x : M // g x = c - ε} → ℝ)
    rw [hg_eq]
    exact hTopCont
  have hcontg : Continuous g := hg.continuous
  have hrange : Set.range (handleEmbedding hk c ε r data) =
      data.χ '' (modelHandle hk ε r : Set (MorseModel (m + 1))) :=
    range_handleEmbedding hk c ε r data hε hrpos
  have hunion : {x : M | g x ≤ c - ε} ∪
        data.χ '' (modelHandle hk ε r : Set (MorseModel (m + 1))) =
      {x : M | f x ≤ c - ε} ∪
        data.χ '' (modelHandle hk ε r : Set (MorseModel (m + 1))) := by
    have h := morseModifiedSublevel_union_handleImage_eq (n := m + 1) hk c ε δ r data.R hε hδ hrδ
      (H := H) (M := M) data.χ f data.hnorm data.hχsrc
    simpa [hg_eq] using h
  have h₁set : sublevel f (c - ε) ∪ Set.range (handleEmbedding hk c ε r data) =
      sublevel f (c - ε) ∪ data.χ '' (modelHandle hk ε r : Set (MorseModel (m + 1))) := by
    rw [hrange]
  have h₃set : sublevel g (c - ε) ∪ data.χ '' (modelHandle hk ε r : Set (MorseModel (m + 1))) =
      sublevel g (c - ε) ∪ Set.range (handleEmbedding hk c ε r data) := by
    rw [← hrange]
  have hset : {x : M | g x ≤ c + r ^ 2 / 2} = sublevel f (c + r ^ 2 / 2) := by
    have hident := sublevel_upper_identity_morseModifiedFunction (n := m + 1) hk c ε δ data.R hε hδ hδε
      (H := H) (M := M) data.χ f data.hnorm
    have hlev : c + ε = c + r ^ 2 / 2 := by
      rw [hr2]
      ring
    have hident' : {x : M | morseModifiedFunction (H := H) (M := M) hk c ε δ data.R data.χ f x ≤
        c + r ^ 2 / 2} = sublevel f (c + r ^ 2 / 2) := by
      simpa [hlev] using hident
    simpa [hg_eq] using hident'
  exact (morseHandleAdjunctionHomeoUnion hk c ε r data hε (ne_of_gt hrpos) (le_of_lt hεr') hcontf).trans
    ((subtypeSetHomeomorph h₁set).trans
      (((subtypeSetHomeomorph hunion).symm).trans
        ((subtypeSetHomeomorph h₃set).trans
          ((morseCollarHomeoUnion hk c ε r η data hg hε hη v hv hsupp hdfOn hrate hHandleInterval
            hHandleUpper hflowTop hTopContg hflowMem hcontg).symm.trans
            (subtypeSetHomeomorph hset)))))

private lemma collarLowerAux {m k : ℕ} (hk : k ≤ m + 1) (c ε r η : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} [I.Boundaryless]
    [IsManifold I (⊤ : WithTop ℕ∞) M] {f : M → ℝ}
    {f₀ : M → ℝ} (data : MorseChart (m + 1) k hk c I f₀)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) f)
    (hε : 0 < ε) (hη : 0 < η)
    (v : (x : M) → TangentSpace I x)
    (hv : ContMDiff I (I.prod 𝓘(ℝ, MorseModel (m + 1))) ∞
      (fun x : M => (⟨x, v x⟩ : TangentBundle I M)))
    (hsupp : IsCompact (tsupport v))
    (hdfOn : ∀ x ∈ f ⁻¹' Set.Icc (c - ε - η) (c + r ^ 2 / 2),
      (NormedSpace.fromTangentSpace (f x)) ((mfderiv I 𝓘(ℝ, ℝ) f x) (v x)) = -1)
    (hrate : ∀ x,
      -1 ≤ (NormedSpace.fromTangentSpace (f x)) ((mfderiv I 𝓘(ℝ, ℝ) f x) (v x)) ∧
      (NormedSpace.fromTangentSpace (f x)) ((mfderiv I 𝓘(ℝ, ℝ) f x) (v x)) ≤ 0)
    (hHandleInterval : ∀ (w : MorseModel (m + 1)), w ∈ modelHandle hk ε r →
      f (data.χ w) ∈ Set.Icc (c - ε - η) (c + r ^ 2 / 2))
    (hHandleUpper : ∀ (w : MorseModel (m + 1)), w ∈ modelHandle hk ε r →
      f (data.χ w) ≤ c + r ^ 2 / 2)
    (hflowTop : ∀ (w : MorseModel (m + 1)) (hw : w ∈ modelHandle hk ε r),
      morseCollarTopLevel hk c ε r data
        (morseCollarFlowBase hk c ε r η hf hε hη v hv hsupp hdfOn hrate (data.χ w)
          (hHandleInterval w hw)) ≥
        f (data.χ w) - c + ε)
    (hTopCont : Continuous (morseCollarTopLevel hk c ε r data : LevelSetSpace f (c - ε) → ℝ))
    (hflowMem : ∀ y : SublevelSpace f (c + r ^ 2 / 2),
      morseCollarMap hk c ε r η data hf hε (le_of_lt hη) v hv hsupp hdfOn hrate y ∈
        sublevel f (c - ε) ∪ Set.range (handleEmbedding hk c ε r data))
    (hcont : Continuous f)
    {z : M} (hz : f z ≤ c - ε - η)
    (m : z ∈ sublevel f (c - ε) ∪ Set.range (handleEmbedding hk c ε r data)) :
    ((morseCollarHomeoUnion hk c ε r η data hf hε hη v hv hsupp hdfOn hrate hHandleInterval hHandleUpper
      hflowTop hTopCont hflowMem hcont).symm ⟨z, m⟩).1 = z := by
  simpa using congrArg Subtype.val (morseCollarPreimage_eq_low hk c ε r η data hf hε hη v hv hsupp
    hdfOn hrate hHandleInterval hHandleUpper hflowTop
      (⟨z, m⟩ : {x : M // x ∈ sublevel f (c - ε) ∪ Set.range (handleEmbedding hk c ε r data)}) hz)

theorem morseHandleAttachmentHomeoUpper_lower {m k : ℕ} (hk : k ≤ m + 1) (c ε r δ η : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} [I.Boundaryless]
    [IsManifold I (⊤ : WithTop ℕ∞) M] {f : M → ℝ}
    (data : MorseChart (m + 1) k hk c I f)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) f)
    (hε : 0 < ε) (hδ : 0 < δ) (hη : 0 < η)
    (hεr' : Real.sqrt (2 * ε + 2 * r ^ 2) < data.R)
    (hδε : 9 * δ ^ 2 < 4 * ε)
    (hr2 : r ^ 2 = 2 * ε)
    (hrδ : 3 * δ / 2 ≤ r)
    (g : M → ℝ) (hg_eq : g = morseModifiedFunction (H := H) (M := M) hk c ε δ data.R data.χ f)
    (hg : ContMDiff I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) g)
    (v : (x : M) → TangentSpace I x)
    (hv : ContMDiff I (I.prod 𝓘(ℝ, MorseModel (m + 1))) ∞
      (fun x : M => (⟨x, v x⟩ : TangentBundle I M)))
    (hsupp : IsCompact (tsupport v))
    (hdfOn : ∀ x ∈ g ⁻¹' Set.Icc (c - ε - η) (c + r ^ 2 / 2),
      (NormedSpace.fromTangentSpace (g x)) ((mfderiv I 𝓘(ℝ, ℝ) g x) (v x)) = -1)
    (hrate : ∀ x,
      -1 ≤ (NormedSpace.fromTangentSpace (g x)) ((mfderiv I 𝓘(ℝ, ℝ) g x) (v x)) ∧
      (NormedSpace.fromTangentSpace (g x)) ((mfderiv I 𝓘(ℝ, ℝ) g x) (v x)) ≤ 0)
    (hHandleInterval : ∀ (w : MorseModel (m + 1)), w ∈ modelHandle hk ε r →
      g (data.χ w) ∈ Set.Icc (c - ε - η) (c + r ^ 2 / 2))
    (hHandleUpper : ∀ (w : MorseModel (m + 1)), w ∈ modelHandle hk ε r →
      g (data.χ w) ≤ c + r ^ 2 / 2)
    (hflowTop : ∀ (w : MorseModel (m + 1)) (hw : w ∈ modelHandle hk ε r),
      morseCollarTopLevel hk c ε r data
        (morseCollarFlowBase hk c ε r η hg hε hη v hv hsupp hdfOn hrate (data.χ w)
          (hHandleInterval w hw)) ≥
        g (data.χ w) - c + ε)
    (hflowMem : ∀ y : SublevelSpace g (c + r ^ 2 / 2),
      morseCollarMap hk c ε r η data hg hε (le_of_lt hη) v hv hsupp hdfOn hrate y ∈
        sublevel g (c - ε) ∪ Set.range (handleEmbedding hk c ε r data))
    (x : SublevelSpace f (c - ε - η)) :
    (morseHandleAttachmentHomeoUpper hk c ε r δ η data hf hε hδ hη hεr' hδε hr2 hrδ g hg_eq hg v hv
      hsupp hdfOn hrate hHandleInterval hHandleUpper hflowTop hflowMem
      (Handle.lower (morseAttachingEmbedding hk c ε r data hε (le_of_lt hεr'))
        (⟨x.1, by
          change f x.1 ≤ c - ε
          exact le_trans x.2 (by linarith [hε])⟩ : SublevelSpace f (c - ε)))) =
    ⟨x.1, by
      change f x.1 ≤ c + r ^ 2 / 2
      have hx : f x.1 ≤ c - ε - η := x.2
      have hr2' : 0 ≤ r ^ 2 / 2 := div_nonneg (sq_nonneg r) (by norm_num)
      linarith [hx, hε, hη, hr2']⟩ := by
  apply Subtype.ext
  have hgf : g x.1 ≤ f x.1 := by
    rw [hg_eq]
    exact morseModifiedFunction_le_f hk c ε δ data.R hε data.χ f data.hnorm x.1
  have hglow : g x.1 ≤ c - ε - η := le_trans hgf x.2
  have hrpos : 0 < r := by nlinarith [hδ, hrδ]
  have hr' : r ^ 2 ≥ ε + 9 * δ ^ 2 / 8 := by
    rw [hr2]
    nlinarith [hδε, hε, sq_nonneg δ]
  have hTopContg : Continuous (morseCollarTopLevel hk c ε r data : LevelSetSpace g (c - ε) → ℝ) := by
    have h := continuous_morseCollarTopLevel_modified hk c ε δ r data hε hδ hr' hεr'
    change Continuous (morseCollarTopLevel hk c ε r data : {x : M // g x = c - ε} → ℝ)
    rw [hg_eq]
    exact h
  have hcontg : Continuous g := hg.continuous
  have hrange : Set.range (handleEmbedding hk c ε r data) =
      data.χ '' (modelHandle hk ε r : Set (MorseModel (m + 1))) :=
    range_handleEmbedding hk c ε r data hε hrpos
  have hunion : {x : M | g x ≤ c - ε} ∪
        data.χ '' (modelHandle hk ε r : Set (MorseModel (m + 1))) =
      {x : M | f x ≤ c - ε} ∪
        data.χ '' (modelHandle hk ε r : Set (MorseModel (m + 1))) := by
    have h := morseModifiedSublevel_union_handleImage_eq (n := m + 1) hk c ε δ r data.R hε hδ hrδ
      (H := H) (M := M) data.χ f data.hnorm data.hχsrc
    simpa [hg_eq] using h
  have h₁set : sublevel f (c - ε) ∪ Set.range (handleEmbedding hk c ε r data) =
      sublevel f (c - ε) ∪ data.χ '' (modelHandle hk ε r : Set (MorseModel (m + 1))) := by
    rw [hrange]
  have h₃set : sublevel g (c - ε) ∪ data.χ '' (modelHandle hk ε r : Set (MorseModel (m + 1))) =
      sublevel g (c - ε) ∪ Set.range (handleEmbedding hk c ε r data) := by
    rw [← hrange]
  have hset : {x : M | g x ≤ c + r ^ 2 / 2} = sublevel f (c + r ^ 2 / 2) := by
    have hident := sublevel_upper_identity_morseModifiedFunction (n := m + 1) hk c ε δ data.R hε hδ hδε
      (H := H) (M := M) data.χ f data.hnorm
    have hlev : c + ε = c + r ^ 2 / 2 := by
      rw [hr2]
      ring
    have hident' : {x : M | morseModifiedFunction (H := H) (M := M) hk c ε δ data.R data.χ f x ≤
        c + r ^ 2 / 2} = sublevel f (c + r ^ 2 / 2) := by
      simpa [hlev] using hident
    simpa [hg_eq] using hident'
  let x₀ : SublevelSpace f (c - ε) := ⟨x.1, by
    change f x.1 ≤ c - ε
    exact le_trans x.2 (by linarith [hε])⟩
  change ((morseHandleAdjunctionHomeoUnion hk c ε r data hε (ne_of_gt hrpos) (le_of_lt hεr')
      hf.continuous).trans
    ((subtypeSetHomeomorph h₁set).trans
      (((subtypeSetHomeomorph hunion).symm).trans
        ((subtypeSetHomeomorph h₃set).trans
          ((morseCollarHomeoUnion hk c ε r η data hg hε hη v hv hsupp hdfOn hrate hHandleInterval
            hHandleUpper hflowTop hTopContg hflowMem hcontg).symm.trans
            (subtypeSetHomeomorph hset)))))
      (Handle.lower (morseAttachingEmbedding hk c ε r data hε (le_of_lt hεr')) x₀)).1 = x.1
  erw [Homeomorph.trans_apply]
  erw [Homeomorph.trans_apply]
  erw [Homeomorph.trans_apply]
  erw [Homeomorph.trans_apply]
  erw [Homeomorph.trans_apply]
  rw [morseHandleAdjunctionHomeoUnion_lower hk c ε r data hε (ne_of_gt hrpos) (le_of_lt hεr')
    hf.continuous x₀]
  change ((morseCollarHomeoUnion hk c ε r η data hg hε hη v hv hsupp hdfOn hrate hHandleInterval
      hHandleUpper hflowTop hTopContg hflowMem hcontg).symm
        ((subtypeSetHomeomorph h₃set)
          ((subtypeSetHomeomorph hunion).symm ((subtypeSetHomeomorph h₁set) ⟨x₀.1, _⟩)))).1 = x.1
  simp only [subtypeSetHomeomorph]
  simpa using collarLowerAux hk c ε r η data hg hε hη v hv hsupp hdfOn hrate hHandleInterval
    hHandleUpper hflowTop hTopContg hflowMem hcontg (z := x.1) hglow _

def morseChartBallImage {m k : ℕ} (hk : k ≤ m + 1) (c : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} {f : M → ℝ}
    (data : MorseChart (m + 1) k hk c I f) : Set M :=
  data.χ '' {y : MorseModel (m + 1) | morseNorm (m + 1) y < data.R}

def morseChartCoreBallImage {m k : ℕ} (hk : k ≤ m + 1) (c : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} {f : M → ℝ}
    (data : MorseChart (m + 1) k hk c I f) : Set M :=
  {x : M | x ∈ data.χ.target ∧ ‖negPart hk (data.χ.symm x)‖ < data.R / 2}

noncomputable def morseSharpUnionRound {m k : ℕ} (hk : k ≤ m + 1) (c ε r δ : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} {f : M → ℝ}
    (data : MorseChart (m + 1) k hk c I f)
    (x : M) : M := by
  classical
  exact if hx : x ∈ morseChartBallImage hk c data then
    data.χ (modelSharpUnionRound hk ε r δ (data.χ.symm x))
  else x

noncomputable def morseSharpUnionUnround {m k : ℕ} (hk : k ≤ m + 1) (c ε r δ : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} {f : M → ℝ}
    (data : MorseChart (m + 1) k hk c I f)
    (x : M) : M := by
  classical
  exact if hx : x ∈ morseChartCoreBallImage hk c data ∩ morseChartBallImage hk c data then
    data.χ (modelSharpUnionUnround hk ε r δ (data.χ.symm x))
  else x

noncomputable def morseRoundedAttachment {m k : ℕ} (hk : k ≤ m + 1) (c ε r δ : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} {f : M → ℝ}
    (data : MorseChart (m + 1) k hk c I f) : Set M :=
  data.χ '' (modelAttachedRegion hk ε r δ ∩ {y : MorseModel (m + 1) | ‖negPart hk y‖ < data.R / 2}) ∪
    (sublevel f (c - ε) ∩
      (morseChartCoreBallImage hk c data ∩ morseChartBallImage hk c data)ᶜ)

theorem range_handleEmbedding_subset_ballImage {m k : ℕ} (hk : k ≤ m + 1) (c ε r : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} {f : M → ℝ}
    (data : MorseChart (m + 1) k hk c I f)
    (hε : 0 < ε)
    (hεr' : Real.sqrt (2 * ε + 2 * r ^ 2) < data.R / 2) :
    Set.range (handleEmbedding hk c ε r data) ⊆ morseChartCoreBallImage hk c data := by
  intro x hx
  rcases hx with ⟨d, hd⟩
  rw [← hd]
  dsimp [morseChartCoreBallImage]
  have hsrc : modelHandleMap hk ε r d ∈ data.χ.source := data.hχsrc (modelHandleMap hk ε r d)
    (le_trans (modelHandleMap_norm_le hk ε r (le_of_lt hε) d)
      (le_trans (le_of_lt hεr') (by nlinarith [data.hRpos] : data.R / 2 ≤ data.R)))
  constructor
  · change data.χ (modelHandleMap hk ε r d) ∈ data.χ.target
    exact data.χ.map_source hsrc
  · change ‖negPart hk (data.χ.symm (data.χ (modelHandleMap hk ε r d)))‖ < data.R / 2
    rw [data.χ.left_inv hsrc]
    have hle : ‖negPart hk (modelHandleMap hk ε r d)‖ ^ 2 ≤ 2 * ε + r ^ 2 :=
      modelHandleMap_negPart_norm_sq_le hk ε r (le_of_lt hε) d
    have hlt : 2 * ε + r ^ 2 < (data.R / 2) ^ 2 := by
      have h1 : 2 * ε + 2 * r ^ 2 < (data.R / 2) ^ 2 := by
        have hsc : (Real.sqrt (2 * ε + 2 * r ^ 2)) ^ 2 < (data.R / 2) ^ 2 := by
          have habs : |Real.sqrt (2 * ε + 2 * r ^ 2)| < |data.R / 2| := by
            rw [abs_of_nonneg (Real.sqrt_nonneg _)]
            rw [abs_of_nonneg (div_nonneg (le_of_lt data.hRpos) (by norm_num))]
            exact hεr'
          exact sq_lt_sq.mpr habs
        simpa [Real.sq_sqrt (by positivity : 0 ≤ 2 * ε + 2 * r ^ 2)] using hsc
      nlinarith [h1, sq_nonneg r]
    have hsq : ‖negPart hk (modelHandleMap hk ε r d)‖ ^ 2 < (data.R / 2) ^ 2 :=
      lt_of_le_of_lt hle hlt
    have habs := sq_lt_sq.mp hsq
    rwa [abs_of_nonneg (norm_nonneg (negPart hk (modelHandleMap hk ε r d))),
      abs_of_nonneg (by nlinarith [data.hRpos] : 0 ≤ data.R / 2)] at habs

theorem chartSymm_norm_lt_of_mem_ballImage {m k : ℕ} (hk : k ≤ m + 1) (c : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} {f : M → ℝ}
    (data : MorseChart (m + 1) k hk c I f)
    {x : M} (hx : x ∈ morseChartBallImage hk c data) :
    morseNorm (m + 1) (data.χ.symm x) < data.R := by
  rcases hx with ⟨y, hy, hxy⟩
  have hsrc0 : y ∈ data.χ.source := data.hχsrc y (le_of_lt hy)
  have hsymm : data.χ.symm x = y := by
    rw [← hxy]
    exact data.χ.left_inv hsrc0
  rwa [hsymm]

theorem chartSymm_mem_source_of_mem_ballImage {m k : ℕ} (hk : k ≤ m + 1) (c : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} {f : M → ℝ}
    (data : MorseChart (m + 1) k hk c I f)
    {x : M} (hx : x ∈ morseChartBallImage hk c data) :
    data.χ.symm x ∈ data.χ.source := by
  exact data.hχsrc (data.χ.symm x) (le_of_lt (chartSymm_norm_lt_of_mem_ballImage hk c data hx))

theorem chartSymm_right_inv_of_mem_ballImage {m k : ℕ} (hk : k ≤ m + 1) (c : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} {f : M → ℝ}
    (data : MorseChart (m + 1) k hk c I f)
    {x : M} (hx : x ∈ morseChartBallImage hk c data) :
    data.χ (data.χ.symm x) = x := by
  exact data.χ.right_inv (by
    rcases hx with ⟨y, hy, hxy⟩
    have hsrc0 : y ∈ data.χ.source := data.hχsrc y (le_of_lt hy)
    rw [← hxy]
    exact data.χ.map_source hsrc0)

theorem chartSymm_mem_target_of_mem_ballImage {m k : ℕ} (hk : k ≤ m + 1) (c : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} {f : M → ℝ}
    (data : MorseChart (m + 1) k hk c I f)
    {x : M} (hx : x ∈ morseChartBallImage hk c data) :
    x ∈ data.χ.target := by
  rcases hx with ⟨y, hy, hxy⟩
  have hsrc0 : y ∈ data.χ.source := data.hχsrc y (le_of_lt hy)
  rw [← hxy]
  exact data.χ.map_source hsrc0

theorem chartSymm_mem_sharpUnion_model {m k : ℕ} (hk : k ≤ m + 1) (c ε r : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} {f : M → ℝ}
    (data : MorseChart (m + 1) k hk c I f)
    (hε : 0 < ε)
    (hεr' : Real.sqrt (2 * ε + 2 * r ^ 2) < data.R / 2)
    {x : M} (hx : x ∈ morseChartBallImage hk c data)
    (hxU : x ∈ sublevel f (c - ε) ∪ Set.range (handleEmbedding hk c ε r data)) :
    data.χ.symm x ∈
      (sublevel (morseNormalForm hk c) (c - ε) : Set (MorseModel (m + 1))) ∪ modelHandle hk ε r := by
  rcases hxU with hf | hh
  · left
    have hfx : f x = morseNormalForm hk c (data.χ.symm x) := by
      rcases hx with ⟨y, hy, hxy⟩
      have hsrc0 : y ∈ data.χ.source := data.hχsrc y (le_of_lt hy)
      have hxy' : data.χ.symm x = y := by
        rw [← hxy]
        exact data.χ.left_inv hsrc0
      calc
        f x = morseNormalForm hk c y := by
          rw [← hxy]
          exact data.hnorm y (le_of_lt hy)
        _ = morseNormalForm hk c (data.χ.symm x) := by rw [hxy']
    change morseNormalForm hk c (data.χ.symm x) ≤ c - ε
    rw [← hfx]
    exact (by simpa [sublevel] using hf : f x ≤ c - ε)
  · right
    rcases hh with ⟨d, hd⟩
    have hd' : data.χ.symm x = modelHandleMap hk ε r d := by
      rw [← hd]
      have hsrc' : modelHandleMap hk ε r d ∈ data.χ.source :=
        data.hχsrc (modelHandleMap hk ε r d)
          (le_trans (modelHandleMap_norm_le hk ε r (le_of_lt hε) d)
            (le_trans (le_of_lt hεr') (by nlinarith [data.hRpos] : data.R / 2 ≤ data.R)))
      exact data.χ.left_inv hsrc'
    rw [hd']
    exact modelHandleMap_mem hk ε r (le_of_lt hε) d

theorem negPart_norm_sq_ge_of_lower_bound {m k : ℕ} (hk : k ≤ m + 1) (c ε r δ : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} {f : M → ℝ}
    (data : MorseChart (m + 1) k hk c I f)
    (hbig : r ^ 2 + ε + δ ≤ data.R ^ 2 / 8)
    {x : M} (hx : x ∈ sublevel f (c - ε))
    {y : MorseModel (m + 1)} (hxy : data.χ y = x)
    (hynorm : morseNorm (m + 1) y ≤ data.R)
    (hyfar : data.R / 2 ≤ ‖negPart hk y‖) :
    r ^ 2 + 2 * ε + δ ≤ ‖negPart hk y‖ ^ 2 := by
  have hlower : ‖posPart hk y‖ ^ 2 ≤ ‖negPart hk y‖ ^ 2 - 2 * ε := by
    have hf' : morseNormalForm hk c y ≤ c - ε := by
      rw [← data.hnorm y hynorm]
      rw [hxy]
      exact (by simpa [sublevel] using hx : f x ≤ c - ε)
    rw [morseNormalForm_split] at hf'
    nlinarith
  have hnorm_sq : ‖negPart hk y‖ ^ 2 + ‖posPart hk y‖ ^ 2 ≥ (data.R / 2) ^ 2 := by
    have hsqn : (data.R / 2) ^ 2 ≤ ‖negPart hk y‖ ^ 2 := by
      have hR2nonneg : 0 ≤ data.R / 2 := by nlinarith [data.hRpos]
      exact sq_le_sq.mpr (by
        rw [abs_of_nonneg hR2nonneg, abs_of_nonneg (norm_nonneg (negPart hk y))]
        exact hyfar)
    nlinarith [hsqn, sq_nonneg (‖posPart hk y‖)]
  nlinarith [hbig, hlower, hnorm_sq]

theorem morseSharpUnionRound_eq_self_of_not_mem_halfBall {m k : ℕ} (hk : k ≤ m + 1) (c ε r δ : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} {f : M → ℝ}
    (data : MorseChart (m + 1) k hk c I f)
    (hε : 0 < ε) (hδ0 : 0 < δ) (hδr : δ < r ^ 2)
    (hεr' : Real.sqrt (2 * ε + 2 * r ^ 2) < data.R / 2)
    (hbig : r ^ 2 + ε + δ ≤ data.R ^ 2 / 8)
    {x : M} (hx : x ∈ sublevel f (c - ε) ∪ Set.range (handleEmbedding hk c ε r data))
    (hxball : x ∉ morseChartCoreBallImage hk c data) :
    morseSharpUnionRound hk c ε r δ data x = x := by
  by_cases hb : x ∈ morseChartBallImage hk c data
  · have hxlow : x ∈ sublevel f (c - ε) := by
      rcases hx with hf | hh
      · exact hf
      · exact False.elim (hxball (range_handleEmbedding_subset_ballImage hk c ε r data hε hεr' hh))
    dsimp [morseChartBallImage] at hb
    rcases hb with ⟨y, hy, hxy⟩
    have hsrc0 : y ∈ data.χ.source := data.hχsrc y (le_of_lt hy)
    have hsymm : data.χ.symm x = y := by
      rw [← hxy]
      exact data.χ.left_inv hsrc0
    have hneg : r ^ 2 + 2 * ε + δ ≤ ‖negPart hk y‖ ^ 2 :=
      negPart_norm_sq_ge_of_lower_bound hk c ε r δ data hbig hxlow hxy
        (le_of_lt hy) (by
          have hnot : ¬ ‖negPart hk (data.χ.symm x)‖ < data.R / 2 := by
            intro hlt
            exact hxball ⟨chartSymm_mem_target_of_mem_ballImage hk c data (by
              exact ⟨y, hy, hxy⟩), hlt⟩
          have hge : data.R / 2 ≤ ‖negPart hk (data.χ.symm x)‖ := by nlinarith [hnot]
          rw [hsymm] at hge
          exact hge)
    have hmap : modelSharpUnionRound hk ε r δ (data.χ.symm x) = data.χ.symm x := by
      rw [hsymm]
      exact modelSharpUnionRound_eq_self_of_negPart_large hk ε r δ hδ0 hδr hneg
    calc
      morseSharpUnionRound hk c ε r δ data x = data.χ (modelSharpUnionRound hk ε r δ (data.χ.symm x)) := by
        dsimp [morseSharpUnionRound]
        rw [if_pos (by exact ⟨y, hy, hxy⟩)]
      _ = data.χ (data.χ.symm x) := by rw [hmap]
      _ = x := by
        rw [← hxy]
        exact data.χ.right_inv (data.χ.map_source hsrc0)
  · dsimp [morseSharpUnionRound]
    rw [if_neg hb]

theorem morseSharpUnionRound_mem_rounded {m k : ℕ} (hk : k ≤ m + 1) (c ε r δ : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} {f : M → ℝ}
    (data : MorseChart (m + 1) k hk c I f)
    (hε : 0 < ε) (hδ0 : 0 < δ) (hδr : δ < r ^ 2)
    (hεr' : Real.sqrt (2 * ε + 2 * r ^ 2) < data.R / 2)
    (hbig : r ^ 2 + ε + δ ≤ data.R ^ 2 / 8)
    {x : M} (hx : x ∈ sublevel f (c - ε) ∪ Set.range (handleEmbedding hk c ε r data)) :
    morseSharpUnionRound hk c ε r δ data x ∈ morseRoundedAttachment hk c ε r δ data := by
  by_cases hb : x ∈ morseChartBallImage hk c data
  · by_cases hb2 : x ∈ morseChartCoreBallImage hk c data
    · left
      refine ⟨modelSharpUnionRound hk ε r δ (data.χ.symm x), ?_, ?_⟩
      · constructor
        · exact modelSharpUnionRound_mem_attached hk c ε r δ hδ0 hδr
            (chartSymm_mem_sharpUnion_model hk c ε r data hε hεr' hb hx)
        · dsimp [morseChartCoreBallImage] at hb2
          change ‖negPart hk (modelSharpUnionRound hk ε r δ (data.χ.symm x))‖ < data.R / 2
          rw [modelSharpUnionRound_negPart]
          exact hb2.2
      · dsimp [morseSharpUnionRound]
        rw [if_pos hb]
    · right
      have hxlow : x ∈ sublevel f (c - ε) := by
        rcases hx with hf | hh
        · exact hf
        · exact False.elim (hb2 (range_handleEmbedding_subset_ballImage hk c ε r data hε hεr' hh))
      have hfix : morseSharpUnionRound hk c ε r δ data x = x :=
        morseSharpUnionRound_eq_self_of_not_mem_halfBall hk c ε r δ data hε hδ0 hδr hεr' hbig hx hb2
      constructor
      · change morseSharpUnionRound hk c ε r δ data x ∈ sublevel f (c - ε)
        rw [hfix]
        exact hxlow
      · change morseSharpUnionRound hk c ε r δ data x ∈
          (morseChartCoreBallImage hk c data ∩ morseChartBallImage hk c data)ᶜ
        rw [hfix]
        intro hx
        exact hb2 hx.1
  · right
    constructor
    · change morseSharpUnionRound hk c ε r δ data x ∈ sublevel f (c - ε)
      dsimp [morseSharpUnionRound]
      rw [if_neg hb]
      have hnot : x ∉ Set.range (handleEmbedding hk c ε r data) := by
        intro hh
        exact hb (by
          rcases hh with ⟨d, hd⟩
          rw [← hd]
          dsimp [morseChartBallImage, handleEmbedding]
          refine ⟨modelHandleMap hk ε r d, ?_, rfl⟩
          have hle : morseNorm (m + 1) (modelHandleMap hk ε r d) ≤ Real.sqrt (2 * ε + 2 * r ^ 2) :=
            modelHandleMap_norm_le hk ε r (le_of_lt hε) d
          exact lt_of_le_of_lt hle (lt_trans hεr' (by nlinarith [data.hRpos] : data.R / 2 < data.R)))
      rcases hx with hf | hh
      · exact hf
      · exact False.elim (hnot hh)
    · change morseSharpUnionRound hk c ε r δ data x ∈
        (morseChartCoreBallImage hk c data ∩ morseChartBallImage hk c data)ᶜ
      dsimp [morseSharpUnionRound]
      rw [if_neg hb]
      intro hx
      exact hb hx.2

theorem chart_mem_sharpUnion_ambient {m k : ℕ} (hk : k ≤ m + 1) (c ε r : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} {f : M → ℝ}
    (data : MorseChart (m + 1) k hk c I f)
    (hε : 0 < ε) (hr : 0 < r)
    {y : MorseModel (m + 1)}
    (hy : y ∈ (sublevel (morseNormalForm hk c) (c - ε) : Set (MorseModel (m + 1))) ∪ modelHandle hk ε r)
    (hnorm : morseNorm (m + 1) y ≤ data.R) :
    data.χ y ∈ sublevel f (c - ε) ∪ Set.range (handleEmbedding hk c ε r data) := by
  rcases hy with hy | hy
  · left
    change f (data.χ y) ≤ c - ε
    rw [data.hnorm y hnorm]
    exact (by simpa [sublevel] using hy : morseNormalForm hk c y ≤ c - ε)
  · right
    have hrange : y ∈ Set.range (modelHandleMap hk ε r) := by
      simpa [← modelHandleMap_range hk ε r hε hr] using hy
    rcases hrange with ⟨d, hd⟩
    refine ⟨d, ?_⟩
    rw [← hd]
    rfl

theorem morseSharpUnionUnround_mem_sharpUnion {m k : ℕ} (hk : k ≤ m + 1) (c ε r δ : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} {f : M → ℝ}
    (data : MorseChart (m + 1) k hk c I f)
    (hε : 0 < ε) (hδ0 : 0 < δ) (hδr : δ < r ^ 2) (hr : 0 < r)
    (hεr' : Real.sqrt (2 * ε + 2 * r ^ 2) < data.R / 2)
    {x : M} (hx : x ∈ morseRoundedAttachment hk c ε r δ data) :
    morseSharpUnionUnround hk c ε r δ data x ∈
      sublevel f (c - ε) ∪ Set.range (handleEmbedding hk c ε r data) := by
  by_cases hb : x ∈ morseChartCoreBallImage hk c data ∩ morseChartBallImage hk c data
  · rcases hx with hx' | hx'
    · rcases hx' with ⟨y, hy, hxy⟩
      have hyU : modelSharpUnionUnround hk ε r δ y ∈
          (sublevel (morseNormalForm hk c) (c - ε) : Set (MorseModel (m + 1))) ∪ modelHandle hk ε r :=
        modelSharpUnionUnround_mem_sharpUnion hk c ε r δ hδ0 hδr hy.1
      have hnorm_le : morseNorm (m + 1) (modelSharpUnionUnround hk ε r δ y) ≤ data.R := by
        have hsq := modelSharpUnionUnround_norm_sq_le hk ε r δ hδ0 hδr (ne_of_gt hr) hy.1
        have ht : ‖negPart hk y‖ ^ 2 < (data.R / 2) ^ 2 := by
          have habs : |‖negPart hk y‖| < |data.R / 2| := by
            rw [abs_of_nonneg (norm_nonneg (negPart hk y)),
              abs_of_nonneg (by nlinarith [data.hRpos] : 0 ≤ data.R / 2)]
            exact hy.2
          exact sq_lt_sq.mpr habs
        have hB : modelSharpUnionBound ε r (‖negPart hk y‖ ^ 2) ≤ (data.R / 2) ^ 2 := by
          change max (r ^ 2) (‖negPart hk y‖ ^ 2 - 2 * ε) ≤ (data.R / 2) ^ 2
          have hle1 : r ^ 2 ≤ (data.R / 2) ^ 2 := by
            have h1 : 2 * ε + 2 * r ^ 2 < (data.R / 2) ^ 2 := by
              have hsc : (Real.sqrt (2 * ε + 2 * r ^ 2)) ^ 2 < (data.R / 2) ^ 2 := by
                have habs : |Real.sqrt (2 * ε + 2 * r ^ 2)| < |data.R / 2| := by
                  rw [abs_of_nonneg (Real.sqrt_nonneg _)]
                  rw [abs_of_nonneg (div_nonneg (le_of_lt data.hRpos) (by norm_num))]
                  exact hεr'
                exact sq_lt_sq.mpr habs
              simpa [Real.sq_sqrt (by positivity : 0 ≤ 2 * ε + 2 * r ^ 2)] using hsc
            nlinarith [hε, h1]
          have hle2 : ‖negPart hk y‖ ^ 2 - 2 * ε ≤ (data.R / 2) ^ 2 := by nlinarith [ht]
          exact max_le hle1 hle2
        have hsum : ‖negPart hk y‖ ^ 2 + modelSharpUnionBound ε r (‖negPart hk y‖ ^ 2) ≤ data.R ^ 2 := by
          nlinarith [ht, hB]
        have hsq' : morseNorm (m + 1) (modelSharpUnionUnround hk ε r δ y) ^ 2 ≤ data.R ^ 2 := by
          nlinarith [hsq, hsum]
        have habs := sq_le_sq.mp hsq'
        rwa [abs_of_nonneg (norm_nonneg _), abs_of_nonneg (le_of_lt data.hRpos)] at habs
      have hχ : data.χ (modelSharpUnionUnround hk ε r δ y) ∈
          sublevel f (c - ε) ∪ Set.range (handleEmbedding hk c ε r data) :=
        chart_mem_sharpUnion_ambient hk c ε r data hε hr hyU hnorm_le
      have hval : morseSharpUnionUnround hk c ε r δ data x = data.χ (modelSharpUnionUnround hk ε r δ y) := by
        dsimp [morseSharpUnionUnround]
        rw [if_pos hb]
        congr 1
        rw [← hxy]
        have hsrc0 : y ∈ data.χ.source := data.hχsrc y (le_of_lt
          (morseNorm_lt_of_mem_attached_negPart_lt hk ε r δ data.R (le_of_lt hε) hδ0 hδr hεr'
            data.hRpos hy.1 hy.2))
        exact congrArg (modelSharpUnionUnround hk ε r δ) (data.χ.left_inv hsrc0)
      rw [hval]
      exact hχ
    · exact False.elim (hx'.2 hb)
  · have hx' : x ∈ sublevel f (c - ε) := by
      rcases hx with hx' | hx'
      · exact False.elim (hb (by
          rcases hx' with ⟨y, hy, hxy⟩
          have hyb : morseNorm (m + 1) y < data.R :=
            morseNorm_lt_of_mem_attached_negPart_lt hk ε r δ data.R (le_of_lt hε) hδ0 hδr hεr'
              data.hRpos hy.1 hy.2
          have hsrc0 : y ∈ data.χ.source := data.hχsrc y (le_of_lt hyb)
          constructor
          · constructor
            · rw [← hxy]
              exact data.χ.map_source hsrc0
            · rw [← hxy]
              rw [data.χ.left_inv hsrc0]
              exact hy.2
          · dsimp [morseChartBallImage]
            refine ⟨y, hyb, hxy⟩))
      · exact hx'.1
    have hval : morseSharpUnionUnround hk c ε r δ data x = x := by
      dsimp [morseSharpUnionUnround]
      rw [if_neg hb]
    rw [hval]
    exact Or.inl hx'

theorem morseSharpUnionUnround_round {m k : ℕ} (hk : k ≤ m + 1) (c ε r δ : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} {f : M → ℝ}
    (data : MorseChart (m + 1) k hk c I f)
    (hε : 0 < ε) (hδ0 : 0 < δ) (hδr : δ < r ^ 2)
    (hεr' : Real.sqrt (2 * ε + 2 * r ^ 2) < data.R / 2)
    (hbig : r ^ 2 + ε + δ ≤ data.R ^ 2 / 8)
    {x : M} (hx : x ∈ sublevel f (c - ε) ∪ Set.range (handleEmbedding hk c ε r data)) :
    morseSharpUnionUnround hk c ε r δ data (morseSharpUnionRound hk c ε r δ data x) = x := by
  by_cases hb : x ∈ morseChartCoreBallImage hk c data ∩ morseChartBallImage hk c data
  · have hbFull : x ∈ morseChartBallImage hk c data := hb.2
    have hneg : ‖negPart hk (data.χ.symm x)‖ < data.R / 2 := hb.1.2
    have hnormx : morseNorm (m + 1) (data.χ.symm x) < data.R :=
      chartSymm_norm_lt_of_mem_ballImage hk c data hbFull
    have hsrcRound : modelSharpUnionRound hk ε r δ (data.χ.symm x) ∈ data.χ.source :=
      data.hχsrc (modelSharpUnionRound hk ε r δ (data.χ.symm x))
        (le_trans (modelSharpUnionRound_morseNorm_le hk ε r δ hδ0 hδr (data.χ.symm x))
          (le_of_lt hnormx))
    have hmemCore : data.χ (modelSharpUnionRound hk ε r δ (data.χ.symm x)) ∈
        morseChartCoreBallImage hk c data := by
      dsimp [morseChartCoreBallImage]
      constructor
      · exact data.χ.map_source hsrcRound
      · rw [data.χ.left_inv hsrcRound]
        rw [modelSharpUnionRound_negPart]
        exact hneg
    have hmemFull : data.χ (modelSharpUnionRound hk ε r δ (data.χ.symm x)) ∈
        morseChartBallImage hk c data := by
      dsimp [morseChartBallImage]
      refine ⟨modelSharpUnionRound hk ε r δ (data.χ.symm x),
        (lt_of_le_of_lt (modelSharpUnionRound_morseNorm_le hk ε r δ hδ0 hδr (data.χ.symm x))
          hnormx), rfl⟩
    have hround : morseSharpUnionRound hk c ε r δ data x =
        data.χ (modelSharpUnionRound hk ε r δ (data.χ.symm x)) := by
      dsimp [morseSharpUnionRound]
      rw [if_pos hbFull]
    rw [hround]
    have hunround : morseSharpUnionUnround hk c ε r δ data
        (data.χ (modelSharpUnionRound hk ε r δ (data.χ.symm x))) =
        data.χ (modelSharpUnionUnround hk ε r δ (modelSharpUnionRound hk ε r δ (data.χ.symm x))) := by
      dsimp [morseSharpUnionUnround]
      rw [if_pos ⟨hmemCore, hmemFull⟩]
      congr 1
      rw [data.χ.left_inv hsrcRound]
    rw [hunround]
    rw [modelSharpUnionUnround_round hk ε r δ hδ0 hδr (y := data.χ.symm x)]
    exact chartSymm_right_inv_of_mem_ballImage hk c data hbFull
  · by_cases hbF : x ∈ morseChartBallImage hk c data
    · have hfix : morseSharpUnionRound hk c ε r δ data x = x :=
        morseSharpUnionRound_eq_self_of_not_mem_halfBall hk c ε r δ data hε hδ0 hδr hεr' hbig hx (by
          intro hc
          exact hb ⟨hc, hbF⟩)
      rw [hfix]
      dsimp [morseSharpUnionUnround]
      rw [if_neg hb]
    · have hfix : morseSharpUnionRound hk c ε r δ data x = x := by
        dsimp [morseSharpUnionRound]
        rw [if_neg hbF]
      rw [hfix]
      dsimp [morseSharpUnionUnround]
      rw [if_neg hb]

theorem morseSharpUnionRound_unround {m k : ℕ} (hk : k ≤ m + 1) (c ε r δ : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} {f : M → ℝ}
    (data : MorseChart (m + 1) k hk c I f)
    (hε : 0 < ε) (hδ0 : 0 < δ) (hδr : δ < r ^ 2) (hr : 0 < r)
    (hεr' : Real.sqrt (2 * ε + 2 * r ^ 2) < data.R / 2)
    (hbig : r ^ 2 + ε + δ ≤ data.R ^ 2 / 8)
    {x : M} (hx : x ∈ morseRoundedAttachment hk c ε r δ data) :
    morseSharpUnionRound hk c ε r δ data (morseSharpUnionUnround hk c ε r δ data x) = x := by
  by_cases hb : x ∈ morseChartCoreBallImage hk c data ∩ morseChartBallImage hk c data
  · have hbFull : x ∈ morseChartBallImage hk c data := hb.2
    have hyatt : data.χ.symm x ∈ modelAttachedRegion hk ε r δ := by
      rcases hx with hx' | hx'
      · rcases hx' with ⟨z, hz, hzy⟩
        have hsrcz : z ∈ data.χ.source := data.hχsrc z
          (le_of_lt (morseNorm_lt_of_mem_attached_negPart_lt hk ε r δ data.R (le_of_lt hε) hδ0 hδr hεr'
            data.hRpos hz.1 hz.2))
        have hz' : z = data.χ.symm x := by
          rw [← hzy]
          exact (data.χ.left_inv hsrcz).symm
        rw [← hz']
        exact hz.1
      · exact False.elim (hx'.2 hb)
    have hnegx : ‖negPart hk (data.χ.symm x)‖ < data.R / 2 := hb.1.2
    have hbound : morseNorm (m + 1) (modelSharpUnionUnround hk ε r δ (data.χ.symm x)) < data.R := by
      have hsq := modelSharpUnionUnround_norm_sq_le hk ε r δ hδ0 hδr (ne_of_gt hr) hyatt
      have ht : ‖negPart hk (data.χ.symm x)‖ ^ 2 < (data.R / 2) ^ 2 := by
        have habs : |‖negPart hk (data.χ.symm x)‖| < |data.R / 2| := by
          rw [abs_of_nonneg (norm_nonneg (negPart hk (data.χ.symm x))),
            abs_of_nonneg (by nlinarith [data.hRpos] : 0 ≤ data.R / 2)]
          exact hnegx
        exact sq_lt_sq.mpr habs
      have hB : modelSharpUnionBound ε r (‖negPart hk (data.χ.symm x)‖ ^ 2) ≤ (data.R / 2) ^ 2 := by
        change max (r ^ 2) (‖negPart hk (data.χ.symm x)‖ ^ 2 - 2 * ε) ≤ (data.R / 2) ^ 2
        have hle1 : r ^ 2 ≤ (data.R / 2) ^ 2 := by
          have h1 : 2 * ε + 2 * r ^ 2 < (data.R / 2) ^ 2 := by
            have hsc : (Real.sqrt (2 * ε + 2 * r ^ 2)) ^ 2 < (data.R / 2) ^ 2 := by
              have habs : |Real.sqrt (2 * ε + 2 * r ^ 2)| < |data.R / 2| := by
                rw [abs_of_nonneg (Real.sqrt_nonneg _)]
                rw [abs_of_nonneg (div_nonneg (le_of_lt data.hRpos) (by norm_num))]
                exact hεr'
              exact sq_lt_sq.mpr habs
            simpa [Real.sq_sqrt (by positivity : 0 ≤ 2 * ε + 2 * r ^ 2)] using hsc
          nlinarith [hε, h1]
        have hle2 : ‖negPart hk (data.χ.symm x)‖ ^ 2 - 2 * ε ≤ (data.R / 2) ^ 2 := by nlinarith [ht]
        exact max_le hle1 hle2
      have hsum : ‖negPart hk (data.χ.symm x)‖ ^ 2 + modelSharpUnionBound ε r
          (‖negPart hk (data.χ.symm x)‖ ^ 2) < data.R ^ 2 := by
        nlinarith [ht, hB, data.hRpos]
      have hsq' : morseNorm (m + 1) (modelSharpUnionUnround hk ε r δ (data.χ.symm x)) ^ 2 <
          data.R ^ 2 := by
        nlinarith [hsq, hsum]
      have habs := sq_lt_sq.mp hsq'
      rwa [abs_of_nonneg (norm_nonneg (WithLp.toLp 2 (modelSharpUnionUnround hk ε r δ (data.χ.symm x))
        : EuclideanSpace ℝ (Fin (m + 1)))),
        abs_of_nonneg (le_of_lt data.hRpos)] at habs
    have hunround : morseSharpUnionUnround hk c ε r δ data x =
        data.χ (modelSharpUnionUnround hk ε r δ (data.χ.symm x)) := by
      dsimp [morseSharpUnionUnround]
      rw [if_pos hb]
    rw [hunround]
    have hmemFull : data.χ (modelSharpUnionUnround hk ε r δ (data.χ.symm x)) ∈
        morseChartBallImage hk c data := by
      dsimp [morseChartBallImage]
      refine ⟨modelSharpUnionUnround hk ε r δ (data.χ.symm x), hbound, rfl⟩
    have hsrcUnround : modelSharpUnionUnround hk ε r δ (data.χ.symm x) ∈ data.χ.source :=
      data.hχsrc (modelSharpUnionUnround hk ε r δ (data.χ.symm x)) (le_of_lt hbound)
    have hround : morseSharpUnionRound hk c ε r δ data
        (data.χ (modelSharpUnionUnround hk ε r δ (data.χ.symm x))) =
        data.χ (modelSharpUnionRound hk ε r δ (modelSharpUnionUnround hk ε r δ (data.χ.symm x))) := by
      dsimp [morseSharpUnionRound]
      rw [if_pos hmemFull]
      congr 1
      rw [data.χ.left_inv hsrcUnround]
    rw [hround]
    rw [modelSharpUnionRound_unround hk ε r δ hδ0 hδr (z := data.χ.symm x)]
    exact chartSymm_right_inv_of_mem_ballImage hk c data hbFull
  · have hunround : morseSharpUnionUnround hk c ε r δ data x = x := by
      dsimp [morseSharpUnionUnround]
      rw [if_neg hb]
    rw [hunround]
    have hxlow : x ∈ sublevel f (c - ε) := by
      rcases hx with hx' | hx'
      · exact False.elim (hb (by
          rcases hx' with ⟨y, hy, hxy⟩
          have hyb : morseNorm (m + 1) y < data.R :=
            morseNorm_lt_of_mem_attached_negPart_lt hk ε r δ data.R (le_of_lt hε) hδ0 hδr hεr'
              data.hRpos hy.1 hy.2
          have hsrc0 : y ∈ data.χ.source := data.hχsrc y (le_of_lt hyb)
          constructor
          · constructor
            · rw [← hxy]
              exact data.χ.map_source hsrc0
            · rw [← hxy]
              rw [data.χ.left_inv hsrc0]
              exact hy.2
          · dsimp [morseChartBallImage]
            refine ⟨y, hyb, hxy⟩))
      · exact hx'.1
    by_cases hbF : x ∈ morseChartBallImage hk c data
    · exact morseSharpUnionRound_eq_self_of_not_mem_halfBall hk c ε r δ data hε hδ0 hδr hεr' hbig
        (Or.inl hxlow) (by intro hc; exact hb ⟨hc, hbF⟩)
    · dsimp [morseSharpUnionRound]
      rw [if_neg hbF]

private lemma continuousAt_piecewise_open_compl {X : Type} [TopologicalSpace X]
    (f g : X → X) (U : Set X) (x : X) (hxU : x ∉ U)
    (hU : ∀ y ∈ U, f y = g y)
    (hcompl : ∀ y ∈ Uᶜ, f y = y)
    (hg : Filter.Tendsto g (nhdsWithin x U) (nhds x)) :
    ContinuousAt f x := by
  rw [ContinuousAt, hcompl x hxU]
  have hI : Set.univ = U ∪ Uᶜ := by
    ext y
    simp
  have h1 : Filter.Tendsto f (nhdsWithin x U) (nhds x) := by
    have hEq : f =ᶠ[nhdsWithin x U] g :=
      Filter.eventually_inf_principal.mpr (Filter.Eventually.of_forall (fun y => hU y))
    exact Filter.Tendsto.congr' hEq.symm hg
  have h2 : Filter.Tendsto f (nhdsWithin x Uᶜ) (nhds x) := by
    have hid : Filter.Tendsto (fun y : X => y) (nhdsWithin x Uᶜ) (nhds x) :=
      (continuousAt_id.tendsto).mono_left nhdsWithin_le_nhds
    have hEq : (fun y : X => y) =ᶠ[nhdsWithin x Uᶜ] f :=
      Filter.eventually_inf_principal.mpr
        (Filter.Eventually.of_forall (fun y => fun hyUc => (hcompl y hyUc).symm))
    exact Filter.Tendsto.congr' hEq hid
  have hgoal : Filter.Tendsto f (nhdsWithin x U ⊔ nhdsWithin x Uᶜ) (nhds x) :=
    Filter.tendsto_sup.mpr ⟨h1, h2⟩
  rwa [← nhds_eq_nhdsWithin_sup_nhdsWithin x hI] at hgoal

theorem continuousOn_morseSharpUnionRound {m k : ℕ} (hk : k ≤ m + 1) (c ε r δ : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} {f : M → ℝ}
    (data : MorseChart (m + 1) k hk c I f)
    (hε : 0 < ε) (hδ0 : 0 < δ) (hδr : δ < r ^ 2)
    (hεr' : Real.sqrt (2 * ε + 2 * r ^ 2) < data.R / 2)
    (hbig : r ^ 2 + ε + δ ≤ data.R ^ 2 / 8)
    (hcont : Continuous f) :
    ContinuousOn (morseSharpUnionRound hk c ε r δ data)
      (sublevel f (c - ε) ∪ Set.range (handleEmbedding hk c ε r data)) := by
  let S : Set M := sublevel f (c - ε) ∪ Set.range (handleEmbedding hk c ε r data)
  let U : Set M := morseChartBallImage hk c data
  let V : Set M := morseChartCoreBallImage hk c data
  let C : Set M := sublevel f (c - ε) ∩ (V ∩ U)ᶜ
  have hUopen : IsOpen U := by
    dsimp [U]
    exact isOpen_chiBallImage data.χ data.R (fun y hy => data.hχsrc y (le_of_lt hy))
  have hVopen : IsOpen V := by
    dsimp [V]
    rw [isOpen_iff_mem_nhds]
    intro x hx
    rcases hx with ⟨hxtgt, hxneg⟩
    have hcontSymm : ContinuousAt data.χ.symm x := by
      exact (data.χ.continuousOn_invFun x hxtgt).continuousAt
        (IsOpen.mem_nhds data.χ.open_target hxtgt)
    have hnormCont : Continuous (fun y : MorseModel (m + 1) => ‖negPart hk y‖) :=
      continuous_norm.comp (continuous_negPart hk)
    have hcomp : ContinuousAt (fun y : M => ‖negPart hk (data.χ.symm y)‖) x :=
      hnormCont.continuousAt.comp hcontSymm
    have hpre : (fun y : M => ‖negPart hk (data.χ.symm y)‖) ⁻¹' (Set.Iio (data.R / 2)) ∈
        nhds x :=
      hcomp.preimage_mem_nhds (IsOpen.mem_nhds isOpen_Iio hxneg)
    simpa [Set.inter_def, Set.preimage] using
      (Filter.inter_mem (IsOpen.mem_nhds data.χ.open_target hxtgt) hpre)
  have hCclosed : IsClosed C := by
    dsimp [C]
    exact IsClosed.inter (isClosed_Iic.preimage hcont) (isClosed_compl_iff.mpr (hVopen.inter hUopen))
  have hU : ContinuousOn (morseSharpUnionRound hk c ε r δ data) U := by
    have hχsymm : ContinuousOn data.χ.symm data.χ.target := data.χ.continuousOn_invFun
    have hχ : ContinuousOn data.χ data.χ.source := data.χ.continuousOn_toFun
    have hmodel : ContinuousOn (modelSharpUnionRound hk ε r δ) Set.univ :=
      (continuous_modelSharpUnionRound hk ε r δ hδ0 hδr).continuousOn
    have h1 : ContinuousOn (fun x : M => modelSharpUnionRound hk ε r δ (data.χ.symm x)) U := by
      refine hmodel.comp (hχsymm.mono ?_) ?_
      · intro x hx
        rcases hx with ⟨y, hy, hxy⟩
        have hsrc0 : y ∈ data.χ.source := data.hχsrc y (le_of_lt hy)
        rw [← hxy]
        exact data.χ.map_source hsrc0
      · intro x hx
        trivial
    have h2 : ContinuousOn (fun x : M => data.χ (modelSharpUnionRound hk ε r δ (data.χ.symm x))) U := by
      refine hχ.comp h1 ?_
      intro x hx
      rcases hx with ⟨y, hy, hxy⟩
      change modelSharpUnionRound hk ε r δ (data.χ.symm x) ∈ data.χ.source
      rw [← hxy]
      rw [data.χ.left_inv (data.hχsrc y (le_of_lt hy))]
      exact data.hχsrc (modelSharpUnionRound hk ε r δ y)
        (le_trans (modelSharpUnionRound_morseNorm_le hk ε r δ hδ0 hδr y) (le_of_lt hy))
    exact h2.congr (s := U) (g := morseSharpUnionRound hk c ε r δ data) (fun x hx => by
      dsimp [morseSharpUnionRound]
      rw [if_pos hx])
  have hC : ContinuousOn (morseSharpUnionRound hk c ε r δ data) C := by
    refine continuousOn_id.congr (s := C) (g := morseSharpUnionRound hk c ε r δ data) ?_
    intro x hx
    by_cases hbF : x ∈ morseChartBallImage hk c data
    · exact morseSharpUnionRound_eq_self_of_not_mem_halfBall hk c ε r δ data hε hδ0 hδr hεr' hbig
        (Or.inl hx.1) (by intro hc; exact hx.2 ⟨hc, hbF⟩)
    · dsimp [morseSharpUnionRound]
      rw [if_neg hbF]
  have hboundary : ∀ x ∈ C, ContinuousAt (morseSharpUnionRound hk c ε r δ data) x := by
    intro x hx
    by_cases hbF : x ∈ morseChartBallImage hk c data
    · have hnotCore : x ∉ morseChartCoreBallImage hk c data := by
        intro hc
        exact hx.2 ⟨hc, hbF⟩
      have hxlow : x ∈ sublevel f (c - ε) := hx.1
      rcases hbF with ⟨y, hy, hxy⟩
      have hsrc0 : y ∈ data.χ.source := data.hχsrc y (le_of_lt hy)
      have hxtgt : x ∈ data.χ.target := by
        rw [← hxy]
        exact data.χ.map_source hsrc0
      have hdeep : modelSharpUnionRound hk ε r δ (data.χ.symm x) = data.χ.symm x := by
        have hsymm : data.χ.symm x = y := by
          rw [← hxy]
          exact data.χ.left_inv hsrc0
        rw [hsymm]
        have hneg : r ^ 2 + 2 * ε + δ ≤ ‖negPart hk y‖ ^ 2 :=
          negPart_norm_sq_ge_of_lower_bound hk c ε r δ data hbig hxlow hxy
            (le_of_lt hy) (by
              have hnot : ¬ ‖negPart hk (data.χ.symm x)‖ < data.R / 2 := by
                intro hlt
                exact hnotCore ⟨chartSymm_mem_target_of_mem_ballImage hk c data (by
                  exact ⟨y, hy, hxy⟩), hlt⟩
              have hge : data.R / 2 ≤ ‖negPart hk (data.χ.symm x)‖ := by nlinarith [hnot]
              rw [hsymm] at hge
              exact hge)
        exact modelSharpUnionRound_eq_self_of_negPart_large hk ε r δ hδ0 hδr hneg
      have hsrcModel : modelSharpUnionRound hk ε r δ (data.χ.symm x) ∈ data.χ.source := by
        rw [hdeep]
        rw [← hxy]
        rw [data.χ.left_inv hsrc0]
        exact hsrc0
      have hchart : ContinuousAt (fun z : M => data.χ (modelSharpUnionRound hk ε r δ (data.χ.symm z))) x := by
        have hcontSymm : ContinuousAt data.χ.symm x := by
          exact (data.χ.continuousOn_invFun x hxtgt).continuousAt
            (IsOpen.mem_nhds data.χ.open_target hxtgt)
        have hcontModel : ContinuousAt (modelSharpUnionRound hk ε r δ) (data.χ.symm x) :=
          (continuous_modelSharpUnionRound hk ε r δ hδ0 hδr).continuousAt
        have hcontχ : ContinuousAt data.χ (modelSharpUnionRound hk ε r δ (data.χ.symm x)) := by
          exact (data.χ.continuousOn_toFun (modelSharpUnionRound hk ε r δ (data.χ.symm x)) hsrcModel).continuousAt
            (IsOpen.mem_nhds data.χ.open_source hsrcModel)
        exact (hcontχ.comp hcontModel).comp hcontSymm
      exact hchart.congr_of_eventuallyEq (Filter.eventually_of_mem
        (IsOpen.mem_nhds hUopen (by exact ⟨y, hy, hxy⟩)) (fun z hz => by
          dsimp [morseSharpUnionRound]
          rw [if_pos hz]))
    · have hg : Filter.Tendsto (fun z : M => data.χ (modelSharpUnionRound hk ε r δ (data.χ.symm z)))
        (nhdsWithin x U) (nhds x) := by
        by_cases hclose : x ∈ closure U
        · have hxA : x ∈ data.χ '' {y : MorseModel (m + 1) | morseNorm (m + 1) y ≤ data.R} :=
            ((closure_mono (by
                intro y hy
                rcases hy with ⟨w, hw, hwy⟩
                have hw' : morseNorm (m + 1) w < data.R := by simpa using hw
                exact ⟨w, (le_of_lt hw'), hwy⟩)).trans
              (isClosed_chartBallImage (H := H) data.χ data.R
                (fun y hy => data.hχsrc y hy)).closure_subset) hclose
          rcases hxA with ⟨y, hy, hxy⟩
          have hsrc0 : y ∈ data.χ.source := data.hχsrc y hy
          have hxtgt : x ∈ data.χ.target := by
            rw [← hxy]
            exact data.χ.map_source hsrc0
          have hdeep : modelSharpUnionRound hk ε r δ (data.χ.symm x) = data.χ.symm x := by
            have hsymm : data.χ.symm x = y := by
              rw [← hxy]
              exact data.χ.left_inv hsrc0
            rw [hsymm]
            have hneg : r ^ 2 + 2 * ε + δ ≤ ‖negPart hk y‖ ^ 2 := by
              have hnormy : data.R ≤ morseNorm (m + 1) y := by
                have hnot : ¬ morseNorm (m + 1) y < data.R := by
                  intro hylt
                  exact hbF (by dsimp [morseChartBallImage]; refine ⟨y, hylt, hxy⟩)
                nlinarith [hnot]
              exact negPart_norm_sq_ge_of_lower_bound hk c ε r δ data hbig hx.1 hxy hy
                (by
                  have hpos : ‖posPart hk y‖ ^ 2 ≤ ‖negPart hk y‖ ^ 2 - 2 * ε := by
                    have hf' : morseNormalForm hk c y ≤ c - ε := by
                      rw [← data.hnorm y hy]
                      rw [hxy]
                      exact (by simpa [sublevel] using hx.1 : f x ≤ c - ε)
                    rw [morseNormalForm_split] at hf'
                    nlinarith
                  have hnorm_sq : ‖negPart hk y‖ ^ 2 + ‖posPart hk y‖ ^ 2 ≥ data.R ^ 2 := by
                    have hsqy : data.R ^ 2 ≤ morseNorm (m + 1) y ^ 2 := by
                      have hRnonneg : 0 ≤ data.R := le_of_lt data.hRpos
                      exact sq_le_sq.mpr (by
                        rw [abs_of_nonneg hRnonneg, abs_of_nonneg (norm_nonneg _)]
                        exact hnormy)
                    have hnorm_sq' : morseNorm (m + 1) y ^ 2 = ‖negPart hk y‖ ^ 2 + ‖posPart hk y‖ ^ 2 := by
                      calc
                        morseNorm (m + 1) y ^ 2 =
                            morseNorm (m + 1) (recombine hk (negPart hk y) (posPart hk y)) ^ 2 := by
                          rw [recombine_decompose hk y]
                        _ = ‖negPart hk y‖ ^ 2 + ‖posPart hk y‖ ^ 2 :=
                          morseNorm_recombine_sq hk (negPart hk y) (posPart hk y)
                    nlinarith [hsqy, hnorm_sq']
                  have hsqneg : (data.R / 2) ^ 2 ≤ ‖negPart hk y‖ ^ 2 := by
                    nlinarith [hpos, hnorm_sq, hε, sq_nonneg (‖posPart hk y‖)]
                  have habs := sq_le_sq.mp hsqneg
                  rwa [abs_of_nonneg (by nlinarith [data.hRpos] : 0 ≤ data.R / 2),
                    abs_of_nonneg (norm_nonneg (negPart hk y))] at habs)
            exact modelSharpUnionRound_eq_self_of_negPart_large hk ε r δ hδ0 hδr hneg
          have hsrcModel : modelSharpUnionRound hk ε r δ (data.χ.symm x) ∈ data.χ.source := by
            rw [hdeep]
            rw [← hxy]
            rw [data.χ.left_inv hsrc0]
            exact hsrc0
          have hchart : ContinuousAt (fun z : M => data.χ (modelSharpUnionRound hk ε r δ (data.χ.symm z))) x := by
            have hcontSymm : ContinuousAt data.χ.symm x := by
              exact (data.χ.continuousOn_invFun x hxtgt).continuousAt
                (IsOpen.mem_nhds data.χ.open_target hxtgt)
            have hcontModel : ContinuousAt (modelSharpUnionRound hk ε r δ) (data.χ.symm x) :=
              (continuous_modelSharpUnionRound hk ε r δ hδ0 hδr).continuousAt
            have hcontχ : ContinuousAt data.χ (modelSharpUnionRound hk ε r δ (data.χ.symm x)) := by
              exact (data.χ.continuousOn_toFun (modelSharpUnionRound hk ε r δ (data.χ.symm x)) hsrcModel).continuousAt
                (IsOpen.mem_nhds data.χ.open_source hsrcModel)
            exact (hcontχ.comp hcontModel).comp hcontSymm
          have hchartx : data.χ (modelSharpUnionRound hk ε r δ (data.χ.symm x)) = x := by
            rw [hdeep]
            exact data.χ.right_inv hxtgt
          have hT : Filter.Tendsto (fun z : M => data.χ (modelSharpUnionRound hk ε r δ (data.χ.symm z)))
              (nhdsWithin x U) (nhds (data.χ (modelSharpUnionRound hk ε r δ (data.χ.symm x)))) :=
            hchart.tendsto.mono_left nhdsWithin_le_nhds
          simpa [hchartx] using hT
        · rw [(notMem_closure_iff_nhdsWithin_eq_bot).mp hclose]
          exact Filter.tendsto_bot
      exact continuousAt_piecewise_open_compl (morseSharpUnionRound hk c ε r δ data)
        (fun z : M => data.χ (modelSharpUnionRound hk ε r δ (data.χ.symm z))) U x hbF
        (fun z hzU => by
          dsimp [morseSharpUnionRound]
          rw [if_pos hzU])
        (fun z hzUc => by
          dsimp [morseSharpUnionRound]
          rw [if_neg hzUc])
        hg
  exact (ContinuousOn.union_continuousAt hUopen hU hboundary).mono (by
    intro x hx
    by_cases hxU : x ∈ U
    · exact Or.inl hxU
    · rcases hx with hflow | hcell
      · exact Or.inr ⟨hflow, by intro hx; exact hxU hx.2⟩
      · exact False.elim (hxU (by
          rcases hcell with ⟨d, hd⟩
          rw [← hd]
          dsimp [morseChartBallImage, handleEmbedding]
          refine ⟨modelHandleMap hk ε r d, ?_, rfl⟩
          have hle : morseNorm (m + 1) (modelHandleMap hk ε r d) ≤ Real.sqrt (2 * ε + 2 * r ^ 2) :=
            modelHandleMap_norm_le hk ε r (le_of_lt hε) d
          exact lt_of_le_of_lt hle (lt_trans hεr' (by nlinarith [data.hRpos] : data.R / 2 < data.R)))))

theorem continuousOn_morseSharpUnionUnround {m k : ℕ} (hk : k ≤ m + 1) (c ε r δ : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} {f : M → ℝ}
    (data : MorseChart (m + 1) k hk c I f)
    (hε : 0 < ε) (hδ0 : 0 < δ) (hδr : δ < r ^ 2) (hr : r ≠ 0)
    (hεr' : Real.sqrt (2 * ε + 2 * r ^ 2) < data.R / 2)
    (hbig : r ^ 2 + ε + δ ≤ data.R ^ 2 / 8) :
    ContinuousOn (morseSharpUnionUnround hk c ε r δ data)
      (morseRoundedAttachment hk c ε r δ data) := by
  let R : Set M := morseRoundedAttachment hk c ε r δ data
  let V : Set M := morseChartCoreBallImage hk c data
  let W : Set M := morseChartBallImage hk c data
  let U : Set M := V ∩ W
  let C : Set M := sublevel f (c - ε) ∩ Uᶜ
  have hUopen : IsOpen U := by
    dsimp [U, V, W]
    exact IsOpen.inter (by
      rw [isOpen_iff_mem_nhds]
      intro x hx
      rcases hx with ⟨hxtgt, hxneg⟩
      have hcontSymm : ContinuousAt data.χ.symm x := by
        exact (data.χ.continuousOn_invFun x hxtgt).continuousAt
          (IsOpen.mem_nhds data.χ.open_target hxtgt)
      have hnormCont : Continuous (fun y : MorseModel (m + 1) => ‖negPart hk y‖) :=
        continuous_norm.comp (continuous_negPart hk)
      have hcomp : ContinuousAt (fun y : M => ‖negPart hk (data.χ.symm y)‖) x :=
        hnormCont.continuousAt.comp hcontSymm
      have hpre : (fun y : M => ‖negPart hk (data.χ.symm y)‖) ⁻¹' (Set.Iio (data.R / 2)) ∈
          nhds x :=
        hcomp.preimage_mem_nhds (IsOpen.mem_nhds isOpen_Iio hxneg)
      simpa [Set.inter_def, Set.preimage] using
        (Filter.inter_mem (IsOpen.mem_nhds data.χ.open_target hxtgt) hpre))
      (isOpen_chiBallImage data.χ data.R (fun y hy => data.hχsrc y (le_of_lt hy)))
  have hUR : ContinuousOn (morseSharpUnionUnround hk c ε r δ data) (U ∩ R) := by
    have hχsymm : ContinuousOn data.χ.symm data.χ.target := data.χ.continuousOn_invFun
    have hχ : ContinuousOn data.χ data.χ.source := data.χ.continuousOn_toFun
    have hmodel : ContinuousOn (modelSharpUnionUnround hk ε r δ) Set.univ :=
      (continuous_modelSharpUnionUnround hk ε r δ hδ0 hδr).continuousOn
    have h1 : ContinuousOn (fun x : M => modelSharpUnionUnround hk ε r δ (data.χ.symm x)) (U ∩ R) := by
      refine hmodel.comp (hχsymm.mono ?_) ?_
      · intro x hx
        exact chartSymm_mem_target_of_mem_ballImage hk c data hx.1.2
      · intro x hx
        trivial
    have h2 : ContinuousOn (fun x : M => data.χ (modelSharpUnionUnround hk ε r δ (data.χ.symm x))) (U ∩ R) := by
      refine hχ.comp h1 ?_
      intro x hx
      have hyatt : data.χ.symm x ∈ modelAttachedRegion hk ε r δ := by
        rcases hx.2 with hx' | hx'
        · rcases hx' with ⟨z, hz, hzy⟩
          have hsrcz : z ∈ data.χ.source := data.hχsrc z
            (le_of_lt (morseNorm_lt_of_mem_attached_negPart_lt hk ε r δ data.R (le_of_lt hε) hδ0 hδr hεr'
              data.hRpos hz.1 hz.2))
          have hz' : z = data.χ.symm x := by
            rw [← hzy]
            exact (data.χ.left_inv hsrcz).symm
          rw [← hz']
          exact hz.1
        · exact False.elim (hx'.2 hx.1)
      have hnegx : ‖negPart hk (data.χ.symm x)‖ < data.R / 2 := hx.1.1.2
      change modelSharpUnionUnround hk ε r δ (data.χ.symm x) ∈ data.χ.source
      have hbounded : morseNorm (m + 1) (modelSharpUnionUnround hk ε r δ (data.χ.symm x)) ≤ data.R := by
        have hsq := modelSharpUnionUnround_norm_sq_le hk ε r δ hδ0 hδr hr hyatt
        have ht : ‖negPart hk (data.χ.symm x)‖ ^ 2 < (data.R / 2) ^ 2 := by
          have habs : |‖negPart hk (data.χ.symm x)‖| < |data.R / 2| := by
            rw [abs_of_nonneg (norm_nonneg (negPart hk (data.χ.symm x))),
              abs_of_nonneg (by nlinarith [data.hRpos] : 0 ≤ data.R / 2)]
            exact hnegx
          exact sq_lt_sq.mpr habs
        have hB : modelSharpUnionBound ε r (‖negPart hk (data.χ.symm x)‖ ^ 2) ≤ (data.R / 2) ^ 2 := by
          change max (r ^ 2) (‖negPart hk (data.χ.symm x)‖ ^ 2 - 2 * ε) ≤ (data.R / 2) ^ 2
          have hle1 : r ^ 2 ≤ (data.R / 2) ^ 2 := by
            have h1 : 2 * ε + 2 * r ^ 2 < (data.R / 2) ^ 2 := by
              have hsc : (Real.sqrt (2 * ε + 2 * r ^ 2)) ^ 2 < (data.R / 2) ^ 2 := by
                have habs : |Real.sqrt (2 * ε + 2 * r ^ 2)| < |data.R / 2| := by
                  rw [abs_of_nonneg (Real.sqrt_nonneg _)]
                  rw [abs_of_nonneg (div_nonneg (le_of_lt data.hRpos) (by norm_num))]
                  exact hεr'
                exact sq_lt_sq.mpr habs
              simpa [Real.sq_sqrt (by positivity : 0 ≤ 2 * ε + 2 * r ^ 2)] using hsc
            nlinarith [hε, h1]
          have hle2 : ‖negPart hk (data.χ.symm x)‖ ^ 2 - 2 * ε ≤ (data.R / 2) ^ 2 := by nlinarith [ht]
          exact max_le hle1 hle2
        have hsum : ‖negPart hk (data.χ.symm x)‖ ^ 2 + modelSharpUnionBound ε r
            (‖negPart hk (data.χ.symm x)‖ ^ 2) ≤ data.R ^ 2 := by
          nlinarith [ht, hB, data.hRpos]
        have hsq' : morseNorm (m + 1) (modelSharpUnionUnround hk ε r δ (data.χ.symm x)) ^ 2 ≤
            data.R ^ 2 := by
          nlinarith [hsq, hsum]
        have habs := sq_le_sq.mp hsq'
        rwa [abs_of_nonneg (norm_nonneg _), abs_of_nonneg (le_of_lt data.hRpos)] at habs
      exact data.hχsrc (modelSharpUnionUnround hk ε r δ (data.χ.symm x)) hbounded
    exact h2.congr (s := U ∩ R) (g := morseSharpUnionUnround hk c ε r δ data) (fun x hx => by
      dsimp [morseSharpUnionUnround]
      rw [if_pos hx.1])
  have hC : ContinuousOn (morseSharpUnionUnround hk c ε r δ data) C := by
    refine continuousOn_id.congr (s := C) (g := morseSharpUnionUnround hk c ε r δ data) ?_
    intro x hx
    dsimp [morseSharpUnionUnround]
    rw [if_neg hx.2]
  have hboundary : ∀ x ∈ C, ContinuousAt (morseSharpUnionUnround hk c ε r δ data) x := by
    intro x hx
    have hg : Filter.Tendsto (fun z : M => data.χ (modelSharpUnionUnround hk ε r δ (data.χ.symm z)))
        (nhdsWithin x U) (nhds x) := by
      by_cases hclose : x ∈ closure W
      · have hxA : x ∈ data.χ '' {y : MorseModel (m + 1) | morseNorm (m + 1) y ≤ data.R} :=
          ((closure_mono (by
              intro y hy
              rcases hy with ⟨w, hw, hwy⟩
              have hw' : morseNorm (m + 1) w < data.R := by simpa using hw
              exact ⟨w, (le_of_lt hw'), hwy⟩)).trans
            (isClosed_chartBallImage (H := H) data.χ data.R
              (fun y hy => data.hχsrc y hy)).closure_subset) hclose
        rcases hxA with ⟨y, hy, hxy⟩
        have hsrc0 : y ∈ data.χ.source := data.hχsrc y hy
        have hxtgt : x ∈ data.χ.target := by
          rw [← hxy]
          exact data.χ.map_source hsrc0
        have hdeep : modelSharpUnionUnround hk ε r δ (data.χ.symm x) = data.χ.symm x := by
          have hsymm : data.χ.symm x = y := by
            rw [← hxy]
            exact data.χ.left_inv hsrc0
          rw [hsymm]
          have hneg : r ^ 2 + 2 * ε + δ ≤ ‖negPart hk y‖ ^ 2 := by
            by_cases hbW : x ∈ morseChartBallImage hk c data
            · have hnotCore : x ∉ morseChartCoreBallImage hk c data := by
                intro hc
                exact hx.2 ⟨hc, hbW⟩
              have hnot : ¬ ‖negPart hk (data.χ.symm x)‖ < data.R / 2 := by
                intro hlt
                exact hnotCore ⟨chartSymm_mem_target_of_mem_ballImage hk c data hbW, hlt⟩
              have hge : data.R / 2 ≤ ‖negPart hk (data.χ.symm x)‖ := by nlinarith [hnot]
              rw [hsymm] at hge
              exact negPart_norm_sq_ge_of_lower_bound hk c ε r δ data hbig hx.1 hxy hy hge
            · have hnormy : data.R ≤ morseNorm (m + 1) y := by
                have hnot : ¬ morseNorm (m + 1) y < data.R := by
                  intro hylt
                  exact hbW (by dsimp [morseChartBallImage]; refine ⟨y, hylt, hxy⟩)
                nlinarith [hnot]
              have hpos : ‖posPart hk y‖ ^ 2 ≤ ‖negPart hk y‖ ^ 2 - 2 * ε := by
                have hf' : morseNormalForm hk c y ≤ c - ε := by
                  rw [← data.hnorm y hy]
                  rw [hxy]
                  exact (by simpa [sublevel] using hx.1 : f x ≤ c - ε)
                rw [morseNormalForm_split] at hf'
                nlinarith
              have hnorm_sq : ‖negPart hk y‖ ^ 2 + ‖posPart hk y‖ ^ 2 ≥ data.R ^ 2 := by
                have hsqy : data.R ^ 2 ≤ morseNorm (m + 1) y ^ 2 := by
                  have hRnonneg : 0 ≤ data.R := le_of_lt data.hRpos
                  exact sq_le_sq.mpr (by
                    rw [abs_of_nonneg hRnonneg, abs_of_nonneg (norm_nonneg _)]
                    exact hnormy)
                have hnorm_sq' : morseNorm (m + 1) y ^ 2 = ‖negPart hk y‖ ^ 2 + ‖posPart hk y‖ ^ 2 := by
                  calc
                    morseNorm (m + 1) y ^ 2 =
                        morseNorm (m + 1) (recombine hk (negPart hk y) (posPart hk y)) ^ 2 := by
                      rw [recombine_decompose hk y]
                    _ = ‖negPart hk y‖ ^ 2 + ‖posPart hk y‖ ^ 2 :=
                      morseNorm_recombine_sq hk (negPart hk y) (posPart hk y)
                nlinarith [hsqy, hnorm_sq']
              have hsqneg : (data.R / 2) ^ 2 ≤ ‖negPart hk y‖ ^ 2 := by
                nlinarith [hpos, hnorm_sq, hε, sq_nonneg (‖posPart hk y‖)]
              have habs := sq_le_sq.mp hsqneg
              rw [abs_of_nonneg (by nlinarith [data.hRpos] : 0 ≤ data.R / 2),
                abs_of_nonneg (norm_nonneg (negPart hk y))] at habs
              exact negPart_norm_sq_ge_of_lower_bound hk c ε r δ data hbig hx.1 hxy hy habs
          exact modelSharpUnionUnround_eq_self_of_negPart_large hk ε r δ hδ0 hδr hneg
        have hsrcModel : modelSharpUnionUnround hk ε r δ (data.χ.symm x) ∈ data.χ.source := by
          rw [hdeep]
          rw [← hxy]
          rw [data.χ.left_inv hsrc0]
          exact hsrc0
        have hchart : ContinuousAt (fun z : M => data.χ (modelSharpUnionUnround hk ε r δ (data.χ.symm z))) x := by
          have hcontSymm : ContinuousAt data.χ.symm x := by
            exact (data.χ.continuousOn_invFun x hxtgt).continuousAt
              (IsOpen.mem_nhds data.χ.open_target hxtgt)
          have hcontModel : ContinuousAt (modelSharpUnionUnround hk ε r δ) (data.χ.symm x) :=
            (continuous_modelSharpUnionUnround hk ε r δ hδ0 hδr).continuousAt
          have hcontχ : ContinuousAt data.χ (modelSharpUnionUnround hk ε r δ (data.χ.symm x)) := by
            exact (data.χ.continuousOn_toFun (modelSharpUnionUnround hk ε r δ (data.χ.symm x)) hsrcModel).continuousAt
              (IsOpen.mem_nhds data.χ.open_source hsrcModel)
          exact (hcontχ.comp hcontModel).comp hcontSymm
        have hchartx : data.χ (modelSharpUnionUnround hk ε r δ (data.χ.symm x)) = x := by
          rw [hdeep]
          exact data.χ.right_inv hxtgt
        have hT : Filter.Tendsto (fun z : M => data.χ (modelSharpUnionUnround hk ε r δ (data.χ.symm z)))
            (nhdsWithin x U) (nhds (data.χ (modelSharpUnionUnround hk ε r δ (data.χ.symm x)))) :=
          hchart.tendsto.mono_left nhdsWithin_le_nhds
        simpa [hchartx] using hT
      · rw [(notMem_closure_iff_nhdsWithin_eq_bot).mp (by
          intro hz
          exact hclose ((closure_mono (by intro y hy; exact hy.2)) hz))]
        exact Filter.tendsto_bot
    exact continuousAt_piecewise_open_compl (morseSharpUnionUnround hk c ε r δ data)
      (fun z : M => data.χ (modelSharpUnionUnround hk ε r δ (data.χ.symm z))) U x hx.2
      (fun z hzU => by
        dsimp [morseSharpUnionUnround]
        rw [if_pos hzU])
      (fun z hzUc => by
        dsimp [morseSharpUnionUnround]
        rw [if_neg hzUc])
      hg
  intro x hx
  by_cases hxU : x ∈ U
  · have hcontUR : ContinuousWithinAt (morseSharpUnionUnround hk c ε r δ data) (U ∩ R) x :=
      hUR.continuousWithinAt ⟨hxU, hx⟩
    have hUev : ∀ᶠ y in nhds x, y ∈ U := IsOpen.mem_nhds hUopen hxU
    have hEq : nhdsWithin x R = nhdsWithin x (U ∩ R) := by
      rw [nhdsWithin_eq_iff_eventuallyEq]
      refine hUev.mono ?_
      intro y hyU
      exact propext (by
        constructor
        · intro hy
          exact ⟨hyU, hy⟩
        · intro hy
          exact hy.2)
    rw [ContinuousWithinAt, hEq]
    exact hcontUR
  · have hxlow : x ∈ sublevel f (c - ε) := by
      rcases hx with hx' | hx'
      · exact False.elim (hxU (by
          rcases hx' with ⟨y, hy, hxy⟩
          have hyb : morseNorm (m + 1) y < data.R :=
            morseNorm_lt_of_mem_attached_negPart_lt hk ε r δ data.R (le_of_lt hε) hδ0 hδr hεr'
              data.hRpos hy.1 hy.2
          have hsrc0 : y ∈ data.χ.source := data.hχsrc y (le_of_lt hyb)
          constructor
          · constructor
            · rw [← hxy]
              exact data.χ.map_source hsrc0
            · rw [← hxy]
              rw [data.χ.left_inv hsrc0]
              exact hy.2
          · dsimp [morseChartBallImage]
            refine ⟨y, hyb, hxy⟩))
      · exact hx'.1
    exact (hboundary x ⟨hxlow, hxU⟩).continuousWithinAt

noncomputable def morseSharpUnionRoundingHomeo {m k : ℕ} (hk : k ≤ m + 1) (c ε r δ : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} {f : M → ℝ}
    (data : MorseChart (m + 1) k hk c I f)
    (hε : 0 < ε) (hδ0 : 0 < δ) (hδr : δ < r ^ 2) (hr : 0 < r)
    (hεr' : Real.sqrt (2 * ε + 2 * r ^ 2) < data.R / 2)
    (hbig : r ^ 2 + ε + δ ≤ data.R ^ 2 / 8)
    (hcont : Continuous f) :
    {x : M // x ∈ sublevel f (c - ε) ∪ Set.range (handleEmbedding hk c ε r data)} ≃ₜ
      {x : M // x ∈ morseRoundedAttachment hk c ε r δ data} where
  toFun := fun x => ⟨morseSharpUnionRound hk c ε r δ data x.1,
    morseSharpUnionRound_mem_rounded hk c ε r δ data hε hδ0 hδr hεr' hbig x.2⟩
  invFun := fun x => ⟨morseSharpUnionUnround hk c ε r δ data x.1,
    morseSharpUnionUnround_mem_sharpUnion hk c ε r δ data hε hδ0 hδr hr hεr' x.2⟩
  left_inv := by
    intro x
    apply Subtype.ext
    exact morseSharpUnionUnround_round hk c ε r δ data hε hδ0 hδr hεr' hbig x.2
  right_inv := by
    intro x
    apply Subtype.ext
    exact morseSharpUnionRound_unround hk c ε r δ data hε hδ0 hδr hr hεr' hbig x.2
  continuous_toFun := by
    have hrest : Continuous (fun x : {x : M // x ∈ sublevel f (c - ε) ∪
        Set.range (handleEmbedding hk c ε r data)} =>
        morseSharpUnionRound hk c ε r δ data x.1) :=
      continuousOn_iff_continuous_restrict.mp
        (continuousOn_morseSharpUnionRound hk c ε r δ data hε hδ0 hδr hεr' hbig hcont)
    exact Continuous.subtype_mk hrest (fun x =>
      morseSharpUnionRound_mem_rounded hk c ε r δ data hε hδ0 hδr hεr' hbig x.2)
  continuous_invFun := by
    have hrest : Continuous (fun x : {x : M // x ∈ morseRoundedAttachment hk c ε r δ data} =>
        morseSharpUnionUnround hk c ε r δ data x.1) :=
      continuousOn_iff_continuous_restrict.mp
        (continuousOn_morseSharpUnionUnround hk c ε r δ data hε hδ0 hδr (ne_of_gt hr) hεr' hbig)
    exact Continuous.subtype_mk hrest (fun x =>
      morseSharpUnionUnround_mem_sharpUnion hk c ε r δ data hε hδ0 hδr hr hεr' x.2)

theorem morseSharpUnionRound_eq_self_of_deep {m k : ℕ} (hk : k ≤ m + 1) (c ε r δ η : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} {f : M → ℝ}
    (data : MorseChart (m + 1) k hk c I f)
    (hδ0 : 0 < δ) (hδr : δ < r ^ 2)
    (hη : r ^ 2 + δ ≤ 2 * η)
    {x : M} (hx : f x ≤ c - ε - η) :
    morseSharpUnionRound hk c ε r δ data x = x := by
  by_cases hb : x ∈ morseChartBallImage hk c data
  · dsimp [morseChartBallImage] at hb
    rcases hb with ⟨y, hy, hxy⟩
    have hsrc0 : y ∈ data.χ.source := data.hχsrc y (le_of_lt hy)
    have hsymm : data.χ.symm x = y := by
      rw [← hxy]
      exact data.χ.left_inv hsrc0
    have hdeep : modelSharpUnionRound hk ε r δ (data.χ.symm x) = data.χ.symm x := by
      rw [hsymm]
      exact modelSharpUnionRound_eq_self_of_deep hk c ε r δ η hδ0 hδr hη (by
        rw [← data.hnorm y (le_of_lt hy)]
        rw [hxy]
        exact hx)
    calc
      morseSharpUnionRound hk c ε r δ data x = data.χ (modelSharpUnionRound hk ε r δ (data.χ.symm x)) := by
        dsimp [morseSharpUnionRound]
        rw [if_pos (by exact ⟨y, hy, hxy⟩)]
      _ = data.χ (data.χ.symm x) := by rw [hdeep]
      _ = x := by
        rw [← hxy]
        exact data.χ.right_inv (data.χ.map_source hsrc0)
  · dsimp [morseSharpUnionRound]
    rw [if_neg hb]

theorem morseSharpUnionUnround_eq_self_of_deep {m k : ℕ} (hk : k ≤ m + 1) (c ε r δ η : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} {f : M → ℝ}
    (data : MorseChart (m + 1) k hk c I f)
    (hδ0 : 0 < δ) (hδr : δ < r ^ 2)
    (hη : r ^ 2 + δ ≤ 2 * η)
    {x : M} (hx : f x ≤ c - ε - η) :
    morseSharpUnionUnround hk c ε r δ data x = x := by
  by_cases hb : x ∈ morseChartCoreBallImage hk c data ∩ morseChartBallImage hk c data
  · rcases hb.2 with ⟨y, hy, hxy⟩
    have hsrc0 : y ∈ data.χ.source := data.hχsrc y (le_of_lt hy)
    have hsymm : data.χ.symm x = y := by
      rw [← hxy]
      exact data.χ.left_inv hsrc0
    have hdeep : modelSharpUnionUnround hk ε r δ (data.χ.symm x) = data.χ.symm x := by
      rw [hsymm]
      exact modelSharpUnionUnround_eq_self_of_deep hk c ε r δ η hδ0 hδr hη (by
        rw [← data.hnorm y (le_of_lt hy)]
        rw [hxy]
        exact hx)
    calc
      morseSharpUnionUnround hk c ε r δ data x =
          data.χ (modelSharpUnionUnround hk ε r δ (data.χ.symm x)) := by
        dsimp [morseSharpUnionUnround]
        rw [if_pos hb]
      _ = data.χ (data.χ.symm x) := by rw [hdeep]
      _ = x := by
        rw [← hxy]
        exact data.χ.right_inv (data.χ.map_source hsrc0)
  · dsimp [morseSharpUnionUnround]
    rw [if_neg hb]

theorem morseSharpUnionRoundingHomeo_rel_deep {m k : ℕ} (hk : k ≤ m + 1) (c ε r δ η : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} {f : M → ℝ}
    (data : MorseChart (m + 1) k hk c I f)
    (hε : 0 < ε) (hδ0 : 0 < δ) (hδr : δ < r ^ 2) (hr : 0 < r)
    (hεr' : Real.sqrt (2 * ε + 2 * r ^ 2) < data.R / 2)
    (hbig : r ^ 2 + ε + δ ≤ data.R ^ 2 / 8)
    (hcont : Continuous f) (hη : r ^ 2 + δ ≤ 2 * η)
    (x : {x : M // x ∈ sublevel f (c - ε) ∪ Set.range (handleEmbedding hk c ε r data)})
    (hx : f x.1 ≤ c - ε - η) :
    (morseSharpUnionRoundingHomeo hk c ε r δ data hε hδ0 hδr hr hεr' hbig hcont x).1 = x.1 := by
  change morseSharpUnionRound hk c ε r δ data x.1 = x.1
  exact morseSharpUnionRound_eq_self_of_deep hk c ε r δ η data hδ0 hδr hη hx

theorem morseSharpUnionRoundingHomeo_symm_rel_deep {m k : ℕ} (hk : k ≤ m + 1) (c ε r δ η : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} {f : M → ℝ}
    (data : MorseChart (m + 1) k hk c I f)
    (hε : 0 < ε) (hδ0 : 0 < δ) (hδr : δ < r ^ 2) (hr : 0 < r)
    (hεr' : Real.sqrt (2 * ε + 2 * r ^ 2) < data.R / 2)
    (hbig : r ^ 2 + ε + δ ≤ data.R ^ 2 / 8)
    (hcont : Continuous f) (hη : r ^ 2 + δ ≤ 2 * η)
    (x : {x : M // x ∈ morseRoundedAttachment hk c ε r δ data})
    (hx : f x.1 ≤ c - ε - η) :
    (morseSharpUnionRoundingHomeo hk c ε r δ data hε hδ0 hδr hr hεr' hbig hcont).symm x =
      ⟨x.1, Or.inl (by
        change f x.1 ≤ c - ε
        exact le_trans hx (by nlinarith [hδ0, hη]))⟩ := by
  apply Subtype.ext
  change morseSharpUnionUnround hk c ε r δ data x.1 = x.1
  exact morseSharpUnionUnround_eq_self_of_deep hk c ε r δ η data hδ0 hδr hη hx

noncomputable def morseHandleAdjunctionEquivRounded {m k : ℕ} (hk : k ≤ m + 1) (c ε r δ : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} {f : M → ℝ}
    (data : MorseChart (m + 1) k hk c I f)
    (hε : 0 < ε) (hδ0 : 0 < δ) (hδr : δ < r ^ 2) (hr : 0 < r)
    (hεr' : Real.sqrt (2 * ε + 2 * r ^ 2) < data.R / 2)
    (hbig : r ^ 2 + ε + δ ≤ data.R ^ 2 / 8)
    (hcont : Continuous f) :
    Handle.AdjunctionSpace k (m + 1 - k)
      (morseAttachingEmbedding hk c ε r data hε
        (le_trans (le_of_lt hεr') (by nlinarith [data.hRpos] : data.R / 2 ≤ data.R))) ≃ₜ
      {x : M // x ∈ morseRoundedAttachment hk c ε r δ data} :=
  (morseHandleAdjunctionHomeoUnion hk c ε r data hε (ne_of_gt hr)
      (le_trans (le_of_lt hεr') (by nlinarith [data.hRpos] : data.R / 2 ≤ data.R)) hcont).trans
    (morseSharpUnionRoundingHomeo hk c ε r δ data hε hδ0 hδr hr hεr' hbig hcont)

theorem morseHandleAdjunctionEquivRounded_rel_deep {m k : ℕ} (hk : k ≤ m + 1) (c ε r δ η : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} {f : M → ℝ}
    (data : MorseChart (m + 1) k hk c I f)
    (hε : 0 < ε) (hδ0 : 0 < δ) (hδr : δ < r ^ 2) (hr : 0 < r)
    (hεr' : Real.sqrt (2 * ε + 2 * r ^ 2) < data.R / 2)
    (hbig : r ^ 2 + ε + δ ≤ data.R ^ 2 / 8)
    (hcont : Continuous f) (hη : r ^ 2 + δ ≤ 2 * η)
    (x : SublevelSpace f (c - ε - η)) :
    (morseHandleAdjunctionEquivRounded hk c ε r δ data hε hδ0 hδr hr hεr' hbig hcont
      (Handle.lower (morseAttachingEmbedding hk c ε r data hε
        (le_trans (le_of_lt hεr') (by nlinarith [data.hRpos] : data.R / 2 ≤ data.R)))
        ⟨x.1, by
          have hx : f x.1 ≤ c - ε - η := by
            change f x.1 ≤ c - ε - η
            exact x.2
          have hsum : 0 ≤ r ^ 2 + δ := by positivity
          have hη0 : 0 ≤ η := by nlinarith [hη, hsum]
          exact le_trans hx (by nlinarith [hη0])⟩)).1 = x.1 := by
  have hx : f x.1 ≤ c - ε - η := by
    change f x.1 ≤ c - ε - η
    exact x.2
  change morseSharpUnionRound hk c ε r δ data
    (morseHandleAdjunctionHomeoUnion hk c ε r data hε (ne_of_gt hr)
      (le_trans (le_of_lt hεr') (by nlinarith [data.hRpos] : data.R / 2 ≤ data.R)) hcont
      (Handle.lower (morseAttachingEmbedding hk c ε r data hε
        (le_trans (le_of_lt hεr') (by nlinarith [data.hRpos] : data.R / 2 ≤ data.R)))
        ⟨x.1, by
          have hsum : 0 ≤ r ^ 2 + δ := by positivity
          have hη0 : 0 ≤ η := by nlinarith [hη, hsum]
          exact le_trans hx (by nlinarith [hη0])⟩)).1 = x.1
  rw [morseHandleAdjunctionHomeoUnion_lower hk c ε r data hε (ne_of_gt hr)
    (le_trans (le_of_lt hεr') (by nlinarith [data.hRpos] : data.R / 2 ≤ data.R)) hcont
    ⟨x.1, by
      have hsum : 0 ≤ r ^ 2 + δ := by positivity
      have hη0 : 0 ≤ η := by nlinarith [hη, hsum]
      exact le_trans hx (by nlinarith [hη0])⟩]
  exact morseSharpUnionRound_eq_self_of_deep hk c ε r δ η data hδ0 hδr hη hx

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

theorem morseModifiedRetractionHomotopy_eq_self_of_mem_lowerUnion {n k : ℕ} (hk : k ≤ n)
    (c ε R : ℝ) (hε : 0 < ε) (hεR : Real.sqrt (2 * ε) ≤ R)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    (χ : OpenPartialHomeomorph (MorseModel n) M) (f : M → ℝ)
    (hnorm : ∀ y : MorseModel n, morseNorm n y ≤ R → f (χ y) = morseNormalForm hk c y)
    (hχsrc : ∀ y : MorseModel n, morseNorm n y ≤ R → y ∈ χ.source)
    {t : ℝ} {x : M}
    (hx : x ∈ sublevel f (c - ε) ∪ χ '' (Set.range (fun z : ClosedCell k =>
      cellMap (Real.sqrt (2 * ε)) (z : EuclideanSpace ℝ (Fin k))))) :
    morseModifiedRetractionHomotopy (H := H) (M := M) hk c ε R χ t x = x := by
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
      dsimp [morseModifiedRetractionHomotopy]
      rw [if_pos ⟨y, hy, hxy⟩]
      rw [modifiedCollarHomotopy_eq_self_of_lower hk c ε (by simpa [hsymm] using hfy)]
      exact χ.right_inv (by
        rw [← hxy]
        exact χ.map_source (hχsrc y hy))
    · dsimp [morseModifiedRetractionHomotopy]
      rw [if_neg hC]
  · rcases hcell with ⟨y, hy, hxy⟩
    have hyCell : y ∈ Set.range (fun z : ClosedCell k =>
        cellMap (Real.sqrt (2 * ε)) (z : EuclideanSpace ℝ (Fin k))) := hy
    rcases hy with ⟨u, hu⟩
    have hyb : morseNorm n y ≤ R := by
      rw [← hu]
      exact norm_cellMap_le hk ε R hεR (u : EuclideanSpace ℝ (Fin k)) u.2
    have hfix : modifiedCollarHomotopy hk c ε t y = y :=
      modifiedCollarHomotopy_fix_cell hk c ε hε hyCell
    have hsymm : χ.symm x = y := by
      rw [← hxy]
      exact χ.left_inv (hχsrc y hyb)
    dsimp [morseModifiedRetractionHomotopy]
    rw [if_pos ⟨y, hyb, hxy⟩]
    rw [hsymm, hfix]
    exact hxy

theorem modifiedCollarHomotopy_fix_handle {n k : ℕ} (hk : k ≤ n) (c ε r : ℝ)
    (hε : 0 < ε) {t : ℝ} {y : MorseModel n}
    (hy : y ∈ Set.range (fun p : CellBoundary k × ClosedCell (n - k) =>
      cocoreModelPoint hk ε r p)) :
    modifiedCollarHomotopy hk c ε t y = y := by
  rcases hy with ⟨p, hp⟩
  have hfy : morseNormalForm hk c y ≤ c - ε := by
    rw [← hp]
    exact le_of_eq (morseNormalForm_cocoreModelPoint hk c ε r (le_of_lt hε) p)
  dsimp [modifiedCollarHomotopy]
  rw [if_pos hfy]

theorem modifiedNormalForm_cocoreModelPoint_mem_lower {n k : ℕ} (hk : k ≤ n) (c ε r δ : ℝ)
    (hε : 0 < ε) (p : CellBoundary k × ClosedCell (n - k)) :
    modifiedNormalForm hk c ε δ (cocoreModelPoint hk ε r p) ≤ c - ε := by
  rw [modifiedNormalForm_eq_sub_dip]
  have hnf : morseNormalForm hk c (cocoreModelPoint hk ε r p) = c - ε :=
    morseNormalForm_cocoreModelPoint hk c ε r (le_of_lt hε) p
  rw [hnf]
  have hd : 0 ≤ modelModifiedDip hk ε δ (cocoreModelPoint hk ε r p) :=
    modelModifiedDip_nonneg hk ε δ (le_of_lt hε) _
  linarith

theorem lowerHandleUnion_subset_modifiedSublevel {n k : ℕ} (hk : k ≤ n) (c ε r δ R : ℝ)
    (hε : 0 < ε) (hεr : Real.sqrt (2 * ε + 2 * r ^ 2) ≤ R)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    (χ : OpenPartialHomeomorph (MorseModel n) M) (f : M → ℝ)
    (hnorm : ∀ y : MorseModel n, morseNorm n y ≤ R → f (χ y) = morseNormalForm hk c y)
    (hχsrc : ∀ y : MorseModel n, morseNorm n y ≤ R → y ∈ χ.source) :
    {x : M | x ∈ sublevel f (c - ε) ∪ χ '' (Set.range (fun p : CellBoundary k × ClosedCell (n - k) =>
      cocoreModelPoint hk ε r p))} ⊆
    {x : M | morseModifiedFunction (H := H) (M := M) hk c ε δ R χ f x ≤ c - ε} := by
  let g : M → ℝ := morseModifiedFunction (H := H) (M := M) hk c ε δ R χ f
  intro x hx
  change g x ≤ c - ε
  rcases hx with hflow | hhandle
  · have hle : g x ≤ f x := morseModifiedFunction_le_f (H := H) (M := M) hk c ε δ R hε χ f hnorm x
    exact le_trans hle hflow
  · rcases hhandle with ⟨y, hy, hxy⟩
    rcases hy with ⟨p, hp⟩
    have hyb : morseNorm n y ≤ R := by
      rw [← hp]
      exact le_trans (cocoreModelPoint_norm_le hk ε r (le_of_lt hε) p) hεr
    have hysrc : y ∈ χ.source := hχsrc y hyb
    have hgx : g x = modifiedNormalForm hk c ε δ y := by
      dsimp [g, morseModifiedFunction]
      rw [← hxy, if_pos (χ.map_source hysrc), χ.left_inv hysrc, if_pos hyb]
    rw [hgx]
    rw [← hp]
    exact modifiedNormalForm_cocoreModelPoint_mem_lower hk c ε r δ hε p

theorem morseModifiedRetraction_eq_self_of_mem_lowerHandleUnion {n k : ℕ} (hk : k ≤ n)
    (c ε r R : ℝ) (hε : 0 < ε) (hεr : Real.sqrt (2 * ε + 2 * r ^ 2) ≤ R)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    (χ : OpenPartialHomeomorph (MorseModel n) M) (f : M → ℝ)
    (hnorm : ∀ y : MorseModel n, morseNorm n y ≤ R → f (χ y) = morseNormalForm hk c y)
    (hχsrc : ∀ y : MorseModel n, morseNorm n y ≤ R → y ∈ χ.source)
    {x : M}
    (hx : x ∈ sublevel f (c - ε) ∪ χ '' (Set.range (fun p : CellBoundary k × ClosedCell (n - k) =>
      cocoreModelPoint hk ε r p))) :
    morseModifiedRetraction (H := H) (M := M) hk c ε R χ x = x := by
  let ball : Set (MorseModel n) := {y : MorseModel n | morseNorm n y ≤ R}
  rcases hx with hflow | hhandle
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
  · rcases hhandle with ⟨y, hy, hxy⟩
    have hyHandle : y ∈ Set.range (fun p : CellBoundary k × ClosedCell (n - k) =>
        cocoreModelPoint hk ε r p) := hy
    rcases hy with ⟨p, hp⟩
    have hyb : morseNorm n y ≤ R := by
      rw [← hp]
      exact le_trans (cocoreModelPoint_norm_le hk ε r (le_of_lt hε) p) hεr
    have hfix : modifiedCollarRetraction hk c ε y = y := by
      have h1 := modifiedCollarHomotopy_fix_handle hk c ε r hε (t := 1) hyHandle
      simpa [modifiedCollarHomotopy_one hk c ε y] using h1
    have hsymm : χ.symm x = y := by
      rw [← hxy]
      exact χ.left_inv (hχsrc y hyb)
    dsimp [morseModifiedRetraction]
    rw [if_pos ⟨y, hyb, hxy⟩]
    rw [hsymm, hfix]
    exact hxy

theorem morseModifiedRetractionHomotopy_eq_self_of_mem_lowerHandleUnion {n k : ℕ} (hk : k ≤ n)
    (c ε r R : ℝ) (hε : 0 < ε) (hεr : Real.sqrt (2 * ε + 2 * r ^ 2) ≤ R)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    (χ : OpenPartialHomeomorph (MorseModel n) M) (f : M → ℝ)
    (hnorm : ∀ y : MorseModel n, morseNorm n y ≤ R → f (χ y) = morseNormalForm hk c y)
    (hχsrc : ∀ y : MorseModel n, morseNorm n y ≤ R → y ∈ χ.source)
    {t : ℝ} {x : M}
    (hx : x ∈ sublevel f (c - ε) ∪ χ '' (Set.range (fun p : CellBoundary k × ClosedCell (n - k) =>
      cocoreModelPoint hk ε r p))) :
    morseModifiedRetractionHomotopy (H := H) (M := M) hk c ε R χ t x = x := by
  let ball : Set (MorseModel n) := {y : MorseModel n | morseNorm n y ≤ R}
  rcases hx with hflow | hhandle
  · by_cases hC : x ∈ χ '' ball
    · rcases hC with ⟨y, hy, hxy⟩
      have hfy : morseNormalForm hk c y ≤ c - ε := by
        have hfx : f (χ y) ≤ c - ε := by
          simpa [hxy] using hflow
        rwa [hnorm y hy] at hfx
      have hsymm : χ.symm x = y := by
        rw [← hxy]
        exact χ.left_inv (hχsrc y hy)
      dsimp [morseModifiedRetractionHomotopy]
      rw [if_pos ⟨y, hy, hxy⟩]
      rw [modifiedCollarHomotopy_eq_self_of_lower hk c ε (by simpa [hsymm] using hfy)]
      exact χ.right_inv (by
        rw [← hxy]
        exact χ.map_source (hχsrc y hy))
    · dsimp [morseModifiedRetractionHomotopy]
      rw [if_neg hC]
  · rcases hhandle with ⟨y, hy, hxy⟩
    have hyb : morseNorm n y ≤ R := by
      rcases hy with ⟨p, hp⟩
      rw [← hp]
      exact le_trans (cocoreModelPoint_norm_le hk ε r (le_of_lt hε) p) hεr
    have hfix : modifiedCollarHomotopy hk c ε t y = y :=
      modifiedCollarHomotopy_fix_handle hk c ε r hε hy
    have hsymm : χ.symm x = y := by
      rw [← hxy]
      exact χ.left_inv (hχsrc y hyb)
    dsimp [morseModifiedRetractionHomotopy]
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

noncomputable def sublevelInclusionLE {M : Type} [TopologicalSpace M] {f g : M → ℝ}
    (hg_le : ∀ x : M, g x ≤ f x) (a : ℝ) : C(SublevelSpace f a, SublevelSpace g a) :=
  ContinuousMap.mk
    (fun x : SublevelSpace f a => ⟨x.1, le_trans (hg_le x.1) (by change f x.1 ≤ a; exact x.2)⟩)
    (by
      exact Continuous.subtype_mk continuous_subtype_val (by
        intro x
        exact le_trans (hg_le x.1) (by change f x.1 ≤ a; exact x.2)))

noncomputable def sublevelUnionInclusion {M : Type} [TopologicalSpace M] {f : M → ℝ}
    (a : ℝ) (S : Set M) : C(SublevelSpace f a, {x : M // x ∈ sublevel f a ∪ S}) :=
  ContinuousMap.mk
    (fun x : SublevelSpace f a => ⟨x.1, Or.inl x.2⟩)
    (by
      exact Continuous.subtype_mk continuous_subtype_val (by intro x; exact Or.inl x.2))

noncomputable def modifiedLowerSublevelInclusion {n k : ℕ} (hk : k ≤ n) (c ε δ R : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    (χ : OpenPartialHomeomorph (MorseModel n) M) (f : M → ℝ)
    (hg_le : ∀ x : M, morseModifiedFunction (H := H) (M := M) hk c ε δ R χ f x ≤ f x) :
    C(SublevelSpace f (c - ε),
      SublevelSpace (morseModifiedFunction (H := H) (M := M) hk c ε δ R χ f) (c - ε)) :=
  sublevelInclusionLE hg_le (c - ε)

noncomputable def modifiedLowerSublevelUnionInclusion {n k : ℕ} (c ε : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    (χ : OpenPartialHomeomorph (MorseModel n) M) (f : M → ℝ) :
    C(SublevelSpace f (c - ε), {x : M // x ∈ sublevel f (c - ε) ∪ χ '' (Set.range (fun z : ClosedCell k =>
      cellMap (Real.sqrt (2 * ε)) (z : EuclideanSpace ℝ (Fin k))))}) :=
  sublevelUnionInclusion (c - ε) (χ '' (Set.range (fun z : ClosedCell k =>
    cellMap (Real.sqrt (2 * ε)) (z : EuclideanSpace ℝ (Fin k)))))

noncomputable def morseModifiedLowerSublevelHomotopyEquivUnder {n k : ℕ} (hk : k ≤ n)
    (c ε δ R : ℝ) (hε : 0 < ε) (hδ : 0 < δ) (hR : 4 * ε + 9 * δ ^ 2 / 4 < R ^ 2)
    (hRpos : 0 < R) (hεR : Real.sqrt (2 * ε) ≤ R)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
    (χ : OpenPartialHomeomorph (MorseModel n) M) (f : M → ℝ)
    (hg : Continuous (morseModifiedFunction (H := H) (M := M) hk c ε δ R χ f))
    (hnorm : ∀ y : MorseModel n, morseNorm n y ≤ R → f (χ y) = morseNormalForm hk c y)
    (hχsrc : ∀ y : MorseModel n, morseNorm n y ≤ R → y ∈ χ.source) :
    HomotopyEquivUnder
      (X := SublevelSpace f (c - ε))
      (Y := SublevelSpace (morseModifiedFunction (H := H) (M := M) hk c ε δ R χ f) (c - ε))
      (Z := {x : M // x ∈ sublevel f (c - ε) ∪ χ '' (Set.range (fun z : ClosedCell k =>
        cellMap (Real.sqrt (2 * ε)) (z : EuclideanSpace ℝ (Fin k))))})
      (toBase := modifiedLowerSublevelInclusion hk c ε δ R χ f
        (morseModifiedFunction_le_f (H := H) (M := M) hk c ε δ R hε χ f hnorm))
      (fromBase := modifiedLowerSublevelUnionInclusion (H := H) (M := M) c ε χ f) where
  toFun := (morseModifiedLowerSublevelHomotopyEquiv hk c ε δ R hε hδ hR hRpos hεR χ f hg hnorm hχsrc).toFun
  invFun := (morseModifiedLowerSublevelHomotopyEquiv hk c ε δ R hε hδ hR hRpos hεR χ f hg hnorm hχsrc).invFun
  map_toBase := by
    ext x
    change morseModifiedRetraction (H := H) (M := M) hk c ε R χ x.1 = x.1
    exact morseModifiedRetraction_eq_self_of_mem_lowerUnion (H := H) (M := M) hk c ε R hε hεR
      χ f hnorm hχsrc (Or.inl x.2)
  map_fromBase := by
    ext x
    rfl
  left_inv := by
    let Y : Type := SublevelSpace (morseModifiedFunction (H := H) (M := M) hk c ε δ R χ f) (c - ε)
    let toFun : C(Y, {x : M // x ∈ sublevel f (c - ε) ∪ χ '' (Set.range (fun z : ClosedCell k =>
      cellMap (Real.sqrt (2 * ε)) (z : EuclideanSpace ℝ (Fin k))))}) :=
      (morseModifiedLowerSublevelHomotopyEquiv hk c ε δ R hε hδ hR hRpos hεR χ f hg hnorm hχsrc).toFun
    let invFun : C({x : M // x ∈ sublevel f (c - ε) ∪ χ '' (Set.range (fun z : ClosedCell k =>
      cellMap (Real.sqrt (2 * ε)) (z : EuclideanSpace ℝ (Fin k))))}, Y) :=
      (morseModifiedLowerSublevelHomotopyEquiv hk c ε δ R hε hδ hR hRpos hεR χ f hg hnorm hχsrc).invFun
    let F : (Set.Icc (0 : ℝ) 1) × Y → Y := fun p =>
      Subtype.mk (morseModifiedRetractionHomotopy (H := H) (M := M) hk c ε R χ (1 - (p.1 : ℝ)) p.2.1)
        (by
          have ht0 : 0 ≤ 1 - (p.1 : ℝ) := by exact sub_nonneg.mpr p.1.2.2
          have ht1 : 1 - (p.1 : ℝ) ≤ 1 := by
            exact sub_le_self (a := (1 : ℝ)) (b := (p.1 : ℝ)) p.1.2.1
          exact morseModifiedRetractionHomotopy_mem_sublevel (H := H) (M := M) hk c ε δ R hε hδ
            χ f hχsrc ht0 ht1 p.2.2)
    have hFcont : Continuous F := by
      have hcont : Continuous (fun p : (Set.Icc (0 : ℝ) 1) × Y =>
          morseModifiedRetractionHomotopy (H := H) (M := M) hk c ε R χ (1 - (p.1 : ℝ)) p.2.1) := by
        have hcont' := continuousOn_morseModifiedRetractionHomotopy (H := H) (M := M)
          hk c ε δ R hε hδ hR hRpos χ f hg hχsrc
        have hembed : Continuous (fun p : (Set.Icc (0 : ℝ) 1) × Y => (p.1, p.2.1)) := by
          exact continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)
        have hmem : ∀ p : (Set.Icc (0 : ℝ) 1) × Y,
            (p.1, p.2.1) ∈ (Set.univ : Set (Set.Icc (0 : ℝ) 1)) ×ˢ
              {x : M | morseModifiedFunction (H := H) (M := M) hk c ε δ R χ f x ≤ c - ε} := by
          intro p
          exact ⟨trivial, by simp [sublevel]⟩
        simpa [Function.comp_def] using (hcont'.comp_continuous hembed hmem)
      exact Continuous.subtype_mk (p := fun x : M =>
        x ∈ sublevel (morseModifiedFunction (H := H) (M := M) hk c ε δ R χ f) (c - ε)) hcont (by
        intro p
        change morseModifiedFunction (H := H) (M := M) hk c ε δ R χ f
          (morseModifiedRetractionHomotopy (H := H) (M := M) hk c ε R χ (1 - (p.1 : ℝ)) p.2.1) ≤
          c - ε
        have ht0 : 0 ≤ 1 - (p.1 : ℝ) := by exact sub_nonneg.mpr p.1.2.2
        have ht1 : 1 - (p.1 : ℝ) ≤ 1 := by
          exact sub_le_self (a := (1 : ℝ)) (b := (p.1 : ℝ)) p.1.2.1
        exact morseModifiedRetractionHomotopy_mem_sublevel (H := H) (M := M) hk c ε δ R hε hδ
          χ f hχsrc ht0 ht1 p.2.2)
    refine { toHomotopy := { toFun := ContinuousMap.mk F hFcont, map_zero_left := ?_, map_one_left := ?_ }, prop' := ?_ }
    · intro x
      apply Subtype.ext
      simpa [F, invFun, toFun] using (morseModifiedRetractionHomotopy_one (H := H) (M := M) hk c ε R χ x.1)
    · intro x
      apply Subtype.ext
      simpa [F, invFun, toFun] using
        (morseModifiedRetractionHomotopy_zero (H := H) (M := M) hk c ε R χ hχsrc x.1)
    · intro t x hx
      rcases hx with ⟨y, rfl⟩
      apply Subtype.ext
      calc
        (F (t, modifiedLowerSublevelInclusion hk c ε δ R χ f
            (morseModifiedFunction_le_f (H := H) (M := M) hk c ε δ R hε χ f hnorm) y)).1 =
            morseModifiedRetractionHomotopy (H := H) (M := M) hk c ε R χ (1 - (t : ℝ)) y.1 := by
          simp [F, modifiedLowerSublevelInclusion, sublevelInclusionLE]
        _ = y.1 :=
          morseModifiedRetractionHomotopy_eq_self_of_mem_lowerUnion (H := H) (M := M) hk c ε R hε hεR
            χ f hnorm hχsrc (Or.inl y.2)
        _ = ((invFun.comp toFun)
            (modifiedLowerSublevelInclusion hk c ε δ R χ f
              (morseModifiedFunction_le_f (H := H) (M := M) hk c ε δ R hε χ f hnorm) y)).1 := by
          symm
          calc
            ((invFun.comp toFun)
                (modifiedLowerSublevelInclusion hk c ε δ R χ f
                  (morseModifiedFunction_le_f (H := H) (M := M) hk c ε δ R hε χ f hnorm) y)).1 =
                ((morseModifiedLowerSublevelHomotopyEquiv hk c ε δ R hε hδ hR hRpos hεR χ f hg hnorm hχsrc).toFun
                  (modifiedLowerSublevelInclusion hk c ε δ R χ f
                    (morseModifiedFunction_le_f (H := H) (M := M) hk c ε δ R hε χ f hnorm) y)).1 := by
              rfl
            _ = y.1 := (morseModifiedLowerSublevelHomotopyEquiv_lower hk c ε δ R hε hδ hR hRpos hεR χ f hg hnorm hχsrc).1 y
  right_inv := by
    let Z : Type := {x : M // x ∈ sublevel f (c - ε) ∪ χ '' (Set.range (fun z : ClosedCell k =>
      cellMap (Real.sqrt (2 * ε)) (z : EuclideanSpace ℝ (Fin k))))}
    have h : (morseModifiedLowerSublevelHomotopyEquiv hk c ε δ R hε hδ hR hRpos hεR χ f hg hnorm hχsrc).toFun.comp
        (morseModifiedLowerSublevelHomotopyEquiv hk c ε δ R hε hδ hR hRpos hεR χ f hg hnorm hχsrc).invFun =
        ContinuousMap.id Z := by
      ext x
      calc
        ((morseModifiedLowerSublevelHomotopyEquiv hk c ε δ R hε hδ hR hRpos hεR χ f hg hnorm hχsrc).toFun
          ((morseModifiedLowerSublevelHomotopyEquiv hk c ε δ R hε hδ hR hRpos hεR χ f hg hnorm hχsrc).invFun x)).1
            = morseModifiedRetraction (H := H) (M := M) hk c ε R χ x.1 := rfl
        _ = x.1 := (morseModifiedRetraction_eq_self_of_mem_lowerUnion (H := H) (M := M) hk c ε R hε hεR
          χ f hnorm hχsrc x.2)
    exact (ContinuousMap.HomotopyRel.refl (ContinuousMap.id Z)
      (Set.range (modifiedLowerSublevelUnionInclusion (H := H) (M := M) c ε χ f))).cast h.symm rfl

end ManifoldCellAttachment

end
end DifferentialGeometry.Topology.Morse
