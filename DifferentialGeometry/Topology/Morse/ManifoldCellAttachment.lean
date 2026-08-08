import DifferentialGeometry.Topology.Morse.CellAttachment
import DifferentialGeometry.Topology.Handle.Manifold
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
    [NeZero k] [NeZero (n - k)]
    [Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin k)) = (k - 1) + 1)]
    [Fact (n - k = (n - k - 1) + 1)] :
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
    [NeZero k] [NeZero (n - k)]
    [Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin k)) = (k - 1) + 1)]
    [Fact (n - k = (n - k - 1) + 1)] :
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
    [NeZero k] [NeZero (m + 1 - k)]
    [Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin k)) = (k - 1) + 1)]
    [Fact (m + 1 - k = (m + 1 - k - 1) + 1)] :
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
    (hRltR' : data.R < data.R')
    (hf : ContMDiff I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) f)
    (hreg : ∀ x : M, f x = c - ε → ¬ IsCriticalPointAt I f x)
    [NeZero k] [NeZero (m + 1 - k)]
    [Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin k)) = (k - 1) + 1)]
    [Fact (m + 1 - k = (m + 1 - k - 1) + 1)] :
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
    have hnormb : morseNorm (m + 1) (cocoreModelPoint hk ε r p) ≤ data.R := by
      exact le_trans (cocoreModelPoint_norm_le hk ε r (le_of_lt hε) p) hεr
    have hlt : ‖cocoreModelPoint hk ε r p‖ < data.R' :=
      lt_of_le_of_lt (morseNorm_piNorm_le (cocoreModelPoint hk ε r p)) (lt_of_le_of_lt hnormb hRltR')
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
    (hRltR' : data.R < data.R')
    (hf : ContMDiff I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) f)
    (hreg : ∀ x : M, f x = c - ε → ¬ IsCriticalPointAt I f x)
    [NeZero k] [NeZero (m + 1 - k)]
    [Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin k)) = (k - 1) + 1)]
    [Fact (m + 1 - k = (m + 1 - k - 1) + 1)] :
    Topology.IsClosedEmbedding (cocoreAttachingEmbedding hk c ε r data hε hεr) := by
  letI : ChartedSpace (MorseModel m) (LevelSetSpace f (c - ε)) :=
    manifoldLevelSetChartedSpace I f (c - ε) hf hreg
  exact (contMDiff_cocoreAttachingEmbedding hk c ε r data hε hεr hRltR' hf hreg).continuous.isClosedEmbedding
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
    [NeZero k] [NeZero (m + 1 - k)]
    [Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin k)) = (k - 1) + 1)]
    [Fact (m + 1 - k = (m + 1 - k - 1) + 1)] :
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
      simpa [Iatt] using (contMDiff_cocoreAttachingEmbedding hk c ε r data hε hεr hRltR' hf hreg)
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
    [NeZero k] [NeZero (m + 1 - k)]
    [Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin k)) = (k - 1) + 1)]
    [Fact (m + 1 - k = (m + 1 - k - 1) + 1)] :
    Topology.IsClosedEmbedding (handleCollarMap hk c ε r data hε hεr v hcomplete) := by
  exact (contMDiff_handleCollarMap hk c ε r data hε hεr hRltR' hf hreg v hv hsupp hcomplete).continuous.isClosedEmbedding
    (handleCollarMap_injective hk c ε r δ data hε hr hεr hδ hf v hv hdfOn hrate hcomplete)

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

noncomputable def sublevelCellAdjunctionHomotopyEquivUnderOfMorseChart {n : ℕ} {H : Type}
    [TopologicalSpace H] {M : Type} [TopologicalSpace M]
    [ChartedSpace H M] [T2Space M] (I : ModelWithCorners ℝ (MorseModel n) H) [I.Boundaryless]
    [IsManifold I (⊤ : WithTop ℕ∞) M] (f : M → ℝ) (hf : ContMDiff I 𝓘(ℝ, ℝ) (⊤ : WithTop ℕ∞) f)
    (c : ℝ) (k : ℕ) (hk : k ≤ n)
    (data : MorseChart n k hk c I f)
    (g : M → ℝ) (hg : ContMDiff I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) g)
    (hg_le : ∀ x : M, g x ≤ f x)
    (hlow : HomotopyEquivUnder
      (X := SublevelSpace f (c - data.ε))
      (Y := SublevelSpace g (c - data.ε))
      (Z := {x : M // x ∈ sublevel f (c - data.ε) ∪ data.χ '' (Set.range (fun z : ClosedCell k =>
        cellMap (Real.sqrt (2 * data.ε)) (z : EuclideanSpace ℝ (Fin k))))})
      (toBase := sublevelInclusionLE hg_le (c - data.ε))
      (fromBase := sublevelUnionInclusion (c - data.ε) (data.χ '' (Set.range (fun z : ClosedCell k =>
        cellMap (Real.sqrt (2 * data.ε)) (z : EuclideanSpace ℝ (Fin k)))))))
    (hcell : cellImage hk c data = data.χ '' (Set.range (fun z : ClosedCell k =>
      cellMap (Real.sqrt (2 * data.ε)) (z : EuclideanSpace ℝ (Fin k)))))
    (hunion_sub : ∀ x : M, x ∈ sublevel f (c - data.ε) ∪ data.χ '' (Set.range (fun z : ClosedCell k =>
      cellMap (Real.sqrt (2 * data.ε)) (z : EuclideanSpace ℝ (Fin k)))) → g x ≤ c - data.ε)
    (hlow_invFun_val : ∀ z : {x : M // x ∈ sublevel f (c - data.ε) ∪ data.χ '' (Set.range (fun z : ClosedCell k =>
      cellMap (Real.sqrt (2 * data.ε)) (z : EuclideanSpace ℝ (Fin k))))},
      (hlow.invFun z).1 = z.1)
    (hgup : {x : M | g x ≤ c + data.ε} = sublevel f (c + data.ε))
    (v : (x : M) → TangentSpace I x)
    (hv : ContMDiff I (I.prod 𝓘(ℝ, MorseModel n)) ∞
      (fun x : M => (⟨x, v x⟩ : TangentBundle I M)))
    (hsupp : IsCompact (tsupport v))
    (hdfOn : ∀ x ∈ g ⁻¹' Set.Icc (c - data.ε) (c + data.ε),
      (NormedSpace.fromTangentSpace (g x)) ((mfderiv I 𝓘(ℝ, ℝ) g x) (v x)) = -1)
    (hrate : ∀ x,
      -1 ≤ (NormedSpace.fromTangentSpace (g x)) ((mfderiv I 𝓘(ℝ, ℝ) g x) (v x)) ∧
      (NormedSpace.fromTangentSpace (g x)) ((mfderiv I 𝓘(ℝ, ℝ) g x) (v x)) ≤ 0) :
    HomotopyEquivUnder
      (X := SublevelSpace f (c - data.ε)) (Y := SublevelSpace f (c + data.ε))
      (Z := CellAdjunctionSpace k (cellAttachingMap hk c data))
      (toBase := sublevelInclusion f (by linarith [data.hεpos]))
      (fromBase := ContinuousMap.mk (adjunctionLower (i := cellBoundaryInclusion k) (cellAttachingMap hk c data))
        (continuous_adjunctionLower (i := cellBoundaryInclusion k) (cellAttachingMap hk c data))) := by
  let E : Set M := cellImage hk c data
  let φ : C(CellBoundary k, SublevelSpace f (c - data.ε)) := cellAttachingMap hk c data
  let U₀ : Set M := data.χ '' (Set.range (fun z : ClosedCell k =>
    cellMap (Real.sqrt (2 * data.ε)) (z : EuclideanSpace ℝ (Fin k))))
  let Z₀ : Type := {x : M // x ∈ sublevel f (c - data.ε) ∪ U₀}
  let Z' : Type := {x : M // x ∈ sublevel f (c - data.ε) ∪ E}
  let hcomplete : ∀ x : M, ∃ γ : ℝ → M, γ 0 = x ∧ IsMIntegralCurve γ v :=
    exists_globalIntegralCurve_of_compactSupport v hv hsupp
  let T : M → ℝ := fun x => max (g x - (c - data.ε)) 0
  let ι : C(SublevelSpace f (c - data.ε), SublevelSpace f (c + data.ε)) :=
    sublevelInclusion f (by linarith [data.hεpos])
  let j : C(SublevelSpace f (c - data.ε), CellAdjunctionSpace k φ) :=
    ContinuousMap.mk (adjunctionLower (i := cellBoundaryInclusion k) φ)
      (continuous_adjunctionLower (i := cellBoundaryInclusion k) φ)
  have hup_iff : ∀ x : M, g x ≤ c + data.ε ↔ f x ≤ c + data.ε := by
    intro x
    change (x ∈ {y : M | g y ≤ c + data.ε}) ↔ (x ∈ sublevel f (c + data.ε))
    rw [← hgup]
  have hT_nonneg : ∀ x : M, 0 ≤ T x := by
    intro x
    dsimp [T]
    exact le_max_right (g x - (c - data.ε)) 0
  have hT_zero : ∀ x : M, g x ≤ c - data.ε → T x = 0 := by
    intro x hx
    dsimp [T]
    rw [max_eq_right (by linarith)]
  have hT_pos : ∀ x : M, c - data.ε ≤ g x → T x = g x - (c - data.ε) := by
    intro x hx
    dsimp [T]
    rw [max_eq_left (by linarith)]
  have hretr_mem : ∀ y : SublevelSpace f (c + data.ε),
      g (curveAt v hcomplete y.1 (T y.1)) ≤ c - data.ε := by
    intro y
    by_cases hy : c - data.ε ≤ g y.1
    · let s : ℝ := g y.1 - (c - data.ε)
      have hs : 0 ≤ s := by dsimp [s]; linarith
      have hT : T y.1 = s := by
        rw [hT_pos y.1 hy]
      have hstay : ∀ u ∈ Set.Icc (0 : ℝ) s,
          curveAt v hcomplete y.1 u ∈ g ⁻¹' Set.Icc (c - data.ε) (c + data.ε) := by
        intro u hu
        have hrb := f_rate_bounds_of_integralCurve g hg v hrate
          (hγ := curveAt_integralCurve v hcomplete y.1) (t := u) hu.1
        have hglo : g y.1 - u ≤ g (curveAt v hcomplete y.1 u) := by
          simpa [curveAt_zero v hcomplete y.1] using hrb.1
        have hgup'' : g (curveAt v hcomplete y.1 u) ≤ g y.1 := by
          simpa [curveAt_zero v hcomplete y.1] using hrb.2
        have hgy : g y.1 ≤ c + data.ε := by
          exact le_trans (hg_le y.1) (by change f y.1 ≤ c + data.ε; exact y.2)
        constructor
        · change c - data.ε ≤ g (curveAt v hcomplete y.1 u)
          have hle : c - data.ε ≤ g y.1 - u := by
            have hu2 : u ≤ g y.1 - (c - data.ε) := by simpa [s] using hu.2
            linarith
          exact le_trans hle hglo
        · change g (curveAt v hcomplete y.1 u) ≤ c + data.ε
          exact le_trans hgup'' hgy
      have heq := f_eq_sub_of_integralCurve_on_strip g hg v hdfOn
        (hγ := curveAt_integralCurve v hcomplete y.1) (t := s) hs hstay
      have hval : g (curveAt v hcomplete y.1 s) = c - data.ε := by
        have hmain : g (curveAt v hcomplete y.1 s) = g y.1 - s := by
          simpa [curveAt_zero v hcomplete y.1] using heq
        dsimp [s] at hmain ⊢
        linarith
      rw [hT]
      exact le_of_eq hval
    · have hT : T y.1 = 0 := hT_zero y.1 (le_of_not_ge hy)
      rw [hT, curveAt_zero v hcomplete y.1]
      exact le_of_not_ge hy
  have hTcont : Continuous T := by
    dsimp [T]
    exact continuous_max.comp ((hg.continuous.sub continuous_const).prodMk continuous_const)
  let flowRetract : C(SublevelSpace f (c + data.ε), SublevelSpace g (c - data.ε)) :=
    ContinuousMap.mk
      (fun y => ⟨curveAt v hcomplete y.1 (T y.1), hretr_mem y⟩)
      (by
        have hpair : Continuous (fun y : SublevelSpace f (c + data.ε) => (T y.1, y.1)) :=
          (hTcont.comp continuous_subtype_val).prodMk continuous_subtype_val
        have hmain : Continuous (fun y : SublevelSpace f (c + data.ε) =>
            curveAt v hcomplete y.1 (T y.1)) :=
          (continuous_globalFlow_of_compactSupport v hv hsupp).comp hpair
        exact Continuous.subtype_mk hmain (by intro y; exact hretr_mem y))
  let intoUpper : C(SublevelSpace g (c - data.ε), SublevelSpace f (c + data.ε)) :=
    ContinuousMap.mk
      (fun y => ⟨y.1, (hup_iff y.1).1 (by
        have hy' : g y.1 ≤ c - data.ε := by
          change y.1 ∈ sublevel g (c - data.ε)
          exact y.2
        have hle : g y.1 ≤ c + data.ε := by linarith [data.hεpos]
        exact hle)⟩)
      (by
        exact Continuous.subtype_mk continuous_subtype_val (by
          intro y
          exact (hup_iff y.1).1 (by
            have hy' : g y.1 ≤ c - data.ε := by
              change y.1 ∈ sublevel g (c - data.ε)
              exact y.2
            have hle : g y.1 ≤ c + data.ε := by linarith [data.hεpos]
            exact hle)))
  let hset : sublevel f (c - data.ε) ∪ U₀ = sublevel f (c - data.ε) ∪ E := by
    simp [E, U₀, hcell]
  let hcast : Z₀ ≃ₜ Z' := subtypeSetHomeo hset
  let hAdj : CellAdjunctionSpace k φ ≃ₜ Z' := by
    simpa [E, φ] using (cellAdjunctionSpaceHomeomorphLowerUnion (I := I) (hf := hf) (data := data))
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
  let toFun : C(SublevelSpace f (c + data.ε), CellAdjunctionSpace k φ) :=
    ContinuousMap.mk
      (fun y => hAdj.symm (hcast (hlow.toFun (flowRetract y))))
      (by
        exact (hAdj.symm.continuous_toFun.comp (hcast.continuous_toFun.comp
          (hlow.toFun.continuous.comp flowRetract.continuous))))
  let invFun : C(CellAdjunctionSpace k φ, SublevelSpace f (c + data.ε)) :=
    ContinuousMap.mk
      (fun z => intoUpper (hlow.invFun (hcast.symm (hAdj z))))
      (by
        exact (intoUpper.continuous.comp (hlow.invFun.continuous.comp
          (hcast.symm.continuous_toFun.comp hAdj.continuous_toFun))))
  let H₂ : ContinuousMap.HomotopyRel (intoUpper.comp flowRetract)
      (ContinuousMap.id (SublevelSpace f (c + data.ε))) (Set.range ι) := by
    have hGmem : ∀ p : (Set.Icc (0 : ℝ) 1) × SublevelSpace f (c + data.ε),
        f (curveAt v hcomplete p.2.1 (T p.2.1 * (1 - (p.1 : ℝ)))) ≤ c + data.ε := by
      intro p
      have ht : 0 ≤ T p.2.1 * (1 - (p.1 : ℝ)) := by
        exact mul_nonneg (hT_nonneg p.2.1) (sub_nonneg.mpr p.1.2.2)
      have hrb := f_rate_bounds_of_integralCurve g hg v hrate
        (hγ := curveAt_integralCurve v hcomplete p.2.1) (t := T p.2.1 * (1 - (p.1 : ℝ))) ht
      have hgz : g (curveAt v hcomplete p.2.1 (T p.2.1 * (1 - (p.1 : ℝ)))) ≤ g p.2.1 := by
        simpa [curveAt_zero v hcomplete p.2.1] using hrb.2
      have hgy : g p.2.1 ≤ c + data.ε := by
        exact le_trans (hg_le p.2.1) (by change f p.2.1 ≤ c + data.ε; exact p.2.2)
      exact (hup_iff _).1 (le_trans hgz hgy)
    let G : (Set.Icc (0 : ℝ) 1) × SublevelSpace f (c + data.ε) → SublevelSpace f (c + data.ε) :=
      fun p => ⟨curveAt v hcomplete p.2.1 (T p.2.1 * (1 - (p.1 : ℝ))), hGmem p⟩
    have hGcont : Continuous G := by
      have hpair : Continuous (fun p : (Set.Icc (0 : ℝ) 1) × SublevelSpace f (c + data.ε) =>
          (T p.2.1 * (1 - (p.1 : ℝ)), p.2.1)) := by
        fun_prop
      have hmain : Continuous (fun p : (Set.Icc (0 : ℝ) 1) × SublevelSpace f (c + data.ε) =>
          curveAt v hcomplete p.2.1 (T p.2.1 * (1 - (p.1 : ℝ)))) :=
        (continuous_globalFlow_of_compactSupport v hv hsupp).comp hpair
      exact Continuous.subtype_mk hmain (by intro p; exact hGmem p)
    refine { toHomotopy := { toFun := ContinuousMap.mk G hGcont, map_zero_left := ?_, map_one_left := ?_ }, prop' := ?_ }
    · intro y
      apply Subtype.ext
      change curveAt v hcomplete y.1 (T y.1 * (1 - (0 : ℝ))) = curveAt v hcomplete y.1 (T y.1)
      simp
    · intro y
      apply Subtype.ext
      change curveAt v hcomplete y.1 (T y.1 * (1 - (1 : ℝ))) = y.1
      simp [curveAt_zero v hcomplete y.1]
    · intro t x hx
      rcases hx with ⟨y, rfl⟩
      apply Subtype.ext
      have hT0 : T y.1 = 0 := hT_zero y.1 (by
        exact le_trans (hg_le y.1) (by change f y.1 ≤ c - data.ε; exact y.2))
      change curveAt v hcomplete y.1 (T y.1 * (1 - (t : ℝ))) = curveAt v hcomplete y.1 (T y.1)
      simp [hT0, curveAt_zero v hcomplete y.1]
  let H₁ : ContinuousMap.HomotopyRel
      ((intoUpper.comp (hlow.invFun.comp hlow.toFun)).comp flowRetract)
      (intoUpper.comp flowRetract) (Set.range ι) := by
    let P : (Set.Icc (0 : ℝ) 1) × SublevelSpace f (c + data.ε) → SublevelSpace f (c + data.ε) :=
      fun p => intoUpper (hlow.left_inv (p.1, flowRetract p.2))
    have hPcont : Continuous P := by
      have hpair : Continuous (fun p : (Set.Icc (0 : ℝ) 1) × SublevelSpace f (c + data.ε) =>
          (p.1, flowRetract p.2)) := by
        exact continuous_fst.prodMk (flowRetract.continuous.comp continuous_snd)
      exact intoUpper.continuous.comp (hlow.left_inv.toHomotopy.continuous.comp hpair)
    refine { toHomotopy := { toFun := ContinuousMap.mk P hPcont, map_zero_left := ?_, map_one_left := ?_ }, prop' := ?_ }
    · intro y
      change intoUpper (hlow.left_inv (0, flowRetract y)) =
        intoUpper ((hlow.invFun.comp hlow.toFun) (flowRetract y))
      exact congrArg intoUpper (hlow.left_inv.map_zero_left (flowRetract y))
    · intro y
      change intoUpper (hlow.left_inv (1, flowRetract y)) = intoUpper (flowRetract y)
      exact congrArg intoUpper (hlow.left_inv.map_one_left (flowRetract y))
    · intro t x hx
      rcases hx with ⟨y, rfl⟩
      change intoUpper (hlow.left_inv (t, flowRetract (ι y))) =
        intoUpper ((hlow.invFun.comp hlow.toFun) (flowRetract (ι y)))
      have hfr : flowRetract (ι y) = sublevelInclusionLE hg_le (c - data.ε) y := by
        apply Subtype.ext
        change curveAt v hcomplete y.1 (T y.1) = y.1
        rw [hT_zero y.1 (by
          exact le_trans (hg_le y.1) (by change f y.1 ≤ c - data.ε; exact y.2)),
          curveAt_zero v hcomplete y.1]
      have hz : flowRetract (ι y) ∈ Set.range (sublevelInclusionLE hg_le (c - data.ε)) := by
        rw [hfr]
        exact Set.mem_range.mpr ⟨y, rfl⟩
      exact congrArg intoUpper (hlow.left_inv.prop t (flowRetract (ι y)) hz)
  let L : ContinuousMap.HomotopyRel
      ((intoUpper.comp (hlow.invFun.comp hlow.toFun)).comp flowRetract)
      (ContinuousMap.id (SublevelSpace f (c + data.ε))) (Set.range ι) :=
    H₁.trans H₂
  have h₀ : invFun.comp toFun =
      ((intoUpper.comp (hlow.invFun.comp hlow.toFun)).comp flowRetract) := by
    ext y
    exact congrArg (fun w : SublevelSpace g (c - data.ε) => (w : M)) (congrArg hlow.invFun (by
      calc
        hcast.symm (hAdj (hAdj.symm (hcast (hlow.toFun (flowRetract y))))) =
            hcast.symm (hcast (hlow.toFun (flowRetract y))) := by
          exact congrArg hcast.symm (hAdj.right_inv (hcast (hlow.toFun (flowRetract y))))
        _ = hlow.toFun (flowRetract y) := hcast.left_inv (hlow.toFun (flowRetract y))))
  let H₃ : ContinuousMap.HomotopyRel (toFun.comp invFun)
      (ContinuousMap.id (CellAdjunctionSpace k φ)) (Set.range j) := by
    let Q : (Set.Icc (0 : ℝ) 1) × CellAdjunctionSpace k φ → CellAdjunctionSpace k φ :=
      fun p => hAdj.symm (hcast (hlow.right_inv (p.1, hcast.symm (hAdj p.2))))
    have hQcont : Continuous Q := by
      have hpair : Continuous (fun p : (Set.Icc (0 : ℝ) 1) × CellAdjunctionSpace k φ =>
          (p.1, hcast.symm (hAdj p.2))) := by
        exact continuous_fst.prodMk (hcast.symm.continuous_toFun.comp (hAdj.continuous_toFun.comp continuous_snd))
      exact (hAdj.symm.continuous_toFun.comp (hcast.continuous_toFun.comp
        (hlow.right_inv.toHomotopy.continuous.comp hpair)))
    refine { toHomotopy := { toFun := ContinuousMap.mk Q hQcont, map_zero_left := ?_, map_one_left := ?_ }, prop' := ?_ }
    · intro z
      change hAdj.symm (hcast (hlow.right_inv (0, hcast.symm (hAdj z)))) =
        hAdj.symm (hcast (hlow.toFun (flowRetract (intoUpper (hlow.invFun (hcast.symm (hAdj z)))))))
      have hflowfix : flowRetract (intoUpper (hlow.invFun (hcast.symm (hAdj z)))) =
          hlow.invFun (hcast.symm (hAdj z)) := by
        apply Subtype.ext
        dsimp [flowRetract, intoUpper]
        change curveAt v hcomplete ((hlow.invFun (hcast.symm (hAdj z))).1)
            (T ((hlow.invFun (hcast.symm (hAdj z))).1)) = (hlow.invFun (hcast.symm (hAdj z))).1
        rw [hT_zero ((hlow.invFun (hcast.symm (hAdj z))).1) (hunion_sub ((hlow.invFun (hcast.symm (hAdj z))).1) (by
          rw [hlow_invFun_val (hcast.symm (hAdj z))]
          exact (hcast.symm (hAdj z)).2)),
          curveAt_zero v hcomplete ((hlow.invFun (hcast.symm (hAdj z))).1)]
      calc
        hAdj.symm (hcast (hlow.right_inv (0, hcast.symm (hAdj z)))) =
            hAdj.symm (hcast ((hlow.toFun.comp hlow.invFun) (hcast.symm (hAdj z)))) := by
          exact congrArg (fun w => hAdj.symm (hcast w)) (hlow.right_inv.map_zero_left (hcast.symm (hAdj z)))
        _ = hAdj.symm (hcast (hlow.toFun (hlow.invFun (hcast.symm (hAdj z))))) := rfl
        _ = hAdj.symm (hcast (hlow.toFun (flowRetract
              (intoUpper (hlow.invFun (hcast.symm (hAdj z))))))) := by rw [hflowfix]
        _ = toFun (invFun z) := rfl
    · intro z
      change hAdj.symm (hcast (hlow.right_inv (1, hcast.symm (hAdj z)))) = z
      calc
        hAdj.symm (hcast (hlow.right_inv (1, hcast.symm (hAdj z)))) =
            hAdj.symm (hcast (hcast.symm (hAdj z))) := by
          exact congrArg (fun w => hAdj.symm (hcast w)) (hlow.right_inv.map_one_left (hcast.symm (hAdj z)))
        _ = hAdj.symm (hAdj z) := by
          exact congrArg hAdj.symm (hcast.right_inv (hAdj z))
        _ = z := hAdj.left_inv z
    · intro t z hz
      rcases hz with ⟨x, rfl⟩
      change hAdj.symm (hcast (hlow.right_inv (t, hcast.symm (hAdj (j x))))) =
        hAdj.symm (hcast (hlow.toFun (flowRetract (intoUpper (hlow.invFun (hcast.symm (hAdj (j x))))))))
      have hz₀ : hcast.symm (hAdj (j x)) = sublevelUnionInclusion (c - data.ε) U₀ x := by
        apply Subtype.ext
        change (hAdj (j x)).1 = x.1
        simpa [j] using congrArg Subtype.val (hAdjLower x)
      have hrel : hlow.right_inv (t, hcast.symm (hAdj (j x))) =
          (hlow.toFun.comp hlow.invFun) (hcast.symm (hAdj (j x))) := by
        have hmem : hcast.symm (hAdj (j x)) ∈ Set.range (sublevelUnionInclusion (c - data.ε) U₀) := by
          rw [hz₀]
          exact Set.mem_range.mpr ⟨x, rfl⟩
        exact hlow.right_inv.prop t (hcast.symm (hAdj (j x))) hmem
      have hflowfix : flowRetract (intoUpper (hlow.invFun (hcast.symm (hAdj (j x))))) =
          hlow.invFun (hcast.symm (hAdj (j x))) := by
        apply Subtype.ext
        dsimp [flowRetract, intoUpper]
        change curveAt v hcomplete ((hlow.invFun (hcast.symm (hAdj (j x)))).1)
            (T ((hlow.invFun (hcast.symm (hAdj (j x)))).1)) = (hlow.invFun (hcast.symm (hAdj (j x)))).1
        rw [hT_zero ((hlow.invFun (hcast.symm (hAdj (j x)))).1) (hunion_sub ((hlow.invFun (hcast.symm (hAdj (j x)))).1) (by
          rw [hlow_invFun_val (hcast.symm (hAdj (j x)))]
          exact (hcast.symm (hAdj (j x))).2)),
          curveAt_zero v hcomplete ((hlow.invFun (hcast.symm (hAdj (j x)))).1)]
      calc
        hAdj.symm (hcast (hlow.right_inv (t, hcast.symm (hAdj (j x))))) =
            hAdj.symm (hcast ((hlow.toFun.comp hlow.invFun) (hcast.symm (hAdj (j x))))) := by
          exact congrArg (fun w => hAdj.symm (hcast w)) hrel
        _ = hAdj.symm (hcast (hlow.toFun (hlow.invFun (hcast.symm (hAdj (j x)))))) := rfl
        _ = hAdj.symm (hcast (hlow.toFun (flowRetract
              (intoUpper (hlow.invFun (hcast.symm (hAdj (j x)))))))) := by rw [hflowfix]
        _ = toFun (invFun (j x)) := rfl
  exact
    { toFun := toFun
      invFun := invFun
      map_toBase := by
        ext x
        calc
          toFun (ι x) = hAdj.symm (hcast (hlow.toFun (flowRetract (ι x)))) := rfl
          _ = hAdj.symm (hcast (hlow.toFun (sublevelInclusionLE hg_le (c - data.ε) x))) := by
            exact congrArg (fun w => hAdj.symm (hcast (hlow.toFun w))) (by
              apply Subtype.ext
              dsimp [flowRetract, sublevelInclusionLE, ι]
              change curveAt v hcomplete x.1 (T x.1) = x.1
              rw [hT_zero x.1 (by
                exact le_trans (hg_le x.1) (by change f x.1 ≤ c - data.ε; exact x.2)),
                curveAt_zero v hcomplete x.1])
          _ = hAdj.symm (hcast (sublevelUnionInclusion (c - data.ε) U₀ x)) := by
            exact congrArg (fun w => hAdj.symm (hcast w)) (hlow.map_toBase_apply x)
          _ = hAdj.symm (⟨x.1, Or.inl x.2⟩ : Z') := by
            exact congrArg hAdj.symm (by
              apply Subtype.ext
              rfl)
          _ = j x := by
            have hh0 : hAdj.symm (⟨x.1, Or.inl x.2⟩ : Z') = j x := by
              have h := hAdj.left_inv (j x)
              rw [show hAdj.toFun (j x) = (⟨x.1, Or.inl x.2⟩ : Z') from by simpa [j] using hAdjLower x] at h
              exact h
            exact hh0
      map_fromBase := by
        ext x
        exact congrArg Subtype.val (by
          calc
            invFun (j x) = intoUpper (hlow.invFun (hcast.symm (hAdj (j x)))) := rfl
            _ = intoUpper (hlow.invFun (hcast.symm (⟨x.1, Or.inl x.2⟩ : Z'))) := by
              exact congrArg (fun w => intoUpper (hlow.invFun (hcast.symm w))) (hAdjLower x)
            _ = intoUpper (hlow.invFun (sublevelUnionInclusion (c - data.ε) U₀ x)) := by
              exact congrArg (fun w => intoUpper (hlow.invFun w)) (by
                apply Subtype.ext
                rfl)
            _ = intoUpper (sublevelInclusionLE hg_le (c - data.ε) x) := by
              exact congrArg intoUpper (hlow.map_fromBase_apply x)
            _ = ι x := by
              exact Subtype.ext (by rfl))
      left_inv := L.cast h₀.symm rfl
      right_inv := H₃ }
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
      Nonempty (HomotopyEquivUnder
        (X := SublevelSpace f (c - ε)) (Y := SublevelSpace f (c + ε))
        (Z := CellAdjunctionSpace k φ)
        (toBase := sublevelInclusion f (by linarith [hε]))
        (fromBase := ContinuousMap.mk (adjunctionLower (i := cellBoundaryInclusion k) φ)
          (continuous_adjunctionLower (i := cellBoundaryInclusion k) φ))) := by
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
  let hlow0 : HomotopyEquivUnder
      (X := SublevelSpace f (c - ε₀))
      (Y := SublevelSpace g (c - ε₀))
      (Z := {x : M // x ∈ sublevel f (c - ε₀) ∪ χ '' (Set.range (fun z : ClosedCell k =>
        cellMap (Real.sqrt (2 * ε₀)) (z : EuclideanSpace ℝ (Fin k))))})
      (toBase := sublevelInclusionLE hg_le (c - ε₀))
      (fromBase := sublevelUnionInclusion (c - ε₀) (χ '' (Set.range (fun z : ClosedCell k =>
        cellMap (Real.sqrt (2 * ε₀)) (z : EuclideanSpace ℝ (Fin k)))))) :=
    morseModifiedLowerSublevelHomotopyEquivUnder (H := H) (M := M) hk c ε₀ δ₀ R hε₀ hδ₀ hR' hRpos hεR
      χ f hg hnorm hχsrc
  have hcell : cellImage hk c data = χ '' (Set.range (fun z : ClosedCell k =>
      cellMap (Real.sqrt (2 * ε₀)) (z : EuclideanSpace ℝ (Fin k)))) := by
    change Set.range (fun z : ClosedCell k =>
        χ (cellMap (Real.sqrt (2 * ε₀)) (z : EuclideanSpace ℝ (Fin k)))) =
      χ '' (Set.range (fun z : ClosedCell k =>
        cellMap (Real.sqrt (2 * ε₀)) (z : EuclideanSpace ℝ (Fin k))))
    exact Set.range_comp (g := fun y : MorseModel n => χ y)
      (f := fun z : ClosedCell k => cellMap (Real.sqrt (2 * ε₀)) (z : EuclideanSpace ℝ (Fin k)))
  have hunion_sub : ∀ x : M, x ∈ sublevel f (c - ε₀) ∪ χ '' (Set.range (fun z : ClosedCell k =>
      cellMap (Real.sqrt (2 * ε₀)) (z : EuclideanSpace ℝ (Fin k)))) → g x ≤ c - ε₀ := by
    intro x hx
    change g x ≤ c - ε₀
    dsimp [g]
    exact lowerUnionCellImage_subset_modifiedSublevel (H := H) (M := M) hk c ε₀ δ₀ R hε₀ hδ₀ hεR
      χ f hnorm hχsrc hx
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
    ⟨v, _Φ, hv, hsupp, hdfOn, hrate, _htransport⟩
  have hlow_inv_val : ∀ z : {x : M // x ∈ sublevel f (c - ε₀) ∪ χ '' (Set.range (fun z : ClosedCell k =>
      cellMap (Real.sqrt (2 * ε₀)) (z : EuclideanSpace ℝ (Fin k))))}, (hlow0.invFun z).1 = z.1 := by
    intro z
    rfl
  refine ⟨ε₀, hε₀, hεa, cellAttachingMap hk c data, ⟨?_⟩⟩
  exact sublevelCellAdjunctionHomotopyEquivUnderOfMorseChart (I := I) (hf := hf)
    (f := f) (c := c) (k := k) (hk := hk) (data := data) (g := g) hgmd hg_le hlow0 hcell hunion_sub
    hlow_inv_val hgup v hv hsupp hdfOn hrate
end ManifoldCellAttachment

end
end DifferentialGeometry.Topology.Morse
