import DifferentialGeometry.Topology.Morse.CellAttachment
import DifferentialGeometry.Topology.Morse.Flow
import DifferentialGeometry.Topology.Morse.Manifold
import DifferentialGeometry.Topology.Morse.ModifiedFunction
import Mathlib.Topology.MetricSpace.Bounded

namespace DifferentialGeometry.Topology.Morse

open Manifold
open scoped Topology Manifold

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


private theorem exists_morseChart {n : ℕ} {H : Type} [TopologicalSpace H] {M : Type}
    [TopologicalSpace M] [ChartedSpace H M] (I : ModelWithCorners ℝ (MorseModel n) H) [I.Boundaryless]
    [IsManifold I (⊤ : WithTop ℕ∞) M] (f : M → ℝ) (hf : ContMDiff I 𝓘(ℝ, ℝ) (⊤ : WithTop ℕ∞) f)
    (p : M) (c : ℝ) (k : ℕ) (hk : k ≤ n)
    (hcrit : fderiv ℝ (fun y => f ((extChartAt I p).symm y)) (extChartAt I p p) = 0)
    (hnd : (QuadraticMap.associated (R := ℝ)
      (chartHessianAt (g := fun y => f ((extChartAt I p).symm y)) (extChartAt I p p))).SeparatingLeft)
    (hindex : sigNeg (chartHessianAt (g := fun y => f ((extChartAt I p).symm y)) (extChartAt I p p)) = k)
    (hfp : f p = c) :
    ∃ R : ℝ, 0 < R ∧
    ∃ χ : OpenPartialHomeomorph (MorseModel n) M,
      (∀ y : MorseModel n, morseNorm n y ≤ R → f (χ y) = morseNormalForm hk c y) ∧
      (∀ y : MorseModel n, morseNorm n y ≤ R → y ∈ χ.source) := by
  have hcrit' : IsCriticalPointAt I f p :=
    (isCriticalPointAt_iff_chart_fderiv I f
      (hf.of_le (le_top : (↑(⊤ : ℕ∞) : WithTop ℕ∞) ≤ (⊤ : WithTop ℕ∞))) p).2 hcrit
  have hnd' : IsNondegenerateCriticalPointAt I f p := ⟨hcrit', hnd⟩
  rcases morse_lemma I f hf p k hk hcrit' hnd' hindex with
    ⟨R, hRpos, χ, _, _, _, hχsrc, hnorm, _, _⟩
  refine ⟨R, hRpos, χ, ?_, ?_⟩
  · intro y hy
    rw [← hfp]
    exact hnorm y hy
  · exact hχsrc

private theorem chartBallHomeo_eval {n : ℕ} {M : Type} [TopologicalSpace M]
    (χ : OpenPartialHomeomorph (MorseModel n) M) (R : ℝ)
    (hχsrc : ∀ y : MorseModel n, morseNorm n y ≤ R → y ∈ χ.source) :
    ∃ he : {y : MorseModel n // morseNorm n y ≤ R} ≃ₜ
        {x : M // x ∈ χ '' {y : MorseModel n | morseNorm n y ≤ R}},
      ∀ y : {y : MorseModel n // morseNorm n y ≤ R}, (he y : M) = χ y.1 := by
  let ball : Set (MorseModel n) := {y : MorseModel n | morseNorm n y ≤ R}
  let U : Set M := χ '' ball
  let hχ : χ.source ≃ₜ χ.target := openPartialHomeomorphSourceHomeo χ
  have himg : χ '' ball ⊆ χ.target := by
    intro x hx
    rcases hx with ⟨y, hy, hxy⟩
    rw [← hxy]
    exact χ.map_source (hχsrc y hy)
  let he : {y : MorseModel n // morseNorm n y ≤ R} ≃ₜ {x : M // x ∈ U} :=
    { toFun := fun y => ⟨χ y.1, ⟨y.1, y.2, rfl⟩⟩
      invFun := fun x => ⟨χ.symm x.1, by
        rcases x.2 with ⟨y, hy, hxy⟩
        have hyin : y ∈ χ.source := hχsrc y hy
        have hround : χ.symm x.1 = y := by
          rw [← hxy]
          exact χ.left_inv hyin
        rw [hround]
        exact hy⟩
      left_inv := by
        intro y
        apply Subtype.ext
        exact χ.left_inv (hχsrc y.1 y.2)
      right_inv := by
        intro x
        apply Subtype.ext
        exact χ.right_inv (himg x.2)
      continuous_toFun := by
        have h1 : Continuous (fun y : {y : MorseModel n // y ∈ χ.source} => χ y.1) :=
          continuousOn_iff_continuous_restrict.mp χ.continuousOn_toFun
        have h2 : Continuous (fun y : {y : MorseModel n // morseNorm n y ≤ R} =>
            (⟨y.1, hχsrc y.1 y.2⟩ : {y : MorseModel n // y ∈ χ.source})) := by
          exact (Topology.IsInducing.subtypeVal.continuous_iff).2 continuous_subtype_val
        exact (Topology.IsInducing.subtypeVal.continuous_iff).2 (h1.comp h2)
      continuous_invFun := by
        have h1 : Continuous (fun x : {x : M // x ∈ χ.target} => χ.symm x.1) :=
          continuousOn_iff_continuous_restrict.mp χ.continuousOn_invFun
        have h2 : Continuous (fun x : {x : M // x ∈ U} =>
            (⟨x.1, himg x.2⟩ : {x : M // x ∈ χ.target})) := by
          exact (Topology.IsInducing.subtypeVal.continuous_iff).2 continuous_subtype_val
        exact (Topology.IsInducing.subtypeVal.continuous_iff).2 (h1.comp h2) }
  have heval : ∀ y : {y : MorseModel n // morseNorm n y ≤ R}, (he y : M) = χ y.1 := by
    intro y
    simp [he]
  exact ⟨he, heval⟩

theorem morseCellAttachment {n : ℕ} {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M]
    [ChartedSpace H M] (I : ModelWithCorners ℝ (MorseModel n) H) [I.Boundaryless]
    [IsManifold I (⊤ : WithTop ℕ∞) M] (f : M → ℝ) (hf : ContMDiff I 𝓘(ℝ, ℝ) (⊤ : WithTop ℕ∞) f)
    (p : M) (c : ℝ) (k : ℕ) (hk : k ≤ n)
    (hcrit : fderiv ℝ (fun y => f ((extChartAt I p).symm y)) (extChartAt I p p) = 0)
    (hnd : (QuadraticMap.associated (R := ℝ)
      (chartHessianAt (g := fun y => f ((extChartAt I p).symm y)) (extChartAt I p p))).SeparatingLeft)
    (hindex : sigNeg (chartHessianAt (g := fun y => f ((extChartAt I p).symm y)) (extChartAt I p p)) = k)
    (hfp : f p = c) :
    ∃ R : ℝ, 0 < R ∧
    ∃ χ : OpenPartialHomeomorph (MorseModel n) M,
      (∀ y : MorseModel n, morseNorm n y ≤ R → f (χ y) = morseNormalForm hk c y) ∧
      (∀ y : MorseModel n, morseNorm n y ≤ R → y ∈ χ.source) ∧
      ∃ ε : ℝ, 0 < ε ∧ Real.sqrt (2 * ε) ≤ R ∧
        ∃ φ : CellBoundary k →
            {x : {x : M // x ∈ χ '' {y : MorseModel n | morseNorm n y ≤ R}} //
              x.1 ∈ sublevel f (c - ε)},
          Nonempty (ContinuousMap.HomotopyEquiv
            {x : M // x ∈ χ '' {y : MorseModel n | morseNorm n y ≤ R} ∧ x ∈ sublevel f (c + ε)}
            (CellAdjunctionSpace k φ)) := by
  rcases exists_morseChart I f hf p c k hk hcrit hnd hindex hfp with ⟨R, hRpos, χ, hnorm, hχsrc⟩
  let ε : ℝ := R ^ 2 / 4
  have hεpos : 0 < ε := by dsimp [ε]; positivity
  have hεR : Real.sqrt (2 * ε) ≤ R := by
    dsimp [ε]
    have hRnonneg : 0 ≤ R := le_of_lt hRpos
    have hsq : (Real.sqrt (2 * (R ^ 2 / 4))) ^ 2 ≤ R ^ 2 := by
      rw [Real.sq_sqrt (by nlinarith [sq_nonneg R])]
      ring_nf
      nlinarith [sq_nonneg R]
    have habs := sq_le_sq.mp hsq
    calc
      Real.sqrt (2 * (R ^ 2 / 4)) = |Real.sqrt (2 * (R ^ 2 / 4))| :=
        (abs_of_nonneg (Real.sqrt_nonneg _)).symm
      _ ≤ |R| := habs
      _ = R := abs_of_nonneg hRnonneg
  let he : {y : MorseModel n // morseNorm n y ≤ R} ≃ₜ
      {x : M // x ∈ χ '' {y : MorseModel n | morseNorm n y ≤ R}} :=
    Classical.choose (chartBallHomeo_eval (M := M) χ R hχsrc)
  have heval : ∀ y : {y : MorseModel n // morseNorm n y ≤ R}, (he y : M) = χ y.1 :=
    Classical.choose_spec (chartBallHomeo_eval (M := M) χ R hχsrc)
  let ball : Set (MorseModel n) := {y : MorseModel n | morseNorm n y ≤ R}
  let U : Set M := χ '' ball
  refine ⟨R, hRpos, χ, hnorm, hχsrc, ε, hεpos, hεR, ?_⟩
  have hpLower : ∀ y : {y : MorseModel n // morseNorm n y ≤ R},
      y.1 ∈ sublevel (morseNormalForm hk c) (c - ε) ↔ (he y : M) ∈ sublevel f (c - ε) := by
    intro y
    have hval : f (he y : M) = morseNormalForm hk c y.1 := by
      rw [heval y]
      exact hnorm y.1 y.2
    constructor
    · intro hy
      change f (he y : M) ≤ c - ε
      rw [hval]
      exact hy
    · intro hy
      change morseNormalForm hk c y.1 ≤ c - ε
      rw [← hval]
      exact hy
  let hLower : {y : MorseModel n // y ∈ sublevel (morseNormalForm hk c) (c - ε) ∧ morseNorm n y ≤ R} ≃ₜ
      {x : {x : M // x ∈ U} // x.1 ∈ sublevel f (c - ε)} :=
    (andSwapHomeo (fun y : MorseModel n => y ∈ sublevel (morseNormalForm hk c) (c - ε))
      (fun y : MorseModel n => morseNorm n y ≤ R)).trans
      ((subtypeAndNestedHomeo (fun y : MorseModel n => morseNorm n y ≤ R)
        (fun y : MorseModel n => y ∈ sublevel (morseNormalForm hk c) (c - ε))).trans
      (homeoRestrictPred he (fun y => y.1 ∈ sublevel (morseNormalForm hk c) (c - ε))
        (fun x => x.1 ∈ sublevel f (c - ε)) hpLower))
  let φB : CellBoundary k →
      {y : MorseModel n // y ∈ sublevel (morseNormalForm hk c) (c - ε) ∧ morseNorm n y ≤ R} :=
    ballAttachMap hk c ε R (le_of_lt hεpos) hεR
  let φ : CellBoundary k → {x : {x : M // x ∈ U} // x.1 ∈ sublevel f (c - ε)} := hLower ∘ φB
  have hUpper : {x : M // x ∈ U ∧ x ∈ sublevel f (c + ε)} ≃ₜ ballUpperSublevel hk c ε R := by
    have hpUpper : ∀ y : {y : MorseModel n // morseNorm n y ≤ R},
        y.1 ∈ sublevel (morseNormalForm hk c) (c + ε) ↔ (he y : M) ∈ sublevel f (c + ε) := by
      intro y
      have hval : f (he y : M) = morseNormalForm hk c y.1 := by
        rw [heval y]
        exact hnorm y.1 y.2
      constructor
      · intro hy
        change f (he y : M) ≤ c + ε
        rw [hval]
        exact hy
      · intro hy
        change morseNormalForm hk c y.1 ≤ c + ε
        rw [← hval]
        exact hy
    have hU' : {y : {y : MorseModel n // morseNorm n y ≤ R} // y.1 ∈ sublevel (morseNormalForm hk c) (c + ε)} ≃ₜ
        {x : {x : M // x ∈ U} // x.1 ∈ sublevel f (c + ε)} :=
      homeoRestrictPred he (fun y => y.1 ∈ sublevel (morseNormalForm hk c) (c + ε))
        (fun x => x.1 ∈ sublevel f (c + ε)) hpUpper
    have hcast : {y : {y : MorseModel n // morseNorm n y ≤ R} //
        y.1 ∈ sublevel (morseNormalForm hk c) (c + ε)} ≃ₜ ballUpperSublevel hk c ε R :=
      ((andSwapHomeo (fun y : MorseModel n => y ∈ sublevel (morseNormalForm hk c) (c + ε))
        (fun y : MorseModel n => morseNorm n y ≤ R)).trans
        (subtypeAndNestedHomeo (fun y : MorseModel n => morseNorm n y ≤ R)
          (fun y : MorseModel n => y ∈ sublevel (morseNormalForm hk c) (c + ε)))).symm
    exact (subtypeAndNestedHomeo (fun x : M => x ∈ U) (fun x : M => x ∈ sublevel f (c + ε))).trans
      (hU'.symm.trans hcast)
  have hAdj : CellAdjunctionSpace k φB ≃ₜ CellAdjunctionSpace k φ :=
    (adjunctionHomeoOfLowerEquiv (cellBoundaryInclusion k) φB hLower).symm
  exact ⟨φ, ⟨(hUpper.toHomotopyEquiv.trans
    (ballCellAttachmentModel hk c ε R hεpos hεR)).trans hAdj.toHomotopyEquiv⟩⟩

structure MorseChartData (n k : ℕ) (hk : k ≤ n) (c : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    (I : ModelWithCorners ℝ (MorseModel n) H) (f : M → ℝ) where
  R : ℝ
  ε : ℝ
  χ : OpenPartialHomeomorph (MorseModel n) M
  hRpos : 0 < R
  hεpos : 0 < ε
  hεR : Real.sqrt (2 * ε) ≤ R
  hnorm : ∀ y : MorseModel n, morseNorm n y ≤ R → f (χ y) = morseNormalForm hk c y
  hχsrc : ∀ y : MorseModel n, morseNorm n y ≤ R → y ∈ χ.source

noncomputable def morseChartData {n : ℕ} {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M]
    [ChartedSpace H M] (I : ModelWithCorners ℝ (MorseModel n) H) [I.Boundaryless]
    [IsManifold I (⊤ : WithTop ℕ∞) M] (f : M → ℝ) (hf : ContMDiff I 𝓘(ℝ, ℝ) (⊤ : WithTop ℕ∞) f)
    (p : M) (c : ℝ) (k : ℕ) (hk : k ≤ n)
    (hcrit : fderiv ℝ (fun y => f ((extChartAt I p).symm y)) (extChartAt I p p) = 0)
    (hnd : (QuadraticMap.associated (R := ℝ)
      (chartHessianAt (g := fun y => f ((extChartAt I p).symm y)) (extChartAt I p p))).SeparatingLeft)
    (hindex : sigNeg (chartHessianAt (g := fun y => f ((extChartAt I p).symm y)) (extChartAt I p p)) = k)
    (hfp : f p = c) : MorseChartData n k hk c I f := by
  let hdata := exists_morseChart I f hf p c k hk hcrit hnd hindex hfp
  let R : ℝ := Classical.choose hdata
  have hR : 0 < R ∧ ∃ χ : OpenPartialHomeomorph (MorseModel n) M,
      (∀ y : MorseModel n, morseNorm n y ≤ R → f (χ y) = morseNormalForm hk c y) ∧
      (∀ y : MorseModel n, morseNorm n y ≤ R → y ∈ χ.source) := Classical.choose_spec hdata
  rcases hR with ⟨hRpos, hχ⟩
  let χ : OpenPartialHomeomorph (MorseModel n) M := Classical.choose hχ
  have hχspec : (∀ y : MorseModel n, morseNorm n y ≤ R → f (χ y) = morseNormalForm hk c y) ∧
      (∀ y : MorseModel n, morseNorm n y ≤ R → y ∈ χ.source) := Classical.choose_spec hχ
  rcases hχspec with ⟨hnorm, hχsrc⟩
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
  exact MorseChartData.mk R ε χ hRpos hεpos hεR hnorm hχsrc

def cellEmbedding {n k : ℕ} (hk : k ≤ n) (c : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ (MorseModel n) H} {f : M → ℝ}
    (data : MorseChartData n k hk c I f) : ClosedCell k → M :=
  fun x => data.χ (cellMap hk (Real.sqrt (2 * data.ε)) (x : EuclideanSpace ℝ (Fin k)))

def cellImage {n k : ℕ} (hk : k ≤ n) (c : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ (MorseModel n) H} {f : M → ℝ}
    (data : MorseChartData n k hk c I f) : Set M :=
  Set.range (cellEmbedding hk c data)

def cellAttachingMap {n k : ℕ} (hk : k ≤ n) (c : ℝ)
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ (MorseModel n) H} {f : M → ℝ}
    (data : MorseChartData n k hk c I f) :
    CellBoundary k → {x : M // x ∈ sublevel f (c - data.ε)} :=
  fun b => ⟨data.χ (cellMap hk (Real.sqrt (2 * data.ε)) (b : EuclideanSpace ℝ (Fin k))), by
    change f (data.χ (cellMap hk (Real.sqrt (2 * data.ε)) (b : EuclideanSpace ℝ (Fin k)))) ≤ c - data.ε
    have hn := data.hnorm (cellMap hk (Real.sqrt (2 * data.ε)) (b : EuclideanSpace ℝ (Fin k))) (by
      exact norm_cellMap_le hk data.ε data.R data.hεR (b : EuclideanSpace ℝ (Fin k)) (le_of_eq b.2))
    rw [hn]
    have hf := morseNormalForm_cellMap hk c (Real.sqrt (2 * data.ε)) (b : EuclideanSpace ℝ (Fin k))
    rw [hf]
    have hnorm1 : ‖(b : EuclideanSpace ℝ (Fin k))‖ = 1 := b.2
    have hsq : (Real.sqrt (2 * data.ε)) ^ 2 = 2 * data.ε := by
      rw [Real.sq_sqrt (by exact mul_nonneg (by norm_num) (le_of_lt data.hεpos))]
    rw [hsq, hnorm1]
    linarith⟩

theorem sublevel_cellAdjunction_homotopyEquiv_of_morseChart_and_flow {n : ℕ} {H : Type}
    [TopologicalSpace H] {M : Type} [TopologicalSpace M]
    [ChartedSpace H M] [T2Space M] (I : ModelWithCorners ℝ (MorseModel n) H) [I.Boundaryless]
    [IsManifold I (⊤ : WithTop ℕ∞) M] (f : M → ℝ) (hf : ContMDiff I 𝓘(ℝ, ℝ) (⊤ : WithTop ℕ∞) f)
    (c : ℝ) (k : ℕ) (hk : k ≤ n)
    (data : MorseChartData n k hk c I f)
    (g : M → ℝ)
    (hlow : Nonempty (ContinuousMap.HomotopyEquiv (SublevelSpace g (c - data.ε))
      {x : M // x ∈ sublevel f (c - data.ε) ∪ cellImage hk c data}))
    (hgup : {x : M | g x ≤ c + data.ε} = sublevel f (c + data.ε))
    (Φ : GradientLikeFlow I g (c - data.ε) (c + data.ε)) :
    Nonempty (ContinuousMap.HomotopyEquiv (SublevelSpace f (c + data.ε))
      (CellAdjunctionSpace k (cellAttachingMap hk c data))) := by
  let E : Set M := cellImage hk c data
  let c' : ClosedCell k → M := cellEmbedding hk c data
  let φ : CellBoundary k → {x : M // x ∈ sublevel f (c - data.ε)} := cellAttachingMap hk c data
  have hAdj : CellAdjunctionSpace k φ ≃ₜ {x : M // x ∈ sublevel f (c - data.ε) ∪ Set.range c'} := by
    refine cellAdjunctionHomeomorphUnionImage (n := k) (φ := φ) (c := c') ?hφ ?hc ?hcont ?hinterior ?hclosed
    · intro b
      rfl
    · intro x y hxy
      have hx : cellMap hk (Real.sqrt (2 * data.ε)) (x : EuclideanSpace ℝ (Fin k)) ∈
          {y : MorseModel n | morseNorm n y ≤ data.R} := by
        exact norm_cellMap_le hk data.ε data.R data.hεR (x : EuclideanSpace ℝ (Fin k)) x.2
      have hy : cellMap hk (Real.sqrt (2 * data.ε)) (y : EuclideanSpace ℝ (Fin k)) ∈
          {y : MorseModel n | morseNorm n y ≤ data.R} := by
        exact norm_cellMap_le hk data.ε data.R data.hεR (y : EuclideanSpace ℝ (Fin k)) y.2
      have hχ : cellMap hk (Real.sqrt (2 * data.ε)) (x : EuclideanSpace ℝ (Fin k)) =
          cellMap hk (Real.sqrt (2 * data.ε)) (y : EuclideanSpace ℝ (Fin k)) := by
        exact data.χ.injOn (data.hχsrc _ hx) (data.hχsrc _ hy) (by
          simpa [c', cellEmbedding] using hxy)
      exact cellMap_injective hk data.ε data.hεpos hχ
    · have hc'cont : Continuous (fun x : ClosedCell k =>
          cellMap hk (Real.sqrt (2 * data.ε)) (x : EuclideanSpace ℝ (Fin k))) :=
        continuous_cellMap hk (Real.sqrt (2 * data.ε))
      have hmap : Set.MapsTo (fun x : ClosedCell k =>
          cellMap hk (Real.sqrt (2 * data.ε)) (x : EuclideanSpace ℝ (Fin k))) Set.univ data.χ.source := by
        intro x hx
        exact data.hχsrc (cellMap hk (Real.sqrt (2 * data.ε)) (x : EuclideanSpace ℝ (Fin k)))
          (norm_cellMap_le hk data.ε data.R data.hεR (x : EuclideanSpace ℝ (Fin k)) x.2)
      have hcont : ContinuousOn (fun x : ClosedCell k =>
          data.χ (cellMap hk (Real.sqrt (2 * data.ε)) (x : EuclideanSpace ℝ (Fin k)))) Set.univ :=
        data.χ.continuousOn_toFun.comp hc'cont.continuousOn hmap
      change Continuous (fun x : ClosedCell k =>
        data.χ (cellMap hk (Real.sqrt (2 * data.ε)) (x : EuclideanSpace ℝ (Fin k))))
      exact (continuousOn_univ.mp hcont)
    · rw [Set.disjoint_left]
      intro x hxA hxB
      rcases hxA with ⟨y, hy, hxy⟩
      rcases hy with ⟨z, hz⟩
      have hfz : f x ≤ c - data.ε := by simpa [sublevel] using hxB
      have hxeq : x = data.χ (cellMap hk (Real.sqrt (2 * data.ε)) (z : EuclideanSpace ℝ (Fin k))) := by
        rw [← hxy]
        have hzval : (y : EuclideanSpace ℝ (Fin k)) = (z : EuclideanSpace ℝ (Fin k)) := by
          simpa [cellInteriorInclusion] using
            (congrArg (fun w : ClosedCell k => (w : EuclideanSpace ℝ (Fin k))) hz).symm
        dsimp [c', cellEmbedding]
        simp [hzval]
      have hfz' : f x = morseNormalForm hk c (cellMap hk (Real.sqrt (2 * data.ε)) (z : EuclideanSpace ℝ (Fin k))) := by
        rw [hxeq]
        rw [data.hnorm (cellMap hk (Real.sqrt (2 * data.ε)) (z : EuclideanSpace ℝ (Fin k))) (by
          exact norm_cellMap_le hk data.ε data.R data.hεR (z : EuclideanSpace ℝ (Fin k)) (le_of_lt z.2))]
      have hnot : ¬ morseNormalForm hk c (cellMap hk (Real.sqrt (2 * data.ε)) (z : EuclideanSpace ℝ (Fin k))) ≤
          c - data.ε := by
        intro hn
        have hmem : cellMap hk (Real.sqrt (2 * data.ε)) (z : EuclideanSpace ℝ (Fin k)) ∈
            (fun x : ClosedCell k => cellMap hk (Real.sqrt (2 * data.ε)) (x : EuclideanSpace ℝ (Fin k))) ''
              Set.range (cellInteriorInclusion k) := by
          refine ⟨cellInteriorInclusion k z, ?_, rfl⟩
          exact Set.mem_range.mpr ⟨z, rfl⟩
        exact (Set.disjoint_left.mp (cellInterior_disjoint hk c data.ε data.hεpos)) hmem hn
      exact hnot (by rw [← hfz']; exact hfz)
    · exact isClosed_Iic.preimage hf.continuous
  have hflow : (Φ.toDiffeomorph (c - data.ε - (c + data.ε))) ''
        sublevel g (c - data.ε) = sublevel g (c + data.ε) :=
    GradientLikeFlow.toDiffeomorph_image_sublevels Φ (by linarith [data.hεpos])
  let d : M ≃ₜ M := (Φ.toDiffeomorph (c - data.ε - (c + data.ε))).toHomeomorph
  let s : Set M := sublevel g (c - data.ε)
  have hflow' : (Φ.toDiffeomorph (c - data.ε - (c + data.ε))) '' sublevel g (c - data.ε) =
      sublevel f (c + data.ε) := by
    change ((Φ.toDiffeomorph (c - data.ε - (c + data.ε))) '' {x : M | g x ≤ c - data.ε}) =
        {x : M | g x ≤ c + data.ε} at hflow
    rw [hgup] at hflow
    exact hflow
  have hflowHomeo : SublevelSpace g (c - data.ε) ≃ₜ SublevelSpace f (c + data.ε) := by
    have himg : d '' s = sublevel f (c + data.ε) := by
      simpa [d, s] using hflow'
    exact (Homeomorph.image d s).trans (subtypeSetHomeo himg)
  have hlowE : ContinuousMap.HomotopyEquiv (SublevelSpace g (c - data.ε))
      {x : M // x ∈ sublevel f (c - data.ε) ∪ Set.range c'} := Classical.choice hlow
  have hAdjE : ContinuousMap.HomotopyEquiv
      {x : M // x ∈ sublevel f (c - data.ε) ∪ Set.range c'}
      (CellAdjunctionSpace k φ) := hAdj.symm.toHomotopyEquiv
  exact ⟨(hlowE.symm.trans hflowHomeo.toHomotopyEquiv).symm.trans hAdjE⟩

theorem cellAdjunctionSpace_homeomorph_lowerUnion {n : ℕ} {H : Type}
    [TopologicalSpace H] {M : Type} [TopologicalSpace M]
    [ChartedSpace H M] [T2Space M] (I : ModelWithCorners ℝ (MorseModel n) H) [I.Boundaryless]
    [IsManifold I (⊤ : WithTop ℕ∞) M] (f : M → ℝ) (hf : ContMDiff I 𝓘(ℝ, ℝ) (⊤ : WithTop ℕ∞) f)
    (c : ℝ) (k : ℕ) (hk : k ≤ n)
    (data : MorseChartData n k hk c I f) :
    Nonempty (CellAdjunctionSpace k (cellAttachingMap hk c data) ≃ₜ
      {x : M // x ∈ sublevel f (c - data.ε) ∪ cellImage hk c data}) := by
  let E : Set M := cellImage hk c data
  let c' : ClosedCell k → M := cellEmbedding hk c data
  let φ : CellBoundary k → {x : M // x ∈ sublevel f (c - data.ε)} := cellAttachingMap hk c data
  have hAdj : CellAdjunctionSpace k φ ≃ₜ
      {x : M // x ∈ sublevel f (c - data.ε) ∪ Set.range c'} := by
    refine cellAdjunctionHomeomorphUnionImage (n := k) (φ := φ) (c := c') ?hφ ?hc ?hcont ?hinterior ?hclosed
    · intro b
      rfl
    · intro x y hxy
      have hx : cellMap hk (Real.sqrt (2 * data.ε)) (x : EuclideanSpace ℝ (Fin k)) ∈
          {y : MorseModel n | morseNorm n y ≤ data.R} := by
        exact norm_cellMap_le hk data.ε data.R data.hεR (x : EuclideanSpace ℝ (Fin k)) x.2
      have hy : cellMap hk (Real.sqrt (2 * data.ε)) (y : EuclideanSpace ℝ (Fin k)) ∈
          {y : MorseModel n | morseNorm n y ≤ data.R} := by
        exact norm_cellMap_le hk data.ε data.R data.hεR (y : EuclideanSpace ℝ (Fin k)) y.2
      have hχ : cellMap hk (Real.sqrt (2 * data.ε)) (x : EuclideanSpace ℝ (Fin k)) =
          cellMap hk (Real.sqrt (2 * data.ε)) (y : EuclideanSpace ℝ (Fin k)) := by
        exact data.χ.injOn (data.hχsrc _ hx) (data.hχsrc _ hy) (by
          simpa [c', cellEmbedding] using hxy)
      exact cellMap_injective hk data.ε data.hεpos hχ
    · have hc'cont : Continuous (fun x : ClosedCell k =>
          cellMap hk (Real.sqrt (2 * data.ε)) (x : EuclideanSpace ℝ (Fin k))) :=
        continuous_cellMap hk (Real.sqrt (2 * data.ε))
      have hmap : Set.MapsTo (fun x : ClosedCell k =>
          cellMap hk (Real.sqrt (2 * data.ε)) (x : EuclideanSpace ℝ (Fin k))) Set.univ data.χ.source := by
        intro x hx
        exact data.hχsrc (cellMap hk (Real.sqrt (2 * data.ε)) (x : EuclideanSpace ℝ (Fin k)))
          (norm_cellMap_le hk data.ε data.R data.hεR (x : EuclideanSpace ℝ (Fin k)) x.2)
      have hcont : ContinuousOn (fun x : ClosedCell k =>
          data.χ (cellMap hk (Real.sqrt (2 * data.ε)) (x : EuclideanSpace ℝ (Fin k)))) Set.univ :=
        data.χ.continuousOn_toFun.comp hc'cont.continuousOn hmap
      change Continuous (fun x : ClosedCell k =>
        data.χ (cellMap hk (Real.sqrt (2 * data.ε)) (x : EuclideanSpace ℝ (Fin k))))
      exact (continuousOn_univ.mp hcont)
    · rw [Set.disjoint_left]
      intro x hxA hxB
      rcases hxA with ⟨y, hy, hxy⟩
      rcases hy with ⟨z, hz⟩
      have hfz : f x ≤ c - data.ε := by simpa [sublevel] using hxB
      have hxeq : x = data.χ (cellMap hk (Real.sqrt (2 * data.ε)) (z : EuclideanSpace ℝ (Fin k))) := by
        rw [← hxy]
        have hzval : (y : EuclideanSpace ℝ (Fin k)) = (z : EuclideanSpace ℝ (Fin k)) := by
          simpa [cellInteriorInclusion] using
            (congrArg (fun w : ClosedCell k => (w : EuclideanSpace ℝ (Fin k))) hz).symm
        dsimp [c', cellEmbedding]
        simp [hzval]
      have hfz' : f x = morseNormalForm hk c (cellMap hk (Real.sqrt (2 * data.ε)) (z : EuclideanSpace ℝ (Fin k))) := by
        rw [hxeq]
        rw [data.hnorm (cellMap hk (Real.sqrt (2 * data.ε)) (z : EuclideanSpace ℝ (Fin k))) (by
          exact norm_cellMap_le hk data.ε data.R data.hεR (z : EuclideanSpace ℝ (Fin k)) (le_of_lt z.2))]
      have hnot : ¬ morseNormalForm hk c (cellMap hk (Real.sqrt (2 * data.ε)) (z : EuclideanSpace ℝ (Fin k))) ≤
          c - data.ε := by
        intro hn
        have hmem : cellMap hk (Real.sqrt (2 * data.ε)) (z : EuclideanSpace ℝ (Fin k)) ∈
            (fun x : ClosedCell k => cellMap hk (Real.sqrt (2 * data.ε)) (x : EuclideanSpace ℝ (Fin k))) ''
              Set.range (cellInteriorInclusion k) := by
          refine ⟨cellInteriorInclusion k z, ?_, rfl⟩
          exact Set.mem_range.mpr ⟨z, rfl⟩
        exact (Set.disjoint_left.mp (cellInterior_disjoint hk c data.ε data.hεpos)) hmem hn
      exact hnot (by rw [← hfz']; exact hfz)
    · exact isClosed_Iic.preimage hf.continuous
  exact ⟨by simpa [E, c', cellImage] using hAdj⟩

theorem sublevel_cellAdjunction_homotopyEquiv_of_morseChart_and_diffeomorph {n : ℕ} {H : Type}
    [TopologicalSpace H] {M : Type} [TopologicalSpace M]
    [ChartedSpace H M] [T2Space M] (I : ModelWithCorners ℝ (MorseModel n) H) [I.Boundaryless]
    [IsManifold I (⊤ : WithTop ℕ∞) M] (f : M → ℝ) (hf : ContMDiff I 𝓘(ℝ, ℝ) (⊤ : WithTop ℕ∞) f)
    (c : ℝ) (k : ℕ) (hk : k ≤ n)
    (data : MorseChartData n k hk c I f)
    (g : M → ℝ)
    (hlow : Nonempty (ContinuousMap.HomotopyEquiv (SublevelSpace g (c - data.ε))
      {x : M // x ∈ sublevel f (c - data.ε) ∪ cellImage hk c data}))
    (hgup : {x : M | g x ≤ c + data.ε} = sublevel f (c + data.ε))
    (Φ : Diffeomorph I I M M (↑(⊤ : ℕ∞) : WithTop ℕ∞))
    (hflow : Φ.toEquiv '' sublevel g (c - data.ε) = sublevel g (c + data.ε)) :
    Nonempty (ContinuousMap.HomotopyEquiv (SublevelSpace f (c + data.ε))
      (CellAdjunctionSpace k (cellAttachingMap hk c data))) := by
  let E : Set M := cellImage hk c data
  have hAdj : CellAdjunctionSpace k (cellAttachingMap hk c data) ≃ₜ
      {x : M // x ∈ sublevel f (c - data.ε) ∪ E} := by
    simpa [E] using (Classical.choice
      (cellAdjunctionSpace_homeomorph_lowerUnion (I := I) (hf := hf) (data := data)))
  have hflow' : Φ.toEquiv '' sublevel g (c - data.ε) = sublevel f (c + data.ε) := by
    change (Φ.toEquiv '' {x : M | g x ≤ c - data.ε}) = {x : M | g x ≤ c + data.ε} at hflow
    rw [hgup] at hflow
    exact hflow
  let d : M ≃ₜ M := Φ.toHomeomorph
  let s : Set M := sublevel g (c - data.ε)
  have hflowHomeo : SublevelSpace g (c - data.ε) ≃ₜ SublevelSpace f (c + data.ε) := by
    have himg : d '' s = sublevel f (c + data.ε) := by
      simpa [d, s] using hflow'
    exact (Homeomorph.image d s).trans (subtypeSetHomeo himg)
  have hlowE : ContinuousMap.HomotopyEquiv (SublevelSpace g (c - data.ε))
      {x : M // x ∈ sublevel f (c - data.ε) ∪ E} := Classical.choice hlow
  have hAdjE : ContinuousMap.HomotopyEquiv
      {x : M // x ∈ sublevel f (c - data.ε) ∪ E}
      (CellAdjunctionSpace k (cellAttachingMap hk c data)) := hAdj.symm.toHomotopyEquiv
  exact ⟨(hlowE.symm.trans hflowHomeo.toHomotopyEquiv).symm.trans hAdjE⟩

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

end ManifoldCellAttachment

end
end DifferentialGeometry.Topology.Morse
