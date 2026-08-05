import DifferentialGeometry.Topology.Morse.CellAttachment
import DifferentialGeometry.Topology.Morse.Flow
import DifferentialGeometry.Topology.Morse.Manifold

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

def subtypeSubtypeOfSubset {X : Type} [TopologicalSpace X] {s t : Set X} (hst : s ⊆ t) :
    {x : X // x ∈ s} ≃ₜ {x : {x : X // x ∈ t} // x.1 ∈ s} where
  toFun := fun x => ⟨⟨x.1, hst x.2⟩, x.2⟩
  invFun := fun x => ⟨x.1.1, x.2⟩
  left_inv := by intro x; rfl
  right_inv := by intro x; rfl
  continuous_toFun := by
    fun_prop
  continuous_invFun := by
    fun_prop

def subtypeSubtypeValHomeo {X : Type} [TopologicalSpace X] {s t : Set X} (ht : t ⊆ s) :
    {x : {y : X // y ∈ s} // x.1 ∈ t} ≃ₜ {x : X // x ∈ t} where
  toFun := fun x => ⟨x.1.1, x.2⟩
  invFun := fun x => ⟨⟨x.1, ht x.2⟩, x.2⟩
  left_inv := by intro x; rfl
  right_inv := by intro x; rfl
  continuous_toFun := by
    fun_prop
  continuous_invFun := by
    fun_prop

def homeoRestrictPred {A B : Type} [TopologicalSpace A] [TopologicalSpace B] (h : A ≃ₜ B)
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

def subtypeAndNestedHomeo {X : Type} [TopologicalSpace X] (p q : X → Prop) :
    {x : X // p x ∧ q x} ≃ₜ {x : {x : X // p x} // q x.1} where
  toFun := fun x => ⟨⟨x.1, x.2.1⟩, x.2.2⟩
  invFun := fun x => ⟨x.1.1, ⟨x.1.2, x.2⟩⟩
  left_inv := by intro x; rfl
  right_inv := by intro x; rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

def andSwapHomeo {X : Type} [TopologicalSpace X] (p q : X → Prop) :
    {x : X // p x ∧ q x} ≃ₜ {x : X // q x ∧ p x} where
  toFun := fun x => ⟨x.1, ⟨x.2.2, x.2.1⟩⟩
  invFun := fun x => ⟨x.1, ⟨x.2.2, x.2.1⟩⟩
  left_inv := by intro x; rfl
  right_inv := by intro x; rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

def subtypeSetHomeo {X : Type} [TopologicalSpace X] {s t : Set X} (h : s = t) :
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
  have hcrit' : IsCriticalPointAt I f p := (isCriticalPointAt_iff_chart_fderiv I f hf p).2 hcrit
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

def attachMap' {n k : ℕ} (hk : k ≤ n) (c : ℝ)
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

theorem cellAttachment {n : ℕ} {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M]
    [ChartedSpace H M] [T2Space M] (I : ModelWithCorners ℝ (MorseModel n) H) [I.Boundaryless]
    [IsManifold I (⊤ : WithTop ℕ∞) M] (f : M → ℝ) (hf : ContMDiff I 𝓘(ℝ, ℝ) (⊤ : WithTop ℕ∞) f)
    (p : M) (c : ℝ) (k : ℕ) (hk : k ≤ n)
    (_hcrit : fderiv ℝ (fun y => f ((extChartAt I p).symm y)) (extChartAt I p p) = 0)
    (_hnd : (QuadraticMap.associated (R := ℝ)
      (chartHessianAt (g := fun y => f ((extChartAt I p).symm y)) (extChartAt I p p))).SeparatingLeft)
    (_hindex : sigNeg (chartHessianAt (g := fun y => f ((extChartAt I p).symm y)) (extChartAt I p p)) = k)
    (_hfp : f p = c)
    (data : MorseChartData n k hk c I f)
    (_hcompact : IsCompact (f ⁻¹' Set.Icc (c - data.ε) (c + data.ε)))
    (_hunique : ∀ q ∈ f ⁻¹' Set.Icc (c - data.ε) (c + data.ε), IsCriticalPointAt I f q → q = p)
    (g : M → ℝ)
    (hglow : {x : M | g x ≤ c - data.ε} = sublevel f (c - data.ε) ∪ cellImage hk c data)
    (hgup : {x : M | g x ≤ c + data.ε} = sublevel f (c + data.ε))
    (Φ : GradientLikeFlow I g (c - data.ε) (c + data.ε)) :
    Nonempty (ContinuousMap.HomotopyEquiv (SublevelSpace f (c + data.ε))
      (CellAdjunctionSpace k (attachMap' hk c data))) := by
  let E : Set M := cellImage hk c data
  let c' : ClosedCell k → M := cellEmbedding hk c data
  let φ : CellBoundary k → {x : M // x ∈ sublevel f (c - data.ε)} := attachMap' hk c data
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
    noCriticalValues_toDiffeomorph Φ (by linarith [data.hεpos])
  have hflow' : (Φ.toDiffeomorph (c - data.ε - (c + data.ε))) ''
        (sublevel f (c - data.ε) ∪ E) = sublevel f (c + data.ε) := by
    change ((Φ.toDiffeomorph (c - data.ε - (c + data.ε))) '' {x : M | g x ≤ c - data.ε}) =
        {x : M | g x ≤ c + data.ε} at hflow
    rw [hglow, hgup] at hflow
    exact hflow
  let d : M ≃ₜ M := (Φ.toDiffeomorph (c - data.ε - (c + data.ε))).toHomeomorph
  let s : Set M := sublevel f (c - data.ε) ∪ E
  have hflowHomeo : {x : M // x ∈ s} ≃ₜ SublevelSpace f (c + data.ε) := by
    have himg : d '' s = sublevel f (c + data.ε) := by
      simpa [d, s] using hflow'
    exact (Homeomorph.image d s).trans (subtypeSetHomeo himg)
  have hAdj' : CellAdjunctionSpace k φ ≃ₜ {x : M // x ∈ s} := by
    simpa [s, E, c', cellImage] using hAdj
  exact ⟨(hflowHomeo.symm.trans hAdj'.symm).toHomotopyEquiv⟩

end ManifoldCellAttachment

end
end DifferentialGeometry.Topology.Morse
