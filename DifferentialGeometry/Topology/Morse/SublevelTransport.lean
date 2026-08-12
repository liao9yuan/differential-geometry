import DifferentialGeometry.Topology.Morse.ManifoldCellAttachment
import DifferentialGeometry.Topology.Morse.RegularIsotopy

namespace DifferentialGeometry.Topology.Morse

open Manifold Set ManifoldCellAttachment
open DifferentialGeometry.Analysis.ODE
open scoped Manifold ContDiff Topology

noncomputable section

private theorem morseFunction_value_at_morseChartPoint {m k : ℕ} (hk : k ≤ m + 1)
    (c : ℝ) {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} {f : M → ℝ}
    (data : MorseChart (m + 1) k hk c I f) : f data.p = c := by
  rw [← data.hχ0]
  have hnorm := data.hnorm 0 (by simpa [CellAttachment.morseNorm] using (le_of_lt data.hRpos))
  rw [hnorm]
  have hsplit := CellAttachment.morseNormalForm_split hk c (0 : MorseModel (m + 1))
  rw [hsplit]
  have hpos : CellAttachment.posPart hk (0 : MorseModel (m + 1)) = 0 := by
    ext j
    simp [CellAttachment.posPart]
  have hneg : CellAttachment.negPart hk (0 : MorseModel (m + 1)) = 0 := by
    ext i
    simp [CellAttachment.negPart]
  rw [hpos, hneg]
  simp

theorem morseFunction_no_critical_at_upper_level_of_morseChart {m k : ℕ} (hk : k ≤ m + 1)
    (c ε a ε₀ : ℝ) {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} {f : M → ℝ}
    (data : MorseChart (m + 1) k hk c I f)
    (hε : 0 < ε) (hε₀ : 0 < ε₀) (haε : ε + 2 * ε₀ ≤ a)
    (hunique : ∀ x : M, f x ∈ Set.Icc (c - a) (c + a) →
      x = data.p ∨ ¬ IsCriticalPointAt I f x)
    {x : M} (hx : f x = c + ε) : ¬ IsCriticalPointAt I f x := by
  have ha : ε ≤ a := by nlinarith [haε, hε₀.le]
  have hmem : f x ∈ Set.Icc (c - a) (c + a) := by
    constructor <;> nlinarith [hx, ha, hε.le]
  rcases hunique x hmem with hxp | hnc
  · exfalso
    have hpval : f data.p = c := morseFunction_value_at_morseChartPoint hk c data
    have : c = c + ε := by
      rw [hxp] at hx
      rw [hpval] at hx
      exact hx
    nlinarith [hε, this]
  · exact hnc

theorem exists_morseRoundedSublevel_diffeomorph_upperSublevel_of_morseChart
    {m k : ℕ} (hk : k ≤ m + 1)
    (c ε r δ R₀ R₁ R₁' a η ε₀ : ℝ) {H : Type} [TopologicalSpace H] {M : Type}
    [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [SigmaCompactSpace M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} [I.Boundaryless]
    [IsManifold I (⊤ : WithTop ℕ∞) M] {f : M → ℝ}
    (data : MorseChart (m + 1) k hk c I f)
    (hε : 0 < ε) (hε₀ : 0 < ε₀) (hδ : 0 < δ) (hδr : δ < r ^ 2) (hR : R₀ < R₁) (hR0 : 0 ≤ R₀)
    (hbig : 2 * (r ^ 2 + 2 * ε + δ) ≤ R₀ ^ 2) (hδR : 40 * δ < R₁ ^ 2 - R₀ ^ 2)
    (hε₀le : 2 * ε₀ < min (min ε (r ^ 2 / 2)) ((r ^ 2 - δ) / 2))
    (hR₁₂ : R₁ < R₁') (hR₁₂R : R₁' ≤ data.R) (hR₁₂R' : R₁' ≤ data.R')
    (hf : ContMDiff I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) f)
    (haε : ε + 2 * ε₀ ≤ a)
    (hcompact : IsCompact (f ⁻¹' Set.Icc (c - a) (c + a)))
    (hunique : ∀ x : M, f x ∈ Set.Icc (c - a) (c + a) →
      x = data.p ∨ ¬ IsCriticalPointAt I f x)
    (hreg_f : ∀ x : M, f x = c - ε → ¬ IsCriticalPointAt I f x)
    (hη : r ^ 2 + δ ≤ 2 * η) (hηε₀ : 2 * ε₀ < η)
    (hcs₁ : ChartedSpace (MorseHalfSpace m) (SublevelSpace (morseRoundedFunction hk c ε r δ R₀ R₁ data) c) :=
      morseRoundedSublevelChartedSpace hk c ε r δ R₀ R₁ R₁' data hε hδ hδr hR hR0 hbig
        hR₁₂ hR₁₂R hR₁₂R' hf hreg_f)
    (hcs₂ : ChartedSpace (MorseHalfSpace m) (SublevelSpace f (c + ε)) :=
      manifoldSublevelChartedSpace I f (c + ε) hf
        (fun _x hx => morseFunction_no_critical_at_upper_level_of_morseChart hk c ε a ε₀ data
          hε hε₀ haε hunique hx))
    (hchart₁ : ∀ y : SublevelSpace (morseRoundedFunction hk c ε r δ R₀ R₁ data) c, hcs₁.chartAt y =
      (if h : morseRoundedFunction hk c ε r δ R₀ R₁ data y.1 = c then
        manifoldSublevelBoundaryChart I (morseRoundedFunction hk c ε r δ R₀ R₁ data) c y h
          (contMDiff_morseRoundedFunction hk c ε r δ R₀ R₁ R₁' data hf hR hR0 hR₁₂ hR₁₂R hR₁₂R')
          (fun _x hx => morseRoundedFunction_no_critical_at_level hk c ε r δ R₀ R₁ R₁' data
            hε hδ hδr hR hR0 hbig hR₁₂ hR₁₂R hR₁₂R' hreg_f hx)
        else manifoldSublevelInteriorChart I (morseRoundedFunction hk c ε r δ R₀ R₁ data) c y
          (lt_of_le_of_ne (show morseRoundedFunction hk c ε r δ R₀ R₁ data y.1 ≤ c from y.2) h)
          (contMDiff_morseRoundedFunction hk c ε r δ R₀ R₁ R₁' data hf hR hR0 hR₁₂ hR₁₂R hR₁₂R')) := by
      intro y
      rfl)
    (hchart₂ : ∀ y : SublevelSpace f (c + ε), hcs₂.chartAt y =
      (if h : f y.1 = c + ε then
        manifoldSublevelBoundaryChart I f (c + ε) y h hf
          (fun _x hx => morseFunction_no_critical_at_upper_level_of_morseChart hk c ε a ε₀ data
            hε hε₀ haε hunique hx)
        else manifoldSublevelInteriorChart I f (c + ε) y
          (lt_of_le_of_ne (show f y.1 ≤ c + ε from y.2) h) hf) := by
      intro y
      rfl) :
    ∃ e : @Diffeomorph ℝ _ (MorseModel (m + 1)) _ _ (MorseModel (m + 1)) _ _
      (MorseHalfSpace m) _ (MorseHalfSpace m) _ (morseModelWithCornersHalfSpace m)
      (morseModelWithCornersHalfSpace m)
      (SublevelSpace (morseRoundedFunction hk c ε r δ R₀ R₁ data) c) _ hcs₁
      (SublevelSpace f (c + ε)) _ hcs₂ (⊤ : ℕ∞),
      ∀ x : M, f x ≤ c - ε - η → ∀ hx : morseRoundedFunction hk c ε r δ R₀ R₁ data x ≤ c,
        (e ⟨x, hx⟩).1 = x ∧
        ∀ hy : f x ≤ c + ε, (e.symm ⟨x, hy⟩).1 = x := by
  classical
  letI := hcs₁
  letI := hcs₂
  let F : M → ℝ → ℝ := fun x s =>
    morseSublevelIsotopyFamily hk c ε r δ R₀ R₁ data s x
  have hF : ContMDiff (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : M × ℝ => F q.1 q.2) := by
    simpa [F] using (contMDiff_morseSublevelIsotopyFamily hk c ε r δ R₀ R₁ R₁' data hf
      hR hR0 hR₁₂ hR₁₂R hR₁₂R')
  let D : Set M := {x : M | f x ≤ c - ε - η}
  have hDcl : IsClosed D := by
    have hcont : Continuous f := hf.continuous
    have hpre : IsClosed (f ⁻¹' Set.Iic (c - ε - η)) :=
      IsClosed.preimage hcont isClosed_Iic
    simpa [D] using hpre
  have hDsep : ∀ x : M, x ∈ D → ∀ s : ℝ, s ∈ Set.Icc 0 1 → 2 * ε₀ < |F x s| := by
    intro x hx s hs
    exact morseSublevelIsotopyFamily_strip_of_deep hk c ε r δ R₀ R₁ R₁' η ε₀ data
      (le_of_lt hε) hδ hR₁₂ hR₁₂R hη hηε₀ (le_of_lt hε₀) hx s hs
  have hDsign : ∀ x : M, x ∈ D → (F x 0 ≤ 0 ↔ F x 1 ≤ 0) := by
    intro x hx
    exact morseSublevelIsotopyFamily_sign_deep hk c ε r δ R₀ R₁ R₁' η data
      (le_of_lt hε) hδ hR₁₂ hR₁₂R hη hx
  rcases exists_relDiffeomorph_sublevel_of_regularFamily (I := I) F hF ε₀ hε₀
    (isCompact_morseSublevelIsotopyFamily_strip hk c ε r δ R₀ R₁ R₁' a data hf ε₀
      hε hR hR0 hR₁₂ hR₁₂R hR₁₂R' haε hcompact)
    (fun q hq hs => no_critical_morseSublevelIsotopyFamily_strip hk c ε r δ R₀ R₁ R₁' a ε₀ data
      hε hδ hδr hR hR0 hbig hδR hε₀le hR₁₂ hR₁₂R hR₁₂R' hf haε hunique q.2 hs (x := q.1) hq)
    D hDcl hDsep hDsign with
    ⟨Φ, Ψ, hΦsm, hΨsm, hDfix, hsub_fwd, hsub_back, hbnd_fwd, hbnd_back,
      hstrict_fwd, hstrict_back, hinv_fwd, hinv_back⟩
  have hreg_round : ∀ x : M, morseRoundedFunction hk c ε r δ R₀ R₁ data x = c →
      ¬ IsCriticalPointAt I (morseRoundedFunction hk c ε r δ R₀ R₁ data) x := by
    intro x hx
    exact morseRoundedFunction_no_critical_at_level hk c ε r δ R₀ R₁ R₁' data hε hδ hδr hR hR0 hbig
      hR₁₂ hR₁₂R hR₁₂R' hreg_f hx
  have hreg_upper : ∀ x : M, f x = c + ε → ¬ IsCriticalPointAt I f x := fun x hx =>
    morseFunction_no_critical_at_upper_level_of_morseChart hk c ε a ε₀ data hε hε₀ haε hunique hx
  have hround_sm : ContMDiff I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (morseRoundedFunction hk c ε r δ R₀ R₁ data) :=
    contMDiff_morseRoundedFunction hk c ε r δ R₀ R₁ R₁' data hf hR hR0 hR₁₂ hR₁₂R hR₁₂R'
  have hF0_le : ∀ x : M, morseRoundedFunction hk c ε r δ R₀ R₁ data x ≤ c → F x 0 ≤ 0 := by
    intro x hx
    dsimp [F, morseSublevelIsotopyFamily]
    nlinarith
  have hmap : ∀ x : M, morseRoundedFunction hk c ε r δ R₀ R₁ data x ≤ c → f (Φ x) ≤ c + ε := by
    intro x hx
    have hF1 : F (Φ x) 1 ≤ 0 := hsub_fwd x (hF0_le x hx)
    dsimp [F, morseSublevelIsotopyFamily] at hF1
    nlinarith
  have hbnd : ∀ x : M, morseRoundedFunction hk c ε r δ R₀ R₁ data x = c → f (Φ x) = c + ε := by
    intro x hx
    have hF0 : F x 0 = 0 := by
      dsimp [F, morseSublevelIsotopyFamily]
      rw [hx]
      ring
    have hF1 : F (Φ x) 1 = 0 := hbnd_fwd x hF0
    dsimp [F, morseSublevelIsotopyFamily] at hF1
    nlinarith
  have hstrict : ∀ x : M, morseRoundedFunction hk c ε r δ R₀ R₁ data x < c → f (Φ x) < c + ε := by
    intro x hx
    have hF0 : F x 0 < 0 := by
      dsimp [F, morseSublevelIsotopyFamily]
      nlinarith
    have hF1 : F (Φ x) 1 < 0 := hstrict_fwd x hF0
    dsimp [F, morseSublevelIsotopyFamily] at hF1
    nlinarith
  have hF1_le : ∀ x : M, f x ≤ c + ε → F x 1 ≤ 0 := by
    intro x hx
    dsimp [F, morseSublevelIsotopyFamily]
    nlinarith
  have hmap_back : ∀ x : M, f x ≤ c + ε → morseRoundedFunction hk c ε r δ R₀ R₁ data (Ψ x) ≤ c := by
    intro x hx
    have hF0 : F (Ψ x) 0 ≤ 0 := hsub_back x (hF1_le x hx)
    dsimp [F, morseSublevelIsotopyFamily] at hF0
    nlinarith
  have hbnd_back : ∀ x : M, f x = c + ε → morseRoundedFunction hk c ε r δ R₀ R₁ data (Ψ x) = c := by
    intro x hx
    have hF1 : F x 1 = 0 := by
      dsimp [F, morseSublevelIsotopyFamily]
      rw [hx]
      ring
    have hF0 : F (Ψ x) 0 = 0 := hbnd_back x hF1
    dsimp [F, morseSublevelIsotopyFamily] at hF0
    nlinarith
  have hstrict_back : ∀ x : M, f x < c + ε → morseRoundedFunction hk c ε r δ R₀ R₁ data (Ψ x) < c := by
    intro x hx
    have hF1 : F x 1 < 0 := by
      dsimp [F, morseSublevelIsotopyFamily]
      nlinarith
    have hF0 : F (Ψ x) 0 < 0 := hstrict_back x hF1
    dsimp [F, morseSublevelIsotopyFamily] at hF0
    nlinarith
  let toFun : SublevelSpace (morseRoundedFunction hk c ε r δ R₀ R₁ data) c →
      SublevelSpace f (c + ε) :=
    fun x => ⟨Φ x.1, hmap x.1 x.2⟩
  let invFun : SublevelSpace f (c + ε) →
      SublevelSpace (morseRoundedFunction hk c ε r δ R₀ R₁ data) c :=
    fun y => ⟨Ψ y.1, hmap_back y.1 y.2⟩
  let e : SublevelSpace (morseRoundedFunction hk c ε r δ R₀ R₁ data) c ≃
      SublevelSpace f (c + ε) := by
    refine { toFun := toFun, invFun := invFun, left_inv := ?_, right_inv := ?_ }
    · intro x
      apply Subtype.ext
      exact hinv_fwd x.1 (hF0_le x.1 x.2)
    · intro y
      apply Subtype.ext
      exact hinv_back y.1 (hF1_le y.1 y.2)
  let d : @Diffeomorph ℝ _ (MorseModel (m + 1)) _ _ (MorseModel (m + 1)) _ _
      (MorseHalfSpace m) _ (MorseHalfSpace m) _ (morseModelWithCornersHalfSpace m)
      (morseModelWithCornersHalfSpace m)
      (SublevelSpace (morseRoundedFunction hk c ε r δ R₀ R₁ data) c) _ hcs₁
      (SublevelSpace f (c + ε)) _ hcs₂ (⊤ : ℕ∞) := by
    refine { toEquiv := e, contMDiff_toFun := ?_, contMDiff_invFun := ?_ }
    · simpa [toFun] using contMDiff_manifoldSublevelMap (I := I)
        (morseRoundedFunction hk c ε r δ R₀ R₁ data) f c (c + ε)
        hround_sm hf hreg_round hreg_upper Φ hΦsm hmap hbnd hstrict
        (hcs₁ := hcs₁) (hcs₂ := hcs₂) (hchart₁ := hchart₁) (hchart₂ := hchart₂)
    · simpa [invFun] using contMDiff_manifoldSublevelMap (I := I)
        f (morseRoundedFunction hk c ε r δ R₀ R₁ data) (c + ε) c
        hf hround_sm hreg_upper hreg_round Ψ hΨsm hmap_back hbnd_back hstrict_back
        (hcs₁ := hcs₂) (hcs₂ := hcs₁) (hchart₁ := hchart₂) (hchart₂ := hchart₁)
  refine ⟨d, ?_⟩
  intro x hx_global hx
  constructor
  · dsimp [d, e, toFun]
    exact (hDfix x hx_global).1
  · intro hy
    dsimp [d, e, invFun]
    exact (hDfix x hx_global).2

private theorem no_criticalPointAt_above_c_of_uniqueCritical {m : ℕ} {H : Type}
    [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} [I.Boundaryless]
    [IsManifold I (⊤ : WithTop ℕ∞) M] (f : M → ℝ)
    (p : M) (c : ℝ) (hfp : f p = c) (a hlevel : ℝ)
    (hlevelpos : 0 < hlevel) (hlevela : hlevel ≤ a)
    (hunique : ∀ x : M, f x ∈ Set.Icc (c - a) (c + a) →
      x = p ∨ ¬ IsCriticalPointAt I f x)
    {x : M} (hx : f x = c + hlevel) :
    ¬ IsCriticalPointAt I f x := by
  have hmem : f x ∈ Set.Icc (c - a) (c + a) := by
    constructor <;> nlinarith [hx, hlevela]
  rcases hunique x hmem with hxp | hnc
  · exfalso
    have : c = c + hlevel := by
      rw [hxp] at hx
      rw [hfp] at hx
      exact hx
    nlinarith [this, hlevelpos]
  · exact hnc

private theorem regularFamily_f_sublevel_of_uniqueCritical
    {m : ℕ} {H : Type} [TopologicalSpace H] {M : Type}
    [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [SigmaCompactSpace M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} [I.Boundaryless]
    [IsManifold I (⊤ : WithTop ℕ∞) M] (f : M → ℝ)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) f)
    (p : M) (c : ℝ) (hfp : f p = c)
    (r ε a η ε₀ : ℝ)
    (hε : 0 < ε) (hε₀ : 0 < ε₀)
    (hε₀le : 2 * ε₀ < min ε (r ^ 2 / 2))
    (hr2a : r ^ 2 / 2 + 2 * ε₀ ≤ a)
    (haε : ε + 2 * ε₀ ≤ a)
    (hcompact : IsCompact (f ⁻¹' Set.Icc (c - a) (c + a)))
    (hunique : ∀ x : M, f x ∈ Set.Icc (c - a) (c + a) →
      x = p ∨ ¬ IsCriticalPointAt I f x)
    (hηε₀ : 2 * ε₀ < η) :
    ∃ Φ Ψ : M → M,
      ContMDiff I I (⊤ : ℕ∞) Φ ∧ ContMDiff I I (⊤ : ℕ∞) Ψ ∧
      (∀ x : M, f x ≤ c - ε - η → Φ x = x ∧ Ψ x = x) ∧
      (∀ x : M, f x ≤ c + r ^ 2 / 2 → f (Φ x) ≤ c + ε) ∧
      (∀ y : M, f y ≤ c + ε → f (Ψ y) ≤ c + r ^ 2 / 2) ∧
      (∀ x : M, f x = c + r ^ 2 / 2 → f (Φ x) = c + ε) ∧
      (∀ y : M, f y = c + ε → f (Ψ y) = c + r ^ 2 / 2) ∧
      (∀ x : M, f x < c + r ^ 2 / 2 → f (Φ x) < c + ε) ∧
      (∀ y : M, f y < c + ε → f (Ψ y) < c + r ^ 2 / 2) ∧
      (∀ x : M, f x ≤ c + r ^ 2 / 2 → Ψ (Φ x) = x) ∧
      (∀ y : M, f y ≤ c + ε → Φ (Ψ y) = y) := by
  classical
  let F : M → ℝ → ℝ := fun x s => f x - (c + r ^ 2 / 2 + s * (ε - r ^ 2 / 2))
  have hF : ContMDiff (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : M × ℝ => F q.1 q.2) := by
    have hfst : ContMDiff (I.prod 𝓘(ℝ, ℝ)) I (↑(⊤ : ℕ∞) : WithTop ℕ∞)
        (fun q : M × ℝ => q.1) := contMDiff_fst
    have hfs : ContMDiff (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
        (fun q : M × ℝ => f q.1) := hf.comp hfst
    have hsnd : ContMDiff (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
        (fun q : M × ℝ => q.2) := contMDiff_snd
    have hconst : ContMDiff (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
        (fun q : M × ℝ => c + r ^ 2 / 2 + q.2 * (ε - r ^ 2 / 2)) := by
      simpa using ((contMDiff_const : ContMDiff (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) (⊤ : ℕ∞)
        (fun _ : M × ℝ => c + r ^ 2 / 2)).add
        (hsnd.mul (contMDiff_const : ContMDiff (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) (⊤ : ℕ∞)
          (fun _ : M × ℝ => ε - r ^ 2 / 2))))
    simpa [F] using hfs.sub hconst
  let D : Set M := {x : M | f x ≤ c - ε - η}
  have hDcl : IsClosed D := by
    have hcont : Continuous f := hf.continuous
    have hpre : IsClosed (f ⁻¹' Set.Iic (c - ε - η)) :=
      IsClosed.preimage hcont isClosed_Iic
    simpa [D] using hpre
  have hε₀ε : 2 * ε₀ < ε := (lt_min_iff.mp hε₀le).1
  have hε₀r : 2 * ε₀ < r ^ 2 / 2 := (lt_min_iff.mp hε₀le).2
  have ha : 0 < a := by nlinarith [hr2a, hε₀]
  have hlevel_mem : ∀ q : M × ℝ, |F q.1 q.2| ≤ 2 * ε₀ → q.2 ∈ Set.Icc 0 1 →
      f q.1 ∈ Set.Icc (c - a) (c + a) := by
    intro q hq hs
    have hFhi : F q.1 q.2 ≤ 2 * ε₀ := (abs_le.mp hq).2
    have hFlo : -(2 * ε₀) ≤ F q.1 q.2 := (abs_le.mp hq).1
    have hlevlo : 2 * ε₀ < r ^ 2 / 2 + q.2 * (ε - r ^ 2 / 2) := by
      rcases le_total ε (r ^ 2 / 2) with h | h
      · nlinarith [hε₀ε, hs.2, h]
      · nlinarith [hε₀r, hs.1, h]
    have hlevhi : r ^ 2 / 2 + q.2 * (ε - r ^ 2 / 2) ≤ max (r ^ 2 / 2) ε := by
      nlinarith [le_max_left (r ^ 2 / 2) ε, le_max_right (r ^ 2 / 2) ε, hs.1, hs.2]
    have hmaxa : max (r ^ 2 / 2) ε + 2 * ε₀ ≤ a := by
      rcases le_total (r ^ 2 / 2) ε with h | h
      · rw [max_eq_right h]
        exact haε
      · rw [max_eq_left h]
        exact hr2a
    constructor
    · dsimp [F] at hFlo
      nlinarith [hFlo, hlevlo, ha]
    · dsimp [F] at hFhi
      nlinarith [hFhi, hlevhi, hmaxa]
  have hlevel_ne_c : ∀ q : M × ℝ, |F q.1 q.2| ≤ 2 * ε₀ → q.2 ∈ Set.Icc 0 1 →
      f q.1 ≠ c := by
    intro q hq hs
    have hFlo : -(2 * ε₀) ≤ F q.1 q.2 := (abs_le.mp hq).1
    have hlevlo : 2 * ε₀ < r ^ 2 / 2 + q.2 * (ε - r ^ 2 / 2) := by
      rcases le_total ε (r ^ 2 / 2) with h | h
      · nlinarith [hε₀ε, hs.2, h]
      · nlinarith [hε₀r, hs.1, h]
    dsimp [F] at hFlo
    nlinarith [hFlo, hlevlo]
  have hstrip : IsCompact {q : M × ℝ | |F q.1 q.2| ≤ 2 * ε₀ ∧ q.2 ∈ Set.Icc 0 1} := by
    have hK : IsCompact ((f ⁻¹' Set.Icc (c - a) (c + a)) ×ˢ (Set.Icc (0 : ℝ) 1)) :=
      hcompact.prod isCompact_Icc
    have hcl : IsClosed {q : M × ℝ | |F q.1 q.2| ≤ 2 * ε₀ ∧ q.2 ∈ Set.Icc 0 1} := by
      have hcF : Continuous (fun q : M × ℝ => F q.1 q.2) := hF.continuous
      exact (isClosed_le (continuous_norm.comp hcF) continuous_const).inter
        (isClosed_Icc.preimage continuous_snd)
    refine hK.of_isClosed_subset hcl ?_
    intro q hq
    exact ⟨hlevel_mem q hq.1 hq.2, hq.2⟩
  have hreg : ∀ q : M × ℝ, |F q.1 q.2| ≤ 2 * ε₀ → q.2 ∈ Set.Icc 0 1 →
      ¬ IsCriticalPointAt I (fun x : M => F x q.2) q.1 := by
    intro q hq hs
    have hmem : f q.1 ∈ Set.Icc (c - a) (c + a) := hlevel_mem q hq hs
    rcases hunique q.1 hmem with hxp | hnc
    · exfalso
      exact (hlevel_ne_c q hq hs) (by rw [hxp]; exact hfp)
    · have hcrit_eq : IsCriticalPointAt I (fun x : M => F x q.2) q.1 ↔
          IsCriticalPointAt I f q.1 := by
        have hg : ContMDiff I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
            (fun x : M => F x q.2) := regularFamilySliceSmooth I F hF q.2
        rw [isCriticalPointAt_iff_chart_fderiv I (fun x : M => F x q.2) hg q.1]
        rw [isCriticalPointAt_iff_chart_fderiv I f hf q.1]
        have hEq : (fun y : MorseModel (m + 1) => F ((extChartAt I q.1).symm y) q.2) =ᶠ[nhds ((extChartAt I q.1) q.1)] (fun y : MorseModel (m + 1) => f ((extChartAt I q.1).symm y) - (c + r ^ 2 / 2 + q.2 * (ε - r ^ 2 / 2))) := by
          filter_upwards with y
          simp [F]
        have hfe : fderiv ℝ (fun y : MorseModel (m + 1) => F ((extChartAt I q.1).symm y) q.2)
              ((extChartAt I q.1) q.1) =
            fderiv ℝ (fun y : MorseModel (m + 1) =>
              f ((extChartAt I q.1).symm y) - (c + r ^ 2 / 2 + q.2 * (ε - r ^ 2 / 2)))
              ((extChartAt I q.1) q.1) :=
          Filter.EventuallyEq.fderiv_eq hEq
        rw [hfe]
        have hsub := fderiv_sub_const (𝕜 := ℝ)
          (f := fun y : MorseModel (m + 1) => f ((extChartAt I q.1).symm y))
          (x := (extChartAt I q.1) q.1) (c := c + r ^ 2 / 2 + q.2 * (ε - r ^ 2 / 2))
        rw [← hsub]
      exact fun hc => hnc (hcrit_eq.mp hc)
  have hDsep : ∀ x : M, x ∈ D → ∀ s : ℝ, s ∈ Set.Icc 0 1 → 2 * ε₀ < |F x s| := by
    intro x hx s hs
    change f x ≤ c - ε - η at hx
    have hFneg : F x s ≤ -ε - η := by
      change f x - (c + r ^ 2 / 2 + s * (ε - r ^ 2 / 2)) ≤ -ε - η
      have hle : f x - c ≤ -ε - η := by linarith
      have hsum : 0 ≤ (1 - s) * (r ^ 2 / 2) + s * ε := by
        nlinarith [sq_nonneg r, hε.le, hs.1, hs.2]
      linarith [hle, hsum]
    have hFneg' : F x s < 0 := by nlinarith [hFneg, hε, hηε₀]
    have hFabs : ε + η ≤ |F x s| := by
      rw [abs_of_neg hFneg']
      linarith
    nlinarith [hFabs, hηε₀]
  have hDsign : ∀ x : M, x ∈ D → (F x 0 ≤ 0 ↔ F x 1 ≤ 0) := by
    intro x hx
    change f x ≤ c - ε - η at hx
    have h0 : F x 0 < 0 := by
      dsimp [F]
      nlinarith [hx]
    have h1 : F x 1 < 0 := by
      dsimp [F]
      nlinarith [hx, hε]
    constructor
    · intro _
      exact le_of_lt h1
    · intro _
      exact le_of_lt h0
  rcases exists_relDiffeomorph_sublevel_of_regularFamily (I := I) F hF ε₀ hε₀ hstrip hreg
    D hDcl hDsep hDsign with
    ⟨Φ, Ψ, hΦsm, hΨsm, hDfix, hsub_fwd, hsub_back, hbnd_fwd, hbnd_back,
      hstrict_fwd, hstrict_back, hinv_fwd, hinv_back⟩
  refine ⟨Φ, Ψ, hΦsm, hΨsm, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    exact hDfix x hx
  · intro x hx
    have hF1 : F (Φ x) 1 ≤ 0 := hsub_fwd x (by
      dsimp [F]
      nlinarith)
    dsimp [F] at hF1
    nlinarith
  · intro y hy
    have hF0 : F (Ψ y) 0 ≤ 0 := hsub_back y (by
      dsimp [F]
      nlinarith)
    dsimp [F] at hF0
    nlinarith
  · intro x hx
    have hF0 : F x 0 = 0 := by
      dsimp [F]
      rw [hx]
      ring
    have hF1 : F (Φ x) 1 = 0 := hbnd_fwd x hF0
    dsimp [F] at hF1
    nlinarith
  · intro y hy
    have hF1 : F y 1 = 0 := by
      dsimp [F]
      rw [hy]
      ring
    have hF0 : F (Ψ y) 0 = 0 := hbnd_back y hF1
    dsimp [F] at hF0
    nlinarith
  · intro x hx
    have hF1 : F (Φ x) 1 < 0 := hstrict_fwd x (by
      dsimp [F]
      nlinarith)
    dsimp [F] at hF1
    nlinarith
  · intro y hy
    have hF0 : F (Ψ y) 0 < 0 := hstrict_back y (by
      dsimp [F]
      nlinarith)
    dsimp [F] at hF0
    nlinarith
  · intro x hx
    exact hinv_fwd x (by
      dsimp [F]
      nlinarith)
  · intro y hy
    exact hinv_back y (by
      dsimp [F]
      nlinarith)


theorem exists_sublevel_diffeomorph_regularLevels_of_uniqueCriticalPoint
    {m : ℕ} {H : Type} [TopologicalSpace H] {M : Type}
    [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [SigmaCompactSpace M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} [I.Boundaryless]
    [IsManifold I (⊤ : WithTop ℕ∞) M] (f : M → ℝ)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) f)
    (p : M) (c : ℝ) (hfp : f p = c)
    (r ε a η ε₀ : ℝ)
    (hε : 0 < ε) (hε₀ : 0 < ε₀) (hr : 0 < r)
    (hε₀le : 2 * ε₀ < min ε (r ^ 2 / 2))
    (hr2a : r ^ 2 / 2 + 2 * ε₀ ≤ a)
    (haε : ε + 2 * ε₀ ≤ a)
    (hcompact : IsCompact (f ⁻¹' Set.Icc (c - a) (c + a)))
    (hunique : ∀ x : M, f x ∈ Set.Icc (c - a) (c + a) →
      x = p ∨ ¬ IsCriticalPointAt I f x)
    (hηε₀ : 2 * ε₀ < η)
    (hcs₁ : ChartedSpace (MorseHalfSpace m) (SublevelSpace f (c + r ^ 2 / 2)) :=
      manifoldSublevelChartedSpace I f (c + r ^ 2 / 2) hf (fun x hx =>
        no_criticalPointAt_above_c_of_uniqueCritical f p c hfp a (r ^ 2 / 2)
          (by positivity) (by nlinarith [hr2a]) hunique hx))
    (hcs₂ : ChartedSpace (MorseHalfSpace m) (SublevelSpace f (c + ε)) :=
      manifoldSublevelChartedSpace I f (c + ε) hf (fun x hx =>
        no_criticalPointAt_above_c_of_uniqueCritical f p c hfp a ε hε
          (by nlinarith [haε]) hunique hx))
    (hchart₁ : ∀ y : SublevelSpace f (c + r ^ 2 / 2), hcs₁.chartAt y =
      (if h : f y.1 = c + r ^ 2 / 2 then
        manifoldSublevelBoundaryChart I f (c + r ^ 2 / 2) y h hf
          (fun x hx => no_criticalPointAt_above_c_of_uniqueCritical f p c hfp a (r ^ 2 / 2)
            (by positivity) (by nlinarith [hr2a]) hunique hx)
        else manifoldSublevelInteriorChart I f (c + r ^ 2 / 2) y
          (lt_of_le_of_ne (show f y.1 ≤ c + r ^ 2 / 2 from y.2) h) hf) := by
      intro y
      rfl)
    (hchart₂ : ∀ y : SublevelSpace f (c + ε), hcs₂.chartAt y =
      (if h : f y.1 = c + ε then
        manifoldSublevelBoundaryChart I f (c + ε) y h hf
          (fun x hx => no_criticalPointAt_above_c_of_uniqueCritical f p c hfp a ε hε
            (by nlinarith [haε]) hunique hx)
        else manifoldSublevelInteriorChart I f (c + ε) y
          (lt_of_le_of_ne (show f y.1 ≤ c + ε from y.2) h) hf) := by
      intro y
      rfl) :
    ∃ e : @Diffeomorph ℝ _ (MorseModel (m + 1)) _ _ (MorseModel (m + 1)) _ _
      (MorseHalfSpace m) _ (MorseHalfSpace m) _ (morseModelWithCornersHalfSpace m)
      (morseModelWithCornersHalfSpace m)
      (SublevelSpace f (c + r ^ 2 / 2)) _ hcs₁
      (SublevelSpace f (c + ε)) _ hcs₂ (⊤ : ℕ∞),
      ∀ x : M, f x ≤ c - ε - η → ∀ hx : f x ≤ c + r ^ 2 / 2,
        (e ⟨x, hx⟩).1 = x ∧ ∀ hy : f x ≤ c + ε, (e.symm ⟨x, hy⟩).1 = x := by
  classical
  letI := hcs₁
  letI := hcs₂
  rcases regularFamily_f_sublevel_of_uniqueCritical f hf p c hfp r ε a η ε₀ hε hε₀ hε₀le
    hr2a haε hcompact hunique hηε₀ with
    ⟨Φ, Ψ, hΦsm, hΨsm, hDfix, hmap, hmap_back, hbnd, hbnd_back, hstrict, hstrict_back,
      hinv_fwd, hinv_back⟩
  have hreg₁ : ∀ x : M, f x = c + r ^ 2 / 2 → ¬ IsCriticalPointAt I f x := fun x hx =>
    no_criticalPointAt_above_c_of_uniqueCritical f p c hfp a (r ^ 2 / 2)
      (by positivity) (by nlinarith [hr2a]) hunique hx
  have hreg₂ : ∀ x : M, f x = c + ε → ¬ IsCriticalPointAt I f x := fun x hx =>
    no_criticalPointAt_above_c_of_uniqueCritical f p c hfp a ε hε
      (by nlinarith [haε]) hunique hx
  let toFun : SublevelSpace f (c + r ^ 2 / 2) → SublevelSpace f (c + ε) :=
    fun x => ⟨Φ x.1, hmap x.1 x.2⟩
  let invFun : SublevelSpace f (c + ε) → SublevelSpace f (c + r ^ 2 / 2) :=
    fun y => ⟨Ψ y.1, hmap_back y.1 y.2⟩
  let e : SublevelSpace f (c + r ^ 2 / 2) ≃ SublevelSpace f (c + ε) := by
    refine { toFun := toFun, invFun := invFun, left_inv := ?_, right_inv := ?_ }
    · intro x
      apply Subtype.ext
      exact hinv_fwd x.1 x.2
    · intro y
      apply Subtype.ext
      exact hinv_back y.1 y.2
  let d : @Diffeomorph ℝ _ (MorseModel (m + 1)) _ _ (MorseModel (m + 1)) _ _
      (MorseHalfSpace m) _ (MorseHalfSpace m) _ (morseModelWithCornersHalfSpace m)
      (morseModelWithCornersHalfSpace m)
      (SublevelSpace f (c + r ^ 2 / 2)) _ hcs₁
      (SublevelSpace f (c + ε)) _ hcs₂ (⊤ : ℕ∞) := by
    refine { toEquiv := e, contMDiff_toFun := ?_, contMDiff_invFun := ?_ }
    · simpa [toFun] using contMDiff_manifoldSublevelMap (I := I)
        f f (c + r ^ 2 / 2) (c + ε) hf hf hreg₁ hreg₂ Φ hΦsm hmap hbnd hstrict
        (hcs₁ := hcs₁) (hcs₂ := hcs₂) (hchart₁ := hchart₁) (hchart₂ := hchart₂)
    · simpa [invFun] using contMDiff_manifoldSublevelMap (I := I)
        f f (c + ε) (c + r ^ 2 / 2) hf hf hreg₂ hreg₁ Ψ hΨsm hmap_back hbnd_back hstrict_back
        (hcs₁ := hcs₂) (hcs₂ := hcs₁) (hchart₁ := hchart₂) (hchart₂ := hchart₁)
  refine ⟨d, ?_⟩
  intro x hx_global hx
  constructor
  · dsimp [d, e, toFun]
    exact (hDfix x hx_global).1
  · intro hy
    dsimp [d, e, invFun]
    exact (hDfix x hx_global).2


theorem exists_morseHandleAdjunction_diffeomorph_upperSublevel_of_morseChart
    {m k : ℕ} (hk : k ≤ m + 1)
    (c ε r δ R₀ R₁ R₁' a η ε₀ : ℝ) {H : Type} [TopologicalSpace H] {M : Type}
    [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [SigmaCompactSpace M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} [I.Boundaryless]
    [IsManifold I (⊤ : WithTop ℕ∞) M] {f : M → ℝ}
    (data : MorseChart (m + 1) k hk c I f)
    (hε : 0 < ε) (hε₀ : 0 < ε₀) (hδ : 0 < δ) (hδr : δ < r ^ 2) (hr : 0 < r)
    (hR : R₀ < R₁) (hR0 : 0 ≤ R₀)
    (hbig : 2 * (r ^ 2 + 2 * ε + δ) ≤ R₀ ^ 2) (hδR : 40 * δ < R₁ ^ 2 - R₀ ^ 2)
    (hε₀le : 2 * ε₀ < min (min ε (r ^ 2 / 2)) ((r ^ 2 - δ) / 2))
    (hR₁₂ : R₁ < R₁') (hR₁₂R : R₁' ≤ data.R) (hR₁₂R' : R₁' ≤ data.R')
    (hf : ContMDiff I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) f)
    (haε : ε + 2 * ε₀ ≤ a)
    (hcompact : IsCompact (f ⁻¹' Set.Icc (c - a) (c + a)))
    (hunique : ∀ x : M, f x ∈ Set.Icc (c - a) (c + a) →
      x = data.p ∨ ¬ IsCriticalPointAt I f x)
    (hreg_f : ∀ x : M, f x = c - ε → ¬ IsCriticalPointAt I f x)
    (hη : r ^ 2 + δ ≤ 2 * η) (hηε₀ : 2 * ε₀ < η)
    (hεr' : Real.sqrt (2 * ε + 2 * r ^ 2) < data.R / 2)
    (hbigR : r ^ 2 + ε + δ ≤ data.R ^ 2 / 8)
    (hRbig : r ^ 2 + 2 * ε + δ ≤ (data.R / 2) ^ 2)
    (hR₁big : 2 * (data.R / 2) ^ 2 - 2 * ε ≤ R₁ ^ 2)
    (hR₁₂R₀ : R₁ ≤ data.R)
    (hcont : Continuous f) :
    ∃ e₂ : @Diffeomorph ℝ _ (MorseModel (m + 1)) _ _ (MorseModel (m + 1)) _ _
      (MorseHalfSpace m) _ (MorseHalfSpace m) _ (morseModelWithCornersHalfSpace m)
      (morseModelWithCornersHalfSpace m)
      (SublevelSpace (morseRoundedFunction hk c ε r δ R₀ R₁ data) c) _
      (morseRoundedSublevelChartedSpace hk c ε r δ R₀ R₁ R₁' data hε hδ hδr hR hR0 hbig
        hR₁₂ hR₁₂R hR₁₂R' hf hreg_f)
      (SublevelSpace f (c + ε)) _
      (manifoldSublevelChartedSpace I f (c + ε) hf
        (fun _x hx => morseFunction_no_critical_at_upper_level_of_morseChart hk c ε a ε₀ data
          hε hε₀ haε hunique hx))
      (⊤ : ℕ∞),
    ∃ e : @Diffeomorph ℝ _ (MorseModel (m + 1)) _ _ (MorseModel (m + 1)) _ _
      (MorseHalfSpace m) _ (MorseHalfSpace m) _ (morseModelWithCornersHalfSpace m)
      (morseModelWithCornersHalfSpace m)
      (Handle.AdjunctionSpace k (m + 1 - k)
        (morseAttachingEmbedding hk c ε r data hε
          (le_trans (le_of_lt hεr') (by nlinarith [data.hRpos] : data.R / 2 ≤ data.R)))) _
      (morseHandleAdjunctionChartedSpace hk c ε r δ R₀ R₁ R₁' data hε hδ hδr hr hεr' hbigR
        hR hR0 hbig hRbig hR₁big hR₁₂R₀ hR₁₂ hR₁₂R hR₁₂R' hcont hf hreg_f)
      (SublevelSpace f (c + ε)) _
      (manifoldSublevelChartedSpace I f (c + ε) hf
        (fun _x hx => morseFunction_no_critical_at_upper_level_of_morseChart hk c ε a ε₀ data
          hε hε₀ haε hunique hx))
      (⊤ : ℕ∞),
      (∀ z : Handle.AdjunctionSpace k (m + 1 - k)
          (morseAttachingEmbedding hk c ε r data hε
            (le_trans (le_of_lt hεr') (by nlinarith [data.hRpos] : data.R / 2 ≤ data.R))),
        (e z).1 = (e₂ (morseHandleAdjunctionEquivRoundedSublevel hk c ε r δ R₀ R₁ data
          hε hδ hδr hr hεr' hbigR hR hR0 hbig hRbig hR₁big hR₁₂R₀ hcont z)).1) ∧
      (∀ x : M, f x ≤ c - ε - η → ∀ hx : f x ≤ c - ε,
        (e (Handle.lower (morseAttachingEmbedding hk c ε r data hε
          (le_trans (le_of_lt hεr') (by nlinarith [data.hRpos] : data.R / 2 ≤ data.R)))
          ⟨x, hx⟩)).1 = x) ∧
      (∀ y : M, (hydeep : f y ≤ c - ε - η) → ∀ hy : f y ≤ c + ε,
        ∀ z : Handle.AdjunctionSpace k (m + 1 - k)
            (morseAttachingEmbedding hk c ε r data hε
              (le_trans (le_of_lt hεr') (by nlinarith [data.hRpos] : data.R / 2 ≤ data.R))),
          e z = ⟨y, hy⟩ →
            z = Handle.lower (morseAttachingEmbedding hk c ε r data hε
              (le_trans (le_of_lt hεr') (by nlinarith [data.hRpos] : data.R / 2 ≤ data.R)))
              ⟨y, by
                have hsum : 0 ≤ r ^ 2 + δ := by positivity
                have hη0 : 0 ≤ η := by nlinarith [hη, hsum]
                change f y ≤ c - ε
                nlinarith [hydeep, hη0]⟩) := by
  classical
  let φ : Handle.AttachingRegion k (m + 1 - k) → SublevelSpace f (c - ε) :=
    morseAttachingEmbedding hk c ε r data hε
      (le_trans (le_of_lt hεr') (by nlinarith [data.hRpos] : data.R / 2 ≤ data.R))
  let h : Handle.AdjunctionSpace k (m + 1 - k) φ ≃ₜ
      SublevelSpace (morseRoundedFunction hk c ε r δ R₀ R₁ data) c :=
    morseHandleAdjunctionEquivRoundedSublevel hk c ε r δ R₀ R₁ data hε hδ hδr hr hεr' hbigR
      hR hR0 hbig hRbig hR₁big hR₁₂R₀ hcont
  letI : ChartedSpace (MorseHalfSpace m)
      (Handle.AdjunctionSpace k (m + 1 - k) φ) :=
    morseHandleAdjunctionChartedSpace hk c ε r δ R₀ R₁ R₁' data hε hδ hδr hr hεr' hbigR
      hR hR0 hbig hRbig hR₁big hR₁₂R₀ hR₁₂ hR₁₂R hR₁₂R' hcont hf hreg_f
  letI : ChartedSpace (MorseHalfSpace m)
      (SublevelSpace (morseRoundedFunction hk c ε r δ R₀ R₁ data) c) :=
    morseRoundedSublevelChartedSpace hk c ε r δ R₀ R₁ R₁' data hε hδ hδr hR hR0 hbig
      hR₁₂ hR₁₂R hR₁₂R' hf hreg_f
  letI : IsManifold (morseModelWithCornersHalfSpace m) (⊤ : ℕ∞)
      (SublevelSpace (morseRoundedFunction hk c ε r δ R₀ R₁ data) c) :=
    morseRoundedSublevelIsManifold hk c ε r δ R₀ R₁ R₁' data hε hδ hδr hR hR0 hbig
      hR₁₂ hR₁₂R hR₁₂R' hf hreg_f
  letI : ChartedSpace (MorseHalfSpace m) (SublevelSpace f (c + ε)) :=
    manifoldSublevelChartedSpace I f (c + ε) hf
      (fun _x hx => morseFunction_no_critical_at_upper_level_of_morseChart hk c ε a ε₀ data
        hε hε₀ haε hunique hx)
  let hD : @Diffeomorph ℝ _ (MorseModel (m + 1)) _ _ (MorseModel (m + 1)) _ _
      (MorseHalfSpace m) _ (MorseHalfSpace m) _ (morseModelWithCornersHalfSpace m)
      (morseModelWithCornersHalfSpace m)
      (Handle.AdjunctionSpace k (m + 1 - k) φ) _
      (morseHandleAdjunctionChartedSpace hk c ε r δ R₀ R₁ R₁' data hε hδ hδr hr hεr' hbigR
        hR hR0 hbig hRbig hR₁big hR₁₂R₀ hR₁₂ hR₁₂R hR₁₂R' hcont hf hreg_f)
      (SublevelSpace (morseRoundedFunction hk c ε r δ R₀ R₁ data) c) _
      (morseRoundedSublevelChartedSpace hk c ε r δ R₀ R₁ R₁' data hε hδ hδr hR hR0 hbig
        hR₁₂ hR₁₂R hR₁₂R' hf hreg_f)
      (⊤ : ℕ∞) :=
    morseHandleAdjunctionDiffeomorphRoundedSublevel hk c ε r δ R₀ R₁ R₁' data hε hδ hδr hr
      hεr' hbigR hR hR0 hbig hRbig hR₁big hR₁₂R₀ hR₁₂ hR₁₂R hR₁₂R' hcont hf hreg_f
  rcases exists_morseRoundedSublevel_diffeomorph_upperSublevel_of_morseChart (m := m) (k := k)
    (hk := hk) (c := c) (ε := ε) (r := r) (δ := δ) (R₀ := R₀) (R₁ := R₁) (R₁' := R₁')
    (a := a) (η := η) (ε₀ := ε₀) (data := data)
    hε hε₀ hδ hδr hR hR0 hbig hδR hε₀le hR₁₂ hR₁₂R hR₁₂R' hf haε hcompact hunique hreg_f
    hη hηε₀ (hcs₁ := morseRoundedSublevelChartedSpace hk c ε r δ R₀ R₁ R₁' data hε hδ hδr
      hR hR0 hbig hR₁₂ hR₁₂R hR₁₂R' hf hreg_f) with ⟨e₂, hrel⟩
  let e : @Diffeomorph ℝ _ (MorseModel (m + 1)) _ _ (MorseModel (m + 1)) _ _
      (MorseHalfSpace m) _ (MorseHalfSpace m) _ (morseModelWithCornersHalfSpace m)
      (morseModelWithCornersHalfSpace m)
      (Handle.AdjunctionSpace k (m + 1 - k) φ) _
      (morseHandleAdjunctionChartedSpace hk c ε r δ R₀ R₁ R₁' data hε hδ hδr hr hεr' hbigR
        hR hR0 hbig hRbig hR₁big hR₁₂R₀ hR₁₂ hR₁₂R hR₁₂R' hcont hf hreg_f)
      (SublevelSpace f (c + ε)) _
      (manifoldSublevelChartedSpace I f (c + ε) hf
        (fun _x hx => morseFunction_no_critical_at_upper_level_of_morseChart hk c ε a ε₀ data
          hε hε₀ haε hunique hx))
      (⊤ : ℕ∞) :=
    hD.trans e₂
  have hcomm : ∀ z : Handle.AdjunctionSpace k (m + 1 - k) φ,
      (e z).1 = (e₂ (h z)).1 := by
    intro z
    change (e z).1 = (e₂.toFun (h z)).1
    rfl
  refine ⟨e₂, e, ?_, ?_, ?_⟩
  · intro z
    exact hcomm z
  · intro x hx_global hx
    have hlower : (h (Handle.lower φ ⟨x, hx⟩)).1 = x := by
      dsimp [φ]
      exact morseHandleAdjunctionEquivRoundedSublevel_lower hk c ε r δ R₀ R₁ η data hε hδ hδr hr
        hεr' hbigR hR hR0 hbig hRbig hR₁big hR₁₂R₀ hcont hη hx_global
    have hmem : morseRoundedFunction hk c ε r δ R₀ R₁ data x ≤ c := by
      have hb := morseSublevelIsotopyFamily_le_neg_eta_of_deep hk c ε r δ R₀ R₁ R₁' η data
        (le_of_lt hε) hδ hR₁₂ hR₁₂R hη hx_global 0 (by norm_num)
      have hF0 : morseSublevelIsotopyFamily hk c ε r δ R₀ R₁ data 0 x =
          morseRoundedFunction hk c ε r δ R₀ R₁ data x - c := by
        dsimp [morseSublevelIsotopyFamily]
        ring
      rw [hF0] at hb
      have hsum : 0 ≤ r ^ 2 + δ := by positivity
      have hη0 : 0 ≤ η := by
        have h2η : 0 ≤ 2 * η := le_trans hsum hη
        linarith only [h2η]
      linarith only [hb, hη0]
    have hfix : (e₂ ⟨x, hmem⟩).1 = x := (hrel x hx_global hmem).1
    have hH : h (Handle.lower φ ⟨x, hx⟩) = ⟨x, hmem⟩ := by
      apply Subtype.ext
      exact hlower
    change (e (Handle.lower φ ⟨x, hx⟩)).1 = x
    rw [hcomm (Handle.lower φ ⟨x, hx⟩)]
    rw [hH]
    exact hfix
  · intro y hy_global hy z hz
    have hmem : morseRoundedFunction hk c ε r δ R₀ R₁ data y ≤ c := by
      have hb := morseSublevelIsotopyFamily_le_neg_eta_of_deep hk c ε r δ R₀ R₁ R₁' η data
        (le_of_lt hε) hδ hR₁₂ hR₁₂R hη hy_global 0 (by norm_num)
      have hF0 : morseSublevelIsotopyFamily hk c ε r δ R₀ R₁ data 0 y =
          morseRoundedFunction hk c ε r δ R₀ R₁ data y - c := by
        dsimp [morseSublevelIsotopyFamily]
        ring
      rw [hF0] at hb
      have hsum : 0 ≤ r ^ 2 + δ := by positivity
      have hη0 : 0 ≤ η := by
        have h2η : 0 ≤ 2 * η := le_trans hsum hη
        linarith only [h2η]
      linarith only [hb, hη0]
    have hfix : (e₂.symm ⟨y, hy⟩).1 = y := (hrel y hy_global hmem).2 hy
    have hmem_lower : f y ≤ c - ε := by
      have hsum : 0 ≤ r ^ 2 + δ := by positivity
      have hη0 : 0 ≤ η := by
        have h2η : 0 ≤ 2 * η := le_trans hsum hη
        linarith only [h2η]
      linarith only [hy_global, hη0]
    have hsymm : h.symm ⟨y, hmem⟩ = Handle.lower φ ⟨y, hmem_lower⟩ := by
      dsimp [φ]
      exact morseHandleAdjunctionEquivRoundedSublevel_symm_rel_deep hk c ε r δ R₀ R₁ η data
        hε hδ hδr hr hεr' hbigR hR hR0 hbig hRbig hR₁big hR₁₂R₀ hcont hη hy_global hmem
    have hfix' : e₂.symm ⟨y, hy⟩ = ⟨y, hmem⟩ := by
      apply Subtype.ext
      exact hfix
    have heq : h.symm (e₂.symm ⟨y, hy⟩) = Handle.lower φ ⟨y, hmem_lower⟩ := by
      rw [hfix']
      exact hsymm
    have hz' : e₂ (h z) = ⟨y, hy⟩ := by
      change e₂ (h z) = ⟨y, hy⟩
      simpa [e] using hz
    have hz'' : h z = ⟨y, hmem⟩ := by
      calc
        h z = e₂.symm (e₂ (h z)) := by simp
        _ = e₂.symm ⟨y, hy⟩ := by rw [hz']
        _ = ⟨y, hmem⟩ := hfix'
    have hfinal : z = Handle.lower φ ⟨y, hmem_lower⟩ := by
      calc
        z = h.symm (h z) := (h.symm_apply_apply z).symm
        _ = h.symm ⟨y, hmem⟩ := by rw [hz'']
        _ = Handle.lower φ ⟨y, hmem_lower⟩ := hsymm
    exact hfinal.trans (congrArg (Handle.lower φ) (by
      apply Subtype.ext
      rfl))

end

end DifferentialGeometry.Topology.Morse
