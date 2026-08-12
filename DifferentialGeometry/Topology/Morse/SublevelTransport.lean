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

end

end DifferentialGeometry.Topology.Morse
