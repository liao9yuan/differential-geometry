import DifferentialGeometry.Analysis.Parabolic.Euclidean.LowerOrder
import DifferentialGeometry.Analysis.Schauder.CompactRegularity
import DifferentialGeometry.Analysis.Schauder.ParabolicBallRetraction

noncomputable section

open Matrix Real Set
open scoped NNReal RealInnerProductSpace

namespace DifferentialGeometry.Analysis.Parabolic.Euclidean

open DifferentialGeometry.Analysis.Schauder

private abbrev Euc (n : Type*) := EuclideanSpace Real n

variable {n : Type*} [Fintype n] [DecidableEq n]

def parabolicMatrixCoefficientRescaleExtension
    (tau R : Real) (rho : NNReal) (p0 : ParabolicPoint (Euc n))
    (principal : n → n → ParabolicPoint (Euc n) → Real) :
    n → n → ParabolicPoint (Euc n) → Real :=
  fun i j ↦ parabolicTimeCenteredBallRetractionExtension tau R
    (parabolicMatrixCoefficientRescale rho p0 principal i j)

def parabolicDriftCoefficientRescaleExtension
    (tau R : Real) (rho : NNReal) (p0 : ParabolicPoint (Euc n))
    (drift : n → ParabolicPoint (Euc n) → Real) :
    n → ParabolicPoint (Euc n) → Real :=
  fun i ↦ parabolicTimeCenteredBallRetractionExtension tau R
    (parabolicDriftCoefficientRescale rho p0 drift i)

def parabolicPotentialCoefficientRescaleExtension
    (tau R : Real) (rho : NNReal) (p0 : ParabolicPoint (Euc n))
    (potential : ParabolicPoint (Euc n) → Real) :
    ParabolicPoint (Euc n) → Real :=
  parabolicTimeCenteredBallRetractionExtension tau R
    (parabolicPotentialCoefficientRescale rho p0 potential)

omit [DecidableEq n] in
@[simp]
theorem parabolicMatrixCoefficientRescaleExtension_apply
    (tau R : Real) (rho : NNReal) (p0 : ParabolicPoint (Euc n))
    (principal : n → n → ParabolicPoint (Euc n) → Real)
    (i j : n) (p : ParabolicPoint (Euc n)) :
    parabolicMatrixCoefficientRescaleExtension
        tau R rho p0 principal i j p =
      parabolicMatrixCoefficientRescale rho p0 principal i j
        (parabolicTimeCenteredBallRetraction tau R p) :=
  rfl

omit [DecidableEq n] in
@[simp]
theorem parabolicDriftCoefficientRescaleExtension_apply
    (tau R : Real) (rho : NNReal) (p0 : ParabolicPoint (Euc n))
    (drift : n → ParabolicPoint (Euc n) → Real)
    (i : n) (p : ParabolicPoint (Euc n)) :
    parabolicDriftCoefficientRescaleExtension tau R rho p0 drift i p =
      parabolicDriftCoefficientRescale rho p0 drift i
        (parabolicTimeCenteredBallRetraction tau R p) :=
  rfl

omit [DecidableEq n] in
@[simp]
theorem parabolicPotentialCoefficientRescaleExtension_apply
    (tau R : Real) (rho : NNReal) (p0 : ParabolicPoint (Euc n))
    (potential : ParabolicPoint (Euc n) → Real)
    (p : ParabolicPoint (Euc n)) :
    parabolicPotentialCoefficientRescaleExtension
        tau R rho p0 potential p =
      parabolicPotentialCoefficientRescale rho p0 potential
        (parabolicTimeCenteredBallRetraction tau R p) :=
  rfl

omit [DecidableEq n] in
theorem parabolicMatrixCoefficientRescaleExtension_eq_of_mem_closedBall
    (tau : Real) {R : Real} (rho : NNReal)
    (p0 : ParabolicPoint (Euc n))
    (principal : n → n → ParabolicPoint (Euc n) → Real)
    (i j : n) {p : ParabolicPoint (Euc n)}
    (hp : p.space ∈ Metric.closedBall (0 : Euc n) R) :
    parabolicMatrixCoefficientRescaleExtension
        tau R rho p0 principal i j p =
      parabolicMatrixCoefficientRescale rho p0 principal i j
        (parabolicPoint (p.time - tau) p.space) := by
  exact parabolicTimeCenteredBallRetractionExtension_eq_of_mem_closedBall
    tau _ hp

omit [DecidableEq n] in
theorem parabolicDriftCoefficientRescaleExtension_eq_of_mem_closedBall
    (tau : Real) {R : Real} (rho : NNReal)
    (p0 : ParabolicPoint (Euc n))
    (drift : n → ParabolicPoint (Euc n) → Real)
    (i : n) {p : ParabolicPoint (Euc n)}
    (hp : p.space ∈ Metric.closedBall (0 : Euc n) R) :
    parabolicDriftCoefficientRescaleExtension tau R rho p0 drift i p =
      parabolicDriftCoefficientRescale rho p0 drift i
        (parabolicPoint (p.time - tau) p.space) := by
  exact parabolicTimeCenteredBallRetractionExtension_eq_of_mem_closedBall
    tau _ hp

omit [DecidableEq n] in
theorem parabolicPotentialCoefficientRescaleExtension_eq_of_mem_closedBall
    (tau : Real) {R : Real} (rho : NNReal)
    (p0 : ParabolicPoint (Euc n))
    (potential : ParabolicPoint (Euc n) → Real)
    {p : ParabolicPoint (Euc n)}
    (hp : p.space ∈ Metric.closedBall (0 : Euc n) R) :
    parabolicPotentialCoefficientRescaleExtension
        tau R rho p0 potential p =
      parabolicPotentialCoefficientRescale rho p0 potential
        (parabolicPoint (p.time - tau) p.space) := by
  exact parabolicTimeCenteredBallRetractionExtension_eq_of_mem_closedBall
    tau _ hp

def IsParabolicNondivergenceSchauderScale
    (principal : n → n → ParabolicPoint (Euc n) → Real)
    (drift : n → ParabolicPoint (Euc n) → Real)
    (potential : ParabolicPoint (Euc n) → Real)
    (p : ParabolicPoint (Euc n))
    (hA : (Matrix.of fun i j ↦ principal i j p).PosDef)
    (alpha : NNReal) (Ka : n → n → NNReal)
    (Kb Bb : n → NNReal) (Kc Bc : NNReal)
    (maxRadius T : Real) (rho : NNReal) : Prop :=
  0 < rho ∧ rho ≤ 1 ∧ (rho : Real) ≤ maxRadius ∧
  (∀ i j, HolderWith (Ka i j * rho ^ (alpha : Real)) alpha
    ((Metric.ball (parabolicPoint 0 0) 1).restrict
      (parabolicMatrixCoefficientRescale rho p principal i j))) ∧
  (∀ i j q, q ∈ Metric.ball (parabolicPoint 0 0) 1 →
    ‖principal i j p -
        parabolicMatrixCoefficientRescale rho p principal i j q‖ ≤
      Ka i j * rho ^ (alpha : Real)) ∧
  (∀ i, HolderWith (Kb i * rho ^ (alpha : Real) * rho) alpha
    ((Metric.ball (parabolicPoint 0 0) 1).restrict
      (parabolicDriftCoefficientRescale rho p drift i))) ∧
  (∀ i q, q ∈ Metric.ball (parabolicPoint 0 0) 1 →
    ‖parabolicDriftCoefficientRescale rho p drift i q‖ ≤ rho * Bb i) ∧
  HolderWith (Kc * rho ^ (alpha : Real) * rho ^ 2) alpha
    ((Metric.ball (parabolicPoint 0 0) 1).restrict
      (parabolicPotentialCoefficientRescale rho p potential)) ∧
  (∀ q, q ∈ Metric.ball (parabolicPoint 0 0) 1 →
    ‖parabolicPotentialCoefficientRescale rho p potential q‖ ≤ rho ^ 2 * Bc) ∧
  spdParabolicSchauderDefectConst
    (Matrix.of fun i j ↦ principal i j p) hA alpha
    (fun i j ↦ Ka i j * rho ^ (alpha : Real))
    (fun i j ↦ Ka i j * rho ^ (alpha : Real)) T < 1

theorem exists_parabolicNondivergenceCoefficientRescaleExtension_schauder_bounds
    (principal : n → n → ParabolicPoint (Euc n) → Real)
    (drift : n → ParabolicPoint (Euc n) → Real)
    (potential : ParabolicPoint (Euc n) → Real)
    (p : ParabolicPoint (Euc n))
    (hA : (Matrix.of fun i j ↦ principal i j p).PosDef)
    (alpha : NNReal) (Ka : n → n → NNReal)
    (Kb Bb : n → NNReal) (Kc Bc : NNReal)
    (maxRadius T : Real) (rho : NNReal)
    (hscale : IsParabolicNondivergenceSchauderScale
      principal drift potential p hA alpha Ka Kb Bb Kc Bc
        maxRadius T rho)
    (tau : Real) {J : Set Real} {R : Real}
    (hR : 0 ≤ R) (hRone : R < 1)
    (htime : ∀ t ∈ J, |t - tau| ^ (1 / 2 : Real) < 1) :
    ∃ hAext : (Matrix.of fun i j ↦
        parabolicMatrixCoefficientRescaleExtension
          tau R rho p principal i j (parabolicPoint tau 0)).PosDef,
      (∀ i j, HolderWith (Ka i j * rho ^ (alpha : Real)) alpha
        ((parabolicCylinder J Set.univ).restrict
          (parabolicMatrixCoefficientRescaleExtension
            tau R rho p principal i j))) ∧
      (∀ i j q, q ∈ parabolicCylinder J Set.univ →
        ‖parabolicMatrixCoefficientRescaleExtension
              tau R rho p principal i j (parabolicPoint tau 0) -
            parabolicMatrixCoefficientRescaleExtension
              tau R rho p principal i j q‖ ≤
          Ka i j * rho ^ (alpha : Real)) ∧
      (∀ i j q, q ∈ parabolicCylinder J Set.univ →
        ‖parabolicMatrixCoefficientRescaleExtension
            tau R rho p principal i j q‖ ≤
          ‖principal i j p‖₊ + Ka i j * rho ^ (alpha : Real)) ∧
      (∀ i, HolderWith (Kb i * rho ^ (alpha : Real) * rho) alpha
        ((parabolicCylinder J Set.univ).restrict
          (parabolicDriftCoefficientRescaleExtension
            tau R rho p drift i))) ∧
      (∀ i q, q ∈ parabolicCylinder J Set.univ →
        ‖parabolicDriftCoefficientRescaleExtension
            tau R rho p drift i q‖ ≤ rho * Bb i) ∧
      HolderWith (Kc * rho ^ (alpha : Real) * rho ^ 2) alpha
        ((parabolicCylinder J Set.univ).restrict
          (parabolicPotentialCoefficientRescaleExtension
            tau R rho p potential)) ∧
      (∀ q, q ∈ parabolicCylinder J Set.univ →
        ‖parabolicPotentialCoefficientRescaleExtension
            tau R rho p potential q‖ ≤ rho ^ 2 * Bc) ∧
      spdParabolicSchauderDefectConst
        (Matrix.of fun i j ↦
          parabolicMatrixCoefficientRescaleExtension
            tau R rho p principal i j (parabolicPoint tau 0))
        hAext alpha
        (fun i j ↦ Ka i j * rho ^ (alpha : Real))
        (fun i j ↦ Ka i j * rho ^ (alpha : Real)) T < 1 := by
  rcases hscale with ⟨hrho, hrhoOne, hrhoMax, ha, homega,
    hb, hbNorm, hc, hcNorm, hsmall⟩
  have hcenter : ∀ i j,
      parabolicMatrixCoefficientRescaleExtension
          tau R rho p principal i j (parabolicPoint tau 0) =
        principal i j p := by
    intro i j
    simp [parabolicMatrixCoefficientRescaleExtension,
      parabolicTimeCenteredBallRetractionExtension,
      parabolicTimeCenteredBallRetraction, ballRetraction]
  have hAext : (Matrix.of fun i j ↦
      parabolicMatrixCoefficientRescaleExtension
        tau R rho p principal i j (parabolicPoint tau 0)).PosDef := by
    simpa only [hcenter] using hA
  refine ⟨hAext, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i j
    simpa only [parabolicMatrixCoefficientRescaleExtension] using
      parabolicTimeCenteredBallRetractionExtension_holderWith
        tau hR hRone htime
        (parabolicMatrixCoefficientRescale rho p principal i j) (ha i j)
  · intro i j q hq
    rw [hcenter]
    exact norm_sub_parabolicTimeCenteredBallRetractionExtension_le
      (omega := Ka i j * rho ^ (alpha : Real))
      tau hR hRone htime (principal i j p)
      (parabolicMatrixCoefficientRescale rho p principal i j)
      (homega i j) q hq
  · intro i j q hq
    have hoscillation :=
      norm_sub_parabolicTimeCenteredBallRetractionExtension_le
        (omega := Ka i j * rho ^ (alpha : Real))
        tau hR hRone htime (principal i j p)
        (parabolicMatrixCoefficientRescale rho p principal i j)
        (homega i j) q hq
    have hoscillation' :
        ‖principal i j p -
          parabolicMatrixCoefficientRescaleExtension
            tau R rho p principal i j q‖ ≤
          Ka i j * rho ^ (alpha : Real) := by
      simpa only [parabolicMatrixCoefficientRescaleExtension] using
        hoscillation
    calc
      ‖parabolicMatrixCoefficientRescaleExtension
          tau R rho p principal i j q‖ ≤
          ‖principal i j p‖ +
            ‖principal i j p -
              parabolicMatrixCoefficientRescaleExtension
                tau R rho p principal i j q‖ :=
        norm_le_norm_add_norm_sub _ _
      _ ≤ ‖principal i j p‖ +
          (Ka i j * rho ^ (alpha : Real) : NNReal) :=
        by
          simpa only [NNReal.coe_mul, NNReal.coe_rpow] using
            add_le_add (le_refl ‖principal i j p‖) hoscillation'
      _ = (‖principal i j p‖₊ +
          Ka i j * rho ^ (alpha : Real) : NNReal) := by
        simp only [NNReal.coe_add, coe_nnnorm]
  · intro i
    simpa only [parabolicDriftCoefficientRescaleExtension] using
      parabolicTimeCenteredBallRetractionExtension_holderWith
        tau hR hRone htime
        (parabolicDriftCoefficientRescale rho p drift i) (hb i)
  · intro i q hq
    exact norm_parabolicTimeCenteredBallRetractionExtension_le
      (B := rho * Bb i) tau hR hRone htime
      (parabolicDriftCoefficientRescale rho p drift i) (hbNorm i) q hq
  · simpa only [parabolicPotentialCoefficientRescaleExtension] using
      parabolicTimeCenteredBallRetractionExtension_holderWith
        tau hR hRone htime
        (parabolicPotentialCoefficientRescale rho p potential) hc
  · intro q hq
    have hcNorm' : ∀ z,
        z ∈ Metric.ball (parabolicPoint 0 0) 1 →
          ‖parabolicPotentialCoefficientRescale rho p potential z‖ ≤
            (rho ^ 2 * Bc : NNReal) := by
      intro z hz
      simpa only [NNReal.coe_mul, NNReal.coe_pow] using hcNorm z hz
    exact norm_parabolicTimeCenteredBallRetractionExtension_le
      (B := rho ^ 2 * Bc) tau hR hRone htime
      (parabolicPotentialCoefficientRescale rho p potential) hcNorm' q hq
  · simpa only [hcenter] using hsmall

theorem exists_finite_parabolicNondivergence_schauder_cover
    (principal : n → n → ParabolicPoint (Euc n) → Real)
    (drift : n → ParabolicPoint (Euc n) → Real)
    (potential : ParabolicPoint (Euc n) → Real)
    {a t₀ t₁ b r R : Real}
    (hat₀ : a < t₀) (ht₁b : t₁ < b) (hrR : r < R)
    (center : Euc n)
    (hpos : ∀ p,
      p ∈ parabolicCylinder (Set.Icc t₀ t₁) (Metric.closedBall center r) →
        (Matrix.of fun i j ↦ principal i j p).PosDef)
    (alpha : NNReal) (halpha : 0 < alpha)
    (Ka : n → n → NNReal) (Kb Bb : n → NNReal) (Kc Bc : NNReal)
    (T : Real)
    (ha : ∀ i j, HolderWith (Ka i j) alpha
      ((parabolicCylinder (Set.Icc a b) (Metric.closedBall center R)).restrict
        (principal i j)))
    (hb : ∀ i, HolderWith (Kb i) alpha
      ((parabolicCylinder (Set.Icc a b) (Metric.closedBall center R)).restrict
        (drift i)))
    (hc : HolderWith Kc alpha
      ((parabolicCylinder (Set.Icc a b) (Metric.closedBall center R)).restrict
        potential))
    (hbNorm : ∀ i p,
      p ∈ parabolicCylinder (Set.Icc a b) (Metric.closedBall center R) →
        ‖drift i p‖ ≤ Bb i)
    (hcNorm : ∀ p,
      p ∈ parabolicCylinder (Set.Icc a b) (Metric.closedBall center R) →
        ‖potential p‖ ≤ Bc) :
    ∃ localScale : ∀ p : ↥(parabolicCylinder (Set.Icc t₀ t₁)
        (Metric.closedBall center r)),
      {rho : NNReal //
        IsParabolicNondivergenceSchauderScale principal drift potential p.1
          (hpos p.1 p.2) alpha Ka Kb Bb Kc Bc
          (parabolicInteriorRadius a t₀ t₁ b r R) T rho},
      ∃ s : Finset ↥(parabolicCylinder (Set.Icc t₀ t₁)
          (Metric.closedBall center r)),
        parabolicCylinder (Set.Icc t₀ t₁) (Metric.closedBall center r) ⊆
          ⋃ p ∈ s, Metric.ball p.1 ((localScale p).1 : Real) := by
  let Q := parabolicCylinder (Set.Icc t₀ t₁) (Metric.closedBall center r)
  have hpoint : ∀ p : Q, ∃ rho : NNReal,
      IsParabolicNondivergenceSchauderScale principal drift potential p.1
        (hpos p.1 p.2) alpha Ka Kb Bb Kc Bc
        (parabolicInteriorRadius a t₀ t₁ b r R) T rho := by
    intro p
    simpa only [IsParabolicNondivergenceSchauderScale] using
      exists_parabolicNondivergenceCoefficientRescale_schauder_bounds_of_holderWith_on_parabolicCylinder
        principal drift potential hat₀ ht₁b hrR p.2 (hpos p.1 p.2)
        alpha halpha Ka Kb Bb Kc Bc T ha hb hc hbNorm hcNorm
  choose rho hrho using hpoint
  let localScale : ∀ p : Q, {rho : NNReal //
      IsParabolicNondivergenceSchauderScale principal drift potential p.1
        (hpos p.1 p.2) alpha Ka Kb Bb Kc Bc
        (parabolicInteriorRadius a t₀ t₁ b r R) T rho} :=
    fun p ↦ ⟨rho p, hrho p⟩
  have hcompact : IsCompact Q :=
    isCompact_parabolicCylinder_Icc t₀ t₁ (isCompact_closedBall center r)
  obtain ⟨s, hs⟩ := exists_finite_ball_cover_of_isCompact hcompact
    (fun p : Q ↦ ((localScale p).1 : Real))
    (fun p ↦ by exact_mod_cast (localScale p).2.1)
  exact ⟨localScale, s, hs⟩

theorem exists_finite_buffered_parabolicNondivergence_schauder_cover
    (principal : n → n → ParabolicPoint (Euc n) → Real)
    (drift : n → ParabolicPoint (Euc n) → Real)
    (potential : ParabolicPoint (Euc n) → Real)
    {a t₀ t₁ b r R : Real}
    (hat₀ : a < t₀) (ht₁b : t₁ < b) (hrR : r < R)
    (center : Euc n)
    (hpos : ∀ p,
      p ∈ parabolicCylinder (Set.Icc t₀ t₁) (Metric.closedBall center r) →
        (Matrix.of fun i j ↦ principal i j p).PosDef)
    (alpha : NNReal) (halpha : 0 < alpha)
    (Ka : n → n → NNReal) (Kb Bb : n → NNReal) (Kc Bc : NNReal)
    (T : Real) (theta : NNReal) (htheta : 0 < theta)
    (ha : ∀ i j, HolderWith (Ka i j) alpha
      ((parabolicCylinder (Set.Icc a b) (Metric.closedBall center R)).restrict
        (principal i j)))
    (hb : ∀ i, HolderWith (Kb i) alpha
      ((parabolicCylinder (Set.Icc a b) (Metric.closedBall center R)).restrict
        (drift i)))
    (hc : HolderWith Kc alpha
      ((parabolicCylinder (Set.Icc a b) (Metric.closedBall center R)).restrict
        potential))
    (hbNorm : ∀ i p,
      p ∈ parabolicCylinder (Set.Icc a b) (Metric.closedBall center R) →
        ‖drift i p‖ ≤ Bb i)
    (hcNorm : ∀ p,
      p ∈ parabolicCylinder (Set.Icc a b) (Metric.closedBall center R) →
        ‖potential p‖ ≤ Bc) :
    ∃ localScale : ∀ p : ↥(parabolicCylinder (Set.Icc t₀ t₁)
        (Metric.closedBall center r)),
      {rho : NNReal //
        IsParabolicNondivergenceSchauderScale principal drift potential p.1
          (hpos p.1 p.2) alpha Ka Kb Bb Kc Bc
          (parabolicInteriorRadius a t₀ t₁ b r R) T rho},
        ∃ s : Finset ↥(parabolicCylinder (Set.Icc t₀ t₁)
          (Metric.closedBall center r)),
        ∃ delta : NNReal, 0 < delta ∧
          (∀ p ∈ s, (delta : Real) ≤
            (theta : Real) * ((localScale p).1 : Real)) ∧
          parabolicCylinder (Set.Icc t₀ t₁) (Metric.closedBall center r) ⊆
            ⋃ p ∈ s, Metric.ball p.1
              ((theta : Real) * ((localScale p).1 : Real)) := by
  obtain ⟨localScale, _⟩ :=
    exists_finite_parabolicNondivergence_schauder_cover
      principal drift potential hat₀ ht₁b hrR center hpos alpha halpha
        Ka Kb Bb Kc Bc T ha hb hc hbNorm hcNorm
  let Q := parabolicCylinder (Set.Icc t₀ t₁) (Metric.closedBall center r)
  have hcompact : IsCompact Q :=
    isCompact_parabolicCylinder_Icc t₀ t₁ (isCompact_closedBall center r)
  obtain ⟨s, delta, hdelta, hdeltaLe, hs⟩ :=
    exists_finite_buffered_ball_cover_of_isCompact hcompact
      (fun p : Q ↦ ((localScale p).1 : Real))
      (fun p ↦ by exact_mod_cast (localScale p).2.1) theta htheta
  exact ⟨localScale, s, delta, hdelta, hdeltaLe, hs⟩

theorem exists_parabolicNondivergence_schauder_estimate_of_local_scaledBall_estimates
    {F : Type*} [NormedAddCommGroup F] [NormedSpace Real F]
    (principal : n → n → ParabolicPoint (Euc n) → Real)
    (drift : n → ParabolicPoint (Euc n) → Real)
    (potential : ParabolicPoint (Euc n) → Real)
    {a t₀ t₁ b r R : Real}
    (hat₀ : a < t₀) (ht₁b : t₁ < b) (hrR : r < R)
    (center : Euc n)
    (hpos : ∀ p,
      p ∈ parabolicCylinder (Set.Icc t₀ t₁) (Metric.closedBall center r) →
        (Matrix.of fun i j ↦ principal i j p).PosDef)
    (alpha : NNReal) (halpha : 0 < alpha)
    (Ka : n → n → NNReal) (Kb Bb : n → NNReal) (Kc Bc : NNReal)
    (T : Real)
    (ha : ∀ i j, HolderWith (Ka i j) alpha
      ((parabolicCylinder (Set.Icc a b) (Metric.closedBall center R)).restrict
        (principal i j)))
    (hb : ∀ i, HolderWith (Kb i) alpha
      ((parabolicCylinder (Set.Icc a b) (Metric.closedBall center R)).restrict
        (drift i)))
    (hc : HolderWith Kc alpha
      ((parabolicCylinder (Set.Icc a b) (Metric.closedBall center R)).restrict
        potential))
    (hbNorm : ∀ i p,
      p ∈ parabolicCylinder (Set.Icc a b) (Metric.closedBall center R) →
        ‖drift i p‖ ≤ Bb i)
    (hcNorm : ∀ p,
      p ∈ parabolicCylinder (Set.Icc a b) (Metric.closedBall center R) →
        ‖potential p‖ ≤ Bc)
    (innerRadius : NNReal) (hinnerRadius : 0 < innerRadius)
    (u : Real → Euc n → F) (hspace : ∀ t, ContDiff Real 2 (u t))
    (localBound : ↥(parabolicCylinder (Set.Icc t₀ t₁)
      (Metric.closedBall center r)) → NNReal → NNReal)
    (hlocal : ∀ p : ↥(parabolicCylinder (Set.Icc t₀ t₁)
        (Metric.closedBall center r)), ∀ rho : NNReal,
      IsParabolicNondivergenceSchauderScale principal drift potential p.1
        (hpos p.1 p.2) alpha Ka Kb Bb Kc Bc
        (parabolicInteriorRadius a t₀ t₁ b r R) T rho →
      eParabolicC2HolderGaugeOn alpha
        (Metric.ball (parabolicPoint 0 0) (innerRadius : Real))
        (parabolicRescaleAt rho p.1 u) ≤ localBound p rho) :
    ∃ localScale : ∀ p : ↥(parabolicCylinder (Set.Icc t₀ t₁)
        (Metric.closedBall center r)),
      {rho : NNReal //
        IsParabolicNondivergenceSchauderScale principal drift potential p.1
          (hpos p.1 p.2) alpha Ka Kb Bb Kc Bc
          (parabolicInteriorRadius a t₀ t₁ b r R) T rho},
      ∃ s : Finset ↥(parabolicCylinder (Set.Icc t₀ t₁)
          (Metric.closedBall center r)),
        ∃ delta : NNReal, 0 < delta ∧
          (∀ p ∈ s, (delta : Real) ≤
            (((localScale p).1 : Real) * (innerRadius : Real)) / 2) ∧
          parabolicCylinder (Set.Icc t₀ t₁) (Metric.closedBall center r) ⊆
            ⋃ p ∈ s, Metric.ball p.1
              ((((localScale p).1 : Real) * (innerRadius : Real)) / 2) ∧
          eParabolicC2HolderGaugeOn alpha
              (parabolicCylinder (Set.Icc t₀ t₁)
                (Metric.closedBall center r)) u ≤
            bufferedParabolicC2HolderGaugeConst alpha
              (∑ p ∈ s, parabolicC2HolderRescaleConst
                (localScale p).1⁻¹ alpha (localBound p (localScale p).1))
              delta := by
  let theta : NNReal := innerRadius / 2
  have htheta : 0 < theta := div_pos hinnerRadius (by norm_num)
  obtain ⟨localScale, s, delta, hdelta, hdeltaLe, hcover⟩ :=
    exists_finite_buffered_parabolicNondivergence_schauder_cover
      principal drift potential hat₀ ht₁b hrR center hpos alpha halpha
        Ka Kb Bb Kc Bc T theta htheta ha hb hc hbNorm hcNorm
  have hbuffer : ∀ p ∈ s, (delta : Real) ≤
      (((localScale p).1 : Real) * (innerRadius : Real)) / 2 := by
    intro p hp
    calc
      (delta : Real) ≤ (theta : Real) * ((localScale p).1 : Real) :=
        hdeltaLe p hp
      _ = (((localScale p).1 : Real) * (innerRadius : Real)) / 2 := by
        simp only [theta, NNReal.coe_div, NNReal.coe_ofNat]
        ring
  have hcover' :
      parabolicCylinder (Set.Icc t₀ t₁) (Metric.closedBall center r) ⊆
        ⋃ p ∈ s, Metric.ball p.1
          ((((localScale p).1 : Real) * (innerRadius : Real)) / 2) := by
    intro q hq
    rcases Set.mem_iUnion₂.mp (hcover hq) with ⟨p, hp, hqp⟩
    apply Set.mem_iUnion₂.mpr
    refine ⟨p, hp, ?_⟩
    simpa only [theta, NNReal.coe_div, NNReal.coe_ofNat,
      show (innerRadius : Real) / 2 * ((localScale p).1 : Real) =
        ((localScale p).1 : Real) * (innerRadius : Real) / 2 by ring] using hqp
  have hglobal :=
    eParabolicC2HolderGaugeOn_le_of_finite_buffered_scaledBall_rescaleAt
      hdelta s (fun p ↦ p.1) (fun p ↦ (localScale p).1)
        (fun _ ↦ (innerRadius : Real))
        (fun p _ ↦ (localScale p).2.1) hbuffer hcover' u hspace
        (fun p ↦ localBound p (localScale p).1)
        (fun p _ ↦ hlocal p (localScale p).1 (localScale p).2)
  exact ⟨localScale, s, delta, hdelta, hbuffer, hcover', hglobal⟩

end DifferentialGeometry.Analysis.Parabolic.Euclidean

end
