import DifferentialGeometry.Analysis.Parabolic.Euclidean.LowerOrder
import DifferentialGeometry.Analysis.Schauder.CompactRegularity

noncomputable section

open Matrix Real Set
open scoped NNReal RealInnerProductSpace

namespace DifferentialGeometry.Analysis.Parabolic.Euclidean

open DifferentialGeometry.Analysis.Schauder

private abbrev Euc (n : Type*) := EuclideanSpace Real n

variable {n : Type*} [Fintype n] [DecidableEq n]

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
