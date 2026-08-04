import DifferentialGeometry.Analysis.Parabolic.Euclidean.LowerOrder
import DifferentialGeometry.Analysis.Schauder.CompactRegularity

noncomputable section

open Matrix Real Set
open scoped NNReal RealInnerProductSpace

namespace DifferentialGeometry.Analysis.Parabolic.Euclidean

open DifferentialGeometry.Analysis.Schauder

private abbrev Euc (n : Type*) := EuclideanSpace Real n

variable {n : Type*} [Fintype n] [DecidableEq n]

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
        0 < rho ∧ rho ≤ 1 ∧
        (rho : Real) ≤ parabolicInteriorRadius a t₀ t₁ b r R ∧
        (∀ i j, HolderWith (Ka i j * rho ^ (alpha : Real)) alpha
          ((Metric.ball (parabolicPoint 0 0) 1).restrict
            (parabolicMatrixCoefficientRescale rho p.1 principal i j))) ∧
        (∀ i j q, q ∈ Metric.ball (parabolicPoint 0 0) 1 →
          ‖principal i j p.1 -
              parabolicMatrixCoefficientRescale rho p.1 principal i j q‖ ≤
            Ka i j * rho ^ (alpha : Real)) ∧
        (∀ i, HolderWith (Kb i * rho ^ (alpha : Real) * rho) alpha
          ((Metric.ball (parabolicPoint 0 0) 1).restrict
            (parabolicDriftCoefficientRescale rho p.1 drift i))) ∧
        (∀ i q, q ∈ Metric.ball (parabolicPoint 0 0) 1 →
          ‖parabolicDriftCoefficientRescale rho p.1 drift i q‖ ≤
            rho * Bb i) ∧
        HolderWith (Kc * rho ^ (alpha : Real) * rho ^ 2) alpha
          ((Metric.ball (parabolicPoint 0 0) 1).restrict
            (parabolicPotentialCoefficientRescale rho p.1 potential)) ∧
        (∀ q, q ∈ Metric.ball (parabolicPoint 0 0) 1 →
          ‖parabolicPotentialCoefficientRescale rho p.1 potential q‖ ≤
            rho ^ 2 * Bc) ∧
        spdParabolicSchauderDefectConst
          (Matrix.of fun i j ↦ principal i j p.1) (hpos p.1 p.2) alpha
          (fun i j ↦ Ka i j * rho ^ (alpha : Real))
          (fun i j ↦ Ka i j * rho ^ (alpha : Real)) T < 1},
      ∃ s : Finset ↥(parabolicCylinder (Set.Icc t₀ t₁)
          (Metric.closedBall center r)),
        parabolicCylinder (Set.Icc t₀ t₁) (Metric.closedBall center r) ⊆
          ⋃ p ∈ s, Metric.ball p.1 ((localScale p).1 : Real) := by
  let Q := parabolicCylinder (Set.Icc t₀ t₁) (Metric.closedBall center r)
  have hpoint : ∀ p : Q, ∃ rho : NNReal,
      0 < rho ∧ rho ≤ 1 ∧
      (rho : Real) ≤ parabolicInteriorRadius a t₀ t₁ b r R ∧
      (∀ i j, HolderWith (Ka i j * rho ^ (alpha : Real)) alpha
        ((Metric.ball (parabolicPoint 0 0) 1).restrict
          (parabolicMatrixCoefficientRescale rho p.1 principal i j))) ∧
      (∀ i j q, q ∈ Metric.ball (parabolicPoint 0 0) 1 →
        ‖principal i j p.1 -
            parabolicMatrixCoefficientRescale rho p.1 principal i j q‖ ≤
          Ka i j * rho ^ (alpha : Real)) ∧
      (∀ i, HolderWith (Kb i * rho ^ (alpha : Real) * rho) alpha
        ((Metric.ball (parabolicPoint 0 0) 1).restrict
          (parabolicDriftCoefficientRescale rho p.1 drift i))) ∧
      (∀ i q, q ∈ Metric.ball (parabolicPoint 0 0) 1 →
        ‖parabolicDriftCoefficientRescale rho p.1 drift i q‖ ≤
          rho * Bb i) ∧
      HolderWith (Kc * rho ^ (alpha : Real) * rho ^ 2) alpha
        ((Metric.ball (parabolicPoint 0 0) 1).restrict
          (parabolicPotentialCoefficientRescale rho p.1 potential)) ∧
      (∀ q, q ∈ Metric.ball (parabolicPoint 0 0) 1 →
        ‖parabolicPotentialCoefficientRescale rho p.1 potential q‖ ≤
          rho ^ 2 * Bc) ∧
      spdParabolicSchauderDefectConst
        (Matrix.of fun i j ↦ principal i j p.1) (hpos p.1 p.2) alpha
        (fun i j ↦ Ka i j * rho ^ (alpha : Real))
        (fun i j ↦ Ka i j * rho ^ (alpha : Real)) T < 1 := by
    intro p
    exact exists_parabolicNondivergenceCoefficientRescale_schauder_bounds_of_holderWith_on_parabolicCylinder
      principal drift potential hat₀ ht₁b hrR p.2 (hpos p.1 p.2)
      alpha halpha Ka Kb Bb Kc Bc T ha hb hc hbNorm hcNorm
  choose rho hrho using hpoint
  let localScale : ∀ p : Q, {rho : NNReal //
      0 < rho ∧ rho ≤ 1 ∧
      (rho : Real) ≤ parabolicInteriorRadius a t₀ t₁ b r R ∧
      (∀ i j, HolderWith (Ka i j * rho ^ (alpha : Real)) alpha
        ((Metric.ball (parabolicPoint 0 0) 1).restrict
          (parabolicMatrixCoefficientRescale rho p.1 principal i j))) ∧
      (∀ i j q, q ∈ Metric.ball (parabolicPoint 0 0) 1 →
        ‖principal i j p.1 -
            parabolicMatrixCoefficientRescale rho p.1 principal i j q‖ ≤
          Ka i j * rho ^ (alpha : Real)) ∧
      (∀ i, HolderWith (Kb i * rho ^ (alpha : Real) * rho) alpha
        ((Metric.ball (parabolicPoint 0 0) 1).restrict
          (parabolicDriftCoefficientRescale rho p.1 drift i))) ∧
      (∀ i q, q ∈ Metric.ball (parabolicPoint 0 0) 1 →
        ‖parabolicDriftCoefficientRescale rho p.1 drift i q‖ ≤
          rho * Bb i) ∧
      HolderWith (Kc * rho ^ (alpha : Real) * rho ^ 2) alpha
        ((Metric.ball (parabolicPoint 0 0) 1).restrict
          (parabolicPotentialCoefficientRescale rho p.1 potential)) ∧
      (∀ q, q ∈ Metric.ball (parabolicPoint 0 0) 1 →
        ‖parabolicPotentialCoefficientRescale rho p.1 potential q‖ ≤
          rho ^ 2 * Bc) ∧
      spdParabolicSchauderDefectConst
        (Matrix.of fun i j ↦ principal i j p.1) (hpos p.1 p.2) alpha
        (fun i j ↦ Ka i j * rho ^ (alpha : Real))
        (fun i j ↦ Ka i j * rho ^ (alpha : Real)) T < 1} :=
    fun p ↦ ⟨rho p, hrho p⟩
  have hcompact : IsCompact Q :=
    isCompact_parabolicCylinder_Icc t₀ t₁ (isCompact_closedBall center r)
  obtain ⟨s, hs⟩ := exists_finite_ball_cover_of_isCompact hcompact
    (fun p : Q ↦ ((localScale p).1 : Real))
    (fun p ↦ by exact_mod_cast (localScale p).2.1)
  exact ⟨localScale, s, hs⟩

end DifferentialGeometry.Analysis.Parabolic.Euclidean

end
