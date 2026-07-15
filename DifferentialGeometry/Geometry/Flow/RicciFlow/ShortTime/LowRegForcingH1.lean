import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegCoefficients
import DifferentialGeometry.Analysis.Spectral.Tensor.Estimates.UniformL2FromRaw
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.RHSSectionChartComponentIdentity
import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.RealizedCovGradJetInput
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.IteratedCovGradHsJetBound

/-!
# Uniform low-regularity Ricci--DeTurck forcing bound

The chart coefficient package `IsLowRegCoeff` gives a uniform spectral `H1`
bound for the realized Ricci--DeTurck right-hand-side sections.
-/

noncomputable section

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal NNReal BigOperators Matrix

namespace DifferentialGeometry.PDE.RicciFlow

open DifferentialGeometry
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Laplacian.TensorRegularity
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurckCoefficients
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

private theorem rhs_raw_eq
    (gBase g : SmoothRiemannianMetric I M) (α : M) {b : M}
    (hb : b ∈ chartLeviCivitaGoodSet (I := I) α)
    (Idx : Fin 0 → Fin (Module.finrank ℝ E))
    (Jdx : Fin 2 → Fin (Module.finrank ℝ E)) :
    tensorChartComponentRaw (I := I) (M := M) gBase 0 2
        (deTurckRHSSectionBg (I := I) gBase g) α Idx Jdx b =
      chartDeTurckRHSComp (I := I) gBase g α (Jdx 0) (Jdx 1)
        (extChartAt I α b) := by
  simpa only [chartDeTurckRHSComp_def] using
    tensorChartComponentRaw_deTurckRHSSectionBg_eq_chartRicciLie
      (I := I) (M := M) gBase g α hb Idx Jdx

private theorem rhs_pull_eq
    (gBase g : SmoothRiemannianMetric I M) (α : M)
    (Jdx : Fin 2 → Fin (Module.finrank ℝ E)) :
    Set.EqOn
      (chartPushedRaw I α
        (tensorChartComponentRaw (I := I) (M := M) gBase 0 2
          (deTurckRHSSectionBg (I := I) gBase g) α
          (fun _ : Fin 0 => (0 : Fin (Module.finrank ℝ E))) Jdx))
      (chartDeTurckRHSComp (I := I) gBase g α (Jdx 0) (Jdx 1) ∘
        (toEuclidean (E := E)).symm)
      (chartTargetEuclid (I := I) (M := M) α) := by
  intro y hy
  rw [chartPushedRaw_apply_of_mem (I := I) (M := M) α _ hy]
  let b : M := (extChartAt I α).symm ((toEuclidean (E := E)).symm y)
  have hy_target : (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target :=
    DifferentialGeometry.Analysis.Laplacian.MetricExtension.toEuclidean_symm_mem_target
      (I := I) hy
  have hb_src : b ∈ (extChartAt I α).source :=
    (extChartAt I α).map_target hy_target
  have hb_good : b ∈ chartLeviCivitaGoodSet (I := I) α :=
    (mem_chartLeviCivitaGoodSet_iff_mem_extChartAt_source
      (I := I) α b).2 hb_src
  have hφ : extChartAt I α b = (toEuclidean (E := E)).symm y :=
    (extChartAt I α).right_inv hy_target
  rw [rhs_raw_eq (I := I) (M := M) gBase g α hb_good]
  simp only [Function.comp_apply, hφ]

private theorem rhs_partial_eq
    (gBase g : SmoothRiemannianMetric I M) (α : M)
    (d : Fin (Module.finrank ℝ E))
    (Jdx : Fin 2 → Fin (Module.finrank ℝ E)) {y : EuclN}
    (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    euclidPartial (E := E) d
        (chartPushedRaw I α
          (tensorChartComponentRaw (I := I) (M := M) gBase 0 2
            (deTurckRHSSectionBg (I := I) gBase g) α
            (fun _ : Fin 0 => (0 : Fin (Module.finrank ℝ E))) Jdx)) y =
      partialDeriv (E := E) d
        (chartDeTurckRHSComp (I := I) gBase g α (Jdx 0) (Jdx 1))
        ((toEuclidean (E := E)).symm y) := by
  have hderiv := euclidPartial_congr_of_eqOn_isOpen (E := E) d
    (chartTargetEuclid_isOpen (I := I) (M := M) α)
    (rhs_pull_eq (I := I) (M := M) gBase g α Jdx) hy
  calc
    euclidPartial (E := E) d
        (chartPushedRaw I α
          (tensorChartComponentRaw (I := I) (M := M) gBase 0 2
            (deTurckRHSSectionBg (I := I) gBase g) α
            (fun _ : Fin 0 => (0 : Fin (Module.finrank ℝ E))) Jdx)) y
        = euclidPartial (E := E) d
            (chartDeTurckRHSComp (I := I) gBase g α (Jdx 0) (Jdx 1) ∘
              (toEuclidean (E := E)).symm) y := hderiv
    _ = ((partialDeriv (E := E) d
          (chartDeTurckRHSComp (I := I) gBase g α (Jdx 0) (Jdx 1))) ∘
            (toEuclidean (E := E)).symm) y :=
      (congrFun (partialDeriv_comp_toEuclidean_symm_eq_euclidPartial
        (E := E) d
        (chartDeTurckRHSComp (I := I) gBase g α (Jdx 0) (Jdx 1))) y).symm
    _ = _ := rfl

/-- A low-regularity coefficient package gives one uniform spectral `H1`
bound for the Ricci--DeTurck right-hand side over the whole metric family. -/
theorem rhs_h1_bdd {ι : Type*}
    (gBase : SmoothRiemannianMetric I M)
    (gSeq : ι → SmoothRiemannianMetric I M) (D : LowRegCoeff)
    (hD : IsLowRegCoeff (I := I) gBase gSeq D) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k : ι,
      ‖ccTensorToHs (I := I) (M := M) gBase 2 (1 : ℝ)
        (deTurckRHSSectionBg (I := I) gBase (gSeq k))‖ ≤ C := by
  classical
  let S : ι → SmoothCcTensor gBase 0 2 := fun k =>
    deTurckRHSSectionBg (I := I) gBase (gSeq k)
  have hraw0 : ∀ α ∈ chartAtlasPOU_finset (I := I) (M := M),
      ∀ k : ι, ∀ b ∈ tsupport
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ),
        ∀ Idx : Fin 0 → Fin (Module.finrank ℝ E),
          ∀ Jdx : Fin 2 → Fin (Module.finrank ℝ E),
            |tensorChartComponentRaw (I := I) (M := M)
              gBase 0 2 (S k) α Idx Jdx b| ≤ D.rhsBound := by
    intro α hα k b hb Idx Jdx
    have hb_src : b ∈ (extChartAt I α).source := by
      rw [extChartAt_source]
      exact chartAtlasPOU_isSubordinate I M α hb
    have hb_good : b ∈ chartLeviCivitaGoodSet (I := I) α :=
      (mem_chartLeviCivitaGoodSet_iff_mem_extChartAt_source
        (I := I) α b).2 hb_src
    rw [show S k = deTurckRHSSectionBg (I := I) gBase (gSeq k) from rfl,
      rhs_raw_eq (I := I) (M := M) gBase (gSeq k) α hb_good]
    exact hD.rhs_bound α hα k b hb (Jdx 0) (Jdx 1)
  obtain ⟨C₀, hC₀, hL2₀⟩ := l2_bdd_of_raw
    (I := I) (M := M) gBase 0 2 S D.rhsBound hD.rhsBound_pos.le hraw0

  choose Cα hCα hCα_bd using fun α : M =>
    exists_lowerOrderCoeff_uniform_boundR
      (I := I) (M := M) gBase 0 2 α 0
  let CΓ : ℝ := ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M), Cα α
  have hCΓ : 0 ≤ CΓ := by
    dsimp [CΓ]
    exact Finset.sum_nonneg fun α _ => hCα α
  have hcoeff : ∀ α ∈ chartAtlasPOU_finset (I := I) (M := M),
      ∀ m : Fin (Module.finrank ℝ E),
        ∀ Idx : Fin 0 → Fin (Module.finrank ℝ E),
          ∀ Jdx : Fin 2 → Fin (Module.finrank ℝ E),
            ∀ p : (Fin 0 → Fin (Module.finrank ℝ E)) ×
                (Fin 2 → Fin (Module.finrank ℝ E)),
              ∀ y ∈ chartImagePOUTsupport (I := I) (M := M) α,
                |covDerivLowerOrderCoeff (I := I) (M := M)
                  gBase 0 2 α m Idx p.1 Jdx p.2 y| ≤ CΓ := by
    intro α hα m Idx Jdx p y hy
    have h := hCα_bd α m Idx Jdx p 0 (by omega) y hy
    rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at h
    refine h.trans ?_
    exact Finset.single_le_sum (f := Cα)
      (fun β _ => hCα β) hα
  let L : ℝ :=
    ∑ _p : (Fin 0 → Fin (Module.finrank ℝ E)) ×
        (Fin 2 → Fin (Module.finrank ℝ E)), CΓ * D.rhsBound
  have hL : 0 ≤ L := by
    dsimp [L]
    exact Finset.sum_nonneg fun _ _ =>
      mul_nonneg hCΓ hD.rhsBound_pos.le
  let B₁ : ℝ := D.rhsD1Bound + L
  have hB₁ : 0 ≤ B₁ := by
    dsimp [B₁]
    exact add_nonneg hD.rhsD1Bound_pos.le hL
  have hlower : ∀ α ∈ chartAtlasPOU_finset (I := I) (M := M),
      ∀ k : ι, ∀ b ∈ tsupport
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ),
        ∀ m : Fin (Module.finrank ℝ E),
          ∀ Jdx : Fin 2 → Fin (Module.finrank ℝ E),
            |covDerivLowerOrderTerm (I := I) (M := M) gBase 0 2
              (S k) α m (fun _ : Fin 0 => (0 : Fin (Module.finrank ℝ E))) Jdx
              (toEuclidean (E := E) (extChartAt I α b))| ≤ L := by
    intro α hα k b hb m Jdx
    have hb_src : b ∈ (extChartAt I α).source := by
      rw [extChartAt_source]
      exact chartAtlasPOU_isSubordinate I M α hb
    have hround :
        (extChartAt I α).symm
          ((toEuclidean (E := E)).symm
            (toEuclidean (E := E) (extChartAt I α b))) = b := by
      simpa using (extChartAt I α).left_inv hb_src
    have hyK : toEuclidean (E := E) (extChartAt I α b) ∈
        chartImagePOUTsupport (I := I) (M := M) α :=
      ⟨extChartAt I α b, ⟨b, hb, rfl⟩, rfl⟩
    have hsum :
        (∑ p : (Fin 0 → Fin (Module.finrank ℝ E)) ×
            (Fin 2 → Fin (Module.finrank ℝ E)),
          |covDerivLowerOrderCoeff (I := I) (M := M) gBase 0 2 α m
              (fun _ : Fin 0 => (0 : Fin (Module.finrank ℝ E))) p.1 Jdx p.2
              (toEuclidean (E := E) (extChartAt I α b)) *
            tensorChartComponentRaw (I := I) (M := M) gBase 0 2 (S k) α p.1 p.2
              ((extChartAt I α).symm
                ((toEuclidean (E := E)).symm
                  (toEuclidean (E := E) (extChartAt I α b))))|) ≤
          ∑ _p : (Fin 0 → Fin (Module.finrank ℝ E)) ×
            (Fin 2 → Fin (Module.finrank ℝ E)), CΓ * D.rhsBound := by
      exact Finset.sum_le_sum fun p _ => by
        rw [abs_mul, hround]
        exact mul_le_mul (hcoeff α hα m _ Jdx p _ hyK)
          (hraw0 α hα k b hb p.1 p.2) (abs_nonneg _) hCΓ
    rw [covDerivLowerOrderTerm_def]
    exact (Finset.abs_sum_le_sum_abs _ _).trans (hsum.trans_eq rfl)
  have hraw1 : ∀ α ∈ chartAtlasPOU_finset (I := I) (M := M),
      ∀ k : ι, ∀ b ∈ tsupport
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ),
        ∀ Idx : Fin 0 → Fin (Module.finrank ℝ E),
          ∀ Kdx : Fin 3 → Fin (Module.finrank ℝ E),
            |tensorChartComponentRaw (I := I) (M := M) gBase 0 3
              (covGrad (I := I) (M := M) gBase 0 2 (S k))
              α Idx Kdx b| ≤ B₁ := by
    intro α hα k b hb Idx Kdx
    have hIdx : Idx = fun _ : Fin 0 => (0 : Fin (Module.finrank ℝ E)) :=
      Subsingleton.elim _ _
    subst Idx
    let d : Fin (Module.finrank ℝ E) := Kdx 0
    let Jdx : Fin 2 → Fin (Module.finrank ℝ E) := Matrix.vecTail Kdx
    let y : EuclN := toEuclidean (E := E) (extChartAt I α b)
    have hb_src : b ∈ (extChartAt I α).source := by
      rw [extChartAt_source]
      exact chartAtlasPOU_isSubordinate I M α hb
    have hy : y ∈ chartTargetEuclid (I := I) (M := M) α :=
      ⟨extChartAt I α b, (extChartAt I α).map_source hb_src, rfl⟩
    have hround :
        (extChartAt I α).symm ((toEuclidean (E := E)).symm y) = b := by
      dsimp [y]
      simpa using (extChartAt I α).left_inv hb_src
    have hcons : (Fin.cons d Jdx : Fin 3 → Fin (Module.finrank ℝ E)) = Kdx := by
      exact Fin.cons_self_tail Kdx
    have hinv := euclidPartial_chartPushedRaw_general_eq_covGrad_sub_lowerOrder
      (I := I) (M := M) gBase 2 (S k) α d Jdx hy
    rw [hcons, hround] at hinv
    have hderiv := rhs_partial_eq
      (I := I) (M := M) gBase (gSeq k) α d Jdx hy
    have hyround : (toEuclidean (E := E)).symm y = extChartAt I α b := by
      dsimp [y]
      simp
    rw [hyround] at hderiv
    rw [hderiv] at hinv
    have hcov :
        tensorChartComponentRaw (I := I) (M := M) gBase 0 3
            (covGrad (I := I) (M := M) gBase 0 2 (S k)) α
            (fun _ : Fin 0 => (0 : Fin (Module.finrank ℝ E))) Kdx b =
          partialDeriv (E := E) d
              (chartDeTurckRHSComp (I := I) gBase (gSeq k) α
                (Jdx 0) (Jdx 1)) (extChartAt I α b) +
            covDerivLowerOrderTerm (I := I) (M := M) gBase 0 2
              (S k) α d (fun _ : Fin 0 => (0 : Fin (Module.finrank ℝ E))) Jdx y := by
      linarith
    rw [hcov]
    calc
      |partialDeriv (E := E) d
            (chartDeTurckRHSComp (I := I) gBase (gSeq k) α
              (Jdx 0) (Jdx 1)) (extChartAt I α b) +
          covDerivLowerOrderTerm (I := I) (M := M) gBase 0 2
            (S k) α d (fun _ : Fin 0 => (0 : Fin (Module.finrank ℝ E))) Jdx y|
          ≤ |partialDeriv (E := E) d
              (chartDeTurckRHSComp (I := I) gBase (gSeq k) α
                (Jdx 0) (Jdx 1)) (extChartAt I α b)| +
            |covDerivLowerOrderTerm (I := I) (M := M) gBase 0 2
              (S k) α d (fun _ : Fin 0 => (0 : Fin (Module.finrank ℝ E))) Jdx y| :=
            abs_add_le _ _
      _ ≤ D.rhsD1Bound + L := add_le_add
        (hD.rhs_d1_bound α hα k b hb d (Jdx 0) (Jdx 1))
        (by simpa [y] using hlower α hα k b hb d Jdx)
      _ = B₁ := rfl
  obtain ⟨C₁, hC₁, hL2₁⟩ := l2_bdd_of_raw
    (I := I) (M := M) gBase 0 3
    (fun k => covGrad (I := I) (M := M) gBase 0 2 (S k))
    B₁ hB₁ hraw1
  obtain ⟨Csp, hCsp, hsp⟩ := hs_le_jet (I := I) (M := M) gBase 2 1
  refine ⟨Csp * (C₀ + C₁), mul_nonneg hCsp (add_nonneg hC₀ hC₁), fun k => ?_⟩
  have hsum : ∑ j ∈ Finset.range (1 + 1),
        ‖iteratedCovGrad (I := I) gBase 0 2 j (S k)‖ =
      ‖S k‖ + ‖covGrad (I := I) (M := M) gBase 0 2 (S k)‖ := by
    rw [show (1 + 1) = 2 by omega, Finset.sum_range_succ, Finset.sum_range_one]
    simp only [iteratedCovGrad_zero, iteratedCovGrad_succ, Nat.add_zero]
  calc
    ‖ccTensorToHs (I := I) (M := M) gBase 2 (1 : ℝ) (S k)‖
        ≤ Csp * ∑ j ∈ Finset.range (1 + 1),
            ‖iteratedCovGrad (I := I) gBase 0 2 j (S k)‖ := by
              have hcast : (1 : ℝ) = ((1 : ℕ) : ℝ) := by norm_num
              rw [hcast]
              exact hsp (S k)
    _ = Csp * (‖S k‖ + ‖covGrad (I := I) (M := M) gBase 0 2 (S k)‖) := by
      rw [hsum]
    _ ≤ Csp * (C₀ + C₁) :=
      mul_le_mul_of_nonneg_left (add_le_add (hL2₀ k) (hL2₁ k)) hCsp

end DifferentialGeometry.PDE.RicciFlow
