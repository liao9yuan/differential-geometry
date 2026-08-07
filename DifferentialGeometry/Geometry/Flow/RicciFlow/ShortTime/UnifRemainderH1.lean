import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderTameLipschitz.Base
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegRemainderH1
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.UnifTopPathH1
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.UnifPathLower
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.UnifRhsConvex

/-!
# Class-first low-regularity Ricci--DeTurck remainder estimate

The top-path action, the lower application estimate, and both integrated lower
coefficient jets are assembled with all constants selected before the metric in
the order-three class varies.  The public theorem is restricted to dimension
three, matching the low-regularity existence interface.
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry
open DifferentialGeometry.HCGCompactness
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.PDE.DeTurck.RicciLinearization
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurckCoefficients

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

-- The symmetry hypotheses are used to obtain the path identity in the proof,
-- although their dependency is not visible in the conclusion's syntax.
set_option linter.unusedVariables false in
/-- **Dimension-three class-first mixed `H3 -> H1` remainder estimate.**

The radius, top coefficient, and affine lower coefficients are chosen before
the class metric varies.  The DeTurck background is the fixed class background
`gBase`; endpoint `H3` size occurs only in the coefficient of the `H2`
difference. -/
theorem rem_h1_unif
    (hDim : Module.finrank ℝ E = 3)
    (gBase : SmoothRiemannianMetric I M) {Λ : ℝ} (hΛ : 1 ≤ Λ)
    {δ₀ : ℝ} (hδ₀_nonneg : 0 ≤ δ₀) (hδ₀_lt : δ₀ < 1) :
    ∃ ρ Ctop : ℝ, ∃ B0 B1 : ℝ → ℝ,
      0 < ρ ∧ 0 ≤ Ctop ∧
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B0 R) ∧
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B1 R) ∧
      ∀ g : SmoothRiemannianMetric I M,
        MetricUniformEquivalentOn (I := I) Set.univ gBase g Λ →
        (∀ a : ℕ, a ≤ 3 →
          MetricCovDerivOrderBoundOn (I := I) Set.univ a g gBase Λ) →
        ∀ (T T' : SmoothCcTensor g 0 2)
          (hTsymm : ∀ (x : M) (v w : TangentSpace I x),
            ccTensorBilin (I := I) g T x v w = ccTensorBilin (I := I) g T x w v)
          (hT'symm : ∀ (x : M) (v w : TangentSpace I x),
            ccTensorBilin (I := I) g T' x v w = ccTensorBilin (I := I) g T' x w v)
          (hδ : gFibreOpBound (I := I) (M := M) g
            (ccTensorBilinSymm (I := I) g T) δ₀)
          (hδ' : gFibreOpBound (I := I) (M := M) g
            (ccTensorBilinSymm (I := I) g T') δ₀)
          (R : ℝ), 0 ≤ R → R ≤ ρ →
          ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ R →
          ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T'‖ ≤ R →
          ‖ccTensorToHs (I := I) (M := M) g 2 ((1 : ℕ) : ℝ)
            ((deTurckRHSArmG0 (I := I) g gBase T hδ₀_lt hδ -
                deTurckRHSArmG0 (I := I) g gBase T' hδ₀_lt hδ') -
              rawTensorConnLapSmooth (I := I) g 0 2 (T - T'))‖ ≤
            Ctop * R *
                ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) (T - T')‖ +
              B0 R *
                ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - T')‖ +
              B1 R *
                  (‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖ +
                    ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T'‖) *
                ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - T')‖ := by
  obtain ⟨ρ, Ctop, Clow, hρ, hCtop, hClow, htop⟩ :=
    top_path_h1_unif (I := I) (M := M) hDim gBase hΛ
  obtain ⟨Ccoef, hCcoef, hlower⟩ :=
    lower_jet_unif (I := I) (M := M) hDim gBase hΛ
  obtain ⟨Z0, Z1, hZ0, hZ1, hzero⟩ :=
    rhs0_path_unif (I := I) (M := M) hDim gBase hΛ hδ₀_nonneg hδ₀_lt
  obtain ⟨O0, O1, hO0, hO1, hone⟩ :=
    rhs1_path_unif (I := I) (M := M) hDim gBase hΛ hδ₀_nonneg hδ₀_lt
  let B0 : ℝ → ℝ := fun R => Clow + Ccoef * (Z0 R + O0 R)
  let B1 : ℝ → ℝ := fun R => Ccoef * (Z1 R + O1 R)
  have hB0 : ∀ R : ℝ, 0 ≤ R → 0 ≤ B0 R := by
    intro R hR
    exact add_nonneg hClow
      (mul_nonneg hCcoef (add_nonneg (hZ0 R hR) (hO0 R hR)))
  have hB1 : ∀ R : ℝ, 0 ≤ R → 0 ≤ B1 R := by
    intro R hR
    exact mul_nonneg hCcoef (add_nonneg (hZ1 R hR) (hO1 R hR))
  refine ⟨ρ, Ctop, B0, B1, hρ, hCtop, hB0, hB1, ?_⟩
  intro g hEq hjet T T' hTsymm hT'symm hδ hδ' R hR hRρ hT2 hT2'
  let A : ℝ :=
    ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖ +
      ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T'‖
  have hA : 0 ≤ A := add_nonneg (norm_nonneg _) (norm_nonneg _)
  have hT3 : ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖ ≤ A := by
    exact le_add_of_nonneg_right (norm_nonneg _)
  have hT3' : ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T'‖ ≤ A := by
    exact le_add_of_nonneg_left (norm_nonneg _)
  let A0 : ℝ := Z0 R + Z1 R * A
  let A1 : ℝ := O0 R + O1 R * A
  have hA0 : 0 ≤ A0 :=
    add_nonneg (hZ0 R hR) (mul_nonneg (hZ1 R hR) hA)
  have hA1 : 0 ≤ A1 :=
    add_nonneg (hO0 R hR) (mul_nonneg (hO1 R hR) hA)
  have hΦ0 : (∑ j ∈ Finset.range 2,
      ‖iteratedCovGrad (I := I) g 2 2 j
        (rhsLow0PathIntegral (I := I) (M := M) g gBase T T'
          hδ₀_lt hδ hδ₀_lt hδ')‖ ^ 2) ≤ A0 ^ 2 := by
    simpa only [A0] using
      hzero g hEq hjet T T' hδ hδ' R A hR hA hT2 hT2' hT3 hT3'
  have hΦ1 : (∑ j ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g 3 2 j
        (rhsLow1PathIntegral (I := I) (M := M) g gBase T T'
          hδ₀_lt hδ hδ₀_lt hδ')‖ ^ 2) ≤ A1 ^ 2 := by
    simpa only [A1] using
      hone g hEq hjet T T' hδ hδ' R A hR hA hT2 hT2' hT3 hT3'
  let U : SmoothCcTensor g 0 2 := T - T'
  set Φ0 : SmoothCcTensor g 2 2 :=
    rhsLow0PathIntegral (I := I) (M := M) g gBase T T'
      hδ₀_lt hδ hδ₀_lt hδ' with hΦ0def
  set Φ1 : SmoothCcTensor g 3 2 :=
    rhsLow1PathIntegral (I := I) (M := M) g gBase T T'
      hδ₀_lt hδ hδ₀_lt hδ' with hΦ1def
  clear_value Φ0 Φ1
  have hΦ0eq :
      rhsLow0PathIntegral (I := I) (M := M) g gBase T T'
        hδ₀_lt hδ hδ₀_lt hδ' = Φ0 := hΦ0def.symm
  have hΦ1eq :
      rhsLow1PathIntegral (I := I) (M := M) g gBase T T'
        hδ₀_lt hδ hδ₀_lt hδ' = Φ1 := hΦ1def.symm
  clear hΦ0def hΦ1def
  have hΦ0bound : (∑ j ∈ Finset.range 2,
      ‖iteratedCovGrad (I := I) g 2 2 j Φ0‖ ^ 2) ≤ A0 ^ 2 := by
    simpa only [hΦ0eq] using hΦ0
  have hΦ1bound : (∑ j ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g 3 2 j Φ1‖ ^ 2) ≤ A1 ^ 2 := by
    simpa only [hΦ1eq] using hΦ1
  let Φ2 : SmoothCcTensor g 4 2 :=
    rhsTopPathIntegral (I := I) (M := M) g gBase T T'
      hδ₀_lt hδ hδ₀_lt hδ'
  have hpath :
      realizedRHSArm (I := I) g gBase T hδ₀_lt hδ -
          realizedRHSArm (I := I) g gBase T' hδ₀_lt hδ' =
        appCc (I := I) (M := M) g 2 2 Φ0
            (iteratedCovGrad (I := I) g 0 2 0 U) +
          appCc (I := I) (M := M) g 3 2 Φ1
            (iteratedCovGrad (I := I) g 0 2 1 U) +
          appCc (I := I) (M := M) g 4 2 Φ2
            (iteratedCovGrad (I := I) g 0 2 2 U) := by
    simpa only [U, Φ2, hΦ0eq, hΦ1eq] using
      rhsArm_sub_eq_paths (I := I) (M := M) g gBase T T'
        hTsymm hT'symm hδ₀_lt hδ hδ₀_lt hδ'
  have hiter0 : iteratedCovGrad (I := I) g 0 2 0 U = U := by
    rw [iteratedCovGrad_zero]
  have hiter1 : iteratedCovGrad (I := I) g 0 2 1 U =
      covGrad (I := I) (M := M) g 0 2 U := by
    rw [iteratedCovGrad_succ, iteratedCovGrad_zero]
  rw [hiter0, hiter1] at hpath
  have hlower' :
      ‖ccTensorToHs (I := I) (M := M) g 2 (1 : ℝ)
        (appCc (I := I) (M := M) g 2 2 Φ0 U +
          appCc (I := I) (M := M) g 3 2 Φ1
            (covGrad (I := I) (M := M) g 0 2 U))‖ ≤
        Ccoef * (A0 + A1) *
          ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ := by
    exact hlower g hEq hjet Φ0 Φ1 U A0 A1 hA0 hA1 hΦ0bound hΦ1bound
  have htop' :
      ‖ccTensorToHs (I := I) (M := M) g 2 (1 : ℝ)
        (appCc (I := I) (M := M) g 4 2 Φ2
            (iteratedCovGrad (I := I) g 0 2 2 U) -
          rawTensorConnLapSmooth (I := I) g 0 2 U)‖ ≤
        Ctop * R * ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) U‖ +
          Clow * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ := by
    simpa only [U, Φ2] using
      htop g hEq hjet T T' hδ₀_lt hδ hδ₀_lt hδ'
        hR hRρ hT2 hT2' U
  change
    ‖ccTensorToHs (I := I) (M := M) g 2 ((1 : ℕ) : ℝ)
      ((realizedRHSArm (I := I) g gBase T hδ₀_lt hδ -
          realizedRHSArm (I := I) g gBase T' hδ₀_lt hδ') -
        rawTensorConnLapSmooth (I := I) g 0 2 (T - T'))‖ ≤ _
  rw [Nat.cast_one]
  rw [hpath]
  let Slow : SmoothCcTensor g 0 2 :=
    appCc (I := I) (M := M) g 2 2 Φ0 U +
      appCc (I := I) (M := M) g 3 2 Φ1
        (covGrad (I := I) (M := M) g 0 2 U)
  let Stop : SmoothCcTensor g 0 2 :=
    appCc (I := I) (M := M) g 4 2 Φ2
        (iteratedCovGrad (I := I) g 0 2 2 U) -
      rawTensorConnLapSmooth (I := I) g 0 2 U
  have hsplit :
      (appCc (I := I) (M := M) g 2 2 Φ0 U +
          appCc (I := I) (M := M) g 3 2 Φ1
            (covGrad (I := I) (M := M) g 0 2 U) +
        appCc (I := I) (M := M) g 4 2 Φ2
            (iteratedCovGrad (I := I) g 0 2 2 U)) -
          rawTensorConnLapSmooth (I := I) g 0 2 U = Slow + Stop := by
    simp only [Slow, Stop]
    abel
  rw [hsplit, ccTensorToHs_add]
  calc
    _ ≤ ‖ccTensorToHs (I := I) (M := M) g 2 (1 : ℝ) Slow‖ +
          ‖ccTensorToHs (I := I) (M := M) g 2 (1 : ℝ) Stop‖ := norm_add_le _ _
    _ ≤ Ccoef * (A0 + A1) *
          ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ +
        (Ctop * R * ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) U‖ +
          Clow * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖) := by
      apply add_le_add
      · simpa only [Slow] using hlower'
      · simpa only [Stop] using htop'
    _ = Ctop * R *
          ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) U‖ +
        B0 R * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ +
        B1 R * A *
          ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ := by
      simp only [A0, A1, B0, B1]
      ring

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
