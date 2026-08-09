import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderLowBaseAction

/-!
# The `k = 0` dissipation rung of the zero-based Ricci--DeTurck remainder

On a closed three-manifold this module records the lowest rung of the
supercritical dissipation ladder

`‖N T - N 0‖_{H^{k+1}} ≤ Cδ₀ ‖T‖_{H^{k+3}} + C k ‖T‖_{H^{k+2}}`,  `Cδ₀ < 1`,

at `k = 0`, i.e. an `H1`-output estimate whose top-order term is carried by the
`H3` norm with a constant that is *smaller than one* on a sufficiently small
spectral `H2` ball, and whose remaining term only costs the `H2` norm.

The two summands are the canonical zero-based smooth-core split
`N T - N 0 = a₂ T + a₁ T` of `lowData_split`: the small second-order action
`a₂` supplies the top-order term (its coefficient is pointwise and two-jet
small by `c2_h2_small`), and the genuinely first-order action `a₁` supplies the
lower-order term (`a1_h2_h1` together with the coefficient envelope
`lowData_a1_coeff`).
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

open Bundle Manifold Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

/-- The covariant `L²` jet square-sum through any order `n` is controlled by
the spectral `H^n` norm.  This is the order-generic form of `hs2_low2`. -/
private theorem jetSq_le_hs
    (g : SmoothRiemannianMetric I M) (s n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : SmoothCcTensor g 0 s,
      lowJetSq (I := I) (M := M) g n T ≤
        (C * ‖ccTensorToHs (I := I) (M := M) g s (n : ℝ) T‖) ^ 2 := by
  obtain ⟨C, hC, hjet⟩ := hsJet_le (I := I) (M := M) g s n
  refine ⟨C, hC, fun T => ?_⟩
  simp only [lowJetSq]
  refine (Finset.sum_sq_le_sq_sum_of_nonneg (fun _ _ => norm_nonneg _)).trans ?_
  exact pow_le_pow_left₀
    (Finset.sum_nonneg (fun _ _ => norm_nonneg _)) (hjet T) 2

set_option linter.unusedVariables false in
/-- **The `k = 0` rung of the low-regularity dissipation ladder.**

In dimension three there is a spectral `H2` radius `ρ` and constants
`Cδ₀ < 1`, `C₀`, such that every symmetric `T` lying in the `H2` ball of
radius `ρ` and in the `H3` ball of radius `R₀` satisfies

`‖N T - N 0‖_{H1} ≤ Cδ₀ ‖T‖_{H3} + C₀ ‖T‖_{H2}`,

where `N` is the zero-based smooth Ricci--DeTurck remainder over the
background `g₀`.  The top-order constant `Cδ₀` is smaller than one because it
is proportional to the ball radius `ρ`; the remaining constant `C₀` depends on
`R₀` only.

The binders `hT` and `hδ0` are consumed by the proof, not by the statement,
so the unused-variable linter is switched off for this declaration. -/
theorem n_diff_h1_rung
    (hDim : Module.finrank ℝ E = 3)
    (g₀ : SmoothRiemannianMetric I M) (R₀ : ℝ) :
    ∃ ρ Cδ₀ C₀ : ℝ, 0 < ρ ∧ 0 ≤ Cδ₀ ∧ Cδ₀ < 1 ∧ 0 ≤ C₀ ∧
      ∀ (T : SmoothCcTensor g₀ 0 2)
        (hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g₀ T x u v =
            ccTensorBilin (I := I) g₀ T x v u)
        {δ : ℝ} (hδ_le : δ ≤ 1 / 3) (hδ0 : 0 ≤ δ)
        (hδ : gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ T) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀
            (0 : SmoothCcTensor g₀ 0 2)) δ),
        ‖ccTensorToHs (I := I) (M := M) g₀ 2 (2 : ℝ) T‖ ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g₀ 2 (3 : ℝ) T‖ ≤ R₀ →
        ‖ccTensorToHs (I := I) (M := M) g₀ 2 (1 : ℝ)
            (deTurckSmoothRemainder (I := I) g₀ g₀ T
                (lt_of_le_of_lt hδ_le (by norm_num)) hδ -
              deTurckSmoothRemainder (I := I) g₀ g₀
                (0 : SmoothCcTensor g₀ 0 2)
                (lt_of_le_of_lt hδ_le (by norm_num)) hδZ)‖ ≤
          Cδ₀ * ‖ccTensorToHs (I := I) (M := M) g₀ 2 (3 : ℝ) T‖ +
            C₀ * ‖ccTensorToHs (I := I) (M := M) g₀ 2 (2 : ℝ) T‖ := by
  classical
  obtain ⟨ρ2, Cc2, hρ2, hCc2, hc2⟩ := c2_h2_small (I := I) (M := M) hDim g₀
  obtain ⟨Capp, hCapp, happ⟩ := appCc_h2_h3_h1 (I := I) (M := M) hDim g₀ 2 2
  obtain ⟨_, _, hsplit⟩ := lowData_split (I := I) (M := M) g₀ g₀
  obtain ⟨Ka1, hKa1, hcoef⟩ := lowData_a1_coeff (I := I) (M := M) hDim g₀
  obtain ⟨Ca1, hCa1, ha1⟩ := a1_h2_h1 (I := I) (M := M) hDim g₀
  obtain ⟨Chs2, hChs2, hjet2⟩ := jetSq_le_hs (I := I) (M := M) g₀ 2 2
  obtain ⟨Chs3, hChs3, hjet3⟩ := jetSq_le_hs (I := I) (M := M) g₀ 2 3
  obtain ⟨Csp, hCsp, hsp⟩ := hs_le_jet (I := I) (M := M) g₀ 2 1
  have hcc : (0 : ℝ) ≤ Capp * Cc2 := mul_nonneg hCapp hCc2
  have hden : (0 : ℝ) < 2 * (Capp * Cc2 + 1) := by linarith
  -- the shrunken `H2` radius making the top-order constant a contraction
  obtain ⟨ρ, hρpos, hρ2le, hsmall⟩ :
      ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ ρ2 ∧ Capp * Cc2 * ρ < 1 := by
    refine ⟨min ρ2 (1 / (2 * (Capp * Cc2 + 1))),
      lt_min hρ2 (div_pos one_pos hden), min_le_left _ _, ?_⟩
    have h2 : Capp * Cc2 * min ρ2 (1 / (2 * (Capp * Cc2 + 1))) ≤
        Capp * Cc2 * (1 / (2 * (Capp * Cc2 + 1))) :=
      mul_le_mul_of_nonneg_left (min_le_right _ _) hcc
    have h3 : Capp * Cc2 * (1 / (2 * (Capp * Cc2 + 1))) < 1 := by
      rw [mul_one_div, div_lt_one hden]
      linarith
    linarith
  -- the `H3`-ball coefficient envelope of the first-order arm
  obtain ⟨B, hB0, hBsq⟩ :
      ∃ B : ℝ, 0 ≤ B ∧ Ka1 * (1 + (Chs3 * R₀) ^ 2) ^ 6 = B ^ 2 :=
    ⟨Real.sqrt (Ka1 * (1 + (Chs3 * R₀) ^ 2) ^ 6), Real.sqrt_nonneg _,
      (Real.sq_sqrt (mul_nonneg hKa1 (pow_nonneg (by positivity) 6))).symm⟩
  refine ⟨ρ, Capp * Cc2 * ρ, 2 * Csp * Ca1 * B * Chs2, hρpos,
    mul_nonneg hcc hρpos.le, hsmall,
    mul_nonneg (mul_nonneg (mul_nonneg
      (mul_nonneg (by norm_num) hCsp) hCa1) hB0) hChs2, ?_⟩
  intro T hT δ hδ_le hδ0 hδ hδZ hball2 hball3
  have hN2 : (0 : ℝ) ≤ ‖ccTensorToHs (I := I) (M := M) g₀ 2 (2 : ℝ) T‖ :=
    norm_nonneg _
  have hN3 : (0 : ℝ) ≤ ‖ccTensorToHs (I := I) (M := M) g₀ 2 (3 : ℝ) T‖ :=
    norm_nonneg _
  -- the canonical zero-based smooth-core split, with its coefficient data made
  -- opaque so that no later step unfolds the path-integral witnesses
  obtain ⟨A, hsplitA, hc2pt, hc2jet, hcoefT⟩ :
      ∃ A : LowBaseActionData g₀,
        deTurckSmoothRemainder (I := I) g₀ g₀ T
              (lt_of_le_of_lt hδ_le (by norm_num)) hδ -
            deTurckSmoothRemainder (I := I) g₀ g₀
              (0 : SmoothCcTensor g₀ 0 2)
              (lt_of_le_of_lt hδ_le (by norm_num)) hδZ =
          A.a2 (I := I) (M := M) T + A.a1 (I := I) (M := M) T ∧
        (∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x
            (A.C2.toSection x) ≤ (Cc2 * ρ) ^ 2) ∧
        lowJetSq (I := I) (M := M) g₀ 2 A.C2 ≤ (Cc2 * ρ) ^ 2 ∧
        lowJetSq (I := I) (M := M) g₀ 2 A.C0 +
            lowJetSq (I := I) (M := M) g₀ 2 A.C1 ≤
          Ka1 * (1 + lowJetSq (I := I) (M := M) g₀ 3 T) ^ 6 := by
    refine ⟨lowBaseData (I := I) (M := M) g₀ g₀ T
      (lt_of_le_of_lt hδ_le (by norm_num)) hδ hδZ,
      (hsplit T hT hδ_le hδ0 hδ hδZ).1,
      (hc2 T hT hδ_le hδ0 hδ hδZ (R := ρ) hρpos.le hρ2le hball2).1,
      (hc2 T hT hδ_le hδ0 hδ hδZ (R := ρ) hρpos.le hρ2le hball2).2,
      hcoef T hT hδ_le hδ0 hδ hδZ⟩
  rw [hsplitA]
  -- the top-order arm is a contraction on the `H2` ball
  have ha2 :
      ‖ccTensorToHs (I := I) (M := M) g₀ 2 (1 : ℝ)
          (A.a2 (I := I) (M := M) T)‖ ≤
        Capp * Cc2 * ρ *
          ‖ccTensorToHs (I := I) (M := M) g₀ 2 (3 : ℝ) T‖ := by
    have hb := happ A.C2 T (Cc2 * ρ) (mul_nonneg hCc2 hρpos.le) hc2pt
      (by simpa only [lowJetSq, Nat.reduceAdd] using hc2jet)
    calc
      ‖ccTensorToHs (I := I) (M := M) g₀ 2 (1 : ℝ)
          (A.a2 (I := I) (M := M) T)‖ ≤
          Capp * (Cc2 * ρ) *
            ‖ccTensorToHs (I := I) (M := M) g₀ 2 (3 : ℝ) T‖ := hb
      _ = Capp * Cc2 * ρ *
            ‖ccTensorToHs (I := I) (M := M) g₀ 2 (3 : ℝ) T‖ := by ring
  -- jet control of the state from the two spectral balls
  have hjet2T :
      lowJetSq (I := I) (M := M) g₀ 2 T ≤
        (Chs2 * ‖ccTensorToHs (I := I) (M := M) g₀ 2 (2 : ℝ) T‖) ^ 2 := by
    have h := hjet2 T
    norm_num at h
    exact h
  have hjet3T :
      lowJetSq (I := I) (M := M) g₀ 3 T ≤ (Chs3 * R₀) ^ 2 := by
    have h := hjet3 T
    norm_num at h
    refine h.trans (pow_le_pow_left₀ (mul_nonneg hChs3 hN3) ?_ 2)
    exact mul_le_mul_of_nonneg_left hball3 hChs3
  have hjnn : (0 : ℝ) ≤ lowJetSq (I := I) (M := M) g₀ 3 T := by
    simp only [lowJetSq]
    exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  -- the first-order coefficient envelope on the `H3` ball
  have hcoefB :
      lowJetSq (I := I) (M := M) g₀ 2 A.C0 +
        lowJetSq (I := I) (M := M) g₀ 2 A.C1 ≤ B ^ 2 := by
    refine hcoefT.trans ?_
    rw [← hBsq]
    refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith) ?_ 6) hKa1
    linarith
  -- the first-order arm only costs the `H2` norm
  have hX : (0 : ℝ) ≤
      Ca1 * B * (Chs2 * ‖ccTensorToHs (I := I) (M := M) g₀ 2 (2 : ℝ) T‖) :=
    mul_nonneg (mul_nonneg hCa1 hB0) (mul_nonneg hChs2 hN2)
  have ha1norm :
      ‖ccTensorToHs (I := I) (M := M) g₀ 2 (1 : ℝ)
          (A.a1 (I := I) (M := M) T)‖ ≤
        2 * Csp * Ca1 * B * Chs2 *
          ‖ccTensorToHs (I := I) (M := M) g₀ 2 (2 : ℝ) T‖ := by
    have hspY := hsp (A.a1 (I := I) (M := M) T)
    rw [show ((1 : ℕ) : ℝ) = (1 : ℝ) by norm_num] at hspY
    have hjetY :
        ‖iteratedCovGrad (I := I) g₀ 0 2 0 (A.a1 (I := I) (M := M) T)‖ ^ 2 +
            ‖iteratedCovGrad (I := I) g₀ 0 2 1
              (A.a1 (I := I) (M := M) T)‖ ^ 2 ≤
          (Ca1 * B *
            (Chs2 * ‖ccTensorToHs (I := I) (M := M) g₀ 2 (2 : ℝ) T‖)) ^ 2 := by
      have h := ha1 A T B
        (Chs2 * ‖ccTensorToHs (I := I) (M := M) g₀ 2 (2 : ℝ) T‖) hB0
        (mul_nonneg hChs2 hN2) hcoefB hjet2T
      simp only [lowJetSq, Finset.sum_range_succ, Finset.sum_range_zero,
        zero_add] at h
      exact h
    have h0nn : (0 : ℝ) ≤
        ‖iteratedCovGrad (I := I) g₀ 0 2 0 (A.a1 (I := I) (M := M) T)‖ :=
      norm_nonneg _
    have h1nn : (0 : ℝ) ≤
        ‖iteratedCovGrad (I := I) g₀ 0 2 1 (A.a1 (I := I) (M := M) T)‖ :=
      norm_nonneg _
    have h0 :
        ‖iteratedCovGrad (I := I) g₀ 0 2 0 (A.a1 (I := I) (M := M) T)‖ ≤
          Ca1 * B * (Chs2 * ‖ccTensorToHs (I := I) (M := M) g₀ 2 (2 : ℝ) T‖) :=
      le_of_sq_le_sq (by
        linarith only [hjetY, sq_nonneg
          ‖iteratedCovGrad (I := I) g₀ 0 2 1 (A.a1 (I := I) (M := M) T)‖]) hX
    have h1 :
        ‖iteratedCovGrad (I := I) g₀ 0 2 1 (A.a1 (I := I) (M := M) T)‖ ≤
          Ca1 * B * (Chs2 * ‖ccTensorToHs (I := I) (M := M) g₀ 2 (2 : ℝ) T‖) :=
      le_of_sq_le_sq (by
        linarith only [hjetY, sq_nonneg
          ‖iteratedCovGrad (I := I) g₀ 0 2 0 (A.a1 (I := I) (M := M) T)‖]) hX
    have hsum : ∑ j ∈ Finset.range (1 + 1),
        ‖iteratedCovGrad (I := I) g₀ 0 2 j (A.a1 (I := I) (M := M) T)‖ ≤
          2 * (Ca1 * B *
            (Chs2 * ‖ccTensorToHs (I := I) (M := M) g₀ 2 (2 : ℝ) T‖)) := by
      rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero,
        zero_add]
      linarith only [h0, h1]
    calc
      ‖ccTensorToHs (I := I) (M := M) g₀ 2 (1 : ℝ)
          (A.a1 (I := I) (M := M) T)‖ ≤
          Csp * ∑ j ∈ Finset.range (1 + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 2 j
              (A.a1 (I := I) (M := M) T)‖ := hspY
      _ ≤ Csp * (2 * (Ca1 * B *
            (Chs2 * ‖ccTensorToHs (I := I) (M := M) g₀ 2 (2 : ℝ) T‖))) :=
        mul_le_mul_of_nonneg_left hsum hCsp
      _ = 2 * Csp * Ca1 * B * Chs2 *
            ‖ccTensorToHs (I := I) (M := M) g₀ 2 (2 : ℝ) T‖ := by ring
  -- assemble
  rw [ccTensorToHs_add (I := I) (M := M) g₀ 2 (1 : ℝ)]
  exact (norm_add_le _ _).trans (add_le_add ha2 ha1norm)

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
