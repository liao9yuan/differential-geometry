import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegBgC0PairBase

/-!
# Order-zero curvature pair estimates

Internal pair-estimate layer for the low-regularity order-zero refold.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert
open DifferentialGeometry.PDE.DeTurck.RicciLinearization
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

namespace LowRegBgC0Core

set_option maxHeartbeats 5000000 in
set_option linter.unusedVariables false in
theorem aaKerOnePairH2
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ : ℝ, ∃ B : ℝ → ℝ, 0 < ρ ∧
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B R) ∧
      ∀ (gT gU : SmoothRiemannianMetric I M)
        (T U : SmoothCcTensor g 0 2)
        (hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        (hU : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g U x u v =
            ccTensorBilin (I := I) g U x v u)
        (hTtie : ∀ (x : M) (u v : TangentSpace I x),
          gT.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g T x u v)
        (hUtie : ∀ (x : M) (u v : TangentSpace I x),
          gU.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g U x u v)
        {δ : ℝ} (hδ_le : δ ≤ 1 / 3) (hδ0 : 0 ≤ δ)
        (hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδU : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g U) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ),
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ ≤ ρ →
        ∀ (R A D2 D3 N : ℝ),
        0 ≤ R → 0 ≤ A → 0 ≤ D2 → 0 ≤ D3 → 0 ≤ N →
        lowJetSq (I := I) (M := M) g 2 T ≤ R ^ 2 →
        lowJetSq (I := I) (M := M) g 2 U ≤ R ^ 2 →
        lowJetSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
        lowJetSq (I := I) (M := M) g 3 U ≤ A ^ 2 →
        lowJetSq (I := I) (M := M) g 2 (T - U) ≤ D2 ^ 2 →
        lowJetSq (I := I) (M := M) g 3 (T - U) ≤ D3 ^ 2 →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U)‖ ≤ N →
      lowJetSq (I := I) (M := M) g 2
          (aaKerOne (I := I) (M := M) g gT T -
            aaKerOne (I := I) (M := M) g gU U) ≤
        (B R * (1 + A) * (D3 + D2 + A * D2 + N)) ^ 2 := by
  obtain ⟨B0, B1, hB0, hB1, houtPair⟩ :=
    connIns_sub_tame (I := I) (M := M) hDim g
      (by norm_num : (0 : ℝ) ≤ 1 / 3) (by norm_num : (1 : ℝ) / 3 < 1)
  obtain ⟨Bo, hBo, houtBdd⟩ := connOut_h2 (I := I) (M := M) hDim g
  obtain ⟨ρi, Bi, hρi, hBi, hinBdd⟩ :=
    innerAct_h2 (I := I) (M := M) hDim g
  obtain ⟨ρp, Bp, hρp, hBp, hinPair⟩ :=
    innerActPairH2 (I := I) (M := M) hDim g
  obtain ⟨Cb, hCb, hblk⟩ :=
    aaBlkOnePairH2 (I := I) (M := M) hDim g
  obtain ⟨Cm, hCm, hmid⟩ :=
    appRoot_h2 (I := I) (M := M) hDim g 3 3 3
  let J : ℝ := aaCapOne (I := I) (M := M) g
  let P : ℝ := Real.sqrt J
  let Zf : ℝ := 1 + Cm * P
  let Co : ℝ → ℝ := fun R => B0 R + B1 R
  let L : ℝ → ℝ := fun R =>
    Cb * P *
      (Co R * (Zf * Bi * R) + Bo R * Zf * Bp * (1 + R))
  let B : ℝ → ℝ := fun R => 10 * L R
  let ρ : ℝ := min ρi ρp
  have hJ : 0 ≤ J := aaCap_nneg (I := I) (M := M) g
  have hP : 0 ≤ P := Real.sqrt_nonneg _
  have hPsq : P ^ 2 = J := by
    simpa only [P] using Real.sq_sqrt hJ
  have hZf : 0 ≤ Zf :=
    add_nonneg (by norm_num) (mul_nonneg hCm hP)
  have hZf1 : 1 ≤ Zf := by
    dsimp only [Zf]
    exact le_add_of_nonneg_right (mul_nonneg hCm hP)
  have hCo : ∀ R : ℝ, 0 ≤ R → 0 ≤ Co R := by
    intro R hR
    exact add_nonneg (hB0 R hR) (hB1 R hR)
  have hL : ∀ R : ℝ, 0 ≤ R → 0 ≤ L R := by
    intro R hR
    dsimp only [L]
    exact mul_nonneg (mul_nonneg hCb hP)
      (add_nonneg
        (mul_nonneg (hCo R hR)
          (mul_nonneg (mul_nonneg hZf hBi) hR))
        (mul_nonneg
          (mul_nonneg (mul_nonneg (hBo R hR) hZf) hBp)
          (add_nonneg (by norm_num) hR)))
  have hρ : 0 < ρ := lt_min hρi hρp
  refine ⟨ρ, B, hρ,
    fun R hR => mul_nonneg (by norm_num) (hL R hR), ?_⟩
  intro gT gU T U hT hU hTtie hUtie δ hδ_le hδ0 hδT hδU hδZ
    hTn hUn R A D2 D3 N hR hA hD2 hD3 hN
    hT2 hU2 hT3 hU3 hTU2 hTU3 hTUn
  let IT : SmoothCcTensor g 3 3 :=
    innerAct (I := I) (M := M) g gT T
  let IU : SmoothCcTensor g 3 3 :=
    innerAct (I := I) (M := M) g gU U
  let OD : ℝ := B0 R * D3 + B1 R * D2 + B1 R * A * D2
  let OU : ℝ := Bo R * (1 + A)
  let ZB : ℝ := Zf * (Bi * R)
  let ZD : ℝ := Zf * (Bp * (D2 + R * N))
  let D : ℝ := D3 + D2 + A * D2
  let S : ℝ := (1 + A) * (D + N)
  let Q : ℝ := (L R * S) ^ 2
  have hOD : 0 ≤ OD := by
    dsimp only [OD]
    exact add_nonneg
      (add_nonneg (mul_nonneg (hB0 R hR) hD3)
        (mul_nonneg (hB1 R hR) hD2))
      (mul_nonneg (mul_nonneg (hB1 R hR) hA) hD2)
  have hOU : 0 ≤ OU := by
    dsimp only [OU]
    exact mul_nonneg (hBo R hR) (add_nonneg (by norm_num) hA)
  have hZB : 0 ≤ ZB := by
    dsimp only [ZB]
    exact mul_nonneg hZf (mul_nonneg hBi hR)
  have hZD : 0 ≤ ZD := by
    dsimp only [ZD]
    exact mul_nonneg hZf
      (mul_nonneg hBp (add_nonneg hD2 (mul_nonneg hR hN)))
  have hD : 0 ≤ D := by
    dsimp only [D]
    exact add_nonneg (add_nonneg hD3 hD2) (mul_nonneg hA hD2)
  have hS : 0 ≤ S := by
    dsimp only [S]
    exact mul_nonneg (add_nonneg (by norm_num) hA)
      (add_nonneg hD hN)
  have hQ : 0 ≤ Q := sq_nonneg _
  have hTni : ‖ccTensorToHs (I := I) (M := M) g 2
      (2 : ℝ) T‖ ≤ ρi := hTn.trans (min_le_left _ _)
  have hTnp : ‖ccTensorToHs (I := I) (M := M) g 2
      (2 : ℝ) T‖ ≤ ρp := hTn.trans (min_le_right _ _)
  have hUnp : ‖ccTensorToHs (I := I) (M := M) g 2
      (2 : ℝ) U‖ ≤ ρp := hUn.trans (min_le_right _ _)
  have hIT : lowJetSq (I := I) (M := M) g 2 IT ≤ (Bi * R) ^ 2 := by
    simpa only [IT] using
      hinBdd gT T T hT hT hTtie R hR hT2 hTni
  have hIdiff : lowJetSq (I := I) (M := M) g 2 (IT - IU) ≤
      (Bp * (D2 + R * N)) ^ 2 := by
    simpa only [IT, IU] using
      hinPair gT gU T U hT hU hTtie hUtie hTnp hUnp
        R D2 N hR hD2 hN hU2 hTU2 hTUn
  have hoDiff : lowJetSq (I := I) (M := M) g 2
      (connDiffContrInsertionField (I := I) g gT -
        connDiffContrInsertionField (I := I) g gU) ≤ OD ^ 2 := by
    simpa only [OD] using
      houtPair gT gU T U hT hU hTtie hUtie
        hδ_le hδ0 hδT hδ_le hδ0 hδU
        R A D2 D3 hR hA hD2 hD3 hU2 hT3 hTU2 hTU3
  have hoU : lowJetSq (I := I) (M := M) g 2
      (connDiffContrInsertionField (I := I) g gU) ≤ OU ^ 2 := by
    simpa only [OU] using
      houtBdd gU U hU hUtie hδ_le hδ0 hδU hδZ
        R A hR hA hU2 hU3
  have hcap4 : ∀ pm : Equiv.Perm (Fin 4),
      (pm = ricPerm3201 ∨ pm = ricPerm2301 ∨ pm = ricPerm3102 ∨
        pm = ricPerm1302 ∨ pm = ricPerm1203 ∨ pm = ricPerm2103) →
      lowJetSq (I := I) (M := M) g 2
          (permCoeff (I := I) (M := M) g pm) ≤ P ^ 2 := by
    intro pm hpm
    simpa only [hPsq, J] using aaCap4 (I := I) (M := M) g pm hpm
  have hcap3 : ∀ pm : Equiv.Perm (Fin 3),
      (pm = ricPerm102 ∨ pm = ricPerm120) →
      lowJetSq (I := I) (M := M) g 2
          (permCoeff (I := I) (M := M) g pm) ≤ P ^ 2 := by
    intro pm hpm
    simpa only [hPsq, J] using aaCap3 (I := I) (M := M) g pm hpm
  have hmidB : ∀ pm : Equiv.Perm (Fin 3),
      (pm = ricPerm102 ∨ pm = ricPerm120) →
      lowJetSq (I := I) (M := M) g 2
          (appCcRS (I := I) (M := M) g 3 3 3
            (permCoeff (I := I) (M := M) g pm) IT) ≤ ZB ^ 2 := by
    intro pm hpm
    have hraw := hmid
      (permCoeff (I := I) (M := M) g pm) IT
      P (Bi * R) hP (mul_nonneg hBi hR) (hcap3 pm hpm) hIT
    refine hraw.trans (pow_le_pow_left₀
      (mul_nonneg (mul_nonneg hCm hP) (mul_nonneg hBi hR)) ?_ 2)
    dsimp only [ZB, Zf]
    rw [show (1 + Cm * P) * (Bi * R) =
        Cm * P * (Bi * R) + 1 * (Bi * R) by ring]
    exact le_add_of_nonneg_right
      (mul_nonneg (by norm_num) (mul_nonneg hBi hR))
  have hmidD : ∀ pm : Equiv.Perm (Fin 3),
      (pm = ricPerm102 ∨ pm = ricPerm120) →
      lowJetSq (I := I) (M := M) g 2
          (appCcRS (I := I) (M := M) g 3 3 3
              (permCoeff (I := I) (M := M) g pm) IT -
            appCcRS (I := I) (M := M) g 3 3 3
              (permCoeff (I := I) (M := M) g pm) IU) ≤ ZD ^ 2 := by
    intro pm hpm
    rw [← appCcRS_sub_right]
    have hraw := hmid
      (permCoeff (I := I) (M := M) g pm) (IT - IU)
      P (Bp * (D2 + R * N)) hP
      (mul_nonneg hBp (add_nonneg hD2 (mul_nonneg hR hN)))
      (hcap3 pm hpm) hIdiff
    refine hraw.trans (pow_le_pow_left₀
      (mul_nonneg (mul_nonneg hCm hP)
        (mul_nonneg hBp (add_nonneg hD2 (mul_nonneg hR hN)))) ?_ 2)
    dsimp only [ZD, Zf]
    rw [show (1 + Cm * P) * (Bp * (D2 + R * N)) =
        Cm * P * (Bp * (D2 + R * N)) +
          1 * (Bp * (D2 + R * N)) by ring]
    exact le_add_of_nonneg_right
      (mul_nonneg (by norm_num)
        (mul_nonneg hBp (add_nonneg hD2 (mul_nonneg hR hN))))
  have hbareB : lowJetSq (I := I) (M := M) g 2 IT ≤ ZB ^ 2 := by
    refine hIT.trans (pow_le_pow_left₀ (mul_nonneg hBi hR) ?_ 2)
    dsimp only [ZB]
    simpa only [one_mul] using
      mul_le_mul_of_nonneg_right hZf1 (mul_nonneg hBi hR)
  have hbareD : lowJetSq (I := I) (M := M) g 2 (IT - IU) ≤ ZD ^ 2 := by
    refine hIdiff.trans (pow_le_pow_left₀
      (mul_nonneg hBp (add_nonneg hD2 (mul_nonneg hR hN))) ?_ 2)
    dsimp only [ZD]
    simpa only [one_mul] using
      mul_le_mul_of_nonneg_right hZf1
        (mul_nonneg hBp (add_nonneg hD2 (mul_nonneg hR hN)))
  have hD2D : D2 ≤ D := by
    dsimp only [D]
    nlinarith [mul_nonneg hA hD2]
  have hDS : D ≤ S := by
    have hDN : D ≤ D + N := le_add_of_nonneg_right hN
    have hmul : D + N ≤ (1 + A) * (D + N) := by
      have h1A : 1 ≤ 1 + A := le_add_of_nonneg_right hA
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_right h1A (add_nonneg hD hN)
    exact hDN.trans hmul
  have hDR : D2 + R * N ≤ (1 + R) * (D + N) := by
    have hNsum : N ≤ D + N := le_add_of_nonneg_left hD
    calc
      D2 + R * N ≤ D + R * (D + N) :=
        add_le_add hD2D (mul_le_mul_of_nonneg_left hNsum hR)
      _ ≤ (D + N) + R * (D + N) :=
        add_le_add (le_add_of_nonneg_right hN) le_rfl
      _ = (1 + R) * (D + N) := by ring
  have hODle : OD ≤ Co R * D := by
    have hgap : Co R * D = OD +
        (B0 R * D2 + B0 R * A * D2 + B1 R * D3) := by
      simp only [Co, D, OD]
      ring
    rw [hgap]
    exact le_add_of_nonneg_right
      (add_nonneg
        (add_nonneg (mul_nonneg (hB0 R hR) hD2)
          (mul_nonneg (mul_nonneg (hB0 R hR) hA) hD2))
        (mul_nonneg (hB1 R hR) hD3))
  have hlead : Cb * P * (OD * ZB + OU * ZD) ≤ L R * S := by
    let c1 : ℝ := Co R * (Zf * Bi * R)
    let c2 : ℝ := Bo R * Zf * Bp * (1 + R)
    have hc1 : 0 ≤ c1 := by
      dsimp only [c1]
      exact mul_nonneg (hCo R hR)
        (mul_nonneg (mul_nonneg hZf hBi) hR)
    have hc2 : 0 ≤ c2 := by
      dsimp only [c2]
      exact mul_nonneg
        (mul_nonneg (mul_nonneg (hBo R hR) hZf) hBp)
        (add_nonneg (by norm_num) hR)
    have hfirst : OD * ZB ≤ c1 * S := by
      calc
        OD * ZB ≤ (Co R * D) * ZB :=
          mul_le_mul_of_nonneg_right hODle hZB
        _ = c1 * D := by simp only [c1, ZB]; ring
        _ ≤ c1 * S := mul_le_mul_of_nonneg_left hDS hc1
    have hsecond : OU * ZD ≤ c2 * S := by
      have hbase : 0 ≤ Bo R * Zf * Bp * (1 + A) :=
        mul_nonneg
          (mul_nonneg (mul_nonneg (hBo R hR) hZf) hBp)
          (add_nonneg (by norm_num) hA)
      calc
        OU * ZD =
            (Bo R * Zf * Bp * (1 + A)) * (D2 + R * N) := by
          simp only [OU, ZD]
          ring
        _ ≤ (Bo R * Zf * Bp * (1 + A)) *
            ((1 + R) * (D + N)) :=
          mul_le_mul_of_nonneg_left hDR hbase
        _ = c2 * S := by simp only [c2, S]; ring
    calc
      Cb * P * (OD * ZB + OU * ZD) ≤
          Cb * P * (c1 * S + c2 * S) :=
        mul_le_mul_of_nonneg_left (add_le_add hfirst hsecond)
          (mul_nonneg hCb hP)
      _ = L R * S := by simp only [L, c1, c2]; ring
  have hblkFin : ∀ (pm : Equiv.Perm (Fin 4))
      (hpm : pm = ricPerm3201 ∨ pm = ricPerm2301 ∨
        pm = ricPerm3102 ∨ pm = ricPerm1302 ∨
        pm = ricPerm1203 ∨ pm = ricPerm2103)
      (ZT ZU : SmoothCcTensor g 3 3),
      lowJetSq (I := I) (M := M) g 2 ZT ≤ ZB ^ 2 →
      lowJetSq (I := I) (M := M) g 2 (ZT - ZU) ≤ ZD ^ 2 →
      lowJetSq (I := I) (M := M) g 2
          (aaBlkOne (I := I) (M := M) g gT pm ZT -
            aaBlkOne (I := I) (M := M) g gU pm ZU) ≤ Q := by
    intro pm hpm ZT ZU hZT hZD'
    have hraw := hblk gT gU pm ZT ZU P OD OU ZB ZD
      hP hOD hOU hZB hZD (hcap4 pm hpm) hoDiff hoU hZT hZD'
    exact hraw.trans
      (pow_le_pow_left₀
        (mul_nonneg (mul_nonneg hCb hP)
          (add_nonneg (mul_nonneg hOD hZB) (mul_nonneg hOU hZD)))
        hlead 2)
  have hx0 : lowJetSq (I := I) (M := M) g 2
      (aaMidOne (I := I) (M := M) g gT T ricPerm102 ricPerm3201 -
        aaMidOne (I := I) (M := M) g gU U ricPerm102 ricPerm3201) ≤ Q := by
    simpa only [aaMidOne, aaBlkOne, IT, IU] using
      hblkFin ricPerm3201 (Or.inl rfl) _ _
        (hmidB ricPerm102 (Or.inl rfl))
        (hmidD ricPerm102 (Or.inl rfl))
  have hx1 : lowJetSq (I := I) (M := M) g 2
      (aaMidOne (I := I) (M := M) g gT T ricPerm102 ricPerm2301 -
        aaMidOne (I := I) (M := M) g gU U ricPerm102 ricPerm2301) ≤ Q := by
    simpa only [aaMidOne, aaBlkOne, IT, IU] using
      hblkFin ricPerm2301 (Or.inr (Or.inl rfl)) _ _
        (hmidB ricPerm102 (Or.inl rfl))
        (hmidD ricPerm102 (Or.inl rfl))
  have hx2 : lowJetSq (I := I) (M := M) g 2
      (aaMidOne (I := I) (M := M) g gT T ricPerm120 ricPerm3102 -
        aaMidOne (I := I) (M := M) g gU U ricPerm120 ricPerm3102) ≤ Q := by
    simpa only [aaMidOne, aaBlkOne, IT, IU] using
      hblkFin ricPerm3102 (Or.inr (Or.inr (Or.inl rfl))) _ _
        (hmidB ricPerm120 (Or.inr rfl))
        (hmidD ricPerm120 (Or.inr rfl))
  have hx3 : lowJetSq (I := I) (M := M) g 2
      (aaBareOne (I := I) (M := M) g gT T ricPerm1302 -
        aaBareOne (I := I) (M := M) g gU U ricPerm1302) ≤ Q := by
    simpa only [aaBareOne, aaBlkOne, IT, IU] using
      hblkFin ricPerm1302
        (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) IT IU hbareB hbareD
  have hx4 : lowJetSq (I := I) (M := M) g 2
      (aaBareOne (I := I) (M := M) g gT T ricPerm1203 -
        aaBareOne (I := I) (M := M) g gU U ricPerm1203) ≤ Q := by
    simpa only [aaBareOne, aaBlkOne, IT, IU] using
      hblkFin ricPerm1203
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
        IT IU hbareB hbareD
  have hx5 : lowJetSq (I := I) (M := M) g 2
      (aaMidOne (I := I) (M := M) g gT T ricPerm120 ricPerm2103 -
        aaMidOne (I := I) (M := M) g gU U ricPerm120 ricPerm2103) ≤ Q := by
    simpa only [aaMidOne, aaBlkOne, IT, IU] using
      hblkFin ricPerm2103
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))) _ _
        (hmidB ricPerm120 (Or.inr rfl))
        (hmidD ricPerm120 (Or.inr rfl))
  have hker :
      aaKerOne (I := I) (M := M) g gT T -
          aaKerOne (I := I) (M := M) g gU U =
        (aaMidOne (I := I) (M := M) g gT T ricPerm102 ricPerm3201 -
          aaMidOne (I := I) (M := M) g gU U ricPerm102 ricPerm3201) +
        (aaMidOne (I := I) (M := M) g gT T ricPerm102 ricPerm2301 -
          aaMidOne (I := I) (M := M) g gU U ricPerm102 ricPerm2301) +
        (aaMidOne (I := I) (M := M) g gT T ricPerm120 ricPerm3102 -
          aaMidOne (I := I) (M := M) g gU U ricPerm120 ricPerm3102) +
        (aaBareOne (I := I) (M := M) g gT T ricPerm1302 -
          aaBareOne (I := I) (M := M) g gU U ricPerm1302) +
        (aaBareOne (I := I) (M := M) g gT T ricPerm1203 -
          aaBareOne (I := I) (M := M) g gU U ricPerm1203) +
        (aaMidOne (I := I) (M := M) g gT T ricPerm120 ricPerm2103 -
          aaMidOne (I := I) (M := M) g gU U ricPerm120 ricPerm2103) := by
    simp only [aaKerOne]
    module
  rw [hker]
  refine (jetSix (I := I) (M := M) g 2 _ _ _ _ _ _
    hx0 hx1 hx2 hx3 hx4 hx5).trans ?_
  calc
    94 * Q ≤ 100 * Q := mul_le_mul_of_nonneg_right (by norm_num) hQ
    _ = (B R * (1 + A) * (D3 + D2 + A * D2 + N)) ^ 2 := by
      simp only [B, Q, S, D]
      ring

theorem reindexSubC0
    (g : SmoothRiemannianMetric I M) {r s : ℕ}
    (A B : SmoothCcTensor g r s) (σ : Equiv.Perm (Fin r)) :
    reindexCoeffGen (I := I) (M := M) g r s (A - B) σ =
      reindexCoeffGen (I := I) (M := M) g r s A σ -
        reindexCoeffGen (I := I) (M := M) g r s B σ := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [SmoothCcTensor.toSection_sub, ContMDiffSection.coe_sub, Pi.sub_apply,
    reindexCoeffGen_toSection, reindexCoeffGen_toSection,
    reindexCoeffGen_toSection, SmoothCcTensor.toSection_sub,
    ContMDiffSection.coe_sub, Pi.sub_apply]
  apply ContinuousLinearMap.ext
  intro D
  rw [ContinuousLinearMap.sub_apply, reindexCoeffFibGen_apply,
    reindexCoeffFibGen_apply, reindexCoeffFibGen_apply,
    ContinuousLinearMap.sub_apply]

set_option maxHeartbeats 2400000 in
set_option linter.unusedVariables false in
theorem fourTracePair
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ C : ℝ, 0 < ρ ∧ 0 ≤ C ∧
      ∀ (T U : SmoothCcTensor g 0 2)
        (gT gU : SmoothRiemannianMetric I M),
        (∀ (y : M) (v w : TangentSpace I y),
          gT.inner y v w =
            g.inner y v w + ccTensorBilinSymm (I := I) g T y v w) →
        (∀ (y : M) (v w : TangentSpace I y),
          gU.inner y v w =
            g.inner y v w + ccTensorBilinSymm (I := I) g U y v w) →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ ≤ ρ →
        lowJetSq (I := I) (M := M) g 2
            (ricciCometricFourTraceCastG0 (I := I) g gT -
              ricciCometricFourTraceCastG0 (I := I) g gU) ≤
          (C * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
            (T - U)‖) ^ 2 := by
  obtain ⟨ρ, C0, hρ, hC0, hlip⟩ :=
    LowBaseInternal.trace2_pair_h2 (I := I) (M := M) hDim g
  let L : ℝ := 22 * C0 ^ 2
  let C : ℝ := Real.sqrt L
  have hL : 0 ≤ L := mul_nonneg (by norm_num) (sq_nonneg C0)
  refine ⟨ρ, C, hρ, Real.sqrt_nonneg _, ?_⟩
  intro T U gT gU hTtie hUtie hTn hUn
  have hF : lowJetSq (I := I) (M := M) g 2
      (ricciArmPrincipalCoeffPure (I := I) (M := M) g gT -
        ricciArmPrincipalCoeffPure (I := I) (M := M) g gU) ≤
      (C0 * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
        (T - U)‖) ^ 2 := by
    rw [pureCoeff_eq, pureCoeff_eq]
    exact hlip T U gT gU hTtie hUtie hTn hUn
  have heq :
      ricciCometricFourTraceCastG0 (I := I) g gT -
          ricciCometricFourTraceCastG0 (I := I) g gU =
        ((1 : ℝ) / 2) •
          (reindexCoeffGen (I := I) (M := M) g 4 2
                (ricciArmPrincipalCoeffPure (I := I) (M := M) g gT -
                  ricciArmPrincipalCoeffPure (I := I) (M := M) g gU)
                fourTraceArgPerm0231 +
            reindexCoeffGen (I := I) (M := M) g 4 2
                (ricciArmPrincipalCoeffPure (I := I) (M := M) g gT -
                  ricciArmPrincipalCoeffPure (I := I) (M := M) g gU)
                fourTraceArgPerm0321 -
            (ricciArmPrincipalCoeffPure (I := I) (M := M) g gT -
              ricciArmPrincipalCoeffPure (I := I) (M := M) g gU) -
            reindexCoeffGen (I := I) (M := M) g 4 2
                (ricciArmPrincipalCoeffPure (I := I) (M := M) g gT -
                  ricciArmPrincipalCoeffPure (I := I) (M := M) g gU)
                fourTraceArgPerm2301) := by
    rw [ricciCometricFourTraceCastG0_eq_reindex_combination
        (I := I) (M := M) g gT,
      ricciCometricFourTraceCastG0_eq_reindex_combination
        (I := I) (M := M) g gU,
      reindexSubC0, reindexSubC0, reindexSubC0]
    module
  rw [heq]
  refine (fourTrace_jet (I := I) (M := M) g _).trans ?_
  calc
    22 * lowJetSq (I := I) (M := M) g 2
        (ricciArmPrincipalCoeffPure (I := I) (M := M) g gT -
          ricciArmPrincipalCoeffPure (I := I) (M := M) g gU) ≤
      22 * (C0 * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
        (T - U)‖) ^ 2 :=
      mul_le_mul_of_nonneg_left hF (by norm_num)
    _ = (C * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
        (T - U)‖) ^ 2 := by
      simp only [C, mul_pow]
      rw [Real.sq_sqrt hL]
      simp only [L]
      ring

set_option maxHeartbeats 4000000 in
set_option linter.unusedVariables false in
theorem aaOnePairH2
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ : ℝ, ∃ B : ℝ → ℝ, 0 < ρ ∧
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B R) ∧
      ∀ (gT gU : SmoothRiemannianMetric I M)
        (T U : SmoothCcTensor g 0 2)
        (hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        (hU : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g U x u v =
            ccTensorBilin (I := I) g U x v u)
        (hTtie : ∀ (x : M) (u v : TangentSpace I x),
          gT.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g T x u v)
        (hUtie : ∀ (x : M) (u v : TangentSpace I x),
          gU.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g U x u v)
        {δ : ℝ} (hδ_le : δ ≤ 1 / 3) (hδ0 : 0 ≤ δ)
        (hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδU : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g U) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ),
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ ≤ ρ →
        ∀ (R A D2 D3 N : ℝ),
        0 ≤ R → 0 ≤ A → 0 ≤ D2 → 0 ≤ D3 → 0 ≤ N →
        lowJetSq (I := I) (M := M) g 2 T ≤ R ^ 2 →
        lowJetSq (I := I) (M := M) g 2 U ≤ R ^ 2 →
        lowJetSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
        lowJetSq (I := I) (M := M) g 3 U ≤ A ^ 2 →
        lowJetSq (I := I) (M := M) g 2 (T - U) ≤ D2 ^ 2 →
        lowJetSq (I := I) (M := M) g 3 (T - U) ≤ D3 ^ 2 →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U)‖ ≤ N →
      lowJetSq (I := I) (M := M) g 2
          (aaOne (I := I) (M := M) g gT T -
            aaOne (I := I) (M := M) g gU U) ≤
        (B R * (1 + A) * (D3 + D2 + A * D2 + N)) ^ 2 := by
  obtain ⟨ρkp, Bp, hρkp, hBp, hkerPair⟩ :=
    aaKerOnePairH2 (I := I) (M := M) hDim g
  obtain ⟨ρkb, Bk, hρkb, hBk, hkerBdd⟩ :=
    aaKerOne_h2 (I := I) (M := M) hDim g
  obtain ⟨ρtp, Ct, hρtp, hCt, htracePair⟩ :=
    fourTracePair (I := I) (M := M) hDim g
  obtain ⟨ρtb, Bt, hρtb, hBt, htraceBdd⟩ :=
    fourTrace_h2 (I := I) (M := M) hDim g
  obtain ⟨Ca, hCa, happ⟩ :=
    appRoot_h2 (I := I) (M := M) hDim g 3 4 2
  let ρ : ℝ := min ρkp (min ρkb (min ρtp ρtb))
  let B : ℝ → ℝ := fun R =>
    2 * Ca * (Ct * Bk R + Bt * Bp R)
  have hρ : 0 < ρ := lt_min hρkp (lt_min hρkb (lt_min hρtp hρtb))
  have hB : ∀ R : ℝ, 0 ≤ R → 0 ≤ B R := by
    intro R hR
    exact mul_nonneg (mul_nonneg (by norm_num) hCa)
      (add_nonneg (mul_nonneg hCt (hBk R hR))
        (mul_nonneg hBt (hBp R hR)))
  refine ⟨ρ, B, hρ, hB, ?_⟩
  intro gT gU T U hT hU hTtie hUtie δ hδ_le hδ0 hδT hδU hδZ
    hTn hUn R A D2 D3 N hR hA hD2 hD3 hN
    hT2 hU2 hT3 hU3 hTU2 hTU3 hTUn
  let FT : SmoothCcTensor g 4 2 :=
    ricciCometricFourTraceCastG0 (I := I) g gT
  let FU : SmoothCcTensor g 4 2 :=
    ricciCometricFourTraceCastG0 (I := I) g gU
  let KT : SmoothCcTensor g 3 4 := aaKerOne (I := I) (M := M) g gT T
  let KU : SmoothCcTensor g 3 4 := aaKerOne (I := I) (M := M) g gU U
  let D : ℝ := D3 + D2 + A * D2 + N
  let x : ℝ := Ca * (Ct * N) * (Bk R * (1 + A))
  let y : ℝ := Ca * Bt * (Bp R * (1 + A) * D)
  have hD : 0 ≤ D := by
    dsimp only [D]
    exact add_nonneg
      (add_nonneg (add_nonneg hD3 hD2) (mul_nonneg hA hD2)) hN
  have hx0 : 0 ≤ x := by
    dsimp only [x]
    exact mul_nonneg (mul_nonneg hCa (mul_nonneg hCt hN))
      (mul_nonneg (hBk R hR) (add_nonneg (by norm_num) hA))
  have hy0 : 0 ≤ y := by
    dsimp only [y]
    exact mul_nonneg (mul_nonneg hCa hBt)
      (mul_nonneg
        (mul_nonneg (hBp R hR) (add_nonneg (by norm_num) hA)) hD)
  have hTkp : ‖ccTensorToHs (I := I) (M := M) g 2
      (2 : ℝ) T‖ ≤ ρkp := hTn.trans (min_le_left _ _)
  have hUkp : ‖ccTensorToHs (I := I) (M := M) g 2
      (2 : ℝ) U‖ ≤ ρkp := hUn.trans (min_le_left _ _)
  have hTkb : ‖ccTensorToHs (I := I) (M := M) g 2
      (2 : ℝ) T‖ ≤ ρkb :=
    hTn.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hTtp : ‖ccTensorToHs (I := I) (M := M) g 2
      (2 : ℝ) T‖ ≤ ρtp :=
    hTn.trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _)))
  have hUtp : ‖ccTensorToHs (I := I) (M := M) g 2
      (2 : ℝ) U‖ ≤ ρtp :=
    hUn.trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _)))
  have hUtb : ‖ccTensorToHs (I := I) (M := M) g 2
      (2 : ℝ) U‖ ≤ ρtb :=
    hUn.trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_right _ _)))
  have hFdiff : lowJetSq (I := I) (M := M) g 2 (FT - FU) ≤
      (Ct * N) ^ 2 := by
    have hraw := htracePair T U gT gU hTtie hUtie hTtp hUtp
    exact hraw.trans
      (pow_le_pow_left₀ (mul_nonneg hCt (norm_nonneg _))
        (mul_le_mul_of_nonneg_left hTUn hCt) 2)
  have hFU : lowJetSq (I := I) (M := M) g 2 FU ≤ Bt ^ 2 := by
    simpa only [FU] using htraceBdd U gU hUtie hUtb
  have hKT : lowJetSq (I := I) (M := M) g 2 KT ≤
      (Bk R * (1 + A)) ^ 2 := by
    simpa only [KT] using
      hkerBdd gT T T hT hT hTtie hδ_le hδ0 hδT hδZ
        R A hR hA hT2 hT3 hT2 hTkb
  have hKdiff : lowJetSq (I := I) (M := M) g 2 (KT - KU) ≤
      (Bp R * (1 + A) * D) ^ 2 := by
    simpa only [KT, KU, D] using
      hkerPair gT gU T U hT hU hTtie hUtie
        hδ_le hδ0 hδT hδU hδZ hTkp hUkp
        R A D2 D3 N hR hA hD2 hD3 hN
        hT2 hU2 hT3 hU3 hTU2 hTU3 hTUn
  let X : SmoothCcTensor g 3 2 :=
    appCcRS (I := I) (M := M) g 3 4 2 (FT - FU) KT
  let Y : SmoothCcTensor g 3 2 :=
    appCcRS (I := I) (M := M) g 3 4 2 FU (KT - KU)
  have hX : lowJetSq (I := I) (M := M) g 2 X ≤ x ^ 2 := by
    simpa only [X, x] using
      happ (FT - FU) KT (Ct * N) (Bk R * (1 + A))
        (mul_nonneg hCt hN)
        (mul_nonneg (hBk R hR) (add_nonneg (by norm_num) hA))
        hFdiff hKT
  have hY : lowJetSq (I := I) (M := M) g 2 Y ≤ y ^ 2 := by
    simpa only [Y, y] using
      happ FU (KT - KU) Bt (Bp R * (1 + A) * D)
        hBt
        (mul_nonneg
          (mul_nonneg (hBp R hR) (add_nonneg (by norm_num) hA)) hD)
        hFU hKdiff
  have hsplit :
      aaOne (I := I) (M := M) g gT T -
          aaOne (I := I) (M := M) g gU U = X + Y := by
    simp only [aaOne, X, Y, FT, FU, KT, KU,
      appCcRS_sub_left, appCcRS_sub_right]
    module
  have hNle : N ≤ D := by
    dsimp only [D]
    exact le_add_of_nonneg_left
      (add_nonneg (add_nonneg hD3 hD2) (mul_nonneg hA hD2))
  have hlead : 2 * (x + y) ≤ B R * (1 + A) * D := by
    let c : ℝ := Ca * Ct * Bk R * (1 + A)
    have hc : 0 ≤ c := by
      dsimp only [c]
      exact mul_nonneg
        (mul_nonneg (mul_nonneg hCa hCt) (hBk R hR))
        (add_nonneg (by norm_num) hA)
    have hx : x ≤ c * D := by
      calc
        x = c * N := by simp only [x, c]; ring
        _ ≤ c * D := mul_le_mul_of_nonneg_left hNle hc
    calc
      2 * (x + y) ≤ 2 * (c * D + y) :=
        mul_le_mul_of_nonneg_left (add_le_add hx le_rfl) (by norm_num)
      _ = B R * (1 + A) * D := by simp only [B, c, y]; ring
  rw [hsplit]
  refine (jetAdd (I := I) (M := M) g 2 X Y).trans ?_
  calc
    2 * (lowJetSq (I := I) (M := M) g 2 X +
        lowJetSq (I := I) (M := M) g 2 Y) ≤
      2 * (x ^ 2 + y ^ 2) :=
        mul_le_mul_of_nonneg_left (add_le_add hX hY) (by norm_num)
    _ ≤ (2 * (x + y)) ^ 2 := by
      nlinarith [mul_nonneg hx0 hy0]
    _ ≤ (B R * (1 + A) * D) ^ 2 :=
      pow_le_pow_left₀
        (mul_nonneg (by norm_num) (add_nonneg hx0 hy0)) hlead 2


end LowRegBgC0Core
end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral
