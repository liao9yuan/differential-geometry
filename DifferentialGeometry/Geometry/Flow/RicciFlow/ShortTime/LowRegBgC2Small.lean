import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.LowRegC2JetTower

/-!
# Fixed-background smallness of the complete second-order coefficient

`c2_h2_small` shows that the complete canonical second-order coefficient of the
zero-based low-base split is pointwise and two-jet small on a small spectral
`H2` ball, but only at the *diagonal* background `g_bg = g`.  The adjacent-scale
lift needs the same statement at an arbitrary fixed background `gB`.

The background enters the top path integrand only through the metric-deviation
arm: by `topKernel_eq` the integrand splits as

`lieRefold2 g T s + (Φmet(g, gB, gm) - Φmet(g, gB, g)) + (-2s) • ricciTop g gm T`,

and the outer two summands are background-*blind*.  So the difference of the two
integrands (at `gB` and at `g`) is exactly the difference of the two metric
deviations, each of which is controlled by the two-metric `phi_dev_h2`.  The
difference of the two coefficients is therefore a single path integral of a
small integrand, and the fixed-background bound follows by the triangle
inequality against the diagonal `c2_h2_small`.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.PDE.DeTurck.RicciLinearization
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurckCoefficients

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

/-- **The background-blind arms cancel.**  Changing the fixed DeTurck
background from `g` to `gB` changes the complete top path integrand by exactly
the difference of the two metric deviations: the Lie refold and the Ricci top
arm produced by `topKernel_eq` carry no background at all. -/
theorem kerBgDiff
    (g gB : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    {δ : ℝ}
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ)
    (s : ℝ) :
    (rhsRefoldTop (I := I) (M := M) g gB T hδ hδZ s +
          LowBaseInternal.rhsSelfTop (I := I) (M := M) g T hδ hδZ s -
          deTurckPhiMetTotal (I := I) (M := M) g gB g) -
        (rhsRefoldTop (I := I) (M := M) g g T hδ hδZ s +
          LowBaseInternal.rhsSelfTop (I := I) (M := M) g T hδ hδZ s -
          deTurckPhiMetTotal (I := I) (M := M) g g g) =
      (deTurckPhiMetTotal (I := I) (M := M) g gB
            (realizedFam (I := I) g T 0 hδ hδZ s) -
          deTurckPhiMetTotal (I := I) (M := M) g gB g) -
        (deTurckPhiMetTotal (I := I) (M := M) g g
            (realizedFam (I := I) g T 0 hδ hδZ s) -
          deTurckPhiMetTotal (I := I) (M := M) g g g) := by
  rw [show rhsRefoldTop (I := I) (M := M) g gB T hδ hδZ s +
        LowBaseInternal.rhsSelfTop (I := I) (M := M) g T hδ hδZ s -
        deTurckPhiMetTotal (I := I) (M := M) g gB g = _ from
      LowBaseInternal.topKernel_eq (I := I) (M := M) g gB T hδ hδZ s,
    show rhsRefoldTop (I := I) (M := M) g g T hδ hδZ s +
        LowBaseInternal.rhsSelfTop (I := I) (M := M) g T hδ hδZ s -
        deTurckPhiMetTotal (I := I) (M := M) g g g = _ from
      LowBaseInternal.topKernel_eq (I := I) (M := M) g g T hδ hδZ s]
  abel

/-- The canonical `C2` projection at an arbitrary fixed background is the
single path integral of the complete top integrand.  This is `c2_eq` with the
two integrated arms and the fixed coefficient merged by `path_add_sub_eq`. -/
private theorem c2BgPath
    (g gB : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ)
    (hSI : Set.uIcc (0 : ℝ) 1 ⊆ realizedSmallSet (δ := δ) (δ' := δ))
    (hK : linearizedRicciThreeArmHjoint (I := I) (M := M) g 4
      (fun s => rhsRefoldTop (I := I) (M := M) g gB T hδ hδZ s +
          LowBaseInternal.rhsSelfTop (I := I) (M := M) g T hδ hδZ s -
          deTurckPhiMetTotal (I := I) (M := M) g gB g)
      (δ := δ) (δ' := δ)) :
    (lowBaseData (I := I) (M := M) g gB T hδ_lt hδ hδZ).C2 =
      pathIntegralCoeffField (I := I) (M := M) g 4 2
        (fun s => rhsRefoldTop (I := I) (M := M) g gB T hδ hδZ s +
            LowBaseInternal.rhsSelfTop (I := I) (M := M) g T hδ hδZ s -
            deTurckPhiMetTotal (I := I) (M := M) g gB g)
        (realizedSmallSet (δ := δ) (δ' := δ))
        realizedSmallSet_isOpen hSI hK := by
  rw [LowBaseInternal.c2_eq (I := I) (M := M) g gB T hδ_lt hδ hδZ]
  exact path_add_sub_eq (I := I) (M := M) g 4 hSI _ _ _
    (rhsRefoldTop_joint (I := I) (M := M) g gB T hδ_lt hδ hδZ)
    (LowBaseInternal.selfTop_joint (I := I) (M := M) g T hδ hδZ) hK

/-- **The background difference of the two metric deviations is small.**
Along the whole realized segment the deviation at `gB` and the deviation at
`g` are each linear in the `H2` radius by `phi_dev_h2`, so their difference is
too, in both the fibre and the two-jet clause. -/
private theorem devBgCap
    (hDim : Module.finrank ℝ E = 3)
    (g gB : SmoothRiemannianMetric I M) :
    ∃ ρ C : ℝ, 0 < ρ ∧ 0 ≤ C ∧
      ∀ (T : SmoothCcTensor g 0 2) {δ : ℝ} (_hδ_lt : δ < 1)
        (hδ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        {R : ℝ}, 0 ≤ R → R ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ R →
        ∀ s ∈ Set.Icc (0 : ℝ) 1,
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g 4 2 x
            (((deTurckPhiMetTotal (I := I) (M := M) g gB
                  (realizedFam (I := I) g T 0 hδ hδZ s) -
                deTurckPhiMetTotal (I := I) (M := M) g gB g) -
              (deTurckPhiMetTotal (I := I) (M := M) g g
                  (realizedFam (I := I) g T 0 hδ hδZ s) -
                deTurckPhiMetTotal (I := I) (M := M) g g g)).toSection x) ≤
            (C * R) ^ 2) ∧
          lowJetSq (I := I) (M := M) g 2
            ((deTurckPhiMetTotal (I := I) (M := M) g gB
                  (realizedFam (I := I) g T 0 hδ hδZ s) -
                deTurckPhiMetTotal (I := I) (M := M) g gB g) -
              (deTurckPhiMetTotal (I := I) (M := M) g g
                  (realizedFam (I := I) g T 0 hδ hδZ s) -
                deTurckPhiMetTotal (I := I) (M := M) g g g)) ≤ (C * R) ^ 2 := by
  obtain ⟨ρ1, C1, hρ1, hC1, hphiB⟩ := phi_dev_h2 (I := I) (M := M) hDim g gB
  obtain ⟨ρ2, C2, hρ2, hC2, hphiG⟩ := phi_dev_h2 (I := I) (M := M) hDim g g
  refine ⟨min ρ1 ρ2, 2 * (C1 + C2), lt_min hρ1 hρ2, by positivity, ?_⟩
  intro T δ hδ_lt hδ hδZ R hR0 hRρ hTHs s hs
  have hRρ1 : R ≤ ρ1 := hRρ.trans (min_le_left _ _)
  have hRρ2 : R ≤ ρ2 := hRρ.trans (min_le_right _ _)
  have hzeroHs :
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
          (0 : SmoothCcTensor g 0 2)‖ ≤ R := by
    have hz :
        ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
            (0 : SmoothCcTensor g 0 2) = 0 := by
      rw [show (0 : SmoothCcTensor g 0 2) =
          (0 : ℝ) • (0 : SmoothCcTensor g 0 2) by simp,
        ccTensorToHs_smul, zero_smul]
    rw [hz, norm_zero]
    exact hR0
  have hkey : 2 * (C1 * R) ^ 2 + 2 * (C2 * R) ^ 2 ≤ (2 * (C1 + C2) * R) ^ 2 := by
    have hexp : (2 * (C1 + C2) * R) ^ 2 = 4 * (C1 + C2) ^ 2 * R ^ 2 := by ring
    rw [hexp]
    nlinarith [sq_nonneg (C1 * R), sq_nonneg (C2 * R),
      mul_nonneg (mul_nonneg hC1 hC2) (sq_nonneg R)]
  have hB := hphiB T (0 : SmoothCcTensor g 0 2) hδ_lt hδ hδ_lt hδZ
    hR0 hRρ1 hTHs hzeroHs hs.1 hs.2
  have hG := hphiG T (0 : SmoothCcTensor g 0 2) hδ_lt hδ hδ_lt hδZ
    hR0 hRρ2 hTHs hzeroHs hs.1 hs.2
  constructor
  · intro x
    have hBx := hB.1 x
    have hGx := hG.1 x
    have hsub := riemannianFiberNormSq_sub_le (I := I) (M := M) g 4 2 x
      ((deTurckPhiMetTotal (I := I) (M := M) g gB
          (realizedFam (I := I) g T 0 hδ hδZ s) -
        deTurckPhiMetTotal (I := I) (M := M) g gB g).toSection x)
      ((deTurckPhiMetTotal (I := I) (M := M) g g
          (realizedFam (I := I) g T 0 hδ hδZ s) -
        deTurckPhiMetTotal (I := I) (M := M) g g g).toSection x)
    simp only [SmoothCcTensor.toSection_sub, ContMDiffSection.coe_sub,
      Pi.sub_apply] at hsub hBx hGx ⊢
    linarith [hsub, hBx, hGx, hkey]
  · have hBj : lowJetSq (I := I) (M := M) g 2
        (deTurckPhiMetTotal (I := I) (M := M) g gB
            (realizedFam (I := I) g T 0 hδ hδZ s) -
          deTurckPhiMetTotal (I := I) (M := M) g gB g) ≤ (C1 * R) ^ 2 := by
      simpa only [lowJetSq, Nat.reduceAdd] using hB.2
    have hGj : lowJetSq (I := I) (M := M) g 2
        (deTurckPhiMetTotal (I := I) (M := M) g g
            (realizedFam (I := I) g T 0 hδ hδZ s) -
          deTurckPhiMetTotal (I := I) (M := M) g g g) ≤ (C2 * R) ^ 2 := by
      simpa only [lowJetSq, Nat.reduceAdd] using hG.2
    have hsub := jetSub (I := I) (M := M) g 2
      (deTurckPhiMetTotal (I := I) (M := M) g gB
          (realizedFam (I := I) g T 0 hδ hδZ s) -
        deTurckPhiMetTotal (I := I) (M := M) g gB g)
      (deTurckPhiMetTotal (I := I) (M := M) g g
          (realizedFam (I := I) g T 0 hδ hδZ s) -
        deTurckPhiMetTotal (I := I) (M := M) g g g)
    linarith [hsub, hBj, hGj, hkey]

/-- Both smallness clauses pass from a radial integrand to its path integral,
with the same constant. -/
private theorem pathBoth
    (g : SmoothRiemannianMetric I M) {δ : ℝ}
    (hSI : Set.uIcc (0 : ℝ) 1 ⊆ realizedSmallSet (δ := δ) (δ' := δ))
    (D : ℝ → SmoothCcTensor g 4 2)
    (hD : linearizedRicciThreeArmHjoint (I := I) (M := M) g 4 D
      (δ := δ) (δ' := δ))
    {Λ : ℝ} (hΛ : 0 ≤ Λ)
    (hpt : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g 4 2 x
        ((D s).toSection x) ≤ Λ ^ 2)
    (hjet : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      lowJetSq (I := I) (M := M) g 2 (D s) ≤ Λ ^ 2) :
    (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g 4 2 x
        ((pathIntegralCoeffField (I := I) (M := M) g 4 2 D
          (realizedSmallSet (δ := δ) (δ' := δ))
          realizedSmallSet_isOpen hSI hD).toSection x) ≤ Λ ^ 2) ∧
      lowJetSq (I := I) (M := M) g 2
        (pathIntegralCoeffField (I := I) (M := M) g 4 2 D
          (realizedSmallSet (δ := δ) (δ' := δ))
          realizedSmallSet_isOpen hSI hD) ≤ Λ ^ 2 := by
  have hIcc : Set.Icc (0 : ℝ) 1 ⊆ realizedSmallSet (δ := δ) (δ' := δ) := by
    simpa only [Set.uIcc_of_le zero_le_one] using hSI
  constructor
  · intro x
    have hcont := (jointContMDiff_toModel_continuous_slice
      (I := I) g 4 2 D (realizedSmallSet (δ := δ) (δ' := δ)) hD x).mono hIcc
    refine riemannianFiberNormSq_pathIntegralCoeffField_le_sq
      (I := I) (M := M) g 4 2 D (realizedSmallSet (δ := δ) (δ' := δ))
      realizedSmallSet_isOpen hSI hD x Λ hΛ hcont ?_
    intro s hs
    have hsqrt := Real.sqrt_le_sqrt (hpt s hs x)
    simpa only [Real.sqrt_sq hΛ] using hsqrt
  · exact path_jetL2_le (I := I) (M := M) g 4 2 2 D
      (realizedSmallSet (δ := δ) (δ' := δ))
      realizedSmallSet_isOpen hSI hD hΛ (fun s hs => hjet s hs)

/-- **In dimension three, the complete canonical second-order coefficient is
pointwise and two-jet small on a small spectral `H2` ball, at an arbitrary
fixed DeTurck background.**

This is the fixed-background sibling of `c2_h2_small`; the diagonal statement
is consumed as a black box and only the background *difference* is estimated
here.  The `δ`-certificates are unchanged: `lowBaseData g gB T` measures the
state against the carrier `g` alone, so `gB` is a bare parameter. -/
theorem c2Bg_h2_small
    (hDim : Module.finrank ℝ E = 3)
    (g gB : SmoothRiemannianMetric I M) :
    ∃ ρ C : ℝ, 0 < ρ ∧ 0 ≤ C ∧
      ∀ (T : SmoothCcTensor g 0 2)
        (hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        {δ : ℝ} (hδ_le : δ ≤ (1 : ℝ) / 3) (hδ0 : 0 ≤ δ)
        (hδ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        {R : ℝ}, 0 ≤ R → R ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ R →
      let A := lowBaseData (I := I) (M := M) g gB T
        (lt_of_le_of_lt hδ_le (by norm_num)) hδ hδZ
      (∀ x : M,
        riemannianFiberNormSq (I := I) (M := M) g 4 2 x
            (A.C2.toSection x) ≤ (C * R) ^ 2) ∧
        lowJetSq (I := I) (M := M) g 2 A.C2 ≤ (C * R) ^ 2 := by
  classical
  obtain ⟨ρ0, C0, hρ0, hC0, hdiag⟩ := c2_h2_small (I := I) (M := M) hDim g
  obtain ⟨ρd, Cd, hρd, hCd, hdev⟩ := devBgCap (I := I) (M := M) hDim g gB
  let C : ℝ := 2 * (Cd + C0)
  have hC : 0 ≤ C := by positivity
  refine ⟨min ρ0 ρd, C, lt_min hρ0 hρd, hC, ?_⟩
  intro T hT δ hδ_le hδ0 hδ hδZ R hR0 hRρ hTHs
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le (by norm_num)
  have hRρ0 : R ≤ ρ0 := hRρ.trans (min_le_left _ _)
  have hRρd : R ≤ ρd := hRρ.trans (min_le_right _ _)
  -- the shared radial data
  have hSI : Set.uIcc (0 : ℝ) 1 ⊆
      realizedSmallSet (δ := δ) (δ' := δ) := by
    rw [Set.uIcc_of_le zero_le_one]
    exact Icc_subset_realizedSmallSet hδ_lt hδ_lt
  have hjΦB := rhsRefoldTop_joint (I := I) (M := M) g gB T hδ_lt hδ hδZ
  have hjΦG := rhsRefoldTop_joint (I := I) (M := M) g g T hδ_lt hδ hδZ
  have hjΨ := LowBaseInternal.selfTop_joint (I := I) (M := M) g T hδ hδZ
  have hjKerB := threeArmJoint_sub (I := I) (M := M) g _ _
    (threeArmJoint_add (I := I) (M := M) g _ _ hjΦB hjΨ)
    (armConst (I := I) (M := M) g (δ := δ) (δ' := δ)
      (deTurckPhiMetTotal (I := I) (M := M) g gB g))
  have hjKerG := threeArmJoint_sub (I := I) (M := M) g _ _
    (threeArmJoint_add (I := I) (M := M) g _ _ hjΦG hjΨ)
    (armConst (I := I) (M := M) g (δ := δ) (δ' := δ)
      (deTurckPhiMetTotal (I := I) (M := M) g g g))
  have hjD := threeArmJoint_sub (I := I) (M := M) g _ _ hjKerB hjKerG
  -- the two coefficients differ by a single path integral
  have hcB := c2BgPath (I := I) (M := M) g gB T hδ_lt hδ hδZ hSI hjKerB
  have hcG := c2BgPath (I := I) (M := M) g g T hδ_lt hδ hδZ hSI hjKerG
  have hdiff :
      (lowBaseData (I := I) (M := M) g gB T hδ_lt hδ hδZ).C2 -
          (lowBaseData (I := I) (M := M) g g T hδ_lt hδ hδZ).C2 =
        pathIntegralCoeffField (I := I) (M := M) g 4 2
          (fun s =>
            (rhsRefoldTop (I := I) (M := M) g gB T hδ hδZ s +
                LowBaseInternal.rhsSelfTop (I := I) (M := M) g T hδ hδZ s -
                deTurckPhiMetTotal (I := I) (M := M) g gB g) -
              (rhsRefoldTop (I := I) (M := M) g g T hδ hδZ s +
                LowBaseInternal.rhsSelfTop (I := I) (M := M) g T hδ hδZ s -
                deTurckPhiMetTotal (I := I) (M := M) g g g))
          (realizedSmallSet (δ := δ) (δ' := δ))
          realizedSmallSet_isOpen hSI hjD := by
    rw [hcB, hcG]
    exact path_sub_eq (I := I) (M := M) g 4 hSI _ _ hjKerB hjKerG hjD
  -- the integrand difference is small, in both clauses
  have hcapPt : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g 4 2 x
          (((rhsRefoldTop (I := I) (M := M) g gB T hδ hδZ s +
                LowBaseInternal.rhsSelfTop (I := I) (M := M) g T hδ hδZ s -
                deTurckPhiMetTotal (I := I) (M := M) g gB g) -
              (rhsRefoldTop (I := I) (M := M) g g T hδ hδZ s +
                LowBaseInternal.rhsSelfTop (I := I) (M := M) g T hδ hδZ s -
                deTurckPhiMetTotal (I := I) (M := M) g g g)).toSection x) ≤
        (Cd * R) ^ 2 := by
    intro s hs x
    rw [kerBgDiff (I := I) (M := M) g gB T hδ hδZ s]
    exact (hdev T hδ_lt hδ hδZ hR0 hRρd hTHs s hs).1 x
  have hcapJet : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      lowJetSq (I := I) (M := M) g 2
          ((rhsRefoldTop (I := I) (M := M) g gB T hδ hδZ s +
              LowBaseInternal.rhsSelfTop (I := I) (M := M) g T hδ hδZ s -
              deTurckPhiMetTotal (I := I) (M := M) g gB g) -
            (rhsRefoldTop (I := I) (M := M) g g T hδ hδZ s +
              LowBaseInternal.rhsSelfTop (I := I) (M := M) g T hδ hδZ s -
              deTurckPhiMetTotal (I := I) (M := M) g g g)) ≤
        (Cd * R) ^ 2 := by
    intro s hs
    rw [kerBgDiff (I := I) (M := M) g gB T hδ hδZ s]
    exact (hdev T hδ_lt hδ hδZ hR0 hRρd hTHs s hs).2
  have hCdR0 : 0 ≤ Cd * R := mul_nonneg hCd hR0
  -- integrate the difference
  obtain ⟨hdPt, hdJet⟩ := pathBoth (I := I) (M := M) g hSI _ hjD hCdR0
    hcapPt hcapJet
  rw [← hdiff] at hdPt hdJet
  -- the diagonal black box
  have hdg :
      (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g 4 2 x
          ((lowBaseData (I := I) (M := M) g g T hδ_lt hδ hδZ).C2.toSection x) ≤
            (C0 * R) ^ 2) ∧
        lowJetSq (I := I) (M := M) g 2
          (lowBaseData (I := I) (M := M) g g T hδ_lt hδ hδZ).C2 ≤ (C0 * R) ^ 2 :=
    hdiag T hT hδ_le hδ0 hδ hδZ hR0 hRρ0 hTHs
  have hsplit :
      (lowBaseData (I := I) (M := M) g gB T hδ_lt hδ hδZ).C2 =
        ((lowBaseData (I := I) (M := M) g gB T hδ_lt hδ hδZ).C2 -
            (lowBaseData (I := I) (M := M) g g T hδ_lt hδ hδZ).C2) +
          (lowBaseData (I := I) (M := M) g g T hδ_lt hδ hδZ).C2 := by
    abel
  have hkey2 : 2 * (Cd * R) ^ 2 + 2 * (C0 * R) ^ 2 ≤ (C * R) ^ 2 := by
    have hCR : (C * R) ^ 2 = 4 * (Cd + C0) ^ 2 * R ^ 2 := by
      simp only [C]; ring
    rw [hCR]
    nlinarith [sq_nonneg (Cd * R), sq_nonneg (C0 * R),
      mul_nonneg (mul_nonneg hCd hC0) (sq_nonneg R)]
  change
    (∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g 4 2 x
          ((lowBaseData (I := I) (M := M) g gB T hδ_lt hδ hδZ).C2.toSection x) ≤
        (C * R) ^ 2) ∧
      lowJetSq (I := I) (M := M) g 2
        (lowBaseData (I := I) (M := M) g gB T hδ_lt hδ hδZ).C2 ≤ (C * R) ^ 2
  constructor
  · intro x
    have hd := hdPt x
    have hg := hdg.1 x
    rw [hsplit]
    have hadd := riemannianFiberNormSq_add_le (I := I) (M := M) g 4 2 x
      (((lowBaseData (I := I) (M := M) g gB T hδ_lt hδ hδZ).C2 -
        (lowBaseData (I := I) (M := M) g g T hδ_lt hδ hδZ).C2).toSection x)
      ((lowBaseData (I := I) (M := M) g g T hδ_lt hδ hδZ).C2.toSection x)
    simp only [SmoothCcTensor.toSection_add, SmoothCcTensor.toSection_sub,
      ContMDiffSection.coe_add, ContMDiffSection.coe_sub,
      Pi.add_apply, Pi.sub_apply] at hadd hd ⊢
    linarith [hadd, hd, hg, hkey2]
  · rw [hsplit]
    have hadd := opJetAdd (I := I) (M := M) g 2
      ((lowBaseData (I := I) (M := M) g gB T hδ_lt hδ hδZ).C2 -
        (lowBaseData (I := I) (M := M) g g T hδ_lt hδ hδZ).C2)
      (lowBaseData (I := I) (M := M) g g T hδ_lt hδ hδZ).C2
    linarith [hadd, hdJet, hdg.2, hkey2]

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
