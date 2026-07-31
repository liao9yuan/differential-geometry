import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.PrincipalResidualH2
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderLowBaseC1Lip
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderLowBasePair

/-!
# Pairwise low-base Ricci--DeTurck remainder

This module records the exact coefficient difference which remains after
subtracting the complete canonical second-order low-base action.  It does not
replace the missing fixed-order coefficient-difference estimate by an
assumption.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Bundle Manifold Tensor0SBundle
open scoped BigOperators Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.PDE.DeTurck.RicciLinearization
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurckCoefficients
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

/-- Difference of the first-order coefficients of two low-base action data
bundles.  Its second-order coefficient is exactly zero. -/
noncomputable def LowBaseActionData.a1Sub
    {g : SmoothRiemannianMetric I M}
    (A B : LowBaseActionData g) : LowBaseActionData g where
  C0 := A.C0 - B.C0
  C1 := A.C1 - B.C1
  C2 := 0

private theorem app_sub_right
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (Φ : SmoothCcTensor g r s) (W V : SmoothCcTensor g 0 r) :
    appCc (I := I) (M := M) g r s Φ (W - V) =
      appCc (I := I) (M := M) g r s Φ W -
        appCc (I := I) (M := M) g r s Φ V := by
  rw [sub_eq_add_neg, appCc_add_right]
  have hneg := appCc_smul_right (I := I) (M := M) g r s
    (-1 : ℝ) Φ V
  simp only [neg_one_smul] at hneg
  rw [hneg]
  rfl

/-- The canonical difference of the zero-based low-base first-order
coefficients at two perturbations. -/
noncomputable def lowBaseDiff
    (g : SmoothRiemannianMetric I M)
    (T U : SmoothCcTensor g 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδT : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδU : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g U) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ) :
    LowBaseActionData g :=
  (lowBaseData (I := I) (M := M) g g T hδ_lt hδT hδZ).a1Sub
    (lowBaseData (I := I) (M := M) g g U hδ_lt hδU hδZ)

/-- Pointwise splitting of the radial order-one coefficient difference into
its Ricci connection-difference and DeTurck--Lie arms. -/
theorem rhsLow1_sub
    (g : SmoothRiemannianMetric I M)
    (T U : SmoothCcTensor g 0 2)
    {δ : ℝ}
    (hδT : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδU : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g U) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ)
    (s : ℝ) :
    rhsLow1Coeff (I := I) (M := M) g g T 0 hδT hδZ s -
        rhsLow1Coeff (I := I) (M := M) g g U 0 hδU hδZ s =
      (-2 : ℝ) •
          (linearizedRicciConnDiffOrder1Coeff
              (I := I) g T 0 hδT hδZ s -
            linearizedRicciConnDiffOrder1Coeff
              (I := I) g U 0 hδU hδZ s) +
        (deTurckLieArm1Coeff (I := I) (M := M) g
            (realizedFam (I := I) g T 0 hδT hδZ s) g -
          deTurckLieArm1Coeff (I := I) (M := M) g
            (realizedFam (I := I) g U 0 hδU hδZ s) g) := by
  simp only [rhsLow1Coeff, smul_sub]
  abel

/-- The integrated difference of the two radial order-one coefficient
families.  This is the exact pairwise producer underlying the `C1` component
of `lowBaseDiff`. -/
noncomputable def lowC1Diff
    (g : SmoothRiemannianMetric I M)
    (T U : SmoothCcTensor g 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδT : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδU : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g U) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ) :
    SmoothCcTensor g 3 2 :=
  pathIntegralCoeffField (I := I) (M := M) g 3 2
    (fun s =>
      rhsLow1Coeff (I := I) (M := M) g g T 0 hδT hδZ s -
        rhsLow1Coeff (I := I) (M := M) g g U 0 hδU hδZ s)
    (realizedSmallSet (δ := δ) (δ' := δ))
    realizedSmallSet_isOpen
    (by
      rw [Set.uIcc_of_le zero_le_one]
      exact Icc_subset_realizedSmallSet hδ_lt hδ_lt)
    (threeArmJoint_sub (I := I) (M := M) g _ _
      (rhsLow1_path_joint (I := I) (M := M) g g T 0 hδT hδZ)
      (rhsLow1_path_joint (I := I) (M := M) g g U 0 hδU hδZ))

/-- The `C1` coefficient difference in the canonical low-base data is exactly
the path integral of the pointwise radial-family difference. -/
theorem lowC1_sub
    (g : SmoothRiemannianMetric I M)
    (T U : SmoothCcTensor g 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδT : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδU : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g U) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ) :
    (lowBaseData (I := I) (M := M) g g T hδ_lt hδT hδZ).C1 -
        (lowBaseData (I := I) (M := M) g g U hδ_lt hδU hδZ).C1 =
      lowC1Diff (I := I) (M := M) g T U hδ_lt hδT hδU hδZ := by
  classical
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply TensorRSSpace.toModel_injective
  have hSI : Set.uIcc (0 : ℝ) 1 ⊆
      realizedSmallSet (δ := δ) (δ' := δ) := by
    rw [Set.uIcc_of_le zero_le_one]
    exact Icc_subset_realizedSmallSet hδ_lt hδ_lt
  have hTcont :=
    jointContMDiff_toModel_continuous_slice
      (I := I) g 3 2
      (fun s => rhsLow1Coeff (I := I) (M := M) g g
        T 0 hδT hδZ s)
      (realizedSmallSet (δ := δ) (δ' := δ))
      (rhsLow1_path_joint (I := I) (M := M) g g T 0 hδT hδZ) x
  have hUcont :=
    jointContMDiff_toModel_continuous_slice
      (I := I) g 3 2
      (fun s => rhsLow1Coeff (I := I) (M := M) g g
        U 0 hδU hδZ s)
      (realizedSmallSet (δ := δ) (δ' := δ))
      (rhsLow1_path_joint (I := I) (M := M) g g U 0 hδU hδZ) x
  have hTint : IntervalIntegrable
      (fun s : ℝ => TensorRSSpace.toModel
        ((rhsLow1Coeff (I := I) (M := M) g g
          T 0 hδT hδZ s).toSection x))
      MeasureTheory.volume 0 1 :=
    (hTcont.mono hSI).intervalIntegrable
  have hUint : IntervalIntegrable
      (fun s : ℝ => TensorRSSpace.toModel
        ((rhsLow1Coeff (I := I) (M := M) g g
          U 0 hδU hδZ s).toSection x))
      MeasureTheory.volume 0 1 :=
    (hUcont.mono hSI).intervalIntegrable
  simp only [lowBaseData, rhsLow1PathIntegral, lowC1Diff,
    pathIntegralCoeffField_toModel, SmoothCcTensor.toSection_sub,
    ContMDiffSection.coe_sub, Pi.sub_apply, TensorRSSpace.toModel_sub]
  rw [intervalIntegral.integral_sub hTint hUint]

/-- The integrated difference of the two transparent zero-arm self-action
families.  The fixed background-curvature coefficient is not part of this
difference. -/
noncomputable def lowC0Diff
    (g : SmoothRiemannianMetric I M)
    (T U : SmoothCcTensor g 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδT : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδU : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g U) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ) :
    SmoothCcTensor g 2 2 :=
  pathIntegralCoeffField (I := I) (M := M) g 2 2
    (fun s =>
      LowBaseInternal.rhsSelfLow (I := I) (M := M)
          g g T hδT hδZ s -
        LowBaseInternal.rhsSelfLow (I := I) (M := M)
          g g U hδU hδZ s)
    (realizedSmallSet (δ := δ) (δ' := δ))
    realizedSmallSet_isOpen
    (by
      rw [Set.uIcc_of_le zero_le_one]
      exact Icc_subset_realizedSmallSet hδ_lt hδ_lt)
    (threeArmJoint_sub (I := I) (M := M) g _ _
      (LowBaseInternal.selfLow_joint
        (I := I) (M := M) g g T hδT hδZ)
      (LowBaseInternal.selfLow_joint
        (I := I) (M := M) g g U hδU hδZ))

private theorem selfLow_parts
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    (hT : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g T x u v =
        ccTensorBilin (I := I) g T x v u)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ)
    {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    LowBaseInternal.rhsSelfLow (I := I) (M := M)
        g g T hδ hδZ s =
      let gm := realizedFam (I := I) g T 0 hδ hδZ s
      ((((-2 : ℝ) •
            LowBaseInternal.ricciGoodLow
              (I := I) (M := M) g gm (s • T) +
          (deTurckLieCovDerivArmField (I := I) (M := M) g gm g -
            edgeLiePairFam (I := I) (M := M) g T hδ hδZ
              lieRefoldQ lieRefoldEps s)) +
        lc0VB (I := I) (M := M) g gm) +
        lc0AMix (I := I) (M := M) g gm g) +
        lc0Riem (I := I) (M := M) g gm := by
  rw [LowBaseInternal.selfLow_good
    (I := I) (M := M) g g T hT hδ_lt hδ hδZ hs]
  let gm := realizedFam (I := I) g T 0 hδ hδZ s
  let Q := edgeLiePairFam (I := I) (M := M) g T hδ hδZ
    lieRefoldQ lieRefoldEps s
  have hlie :
      deTurckLieCoeffField (I := I) (M := M) g gm g +
            lieCorr0Field (I := I) (M := M) g gm g - Q =
        (deTurckLieCovDerivArmField (I := I) (M := M) g gm g - Q) +
          (deTurckLieEndoArmField (I := I) (M := M) g gm g -
            deTurckLieEndoArmField (I := I) (M := M) g gm g) +
          ((((lc0Insert (I := I) (M := M) g gm g -
                lc0Insert (I := I) (M := M) g gm g) +
              lc0VB (I := I) (M := M) g gm) +
            lc0AMix (I := I) (M := M) g gm g) +
          lc0Riem (I := I) (M := M) g gm) := by
    rw [deTurckLieCoeffField_eq_covDerivArm_add_endoArm]
    rw [← tail_base_split (I := I) (M := M) g gm g]
    abel
  calc
    _ = (-2 : ℝ) •
          LowBaseInternal.ricciGoodLow
            (I := I) (M := M) g gm (s • T) +
        (deTurckLieCoeffField (I := I) (M := M) g gm g +
          lieCorr0Field (I := I) (M := M) g gm g - Q) := by
      simp only [gm, Q]
      abel
    _ = (-2 : ℝ) •
          LowBaseInternal.ricciGoodLow
            (I := I) (M := M) g gm (s • T) +
        ((deTurckLieCovDerivArmField (I := I) (M := M) g gm g - Q) +
          (deTurckLieEndoArmField (I := I) (M := M) g gm g -
            deTurckLieEndoArmField (I := I) (M := M) g gm g) +
          ((((lc0Insert (I := I) (M := M) g gm g -
                lc0Insert (I := I) (M := M) g gm g) +
              lc0VB (I := I) (M := M) g gm) +
            lc0AMix (I := I) (M := M) g gm g) +
          lc0Riem (I := I) (M := M) g gm)) := by
      rw [hlie]
    _ = _ := by
      simp only [sub_self, zero_add, add_zero]
      abel

/-- The `C0` coefficient difference in the canonical low-base data is exactly
the path integral of the transparent zero-arm family difference. -/
theorem lowC0_sub
    (g : SmoothRiemannianMetric I M)
    (T U : SmoothCcTensor g 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδT : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδU : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g U) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ) :
    (lowBaseData (I := I) (M := M) g g T hδ_lt hδT hδZ).C0 -
        (lowBaseData (I := I) (M := M) g g U hδ_lt hδU hδZ).C0 =
      lowC0Diff (I := I) (M := M) g T U hδ_lt hδT hδU hδZ := by
  classical
  have hSI : Set.uIcc (0 : ℝ) 1 ⊆
      realizedSmallSet (δ := δ) (δ' := δ) := by
    rw [Set.uIcc_of_le zero_le_one]
    exact Icc_subset_realizedSmallSet hδ_lt hδ_lt
  have hTcont :=
    jointContMDiff_toModel_continuous_slice
      (I := I) g 2 2
      (LowBaseInternal.rhsSelfLow
        (I := I) (M := M) g g T hδT hδZ)
      (realizedSmallSet (δ := δ) (δ' := δ))
      (LowBaseInternal.selfLow_joint
        (I := I) (M := M) g g T hδT hδZ)
  have hUcont :=
    jointContMDiff_toModel_continuous_slice
      (I := I) g 2 2
      (LowBaseInternal.rhsSelfLow
        (I := I) (M := M) g g U hδU hδZ)
      (realizedSmallSet (δ := δ) (δ' := δ))
      (LowBaseInternal.selfLow_joint
        (I := I) (M := M) g g U hδU hδZ)
  have hInt :
      LowBaseInternal.selfLowInt (I := I) (M := M)
            g g T hδ_lt hδT hδZ -
          LowBaseInternal.selfLowInt (I := I) (M := M)
            g g U hδ_lt hδU hδZ =
        lowC0Diff (I := I) (M := M)
          g T U hδ_lt hδT hδU hδZ := by
    apply SmoothCcTensor.ext
    apply ContMDiffSection.ext
    intro x
    apply TensorRSSpace.toModel_injective
    have hTint : IntervalIntegrable
        (fun s : ℝ => TensorRSSpace.toModel
          ((LowBaseInternal.rhsSelfLow
            (I := I) (M := M) g g T hδT hδZ s).toSection x))
        MeasureTheory.volume 0 1 :=
      ((hTcont x).mono hSI).intervalIntegrable
    have hUint : IntervalIntegrable
        (fun s : ℝ => TensorRSSpace.toModel
          ((LowBaseInternal.rhsSelfLow
            (I := I) (M := M) g g U hδU hδZ s).toSection x))
        MeasureTheory.volume 0 1 :=
      ((hUcont x).mono hSI).intervalIntegrable
    simp only [LowBaseInternal.selfLowInt, lowC0Diff,
      pathIntegralCoeffField_toModel, SmoothCcTensor.toSection_sub,
      ContMDiffSection.coe_sub, Pi.sub_apply, TensorRSSpace.toModel_sub]
    rw [intervalIntegral.integral_sub hTint hUint]
  rw [LowBaseInternal.c0_eq, LowBaseInternal.c0_eq]
  calc
    (LowBaseInternal.selfLowInt (I := I) (M := M)
          g g T hδ_lt hδT hδZ +
        phiMetCurvCoeff (I := I) g g g) -
        (LowBaseInternal.selfLowInt (I := I) (M := M)
          g g U hδ_lt hδU hδZ +
        phiMetCurvCoeff (I := I) g g g) =
      LowBaseInternal.selfLowInt (I := I) (M := M)
          g g T hδ_lt hδT hδZ -
        LowBaseInternal.selfLowInt (I := I) (M := M)
          g g U hδ_lt hδU hδZ := by
      abel
    _ = lowC0Diff (I := I) (M := M)
        g T U hδ_lt hδT hδU hδZ := hInt

/-- The `C1` projection of the canonical pairwise bundle is the explicit
path-integrated family difference. -/
theorem lowBaseDiff_c1
    (g : SmoothRiemannianMetric I M)
    (T U : SmoothCcTensor g 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδT : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδU : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g U) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ) :
    (lowBaseDiff (I := I) (M := M) g T U
        hδ_lt hδT hδU hδZ).C1 =
      lowC1Diff (I := I) (M := M) g T U
        hδ_lt hδT hδU hδZ := by
  simpa only [lowBaseDiff, LowBaseActionData.a1Sub] using
    lowC1_sub (I := I) (M := M) g T U hδ_lt hδT hδU hδZ

/-- The `C0` projection of the canonical pairwise bundle is the explicit
path-integrated transparent self-action difference. -/
theorem lowBaseDiff_c0
    (g : SmoothRiemannianMetric I M)
    (T U : SmoothCcTensor g 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδT : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδU : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g U) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ) :
    (lowBaseDiff (I := I) (M := M) g T U
        hδ_lt hδT hδU hδZ).C0 =
      lowC0Diff (I := I) (M := M) g T U
        hδ_lt hδT hδU hδZ := by
  simpa only [lowBaseDiff, LowBaseActionData.a1Sub] using
    lowC0_sub (I := I) (M := M) g T U hδ_lt hδT hδU hδZ

/-- Radius-free H2 Lipschitz control in the explicit perturbation slot of the
moving-lowering correction.  This is one genuine telescope arm in the
pairwise `C0` coefficient difference. -/
theorem metricCorr_sub_h2
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (g₁ g_bg : SmoothRiemannianMetric I M)
        (P Q : SmoothCcTensor g 0 2),
        lowJetSq (I := I) (M := M) g 2
            (metricLowerCorr (I := I) (M := M) g g₁ g_bg P -
              metricLowerCorr (I := I) (M := M) g g₁ g_bg Q) ≤
          C * lowJetSq (I := I) (M := M) g 2 (P - Q) *
            lowJetSq (I := I) (M := M) g 2
              (wXi (I := I) (M := M) g g₁ g_bg) := by
  obtain ⟨C, hC, hmul⟩ :=
    metricCorr_h2_mul (I := I) (M := M) hDim g
  refine ⟨C, hC, ?_⟩
  intro g₁ g_bg P Q
  rw [← metricCorr_sub (I := I) (M := M) g g₁ g_bg P Q]
  simpa only [lowJetSq, Nat.reduceAdd] using hmul g₁ g_bg (P - Q)

/-- Exact two-slot telescope for the moving-lowering correction.  The first
summand is controlled by `metricCorr_sub_h2`; the second isolates the remaining
moving-metric coefficient difference. -/
theorem metricCorr_tel
    (g gT gU g_bg : SmoothRiemannianMetric I M)
    (T U : SmoothCcTensor g 0 2) :
    metricLowerCorr (I := I) (M := M) g gT g_bg T -
        metricLowerCorr (I := I) (M := M) g gU g_bg U =
      metricLowerCorr (I := I) (M := M) g gT g_bg (T - U) +
        (metricLowerCorr (I := I) (M := M) g gT g_bg U -
          metricLowerCorr (I := I) (M := M) g gU g_bg U) := by
  rw [metricCorr_sub (I := I) (M := M) g gT g_bg T U]
  abel

/-- The fixed DeTurck background cancels from the pairwise difference of the
background-lowered connection arm. -/
theorem wXi_sub
    (g gT gU g_bg : SmoothRiemannianMetric I M) :
    wXi (I := I) (M := M) g gT g_bg -
        wXi (I := I) (M := M) g gU g_bg =
      connDiffLoweredCc (I := I) g gT -
        connDiffLoweredCc (I := I) g gU := by
  simp only [wXi]
  abel

omit [BoundarylessManifold I M] in
private theorem jet_nonneg_lip
    (g : SmoothRiemannianMetric I M) {r s m : ℕ}
    (S : SmoothCcTensor g r s) :
    0 ≤ lowJetSq (I := I) (M := M) g m S :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

private theorem jet_smul_lip
    (g : SmoothRiemannianMetric I M) {r s : ℕ} (m : ℕ)
    (c : ℝ) (S : SmoothCcTensor g r s) :
    lowJetSq (I := I) (M := M) g m (c • S) =
      c ^ 2 * lowJetSq (I := I) (M := M) g m S := by
  unfold lowJetSq
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q _
  rw [iteratedCovGrad_smul, norm_smul, Real.norm_eq_abs,
    mul_pow, sq_abs]

private theorem jet_add_lip
    (g : SmoothRiemannianMetric I M) {r s : ℕ} (m : ℕ)
    (S V : SmoothCcTensor g r s) :
    lowJetSq (I := I) (M := M) g m (S + V) ≤
      2 * (lowJetSq (I := I) (M := M) g m S +
        lowJetSq (I := I) (M := M) g m V) := by
  unfold lowJetSq
  calc
    ∑ q ∈ Finset.range (m + 1),
        ‖iteratedCovGrad (I := I) g r s q (S + V)‖ ^ 2 ≤
        ∑ q ∈ Finset.range (m + 1),
          2 * (‖iteratedCovGrad (I := I) g r s q S‖ ^ 2 +
            ‖iteratedCovGrad (I := I) g r s q V‖ ^ 2) := by
      refine Finset.sum_le_sum fun q _ => ?_
      rw [iteratedCovGrad_add]
      have htri := norm_add_le
        (iteratedCovGrad (I := I) g r s q S)
        (iteratedCovGrad (I := I) g r s q V)
      calc
        ‖iteratedCovGrad (I := I) g r s q S +
            iteratedCovGrad (I := I) g r s q V‖ ^ 2 ≤
            (‖iteratedCovGrad (I := I) g r s q S‖ +
              ‖iteratedCovGrad (I := I) g r s q V‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) htri 2
        _ ≤ 2 * (‖iteratedCovGrad (I := I) g r s q S‖ ^ 2 +
            ‖iteratedCovGrad (I := I) g r s q V‖ ^ 2) := by
          nlinarith [sq_nonneg
            (‖iteratedCovGrad (I := I) g r s q S‖ -
              ‖iteratedCovGrad (I := I) g r s q V‖)]
    _ = 2 * ((∑ q ∈ Finset.range (m + 1),
          ‖iteratedCovGrad (I := I) g r s q S‖ ^ 2) +
        ∑ q ∈ Finset.range (m + 1),
          ‖iteratedCovGrad (I := I) g r s q V‖ ^ 2) := by
      simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]

set_option maxHeartbeats 1800000 in
set_option synthInstance.maxHeartbeats 1800000 in
/-- On a common spectral `H²` ball, the path-integrated order-one
Ricci--DeTurck coefficient has the critical `H³/H²` two-arm modulus. -/
theorem c1Diff_tame
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ B0 B1 : ℝ,
      0 < ρ ∧ 0 ≤ B0 ∧ 0 ≤ B1 ∧
      ∀ (T U : SmoothCcTensor g 0 2)
        (hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        (hU : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g U x u v =
            ccTensorBilin (I := I) g U x v u)
        {δ : ℝ} (hδ_le : δ ≤ (1 : ℝ) / 3) (hδ0 : 0 ≤ δ)
        (hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδU : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g U) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ),
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ ≤ ρ →
        ∀ (A D3 : ℝ), 0 ≤ A → 0 ≤ D3 →
        lowJetSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
        lowJetSq (I := I) (M := M) g 3 (T - U) ≤ D3 ^ 2 →
      lowJetSq (I := I) (M := M) g 2
          (lowC1Diff (I := I) (M := M) g T U
            (lt_of_le_of_lt hδ_le
              (by norm_num : (1 : ℝ) / 3 < 1))
            hδT hδU hδZ) ≤
        (B0 * D3 +
          B1 * ‖ccTensorToHs (I := I) (M := M)
            g 2 (2 : ℝ) (T - U)‖ +
          B1 * A * ‖ccTensorToHs (I := I) (M := M)
            g 2 (2 : ℝ) (T - U)‖) ^ 2 := by
  obtain ⟨ρ, B0, B1, hρ, hB0, hB1, hkernel⟩ :=
    rhs1_pair_h2 (I := I) (M := M) hDim g
  refine ⟨ρ, B0, B1, hρ, hB0, hB1, ?_⟩
  intro T U hT hU δ hδ_le hδ0 hδT hδU hδZ
    hTHs hUHs A D3 hA hD3 hT3 hTU3
  let hδ_lt : δ < 1 :=
    lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)
  let Φ : ℝ → SmoothCcTensor g 3 2 := fun s =>
    rhsLow1Coeff (I := I) (M := M) g g T 0 hδT hδZ s -
      rhsLow1Coeff (I := I) (M := M) g g U 0 hδU hδZ s
  let S : Set ℝ := realizedSmallSet (δ := δ) (δ' := δ)
  let N : ℝ :=
    ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U)‖
  let B : ℝ := B0 * D3 + B1 * N + B1 * A * N
  have hN : 0 ≤ N := norm_nonneg _
  have hB : 0 ≤ B :=
    add_nonneg
      (add_nonneg (mul_nonneg hB0 hD3) (mul_nonneg hB1 hN))
      (mul_nonneg (mul_nonneg hB1 hA) hN)
  have hSI : Set.uIcc (0 : ℝ) 1 ⊆ S := by
    dsimp only [S]
    rw [Set.uIcc_of_le zero_le_one]
    exact Icc_subset_realizedSmallSet hδ_lt hδ_lt
  have hjoint :
      linearizedRicciThreeArmHjoint (I := I) (M := M) g 3 Φ
        (δ := δ) (δ' := δ) := by
    dsimp only [Φ]
    exact threeArmJoint_sub (I := I) (M := M) g _ _
      (rhsLow1_path_joint (I := I) (M := M)
        g g T 0 hδT hδZ)
      (rhsLow1_path_joint (I := I) (M := M)
        g g U 0 hδU hδZ)
  have hpoint :
      ∀ s ∈ Set.Icc (0 : ℝ) 1,
        lowJetSq (I := I) (M := M) g 2 (Φ s) ≤ B ^ 2 := by
    intro s hs
    let P : SmoothCcTensor g 0 2 := s • T
    let Q : SmoothCcTensor g 0 2 := s • U
    let gmT : SmoothRiemannianMetric I M :=
      realizedFam (I := I) g T 0 hδT hδZ s
    let gmU : SmoothRiemannianMetric I M :=
      realizedFam (I := I) g U 0 hδU hδZ s
    have hs_mem : s ∈ realizedSmallSet (δ := δ) (δ' := δ) :=
      Icc_subset_realizedSmallSet hδ_lt hδ_lt hs
    have hsabs : ‖s‖ ≤ (1 : ℝ) := by
      rw [Real.norm_eq_abs, abs_of_nonneg hs.1]
      exact hs.2
    have hs2 : s ^ 2 ≤ (1 : ℝ) := by
      nlinarith [hs.1, hs.2]
    have hPsymm : ∀ (x : M) (u v : TangentSpace I x),
        ccTensorBilin (I := I) g P x u v =
          ccTensorBilin (I := I) g P x v u := by
      intro x u v
      simp only [P, ccTensorBilin_apply, ccTensorModel_smul,
        ContinuousMultilinearMap.smul_apply, smul_eq_mul]
      apply congrArg (fun z : ℝ => s * z)
      simpa only [ccTensorBilin_apply] using hT x u v
    have hQsymm : ∀ (x : M) (u v : TangentSpace I x),
        ccTensorBilin (I := I) g Q x u v =
          ccTensorBilin (I := I) g Q x v u := by
      intro x u v
      simp only [Q, ccTensorBilin_apply, ccTensorModel_smul,
        ContinuousMultilinearMap.smul_apply, smul_eq_mul]
      apply congrArg (fun z : ℝ => s * z)
      simpa only [ccTensorBilin_apply] using hU x u v
    have hPtie : ∀ (x : M) (u v : TangentSpace I x),
        gmT.inner x u v =
          g.inner x u v + ccTensorBilinSymm (I := I) g P x u v := by
      intro x u v
      simpa only [gmT, P, convexPerturbation, smul_zero, zero_add] using
        realizedFam_inner_of_mem
          (I := I) g T 0 hδT hδZ hs_mem x u v
    have hQtie : ∀ (x : M) (u v : TangentSpace I x),
        gmU.inner x u v =
          g.inner x u v + ccTensorBilinSymm (I := I) g Q x u v := by
      intro x u v
      simpa only [gmU, Q, convexPerturbation, smul_zero, zero_add] using
        realizedFam_inner_of_mem
          (I := I) g U 0 hδU hδZ hs_mem x u v
    have hδP : gFibreOpBound (I := I) (M := M) g
        (ccTensorBilinSymm (I := I) g P) δ := by
      intro x u v
      have hraw :=
        convexPerturbation_gFibreOpBound_abs
          (I := I) g T 0 hδT hδZ s x u v
      have heq : |1 - s| * δ + |s| * δ = δ := by
        rw [abs_of_nonneg (by linarith [hs.2] : (0 : ℝ) ≤ 1 - s),
          abs_of_nonneg hs.1]
        ring
      simpa only [P, convexPerturbation, smul_zero, zero_add, heq] using hraw
    have hδQ : gFibreOpBound (I := I) (M := M) g
        (ccTensorBilinSymm (I := I) g Q) δ := by
      intro x u v
      have hraw :=
        convexPerturbation_gFibreOpBound_abs
          (I := I) g U 0 hδU hδZ s x u v
      have heq : |1 - s| * δ + |s| * δ = δ := by
        rw [abs_of_nonneg (by linarith [hs.2] : (0 : ℝ) ≤ 1 - s),
          abs_of_nonneg hs.1]
        ring
      simpa only [Q, convexPerturbation, smul_zero, zero_add, heq] using hraw
    have hPnorm :
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) P‖ ≤ ρ := by
      rw [show P = s • T from rfl, ccTensorToHs_smul, norm_smul]
      exact (mul_le_mul_of_nonneg_right hsabs (norm_nonneg _)).trans
        (by simpa using hTHs)
    have hQnorm :
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) Q‖ ≤ ρ := by
      rw [show Q = s • U from rfl, ccTensorToHs_smul, norm_smul]
      exact (mul_le_mul_of_nonneg_right hsabs (norm_nonneg _)).trans
        (by simpa using hUHs)
    have hP3 :
        lowJetSq (I := I) (M := M) g 3 P ≤ A ^ 2 := by
      rw [show P = s • T from rfl, jet_smul_lip]
      calc
        s ^ 2 * lowJetSq (I := I) (M := M) g 3 T ≤
            1 * lowJetSq (I := I) (M := M) g 3 T :=
          mul_le_mul_of_nonneg_right hs2
            (jet_nonneg_lip (I := I) (M := M) g T)
        _ ≤ A ^ 2 := by simpa using hT3
    have hPQeq : P - Q = s • (T - U) := by
      dsimp only [P, Q]
      module
    have hPQ3 :
        lowJetSq (I := I) (M := M) g 3 (P - Q) ≤ D3 ^ 2 := by
      rw [hPQeq, jet_smul_lip]
      calc
        s ^ 2 * lowJetSq (I := I) (M := M) g 3 (T - U) ≤
            1 * lowJetSq (I := I) (M := M) g 3 (T - U) :=
          mul_le_mul_of_nonneg_right hs2
            (jet_nonneg_lip (I := I) (M := M) g (T - U))
        _ ≤ D3 ^ 2 := by simpa using hTU3
    have hPQ2 :
        ‖ccTensorToHs (I := I) (M := M) g
          2 (2 : ℝ) (P - Q)‖ ≤ N := by
      rw [hPQeq, ccTensorToHs_smul, norm_smul]
      exact (mul_le_mul_of_nonneg_right hsabs hN).trans (by simp)
    have hraw :
        lowJetSq (I := I) (M := M) g 2
            ((-2 : ℝ) •
                (linearizedRicciConnDiffOrder1CoeffField
                    (I := I) (M := M) g gmT -
                  linearizedRicciConnDiffOrder1CoeffField
                    (I := I) (M := M) g gmU) +
              (deTurckLieArm1Coeff (I := I) (M := M) g gmT g -
                deTurckLieArm1Coeff (I := I) (M := M) g gmU g)) ≤
          (B0 * D3 +
            B1 * ‖ccTensorToHs (I := I) (M := M)
              g 2 (2 : ℝ) (P - Q)‖ +
            B1 * A * ‖ccTensorToHs (I := I) (M := M)
              g 2 (2 : ℝ) (P - Q)‖) ^ 2 := by
      simpa only [gmT, gmU] using
        hkernel gmT gmU P Q hPsymm hQsymm hPtie hQtie
          hδ_le hδ0 hδP hδQ hδZ hPnorm hQnorm
          A D3 hA hD3 hP3 hPQ3
    have hbase0 :
        0 ≤ B0 * D3 +
          B1 * ‖ccTensorToHs (I := I) (M := M)
            g 2 (2 : ℝ) (P - Q)‖ +
          B1 * A * ‖ccTensorToHs (I := I) (M := M)
            g 2 (2 : ℝ) (P - Q)‖ :=
      add_nonneg
        (add_nonneg (mul_nonneg hB0 hD3)
          (mul_nonneg hB1 (norm_nonneg _)))
        (mul_nonneg (mul_nonneg hB1 hA) (norm_nonneg _))
    have hbase :
        B0 * D3 +
            B1 * ‖ccTensorToHs (I := I) (M := M)
              g 2 (2 : ℝ) (P - Q)‖ +
            B1 * A * ‖ccTensorToHs (I := I) (M := M)
              g 2 (2 : ℝ) (P - Q)‖ ≤ B := by
      dsimp only [B]
      have h1 := mul_le_mul_of_nonneg_left hPQ2 hB1
      have h2 := mul_le_mul_of_nonneg_left hPQ2 (mul_nonneg hB1 hA)
      dsimp only [N] at h1 h2 ⊢
      linarith
    have hΦeq :
        Φ s =
          (-2 : ℝ) •
              (linearizedRicciConnDiffOrder1CoeffField
                  (I := I) (M := M) g gmT -
                linearizedRicciConnDiffOrder1CoeffField
                  (I := I) (M := M) g gmU) +
            (deTurckLieArm1Coeff (I := I) (M := M) g gmT g -
              deTurckLieArm1Coeff (I := I) (M := M) g gmU g) := by
      dsimp only [Φ, gmT, gmU]
      rw [rhsLow1_sub (I := I) (M := M) g T U hδT hδU hδZ s]
      rfl
    rw [hΦeq]
    exact hraw.trans (pow_le_pow_left₀ hbase0 hbase 2)
  have hpath := path_jetL2_le (I := I) (M := M)
    g 3 2 2 Φ S realizedSmallSet_isOpen hSI hjoint
    (B := B) hB hpoint
  simpa only [lowJetSq, lowC1Diff, Φ, S, N, B, Nat.reduceAdd,
    hδ_lt] using hpath

private theorem riemLive_eq
    (g gm : SmoothRiemannianMetric I M) :
    lc0RiemLive (I := I) (M := M) g gm =
      pureTrace (I := I) (M := M) g gm 2 := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  change
    (show Tensor0SSpace 4 I x →L[ℝ] Tensor0SSpace 2 I x from
      (lc0RiemLive (I := I) (M := M) g gm).toSection x) =
    (show Tensor0SSpace 4 I x →L[ℝ] Tensor0SSpace 2 I x from
      (pureTrace (I := I) (M := M) g gm 2).toSection x)
  calc
    _ = cometricDoubleTraceFib (I := I) gm 2 x :=
      lc0RiemLive_fiber (I := I) (M := M) g gm x
    _ = _ := (pureTrace_toSection
      (I := I) (M := M) g gm 2 x).symm

set_option maxHeartbeats 1800000 in
/-- The curvature passenger in the transparent zero-arm decomposition is
locally `H²`-Lipschitz in the moving metric, with only an `H²` state
difference on the right. -/
theorem riem_pair_h2
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ C : ℝ, 0 < ρ ∧ 0 ≤ C ∧
      ∀ (T U : SmoothCcTensor g 0 2)
        (gT gU : SmoothRiemannianMetric I M),
        (∀ (x : M) (u v : TangentSpace I x),
          gT.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g T x u v) →
        (∀ (x : M) (u v : TangentSpace I x),
          gU.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g U x u v) →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ ≤ ρ →
        lowJetSq (I := I) (M := M) g 2
            (lc0Riem (I := I) (M := M) g gT -
              lc0Riem (I := I) (M := M) g gU) ≤
          (C * ‖ccTensorToHs (I := I) (M := M)
            g 2 (2 : ℝ) (T - U)‖) ^ 2 := by
  obtain ⟨ρ, Ct, hρ, hCt, htrace⟩ :=
    LowBaseInternal.trace2_pair_h2 (I := I) (M := M) hDim g
  obtain ⟨Ca, hCa, happ⟩ :=
    appRS_h2_h2_h2 (I := I) (M := M) hDim g 2 4 2
  let JP : ℝ := lowJetSq (I := I) (M := M) g 2
    (lc0RiemPass (I := I) g)
  let Pn : ℝ := Real.sqrt JP
  let C : ℝ := Ca * Ct * Pn
  have hJP : 0 ≤ JP :=
    jet_nonneg_lip (I := I) (M := M) g
      (lc0RiemPass (I := I) g)
  have hPn : 0 ≤ Pn := Real.sqrt_nonneg _
  have hPnsq : Pn ^ 2 = JP := by
    simpa only [Pn] using Real.sq_sqrt hJP
  have hC : 0 ≤ C :=
    mul_nonneg (mul_nonneg hCa hCt) hPn
  refine ⟨ρ, C, hρ, hC, ?_⟩
  intro T U gT gU hTtie hUtie hTHs hUHs
  let N : ℝ :=
    ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U)‖
  let L : SmoothCcTensor g 4 2 :=
    lc0RiemLive (I := I) (M := M) g gT -
      lc0RiemLive (I := I) (M := M) g gU
  have hN : 0 ≤ N := norm_nonneg _
  have hL :
      lowJetSq (I := I) (M := M) g 2 L ≤ (Ct * N) ^ 2 := by
    rw [show L =
      pureTrace (I := I) (M := M) g gT 2 -
        pureTrace (I := I) (M := M) g gU 2 by
          simp only [L, riemLive_eq]]
    simpa only [N] using
      htrace T U gT gU hTtie hUtie hTHs hUHs
  have hApp :
      lowJetSq (I := I) (M := M) g 2
          (appCcRS (I := I) (M := M) g 2 4 2 L
            (lc0RiemPass (I := I) g)) ≤
        (Ca * (Ct * N) * Pn) ^ 2 := by
    simpa only [lowJetSq, JP] using
      happ L (lc0RiemPass (I := I) g) (Ct * N) Pn
        (mul_nonneg hCt hN) hPn hL
        (by
          simpa only [lowJetSq, JP] using
            (le_of_eq hPnsq.symm))
  have heq :
      lc0Riem (I := I) (M := M) g gT -
          lc0Riem (I := I) (M := M) g gU =
        -appCcRS (I := I) (M := M) g 2 4 2 L
          (lc0RiemPass (I := I) g) := by
    rw [lc0Riem_eq_app, lc0Riem_eq_app]
    dsimp only [L]
    rw [appCcRS_sub_left]
    module
  rw [heq, show -appCcRS (I := I) (M := M) g 2 4 2 L
      (lc0RiemPass (I := I) g) =
        (-1 : ℝ) • appCcRS (I := I) (M := M) g 2 4 2 L
          (lc0RiemPass (I := I) g) by simp,
    jet_smul_lip]
  norm_num
  calc
    lowJetSq (I := I) (M := M) g 2
        (appCcRS (I := I) (M := M) g 2 4 2 L
          (lc0RiemPass (I := I) g)) ≤
      (Ca * (Ct * N) * Pn) ^ 2 := hApp
    _ = (C * N) ^ 2 := by
      dsimp only [C]
      ring

private theorem lieArm2_jet_le
    (g gT gU : SmoothRiemannianMetric I M) :
    lowJetSq (I := I) (M := M) g 2
        (lieCovArm2 (I := I) (M := M) g gT -
          lieCovArm2 (I := I) (M := M) g gU) ≤
      (Module.finrank ℝ E : ℝ) ^ 2 *
        lowJetSq (I := I) (M := M) g 2
          (connDiffSection (I := I) gT g -
            connDiffSection (I := I) gU g) := by
  let fr : ℝ := Module.finrank ℝ E
  have hper : ∀ q : ℕ,
      ‖iteratedCovGrad (I := I) g 3 4 q
          (lieCovArm2 (I := I) (M := M) g gT -
            lieCovArm2 (I := I) (M := M) g gU)‖ ^ 2 ≤
        fr ^ 2 *
          ‖iteratedCovGrad (I := I) g 1 2 q
            (connDiffSection (I := I) gT g -
              connDiffSection (I := I) gU g)‖ ^ 2 := by
    intro q
    let F : M → ℝ := fun x => fr ^ 2 *
      riemannianFiberNormSq (I := I) (M := M) g 1 (2 + q) x
        ((iteratedCovGrad (I := I) g 1 2 q
          (connDiffSection (I := I) gT g -
            connDiffSection (I := I) gU g)).toSection x)
    have hF : MeasureTheory.Integrable F
        (riemannianVolumeMeasure (I := I) (M := M) g) := by
      dsimp only [F]
      exact (integrable_riemannianFiberNormSq_toSection
        (I := I) (M := M) g 1 (2 + q)
        (iteratedCovGrad (I := I) g 1 2 q
          (connDiffSection (I := I) gT g -
            connDiffSection (I := I) gU g))).const_mul _
    have hsq := normSq_le_integral_of_pointwise_fiberNormSq_le_rs
      (I := I) (M := M) g 3 (4 + q)
      (iteratedCovGrad (I := I) g 3 4 q
        (lieCovArm2 (I := I) (M := M) g gT -
          lieCovArm2 (I := I) (M := M) g gU))
      F hF (fun x => by
        simpa only [F, fr] using
          lieCovArm2_sub_l2 (I := I) (M := M) g gT gU q x)
    have hint : (∫ x,
        riemannianFiberNormSq (I := I) (M := M) g 1 (2 + q) x
          ((iteratedCovGrad (I := I) g 1 2 q
            (connDiffSection (I := I) gT g -
              connDiffSection (I := I) gU g)).toSection x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g)) =
          ‖iteratedCovGrad (I := I) g 1 2 q
            (connDiffSection (I := I) gT g -
              connDiffSection (I := I) gU g)‖ ^ 2 := by
      rw [SmoothCcTensor.norm_def,
        tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs]
    dsimp only [F] at hsq
    rw [MeasureTheory.integral_const_mul, hint] at hsq
    exact hsq
  unfold lowJetSq
  calc
    ∑ q ∈ Finset.range 3,
        ‖iteratedCovGrad (I := I) g 3 4 q
          (lieCovArm2 (I := I) (M := M) g gT -
            lieCovArm2 (I := I) (M := M) g gU)‖ ^ 2 ≤
      ∑ q ∈ Finset.range 3, fr ^ 2 *
        ‖iteratedCovGrad (I := I) g 1 2 q
          (connDiffSection (I := I) gT g -
            connDiffSection (I := I) gU g)‖ ^ 2 :=
      Finset.sum_le_sum fun q _ => hper q
    _ = fr ^ 2 * ∑ q ∈ Finset.range 3,
        ‖iteratedCovGrad (I := I) g 1 2 q
          (connDiffSection (I := I) gT g -
            connDiffSection (I := I) gU g)‖ ^ 2 := by
      rw [Finset.mul_sum]

private theorem lieArm2_jet1_le
    (g gT gU : SmoothRiemannianMetric I M) :
    lowJetSq (I := I) (M := M) g 1
        (lieCovArm2 (I := I) (M := M) g gT -
          lieCovArm2 (I := I) (M := M) g gU) ≤
      (Module.finrank ℝ E : ℝ) ^ 2 *
        lowJetSq (I := I) (M := M) g 1
          (connDiffSection (I := I) gT g -
            connDiffSection (I := I) gU g) := by
  let fr : ℝ := Module.finrank ℝ E
  have hper : ∀ q : ℕ,
      ‖iteratedCovGrad (I := I) g 3 4 q
          (lieCovArm2 (I := I) (M := M) g gT -
            lieCovArm2 (I := I) (M := M) g gU)‖ ^ 2 ≤
        fr ^ 2 *
          ‖iteratedCovGrad (I := I) g 1 2 q
            (connDiffSection (I := I) gT g -
              connDiffSection (I := I) gU g)‖ ^ 2 := by
    intro q
    let F : M → ℝ := fun x => fr ^ 2 *
      riemannianFiberNormSq (I := I) (M := M) g 1 (2 + q) x
        ((iteratedCovGrad (I := I) g 1 2 q
          (connDiffSection (I := I) gT g -
            connDiffSection (I := I) gU g)).toSection x)
    have hF : MeasureTheory.Integrable F
        (riemannianVolumeMeasure (I := I) (M := M) g) := by
      dsimp only [F]
      exact (integrable_riemannianFiberNormSq_toSection
        (I := I) (M := M) g 1 (2 + q)
        (iteratedCovGrad (I := I) g 1 2 q
          (connDiffSection (I := I) gT g -
            connDiffSection (I := I) gU g))).const_mul _
    have hsq := normSq_le_integral_of_pointwise_fiberNormSq_le_rs
      (I := I) (M := M) g 3 (4 + q)
      (iteratedCovGrad (I := I) g 3 4 q
        (lieCovArm2 (I := I) (M := M) g gT -
          lieCovArm2 (I := I) (M := M) g gU))
      F hF (fun x => by
        simpa only [F, fr] using
          lieCovArm2_sub_l2 (I := I) (M := M) g gT gU q x)
    have hint : (∫ x,
        riemannianFiberNormSq (I := I) (M := M) g 1 (2 + q) x
          ((iteratedCovGrad (I := I) g 1 2 q
            (connDiffSection (I := I) gT g -
              connDiffSection (I := I) gU g)).toSection x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g)) =
          ‖iteratedCovGrad (I := I) g 1 2 q
            (connDiffSection (I := I) gT g -
              connDiffSection (I := I) gU g)‖ ^ 2 := by
      rw [SmoothCcTensor.norm_def,
        tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs]
    dsimp only [F] at hsq
    rw [MeasureTheory.integral_const_mul, hint] at hsq
    exact hsq
  unfold lowJetSq
  calc
    ∑ q ∈ Finset.range 2,
        ‖iteratedCovGrad (I := I) g 3 4 q
          (lieCovArm2 (I := I) (M := M) g gT -
            lieCovArm2 (I := I) (M := M) g gU)‖ ^ 2 ≤
      ∑ q ∈ Finset.range 2, fr ^ 2 *
        ‖iteratedCovGrad (I := I) g 1 2 q
          (connDiffSection (I := I) gT g -
            connDiffSection (I := I) gU g)‖ ^ 2 :=
      Finset.sum_le_sum fun q _ => hper q
    _ = fr ^ 2 * ∑ q ∈ Finset.range 2,
        ‖iteratedCovGrad (I := I) g 1 2 q
          (connDiffSection (I := I) gT g -
            connDiffSection (I := I) gU g)‖ ^ 2 := by
      rw [Finset.mul_sum]

set_option linter.unusedVariables false in
/-- The lifted connection arm in the covariant-derivative residual preserves
the critical two-state `H²` modulus of the underlying connection difference. -/
theorem lieArm2_pair_h2
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ B0 B1 : ℝ → ℝ,
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B0 R) ∧
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B1 R) ∧
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
        {δT δU : ℝ}
        (hδT_le : δT ≤ 1 / 3) (hδT0 : 0 ≤ δT)
        (hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δT)
        (hδU_le : δU ≤ 1 / 3) (hδU0 : 0 ≤ δU)
        (hδU : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g U) δU)
        (R A D2 D3 : ℝ),
        0 ≤ R → 0 ≤ A → 0 ≤ D2 → 0 ≤ D3 →
        lowJetSq (I := I) (M := M) g 2 U ≤ R ^ 2 →
        lowJetSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
        lowJetSq (I := I) (M := M) g 2 (T - U) ≤ D2 ^ 2 →
        lowJetSq (I := I) (M := M) g 3 (T - U) ≤ D3 ^ 2 →
      lowJetSq (I := I) (M := M) g 2
          (lieCovArm2 (I := I) (M := M) g gT -
            lieCovArm2 (I := I) (M := M) g gU) ≤
        (B0 R * D3 + B1 R * D2 + B1 R * A * D2) ^ 2 := by
  obtain ⟨C0, C1, hC0, hC1, hconn⟩ :=
    connSec_sub_tame (I := I) (M := M) hDim g
      (δ₀ := (1 : ℝ) / 3) (by norm_num) (by norm_num)
  let fr : ℝ := Module.finrank ℝ E
  let B0 : ℝ → ℝ := fun R => fr * C0 R
  let B1 : ℝ → ℝ := fun R => fr * C1 R
  have hfr : 0 ≤ fr := Nat.cast_nonneg _
  refine ⟨B0, B1, fun R hR => mul_nonneg hfr (hC0 R hR),
    fun R hR => mul_nonneg hfr (hC1 R hR), ?_⟩
  intro gT gU T U hT hU hTtie hUtie
    δT δU hδT_le hδT0 hδT hδU_le hδU0 hδU
    R A D2 D3 hR hA hD2 hD3 hU2 hT3 hTU2 hTU3
  let X : ℝ := C0 R * D3 + C1 R * D2 + C1 R * A * D2
  have hC :
      lowJetSq (I := I) (M := M) g 2
          (connDiffSection (I := I) gT g -
            connDiffSection (I := I) gU g) ≤ X ^ 2 := by
    simpa only [X] using
      hconn gT gU T U hT hU hTtie hUtie
        hδT_le hδT0 hδT hδU_le hδU0 hδU
        R A D2 D3 hR hA hD2 hD3 hU2 hT3 hTU2 hTU3
  calc
    lowJetSq (I := I) (M := M) g 2
        (lieCovArm2 (I := I) (M := M) g gT -
          lieCovArm2 (I := I) (M := M) g gU) ≤
      fr ^ 2 * lowJetSq (I := I) (M := M) g 2
        (connDiffSection (I := I) gT g -
          connDiffSection (I := I) gU g) := by
            simpa only [fr] using
              lieArm2_jet_le (I := I) (M := M) g gT gU
    _ ≤ fr ^ 2 * X ^ 2 :=
      mul_le_mul_of_nonneg_left hC (sq_nonneg fr)
    _ = (B0 R * D3 + B1 R * D2 + B1 R * A * D2) ^ 2 := by
      simp only [B0, B1, X]
      ring

set_option linter.unusedVariables false in
/-- At the low endpoint, the lifted connection arm is Lipschitz in the
metric `H²` difference; no `H³` difference is required. -/
theorem lieArm2_pair_h1
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ B0 B1 : ℝ → ℝ,
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B0 R) ∧
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B1 R) ∧
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
        {δT δU : ℝ}
        (hδT_le : δT ≤ 1 / 3) (hδT0 : 0 ≤ δT)
        (hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δT)
        (hδU_le : δU ≤ 1 / 3) (hδU0 : 0 ≤ δU)
        (hδU : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g U) δU)
        (R A D2 : ℝ),
        0 ≤ R → 0 ≤ A → 0 ≤ D2 →
        lowJetSq (I := I) (M := M) g 2 U ≤ R ^ 2 →
        lowJetSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
        lowJetSq (I := I) (M := M) g 2 (T - U) ≤ D2 ^ 2 →
      lowJetSq (I := I) (M := M) g 1
          (lieCovArm2 (I := I) (M := M) g gT -
            lieCovArm2 (I := I) (M := M) g gU) ≤
        (B0 R * D2 + B1 R * A * D2) ^ 2 := by
  obtain ⟨C0, C1, hC0, hC1, hconn⟩ :=
    connSec_pair_h1 (I := I) (M := M) hDim g
      (δ₀ := (1 : ℝ) / 3) (by norm_num) (by norm_num)
  let fr : ℝ := Module.finrank ℝ E
  let B0 : ℝ → ℝ := fun R => fr * C0 R
  let B1 : ℝ → ℝ := fun R => fr * C1 R
  have hfr : 0 ≤ fr := Nat.cast_nonneg _
  refine ⟨B0, B1, fun R hR => mul_nonneg hfr (hC0 R hR),
    fun R hR => mul_nonneg hfr (hC1 R hR), ?_⟩
  intro gT gU T U hT hU hTtie hUtie
    δT δU hδT_le hδT0 hδT hδU_le hδU0 hδU
    R A D2 hR hA hD2 hU2 hT3 hTU2
  let X : ℝ := C0 R * D2 + C1 R * A * D2
  have hC :
      lowJetSq (I := I) (M := M) g 1
          (connDiffSection (I := I) gT g -
            connDiffSection (I := I) gU g) ≤ X ^ 2 := by
    simpa only [X] using
      hconn gT gU T U hT hU hTtie hUtie
        hδT_le hδT0 hδT hδU_le hδU0 hδU
        R A D2 hR hA hD2 hU2 hT3 hTU2
  calc
    lowJetSq (I := I) (M := M) g 1
        (lieCovArm2 (I := I) (M := M) g gT -
          lieCovArm2 (I := I) (M := M) g gU) ≤
      fr ^ 2 * lowJetSq (I := I) (M := M) g 1
        (connDiffSection (I := I) gT g -
          connDiffSection (I := I) gU g) := by
            simpa only [fr] using
              lieArm2_jet1_le (I := I) (M := M) g gT gU
    _ ≤ fr ^ 2 * X ^ 2 :=
      mul_le_mul_of_nonneg_left hC (sq_nonneg fr)
    _ = (B0 R * D2 + B1 R * A * D2) ^ 2 := by
      simp only [B0, B1, X]
      ring

set_option maxHeartbeats 1600000 in
/-- Complete radius-free H2 telescope for the two-state moving-lowering
correction.  The sole remaining pairwise geometric factor is the H2
difference of the two `wXi` connection coefficients. -/
theorem metricCorr_pair
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (gT gU g_bg : SmoothRiemannianMetric I M)
        (T U : SmoothCcTensor g 0 2),
        lowJetSq (I := I) (M := M) g 2
            (metricLowerCorr (I := I) (M := M) g gT g_bg T -
              metricLowerCorr (I := I) (M := M) g gU g_bg U) ≤
          C *
            (lowJetSq (I := I) (M := M) g 2 (T - U) *
                lowJetSq (I := I) (M := M) g 2
                  (wXi (I := I) (M := M) g gT g_bg) +
              lowJetSq (I := I) (M := M) g 2 U *
                lowJetSq (I := I) (M := M) g 2
                  (wXi (I := I) (M := M) g gT g_bg -
                    wXi (I := I) (M := M) g gU g_bg)) := by
  obtain ⟨C₀, hC₀, hsub⟩ :=
    metricCorr_sub_h2 (I := I) (M := M) hDim g
  obtain ⟨C₁, hC₁, hmove⟩ :=
    metricCorr_move (I := I) (M := M) hDim g
  let C : ℝ := 2 * max C₀ C₁
  have hCmax : 0 ≤ max C₀ C₁ := hC₀.trans (le_max_left C₀ C₁)
  refine ⟨C, mul_nonneg (by norm_num) hCmax, ?_⟩
  intro gT gU g_bg T U
  let X : SmoothCcTensor g 0 3 :=
    metricLowerCorr (I := I) (M := M) g gT g_bg (T - U)
  let Y : SmoothCcTensor g 0 3 :=
    metricLowerCorr (I := I) (M := M) g gT g_bg U -
      metricLowerCorr (I := I) (M := M) g gU g_bg U
  let A : ℝ :=
    lowJetSq (I := I) (M := M) g 2 (T - U) *
      lowJetSq (I := I) (M := M) g 2
        (wXi (I := I) (M := M) g gT g_bg)
  let B : ℝ :=
    lowJetSq (I := I) (M := M) g 2 U *
      lowJetSq (I := I) (M := M) g 2
        (wXi (I := I) (M := M) g gT g_bg -
          wXi (I := I) (M := M) g gU g_bg)
  have hA : 0 ≤ A := mul_nonneg
    (jet_nonneg_lip (I := I) (M := M) g (T - U))
    (jet_nonneg_lip (I := I) (M := M) g
      (wXi (I := I) (M := M) g gT g_bg))
  have hB : 0 ≤ B := mul_nonneg
    (jet_nonneg_lip (I := I) (M := M) g U)
    (jet_nonneg_lip (I := I) (M := M) g
      (wXi (I := I) (M := M) g gT g_bg -
        wXi (I := I) (M := M) g gU g_bg))
  have hX :
      lowJetSq (I := I) (M := M) g 2 X ≤ C₀ * A := by
    have hXraw := hsub gT g_bg T U
    rw [← metricCorr_sub (I := I) (M := M) g gT g_bg T U] at hXraw
    simpa only [X, A, mul_assoc] using hXraw
  have hY :
      lowJetSq (I := I) (M := M) g 2 Y ≤ C₁ * B := by
    have hYraw := hmove gT gU g_bg U
    change lowJetSq (I := I) (M := M) g 2
        (metricLowerCorr (I := I) (M := M) g gT g_bg U -
          metricLowerCorr (I := I) (M := M) g gU g_bg U) ≤
      C₁ * lowJetSq (I := I) (M := M) g 2 U *
        lowJetSq (I := I) (M := M) g 2
          (wXi (I := I) (M := M) g gT g_bg -
            wXi (I := I) (M := M) g gU g_bg) at hYraw
    simpa only [Y, B, mul_assoc] using hYraw
  have hC₀max : C₀ * A ≤ max C₀ C₁ * A :=
    mul_le_mul_of_nonneg_right (le_max_left C₀ C₁) hA
  have hC₁max : C₁ * B ≤ max C₀ C₁ * B :=
    mul_le_mul_of_nonneg_right (le_max_right C₀ C₁) hB
  rw [metricCorr_tel (I := I) (M := M) g gT gU g_bg T U]
  calc
    lowJetSq (I := I) (M := M) g 2 (X + Y) ≤
        2 * (lowJetSq (I := I) (M := M) g 2 X +
          lowJetSq (I := I) (M := M) g 2 Y) :=
      jet_add_lip (I := I) (M := M) g 2 X Y
    _ ≤ 2 * (C₀ * A + C₁ * B) :=
      mul_le_mul_of_nonneg_left (add_le_add hX hY) (by norm_num)
    _ ≤ 2 * (max C₀ C₁ * A + max C₀ C₁ * B) :=
      mul_le_mul_of_nonneg_left
        (add_le_add hC₀max hC₁max) (by norm_num)
    _ = C * (A + B) := by
      simp only [C]
      ring

omit [BoundarylessManifold I M] in
private theorem jet_mono_lip
    (g : SmoothRiemannianMetric I M) {r s m n : ℕ}
    (hmn : m ≤ n) (S : SmoothCcTensor g r s) :
    lowJetSq (I := I) (M := M) g m S ≤
      lowJetSq (I := I) (M := M) g n S := by
  unfold lowJetSq
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.range_subset_range.mpr (Nat.add_le_add_right hmn 1))
    (fun _ _ _ => sq_nonneg _)

private theorem icg_zero_lip
    (g : SmoothRiemannianMetric I M) (r s m : ℕ) :
    iteratedCovGrad (I := I) g r s m
        (0 : SmoothCcTensor g r s) = 0 := by
  induction m with
  | zero => rw [iteratedCovGrad_zero]
  | succ m ih => rw [iteratedCovGrad_succ, ih, covGrad_zero]

omit [BoundarylessManifold I M] in
private theorem jet_zero_lip
    (g : SmoothRiemannianMetric I M) {r s m : ℕ} :
    lowJetSq (I := I) (M := M) g m
        (0 : SmoothCcTensor g r s) = 0 := by
  unfold lowJetSq
  apply Finset.sum_eq_zero
  intro q hq
  rw [icg_zero_lip, norm_zero, zero_pow (by norm_num)]

private theorem wXi_zero_lip
    (g : SmoothRiemannianMetric I M) :
    wXi (I := I) (M := M) g g g = 0 := by
  refine smoothCcTensor_ext_of_unitModel (I := I) (M := M) g fun x => ?_
  apply ContinuousMultilinearMap.ext
  intro m
  rw [wXi_unitModel_apply]
  simp only [PDE.DeTurck.connDiff_self, Pi.zero_apply,
    ContinuousLinearMap.zero_apply, map_zero]
  rfl

set_option linter.unusedVariables false in
/-- On a common fibre-small metric neighborhood, the complete two-state
moving-lowering correction is `H²`-Lipschitz with polynomial dependence on
the two `H³` state jets. -/
theorem metricCorr_pair_h3
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ K : ℝ, 0 ≤ K ∧
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
      lowJetSq (I := I) (M := M) g 2
          (metricLowerCorr (I := I) (M := M) g gT g T -
            metricLowerCorr (I := I) (M := M) g gU g U) ≤
        K * (1 + lowJetSq (I := I) (M := M) g 3 T) ^ 2 *
          (1 + lowJetSq (I := I) (M := M) g 3 U) ^ 2 *
          lowJetSq (I := I) (M := M) g 3 (T - U) := by
  obtain ⟨C, hC, hpair⟩ :=
    metricCorr_pair (I := I) (M := M) hDim g
  obtain ⟨Kw, hKw, hw⟩ :=
    wXi_sub_h2 (I := I) (M := M) hDim g
      (δ₀ := (1 : ℝ) / 3) (by norm_num) (by norm_num)
  let K : ℝ := 2 * C * Kw
  refine ⟨K, mul_nonneg (mul_nonneg (by norm_num) hC) hKw, ?_⟩
  intro gT gU T U hT hU hTtie hUtie δ hδ_le hδ0
    hδT hδU hδZ
  let JT : ℝ := lowJetSq (I := I) (M := M) g 3 T
  let JU : ℝ := lowJetSq (I := I) (M := M) g 3 U
  let JD : ℝ := lowJetSq (I := I) (M := M) g 3 (T - U)
  let WT : ℝ := lowJetSq (I := I) (M := M) g 2
    (wXi (I := I) (M := M) g gT g)
  let WD : ℝ := lowJetSq (I := I) (M := M) g 2
    (wXi (I := I) (M := M) g gT g -
      wXi (I := I) (M := M) g gU g)
  let A : ℝ :=
    lowJetSq (I := I) (M := M) g 2 (T - U) * WT
  let B : ℝ :=
    lowJetSq (I := I) (M := M) g 2 U * WD
  let P : ℝ := (1 + JT) ^ 2 * (1 + JU) ^ 2
  have hZsymm : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g (0 : SmoothCcTensor g 0 2) x u v =
        ccTensorBilin (I := I) g (0 : SmoothCcTensor g 0 2) x v u := by
    intro x u v
    rw [ccTensorBilin_zero_weight, ccTensorBilin_zero_weight]
  have hZtie : ∀ (x : M) (u v : TangentSpace I x),
      g.inner x u v =
        g.inner x u v +
          ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2) x u v := by
    intro x u v
    rw [ccTensorBilinSymm_apply, ccTensorBilin_zero_weight,
      ccTensorBilin_zero_weight]
    ring
  have hJT : 0 ≤ JT := jet_nonneg_lip (I := I) (M := M) g T
  have hJU : 0 ≤ JU := jet_nonneg_lip (I := I) (M := M) g U
  have hJD : 0 ≤ JD := jet_nonneg_lip (I := I) (M := M) g (T - U)
  have hWT : 0 ≤ WT :=
    jet_nonneg_lip (I := I) (M := M) g
      (wXi (I := I) (M := M) g gT g)
  have hWD : 0 ≤ WD :=
    jet_nonneg_lip (I := I) (M := M) g
      (wXi (I := I) (M := M) g gT g -
        wXi (I := I) (M := M) g gU g)
  have hwTraw := hw gT g g T (0 : SmoothCcTensor g 0 2)
    hT hZsymm hTtie hZtie
    hδ_le hδ0 hδT hδ_le hδ0 hδZ
  have hwT : WT ≤ Kw * (1 + JT) * JT := by
    simpa only [WT, JT, wXi_zero_lip, sub_zero, jet_zero_lip,
      add_zero, one_mul, mul_one] using hwTraw
  have hwD : WD ≤ Kw * (1 + JT) * (1 + JU) * JD := by
    simpa only [WD, JT, JU, JD] using
      hw gT gU g T U hT hU hTtie hUtie
        hδ_le hδ0 hδT hδ_le hδ0 hδU
  have hD2 : lowJetSq (I := I) (M := M) g 2 (T - U) ≤ JD := by
    simpa only [JD] using
      jet_mono_lip (I := I) (M := M) g (by omega : 2 ≤ 3) (T - U)
  have hU2 : lowJetSq (I := I) (M := M) g 2 U ≤ JU := by
    simpa only [JU] using
      jet_mono_lip (I := I) (M := M) g (by omega : 2 ≤ 3) U
  have hPA : (1 + JT) * JT ≤ P := by
    have hJT1 : JT ≤ 1 + JT := by linarith
    have h1JT : 0 ≤ 1 + JT := by linarith
    have h1U : 1 ≤ (1 + JU) ^ 2 := by nlinarith
    calc
      (1 + JT) * JT ≤ (1 + JT) * (1 + JT) :=
        mul_le_mul_of_nonneg_left hJT1 h1JT
      _ = ((1 + JT) * (1 + JT)) * 1 := by ring
      _ ≤ ((1 + JT) * (1 + JT)) * (1 + JU) ^ 2 :=
        mul_le_mul_of_nonneg_left h1U (mul_nonneg h1JT h1JT)
      _ = P := by simp only [P, pow_two]
  have hPB : (1 + JT) * (1 + JU) * JU ≤ P := by
    have hJU1 : JU ≤ 1 + JU := by linarith
    have h1JT : 0 ≤ 1 + JT := by linarith
    have h1JU : 0 ≤ 1 + JU := by linarith
    have hJT1 : 1 ≤ 1 + JT := by linarith
    have hJTsq : 1 + JT ≤ (1 + JT) ^ 2 := by
      calc
        1 + JT = (1 + JT) * 1 := by ring
        _ ≤ (1 + JT) * (1 + JT) :=
          mul_le_mul_of_nonneg_left hJT1 h1JT
        _ = (1 + JT) ^ 2 := by ring
    calc
      (1 + JT) * (1 + JU) * JU ≤
          (1 + JT) * (1 + JU) * (1 + JU) :=
        mul_le_mul_of_nonneg_left hJU1 (mul_nonneg h1JT h1JU)
      _ = (1 + JT) * (1 + JU) ^ 2 := by ring
      _ ≤ (1 + JT) ^ 2 * (1 + JU) ^ 2 :=
        mul_le_mul_of_nonneg_right hJTsq (sq_nonneg _)
      _ = P := rfl
  have hA : A ≤ Kw * P * JD := by
    have hraw : A ≤ JD * (Kw * (1 + JT) * JT) := by
      exact mul_le_mul hD2 hwT hWT hJD
    calc
      A ≤ JD * (Kw * (1 + JT) * JT) := hraw
      _ = Kw * ((1 + JT) * JT) * JD := by ring
      _ ≤ Kw * P * JD :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hPA hKw) hJD
  have hB : B ≤ Kw * P * JD := by
    have hraw : B ≤ JU * (Kw * (1 + JT) * (1 + JU) * JD) := by
      exact mul_le_mul hU2 hwD hWD hJU
    calc
      B ≤ JU * (Kw * (1 + JT) * (1 + JU) * JD) := hraw
      _ = Kw * ((1 + JT) * (1 + JU) * JU) * JD := by ring
      _ ≤ Kw * P * JD :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hPB hKw) hJD
  have hAB : A + B ≤ 2 * (Kw * P * JD) := by
    linarith
  have hraw := hpair gT gU g T U
  change lowJetSq (I := I) (M := M) g 2
      (metricLowerCorr (I := I) (M := M) g gT g T -
        metricLowerCorr (I := I) (M := M) g gU g U) ≤
    C * (A + B) at hraw
  calc
    lowJetSq (I := I) (M := M) g 2
        (metricLowerCorr (I := I) (M := M) g gT g T -
          metricLowerCorr (I := I) (M := M) g gU g U) ≤
      C * (A + B) := hraw
    _ ≤ C * (2 * (Kw * P * JD)) :=
      mul_le_mul_of_nonneg_left hAB hC
    _ = K * P * JD := by
      simp only [K]
      ring
    _ = K * (1 + lowJetSq (I := I) (M := M) g 3 T) ^ 2 *
        (1 + lowJetSq (I := I) (M := M) g 3 U) ^ 2 *
        lowJetSq (I := I) (M := M) g 3 (T - U) := by
      simp only [P, JT, JU, JD]
      ring

set_option linter.unusedVariables false in
private theorem wXi_self_tame
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ B : ℝ → ℝ,
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B R) ∧
      ∀ (gT : SmoothRiemannianMetric I M)
        (T : SmoothCcTensor g 0 2)
        (hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        (hTtie : ∀ (x : M) (u v : TangentSpace I x),
          gT.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g T x u v)
        {δ : ℝ} (hδ_le : δ ≤ 1 / 3) (hδ0 : 0 ≤ δ)
        (hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        (R A : ℝ), 0 ≤ R → 0 ≤ A →
        lowJetSq (I := I) (M := M) g 2 T ≤ R ^ 2 →
        lowJetSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
      lowJetSq (I := I) (M := M) g 2
          (wXi (I := I) (M := M) g gT g) ≤
        (B R * A) ^ 2 := by
  obtain ⟨B0, B1, hB0, hB1, hw⟩ :=
    wXi_sub_tame (I := I) (M := M) hDim g
      (δ₀ := (1 : ℝ) / 3) (by norm_num) (by norm_num)
  let B : ℝ → ℝ := fun R => B0 0 + B1 0 + B1 0 * R
  refine ⟨B, ?_, ?_⟩
  · intro R hR
    exact add_nonneg
      (add_nonneg (hB0 0 (by norm_num)) (hB1 0 (by norm_num)))
      (mul_nonneg (hB1 0 (by norm_num)) hR)
  intro gT T hT hTtie δ hδ_le hδ0 hδT hδZ
    R A hR hA hT2 hT3
  let J2 : ℝ := lowJetSq (I := I) (M := M) g 2 T
  let D2 : ℝ := Real.sqrt J2
  have hJ2 : 0 ≤ J2 :=
    jet_nonneg_lip (I := I) (M := M) g T
  have hD2 : 0 ≤ D2 := Real.sqrt_nonneg _
  have hD2sq : D2 ^ 2 = J2 := by
    simpa only [D2] using Real.sq_sqrt hJ2
  have hJ23 : J2 ≤ lowJetSq (I := I) (M := M) g 3 T := by
    simpa only [J2] using
      jet_mono_lip (I := I) (M := M) g (by omega : 2 ≤ 3) T
  have hD2A : D2 ≤ A := by
    nlinarith
  have hD2R : D2 ≤ R := by
    have : J2 ≤ R ^ 2 := by simpa only [J2] using hT2
    nlinarith
  have hZsymm : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g (0 : SmoothCcTensor g 0 2) x u v =
        ccTensorBilin (I := I) g
          (0 : SmoothCcTensor g 0 2) x v u := by
    intro x u v
    rw [ccTensorBilin_zero_weight, ccTensorBilin_zero_weight]
  have hZtie : ∀ (x : M) (u v : TangentSpace I x),
      g.inner x u v =
        g.inner x u v +
          ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2) x u v := by
    intro x u v
    rw [ccTensorBilinSymm_apply, ccTensorBilin_zero_weight,
      ccTensorBilin_zero_weight]
    ring
  have hraw := hw gT g g T (0 : SmoothCcTensor g 0 2)
    hT hZsymm hTtie hZtie
    hδ_le hδ0 hδT hδ_le hδ0 hδZ
    0 A D2 A (by norm_num) hA hD2 hA
    (by
      rw [jet_zero_lip]
      norm_num)
    hT3
    (by
      rw [sub_zero]
      change J2 ≤ D2 ^ 2
      rw [hD2sq])
    (by simpa only [sub_zero] using hT3)
  have hraw' :
      lowJetSq (I := I) (M := M) g 2
          (wXi (I := I) (M := M) g gT g) ≤
        (B0 0 * A + B1 0 * D2 + B1 0 * A * D2) ^ 2 := by
    simpa only [wXi_zero_lip, sub_zero] using hraw
  have hB00 : 0 ≤ B0 0 := hB0 0 (by norm_num)
  have hB10 : 0 ≤ B1 0 := hB1 0 (by norm_num)
  have hmid : B1 0 * D2 ≤ B1 0 * A :=
    mul_le_mul_of_nonneg_left hD2A hB10
  have hlast : B1 0 * A * D2 ≤ B1 0 * A * R :=
    mul_le_mul_of_nonneg_left hD2R (mul_nonneg hB10 hA)
  have hlin :
      B0 0 * A + B1 0 * D2 + B1 0 * A * D2 ≤ B R * A := by
    simp only [B]
    nlinarith
  have hlin0 :
      0 ≤ B0 0 * A + B1 0 * D2 + B1 0 * A * D2 :=
    add_nonneg
      (add_nonneg (mul_nonneg hB00 hA) (mul_nonneg hB10 hD2))
      (mul_nonneg (mul_nonneg hB10 hA) hD2)
  exact hraw'.trans (pow_le_pow_left₀ hlin0 hlin 2)

private theorem connSec_zero_lip
    (g : SmoothRiemannianMetric I M) :
    connDiffSection (I := I) g g = 0 := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [connDiffSection_toSection]
  apply ContinuousLinearMap.ext
  intro om
  apply ContinuousMultilinearMap.ext
  intro YZ
  rw [connDiffFib_apply_eval, PDE.DeTurck.connDiff_self]
  change om (0 : Fin 1 → TangentSpace I x) = 0
  exact ContinuousMultilinearMap.map_zero om

private theorem lieArm2_self_le
    (g gT : SmoothRiemannianMetric I M) :
    lowJetSq (I := I) (M := M) g 2
        (lieCovArm2 (I := I) (M := M) g gT) ≤
      (Module.finrank ℝ E : ℝ) ^ 2 *
        lowJetSq (I := I) (M := M) g 2
          (connDiffSection (I := I) gT g) := by
  let fr : ℝ := Module.finrank ℝ E
  have hper : ∀ q : ℕ,
      ‖iteratedCovGrad (I := I) g 3 4 q
          (lieCovArm2 (I := I) (M := M) g gT)‖ ^ 2 ≤
        fr ^ 2 *
          ‖iteratedCovGrad (I := I) g 1 2 q
            (connDiffSection (I := I) gT g)‖ ^ 2 := by
    intro q
    let F : M → ℝ := fun x => fr ^ 2 *
      riemannianFiberNormSq (I := I) (M := M) g 1 (2 + q) x
        ((iteratedCovGrad (I := I) g 1 2 q
          (connDiffSection (I := I) gT g)).toSection x)
    have hF : MeasureTheory.Integrable F
        (riemannianVolumeMeasure (I := I) (M := M) g) := by
      dsimp only [F]
      exact (integrable_riemannianFiberNormSq_toSection
        (I := I) (M := M) g 1 (2 + q)
        (iteratedCovGrad (I := I) g 1 2 q
          (connDiffSection (I := I) gT g))).const_mul _
    have hsq := normSq_le_integral_of_pointwise_fiberNormSq_le_rs
      (I := I) (M := M) g 3 (4 + q)
      (iteratedCovGrad (I := I) g 3 4 q
        (lieCovArm2 (I := I) (M := M) g gT))
      F hF (fun x => by
        simpa only [F, fr] using
          lieCovArm2_l2 (I := I) (M := M) g gT q x)
    have hint : (∫ x,
        riemannianFiberNormSq (I := I) (M := M) g 1 (2 + q) x
          ((iteratedCovGrad (I := I) g 1 2 q
            (connDiffSection (I := I) gT g)).toSection x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g)) =
          ‖iteratedCovGrad (I := I) g 1 2 q
            (connDiffSection (I := I) gT g)‖ ^ 2 := by
      rw [SmoothCcTensor.norm_def,
        tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs]
    dsimp only [F] at hsq
    rw [MeasureTheory.integral_const_mul, hint] at hsq
    exact hsq
  unfold lowJetSq
  calc
    ∑ q ∈ Finset.range 3,
        ‖iteratedCovGrad (I := I) g 3 4 q
          (lieCovArm2 (I := I) (M := M) g gT)‖ ^ 2 ≤
      ∑ q ∈ Finset.range 3, fr ^ 2 *
        ‖iteratedCovGrad (I := I) g 1 2 q
          (connDiffSection (I := I) gT g)‖ ^ 2 :=
      Finset.sum_le_sum fun q _ => hper q
    _ = fr ^ 2 * ∑ q ∈ Finset.range 3,
        ‖iteratedCovGrad (I := I) g 1 2 q
          (connDiffSection (I := I) gT g)‖ ^ 2 := by
      rw [Finset.mul_sum]

set_option linter.unusedVariables false in
/-- A lifted connection arm is controlled by the low `H²` radius and the
endpoint `H³` size. -/
theorem lieArm2_bdd_h2
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ B : ℝ → ℝ,
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B R) ∧
      ∀ (gT : SmoothRiemannianMetric I M)
        (T : SmoothCcTensor g 0 2)
        (hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        (hTtie : ∀ (x : M) (u v : TangentSpace I x),
          gT.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g T x u v)
        {δ : ℝ} (hδ_le : δ ≤ 1 / 3) (hδ0 : 0 ≤ δ)
        (hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        (R A : ℝ), 0 ≤ R → 0 ≤ A →
        lowJetSq (I := I) (M := M) g 2 T ≤ R ^ 2 →
        lowJetSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
      lowJetSq (I := I) (M := M) g 2
          (lieCovArm2 (I := I) (M := M) g gT) ≤
        (B R * A) ^ 2 := by
  obtain ⟨B0, B1, hB0, hB1, hpair⟩ :=
    lieArm2_pair_h2 (I := I) (M := M) hDim g
  let H2 : ℝ := Real.sqrt 2
  let B : ℝ → ℝ := fun R =>
    H2 * (B0 0 + B1 0 + B1 0 * R)
  have hH2 : 0 ≤ H2 := Real.sqrt_nonneg _
  have hH2sq : H2 ^ 2 = (2 : ℝ) := by
    simpa only [H2] using Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hB00 : 0 ≤ B0 0 := hB0 0 (by norm_num)
  have hB10 : 0 ≤ B1 0 := hB1 0 (by norm_num)
  refine ⟨B, ?_, ?_⟩
  · intro R hR
    exact mul_nonneg hH2
      (add_nonneg (add_nonneg hB00 hB10) (mul_nonneg hB10 hR))
  intro gT T hT hTtie δ hδ_le hδ0 hδT hδZ
    R A hR hA hT2 hT3
  let J2 : ℝ := lowJetSq (I := I) (M := M) g 2 T
  let D2 : ℝ := Real.sqrt J2
  let X : ℝ := B0 0 * A + B1 0 * D2 + B1 0 * A * D2
  let L : ℝ := (B0 0 + B1 0 + B1 0 * R) * A
  have hJ2 : 0 ≤ J2 :=
    jet_nonneg_lip (I := I) (M := M) g T
  have hD2 : 0 ≤ D2 := Real.sqrt_nonneg _
  have hD2sq : D2 ^ 2 = J2 := by
    simpa only [D2] using Real.sq_sqrt hJ2
  have hJ23 : J2 ≤ lowJetSq (I := I) (M := M) g 3 T := by
    simpa only [J2] using
      jet_mono_lip (I := I) (M := M) g (by omega : 2 ≤ 3) T
  have hD2A : D2 ≤ A := by
    nlinarith
  have hD2R : D2 ≤ R := by
    have : J2 ≤ R ^ 2 := by simpa only [J2] using hT2
    nlinarith
  have hZsymm : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g (0 : SmoothCcTensor g 0 2) x u v =
        ccTensorBilin (I := I) g
          (0 : SmoothCcTensor g 0 2) x v u := by
    intro x u v
    rw [ccTensorBilin_zero_weight, ccTensorBilin_zero_weight]
  have hZtie : ∀ (x : M) (u v : TangentSpace I x),
      g.inner x u v =
        g.inner x u v +
          ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2) x u v := by
    intro x u v
    rw [ccTensorBilinSymm_apply, ccTensorBilin_zero_weight,
      ccTensorBilin_zero_weight]
    ring
  have hdiff :
      lowJetSq (I := I) (M := M) g 2
          (lieCovArm2 (I := I) (M := M) g gT -
            lieCovArm2 (I := I) (M := M) g g) ≤ X ^ 2 := by
    simpa only [X] using
      hpair gT g T (0 : SmoothCcTensor g 0 2)
        hT hZsymm hTtie hZtie
        hδ_le hδ0 hδT hδ_le hδ0 hδZ
        0 A D2 A (by norm_num) hA hD2 hA
        (by rw [jet_zero_lip]; norm_num)
        hT3
        (by
          rw [sub_zero]
          change J2 ≤ D2 ^ 2
          rw [hD2sq])
        (by simpa only [sub_zero] using hT3)
  have hbase :
      lowJetSq (I := I) (M := M) g 2
          (lieCovArm2 (I := I) (M := M) g g) = 0 := by
    apply le_antisymm
    · calc
        lowJetSq (I := I) (M := M) g 2
            (lieCovArm2 (I := I) (M := M) g g) ≤
          (Module.finrank ℝ E : ℝ) ^ 2 *
            lowJetSq (I := I) (M := M) g 2
              (connDiffSection (I := I) g g) :=
          lieArm2_self_le (I := I) (M := M) g g
        _ = 0 := by
          rw [connSec_zero_lip, jet_zero_lip, mul_zero]
    · exact jet_nonneg_lip (I := I) (M := M) g _
  have hX0 : 0 ≤ X := by
    exact add_nonneg
      (add_nonneg (mul_nonneg hB00 hA) (mul_nonneg hB10 hD2))
      (mul_nonneg (mul_nonneg hB10 hA) hD2)
  have hXL : X ≤ L := by
    simp only [X, L]
    have hmid : B1 0 * D2 ≤ B1 0 * A :=
      mul_le_mul_of_nonneg_left hD2A hB10
    have hlast : B1 0 * A * D2 ≤ B1 0 * A * R :=
      mul_le_mul_of_nonneg_left hD2R (mul_nonneg hB10 hA)
    nlinarith
  have hsplit :
      lieCovArm2 (I := I) (M := M) g gT =
        (lieCovArm2 (I := I) (M := M) g gT -
          lieCovArm2 (I := I) (M := M) g g) +
        lieCovArm2 (I := I) (M := M) g g := by
    module
  rw [hsplit]
  calc
    lowJetSq (I := I) (M := M) g 2
        ((lieCovArm2 (I := I) (M := M) g gT -
          lieCovArm2 (I := I) (M := M) g g) +
          lieCovArm2 (I := I) (M := M) g g) ≤
      2 * (lowJetSq (I := I) (M := M) g 2
          (lieCovArm2 (I := I) (M := M) g gT -
            lieCovArm2 (I := I) (M := M) g g) +
        lowJetSq (I := I) (M := M) g 2
          (lieCovArm2 (I := I) (M := M) g g)) :=
      jet_add_lip (I := I) (M := M) g 2 _ _
    _ ≤ 2 * (X ^ 2 + 0) :=
      mul_le_mul_of_nonneg_left (add_le_add hdiff (le_of_eq hbase))
        (by norm_num)
    _ ≤ 2 * L ^ 2 := by
      exact mul_le_mul_of_nonneg_left
        (by simpa only [add_zero] using pow_le_pow_left₀ hX0 hXL 2)
        (by norm_num)
    _ = (B R * A) ^ 2 := by
      simp only [B, L]
      rw [← hH2sq]
      ring

set_option linter.unusedVariables false in
private theorem app_h2_mul_lip
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) (p r c : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (Φ : SmoothCcTensor g r c) (W : SmoothCcTensor g p r),
        lowJetSq (I := I) (M := M) g 2
            (appCcRS (I := I) (M := M) g p r c Φ W) ≤
          C * lowJetSq (I := I) (M := M) g 2 Φ *
            lowJetSq (I := I) (M := M) g 2 W := by
  obtain ⟨C₀, hC₀, happ⟩ :=
    appRS_h2_h2_h2 (I := I) (M := M) hDim g p r c
  refine ⟨C₀ ^ 2, sq_nonneg _, ?_⟩
  intro Φ W
  have hΦ0 : 0 ≤ lowJetSq (I := I) (M := M) g 2 Φ :=
    jet_nonneg_lip (I := I) (M := M) g Φ
  have hW0 : 0 ≤ lowJetSq (I := I) (M := M) g 2 W :=
    jet_nonneg_lip (I := I) (M := M) g W
  have hsΦ :
      Real.sqrt (lowJetSq (I := I) (M := M) g 2 Φ) ^ 2 =
        lowJetSq (I := I) (M := M) g 2 Φ :=
    Real.sq_sqrt hΦ0
  have hsW :
      Real.sqrt (lowJetSq (I := I) (M := M) g 2 W) ^ 2 =
        lowJetSq (I := I) (M := M) g 2 W :=
    Real.sq_sqrt hW0
  have h := happ Φ W
    (Real.sqrt (lowJetSq (I := I) (M := M) g 2 Φ))
    (Real.sqrt (lowJetSq (I := I) (M := M) g 2 W))
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    (by
      unfold lowJetSq
      exact le_of_eq hsΦ.symm)
    (by
      unfold lowJetSq
      exact le_of_eq hsW.symm)
  calc
    lowJetSq (I := I) (M := M) g 2
        (appCcRS (I := I) (M := M) g p r c Φ W) ≤
      (C₀ *
        Real.sqrt (lowJetSq (I := I) (M := M) g 2 Φ) *
        Real.sqrt (lowJetSq (I := I) (M := M) g 2 W)) ^ 2 := by
      simpa only [lowJetSq, Nat.reduceAdd] using h
    _ = C₀ ^ 2 * lowJetSq (I := I) (M := M) g 2 Φ *
        lowJetSq (I := I) (M := M) g 2 W := by
      rw [mul_pow, mul_pow, hsΦ, hsW]

private theorem dom_h2_lip
    (g : SmoothRiemannianMetric I M) {s : ℕ}
    (σ : Equiv.Perm (Fin s)) (S : SmoothCcTensor g 0 s) :
    lowJetSq (I := I) (M := M) g 2
        (domDomCongrSection (I := I) g σ S) =
      lowJetSq (I := I) (M := M) g 2 S := by
  unfold lowJetSq
  apply Finset.sum_congr rfl
  intro q _
  rw [SmoothCcTensor.norm_def,
    tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs,
    SmoothCcTensor.norm_def,
    tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs]
  apply MeasureTheory.integral_congr_ae
  exact Filter.Eventually.of_forall fun x =>
    riemannianFiberNormSq_iteratedCovGrad_domDomCongrSection
      (I := I) (M := M) g σ S q x

set_option linter.unusedVariables false in
private theorem dom_sub_lip
    (g : SmoothRiemannianMetric I M) {s : ℕ}
    (σ : Equiv.Perm (Fin s)) (A B : SmoothCcTensor g 0 s) :
    domDomCongrSection (I := I) g σ (A - B) =
      domDomCongrSection (I := I) g σ A -
        domDomCongrSection (I := I) g σ B := by
  apply smoothCcTensor_ext_of_unitModel (I := I) (M := M) g
  intro x
  have hsub : ∀ (P Q : SmoothCcTensor g 0 s),
      unitModel (I := I) (M := M) g s (P - Q) x =
        unitModel (I := I) (M := M) g s P x -
          unitModel (I := I) (M := M) g s Q x := by
    intro P Q
    simp only [unitModel]
    rw [SmoothCcTensor.toSection_sub]
    rfl
  rw [domDomCongrSection_unitModel, hsub A B]
  rw [hsub
    (domDomCongrSection (I := I) g σ A)
    (domDomCongrSection (I := I) g σ B)]
  rw [domDomCongrSection_unitModel, domDomCongrSection_unitModel]
  apply ContinuousMultilinearMap.ext
  intro v
  simp only [ContinuousMultilinearMap.sub_apply,
    ContinuousMultilinearMap.domDomCongr_apply]

private noncomputable def lipOmega
    (g gm : SmoothRiemannianMetric I M) : SmoothCcTensor g 0 3 :=
  appCcRS (I := I) (M := M) g 0 3 3
    (slotInsertEndoCc (I := I) (M := M) g 2
      (fullRaisedEndoField (I := I) (M := M) gm g))
    (domDomCongrSection (I := I) g (finRotate 3)
      (connDiffLoweredCc (I := I) g gm))

private theorem lipOmega_tel
    (g gT gU : SmoothRiemannianMetric I M) :
    lipOmega (I := I) (M := M) g gT -
        lipOmega (I := I) (M := M) g gU =
      appCcRS (I := I) (M := M) g 0 3 3
          (slotInsertEndoCc (I := I) (M := M) g 2
            (fullRaisedEndoField (I := I) (M := M) gU g))
          (domDomCongrSection (I := I) g (finRotate 3)
            (connDiffLoweredCc (I := I) g gT -
              connDiffLoweredCc (I := I) g gU)) +
        appCcRS (I := I) (M := M) g 0 3 3
          (slotInsertEndoCc (I := I) (M := M) g 2
              (fullRaisedEndoField (I := I) (M := M) gT g) -
            slotInsertEndoCc (I := I) (M := M) g 2
              (fullRaisedEndoField (I := I) (M := M) gU g))
          (domDomCongrSection (I := I) g (finRotate 3)
            (connDiffLoweredCc (I := I) g gT)) := by
  rw [lipOmega, lipOmega, dom_sub_lip,
    appCcRS_sub_right, appCcRS_sub_left]
  module

set_option linter.unusedVariables false in
private theorem omega_pair
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (gT gU : SmoothRiemannianMetric I M),
        lowJetSq (I := I) (M := M) g 2
            (lipOmega (I := I) (M := M) g gT -
              lipOmega (I := I) (M := M) g gU) ≤
          C *
            (lowJetSq (I := I) (M := M) g 2
                (slotInsertEndoCc (I := I) (M := M) g 2
                  (fullRaisedEndoField (I := I) (M := M) gU g)) *
              lowJetSq (I := I) (M := M) g 2
                (connDiffLoweredCc (I := I) g gT -
                  connDiffLoweredCc (I := I) g gU) +
            lowJetSq (I := I) (M := M) g 2
                (slotInsertEndoCc (I := I) (M := M) g 2
                    (fullRaisedEndoField (I := I) (M := M) gT g) -
                  slotInsertEndoCc (I := I) (M := M) g 2
                    (fullRaisedEndoField (I := I) (M := M) gU g)) *
              lowJetSq (I := I) (M := M) g 2
                (connDiffLoweredCc (I := I) g gT)) := by
  obtain ⟨C₀, hC₀, happ⟩ :=
    app_h2_mul_lip (I := I) (M := M) hDim g 0 3 3
  refine ⟨2 * C₀, mul_nonneg (by norm_num) hC₀, ?_⟩
  intro gT gU
  let AU : SmoothCcTensor g 3 3 :=
    slotInsertEndoCc (I := I) (M := M) g 2
      (fullRaisedEndoField (I := I) (M := M) gU g)
  let AD : SmoothCcTensor g 3 3 :=
    slotInsertEndoCc (I := I) (M := M) g 2
        (fullRaisedEndoField (I := I) (M := M) gT g) -
      slotInsertEndoCc (I := I) (M := M) g 2
        (fullRaisedEndoField (I := I) (M := M) gU g)
  let BD : SmoothCcTensor g 0 3 :=
    domDomCongrSection (I := I) g (finRotate 3)
      (connDiffLoweredCc (I := I) g gT -
        connDiffLoweredCc (I := I) g gU)
  let BT : SmoothCcTensor g 0 3 :=
    domDomCongrSection (I := I) g (finRotate 3)
      (connDiffLoweredCc (I := I) g gT)
  let X : SmoothCcTensor g 0 3 :=
    appCcRS (I := I) (M := M) g 0 3 3 AU BD
  let Y : SmoothCcTensor g 0 3 :=
    appCcRS (I := I) (M := M) g 0 3 3 AD BT
  have hX :
      lowJetSq (I := I) (M := M) g 2 X ≤
        C₀ * lowJetSq (I := I) (M := M) g 2 AU *
          lowJetSq (I := I) (M := M) g 2
            (connDiffLoweredCc (I := I) g gT -
              connDiffLoweredCc (I := I) g gU) := by
    have hraw := happ AU BD
    rw [dom_h2_lip] at hraw
    simpa only [X, BD] using hraw
  have hY :
      lowJetSq (I := I) (M := M) g 2 Y ≤
        C₀ * lowJetSq (I := I) (M := M) g 2 AD *
          lowJetSq (I := I) (M := M) g 2
            (connDiffLoweredCc (I := I) g gT) := by
    have hraw := happ AD BT
    rw [dom_h2_lip] at hraw
    simpa only [Y, BT] using hraw
  rw [lipOmega_tel (I := I) (M := M) g gT gU]
  change lowJetSq (I := I) (M := M) g 2 (X + Y) ≤ _
  calc
    lowJetSq (I := I) (M := M) g 2 (X + Y) ≤
        2 * (lowJetSq (I := I) (M := M) g 2 X +
          lowJetSq (I := I) (M := M) g 2 Y) :=
      jet_add_lip (I := I) (M := M) g 2 X Y
    _ ≤ 2 * (C₀ * lowJetSq (I := I) (M := M) g 2 AU *
          lowJetSq (I := I) (M := M) g 2
            (connDiffLoweredCc (I := I) g gT -
              connDiffLoweredCc (I := I) g gU) +
        C₀ * lowJetSq (I := I) (M := M) g 2 AD *
          lowJetSq (I := I) (M := M) g 2
            (connDiffLoweredCc (I := I) g gT)) :=
      mul_le_mul_of_nonneg_left (add_le_add hX hY) (by norm_num)
    _ = (2 * C₀) *
        (lowJetSq (I := I) (M := M) g 2 AU *
            lowJetSq (I := I) (M := M) g 2
              (connDiffLoweredCc (I := I) g gT -
                connDiffLoweredCc (I := I) g gU) +
          lowJetSq (I := I) (M := M) g 2 AD *
            lowJetSq (I := I) (M := M) g 2
              (connDiffLoweredCc (I := I) g gT)) := by
      ring

private theorem app_h21_mul_lip
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) (p r c : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (Φ : SmoothCcTensor g r c) (W : SmoothCcTensor g p r),
        lowJetSq (I := I) (M := M) g 1
            (appCcRS (I := I) (M := M) g p r c Φ W) ≤
          C * lowJetSq (I := I) (M := M) g 2 Φ *
            lowJetSq (I := I) (M := M) g 1 W := by
  obtain ⟨C₀, hC₀, happ⟩ :=
    appRS_h2_h1_h1 (I := I) (M := M) hDim g p r c
  refine ⟨C₀ ^ 2, sq_nonneg _, ?_⟩
  intro Φ W
  let A : ℝ := Real.sqrt (lowJetSq (I := I) (M := M) g 2 Φ)
  let B : ℝ := Real.sqrt (lowJetSq (I := I) (M := M) g 1 W)
  have hΦ0 : 0 ≤ lowJetSq (I := I) (M := M) g 2 Φ :=
    jet_nonneg_lip (I := I) (M := M) g Φ
  have hW0 : 0 ≤ lowJetSq (I := I) (M := M) g 1 W :=
    jet_nonneg_lip (I := I) (M := M) g W
  have hA : 0 ≤ A := Real.sqrt_nonneg _
  have hB : 0 ≤ B := Real.sqrt_nonneg _
  have hAsq : A ^ 2 = lowJetSq (I := I) (M := M) g 2 Φ := by
    simpa only [A] using Real.sq_sqrt hΦ0
  have hBsq : B ^ 2 = lowJetSq (I := I) (M := M) g 1 W := by
    simpa only [B] using Real.sq_sqrt hW0
  have hnorm := happ Φ W A B hA hB
    (by
      simpa only [lowJetSq, Nat.reduceAdd] using
        (le_of_eq hAsq.symm))
    (by
      simpa only [lowJetSq, Nat.reduceAdd] using
        (le_of_eq hBsq.symm))
  have hsq := pow_le_pow_left₀
    (norm_nonneg
      (⟨appCcRS (I := I) (M := M) g p r c Φ W⟩ :
        SmoothCcTensorH1 g p c))
    hnorm 2
  have hjet :
      lowJetSq (I := I) (M := M) g 1
          (appCcRS (I := I) (M := M) g p r c Φ W) ≤
        (C₀ * A * B) ^ 2 := by
    rw [h1_jet_sq (I := I) (M := M) g p c
      (appCcRS (I := I) (M := M) g p r c Φ W)] at hsq
    simpa only [lowJetSq, Finset.sum_range_succ,
      Finset.sum_range_zero, zero_add, Nat.reduceAdd,
      iteratedCovGrad_zero, iteratedCovGrad_succ] using hsq
  calc
    lowJetSq (I := I) (M := M) g 1
        (appCcRS (I := I) (M := M) g p r c Φ W) ≤
      (C₀ * A * B) ^ 2 := hjet
    _ = C₀ ^ 2 * lowJetSq (I := I) (M := M) g 2 Φ *
        lowJetSq (I := I) (M := M) g 1 W := by
      rw [mul_pow, mul_pow, hAsq, hBsq]

private theorem app_h12_mul_lip
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) (p r c : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (Φ : SmoothCcTensor g r c) (W : SmoothCcTensor g p r),
        lowJetSq (I := I) (M := M) g 1
            (appCcRS (I := I) (M := M) g p r c Φ W) ≤
          C * lowJetSq (I := I) (M := M) g 1 Φ *
            lowJetSq (I := I) (M := M) g 2 W := by
  obtain ⟨C₀, hC₀, happ⟩ :=
    appRS_h1_h2_h1 (I := I) (M := M) hDim g p r c
  refine ⟨C₀ ^ 2, sq_nonneg _, ?_⟩
  intro Φ W
  let A : ℝ := Real.sqrt (lowJetSq (I := I) (M := M) g 1 Φ)
  let B : ℝ := Real.sqrt (lowJetSq (I := I) (M := M) g 2 W)
  have hΦ0 : 0 ≤ lowJetSq (I := I) (M := M) g 1 Φ :=
    jet_nonneg_lip (I := I) (M := M) g Φ
  have hW0 : 0 ≤ lowJetSq (I := I) (M := M) g 2 W :=
    jet_nonneg_lip (I := I) (M := M) g W
  have hA : 0 ≤ A := Real.sqrt_nonneg _
  have hB : 0 ≤ B := Real.sqrt_nonneg _
  have hAsq : A ^ 2 = lowJetSq (I := I) (M := M) g 1 Φ := by
    simpa only [A] using Real.sq_sqrt hΦ0
  have hBsq : B ^ 2 = lowJetSq (I := I) (M := M) g 2 W := by
    simpa only [B] using Real.sq_sqrt hW0
  have hnorm := happ Φ W A B hA hB
    (by
      simpa only [lowJetSq, Nat.reduceAdd] using
        (le_of_eq hAsq.symm))
    (by
      simpa only [lowJetSq, Nat.reduceAdd] using
        (le_of_eq hBsq.symm))
  have hsq := pow_le_pow_left₀
    (norm_nonneg
      (⟨appCcRS (I := I) (M := M) g p r c Φ W⟩ :
        SmoothCcTensorH1 g p c))
    hnorm 2
  have hjet :
      lowJetSq (I := I) (M := M) g 1
          (appCcRS (I := I) (M := M) g p r c Φ W) ≤
        (C₀ * A * B) ^ 2 := by
    rw [h1_jet_sq (I := I) (M := M) g p c
      (appCcRS (I := I) (M := M) g p r c Φ W)] at hsq
    simpa only [lowJetSq, Finset.sum_range_succ,
      Finset.sum_range_zero, zero_add, Nat.reduceAdd,
      iteratedCovGrad_zero, iteratedCovGrad_succ] using hsq
  calc
    lowJetSq (I := I) (M := M) g 1
        (appCcRS (I := I) (M := M) g p r c Φ W) ≤
      (C₀ * A * B) ^ 2 := hjet
    _ = C₀ ^ 2 * lowJetSq (I := I) (M := M) g 1 Φ *
        lowJetSq (I := I) (M := M) g 2 W := by
      rw [mul_pow, mul_pow, hAsq, hBsq]

private theorem dom_h1_lip
    (g : SmoothRiemannianMetric I M) {s : ℕ}
    (σ : Equiv.Perm (Fin s)) (S : SmoothCcTensor g 0 s) :
    lowJetSq (I := I) (M := M) g 1
        (domDomCongrSection (I := I) g σ S) =
      lowJetSq (I := I) (M := M) g 1 S := by
  unfold lowJetSq
  apply Finset.sum_congr rfl
  intro q _
  rw [SmoothCcTensor.norm_def,
    tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs,
    SmoothCcTensor.norm_def,
    tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs]
  apply MeasureTheory.integral_congr_ae
  exact Filter.Eventually.of_forall fun x =>
    riemannianFiberNormSq_iteratedCovGrad_domDomCongrSection
      (I := I) (M := M) g σ S q x

/-- Narrow `H¹` form of the two-state Riemann-pass modulus: the `H¹` jet of
the `lc0Riem` difference is controlled by the same `H²`-difference norm. -/
theorem riem_pair_h1
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ C : ℝ, 0 < ρ ∧ 0 ≤ C ∧
      ∀ (T U : SmoothCcTensor g 0 2)
        (gT gU : SmoothRiemannianMetric I M),
        (∀ (x : M) (u v : TangentSpace I x),
          gT.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g T x u v) →
        (∀ (x : M) (u v : TangentSpace I x),
          gU.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g U x u v) →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ ≤ ρ →
        lowJetSq (I := I) (M := M) g 1
            (lc0Riem (I := I) (M := M) g gT -
              lc0Riem (I := I) (M := M) g gU) ≤
          (C * ‖ccTensorToHs (I := I) (M := M)
            g 2 (2 : ℝ) (T - U)‖) ^ 2 := by
  obtain ⟨ρ, C, hρ, hC, hpair⟩ :=
    riem_pair_h2 (I := I) (M := M) hDim g
  refine ⟨ρ, C, hρ, hC, ?_⟩
  intro T U gT gU hTtie hUtie hTHs hUHs
  calc
    lowJetSq (I := I) (M := M) g 1
        (lc0Riem (I := I) (M := M) g gT -
          lc0Riem (I := I) (M := M) g gU) ≤
      lowJetSq (I := I) (M := M) g 2
        (lc0Riem (I := I) (M := M) g gT -
          lc0Riem (I := I) (M := M) g gU) :=
      jet_mono_lip (I := I) (M := M) g (by norm_num) _
    _ ≤ (C * ‖ccTensorToHs (I := I) (M := M)
        g 2 (2 : ℝ) (T - U)‖) ^ 2 :=
      hpair T U gT gU hTtie hUtie hTHs hUHs

set_option linter.unusedVariables false in
private theorem omega_pair_h1
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (gT gU : SmoothRiemannianMetric I M),
        lowJetSq (I := I) (M := M) g 1
            (lipOmega (I := I) (M := M) g gT -
              lipOmega (I := I) (M := M) g gU) ≤
          C *
            (lowJetSq (I := I) (M := M) g 2
                (slotInsertEndoCc (I := I) (M := M) g 2
                  (fullRaisedEndoField (I := I) (M := M) gU g)) *
              lowJetSq (I := I) (M := M) g 1
                (connDiffLoweredCc (I := I) g gT -
                  connDiffLoweredCc (I := I) g gU) +
            lowJetSq (I := I) (M := M) g 2
                (slotInsertEndoCc (I := I) (M := M) g 2
                    (fullRaisedEndoField (I := I) (M := M) gT g) -
                  slotInsertEndoCc (I := I) (M := M) g 2
                    (fullRaisedEndoField (I := I) (M := M) gU g)) *
              lowJetSq (I := I) (M := M) g 1
                (connDiffLoweredCc (I := I) g gT)) := by
  obtain ⟨C₀, hC₀, happ⟩ :=
    app_h21_mul_lip (I := I) (M := M) hDim g 0 3 3
  refine ⟨2 * C₀, mul_nonneg (by norm_num) hC₀, ?_⟩
  intro gT gU
  let AU : SmoothCcTensor g 3 3 :=
    slotInsertEndoCc (I := I) (M := M) g 2
      (fullRaisedEndoField (I := I) (M := M) gU g)
  let AD : SmoothCcTensor g 3 3 :=
    slotInsertEndoCc (I := I) (M := M) g 2
        (fullRaisedEndoField (I := I) (M := M) gT g) -
      slotInsertEndoCc (I := I) (M := M) g 2
        (fullRaisedEndoField (I := I) (M := M) gU g)
  let BD : SmoothCcTensor g 0 3 :=
    domDomCongrSection (I := I) g (finRotate 3)
      (connDiffLoweredCc (I := I) g gT -
        connDiffLoweredCc (I := I) g gU)
  let BT : SmoothCcTensor g 0 3 :=
    domDomCongrSection (I := I) g (finRotate 3)
      (connDiffLoweredCc (I := I) g gT)
  let X : SmoothCcTensor g 0 3 :=
    appCcRS (I := I) (M := M) g 0 3 3 AU BD
  let Y : SmoothCcTensor g 0 3 :=
    appCcRS (I := I) (M := M) g 0 3 3 AD BT
  have hX :
      lowJetSq (I := I) (M := M) g 1 X ≤
        C₀ * lowJetSq (I := I) (M := M) g 2 AU *
          lowJetSq (I := I) (M := M) g 1
            (connDiffLoweredCc (I := I) g gT -
              connDiffLoweredCc (I := I) g gU) := by
    have hraw := happ AU BD
    rw [dom_h1_lip] at hraw
    simpa only [X, BD] using hraw
  have hY :
      lowJetSq (I := I) (M := M) g 1 Y ≤
        C₀ * lowJetSq (I := I) (M := M) g 2 AD *
          lowJetSq (I := I) (M := M) g 1
            (connDiffLoweredCc (I := I) g gT) := by
    have hraw := happ AD BT
    rw [dom_h1_lip] at hraw
    simpa only [Y, BT] using hraw
  rw [lipOmega_tel (I := I) (M := M) g gT gU]
  change lowJetSq (I := I) (M := M) g 1 (X + Y) ≤ _
  calc
    lowJetSq (I := I) (M := M) g 1 (X + Y) ≤
        2 * (lowJetSq (I := I) (M := M) g 1 X +
          lowJetSq (I := I) (M := M) g 1 Y) :=
      jet_add_lip (I := I) (M := M) g 1 X Y
    _ ≤ 2 * (C₀ * lowJetSq (I := I) (M := M) g 2 AU *
          lowJetSq (I := I) (M := M) g 1
            (connDiffLoweredCc (I := I) g gT -
              connDiffLoweredCc (I := I) g gU) +
        C₀ * lowJetSq (I := I) (M := M) g 2 AD *
          lowJetSq (I := I) (M := M) g 1
            (connDiffLoweredCc (I := I) g gT)) :=
      mul_le_mul_of_nonneg_left (add_le_add hX hY) (by norm_num)
    _ = (2 * C₀) *
        (lowJetSq (I := I) (M := M) g 2 AU *
            lowJetSq (I := I) (M := M) g 1
              (connDiffLoweredCc (I := I) g gT -
                connDiffLoweredCc (I := I) g gU) +
          lowJetSq (I := I) (M := M) g 2 AD *
            lowJetSq (I := I) (M := M) g 1
              (connDiffLoweredCc (I := I) g gT)) := by
      ring

set_option maxHeartbeats 1600000 in
set_option linter.unusedVariables false in
/-- The reverse-raised connection product in the Lie zero-head has the
two-state `H¹` modulus with only the `H²` state difference `D2`. -/
theorem lieOmega_pair_h1
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ B0 B1 : ℝ → ℝ,
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B0 R) ∧
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B1 R) ∧
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
            (0 : SmoothCcTensor g 0 2)) δ)
        (R A D2 : ℝ), 0 ≤ R → 0 ≤ A → 0 ≤ D2 →
        lowJetSq (I := I) (M := M) g 2 T ≤ R ^ 2 →
        lowJetSq (I := I) (M := M) g 2 U ≤ R ^ 2 →
        lowJetSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
        lowJetSq (I := I) (M := M) g 2 (T - U) ≤ D2 ^ 2 →
      lowJetSq (I := I) (M := M) g 1
          (lipOmega (I := I) (M := M) g gT -
            lipOmega (I := I) (M := M) g gU) ≤
        (B0 R * D2 + B1 R * A * D2) ^ 2 := by
  obtain ⟨C, hC, hpair⟩ :=
    omega_pair_h1 (I := I) (M := M) hDim g
  obtain ⟨Cr, hCr, hrevB⟩ :=
    LowBaseInternal.revSlot_bdd_h2 (I := I) (M := M) g
  obtain ⟨Bs, hBs, hwSelf⟩ :=
    wXi_self_tame (I := I) (M := M) hDim g
  obtain ⟨W0, W1, hW0, hW1, hwDiff⟩ :=
    wXi_pair_h1 (I := I) (M := M) hDim g
      (δ₀ := (1 : ℝ) / 3) (by norm_num) (by norm_num)
  let Hc : ℝ := Real.sqrt C
  let fr : ℝ := Module.finrank ℝ E
  let B0 : ℝ → ℝ := fun R =>
    Hc * (Cr * (1 + R)) * W0 R
  let B1 : ℝ → ℝ := fun R =>
    Hc * (Cr * (1 + R) * W1 R + fr * Bs R)
  have hHc : 0 ≤ Hc := Real.sqrt_nonneg _
  have hHcSq : Hc ^ 2 = C := by
    simpa only [Hc] using Real.sq_sqrt hC
  have hfr : 0 ≤ fr := Nat.cast_nonneg _
  refine ⟨B0, B1, ?_, ?_, ?_⟩
  · intro R hR
    exact mul_nonneg
      (mul_nonneg hHc (mul_nonneg hCr (by linarith)))
      (hW0 R hR)
  · intro R hR
    exact mul_nonneg hHc
      (add_nonneg
        (mul_nonneg (mul_nonneg hCr (by linarith)) (hW1 R hR))
        (mul_nonneg hfr (hBs R hR)))
  intro gT gU T U hT hU hTtie hUtie
    δ hδ_le hδ0 hδT hδU hδZ
    R A D2 hR hA hD2 hT2 hU2 hT3 hTU2
  let AU : ℝ := lowJetSq (I := I) (M := M) g 2
    (slotInsertEndoCc (I := I) (M := M) g 2
      (fullRaisedEndoField (I := I) (M := M) gU g))
  let AD : ℝ := lowJetSq (I := I) (M := M) g 2
    (slotInsertEndoCc (I := I) (M := M) g 2
        (fullRaisedEndoField (I := I) (M := M) gT g) -
      slotInsertEndoCc (I := I) (M := M) g 2
        (fullRaisedEndoField (I := I) (M := M) gU g))
  let WT : ℝ := lowJetSq (I := I) (M := M) g 1
    (wXi (I := I) (M := M) g gT g)
  let WD : ℝ := lowJetSq (I := I) (M := M) g 1
    (wXi (I := I) (M := M) g gT g -
      wXi (I := I) (M := M) g gU g)
  let X : ℝ := W0 R * D2 + W1 R * A * D2
  let P : ℝ := Cr * (1 + R)
  let Q : ℝ := fr * Bs R
  let L : ℝ := Hc * (P * X + Q * A * D2)
  have hAU0 : 0 ≤ AU := jet_nonneg_lip (I := I) (M := M) g _
  have hAD0 : 0 ≤ AD := jet_nonneg_lip (I := I) (M := M) g _
  have hWT0 : 0 ≤ WT := jet_nonneg_lip (I := I) (M := M) g _
  have hWD0 : 0 ≤ WD := jet_nonneg_lip (I := I) (M := M) g _
  have hW0R : 0 ≤ W0 R := hW0 R hR
  have hW1R : 0 ≤ W1 R := hW1 R hR
  have hBsR : 0 ≤ Bs R := hBs R hR
  have hP : 0 ≤ P := mul_nonneg hCr (by linarith)
  have hQ : 0 ≤ Q := mul_nonneg hfr hBsR
  have hX : 0 ≤ X :=
    add_nonneg (mul_nonneg hW0R hD2)
      (mul_nonneg (mul_nonneg hW1R hA) hD2)
  have hAU :
      AU ≤ P ^ 2 := by
    simpa only [AU, P] using
      hrevB gU U hU hUtie R hR hU2
  have hAD :
      AD ≤ (fr * D2) ^ 2 := by
    have hraw :=
      LowBaseInternal.revSlot_pair_h2 (I := I) (M := M)
        g gT gU T U hT hU hTtie hUtie
    calc
      AD ≤ fr ^ 2 * lowJetSq (I := I) (M := M) g 2 (T - U) := by
        simpa only [AD, fr] using hraw
      _ ≤ fr ^ 2 * D2 ^ 2 :=
        mul_le_mul_of_nonneg_left hTU2 (sq_nonneg fr)
      _ = (fr * D2) ^ 2 := by ring
  have hWT :
      WT ≤ (Bs R * A) ^ 2 := by
    calc
      WT ≤ lowJetSq (I := I) (M := M) g 2
          (wXi (I := I) (M := M) g gT g) :=
        jet_mono_lip (I := I) (M := M) g (by norm_num) _
      _ ≤ (Bs R * A) ^ 2 :=
        hwSelf gT T hT hTtie hδ_le hδ0 hδT hδZ
          R A hR hA hT2 hT3
  have hWD :
      WD ≤ X ^ 2 := by
    simpa only [WD, X] using
      hwDiff gT gU g T U hT hU hTtie hUtie
        hδ_le hδ0 hδT hδ_le hδ0 hδU
        R A D2 hR hA hD2 hU2 hT3 hTU2
  have hPairRaw :
      lowJetSq (I := I) (M := M) g 1
          (lipOmega (I := I) (M := M) g gT -
            lipOmega (I := I) (M := M) g gU) ≤
        C * (AU * WD + AD * WT) := by
    simpa only [AU, AD, WT, WD, wXi_self_eq] using hpair gT gU
  have hFirst : AU * WD ≤ (P * X) ^ 2 := by
    calc
      AU * WD ≤ P ^ 2 * X ^ 2 :=
        mul_le_mul hAU hWD hWD0 (sq_nonneg P)
      _ = (P * X) ^ 2 := by ring
  have hSecond : AD * WT ≤ (Q * A * D2) ^ 2 := by
    calc
      AD * WT ≤ (fr * D2) ^ 2 * (Bs R * A) ^ 2 :=
        mul_le_mul hAD hWT hWT0 (sq_nonneg (fr * D2))
      _ = (Q * A * D2) ^ 2 := by
        simp only [Q]
        ring
  have hPX : 0 ≤ P * X := mul_nonneg hP hX
  have hQAD : 0 ≤ Q * A * D2 :=
    mul_nonneg (mul_nonneg hQ hA) hD2
  have hToL :
      C * (AU * WD + AD * WT) ≤ L ^ 2 := by
    calc
      C * (AU * WD + AD * WT) ≤
          C * ((P * X) ^ 2 + (Q * A * D2) ^ 2) :=
        mul_le_mul_of_nonneg_left (add_le_add hFirst hSecond) hC
      _ ≤ C * (P * X + Q * A * D2) ^ 2 := by
        apply mul_le_mul_of_nonneg_left _ hC
        nlinarith [mul_nonneg hPX hQAD]
      _ = L ^ 2 := by
        simp only [L]
        rw [mul_pow, hHcSq]
  have hLeq : L = B0 R * D2 + B1 R * A * D2 := by
    simp only [L, B0, B1, P, Q, X]
    ring
  calc
    lowJetSq (I := I) (M := M) g 1
        (lipOmega (I := I) (M := M) g gT -
          lipOmega (I := I) (M := M) g gU) ≤
      C * (AU * WD + AD * WT) := hPairRaw
    _ ≤ L ^ 2 := hToL
    _ = (B0 R * D2 + B1 R * A * D2) ^ 2 := by rw [hLeq]

private theorem hat_eq_lip
    (g gm : SmoothRiemannianMetric I M) :
    lrOmegaHat (I := I) (M := M) g gm =
      lipOmega (I := I) (M := M) g gm := rfl

private theorem curvF_pair_h1
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (T U : SmoothCcTensor g 0 2),
        lowJetSq (I := I) (M := M) g 1
            (lrCurvF (I := I) (M := M) g T -
              lrCurvF (I := I) (M := M) g U) ≤
          C * lowJetSq (I := I) (M := M) g 2 (T - U) := by
  obtain ⟨C₀, hC₀, happ⟩ :=
    app_h21_mul_lip (I := I) (M := M) hDim g 0 2 4
  let J1w : ℝ := lowJetSq (I := I) (M := M) g 2
    (lrRiemW1 (I := I) (M := M) g)
  let J2w : ℝ := lowJetSq (I := I) (M := M) g 2
    (lrRiemW2 (I := I) (M := M) g)
  have hJ1w : 0 ≤ J1w := jet_nonneg_lip (I := I) (M := M) g _
  have hJ2w : 0 ≤ J2w := jet_nonneg_lip (I := I) (M := M) g _
  refine ⟨2 * (C₀ * J1w + C₀ * J2w),
    mul_nonneg (by norm_num)
      (add_nonneg (mul_nonneg hC₀ hJ1w) (mul_nonneg hC₀ hJ2w)), ?_⟩
  intro T U
  have hsub :
      lrCurvF (I := I) (M := M) g T -
          lrCurvF (I := I) (M := M) g U =
        appCcRS (I := I) (M := M) g 0 2 4
            (lrRiemW1 (I := I) (M := M) g) (T - U) +
          appCcRS (I := I) (M := M) g 0 2 4
            (lrRiemW2 (I := I) (M := M) g) (T - U) := by
    rw [lrCurvF, lrCurvF, appCcRS_sub_right, appCcRS_sub_right]
    module
  have hX := happ (lrRiemW1 (I := I) (M := M) g) (T - U)
  have hY := happ (lrRiemW2 (I := I) (M := M) g) (T - U)
  have hmono :
      lowJetSq (I := I) (M := M) g 1 (T - U) ≤
        lowJetSq (I := I) (M := M) g 2 (T - U) :=
    jet_mono_lip (I := I) (M := M) g (by norm_num) _
  have hTU0 : 0 ≤ lowJetSq (I := I) (M := M) g 2 (T - U) :=
    jet_nonneg_lip (I := I) (M := M) g _
  rw [hsub]
  calc
    lowJetSq (I := I) (M := M) g 1
        (appCcRS (I := I) (M := M) g 0 2 4
            (lrRiemW1 (I := I) (M := M) g) (T - U) +
          appCcRS (I := I) (M := M) g 0 2 4
            (lrRiemW2 (I := I) (M := M) g) (T - U)) ≤
      2 * (lowJetSq (I := I) (M := M) g 1
          (appCcRS (I := I) (M := M) g 0 2 4
            (lrRiemW1 (I := I) (M := M) g) (T - U)) +
        lowJetSq (I := I) (M := M) g 1
          (appCcRS (I := I) (M := M) g 0 2 4
            (lrRiemW2 (I := I) (M := M) g) (T - U))) :=
      jet_add_lip (I := I) (M := M) g 1 _ _
    _ ≤ 2 * (C₀ * J1w *
          lowJetSq (I := I) (M := M) g 1 (T - U) +
        C₀ * J2w *
          lowJetSq (I := I) (M := M) g 1 (T - U)) := by
      refine mul_le_mul_of_nonneg_left (add_le_add ?_ ?_) (by norm_num)
      · simpa only [J1w] using hX
      · simpa only [J2w] using hY
    _ ≤ 2 * (C₀ * J1w *
          lowJetSq (I := I) (M := M) g 2 (T - U) +
        C₀ * J2w *
          lowJetSq (I := I) (M := M) g 2 (T - U)) := by
      refine mul_le_mul_of_nonneg_left (add_le_add ?_ ?_) (by norm_num)
      · exact mul_le_mul_of_nonneg_left hmono
          (mul_nonneg hC₀ hJ1w)
      · exact mul_le_mul_of_nonneg_left hmono
          (mul_nonneg hC₀ hJ2w)
    _ = 2 * (C₀ * J1w + C₀ * J2w) *
        lowJetSq (I := I) (M := M) g 2 (T - U) := by ring

private theorem quadB_tel
    (g gT gU : SmoothRiemannianMetric I M) :
    lrQB (I := I) (M := M) g gT -
        lrQB (I := I) (M := M) g gU =
      appCcRS (I := I) (M := M) g 0 3 4
          (armSlotEndoCc (I := I) (M := M) g 2
            (bdConnPair (I := I) (M := M) g gU))
          (lrOmegaHat (I := I) (M := M) g gT -
            lrOmegaHat (I := I) (M := M) g gU) +
        appCcRS (I := I) (M := M) g 0 3 4
          (armSlotEndoCc (I := I) (M := M) g 2
              (bdConnPair (I := I) (M := M) g gT) -
            armSlotEndoCc (I := I) (M := M) g 2
              (bdConnPair (I := I) (M := M) g gU))
          (lrOmegaHat (I := I) (M := M) g gT) := by
  rw [lrQB, lrQB, appCcRS_sub_right, appCcRS_sub_left]
  module

private theorem quadA_tel
    (g gT gU : SmoothRiemannianMetric I M) :
    lrQA (I := I) (M := M) g gT -
        lrQA (I := I) (M := M) g gU =
      appCcRS (I := I) (M := M) g 0 3 4
          (armSlotEndoCc (I := I) (M := M) g 2
            (bdConnPair (I := I) (M := M) g gU))
          (domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 3) 1)
            (lrOmegaHat (I := I) (M := M) g gT -
              lrOmegaHat (I := I) (M := M) g gU)) +
        appCcRS (I := I) (M := M) g 0 3 4
          (armSlotEndoCc (I := I) (M := M) g 2
              (bdConnPair (I := I) (M := M) g gT) -
            armSlotEndoCc (I := I) (M := M) g 2
              (bdConnPair (I := I) (M := M) g gU))
          (domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 3) 1)
            (lrOmegaHat (I := I) (M := M) g gT)) := by
  rw [lrQA, lrQA, dom_sub_lip, appCcRS_sub_right, appCcRS_sub_left]
  module

set_option maxHeartbeats 1600000 in
set_option linter.unusedVariables false in
private theorem quad_pair_h1
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (gT gU : SmoothRiemannianMetric I M),
        lowJetSq (I := I) (M := M) g 1
            (lrQuadF (I := I) (M := M) g gT -
              lrQuadF (I := I) (M := M) g gU) ≤
          C *
            (lowJetSq (I := I) (M := M) g 2
                (armSlotEndoCc (I := I) (M := M) g 2
                  (bdConnPair (I := I) (M := M) g gU)) *
              lowJetSq (I := I) (M := M) g 1
                (lrOmegaHat (I := I) (M := M) g gT -
                  lrOmegaHat (I := I) (M := M) g gU) +
            lowJetSq (I := I) (M := M) g 1
                (armSlotEndoCc (I := I) (M := M) g 2
                    (bdConnPair (I := I) (M := M) g gT) -
                  armSlotEndoCc (I := I) (M := M) g 2
                    (bdConnPair (I := I) (M := M) g gU)) *
              lowJetSq (I := I) (M := M) g 2
                (lrOmegaHat (I := I) (M := M) g gT)) := by
  obtain ⟨C₀, hC₀, happ⟩ :=
    app_h21_mul_lip (I := I) (M := M) hDim g 0 3 4
  obtain ⟨C₁, hC₁, happ12⟩ :=
    app_h12_mul_lip (I := I) (M := M) hDim g 0 3 4
  refine ⟨384 * (C₀ + C₁), by positivity, ?_⟩
  intro gT gU
  set cU : SmoothCcTensor g 3 4 :=
    armSlotEndoCc (I := I) (M := M) g 2
      (bdConnPair (I := I) (M := M) g gU) with hcU
  set cD : SmoothCcTensor g 3 4 :=
    armSlotEndoCc (I := I) (M := M) g 2
        (bdConnPair (I := I) (M := M) g gT) -
      armSlotEndoCc (I := I) (M := M) g 2
        (bdConnPair (I := I) (M := M) g gU) with hcD
  set hatT : SmoothCcTensor g 0 3 :=
    lrOmegaHat (I := I) (M := M) g gT with hhatT
  set hatD : SmoothCcTensor g 0 3 :=
    lrOmegaHat (I := I) (M := M) g gT -
      lrOmegaHat (I := I) (M := M) g gU with hhatD
  set S : ℝ :=
    lowJetSq (I := I) (M := M) g 2 cU *
        lowJetSq (I := I) (M := M) g 1 hatD +
      lowJetSq (I := I) (M := M) g 1 cD *
        lowJetSq (I := I) (M := M) g 2 hatT with hSdef
  have hS0 : 0 ≤ S :=
    add_nonneg
      (mul_nonneg (jet_nonneg_lip (I := I) (M := M) g _)
        (jet_nonneg_lip (I := I) (M := M) g _))
      (mul_nonneg (jet_nonneg_lip (I := I) (M := M) g _)
        (jet_nonneg_lip (I := I) (M := M) g _))
  set QBd : SmoothCcTensor g 0 4 :=
    lrQB (I := I) (M := M) g gT - lrQB (I := I) (M := M) g gU with hQBd
  set QAd : SmoothCcTensor g 0 4 :=
    lrQA (I := I) (M := M) g gT - lrQA (I := I) (M := M) g gU with hQAd
  have htelB : QBd =
      appCcRS (I := I) (M := M) g 0 3 4 cU hatD +
        appCcRS (I := I) (M := M) g 0 3 4 cD hatT := by
    rw [hQBd, hcU, hcD, hhatT, hhatD]
    exact quadB_tel (I := I) (M := M) g gT gU
  have htelA : QAd =
      appCcRS (I := I) (M := M) g 0 3 4 cU
          (domDomCongrSection (I := I) g
            (Equiv.swap (0 : Fin 3) 1) hatD) +
        appCcRS (I := I) (M := M) g 0 3 4 cD
          (domDomCongrSection (I := I) g
            (Equiv.swap (0 : Fin 3) 1) hatT) := by
    rw [hQAd, hcU, hcD, hhatT, hhatD]
    exact quadA_tel (I := I) (M := M) g gT gU
  set x : ℝ := lowJetSq (I := I) (M := M) g 1 QBd with hxdef
  set y : ℝ := lowJetSq (I := I) (M := M) g 1 QAd with hydef
  have hQB : x ≤ 2 * (C₀ + C₁) * S := by
    rw [hxdef]
    have hX := happ cU hatD
    have hY := happ12 cD hatT
    calc
      lowJetSq (I := I) (M := M) g 1 QBd =
          lowJetSq (I := I) (M := M) g 1
            (appCcRS (I := I) (M := M) g 0 3 4 cU hatD +
              appCcRS (I := I) (M := M) g 0 3 4 cD hatT) := by
        rw [htelB]
      _ ≤ 2 * (lowJetSq (I := I) (M := M) g 1
            (appCcRS (I := I) (M := M) g 0 3 4 cU hatD) +
          lowJetSq (I := I) (M := M) g 1
            (appCcRS (I := I) (M := M) g 0 3 4 cD hatT)) :=
        jet_add_lip (I := I) (M := M) g 1 _ _
      _ ≤ 2 * (C₀ * lowJetSq (I := I) (M := M) g 2 cU *
            lowJetSq (I := I) (M := M) g 1 hatD +
          C₁ * lowJetSq (I := I) (M := M) g 1 cD *
            lowJetSq (I := I) (M := M) g 2 hatT) :=
        mul_le_mul_of_nonneg_left (add_le_add hX hY) (by norm_num)
      _ ≤ 2 * (C₀ + C₁) * S := by
        rw [hSdef]
        linarith [mul_nonneg hC₀
            (mul_nonneg (jet_nonneg_lip (I := I) (M := M) g (m := 1) cD)
              (jet_nonneg_lip (I := I) (M := M) g (m := 2) hatT)),
          mul_nonneg hC₁
            (mul_nonneg (jet_nonneg_lip (I := I) (M := M) g (m := 2) cU)
              (jet_nonneg_lip (I := I) (M := M) g (m := 1) hatD))]
  have hQA : y ≤ 2 * (C₀ + C₁) * S := by
    rw [hydef]
    have hX := happ cU
      (domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 3) 1) hatD)
    have hY := happ12 cD
      (domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 3) 1) hatT)
    rw [dom_h1_lip] at hX
    rw [dom_h2_lip] at hY
    calc
      lowJetSq (I := I) (M := M) g 1 QAd =
          lowJetSq (I := I) (M := M) g 1
            (appCcRS (I := I) (M := M) g 0 3 4 cU
                (domDomCongrSection (I := I) g
                  (Equiv.swap (0 : Fin 3) 1) hatD) +
              appCcRS (I := I) (M := M) g 0 3 4 cD
                (domDomCongrSection (I := I) g
                  (Equiv.swap (0 : Fin 3) 1) hatT)) := by
        rw [htelA]
      _ ≤ 2 * (lowJetSq (I := I) (M := M) g 1
            (appCcRS (I := I) (M := M) g 0 3 4 cU
              (domDomCongrSection (I := I) g
                (Equiv.swap (0 : Fin 3) 1) hatD)) +
          lowJetSq (I := I) (M := M) g 1
            (appCcRS (I := I) (M := M) g 0 3 4 cD
              (domDomCongrSection (I := I) g
                (Equiv.swap (0 : Fin 3) 1) hatT))) :=
        jet_add_lip (I := I) (M := M) g 1 _ _
      _ ≤ 2 * (C₀ * lowJetSq (I := I) (M := M) g 2 cU *
            lowJetSq (I := I) (M := M) g 1 hatD +
          C₁ * lowJetSq (I := I) (M := M) g 1 cD *
            lowJetSq (I := I) (M := M) g 2 hatT) :=
        mul_le_mul_of_nonneg_left (add_le_add hX hY) (by norm_num)
      _ ≤ 2 * (C₀ + C₁) * S := by
        rw [hSdef]
        linarith [mul_nonneg hC₀
            (mul_nonneg (jet_nonneg_lip (I := I) (M := M) g (m := 1) cD)
              (jet_nonneg_lip (I := I) (M := M) g (m := 2) hatT)),
          mul_nonneg hC₁
            (mul_nonneg (jet_nonneg_lip (I := I) (M := M) g (m := 2) cU)
              (jet_nonneg_lip (I := I) (M := M) g (m := 1) hatD))]
  have hsplit :
      lrQuadF (I := I) (M := M) g gT -
          lrQuadF (I := I) (M := M) g gU =
        domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 4) 1) QBd +
          (QBd +
            (domDomCongrSection (I := I) g lrPermA QAd +
              (domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 4) 2) QAd +
                (domDomCongrSection (I := I) g lrPermB QAd +
                  domDomCongrSection (I := I) g lrPermC QAd)))) := by
    rw [hQBd, hQAd]
    simp only [lrQuadF, dom_sub_lip]
    abel
  have hd1 : lowJetSq (I := I) (M := M) g 1
      (domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 4) 1) QBd) =
      lowJetSq (I := I) (M := M) g 1 QBd :=
    dom_h1_lip (I := I) (M := M) g _ _
  have hd3 : lowJetSq (I := I) (M := M) g 1
      (domDomCongrSection (I := I) g lrPermA QAd) =
      lowJetSq (I := I) (M := M) g 1 QAd :=
    dom_h1_lip (I := I) (M := M) g _ _
  have hd4 : lowJetSq (I := I) (M := M) g 1
      (domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 4) 2) QAd) =
      lowJetSq (I := I) (M := M) g 1 QAd :=
    dom_h1_lip (I := I) (M := M) g _ _
  have hd5 : lowJetSq (I := I) (M := M) g 1
      (domDomCongrSection (I := I) g lrPermB QAd) =
      lowJetSq (I := I) (M := M) g 1 QAd :=
    dom_h1_lip (I := I) (M := M) g _ _
  have hd6 : lowJetSq (I := I) (M := M) g 1
      (domDomCongrSection (I := I) g lrPermC QAd) =
      lowJetSq (I := I) (M := M) g 1 QAd :=
    dom_h1_lip (I := I) (M := M) g _ _
  have hQB0 : 0 ≤ lowJetSq (I := I) (M := M) g 1 QBd :=
    jet_nonneg_lip (I := I) (M := M) g _
  have hQA0 : 0 ≤ lowJetSq (I := I) (M := M) g 1 QAd :=
    jet_nonneg_lip (I := I) (M := M) g _
  have h56 : lowJetSq (I := I) (M := M) g 1
      (domDomCongrSection (I := I) g lrPermB QAd +
        domDomCongrSection (I := I) g lrPermC QAd) ≤
      2 * (lowJetSq (I := I) (M := M) g 1 QAd +
        lowJetSq (I := I) (M := M) g 1 QAd) := by
    linarith [jet_add_lip (I := I) (M := M) g 1
        (domDomCongrSection (I := I) g lrPermB QAd)
        (domDomCongrSection (I := I) g lrPermC QAd),
      hd5, hd6]
  have h456 : lowJetSq (I := I) (M := M) g 1
      (domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 4) 2) QAd +
        (domDomCongrSection (I := I) g lrPermB QAd +
          domDomCongrSection (I := I) g lrPermC QAd)) ≤
      2 * lowJetSq (I := I) (M := M) g 1 QAd +
        2 * (2 * (lowJetSq (I := I) (M := M) g 1 QAd +
          lowJetSq (I := I) (M := M) g 1 QAd)) := by
    linarith [jet_add_lip (I := I) (M := M) g 1
        (domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 4) 2) QAd)
        (domDomCongrSection (I := I) g lrPermB QAd +
          domDomCongrSection (I := I) g lrPermC QAd),
      hd4, h56]
  have h3456 : lowJetSq (I := I) (M := M) g 1
      (domDomCongrSection (I := I) g lrPermA QAd +
        (domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 4) 2) QAd +
          (domDomCongrSection (I := I) g lrPermB QAd +
            domDomCongrSection (I := I) g lrPermC QAd))) ≤
      2 * lowJetSq (I := I) (M := M) g 1 QAd +
        2 * (2 * lowJetSq (I := I) (M := M) g 1 QAd +
          2 * (2 * (lowJetSq (I := I) (M := M) g 1 QAd +
            lowJetSq (I := I) (M := M) g 1 QAd))) := by
    linarith [jet_add_lip (I := I) (M := M) g 1
        (domDomCongrSection (I := I) g lrPermA QAd)
        (domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 4) 2) QAd +
          (domDomCongrSection (I := I) g lrPermB QAd +
            domDomCongrSection (I := I) g lrPermC QAd)),
      hd3, h456]
  have h23456 : lowJetSq (I := I) (M := M) g 1
      (QBd +
        (domDomCongrSection (I := I) g lrPermA QAd +
          (domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 4) 2) QAd +
            (domDomCongrSection (I := I) g lrPermB QAd +
              domDomCongrSection (I := I) g lrPermC QAd)))) ≤
      2 * lowJetSq (I := I) (M := M) g 1 QBd +
        2 * (2 * lowJetSq (I := I) (M := M) g 1 QAd +
          2 * (2 * lowJetSq (I := I) (M := M) g 1 QAd +
            2 * (2 * (lowJetSq (I := I) (M := M) g 1 QAd +
              lowJetSq (I := I) (M := M) g 1 QAd)))) := by
    linarith [jet_add_lip (I := I) (M := M) g 1 QBd
        (domDomCongrSection (I := I) g lrPermA QAd +
          (domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 4) 2) QAd +
            (domDomCongrSection (I := I) g lrPermB QAd +
              domDomCongrSection (I := I) g lrPermC QAd))),
      h3456]
  calc
    lowJetSq (I := I) (M := M) g 1
        (lrQuadF (I := I) (M := M) g gT -
          lrQuadF (I := I) (M := M) g gU) =
      lowJetSq (I := I) (M := M) g 1
        (domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 4) 1) QBd +
          (QBd +
            (domDomCongrSection (I := I) g lrPermA QAd +
              (domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 4) 2) QAd +
                (domDomCongrSection (I := I) g lrPermB QAd +
                  domDomCongrSection (I := I) g lrPermC QAd))))) := by
      rw [hsplit]
    _ ≤ 2 * lowJetSq (I := I) (M := M) g 1 QBd +
        2 * (2 * lowJetSq (I := I) (M := M) g 1 QBd +
          2 * (2 * lowJetSq (I := I) (M := M) g 1 QAd +
            2 * (2 * lowJetSq (I := I) (M := M) g 1 QAd +
              2 * (2 * (lowJetSq (I := I) (M := M) g 1 QAd +
                lowJetSq (I := I) (M := M) g 1 QAd))))) := by
      linarith [jet_add_lip (I := I) (M := M) g 1
          (domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 4) 1) QBd)
          (QBd +
            (domDomCongrSection (I := I) g lrPermA QAd +
              (domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 4) 2) QAd +
                (domDomCongrSection (I := I) g lrPermB QAd +
                  domDomCongrSection (I := I) g lrPermC QAd)))),
        hd1, h23456]
    _ = 2 * x +
        2 * (2 * x +
          2 * (2 * y +
            2 * (2 * y +
              2 * (2 * (y + y))))) := by
      rw [hxdef, hydef]
    _ ≤ 384 * (C₀ + C₁) * S := by nlinarith [hQB, hQA, hS0, hC₀, hC₁]

set_option maxHeartbeats 1600000 in
set_option linter.unusedVariables false in
private theorem r4_pair_h1
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (T U : SmoothCcTensor g 0 2) {δ : ℝ}
        (hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδU : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g U) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        {s : ℝ}, s ∈ Set.Icc (0 : ℝ) 1 →
        lowJetSq (I := I) (M := M) g 1
            (lieCovR4 (I := I) (M := M) g T hδT hδZ s -
              lieCovR4 (I := I) (M := M) g U hδU hδZ s) ≤
          C *
            (lowJetSq (I := I) (M := M) g 2 (T - U) +
              (lowJetSq (I := I) (M := M) g 2
                  (armSlotEndoCc (I := I) (M := M) g 2
                    (bdConnPair (I := I) (M := M) g
                      (realizedFam (I := I) g U 0 hδU hδZ s))) *
                lowJetSq (I := I) (M := M) g 1
                  (lrOmegaHat (I := I) (M := M) g
                      (realizedFam (I := I) g T 0 hδT hδZ s) -
                    lrOmegaHat (I := I) (M := M) g
                      (realizedFam (I := I) g U 0 hδU hδZ s)) +
              lowJetSq (I := I) (M := M) g 1
                  (armSlotEndoCc (I := I) (M := M) g 2
                      (bdConnPair (I := I) (M := M) g
                        (realizedFam (I := I) g T 0 hδT hδZ s)) -
                    armSlotEndoCc (I := I) (M := M) g 2
                      (bdConnPair (I := I) (M := M) g
                        (realizedFam (I := I) g U 0 hδU hδZ s))) *
                lowJetSq (I := I) (M := M) g 2
                  (lrOmegaHat (I := I) (M := M) g
                    (realizedFam (I := I) g T 0 hδT hδZ s)))) := by
  obtain ⟨Cc, hCc, hcurv⟩ :=
    curvF_pair_h1 (I := I) (M := M) hDim g
  obtain ⟨Cq, hCq, hquad⟩ :=
    quad_pair_h1 (I := I) (M := M) hDim g
  refine ⟨2 * Cc + 2 * Cq, by positivity, ?_⟩
  intro T U δ hδT hδU hδZ s hs
  set gmT : SmoothRiemannianMetric I M :=
    realizedFam (I := I) g T 0 hδT hδZ s with hgmT
  set gmU : SmoothRiemannianMetric I M :=
    realizedFam (I := I) g U 0 hδU hδZ s with hgmU
  set CFd : SmoothCcTensor g 0 4 :=
    lrCurvF (I := I) (M := M) g T -
      lrCurvF (I := I) (M := M) g U with hCFd
  set QFd : SmoothCcTensor g 0 4 :=
    lrQuadF (I := I) (M := M) g gmT -
      lrQuadF (I := I) (M := M) g gmU with hQFd
  have hdecomp :
      lieCovR4 (I := I) (M := M) g T hδT hδZ s -
          lieCovR4 (I := I) (M := M) g U hδU hδZ s =
        (-(s / 2) : ℝ) • CFd + (-1 : ℝ) • QFd := by
    rw [hCFd, hQFd, hgmT, hgmU,
      lieCovR4_eq (I := I) (M := M) g T hδT hδZ s,
      lieCovR4_eq (I := I) (M := M) g U hδU hδZ s]
    module
  set a : ℝ := lowJetSq (I := I) (M := M) g 2 (T - U) with ha
  set b : ℝ :=
    lowJetSq (I := I) (M := M) g 2
        (armSlotEndoCc (I := I) (M := M) g 2
          (bdConnPair (I := I) (M := M) g gmU)) *
      lowJetSq (I := I) (M := M) g 1
        (lrOmegaHat (I := I) (M := M) g gmT -
          lrOmegaHat (I := I) (M := M) g gmU) +
    lowJetSq (I := I) (M := M) g 1
        (armSlotEndoCc (I := I) (M := M) g 2
            (bdConnPair (I := I) (M := M) g gmT) -
          armSlotEndoCc (I := I) (M := M) g 2
            (bdConnPair (I := I) (M := M) g gmU)) *
      lowJetSq (I := I) (M := M) g 2
        (lrOmegaHat (I := I) (M := M) g gmT) with hb
  have ha0 : 0 ≤ a := jet_nonneg_lip (I := I) (M := M) g _
  have hb0 : 0 ≤ b :=
    add_nonneg
      (mul_nonneg (jet_nonneg_lip (I := I) (M := M) g _)
        (jet_nonneg_lip (I := I) (M := M) g _))
      (mul_nonneg (jet_nonneg_lip (I := I) (M := M) g _)
        (jet_nonneg_lip (I := I) (M := M) g _))
  have hCF : lowJetSq (I := I) (M := M) g 1 CFd ≤ Cc * a := by
    rw [hCFd, ha]
    exact hcurv T U
  have hQF : lowJetSq (I := I) (M := M) g 1 QFd ≤ Cq * b := by
    rw [hQFd, hb]
    exact hquad gmT gmU
  have hs2 : (s / 2) ^ 2 ≤ 1 := by
    obtain ⟨hs0, hs1⟩ := hs
    nlinarith
  set u : ℝ := lowJetSq (I := I) (M := M) g 1 CFd with hu
  set v : ℝ := lowJetSq (I := I) (M := M) g 1 QFd with hv
  have hu0 : 0 ≤ u := jet_nonneg_lip (I := I) (M := M) g _
  have hv0 : 0 ≤ v := jet_nonneg_lip (I := I) (M := M) g _
  calc
    lowJetSq (I := I) (M := M) g 1
        (lieCovR4 (I := I) (M := M) g T hδT hδZ s -
          lieCovR4 (I := I) (M := M) g U hδU hδZ s) =
      lowJetSq (I := I) (M := M) g 1
        ((-(s / 2) : ℝ) • CFd + (-1 : ℝ) • QFd) := by
      rw [hdecomp]
    _ ≤ 2 * (lowJetSq (I := I) (M := M) g 1
          ((-(s / 2) : ℝ) • CFd) +
        lowJetSq (I := I) (M := M) g 1
          ((-1 : ℝ) • QFd)) :=
      jet_add_lip (I := I) (M := M) g 1 _ _
    _ = 2 * ((-(s / 2)) ^ 2 * u + (-1 : ℝ) ^ 2 * v) := by
      rw [jet_smul_lip, jet_smul_lip, hu, hv]
    _ ≤ 2 * (Cc * a + Cq * b) := by
      have h1 : (-(s / 2)) ^ 2 * u ≤ Cc * a := by
        have hle : (-(s / 2)) ^ 2 * u ≤ 1 * u := by
          have : (-(s / 2)) ^ 2 = (s / 2) ^ 2 := by ring
          rw [this]
          exact mul_le_mul_of_nonneg_right hs2 hu0
        rw [one_mul] at hle
        exact hle.trans (by rw [hu]; exact hCF)
      have h2 : (-1 : ℝ) ^ 2 * v ≤ Cq * b := by
        have : ((-1 : ℝ) ^ 2 * v) = v := by ring
        rw [this, hv]
        exact hQF
      linarith
    _ ≤ (2 * Cc + 2 * Cq) * (a + b) := by nlinarith [hCc, hCq, ha0, hb0]

private theorem lcvPair_eq_lip
    (g gm : SmoothRiemannianMetric I M) :
    lieCovPair (I := I) (M := M) g gm =
      appCcRS (I := I) (M := M) g 6 4 2
        (pureTrace (I := I) (M := M) g gm 2)
        (pureTrace (I := I) (M := M) g gm 4) := rfl

set_option maxHeartbeats 1600000 in
set_option linter.unusedVariables false in
private theorem lcvPair_pair_h2
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
            (lieCovPair (I := I) (M := M) g gT -
              lieCovPair (I := I) (M := M) g gU) ≤
          (C * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
            (T - U)‖) ^ 2 := by
  obtain ⟨ρ₂, C₂, hρ₂, hC₂, hp₂⟩ :=
    LowBaseInternal.trace2_pair_h2 (I := I) (M := M) hDim g
  obtain ⟨ρ₄, C₄, hρ₄, hC₄, hp₄⟩ :=
    LowBaseInternal.trace4_pair_h2 (I := I) (M := M) hDim g
  obtain ⟨ρb₂, B₂, hρb₂, hB₂, hb₂⟩ :=
    LowBaseInternal.trace2_h2_bdd (I := I) (M := M) hDim g
  obtain ⟨ρb₄, B₄, hρb₄, hB₄, hb₄⟩ :=
    LowBaseInternal.trace4_h2_bdd (I := I) (M := M) hDim g
  obtain ⟨Ca, hCa, happ⟩ :=
    app_h2_mul_lip (I := I) (M := M) hDim g 6 4 2
  refine ⟨min (min ρ₂ ρ₄) (min ρb₂ ρb₄),
    Real.sqrt (2 * (Ca * B₂ ^ 2 * C₄ ^ 2 + Ca * C₂ ^ 2 * B₄ ^ 2)),
    lt_min (lt_min hρ₂ hρ₄) (lt_min hρb₂ hρb₄),
    Real.sqrt_nonneg _, ?_⟩
  intro T U gT gU hTtie hUtie hTn hUn
  have hT₂ : ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρ₂ :=
    hTn.trans (le_trans (min_le_left _ _) (min_le_left _ _))
  have hU₂ : ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ ≤ ρ₂ :=
    hUn.trans (le_trans (min_le_left _ _) (min_le_left _ _))
  have hT₄ : ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρ₄ :=
    hTn.trans (le_trans (min_le_left _ _) (min_le_right _ _))
  have hU₄ : ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ ≤ ρ₄ :=
    hUn.trans (le_trans (min_le_left _ _) (min_le_right _ _))
  have hTb₂ : ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρb₂ :=
    hTn.trans (le_trans (min_le_right _ _) (min_le_left _ _))
  have hUb₂ : ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ ≤ ρb₂ :=
    hUn.trans (le_trans (min_le_right _ _) (min_le_left _ _))
  have hTb₄ : ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρb₄ :=
    hTn.trans (le_trans (min_le_right _ _) (min_le_right _ _))
  set N : ℝ :=
    ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U)‖ with hN
  have hN0 : 0 ≤ N := norm_nonneg _
  have htel :
      lieCovPair (I := I) (M := M) g gT -
          lieCovPair (I := I) (M := M) g gU =
        appCcRS (I := I) (M := M) g 6 4 2
            (pureTrace (I := I) (M := M) g gU 2)
            (pureTrace (I := I) (M := M) g gT 4 -
              pureTrace (I := I) (M := M) g gU 4) +
          appCcRS (I := I) (M := M) g 6 4 2
            (pureTrace (I := I) (M := M) g gT 2 -
              pureTrace (I := I) (M := M) g gU 2)
            (pureTrace (I := I) (M := M) g gT 4) := by
    rw [lcvPair_eq_lip, lcvPair_eq_lip,
      appCcRS_sub_right, appCcRS_sub_left]
    module
  have hXraw := happ
    (pureTrace (I := I) (M := M) g gU 2)
    (pureTrace (I := I) (M := M) g gT 4 -
      pureTrace (I := I) (M := M) g gU 4)
  have hYraw := happ
    (pureTrace (I := I) (M := M) g gT 2 -
      pureTrace (I := I) (M := M) g gU 2)
    (pureTrace (I := I) (M := M) g gT 4)
  have hb₂U := hb₂ U gU hUtie hUb₂
  have hb₄T := hb₄ T gT hTtie hTb₄
  have hp₂TU := hp₂ T U gT gU hTtie hUtie hT₂ hU₂
  have hp₄TU := hp₄ T U gT gU hTtie hUtie hT₄ hU₄
  set j2U : ℝ := lowJetSq (I := I) (M := M) g 2
    (pureTrace (I := I) (M := M) g gU 2) with hj2U
  set j4T : ℝ := lowJetSq (I := I) (M := M) g 2
    (pureTrace (I := I) (M := M) g gT 4) with hj4T
  set j2d : ℝ := lowJetSq (I := I) (M := M) g 2
    (pureTrace (I := I) (M := M) g gT 2 -
      pureTrace (I := I) (M := M) g gU 2) with hj2d
  set j4d : ℝ := lowJetSq (I := I) (M := M) g 2
    (pureTrace (I := I) (M := M) g gT 4 -
      pureTrace (I := I) (M := M) g gU 4) with hj4d
  have hj2U0 : 0 ≤ j2U := jet_nonneg_lip (I := I) (M := M) g _
  have hj4T0 : 0 ≤ j4T := jet_nonneg_lip (I := I) (M := M) g _
  have hj2d0 : 0 ≤ j2d := jet_nonneg_lip (I := I) (M := M) g _
  have hj4d0 : 0 ≤ j4d := jet_nonneg_lip (I := I) (M := M) g _
  have hsq :
      Real.sqrt (2 * (Ca * B₂ ^ 2 * C₄ ^ 2 +
          Ca * C₂ ^ 2 * B₄ ^ 2)) ^ 2 =
        2 * (Ca * B₂ ^ 2 * C₄ ^ 2 + Ca * C₂ ^ 2 * B₄ ^ 2) := by
    exact Real.sq_sqrt (by positivity)
  calc
    lowJetSq (I := I) (M := M) g 2
        (lieCovPair (I := I) (M := M) g gT -
          lieCovPair (I := I) (M := M) g gU) =
      lowJetSq (I := I) (M := M) g 2
        (appCcRS (I := I) (M := M) g 6 4 2
            (pureTrace (I := I) (M := M) g gU 2)
            (pureTrace (I := I) (M := M) g gT 4 -
              pureTrace (I := I) (M := M) g gU 4) +
          appCcRS (I := I) (M := M) g 6 4 2
            (pureTrace (I := I) (M := M) g gT 2 -
              pureTrace (I := I) (M := M) g gU 2)
            (pureTrace (I := I) (M := M) g gT 4)) := by
      rw [htel]
    _ ≤ 2 * (lowJetSq (I := I) (M := M) g 2
          (appCcRS (I := I) (M := M) g 6 4 2
            (pureTrace (I := I) (M := M) g gU 2)
            (pureTrace (I := I) (M := M) g gT 4 -
              pureTrace (I := I) (M := M) g gU 4)) +
        lowJetSq (I := I) (M := M) g 2
          (appCcRS (I := I) (M := M) g 6 4 2
            (pureTrace (I := I) (M := M) g gT 2 -
              pureTrace (I := I) (M := M) g gU 2)
            (pureTrace (I := I) (M := M) g gT 4))) :=
      jet_add_lip (I := I) (M := M) g 2 _ _
    _ ≤ 2 * (Ca * j2U * j4d + Ca * j2d * j4T) := by
      linarith [hXraw, hYraw]
    _ ≤ 2 * (Ca * B₂ ^ 2 * ((C₄ * N) ^ 2) +
        Ca * ((C₂ * N) ^ 2) * B₄ ^ 2) := by
      have h1 : Ca * j2U * j4d ≤ Ca * B₂ ^ 2 * ((C₄ * N) ^ 2) := by
        have hu : j2U ≤ B₂ ^ 2 := by rw [hj2U]; exact hb₂U
        have hd : j4d ≤ (C₄ * N) ^ 2 := by rw [hj4d, hN]; exact hp₄TU
        have hstep := mul_le_mul hu hd hj4d0
          (le_trans hj2U0 hu)
        calc
          Ca * j2U * j4d = Ca * (j2U * j4d) := by ring
          _ ≤ Ca * (B₂ ^ 2 * ((C₄ * N) ^ 2)) :=
            mul_le_mul_of_nonneg_left hstep hCa
          _ = Ca * B₂ ^ 2 * ((C₄ * N) ^ 2) := by ring
      have h2 : Ca * j2d * j4T ≤ Ca * ((C₂ * N) ^ 2) * B₄ ^ 2 := by
        have hd : j2d ≤ (C₂ * N) ^ 2 := by rw [hj2d, hN]; exact hp₂TU
        have hu : j4T ≤ B₄ ^ 2 := by rw [hj4T]; exact hb₄T
        have hstep := mul_le_mul hd hu hj4T0
          (le_trans hj2d0 hd)
        calc
          Ca * j2d * j4T = Ca * (j2d * j4T) := by ring
          _ ≤ Ca * (((C₂ * N) ^ 2) * B₄ ^ 2) :=
            mul_le_mul_of_nonneg_left hstep hCa
          _ = Ca * ((C₂ * N) ^ 2) * B₄ ^ 2 := by ring
      linarith
    _ = (Real.sqrt (2 * (Ca * B₂ ^ 2 * C₄ ^ 2 +
          Ca * C₂ ^ 2 * B₄ ^ 2)) * N) ^ 2 := by
      conv_rhs => rw [mul_pow, hsq]
      ring

private theorem slot_l2_lip
    (g : SmoothRiemannianMetric I M) (r s i : ℕ)
    (Φ : SmoothCcTensor g r s) :
    ‖iteratedCovGrad (I := I) g (r + 1) (s + 1) i
        (slotExtend (I := I) (M := M) g r s Φ)‖ ^ 2 ≤
      (Module.finrank ℝ E : ℝ) *
        ‖iteratedCovGrad (I := I) g r s i Φ‖ ^ 2 := by
  let F : M → ℝ := fun x => (Module.finrank ℝ E : ℝ) *
    riemannianFiberNormSq (I := I) (M := M) g r (s + i) x
      ((iteratedCovGrad (I := I) g r s i Φ).toSection x)
  have hF : MeasureTheory.Integrable F
      (riemannianVolumeMeasure (I := I) (M := M) g) := by
    dsimp only [F]
    exact (integrable_riemannianFiberNormSq_toSection
      (I := I) (M := M) g r (s + i)
      (iteratedCovGrad (I := I) g r s i Φ)).const_mul _
  have hsq := normSq_le_integral_of_pointwise_fiberNormSq_le_rs
    (I := I) (M := M) g (r + 1) ((s + 1) + i)
    (iteratedCovGrad (I := I) g (r + 1) (s + 1) i
      (slotExtend (I := I) (M := M) g r s Φ))
    F hF (fun x =>
      rfns_iteratedCovGrad_slotExtend_le
        (I := I) (M := M) g r s Φ i x)
  have hint : (∫ x,
      riemannianFiberNormSq (I := I) (M := M) g r (s + i) x
        ((iteratedCovGrad (I := I) g r s i Φ).toSection x)
      ∂(riemannianVolumeMeasure (I := I) (M := M) g)) =
      ‖iteratedCovGrad (I := I) g r s i Φ‖ ^ 2 := by
    rw [SmoothCcTensor.norm_def,
      tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs
        (I := I) (M := M) g r (s + i)]
  dsimp only [F] at hsq
  rw [MeasureTheory.integral_const_mul, hint] at hsq
  exact hsq

private theorem slot_h1_lip
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (Φ : SmoothCcTensor g r s) :
    lowJetSq (I := I) (M := M) g 1
        (slotExtend (I := I) (M := M) g r s Φ) ≤
      (Module.finrank ℝ E : ℝ) *
        lowJetSq (I := I) (M := M) g 1 Φ := by
  unfold lowJetSq
  calc
    ∑ i ∈ Finset.range 2,
        ‖iteratedCovGrad (I := I) g (r + 1) (s + 1) i
          (slotExtend (I := I) (M := M) g r s Φ)‖ ^ 2 ≤
      ∑ i ∈ Finset.range 2, (Module.finrank ℝ E : ℝ) *
        ‖iteratedCovGrad (I := I) g r s i Φ‖ ^ 2 :=
      Finset.sum_le_sum fun i _ =>
        slot_l2_lip (I := I) (M := M) g r s i Φ
    _ = (Module.finrank ℝ E : ℝ) *
        ∑ i ∈ Finset.range 2,
          ‖iteratedCovGrad (I := I) g r s i Φ‖ ^ 2 := by
      rw [Finset.mul_sum]

private theorem slot_h2_lip
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (Φ : SmoothCcTensor g r s) :
    lowJetSq (I := I) (M := M) g 2
        (slotExtend (I := I) (M := M) g r s Φ) ≤
      (Module.finrank ℝ E : ℝ) *
        lowJetSq (I := I) (M := M) g 2 Φ := by
  unfold lowJetSq
  calc
    ∑ i ∈ Finset.range 3,
        ‖iteratedCovGrad (I := I) g (r + 1) (s + 1) i
          (slotExtend (I := I) (M := M) g r s Φ)‖ ^ 2 ≤
      ∑ i ∈ Finset.range 3, (Module.finrank ℝ E : ℝ) *
        ‖iteratedCovGrad (I := I) g r s i Φ‖ ^ 2 :=
      Finset.sum_le_sum fun i _ =>
        slot_l2_lip (I := I) (M := M) g r s i Φ
    _ = (Module.finrank ℝ E : ℝ) *
        ∑ i ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g r s i Φ‖ ^ 2 := by
      rw [Finset.mul_sum]

private theorem reindex_jet_lip
    (g : SmoothRiemannianMetric I M) {r s m : ℕ}
    (R : SmoothCcTensor g r s) (σ : Equiv.Perm (Fin r)) :
    lowJetSq (I := I) (M := M) g m
        (reindexCoeffGen (I := I) (M := M) g r s R σ) =
      lowJetSq (I := I) (M := M) g m R := by
  unfold lowJetSq
  apply Finset.sum_congr rfl
  intro q _
  rw [SmoothCcTensor.norm_def,
    tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs,
    SmoothCcTensor.norm_def,
    tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs]
  apply MeasureTheory.integral_congr_ae
  exact Filter.Eventually.of_forall fun x =>
    rfns_iteratedCovGrad_reindexCoeffGen_eq
      (I := I) (M := M) g r s R σ q x

private theorem rsperm_l2_lip
    (g : SmoothRiemannianMetric I M) {r s : ℕ}
    (σ : Equiv.Perm (Fin s)) (S : SmoothCcTensor g r s) (i : ℕ) :
    ‖iteratedCovGrad (I := I) g r s i
        (rsDomDomCongrSection (I := I) (M := M) g r s σ S)‖ ^ 2 =
      ‖iteratedCovGrad (I := I) g r s i S‖ ^ 2 := by
  rw [SmoothCcTensor.norm_def,
    tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs,
    SmoothCcTensor.norm_def,
    tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs]
  refine MeasureTheory.integral_congr_ae
    (Filter.Eventually.of_forall fun x => ?_)
  exact rfns_iteratedCovGrad_rs_eq_of_section_domDomCongr
    (I := I) (M := M) g r s σ S
      (rsDomDomCongrSection (I := I) (M := M) g r s σ S)
      (fun y d => by
        rw [rsDomDomCongrSection_toSection,
          toModel_rsDomDomCongr_apply]) i x

private theorem rsperm_h1_lip
    (g : SmoothRiemannianMetric I M) {r s : ℕ}
    (σ : Equiv.Perm (Fin s)) (S : SmoothCcTensor g r s) :
    lowJetSq (I := I) (M := M) g 1
        (rsDomDomCongrSection (I := I) (M := M) g r s σ S) =
      lowJetSq (I := I) (M := M) g 1 S := by
  unfold lowJetSq
  apply Finset.sum_congr rfl
  intro i _
  exact rsperm_l2_lip (I := I) (M := M) g σ S i

set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 1600000 in
private theorem armSlot_succ_lip
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (A : ContMDiffSection I (E →L[ℝ] (E →L[ℝ] E)) ∞
      (fun x : M => TangentSpace I x →L[ℝ]
        (TangentSpace I x →L[ℝ] TangentSpace I x))) :
    armSlotEndoCc (I := I) (M := M) g (s + 1) A =
      reindexCoeffGen (I := I) (M := M) g (s + 1 + 1) (s + 1 + 1 + 1)
        (rsDomDomCongrSection (I := I) (M := M) g
          (s + 1 + 1) (s + 1 + 1 + 1)
          ((Equiv.swap (0 : Fin (s + 1 + 1 + 1)) 1).trans
            (Equiv.swap (1 : Fin (s + 1 + 1 + 1)) 2))
          (slotExtend (I := I) (M := M) g (s + 1) (s + 1 + 1)
            (armSlotEndoCc (I := I) (M := M) g s A)))
        (Equiv.swap (0 : Fin (s + 1 + 1)) 1) := by
  classical
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro D
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro m
  dsimp only
  rw [armSlotEndoCc_toSection]
  rw [show (TensorRSSpace.ofCLM
      (armSlotFib (I := I) (M := M) (s + 1) x (A x)) :
        Tensor0SSpace (s + 1 + 1) I x →L[ℝ]
          Tensor0SSpace (s + 1 + 1 + 1) I x) D =
    armSlotFib (I := I) (M := M) (s + 1) x (A x) D from rfl]
  rw [armSlotFib_apply_eval]
  rw [reindexCoeffGen_toSection, reindexCoeffFibGen_apply,
    rsDomDomCongrSection_toSection, toModel_rsDomDomCongr_apply,
    ContinuousMultilinearMap.domDomCongr_apply, slotExtend_toSection]
  rw [show (fun k : Fin (s + 1 + 1 + 1) =>
      m (((Equiv.swap (0 : Fin (s + 1 + 1 + 1)) 1).trans
        (Equiv.swap (1 : Fin (s + 1 + 1 + 1)) 2)) k)) =
      Fin.cons (m (((Equiv.swap (0 : Fin (s + 1 + 1 + 1)) 1).trans
          (Equiv.swap (1 : Fin (s + 1 + 1 + 1)) 2)) 0))
        (fun j : Fin (s + 1 + 1) =>
          m (((Equiv.swap (0 : Fin (s + 1 + 1 + 1)) 1).trans
            (Equiv.swap (1 : Fin (s + 1 + 1 + 1)) 2)) (Fin.succ j))) from by
    funext k
    refine Fin.cases ?_ (fun j => ?_) k
    · simp only [Fin.cons_zero]
    · simp only [Fin.cons_succ]]
  rw [slotExtendFib_apply_eval]
  rw [armSlotEndoCc_toSection]
  rw [show (TensorRSSpace.ofCLM
      (armSlotFib (I := I) (M := M) s x (A x)) :
        Tensor0SSpace (s + 1) I x →L[ℝ]
          Tensor0SSpace (s + 1 + 1) I x)
      ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) (s + 1) x)
        (Tensor0SSpace.ofModel
          (ContinuousMultilinearMap.domDomCongr
            (Equiv.swap (0 : Fin (s + 1 + 1)) 1)
            (Tensor0SSpace.toModel D)))
        (m (((Equiv.swap (0 : Fin (s + 1 + 1 + 1)) 1).trans
          (Equiv.swap (1 : Fin (s + 1 + 1 + 1)) 2)) 0))) =
    armSlotFib (I := I) (M := M) s x (A x)
      ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) (s + 1) x)
        (Tensor0SSpace.ofModel
          (ContinuousMultilinearMap.domDomCongr
            (Equiv.swap (0 : Fin (s + 1 + 1)) 1)
            (Tensor0SSpace.toModel D)))
        (m (((Equiv.swap (0 : Fin (s + 1 + 1 + 1)) 1).trans
          (Equiv.swap (1 : Fin (s + 1 + 1 + 1)) 2)) 0))) from rfl]
  rw [armSlotFib_apply_eval]
  rw [slotInsertEndoFib_apply_eval, slotInsertEndoFib_apply_eval]
  simp only [TensorMultilinear.tensor0S_curry_apply_eval,
    Tensor0SSpace.toModel_ofModel, ContinuousMultilinearMap.domDomCongr_apply]
  congr 1
  funext k
  refine Fin.cases ?_ (fun k₁ => Fin.cases ?_ (fun k₂ => ?_) k₁) k
  · rfl
  · rfl
  · rfl

set_option maxHeartbeats 1600000 in
private theorem rfns_arm_le_lip
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (A : ContMDiffSection I (E →L[ℝ] (E →L[ℝ] E)) ∞
      (fun x : M => TangentSpace I x →L[ℝ]
        (TangentSpace I x →L[ℝ] TangentSpace I x)))
    (i : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g (s + 1) ((s + 1 + 1) + i) x
        ((iteratedCovGrad (I := I) g (s + 1) (s + 1 + 1) i
          (armSlotEndoCc (I := I) (M := M) g s A)).toSection x) ≤
      (Module.finrank ℝ E : ℝ) ^ s *
        riemannianFiberNormSq (I := I) (M := M) g 1 (1 + 1 + i) x
          ((iteratedCovGrad (I := I) g 1 (1 + 1) i
            (armSlotEndoCc (I := I) (M := M) g 0 A)).toSection x) := by
  induction s with
  | zero =>
    rw [pow_zero, one_mul]
  | succ s ih =>
    have hfr : (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ) := Nat.cast_nonneg _
    have hA : riemannianFiberNormSq (I := I) (M := M) g
          (s + 1 + 1) ((s + 1 + 1 + 1) + i) x
          ((iteratedCovGrad (I := I) g (s + 1 + 1) (s + 1 + 1 + 1) i
            (armSlotEndoCc (I := I) (M := M) g (s + 1) A)).toSection x) =
        riemannianFiberNormSq (I := I) (M := M) g
          (s + 1 + 1) ((s + 1 + 1 + 1) + i) x
          ((iteratedCovGrad (I := I) g (s + 1 + 1) (s + 1 + 1 + 1) i
            (slotExtend (I := I) (M := M) g (s + 1) (s + 1 + 1)
              (armSlotEndoCc (I := I) (M := M) g s A))).toSection x) := by
      rw [armSlot_succ_lip (I := I) (M := M) g s A]
      exact rfns_iteratedCovGrad_rsDomDomCongr_both_eq (I := I) (M := M) g
        (s + 1 + 1) (s + 1 + 1 + 1)
        (Equiv.swap (0 : Fin (s + 1 + 1)) 1)
        ((Equiv.swap (0 : Fin (s + 1 + 1 + 1)) 1).trans
          (Equiv.swap (1 : Fin (s + 1 + 1 + 1)) 2))
        (slotExtend (I := I) (M := M) g (s + 1) (s + 1 + 1)
          (armSlotEndoCc (I := I) (M := M) g s A)) i x
    rw [hA]
    refine le_trans (rfns_iteratedCovGrad_slotExtend_le (I := I) (M := M) g
      (s + 1) (s + 1 + 1)
      (armSlotEndoCc (I := I) (M := M) g s A) i x) ?_
    calc (Module.finrank ℝ E : ℝ) *
            riemannianFiberNormSq (I := I) (M := M) g
              (s + 1) ((s + 1 + 1) + i) x
              ((iteratedCovGrad (I := I) g (s + 1) (s + 1 + 1) i
                (armSlotEndoCc (I := I) (M := M) g s A)).toSection x)
        ≤ (Module.finrank ℝ E : ℝ) *
            ((Module.finrank ℝ E : ℝ) ^ s *
              riemannianFiberNormSq (I := I) (M := M) g 1 (1 + 1 + i) x
                ((iteratedCovGrad (I := I) g 1 (1 + 1) i
                  (armSlotEndoCc (I := I) (M := M) g 0 A)).toSection x)) :=
          mul_le_mul_of_nonneg_left ih hfr
      _ = (Module.finrank ℝ E : ℝ) ^ (s + 1) *
            riemannianFiberNormSq (I := I) (M := M) g 1 (1 + 1 + i) x
              ((iteratedCovGrad (I := I) g 1 (1 + 1) i
                (armSlotEndoCc (I := I) (M := M) g 0 A)).toSection x) := by
          rw [pow_succ]
          ring

private theorem arm_l2_lip
    (g : SmoothRiemannianMetric I M) (s i : ℕ)
    (A : ContMDiffSection I (E →L[ℝ] (E →L[ℝ] E)) ∞
      (fun x : M => TangentSpace I x →L[ℝ]
        (TangentSpace I x →L[ℝ] TangentSpace I x))) :
    ‖iteratedCovGrad (I := I) g (s + 1) (s + 1 + 1) i
        (armSlotEndoCc (I := I) (M := M) g s A)‖ ^ 2 ≤
      (Module.finrank ℝ E : ℝ) ^ s *
        ‖iteratedCovGrad (I := I) g 1 (1 + 1) i
          (armSlotEndoCc (I := I) (M := M) g 0 A)‖ ^ 2 := by
  let F : M → ℝ := fun x => (Module.finrank ℝ E : ℝ) ^ s *
    riemannianFiberNormSq (I := I) (M := M) g 1 (1 + 1 + i) x
      ((iteratedCovGrad (I := I) g 1 (1 + 1) i
        (armSlotEndoCc (I := I) (M := M) g 0 A)).toSection x)
  have hF : MeasureTheory.Integrable F
      (riemannianVolumeMeasure (I := I) (M := M) g) := by
    dsimp only [F]
    exact (integrable_riemannianFiberNormSq_toSection
      (I := I) (M := M) g 1 (1 + 1 + i)
      (iteratedCovGrad (I := I) g 1 (1 + 1) i
        (armSlotEndoCc (I := I) (M := M) g 0 A))).const_mul _
  have hsq := normSq_le_integral_of_pointwise_fiberNormSq_le_rs
    (I := I) (M := M) g (s + 1) ((s + 1 + 1) + i)
    (iteratedCovGrad (I := I) g (s + 1) (s + 1 + 1) i
      (armSlotEndoCc (I := I) (M := M) g s A))
    F hF (fun x =>
      rfns_arm_le_lip (I := I) (M := M) g s A i x)
  have hint : (∫ x,
      riemannianFiberNormSq (I := I) (M := M) g 1 (1 + 1 + i) x
        ((iteratedCovGrad (I := I) g 1 (1 + 1) i
          (armSlotEndoCc (I := I) (M := M) g 0 A)).toSection x)
      ∂(riemannianVolumeMeasure (I := I) (M := M) g)) =
      ‖iteratedCovGrad (I := I) g 1 (1 + 1) i
        (armSlotEndoCc (I := I) (M := M) g 0 A)‖ ^ 2 := by
    rw [SmoothCcTensor.norm_def,
      tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs
        (I := I) (M := M) g 1 (1 + 1 + i)]
  dsimp only [F] at hsq
  rw [MeasureTheory.integral_const_mul, hint] at hsq
  exact hsq

private theorem arm_h1_lip
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (A : ContMDiffSection I (E →L[ℝ] (E →L[ℝ] E)) ∞
      (fun x : M => TangentSpace I x →L[ℝ]
        (TangentSpace I x →L[ℝ] TangentSpace I x))) :
    lowJetSq (I := I) (M := M) g 1
        (armSlotEndoCc (I := I) (M := M) g s A) ≤
      (Module.finrank ℝ E : ℝ) ^ s *
        lowJetSq (I := I) (M := M) g 1
          (armSlotEndoCc (I := I) (M := M) g 0 A) := by
  unfold lowJetSq
  calc
    ∑ i ∈ Finset.range 2,
        ‖iteratedCovGrad (I := I) g (s + 1) (s + 1 + 1) i
          (armSlotEndoCc (I := I) (M := M) g s A)‖ ^ 2 ≤
      ∑ i ∈ Finset.range 2, (Module.finrank ℝ E : ℝ) ^ s *
        ‖iteratedCovGrad (I := I) g 1 (1 + 1) i
          (armSlotEndoCc (I := I) (M := M) g 0 A)‖ ^ 2 :=
      Finset.sum_le_sum fun i _ =>
        arm_l2_lip (I := I) (M := M) g s i A
    _ = (Module.finrank ℝ E : ℝ) ^ s *
        ∑ i ∈ Finset.range 2,
          ‖iteratedCovGrad (I := I) g 1 (1 + 1) i
            (armSlotEndoCc (I := I) (M := M) g 0 A)‖ ^ 2 := by
      rw [Finset.mul_sum]

private theorem arm_h2_lip
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (A : ContMDiffSection I (E →L[ℝ] (E →L[ℝ] E)) ∞
      (fun x : M => TangentSpace I x →L[ℝ]
        (TangentSpace I x →L[ℝ] TangentSpace I x))) :
    lowJetSq (I := I) (M := M) g 2
        (armSlotEndoCc (I := I) (M := M) g s A) ≤
      (Module.finrank ℝ E : ℝ) ^ s *
        lowJetSq (I := I) (M := M) g 2
          (armSlotEndoCc (I := I) (M := M) g 0 A) := by
  unfold lowJetSq
  calc
    ∑ i ∈ Finset.range 3,
        ‖iteratedCovGrad (I := I) g (s + 1) (s + 1 + 1) i
          (armSlotEndoCc (I := I) (M := M) g s A)‖ ^ 2 ≤
      ∑ i ∈ Finset.range 3, (Module.finrank ℝ E : ℝ) ^ s *
        ‖iteratedCovGrad (I := I) g 1 (1 + 1) i
          (armSlotEndoCc (I := I) (M := M) g 0 A)‖ ^ 2 :=
      Finset.sum_le_sum fun i _ =>
        arm_l2_lip (I := I) (M := M) g s i A
    _ = (Module.finrank ℝ E : ℝ) ^ s *
        ∑ i ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g 1 (1 + 1) i
            (armSlotEndoCc (I := I) (M := M) g 0 A)‖ ^ 2 := by
      rw [Finset.mul_sum]

set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 1600000 in
private theorem armSlot_sub_lip
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (A B : ContMDiffSection I (E →L[ℝ] (E →L[ℝ] E)) ∞
      (fun x : M => TangentSpace I x →L[ℝ]
        (TangentSpace I x →L[ℝ] TangentSpace I x))) :
    armSlotEndoCc (I := I) (M := M) g s (A - B) =
      armSlotEndoCc (I := I) (M := M) g s A -
        armSlotEndoCc (I := I) (M := M) g s B := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro D
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro m
  have hRHS : (show Tensor0SSpace (s + 1) I x →L[ℝ]
        Tensor0SSpace (s + 1 + 1) I x from
        (armSlotEndoCc (I := I) (M := M) g s A -
          armSlotEndoCc (I := I) (M := M) g s B).toSection x) D =
      armSlotFib (I := I) (M := M) s x (A x) D -
        armSlotFib (I := I) (M := M) s x (B x) D := by
    rw [show ((armSlotEndoCc (I := I) (M := M) g s A -
          armSlotEndoCc (I := I) (M := M) g s B).toSection x) =
        (armSlotEndoCc (I := I) (M := M) g s A).toSection x -
          (armSlotEndoCc (I := I) (M := M) g s B).toSection x from rfl]
    rfl
  have hLHS : (show Tensor0SSpace (s + 1) I x →L[ℝ]
        Tensor0SSpace (s + 1 + 1) I x from
        (armSlotEndoCc (I := I) (M := M) g s (A - B)).toSection x) D =
      armSlotFib (I := I) (M := M) s x ((A - B) x) D := rfl
  have hfib : armSlotFib (I := I) (M := M) s x (A x - B x) D =
      armSlotFib (I := I) (M := M) s x (A x) D -
        armSlotFib (I := I) (M := M) s x (B x) D := by
    apply Tensor0SSpace.toModel_injective
    apply ContinuousMultilinearMap.ext
    intro v
    dsimp only
    rw [Tensor0SSpace.toModel_sub, ContinuousMultilinearMap.sub_apply,
      armSlotFib_apply_eval, armSlotFib_apply_eval, armSlotFib_apply_eval,
      ContinuousLinearMap.sub_apply,
      slotInsertEndoFib_sub_left (I := I) (M := M) (s + 1) 0 x
        (A x (v 0)) (B x (v 0)),
      ContinuousLinearMap.sub_apply, Tensor0SSpace.toModel_sub,
      ContinuousMultilinearMap.sub_apply]
  rw [hLHS, hRHS, show ((A - B) x) = A x - B x from rfl, hfib]


private theorem armU_bdd_h2
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ B : ℝ → ℝ,
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B R) ∧
      ∀ (gT : SmoothRiemannianMetric I M)
        (T : SmoothCcTensor g 0 2)
        (hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        (hTtie : ∀ (x : M) (u v : TangentSpace I x),
          gT.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g T x u v)
        {δ : ℝ} (hδ_le : δ ≤ 1 / 3) (hδ0 : 0 ≤ δ)
        (hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        (R A : ℝ), 0 ≤ R → 0 ≤ A →
        lowJetSq (I := I) (M := M) g 2 T ≤ R ^ 2 →
        lowJetSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
      lowJetSq (I := I) (M := M) g 2
          (armSlotEndoCc (I := I) (M := M) g 2
            (bdConnPair (I := I) (M := M) g gT)) ≤
        (((Module.finrank ℝ E : ℝ)) * B R * A) ^ 2 := by
  obtain ⟨Bs, hBs, hwSelf⟩ :=
    wXi_self_tame (I := I) (M := M) hDim g
  refine ⟨Bs, hBs, ?_⟩
  intro gT T hT hTtie δ hδ_le hδ0 hδT hδZ R A hR hA hT2 hT3
  have hbase : armSlotEndoCc (I := I) (M := M) g 0
      (bdConnPair (I := I) (M := M) g gT) =
      connDiffSection (I := I) gT g :=
    (bdConnDiffSection_eq_armSlotEndoCc_zero
      (I := I) (M := M) g gT).symm
  have hw := hwSelf gT T hT hTtie hδ_le hδ0 hδT hδZ R A hR hA hT2 hT3
  have h0 : lowJetSq (I := I) (M := M) g 2
      (armSlotEndoCc (I := I) (M := M) g 0
        (bdConnPair (I := I) (M := M) g gT)) ≤
      (Bs R * A) ^ 2 := by
    rw [hbase, connSec_self_h2 (I := I) (M := M) g gT]
    exact hw
  calc
    lowJetSq (I := I) (M := M) g 2
        (armSlotEndoCc (I := I) (M := M) g 2
          (bdConnPair (I := I) (M := M) g gT)) ≤
      (Module.finrank ℝ E : ℝ) ^ 2 *
        lowJetSq (I := I) (M := M) g 2
          (armSlotEndoCc (I := I) (M := M) g 0
            (bdConnPair (I := I) (M := M) g gT)) :=
      arm_h2_lip (I := I) (M := M) g 2
        (bdConnPair (I := I) (M := M) g gT)
    _ ≤ (Module.finrank ℝ E : ℝ) ^ 2 * (Bs R * A) ^ 2 :=
      mul_le_mul_of_nonneg_left h0
        (pow_nonneg (Nat.cast_nonneg _) 2)
    _ = (((Module.finrank ℝ E : ℝ)) * Bs R * A) ^ 2 := by ring

set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 1600000 in
private theorem armD_pair_h1
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀0 : 0 ≤ δ₀) (hδ₀ : δ₀ < 1) :
    ∃ B0 B1 : ℝ → ℝ,
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B0 R) ∧
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B1 R) ∧
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
        {δT δU : ℝ}
        (hδT_le : δT ≤ δ₀) (hδT0 : 0 ≤ δT)
        (hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δT)
        (hδU_le : δU ≤ δ₀) (hδU0 : 0 ≤ δU)
        (hδU : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g U) δU)
        (R A D2 : ℝ),
        0 ≤ R → 0 ≤ A → 0 ≤ D2 →
        lowJetSq (I := I) (M := M) g 2 U ≤ R ^ 2 →
        lowJetSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
        lowJetSq (I := I) (M := M) g 2 (T - U) ≤ D2 ^ 2 →
      lowJetSq (I := I) (M := M) g 1
          (armSlotEndoCc (I := I) (M := M) g 2
              (bdConnPair (I := I) (M := M) g gT) -
            armSlotEndoCc (I := I) (M := M) g 2
              (bdConnPair (I := I) (M := M) g gU)) ≤
        (((Module.finrank ℝ E : ℝ)) * B0 R * D2 +
          ((Module.finrank ℝ E : ℝ)) * B1 R * A * D2) ^ 2 := by
  obtain ⟨B0, B1, hB0, hB1, hpair⟩ :=
    connSec_pair_h1 (I := I) (M := M) hDim g hδ₀0 hδ₀
  refine ⟨B0, B1, hB0, hB1, ?_⟩
  intro gT gU T U hT hU hTtie hUtie
    δT δU hδT_le hδT0 hδT hδU_le hδU0 hδU
    R A D2 hR hA hD2 hU2 hT3 hTU2
  have hp := hpair gT gU T U hT hU hTtie hUtie
    hδT_le hδT0 hδT hδU_le hδU0 hδU
    R A D2 hR hA hD2 hU2 hT3 hTU2
  have hsub : armSlotEndoCc (I := I) (M := M) g 2
        (bdConnPair (I := I) (M := M) g gT) -
      armSlotEndoCc (I := I) (M := M) g 2
        (bdConnPair (I := I) (M := M) g gU) =
      armSlotEndoCc (I := I) (M := M) g 2
        (bdConnPair (I := I) (M := M) g gT -
          bdConnPair (I := I) (M := M) g gU) :=
    (armSlot_sub_lip (I := I) (M := M) g 2 _ _).symm
  have hsub0 : armSlotEndoCc (I := I) (M := M) g 0
        (bdConnPair (I := I) (M := M) g gT -
          bdConnPair (I := I) (M := M) g gU) =
      connDiffSection (I := I) gT g -
        connDiffSection (I := I) gU g := by
    rw [armSlot_sub_lip (I := I) (M := M) g 0 _ _,
      ← bdConnDiffSection_eq_armSlotEndoCc_zero
        (I := I) (M := M) g gT,
      ← bdConnDiffSection_eq_armSlotEndoCc_zero
        (I := I) (M := M) g gU]
  calc
    lowJetSq (I := I) (M := M) g 1
        (armSlotEndoCc (I := I) (M := M) g 2
            (bdConnPair (I := I) (M := M) g gT) -
          armSlotEndoCc (I := I) (M := M) g 2
            (bdConnPair (I := I) (M := M) g gU)) =
      lowJetSq (I := I) (M := M) g 1
        (armSlotEndoCc (I := I) (M := M) g 2
          (bdConnPair (I := I) (M := M) g gT -
            bdConnPair (I := I) (M := M) g gU)) := by
      rw [hsub]
    _ ≤ (Module.finrank ℝ E : ℝ) ^ 2 *
        lowJetSq (I := I) (M := M) g 1
          (armSlotEndoCc (I := I) (M := M) g 0
            (bdConnPair (I := I) (M := M) g gT -
              bdConnPair (I := I) (M := M) g gU)) :=
      arm_h1_lip (I := I) (M := M) g 2 _
    _ = (Module.finrank ℝ E : ℝ) ^ 2 *
        lowJetSq (I := I) (M := M) g 1
          (connDiffSection (I := I) gT g -
            connDiffSection (I := I) gU g) := by
      rw [hsub0]
    _ ≤ (Module.finrank ℝ E : ℝ) ^ 2 *
        (B0 R * D2 + B1 R * A * D2) ^ 2 :=
      mul_le_mul_of_nonneg_left hp
        (pow_nonneg (Nat.cast_nonneg _) 2)
    _ = (((Module.finrank ℝ E : ℝ)) * B0 R * D2 +
        ((Module.finrank ℝ E : ℝ)) * B1 R * A * D2) ^ 2 := by
      ring

set_option maxHeartbeats 1600000 in
set_option linter.unusedVariables false in
private theorem lcvPair_h2_bdd
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ B : ℝ, 0 < ρ ∧ 0 ≤ B ∧
      ∀ (T : SmoothCcTensor g 0 2)
        (gT : SmoothRiemannianMetric I M),
        (∀ (y : M) (v w : TangentSpace I y),
          gT.inner y v w =
            g.inner y v w + ccTensorBilinSymm (I := I) g T y v w) →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρ →
        lowJetSq (I := I) (M := M) g 2
            (lieCovPair (I := I) (M := M) g gT) ≤ B := by
  obtain ⟨ρb₂, B₂, hρb₂, hB₂, hb₂⟩ :=
    LowBaseInternal.trace2_h2_bdd (I := I) (M := M) hDim g
  obtain ⟨ρb₄, B₄, hρb₄, hB₄, hb₄⟩ :=
    LowBaseInternal.trace4_h2_bdd (I := I) (M := M) hDim g
  obtain ⟨Ca, hCa, happ⟩ :=
    app_h2_mul_lip (I := I) (M := M) hDim g 6 4 2
  refine ⟨min ρb₂ ρb₄, Ca * B₂ ^ 2 * B₄ ^ 2,
    lt_min hρb₂ hρb₄, by positivity, ?_⟩
  intro T gT hTtie hTn
  have hT₂ : ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρb₂ :=
    hTn.trans (min_le_left _ _)
  have hT₄ : ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρb₄ :=
    hTn.trans (min_le_right _ _)
  have hb₂T := hb₂ T gT hTtie hT₂
  have hb₄T := hb₄ T gT hTtie hT₄
  have hraw := happ
    (pureTrace (I := I) (M := M) g gT 2)
    (pureTrace (I := I) (M := M) g gT 4)
  have hj2 : 0 ≤ lowJetSq (I := I) (M := M) g 2
      (pureTrace (I := I) (M := M) g gT 2) :=
    jet_nonneg_lip (I := I) (M := M) g _
  have hj4 : 0 ≤ lowJetSq (I := I) (M := M) g 2
      (pureTrace (I := I) (M := M) g gT 4) :=
    jet_nonneg_lip (I := I) (M := M) g _
  calc
    lowJetSq (I := I) (M := M) g 2
        (lieCovPair (I := I) (M := M) g gT) =
      lowJetSq (I := I) (M := M) g 2
        (appCcRS (I := I) (M := M) g 6 4 2
          (pureTrace (I := I) (M := M) g gT 2)
          (pureTrace (I := I) (M := M) g gT 4)) := by
      rw [lcvPair_eq_lip]
    _ ≤ Ca * lowJetSq (I := I) (M := M) g 2
          (pureTrace (I := I) (M := M) g gT 2) *
        lowJetSq (I := I) (M := M) g 2
          (pureTrace (I := I) (M := M) g gT 4) := hraw
    _ ≤ Ca * B₂ ^ 2 * B₄ ^ 2 := by
      have hstep := mul_le_mul hb₂T hb₄T hj4
        (le_trans hj2 hb₂T)
      calc
        Ca * lowJetSq (I := I) (M := M) g 2
              (pureTrace (I := I) (M := M) g gT 2) *
            lowJetSq (I := I) (M := M) g 2
              (pureTrace (I := I) (M := M) g gT 4) =
          Ca * (lowJetSq (I := I) (M := M) g 2
              (pureTrace (I := I) (M := M) g gT 2) *
            lowJetSq (I := I) (M := M) g 2
              (pureTrace (I := I) (M := M) g gT 4)) := by ring
        _ ≤ Ca * (B₂ ^ 2 * B₄ ^ 2) :=
          mul_le_mul_of_nonneg_left hstep hCa
        _ = Ca * B₂ ^ 2 * B₄ ^ 2 := by ring

set_option maxHeartbeats 1600000 in
set_option linter.unusedVariables false in
/-- The reverse-raised connection product in the Lie zero-head has the
critical two-state `H²` modulus. -/
theorem lieOmega_pair_h2
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ B0 B1 : ℝ → ℝ,
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B0 R) ∧
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B1 R) ∧
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
            (0 : SmoothCcTensor g 0 2)) δ)
        (R A D2 D3 : ℝ), 0 ≤ R → 0 ≤ A → 0 ≤ D2 → 0 ≤ D3 →
        lowJetSq (I := I) (M := M) g 2 T ≤ R ^ 2 →
        lowJetSq (I := I) (M := M) g 2 U ≤ R ^ 2 →
        lowJetSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
        lowJetSq (I := I) (M := M) g 2 (T - U) ≤ D2 ^ 2 →
        lowJetSq (I := I) (M := M) g 3 (T - U) ≤ D3 ^ 2 →
      lowJetSq (I := I) (M := M) g 2
          (lipOmega (I := I) (M := M) g gT -
            lipOmega (I := I) (M := M) g gU) ≤
        (B0 R * D3 + B1 R * D2 + B1 R * A * D2) ^ 2 := by
  obtain ⟨C, hC, hpair⟩ :=
    omega_pair (I := I) (M := M) hDim g
  obtain ⟨Cr, hCr, hrevB⟩ :=
    LowBaseInternal.revSlot_bdd_h2 (I := I) (M := M) g
  obtain ⟨Bs, hBs, hwSelf⟩ :=
    wXi_self_tame (I := I) (M := M) hDim g
  obtain ⟨W0, W1, hW0, hW1, hwDiff⟩ :=
    wXi_sub_tame (I := I) (M := M) hDim g
      (δ₀ := (1 : ℝ) / 3) (by norm_num) (by norm_num)
  let Hc : ℝ := Real.sqrt C
  let fr : ℝ := Module.finrank ℝ E
  let B0 : ℝ → ℝ := fun R =>
    Hc * (Cr * (1 + R)) * W0 R
  let B1 : ℝ → ℝ := fun R =>
    Hc * (Cr * (1 + R) * W1 R + fr * Bs R)
  have hHc : 0 ≤ Hc := Real.sqrt_nonneg _
  have hHcSq : Hc ^ 2 = C := by
    simpa only [Hc] using Real.sq_sqrt hC
  have hfr : 0 ≤ fr := Nat.cast_nonneg _
  refine ⟨B0, B1, ?_, ?_, ?_⟩
  · intro R hR
    exact mul_nonneg
      (mul_nonneg hHc (mul_nonneg hCr (by linarith)))
      (hW0 R hR)
  · intro R hR
    exact mul_nonneg hHc
      (add_nonneg
        (mul_nonneg (mul_nonneg hCr (by linarith)) (hW1 R hR))
        (mul_nonneg hfr (hBs R hR)))
  intro gT gU T U hT hU hTtie hUtie
    δ hδ_le hδ0 hδT hδU hδZ
    R A D2 D3 hR hA hD2 hD3 hT2 hU2 hT3 hTU2 hTU3
  let AU : ℝ := lowJetSq (I := I) (M := M) g 2
    (slotInsertEndoCc (I := I) (M := M) g 2
      (fullRaisedEndoField (I := I) (M := M) gU g))
  let AD : ℝ := lowJetSq (I := I) (M := M) g 2
    (slotInsertEndoCc (I := I) (M := M) g 2
        (fullRaisedEndoField (I := I) (M := M) gT g) -
      slotInsertEndoCc (I := I) (M := M) g 2
        (fullRaisedEndoField (I := I) (M := M) gU g))
  let WT : ℝ := lowJetSq (I := I) (M := M) g 2
    (wXi (I := I) (M := M) g gT g)
  let WD : ℝ := lowJetSq (I := I) (M := M) g 2
    (wXi (I := I) (M := M) g gT g -
      wXi (I := I) (M := M) g gU g)
  let X : ℝ := W0 R * D3 + W1 R * D2 + W1 R * A * D2
  let P : ℝ := Cr * (1 + R)
  let Q : ℝ := fr * Bs R
  let L : ℝ := Hc * (P * X + Q * A * D2)
  let Z : ℝ := B0 R * D3 + B1 R * D2 + B1 R * A * D2
  have hAU0 : 0 ≤ AU := jet_nonneg_lip (I := I) (M := M) g _
  have hAD0 : 0 ≤ AD := jet_nonneg_lip (I := I) (M := M) g _
  have hWT0 : 0 ≤ WT := jet_nonneg_lip (I := I) (M := M) g _
  have hWD0 : 0 ≤ WD := jet_nonneg_lip (I := I) (M := M) g _
  have hW0R : 0 ≤ W0 R := hW0 R hR
  have hW1R : 0 ≤ W1 R := hW1 R hR
  have hBsR : 0 ≤ Bs R := hBs R hR
  have hP : 0 ≤ P := mul_nonneg hCr (by linarith)
  have hQ : 0 ≤ Q := mul_nonneg hfr hBsR
  have hX : 0 ≤ X := by
    exact add_nonneg
      (add_nonneg (mul_nonneg hW0R hD3) (mul_nonneg hW1R hD2))
      (mul_nonneg (mul_nonneg hW1R hA) hD2)
  have hAU :
      AU ≤ P ^ 2 := by
    simpa only [AU, P] using
      hrevB gU U hU hUtie R hR hU2
  have hAD :
      AD ≤ (fr * D2) ^ 2 := by
    have hraw :=
      LowBaseInternal.revSlot_pair_h2 (I := I) (M := M)
        g gT gU T U hT hU hTtie hUtie
    calc
      AD ≤ fr ^ 2 * lowJetSq (I := I) (M := M) g 2 (T - U) := by
        simpa only [AD, fr] using hraw
      _ ≤ fr ^ 2 * D2 ^ 2 :=
        mul_le_mul_of_nonneg_left hTU2 (sq_nonneg fr)
      _ = (fr * D2) ^ 2 := by ring
  have hWT :
      WT ≤ (Bs R * A) ^ 2 := by
    simpa only [WT] using
      hwSelf gT T hT hTtie hδ_le hδ0 hδT hδZ
        R A hR hA hT2 hT3
  have hWD :
      WD ≤ X ^ 2 := by
    simpa only [WD, X] using
      hwDiff gT gU g T U hT hU hTtie hUtie
        hδ_le hδ0 hδT hδ_le hδ0 hδU
        R A D2 D3 hR hA hD2 hD3 hU2 hT3 hTU2 hTU3
  have hPairRaw :
      lowJetSq (I := I) (M := M) g 2
          (lipOmega (I := I) (M := M) g gT -
            lipOmega (I := I) (M := M) g gU) ≤
        C * (AU * WD + AD * WT) := by
    simpa only [AU, AD, WT, WD, wXi_self_eq] using hpair gT gU
  have hFirst : AU * WD ≤ (P * X) ^ 2 := by
    calc
      AU * WD ≤ P ^ 2 * X ^ 2 :=
        mul_le_mul hAU hWD hWD0 (sq_nonneg P)
      _ = (P * X) ^ 2 := by ring
  have hSecond : AD * WT ≤ (Q * A * D2) ^ 2 := by
    calc
      AD * WT ≤ (fr * D2) ^ 2 * (Bs R * A) ^ 2 :=
        mul_le_mul hAD hWT hWT0 (sq_nonneg (fr * D2))
      _ = (Q * A * D2) ^ 2 := by
        simp only [Q]
        ring
  have hPX : 0 ≤ P * X := mul_nonneg hP hX
  have hQAD : 0 ≤ Q * A * D2 :=
    mul_nonneg (mul_nonneg hQ hA) hD2
  have hL0 : 0 ≤ L :=
    mul_nonneg hHc (add_nonneg hPX hQAD)
  have hToL :
      C * (AU * WD + AD * WT) ≤ L ^ 2 := by
    calc
      C * (AU * WD + AD * WT) ≤
          C * ((P * X) ^ 2 + (Q * A * D2) ^ 2) :=
        mul_le_mul_of_nonneg_left (add_le_add hFirst hSecond) hC
      _ ≤ C * (P * X + Q * A * D2) ^ 2 := by
        apply mul_le_mul_of_nonneg_left _ hC
        nlinarith [mul_nonneg hPX hQAD]
      _ = L ^ 2 := by
        simp only [L]
        rw [mul_pow, hHcSq]
  have hZeq : Z = L + Hc * Q * D2 := by
    simp only [Z, L, B0, B1, P, Q, X]
    ring
  have hLZ : L ≤ Z := by
    rw [hZeq]
    exact le_add_of_nonneg_right
      (mul_nonneg (mul_nonneg hHc hQ) hD2)
  calc
    lowJetSq (I := I) (M := M) g 2
        (lipOmega (I := I) (M := M) g gT -
          lipOmega (I := I) (M := M) g gU) ≤
      C * (AU * WD + AD * WT) := hPairRaw
    _ ≤ L ^ 2 := hToL
    _ ≤ Z ^ 2 := pow_le_pow_left₀ hL0 hLZ 2
    _ = (B0 R * D3 + B1 R * D2 + B1 R * A * D2) ^ 2 := rfl

set_option linter.unusedVariables false in
/-- A single reverse-raised connection product is controlled by the low
`H²` radius and the endpoint `H³` size. -/
theorem lieOmega_bdd_h2
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ B : ℝ → ℝ,
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B R) ∧
      ∀ (gT : SmoothRiemannianMetric I M)
        (T : SmoothCcTensor g 0 2)
        (hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        (hTtie : ∀ (x : M) (u v : TangentSpace I x),
          gT.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g T x u v)
        {δ : ℝ} (hδ_le : δ ≤ 1 / 3) (hδ0 : 0 ≤ δ)
        (hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        (R A : ℝ), 0 ≤ R → 0 ≤ A →
        lowJetSq (I := I) (M := M) g 2 T ≤ R ^ 2 →
        lowJetSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
      lowJetSq (I := I) (M := M) g 2
          (lipOmega (I := I) (M := M) g gT) ≤
        (B R * A) ^ 2 := by
  obtain ⟨C, hC, happ⟩ :=
    app_h2_mul_lip (I := I) (M := M) hDim g 0 3 3
  obtain ⟨Cr, hCr, hrevB⟩ :=
    LowBaseInternal.revSlot_bdd_h2 (I := I) (M := M) g
  obtain ⟨Bs, hBs, hwSelf⟩ :=
    wXi_self_tame (I := I) (M := M) hDim g
  let Hc : ℝ := Real.sqrt C
  let B : ℝ → ℝ := fun R =>
    Hc * Cr * (1 + R) * Bs R
  have hHc : 0 ≤ Hc := Real.sqrt_nonneg _
  have hHcSq : Hc ^ 2 = C := by
    simpa only [Hc] using Real.sq_sqrt hC
  refine ⟨B, ?_, ?_⟩
  · intro R hR
    exact mul_nonneg
      (mul_nonneg (mul_nonneg hHc hCr) (by linarith))
      (hBs R hR)
  intro gT T hT hTtie δ hδ_le hδ0 hδT hδZ
    R A hR hA hT2 hT3
  let RF : SmoothCcTensor g 3 3 :=
    slotInsertEndoCc (I := I) (M := M) g 2
      (fullRaisedEndoField (I := I) (M := M) gT g)
  let CD : SmoothCcTensor g 0 3 :=
    domDomCongrSection (I := I) g (finRotate 3)
      (connDiffLoweredCc (I := I) g gT)
  have hRF0 : 0 ≤ lowJetSq (I := I) (M := M) g 2 RF :=
    jet_nonneg_lip (I := I) (M := M) g RF
  have hCD0 : 0 ≤ lowJetSq (I := I) (M := M) g 2 CD :=
    jet_nonneg_lip (I := I) (M := M) g CD
  have hRF :
      lowJetSq (I := I) (M := M) g 2 RF ≤
        (Cr * (1 + R)) ^ 2 := by
    simpa only [RF] using hrevB gT T hT hTtie R hR hT2
  have hCD :
      lowJetSq (I := I) (M := M) g 2 CD ≤
        (Bs R * A) ^ 2 := by
    rw [dom_h2_lip]
    simpa only [wXi_self_eq] using
      hwSelf gT T hT hTtie hδ_le hδ0 hδT hδZ
        R A hR hA hT2 hT3
  have hraw := happ RF CD
  change lowJetSq (I := I) (M := M) g 2
      (lipOmega (I := I) (M := M) g gT) ≤
    C * lowJetSq (I := I) (M := M) g 2 RF *
      lowJetSq (I := I) (M := M) g 2 CD at hraw
  calc
    lowJetSq (I := I) (M := M) g 2
        (lipOmega (I := I) (M := M) g gT) ≤
      C * lowJetSq (I := I) (M := M) g 2 RF *
        lowJetSq (I := I) (M := M) g 2 CD := hraw
    _ ≤ C * (Cr * (1 + R)) ^ 2 *
        lowJetSq (I := I) (M := M) g 2 CD :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hRF hC) hCD0
    _ ≤ C * (Cr * (1 + R)) ^ 2 * (Bs R * A) ^ 2 :=
      mul_le_mul_of_nonneg_left hCD
        (mul_nonneg hC (sq_nonneg _))
    _ = (B R * A) ^ 2 := by
      simp only [B]
      rw [← hHcSq]
      ring

set_option linter.unusedVariables false in
/-- The complete moving-lowering correction has the critical two-state tame
estimate: the `H³` difference is multiplied only by the common `H²` radius,
whereas endpoint `H³` size multiplies only the `H²` difference. -/
private theorem hat_bdd_h2
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ B : ℝ → ℝ,
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B R) ∧
      ∀ (gT : SmoothRiemannianMetric I M)
        (T : SmoothCcTensor g 0 2)
        (hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        (hTtie : ∀ (x : M) (u v : TangentSpace I x),
          gT.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g T x u v)
        {δ : ℝ} (hδ_le : δ ≤ 1 / 3) (hδ0 : 0 ≤ δ)
        (hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        (R A : ℝ), 0 ≤ R → 0 ≤ A →
        lowJetSq (I := I) (M := M) g 2 T ≤ R ^ 2 →
        lowJetSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
      lowJetSq (I := I) (M := M) g 2
          (lrOmegaHat (I := I) (M := M) g gT) ≤
        (B R * A) ^ 2 := by
  obtain ⟨B, hB, hbdd⟩ :=
    lieOmega_bdd_h2 (I := I) (M := M) hDim g
  refine ⟨B, hB, ?_⟩
  intro gT T hT hTtie δ hδ_le hδ0 hδT hδZ R A hR hA hT2 hT3
  rw [hat_eq_lip (I := I) (M := M) g gT]
  exact hbdd gT T hT hTtie hδ_le hδ0 hδT hδZ R A hR hA hT2 hT3

private theorem curvF_zero_lip
    (g : SmoothRiemannianMetric I M) :
    lrCurvF (I := I) (M := M) g (0 : SmoothCcTensor g 0 2) = 0 := by
  rw [lrCurvF, appCcRS_zero_right, appCcRS_zero_right, add_zero]

private theorem curvF_bdd_h1
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (T : SmoothCcTensor g 0 2),
        lowJetSq (I := I) (M := M) g 1
            (lrCurvF (I := I) (M := M) g T) ≤
          C * lowJetSq (I := I) (M := M) g 2 T := by
  obtain ⟨C, hC, hpair⟩ :=
    curvF_pair_h1 (I := I) (M := M) hDim g
  refine ⟨C, hC, ?_⟩
  intro T
  have h := hpair T 0
  rw [curvF_zero_lip (I := I) (M := M) g, sub_zero, sub_zero] at h
  exact h

set_option maxHeartbeats 1600000 in
set_option linter.unusedVariables false in
private theorem quadF_bdd_h1
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ B : ℝ → ℝ,
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B R) ∧
      ∀ (gT : SmoothRiemannianMetric I M)
        (T : SmoothCcTensor g 0 2)
        (hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        (hTtie : ∀ (x : M) (u v : TangentSpace I x),
          gT.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g T x u v)
        {δ : ℝ} (hδ_le : δ ≤ 1 / 3) (hδ0 : 0 ≤ δ)
        (hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        (R A : ℝ), 0 ≤ R → 0 ≤ A →
        lowJetSq (I := I) (M := M) g 2 T ≤ R ^ 2 →
        lowJetSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
      lowJetSq (I := I) (M := M) g 1
          (lrQuadF (I := I) (M := M) g gT) ≤
        (B R * (A + A ^ 2)) ^ 2 := by
  obtain ⟨C₀, hC₀, happ⟩ :=
    app_h21_mul_lip (I := I) (M := M) hDim g 0 3 4
  obtain ⟨Ba, hBa, harm⟩ :=
    armU_bdd_h2 (I := I) (M := M) hDim g
  obtain ⟨Bh, hBh, hhat⟩ :=
    hat_bdd_h2 (I := I) (M := M) hDim g
  let fr : ℝ := (Module.finrank ℝ E : ℝ)
  have hfr : 0 ≤ fr := Nat.cast_nonneg _
  let B : ℝ → ℝ := fun R =>
    Real.sqrt (384 * C₀) * (fr * Ba R) * Bh R
  refine ⟨B, ?_, ?_⟩
  · intro R hR
    exact mul_nonneg
      (mul_nonneg (Real.sqrt_nonneg _)
        (mul_nonneg hfr (hBa R hR)))
      (hBh R hR)
  intro gT T hT hTtie δ hδ_le hδ0 hδT hδZ R A hR hA hT2 hT3
  have harmB := harm gT T hT hTtie hδ_le hδ0 hδT hδZ R A hR hA hT2 hT3
  have hhatB := hhat gT T hT hTtie hδ_le hδ0 hδT hδZ R A hR hA hT2 hT3
  set c : SmoothCcTensor g 3 4 :=
    armSlotEndoCc (I := I) (M := M) g 2
      (bdConnPair (I := I) (M := M) g gT) with hc
  set w : SmoothCcTensor g 0 3 :=
    lrOmegaHat (I := I) (M := M) g gT with hw
  have hhat1 : lowJetSq (I := I) (M := M) g 1 w ≤ (Bh R * A) ^ 2 :=
    le_trans (jet_mono_lip (I := I) (M := M) g (by norm_num) w) hhatB
  have hQBapp : lrQB (I := I) (M := M) g gT =
      appCcRS (I := I) (M := M) g 0 3 4 c w := rfl
  have hQAapp : lrQA (I := I) (M := M) g gT =
      appCcRS (I := I) (M := M) g 0 3 4 c
        (domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 3) 1) w) := rfl
  set K : ℝ := C₀ * ((fr * Ba R * A) ^ 2) * ((Bh R * A) ^ 2) with hK
  have hK0 : 0 ≤ K :=
    mul_nonneg (mul_nonneg hC₀ (sq_nonneg _)) (sq_nonneg _)
  set x : ℝ := lowJetSq (I := I) (M := M) g 1
    (lrQB (I := I) (M := M) g gT) with hxdef
  set y : ℝ := lowJetSq (I := I) (M := M) g 1
    (lrQA (I := I) (M := M) g gT) with hydef
  have hx : x ≤ K := by
    rw [hxdef, hQBapp, hK]
    calc
      lowJetSq (I := I) (M := M) g 1
          (appCcRS (I := I) (M := M) g 0 3 4 c w) ≤
        C₀ * lowJetSq (I := I) (M := M) g 2 c *
          lowJetSq (I := I) (M := M) g 1 w := happ c w
      _ ≤ C₀ * ((fr * Ba R * A) ^ 2) * ((Bh R * A) ^ 2) :=
        mul_le_mul
          (mul_le_mul_of_nonneg_left harmB hC₀)
          hhat1
          (jet_nonneg_lip (I := I) (M := M) g w)
          (mul_nonneg hC₀ (sq_nonneg _))
  have hy : y ≤ K := by
    rw [hydef, hQAapp, hK]
    have hd := dom_h1_lip (I := I) (M := M) g
      (Equiv.swap (0 : Fin 3) 1) w
    calc
      lowJetSq (I := I) (M := M) g 1
          (appCcRS (I := I) (M := M) g 0 3 4 c
            (domDomCongrSection (I := I) g
              (Equiv.swap (0 : Fin 3) 1) w)) ≤
        C₀ * lowJetSq (I := I) (M := M) g 2 c *
          lowJetSq (I := I) (M := M) g 1
            (domDomCongrSection (I := I) g
              (Equiv.swap (0 : Fin 3) 1) w) :=
        happ c _
      _ = C₀ * lowJetSq (I := I) (M := M) g 2 c *
          lowJetSq (I := I) (M := M) g 1 w := by rw [hd]
      _ ≤ C₀ * ((fr * Ba R * A) ^ 2) * ((Bh R * A) ^ 2) :=
        mul_le_mul
          (mul_le_mul_of_nonneg_left harmB hC₀)
          hhat1
          (jet_nonneg_lip (I := I) (M := M) g w)
          (mul_nonneg hC₀ (sq_nonneg _))
  have hsplit :
      lrQuadF (I := I) (M := M) g gT =
        domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 4) 1)
            (lrQB (I := I) (M := M) g gT) +
          (lrQB (I := I) (M := M) g gT +
            (domDomCongrSection (I := I) g lrPermA
                (lrQA (I := I) (M := M) g gT) +
              (domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 4) 2)
                  (lrQA (I := I) (M := M) g gT) +
                (domDomCongrSection (I := I) g lrPermB
                    (lrQA (I := I) (M := M) g gT) +
                  domDomCongrSection (I := I) g lrPermC
                    (lrQA (I := I) (M := M) g gT))))) := by
    simp only [lrQuadF]
    abel
  set QB : SmoothCcTensor g 0 4 := lrQB (I := I) (M := M) g gT with hQB
  set QA : SmoothCcTensor g 0 4 := lrQA (I := I) (M := M) g gT with hQA
  have hd1 : lowJetSq (I := I) (M := M) g 1
      (domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 4) 1) QB) =
      lowJetSq (I := I) (M := M) g 1 QB :=
    dom_h1_lip (I := I) (M := M) g _ _
  have hd3 : lowJetSq (I := I) (M := M) g 1
      (domDomCongrSection (I := I) g lrPermA QA) =
      lowJetSq (I := I) (M := M) g 1 QA :=
    dom_h1_lip (I := I) (M := M) g _ _
  have hd4 : lowJetSq (I := I) (M := M) g 1
      (domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 4) 2) QA) =
      lowJetSq (I := I) (M := M) g 1 QA :=
    dom_h1_lip (I := I) (M := M) g _ _
  have hd5 : lowJetSq (I := I) (M := M) g 1
      (domDomCongrSection (I := I) g lrPermB QA) =
      lowJetSq (I := I) (M := M) g 1 QA :=
    dom_h1_lip (I := I) (M := M) g _ _
  have hd6 : lowJetSq (I := I) (M := M) g 1
      (domDomCongrSection (I := I) g lrPermC QA) =
      lowJetSq (I := I) (M := M) g 1 QA :=
    dom_h1_lip (I := I) (M := M) g _ _
  have h56 : lowJetSq (I := I) (M := M) g 1
      (domDomCongrSection (I := I) g lrPermB QA +
        domDomCongrSection (I := I) g lrPermC QA) ≤
      2 * (lowJetSq (I := I) (M := M) g 1 QA +
        lowJetSq (I := I) (M := M) g 1 QA) := by
    linarith [jet_add_lip (I := I) (M := M) g 1
        (domDomCongrSection (I := I) g lrPermB QA)
        (domDomCongrSection (I := I) g lrPermC QA),
      hd5, hd6]
  have h456 : lowJetSq (I := I) (M := M) g 1
      (domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 4) 2) QA +
        (domDomCongrSection (I := I) g lrPermB QA +
          domDomCongrSection (I := I) g lrPermC QA)) ≤
      2 * lowJetSq (I := I) (M := M) g 1 QA +
        2 * (2 * (lowJetSq (I := I) (M := M) g 1 QA +
          lowJetSq (I := I) (M := M) g 1 QA)) := by
    linarith [jet_add_lip (I := I) (M := M) g 1
        (domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 4) 2) QA)
        (domDomCongrSection (I := I) g lrPermB QA +
          domDomCongrSection (I := I) g lrPermC QA),
      hd4, h56]
  have h3456 : lowJetSq (I := I) (M := M) g 1
      (domDomCongrSection (I := I) g lrPermA QA +
        (domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 4) 2) QA +
          (domDomCongrSection (I := I) g lrPermB QA +
            domDomCongrSection (I := I) g lrPermC QA))) ≤
      2 * lowJetSq (I := I) (M := M) g 1 QA +
        2 * (2 * lowJetSq (I := I) (M := M) g 1 QA +
          2 * (2 * (lowJetSq (I := I) (M := M) g 1 QA +
            lowJetSq (I := I) (M := M) g 1 QA))) := by
    linarith [jet_add_lip (I := I) (M := M) g 1
        (domDomCongrSection (I := I) g lrPermA QA)
        (domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 4) 2) QA +
          (domDomCongrSection (I := I) g lrPermB QA +
            domDomCongrSection (I := I) g lrPermC QA)),
      hd3, h456]
  have h23456 : lowJetSq (I := I) (M := M) g 1
      (QB +
        (domDomCongrSection (I := I) g lrPermA QA +
          (domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 4) 2) QA +
            (domDomCongrSection (I := I) g lrPermB QA +
              domDomCongrSection (I := I) g lrPermC QA)))) ≤
      2 * lowJetSq (I := I) (M := M) g 1 QB +
        2 * (2 * lowJetSq (I := I) (M := M) g 1 QA +
          2 * (2 * lowJetSq (I := I) (M := M) g 1 QA +
            2 * (2 * (lowJetSq (I := I) (M := M) g 1 QA +
              lowJetSq (I := I) (M := M) g 1 QA)))) := by
    linarith [jet_add_lip (I := I) (M := M) g 1 QB
        (domDomCongrSection (I := I) g lrPermA QA +
          (domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 4) 2) QA +
            (domDomCongrSection (I := I) g lrPermB QA +
              domDomCongrSection (I := I) g lrPermC QA))),
      h3456]
  have hlift : lowJetSq (I := I) (M := M) g 1
      (lrQuadF (I := I) (M := M) g gT) ≤
      2 * x + 2 * (2 * x + 2 * (2 * y + 2 * (2 * y +
        2 * (2 * (y + y))))) := by
    calc
      lowJetSq (I := I) (M := M) g 1
          (lrQuadF (I := I) (M := M) g gT) =
        lowJetSq (I := I) (M := M) g 1
          (domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 4) 1) QB +
            (QB +
              (domDomCongrSection (I := I) g lrPermA QA +
                (domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 4) 2) QA +
                  (domDomCongrSection (I := I) g lrPermB QA +
                    domDomCongrSection (I := I) g lrPermC QA))))) := by
        rw [← hsplit]
      _ ≤ 2 * lowJetSq (I := I) (M := M) g 1 QB +
          2 * (2 * lowJetSq (I := I) (M := M) g 1 QB +
            2 * (2 * lowJetSq (I := I) (M := M) g 1 QA +
              2 * (2 * lowJetSq (I := I) (M := M) g 1 QA +
                2 * (2 * (lowJetSq (I := I) (M := M) g 1 QA +
                  lowJetSq (I := I) (M := M) g 1 QA))))) := by
        linarith [jet_add_lip (I := I) (M := M) g 1
            (domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 4) 1) QB)
            (QB +
              (domDomCongrSection (I := I) g lrPermA QA +
                (domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 4) 2) QA +
                  (domDomCongrSection (I := I) g lrPermB QA +
                    domDomCongrSection (I := I) g lrPermC QA)))),
          hd1, h23456]
      _ = 2 * x + 2 * (2 * x + 2 * (2 * y + 2 * (2 * y +
          2 * (2 * (y + y))))) := by
        rw [hxdef, hydef]
  have hKfin : lowJetSq (I := I) (M := M) g 1
      (lrQuadF (I := I) (M := M) g gT) ≤ 384 * K := by
    nlinarith [hlift, hx, hy, hK0]
  calc
    lowJetSq (I := I) (M := M) g 1
        (lrQuadF (I := I) (M := M) g gT) ≤ 384 * K := hKfin
    _ = 384 * C₀ * (fr * Ba R) ^ 2 * (Bh R) ^ 2 * (A ^ 2 * A ^ 2) := by
      rw [hK]; ring
    _ ≤ 384 * C₀ * (fr * Ba R) ^ 2 * (Bh R) ^ 2 * (A + A ^ 2) ^ 2 := by
      have hle : A ^ 2 * A ^ 2 ≤ (A + A ^ 2) ^ 2 := by nlinarith [hA]
      exact mul_le_mul_of_nonneg_left hle
        (by positivity)
    _ = (B R * (A + A ^ 2)) ^ 2 := by
      have hsq : Real.sqrt (384 * C₀) ^ 2 = 384 * C₀ :=
        Real.sq_sqrt (by positivity)
      simp only [B]
      rw [show (Real.sqrt (384 * C₀) * (fr * Ba R) * Bh R *
            (A + A ^ 2)) ^ 2 =
          Real.sqrt (384 * C₀) ^ 2 *
            ((fr * Ba R) ^ 2 * (Bh R ^ 2 * (A + A ^ 2) ^ 2)) from by
            ring,
        hsq]
      ring

set_option maxHeartbeats 1600000 in
set_option linter.unusedVariables false in
private theorem r4_bdd_h1
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ D : ℝ → ℝ,
      (∀ R : ℝ, 0 ≤ R → 0 ≤ D R) ∧
      ∀ (T : SmoothCcTensor g 0 2)
        (hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        {δ : ℝ} (hδ_le : δ ≤ 1 / 3) (hδ0 : 0 ≤ δ)
        (hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        (R A : ℝ), 0 ≤ R → 0 ≤ A →
        lowJetSq (I := I) (M := M) g 2 T ≤ R ^ 2 →
        lowJetSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
        ∀ {s : ℝ}, s ∈ Set.Icc (0 : ℝ) 1 →
      lowJetSq (I := I) (M := M) g 1
          (lieCovR4 (I := I) (M := M) g T hδT hδZ s) ≤
        (D R * (A + A ^ 2)) ^ 2 := by
  obtain ⟨Cc, hCc, hcurv⟩ :=
    curvF_bdd_h1 (I := I) (M := M) hDim g
  obtain ⟨Bq, hBq, hquad⟩ :=
    quadF_bdd_h1 (I := I) (M := M) hDim g
  let D : ℝ → ℝ := fun R =>
    Real.sqrt (2 * Cc + 2 * (Bq R) ^ 2)
  refine ⟨D, fun R hR => Real.sqrt_nonneg _, ?_⟩
  intro T hT δ hδ_le hδ0 hδT hδZ R A hR hA hT2 hT3 s hs
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le (by norm_num)
  set gm : SmoothRiemannianMetric I M :=
    realizedFam (I := I) g T 0 hδT hδZ s with hgm
  set P : SmoothCcTensor g 0 2 := s • T with hcP
  have hs_mem : s ∈ realizedSmallSet (δ := δ) (δ' := δ) :=
    Icc_subset_realizedSmallSet hδ_lt hδ_lt hs
  have hs2 : s ^ 2 ≤ (1 : ℝ) := by
    nlinarith [hs.1, hs.2]
  have hPsymm : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g P x u v =
        ccTensorBilin (I := I) g P x v u := by
    intro x u v
    simp only [hcP, ccTensorBilin_apply, ccTensorModel_smul,
      ContinuousMultilinearMap.smul_apply, smul_eq_mul]
    apply congrArg (fun z : ℝ => s * z)
    simpa only [ccTensorBilin_apply] using hT x u v
  have hPtie : ∀ (x : M) (u v : TangentSpace I x),
      gm.inner x u v =
        g.inner x u v + ccTensorBilinSymm (I := I) g P x u v := by
    intro x u v
    simpa only [hgm, hcP, convexPerturbation, smul_zero, zero_add] using
      realizedFam_inner_of_mem
        (I := I) g T 0 hδT hδZ hs_mem x u v
  have hδP : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g P) δ := by
    intro x u v
    have hraw :=
      convexPerturbation_gFibreOpBound_abs
        (I := I) g T 0 hδT hδZ s x u v
    have heq : |1 - s| * δ + |s| * δ = δ := by
      rw [abs_of_nonneg (by linarith [hs.2] : (0 : ℝ) ≤ 1 - s),
        abs_of_nonneg hs.1]
      ring
    simpa only [hcP, convexPerturbation, smul_zero, zero_add, heq] using hraw
  have hP2 : lowJetSq (I := I) (M := M) g 2 P ≤ R ^ 2 := by
    rw [hcP, jet_smul_lip]
    exact (mul_le_of_le_one_left
      (jet_nonneg_lip (I := I) (M := M) (m := 2) g T) hs2).trans hT2
  have hP3 : lowJetSq (I := I) (M := M) g 3 P ≤ A ^ 2 := by
    rw [hcP, jet_smul_lip]
    exact (mul_le_of_le_one_left
      (jet_nonneg_lip (I := I) (M := M) (m := 3) g T) hs2).trans hT3
  have hQF := hquad gm P hPsymm hPtie hδ_le hδ0 hδP hδZ
    R A hR hA hP2 hP3
  have hCF : lowJetSq (I := I) (M := M) g 1
      (lrCurvF (I := I) (M := M) g T) ≤ Cc * A ^ 2 := by
    calc
      lowJetSq (I := I) (M := M) g 1
          (lrCurvF (I := I) (M := M) g T) ≤
        Cc * lowJetSq (I := I) (M := M) g 2 T := hcurv T
      _ ≤ Cc * lowJetSq (I := I) (M := M) g 3 T :=
        mul_le_mul_of_nonneg_left
          (jet_mono_lip (I := I) (M := M) g (by norm_num) T) hCc
      _ ≤ Cc * A ^ 2 := mul_le_mul_of_nonneg_left hT3 hCc
  have hdecomp :
      lieCovR4 (I := I) (M := M) g T hδT hδZ s =
        (-(s / 2) : ℝ) • lrCurvF (I := I) (M := M) g T +
          (-1 : ℝ) • lrQuadF (I := I) (M := M) g gm := by
    rw [hgm, lieCovR4_eq (I := I) (M := M) g T hδT hδZ s]
    module
  have hs22 : (s / 2) ^ 2 ≤ 1 := by
    nlinarith [hs.1, hs.2]
  set u : ℝ := lowJetSq (I := I) (M := M) g 1
    (lrCurvF (I := I) (M := M) g T) with hu
  set v : ℝ := lowJetSq (I := I) (M := M) g 1
    (lrQuadF (I := I) (M := M) g gm) with hv
  have hu0 : 0 ≤ u := jet_nonneg_lip (I := I) (M := M) g _
  have hv0 : 0 ≤ v := jet_nonneg_lip (I := I) (M := M) g _
  have hA2 : 0 ≤ (A + A ^ 2) ^ 2 := sq_nonneg _
  calc
    lowJetSq (I := I) (M := M) g 1
        (lieCovR4 (I := I) (M := M) g T hδT hδZ s) =
      lowJetSq (I := I) (M := M) g 1
        ((-(s / 2) : ℝ) • lrCurvF (I := I) (M := M) g T +
          (-1 : ℝ) • lrQuadF (I := I) (M := M) g gm) := by
      rw [hdecomp]
    _ ≤ 2 * (lowJetSq (I := I) (M := M) g 1
          ((-(s / 2) : ℝ) • lrCurvF (I := I) (M := M) g T) +
        lowJetSq (I := I) (M := M) g 1
          ((-1 : ℝ) • lrQuadF (I := I) (M := M) g gm)) :=
      jet_add_lip (I := I) (M := M) g 1 _ _
    _ = 2 * ((-(s / 2)) ^ 2 * u + (-1 : ℝ) ^ 2 * v) := by
      rw [jet_smul_lip, jet_smul_lip, hu, hv]
    _ ≤ 2 * (Cc * A ^ 2 + (Bq R * (A + A ^ 2)) ^ 2) := by
      have h1 : (-(s / 2)) ^ 2 * u ≤ Cc * A ^ 2 := by
        have hle : (-(s / 2)) ^ 2 * u ≤ 1 * u := by
          have hss : (-(s / 2)) ^ 2 = (s / 2) ^ 2 := by ring
          rw [hss]
          exact mul_le_mul_of_nonneg_right hs22 hu0
        rw [one_mul] at hle
        exact hle.trans (by rw [hu]; exact hCF)
      have h2 : (-1 : ℝ) ^ 2 * v ≤ (Bq R * (A + A ^ 2)) ^ 2 := by
        have hvv : ((-1 : ℝ) ^ 2 * v) = v := by ring
        rw [hvv, hv]
        exact hQF
      linarith
    _ ≤ (D R * (A + A ^ 2)) ^ 2 := by
      have hCcA : Cc * A ^ 2 ≤ Cc * (A + A ^ 2) ^ 2 := by
        have : A ^ 2 ≤ (A + A ^ 2) ^ 2 := by nlinarith [hA]
        exact mul_le_mul_of_nonneg_left this hCc
      have hsq : D R ^ 2 = 2 * Cc + 2 * (Bq R) ^ 2 := by
        simp only [D]
        exact Real.sq_sqrt (by positivity)
      have hexp : (D R * (A + A ^ 2)) ^ 2 =
          (2 * Cc + 2 * (Bq R) ^ 2) * (A + A ^ 2) ^ 2 := by
        rw [mul_pow, hsq]
      rw [hexp]
      have hBq2 : ((Bq R) * (A + A ^ 2)) ^ 2 =
          (Bq R) ^ 2 * (A + A ^ 2) ^ 2 := by ring
      nlinarith [hCcA, hA2, sq_nonneg (Bq R), sq_nonneg (A + A ^ 2)]

private theorem edgePair_eq_lip
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    {δ : ℝ}
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ)
    (s : ℝ) :
    edgeLiePairFam (I := I) (M := M) g T hδ hδZ
        lieRefoldQ lieRefoldEps s =
      deTurckLieCovDerivRefoldPairTraceFamily (I := I) (M := M)
        g T hδ hδZ
          ![Equiv.swap (0 : Fin 4) 1 * Equiv.swap (0 : Fin 4) 2,
            Equiv.swap (2 : Fin 4) 3 * Equiv.swap (1 : Fin 4) 2 *
              Equiv.swap (0 : Fin 4) 1,
            Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3]
          ![(-1 : ℝ), -1, 1] s := rfl

private theorem rsperm_sub_lip
    (g : SmoothRiemannianMetric I M) {r s : ℕ}
    (σ : Equiv.Perm (Fin s)) (A B : SmoothCcTensor g r s) :
    rsDomDomCongrSection (I := I) (M := M) g r s σ (A - B) =
      rsDomDomCongrSection (I := I) (M := M) g r s σ A -
        rsDomDomCongrSection (I := I) (M := M) g r s σ B := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  show rsDomDomCongr σ ((A - B).toSection x) =
    rsDomDomCongr σ (A.toSection x) - rsDomDomCongr σ (B.toSection x)
  rw [show (A - B).toSection x = A.toSection x - B.toSection x from rfl]
  simp only [rsDomDomCongr]
  rfl

private theorem covX_bdd_h1
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ D : ℝ → ℝ,
      (∀ R : ℝ, 0 ≤ R → 0 ≤ D R) ∧
      ∀ (T : SmoothCcTensor g 0 2)
        (hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        {δ : ℝ} (hδ_le : δ ≤ 1 / 3) (hδ0 : 0 ≤ δ)
        (hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        (R A : ℝ), 0 ≤ R → 0 ≤ A →
        lowJetSq (I := I) (M := M) g 2 T ≤ R ^ 2 →
        lowJetSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
        ∀ {s : ℝ}, s ∈ Set.Icc (0 : ℝ) 1 →
      lowJetSq (I := I) (M := M) g 1
          (rsDomDomCongrSection (I := I) (M := M) g 2 6 lieCovSigma
            (slotExtendIter (I := I) (M := M) g 0 4 2
              (lieCovR4 (I := I) (M := M) g T hδT hδZ s))) ≤
        (Module.finrank ℝ E : ℝ) ^ 2 * (D R * (A + A ^ 2)) ^ 2 := by
  obtain ⟨D, hD, hr4⟩ :=
    r4_bdd_h1 (I := I) (M := M) hDim g
  refine ⟨D, hD, ?_⟩
  intro T hT δ hδ_le hδ0 hδT hδZ R A hR hA hT2 hT3 s hs
  have hfr : (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ) :=
    Nat.cast_nonneg _
  have hIter : slotExtendIter (I := I) (M := M) g 0 4 2
      (lieCovR4 (I := I) (M := M) g T hδT hδZ s) =
      slotExtend (I := I) (M := M) g 1 5
        (slotExtend (I := I) (M := M) g 0 4
          (lieCovR4 (I := I) (M := M) g T hδT hδZ s)) := rfl
  have hbase := hr4 T hT hδ_le hδ0 hδT hδZ R A hR hA hT2 hT3 hs
  calc
    lowJetSq (I := I) (M := M) g 1
        (rsDomDomCongrSection (I := I) (M := M) g 2 6 lieCovSigma
          (slotExtendIter (I := I) (M := M) g 0 4 2
            (lieCovR4 (I := I) (M := M) g T hδT hδZ s))) =
      lowJetSq (I := I) (M := M) g 1
        (slotExtend (I := I) (M := M) g 1 5
          (slotExtend (I := I) (M := M) g 0 4
            (lieCovR4 (I := I) (M := M) g T hδT hδZ s))) := by
      rw [hIter, rsperm_h1_lip]
    _ ≤ (Module.finrank ℝ E : ℝ) *
        lowJetSq (I := I) (M := M) g 1
          (slotExtend (I := I) (M := M) g 0 4
            (lieCovR4 (I := I) (M := M) g T hδT hδZ s)) :=
      slot_h1_lip (I := I) (M := M) g 1 5 _
    _ ≤ (Module.finrank ℝ E : ℝ) *
        ((Module.finrank ℝ E : ℝ) *
          lowJetSq (I := I) (M := M) g 1
            (lieCovR4 (I := I) (M := M) g T hδT hδZ s)) :=
      mul_le_mul_of_nonneg_left
        (slot_h1_lip (I := I) (M := M) g 0 4 _) hfr
    _ ≤ (Module.finrank ℝ E : ℝ) *
        ((Module.finrank ℝ E : ℝ) * (D R * (A + A ^ 2)) ^ 2) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hbase hfr) hfr
    _ = (Module.finrank ℝ E : ℝ) ^ 2 * (D R * (A + A ^ 2)) ^ 2 := by
      ring

set_option maxHeartbeats 1600000 in
set_option linter.unusedVariables false in
private theorem covX_pair_h1
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ C : ℝ → ℝ,
      (∀ R : ℝ, 0 ≤ R → 0 ≤ C R) ∧
      ∀ (T U : SmoothCcTensor g 0 2)
        (hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        (hU : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g U x u v =
            ccTensorBilin (I := I) g U x v u)
        {δ : ℝ} (hδ_le : δ ≤ 1 / 3) (hδ0 : 0 ≤ δ)
        (hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδU : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g U) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        (R A D2 : ℝ), 0 ≤ R → 0 ≤ A → 0 ≤ D2 →
        lowJetSq (I := I) (M := M) g 2 T ≤ R ^ 2 →
        lowJetSq (I := I) (M := M) g 2 U ≤ R ^ 2 →
        lowJetSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
        lowJetSq (I := I) (M := M) g 3 U ≤ A ^ 2 →
        lowJetSq (I := I) (M := M) g 2 (T - U) ≤ D2 ^ 2 →
        ∀ {s : ℝ}, s ∈ Set.Icc (0 : ℝ) 1 →
      lowJetSq (I := I) (M := M) g 1
          (rsDomDomCongrSection (I := I) (M := M) g 2 6 lieCovSigma
              (slotExtendIter (I := I) (M := M) g 0 4 2
                (lieCovR4 (I := I) (M := M) g T hδT hδZ s)) -
            rsDomDomCongrSection (I := I) (M := M) g 2 6 lieCovSigma
              (slotExtendIter (I := I) (M := M) g 0 4 2
                (lieCovR4 (I := I) (M := M) g U hδU hδZ s))) ≤
        C R * ((1 + A + A ^ 2) ^ 4 * D2 ^ 2) := by
  obtain ⟨Cr, hCr, hr4p⟩ :=
    r4_pair_h1 (I := I) (M := M) hDim g
  obtain ⟨Ba, hBa, harmU⟩ :=
    armU_bdd_h2 (I := I) (M := M) hDim g
  obtain ⟨B0ω, B1ω, hB0ω, hB1ω, hω⟩ :=
    lieOmega_pair_h1 (I := I) (M := M) hDim g
  obtain ⟨B0c, B1c, hB0c, hB1c, harmD⟩ :=
    armD_pair_h1 (I := I) (M := M) hDim g
      (δ₀ := (1 : ℝ) / 3) (by norm_num) (by norm_num)
  obtain ⟨Bh, hBh, hhatb⟩ :=
    hat_bdd_h2 (I := I) (M := M) hDim g
  set fr : ℝ := (Module.finrank ℝ E : ℝ) with hfrdef
  have hfr : 0 ≤ fr := Nat.cast_nonneg _
  let C : ℝ → ℝ := fun R =>
    fr ^ 2 * Cr *
      (1 + (fr * Ba R) ^ 2 * (2 * (B0ω R) ^ 2 + 2 * (B1ω R) ^ 2) +
        (2 * (fr * B0c R) ^ 2 + 2 * (fr * B1c R) ^ 2) * (Bh R) ^ 2)
  refine ⟨C, ?_, ?_⟩
  · intro R hR
    have h1 : 0 ≤ (fr * Ba R) ^ 2 * (2 * (B0ω R) ^ 2 + 2 * (B1ω R) ^ 2) :=
      mul_nonneg (sq_nonneg _) (by positivity)
    have h2 : 0 ≤ (2 * (fr * B0c R) ^ 2 + 2 * (fr * B1c R) ^ 2) *
        (Bh R) ^ 2 := mul_nonneg (by positivity) (sq_nonneg _)
    have : (0 : ℝ) ≤ 1 + (fr * Ba R) ^ 2 *
        (2 * (B0ω R) ^ 2 + 2 * (B1ω R) ^ 2) +
        (2 * (fr * B0c R) ^ 2 + 2 * (fr * B1c R) ^ 2) * (Bh R) ^ 2 := by
      linarith
    exact mul_nonneg (mul_nonneg (sq_nonneg _) hCr) this
  intro T U hT hU δ hδ_le hδ0 hδT hδU hδZ
    R A D2 hR hA hD2 hT2 hU2 hT3 hU3 hTU2 s hs
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le (by norm_num)
  set gmT : SmoothRiemannianMetric I M :=
    realizedFam (I := I) g T 0 hδT hδZ s with hgmT
  set gmU : SmoothRiemannianMetric I M :=
    realizedFam (I := I) g U 0 hδU hδZ s with hgmU
  set P : SmoothCcTensor g 0 2 := s • T with hcP
  set Q : SmoothCcTensor g 0 2 := s • U with hcQ
  have hs_mem : s ∈ realizedSmallSet (δ := δ) (δ' := δ) :=
    Icc_subset_realizedSmallSet hδ_lt hδ_lt hs
  have hs2 : s ^ 2 ≤ (1 : ℝ) := by
    nlinarith [hs.1, hs.2]
  have hPsymm : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g P x u v =
        ccTensorBilin (I := I) g P x v u := by
    intro x u v
    simp only [hcP, ccTensorBilin_apply, ccTensorModel_smul,
      ContinuousMultilinearMap.smul_apply, smul_eq_mul]
    apply congrArg (fun z : ℝ => s * z)
    simpa only [ccTensorBilin_apply] using hT x u v
  have hQsymm : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g Q x u v =
        ccTensorBilin (I := I) g Q x v u := by
    intro x u v
    simp only [hcQ, ccTensorBilin_apply, ccTensorModel_smul,
      ContinuousMultilinearMap.smul_apply, smul_eq_mul]
    apply congrArg (fun z : ℝ => s * z)
    simpa only [ccTensorBilin_apply] using hU x u v
  have hPtie : ∀ (x : M) (u v : TangentSpace I x),
      gmT.inner x u v =
        g.inner x u v + ccTensorBilinSymm (I := I) g P x u v := by
    intro x u v
    simpa only [hgmT, hcP, convexPerturbation, smul_zero, zero_add] using
      realizedFam_inner_of_mem
        (I := I) g T 0 hδT hδZ hs_mem x u v
  have hQtie : ∀ (x : M) (u v : TangentSpace I x),
      gmU.inner x u v =
        g.inner x u v + ccTensorBilinSymm (I := I) g Q x u v := by
    intro x u v
    simpa only [hgmU, hcQ, convexPerturbation, smul_zero, zero_add] using
      realizedFam_inner_of_mem
        (I := I) g U 0 hδU hδZ hs_mem x u v
  have hδP : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g P) δ := by
    intro x u v
    have hraw :=
      convexPerturbation_gFibreOpBound_abs
        (I := I) g T 0 hδT hδZ s x u v
    have heq : |1 - s| * δ + |s| * δ = δ := by
      rw [abs_of_nonneg (by linarith [hs.2] : (0 : ℝ) ≤ 1 - s),
        abs_of_nonneg hs.1]
      ring
    simpa only [hcP, convexPerturbation, smul_zero, zero_add, heq] using hraw
  have hδQ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g Q) δ := by
    intro x u v
    have hraw :=
      convexPerturbation_gFibreOpBound_abs
        (I := I) g U 0 hδU hδZ s x u v
    have heq : |1 - s| * δ + |s| * δ = δ := by
      rw [abs_of_nonneg (by linarith [hs.2] : (0 : ℝ) ≤ 1 - s),
        abs_of_nonneg hs.1]
      ring
    simpa only [hcQ, convexPerturbation, smul_zero, zero_add, heq] using hraw
  have hP2 : lowJetSq (I := I) (M := M) g 2 P ≤ R ^ 2 := by
    rw [hcP, jet_smul_lip]
    exact (mul_le_of_le_one_left
      (jet_nonneg_lip (I := I) (M := M) (m := 2) g T) hs2).trans hT2
  have hQ2 : lowJetSq (I := I) (M := M) g 2 Q ≤ R ^ 2 := by
    rw [hcQ, jet_smul_lip]
    exact (mul_le_of_le_one_left
      (jet_nonneg_lip (I := I) (M := M) (m := 2) g U) hs2).trans hU2
  have hP3 : lowJetSq (I := I) (M := M) g 3 P ≤ A ^ 2 := by
    rw [hcP, jet_smul_lip]
    exact (mul_le_of_le_one_left
      (jet_nonneg_lip (I := I) (M := M) (m := 3) g T) hs2).trans hT3
  have hQ3 : lowJetSq (I := I) (M := M) g 3 Q ≤ A ^ 2 := by
    rw [hcQ, jet_smul_lip]
    exact (mul_le_of_le_one_left
      (jet_nonneg_lip (I := I) (M := M) (m := 3) g U) hs2).trans hU3
  have hPQ2 : lowJetSq (I := I) (M := M) g 2 (P - Q) ≤ D2 ^ 2 := by
    have hPQ : P - Q = s • (T - U) := by
      rw [hcP, hcQ, smul_sub]
    rw [hPQ, jet_smul_lip]
    exact (mul_le_of_le_one_left
      (jet_nonneg_lip (I := I) (M := M) (m := 2) g (T - U)) hs2).trans hTU2
  have hXsub :
      rsDomDomCongrSection (I := I) (M := M) g 2 6 lieCovSigma
          (slotExtendIter (I := I) (M := M) g 0 4 2
            (lieCovR4 (I := I) (M := M) g T hδT hδZ s)) -
        rsDomDomCongrSection (I := I) (M := M) g 2 6 lieCovSigma
          (slotExtendIter (I := I) (M := M) g 0 4 2
            (lieCovR4 (I := I) (M := M) g U hδU hδZ s)) =
      rsDomDomCongrSection (I := I) (M := M) g 2 6 lieCovSigma
        (slotExtend (I := I) (M := M) g 1 5
          (slotExtend (I := I) (M := M) g 0 4
            (lieCovR4 (I := I) (M := M) g T hδT hδZ s -
              lieCovR4 (I := I) (M := M) g U hδU hδZ s))) := by
    rw [← rsperm_sub_lip, slotExtend_sub, slotExtend_sub]
    rfl
  have hfr2 : (0 : ℝ) ≤ fr ^ 2 := sq_nonneg _
  have hXle : lowJetSq (I := I) (M := M) g 1
      (rsDomDomCongrSection (I := I) (M := M) g 2 6 lieCovSigma
          (slotExtendIter (I := I) (M := M) g 0 4 2
            (lieCovR4 (I := I) (M := M) g T hδT hδZ s)) -
        rsDomDomCongrSection (I := I) (M := M) g 2 6 lieCovSigma
          (slotExtendIter (I := I) (M := M) g 0 4 2
            (lieCovR4 (I := I) (M := M) g U hδU hδZ s))) ≤
      fr ^ 2 * lowJetSq (I := I) (M := M) g 1
        (lieCovR4 (I := I) (M := M) g T hδT hδZ s -
          lieCovR4 (I := I) (M := M) g U hδU hδZ s) := by
    rw [hXsub, rsperm_h1_lip]
    calc
      lowJetSq (I := I) (M := M) g 1
          (slotExtend (I := I) (M := M) g 1 5
            (slotExtend (I := I) (M := M) g 0 4
              (lieCovR4 (I := I) (M := M) g T hδT hδZ s -
                lieCovR4 (I := I) (M := M) g U hδU hδZ s))) ≤
        fr * lowJetSq (I := I) (M := M) g 1
          (slotExtend (I := I) (M := M) g 0 4
            (lieCovR4 (I := I) (M := M) g T hδT hδZ s -
              lieCovR4 (I := I) (M := M) g U hδU hδZ s)) :=
        slot_h1_lip (I := I) (M := M) g 1 5 _
      _ ≤ fr * (fr * lowJetSq (I := I) (M := M) g 1
          (lieCovR4 (I := I) (M := M) g T hδT hδZ s -
            lieCovR4 (I := I) (M := M) g U hδU hδZ s)) :=
        mul_le_mul_of_nonneg_left
          (slot_h1_lip (I := I) (M := M) g 0 4 _) hfr
      _ = fr ^ 2 * lowJetSq (I := I) (M := M) g 1
          (lieCovR4 (I := I) (M := M) g T hδT hδZ s -
            lieCovR4 (I := I) (M := M) g U hδU hδZ s) := by
        ring
  have hr4 := hr4p T U hδT hδU hδZ hs
  rw [← hgmT, ← hgmU] at hr4
  have hJarmQ : lowJetSq (I := I) (M := M) g 2
      (armSlotEndoCc (I := I) (M := M) g 2
        (bdConnPair (I := I) (M := M) g gmU)) ≤
      (fr * Ba R * A) ^ 2 :=
    harmU gmU Q hQsymm hQtie hδ_le hδ0 hδQ hδZ R A hR hA hQ2 hQ3
  have hJhatD : lowJetSq (I := I) (M := M) g 1
      (lrOmegaHat (I := I) (M := M) g gmT -
        lrOmegaHat (I := I) (M := M) g gmU) ≤
      (B0ω R * D2 + B1ω R * A * D2) ^ 2 := by
    rw [hat_eq_lip (I := I) (M := M) g gmT,
      hat_eq_lip (I := I) (M := M) g gmU]
    exact hω gmT gmU P Q hPsymm hQsymm hPtie hQtie
      hδ_le hδ0 hδP hδQ hδZ R A D2 hR hA hD2 hP2 hQ2 hP3 hPQ2
  have hJarmD : lowJetSq (I := I) (M := M) g 1
      (armSlotEndoCc (I := I) (M := M) g 2
          (bdConnPair (I := I) (M := M) g gmT) -
        armSlotEndoCc (I := I) (M := M) g 2
          (bdConnPair (I := I) (M := M) g gmU)) ≤
      (fr * B0c R * D2 + fr * B1c R * A * D2) ^ 2 :=
    harmD gmT gmU P Q hPsymm hQsymm hPtie hQtie
      hδ_le hδ0 hδP hδ_le hδ0 hδQ R A D2 hR hA hD2 hQ2 hP3 hPQ2
  have hJhatP : lowJetSq (I := I) (M := M) g 2
      (lrOmegaHat (I := I) (M := M) g gmT) ≤
      (Bh R * A) ^ 2 :=
    hhatb gmT P hPsymm hPtie hδ_le hδ0 hδP hδZ R A hR hA hP2 hP3
  have hp1 : lowJetSq (I := I) (M := M) g 2
        (armSlotEndoCc (I := I) (M := M) g 2
          (bdConnPair (I := I) (M := M) g gmU)) *
      lowJetSq (I := I) (M := M) g 1
        (lrOmegaHat (I := I) (M := M) g gmT -
          lrOmegaHat (I := I) (M := M) g gmU) ≤
      (fr * Ba R * A) ^ 2 * (B0ω R * D2 + B1ω R * A * D2) ^ 2 :=
    mul_le_mul hJarmQ hJhatD
      (jet_nonneg_lip (I := I) (M := M) (m := 1) g _)
      (sq_nonneg _)
  have hp2 : lowJetSq (I := I) (M := M) g 1
        (armSlotEndoCc (I := I) (M := M) g 2
            (bdConnPair (I := I) (M := M) g gmT) -
          armSlotEndoCc (I := I) (M := M) g 2
            (bdConnPair (I := I) (M := M) g gmU)) *
      lowJetSq (I := I) (M := M) g 2
        (lrOmegaHat (I := I) (M := M) g gmT) ≤
      (fr * B0c R * D2 + fr * B1c R * A * D2) ^ 2 * (Bh R * A) ^ 2 :=
    mul_le_mul hJarmD hJhatP
      (jet_nonneg_lip (I := I) (M := M) (m := 2) g _)
      (sq_nonneg _)
  have hr4le : lowJetSq (I := I) (M := M) g 1
      (lieCovR4 (I := I) (M := M) g T hδT hδZ s -
        lieCovR4 (I := I) (M := M) g U hδU hδZ s) ≤
      Cr * (D2 ^ 2 +
        ((fr * Ba R * A) ^ 2 * (B0ω R * D2 + B1ω R * A * D2) ^ 2 +
          (fr * B0c R * D2 + fr * B1c R * A * D2) ^ 2 *
            (Bh R * A) ^ 2)) := by
    refine hr4.trans (mul_le_mul_of_nonneg_left ?_ hCr)
    linarith [hTU2, hp1, hp2]
  have hb1 : (1 : ℝ) ≤ 1 + A + A ^ 2 := by
    nlinarith [hA, sq_nonneg A]
  have hb24 : (1 + A + A ^ 2) ^ 2 ≤ (1 + A + A ^ 2) ^ 4 :=
    pow_le_pow_right₀ hb1 (by norm_num)
  have hbA2 : A ^ 2 ≤ (1 + A + A ^ 2) ^ 2 := by
    nlinarith [hA, sq_nonneg A, mul_nonneg hA hA,
      mul_nonneg (mul_nonneg hA hA) hA]
  set pl : ℝ := (1 + A + A ^ 2) ^ 4 with hpl
  have hpl1 : (1 : ℝ) ≤ pl := by
    rw [hpl]
    calc (1 : ℝ) = 1 ^ 4 := by norm_num
      _ ≤ (1 + A + A ^ 2) ^ 4 :=
        pow_le_pow_left₀ zero_le_one hb1 4
  have hplA2 : A ^ 2 ≤ pl := by
    rw [hpl]
    exact hbA2.trans hb24
  have hplA4 : A ^ 4 ≤ pl := by
    rw [hpl]
    calc A ^ 4 = (A ^ 2) ^ 2 := by ring
      _ ≤ ((1 + A + A ^ 2) ^ 2) ^ 2 :=
        pow_le_pow_left₀ (sq_nonneg A) hbA2 2
      _ = (1 + A + A ^ 2) ^ 4 := by ring
  have hpl0 : 0 ≤ pl := le_trans zero_le_one hpl1
  have hq1 : (B0ω R * D2 + B1ω R * A * D2) ^ 2 ≤
      (2 * (B0ω R) ^ 2 + 2 * (B1ω R) ^ 2 * A ^ 2) * D2 ^ 2 := by
    nlinarith [sq_nonneg (B0ω R * D2 - B1ω R * A * D2)]
  have hq2 : (fr * B0c R * D2 + fr * B1c R * A * D2) ^ 2 ≤
      (2 * (fr * B0c R) ^ 2 + 2 * (fr * B1c R) ^ 2 * A ^ 2) *
        D2 ^ 2 := by
    nlinarith [sq_nonneg (fr * B0c R * D2 - fr * B1c R * A * D2)]
  have hD22 : 0 ≤ D2 ^ 2 := sq_nonneg _
  have hterm1 : (fr * Ba R * A) ^ 2 *
      (B0ω R * D2 + B1ω R * A * D2) ^ 2 ≤
      (fr * Ba R) ^ 2 * (2 * (B0ω R) ^ 2 + 2 * (B1ω R) ^ 2) *
        (pl * D2 ^ 2) := by
    have h1 : (fr * Ba R * A) ^ 2 *
        (B0ω R * D2 + B1ω R * A * D2) ^ 2 ≤
        (fr * Ba R * A) ^ 2 *
          ((2 * (B0ω R) ^ 2 + 2 * (B1ω R) ^ 2 * A ^ 2) * D2 ^ 2) :=
      mul_le_mul_of_nonneg_left hq1 (sq_nonneg _)
    have h2 : (fr * Ba R * A) ^ 2 *
        ((2 * (B0ω R) ^ 2 + 2 * (B1ω R) ^ 2 * A ^ 2) * D2 ^ 2) =
        (fr * Ba R) ^ 2 *
          (2 * (B0ω R) ^ 2 * A ^ 2 + 2 * (B1ω R) ^ 2 * A ^ 4) *
            D2 ^ 2 := by ring
    have h3 : (fr * Ba R) ^ 2 *
        (2 * (B0ω R) ^ 2 * A ^ 2 + 2 * (B1ω R) ^ 2 * A ^ 4) *
          D2 ^ 2 ≤
        (fr * Ba R) ^ 2 *
          (2 * (B0ω R) ^ 2 * pl + 2 * (B1ω R) ^ 2 * pl) * D2 ^ 2 := by
      have hin : 2 * (B0ω R) ^ 2 * A ^ 2 + 2 * (B1ω R) ^ 2 * A ^ 4 ≤
          2 * (B0ω R) ^ 2 * pl + 2 * (B1ω R) ^ 2 * pl := by
        have i1 : 2 * (B0ω R) ^ 2 * A ^ 2 ≤ 2 * (B0ω R) ^ 2 * pl :=
          mul_le_mul_of_nonneg_left hplA2 (by positivity)
        have i2 : 2 * (B1ω R) ^ 2 * A ^ 4 ≤ 2 * (B1ω R) ^ 2 * pl :=
          mul_le_mul_of_nonneg_left hplA4 (by positivity)
        linarith
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hin (sq_nonneg _)) hD22
    calc (fr * Ba R * A) ^ 2 *
        (B0ω R * D2 + B1ω R * A * D2) ^ 2 ≤
        (fr * Ba R * A) ^ 2 *
          ((2 * (B0ω R) ^ 2 + 2 * (B1ω R) ^ 2 * A ^ 2) * D2 ^ 2) := h1
      _ = (fr * Ba R) ^ 2 *
          (2 * (B0ω R) ^ 2 * A ^ 2 + 2 * (B1ω R) ^ 2 * A ^ 4) *
            D2 ^ 2 := h2
      _ ≤ (fr * Ba R) ^ 2 *
          (2 * (B0ω R) ^ 2 * pl + 2 * (B1ω R) ^ 2 * pl) * D2 ^ 2 := h3
      _ = (fr * Ba R) ^ 2 * (2 * (B0ω R) ^ 2 + 2 * (B1ω R) ^ 2) *
          (pl * D2 ^ 2) := by ring
  have hterm2 : (fr * B0c R * D2 + fr * B1c R * A * D2) ^ 2 *
      (Bh R * A) ^ 2 ≤
      (2 * (fr * B0c R) ^ 2 + 2 * (fr * B1c R) ^ 2) * (Bh R) ^ 2 *
        (pl * D2 ^ 2) := by
    have h1 : (fr * B0c R * D2 + fr * B1c R * A * D2) ^ 2 *
        (Bh R * A) ^ 2 ≤
        ((2 * (fr * B0c R) ^ 2 + 2 * (fr * B1c R) ^ 2 * A ^ 2) *
          D2 ^ 2) * (Bh R * A) ^ 2 :=
      mul_le_mul_of_nonneg_right hq2 (sq_nonneg _)
    have h2 : ((2 * (fr * B0c R) ^ 2 + 2 * (fr * B1c R) ^ 2 * A ^ 2) *
        D2 ^ 2) * (Bh R * A) ^ 2 =
        (2 * (fr * B0c R) ^ 2 * A ^ 2 +
          2 * (fr * B1c R) ^ 2 * A ^ 4) * (Bh R) ^ 2 * D2 ^ 2 := by
      ring
    have h3 : (2 * (fr * B0c R) ^ 2 * A ^ 2 +
        2 * (fr * B1c R) ^ 2 * A ^ 4) * (Bh R) ^ 2 * D2 ^ 2 ≤
        (2 * (fr * B0c R) ^ 2 * pl + 2 * (fr * B1c R) ^ 2 * pl) *
          (Bh R) ^ 2 * D2 ^ 2 := by
      have hin : 2 * (fr * B0c R) ^ 2 * A ^ 2 +
          2 * (fr * B1c R) ^ 2 * A ^ 4 ≤
          2 * (fr * B0c R) ^ 2 * pl + 2 * (fr * B1c R) ^ 2 * pl := by
        have i1 : 2 * (fr * B0c R) ^ 2 * A ^ 2 ≤
            2 * (fr * B0c R) ^ 2 * pl :=
          mul_le_mul_of_nonneg_left hplA2 (by positivity)
        have i2 : 2 * (fr * B1c R) ^ 2 * A ^ 4 ≤
            2 * (fr * B1c R) ^ 2 * pl :=
          mul_le_mul_of_nonneg_left hplA4 (by positivity)
        linarith
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hin (sq_nonneg _)) hD22
    calc (fr * B0c R * D2 + fr * B1c R * A * D2) ^ 2 *
        (Bh R * A) ^ 2 ≤
        ((2 * (fr * B0c R) ^ 2 + 2 * (fr * B1c R) ^ 2 * A ^ 2) *
          D2 ^ 2) * (Bh R * A) ^ 2 := h1
      _ = (2 * (fr * B0c R) ^ 2 * A ^ 2 +
          2 * (fr * B1c R) ^ 2 * A ^ 4) * (Bh R) ^ 2 * D2 ^ 2 := h2
      _ ≤ (2 * (fr * B0c R) ^ 2 * pl + 2 * (fr * B1c R) ^ 2 * pl) *
          (Bh R) ^ 2 * D2 ^ 2 := h3
      _ = (2 * (fr * B0c R) ^ 2 + 2 * (fr * B1c R) ^ 2) * (Bh R) ^ 2 *
          (pl * D2 ^ 2) := by ring
  have hD2pl : D2 ^ 2 ≤ pl * D2 ^ 2 := by
    nlinarith [hpl1, hD22]
  calc
    lowJetSq (I := I) (M := M) g 1
        (rsDomDomCongrSection (I := I) (M := M) g 2 6 lieCovSigma
            (slotExtendIter (I := I) (M := M) g 0 4 2
              (lieCovR4 (I := I) (M := M) g T hδT hδZ s)) -
          rsDomDomCongrSection (I := I) (M := M) g 2 6 lieCovSigma
            (slotExtendIter (I := I) (M := M) g 0 4 2
              (lieCovR4 (I := I) (M := M) g U hδU hδZ s))) ≤
      fr ^ 2 * lowJetSq (I := I) (M := M) g 1
        (lieCovR4 (I := I) (M := M) g T hδT hδZ s -
          lieCovR4 (I := I) (M := M) g U hδU hδZ s) := hXle
    _ ≤ fr ^ 2 * (Cr * (D2 ^ 2 +
        ((fr * Ba R * A) ^ 2 * (B0ω R * D2 + B1ω R * A * D2) ^ 2 +
          (fr * B0c R * D2 + fr * B1c R * A * D2) ^ 2 *
            (Bh R) ^ 2 * A ^ 2))) := by
      refine mul_le_mul_of_nonneg_left ?_ hfr2
      refine hr4le.trans (le_of_eq ?_)
      ring
    _ ≤ fr ^ 2 * (Cr *
        ((1 + (fr * Ba R) ^ 2 * (2 * (B0ω R) ^ 2 + 2 * (B1ω R) ^ 2) +
          (2 * (fr * B0c R) ^ 2 + 2 * (fr * B1c R) ^ 2) * (Bh R) ^ 2) *
            (pl * D2 ^ 2))) := by
      refine mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left ?_ hCr) hfr2
      have hterm2' : (fr * B0c R * D2 + fr * B1c R * A * D2) ^ 2 *
          (Bh R) ^ 2 * A ^ 2 ≤
          (2 * (fr * B0c R) ^ 2 + 2 * (fr * B1c R) ^ 2) * (Bh R) ^ 2 *
            (pl * D2 ^ 2) := by
        have heq : (fr * B0c R * D2 + fr * B1c R * A * D2) ^ 2 *
            (Bh R) ^ 2 * A ^ 2 =
            (fr * B0c R * D2 + fr * B1c R * A * D2) ^ 2 *
              (Bh R * A) ^ 2 := by ring
        rw [heq]
        exact hterm2
      have hsum : D2 ^ 2 +
          ((fr * Ba R * A) ^ 2 * (B0ω R * D2 + B1ω R * A * D2) ^ 2 +
            (fr * B0c R * D2 + fr * B1c R * A * D2) ^ 2 *
              (Bh R) ^ 2 * A ^ 2) ≤
          pl * D2 ^ 2 +
            ((fr * Ba R) ^ 2 * (2 * (B0ω R) ^ 2 + 2 * (B1ω R) ^ 2) *
                (pl * D2 ^ 2) +
              (2 * (fr * B0c R) ^ 2 + 2 * (fr * B1c R) ^ 2) *
                (Bh R) ^ 2 * (pl * D2 ^ 2)) := by
        linarith [hterm1, hterm2', hD2pl]
      refine hsum.trans (le_of_eq ?_)
      ring
    _ = C R * ((1 + A + A ^ 2) ^ 4 * D2 ^ 2) := by
      simp only [C, hpl]
      ring

set_option maxHeartbeats 1600000 in
set_option linter.unusedVariables false in
private theorem lieCov_pair_h1
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ : ℝ, ∃ B : ℝ → ℝ,
      0 < ρ ∧ (∀ R : ℝ, 0 ≤ R → 0 ≤ B R) ∧
      ∀ (T U : SmoothCcTensor g 0 2)
        (hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        (hU : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g U x u v =
            ccTensorBilin (I := I) g U x v u)
        {δ : ℝ} (hδ_le : δ ≤ 1 / 3) (hδ0 : 0 ≤ δ)
        (hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδU : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g U) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        (R A D2 N : ℝ), 0 ≤ R → 0 ≤ A → 0 ≤ D2 → 0 ≤ N →
        lowJetSq (I := I) (M := M) g 2 T ≤ R ^ 2 →
        lowJetSq (I := I) (M := M) g 2 U ≤ R ^ 2 →
        lowJetSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
        lowJetSq (I := I) (M := M) g 3 U ≤ A ^ 2 →
        lowJetSq (I := I) (M := M) g 2 (T - U) ≤ D2 ^ 2 →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U)‖ ≤ N →
        ∀ {s : ℝ}, s ∈ Set.Icc (0 : ℝ) 1 →
      lowJetSq (I := I) (M := M) g 1
          ((deTurckLieCovDerivArmField (I := I) (M := M) g
              (realizedFam (I := I) g T 0 hδT hδZ s) g -
            edgeLiePairFam (I := I) (M := M) g T hδT hδZ
              lieRefoldQ lieRefoldEps s) -
          (deTurckLieCovDerivArmField (I := I) (M := M) g
              (realizedFam (I := I) g U 0 hδU hδZ s) g -
            edgeLiePairFam (I := I) (M := M) g U hδU hδZ
              lieRefoldQ lieRefoldEps s)) ≤
        B R * ((1 + A + A ^ 2) ^ 4 * (D2 ^ 2 + N ^ 2)) := by
  obtain ⟨C₂, hC₂, happ⟩ :=
    app_h21_mul_lip (I := I) (M := M) hDim g 2 6 2
  obtain ⟨ρp, Cp, hρp, hCp, hlcvp⟩ :=
    lcvPair_pair_h2 (I := I) (M := M) hDim g
  obtain ⟨ρb, Bp, hρb, hBp, hlcvb⟩ :=
    lcvPair_h2_bdd (I := I) (M := M) hDim g
  obtain ⟨Dr, hDr, hcovb⟩ :=
    covX_bdd_h1 (I := I) (M := M) hDim g
  obtain ⟨Cx, hCx, hcovp⟩ :=
    covX_pair_h1 (I := I) (M := M) hDim g
  set fr : ℝ := (Module.finrank ℝ E : ℝ) with hfrdef
  have hfr : 0 ≤ fr := Nat.cast_nonneg _
  let B : ℝ → ℝ := fun R =>
    2 * (C₂ * Cp ^ 2 * (fr ^ 2 * (Dr R) ^ 2) + C₂ * Bp * Cx R)
  refine ⟨min ρp ρb, B, lt_min hρp hρb, ?_, ?_⟩
  · intro R hR
    have h1 : 0 ≤ C₂ * Cp ^ 2 * (fr ^ 2 * (Dr R) ^ 2) := by positivity
    have h2 : 0 ≤ C₂ * Bp * Cx R :=
      mul_nonneg (mul_nonneg hC₂ hBp) (hCx R hR)
    linarith
  intro T U hT hU δ hδ_le hδ0 hδT hδU hδZ
    R A D2 N hR hA hD2 hN hT2 hU2 hT3 hU3 hTU2 hTn hUn hTUn s hs
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le (by norm_num)
  set gmT : SmoothRiemannianMetric I M :=
    realizedFam (I := I) g T 0 hδT hδZ s with hgmT
  set gmU : SmoothRiemannianMetric I M :=
    realizedFam (I := I) g U 0 hδU hδZ s with hgmU
  set P : SmoothCcTensor g 0 2 := s • T with hcP
  set Q : SmoothCcTensor g 0 2 := s • U with hcQ
  have hs_mem : s ∈ realizedSmallSet (δ := δ) (δ' := δ) :=
    Icc_subset_realizedSmallSet hδ_lt hδ_lt hs
  have hsabs : ‖s‖ ≤ (1 : ℝ) := by
    rw [Real.norm_eq_abs, abs_of_nonneg hs.1]
    exact hs.2
  have hPtie : ∀ (x : M) (u v : TangentSpace I x),
      gmT.inner x u v =
        g.inner x u v + ccTensorBilinSymm (I := I) g P x u v := by
    intro x u v
    simpa only [hgmT, hcP, convexPerturbation, smul_zero, zero_add] using
      realizedFam_inner_of_mem
        (I := I) g T 0 hδT hδZ hs_mem x u v
  have hQtie : ∀ (x : M) (u v : TangentSpace I x),
      gmU.inner x u v =
        g.inner x u v + ccTensorBilinSymm (I := I) g Q x u v := by
    intro x u v
    simpa only [hgmU, hcQ, convexPerturbation, smul_zero, zero_add] using
      realizedFam_inner_of_mem
        (I := I) g U 0 hδU hδZ hs_mem x u v
  have hPn : ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) P‖ ≤ ρp := by
    rw [hcP, ccTensorToHs_smul, norm_smul]
    exact (mul_le_mul_of_nonneg_right hsabs (norm_nonneg _)).trans
      (by simpa using hTn.trans (min_le_left _ _))
  have hQn : ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) Q‖ ≤ ρp := by
    rw [hcQ, ccTensorToHs_smul, norm_smul]
    exact (mul_le_mul_of_nonneg_right hsabs (norm_nonneg _)).trans
      (by simpa using hUn.trans (min_le_left _ _))
  have hQnb : ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) Q‖ ≤ ρb := by
    rw [hcQ, ccTensorToHs_smul, norm_smul]
    exact (mul_le_mul_of_nonneg_right hsabs (norm_nonneg _)).trans
      (by simpa using hUn.trans (min_le_right _ _))
  have hPQn : ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (P - Q)‖ ≤
      N := by
    have hPQ : P - Q = s • (T - U) := by
      rw [hcP, hcQ, smul_sub]
    rw [hPQ, ccTensorToHs_smul, norm_smul]
    exact (mul_le_mul_of_nonneg_right hsabs (norm_nonneg _)).trans
      (by simpa using hTUn)
  have hUT :
      deTurckLieCovDerivArmField (I := I) (M := M) g gmT g -
        deTurckLieCovDerivRefoldPairTraceFamily (I := I) (M := M)
          g T hδT hδZ
            ![Equiv.swap (0 : Fin 4) 1 * Equiv.swap (0 : Fin 4) 2,
              Equiv.swap (2 : Fin 4) 3 * Equiv.swap (1 : Fin 4) 2 *
                Equiv.swap (0 : Fin 4) 1,
              Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3]
            ![(-1 : ℝ), -1, 1] s =
      (-1 : ℝ) • appCcRS (I := I) (M := M) g 2 6 2
        (lieCovPair (I := I) (M := M) g gmT)
        (rsDomDomCongrSection (I := I) (M := M) g 2 6 lieCovSigma
          (slotExtendIter (I := I) (M := M) g 0 4 2
            (lieCovR4 (I := I) (M := M) g T hδT hδZ s))) := by
    rw [hgmT]
    exact lieCov_residual (I := I) (M := M) g T hδ_lt hδT hδZ hT hs
  have hUU :
      deTurckLieCovDerivArmField (I := I) (M := M) g gmU g -
        deTurckLieCovDerivRefoldPairTraceFamily (I := I) (M := M)
          g U hδU hδZ
            ![Equiv.swap (0 : Fin 4) 1 * Equiv.swap (0 : Fin 4) 2,
              Equiv.swap (2 : Fin 4) 3 * Equiv.swap (1 : Fin 4) 2 *
                Equiv.swap (0 : Fin 4) 1,
              Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3]
            ![(-1 : ℝ), -1, 1] s =
      (-1 : ℝ) • appCcRS (I := I) (M := M) g 2 6 2
        (lieCovPair (I := I) (M := M) g gmU)
        (rsDomDomCongrSection (I := I) (M := M) g 2 6 lieCovSigma
          (slotExtendIter (I := I) (M := M) g 0 4 2
            (lieCovR4 (I := I) (M := M) g U hδU hδZ s))) := by
    rw [hgmU]
    exact lieCov_residual (I := I) (M := M) g U hδ_lt hδU hδZ hU hs
  rw [edgePair_eq_lip (I := I) (M := M) g T hδT hδZ s,
    edgePair_eq_lip (I := I) (M := M) g U hδU hδZ s, hUT, hUU]
  have htel :
      (-1 : ℝ) • appCcRS (I := I) (M := M) g 2 6 2
          (lieCovPair (I := I) (M := M) g gmT)
          (rsDomDomCongrSection (I := I) (M := M) g 2 6 lieCovSigma
            (slotExtendIter (I := I) (M := M) g 0 4 2
              (lieCovR4 (I := I) (M := M) g T hδT hδZ s))) -
        (-1 : ℝ) • appCcRS (I := I) (M := M) g 2 6 2
          (lieCovPair (I := I) (M := M) g gmU)
          (rsDomDomCongrSection (I := I) (M := M) g 2 6 lieCovSigma
            (slotExtendIter (I := I) (M := M) g 0 4 2
              (lieCovR4 (I := I) (M := M) g U hδU hδZ s))) =
      (-1 : ℝ) • (appCcRS (I := I) (M := M) g 2 6 2
          (lieCovPair (I := I) (M := M) g gmT -
            lieCovPair (I := I) (M := M) g gmU)
          (rsDomDomCongrSection (I := I) (M := M) g 2 6 lieCovSigma
            (slotExtendIter (I := I) (M := M) g 0 4 2
              (lieCovR4 (I := I) (M := M) g T hδT hδZ s))) +
        appCcRS (I := I) (M := M) g 2 6 2
          (lieCovPair (I := I) (M := M) g gmU)
          (rsDomDomCongrSection (I := I) (M := M) g 2 6 lieCovSigma
              (slotExtendIter (I := I) (M := M) g 0 4 2
                (lieCovR4 (I := I) (M := M) g T hδT hδZ s)) -
            rsDomDomCongrSection (I := I) (M := M) g 2 6 lieCovSigma
              (slotExtendIter (I := I) (M := M) g 0 4 2
                (lieCovR4 (I := I) (M := M) g U hδU hδZ s)))) := by
    rw [appCcRS_sub_left, appCcRS_sub_right]
    module
  rw [htel, jet_smul_lip]
  rw [neg_one_sq, one_mul]
  have hPairD : lowJetSq (I := I) (M := M) g 2
      (lieCovPair (I := I) (M := M) g gmT -
        lieCovPair (I := I) (M := M) g gmU) ≤ (Cp * N) ^ 2 := by
    refine (hlcvp P Q gmT gmU hPtie hQtie hPn hQn).trans ?_
    have h1 : Cp * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
        (P - Q)‖ ≤ Cp * N :=
      mul_le_mul_of_nonneg_left hPQn hCp
    exact pow_le_pow_left₀
      (mul_nonneg hCp (norm_nonneg _)) h1 2
  have hPairU : lowJetSq (I := I) (M := M) g 2
      (lieCovPair (I := I) (M := M) g gmU) ≤ Bp :=
    hlcvb Q gmU hQtie hQnb
  have hXT : lowJetSq (I := I) (M := M) g 1
      (rsDomDomCongrSection (I := I) (M := M) g 2 6 lieCovSigma
        (slotExtendIter (I := I) (M := M) g 0 4 2
          (lieCovR4 (I := I) (M := M) g T hδT hδZ s))) ≤
      fr ^ 2 * (Dr R * (A + A ^ 2)) ^ 2 :=
    hcovb T hT hδ_le hδ0 hδT hδZ R A hR hA hT2 hT3 hs
  have hXD : lowJetSq (I := I) (M := M) g 1
      (rsDomDomCongrSection (I := I) (M := M) g 2 6 lieCovSigma
          (slotExtendIter (I := I) (M := M) g 0 4 2
            (lieCovR4 (I := I) (M := M) g T hδT hδZ s)) -
        rsDomDomCongrSection (I := I) (M := M) g 2 6 lieCovSigma
          (slotExtendIter (I := I) (M := M) g 0 4 2
            (lieCovR4 (I := I) (M := M) g U hδU hδZ s))) ≤
      Cx R * ((1 + A + A ^ 2) ^ 4 * D2 ^ 2) :=
    hcovp T U hT hU hδ_le hδ0 hδT hδU hδZ
      R A D2 hR hA hD2 hT2 hU2 hT3 hU3 hTU2 hs
  have happ1 := happ
    (lieCovPair (I := I) (M := M) g gmT -
      lieCovPair (I := I) (M := M) g gmU)
    (rsDomDomCongrSection (I := I) (M := M) g 2 6 lieCovSigma
      (slotExtendIter (I := I) (M := M) g 0 4 2
        (lieCovR4 (I := I) (M := M) g T hδT hδZ s)))
  have happ2 := happ
    (lieCovPair (I := I) (M := M) g gmU)
    (rsDomDomCongrSection (I := I) (M := M) g 2 6 lieCovSigma
        (slotExtendIter (I := I) (M := M) g 0 4 2
          (lieCovR4 (I := I) (M := M) g T hδT hδZ s)) -
      rsDomDomCongrSection (I := I) (M := M) g 2 6 lieCovSigma
        (slotExtendIter (I := I) (M := M) g 0 4 2
          (lieCovR4 (I := I) (M := M) g U hδU hδZ s)))
  have hb1 : (1 : ℝ) ≤ 1 + A + A ^ 2 := by
    nlinarith [hA, sq_nonneg A]
  have hbAA : (A + A ^ 2) ^ 2 ≤ (1 + A + A ^ 2) ^ 4 := by
    have h1 : A + A ^ 2 ≤ (1 + A + A ^ 2) ^ 2 := by
      nlinarith [hA, sq_nonneg A, mul_nonneg hA hA,
        mul_nonneg (mul_nonneg hA hA) hA]
    have h0 : (0 : ℝ) ≤ A + A ^ 2 := by positivity
    calc (A + A ^ 2) ^ 2 ≤ ((1 + A + A ^ 2) ^ 2) ^ 2 :=
        pow_le_pow_left₀ h0 h1 2
      _ = (1 + A + A ^ 2) ^ 4 := by ring
  have hpl0 : (0 : ℝ) ≤ (1 + A + A ^ 2) ^ 4 := by positivity
  have hT1 : lowJetSq (I := I) (M := M) g 1
      (appCcRS (I := I) (M := M) g 2 6 2
        (lieCovPair (I := I) (M := M) g gmT -
          lieCovPair (I := I) (M := M) g gmU)
        (rsDomDomCongrSection (I := I) (M := M) g 2 6 lieCovSigma
          (slotExtendIter (I := I) (M := M) g 0 4 2
            (lieCovR4 (I := I) (M := M) g T hδT hδZ s)))) ≤
      C₂ * Cp ^ 2 * (fr ^ 2 * (Dr R) ^ 2) *
        ((1 + A + A ^ 2) ^ 4 * N ^ 2) := by
    refine happ1.trans ?_
    have hstep : C₂ * lowJetSq (I := I) (M := M) g 2
        (lieCovPair (I := I) (M := M) g gmT -
          lieCovPair (I := I) (M := M) g gmU) *
        lowJetSq (I := I) (M := M) g 1
          (rsDomDomCongrSection (I := I) (M := M) g 2 6 lieCovSigma
            (slotExtendIter (I := I) (M := M) g 0 4 2
              (lieCovR4 (I := I) (M := M) g T hδT hδZ s))) ≤
        C₂ * (Cp * N) ^ 2 * (fr ^ 2 * (Dr R * (A + A ^ 2)) ^ 2) := by
      refine mul_le_mul ?_ hXT
        (jet_nonneg_lip (I := I) (M := M) (m := 1) g _) ?_
      · exact mul_le_mul_of_nonneg_left hPairD hC₂
      · exact mul_nonneg hC₂ (sq_nonneg _)
    refine hstep.trans ?_
    have hAA : (Dr R * (A + A ^ 2)) ^ 2 =
        (Dr R) ^ 2 * (A + A ^ 2) ^ 2 := by ring
    have hmono : (Dr R) ^ 2 * (A + A ^ 2) ^ 2 ≤
        (Dr R) ^ 2 * (1 + A + A ^ 2) ^ 4 :=
      mul_le_mul_of_nonneg_left hbAA (sq_nonneg _)
    calc C₂ * (Cp * N) ^ 2 * (fr ^ 2 * (Dr R * (A + A ^ 2)) ^ 2) =
        C₂ * Cp ^ 2 * (fr ^ 2 * ((Dr R) ^ 2 * (A + A ^ 2) ^ 2)) *
          N ^ 2 := by ring
      _ ≤ C₂ * Cp ^ 2 * (fr ^ 2 * ((Dr R) ^ 2 *
          (1 + A + A ^ 2) ^ 4)) * N ^ 2 := by
        have hin : fr ^ 2 * ((Dr R) ^ 2 * (A + A ^ 2) ^ 2) ≤
            fr ^ 2 * ((Dr R) ^ 2 * (1 + A + A ^ 2) ^ 4) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hbAA (sq_nonneg _))
            (sq_nonneg _)
        have hout : C₂ * Cp ^ 2 * (fr ^ 2 * ((Dr R) ^ 2 *
            (A + A ^ 2) ^ 2)) ≤
            C₂ * Cp ^ 2 * (fr ^ 2 * ((Dr R) ^ 2 *
              (1 + A + A ^ 2) ^ 4)) :=
          mul_le_mul_of_nonneg_left hin
            (mul_nonneg hC₂ (sq_nonneg _))
        exact mul_le_mul_of_nonneg_right hout (sq_nonneg _)
      _ = C₂ * Cp ^ 2 * (fr ^ 2 * (Dr R) ^ 2) *
          ((1 + A + A ^ 2) ^ 4 * N ^ 2) := by ring
  have hT2b : lowJetSq (I := I) (M := M) g 1
      (appCcRS (I := I) (M := M) g 2 6 2
        (lieCovPair (I := I) (M := M) g gmU)
        (rsDomDomCongrSection (I := I) (M := M) g 2 6 lieCovSigma
            (slotExtendIter (I := I) (M := M) g 0 4 2
              (lieCovR4 (I := I) (M := M) g T hδT hδZ s)) -
          rsDomDomCongrSection (I := I) (M := M) g 2 6 lieCovSigma
            (slotExtendIter (I := I) (M := M) g 0 4 2
              (lieCovR4 (I := I) (M := M) g U hδU hδZ s)))) ≤
      C₂ * Bp * Cx R * ((1 + A + A ^ 2) ^ 4 * D2 ^ 2) := by
    refine happ2.trans ?_
    have hstep : C₂ * lowJetSq (I := I) (M := M) g 2
        (lieCovPair (I := I) (M := M) g gmU) *
        lowJetSq (I := I) (M := M) g 1
          (rsDomDomCongrSection (I := I) (M := M) g 2 6 lieCovSigma
              (slotExtendIter (I := I) (M := M) g 0 4 2
                (lieCovR4 (I := I) (M := M) g T hδT hδZ s)) -
            rsDomDomCongrSection (I := I) (M := M) g 2 6 lieCovSigma
              (slotExtendIter (I := I) (M := M) g 0 4 2
                (lieCovR4 (I := I) (M := M) g U hδU hδZ s))) ≤
        C₂ * Bp * (Cx R * ((1 + A + A ^ 2) ^ 4 * D2 ^ 2)) := by
      refine mul_le_mul ?_ hXD
        (jet_nonneg_lip (I := I) (M := M) (m := 1) g _) ?_
      · exact mul_le_mul_of_nonneg_left hPairU hC₂
      · exact mul_nonneg hC₂ hBp
    refine hstep.trans (le_of_eq ?_)
    ring
  have hj1 : (0 : ℝ) ≤ lowJetSq (I := I) (M := M) g 1
      (appCcRS (I := I) (M := M) g 2 6 2
        (lieCovPair (I := I) (M := M) g gmT -
          lieCovPair (I := I) (M := M) g gmU)
        (rsDomDomCongrSection (I := I) (M := M) g 2 6 lieCovSigma
          (slotExtendIter (I := I) (M := M) g 0 4 2
            (lieCovR4 (I := I) (M := M) g T hδT hδZ s)))) :=
    jet_nonneg_lip (I := I) (M := M) (m := 1) g _
  calc
    lowJetSq (I := I) (M := M) g 1
        (appCcRS (I := I) (M := M) g 2 6 2
            (lieCovPair (I := I) (M := M) g gmT -
              lieCovPair (I := I) (M := M) g gmU)
            (rsDomDomCongrSection (I := I) (M := M) g 2 6 lieCovSigma
              (slotExtendIter (I := I) (M := M) g 0 4 2
                (lieCovR4 (I := I) (M := M) g T hδT hδZ s))) +
          appCcRS (I := I) (M := M) g 2 6 2
            (lieCovPair (I := I) (M := M) g gmU)
            (rsDomDomCongrSection (I := I) (M := M) g 2 6 lieCovSigma
                (slotExtendIter (I := I) (M := M) g 0 4 2
                  (lieCovR4 (I := I) (M := M) g T hδT hδZ s)) -
              rsDomDomCongrSection (I := I) (M := M) g 2 6 lieCovSigma
                (slotExtendIter (I := I) (M := M) g 0 4 2
                  (lieCovR4 (I := I) (M := M) g U hδU hδZ s)))) ≤
      2 * (lowJetSq (I := I) (M := M) g 1
          (appCcRS (I := I) (M := M) g 2 6 2
            (lieCovPair (I := I) (M := M) g gmT -
              lieCovPair (I := I) (M := M) g gmU)
            (rsDomDomCongrSection (I := I) (M := M) g 2 6 lieCovSigma
              (slotExtendIter (I := I) (M := M) g 0 4 2
                (lieCovR4 (I := I) (M := M) g T hδT hδZ s)))) +
        lowJetSq (I := I) (M := M) g 1
          (appCcRS (I := I) (M := M) g 2 6 2
            (lieCovPair (I := I) (M := M) g gmU)
            (rsDomDomCongrSection (I := I) (M := M) g 2 6 lieCovSigma
                (slotExtendIter (I := I) (M := M) g 0 4 2
                  (lieCovR4 (I := I) (M := M) g T hδT hδZ s)) -
              rsDomDomCongrSection (I := I) (M := M) g 2 6 lieCovSigma
                (slotExtendIter (I := I) (M := M) g 0 4 2
                  (lieCovR4 (I := I) (M := M) g U hδU hδZ s))))) :=
      jet_add_lip (I := I) (M := M) g 1 _ _
    _ ≤ 2 * (C₂ * Cp ^ 2 * (fr ^ 2 * (Dr R) ^ 2) *
          ((1 + A + A ^ 2) ^ 4 * N ^ 2) +
        C₂ * Bp * Cx R * ((1 + A + A ^ 2) ^ 4 * D2 ^ 2)) := by
      have := add_le_add hT1 hT2b
      linarith
    _ ≤ B R * ((1 + A + A ^ 2) ^ 4 * (D2 ^ 2 + N ^ 2)) := by
      have c1 : (0 : ℝ) ≤ C₂ * Cp ^ 2 * (fr ^ 2 * (Dr R) ^ 2) := by
        positivity
      have c2 : (0 : ℝ) ≤ C₂ * Bp * Cx R :=
        mul_nonneg (mul_nonneg hC₂ hBp) (hCx R hR)
      have hd : (0 : ℝ) ≤ (1 + A + A ^ 2) ^ 4 * D2 ^ 2 :=
        mul_nonneg hpl0 (sq_nonneg _)
      have hn : (0 : ℝ) ≤ (1 + A + A ^ 2) ^ 4 * N ^ 2 :=
        mul_nonneg hpl0 (sq_nonneg _)
      have hsum : 2 * (C₂ * Cp ^ 2 * (fr ^ 2 * (Dr R) ^ 2) *
            ((1 + A + A ^ 2) ^ 4 * N ^ 2) +
          C₂ * Bp * Cx R * ((1 + A + A ^ 2) ^ 4 * D2 ^ 2)) ≤
          2 * (C₂ * Cp ^ 2 * (fr ^ 2 * (Dr R) ^ 2) *
              ((1 + A + A ^ 2) ^ 4 * D2 ^ 2 +
                (1 + A + A ^ 2) ^ 4 * N ^ 2) +
            C₂ * Bp * Cx R *
              ((1 + A + A ^ 2) ^ 4 * D2 ^ 2 +
                (1 + A + A ^ 2) ^ 4 * N ^ 2)) := by
        have e1 : C₂ * Cp ^ 2 * (fr ^ 2 * (Dr R) ^ 2) *
            ((1 + A + A ^ 2) ^ 4 * N ^ 2) ≤
            C₂ * Cp ^ 2 * (fr ^ 2 * (Dr R) ^ 2) *
              ((1 + A + A ^ 2) ^ 4 * D2 ^ 2 +
                (1 + A + A ^ 2) ^ 4 * N ^ 2) :=
          mul_le_mul_of_nonneg_left (by linarith) c1
        have e2 : C₂ * Bp * Cx R *
            ((1 + A + A ^ 2) ^ 4 * D2 ^ 2) ≤
            C₂ * Bp * Cx R *
              ((1 + A + A ^ 2) ^ 4 * D2 ^ 2 +
                (1 + A + A ^ 2) ^ 4 * N ^ 2) :=
          mul_le_mul_of_nonneg_left (by linarith) c2
        linarith
      refine hsum.trans (le_of_eq ?_)
      simp only [B]
      ring

private theorem reindex_sub_lip
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
    reindexCoeffGen_toSection,
    SmoothCcTensor.toSection_sub, ContMDiffSection.coe_sub, Pi.sub_apply]
  apply ContinuousLinearMap.ext
  intro D
  rw [ContinuousLinearMap.sub_apply, reindexCoeffFibGen_apply,
    reindexCoeffFibGen_apply, reindexCoeffFibGen_apply,
    ContinuousLinearMap.sub_apply]

private theorem trPair_sub_lip
    (g gT gU : SmoothRiemannianMetric I M) (p : ℕ)
    (σ : Equiv.Perm (Fin (p + 2))) :
    lc0TraceRF (I := I) (M := M) g gT p σ -
      lc0TraceRF (I := I) (M := M) g gU p σ =
      reindexCoeffGen (I := I) (M := M) g (p + 2) p
        (pureTrace (I := I) (M := M) g gT p -
          pureTrace (I := I) (M := M) g gU p) σ := by
  rw [lc0TraceRF, lc0TraceRF, ← reindex_sub_lip]

private theorem trPair_jet_lip
    (g gm : SmoothRiemannianMetric I M) (p m : ℕ)
    (σ : Equiv.Perm (Fin (p + 2))) :
    lowJetSq (I := I) (M := M) g m
        (lc0TraceRF (I := I) (M := M) g gm p σ) =
      lowJetSq (I := I) (M := M) g m
        (pureTrace (I := I) (M := M) g gm p) := by
  rw [lc0TraceRF, reindex_jet_lip]

private theorem rsperm_h2_lip
    (g : SmoothRiemannianMetric I M) {r s : ℕ}
    (σ : Equiv.Perm (Fin s)) (S : SmoothCcTensor g r s) :
    lowJetSq (I := I) (M := M) g 2
        (rsDomDomCongrSection (I := I) (M := M) g r s σ S) =
      lowJetSq (I := I) (M := M) g 2 S := by
  unfold lowJetSq
  apply Finset.sum_congr rfl
  intro i _
  exact rsperm_l2_lip (I := I) (M := M) g σ S i

private noncomputable def ipHead (g : SmoothRiemannianMetric I M) :
    SmoothCcTensor g 3 1 :=
  reindexCoeffGen (I := I) (M := M) g 3 1
    (cometricDoubleTraceField (I := I) g 1) ipTracePerm

private theorem ip_form_lip
    (g : SmoothRiemannianMetric I M) (om : SmoothCcTensor g 0 1) :
    ipLowCc (I := I) (M := M) g om =
      appCcRS (I := I) (M := M) g 2 3 1 (ipHead (I := I) (M := M) g)
        (slotExtend (I := I) (M := M) g 1 2
          (slotExtend (I := I) (M := M) g 0 1 om)) := rfl

private theorem ip_sub_lip
    (g : SmoothRiemannianMetric I M) (a b : SmoothCcTensor g 0 1) :
    ipLowCc (I := I) (M := M) g (a - b) =
      ipLowCc (I := I) (M := M) g a - ipLowCc (I := I) (M := M) g b := by
  rw [ip_form_lip, ip_form_lip, ip_form_lip, slotExtend_sub, slotExtend_sub,
    appCcRS_sub_right]

private lemma vb_rank0_smul_lip (x : M) (c : Tensor0SSpace 0 I x) :
    c = Tensor0SSpace.toModel c (fun i : Fin 0 => i.elim0) •
      unitTensor (I := I) (M := M) x := by
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro v
  beta_reduce
  rw [Tensor0SSpace.toModel_smul, ContinuousMultilinearMap.smul_apply,
    smul_eq_mul]
  have h1 : Tensor0SSpace.toModel
      (unitTensor (I := I) (M := M) x) v = (1 : ℝ) := rfl
  rw [h1, mul_one]
  congr 1
  funext i
  exact i.elim0

private lemma vbMcd_unit_lip (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (m : Fin 3 → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 3
        (metricConnDiffLoweredCc (I := I) (M := M) g₀ g₁ g₀) x m =
      g₁.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (m 0) (m 1)) (m 2) := by
  rw [unitModel]
  rw [show (metricConnDiffLoweredCc (I := I) (M := M) g₀ g₁ g₀).toSection x
      (unitTensor (I := I) (M := M) x) =
      (MixedSection.eval₀ (F := E)
          (E := (TangentSpace I : M → Type _)) x).smulRight
        (metricConnDiffLoweredFib (I := I) g₁ g₁ g₀ x)
        (ContinuousMultilinearMap.constOfIsEmpty ℝ
          (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))
      from rfl]
  rw [ContinuousLinearMap.smulRight_apply, MixedSection.eval₀_apply,
    ContinuousMultilinearMap.constOfIsEmpty_apply, one_smul]
  exact metricConnDiffLoweredFib_toModel (I := I) g₁ g₁ g₀ x m

private lemma vbPK_slotExt_lip (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (B : Tensor0SSpace 1 I x) :
    Tensor0SSpace.toModel
        (tensor0SProdKappaFib (I := I) (p := 1) (q := 3) x
          (metricConnDiffLoweredFib (I := I) g₁ g₁ g₀ x) B) =
      Tensor0SSpace.toModel
        (slotExtendFib (I := I) (M := M) g₀ 0 3 x
          (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
            (metricConnDiffLoweredCc (I := I) (M := M) g₀ g₁ g₀).toSection x)
          B) := by
  classical
  apply ContinuousMultilinearMap.ext
  intro u
  rw [show (u : Fin 4 → E) = Fin.cons (u 0) (Fin.tail u) from
    (Fin.cons_self_tail u).symm]
  rw [tensor0SProdKappaFib_apply, Tensor0SSpace.toModel_ofModel,
    Bundle.continuousMultilinearMap.modelProduct_apply]
  rw [slotExtendFib_apply_eval (I := I) (M := M) g₀ 0 3 x
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
      (metricConnDiffLoweredCc (I := I) (M := M) g₀ g₁ g₀).toSection x)
    B (u 0) (Fin.tail u)]
  have hc : tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 0 x B (u 0) =
      Tensor0SSpace.toModel B (fun _ : Fin 1 => u 0) •
        unitTensor (I := I) (M := M) x := by
    have h2 := vb_rank0_smul_lip (I := I) (M := M) x
      (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 0 x B (u 0))
    rw [h2]
    congr 1
    rw [TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M)
      (T := B) (v0 := u 0) (vs := fun i : Fin 0 => i.elim0)]
    congr 1
    funext k
    fin_cases k
    rfl
  rw [hc, ContinuousLinearMap.map_smul, Tensor0SSpace.toModel_smul,
    ContinuousMultilinearMap.smul_apply, smul_eq_mul]
  rw [show Tensor0SSpace.toModel
      ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
        (metricConnDiffLoweredCc (I := I) (M := M) g₀ g₁ g₀).toSection x)
        (unitTensor (I := I) (M := M) x)) (Fin.tail u) =
      unitModel (I := I) (M := M) g₀ 3
        (metricConnDiffLoweredCc (I := I) (M := M) g₀ g₁ g₀) x
        (fun j => Fin.tail u j) from by rw [unitModel]]
  rw [vbMcd_unit_lip (I := I) (M := M) g₀ g₁ x (fun j => Fin.tail u j)]
  have hcast : ((Fin.cons (u 0) (Fin.tail u) : Fin 4 → E) ∘
      Fin.castAdd 3) = (fun _ : Fin 1 => u 0) := by
    funext i
    fin_cases i
    rfl
  have hnat : ((Fin.cons (u 0) (Fin.tail u) : Fin 4 → E) ∘
      Fin.natAdd 1) = Fin.tail u := by
    funext j
    have hj : Fin.natAdd 1 j = Fin.succ j := by
      apply Fin.ext
      simp [Fin.natAdd, Fin.succ, Nat.add_comm]
    show Fin.cons (u 0) (Fin.tail u) (Fin.natAdd 1 j) = Fin.tail u j
    rw [hj, Fin.cons_succ]
  rw [hcast, hnat]
  rw [metricConnDiffLoweredFib_toModel (I := I) g₁ g₁ g₀ x
    (fun j => Fin.tail u j)]

private lemma vbmcd_rel_lip (g₀ g₁ : SmoothRiemannianMetric I M) :
    ∀ (y : M) (d : Tensor0SSpace 1 I y),
      Tensor0SSpace.toModel
          ((show Tensor0SSpace 1 I y →L[ℝ] Tensor0SSpace 4 I y from
            (vbMcdArm (I := I) (M := M) g₀ g₁).toSection y) d) =
        ContinuousMultilinearMap.domDomCongr LieCorr0Core.lieCorr0VBPerm
          (Tensor0SSpace.toModel
            ((show Tensor0SSpace 1 I y →L[ℝ] Tensor0SSpace 4 I y from
              (slotExtend (I := I) (M := M) g₀ 0 3
                (metricConnDiffLoweredCc (I := I) (M := M) g₀ g₁ g₀)).toSection
                  y) d)) := by
  intro y d
  rw [show ((show Tensor0SSpace 1 I y →L[ℝ] Tensor0SSpace 4 I y from
      (vbMcdArm (I := I) (M := M) g₀ g₁).toSection y) d) =
      domDomCongrFibRank (I := I) 4 LieCorr0Core.lieCorr0VBPerm y
        (tensor0SProdKappaFib (I := I) (p := 1) (q := 3) y
          (metricConnDiffLoweredFib (I := I) g₁ g₁ g₀ y) d) from rfl]
  rw [domDomCongrFibRank_apply, Tensor0SSpace.toModel_ofModel]
  exact congrArg
    (ContinuousMultilinearMap.domDomCongr LieCorr0Core.lieCorr0VBPerm)
    (vbPK_slotExt_lip (I := I) (M := M) g₀ g₁ y d)

private theorem vbmcd_perm_eq
    (g gm : SmoothRiemannianMetric I M) :
    vbMcdArm (I := I) (M := M) g gm =
      rsDomDomCongrSection (I := I) (M := M) g 1 4
        LieCorr0Core.lieCorr0VBPerm
        (slotExtend (I := I) (M := M) g 0 3
          (metricConnDiffLoweredCc (I := I) (M := M) g gm g)) := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro d
  apply Tensor0SSpace.toModel_injective
  beta_reduce
  rw [rsDomDomCongrSection_toSection, toModel_rsDomDomCongr_apply]
  exact vbmcd_rel_lip (I := I) (M := M) g gm x d

private theorem vbmcd_h2_lip
    (g gm : SmoothRiemannianMetric I M) :
    lowJetSq (I := I) (M := M) g 2 (vbMcdArm (I := I) (M := M) g gm) ≤
      (Module.finrank ℝ E : ℝ) *
        lowJetSq (I := I) (M := M) g 2
          (metricConnDiffLoweredCc (I := I) (M := M) g gm g) := by
  rw [vbmcd_perm_eq, rsperm_h2_lip]
  exact slot_h2_lip (I := I) (M := M) g 0 3 _

private theorem vbmcd_sub_h1_lip
    (g gT gU : SmoothRiemannianMetric I M) :
    lowJetSq (I := I) (M := M) g 1
        (vbMcdArm (I := I) (M := M) g gT -
          vbMcdArm (I := I) (M := M) g gU) ≤
      (Module.finrank ℝ E : ℝ) *
        lowJetSq (I := I) (M := M) g 1
          (metricConnDiffLoweredCc (I := I) (M := M) g gT g -
            metricConnDiffLoweredCc (I := I) (M := M) g gU g) := by
  rw [vbmcd_perm_eq, vbmcd_perm_eq, ← rsperm_sub_lip, ← slotExtend_sub,
    rsperm_h1_lip]
  exact slot_h1_lip (I := I) (M := M) g 0 3 _

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 1000000 in
set_option linter.unusedVariables false in
/-- **Class 3 of the C0 `H¹` five-class telescope.**  On a common spectral `H²` ball the
vector--bilinear zeroth-order DeTurck correction `lc0VB` is `H¹`-Lipschitz along the
realized family, with only the `H²` state difference `D2` and the `Hˢ` difference `N`
on the right and the third-jet size `A` entering polynomially. -/
private theorem vb_pair_h1
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ : ℝ, ∃ B : ℝ → ℝ,
      0 < ρ ∧ (∀ R : ℝ, 0 ≤ R → 0 ≤ B R) ∧
      ∀ (T U : SmoothCcTensor g 0 2)
        (hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        (hU : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g U x u v =
            ccTensorBilin (I := I) g U x v u)
        {δ : ℝ} (hδ_le : δ ≤ 1 / 3) (hδ0 : 0 ≤ δ)
        (hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδU : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g U) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        (R A D2 N : ℝ), 0 ≤ R → 0 ≤ A → 0 ≤ D2 → 0 ≤ N →
        lowJetSq (I := I) (M := M) g 2 T ≤ R ^ 2 →
        lowJetSq (I := I) (M := M) g 2 U ≤ R ^ 2 →
        lowJetSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
        lowJetSq (I := I) (M := M) g 3 U ≤ A ^ 2 →
        lowJetSq (I := I) (M := M) g 2 (T - U) ≤ D2 ^ 2 →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U)‖ ≤ N →
        ∀ {s : ℝ}, s ∈ Set.Icc (0 : ℝ) 1 →
      lowJetSq (I := I) (M := M) g 1
          (lc0VB (I := I) (M := M) g
              (realizedFam (I := I) g T 0 hδT hδZ s) -
            lc0VB (I := I) (M := M) g
              (realizedFam (I := I) g U 0 hδU hδZ s)) ≤
        B R * ((1 + A + A ^ 2) ^ 4 * (D2 ^ 2 + N ^ 2)) := by
  -- ## product moduli
  obtain ⟨Cout, hCout, happOut⟩ :=
    app_h21_mul_lip (I := I) (M := M) hDim g 2 4 2
  obtain ⟨Cin1, hCin1, happIn1⟩ :=
    app_h21_mul_lip (I := I) (M := M) hDim g 2 1 4
  obtain ⟨Cin12, hCin12, happIn12⟩ :=
    app_h12_mul_lip (I := I) (M := M) hDim g 2 1 4
  obtain ⟨Cip1, hCip1, happIp1⟩ :=
    app_h21_mul_lip (I := I) (M := M) hDim g 2 3 1
  obtain ⟨Cip2, hCip2, happIp2⟩ :=
    app_h2_mul_lip (I := I) (M := M) hDim g 2 3 1
  obtain ⟨Cw1, hCw1, happW1⟩ :=
    app_h21_mul_lip (I := I) (M := M) hDim g 0 3 1
  obtain ⟨Cw2, hCw2, happW2⟩ :=
    app_h2_mul_lip (I := I) (M := M) hDim g 0 3 1
  -- ## factor moduli
  obtain ⟨ρt1, Ct1, hρt1, hCt1, htp1⟩ :=
    LowBaseInternal.trace1_pair_h2 (I := I) (M := M) hDim g      -- (M1)
  obtain ⟨ρb1, Bt1, hρb1, hBt1, htb1⟩ :=
    LowBaseInternal.trace1_h2_bdd (I := I) (M := M) hDim g       -- (M2)
  obtain ⟨ρt2, Ct2, hρt2, hCt2, htp2⟩ :=
    LowBaseInternal.trace2_pair_h2 (I := I) (M := M) hDim g
  obtain ⟨ρb2, Bt2, hρb2, hBt2, htb2⟩ :=
    LowBaseInternal.trace2_h2_bdd (I := I) (M := M) hDim g
  obtain ⟨B0m, B1m, hB0m, hB1m, hmcdp⟩ :=
    LowBaseInternal.mcd_pair_h1 (I := I) (M := M) hDim g
      (δ₀ := (1 : ℝ) / 3) (by norm_num) (by norm_num)
  obtain ⟨Bm, hBm, hmcdb⟩ :=
    LowBaseInternal.mcd_h2_bdd (I := I) (M := M) hDim g
      (δ₀ := (1 : ℝ) / 3) (by norm_num) (by norm_num)
  obtain ⟨W0, W1, hW0, hW1, hwxip⟩ :=
    wXi_pair_h1 (I := I) (M := M) hDim g
      (δ₀ := (1 : ℝ) / 3) (by norm_num) (by norm_num)
  obtain ⟨Bs, hBs, hwxib⟩ :=
    wXi_self_tame (I := I) (M := M) hDim g
  -- ## fixed scalars
  set fr : ℝ := (Module.finrank ℝ E : ℝ) with hfrdef
  have hfr : 0 ≤ fr := Nat.cast_nonneg _
  set Jp : ℝ := lowJetSq (I := I) (M := M) g 2 (ipHead (I := I) (M := M) g)
    with hJpdef
  have hJp : 0 ≤ Jp := jet_nonneg_lip (I := I) (M := M) (m := 2) g _
  set ρ : ℝ := min (min ρt1 ρb1) (min ρt2 ρb2) with hρdef
  have hρ0 : 0 < ρ :=
    lt_min (lt_min hρt1 hρb1) (lt_min hρt2 hρb2)
  -- ## constant ladder
  let Wb : ℝ → ℝ := fun R => Cw2 * Bt1 ^ 2 * (Bs R) ^ 2
  let Wm : ℝ → ℝ := fun R =>
    2 * (Cw1 * Ct1 ^ 2 * (Bs R) ^ 2 +
      Cw1 * Bt1 ^ 2 * (2 * (W0 R) ^ 2 + 2 * (W1 R) ^ 2))
  let Ib : ℝ → ℝ := fun R => Cip2 * Jp * fr ^ 2 * Wb R
  let Im : ℝ → ℝ := fun R => Cip1 * Jp * fr ^ 2 * Wm R
  let Vb : ℝ → ℝ := fun R => fr * (Bm R) ^ 2 * 2
  let Vd : ℝ → ℝ := fun R => fr * (2 * (B0m R) ^ 2 + 2 * (B1m R) ^ 2)
  let Sin : ℝ → ℝ := fun R => Cin1 * Vb R * Ib R
  let Kv : ℝ → ℝ := fun R => Cin12 * Vd R * Ib R
  let Ki : ℝ → ℝ := fun R => Cin1 * Vb R * Im R
  let K1 : ℝ → ℝ := fun R => Cout * Ct2 ^ 2 * Sin R
  let K2 : ℝ → ℝ := fun R => Cout * Bt2 ^ 2 * (2 * (Kv R + Ki R))
  let B : ℝ → ℝ := fun R => 4 * (2 * (K1 R + K2 R))
  have hWb : ∀ R : ℝ, 0 ≤ R → 0 ≤ Wb R := fun R hR => by
    have := hBs R hR; positivity
  have hWm : ∀ R : ℝ, 0 ≤ R → 0 ≤ Wm R := fun R hR => by
    have h0 := hW0 R hR
    have h1 := hW1 R hR
    have hb := hBs R hR
    positivity
  have hIb : ∀ R : ℝ, 0 ≤ R → 0 ≤ Ib R := fun R hR => by
    have := hWb R hR; positivity
  have hIm : ∀ R : ℝ, 0 ≤ R → 0 ≤ Im R := fun R hR => by
    have := hWm R hR; positivity
  have hVb : ∀ R : ℝ, 0 ≤ R → 0 ≤ Vb R := fun R hR => by positivity
  have hVd : ∀ R : ℝ, 0 ≤ R → 0 ≤ Vd R := fun R hR => by positivity
  have hSin : ∀ R : ℝ, 0 ≤ R → 0 ≤ Sin R := fun R hR =>
    mul_nonneg (mul_nonneg hCin1 (hVb R hR)) (hIb R hR)
  have hKv : ∀ R : ℝ, 0 ≤ R → 0 ≤ Kv R := fun R hR =>
    mul_nonneg (mul_nonneg hCin12 (hVd R hR)) (hIb R hR)
  have hKi : ∀ R : ℝ, 0 ≤ R → 0 ≤ Ki R := fun R hR =>
    mul_nonneg (mul_nonneg hCin1 (hVb R hR)) (hIm R hR)
  have hK1 : ∀ R : ℝ, 0 ≤ R → 0 ≤ K1 R := fun R hR =>
    mul_nonneg (mul_nonneg hCout (sq_nonneg _)) (hSin R hR)
  have hK2 : ∀ R : ℝ, 0 ≤ R → 0 ≤ K2 R := fun R hR =>
    mul_nonneg (mul_nonneg hCout (sq_nonneg _))
      (by
        have := hKv R hR
        have := hKi R hR
        linarith)
  refine ⟨ρ, B, hρ0, ?_, ?_⟩
  · intro R hR
    have := hK1 R hR
    have := hK2 R hR
    simp only [B]
    linarith
  intro T U hT hU δ hδ_le hδ0 hδT hδU hδZ
    R A D2 N hR hA hD2 hN hT2 hU2 hT3 hU3 hTU2 hTn hUn hTUn s hs
  ------------------------------------------------------------------
  -- ## standard plumbing block (verbatim from `amixHalf_pair_h1`)
  ------------------------------------------------------------------
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le (by norm_num)
  set gmT : SmoothRiemannianMetric I M :=
    realizedFam (I := I) g T 0 hδT hδZ s with hgmT
  set gmU : SmoothRiemannianMetric I M :=
    realizedFam (I := I) g U 0 hδU hδZ s with hgmU
  set P : SmoothCcTensor g 0 2 := s • T with hcP
  set Q : SmoothCcTensor g 0 2 := s • U with hcQ
  have hs_mem : s ∈ realizedSmallSet (δ := δ) (δ' := δ) :=
    Icc_subset_realizedSmallSet hδ_lt hδ_lt hs
  have hsabs : ‖s‖ ≤ (1 : ℝ) := by
    rw [Real.norm_eq_abs, abs_of_nonneg hs.1]
    exact hs.2
  have hs2 : s ^ 2 ≤ (1 : ℝ) := by
    nlinarith [hs.1, hs.2]
  have hPsymm : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g P x u v =
        ccTensorBilin (I := I) g P x v u := by
    intro x u v
    simp only [hcP, ccTensorBilin_apply, ccTensorModel_smul,
      ContinuousMultilinearMap.smul_apply, smul_eq_mul]
    apply congrArg (fun z : ℝ => s * z)
    simpa only [ccTensorBilin_apply] using hT x u v
  have hQsymm : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g Q x u v =
        ccTensorBilin (I := I) g Q x v u := by
    intro x u v
    simp only [hcQ, ccTensorBilin_apply, ccTensorModel_smul,
      ContinuousMultilinearMap.smul_apply, smul_eq_mul]
    apply congrArg (fun z : ℝ => s * z)
    simpa only [ccTensorBilin_apply] using hU x u v
  have hPtie : ∀ (x : M) (u v : TangentSpace I x),
      gmT.inner x u v =
        g.inner x u v + ccTensorBilinSymm (I := I) g P x u v := by
    intro x u v
    simpa only [hgmT, hcP, convexPerturbation, smul_zero, zero_add] using
      realizedFam_inner_of_mem (I := I) g T 0 hδT hδZ hs_mem x u v
  have hQtie : ∀ (x : M) (u v : TangentSpace I x),
      gmU.inner x u v =
        g.inner x u v + ccTensorBilinSymm (I := I) g Q x u v := by
    intro x u v
    simpa only [hgmU, hcQ, convexPerturbation, smul_zero, zero_add] using
      realizedFam_inner_of_mem (I := I) g U 0 hδU hδZ hs_mem x u v
  have hδP : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g P) δ := by
    intro x u v
    have hraw :=
      convexPerturbation_gFibreOpBound_abs (I := I) g T 0 hδT hδZ s x u v
    have heq : |1 - s| * δ + |s| * δ = δ := by
      rw [abs_of_nonneg (by linarith [hs.2] : (0 : ℝ) ≤ 1 - s),
        abs_of_nonneg hs.1]
      ring
    simpa only [hcP, convexPerturbation, smul_zero, zero_add, heq] using hraw
  have hδQ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g Q) δ := by
    intro x u v
    have hraw :=
      convexPerturbation_gFibreOpBound_abs (I := I) g U 0 hδU hδZ s x u v
    have heq : |1 - s| * δ + |s| * δ = δ := by
      rw [abs_of_nonneg (by linarith [hs.2] : (0 : ℝ) ≤ 1 - s),
        abs_of_nonneg hs.1]
      ring
    simpa only [hcQ, convexPerturbation, smul_zero, zero_add, heq] using hraw
  have hP2 : lowJetSq (I := I) (M := M) g 2 P ≤ R ^ 2 := by
    rw [hcP, jet_smul_lip]
    exact (mul_le_of_le_one_left
      (jet_nonneg_lip (I := I) (M := M) (m := 2) g T) hs2).trans hT2
  have hQ2 : lowJetSq (I := I) (M := M) g 2 Q ≤ R ^ 2 := by
    rw [hcQ, jet_smul_lip]
    exact (mul_le_of_le_one_left
      (jet_nonneg_lip (I := I) (M := M) (m := 2) g U) hs2).trans hU2
  have hP3 : lowJetSq (I := I) (M := M) g 3 P ≤ A ^ 2 := by
    rw [hcP, jet_smul_lip]
    exact (mul_le_of_le_one_left
      (jet_nonneg_lip (I := I) (M := M) (m := 3) g T) hs2).trans hT3
  have hQ3 : lowJetSq (I := I) (M := M) g 3 Q ≤ A ^ 2 := by
    rw [hcQ, jet_smul_lip]
    exact (mul_le_of_le_one_left
      (jet_nonneg_lip (I := I) (M := M) (m := 3) g U) hs2).trans hU3
  have hPQ2 : lowJetSq (I := I) (M := M) g 2 (P - Q) ≤ D2 ^ 2 := by
    have hPQ : P - Q = s • (T - U) := by rw [hcP, hcQ, smul_sub]
    rw [hPQ, jet_smul_lip]
    exact (mul_le_of_le_one_left
      (jet_nonneg_lip (I := I) (M := M) (m := 2) g (T - U)) hs2).trans hTU2
  have hball : ∀ ρ' : ℝ, ρ ≤ ρ' →
      (‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) P‖ ≤ ρ' ∧
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) Q‖ ≤ ρ') := by
    intro ρ' hρ'
    constructor
    · rw [hcP, ccTensorToHs_smul, norm_smul]
      exact (mul_le_mul_of_nonneg_right hsabs (norm_nonneg _)).trans
        (by simpa using (hTn.trans hρ'))
    · rw [hcQ, ccTensorToHs_smul, norm_smul]
      exact (mul_le_mul_of_nonneg_right hsabs (norm_nonneg _)).trans
        (by simpa using (hUn.trans hρ'))
  have hPQn : ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (P - Q)‖ ≤ N := by
    have hPQ : P - Q = s • (T - U) := by rw [hcP, hcQ, smul_sub]
    rw [hPQ, ccTensorToHs_smul, norm_smul]
    exact (mul_le_mul_of_nonneg_right hsabs (norm_nonneg _)).trans
      (by simpa using hTUn)
  ------------------------------------------------------------------
  -- ## polynomial bookkeeping
  ------------------------------------------------------------------
  set pl2 : ℝ := (1 + A + A ^ 2) ^ 2 with hpl2
  have hb1 : (1 : ℝ) ≤ 1 + A + A ^ 2 := by nlinarith [hA, sq_nonneg A]
  have hpl21 : (1 : ℝ) ≤ pl2 := by
    rw [hpl2]
    calc (1 : ℝ) = 1 ^ 2 := by norm_num
      _ ≤ (1 + A + A ^ 2) ^ 2 := pow_le_pow_left₀ zero_le_one hb1 2
  have hpl20 : 0 ≤ pl2 := le_trans zero_le_one hpl21
  have hplA2 : A ^ 2 ≤ pl2 := by
    rw [hpl2]
    nlinarith [hA, sq_nonneg A, mul_nonneg hA hA,
      mul_nonneg (mul_nonneg hA hA) hA]
  have h1A : (1 + A) ^ 2 ≤ 2 * pl2 := by
    rw [hpl2]
    nlinarith [hA, sq_nonneg A, mul_nonneg hA hA,
      mul_nonneg (mul_nonneg hA hA) hA]
  set u : ℝ := D2 ^ 2 + N ^ 2 with hu
  have hu0 : 0 ≤ u := by rw [hu]; positivity
  have hpl2u : 0 ≤ pl2 * u := mul_nonneg hpl20 hu0
  have hD2u : D2 ^ 2 ≤ pl2 * u := by
    have h1 : D2 ^ 2 ≤ u := by rw [hu]; nlinarith [sq_nonneg N]
    calc D2 ^ 2 ≤ u := h1
      _ = 1 * u := (one_mul u).symm
      _ ≤ pl2 * u := mul_le_mul_of_nonneg_right hpl21 hu0
  have hA2D : A ^ 2 * D2 ^ 2 ≤ pl2 * u := by
    have h1 : A ^ 2 * D2 ^ 2 ≤ pl2 * D2 ^ 2 :=
      mul_le_mul_of_nonneg_right hplA2 (sq_nonneg _)
    have h2 : pl2 * D2 ^ 2 ≤ pl2 * u := by
      rw [hu]
      have : D2 ^ 2 ≤ D2 ^ 2 + N ^ 2 := by nlinarith [sq_nonneg N]
      exact mul_le_mul_of_nonneg_left this hpl20
    linarith
  -- the `(B0·D2 + B1·A·D2)² ≤ (2B0² + 2B1²)·(pl2·u)` folding, used twice
  have hpairfold : ∀ b0 b1 : ℝ,
      (b0 * D2 + b1 * A * D2) ^ 2 ≤
        (2 * b0 ^ 2 + 2 * b1 ^ 2) * (pl2 * u) := by
    intro b0 b1
    have hstep : (b0 * D2 + b1 * A * D2) ^ 2 ≤
        2 * b0 ^ 2 * D2 ^ 2 + 2 * b1 ^ 2 * (A ^ 2 * D2 ^ 2) := by
      nlinarith [sq_nonneg (b0 * D2 - b1 * A * D2)]
    refine hstep.trans ?_
    have e1 : 2 * b0 ^ 2 * D2 ^ 2 ≤ 2 * b0 ^ 2 * (pl2 * u) :=
      mul_le_mul_of_nonneg_left hD2u (by positivity)
    have e2 : 2 * b1 ^ 2 * (A ^ 2 * D2 ^ 2) ≤ 2 * b1 ^ 2 * (pl2 * u) :=
      mul_le_mul_of_nonneg_left hA2D (by positivity)
    linarith
  ------------------------------------------------------------------
  -- ## the moving factors
  ------------------------------------------------------------------
  set mcdT : SmoothCcTensor g 0 3 :=
    metricConnDiffLoweredCc (I := I) (M := M) g gmT g with hmT
  set mcdU : SmoothCcTensor g 0 3 :=
    metricConnDiffLoweredCc (I := I) (M := M) g gmU g with hmU
  set cdT : SmoothCcTensor g 0 3 :=
    connDiffLoweredCc (I := I) g gmT with hcdT
  set cdU : SmoothCcTensor g 0 3 :=
    connDiffLoweredCc (I := I) g gmU with hcdU
  set Tr1T : SmoothCcTensor g 3 1 :=
    lc0TraceRF (I := I) (M := M) g gmT 1 (Equiv.refl (Fin 3)) with hTr1T
  set Tr1U : SmoothCcTensor g 3 1 :=
    lc0TraceRF (I := I) (M := M) g gmU 1 (Equiv.refl (Fin 3)) with hTr1U
  set WT : SmoothCcTensor g 0 1 :=
    wOmega (I := I) (M := M) g gmT g with hWTdef
  set WU : SmoothCcTensor g 0 1 :=
    wOmega (I := I) (M := M) g gmU g with hWUdef
  set IpT : SmoothCcTensor g 2 1 := ipLowCc (I := I) (M := M) g WT with hIpT
  set IpU : SmoothCcTensor g 2 1 := ipLowCc (I := I) (M := M) g WU with hIpU
  set VmT : SmoothCcTensor g 1 4 := vbMcdArm (I := I) (M := M) g gmT with hVmT
  set VmU : SmoothCcTensor g 1 4 := vbMcdArm (I := I) (M := M) g gmU with hVmU
  set LvT : SmoothCcTensor g 4 2 := lc0RiemLive (I := I) (M := M) g gmT with hLvT
  set LvU : SmoothCcTensor g 4 2 := lc0RiemLive (I := I) (M := M) g gmU with hLvU
  set InT : SmoothCcTensor g 2 4 :=
    appCcRS (I := I) (M := M) g 2 1 4 VmT IpT with hInT
  set InU : SmoothCcTensor g 2 4 :=
    appCcRS (I := I) (M := M) g 2 1 4 VmU IpU with hInU
  ------------------------------------------------------------------
  -- ## trace moduli (ρ-cascade), verbatim shape from `amixHalf_pair_h1`
  ------------------------------------------------------------------
  have hρc : ρ ≤ ρt1 ∧ ρ ≤ ρb1 ∧ ρ ≤ ρt2 ∧ ρ ≤ ρb2 := by
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
      · rw [hρdef]
        first
        | exact le_trans (min_le_left _ _) (min_le_left _ _)
        | exact le_trans (min_le_left _ _) (min_le_right _ _)
        | exact le_trans (min_le_right _ _) (min_le_left _ _)
        | exact le_trans (min_le_right _ _) (min_le_right _ _)
  have htrp : ∀ (p : ℕ) (Cp : ℝ) (ρp' : ℝ),
      (∀ (T' U' : SmoothCcTensor g 0 2)
        (gT' gU' : SmoothRiemannianMetric I M),
        (∀ (y : M) (v w : TangentSpace I y),
          gT'.inner y v w =
            g.inner y v w + ccTensorBilinSymm (I := I) g T' y v w) →
        (∀ (y : M) (v w : TangentSpace I y),
          gU'.inner y v w =
            g.inner y v w + ccTensorBilinSymm (I := I) g U' y v w) →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T'‖ ≤ ρp' →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U'‖ ≤ ρp' →
        lowJetSq (I := I) (M := M) g 2
            (pureTrace (I := I) (M := M) g gT' p -
              pureTrace (I := I) (M := M) g gU' p) ≤
          (Cp * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
            (T' - U')‖) ^ 2) →
      0 ≤ Cp → ρ ≤ ρp' →
      lowJetSq (I := I) (M := M) g 2
          (pureTrace (I := I) (M := M) g gmT p -
            pureTrace (I := I) (M := M) g gmU p) ≤ Cp ^ 2 * u := by
    intro p Cp ρp' hpair hCp hρp'
    obtain ⟨hPn, hQn⟩ := hball ρp' hρp'
    have h := hpair P Q gmT gmU hPtie hQtie hPn hQn
    refine h.trans ?_
    have h1 : Cp * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (P - Q)‖ ≤
        Cp * N := mul_le_mul_of_nonneg_left hPQn hCp
    have h2 : (Cp * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (P - Q)‖) ^ 2 ≤
        (Cp * N) ^ 2 :=
      pow_le_pow_left₀ (mul_nonneg hCp (norm_nonneg _)) h1 2
    refine h2.trans ?_
    have : (Cp * N) ^ 2 = Cp ^ 2 * N ^ 2 := by ring
    rw [this, hu]
    nlinarith [sq_nonneg Cp, sq_nonneg D2, sq_nonneg N]
  have htrb : ∀ (p : ℕ) (Bp : ℝ) (ρp' : ℝ),
      (∀ (T' : SmoothCcTensor g 0 2)
        (gT' : SmoothRiemannianMetric I M),
        (∀ (y : M) (v w : TangentSpace I y),
          gT'.inner y v w =
            g.inner y v w + ccTensorBilinSymm (I := I) g T' y v w) →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T'‖ ≤ ρp' →
        lowJetSq (I := I) (M := M) g 2
            (pureTrace (I := I) (M := M) g gT' p) ≤ Bp ^ 2) →
      ρ ≤ ρp' →
      (lowJetSq (I := I) (M := M) g 2
          (pureTrace (I := I) (M := M) g gmT p) ≤ Bp ^ 2 ∧
        lowJetSq (I := I) (M := M) g 2
          (pureTrace (I := I) (M := M) g gmU p) ≤ Bp ^ 2) := by
    intro p Bp ρp' hbdd hρp'
    obtain ⟨hPn, hQn⟩ := hball ρp' hρp'
    exact ⟨hbdd P gmT hPtie hPn, hbdd Q gmU hQtie hQn⟩
  have htp1' := htrp 1 Ct1 ρt1 htp1 hCt1 hρc.1
  have htb1' := htrb 1 Bt1 ρb1 htb1 hρc.2.1
  have htp2' := htrp 2 Ct2 ρt2 htp2 hCt2 hρc.2.2.1
  have htb2' := htrb 2 Bt2 ρb2 htb2 hρc.2.2.2
  ------------------------------------------------------------------
  -- ## mcd / connection-difference moduli
  ------------------------------------------------------------------
  have hmbT : lowJetSq (I := I) (M := M) g 2 mcdT ≤ (Bm R) ^ 2 * (2 * pl2) := by
    rw [hmT]
    refine (hmcdb gmT P hPsymm hPtie hδ_le hδ0 hδP R A hR hA hP2 hP3).trans ?_
    have : (Bm R * (1 + A)) ^ 2 = (Bm R) ^ 2 * (1 + A) ^ 2 := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_left h1A (sq_nonneg _)
  have hmbU : lowJetSq (I := I) (M := M) g 2 mcdU ≤ (Bm R) ^ 2 * (2 * pl2) := by
    rw [hmU]
    refine (hmcdb gmU Q hQsymm hQtie hδ_le hδ0 hδQ R A hR hA hQ2 hQ3).trans ?_
    have : (Bm R * (1 + A)) ^ 2 = (Bm R) ^ 2 * (1 + A) ^ 2 := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_left h1A (sq_nonneg _)
  have hmpd : lowJetSq (I := I) (M := M) g 1 (mcdT - mcdU) ≤
      (2 * (B0m R) ^ 2 + 2 * (B1m R) ^ 2) * (pl2 * u) := by
    rw [hmT, hmU]
    exact (hmcdp gmT gmU P Q hPsymm hQsymm hPtie hQtie
      hδ_le hδ0 hδP hδ_le hδ0 hδQ R A D2 hR hA hD2 hQ2 hP3 hPQ2).trans
      (hpairfold (B0m R) (B1m R))
  -- `connDiffLoweredCc` via `wXi_self_eq`
  have hcdT2 : lowJetSq (I := I) (M := M) g 2 cdT ≤ (Bs R) ^ 2 * pl2 := by
    rw [hcdT, ← wXi_self_eq (I := I) (M := M) g gmT]
    refine (hwxib gmT P hPsymm hPtie hδ_le hδ0 hδP hδZ R A hR hA hP2 hP3).trans ?_
    have : (Bs R * A) ^ 2 = (Bs R) ^ 2 * A ^ 2 := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_left hplA2 (sq_nonneg _)
  have hcdT1 : lowJetSq (I := I) (M := M) g 1 cdT ≤ (Bs R) ^ 2 * pl2 :=
    le_trans (jet_mono_lip (I := I) (M := M) g (by norm_num) cdT) hcdT2
  have hcdd1 : lowJetSq (I := I) (M := M) g 1 (cdT - cdU) ≤
      (2 * (W0 R) ^ 2 + 2 * (W1 R) ^ 2) * (pl2 * u) := by
    rw [hcdT, hcdU, ← wXi_self_eq (I := I) (M := M) g gmT,
      ← wXi_self_eq (I := I) (M := M) g gmU]
    exact (hwxip gmT gmU g P Q hPsymm hQsymm hPtie hQtie
      hδ_le hδ0 hδP hδ_le hδ0 hδQ R A D2 hR hA hD2 hQ2 hP3 hPQ2).trans
      (hpairfold (W0 R) (W1 R))
  ------------------------------------------------------------------
  -- ## level ω : `wOmega`
  ------------------------------------------------------------------
  have hTr1U2 : lowJetSq (I := I) (M := M) g 2 Tr1U ≤ Bt1 ^ 2 := by
    rw [hTr1U, trPair_jet_lip]
    exact htb1'.2
  have hTr1T2 : lowJetSq (I := I) (M := M) g 2 Tr1T ≤ Bt1 ^ 2 := by
    rw [hTr1T, trPair_jet_lip]
    exact htb1'.1
  have hTr1d2 : lowJetSq (I := I) (M := M) g 2 (Tr1T - Tr1U) ≤ Ct1 ^ 2 * u := by
    rw [hTr1T, hTr1U, trPair_sub_lip, reindex_jet_lip]
    exact htp1'
  have hWTform : WT = appCcRS (I := I) (M := M) g 0 3 1 Tr1T cdT := by
    rw [hWTdef, hTr1T, hcdT, wOmega_refold]
  have hWUform : WU = appCcRS (I := I) (M := M) g 0 3 1 Tr1U cdU := by
    rw [hWUdef, hTr1U, hcdU, wOmega_refold]
  have hWT2 : lowJetSq (I := I) (M := M) g 2 WT ≤ Wb R * pl2 := by
    rw [hWTform]
    refine (happW2 Tr1T cdT).trans ?_
    calc
      Cw2 * lowJetSq (I := I) (M := M) g 2 Tr1T *
          lowJetSq (I := I) (M := M) g 2 cdT ≤
          Cw2 * Bt1 ^ 2 * ((Bs R) ^ 2 * pl2) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hTr1T2 hCw2) hcdT2
          (jet_nonneg_lip (I := I) (M := M) (m := 2) g cdT)
          (mul_nonneg hCw2 (sq_nonneg _))
      _ = Wb R * pl2 := by simp only [Wb]; ring
  have hWd1 : lowJetSq (I := I) (M := M) g 1 (WT - WU) ≤ Wm R * (pl2 * u) := by
    have hdel : WT - WU =
        appCcRS (I := I) (M := M) g 0 3 1 (Tr1T - Tr1U) cdT +
          appCcRS (I := I) (M := M) g 0 3 1 Tr1U (cdT - cdU) := by
      rw [hWTform, hWUform, appCcRS_sub_left, appCcRS_sub_right]
      module
    rw [hdel]
    have h1 : lowJetSq (I := I) (M := M) g 1
        (appCcRS (I := I) (M := M) g 0 3 1 (Tr1T - Tr1U) cdT) ≤
        Cw1 * Ct1 ^ 2 * (Bs R) ^ 2 * (pl2 * u) := by
      refine (happW1 _ cdT).trans ?_
      calc
        Cw1 * lowJetSq (I := I) (M := M) g 2 (Tr1T - Tr1U) *
            lowJetSq (I := I) (M := M) g 1 cdT ≤
            Cw1 * (Ct1 ^ 2 * u) * ((Bs R) ^ 2 * pl2) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hTr1d2 hCw1) hcdT1
            (jet_nonneg_lip (I := I) (M := M) (m := 1) g cdT)
            (mul_nonneg hCw1 (by positivity))
        _ = Cw1 * Ct1 ^ 2 * (Bs R) ^ 2 * (pl2 * u) := by ring
    have h2 : lowJetSq (I := I) (M := M) g 1
        (appCcRS (I := I) (M := M) g 0 3 1 Tr1U (cdT - cdU)) ≤
        Cw1 * Bt1 ^ 2 * (2 * (W0 R) ^ 2 + 2 * (W1 R) ^ 2) * (pl2 * u) := by
      refine (happW1 Tr1U _).trans ?_
      calc
        Cw1 * lowJetSq (I := I) (M := M) g 2 Tr1U *
            lowJetSq (I := I) (M := M) g 1 (cdT - cdU) ≤
            Cw1 * Bt1 ^ 2 *
              ((2 * (W0 R) ^ 2 + 2 * (W1 R) ^ 2) * (pl2 * u)) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hTr1U2 hCw1) hcdd1
            (jet_nonneg_lip (I := I) (M := M) (m := 1) g _)
            (mul_nonneg hCw1 (sq_nonneg _))
        _ = Cw1 * Bt1 ^ 2 * (2 * (W0 R) ^ 2 + 2 * (W1 R) ^ 2) * (pl2 * u) := by
          ring
    calc
      lowJetSq (I := I) (M := M) g 1 (_ + _) ≤
          2 * (lowJetSq (I := I) (M := M) g 1 _ +
            lowJetSq (I := I) (M := M) g 1 _) :=
        jet_add_lip (I := I) (M := M) g 1 _ _
      _ ≤ 2 * (Cw1 * Ct1 ^ 2 * (Bs R) ^ 2 * (pl2 * u) +
            Cw1 * Bt1 ^ 2 * (2 * (W0 R) ^ 2 + 2 * (W1 R) ^ 2) * (pl2 * u)) := by
        linarith [h1, h2]
      _ = Wm R * (pl2 * u) := by simp only [Wm]; ring
  ------------------------------------------------------------------
  -- ## level ip : `ipLowCc`
  ------------------------------------------------------------------
  have hIpT2 : lowJetSq (I := I) (M := M) g 2 IpT ≤ Ib R * pl2 := by
    rw [hIpT, ip_form_lip]
    refine (happIp2 (ipHead (I := I) (M := M) g) _).trans ?_
    have hslot : lowJetSq (I := I) (M := M) g 2
        (slotExtend (I := I) (M := M) g 1 2
          (slotExtend (I := I) (M := M) g 0 1 WT)) ≤
        fr * (fr * lowJetSq (I := I) (M := M) g 2 WT) :=
      le_trans (slot_h2_lip (I := I) (M := M) g 1 2 _)
        (mul_le_mul_of_nonneg_left (slot_h2_lip (I := I) (M := M) g 0 1 _) hfr)
    calc
      Cip2 * lowJetSq (I := I) (M := M) g 2 (ipHead (I := I) (M := M) g) *
          lowJetSq (I := I) (M := M) g 2
            (slotExtend (I := I) (M := M) g 1 2
              (slotExtend (I := I) (M := M) g 0 1 WT)) ≤
          Cip2 * Jp * (fr * (fr * (Wb R * pl2))) := by
        refine mul_le_mul (le_of_eq (by rw [hJpdef]))
          (le_trans hslot
            (mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left hWT2 hfr) hfr))
          (jet_nonneg_lip (I := I) (M := M) (m := 2) g _)
          (mul_nonneg hCip2 hJp)
      _ = Ib R * pl2 := by simp only [Ib]; ring
  have hIpT1 : lowJetSq (I := I) (M := M) g 1 IpT ≤ Ib R * pl2 :=
    le_trans (jet_mono_lip (I := I) (M := M) g (by norm_num) IpT) hIpT2
  have hIpd1 : lowJetSq (I := I) (M := M) g 1 (IpT - IpU) ≤ Im R * (pl2 * u) := by
    rw [hIpT, hIpU, ← ip_sub_lip, ip_form_lip]
    refine (happIp1 (ipHead (I := I) (M := M) g) _).trans ?_
    have hslot : lowJetSq (I := I) (M := M) g 1
        (slotExtend (I := I) (M := M) g 1 2
          (slotExtend (I := I) (M := M) g 0 1 (WT - WU))) ≤
        fr * (fr * lowJetSq (I := I) (M := M) g 1 (WT - WU)) :=
      le_trans (slot_h1_lip (I := I) (M := M) g 1 2 _)
        (mul_le_mul_of_nonneg_left (slot_h1_lip (I := I) (M := M) g 0 1 _) hfr)
    calc
      Cip1 * lowJetSq (I := I) (M := M) g 2 (ipHead (I := I) (M := M) g) *
          lowJetSq (I := I) (M := M) g 1
            (slotExtend (I := I) (M := M) g 1 2
              (slotExtend (I := I) (M := M) g 0 1 (WT - WU))) ≤
          Cip1 * Jp * (fr * (fr * (Wm R * (pl2 * u)))) := by
        refine mul_le_mul (le_of_eq (by rw [hJpdef]))
          (le_trans hslot
            (mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left hWd1 hfr) hfr))
          (jet_nonneg_lip (I := I) (M := M) (m := 1) g _)
          (mul_nonneg hCip1 hJp)
      _ = Im R * (pl2 * u) := by simp only [Im]; ring
  ------------------------------------------------------------------
  -- ## level vbMcd
  ------------------------------------------------------------------
  have hVmT2 : lowJetSq (I := I) (M := M) g 2 VmT ≤ Vb R * pl2 := by
    rw [hVmT]
    refine (vbmcd_h2_lip (I := I) (M := M) g gmT).trans ?_
    calc
      fr * lowJetSq (I := I) (M := M) g 2
          (metricConnDiffLoweredCc (I := I) (M := M) g gmT g) ≤
          fr * ((Bm R) ^ 2 * (2 * pl2)) := by
        have := hmbT
        rw [hmT] at this
        exact mul_le_mul_of_nonneg_left this hfr
      _ = Vb R * pl2 := by simp only [Vb]; ring
  have hVmU2 : lowJetSq (I := I) (M := M) g 2 VmU ≤ Vb R * pl2 := by
    rw [hVmU]
    refine (vbmcd_h2_lip (I := I) (M := M) g gmU).trans ?_
    calc
      fr * lowJetSq (I := I) (M := M) g 2
          (metricConnDiffLoweredCc (I := I) (M := M) g gmU g) ≤
          fr * ((Bm R) ^ 2 * (2 * pl2)) := by
        have := hmbU
        rw [hmU] at this
        exact mul_le_mul_of_nonneg_left this hfr
      _ = Vb R * pl2 := by simp only [Vb]; ring
  have hVmd1 : lowJetSq (I := I) (M := M) g 1 (VmT - VmU) ≤ Vd R * (pl2 * u) := by
    rw [hVmT, hVmU]
    refine (vbmcd_sub_h1_lip (I := I) (M := M) g gmT gmU).trans ?_
    calc
      fr * lowJetSq (I := I) (M := M) g 1
          (metricConnDiffLoweredCc (I := I) (M := M) g gmT g -
            metricConnDiffLoweredCc (I := I) (M := M) g gmU g) ≤
          fr * ((2 * (B0m R) ^ 2 + 2 * (B1m R) ^ 2) * (pl2 * u)) := by
        have := hmpd
        rw [hmT, hmU] at this
        exact mul_le_mul_of_nonneg_left this hfr
      _ = Vd R * (pl2 * u) := by simp only [Vd]; ring
  ------------------------------------------------------------------
  -- ## level In (inner `appCcRS`)
  ------------------------------------------------------------------
  have hInT1 : lowJetSq (I := I) (M := M) g 1 InT ≤ Sin R * (pl2 * pl2) := by
    rw [hInT]
    refine (happIn1 VmT IpT).trans ?_
    calc
      Cin1 * lowJetSq (I := I) (M := M) g 2 VmT *
          lowJetSq (I := I) (M := M) g 1 IpT ≤
          Cin1 * (Vb R * pl2) * (Ib R * pl2) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hVmT2 hCin1) hIpT1
          (jet_nonneg_lip (I := I) (M := M) (m := 1) g IpT)
          (mul_nonneg hCin1 (mul_nonneg (hVb R hR) hpl20))
      _ = Sin R * (pl2 * pl2) := by simp only [Sin]; ring
  have hInd1 : lowJetSq (I := I) (M := M) g 1 (InT - InU) ≤
      2 * (Kv R * ((pl2 * pl2) * u) + Ki R * ((pl2 * pl2) * u)) := by
    have hdel : InT - InU =
        appCcRS (I := I) (M := M) g 2 1 4 (VmT - VmU) IpT +
          appCcRS (I := I) (M := M) g 2 1 4 VmU (IpT - IpU) := by
      rw [hInT, hInU, appCcRS_sub_left, appCcRS_sub_right]
      module
    rw [hdel]
    have h1 : lowJetSq (I := I) (M := M) g 1
        (appCcRS (I := I) (M := M) g 2 1 4 (VmT - VmU) IpT) ≤
        Kv R * ((pl2 * pl2) * u) := by
      refine (happIn12 (VmT - VmU) IpT).trans ?_
      calc
        Cin12 * lowJetSq (I := I) (M := M) g 1 (VmT - VmU) *
            lowJetSq (I := I) (M := M) g 2 IpT ≤
            Cin12 * (Vd R * (pl2 * u)) * (Ib R * pl2) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hVmd1 hCin12) hIpT2
            (jet_nonneg_lip (I := I) (M := M) (m := 2) g IpT)
            (mul_nonneg hCin12 (mul_nonneg (hVd R hR) hpl2u))
        _ = Kv R * ((pl2 * pl2) * u) := by simp only [Kv]; ring
    have h2 : lowJetSq (I := I) (M := M) g 1
        (appCcRS (I := I) (M := M) g 2 1 4 VmU (IpT - IpU)) ≤
        Ki R * ((pl2 * pl2) * u) := by
      refine (happIn1 VmU (IpT - IpU)).trans ?_
      calc
        Cin1 * lowJetSq (I := I) (M := M) g 2 VmU *
            lowJetSq (I := I) (M := M) g 1 (IpT - IpU) ≤
            Cin1 * (Vb R * pl2) * (Im R * (pl2 * u)) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hVmU2 hCin1) hIpd1
            (jet_nonneg_lip (I := I) (M := M) (m := 1) g _)
            (mul_nonneg hCin1 (mul_nonneg (hVb R hR) hpl20))
        _ = Ki R * ((pl2 * pl2) * u) := by simp only [Ki]; ring
    calc
      lowJetSq (I := I) (M := M) g 1 (_ + _) ≤
          2 * (lowJetSq (I := I) (M := M) g 1 _ +
            lowJetSq (I := I) (M := M) g 1 _) :=
        jet_add_lip (I := I) (M := M) g 1 _ _
      _ ≤ 2 * (Kv R * ((pl2 * pl2) * u) + Ki R * ((pl2 * pl2) * u)) := by
        linarith [h1, h2]
  ------------------------------------------------------------------
  -- ## level Lv (outer trace) and the outer telescope
  ------------------------------------------------------------------
  have hLvd2 : lowJetSq (I := I) (M := M) g 2 (LvT - LvU) ≤ Ct2 ^ 2 * u := by
    rw [hLvT, hLvU, riemLive_eq, riemLive_eq]
    exact htp2'
  have hLvU2 : lowJetSq (I := I) (M := M) g 2 LvU ≤ Bt2 ^ 2 := by
    rw [hLvU, riemLive_eq]
    exact htb2'.2
  have hFormT : lc0VB (I := I) (M := M) g gmT =
      (2 : ℝ) • appCcRS (I := I) (M := M) g 2 4 2 LvT InT := by
    rw [hLvT, hInT, hVmT, hIpT, hWTdef, vb_refold_rf, lc0VBFormRF]
  have hFormU : lc0VB (I := I) (M := M) g gmU =
      (2 : ℝ) • appCcRS (I := I) (M := M) g 2 4 2 LvU InU := by
    rw [hLvU, hInU, hVmU, hIpU, hWUdef, vb_refold_rf, lc0VBFormRF]
  have hdel1 : lc0VB (I := I) (M := M) g gmT - lc0VB (I := I) (M := M) g gmU =
      (2 : ℝ) • (appCcRS (I := I) (M := M) g 2 4 2 (LvT - LvU) InT +
        appCcRS (I := I) (M := M) g 2 4 2 LvU (InT - InU)) := by
    rw [hFormT, hFormU, appCcRS_sub_left, appCcRS_sub_right]
    module
  rw [hdel1, jet_smul_lip]
  have h1 : lowJetSq (I := I) (M := M) g 1
      (appCcRS (I := I) (M := M) g 2 4 2 (LvT - LvU) InT) ≤
      K1 R * ((pl2 * pl2) * u) := by
    refine (happOut (LvT - LvU) InT).trans ?_
    calc
      Cout * lowJetSq (I := I) (M := M) g 2 (LvT - LvU) *
          lowJetSq (I := I) (M := M) g 1 InT ≤
          Cout * (Ct2 ^ 2 * u) * (Sin R * (pl2 * pl2)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hLvd2 hCout) hInT1
          (jet_nonneg_lip (I := I) (M := M) (m := 1) g InT)
          (mul_nonneg hCout (by positivity))
      _ = K1 R * ((pl2 * pl2) * u) := by simp only [K1]; ring
  have h2 : lowJetSq (I := I) (M := M) g 1
      (appCcRS (I := I) (M := M) g 2 4 2 LvU (InT - InU)) ≤
      K2 R * ((pl2 * pl2) * u) := by
    refine (happOut LvU (InT - InU)).trans ?_
    calc
      Cout * lowJetSq (I := I) (M := M) g 2 LvU *
          lowJetSq (I := I) (M := M) g 1 (InT - InU) ≤
          Cout * Bt2 ^ 2 *
            (2 * (Kv R * ((pl2 * pl2) * u) + Ki R * ((pl2 * pl2) * u))) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hLvU2 hCout) hInd1
          (jet_nonneg_lip (I := I) (M := M) (m := 1) g _)
          (mul_nonneg hCout (sq_nonneg _))
      _ = K2 R * ((pl2 * pl2) * u) := by simp only [K2]; ring
  have hsum : lowJetSq (I := I) (M := M) g 1
      (appCcRS (I := I) (M := M) g 2 4 2 (LvT - LvU) InT +
        appCcRS (I := I) (M := M) g 2 4 2 LvU (InT - InU)) ≤
      2 * (K1 R * ((pl2 * pl2) * u) + K2 R * ((pl2 * pl2) * u)) := by
    calc
      lowJetSq (I := I) (M := M) g 1 (_ + _) ≤
          2 * (lowJetSq (I := I) (M := M) g 1 _ +
            lowJetSq (I := I) (M := M) g 1 _) :=
        jet_add_lip (I := I) (M := M) g 1 _ _
      _ ≤ 2 * (K1 R * ((pl2 * pl2) * u) + K2 R * ((pl2 * pl2) * u)) := by
        linarith [h1, h2]
  have h4 : ((2 : ℝ)) ^ 2 = 4 := by norm_num
  rw [h4]
  calc
    (4 : ℝ) * lowJetSq (I := I) (M := M) g 1
        (appCcRS (I := I) (M := M) g 2 4 2 (LvT - LvU) InT +
          appCcRS (I := I) (M := M) g 2 4 2 LvU (InT - InU)) ≤
        4 * (2 * (K1 R * ((pl2 * pl2) * u) + K2 R * ((pl2 * pl2) * u))) :=
      mul_le_mul_of_nonneg_left hsum (by norm_num)
    _ = B R * ((1 + A + A ^ 2) ^ 4 * (D2 ^ 2 + N ^ 2)) := by
      simp only [B, hpl2, hu]
      ring

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 1000000 in
set_option linter.unusedVariables false in
private theorem amixHalf_pair_h1
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ : ℝ, ∃ B : ℝ → ℝ,
      0 < ρ ∧ (∀ R : ℝ, 0 ≤ R → 0 ≤ B R) ∧
      ∀ (T U : SmoothCcTensor g 0 2)
        (hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        (hU : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g U x u v =
            ccTensorBilin (I := I) g U x v u)
        {δ : ℝ} (hδ_le : δ ≤ 1 / 3) (hδ0 : 0 ≤ δ)
        (hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδU : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g U) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        (R A D2 N : ℝ), 0 ≤ R → 0 ≤ A → 0 ≤ D2 → 0 ≤ N →
        lowJetSq (I := I) (M := M) g 2 T ≤ R ^ 2 →
        lowJetSq (I := I) (M := M) g 2 U ≤ R ^ 2 →
        lowJetSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
        lowJetSq (I := I) (M := M) g 3 U ≤ A ^ 2 →
        lowJetSq (I := I) (M := M) g 2 (T - U) ≤ D2 ^ 2 →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U)‖ ≤ N →
        ∀ {s : ℝ}, s ∈ Set.Icc (0 : ℝ) 1 →
        ∀ (σlast : Equiv.Perm (Fin 4)),
      lowJetSq (I := I) (M := M) g 1
          (lc0AMixHalfRF (I := I) (M := M) g
              (realizedFam (I := I) g T 0 hδT hδZ s) g σlast -
            lc0AMixHalfRF (I := I) (M := M) g
              (realizedFam (I := I) g U 0 hδU hδZ s) g σlast) ≤
        B R * ((1 + A + A ^ 2) ^ 4 * (D2 ^ 2 + N ^ 2)) := by
  obtain ⟨Ca1, hCa1, happ1⟩ :=
    app_h21_mul_lip (I := I) (M := M) hDim g 2 4 2
  obtain ⟨Ca2, hCa2, happ2⟩ :=
    app_h21_mul_lip (I := I) (M := M) hDim g 2 6 4
  obtain ⟨Ca3, hCa3, happ3⟩ :=
    app_h21_mul_lip (I := I) (M := M) hDim g 2 3 6
  obtain ⟨Ca3f, hCa3f, happ3f⟩ :=
    app_h12_mul_lip (I := I) (M := M) hDim g 2 3 6
  obtain ⟨Ca4, hCa4, happ4⟩ :=
    app_h21_mul_lip (I := I) (M := M) hDim g 2 5 3
  obtain ⟨Ca4b, hCa4b, happ4b⟩ :=
    app_h2_mul_lip (I := I) (M := M) hDim g 2 5 3
  obtain ⟨ρt2, Ct2, hρt2, hCt2, htp2⟩ :=
    LowBaseInternal.trace2_pair_h2 (I := I) (M := M) hDim g
  obtain ⟨ρt3, Ct3, hρt3, hCt3, htp3⟩ :=
    LowBaseInternal.trace3_pair_h2 (I := I) (M := M) hDim g
  obtain ⟨ρt4, Ct4, hρt4, hCt4, htp4⟩ :=
    LowBaseInternal.trace4_pair_h2 (I := I) (M := M) hDim g
  obtain ⟨ρb2, Bt2, hρb2, hBt2, htb2⟩ :=
    LowBaseInternal.trace2_h2_bdd (I := I) (M := M) hDim g
  obtain ⟨ρb3, Bt3, hρb3, hBt3, htb3⟩ :=
    LowBaseInternal.trace3_h2_bdd (I := I) (M := M) hDim g
  obtain ⟨ρb4, Bt4, hρb4, hBt4, htb4⟩ :=
    LowBaseInternal.trace4_h2_bdd (I := I) (M := M) hDim g
  obtain ⟨B0m, B1m, hB0m, hB1m, hmcdp⟩ :=
    LowBaseInternal.mcd_pair_h1 (I := I) (M := M) hDim g
      (δ₀ := (1 : ℝ) / 3) (by norm_num) (by norm_num)
  obtain ⟨Bm, hBm, hmcdb⟩ :=
    LowBaseInternal.mcd_h2_bdd (I := I) (M := M) hDim g
      (δ₀ := (1 : ℝ) / 3) (by norm_num) (by norm_num)
  set fr : ℝ := (Module.finrank ℝ E : ℝ) with hfrdef
  have hfr : 0 ≤ fr := Nat.cast_nonneg _
  set ρ : ℝ := min (min ρt2 (min ρt3 ρt4)) (min ρb2 (min ρb3 ρb4))
    with hρdef
  have hρ0 : 0 < ρ :=
    lt_min (lt_min hρt2 (lt_min hρt3 hρt4))
      (lt_min hρb2 (lt_min hρb3 hρb4))
  let S5b : ℝ → ℝ := fun R => fr ^ 2 * (Bm R) ^ 2 * 2
  let S4b : ℝ → ℝ := fun R => Ca4b * (Bt3 ^ 2) * S5b R
  let S4b1 : ℝ → ℝ := fun R => Ca4 * (Bt3 ^ 2) * S5b R
  let S3b : ℝ → ℝ := fun R =>
    Ca3 * (fr ^ 3 * (Bm R) ^ 2 * 2) * S4b1 R
  let S2b : ℝ → ℝ := fun R => Ca2 * (Bt4 ^ 2) * S3b R
  let M5 : ℝ → ℝ := fun R =>
    fr ^ 2 * (2 * (B0m R) ^ 2 + 2 * (B1m R) ^ 2)
  let K5 : ℝ → ℝ := fun R => Ca4 * (Bt3 ^ 2) * M5 R
  let K4 : ℝ → ℝ := fun R => Ca4 * (Ct3 ^ 2) * S5b R
  let K3 : ℝ → ℝ := fun R =>
    Ca3f * (fr ^ 3 * (2 * (B0m R) ^ 2 + 2 * (B1m R) ^ 2)) * S4b R
  let K34 : ℝ → ℝ := fun R =>
    Ca3 * (fr ^ 3 * (Bm R) ^ 2 * 2) * (2 * (K4 R + K5 R))
  let K2 : ℝ → ℝ := fun R => Ca2 * (Ct4 ^ 2) * S3b R
  let K23 : ℝ → ℝ := fun R =>
    Ca2 * (Bt4 ^ 2) * (2 * (K3 R + K34 R))
  let K1 : ℝ → ℝ := fun R => Ca1 * (Ct2 ^ 2) * S2b R
  let K12 : ℝ → ℝ := fun R =>
    Ca1 * (Bt2 ^ 2) * (2 * (K2 R + K23 R))
  let B : ℝ → ℝ := fun R => 2 * (K1 R + K12 R)
  have hS5b : ∀ R : ℝ, 0 ≤ R → 0 ≤ S5b R := fun R hR => by
    have := hBm R hR
    positivity
  have hS4b : ∀ R : ℝ, 0 ≤ R → 0 ≤ S4b R := fun R hR =>
    mul_nonneg (mul_nonneg hCa4b (sq_nonneg _)) (hS5b R hR)
  have hS4b1 : ∀ R : ℝ, 0 ≤ R → 0 ≤ S4b1 R := fun R hR =>
    mul_nonneg (mul_nonneg hCa4 (sq_nonneg _)) (hS5b R hR)
  have hS3b : ∀ R : ℝ, 0 ≤ R → 0 ≤ S3b R := fun R hR =>
    mul_nonneg (mul_nonneg hCa3 (by positivity)) (hS4b1 R hR)
  have hS2b : ∀ R : ℝ, 0 ≤ R → 0 ≤ S2b R := fun R hR =>
    mul_nonneg (mul_nonneg hCa2 (sq_nonneg _)) (hS3b R hR)
  have hM5 : ∀ R : ℝ, 0 ≤ R → 0 ≤ M5 R := fun R hR => by
    positivity
  have hK5 : ∀ R : ℝ, 0 ≤ R → 0 ≤ K5 R := fun R hR =>
    mul_nonneg (mul_nonneg hCa4 (sq_nonneg _)) (hM5 R hR)
  have hK4 : ∀ R : ℝ, 0 ≤ R → 0 ≤ K4 R := fun R hR =>
    mul_nonneg (mul_nonneg hCa4 (sq_nonneg _)) (hS5b R hR)
  have hK3 : ∀ R : ℝ, 0 ≤ R → 0 ≤ K3 R := fun R hR =>
    mul_nonneg (mul_nonneg hCa3f (by positivity)) (hS4b R hR)
  have hK34 : ∀ R : ℝ, 0 ≤ R → 0 ≤ K34 R := fun R hR =>
    mul_nonneg (mul_nonneg hCa3 (by positivity))
      (by
        have := hK4 R hR
        have := hK5 R hR
        linarith)
  have hK2 : ∀ R : ℝ, 0 ≤ R → 0 ≤ K2 R := fun R hR =>
    mul_nonneg (mul_nonneg hCa2 (sq_nonneg _)) (hS3b R hR)
  have hK23 : ∀ R : ℝ, 0 ≤ R → 0 ≤ K23 R := fun R hR =>
    mul_nonneg (mul_nonneg hCa2 (sq_nonneg _))
      (by
        have := hK3 R hR
        have := hK34 R hR
        linarith)
  have hK1 : ∀ R : ℝ, 0 ≤ R → 0 ≤ K1 R := fun R hR =>
    mul_nonneg (mul_nonneg hCa1 (sq_nonneg _)) (hS2b R hR)
  have hK12 : ∀ R : ℝ, 0 ≤ R → 0 ≤ K12 R := fun R hR =>
    mul_nonneg (mul_nonneg hCa1 (sq_nonneg _))
      (by
        have := hK2 R hR
        have := hK23 R hR
        linarith)
  refine ⟨ρ, B, hρ0, ?_, ?_⟩
  · intro R hR
    have := hK1 R hR
    have := hK12 R hR
    simp only [B]
    linarith
  intro T U hT hU δ hδ_le hδ0 hδT hδU hδZ
    R A D2 N hR hA hD2 hN hT2 hU2 hT3 hU3 hTU2 hTn hUn hTUn s hs σlast
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le (by norm_num)
  set gmT : SmoothRiemannianMetric I M :=
    realizedFam (I := I) g T 0 hδT hδZ s with hgmT
  set gmU : SmoothRiemannianMetric I M :=
    realizedFam (I := I) g U 0 hδU hδZ s with hgmU
  set P : SmoothCcTensor g 0 2 := s • T with hcP
  set Q : SmoothCcTensor g 0 2 := s • U with hcQ
  have hs_mem : s ∈ realizedSmallSet (δ := δ) (δ' := δ) :=
    Icc_subset_realizedSmallSet hδ_lt hδ_lt hs
  have hsabs : ‖s‖ ≤ (1 : ℝ) := by
    rw [Real.norm_eq_abs, abs_of_nonneg hs.1]
    exact hs.2
  have hs2 : s ^ 2 ≤ (1 : ℝ) := by
    nlinarith [hs.1, hs.2]
  have hPsymm : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g P x u v =
        ccTensorBilin (I := I) g P x v u := by
    intro x u v
    simp only [hcP, ccTensorBilin_apply, ccTensorModel_smul,
      ContinuousMultilinearMap.smul_apply, smul_eq_mul]
    apply congrArg (fun z : ℝ => s * z)
    simpa only [ccTensorBilin_apply] using hT x u v
  have hQsymm : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g Q x u v =
        ccTensorBilin (I := I) g Q x v u := by
    intro x u v
    simp only [hcQ, ccTensorBilin_apply, ccTensorModel_smul,
      ContinuousMultilinearMap.smul_apply, smul_eq_mul]
    apply congrArg (fun z : ℝ => s * z)
    simpa only [ccTensorBilin_apply] using hU x u v
  have hPtie : ∀ (x : M) (u v : TangentSpace I x),
      gmT.inner x u v =
        g.inner x u v + ccTensorBilinSymm (I := I) g P x u v := by
    intro x u v
    simpa only [hgmT, hcP, convexPerturbation, smul_zero, zero_add] using
      realizedFam_inner_of_mem
        (I := I) g T 0 hδT hδZ hs_mem x u v
  have hQtie : ∀ (x : M) (u v : TangentSpace I x),
      gmU.inner x u v =
        g.inner x u v + ccTensorBilinSymm (I := I) g Q x u v := by
    intro x u v
    simpa only [hgmU, hcQ, convexPerturbation, smul_zero, zero_add] using
      realizedFam_inner_of_mem
        (I := I) g U 0 hδU hδZ hs_mem x u v
  have hδP : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g P) δ := by
    intro x u v
    have hraw :=
      convexPerturbation_gFibreOpBound_abs
        (I := I) g T 0 hδT hδZ s x u v
    have heq : |1 - s| * δ + |s| * δ = δ := by
      rw [abs_of_nonneg (by linarith [hs.2] : (0 : ℝ) ≤ 1 - s),
        abs_of_nonneg hs.1]
      ring
    simpa only [hcP, convexPerturbation, smul_zero, zero_add, heq] using hraw
  have hδQ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g Q) δ := by
    intro x u v
    have hraw :=
      convexPerturbation_gFibreOpBound_abs
        (I := I) g U 0 hδU hδZ s x u v
    have heq : |1 - s| * δ + |s| * δ = δ := by
      rw [abs_of_nonneg (by linarith [hs.2] : (0 : ℝ) ≤ 1 - s),
        abs_of_nonneg hs.1]
      ring
    simpa only [hcQ, convexPerturbation, smul_zero, zero_add, heq] using hraw
  have hP2 : lowJetSq (I := I) (M := M) g 2 P ≤ R ^ 2 := by
    rw [hcP, jet_smul_lip]
    exact (mul_le_of_le_one_left
      (jet_nonneg_lip (I := I) (M := M) (m := 2) g T) hs2).trans hT2
  have hQ2 : lowJetSq (I := I) (M := M) g 2 Q ≤ R ^ 2 := by
    rw [hcQ, jet_smul_lip]
    exact (mul_le_of_le_one_left
      (jet_nonneg_lip (I := I) (M := M) (m := 2) g U) hs2).trans hU2
  have hP3 : lowJetSq (I := I) (M := M) g 3 P ≤ A ^ 2 := by
    rw [hcP, jet_smul_lip]
    exact (mul_le_of_le_one_left
      (jet_nonneg_lip (I := I) (M := M) (m := 3) g T) hs2).trans hT3
  have hQ3 : lowJetSq (I := I) (M := M) g 3 Q ≤ A ^ 2 := by
    rw [hcQ, jet_smul_lip]
    exact (mul_le_of_le_one_left
      (jet_nonneg_lip (I := I) (M := M) (m := 3) g U) hs2).trans hU3
  have hPQ2 : lowJetSq (I := I) (M := M) g 2 (P - Q) ≤ D2 ^ 2 := by
    have hPQ : P - Q = s • (T - U) := by
      rw [hcP, hcQ, smul_sub]
    rw [hPQ, jet_smul_lip]
    exact (mul_le_of_le_one_left
      (jet_nonneg_lip (I := I) (M := M) (m := 2) g (T - U)) hs2).trans hTU2
  have hball : ∀ ρ' : ℝ, ρ ≤ ρ' →
      (‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) P‖ ≤ ρ' ∧
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) Q‖ ≤ ρ') := by
    intro ρ' hρ'
    constructor
    · rw [hcP, ccTensorToHs_smul, norm_smul]
      exact (mul_le_mul_of_nonneg_right hsabs (norm_nonneg _)).trans
        (by simpa using (hTn.trans hρ'))
    · rw [hcQ, ccTensorToHs_smul, norm_smul]
      exact (mul_le_mul_of_nonneg_right hsabs (norm_nonneg _)).trans
        (by simpa using (hUn.trans hρ'))
  have hPQn : ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (P - Q)‖ ≤
      N := by
    have hPQ : P - Q = s • (T - U) := by
      rw [hcP, hcQ, smul_sub]
    rw [hPQ, ccTensorToHs_smul, norm_smul]
    exact (mul_le_mul_of_nonneg_right hsabs (norm_nonneg _)).trans
      (by simpa using hTUn)
  set mcdT : SmoothCcTensor g 0 3 :=
    metricConnDiffLoweredCc (I := I) (M := M) g gmT g with hmT
  set mcdU : SmoothCcTensor g 0 3 :=
    metricConnDiffLoweredCc (I := I) (M := M) g gmU g with hmU
  set pl2 : ℝ := (1 + A + A ^ 2) ^ 2 with hpl2
  have hb1 : (1 : ℝ) ≤ 1 + A + A ^ 2 := by
    nlinarith [hA, sq_nonneg A]
  have hpl21 : (1 : ℝ) ≤ pl2 := by
    rw [hpl2]
    calc (1 : ℝ) = 1 ^ 2 := by norm_num
      _ ≤ (1 + A + A ^ 2) ^ 2 :=
        pow_le_pow_left₀ zero_le_one hb1 2
  have hpl20 : 0 ≤ pl2 := le_trans zero_le_one hpl21
  have hplA2 : A ^ 2 ≤ pl2 := by
    rw [hpl2]
    nlinarith [hA, sq_nonneg A, mul_nonneg hA hA,
      mul_nonneg (mul_nonneg hA hA) hA]
  have h1A : (1 + A) ^ 2 ≤ 2 * pl2 := by
    rw [hpl2]
    nlinarith [hA, sq_nonneg A, mul_nonneg hA hA,
      mul_nonneg (mul_nonneg hA hA) hA]
  set u : ℝ := D2 ^ 2 + N ^ 2 with hu
  have hu0 : 0 ≤ u := by
    rw [hu]
    positivity
  -- mcd moduli
  have hmb : ∀ (gm : SmoothRiemannianMetric I M)
      (Pt : SmoothCcTensor g 0 2),
      (∀ (x : M) (u v : TangentSpace I x),
        ccTensorBilin (I := I) g Pt x u v =
          ccTensorBilin (I := I) g Pt x v u) →
      (∀ (x : M) (u v : TangentSpace I x),
        gm.inner x u v =
          g.inner x u v + ccTensorBilinSymm (I := I) g Pt x u v) →
      gFibreOpBound (I := I) (M := M) g
        (ccTensorBilinSymm (I := I) g Pt) δ →
      lowJetSq (I := I) (M := M) g 2 Pt ≤ R ^ 2 →
      lowJetSq (I := I) (M := M) g 3 Pt ≤ A ^ 2 →
      lowJetSq (I := I) (M := M) g 2
        (metricConnDiffLoweredCc (I := I) (M := M) g gm g) ≤
        (Bm R) ^ 2 * (2 * pl2) := by
    intro gm Pt hPt htie hδt hp2 hp3
    have h := hmcdb gm Pt hPt htie hδ_le hδ0 hδt R A hR hA hp2 hp3
    refine h.trans ?_
    have : (Bm R * (1 + A)) ^ 2 = (Bm R) ^ 2 * (1 + A) ^ 2 := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_left h1A (sq_nonneg _)
  have hmbT : lowJetSq (I := I) (M := M) g 2 mcdT ≤
      (Bm R) ^ 2 * (2 * pl2) := by
    rw [hmT]
    exact hmb gmT P hPsymm hPtie hδP hP2 hP3
  have hmbU : lowJetSq (I := I) (M := M) g 2 mcdU ≤
      (Bm R) ^ 2 * (2 * pl2) := by
    rw [hmU]
    exact hmb gmU Q hQsymm hQtie hδQ hQ2 hQ3
  have hmpd : lowJetSq (I := I) (M := M) g 1 (mcdT - mcdU) ≤
      (2 * (B0m R) ^ 2 + 2 * (B1m R) ^ 2) * (pl2 * u) := by
    have h := hmcdp gmT gmU P Q hPsymm hQsymm hPtie hQtie
      hδ_le hδ0 hδP hδ_le hδ0 hδQ R A D2 hR hA hD2 hQ2 hP3 hPQ2
    rw [hmT, hmU]
    refine h.trans ?_
    have hstep : (B0m R * D2 + B1m R * A * D2) ^ 2 ≤
        2 * (B0m R) ^ 2 * D2 ^ 2 +
          2 * (B1m R) ^ 2 * (A ^ 2 * D2 ^ 2) := by
      nlinarith [sq_nonneg (B0m R * D2 - B1m R * A * D2)]
    refine hstep.trans ?_
    have hA2D : A ^ 2 * D2 ^ 2 ≤ pl2 * u := by
      have h1 : A ^ 2 * D2 ^ 2 ≤ pl2 * D2 ^ 2 :=
        mul_le_mul_of_nonneg_right hplA2 (sq_nonneg _)
      have h2 : pl2 * D2 ^ 2 ≤ pl2 * u := by
        rw [hu]
        have : D2 ^ 2 ≤ D2 ^ 2 + N ^ 2 := by nlinarith [sq_nonneg N]
        exact mul_le_mul_of_nonneg_left this hpl20
      linarith
    have hD2u : D2 ^ 2 ≤ pl2 * u := by
      have h1 : D2 ^ 2 ≤ u := by
        rw [hu]
        nlinarith [sq_nonneg N]
      calc D2 ^ 2 ≤ u := h1
        _ = 1 * u := (one_mul u).symm
        _ ≤ pl2 * u := mul_le_mul_of_nonneg_right hpl21 hu0
    have e1 : 2 * (B0m R) ^ 2 * D2 ^ 2 ≤
        2 * (B0m R) ^ 2 * (pl2 * u) :=
      mul_le_mul_of_nonneg_left hD2u (by positivity)
    have e2 : 2 * (B1m R) ^ 2 * (A ^ 2 * D2 ^ 2) ≤
        2 * (B1m R) ^ 2 * (pl2 * u) :=
      mul_le_mul_of_nonneg_left hA2D (by positivity)
    linarith
  -- trace moduli (ρ-cascade)
  have hρc : ρ ≤ ρt2 ∧ ρ ≤ ρt3 ∧ ρ ≤ ρt4 ∧ ρ ≤ ρb2 ∧ ρ ≤ ρb3 ∧
      ρ ≤ ρb4 := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      · rw [hρdef]
        first
        | exact le_trans (min_le_left _ _) (min_le_left _ _)
        | exact le_trans (min_le_left _ _)
            (le_trans (min_le_right _ _) (min_le_left _ _))
        | exact le_trans (min_le_left _ _)
            (le_trans (min_le_right _ _) (min_le_right _ _))
        | exact le_trans (min_le_right _ _) (min_le_left _ _)
        | exact le_trans (min_le_right _ _)
            (le_trans (min_le_right _ _) (min_le_left _ _))
        | exact le_trans (min_le_right _ _)
            (le_trans (min_le_right _ _) (min_le_right _ _))
  have htrp : ∀ (p : ℕ) (Cp : ℝ) (ρp' : ℝ),
      (∀ (T' U' : SmoothCcTensor g 0 2)
        (gT' gU' : SmoothRiemannianMetric I M),
        (∀ (y : M) (v w : TangentSpace I y),
          gT'.inner y v w =
            g.inner y v w + ccTensorBilinSymm (I := I) g T' y v w) →
        (∀ (y : M) (v w : TangentSpace I y),
          gU'.inner y v w =
            g.inner y v w + ccTensorBilinSymm (I := I) g U' y v w) →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T'‖ ≤ ρp' →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U'‖ ≤ ρp' →
        lowJetSq (I := I) (M := M) g 2
            (pureTrace (I := I) (M := M) g gT' p -
              pureTrace (I := I) (M := M) g gU' p) ≤
          (Cp * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
            (T' - U')‖) ^ 2) →
      0 ≤ Cp → ρ ≤ ρp' →
      lowJetSq (I := I) (M := M) g 2
          (pureTrace (I := I) (M := M) g gmT p -
            pureTrace (I := I) (M := M) g gmU p) ≤
        Cp ^ 2 * u := by
    intro p Cp ρp' hpair hCp hρp'
    obtain ⟨hPn, hQn⟩ := hball ρp' hρp'
    have h := hpair P Q gmT gmU hPtie hQtie hPn hQn
    refine h.trans ?_
    have h1 : Cp * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
        (P - Q)‖ ≤ Cp * N :=
      mul_le_mul_of_nonneg_left hPQn hCp
    have h2 : (Cp * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
        (P - Q)‖) ^ 2 ≤ (Cp * N) ^ 2 :=
      pow_le_pow_left₀ (mul_nonneg hCp (norm_nonneg _)) h1 2
    refine h2.trans ?_
    have : (Cp * N) ^ 2 = Cp ^ 2 * N ^ 2 := by ring
    rw [this, hu]
    nlinarith [sq_nonneg Cp, sq_nonneg D2, sq_nonneg N]
  have htrb : ∀ (p : ℕ) (Bp : ℝ) (ρp' : ℝ),
      (∀ (T' : SmoothCcTensor g 0 2)
        (gT' : SmoothRiemannianMetric I M),
        (∀ (y : M) (v w : TangentSpace I y),
          gT'.inner y v w =
            g.inner y v w + ccTensorBilinSymm (I := I) g T' y v w) →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T'‖ ≤ ρp' →
        lowJetSq (I := I) (M := M) g 2
            (pureTrace (I := I) (M := M) g gT' p) ≤ Bp ^ 2) →
      ρ ≤ ρp' →
      (lowJetSq (I := I) (M := M) g 2
          (pureTrace (I := I) (M := M) g gmT p) ≤ Bp ^ 2 ∧
        lowJetSq (I := I) (M := M) g 2
          (pureTrace (I := I) (M := M) g gmU p) ≤ Bp ^ 2) := by
    intro p Bp ρp' hbdd hρp'
    obtain ⟨hPn, hQn⟩ := hball ρp' hρp'
    exact ⟨hbdd P gmT hPtie hPn, hbdd Q gmU hQtie hQn⟩
  have htp2' := htrp 2 Ct2 ρt2 htp2 hCt2 hρc.1
  have htp3' := htrp 3 Ct3 ρt3 htp3 hCt3 hρc.2.1
  have htp4' := htrp 4 Ct4 ρt4 htp4 hCt4 hρc.2.2.1
  have htb2' := htrb 2 Bt2 ρb2 htb2 hρc.2.2.2.1
  have htb3' := htrb 3 Bt3 ρb3 htb3 hρc.2.2.2.2.1
  have htb4' := htrb 4 Bt4 ρb4 htb4 hρc.2.2.2.2.2
  -- stack abbreviations
  set S5T : SmoothCcTensor g 2 5 :=
    slotExtendIter (I := I) (M := M) g 0 3 2 mcdT with hS5Tdef
  set S5U : SmoothCcTensor g 2 5 :=
    slotExtendIter (I := I) (M := M) g 0 3 2 mcdU with hS5Udef
  set S4T : SmoothCcTensor g 2 3 :=
    appCcRS (I := I) (M := M) g 2 5 3
      (lc0TraceRF (I := I) (M := M) g gmT 3 LieCorr0Core.lieCorr0AMixPermQ) S5T
    with hS4Tdef
  set S4U : SmoothCcTensor g 2 3 :=
    appCcRS (I := I) (M := M) g 2 5 3
      (lc0TraceRF (I := I) (M := M) g gmU 3 LieCorr0Core.lieCorr0AMixPermQ) S5U
    with hS4Udef
  set E3T : SmoothCcTensor g 3 6 :=
    slotExtendIter (I := I) (M := M) g 0 3 3 mcdT with hE3Tdef
  set E3U : SmoothCcTensor g 3 6 :=
    slotExtendIter (I := I) (M := M) g 0 3 3 mcdU with hE3Udef
  set S3T : SmoothCcTensor g 2 6 :=
    appCcRS (I := I) (M := M) g 2 3 6 E3T S4T with hS3Tdef
  set S3U : SmoothCcTensor g 2 6 :=
    appCcRS (I := I) (M := M) g 2 3 6 E3U S4U with hS3Udef
  set S2T : SmoothCcTensor g 2 4 :=
    appCcRS (I := I) (M := M) g 2 6 4
      (lc0TraceRF (I := I) (M := M) g gmT 4 LieCorr0Core.lieCorr0AMixPerm1) S3T
    with hS2Tdef
  set S2U : SmoothCcTensor g 2 4 :=
    appCcRS (I := I) (M := M) g 2 6 4
      (lc0TraceRF (I := I) (M := M) g gmU 4 LieCorr0Core.lieCorr0AMixPerm1) S3U
    with hS2Udef
  have hHalfT : lc0AMixHalfRF (I := I) (M := M) g gmT g σlast =
      appCcRS (I := I) (M := M) g 2 4 2
        (lc0TraceRF (I := I) (M := M) g gmT 2 σlast) S2T := rfl
  have hHalfU : lc0AMixHalfRF (I := I) (M := M) g gmU g σlast =
      appCcRS (I := I) (M := M) g 2 4 2
        (lc0TraceRF (I := I) (M := M) g gmU 2 σlast) S2U := rfl
  -- singles, T-state
  have hmcdT1 : lowJetSq (I := I) (M := M) g 1 mcdT ≤
      (Bm R) ^ 2 * (2 * pl2) :=
    le_trans (jet_mono_lip (I := I) (M := M) g (by norm_num) mcdT) hmbT
  have hS5T1 : lowJetSq (I := I) (M := M) g 1 S5T ≤
      S5b R * pl2 := by
    rw [hS5Tdef]
    have h0 : slotExtendIter (I := I) (M := M) g 0 3 2 mcdT =
        slotExtend (I := I) (M := M) g 1 4
          (slotExtend (I := I) (M := M) g 0 3 mcdT) := rfl
    rw [h0]
    calc
      lowJetSq (I := I) (M := M) g 1
          (slotExtend (I := I) (M := M) g 1 4
            (slotExtend (I := I) (M := M) g 0 3 mcdT)) ≤
        fr * lowJetSq (I := I) (M := M) g 1
          (slotExtend (I := I) (M := M) g 0 3 mcdT) :=
        slot_h1_lip (I := I) (M := M) g 1 4 _
      _ ≤ fr * (fr * lowJetSq (I := I) (M := M) g 1 mcdT) :=
        mul_le_mul_of_nonneg_left
          (slot_h1_lip (I := I) (M := M) g 0 3 _) hfr
      _ ≤ fr * (fr * ((Bm R) ^ 2 * (2 * pl2))) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hmcdT1 hfr) hfr
      _ = S5b R * pl2 := by simp only [S5b]; ring
  have hS5T2 : lowJetSq (I := I) (M := M) g 2 S5T ≤
      S5b R * pl2 := by
    rw [hS5Tdef]
    have h0 : slotExtendIter (I := I) (M := M) g 0 3 2 mcdT =
        slotExtend (I := I) (M := M) g 1 4
          (slotExtend (I := I) (M := M) g 0 3 mcdT) := rfl
    rw [h0]
    calc
      lowJetSq (I := I) (M := M) g 2
          (slotExtend (I := I) (M := M) g 1 4
            (slotExtend (I := I) (M := M) g 0 3 mcdT)) ≤
        fr * lowJetSq (I := I) (M := M) g 2
          (slotExtend (I := I) (M := M) g 0 3 mcdT) :=
        slot_h2_lip (I := I) (M := M) g 1 4 _
      _ ≤ fr * (fr * lowJetSq (I := I) (M := M) g 2 mcdT) :=
        mul_le_mul_of_nonneg_left
          (slot_h2_lip (I := I) (M := M) g 0 3 _) hfr
      _ ≤ fr * (fr * ((Bm R) ^ 2 * (2 * pl2))) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hmbT hfr) hfr
      _ = S5b R * pl2 := by simp only [S5b]; ring
  have hE3T2 : lowJetSq (I := I) (M := M) g 2 E3T ≤
      fr ^ 3 * (Bm R) ^ 2 * 2 * pl2 := by
    rw [hE3Tdef]
    have h0 : slotExtendIter (I := I) (M := M) g 0 3 3 mcdT =
        slotExtend (I := I) (M := M) g 2 5
          (slotExtend (I := I) (M := M) g 1 4
            (slotExtend (I := I) (M := M) g 0 3 mcdT)) := rfl
    rw [h0]
    calc
      lowJetSq (I := I) (M := M) g 2
          (slotExtend (I := I) (M := M) g 2 5
            (slotExtend (I := I) (M := M) g 1 4
              (slotExtend (I := I) (M := M) g 0 3 mcdT))) ≤
        fr * lowJetSq (I := I) (M := M) g 2
          (slotExtend (I := I) (M := M) g 1 4
            (slotExtend (I := I) (M := M) g 0 3 mcdT)) :=
        slot_h2_lip (I := I) (M := M) g 2 5 _
      _ ≤ fr * (fr * lowJetSq (I := I) (M := M) g 2
          (slotExtend (I := I) (M := M) g 0 3 mcdT)) :=
        mul_le_mul_of_nonneg_left
          (slot_h2_lip (I := I) (M := M) g 1 4 _) hfr
      _ ≤ fr * (fr * (fr * lowJetSq (I := I) (M := M) g 2 mcdT)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left
            (slot_h2_lip (I := I) (M := M) g 0 3 _) hfr) hfr
      _ ≤ fr * (fr * (fr * ((Bm R) ^ 2 * (2 * pl2)))) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hmbT hfr) hfr) hfr
      _ = fr ^ 3 * (Bm R) ^ 2 * 2 * pl2 := by ring
  have hE3U2 : lowJetSq (I := I) (M := M) g 2 E3U ≤
      fr ^ 3 * (Bm R) ^ 2 * 2 * pl2 := by
    rw [hE3Udef]
    have h0 : slotExtendIter (I := I) (M := M) g 0 3 3 mcdU =
        slotExtend (I := I) (M := M) g 2 5
          (slotExtend (I := I) (M := M) g 1 4
            (slotExtend (I := I) (M := M) g 0 3 mcdU)) := rfl
    rw [h0]
    calc
      lowJetSq (I := I) (M := M) g 2
          (slotExtend (I := I) (M := M) g 2 5
            (slotExtend (I := I) (M := M) g 1 4
              (slotExtend (I := I) (M := M) g 0 3 mcdU))) ≤
        fr * lowJetSq (I := I) (M := M) g 2
          (slotExtend (I := I) (M := M) g 1 4
            (slotExtend (I := I) (M := M) g 0 3 mcdU)) :=
        slot_h2_lip (I := I) (M := M) g 2 5 _
      _ ≤ fr * (fr * lowJetSq (I := I) (M := M) g 2
          (slotExtend (I := I) (M := M) g 0 3 mcdU)) :=
        mul_le_mul_of_nonneg_left
          (slot_h2_lip (I := I) (M := M) g 1 4 _) hfr
      _ ≤ fr * (fr * (fr * lowJetSq (I := I) (M := M) g 2 mcdU)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left
            (slot_h2_lip (I := I) (M := M) g 0 3 _) hfr) hfr
      _ ≤ fr * (fr * (fr * ((Bm R) ^ 2 * (2 * pl2)))) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hmbU hfr) hfr) hfr
      _ = fr ^ 3 * (Bm R) ^ 2 * 2 * pl2 := by ring
  have hpl2u : 0 ≤ pl2 * u := mul_nonneg hpl20 hu0
  have hS4T1 : lowJetSq (I := I) (M := M) g 1 S4T ≤
      S4b1 R * pl2 := by
    rw [hS4Tdef]
    refine (happ4 _ S5T).trans ?_
    have htr := (trPair_jet_lip (I := I) (M := M) g gmT 3 2
      LieCorr0Core.lieCorr0AMixPermQ).le.trans htb3'.1
    calc
      Ca4 * lowJetSq (I := I) (M := M) g 2
          (lc0TraceRF (I := I) (M := M) g gmT 3 LieCorr0Core.lieCorr0AMixPermQ) *
        lowJetSq (I := I) (M := M) g 1 S5T ≤
        Ca4 * Bt3 ^ 2 * (S5b R * pl2) := by
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left htr hCa4) hS5T1
          (jet_nonneg_lip (I := I) (M := M) (m := 1) g _)
          (mul_nonneg hCa4 (sq_nonneg _))
      _ = S4b1 R * pl2 := by simp only [S4b1]; ring
  have hS4T2 : lowJetSq (I := I) (M := M) g 2 S4T ≤
      S4b R * pl2 := by
    rw [hS4Tdef]
    refine (happ4b _ S5T).trans ?_
    have htr := (trPair_jet_lip (I := I) (M := M) g gmT 3 2
      LieCorr0Core.lieCorr0AMixPermQ).le.trans htb3'.1
    calc
      Ca4b * lowJetSq (I := I) (M := M) g 2
          (lc0TraceRF (I := I) (M := M) g gmT 3 LieCorr0Core.lieCorr0AMixPermQ) *
        lowJetSq (I := I) (M := M) g 2 S5T ≤
        Ca4b * Bt3 ^ 2 * (S5b R * pl2) := by
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left htr hCa4b) hS5T2
          (jet_nonneg_lip (I := I) (M := M) (m := 2) g _)
          (mul_nonneg hCa4b (sq_nonneg _))
      _ = S4b R * pl2 := by simp only [S4b]; ring
  have hS3T1 : lowJetSq (I := I) (M := M) g 1 S3T ≤
      S3b R * (pl2 * pl2) := by
    rw [hS3Tdef]
    refine (happ3 E3T S4T).trans ?_
    calc
      Ca3 * lowJetSq (I := I) (M := M) g 2 E3T *
        lowJetSq (I := I) (M := M) g 1 S4T ≤
        Ca3 * (fr ^ 3 * (Bm R) ^ 2 * 2 * pl2) * (S4b1 R * pl2) := by
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left hE3T2 hCa3) hS4T1
          (jet_nonneg_lip (I := I) (M := M) (m := 1) g _)
          (mul_nonneg hCa3 (by positivity))
      _ = S3b R * (pl2 * pl2) := by simp only [S3b]; ring
  have hS2T1 : lowJetSq (I := I) (M := M) g 1 S2T ≤
      S2b R * (pl2 * pl2) := by
    rw [hS2Tdef]
    refine (happ2 _ S3T).trans ?_
    have htr := (trPair_jet_lip (I := I) (M := M) g gmT 4 2
      LieCorr0Core.lieCorr0AMixPerm1).le.trans htb4'.1
    calc
      Ca2 * lowJetSq (I := I) (M := M) g 2
          (lc0TraceRF (I := I) (M := M) g gmT 4 LieCorr0Core.lieCorr0AMixPerm1) *
        lowJetSq (I := I) (M := M) g 1 S3T ≤
        Ca2 * Bt4 ^ 2 * (S3b R * (pl2 * pl2)) := by
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left htr hCa2) hS3T1
          (jet_nonneg_lip (I := I) (M := M) (m := 1) g _)
          (mul_nonneg hCa2 (sq_nonneg _))
      _ = S2b R * (pl2 * pl2) := by simp only [S2b]; ring
  -- level-5 difference
  have hdel5 : S5T - S5U =
      slotExtend (I := I) (M := M) g 1 4
        (slotExtend (I := I) (M := M) g 0 3 (mcdT - mcdU)) := by
    rw [hS5Tdef, hS5Udef,
      show slotExtendIter (I := I) (M := M) g 0 3 2 mcdT =
        slotExtend (I := I) (M := M) g 1 4
          (slotExtend (I := I) (M := M) g 0 3 mcdT) from rfl,
      show slotExtendIter (I := I) (M := M) g 0 3 2 mcdU =
        slotExtend (I := I) (M := M) g 1 4
          (slotExtend (I := I) (M := M) g 0 3 mcdU) from rfl,
      slotExtend_sub, slotExtend_sub]
  have hd5 : lowJetSq (I := I) (M := M) g 1 (S5T - S5U) ≤
      M5 R * (pl2 * u) := by
    rw [hdel5]
    calc
      lowJetSq (I := I) (M := M) g 1
          (slotExtend (I := I) (M := M) g 1 4
            (slotExtend (I := I) (M := M) g 0 3 (mcdT - mcdU))) ≤
        fr * lowJetSq (I := I) (M := M) g 1
          (slotExtend (I := I) (M := M) g 0 3 (mcdT - mcdU)) :=
        slot_h1_lip (I := I) (M := M) g 1 4 _
      _ ≤ fr * (fr * lowJetSq (I := I) (M := M) g 1 (mcdT - mcdU)) :=
        mul_le_mul_of_nonneg_left
          (slot_h1_lip (I := I) (M := M) g 0 3 _) hfr
      _ ≤ fr * (fr * ((2 * (B0m R) ^ 2 + 2 * (B1m R) ^ 2) *
          (pl2 * u))) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hmpd hfr) hfr
      _ = M5 R * (pl2 * u) := by simp only [M5]; ring
  -- level-4 difference
  have hdel4 : S4T - S4U =
      appCcRS (I := I) (M := M) g 2 5 3
          (lc0TraceRF (I := I) (M := M) g gmT 3 LieCorr0Core.lieCorr0AMixPermQ -
            lc0TraceRF (I := I) (M := M) g gmU 3 LieCorr0Core.lieCorr0AMixPermQ)
          S5T +
        appCcRS (I := I) (M := M) g 2 5 3
          (lc0TraceRF (I := I) (M := M) g gmU 3 LieCorr0Core.lieCorr0AMixPermQ)
          (S5T - S5U) := by
    rw [hS4Tdef, hS4Udef, appCcRS_sub_left, appCcRS_sub_right]
    module
  have htrd3 : lowJetSq (I := I) (M := M) g 2
      (lc0TraceRF (I := I) (M := M) g gmT 3 LieCorr0Core.lieCorr0AMixPermQ -
        lc0TraceRF (I := I) (M := M) g gmU 3 LieCorr0Core.lieCorr0AMixPermQ) ≤
      Ct3 ^ 2 * u := by
    rw [trPair_sub_lip, reindex_jet_lip]
    exact htp3'
  have hd4 : lowJetSq (I := I) (M := M) g 1 (S4T - S4U) ≤
      2 * (K4 R * (pl2 * u) + K5 R * (pl2 * u)) := by
    rw [hdel4]
    have h1 : lowJetSq (I := I) (M := M) g 1
        (appCcRS (I := I) (M := M) g 2 5 3
          (lc0TraceRF (I := I) (M := M) g gmT 3 LieCorr0Core.lieCorr0AMixPermQ -
            lc0TraceRF (I := I) (M := M) g gmU 3 LieCorr0Core.lieCorr0AMixPermQ)
          S5T) ≤ K4 R * (pl2 * u) := by
      refine (happ4 _ S5T).trans ?_
      calc
        Ca4 * lowJetSq (I := I) (M := M) g 2
            (lc0TraceRF (I := I) (M := M) g gmT 3 LieCorr0Core.lieCorr0AMixPermQ -
              lc0TraceRF (I := I) (M := M) g gmU 3 LieCorr0Core.lieCorr0AMixPermQ) *
          lowJetSq (I := I) (M := M) g 1 S5T ≤
          Ca4 * (Ct3 ^ 2 * u) * (S5b R * pl2) := by
          exact mul_le_mul
            (mul_le_mul_of_nonneg_left htrd3 hCa4) hS5T1
            (jet_nonneg_lip (I := I) (M := M) (m := 1) g _)
            (mul_nonneg hCa4 (by positivity))
        _ = K4 R * (pl2 * u) := by simp only [K4]; ring
    have h2 : lowJetSq (I := I) (M := M) g 1
        (appCcRS (I := I) (M := M) g 2 5 3
          (lc0TraceRF (I := I) (M := M) g gmU 3 LieCorr0Core.lieCorr0AMixPermQ)
          (S5T - S5U)) ≤ K5 R * (pl2 * u) := by
      refine (happ4 _ _).trans ?_
      have htr := (trPair_jet_lip (I := I) (M := M) g gmU 3 2
        LieCorr0Core.lieCorr0AMixPermQ).le.trans htb3'.2
      calc
        Ca4 * lowJetSq (I := I) (M := M) g 2
            (lc0TraceRF (I := I) (M := M) g gmU 3 LieCorr0Core.lieCorr0AMixPermQ) *
          lowJetSq (I := I) (M := M) g 1 (S5T - S5U) ≤
          Ca4 * Bt3 ^ 2 * (M5 R * (pl2 * u)) := by
          exact mul_le_mul
            (mul_le_mul_of_nonneg_left htr hCa4) hd5
            (jet_nonneg_lip (I := I) (M := M) (m := 1) g _)
            (mul_nonneg hCa4 (sq_nonneg _))
        _ = K5 R * (pl2 * u) := by simp only [K5]; ring
    calc
      lowJetSq (I := I) (M := M) g 1 (_ + _) ≤
        2 * (lowJetSq (I := I) (M := M) g 1 _ +
          lowJetSq (I := I) (M := M) g 1 _) :=
        jet_add_lip (I := I) (M := M) g 1 _ _
      _ ≤ 2 * (K4 R * (pl2 * u) + K5 R * (pl2 * u)) := by
        linarith [h1, h2]
  -- level-3 difference
  have hdel3 : S3T - S3U =
      appCcRS (I := I) (M := M) g 2 3 6 (E3T - E3U) S4T +
        appCcRS (I := I) (M := M) g 2 3 6 E3U (S4T - S4U) := by
    rw [hS3Tdef, hS3Udef, appCcRS_sub_left, appCcRS_sub_right]
    module
  have hdelE3 : E3T - E3U =
      slotExtend (I := I) (M := M) g 2 5
        (slotExtend (I := I) (M := M) g 1 4
          (slotExtend (I := I) (M := M) g 0 3 (mcdT - mcdU))) := by
    rw [hE3Tdef, hE3Udef,
      show slotExtendIter (I := I) (M := M) g 0 3 3 mcdT =
        slotExtend (I := I) (M := M) g 2 5
          (slotExtend (I := I) (M := M) g 1 4
            (slotExtend (I := I) (M := M) g 0 3 mcdT)) from rfl,
      show slotExtendIter (I := I) (M := M) g 0 3 3 mcdU =
        slotExtend (I := I) (M := M) g 2 5
          (slotExtend (I := I) (M := M) g 1 4
            (slotExtend (I := I) (M := M) g 0 3 mcdU)) from rfl,
      slotExtend_sub, slotExtend_sub, slotExtend_sub]
  have hdE31 : lowJetSq (I := I) (M := M) g 1 (E3T - E3U) ≤
      fr ^ 3 * (2 * (B0m R) ^ 2 + 2 * (B1m R) ^ 2) * (pl2 * u) := by
    rw [hdelE3]
    calc
      lowJetSq (I := I) (M := M) g 1
          (slotExtend (I := I) (M := M) g 2 5
            (slotExtend (I := I) (M := M) g 1 4
              (slotExtend (I := I) (M := M) g 0 3 (mcdT - mcdU)))) ≤
        fr * lowJetSq (I := I) (M := M) g 1
          (slotExtend (I := I) (M := M) g 1 4
            (slotExtend (I := I) (M := M) g 0 3 (mcdT - mcdU))) :=
        slot_h1_lip (I := I) (M := M) g 2 5 _
      _ ≤ fr * (fr * lowJetSq (I := I) (M := M) g 1
          (slotExtend (I := I) (M := M) g 0 3 (mcdT - mcdU))) :=
        mul_le_mul_of_nonneg_left
          (slot_h1_lip (I := I) (M := M) g 1 4 _) hfr
      _ ≤ fr * (fr * (fr *
          lowJetSq (I := I) (M := M) g 1 (mcdT - mcdU))) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left
            (slot_h1_lip (I := I) (M := M) g 0 3 _) hfr) hfr
      _ ≤ fr * (fr * (fr * ((2 * (B0m R) ^ 2 + 2 * (B1m R) ^ 2) *
          (pl2 * u)))) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hmpd hfr) hfr) hfr
      _ = fr ^ 3 * (2 * (B0m R) ^ 2 + 2 * (B1m R) ^ 2) * (pl2 * u) := by
        ring
  have hd3 : lowJetSq (I := I) (M := M) g 1 (S3T - S3U) ≤
      2 * (K3 R * ((pl2 * pl2) * u) + K34 R * ((pl2 * pl2) * u)) := by
    rw [hdel3]
    have h1 : lowJetSq (I := I) (M := M) g 1
        (appCcRS (I := I) (M := M) g 2 3 6 (E3T - E3U) S4T) ≤
        K3 R * ((pl2 * pl2) * u) := by
      refine (happ3f (E3T - E3U) S4T).trans ?_
      calc
        Ca3f * lowJetSq (I := I) (M := M) g 1 (E3T - E3U) *
          lowJetSq (I := I) (M := M) g 2 S4T ≤
          Ca3f * (fr ^ 3 * (2 * (B0m R) ^ 2 + 2 * (B1m R) ^ 2) *
            (pl2 * u)) * (S4b R * pl2) := by
          exact mul_le_mul
            (mul_le_mul_of_nonneg_left hdE31 hCa3f) hS4T2
            (jet_nonneg_lip (I := I) (M := M) (m := 2) g _)
            (mul_nonneg hCa3f (by positivity))
        _ = K3 R * ((pl2 * pl2) * u) := by simp only [K3]; ring
    have h2 : lowJetSq (I := I) (M := M) g 1
        (appCcRS (I := I) (M := M) g 2 3 6 E3U (S4T - S4U)) ≤
        K34 R * ((pl2 * pl2) * u) := by
      refine (happ3 E3U _).trans ?_
      calc
        Ca3 * lowJetSq (I := I) (M := M) g 2 E3U *
          lowJetSq (I := I) (M := M) g 1 (S4T - S4U) ≤
          Ca3 * (fr ^ 3 * (Bm R) ^ 2 * 2 * pl2) *
            (2 * (K4 R * (pl2 * u) + K5 R * (pl2 * u))) := by
          exact mul_le_mul
            (mul_le_mul_of_nonneg_left hE3U2 hCa3) hd4
            (jet_nonneg_lip (I := I) (M := M) (m := 1) g _)
            (mul_nonneg hCa3 (by positivity))
        _ = Ca3 * (fr ^ 3 * (Bm R) ^ 2 * 2) *
            (2 * (K4 R + K5 R)) * ((pl2 * pl2) * u) := by ring
        _ = K34 R * ((pl2 * pl2) * u) := by simp only [K34]
    calc
      lowJetSq (I := I) (M := M) g 1 (_ + _) ≤
        2 * (lowJetSq (I := I) (M := M) g 1 _ +
          lowJetSq (I := I) (M := M) g 1 _) :=
        jet_add_lip (I := I) (M := M) g 1 _ _
      _ ≤ 2 * (K3 R * ((pl2 * pl2) * u) +
          K34 R * ((pl2 * pl2) * u)) := by
        linarith [h1, h2]
  -- level-2 difference
  have hdel2 : S2T - S2U =
      appCcRS (I := I) (M := M) g 2 6 4
          (lc0TraceRF (I := I) (M := M) g gmT 4 LieCorr0Core.lieCorr0AMixPerm1 -
            lc0TraceRF (I := I) (M := M) g gmU 4 LieCorr0Core.lieCorr0AMixPerm1)
          S3T +
        appCcRS (I := I) (M := M) g 2 6 4
          (lc0TraceRF (I := I) (M := M) g gmU 4 LieCorr0Core.lieCorr0AMixPerm1)
          (S3T - S3U) := by
    rw [hS2Tdef, hS2Udef, appCcRS_sub_left, appCcRS_sub_right]
    module
  have htrd4 : lowJetSq (I := I) (M := M) g 2
      (lc0TraceRF (I := I) (M := M) g gmT 4 LieCorr0Core.lieCorr0AMixPerm1 -
        lc0TraceRF (I := I) (M := M) g gmU 4 LieCorr0Core.lieCorr0AMixPerm1) ≤
      Ct4 ^ 2 * u := by
    rw [trPair_sub_lip, reindex_jet_lip]
    exact htp4'
  have hd2 : lowJetSq (I := I) (M := M) g 1 (S2T - S2U) ≤
      2 * (K2 R * ((pl2 * pl2) * u) + K23 R * ((pl2 * pl2) * u)) := by
    rw [hdel2]
    have h1 : lowJetSq (I := I) (M := M) g 1
        (appCcRS (I := I) (M := M) g 2 6 4
          (lc0TraceRF (I := I) (M := M) g gmT 4 LieCorr0Core.lieCorr0AMixPerm1 -
            lc0TraceRF (I := I) (M := M) g gmU 4 LieCorr0Core.lieCorr0AMixPerm1)
          S3T) ≤ K2 R * ((pl2 * pl2) * u) := by
      refine (happ2 _ S3T).trans ?_
      calc
        Ca2 * lowJetSq (I := I) (M := M) g 2
            (lc0TraceRF (I := I) (M := M) g gmT 4 LieCorr0Core.lieCorr0AMixPerm1 -
              lc0TraceRF (I := I) (M := M) g gmU 4 LieCorr0Core.lieCorr0AMixPerm1) *
          lowJetSq (I := I) (M := M) g 1 S3T ≤
          Ca2 * (Ct4 ^ 2 * u) * (S3b R * (pl2 * pl2)) := by
          exact mul_le_mul
            (mul_le_mul_of_nonneg_left htrd4 hCa2) hS3T1
            (jet_nonneg_lip (I := I) (M := M) (m := 1) g _)
            (mul_nonneg hCa2 (by positivity))
        _ = K2 R * ((pl2 * pl2) * u) := by simp only [K2]; ring
    have h2 : lowJetSq (I := I) (M := M) g 1
        (appCcRS (I := I) (M := M) g 2 6 4
          (lc0TraceRF (I := I) (M := M) g gmU 4 LieCorr0Core.lieCorr0AMixPerm1)
          (S3T - S3U)) ≤ K23 R * ((pl2 * pl2) * u) := by
      refine (happ2 _ _).trans ?_
      have htr := (trPair_jet_lip (I := I) (M := M) g gmU 4 2
        LieCorr0Core.lieCorr0AMixPerm1).le.trans htb4'.2
      calc
        Ca2 * lowJetSq (I := I) (M := M) g 2
            (lc0TraceRF (I := I) (M := M) g gmU 4 LieCorr0Core.lieCorr0AMixPerm1) *
          lowJetSq (I := I) (M := M) g 1 (S3T - S3U) ≤
          Ca2 * Bt4 ^ 2 * (2 * (K3 R * ((pl2 * pl2) * u) +
            K34 R * ((pl2 * pl2) * u))) := by
          exact mul_le_mul
            (mul_le_mul_of_nonneg_left htr hCa2) hd3
            (jet_nonneg_lip (I := I) (M := M) (m := 1) g _)
            (mul_nonneg hCa2 (sq_nonneg _))
        _ = K23 R * ((pl2 * pl2) * u) := by simp only [K23]; ring
    calc
      lowJetSq (I := I) (M := M) g 1 (_ + _) ≤
        2 * (lowJetSq (I := I) (M := M) g 1 _ +
          lowJetSq (I := I) (M := M) g 1 _) :=
        jet_add_lip (I := I) (M := M) g 1 _ _
      _ ≤ 2 * (K2 R * ((pl2 * pl2) * u) +
          K23 R * ((pl2 * pl2) * u)) := by
        linarith [h1, h2]
  -- level-1 (Half) difference
  have htrd2 : lowJetSq (I := I) (M := M) g 2
      (lc0TraceRF (I := I) (M := M) g gmT 2 σlast -
        lc0TraceRF (I := I) (M := M) g gmU 2 σlast) ≤
      Ct2 ^ 2 * u := by
    rw [trPair_sub_lip, reindex_jet_lip]
    exact htp2'
  have hdel1 : lc0AMixHalfRF (I := I) (M := M) g gmT g σlast -
      lc0AMixHalfRF (I := I) (M := M) g gmU g σlast =
      appCcRS (I := I) (M := M) g 2 4 2
          (lc0TraceRF (I := I) (M := M) g gmT 2 σlast -
            lc0TraceRF (I := I) (M := M) g gmU 2 σlast) S2T +
        appCcRS (I := I) (M := M) g 2 4 2
          (lc0TraceRF (I := I) (M := M) g gmU 2 σlast)
          (S2T - S2U) := by
    rw [hHalfT, hHalfU, appCcRS_sub_left, appCcRS_sub_right]
    module
  rw [hdel1]
  have h1 : lowJetSq (I := I) (M := M) g 1
      (appCcRS (I := I) (M := M) g 2 4 2
        (lc0TraceRF (I := I) (M := M) g gmT 2 σlast -
          lc0TraceRF (I := I) (M := M) g gmU 2 σlast) S2T) ≤
      K1 R * ((pl2 * pl2) * u) := by
    refine (happ1 _ S2T).trans ?_
    calc
      Ca1 * lowJetSq (I := I) (M := M) g 2
          (lc0TraceRF (I := I) (M := M) g gmT 2 σlast -
            lc0TraceRF (I := I) (M := M) g gmU 2 σlast) *
        lowJetSq (I := I) (M := M) g 1 S2T ≤
        Ca1 * (Ct2 ^ 2 * u) * (S2b R * (pl2 * pl2)) := by
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left htrd2 hCa1) hS2T1
          (jet_nonneg_lip (I := I) (M := M) (m := 1) g _)
          (mul_nonneg hCa1 (by positivity))
      _ = K1 R * ((pl2 * pl2) * u) := by simp only [K1]; ring
  have h2 : lowJetSq (I := I) (M := M) g 1
      (appCcRS (I := I) (M := M) g 2 4 2
        (lc0TraceRF (I := I) (M := M) g gmU 2 σlast)
        (S2T - S2U)) ≤
      K12 R * ((pl2 * pl2) * u) := by
    refine (happ1 _ _).trans ?_
    have htr := (trPair_jet_lip (I := I) (M := M) g gmU 2 2
      σlast).le.trans htb2'.2
    calc
      Ca1 * lowJetSq (I := I) (M := M) g 2
          (lc0TraceRF (I := I) (M := M) g gmU 2 σlast) *
        lowJetSq (I := I) (M := M) g 1 (S2T - S2U) ≤
        Ca1 * Bt2 ^ 2 * (2 * (K2 R * ((pl2 * pl2) * u) +
          K23 R * ((pl2 * pl2) * u))) := by
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left htr hCa1) hd2
          (jet_nonneg_lip (I := I) (M := M) (m := 1) g _)
          (mul_nonneg hCa1 (sq_nonneg _))
      _ = K12 R * ((pl2 * pl2) * u) := by simp only [K12]; ring
  calc
    lowJetSq (I := I) (M := M) g 1 (_ + _) ≤
      2 * (lowJetSq (I := I) (M := M) g 1 _ +
        lowJetSq (I := I) (M := M) g 1 _) :=
      jet_add_lip (I := I) (M := M) g 1 _ _
    _ ≤ 2 * (K1 R * ((pl2 * pl2) * u) + K12 R * ((pl2 * pl2) * u)) := by
      linarith [h1, h2]
    _ = B R * ((1 + A + A ^ 2) ^ 4 * (D2 ^ 2 + N ^ 2)) := by
      simp only [B, hpl2, hu]
      ring

set_option maxHeartbeats 1600000 in
set_option linter.unusedVariables false in
private theorem amix_pair_h1
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ : ℝ, ∃ B : ℝ → ℝ,
      0 < ρ ∧ (∀ R : ℝ, 0 ≤ R → 0 ≤ B R) ∧
      ∀ (T U : SmoothCcTensor g 0 2)
        (hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        (hU : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g U x u v =
            ccTensorBilin (I := I) g U x v u)
        {δ : ℝ} (hδ_le : δ ≤ 1 / 3) (hδ0 : 0 ≤ δ)
        (hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδU : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g U) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        (R A D2 N : ℝ), 0 ≤ R → 0 ≤ A → 0 ≤ D2 → 0 ≤ N →
        lowJetSq (I := I) (M := M) g 2 T ≤ R ^ 2 →
        lowJetSq (I := I) (M := M) g 2 U ≤ R ^ 2 →
        lowJetSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
        lowJetSq (I := I) (M := M) g 3 U ≤ A ^ 2 →
        lowJetSq (I := I) (M := M) g 2 (T - U) ≤ D2 ^ 2 →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U)‖ ≤ N →
        ∀ {s : ℝ}, s ∈ Set.Icc (0 : ℝ) 1 →
      lowJetSq (I := I) (M := M) g 1
          (lc0AMix (I := I) (M := M) g
              (realizedFam (I := I) g T 0 hδT hδZ s) g -
            lc0AMix (I := I) (M := M) g
              (realizedFam (I := I) g U 0 hδU hδZ s) g) ≤
        B R * ((1 + A + A ^ 2) ^ 4 * (D2 ^ 2 + N ^ 2)) := by
  obtain ⟨ρ, Bh, hρ, hBh, hhalf⟩ :=
    amixHalf_pair_h1 (I := I) (M := M) hDim g
  refine ⟨ρ, fun R => 16 * Bh R, hρ,
    fun R hR => by
      have := hBh R hR
      linarith, ?_⟩
  intro T U hT hU δ hδ_le hδ0 hδT hδU hδZ
    R A D2 N hR hA hD2 hN hT2 hU2 hT3 hU3 hTU2 hTn hUn hTUn s hs
  have hh1 := hhalf T U hT hU hδ_le hδ0 hδT hδU hδZ
    R A D2 N hR hA hD2 hN hT2 hU2 hT3 hU3 hTU2 hTn hUn hTUn hs
    LieCorr0Core.lieCorr0AMixPerm2
  have hh2 := hhalf T U hT hU hδ_le hδ0 hδT hδU hδZ
    R A D2 N hR hA hD2 hN hT2 hU2 hT3 hU3 hTU2 hTn hUn hTUn hs
    (lc0SwapPermRF * LieCorr0Core.lieCorr0AMixPerm2)
  have hX0 : 0 ≤ (1 + A + A ^ 2) ^ 4 * (D2 ^ 2 + N ^ 2) := by
    positivity
  rw [amix_refold_rf (I := I) (M := M) g
      (realizedFam (I := I) g T 0 hδT hδZ s) g,
    amix_refold_rf (I := I) (M := M) g
      (realizedFam (I := I) g U 0 hδU hδZ s) g]
  have hform :
      lc0AMixFormRF (I := I) (M := M) g
          (realizedFam (I := I) g T 0 hδT hδZ s) g -
        lc0AMixFormRF (I := I) (M := M) g
          (realizedFam (I := I) g U 0 hδU hδZ s) g =
      (2 : ℝ) •
        ((lc0AMixHalfRF (I := I) (M := M) g
            (realizedFam (I := I) g T 0 hδT hδZ s) g
              LieCorr0Core.lieCorr0AMixPerm2 -
          lc0AMixHalfRF (I := I) (M := M) g
            (realizedFam (I := I) g U 0 hδU hδZ s) g
              LieCorr0Core.lieCorr0AMixPerm2) +
        (lc0AMixHalfRF (I := I) (M := M) g
            (realizedFam (I := I) g T 0 hδT hδZ s) g
              (lc0SwapPermRF * LieCorr0Core.lieCorr0AMixPerm2) -
          lc0AMixHalfRF (I := I) (M := M) g
            (realizedFam (I := I) g U 0 hδU hδZ s) g
              (lc0SwapPermRF * LieCorr0Core.lieCorr0AMixPerm2))) := by
    simp only [lc0AMixFormRF]
    module
  rw [hform, jet_smul_lip]
  have hadd := jet_add_lip (I := I) (M := M) g 1
    (lc0AMixHalfRF (I := I) (M := M) g
        (realizedFam (I := I) g T 0 hδT hδZ s) g
          LieCorr0Core.lieCorr0AMixPerm2 -
      lc0AMixHalfRF (I := I) (M := M) g
        (realizedFam (I := I) g U 0 hδU hδZ s) g
          LieCorr0Core.lieCorr0AMixPerm2)
    (lc0AMixHalfRF (I := I) (M := M) g
        (realizedFam (I := I) g T 0 hδT hδZ s) g
          (lc0SwapPermRF * LieCorr0Core.lieCorr0AMixPerm2) -
      lc0AMixHalfRF (I := I) (M := M) g
        (realizedFam (I := I) g U 0 hδU hδZ s) g
          (lc0SwapPermRF * LieCorr0Core.lieCorr0AMixPerm2))
  have h4 : (2 : ℝ) ^ 2 = 4 := by norm_num
  calc
    (2 : ℝ) ^ 2 * lowJetSq (I := I) (M := M) g 1 (_ + _) ≤
      (2 : ℝ) ^ 2 * (2 * (lowJetSq (I := I) (M := M) g 1 _ +
        lowJetSq (I := I) (M := M) g 1 _)) :=
      mul_le_mul_of_nonneg_left hadd (by positivity)
    _ ≤ (2 : ℝ) ^ 2 * (2 *
        (Bh R * ((1 + A + A ^ 2) ^ 4 * (D2 ^ 2 + N ^ 2)) +
          Bh R * ((1 + A + A ^ 2) ^ 4 * (D2 ^ 2 + N ^ 2)))) := by
      have := add_le_add hh1 hh2
      nlinarith [this]
    _ = 16 * Bh R * ((1 + A + A ^ 2) ^ 4 * (D2 ^ 2 + N ^ 2)) := by
      ring




/-! ############################################################################
    ## Class 1 of the `C0` `H¹` five-class telescope: shared leaves.

    Everything below builds the two-state `H¹` modulus of
    `LowBaseInternal.ricciGoodLow` along the realized family.  This first block
    collects the jet-algebra leaves (subtraction folding, gradient transfer),
    the input symmetrizer, the two connection-insertion fields, the moving
    four-trace, the refold coefficient, and the `dagLowOp` moduli.
    ############################################################################ -/

private theorem jet_sub_lip
    (g : SmoothRiemannianMetric I M) {r s : ℕ} (m : ℕ)
    (S V : SmoothCcTensor g r s) :
    lowJetSq (I := I) (M := M) g m (S - V) ≤
      2 * (lowJetSq (I := I) (M := M) g m S +
        lowJetSq (I := I) (M := M) g m V) := by
  have hrw : S - V = S + (-1 : ℝ) • V := by module
  rw [hrw]
  calc
    lowJetSq (I := I) (M := M) g m (S + (-1 : ℝ) • V) ≤
        2 * (lowJetSq (I := I) (M := M) g m S +
          lowJetSq (I := I) (M := M) g m ((-1 : ℝ) • V)) :=
      jet_add_lip (I := I) (M := M) g m S ((-1 : ℝ) • V)
    _ = 2 * (lowJetSq (I := I) (M := M) g m S +
        lowJetSq (I := I) (M := M) g m V) := by
      rw [jet_smul_lip]; ring

private theorem grad_l2_sq_lip
    (g : SmoothRiemannianMetric I M) (r s i : ℕ)
    (S : SmoothCcTensor g r s) :
    ‖iteratedCovGrad (I := I) g r (s + 1) i
        (covGrad (I := I) (M := M) g r s S)‖ ^ 2 =
      ‖iteratedCovGrad (I := I) g r s (i + 1) S‖ ^ 2 := by
  rw [SmoothCcTensor.norm_def,
    tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs,
    SmoothCcTensor.norm_def,
    tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs]
  refine MeasureTheory.integral_congr_ae
    (Filter.Eventually.of_forall fun x => ?_)
  exact rfns_iteratedCovGrad_covGrad_comm_rs
    (I := I) (M := M) g r s i S x

/-- `H¹` gradient transfer: one covariant derivative costs one jet level. -/
private theorem grad_h1_le_h2_lip
    (g : SmoothRiemannianMetric I M) {r s : ℕ}
    (S : SmoothCcTensor g r s) :
    lowJetSq (I := I) (M := M) g 1
        (covGrad (I := I) (M := M) g r s S) ≤
      lowJetSq (I := I) (M := M) g 2 S := by
  have h0 := grad_l2_sq_lip (I := I) (M := M) g r s 0 S
  have h1 := grad_l2_sq_lip (I := I) (M := M) g r s 1 S
  unfold lowJetSq
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    Nat.reduceAdd] at h0 h1 ⊢
  rw [h0, h1]
  nlinarith [sq_nonneg ‖iteratedCovGrad (I := I) g r s 0 S‖,
    sq_nonneg ‖S‖]

/-- `H²` gradient transfer: one covariant derivative costs one jet level. -/
private theorem grad_h2_le_h3_lip
    (g : SmoothRiemannianMetric I M) {r s : ℕ}
    (S : SmoothCcTensor g r s) :
    lowJetSq (I := I) (M := M) g 2
        (covGrad (I := I) (M := M) g r s S) ≤
      lowJetSq (I := I) (M := M) g 3 S := by
  have h0 := grad_l2_sq_lip (I := I) (M := M) g r s 0 S
  have h1 := grad_l2_sq_lip (I := I) (M := M) g r s 1 S
  have h2 := grad_l2_sq_lip (I := I) (M := M) g r s 2 S
  unfold lowJetSq
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    Nat.reduceAdd] at h0 h1 h2 ⊢
  rw [h0, h1, h2]
  nlinarith [sq_nonneg ‖iteratedCovGrad (I := I) g r s 0 S‖,
    sq_nonneg ‖S‖]

/-! ### Layer A — the input symmetrizer at `H¹` -/

/-- `ccInputSymm` is linear, so it commutes with the two-state difference. -/
private theorem ccSymm_sub_lip
    (g : SmoothRiemannianMetric I M) (C D : SmoothCcTensor g 2 2) :
    ccInputSymm (I := I) (M := M) g C -
        ccInputSymm (I := I) (M := M) g D =
      ccInputSymm (I := I) (M := M) g (C - D) := by
  have hC : ccInputSymm (I := I) (M := M) g C =
      (1 / 2 : ℝ) • (C + appCcRS (I := I) (M := M) g 2 2 2 C
        (ccSlotSwapField (I := I) (M := M) g)) := rfl
  have hD : ccInputSymm (I := I) (M := M) g D =
      (1 / 2 : ℝ) • (D + appCcRS (I := I) (M := M) g 2 2 2 D
        (ccSlotSwapField (I := I) (M := M) g)) := rfl
  have hCD : ccInputSymm (I := I) (M := M) g (C - D) =
      (1 / 2 : ℝ) • ((C - D) + appCcRS (I := I) (M := M) g 2 2 2 (C - D)
        (ccSlotSwapField (I := I) (M := M) g)) := rfl
  rw [hC, hD, hCD, appCcRS_sub_left]
  module

/-- `H¹` size of the input symmetrizer: the swap field is a fixed background
tensor, so its `H²` jet is a constant and the moving factor is consumed at
`H¹`. -/
private theorem inputSymm_h1
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ C : SmoothCcTensor g 2 2,
        lowJetSq (I := I) (M := M) g 1
            (ccInputSymm (I := I) (M := M) g C) ≤
          K * lowJetSq (I := I) (M := M) g 1 C := by
  obtain ⟨Ca, hCa, happ⟩ :=
    app_h12_mul_lip (I := I) (M := M) hDim g 2 2 2
  have hKs : 0 ≤ lowJetSq (I := I) (M := M) g 2
      (ccSlotSwapField (I := I) (M := M) g) :=
    jet_nonneg_lip (I := I) (M := M) (m := 2) g _
  refine ⟨2 * (1 + Ca * lowJetSq (I := I) (M := M) g 2
    (ccSlotSwapField (I := I) (M := M) g)), by positivity, ?_⟩
  intro C
  have hC0 : 0 ≤ lowJetSq (I := I) (M := M) g 1 C :=
    jet_nonneg_lip (I := I) (M := M) (m := 1) g C
  have happ' :
      lowJetSq (I := I) (M := M) g 1
          (appCcRS (I := I) (M := M) g 2 2 2 C
            (ccSlotSwapField (I := I) (M := M) g)) ≤
        Ca * lowJetSq (I := I) (M := M) g 2
            (ccSlotSwapField (I := I) (M := M) g) *
          lowJetSq (I := I) (M := M) g 1 C := by
    have h := happ C (ccSlotSwapField (I := I) (M := M) g)
    calc
      lowJetSq (I := I) (M := M) g 1
          (appCcRS (I := I) (M := M) g 2 2 2 C
            (ccSlotSwapField (I := I) (M := M) g)) ≤
          Ca * lowJetSq (I := I) (M := M) g 1 C *
            lowJetSq (I := I) (M := M) g 2
              (ccSlotSwapField (I := I) (M := M) g) := h
      _ = Ca * lowJetSq (I := I) (M := M) g 2
            (ccSlotSwapField (I := I) (M := M) g) *
          lowJetSq (I := I) (M := M) g 1 C := by ring
  have hsum :
      lowJetSq (I := I) (M := M) g 1
          (C + appCcRS (I := I) (M := M) g 2 2 2 C
            (ccSlotSwapField (I := I) (M := M) g)) ≤
        2 * (1 + Ca * lowJetSq (I := I) (M := M) g 2
            (ccSlotSwapField (I := I) (M := M) g)) *
          lowJetSq (I := I) (M := M) g 1 C := by
    refine (jet_add_lip (I := I) (M := M) g 1 C _).trans ?_
    linarith [happ']
  have hnn : 0 ≤ lowJetSq (I := I) (M := M) g 1
      (C + appCcRS (I := I) (M := M) g 2 2 2 C
        (ccSlotSwapField (I := I) (M := M) g)) :=
    jet_nonneg_lip (I := I) (M := M) (m := 1) g _
  have hform : ccInputSymm (I := I) (M := M) g C =
      (1 / 2 : ℝ) • (C + appCcRS (I := I) (M := M) g 2 2 2 C
        (ccSlotSwapField (I := I) (M := M) g)) := rfl
  rw [hform, jet_smul_lip]
  linarith [hsum, hnn]

/-! ### Layer B — the two connection-insertion fields -/

set_option linter.unusedVariables false in
/-- Single-state `H²` size of the mixed connection-difference section. -/
private theorem connSec_bdd_h2
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ B : ℝ → ℝ,
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B R) ∧
      ∀ (gT : SmoothRiemannianMetric I M)
        (T : SmoothCcTensor g 0 2)
        (hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        (hTtie : ∀ (x : M) (u v : TangentSpace I x),
          gT.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g T x u v)
        {δ : ℝ} (hδ_le : δ ≤ 1 / 3) (hδ0 : 0 ≤ δ)
        (hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        (R A : ℝ), 0 ≤ R → 0 ≤ A →
        lowJetSq (I := I) (M := M) g 2 T ≤ R ^ 2 →
        lowJetSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
      lowJetSq (I := I) (M := M) g 2
          (connDiffSection (I := I) gT g) ≤ (B R * A) ^ 2 := by
  obtain ⟨Bs, hBs, hw⟩ := wXi_self_tame (I := I) (M := M) hDim g
  refine ⟨Bs, hBs, ?_⟩
  intro gT T hT hTtie δ hδ_le hδ0 hδT hδZ R A hR hA hT2 hT3
  rw [connSec_self_h2 (I := I) (M := M) g gT]
  exact hw gT T hT hTtie hδ_le hδ0 hδT hδZ R A hR hA hT2 hT3

set_option linter.unusedVariables false in
/-- Single-state `H²` size of the outer connection-insertion field. -/
private theorem connIns_bdd_h2
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ B : ℝ → ℝ,
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B R) ∧
      ∀ (gT : SmoothRiemannianMetric I M)
        (T : SmoothCcTensor g 0 2)
        (hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        (hTtie : ∀ (x : M) (u v : TangentSpace I x),
          gT.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g T x u v)
        {δ : ℝ} (hδ_le : δ ≤ 1 / 3) (hδ0 : 0 ≤ δ)
        (hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        (R A : ℝ), 0 ≤ R → 0 ≤ A →
        lowJetSq (I := I) (M := M) g 2 T ≤ R ^ 2 →
        lowJetSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
      lowJetSq (I := I) (M := M) g 2
          (connDiffContrInsertionField (I := I) g gT) ≤
        (Module.finrank ℝ E : ℝ) ^ 2 * (B R * A) ^ 2 := by
  obtain ⟨Bs, hBs, hsec⟩ := connSec_bdd_h2 (I := I) (M := M) hDim g
  refine ⟨Bs, hBs, ?_⟩
  intro gT T hT hTtie δ hδ_le hδ0 hδT hδZ R A hR hA hT2 hT3
  have hfr : (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ) := Nat.cast_nonneg _
  have hbase := hsec gT T hT hTtie hδ_le hδ0 hδT hδZ R A hR hA hT2 hT3
  rw [connDiffContrInsertionField_eq_reindex_slotExtend_two
      (I := I) (M := M) g gT, reindex_jet_lip]
  calc
    lowJetSq (I := I) (M := M) g 2
        (slotExtend (I := I) (M := M) g 2 3
          (slotExtend (I := I) (M := M) g 1 2
            (connDiffSection (I := I) gT g))) ≤
      (Module.finrank ℝ E : ℝ) * lowJetSq (I := I) (M := M) g 2
        (slotExtend (I := I) (M := M) g 1 2
          (connDiffSection (I := I) gT g)) :=
      slot_h2_lip (I := I) (M := M) g 2 3 _
    _ ≤ (Module.finrank ℝ E : ℝ) *
        ((Module.finrank ℝ E : ℝ) * lowJetSq (I := I) (M := M) g 2
          (connDiffSection (I := I) gT g)) :=
      mul_le_mul_of_nonneg_left
        (slot_h2_lip (I := I) (M := M) g 1 2 _) hfr
    _ ≤ (Module.finrank ℝ E : ℝ) *
        ((Module.finrank ℝ E : ℝ) * (Bs R * A) ^ 2) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hbase hfr) hfr
    _ = (Module.finrank ℝ E : ℝ) ^ 2 * (Bs R * A) ^ 2 := by ring

set_option linter.unusedVariables false in
/-- `H¹` two-state modulus of the outer connection-insertion field. -/
private theorem connIns_pair_h1
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀0 : 0 ≤ δ₀) (hδ₀ : δ₀ < 1) :
    ∃ B0 B1 : ℝ → ℝ,
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B0 R) ∧
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B1 R) ∧
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
        {δT δU : ℝ}
        (hδT_le : δT ≤ δ₀) (hδT0 : 0 ≤ δT)
        (hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δT)
        (hδU_le : δU ≤ δ₀) (hδU0 : 0 ≤ δU)
        (hδU : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g U) δU)
        (R A D2 : ℝ), 0 ≤ R → 0 ≤ A → 0 ≤ D2 →
        lowJetSq (I := I) (M := M) g 2 U ≤ R ^ 2 →
        lowJetSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
        lowJetSq (I := I) (M := M) g 2 (T - U) ≤ D2 ^ 2 →
      lowJetSq (I := I) (M := M) g 1
          (connDiffContrInsertionField (I := I) g gT -
            connDiffContrInsertionField (I := I) g gU) ≤
        (Module.finrank ℝ E : ℝ) ^ 2 *
          (B0 R * D2 + B1 R * A * D2) ^ 2 := by
  obtain ⟨B0, B1, hB0, hB1, hpair⟩ :=
    connSec_pair_h1 (I := I) (M := M) hDim g hδ₀0 hδ₀
  refine ⟨B0, B1, hB0, hB1, ?_⟩
  intro gT gU T U hT hU hTtie hUtie
    δT δU hδT_le hδT0 hδT hδU_le hδU0 hδU R A D2 hR hA hD2 hU2 hT3 hTU2
  have hfr : (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ) := Nat.cast_nonneg _
  have hp := hpair gT gU T U hT hU hTtie hUtie
    hδT_le hδT0 hδT hδU_le hδU0 hδU R A D2 hR hA hD2 hU2 hT3 hTU2
  have hsub :
      connDiffContrInsertionField (I := I) g gT -
          connDiffContrInsertionField (I := I) g gU =
        reindexCoeffGen (I := I) (M := M) g 3 4
          (slotExtend (I := I) (M := M) g 2 3
            (slotExtend (I := I) (M := M) g 1 2
              (connDiffSection (I := I) gT g -
                connDiffSection (I := I) gU g)))
          coreInPerm201 := by
    rw [connDiffContrInsertionField_eq_reindex_slotExtend_two
        (I := I) (M := M) g gT,
      connDiffContrInsertionField_eq_reindex_slotExtend_two
        (I := I) (M := M) g gU,
      slotExtend_sub, slotExtend_sub, reindex_sub_lip]
  rw [hsub, reindex_jet_lip]
  calc
    lowJetSq (I := I) (M := M) g 1
        (slotExtend (I := I) (M := M) g 2 3
          (slotExtend (I := I) (M := M) g 1 2
            (connDiffSection (I := I) gT g -
              connDiffSection (I := I) gU g))) ≤
      (Module.finrank ℝ E : ℝ) * lowJetSq (I := I) (M := M) g 1
        (slotExtend (I := I) (M := M) g 1 2
          (connDiffSection (I := I) gT g -
            connDiffSection (I := I) gU g)) :=
      slot_h1_lip (I := I) (M := M) g 2 3 _
    _ ≤ (Module.finrank ℝ E : ℝ) *
        ((Module.finrank ℝ E : ℝ) * lowJetSq (I := I) (M := M) g 1
          (connDiffSection (I := I) gT g -
            connDiffSection (I := I) gU g)) :=
      mul_le_mul_of_nonneg_left
        (slot_h1_lip (I := I) (M := M) g 1 2 _) hfr
    _ ≤ (Module.finrank ℝ E : ℝ) *
        ((Module.finrank ℝ E : ℝ) *
          (B0 R * D2 + B1 R * A * D2) ^ 2) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hp hfr) hfr
    _ = (Module.finrank ℝ E : ℝ) ^ 2 *
        (B0 R * D2 + B1 R * A * D2) ^ 2 := by ring

set_option linter.unusedVariables false in
/-- Single-state `H²` size of the inner connection-insertion field. -/
private theorem connInn_bdd_h2
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ B : ℝ → ℝ,
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B R) ∧
      ∀ (gT : SmoothRiemannianMetric I M)
        (T : SmoothCcTensor g 0 2)
        (hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        (hTtie : ∀ (x : M) (u v : TangentSpace I x),
          gT.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g T x u v)
        {δ : ℝ} (hδ_le : δ ≤ 1 / 3) (hδ0 : 0 ≤ δ)
        (hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        (R A : ℝ), 0 ≤ R → 0 ≤ A →
        lowJetSq (I := I) (M := M) g 2 T ≤ R ^ 2 →
        lowJetSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
      lowJetSq (I := I) (M := M) g 2
          (connDiffContrInsertionInnerField (I := I) g gT) ≤
        (Module.finrank ℝ E : ℝ) * (B R * A) ^ 2 := by
  obtain ⟨Bs, hBs, hsec⟩ := connSec_bdd_h2 (I := I) (M := M) hDim g
  refine ⟨Bs, hBs, ?_⟩
  intro gT T hT hTtie δ hδ_le hδ0 hδT hδZ R A hR hA hT2 hT3
  have hfr : (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ) := Nat.cast_nonneg _
  have hbase := hsec gT T hT hTtie hδ_le hδ0 hδT hδZ R A hR hA hT2 hT3
  rw [connDiffContrInsertionInnerField_eq_reindex_slotExtend
      (I := I) (M := M) g gT, reindex_jet_lip]
  exact (slot_h2_lip (I := I) (M := M) g 1 2 _).trans
    (mul_le_mul_of_nonneg_left hbase hfr)

set_option linter.unusedVariables false in
/-- `H¹` two-state modulus of the inner connection-insertion field. -/
private theorem connInn_pair_h1
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀0 : 0 ≤ δ₀) (hδ₀ : δ₀ < 1) :
    ∃ B0 B1 : ℝ → ℝ,
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B0 R) ∧
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B1 R) ∧
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
        {δT δU : ℝ}
        (hδT_le : δT ≤ δ₀) (hδT0 : 0 ≤ δT)
        (hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δT)
        (hδU_le : δU ≤ δ₀) (hδU0 : 0 ≤ δU)
        (hδU : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g U) δU)
        (R A D2 : ℝ), 0 ≤ R → 0 ≤ A → 0 ≤ D2 →
        lowJetSq (I := I) (M := M) g 2 U ≤ R ^ 2 →
        lowJetSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
        lowJetSq (I := I) (M := M) g 2 (T - U) ≤ D2 ^ 2 →
      lowJetSq (I := I) (M := M) g 1
          (connDiffContrInsertionInnerField (I := I) g gT -
            connDiffContrInsertionInnerField (I := I) g gU) ≤
        (Module.finrank ℝ E : ℝ) * (B0 R * D2 + B1 R * A * D2) ^ 2 := by
  obtain ⟨B0, B1, hB0, hB1, hpair⟩ :=
    connSec_pair_h1 (I := I) (M := M) hDim g hδ₀0 hδ₀
  refine ⟨B0, B1, hB0, hB1, ?_⟩
  intro gT gU T U hT hU hTtie hUtie
    δT δU hδT_le hδT0 hδT hδU_le hδU0 hδU R A D2 hR hA hD2 hU2 hT3 hTU2
  have hfr : (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ) := Nat.cast_nonneg _
  have hp := hpair gT gU T U hT hU hTtie hUtie
    hδT_le hδT0 hδT hδU_le hδU0 hδU R A D2 hR hA hD2 hU2 hT3 hTU2
  have hsub :
      connDiffContrInsertionInnerField (I := I) g gT -
          connDiffContrInsertionInnerField (I := I) g gU =
        reindexCoeffGen (I := I) (M := M) g 2 3
          (slotExtend (I := I) (M := M) g 1 2
            (connDiffSection (I := I) gT g -
              connDiffSection (I := I) gU g))
          innerCoreInPerm10 := by
    rw [connDiffContrInsertionInnerField_eq_reindex_slotExtend
        (I := I) (M := M) g gT,
      connDiffContrInsertionInnerField_eq_reindex_slotExtend
        (I := I) (M := M) g gU,
      slotExtend_sub, reindex_sub_lip]
  rw [hsub, reindex_jet_lip]
  exact (slot_h1_lip (I := I) (M := M) g 1 2 _).trans
    (mul_le_mul_of_nonneg_left hp hfr)

/-! ### Layer C — the moving four-trace -/

/-- The pure Ricci principal coefficient is the moving two-slot pure trace. -/
private theorem pureCoeff_eq_lip
    (g gm : SmoothRiemannianMetric I M) :
    ricciArmPrincipalCoeffPure (I := I) (M := M) g gm =
      pureTrace (I := I) (M := M) g gm 2 := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [ricciArmPrincipalCoeffPure_toSection, pureTrace_toSection]

/-- Jet bookkeeping for the reindexed four-trace combination. -/
private theorem fourtrace_jet_le
    (g : SmoothRiemannianMetric I M) (F : SmoothCcTensor g 4 2) :
    lowJetSq (I := I) (M := M) g 2
        (((1 : ℝ) / 2) •
          (reindexCoeffGen (I := I) (M := M) g 4 2 F fourTraceArgPerm0231
              + reindexCoeffGen (I := I) (M := M) g 4 2 F fourTraceArgPerm0321
              - F
              - reindexCoeffGen (I := I) (M := M) g 4 2 F
                  fourTraceArgPerm2301)) ≤
      22 * lowJetSq (I := I) (M := M) g 2 F := by
  have hJ0 : 0 ≤ lowJetSq (I := I) (M := M) g 2 F :=
    jet_nonneg_lip (I := I) (M := M) (m := 2) g F
  have hr1 : lowJetSq (I := I) (M := M) g 2
      (reindexCoeffGen (I := I) (M := M) g 4 2 F fourTraceArgPerm0231) =
      lowJetSq (I := I) (M := M) g 2 F :=
    reindex_jet_lip (I := I) (M := M) g F fourTraceArgPerm0231
  have hr2 : lowJetSq (I := I) (M := M) g 2
      (reindexCoeffGen (I := I) (M := M) g 4 2 F fourTraceArgPerm0321) =
      lowJetSq (I := I) (M := M) g 2 F :=
    reindex_jet_lip (I := I) (M := M) g F fourTraceArgPerm0321
  have hr3 : lowJetSq (I := I) (M := M) g 2
      (reindexCoeffGen (I := I) (M := M) g 4 2 F fourTraceArgPerm2301) =
      lowJetSq (I := I) (M := M) g 2 F :=
    reindex_jet_lip (I := I) (M := M) g F fourTraceArgPerm2301
  have e1 := jet_add_lip (I := I) (M := M) g 2
    (reindexCoeffGen (I := I) (M := M) g 4 2 F fourTraceArgPerm0231)
    (reindexCoeffGen (I := I) (M := M) g 4 2 F fourTraceArgPerm0321)
  have e2 := jet_sub_lip (I := I) (M := M) g 2
    (reindexCoeffGen (I := I) (M := M) g 4 2 F fourTraceArgPerm0231 +
      reindexCoeffGen (I := I) (M := M) g 4 2 F fourTraceArgPerm0321) F
  have e3 := jet_sub_lip (I := I) (M := M) g 2
    (reindexCoeffGen (I := I) (M := M) g 4 2 F fourTraceArgPerm0231 +
        reindexCoeffGen (I := I) (M := M) g 4 2 F fourTraceArgPerm0321 - F)
    (reindexCoeffGen (I := I) (M := M) g 4 2 F fourTraceArgPerm2301)
  rw [jet_smul_lip]
  rw [hr1, hr2] at e1
  rw [hr3] at e3
  linarith [e1, e2, e3, hJ0]

set_option linter.unusedVariables false in
/-- Single-state `H²` size of the moving four-trace on the spectral ball. -/
private theorem fourtrace_bdd_h2
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ B : ℝ, 0 < ρ ∧ 0 ≤ B ∧
      ∀ (T : SmoothCcTensor g 0 2)
        (gT : SmoothRiemannianMetric I M),
        (∀ (y : M) (v w : TangentSpace I y),
          gT.inner y v w =
            g.inner y v w + ccTensorBilinSymm (I := I) g T y v w) →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρ →
        lowJetSq (I := I) (M := M) g 2
            (ricciCometricFourTraceCastG0 (I := I) g gT) ≤ 22 * B ^ 2 := by
  obtain ⟨ρ, B, hρ, hB, hbdd⟩ :=
    LowBaseInternal.trace2_h2_bdd (I := I) (M := M) hDim g
  refine ⟨ρ, B, hρ, hB, ?_⟩
  intro T gT htie hTn
  have hF : lowJetSq (I := I) (M := M) g 2
      (ricciArmPrincipalCoeffPure (I := I) (M := M) g gT) ≤ B ^ 2 := by
    rw [pureCoeff_eq_lip]
    exact hbdd T gT htie hTn
  rw [ricciCometricFourTraceCastG0_eq_reindex_combination (I := I) (M := M) g gT]
  refine (fourtrace_jet_le (I := I) (M := M) g _).trans ?_
  linarith [hF]

set_option linter.unusedVariables false in
/-- Two-state `H²` modulus of the moving four-trace in the spectral `Hˢ`
currency. -/
private theorem fourtrace_pair_h2
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
          22 * (C * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
            (T - U)‖) ^ 2 := by
  obtain ⟨ρ, C, hρ, hC, hlip⟩ :=
    LowBaseInternal.trace2_pair_h2 (I := I) (M := M) hDim g
  refine ⟨ρ, C, hρ, hC, ?_⟩
  intro T U gT gU hTtie hUtie hTn hUn
  have hF : lowJetSq (I := I) (M := M) g 2
      (ricciArmPrincipalCoeffPure (I := I) (M := M) g gT -
        ricciArmPrincipalCoeffPure (I := I) (M := M) g gU) ≤
      (C * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U)‖) ^ 2 := by
    rw [pureCoeff_eq_lip, pureCoeff_eq_lip]
    exact hlip T U gT gU hTtie hUtie hTn hUn
  have hsub :
      ricciCometricFourTraceCastG0 (I := I) g gT -
          ricciCometricFourTraceCastG0 (I := I) g gU =
        ((1 : ℝ) / 2) •
          (reindexCoeffGen (I := I) (M := M) g 4 2
                (ricciArmPrincipalCoeffPure (I := I) (M := M) g gT -
                  ricciArmPrincipalCoeffPure (I := I) (M := M) g gU)
                fourTraceArgPerm0231
              + reindexCoeffGen (I := I) (M := M) g 4 2
                  (ricciArmPrincipalCoeffPure (I := I) (M := M) g gT -
                    ricciArmPrincipalCoeffPure (I := I) (M := M) g gU)
                  fourTraceArgPerm0321
              - (ricciArmPrincipalCoeffPure (I := I) (M := M) g gT -
                  ricciArmPrincipalCoeffPure (I := I) (M := M) g gU)
              - reindexCoeffGen (I := I) (M := M) g 4 2
                  (ricciArmPrincipalCoeffPure (I := I) (M := M) g gT -
                    ricciArmPrincipalCoeffPure (I := I) (M := M) g gU)
                  fourTraceArgPerm2301) := by
    rw [ricciCometricFourTraceCastG0_eq_reindex_combination
        (I := I) (M := M) g gT,
      ricciCometricFourTraceCastG0_eq_reindex_combination
        (I := I) (M := M) g gU,
      reindex_sub_lip, reindex_sub_lip, reindex_sub_lip]
    module
  rw [hsub]
  refine (fourtrace_jet_le (I := I) (M := M) g _).trans ?_
  linarith [hF]

/-! ### Layer D — the refold coefficient -/

/-- `refoldKernelContractionMonomialField` is linear in its kernel slot. -/
private theorem refold_sub_lip
    (g : SmoothRiemannianMetric I M)
    (G H : SmoothCcTensor g 0 4) (σ : Equiv.Perm (Fin 4)) :
    refoldKernelContractionMonomialField (I := I) (M := M) g g (G - H) σ =
      refoldKernelContractionMonomialField (I := I) (M := M) g g G σ -
        refoldKernelContractionMonomialField (I := I) (M := M) g g H σ := by
  classical
  have hiter : ∀ D : SmoothCcTensor g 0 4,
      slotExtendIter (I := I) (M := M) g 0 4 2 D =
        slotExtend (I := I) (M := M) g 1 5
          (slotExtend (I := I) (M := M) g 0 4 D) := fun _ => rfl
  simp only [refoldKernelContractionMonomialField_eq_mvPairTraceRefold, hiter]
  rw [dom_sub_lip, slotExtend_sub, slotExtend_sub, rsperm_sub_lip,
    appCcRS_sub_right]

/-- `H¹` size of the refold coefficient in terms of its kernel slot. -/
private theorem refold_h1_lip
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (G : SmoothCcTensor g 0 4) (σ : Equiv.Perm (Fin 4)),
        lowJetSq (I := I) (M := M) g 1
            (refoldKernelContractionMonomialField
              (I := I) (M := M) g g G σ) ≤
          K * lowJetSq (I := I) (M := M) g 1 G := by
  classical
  obtain ⟨C, hC, happ⟩ := app_h21_mul_lip (I := I) (M := M) hDim g 2 6 2
  have hKm : 0 ≤ lowJetSq (I := I) (M := M) g 2
      (mvPairTraceOp (I := I) (M := M) g g) :=
    jet_nonneg_lip (I := I) (M := M) (m := 2) g _
  have hfr : (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ) := Nat.cast_nonneg _
  refine ⟨C * lowJetSq (I := I) (M := M) g 2
      (mvPairTraceOp (I := I) (M := M) g g) *
      ((Module.finrank ℝ E : ℝ) * (Module.finrank ℝ E : ℝ)),
    by positivity, ?_⟩
  intro G σ
  have hiter : ∀ D : SmoothCcTensor g 0 4,
      slotExtendIter (I := I) (M := M) g 0 4 2 D =
        slotExtend (I := I) (M := M) g 1 5
          (slotExtend (I := I) (M := M) g 0 4 D) := fun _ => rfl
  simp only [refoldKernelContractionMonomialField_eq_mvPairTraceRefold, hiter]
  refine (happ _ _).trans ?_
  have hjet : lowJetSq (I := I) (M := M) g 1
      (rsDomDomCongrSection (I := I) (M := M) g 2 6 sigmaE
        (slotExtend (I := I) (M := M) g 1 5
          (slotExtend (I := I) (M := M) g 0 4
            (domDomCongrSection (I := I) g
              (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3 * σ)
              G)))) ≤
      (Module.finrank ℝ E : ℝ) *
        ((Module.finrank ℝ E : ℝ) * lowJetSq (I := I) (M := M) g 1 G) := by
    rw [rsperm_h1_lip]
    calc
      lowJetSq (I := I) (M := M) g 1
          (slotExtend (I := I) (M := M) g 1 5
            (slotExtend (I := I) (M := M) g 0 4
              (domDomCongrSection (I := I) g
                (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3 * σ)
                G))) ≤
        (Module.finrank ℝ E : ℝ) * lowJetSq (I := I) (M := M) g 1
          (slotExtend (I := I) (M := M) g 0 4
            (domDomCongrSection (I := I) g
              (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3 * σ)
              G)) :=
        slot_h1_lip (I := I) (M := M) g 1 5 _
      _ ≤ (Module.finrank ℝ E : ℝ) *
          ((Module.finrank ℝ E : ℝ) * lowJetSq (I := I) (M := M) g 1
            (domDomCongrSection (I := I) g
              (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3 * σ)
              G)) :=
        mul_le_mul_of_nonneg_left (slot_h1_lip (I := I) (M := M) g 0 4 _) hfr
      _ = (Module.finrank ℝ E : ℝ) *
          ((Module.finrank ℝ E : ℝ) * lowJetSq (I := I) (M := M) g 1 G) := by
        rw [dom_h1_lip]
  calc
    C * lowJetSq (I := I) (M := M) g 2
          (mvPairTraceOp (I := I) (M := M) g g) *
        lowJetSq (I := I) (M := M) g 1
          (rsDomDomCongrSection (I := I) (M := M) g 2 6 sigmaE
            (slotExtend (I := I) (M := M) g 1 5
              (slotExtend (I := I) (M := M) g 0 4
                (domDomCongrSection (I := I) g
                  (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3 * σ)
                  G)))) ≤
        C * lowJetSq (I := I) (M := M) g 2
            (mvPairTraceOp (I := I) (M := M) g g) *
          ((Module.finrank ℝ E : ℝ) *
            ((Module.finrank ℝ E : ℝ) *
              lowJetSq (I := I) (M := M) g 1 G)) :=
      mul_le_mul_of_nonneg_left hjet (mul_nonneg hC hKm)
    _ = C * lowJetSq (I := I) (M := M) g 2
          (mvPairTraceOp (I := I) (M := M) g g) *
        ((Module.finrank ℝ E : ℝ) * (Module.finrank ℝ E : ℝ)) *
        lowJetSq (I := I) (M := M) g 1 G := by ring

/-- `H²` size of the refold coefficient in terms of its kernel slot. -/
private theorem refold_h2_lip
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (G : SmoothCcTensor g 0 4) (σ : Equiv.Perm (Fin 4)),
        lowJetSq (I := I) (M := M) g 2
            (refoldKernelContractionMonomialField
              (I := I) (M := M) g g G σ) ≤
          K * lowJetSq (I := I) (M := M) g 2 G := by
  classical
  obtain ⟨C, hC, happ⟩ := app_h2_mul_lip (I := I) (M := M) hDim g 2 6 2
  have hKm : 0 ≤ lowJetSq (I := I) (M := M) g 2
      (mvPairTraceOp (I := I) (M := M) g g) :=
    jet_nonneg_lip (I := I) (M := M) (m := 2) g _
  have hfr : (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ) := Nat.cast_nonneg _
  refine ⟨C * lowJetSq (I := I) (M := M) g 2
      (mvPairTraceOp (I := I) (M := M) g g) *
      ((Module.finrank ℝ E : ℝ) * (Module.finrank ℝ E : ℝ)),
    by positivity, ?_⟩
  intro G σ
  have hiter : ∀ D : SmoothCcTensor g 0 4,
      slotExtendIter (I := I) (M := M) g 0 4 2 D =
        slotExtend (I := I) (M := M) g 1 5
          (slotExtend (I := I) (M := M) g 0 4 D) := fun _ => rfl
  simp only [refoldKernelContractionMonomialField_eq_mvPairTraceRefold, hiter]
  refine (happ _ _).trans ?_
  have hjet : lowJetSq (I := I) (M := M) g 2
      (rsDomDomCongrSection (I := I) (M := M) g 2 6 sigmaE
        (slotExtend (I := I) (M := M) g 1 5
          (slotExtend (I := I) (M := M) g 0 4
            (domDomCongrSection (I := I) g
              (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3 * σ)
              G)))) ≤
      (Module.finrank ℝ E : ℝ) *
        ((Module.finrank ℝ E : ℝ) * lowJetSq (I := I) (M := M) g 2 G) := by
    rw [rsperm_h2_lip]
    calc
      lowJetSq (I := I) (M := M) g 2
          (slotExtend (I := I) (M := M) g 1 5
            (slotExtend (I := I) (M := M) g 0 4
              (domDomCongrSection (I := I) g
                (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3 * σ)
                G))) ≤
        (Module.finrank ℝ E : ℝ) * lowJetSq (I := I) (M := M) g 2
          (slotExtend (I := I) (M := M) g 0 4
            (domDomCongrSection (I := I) g
              (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3 * σ)
              G)) :=
        slot_h2_lip (I := I) (M := M) g 1 5 _
      _ ≤ (Module.finrank ℝ E : ℝ) *
          ((Module.finrank ℝ E : ℝ) * lowJetSq (I := I) (M := M) g 2
            (domDomCongrSection (I := I) g
              (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3 * σ)
              G)) :=
        mul_le_mul_of_nonneg_left (slot_h2_lip (I := I) (M := M) g 0 4 _) hfr
      _ = (Module.finrank ℝ E : ℝ) *
          ((Module.finrank ℝ E : ℝ) * lowJetSq (I := I) (M := M) g 2 G) := by
        rw [dom_h2_lip]
  calc
    C * lowJetSq (I := I) (M := M) g 2
          (mvPairTraceOp (I := I) (M := M) g g) *
        lowJetSq (I := I) (M := M) g 2
          (rsDomDomCongrSection (I := I) (M := M) g 2 6 sigmaE
            (slotExtend (I := I) (M := M) g 1 5
              (slotExtend (I := I) (M := M) g 0 4
                (domDomCongrSection (I := I) g
                  (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3 * σ)
                  G)))) ≤
        C * lowJetSq (I := I) (M := M) g 2
            (mvPairTraceOp (I := I) (M := M) g g) *
          ((Module.finrank ℝ E : ℝ) *
            ((Module.finrank ℝ E : ℝ) *
              lowJetSq (I := I) (M := M) g 2 G)) :=
      mul_le_mul_of_nonneg_left hjet (mul_nonneg hC hKm)
    _ = C * lowJetSq (I := I) (M := M) g 2
          (mvPairTraceOp (I := I) (M := M) g g) *
        ((Module.finrank ℝ E : ℝ) * (Module.finrank ℝ E : ℝ)) *
        lowJetSq (I := I) (M := M) g 2 G := by ring

/-! ### Layer E — the `dagLowOp` moduli -/

set_option linter.unusedVariables false in
/-- Single-state `H²` size of the lower Ricci derivative coefficient,
imported from the already-verified action-level bound. -/
private theorem dagLow_bdd_h2
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (gm : SmoothRiemannianMetric I M)
        (P : SmoothCcTensor g 0 2)
        (hP : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g P x u v =
            ccTensorBilin (I := I) g P x v u)
        (htie : ∀ (x : M) (u v : TangentSpace I x),
          gm.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g P x u v)
        {δ : ℝ} (hδ_le : δ ≤ 1 / 3) (hδ0 : 0 ≤ δ)
        (hδP : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g P) δ)
        (A : ℝ), 0 ≤ A →
        lowJetSq (I := I) (M := M) g 3 P ≤ A ^ 2 →
      lowJetSq (I := I) (M := M) g 2
          (LowBaseInternal.dagLowOp (I := I) (M := M) g gm) ≤
        K * (1 + A ^ 2) := by
  obtain ⟨K, hK, hdag⟩ :=
    dagLow_h2_rf (I := I) (M := M) hDim g
      (δ₀ := (1 : ℝ) / 3) (by norm_num) (by norm_num)
  refine ⟨K, hK, ?_⟩
  intro gm P hP htie δ hδ_le hδ0 hδP A hA hP3
  refine (hdag gm P hP htie hδ_le hδ0 hδP).trans ?_
  exact mul_le_mul_of_nonneg_left (by linarith) hK

set_option linter.unusedVariables false in
/-- `H¹` two-state modulus of the lower Ricci derivative coefficient, in the
spectral `Hˢ` currency (the only moving factor is `connLowOp`). -/
private theorem dagLow_pair_h1
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
        lowJetSq (I := I) (M := M) g 1
            (LowBaseInternal.dagLowOp (I := I) (M := M) g gT -
              LowBaseInternal.dagLowOp (I := I) (M := M) g gU) ≤
          C * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U)‖ ^ 2 := by
  obtain ⟨Ca, hCa, happ⟩ :=
    app_h21_mul_lip (I := I) (M := M) hDim g 3 4 4
  obtain ⟨ρc, Cc, hρc, hCc, hcl⟩ :=
    LowBaseInternal.connLow_pair_h2 (I := I) (M := M) hDim g
  have hKp0 : 0 ≤ lowJetSq (I := I) (M := M) g 2
      (permCoeff (I := I) (M := M) g LowBaseInternal.daPermA) :=
    jet_nonneg_lip (I := I) (M := M) (m := 2) g _
  refine ⟨ρc, Ca * lowJetSq (I := I) (M := M) g 2
      (permCoeff (I := I) (M := M) g LowBaseInternal.daPermA) * Cc ^ 2,
    hρc, by positivity, ?_⟩
  intro T U gT gU hTtie hUtie hTn hUn
  have hformT : LowBaseInternal.dagLowOp (I := I) (M := M) g gT =
      appCcRS (I := I) (M := M) g 3 4 4
        (permCoeff (I := I) (M := M) g LowBaseInternal.daPermA)
        (covGrad (I := I) (M := M) g 3 3
          (LowBaseInternal.connLowOp (I := I) (M := M) g gT)) := rfl
  have hformU : LowBaseInternal.dagLowOp (I := I) (M := M) g gU =
      appCcRS (I := I) (M := M) g 3 4 4
        (permCoeff (I := I) (M := M) g LowBaseInternal.daPermA)
        (covGrad (I := I) (M := M) g 3 3
          (LowBaseInternal.connLowOp (I := I) (M := M) g gU)) := rfl
  have hsub :
      LowBaseInternal.dagLowOp (I := I) (M := M) g gT -
          LowBaseInternal.dagLowOp (I := I) (M := M) g gU =
        appCcRS (I := I) (M := M) g 3 4 4
          (permCoeff (I := I) (M := M) g LowBaseInternal.daPermA)
          (covGrad (I := I) (M := M) g 3 3
            (LowBaseInternal.connLowOp (I := I) (M := M) g gT -
              LowBaseInternal.connLowOp (I := I) (M := M) g gU)) := by
    rw [hformT, hformU, covGrad_sub, appCcRS_sub_right]
  have hg : lowJetSq (I := I) (M := M) g 1
      (covGrad (I := I) (M := M) g 3 3
        (LowBaseInternal.connLowOp (I := I) (M := M) g gT -
          LowBaseInternal.connLowOp (I := I) (M := M) g gU)) ≤
      (Cc * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U)‖) ^ 2 :=
    (grad_h1_le_h2_lip (I := I) (M := M) g _).trans
      (hcl T U gT gU hTtie hUtie hTn hUn)
  rw [hsub]
  refine (happ _ _).trans ?_
  calc
    Ca * lowJetSq (I := I) (M := M) g 2
          (permCoeff (I := I) (M := M) g LowBaseInternal.daPermA) *
        lowJetSq (I := I) (M := M) g 1
          (covGrad (I := I) (M := M) g 3 3
            (LowBaseInternal.connLowOp (I := I) (M := M) g gT -
              LowBaseInternal.connLowOp (I := I) (M := M) g gU)) ≤
        Ca * lowJetSq (I := I) (M := M) g 2
            (permCoeff (I := I) (M := M) g LowBaseInternal.daPermA) *
          (Cc * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U)‖) ^ 2 :=
      mul_le_mul_of_nonneg_left hg (mul_nonneg hCa hKp0)
    _ = Ca * lowJetSq (I := I) (M := M) g 2
          (permCoeff (I := I) (M := M) g LowBaseInternal.daPermA) * Cc ^ 2 *
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U)‖ ^ 2 := by ring

/-! ### Layer F — the quadratic (`AA`) Ricci arm -/

private def aaP3201 : Equiv.Perm (Fin 4) :=
  ⟨![3, 2, 0, 1], ![2, 3, 1, 0], by decide, by decide⟩

private def aaP2301 : Equiv.Perm (Fin 4) :=
  ⟨![2, 3, 0, 1], ![2, 3, 0, 1], by decide, by decide⟩

private def aaP3102 : Equiv.Perm (Fin 4) :=
  ⟨![3, 1, 0, 2], ![2, 1, 3, 0], by decide, by decide⟩

private def aaP1302 : Equiv.Perm (Fin 4) :=
  ⟨![1, 3, 0, 2], ![2, 0, 3, 1], by decide, by decide⟩

private def aaP1203 : Equiv.Perm (Fin 4) :=
  ⟨![1, 2, 0, 3], ![2, 0, 1, 3], by decide, by decide⟩

private def aaP2103 : Equiv.Perm (Fin 4) :=
  ⟨![2, 1, 0, 3], ![2, 1, 0, 3], by decide, by decide⟩

private def aaP102 : Equiv.Perm (Fin 3) :=
  ⟨![1, 0, 2], ![1, 0, 2], by decide, by decide⟩

private def aaP120 : Equiv.Perm (Fin 3) :=
  ⟨![1, 2, 0], ![2, 0, 1], by decide, by decide⟩

/-- Permuted inner connection-insertion factor of a quadratic Ricci block. -/
private noncomputable def aaInn
    (g gm : SmoothRiemannianMetric I M) (ρ : Equiv.Perm (Fin 3)) :
    SmoothCcTensor g 2 3 :=
  appCcRS (I := I) (M := M) g 2 3 3
    (permCoeff (I := I) (M := M) g ρ)
    (connDiffContrInsertionInnerField (I := I) g gm)

/-- Generic quadratic Ricci block: a frozen slot permutation applied to the
product of the outer connection-insertion field with an inner factor. -/
private noncomputable def aaBlk
    (g gm : SmoothRiemannianMetric I M) (pm : Equiv.Perm (Fin 4))
    (Z : SmoothCcTensor g 2 3) : SmoothCcTensor g 2 4 :=
  appCcRS (I := I) (M := M) g 2 4 4
    (permCoeff (I := I) (M := M) g pm)
    (appCcRS (I := I) (M := M) g 2 3 4
      (connDiffContrInsertionField (I := I) g gm) Z)

set_option maxHeartbeats 1600000 in
/-- The six quadratic blocks of the order-zero Ricci kernel. -/
private theorem aaKer_eq_lip (g gm : SmoothRiemannianMetric I M) :
    ricciAAKer (I := I) (M := M) g gm =
      aaBlk (I := I) (M := M) g gm aaP3201
          (aaInn (I := I) (M := M) g gm aaP102) +
        reindexCoeffGen (I := I) (M := M) g 2 4
          (aaBlk (I := I) (M := M) g gm aaP2301
            (aaInn (I := I) (M := M) g gm aaP102)) innerCoreInPerm10 +
        aaBlk (I := I) (M := M) g gm aaP3102
          (aaInn (I := I) (M := M) g gm aaP120) +
        reindexCoeffGen (I := I) (M := M) g 2 4
          (aaBlk (I := I) (M := M) g gm aaP1302
            (connDiffContrInsertionInnerField (I := I) g gm))
          innerCoreInPerm10 +
        aaBlk (I := I) (M := M) g gm aaP1203
          (connDiffContrInsertionInnerField (I := I) g gm) +
        reindexCoeffGen (I := I) (M := M) g 2 4
          (aaBlk (I := I) (M := M) g gm aaP2103
            (aaInn (I := I) (M := M) g gm aaP120)) innerCoreInPerm10 :=
  rfl

/-- Uniform `H²` size of the frozen slot permutations occurring in the
quadratic Ricci kernel. -/
private noncomputable def aaPK (g : SmoothRiemannianMetric I M) : ℝ :=
  lowJetSq (I := I) (M := M) g 2 (permCoeff (I := I) (M := M) g aaP3201) +
    lowJetSq (I := I) (M := M) g 2 (permCoeff (I := I) (M := M) g aaP2301) +
    lowJetSq (I := I) (M := M) g 2 (permCoeff (I := I) (M := M) g aaP3102) +
    lowJetSq (I := I) (M := M) g 2 (permCoeff (I := I) (M := M) g aaP1302) +
    lowJetSq (I := I) (M := M) g 2 (permCoeff (I := I) (M := M) g aaP1203) +
    lowJetSq (I := I) (M := M) g 2 (permCoeff (I := I) (M := M) g aaP2103) +
    lowJetSq (I := I) (M := M) g 2 (permCoeff (I := I) (M := M) g aaP102) +
    lowJetSq (I := I) (M := M) g 2 (permCoeff (I := I) (M := M) g aaP120)

private theorem aaPK_nonneg (g : SmoothRiemannianMetric I M) :
    0 ≤ aaPK (I := I) (M := M) g := by
  unfold aaPK
  have h1 : 0 ≤ lowJetSq (I := I) (M := M) g 2
    (permCoeff (I := I) (M := M) g aaP3201) :=
    jet_nonneg_lip (I := I) (M := M) (m := 2) g _
  have h2 : 0 ≤ lowJetSq (I := I) (M := M) g 2
    (permCoeff (I := I) (M := M) g aaP2301) :=
    jet_nonneg_lip (I := I) (M := M) (m := 2) g _
  have h3 : 0 ≤ lowJetSq (I := I) (M := M) g 2
    (permCoeff (I := I) (M := M) g aaP3102) :=
    jet_nonneg_lip (I := I) (M := M) (m := 2) g _
  have h4 : 0 ≤ lowJetSq (I := I) (M := M) g 2
    (permCoeff (I := I) (M := M) g aaP1302) :=
    jet_nonneg_lip (I := I) (M := M) (m := 2) g _
  have h5 : 0 ≤ lowJetSq (I := I) (M := M) g 2
    (permCoeff (I := I) (M := M) g aaP1203) :=
    jet_nonneg_lip (I := I) (M := M) (m := 2) g _
  have h6 : 0 ≤ lowJetSq (I := I) (M := M) g 2
    (permCoeff (I := I) (M := M) g aaP2103) :=
    jet_nonneg_lip (I := I) (M := M) (m := 2) g _
  have h7 : 0 ≤ lowJetSq (I := I) (M := M) g 2
    (permCoeff (I := I) (M := M) g aaP102) :=
    jet_nonneg_lip (I := I) (M := M) (m := 2) g _
  have h8 : 0 ≤ lowJetSq (I := I) (M := M) g 2
    (permCoeff (I := I) (M := M) g aaP120) :=
    jet_nonneg_lip (I := I) (M := M) (m := 2) g _
  linarith

private theorem aaPK_ge4 (g : SmoothRiemannianMetric I M)
    (pm : Equiv.Perm (Fin 4))
    (hpm : pm = aaP3201 ∨ pm = aaP2301 ∨ pm = aaP3102 ∨ pm = aaP1302 ∨
      pm = aaP1203 ∨ pm = aaP2103) :
    lowJetSq (I := I) (M := M) g 2 (permCoeff (I := I) (M := M) g pm) ≤
      aaPK (I := I) (M := M) g := by
  have h1 : 0 ≤ lowJetSq (I := I) (M := M) g 2
    (permCoeff (I := I) (M := M) g aaP3201) :=
    jet_nonneg_lip (I := I) (M := M) (m := 2) g _
  have h2 : 0 ≤ lowJetSq (I := I) (M := M) g 2
    (permCoeff (I := I) (M := M) g aaP2301) :=
    jet_nonneg_lip (I := I) (M := M) (m := 2) g _
  have h3 : 0 ≤ lowJetSq (I := I) (M := M) g 2
    (permCoeff (I := I) (M := M) g aaP3102) :=
    jet_nonneg_lip (I := I) (M := M) (m := 2) g _
  have h4 : 0 ≤ lowJetSq (I := I) (M := M) g 2
    (permCoeff (I := I) (M := M) g aaP1302) :=
    jet_nonneg_lip (I := I) (M := M) (m := 2) g _
  have h5 : 0 ≤ lowJetSq (I := I) (M := M) g 2
    (permCoeff (I := I) (M := M) g aaP1203) :=
    jet_nonneg_lip (I := I) (M := M) (m := 2) g _
  have h6 : 0 ≤ lowJetSq (I := I) (M := M) g 2
    (permCoeff (I := I) (M := M) g aaP2103) :=
    jet_nonneg_lip (I := I) (M := M) (m := 2) g _
  have h7 : 0 ≤ lowJetSq (I := I) (M := M) g 2
    (permCoeff (I := I) (M := M) g aaP102) :=
    jet_nonneg_lip (I := I) (M := M) (m := 2) g _
  have h8 : 0 ≤ lowJetSq (I := I) (M := M) g 2
    (permCoeff (I := I) (M := M) g aaP120) :=
    jet_nonneg_lip (I := I) (M := M) (m := 2) g _
  unfold aaPK
  rcases hpm with rfl | rfl | rfl | rfl | rfl | rfl <;> linarith

private theorem aaPK_ge3 (g : SmoothRiemannianMetric I M)
    (ρ : Equiv.Perm (Fin 3)) (hρ : ρ = aaP102 ∨ ρ = aaP120) :
    lowJetSq (I := I) (M := M) g 2 (permCoeff (I := I) (M := M) g ρ) ≤
      aaPK (I := I) (M := M) g := by
  have h1 : 0 ≤ lowJetSq (I := I) (M := M) g 2
    (permCoeff (I := I) (M := M) g aaP3201) :=
    jet_nonneg_lip (I := I) (M := M) (m := 2) g _
  have h2 : 0 ≤ lowJetSq (I := I) (M := M) g 2
    (permCoeff (I := I) (M := M) g aaP2301) :=
    jet_nonneg_lip (I := I) (M := M) (m := 2) g _
  have h3 : 0 ≤ lowJetSq (I := I) (M := M) g 2
    (permCoeff (I := I) (M := M) g aaP3102) :=
    jet_nonneg_lip (I := I) (M := M) (m := 2) g _
  have h4 : 0 ≤ lowJetSq (I := I) (M := M) g 2
    (permCoeff (I := I) (M := M) g aaP1302) :=
    jet_nonneg_lip (I := I) (M := M) (m := 2) g _
  have h5 : 0 ≤ lowJetSq (I := I) (M := M) g 2
    (permCoeff (I := I) (M := M) g aaP1203) :=
    jet_nonneg_lip (I := I) (M := M) (m := 2) g _
  have h6 : 0 ≤ lowJetSq (I := I) (M := M) g 2
    (permCoeff (I := I) (M := M) g aaP2103) :=
    jet_nonneg_lip (I := I) (M := M) (m := 2) g _
  have h7 : 0 ≤ lowJetSq (I := I) (M := M) g 2
    (permCoeff (I := I) (M := M) g aaP102) :=
    jet_nonneg_lip (I := I) (M := M) (m := 2) g _
  have h8 : 0 ≤ lowJetSq (I := I) (M := M) g 2
    (permCoeff (I := I) (M := M) g aaP120) :=
    jet_nonneg_lip (I := I) (M := M) (m := 2) g _
  unfold aaPK
  rcases hρ with rfl | rfl <;> linarith

/-- Generic single-state `H²` size of a quadratic Ricci block. -/
private theorem aaBlk_h2
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (gm : SmoothRiemannianMetric I M) (pm : Equiv.Perm (Fin 4))
        (Z : SmoothCcTensor g 2 3),
        lowJetSq (I := I) (M := M) g 2
            (aaBlk (I := I) (M := M) g gm pm Z) ≤
          C * (lowJetSq (I := I) (M := M) g 2
              (permCoeff (I := I) (M := M) g pm) *
            (lowJetSq (I := I) (M := M) g 2
                (connDiffContrInsertionField (I := I) g gm) *
              lowJetSq (I := I) (M := M) g 2 Z)) := by
  obtain ⟨C244, hC244, h244⟩ := app_h2_mul_lip (I := I) (M := M) hDim g 2 4 4
  obtain ⟨C234, hC234, h234⟩ := app_h2_mul_lip (I := I) (M := M) hDim g 2 3 4
  refine ⟨C244 * C234, mul_nonneg hC244 hC234, ?_⟩
  intro gm pm Z
  have hp0 : 0 ≤ lowJetSq (I := I) (M := M) g 2
      (permCoeff (I := I) (M := M) g pm) :=
    jet_nonneg_lip (I := I) (M := M) (m := 2) g _
  have hform : aaBlk (I := I) (M := M) g gm pm Z =
      appCcRS (I := I) (M := M) g 2 4 4
        (permCoeff (I := I) (M := M) g pm)
        (appCcRS (I := I) (M := M) g 2 3 4
          (connDiffContrInsertionField (I := I) g gm) Z) := rfl
  rw [hform]
  refine (h244 (permCoeff (I := I) (M := M) g pm) _).trans ?_
  calc
    C244 * lowJetSq (I := I) (M := M) g 2
          (permCoeff (I := I) (M := M) g pm) *
        lowJetSq (I := I) (M := M) g 2
          (appCcRS (I := I) (M := M) g 2 3 4
            (connDiffContrInsertionField (I := I) g gm) Z) ≤
        C244 * lowJetSq (I := I) (M := M) g 2
            (permCoeff (I := I) (M := M) g pm) *
          (C234 * lowJetSq (I := I) (M := M) g 2
              (connDiffContrInsertionField (I := I) g gm) *
            lowJetSq (I := I) (M := M) g 2 Z) :=
      mul_le_mul_of_nonneg_left
        (h234 (connDiffContrInsertionField (I := I) g gm) Z)
        (mul_nonneg hC244 hp0)
    _ = C244 * C234 * (lowJetSq (I := I) (M := M) g 2
          (permCoeff (I := I) (M := M) g pm) *
        (lowJetSq (I := I) (M := M) g 2
            (connDiffContrInsertionField (I := I) g gm) *
          lowJetSq (I := I) (M := M) g 2 Z)) := by ring

/-- Generic two-state `H¹` modulus of a quadratic Ricci block: both connection
factors are consumed at `J1` on the difference side and at `J2` on the frozen
side. -/
private theorem aaBlk_pair_h1
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (gT gU : SmoothRiemannianMetric I M) (pm : Equiv.Perm (Fin 4))
        (ZT ZU : SmoothCcTensor g 2 3),
        lowJetSq (I := I) (M := M) g 1
            (aaBlk (I := I) (M := M) g gT pm ZT -
              aaBlk (I := I) (M := M) g gU pm ZU) ≤
          C * (lowJetSq (I := I) (M := M) g 2
              (permCoeff (I := I) (M := M) g pm) *
            (lowJetSq (I := I) (M := M) g 1
                (connDiffContrInsertionField (I := I) g gT -
                  connDiffContrInsertionField (I := I) g gU) *
                lowJetSq (I := I) (M := M) g 2 ZT +
              lowJetSq (I := I) (M := M) g 2
                  (connDiffContrInsertionField (I := I) g gU) *
                lowJetSq (I := I) (M := M) g 1 (ZT - ZU))) := by
  obtain ⟨Ca, hCa, hout⟩ := app_h21_mul_lip (I := I) (M := M) hDim g 2 4 4
  obtain ⟨Cf, hCf, hleft⟩ := app_h12_mul_lip (I := I) (M := M) hDim g 2 3 4
  obtain ⟨Cb, hCb, hright⟩ := app_h21_mul_lip (I := I) (M := M) hDim g 2 3 4
  refine ⟨2 * Ca * (Cf + Cb), by positivity, ?_⟩
  intro gT gU pm ZT ZU
  have hp0 : 0 ≤ lowJetSq (I := I) (M := M) g 2
      (permCoeff (I := I) (M := M) g pm) :=
    jet_nonneg_lip (I := I) (M := M) (m := 2) g _
  have ha0 : 0 ≤ lowJetSq (I := I) (M := M) g 1
        (connDiffContrInsertionField (I := I) g gT -
          connDiffContrInsertionField (I := I) g gU) *
      lowJetSq (I := I) (M := M) g 2 ZT :=
    mul_nonneg (jet_nonneg_lip (I := I) (M := M) (m := 1) g _)
      (jet_nonneg_lip (I := I) (M := M) (m := 2) g _)
  have hb0 : 0 ≤ lowJetSq (I := I) (M := M) g 2
        (connDiffContrInsertionField (I := I) g gU) *
      lowJetSq (I := I) (M := M) g 1 (ZT - ZU) :=
    mul_nonneg (jet_nonneg_lip (I := I) (M := M) (m := 2) g _)
      (jet_nonneg_lip (I := I) (M := M) (m := 1) g _)
  have hformT : aaBlk (I := I) (M := M) g gT pm ZT =
      appCcRS (I := I) (M := M) g 2 4 4
        (permCoeff (I := I) (M := M) g pm)
        (appCcRS (I := I) (M := M) g 2 3 4
          (connDiffContrInsertionField (I := I) g gT) ZT) := rfl
  have hformU : aaBlk (I := I) (M := M) g gU pm ZU =
      appCcRS (I := I) (M := M) g 2 4 4
        (permCoeff (I := I) (M := M) g pm)
        (appCcRS (I := I) (M := M) g 2 3 4
          (connDiffContrInsertionField (I := I) g gU) ZU) := rfl
  have hinner : appCcRS (I := I) (M := M) g 2 3 4
        (connDiffContrInsertionField (I := I) g gT -
          connDiffContrInsertionField (I := I) g gU) ZT +
      appCcRS (I := I) (M := M) g 2 3 4
        (connDiffContrInsertionField (I := I) g gU) (ZT - ZU) =
      appCcRS (I := I) (M := M) g 2 3 4
          (connDiffContrInsertionField (I := I) g gT) ZT -
        appCcRS (I := I) (M := M) g 2 3 4
          (connDiffContrInsertionField (I := I) g gU) ZU := by
    rw [appCcRS_sub_left, appCcRS_sub_right]
    module
  have hsub : aaBlk (I := I) (M := M) g gT pm ZT -
        aaBlk (I := I) (M := M) g gU pm ZU =
      appCcRS (I := I) (M := M) g 2 4 4
        (permCoeff (I := I) (M := M) g pm)
        (appCcRS (I := I) (M := M) g 2 3 4
            (connDiffContrInsertionField (I := I) g gT -
              connDiffContrInsertionField (I := I) g gU) ZT +
          appCcRS (I := I) (M := M) g 2 3 4
            (connDiffContrInsertionField (I := I) g gU) (ZT - ZU)) := by
    rw [hformT, hformU, hinner, appCcRS_sub_right]
  rw [hsub]
  refine (hout _ _).trans ?_
  have h1 : lowJetSq (I := I) (M := M) g 1
      (appCcRS (I := I) (M := M) g 2 3 4
        (connDiffContrInsertionField (I := I) g gT -
          connDiffContrInsertionField (I := I) g gU) ZT) ≤
      Cf * (lowJetSq (I := I) (M := M) g 1
          (connDiffContrInsertionField (I := I) g gT -
            connDiffContrInsertionField (I := I) g gU) *
        lowJetSq (I := I) (M := M) g 2 ZT) := by
    have h := hleft (connDiffContrInsertionField (I := I) g gT -
      connDiffContrInsertionField (I := I) g gU) ZT
    linarith [h]
  have h2 : lowJetSq (I := I) (M := M) g 1
      (appCcRS (I := I) (M := M) g 2 3 4
        (connDiffContrInsertionField (I := I) g gU) (ZT - ZU)) ≤
      Cb * (lowJetSq (I := I) (M := M) g 2
          (connDiffContrInsertionField (I := I) g gU) *
        lowJetSq (I := I) (M := M) g 1 (ZT - ZU)) := by
    have h := hright (connDiffContrInsertionField (I := I) g gU) (ZT - ZU)
    linarith [h]
  have hY : lowJetSq (I := I) (M := M) g 1
      (appCcRS (I := I) (M := M) g 2 3 4
          (connDiffContrInsertionField (I := I) g gT -
            connDiffContrInsertionField (I := I) g gU) ZT +
        appCcRS (I := I) (M := M) g 2 3 4
          (connDiffContrInsertionField (I := I) g gU) (ZT - ZU)) ≤
      2 * (Cf * (lowJetSq (I := I) (M := M) g 1
            (connDiffContrInsertionField (I := I) g gT -
              connDiffContrInsertionField (I := I) g gU) *
          lowJetSq (I := I) (M := M) g 2 ZT) +
        Cb * (lowJetSq (I := I) (M := M) g 2
            (connDiffContrInsertionField (I := I) g gU) *
          lowJetSq (I := I) (M := M) g 1 (ZT - ZU))) := by
    refine (jet_add_lip (I := I) (M := M) g 1 _ _).trans ?_
    linarith [h1, h2]
  have hstep := mul_le_mul_of_nonneg_left hY (mul_nonneg hCa hp0)
  nlinarith [hstep,
    mul_nonneg (mul_nonneg (mul_nonneg hCa hp0) hCb) ha0,
    mul_nonneg (mul_nonneg (mul_nonneg hCa hp0) hCf) hb0]

set_option maxHeartbeats 1600000 in
set_option linter.unusedVariables false in
/-- Single-state `H²` size of the quadratic Ricci kernel. -/
private theorem aaKer_bdd_h2
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ B : ℝ → ℝ,
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B R) ∧
      ∀ (gT : SmoothRiemannianMetric I M)
        (T : SmoothCcTensor g 0 2)
        (hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        (hTtie : ∀ (x : M) (u v : TangentSpace I x),
          gT.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g T x u v)
        {δ : ℝ} (hδ_le : δ ≤ 1 / 3) (hδ0 : 0 ≤ δ)
        (hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        (R A : ℝ), 0 ≤ R → 0 ≤ A →
        lowJetSq (I := I) (M := M) g 2 T ≤ R ^ 2 →
        lowJetSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
      lowJetSq (I := I) (M := M) g 2
          (ricciAAKer (I := I) (M := M) g gT) ≤
        B R * (1 + A + A ^ 2) ^ 4 := by
  obtain ⟨Cblk, hCblk, hblk⟩ := aaBlk_h2 (I := I) (M := M) hDim g
  obtain ⟨C233, hC233, h233⟩ := app_h2_mul_lip (I := I) (M := M) hDim g 2 3 3
  obtain ⟨Bs, hBs, hci⟩ := connIns_bdd_h2 (I := I) (M := M) hDim g
  obtain ⟨Bn, hBn, hcn⟩ := connInn_bdd_h2 (I := I) (M := M) hDim g
  have hfr : (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ) := Nat.cast_nonneg _
  have hPK : 0 ≤ aaPK (I := I) (M := M) g := aaPK_nonneg (I := I) (M := M) g
  have hone : (0 : ℝ) ≤ 1 + C233 * aaPK (I := I) (M := M) g := by
    have := mul_nonneg hC233 hPK; linarith
  let B : ℝ → ℝ := fun R =>
    94 * Cblk * (aaPK (I := I) (M := M) g *
      (((Module.finrank ℝ E : ℝ) ^ 2 * Bs R ^ 2) *
        ((1 + C233 * aaPK (I := I) (M := M) g) *
          ((Module.finrank ℝ E : ℝ) * Bn R ^ 2))))
  have hB0 : ∀ R : ℝ, 0 ≤ R → 0 ≤ B R := by
    intro R hR
    have e1 : (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ) ^ 2 * Bs R ^ 2 := by positivity
    have e2 : (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ) * Bn R ^ 2 := by positivity
    simp only [B]
    exact mul_nonneg (mul_nonneg (by norm_num) hCblk)
      (mul_nonneg hPK (mul_nonneg e1 (mul_nonneg hone e2)))
  refine ⟨B, hB0, ?_⟩
  intro gT T hT hTtie δ hδ_le hδ0 hδT hδZ R A hR hA hT2 hT3
  set pl2 : ℝ := (1 + A + A ^ 2) ^ 2 with hpl2
  have hbase : (1 : ℝ) ≤ 1 + A + A ^ 2 := by nlinarith [hA, sq_nonneg A]
  have hpl21 : (1 : ℝ) ≤ pl2 := by
    rw [hpl2]
    calc (1 : ℝ) = 1 ^ 2 := by norm_num
      _ ≤ (1 + A + A ^ 2) ^ 2 := pow_le_pow_left₀ zero_le_one hbase 2
  have hpl20 : (0 : ℝ) ≤ pl2 := le_trans zero_le_one hpl21
  have hplA2 : A ^ 2 ≤ pl2 := by
    rw [hpl2]
    nlinarith [hA, sq_nonneg A, mul_nonneg hA hA,
      mul_nonneg (mul_nonneg hA hA) hA]
  set CI2 : ℝ := (Module.finrank ℝ E : ℝ) ^ 2 * Bs R ^ 2 * pl2 with hCI2
  set VN : ℝ := (Module.finrank ℝ E : ℝ) * Bn R ^ 2 * pl2 with hVN
  set ZB : ℝ := (1 + C233 * aaPK (I := I) (M := M) g) * VN with hZB
  have hVN0 : 0 ≤ VN := by
    rw [hVN]
    exact mul_nonneg (by positivity) hpl20
  have hCI20 : 0 ≤ CI2 := by
    rw [hCI2]
    exact mul_nonneg (by positivity) hpl20
  have hci2T : lowJetSq (I := I) (M := M) g 2
      (connDiffContrInsertionField (I := I) g gT) ≤ CI2 := by
    refine (hci gT T hT hTtie hδ_le hδ0 hδT hδZ R A hR hA hT2 hT3).trans ?_
    rw [hCI2]
    have hb : (Bs R * A) ^ 2 = Bs R ^ 2 * A ^ 2 := by ring
    rw [hb]
    have hnn : (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ) ^ 2 * Bs R ^ 2 := by
      positivity
    nlinarith [hplA2, hnn]
  have hcnbase : lowJetSq (I := I) (M := M) g 2
      (connDiffContrInsertionInnerField (I := I) g gT) ≤ VN := by
    refine (hcn gT T hT hTtie hδ_le hδ0 hδT hδZ R A hR hA hT2 hT3).trans ?_
    rw [hVN]
    have hb : (Bn R * A) ^ 2 = Bn R ^ 2 * A ^ 2 := by ring
    rw [hb]
    have hnn : (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ) * Bn R ^ 2 := by positivity
    nlinarith [hplA2, hnn]
  have hprodPK : 0 ≤ C233 * aaPK (I := I) (M := M) g * VN :=
    mul_nonneg (mul_nonneg hC233 hPK) hVN0
  have hZdir : lowJetSq (I := I) (M := M) g 2
      (connDiffContrInsertionInnerField (I := I) g gT) ≤ ZB := by
    rw [hZB]
    linarith [hcnbase, hprodPK]
  have hZinn : ∀ ρ : Equiv.Perm (Fin 3), (ρ = aaP102 ∨ ρ = aaP120) →
      lowJetSq (I := I) (M := M) g 2
        (aaInn (I := I) (M := M) g gT ρ) ≤ ZB := by
    intro ρ hρ
    have hpm := aaPK_ge3 (I := I) (M := M) g ρ hρ
    have hp0 : 0 ≤ lowJetSq (I := I) (M := M) g 2
        (permCoeff (I := I) (M := M) g ρ) :=
      jet_nonneg_lip (I := I) (M := M) (m := 2) g _
    have hform : aaInn (I := I) (M := M) g gT ρ =
        appCcRS (I := I) (M := M) g 2 3 3
          (permCoeff (I := I) (M := M) g ρ)
          (connDiffContrInsertionInnerField (I := I) g gT) := rfl
    rw [hform]
    refine (h233 (permCoeff (I := I) (M := M) g ρ) _).trans ?_
    have hstep : C233 * lowJetSq (I := I) (M := M) g 2
          (permCoeff (I := I) (M := M) g ρ) *
        lowJetSq (I := I) (M := M) g 2
          (connDiffContrInsertionInnerField (I := I) g gT) ≤
        C233 * aaPK (I := I) (M := M) g * VN :=
      mul_le_mul (mul_le_mul_of_nonneg_left hpm hC233) hcnbase
        (jet_nonneg_lip (I := I) (M := M) (m := 2) g _)
        (mul_nonneg hC233 hPK)
    rw [hZB]
    linarith [hstep, hVN0]
  set Q : ℝ := Cblk * (aaPK (I := I) (M := M) g * (CI2 * ZB)) with hQ
  have hZB0 : 0 ≤ ZB := by rw [hZB]; exact mul_nonneg hone hVN0
  have hblkQ : ∀ (pm : Equiv.Perm (Fin 4)),
      (pm = aaP3201 ∨ pm = aaP2301 ∨ pm = aaP3102 ∨ pm = aaP1302 ∨
        pm = aaP1203 ∨ pm = aaP2103) →
      ∀ Z : SmoothCcTensor g 2 3,
      lowJetSq (I := I) (M := M) g 2 Z ≤ ZB →
      lowJetSq (I := I) (M := M) g 2
        (aaBlk (I := I) (M := M) g gT pm Z) ≤ Q := by
    intro pm hpmMem Z hZ
    have hpm := aaPK_ge4 (I := I) (M := M) g pm hpmMem
    refine (hblk gT pm Z).trans ?_
    have hinner : lowJetSq (I := I) (M := M) g 2
          (connDiffContrInsertionField (I := I) g gT) *
        lowJetSq (I := I) (M := M) g 2 Z ≤ CI2 * ZB :=
      mul_le_mul hci2T hZ (jet_nonneg_lip (I := I) (M := M) (m := 2) g Z)
        hCI20
    have hmid : lowJetSq (I := I) (M := M) g 2
          (permCoeff (I := I) (M := M) g pm) *
        (lowJetSq (I := I) (M := M) g 2
            (connDiffContrInsertionField (I := I) g gT) *
          lowJetSq (I := I) (M := M) g 2 Z) ≤
        aaPK (I := I) (M := M) g * (CI2 * ZB) :=
      mul_le_mul hpm hinner
        (mul_nonneg (jet_nonneg_lip (I := I) (M := M) (m := 2) g _)
          (jet_nonneg_lip (I := I) (M := M) (m := 2) g Z))
        hPK
    rw [hQ]
    exact mul_le_mul_of_nonneg_left hmid hCblk
  have hx0 := hblkQ aaP3201 (Or.inl rfl) _ (hZinn aaP102 (Or.inl rfl))
  have hx1 := hblkQ aaP2301 (Or.inr (Or.inl rfl)) _
    (hZinn aaP102 (Or.inl rfl))
  have hx2 := hblkQ aaP3102 (Or.inr (Or.inr (Or.inl rfl))) _
    (hZinn aaP120 (Or.inr rfl))
  have hx3 := hblkQ aaP1302 (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) _ hZdir
  have hx4 := hblkQ aaP1203
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) _ hZdir
  have hx5 := hblkQ aaP2103
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))) _
    (hZinn aaP120 (Or.inr rfl))
  have hrx : ∀ X : SmoothCcTensor g 2 4,
      lowJetSq (I := I) (M := M) g 2
          (reindexCoeffGen (I := I) (M := M) g 2 4 X innerCoreInPerm10) =
        lowJetSq (I := I) (M := M) g 2 X := by
    intro X
    rw [reindex_jet_lip]
  rw [aaKer_eq_lip (I := I) (M := M) g gT]
  set y0 := aaBlk (I := I) (M := M) g gT aaP3201
    (aaInn (I := I) (M := M) g gT aaP102) with hy0
  set y1 := reindexCoeffGen (I := I) (M := M) g 2 4
    (aaBlk (I := I) (M := M) g gT aaP2301
      (aaInn (I := I) (M := M) g gT aaP102)) innerCoreInPerm10 with hy1
  set y2 := aaBlk (I := I) (M := M) g gT aaP3102
    (aaInn (I := I) (M := M) g gT aaP120) with hy2
  set y3 := reindexCoeffGen (I := I) (M := M) g 2 4
    (aaBlk (I := I) (M := M) g gT aaP1302
      (connDiffContrInsertionInnerField (I := I) g gT)) innerCoreInPerm10
    with hy3
  set y4 := aaBlk (I := I) (M := M) g gT aaP1203
    (connDiffContrInsertionInnerField (I := I) g gT) with hy4
  set y5 := reindexCoeffGen (I := I) (M := M) g 2 4
    (aaBlk (I := I) (M := M) g gT aaP2103
      (aaInn (I := I) (M := M) g gT aaP120)) innerCoreInPerm10 with hy5
  have hb1 : lowJetSq (I := I) (M := M) g 2 y1 ≤ Q := by
    rw [hy1, hrx]; exact hx1
  have hb3 : lowJetSq (I := I) (M := M) g 2 y3 ≤ Q := by
    rw [hy3, hrx]; exact hx3
  have hb5 : lowJetSq (I := I) (M := M) g 2 y5 ≤ Q := by
    rw [hy5, hrx]; exact hx5
  have s01 : lowJetSq (I := I) (M := M) g 2 (y0 + y1) ≤ 4 * Q :=
    (jet_add_lip (I := I) (M := M) g 2 _ _).trans (by linarith [hx0, hb1])
  have s02 : lowJetSq (I := I) (M := M) g 2 (y0 + y1 + y2) ≤ 10 * Q :=
    (jet_add_lip (I := I) (M := M) g 2 _ _).trans (by linarith [s01, hx2])
  have s03 : lowJetSq (I := I) (M := M) g 2 (y0 + y1 + y2 + y3) ≤ 22 * Q :=
    (jet_add_lip (I := I) (M := M) g 2 _ _).trans (by linarith [s02, hb3])
  have s04 : lowJetSq (I := I) (M := M) g 2 (y0 + y1 + y2 + y3 + y4) ≤
      46 * Q :=
    (jet_add_lip (I := I) (M := M) g 2 _ _).trans (by linarith [s03, hx4])
  have s05 : lowJetSq (I := I) (M := M) g 2
      (y0 + y1 + y2 + y3 + y4 + y5) ≤ 94 * Q :=
    (jet_add_lip (I := I) (M := M) g 2 _ _).trans (by linarith [s04, hb5])
  refine s05.trans ?_
  simp only [B, hQ, hCI2, hZB, hVN, hpl2]
  apply le_of_eq
  ring

set_option maxHeartbeats 1600000 in
set_option linter.unusedVariables false in
/-- `H¹` two-state modulus of the quadratic Ricci kernel: `D2`-only. -/
private theorem aaKer_pair_h1
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ B : ℝ → ℝ,
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
            (0 : SmoothCcTensor g 0 2)) δ)
        (R A D2 : ℝ), 0 ≤ R → 0 ≤ A → 0 ≤ D2 →
        lowJetSq (I := I) (M := M) g 2 T ≤ R ^ 2 →
        lowJetSq (I := I) (M := M) g 2 U ≤ R ^ 2 →
        lowJetSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
        lowJetSq (I := I) (M := M) g 3 U ≤ A ^ 2 →
        lowJetSq (I := I) (M := M) g 2 (T - U) ≤ D2 ^ 2 →
      lowJetSq (I := I) (M := M) g 1
          (ricciAAKer (I := I) (M := M) g gT -
            ricciAAKer (I := I) (M := M) g gU) ≤
        B R * ((1 + A + A ^ 2) ^ 4 * D2 ^ 2) := by
  obtain ⟨Cblk, hCblk, hblk⟩ := aaBlk_pair_h1 (I := I) (M := M) hDim g
  obtain ⟨C233, hC233, h233⟩ := app_h2_mul_lip (I := I) (M := M) hDim g 2 3 3
  obtain ⟨C233p, hC233p, h233p⟩ :=
    app_h21_mul_lip (I := I) (M := M) hDim g 2 3 3
  obtain ⟨Bs, hBs, hci⟩ := connIns_bdd_h2 (I := I) (M := M) hDim g
  obtain ⟨Bn, hBn, hcn⟩ := connInn_bdd_h2 (I := I) (M := M) hDim g
  obtain ⟨Bi0, Bi1, hBi0, hBi1, hcid⟩ :=
    connIns_pair_h1 (I := I) (M := M) hDim g
      (δ₀ := (1 : ℝ) / 3) (by norm_num) (by norm_num)
  obtain ⟨Bm0, Bm1, hBm0, hBm1, hcnd⟩ :=
    connInn_pair_h1 (I := I) (M := M) hDim g
      (δ₀ := (1 : ℝ) / 3) (by norm_num) (by norm_num)
  have hfr : (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ) := Nat.cast_nonneg _
  have hPK : 0 ≤ aaPK (I := I) (M := M) g := aaPK_nonneg (I := I) (M := M) g
  have hone : (0 : ℝ) ≤ 1 + C233 * aaPK (I := I) (M := M) g := by
    have := mul_nonneg hC233 hPK; linarith
  have honep : (0 : ℝ) ≤ 1 + C233p * aaPK (I := I) (M := M) g := by
    have := mul_nonneg hC233p hPK; linarith
  let B : ℝ → ℝ := fun R =>
    94 * Cblk * (aaPK (I := I) (M := M) g *
      (((Module.finrank ℝ E : ℝ) ^ 2 * (2 * Bi0 R ^ 2 + 2 * Bi1 R ^ 2)) *
          ((1 + C233 * aaPK (I := I) (M := M) g) *
            ((Module.finrank ℝ E : ℝ) * Bn R ^ 2)) +
        ((Module.finrank ℝ E : ℝ) ^ 2 * Bs R ^ 2) *
          ((1 + C233p * aaPK (I := I) (M := M) g) *
            ((Module.finrank ℝ E : ℝ) *
              (2 * Bm0 R ^ 2 + 2 * Bm1 R ^ 2)))))
  have hB0 : ∀ R : ℝ, 0 ≤ R → 0 ≤ B R := by
    intro R hR
    have e1 : (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ) ^ 2 *
      (2 * Bi0 R ^ 2 + 2 * Bi1 R ^ 2) := by positivity
    have e2 : (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ) * Bn R ^ 2 := by positivity
    have e3 : (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ) ^ 2 * Bs R ^ 2 := by
      positivity
    have e4 : (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ) *
      (2 * Bm0 R ^ 2 + 2 * Bm1 R ^ 2) := by positivity
    simp only [B]
    exact mul_nonneg (mul_nonneg (by norm_num) hCblk)
      (mul_nonneg hPK
        (add_nonneg (mul_nonneg e1 (mul_nonneg hone e2))
          (mul_nonneg e3 (mul_nonneg honep e4))))
  refine ⟨B, hB0, ?_⟩
  intro gT gU T U hT hU hTtie hUtie δ hδ_le hδ0 hδT hδU hδZ
    R A D2 hR hA hD2 hT2 hU2 hT3 hU3 hTU2
  set pl2 : ℝ := (1 + A + A ^ 2) ^ 2 with hpl2
  have hbase : (1 : ℝ) ≤ 1 + A + A ^ 2 := by nlinarith [hA, sq_nonneg A]
  have hpl21 : (1 : ℝ) ≤ pl2 := by
    rw [hpl2]
    calc (1 : ℝ) = 1 ^ 2 := by norm_num
      _ ≤ (1 + A + A ^ 2) ^ 2 := pow_le_pow_left₀ zero_le_one hbase 2
  have hpl20 : (0 : ℝ) ≤ pl2 := le_trans zero_le_one hpl21
  have hplA2 : A ^ 2 ≤ pl2 := by
    rw [hpl2]
    nlinarith [hA, sq_nonneg A, mul_nonneg hA hA,
      mul_nonneg (mul_nonneg hA hA) hA]
  have hpu0 : (0 : ℝ) ≤ pl2 * D2 ^ 2 := mul_nonneg hpl20 (sq_nonneg D2)
  have hD2p : D2 ^ 2 ≤ pl2 * D2 ^ 2 := by nlinarith [hpl21, sq_nonneg D2]
  have hA2D : A ^ 2 * D2 ^ 2 ≤ pl2 * D2 ^ 2 :=
    mul_le_mul_of_nonneg_right hplA2 (sq_nonneg D2)
  have hpairfold : ∀ b0 b1 : ℝ,
      (b0 * D2 + b1 * A * D2) ^ 2 ≤
        (2 * b0 ^ 2 + 2 * b1 ^ 2) * (pl2 * D2 ^ 2) := by
    intro b0 b1
    have hstep : (b0 * D2 + b1 * A * D2) ^ 2 ≤
        2 * b0 ^ 2 * D2 ^ 2 + 2 * b1 ^ 2 * (A ^ 2 * D2 ^ 2) := by
      nlinarith [sq_nonneg (b0 * D2 - b1 * A * D2)]
    refine hstep.trans ?_
    have e1 : 2 * b0 ^ 2 * D2 ^ 2 ≤ 2 * b0 ^ 2 * (pl2 * D2 ^ 2) :=
      mul_le_mul_of_nonneg_left hD2p (by positivity)
    have e2 : 2 * b1 ^ 2 * (A ^ 2 * D2 ^ 2) ≤ 2 * b1 ^ 2 * (pl2 * D2 ^ 2) :=
      mul_le_mul_of_nonneg_left hA2D (by positivity)
    linarith
  set CI2 : ℝ := (Module.finrank ℝ E : ℝ) ^ 2 * Bs R ^ 2 * pl2 with hCI2
  set CID : ℝ := (Module.finrank ℝ E : ℝ) ^ 2 *
    ((2 * Bi0 R ^ 2 + 2 * Bi1 R ^ 2) * (pl2 * D2 ^ 2)) with hCID
  set VN : ℝ := (Module.finrank ℝ E : ℝ) * Bn R ^ 2 * pl2 with hVN
  set VM : ℝ := (Module.finrank ℝ E : ℝ) *
    ((2 * Bm0 R ^ 2 + 2 * Bm1 R ^ 2) * (pl2 * D2 ^ 2)) with hVM
  set ZB : ℝ := (1 + C233 * aaPK (I := I) (M := M) g) * VN with hZB
  set ZD : ℝ := (1 + C233p * aaPK (I := I) (M := M) g) * VM with hZD
  have hVN0 : 0 ≤ VN := by
    rw [hVN]; exact mul_nonneg (by positivity) hpl20
  have hVM0 : 0 ≤ VM := by
    rw [hVM]
    exact mul_nonneg hfr (mul_nonneg (by positivity) hpu0)
  have hCI20 : 0 ≤ CI2 := by
    rw [hCI2]; exact mul_nonneg (by positivity) hpl20
  have hCID0 : 0 ≤ CID := by
    rw [hCID]
    exact mul_nonneg (by positivity) (mul_nonneg (by positivity) hpu0)
  have hZB0 : 0 ≤ ZB := by rw [hZB]; exact mul_nonneg hone hVN0
  have hZD0 : 0 ≤ ZD := by rw [hZD]; exact mul_nonneg honep hVM0
  have hci2U : lowJetSq (I := I) (M := M) g 2
      (connDiffContrInsertionField (I := I) g gU) ≤ CI2 := by
    refine (hci gU U hU hUtie hδ_le hδ0 hδU hδZ R A hR hA hU2 hU3).trans ?_
    rw [hCI2]
    have hb : (Bs R * A) ^ 2 = Bs R ^ 2 * A ^ 2 := by ring
    rw [hb]
    have hnn : (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ) ^ 2 * Bs R ^ 2 := by
      positivity
    nlinarith [hplA2, hnn]
  have hcidT : lowJetSq (I := I) (M := M) g 1
      (connDiffContrInsertionField (I := I) g gT -
        connDiffContrInsertionField (I := I) g gU) ≤ CID := by
    refine (hcid gT gU T U hT hU hTtie hUtie hδ_le hδ0 hδT hδ_le hδ0 hδU
      R A D2 hR hA hD2 hU2 hT3 hTU2).trans ?_
    rw [hCID]
    have hnn : (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ) ^ 2 := by positivity
    exact mul_le_mul_of_nonneg_left (hpairfold (Bi0 R) (Bi1 R)) hnn
  have hcnbase : lowJetSq (I := I) (M := M) g 2
      (connDiffContrInsertionInnerField (I := I) g gT) ≤ VN := by
    refine (hcn gT T hT hTtie hδ_le hδ0 hδT hδZ R A hR hA hT2 hT3).trans ?_
    rw [hVN]
    have hb : (Bn R * A) ^ 2 = Bn R ^ 2 * A ^ 2 := by ring
    rw [hb]
    have hnn : (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ) * Bn R ^ 2 := by positivity
    nlinarith [hplA2, hnn]
  have hcndT : lowJetSq (I := I) (M := M) g 1
      (connDiffContrInsertionInnerField (I := I) g gT -
        connDiffContrInsertionInnerField (I := I) g gU) ≤ VM := by
    refine (hcnd gT gU T U hT hU hTtie hUtie hδ_le hδ0 hδT hδ_le hδ0 hδU
      R A D2 hR hA hD2 hU2 hT3 hTU2).trans ?_
    rw [hVM]
    exact mul_le_mul_of_nonneg_left (hpairfold (Bm0 R) (Bm1 R)) hfr
  have hZdirB : lowJetSq (I := I) (M := M) g 2
      (connDiffContrInsertionInnerField (I := I) g gT) ≤ ZB := by
    rw [hZB]
    linarith [hcnbase, mul_nonneg (mul_nonneg hC233 hPK) hVN0]
  have hZdirD : lowJetSq (I := I) (M := M) g 1
      (connDiffContrInsertionInnerField (I := I) g gT -
        connDiffContrInsertionInnerField (I := I) g gU) ≤ ZD := by
    rw [hZD]
    linarith [hcndT, mul_nonneg (mul_nonneg hC233p hPK) hVM0]
  have hZinnB : ∀ ρ : Equiv.Perm (Fin 3), (ρ = aaP102 ∨ ρ = aaP120) →
      lowJetSq (I := I) (M := M) g 2
        (aaInn (I := I) (M := M) g gT ρ) ≤ ZB := by
    intro ρ hρ
    have hpm := aaPK_ge3 (I := I) (M := M) g ρ hρ
    have hform : aaInn (I := I) (M := M) g gT ρ =
        appCcRS (I := I) (M := M) g 2 3 3
          (permCoeff (I := I) (M := M) g ρ)
          (connDiffContrInsertionInnerField (I := I) g gT) := rfl
    rw [hform]
    refine (h233 (permCoeff (I := I) (M := M) g ρ) _).trans ?_
    have hstep : C233 * lowJetSq (I := I) (M := M) g 2
          (permCoeff (I := I) (M := M) g ρ) *
        lowJetSq (I := I) (M := M) g 2
          (connDiffContrInsertionInnerField (I := I) g gT) ≤
        C233 * aaPK (I := I) (M := M) g * VN :=
      mul_le_mul (mul_le_mul_of_nonneg_left hpm hC233) hcnbase
        (jet_nonneg_lip (I := I) (M := M) (m := 2) g _)
        (mul_nonneg hC233 hPK)
    rw [hZB]
    linarith [hstep, hVN0]
  have hZinnD : ∀ ρ : Equiv.Perm (Fin 3), (ρ = aaP102 ∨ ρ = aaP120) →
      lowJetSq (I := I) (M := M) g 1
        (aaInn (I := I) (M := M) g gT ρ -
          aaInn (I := I) (M := M) g gU ρ) ≤ ZD := by
    intro ρ hρ
    have hpm := aaPK_ge3 (I := I) (M := M) g ρ hρ
    have hsub : aaInn (I := I) (M := M) g gT ρ -
          aaInn (I := I) (M := M) g gU ρ =
        appCcRS (I := I) (M := M) g 2 3 3
          (permCoeff (I := I) (M := M) g ρ)
          (connDiffContrInsertionInnerField (I := I) g gT -
            connDiffContrInsertionInnerField (I := I) g gU) := by
      have hfT : aaInn (I := I) (M := M) g gT ρ =
          appCcRS (I := I) (M := M) g 2 3 3
            (permCoeff (I := I) (M := M) g ρ)
            (connDiffContrInsertionInnerField (I := I) g gT) := rfl
      have hfU : aaInn (I := I) (M := M) g gU ρ =
          appCcRS (I := I) (M := M) g 2 3 3
            (permCoeff (I := I) (M := M) g ρ)
            (connDiffContrInsertionInnerField (I := I) g gU) := rfl
      rw [hfT, hfU, appCcRS_sub_right]
    rw [hsub]
    refine (h233p (permCoeff (I := I) (M := M) g ρ) _).trans ?_
    have hstep : C233p * lowJetSq (I := I) (M := M) g 2
          (permCoeff (I := I) (M := M) g ρ) *
        lowJetSq (I := I) (M := M) g 1
          (connDiffContrInsertionInnerField (I := I) g gT -
            connDiffContrInsertionInnerField (I := I) g gU) ≤
        C233p * aaPK (I := I) (M := M) g * VM :=
      mul_le_mul (mul_le_mul_of_nonneg_left hpm hC233p) hcndT
        (jet_nonneg_lip (I := I) (M := M) (m := 1) g _)
        (mul_nonneg hC233p hPK)
    rw [hZD]
    linarith [hstep, hVM0]
  set Q : ℝ := Cblk * (aaPK (I := I) (M := M) g * (CID * ZB + CI2 * ZD))
    with hQ
  have hblkQ : ∀ (pm : Equiv.Perm (Fin 4)),
      (pm = aaP3201 ∨ pm = aaP2301 ∨ pm = aaP3102 ∨ pm = aaP1302 ∨
        pm = aaP1203 ∨ pm = aaP2103) →
      ∀ ZT ZU : SmoothCcTensor g 2 3,
      lowJetSq (I := I) (M := M) g 2 ZT ≤ ZB →
      lowJetSq (I := I) (M := M) g 1 (ZT - ZU) ≤ ZD →
      lowJetSq (I := I) (M := M) g 1
        (aaBlk (I := I) (M := M) g gT pm ZT -
          aaBlk (I := I) (M := M) g gU pm ZU) ≤ Q := by
    intro pm hpmMem ZT ZU hzb hzd
    have hpm := aaPK_ge4 (I := I) (M := M) g pm hpmMem
    refine (hblk gT gU pm ZT ZU).trans ?_
    have h1 : lowJetSq (I := I) (M := M) g 1
          (connDiffContrInsertionField (I := I) g gT -
            connDiffContrInsertionField (I := I) g gU) *
        lowJetSq (I := I) (M := M) g 2 ZT ≤ CID * ZB :=
      mul_le_mul hcidT hzb (jet_nonneg_lip (I := I) (M := M) (m := 2) g ZT)
        hCID0
    have h2 : lowJetSq (I := I) (M := M) g 2
          (connDiffContrInsertionField (I := I) g gU) *
        lowJetSq (I := I) (M := M) g 1 (ZT - ZU) ≤ CI2 * ZD :=
      mul_le_mul hci2U hzd (jet_nonneg_lip (I := I) (M := M) (m := 1) g _)
        hCI20
    have hsum0 : 0 ≤ lowJetSq (I := I) (M := M) g 1
          (connDiffContrInsertionField (I := I) g gT -
            connDiffContrInsertionField (I := I) g gU) *
          lowJetSq (I := I) (M := M) g 2 ZT +
        lowJetSq (I := I) (M := M) g 2
            (connDiffContrInsertionField (I := I) g gU) *
          lowJetSq (I := I) (M := M) g 1 (ZT - ZU) :=
      add_nonneg
        (mul_nonneg (jet_nonneg_lip (I := I) (M := M) (m := 1) g _)
          (jet_nonneg_lip (I := I) (M := M) (m := 2) g ZT))
        (mul_nonneg (jet_nonneg_lip (I := I) (M := M) (m := 2) g _)
          (jet_nonneg_lip (I := I) (M := M) (m := 1) g _))
    have hmid : lowJetSq (I := I) (M := M) g 2
          (permCoeff (I := I) (M := M) g pm) *
        (lowJetSq (I := I) (M := M) g 1
              (connDiffContrInsertionField (I := I) g gT -
                connDiffContrInsertionField (I := I) g gU) *
            lowJetSq (I := I) (M := M) g 2 ZT +
          lowJetSq (I := I) (M := M) g 2
              (connDiffContrInsertionField (I := I) g gU) *
            lowJetSq (I := I) (M := M) g 1 (ZT - ZU)) ≤
        aaPK (I := I) (M := M) g * (CID * ZB + CI2 * ZD) :=
      mul_le_mul hpm (by linarith [h1, h2]) hsum0 hPK
    rw [hQ]
    exact mul_le_mul_of_nonneg_left hmid hCblk
  have hx0 := hblkQ aaP3201 (Or.inl rfl) _ _
    (hZinnB aaP102 (Or.inl rfl)) (hZinnD aaP102 (Or.inl rfl))
  have hx1 := hblkQ aaP2301 (Or.inr (Or.inl rfl)) _ _
    (hZinnB aaP102 (Or.inl rfl)) (hZinnD aaP102 (Or.inl rfl))
  have hx2 := hblkQ aaP3102 (Or.inr (Or.inr (Or.inl rfl))) _ _
    (hZinnB aaP120 (Or.inr rfl)) (hZinnD aaP120 (Or.inr rfl))
  have hx3 := hblkQ aaP1302 (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) _ _
    hZdirB hZdirD
  have hx4 := hblkQ aaP1203
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) _ _ hZdirB hZdirD
  have hx5 := hblkQ aaP2103
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))) _ _
    (hZinnB aaP120 (Or.inr rfl)) (hZinnD aaP120 (Or.inr rfl))
  have hrx : ∀ X Y : SmoothCcTensor g 2 4,
      lowJetSq (I := I) (M := M) g 1
          (reindexCoeffGen (I := I) (M := M) g 2 4 X innerCoreInPerm10 -
            reindexCoeffGen (I := I) (M := M) g 2 4 Y innerCoreInPerm10) =
        lowJetSq (I := I) (M := M) g 1 (X - Y) := by
    intro X Y
    rw [← reindex_sub_lip, reindex_jet_lip]
  rw [aaKer_eq_lip (I := I) (M := M) g gT,
    aaKer_eq_lip (I := I) (M := M) g gU]
  set y0 := aaBlk (I := I) (M := M) g gT aaP3201
    (aaInn (I := I) (M := M) g gT aaP102) with hy0
  set y1 := reindexCoeffGen (I := I) (M := M) g 2 4
    (aaBlk (I := I) (M := M) g gT aaP2301
      (aaInn (I := I) (M := M) g gT aaP102)) innerCoreInPerm10 with hy1
  set y2 := aaBlk (I := I) (M := M) g gT aaP3102
    (aaInn (I := I) (M := M) g gT aaP120) with hy2
  set y3 := reindexCoeffGen (I := I) (M := M) g 2 4
    (aaBlk (I := I) (M := M) g gT aaP1302
      (connDiffContrInsertionInnerField (I := I) g gT)) innerCoreInPerm10
    with hy3
  set y4 := aaBlk (I := I) (M := M) g gT aaP1203
    (connDiffContrInsertionInnerField (I := I) g gT) with hy4
  set y5 := reindexCoeffGen (I := I) (M := M) g 2 4
    (aaBlk (I := I) (M := M) g gT aaP2103
      (aaInn (I := I) (M := M) g gT aaP120)) innerCoreInPerm10 with hy5
  set z0 := aaBlk (I := I) (M := M) g gU aaP3201
    (aaInn (I := I) (M := M) g gU aaP102) with hz0
  set z1 := reindexCoeffGen (I := I) (M := M) g 2 4
    (aaBlk (I := I) (M := M) g gU aaP2301
      (aaInn (I := I) (M := M) g gU aaP102)) innerCoreInPerm10 with hz1
  set z2 := aaBlk (I := I) (M := M) g gU aaP3102
    (aaInn (I := I) (M := M) g gU aaP120) with hz2
  set z3 := reindexCoeffGen (I := I) (M := M) g 2 4
    (aaBlk (I := I) (M := M) g gU aaP1302
      (connDiffContrInsertionInnerField (I := I) g gU)) innerCoreInPerm10
    with hz3
  set z4 := aaBlk (I := I) (M := M) g gU aaP1203
    (connDiffContrInsertionInnerField (I := I) g gU) with hz4
  set z5 := reindexCoeffGen (I := I) (M := M) g 2 4
    (aaBlk (I := I) (M := M) g gU aaP2103
      (aaInn (I := I) (M := M) g gU aaP120)) innerCoreInPerm10 with hz5
  have hb1 : lowJetSq (I := I) (M := M) g 1 (y1 - z1) ≤ Q := by
    rw [hy1, hz1, hrx]; exact hx1
  have hb3 : lowJetSq (I := I) (M := M) g 1 (y3 - z3) ≤ Q := by
    rw [hy3, hz3, hrx]; exact hx3
  have hb5 : lowJetSq (I := I) (M := M) g 1 (y5 - z5) ≤ Q := by
    rw [hy5, hz5, hrx]; exact hx5
  have hsplit : y0 + y1 + y2 + y3 + y4 + y5 -
      (z0 + z1 + z2 + z3 + z4 + z5) =
      (y0 - z0) + (y1 - z1) + (y2 - z2) + (y3 - z3) + (y4 - z4) +
        (y5 - z5) := by abel
  rw [hsplit]
  have s01 : lowJetSq (I := I) (M := M) g 1 ((y0 - z0) + (y1 - z1)) ≤
      4 * Q :=
    (jet_add_lip (I := I) (M := M) g 1 _ _).trans (by linarith [hx0, hb1])
  have s02 : lowJetSq (I := I) (M := M) g 1
      ((y0 - z0) + (y1 - z1) + (y2 - z2)) ≤ 10 * Q :=
    (jet_add_lip (I := I) (M := M) g 1 _ _).trans (by linarith [s01, hx2])
  have s03 : lowJetSq (I := I) (M := M) g 1
      ((y0 - z0) + (y1 - z1) + (y2 - z2) + (y3 - z3)) ≤ 22 * Q :=
    (jet_add_lip (I := I) (M := M) g 1 _ _).trans (by linarith [s02, hb3])
  have s04 : lowJetSq (I := I) (M := M) g 1
      ((y0 - z0) + (y1 - z1) + (y2 - z2) + (y3 - z3) + (y4 - z4)) ≤
      46 * Q :=
    (jet_add_lip (I := I) (M := M) g 1 _ _).trans (by linarith [s03, hx4])
  have s05 : lowJetSq (I := I) (M := M) g 1
      ((y0 - z0) + (y1 - z1) + (y2 - z2) + (y3 - z3) + (y4 - z4) +
        (y5 - z5)) ≤ 94 * Q :=
    (jet_add_lip (I := I) (M := M) g 1 _ _).trans (by linarith [s04, hb5])
  refine s05.trans ?_
  simp only [B, hQ, hCI2, hCID, hZB, hZD, hVN, hVM, hpl2]
  apply le_of_eq
  ring

set_option maxHeartbeats 1600000 in
set_option linter.unusedVariables false in
/-- Two-state `H¹` modulus of the whole quadratic Ricci arm. -/
private theorem ricciAA_pair_h1
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ : ℝ, ∃ B : ℝ → ℝ,
      0 < ρ ∧ (∀ R : ℝ, 0 ≤ R → 0 ≤ B R) ∧
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
            (0 : SmoothCcTensor g 0 2)) δ)
        (R A D2 N : ℝ), 0 ≤ R → 0 ≤ A → 0 ≤ D2 → 0 ≤ N →
        lowJetSq (I := I) (M := M) g 2 T ≤ R ^ 2 →
        lowJetSq (I := I) (M := M) g 2 U ≤ R ^ 2 →
        lowJetSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
        lowJetSq (I := I) (M := M) g 3 U ≤ A ^ 2 →
        lowJetSq (I := I) (M := M) g 2 (T - U) ≤ D2 ^ 2 →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U)‖ ≤ N →
      lowJetSq (I := I) (M := M) g 1
          (ricciAAArm (I := I) (M := M) g gT -
            ricciAAArm (I := I) (M := M) g gU) ≤
        B R * ((1 + A + A ^ 2) ^ 4 * (D2 ^ 2 + N ^ 2)) := by
  obtain ⟨Ca, hCa, happ⟩ := app_h21_mul_lip (I := I) (M := M) hDim g 2 4 2
  obtain ⟨ρp, Cft, hρp, hCft, hftp⟩ :=
    fourtrace_pair_h2 (I := I) (M := M) hDim g
  obtain ⟨ρb, Bft, hρb, hBft, hftb⟩ :=
    fourtrace_bdd_h2 (I := I) (M := M) hDim g
  obtain ⟨Bk, hBk, hkerb⟩ := aaKer_bdd_h2 (I := I) (M := M) hDim g
  obtain ⟨Bd, hBd, hkerd⟩ := aaKer_pair_h1 (I := I) (M := M) hDim g
  let K1 : ℝ → ℝ := fun R => Ca * (22 * Cft ^ 2) * Bk R
  let K2 : ℝ → ℝ := fun R => Ca * (22 * Bft ^ 2) * Bd R
  let B : ℝ → ℝ := fun R => 2 * (K1 R + K2 R)
  have hK10 : ∀ R : ℝ, 0 ≤ R → 0 ≤ K1 R := by
    intro R hR
    have := hBk R hR
    simp only [K1]
    positivity
  have hK20 : ∀ R : ℝ, 0 ≤ R → 0 ≤ K2 R := by
    intro R hR
    have := hBd R hR
    simp only [K2]
    positivity
  refine ⟨min ρp ρb, B, lt_min hρp hρb, ?_, ?_⟩
  · intro R hR
    have e1 := hK10 R hR
    have e2 := hK20 R hR
    simp only [B]
    linarith
  intro gT gU T U hT hU hTtie hUtie δ hδ_le hδ0 hδT hδU hδZ
    R A D2 N hR hA hD2 hN hT2 hU2 hT3 hU3 hTU2 hTn hUn hTUn
  have hρp' : min ρp ρb ≤ ρp := min_le_left _ _
  have hρb' : min ρp ρb ≤ ρb := min_le_right _ _
  set W : ℝ := (1 + A + A ^ 2) ^ 4 with hW
  set u : ℝ := D2 ^ 2 + N ^ 2 with hu
  have hu0 : (0 : ℝ) ≤ u := by rw [hu]; positivity
  have hW0 : (0 : ℝ) ≤ W := by rw [hW]; positivity
  have hNu : N ^ 2 ≤ u := by rw [hu]; nlinarith [sq_nonneg D2]
  have hDu : D2 ^ 2 ≤ u := by rw [hu]; nlinarith [sq_nonneg N]
  have hftd : lowJetSq (I := I) (M := M) g 2
      (ricciCometricFourTraceCastG0 (I := I) g gT -
        ricciCometricFourTraceCastG0 (I := I) g gU) ≤
      22 * Cft ^ 2 * u := by
    refine (hftp T U gT gU hTtie hUtie (hTn.trans hρp')
      (hUn.trans hρp')).trans ?_
    have h1 : Cft * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U)‖ ≤
        Cft * N := mul_le_mul_of_nonneg_left hTUn hCft
    have h2 : (Cft * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
        (T - U)‖) ^ 2 ≤ (Cft * N) ^ 2 :=
      pow_le_pow_left₀ (mul_nonneg hCft (norm_nonneg _)) h1 2
    have h3 : (Cft * N) ^ 2 = Cft ^ 2 * N ^ 2 := by ring
    have h4 : Cft ^ 2 * N ^ 2 ≤ Cft ^ 2 * u :=
      mul_le_mul_of_nonneg_left hNu (sq_nonneg Cft)
    linarith
  have hftbU : lowJetSq (I := I) (M := M) g 2
      (ricciCometricFourTraceCastG0 (I := I) g gU) ≤ 22 * Bft ^ 2 :=
    hftb U gU hUtie (hUn.trans hρb')
  have hkT2 : lowJetSq (I := I) (M := M) g 2
      (ricciAAKer (I := I) (M := M) g gT) ≤ Bk R * W := by
    rw [hW]
    exact hkerb gT T hT hTtie hδ_le hδ0 hδT hδZ R A hR hA hT2 hT3
  have hkT1 : lowJetSq (I := I) (M := M) g 1
      (ricciAAKer (I := I) (M := M) g gT) ≤ Bk R * W :=
    le_trans (jet_mono_lip (I := I) (M := M) g (by norm_num : (1:ℕ) ≤ 2) _)
      hkT2
  have hkd : lowJetSq (I := I) (M := M) g 1
      (ricciAAKer (I := I) (M := M) g gT -
        ricciAAKer (I := I) (M := M) g gU) ≤ Bd R * (W * u) := by
    refine (hkerd gT gU T U hT hU hTtie hUtie hδ_le hδ0 hδT hδU hδZ
      R A D2 hR hA hD2 hT2 hU2 hT3 hU3 hTU2).trans ?_
    rw [hW]
    have hBdR := hBd R hR
    have hstep : (1 + A + A ^ 2) ^ 4 * D2 ^ 2 ≤ (1 + A + A ^ 2) ^ 4 * u :=
      mul_le_mul_of_nonneg_left hDu (by positivity)
    exact mul_le_mul_of_nonneg_left hstep hBdR
  have hformT : ricciAAArm (I := I) (M := M) g gT =
      appCcRS (I := I) (M := M) g 2 4 2
        (ricciCometricFourTraceCastG0 (I := I) g gT)
        (ricciAAKer (I := I) (M := M) g gT) := rfl
  have hformU : ricciAAArm (I := I) (M := M) g gU =
      appCcRS (I := I) (M := M) g 2 4 2
        (ricciCometricFourTraceCastG0 (I := I) g gU)
        (ricciAAKer (I := I) (M := M) g gU) := rfl
  have hdel : ricciAAArm (I := I) (M := M) g gT -
        ricciAAArm (I := I) (M := M) g gU =
      appCcRS (I := I) (M := M) g 2 4 2
          (ricciCometricFourTraceCastG0 (I := I) g gT -
            ricciCometricFourTraceCastG0 (I := I) g gU)
          (ricciAAKer (I := I) (M := M) g gT) +
        appCcRS (I := I) (M := M) g 2 4 2
          (ricciCometricFourTraceCastG0 (I := I) g gU)
          (ricciAAKer (I := I) (M := M) g gT -
            ricciAAKer (I := I) (M := M) g gU) := by
    rw [hformT, hformU, appCcRS_sub_left, appCcRS_sub_right]
    module
  rw [hdel]
  have h1 : lowJetSq (I := I) (M := M) g 1
      (appCcRS (I := I) (M := M) g 2 4 2
        (ricciCometricFourTraceCastG0 (I := I) g gT -
          ricciCometricFourTraceCastG0 (I := I) g gU)
        (ricciAAKer (I := I) (M := M) g gT)) ≤ K1 R * (W * u) := by
    refine (happ _ _).trans ?_
    calc
      Ca * lowJetSq (I := I) (M := M) g 2
            (ricciCometricFourTraceCastG0 (I := I) g gT -
              ricciCometricFourTraceCastG0 (I := I) g gU) *
          lowJetSq (I := I) (M := M) g 1
            (ricciAAKer (I := I) (M := M) g gT) ≤
          Ca * (22 * Cft ^ 2 * u) * (Bk R * W) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hftd hCa) hkT1
          (jet_nonneg_lip (I := I) (M := M) (m := 1) g _)
          (mul_nonneg hCa (by positivity))
      _ = K1 R * (W * u) := by simp only [K1]; ring
  have h2 : lowJetSq (I := I) (M := M) g 1
      (appCcRS (I := I) (M := M) g 2 4 2
        (ricciCometricFourTraceCastG0 (I := I) g gU)
        (ricciAAKer (I := I) (M := M) g gT -
          ricciAAKer (I := I) (M := M) g gU)) ≤ K2 R * (W * u) := by
    refine (happ _ _).trans ?_
    calc
      Ca * lowJetSq (I := I) (M := M) g 2
            (ricciCometricFourTraceCastG0 (I := I) g gU) *
          lowJetSq (I := I) (M := M) g 1
            (ricciAAKer (I := I) (M := M) g gT -
              ricciAAKer (I := I) (M := M) g gU) ≤
          Ca * (22 * Bft ^ 2) * (Bd R * (W * u)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hftbU hCa) hkd
          (jet_nonneg_lip (I := I) (M := M) (m := 1) g _)
          (mul_nonneg hCa (by positivity))
      _ = K2 R * (W * u) := by simp only [K2]; ring
  refine (jet_add_lip (I := I) (M := M) g 1 _ _).trans ?_
  have hsum : 2 * (K1 R * (W * u) + K2 R * (W * u)) =
      B R * ((1 + A + A ^ 2) ^ 4 * (D2 ^ 2 + N ^ 2)) := by
    simp only [B, hW, hu]
    ring
  calc
    2 * (lowJetSq (I := I) (M := M) g 1
          (appCcRS (I := I) (M := M) g 2 4 2
            (ricciCometricFourTraceCastG0 (I := I) g gT -
              ricciCometricFourTraceCastG0 (I := I) g gU)
            (ricciAAKer (I := I) (M := M) g gT)) +
        lowJetSq (I := I) (M := M) g 1
          (appCcRS (I := I) (M := M) g 2 4 2
            (ricciCometricFourTraceCastG0 (I := I) g gU)
            (ricciAAKer (I := I) (M := M) g gT -
              ricciAAKer (I := I) (M := M) g gU))) ≤
        2 * (K1 R * (W * u) + K2 R * (W * u)) := by linarith [h1, h2]
    _ = B R * ((1 + A + A ^ 2) ^ 4 * (D2 ^ 2 + N ^ 2)) := hsum

/-! ### Layer G — the derivative-of-connection (`DA`) Ricci arm -/

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1000000 in
set_option linter.unusedVariables false in
/-- Two-state `H¹` modulus of the lower derivative-of-connection Ricci arm.
This is where the second argument of `ricciGoodLow` moves, and it is consumed
only through `J1 (covGrad (P - Q)) ≤ J2 (P - Q) ≤ D2 ^ 2`. -/
private theorem ricciDA_pair_h1
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ : ℝ, ∃ B : ℝ → ℝ,
      0 < ρ ∧ (∀ R : ℝ, 0 ≤ R → 0 ≤ B R) ∧
      ∀ (gT gU : SmoothRiemannianMetric I M)
        (P Q : SmoothCcTensor g 0 2)
        (hP : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g P x u v =
            ccTensorBilin (I := I) g P x v u)
        (hQ : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g Q x u v =
            ccTensorBilin (I := I) g Q x v u)
        (hPtie : ∀ (x : M) (u v : TangentSpace I x),
          gT.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g P x u v)
        (hQtie : ∀ (x : M) (u v : TangentSpace I x),
          gU.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g Q x u v)
        {δ : ℝ} (hδ_le : δ ≤ 1 / 3) (hδ0 : 0 ≤ δ)
        (hδP : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g P) δ)
        (hδQ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g Q) δ)
        (R A D2 N : ℝ), 0 ≤ R → 0 ≤ A → 0 ≤ D2 → 0 ≤ N →
        lowJetSq (I := I) (M := M) g 2 P ≤ R ^ 2 →
        lowJetSq (I := I) (M := M) g 2 Q ≤ R ^ 2 →
        lowJetSq (I := I) (M := M) g 3 P ≤ A ^ 2 →
        lowJetSq (I := I) (M := M) g 3 Q ≤ A ^ 2 →
        lowJetSq (I := I) (M := M) g 2 (P - Q) ≤ D2 ^ 2 →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) P‖ ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) Q‖ ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (P - Q)‖ ≤ N →
      lowJetSq (I := I) (M := M) g 1
          (LowBaseInternal.ricciDALow (I := I) (M := M) g gT P -
            LowBaseInternal.ricciDALow (I := I) (M := M) g gU Q) ≤
        B R * ((1 + A + A ^ 2) ^ 4 * (D2 ^ 2 + N ^ 2)) := by
  obtain ⟨Kdag, hKdag, hdagb⟩ := dagLow_bdd_h2 (I := I) (M := M) hDim g
  obtain ⟨ρd, Cd, hρd, hCd, hdagd⟩ := dagLow_pair_h1 (I := I) (M := M) hDim g
  obtain ⟨Cf034, hCf034, h034f⟩ :=
    app_h12_mul_lip (I := I) (M := M) hDim g 0 3 4
  obtain ⟨Ca034, hCa034, h034a⟩ :=
    app_h21_mul_lip (I := I) (M := M) hDim g 0 3 4
  obtain ⟨Cb034, hCb034, h034b⟩ :=
    app_h2_mul_lip (I := I) (M := M) hDim g 0 3 4
  obtain ⟨Kr1, hKr1, hrf1⟩ := refold_h1_lip (I := I) (M := M) hDim g
  obtain ⟨Kr2, hKr2, hrf2⟩ := refold_h2_lip (I := I) (M := M) hDim g
  obtain ⟨Cf222, hCf222, h222f⟩ :=
    app_h12_mul_lip (I := I) (M := M) hDim g 2 2 2
  obtain ⟨Ca222, hCa222, h222a⟩ :=
    app_h21_mul_lip (I := I) (M := M) hDim g 2 2 2
  obtain ⟨Be, hBe, hfsb⟩ :=
    LowBaseInternal.fullSlot_bdd_h2 (I := I) (M := M) g
      (δ₀ := (1 : ℝ) / 3) (by norm_num) (by norm_num)
  obtain ⟨Be0, Be1, hBe0, hBe1, hfsd⟩ :=
    LowBaseInternal.fullSlot_pair_h1 (I := I) (M := M) hDim g
      (δ₀ := (1 : ℝ) / 3) (by norm_num) (by norm_num)
  let c1 : ℝ := 2 * (Cf034 * Cd + 2 * (Ca034 * Kdag))
  let c2 : ℝ := 2 * (Cb034 * Kdag)
  let D1 : ℝ → ℝ := fun R => Cf222 * Kr1 * c1 * Be R ^ 2
  let D2c : ℝ → ℝ := fun R =>
    Ca222 * Kr2 * c2 * (2 * Be0 R ^ 2 + 2 * Be1 R ^ 2)
  let B : ℝ → ℝ := fun R => 8 * (D1 R + D2c R)
  have hc10 : (0 : ℝ) ≤ c1 := by
    have e1 := mul_nonneg hCf034 hCd
    have e2 := mul_nonneg hCa034 hKdag
    simp only [c1]
    linarith only [e1, e2]
  have hc20 : (0 : ℝ) ≤ c2 := by
    have e1 := mul_nonneg hCb034 hKdag
    simp only [c2]
    linarith only [e1]
  have hD10 : ∀ R : ℝ, 0 ≤ D1 R := by
    intro R
    simp only [D1]
    exact mul_nonneg (mul_nonneg (mul_nonneg hCf222 hKr1) hc10) (sq_nonneg _)
  have hD2c0 : ∀ R : ℝ, 0 ≤ D2c R := by
    intro R
    simp only [D2c]
    refine mul_nonneg (mul_nonneg (mul_nonneg hCa222 hKr2) hc20) ?_
    positivity
  refine ⟨ρd, B, hρd, ?_, ?_⟩
  · intro R hR
    have e1 := hD10 R
    have e2 := hD2c0 R
    simp only [B]
    linarith only [e1, e2]
  intro gT gU P Q hP hQ hPtie hQtie δ hδ_le hδ0 hδP hδQ
    R A D2 N hR hA hD2 hN hP2 hQ2 hP3 hQ3 hPQ2 hPn hQn hPQn
  -- ## polynomial bookkeeping
  set p : ℝ := 1 + A + A ^ 2 with hp
  have hp1 : (1 : ℝ) ≤ p := by
    rw [hp]; linarith only [hA, sq_nonneg A]
  have hp0 : (0 : ℝ) ≤ p := by linarith only [hp1]
  have hpA2 : A ^ 2 ≤ p := by
    rw [hp]; linarith only [hA]
  have hpm1 : (0 : ℝ) ≤ p - 1 := by linarith only [hp1]
  have hpq : (0 : ℝ) ≤ p ^ 2 + p + 1 := by
    linarith only [sq_nonneg p, hp0]
  have hp4_1 : p ≤ p ^ 4 := by
    linarith only [mul_nonneg (mul_nonneg hp0 hpm1) hpq]
  have hp4_3 : p ^ 3 ≤ p ^ 4 := by
    linarith only [mul_nonneg (mul_nonneg (mul_nonneg hp0 hp0) hp0) hpm1]
  set u : ℝ := D2 ^ 2 + N ^ 2 with hu
  have hu0 : (0 : ℝ) ≤ u := by
    rw [hu]; linarith only [sq_nonneg D2, sq_nonneg N]
  have hNu : N ^ 2 ≤ u := by rw [hu]; linarith only [sq_nonneg D2]
  have hDu : D2 ^ 2 ≤ u := by rw [hu]; linarith only [sq_nonneg N]
  have hpu0 : (0 : ℝ) ≤ p * u := mul_nonneg hp0 hu0
  have hpu : p * u ≤ p ^ 4 * u := mul_le_mul_of_nonneg_right hp4_1 hu0
  have hp3u : p ^ 3 * u ≤ p ^ 4 * u := mul_le_mul_of_nonneg_right hp4_3 hu0
  have huple : u ≤ p * u := by
    have h := mul_le_mul_of_nonneg_right hp1 hu0
    linarith only [h]
  -- ## the moving factors
  set GT : SmoothCcTensor g 0 4 :=
    appCcRS (I := I) (M := M) g 0 3 4
      (LowBaseInternal.dagLowOp (I := I) (M := M) g gT)
      (covGrad (I := I) (M := M) g 0 2 P) with hGT
  set GU : SmoothCcTensor g 0 4 :=
    appCcRS (I := I) (M := M) g 0 3 4
      (LowBaseInternal.dagLowOp (I := I) (M := M) g gU)
      (covGrad (I := I) (M := M) g 0 2 Q) with hGU
  set ET : SmoothCcTensor g 2 2 :=
    slotInsertEndoCc (I := I) (M := M) g 1
      (fullRaisedEndoField (I := I) (M := M) g gT) with hET
  set EU : SmoothCcTensor g 2 2 :=
    slotInsertEndoCc (I := I) (M := M) g 1
      (fullRaisedEndoField (I := I) (M := M) g gU) with hEU
  have hdagU : lowJetSq (I := I) (M := M) g 2
      (LowBaseInternal.dagLowOp (I := I) (M := M) g gU) ≤
      Kdag * (1 + A ^ 2) :=
    hdagb gU Q hQ hQtie hδ_le hδ0 hδQ A hA hQ3
  have hdagd' : lowJetSq (I := I) (M := M) g 1
      (LowBaseInternal.dagLowOp (I := I) (M := M) g gT -
        LowBaseInternal.dagLowOp (I := I) (M := M) g gU) ≤ Cd * N ^ 2 := by
    refine (hdagd P Q gT gU hPtie hQtie hPn hQn).trans ?_
    have hsq : ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (P - Q)‖ ^ 2 ≤
        N ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hPQn 2
    exact mul_le_mul_of_nonneg_left hsq hCd
  have hgP2 : lowJetSq (I := I) (M := M) g 2
      (covGrad (I := I) (M := M) g 0 2 P) ≤ A ^ 2 :=
    (grad_h2_le_h3_lip (I := I) (M := M) g P).trans hP3
  have hgQ2 : lowJetSq (I := I) (M := M) g 2
      (covGrad (I := I) (M := M) g 0 2 Q) ≤ A ^ 2 :=
    (grad_h2_le_h3_lip (I := I) (M := M) g Q).trans hQ3
  have hgd1 : lowJetSq (I := I) (M := M) g 1
      (covGrad (I := I) (M := M) g 0 2 (P - Q)) ≤ D2 ^ 2 :=
    (grad_h1_le_h2_lip (I := I) (M := M) g (P - Q)).trans hPQ2
  -- ## the `G` telescope
  have hGcomb : appCcRS (I := I) (M := M) g 0 3 4
        (LowBaseInternal.dagLowOp (I := I) (M := M) g gT -
          LowBaseInternal.dagLowOp (I := I) (M := M) g gU)
        (covGrad (I := I) (M := M) g 0 2 P) +
      appCcRS (I := I) (M := M) g 0 3 4
        (LowBaseInternal.dagLowOp (I := I) (M := M) g gU)
        (covGrad (I := I) (M := M) g 0 2 (P - Q)) = GT - GU := by
    rw [hGT, hGU, appCcRS_sub_left, covGrad_sub, appCcRS_sub_right]
    module
  have hGd : lowJetSq (I := I) (M := M) g 1 (GT - GU) ≤ c1 * (p * u) := by
    rw [← hGcomb]
    have e1 : lowJetSq (I := I) (M := M) g 1
        (appCcRS (I := I) (M := M) g 0 3 4
          (LowBaseInternal.dagLowOp (I := I) (M := M) g gT -
            LowBaseInternal.dagLowOp (I := I) (M := M) g gU)
          (covGrad (I := I) (M := M) g 0 2 P)) ≤
        Cf034 * Cd * (p * u) := by
      refine (h034f _ _).trans ?_
      have hstep : Cf034 * lowJetSq (I := I) (M := M) g 1
            (LowBaseInternal.dagLowOp (I := I) (M := M) g gT -
              LowBaseInternal.dagLowOp (I := I) (M := M) g gU) *
          lowJetSq (I := I) (M := M) g 2
            (covGrad (I := I) (M := M) g 0 2 P) ≤
          Cf034 * (Cd * N ^ 2) * A ^ 2 :=
        mul_le_mul (mul_le_mul_of_nonneg_left hdagd' hCf034) hgP2
          (jet_nonneg_lip (I := I) (M := M) (m := 2) g _)
          (mul_nonneg hCf034 (mul_nonneg hCd (sq_nonneg N)))
      refine hstep.trans ?_
      have hNA : N ^ 2 * A ^ 2 ≤ u * p :=
        mul_le_mul hNu hpA2 (sq_nonneg A) hu0
      have hmulc : Cf034 * Cd * (N ^ 2 * A ^ 2) ≤ Cf034 * Cd * (u * p) :=
        mul_le_mul_of_nonneg_left hNA (mul_nonneg hCf034 hCd)
      calc
        Cf034 * (Cd * N ^ 2) * A ^ 2 =
            Cf034 * Cd * (N ^ 2 * A ^ 2) := by ring
        _ ≤ Cf034 * Cd * (u * p) := hmulc
        _ = Cf034 * Cd * (p * u) := by ring
    have e2 : lowJetSq (I := I) (M := M) g 1
        (appCcRS (I := I) (M := M) g 0 3 4
          (LowBaseInternal.dagLowOp (I := I) (M := M) g gU)
          (covGrad (I := I) (M := M) g 0 2 (P - Q))) ≤
        2 * (Ca034 * Kdag) * (p * u) := by
      refine (h034a _ _).trans ?_
      have hstep : Ca034 * lowJetSq (I := I) (M := M) g 2
            (LowBaseInternal.dagLowOp (I := I) (M := M) g gU) *
          lowJetSq (I := I) (M := M) g 1
            (covGrad (I := I) (M := M) g 0 2 (P - Q)) ≤
          Ca034 * (Kdag * (1 + A ^ 2)) * D2 ^ 2 :=
        mul_le_mul (mul_le_mul_of_nonneg_left hdagU hCa034) hgd1
          (jet_nonneg_lip (I := I) (M := M) (m := 1) g _)
          (mul_nonneg hCa034 (mul_nonneg hKdag (by positivity)))
      refine hstep.trans ?_
      have h1 : (1 : ℝ) + A ^ 2 ≤ 2 * p := by linarith only [hp1, hpA2]
      have h2 : (1 + A ^ 2) * D2 ^ 2 ≤ 2 * p * D2 ^ 2 :=
        mul_le_mul_of_nonneg_right h1 (sq_nonneg D2)
      have h3 : 2 * p * D2 ^ 2 ≤ 2 * p * u :=
        mul_le_mul_of_nonneg_left hDu (by linarith only [hp0])
      have hAD : (1 + A ^ 2) * D2 ^ 2 ≤ 2 * (p * u) := by
        linarith only [h2, h3]
      have hmulc : Ca034 * Kdag * ((1 + A ^ 2) * D2 ^ 2) ≤
          Ca034 * Kdag * (2 * (p * u)) :=
        mul_le_mul_of_nonneg_left hAD (mul_nonneg hCa034 hKdag)
      calc
        Ca034 * (Kdag * (1 + A ^ 2)) * D2 ^ 2 =
            Ca034 * Kdag * ((1 + A ^ 2) * D2 ^ 2) := by ring
        _ ≤ Ca034 * Kdag * (2 * (p * u)) := hmulc
        _ = 2 * (Ca034 * Kdag) * (p * u) := by ring
    refine (jet_add_lip (I := I) (M := M) g 1 _ _).trans ?_
    simp only [c1]
    linarith only [e1, e2]
  have hGU2 : lowJetSq (I := I) (M := M) g 2 GU ≤ c2 * p ^ 2 := by
    rw [hGU]
    refine (h034b _ _).trans ?_
    have hstep : Cb034 * lowJetSq (I := I) (M := M) g 2
          (LowBaseInternal.dagLowOp (I := I) (M := M) g gU) *
        lowJetSq (I := I) (M := M) g 2
          (covGrad (I := I) (M := M) g 0 2 Q) ≤
        Cb034 * (Kdag * (1 + A ^ 2)) * A ^ 2 :=
      mul_le_mul (mul_le_mul_of_nonneg_left hdagU hCb034) hgQ2
        (jet_nonneg_lip (I := I) (M := M) (m := 2) g _)
        (mul_nonneg hCb034 (mul_nonneg hKdag (by positivity)))
    refine hstep.trans ?_
    have h1 : (1 : ℝ) + A ^ 2 ≤ 2 * p := by linarith only [hp1, hpA2]
    have h2 : (1 + A ^ 2) * A ^ 2 ≤ 2 * p * A ^ 2 :=
      mul_le_mul_of_nonneg_right h1 (sq_nonneg A)
    have h3 : 2 * p * A ^ 2 ≤ 2 * p * p :=
      mul_le_mul_of_nonneg_left hpA2 (by linarith only [hp0])
    have hAA : (1 + A ^ 2) * A ^ 2 ≤ 2 * p ^ 2 := by
      linarith only [h2, h3]
    have hmulc : Cb034 * Kdag * ((1 + A ^ 2) * A ^ 2) ≤
        Cb034 * Kdag * (2 * p ^ 2) :=
      mul_le_mul_of_nonneg_left hAA (mul_nonneg hCb034 hKdag)
    simp only [c2]
    calc
      Cb034 * (Kdag * (1 + A ^ 2)) * A ^ 2 =
          Cb034 * Kdag * ((1 + A ^ 2) * A ^ 2) := by ring
      _ ≤ Cb034 * Kdag * (2 * p ^ 2) := hmulc
      _ = 2 * (Cb034 * Kdag) * p ^ 2 := by ring
  -- ## the endomorphism slot factors
  have hETb : lowJetSq (I := I) (M := M) g 2 ET ≤ Be R ^ 2 := by
    rw [hET]
    exact hfsb gT P hP hPtie hδ_le hδ0 hδP R hR hP2
  have hEd : lowJetSq (I := I) (M := M) g 1 (ET - EU) ≤
      (2 * Be0 R ^ 2 + 2 * Be1 R ^ 2) * (p * u) := by
    rw [hET, hEU]
    refine (hfsd gT gU P Q hP hQ hPtie hQtie hδ_le hδ0 hδP hδ_le hδ0 hδQ
      R A D2 hR hA hD2 hQ2 hP3 hPQ2).trans ?_
    have hstep : (Be0 R * D2 + Be1 R * A * D2) ^ 2 ≤
        2 * Be0 R ^ 2 * D2 ^ 2 + 2 * Be1 R ^ 2 * (A ^ 2 * D2 ^ 2) := by
      linarith only [sq_nonneg (Be0 R * D2 - Be1 R * A * D2)]
    refine hstep.trans ?_
    have e1 : D2 ^ 2 ≤ p * u := by linarith only [hDu, huple]
    have e2 : A ^ 2 * D2 ^ 2 ≤ p * u :=
      mul_le_mul hpA2 hDu (sq_nonneg D2) hp0
    have f1 : 2 * Be0 R ^ 2 * D2 ^ 2 ≤ 2 * Be0 R ^ 2 * (p * u) :=
      mul_le_mul_of_nonneg_left e1 (by positivity)
    have f2 : 2 * Be1 R ^ 2 * (A ^ 2 * D2 ^ 2) ≤
        2 * Be1 R ^ 2 * (p * u) :=
      mul_le_mul_of_nonneg_left e2 (by positivity)
    linarith only [f1, f2]
  -- ## the two contraction monomials
  have hmono : ∀ σ : Equiv.Perm (Fin 4),
      lowJetSq (I := I) (M := M) g 1
        (LowBaseInternal.daMono (I := I) (M := M) g gT GT σ -
          LowBaseInternal.daMono (I := I) (M := M) g gU GU σ) ≤
        2 * (D1 R * (p * u) + D2c R * (p ^ 3 * u)) := by
    intro σ
    have hfT : LowBaseInternal.daMono (I := I) (M := M) g gT GT σ =
        appCcRS (I := I) (M := M) g 2 2 2
          (refoldKernelContractionMonomialField (I := I) (M := M) g g GT σ)
          ET := by rw [hET]; rfl
    have hfU : LowBaseInternal.daMono (I := I) (M := M) g gU GU σ =
        appCcRS (I := I) (M := M) g 2 2 2
          (refoldKernelContractionMonomialField (I := I) (M := M) g g GU σ)
          EU := by rw [hEU]; rfl
    have hsub : LowBaseInternal.daMono (I := I) (M := M) g gT GT σ -
          LowBaseInternal.daMono (I := I) (M := M) g gU GU σ =
        appCcRS (I := I) (M := M) g 2 2 2
            (refoldKernelContractionMonomialField (I := I) (M := M) g g
              (GT - GU) σ) ET +
          appCcRS (I := I) (M := M) g 2 2 2
            (refoldKernelContractionMonomialField (I := I) (M := M) g g GU σ)
            (ET - EU) := by
      rw [hfT, hfU, refold_sub_lip, appCcRS_sub_left, appCcRS_sub_right]
      module
    rw [hsub]
    have e1 : lowJetSq (I := I) (M := M) g 1
        (appCcRS (I := I) (M := M) g 2 2 2
          (refoldKernelContractionMonomialField (I := I) (M := M) g g
            (GT - GU) σ) ET) ≤ D1 R * (p * u) := by
      refine (h222f _ _).trans ?_
      have hr : lowJetSq (I := I) (M := M) g 1
          (refoldKernelContractionMonomialField (I := I) (M := M) g g
            (GT - GU) σ) ≤ Kr1 * (c1 * (p * u)) :=
        (hrf1 (GT - GU) σ).trans (mul_le_mul_of_nonneg_left hGd hKr1)
      have hstep : Cf222 * lowJetSq (I := I) (M := M) g 1
            (refoldKernelContractionMonomialField (I := I) (M := M) g g
              (GT - GU) σ) *
          lowJetSq (I := I) (M := M) g 2 ET ≤
          Cf222 * (Kr1 * (c1 * (p * u))) * Be R ^ 2 :=
        mul_le_mul (mul_le_mul_of_nonneg_left hr hCf222) hETb
          (jet_nonneg_lip (I := I) (M := M) (m := 2) g _)
          (mul_nonneg hCf222 (mul_nonneg hKr1 (mul_nonneg hc10 hpu0)))
      refine hstep.trans ?_
      simp only [D1]
      apply le_of_eq
      ring
    have e2 : lowJetSq (I := I) (M := M) g 1
        (appCcRS (I := I) (M := M) g 2 2 2
          (refoldKernelContractionMonomialField (I := I) (M := M) g g GU σ)
          (ET - EU)) ≤ D2c R * (p ^ 3 * u) := by
      refine (h222a _ _).trans ?_
      have hr : lowJetSq (I := I) (M := M) g 2
          (refoldKernelContractionMonomialField (I := I) (M := M) g g GU σ) ≤
          Kr2 * (c2 * p ^ 2) :=
        (hrf2 GU σ).trans (mul_le_mul_of_nonneg_left hGU2 hKr2)
      have hstep : Ca222 * lowJetSq (I := I) (M := M) g 2
            (refoldKernelContractionMonomialField (I := I) (M := M) g g
              GU σ) *
          lowJetSq (I := I) (M := M) g 1 (ET - EU) ≤
          Ca222 * (Kr2 * (c2 * p ^ 2)) *
            ((2 * Be0 R ^ 2 + 2 * Be1 R ^ 2) * (p * u)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hr hCa222) hEd
          (jet_nonneg_lip (I := I) (M := M) (m := 1) g _)
          (mul_nonneg hCa222
            (mul_nonneg hKr2 (mul_nonneg hc20 (sq_nonneg p))))
      refine hstep.trans ?_
      simp only [D2c]
      apply le_of_eq
      ring
    refine (jet_add_lip (I := I) (M := M) g 1 _ _).trans ?_
    linarith only [e1, e2]
  -- ## assemble the two monomials
  have hDAT : LowBaseInternal.ricciDALow (I := I) (M := M) g gT P =
      LowBaseInternal.daMono (I := I) (M := M) g gT GT
          LowBaseInternal.daPermA -
        LowBaseInternal.daMono (I := I) (M := M) g gT GT
          LowBaseInternal.daPermB := by
    rw [hGT]; rfl
  have hDAU : LowBaseInternal.ricciDALow (I := I) (M := M) g gU Q =
      LowBaseInternal.daMono (I := I) (M := M) g gU GU
          LowBaseInternal.daPermA -
        LowBaseInternal.daMono (I := I) (M := M) g gU GU
          LowBaseInternal.daPermB := by
    rw [hGU]; rfl
  have hsplit : LowBaseInternal.ricciDALow (I := I) (M := M) g gT P -
        LowBaseInternal.ricciDALow (I := I) (M := M) g gU Q =
      (LowBaseInternal.daMono (I := I) (M := M) g gT GT
            LowBaseInternal.daPermA -
          LowBaseInternal.daMono (I := I) (M := M) g gU GU
            LowBaseInternal.daPermA) -
        (LowBaseInternal.daMono (I := I) (M := M) g gT GT
            LowBaseInternal.daPermB -
          LowBaseInternal.daMono (I := I) (M := M) g gU GU
            LowBaseInternal.daPermB) := by
    rw [hDAT, hDAU]
    abel
  rw [hsplit]
  refine (jet_sub_lip (I := I) (M := M) g 1 _ _).trans ?_
  have hA' := hmono LowBaseInternal.daPermA
  have hB' := hmono LowBaseInternal.daPermB
  have hfold : D1 R * (p * u) + D2c R * (p ^ 3 * u) ≤
      (D1 R + D2c R) * (p ^ 4 * u) := by
    have e1 : D1 R * (p * u) ≤ D1 R * (p ^ 4 * u) :=
      mul_le_mul_of_nonneg_left hpu (hD10 R)
    have e2 : D2c R * (p ^ 3 * u) ≤ D2c R * (p ^ 4 * u) :=
      mul_le_mul_of_nonneg_left hp3u (hD2c0 R)
    have e3 : (D1 R + D2c R) * (p ^ 4 * u) =
        D1 R * (p ^ 4 * u) + D2c R * (p ^ 4 * u) := by ring
    rw [e3]
    exact add_le_add e1 e2
  have hlast : (8 : ℝ) * ((D1 R + D2c R) * (p ^ 4 * u)) =
      B R * ((1 + A + A ^ 2) ^ 4 * (D2 ^ 2 + N ^ 2)) := by
    simp only [B, hp, hu]
    ring
  refine le_trans ?_ (le_of_eq hlast)
  linarith only [hA', hB', hfold]

/-! ### Capstone — class 1 of the `C0` `H¹` five-class telescope -/

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 1000000 in
set_option linter.unusedVariables false in
/-- **Class 1 of the `C0` `H¹` five-class telescope.**  On a common spectral
`H²` ball the symmetrized first-order Ricci coefficient `ricciGoodLow` is
`H¹`-Lipschitz along the realized family, with only the `H²` state difference
`D2` and the `Hˢ` difference `N` on the right and the third-jet size `A`
entering polynomially. -/
private theorem good_pair_h1
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ : ℝ, ∃ B : ℝ → ℝ,
      0 < ρ ∧ (∀ R : ℝ, 0 ≤ R → 0 ≤ B R) ∧
      ∀ (T U : SmoothCcTensor g 0 2)
        (hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        (hU : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g U x u v =
            ccTensorBilin (I := I) g U x v u)
        {δ : ℝ} (hδ_le : δ ≤ 1 / 3) (hδ0 : 0 ≤ δ)
        (hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδU : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g U) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        (R A D2 N : ℝ), 0 ≤ R → 0 ≤ A → 0 ≤ D2 → 0 ≤ N →
        lowJetSq (I := I) (M := M) g 2 T ≤ R ^ 2 →
        lowJetSq (I := I) (M := M) g 2 U ≤ R ^ 2 →
        lowJetSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
        lowJetSq (I := I) (M := M) g 3 U ≤ A ^ 2 →
        lowJetSq (I := I) (M := M) g 2 (T - U) ≤ D2 ^ 2 →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U)‖ ≤ N →
        ∀ {s : ℝ}, s ∈ Set.Icc (0 : ℝ) 1 →
      lowJetSq (I := I) (M := M) g 1
          (LowBaseInternal.ricciGoodLow (I := I) (M := M) g
              (realizedFam (I := I) g T 0 hδT hδZ s) (s • T) -
            LowBaseInternal.ricciGoodLow (I := I) (M := M) g
              (realizedFam (I := I) g U 0 hδU hδZ s) (s • U)) ≤
        B R * ((1 + A + A ^ 2) ^ 4 * (D2 ^ 2 + N ^ 2)) := by
  obtain ⟨Ks, hKs, hsymm⟩ := inputSymm_h1 (I := I) (M := M) hDim g
  obtain ⟨ρA, BA, hρA, hBA, haa⟩ := ricciAA_pair_h1 (I := I) (M := M) hDim g
  obtain ⟨ρD, BD, hρD, hBD, hda⟩ := ricciDA_pair_h1 (I := I) (M := M) hDim g
  let B : ℝ → ℝ := fun R => Ks * (2 * (BA R + BD R))
  refine ⟨min ρA ρD, B, lt_min hρA hρD, ?_, ?_⟩
  · intro R hR
    have e1 := hBA R hR
    have e2 := hBD R hR
    simp only [B]
    positivity
  intro T U hT hU δ hδ_le hδ0 hδT hδU hδZ
    R A D2 N hR hA hD2 hN hT2 hU2 hT3 hU3 hTU2 hTn hUn hTUn s hs
  ------------------------------------------------------------------
  -- ## standard plumbing block
  ------------------------------------------------------------------
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le (by norm_num)
  set gmT : SmoothRiemannianMetric I M :=
    realizedFam (I := I) g T 0 hδT hδZ s with hgmT
  set gmU : SmoothRiemannianMetric I M :=
    realizedFam (I := I) g U 0 hδU hδZ s with hgmU
  set P : SmoothCcTensor g 0 2 := s • T with hcP
  set Q : SmoothCcTensor g 0 2 := s • U with hcQ
  have hs_mem : s ∈ realizedSmallSet (δ := δ) (δ' := δ) :=
    Icc_subset_realizedSmallSet hδ_lt hδ_lt hs
  have hsabs : ‖s‖ ≤ (1 : ℝ) := by
    rw [Real.norm_eq_abs, abs_of_nonneg hs.1]
    exact hs.2
  have hs2 : s ^ 2 ≤ (1 : ℝ) := by
    nlinarith [hs.1, hs.2]
  have hPsymm : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g P x u v =
        ccTensorBilin (I := I) g P x v u := by
    intro x u v
    simp only [hcP, ccTensorBilin_apply, ccTensorModel_smul,
      ContinuousMultilinearMap.smul_apply, smul_eq_mul]
    apply congrArg (fun z : ℝ => s * z)
    simpa only [ccTensorBilin_apply] using hT x u v
  have hQsymm : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g Q x u v =
        ccTensorBilin (I := I) g Q x v u := by
    intro x u v
    simp only [hcQ, ccTensorBilin_apply, ccTensorModel_smul,
      ContinuousMultilinearMap.smul_apply, smul_eq_mul]
    apply congrArg (fun z : ℝ => s * z)
    simpa only [ccTensorBilin_apply] using hU x u v
  have hPtie : ∀ (x : M) (u v : TangentSpace I x),
      gmT.inner x u v =
        g.inner x u v + ccTensorBilinSymm (I := I) g P x u v := by
    intro x u v
    simpa only [hgmT, hcP, convexPerturbation, smul_zero, zero_add] using
      realizedFam_inner_of_mem (I := I) g T 0 hδT hδZ hs_mem x u v
  have hQtie : ∀ (x : M) (u v : TangentSpace I x),
      gmU.inner x u v =
        g.inner x u v + ccTensorBilinSymm (I := I) g Q x u v := by
    intro x u v
    simpa only [hgmU, hcQ, convexPerturbation, smul_zero, zero_add] using
      realizedFam_inner_of_mem (I := I) g U 0 hδU hδZ hs_mem x u v
  have hδP : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g P) δ := by
    intro x u v
    have hraw :=
      convexPerturbation_gFibreOpBound_abs (I := I) g T 0 hδT hδZ s x u v
    have heq : |1 - s| * δ + |s| * δ = δ := by
      rw [abs_of_nonneg (by linarith [hs.2] : (0 : ℝ) ≤ 1 - s),
        abs_of_nonneg hs.1]
      ring
    simpa only [hcP, convexPerturbation, smul_zero, zero_add, heq] using hraw
  have hδQ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g Q) δ := by
    intro x u v
    have hraw :=
      convexPerturbation_gFibreOpBound_abs (I := I) g U 0 hδU hδZ s x u v
    have heq : |1 - s| * δ + |s| * δ = δ := by
      rw [abs_of_nonneg (by linarith [hs.2] : (0 : ℝ) ≤ 1 - s),
        abs_of_nonneg hs.1]
      ring
    simpa only [hcQ, convexPerturbation, smul_zero, zero_add, heq] using hraw
  have hP2 : lowJetSq (I := I) (M := M) g 2 P ≤ R ^ 2 := by
    rw [hcP, jet_smul_lip]
    exact (mul_le_of_le_one_left
      (jet_nonneg_lip (I := I) (M := M) (m := 2) g T) hs2).trans hT2
  have hQ2 : lowJetSq (I := I) (M := M) g 2 Q ≤ R ^ 2 := by
    rw [hcQ, jet_smul_lip]
    exact (mul_le_of_le_one_left
      (jet_nonneg_lip (I := I) (M := M) (m := 2) g U) hs2).trans hU2
  have hP3 : lowJetSq (I := I) (M := M) g 3 P ≤ A ^ 2 := by
    rw [hcP, jet_smul_lip]
    exact (mul_le_of_le_one_left
      (jet_nonneg_lip (I := I) (M := M) (m := 3) g T) hs2).trans hT3
  have hQ3 : lowJetSq (I := I) (M := M) g 3 Q ≤ A ^ 2 := by
    rw [hcQ, jet_smul_lip]
    exact (mul_le_of_le_one_left
      (jet_nonneg_lip (I := I) (M := M) (m := 3) g U) hs2).trans hU3
  have hPQ2 : lowJetSq (I := I) (M := M) g 2 (P - Q) ≤ D2 ^ 2 := by
    have hPQ : P - Q = s • (T - U) := by rw [hcP, hcQ, smul_sub]
    rw [hPQ, jet_smul_lip]
    exact (mul_le_of_le_one_left
      (jet_nonneg_lip (I := I) (M := M) (m := 2) g (T - U)) hs2).trans hTU2
  have hball : ∀ ρ' : ℝ, min ρA ρD ≤ ρ' →
      (‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) P‖ ≤ ρ' ∧
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) Q‖ ≤ ρ') := by
    intro ρ' hρ'
    constructor
    · rw [hcP, ccTensorToHs_smul, norm_smul]
      exact (mul_le_mul_of_nonneg_right hsabs (norm_nonneg _)).trans
        (by simpa using (hTn.trans hρ'))
    · rw [hcQ, ccTensorToHs_smul, norm_smul]
      exact (mul_le_mul_of_nonneg_right hsabs (norm_nonneg _)).trans
        (by simpa using (hUn.trans hρ'))
  have hPQn : ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (P - Q)‖ ≤ N := by
    have hPQ : P - Q = s • (T - U) := by rw [hcP, hcQ, smul_sub]
    rw [hPQ, ccTensorToHs_smul, norm_smul]
    exact (mul_le_mul_of_nonneg_right hsabs (norm_nonneg _)).trans
      (by simpa using hTUn)
  obtain ⟨hPnA, hQnA⟩ := hball ρA (min_le_left _ _)
  obtain ⟨hPnD, hQnD⟩ := hball ρD (min_le_right _ _)
  ------------------------------------------------------------------
  -- ## the two arms
  ------------------------------------------------------------------
  set Z : ℝ := (1 + A + A ^ 2) ^ 4 * (D2 ^ 2 + N ^ 2) with hZ
  have hAA : lowJetSq (I := I) (M := M) g 1
      (ricciAAArm (I := I) (M := M) g gmT -
        ricciAAArm (I := I) (M := M) g gmU) ≤ BA R * Z := by
    rw [hZ]
    exact haa gmT gmU P Q hPsymm hQsymm hPtie hQtie hδ_le hδ0 hδP hδQ hδZ
      R A D2 N hR hA hD2 hN hP2 hQ2 hP3 hQ3 hPQ2 hPnA hQnA hPQn
  have hDA : lowJetSq (I := I) (M := M) g 1
      (LowBaseInternal.ricciDALow (I := I) (M := M) g gmT P -
        LowBaseInternal.ricciDALow (I := I) (M := M) g gmU Q) ≤
      BD R * Z := by
    rw [hZ]
    exact hda gmT gmU P Q hPsymm hQsymm hPtie hQtie hδ_le hδ0 hδP hδQ
      R A D2 N hR hA hD2 hN hP2 hQ2 hP3 hQ3 hPQ2 hPnD hQnD hPQn
  ------------------------------------------------------------------
  -- ## symmetrizer + two-term ladder
  ------------------------------------------------------------------
  have hlowT : LowBaseInternal.ricciLow (I := I) (M := M) g gmT P =
      ricciAAArm (I := I) (M := M) g gmT +
        LowBaseInternal.ricciDALow (I := I) (M := M) g gmT P := rfl
  have hlowU : LowBaseInternal.ricciLow (I := I) (M := M) g gmU Q =
      ricciAAArm (I := I) (M := M) g gmU +
        LowBaseInternal.ricciDALow (I := I) (M := M) g gmU Q := rfl
  have hgoodT : LowBaseInternal.ricciGoodLow (I := I) (M := M) g gmT P =
      ccInputSymm (I := I) (M := M) g
        (LowBaseInternal.ricciLow (I := I) (M := M) g gmT P) := rfl
  have hgoodU : LowBaseInternal.ricciGoodLow (I := I) (M := M) g gmU Q =
      ccInputSymm (I := I) (M := M) g
        (LowBaseInternal.ricciLow (I := I) (M := M) g gmU Q) := rfl
  have hlow : LowBaseInternal.ricciLow (I := I) (M := M) g gmT P -
        LowBaseInternal.ricciLow (I := I) (M := M) g gmU Q =
      (ricciAAArm (I := I) (M := M) g gmT -
          ricciAAArm (I := I) (M := M) g gmU) +
        (LowBaseInternal.ricciDALow (I := I) (M := M) g gmT P -
          LowBaseInternal.ricciDALow (I := I) (M := M) g gmU Q) := by
    rw [hlowT, hlowU]
    abel
  have hgood : LowBaseInternal.ricciGoodLow (I := I) (M := M) g gmT P -
        LowBaseInternal.ricciGoodLow (I := I) (M := M) g gmU Q =
      ccInputSymm (I := I) (M := M) g
        ((ricciAAArm (I := I) (M := M) g gmT -
            ricciAAArm (I := I) (M := M) g gmU) +
          (LowBaseInternal.ricciDALow (I := I) (M := M) g gmT P -
            LowBaseInternal.ricciDALow (I := I) (M := M) g gmU Q)) := by
    rw [hgoodT, hgoodU, ccSymm_sub_lip, hlow]
  rw [hgood]
  have hZ0 : (0 : ℝ) ≤ Z := by rw [hZ]; positivity
  calc
    lowJetSq (I := I) (M := M) g 1
        (ccInputSymm (I := I) (M := M) g
          ((ricciAAArm (I := I) (M := M) g gmT -
              ricciAAArm (I := I) (M := M) g gmU) +
            (LowBaseInternal.ricciDALow (I := I) (M := M) g gmT P -
              LowBaseInternal.ricciDALow (I := I) (M := M) g gmU Q))) ≤
        Ks * lowJetSq (I := I) (M := M) g 1
          ((ricciAAArm (I := I) (M := M) g gmT -
              ricciAAArm (I := I) (M := M) g gmU) +
            (LowBaseInternal.ricciDALow (I := I) (M := M) g gmT P -
              LowBaseInternal.ricciDALow (I := I) (M := M) g gmU Q)) :=
      hsymm _
    _ ≤ Ks * (2 * (lowJetSq (I := I) (M := M) g 1
          (ricciAAArm (I := I) (M := M) g gmT -
            ricciAAArm (I := I) (M := M) g gmU) +
        lowJetSq (I := I) (M := M) g 1
          (LowBaseInternal.ricciDALow (I := I) (M := M) g gmT P -
            LowBaseInternal.ricciDALow (I := I) (M := M) g gmU Q))) :=
      mul_le_mul_of_nonneg_left (jet_add_lip (I := I) (M := M) g 1 _ _) hKs
    _ ≤ Ks * (2 * (BA R * Z + BD R * Z)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (add_le_add hAA hDA) (by norm_num)) hKs
    _ = B R * ((1 + A + A ^ 2) ^ 4 * (D2 ^ 2 + N ^ 2)) := by
      simp only [B, hZ]
      ring

private theorem selfLow_sub_parts
    (g : SmoothRiemannianMetric I M) (T U : SmoothCcTensor g 0 2)
    (hT : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g T x u v =
        ccTensorBilin (I := I) g T x v u)
    (hU : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g U x u v =
        ccTensorBilin (I := I) g U x v u)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδT : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδU : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g U) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ)
    {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    LowBaseInternal.rhsSelfLow (I := I) (M := M)
        g g T hδT hδZ s -
      LowBaseInternal.rhsSelfLow (I := I) (M := M)
        g g U hδU hδZ s =
      (((((-2 : ℝ) •
            (LowBaseInternal.ricciGoodLow (I := I) (M := M) g
                (realizedFam (I := I) g T 0 hδT hδZ s) (s • T) -
              LowBaseInternal.ricciGoodLow (I := I) (M := M) g
                (realizedFam (I := I) g U 0 hδU hδZ s) (s • U)) +
          ((deTurckLieCovDerivArmField (I := I) (M := M) g
              (realizedFam (I := I) g T 0 hδT hδZ s) g -
            edgeLiePairFam (I := I) (M := M) g T hδT hδZ
              lieRefoldQ lieRefoldEps s) -
          (deTurckLieCovDerivArmField (I := I) (M := M) g
              (realizedFam (I := I) g U 0 hδU hδZ s) g -
            edgeLiePairFam (I := I) (M := M) g U hδU hδZ
              lieRefoldQ lieRefoldEps s))) +
        (lc0VB (I := I) (M := M) g
            (realizedFam (I := I) g T 0 hδT hδZ s) -
          lc0VB (I := I) (M := M) g
            (realizedFam (I := I) g U 0 hδU hδZ s))) +
        (lc0AMix (I := I) (M := M) g
            (realizedFam (I := I) g T 0 hδT hδZ s) g -
          lc0AMix (I := I) (M := M) g
            (realizedFam (I := I) g U 0 hδU hδZ s) g)) +
        (lc0Riem (I := I) (M := M) g
            (realizedFam (I := I) g T 0 hδT hδZ s) -
          lc0Riem (I := I) (M := M) g
            (realizedFam (I := I) g U 0 hδU hδZ s))) := by
  rw [selfLow_parts (I := I) (M := M) g T hT hδ_lt hδT hδZ hs,
    selfLow_parts (I := I) (M := M) g U hU hδ_lt hδU hδZ hs]
  dsimp only
  module

set_option maxHeartbeats 3200000 in
set_option linter.unusedVariables false in
/-- **The five-class master telescope at fixed `s`.**  On a common spectral
`H²` ball the transparent self-action family difference is `H¹`-Lipschitz
with the uniform `(1+A+A²)⁴·(D2²+N²)` modulus. -/
private theorem selfLow_pair_h1
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ : ℝ, ∃ B : ℝ → ℝ,
      0 < ρ ∧ (∀ R : ℝ, 0 ≤ R → 0 ≤ B R) ∧
      ∀ (T U : SmoothCcTensor g 0 2)
        (hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        (hU : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g U x u v =
            ccTensorBilin (I := I) g U x v u)
        {δ : ℝ} (hδ_le : δ ≤ 1 / 3) (hδ0 : 0 ≤ δ)
        (hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδU : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g U) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        (R A D2 N : ℝ), 0 ≤ R → 0 ≤ A → 0 ≤ D2 → 0 ≤ N →
        lowJetSq (I := I) (M := M) g 2 T ≤ R ^ 2 →
        lowJetSq (I := I) (M := M) g 2 U ≤ R ^ 2 →
        lowJetSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
        lowJetSq (I := I) (M := M) g 3 U ≤ A ^ 2 →
        lowJetSq (I := I) (M := M) g 2 (T - U) ≤ D2 ^ 2 →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U)‖ ≤ N →
        ∀ {s : ℝ}, s ∈ Set.Icc (0 : ℝ) 1 →
      lowJetSq (I := I) (M := M) g 1
          (LowBaseInternal.rhsSelfLow (I := I) (M := M)
              g g T hδT hδZ s -
            LowBaseInternal.rhsSelfLow (I := I) (M := M)
              g g U hδU hδZ s) ≤
        B R * ((1 + A + A ^ 2) ^ 4 * (D2 ^ 2 + N ^ 2)) := by
  obtain ⟨ρg, Bg, hρg, hBg, hgood⟩ :=
    good_pair_h1 (I := I) (M := M) hDim g
  obtain ⟨ρl, Bl, hρl, hBl, hlie⟩ :=
    lieCov_pair_h1 (I := I) (M := M) hDim g
  obtain ⟨ρv, Bv, hρv, hBv, hvb⟩ :=
    vb_pair_h1 (I := I) (M := M) hDim g
  obtain ⟨ρa, Ba, hρa, hBa, hamix⟩ :=
    amix_pair_h1 (I := I) (M := M) hDim g
  obtain ⟨ρr, Cr, hρr, hCr, hriem⟩ :=
    riem_pair_h1 (I := I) (M := M) hDim g
  set ρ : ℝ := min (min ρg ρl) (min ρv (min ρa ρr)) with hρdef
  have hρ0 : 0 < ρ :=
    lt_min (lt_min hρg hρl) (lt_min hρv (lt_min hρa hρr))
  let B : ℝ → ℝ := fun R =>
    64 * Bg R + 16 * Bl R + 8 * Bv R + 4 * Ba R + 2 * Cr ^ 2
  refine ⟨ρ, B, hρ0, ?_, ?_⟩
  · intro R hR
    have h1 := hBg R hR
    have h2 := hBl R hR
    have h3 := hBv R hR
    have h4 := hBa R hR
    have h5 : (0 : ℝ) ≤ Cr ^ 2 := sq_nonneg _
    simp only [B]
    linarith
  intro T U hT hU δ hδ_le hδ0 hδT hδU hδZ
    R A D2 N hR hA hD2 hN hT2 hU2 hT3 hU3 hTU2 hTn hUn hTUn s hs
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le (by norm_num)
  have hρc : ρ ≤ ρg ∧ ρ ≤ ρl ∧ ρ ≤ ρv ∧ ρ ≤ ρa ∧ ρ ≤ ρr := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
      · rw [hρdef]
        first
        | exact le_trans (min_le_left _ _) (min_le_left _ _)
        | exact le_trans (min_le_left _ _) (min_le_right _ _)
        | exact le_trans (min_le_right _ _) (min_le_left _ _)
        | exact le_trans (min_le_right _ _)
            (le_trans (min_le_right _ _) (min_le_left _ _))
        | exact le_trans (min_le_right _ _)
            (le_trans (min_le_right _ _) (min_le_right _ _))
  have hXg := hgood T U hT hU hδ_le hδ0 hδT hδU hδZ
    R A D2 N hR hA hD2 hN hT2 hU2 hT3 hU3 hTU2
    (hTn.trans hρc.1) (hUn.trans hρc.1) hTUn hs
  have hXl := hlie T U hT hU hδ_le hδ0 hδT hδU hδZ
    R A D2 N hR hA hD2 hN hT2 hU2 hT3 hU3 hTU2
    (hTn.trans hρc.2.1) (hUn.trans hρc.2.1) hTUn hs
  have hXv := hvb T U hT hU hδ_le hδ0 hδT hδU hδZ
    R A D2 N hR hA hD2 hN hT2 hU2 hT3 hU3 hTU2
    (hTn.trans hρc.2.2.1) (hUn.trans hρc.2.2.1) hTUn hs
  have hXa := hamix T U hT hU hδ_le hδ0 hδT hδU hδZ
    R A D2 N hR hA hD2 hN hT2 hU2 hT3 hU3 hTU2
    (hTn.trans hρc.2.2.2.1) (hUn.trans hρc.2.2.2.1) hTUn hs
  -- riem needs the (P,Q) plumbing
  set gmT : SmoothRiemannianMetric I M :=
    realizedFam (I := I) g T 0 hδT hδZ s with hgmT
  set gmU : SmoothRiemannianMetric I M :=
    realizedFam (I := I) g U 0 hδU hδZ s with hgmU
  set P : SmoothCcTensor g 0 2 := s • T with hcP
  set Q : SmoothCcTensor g 0 2 := s • U with hcQ
  have hs_mem : s ∈ realizedSmallSet (δ := δ) (δ' := δ) :=
    Icc_subset_realizedSmallSet hδ_lt hδ_lt hs
  have hsabs : ‖s‖ ≤ (1 : ℝ) := by
    rw [Real.norm_eq_abs, abs_of_nonneg hs.1]
    exact hs.2
  have hPtie : ∀ (x : M) (u v : TangentSpace I x),
      gmT.inner x u v =
        g.inner x u v + ccTensorBilinSymm (I := I) g P x u v := by
    intro x u v
    simpa only [hgmT, hcP, convexPerturbation, smul_zero, zero_add] using
      realizedFam_inner_of_mem (I := I) g T 0 hδT hδZ hs_mem x u v
  have hQtie : ∀ (x : M) (u v : TangentSpace I x),
      gmU.inner x u v =
        g.inner x u v + ccTensorBilinSymm (I := I) g Q x u v := by
    intro x u v
    simpa only [hgmU, hcQ, convexPerturbation, smul_zero, zero_add] using
      realizedFam_inner_of_mem (I := I) g U 0 hδU hδZ hs_mem x u v
  have hPn : ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) P‖ ≤ ρr := by
    rw [hcP, ccTensorToHs_smul, norm_smul]
    exact (mul_le_mul_of_nonneg_right hsabs (norm_nonneg _)).trans
      (by simpa using (hTn.trans hρc.2.2.2.2))
  have hQn : ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) Q‖ ≤ ρr := by
    rw [hcQ, ccTensorToHs_smul, norm_smul]
    exact (mul_le_mul_of_nonneg_right hsabs (norm_nonneg _)).trans
      (by simpa using (hUn.trans hρc.2.2.2.2))
  have hPQn : ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (P - Q)‖ ≤
      N := by
    have hPQ : P - Q = s • (T - U) := by
      rw [hcP, hcQ, smul_sub]
    rw [hPQ, ccTensorToHs_smul, norm_smul]
    exact (mul_le_mul_of_nonneg_right hsabs (norm_nonneg _)).trans
      (by simpa using hTUn)
  have hpl1 : (1 : ℝ) ≤ (1 + A + A ^ 2) ^ 4 := by
    have hb1 : (1 : ℝ) ≤ 1 + A + A ^ 2 := by
      nlinarith [hA, sq_nonneg A]
    calc (1 : ℝ) = 1 ^ 4 := by norm_num
      _ ≤ (1 + A + A ^ 2) ^ 4 :=
        pow_le_pow_left₀ zero_le_one hb1 4
  have hXr : lowJetSq (I := I) (M := M) g 1
      (lc0Riem (I := I) (M := M) g gmT -
        lc0Riem (I := I) (M := M) g gmU) ≤
      Cr ^ 2 * ((1 + A + A ^ 2) ^ 4 * (D2 ^ 2 + N ^ 2)) := by
    refine (hriem P Q gmT gmU hPtie hQtie hPn hQn).trans ?_
    have h1 : Cr * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
        (P - Q)‖ ≤ Cr * N :=
      mul_le_mul_of_nonneg_left hPQn hCr
    have h2 : (Cr * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
        (P - Q)‖) ^ 2 ≤ (Cr * N) ^ 2 :=
      pow_le_pow_left₀ (mul_nonneg hCr (norm_nonneg _)) h1 2
    refine h2.trans ?_
    have hN2 : (Cr * N) ^ 2 = Cr ^ 2 * N ^ 2 := by ring
    rw [hN2]
    have hstep : N ^ 2 ≤ (1 + A + A ^ 2) ^ 4 * (D2 ^ 2 + N ^ 2) := by
      nlinarith [hpl1, sq_nonneg D2, sq_nonneg N,
        mul_nonneg (le_trans zero_le_one hpl1)
          (add_nonneg (sq_nonneg D2) (sq_nonneg N))]
    exact mul_le_mul_of_nonneg_left hstep (sq_nonneg _)
  rw [selfLow_sub_parts (I := I) (M := M) g T U hT hU
    hδ_lt hδT hδU hδZ hs]
  set Y1 : SmoothCcTensor g 2 2 :=
    (-2 : ℝ) •
      (LowBaseInternal.ricciGoodLow (I := I) (M := M) g gmT P -
        LowBaseInternal.ricciGoodLow (I := I) (M := M) g gmU Q)
    with hY1
  set Y2 : SmoothCcTensor g 2 2 :=
    (deTurckLieCovDerivArmField (I := I) (M := M) g gmT g -
        edgeLiePairFam (I := I) (M := M) g T hδT hδZ
          lieRefoldQ lieRefoldEps s) -
      (deTurckLieCovDerivArmField (I := I) (M := M) g gmU g -
        edgeLiePairFam (I := I) (M := M) g U hδU hδZ
          lieRefoldQ lieRefoldEps s) with hY2
  set Y3 : SmoothCcTensor g 2 2 :=
    lc0VB (I := I) (M := M) g gmT -
      lc0VB (I := I) (M := M) g gmU with hY3
  set Y4 : SmoothCcTensor g 2 2 :=
    lc0AMix (I := I) (M := M) g gmT g -
      lc0AMix (I := I) (M := M) g gmU g with hY4
  set Y5 : SmoothCcTensor g 2 2 :=
    lc0Riem (I := I) (M := M) g gmT -
      lc0Riem (I := I) (M := M) g gmU with hY5
  set X : ℝ := (1 + A + A ^ 2) ^ 4 * (D2 ^ 2 + N ^ 2) with hX
  have hX0 : 0 ≤ X := by
    rw [hX]
    positivity
  have hj1 : lowJetSq (I := I) (M := M) g 1 Y1 ≤ 4 * (Bg R * X) := by
    rw [hY1]
    rw [jet_smul_lip]
    have h4 : ((-2 : ℝ)) ^ 2 = 4 := by norm_num
    rw [h4]
    linarith [hXg]
  have hj2 : lowJetSq (I := I) (M := M) g 1 Y2 ≤ Bl R * X := by
    rw [hY2]
    exact hXl
  have hj3 : lowJetSq (I := I) (M := M) g 1 Y3 ≤ Bv R * X := by
    rw [hY3]
    exact hXv
  have hj4 : lowJetSq (I := I) (M := M) g 1 Y4 ≤ Ba R * X := by
    rw [hY4]
    exact hXa
  have hj5 : lowJetSq (I := I) (M := M) g 1 Y5 ≤ Cr ^ 2 * X := by
    rw [hY5]
    exact hXr
  have h12 : lowJetSq (I := I) (M := M) g 1 (Y1 + Y2) ≤
      2 * (4 * (Bg R * X) + Bl R * X) := by
    have hadd := jet_add_lip (I := I) (M := M) g 1 Y1 Y2
    linarith [hj1, hj2, hadd]
  have h123 : lowJetSq (I := I) (M := M) g 1 ((Y1 + Y2) + Y3) ≤
      2 * (2 * (4 * (Bg R * X) + Bl R * X) + Bv R * X) := by
    have hadd := jet_add_lip (I := I) (M := M) g 1 (Y1 + Y2) Y3
    linarith [h12, hj3, hadd]
  have h1234 : lowJetSq (I := I) (M := M) g 1 (((Y1 + Y2) + Y3) + Y4) ≤
      2 * (2 * (2 * (4 * (Bg R * X) + Bl R * X) + Bv R * X) +
        Ba R * X) := by
    have hadd := jet_add_lip (I := I) (M := M) g 1 ((Y1 + Y2) + Y3) Y4
    linarith [h123, hj4, hadd]
  calc
    lowJetSq (I := I) (M := M) g 1 ((((Y1 + Y2) + Y3) + Y4) + Y5) ≤
      2 * (lowJetSq (I := I) (M := M) g 1 (((Y1 + Y2) + Y3) + Y4) +
        lowJetSq (I := I) (M := M) g 1 Y5) :=
      jet_add_lip (I := I) (M := M) g 1 _ _
    _ ≤ 2 * (2 * (2 * (2 * (4 * (Bg R * X) + Bl R * X) + Bv R * X) +
        Ba R * X) + Cr ^ 2 * X) := by
      linarith [h1234, hj5]
    _ = B R * X := by
      simp only [B]
      ring

set_option maxHeartbeats 3200000 in
set_option linter.unusedVariables false in
/-- **The tame `H¹` bound for the pairwise `C0` coefficient difference.**
On a common spectral `H²` ball the path-integrated transparent
self-action difference obeys the uniform low-regularity modulus
`B R · (1+A+A²)⁴ · (D2²+N²)`. -/
theorem c0Diff_tame
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ : ℝ, ∃ B : ℝ → ℝ,
      0 < ρ ∧ (∀ R : ℝ, 0 ≤ R → 0 ≤ B R) ∧
      ∀ (T U : SmoothCcTensor g 0 2)
        (hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        (hU : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g U x u v =
            ccTensorBilin (I := I) g U x v u)
        {δ : ℝ} (hδ_le : δ ≤ 1 / 3) (hδ0 : 0 ≤ δ)
        (hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδU : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g U) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        (R A D2 N : ℝ), 0 ≤ R → 0 ≤ A → 0 ≤ D2 → 0 ≤ N →
        lowJetSq (I := I) (M := M) g 2 T ≤ R ^ 2 →
        lowJetSq (I := I) (M := M) g 2 U ≤ R ^ 2 →
        lowJetSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
        lowJetSq (I := I) (M := M) g 3 U ≤ A ^ 2 →
        lowJetSq (I := I) (M := M) g 2 (T - U) ≤ D2 ^ 2 →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U)‖ ≤ N →
      lowJetSq (I := I) (M := M) g 1
          (lowC0Diff (I := I) (M := M) g T U
            (lt_of_le_of_lt hδ_le
              (by norm_num : (1 : ℝ) / 3 < 1))
            hδT hδU hδZ) ≤
        B R * ((1 + A + A ^ 2) ^ 4 * (D2 ^ 2 + N ^ 2)) := by
  obtain ⟨ρ, Bs, hρ, hBs, hker⟩ :=
    selfLow_pair_h1 (I := I) (M := M) hDim g
  refine ⟨ρ, Bs, hρ, hBs, ?_⟩
  intro T U hT hU δ hδ_le hδ0 hδT hδU hδZ
    R A D2 N hR hA hD2 hN hT2 hU2 hT3 hU3 hTU2 hTn hUn hTUn
  let hδ_lt : δ < 1 :=
    lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)
  let Φ : ℝ → SmoothCcTensor g 2 2 := fun s =>
    LowBaseInternal.rhsSelfLow (I := I) (M := M)
        g g T hδT hδZ s -
      LowBaseInternal.rhsSelfLow (I := I) (M := M)
        g g U hδU hδZ s
  let S : Set ℝ := realizedSmallSet (δ := δ) (δ' := δ)
  have hSI : Set.uIcc (0 : ℝ) 1 ⊆ S := by
    dsimp only [S]
    rw [Set.uIcc_of_le zero_le_one]
    exact Icc_subset_realizedSmallSet hδ_lt hδ_lt
  have hjoint :=
    threeArmJoint_sub (I := I) (M := M) g _ _
      (LowBaseInternal.selfLow_joint
        (I := I) (M := M) g g T hδT hδZ)
      (LowBaseInternal.selfLow_joint
        (I := I) (M := M) g g U hδU hδZ)
  set X : ℝ := (1 + A + A ^ 2) ^ 4 * (D2 ^ 2 + N ^ 2) with hXdef
  have hX0 : 0 ≤ X := by
    rw [hXdef]
    positivity
  set Btot : ℝ := Real.sqrt (Bs R * X) with hBtot
  have hB0 : 0 ≤ Btot := Real.sqrt_nonneg _
  have hBsq : Btot ^ 2 = Bs R * X := by
    rw [hBtot]
    exact Real.sq_sqrt (mul_nonneg (hBs R hR) hX0)
  have hpoint : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      lowJetSq (I := I) (M := M) g 1 (Φ s) ≤ Btot ^ 2 := by
    intro s hs
    rw [hBsq]
    have := hker T U hT hU hδ_le hδ0 hδT hδU hδZ
      R A D2 N hR hA hD2 hN hT2 hU2 hT3 hU3 hTU2 hTn hUn hTUn hs
    rw [← hXdef] at this
    exact this
  have hpath := path_jetL2_le (I := I) (M := M)
    g 2 2 1 Φ S realizedSmallSet_isOpen hSI hjoint
    (B := Btot) hB0
    (by
      intro t ht
      simpa only [lowJetSq, Nat.reduceAdd] using hpoint t ht)
  have hfin : lowJetSq (I := I) (M := M) g 1
      (lowC0Diff (I := I) (M := M) g T U hδ_lt hδT hδU hδZ) ≤
      Btot ^ 2 := by
    simpa only [lowJetSq, lowC0Diff, Φ, S, Nat.reduceAdd] using hpath
  calc
    lowJetSq (I := I) (M := M) g 1
        (lowC0Diff (I := I) (M := M) g T U
          (lt_of_le_of_lt hδ_le
            (by norm_num : (1 : ℝ) / 3 < 1))
          hδT hδU hδZ) ≤ Btot ^ 2 := hfin
    _ = Bs R * ((1 + A + A ^ 2) ^ 4 * (D2 ^ 2 + N ^ 2)) := by
      rw [hBsq, hXdef]

private theorem grad_shift_lip
    (g : SmoothRiemannianMetric I M) (W : SmoothCcTensor g 0 2) :
    lowJetSq (I := I) (M := M) g 1
        (iteratedCovGrad (I := I) g 0 2 1 W) ≤
      lowJetSq (I := I) (M := M) g 2 W := by
  have hcomp : ∀ i : ℕ,
      ‖iteratedCovGrad (I := I) g 0 3 i
          (iteratedCovGrad (I := I) g 0 2 1 W)‖ ^ 2 =
        ‖iteratedCovGrad (I := I) g 0 2 (1 + i) W‖ ^ 2 := by
    intro i
    rw [SmoothCcTensor.norm_def (I := I) (M := M),
      SmoothCcTensor.norm_def (I := I) (M := M),
      tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs
        (I := I) (M := M) g 0 (3 + i)
        (iteratedCovGrad (I := I) g 0 3 i
          (iteratedCovGrad (I := I) g 0 2 1 W)),
      tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs
        (I := I) (M := M) g 0 (2 + (1 + i))
        (iteratedCovGrad (I := I) g 0 2 (1 + i) W)]
    refine MeasureTheory.integral_congr_ae
      (Filter.Eventually.of_forall (fun x => ?_))
    exact rfns_iteratedCovGrad_comp (I := I) (M := M) g 0 2 1 i W x
  have h0 : (0 : ℝ) ≤ ‖iteratedCovGrad (I := I) g 0 2 0 W‖ ^ 2 :=
    sq_nonneg _
  calc
    lowJetSq (I := I) (M := M) g 1
        (iteratedCovGrad (I := I) g 0 2 1 W) =
      ‖iteratedCovGrad (I := I) g 0 3 0
          (iteratedCovGrad (I := I) g 0 2 1 W)‖ ^ 2 +
        ‖iteratedCovGrad (I := I) g 0 3 1
          (iteratedCovGrad (I := I) g 0 2 1 W)‖ ^ 2 := by
      simp only [lowJetSq, Finset.sum_range_succ,
        Finset.sum_range_zero, zero_add]
    _ = ‖iteratedCovGrad (I := I) g 0 2 1 W‖ ^ 2 +
        ‖iteratedCovGrad (I := I) g 0 2 2 W‖ ^ 2 := by
      rw [hcomp 0, hcomp 1]
    _ ≤ ‖iteratedCovGrad (I := I) g 0 2 0 W‖ ^ 2 +
        (‖iteratedCovGrad (I := I) g 0 2 1 W‖ ^ 2 +
          ‖iteratedCovGrad (I := I) g 0 2 2 W‖ ^ 2) := by
      linarith [h0]
    _ = lowJetSq (I := I) (M := M) g 2 W := by
      simp only [lowJetSq, Finset.sum_range_succ,
        Finset.sum_range_zero, zero_add]
      ring

set_option maxHeartbeats 3200000 in
set_option linter.unusedVariables false in
/-- **The uniform low-regularity Lipschitz bound for the pairwise
first-order action at the low `H² → H¹` scale.**  On a common spectral
`H²` ball, the difference action of two realized low-base data sets is
`H¹`-operator-bounded with modulus controlled by the `H²` state
difference `D2`, the `H³` state difference `D3`, and the spectral
difference `N` — the uniform-uniqueness estimate of the `C0` lane. -/
theorem a1Sub_lo_tame
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ : ℝ, ∃ C : ℝ, ∃ Bq : ℝ → ℝ, ∃ B0 B1 : ℝ,
      0 < ρ ∧ 0 ≤ C ∧ (∀ R : ℝ, 0 ≤ R → 0 ≤ Bq R) ∧
      0 ≤ B0 ∧ 0 ≤ B1 ∧
      ∀ (T U : SmoothCcTensor g 0 2)
        (hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        (hU : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g U x u v =
            ccTensorBilin (I := I) g U x v u)
        {δ : ℝ} (hδ_le : δ ≤ 1 / 3) (hδ0 : 0 ≤ δ)
        (hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδU : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g U) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        (R A D2 D3 N : ℝ),
        0 ≤ R → 0 ≤ A → 0 ≤ D2 → 0 ≤ D3 → 0 ≤ N →
        lowJetSq (I := I) (M := M) g 2 T ≤ R ^ 2 →
        lowJetSq (I := I) (M := M) g 2 U ≤ R ^ 2 →
        lowJetSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
        lowJetSq (I := I) (M := M) g 3 U ≤ A ^ 2 →
        lowJetSq (I := I) (M := M) g 2 (T - U) ≤ D2 ^ 2 →
        lowJetSq (I := I) (M := M) g 3 (T - U) ≤ D3 ^ 2 →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U)‖ ≤ N →
        ∀ W : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (1 : ℝ)
          ((lowBaseDiff (I := I) (M := M) g T U
              (lt_of_le_of_lt hδ_le
                (by norm_num : (1 : ℝ) / 3 < 1))
              hδT hδU hδZ).a1 (I := I) (M := M) W)‖ ≤
        C * Real.sqrt
            (Bq R * ((1 + A + A ^ 2) ^ 4 * (D2 ^ 2 + N ^ 2)) +
              (B0 * D3 + B1 * N + B1 * A * N) ^ 2) *
          ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) W‖ := by
  obtain ⟨ρ0, Bq0, hρ0, hBq0, hc0⟩ :=
    c0Diff_tame (I := I) (M := M) hDim g
  obtain ⟨ρ1, B0c, B1c, hρ1, hB0c, hB1c, hc1⟩ :=
    c1Diff_tame (I := I) (M := M) hDim g
  obtain ⟨Ca, hCa, happ12⟩ :=
    app_h12_mul_lip (I := I) (M := M) hDim g 0 2 2
  obtain ⟨Cb, hCb, happ21⟩ :=
    app_h21_mul_lip (I := I) (M := M) hDim g 0 3 2
  obtain ⟨Cs, hCs, hspec⟩ :=
    a1_spec_lo (I := I) (M := M) g
  set ρ : ℝ := min ρ0 ρ1 with hρdef
  have hρpos : 0 < ρ := lt_min hρ0 hρ1
  set K : ℝ := 2 * Ca + 2 * Cb with hKdef
  have hK0 : 0 ≤ K := by
    rw [hKdef]
    linarith [hCa, hCb]
  let Bq : ℝ → ℝ := fun R => K * Bq0 R
  let B0 : ℝ := Real.sqrt K * B0c
  let B1 : ℝ := Real.sqrt K * B1c
  have hB0' : 0 ≤ B0 := mul_nonneg (Real.sqrt_nonneg _) hB0c
  have hB1' : 0 ≤ B1 := mul_nonneg (Real.sqrt_nonneg _) hB1c
  refine ⟨ρ, Cs, Bq, B0, B1, hρpos, hCs,
    fun R hR => mul_nonneg hK0 (hBq0 R hR), hB0', hB1', ?_⟩
  intro T U hT hU δ hδ_le hδ0 hδT hδU hδZ
    R A D2 D3 N hR hA hD2 hD3 hN hT2 hU2 hT3 hU3 hTU2 hTU3 hTn hUn hTUn W
  have hM0 := hc0 T U hT hU hδ_le hδ0 hδT hδU hδZ
    R A D2 N hR hA hD2 hN hT2 hU2 hT3 hU3 hTU2
    (hTn.trans (min_le_left _ _)) (hUn.trans (min_le_left _ _)) hTUn
  have hM1 := hc1 T U hT hU hδ_le hδ0 hδT hδU hδZ
    (hTn.trans (min_le_right _ _)) (hUn.trans (min_le_right _ _))
    A D3 hA hD3 hT3 hTU3
  set X : ℝ := (1 + A + A ^ 2) ^ 4 * (D2 ^ 2 + N ^ 2) with hXdef
  have hX0 : 0 ≤ X := by
    rw [hXdef]
    positivity
  set Nrm : ℝ := ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U)‖
    with hNrm
  set M1 : ℝ := (B0c * D3 + B1c * Nrm + B1c * A * Nrm) ^ 2 with hM1def
  have hM1n : 0 ≤ M1 := sq_nonneg _
  set Q : ℝ := K * (Bq0 R * X + M1) with hQdef
  have hQ0 : 0 ≤ Q := by
    rw [hQdef]
    exact mul_nonneg hK0
      (add_nonneg (mul_nonneg (hBq0 R hR) hX0) hM1n)
  set D : LowBaseActionData g :=
    lowBaseDiff (I := I) (M := M) g T U
      (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
      hδT hδU hδZ with hDdef
  have hcore : ∀ V : SmoothCcTensor g 0 2,
      lowJetSq (I := I) (M := M) g 1
          (D.a1 (I := I) (M := M) V) ≤
        Q * lowJetSq (I := I) (M := M) g 2 V := by
    intro V
    have hC0eq : D.C0 = lowC0Diff (I := I) (M := M) g T U
        (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
        hδT hδU hδZ := by
      rw [hDdef]
      exact lowBaseDiff_c0 (I := I) (M := M) g T U _ hδT hδU hδZ
    have hC1eq : D.C1 = lowC1Diff (I := I) (M := M) g T U
        (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
        hδT hδU hδZ := by
      rw [hDdef]
      exact lowBaseDiff_c1 (I := I) (M := M) g T U _ hδT hδU hδZ
    have hj0 : lowJetSq (I := I) (M := M) g 1 D.C0 ≤ Bq0 R * X := by
      rw [hC0eq]
      exact hM0
    have hj1 : lowJetSq (I := I) (M := M) g 2 D.C1 ≤ M1 := by
      rw [hC1eq]
      exact hM1
    have ha1 : D.a1 (I := I) (M := M) V =
        appCc (I := I) (M := M) g 2 2 D.C0 V +
          appCc (I := I) (M := M) g 3 2 D.C1
            (iteratedCovGrad (I := I) g 0 2 1 V) := rfl
    rw [ha1]
    have hL : lowJetSq (I := I) (M := M) g 1
        (appCc (I := I) (M := M) g 2 2 D.C0 V) ≤
        Ca * (Bq0 R * X) * lowJetSq (I := I) (M := M) g 2 V := by
      have h := happ12 D.C0 V
      rw [appCcRS_zero_eq_appCc] at h
      refine h.trans ?_
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hj0 hCa)
        (jet_nonneg_lip (I := I) (M := M) (m := 2) g V)
    have hRt : lowJetSq (I := I) (M := M) g 1
        (appCc (I := I) (M := M) g 3 2 D.C1
          (iteratedCovGrad (I := I) g 0 2 1 V)) ≤
        Cb * M1 * lowJetSq (I := I) (M := M) g 2 V := by
      have h := happ21 D.C1 (iteratedCovGrad (I := I) g 0 2 1 V)
      rw [appCcRS_zero_eq_appCc] at h
      refine h.trans
        (mul_le_mul
          (mul_le_mul_of_nonneg_left hj1 hCb)
          (grad_shift_lip (I := I) (M := M) g V)
          (jet_nonneg_lip (I := I) (M := M) (m := 1) g _)
          (mul_nonneg hCb hM1n))
    calc
      lowJetSq (I := I) (M := M) g 1
          (appCc (I := I) (M := M) g 2 2 D.C0 V +
            appCc (I := I) (M := M) g 3 2 D.C1
              (iteratedCovGrad (I := I) g 0 2 1 V)) ≤
        2 * (lowJetSq (I := I) (M := M) g 1
            (appCc (I := I) (M := M) g 2 2 D.C0 V) +
          lowJetSq (I := I) (M := M) g 1
            (appCc (I := I) (M := M) g 3 2 D.C1
              (iteratedCovGrad (I := I) g 0 2 1 V))) :=
        jet_add_lip (I := I) (M := M) g 1 _ _
      _ ≤ 2 * (Ca * (Bq0 R * X) * lowJetSq (I := I) (M := M) g 2 V +
          Cb * M1 * lowJetSq (I := I) (M := M) g 2 V) := by
        linarith [hL, hRt]
      _ ≤ Q * lowJetSq (I := I) (M := M) g 2 V := by
        rw [hQdef, hKdef]
        have hjV := jet_nonneg_lip (I := I) (M := M) (m := 2) g V
        have e1 : (0 : ℝ) ≤ Ca * M1 *
            lowJetSq (I := I) (M := M) g 2 V :=
          mul_nonneg (mul_nonneg hCa hM1n) hjV
        have e2 : (0 : ℝ) ≤ Cb * (Bq0 R * X) *
            lowJetSq (I := I) (M := M) g 2 V :=
          mul_nonneg (mul_nonneg hCb
            (mul_nonneg (hBq0 R hR) hX0)) hjV
        nlinarith [hjV, e1, e2]
  have hfin := hspec D Q hQ0 hcore W
  refine hfin.trans ?_
  have hQle : Real.sqrt Q ≤ Real.sqrt
      (Bq R * ((1 + A + A ^ 2) ^ 4 * (D2 ^ 2 + N ^ 2)) +
        (B0 * D3 + B1 * N + B1 * A * N) ^ 2) := by
    apply Real.sqrt_le_sqrt
    rw [hQdef]
    have hKsq : Real.sqrt K ^ 2 = K := Real.sq_sqrt hK0
    have hexp : (B0 * D3 + B1 * N + B1 * A * N) ^ 2 =
        K * (B0c * D3 + B1c * N + B1c * A * N) ^ 2 := by
      simp only [B0, B1]
      rw [show (Real.sqrt K * B0c * D3 + Real.sqrt K * B1c * N +
          Real.sqrt K * B1c * A * N) ^ 2 =
          Real.sqrt K ^ 2 *
            (B0c * D3 + B1c * N + B1c * A * N) ^ 2 from by ring,
        hKsq]
    have hM1le : M1 ≤ (B0c * D3 + B1c * N + B1c * A * N) ^ 2 := by
      rw [hM1def]
      have hle : B0c * D3 + B1c * Nrm + B1c * A * Nrm ≤
          B0c * D3 + B1c * N + B1c * A * N := by
        have h1 : B1c * Nrm ≤ B1c * N :=
          mul_le_mul_of_nonneg_left (by rw [hNrm]; exact hTUn) hB1c
        have h2 : B1c * A * Nrm ≤ B1c * A * N :=
          mul_le_mul_of_nonneg_left (by rw [hNrm]; exact hTUn)
            (mul_nonneg hB1c hA)
        linarith
      have hnn : 0 ≤ B0c * D3 + B1c * Nrm + B1c * A * Nrm := by
        have : 0 ≤ Nrm := by rw [hNrm]; exact norm_nonneg _
        have h1 : 0 ≤ B0c * D3 := mul_nonneg hB0c hD3
        have h2 : 0 ≤ B1c * Nrm := mul_nonneg hB1c this
        have h3 : 0 ≤ B1c * A * Nrm :=
          mul_nonneg (mul_nonneg hB1c hA) this
        linarith
      exact pow_le_pow_left₀ hnn hle 2
    simp only [Bq]
    rw [hexp, ← hXdef]
    have := mul_le_mul_of_nonneg_left hM1le hK0
    nlinarith [this, hK0, mul_nonneg (hBq0 R hR) hX0]
  calc
    Cs * Real.sqrt Q *
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) W‖ ≤
      Cs * Real.sqrt
          (Bq R * ((1 + A + A ^ 2) ^ 4 * (D2 ^ 2 + N ^ 2)) +
            (B0 * D3 + B1 * N + B1 * A * N) ^ 2) *
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) W‖ := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hQle hCs) (norm_nonneg _)

theorem metricCorr_tame
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ B0 B1 : ℝ → ℝ,
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B0 R) ∧
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B1 R) ∧
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
            (0 : SmoothCcTensor g 0 2)) δ)
        (R A D2 D3 : ℝ), 0 ≤ R → 0 ≤ A → 0 ≤ D2 → 0 ≤ D3 →
        lowJetSq (I := I) (M := M) g 2 T ≤ R ^ 2 →
        lowJetSq (I := I) (M := M) g 2 U ≤ R ^ 2 →
        lowJetSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
        lowJetSq (I := I) (M := M) g 2 (T - U) ≤ D2 ^ 2 →
        lowJetSq (I := I) (M := M) g 3 (T - U) ≤ D3 ^ 2 →
      lowJetSq (I := I) (M := M) g 2
          (metricLowerCorr (I := I) (M := M) g gT g T -
            metricLowerCorr (I := I) (M := M) g gU g U) ≤
        (B0 R * D3 + B1 R * D2 + B1 R * A * D2) ^ 2 := by
  obtain ⟨C, hC, hpair⟩ :=
    metricCorr_pair (I := I) (M := M) hDim g
  obtain ⟨Bs, hBs, hself⟩ :=
    wXi_self_tame (I := I) (M := M) hDim g
  obtain ⟨W0, W1, hW0, hW1, hw⟩ :=
    wXi_sub_tame (I := I) (M := M) hDim g
      (δ₀ := (1 : ℝ) / 3) (by norm_num) (by norm_num)
  let H : ℝ := Real.sqrt C
  let B0 : ℝ → ℝ := fun R => H * R * W0 R
  let B1 : ℝ → ℝ := fun R => H * (Bs R + R * W1 R)
  have hH : 0 ≤ H := Real.sqrt_nonneg _
  have hHsq : H ^ 2 = C := by
    simpa only [H] using Real.sq_sqrt hC
  refine ⟨B0, B1, ?_, ?_, ?_⟩
  · intro R hR
    exact mul_nonneg (mul_nonneg hH hR) (hW0 R hR)
  · intro R hR
    exact mul_nonneg hH
      (add_nonneg (hBs R hR) (mul_nonneg hR (hW1 R hR)))
  intro gT gU T U hT hU hTtie hUtie δ hδ_le hδ0
    hδT hδU hδZ R A D2 D3 hR hA hD2 hD3
    hT2 hU2 hT3 hTU2 hTU3
  let WT : ℝ := lowJetSq (I := I) (M := M) g 2
    (wXi (I := I) (M := M) g gT g)
  let WD : ℝ := lowJetSq (I := I) (M := M) g 2
    (wXi (I := I) (M := M) g gT g -
      wXi (I := I) (M := M) g gU g)
  let X : ℝ := W0 R * D3 + W1 R * D2 + W1 R * A * D2
  let S : ℝ := Bs R * A * D2
  let Y : ℝ := R * X
  have hWT : WT ≤ (Bs R * A) ^ 2 := by
    simpa only [WT] using hself gT T hT hTtie
      hδ_le hδ0 hδT hδZ R A hR hA hT2 hT3
  have hWD : WD ≤ X ^ 2 := by
    simpa only [WD, X] using
      hw gT gU g T U hT hU hTtie hUtie
        hδ_le hδ0 hδT hδ_le hδ0 hδU
        R A D2 D3 hR hA hD2 hD3 hU2 hT3 hTU2 hTU3
  have hWT0 : 0 ≤ WT := jet_nonneg_lip (I := I) (M := M) g _
  have hWD0 : 0 ≤ WD := jet_nonneg_lip (I := I) (M := M) g _
  have hX0 : 0 ≤ X :=
    add_nonneg
      (add_nonneg (mul_nonneg (hW0 R hR) hD3)
        (mul_nonneg (hW1 R hR) hD2))
      (mul_nonneg (mul_nonneg (hW1 R hR) hA) hD2)
  have hS0 : 0 ≤ S :=
    mul_nonneg (mul_nonneg (hBs R hR) hA) hD2
  have hY0 : 0 ≤ Y := mul_nonneg hR hX0
  have hfirst :
      lowJetSq (I := I) (M := M) g 2 (T - U) * WT ≤ S ^ 2 := by
    calc
      lowJetSq (I := I) (M := M) g 2 (T - U) * WT ≤
          D2 ^ 2 * (Bs R * A) ^ 2 :=
        mul_le_mul hTU2 hWT hWT0 (sq_nonneg D2)
      _ = S ^ 2 := by
        simp only [S]
        ring
  have hsecond :
      lowJetSq (I := I) (M := M) g 2 U * WD ≤ Y ^ 2 := by
    calc
      lowJetSq (I := I) (M := M) g 2 U * WD ≤
          R ^ 2 * X ^ 2 :=
        mul_le_mul hU2 hWD hWD0 (sq_nonneg R)
      _ = Y ^ 2 := by
        simp only [Y]
        ring
  have hraw := hpair gT gU g T U
  change lowJetSq (I := I) (M := M) g 2
      (metricLowerCorr (I := I) (M := M) g gT g T -
        metricLowerCorr (I := I) (M := M) g gU g U) ≤
    C * (lowJetSq (I := I) (M := M) g 2 (T - U) * WT +
      lowJetSq (I := I) (M := M) g 2 U * WD) at hraw
  have hCSY :
      C * (lowJetSq (I := I) (M := M) g 2 (T - U) * WT +
          lowJetSq (I := I) (M := M) g 2 U * WD) ≤
        C * (S ^ 2 + Y ^ 2) :=
    mul_le_mul_of_nonneg_left (add_le_add hfirst hsecond) hC
  have hquad :
      C * (S ^ 2 + Y ^ 2) ≤ (H * S + H * Y) ^ 2 := by
    rw [show C * (S ^ 2 + Y ^ 2) =
        (H * S) ^ 2 + (H * Y) ^ 2 by
      rw [← hHsq]
      ring]
    nlinarith [mul_nonneg (mul_nonneg hH hS0) (mul_nonneg hH hY0)]
  have hlin :
      H * S + H * Y ≤
        B0 R * D3 + B1 R * D2 + B1 R * A * D2 := by
    have hextra : 0 ≤ H * Bs R * D2 :=
      mul_nonneg (mul_nonneg hH (hBs R hR)) hD2
    simp only [S, Y, X, B0, B1]
    nlinarith
  have hlin0 : 0 ≤ H * S + H * Y :=
    add_nonneg (mul_nonneg hH hS0) (mul_nonneg hH hY0)
  calc
    lowJetSq (I := I) (M := M) g 2
        (metricLowerCorr (I := I) (M := M) g gT g T -
          metricLowerCorr (I := I) (M := M) g gU g U) ≤
      C * (lowJetSq (I := I) (M := M) g 2 (T - U) * WT +
        lowJetSq (I := I) (M := M) g 2 U * WD) := hraw
    _ ≤ C * (S ^ 2 + Y ^ 2) := hCSY
    _ ≤ (H * S + H * Y) ^ 2 := hquad
    _ ≤ (B0 R * D3 + B1 R * D2 + B1 R * A * D2) ^ 2 :=
      pow_le_pow_left₀ hlin0 hlin 2

set_option linter.unusedVariables false in
/-- The moving-lowering correction has the low-scale `H² → H¹` tame modulus.
The state difference is measured only in `H²`; no `H³` difference enters. -/
theorem metricCorr_tame_h1
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ B0 B1 : ℝ → ℝ,
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B0 R) ∧
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B1 R) ∧
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
            (0 : SmoothCcTensor g 0 2)) δ)
        (R A D2 : ℝ), 0 ≤ R → 0 ≤ A → 0 ≤ D2 →
        lowJetSq (I := I) (M := M) g 2 T ≤ R ^ 2 →
        lowJetSq (I := I) (M := M) g 2 U ≤ R ^ 2 →
        lowJetSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
        lowJetSq (I := I) (M := M) g 2 (T - U) ≤ D2 ^ 2 →
      lowJetSq (I := I) (M := M) g 1
          (metricLowerCorr (I := I) (M := M) g gT g T -
            metricLowerCorr (I := I) (M := M) g gU g U) ≤
        (B0 R * D2 + B1 R * A * D2) ^ 2 := by
  obtain ⟨C, hC, hpair⟩ :=
    metricCorr_pair_h1 (I := I) (M := M) hDim g
  obtain ⟨Bs, hBs, hself⟩ :=
    wXi_self_tame (I := I) (M := M) hDim g
  obtain ⟨W0, W1, hW0, hW1, hw⟩ :=
    wXi_pair_h1 (I := I) (M := M) hDim g
      (δ₀ := (1 : ℝ) / 3) (by norm_num) (by norm_num)
  let H : ℝ := Real.sqrt C
  let B0 : ℝ → ℝ := fun R => H * R * W0 R
  let B1 : ℝ → ℝ := fun R => H * (Bs R + R * W1 R)
  have hH : 0 ≤ H := Real.sqrt_nonneg _
  have hHsq : H ^ 2 = C := by
    simpa only [H] using Real.sq_sqrt hC
  refine ⟨B0, B1, ?_, ?_, ?_⟩
  · intro R hR
    exact mul_nonneg (mul_nonneg hH hR) (hW0 R hR)
  · intro R hR
    exact mul_nonneg hH
      (add_nonneg (hBs R hR) (mul_nonneg hR (hW1 R hR)))
  intro gT gU T U hT hU hTtie hUtie δ hδ_le hδ0
    hδT hδU hδZ R A D2 hR hA hD2 hT2 hU2 hT3 hTU2
  let WT : ℝ := lowJetSq (I := I) (M := M) g 1
    (wXi (I := I) (M := M) g gT g)
  let WD : ℝ := lowJetSq (I := I) (M := M) g 1
    (wXi (I := I) (M := M) g gT g -
      wXi (I := I) (M := M) g gU g)
  let X : ℝ := W0 R * D2 + W1 R * A * D2
  let S : ℝ := Bs R * A * D2
  let Y : ℝ := R * X
  have hWT2 :
      lowJetSq (I := I) (M := M) g 2
          (wXi (I := I) (M := M) g gT g) ≤
        (Bs R * A) ^ 2 := by
    exact hself gT T hT hTtie
      hδ_le hδ0 hδT hδZ R A hR hA hT2 hT3
  have hWT : WT ≤ (Bs R * A) ^ 2 := by
    exact (jet_mono_lip (I := I) (M := M) g
      (by omega : 1 ≤ 2)
      (wXi (I := I) (M := M) g gT g)).trans hWT2
  have hWD : WD ≤ X ^ 2 := by
    simpa only [WD, X] using
      hw gT gU g T U hT hU hTtie hUtie
        hδ_le hδ0 hδT hδ_le hδ0 hδU
        R A D2 hR hA hD2 hU2 hT3 hTU2
  have hWT0 : 0 ≤ WT := jet_nonneg_lip (I := I) (M := M) g _
  have hWD0 : 0 ≤ WD := jet_nonneg_lip (I := I) (M := M) g _
  have hX0 : 0 ≤ X :=
    add_nonneg
      (mul_nonneg (hW0 R hR) hD2)
      (mul_nonneg (mul_nonneg (hW1 R hR) hA) hD2)
  have hS0 : 0 ≤ S :=
    mul_nonneg (mul_nonneg (hBs R hR) hA) hD2
  have hY0 : 0 ≤ Y := mul_nonneg hR hX0
  have hfirst :
      lowJetSq (I := I) (M := M) g 2 (T - U) * WT ≤ S ^ 2 := by
    calc
      lowJetSq (I := I) (M := M) g 2 (T - U) * WT ≤
          D2 ^ 2 * (Bs R * A) ^ 2 :=
        mul_le_mul hTU2 hWT hWT0 (sq_nonneg D2)
      _ = S ^ 2 := by
        simp only [S]
        ring
  have hsecond :
      lowJetSq (I := I) (M := M) g 2 U * WD ≤ Y ^ 2 := by
    calc
      lowJetSq (I := I) (M := M) g 2 U * WD ≤
          R ^ 2 * X ^ 2 :=
        mul_le_mul hU2 hWD hWD0 (sq_nonneg R)
      _ = Y ^ 2 := by
        simp only [Y]
        ring
  have hraw := hpair gT gU T U
  change lowJetSq (I := I) (M := M) g 1
      (metricLowerCorr (I := I) (M := M) g gT g T -
        metricLowerCorr (I := I) (M := M) g gU g U) ≤
    C * (lowJetSq (I := I) (M := M) g 2 (T - U) * WT +
      lowJetSq (I := I) (M := M) g 2 U * WD) at hraw
  have hCSY :
      C * (lowJetSq (I := I) (M := M) g 2 (T - U) * WT +
          lowJetSq (I := I) (M := M) g 2 U * WD) ≤
        C * (S ^ 2 + Y ^ 2) :=
    mul_le_mul_of_nonneg_left (add_le_add hfirst hsecond) hC
  have hquad :
      C * (S ^ 2 + Y ^ 2) ≤ (H * S + H * Y) ^ 2 := by
    rw [show C * (S ^ 2 + Y ^ 2) =
        (H * S) ^ 2 + (H * Y) ^ 2 by
      rw [← hHsq]
      ring]
    nlinarith [mul_nonneg (mul_nonneg hH hS0) (mul_nonneg hH hY0)]
  have hlin :
      H * S + H * Y = B0 R * D2 + B1 R * A * D2 := by
    simp only [S, Y, X, B0, B1]
    ring
  calc
    lowJetSq (I := I) (M := M) g 1
        (metricLowerCorr (I := I) (M := M) g gT g T -
          metricLowerCorr (I := I) (M := M) g gU g U) ≤
      C * (lowJetSq (I := I) (M := M) g 2 (T - U) * WT +
        lowJetSq (I := I) (M := M) g 2 U * WD) := hraw
    _ ≤ C * (S ^ 2 + Y ^ 2) := hCSY
    _ ≤ (H * S + H * Y) ^ 2 := hquad
    _ = (B0 R * D2 + B1 R * A * D2) ^ 2 := by rw [hlin]

private theorem a1_comm_any
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) (A : LowBaseActionData g) :
    (tensorHsInclusion (I := I) (M := M) (g := g)
        (r := 0) (s := 2) (show (1 : ℝ) ≤ 2 by norm_num)).comp
          (A.a1Hi (I := I) (M := M)) =
      (A.a1Lo (I := I) (M := M)).comp
        (tensorHsInclusion (I := I) (M := M) (g := g)
          (r := 0) (s := 2) (show (2 : ℝ) ≤ 3 by norm_num)) := by
  obtain ⟨_, _, hpair⟩ := a1_pair (I := I) (M := M) g
  obtain ⟨Ch, hCh, hhigh⟩ :=
    a1_h3_h2 (I := I) (M := M) hDim g
  obtain ⟨Cl, hCl, hlow⟩ :=
    a1_h2_h1 (I := I) (M := M) hDim g
  let J : ℝ :=
    lowJetSq (I := I) (M := M) g 2 A.C0 +
      lowJetSq (I := I) (M := M) g 2 A.C1
  let B : ℝ := Real.sqrt J
  let C : ℝ := Ch + Cl
  let Q : ℝ := (C * B) ^ 2
  have hJ : 0 ≤ J := by
    exact add_nonneg
      (jet_nonneg_lip (I := I) (M := M) g A.C0)
      (jet_nonneg_lip (I := I) (M := M) g A.C1)
  have hB : 0 ≤ B := Real.sqrt_nonneg _
  have hBsq : B ^ 2 = J := by
    simpa only [B] using Real.sq_sqrt hJ
  have hC : 0 ≤ C := add_nonneg hCh hCl
  have hQ : 0 ≤ Q := sq_nonneg _
  have hcoeff :
      lowJetSq (I := I) (M := M) g 2 A.C0 +
          lowJetSq (I := I) (M := M) g 2 A.C1 ≤ B ^ 2 := by
    rw [hBsq]
  have hHi : ∀ W : SmoothCcTensor g 0 2,
      lowJetSq (I := I) (M := M) g 2
          (A.a1 (I := I) (M := M) W) ≤
        Q * lowJetSq (I := I) (M := M) g 3 W := by
    intro W
    let D : ℝ :=
      Real.sqrt (lowJetSq (I := I) (M := M) g 3 W)
    have hW : 0 ≤ lowJetSq (I := I) (M := M) g 3 W :=
      jet_nonneg_lip (I := I) (M := M) g W
    have hD : 0 ≤ D := Real.sqrt_nonneg _
    have hDsq :
        D ^ 2 = lowJetSq (I := I) (M := M) g 3 W := by
      simpa only [D] using Real.sq_sqrt hW
    calc
      lowJetSq (I := I) (M := M) g 2
          (A.a1 (I := I) (M := M) W) ≤
        (Ch * B * D) ^ 2 :=
          hhigh A W B D hB hD hcoeff (by rw [hDsq])
      _ ≤ (C * B * D) ^ 2 := by
        exact pow_le_pow_left₀
          (mul_nonneg (mul_nonneg hCh hB) hD)
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right
              (le_add_of_nonneg_right hCl) hB) hD) 2
      _ = Q * lowJetSq (I := I) (M := M) g 3 W := by
        rw [show (C * B * D) ^ 2 = (C * B) ^ 2 * D ^ 2 by ring,
          hDsq]
  have hLo : ∀ W : SmoothCcTensor g 0 2,
      lowJetSq (I := I) (M := M) g 1
          (A.a1 (I := I) (M := M) W) ≤
        Q * lowJetSq (I := I) (M := M) g 2 W := by
    intro W
    let D : ℝ :=
      Real.sqrt (lowJetSq (I := I) (M := M) g 2 W)
    have hW : 0 ≤ lowJetSq (I := I) (M := M) g 2 W :=
      jet_nonneg_lip (I := I) (M := M) g W
    have hD : 0 ≤ D := Real.sqrt_nonneg _
    have hDsq :
        D ^ 2 = lowJetSq (I := I) (M := M) g 2 W := by
      simpa only [D] using Real.sq_sqrt hW
    calc
      lowJetSq (I := I) (M := M) g 1
          (A.a1 (I := I) (M := M) W) ≤
        (Cl * B * D) ^ 2 :=
          hlow A W B D hB hD hcoeff (by rw [hDsq])
      _ ≤ (C * B * D) ^ 2 := by
        exact pow_le_pow_left₀
          (mul_nonneg (mul_nonneg hCl hB) hD)
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right
              (le_add_of_nonneg_left hCh) hB) hD) 2
      _ = Q * lowJetSq (I := I) (M := M) g 2 W := by
        rw [show (C * B * D) ^ 2 = (C * B) ^ 2 * D ^ 2 by ring,
          hDsq]
  exact (hpair A Q hQ hHi hLo).2.2.2.2

/-- The difference of two completed first-order actions preserves the
adjacent-scale commuting square. -/
theorem a1_sub_comm
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M)
    (A B : LowBaseActionData g) :
    (tensorHsInclusion (I := I) (M := M) (g := g)
        (r := 0) (s := 2) (show (1 : ℝ) ≤ 2 by norm_num)).comp
          (A.a1Hi (I := I) (M := M) -
            B.a1Hi (I := I) (M := M)) =
      (A.a1Lo (I := I) (M := M) -
          B.a1Lo (I := I) (M := M)).comp
        (tensorHsInclusion (I := I) (M := M) (g := g)
          (r := 0) (s := 2) (show (2 : ℝ) ≤ 3 by norm_num)) := by
  have hA := a1_comm_any (I := I) (M := M) hDim g A
  have hB := a1_comm_any (I := I) (M := M) hDim g B
  apply ContinuousLinearMap.ext
  intro W
  have hAW := congrArg (fun L => L W) hA
  have hBW := congrArg (fun L => L W) hB
  simp only [ContinuousLinearMap.comp_apply] at hAW hBW
  simp only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.sub_apply, map_sub]
  rw [hAW, hBW]

/-- Exact polarization of two first-order low-base actions. -/
theorem a1_sub
    (g : SmoothRiemannianMetric I M)
    (A B : LowBaseActionData g) (T U : SmoothCcTensor g 0 2) :
    A.a1 (I := I) (M := M) T - B.a1 (I := I) (M := M) U =
      A.a1 (I := I) (M := M) (T - U) +
        (A.a1Sub B).a1
          (I := I) (M := M) U := by
  simp only [LowBaseActionData.a1, LowBaseActionData.a1Sub,
    iteratedCovGrad_sub, appCc_sub_left, app_sub_right]
  module

/-- After the complete second-order action is subtracted, the pairwise lower
residual is the sum of one frozen first-order action on `T - U` and the
canonical first-order coefficient difference acting on `U`. -/
theorem lowResidual_sub
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M)
    (T U : SmoothCcTensor g 0 2)
    (hT : ∀ (x : M) (v w : TangentSpace I x),
      ccTensorBilin (I := I) g T x v w =
        ccTensorBilin (I := I) g T x w v)
    (hU : ∀ (x : M) (v w : TangentSpace I x),
      ccTensorBilin (I := I) g U x v w =
        ccTensorBilin (I := I) g U x w v)
    {δ : ℝ} (hδ_le : δ ≤ 1 / 3) (hδ0 : 0 ≤ δ)
    (hδT : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδU : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g U) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ)
    (R A : ℝ) (hR : 0 ≤ R) (hA : 0 ≤ A)
    (hT2 : lowJetSq (I := I) (M := M) g 2 T ≤ R ^ 2)
    (hU2 : lowJetSq (I := I) (M := M) g 2 U ≤ R ^ 2)
    (hT3 : lowJetSq (I := I) (M := M) g 3 T ≤ A ^ 2)
    (hU3 : lowJetSq (I := I) (M := M) g 3 U ≤ A ^ 2) :
    let hδ_lt : δ < 1 :=
      lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)
    let LT : LowBaseActionData g :=
      lowBaseData (I := I) (M := M) g g T hδ_lt hδT hδZ
    lowBaseResidual (I := I) (M := M) g T hδ_lt hδT hδZ -
        lowBaseResidual (I := I) (M := M) g U hδ_lt hδU hδZ =
      LT.a1 (I := I) (M := M) (T - U) +
        (lowBaseDiff (I := I) (M := M) g T U
          hδ_lt hδT hδU hδZ).a1 (I := I) (M := M) U := by
  obtain ⟨_, _, hdiag⟩ :=
    lowResidual_diag (I := I) (M := M) hDim g
  dsimp only
  have hT_eq :=
    (hdiag T hT hδ_le hδ0 hδT hδZ R A hR hA hT2 hT3).1
  have hU_eq :=
    (hdiag U hU hδ_le hδ0 hδU hδZ R A hR hA hU2 hU3).1
  rw [hT_eq, hU_eq]
  exact a1_sub (I := I) (M := M) g
    (lowBaseData (I := I) (M := M) g g T
      (lt_of_le_of_lt hδ_le (by norm_num)) hδT hδZ)
    (lowBaseData (I := I) (M := M) g g U
      (lt_of_le_of_lt hδ_le (by norm_num)) hδU hδZ) T U

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
