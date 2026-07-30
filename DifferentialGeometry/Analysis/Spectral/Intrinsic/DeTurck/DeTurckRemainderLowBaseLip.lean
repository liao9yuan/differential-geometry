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
