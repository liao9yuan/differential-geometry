import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.PrincipalLowRegH2
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.PrincipalOpH2
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.InverseMetricRaisedEndomorphismJetBound

/-!
# Smooth-core realization of the low-regularity principal operator

This file identifies the Banach-algebra Neumann correction with the geometric
moving inverse-cometric coefficient on smooth metric deviations.
-/

noncomputable section

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

private abbrev rank4H2 (g : SmoothRiemannianMetric I M) :=
  tensorHs (I := I) (M := M) g 0 4 (2 : ℝ)

private abbrev rank4End (g : SmoothRiemannianMetric I M) :=
  rank4H2 (I := I) (M := M) g →L[ℝ]
    rank4H2 (I := I) (M := M) g

private local instance rank4EndNorm
    (g : SmoothRiemannianMetric I M) :
    NormedAddCommGroup (rank4End (I := I) (M := M) g) :=
  ContinuousLinearMap.toNormedAddCommGroup

private local instance rank4EndSpace
    (g : SmoothRiemannianMetric I M) :
    NormedSpace ℝ (rank4End (I := I) (M := M) g) :=
  ContinuousLinearMap.toNormedSpace

private noncomputable def diffCoeff4
    (g a b : SmoothRiemannianMetric I M) :
    SmoothCcTensor g 4 4 :=
  slotInsertEndoCc (I := I) (M := M) g 3
    (gInvDiffRaisedEndoField (I := I) a b)

private noncomputable def fullCoeff4
    (g a b : SmoothRiemannianMetric I M) :
    SmoothCcTensor g 4 4 :=
  slotInsertEndoCc (I := I) (M := M) g 3
    (fullRaisedEndoField (I := I) (M := M) a b)

private noncomputable def diffH2
    (g a b : SmoothRiemannianMetric I M) :
    rank4End (I := I) (M := M) g :=
  appHs (I := I) (M := M) g 4 4 2
    (diffCoeff4 (I := I) (M := M) g a b)

private noncomputable def fullH2
    (g a b : SmoothRiemannianMetric I M) :
    rank4End (I := I) (M := M) g :=
  appHs (I := I) (M := M) g 4 4 2
    (fullCoeff4 (I := I) (M := M) g a b)

set_option backward.isDefEq.respectTransparency false in
private lemma raise_eq_diff
    (g₀ g₁ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w =
        g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w) :
    symmRaiseEndo (I := I) (M := M) g₀ T =
      gInvDiffRaisedEndoField (I := I) g₁ g₀ := by
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro v
  apply (metricFlatMap (I := I) g₀ x).injective
  ext w
  rw [metricFlatMap_apply, metricFlatMap_apply]
  rw [symmRaiseEndo_apply, inner_symmRaiseEndo]
  rw [show gInvDiffRaisedEndoField (I := I) g₁ g₀ x =
      gInvDiffRaisedEndo (I := I) g₁ g₀ x from rfl]
  rw [inner_g1_gInvDiffRaisedEndo (I := I) g₁ g₀ x v w]
  rw [htie x v w]
  ring

set_option backward.isDefEq.respectTransparency false in
private lemma perturbCoeff_eq_diff
    (g₀ g₁ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w =
        g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w) :
    perturbCoeff4 (I := I) (M := M) g₀ T =
      diffCoeff4 (I := I) (M := M) g₀ g₁ g₀ := by
  rw [perturbCoeff4, diffCoeff4,
    raise_eq_diff (I := I) (M := M) g₀ g₁ T htie]

private lemma fullField_decomp
    (g a b : SmoothRiemannianMetric I M) :
    fullRaisedEndoField (I := I) (M := M) a b =
      gInvDiffRaisedEndoField (I := I) a b +
        fullRaisedEndoField (I := I) (M := M) g g := by
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro v
  rw [fullRaisedEndoField_apply]
  rw [show ((gInvDiffRaisedEndoField (I := I) a b +
      fullRaisedEndoField (I := I) (M := M) g g) x) =
      gInvDiffRaisedEndoField (I := I) a b x +
        fullRaisedEndoField (I := I) (M := M) g g x from by
    rw [ContMDiffSection.coe_add]
    rfl]
  rw [ContinuousLinearMap.add_apply]
  rw [show gInvDiffRaisedEndoField (I := I) a b x =
      gInvDiffRaisedEndo (I := I) a b x from rfl]
  rw [fullRaisedEndoField_apply]
  rw [gInvRaisedEndo_eq_diff_add_id]
  rw [gInvRaisedEndo_apply, inverseMetricSharpFib_g0FlatCLM]

private lemma fullCoeff_decomp
    (g a b : SmoothRiemannianMetric I M) :
    fullCoeff4 (I := I) (M := M) g a b =
      diffCoeff4 (I := I) (M := M) g a b +
        fullCoeff4 (I := I) (M := M) g g g := by
  rw [fullCoeff4, diffCoeff4, fullCoeff4,
    fullField_decomp (I := I) (M := M) g a b,
    slotInsertEndoCc_add]

private lemma fullH2_decomp
    (g a b : SmoothRiemannianMetric I M) :
    fullH2 (I := I) (M := M) g a b =
      diffH2 (I := I) (M := M) g a b +
        fullH2 (I := I) (M := M) g g g := by
  apply ContinuousLinearMap.ext
  intro U
  simp only [fullH2, diffH2, ContinuousLinearMap.add_apply]
  rw [fullCoeff_decomp (I := I) (M := M) g a b]
  exact appHs_add (I := I) (M := M) g 4 4 2
    (diffCoeff4 (I := I) (M := M) g a b)
    (fullCoeff4 (I := I) (M := M) g g g) U

private lemma fullCoeff_self
    (g : SmoothRiemannianMetric I M) (W : SmoothCcTensor g 0 4) :
    appCc (I := I) (M := M) g 4 4
        (fullCoeff4 (I := I) (M := M) g g g) W = W := by
  apply smoothCcTensor_ext_of_unitModel (I := I) (M := M) g
  intro x
  simp only [unitModel]
  rw [appCc_toSection]
  simp only [fullCoeff4, slotInsertEndoCc_toSection,
    fullRaisedEndoField_apply]
  have hid : gInvRaisedEndo (I := I) g g x =
      ContinuousLinearMap.id ℝ (TangentSpace I x) := by
    apply ContinuousLinearMap.ext
    intro v
    rw [gInvRaisedEndo_apply, inverseMetricSharpFib_g0FlatCLM,
      ContinuousLinearMap.id_apply]
  rw [hid, slotInsertFib_id, ContinuousLinearMap.id_comp]

private lemma fullH2_self
    (g : SmoothRiemannianMetric I M) :
    fullH2 (I := I) (M := M) g g g = 1 := by
  rw [ContinuousLinearMap.one_def]
  apply ContinuousLinearMap.ext
  intro U
  let ι := ccToHsLin (I := I) (M := M) g 4 (2 : ℝ)
  have hdense : DenseRange ι :=
    ccToHsLin_dense (I := I) (M := M) g 4 (by positivity)
  have hfun := hdense.equalizer
    (fullH2 (I := I) (M := M) g g g).continuous
    (ContinuousLinearMap.id ℝ
      (rank4H2 (I := I) (M := M) g)).continuous (by
      funext W
      simp only [Function.comp_apply, ι, ccToHsLin_apply,
        ContinuousLinearMap.id_apply]
      calc
        fullH2 (I := I) (M := M) g g g
            (ccTensorToHs (I := I) (M := M) g 4 (2 : ℝ) W) =
            ccTensorToHs (I := I) (M := M) g 4 (2 : ℝ)
              (appCc (I := I) (M := M) g 4 4
                (fullCoeff4 (I := I) (M := M) g g g) W) := by
                  exact appHs_core (I := I) (M := M) g 4 4 2
                    (fullCoeff4 (I := I) (M := M) g g g) W
        _ = ccTensorToHs (I := I) (M := M) g 4 (2 : ℝ) W := by
          rw [fullCoeff_self (I := I) (M := M) g W])
  exact congrFun hfun U

private lemma fullH2_sub_one
    (g a b : SmoothRiemannianMetric I M) :
    fullH2 (I := I) (M := M) g a b - 1 =
      diffH2 (I := I) (M := M) g a b := by
  rw [fullH2_decomp (I := I) (M := M) g a b,
    fullH2_self (I := I) (M := M) g]
  abel

private lemma raised_cancel
    (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) :
    (gInvRaisedEndo (I := I) g₁ g₀ x).comp
        (gInvRaisedEndo (I := I) g₀ g₁ x) =
      ContinuousLinearMap.id ℝ (TangentSpace I x) := by
  apply ContinuousLinearMap.ext
  intro v
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
    gInvRaisedEndo_apply, gInvRaisedEndo_apply]
  rw [g0FlatCLM_inverseMetricSharpFib (I := I) g₁ x
    (g0FlatCLM (I := I) g₀ x v)]
  rw [inverseMetricSharpFib_g0FlatCLM (I := I) g₀ x v]

private lemma fullCoeff_cancel
    (g₀ g₁ : SmoothRiemannianMetric I M)
    (W : SmoothCcTensor g₀ 0 4) :
    appCc (I := I) (M := M) g₀ 4 4
        (fullCoeff4 (I := I) (M := M) g₀ g₀ g₁)
        (appCc (I := I) (M := M) g₀ 4 4
          (fullCoeff4 (I := I) (M := M) g₀ g₁ g₀) W) = W := by
  apply smoothCcTensor_ext_of_unitModel (I := I) (M := M) g₀
  intro x
  simp only [unitModel]
  rw [appCc_toSection, appCc_toSection]
  rw [← ContinuousLinearMap.comp_assoc]
  simp only [fullCoeff4, slotInsertEndoCc_toSection,
    fullRaisedEndoField_apply]
  rw [slotInsertFib_comp, raised_cancel, slotInsertFib_id,
    ContinuousLinearMap.id_comp]

private lemma fullH2_mul
    (g₀ g₁ : SmoothRiemannianMetric I M) :
    fullH2 (I := I) (M := M) g₀ g₀ g₁ *
        fullH2 (I := I) (M := M) g₀ g₁ g₀ = 1 := by
  rw [ContinuousLinearMap.mul_def, ContinuousLinearMap.one_def]
  apply ContinuousLinearMap.ext
  intro U
  let ι := ccToHsLin (I := I) (M := M) g₀ 4 (2 : ℝ)
  let L := (fullH2 (I := I) (M := M) g₀ g₀ g₁).comp
    (fullH2 (I := I) (M := M) g₀ g₁ g₀)
  let R := ContinuousLinearMap.id ℝ
    (rank4H2 (I := I) (M := M) g₀)
  have hdense : DenseRange ι :=
    ccToHsLin_dense (I := I) (M := M) g₀ 4 (by positivity)
  have hfun := hdense.equalizer L.continuous R.continuous (by
    funext W
    simp only [Function.comp_apply, L, R, ι, ccToHsLin_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply]
    calc
      fullH2 (I := I) (M := M) g₀ g₀ g₁
          (fullH2 (I := I) (M := M) g₀ g₁ g₀
            (ccTensorToHs (I := I) (M := M) g₀ 4 (2 : ℝ) W)) =
          fullH2 (I := I) (M := M) g₀ g₀ g₁
            (ccTensorToHs (I := I) (M := M) g₀ 4 (2 : ℝ)
              (appCc (I := I) (M := M) g₀ 4 4
                (fullCoeff4 (I := I) (M := M) g₀ g₁ g₀) W)) := by
            congr 1
            exact appHs_core (I := I) (M := M) g₀ 4 4 2
              (fullCoeff4 (I := I) (M := M) g₀ g₁ g₀) W
      _ = ccTensorToHs (I := I) (M := M) g₀ 4 (2 : ℝ)
            (appCc (I := I) (M := M) g₀ 4 4
              (fullCoeff4 (I := I) (M := M) g₀ g₀ g₁)
              (appCc (I := I) (M := M) g₀ 4 4
                (fullCoeff4 (I := I) (M := M) g₀ g₁ g₀) W)) := by
            exact appHs_core (I := I) (M := M) g₀ 4 4 2
              (fullCoeff4 (I := I) (M := M) g₀ g₀ g₁)
              (appCc (I := I) (M := M) g₀ 4 4
                (fullCoeff4 (I := I) (M := M) g₀ g₁ g₀) W)
      _ = ccTensorToHs (I := I) (M := M) g₀ 4 (2 : ℝ) W := by
        rw [fullCoeff_cancel (I := I) (M := M) g₀ g₁ W])
  exact congrFun hfun U

private lemma perturbH2_eq_diff
    (hDim : Module.finrank ℝ E = 3)
    (g₀ g₁ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w =
        g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w) :
    perturbH2 (I := I) (M := M) g₀
        (ccTensorToHs (I := I) (M := M) g₀ 2 (2 : ℝ) T) =
      diffH2 (I := I) (M := M) g₀ g₁ g₀ := by
  rw [perturbH2_core (I := I) (M := M) hDim g₀ T,
    diffH2, perturbCoeff_eq_diff (I := I) (M := M) g₀ g₁ T htie]

private lemma totalH2_eq
    (hDim : Module.finrank ℝ E = 3)
    (g₀ g₁ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w =
        g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w) :
    1 + perturbH2 (I := I) (M := M) g₀
        (ccTensorToHs (I := I) (M := M) g₀ 2 (2 : ℝ) T) =
      fullH2 (I := I) (M := M) g₀ g₁ g₀ := by
  rw [fullH2_decomp (I := I) (M := M) g₀ g₁ g₀,
    fullH2_self (I := I) (M := M) g₀,
    perturbH2_eq_diff (I := I) (M := M) hDim g₀ g₁ T htie]
  abel

private lemma fullH2_inverse
    (hDim : Module.finrank ℝ E = 3)
    (g₀ g₁ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w =
        g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
    (hsmall : ‖perturbH2 (I := I) (M := M) g₀
      (ccTensorToHs (I := I) (M := M) g₀ 2 (2 : ℝ) T)‖ < 1) :
    Ring.inverse (1 + perturbH2 (I := I) (M := M) g₀
        (ccTensorToHs (I := I) (M := M) g₀ 2 (2 : ℝ) T)) =
      fullH2 (I := I) (M := M) g₀ g₀ g₁ := by
  let B := perturbH2 (I := I) (M := M) g₀
    (ccTensorToHs (I := I) (M := M) g₀ 2 (2 : ℝ) T)
  have hneg : ‖-B‖ < 1 := by
    simpa only [norm_neg, B] using hsmall
  have hu : IsUnit (1 + B) := by
    have h := isUnit_one_sub_of_norm_lt_one (x := -B) hneg
    simpa only [sub_neg_eq_add] using h
  have hleft :
      fullH2 (I := I) (M := M) g₀ g₀ g₁ * (1 + B) = 1 := by
    rw [show 1 + B = fullH2 (I := I) (M := M) g₀ g₁ g₀ from by
      simpa only [B] using
        totalH2_eq (I := I) (M := M) hDim g₀ g₁ T htie]
    exact fullH2_mul (I := I) (M := M) g₀ g₁
  have hgeom :
      fullH2 (I := I) (M := M) g₀ g₀ g₁ =
        Ring.inverse (1 + B) := by
    calc
      fullH2 (I := I) (M := M) g₀ g₀ g₁ =
          fullH2 (I := I) (M := M) g₀ g₀ g₁ * 1 :=
        (mul_one _).symm
      _ = fullH2 (I := I) (M := M) g₀ g₀ g₁ *
          ((1 + B) * Ring.inverse (1 + B)) := by
            rw [Ring.mul_inverse_cancel (1 + B) hu]
      _ = (fullH2 (I := I) (M := M) g₀ g₀ g₁ * (1 + B)) *
          Ring.inverse (1 + B) := by
            rw [mul_assoc]
      _ = Ring.inverse (1 + B) := by
        rw [hleft, one_mul]
  simpa only [B] using hgeom.symm

/-- On a smooth metric deviation, the Neumann correction is exactly the
moving inverse-metric difference acting in the leading covariant slot. -/
theorem invPerturbH2_core
    (hDim : Module.finrank ℝ E = 3)
    (g₀ g₁ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w =
        g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
    (hsmall : ‖perturbH2 (I := I) (M := M) g₀
      (ccTensorToHs (I := I) (M := M) g₀ 2 (2 : ℝ) T)‖ < 1) :
    invPerturbH2 (I := I) (M := M) g₀
        (ccTensorToHs (I := I) (M := M) g₀ 2 (2 : ℝ) T) =
      appHs (I := I) (M := M) g₀ 4 4 2
        (slotInsertEndoCc (I := I) (M := M) g₀ 3
          (gInvDiffRaisedEndoField (I := I) g₀ g₁)) := by
  change invPerturbH2 (I := I) (M := M) g₀
      (ccTensorToHs (I := I) (M := M) g₀ 2 (2 : ℝ) T) =
    diffH2 (I := I) (M := M) g₀ g₀ g₁
  rw [invPerturbH2,
    fullH2_inverse (I := I) (M := M) hDim g₀ g₁ T htie hsmall,
    fullH2_sub_one (I := I) (M := M) g₀ g₀ g₁]

/-- On a smooth small metric deviation, the low-regularity principal
correction agrees with the geometric DeTurck principal-cometric arm. -/
theorem lowRegPrincipal_core
    (hDim : Module.finrank ℝ E = 3)
    (g₀ g₁ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w =
        g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
    (hsmall : ‖perturbH2 (I := I) (M := M) g₀
      (ccTensorToHs (I := I) (M := M) g₀ 2 (2 : ℝ) T)‖ < 1) :
    lowRegPrincipal (I := I) (M := M) g₀
        (ccTensorToHs (I := I) (M := M) g₀ 2 (2 : ℝ) T) =
      principalOpH2 (I := I) (M := M) g₀ g₁ := by
  apply ContinuousLinearMap.ext
  intro U
  let ι := ccToHsLin (I := I) (M := M) g₀ 2 (4 : ℝ)
  have hdense : DenseRange ι :=
    ccToHsLin_dense (I := I) (M := M) g₀ 2 (by positivity)
  have hfun := hdense.equalizer
    (lowRegPrincipal (I := I) (M := M) g₀
      (ccTensorToHs (I := I) (M := M) g₀ 2 (2 : ℝ) T)).continuous
    (principalOpH2 (I := I) (M := M) g₀ g₁).continuous (by
      funext W
      simp only [Function.comp_apply, ι, ccToHsLin_apply]
      calc
        lowRegPrincipal (I := I) (M := M) g₀
            (ccTensorToHs (I := I) (M := M) g₀ 2 (2 : ℝ) T)
            (ccTensorToHs (I := I) (M := M) g₀ 2 (4 : ℝ) W) =
            traceH2 (I := I) (M := M) g₀
              (invPerturbH2 (I := I) (M := M) g₀
                (ccTensorToHs (I := I) (M := M) g₀ 2 (2 : ℝ) T)
                (hessianH2 (I := I) (M := M) g₀
                  (ccTensorToHs (I := I) (M := M) g₀ 2 (4 : ℝ) W))) := by
                    rfl
        _ = traceH2 (I := I) (M := M) g₀
              (appHs (I := I) (M := M) g₀ 4 4 2
                (slotInsertEndoCc (I := I) (M := M) g₀ 3
                  (gInvDiffRaisedEndoField (I := I) g₀ g₁))
                (ccTensorToHs (I := I) (M := M) g₀ 4 (2 : ℝ)
                  (iteratedCovGrad (I := I) g₀ 0 2 2 W))) := by
                    rw [hessianH2_core (I := I) (M := M) g₀ W,
                      invPerturbH2_core (I := I) (M := M)
                        hDim g₀ g₁ T htie hsmall]
        _ = traceH2 (I := I) (M := M) g₀
              (ccTensorToHs (I := I) (M := M) g₀ 4 (2 : ℝ)
                (appCc (I := I) (M := M) g₀ 4 4
                  (slotInsertEndoCc (I := I) (M := M) g₀ 3
                    (gInvDiffRaisedEndoField (I := I) g₀ g₁))
                  (iteratedCovGrad (I := I) g₀ 0 2 2 W))) := by
                    congr 1
                    exact appHs_core (I := I) (M := M) g₀ 4 4 2
                      (slotInsertEndoCc (I := I) (M := M) g₀ 3
                        (gInvDiffRaisedEndoField (I := I) g₀ g₁))
                      (iteratedCovGrad (I := I) g₀ 0 2 2 W)
        _ = ccTensorToHs (I := I) (M := M) g₀ 2 (2 : ℝ)
              (appCc (I := I) (M := M) g₀ 4 2
                (cometricDoubleTraceField (I := I) g₀ 2)
                (appCc (I := I) (M := M) g₀ 4 4
                  (slotInsertEndoCc (I := I) (M := M) g₀ 3
                    (gInvDiffRaisedEndoField (I := I) g₀ g₁))
                  (iteratedCovGrad (I := I) g₀ 0 2 2 W))) := by
                    exact traceH2_core (I := I) (M := M) g₀ _
        _ = ccTensorToHs (I := I) (M := M) g₀ 2 (2 : ℝ)
              (deTurckPrincipalCometricArm (I := I) (M := M) g₀ g₁ W) := by
                    congr 1
                    rw [deTurckPrincipalCometricArm,
                      deTurckPrincipalCometricCoeff_eq_appCcRS_doubleTrace_slotInsertEndo,
                      appCc_assoc]
        _ = principalOpH2 (I := I) (M := M) g₀ g₁
              (ccTensorToHs (I := I) (M := M) g₀ 2 (4 : ℝ) W) := by
                    exact
                      (principalOpH2_core (I := I) (M := M)
                        hDim g₀ g₁ W).symm)
  exact congrFun hfun U

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
