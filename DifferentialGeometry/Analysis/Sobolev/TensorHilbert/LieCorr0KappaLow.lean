import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.LieCorr0AMixRefold
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.IteratedCovGradFibreNormPermutationInvariance
import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.TensorHsRealize

/-!
# Low-regularity lowered connection-difference identities

This leaf contains only the lowered connection-difference and perturbative
passenger identities needed by the three-dimensional low-regularity
Ricci--DeTurck estimates. It is independent of the unfinished broad
`LieCorr0LowJet` module.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Bundle Manifold Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

/-- The moving connection difference lowered by the moving metric, viewed over
the frozen Sobolev background. -/
abbrev lc0Kappa (g₀ g₁ gB : SmoothRiemannianMetric I M) :
    SmoothCcTensor g₀ 0 3 :=
  metricConnDiffLoweredCc (I := I) (M := M) g₀ g₁ gB

/-- Fibre evaluation of the moving lowered connection difference. -/
theorem kappa_unit (g₀ g₁ gB : SmoothRiemannianMetric I M) (x : M)
    (m : Fin 3 → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 3
        (lc0Kappa (I := I) (M := M) g₀ g₁ gB) x m =
      g₁.inner x (PDE.DeTurck.connDiff (I := I) g₁ gB x (m 0) (m 1)) (m 2) := by
  rw [unitModel]
  rw [show (lc0Kappa (I := I) (M := M) g₀ g₁ gB).toSection x
      (unitTensor (I := I) (M := M) x) =
      (MixedSection.eval₀ (F := E) (E := (TangentSpace I : M → Type _)) x).smulRight
        (metricConnDiffLoweredFib (I := I) g₁ g₁ gB x)
        (ContinuousMultilinearMap.constOfIsEmpty ℝ
          (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ)) from rfl]
  rw [ContinuousLinearMap.smulRight_apply, MixedSection.eval₀_apply,
    ContinuousMultilinearMap.constOfIsEmpty_apply, one_smul]
  exact metricConnDiffLoweredFib_toModel (I := I) g₁ g₁ gB x m

set_option linter.unusedSectionVars false in
open DifferentialGeometry.Integral.DivergenceTheorem in
private theorem koszul_g1 (g₀ g₁ : SmoothRiemannianMetric I M)
    (P : SmoothCcTensor g₀ 0 2)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w +
        ccTensorBilinSymm (I := I) g₀ P y v w)
    (x : M) (a b c : TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 3
        (koszulCovecCc (I := I) g₀ P) x ![c, a, b] =
      g₁.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x a b) c := by
  rw [koszulCovecCc_unitModel (I := I) (M := M) g₀ P x a b c]
  rw [connDiffInner_g1_eq_half_covGradSymmS
    (I := I) (M := M) g₀ g₁ P htie x a b c]
  rfl

/-- The self-background lowered connection difference is exactly the cyclic
Koszul covector of the metric perturbation. -/
theorem kappa_self (g₀ g₁ : SmoothRiemannianMetric I M)
    (P : SmoothCcTensor g₀ 0 2)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w +
        ccTensorBilinSymm (I := I) g₀ P y v w) :
    lc0Kappa (I := I) (M := M) g₀ g₁ g₀ =
      domDomCongrSection (I := I) g₀ (finRotate 3).symm
        (koszulCovecCc (I := I) g₀ P) := by
  apply smoothCcTensor_ext_of_unitModel (I := I) (M := M) g₀
  intro x
  apply ContinuousMultilinearMap.ext
  intro m
  rw [kappa_unit (I := I) (M := M) g₀ g₁ g₀ x m]
  rw [domDomCongrSection_unitModel (I := I) g₀ (finRotate 3).symm
    (koszulCovecCc (I := I) g₀ P) x]
  rw [ContinuousMultilinearMap.domDomCongr_apply]
  have hτ0 : (finRotate 3).symm (0 : Fin 3) = (2 : Fin 3) := by decide
  have hτ1 : (finRotate 3).symm (1 : Fin 3) = (0 : Fin 3) := by decide
  have hτ2 : (finRotate 3).symm (2 : Fin 3) = (1 : Fin 3) := by decide
  rw [show (fun i => m ((finRotate 3).symm i)) = ![m 2, m 0, m 1] from by
    funext i
    fin_cases i
    · exact congrArg m hτ0
    · exact congrArg m hτ1
    · exact congrArg m hτ2]
  exact (koszul_g1 (I := I) (M := M) g₀ g₁ P htie x (m 0) (m 1) (m 2)).symm

private def lc0PbLowField (g₀ : SmoothRiemannianMetric I M)
    (P : SmoothCcTensor g₀ 0 2) (gA gB : SmoothRiemannianMetric I M) :
    Tensor0SBundle.Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) ∞ 3 :=
  letI := Tensor0SBundle.tensor0SBundle_topology
    (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 3
  ⟨fun x => ccBilinConnDiffLoweredFib (I := I) g₀ P gA gB x,
    ccBilinConnDiffLoweredFib_contMDiff (I := I) g₀ P gA gB⟩

/-- The perturbation paired with a fixed connection difference, viewed as a
covariant rank-three tensor over the frozen metric. -/
def lc0PbLow (g₀ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
    (gA gB : SmoothRiemannianMetric I M) : SmoothCcTensor g₀ 0 3 where
  toSection :=
    MixedSection.fromMultilinearSection (𝕜 := ℝ) (F := E) (IB := I)
      (E := (TangentSpace I : M → Type _)) ∞
      (lc0PbLowField (I := I) (M := M) g₀ P gA gB)
  hasCompactSupport := HasCompactSupport.of_compactSpace _

/-- Fibre evaluation of the perturbative lowered connection difference. -/
theorem pbLow_unit (g₀ : SmoothRiemannianMetric I M)
    (P : SmoothCcTensor g₀ 0 2) (gA gB : SmoothRiemannianMetric I M)
    (x : M) (m : Fin 3 → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 3
        (lc0PbLow (I := I) (M := M) g₀ P gA gB) x m =
      ccTensorBilinSymm (I := I) g₀ P x
        (PDE.DeTurck.connDiff (I := I) gA gB x (m 0) (m 1)) (m 2) := by
  rw [unitModel]
  rw [show (lc0PbLow (I := I) (M := M) g₀ P gA gB).toSection x
      (unitTensor (I := I) (M := M) x) =
      (MixedSection.eval₀ (F := E) (E := (TangentSpace I : M → Type _)) x).smulRight
        (lc0PbLowField (I := I) (M := M) g₀ P gA gB x)
        (ContinuousMultilinearMap.constOfIsEmpty ℝ
          (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ)) from rfl]
  rw [ContinuousLinearMap.smulRight_apply, MixedSection.eval₀_apply,
    ContinuousMultilinearMap.constOfIsEmpty_apply, one_smul]
  exact ccBilinConnDiffLoweredFib_toModel (I := I) g₀ P gA gB x m

/-- The perturbative lowered connection-difference passenger is subtractive in
the perturbation tensor. -/
theorem pbLow_sub (g₀ : SmoothRiemannianMetric I M)
    (P Q : SmoothCcTensor g₀ 0 2) (gA gB : SmoothRiemannianMetric I M) :
    lc0PbLow (I := I) (M := M) g₀ (P - Q) gA gB =
      lc0PbLow (I := I) (M := M) g₀ P gA gB -
        lc0PbLow (I := I) (M := M) g₀ Q gA gB := by
  apply smoothCcTensor_ext_of_unitModel (I := I) (M := M) g₀
  intro x
  apply ContinuousMultilinearMap.ext
  intro m
  rw [show unitModel (I := I) (M := M) g₀ 3
      (lc0PbLow (I := I) (M := M) g₀ P gA gB -
        lc0PbLow (I := I) (M := M) g₀ Q gA gB) x m =
      unitModel (I := I) (M := M) g₀ 3
          (lc0PbLow (I := I) (M := M) g₀ P gA gB) x m -
        unitModel (I := I) (M := M) g₀ 3
          (lc0PbLow (I := I) (M := M) g₀ Q gA gB) x m by
    simp only [unitModel]
    rw [SmoothCcTensor.toSection_sub, ContMDiffSection.coe_sub, Pi.sub_apply,
      ContinuousLinearMap.sub_apply, Tensor0SSpace.toModel_sub,
      ContinuousMultilinearMap.sub_apply]]
  rw [pbLow_unit (I := I) (M := M) g₀ (P - Q) gA gB x m,
    pbLow_unit (I := I) (M := M) g₀ P gA gB x m,
    pbLow_unit (I := I) (M := M) g₀ Q gA gB x m,
    ccTensorBilinSymm_sub]

set_option linter.unusedSectionVars false in
private theorem unit_add0 (g₀ : SmoothRiemannianMetric I M) (s : ℕ)
    (A B : SmoothCcTensor g₀ 0 s) (x : M) (m : Fin s → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ s (A + B) x m =
      unitModel (I := I) (M := M) g₀ s A x m +
        unitModel (I := I) (M := M) g₀ s B x m := by
  rw [unitModel, unitModel, unitModel]
  rw [show (A + B).toSection x = A.toSection x + B.toSection x from by
    rw [SmoothCcTensor.toSection_add]; rfl]
  rw [show ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
      A.toSection x + B.toSection x) (unitTensor (I := I) (M := M) x)) =
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from A.toSection x)
          (unitTensor (I := I) (M := M) x) +
        (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from B.toSection x)
          (unitTensor (I := I) (M := M) x) from rfl]
  rw [Tensor0SSpace.toModel_add, ContinuousMultilinearMap.add_apply]

/-- The moving-metric lowered connection difference splits into the
self-background Koszul term, the fixed background connection difference, and
the perturbative passenger. -/
theorem kappa_bg (g₀ g₁ gB : SmoothRiemannianMetric I M)
    (P : SmoothCcTensor g₀ 0 2)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w +
        ccTensorBilinSymm (I := I) g₀ P y v w) :
    lc0Kappa (I := I) (M := M) g₀ g₁ gB =
      lc0Kappa (I := I) (M := M) g₀ g₁ g₀ +
        lc0Kappa (I := I) (M := M) g₀ g₀ gB +
        lc0PbLow (I := I) (M := M) g₀ P g₀ gB := by
  apply smoothCcTensor_ext_of_unitModel (I := I) (M := M) g₀
  intro x
  apply ContinuousMultilinearMap.ext
  intro m
  rw [unit_add0 (I := I) (M := M) g₀ 3 _ _ x m,
    unit_add0 (I := I) (M := M) g₀ 3 _ _ x m]
  rw [kappa_unit (I := I) (M := M) g₀ g₁ gB x m,
    kappa_unit (I := I) (M := M) g₀ g₁ g₀ x m,
    kappa_unit (I := I) (M := M) g₀ g₀ gB x m,
    pbLow_unit (I := I) (M := M) g₀ P g₀ gB x m]
  rw [htie x (PDE.DeTurck.connDiff (I := I) g₁ gB x (m 0) (m 1)) (m 2)]
  rw [PDE.DeTurck.connDiff_cocycle (I := I) g₀ g₁ gB x (m 0) (m 1)]
  rw [htie x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (m 0) (m 1)) (m 2)]
  rw [map_add (g₀.inner x), map_add (ccTensorBilinSymm (I := I) g₀ P x)]
  rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.add_apply]
  ring

/-- Reversing a fixed connection difference reverses its frozen lowering. -/
theorem kappa_base_neg (g₀ gB : SmoothRiemannianMetric I M) :
    lc0Kappa (I := I) (M := M) g₀ g₀ gB =
      -connDiffLoweredCc (I := I) g₀ gB := by
  apply smoothCcTensor_ext_of_unitModel (I := I) (M := M) g₀
  intro x
  apply ContinuousMultilinearMap.ext
  intro m
  rw [kappa_unit (I := I) (M := M) g₀ g₀ gB x m]
  rw [show unitModel (I := I) (M := M) g₀ 3
      (-connDiffLoweredCc (I := I) g₀ gB) x =
      -unitModel (I := I) (M := M) g₀ 3
        (connDiffLoweredCc (I := I) g₀ gB) x by
    simp only [unitModel]
    rw [SmoothCcTensor.toSection_neg, ContMDiffSection.coe_neg, Pi.neg_apply,
      ContinuousLinearMap.neg_apply, Tensor0SSpace.toModel_neg]]
  rw [ContinuousMultilinearMap.neg_apply,
    connDiffLoweredCc_unitModel_apply']
  have hcycle := PDE.DeTurck.connDiff_cocycle
    (I := I) gB g₀ g₀ x (m 0) (m 1)
  rw [PDE.DeTurck.connDiff_self] at hcycle
  have hneg :
      PDE.DeTurck.connDiff (I := I) g₀ gB x (m 0) (m 1) =
        -PDE.DeTurck.connDiff (I := I) gB g₀ x (m 0) (m 1) :=
    eq_neg_of_add_eq_zero_left hcycle.symm
  rw [hneg, map_neg, ContinuousLinearMap.neg_apply]

set_option linter.unusedSectionVars false in
private theorem ip_toModel (s : ℕ) (x : M) (v : TangentSpace I x)
    (D : Tensor0SSpace (s + 1) I x) (w : Fin s → TangentSpace I x) :
    Tensor0SSpace.toModel
        (Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) s x v D) w =
      Tensor0SSpace.toModel D
        (Fin.cons (show E from v) (fun k => (show E from w k))) := by
  have h1 : Tensor0SSpace.toModel
      (Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) s x v D) =
      Tensor0SBundle.model_interior_product (𝕜 := ℝ) (E := E) s
        (show E from v) (Tensor0SSpace.toModel D) := rfl
  rw [h1]
  rfl

/-- Raising and cyclically rotating the perturbative passenger exposes the
fixed connection-difference operator acting on the raised perturbation. -/
theorem pbLow_raise (g₀ gB : SmoothRiemannianMetric I M)
    (P : SmoothCcTensor g₀ 0 2) :
    cometricRaiseSlot0Field (I := I) (M := M) g₀ 1
        (domDomCongrSection (I := I) g₀ (finRotate 3)
          (lc0PbLow (I := I) (M := M) g₀ P g₀ gB)) =
      appCcRS (I := I) (M := M) g₀ 1 1 2
        (lieArm1FixCd (I := I) (M := M) g₀ gB)
        (cometricRaiseSlot0Field (I := I) (M := M) g₀ 0
          (symmS (I := I) (M := M) g₀ P)) := by
  apply Integral.L2.SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [cometricRaiseSlot0Field_toSection, appCcRS_toSection]
  apply tensorRSSpace_ext 1 2 x
  intro om
  apply ContinuousMultilinearMap.ext
  intro YZ
  set u : TangentSpace I x := inverseMetricSharpFib (I := I) g₀ x om with hu
  set D : Tensor0SSpace 3 I x :=
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
      (domDomCongrSection (I := I) g₀ (finRotate 3)
        (lc0PbLow (I := I) (M := M) g₀ P g₀ gB)).toSection x)
      (unitTensor (I := I) (M := M) x) with hDdef
  have hLHS : (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from
        cometricRaiseSlot0Fib (I := I) g₀ 1 x D) om YZ =
      Tensor0SSpace.toModel D
        (Fin.cons (show E from u) (fun k => (show E from YZ k))) := by
    rw [cometricRaiseSlot0Fib_clm_apply (I := I) g₀ 1 x D om]
    rw [show (Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) (1 + 1) x
          (inverseMetricSharpFib (I := I) g₀ x om) D YZ : ℝ) =
        Tensor0SSpace.toModel
          (Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) (1 + 1) x
            (inverseMetricSharpFib (I := I) g₀ x om) D) YZ from rfl]
    rw [ip_toModel (I := I) (M := M) (1 + 1) x
      (inverseMetricSharpFib (I := I) g₀ x om) D YZ, ← hu]
  have hLHSval : Tensor0SSpace.toModel D
      (Fin.cons (show E from u) (fun k => (show E from YZ k))) =
      ccTensorBilinSymm (I := I) g₀ P x
        (PDE.DeTurck.connDiff (I := I) g₀ gB x (YZ 0) (YZ 1)) u := by
    have hum : unitModel (I := I) (M := M) g₀ 3
        (domDomCongrSection (I := I) g₀ (finRotate 3)
          (lc0PbLow (I := I) (M := M) g₀ P g₀ gB)) x =
        Tensor0SSpace.toModel D := rfl
    rw [show Tensor0SSpace.toModel D
          (Fin.cons (show E from u) (fun k => (show E from YZ k))) =
        unitModel (I := I) (M := M) g₀ 3
          (domDomCongrSection (I := I) g₀ (finRotate 3)
            (lc0PbLow (I := I) (M := M) g₀ P g₀ gB)) x
          ![u, YZ 0, YZ 1] from by
      rw [hum]
      congr 1
      funext k
      fin_cases k <;> rfl]
    rw [domDomCongrSection_unitModel, ContinuousMultilinearMap.domDomCongr_apply]
    rw [show (fun i => (![u, YZ 0, YZ 1] : Fin 3 → TangentSpace I x)
          ((finRotate 3) i)) = ![YZ 0, YZ 1, u] from by
      funext i
      fin_cases i <;> simp [finRotate_succ_apply]]
    rw [pbLow_unit (I := I) (M := M) g₀ P g₀ gB x ![YZ 0, YZ 1, u]]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons]
  have hRHS : ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from
        (lieArm1FixCd (I := I) (M := M) g₀ gB).toSection x).comp
        (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
          (cometricRaiseSlot0Field (I := I) (M := M) g₀ 0
            (symmS (I := I) (M := M) g₀ P)).toSection x)) om YZ =
      ccTensorBilinSymm (I := I) g₀ P x
        (PDE.DeTurck.connDiff (I := I) g₀ gB x (YZ 0) (YZ 1)) u := by
    rw [ContinuousLinearMap.comp_apply]
    set om' : Tensor0SSpace 1 I x :=
      (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
        (cometricRaiseSlot0Field (I := I) (M := M) g₀ 0
          (symmS (I := I) (M := M) g₀ P)).toSection x) om with hom'
    rw [show (lieArm1FixCd (I := I) (M := M) g₀ gB).toSection x =
      connDiffFib (I := I) g₀ gB x from rfl]
    rw [connDiffFib_apply_eval (I := I) g₀ gB x om' YZ]
    rw [show om' (fun _ : Fin 1 =>
        PDE.DeTurck.connDiff (I := I) g₀ gB x (YZ 0) (YZ 1)) =
        Tensor0SSpace.toModel om' (fun _ : Fin 1 => (show E from
          PDE.DeTurck.connDiff (I := I) g₀ gB x (YZ 0) (YZ 1))) from rfl]
    rw [hom']
    rw [show ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
        (cometricRaiseSlot0Field (I := I) (M := M) g₀ 0
          (symmS (I := I) (M := M) g₀ P)).toSection x) om) =
        cometricRaiseSlot0Fib (I := I) g₀ 0 x
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
            (symmS (I := I) (M := M) g₀ P).toSection x)
            (unitTensor (I := I) (M := M) x)) om from by
      rw [cometricRaiseSlot0Field_toSection]]
    rw [cometricRaiseSlot0Fib_clm_apply (I := I) g₀ 0 x _ om]
    rw [show Tensor0SSpace.toModel
        (Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) (0 + 1) x
          (inverseMetricSharpFib (I := I) g₀ x om)
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
            (symmS (I := I) (M := M) g₀ P).toSection x)
            (unitTensor (I := I) (M := M) x)))
        (fun _ : Fin 1 => (show E from
          PDE.DeTurck.connDiff (I := I) g₀ gB x (YZ 0) (YZ 1))) =
        Tensor0SSpace.toModel
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
            (symmS (I := I) (M := M) g₀ P).toSection x)
            (unitTensor (I := I) (M := M) x))
          (Fin.cons (show E from u)
            (fun _ : Fin 1 => (show E from
              PDE.DeTurck.connDiff (I := I) g₀ gB x (YZ 0) (YZ 1)))) from by
      rw [ip_toModel (I := I) (M := M) (0 + 1) x
        (inverseMetricSharpFib (I := I) g₀ x om) _ _, ← hu]]
    rw [show Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
          (symmS (I := I) (M := M) g₀ P).toSection x)
          (unitTensor (I := I) (M := M) x))
        (Fin.cons (show E from u)
          (fun _ : Fin 1 => (show E from
            PDE.DeTurck.connDiff (I := I) g₀ gB x (YZ 0) (YZ 1)))) =
        unitModel (I := I) (M := M) g₀ 2
          (symmS (I := I) (M := M) g₀ P) x
          ![u, PDE.DeTurck.connDiff (I := I) g₀ gB x (YZ 0) (YZ 1)] from by
      rw [unitModel]
      congr 1
      funext k
      fin_cases k <;> rfl]
    rw [unitModel_eq_ccTensorBilin_local (I := I) (M := M) g₀
      (symmS (I := I) (M := M) g₀ P) x u
      (PDE.DeTurck.connDiff (I := I) g₀ gB x (YZ 0) (YZ 1))]
    rw [ccTensorBilin_symmS (I := I) (M := M) g₀ P x u
      (PDE.DeTurck.connDiff (I := I) g₀ gB x (YZ 0) (YZ 1))]
    exact ccTensorBilinSymm_symm (I := I) g₀ P x u
      (PDE.DeTurck.connDiff (I := I) g₀ gB x (YZ 0) (YZ 1))
  rw [hLHS, hLHSval]
  exact hRHS.symm

/-- The perturbative passenger and its raised operator realization have equal
pointwise covariant-jet norms. -/
theorem pbLow_rfns (g₀ gB : SmoothRiemannianMetric I M)
    (P : SmoothCcTensor g₀ 0 2) (n : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + n) x
        ((iteratedCovGrad (I := I) g₀ 0 3 n
          (lc0PbLow (I := I) (M := M) g₀ P g₀ gB)).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + n) x
        ((iteratedCovGrad (I := I) g₀ 1 2 n
          (appCcRS (I := I) (M := M) g₀ 1 1 2
            (lieArm1FixCd (I := I) (M := M) g₀ gB)
            (cometricRaiseSlot0Field (I := I) (M := M) g₀ 0
              (symmS (I := I) (M := M) g₀ P)))).toSection x) := by
  calc
    riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + n) x
        ((iteratedCovGrad (I := I) g₀ 0 3 n
          (lc0PbLow (I := I) (M := M) g₀ P g₀ gB)).toSection x)
        = riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + n) x
            ((iteratedCovGrad (I := I) g₀ 0 3 n
              (domDomCongrSection (I := I) g₀ (finRotate 3)
                (lc0PbLow (I := I) (M := M) g₀ P g₀ gB))).toSection x) :=
          (riemannianFiberNormSq_iteratedCovGrad_domDomCongrSection
            (I := I) (M := M) g₀ (finRotate 3)
            (lc0PbLow (I := I) (M := M) g₀ P g₀ gB) n x).symm
    _ = riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + n) x
          ((iteratedCovGrad (I := I) g₀ 1 2 n
            (cometricRaiseSlot0Field (I := I) (M := M) g₀ 1
              (domDomCongrSection (I := I) g₀ (finRotate 3)
                (lc0PbLow (I := I) (M := M) g₀ P g₀ gB)))).toSection x) :=
        (rfns_iteratedCovGrad_cometricRaiseSlot0Field_eq
          (I := I) (M := M) g₀ 1
          (domDomCongrSection (I := I) g₀ (finRotate 3)
            (lc0PbLow (I := I) (M := M) g₀ P g₀ gB)) n x).symm
    _ = riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + n) x
          ((iteratedCovGrad (I := I) g₀ 1 2 n
            (appCcRS (I := I) (M := M) g₀ 1 1 2
              (lieArm1FixCd (I := I) (M := M) g₀ gB)
              (cometricRaiseSlot0Field (I := I) (M := M) g₀ 0
                (symmS (I := I) (M := M) g₀ P)))).toSection x) := by
        rw [pbLow_raise (I := I) (M := M) g₀ gB P]

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral
