import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.LowRegPathSplit
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.RHSRefoldPathIntegral
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.RHSRefoldField
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.EdgeRicciPairing
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.LieCorr0Split
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciArmResidualCoefficientFields
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.PrincipalCoeffH2
import DifferentialGeometry.Analysis.Spectral.Tensor.Estimates.H1H2AppCc
import DifferentialGeometry.Analysis.Spectral.Tensor.Estimates.H1H2AppCcRS
import DifferentialGeometry.Analysis.Spectral.Tensor.Estimates.H2H4Principal
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.ParametricJetIntegral
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.LieCorr0TraceRadiusFree
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.LieCorr0VBRefold
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.LieCorr0CoeffDiffRadiusFree
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.RicciArmResidualFieldGridWindow
/-!
# Low-base Ricci--DeTurck remainder actions

This module gives the fixed-order smooth-core action split used by uniform
low-regularity Ricci--DeTurck existence.  The dangerous Ricci zero-head is
refolded at the self-action level before any Sobolev estimate is taken.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped BigOperators Manifold ContDiff
namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace IntrinsicSpectral
open DifferentialGeometry
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert
open DifferentialGeometry.PDE.DeTurck.RicciLinearization
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurckCoefficients
open LieCorr0Core
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
    [BoundarylessManifold I M] in
private theorem zero_eq_unit (x : M) (D : Tensor0SSpace 0 I x) :
    D = (Tensor0SNabla.tensor0Iso I M x D) •
      unitTensor (I := I) (M := M) x := by
  classical
  have hunit :
      Tensor0SNabla.tensor0Iso I M x
          (unitTensor (I := I) (M := M) x) = (1 : ℝ) := by
    have h := Tensor0SNabla.scalarFn_unitZero (I := I) (M := M)
    have hx := congrFun h x
    simpa [Tensor0SNabla.scalarFn_apply, unitTensor] using hx
  apply (Tensor0SNabla.tensor0Iso I M x).injective
  rw [map_smul, hunit, smul_eq_mul, mul_one]
/-! ## The fixed Koszul operator -/
private theorem permCoeff_app
    (g : SmoothRiemannianMetric I M) {d : ℕ}
    (ρ : Equiv.Perm (Fin d)) (S : SmoothCcTensor g 0 d) :
    appCcRS (I := I) (M := M) g 0 d d
        (permCoeff (I := I) (M := M) g ρ) S =
      domDomCongrSection (I := I) g ρ S := by
  refine smoothCcTensor_ext_of_unitModel (I := I) (M := M) g fun x => ?_
  rw [domDomCongrSection_unitModel]
  rw [unitModel, appCcRS_toSection, ContinuousLinearMap.comp_apply]
  change Tensor0SSpace.toModel
      (slotPermCLM (I := I) ρ x
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace d I x from
          S.toSection x) (unitTensor (I := I) (M := M) x))) = _
  rw [slotPermCLM_apply, Tensor0SSpace.toModel_ofModel]
  rfl
private theorem app_smul_left
    (g : SmoothRiemannianMetric I M) (a b c : ℕ) (k : ℝ)
    (Φ : SmoothCcTensor g b c) (W : SmoothCcTensor g a b) :
    appCcRS (I := I) (M := M) g a b c (k • Φ) W =
      k • appCcRS (I := I) (M := M) g a b c Φ W := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [appCcRS_toSection]
  rw [show (k • appCcRS (I := I) (M := M) g a b c Φ W).toSection x =
      k • (appCcRS (I := I) (M := M) g a b c Φ W).toSection x from rfl]
  rw [appCcRS_toSection, SmoothCcTensor.toSection_smul,
    ContMDiffSection.coe_smul, Pi.smul_apply]
  exact ContinuousLinearMap.smul_comp k
    (show Tensor0SSpace b I x →L[ℝ] Tensor0SSpace c I x from Φ.toSection x)
    (show Tensor0SSpace a I x →L[ℝ] Tensor0SSpace b I x from W.toSection x)
private def koszulOp
    (g : SmoothRiemannianMetric I M) : SmoothCcTensor g 3 3 :=
  (1 / 2 : ℝ) •
    (permCoeff (I := I) (M := M) g (Equiv.swap (0 : Fin 3) 2) +
      permCoeff (I := I) (M := M) g (finRotate 3) -
      permCoeff (I := I) (M := M) g (Equiv.swap (1 : Fin 3) 2))
private theorem symm_eq_self
    (g : SmoothRiemannianMetric I M) (S : SmoothCcTensor g 0 2)
    (hS : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g S x u v =
        ccTensorBilin (I := I) g S x v u) :
    symmS (I := I) (M := M) g S = S := by
  have hswap :
      domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 2) 1) S = S := by
    refine smoothCcTensor_ext_of_unitModel (I := I) (M := M) g fun x => ?_
    rw [domDomCongrSection_unitModel]
    refine ContinuousMultilinearMap.ext fun v => ?_
    rw [ContinuousMultilinearMap.domDomCongr_apply]
    have hv : ∀ u w : TangentSpace I x,
        unitModel (I := I) (M := M) g 2 S x ![u, w] =
          unitModel (I := I) (M := M) g 2 S x ![w, u] := by
      intro u w
      rw [unitModel_eq_ccTensorBilin_local (I := I) (M := M) g S x u w,
        unitModel_eq_ccTensorBilin_local (I := I) (M := M) g S x w u]
      exact hS x u w
    have hveta :
        (fun i => v ((Equiv.swap (0 : Fin 2) 1) i)) = ![v 1, v 0] := by
      funext i
      fin_cases i <;> rfl
    have hveta' : v = ![v 0, v 1] := by
      funext i
      fin_cases i <;> rfl
    rw [hveta]
    conv_rhs => rw [hveta']
    exact hv (v 1) (v 0)
  have htwo : S + S = (2 : ℝ) • S := (two_smul ℝ S).symm
  rw [symmS, hswap, htwo, smul_smul,
    show (1 / 2 : ℝ) * 2 = 1 by norm_num, one_smul]
private theorem koszulOp_app
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    (hT : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g T x u v =
        ccTensorBilin (I := I) g T x v u) :
    appCcRS (I := I) (M := M) g 0 3 3
        (koszulOp (I := I) (M := M) g)
        (covGrad (I := I) (M := M) g 0 2 T) =
      koszulCovecCc (I := I) g T := by
  have hs := symm_eq_self (I := I) (M := M) g T hT
  rw [koszulOp, app_smul_left, appCcRS_sub_left,
    appCcRS_add_left, permCoeff_app, permCoeff_app, permCoeff_app]
  rw [koszulCovecCc, symmSCovGrad3, hs]
private theorem raised_inner
    (g gm : SmoothRiemannianMetric I M) (x : M)
    (v w : TangentSpace I x) :
    gm.inner x (fullRaisedEndoField (I := I) (M := M) g gm x v) w =
      g.inner x v w := by
  rw [fullRaisedEndoField_apply, gInvRaisedEndo_apply]
  rw [inverseMetricSharpFib_inner (I := I) gm x
    (g0FlatCLM (I := I) g x v) w]
  rw [show cotangentToDualLinear (I := I) (x := x)
      (g0FlatCLM (I := I) g x v) w =
        cotangentToDual (I := I) (x := x)
          (g0FlatCLM (I := I) g x v) w from rfl]
  rw [cotangentToDual_g0FlatCLM]
private def lowPerm : Equiv.Perm (Fin 3) :=
  ⟨![2, 0, 1], ![1, 2, 0], by decide, by decide⟩
private def connLowOp
    (g gm : SmoothRiemannianMetric I M) : SmoothCcTensor g 3 3 :=
  appCcRS (I := I) (M := M) g 3 3 3
    (permCoeff (I := I) (M := M) g lowPerm)
    (appCcRS (I := I) (M := M) g 3 3 3
      (slotInsertEndoCc (I := I) (M := M) g 2
        (fullRaisedEndoField (I := I) (M := M) g gm))
      (koszulOp (I := I) (M := M) g))
private theorem connLower_unit
    (g gm : SmoothRiemannianMetric I M) (x : M)
    (v : Fin 3 → TangentSpace I x) :
    unitModel (I := I) (M := M) g 3
        (connDiffLoweredCc (I := I) g gm) x v =
      g.inner x (PDE.DeTurck.connDiff (I := I) gm g x (v 0) (v 1))
        (v 2) := by
  rw [unitModel]
  rw [show (connDiffLoweredCc (I := I) g gm).toSection x
        (unitTensor (I := I) (M := M) x) =
      (MixedSection.eval₀ (F := E)
          (E := (TangentSpace I : M → Type _)) x).smulRight
        (connDiffLoweredField (I := I) g gm x)
        (ContinuousMultilinearMap.constOfIsEmpty ℝ
          (fun _ : Fin 0 => TangentSpace I x) 1) from rfl]
  rw [ContinuousLinearMap.smulRight_apply, MixedSection.eval₀_apply,
    ContinuousMultilinearMap.constOfIsEmpty_apply, one_smul]
  rfl
private theorem connLowerK
    (g gm : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    (htie : ∀ (x : M) (u v : TangentSpace I x),
      gm.inner x u v =
        g.inner x u v + ccTensorBilinSymm (I := I) g T x u v) :
    appCc (I := I) (M := M) g 3 3
        (permCoeff (I := I) (M := M) g lowPerm)
        (appCc (I := I) (M := M) g 3 3
          (slotInsertEndoCc (I := I) (M := M) g 2
            (fullRaisedEndoField (I := I) (M := M) g gm))
          (koszulCovecCc (I := I) g T)) =
      connDiffLoweredCc (I := I) g gm := by
  rw [← appCcRS_zero_eq_appCc, permCoeff_app]
  refine smoothCcTensor_ext_of_unitModel (I := I) (M := M) g fun x => ?_
  refine ContinuousMultilinearMap.ext fun v => ?_
  rw [domDomCongrSection_unitModel,
    ContinuousMultilinearMap.domDomCongr_apply]
  have hv :
      (fun i => v (lowPerm i)) = ![v 2, v 0, v 1] := by
    funext i
    fin_cases i <;> rfl
  rw [hv]
  rw [unitModel, appCc_toSection, ContinuousLinearMap.comp_apply,
    slotInsertEndoCc_toSection, slotInsertEndoFib_apply_eval]
  have hu :
      Function.update ![v 2, v 0, v 1] 0
          (fullRaisedEndoField (I := I) (M := M) g gm x
            ((![v 2, v 0, v 1] : Fin 3 → TangentSpace I x) 0)) =
        ![fullRaisedEndoField (I := I) (M := M) g gm x (v 2),
          v 0, v 1] := by
    funext i
    fin_cases i <;> simp
  rw [hu]
  rw [show Tensor0SSpace.toModel
      ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
        (koszulCovecCc (I := I) g T).toSection x)
        (unitTensor (I := I) (M := M) x))
      ![fullRaisedEndoField (I := I) (M := M) g gm x (v 2),
        v 0, v 1] =
      unitModel (I := I) (M := M) g 3
        (koszulCovecCc (I := I) g T) x
        ![fullRaisedEndoField (I := I) (M := M) g gm x (v 2),
          v 0, v 1] from rfl]
  rw [koszulCovecCc_unitModel (I := I) g T x (v 0) (v 1)
    (fullRaisedEndoField (I := I) (M := M) g gm x (v 2))]
  rw [symmSCovGrad3_def]
  rw [← connDiffInner_g1_eq_half_covGradSymmS
    (I := I) (M := M) g gm T htie x (v 0) (v 1)
      (fullRaisedEndoField (I := I) (M := M) g gm x (v 2))]
  rw [gm.symm x
    (PDE.DeTurck.connDiff (I := I) gm g x (v 0) (v 1))
    (fullRaisedEndoField (I := I) (M := M) g gm x (v 2))]
  rw [raised_inner (I := I) (M := M) g gm x, g.symm x]
  change g.inner x (PDE.DeTurck.connDiff (I := I) gm g x (v 0) (v 1))
      (v 2) =
    unitModel (I := I) (M := M) g 3
      (connDiffLoweredCc (I := I) g gm) x v
  rw [connLower_unit (I := I) (M := M) g gm x v]
private theorem connLowOp_app
    (g gm : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    (hT : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g T x u v =
        ccTensorBilin (I := I) g T x v u)
    (htie : ∀ (x : M) (u v : TangentSpace I x),
      gm.inner x u v =
        g.inner x u v + ccTensorBilinSymm (I := I) g T x u v) :
    appCcRS (I := I) (M := M) g 0 3 3
        (connLowOp (I := I) (M := M) g gm)
        (covGrad (I := I) (M := M) g 0 2 T) =
      connDiffLoweredCc (I := I) g gm := by
  rw [appCcRS_zero_eq_appCc, connLowOp, ← appCc_assoc, ← appCc_assoc]
  rw [show appCc (I := I) (M := M) g 3 3
      (koszulOp (I := I) (M := M) g)
      (covGrad (I := I) (M := M) g 0 2 T) =
        koszulCovecCc (I := I) g T by
      rw [← appCcRS_zero_eq_appCc]
      exact koszulOp_app (I := I) (M := M) g T hT]
  exact connLowerK (I := I) (M := M) g gm T htie
/-! ## Action-level extraction of the Ricci derivative head -/
private def daPermA : Equiv.Perm (Fin 4) :=
  ⟨![1, 2, 3, 0], ![3, 0, 1, 2], by decide, by decide⟩
private def daPermB : Equiv.Perm (Fin 4) :=
  ⟨![1, 0, 2, 3], ![1, 0, 2, 3], by decide, by decide⟩
private def gradRotate : Equiv.Perm (Fin 4) :=
  ⟨![0, 2, 3, 1], ![0, 3, 1, 2], by decide, by decide⟩
private theorem ricciDAG_perm
    (g gm : SmoothRiemannianMetric I M) :
    ricciDAG (I := I) (M := M) g gm =
      appCcRS (I := I) (M := M) g 0 4 4
        (permCoeff (I := I) (M := M) g daPermA)
        (covGrad (I := I) (M := M) g 0 3
          (connDiffLoweredCc (I := I) g gm)) := by
  rw [permCoeff_app]
  let S : SmoothCcTensor g 0 3 := connDiffLoweredCc (I := I) g gm
  let S' : SmoothCcTensor g 0 3 :=
    domDomCongrSection (I := I) g (finRotate 3) S
  have hrel : ∀ (y : M) (d : Tensor0SSpace 0 I y),
      Tensor0SSpace.toModel
          ((show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace 3 I y from
            S'.toSection y) d) =
        ContinuousMultilinearMap.domDomCongr (finRotate 3)
          (Tensor0SSpace.toModel
            ((show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace 3 I y from
              S.toSection y) d)) := by
    intro y d
    rw [zero_eq_unit (I := I) (M := M) y d, map_smul, map_smul,
      Tensor0SSpace.toModel_smul, Tensor0SSpace.toModel_smul]
    rw [show Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace 3 I y from
          S'.toSection y) (unitTensor (I := I) (M := M) y)) =
      unitModel (I := I) (M := M) g 3 S' y from rfl]
    rw [show Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace 3 I y from
          S.toSection y) (unitTensor (I := I) (M := M) y)) =
      unitModel (I := I) (M := M) g 3 S y from rfl]
    rw [show S' = domDomCongrSection (I := I) g (finRotate 3) S from rfl,
      domDomCongrSection_unitModel]
    apply ContinuousMultilinearMap.ext
    intro v
    rw [ContinuousMultilinearMap.smul_apply,
      ContinuousMultilinearMap.domDomCongr_apply,
      ContinuousMultilinearMap.domDomCongr_apply,
      ContinuousMultilinearMap.smul_apply]
  refine smoothCcTensor_ext_of_unitModel (I := I) (M := M) g fun x => ?_
  refine ContinuousMultilinearMap.ext fun v => ?_
  rw [ricciDAG_eval (I := I) (M := M) g gm x v]
  rw [domDomCongrSection_unitModel,
    ContinuousMultilinearMap.domDomCongr_apply]
  have hda :
      (fun i => v (daPermA i)) = ![v 1, v 2, v 3, v 0] := by
    funext i
    fin_cases i <;> rfl
  rw [hda]
  have hnat := covGrad_rs_toModel_domDomCongr
    (I := I) (M := M) g 0 3 (finRotate 3) S S' hrel x
    (unitTensor (I := I) (M := M) x) ![v 1, v 0, v 2, v 3]
  change unitModel (I := I) (M := M) g 4
      (covGrad (I := I) (M := M) g 0 3 S') x
        ![v 1, v 0, v 2, v 3] =
    unitModel (I := I) (M := M) g 4
      (covGrad (I := I) (M := M) g 0 3 S) x
        ![v 1, v 2, v 3, v 0]
  rw [show S' = domDomCongrSection (I := I) g (finRotate 3) S from rfl]
  change Tensor0SSpace.toModel
      ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 4 I x from
        (covGrad (I := I) (M := M) g 0 3
          (domDomCongrSection (I := I) g (finRotate 3) S)).toSection x)
        (unitTensor (I := I) (M := M) x)) _ = _
  rw [hnat]
  rw [ContinuousMultilinearMap.domDomCongr_apply]
  have hgrad :
      Equiv.Perm.decomposeFin.symm (0, finRotate 3) = gradRotate := by
    apply Equiv.ext
    intro i
    fin_cases i <;> decide
  rw [hgrad]
  congr 1
  funext i
  fin_cases i <;> rfl
private def dagLowOp
    (g gm : SmoothRiemannianMetric I M) : SmoothCcTensor g 3 4 :=
  appCcRS (I := I) (M := M) g 3 4 4
    (permCoeff (I := I) (M := M) g daPermA)
    (covGrad (I := I) (M := M) g 3 3
      (connLowOp (I := I) (M := M) g gm))
private def dagTopOp
    (g gm : SmoothRiemannianMetric I M) : SmoothCcTensor g 4 4 :=
  appCcRS (I := I) (M := M) g 4 4 4
    (permCoeff (I := I) (M := M) g daPermA)
    (slotExtend (I := I) (M := M) g 3 3
      (connLowOp (I := I) (M := M) g gm))
private theorem ricciDAG_split
    (g gm : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    (hT : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g T x u v =
        ccTensorBilin (I := I) g T x v u)
    (htie : ∀ (x : M) (u v : TangentSpace I x),
      gm.inner x u v =
        g.inner x u v + ccTensorBilinSymm (I := I) g T x u v) :
    ricciDAG (I := I) (M := M) g gm =
      appCcRS (I := I) (M := M) g 0 3 4
          (dagLowOp (I := I) (M := M) g gm)
          (covGrad (I := I) (M := M) g 0 2 T) +
        appCcRS (I := I) (M := M) g 0 4 4
          (dagTopOp (I := I) (M := M) g gm)
          (iteratedCovGrad (I := I) g 0 2 2 T) := by
  rw [ricciDAG_perm (I := I) (M := M) g gm]
  rw [← connLowOp_app (I := I) (M := M) g gm T hT htie]
  rw [covGrad_appCcRS_eq, appCcRS_add_right]
  rw [appCcRS_zero_eq_appCc, appCcRS_zero_eq_appCc, appCc_assoc]
  rw [appCcRS_zero_eq_appCc, appCcRS_zero_eq_appCc, appCc_assoc]
  simp only [dagLowOp, dagTopOp, appCcRS_zero_eq_appCc,
    iteratedCovGrad_succ, iteratedCovGrad_zero]
private def daMono
    (g gm : SmoothRiemannianMetric I M) (G : SmoothCcTensor g 0 4)
    (σ : Equiv.Perm (Fin 4)) : SmoothCcTensor g 2 2 :=
  appCcRS (I := I) (M := M) g 2 2 2
    (refoldKernelContractionMonomialField (I := I) (M := M) g g G σ)
    (slotInsertEndoCc (I := I) (M := M) g 1
      (fullRaisedEndoField (I := I) (M := M) g gm))
private def daContr
    (g gm : SmoothRiemannianMetric I M) (G : SmoothCcTensor g 0 4) :
    SmoothCcTensor g 2 2 :=
  daMono (I := I) (M := M) g gm G daPermA -
    daMono (I := I) (M := M) g gm G daPermB
private def daWeight
    (g gm : SmoothRiemannianMetric I M) (W : SmoothCcTensor g 0 2) :
    SmoothCcTensor g 0 2 :=
  appCc (I := I) (M := M) g 2 2
    (slotInsertEndoCc (I := I) (M := M) g 1
      (fullRaisedEndoField (I := I) (M := M) g gm)) W
private theorem daWeight_cap
    (g gm : SmoothRiemannianMetric I M)
    (P W : SmoothCcTensor g 0 2)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      gm.inner y v w =
        g.inner y v w + ccTensorBilinSymm (I := I) g P y v w)
    {δ η : ℝ} (hδ_lt : δ < 1) (hδ : 0 ≤ δ)
    (hP : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g P) δ)
    (hη : 0 ≤ η)
    (hW : ∀ (y : M) (v w : TangentSpace I y),
      |ccTensorBilin (I := I) g W y v w| ≤
        η * Real.sqrt (g.inner y v v) *
          Real.sqrt (g.inner y w w))
    (y : M) (v w : TangentSpace I y) :
    |Tensor0SSpace.toModel
        (ccTensorUnitValueSection (I := I) (M := M) g
          (daWeight (I := I) (M := M) g gm W) y)
        ![(v : E), (w : E)]| ≤
      (η / (1 - δ)) * Real.sqrt (g.inner y v v) *
        Real.sqrt (g.inner y w w) := by
  have hval :
      Tensor0SSpace.toModel
          (ccTensorUnitValueSection (I := I) (M := M) g
            (daWeight (I := I) (M := M) g gm W) y)
          ![(v : E), (w : E)] =
        ccTensorBilin (I := I) g W y
          (fullRaisedEndoField (I := I) (M := M) g gm y v) w := by
    rw [show Tensor0SSpace.toModel
        (ccTensorUnitValueSection (I := I) (M := M) g
          (daWeight (I := I) (M := M) g gm W) y) =
      unitModel (I := I) (M := M) g 2
        (daWeight (I := I) (M := M) g gm W) y from rfl]
    simp only [daWeight, unitModel, appCc_toSection,
      ContinuousLinearMap.comp_apply, slotInsertEndoCc_toSection,
      slotInsertEndoFib_apply_eval]
    have hu :
        Function.update ![v, w] 0
            (fullRaisedEndoField (I := I) (M := M) g gm y
              ((![v, w] : Fin 2 → TangentSpace I y) 0)) =
          ![fullRaisedEndoField (I := I) (M := M) g gm y v, w] := by
      funext i
      fin_cases i <;> simp
    rw [hu]
    change unitModel (I := I) (M := M) g 2 W y
        ![fullRaisedEndoField (I := I) (M := M) g gm y v, w] = _
    rw [unitModel_eq_ccTensorBilin_local]
  have hinv := sqrt_inner_gInvRaisedEndo_le
    (I := I) (M := M) g gm
    (ccTensorBilinSymm (I := I) g P) htie hδ_lt hδ hP y v
  calc
    _ = |ccTensorBilin (I := I) g W y
          (fullRaisedEndoField (I := I) (M := M) g gm y v) w| := by
      rw [hval]
    _ ≤ η * Real.sqrt (g.inner y
          (fullRaisedEndoField (I := I) (M := M) g gm y v)
          (fullRaisedEndoField (I := I) (M := M) g gm y v)) *
        Real.sqrt (g.inner y w w) := hW _ _ _
    _ ≤ η * ((1 / (1 - δ)) * Real.sqrt (g.inner y v v)) *
        Real.sqrt (g.inner y w w) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hinv hη) (Real.sqrt_nonneg _)
    _ = (η / (1 - δ)) * Real.sqrt (g.inner y v v) *
        Real.sqrt (g.inner y w w) := by ring
private def daTransMono
    (g gm : SmoothRiemannianMetric I M) (W : SmoothCcTensor g 0 2)
    (σ : Equiv.Perm (Fin 4)) : SmoothCcTensor g 4 2 :=
  curvatureRefoldMonomialCoeffField (I := I) (M := M) g g
    (ccTensorUnitValueSection (I := I) (M := M) g
      (daWeight (I := I) (M := M) g gm W))
    (ccTensorUnitValueSection_contMDiff (I := I) (M := M) g
      (daWeight (I := I) (M := M) g gm W)) σ
private theorem daMono_cap
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    (hT : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g T x u v =
        ccTensorBilin (I := I) g T x v u)
    {δ : ℝ} (hδ_lt : δ < 1) (hδ : 0 ≤ δ)
    (hTδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ)
    (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1)
    (σ : Equiv.Perm (Fin 4)) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g 4 2 x
        ((daTransMono (I := I) (M := M) g
          (realizedFam (I := I) g T 0 hTδ hδZ s) T σ).toSection x) ≤
      (deTurckArmFibreConst (Module.finrank ℝ E) *
        (δ / (1 - δ))) ^ 2 := by
  let gm := realizedFam (I := I) g T 0 hTδ hδZ s
  have hsmem : s ∈ realizedSmallSet (δ := δ) (δ' := δ) :=
    Icc_subset_realizedSmallSet hδ_lt hδ_lt hs
  have htie : ∀ (y : M) (v w : TangentSpace I y),
      gm.inner y v w =
        g.inner y v w +
          ccTensorBilinSymm (I := I) g
            (convexPerturbation (I := I) g T 0 s) y v w :=
    fun y v w => realizedFam_inner_of_mem
      (I := I) g T 0 hTδ hδZ hsmem y v w
  have hP : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (convexPerturbation (I := I) g T 0 s)) δ := by
    convert convexPerturbation_gFibreOpBound
      (I := I) (M := M) g T 0 hTδ hδZ hs.1 hs.2 using 1 <;> ring
  have hTcap : ∀ (y : M) (v w : TangentSpace I y),
      |ccTensorBilin (I := I) g T y v w| ≤
        δ * Real.sqrt (g.inner y v v) *
          Real.sqrt (g.inner y w w) := by
    intro y v w
    rw [show ccTensorBilin (I := I) g T y v w =
        ccTensorBilinSymm (I := I) g T y v w by
      rw [ccTensorBilinSymm_apply, ← hT y v w]
      ring]
    exact hTδ y v w
  have hratio : 0 ≤ δ / (1 - δ) :=
    div_nonneg hδ (by linarith)
  have hweight := daWeight_cap (I := I) (M := M)
    g gm (convexPerturbation (I := I) g T 0 s) T
    htie hδ_lt hδ hP hδ hTcap
  have hzero_app : ∀ (y : M) (v w : TangentSpace I y),
      ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2) y v w = 0 := by
    intro y v w
    have hzero : (0 : SmoothCcTensor g 0 2) =
        (0 : ℝ) • (0 : SmoothCcTensor g 0 2) :=
      (zero_smul ℝ _).symm
    rw [hzero, ccTensorBilinSymm_smul]
    ring
  have htie0 : ∀ (y : M) (v w : TangentSpace I y),
      g.inner y v w =
        g.inner y v w +
          ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2) y v w := by
    intro y v w
    rw [hzero_app, add_zero]
  have hzero_bound : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) 0 := by
    intro y v w
    rw [hzero_app]
    simp only [abs_zero, zero_mul, le_refl]
  rw [daTransMono, curvatureRefoldMonomialCoeffField_toSection]
  simpa only [gm, sub_zero, one_pow, div_one] using
    (rfns_curvatureRefoldMonomialBiContrFib_le
      (I := I) (M := M) g g (0 : SmoothCcTensor g 0 2)
      htie0 (δ := 0) (by norm_num)
      hzero_bound
      (ccTensorUnitValueSection (I := I) (M := M) g
        (daWeight (I := I) (M := M) g gm T))
      hratio hweight σ x)
private def daTrans
    (g gm : SmoothRiemannianMetric I M) (W : SmoothCcTensor g 0 2) :
    SmoothCcTensor g 4 2 :=
  daTransMono (I := I) (M := M) g gm W daPermA -
    daTransMono (I := I) (M := M) g gm W daPermB
private theorem daTrans_cap
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    (hT : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g T x u v =
        ccTensorBilin (I := I) g T x v u)
    {δ : ℝ} (hδ_lt : δ < 1) (hδ : 0 ≤ δ)
    (hTδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ)
    (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g 4 2 x
        ((daTrans (I := I) (M := M) g
          (realizedFam (I := I) g T 0 hTδ hδZ s) T).toSection x) ≤
      (2 * deTurckArmFibreConst (Module.finrank ℝ E) *
        (δ / (1 - δ))) ^ 2 := by
  simp only [daTrans, SmoothCcTensor.toSection_sub,
    ContMDiffSection.coe_sub, Pi.sub_apply]
  refine le_trans
    (riemannianFiberNormSq_sub_le (I := I) (M := M)
      g 4 2 x _ _) ?_
  have hA := daMono_cap (I := I) (M := M) g T hT
    hδ_lt hδ hTδ hδZ s hs daPermA x
  have hB := daMono_cap (I := I) (M := M) g T hT
    hδ_lt hδ hTδ hδZ s hs daPermB x
  nlinarith
private theorem fullSlot_cap
    (g : SmoothRiemannianMetric I M) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (gm : SmoothRiemannianMetric I M)
        (P : SmoothCcTensor g 0 2)
        {δ : ℝ}, δ ≤ 1 / 3 → 0 ≤ δ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g P) δ →
        (∀ (y : M) (v w : TangentSpace I y),
          gm.inner y v w =
            g.inner y v w + ccTensorBilinSymm (I := I) g P y v w) →
        ∀ x : M,
        riemannianFiberNormSq (I := I) (M := M) g 3 3 x
            ((slotInsertEndoCc (I := I) (M := M) g 2
              (fullRaisedEndoField (I := I) (M := M) g gm)).toSection x) ≤ K := by
  obtain ⟨C, hC_nn, hC⟩ :=
    rfns_iteratedCovGrad_slotInsertEndoCc_zero_gInvDiffRaisedEndoField_diagonalProductGrid_le
      (I := I) (M := M) g (δ₀ := (1 : ℝ) / 3) (by norm_num)
  obtain ⟨K0, hK0, hK0b⟩ :=
    exists_bound_riemannianFiberNormSq_smoothCcTensor
      (I := I) (M := M) g 3 3
      (slotInsertEndoCc (I := I) (M := M) g 2
        (fullRaisedEndoField (I := I) (M := M) g g))
  let n : ℝ := Module.finrank ℝ E
  let K := 2 * (n ^ 2 * C 0 + K0)
  refine ⟨K, by
    exact mul_nonneg (by norm_num)
      (add_nonneg
        (mul_nonneg (sq_nonneg n) (hC_nn 0)) hK0), ?_⟩
  intro gm P δ hδ_le hδ hP htie x
  have hD0 := hC gm P htie hδ_le hδ hP 0 x
  rw [show (∑ q ∈ Finset.range (0 + 1),
      ∑ e ∈ Finset.Nat.antidiagonalTuple q 0,
        ∏ m : Fin q,
          riemannianFiberNormSq (I := I) (M := M) g 0 (2 + e m) x
            ((iteratedCovGrad (I := I) g 0 2 (e m) P).toSection x)) =
      DifferentialGeometry.Combinatorics.antidiagonalTupleGrid
        (fun j => riemannianFiberNormSq (I := I) (M := M) g 0 (2 + j) x
          ((iteratedCovGrad (I := I) g 0 2 j P).toSection x)) 0 from rfl,
    DifferentialGeometry.Combinatorics.antidiagonalTupleGrid_zero,
    iteratedCovGrad_zero, mul_one] at hD0
  have hD2 := rfns_iteratedCovGrad_slotInsertEndoCc_le_endo
    (I := I) (M := M) g 2
    (gInvDiffRaisedEndoField (I := I) g gm) 0 x
  simp only [iteratedCovGrad_zero, Nat.reduceAdd] at hD2
  have hdiff :
      riemannianFiberNormSq (I := I) (M := M) g 3 3 x
          ((slotInsertEndoCc (I := I) (M := M) g 2
            (gInvDiffRaisedEndoField (I := I) g gm)).toSection x) ≤
        n ^ 2 * C 0 := by
    calc
      _ ≤ n ^ 2 * riemannianFiberNormSq (I := I) (M := M) g 1 1 x
          ((slotInsertEndoCc (I := I) (M := M) g 0
            (gInvDiffRaisedEndoField (I := I) g gm)).toSection x) := by
        simpa only [n] using hD2
      _ ≤ n ^ 2 * C 0 := by
        exact mul_le_mul_of_nonneg_left
          (by simpa only [Nat.add_zero] using hD0) (sq_nonneg n)
  have hfull :
      fullRaisedEndoField (I := I) (M := M) g gm =
        gInvDiffRaisedEndoField (I := I) g gm +
          fullRaisedEndoField (I := I) (M := M) g g := by
    apply ContMDiffSection.ext
    intro y
    apply ContinuousLinearMap.ext
    intro v
    change gInvRaisedEndo (I := I) g gm y v =
      gInvDiffRaisedEndo (I := I) g gm y v +
        gInvRaisedEndo (I := I) g g y v
    rw [show gInvRaisedEndo (I := I) g g y v = v by
      rw [gInvRaisedEndo_apply, inverseMetricSharpFib_g0FlatCLM]]
    exact gInvRaisedEndo_eq_diff_add_id (I := I) g gm y v
  rw [hfull, slotInsertEndoCc_add, SmoothCcTensor.toSection_add,
    ContMDiffSection.coe_add, Pi.add_apply]
  refine le_trans
    (riemannianFiberNormSq_add_le (I := I) (M := M)
      g 3 3 x _ _) ?_
  have hbase := hK0b x
  dsimp only [K]
  nlinarith
private theorem dagTop_cap
    (g : SmoothRiemannianMetric I M) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (gm : SmoothRiemannianMetric I M)
        (P : SmoothCcTensor g 0 2) {δ : ℝ},
        δ ≤ 1 / 3 → 0 ≤ δ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g P) δ →
        (∀ (y : M) (v w : TangentSpace I y),
          gm.inner y v w =
            g.inner y v w + ccTensorBilinSymm (I := I) g P y v w) →
        ∀ x : M,
        riemannianFiberNormSq (I := I) (M := M) g 4 4 x
          ((dagTopOp (I := I) (M := M) g gm).toSection x) ≤ K := by
  obtain ⟨KF, hKF, hFb⟩ := fullSlot_cap (I := I) (M := M) g
  obtain ⟨KK, hKK, hKb⟩ :=
    exists_bound_riemannianFiberNormSq_smoothCcTensor
      (I := I) (M := M) g 3 3 (koszulOp (I := I) (M := M) g)
  obtain ⟨KP3, hKP3, hP3b⟩ :=
    exists_bound_riemannianFiberNormSq_smoothCcTensor
      (I := I) (M := M) g 3 3
      (permCoeff (I := I) (M := M) g lowPerm)
  obtain ⟨KP4, hKP4, hP4b⟩ :=
    exists_bound_riemannianFiberNormSq_smoothCcTensor
      (I := I) (M := M) g 4 4
      (permCoeff (I := I) (M := M) g daPermA)
  let n : ℝ := Module.finrank ℝ E
  let K := KP4 * (n * (KP3 * (KF * KK)))
  refine ⟨K, mul_nonneg hKP4
    (mul_nonneg (Nat.cast_nonneg _)
      (mul_nonneg hKP3 (mul_nonneg hKF hKK))), ?_⟩
  intro gm P δ hδ_le hδ hP htie x
  have hfull := hFb gm P hδ_le hδ hP htie x
  have hinner := riemannianFiberNormSq_compRS_le_mul
    (I := I) (M := M) g 3 3 3 x
    ((slotInsertEndoCc (I := I) (M := M) g 2
      (fullRaisedEndoField (I := I) (M := M) g gm)).toSection x)
    ((koszulOp (I := I) (M := M) g).toSection x)
  rw [← appCcRS_toSection] at hinner
  have hinner' :
      riemannianFiberNormSq (I := I) (M := M) g 3 3 x
          ((appCcRS (I := I) (M := M) g 3 3 3
            (slotInsertEndoCc (I := I) (M := M) g 2
              (fullRaisedEndoField (I := I) (M := M) g gm))
            (koszulOp (I := I) (M := M) g)).toSection x) ≤ KF * KK :=
    hinner.trans (mul_le_mul (hfull) (hKb x)
      (riemannianFiberNormSq_nonneg (I := I) (M := M) g 3 3 x _)
      hKF)
  have hconn := riemannianFiberNormSq_compRS_le_mul
    (I := I) (M := M) g 3 3 3 x
    ((permCoeff (I := I) (M := M) g lowPerm).toSection x)
    ((appCcRS (I := I) (M := M) g 3 3 3
      (slotInsertEndoCc (I := I) (M := M) g 2
        (fullRaisedEndoField (I := I) (M := M) g gm))
      (koszulOp (I := I) (M := M) g)).toSection x)
  rw [← appCcRS_toSection] at hconn
  have hconn' := hconn.trans
    (mul_le_mul (hP3b x) hinner'
      (riemannianFiberNormSq_nonneg (I := I) (M := M) g 3 3 x _) hKP3)
  have hslot := rfns_slotExtend_eq (I := I) (M := M)
    g 3 3 (connLowOp (I := I) (M := M) g gm) x
  have hout := riemannianFiberNormSq_compRS_le_mul
    (I := I) (M := M) g 4 4 4 x
    ((permCoeff (I := I) (M := M) g daPermA).toSection x)
    ((slotExtend (I := I) (M := M) g 3 3
      (connLowOp (I := I) (M := M) g gm)).toSection x)
  rw [← appCcRS_toSection] at hout
  rw [hslot] at hout
  have hout' :
      riemannianFiberNormSq (I := I) (M := M) g 4 4 x
          ((dagTopOp (I := I) (M := M) g gm).toSection x) ≤
        riemannianFiberNormSq (I := I) (M := M) g 4 4 x
            ((permCoeff (I := I) (M := M) g daPermA).toSection x) *
          ((Module.finrank ℝ E : ℝ) *
            riemannianFiberNormSq (I := I) (M := M) g 3 3 x
              ((connLowOp (I := I) (M := M) g gm).toSection x)) := by
    simpa only [dagTopOp] using hout
  refine hout'.trans ?_
  dsimp only [K, n]
  exact mul_le_mul (hP4b x)
    (mul_le_mul_of_nonneg_left hconn' (Nat.cast_nonneg _))
    (mul_nonneg (Nat.cast_nonneg _)
      (riemannianFiberNormSq_nonneg (I := I) (M := M) g 3 3 x _)) hKP4

private theorem mono_trans
    (g : SmoothRiemannianMetric I M) (G : SmoothCcTensor g 0 4)
    (σ : Equiv.Perm (Fin 4)) (W : SmoothCcTensor g 0 2) :
    appCc (I := I) (M := M) g 2 2
        (refoldKernelContractionMonomialField
          (I := I) (M := M) g g G σ) W =
      appCc (I := I) (M := M) g 4 2
        (curvatureRefoldMonomialCoeffField (I := I) (M := M) g g
          (ccTensorUnitValueSection (I := I) (M := M) g W)
          (ccTensorUnitValueSection_contMDiff (I := I) (M := M) g W) σ) G := by
  classical
  refine smoothCcTensor_ext_of_unitModel (I := I) (M := M) g fun x => ?_
  rw [unitModel, unitModel]
  refine congrArg Tensor0SSpace.toModel ?_
  change
    (refoldKernelContractionMonomialBiContrFib (I := I) (M := M) g
      (ccTensorFourUnitValueSection (I := I) (M := M) g G) σ x)
      ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
        W.toSection x) (unitTensor (I := I) (M := M) x)) =
    (curvatureRefoldMonomialBiContrFib (I := I) (M := M) g
      (ccTensorUnitValueSection (I := I) (M := M) g W) σ x)
      ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 4 I x from
        G.toSection x) (unitTensor (I := I) (M := M) x))
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro v
  rw [refoldKernelContractionMonomialBiContrFib,
    refoldKernelContractionMonomialFibFixedFrame_toModel,
    curvatureRefoldMonomialBiContrFib,
    curvatureRefoldMonomialFibFixedFrame_toModel]
  rfl

private theorem daMono_trans
    (g gm : SmoothRiemannianMetric I M) (G : SmoothCcTensor g 0 4)
    (σ : Equiv.Perm (Fin 4)) (W : SmoothCcTensor g 0 2) :
    appCc (I := I) (M := M) g 2 2
        (daMono (I := I) (M := M) g gm G σ) W =
      appCc (I := I) (M := M) g 4 2
        (daTransMono (I := I) (M := M) g gm W σ) G := by
  rw [daMono, ← appCc_assoc]
  exact mono_trans (I := I) (M := M) g G σ
    (daWeight (I := I) (M := M) g gm W)

private theorem daContr_trans
    (g gm : SmoothRiemannianMetric I M) (G : SmoothCcTensor g 0 4)
    (W : SmoothCcTensor g 0 2) :
    appCc (I := I) (M := M) g 2 2
        (daContr (I := I) (M := M) g gm G) W =
      appCc (I := I) (M := M) g 4 2
        (daTrans (I := I) (M := M) g gm W) G := by
  rw [daContr, daTrans, appCc_sub_left, appCc_sub_left,
    daMono_trans, daMono_trans]

set_option maxHeartbeats 3200000 in
private theorem daMono_eval
    (g gm : SmoothRiemannianMetric I M) (G : SmoothCcTensor g 0 4)
    (σ : Equiv.Perm (Fin 4)) (W : SmoothCcTensor g 0 2)
    (x : M) (v : Fin 2 → E) :
    unitModel (I := I) (M := M) g 2
        (appCc (I := I) (M := M) g 2 2
          (daMono (I := I) (M := M) g gm G σ) W) x v =
      ∑ a : Fin (Module.finrank ℝ E),
        ∑ b : Fin (Module.finrank ℝ E),
          unitModel (I := I) (M := M) g 2 W x
              ![fullRaisedEndoField (I := I) (M := M) g gm x
                  (smoothOrthoFrame (I := I) g x a x),
                smoothOrthoFrame (I := I) g x b x] *
            unitModel (I := I) (M := M) g 4 G x
              (fun i =>
                (![smoothOrthoFrame (I := I) g x a x,
                    smoothOrthoFrame (I := I) g x b x,
                    (v 0 : TangentSpace I x), (v 1 : TangentSpace I x)] :
                    Fin 4 → TangentSpace I x) (σ i)) := by
  classical
  rw [daMono, ← appCc_assoc (I := I) (M := M) g 2 2 2]
  rw [unitModel, appCc_toSection, ContinuousLinearMap.comp_apply,
    refoldKernelContractionMonomialField_toSection]
  change Tensor0SSpace.toModel
      (refoldKernelContractionMonomialFibFixedFrame
        (I := I) (M := M)
        (ccTensorFourUnitValueSection (I := I) (M := M) g G) σ
        (smoothOrthoFrame (I := I) g x) x
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
          (appCc (I := I) (M := M) g 2 2
            (slotInsertEndoCc (I := I) (M := M) g 1
              (fullRaisedEndoField (I := I) (M := M) g gm)) W).toSection x)
          (unitTensor (I := I) (M := M) x))) v = _
  rw [refoldKernelContractionMonomialFibFixedFrame_toModel]
  refine Finset.sum_congr rfl fun a _ => ?_
  refine Finset.sum_congr rfl fun b _ => ?_
  congr 1
  rw [show Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
          (appCc (I := I) (M := M) g 2 2
            (slotInsertEndoCc (I := I) (M := M) g 1
              (fullRaisedEndoField (I := I) (M := M) g gm)) W).toSection x)
          (unitTensor (I := I) (M := M) x))
        ![smoothOrthoFrame (I := I) g x a x,
          smoothOrthoFrame (I := I) g x b x] =
      unitModel (I := I) (M := M) g 2
        (appCc (I := I) (M := M) g 2 2
          (slotInsertEndoCc (I := I) (M := M) g 1
            (fullRaisedEndoField (I := I) (M := M) g gm)) W) x
        ![smoothOrthoFrame (I := I) g x a x,
          smoothOrthoFrame (I := I) g x b x] from rfl]
  rw [unitModel, appCc_toSection, ContinuousLinearMap.comp_apply,
    slotInsertEndoCc_toSection, slotInsertEndoFib_apply_eval]
  have hv :
      Function.update
          ![smoothOrthoFrame (I := I) g x a x,
            smoothOrthoFrame (I := I) g x b x]
          0
          (fullRaisedEndoField (I := I) (M := M) g gm x
            (![smoothOrthoFrame (I := I) g x a x,
              smoothOrthoFrame (I := I) g x b x] 0)) =
        ![fullRaisedEndoField (I := I) (M := M) g gm x
            (smoothOrthoFrame (I := I) g x a x),
          smoothOrthoFrame (I := I) g x b x] := by
    funext i
    fin_cases i <;> simp
  rw [hv]
  rfl
  congr 1
  funext i
  congr 1
  funext j
  fin_cases j <;> rfl

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
    [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private theorem unit_sub
    (g : SmoothRiemannianMetric I M) (A B : SmoothCcTensor g 0 2)
    (x : M) (v : Fin 2 → E) :
    unitModel (I := I) (M := M) g 2 (A - B) x v =
      unitModel (I := I) (M := M) g 2 A x v -
        unitModel (I := I) (M := M) g 2 B x v := by
  have hfun : unitModel (I := I) (M := M) g 2 (A - B) x =
      unitModel (I := I) (M := M) g 2 A x -
        unitModel (I := I) (M := M) g 2 B x := by
    simp only [unitModel]
    rw [SmoothCcTensor.toSection_sub, ContMDiffSection.coe_sub, Pi.sub_apply,
      ContinuousLinearMap.sub_apply, Tensor0SSpace.toModel_sub]
  rw [hfun, ContinuousMultilinearMap.sub_apply]

set_option maxHeartbeats 3200000 in
private theorem ricciDA_action
    (g gm : SmoothRiemannianMetric I M) (W : SmoothCcTensor g 0 2)
    (hW : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g W x u v =
        ccTensorBilin (I := I) g W x v u) :
    appCc (I := I) (M := M) g 2 2
        (ricciDAArm (I := I) (M := M) g gm) W =
      appCc (I := I) (M := M) g 2 2
        (daContr (I := I) (M := M) g gm
          (ricciDAG (I := I) (M := M) g gm)) W := by
  classical
  refine smoothCcTensor_ext_of_unitModel (I := I) (M := M) g fun x => ?_
  refine ContinuousMultilinearMap.ext fun v => ?_
  rw [ricciDAOut_fin (I := I) (M := M) g gm W hW x v]
  simp only [daContr, appCc_sub_left]
  rw [unit_sub (I := I) (M := M) g]
  rw [daMono_eval (I := I) (M := M) g gm _ daPermA W x v,
    daMono_eval (I := I) (M := M) g gm _ daPermB W x v]
  nth_rewrite 1 [Finset.sum_comm]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun r _ => ?_
  have hA :
      (fun i =>
        (![smoothOrthoFrame (I := I) g x p x,
            smoothOrthoFrame (I := I) g x r x, v 0, v 1] :
          Fin 4 → E) (daPermA i)) =
        ![smoothOrthoFrame (I := I) g x r x, v 0, v 1,
          smoothOrthoFrame (I := I) g x p x] := by
    funext i
    fin_cases i <;> rfl
  have hB :
      (fun i =>
        (![smoothOrthoFrame (I := I) g x p x,
            smoothOrthoFrame (I := I) g x r x, v 0, v 1] :
          Fin 4 → E) (daPermB i)) =
        ![smoothOrthoFrame (I := I) g x r x,
          smoothOrthoFrame (I := I) g x p x, v 0, v 1] := by
    funext i
    fin_cases i <;> rfl
  rw [hA, hB]
  ring

private def ricciDALow
    (g gm : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2) :
    SmoothCcTensor g 2 2 :=
  daContr (I := I) (M := M) g gm
    (appCcRS (I := I) (M := M) g 0 3 4
      (dagLowOp (I := I) (M := M) g gm)
      (covGrad (I := I) (M := M) g 0 2 T))

private def ricciDATop
    (g gm : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2) :
    SmoothCcTensor g 4 2 :=
  appCcRS (I := I) (M := M) g 4 4 2
    (daTrans (I := I) (M := M) g gm T)
    (dagTopOp (I := I) (M := M) g gm)

private theorem ricciDA_refold
    (g gm : SmoothRiemannianMetric I M) (P W : SmoothCcTensor g 0 2)
    (hP : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g P x u v =
        ccTensorBilin (I := I) g P x v u)
    (hW : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g W x u v =
        ccTensorBilin (I := I) g W x v u)
    (htie : ∀ (x : M) (u v : TangentSpace I x),
      gm.inner x u v =
        g.inner x u v + ccTensorBilinSymm (I := I) g P x u v) :
    appCc (I := I) (M := M) g 2 2
        (ricciDAArm (I := I) (M := M) g gm) W =
      appCc (I := I) (M := M) g 2 2
          (ricciDALow (I := I) (M := M) g gm P) W +
        appCc (I := I) (M := M) g 4 2
          (ricciDATop (I := I) (M := M) g gm W)
          (iteratedCovGrad (I := I) g 0 2 2 P) := by
  rw [ricciDA_action (I := I) (M := M) g gm W hW]
  rw [daContr_trans]
  rw [ricciDAG_split (I := I) (M := M) g gm P hP htie]
  rw [appCc_add_right]
  rw [← daContr_trans]
  simp only [ricciDALow, ricciDATop]
  simp only [appCcRS_zero_eq_appCc]
  rw [← appCc_assoc]

private def ricciLow
    (g gm : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2) :
    SmoothCcTensor g 2 2 :=
  ricciAAArm (I := I) (M := M) g gm +
    ricciDALow (I := I) (M := M) g gm T

private def ricciTop
    (g gm : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2) :
    SmoothCcTensor g 4 2 :=
  ricciDATop (I := I) (M := M) g gm T

private theorem ricciTop_cap
    (g : SmoothRiemannianMetric I M) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (T : SmoothCcTensor g 0 2)
        (_hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        {δ : ℝ}, δ ≤ 1 / 3 → 0 ≤ δ →
        ∀ (hTδ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
          (hδZ : gFibreOpBound (I := I) (M := M) g
            (ccTensorBilinSymm (I := I) g
              (0 : SmoothCcTensor g 0 2)) δ)
          (s : ℝ), s ∈ Set.Icc (0 : ℝ) 1 → ∀ x : M,
        riemannianFiberNormSq (I := I) (M := M) g 4 2 x
            ((ricciTop (I := I) (M := M) g
              (realizedFam (I := I) g T 0 hTδ hδZ s) T).toSection x) ≤
          (K * (δ / (1 - δ))) ^ 2 := by
  obtain ⟨KD, hKD, hDb⟩ := dagTop_cap (I := I) (M := M) g
  let K := 2 * deTurckArmFibreConst (Module.finrank ℝ E) * (1 + KD)
  refine ⟨K, mul_nonneg
    (mul_nonneg (by norm_num)
      (by
        exact Real.sqrt_nonneg _ :
          0 ≤ deTurckArmFibreConst (Module.finrank ℝ E)))
    (by linarith), ?_⟩
  intro T hT δ hδ_le hδ hTδ hδZ s hs x
  let gm := realizedFam (I := I) g T 0 hTδ hδZ s
  let P := convexPerturbation (I := I) g T 0 s
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le (by norm_num)
  have hsmem : s ∈ realizedSmallSet (δ := δ) (δ' := δ) :=
    Icc_subset_realizedSmallSet hδ_lt hδ_lt hs
  have htie : ∀ (y : M) (v w : TangentSpace I y),
      gm.inner y v w =
        g.inner y v w + ccTensorBilinSymm (I := I) g P y v w :=
    fun y v w => realizedFam_inner_of_mem
      (I := I) g T 0 hTδ hδZ hsmem y v w
  have hP : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g P) δ := by
    convert convexPerturbation_gFibreOpBound
      (I := I) (M := M) g T 0 hTδ hδZ hs.1 hs.2 using 1 <;> ring
  have hA := daTrans_cap (I := I) (M := M) g T hT
    hδ_lt hδ hTδ hδZ s hs x
  have hD := hDb gm P hδ_le hδ hP htie x
  have hc := riemannianFiberNormSq_compRS_le_mul
    (I := I) (M := M) g 4 4 2 x
    ((daTrans (I := I) (M := M) g gm T).toSection x)
    ((dagTopOp (I := I) (M := M) g gm).toSection x)
  rw [← appCcRS_toSection] at hc
  have hprod := mul_le_mul hA hD
    (riemannianFiberNormSq_nonneg (I := I) (M := M) g 4 4 x _)
    (sq_nonneg (2 * deTurckArmFibreConst (Module.finrank ℝ E) *
      (δ / (1 - δ))))
  calc
    _ ≤ riemannianFiberNormSq (I := I) (M := M) g 4 2 x
        ((daTrans (I := I) (M := M) g gm T).toSection x) *
      riemannianFiberNormSq (I := I) (M := M) g 4 4 x
        ((dagTopOp (I := I) (M := M) g gm).toSection x) := by
      simpa only [ricciTop, ricciDATop, gm] using hc
    _ ≤ (2 * deTurckArmFibreConst (Module.finrank ℝ E) *
          (δ / (1 - δ))) ^ 2 * KD := hprod
    _ ≤ (2 * deTurckArmFibreConst (Module.finrank ℝ E) *
          (δ / (1 - δ))) ^ 2 * (1 + KD) ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
      nlinarith
    _ = (K * (δ / (1 - δ))) ^ 2 := by
      simp only [K]
      ring

private def ricciDanger
    (g gm : SmoothRiemannianMetric I M) (P : SmoothCcTensor g 0 2) :
    SmoothCcTensor g 2 2 :=
  daContr (I := I) (M := M) g gm
    (appCcRS (I := I) (M := M) g 0 4 4
      (dagTopOp (I := I) (M := M) g gm)
      (iteratedCovGrad (I := I) g 0 2 2 P))

private def ricciSafeLow
    (g gm : SmoothRiemannianMetric I M) (P : SmoothCcTensor g 0 2) :
    SmoothCcTensor g 2 2 :=
  ccInputSymm (I := I) (M := M) g
    (linearizedRicciConnDiffOrder0CoeffField
        (I := I) (M := M) g gm -
      ricciDanger (I := I) (M := M) g gm P)

private theorem ccInputSymm_app
    (g : SmoothRiemannianMetric I M) (C : SmoothCcTensor g 2 2)
    (W : SmoothCcTensor g 0 2)
    (hW : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g W x u v =
        ccTensorBilin (I := I) g W x v u) :
    appCc (I := I) (M := M) g 2 2
        (ccInputSymm (I := I) (M := M) g C) W =
      appCc (I := I) (M := M) g 2 2 C W := by
  have hswap :
      appCc (I := I) (M := M) g 2 2
          (ccSlotSwapField (I := I) (M := M) g) W = W := by
    refine smoothCcTensor_ext_of_unitModel (I := I) (M := M) g fun x => ?_
    refine ContinuousMultilinearMap.ext fun v => ?_
    rw [unitModel, appCc_toSection, ContinuousLinearMap.comp_apply,
      ccSlotSwapField_toSection]
    change Tensor0SSpace.toModel
        (slotSwapFib (I := I) (M := M) x
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
            W.toSection x) (unitTensor (I := I) (M := M) x))) v =
      unitModel (I := I) (M := M) g 2 W x v
    rw [slotSwapFib_apply,
      Tensor0SSpace.toModel_ofModel,
      ContinuousMultilinearMap.domDomCongr_apply]
    have hv :
        (fun i => v ((Equiv.swap (0 : Fin 2) 1) i)) = ![v 1, v 0] := by
      funext i
      fin_cases i <;> rfl
    have hv' : v = ![v 0, v 1] := by
      funext i
      fin_cases i <;> rfl
    rw [hv]
    conv_rhs => rw [hv']
    have hunit :
        Tensor0SSpace.toModel
            ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
              W.toSection x) (unitTensor (I := I) (M := M) x)) =
          unitModel (I := I) (M := M) g 2 W x := rfl
    rw [hunit,
      unitModel_eq_ccTensorBilin_local (I := I) (M := M) g W x,
      unitModel_eq_ccTensorBilin_local (I := I) (M := M) g W x]
    exact hW x (v 1) (v 0)
  rw [ccInputSymm, appCc_smul_left, appCc_add_left, ← appCc_assoc, hswap]
  module

private theorem ricciConn_refold
    (g gm : SmoothRiemannianMetric I M) (P W : SmoothCcTensor g 0 2)
    (hP : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g P x u v =
        ccTensorBilin (I := I) g P x v u)
    (hW : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g W x u v =
        ccTensorBilin (I := I) g W x v u)
    (htie : ∀ (x : M) (u v : TangentSpace I x),
      gm.inner x u v =
        g.inner x u v + ccTensorBilinSymm (I := I) g P x u v) :
    appCc (I := I) (M := M) g 2 2
        (linearizedRicciConnDiffOrder0CoeffField
          (I := I) (M := M) g gm) W =
      appCc (I := I) (M := M) g 2 2
          (ricciLow (I := I) (M := M) g gm P) W +
        appCc (I := I) (M := M) g 4 2
          (ricciTop (I := I) (M := M) g gm W)
          (iteratedCovGrad (I := I) g 0 2 2 P) := by
  rw [ricciCoeff_split, appCc_add_left]
  rw [ricciDA_refold (I := I) (M := M) g gm P W hP hW htie]
  simp only [ricciLow, ricciTop, appCc_add_left]
  module

private theorem safeLow_action
    (g gm : SmoothRiemannianMetric I M) (P W : SmoothCcTensor g 0 2)
    (hP : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g P x u v =
        ccTensorBilin (I := I) g P x v u)
    (hW : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g W x u v =
        ccTensorBilin (I := I) g W x v u)
    (htie : ∀ (x : M) (u v : TangentSpace I x),
      gm.inner x u v =
        g.inner x u v + ccTensorBilinSymm (I := I) g P x u v) :
    appCc (I := I) (M := M) g 2 2
        (ricciSafeLow (I := I) (M := M) g gm P) W =
      appCc (I := I) (M := M) g 2 2
        (ricciLow (I := I) (M := M) g gm P) W := by
  rw [ricciSafeLow, ccInputSymm_app (I := I) (M := M) g _ W hW,
    appCc_sub_left]
  have hconn := ricciConn_refold (I := I) (M := M)
    g gm P W hP hW htie
  have htop :
      appCc (I := I) (M := M) g 2 2
          (ricciDanger (I := I) (M := M) g gm P) W =
        appCc (I := I) (M := M) g 4 2
          (ricciTop (I := I) (M := M) g gm W)
          (iteratedCovGrad (I := I) g 0 2 2 P) := by
    rw [ricciDanger, daContr_trans, appCcRS_zero_eq_appCc, appCc_assoc]
    rfl
  rw [htop, hconn]
  module

private theorem ccSwap_app
    (g : SmoothRiemannianMetric I M) (W : SmoothCcTensor g 0 2) :
    appCc (I := I) (M := M) g 2 2
        (ccSlotSwapField (I := I) (M := M) g) W =
      domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 2) 1) W := by
  refine smoothCcTensor_ext_of_unitModel (I := I) (M := M) g fun x => ?_
  rw [domDomCongrSection_unitModel]
  refine ContinuousMultilinearMap.ext fun v => ?_
  rw [unitModel, appCc_toSection, ContinuousLinearMap.comp_apply,
    ccSlotSwapField_toSection]
  change Tensor0SSpace.toModel
      (slotSwapFib (I := I) (M := M) x
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
          W.toSection x) (unitTensor (I := I) (M := M) x))) v =
    (ContinuousMultilinearMap.domDomCongr
      (Equiv.swap (0 : Fin 2) 1)
      (unitModel (I := I) (M := M) g 2 W x)) v
  rw [slotSwapFib_apply, Tensor0SSpace.toModel_ofModel,
    ContinuousMultilinearMap.domDomCongr_apply]
  rfl

private theorem ccInputSymm_action
    (g : SmoothRiemannianMetric I M) (C : SmoothCcTensor g 2 2)
    (W : SmoothCcTensor g 0 2) :
    appCc (I := I) (M := M) g 2 2
        (ccInputSymm (I := I) (M := M) g C) W =
      appCc (I := I) (M := M) g 2 2 C
        (symmS (I := I) (M := M) g W) := by
  rw [ccInputSymm, appCc_smul_left, appCc_add_left, ← appCc_assoc,
    ccSwap_app (I := I) (M := M) g W]
  rw [symmS, appCc_smul_right, appCc_add_right]

private theorem cc22_ext
    (g : SmoothRiemannianMetric I M) (C D : SmoothCcTensor g 2 2)
    (h : ∀ W : SmoothCcTensor g 0 2,
      appCc (I := I) (M := M) g 2 2 C W =
        appCc (I := I) (M := M) g 2 2 D W) :
    C = D := by
  classical
  refine SmoothCcTensor.ext ?_
  refine ContMDiffSection.ext fun x => ?_
  refine tensorRSSpace_ext 2 2 x fun u => ?_
  let V : TensorRSSpace 0 2 I x :=
    (show TensorRSSpace 0 2 I x from
      ((MixedSection.eval₀ (F := E)
        (E := (TangentSpace I : M → Type _)) x).smulRight u))
  obtain ⟨σW, hσW⟩ := ContMDiffSection.exists_eq_at
    (I := I) (n := (⊤ : ℕ∞)) (F := TensorRSModel 0 2 ℝ E)
    (V := fun z : M => TensorRSSpace 0 2 I z) x V
  let W₀ : SmoothCcTensor g 0 2 :=
    { toSection := σW
      hasCompactSupport := HasCompactSupport.of_compactSpace _ }
  have h1 : (appCc (I := I) (M := M) g 2 2 C W₀).toSection x =
      (appCc (I := I) (M := M) g 2 2 D W₀).toSection x := by
    rw [h W₀]
  have h2 : (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        C.toSection x)
      ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
        W₀.toSection x) (unitTensor (I := I) (M := M) x)) =
    (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        D.toSection x)
      ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
        W₀.toSection x) (unitTensor (I := I) (M := M) x)) := by
    exact congrArg
      (fun Z : TensorRSSpace 0 2 I x =>
        (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from Z)
          (unitTensor (I := I) (M := M) x)) h1
  have hWval :
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
        W₀.toSection x) (unitTensor (I := I) (M := M) x) = u := by
    rw [show W₀.toSection x = V from hσW]
    change ((MixedSection.eval₀ (F := E)
        (E := (TangentSpace I : M → Type _)) x).smulRight u)
      (ContinuousMultilinearMap.constOfIsEmpty ℝ
        (fun _ : Fin 0 => TangentSpace I x) 1) = u
    rw [ContinuousLinearMap.smulRight_apply, MixedSection.eval₀_apply,
      ContinuousMultilinearMap.constOfIsEmpty_apply, one_smul]
  rwa [hWval] at h2

private def ricciGoodLow
    (g gm : SmoothRiemannianMetric I M) (P : SmoothCcTensor g 0 2) :
    SmoothCcTensor g 2 2 :=
  ccInputSymm (I := I) (M := M) g
    (ricciLow (I := I) (M := M) g gm P)

private theorem ricciGood_eq_safe
    (g gm : SmoothRiemannianMetric I M) (P : SmoothCcTensor g 0 2)
    (hP : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g P x u v =
        ccTensorBilin (I := I) g P x v u)
    (htie : ∀ (x : M) (u v : TangentSpace I x),
      gm.inner x u v =
        g.inner x u v + ccTensorBilinSymm (I := I) g P x u v) :
    ricciGoodLow (I := I) (M := M) g gm P =
      ricciSafeLow (I := I) (M := M) g gm P := by
  apply cc22_ext (I := I) (M := M) g
  intro W
  rw [ricciGoodLow, ccInputSymm_action]
  rw [ricciSafeLow, ccInputSymm_action]
  let SW := symmS (I := I) (M := M) g W
  have hSW : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g SW x u v =
        ccTensorBilin (I := I) g SW x v u := by
    intro x u v
    simp only [SW, ccTensorBilin_symmS, ccTensorBilinSymm_apply]
    ring
  have hs := safeLow_action (I := I) (M := M)
    g gm P SW hP hSW htie
  rw [ricciSafeLow,
    ccInputSymm_app (I := I) (M := M) g _ SW hSW] at hs
  exact hs.symm

/-! ## Jointly smooth coefficient families -/

private abbrev JointRS
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (S : Set ℝ)
    (A : ℝ → SmoothCcTensor g r s) : Prop :=
  ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
    (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
    (fun p : M × ℝ => TotalSpace.mk' (TensorRSModel r s ℝ E)
      (E := fun x : M => TensorRSSpace r s I x) p.1
      ((A p.2).toSection p.1))
    ((Set.univ : Set M) ×ˢ S)

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
    [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private theorem joint_const
    (g : SmoothRiemannianMetric I M) {r s : ℕ} {S : Set ℝ}
    (A : SmoothCcTensor g r s) :
    JointRS (I := I) g r s S (fun _ => A) := by
  exact (A.toSection.contMDiff.comp_contMDiffOn contMDiffOn_fst).mono
    (Set.subset_univ _)

private theorem joint_app
    (g : SmoothRiemannianMetric I M) {a b c : ℕ} {S : Set ℝ}
    (A : ℝ → SmoothCcTensor g b c) (B : ℝ → SmoothCcTensor g a b)
    (hA : JointRS (I := I) g b c S A)
    (hB : JointRS (I := I) g a b S B) :
    JointRS (I := I) g a c S
      (fun t => appCcRS (I := I) (M := M) g a b c (A t) (B t)) := by
  apply contMDiffOn_clm_section_of_pointwise_jointMR (I := I) (M := M)
    (F₁ := Tensor0SModel a ℝ E) (V₁ := fun x : M => Tensor0SSpace a I x)
    (F₂ := Tensor0SModel c ℝ E) (V₂ := fun x : M => Tensor0SSpace c I x)
    (φ := fun p : M × ℝ =>
      (show Tensor0SSpace a I p.1 →L[ℝ] Tensor0SSpace c I p.1 from
        (appCcRS (I := I) (M := M) g a b c
          (A p.2) (B p.2)).toSection p.1))
    (S := S)
  intro Y
  have hY : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, Tensor0SModel a ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SModel a ℝ E)
        (E := fun x : M => Tensor0SSpace a I x) p.1 (Y p.1))
      ((Set.univ : Set M) ×ˢ S) :=
    Y.contMDiff.comp_contMDiffOn contMDiffOn_fst
  have hBY := ContMDiffOn.clm_bundle_apply (b := Prod.fst) hB hY
  have hABY := ContMDiffOn.clm_bundle_apply (b := Prod.fst) hA hBY
  refine hABY.congr (fun p _ => ?_)
  refine congrArg (fun z => TotalSpace.mk' (Tensor0SModel c ℝ E)
    (E := fun x : M => Tensor0SSpace c I x) p.1 z) ?_
  rw [appCcRS_toSection]
  rfl

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
    [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private theorem joint_param_smul
    (g : SmoothRiemannianMetric I M) {r s : ℕ} {S : Set ℝ}
    (A : ℝ → SmoothCcTensor g r s)
    (hA : JointRS (I := I) g r s S A) :
    JointRS (I := I) g r s S (fun t => t • A t) := by
  letI := tensorRSBundle_topology (𝕜 := ℝ) (E := E) (H := H)
    (I := I) (M := M) r s
  intro p hp
  rw [Bundle.contMDiffWithinAt_totalSpace]
  refine ⟨contMDiffWithinAt_fst, ?_⟩
  set x := p.1 with hx
  set e := trivializationAt (TensorRSModel r s ℝ E)
    (fun z : M => TensorRSSpace r s I z) x with he
  have hA' := (Bundle.contMDiffWithinAt_totalSpace
    (F := TensorRSModel r s ℝ E)
    (E := fun z : M => TensorRSSpace r s I z)).mp (hA p hp)
  refine (contMDiffWithinAt_snd.smul hA'.2).congr_of_eventuallyEq ?_ ?_
  · have hbase : ∀ᶠ q : M × ℝ in
        nhdsWithin p ((Set.univ : Set M) ×ˢ S), q.1 ∈ e.baseSet :=
      (continuousWithinAt_fst
        (s := (Set.univ : Set M) ×ˢ S) (p := p))
        (e.open_baseSet.mem_nhds (by
          rw [he]
          exact mem_baseSet_trivializationAt _ _ x))
    filter_upwards [hbase] with q hq
    exact (e.linear ℝ hq).map_smul q.2 ((A q.2).toSection q.1)
  · exact (e.linear ℝ (by
      rw [he, ← hx]
      exact mem_baseSet_trivializationAt _ _ x)).map_smul
        p.2 ((A p.2).toSection p.1)

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
    [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
open DifferentialGeometry.Integral.DivergenceTheorem in
private theorem joint_curry {d : ℕ} {S : Set ℝ}
    (A : ∀ p : M × ℝ, Tensor0SSpace (d + 1) I p.1)
    (hA : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, Tensor0SModel (d + 1) ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SModel (d + 1) ℝ E)
        (E := fun z : M => Tensor0SSpace (d + 1) I z) p.1 (A p))
      ((Set.univ : Set M) ×ˢ S)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, E →L[ℝ] Tensor0SModel d ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (E →L[ℝ] Tensor0SModel d ℝ E)
        (E := fun z : M => TangentSpace I z →L[ℝ] Tensor0SSpace d I z) p.1
        (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) d p.1 (A p)))
      ((Set.univ : Set M) ×ˢ S) := by
  letI := tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H)
    (I := I) (M := M) (d + 1)
  intro p₀ hp₀
  rw [Bundle.contMDiffWithinAt_totalSpace]
  refine ⟨contMDiffWithinAt_fst, ?_⟩
  set x₀ := p₀.1 with hx₀
  have hA' := (Bundle.contMDiffWithinAt_totalSpace
    (F := Tensor0SModel (d + 1) ℝ E)
    (E := fun z : M => Tensor0SSpace (d + 1) I z)).mp (hA p₀ hp₀)
  have hcurry : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ))
      𝓘(ℝ, E →L[ℝ] Tensor0SModel d ℝ E) ∞
      (fun p : M × ℝ =>
        continuousMultilinearCurryLeftEquiv ℝ
          (fun _ : Fin (d + 1) => E) ℝ
          ((trivializationAt (Tensor0SModel (d + 1) ℝ E)
            (fun z : M => Tensor0SSpace (d + 1) I z) x₀
            ⟨p.1, A p⟩).2))
      ((Set.univ : Set M) ×ˢ S) p₀ := by
    have hop : ContMDiff 𝓘(ℝ, Tensor0SModel (d + 1) ℝ E)
        𝓘(ℝ, E →L[ℝ] Tensor0SModel d ℝ E) ∞
        (fun U : Tensor0SModel (d + 1) ℝ E =>
          continuousMultilinearCurryLeftEquiv ℝ
            (fun _ : Fin (d + 1) => E) ℝ U) :=
      ((continuousMultilinearCurryLeftEquiv ℝ
        (fun _ : Fin (d + 1) => E) ℝ
        ).toContinuousLinearEquiv.toContinuousLinearMap).contMDiff
    exact hop.contMDiffAt.comp_contMDiffWithinAt p₀ hA'.2
  refine hcurry.congr_of_eventuallyEq ?_ ?_
  · have hbase : ∀ᶠ p : M × ℝ in
        nhdsWithin p₀ ((Set.univ : Set M) ×ˢ S),
        p.1 ∈ (trivializationAt (Tensor0SModel d ℝ E)
          (fun z : M => Tensor0SSpace d I z) x₀).baseSet :=
      (continuousWithinAt_fst
        (s := (Set.univ : Set M) ×ˢ S) (p := p₀))
        ((trivializationAt (Tensor0SModel d ℝ E)
          (fun z : M => Tensor0SSpace d I z) x₀).open_baseSet.mem_nhds
          (mem_baseSet_trivializationAt _ _ x₀))
    filter_upwards [hbase] with p hx
    have hc :=
      TensorMultilinear.trivializationAt_homBundle_curriedSection_eq
        (I := I) (M := M) (fun z : M => A ⟨z, p.2⟩) x₀ p.1 hx
    rw [TensorMultilinear.curriedSection] at hc
    exact hc
  · have hx0 : p₀.1 ∈
        (trivializationAt (Tensor0SModel d ℝ E)
          (fun z : M => Tensor0SSpace d I z) x₀).baseSet := by
      rw [← hx₀]
      exact mem_baseSet_trivializationAt _ _ x₀
    have hc :=
      TensorMultilinear.trivializationAt_homBundle_curriedSection_eq
        (I := I) (M := M) (fun z : M => A ⟨z, p₀.2⟩) x₀ p₀.1 hx0
    rw [TensorMultilinear.curriedSection] at hc
    exact hc

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
    [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
open DifferentialGeometry.Integral.DivergenceTheorem in
private theorem joint_uncurry {d : ℕ} {S : Set ℝ}
    (G : ∀ p : M × ℝ,
      TangentSpace I p.1 →L[ℝ] Tensor0SSpace d I p.1)
    (hG : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, E →L[ℝ] Tensor0SModel d ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (E →L[ℝ] Tensor0SModel d ℝ E)
        (E := fun z : M => TangentSpace I z →L[ℝ] Tensor0SSpace d I z)
        p.1 (G p))
      ((Set.univ : Set M) ×ˢ S)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, Tensor0SModel (d + 1) ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SModel (d + 1) ℝ E)
        (E := fun z : M => Tensor0SSpace (d + 1) I z) p.1
        ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) d p.1).symm
          (G p)))
      ((Set.univ : Set M) ×ˢ S) := by
  letI := tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H)
    (I := I) (M := M) (d + 1)
  intro p₀ hp₀
  rw [Bundle.contMDiffWithinAt_totalSpace]
  refine ⟨contMDiffWithinAt_fst, ?_⟩
  set x₀ := p₀.1 with hx₀
  have hG' := (Bundle.contMDiffWithinAt_totalSpace
    (F := E →L[ℝ] Tensor0SModel d ℝ E)
    (E := fun z : M =>
      TangentSpace I z →L[ℝ] Tensor0SSpace d I z)).mp (hG p₀ hp₀)
  have huncurry : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ))
      𝓘(ℝ, Tensor0SModel (d + 1) ℝ E) ∞
      (fun p : M × ℝ =>
        (continuousMultilinearCurryLeftEquiv ℝ
          (fun _ : Fin (d + 1) => E) ℝ).symm
          ((trivializationAt (E →L[ℝ] Tensor0SModel d ℝ E)
            (fun z : M =>
              TangentSpace I z →L[ℝ] Tensor0SSpace d I z) x₀
            ⟨p.1, G p⟩).2))
      ((Set.univ : Set M) ×ˢ S) p₀ := by
    have hop : ContMDiff 𝓘(ℝ, E →L[ℝ] Tensor0SModel d ℝ E)
        𝓘(ℝ, Tensor0SModel (d + 1) ℝ E) ∞
        (fun U : E →L[ℝ] Tensor0SModel d ℝ E =>
          (continuousMultilinearCurryLeftEquiv ℝ
            (fun _ : Fin (d + 1) => E) ℝ).symm U) :=
      ((continuousMultilinearCurryLeftEquiv ℝ
        (fun _ : Fin (d + 1) => E) ℝ
        ).toContinuousLinearEquiv.symm.toContinuousLinearMap).contMDiff
    exact hop.contMDiffAt.comp_contMDiffWithinAt p₀ hG'.2
  have hpt : ∀ p : M × ℝ,
      p.1 ∈ (trivializationAt (Tensor0SModel d ℝ E)
          (fun y : M => Tensor0SSpace d I y) x₀).baseSet →
      (trivializationAt (Tensor0SModel (d + 1) ℝ E)
          (fun y : M => Tensor0SSpace (d + 1) I y) x₀
          ⟨p.1, (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ)
            d p.1).symm (G p)⟩).2 =
        (continuousMultilinearCurryLeftEquiv ℝ
          (fun _ : Fin (d + 1) => E) ℝ).symm
          ((trivializationAt (E →L[ℝ] Tensor0SModel d ℝ E)
            (fun y : M =>
              TangentSpace I y →L[ℝ] Tensor0SSpace d I y) x₀
            ⟨p.1, G p⟩).2) := by
    intro p hz
    have hUcurry :
        TensorMultilinear.curriedSection (I := I) (M := M)
          (fun y : M =>
            (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ)
              d y).symm (G ⟨y, p.2⟩)) p.1 = G p := by
      rw [TensorMultilinear.curriedSection]
      exact ContinuousLinearEquiv.apply_symm_apply _ _
    have hfwd :=
      TensorMultilinear.trivializationAt_homBundle_curriedSection_eq
        (I := I) (M := M)
        (fun y : M =>
          (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ)
            d y).symm (G ⟨y, p.2⟩)) x₀ p.1 hz
    rw [hUcurry] at hfwd
    rw [show (fun y : M =>
        (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ)
          d y).symm (G ⟨y, p.2⟩)) p.1 =
        (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ)
          d p.1).symm (G p) from rfl] at hfwd
    rw [hfwd]
    exact (LinearIsometryEquiv.symm_apply_apply
      (continuousMultilinearCurryLeftEquiv ℝ
        (fun _ : Fin (d + 1) => E) ℝ) _).symm
  refine huncurry.congr_of_eventuallyEq ?_ ?_
  · have hbase : ∀ᶠ p : M × ℝ in
        nhdsWithin p₀ ((Set.univ : Set M) ×ˢ S),
        p.1 ∈ (trivializationAt (Tensor0SModel d ℝ E)
          (fun z : M => Tensor0SSpace d I z) x₀).baseSet :=
      (continuousWithinAt_fst
        (s := (Set.univ : Set M) ×ˢ S) (p := p₀))
        ((trivializationAt (Tensor0SModel d ℝ E)
          (fun z : M => Tensor0SSpace d I z) x₀).open_baseSet.mem_nhds
          (mem_baseSet_trivializationAt _ _ x₀))
    filter_upwards [hbase] with p hx
    exact hpt p hx
  · have hx0 : p₀.1 ∈
        (trivializationAt (Tensor0SModel d ℝ E)
          (fun z : M => Tensor0SSpace d I z) x₀).baseSet := by
      rw [← hx₀]
      exact mem_baseSet_trivializationAt _ _ x₀
    apply hpt
    exact hx0

private theorem slotExtend_joint
    (g : SmoothRiemannianMetric I M) {r s : ℕ} {S : Set ℝ}
    (A : ℝ → SmoothCcTensor g r s)
    (hA : JointRS (I := I) g r s S A) :
    JointRS (I := I) g (r + 1) (s + 1) S
      (fun t => slotExtend (I := I) (M := M) g r s (A t)) := by
  apply contMDiffOn_clm_section_of_pointwise_jointMR (I := I) (M := M)
    (F₁ := Tensor0SModel (r + 1) ℝ E)
    (V₁ := fun x : M => Tensor0SSpace (r + 1) I x)
    (F₂ := Tensor0SModel (s + 1) ℝ E)
    (V₂ := fun x : M => Tensor0SSpace (s + 1) I x)
    (φ := fun p : M × ℝ =>
      (slotExtend (I := I) (M := M) g r s (A p.2)).toSection p.1)
    (S := S)
  intro Y
  have hY : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, Tensor0SModel (r + 1) ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk'
        (Tensor0SModel (r + 1) ℝ E)
        (E := fun x : M => Tensor0SSpace (r + 1) I x)
        p.1 (Y p.1))
      ((Set.univ : Set M) ×ˢ S) :=
    Y.contMDiff.comp_contMDiffOn contMDiffOn_fst
  have hcur := joint_curry (I := I) (M := M) (d := r) (S := S)
    (fun p : M × ℝ => Y p.1) hY
  have hcomp : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, E →L[ℝ] Tensor0SModel s ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk'
        (E →L[ℝ] Tensor0SModel s ℝ E)
        (E := fun x : M =>
          TangentSpace I x →L[ℝ] Tensor0SSpace s I x) p.1
        (((A p.2).toSection p.1).comp
          ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ)
            r p.1) (Y p.1))))
      ((Set.univ : Set M) ×ˢ S) := by
    apply contMDiffOn_clm_section_of_pointwise_jointMR (I := I) (M := M)
      (F₁ := E) (V₁ := fun x : M => TangentSpace I x)
      (F₂ := Tensor0SModel s ℝ E)
      (V₂ := fun x : M => Tensor0SSpace s I x)
      (φ := fun p : M × ℝ =>
        ((A p.2).toSection p.1).comp
          ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ)
            r p.1) (Y p.1)))
      (S := S)
    intro Z
    have hZ : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
        (I.prod 𝓘(ℝ, E)) ∞
        (fun p : M × ℝ => TotalSpace.mk' E
          (E := fun x : M => TangentSpace I x) p.1 (Z p.1))
        ((Set.univ : Set M) ×ˢ S) :=
      Z.contMDiff.comp_contMDiffOn contMDiffOn_fst
    have hcurZ := ContMDiffOn.clm_bundle_apply
      (b := Prod.fst) hcur hZ
    have hAZ := ContMDiffOn.clm_bundle_apply
      (b := Prod.fst) hA hcurZ
    refine hAZ.congr (fun p _ => ?_)
    rfl
  have hout := joint_uncurry (I := I) (M := M)
    (d := s) (S := S)
    (fun p : M × ℝ =>
      (((A p.2).toSection p.1).comp
        ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ)
          r p.1) (Y p.1)))) hcomp
  refine hout.congr (fun p _ => ?_)
  refine congrArg (fun z => TotalSpace.mk'
    (Tensor0SModel (s + 1) ℝ E)
    (E := fun x : M => Tensor0SSpace (s + 1) I x) p.1 z) ?_
  rw [slotExtend_toSection, slotExtendFib_apply]

private def lift0
    (g : SmoothRiemannianMetric I M) {s : ℕ}
    (Y : Cₛ^∞⟮I; Tensor0SModel s ℝ E,
      (fun x : M => Tensor0SSpace s I x)⟯) :
    SmoothCcTensor g 0 s where
  toSection :=
    MixedSection.fromMultilinearSection
      (𝕜 := ℝ) (F := E) (IB := I)
      (E := (TangentSpace I : M → Type _)) ∞ Y
  hasCompactSupport := HasCompactSupport.of_compactSpace _

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private theorem lift0_unit
    (g : SmoothRiemannianMetric I M) {s : ℕ}
    (Y : Cₛ^∞⟮I; Tensor0SModel s ℝ E,
      (fun x : M => Tensor0SSpace s I x)⟯) (x : M) :
    (lift0 (I := I) (M := M) g Y).toSection x
        (unitZeroSec (I := I) (M := M) x) = Y x := by
  change
    (MixedSection.fromMultilinearSection
      (𝕜 := ℝ) (F := E) (IB := I)
      (E := (TangentSpace I : M → Type _)) ∞ Y) x
        (unitZeroSec (I := I) (M := M) x) = Y x
  have h := congrArg (fun Z =>
    Z x) (MixedSection.toMultilinearSection_fromMultilinearSection
      (𝕜 := ℝ) (F := E) (IB := I)
      (E := (TangentSpace I : M → Type _)) ∞ Y)
  simpa only [MixedSection.toMultilinearSection,
    unitZeroSec_apply, Tensor0SSpace.ofModel] using h

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
private theorem joint_eval0
    (g : SmoothRiemannianMetric I M) {s : ℕ} {S : Set ℝ}
    (A : ℝ → SmoothCcTensor g 0 s)
    (hA : JointRS (I := I) g 0 s S A) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, Tensor0SModel s ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SModel s ℝ E)
        (E := fun x : M => Tensor0SSpace s I x) p.1
        ((A p.2).toSection p.1
          (unitZeroSec (I := I) (M := M) p.1)))
      ((Set.univ : Set M) ×ˢ S) := by
  have hu : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, Tensor0SModel 0 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SModel 0 ℝ E)
        (E := fun x : M => Tensor0SSpace 0 I x) p.1
        (unitZeroSec (I := I) (M := M) p.1))
      ((Set.univ : Set M) ×ˢ S) :=
    (unitZeroSec (I := I) (M := M)).contMDiff.comp_contMDiffOn
      contMDiffOn_fst
  exact ContMDiffOn.clm_bundle_apply (b := Prod.fst) hA hu

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
    [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private theorem arm_const
    (g : SmoothRiemannianMetric I M) {r : ℕ}
    (A : SmoothCcTensor g r 2) {δ δ' : ℝ} :
    linearizedRicciThreeArmHjoint (I := I) (M := M) g r
      (fun _ => A) (δ := δ) (δ' := δ') := by
  exact joint_const (I := I) (M := M)
    (S := realizedSmallSet (δ := δ) (δ' := δ')) g A

private theorem arm_comp
    (g : SmoothRiemannianMetric I M) (a b : ℕ)
    (A : ℝ → SmoothCcTensor g b 2) (B : SmoothCcTensor g a b)
    {δ δ' : ℝ}
    (hA : linearizedRicciThreeArmHjoint (I := I) (M := M) g b A
      (δ := δ) (δ' := δ')) :
    linearizedRicciThreeArmHjoint (I := I) (M := M) g a
      (fun t => appCcRS (I := I) (M := M) g a b 2 (A t) B)
      (δ := δ) (δ' := δ') := by
  have hA' : JointRS (I := I) g b 2
      (realizedSmallSet (δ := δ) (δ' := δ')) A := hA
  have hB := joint_const (I := I) (M := M)
    (S := realizedSmallSet (δ := δ) (δ' := δ')) g B
  exact joint_app (I := I) (M := M)
    (a := a) (b := b) (c := 2) g A (fun _ => B) hA' hB

private theorem fullRaised_joint
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    {δ : ℝ}
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x) p.1
        (fullRaisedEndoField (I := I) (M := M) g
          (realizedFam (I := I) g T 0 hδ hδZ p.2) p.1))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ)) := by
  apply contMDiffOn_clm_section_of_pointwise_jointMR (I := I) (M := M)
    (F₁ := E) (V₁ := fun x : M => TangentSpace I x)
    (F₂ := E) (V₂ := fun x : M => TangentSpace I x)
    (φ := fun p : M × ℝ =>
      fullRaisedEndoField (I := I) (M := M) g
        (realizedFam (I := I) g T 0 hδ hδZ p.2) p.1)
    (S := realizedSmallSet (δ := δ) (δ' := δ))
  intro Y
  have hY : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' E
        (E := fun x : M => TangentSpace I x) p.1 (Y p.1))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ)) :=
    Y.contMDiff.comp_contMDiffOn contMDiffOn_fst
  have hflat : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, E →L[ℝ] Tensor0SModel 1 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (E →L[ℝ] Tensor0SModel 1 ℝ E)
        (E := fun x : M => TangentSpace I x →L[ℝ] Tensor0SSpace 1 I x) p.1
        (g0FlatCLM (I := I) g p.1))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ)) :=
    (g0FlatField_contMDiff (I := I) g).comp_contMDiffOn contMDiffOn_fst
  have hflatY := ContMDiffOn.clm_bundle_apply
    (b := Prod.fst) hflat hY
  have hsharp :=
    inverseMetricSharpField_realizedFam_jointContMDiffOn
      (I := I) (M := M) g T 0 hδ hδZ
  have hout := ContMDiffOn.clm_bundle_apply
    (b := Prod.fst) hsharp hflatY
  refine hout.congr (fun p _ => ?_)
  rfl

private theorem slotInsert_joint
    (g : SmoothRiemannianMetric I M) (d : ℕ)
    (T : SmoothCcTensor g 0 2) {δ : ℝ}
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ) :
    JointRS (I := I) g (d + 1) (d + 1)
      (realizedSmallSet (δ := δ) (δ' := δ))
      (fun t => slotInsertEndoCc (I := I) (M := M) g d
        (fullRaisedEndoField (I := I) (M := M) g
          (realizedFam (I := I) g T 0 hδ hδZ t))) := by
  apply contMDiffOn_clm_section_of_pointwise_jointMR (I := I) (M := M)
    (F₁ := Tensor0SModel (d + 1) ℝ E)
    (V₁ := fun x : M => Tensor0SSpace (d + 1) I x)
    (F₂ := Tensor0SModel (d + 1) ℝ E)
    (V₂ := fun x : M => Tensor0SSpace (d + 1) I x)
    (φ := fun p : M × ℝ =>
      (show Tensor0SSpace (d + 1) I p.1 →L[ℝ]
          Tensor0SSpace (d + 1) I p.1 from
        (slotInsertEndoCc (I := I) (M := M) g d
          (fullRaisedEndoField (I := I) (M := M) g
            (realizedFam (I := I) g T 0 hδ hδZ p.2))).toSection p.1))
    (S := realizedSmallSet (δ := δ) (δ' := δ))
  intro Y
  have hY : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, Tensor0SModel (d + 1) ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SModel (d + 1) ℝ E)
        (E := fun x : M => Tensor0SSpace (d + 1) I x) p.1 (Y p.1))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ)) :=
    Y.contMDiff.comp_contMDiffOn contMDiffOn_fst
  have hout := slotInsertEndo0Field_apply_jointContMDiffOn
    (I := I) (M := M) (d := d)
    (fun p : M × ℝ => fullRaisedEndoField (I := I) (M := M) g
      (realizedFam (I := I) g T 0 hδ hδZ p.2) p.1)
    (fullRaised_joint (I := I) (M := M) g T hδ hδZ)
    (fun p : M × ℝ => Y p.1) hY
  refine hout.congr (fun p _ => ?_)
  refine congrArg (fun z => TotalSpace.mk' (Tensor0SModel (d + 1) ℝ E)
    (E := fun x : M => Tensor0SSpace (d + 1) I x) p.1 z) ?_
  rw [slotInsertEndoCc_toSection]

private theorem connLow_joint
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    {δ : ℝ}
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ) :
    JointRS (I := I) g 3 3
      (realizedSmallSet (δ := δ) (δ' := δ))
      (fun t => connLowOp (I := I) (M := M) g
        (realizedFam (I := I) g T 0 hδ hδZ t)) := by
  have hi := slotInsert_joint (I := I) (M := M) g 2 T hδ hδZ
  have hk := joint_const (I := I) (M := M) (S :=
    realizedSmallSet (δ := δ) (δ' := δ))
    g (koszulOp (I := I) (M := M) g)
  have hinner := joint_app (I := I) (M := M) g _ _ hi hk
  have hp := joint_const (I := I) (M := M) (S :=
    realizedSmallSet (δ := δ) (δ' := δ))
    g (permCoeff (I := I) (M := M) g lowPerm)
  have hout := joint_app (I := I) (M := M) g _ _ hp hinner
  simpa only [connLowOp] using hout

private theorem dagTop_joint
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    {δ : ℝ}
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ) :
    JointRS (I := I) g 4 4
      (realizedSmallSet (δ := δ) (δ' := δ))
      (fun t => dagTopOp (I := I) (M := M) g
        (realizedFam (I := I) g T 0 hδ hδZ t)) := by
  have hc := connLow_joint (I := I) (M := M) g T hδ hδZ
  have hs := slotExtend_joint (I := I) (M := M) g _ hc
  have hp := joint_const (I := I) (M := M) (S :=
    realizedSmallSet (δ := δ) (δ' := δ))
    g (permCoeff (I := I) (M := M) g daPermA)
  have hout := joint_app (I := I) (M := M) g _ _ hp hs
  simpa only [dagTopOp] using hout

private theorem daMono_joint
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    {δ : ℝ}
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ)
    (G : SmoothCcTensor g 0 4) (σ : Equiv.Perm (Fin 4)) :
    linearizedRicciThreeArmHjoint (I := I) (M := M) g 2
      (fun t => daMono (I := I) (M := M) g
        (realizedFam (I := I) g T 0 hδ hδZ t) G σ)
      (δ := δ) (δ' := δ) := by
  have hk := joint_const (I := I) (M := M) (S :=
    realizedSmallSet (δ := δ) (δ' := δ))
    g (refoldKernelContractionMonomialField
      (I := I) (M := M) g g G σ)
  have hi := slotInsert_joint (I := I) (M := M) g 1 T hδ hδZ
  have hout := joint_app (I := I) (M := M) g _ _ hk hi
  simpa only [linearizedRicciThreeArmHjoint, daMono] using hout

private theorem daContr_joint
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    {δ : ℝ}
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ)
    (G : SmoothCcTensor g 0 4) :
    linearizedRicciThreeArmHjoint (I := I) (M := M) g 2
      (fun t => daContr (I := I) (M := M) g
        (realizedFam (I := I) g T 0 hδ hδZ t) G)
      (δ := δ) (δ' := δ) := by
  have hA := daMono_joint (I := I) (M := M)
    g T hδ hδZ G daPermA
  have hB := daMono_joint (I := I) (M := M)
    g T hδ hδZ G daPermB
  simpa only [daContr] using
    threeArmJoint_sub (I := I) (M := M) g _ _ hA hB

private theorem daTrans_joint
    (g : SmoothRiemannianMetric I M) (T W : SmoothCcTensor g 0 2)
    {δ : ℝ}
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ) :
    linearizedRicciThreeArmHjoint (I := I) (M := M) g 4
      (fun t => daTrans (I := I) (M := M) g
        (realizedFam (I := I) g T 0 hδ hδZ t) W)
      (δ := δ) (δ' := δ) := by
  rw [linearizedRicciThreeArmHjoint]
  apply contMDiffOn_clm_section_of_pointwise_jointMR (I := I) (M := M)
    (F₁ := Tensor0SModel 4 ℝ E)
    (V₁ := fun x : M => Tensor0SSpace 4 I x)
    (F₂ := Tensor0SModel 2 ℝ E)
    (V₂ := fun x : M => Tensor0SSpace 2 I x)
    (φ := fun p : M × ℝ =>
      (daTrans (I := I) (M := M) g
        (realizedFam (I := I) g T 0 hδ hδZ p.2) W).toSection p.1)
    (S := realizedSmallSet (δ := δ) (δ' := δ))
  intro G
  let Gc : SmoothCcTensor g 0 4 :=
    lift0 (I := I) (M := M) g G
  have hc := daContr_joint (I := I) (M := M)
    g T hδ hδZ Gc
  have hc' : JointRS (I := I) g 2 2
      (realizedSmallSet (δ := δ) (δ' := δ))
      (fun t => daContr (I := I) (M := M) g
        (realizedFam (I := I) g T 0 hδ hδZ t) Gc) := hc
  have hW := joint_const (I := I) (M := M) (S :=
    realizedSmallSet (δ := δ) (δ' := δ)) g W
  have hout := joint_app (I := I) (M := M)
    (a := 0) (b := 2) (c := 2) g _ _ hc' hW
  have heval := joint_eval0 (I := I) (M := M) g _ hout
  refine heval.congr (fun p _ => ?_)
  refine congrArg (fun z => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
    (E := fun x : M => Tensor0SSpace 2 I x) p.1 z) ?_
  have h := congrArg (fun Z : SmoothCcTensor g 0 2 => Z.toSection p.1)
    (daContr_trans (I := I) (M := M) g
      (realizedFam (I := I) g T 0 hδ hδZ p.2)
      Gc W)
  have hunit := congrArg
    (fun L : Tensor0SSpace 0 I p.1 →L[ℝ] Tensor0SSpace 2 I p.1 =>
      L (unitZeroSec (I := I) (M := M) p.1)) h
  simp only [appCc_toSection, ContinuousLinearMap.comp_apply] at hunit
  rw [show Gc.toSection p.1
      (unitZeroSec (I := I) (M := M) p.1) = G p.1 by
    exact lift0_unit (I := I) (M := M) g G p.1] at hunit
  simpa only [appCcRS_zero_eq_appCc, appCc_toSection,
    ContinuousLinearMap.comp_apply] using hunit.symm

private theorem ricciTop_joint
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    {δ : ℝ}
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ) :
    linearizedRicciThreeArmHjoint (I := I) (M := M) g 4
      (fun t => ricciTop (I := I) (M := M) g
        (realizedFam (I := I) g T 0 hδ hδZ t) T)
      (δ := δ) (δ' := δ) := by
  have hA := daTrans_joint (I := I) (M := M)
    g T T hδ hδZ
  have hB := dagTop_joint (I := I) (M := M)
    g T hδ hδZ
  have hA' : JointRS (I := I) g 4 2
      (realizedSmallSet (δ := δ) (δ' := δ))
      (fun t => daTrans (I := I) (M := M) g
        (realizedFam (I := I) g T 0 hδ hδZ t) T) := hA
  rw [linearizedRicciThreeArmHjoint]
  have hout := joint_app (I := I) (M := M)
    (a := 4) (b := 4) (c := 2) g _ _ hA' hB
  simpa only [ricciTop, ricciDATop] using hout

private theorem danger_joint
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    {δ : ℝ}
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ) :
    linearizedRicciThreeArmHjoint (I := I) (M := M) g 2
      (fun t => ricciDanger (I := I) (M := M) g
        (realizedFam (I := I) g T 0 hδ hδZ t) (t • T))
      (δ := δ) (δ' := δ) := by
  rw [linearizedRicciThreeArmHjoint]
  apply contMDiffOn_clm_section_of_pointwise_jointMR (I := I) (M := M)
    (F₁ := Tensor0SModel 2 ℝ E)
    (V₁ := fun x : M => Tensor0SSpace 2 I x)
    (F₂ := Tensor0SModel 2 ℝ E)
    (V₂ := fun x : M => Tensor0SSpace 2 I x)
    (φ := fun p : M × ℝ =>
      (ricciDanger (I := I) (M := M) g
        (realizedFam (I := I) g T 0 hδ hδZ p.2)
        (p.2 • T)).toSection p.1)
    (S := realizedSmallSet (δ := δ) (δ' := δ))
  intro W
  let Wc : SmoothCcTensor g 0 2 :=
    lift0 (I := I) (M := M) g W
  have hTop := daTrans_joint (I := I) (M := M)
    g T Wc hδ hδZ
  have hTop' : JointRS (I := I) g 4 2
      (realizedSmallSet (δ := δ) (δ' := δ))
      (fun t => daTrans (I := I) (M := M) g
        (realizedFam (I := I) g T 0 hδ hδZ t) Wc) := hTop
  have hDag := dagTop_joint (I := I) (M := M)
    g T hδ hδZ
  have hD2 := joint_const (I := I) (M := M) (S :=
    realizedSmallSet (δ := δ) (δ' := δ)) g
    (iteratedCovGrad (I := I) g 0 2 2 T)
  have hsD2 := joint_param_smul (I := I) (M := M) g _ hD2
  have hG := joint_app (I := I) (M := M) g _ _ hDag hsD2
  have hout := joint_app (I := I) (M := M)
    (a := 0) (b := 4) (c := 2) g _ _ hTop' hG
  have heval := joint_eval0 (I := I) (M := M) g _ hout
  refine heval.congr (fun p _ => ?_)
  refine congrArg (fun z => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
    (E := fun x : M => Tensor0SSpace 2 I x) p.1 z) ?_
  have h := congrArg (fun Z : SmoothCcTensor g 0 2 => Z.toSection p.1)
    (daContr_trans (I := I) (M := M) g
      (realizedFam (I := I) g T 0 hδ hδZ p.2)
      (appCcRS (I := I) (M := M) g 0 4 4
        (dagTopOp (I := I) (M := M) g
          (realizedFam (I := I) g T 0 hδ hδZ p.2))
        (iteratedCovGrad (I := I) g 0 2 2 (p.2 • T)))
      Wc)
  have hunit := congrArg
    (fun L : Tensor0SSpace 0 I p.1 →L[ℝ] Tensor0SSpace 2 I p.1 =>
      L (unitZeroSec (I := I) (M := M) p.1)) h
  simp only [appCc_toSection, ContinuousLinearMap.comp_apply] at hunit
  rw [show Wc.toSection p.1
      (unitZeroSec (I := I) (M := M) p.1) = W p.1 by
    exact lift0_unit (I := I) (M := M) g W p.1] at hunit
  simpa only [ricciDanger, iteratedCovGrad_smul,
    appCcRS_zero_eq_appCc, appCc_toSection,
    ContinuousLinearMap.comp_apply] using hunit

private theorem inputSymm_joint
    (g : SmoothRiemannianMetric I M) {δ : ℝ}
    (C : ℝ → SmoothCcTensor g 2 2)
    (hC : linearizedRicciThreeArmHjoint (I := I) (M := M) g 2 C
      (δ := δ) (δ' := δ)) :
    linearizedRicciThreeArmHjoint (I := I) (M := M) g 2
      (fun t => ccInputSymm (I := I) (M := M) g (C t))
      (δ := δ) (δ' := δ) := by
  have hswap := joint_app (I := I) (M := M) g C
    (fun _ => ccSlotSwapField (I := I) (M := M) g) hC
    (joint_const (I := I) (M := M) (S :=
      realizedSmallSet (δ := δ) (δ' := δ)) g
      (ccSlotSwapField (I := I) (M := M) g))
  change linearizedRicciThreeArmHjoint (I := I) (M := M) g 2
    (fun t => appCcRS (I := I) (M := M) g 2 2 2
      (C t) (ccSlotSwapField (I := I) (M := M) g))
      (δ := δ) (δ' := δ) at hswap
  have hadd := threeArmJoint_add (I := I) (M := M) g _ _ hC hswap
  simpa only [ccInputSymm] using
    threeArmJoint_smul (I := I) (M := M) g (1 / 2 : ℝ) _ hadd

private theorem safeLow_joint
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    {δ : ℝ}
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ) :
    linearizedRicciThreeArmHjoint (I := I) (M := M) g 2
      (fun t => ricciSafeLow (I := I) (M := M) g
        (realizedFam (I := I) g T 0 hδ hδZ t) (t • T))
      (δ := δ) (δ' := δ) := by
  have hraw :=
    linearizedRicciConnDiffOrder0Coeff_threeArmHjoint
      (I := I) (M := M) g T 0 hδ hδZ
  have hdanger := danger_joint (I := I) (M := M)
    g T hδ hδZ
  have hsub := threeArmJoint_sub (I := I) (M := M)
    g _ _ hraw hdanger
  simpa only [ricciSafeLow] using
    inputSymm_joint (I := I) (M := M) g _ hsub

private theorem half_joint
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    {δ : ℝ}
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ) :
    linearizedRicciThreeArmHjoint (I := I) (M := M) g 2
      (fun t => edgeRicciHalf (I := I) (M := M) g
        (realizedFam (I := I) g T 0 hδ hδZ t))
      (δ := δ) (δ' := δ) := by
  have hconn :=
    linearizedRicciConnDiffOrder0Coeff_threeArmHjoint
      (I := I) (M := M) g T 0 hδ hδZ
  have hriem : linearizedRicciThreeArmHjoint
      (I := I) (M := M) g 2
      (fun t => ricciArmOrder0RiemannCoeff
        (I := I) (M := M) g
        (realizedFam (I := I) g T 0 hδ hδZ t))
      (δ := δ) (δ' := δ) := by
    rw [linearizedRicciThreeArmHjoint]
    exact ricciArmOrder0RiemannCoeff_realizedFam_jointContMDiff
      (I := I) (M := M) g T 0 hδ hδZ
  have hsum := threeArmJoint_add (I := I) (M := M) g _ _
    hconn (threeArmJoint_smul (I := I) (M := M)
      g (1 / 2 : ℝ) _ hriem)
  simpa only [edgeRicciHalf,
    linearizedRicciConnDiffOrder0Coeff] using hsum

private theorem refoldLow_joint
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    {δ : ℝ}
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ) :
    linearizedRicciThreeArmHjoint (I := I) (M := M) g 2
      (fun t => ricciRefold0 (I := I) (M := M) g
        (realizedFam (I := I) g T 0 hδ hδZ t) (t • T))
      (δ := δ) (δ' := δ) := by
  have hriem := arm_const (I := I) (M := M) g
    (ricciArmOrder0RiemannCoeff (I := I) (M := M) g g)
    (δ := δ) (δ' := δ)
  have hAA :=
    ricciArmOrder0AACommCoeffField_realizedFam_threeArmHjoint
      (I := I) (M := M) g T hδ hδZ
  have hBg :=
    ricciArmOrder0BgRCommCoeffField_realizedFam_threeArmHjoint
      (I := I) (M := M) g T hδ hδZ
  have hBg0 := arm_const (I := I) (M := M) g
    (ricciArmOrder0BgRCommCoeffField (I := I) (M := M) g g)
    (δ := δ) (δ' := δ)
  have hBgDiff := threeArmJoint_sub (I := I) (M := M)
    g _ _ hBg hBg0
  have hSwap := arm_comp (I := I) (M := M) g 2 2 _
    (ccSlotSwapField (I := I) (M := M) g) hBgDiff
  have hSharp :=
    ricciArmSharpGradKoszulResidualField_realizedFam_threeArmHjoint
      (I := I) (M := M) g T hδ hδZ
  have hFold :=
    ricciArmRicciFoldRemainderField_realizedFam_threeArmHjoint
      (I := I) (M := M) g T hδ hδZ
  have htail := threeArmJoint_sub (I := I) (M := M) g _ _
    (threeArmJoint_add (I := I) (M := M) g _ _ hSwap
      (threeArmJoint_smul (I := I) (M := M)
        g (1 / 2 : ℝ) _ hSharp))
    hFold
  have hinner := threeArmJoint_add (I := I) (M := M)
    g _ _ hAA htail
  have hall := threeArmJoint_add (I := I) (M := M) g _ _ hriem
    (threeArmJoint_smul (I := I) (M := M) g (2 : ℝ) _ hinner)
  simpa only [ricciRefold0] using hall

/-! ## The complete zero-arm self-action refold -/

private def rhsSelfLow
    (g g_bg : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    {δ : ℝ}
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ)
    (s : ℝ) : SmoothCcTensor g 2 2 :=
  let gm := realizedFam (I := I) g T 0 hδ hδZ s
  (-2 : ℝ) • ricciSafeLow (I := I) (M := M) g gm (s • T) +
    deTurckLieCoeffField (I := I) (M := M) g gm g_bg +
    lieCorr0Field (I := I) (M := M) g gm g_bg -
    edgeLiePairFam (I := I) (M := M) g T hδ hδZ
      lieRefoldQ lieRefoldEps s

private theorem rhsSelf_good
    (g g_bg : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
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
    rhsSelfLow (I := I) (M := M) g g_bg T hδ hδZ s =
      let gm := realizedFam (I := I) g T 0 hδ hδZ s
      (-2 : ℝ) • ricciGoodLow (I := I) (M := M) g gm (s • T) +
        deTurckLieCoeffField (I := I) (M := M) g gm g_bg +
        lieCorr0Field (I := I) (M := M) g gm g_bg -
        edgeLiePairFam (I := I) (M := M) g T hδ hδZ
          lieRefoldQ lieRefoldEps s := by
  let P : SmoothCcTensor g 0 2 := s • T
  let gm : SmoothRiemannianMetric I M :=
    realizedFam (I := I) g T 0 hδ hδZ s
  have hs_mem : s ∈ realizedSmallSet (δ := δ) (δ' := δ) :=
    Icc_subset_realizedSmallSet hδ_lt hδ_lt hs
  have htie : ∀ (x : M) (u v : TangentSpace I x),
      gm.inner x u v =
        g.inner x u v + ccTensorBilinSymm (I := I) g P x u v := by
    intro x u v
    rw [← show convexPerturbation (I := I) g T 0 s = P by
      simp only [P, convexPerturbation, smul_zero, zero_add]]
    exact realizedFam_inner_of_mem
      (I := I) g T 0 hδ hδZ hs_mem x u v
  have hP : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g P x u v =
        ccTensorBilin (I := I) g P x v u := by
    intro x u v
    simp only [P, ccTensorBilin_apply, ccTensorModel_smul,
      ContinuousMultilinearMap.smul_apply, smul_eq_mul]
    apply congrArg (fun z : ℝ => s * z)
    simpa only [ccTensorBilin_apply] using hT x u v
  have hgood := ricciGood_eq_safe (I := I) (M := M) g gm P hP htie
  simp only [rhsSelfLow]
  rw [← hgood]

private def rhsSelfTop
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    {δ : ℝ}
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ)
    (s : ℝ) : SmoothCcTensor g 4 2 :=
  let gm := realizedFam (I := I) g T 0 hδ hδZ s
  (-2 * s : ℝ) • ricciTop (I := I) (M := M) g gm T +
    (-1 : ℝ) • ricciRefold2 (I := I) (M := M) g T hδ hδZ s

private theorem topKernel_eq
    (g g_bg : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    {δ : ℝ}
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ)
    (s : ℝ) :
    let gm := realizedFam (I := I) g T 0 hδ hδZ s
    rhsRefoldTop (I := I) (M := M) g g_bg T hδ hδZ s +
          rhsSelfTop (I := I) (M := M) g T hδ hδZ s -
          deTurckPhiMetTotal (I := I) (M := M) g g_bg g =
      lieRefold2 (I := I) (M := M) g T hδ hδZ s +
        (deTurckPhiMetTotal (I := I) (M := M) g g_bg gm -
          deTurckPhiMetTotal (I := I) (M := M) g g_bg g) +
        (-2 * s : ℝ) • ricciTop (I := I) (M := M) g gm T := by
  simp only [rhsRefoldTop, rhsRefold2, rhsSelfTop]
  module

private theorem lieLow_decomp
    (g gm g_bg : SmoothRiemannianMetric I M)
    (Q : SmoothCcTensor g 2 2) :
    deTurckLieCoeffField (I := I) (M := M) g gm g_bg +
          lieCorr0Field (I := I) (M := M) g gm g_bg - Q =
      (deTurckLieCovDerivArmField (I := I) (M := M) g gm g_bg - Q) +
        (deTurckLieEndoArmField (I := I) (M := M) g gm g_bg -
          deTurckLieEndoArmField (I := I) (M := M) g gm g) +
        ((((lc0Insert (I := I) (M := M) g gm g_bg -
              lc0Insert (I := I) (M := M) g gm g) +
            lc0VB (I := I) (M := M) g gm) +
          lc0AMix (I := I) (M := M) g gm g_bg) +
        lc0Riem (I := I) (M := M) g gm) := by
  rw [deTurckLieCoeffField_eq_covDerivArm_add_endoArm]
  rw [← tail_base_split (I := I) (M := M) g gm g_bg]
  abel

private theorem selfLow_decomp
    (g g_bg : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    {δ : ℝ}
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ)
    (s : ℝ) :
    rhsSelfLow (I := I) (M := M) g g_bg T hδ hδZ s =
      let gm := realizedFam (I := I) g T 0 hδ hδZ s
      (-2 : ℝ) • ricciSafeLow (I := I) (M := M) g gm (s • T) +
        ((deTurckLieCovDerivArmField (I := I) (M := M) g gm g_bg -
            edgeLiePairFam (I := I) (M := M) g T hδ hδZ
              lieRefoldQ lieRefoldEps s) +
          (deTurckLieEndoArmField (I := I) (M := M) g gm g_bg -
            deTurckLieEndoArmField (I := I) (M := M) g gm g) +
          ((((lc0Insert (I := I) (M := M) g gm g_bg -
                lc0Insert (I := I) (M := M) g gm g) +
              lc0VB (I := I) (M := M) g gm) +
            lc0AMix (I := I) (M := M) g gm g_bg) +
          lc0Riem (I := I) (M := M) g gm)) := by
  simp only [rhsSelfLow]
  let gm := realizedFam (I := I) g T 0 hδ hδZ s
  let Q := edgeLiePairFam (I := I) (M := M) g T hδ hδZ
    lieRefoldQ lieRefoldEps s
  have hlie := lieLow_decomp (I := I) (M := M) g gm g_bg Q
  calc
    _ = (-2 : ℝ) • ricciSafeLow (I := I) (M := M) g gm (s • T) +
        (deTurckLieCoeffField (I := I) (M := M) g gm g_bg +
          lieCorr0Field (I := I) (M := M) g gm g_bg - Q) := by
      simp only [gm, Q]
      abel
    _ = (-2 : ℝ) • ricciSafeLow (I := I) (M := M) g gm (s • T) +
        ((deTurckLieCovDerivArmField (I := I) (M := M) g gm g_bg - Q) +
          (deTurckLieEndoArmField (I := I) (M := M) g gm g_bg -
            deTurckLieEndoArmField (I := I) (M := M) g gm g) +
          ((((lc0Insert (I := I) (M := M) g gm g_bg -
                lc0Insert (I := I) (M := M) g gm g) +
              lc0VB (I := I) (M := M) g gm) +
            lc0AMix (I := I) (M := M) g gm g_bg) +
          lc0Riem (I := I) (M := M) g gm)) := by
      rw [hlie]

private def oldRicci
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    {δ : ℝ}
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ)
    (s : ℝ) : SmoothCcTensor g 2 2 :=
  let gm := realizedFam (I := I) g T 0 hδ hδZ s
  (-2 : ℝ) • edgeRicciHalf (I := I) (M := M) g gm +
    ricciRefold0 (I := I) (M := M) g gm (s • T)

private theorem selfLow_eq
    (g g_bg : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    {δ : ℝ}
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ)
    (s : ℝ) :
    rhsSelfLow (I := I) (M := M) g g_bg T hδ hδZ s =
      (-2 : ℝ) • ricciSafeLow (I := I) (M := M) g
          (realizedFam (I := I) g T 0 hδ hδZ s) (s • T) +
        (rhsRefold0 (I := I) (M := M) g g_bg T hδ hδZ s -
          oldRicci (I := I) (M := M) g T hδ hδZ s) := by
  simp only [rhsSelfLow, oldRicci, rhsRefold0, lieRefold0]
  rw [deTurckLieCoeffField_eq_covDerivArm_add_endoArm]
  module

private theorem oldRicci_joint
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    {δ : ℝ}
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ) :
    linearizedRicciThreeArmHjoint (I := I) (M := M) g 2
      (oldRicci (I := I) (M := M) g T hδ hδZ)
      (δ := δ) (δ' := δ) := by
  have hh := half_joint (I := I) (M := M) g T hδ hδZ
  have hscaled := threeArmJoint_smul (I := I) (M := M)
    g (-2 : ℝ) _ hh
  have hrefold := refoldLow_joint (I := I) (M := M)
    g T hδ hδZ
  simpa only [oldRicci] using
    threeArmJoint_add (I := I) (M := M)
      g _ _ hscaled hrefold

private theorem selfLow_joint
    (g g_bg : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    {δ : ℝ}
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ) :
    linearizedRicciThreeArmHjoint (I := I) (M := M) g 2
      (rhsSelfLow (I := I) (M := M) g g_bg T hδ hδZ)
      (δ := δ) (δ' := δ) := by
  have hsafe := safeLow_joint (I := I) (M := M)
    g T hδ hδZ
  have hsafe' := threeArmJoint_smul (I := I) (M := M)
    g (-2 : ℝ) _ hsafe
  have hfull := rhsRefold0_joint (I := I) (M := M)
    g g_bg T hδ hδZ
  have hold := oldRicci_joint (I := I) (M := M)
    g T hδ hδZ
  have htail := threeArmJoint_sub (I := I) (M := M)
    g _ _ hfull hold
  have hall := threeArmJoint_add (I := I) (M := M)
    g _ _ hsafe' htail
  convert hall using 1
  funext s
  exact selfLow_eq (I := I) (M := M)
    g g_bg T hδ hδZ s

private theorem selfTop_joint
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    {δ : ℝ}
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ) :
    linearizedRicciThreeArmHjoint (I := I) (M := M) g 4
      (rhsSelfTop (I := I) (M := M) g T hδ hδZ)
      (δ := δ) (δ' := δ) := by
  have htop := ricciTop_joint (I := I) (M := M)
    g T hδ hδZ
  have htop' : JointRS (I := I) g 4 2
      (realizedSmallSet (δ := δ) (δ' := δ))
      (fun s => ricciTop (I := I) (M := M) g
        (realizedFam (I := I) g T 0 hδ hδZ s) T) := htop
  have hparam := joint_param_smul (I := I) (M := M)
    g _ htop'
  change linearizedRicciThreeArmHjoint (I := I) (M := M) g 4
    (fun s => s • ricciTop (I := I) (M := M) g
      (realizedFam (I := I) g T 0 hδ hδZ s) T)
      (δ := δ) (δ' := δ) at hparam
  have htopScaled := threeArmJoint_smul (I := I) (M := M)
    g (-2 : ℝ) _ hparam
  have hpal :=
    riemannPalatiniRefoldC2Family_threeArmHjoint
      (I := I) (M := M) g T hδ hδZ ricciRefoldQA ricciRefoldQB
  have hrefold := threeArmJoint_smul (I := I) (M := M)
    g (2 : ℝ) _ hpal
  have hrefold' : linearizedRicciThreeArmHjoint
      (I := I) (M := M) g 4
      (fun s => ricciRefold2 (I := I) (M := M)
        g T hδ hδZ s) (δ := δ) (δ' := δ) := by
    simpa only [ricciRefold2] using hrefold
  have hneg := threeArmJoint_smul (I := I) (M := M)
    g (-1 : ℝ) _ hrefold'
  have hall := threeArmJoint_add (I := I) (M := M)
    g _ _ htopScaled hneg
  simpa only [rhsSelfTop, smul_smul] using hall

private theorem rhsSelf_refold
    (g g_bg : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
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
    appCc (I := I) (M := M) g 2 2
        (rhsRefold0 (I := I) (M := M) g g_bg T hδ hδZ s) T =
      appCc (I := I) (M := M) g 2 2
          (rhsSelfLow (I := I) (M := M) g g_bg T hδ hδZ s) T +
        appCc (I := I) (M := M) g 4 2
          (rhsSelfTop (I := I) (M := M) g T hδ hδZ s)
          (iteratedCovGrad (I := I) g 0 2 2 T) := by
  let P : SmoothCcTensor g 0 2 := s • T
  let gm : SmoothRiemannianMetric I M :=
    realizedFam (I := I) g T 0 hδ hδZ s
  have hs_mem : s ∈ realizedSmallSet (δ := δ) (δ' := δ) :=
    Icc_subset_realizedSmallSet hδ_lt hδ_lt hs
  have htie : ∀ (x : M) (u v : TangentSpace I x),
      gm.inner x u v =
        g.inner x u v + ccTensorBilinSymm (I := I) g P x u v := by
    intro x u v
    rw [← show convexPerturbation (I := I) g T 0 s = P by
      simp only [P, convexPerturbation, smul_zero, zero_add]]
    exact realizedFam_inner_of_mem
      (I := I) g T 0 hδ hδZ hs_mem x u v
  have hP : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g P x u v =
        ccTensorBilin (I := I) g P x v u := by
    intro x u v
    simp only [P, ccTensorBilin_apply, ccTensorModel_smul,
      ContinuousMultilinearMap.smul_apply, smul_eq_mul]
    apply congrArg (fun z : ℝ => s * z)
    simpa only [ccTensorBilin_apply] using hT x u v
  have hconn := ricciConn_refold (I := I) (M := M)
    g gm P T hP hT htie
  have hsafe := safeLow_action (I := I) (M := M)
    g gm P T hP hT htie
  have hkernel :=
    appCc_refoldKernelContractionField (I := I) (M := M) g gm
      (iteratedCovGrad (I := I) g 0 2 2 P)
      (Equiv.swap (0 : Fin 4) 2) (Equiv.swap (1 : Fin 4) 3)
      (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3) 1 T
  have hsymm : symmS (I := I) (M := M) g T = T :=
    symm_eq_self (I := I) (M := M) g T hT
  have hpal :
      ricciRefold2 (I := I) (M := M) g T hδ hδZ s =
        (2 * s : ℝ) •
          curvatureRefoldKernelCoeffField (I := I) (M := M) g gm
            (ccTensorUnitValueSection (I := I) (M := M) g T)
            (ccTensorUnitValueSection_contMDiff (I := I) (M := M) g T)
            (Equiv.swap (0 : Fin 4) 2) (Equiv.swap (1 : Fin 4) 3)
            (Equiv.swap (0 : Fin 4) 2 *
              Equiv.swap (1 : Fin 4) 3) 1 := by
    rw [ricciRefold2,
      riemannC2_eq_kernel (I := I) (M := M) g T hδ hδZ
        ricciRefoldQA ricciRefoldQB (fun _ => rfl) s,
      hsymm, smul_smul]
    rfl
  rw [rhsRefold_eq (I := I) (M := M) g g_bg T
    hδ hδZ hT hδ_lt s hs]
  change appCc (I := I) (M := M) g 2 2
      ((-2 : ℝ) •
          linearizedRicciConnDiffOrder0CoeffField
            (I := I) (M := M) g gm -
        (2 : ℝ) •
          refoldKernelContractionField (I := I) (M := M) g gm
            (iteratedCovGrad (I := I) g 0 2 2 P)
            (Equiv.swap (0 : Fin 4) 2) (Equiv.swap (1 : Fin 4) 3)
            (Equiv.swap (0 : Fin 4) 2 *
              Equiv.swap (1 : Fin 4) 3) 1 +
        deTurckLieDLaCoeffField (I := I) (M := M) g gm g_bg +
        deTurckLieDLbCoeffField (I := I) (M := M) g gm g_bg +
        lieCorr0Field (I := I) (M := M) g gm g_bg -
        edgeLiePairFam (I := I) (M := M) g T hδ hδZ
          lieRefoldQ lieRefoldEps s) T = _
  simp only [appCc_add_left, appCc_sub_left, appCc_smul_left]
  rw [hconn, ← hsafe, hkernel]
  simp only [P, iteratedCovGrad_smul, appCc_smul_right]
  have hLie :
      appCc (I := I) (M := M) g 2 2
          (deTurckLieDLaCoeffField (I := I) (M := M) g gm g_bg) T +
        appCc (I := I) (M := M) g 2 2
          (deTurckLieDLbCoeffField (I := I) (M := M) g gm g_bg) T =
      appCc (I := I) (M := M) g 2 2
        (deTurckLieCoeffField (I := I) (M := M) g gm g_bg) T := by
    rw [← appCc_add_left]
    rw [deTurckLieDLaCoeffField_add_deTurckLieDLbCoeffField
      (I := I) (M := M) g gm g_bg]
  simp only [rhsSelfLow, rhsSelfTop, gm, appCc_add_left,
    appCc_sub_left, appCc_smul_left]
  rw [hpal]
  simp only [appCc_smul_left]
  rw [← sub_eq_zero]
  calc
    _ =
        (appCc (I := I) (M := M) g 2 2
            (deTurckLieDLaCoeffField (I := I) (M := M) g gm g_bg) T +
          appCc (I := I) (M := M) g 2 2
            (deTurckLieDLbCoeffField (I := I) (M := M) g gm g_bg) T) -
        appCc (I := I) (M := M) g 2 2
          (deTurckLieCoeffField (I := I) (M := M) g gm g_bg) T := by
      module
    _ = 0 := by rw [hLie, sub_self]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
    [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private theorem unit_add
    (g : SmoothRiemannianMetric I M)
    (A B : SmoothCcTensor g 0 2) (x : M) (v : Fin 2 → E) :
    unitModel (I := I) (M := M) g 2 (A + B) x v =
      unitModel (I := I) (M := M) g 2 A x v +
        unitModel (I := I) (M := M) g 2 B x v := by
  simp only [unitModel]
  rw [SmoothCcTensor.toSection_add, ContMDiffSection.coe_add,
    Pi.add_apply, ContinuousLinearMap.add_apply,
    Tensor0SSpace.toModel_add, ContinuousMultilinearMap.add_apply]

private def selfLowInt
    (g g_bg : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ) :
    SmoothCcTensor g 2 2 :=
  pathIntegralCoeffField (I := I) (M := M) g 2 2
    (rhsSelfLow (I := I) (M := M) g g_bg T hδ hδZ)
    (realizedSmallSet (δ := δ) (δ' := δ))
    realizedSmallSet_isOpen
    (by
      rw [Set.uIcc_of_le zero_le_one]
      exact Icc_subset_realizedSmallSet hδ_lt hδ_lt)
    (selfLow_joint (I := I) (M := M) g g_bg T hδ hδZ)
private def selfTopInt
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ) :
    SmoothCcTensor g 4 2 :=
  pathIntegralCoeffField (I := I) (M := M) g 4 2
    (rhsSelfTop (I := I) (M := M) g T hδ hδZ)
    (realizedSmallSet (δ := δ) (δ' := δ))
    realizedSmallSet_isOpen
    (by
      rw [Set.uIcc_of_le zero_le_one]
      exact Icc_subset_realizedSmallSet hδ_lt hδ_lt)
    (selfTop_joint (I := I) (M := M) g T hδ hδZ)
set_option maxHeartbeats 1600000 in
private theorem refold0_self
    (g g_bg : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    (hT : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g T x u v =
        ccTensorBilin (I := I) g T x v u)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ) :
    appCc (I := I) (M := M) g 2 2
        (rhsRefold0Int (I := I) (M := M) g g_bg T
          hδ_lt hδ hδZ) T =
      appCc (I := I) (M := M) g 2 2
          (selfLowInt (I := I) (M := M) g g_bg T
            hδ_lt hδ hδZ) T +
        appCc (I := I) (M := M) g 4 2
          (selfTopInt (I := I) (M := M) g T
            hδ_lt hδ hδZ)
          (iteratedCovGrad (I := I) g 0 2 2 T) := by
  classical
  have hSI : Set.uIcc (0 : ℝ) 1 ⊆
      realizedSmallSet (δ := δ) (δ' := δ) := by
    rw [Set.uIcc_of_le zero_le_one]
    exact Icc_subset_realizedSmallSet hδ_lt hδ_lt
  let Ψ : ℝ → SmoothCcTensor g 2 2 :=
    rhsRefold0 (I := I) (M := M) g g_bg T hδ hδZ
  let L : ℝ → SmoothCcTensor g 2 2 :=
    rhsSelfLow (I := I) (M := M) g g_bg T hδ hδZ
  let Q : ℝ → SmoothCcTensor g 4 2 :=
    rhsSelfTop (I := I) (M := M) g T hδ hδZ
  have hjΨ : linearizedRicciThreeArmHjoint
      (I := I) (M := M) g 2 Ψ (δ := δ) (δ' := δ) :=
    rhsRefold0_joint (I := I) (M := M) g g_bg T hδ hδZ
  have hjL : linearizedRicciThreeArmHjoint
      (I := I) (M := M) g 2 L (δ := δ) (δ' := δ) :=
    selfLow_joint (I := I) (M := M) g g_bg T hδ hδZ
  have hjQ : linearizedRicciThreeArmHjoint
      (I := I) (M := M) g 4 Q (δ := δ) (δ' := δ) :=
    selfTop_joint (I := I) (M := M) g T hδ hδZ
  have hcΨ : ∀ x : M, ContinuousOn (fun t : ℝ =>
      TensorRSSpace.toModel ((Ψ t).toSection x))
      (realizedSmallSet (δ := δ) (δ' := δ)) := fun x =>
    jointContMDiff_toModel_continuous_slice
      (I := I) g 2 2 Ψ
      (realizedSmallSet (δ := δ) (δ' := δ)) hjΨ x
  have hcL : ∀ x : M, ContinuousOn (fun t : ℝ =>
      TensorRSSpace.toModel ((L t).toSection x))
      (realizedSmallSet (δ := δ) (δ' := δ)) := fun x =>
    jointContMDiff_toModel_continuous_slice
      (I := I) g 2 2 L
      (realizedSmallSet (δ := δ) (δ' := δ)) hjL x
  have hcQ : ∀ x : M, ContinuousOn (fun t : ℝ =>
      TensorRSSpace.toModel ((Q t).toSection x))
      (realizedSmallSet (δ := δ) (δ' := δ)) := fun x =>
    jointContMDiff_toModel_continuous_slice
      (I := I) g 4 2 Q
      (realizedSmallSet (δ := δ) (δ' := δ)) hjQ x
  have hPiΨ :
      rhsRefold0Int (I := I) (M := M) g g_bg T hδ_lt hδ hδZ =
        pathIntegralCoeffField (I := I) (M := M) g 2 2 Ψ
          (realizedSmallSet (δ := δ) (δ' := δ))
          realizedSmallSet_isOpen hSI hjΨ := rfl
  have hPiL :
      selfLowInt (I := I) (M := M) g g_bg T hδ_lt hδ hδZ =
        pathIntegralCoeffField (I := I) (M := M) g 2 2 L
          (realizedSmallSet (δ := δ) (δ' := δ))
          realizedSmallSet_isOpen hSI hjL := rfl
  have hPiQ :
      selfTopInt (I := I) (M := M) g T hδ_lt hδ hδZ =
        pathIntegralCoeffField (I := I) (M := M) g 4 2 Q
          (realizedSmallSet (δ := δ) (δ' := δ))
          realizedSmallSet_isOpen hSI hjQ := rfl
  apply smoothCcTensor_ext_of_unitModel (I := I) (M := M) g
  intro x
  apply ContinuousMultilinearMap.ext
  intro v
  rw [hPiΨ, hPiL, hPiQ]
  rw [pathIntegralCoeffField_appCc_eq
      (I := I) (M := M) g 2 2 Ψ T
      (realizedSmallSet (δ := δ) (δ' := δ))
      realizedSmallSet_isOpen hSI hjΨ hcΨ x v]
  rw [unit_add (I := I) (M := M) g]
  rw [pathIntegralCoeffField_appCc_eq
      (I := I) (M := M) g 2 2 L T
      (realizedSmallSet (δ := δ) (δ' := δ))
      realizedSmallSet_isOpen hSI hjL hcL x v]
  rw [pathIntegralCoeffField_appCc_eq
      (I := I) (M := M) g 4 2 Q
      (iteratedCovGrad (I := I) g 0 2 2 T)
      (realizedSmallSet (δ := δ) (δ' := δ))
      realizedSmallSet_isOpen hSI hjQ hcQ x v]
  have hIL := coeffApp_integrable (I := I) (M := M)
    g 2 2 L T (realizedSmallSet (δ := δ) (δ' := δ))
    hSI hcL x v
  have hIQ := coeffApp_integrable (I := I) (M := M)
    g 4 2 Q (iteratedCovGrad (I := I) g 0 2 2 T)
    (realizedSmallSet (δ := δ) (δ' := δ)) hSI hcQ x v
  rw [← intervalIntegral.integral_add hIL hIQ]
  apply intervalIntegral.integral_congr
  intro s hs
  rw [Set.uIcc_of_le zero_le_one] at hs
  have hrefold := rhsSelf_refold (I := I) (M := M)
    g g_bg T hT hδ_lt hδ hδZ hs
  have hmodel := congrArg
    (fun Z : SmoothCcTensor g 0 2 =>
      unitModel (I := I) (M := M) g 2 Z x v) hrefold
  simpa only [Ψ, L, Q, unit_add (I := I) (M := M) g] using hmodel
private theorem c2_cap
    (g g_bg : SmoothRiemannianMetric I M) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (T : SmoothCcTensor g 0 2)
        (_hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        {δ : ℝ}, δ ≤ 1 / 3 → 0 ≤ δ → ∀ (hδ_lt : δ < 1)
        (hδ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g 4 2 x
            ((rhsRefoldTopInt (I := I) (M := M) g g_bg T hδ_lt hδ hδZ +
              selfTopInt (I := I) (M := M) g T hδ_lt hδ hδZ -
              deTurckPhiMetTotal (I := I) (M := M) g g_bg g).toSection x) ≤
          (K * (δ / (1 - δ) ^ 2)) ^ 2 := by
  obtain ⟨KP, hKP, hPb⟩ := phiMet_cap (I := I) (M := M) g g_bg
  obtain ⟨KR, hKR, hRb⟩ := ricciTop_cap (I := I) (M := M) g
  let KL := 4 * deTurckArmFibreConst (Module.finrank ℝ E)
  let K0 := 4 * KL ^ 2 + 4 * KP ^ 2 + 8 * KR ^ 2
  have hK0 : 0 ≤ K0 := by positivity
  refine ⟨Real.sqrt K0, Real.sqrt_nonneg _, ?_⟩
  intro T hT δ hδ_le hδ0 hδ_lt hδ hδZ x
  let Φ := rhsRefoldTop (I := I) (M := M) g g_bg T hδ hδZ
  let Ψ := rhsSelfTop (I := I) (M := M) g T hδ hδZ
  let C := deTurckPhiMetTotal (I := I) (M := M) g g_bg g
  have hSI : Set.uIcc (0 : ℝ) 1 ⊆
      realizedSmallSet (δ := δ) (δ' := δ) := by
    rw [Set.uIcc_of_le zero_le_one]
    exact Icc_subset_realizedSmallSet hδ_lt hδ_lt
  have hΦ := rhsRefoldTop_joint (I := I) (M := M)
    g g_bg T hδ_lt hδ hδZ
  have hΨ := selfTop_joint (I := I) (M := M) g T hδ hδZ
  have hC := arm_const (I := I) (M := M) g (δ := δ) (δ' := δ) C
  have hKern := threeArmJoint_sub (I := I) (M := M) g _ _
    (threeArmJoint_add (I := I) (M := M) g _ _ hΦ hΨ) hC
  let r1 := δ / (1 - δ)
  let r2 := δ / (1 - δ) ^ 2
  have hr1 : 0 ≤ r1 := div_nonneg hδ0 (by linarith)
  have hr2 : 0 ≤ r2 := div_nonneg hδ0 (sq_nonneg _)
  have hr12 : r1 ≤ r2 := by
    have hb : 0 < 1 - δ := by linarith
    rw [div_le_div_iff₀ hb (sq_pos_of_pos hb)]
    nlinarith [mul_nonneg (sq_nonneg δ) (le_of_lt hb)]
  apply path_add_sub_cap (I := I) (M := M) g 4 hSI Φ Ψ C
    hΦ hΨ hKern x (Real.sqrt K0 * r2)
    (mul_nonneg (Real.sqrt_nonneg _) hr2)
  intro s hs
  let gm := realizedFam (I := I) g T 0 hδ hδZ s
  let P := convexPerturbation (I := I) g T 0 s
  have hsmem : s ∈ realizedSmallSet (δ := δ) (δ' := δ) :=
    Icc_subset_realizedSmallSet hδ_lt hδ_lt hs
  have htie : ∀ (y : M) (u v : TangentSpace I y),
      gm.inner y u v = g.inner y u v +
        ccTensorBilinSymm (I := I) g P y u v :=
    fun y u v => realizedFam_inner_of_mem
      (I := I) g T 0 hδ hδZ hsmem y u v
  have hP : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g P) δ := by
    convert convexPerturbation_gFibreOpBound
      (I := I) (M := M) g T 0 hδ hδZ hs.1 hs.2 using 1 <;> ring
  have hL := lieRefold2_cap (I := I) (M := M)
    g T hδ_lt hδ0 hδ hδZ hs x
  have hP1 := hPb gm P hδ_lt hδ0 htie hP x
  have hR1 := hRb T hT hδ_le hδ0 hδ hδZ s hs x
  have hP2 := hP1.trans (pow_le_pow_left₀
    (mul_nonneg hKP hr1) (mul_le_mul_of_nonneg_left hr12 hKP) 2)
  have hR2 := hR1.trans (pow_le_pow_left₀
    (mul_nonneg hKR hr1) (mul_le_mul_of_nonneg_left hr12 hKR) 2)
  have hRs : riemannianFiberNormSq (I := I) (M := M) g 4 2 x
      (((-2 * s : ℝ) • ricciTop (I := I) (M := M) g gm T).toSection x) ≤
        4 * (KR * r2) ^ 2 := by
    rw [SmoothCcTensor.toSection_smul, ContMDiffSection.coe_smul, Pi.smul_apply,
      riemannianFiberNormSq_smul]
    calc
      (-2 * s) ^ 2 * riemannianFiberNormSq (I := I) (M := M) g 4 2 x
          ((ricciTop (I := I) (M := M) g gm T).toSection x) ≤
        4 * riemannianFiberNormSq (I := I) (M := M) g 4 2 x
          ((ricciTop (I := I) (M := M) g gm T).toSection x) := by
            apply mul_le_mul_of_nonneg_right
              (by nlinarith [hs.1, hs.2])
              (riemannianFiberNormSq_nonneg
                (I := I) (M := M) g 4 2 x _)
      _ ≤ 4 * (KR * r2) ^ 2 := mul_le_mul_of_nonneg_left hR2 (by norm_num)
  rw [topKernel_eq (I := I) (M := M) g g_bg T hδ hδZ s]
  have hAB := riemannianFiberNormSq_add_le (I := I) (M := M) g 4 2 x
    ((lieRefold2 (I := I) (M := M) g T hδ hδZ s).toSection x)
    ((deTurckPhiMetTotal (I := I) (M := M) g g_bg gm -
      deTurckPhiMetTotal (I := I) (M := M) g g_bg g).toSection x)
  have hABC := riemannianFiberNormSq_add_le (I := I) (M := M) g 4 2 x
    ((lieRefold2 (I := I) (M := M) g T hδ hδZ s +
      (deTurckPhiMetTotal (I := I) (M := M) g g_bg gm -
        deTurckPhiMetTotal (I := I) (M := M) g g_bg g)).toSection x)
    (((-2 * s : ℝ) • ricciTop (I := I) (M := M) g gm T).toSection x)
  have htarget : (Real.sqrt K0 * r2) ^ 2 = K0 * r2 ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hK0]
  rw [htarget]
  dsimp only [KL, K0, r1, r2] at hL hP2 hR2 hRs ⊢
  simp only [SmoothCcTensor.toSection_add, ContMDiffSection.coe_add,
    Pi.add_apply] at hAB hABC ⊢
  linarith
private theorem top_sub_lap
    (g g_bg : SmoothRiemannianMetric I M)
    (C : SmoothCcTensor g 4 2) (U : SmoothCcTensor g 0 2) :
    appCc (I := I) (M := M) g 4 2 C
          (iteratedCovGrad (I := I) g 0 2 2 U) -
        rawTensorConnLapSmooth (I := I) g 0 2 U =
      appCc (I := I) (M := M) g 4 2
          (C - deTurckPhiMetTotal (I := I) (M := M) g g_bg g)
          (iteratedCovGrad (I := I) g 0 2 2 U) +
        appCc (I := I) (M := M) g 2 2
          (phiMetCurvCoeff (I := I) g g_bg g) U := by
  have hlap : rawTensorConnLapSmooth (I := I) g 0 2 U =
      appCc (I := I) (M := M) g 4 2
        (ricciArmPrincipalCoeffPure (I := I) (M := M) g g)
        (iteratedCovGrad (I := I) g 0 2 2 U) := by
    apply smoothCcTensor_ext_of_unitModel (I := I) (M := M) g
    intro x
    apply ContinuousMultilinearMap.ext
    intro v
    exact rawTensorConnLapSmooth_eq_appCc_cometricDoubleTrace
      (I := I) (M := M) g U x v
  have hcurv := phiMet_curv_fold
    (I := I) (M := M) g g_bg g U
  rw [appCc_sub_left] at hcurv
  simp only [iteratedCovGrad_zero] at hcurv
  rw [hlap, appCc_sub_left, ← hcurv]
  abel

/-- Squared intrinsic covariant `L2` jet through order `m`. -/
noncomputable def lowJetSq
    (g : SmoothRiemannianMetric I M) {r s : ℕ} (m : ℕ)
    (S : SmoothCcTensor g r s) : ℝ :=
  ∑ q ∈ Finset.range (m + 1),
    ‖iteratedCovGrad (I := I) g r s q S‖ ^ 2

omit [BoundarylessManifold I M] in
private theorem jet_term_le
    (g : SmoothRiemannianMetric I M) {r s q m : ℕ}
    (hqm : q ≤ m) (S : SmoothCcTensor g r s) :
    ‖iteratedCovGrad (I := I) g r s q S‖ ^ 2 ≤
      lowJetSq (I := I) (M := M) g m S := by
  unfold lowJetSq
  exact Finset.single_le_sum
    (fun j _ => sq_nonneg
      ‖iteratedCovGrad (I := I) g r s j S‖)
    (Finset.mem_range.mpr (by omega))

set_option linter.unusedVariables false in
private theorem trace_h2_rf
    (p : ℕ) (g : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀0 : 0 ≤ δ₀) (hδ₀ : δ₀ < 1) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (g₁ : SmoothRiemannianMetric I M)
        (P : SmoothCcTensor g 0 2)
        (hP : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g P x u v =
            ccTensorBilin (I := I) g P x v u)
        (htie : ∀ (x : M) (u v : TangentSpace I x),
          g₁.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g P x u v)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
        (hδ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g P) δ)
        (σ : Equiv.Perm (Fin (p + 2))),
      lowJetSq (I := I) (M := M) g 2
          (lc0TraceRF (I := I) (M := M) g g₁ p σ) ≤
        K * (1 + lowJetSq (I := I) (M := M) g 2 P) := by
  classical
  haveI : IsFiniteMeasure
      (riemannianVolumeMeasure (I := I) (M := M) g) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace g
  obtain ⟨C, hC0, hC⟩ :=
    trace_grid_rf (I := I) (M := M) p g hδ₀
  let Λ₀ : ℝ := (Module.finrank ℝ E : ℝ) * δ₀
  have hΛ₀0 : 0 ≤ Λ₀ :=
    mul_nonneg (Nat.cast_nonneg _) hδ₀0
  obtain ⟨G, hG0, hG⟩ :=
    antidiagonalTupleGrid_integral_radiusFree
      (I := I) (M := M) g hΛ₀0
  let K : ℝ :=
    ∑ q ∈ Finset.range 3,
      C q * ∑ k ∈ Finset.range (q + 1), G k
  have hK0 : 0 ≤ K := by
    dsimp only [K]
    exact Finset.sum_nonneg fun q _ =>
      mul_nonneg (hC0 q) (Finset.sum_nonneg fun k _ => hG0 k)
  refine ⟨K, hK0, ?_⟩
  intro g₁ P hP htie δ hδ_le hδ0 hδ σ
  have hsymm : symmS (I := I) (M := M) g P = P :=
    symm_eq_self (I := I) (M := M) g P hP
  have hsup : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g 0 2 x
          (P.toSection x) ≤ Λ₀ ^ 2 := by
    intro x
    rw [← hsymm]
    exact rfns_symmS_zero_le_fibreSmall
      (I := I) (M := M) g hδ₀0 P hδ_le hδ0 hδ x
  have hAG : ∀ k : ℕ,
      MeasureTheory.Integrable
          (fun x => Combinatorics.antidiagonalTupleGrid
            (fun j => riemannianFiberNormSq
              (I := I) (M := M) g 0 (2 + j) x
              ((iteratedCovGrad (I := I) g 0 2 j P).toSection x)) k)
          (riemannianVolumeMeasure (I := I) (M := M) g) ∧
        (∫ x, Combinatorics.antidiagonalTupleGrid
            (fun j => riemannianFiberNormSq
              (I := I) (M := M) g 0 (2 + j) x
              ((iteratedCovGrad (I := I) g 0 2 j P).toSection x)) k
            ∂(riemannianVolumeMeasure (I := I) (M := M) g)) ≤
          G k *
            (1 + ‖iteratedCovGrad (I := I) g 0 2 k P‖ ^ 2) := by
    intro k
    have hexpand :
        (fun x => Combinatorics.antidiagonalTupleGrid
          (fun j => riemannianFiberNormSq
            (I := I) (M := M) g 0 (2 + j) x
            ((iteratedCovGrad (I := I) g 0 2 j P).toSection x)) k) =
          (fun x => ∑ n ∈ Finset.range (k + 1),
            ∑ e ∈ Finset.Nat.antidiagonalTuple n k,
              ∏ m : Fin n,
                riemannianFiberNormSq
                  (I := I) (M := M) g 0 (2 + e m) x
                  ((iteratedCovGrad (I := I) g 0 2
                    (e m) P).toSection x)) := by
      funext x
      rw [Combinatorics.antidiagonalTupleGrid]
    rw [hexpand]
    exact hG P hsup k
  have hper : ∀ q : ℕ, q ≤ 2 →
      ‖iteratedCovGrad (I := I) g (p + 2) p q
          (lc0TraceRF (I := I) (M := M) g g₁ p σ)‖ ^ 2 ≤
        (C q * ∑ k ∈ Finset.range (q + 1), G k) *
          (1 + lowJetSq (I := I) (M := M) g 2 P) := by
    intro q hq
    let W : M → ℝ := fun x =>
      ∑ k ∈ Finset.range (q + 1),
        Combinatorics.antidiagonalTupleGrid
          (fun j => riemannianFiberNormSq
            (I := I) (M := M) g 0 (2 + j) x
            ((iteratedCovGrad (I := I) g 0 2 j P).toSection x)) k
    have hWint : MeasureTheory.Integrable W
        (riemannianVolumeMeasure (I := I) (M := M) g) := by
      dsimp only [W]
      exact MeasureTheory.integrable_finset_sum _
        (fun k _ => (hAG k).1)
    have hCWint : MeasureTheory.Integrable
        (fun x => C q * W x)
        (riemannianVolumeMeasure (I := I) (M := M) g) :=
      hWint.const_mul _
    have hnorm :=
      normSq_le_integral_of_pointwise_fiberNormSq_le_rs
        (I := I) (M := M) g (p + 2) (p + q)
        (iteratedCovGrad (I := I) g (p + 2) p q
          (lc0TraceRF (I := I) (M := M) g g₁ p σ))
        (fun x => C q * W x) hCWint
        (fun x => by
          simpa only [W] using
            hC g₁ P htie hδ_le hδ0 hδ σ q x)
    rw [MeasureTheory.integral_const_mul] at hnorm
    refine le_trans hnorm ?_
    have hWbd : (∫ x, W x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g)) ≤
        (∑ k ∈ Finset.range (q + 1), G k) *
          (1 + lowJetSq (I := I) (M := M) g 2 P) := by
      dsimp only [W]
      rw [MeasureTheory.integral_finset_sum _
        (fun k _ => (hAG k).1), Finset.sum_mul]
      refine Finset.sum_le_sum fun k hk => ?_
      refine le_trans (hAG k).2 ?_
      apply mul_le_mul_of_nonneg_left _ (hG0 k)
      have hkq : k ≤ q := by
        exact Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      have hterm :=
        jet_term_le (I := I) (M := M) g
          (le_trans hkq hq) P
      linarith
    calc
      C q * (∫ x, W x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g))
          ≤ C q * ((∑ k ∈ Finset.range (q + 1), G k) *
            (1 + lowJetSq (I := I) (M := M) g 2 P)) :=
        mul_le_mul_of_nonneg_left hWbd (hC0 q)
      _ = (C q * ∑ k ∈ Finset.range (q + 1), G k) *
          (1 + lowJetSq (I := I) (M := M) g 2 P) := by ring
  unfold lowJetSq
  rw [Finset.sum_mul]
  exact Finset.sum_le_sum fun q hq =>
    hper q (by
      have : q < 3 := Finset.mem_range.mp hq
      omega)

set_option linter.unusedVariables false in
private theorem conn_h2_rf
    (g : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀0 : 0 ≤ δ₀) (hδ₀ : δ₀ < 1) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (g₁ : SmoothRiemannianMetric I M)
        (P : SmoothCcTensor g 0 2)
        (hP : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g P x u v =
            ccTensorBilin (I := I) g P x v u)
        (htie : ∀ (x : M) (u v : TangentSpace I x),
          g₁.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g P x u v)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
        (hδ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g P) δ),
      lowJetSq (I := I) (M := M) g 2
          (connDiffSection (I := I) g₁ g) ≤
        K * (1 + lowJetSq (I := I) (M := M) g 3 P) := by
  classical
  let Λ₀ : ℝ := (Module.finrank ℝ E : ℝ) * δ₀
  have hΛ₀0 : 0 ≤ Λ₀ :=
    mul_nonneg (Nat.cast_nonneg _) hδ₀0
  obtain ⟨Flow, hFlow0, hFlow⟩ :=
    connDiffSection_lowOrder_jetL2_radiusFree
      (I := I) (M := M) g
        (2 * Module.finrank ℝ E + 10) le_rfl hδ₀ hΛ₀0
  refine ⟨Flow 2, hFlow0 2, ?_⟩
  intro g₁ P hP htie δ hδ_le hδ0 hδ
  have hsymm : symmS (I := I) (M := M) g P = P :=
    symm_eq_self (I := I) (M := M) g P hP
  have hsup : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g 0 2 x
          (P.toSection x) ≤ Λ₀ ^ 2 := by
    intro x
    rw [← hsymm]
    exact rfns_symmS_zero_le_fibreSmall
      (I := I) (M := M) g hδ₀0 P hδ_le hδ0 hδ x
  simpa only [lowJetSq, Nat.reduceAdd] using
    hFlow g₁ P htie hδ_le hδ0 hδ hsup 2 (by omega)

private theorem slot_l2
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

private theorem slot_h2
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
        slot_l2 (I := I) (M := M) g r s i Φ
    _ = (Module.finrank ℝ E : ℝ) *
        ∑ i ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g r s i Φ‖ ^ 2 := by
      rw [Finset.mul_sum]

private theorem reindex_h2
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (Φ : SmoothCcTensor g r s) (ρ : Equiv.Perm (Fin r)) :
    lowJetSq (I := I) (M := M) g 2
        (reindexCoeffGen (I := I) (M := M) g r s Φ ρ) =
      lowJetSq (I := I) (M := M) g 2 Φ := by
  unfold lowJetSq
  apply Finset.sum_congr rfl
  intro i _
  rw [iteratedCovGrad_reindexCoeffGen,
    norm_reindexCoeffGen_eq]

set_option linter.unusedVariables false in
private theorem app_h2_mul
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
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hW0 : 0 ≤ lowJetSq (I := I) (M := M) g 2 W :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
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

/-- Three intrinsic coefficients of the smooth-core low-base action split. -/
structure LowBaseActionData
    (g : SmoothRiemannianMetric I M) where
  C0 : SmoothCcTensor g 2 2
  C1 : SmoothCcTensor g 3 2
  C2 : SmoothCcTensor g 4 2

/-- The genuinely first-order action associated to low-base coefficient data. -/
noncomputable def LowBaseActionData.a1
    {g : SmoothRiemannianMetric I M} (A : LowBaseActionData g)
    (W : SmoothCcTensor g 0 2) : SmoothCcTensor g 0 2 :=
  appCc (I := I) (M := M) g 2 2 A.C0 W +
    appCc (I := I) (M := M) g 3 2 A.C1
      (iteratedCovGrad (I := I) g 0 2 1 W)

/-- The small second-order action associated to low-base coefficient data. -/
noncomputable def LowBaseActionData.a2
    {g : SmoothRiemannianMetric I M} (A : LowBaseActionData g)
    (W : SmoothCcTensor g 0 2) : SmoothCcTensor g 0 2 :=
  appCc (I := I) (M := M) g 4 2 A.C2
    (iteratedCovGrad (I := I) g 0 2 2 W)

private def lowData
    (g g_bg : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ) :
    LowBaseActionData g where
  C0 := selfLowInt (I := I) (M := M) g g_bg T
      hδ_lt hδ hδZ + phiMetCurvCoeff (I := I) g g_bg g
  C1 := rhsLow1PathIntegral (I := I) (M := M)
      g g_bg T 0 hδ_lt hδ hδ_lt hδZ
  C2 := rhsRefoldTopInt (I := I) (M := M)
      g g_bg T hδ_lt hδ hδZ +
    selfTopInt (I := I) (M := M) g T hδ_lt hδ hδZ -
    deTurckPhiMetTotal (I := I) (M := M) g g_bg g

set_option maxHeartbeats 1600000 in
/-- The zero-based Ricci--DeTurck smooth remainder is exactly the sum of the
small second-order action and the genuinely first-order action. -/
theorem remainder_low_split
    (g g_bg : SmoothRiemannianMetric I M) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (T : SmoothCcTensor g 0 2)
        (hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        {δ : ℝ} (hδ_le : δ ≤ 1 / 3) (hδ0 : 0 ≤ δ)
        (hδ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ),
      ∃ A : LowBaseActionData g,
        deTurckSmoothRemainder (I := I) g g_bg T
              (lt_of_le_of_lt hδ_le (by norm_num)) hδ -
            deTurckSmoothRemainder (I := I) g g_bg
              (0 : SmoothCcTensor g 0 2)
              (lt_of_le_of_lt hδ_le (by norm_num)) hδZ =
          A.a2 (I := I) (M := M) T + A.a1 (I := I) (M := M) T ∧
        ∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g 4 2 x
              (A.C2.toSection x) ≤
            (K * (δ / (1 - δ) ^ 2)) ^ 2 := by
  obtain ⟨K, hK, hcap⟩ := c2_cap (I := I) (M := M) g g_bg
  refine ⟨K, hK, ?_⟩
  intro T hT δ hδ_le hδ0 hδ hδZ
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le (by norm_num)
  let A := lowData (I := I) (M := M)
    g g_bg T hδ_lt hδ hδZ
  refine ⟨A, ?_, fun x => by
    simpa only [A, lowData] using
      hcap T hT hδ_le hδ0 hδ_lt hδ hδZ x⟩
  change
    (realizedRHSArm (I := I) g g_bg T hδ_lt hδ -
        rawTensorConnLapSmooth (I := I) g 0 2 T) -
      (realizedRHSArm (I := I) g g_bg
          (0 : SmoothCcTensor g 0 2) hδ_lt hδZ -
        rawTensorConnLapSmooth (I := I) g 0 2
          (0 : SmoothCcTensor g 0 2)) = _
  have hlap0 : rawTensorConnLapSmooth (I := I) g 0 2
      (0 : SmoothCcTensor g 0 2) = 0 := by
    have hzero := rawTensorConnLapSmooth_sub
      (I := I) (M := M) g 0 2 T T
    rwa [sub_self, sub_self] at hzero
  rw [hlap0, sub_zero]
  rw [show
    (realizedRHSArm (I := I) g g_bg T hδ_lt hδ -
        rawTensorConnLapSmooth (I := I) g 0 2 T) -
      realizedRHSArm (I := I) g g_bg
        (0 : SmoothCcTensor g 0 2) hδ_lt hδZ =
      (realizedRHSArm (I := I) g g_bg T hδ_lt hδ -
        realizedRHSArm (I := I) g g_bg
          (0 : SmoothCcTensor g 0 2) hδ_lt hδZ) -
        rawTensorConnLapSmooth (I := I) g 0 2 T by abel]
  rw [rhs_sub_zero_refold (I := I) (M := M)
    g g_bg T hT hδ_lt hδ hδZ]
  rw [refold0_self (I := I) (M := M)
    g g_bg T hT hδ_lt hδ hδZ]
  rw [show
      (appCc (I := I) (M := M) g 2 2
          (selfLowInt (I := I) (M := M) g g_bg T
            hδ_lt hδ hδZ) T +
        appCc (I := I) (M := M) g 4 2
          (selfTopInt (I := I) (M := M) g T
            hδ_lt hδ hδZ)
          (iteratedCovGrad (I := I) g 0 2 2 T) +
        appCc (I := I) (M := M) g 3 2
          (rhsLow1PathIntegral (I := I) (M := M)
            g g_bg T 0 hδ_lt hδ hδ_lt hδZ)
          (iteratedCovGrad (I := I) g 0 2 1 T) +
        appCc (I := I) (M := M) g 4 2
          (rhsRefoldTopInt (I := I) (M := M)
            g g_bg T hδ_lt hδ hδZ)
          (iteratedCovGrad (I := I) g 0 2 2 T)) -
        rawTensorConnLapSmooth (I := I) g 0 2 T =
      (appCc (I := I) (M := M) g 4 2
          (rhsRefoldTopInt (I := I) (M := M)
              g g_bg T hδ_lt hδ hδZ +
            selfTopInt (I := I) (M := M) g T
              hδ_lt hδ hδZ)
          (iteratedCovGrad (I := I) g 0 2 2 T) -
        rawTensorConnLapSmooth (I := I) g 0 2 T) +
      (appCc (I := I) (M := M) g 2 2
          (selfLowInt (I := I) (M := M) g g_bg T
            hδ_lt hδ hδZ) T +
        appCc (I := I) (M := M) g 3 2
          (rhsLow1PathIntegral (I := I) (M := M)
            g g_bg T 0 hδ_lt hδ hδ_lt hδZ)
          (iteratedCovGrad (I := I) g 0 2 1 T)) by
      rw [appCc_add_left]
      abel]
  rw [top_sub_lap (I := I) (M := M) g g_bg]
  simp only [A, lowData, LowBaseActionData.a1,
    LowBaseActionData.a2, appCc_add_left, appCc_sub_left]
  abel

/-! ## Fixed three-dimensional action estimates -/

omit [BoundarylessManifold I M] in
private theorem jet_nonneg
    (g : SmoothRiemannianMetric I M) {r s m : ℕ}
    (S : SmoothCcTensor g r s) :
    0 ≤ lowJetSq (I := I) (M := M) g m S :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

omit [BoundarylessManifold I M] in
private theorem jet_mono
    (g : SmoothRiemannianMetric I M) {r s m n : ℕ}
    (hmn : m ≤ n) (S : SmoothCcTensor g r s) :
    lowJetSq (I := I) (M := M) g m S ≤
      lowJetSq (I := I) (M := M) g n S := by
  unfold lowJetSq
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.range_subset_range.mpr (Nat.add_le_add_right hmn 1))
    (fun _ _ _ => sq_nonneg _)

private theorem jet_add
    (g : SmoothRiemannianMetric I M) {r s : ℕ} (m : ℕ)
    (S T : SmoothCcTensor g r s) :
    lowJetSq (I := I) (M := M) g m (S + T) ≤
      2 * (lowJetSq (I := I) (M := M) g m S +
        lowJetSq (I := I) (M := M) g m T) := by
  unfold lowJetSq
  calc
    ∑ q ∈ Finset.range (m + 1),
        ‖iteratedCovGrad (I := I) g r s q (S + T)‖ ^ 2 ≤
        ∑ q ∈ Finset.range (m + 1),
          2 * (‖iteratedCovGrad (I := I) g r s q S‖ ^ 2 +
            ‖iteratedCovGrad (I := I) g r s q T‖ ^ 2) := by
      refine Finset.sum_le_sum fun q _ => ?_
      rw [iteratedCovGrad_add]
      have htri := norm_add_le
        (iteratedCovGrad (I := I) g r s q S)
        (iteratedCovGrad (I := I) g r s q T)
      calc
        ‖iteratedCovGrad (I := I) g r s q S +
            iteratedCovGrad (I := I) g r s q T‖ ^ 2 ≤
            (‖iteratedCovGrad (I := I) g r s q S‖ +
              ‖iteratedCovGrad (I := I) g r s q T‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) htri 2
        _ ≤ 2 * (‖iteratedCovGrad (I := I) g r s q S‖ ^ 2 +
            ‖iteratedCovGrad (I := I) g r s q T‖ ^ 2) := by
          nlinarith [sq_nonneg
            (‖iteratedCovGrad (I := I) g r s q S‖ -
              ‖iteratedCovGrad (I := I) g r s q T‖)]
    _ = 2 * ((∑ q ∈ Finset.range (m + 1),
          ‖iteratedCovGrad (I := I) g r s q S‖ ^ 2) +
        ∑ q ∈ Finset.range (m + 1),
          ‖iteratedCovGrad (I := I) g r s q T‖ ^ 2) := by
      simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]

private theorem jet_smul
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

private theorem jet_sub
    (g : SmoothRiemannianMetric I M) {r s : ℕ} (m : ℕ)
    (S T : SmoothCcTensor g r s) :
    lowJetSq (I := I) (M := M) g m (S - T) ≤
      2 * (lowJetSq (I := I) (M := M) g m S +
        lowJetSq (I := I) (M := M) g m T) := by
  have hneg :
      lowJetSq (I := I) (M := M) g m (-T) =
        lowJetSq (I := I) (M := M) g m T := by
    unfold lowJetSq
    apply Finset.sum_congr rfl
    intro q _
    rw [iteratedCovGrad_neg, norm_neg]
  rw [sub_eq_add_neg]
  simpa only [hneg] using
    jet_add (I := I) (M := M) g m S (-T)

private theorem pure_eq_trace
    (g g₁ : SmoothRiemannianMetric I M) :
    ricciArmPrincipalCoeffPure (I := I) (M := M) g g₁ =
      pureTrace (I := I) (M := M) g g₁ 2 := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [ricciArmPrincipalCoeffPure_toSection,
    pureTrace_toSection]

set_option linter.unusedVariables false in
private theorem fourtrace_h2_rf
    (g : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀0 : 0 ≤ δ₀) (hδ₀ : δ₀ < 1) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (g₁ : SmoothRiemannianMetric I M)
        (P : SmoothCcTensor g 0 2)
        (hP : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g P x u v =
            ccTensorBilin (I := I) g P x v u)
        (htie : ∀ (x : M) (u v : TangentSpace I x),
          g₁.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g P x u v)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
        (hδ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g P) δ),
      lowJetSq (I := I) (M := M) g 2
          (ricciCometricFourTraceCastG0 (I := I) g g₁) ≤
        K * (1 + lowJetSq (I := I) (M := M) g 2 P) := by
  classical
  obtain ⟨K₀, hK₀, htrace⟩ :=
    trace_h2_rf (I := I) (M := M) 2 g hδ₀0 hδ₀
  refine ⟨22 * K₀, mul_nonneg (by norm_num) hK₀, ?_⟩
  intro g₁ P hP htie δ hδ_le hδ0 hδ
  let F : SmoothCcTensor g 4 2 :=
    ricciArmPrincipalCoeffPure (I := I) (M := M) g g₁
  let R₁ : SmoothCcTensor g 4 2 :=
    reindexCoeffGen (I := I) (M := M) g 4 2 F
      fourTraceArgPerm0231
  let R₂ : SmoothCcTensor g 4 2 :=
    reindexCoeffGen (I := I) (M := M) g 4 2 F
      fourTraceArgPerm0321
  let R₃ : SmoothCcTensor g 4 2 :=
    reindexCoeffGen (I := I) (M := M) g 4 2 F
      fourTraceArgPerm2301
  have hF :
      lowJetSq (I := I) (M := M) g 2 F ≤
        K₀ * (1 + lowJetSq (I := I) (M := M) g 2 P) := by
    have h :=
      htrace g₁ P hP htie hδ_le hδ0 hδ
        (Equiv.refl (Fin 4))
    rw [lc0TraceRF, reindex_h2] at h
    simpa only [F, pure_eq_trace (I := I) (M := M) g g₁] using h
  have hR₁ :
      lowJetSq (I := I) (M := M) g 2 R₁ =
        lowJetSq (I := I) (M := M) g 2 F := by
    exact reindex_h2 (I := I) (M := M) g 4 2 F
      fourTraceArgPerm0231
  have hR₂ :
      lowJetSq (I := I) (M := M) g 2 R₂ =
        lowJetSq (I := I) (M := M) g 2 F := by
    exact reindex_h2 (I := I) (M := M) g 4 2 F
      fourTraceArgPerm0321
  have hR₃ :
      lowJetSq (I := I) (M := M) g 2 R₃ =
        lowJetSq (I := I) (M := M) g 2 F := by
    exact reindex_h2 (I := I) (M := M) g 4 2 F
      fourTraceArgPerm2301
  have h12 :
      lowJetSq (I := I) (M := M) g 2 (R₁ + R₂) ≤
        4 * lowJetSq (I := I) (M := M) g 2 F := by
    have h := jet_add (I := I) (M := M) g 2 R₁ R₂
    rw [hR₁, hR₂] at h
    linarith
  have h123 :
      lowJetSq (I := I) (M := M) g 2 (R₁ + R₂ - F) ≤
        10 * lowJetSq (I := I) (M := M) g 2 F := by
    have h := jet_sub (I := I) (M := M) g 2 (R₁ + R₂) F
    have hF0 := jet_nonneg (I := I) (M := M) (m := 2) g F
    nlinarith
  have h1234 :
      lowJetSq (I := I) (M := M) g 2
          (R₁ + R₂ - F - R₃) ≤
        22 * lowJetSq (I := I) (M := M) g 2 F := by
    have h := jet_sub (I := I) (M := M) g 2
      (R₁ + R₂ - F) R₃
    rw [hR₃] at h
    have hF0 := jet_nonneg (I := I) (M := M) (m := 2) g F
    nlinarith
  have hcomb :
      ricciCometricFourTraceCastG0 (I := I) g g₁ =
        ((1 : ℝ) / 2) • (R₁ + R₂ - F - R₃) := by
    simpa only [F, R₁, R₂, R₃] using
      ricciCometricFourTraceCastG0_eq_reindex_combination
        (I := I) g g₁
  rw [hcomb, jet_smul]
  have hJ0 := jet_nonneg (I := I) (M := M) (m := 2) g
    (R₁ + R₂ - F - R₃)
  calc
    ((1 : ℝ) / 2) ^ 2 *
        lowJetSq (I := I) (M := M) g 2 (R₁ + R₂ - F - R₃) ≤
      lowJetSq (I := I) (M := M) g 2 (R₁ + R₂ - F - R₃) := by
        nlinarith
    _ ≤ 22 * lowJetSq (I := I) (M := M) g 2 F := h1234
    _ ≤ 22 * (K₀ *
        (1 + lowJetSq (I := I) (M := M) g 2 P)) :=
      mul_le_mul_of_nonneg_left hF (by norm_num)
    _ = (22 * K₀) *
        (1 + lowJetSq (I := I) (M := M) g 2 P) := by ring

private def H2Poly
    (g : SmoothRiemannianMetric I M) (P : SmoothCcTensor g 0 2)
    {r s : ℕ} (n : ℕ) (K : ℝ) (S : SmoothCcTensor g r s) : Prop :=
  0 ≤ K ∧
    lowJetSq (I := I) (M := M) g 2 S ≤
      K * (1 + lowJetSq (I := I) (M := M) g 3 P) ^ n

omit [BoundarylessManifold I M] in
private theorem hp_const
    (g : SmoothRiemannianMetric I M) (P : SmoothCcTensor g 0 2)
    {r s : ℕ} (S : SmoothCcTensor g r s) :
    H2Poly (I := I) (M := M) g P 0
      (lowJetSq (I := I) (M := M) g 2 S) S := by
  refine ⟨jet_nonneg (I := I) (M := M) (m := 2) g S, ?_⟩
  rw [pow_zero, mul_one]

private theorem hp_add
    (g : SmoothRiemannianMetric I M) (P : SmoothCcTensor g 0 2)
    {r s n : ℕ} {A B : ℝ}
    {S T : SmoothCcTensor g r s}
    (hS : H2Poly (I := I) (M := M) g P n A S)
    (hT : H2Poly (I := I) (M := M) g P n B T) :
    H2Poly (I := I) (M := M) g P n
      (2 * (A + B)) (S + T) := by
  have hX0 : 0 ≤
      (1 + lowJetSq (I := I) (M := M) g 3 P) ^ n :=
    pow_nonneg (by
      linarith [jet_nonneg (I := I) (M := M) (m := 3) g P]) n
  refine ⟨mul_nonneg (by norm_num) (add_nonneg hS.1 hT.1), ?_⟩
  calc
    lowJetSq (I := I) (M := M) g 2 (S + T) ≤
        2 * (lowJetSq (I := I) (M := M) g 2 S +
          lowJetSq (I := I) (M := M) g 2 T) :=
      jet_add (I := I) (M := M) g 2 S T
    _ ≤ 2 * (A *
          (1 + lowJetSq (I := I) (M := M) g 3 P) ^ n +
        B * (1 + lowJetSq (I := I) (M := M) g 3 P) ^ n) :=
      mul_le_mul_of_nonneg_left (add_le_add hS.2 hT.2) (by norm_num)
    _ = 2 * (A + B) *
        (1 + lowJetSq (I := I) (M := M) g 3 P) ^ n := by ring

private theorem hp_sub
    (g : SmoothRiemannianMetric I M) (P : SmoothCcTensor g 0 2)
    {r s n : ℕ} {A B : ℝ}
    {S T : SmoothCcTensor g r s}
    (hS : H2Poly (I := I) (M := M) g P n A S)
    (hT : H2Poly (I := I) (M := M) g P n B T) :
    H2Poly (I := I) (M := M) g P n
      (2 * (A + B)) (S - T) := by
  refine ⟨mul_nonneg (by norm_num) (add_nonneg hS.1 hT.1), ?_⟩
  calc
    lowJetSq (I := I) (M := M) g 2 (S - T) ≤
        2 * (lowJetSq (I := I) (M := M) g 2 S +
          lowJetSq (I := I) (M := M) g 2 T) :=
      jet_sub (I := I) (M := M) g 2 S T
    _ ≤ 2 * (A *
          (1 + lowJetSq (I := I) (M := M) g 3 P) ^ n +
        B * (1 + lowJetSq (I := I) (M := M) g 3 P) ^ n) :=
      mul_le_mul_of_nonneg_left (add_le_add hS.2 hT.2) (by norm_num)
    _ = 2 * (A + B) *
        (1 + lowJetSq (I := I) (M := M) g 3 P) ^ n := by ring

private theorem hp_smul
    (g : SmoothRiemannianMetric I M) (P : SmoothCcTensor g 0 2)
    {r s n : ℕ} {A : ℝ} {S : SmoothCcTensor g r s}
    (c : ℝ)
    (hS : H2Poly (I := I) (M := M) g P n A S) :
    H2Poly (I := I) (M := M) g P n
      (c ^ 2 * A) (c • S) := by
  refine ⟨mul_nonneg (sq_nonneg _) hS.1, ?_⟩
  rw [jet_smul]
  calc
    c ^ 2 * lowJetSq (I := I) (M := M) g 2 S ≤
        c ^ 2 * (A *
          (1 + lowJetSq (I := I) (M := M) g 3 P) ^ n) :=
      mul_le_mul_of_nonneg_left hS.2 (sq_nonneg _)
    _ = c ^ 2 * A *
        (1 + lowJetSq (I := I) (M := M) g 3 P) ^ n := by ring

private theorem hp_reindex
    (g : SmoothRiemannianMetric I M) (P : SmoothCcTensor g 0 2)
    {r s n : ℕ} {A : ℝ} {S : SmoothCcTensor g r s}
    (ρ : Equiv.Perm (Fin r))
    (hS : H2Poly (I := I) (M := M) g P n A S) :
    H2Poly (I := I) (M := M) g P n A
      (reindexCoeffGen (I := I) (M := M) g r s S ρ) := by
  refine ⟨hS.1, ?_⟩
  rw [reindex_h2]
  exact hS.2

private theorem hp_slot
    (g : SmoothRiemannianMetric I M) (P : SmoothCcTensor g 0 2)
    {r s n : ℕ} {A : ℝ} {S : SmoothCcTensor g r s}
    (hS : H2Poly (I := I) (M := M) g P n A S) :
    H2Poly (I := I) (M := M) g P n
      ((Module.finrank ℝ E : ℝ) * A)
      (slotExtend (I := I) (M := M) g r s S) := by
  have hfr : (0 : ℝ) ≤ Module.finrank ℝ E := Nat.cast_nonneg _
  refine ⟨mul_nonneg hfr hS.1, ?_⟩
  calc
    lowJetSq (I := I) (M := M) g 2
        (slotExtend (I := I) (M := M) g r s S) ≤
      (Module.finrank ℝ E : ℝ) *
        lowJetSq (I := I) (M := M) g 2 S :=
      slot_h2 (I := I) (M := M) g r s S
    _ ≤ (Module.finrank ℝ E : ℝ) *
        (A * (1 + lowJetSq (I := I) (M := M) g 3 P) ^ n) :=
      mul_le_mul_of_nonneg_left hS.2 hfr
    _ = ((Module.finrank ℝ E : ℝ) * A) *
        (1 + lowJetSq (I := I) (M := M) g 3 P) ^ n := by ring

private theorem hp_slot2
    (g : SmoothRiemannianMetric I M) (P : SmoothCcTensor g 0 2)
    {r s n : ℕ} {A : ℝ} {S : SmoothCcTensor g r s}
    (hS : H2Poly (I := I) (M := M) g P n A S) :
    H2Poly (I := I) (M := M) g P n
      ((Module.finrank ℝ E : ℝ) * ((Module.finrank ℝ E : ℝ) * A))
      (slotExtendIter (I := I) (M := M) g r s 2 S) := by
  have h1 := hp_slot (I := I) (M := M) g P hS
  have h2 := hp_slot (I := I) (M := M) g P h1
  simpa only [slotExtendIter, Nat.add_zero, Nat.zero_add,
    Nat.reduceAdd] using h2

private theorem hp_slot3
    (g : SmoothRiemannianMetric I M) (P : SmoothCcTensor g 0 2)
    {r s n : ℕ} {A : ℝ} {S : SmoothCcTensor g r s}
    (hS : H2Poly (I := I) (M := M) g P n A S) :
    H2Poly (I := I) (M := M) g P n
      ((Module.finrank ℝ E : ℝ) *
        ((Module.finrank ℝ E : ℝ) * ((Module.finrank ℝ E : ℝ) * A)))
      (slotExtendIter (I := I) (M := M) g r s 3 S) := by
  have h1 := hp_slot (I := I) (M := M) g P hS
  have h2 := hp_slot (I := I) (M := M) g P h1
  have h3 := hp_slot (I := I) (M := M) g P h2
  simpa only [slotExtendIter, Nat.add_zero, Nat.zero_add,
    Nat.reduceAdd] using h3

set_option linter.unusedVariables false in
private theorem hp_app_of
    (g : SmoothRiemannianMetric I M) (P : SmoothCcTensor g 0 2)
    {p r c n m : ℕ} {A B : ℝ}
    {Φ : SmoothCcTensor g r c} {W : SmoothCcTensor g p r}
    (C : ℝ) (hC : 0 ≤ C)
    (happ : lowJetSq (I := I) (M := M) g 2
          (appCcRS (I := I) (M := M) g p r c Φ W) ≤
        C * lowJetSq (I := I) (M := M) g 2 Φ *
          lowJetSq (I := I) (M := M) g 2 W)
    (hΦ : H2Poly (I := I) (M := M) g P n A Φ)
    (hW : H2Poly (I := I) (M := M) g P m B W) :
    H2Poly (I := I) (M := M) g P (n + m) (C * A * B)
      (appCcRS (I := I) (M := M) g p r c Φ W) := by
  let X : ℝ := 1 + lowJetSq (I := I) (M := M) g 3 P
  have hX : 0 ≤ X := by
    dsimp only [X]
    linarith [jet_nonneg (I := I) (M := M) (m := 3) g P]
  refine ⟨mul_nonneg (mul_nonneg hC hΦ.1) hW.1, ?_⟩
  calc
    lowJetSq (I := I) (M := M) g 2
        (appCcRS (I := I) (M := M) g p r c Φ W) ≤
      C * lowJetSq (I := I) (M := M) g 2 Φ *
        lowJetSq (I := I) (M := M) g 2 W := happ
    _ ≤ C * (A * X ^ n) *
        lowJetSq (I := I) (M := M) g 2 W := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hΦ.2 hC)
        (jet_nonneg (I := I) (M := M) (m := 2) g W)
    _ ≤ C * (A * X ^ n) * (B * X ^ m) := by
      exact mul_le_mul_of_nonneg_left hW.2
        (mul_nonneg hC (mul_nonneg hΦ.1 (pow_nonneg hX n)))
    _ = (C * A * B) *
        (1 + lowJetSq (I := I) (M := M) g 3 P) ^ (n + m) := by
      rw [pow_add]
      simp only [X]
      ring

private def ricPerm3201 : Equiv.Perm (Fin 4) :=
  ⟨![3, 2, 0, 1], ![2, 3, 1, 0], by decide, by decide⟩

private def ricPerm2301 : Equiv.Perm (Fin 4) :=
  ⟨![2, 3, 0, 1], ![2, 3, 0, 1], by decide, by decide⟩

private def ricPerm3102 : Equiv.Perm (Fin 4) :=
  ⟨![3, 1, 0, 2], ![2, 1, 3, 0], by decide, by decide⟩

private def ricPerm1302 : Equiv.Perm (Fin 4) :=
  ⟨![1, 3, 0, 2], ![2, 0, 3, 1], by decide, by decide⟩

private def ricPerm1203 : Equiv.Perm (Fin 4) :=
  ⟨![1, 2, 0, 3], ![2, 0, 1, 3], by decide, by decide⟩

private def ricPerm2103 : Equiv.Perm (Fin 4) :=
  ⟨![2, 1, 0, 3], ![2, 1, 0, 3], by decide, by decide⟩

private def ricPerm102 : Equiv.Perm (Fin 3) :=
  ⟨![1, 0, 2], ![1, 0, 2], by decide, by decide⟩

private def ricPerm120 : Equiv.Perm (Fin 3) :=
  ⟨![1, 2, 0], ![2, 0, 1], by decide, by decide⟩

private def aa0
    (g g₁ : SmoothRiemannianMetric I M) :
    SmoothCcTensor g 2 4 :=
  appCcRS (I := I) (M := M) g 2 4 4
      (permCoeff (I := I) (M := M) g ricPerm3201)
    (appCcRS (I := I) (M := M) g 2 3 4
      (connDiffContrInsertionField (I := I) g g₁)
      (appCcRS (I := I) (M := M) g 2 3 3
        (permCoeff (I := I) (M := M) g ricPerm102)
        (connDiffContrInsertionInnerField (I := I) g g₁)))

private def aa1
    (g g₁ : SmoothRiemannianMetric I M) :
    SmoothCcTensor g 2 4 :=
  reindexCoeffGen (I := I) (M := M) g 2 4
    (appCcRS (I := I) (M := M) g 2 4 4
      (permCoeff (I := I) (M := M) g ricPerm2301)
      (appCcRS (I := I) (M := M) g 2 3 4
        (connDiffContrInsertionField (I := I) g g₁)
        (appCcRS (I := I) (M := M) g 2 3 3
          (permCoeff (I := I) (M := M) g ricPerm102)
          (connDiffContrInsertionInnerField (I := I) g g₁))))
    innerCoreInPerm10

private def aa2
    (g g₁ : SmoothRiemannianMetric I M) :
    SmoothCcTensor g 2 4 :=
  appCcRS (I := I) (M := M) g 2 4 4
      (permCoeff (I := I) (M := M) g ricPerm3102)
    (appCcRS (I := I) (M := M) g 2 3 4
      (connDiffContrInsertionField (I := I) g g₁)
      (appCcRS (I := I) (M := M) g 2 3 3
        (permCoeff (I := I) (M := M) g ricPerm120)
        (connDiffContrInsertionInnerField (I := I) g g₁)))

private def aa3
    (g g₁ : SmoothRiemannianMetric I M) :
    SmoothCcTensor g 2 4 :=
  reindexCoeffGen (I := I) (M := M) g 2 4
    (appCcRS (I := I) (M := M) g 2 4 4
      (permCoeff (I := I) (M := M) g ricPerm1302)
      (appCcRS (I := I) (M := M) g 2 3 4
        (connDiffContrInsertionField (I := I) g g₁)
        (connDiffContrInsertionInnerField (I := I) g g₁)))
    innerCoreInPerm10

private def aa4
    (g g₁ : SmoothRiemannianMetric I M) :
    SmoothCcTensor g 2 4 :=
  appCcRS (I := I) (M := M) g 2 4 4
      (permCoeff (I := I) (M := M) g ricPerm1203)
    (appCcRS (I := I) (M := M) g 2 3 4
      (connDiffContrInsertionField (I := I) g g₁)
      (connDiffContrInsertionInnerField (I := I) g g₁))

private def aa5
    (g g₁ : SmoothRiemannianMetric I M) :
    SmoothCcTensor g 2 4 :=
  reindexCoeffGen (I := I) (M := M) g 2 4
    (appCcRS (I := I) (M := M) g 2 4 4
      (permCoeff (I := I) (M := M) g ricPerm2103)
      (appCcRS (I := I) (M := M) g 2 3 4
        (connDiffContrInsertionField (I := I) g g₁)
        (appCcRS (I := I) (M := M) g 2 3 3
          (permCoeff (I := I) (M := M) g ricPerm120)
          (connDiffContrInsertionInnerField (I := I) g g₁))))
    innerCoreInPerm10

set_option maxHeartbeats 800000 in
private theorem aaKer_eq
    (g g₁ : SmoothRiemannianMetric I M) :
    ricciAAKer (I := I) (M := M) g g₁ =
      aa0 (I := I) (M := M) g g₁ +
      aa1 (I := I) (M := M) g g₁ +
      aa2 (I := I) (M := M) g g₁ +
      aa3 (I := I) (M := M) g g₁ +
      aa4 (I := I) (M := M) g g₁ +
      aa5 (I := I) (M := M) g g₁ := by
  rfl

set_option maxHeartbeats 1600000 in
set_option linter.unusedVariables false in
private theorem ricciAA_h2_rf
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀0 : 0 ≤ δ₀) (hδ₀ : δ₀ < 1) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (g₁ : SmoothRiemannianMetric I M)
        (P : SmoothCcTensor g 0 2)
        (hP : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g P x u v =
            ccTensorBilin (I := I) g P x v u)
        (htie : ∀ (x : M) (u v : TangentSpace I x),
          g₁.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g P x u v)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
        (hδ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g P) δ),
      lowJetSq (I := I) (M := M) g 2
          (ricciAAArm (I := I) (M := M) g g₁) ≤
        K * (1 + lowJetSq (I := I) (M := M) g 3 P) ^ 3 := by
  classical
  obtain ⟨Kc, hKc, hconn⟩ :=
    conn_h2_rf (I := I) (M := M) g hδ₀0 hδ₀
  obtain ⟨Kt, hKt, htrace⟩ :=
    fourtrace_h2_rf (I := I) (M := M) g hδ₀0 hδ₀
  obtain ⟨C233, hC233, h233⟩ :=
    app_h2_mul (I := I) (M := M) hDim g 2 3 3
  obtain ⟨C234, hC234, h234⟩ :=
    app_h2_mul (I := I) (M := M) hDim g 2 3 4
  obtain ⟨C244, hC244, h244⟩ :=
    app_h2_mul (I := I) (M := M) hDim g 2 4 4
  obtain ⟨C242, hC242, h242⟩ :=
    app_h2_mul (I := I) (M := M) hDim g 2 4 2
  let fr : ℝ := Module.finrank ℝ E
  let Kinner : ℝ := fr * Kc
  let Kouter : ℝ := fr * (fr * Kc)
  have hfr : 0 ≤ fr := Nat.cast_nonneg _
  have hKinner : 0 ≤ Kinner :=
    mul_nonneg hfr hKc
  have hKouter : 0 ≤ Kouter :=
    mul_nonneg hfr hKinner
  let P102 : ℝ := lowJetSq (I := I) (M := M) g 2
    (permCoeff (I := I) (M := M) g ricPerm102)
  let P120 : ℝ := lowJetSq (I := I) (M := M) g 2
    (permCoeff (I := I) (M := M) g ricPerm120)
  let P3201 : ℝ := lowJetSq (I := I) (M := M) g 2
    (permCoeff (I := I) (M := M) g ricPerm3201)
  let P2301 : ℝ := lowJetSq (I := I) (M := M) g 2
    (permCoeff (I := I) (M := M) g ricPerm2301)
  let P3102 : ℝ := lowJetSq (I := I) (M := M) g 2
    (permCoeff (I := I) (M := M) g ricPerm3102)
  let P1302 : ℝ := lowJetSq (I := I) (M := M) g 2
    (permCoeff (I := I) (M := M) g ricPerm1302)
  let P1203 : ℝ := lowJetSq (I := I) (M := M) g 2
    (permCoeff (I := I) (M := M) g ricPerm1203)
  let P2103 : ℝ := lowJetSq (I := I) (M := M) g 2
    (permCoeff (I := I) (M := M) g ricPerm2103)
  have hP102 : 0 ≤ P102 := by
    exact jet_nonneg (I := I) (M := M) (m := 2) g _
  have hP120 : 0 ≤ P120 := by
    exact jet_nonneg (I := I) (M := M) (m := 2) g _
  have hP3201 : 0 ≤ P3201 := by
    exact jet_nonneg (I := I) (M := M) (m := 2) g _
  have hP2301 : 0 ≤ P2301 := by
    exact jet_nonneg (I := I) (M := M) (m := 2) g _
  have hP3102 : 0 ≤ P3102 := by
    exact jet_nonneg (I := I) (M := M) (m := 2) g _
  have hP1302 : 0 ≤ P1302 := by
    exact jet_nonneg (I := I) (M := M) (m := 2) g _
  have hP1203 : 0 ≤ P1203 := by
    exact jet_nonneg (I := I) (M := M) (m := 2) g _
  have hP2103 : 0 ≤ P2103 := by
    exact jet_nonneg (I := I) (M := M) (m := 2) g _
  let K102 : ℝ := C233 * P102 * Kinner
  let K120 : ℝ := C233 * P120 * Kinner
  let Kcore0 : ℝ := C234 * Kouter * K102
  let Kcore2 : ℝ := C234 * Kouter * K120
  let Kcore3 : ℝ := C234 * Kouter * Kinner
  let K0 : ℝ := C244 * P3201 * Kcore0
  let K1 : ℝ := C244 * P2301 * Kcore0
  let K2 : ℝ := C244 * P3102 * Kcore2
  let K3 : ℝ := C244 * P1302 * Kcore3
  let K4 : ℝ := C244 * P1203 * Kcore3
  let K5 : ℝ := C244 * P2103 * Kcore2
  let K01 : ℝ := 2 * (K0 + K1)
  let K012 : ℝ := 2 * (K01 + K2)
  let K0123 : ℝ := 2 * (K012 + K3)
  let K01234 : ℝ := 2 * (K0123 + K4)
  let Kker : ℝ := 2 * (K01234 + K5)
  let Kout : ℝ := C242 * Kt * Kker
  have hK102 : 0 ≤ K102 :=
    mul_nonneg (mul_nonneg hC233 hP102) hKinner
  have hK120 : 0 ≤ K120 :=
    mul_nonneg (mul_nonneg hC233 hP120) hKinner
  have hKcore0 : 0 ≤ Kcore0 :=
    mul_nonneg (mul_nonneg hC234 hKouter) hK102
  have hKcore2 : 0 ≤ Kcore2 :=
    mul_nonneg (mul_nonneg hC234 hKouter) hK120
  have hKcore3 : 0 ≤ Kcore3 :=
    mul_nonneg (mul_nonneg hC234 hKouter) hKinner
  have hK0 : 0 ≤ K0 :=
    mul_nonneg (mul_nonneg hC244 hP3201) hKcore0
  have hK1 : 0 ≤ K1 :=
    mul_nonneg (mul_nonneg hC244 hP2301) hKcore0
  have hK2 : 0 ≤ K2 :=
    mul_nonneg (mul_nonneg hC244 hP3102) hKcore2
  have hK3 : 0 ≤ K3 :=
    mul_nonneg (mul_nonneg hC244 hP1302) hKcore3
  have hK4 : 0 ≤ K4 :=
    mul_nonneg (mul_nonneg hC244 hP1203) hKcore3
  have hK5 : 0 ≤ K5 :=
    mul_nonneg (mul_nonneg hC244 hP2103) hKcore2
  have hK01 : 0 ≤ K01 :=
    mul_nonneg (by norm_num) (add_nonneg hK0 hK1)
  have hK012 : 0 ≤ K012 :=
    mul_nonneg (by norm_num) (add_nonneg hK01 hK2)
  have hK0123 : 0 ≤ K0123 :=
    mul_nonneg (by norm_num) (add_nonneg hK012 hK3)
  have hK01234 : 0 ≤ K01234 :=
    mul_nonneg (by norm_num) (add_nonneg hK0123 hK4)
  have hKker : 0 ≤ Kker :=
    mul_nonneg (by norm_num) (add_nonneg hK01234 hK5)
  have hKout : 0 ≤ Kout :=
    mul_nonneg (mul_nonneg hC242 hKt) hKker
  refine ⟨Kout, hKout, ?_⟩
  intro g₁ P hP htie δ hδ_le hδ0 hδ
  have hc :
      H2Poly (I := I) (M := M) g P 1 Kc
        (connDiffSection (I := I) g₁ g) := by
    refine ⟨hKc, ?_⟩
    simpa only [H2Poly, pow_one] using
      hconn g₁ P hP htie hδ_le hδ0 hδ
  have hinner :
      H2Poly (I := I) (M := M) g P 1 Kinner
        (connDiffContrInsertionInnerField (I := I) g g₁) := by
    have hs := hp_slot (I := I) (M := M) g P hc
    have hr := hp_reindex (I := I) (M := M) g P
      innerCoreInPerm10 hs
    simpa only [Kinner, fr,
      connDiffContrInsertionInnerField_eq_reindex_slotExtend] using hr
  have houter :
      H2Poly (I := I) (M := M) g P 1 Kouter
        (connDiffContrInsertionField (I := I) g g₁) := by
    have hs1 := hp_slot (I := I) (M := M) g P hc
    have hs2 := hp_slot (I := I) (M := M) g P hs1
    have hr := hp_reindex (I := I) (M := M) g P
      coreInPerm201 hs2
    simpa only [Kouter, fr, mul_assoc,
      connDiffContrInsertionField_eq_reindex_slotExtend_two] using hr
  have hp102 :
      H2Poly (I := I) (M := M) g P 0 P102
        (permCoeff (I := I) (M := M) g ricPerm102) := by
    simpa only [P102] using hp_const (I := I) (M := M) g P
      (permCoeff (I := I) (M := M) g ricPerm102)
  have hp120 :
      H2Poly (I := I) (M := M) g P 0 P120
        (permCoeff (I := I) (M := M) g ricPerm120) := by
    simpa only [P120] using hp_const (I := I) (M := M) g P
      (permCoeff (I := I) (M := M) g ricPerm120)
  have h102 :
      H2Poly (I := I) (M := M) g P 1 K102
        (appCcRS (I := I) (M := M) g 2 3 3
          (permCoeff (I := I) (M := M) g ricPerm102)
          (connDiffContrInsertionInnerField (I := I) g g₁)) := by
    simpa only [K102, Nat.zero_add] using
      hp_app_of (I := I) (M := M) g P C233 hC233
        (h233 _ _) hp102 hinner
  have h120 :
      H2Poly (I := I) (M := M) g P 1 K120
        (appCcRS (I := I) (M := M) g 2 3 3
          (permCoeff (I := I) (M := M) g ricPerm120)
          (connDiffContrInsertionInnerField (I := I) g g₁)) := by
    simpa only [K120, Nat.zero_add] using
      hp_app_of (I := I) (M := M) g P C233 hC233
        (h233 _ _) hp120 hinner
  have hcore0 :
      H2Poly (I := I) (M := M) g P 2 Kcore0
        (appCcRS (I := I) (M := M) g 2 3 4
          (connDiffContrInsertionField (I := I) g g₁)
          (appCcRS (I := I) (M := M) g 2 3 3
            (permCoeff (I := I) (M := M) g ricPerm102)
            (connDiffContrInsertionInnerField (I := I) g g₁))) := by
    simpa only [Kcore0, Nat.reduceAdd] using
      hp_app_of (I := I) (M := M) g P C234 hC234
        (h234 _ _) houter h102
  have hcore2 :
      H2Poly (I := I) (M := M) g P 2 Kcore2
        (appCcRS (I := I) (M := M) g 2 3 4
          (connDiffContrInsertionField (I := I) g g₁)
          (appCcRS (I := I) (M := M) g 2 3 3
            (permCoeff (I := I) (M := M) g ricPerm120)
            (connDiffContrInsertionInnerField (I := I) g g₁))) := by
    simpa only [Kcore2, Nat.reduceAdd] using
      hp_app_of (I := I) (M := M) g P C234 hC234
        (h234 _ _) houter h120
  have hcore3 :
      H2Poly (I := I) (M := M) g P 2 Kcore3
        (appCcRS (I := I) (M := M) g 2 3 4
          (connDiffContrInsertionField (I := I) g g₁)
          (connDiffContrInsertionInnerField (I := I) g g₁)) := by
    simpa only [Kcore3, Nat.reduceAdd] using
      hp_app_of (I := I) (M := M) g P C234 hC234
        (h234 _ _) houter hinner
  have hp3201 :
      H2Poly (I := I) (M := M) g P 0 P3201
        (permCoeff (I := I) (M := M) g ricPerm3201) := by
    simpa only [P3201] using hp_const (I := I) (M := M) g P _
  have hp2301 :
      H2Poly (I := I) (M := M) g P 0 P2301
        (permCoeff (I := I) (M := M) g ricPerm2301) := by
    simpa only [P2301] using hp_const (I := I) (M := M) g P _
  have hp3102 :
      H2Poly (I := I) (M := M) g P 0 P3102
        (permCoeff (I := I) (M := M) g ricPerm3102) := by
    simpa only [P3102] using hp_const (I := I) (M := M) g P _
  have hp1302 :
      H2Poly (I := I) (M := M) g P 0 P1302
        (permCoeff (I := I) (M := M) g ricPerm1302) := by
    simpa only [P1302] using hp_const (I := I) (M := M) g P _
  have hp1203 :
      H2Poly (I := I) (M := M) g P 0 P1203
        (permCoeff (I := I) (M := M) g ricPerm1203) := by
    simpa only [P1203] using hp_const (I := I) (M := M) g P _
  have hp2103 :
      H2Poly (I := I) (M := M) g P 0 P2103
        (permCoeff (I := I) (M := M) g ricPerm2103) := by
    simpa only [P2103] using hp_const (I := I) (M := M) g P _
  have h0 :
      H2Poly (I := I) (M := M) g P 2 K0
        (aa0 (I := I) (M := M) g g₁) := by
    simpa only [K0, aa0, Nat.zero_add] using
      hp_app_of (I := I) (M := M) g P C244 hC244
        (h244 _ _) hp3201 hcore0
  have h1r :=
    hp_app_of (I := I) (M := M) g P C244 hC244
      (h244 _ _) hp2301 hcore0
  have h1 :
      H2Poly (I := I) (M := M) g P 2 K1
        (aa1 (I := I) (M := M) g g₁) := by
    have hr := hp_reindex (I := I) (M := M) g P
      innerCoreInPerm10 h1r
    simpa only [K1, aa1, Nat.zero_add] using hr
  have h2 :
      H2Poly (I := I) (M := M) g P 2 K2
        (aa2 (I := I) (M := M) g g₁) := by
    simpa only [K2, aa2, Nat.zero_add] using
      hp_app_of (I := I) (M := M) g P C244 hC244
        (h244 _ _) hp3102 hcore2
  have h3r :=
    hp_app_of (I := I) (M := M) g P C244 hC244
      (h244 _ _) hp1302 hcore3
  have h3 :
      H2Poly (I := I) (M := M) g P 2 K3
        (aa3 (I := I) (M := M) g g₁) := by
    have hr := hp_reindex (I := I) (M := M) g P
      innerCoreInPerm10 h3r
    simpa only [K3, aa3, Nat.zero_add] using hr
  have h4 :
      H2Poly (I := I) (M := M) g P 2 K4
        (aa4 (I := I) (M := M) g g₁) := by
    simpa only [K4, aa4, Nat.zero_add] using
      hp_app_of (I := I) (M := M) g P C244 hC244
        (h244 _ _) hp1203 hcore3
  have h5r :=
    hp_app_of (I := I) (M := M) g P C244 hC244
      (h244 _ _) hp2103 hcore2
  have h5 :
      H2Poly (I := I) (M := M) g P 2 K5
        (aa5 (I := I) (M := M) g g₁) := by
    have hr := hp_reindex (I := I) (M := M) g P
      innerCoreInPerm10 h5r
    simpa only [K5, aa5, Nat.zero_add] using hr
  have h01 :
      H2Poly (I := I) (M := M) g P 2 K01
        (aa0 (I := I) (M := M) g g₁ +
          aa1 (I := I) (M := M) g g₁) := by
    simpa only [K01] using hp_add (I := I) (M := M) g P h0 h1
  have h012 :
      H2Poly (I := I) (M := M) g P 2 K012
        (aa0 (I := I) (M := M) g g₁ +
          aa1 (I := I) (M := M) g g₁ +
          aa2 (I := I) (M := M) g g₁) := by
    simpa only [K012] using hp_add (I := I) (M := M) g P h01 h2
  have h0123 :
      H2Poly (I := I) (M := M) g P 2 K0123
        (aa0 (I := I) (M := M) g g₁ +
          aa1 (I := I) (M := M) g g₁ +
          aa2 (I := I) (M := M) g g₁ +
          aa3 (I := I) (M := M) g g₁) := by
    simpa only [K0123] using hp_add (I := I) (M := M) g P h012 h3
  have h01234 :
      H2Poly (I := I) (M := M) g P 2 K01234
        (aa0 (I := I) (M := M) g g₁ +
          aa1 (I := I) (M := M) g g₁ +
          aa2 (I := I) (M := M) g g₁ +
          aa3 (I := I) (M := M) g g₁ +
          aa4 (I := I) (M := M) g g₁) := by
    simpa only [K01234] using hp_add (I := I) (M := M) g P h0123 h4
  have hk :
      H2Poly (I := I) (M := M) g P 2 Kker
        (ricciAAKer (I := I) (M := M) g g₁) := by
    have hsum := hp_add (I := I) (M := M) g P h01234 h5
    rw [← aaKer_eq (I := I) (M := M) g g₁] at hsum
    simpa only [Kker] using hsum
  have ht :
      H2Poly (I := I) (M := M) g P 1 Kt
        (ricciCometricFourTraceCastG0 (I := I) g g₁) := by
    refine ⟨hKt, ?_⟩
    have hraw := htrace g₁ P hP htie hδ_le hδ0 hδ
    have h23 := jet_mono (I := I) (M := M) g
      (by omega : 2 ≤ 3) P
    calc
      lowJetSq (I := I) (M := M) g 2
          (ricciCometricFourTraceCastG0 (I := I) g g₁) ≤
        Kt * (1 + lowJetSq (I := I) (M := M) g 2 P) := hraw
      _ ≤ Kt * (1 + lowJetSq (I := I) (M := M) g 3 P) :=
        mul_le_mul_of_nonneg_left (by linarith) hKt
      _ = Kt * (1 + lowJetSq (I := I) (M := M) g 3 P) ^ 1 := by
        rw [pow_one]
  have hout :=
    hp_app_of (I := I) (M := M) g P C242 hC242
      (h242 _ _) ht hk
  simpa only [Kout, ricciAAArm, Nat.reduceAdd] using hout.2

private theorem grad_l2_sq
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

private theorem grad_h2_le_h3
    (g : SmoothRiemannianMetric I M) {r s : ℕ}
    (S : SmoothCcTensor g r s) :
    lowJetSq (I := I) (M := M) g 2
        (covGrad (I := I) (M := M) g r s S) ≤
      lowJetSq (I := I) (M := M) g 3 S := by
  have h0 := grad_l2_sq (I := I) (M := M) g r s 0 S
  have h1 := grad_l2_sq (I := I) (M := M) g r s 1 S
  have h2 := grad_l2_sq (I := I) (M := M) g r s 2 S
  unfold lowJetSq
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    Nat.reduceAdd] at h0 h1 h2 ⊢
  rw [h0, h1, h2]
  nlinarith [sq_nonneg ‖S‖]

private theorem jet3_le_grad2
    (g : SmoothRiemannianMetric I M) {r s : ℕ}
    (S : SmoothCcTensor g r s) :
    lowJetSq (I := I) (M := M) g 3 S ≤
      lowJetSq (I := I) (M := M) g 2 S +
        lowJetSq (I := I) (M := M) g 2
          (covGrad (I := I) (M := M) g r s S) := by
  have h0 := grad_l2_sq (I := I) (M := M) g r s 0 S
  have h1 := grad_l2_sq (I := I) (M := M) g r s 1 S
  have h2 := grad_l2_sq (I := I) (M := M) g r s 2 S
  unfold lowJetSq
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    Nat.reduceAdd] at h0 h1 h2 ⊢
  rw [h0, h1, h2]
  nlinarith [sq_nonneg
    ‖iteratedCovGrad (I := I) g r s 1 S‖,
    sq_nonneg ‖iteratedCovGrad (I := I) g r s 2 S‖]

set_option maxHeartbeats 1600000 in
private theorem app_h3_mul
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) (p r c : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (Φ : SmoothCcTensor g r c) (W : SmoothCcTensor g p r),
        lowJetSq (I := I) (M := M) g 3
            (appCcRS (I := I) (M := M) g p r c Φ W) ≤
          C * lowJetSq (I := I) (M := M) g 3 Φ *
            lowJetSq (I := I) (M := M) g 3 W := by
  obtain ⟨C0, hC0, h0⟩ :=
    app_h2_mul (I := I) (M := M) hDim g p r c
  obtain ⟨C1, hC1, h1⟩ :=
    app_h2_mul (I := I) (M := M) hDim g p r (c + 1)
  obtain ⟨C2, hC2, h2⟩ :=
    app_h2_mul (I := I) (M := M) hDim g p (r + 1) (c + 1)
  let fr : ℝ := Module.finrank ℝ E
  let C : ℝ := C0 + 2 * (C1 + C2 * fr)
  have hfr : 0 ≤ fr := Nat.cast_nonneg _
  have hC : 0 ≤ C := by
    dsimp only [C]
    exact add_nonneg hC0
      (mul_nonneg (by norm_num) (add_nonneg hC1 (mul_nonneg hC2 hfr)))
  refine ⟨C, hC, ?_⟩
  intro Φ W
  let Y : SmoothCcTensor g p c :=
    appCcRS (I := I) (M := M) g p r c Φ W
  let A : SmoothCcTensor g p (c + 1) :=
    appCcRS (I := I) (M := M) g p r (c + 1)
      (covGrad (I := I) (M := M) g r c Φ) W
  let B : SmoothCcTensor g p (c + 1) :=
    appCcRS (I := I) (M := M) g p (r + 1) (c + 1)
      (slotExtend (I := I) (M := M) g r c Φ)
      (covGrad (I := I) (M := M) g p r W)
  have hΦ23 := jet_mono (I := I) (M := M) g
    (by omega : 2 ≤ 3) Φ
  have hW23 := jet_mono (I := I) (M := M) g
    (by omega : 2 ≤ 3) W
  have hΦ0 := jet_nonneg (I := I) (M := M) (m := 2) g Φ
  have hW0 := jet_nonneg (I := I) (M := M) (m := 2) g W
  have hΦ30 := jet_nonneg (I := I) (M := M) (m := 3) g Φ
  have hW30 := jet_nonneg (I := I) (M := M) (m := 3) g W
  have hY2 :
      lowJetSq (I := I) (M := M) g 2 Y ≤
        C0 * lowJetSq (I := I) (M := M) g 3 Φ *
          lowJetSq (I := I) (M := M) g 3 W := by
    calc
      lowJetSq (I := I) (M := M) g 2 Y ≤
          C0 * lowJetSq (I := I) (M := M) g 2 Φ *
            lowJetSq (I := I) (M := M) g 2 W := by
        simpa only [Y] using h0 Φ W
      _ ≤ C0 * lowJetSq (I := I) (M := M) g 3 Φ *
            lowJetSq (I := I) (M := M) g 2 W := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hΦ23 hC0) hW0
      _ ≤ C0 * lowJetSq (I := I) (M := M) g 3 Φ *
            lowJetSq (I := I) (M := M) g 3 W := by
        exact mul_le_mul_of_nonneg_left hW23 (mul_nonneg hC0 hΦ30)
  have hA2 :
      lowJetSq (I := I) (M := M) g 2 A ≤
        C1 * lowJetSq (I := I) (M := M) g 3 Φ *
          lowJetSq (I := I) (M := M) g 3 W := by
    calc
      lowJetSq (I := I) (M := M) g 2 A ≤
          C1 * lowJetSq (I := I) (M := M) g 2
              (covGrad (I := I) (M := M) g r c Φ) *
            lowJetSq (I := I) (M := M) g 2 W := by
        simpa only [A] using
          h1 (covGrad (I := I) (M := M) g r c Φ) W
      _ ≤ C1 * lowJetSq (I := I) (M := M) g 3 Φ *
            lowJetSq (I := I) (M := M) g 2 W := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left
            (grad_h2_le_h3 (I := I) (M := M) g Φ) hC1) hW0
      _ ≤ C1 * lowJetSq (I := I) (M := M) g 3 Φ *
            lowJetSq (I := I) (M := M) g 3 W := by
        exact mul_le_mul_of_nonneg_left hW23 (mul_nonneg hC1 hΦ30)
  have hB2 :
      lowJetSq (I := I) (M := M) g 2 B ≤
        (C2 * fr) * lowJetSq (I := I) (M := M) g 3 Φ *
          lowJetSq (I := I) (M := M) g 3 W := by
    calc
      lowJetSq (I := I) (M := M) g 2 B ≤
          C2 * lowJetSq (I := I) (M := M) g 2
              (slotExtend (I := I) (M := M) g r c Φ) *
            lowJetSq (I := I) (M := M) g 2
              (covGrad (I := I) (M := M) g p r W) := by
        simpa only [B] using
          h2 (slotExtend (I := I) (M := M) g r c Φ)
            (covGrad (I := I) (M := M) g p r W)
      _ ≤ C2 * (fr * lowJetSq (I := I) (M := M) g 2 Φ) *
            lowJetSq (I := I) (M := M) g 2
              (covGrad (I := I) (M := M) g p r W) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left
            (by simpa only [fr] using
              slot_h2 (I := I) (M := M) g r c Φ) hC2)
          (jet_nonneg (I := I) (M := M) (m := 2) g
            (covGrad (I := I) (M := M) g p r W))
      _ ≤ C2 * (fr * lowJetSq (I := I) (M := M) g 2 Φ) *
            lowJetSq (I := I) (M := M) g 3 W := by
        exact mul_le_mul_of_nonneg_left
          (grad_h2_le_h3 (I := I) (M := M) g W)
          (mul_nonneg hC2 (mul_nonneg hfr hΦ0))
      _ ≤ C2 * (fr * lowJetSq (I := I) (M := M) g 3 Φ) *
            lowJetSq (I := I) (M := M) g 3 W := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hΦ23 hfr) hC2) hW30
      _ = (C2 * fr) * lowJetSq (I := I) (M := M) g 3 Φ *
            lowJetSq (I := I) (M := M) g 3 W := by ring
  have hgrad :
      lowJetSq (I := I) (M := M) g 2
          (covGrad (I := I) (M := M) g p c Y) ≤
        2 * (C1 + C2 * fr) *
          lowJetSq (I := I) (M := M) g 3 Φ *
          lowJetSq (I := I) (M := M) g 3 W := by
    rw [show covGrad (I := I) (M := M) g p c Y = A + B by
      simpa only [Y, A, B] using
        covGrad_appCcRS_eq (I := I) (M := M) g p r c Φ W]
    calc
      lowJetSq (I := I) (M := M) g 2 (A + B) ≤
          2 * (lowJetSq (I := I) (M := M) g 2 A +
            lowJetSq (I := I) (M := M) g 2 B) :=
        jet_add (I := I) (M := M) g 2 A B
      _ ≤ 2 * (C1 * lowJetSq (I := I) (M := M) g 3 Φ *
              lowJetSq (I := I) (M := M) g 3 W +
            (C2 * fr) * lowJetSq (I := I) (M := M) g 3 Φ *
              lowJetSq (I := I) (M := M) g 3 W) :=
        mul_le_mul_of_nonneg_left (add_le_add hA2 hB2) (by norm_num)
      _ = 2 * (C1 + C2 * fr) *
          lowJetSq (I := I) (M := M) g 3 Φ *
          lowJetSq (I := I) (M := M) g 3 W := by ring
  calc
    lowJetSq (I := I) (M := M) g 3
        (appCcRS (I := I) (M := M) g p r c Φ W) =
      lowJetSq (I := I) (M := M) g 3 Y := rfl
    _ ≤ lowJetSq (I := I) (M := M) g 2 Y +
        lowJetSq (I := I) (M := M) g 2
          (covGrad (I := I) (M := M) g p c Y) :=
      jet3_le_grad2 (I := I) (M := M) g Y
    _ ≤ C0 * lowJetSq (I := I) (M := M) g 3 Φ *
          lowJetSq (I := I) (M := M) g 3 W +
        2 * (C1 + C2 * fr) *
          lowJetSq (I := I) (M := M) g 3 Φ *
          lowJetSq (I := I) (M := M) g 3 W :=
      add_le_add hY2 hgrad
    _ = C * lowJetSq (I := I) (M := M) g 3 Φ *
          lowJetSq (I := I) (M := M) g 3 W := by
      simp only [C]
      ring

private theorem sharp_eq_slot0
    (g g₁ : SmoothRiemannianMetric I M) :
    sharpFlatEndoCc (I := I) g g₁ =
      slotInsertEndoCc (I := I) (M := M) g 0
        (fullRaisedEndoField (I := I) (M := M) g g₁) := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply tensorRSSpace_ext 1 1 x
  intro om
  apply cotangentToDualLinear_injective (I := I) (x := x)
  apply LinearMap.ext
  intro w
  rw [cotangentToDualLinear_apply, cotangentToDualLinear_apply]
  rw [show (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
        (slotInsertEndoCc (I := I) (M := M) g 0
          (fullRaisedEndoField (I := I) (M := M) g g₁)).toSection x) om =
      slotInsertEndoFib (I := I) (M := M) 1 0 x
        (gInvRaisedEndo (I := I) g g₁ x) om from rfl]
  rw [cotangentToDual_slotInsertEndoFib' (I := I) (M := M) x
    (gInvRaisedEndo (I := I) g g₁ x) om w]
  rw [show (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
        (sharpFlatEndoCc (I := I) g g₁).toSection x) om =
      g0FlatCLM (I := I) g x (inverseMetricSharpFib (I := I) g₁ x om) from rfl]
  rw [cotangentToDual_g0FlatCLM]
  rw [show cotangentToDual (I := I) om
      (gInvRaisedEndo (I := I) g g₁ x w) =
      g₁.inner x (inverseMetricSharpFib (I := I) g₁ x om)
        (gInvRaisedEndo (I := I) g g₁ x w) from by
    rw [← cotangentToDualLinear_apply]
    exact (inverseMetricSharpFib_inner (I := I) g₁ x om
      (gInvRaisedEndo (I := I) g g₁ x w)).symm]
  rw [show gInvRaisedEndo (I := I) g g₁ x w =
      inverseMetricSharpFib (I := I) g₁ x (g0FlatCLM (I := I) g x w) from by
    rw [gInvRaisedEndo_apply]]
  rw [g₁.symm x (inverseMetricSharpFib (I := I) g₁ x om)
    (inverseMetricSharpFib (I := I) g₁ x (g0FlatCLM (I := I) g x w))]
  rw [inverseMetricSharpFib_inner (I := I) g₁ x
    (g0FlatCLM (I := I) g x w) (inverseMetricSharpFib (I := I) g₁ x om)]
  rw [cotangentToDualLinear_apply, cotangentToDual_g0FlatCLM]
  rw [g.symm x w (inverseMetricSharpFib (I := I) g₁ x om)]

set_option linter.unusedVariables false in
private theorem sharp_h3_rf
    (g : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀0 : 0 ≤ δ₀) (hδ₀ : δ₀ < 1) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (g₁ : SmoothRiemannianMetric I M)
        (P : SmoothCcTensor g 0 2)
        (hP : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g P x u v =
            ccTensorBilin (I := I) g P x v u)
        (htie : ∀ (x : M) (u v : TangentSpace I x),
          g₁.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g P x u v)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
        (hδ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g P) δ),
      lowJetSq (I := I) (M := M) g 3
          (sharpFlatEndoCc (I := I) g g₁) ≤
        K * (1 + lowJetSq (I := I) (M := M) g 3 P) := by
  classical
  let Λ₀ : ℝ := (Module.finrank ℝ E : ℝ) * δ₀
  have hΛ₀0 : 0 ≤ Λ₀ :=
    mul_nonneg (Nat.cast_nonneg _) hδ₀0
  obtain ⟨Λ, Flow, hΛ, hFlow0, hFlow⟩ :=
    sharpFlatEndoCc_lowOrder_jetL2_radiusFree
      (I := I) (M := M) g
        (2 * Module.finrank ℝ E + 10) le_rfl hδ₀ hΛ₀0
  refine ⟨Flow 3, hFlow0 3, ?_⟩
  intro g₁ P hP htie δ hδ_le hδ0 hδ
  have hsymm : symmS (I := I) (M := M) g P = P :=
    symm_eq_self (I := I) (M := M) g P hP
  have hsup : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g 0 2 x
          (P.toSection x) ≤ Λ₀ ^ 2 := by
    intro x
    rw [← hsymm]
    exact rfns_symmS_zero_le_fibreSmall
      (I := I) (M := M) g hδ₀0 P hδ_le hδ0 hδ x
  simpa only [lowJetSq, Nat.reduceAdd] using
    (hFlow g₁ P htie hδ_le hδ0 hδ hsup).2 3 (by omega)

private theorem endo_slot_l2
    (g : SmoothRiemannianMetric I M) (s i : ℕ)
    (Λ : ContMDiffSection I (E →L[ℝ] E) ∞
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)) :
    ‖iteratedCovGrad (I := I) g (s + 1) (s + 1) i
        (slotInsertEndoCc (I := I) (M := M) g s Λ)‖ ^ 2 ≤
      (Module.finrank ℝ E : ℝ) ^ s *
        ‖iteratedCovGrad (I := I) g 1 1 i
          (slotInsertEndoCc (I := I) (M := M) g 0 Λ)‖ ^ 2 := by
  let F : M → ℝ := fun x => (Module.finrank ℝ E : ℝ) ^ s *
    riemannianFiberNormSq (I := I) (M := M) g 1 (1 + i) x
      ((iteratedCovGrad (I := I) g 1 1 i
        (slotInsertEndoCc (I := I) (M := M) g 0 Λ)).toSection x)
  have hF : MeasureTheory.Integrable F
      (riemannianVolumeMeasure (I := I) (M := M) g) := by
    dsimp only [F]
    exact (integrable_riemannianFiberNormSq_toSection
      (I := I) (M := M) g 1 (1 + i)
      (iteratedCovGrad (I := I) g 1 1 i
        (slotInsertEndoCc (I := I) (M := M) g 0 Λ))).const_mul _
  have hsq := normSq_le_integral_of_pointwise_fiberNormSq_le_rs
    (I := I) (M := M) g (s + 1) ((s + 1) + i)
    (iteratedCovGrad (I := I) g (s + 1) (s + 1) i
      (slotInsertEndoCc (I := I) (M := M) g s Λ))
    F hF (fun x =>
      rfns_iteratedCovGrad_slotInsertEndoCc_le_endo
        (I := I) (M := M) g s Λ i x)
  have hint :
      (∫ x, riemannianFiberNormSq (I := I) (M := M) g 1 (1 + i) x
          ((iteratedCovGrad (I := I) g 1 1 i
            (slotInsertEndoCc (I := I) (M := M) g 0 Λ)).toSection x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g)) =
        ‖iteratedCovGrad (I := I) g 1 1 i
          (slotInsertEndoCc (I := I) (M := M) g 0 Λ)‖ ^ 2 := by
    rw [SmoothCcTensor.norm_def,
      tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs]
  dsimp only [F] at hsq
  rw [MeasureTheory.integral_const_mul, hint] at hsq
  exact hsq

private theorem endo_slot_h3
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (Λ : ContMDiffSection I (E →L[ℝ] E) ∞
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)) :
    lowJetSq (I := I) (M := M) g 3
        (slotInsertEndoCc (I := I) (M := M) g s Λ) ≤
      (Module.finrank ℝ E : ℝ) ^ s *
        lowJetSq (I := I) (M := M) g 3
          (slotInsertEndoCc (I := I) (M := M) g 0 Λ) := by
  unfold lowJetSq
  calc
    ∑ i ∈ Finset.range 4,
        ‖iteratedCovGrad (I := I) g (s + 1) (s + 1) i
          (slotInsertEndoCc (I := I) (M := M) g s Λ)‖ ^ 2 ≤
      ∑ i ∈ Finset.range 4, (Module.finrank ℝ E : ℝ) ^ s *
        ‖iteratedCovGrad (I := I) g 1 1 i
          (slotInsertEndoCc (I := I) (M := M) g 0 Λ)‖ ^ 2 :=
      Finset.sum_le_sum fun i _ =>
        endo_slot_l2 (I := I) (M := M) g s i Λ
    _ = (Module.finrank ℝ E : ℝ) ^ s *
        ∑ i ∈ Finset.range 4,
          ‖iteratedCovGrad (I := I) g 1 1 i
            (slotInsertEndoCc (I := I) (M := M) g 0 Λ)‖ ^ 2 := by
      rw [Finset.mul_sum]

set_option linter.unusedVariables false in
private theorem full_slot_h3_rf
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    {δ₀ : ℝ} (hδ₀0 : 0 ≤ δ₀) (hδ₀ : δ₀ < 1) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (g₁ : SmoothRiemannianMetric I M)
        (P : SmoothCcTensor g 0 2)
        (hP : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g P x u v =
            ccTensorBilin (I := I) g P x v u)
        (htie : ∀ (x : M) (u v : TangentSpace I x),
          g₁.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g P x u v)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
        (hδ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g P) δ),
      lowJetSq (I := I) (M := M) g 3
          (slotInsertEndoCc (I := I) (M := M) g s
            (fullRaisedEndoField (I := I) (M := M) g g₁)) ≤
        K * (1 + lowJetSq (I := I) (M := M) g 3 P) := by
  obtain ⟨K₀, hK₀, hsharp⟩ :=
    sharp_h3_rf (I := I) (M := M) g hδ₀0 hδ₀
  let fr : ℝ := Module.finrank ℝ E
  let K : ℝ := fr ^ s * K₀
  have hfr : 0 ≤ fr := Nat.cast_nonneg _
  have hK : 0 ≤ K := mul_nonneg (pow_nonneg hfr s) hK₀
  refine ⟨K, hK, ?_⟩
  intro g₁ P hP htie δ hδ_le hδ0 hδ
  calc
    lowJetSq (I := I) (M := M) g 3
        (slotInsertEndoCc (I := I) (M := M) g s
          (fullRaisedEndoField (I := I) (M := M) g g₁)) ≤
      fr ^ s * lowJetSq (I := I) (M := M) g 3
        (slotInsertEndoCc (I := I) (M := M) g 0
          (fullRaisedEndoField (I := I) (M := M) g g₁)) := by
      simpa only [fr] using endo_slot_h3 (I := I) (M := M) g s
        (fullRaisedEndoField (I := I) (M := M) g g₁)
    _ = fr ^ s * lowJetSq (I := I) (M := M) g 3
        (sharpFlatEndoCc (I := I) g g₁) := by
      rw [sharp_eq_slot0 (I := I) (M := M) g g₁]
    _ ≤ fr ^ s * (K₀ *
        (1 + lowJetSq (I := I) (M := M) g 3 P)) :=
      mul_le_mul_of_nonneg_left
        (hsharp g₁ P hP htie hδ_le hδ0 hδ) (pow_nonneg hfr s)
    _ = K * (1 + lowJetSq (I := I) (M := M) g 3 P) := by
      simp only [K]
      ring

private def H3Poly
    (g : SmoothRiemannianMetric I M) (P : SmoothCcTensor g 0 2)
    {r s : ℕ} (n : ℕ) (K : ℝ) (S : SmoothCcTensor g r s) : Prop :=
  0 ≤ K ∧
    lowJetSq (I := I) (M := M) g 3 S ≤
      K * (1 + lowJetSq (I := I) (M := M) g 3 P) ^ n

omit [BoundarylessManifold I M] in
private theorem h3p_const
    (g : SmoothRiemannianMetric I M) (P : SmoothCcTensor g 0 2)
    {r s : ℕ} (S : SmoothCcTensor g r s) :
    H3Poly (I := I) (M := M) g P 0
      (lowJetSq (I := I) (M := M) g 3 S) S := by
  refine ⟨jet_nonneg (I := I) (M := M) (m := 3) g S, ?_⟩
  rw [pow_zero, mul_one]

set_option linter.unusedVariables false in
private theorem h3p_app_of
    (g : SmoothRiemannianMetric I M) (P : SmoothCcTensor g 0 2)
    {p r c n m : ℕ} {A B : ℝ}
    {Φ : SmoothCcTensor g r c} {W : SmoothCcTensor g p r}
    (C : ℝ) (hC : 0 ≤ C)
    (happ : lowJetSq (I := I) (M := M) g 3
          (appCcRS (I := I) (M := M) g p r c Φ W) ≤
        C * lowJetSq (I := I) (M := M) g 3 Φ *
          lowJetSq (I := I) (M := M) g 3 W)
    (hΦ : H3Poly (I := I) (M := M) g P n A Φ)
    (hW : H3Poly (I := I) (M := M) g P m B W) :
    H3Poly (I := I) (M := M) g P (n + m) (C * A * B)
      (appCcRS (I := I) (M := M) g p r c Φ W) := by
  let X : ℝ := 1 + lowJetSq (I := I) (M := M) g 3 P
  have hX : 0 ≤ X := by
    dsimp only [X]
    linarith [jet_nonneg (I := I) (M := M) (m := 3) g P]
  refine ⟨mul_nonneg (mul_nonneg hC hΦ.1) hW.1, ?_⟩
  calc
    lowJetSq (I := I) (M := M) g 3
        (appCcRS (I := I) (M := M) g p r c Φ W) ≤
      C * lowJetSq (I := I) (M := M) g 3 Φ *
        lowJetSq (I := I) (M := M) g 3 W := happ
    _ ≤ C * (A * X ^ n) *
        lowJetSq (I := I) (M := M) g 3 W := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hΦ.2 hC)
        (jet_nonneg (I := I) (M := M) (m := 3) g W)
    _ ≤ C * (A * X ^ n) * (B * X ^ m) := by
      exact mul_le_mul_of_nonneg_left hW.2
        (mul_nonneg hC (mul_nonneg hΦ.1 (pow_nonneg hX n)))
    _ = (C * A * B) *
        (1 + lowJetSq (I := I) (M := M) g 3 P) ^ (n + m) := by
      rw [pow_add]
      simp only [X]
      ring

set_option maxHeartbeats 1600000 in
set_option linter.unusedVariables false in
private theorem connLow_h3_rf
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀0 : 0 ≤ δ₀) (hδ₀ : δ₀ < 1) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (g₁ : SmoothRiemannianMetric I M)
        (P : SmoothCcTensor g 0 2)
        (hP : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g P x u v =
            ccTensorBilin (I := I) g P x v u)
        (htie : ∀ (x : M) (u v : TangentSpace I x),
          g₁.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g P x u v)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
        (hδ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g P) δ),
      lowJetSq (I := I) (M := M) g 3
          (connLowOp (I := I) (M := M) g g₁) ≤
        K * (1 + lowJetSq (I := I) (M := M) g 3 P) := by
  obtain ⟨Ks, hKs, hslot⟩ :=
    full_slot_h3_rf (I := I) (M := M) g 2 hδ₀0 hδ₀
  obtain ⟨C, hC, happ⟩ :=
    app_h3_mul (I := I) (M := M) hDim g 3 3 3
  let Kk : ℝ := lowJetSq (I := I) (M := M) g 3
    (koszulOp (I := I) (M := M) g)
  let Kp : ℝ := lowJetSq (I := I) (M := M) g 3
    (permCoeff (I := I) (M := M) g lowPerm)
  let Ki : ℝ := C * Ks * Kk
  let K : ℝ := C * Kp * Ki
  have hKk : 0 ≤ Kk := jet_nonneg (I := I) (M := M) (m := 3) g _
  have hKp : 0 ≤ Kp := jet_nonneg (I := I) (M := M) (m := 3) g _
  have hKi : 0 ≤ Ki := mul_nonneg (mul_nonneg hC hKs) hKk
  have hK : 0 ≤ K := mul_nonneg (mul_nonneg hC hKp) hKi
  refine ⟨K, hK, ?_⟩
  intro g₁ P hP htie δ hδ_le hδ0 hδ
  have hs :
      H3Poly (I := I) (M := M) g P 1 Ks
        (slotInsertEndoCc (I := I) (M := M) g 2
          (fullRaisedEndoField (I := I) (M := M) g g₁)) := by
    refine ⟨hKs, ?_⟩
    simpa only [H3Poly, pow_one] using
      hslot g₁ P hP htie hδ_le hδ0 hδ
  have hk :
      H3Poly (I := I) (M := M) g P 0 Kk
        (koszulOp (I := I) (M := M) g) := by
    simpa only [Kk] using h3p_const (I := I) (M := M) g P
      (koszulOp (I := I) (M := M) g)
  have hi :
      H3Poly (I := I) (M := M) g P 1 Ki
        (appCcRS (I := I) (M := M) g 3 3 3
          (slotInsertEndoCc (I := I) (M := M) g 2
            (fullRaisedEndoField (I := I) (M := M) g g₁))
          (koszulOp (I := I) (M := M) g)) := by
    simpa only [Ki, Nat.reduceAdd] using
      h3p_app_of (I := I) (M := M) g P C hC (happ _ _) hs hk
  have hp :
      H3Poly (I := I) (M := M) g P 0 Kp
        (permCoeff (I := I) (M := M) g lowPerm) := by
    simpa only [Kp] using h3p_const (I := I) (M := M) g P
      (permCoeff (I := I) (M := M) g lowPerm)
  have hout :=
    h3p_app_of (I := I) (M := M) g P C hC (happ _ _) hp hi
  simpa only [K, connLowOp, Nat.zero_add, H3Poly, pow_one] using hout.2

set_option maxHeartbeats 1600000 in
set_option linter.unusedVariables false in
private theorem dagLow_h2_rf
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀0 : 0 ≤ δ₀) (hδ₀ : δ₀ < 1) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (g₁ : SmoothRiemannianMetric I M)
        (P : SmoothCcTensor g 0 2)
        (hP : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g P x u v =
            ccTensorBilin (I := I) g P x v u)
        (htie : ∀ (x : M) (u v : TangentSpace I x),
          g₁.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g P x u v)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
        (hδ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g P) δ),
      lowJetSq (I := I) (M := M) g 2
          (dagLowOp (I := I) (M := M) g g₁) ≤
        K * (1 + lowJetSq (I := I) (M := M) g 3 P) := by
  obtain ⟨Kc, hKc, hconn⟩ :=
    connLow_h3_rf (I := I) (M := M) hDim g hδ₀0 hδ₀
  obtain ⟨C, hC, happ⟩ :=
    app_h2_mul (I := I) (M := M) hDim g 3 4 4
  let Kp : ℝ := lowJetSq (I := I) (M := M) g 2
    (permCoeff (I := I) (M := M) g daPermA)
  let K : ℝ := C * Kp * Kc
  have hKp : 0 ≤ Kp := jet_nonneg (I := I) (M := M) (m := 2) g _
  have hK : 0 ≤ K := mul_nonneg (mul_nonneg hC hKp) hKc
  refine ⟨K, hK, ?_⟩
  intro g₁ P hP htie δ hδ_le hδ0 hδ
  have hp :
      H2Poly (I := I) (M := M) g P 0 Kp
        (permCoeff (I := I) (M := M) g daPermA) := by
    simpa only [Kp] using hp_const (I := I) (M := M) g P
      (permCoeff (I := I) (M := M) g daPermA)
  have hg :
      H2Poly (I := I) (M := M) g P 1 Kc
        (covGrad (I := I) (M := M) g 3 3
          (connLowOp (I := I) (M := M) g g₁)) := by
    refine ⟨hKc, ?_⟩
    calc
      lowJetSq (I := I) (M := M) g 2
          (covGrad (I := I) (M := M) g 3 3
            (connLowOp (I := I) (M := M) g g₁)) ≤
        lowJetSq (I := I) (M := M) g 3
          (connLowOp (I := I) (M := M) g g₁) :=
        grad_h2_le_h3 (I := I) (M := M) g _
      _ ≤ Kc * (1 + lowJetSq (I := I) (M := M) g 3 P) :=
        hconn g₁ P hP htie hδ_le hδ0 hδ
      _ = Kc * (1 + lowJetSq (I := I) (M := M) g 3 P) ^ 1 := by
        rw [pow_one]
  have hout :=
    hp_app_of (I := I) (M := M) g P C hC (happ _ _) hp hg
  simpa only [K, dagLowOp, Nat.zero_add, H2Poly, pow_one] using hout.2

private theorem gradP_hp
    (g : SmoothRiemannianMetric I M) (P : SmoothCcTensor g 0 2) :
    H2Poly (I := I) (M := M) g P 1 1
      (covGrad (I := I) (M := M) g 0 2 P) := by
  refine ⟨by norm_num, ?_⟩
  rw [one_mul, pow_one]
  calc
    lowJetSq (I := I) (M := M) g 2
        (covGrad (I := I) (M := M) g 0 2 P) ≤
      lowJetSq (I := I) (M := M) g 3 P :=
      grad_h2_le_h3 (I := I) (M := M) g P
    _ ≤ 1 + lowJetSq (I := I) (M := M) g 3 P := by linarith

set_option maxHeartbeats 1600000 in
set_option linter.unusedVariables false in
private theorem dagAct_h2_rf
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀0 : 0 ≤ δ₀) (hδ₀ : δ₀ < 1) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (g₁ : SmoothRiemannianMetric I M)
        (P : SmoothCcTensor g 0 2)
        (hP : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g P x u v =
            ccTensorBilin (I := I) g P x v u)
        (htie : ∀ (x : M) (u v : TangentSpace I x),
          g₁.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g P x u v)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
        (hδ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g P) δ),
      lowJetSq (I := I) (M := M) g 2
          (appCcRS (I := I) (M := M) g 0 3 4
            (dagLowOp (I := I) (M := M) g g₁)
            (covGrad (I := I) (M := M) g 0 2 P)) ≤
        K * (1 + lowJetSq (I := I) (M := M) g 3 P) ^ 2 := by
  obtain ⟨Kd, hKd, hdag⟩ :=
    dagLow_h2_rf (I := I) (M := M) hDim g hδ₀0 hδ₀
  obtain ⟨C, hC, happ⟩ :=
    app_h2_mul (I := I) (M := M) hDim g 0 3 4
  let K : ℝ := C * Kd
  have hK : 0 ≤ K := mul_nonneg hC hKd
  refine ⟨K, hK, ?_⟩
  intro g₁ P hP htie δ hδ_le hδ0 hδ
  have hd :
      H2Poly (I := I) (M := M) g P 1 Kd
        (dagLowOp (I := I) (M := M) g g₁) := by
    refine ⟨hKd, ?_⟩
    simpa only [H2Poly, pow_one] using
      hdag g₁ P hP htie hδ_le hδ0 hδ
  have hPgrad := gradP_hp (I := I) (M := M) g P
  have hout :=
    hp_app_of (I := I) (M := M) g P C hC (happ _ _) hd hPgrad
  simpa only [K, mul_one, Nat.reduceAdd, H2Poly] using hout.2

private theorem domperm_l2_sq
    (g : SmoothRiemannianMetric I M) {s : ℕ}
    (σ : Equiv.Perm (Fin s)) (S : SmoothCcTensor g 0 s) (i : ℕ) :
    ‖iteratedCovGrad (I := I) g 0 s i
        (domDomCongrSection (I := I) g σ S)‖ ^ 2 =
      ‖iteratedCovGrad (I := I) g 0 s i S‖ ^ 2 := by
  rw [SmoothCcTensor.norm_def,
    tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs,
    SmoothCcTensor.norm_def,
    tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs]
  refine MeasureTheory.integral_congr_ae
    (Filter.Eventually.of_forall fun x => ?_)
  exact riemannianFiberNormSq_iteratedCovGrad_domDomCongrSection
    (I := I) (M := M) g σ S i x

private theorem domperm_h2
    (g : SmoothRiemannianMetric I M) {s : ℕ}
    (σ : Equiv.Perm (Fin s)) (S : SmoothCcTensor g 0 s) :
    lowJetSq (I := I) (M := M) g 2
        (domDomCongrSection (I := I) g σ S) =
      lowJetSq (I := I) (M := M) g 2 S := by
  unfold lowJetSq
  apply Finset.sum_congr rfl
  intro i _
  exact domperm_l2_sq (I := I) (M := M) g σ S i

private theorem rsperm_l2_sq
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

private theorem rsperm_h2
    (g : SmoothRiemannianMetric I M) {r s : ℕ}
    (σ : Equiv.Perm (Fin s)) (S : SmoothCcTensor g r s) :
    lowJetSq (I := I) (M := M) g 2
        (rsDomDomCongrSection (I := I) (M := M) g r s σ S) =
      lowJetSq (I := I) (M := M) g 2 S := by
  unfold lowJetSq
  apply Finset.sum_congr rfl
  intro i _
  exact rsperm_l2_sq (I := I) (M := M) g σ S i

private theorem slot_iter2_h2
    (g : SmoothRiemannianMetric I M) (G : SmoothCcTensor g 0 4) :
    lowJetSq (I := I) (M := M) g 2
        (slotExtendIter (I := I) (M := M) g 0 4 2 G) ≤
      (Module.finrank ℝ E : ℝ) *
        ((Module.finrank ℝ E : ℝ) *
          lowJetSq (I := I) (M := M) g 2 G) := by
  change lowJetSq (I := I) (M := M) g 2
      (slotExtend (I := I) (M := M) g 1 5
        (slotExtend (I := I) (M := M) g 0 4 G)) ≤ _
  have hfr : (0 : ℝ) ≤ Module.finrank ℝ E := Nat.cast_nonneg _
  calc
    lowJetSq (I := I) (M := M) g 2
        (slotExtend (I := I) (M := M) g 1 5
          (slotExtend (I := I) (M := M) g 0 4 G)) ≤
      (Module.finrank ℝ E : ℝ) *
        lowJetSq (I := I) (M := M) g 2
          (slotExtend (I := I) (M := M) g 0 4 G) :=
      slot_h2 (I := I) (M := M) g 1 5 _
    _ ≤ (Module.finrank ℝ E : ℝ) *
        ((Module.finrank ℝ E : ℝ) *
          lowJetSq (I := I) (M := M) g 2 G) :=
      mul_le_mul_of_nonneg_left
        (slot_h2 (I := I) (M := M) g 0 4 G) hfr

set_option maxHeartbeats 1600000 in
private theorem refold_h2
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (G : SmoothCcTensor g 0 4) (σ : Equiv.Perm (Fin 4)),
        lowJetSq (I := I) (M := M) g 2
            (refoldKernelContractionMonomialField
              (I := I) (M := M) g g G σ) ≤
          K * lowJetSq (I := I) (M := M) g 2 G := by
  obtain ⟨C, hC, happ⟩ :=
    app_h2_mul (I := I) (M := M) hDim g 2 6 2
  let Km : ℝ := lowJetSq (I := I) (M := M) g 2
    (mvPairTraceOp (I := I) (M := M) g g)
  let fr : ℝ := Module.finrank ℝ E
  let K : ℝ := C * Km * (fr * fr)
  have hKm : 0 ≤ Km := jet_nonneg (I := I) (M := M) (m := 2) g _
  have hfr : 0 ≤ fr := Nat.cast_nonneg _
  have hK : 0 ≤ K :=
    mul_nonneg (mul_nonneg hC hKm) (mul_nonneg hfr hfr)
  refine ⟨K, hK, ?_⟩
  intro G σ
  let τ : Equiv.Perm (Fin 4) :=
    Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3 * σ
  let D : SmoothCcTensor g 0 4 :=
    domDomCongrSection (I := I) g τ G
  let S : SmoothCcTensor g 2 6 :=
    slotExtendIter (I := I) (M := M) g 0 4 2 D
  let R : SmoothCcTensor g 2 6 :=
    rsDomDomCongrSection (I := I) (M := M) g 2 6 sigmaE S
  have hD :
      lowJetSq (I := I) (M := M) g 2 D =
        lowJetSq (I := I) (M := M) g 2 G := by
    simpa only [D, τ] using
      domperm_h2 (I := I) (M := M) g τ G
  have hS :
      lowJetSq (I := I) (M := M) g 2 S ≤
        fr * (fr * lowJetSq (I := I) (M := M) g 2 D) := by
    simpa only [S, fr] using
      slot_iter2_h2 (I := I) (M := M) g D
  have hR :
      lowJetSq (I := I) (M := M) g 2 R =
        lowJetSq (I := I) (M := M) g 2 S := by
    simpa only [R] using
      rsperm_h2 (I := I) (M := M) g sigmaE S
  have href :
      refoldKernelContractionMonomialField
          (I := I) (M := M) g g G σ =
        appCcRS (I := I) (M := M) g 2 6 2
          (mvPairTraceOp (I := I) (M := M) g g) R := by
    simpa only [R, S, D, τ] using
      refoldKernelContractionMonomialField_eq_mvPairTraceRefold
        (I := I) (M := M) g g G σ
  rw [href]
  calc
    lowJetSq (I := I) (M := M) g 2
        (appCcRS (I := I) (M := M) g 2 6 2
          (mvPairTraceOp (I := I) (M := M) g g) R) ≤
      C * lowJetSq (I := I) (M := M) g 2
          (mvPairTraceOp (I := I) (M := M) g g) *
        lowJetSq (I := I) (M := M) g 2 R :=
      happ _ _
    _ = C * Km * lowJetSq (I := I) (M := M) g 2 S := by
      rw [hR]
    _ ≤ C * Km * (fr *
        (fr * lowJetSq (I := I) (M := M) g 2 D)) :=
      mul_le_mul_of_nonneg_left hS (mul_nonneg hC hKm)
    _ = K * lowJetSq (I := I) (M := M) g 2 G := by
      rw [hD]
      simp only [K]
      ring

set_option maxHeartbeats 1600000 in
set_option linter.unusedVariables false in
private theorem ricciDA_h2_rf
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀0 : 0 ≤ δ₀) (hδ₀ : δ₀ < 1) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (g₁ : SmoothRiemannianMetric I M)
        (P : SmoothCcTensor g 0 2)
        (hP : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g P x u v =
            ccTensorBilin (I := I) g P x v u)
        (htie : ∀ (x : M) (u v : TangentSpace I x),
          g₁.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g P x u v)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
        (hδ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g P) δ),
      lowJetSq (I := I) (M := M) g 2
          (ricciDALow (I := I) (M := M) g g₁ P) ≤
        K * (1 + lowJetSq (I := I) (M := M) g 3 P) ^ 3 := by
  obtain ⟨Kg, hKg, hG⟩ :=
    dagAct_h2_rf (I := I) (M := M) hDim g hδ₀0 hδ₀
  obtain ⟨Ke, hKe, hE⟩ :=
    full_slot_h3_rf (I := I) (M := M) g 1 hδ₀0 hδ₀
  obtain ⟨Cr, hCr, href⟩ :=
    refold_h2 (I := I) (M := M) hDim g
  obtain ⟨Ca, hCa, happ⟩ :=
    app_h2_mul (I := I) (M := M) hDim g 2 2 2
  let Km : ℝ := Ca * (Cr * Kg) * Ke
  let K : ℝ := 2 * (Km + Km)
  have hKm : 0 ≤ Km :=
    mul_nonneg (mul_nonneg hCa (mul_nonneg hCr hKg)) hKe
  have hK : 0 ≤ K :=
    mul_nonneg (by norm_num) (add_nonneg hKm hKm)
  refine ⟨K, hK, ?_⟩
  intro g₁ P hP htie δ hδ_le hδ0 hδ
  let G : SmoothCcTensor g 0 4 :=
    appCcRS (I := I) (M := M) g 0 3 4
      (dagLowOp (I := I) (M := M) g g₁)
      (covGrad (I := I) (M := M) g 0 2 P)
  let Eop : SmoothCcTensor g 2 2 :=
    slotInsertEndoCc (I := I) (M := M) g 1
      (fullRaisedEndoField (I := I) (M := M) g g₁)
  have hGp :
      H2Poly (I := I) (M := M) g P 2 Kg G := by
    refine ⟨hKg, ?_⟩
    simpa only [G, H2Poly] using
      hG g₁ P hP htie hδ_le hδ0 hδ
  have hEp :
      H2Poly (I := I) (M := M) g P 1 Ke Eop := by
    refine ⟨hKe, ?_⟩
    calc
      lowJetSq (I := I) (M := M) g 2 Eop ≤
        lowJetSq (I := I) (M := M) g 3 Eop :=
        jet_mono (I := I) (M := M) g (by omega : 2 ≤ 3) Eop
      _ ≤ Ke * (1 + lowJetSq (I := I) (M := M) g 3 P) :=
        hE g₁ P hP htie hδ_le hδ0 hδ
      _ = Ke * (1 + lowJetSq (I := I) (M := M) g 3 P) ^ 1 := by
        rw [pow_one]
  have hRp (σ : Equiv.Perm (Fin 4)) :
      H2Poly (I := I) (M := M) g P 2 (Cr * Kg)
        (refoldKernelContractionMonomialField
          (I := I) (M := M) g g G σ) := by
    refine ⟨mul_nonneg hCr hKg, ?_⟩
    calc
      lowJetSq (I := I) (M := M) g 2
          (refoldKernelContractionMonomialField
            (I := I) (M := M) g g G σ) ≤
        Cr * lowJetSq (I := I) (M := M) g 2 G :=
        href G σ
      _ ≤ Cr * (Kg *
          (1 + lowJetSq (I := I) (M := M) g 3 P) ^ 2) :=
        mul_le_mul_of_nonneg_left hGp.2 hCr
      _ = (Cr * Kg) *
          (1 + lowJetSq (I := I) (M := M) g 3 P) ^ 2 := by ring
  have hmono (σ : Equiv.Perm (Fin 4)) :
      H2Poly (I := I) (M := M) g P 3 Km
        (daMono (I := I) (M := M) g g₁ G σ) := by
    simpa only [Km, daMono, Nat.reduceAdd] using
      hp_app_of (I := I) (M := M) g P Ca hCa (happ _ _)
        (hRp σ) hEp
  have hsub :=
    hp_sub (I := I) (M := M) g P
      (hmono daPermA) (hmono daPermB)
  simpa only [K, ricciDALow, daContr, G, Nat.reduceAdd, H2Poly] using hsub.2

set_option maxHeartbeats 1600000 in
private theorem inputSymm_h2
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ C : SmoothCcTensor g 2 2,
        lowJetSq (I := I) (M := M) g 2
            (ccInputSymm (I := I) (M := M) g C) ≤
          K * lowJetSq (I := I) (M := M) g 2 C := by
  obtain ⟨Ca, hCa, happ⟩ :=
    app_h2_mul (I := I) (M := M) hDim g 2 2 2
  let Ks : ℝ := lowJetSq (I := I) (M := M) g 2
    (ccSlotSwapField (I := I) (M := M) g)
  let K : ℝ := 2 * (1 + Ca * Ks)
  have hKs : 0 ≤ Ks := jet_nonneg (I := I) (M := M) (m := 2) g _
  have hK : 0 ≤ K :=
    mul_nonneg (by norm_num) (add_nonneg (by norm_num) (mul_nonneg hCa hKs))
  refine ⟨K, hK, ?_⟩
  intro C
  have hC0 := jet_nonneg (I := I) (M := M) (m := 2) g C
  have happ' :
      lowJetSq (I := I) (M := M) g 2
          (appCcRS (I := I) (M := M) g 2 2 2 C
            (ccSlotSwapField (I := I) (M := M) g)) ≤
        (Ca * Ks) * lowJetSq (I := I) (M := M) g 2 C := by
    calc
      lowJetSq (I := I) (M := M) g 2
          (appCcRS (I := I) (M := M) g 2 2 2 C
            (ccSlotSwapField (I := I) (M := M) g)) ≤
        Ca * lowJetSq (I := I) (M := M) g 2 C * Ks := by
        simpa only [Ks] using happ C
          (ccSlotSwapField (I := I) (M := M) g)
      _ = (Ca * Ks) * lowJetSq (I := I) (M := M) g 2 C := by ring
  rw [ccInputSymm, jet_smul]
  have hsum0 := jet_nonneg (I := I) (M := M) (m := 2) g
    (C + appCcRS (I := I) (M := M) g 2 2 2 C
      (ccSlotSwapField (I := I) (M := M) g))
  calc
    ((1 : ℝ) / 2) ^ 2 *
        lowJetSq (I := I) (M := M) g 2
          (C + appCcRS (I := I) (M := M) g 2 2 2 C
            (ccSlotSwapField (I := I) (M := M) g)) ≤
      lowJetSq (I := I) (M := M) g 2
        (C + appCcRS (I := I) (M := M) g 2 2 2 C
          (ccSlotSwapField (I := I) (M := M) g)) := by
      nlinarith
    _ ≤ 2 * (lowJetSq (I := I) (M := M) g 2 C +
        lowJetSq (I := I) (M := M) g 2
          (appCcRS (I := I) (M := M) g 2 2 2 C
            (ccSlotSwapField (I := I) (M := M) g))) :=
      jet_add (I := I) (M := M) g 2 C _
    _ ≤ 2 * (lowJetSq (I := I) (M := M) g 2 C +
        (Ca * Ks) * lowJetSq (I := I) (M := M) g 2 C) :=
      mul_le_mul_of_nonneg_left
        (add_le_add le_rfl happ') (by norm_num)
    _ = K * lowJetSq (I := I) (M := M) g 2 C := by
      simp only [K]
      ring

set_option maxHeartbeats 1600000 in
set_option linter.unusedVariables false in
private theorem ricciGood_h2_rf
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀0 : 0 ≤ δ₀) (hδ₀ : δ₀ < 1) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (g₁ : SmoothRiemannianMetric I M)
        (P : SmoothCcTensor g 0 2)
        (hP : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g P x u v =
            ccTensorBilin (I := I) g P x v u)
        (htie : ∀ (x : M) (u v : TangentSpace I x),
          g₁.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g P x u v)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
        (hδ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g P) δ),
      lowJetSq (I := I) (M := M) g 2
          (ricciGoodLow (I := I) (M := M) g g₁ P) ≤
        K * (1 + lowJetSq (I := I) (M := M) g 3 P) ^ 3 := by
  obtain ⟨Kaa, hKaa, haa⟩ :=
    ricciAA_h2_rf (I := I) (M := M) hDim g hδ₀0 hδ₀
  obtain ⟨Kda, hKda, hda⟩ :=
    ricciDA_h2_rf (I := I) (M := M) hDim g hδ₀0 hδ₀
  obtain ⟨Cs, hCs, hsymm⟩ :=
    inputSymm_h2 (I := I) (M := M) hDim g
  let Kl : ℝ := 2 * (Kaa + Kda)
  let K : ℝ := Cs * Kl
  have hKl : 0 ≤ Kl :=
    mul_nonneg (by norm_num) (add_nonneg hKaa hKda)
  have hK : 0 ≤ K := mul_nonneg hCs hKl
  refine ⟨K, hK, ?_⟩
  intro g₁ P hP htie δ hδ_le hδ0 hδ
  have hAA :
      H2Poly (I := I) (M := M) g P 3 Kaa
        (ricciAAArm (I := I) (M := M) g g₁) :=
    ⟨hKaa, haa g₁ P hP htie hδ_le hδ0 hδ⟩
  have hDA :
      H2Poly (I := I) (M := M) g P 3 Kda
        (ricciDALow (I := I) (M := M) g g₁ P) :=
    ⟨hKda, hda g₁ P hP htie hδ_le hδ0 hδ⟩
  have hlow :
      H2Poly (I := I) (M := M) g P 3 Kl
        (ricciLow (I := I) (M := M) g g₁ P) := by
    simpa only [Kl, ricciLow] using
      hp_add (I := I) (M := M) g P hAA hDA
  calc
    lowJetSq (I := I) (M := M) g 2
        (ricciGoodLow (I := I) (M := M) g g₁ P) =
      lowJetSq (I := I) (M := M) g 2
        (ccInputSymm (I := I) (M := M) g
          (ricciLow (I := I) (M := M) g g₁ P)) := rfl
    _ ≤ Cs * lowJetSq (I := I) (M := M) g 2
        (ricciLow (I := I) (M := M) g g₁ P) :=
      hsymm _
    _ ≤ Cs * (Kl *
        (1 + lowJetSq (I := I) (M := M) g 3 P) ^ 3) :=
      mul_le_mul_of_nonneg_left hlow.2 hCs
    _ = K * (1 + lowJetSq (I := I) (M := M) g 3 P) ^ 3 := by
      simp only [K]
      ring

set_option linter.unusedVariables false in
private theorem cometric_h2_rf
    (g : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀0 : 0 ≤ δ₀) (hδ₀ : δ₀ < 1) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (g₁ : SmoothRiemannianMetric I M)
        (P : SmoothCcTensor g 0 2)
        (hP : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g P x u v =
            ccTensorBilin (I := I) g P x v u)
        (htie : ∀ (x : M) (u v : TangentSpace I x),
          g₁.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g P x u v)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
        (hδ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g P) δ),
      lowJetSq (I := I) (M := M) g 2
          (cometricCastG0 (I := I) g g₁) ≤
        K * (1 + lowJetSq (I := I) (M := M) g 3 P) := by
  classical
  let aStar : ℕ := 2 * Module.finrank ℝ E + 10
  let Λ₀ : ℝ := (Module.finrank ℝ E : ℝ) * δ₀
  have hΛ₀0 : 0 ≤ Λ₀ :=
    mul_nonneg (Nat.cast_nonneg _) hδ₀0
  obtain ⟨Λ, F, hΛ, hF, hcast⟩ :=
    cometricCastG0_order0sup_jetL2_radiusFree
      (I := I) (M := M) g aStar le_rfl hδ₀ hΛ₀0
  refine ⟨F 2, hF 2, ?_⟩
  intro g₁ P hP htie δ hδ_le hδ0 hδ
  have hsymm : symmS (I := I) (M := M) g P = P :=
    symm_eq_self (I := I) (M := M) g P hP
  have hsup : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g 0 2 x
          (P.toSection x) ≤ Λ₀ ^ 2 := by
    intro x
    rw [← hsymm]
    exact rfns_symmS_zero_le_fibreSmall
      (I := I) (M := M) g hδ₀0 P hδ_le hδ0 hδ x
  have hraw := (hcast g₁ P htie hδ_le hδ0 hδ hsup).2 2 (by
    dsimp only [aStar]
    omega)
  have h23 := jet_mono (I := I) (M := M) g
    (by omega : 2 ≤ 3) P
  calc
    lowJetSq (I := I) (M := M) g 2
        (cometricCastG0 (I := I) g g₁) ≤
      F 2 * (1 + lowJetSq (I := I) (M := M) g 2 P) := by
        simpa only [lowJetSq, Nat.reduceAdd] using hraw
    _ ≤ F 2 * (1 + lowJetSq (I := I) (M := M) g 3 P) :=
      mul_le_mul_of_nonneg_left (add_le_add le_rfl h23) (hF 2)

set_option linter.unusedVariables false in
private theorem riemLive_h2_rf
    (g : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀0 : 0 ≤ δ₀) (hδ₀ : δ₀ < 1) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (g₁ : SmoothRiemannianMetric I M)
        (P : SmoothCcTensor g 0 2)
        (hP : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g P x u v =
            ccTensorBilin (I := I) g P x v u)
        (htie : ∀ (x : M) (u v : TangentSpace I x),
          g₁.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g P x u v)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
        (hδ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g P) δ),
      lowJetSq (I := I) (M := M) g 2
          (lc0RiemLive (I := I) (M := M) g g₁) ≤
        K * (1 + lowJetSq (I := I) (M := M) g 3 P) := by
  obtain ⟨Kc, hKc, hc⟩ :=
    cometric_h2_rf (I := I) (M := M) g hδ₀0 hδ₀
  let fr : ℝ := Module.finrank ℝ E
  let K : ℝ := fr * Kc
  have hfr : 0 ≤ fr := Nat.cast_nonneg _
  have hK : 0 ≤ K := mul_nonneg hfr hKc
  refine ⟨K, hK, ?_⟩
  intro g₁ P hP htie δ hδ_le hδ0 hδ
  unfold lowJetSq
  calc
    ∑ i ∈ Finset.range 3,
        ‖iteratedCovGrad (I := I) g 4 2 i
          (lc0RiemLive (I := I) (M := M) g g₁)‖ ^ 2 ≤
      ∑ i ∈ Finset.range 3, fr *
        ‖iteratedCovGrad (I := I) g 3 1 i
          (cometricCastG0 (I := I) g g₁)‖ ^ 2 := by
        exact Finset.sum_le_sum fun i _ => by
          simpa only [fr] using
            lc0RiemLive_l2_le (I := I) (M := M) g g₁ i
    _ = fr * lowJetSq (I := I) (M := M) g 2
        (cometricCastG0 (I := I) g g₁) := by
      rw [← Finset.mul_sum]
      rfl
    _ ≤ fr * (Kc *
        (1 + lowJetSq (I := I) (M := M) g 3 P)) :=
      mul_le_mul_of_nonneg_left
        (hc g₁ P hP htie hδ_le hδ0 hδ) hfr
    _ = K * (1 + lowJetSq (I := I) (M := M) g 3 P) := by
      simp only [K]
      ring

set_option maxHeartbeats 1600000 in
set_option linter.unusedVariables false in
private theorem lc0Riem_h2_rf
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀0 : 0 ≤ δ₀) (hδ₀ : δ₀ < 1) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (g₁ : SmoothRiemannianMetric I M)
        (P : SmoothCcTensor g 0 2)
        (hP : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g P x u v =
            ccTensorBilin (I := I) g P x v u)
        (htie : ∀ (x : M) (u v : TangentSpace I x),
          g₁.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g P x u v)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
        (hδ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g P) δ),
      lowJetSq (I := I) (M := M) g 2
          (lc0Riem (I := I) (M := M) g g₁) ≤
        K * (1 + lowJetSq (I := I) (M := M) g 3 P) := by
  obtain ⟨Kl, hKl, hlive⟩ :=
    riemLive_h2_rf (I := I) (M := M) g hδ₀0 hδ₀
  obtain ⟨Ca, hCa, happ⟩ :=
    app_h2_mul (I := I) (M := M) hDim g 2 4 2
  let B : ℝ := lowJetSq (I := I) (M := M) g 2
    (lc0RiemPass (I := I) g)
  let K : ℝ := Ca * Kl * B
  have hB : 0 ≤ B :=
    jet_nonneg (I := I) (M := M) (m := 2) g
      (lc0RiemPass (I := I) g)
  have hK : 0 ≤ K := mul_nonneg (mul_nonneg hCa hKl) hB
  refine ⟨K, hK, ?_⟩
  intro g₁ P hP htie δ hδ_le hδ0 hδ
  have hLive := hlive g₁ P hP htie hδ_le hδ0 hδ
  have hApp := happ
    (lc0RiemLive (I := I) (M := M) g g₁)
    (lc0RiemPass (I := I) g)
  calc
    lowJetSq (I := I) (M := M) g 2
        (lc0Riem (I := I) (M := M) g g₁) =
      lowJetSq (I := I) (M := M) g 2
        (appCcRS (I := I) (M := M) g 2 4 2
          (lc0RiemLive (I := I) (M := M) g g₁)
          (lc0RiemPass (I := I) g)) := by
        rw [lc0Riem_eq_app (I := I) (M := M) g g₁]
        unfold lowJetSq
        apply Finset.sum_congr rfl
        intro q _
        rw [iteratedCovGrad_neg, norm_neg]
    _ ≤ Ca *
        lowJetSq (I := I) (M := M) g 2
          (lc0RiemLive (I := I) (M := M) g g₁) *
        lowJetSq (I := I) (M := M) g 2
          (lc0RiemPass (I := I) g) := hApp
    _ ≤ Ca * (Kl *
        (1 + lowJetSq (I := I) (M := M) g 3 P)) * B := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hLive hCa) hB
    _ = K * (1 + lowJetSq (I := I) (M := M) g 3 P) := by
      simp only [K]
      ring

set_option linter.unusedVariables false in
private theorem mcd_h2_rf
    (g : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀0 : 0 ≤ δ₀) (hδ₀ : δ₀ < 1) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (g₁ : SmoothRiemannianMetric I M)
        (P : SmoothCcTensor g 0 2)
        (hP : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g P x u v =
            ccTensorBilin (I := I) g P x v u)
        (htie : ∀ (x : M) (u v : TangentSpace I x),
          g₁.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g P x u v)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
        (hδ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g P) δ),
      lowJetSq (I := I) (M := M) g 2
          (metricConnDiffLoweredCc (I := I) (M := M) g g₁ g) ≤
        K * (1 + lowJetSq (I := I) (M := M) g 3 P) := by
  classical
  let Λ₀ : ℝ := (Module.finrank ℝ E : ℝ) * δ₀
  have hΛ₀ : 0 ≤ Λ₀ := mul_nonneg (Nat.cast_nonneg _) hδ₀0
  obtain ⟨F, hF, hmcd⟩ :=
    mcd_l2_radiusFree (I := I) (M := M) g g hδ₀ hΛ₀
  let K : ℝ := ∑ q ∈ Finset.range 3, F q
  have hK : 0 ≤ K := by
    exact Finset.sum_nonneg fun q _ => hF q
  refine ⟨K, hK, ?_⟩
  intro g₁ P hP htie δ hδ_le hδ0 hδ
  have hsymm : symmS (I := I) (M := M) g P = P :=
    symm_eq_self (I := I) (M := M) g P hP
  have hsup : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g 0 2 x
          (P.toSection x) ≤ Λ₀ ^ 2 := by
    intro x
    rw [← hsymm]
    exact rfns_symmS_zero_le_fibreSmall
      (I := I) (M := M) g hδ₀0 P hδ_le hδ0 hδ x
  unfold lowJetSq
  calc
    ∑ q ∈ Finset.range 3,
        ‖iteratedCovGrad (I := I) g 0 3 q
          (metricConnDiffLoweredCc (I := I) (M := M) g g₁ g)‖ ^ 2 ≤
      ∑ q ∈ Finset.range 3,
        F q * (1 + ∑ j ∈ Finset.range 4,
          ‖iteratedCovGrad (I := I) g 0 2 j P‖ ^ 2) := by
        refine Finset.sum_le_sum fun q hq => ?_
        have hraw := hmcd g₁ P htie hδ_le hδ0 hδ hsup q
        have hsub : Finset.range (q + 2) ⊆ Finset.range 4 :=
          Finset.range_subset_range.mpr (by
            have : q < 3 := Finset.mem_range.mp hq
            omega)
        have hsum :
            (∑ j ∈ Finset.range (q + 2),
                ‖iteratedCovGrad (I := I) g 0 2 j P‖ ^ 2) ≤
              ∑ j ∈ Finset.range 4,
                ‖iteratedCovGrad (I := I) g 0 2 j P‖ ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub
            (fun j _ _ => sq_nonneg
              ‖iteratedCovGrad (I := I) g 0 2 j P‖)
        exact le_trans hraw
          (mul_le_mul_of_nonneg_left
            (add_le_add le_rfl hsum) (hF q))
    _ = K * (1 + ∑ j ∈ Finset.range 4,
          ‖iteratedCovGrad (I := I) g 0 2 j P‖ ^ 2) := by
      rw [← Finset.sum_mul]

set_option maxHeartbeats 1600000 in
set_option linter.unusedVariables false in
private theorem connLower_h2_rf
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀0 : 0 ≤ δ₀) (hδ₀ : δ₀ < 1) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (g₁ : SmoothRiemannianMetric I M)
        (P : SmoothCcTensor g 0 2)
        (hP : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g P x u v =
            ccTensorBilin (I := I) g P x v u)
        (htie : ∀ (x : M) (u v : TangentSpace I x),
          g₁.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g P x u v)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
        (hδ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g P) δ),
      lowJetSq (I := I) (M := M) g 2
          (connDiffLoweredCc (I := I) g g₁) ≤
        K * (1 + lowJetSq (I := I) (M := M) g 3 P) ^ 2 := by
  obtain ⟨Ko, hKo, hop⟩ :=
    connLow_h3_rf (I := I) (M := M) hDim g hδ₀0 hδ₀
  obtain ⟨Ca, hCa, happ⟩ :=
    app_h2_mul (I := I) (M := M) hDim g 0 3 3
  let K : ℝ := Ca * Ko
  have hK : 0 ≤ K := mul_nonneg hCa hKo
  refine ⟨K, hK, ?_⟩
  intro g₁ P hP htie δ hδ_le hδ0 hδ
  have hOp : H2Poly (I := I) (M := M) g P 1 Ko
      (connLowOp (I := I) (M := M) g g₁) := by
    refine ⟨hKo, ?_⟩
    calc
      lowJetSq (I := I) (M := M) g 2
          (connLowOp (I := I) (M := M) g g₁) ≤
        lowJetSq (I := I) (M := M) g 3
          (connLowOp (I := I) (M := M) g g₁) :=
            jet_mono (I := I) (M := M) g (by omega) _
      _ ≤ Ko * (1 + lowJetSq (I := I) (M := M) g 3 P) :=
        hop g₁ P hP htie hδ_le hδ0 hδ
      _ = Ko * (1 + lowJetSq (I := I) (M := M) g 3 P) ^ 1 := by
        rw [pow_one]
  have hGrad : H2Poly (I := I) (M := M) g P 1 1
      (covGrad (I := I) (M := M) g 0 2 P) := by
    refine ⟨by norm_num, ?_⟩
    calc
      lowJetSq (I := I) (M := M) g 2
          (covGrad (I := I) (M := M) g 0 2 P) ≤
        lowJetSq (I := I) (M := M) g 3 P :=
          grad_h2_le_h3 (I := I) (M := M) g P
      _ ≤ 1 * (1 + lowJetSq (I := I) (M := M) g 3 P) ^ 1 := by
        simp only [one_mul, pow_one]
        linarith
  have hApp :=
    hp_app_of (I := I) (M := M) g P Ca hCa
      (happ (connLowOp (I := I) (M := M) g g₁)
        (covGrad (I := I) (M := M) g 0 2 P))
      hOp hGrad
  rw [← connLowOp_app (I := I) (M := M) g g₁ P hP htie]
  simpa only [K, Nat.reduceAdd, mul_one] using hApp.2

set_option maxHeartbeats 1600000 in
set_option linter.unusedVariables false in
private theorem wOmega_h2_rf
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀0 : 0 ≤ δ₀) (hδ₀ : δ₀ < 1) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (g₁ : SmoothRiemannianMetric I M)
        (P : SmoothCcTensor g 0 2)
        (hP : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g P x u v =
            ccTensorBilin (I := I) g P x v u)
        (htie : ∀ (x : M) (u v : TangentSpace I x),
          g₁.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g P x u v)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
        (hδ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g P) δ),
      lowJetSq (I := I) (M := M) g 2
          (wOmega (I := I) (M := M) g g₁ g) ≤
        K * (1 + lowJetSq (I := I) (M := M) g 3 P) ^ 3 := by
  obtain ⟨Kt, hKt, htrace⟩ :=
    trace_h2_rf (I := I) (M := M) 1 g hδ₀0 hδ₀
  obtain ⟨Kc, hKc, hconn⟩ :=
    connLower_h2_rf (I := I) (M := M) hDim g hδ₀0 hδ₀
  obtain ⟨Ca, hCa, happ⟩ :=
    app_h2_mul (I := I) (M := M) hDim g 0 3 1
  let K : ℝ := Ca * Kt * Kc
  have hK : 0 ≤ K := mul_nonneg (mul_nonneg hCa hKt) hKc
  refine ⟨K, hK, ?_⟩
  intro g₁ P hP htie δ hδ_le hδ0 hδ
  have hTr : H2Poly (I := I) (M := M) g P 1 Kt
      (lc0TraceRF (I := I) (M := M) g g₁ 1 (Equiv.refl _)) := by
    refine ⟨hKt, ?_⟩
    calc
      lowJetSq (I := I) (M := M) g 2
          (lc0TraceRF (I := I) (M := M) g g₁ 1 (Equiv.refl _)) ≤
        Kt * (1 + lowJetSq (I := I) (M := M) g 2 P) :=
          htrace g₁ P hP htie hδ_le hδ0 hδ _
      _ ≤ Kt * (1 + lowJetSq (I := I) (M := M) g 3 P) :=
        mul_le_mul_of_nonneg_left
          (add_le_add le_rfl
            (jet_mono (I := I) (M := M) g (by omega : 2 ≤ 3) P))
          hKt
      _ = Kt * (1 + lowJetSq (I := I) (M := M) g 3 P) ^ 1 := by
        rw [pow_one]
  have hConn : H2Poly (I := I) (M := M) g P 2 Kc
      (connDiffLoweredCc (I := I) g g₁) :=
    ⟨hKc, hconn g₁ P hP htie hδ_le hδ0 hδ⟩
  have hApp :=
    hp_app_of (I := I) (M := M) g P Ca hCa
      (happ
        (lc0TraceRF (I := I) (M := M) g g₁ 1 (Equiv.refl _))
        (connDiffLoweredCc (I := I) g g₁))
      hTr hConn
  rw [wOmega_refold (I := I) (M := M) g g₁]
  simpa only [K, Nat.reduceAdd] using hApp.2

set_option linter.unusedVariables false in
private theorem ip_h2
    (g : SmoothRiemannianMetric I M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ om : SmoothCcTensor g 0 1,
        lowJetSq (I := I) (M := M) g 2
            (ipLowCc (I := I) (M := M) g om) ≤
          C * lowJetSq (I := I) (M := M) g 2 om := by
  obtain ⟨c, hc0, hc⟩ :=
    norm_icg_ipLow_le (I := I) (M := M) g
  let C : ℝ := ∑ l ∈ Finset.range 3, c l
  have hC : 0 ≤ C := Finset.sum_nonneg fun l _ => hc0 l
  refine ⟨C, hC, ?_⟩
  intro om
  unfold lowJetSq
  calc
    ∑ l ∈ Finset.range 3,
        ‖iteratedCovGrad (I := I) g 2 1 l
          (ipLowCc (I := I) (M := M) g om)‖ ^ 2 ≤
      ∑ l ∈ Finset.range 3, c l *
        (∑ m ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g 0 1 m om‖ ^ 2) := by
        refine Finset.sum_le_sum fun l hl => ?_
        have hraw := hc om l
        have hsub : Finset.range (l + 1) ⊆ Finset.range 3 :=
          Finset.range_subset_range.mpr (by
            have : l < 3 := Finset.mem_range.mp hl
            omega)
        have hsum :
            (∑ m ∈ Finset.range (l + 1),
                ‖iteratedCovGrad (I := I) g 0 1 m om‖ ^ 2) ≤
              ∑ m ∈ Finset.range 3,
                ‖iteratedCovGrad (I := I) g 0 1 m om‖ ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub
            (fun m _ _ => sq_nonneg
              ‖iteratedCovGrad (I := I) g 0 1 m om‖)
        exact le_trans hraw
          (mul_le_mul_of_nonneg_left hsum (hc0 l))
    _ = C * ∑ m ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g 0 1 m om‖ ^ 2 := by
      rw [← Finset.sum_mul]

set_option linter.unusedVariables false in
private theorem vbMcd_h2
    (g : SmoothRiemannianMetric I M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ g₁ : SmoothRiemannianMetric I M,
        lowJetSq (I := I) (M := M) g 2
            (vbMcdArm (I := I) (M := M) g g₁) ≤
          C * lowJetSq (I := I) (M := M) g 2
            (metricConnDiffLoweredCc (I := I) (M := M) g g₁ g) := by
  let C : ℝ := Module.finrank ℝ E
  have hC : 0 ≤ C := Nat.cast_nonneg _
  refine ⟨C, hC, ?_⟩
  intro g₁
  unfold lowJetSq
  calc
    ∑ m ∈ Finset.range 3,
        ‖iteratedCovGrad (I := I) g 1 4 m
          (vbMcdArm (I := I) (M := M) g g₁)‖ ^ 2 ≤
      ∑ m ∈ Finset.range 3, C *
        ‖iteratedCovGrad (I := I) g 0 3 m
          (metricConnDiffLoweredCc (I := I) (M := M) g g₁ g)‖ ^ 2 := by
        exact Finset.sum_le_sum fun m _ => by
          simpa only [C] using
            vbMcdArm_l2_le (I := I) (M := M) g g₁ m
    _ = C * ∑ m ∈ Finset.range 3,
        ‖iteratedCovGrad (I := I) g 0 3 m
          (metricConnDiffLoweredCc (I := I) (M := M) g g₁ g)‖ ^ 2 := by
      rw [← Finset.mul_sum]

set_option maxHeartbeats 3200000 in
set_option linter.unusedVariables false in
private theorem lc0VB_h2_rf
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀0 : 0 ≤ δ₀) (hδ₀ : δ₀ < 1) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (g₁ : SmoothRiemannianMetric I M)
        (P : SmoothCcTensor g 0 2)
        (hP : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g P x u v =
            ccTensorBilin (I := I) g P x v u)
        (htie : ∀ (x : M) (u v : TangentSpace I x),
          g₁.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g P x u v)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
        (hδ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g P) δ),
      lowJetSq (I := I) (M := M) g 2
          (lc0VB (I := I) (M := M) g g₁) ≤
        K * (1 + lowJetSq (I := I) (M := M) g 3 P) ^ 5 := by
  obtain ⟨Kl, hKl, hlive⟩ :=
    riemLive_h2_rf (I := I) (M := M) g hδ₀0 hδ₀
  obtain ⟨Km, hKm, hmcd⟩ :=
    mcd_h2_rf (I := I) (M := M) g hδ₀0 hδ₀
  obtain ⟨Ko, hKo, homega⟩ :=
    wOmega_h2_rf (I := I) (M := M) hDim g hδ₀0 hδ₀
  obtain ⟨Cv, hCv, hvb⟩ := vbMcd_h2 (I := I) (M := M) g
  obtain ⟨Ci, hCi, hip⟩ := ip_h2 (I := I) (M := M) g
  obtain ⟨Ca, hCa, happA⟩ :=
    app_h2_mul (I := I) (M := M) hDim g 2 1 4
  obtain ⟨Cb, hCb, happB⟩ :=
    app_h2_mul (I := I) (M := M) hDim g 2 4 2
  let Kvm : ℝ := Cv * Km
  let Kip : ℝ := Ci * Ko
  let Kinner : ℝ := Ca * Kvm * Kip
  let Kouter : ℝ := Cb * Kl * Kinner
  let K : ℝ := (2 : ℝ) ^ 2 * Kouter
  have hKvm : 0 ≤ Kvm := mul_nonneg hCv hKm
  have hKip : 0 ≤ Kip := mul_nonneg hCi hKo
  have hKinner : 0 ≤ Kinner :=
    mul_nonneg (mul_nonneg hCa hKvm) hKip
  have hKouter : 0 ≤ Kouter :=
    mul_nonneg (mul_nonneg hCb hKl) hKinner
  have hK : 0 ≤ K := mul_nonneg (sq_nonneg _) hKouter
  refine ⟨K, hK, ?_⟩
  intro g₁ P hP htie δ hδ_le hδ0 hδ
  have hLive : H2Poly (I := I) (M := M) g P 1 Kl
      (lc0RiemLive (I := I) (M := M) g g₁) :=
    ⟨hKl, by
      simpa only [pow_one] using
        hlive g₁ P hP htie hδ_le hδ0 hδ⟩
  have hMcd : H2Poly (I := I) (M := M) g P 1 Km
      (metricConnDiffLoweredCc (I := I) (M := M) g g₁ g) :=
    ⟨hKm, by
      simpa only [pow_one] using
        hmcd g₁ P hP htie hδ_le hδ0 hδ⟩
  have hVBArm : H2Poly (I := I) (M := M) g P 1 Kvm
      (vbMcdArm (I := I) (M := M) g g₁) := by
    refine ⟨hKvm, ?_⟩
    calc
      lowJetSq (I := I) (M := M) g 2
          (vbMcdArm (I := I) (M := M) g g₁) ≤
        Cv * lowJetSq (I := I) (M := M) g 2
          (metricConnDiffLoweredCc (I := I) (M := M) g g₁ g) :=
            hvb g₁
      _ ≤ Cv * (Km *
          (1 + lowJetSq (I := I) (M := M) g 3 P) ^ 1) :=
        mul_le_mul_of_nonneg_left hMcd.2 hCv
      _ = Kvm * (1 + lowJetSq (I := I) (M := M) g 3 P) ^ 1 := by
        simp only [Kvm]
        ring
  have hOmega : H2Poly (I := I) (M := M) g P 3 Ko
      (wOmega (I := I) (M := M) g g₁ g) :=
    ⟨hKo, homega g₁ P hP htie hδ_le hδ0 hδ⟩
  have hIp : H2Poly (I := I) (M := M) g P 3 Kip
      (ipLowCc (I := I) (M := M) g
        (wOmega (I := I) (M := M) g g₁ g)) := by
    refine ⟨hKip, ?_⟩
    calc
      lowJetSq (I := I) (M := M) g 2
          (ipLowCc (I := I) (M := M) g
            (wOmega (I := I) (M := M) g g₁ g)) ≤
        Ci * lowJetSq (I := I) (M := M) g 2
          (wOmega (I := I) (M := M) g g₁ g) := hip _
      _ ≤ Ci * (Ko *
          (1 + lowJetSq (I := I) (M := M) g 3 P) ^ 3) :=
        mul_le_mul_of_nonneg_left hOmega.2 hCi
      _ = Kip * (1 + lowJetSq (I := I) (M := M) g 3 P) ^ 3 := by
        simp only [Kip]
        ring
  have hInner :=
    hp_app_of (I := I) (M := M) g P Ca hCa
      (happA (vbMcdArm (I := I) (M := M) g g₁)
        (ipLowCc (I := I) (M := M) g
          (wOmega (I := I) (M := M) g g₁ g)))
      hVBArm hIp
  have hOuter :=
    hp_app_of (I := I) (M := M) g P Cb hCb
      (happB (lc0RiemLive (I := I) (M := M) g g₁)
        (appCcRS (I := I) (M := M) g 2 1 4
          (vbMcdArm (I := I) (M := M) g g₁)
          (ipLowCc (I := I) (M := M) g
            (wOmega (I := I) (M := M) g g₁ g))))
      hLive hInner
  have hScaled :=
    hp_smul (I := I) (M := M) g P (2 : ℝ) hOuter
  rw [vb_refold_rf (I := I) (M := M) g g₁]
  simpa only [lc0VBFormRF, Kvm, Kip, Kinner, Kouter, K,
    Nat.reduceAdd] using hScaled.2

set_option maxHeartbeats 6400000 in
set_option linter.unusedVariables false in
private theorem lc0AMix_h2_rf
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀0 : 0 ≤ δ₀) (hδ₀ : δ₀ < 1) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (g₁ : SmoothRiemannianMetric I M)
        (P : SmoothCcTensor g 0 2)
        (hP : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g P x u v =
            ccTensorBilin (I := I) g P x v u)
        (htie : ∀ (x : M) (u v : TangentSpace I x),
          g₁.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g P x u v)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
        (hδ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g P) δ),
      lowJetSq (I := I) (M := M) g 2
          (lc0AMix (I := I) (M := M) g g₁ g) ≤
        K * (1 + lowJetSq (I := I) (M := M) g 3 P) ^ 5 := by
  obtain ⟨Km, hKm, hmcd⟩ :=
    mcd_h2_rf (I := I) (M := M) g hδ₀0 hδ₀
  obtain ⟨K2, hK2, ht2⟩ :=
    trace_h2_rf (I := I) (M := M) 2 g hδ₀0 hδ₀
  obtain ⟨K3, hK3, ht3⟩ :=
    trace_h2_rf (I := I) (M := M) 3 g hδ₀0 hδ₀
  obtain ⟨K4, hK4, ht4⟩ :=
    trace_h2_rf (I := I) (M := M) 4 g hδ₀0 hδ₀
  obtain ⟨Ca, hCa, happA⟩ :=
    app_h2_mul (I := I) (M := M) hDim g 2 5 3
  obtain ⟨Cb, hCb, happB⟩ :=
    app_h2_mul (I := I) (M := M) hDim g 2 3 6
  obtain ⟨Cc, hCc, happC⟩ :=
    app_h2_mul (I := I) (M := M) hDim g 2 6 4
  obtain ⟨Cd, hCd, happD⟩ :=
    app_h2_mul (I := I) (M := M) hDim g 2 4 2
  let fr : ℝ := Module.finrank ℝ E
  let Ks2 : ℝ := fr * (fr * Km)
  let Ks3 : ℝ := fr * (fr * (fr * Km))
  let Ktail : ℝ := Ca * K3 * Ks2
  let Kmid : ℝ := Cb * Ks3 * Ktail
  let Ktraced : ℝ := Cc * K4 * Kmid
  let Khalf : ℝ := Cd * K2 * Ktraced
  let Ksum : ℝ := 2 * (Khalf + Khalf)
  let K : ℝ := (2 : ℝ) ^ 2 * Ksum
  have hfr : 0 ≤ fr := Nat.cast_nonneg _
  have hKs2 : 0 ≤ Ks2 := mul_nonneg hfr (mul_nonneg hfr hKm)
  have hKs3 : 0 ≤ Ks3 :=
    mul_nonneg hfr (mul_nonneg hfr (mul_nonneg hfr hKm))
  have hKtail : 0 ≤ Ktail :=
    mul_nonneg (mul_nonneg hCa hK3) hKs2
  have hKmid : 0 ≤ Kmid :=
    mul_nonneg (mul_nonneg hCb hKs3) hKtail
  have hKtraced : 0 ≤ Ktraced :=
    mul_nonneg (mul_nonneg hCc hK4) hKmid
  have hKhalf : 0 ≤ Khalf :=
    mul_nonneg (mul_nonneg hCd hK2) hKtraced
  have hKsum : 0 ≤ Ksum :=
    mul_nonneg (by norm_num) (add_nonneg hKhalf hKhalf)
  have hK : 0 ≤ K := mul_nonneg (sq_nonneg _) hKsum
  refine ⟨K, hK, ?_⟩
  intro g₁ P hP htie δ hδ_le hδ0 hδ
  have hMcd : H2Poly (I := I) (M := M) g P 1 Km
      (metricConnDiffLoweredCc (I := I) (M := M) g g₁ g) :=
    ⟨hKm, by
      simpa only [pow_one] using
        hmcd g₁ P hP htie hδ_le hδ0 hδ⟩
  have hT2 (σ : Equiv.Perm (Fin 4)) :
      H2Poly (I := I) (M := M) g P 1 K2
        (lc0TraceRF (I := I) (M := M) g g₁ 2 σ) := by
    refine ⟨hK2, ?_⟩
    calc
      lowJetSq (I := I) (M := M) g 2
          (lc0TraceRF (I := I) (M := M) g g₁ 2 σ) ≤
        K2 * (1 + lowJetSq (I := I) (M := M) g 2 P) :=
          ht2 g₁ P hP htie hδ_le hδ0 hδ σ
      _ ≤ K2 * (1 + lowJetSq (I := I) (M := M) g 3 P) :=
        mul_le_mul_of_nonneg_left
          (add_le_add le_rfl
            (jet_mono (I := I) (M := M) g (by omega : 2 ≤ 3) P))
          hK2
      _ = K2 * (1 + lowJetSq (I := I) (M := M) g 3 P) ^ 1 := by
        rw [pow_one]
  have hT3 : H2Poly (I := I) (M := M) g P 1 K3
      (lc0TraceRF (I := I) (M := M) g g₁ 3 lieCorr0AMixPermQ) := by
    refine ⟨hK3, ?_⟩
    calc
      lowJetSq (I := I) (M := M) g 2
          (lc0TraceRF (I := I) (M := M) g g₁ 3 lieCorr0AMixPermQ) ≤
        K3 * (1 + lowJetSq (I := I) (M := M) g 2 P) :=
          ht3 g₁ P hP htie hδ_le hδ0 hδ _
      _ ≤ K3 * (1 + lowJetSq (I := I) (M := M) g 3 P) :=
        mul_le_mul_of_nonneg_left
          (add_le_add le_rfl
            (jet_mono (I := I) (M := M) g (by omega : 2 ≤ 3) P))
          hK3
      _ = K3 * (1 + lowJetSq (I := I) (M := M) g 3 P) ^ 1 := by
        rw [pow_one]
  have hT4 : H2Poly (I := I) (M := M) g P 1 K4
      (lc0TraceRF (I := I) (M := M) g g₁ 4 lieCorr0AMixPerm1) := by
    refine ⟨hK4, ?_⟩
    calc
      lowJetSq (I := I) (M := M) g 2
          (lc0TraceRF (I := I) (M := M) g g₁ 4 lieCorr0AMixPerm1) ≤
        K4 * (1 + lowJetSq (I := I) (M := M) g 2 P) :=
          ht4 g₁ P hP htie hδ_le hδ0 hδ _
      _ ≤ K4 * (1 + lowJetSq (I := I) (M := M) g 3 P) :=
        mul_le_mul_of_nonneg_left
          (add_le_add le_rfl
            (jet_mono (I := I) (M := M) g (by omega : 2 ≤ 3) P))
          hK4
      _ = K4 * (1 + lowJetSq (I := I) (M := M) g 3 P) ^ 1 := by
        rw [pow_one]
  have hS2 : H2Poly (I := I) (M := M) g P 1 Ks2
      (slotExtendIter (I := I) (M := M) g 0 3 2
        (metricConnDiffLoweredCc (I := I) (M := M) g g₁ g)) := by
    simpa only [Ks2, fr] using
      hp_slot2 (I := I) (M := M) g P hMcd
  have hS3 : H2Poly (I := I) (M := M) g P 1 Ks3
      (slotExtendIter (I := I) (M := M) g 0 3 3
        (metricConnDiffLoweredCc (I := I) (M := M) g g₁ g)) := by
    simpa only [Ks3, fr] using
      hp_slot3 (I := I) (M := M) g P hMcd
  have hHalf (σ : Equiv.Perm (Fin 4)) :
      H2Poly (I := I) (M := M) g P 5 Khalf
        (lc0AMixHalfRF (I := I) (M := M) g g₁ g σ) := by
    have hTail :=
      hp_app_of (I := I) (M := M) g P Ca hCa
        (happA
          (lc0TraceRF (I := I) (M := M) g g₁ 3 lieCorr0AMixPermQ)
          (slotExtendIter (I := I) (M := M) g 0 3 2
            (metricConnDiffLoweredCc (I := I) (M := M) g g₁ g)))
        hT3 hS2
    have hMid :=
      hp_app_of (I := I) (M := M) g P Cb hCb
        (happB
          (slotExtendIter (I := I) (M := M) g 0 3 3
            (metricConnDiffLoweredCc (I := I) (M := M) g g₁ g))
          (appCcRS (I := I) (M := M) g 2 5 3
            (lc0TraceRF (I := I) (M := M) g g₁ 3 lieCorr0AMixPermQ)
            (slotExtendIter (I := I) (M := M) g 0 3 2
              (metricConnDiffLoweredCc (I := I) (M := M) g g₁ g))))
        hS3 hTail
    have hTraced :=
      hp_app_of (I := I) (M := M) g P Cc hCc
        (happC
          (lc0TraceRF (I := I) (M := M) g g₁ 4 lieCorr0AMixPerm1)
          (appCcRS (I := I) (M := M) g 2 3 6
            (slotExtendIter (I := I) (M := M) g 0 3 3
              (metricConnDiffLoweredCc (I := I) (M := M) g g₁ g))
            (appCcRS (I := I) (M := M) g 2 5 3
              (lc0TraceRF (I := I) (M := M) g g₁ 3 lieCorr0AMixPermQ)
              (slotExtendIter (I := I) (M := M) g 0 3 2
                (metricConnDiffLoweredCc (I := I) (M := M) g g₁ g)))))
        hT4 hMid
    have hLast :=
      hp_app_of (I := I) (M := M) g P Cd hCd
        (happD
          (lc0TraceRF (I := I) (M := M) g g₁ 2 σ)
          (appCcRS (I := I) (M := M) g 2 6 4
            (lc0TraceRF (I := I) (M := M) g g₁ 4 lieCorr0AMixPerm1)
            (appCcRS (I := I) (M := M) g 2 3 6
              (slotExtendIter (I := I) (M := M) g 0 3 3
                (metricConnDiffLoweredCc (I := I) (M := M) g g₁ g))
              (appCcRS (I := I) (M := M) g 2 5 3
                (lc0TraceRF (I := I) (M := M) g g₁ 3 lieCorr0AMixPermQ)
                (slotExtendIter (I := I) (M := M) g 0 3 2
                  (metricConnDiffLoweredCc (I := I) (M := M) g g₁ g))))))
        (hT2 σ) hTraced
    simpa only [lc0AMixHalfRF, Ktail, Kmid, Ktraced, Khalf,
      Nat.reduceAdd] using hLast
  have hSum :=
    hp_add (I := I) (M := M) g P
      (hHalf lieCorr0AMixPerm2)
      (hHalf (lc0SwapPermRF * lieCorr0AMixPerm2))
  have hScaled :=
    hp_smul (I := I) (M := M) g P (2 : ℝ) hSum
  rw [amix_refold_rf (I := I) (M := M) g g₁ g]
  simpa only [lc0AMixFormRF, Ksum, K, Nat.reduceAdd] using hScaled.2

private theorem grad_jet2
    (g : SmoothRiemannianMetric I M) {s : ℕ}
    (W : SmoothCcTensor g 0 s) :
    lowJetSq (I := I) (M := M) g 2
        (iteratedCovGrad (I := I) g 0 s 1 W) ≤
      lowJetSq (I := I) (M := M) g 3 W := by
  have h0 := icg_comp_norm (I := I) (M := M) g s 1 0 W
  have h1 := icg_comp_norm (I := I) (M := M) g s 1 1 W
  have h2 := icg_comp_norm (I := I) (M := M) g s 1 2 W
  unfold lowJetSq
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    Nat.reduceAdd] at h0 h1 h2 ⊢
  rw [h0, h1, h2]
  nlinarith [sq_nonneg ‖W‖]

private theorem grad_jet1
    (g : SmoothRiemannianMetric I M) {s : ℕ}
    (W : SmoothCcTensor g 0 s) :
    lowJetSq (I := I) (M := M) g 1
        (iteratedCovGrad (I := I) g 0 s 1 W) ≤
      lowJetSq (I := I) (M := M) g 2 W := by
  have h0 := icg_comp_norm (I := I) (M := M) g s 1 0 W
  have h1 := icg_comp_norm (I := I) (M := M) g s 1 1 W
  unfold lowJetSq
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    Nat.reduceAdd] at h0 h1 ⊢
  rw [h0, h1]
  nlinarith [sq_nonneg ‖W‖]

/-- In dimension three, the first-order smooth-core action maps an `H3` jet
to an `H2` jet under one common `H2` coefficient envelope. -/
theorem a1_h3_h2
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (A : LowBaseActionData g) (W : SmoothCcTensor g 0 2)
        (B D : ℝ), 0 ≤ B → 0 ≤ D →
        lowJetSq (I := I) (M := M) g 2 A.C0 +
            lowJetSq (I := I) (M := M) g 2 A.C1 ≤ B ^ 2 →
        lowJetSq (I := I) (M := M) g 3 W ≤ D ^ 2 →
        lowJetSq (I := I) (M := M) g 2
            (A.a1 (I := I) (M := M) W) ≤ (C * B * D) ^ 2 := by
  obtain ⟨C0, hC0, happ0⟩ :=
    appCc_h2_h2_h2 (I := I) (M := M) hDim g 2 2
  obtain ⟨C1, hC1, happ1⟩ :=
    appCc_h2_h2_h2 (I := I) (M := M) hDim g 3 2
  let C : ℝ := 2 * (C0 + C1)
  refine ⟨C, mul_nonneg (by norm_num) (add_nonneg hC0 hC1), ?_⟩
  intro A W B D hB hD hA hW
  have hA0 : lowJetSq (I := I) (M := M) g 2 A.C0 ≤ B ^ 2 := by
    nlinarith [jet_nonneg (I := I) (M := M) (m := 2) g A.C1]
  have hA1 : lowJetSq (I := I) (M := M) g 2 A.C1 ≤ B ^ 2 := by
    nlinarith [jet_nonneg (I := I) (M := M) (m := 2) g A.C0]
  have hW2 : lowJetSq (I := I) (M := M) g 2 W ≤ D ^ 2 :=
    (jet_mono (I := I) (M := M) g (by omega : 2 ≤ 3) W).trans hW
  have hGW : lowJetSq (I := I) (M := M) g 2
      (iteratedCovGrad (I := I) g 0 2 1 W) ≤ D ^ 2 :=
    (grad_jet2 (I := I) (M := M) g W).trans hW
  have hY0 : lowJetSq (I := I) (M := M) g 2
      (appCc (I := I) (M := M) g 2 2 A.C0 W) ≤
        (C0 * B * D) ^ 2 := by
    simpa only [lowJetSq, Nat.reduceAdd] using
      happ0 A.C0 W B D hB hD
        (by simpa only [lowJetSq, Nat.reduceAdd] using hA0)
        (by simpa only [lowJetSq, Nat.reduceAdd] using hW2)
  have hY1 : lowJetSq (I := I) (M := M) g 2
      (appCc (I := I) (M := M) g 3 2 A.C1
        (iteratedCovGrad (I := I) g 0 2 1 W)) ≤
        (C1 * B * D) ^ 2 := by
    simpa only [lowJetSq, Nat.reduceAdd] using
      happ1 A.C1 (iteratedCovGrad (I := I) g 0 2 1 W)
        B D hB hD
        (by simpa only [lowJetSq, Nat.reduceAdd] using hA1)
        (by simpa only [lowJetSq, Nat.reduceAdd] using hGW)
  have hcoef :
      2 * (C0 ^ 2 + C1 ^ 2) ≤ (2 * (C0 + C1)) ^ 2 := by
    nlinarith [mul_nonneg hC0 hC1]
  rw [LowBaseActionData.a1]
  calc
    lowJetSq (I := I) (M := M) g 2
        (appCc (I := I) (M := M) g 2 2 A.C0 W +
          appCc (I := I) (M := M) g 3 2 A.C1
            (iteratedCovGrad (I := I) g 0 2 1 W)) ≤
        2 * (lowJetSq (I := I) (M := M) g 2
            (appCc (I := I) (M := M) g 2 2 A.C0 W) +
          lowJetSq (I := I) (M := M) g 2
            (appCc (I := I) (M := M) g 3 2 A.C1
              (iteratedCovGrad (I := I) g 0 2 1 W))) :=
      jet_add (I := I) (M := M) g 2 _ _
    _ ≤ 2 * ((C0 * B * D) ^ 2 + (C1 * B * D) ^ 2) :=
      mul_le_mul_of_nonneg_left (add_le_add hY0 hY1) (by norm_num)
    _ = (2 * (C0 ^ 2 + C1 ^ 2)) * (B * D) ^ 2 := by ring
    _ ≤ (2 * (C0 + C1)) ^ 2 * (B * D) ^ 2 :=
      mul_le_mul_of_nonneg_right hcoef (sq_nonneg _)
    _ = (C * B * D) ^ 2 := by simp only [C]; ring

/-- In dimension three, the same first-order smooth-core action maps an `H2`
jet to an `H1` jet under the same kind of `H2` coefficient envelope. -/
theorem a1_h2_h1
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (A : LowBaseActionData g) (W : SmoothCcTensor g 0 2)
        (B D : ℝ), 0 ≤ B → 0 ≤ D →
        lowJetSq (I := I) (M := M) g 2 A.C0 +
            lowJetSq (I := I) (M := M) g 2 A.C1 ≤ B ^ 2 →
        lowJetSq (I := I) (M := M) g 2 W ≤ D ^ 2 →
        lowJetSq (I := I) (M := M) g 1
            (A.a1 (I := I) (M := M) W) ≤ (C * B * D) ^ 2 := by
  obtain ⟨C0, hC0, happ0⟩ :=
    appRS_h2_h1_h1 (I := I) (M := M) hDim g 0 2 2
  obtain ⟨C1, hC1, happ1⟩ :=
    appRS_h2_h1_h1 (I := I) (M := M) hDim g 0 3 2
  let C : ℝ := 2 * (C0 + C1)
  refine ⟨C, mul_nonneg (by norm_num) (add_nonneg hC0 hC1), ?_⟩
  intro A W B D hB hD hA hW
  have hA0 : lowJetSq (I := I) (M := M) g 2 A.C0 ≤ B ^ 2 := by
    nlinarith [jet_nonneg (I := I) (M := M) (m := 2) g A.C1]
  have hA1 : lowJetSq (I := I) (M := M) g 2 A.C1 ≤ B ^ 2 := by
    nlinarith [jet_nonneg (I := I) (M := M) (m := 2) g A.C0]
  have hW1 : lowJetSq (I := I) (M := M) g 1 W ≤ D ^ 2 :=
    (jet_mono (I := I) (M := M) g (by omega : 1 ≤ 2) W).trans hW
  have hGW : lowJetSq (I := I) (M := M) g 1
      (iteratedCovGrad (I := I) g 0 2 1 W) ≤ D ^ 2 :=
    (grad_jet1 (I := I) (M := M) g W).trans hW
  let Y0 : SmoothCcTensor g 0 2 :=
    appCc (I := I) (M := M) g 2 2 A.C0 W
  let Y1 : SmoothCcTensor g 0 2 :=
    appCc (I := I) (M := M) g 3 2 A.C1
      (iteratedCovGrad (I := I) g 0 2 1 W)
  have hY0norm :
      ‖(⟨Y0⟩ : SmoothCcTensorH1 g 0 2)‖ ≤ C0 * B * D := by
    simpa only [Y0, appCcRS_zero_eq_appCc] using
      happ0 A.C0 W B D hB hD
        (by simpa only [lowJetSq, Nat.reduceAdd] using hA0)
        (by simpa only [lowJetSq, Nat.reduceAdd] using hW1)
  have hY1norm :
      ‖(⟨Y1⟩ : SmoothCcTensorH1 g 0 2)‖ ≤ C1 * B * D := by
    simpa only [Y1, appCcRS_zero_eq_appCc] using
      happ1 A.C1 (iteratedCovGrad (I := I) g 0 2 1 W)
        B D hB hD
        (by simpa only [lowJetSq, Nat.reduceAdd] using hA1)
        (by simpa only [lowJetSq, Nat.reduceAdd] using hGW)
  have hY0 : lowJetSq (I := I) (M := M) g 1 Y0 ≤
      (C0 * B * D) ^ 2 := by
    have hsq := pow_le_pow_left₀
      (norm_nonneg (⟨Y0⟩ : SmoothCcTensorH1 g 0 2)) hY0norm 2
    rw [h1_jet_sq (I := I) (M := M) g 0 2 Y0] at hsq
    simpa only [lowJetSq, Finset.sum_range_succ,
      Finset.sum_range_zero, zero_add, Nat.reduceAdd,
      iteratedCovGrad_zero, iteratedCovGrad_succ] using hsq
  have hY1 : lowJetSq (I := I) (M := M) g 1 Y1 ≤
      (C1 * B * D) ^ 2 := by
    have hsq := pow_le_pow_left₀
      (norm_nonneg (⟨Y1⟩ : SmoothCcTensorH1 g 0 2)) hY1norm 2
    rw [h1_jet_sq (I := I) (M := M) g 0 2 Y1] at hsq
    simpa only [lowJetSq, Finset.sum_range_succ,
      Finset.sum_range_zero, zero_add, Nat.reduceAdd,
      iteratedCovGrad_zero, iteratedCovGrad_succ] using hsq
  have hcoef :
      2 * (C0 ^ 2 + C1 ^ 2) ≤ (2 * (C0 + C1)) ^ 2 := by
    nlinarith [mul_nonneg hC0 hC1]
  change lowJetSq (I := I) (M := M) g 1 (Y0 + Y1) ≤ _
  calc
    lowJetSq (I := I) (M := M) g 1 (Y0 + Y1) ≤
        2 * (lowJetSq (I := I) (M := M) g 1 Y0 +
          lowJetSq (I := I) (M := M) g 1 Y1) :=
      jet_add (I := I) (M := M) g 1 Y0 Y1
    _ ≤ 2 * ((C0 * B * D) ^ 2 + (C1 * B * D) ^ 2) :=
      mul_le_mul_of_nonneg_left (add_le_add hY0 hY1) (by norm_num)
    _ = (2 * (C0 ^ 2 + C1 ^ 2)) * (B * D) ^ 2 := by ring
    _ ≤ (2 * (C0 + C1)) ^ 2 * (B * D) ^ 2 :=
      mul_le_mul_of_nonneg_right hcoef (sq_nonneg _)
    _ = (C * B * D) ^ 2 := by simp only [C]; ring

end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry
