import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderLowBaseAction
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderLowBaseC2Lip
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.PrincipalLowRegCore
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.LieCorr0CoeffDiffRadiusFree
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.DeTurckVFEndoInsertTopSep

/-!
# Low-base moving-connection coefficient Lipschitz estimates

This module develops the fixed-order two-endpoint estimate for the
background-lowered connection arm.  The exact algebra first lowers the
connection difference by one moving endpoint and then raises that last slot
back with the same endpoint inverse.  This avoids differentiating a
two-endpoint inverse resolvent.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped BigOperators Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E :=
  FiniteDimensional.complete ℝ E

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
    [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private theorem unit_sub
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (S V : SmoothCcTensor g 0 s) (x : M) :
    unitModel (I := I) (M := M) g s (S - V) x =
      unitModel (I := I) (M := M) g s S x -
        unitModel (I := I) (M := M) g s V x := by
  rw [unitModel, unitModel, unitModel]
  have hsec : (S - V).toSection x = S.toSection x - V.toSection x := by
    rw [SmoothCcTensor.toSection_sub]
    rfl
  rw [show ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
          (S - V).toSection x) (unitTensor (I := I) (M := M) x)) =
        (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
          S.toSection x) (unitTensor (I := I) (M := M) x) -
        (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
          V.toSection x) (unitTensor (I := I) (M := M) x) from by
    rw [hsec]
    rfl]
  rw [Tensor0SSpace.toModel_sub]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
    [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private theorem unit_add
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (S V : SmoothCcTensor g 0 s) (x : M) :
    unitModel (I := I) (M := M) g s (S + V) x =
      unitModel (I := I) (M := M) g s S x +
        unitModel (I := I) (M := M) g s V x := by
  rw [unitModel, unitModel, unitModel]
  have hsec : (S + V).toSection x = S.toSection x + V.toSection x := by
    rw [SmoothCcTensor.toSection_add]
    rfl
  rw [show ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
          (S + V).toSection x) (unitTensor (I := I) (M := M) x)) =
        (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
          S.toSection x) (unitTensor (I := I) (M := M) x) +
        (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
          V.toSection x) (unitTensor (I := I) (M := M) x) from by
    rw [hsec]
    rfl]
  rw [Tensor0SSpace.toModel_add]

private noncomputable def fullSlot3
    (g gm : SmoothRiemannianMetric I M) : SmoothCcTensor g 3 3 :=
  slotInsertEndoCc (I := I) (M := M) g 2
    (fullRaisedEndoField (I := I) (M := M) g gm)

private def lowPerm : Equiv.Perm (Fin 3) :=
  ⟨![2, 0, 1], ![1, 2, 0], by decide, by decide⟩

private noncomputable def raiseLast
    (g gm : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g 0 3) : SmoothCcTensor g 0 3 :=
  domDomCongrSection (I := I) g lowPerm
    (appCc (I := I) (M := M) g 3 3
      (fullSlot3 (I := I) (M := M) g gm)
      (domDomCongrSection (I := I) g (finRotate 3) S))

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

private theorem kappa_split
    (g gm : SmoothRiemannianMetric I M)
    (P : SmoothCcTensor g 0 2)
    (htie : ∀ (x : M) (v w : TangentSpace I x),
      gm.inner x v w =
        g.inner x v w + ccTensorBilinSymm (I := I) g P x v w) :
    lc0Kappa (I := I) (M := M) g gm g =
      connDiffLoweredCc (I := I) g gm +
        lc0PbLow (I := I) (M := M) g P gm g := by
  refine smoothCcTensor_ext_of_unitModel (I := I) (M := M) g fun x => ?_
  refine ContinuousMultilinearMap.ext fun v => ?_
  rw [kappa_unit (I := I) (M := M)]
  rw [unit_add (I := I) (M := M), ContinuousMultilinearMap.add_apply]
  rw [connDiffLoweredCc_unitModel_apply',
    pbLow_unit (I := I) (M := M)]
  exact htie x
    (PDE.DeTurck.connDiff (I := I) gm g x (v 0) (v 1)) (v 2)

private theorem pb_eq_corr
    (g gm : SmoothRiemannianMetric I M)
    (P : SmoothCcTensor g 0 2)
    (htie : ∀ (x : M) (v w : TangentSpace I x),
      gm.inner x v w =
        g.inner x v w + ccTensorBilinSymm (I := I) g P x v w) :
    lc0PbLow (I := I) (M := M) g P gm g =
      metricLowerCorr (I := I) (M := M) g gm g P := by
  have hk := kappa_split (I := I) (M := M) g gm P htie
  have hm := mcd_lower_split (I := I) (M := M) g gm g P htie
  rw [wXi_self_eq (I := I) (M := M) g gm] at hm
  exact add_left_cancel (hk.symm.trans hm)

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

private noncomputable def koszulOp
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

private noncomputable def kappaOp
    (g : SmoothRiemannianMetric I M) : SmoothCcTensor g 3 3 :=
  appCcRS (I := I) (M := M) g 3 3 3
    (permCoeff (I := I) (M := M) g (finRotate 3).symm)
    (koszulOp (I := I) (M := M) g)

private theorem kappaOp_app
    (g gm : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    (hT : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g T x u v =
        ccTensorBilin (I := I) g T x v u)
    (htie : ∀ (x : M) (u v : TangentSpace I x),
      gm.inner x u v =
        g.inner x u v + ccTensorBilinSymm (I := I) g T x u v) :
    appCcRS (I := I) (M := M) g 0 3 3
        (kappaOp (I := I) (M := M) g)
        (covGrad (I := I) (M := M) g 0 2 T) =
      lc0Kappa (I := I) (M := M) g gm g := by
  rw [appCcRS_zero_eq_appCc, kappaOp, ← appCc_assoc]
  rw [show appCc (I := I) (M := M) g 3 3
      (koszulOp (I := I) (M := M) g)
      (covGrad (I := I) (M := M) g 0 2 T) =
        koszulCovecCc (I := I) g T by
      rw [← appCcRS_zero_eq_appCc]
      exact koszulOp_app (I := I) (M := M) g T hT]
  rw [← appCcRS_zero_eq_appCc, permCoeff_app]
  exact (kappa_self (I := I) (M := M) g gm T htie).symm

private theorem kappa_pair
    (g gT gU : SmoothRiemannianMetric I M)
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
        g.inner x u v + ccTensorBilinSymm (I := I) g U x u v) :
    lc0Kappa (I := I) (M := M) g gT g -
        lc0Kappa (I := I) (M := M) g gU g =
      appCcRS (I := I) (M := M) g 0 3 3
        (kappaOp (I := I) (M := M) g)
        (covGrad (I := I) (M := M) g 0 2 (T - U)) := by
  rw [← kappaOp_app (I := I) (M := M) g gT T hT hTtie,
    ← kappaOp_app (I := I) (M := M) g gU U hU hUtie]
  rw [← appCcRS_sub_right, ← covGrad_sub]

private theorem moving_pair
    (g gT gU : SmoothRiemannianMetric I M)
    (T U : SmoothCcTensor g 0 2)
    (hTtie : ∀ (x : M) (v w : TangentSpace I x),
      gT.inner x v w =
        g.inner x v w + ccTensorBilinSymm (I := I) g T x v w)
    (hUtie : ∀ (x : M) (v w : TangentSpace I x),
      gU.inner x v w =
        g.inner x v w + ccTensorBilinSymm (I := I) g U x v w) :
    raiseLast (I := I) (M := M) g gU
        (lc0Kappa (I := I) (M := M) g gT g -
          lc0Kappa (I := I) (M := M) g gU g -
          lc0PbLow (I := I) (M := M) g (T - U) gT g) =
      connDiffLoweredCc (I := I) g gT -
        connDiffLoweredCc (I := I) g gU := by
  refine smoothCcTensor_ext_of_unitModel (I := I) (M := M) g fun x => ?_
  refine ContinuousMultilinearMap.ext fun v => ?_
  rw [raiseLast, domDomCongrSection_unitModel,
    ContinuousMultilinearMap.domDomCongr_apply]
  have hv₀ : (fun i => v (lowPerm i)) = ![v 2, v 0, v 1] := by
    funext i
    fin_cases i <;> rfl
  rw [hv₀]
  rw [unitModel, appCc_toSection, ContinuousLinearMap.comp_apply]
  simp only [fullSlot3, slotInsertEndoCc_toSection]
  rw [slotInsertEndoFib_apply_eval]
  have hv :
      Function.update ![v 2, v 0, v 1] 0
          (fullRaisedEndoField (I := I) (M := M) g gU x (v 2)) =
        ![fullRaisedEndoField (I := I) (M := M) g gU x (v 2),
          v 0, v 1] := by
    funext i
    fin_cases i <;> simp
  simp only [Matrix.cons_val_zero]
  rw [hv]
  rw [show Tensor0SSpace.toModel
      ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
        (domDomCongrSection (I := I) g (finRotate 3)
          (lc0Kappa (I := I) (M := M) g gT g -
            lc0Kappa (I := I) (M := M) g gU g -
            lc0PbLow (I := I) (M := M) g (T - U) gT g)).toSection x)
        (unitTensor (I := I) (M := M) x))
      ![fullRaisedEndoField (I := I) (M := M) g gU x (v 2),
        v 0, v 1] =
      unitModel (I := I) (M := M) g 3
        (domDomCongrSection (I := I) g (finRotate 3)
          (lc0Kappa (I := I) (M := M) g gT g -
            lc0Kappa (I := I) (M := M) g gU g -
            lc0PbLow (I := I) (M := M) g (T - U) gT g)) x
        ![fullRaisedEndoField (I := I) (M := M) g gU x (v 2),
          v 0, v 1] from rfl]
  rw [domDomCongrSection_unitModel,
    ContinuousMultilinearMap.domDomCongr_apply]
  have hv₁ :
      (fun i =>
        (![fullRaisedEndoField (I := I) (M := M) g gU x (v 2),
          v 0, v 1] : Fin 3 → TangentSpace I x) ((finRotate 3) i)) =
        ![v 0, v 1,
          fullRaisedEndoField (I := I) (M := M) g gU x (v 2)] := by
    funext i
    fin_cases i <;> simp [finRotate_succ_apply]
  rw [hv₁]
  rw [unit_sub (I := I) (M := M), unit_sub (I := I) (M := M)]
  simp only [ContinuousMultilinearMap.sub_apply]
  rw [kappa_unit (I := I) (M := M), kappa_unit (I := I) (M := M),
    pbLow_unit (I := I) (M := M)]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  have hTU :
      ccTensorBilinSymm (I := I) g (T - U) x
          (PDE.DeTurck.connDiff (I := I) gT g x (v 0) (v 1))
          (fullRaisedEndoField (I := I) (M := M) g gU x (v 2)) =
        gT.inner x
            (PDE.DeTurck.connDiff (I := I) gT g x (v 0) (v 1))
            (fullRaisedEndoField (I := I) (M := M) g gU x (v 2)) -
          gU.inner x
            (PDE.DeTurck.connDiff (I := I) gT g x (v 0) (v 1))
            (fullRaisedEndoField (I := I) (M := M) g gU x (v 2)) := by
    rw [ccTensorBilinSymm_sub, hTtie, hUtie]
    ring
  rw [hTU]
  rw [show
      gT.inner x
            (PDE.DeTurck.connDiff (I := I) gT g x (v 0) (v 1))
            (fullRaisedEndoField (I := I) (M := M) g gU x (v 2)) -
          gU.inner x
            (PDE.DeTurck.connDiff (I := I) gU g x (v 0) (v 1))
            (fullRaisedEndoField (I := I) (M := M) g gU x (v 2)) -
        (gT.inner x
            (PDE.DeTurck.connDiff (I := I) gT g x (v 0) (v 1))
            (fullRaisedEndoField (I := I) (M := M) g gU x (v 2)) -
          gU.inner x
            (PDE.DeTurck.connDiff (I := I) gT g x (v 0) (v 1))
            (fullRaisedEndoField (I := I) (M := M) g gU x (v 2))) =
        gU.inner x
          (PDE.DeTurck.connDiff (I := I) gT g x (v 0) (v 1) -
            PDE.DeTurck.connDiff (I := I) gU g x (v 0) (v 1))
          (fullRaisedEndoField (I := I) (M := M) g gU x (v 2)) by
    rw [map_sub, ContinuousLinearMap.sub_apply]
    ring]
  rw [gU.symm x
    (PDE.DeTurck.connDiff (I := I) gT g x (v 0) (v 1) -
      PDE.DeTurck.connDiff (I := I) gU g x (v 0) (v 1))
    (fullRaisedEndoField (I := I) (M := M) g gU x (v 2))]
  rw [map_sub, raised_inner (I := I) (M := M),
    raised_inner (I := I) (M := M)]
  rw [g.symm x (v 2)
      (PDE.DeTurck.connDiff (I := I) gT g x (v 0) (v 1)),
    g.symm x (v 2)
      (PDE.DeTurck.connDiff (I := I) gU g x (v 0) (v 1))]
  rw [unit_sub (I := I) (M := M), ContinuousMultilinearMap.sub_apply,
    connDiffLoweredCc_unitModel_apply',
    connDiffLoweredCc_unitModel_apply']

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

private def corrPermA : Equiv.Perm (Fin 5) :=
  ⟨![2, 3, 0, 1, 4], ![2, 3, 0, 1, 4], by decide, by decide⟩

private def corrPermB : Equiv.Perm (Fin 5) :=
  ⟨![2, 3, 0, 4, 1], ![2, 4, 0, 1, 3], by decide, by decide⟩

private noncomputable def corrPk3
    (g : SmoothRiemannianMetric I M) (P : SmoothCcTensor g 0 2) :
    SmoothCcTensor g 3 5 :=
  slotExtend (I := I) (M := M) g 2 4
    (slotExtend (I := I) (M := M) g 1 3
      (slotExtend (I := I) (M := M) g 0 2 P))

private noncomputable def corrPhi
    (g : SmoothRiemannianMetric I M) (P : SmoothCcTensor g 0 2)
    (σ : Equiv.Perm (Fin 5)) : SmoothCcTensor g 3 3 :=
  appCcRS (I := I) (M := M) g 3 5 3
    (reindexCoeffGen (I := I) (M := M) g 5 3
      (cometricDoubleTraceField (I := I) g 3) σ)
    (corrPk3 (I := I) (M := M) g P)

private theorem corr_formula
    (g gm g_bg : SmoothRiemannianMetric I M)
    (P : SmoothCcTensor g 0 2) :
    metricLowerCorr (I := I) (M := M) g gm g_bg P =
      (1 / 2 : ℝ) • appCc (I := I) (M := M) g 3 3
          (corrPhi (I := I) (M := M) g P corrPermA)
          (wXi (I := I) (M := M) g gm g_bg) +
        (1 / 2 : ℝ) • appCc (I := I) (M := M) g 3 3
          (corrPhi (I := I) (M := M) g P corrPermB)
          (wXi (I := I) (M := M) g gm g_bg) := by
  rfl

private theorem corr_cross
    (g gT gU : SmoothRiemannianMetric I M)
    (U : SmoothCcTensor g 0 2) :
    metricLowerCorr (I := I) (M := M) g gT g U -
        metricLowerCorr (I := I) (M := M) g gU g U =
      -metricLowerCorr (I := I) (M := M) g gU gT U := by
  let WT : SmoothCcTensor g 0 3 :=
    wXi (I := I) (M := M) g gT g
  let WU : SmoothCcTensor g 0 3 :=
    wXi (I := I) (M := M) g gU g
  let WC : SmoothCcTensor g 0 3 :=
    wXi (I := I) (M := M) g gU gT
  have hW : WT - WU = -WC := by
    simp only [WT, WU, WC, wXi]
    module
  have hA := app_sub_right (I := I) (M := M) g 3 3
    (corrPhi (I := I) (M := M) g U corrPermA) WT WU
  have hB := app_sub_right (I := I) (M := M) g 3 3
    (corrPhi (I := I) (M := M) g U corrPermB) WT WU
  have hAn := appCc_smul_right (I := I) (M := M) g 3 3
    (-1 : ℝ) (corrPhi (I := I) (M := M) g U corrPermA) WC
  have hBn := appCc_smul_right (I := I) (M := M) g 3 3
    (-1 : ℝ) (corrPhi (I := I) (M := M) g U corrPermB) WC
  simp only [neg_one_smul] at hAn hBn
  have hA' :
      appCc (I := I) (M := M) g 3 3
          (corrPhi (I := I) (M := M) g U corrPermA) WT -
        appCc (I := I) (M := M) g 3 3
          (corrPhi (I := I) (M := M) g U corrPermA) WU =
      -appCc (I := I) (M := M) g 3 3
        (corrPhi (I := I) (M := M) g U corrPermA) WC := by
    rw [← hA, hW, hAn]
  have hB' :
      appCc (I := I) (M := M) g 3 3
          (corrPhi (I := I) (M := M) g U corrPermB) WT -
        appCc (I := I) (M := M) g 3 3
          (corrPhi (I := I) (M := M) g U corrPermB) WU =
      -appCc (I := I) (M := M) g 3 3
        (corrPhi (I := I) (M := M) g U corrPermB) WC := by
    rw [← hB, hW, hBn]
  rw [corr_formula (I := I) (M := M) g gT g U,
    corr_formula (I := I) (M := M) g gU g U,
    corr_formula (I := I) (M := M) g gU gT U]
  change
    ((1 / 2 : ℝ) • appCc (I := I) (M := M) g 3 3
          (corrPhi (I := I) (M := M) g U corrPermA) WT +
        (1 / 2 : ℝ) • appCc (I := I) (M := M) g 3 3
          (corrPhi (I := I) (M := M) g U corrPermB) WT) -
      ((1 / 2 : ℝ) • appCc (I := I) (M := M) g 3 3
          (corrPhi (I := I) (M := M) g U corrPermA) WU +
        (1 / 2 : ℝ) • appCc (I := I) (M := M) g 3 3
          (corrPhi (I := I) (M := M) g U corrPermB) WU) =
    -((1 / 2 : ℝ) • appCc (I := I) (M := M) g 3 3
          (corrPhi (I := I) (M := M) g U corrPermA) WC +
        (1 / 2 : ℝ) • appCc (I := I) (M := M) g 3 3
          (corrPhi (I := I) (M := M) g U corrPermB) WC)
  calc
    _ = (1 / 2 : ℝ) •
          (appCc (I := I) (M := M) g 3 3
              (corrPhi (I := I) (M := M) g U corrPermA) WT -
            appCc (I := I) (M := M) g 3 3
              (corrPhi (I := I) (M := M) g U corrPermA) WU) +
        (1 / 2 : ℝ) •
          (appCc (I := I) (M := M) g 3 3
              (corrPhi (I := I) (M := M) g U corrPermB) WT -
            appCc (I := I) (M := M) g 3 3
              (corrPhi (I := I) (M := M) g U corrPermB) WU) := by
      module
    _ = _ := by rw [hA', hB']; module

private theorem raise_cross
    (g gT gU : SmoothRiemannianMetric I M) :
    raiseLast (I := I) (M := M) g gU
        (-lc0Kappa (I := I) (M := M) g gU gT) =
      connDiffLoweredCc (I := I) g gT -
        connDiffLoweredCc (I := I) g gU := by
  refine smoothCcTensor_ext_of_unitModel (I := I) (M := M) g fun x => ?_
  refine ContinuousMultilinearMap.ext fun v => ?_
  rw [raiseLast, domDomCongrSection_unitModel,
    ContinuousMultilinearMap.domDomCongr_apply]
  have hv₀ : (fun i => v (lowPerm i)) = ![v 2, v 0, v 1] := by
    funext i
    fin_cases i <;> rfl
  rw [hv₀]
  rw [unitModel, appCc_toSection, ContinuousLinearMap.comp_apply]
  simp only [fullSlot3, slotInsertEndoCc_toSection]
  rw [slotInsertEndoFib_apply_eval]
  simp only [Matrix.cons_val_zero]
  have hv :
      Function.update ![v 2, v 0, v 1] 0
          (fullRaisedEndoField (I := I) (M := M) g gU x (v 2)) =
        ![fullRaisedEndoField (I := I) (M := M) g gU x (v 2),
          v 0, v 1] := by
    funext i
    fin_cases i <;> simp
  rw [hv]
  rw [show Tensor0SSpace.toModel
      ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
        (domDomCongrSection (I := I) g (finRotate 3)
          (-lc0Kappa (I := I) (M := M) g gU gT)).toSection x)
        (unitTensor (I := I) (M := M) x))
      ![fullRaisedEndoField (I := I) (M := M) g gU x (v 2),
        v 0, v 1] =
      unitModel (I := I) (M := M) g 3
        (domDomCongrSection (I := I) g (finRotate 3)
          (-lc0Kappa (I := I) (M := M) g gU gT)) x
        ![fullRaisedEndoField (I := I) (M := M) g gU x (v 2),
          v 0, v 1] from rfl]
  rw [domDomCongrSection_unitModel,
    ContinuousMultilinearMap.domDomCongr_apply]
  have hv₁ :
      (fun i =>
        (![fullRaisedEndoField (I := I) (M := M) g gU x (v 2),
          v 0, v 1] : Fin 3 → TangentSpace I x) ((finRotate 3) i)) =
        ![v 0, v 1,
          fullRaisedEndoField (I := I) (M := M) g gU x (v 2)] := by
    funext i
    fin_cases i <;> simp [finRotate_succ_apply]
  rw [hv₁]
  rw [show unitModel (I := I) (M := M) g 3
      (-lc0Kappa (I := I) (M := M) g gU gT) x =
      -unitModel (I := I) (M := M) g 3
        (lc0Kappa (I := I) (M := M) g gU gT) x by
    simp only [unitModel]
    rw [SmoothCcTensor.toSection_neg, ContMDiffSection.coe_neg,
      Pi.neg_apply, ContinuousLinearMap.neg_apply,
      Tensor0SSpace.toModel_neg]]
  rw [ContinuousMultilinearMap.neg_apply,
    kappa_unit (I := I) (M := M)]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  rw [gU.symm x
    (PDE.DeTurck.connDiff (I := I) gU gT x (v 0) (v 1))
    (fullRaisedEndoField (I := I) (M := M) g gU x (v 2))]
  rw [raised_inner (I := I) (M := M)]
  rw [g.symm x (v 2)
    (PDE.DeTurck.connDiff (I := I) gU gT x (v 0) (v 1))]
  have hc := PDE.DeTurck.connDiff_cocycle
    (I := I) gT gU g x (v 0) (v 1)
  rw [unit_sub (I := I) (M := M), ContinuousMultilinearMap.sub_apply,
    connDiffLoweredCc_unitModel_apply',
    connDiffLoweredCc_unitModel_apply']
  rw [hc, map_add, ContinuousLinearMap.add_apply]
  ring

private theorem moving_corr
    (g gT gU : SmoothRiemannianMetric I M)
    (T U : SmoothCcTensor g 0 2)
    (hTtie : ∀ (x : M) (v w : TangentSpace I x),
      gT.inner x v w =
        g.inner x v w + ccTensorBilinSymm (I := I) g T x v w)
    (hUtie : ∀ (x : M) (v w : TangentSpace I x),
      gU.inner x v w =
        g.inner x v w + ccTensorBilinSymm (I := I) g U x v w) :
    raiseLast (I := I) (M := M) g gU
        (lc0Kappa (I := I) (M := M) g gT g -
          lc0Kappa (I := I) (M := M) g gU g -
          metricLowerCorr (I := I) (M := M) g gT g (T - U)) =
      connDiffLoweredCc (I := I) g gT -
        connDiffLoweredCc (I := I) g gU := by
  have hmT := mcd_lower_split (I := I) (M := M) g gT g T hTtie
  have hmU := mcd_lower_split (I := I) (M := M) g gU g U hUtie
  rw [wXi_self_eq (I := I) (M := M) g gT] at hmT
  rw [wXi_self_eq (I := I) (M := M) g gU] at hmU
  have hsub := metricCorr_sub (I := I) (M := M) g gT g T U
  have hcross := corr_cross (I := I) (M := M) g gT gU U
  have hmC := mcd_lower_split (I := I) (M := M) g gU gT U hUtie
  have hwC :
      wXi (I := I) (M := M) g gU gT =
        connDiffLoweredCc (I := I) g gU -
          connDiffLoweredCc (I := I) g gT := by
    simp only [wXi]
  rw [hwC] at hmC
  have hcore :
      lc0Kappa (I := I) (M := M) g gT g -
          lc0Kappa (I := I) (M := M) g gU g -
          metricLowerCorr (I := I) (M := M) g gT g (T - U) =
        -lc0Kappa (I := I) (M := M) g gU gT := by
    change
      metricConnDiffLoweredCc (I := I) (M := M) g gT g -
          metricConnDiffLoweredCc (I := I) (M := M) g gU g -
          metricLowerCorr (I := I) (M := M) g gT g (T - U) =
        -metricConnDiffLoweredCc (I := I) (M := M) g gU gT
    rw [hmT, hmU, hsub]
    calc
      _ = (connDiffLoweredCc (I := I) g gT -
            connDiffLoweredCc (I := I) g gU) +
          (metricLowerCorr (I := I) (M := M) g gT g U -
            metricLowerCorr (I := I) (M := M) g gU g U) := by
        module
      _ = (connDiffLoweredCc (I := I) g gT -
            connDiffLoweredCc (I := I) g gU) -
          metricLowerCorr (I := I) (M := M) g gU gT U := by
        rw [hcross]
        module
      _ = -(connDiffLoweredCc (I := I) g gU -
            connDiffLoweredCc (I := I) g gT +
          metricLowerCorr (I := I) (M := M) g gU gT U) := by
        module
      _ = -metricConnDiffLoweredCc (I := I) (M := M) g gU gT := by
        rw [← hmC]
  rw [hcore]
  exact raise_cross (I := I) (M := M) g gT gU

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

private theorem jet_sub
    (g : SmoothRiemannianMetric I M) {r s : ℕ} (m : ℕ)
    (S V : SmoothCcTensor g r s) :
    lowJetSq (I := I) (M := M) g m (S - V) ≤
      2 * (lowJetSq (I := I) (M := M) g m S +
        lowJetSq (I := I) (M := M) g m V) := by
  unfold lowJetSq
  calc
    ∑ q ∈ Finset.range (m + 1),
        ‖iteratedCovGrad (I := I) g r s q (S - V)‖ ^ 2 ≤
      ∑ q ∈ Finset.range (m + 1),
        2 * (‖iteratedCovGrad (I := I) g r s q S‖ ^ 2 +
          ‖iteratedCovGrad (I := I) g r s q V‖ ^ 2) := by
      refine Finset.sum_le_sum fun q _ => ?_
      rw [iteratedCovGrad_sub]
      have htri := norm_sub_le
        (iteratedCovGrad (I := I) g r s q S)
        (iteratedCovGrad (I := I) g r s q V)
      calc
        ‖iteratedCovGrad (I := I) g r s q S -
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
    jet_nonneg (I := I) (M := M) g Φ
  have hW0 : 0 ≤ lowJetSq (I := I) (M := M) g 2 W :=
    jet_nonneg (I := I) (M := M) g W
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

set_option linter.unusedVariables false in
private theorem app_h21_mul
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
    jet_nonneg (I := I) (M := M) g Φ
  have hW0 : 0 ≤ lowJetSq (I := I) (M := M) g 1 W :=
    jet_nonneg (I := I) (M := M) g W
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

private theorem grad_h1_le_h2
    (g : SmoothRiemannianMetric I M) {r s : ℕ}
    (S : SmoothCcTensor g r s) :
    lowJetSq (I := I) (M := M) g 1
        (covGrad (I := I) (M := M) g r s S) ≤
      lowJetSq (I := I) (M := M) g 2 S := by
  have h0 := grad_l2_sq (I := I) (M := M) g r s 0 S
  have h1 := grad_l2_sq (I := I) (M := M) g r s 1 S
  unfold lowJetSq
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    Nat.reduceAdd] at h0 h1 ⊢
  rw [h0, h1]
  nlinarith [sq_nonneg ‖S‖]

private theorem dom_h2
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

private theorem dom_h1
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

set_option linter.unusedVariables false in
private theorem connSec_eq_raise
    (g gm : SmoothRiemannianMetric I M) :
    connDiffSection (I := I) gm g =
      cometricRaiseSlot0Field (I := I) (M := M) g 1
        (domDomCongrSection (I := I) g (finRotate 3)
          (connDiffLoweredCc (I := I) g gm)) := by
  apply Integral.L2.SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [connDiffSection_toSection, cometricRaiseSlot0Field_toSection]
  apply tensorRSSpace_ext 1 2 x
  intro om
  apply ContinuousMultilinearMap.ext
  intro YZ
  let u : TangentSpace I x := inverseMetricSharpFib (I := I) g x om
  let D : Tensor0SSpace 3 I x :=
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
      (domDomCongrSection (I := I) g (finRotate 3)
        (connDiffLoweredCc (I := I) g gm)).toSection x)
      (unitTensor (I := I) (M := M) x)
  have hL :
      (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from
        connDiffFib (I := I) gm g x) om YZ =
        g.inner x u (PDE.DeTurck.connDiff (I := I) gm g x
          (YZ 0) (YZ 1)) := by
    rw [connDiffFib_apply_eval]
    rw [show om (fun _ : Fin 1 =>
          PDE.DeTurck.connDiff (I := I) gm g x (YZ 0) (YZ 1)) =
        cotangentToDual (I := I) (x := x) om
          (PDE.DeTurck.connDiff (I := I) gm g x (YZ 0) (YZ 1)) from
      (cotangentToDual_apply (I := I) om _).symm]
    rw [show cotangentToDual (I := I) (x := x) om
          (PDE.DeTurck.connDiff (I := I) gm g x (YZ 0) (YZ 1)) =
        cotangentToDualLinear (I := I) (x := x) om
          (PDE.DeTurck.connDiff (I := I) gm g x (YZ 0) (YZ 1)) from rfl]
    rw [← inverseMetricSharpFib_inner (I := I) g x om
      (PDE.DeTurck.connDiff (I := I) gm g x (YZ 0) (YZ 1))]
  have hR :
      (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from
        cometricRaiseSlot0Fib (I := I) g 1 x D) om YZ =
        Tensor0SSpace.toModel D
          (Fin.cons (show E from u) (fun k => (show E from YZ k))) := by
    rw [cometricRaiseSlot0Fib_clm_apply (I := I) g 1 x D om]
    rw [show (Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) (1 + 1) x
          (inverseMetricSharpFib (I := I) g x om) D YZ : ℝ) =
        Tensor0SSpace.toModel
          (Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) (1 + 1) x
            (inverseMetricSharpFib (I := I) g x om) D) YZ from rfl]
    rw [interior_product_toModel_eval' (I := I) (M := M) (1 + 1) x
      (inverseMetricSharpFib (I := I) g x om) D YZ]
  rw [hL, hR]
  rw [show Tensor0SSpace.toModel D
        (Fin.cons (show E from u) (fun k => (show E from YZ k))) =
      unitModel (I := I) (M := M) g 3
        (domDomCongrSection (I := I) g (finRotate 3)
          (connDiffLoweredCc (I := I) g gm)) x
        ![u, YZ 0, YZ 1] from by
    rfl]
  rw [domDomCongrSection_unitModel,
    ContinuousMultilinearMap.domDomCongr_apply]
  rw [show (fun i =>
      (![u, YZ 0, YZ 1] : Fin 3 → TangentSpace I x)
        ((finRotate 3) i)) = ![YZ 0, YZ 1, u] from by
    funext i
    fin_cases i <;> simp [finRotate_succ_apply]]
  rw [connDiffLoweredCc_unitModel_apply']
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]
  exact g.symm x u
    (PDE.DeTurck.connDiff (I := I) gm g x (YZ 0) (YZ 1))

set_option linter.unusedVariables false in
private theorem dom_sub
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

set_option linter.unusedVariables false in
private theorem raise_sub
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (A B : SmoothCcTensor g 0 (s + 2)) :
    cometricRaiseSlot0Field (I := I) (M := M) g s (A - B) =
      cometricRaiseSlot0Field (I := I) (M := M) g s A -
        cometricRaiseSlot0Field (I := I) (M := M) g s B := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [show
      (cometricRaiseSlot0Field (I := I) (M := M) g s A -
        cometricRaiseSlot0Field (I := I) (M := M) g s B).toSection x =
      (cometricRaiseSlot0Field (I := I) (M := M) g s A).toSection x -
        (cometricRaiseSlot0Field (I := I) (M := M) g s B).toSection x from by
    rw [SmoothCcTensor.toSection_sub]
    rfl]
  rw [cometricRaiseSlot0Field_toSection,
    cometricRaiseSlot0Field_toSection,
    cometricRaiseSlot0Field_toSection]
  rw [show
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 2) I x from
        (A - B).toSection x) (unitTensor (I := I) (M := M) x) =
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 2) I x from
        A.toSection x) (unitTensor (I := I) (M := M) x) -
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 2) I x from
        B.toSection x) (unitTensor (I := I) (M := M) x) from by
    rw [SmoothCcTensor.toSection_sub]
    rfl]
  exact ContinuousLinearMap.map_sub _ _ _

private theorem connSec_sub_eq
    (g gT gU : SmoothRiemannianMetric I M) :
    connDiffSection (I := I) gT g -
        connDiffSection (I := I) gU g =
      cometricRaiseSlot0Field (I := I) (M := M) g 1
        (domDomCongrSection (I := I) g (finRotate 3)
          (connDiffLoweredCc (I := I) g gT -
            connDiffLoweredCc (I := I) g gU)) := by
  rw [connSec_eq_raise (I := I) (M := M) g gT,
    connSec_eq_raise (I := I) (M := M) g gU,
    ← raise_sub (I := I) (M := M) g,
    ← dom_sub (I := I) (M := M) g]

private theorem raisePerm_h2
    (g : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g 0 3) :
    lowJetSq (I := I) (M := M) g 2
        (cometricRaiseSlot0Field (I := I) (M := M) g 1
          (domDomCongrSection (I := I) g (finRotate 3) S)) =
      lowJetSq (I := I) (M := M) g 2 S := by
  calc
    lowJetSq (I := I) (M := M) g 2
        (cometricRaiseSlot0Field (I := I) (M := M) g 1
          (domDomCongrSection (I := I) g (finRotate 3) S)) =
      lowJetSq (I := I) (M := M) g 2
        (domDomCongrSection (I := I) g (finRotate 3) S) := by
          unfold lowJetSq
          apply Finset.sum_congr rfl
          intro q _
          rw [norm_iCG_cometricRaiseSlot0Field_eq
            (I := I) (M := M) g 1
            (domDomCongrSection (I := I) g (finRotate 3) S) q]
    _ = lowJetSq (I := I) (M := M) g 2 S :=
      dom_h2 (I := I) (M := M) g (finRotate 3) S

private theorem connSec_h2_eq
    (g gT gU : SmoothRiemannianMetric I M) :
    lowJetSq (I := I) (M := M) g 2
        (connDiffSection (I := I) gT g -
          connDiffSection (I := I) gU g) =
      lowJetSq (I := I) (M := M) g 2
        (connDiffLoweredCc (I := I) g gT -
          connDiffLoweredCc (I := I) g gU) := by
  rw [connSec_sub_eq (I := I) (M := M) g gT gU]
  exact raisePerm_h2 (I := I) (M := M) g _

private theorem raisePerm_h1
    (g : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g 0 3) :
    lowJetSq (I := I) (M := M) g 1
        (cometricRaiseSlot0Field (I := I) (M := M) g 1
          (domDomCongrSection (I := I) g (finRotate 3) S)) =
      lowJetSq (I := I) (M := M) g 1 S := by
  calc
    lowJetSq (I := I) (M := M) g 1
        (cometricRaiseSlot0Field (I := I) (M := M) g 1
          (domDomCongrSection (I := I) g (finRotate 3) S)) =
      lowJetSq (I := I) (M := M) g 1
        (domDomCongrSection (I := I) g (finRotate 3) S) := by
          unfold lowJetSq
          apply Finset.sum_congr rfl
          intro q _
          rw [norm_iCG_cometricRaiseSlot0Field_eq
            (I := I) (M := M) g 1
            (domDomCongrSection (I := I) g (finRotate 3) S) q]
    _ = lowJetSq (I := I) (M := M) g 1 S :=
      dom_h1 (I := I) (M := M) g (finRotate 3) S

private theorem connSec_h1_eq
    (g gT gU : SmoothRiemannianMetric I M) :
    lowJetSq (I := I) (M := M) g 1
        (connDiffSection (I := I) gT g -
          connDiffSection (I := I) gU g) =
      lowJetSq (I := I) (M := M) g 1
        (connDiffLoweredCc (I := I) g gT -
          connDiffLoweredCc (I := I) g gU) := by
  rw [connSec_sub_eq (I := I) (M := M) g gT gU]
  exact raisePerm_h1 (I := I) (M := M) g _

private theorem slotExt_norm_le
    (g : SmoothRiemannianMetric I M) (r s i : ℕ)
    (Φ : SmoothCcTensor g r s) :
    ‖iteratedCovGrad (I := I) g (r + 1) (s + 1) i
        (slotExtend (I := I) (M := M) g r s Φ)‖ ≤
      Real.sqrt (Module.finrank ℝ E) *
        ‖iteratedCovGrad (I := I) g r s i Φ‖ := by
  classical
  let F : M → ℝ := fun x => (Module.finrank ℝ E : ℝ) *
    riemannianFiberNormSq (I := I) (M := M) g r (s + i) x
      ((iteratedCovGrad (I := I) g r s i Φ).toSection x)
  have hFint : Integrable F
      (riemannianVolumeMeasure (I := I) (M := M) g) := by
    dsimp only [F]
    exact (integrable_riemannianFiberNormSq_toSection
      (I := I) (M := M) g r (s + i)
      (iteratedCovGrad (I := I) g r s i Φ)).const_mul _
  have hsq := normSq_le_integral_of_pointwise_fiberNormSq_le_rs
    (I := I) (M := M) g (r + 1) ((s + 1) + i)
    (iteratedCovGrad (I := I) g (r + 1) (s + 1) i
      (slotExtend (I := I) (M := M) g r s Φ))
    F hFint (fun x => rfns_iteratedCovGrad_slotExtend_le
      (I := I) (M := M) g r s Φ i x)
  have hint :
      (∫ x,
        riemannianFiberNormSq (I := I) (M := M) g r (s + i) x
          ((iteratedCovGrad (I := I) g r s i Φ).toSection x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g)) =
        ‖iteratedCovGrad (I := I) g r s i Φ‖ ^ 2 := by
    rw [SmoothCcTensor.norm_def,
      tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs
        (I := I) (M := M) g r (s + i)]
  dsimp only [F] at hsq
  rw [MeasureTheory.integral_const_mul, hint] at hsq
  refine le_of_sq_le_sq ?_
    (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))
  rw [mul_pow, Real.sq_sqrt (by positivity :
    (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ))]
  exact hsq

set_option linter.unusedVariables false in
private theorem reindex_sub
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (A B : SmoothCcTensor g r s) (ρ : Equiv.Perm (Fin r)) :
    reindexCoeffGen (I := I) (M := M) g r s (A - B) ρ =
      reindexCoeffGen (I := I) (M := M) g r s A ρ -
        reindexCoeffGen (I := I) (M := M) g r s B ρ := by
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

private theorem insert_h2
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g 1 2) :
    lowJetSq (I := I) (M := M) g 2
        (reindexCoeffGen (I := I) (M := M) g 3 4
          (slotExtend (I := I) (M := M) g 2 3
            (slotExtend (I := I) (M := M) g 1 2 S))
          coreInPerm201) ≤
      9 * lowJetSq (I := I) (M := M) g 2 S := by
  classical
  have hper : ∀ i : ℕ,
      ‖iteratedCovGrad (I := I) g 3 4 i
          (reindexCoeffGen (I := I) (M := M) g 3 4
            (slotExtend (I := I) (M := M) g 2 3
              (slotExtend (I := I) (M := M) g 1 2 S))
            coreInPerm201)‖ ≤
        3 * ‖iteratedCovGrad (I := I) g 1 2 i S‖ := by
    intro i
    rw [iteratedCovGrad_reindexCoeffGen (I := I) (M := M),
      norm_reindexCoeffGen_eq (I := I) (M := M)]
    calc
      _ ≤ Real.sqrt (Module.finrank ℝ E) *
          ‖iteratedCovGrad (I := I) g 2 3 i
            (slotExtend (I := I) (M := M) g 1 2 S)‖ :=
        slotExt_norm_le (I := I) (M := M) g 2 3 i _
      _ ≤ Real.sqrt (Module.finrank ℝ E) *
          (Real.sqrt (Module.finrank ℝ E) *
            ‖iteratedCovGrad (I := I) g 1 2 i S‖) :=
        mul_le_mul_of_nonneg_left
          (slotExt_norm_le (I := I) (M := M) g 1 2 i S)
          (Real.sqrt_nonneg _)
      _ = 3 * ‖iteratedCovGrad (I := I) g 1 2 i S‖ := by
        rw [hDim]
        have hs : Real.sqrt (3 : ℝ) ^ 2 = 3 :=
          Real.sq_sqrt (by norm_num)
        calc
          Real.sqrt (3 : ℝ) *
              (Real.sqrt (3 : ℝ) *
                ‖iteratedCovGrad (I := I) g 1 2 i S‖) =
              Real.sqrt (3 : ℝ) ^ 2 *
                ‖iteratedCovGrad (I := I) g 1 2 i S‖ := by ring
          _ = 3 * ‖iteratedCovGrad (I := I) g 1 2 i S‖ := by rw [hs]
  have hsq : ∀ i : ℕ,
      ‖iteratedCovGrad (I := I) g 3 4 i
          (reindexCoeffGen (I := I) (M := M) g 3 4
            (slotExtend (I := I) (M := M) g 2 3
              (slotExtend (I := I) (M := M) g 1 2 S))
            coreInPerm201)‖ ^ 2 ≤
        9 * ‖iteratedCovGrad (I := I) g 1 2 i S‖ ^ 2 := by
    intro i
    have h := pow_le_pow_left₀ (norm_nonneg _) (hper i) 2
    nlinarith
  unfold lowJetSq
  calc
    (∑ i ∈ Finset.range (2 + 1),
        ‖iteratedCovGrad (I := I) g 3 4 i
          (reindexCoeffGen (I := I) (M := M) g 3 4
            (slotExtend (I := I) (M := M) g 2 3
              (slotExtend (I := I) (M := M) g 1 2 S))
            coreInPerm201)‖ ^ 2) ≤
      ∑ i ∈ Finset.range (2 + 1),
        9 * ‖iteratedCovGrad (I := I) g 1 2 i S‖ ^ 2 :=
      Finset.sum_le_sum fun i _ => hsq i
    _ = 9 * (∑ i ∈ Finset.range (2 + 1),
        ‖iteratedCovGrad (I := I) g 1 2 i S‖ ^ 2) := by
      rw [Finset.mul_sum]

private theorem connIns_sub_eq
    (g gT gU : SmoothRiemannianMetric I M) :
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
    ← reindex_sub (I := I) (M := M) g,
    ← slotExtend_sub, ← slotExtend_sub]

private def kO0312 : Equiv.Perm (Fin 4) :=
  ⟨![0, 3, 1, 2], ![0, 2, 3, 1], by decide, by decide⟩

private def kO0213 : Equiv.Perm (Fin 4) :=
  ⟨![0, 2, 1, 3], ![0, 2, 1, 3], by decide, by decide⟩

private def kO2301 : Equiv.Perm (Fin 4) :=
  ⟨![2, 3, 0, 1], ![2, 3, 0, 1], by decide, by decide⟩

private def kO1302 : Equiv.Perm (Fin 4) :=
  ⟨![1, 3, 0, 2], ![2, 0, 3, 1], by decide, by decide⟩

private def kO1203 : Equiv.Perm (Fin 4) :=
  ⟨![1, 2, 0, 3], ![2, 0, 1, 3], by decide, by decide⟩

private def kI102 : Equiv.Perm (Fin 3) :=
  ⟨![1, 0, 2], ![1, 0, 2], by decide, by decide⟩

private def kI120 : Equiv.Perm (Fin 3) :=
  ⟨![1, 2, 0], ![2, 0, 1], by decide, by decide⟩

private noncomputable def kerOfIns
    (g : SmoothRiemannianMetric I M)
    (Q : SmoothCcTensor g 3 4) : SmoothCcTensor g 3 4 :=
  -(reindexCoeffGen (I := I) (M := M) g 3 4
        (appCcRS (I := I) (M := M) g 3 4 4
          (permCoeff (I := I) (M := M) g kO0312) Q) kI102
    + reindexCoeffGen (I := I) (M := M) g 3 4
        (appCcRS (I := I) (M := M) g 3 4 4
          (permCoeff (I := I) (M := M) g kO0213) Q) kI120
    + appCcRS (I := I) (M := M) g 3 4 4
        (permCoeff (I := I) (M := M) g kO2301) Q
    + reindexCoeffGen (I := I) (M := M) g 3 4
        (appCcRS (I := I) (M := M) g 3 4 4
          (permCoeff (I := I) (M := M) g kO1302) Q) kI102
    + reindexCoeffGen (I := I) (M := M) g 3 4
        (appCcRS (I := I) (M := M) g 3 4 4
          (permCoeff (I := I) (M := M) g kO1203) Q) kI120)

private theorem ricciKer_eq
    (g gm : SmoothRiemannianMetric I M) :
    linearizedRicciConnDiffOrder1KernelField (I := I) g gm =
      kerOfIns (I := I) (M := M) g
        (connDiffContrInsertionField (I := I) g gm) := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rfl

private theorem kerOfIns_sub
    (g : SmoothRiemannianMetric I M)
    (A B : SmoothCcTensor g 3 4) :
    kerOfIns (I := I) (M := M) g (A - B) =
      kerOfIns (I := I) (M := M) g A -
        kerOfIns (I := I) (M := M) g B := by
  simp only [kerOfIns, appCcRS_sub_right,
    reindex_sub (I := I) (M := M)]
  module

private theorem outPerm_rfns
    (g : SmoothRiemannianMetric I M)
    (σ : Equiv.Perm (Fin 4)) (Q : SmoothCcTensor g 3 4)
    (q : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g 3 (4 + q) x
        ((iteratedCovGrad (I := I) g 3 4 q
          (appCcRS (I := I) (M := M) g 3 4 4
            (permCoeff (I := I) (M := M) g σ) Q)).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g 3 (4 + q) x
        ((iteratedCovGrad (I := I) g 3 4 q Q).toSection x) := by
  refine rfns_iteratedCovGrad_rs_eq_of_section_domDomCongr
    (I := I) (M := M) g 3 4 σ Q
    (appCcRS (I := I) (M := M) g 3 4 4
      (permCoeff (I := I) (M := M) g σ) Q)
    (fun y d => ?_) q x
  have hy :
      (show Tensor0SSpace 3 I y →L[ℝ] Tensor0SSpace 4 I y from
        (appCcRS (I := I) (M := M) g 3 4 4
          (permCoeff (I := I) (M := M) g σ) Q).toSection y) d =
        slotPermCLM (I := I) σ y
          ((show Tensor0SSpace 3 I y →L[ℝ] Tensor0SSpace 4 I y from
            Q.toSection y) d) := rfl
  rw [hy, slotPermCLM_apply, Tensor0SSpace.toModel_ofModel]

private theorem outPerm_norm
    (g : SmoothRiemannianMetric I M)
    (σ : Equiv.Perm (Fin 4)) (Q : SmoothCcTensor g 3 4)
    (q : ℕ) :
    ‖iteratedCovGrad (I := I) g 3 4 q
        (appCcRS (I := I) (M := M) g 3 4 4
          (permCoeff (I := I) (M := M) g σ) Q)‖ =
      ‖iteratedCovGrad (I := I) g 3 4 q Q‖ := by
  refine raisedKoszul_norm_eq_of_sq_eq (norm_nonneg _) (norm_nonneg _) ?_
  rw [SmoothCcTensor.norm_def, SmoothCcTensor.norm_def,
    tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs,
    tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs]
  exact MeasureTheory.integral_congr_ae
    (Filter.Eventually.of_forall fun x =>
      outPerm_rfns (I := I) (M := M) g σ Q q x)

private theorem fullPerm_norm
    (g : SmoothRiemannianMetric I M)
    (σ : Equiv.Perm (Fin 4)) (ρ : Equiv.Perm (Fin 3))
    (Q : SmoothCcTensor g 3 4) (q : ℕ) :
    ‖iteratedCovGrad (I := I) g 3 4 q
        (reindexCoeffGen (I := I) (M := M) g 3 4
          (appCcRS (I := I) (M := M) g 3 4 4
            (permCoeff (I := I) (M := M) g σ) Q) ρ)‖ =
      ‖iteratedCovGrad (I := I) g 3 4 q Q‖ := by
  calc
    _ = ‖iteratedCovGrad (I := I) g 3 4 q
        (appCcRS (I := I) (M := M) g 3 4 4
          (permCoeff (I := I) (M := M) g σ) Q)‖ := by
      rw [iteratedCovGrad_reindexCoeffGen (I := I) (M := M),
        norm_reindexCoeffGen_eq (I := I) (M := M)]
    _ = _ := outPerm_norm (I := I) (M := M) g σ Q q

private theorem norm_five_le
    {V : Type*} [SeminormedAddCommGroup V]
    {a b c d e : V} {n : ℝ}
    (ha : ‖a‖ = n) (hb : ‖b‖ = n) (hc : ‖c‖ = n)
    (hd : ‖d‖ = n) (he : ‖e‖ = n) :
    ‖a + b + c + d + e‖ ≤ 5 * n := by
  have h1 := norm_add_le (a + b + c + d) e
  have h2 := norm_add_le (a + b + c) d
  have h3 := norm_add_le (a + b) c
  have h4 := norm_add_le a b
  linarith

private theorem kerOfIns_h2
    (g : SmoothRiemannianMetric I M)
    (Q : SmoothCcTensor g 3 4) :
    lowJetSq (I := I) (M := M) g 2
        (kerOfIns (I := I) (M := M) g Q) ≤
      25 * lowJetSq (I := I) (M := M) g 2 Q := by
  classical
  have hper : ∀ i : ℕ,
      ‖iteratedCovGrad (I := I) g 3 4 i
          (kerOfIns (I := I) (M := M) g Q)‖ ≤
        5 * ‖iteratedCovGrad (I := I) g 3 4 i Q‖ := by
    intro i
    simp only [kerOfIns, iteratedCovGrad_neg, norm_neg,
      iteratedCovGrad_add]
    exact norm_five_le
      (fullPerm_norm (I := I) (M := M) g kO0312 kI102 Q i)
      (fullPerm_norm (I := I) (M := M) g kO0213 kI120 Q i)
      (outPerm_norm (I := I) (M := M) g kO2301 Q i)
      (fullPerm_norm (I := I) (M := M) g kO1302 kI102 Q i)
      (fullPerm_norm (I := I) (M := M) g kO1203 kI120 Q i)
  have hsq : ∀ i : ℕ,
      ‖iteratedCovGrad (I := I) g 3 4 i
          (kerOfIns (I := I) (M := M) g Q)‖ ^ 2 ≤
        25 * ‖iteratedCovGrad (I := I) g 3 4 i Q‖ ^ 2 := by
    intro i
    have h := pow_le_pow_left₀ (norm_nonneg _) (hper i) 2
    nlinarith
  unfold lowJetSq
  calc
    (∑ i ∈ Finset.range (2 + 1),
        ‖iteratedCovGrad (I := I) g 3 4 i
          (kerOfIns (I := I) (M := M) g Q)‖ ^ 2) ≤
      ∑ i ∈ Finset.range (2 + 1),
        25 * ‖iteratedCovGrad (I := I) g 3 4 i Q‖ ^ 2 :=
      Finset.sum_le_sum fun i _ => hsq i
    _ = 25 * (∑ i ∈ Finset.range (2 + 1),
        ‖iteratedCovGrad (I := I) g 3 4 i Q‖ ^ 2) := by
      rw [Finset.mul_sum]

private theorem ricciKer_sub_eq
    (g gT gU : SmoothRiemannianMetric I M) :
    linearizedRicciConnDiffOrder1KernelField (I := I) g gT -
        linearizedRicciConnDiffOrder1KernelField (I := I) g gU =
      kerOfIns (I := I) (M := M) g
        (connDiffContrInsertionField (I := I) g gT -
          connDiffContrInsertionField (I := I) g gU) := by
  rw [ricciKer_eq (I := I) (M := M) g gT,
    ricciKer_eq (I := I) (M := M) g gU,
    ← kerOfIns_sub (I := I) (M := M) g]

private theorem sharp_eq_slot0
    (g gm : SmoothRiemannianMetric I M) :
    sharpFlatEndoCc (I := I) g gm =
      slotInsertEndoCc (I := I) (M := M) g 0
        (fullRaisedEndoField (I := I) (M := M) g gm) := by
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
          (fullRaisedEndoField (I := I) (M := M) g gm)).toSection x) om =
      slotInsertEndoFib (I := I) (M := M) 1 0 x
        (gInvRaisedEndo (I := I) g gm x) om from rfl]
  rw [cotangentToDual_slotInsertEndoFib' (I := I) (M := M) x
    (gInvRaisedEndo (I := I) g gm x) om w]
  rw [show (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
        (sharpFlatEndoCc (I := I) g gm).toSection x) om =
      g0FlatCLM (I := I) g x
        (inverseMetricSharpFib (I := I) gm x om) from rfl]
  rw [cotangentToDual_g0FlatCLM]
  rw [show cotangentToDual (I := I) om
      (gInvRaisedEndo (I := I) g gm x w) =
      gm.inner x (inverseMetricSharpFib (I := I) gm x om)
        (gInvRaisedEndo (I := I) g gm x w) from by
    rw [← cotangentToDualLinear_apply]
    exact (inverseMetricSharpFib_inner (I := I) gm x om
      (gInvRaisedEndo (I := I) g gm x w)).symm]
  rw [show gInvRaisedEndo (I := I) g gm x w =
      inverseMetricSharpFib (I := I) gm x
        (g0FlatCLM (I := I) g x w) by
    rw [gInvRaisedEndo_apply]]
  rw [gm.symm x (inverseMetricSharpFib (I := I) gm x om)
    (inverseMetricSharpFib (I := I) gm x
      (g0FlatCLM (I := I) g x w))]
  rw [inverseMetricSharpFib_inner (I := I) gm x
    (g0FlatCLM (I := I) g x w)
    (inverseMetricSharpFib (I := I) gm x om)]
  rw [cotangentToDualLinear_apply, cotangentToDual_g0FlatCLM]
  rw [g.symm x w (inverseMetricSharpFib (I := I) gm x om)]

set_option linter.unusedVariables false in
private theorem sharp_h2_low
    (g : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀0 : 0 ≤ δ₀) (hδ₀ : δ₀ < 1) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (gm : SmoothRiemannianMetric I M)
        (P : SmoothCcTensor g 0 2)
        (hP : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g P x u v =
            ccTensorBilin (I := I) g P x v u)
        (htie : ∀ (x : M) (u v : TangentSpace I x),
          gm.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g P x u v)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
        (hδ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g P) δ),
      lowJetSq (I := I) (M := M) g 2
          (sharpFlatEndoCc (I := I) g gm) ≤
        K * (1 + lowJetSq (I := I) (M := M) g 2 P) := by
  classical
  let Λ₀ : ℝ := (Module.finrank ℝ E : ℝ) * δ₀
  have hΛ₀0 : 0 ≤ Λ₀ :=
    mul_nonneg (Nat.cast_nonneg _) hδ₀0
  obtain ⟨Λ, Flow, hΛ, hFlow0, hFlow⟩ :=
    sharpFlatEndoCc_lowOrder_jetL2_radiusFree
      (I := I) (M := M) g
        (2 * Module.finrank ℝ E + 10) le_rfl hδ₀ hΛ₀0
  refine ⟨Flow 2, hFlow0 2, ?_⟩
  intro gm P hP htie δ hδ_le hδ0 hδ
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
    (hFlow gm P htie hδ_le hδ0 hδ hsup).2 2 (by omega)

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

private theorem endo_slot_h2
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (Λ : ContMDiffSection I (E →L[ℝ] E) ∞
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)) :
    lowJetSq (I := I) (M := M) g 2
        (slotInsertEndoCc (I := I) (M := M) g s Λ) ≤
      (Module.finrank ℝ E : ℝ) ^ s *
        lowJetSq (I := I) (M := M) g 2
          (slotInsertEndoCc (I := I) (M := M) g 0 Λ) := by
  unfold lowJetSq
  calc
    ∑ i ∈ Finset.range 3,
        ‖iteratedCovGrad (I := I) g (s + 1) (s + 1) i
          (slotInsertEndoCc (I := I) (M := M) g s Λ)‖ ^ 2 ≤
      ∑ i ∈ Finset.range 3, (Module.finrank ℝ E : ℝ) ^ s *
        ‖iteratedCovGrad (I := I) g 1 1 i
          (slotInsertEndoCc (I := I) (M := M) g 0 Λ)‖ ^ 2 :=
      Finset.sum_le_sum fun i _ =>
        endo_slot_l2 (I := I) (M := M) g s i Λ
    _ = (Module.finrank ℝ E : ℝ) ^ s *
        ∑ i ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g 1 1 i
            (slotInsertEndoCc (I := I) (M := M) g 0 Λ)‖ ^ 2 := by
      rw [Finset.mul_sum]

set_option linter.unusedVariables false in
private theorem full_slot_h2
    (g : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀0 : 0 ≤ δ₀) (hδ₀ : δ₀ < 1) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (gm : SmoothRiemannianMetric I M)
        (P : SmoothCcTensor g 0 2)
        (hP : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g P x u v =
            ccTensorBilin (I := I) g P x v u)
        (htie : ∀ (x : M) (u v : TangentSpace I x),
          gm.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g P x u v)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
        (hδ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g P) δ),
      lowJetSq (I := I) (M := M) g 2
          (fullSlot3 (I := I) (M := M) g gm) ≤
        K * (1 + lowJetSq (I := I) (M := M) g 2 P) := by
  obtain ⟨K₀, hK₀, hsharp⟩ :=
    sharp_h2_low (I := I) (M := M) g hδ₀0 hδ₀
  let fr : ℝ := Module.finrank ℝ E
  let K : ℝ := fr ^ 2 * K₀
  have hfr : 0 ≤ fr := Nat.cast_nonneg _
  have hK : 0 ≤ K := mul_nonneg (pow_nonneg hfr 2) hK₀
  refine ⟨K, hK, ?_⟩
  intro gm P hP htie δ hδ_le hδ0 hδ
  calc
    lowJetSq (I := I) (M := M) g 2
        (fullSlot3 (I := I) (M := M) g gm) ≤
      fr ^ 2 * lowJetSq (I := I) (M := M) g 2
        (slotInsertEndoCc (I := I) (M := M) g 0
          (fullRaisedEndoField (I := I) (M := M) g gm)) := by
      simpa only [fullSlot3, fr] using
        endo_slot_h2 (I := I) (M := M) g 2
          (fullRaisedEndoField (I := I) (M := M) g gm)
    _ = fr ^ 2 * lowJetSq (I := I) (M := M) g 2
        (sharpFlatEndoCc (I := I) g gm) := by
      rw [sharp_eq_slot0 (I := I) (M := M) g gm]
    _ ≤ fr ^ 2 * (K₀ *
        (1 + lowJetSq (I := I) (M := M) g 2 P)) :=
      mul_le_mul_of_nonneg_left
        (hsharp gm P hP htie hδ_le hδ0 hδ) (pow_nonneg hfr 2)
    _ = K * (1 + lowJetSq (I := I) (M := M) g 2 P) := by
      simp only [K]
      ring

set_option linter.unusedVariables false in
private theorem raiseLast_h2
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (gm : SmoothRiemannianMetric I M)
        (S : SmoothCcTensor g 0 3),
      lowJetSq (I := I) (M := M) g 2
          (raiseLast (I := I) (M := M) g gm S) ≤
        C * lowJetSq (I := I) (M := M) g 2
            (fullSlot3 (I := I) (M := M) g gm) *
          lowJetSq (I := I) (M := M) g 2 S := by
  obtain ⟨C, hC, happ⟩ :=
    app_h2_mul (I := I) (M := M) hDim g 0 3 3
  refine ⟨C, hC, ?_⟩
  intro gm S
  calc
    lowJetSq (I := I) (M := M) g 2
        (raiseLast (I := I) (M := M) g gm S) =
      lowJetSq (I := I) (M := M) g 2
        (appCc (I := I) (M := M) g 3 3
          (fullSlot3 (I := I) (M := M) g gm)
          (domDomCongrSection (I := I) g (finRotate 3) S)) := by
      exact dom_h2 (I := I) (M := M) g lowPerm
        (appCc (I := I) (M := M) g 3 3
          (fullSlot3 (I := I) (M := M) g gm)
          (domDomCongrSection (I := I) g (finRotate 3) S))
    _ ≤ C * lowJetSq (I := I) (M := M) g 2
          (fullSlot3 (I := I) (M := M) g gm) *
        lowJetSq (I := I) (M := M) g 2
          (domDomCongrSection (I := I) g (finRotate 3) S) := by
      simpa only [appCc] using happ
        (fullSlot3 (I := I) (M := M) g gm)
        (domDomCongrSection (I := I) g (finRotate 3) S)
    _ = C * lowJetSq (I := I) (M := M) g 2
          (fullSlot3 (I := I) (M := M) g gm) *
        lowJetSq (I := I) (M := M) g 2 S := by
      rw [dom_h2 (I := I) (M := M)]

set_option linter.unusedVariables false in
private theorem raiseLast_h1
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (gm : SmoothRiemannianMetric I M)
        (S : SmoothCcTensor g 0 3),
      lowJetSq (I := I) (M := M) g 1
          (raiseLast (I := I) (M := M) g gm S) ≤
        C * lowJetSq (I := I) (M := M) g 2
            (fullSlot3 (I := I) (M := M) g gm) *
          lowJetSq (I := I) (M := M) g 1 S := by
  obtain ⟨C, hC, happ⟩ :=
    app_h21_mul (I := I) (M := M) hDim g 0 3 3
  refine ⟨C, hC, ?_⟩
  intro gm S
  calc
    lowJetSq (I := I) (M := M) g 1
        (raiseLast (I := I) (M := M) g gm S) =
      lowJetSq (I := I) (M := M) g 1
        (appCc (I := I) (M := M) g 3 3
          (fullSlot3 (I := I) (M := M) g gm)
          (domDomCongrSection (I := I) g (finRotate 3) S)) := by
      exact dom_h1 (I := I) (M := M) g lowPerm
        (appCc (I := I) (M := M) g 3 3
          (fullSlot3 (I := I) (M := M) g gm)
          (domDomCongrSection (I := I) g (finRotate 3) S))
    _ ≤ C * lowJetSq (I := I) (M := M) g 2
          (fullSlot3 (I := I) (M := M) g gm) *
        lowJetSq (I := I) (M := M) g 1
          (domDomCongrSection (I := I) g (finRotate 3) S) := by
      simpa only [appCc] using happ
        (fullSlot3 (I := I) (M := M) g gm)
        (domDomCongrSection (I := I) g (finRotate 3) S)
    _ = C * lowJetSq (I := I) (M := M) g 2
          (fullSlot3 (I := I) (M := M) g gm) *
        lowJetSq (I := I) (M := M) g 1 S := by
      rw [dom_h1 (I := I) (M := M)]

set_option linter.unusedVariables false in
private theorem kappa_pair_h2
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
            g.inner x u v + ccTensorBilinSymm (I := I) g U x u v),
      lowJetSq (I := I) (M := M) g 2
          (lc0Kappa (I := I) (M := M) g gT g -
            lc0Kappa (I := I) (M := M) g gU g) ≤
        K * lowJetSq (I := I) (M := M) g 3 (T - U) := by
  obtain ⟨C, hC, happ⟩ :=
    app_h2_mul (I := I) (M := M) hDim g 0 3 3
  let Jop : ℝ :=
    lowJetSq (I := I) (M := M) g 2
      (kappaOp (I := I) (M := M) g)
  let K : ℝ := C * Jop
  have hJop : 0 ≤ Jop :=
    jet_nonneg (I := I) (M := M) g _
  have hK : 0 ≤ K := mul_nonneg hC hJop
  refine ⟨K, hK, ?_⟩
  intro gT gU T U hT hU hTtie hUtie
  rw [kappa_pair (I := I) (M := M) g gT gU T U
    hT hU hTtie hUtie]
  calc
    lowJetSq (I := I) (M := M) g 2
        (appCcRS (I := I) (M := M) g 0 3 3
          (kappaOp (I := I) (M := M) g)
          (covGrad (I := I) (M := M) g 0 2 (T - U))) ≤
      C * Jop *
        lowJetSq (I := I) (M := M) g 2
          (covGrad (I := I) (M := M) g 0 2 (T - U)) := by
      simpa only [Jop] using happ
        (kappaOp (I := I) (M := M) g)
        (covGrad (I := I) (M := M) g 0 2 (T - U))
    _ ≤ C * Jop *
        lowJetSq (I := I) (M := M) g 3 (T - U) :=
      mul_le_mul_of_nonneg_left
        (grad_h2_le_h3 (I := I) (M := M) g (T - U)) hK
    _ = K * lowJetSq (I := I) (M := M) g 3 (T - U) := by
      rfl

set_option linter.unusedVariables false in
private theorem kappa_pair_h1
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
            g.inner x u v + ccTensorBilinSymm (I := I) g U x u v),
      lowJetSq (I := I) (M := M) g 1
          (lc0Kappa (I := I) (M := M) g gT g -
            lc0Kappa (I := I) (M := M) g gU g) ≤
        K * lowJetSq (I := I) (M := M) g 2 (T - U) := by
  obtain ⟨C, hC, happ⟩ :=
    app_h21_mul (I := I) (M := M) hDim g 0 3 3
  let Jop : ℝ :=
    lowJetSq (I := I) (M := M) g 2
      (kappaOp (I := I) (M := M) g)
  let K : ℝ := C * Jop
  have hJop : 0 ≤ Jop :=
    jet_nonneg (I := I) (M := M) g _
  have hK : 0 ≤ K := mul_nonneg hC hJop
  refine ⟨K, hK, ?_⟩
  intro gT gU T U hT hU hTtie hUtie
  rw [kappa_pair (I := I) (M := M) g gT gU T U
    hT hU hTtie hUtie]
  calc
    lowJetSq (I := I) (M := M) g 1
        (appCcRS (I := I) (M := M) g 0 3 3
          (kappaOp (I := I) (M := M) g)
          (covGrad (I := I) (M := M) g 0 2 (T - U))) ≤
      C * Jop *
        lowJetSq (I := I) (M := M) g 1
          (covGrad (I := I) (M := M) g 0 2 (T - U)) := by
      simpa only [Jop] using happ
        (kappaOp (I := I) (M := M) g)
        (covGrad (I := I) (M := M) g 0 2 (T - U))
    _ ≤ C * Jop *
        lowJetSq (I := I) (M := M) g 2 (T - U) :=
      mul_le_mul_of_nonneg_left
        (grad_h1_le_h2 (I := I) (M := M) g (T - U)) hK
    _ = K * lowJetSq (I := I) (M := M) g 2 (T - U) := by
      rfl

set_option linter.unusedVariables false in
private theorem wXi_h2_low
    (g : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀0 : 0 ≤ δ₀) (hδ₀ : δ₀ < 1) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (gm : SmoothRiemannianMetric I M)
        (P : SmoothCcTensor g 0 2)
        (hP : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g P x u v =
            ccTensorBilin (I := I) g P x v u)
        (htie : ∀ (x : M) (u v : TangentSpace I x),
          gm.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g P x u v)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
        (hδ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g P) δ),
      lowJetSq (I := I) (M := M) g 2
          (wXi (I := I) (M := M) g gm g) ≤
        K * (1 + lowJetSq (I := I) (M := M) g 3 P) := by
  classical
  let Λ₀ : ℝ := (Module.finrank ℝ E : ℝ) * δ₀
  have hΛ₀0 : 0 ≤ Λ₀ :=
    mul_nonneg (Nat.cast_nonneg _) hδ₀0
  obtain ⟨Flow, hFlow0, hFlow⟩ :=
    wXi_lowOrder_jetL2_radiusFree
      (I := I) (M := M) g g
      (2 * Module.finrank ℝ E + 10) le_rfl hδ₀ hΛ₀0
  refine ⟨Flow 2, hFlow0 2, ?_⟩
  intro gm P hP htie δ hδ_le hδ0 hδ
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
    hFlow gm P htie hδ_le hδ0 hδ hsup 2 (by omega)

set_option linter.unusedVariables false in
private theorem corr_diff_h2
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀0 : 0 ≤ δ₀) (hδ₀ : δ₀ < 1) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (gT : SmoothRiemannianMetric I M)
        (T U : SmoothCcTensor g 0 2)
        (hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        (hTtie : ∀ (x : M) (u v : TangentSpace I x),
          gT.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g T x u v)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
        (hδ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ),
      lowJetSq (I := I) (M := M) g 2
          (metricLowerCorr (I := I) (M := M) g gT g (T - U)) ≤
        K * (1 + lowJetSq (I := I) (M := M) g 3 T) *
          lowJetSq (I := I) (M := M) g 3 (T - U) := by
  obtain ⟨C, hC, hmul⟩ :=
    metricCorr_h2_mul (I := I) (M := M) hDim g
  obtain ⟨Kw, hKw, hw⟩ :=
    wXi_h2_low (I := I) (M := M) g hδ₀0 hδ₀
  let K : ℝ := C * Kw
  have hK : 0 ≤ K := mul_nonneg hC hKw
  refine ⟨K, hK, ?_⟩
  intro gT T U hT hTtie δ hδ_le hδ0 hδ
  have hraw :
      lowJetSq (I := I) (M := M) g 2
          (metricLowerCorr (I := I) (M := M) g gT g (T - U)) ≤
        C * lowJetSq (I := I) (M := M) g 2 (T - U) *
          lowJetSq (I := I) (M := M) g 2
            (wXi (I := I) (M := M) g gT g) := by
    simpa only [lowJetSq, Nat.reduceAdd] using
      hmul gT g (T - U)
  have hd := jet_mono (I := I) (M := M) g
    (by omega : 2 ≤ 3) (T - U)
  have hw' := hw gT T hT hTtie hδ_le hδ0 hδ
  have hD0 : 0 ≤ lowJetSq (I := I) (M := M) g 3 (T - U) :=
    jet_nonneg (I := I) (M := M) g _
  have hW0 : 0 ≤ lowJetSq (I := I) (M := M) g 2
      (wXi (I := I) (M := M) g gT g) :=
    jet_nonneg (I := I) (M := M) g _
  calc
    lowJetSq (I := I) (M := M) g 2
        (metricLowerCorr (I := I) (M := M) g gT g (T - U)) ≤
      C * lowJetSq (I := I) (M := M) g 2 (T - U) *
        lowJetSq (I := I) (M := M) g 2
          (wXi (I := I) (M := M) g gT g) := hraw
    _ ≤ C * lowJetSq (I := I) (M := M) g 3 (T - U) *
        lowJetSq (I := I) (M := M) g 2
          (wXi (I := I) (M := M) g gT g) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hd hC) hW0
    _ ≤ C * lowJetSq (I := I) (M := M) g 3 (T - U) *
        (Kw * (1 + lowJetSq (I := I) (M := M) g 3 T)) :=
      mul_le_mul_of_nonneg_left hw'
        (mul_nonneg hC hD0)
    _ = K * (1 + lowJetSq (I := I) (M := M) g 3 T) *
        lowJetSq (I := I) (M := M) g 3 (T - U) := by
      simp only [K]
      ring

set_option linter.unusedVariables false in
private theorem corr_diff_h2_low
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀0 : 0 ≤ δ₀) (hδ₀ : δ₀ < 1) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (gT : SmoothRiemannianMetric I M)
        (T U : SmoothCcTensor g 0 2)
        (hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        (hTtie : ∀ (x : M) (u v : TangentSpace I x),
          gT.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g T x u v)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
        (hδ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ),
      lowJetSq (I := I) (M := M) g 2
          (metricLowerCorr (I := I) (M := M) g gT g (T - U)) ≤
        K * (1 + lowJetSq (I := I) (M := M) g 3 T) *
          lowJetSq (I := I) (M := M) g 2 (T - U) := by
  obtain ⟨C, hC, hmul⟩ :=
    metricCorr_h2_mul (I := I) (M := M) hDim g
  obtain ⟨Kw, hKw, hw⟩ :=
    wXi_h2_low (I := I) (M := M) g hδ₀0 hδ₀
  let K : ℝ := C * Kw
  have hK : 0 ≤ K := mul_nonneg hC hKw
  refine ⟨K, hK, ?_⟩
  intro gT T U hT hTtie δ hδ_le hδ0 hδ
  have hraw :
      lowJetSq (I := I) (M := M) g 2
          (metricLowerCorr (I := I) (M := M) g gT g (T - U)) ≤
        C * lowJetSq (I := I) (M := M) g 2 (T - U) *
          lowJetSq (I := I) (M := M) g 2
            (wXi (I := I) (M := M) g gT g) := by
    simpa only [lowJetSq, Nat.reduceAdd] using
      hmul gT g (T - U)
  have hw' := hw gT T hT hTtie hδ_le hδ0 hδ
  have hD0 : 0 ≤ lowJetSq (I := I) (M := M) g 2 (T - U) :=
    jet_nonneg (I := I) (M := M) g _
  calc
    lowJetSq (I := I) (M := M) g 2
        (metricLowerCorr (I := I) (M := M) g gT g (T - U)) ≤
      C * lowJetSq (I := I) (M := M) g 2 (T - U) *
        lowJetSq (I := I) (M := M) g 2
          (wXi (I := I) (M := M) g gT g) := hraw
    _ ≤ C * lowJetSq (I := I) (M := M) g 2 (T - U) *
        (Kw * (1 + lowJetSq (I := I) (M := M) g 3 T)) :=
      mul_le_mul_of_nonneg_left hw'
        (mul_nonneg hC hD0)
    _ = K * (1 + lowJetSq (I := I) (M := M) g 3 T) *
        lowJetSq (I := I) (M := M) g 2 (T - U) := by
      simp only [K]
      ring

set_option linter.unusedVariables false in
/-- On a closed three-manifold, the background-lowered connection coefficient
is radius-free `H²`-Lipschitz on a common fibre-small metric neighborhood. -/
theorem wXi_sub_h2
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀0 : 0 ≤ δ₀) (hδ₀ : δ₀ < 1) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (gT gU g_bg : SmoothRiemannianMetric I M)
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
          (ccTensorBilinSymm (I := I) g U) δU),
      lowJetSq (I := I) (M := M) g 2
          (wXi (I := I) (M := M) g gT g_bg -
            wXi (I := I) (M := M) g gU g_bg) ≤
        K * (1 + lowJetSq (I := I) (M := M) g 3 T) *
          (1 + lowJetSq (I := I) (M := M) g 3 U) *
          lowJetSq (I := I) (M := M) g 3 (T - U) := by
  obtain ⟨Cr, hCr, hraise⟩ :=
    raiseLast_h2 (I := I) (M := M) hDim g
  obtain ⟨Ks, hKs, hslot⟩ :=
    full_slot_h2 (I := I) (M := M) g hδ₀0 hδ₀
  obtain ⟨Kk, hKk, hkappa⟩ :=
    kappa_pair_h2 (I := I) (M := M) hDim g
  obtain ⟨Kc, hKc, hcorr⟩ :=
    corr_diff_h2 (I := I) (M := M) hDim g hδ₀0 hδ₀
  let K : ℝ := 2 * Cr * Ks * (Kk + Kc)
  have hK : 0 ≤ K :=
    mul_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) hCr) hKs)
      (add_nonneg hKk hKc)
  refine ⟨K, hK, ?_⟩
  intro gT gU g_bg T U hT hU hTtie hUtie
    δT δU hδT_le hδT0 hδT hδU_le hδU0 hδU
  let JT : ℝ := lowJetSq (I := I) (M := M) g 3 T
  let JU : ℝ := lowJetSq (I := I) (M := M) g 3 U
  let JD : ℝ := lowJetSq (I := I) (M := M) g 3 (T - U)
  let X : SmoothCcTensor g 0 3 :=
    lc0Kappa (I := I) (M := M) g gT g -
      lc0Kappa (I := I) (M := M) g gU g
  let Y : SmoothCcTensor g 0 3 :=
    metricLowerCorr (I := I) (M := M) g gT g (T - U)
  have hbg :
      wXi (I := I) (M := M) g gT g_bg -
          wXi (I := I) (M := M) g gU g_bg =
        connDiffLoweredCc (I := I) g gT -
          connDiffLoweredCc (I := I) g gU := by
    simp only [wXi]
    module
  have hexact :
      wXi (I := I) (M := M) g gT g_bg -
          wXi (I := I) (M := M) g gU g_bg =
        raiseLast (I := I) (M := M) g gU (X - Y) := by
    rw [hbg]
    exact (moving_corr (I := I) (M := M) g gT gU T U
      hTtie hUtie).symm
  have hJT : 0 ≤ JT := jet_nonneg (I := I) (M := M) g _
  have hJU : 0 ≤ JU := jet_nonneg (I := I) (M := M) g _
  have hJD : 0 ≤ JD := jet_nonneg (I := I) (M := M) g _
  have hX : lowJetSq (I := I) (M := M) g 2 X ≤ Kk * JD := by
    simpa only [X, JD] using
      hkappa gT gU T U hT hU hTtie hUtie
  have hY :
      lowJetSq (I := I) (M := M) g 2 Y ≤
        Kc * (1 + JT) * JD := by
    simpa only [Y, JT, JD] using
      hcorr gT T U hT hTtie hδT_le hδT0 hδT
  have hX0 : 0 ≤ lowJetSq (I := I) (M := M) g 2 X :=
    jet_nonneg (I := I) (M := M) g _
  have hY0 : 0 ≤ lowJetSq (I := I) (M := M) g 2 Y :=
    jet_nonneg (I := I) (M := M) g _
  have hk_up : Kk * JD ≤ Kk * (1 + JT) * JD := by
    nlinarith [mul_nonneg hKk hJD, mul_nonneg hKk hJT]
  have hsum :
      lowJetSq (I := I) (M := M) g 2 X +
          lowJetSq (I := I) (M := M) g 2 Y ≤
        (Kk + Kc) * (1 + JT) * JD := by
    nlinarith
  have hinner :
      lowJetSq (I := I) (M := M) g 2 (X - Y) ≤
        2 * (Kk + Kc) * (1 + JT) * JD := by
    calc
      lowJetSq (I := I) (M := M) g 2 (X - Y) ≤
        2 * (lowJetSq (I := I) (M := M) g 2 X +
          lowJetSq (I := I) (M := M) g 2 Y) :=
            jet_sub (I := I) (M := M) g 2 X Y
      _ ≤ 2 * ((Kk + Kc) * (1 + JT) * JD) :=
        mul_le_mul_of_nonneg_left hsum (by norm_num)
      _ = 2 * (Kk + Kc) * (1 + JT) * JD := by ring
  have hinner0 :
      0 ≤ lowJetSq (I := I) (M := M) g 2 (X - Y) :=
    jet_nonneg (I := I) (M := M) g _
  have hJU23 := jet_mono (I := I) (M := M) g
    (by omega : 2 ≤ 3) U
  have hslot2 :
      lowJetSq (I := I) (M := M) g 2
          (fullSlot3 (I := I) (M := M) g gU) ≤
        Ks * (1 + JU) := by
    calc
      lowJetSq (I := I) (M := M) g 2
          (fullSlot3 (I := I) (M := M) g gU) ≤
        Ks * (1 + lowJetSq (I := I) (M := M) g 2 U) :=
          hslot gU U hU hUtie hδU_le hδU0 hδU
      _ ≤ Ks * (1 + JU) :=
        mul_le_mul_of_nonneg_left (by
          dsimp only [JU]
          linarith) hKs
  have hslot0 :
      0 ≤ lowJetSq (I := I) (M := M) g 2
          (fullSlot3 (I := I) (M := M) g gU) :=
    jet_nonneg (I := I) (M := M) g _
  rw [hexact]
  calc
    lowJetSq (I := I) (M := M) g 2
        (raiseLast (I := I) (M := M) g gU (X - Y)) ≤
      Cr * lowJetSq (I := I) (M := M) g 2
          (fullSlot3 (I := I) (M := M) g gU) *
        lowJetSq (I := I) (M := M) g 2 (X - Y) :=
      hraise gU (X - Y)
    _ ≤ Cr * (Ks * (1 + JU)) *
        lowJetSq (I := I) (M := M) g 2 (X - Y) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hslot2 hCr) hinner0
    _ ≤ Cr * (Ks * (1 + JU)) *
        (2 * (Kk + Kc) * (1 + JT) * JD) :=
      mul_le_mul_of_nonneg_left hinner
        (mul_nonneg hCr
          (mul_nonneg hKs (by linarith)))
    _ = K * (1 + JT) * (1 + JU) * JD := by
      simp only [K]
      ring

set_option maxHeartbeats 1600000 in
set_option linter.unusedVariables false in
/-- The background-lowered connection difference has the low-scale
`H2 → H1` tame modulus.  Only the endpoint `U` low radius and the endpoint
`T` high size enter; the state difference is measured solely in `H2`. -/
theorem wXi_pair_h1
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀0 : 0 ≤ δ₀) (hδ₀ : δ₀ < 1) :
    ∃ B0 B1 : ℝ → ℝ,
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B0 R) ∧
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B1 R) ∧
      ∀ (gT gU g_bg : SmoothRiemannianMetric I M)
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
          (wXi (I := I) (M := M) g gT g_bg -
            wXi (I := I) (M := M) g gU g_bg) ≤
        (B0 R * D2 + B1 R * A * D2) ^ 2 := by
  obtain ⟨Cr, hCr, hraise⟩ :=
    raiseLast_h1 (I := I) (M := M) hDim g
  obtain ⟨Ks, hKs, hslot⟩ :=
    full_slot_h2 (I := I) (M := M) g hδ₀0 hδ₀
  obtain ⟨Kk, hKk, hkappa⟩ :=
    kappa_pair_h1 (I := I) (M := M) hDim g
  obtain ⟨Kc, hKc, hcorr⟩ :=
    corr_diff_h2_low (I := I) (M := M) hDim g hδ₀0 hδ₀
  let Q0 : ℝ → ℝ := fun R =>
    2 * Cr * Ks * (1 + R ^ 2) * (Kk + Kc)
  let Q1 : ℝ → ℝ := fun R =>
    2 * Cr * Ks * (1 + R ^ 2) * Kc
  let B0 : ℝ → ℝ := fun R => Real.sqrt (Q0 R)
  let B1 : ℝ → ℝ := fun R => Real.sqrt (Q1 R)
  have hQ0 : ∀ R : ℝ, 0 ≤ R → 0 ≤ Q0 R := by
    intro R hR
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (mul_nonneg (by norm_num) hCr) hKs)
        (by nlinarith [sq_nonneg R]))
      (add_nonneg hKk hKc)
  have hQ1 : ∀ R : ℝ, 0 ≤ R → 0 ≤ Q1 R := by
    intro R hR
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (mul_nonneg (by norm_num) hCr) hKs)
        (by nlinarith [sq_nonneg R]))
      hKc
  refine ⟨B0, B1, fun R hR => Real.sqrt_nonneg _,
    fun R hR => Real.sqrt_nonneg _, ?_⟩
  intro gT gU g_bg T U hT hU hTtie hUtie
    δT δU hδT_le hδT0 hδT hδU_le hδU0 hδU
    R A D2 hR hA hD2 hU2 hT3 hTU2
  let JT : ℝ := lowJetSq (I := I) (M := M) g 3 T
  let JD : ℝ := lowJetSq (I := I) (M := M) g 2 (T - U)
  let X : SmoothCcTensor g 0 3 :=
    lc0Kappa (I := I) (M := M) g gT g -
      lc0Kappa (I := I) (M := M) g gU g
  let Y : SmoothCcTensor g 0 3 :=
    metricLowerCorr (I := I) (M := M) g gT g (T - U)
  have hbg :
      wXi (I := I) (M := M) g gT g_bg -
          wXi (I := I) (M := M) g gU g_bg =
        connDiffLoweredCc (I := I) g gT -
          connDiffLoweredCc (I := I) g gU := by
    simp only [wXi]
    module
  have hexact :
      wXi (I := I) (M := M) g gT g_bg -
          wXi (I := I) (M := M) g gU g_bg =
        raiseLast (I := I) (M := M) g gU (X - Y) := by
    rw [hbg]
    exact (moving_corr (I := I) (M := M) g gT gU T U
      hTtie hUtie).symm
  have hJT0 : 0 ≤ JT := jet_nonneg (I := I) (M := M) g _
  have hJD0 : 0 ≤ JD := jet_nonneg (I := I) (M := M) g _
  have hX :
      lowJetSq (I := I) (M := M) g 1 X ≤ Kk * JD := by
    simpa only [X, JD] using
      hkappa gT gU T U hT hU hTtie hUtie
  have hY2 :
      lowJetSq (I := I) (M := M) g 2 Y ≤
        Kc * (1 + JT) * JD := by
    simpa only [Y, JT, JD] using
      hcorr gT T U hT hTtie hδT_le hδT0 hδT
  have hY1 :
      lowJetSq (I := I) (M := M) g 1 Y ≤
        Kc * (1 + JT) * JD := by
    exact (jet_mono (I := I) (M := M) g
      (by omega : 1 ≤ 2) Y).trans hY2
  have hsum :
      lowJetSq (I := I) (M := M) g 1 X +
          lowJetSq (I := I) (M := M) g 1 Y ≤
        (Kk + Kc * (1 + JT)) * JD := by
    calc
      _ ≤ Kk * JD + (Kc * (1 + JT) * JD) :=
        add_le_add hX hY1
      _ = (Kk + Kc * (1 + JT)) * JD := by ring
  have hinner :
      lowJetSq (I := I) (M := M) g 1 (X - Y) ≤
        2 * (Kk + Kc * (1 + JT)) * JD := by
    calc
      lowJetSq (I := I) (M := M) g 1 (X - Y) ≤
          2 * (lowJetSq (I := I) (M := M) g 1 X +
            lowJetSq (I := I) (M := M) g 1 Y) :=
        jet_sub (I := I) (M := M) g 1 X Y
      _ ≤ 2 * ((Kk + Kc * (1 + JT)) * JD) :=
        mul_le_mul_of_nonneg_left hsum (by norm_num)
      _ = 2 * (Kk + Kc * (1 + JT)) * JD := by ring
  have hinner0 :
      0 ≤ lowJetSq (I := I) (M := M) g 1 (X - Y) :=
    jet_nonneg (I := I) (M := M) g _
  have hslot2 :
      lowJetSq (I := I) (M := M) g 2
          (fullSlot3 (I := I) (M := M) g gU) ≤
        Ks * (1 + R ^ 2) := by
    calc
      lowJetSq (I := I) (M := M) g 2
          (fullSlot3 (I := I) (M := M) g gU) ≤
        Ks * (1 + lowJetSq (I := I) (M := M) g 2 U) :=
          hslot gU U hU hUtie hδU_le hδU0 hδU
      _ ≤ Ks * (1 + R ^ 2) :=
        mul_le_mul_of_nonneg_left
          (by linarith) hKs
  have hJT3 : JT ≤ A ^ 2 := by
    simpa only [JT] using hT3
  have hJD2 : JD ≤ D2 ^ 2 := by
    simpa only [JD] using hTU2
  have hpart :
      Kk + Kc * (1 + JT) ≤
        Kk + Kc * (1 + A ^ 2) := by
    have hmul := mul_le_mul_of_nonneg_left hJT3 hKc
    linarith
  have hpart0 : 0 ≤ Kk + Kc * (1 + A ^ 2) := by
    exact add_nonneg hKk
      (mul_nonneg hKc (by nlinarith [sq_nonneg A]))
  have hinnerA :
      2 * (Kk + Kc * (1 + JT)) * JD ≤
        2 * (Kk + Kc * (1 + A ^ 2)) * D2 ^ 2 := by
    calc
      2 * (Kk + Kc * (1 + JT)) * JD ≤
          2 * (Kk + Kc * (1 + A ^ 2)) * JD :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hpart (by norm_num)) hJD0
      _ ≤ 2 * (Kk + Kc * (1 + A ^ 2)) * D2 ^ 2 :=
        mul_le_mul_of_nonneg_left hJD2
          (mul_nonneg (by norm_num) hpart0)
  have hfactor :
      0 ≤ Cr * (Ks * (1 + R ^ 2)) :=
    mul_nonneg hCr
      (mul_nonneg hKs (by nlinarith [sq_nonneg R]))
  have hout :
      lowJetSq (I := I) (M := M) g 1
          (wXi (I := I) (M := M) g gT g_bg -
            wXi (I := I) (M := M) g gU g_bg) ≤
        (Q0 R + Q1 R * A ^ 2) * D2 ^ 2 := by
    rw [hexact]
    calc
      lowJetSq (I := I) (M := M) g 1
          (raiseLast (I := I) (M := M) g gU (X - Y)) ≤
        Cr * lowJetSq (I := I) (M := M) g 2
            (fullSlot3 (I := I) (M := M) g gU) *
          lowJetSq (I := I) (M := M) g 1 (X - Y) :=
        hraise gU (X - Y)
      _ ≤ Cr * (Ks * (1 + R ^ 2)) *
          lowJetSq (I := I) (M := M) g 1 (X - Y) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hslot2 hCr) hinner0
      _ ≤ Cr * (Ks * (1 + R ^ 2)) *
          (2 * (Kk + Kc * (1 + JT)) * JD) :=
        mul_le_mul_of_nonneg_left hinner hfactor
      _ ≤ Cr * (Ks * (1 + R ^ 2)) *
          (2 * (Kk + Kc * (1 + A ^ 2)) * D2 ^ 2) :=
        mul_le_mul_of_nonneg_left hinnerA hfactor
      _ = (Q0 R + Q1 R * A ^ 2) * D2 ^ 2 := by
        simp only [Q0, Q1]
        ring
  have hB0sq : (B0 R) ^ 2 = Q0 R := by
    simpa only [B0] using Real.sq_sqrt (hQ0 R hR)
  have hB1sq : (B1 R) ^ 2 = Q1 R := by
    simpa only [B1] using Real.sq_sqrt (hQ1 R hR)
  have ha0 : 0 ≤ B0 R * D2 :=
    mul_nonneg (Real.sqrt_nonneg _) hD2
  have hb0 : 0 ≤ B1 R * A * D2 :=
    mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) hA) hD2
  calc
    lowJetSq (I := I) (M := M) g 1
        (wXi (I := I) (M := M) g gT g_bg -
          wXi (I := I) (M := M) g gU g_bg) ≤
      (Q0 R + Q1 R * A ^ 2) * D2 ^ 2 := hout
    _ = (B0 R * D2) ^ 2 + (B1 R * A * D2) ^ 2 := by
      rw [add_mul, mul_pow, mul_pow, mul_pow, hB0sq, hB1sq]
    _ ≤ (B0 R * D2 + B1 R * A * D2) ^ 2 := by
      nlinarith [mul_nonneg ha0 hb0]

set_option linter.unusedVariables false in
/-- The background-lowered connection difference obeys the critical tame
two-arm estimate: its `H³` difference has a coefficient depending only on
the endpoint `H²` radius, while endpoint `H³` size multiplies only the
`H²` difference. -/
theorem wXi_sub_tame
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀0 : 0 ≤ δ₀) (hδ₀ : δ₀ < 1) :
    ∃ B0 B1 : ℝ → ℝ,
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B0 R) ∧
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B1 R) ∧
      ∀ (gT gU g_bg : SmoothRiemannianMetric I M)
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
        (R A D2 D3 : ℝ),
        0 ≤ R → 0 ≤ A → 0 ≤ D2 → 0 ≤ D3 →
        lowJetSq (I := I) (M := M) g 2 U ≤ R ^ 2 →
        lowJetSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
        lowJetSq (I := I) (M := M) g 2 (T - U) ≤ D2 ^ 2 →
        lowJetSq (I := I) (M := M) g 3 (T - U) ≤ D3 ^ 2 →
      lowJetSq (I := I) (M := M) g 2
          (wXi (I := I) (M := M) g gT g_bg -
            wXi (I := I) (M := M) g gU g_bg) ≤
        (B0 R * D3 + B1 R * D2 + B1 R * A * D2) ^ 2 := by
  obtain ⟨Cr, hCr, hraise⟩ :=
    raiseLast_h2 (I := I) (M := M) hDim g
  obtain ⟨Ks, hKs, hslot⟩ :=
    full_slot_h2 (I := I) (M := M) g hδ₀0 hδ₀
  obtain ⟨Kk, hKk, hkappa⟩ :=
    kappa_pair_h2 (I := I) (M := M) hDim g
  obtain ⟨Cc, hCc, hcorr⟩ :=
    metricCorr_h2_mul (I := I) (M := M) hDim g
  obtain ⟨Kw, hKw, hwXi⟩ :=
    wXi_h2_low (I := I) (M := M) g hδ₀0 hδ₀
  let Q0 : ℝ → ℝ := fun R =>
    2 * Cr * Ks * (1 + R ^ 2) * Kk
  let Q1 : ℝ → ℝ := fun R =>
    2 * Cr * Ks * (1 + R ^ 2) * (Cc * Kw)
  let B0 : ℝ → ℝ := fun R => Real.sqrt (Q0 R)
  let B1 : ℝ → ℝ := fun R => Real.sqrt (Q1 R)
  have hQ0 : ∀ R : ℝ, 0 ≤ R → 0 ≤ Q0 R := by
    intro R hR
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (mul_nonneg (by norm_num) hCr) hKs)
          (by positivity))
      hKk
  have hQ1 : ∀ R : ℝ, 0 ≤ R → 0 ≤ Q1 R := by
    intro R hR
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (mul_nonneg (by norm_num) hCr) hKs)
          (by positivity))
      (mul_nonneg hCc hKw)
  refine ⟨B0, B1, fun R _ => Real.sqrt_nonneg _,
    fun R _ => Real.sqrt_nonneg _, ?_⟩
  intro gT gU g_bg T U hT hU hTtie hUtie
    δT δU hδT_le hδT0 hδT hδU_le hδU0 hδU
    R A D2 D3 hR hA hD2 hD3 hU2 hT3 hTU2 hTU3
  let X : SmoothCcTensor g 0 3 :=
    lc0Kappa (I := I) (M := M) g gT g -
      lc0Kappa (I := I) (M := M) g gU g
  let Y : SmoothCcTensor g 0 3 :=
    metricLowerCorr (I := I) (M := M) g gT g (T - U)
  have hbg :
      wXi (I := I) (M := M) g gT g_bg -
          wXi (I := I) (M := M) g gU g_bg =
        connDiffLoweredCc (I := I) g gT -
          connDiffLoweredCc (I := I) g gU := by
    simp only [wXi]
    module
  have hexact :
      wXi (I := I) (M := M) g gT g_bg -
          wXi (I := I) (M := M) g gU g_bg =
        raiseLast (I := I) (M := M) g gU (X - Y) := by
    rw [hbg]
    exact (moving_corr (I := I) (M := M) g gT gU T U
      hTtie hUtie).symm
  have hX :
      lowJetSq (I := I) (M := M) g 2 X ≤ Kk * D3 ^ 2 := by
    calc
      lowJetSq (I := I) (M := M) g 2 X ≤
          Kk * lowJetSq (I := I) (M := M) g 3 (T - U) := by
        simpa only [X] using
          hkappa gT gU T U hT hU hTtie hUtie
      _ ≤ Kk * D3 ^ 2 :=
        mul_le_mul_of_nonneg_left hTU3 hKk
  have hW :
      lowJetSq (I := I) (M := M) g 2
          (wXi (I := I) (M := M) g gT g) ≤
        Kw * (1 + A ^ 2) := by
    calc
      lowJetSq (I := I) (M := M) g 2
          (wXi (I := I) (M := M) g gT g) ≤
        Kw * (1 + lowJetSq (I := I) (M := M) g 3 T) :=
          hwXi gT T hT hTtie hδT_le hδT0 hδT
      _ ≤ Kw * (1 + A ^ 2) :=
        mul_le_mul_of_nonneg_left
          (by linarith) hKw
  have hY :
      lowJetSq (I := I) (M := M) g 2 Y ≤
        Cc * Kw * (D2 ^ 2 + A ^ 2 * D2 ^ 2) := by
    have hraw :
        lowJetSq (I := I) (M := M) g 2 Y ≤
          Cc * lowJetSq (I := I) (M := M) g 2 (T - U) *
            lowJetSq (I := I) (M := M) g 2
              (wXi (I := I) (M := M) g gT g) := by
      simpa only [Y, lowJetSq, Nat.reduceAdd] using
        hcorr gT g (T - U)
    have hleft :
        Cc * lowJetSq (I := I) (M := M) g 2 (T - U) ≤
          Cc * D2 ^ 2 :=
      mul_le_mul_of_nonneg_left hTU2 hCc
    have hW0 :
        0 ≤ lowJetSq (I := I) (M := M) g 2
          (wXi (I := I) (M := M) g gT g) :=
      jet_nonneg (I := I) (M := M) g _
    calc
      lowJetSq (I := I) (M := M) g 2 Y ≤
          Cc * lowJetSq (I := I) (M := M) g 2 (T - U) *
            lowJetSq (I := I) (M := M) g 2
              (wXi (I := I) (M := M) g gT g) := hraw
      _ ≤ Cc * D2 ^ 2 * (Kw * (1 + A ^ 2)) :=
        mul_le_mul hleft hW hW0
          (mul_nonneg hCc (sq_nonneg D2))
      _ = Cc * Kw * (D2 ^ 2 + A ^ 2 * D2 ^ 2) := by
        ring
  have hinner :
      lowJetSq (I := I) (M := M) g 2 (X - Y) ≤
        2 * (Kk * D3 ^ 2 +
          Cc * Kw * (D2 ^ 2 + A ^ 2 * D2 ^ 2)) := by
    exact (jet_sub (I := I) (M := M) g 2 X Y).trans
      (mul_le_mul_of_nonneg_left (add_le_add hX hY) (by norm_num))
  have hinner0 :
      0 ≤ lowJetSq (I := I) (M := M) g 2 (X - Y) :=
    jet_nonneg (I := I) (M := M) g _
  have hslotR :
      lowJetSq (I := I) (M := M) g 2
          (fullSlot3 (I := I) (M := M) g gU) ≤
        Ks * (1 + R ^ 2) := by
    calc
      lowJetSq (I := I) (M := M) g 2
          (fullSlot3 (I := I) (M := M) g gU) ≤
        Ks * (1 + lowJetSq (I := I) (M := M) g 2 U) :=
          hslot gU U hU hUtie hδU_le hδU0 hδU
      _ ≤ Ks * (1 + R ^ 2) :=
        mul_le_mul_of_nonneg_left
          (by linarith) hKs
  have hfactor :
      0 ≤ Cr * (Ks * (1 + R ^ 2)) :=
    mul_nonneg hCr (mul_nonneg hKs (by positivity))
  have hout :
      lowJetSq (I := I) (M := M) g 2
          (wXi (I := I) (M := M) g gT g_bg -
            wXi (I := I) (M := M) g gU g_bg) ≤
        Q0 R * D3 ^ 2 + Q1 R * D2 ^ 2 +
          Q1 R * A ^ 2 * D2 ^ 2 := by
    rw [hexact]
    calc
      lowJetSq (I := I) (M := M) g 2
          (raiseLast (I := I) (M := M) g gU (X - Y)) ≤
        Cr * lowJetSq (I := I) (M := M) g 2
            (fullSlot3 (I := I) (M := M) g gU) *
          lowJetSq (I := I) (M := M) g 2 (X - Y) :=
        hraise gU (X - Y)
      _ ≤ Cr * (Ks * (1 + R ^ 2)) *
          lowJetSq (I := I) (M := M) g 2 (X - Y) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hslotR hCr) hinner0
      _ ≤ Cr * (Ks * (1 + R ^ 2)) *
          (2 * (Kk * D3 ^ 2 +
            Cc * Kw * (D2 ^ 2 + A ^ 2 * D2 ^ 2))) :=
        mul_le_mul_of_nonneg_left hinner hfactor
      _ = Q0 R * D3 ^ 2 + Q1 R * D2 ^ 2 +
          Q1 R * A ^ 2 * D2 ^ 2 := by
        simp only [Q0, Q1]
        ring
  have hB0sq : (B0 R) ^ 2 = Q0 R := by
    simpa only [B0] using Real.sq_sqrt (hQ0 R hR)
  have hB1sq : (B1 R) ^ 2 = Q1 R := by
    simpa only [B1] using Real.sq_sqrt (hQ1 R hR)
  have ha0 : 0 ≤ B0 R * D3 :=
    mul_nonneg (Real.sqrt_nonneg _) hD3
  have hb0 : 0 ≤ B1 R * D2 :=
    mul_nonneg (Real.sqrt_nonneg _) hD2
  have hc0 : 0 ≤ B1 R * A * D2 :=
    mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) hA) hD2
  calc
    lowJetSq (I := I) (M := M) g 2
        (wXi (I := I) (M := M) g gT g_bg -
          wXi (I := I) (M := M) g gU g_bg) ≤
      Q0 R * D3 ^ 2 + Q1 R * D2 ^ 2 +
        Q1 R * A ^ 2 * D2 ^ 2 := hout
    _ = (B0 R * D3) ^ 2 + (B1 R * D2) ^ 2 +
        (B1 R * A * D2) ^ 2 := by
      rw [mul_pow, mul_pow, mul_pow, mul_pow, hB0sq, hB1sq]
    _ ≤ (B0 R * D3 + B1 R * D2 + B1 R * A * D2) ^ 2 := by
      nlinarith [mul_nonneg ha0 hb0, mul_nonneg ha0 hc0,
        mul_nonneg hb0 hc0]

set_option linter.unusedVariables false in
/-- The mixed connection-difference section inherits the low-scale
`H2 → H1` pair estimate from its background-lowered realization. -/
theorem connSec_pair_h1
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
          (connDiffSection (I := I) gT g -
            connDiffSection (I := I) gU g) ≤
        (B0 R * D2 + B1 R * A * D2) ^ 2 := by
  obtain ⟨B0, B1, hB0, hB1, hpair⟩ :=
    wXi_pair_h1 (I := I) (M := M) hDim g hδ₀0 hδ₀
  refine ⟨B0, B1, hB0, hB1, ?_⟩
  intro gT gU T U hT hU hTtie hUtie
    δT δU hδT_le hδT0 hδT hδU_le hδU0 hδU
    R A D2 hR hA hD2 hU2 hT3 hTU2
  calc
    lowJetSq (I := I) (M := M) g 1
        (connDiffSection (I := I) gT g -
          connDiffSection (I := I) gU g) =
      lowJetSq (I := I) (M := M) g 1
        (connDiffLoweredCc (I := I) g gT -
          connDiffLoweredCc (I := I) g gU) :=
      connSec_h1_eq (I := I) (M := M) g gT gU
    _ = lowJetSq (I := I) (M := M) g 1
        (wXi (I := I) (M := M) g gT g -
          wXi (I := I) (M := M) g gU g) := by
      congr 1
      simp only [wXi]
      module
    _ ≤ (B0 R * D2 + B1 R * A * D2) ^ 2 :=
      hpair gT gU g T U hT hU hTtie hUtie
        hδT_le hδT0 hδT hδU_le hδU0 hδU
        R A D2 hR hA hD2 hU2 hT3 hTU2

set_option linter.unusedVariables false in
/-- The mixed connection-difference section inherits the critical two-arm
`H²` pair estimate from its background-lowered covariant realization. -/
theorem connSec_sub_tame
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
        (R A D2 D3 : ℝ),
        0 ≤ R → 0 ≤ A → 0 ≤ D2 → 0 ≤ D3 →
        lowJetSq (I := I) (M := M) g 2 U ≤ R ^ 2 →
        lowJetSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
        lowJetSq (I := I) (M := M) g 2 (T - U) ≤ D2 ^ 2 →
        lowJetSq (I := I) (M := M) g 3 (T - U) ≤ D3 ^ 2 →
      lowJetSq (I := I) (M := M) g 2
          (connDiffSection (I := I) gT g -
            connDiffSection (I := I) gU g) ≤
        (B0 R * D3 + B1 R * D2 + B1 R * A * D2) ^ 2 := by
  obtain ⟨B0, B1, hB0, hB1, hpair⟩ :=
    wXi_sub_tame (I := I) (M := M) hDim g hδ₀0 hδ₀
  refine ⟨B0, B1, hB0, hB1, ?_⟩
  intro gT gU T U hT hU hTtie hUtie
    δT δU hδT_le hδT0 hδT hδU_le hδU0 hδU
    R A D2 D3 hR hA hD2 hD3 hU2 hT3 hTU2 hTU3
  calc
    lowJetSq (I := I) (M := M) g 2
        (connDiffSection (I := I) gT g -
          connDiffSection (I := I) gU g) =
      lowJetSq (I := I) (M := M) g 2
        (connDiffLoweredCc (I := I) g gT -
          connDiffLoweredCc (I := I) g gU) :=
      connSec_h2_eq (I := I) (M := M) g gT gU
    _ = lowJetSq (I := I) (M := M) g 2
        (wXi (I := I) (M := M) g gT g -
          wXi (I := I) (M := M) g gU g) := by
      congr 1
      simp only [wXi]
      module
    _ ≤ (B0 R * D3 + B1 R * D2 + B1 R * A * D2) ^ 2 :=
      hpair gT gU g T U hT hU hTtie hUtie
        hδT_le hδT0 hδT hδU_le hδU0 hδU
        R A D2 D3 hR hA hD2 hD3 hU2 hT3 hTU2 hTU3

set_option linter.unusedVariables false in
/-- The connection insertion kernel preserves the critical two-arm pair
shape; in dimension three its two slot extensions contribute only a fixed
factor. -/
theorem connIns_sub_tame
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
        (R A D2 D3 : ℝ),
        0 ≤ R → 0 ≤ A → 0 ≤ D2 → 0 ≤ D3 →
        lowJetSq (I := I) (M := M) g 2 U ≤ R ^ 2 →
        lowJetSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
        lowJetSq (I := I) (M := M) g 2 (T - U) ≤ D2 ^ 2 →
        lowJetSq (I := I) (M := M) g 3 (T - U) ≤ D3 ^ 2 →
      lowJetSq (I := I) (M := M) g 2
          (connDiffContrInsertionField (I := I) g gT -
            connDiffContrInsertionField (I := I) g gU) ≤
        (B0 R * D3 + B1 R * D2 + B1 R * A * D2) ^ 2 := by
  obtain ⟨C0, C1, hC0, hC1, hpair⟩ :=
    connSec_sub_tame (I := I) (M := M) hDim g hδ₀0 hδ₀
  let B0 : ℝ → ℝ := fun R => 3 * C0 R
  let B1 : ℝ → ℝ := fun R => 3 * C1 R
  refine ⟨B0, B1, fun R hR => mul_nonneg (by norm_num) (hC0 R hR),
    fun R hR => mul_nonneg (by norm_num) (hC1 R hR), ?_⟩
  intro gT gU T U hT hU hTtie hUtie
    δT δU hδT_le hδT0 hδT hδU_le hδU0 hδU
    R A D2 D3 hR hA hD2 hD3 hU2 hT3 hTU2 hTU3
  let X : ℝ := C0 R * D3 + C1 R * D2 + C1 R * A * D2
  have hX :
      lowJetSq (I := I) (M := M) g 2
          (connDiffSection (I := I) gT g -
            connDiffSection (I := I) gU g) ≤ X ^ 2 := by
    simpa only [X] using
      hpair gT gU T U hT hU hTtie hUtie
        hδT_le hδT0 hδT hδU_le hδU0 hδU
        R A D2 D3 hR hA hD2 hD3 hU2 hT3 hTU2 hTU3
  have h9 : 0 ≤ (9 : ℝ) := by norm_num
  calc
    lowJetSq (I := I) (M := M) g 2
        (connDiffContrInsertionField (I := I) g gT -
          connDiffContrInsertionField (I := I) g gU) =
      lowJetSq (I := I) (M := M) g 2
        (reindexCoeffGen (I := I) (M := M) g 3 4
          (slotExtend (I := I) (M := M) g 2 3
            (slotExtend (I := I) (M := M) g 1 2
              (connDiffSection (I := I) gT g -
                connDiffSection (I := I) gU g)))
          coreInPerm201) := by
            rw [connIns_sub_eq (I := I) (M := M) g gT gU]
    _ ≤ 9 * lowJetSq (I := I) (M := M) g 2
        (connDiffSection (I := I) gT g -
          connDiffSection (I := I) gU g) :=
      insert_h2 (I := I) (M := M) hDim g _
    _ ≤ 9 * X ^ 2 := mul_le_mul_of_nonneg_left hX h9
    _ = (B0 R * D3 + B1 R * D2 + B1 R * A * D2) ^ 2 := by
      simp only [B0, B1, X]
      ring

set_option linter.unusedVariables false in
/-- The order-one Ricci connection kernel inherits the same critical
two-arm estimate from the insertion field. -/
theorem ricciKer_sub_tame
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
        (R A D2 D3 : ℝ),
        0 ≤ R → 0 ≤ A → 0 ≤ D2 → 0 ≤ D3 →
        lowJetSq (I := I) (M := M) g 2 U ≤ R ^ 2 →
        lowJetSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
        lowJetSq (I := I) (M := M) g 2 (T - U) ≤ D2 ^ 2 →
        lowJetSq (I := I) (M := M) g 3 (T - U) ≤ D3 ^ 2 →
      lowJetSq (I := I) (M := M) g 2
          (linearizedRicciConnDiffOrder1KernelField (I := I) g gT -
            linearizedRicciConnDiffOrder1KernelField (I := I) g gU) ≤
        (B0 R * D3 + B1 R * D2 + B1 R * A * D2) ^ 2 := by
  obtain ⟨C0, C1, hC0, hC1, hpair⟩ :=
    connIns_sub_tame (I := I) (M := M) hDim g hδ₀0 hδ₀
  let B0 : ℝ → ℝ := fun R => 5 * C0 R
  let B1 : ℝ → ℝ := fun R => 5 * C1 R
  refine ⟨B0, B1, fun R hR => mul_nonneg (by norm_num) (hC0 R hR),
    fun R hR => mul_nonneg (by norm_num) (hC1 R hR), ?_⟩
  intro gT gU T U hT hU hTtie hUtie
    δT δU hδT_le hδT0 hδT hδU_le hδU0 hδU
    R A D2 D3 hR hA hD2 hD3 hU2 hT3 hTU2 hTU3
  let X : ℝ := C0 R * D3 + C1 R * D2 + C1 R * A * D2
  have hX :
      lowJetSq (I := I) (M := M) g 2
          (connDiffContrInsertionField (I := I) g gT -
            connDiffContrInsertionField (I := I) g gU) ≤ X ^ 2 := by
    simpa only [X] using
      hpair gT gU T U hT hU hTtie hUtie
        hδT_le hδT0 hδT hδU_le hδU0 hδU
        R A D2 D3 hR hA hD2 hD3 hU2 hT3 hTU2 hTU3
  have h25 : 0 ≤ (25 : ℝ) := by norm_num
  calc
    lowJetSq (I := I) (M := M) g 2
        (linearizedRicciConnDiffOrder1KernelField (I := I) g gT -
          linearizedRicciConnDiffOrder1KernelField (I := I) g gU) =
      lowJetSq (I := I) (M := M) g 2
        (kerOfIns (I := I) (M := M) g
          (connDiffContrInsertionField (I := I) g gT -
            connDiffContrInsertionField (I := I) g gU)) := by
              rw [ricciKer_sub_eq (I := I) (M := M) g gT gU]
    _ ≤ 25 * lowJetSq (I := I) (M := M) g 2
        (connDiffContrInsertionField (I := I) g gT -
          connDiffContrInsertionField (I := I) g gU) :=
      kerOfIns_h2 (I := I) (M := M) g _
    _ ≤ 25 * X ^ 2 := mul_le_mul_of_nonneg_left hX h25
    _ = (B0 R * D3 + B1 R * D2 + B1 R * A * D2) ^ 2 := by
      simp only [B0, B1, X]
      ring

private theorem raise_rev
    (g gm : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      gm.inner y v w =
        g.inner y v w + ccTensorBilinSymm (I := I) g T y v w) :
    symmRaiseEndo (I := I) (M := M) g T =
      gInvDiffRaisedEndoField (I := I) gm g := by
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro v
  apply (metricFlatMap (I := I) g x).injective
  ext w
  rw [metricFlatMap_apply, metricFlatMap_apply]
  rw [symmRaiseEndo_apply, inner_symmRaiseEndo]
  rw [show gInvDiffRaisedEndoField (I := I) gm g x =
      gInvDiffRaisedEndo (I := I) gm g x from rfl]
  rw [inner_g1_gInvDiffRaisedEndo (I := I) gm g x v w]
  rw [htie x v w]
  ring

private theorem raise_cancel
    (a b : SmoothRiemannianMetric I M) (x : M) :
    (gInvRaisedEndo (I := I) a b x).comp
        (gInvRaisedEndo (I := I) b a x) =
      ContinuousLinearMap.id ℝ (TangentSpace I x) := by
  apply ContinuousLinearMap.ext
  intro v
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
    gInvRaisedEndo_apply, gInvRaisedEndo_apply]
  rw [g0FlatCLM_inverseMetricSharpFib (I := I) a x
    (g0FlatCLM (I := I) b x v)]
  rw [inverseMetricSharpFib_g0FlatCLM (I := I) b x v]

private theorem raise_pair
    (g gT gU : SmoothRiemannianMetric I M)
    (T U : SmoothCcTensor g 0 2)
    (hTtie : ∀ (y : M) (v w : TangentSpace I y),
      gT.inner y v w =
        g.inner y v w + ccTensorBilinSymm (I := I) g T y v w)
    (hUtie : ∀ (y : M) (v w : TangentSpace I y),
      gU.inner y v w =
        g.inner y v w + ccTensorBilinSymm (I := I) g U y v w)
    (x : M) :
    gInvRaisedEndo (I := I) g gT x -
        gInvRaisedEndo (I := I) g gU x =
      -((gInvRaisedEndo (I := I) g gT x).comp
        ((symmRaiseEndo (I := I) (M := M) g (T - U) x).comp
          (gInvRaisedEndo (I := I) g gU x))) := by
  let FT := gInvRaisedEndo (I := I) g gT x
  let FU := gInvRaisedEndo (I := I) g gU x
  let RT := gInvRaisedEndo (I := I) gT g x
  let RU := gInvRaisedEndo (I := I) gU g x
  let PT := symmRaiseEndo (I := I) (M := M) g T x
  let PU := symmRaiseEndo (I := I) (M := M) g U x
  let P := symmRaiseEndo (I := I) (M := M) g (T - U) x
  have hRT : RT = PT + 1 := by
    apply ContinuousLinearMap.ext
    intro v
    have hr := congrArg (fun F => F x)
      (raise_rev (I := I) (M := M) g gT T hTtie)
    have hv := congrArg (fun L => L v) hr
    change gInvRaisedEndo (I := I) gT g x v = PT v + v
    rw [gInvRaisedEndo_eq_diff_add_id]
    exact congrArg (fun z => z + v) hv.symm
  have hRU : RU = PU + 1 := by
    apply ContinuousLinearMap.ext
    intro v
    have hr := congrArg (fun F => F x)
      (raise_rev (I := I) (M := M) g gU U hUtie)
    have hv := congrArg (fun L => L v) hr
    change gInvRaisedEndo (I := I) gU g x v = PU v + v
    rw [gInvRaisedEndo_eq_diff_add_id]
    exact congrArg (fun z => z + v) hv.symm
  have hP : P = PT - PU := by
    have hs :
        symmRaiseEndo (I := I) (M := M) g (T - U) =
          symmRaiseEndo (I := I) (M := M) g T -
            symmRaiseEndo (I := I) (M := M) g U := by
      calc
        symmRaiseEndo (I := I) (M := M) g (T - U) =
            symmRaiseEndo (I := I) (M := M) g (T + (-1 : ℝ) • U) := by
              rw [neg_one_smul, sub_eq_add_neg]
        _ = symmRaiseEndo (I := I) (M := M) g T +
              symmRaiseEndo (I := I) (M := M) g ((-1 : ℝ) • U) := by
                rw [symmRaiseEndo_add]
        _ = symmRaiseEndo (I := I) (M := M) g T +
              (-1 : ℝ) • symmRaiseEndo (I := I) (M := M) g U := by
                rw [symmRaiseEndo_smul]
        _ = symmRaiseEndo (I := I) (M := M) g T -
              symmRaiseEndo (I := I) (M := M) g U := by
                simpa only [sub_eq_add_neg] using
                  congrArg
                    (fun z => symmRaiseEndo (I := I) (M := M) g T + z)
                    (neg_one_smul ℝ
                      (symmRaiseEndo (I := I) (M := M) g U))
    exact congrArg (fun F => F x) hs
  have hFTC : FT * RT = 1 := by
    simpa only [FT, RT, ContinuousLinearMap.mul_def] using
      raise_cancel (I := I) (M := M) g gT x
  have hUCF : RU * FU = 1 := by
    simpa only [RU, FU, ContinuousLinearMap.mul_def] using
      raise_cancel (I := I) (M := M) gU g x
  change FT - FU = -(FT.comp (P.comp FU))
  rw [show FT.comp (P.comp FU) = FT * P * FU by
    simp only [ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_assoc]]
  calc
    FT - FU = FT * (RU * FU) - (FT * RT) * FU := by
      rw [hUCF, hFTC, mul_one, one_mul]
    _ = FT * (RU - RT) * FU := by noncomm_ring
    _ = -(FT * P * FU) := by
      rw [hRT, hRU, hP]
      noncomm_ring

private noncomputable def perturb0
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2) :
    SmoothCcTensor g 1 1 :=
  slotInsertEndoCc (I := I) (M := M) g 0
    (symmRaiseEndo (I := I) (M := M) g T)

private theorem sharp_pair
    (g gT gU : SmoothRiemannianMetric I M)
    (T U : SmoothCcTensor g 0 2)
    (hTtie : ∀ (y : M) (v w : TangentSpace I y),
      gT.inner y v w =
        g.inner y v w + ccTensorBilinSymm (I := I) g T y v w)
    (hUtie : ∀ (y : M) (v w : TangentSpace I y),
      gU.inner y v w =
        g.inner y v w + ccTensorBilinSymm (I := I) g U y v w) :
    sharpFlatEndoCc (I := I) g gT -
        sharpFlatEndoCc (I := I) g gU =
      -appCcRS (I := I) (M := M) g 1 1 1
        (sharpFlatEndoCc (I := I) g gU)
        (appCcRS (I := I) (M := M) g 1 1 1
          (perturb0 (I := I) (M := M) g (T - U))
          (sharpFlatEndoCc (I := I) g gT)) := by
  rw [sharp_eq_slot0 (I := I) (M := M) g gT,
    sharp_eq_slot0 (I := I) (M := M) g gU,
    ← slotInsertEndoCc_sub]
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [SmoothCcTensor.toSection_neg]
  simp only [ContMDiffSection.coe_neg, Pi.neg_apply]
  rw [appCcRS_toSection, appCcRS_toSection]
  simp only [perturb0, slotInsertEndoCc_toSection,
    fullRaisedEndoField_apply]
  rw [slotInsertFib_comp, slotInsertFib_comp]
  rw [ContMDiffSection.coe_sub, Pi.sub_apply]
  have hinv :
      gInvDiffRaisedEndoField (I := I) g gT x -
          gInvDiffRaisedEndoField (I := I) g gU x =
        gInvRaisedEndo (I := I) g gT x -
          gInvRaisedEndo (I := I) g gU x := by
    apply ContinuousLinearMap.ext
    intro v
    simp only [ContinuousLinearMap.sub_apply,
      gInvRaisedEndo_eq_diff_add_id]
    abel
  rw [show fullRaisedEndoField (I := I) (M := M) g gT x -
        fullRaisedEndoField (I := I) (M := M) g gU x =
      gInvDiffRaisedEndoField (I := I) g gT x -
        gInvDiffRaisedEndoField (I := I) g gU x by
    apply ContinuousLinearMap.ext
    intro v
    rw [fullRaisedEndoField_apply, fullRaisedEndoField_apply]
    simp only [gInvRaisedEndo_eq_diff_add_id,
      ContinuousLinearMap.sub_apply]
    abel]
  rw [hinv]
  rw [raise_pair (I := I) (M := M) g gT gU T U hTtie hUtie x]
  rw [show -((gInvRaisedEndo (I := I) g gT x).comp
        ((symmRaiseEndo (I := I) (M := M) g (T - U) x).comp
          (gInvRaisedEndo (I := I) g gU x))) =
      (-1 : ℝ) • ((gInvRaisedEndo (I := I) g gT x).comp
        ((symmRaiseEndo (I := I) (M := M) g (T - U) x).comp
          (gInvRaisedEndo (I := I) g gU x))) by rw [neg_one_smul],
    slotInsertEndoFib_smul_left, neg_one_smul]
  rw [ContinuousLinearMap.comp_assoc]

private theorem jet_add1
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

private theorem jet_smul1
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

private theorem reindex_h2_eq
    (g : SmoothRiemannianMetric I M) {r s : ℕ}
    (S : SmoothCcTensor g r s) (ρ : Equiv.Perm (Fin r)) :
    lowJetSq (I := I) (M := M) g 2
        (reindexCoeffGen (I := I) (M := M) g r s S ρ) =
      lowJetSq (I := I) (M := M) g 2 S := by
  unfold lowJetSq
  apply Finset.sum_congr rfl
  intro q _
  rw [iteratedCovGrad_reindexCoeffGen (I := I) (M := M),
    norm_reindexCoeffGen_eq (I := I) (M := M)]

private theorem corrPk3_h2
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M)
    (P : SmoothCcTensor g 0 2) :
    lowJetSq (I := I) (M := M) g 2
        (corrPk3 (I := I) (M := M) g P) ≤
      27 * lowJetSq (I := I) (M := M) g 2 P := by
  let fr : ℝ := Module.finrank ℝ E
  have hper : ∀ q : ℕ,
      ‖iteratedCovGrad (I := I) g 3 5 q
          (corrPk3 (I := I) (M := M) g P)‖ ≤
        Real.sqrt fr *
          (Real.sqrt fr *
            (Real.sqrt fr *
              ‖iteratedCovGrad (I := I) g 0 2 q P‖)) := by
    intro q
    calc
      ‖iteratedCovGrad (I := I) g 3 5 q
          (corrPk3 (I := I) (M := M) g P)‖ ≤
        Real.sqrt (Module.finrank ℝ E) *
          ‖iteratedCovGrad (I := I) g 2 4 q
            (slotExtend (I := I) (M := M) g 1 3
              (slotExtend (I := I) (M := M) g 0 2 P))‖ := by
            simpa only [corrPk3, fr] using
              slotExt_norm_le (I := I) (M := M) g 2 4 q
                (slotExtend (I := I) (M := M) g 1 3
                  (slotExtend (I := I) (M := M) g 0 2 P))
      _ ≤ Real.sqrt fr *
          (Real.sqrt fr *
            ‖iteratedCovGrad (I := I) g 1 3 q
              (slotExtend (I := I) (M := M) g 0 2 P)‖) := by
            exact mul_le_mul_of_nonneg_left
              (slotExt_norm_le (I := I) (M := M) g 1 3 q
                (slotExtend (I := I) (M := M) g 0 2 P))
              (Real.sqrt_nonneg _)
      _ ≤ Real.sqrt fr *
          (Real.sqrt fr *
            (Real.sqrt fr *
              ‖iteratedCovGrad (I := I) g 0 2 q P‖)) := by
            exact mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left
                (slotExt_norm_le (I := I) (M := M) g 0 2 q P)
                (Real.sqrt_nonneg _))
              (Real.sqrt_nonneg _)
  have hsq : ∀ q : ℕ,
      ‖iteratedCovGrad (I := I) g 3 5 q
          (corrPk3 (I := I) (M := M) g P)‖ ^ 2 ≤
        27 * ‖iteratedCovGrad (I := I) g 0 2 q P‖ ^ 2 := by
    intro q
    have h := pow_le_pow_left₀
      (norm_nonneg
        (iteratedCovGrad (I := I) g 3 5 q
          (corrPk3 (I := I) (M := M) g P)))
      (hper q) 2
    have hs : Real.sqrt ((3 : ℕ) : ℝ) ^ 2 = 3 :=
      Real.sq_sqrt (by norm_num)
    calc
      ‖iteratedCovGrad (I := I) g 3 5 q
          (corrPk3 (I := I) (M := M) g P)‖ ^ 2 ≤
        (Real.sqrt fr *
          (Real.sqrt fr *
            (Real.sqrt fr *
              ‖iteratedCovGrad (I := I) g 0 2 q P‖))) ^ 2 := h
      _ = 27 * ‖iteratedCovGrad (I := I) g 0 2 q P‖ ^ 2 := by
        simp only [fr, hDim]
        rw [show
          (Real.sqrt ((3 : ℕ) : ℝ) *
            (Real.sqrt ((3 : ℕ) : ℝ) *
              (Real.sqrt ((3 : ℕ) : ℝ) *
                ‖iteratedCovGrad (I := I) g 0 2 q P‖))) ^ 2 =
            (Real.sqrt ((3 : ℕ) : ℝ) ^ 2) ^ 3 *
              ‖iteratedCovGrad (I := I) g 0 2 q P‖ ^ 2 by ring,
          hs]
        norm_num
  unfold lowJetSq
  calc
    ∑ q ∈ Finset.range 3,
        ‖iteratedCovGrad (I := I) g 3 5 q
          (corrPk3 (I := I) (M := M) g P)‖ ^ 2 ≤
      ∑ q ∈ Finset.range 3,
        27 * ‖iteratedCovGrad (I := I) g 0 2 q P‖ ^ 2 :=
      Finset.sum_le_sum fun q _ => hsq q
    _ = 27 * ∑ q ∈ Finset.range 3,
        ‖iteratedCovGrad (I := I) g 0 2 q P‖ ^ 2 := by
      rw [Finset.mul_sum]

private theorem corrPhi_h2
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (P : SmoothCcTensor g 0 2) (σ : Equiv.Perm (Fin 5)),
        lowJetSq (I := I) (M := M) g 2
            (corrPhi (I := I) (M := M) g P σ) ≤
          C * lowJetSq (I := I) (M := M) g 2 P := by
  obtain ⟨Ca, hCa, happ⟩ :=
    app_h2_mul (I := I) (M := M) hDim g 3 5 3
  let J : ℝ := lowJetSq (I := I) (M := M) g 2
    (cometricDoubleTraceField (I := I) g 3)
  let C : ℝ := 27 * Ca * J
  have hJ : 0 ≤ J :=
    jet_nonneg (I := I) (M := M) g
      (cometricDoubleTraceField (I := I) g 3)
  have hC : 0 ≤ C :=
    mul_nonneg (mul_nonneg (by norm_num) hCa) hJ
  refine ⟨C, hC, ?_⟩
  intro P σ
  have hpk := corrPk3_h2 (I := I) (M := M) hDim g P
  have hraw := happ
    (reindexCoeffGen (I := I) (M := M) g 5 3
      (cometricDoubleTraceField (I := I) g 3) σ)
    (corrPk3 (I := I) (M := M) g P)
  rw [reindex_h2_eq (I := I) (M := M) g
    (cometricDoubleTraceField (I := I) g 3) σ] at hraw
  calc
    lowJetSq (I := I) (M := M) g 2
        (corrPhi (I := I) (M := M) g P σ) ≤
      Ca * J *
        lowJetSq (I := I) (M := M) g 2
          (corrPk3 (I := I) (M := M) g P) := by
            simpa only [corrPhi, J] using hraw
    _ ≤ Ca * J *
        (27 * lowJetSq (I := I) (M := M) g 2 P) :=
      mul_le_mul_of_nonneg_left hpk (mul_nonneg hCa hJ)
    _ = C * lowJetSq (I := I) (M := M) g 2 P := by
      simp only [C]
      ring

private noncomputable def fourOf
    (g : SmoothRiemannianMetric I M) (P : SmoothCcTensor g 4 2) :
    SmoothCcTensor g 4 2 :=
  ((1 : ℝ) / 2) •
    (reindexCoeffGen (I := I) (M := M) g 4 2 P
        fourTraceArgPerm0231 +
      reindexCoeffGen (I := I) (M := M) g 4 2 P
        fourTraceArgPerm0321 -
      P -
      reindexCoeffGen (I := I) (M := M) g 4 2 P
        fourTraceArgPerm2301)

private theorem pure_eq_trace1
    (g gm : SmoothRiemannianMetric I M) :
    ricciArmPrincipalCoeffPure (I := I) (M := M) g gm =
      pureTrace (I := I) (M := M) g gm 2 := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [ricciArmPrincipalCoeffPure_toSection, pureTrace_toSection]

private theorem four_eq
    (g gm : SmoothRiemannianMetric I M) :
    ricciCometricFourTraceCastG0 (I := I) g gm =
      fourOf (I := I) (M := M) g
        (pureTrace (I := I) (M := M) g gm 2) := by
  rw [← pure_eq_trace1 (I := I) (M := M) g gm]
  exact ricciCometricFourTraceCastG0_eq_reindex_combination
    (I := I) g gm

private theorem four_sub
    (g : SmoothRiemannianMetric I M) (P Q : SmoothCcTensor g 4 2) :
    fourOf (I := I) (M := M) g (P - Q) =
      fourOf (I := I) (M := M) g P -
        fourOf (I := I) (M := M) g Q := by
  simp only [fourOf, reindex_sub (I := I) (M := M) g 4 2,
    smul_sub]
  module

private theorem four_h2
    (g : SmoothRiemannianMetric I M) (P : SmoothCcTensor g 4 2) :
    lowJetSq (I := I) (M := M) g 2
        (fourOf (I := I) (M := M) g P) ≤
      22 * lowJetSq (I := I) (M := M) g 2 P := by
  let R₁ : SmoothCcTensor g 4 2 :=
    reindexCoeffGen (I := I) (M := M) g 4 2 P
      fourTraceArgPerm0231
  let R₂ : SmoothCcTensor g 4 2 :=
    reindexCoeffGen (I := I) (M := M) g 4 2 P
      fourTraceArgPerm0321
  let R₃ : SmoothCcTensor g 4 2 :=
    reindexCoeffGen (I := I) (M := M) g 4 2 P
      fourTraceArgPerm2301
  have hR₁ :
      lowJetSq (I := I) (M := M) g 2 R₁ =
        lowJetSq (I := I) (M := M) g 2 P :=
    reindex_h2_eq (I := I) (M := M) g P fourTraceArgPerm0231
  have hR₂ :
      lowJetSq (I := I) (M := M) g 2 R₂ =
        lowJetSq (I := I) (M := M) g 2 P :=
    reindex_h2_eq (I := I) (M := M) g P fourTraceArgPerm0321
  have hR₃ :
      lowJetSq (I := I) (M := M) g 2 R₃ =
        lowJetSq (I := I) (M := M) g 2 P :=
    reindex_h2_eq (I := I) (M := M) g P fourTraceArgPerm2301
  have h12 :
      lowJetSq (I := I) (M := M) g 2 (R₁ + R₂) ≤
        4 * lowJetSq (I := I) (M := M) g 2 P := by
    have h := jet_add1 (I := I) (M := M) g 2 R₁ R₂
    rw [hR₁, hR₂] at h
    linarith
  have h123 :
      lowJetSq (I := I) (M := M) g 2 (R₁ + R₂ - P) ≤
        10 * lowJetSq (I := I) (M := M) g 2 P := by
    have h := jet_sub (I := I) (M := M) g 2 (R₁ + R₂) P
    nlinarith [jet_nonneg (I := I) (M := M) (m := 2) g P]
  have h1234 :
      lowJetSq (I := I) (M := M) g 2 (R₁ + R₂ - P - R₃) ≤
        22 * lowJetSq (I := I) (M := M) g 2 P := by
    have h := jet_sub (I := I) (M := M) g 2 (R₁ + R₂ - P) R₃
    rw [hR₃] at h
    nlinarith [jet_nonneg (I := I) (M := M) (m := 2) g P]
  change lowJetSq (I := I) (M := M) g 2
      (((1 : ℝ) / 2) • (R₁ + R₂ - P - R₃)) ≤ _
  rw [jet_smul1]
  calc
    ((1 : ℝ) / 2) ^ 2 *
        lowJetSq (I := I) (M := M) g 2 (R₁ + R₂ - P - R₃) ≤
      lowJetSq (I := I) (M := M) g 2 (R₁ + R₂ - P - R₃) := by
        nlinarith [jet_nonneg (I := I) (M := M) (m := 2) g
          (R₁ + R₂ - P - R₃)]
    _ ≤ 22 * lowJetSq (I := I) (M := M) g 2 P := h1234

private theorem ricci1_sub_eq
    (g gT gU : SmoothRiemannianMetric I M) :
    linearizedRicciConnDiffOrder1CoeffField (I := I) (M := M) g gT -
        linearizedRicciConnDiffOrder1CoeffField (I := I) (M := M) g gU =
      appCcRS (I := I) (M := M) g 3 4 2
          (ricciCometricFourTraceCastG0 (I := I) g gU)
          (linearizedRicciConnDiffOrder1KernelField (I := I) g gT -
            linearizedRicciConnDiffOrder1KernelField (I := I) g gU) +
        appCcRS (I := I) (M := M) g 3 4 2
          (ricciCometricFourTraceCastG0 (I := I) g gT -
            ricciCometricFourTraceCastG0 (I := I) g gU)
          (linearizedRicciConnDiffOrder1KernelField (I := I) g gT) := by
  rw [linearizedRicciConnDiffOrder1CoeffField_eq_appCcRS
      (I := I) (M := M) g gT,
    linearizedRicciConnDiffOrder1CoeffField_eq_appCcRS
      (I := I) (M := M) g gU,
    appCcRS_sub_right, appCcRS_sub_left]
  module

private theorem connSec_zero
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

private theorem connIns_zero
    (g : SmoothRiemannianMetric I M) :
    connDiffContrInsertionField (I := I) g g = 0 := by
  have h := connIns_sub_eq (I := I) (M := M) g g g
  rw [connDiffContrInsertionField_eq_reindex_slotExtend_two
    (I := I) (M := M) g g,
    connSec_zero (I := I) (M := M) g]
  simpa only [sub_self] using h.symm

private theorem ricciKer_zero
    (g : SmoothRiemannianMetric I M) :
    linearizedRicciConnDiffOrder1KernelField (I := I) g g = 0 := by
  have hzero :
      kerOfIns (I := I) (M := M) g
          (0 : SmoothCcTensor g 3 4) = 0 := by
    have h := kerOfIns_sub (I := I) (M := M) g
      (0 : SmoothCcTensor g 3 4) 0
    simpa only [sub_self] using h
  rw [ricciKer_eq (I := I) (M := M) g g,
    connIns_zero (I := I) (M := M) g, hzero]

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option linter.unusedVariables false in
/-- On a sufficiently small spectral `H²` metric ball, the order-one Ricci
coefficient is Lipschitz with the critical `H³/H²` two-arm modulus. -/
theorem ricci1_pair_h2
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ B0 B1 : ℝ,
      0 < ρ ∧ 0 ≤ B0 ∧ 0 ≤ B1 ∧
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
      let D2 :=
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U)‖
      lowJetSq (I := I) (M := M) g 2
          (linearizedRicciConnDiffOrder1CoeffField
              (I := I) (M := M) g gT -
            linearizedRicciConnDiffOrder1CoeffField
              (I := I) (M := M) g gU) ≤
        (B0 * D3 + B1 * D2 + B1 * A * D2) ^ 2 := by
  obtain ⟨ρp, Cp, hρp, hCp, hpurePair⟩ :=
    LowBaseInternal.trace2_pair_h2 (I := I) (M := M) hDim g
  obtain ⟨ρb, Cb, hρb, hCb, hpureBdd⟩ :=
    LowBaseInternal.trace2_h2_bdd (I := I) (M := M) hDim g
  obtain ⟨Ch, hCh, hhs⟩ :=
    hs2_low2 (I := I) (M := M) g 2
  obtain ⟨K0, K1, hK0, hK1, hker⟩ :=
    ricciKer_sub_tame (I := I) (M := M) hDim g
      (δ₀ := (1 : ℝ) / 3) (by norm_num) (by norm_num)
  obtain ⟨Ca, hCa, happ⟩ :=
    app_h2_mul (I := I) (M := M) hDim g 3 4 2
  let ρ : ℝ := min ρp ρb
  let R0 : ℝ := Ch * ρ
  let X0 : ℝ := K0 R0
  let X1 : ℝ := K1 R0 * Ch
  let Y0 : ℝ := K0 0 + K1 0 + K1 0 * R0
  let H0 : ℝ := Real.sqrt Ca
  let H : ℝ := 2 * H0
  let B0 : ℝ := H * (5 * Cb * X0)
  let B1 : ℝ := H * (5 * Cb * X1 + 5 * Cp * Y0)
  have hρ : 0 < ρ := lt_min hρp hρb
  have hR0 : 0 ≤ R0 := mul_nonneg hCh hρ.le
  have hX0 : 0 ≤ X0 := hK0 R0 hR0
  have hX1 : 0 ≤ X1 := mul_nonneg (hK1 R0 hR0) hCh
  have hY0 : 0 ≤ Y0 := by
    exact add_nonneg
      (add_nonneg (hK0 0 (by norm_num)) (hK1 0 (by norm_num)))
      (mul_nonneg (hK1 0 (by norm_num)) hR0)
  have hH0 : 0 ≤ H0 := Real.sqrt_nonneg _
  have hH0sq : H0 ^ 2 = Ca := by
    simpa only [H0] using Real.sq_sqrt hCa
  have hH : 0 ≤ H := mul_nonneg (by norm_num) hH0
  have hB0 : 0 ≤ B0 :=
    mul_nonneg hH (mul_nonneg (mul_nonneg (by norm_num) hCb) hX0)
  have hB1 : 0 ≤ B1 :=
    mul_nonneg hH
      (add_nonneg
        (mul_nonneg (mul_nonneg (by norm_num) hCb) hX1)
        (mul_nonneg (mul_nonneg (by norm_num) hCp) hY0))
  refine ⟨ρ, B0, B1, hρ, hB0, hB1, ?_⟩
  intro gT gU T U hT hU hTtie hUtie δ hδ_le hδ0
    hδT hδU hδZ hTHs hUHs A D3 hA hD3 hT3 hTU3
  dsimp only
  let N : ℝ :=
    ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U)‖
  let TrT : SmoothCcTensor g 4 2 :=
    ricciCometricFourTraceCastG0 (I := I) g gT
  let TrU : SmoothCcTensor g 4 2 :=
    ricciCometricFourTraceCastG0 (I := I) g gU
  let KT : SmoothCcTensor g 3 4 :=
    linearizedRicciConnDiffOrder1KernelField (I := I) g gT
  let KU : SmoothCcTensor g 3 4 :=
    linearizedRicciConnDiffOrder1KernelField (I := I) g gU
  let XD : ℝ := X0 * D3 + X1 * N + X1 * A * N
  let YT : ℝ := Y0 * A
  have hN : 0 ≤ N := norm_nonneg _
  have hTHsp : ‖ccTensorToHs (I := I) (M := M) g 2
      (2 : ℝ) T‖ ≤ ρp := hTHs.trans (min_le_left _ _)
  have hUHsp : ‖ccTensorToHs (I := I) (M := M) g 2
      (2 : ℝ) U‖ ≤ ρp := hUHs.trans (min_le_left _ _)
  have hTHsb : ‖ccTensorToHs (I := I) (M := M) g 2
      (2 : ℝ) T‖ ≤ ρb := hTHs.trans (min_le_right _ _)
  have hUHsb : ‖ccTensorToHs (I := I) (M := M) g 2
      (2 : ℝ) U‖ ≤ ρb := hUHs.trans (min_le_right _ _)
  have hpD := hpurePair T U gT gU hTtie hUtie hTHsp hUHsp
  have hpU := hpureBdd U gU hUtie hUHsb
  have hTrD :
      lowJetSq (I := I) (M := M) g 2 (TrT - TrU) ≤
        (5 * Cp * N) ^ 2 := by
    have heq : TrT - TrU =
        fourOf (I := I) (M := M) g
          (pureTrace (I := I) (M := M) g gT 2 -
            pureTrace (I := I) (M := M) g gU 2) := by
      rw [show TrT =
          fourOf (I := I) (M := M) g
            (pureTrace (I := I) (M := M) g gT 2) by
            exact four_eq (I := I) (M := M) g gT,
        show TrU =
          fourOf (I := I) (M := M) g
            (pureTrace (I := I) (M := M) g gU 2) by
            exact four_eq (I := I) (M := M) g gU,
        ← four_sub]
    rw [heq]
    calc
      lowJetSq (I := I) (M := M) g 2
          (fourOf (I := I) (M := M) g
            (pureTrace (I := I) (M := M) g gT 2 -
              pureTrace (I := I) (M := M) g gU 2)) ≤
        22 * lowJetSq (I := I) (M := M) g 2
          (pureTrace (I := I) (M := M) g gT 2 -
            pureTrace (I := I) (M := M) g gU 2) :=
        four_h2 (I := I) (M := M) g _
      _ ≤ 22 * (Cp * N) ^ 2 := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        simpa only [N] using hpD
      _ ≤ (5 * Cp * N) ^ 2 := by
        nlinarith [sq_nonneg (Cp * N)]
  have hTrU :
      lowJetSq (I := I) (M := M) g 2 TrU ≤
        (5 * Cb) ^ 2 := by
    rw [show TrU =
        fourOf (I := I) (M := M) g
          (pureTrace (I := I) (M := M) g gU 2) by
      exact four_eq (I := I) (M := M) g gU]
    calc
      lowJetSq (I := I) (M := M) g 2
          (fourOf (I := I) (M := M) g
            (pureTrace (I := I) (M := M) g gU 2)) ≤
        22 * lowJetSq (I := I) (M := M) g 2
          (pureTrace (I := I) (M := M) g gU 2) :=
        four_h2 (I := I) (M := M) g _
      _ ≤ 22 * Cb ^ 2 :=
        mul_le_mul_of_nonneg_left hpU (by norm_num)
      _ ≤ (5 * Cb) ^ 2 := by nlinarith [sq_nonneg Cb]
  have hU2 :
      lowJetSq (I := I) (M := M) g 2 U ≤ R0 ^ 2 := by
    calc
      lowJetSq (I := I) (M := M) g 2 U ≤
          (Ch * ‖ccTensorToHs (I := I) (M := M) g 2
            (2 : ℝ) U‖) ^ 2 := by
        simpa only [lowJetSq, Nat.reduceAdd] using hhs U
      _ ≤ (Ch * ρ) ^ 2 :=
        pow_le_pow_left₀
          (mul_nonneg hCh (norm_nonneg _))
          (mul_le_mul_of_nonneg_left hUHs hCh) 2
      _ = R0 ^ 2 := rfl
  have hTU2 :
      lowJetSq (I := I) (M := M) g 2 (T - U) ≤
        (Ch * N) ^ 2 := by
    simpa only [lowJetSq, Nat.reduceAdd, N] using hhs (T - U)
  have hKD :
      lowJetSq (I := I) (M := M) g 2 (KT - KU) ≤ XD ^ 2 := by
    have hraw := hker gT gU T U hT hU hTtie hUtie
      hδ_le hδ0 hδT hδ_le hδ0 hδU
      R0 A (Ch * N) D3 hR0 hA (mul_nonneg hCh hN) hD3
      hU2 hT3 hTU2 hTU3
    convert hraw using 1
    simp only [XD, X0, X1]
    ring
  let JT2 : ℝ := lowJetSq (I := I) (M := M) g 2 T
  let DT : ℝ := Real.sqrt JT2
  have hJT2 : 0 ≤ JT2 := by
    exact jet_nonneg (I := I) (M := M) (m := 2) g T
  have hDT : 0 ≤ DT := Real.sqrt_nonneg _
  have hDTsq : DT ^ 2 = JT2 := by
    simpa only [DT] using Real.sq_sqrt hJT2
  have hJT23 : JT2 ≤ lowJetSq (I := I) (M := M) g 3 T := by
    simpa only [JT2] using
      jet_mono (I := I) (M := M) g (by omega : 2 ≤ 3) T
  have hDTA : DT ≤ A := by
    apply le_of_sq_le_sq
    · rw [hDTsq]
      exact hJT23.trans hT3
    · exact hA
  have hT2R :
      JT2 ≤ R0 ^ 2 := by
    calc
      JT2 ≤ (Ch * ‖ccTensorToHs (I := I) (M := M) g 2
          (2 : ℝ) T‖) ^ 2 := by
        simpa only [JT2, lowJetSq, Nat.reduceAdd] using hhs T
      _ ≤ (Ch * ρ) ^ 2 :=
        pow_le_pow_left₀
          (mul_nonneg hCh (norm_nonneg _))
          (mul_le_mul_of_nonneg_left hTHs hCh) 2
      _ = R0 ^ 2 := rfl
  have hDTR : DT ≤ R0 := by
    apply le_of_sq_le_sq
    · rw [hDTsq]
      exact hT2R
    · exact hR0
  have hZsymm : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g
          (0 : SmoothCcTensor g 0 2) x u v =
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
  have hzero2 :
      lowJetSq (I := I) (M := M) g 2
          (0 : SmoothCcTensor g 0 2) = 0 := by
    have h := jet_smul1 (I := I) (M := M) g 2 0
      (0 : SmoothCcTensor g 0 2)
    simpa using h
  have hKTraw := hker gT g T (0 : SmoothCcTensor g 0 2)
    hT hZsymm hTtie hZtie
    hδ_le hδ0 hδT hδ_le hδ0 hδZ
    0 A DT A (by norm_num) hA hDT hA
    (by rw [hzero2]; norm_num)
    hT3
    (by simpa only [sub_zero, JT2] using le_of_eq hDTsq.symm)
    (by simpa only [sub_zero] using hT3)
  have hKTraw' :
      lowJetSq (I := I) (M := M) g 2 KT ≤
        (K0 0 * A + K1 0 * DT + K1 0 * A * DT) ^ 2 := by
    simpa only [KT, ricciKer_zero (I := I) (M := M) g, sub_zero]
      using hKTraw
  have hmid : K1 0 * DT ≤ K1 0 * A :=
    mul_le_mul_of_nonneg_left hDTA (hK1 0 (by norm_num))
  have hlast : K1 0 * A * DT ≤ K1 0 * A * R0 :=
    mul_le_mul_of_nonneg_left hDTR
      (mul_nonneg (hK1 0 (by norm_num)) hA)
  have hamp :
      K0 0 * A + K1 0 * DT + K1 0 * A * DT ≤ YT := by
    simp only [YT, Y0]
    nlinarith
  have hamp0 :
      0 ≤ K0 0 * A + K1 0 * DT + K1 0 * A * DT :=
    add_nonneg
      (add_nonneg (mul_nonneg (hK0 0 (by norm_num)) hA)
        (mul_nonneg (hK1 0 (by norm_num)) hDT))
      (mul_nonneg (mul_nonneg (hK1 0 (by norm_num)) hA) hDT)
  have hKT :
      lowJetSq (I := I) (M := M) g 2 KT ≤ YT ^ 2 :=
    hKTraw'.trans (pow_le_pow_left₀ hamp0 hamp 2)
  let Z1 : ℝ := H0 * (5 * Cb) * XD
  let Z2 : ℝ := H0 * (5 * Cp) * YT * N
  have hXD : 0 ≤ XD :=
    add_nonneg
      (add_nonneg (mul_nonneg hX0 hD3)
        (mul_nonneg hX1 hN))
      (mul_nonneg (mul_nonneg hX1 hA) hN)
  have hYT : 0 ≤ YT := mul_nonneg hY0 hA
  have hZ1 : 0 ≤ Z1 :=
    mul_nonneg
      (mul_nonneg hH0 (mul_nonneg (by norm_num) hCb)) hXD
  have hZ2 : 0 ≤ Z2 :=
    mul_nonneg
      (mul_nonneg
        (mul_nonneg hH0 (mul_nonneg (by norm_num) hCp)) hYT) hN
  let V1 : SmoothCcTensor g 3 2 :=
    appCcRS (I := I) (M := M) g 3 4 2 TrU (KT - KU)
  let V2 : SmoothCcTensor g 3 2 :=
    appCcRS (I := I) (M := M) g 3 4 2 (TrT - TrU) KT
  have hV1 :
      lowJetSq (I := I) (M := M) g 2 V1 ≤ Z1 ^ 2 := by
    calc
      lowJetSq (I := I) (M := M) g 2 V1 ≤
          Ca * lowJetSq (I := I) (M := M) g 2 TrU *
            lowJetSq (I := I) (M := M) g 2 (KT - KU) := by
        simpa only [V1] using happ TrU (KT - KU)
      _ ≤ Ca * (5 * Cb) ^ 2 * XD ^ 2 := by
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left hTrU hCa) hKD
          (jet_nonneg (I := I) (M := M) (m := 2) g (KT - KU))
          (mul_nonneg hCa (sq_nonneg (5 * Cb)))
      _ = Z1 ^ 2 := by
        simp only [Z1]
        rw [← hH0sq]
        ring
  have hV2 :
      lowJetSq (I := I) (M := M) g 2 V2 ≤ Z2 ^ 2 := by
    calc
      lowJetSq (I := I) (M := M) g 2 V2 ≤
          Ca * lowJetSq (I := I) (M := M) g 2 (TrT - TrU) *
            lowJetSq (I := I) (M := M) g 2 KT := by
        simpa only [V2] using happ (TrT - TrU) KT
      _ ≤ Ca * (5 * Cp * N) ^ 2 * YT ^ 2 := by
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left hTrD hCa) hKT
          (jet_nonneg (I := I) (M := M) (m := 2) g KT)
          (mul_nonneg hCa (sq_nonneg (5 * Cp * N)))
      _ = Z2 ^ 2 := by
        simp only [Z2]
        rw [← hH0sq]
        ring
  have hlin :
      2 * (Z1 + Z2) ≤
        B0 * D3 + B1 * N + B1 * A * N := by
    have hextra : 0 ≤ H0 * (5 * Cp * Y0 * N) :=
      by positivity
    simp only [Z1, Z2, B0, B1, H, XD, YT, X0, X1, Y0]
    nlinarith
  have hlin0 : 0 ≤ 2 * (Z1 + Z2) :=
    mul_nonneg (by norm_num) (add_nonneg hZ1 hZ2)
  rw [ricci1_sub_eq (I := I) (M := M) g gT gU]
  change lowJetSq (I := I) (M := M) g 2 (V1 + V2) ≤ _
  calc
    lowJetSq (I := I) (M := M) g 2 (V1 + V2) ≤
        2 * (lowJetSq (I := I) (M := M) g 2 V1 +
          lowJetSq (I := I) (M := M) g 2 V2) :=
      jet_add1 (I := I) (M := M) g 2 V1 V2
    _ ≤ 2 * (Z1 ^ 2 + Z2 ^ 2) :=
      mul_le_mul_of_nonneg_left (add_le_add hV1 hV2) (by norm_num)
    _ ≤ (2 * (Z1 + Z2)) ^ 2 := by
      nlinarith [mul_nonneg hZ1 hZ2]
    _ ≤ (B0 * D3 + B1 * N + B1 * A * N) ^ 2 :=
      pow_le_pow_left₀ hlin0 hlin 2

private theorem lieTrace_eq
    (g gm : SmoothRiemannianMetric I M)
    (σ : Equiv.Perm (Fin 4)) :
    deTurckLieTraceCoeff (I := I) (M := M) g gm σ =
      reindexCoeffGen (I := I) (M := M) g 4 2
        (pureTrace (I := I) (M := M) g gm 2) σ := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [deTurckLieTraceCoeff_toSection, reindexCoeffGen_toSection,
    pureTrace_toSection]
  apply ContinuousLinearMap.ext
  intro D
  rw [reindexCoeffFibGen_apply, deTurckLieTraceFib,
    ContinuousLinearMap.comp_apply, domDomCongrFibPerm_apply]

private theorem slots_h2
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) (Ψ : SmoothCcTensor g 1 2) :
    lowJetSq (I := I) (M := M) g 2
        (slotExtend (I := I) (M := M) g 2 3
          (slotExtend (I := I) (M := M) g 1 2 Ψ)) ≤
      9 * lowJetSq (I := I) (M := M) g 2 Ψ := by
  have h := insert_h2 (I := I) (M := M) hDim g Ψ
  rw [reindex_h2_eq (I := I) (M := M)] at h
  exact h

private theorem liePiece_sub
    (g gT gU : SmoothRiemannianMetric I M)
    (σ : Equiv.Perm (Fin 4)) (ρ : Equiv.Perm (Fin 3))
    (ΨT ΨU : SmoothCcTensor g 1 2) :
    lieArm1Piece (I := I) (M := M) g gT σ ρ ΨT -
        lieArm1Piece (I := I) (M := M) g gU σ ρ ΨU =
      reindexCoeffGen (I := I) (M := M) g 3 2
        (appCcRS (I := I) (M := M) g 3 4 2
            (deTurckLieTraceCoeff (I := I) (M := M) g gU σ)
            (slotExtend (I := I) (M := M) g 2 3
              (slotExtend (I := I) (M := M) g 1 2 (ΨT - ΨU))) +
          appCcRS (I := I) (M := M) g 3 4 2
            (deTurckLieTraceCoeff (I := I) (M := M) g gT σ -
              deTurckLieTraceCoeff (I := I) (M := M) g gU σ)
            (slotExtend (I := I) (M := M) g 2 3
              (slotExtend (I := I) (M := M) g 1 2 ΨT))) ρ := by
  simp only [lieArm1Piece]
  rw [← reindex_sub (I := I) (M := M) g,
    slotExtend_sub, slotExtend_sub,
    appCcRS_sub_right, appCcRS_sub_left]
  congr 1
  module

set_option maxHeartbeats 800000 in
private theorem liePiece_pair
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (gT gU : SmoothRiemannianMetric I M)
        (σ : Equiv.Perm (Fin 4)) (ρ : Equiv.Perm (Fin 3))
        (ΨT ΨU : SmoothCcTensor g 1 2)
        (Tb Td Qt Qd : ℝ),
        0 ≤ Tb → 0 ≤ Td → 0 ≤ Qt → 0 ≤ Qd →
        lowJetSq (I := I) (M := M) g 2
            (deTurckLieTraceCoeff (I := I) (M := M) g gU σ) ≤
          Tb ^ 2 →
        lowJetSq (I := I) (M := M) g 2
            (deTurckLieTraceCoeff (I := I) (M := M) g gT σ -
              deTurckLieTraceCoeff (I := I) (M := M) g gU σ) ≤
          Td ^ 2 →
        lowJetSq (I := I) (M := M) g 2 ΨT ≤ Qt ^ 2 →
        lowJetSq (I := I) (M := M) g 2 (ΨT - ΨU) ≤ Qd ^ 2 →
      lowJetSq (I := I) (M := M) g 2
          (lieArm1Piece (I := I) (M := M) g gT σ ρ ΨT -
            lieArm1Piece (I := I) (M := M) g gU σ ρ ΨU) ≤
        (C * (Tb * Qd + Td * Qt)) ^ 2 := by
  obtain ⟨Ca, hCa, happ⟩ :=
    app_h2_mul (I := I) (M := M) hDim g 3 4 2
  let H : ℝ := Real.sqrt Ca
  let C : ℝ := 6 * H
  have hH : 0 ≤ H := Real.sqrt_nonneg _
  have hHsq : H ^ 2 = Ca := by
    simpa only [H] using Real.sq_sqrt hCa
  have hC : 0 ≤ C := mul_nonneg (by norm_num) hH
  refine ⟨C, hC, ?_⟩
  intro gT gU σ ρ ΨT ΨU Tb Td Qt Qd
    hTb hTd hQt hQd hTb2 hTd2 hQt2 hQd2
  let ST : SmoothCcTensor g 3 4 :=
    slotExtend (I := I) (M := M) g 2 3
      (slotExtend (I := I) (M := M) g 1 2 ΨT)
  let SD : SmoothCcTensor g 3 4 :=
    slotExtend (I := I) (M := M) g 2 3
      (slotExtend (I := I) (M := M) g 1 2 (ΨT - ΨU))
  let V1 : SmoothCcTensor g 3 2 :=
    appCcRS (I := I) (M := M) g 3 4 2
      (deTurckLieTraceCoeff (I := I) (M := M) g gU σ) SD
  let V2 : SmoothCcTensor g 3 2 :=
    appCcRS (I := I) (M := M) g 3 4 2
      (deTurckLieTraceCoeff (I := I) (M := M) g gT σ -
        deTurckLieTraceCoeff (I := I) (M := M) g gU σ) ST
  let Z1 : ℝ := H * Tb * (3 * Qd)
  let Z2 : ℝ := H * Td * (3 * Qt)
  have hSD :
      lowJetSq (I := I) (M := M) g 2 SD ≤ (3 * Qd) ^ 2 := by
    calc
      lowJetSq (I := I) (M := M) g 2 SD ≤
          9 * lowJetSq (I := I) (M := M) g 2 (ΨT - ΨU) :=
        slots_h2 (I := I) (M := M) hDim g _
      _ ≤ 9 * Qd ^ 2 :=
        mul_le_mul_of_nonneg_left hQd2 (by norm_num)
      _ = (3 * Qd) ^ 2 := by ring
  have hST :
      lowJetSq (I := I) (M := M) g 2 ST ≤ (3 * Qt) ^ 2 := by
    calc
      lowJetSq (I := I) (M := M) g 2 ST ≤
          9 * lowJetSq (I := I) (M := M) g 2 ΨT :=
        slots_h2 (I := I) (M := M) hDim g _
      _ ≤ 9 * Qt ^ 2 :=
        mul_le_mul_of_nonneg_left hQt2 (by norm_num)
      _ = (3 * Qt) ^ 2 := by ring
  have hZ1 : 0 ≤ Z1 :=
    mul_nonneg (mul_nonneg hH hTb)
      (mul_nonneg (by norm_num) hQd)
  have hZ2 : 0 ≤ Z2 :=
    mul_nonneg (mul_nonneg hH hTd)
      (mul_nonneg (by norm_num) hQt)
  have hV1 :
      lowJetSq (I := I) (M := M) g 2 V1 ≤ Z1 ^ 2 := by
    calc
      lowJetSq (I := I) (M := M) g 2 V1 ≤
          Ca * lowJetSq (I := I) (M := M) g 2
              (deTurckLieTraceCoeff (I := I) (M := M) g gU σ) *
            lowJetSq (I := I) (M := M) g 2 SD := by
        simpa only [V1] using happ
          (deTurckLieTraceCoeff (I := I) (M := M) g gU σ) SD
      _ ≤ Ca * Tb ^ 2 * (3 * Qd) ^ 2 := by
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left hTb2 hCa) hSD
          (jet_nonneg (I := I) (M := M) (m := 2) g SD)
          (mul_nonneg hCa (sq_nonneg Tb))
      _ = Z1 ^ 2 := by
        simp only [Z1]
        rw [← hHsq]
        ring
  have hV2 :
      lowJetSq (I := I) (M := M) g 2 V2 ≤ Z2 ^ 2 := by
    calc
      lowJetSq (I := I) (M := M) g 2 V2 ≤
          Ca * lowJetSq (I := I) (M := M) g 2
              (deTurckLieTraceCoeff (I := I) (M := M) g gT σ -
                deTurckLieTraceCoeff (I := I) (M := M) g gU σ) *
            lowJetSq (I := I) (M := M) g 2 ST := by
        simpa only [V2] using happ
          (deTurckLieTraceCoeff (I := I) (M := M) g gT σ -
            deTurckLieTraceCoeff (I := I) (M := M) g gU σ) ST
      _ ≤ Ca * Td ^ 2 * (3 * Qt) ^ 2 := by
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left hTd2 hCa) hST
          (jet_nonneg (I := I) (M := M) (m := 2) g ST)
          (mul_nonneg hCa (sq_nonneg Td))
      _ = Z2 ^ 2 := by
        simp only [Z2]
        rw [← hHsq]
        ring
  rw [liePiece_sub (I := I) (M := M) g gT gU σ ρ ΨT ΨU,
    reindex_h2_eq (I := I) (M := M)]
  change lowJetSq (I := I) (M := M) g 2 (V1 + V2) ≤ _
  calc
    lowJetSq (I := I) (M := M) g 2 (V1 + V2) ≤
        2 * (lowJetSq (I := I) (M := M) g 2 V1 +
          lowJetSq (I := I) (M := M) g 2 V2) :=
      jet_add1 (I := I) (M := M) g 2 V1 V2
    _ ≤ 2 * (Z1 ^ 2 + Z2 ^ 2) :=
      mul_le_mul_of_nonneg_left (add_le_add hV1 hV2) (by norm_num)
    _ ≤ (2 * (Z1 + Z2)) ^ 2 := by
      nlinarith [mul_nonneg hZ1 hZ2]
    _ = (C * (Tb * Qd + Td * Qt)) ^ 2 := by
      simp only [C, Z1, Z2]
      ring

private theorem connBg_eq
    (g gm : SmoothRiemannianMetric I M) :
    lieArm1ConnDiffBgCc (I := I) (M := M) g gm g =
      connDiffSection (I := I) gm g := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rfl

private noncomputable def psiLeft
    (g gm : SmoothRiemannianMetric I M) : SmoothCcTensor g 1 2 :=
  cometricRaiseSlot0Field (I := I) (M := M) g 1
    (domDomCongrSection (I := I) g lieArm1RhoSlot0
      (lieArm1LoweredBgKappa (I := I) (M := M) g gm g))

private theorem psi_eq
    (g gm : SmoothRiemannianMetric I M) :
    lieArm1PsiB (I := I) (M := M) g gm g =
      appCcRS (I := I) (M := M) g 1 1 2
        (psiLeft (I := I) (M := M) g gm)
        (sharpFlatEndoCc (I := I) g gm) := by
  rfl

private theorem psi_sub_eq
    (g gT gU : SmoothRiemannianMetric I M) :
    lieArm1PsiB (I := I) (M := M) g gT g -
        lieArm1PsiB (I := I) (M := M) g gU g =
      appCcRS (I := I) (M := M) g 1 1 2
          (psiLeft (I := I) (M := M) g gT)
          (sharpFlatEndoCc (I := I) g gT -
            sharpFlatEndoCc (I := I) g gU) +
        appCcRS (I := I) (M := M) g 1 1 2
          (psiLeft (I := I) (M := M) g gT -
            psiLeft (I := I) (M := M) g gU)
          (sharpFlatEndoCc (I := I) g gU) := by
  rw [psi_eq (I := I) (M := M) g gT,
    psi_eq (I := I) (M := M) g gU,
    appCcRS_sub_right, appCcRS_sub_left]
  module

private theorem perturb_h2_eq
    (g : SmoothRiemannianMetric I M) (D : SmoothCcTensor g 0 2)
    (hD : symmS (I := I) (M := M) g D = D) :
    lowJetSq (I := I) (M := M) g 2
        (perturb0 (I := I) (M := M) g D) =
      lowJetSq (I := I) (M := M) g 2 D := by
  rw [show perturb0 (I := I) (M := M) g D =
      cometricRaiseSlot0Field (I := I) (M := M) g 0
        (domDomCongrSection (I := I) g
          (Equiv.swap (0 : Fin 2) 1)
          (symmS (I := I) (M := M) g D)) by
    simpa only [perturb0] using
      insert_symmRaise_eq (I := I) (M := M) g D]
  calc
    lowJetSq (I := I) (M := M) g 2
        (cometricRaiseSlot0Field (I := I) (M := M) g 0
          (domDomCongrSection (I := I) g
            (Equiv.swap (0 : Fin 2) 1)
            (symmS (I := I) (M := M) g D))) =
      lowJetSq (I := I) (M := M) g 2
        (domDomCongrSection (I := I) g
          (Equiv.swap (0 : Fin 2) 1)
          (symmS (I := I) (M := M) g D)) := by
        unfold lowJetSq
        apply Finset.sum_congr rfl
        intro q _
        rw [norm_iCG_cometricRaiseSlot0Field_eq
          (I := I) (M := M) g 0
          (domDomCongrSection (I := I) g
            (Equiv.swap (0 : Fin 2) 1)
            (symmS (I := I) (M := M) g D)) q]
    _ = lowJetSq (I := I) (M := M) g 2
          (symmS (I := I) (M := M) g D) :=
      dom_h2 (I := I) (M := M) g
        (Equiv.swap (0 : Fin 2) 1)
        (symmS (I := I) (M := M) g D)
    _ = lowJetSq (I := I) (M := M) g 2 D := by rw [hD]

private theorem jet_neg1
    (g : SmoothRiemannianMetric I M) {r s : ℕ} (m : ℕ)
    (S : SmoothCcTensor g r s) :
    lowJetSq (I := I) (M := M) g m (-S) =
      lowJetSq (I := I) (M := M) g m S := by
  simpa only [neg_one_smul, neg_one_sq, one_mul] using
    jet_smul1 (I := I) (M := M) g m (-1 : ℝ) S

set_option maxHeartbeats 1200000 in
set_option linter.unusedVariables false in
private theorem sharp_pair_h2
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀0 : 0 ≤ δ₀) (hδ₀ : δ₀ < 1) :
    ∃ ρ C : ℝ, 0 < ρ ∧ 0 ≤ C ∧
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
          (ccTensorBilinSymm (I := I) g U) δU),
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ ≤ ρ →
      lowJetSq (I := I) (M := M) g 2
          (sharpFlatEndoCc (I := I) g gT -
            sharpFlatEndoCc (I := I) g gU) ≤
        (C * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
          (T - U)‖) ^ 2 := by
  obtain ⟨Ks, hKs, hsharp⟩ :=
    sharp_h2_low (I := I) (M := M) g hδ₀0 hδ₀
  obtain ⟨Ca, hCa, happ⟩ :=
    app_h2_mul (I := I) (M := M) hDim g 1 1 1
  obtain ⟨Ch, hCh, hhs⟩ :=
    hs2_low2 (I := I) (M := M) g 2
  let ρ : ℝ := 1
  let S0 : ℝ := Ks * (1 + Ch ^ 2)
  let C : ℝ := Ca * S0 * Ch
  have hρ : 0 < ρ := by norm_num [ρ]
  have hS0 : 0 ≤ S0 :=
    mul_nonneg hKs (add_nonneg (by norm_num) (sq_nonneg Ch))
  have hC : 0 ≤ C := mul_nonneg (mul_nonneg hCa hS0) hCh
  refine ⟨ρ, C, hρ, hC, ?_⟩
  intro gT gU T U hT hU hTtie hUtie
    δT δU hδT_le hδT0 hδT hδU_le hδU0 hδU hTHs hUHs
  let N : ℝ :=
    ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U)‖
  let X : SmoothCcTensor g 1 1 :=
    appCcRS (I := I) (M := M) g 1 1 1
      (perturb0 (I := I) (M := M) g (T - U))
      (sharpFlatEndoCc (I := I) g gT)
  let Y : SmoothCcTensor g 1 1 :=
    appCcRS (I := I) (M := M) g 1 1 1
      (sharpFlatEndoCc (I := I) g gU) X
  have hN : 0 ≤ N := norm_nonneg _
  have hT2 :
      lowJetSq (I := I) (M := M) g 2 T ≤ Ch ^ 2 := by
    calc
      lowJetSq (I := I) (M := M) g 2 T ≤
          (Ch * ‖ccTensorToHs (I := I) (M := M) g 2
            (2 : ℝ) T‖) ^ 2 := by
        simpa only [lowJetSq, Nat.reduceAdd] using hhs T
      _ ≤ (Ch * ρ) ^ 2 :=
        pow_le_pow_left₀
          (mul_nonneg hCh (norm_nonneg _))
          (mul_le_mul_of_nonneg_left hTHs hCh) 2
      _ = Ch ^ 2 := by simp only [ρ, mul_one]
  have hU2 :
      lowJetSq (I := I) (M := M) g 2 U ≤ Ch ^ 2 := by
    calc
      lowJetSq (I := I) (M := M) g 2 U ≤
          (Ch * ‖ccTensorToHs (I := I) (M := M) g 2
            (2 : ℝ) U‖) ^ 2 := by
        simpa only [lowJetSq, Nat.reduceAdd] using hhs U
      _ ≤ (Ch * ρ) ^ 2 :=
        pow_le_pow_left₀
          (mul_nonneg hCh (norm_nonneg _))
          (mul_le_mul_of_nonneg_left hUHs hCh) 2
      _ = Ch ^ 2 := by simp only [ρ, mul_one]
  have hST :
      lowJetSq (I := I) (M := M) g 2
          (sharpFlatEndoCc (I := I) g gT) ≤ S0 := by
    calc
      lowJetSq (I := I) (M := M) g 2
          (sharpFlatEndoCc (I := I) g gT) ≤
        Ks * (1 + lowJetSq (I := I) (M := M) g 2 T) :=
          hsharp gT T hT hTtie hδT_le hδT0 hδT
      _ ≤ S0 := by
        dsimp only [S0]
        exact mul_le_mul_of_nonneg_left (add_le_add le_rfl hT2) hKs
  have hSU :
      lowJetSq (I := I) (M := M) g 2
          (sharpFlatEndoCc (I := I) g gU) ≤ S0 := by
    calc
      lowJetSq (I := I) (M := M) g 2
          (sharpFlatEndoCc (I := I) g gU) ≤
        Ks * (1 + lowJetSq (I := I) (M := M) g 2 U) :=
          hsharp gU U hU hUtie hδU_le hδU0 hδU
      _ ≤ S0 := by
        dsimp only [S0]
        exact mul_le_mul_of_nonneg_left (add_le_add le_rfl hU2) hKs
  have hDsymm :
      symmS (I := I) (M := M) g (T - U) = T - U := by
    rw [symmS_sub, symm_eq_self (I := I) (M := M) g T hT,
      symm_eq_self (I := I) (M := M) g U hU]
  have hD2 :
      lowJetSq (I := I) (M := M) g 2 (T - U) ≤
        (Ch * N) ^ 2 := by
    simpa only [lowJetSq, Nat.reduceAdd, N] using hhs (T - U)
  have hP :
      lowJetSq (I := I) (M := M) g 2
          (perturb0 (I := I) (M := M) g (T - U)) ≤
        (Ch * N) ^ 2 := by
    rw [perturb_h2_eq (I := I) (M := M) g (T - U) hDsymm]
    exact hD2
  have hX :
      lowJetSq (I := I) (M := M) g 2 X ≤
        Ca * (Ch * N) ^ 2 * S0 := by
    calc
      lowJetSq (I := I) (M := M) g 2 X ≤
          Ca * lowJetSq (I := I) (M := M) g 2
              (perturb0 (I := I) (M := M) g (T - U)) *
            lowJetSq (I := I) (M := M) g 2
              (sharpFlatEndoCc (I := I) g gT) := by
        simpa only [X] using happ
          (perturb0 (I := I) (M := M) g (T - U))
          (sharpFlatEndoCc (I := I) g gT)
      _ ≤ Ca * (Ch * N) ^ 2 * S0 := by
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left hP hCa) hST
          (jet_nonneg (I := I) (M := M) (m := 2) g
            (sharpFlatEndoCc (I := I) g gT))
          (mul_nonneg hCa (sq_nonneg (Ch * N)))
  have hY :
      lowJetSq (I := I) (M := M) g 2 Y ≤ (C * N) ^ 2 := by
    calc
      lowJetSq (I := I) (M := M) g 2 Y ≤
          Ca * lowJetSq (I := I) (M := M) g 2
              (sharpFlatEndoCc (I := I) g gU) *
            lowJetSq (I := I) (M := M) g 2 X := by
        simpa only [Y] using happ
          (sharpFlatEndoCc (I := I) g gU) X
      _ ≤ Ca * S0 * (Ca * (Ch * N) ^ 2 * S0) := by
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left hSU hCa) hX
          (jet_nonneg (I := I) (M := M) (m := 2) g X)
          (mul_nonneg hCa hS0)
      _ = (C * N) ^ 2 := by
        simp only [C]
        ring
  rw [sharp_pair (I := I) (M := M) g gT gU T U hTtie hUtie,
    jet_neg1 (I := I) (M := M) g 2]
  exact hY

private theorem corr_tel
    (g gT gU : SmoothRiemannianMetric I M)
    (T U : SmoothCcTensor g 0 2) :
    metricLowerCorr (I := I) (M := M) g gT g T -
        metricLowerCorr (I := I) (M := M) g gU g U =
      metricLowerCorr (I := I) (M := M) g gT g (T - U) +
        (metricLowerCorr (I := I) (M := M) g gT g U -
          metricLowerCorr (I := I) (M := M) g gU g U) := by
  rw [metricCorr_sub (I := I) (M := M) g gT g T U]
  abel

set_option maxHeartbeats 1200000 in
private theorem corr_pair_h2
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (gT gU : SmoothRiemannianMetric I M)
        (T U : SmoothCcTensor g 0 2),
      lowJetSq (I := I) (M := M) g 2
          (metricLowerCorr (I := I) (M := M) g gT g T -
            metricLowerCorr (I := I) (M := M) g gU g U) ≤
        C *
          (lowJetSq (I := I) (M := M) g 2 (T - U) *
              lowJetSq (I := I) (M := M) g 2
                (wXi (I := I) (M := M) g gT g) +
            lowJetSq (I := I) (M := M) g 2 U *
              lowJetSq (I := I) (M := M) g 2
                (wXi (I := I) (M := M) g gT g -
                  wXi (I := I) (M := M) g gU g)) := by
  obtain ⟨C0, hC0, hmul⟩ :=
    metricCorr_h2_mul (I := I) (M := M) hDim g
  obtain ⟨C1, hC1, hmove⟩ :=
    metricCorr_move (I := I) (M := M) hDim g
  let C : ℝ := 2 * max C0 C1
  have hCmax : 0 ≤ max C0 C1 := hC0.trans (le_max_left C0 C1)
  have hC : 0 ≤ C := mul_nonneg (by norm_num) hCmax
  refine ⟨C, hC, ?_⟩
  intro gT gU T U
  let X : SmoothCcTensor g 0 3 :=
    metricLowerCorr (I := I) (M := M) g gT g (T - U)
  let Y : SmoothCcTensor g 0 3 :=
    metricLowerCorr (I := I) (M := M) g gT g U -
      metricLowerCorr (I := I) (M := M) g gU g U
  let A : ℝ :=
    lowJetSq (I := I) (M := M) g 2 (T - U) *
      lowJetSq (I := I) (M := M) g 2
        (wXi (I := I) (M := M) g gT g)
  let B : ℝ :=
    lowJetSq (I := I) (M := M) g 2 U *
      lowJetSq (I := I) (M := M) g 2
        (wXi (I := I) (M := M) g gT g -
          wXi (I := I) (M := M) g gU g)
  have hA : 0 ≤ A := mul_nonneg
    (jet_nonneg (I := I) (M := M) g (T - U))
    (jet_nonneg (I := I) (M := M) g
      (wXi (I := I) (M := M) g gT g))
  have hB : 0 ≤ B := mul_nonneg
    (jet_nonneg (I := I) (M := M) g U)
    (jet_nonneg (I := I) (M := M) g
      (wXi (I := I) (M := M) g gT g -
        wXi (I := I) (M := M) g gU g))
  have hX :
      lowJetSq (I := I) (M := M) g 2 X ≤ C0 * A := by
    simpa only [lowJetSq, Nat.reduceAdd, X, A, mul_assoc] using
      hmul gT g (T - U)
  have hY :
      lowJetSq (I := I) (M := M) g 2 Y ≤ C1 * B := by
    simpa only [lowJetSq, Nat.reduceAdd, Y, B, mul_assoc] using
      hmove gT gU g U
  rw [corr_tel (I := I) (M := M) g gT gU T U]
  calc
    lowJetSq (I := I) (M := M) g 2 (X + Y) ≤
        2 * (lowJetSq (I := I) (M := M) g 2 X +
          lowJetSq (I := I) (M := M) g 2 Y) :=
      jet_add1 (I := I) (M := M) g 2 X Y
    _ ≤ 2 * (C0 * A + C1 * B) :=
      mul_le_mul_of_nonneg_left (add_le_add hX hY) (by norm_num)
    _ ≤ 2 * (max C0 C1 * A + max C0 C1 * B) := by
      exact mul_le_mul_of_nonneg_left
        (add_le_add
          (mul_le_mul_of_nonneg_right (le_max_left C0 C1) hA)
          (mul_le_mul_of_nonneg_right (le_max_right C0 C1) hB))
        (by norm_num)
    _ = (2 * max C0 C1) * (A + B) := by ring
    _ = C * (A + B) := rfl

private theorem corr_h1_mul
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (gm g_bg : SmoothRiemannianMetric I M)
        (P : SmoothCcTensor g 0 2),
        lowJetSq (I := I) (M := M) g 1
            (metricLowerCorr (I := I) (M := M) g gm g_bg P) ≤
          C * lowJetSq (I := I) (M := M) g 2 P *
            lowJetSq (I := I) (M := M) g 1
              (wXi (I := I) (M := M) g gm g_bg) := by
  obtain ⟨Cφ, hCφ, hφ⟩ :=
    corrPhi_h2 (I := I) (M := M) hDim g
  obtain ⟨Ca, hCa, happ⟩ :=
    app_h21_mul (I := I) (M := M) hDim g 0 3 3
  let C : ℝ := Ca * Cφ
  have hC : 0 ≤ C := mul_nonneg hCa hCφ
  refine ⟨C, hC, ?_⟩
  intro gm g_bg P
  let W : SmoothCcTensor g 0 3 :=
    wXi (I := I) (M := M) g gm g_bg
  let ΦA : SmoothCcTensor g 3 3 :=
    corrPhi (I := I) (M := M) g P corrPermA
  let ΦB : SmoothCcTensor g 3 3 :=
    corrPhi (I := I) (M := M) g P corrPermB
  let UA : SmoothCcTensor g 0 3 :=
    appCc (I := I) (M := M) g 3 3 ΦA W
  let UB : SmoothCcTensor g 0 3 :=
    appCc (I := I) (M := M) g 3 3 ΦB W
  let JP : ℝ := lowJetSq (I := I) (M := M) g 2 P
  let JW : ℝ := lowJetSq (I := I) (M := M) g 1 W
  have hJP : 0 ≤ JP := jet_nonneg (I := I) (M := M) g P
  have hJW : 0 ≤ JW := jet_nonneg (I := I) (M := M) g W
  have hA :
      lowJetSq (I := I) (M := M) g 1 UA ≤ C * JP * JW := by
    calc
      lowJetSq (I := I) (M := M) g 1 UA ≤
          Ca * lowJetSq (I := I) (M := M) g 2 ΦA * JW := by
        simpa only [UA, ΦA, W, JW, appCcRS_zero_eq_appCc] using
          happ ΦA W
      _ ≤ Ca * (Cφ * JP) * JW := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left
            (by simpa only [ΦA, JP] using hφ P corrPermA) hCa)
          hJW
      _ = C * JP * JW := by
        simp only [C]
        ring
  have hB :
      lowJetSq (I := I) (M := M) g 1 UB ≤ C * JP * JW := by
    calc
      lowJetSq (I := I) (M := M) g 1 UB ≤
          Ca * lowJetSq (I := I) (M := M) g 2 ΦB * JW := by
        simpa only [UB, ΦB, W, JW, appCcRS_zero_eq_appCc] using
          happ ΦB W
      _ ≤ Ca * (Cφ * JP) * JW := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left
            (by simpa only [ΦB, JP] using hφ P corrPermB) hCa)
          hJW
      _ = C * JP * JW := by
        simp only [C]
        ring
  have hadd := jet_add1 (I := I) (M := M) g 1
    ((1 / 2 : ℝ) • UA) ((1 / 2 : ℝ) • UB)
  rw [jet_smul1, jet_smul1] at hadd
  rw [corr_formula (I := I) (M := M) g gm g_bg P]
  change lowJetSq (I := I) (M := M) g 1
      ((1 / 2 : ℝ) • UA + (1 / 2 : ℝ) • UB) ≤ C * JP * JW
  calc
    lowJetSq (I := I) (M := M) g 1
        ((1 / 2 : ℝ) • UA + (1 / 2 : ℝ) • UB) ≤
      2 * (((1 / 2 : ℝ) ^ 2 *
          lowJetSq (I := I) (M := M) g 1 UA) +
        (1 / 2 : ℝ) ^ 2 *
          lowJetSq (I := I) (M := M) g 1 UB) := hadd
    _ ≤ C * JP * JW := by
      nlinarith

set_option linter.unusedVariables false in
/-- The moving-lowering correction is Lipschitz at the low endpoint with an
`H²` coefficient slot and an `H¹` connection slot. -/
theorem metricCorr_pair_h1
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (gT gU : SmoothRiemannianMetric I M)
        (T U : SmoothCcTensor g 0 2),
      lowJetSq (I := I) (M := M) g 1
          (metricLowerCorr (I := I) (M := M) g gT g T -
            metricLowerCorr (I := I) (M := M) g gU g U) ≤
        C *
          (lowJetSq (I := I) (M := M) g 2 (T - U) *
              lowJetSq (I := I) (M := M) g 1
                (wXi (I := I) (M := M) g gT g) +
            lowJetSq (I := I) (M := M) g 2 U *
              lowJetSq (I := I) (M := M) g 1
                (wXi (I := I) (M := M) g gT g -
                  wXi (I := I) (M := M) g gU g)) := by
  obtain ⟨C0, hC0, hmul⟩ :=
    corr_h1_mul (I := I) (M := M) hDim g
  let C : ℝ := 2 * C0
  have hC : 0 ≤ C := mul_nonneg (by norm_num) hC0
  refine ⟨C, hC, ?_⟩
  intro gT gU T U
  let WT : SmoothCcTensor g 0 3 :=
    wXi (I := I) (M := M) g gT g
  let WU : SmoothCcTensor g 0 3 :=
    wXi (I := I) (M := M) g gU g
  let X : SmoothCcTensor g 0 3 :=
    metricLowerCorr (I := I) (M := M) g gT g (T - U)
  let Y : SmoothCcTensor g 0 3 :=
    metricLowerCorr (I := I) (M := M) g gT g U -
      metricLowerCorr (I := I) (M := M) g gU g U
  let A : ℝ :=
    lowJetSq (I := I) (M := M) g 2 (T - U) *
      lowJetSq (I := I) (M := M) g 1 WT
  let B : ℝ :=
    lowJetSq (I := I) (M := M) g 2 U *
      lowJetSq (I := I) (M := M) g 1 (WT - WU)
  have hA : 0 ≤ A := mul_nonneg
    (jet_nonneg (I := I) (M := M) g (T - U))
    (jet_nonneg (I := I) (M := M) g WT)
  have hB : 0 ≤ B := mul_nonneg
    (jet_nonneg (I := I) (M := M) g U)
    (jet_nonneg (I := I) (M := M) g (WT - WU))
  have hX :
      lowJetSq (I := I) (M := M) g 1 X ≤ C0 * A := by
    simpa only [X, A, WT, mul_assoc] using hmul gT g (T - U)
  have hWcross :
      wXi (I := I) (M := M) g gU gT = -(WT - WU) := by
    simp only [WT, WU, wXi]
    module
  have hY :
      lowJetSq (I := I) (M := M) g 1 Y ≤ C0 * B := by
    change lowJetSq (I := I) (M := M) g 1
      (metricLowerCorr (I := I) (M := M) g gT g U -
        metricLowerCorr (I := I) (M := M) g gU g U) ≤ C0 * B
    rw [corr_cross (I := I) (M := M) g gT gU U,
      jet_neg1 (I := I) (M := M) g 1]
    have hraw := hmul gU gT U
    rw [hWcross, jet_neg1 (I := I) (M := M) g 1] at hraw
    simpa only [B, WT, WU, mul_assoc] using hraw
  rw [corr_tel (I := I) (M := M) g gT gU T U]
  change lowJetSq (I := I) (M := M) g 1 (X + Y) ≤ C * (A + B)
  calc
    lowJetSq (I := I) (M := M) g 1 (X + Y) ≤
        2 * (lowJetSq (I := I) (M := M) g 1 X +
          lowJetSq (I := I) (M := M) g 1 Y) :=
      jet_add1 (I := I) (M := M) g 1 X Y
    _ ≤ 2 * (C0 * A + C0 * B) :=
      mul_le_mul_of_nonneg_left (add_le_add hX hY) (by norm_num)
    _ = C * (A + B) := by
      simp only [C]
      ring

private theorem mcd_sub_eq
    (g gT gU : SmoothRiemannianMetric I M)
    (T U : SmoothCcTensor g 0 2)
    (hTtie : ∀ (x : M) (u v : TangentSpace I x),
      gT.inner x u v =
        g.inner x u v + ccTensorBilinSymm (I := I) g T x u v)
    (hUtie : ∀ (x : M) (u v : TangentSpace I x),
      gU.inner x u v =
        g.inner x u v + ccTensorBilinSymm (I := I) g U x u v) :
    metricConnDiffLoweredCc (I := I) (M := M) g gT g -
        metricConnDiffLoweredCc (I := I) (M := M) g gU g =
      (wXi (I := I) (M := M) g gT g -
        wXi (I := I) (M := M) g gU g) +
      (metricLowerCorr (I := I) (M := M) g gT g T -
        metricLowerCorr (I := I) (M := M) g gU g U) := by
  rw [mcd_lower_split (I := I) (M := M) g gT g T hTtie,
    mcd_lower_split (I := I) (M := M) g gU g U hUtie]
  module

namespace LowBaseInternal

private theorem fullRev_sub
    (g gT gU : SmoothRiemannianMetric I M)
    (T U : SmoothCcTensor g 0 2)
    (hTtie : ∀ (x : M) (u v : TangentSpace I x),
      gT.inner x u v =
        g.inner x u v + ccTensorBilinSymm (I := I) g T x u v)
    (hUtie : ∀ (x : M) (u v : TangentSpace I x),
      gU.inner x u v =
        g.inner x u v + ccTensorBilinSymm (I := I) g U x u v) :
    fullRaisedEndoField (I := I) (M := M) gT g -
        fullRaisedEndoField (I := I) (M := M) gU g =
      symmRaiseEndo (I := I) (M := M) g (T - U) := by
  have hsub :
      symmRaiseEndo (I := I) (M := M) g (T - U) =
        symmRaiseEndo (I := I) (M := M) g T -
          symmRaiseEndo (I := I) (M := M) g U := by
    calc
      symmRaiseEndo (I := I) (M := M) g (T - U) =
          symmRaiseEndo (I := I) (M := M) g
            (T + (-1 : ℝ) • U) := by
              rw [neg_one_smul, sub_eq_add_neg]
      _ = symmRaiseEndo (I := I) (M := M) g T +
            symmRaiseEndo (I := I) (M := M) g
              ((-1 : ℝ) • U) := by
                rw [symmRaiseEndo_add]
      _ = symmRaiseEndo (I := I) (M := M) g T +
            (-1 : ℝ) •
              symmRaiseEndo (I := I) (M := M) g U := by
                rw [symmRaiseEndo_smul]
      _ = symmRaiseEndo (I := I) (M := M) g T -
            symmRaiseEndo (I := I) (M := M) g U := by
              module
  have hdec (gm : SmoothRiemannianMetric I M) :
      fullRaisedEndoField (I := I) (M := M) gm g =
        gInvDiffRaisedEndoField (I := I) gm g +
          fullRaisedEndoField (I := I) (M := M) g g := by
    apply ContMDiffSection.ext
    intro x
    rw [show ((gInvDiffRaisedEndoField (I := I) gm g +
          fullRaisedEndoField (I := I) (M := M) g g) x) =
        gInvDiffRaisedEndoField (I := I) gm g x +
          fullRaisedEndoField (I := I) (M := M) g g x from by
      rw [ContMDiffSection.coe_add]
      rfl]
    apply ContinuousLinearMap.ext
    intro v
    rw [fullRaisedEndoField_apply, ContinuousLinearMap.add_apply]
    rw [show gInvDiffRaisedEndoField (I := I) gm g x =
        gInvDiffRaisedEndo (I := I) gm g x from rfl]
    have hself :
        gInvRaisedEndo (I := I) g g x =
          ContinuousLinearMap.id ℝ (TangentSpace I x) := by
      apply ContinuousLinearMap.ext
      intro w
      rw [gInvRaisedEndo_apply, inverseMetricSharpFib_g0FlatCLM,
        ContinuousLinearMap.id_apply]
    rw [fullRaisedEndoField_apply, hself,
      ContinuousLinearMap.id_apply, gInvRaisedEndo_eq_diff_add_id]
  rw [hdec gT, hdec gU,
    ← raise_rev (I := I) (M := M) g gT T hTtie,
    ← raise_rev (I := I) (M := M) g gU U hUtie, hsub]
  module

/-- The reverse raised-endomorphism factor is exactly linear in a tied
metric perturbation difference at fixed covariant background. -/
theorem revSlot_pair_h2
    (g gT gU : SmoothRiemannianMetric I M)
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
        g.inner x u v + ccTensorBilinSymm (I := I) g U x u v) :
    lowJetSq (I := I) (M := M) g 2
        (slotInsertEndoCc (I := I) (M := M) g 2
            (fullRaisedEndoField (I := I) (M := M) gT g) -
          slotInsertEndoCc (I := I) (M := M) g 2
            (fullRaisedEndoField (I := I) (M := M) gU g)) ≤
      (Module.finrank ℝ E : ℝ) ^ 2 *
        lowJetSq (I := I) (M := M) g 2 (T - U) := by
  have hsymm :
      symmS (I := I) (M := M) g (T - U) = T - U := by
    rw [symmS_sub, symm_eq_self (I := I) (M := M) g T hT,
      symm_eq_self (I := I) (M := M) g U hU]
  rw [← slotInsertEndoCc_sub,
    fullRev_sub (I := I) (M := M) g gT gU T U hTtie hUtie]
  calc
    lowJetSq (I := I) (M := M) g 2
        (slotInsertEndoCc (I := I) (M := M) g 2
          (symmRaiseEndo (I := I) (M := M) g (T - U))) ≤
      (Module.finrank ℝ E : ℝ) ^ 2 *
        lowJetSq (I := I) (M := M) g 2
          (slotInsertEndoCc (I := I) (M := M) g 0
            (symmRaiseEndo (I := I) (M := M) g (T - U))) :=
      endo_slot_h2 (I := I) (M := M) g 2
        (symmRaiseEndo (I := I) (M := M) g (T - U))
    _ = (Module.finrank ℝ E : ℝ) ^ 2 *
        lowJetSq (I := I) (M := M) g 2 (T - U) := by
      rw [show
        slotInsertEndoCc (I := I) (M := M) g 0
            (symmRaiseEndo (I := I) (M := M) g (T - U)) =
          perturb0 (I := I) (M := M) g (T - U) from rfl,
        perturb_h2_eq (I := I) (M := M) g (T - U) hsymm]

set_option linter.unusedVariables false in
/-- A reverse raised-endomorphism factor tied to an `H²` perturbation has a
fixed-order `H²` bound depending only on that low radius. -/
theorem revSlot_bdd_h2
    (g : SmoothRiemannianMetric I M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (gm : SmoothRiemannianMetric I M)
        (P : SmoothCcTensor g 0 2)
        (hP : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g P x u v =
            ccTensorBilin (I := I) g P x v u)
        (htie : ∀ (x : M) (u v : TangentSpace I x),
          gm.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g P x u v)
        (R : ℝ), 0 ≤ R →
        lowJetSq (I := I) (M := M) g 2 P ≤ R ^ 2 →
      lowJetSq (I := I) (M := M) g 2
          (slotInsertEndoCc (I := I) (M := M) g 2
            (fullRaisedEndoField (I := I) (M := M) gm g)) ≤
        (C * (1 + R)) ^ 2 := by
  let A0 : SmoothCcTensor g 3 3 :=
    slotInsertEndoCc (I := I) (M := M) g 2
      (fullRaisedEndoField (I := I) (M := M) g g)
  let J0 : ℝ := lowJetSq (I := I) (M := M) g 2 A0
  let fr : ℝ := Module.finrank ℝ E
  let Z : ℝ := 2 * (fr ^ 2 + J0)
  let C : ℝ := Real.sqrt Z
  have hJ0 : 0 ≤ J0 :=
    jet_nonneg (I := I) (M := M) g A0
  have hZ : 0 ≤ Z :=
    mul_nonneg (by norm_num)
      (add_nonneg (sq_nonneg fr) hJ0)
  refine ⟨C, Real.sqrt_nonneg _, ?_⟩
  intro gm P hP htie R hR hP2
  have hzero :
      ∀ (x : M) (u v : TangentSpace I x),
        ccTensorBilin (I := I) g
            (0 : SmoothCcTensor g 0 2) x u v =
          ccTensorBilin (I := I) g
            (0 : SmoothCcTensor g 0 2) x v u := by
    intro x u v
    rw [ccTensorBilin_zero_weight, ccTensorBilin_zero_weight]
  have hzeroTie :
      ∀ (x : M) (u v : TangentSpace I x),
        g.inner x u v =
          g.inner x u v +
            ccTensorBilinSymm (I := I) g
              (0 : SmoothCcTensor g 0 2) x u v := by
    intro x u v
    rw [ccTensorBilinSymm_apply, ccTensorBilin_zero_weight,
      ccTensorBilin_zero_weight]
    ring
  let A : SmoothCcTensor g 3 3 :=
    slotInsertEndoCc (I := I) (M := M) g 2
      (fullRaisedEndoField (I := I) (M := M) gm g)
  have hpair :
      lowJetSq (I := I) (M := M) g 2 (A - A0) ≤
        fr ^ 2 * lowJetSq (I := I) (M := M) g 2 P := by
    simpa only [A, A0, fr, sub_zero] using
      revSlot_pair_h2 (I := I) (M := M)
        g gm g P (0 : SmoothCcTensor g 0 2)
        hP hzero htie hzeroTie
  have hpairR :
      lowJetSq (I := I) (M := M) g 2 (A - A0) ≤
        fr ^ 2 * R ^ 2 :=
    hpair.trans (mul_le_mul_of_nonneg_left hP2 (sq_nonneg fr))
  have hRdom : R ^ 2 ≤ (1 + R) ^ 2 := by
    nlinarith
  have hone : (1 : ℝ) ≤ (1 + R) ^ 2 := by
    nlinarith [sq_nonneg R]
  have hdom :
      2 * (fr ^ 2 * R ^ 2 + J0) ≤ Z * (1 + R) ^ 2 := by
    calc
      2 * (fr ^ 2 * R ^ 2 + J0) ≤
          2 * (fr ^ 2 * (1 + R) ^ 2 +
            J0 * (1 + R) ^ 2) :=
        mul_le_mul_of_nonneg_left
          (add_le_add
            (mul_le_mul_of_nonneg_left hRdom (sq_nonneg fr))
            (by simpa only [mul_one] using
              mul_le_mul_of_nonneg_left hone hJ0))
          (by norm_num)
      _ = Z * (1 + R) ^ 2 := by
        simp only [Z]
        ring
  have hCsq : C ^ 2 = Z := by
    simpa only [C] using Real.sq_sqrt hZ
  have hAeq : A = (A - A0) + A0 := by module
  change lowJetSq (I := I) (M := M) g 2 A ≤
    (C * (1 + R)) ^ 2
  rw [hAeq]
  calc
    lowJetSq (I := I) (M := M) g 2 ((A - A0) + A0) ≤
        2 * (lowJetSq (I := I) (M := M) g 2 (A - A0) +
          lowJetSq (I := I) (M := M) g 2 A0) :=
      jet_add1 (I := I) (M := M) g 2 (A - A0) A0
    _ ≤ 2 * (fr ^ 2 * R ^ 2 + J0) :=
      mul_le_mul_of_nonneg_left
        (add_le_add hpairR le_rfl) (by norm_num)
    _ ≤ Z * (1 + R) ^ 2 := hdom
    _ = (C * (1 + R)) ^ 2 := by
      rw [mul_pow, hCsq]

set_option maxHeartbeats 1800000 in
set_option linter.unusedVariables false in
theorem mcd_pair_h2
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
        (R A D2 D3 : ℝ),
        0 ≤ R → 0 ≤ A → 0 ≤ D2 → 0 ≤ D3 →
        lowJetSq (I := I) (M := M) g 2 U ≤ R ^ 2 →
        lowJetSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
        lowJetSq (I := I) (M := M) g 2 (T - U) ≤ D2 ^ 2 →
        lowJetSq (I := I) (M := M) g 3 (T - U) ≤ D3 ^ 2 →
      lowJetSq (I := I) (M := M) g 2
          (metricConnDiffLoweredCc (I := I) (M := M) g gT g -
            metricConnDiffLoweredCc (I := I) (M := M) g gU g) ≤
        (B0 R * D3 + B1 R * D2 + B1 R * A * D2) ^ 2 := by
  obtain ⟨W0, W1, hW0, hW1, hw⟩ :=
    wXi_sub_tame (I := I) (M := M) hDim g hδ₀0 hδ₀
  obtain ⟨Kw, hKw, hwT⟩ :=
    wXi_h2_low (I := I) (M := M) g hδ₀0 hδ₀
  obtain ⟨Cc, hCc, hcorr⟩ :=
    corr_pair_h2 (I := I) (M := M) hDim g
  let H : ℝ := Real.sqrt Cc
  let Hw : ℝ := Real.sqrt Kw
  let B0 : ℝ → ℝ := fun R =>
    2 * (W0 R + H * R * W0 R)
  let B1 : ℝ → ℝ := fun R =>
    2 * (W1 R + H * (Hw + R * W1 R))
  have hH : 0 ≤ H := Real.sqrt_nonneg _
  have hHw : 0 ≤ Hw := Real.sqrt_nonneg _
  have hHsq : H ^ 2 = Cc := by
    simpa only [H] using Real.sq_sqrt hCc
  have hHwsq : Hw ^ 2 = Kw := by
    simpa only [Hw] using Real.sq_sqrt hKw
  refine ⟨B0, B1, ?_, ?_, ?_⟩
  · intro R hR
    exact mul_nonneg (by norm_num)
      (add_nonneg (hW0 R hR)
        (mul_nonneg (mul_nonneg hH hR) (hW0 R hR)))
  · intro R hR
    exact mul_nonneg (by norm_num)
      (add_nonneg (hW1 R hR)
        (mul_nonneg hH
          (add_nonneg hHw (mul_nonneg hR (hW1 R hR)))))
  intro gT gU T U hT hU hTtie hUtie
    δT δU hδT_le hδT0 hδT hδU_le hδU0 hδU
    R A D2 D3 hR hA hD2 hD3 hU2 hT3 hTU2 hTU3
  let WD : SmoothCcTensor g 0 3 :=
    wXi (I := I) (M := M) g gT g -
      wXi (I := I) (M := M) g gU g
  let CD : SmoothCcTensor g 0 3 :=
    metricLowerCorr (I := I) (M := M) g gT g T -
      metricLowerCorr (I := I) (M := M) g gU g U
  let X : ℝ := W0 R * D3 + W1 R * D2 + W1 R * A * D2
  let S : ℝ := Hw * (D2 + A * D2)
  let Y : ℝ := R * X
  let Z : ℝ := H * S + H * Y
  have hX : 0 ≤ X :=
    add_nonneg
      (add_nonneg (mul_nonneg (hW0 R hR) hD3)
        (mul_nonneg (hW1 R hR) hD2))
      (mul_nonneg (mul_nonneg (hW1 R hR) hA) hD2)
  have hS : 0 ≤ S :=
    mul_nonneg hHw
      (add_nonneg hD2 (mul_nonneg hA hD2))
  have hY : 0 ≤ Y := mul_nonneg hR hX
  have hZ : 0 ≤ Z :=
    add_nonneg (mul_nonneg hH hS) (mul_nonneg hH hY)
  have hWD :
      lowJetSq (I := I) (M := M) g 2 WD ≤ X ^ 2 := by
    simpa only [WD, X] using
      hw gT gU g T U hT hU hTtie hUtie
        hδT_le hδT0 hδT hδU_le hδU0 hδU
        R A D2 D3 hR hA hD2 hD3 hU2 hT3 hTU2 hTU3
  have hWT :
      lowJetSq (I := I) (M := M) g 2
          (wXi (I := I) (M := M) g gT g) ≤
        Kw * (1 + A ^ 2) := by
    exact (hwT gT T hT hTtie hδT_le hδT0 hδT).trans
      (mul_le_mul_of_nonneg_left (add_le_add le_rfl hT3) hKw)
  have hfirst :
      lowJetSq (I := I) (M := M) g 2 (T - U) *
          lowJetSq (I := I) (M := M) g 2
            (wXi (I := I) (M := M) g gT g) ≤
        S ^ 2 := by
    have hscalar :
        (1 + A ^ 2) * D2 ^ 2 ≤ (D2 + A * D2) ^ 2 := by
      nlinarith [mul_nonneg hA (sq_nonneg D2)]
    calc
      lowJetSq (I := I) (M := M) g 2 (T - U) *
          lowJetSq (I := I) (M := M) g 2
            (wXi (I := I) (M := M) g gT g) ≤
        D2 ^ 2 * (Kw * (1 + A ^ 2)) :=
          mul_le_mul hTU2 hWT
            (jet_nonneg (I := I) (M := M) g
              (wXi (I := I) (M := M) g gT g))
            (sq_nonneg D2)
      _ = Hw ^ 2 * ((1 + A ^ 2) * D2 ^ 2) := by
        rw [hHwsq]
        ring
      _ ≤ Hw ^ 2 * (D2 + A * D2) ^ 2 :=
        mul_le_mul_of_nonneg_left hscalar (sq_nonneg Hw)
      _ = S ^ 2 := by
        simp only [S]
        ring
  have hsecond :
      lowJetSq (I := I) (M := M) g 2 U *
          lowJetSq (I := I) (M := M) g 2 WD ≤ Y ^ 2 := by
    calc
      lowJetSq (I := I) (M := M) g 2 U *
          lowJetSq (I := I) (M := M) g 2 WD ≤
        R ^ 2 * X ^ 2 :=
          mul_le_mul hU2 hWD
            (jet_nonneg (I := I) (M := M) g WD)
            (sq_nonneg R)
      _ = Y ^ 2 := by
        simp only [Y]
        ring
  have hCD :
      lowJetSq (I := I) (M := M) g 2 CD ≤ Z ^ 2 := by
    have hraw := hcorr gT gU T U
    change lowJetSq (I := I) (M := M) g 2 CD ≤
      Cc * (lowJetSq (I := I) (M := M) g 2 (T - U) *
          lowJetSq (I := I) (M := M) g 2
            (wXi (I := I) (M := M) g gT g) +
        lowJetSq (I := I) (M := M) g 2 U *
          lowJetSq (I := I) (M := M) g 2 WD) at hraw
    calc
      lowJetSq (I := I) (M := M) g 2 CD ≤
          Cc * (lowJetSq (I := I) (M := M) g 2 (T - U) *
              lowJetSq (I := I) (M := M) g 2
                (wXi (I := I) (M := M) g gT g) +
            lowJetSq (I := I) (M := M) g 2 U *
              lowJetSq (I := I) (M := M) g 2 WD) := hraw
      _ ≤ Cc * (S ^ 2 + Y ^ 2) :=
        mul_le_mul_of_nonneg_left (add_le_add hfirst hsecond) hCc
      _ = (H * S) ^ 2 + (H * Y) ^ 2 := by
        rw [← hHsq]
        ring
      _ ≤ Z ^ 2 := by
        dsimp only [Z]
        nlinarith [mul_nonneg (mul_nonneg hH hS) (mul_nonneg hH hY)]
  rw [mcd_sub_eq (I := I) (M := M) g gT gU T U hTtie hUtie]
  change lowJetSq (I := I) (M := M) g 2 (WD + CD) ≤ _
  calc
    lowJetSq (I := I) (M := M) g 2 (WD + CD) ≤
        2 * (lowJetSq (I := I) (M := M) g 2 WD +
          lowJetSq (I := I) (M := M) g 2 CD) :=
      jet_add1 (I := I) (M := M) g 2 WD CD
    _ ≤ 2 * (X ^ 2 + Z ^ 2) :=
      mul_le_mul_of_nonneg_left (add_le_add hWD hCD) (by norm_num)
    _ ≤ (2 * (X + Z)) ^ 2 := by
      nlinarith [mul_nonneg hX hZ]
    _ = (B0 R * D3 + B1 R * D2 + B1 R * A * D2) ^ 2 := by
      simp only [B0, B1, Z, S, Y, X]
      ring

set_option maxHeartbeats 1200000 in
set_option linter.unusedVariables false in
theorem mcd_h2_bdd
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀0 : 0 ≤ δ₀) (hδ₀ : δ₀ < 1) :
    ∃ B : ℝ → ℝ,
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B R) ∧
      ∀ (gm : SmoothRiemannianMetric I M)
        (P : SmoothCcTensor g 0 2)
        (hP : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g P x u v =
            ccTensorBilin (I := I) g P x v u)
        (htie : ∀ (x : M) (u v : TangentSpace I x),
          gm.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g P x u v)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
        (hδ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g P) δ)
        (R A : ℝ), 0 ≤ R → 0 ≤ A →
        lowJetSq (I := I) (M := M) g 2 P ≤ R ^ 2 →
        lowJetSq (I := I) (M := M) g 3 P ≤ A ^ 2 →
      lowJetSq (I := I) (M := M) g 2
          (metricConnDiffLoweredCc (I := I) (M := M) g gm g) ≤
        (B R * (1 + A)) ^ 2 := by
  obtain ⟨Kw, hKw, hw⟩ :=
    wXi_h2_low (I := I) (M := M) g hδ₀0 hδ₀
  obtain ⟨Cc, hCc, hmul⟩ :=
    metricCorr_h2_mul (I := I) (M := M) hDim g
  let Q : ℝ → ℝ := fun R => 2 * Kw * (1 + Cc * R ^ 2)
  let B : ℝ → ℝ := fun R => Real.sqrt (Q R)
  have hQ : ∀ R : ℝ, 0 ≤ R → 0 ≤ Q R := by
    intro R hR
    exact mul_nonneg (mul_nonneg (by norm_num) hKw)
      (add_nonneg (by norm_num) (mul_nonneg hCc (sq_nonneg R)))
  refine ⟨B, fun R hR => Real.sqrt_nonneg _, ?_⟩
  intro gm P hP htie δ hδ_le hδ0 hδ R A hR hA hP2 hP3
  let X : SmoothCcTensor g 0 3 :=
    wXi (I := I) (M := M) g gm g
  let Y : SmoothCcTensor g 0 3 :=
    metricLowerCorr (I := I) (M := M) g gm g P
  have hX :
      lowJetSq (I := I) (M := M) g 2 X ≤
        Kw * (1 + A ^ 2) := by
    exact (hw gm P hP htie hδ_le hδ0 hδ).trans
      (mul_le_mul_of_nonneg_left (add_le_add le_rfl hP3) hKw)
  have hY :
      lowJetSq (I := I) (M := M) g 2 Y ≤
        Cc * R ^ 2 * (Kw * (1 + A ^ 2)) := by
    have hraw := hmul gm g P
    change lowJetSq (I := I) (M := M) g 2 Y ≤
      Cc * lowJetSq (I := I) (M := M) g 2 P *
        lowJetSq (I := I) (M := M) g 2 X at hraw
    exact hraw.trans
      (mul_le_mul
        (mul_le_mul_of_nonneg_left hP2 hCc) hX
        (jet_nonneg (I := I) (M := M) g X)
        (mul_nonneg hCc (sq_nonneg R)))
  rw [mcd_lower_split (I := I) (M := M) g gm g P htie]
  change lowJetSq (I := I) (M := M) g 2 (X + Y) ≤ _
  have hBsq : (B R) ^ 2 = Q R := by
    simpa only [B] using Real.sq_sqrt (hQ R hR)
  have hscalar : 1 + A ^ 2 ≤ (1 + A) ^ 2 := by
    nlinarith
  calc
    lowJetSq (I := I) (M := M) g 2 (X + Y) ≤
        2 * (lowJetSq (I := I) (M := M) g 2 X +
          lowJetSq (I := I) (M := M) g 2 Y) :=
      jet_add1 (I := I) (M := M) g 2 X Y
    _ ≤ 2 * (Kw * (1 + A ^ 2) +
        Cc * R ^ 2 * (Kw * (1 + A ^ 2))) :=
      mul_le_mul_of_nonneg_left (add_le_add hX hY) (by norm_num)
    _ = Q R * (1 + A ^ 2) := by
      simp only [Q]
      ring
    _ ≤ Q R * (1 + A) ^ 2 :=
      mul_le_mul_of_nonneg_left hscalar (hQ R hR)
    _ = (B R * (1 + A)) ^ 2 := by
      rw [mul_pow, hBsq]

set_option maxHeartbeats 1600000 in
set_option linter.unusedVariables false in
/-- `H¹` two-state modulus for the moving-metric lowered connection
difference, with the `D2`-only (third-difference-free) right-hand side
required by the `C0` low-regularity lane. -/
theorem mcd_pair_h1
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
          (metricConnDiffLoweredCc (I := I) (M := M) g gT g -
            metricConnDiffLoweredCc (I := I) (M := M) g gU g) ≤
        (B0 R * D2 + B1 R * A * D2) ^ 2 := by
  obtain ⟨W0, W1, hW0, hW1, hwp⟩ :=
    wXi_pair_h1 (I := I) (M := M) hDim g hδ₀0 hδ₀
  obtain ⟨Kw, hKw, hwlow⟩ :=
    wXi_h2_low (I := I) (M := M) g hδ₀0 hδ₀
  obtain ⟨Cc, hCc, hcp⟩ :=
    metricCorr_pair_h1 (I := I) (M := M) hDim g
  let Q0 : ℝ → ℝ := fun R =>
    2 * (2 * (W0 R) ^ 2 + Cc * (Kw + R ^ 2 * (2 * (W0 R) ^ 2)))
  let Q1 : ℝ → ℝ := fun R =>
    2 * (2 * (W1 R) ^ 2 + Cc * (Kw + R ^ 2 * (2 * (W1 R) ^ 2)))
  have hQ0 : ∀ R : ℝ, 0 ≤ R → 0 ≤ Q0 R := by
    intro R hR
    have : 0 ≤ Cc * (Kw + R ^ 2 * (2 * (W0 R) ^ 2)) :=
      mul_nonneg hCc (by positivity)
    positivity
  have hQ1 : ∀ R : ℝ, 0 ≤ R → 0 ≤ Q1 R := by
    intro R hR
    have : 0 ≤ Cc * (Kw + R ^ 2 * (2 * (W1 R) ^ 2)) :=
      mul_nonneg hCc (by positivity)
    positivity
  refine ⟨fun R => Real.sqrt (Q0 R), fun R => Real.sqrt (Q1 R),
    fun R hR => Real.sqrt_nonneg _, fun R hR => Real.sqrt_nonneg _, ?_⟩
  intro gT gU T U hT hU hTtie hUtie
    δT δU hδT_le hδT0 hδT hδU_le hδU0 hδU
    R A D2 hR hA hD2 hU2 hT3 hTU2
  have hwd : lowJetSq (I := I) (M := M) g 1
      (wXi (I := I) (M := M) g gT g -
        wXi (I := I) (M := M) g gU g) ≤
      (W0 R * D2 + W1 R * A * D2) ^ 2 :=
    hwp gT gU g T U hT hU hTtie hUtie
      hδT_le hδT0 hδT hδU_le hδU0 hδU R A D2 hR hA hD2 hU2 hT3 hTU2
  have hws : lowJetSq (I := I) (M := M) g 1
      (wXi (I := I) (M := M) g gT g) ≤ Kw * (1 + A ^ 2) := by
    have h2 := hwlow gT T hT hTtie hδT_le hδT0 hδT
    have hmono : lowJetSq (I := I) (M := M) g 1
        (wXi (I := I) (M := M) g gT g) ≤
        lowJetSq (I := I) (M := M) g 2
          (wXi (I := I) (M := M) g gT g) :=
      jet_mono (I := I) (M := M) g (by norm_num) _
    refine hmono.trans (h2.trans ?_)
    have : 1 + lowJetSq (I := I) (M := M) g 3 T ≤ 1 + A ^ 2 := by
      linarith [hT3]
    exact mul_le_mul_of_nonneg_left this hKw
  have hcd : lowJetSq (I := I) (M := M) g 1
      (metricLowerCorr (I := I) (M := M) g gT g T -
        metricLowerCorr (I := I) (M := M) g gU g U) ≤
      Cc * (D2 ^ 2 * (Kw * (1 + A ^ 2)) +
        R ^ 2 * (W0 R * D2 + W1 R * A * D2) ^ 2) := by
    refine (hcp gT gU T U).trans
      (mul_le_mul_of_nonneg_left ?_ hCc)
    have hx : lowJetSq (I := I) (M := M) g 2 (T - U) *
        lowJetSq (I := I) (M := M) g 1
          (wXi (I := I) (M := M) g gT g) ≤
        D2 ^ 2 * (Kw * (1 + A ^ 2)) :=
      mul_le_mul hTU2 hws
        (jet_nonneg (I := I) (M := M) g _) (sq_nonneg _)
    have hy : lowJetSq (I := I) (M := M) g 2 U *
        lowJetSq (I := I) (M := M) g 1
          (wXi (I := I) (M := M) g gT g -
            wXi (I := I) (M := M) g gU g) ≤
        R ^ 2 * (W0 R * D2 + W1 R * A * D2) ^ 2 :=
      mul_le_mul hU2 hwd
        (jet_nonneg (I := I) (M := M) g _) (sq_nonneg _)
    linarith
  have hsub := mcd_sub_eq (I := I) (M := M) g gT gU T U hTtie hUtie
  rw [hsub]
  have hadd := jet_add1 (I := I) (M := M) g 1
    (wXi (I := I) (M := M) g gT g -
      wXi (I := I) (M := M) g gU g)
    (metricLowerCorr (I := I) (M := M) g gT g T -
      metricLowerCorr (I := I) (M := M) g gU g U)
  have hcross : (W0 R * D2 + W1 R * A * D2) ^ 2 ≤
      2 * (W0 R) ^ 2 * D2 ^ 2 + 2 * (W1 R) ^ 2 * (A ^ 2 * D2 ^ 2) := by
    nlinarith [sq_nonneg (W0 R * D2 - W1 R * A * D2)]
  have hs0 : Real.sqrt (Q0 R) ^ 2 = Q0 R :=
    Real.sq_sqrt (hQ0 R hR)
  have hs1 : Real.sqrt (Q1 R) ^ 2 = Q1 R :=
    Real.sq_sqrt (hQ1 R hR)
  have hrhs : (Real.sqrt (Q0 R) * D2 + Real.sqrt (Q1 R) * (A * D2)) ^ 2 =
      Q0 R * D2 ^ 2 + Q1 R * (A ^ 2 * D2 ^ 2) +
        2 * (Real.sqrt (Q0 R) * Real.sqrt (Q1 R)) * (A * D2 ^ 2) := by
    have : (Real.sqrt (Q0 R) * D2 + Real.sqrt (Q1 R) * (A * D2)) ^ 2 =
        Real.sqrt (Q0 R) ^ 2 * D2 ^ 2 +
          Real.sqrt (Q1 R) ^ 2 * (A ^ 2 * D2 ^ 2) +
          2 * (Real.sqrt (Q0 R) * Real.sqrt (Q1 R)) * (A * D2 ^ 2) := by
      ring
    rw [this, hs0, hs1]
  have hcross0 : 0 ≤
      2 * (Real.sqrt (Q0 R) * Real.sqrt (Q1 R)) * (A * D2 ^ 2) := by
    have h1 : 0 ≤ Real.sqrt (Q0 R) * Real.sqrt (Q1 R) :=
      mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    have h2 : 0 ≤ A * D2 ^ 2 := mul_nonneg hA (sq_nonneg _)
    positivity
  calc
    lowJetSq (I := I) (M := M) g 1
        ((wXi (I := I) (M := M) g gT g -
            wXi (I := I) (M := M) g gU g) +
          (metricLowerCorr (I := I) (M := M) g gT g T -
            metricLowerCorr (I := I) (M := M) g gU g U)) ≤
      2 * (lowJetSq (I := I) (M := M) g 1
          (wXi (I := I) (M := M) g gT g -
            wXi (I := I) (M := M) g gU g) +
        lowJetSq (I := I) (M := M) g 1
          (metricLowerCorr (I := I) (M := M) g gT g T -
            metricLowerCorr (I := I) (M := M) g gU g U)) := hadd
    _ ≤ 2 * ((W0 R * D2 + W1 R * A * D2) ^ 2 +
        Cc * (D2 ^ 2 * (Kw * (1 + A ^ 2)) +
          R ^ 2 * (W0 R * D2 + W1 R * A * D2) ^ 2)) := by
      linarith [hwd, hcd]
    _ ≤ Q0 R * D2 ^ 2 + Q1 R * (A ^ 2 * D2 ^ 2) := by
      have hexp : Cc * (D2 ^ 2 * (Kw * (1 + A ^ 2)) +
          R ^ 2 * (W0 R * D2 + W1 R * A * D2) ^ 2) ≤
          Cc * (D2 ^ 2 * (Kw * (1 + A ^ 2)) +
            R ^ 2 * (2 * (W0 R) ^ 2 * D2 ^ 2 +
              2 * (W1 R) ^ 2 * (A ^ 2 * D2 ^ 2))) := by
        refine mul_le_mul_of_nonneg_left ?_ hCc
        have := mul_le_mul_of_nonneg_left hcross (sq_nonneg R)
        linarith
      have hcross' := hcross
      simp only [Q0, Q1]
      nlinarith [hexp, hcross', hCc, hKw, sq_nonneg D2, sq_nonneg A,
        mul_nonneg (sq_nonneg A) (sq_nonneg D2)]
    _ ≤ (Real.sqrt (Q0 R) * D2 + Real.sqrt (Q1 R) * (A * D2)) ^ 2 := by
      rw [hrhs]
      linarith [hcross0]
    _ = (Real.sqrt (Q0 R) * D2 + Real.sqrt (Q1 R) * A * D2) ^ 2 := by
      ring

set_option linter.unusedVariables false in
/-- Raw fixed-order `H²` bound for the moving-second raised-endomorphism
factor inserted at the rank-two slot, in the `H²` size of the tied metric
perturbation. -/
private theorem fullSlot1_h2
    (g : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀0 : 0 ≤ δ₀) (hδ₀ : δ₀ < 1) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (gm : SmoothRiemannianMetric I M)
        (P : SmoothCcTensor g 0 2)
        (hP : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g P x u v =
            ccTensorBilin (I := I) g P x v u)
        (htie : ∀ (x : M) (u v : TangentSpace I x),
          gm.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g P x u v)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
        (hδ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g P) δ),
      lowJetSq (I := I) (M := M) g 2
          (slotInsertEndoCc (I := I) (M := M) g 1
            (fullRaisedEndoField (I := I) (M := M) g gm)) ≤
        K * (1 + lowJetSq (I := I) (M := M) g 2 P) := by
  obtain ⟨K₀, hK₀, hsharp⟩ :=
    sharp_h2_low (I := I) (M := M) g hδ₀0 hδ₀
  let fr : ℝ := Module.finrank ℝ E
  let K : ℝ := fr ^ 1 * K₀
  have hfr : 0 ≤ fr := Nat.cast_nonneg _
  have hK : 0 ≤ K := mul_nonneg (pow_nonneg hfr 1) hK₀
  refine ⟨K, hK, ?_⟩
  intro gm P hP htie δ hδ_le hδ0 hδ
  calc
    lowJetSq (I := I) (M := M) g 2
        (slotInsertEndoCc (I := I) (M := M) g 1
          (fullRaisedEndoField (I := I) (M := M) g gm)) ≤
      fr ^ 1 * lowJetSq (I := I) (M := M) g 2
        (slotInsertEndoCc (I := I) (M := M) g 0
          (fullRaisedEndoField (I := I) (M := M) g gm)) := by
      simpa only [fr] using
        endo_slot_h2 (I := I) (M := M) g 1
          (fullRaisedEndoField (I := I) (M := M) g gm)
    _ = fr ^ 1 * lowJetSq (I := I) (M := M) g 2
        (sharpFlatEndoCc (I := I) g gm) := by
      rw [sharp_eq_slot0 (I := I) (M := M) g gm]
    _ ≤ fr ^ 1 * (K₀ *
        (1 + lowJetSq (I := I) (M := M) g 2 P)) :=
      mul_le_mul_of_nonneg_left
        (hsharp gm P hP htie hδ_le hδ0 hδ) (pow_nonneg hfr 1)
    _ = K * (1 + lowJetSq (I := I) (M := M) g 2 P) := by
      simp only [K]
      ring

set_option linter.unusedVariables false in
/-- Single-state `H²` bound for the moving-second raised-endomorphism factor
`slotInsertEndoCc g 1 (fullRaisedEndoField g gm)` used by `daMono`: the size
is controlled by the `H²` radius of the tied metric perturbation alone. -/
theorem fullSlot_bdd_h2
    (g : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀0 : 0 ≤ δ₀) (hδ₀ : δ₀ < 1) :
    ∃ B : ℝ → ℝ,
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B R) ∧
      ∀ (gm : SmoothRiemannianMetric I M)
        (P : SmoothCcTensor g 0 2)
        (hP : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g P x u v =
            ccTensorBilin (I := I) g P x v u)
        (htie : ∀ (x : M) (u v : TangentSpace I x),
          gm.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g P x u v)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
        (hδ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g P) δ)
        (R : ℝ), 0 ≤ R →
        lowJetSq (I := I) (M := M) g 2 P ≤ R ^ 2 →
      lowJetSq (I := I) (M := M) g 2
          (slotInsertEndoCc (I := I) (M := M) g 1
            (fullRaisedEndoField (I := I) (M := M) g gm)) ≤
        (B R) ^ 2 := by
  obtain ⟨K, hK, hfull⟩ :=
    fullSlot1_h2 (I := I) (M := M) g hδ₀0 hδ₀
  let Q : ℝ → ℝ := fun R => K * (1 + R ^ 2)
  let B : ℝ → ℝ := fun R => Real.sqrt (Q R)
  have hQ : ∀ R : ℝ, 0 ≤ R → 0 ≤ Q R := by
    intro R hR
    exact mul_nonneg hK (by positivity)
  refine ⟨B, fun R hR => Real.sqrt_nonneg _, ?_⟩
  intro gm P hP htie δ hδ_le hδ0 hδ R hR hP2
  have hBsq : (B R) ^ 2 = Q R := by
    simpa only [B] using Real.sq_sqrt (hQ R hR)
  calc
    lowJetSq (I := I) (M := M) g 2
        (slotInsertEndoCc (I := I) (M := M) g 1
          (fullRaisedEndoField (I := I) (M := M) g gm)) ≤
      K * (1 + lowJetSq (I := I) (M := M) g 2 P) :=
        hfull gm P hP htie hδ_le hδ0 hδ
    _ ≤ Q R := by
      simp only [Q]
      exact mul_le_mul_of_nonneg_left (by linarith) hK
    _ = (B R) ^ 2 := hBsq.symm

set_option maxHeartbeats 1600000 in
set_option linter.unusedVariables false in
/-- `H¹` two-state modulus for the moving-second raised-endomorphism factor,
with the `D2`-only (third-difference-free) right-hand side required by the
`C0` low-regularity lane.  The difference is handled by the resolvent
factorisation `invSlot_sub_factor`, so only the `H²` size `D2` of the
perturbation difference enters. -/
theorem fullSlot_pair_h1
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
          (slotInsertEndoCc (I := I) (M := M) g 1
              (fullRaisedEndoField (I := I) (M := M) g gT) -
            slotInsertEndoCc (I := I) (M := M) g 1
              (fullRaisedEndoField (I := I) (M := M) g gU)) ≤
        (B0 R * D2 + B1 R * A * D2) ^ 2 := by
  obtain ⟨K, hK, hfull⟩ :=
    fullSlot1_h2 (I := I) (M := M) g hδ₀0 hδ₀
  obtain ⟨Cm, hCm, happ⟩ :=
    app_h21_mul (I := I) (M := M) hDim g 2 2 2
  let fr : ℝ := Module.finrank ℝ E
  have hfr : (0 : ℝ) ≤ fr := Nat.cast_nonneg _
  let Z : ℝ := Cm ^ 2 * K ^ 2 * fr
  have hZ : 0 ≤ Z :=
    mul_nonneg (mul_nonneg (sq_nonneg Cm) (sq_nonneg K)) hfr
  let Q : ℝ → ℝ := fun R => 2 * Z * (1 + R ^ 2)
  let B : ℝ → ℝ := fun R => Real.sqrt (Q R)
  have hQ : ∀ R : ℝ, 0 ≤ R → 0 ≤ Q R := by
    intro R hR
    exact mul_nonneg (mul_nonneg (by norm_num) hZ) (by positivity)
  refine ⟨B, B, fun R hR => Real.sqrt_nonneg _,
    fun R hR => Real.sqrt_nonneg _, ?_⟩
  intro gT gU T U hT hU hTtie hUtie
    δT δU hδT_le hδT0 hδT hδU_le hδU0 hδU
    R A D2 hR hA hD2 hU2 hT3 hTU2
  have hsymm : symmS (I := I) (M := M) g (T - U) = T - U := by
    rw [symmS_sub, symm_eq_self (I := I) (M := M) g T hT,
      symm_eq_self (I := I) (M := M) g U hU]
  have hdiff :
      fullRaisedEndoField (I := I) (M := M) g gT -
          fullRaisedEndoField (I := I) (M := M) g gU =
        gInvDiffRaisedEndoField (I := I) g gT -
          gInvDiffRaisedEndoField (I := I) g gU := by
    apply ContMDiffSection.ext
    intro x
    rw [ContMDiffSection.coe_sub, Pi.sub_apply,
      ContMDiffSection.coe_sub, Pi.sub_apply]
    apply ContinuousLinearMap.ext
    intro v
    rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.sub_apply,
      fullRaisedEndoField_apply, fullRaisedEndoField_apply,
      show gInvDiffRaisedEndoField (I := I) g gT x =
        gInvDiffRaisedEndo (I := I) g gT x from rfl,
      show gInvDiffRaisedEndoField (I := I) g gU x =
        gInvDiffRaisedEndo (I := I) g gU x from rfl,
      gInvRaisedEndo_eq_diff_add_id (I := I) g gT x v,
      gInvRaisedEndo_eq_diff_add_id (I := I) g gU x v]
    abel
  have hslot :
      slotInsertEndoCc (I := I) (M := M) g 1
            (fullRaisedEndoField (I := I) (M := M) g gT) -
          slotInsertEndoCc (I := I) (M := M) g 1
            (fullRaisedEndoField (I := I) (M := M) g gU) =
        gInvDiffSlotCoeff (I := I) g gT -
          gInvDiffSlotCoeff (I := I) g gU := by
    rw [gInvDiffSlotCoeff_eq_slotInsertEndoCc (I := I) g gT,
      gInvDiffSlotCoeff_eq_slotInsertEndoCc (I := I) g gU,
      ← slotInsertEndoCc_sub, ← slotInsertEndoCc_sub, hdiff]
  have hT2 : lowJetSq (I := I) (M := M) g 2 T ≤ A ^ 2 :=
    (jet_mono (I := I) (M := M) (m := 2) (n := 3) g
      (by norm_num) T).trans hT3
  have hbdU : lowJetSq (I := I) (M := M) g 2
      (slotInsertEndoCc (I := I) (M := M) g 1
        (fullRaisedEndoField (I := I) (M := M) g gU)) ≤
      K * (1 + R ^ 2) :=
    (hfull gU U hU hUtie hδU_le hδU0 hδU).trans
      (mul_le_mul_of_nonneg_left (by linarith) hK)
  have hbdT2 : lowJetSq (I := I) (M := M) g 2
      (slotInsertEndoCc (I := I) (M := M) g 1
        (fullRaisedEndoField (I := I) (M := M) g gT)) ≤
      K * (1 + A ^ 2) :=
    (hfull gT T hT hTtie hδT_le hδT0 hδT).trans
      (mul_le_mul_of_nonneg_left (by linarith) hK)
  have hbdT1 : lowJetSq (I := I) (M := M) g 1
      (slotInsertEndoCc (I := I) (M := M) g 1
        (fullRaisedEndoField (I := I) (M := M) g gT)) ≤
      K * (1 + A ^ 2) :=
    (jet_mono (I := I) (M := M) (m := 1) (n := 2) g
      (by norm_num) _).trans hbdT2
  have hbdP : lowJetSq (I := I) (M := M) g 2
      (slotInsertEndoCc (I := I) (M := M) g 1
        (symmRaiseEndo (I := I) (M := M) g (T - U))) ≤
      fr * D2 ^ 2 := by
    have h1 := endo_slot_h2 (I := I) (M := M) g 1
      (symmRaiseEndo (I := I) (M := M) g (T - U))
    have h2 : lowJetSq (I := I) (M := M) g 2
        (slotInsertEndoCc (I := I) (M := M) g 0
          (symmRaiseEndo (I := I) (M := M) g (T - U))) =
        lowJetSq (I := I) (M := M) g 2 (T - U) := by
      rw [show slotInsertEndoCc (I := I) (M := M) g 0
          (symmRaiseEndo (I := I) (M := M) g (T - U)) =
          perturb0 (I := I) (M := M) g (T - U) from rfl]
      exact perturb_h2_eq (I := I) (M := M) g (T - U) hsymm
    rw [h2] at h1
    refine h1.trans ?_
    simp only [fr, pow_one]
    exact mul_le_mul_of_nonneg_left hTU2 (Nat.cast_nonneg _)
  have harith : ∀ a b c y w : ℝ,
      w ≤ Cm * a * y → y ≤ Cm * b * c →
      a ≤ K * (1 + R ^ 2) → b ≤ fr * D2 ^ 2 →
      c ≤ K * (1 + A ^ 2) →
      0 ≤ a → 0 ≤ b → 0 ≤ c → 0 ≤ y →
      w ≤ Z * ((1 + R ^ 2) * ((1 + A ^ 2) * D2 ^ 2)) := by
    intro a b c y w hw hyb haR hbD hcA ha hb hc hy
    have hA1 : Cm * a ≤ Cm * (K * (1 + R ^ 2)) :=
      mul_le_mul_of_nonneg_left haR hCm
    have hB1 : Cm * b * c ≤
        Cm * (fr * D2 ^ 2) * (K * (1 + A ^ 2)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hbD hCm) hcA hc
        (mul_nonneg hCm (mul_nonneg hfr (sq_nonneg D2)))
    have hy' : y ≤ Cm * (fr * D2 ^ 2) * (K * (1 + A ^ 2)) :=
      hyb.trans hB1
    have hprod : Cm * a * y ≤
        Cm * (K * (1 + R ^ 2)) *
          (Cm * (fr * D2 ^ 2) * (K * (1 + A ^ 2))) :=
      mul_le_mul hA1 hy' hy
        (mul_nonneg hCm (mul_nonneg hK (by positivity)))
    refine hw.trans (hprod.trans (le_of_eq ?_))
    simp only [Z]
    ring
  have hinner := happ
    (slotInsertEndoCc (I := I) (M := M) g 1
      (symmRaiseEndo (I := I) (M := M) g (T - U)))
    (slotInsertEndoCc (I := I) (M := M) g 1
      (fullRaisedEndoField (I := I) (M := M) g gT))
  have houter := happ
    (slotInsertEndoCc (I := I) (M := M) g 1
      (fullRaisedEndoField (I := I) (M := M) g gU))
    (appCcRS (I := I) (M := M) g 2 2 2
      (slotInsertEndoCc (I := I) (M := M) g 1
        (symmRaiseEndo (I := I) (M := M) g (T - U)))
      (slotInsertEndoCc (I := I) (M := M) g 1
        (fullRaisedEndoField (I := I) (M := M) g gT)))
  rw [hslot,
    invSlot_sub_factor (I := I) (M := M) g gT gU T U hTtie hUtie,
    jet_neg1]
  refine (harith _ _ _ _ _ houter hinner hbdU hbdP hbdT1
    (jet_nonneg (I := I) (M := M) (m := 2) g _)
    (jet_nonneg (I := I) (M := M) (m := 2) g _)
    (jet_nonneg (I := I) (M := M) (m := 1) g _)
    (jet_nonneg (I := I) (M := M) (m := 1) g _)).trans ?_
  have hBsq : (B R) ^ 2 = Q R := by
    simpa only [B] using Real.sq_sqrt (hQ R hR)
  have hexp : (B R * D2 + B R * A * D2) ^ 2 =
      Q R * (D2 ^ 2 * (1 + A) ^ 2) := by
    have h : (B R * D2 + B R * A * D2) ^ 2 =
        (B R) ^ 2 * (D2 ^ 2 * (1 + A) ^ 2) := by ring
    rw [h, hBsq]
  rw [hexp]
  have hA2 : 1 + A ^ 2 ≤ (1 + A) ^ 2 := by nlinarith [hA]
  have hstep : Z * ((1 + R ^ 2) * ((1 + A ^ 2) * D2 ^ 2)) ≤
      Z * ((1 + R ^ 2) * ((1 + A) ^ 2 * D2 ^ 2)) := by
    refine mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hA2 (sq_nonneg D2))
        (by positivity)) hZ
  have hnn : 0 ≤ Z * ((1 + R ^ 2) * ((1 + A) ^ 2 * D2 ^ 2)) :=
    mul_nonneg hZ (mul_nonneg (by positivity)
      (mul_nonneg (sq_nonneg _) (sq_nonneg _)))
  refine hstep.trans ?_
  simp only [Q]
  calc
    Z * ((1 + R ^ 2) * ((1 + A) ^ 2 * D2 ^ 2)) ≤
        Z * ((1 + R ^ 2) * ((1 + A) ^ 2 * D2 ^ 2)) +
          Z * ((1 + R ^ 2) * ((1 + A) ^ 2 * D2 ^ 2)) := by
      linarith [hnn]
    _ = 2 * Z * (1 + R ^ 2) * (D2 ^ 2 * (1 + A) ^ 2) := by ring

end LowBaseInternal

private theorem raiseDom_h2
    (g : SmoothRiemannianMetric I M)
    (ρ : Equiv.Perm (Fin 3)) (S : SmoothCcTensor g 0 3) :
    lowJetSq (I := I) (M := M) g 2
        (cometricRaiseSlot0Field (I := I) (M := M) g 1
          (domDomCongrSection (I := I) g ρ S)) =
      lowJetSq (I := I) (M := M) g 2 S := by
  calc
    lowJetSq (I := I) (M := M) g 2
        (cometricRaiseSlot0Field (I := I) (M := M) g 1
          (domDomCongrSection (I := I) g ρ S)) =
      lowJetSq (I := I) (M := M) g 2
        (domDomCongrSection (I := I) g ρ S) := by
          unfold lowJetSq
          apply Finset.sum_congr rfl
          intro q _
          rw [norm_iCG_cometricRaiseSlot0Field_eq
            (I := I) (M := M) g 1
            (domDomCongrSection (I := I) g ρ S) q]
    _ = lowJetSq (I := I) (M := M) g 2 S :=
      dom_h2 (I := I) (M := M) g ρ S

private theorem psiLeft_h2
    (g gm : SmoothRiemannianMetric I M) :
    lowJetSq (I := I) (M := M) g 2
        (psiLeft (I := I) (M := M) g gm) =
      lowJetSq (I := I) (M := M) g 2
        (lieArm1LoweredBgKappa (I := I) (M := M) g gm g) := by
  exact raiseDom_h2 (I := I) (M := M) g lieArm1RhoSlot0 _

private theorem psiLeft_sub_h2
    (g gT gU : SmoothRiemannianMetric I M) :
    lowJetSq (I := I) (M := M) g 2
        (psiLeft (I := I) (M := M) g gT -
          psiLeft (I := I) (M := M) g gU) =
      lowJetSq (I := I) (M := M) g 2
        (lieArm1LoweredBgKappa (I := I) (M := M) g gT g -
          lieArm1LoweredBgKappa (I := I) (M := M) g gU g) := by
  rw [show psiLeft (I := I) (M := M) g gT -
      psiLeft (I := I) (M := M) g gU =
    cometricRaiseSlot0Field (I := I) (M := M) g 1
      (domDomCongrSection (I := I) g lieArm1RhoSlot0
        (lieArm1LoweredBgKappa (I := I) (M := M) g gT g -
          lieArm1LoweredBgKappa (I := I) (M := M) g gU g)) by
    simp only [psiLeft]
    rw [dom_sub, raise_sub]]
  exact raiseDom_h2 (I := I) (M := M) g lieArm1RhoSlot0 _

set_option maxHeartbeats 2400000 in
set_option synthInstance.maxHeartbeats 2400000 in
set_option linter.unusedVariables false in
private theorem psi_pair_h2
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀0 : 0 ≤ δ₀) (hδ₀ : δ₀ < 1) :
    ∃ ρ P B0 B1 : ℝ,
      0 < ρ ∧ 0 ≤ P ∧ 0 ≤ B0 ∧ 0 ≤ B1 ∧
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
          (ccTensorBilinSymm (I := I) g U) δU),
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ ≤ ρ →
        ∀ (A D3 : ℝ), 0 ≤ A → 0 ≤ D3 →
        lowJetSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
        lowJetSq (I := I) (M := M) g 3 (T - U) ≤ D3 ^ 2 →
      let N :=
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U)‖
      lowJetSq (I := I) (M := M) g 2
          (lieArm1PsiB (I := I) (M := M) g gT g) ≤
          (P * (1 + A)) ^ 2 ∧
        lowJetSq (I := I) (M := M) g 2
          (lieArm1PsiB (I := I) (M := M) g gT g -
            lieArm1PsiB (I := I) (M := M) g gU g) ≤
          (B0 * D3 + B1 * N + B1 * A * N) ^ 2 := by
  obtain ⟨ρs, Cs, hρs, hCs, hsharpPair⟩ :=
    sharp_pair_h2 (I := I) (M := M) hDim g hδ₀0 hδ₀
  obtain ⟨M0, M1, hM0, hM1, hmcdPair⟩ :=
    LowBaseInternal.mcd_pair_h2 (I := I) (M := M) hDim g hδ₀0 hδ₀
  obtain ⟨Mb, hMb, hmcdBdd⟩ :=
    LowBaseInternal.mcd_h2_bdd (I := I) (M := M) hDim g hδ₀0 hδ₀
  obtain ⟨Ks, hKs, hsharpBdd⟩ :=
    sharp_h2_low (I := I) (M := M) g hδ₀0 hδ₀
  obtain ⟨Ch, hCh, hhs⟩ :=
    hs2_low2 (I := I) (M := M) g 2
  obtain ⟨Ca, hCa, happ⟩ :=
    app_h2_mul (I := I) (M := M) hDim g 1 1 2
  let ρ : ℝ := ρs
  let R0 : ℝ := Ch * ρ
  let S0 : ℝ := Ks * (1 + R0 ^ 2)
  let Bs : ℝ := Real.sqrt S0
  let H : ℝ := Real.sqrt Ca
  let P : ℝ := H * Mb R0 * Bs
  let B0 : ℝ := 2 * H * (Bs * M0 R0)
  let B1 : ℝ := 2 * H * (Mb R0 * Cs + Bs * M1 R0 * Ch)
  have hρ : 0 < ρ := hρs
  have hR0 : 0 ≤ R0 := mul_nonneg hCh hρ.le
  have hS0 : 0 ≤ S0 :=
    mul_nonneg hKs (add_nonneg (by norm_num) (sq_nonneg R0))
  have hBs : 0 ≤ Bs := Real.sqrt_nonneg _
  have hBssq : Bs ^ 2 = S0 := by
    simpa only [Bs] using Real.sq_sqrt hS0
  have hH : 0 ≤ H := Real.sqrt_nonneg _
  have hHsq : H ^ 2 = Ca := by
    simpa only [H] using Real.sq_sqrt hCa
  have hP : 0 ≤ P :=
    mul_nonneg (mul_nonneg hH (hMb R0 hR0)) hBs
  have hB0 : 0 ≤ B0 :=
    mul_nonneg (mul_nonneg (by norm_num) hH)
      (mul_nonneg hBs (hM0 R0 hR0))
  have hB1 : 0 ≤ B1 :=
    mul_nonneg (mul_nonneg (by norm_num) hH)
      (add_nonneg
        (mul_nonneg (hMb R0 hR0) hCs)
        (mul_nonneg (mul_nonneg hBs (hM1 R0 hR0)) hCh))
  refine ⟨ρ, P, B0, B1, hρ, hP, hB0, hB1, ?_⟩
  intro gT gU T U hT hU hTtie hUtie
    δT δU hδT_le hδT0 hδT hδU_le hδU0 hδU
    hTHs hUHs A D3 hA hD3 hT3 hTU3
  dsimp only
  let N : ℝ :=
    ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U)‖
  let KT : SmoothCcTensor g 0 3 :=
    lieArm1LoweredBgKappa (I := I) (M := M) g gT g
  let KU : SmoothCcTensor g 0 3 :=
    lieArm1LoweredBgKappa (I := I) (M := M) g gU g
  let LT : SmoothCcTensor g 1 2 :=
    psiLeft (I := I) (M := M) g gT
  let LU : SmoothCcTensor g 1 2 :=
    psiLeft (I := I) (M := M) g gU
  let ST : SmoothCcTensor g 1 1 :=
    sharpFlatEndoCc (I := I) g gT
  let SU : SmoothCcTensor g 1 1 :=
    sharpFlatEndoCc (I := I) g gU
  let XD : ℝ := M0 R0 * D3 +
    M1 R0 * (Ch * N) + M1 R0 * A * (Ch * N)
  let Z1 : ℝ := H * (Mb R0 * (1 + A)) * (Cs * N)
  let Z2 : ℝ := H * XD * Bs
  have hN : 0 ≤ N := norm_nonneg _
  have hT2 :
      lowJetSq (I := I) (M := M) g 2 T ≤ R0 ^ 2 := by
    calc
      lowJetSq (I := I) (M := M) g 2 T ≤
          (Ch * ‖ccTensorToHs (I := I) (M := M) g 2
            (2 : ℝ) T‖) ^ 2 := by
        simpa only [lowJetSq, Nat.reduceAdd] using hhs T
      _ ≤ (Ch * ρ) ^ 2 :=
        pow_le_pow_left₀
          (mul_nonneg hCh (norm_nonneg _))
          (mul_le_mul_of_nonneg_left hTHs hCh) 2
      _ = R0 ^ 2 := rfl
  have hU2 :
      lowJetSq (I := I) (M := M) g 2 U ≤ R0 ^ 2 := by
    calc
      lowJetSq (I := I) (M := M) g 2 U ≤
          (Ch * ‖ccTensorToHs (I := I) (M := M) g 2
            (2 : ℝ) U‖) ^ 2 := by
        simpa only [lowJetSq, Nat.reduceAdd] using hhs U
      _ ≤ (Ch * ρ) ^ 2 :=
        pow_le_pow_left₀
          (mul_nonneg hCh (norm_nonneg _))
          (mul_le_mul_of_nonneg_left hUHs hCh) 2
      _ = R0 ^ 2 := rfl
  have hTU2 :
      lowJetSq (I := I) (M := M) g 2 (T - U) ≤
        (Ch * N) ^ 2 := by
    simpa only [lowJetSq, Nat.reduceAdd, N] using hhs (T - U)
  have hST :
      lowJetSq (I := I) (M := M) g 2 ST ≤ S0 := by
    calc
      lowJetSq (I := I) (M := M) g 2 ST ≤
        Ks * (1 + lowJetSq (I := I) (M := M) g 2 T) := by
          simpa only [ST] using
            hsharpBdd gT T hT hTtie hδT_le hδT0 hδT
      _ ≤ S0 := by
        dsimp only [S0]
        exact mul_le_mul_of_nonneg_left (add_le_add le_rfl hT2) hKs
  have hSU :
      lowJetSq (I := I) (M := M) g 2 SU ≤ S0 := by
    calc
      lowJetSq (I := I) (M := M) g 2 SU ≤
        Ks * (1 + lowJetSq (I := I) (M := M) g 2 U) := by
          simpa only [SU] using
            hsharpBdd gU U hU hUtie hδU_le hδU0 hδU
      _ ≤ S0 := by
        dsimp only [S0]
        exact mul_le_mul_of_nonneg_left (add_le_add le_rfl hU2) hKs
  have hSD :
      lowJetSq (I := I) (M := M) g 2 (ST - SU) ≤
        (Cs * N) ^ 2 := by
    simpa only [ST, SU, N, ρ] using
      hsharpPair gT gU T U hT hU hTtie hUtie
        hδT_le hδT0 hδT hδU_le hδU0 hδU hTHs hUHs
  have hKT :
      lowJetSq (I := I) (M := M) g 2 KT ≤
        (Mb R0 * (1 + A)) ^ 2 := by
    have hraw := hmcdBdd gT T hT hTtie
      hδT_le hδT0 hδT R0 A hR0 hA hT2 hT3
    rw [metricConnDiffLoweredCc_eq_neg_kappa
      (I := I) (M := M) g gT g,
      jet_neg1 (I := I) (M := M) g 2] at hraw
    simpa only [KT] using hraw
  have hLT :
      lowJetSq (I := I) (M := M) g 2 LT ≤
        (Mb R0 * (1 + A)) ^ 2 := by
    rw [show lowJetSq (I := I) (M := M) g 2 LT =
        lowJetSq (I := I) (M := M) g 2 KT by
      simpa only [LT, KT] using
        psiLeft_h2 (I := I) (M := M) g gT]
    exact hKT
  have hKD :
      lowJetSq (I := I) (M := M) g 2 (KT - KU) ≤ XD ^ 2 := by
    have hraw := hmcdPair gT gU T U hT hU hTtie hUtie
      hδT_le hδT0 hδT hδU_le hδU0 hδU
      R0 A (Ch * N) D3 hR0 hA (mul_nonneg hCh hN) hD3
      hU2 hT3 hTU2 hTU3
    rw [metricConnDiffLoweredCc_eq_neg_kappa
      (I := I) (M := M) g gT g,
      metricConnDiffLoweredCc_eq_neg_kappa
      (I := I) (M := M) g gU g] at hraw
    have hsign : -KT - -KU = -(KT - KU) := by
      simp only [KT, KU]
      module
    rw [hsign, jet_neg1 (I := I) (M := M) g 2] at hraw
    simpa only [XD] using hraw
  have hLD :
      lowJetSq (I := I) (M := M) g 2 (LT - LU) ≤ XD ^ 2 := by
    rw [show lowJetSq (I := I) (M := M) g 2 (LT - LU) =
        lowJetSq (I := I) (M := M) g 2 (KT - KU) by
      simpa only [LT, LU, KT, KU] using
        psiLeft_sub_h2 (I := I) (M := M) g gT gU]
    exact hKD
  have hPsiT :
      lowJetSq (I := I) (M := M) g 2
          (lieArm1PsiB (I := I) (M := M) g gT g) ≤
        (P * (1 + A)) ^ 2 := by
    rw [psi_eq (I := I) (M := M) g gT]
    calc
      lowJetSq (I := I) (M := M) g 2
          (appCcRS (I := I) (M := M) g 1 1 2 LT ST) ≤
        Ca * lowJetSq (I := I) (M := M) g 2 LT *
          lowJetSq (I := I) (M := M) g 2 ST := by
            simpa only [LT, ST] using happ LT ST
      _ ≤ Ca * (Mb R0 * (1 + A)) ^ 2 * S0 := by
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left hLT hCa) hST
          (jet_nonneg (I := I) (M := M) g ST)
          (mul_nonneg hCa (sq_nonneg (Mb R0 * (1 + A))))
      _ = (P * (1 + A)) ^ 2 := by
        rw [← hHsq, ← hBssq]
        simp only [P]
        ring
  have hZ1 : 0 ≤ Z1 :=
    mul_nonneg
      (mul_nonneg hH
        (mul_nonneg (hMb R0 hR0) (by linarith)))
      (mul_nonneg hCs hN)
  have hXD : 0 ≤ XD :=
    add_nonneg
      (add_nonneg (mul_nonneg (hM0 R0 hR0) hD3)
        (mul_nonneg (hM1 R0 hR0) (mul_nonneg hCh hN)))
      (mul_nonneg
        (mul_nonneg (hM1 R0 hR0) hA)
        (mul_nonneg hCh hN))
  have hZ2 : 0 ≤ Z2 :=
    mul_nonneg (mul_nonneg hH hXD) hBs
  let V1 : SmoothCcTensor g 1 2 :=
    appCcRS (I := I) (M := M) g 1 1 2 LT (ST - SU)
  let V2 : SmoothCcTensor g 1 2 :=
    appCcRS (I := I) (M := M) g 1 1 2 (LT - LU) SU
  have hV1 :
      lowJetSq (I := I) (M := M) g 2 V1 ≤ Z1 ^ 2 := by
    calc
      lowJetSq (I := I) (M := M) g 2 V1 ≤
        Ca * lowJetSq (I := I) (M := M) g 2 LT *
          lowJetSq (I := I) (M := M) g 2 (ST - SU) := by
            simpa only [V1] using happ LT (ST - SU)
      _ ≤ Ca * (Mb R0 * (1 + A)) ^ 2 * (Cs * N) ^ 2 := by
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left hLT hCa) hSD
          (jet_nonneg (I := I) (M := M) g (ST - SU))
          (mul_nonneg hCa (sq_nonneg (Mb R0 * (1 + A))))
      _ = Z1 ^ 2 := by
        rw [← hHsq]
        simp only [Z1]
        ring
  have hV2 :
      lowJetSq (I := I) (M := M) g 2 V2 ≤ Z2 ^ 2 := by
    calc
      lowJetSq (I := I) (M := M) g 2 V2 ≤
        Ca * lowJetSq (I := I) (M := M) g 2 (LT - LU) *
          lowJetSq (I := I) (M := M) g 2 SU := by
            simpa only [V2] using happ (LT - LU) SU
      _ ≤ Ca * XD ^ 2 * S0 := by
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left hLD hCa) hSU
          (jet_nonneg (I := I) (M := M) g SU)
          (mul_nonneg hCa (sq_nonneg XD))
      _ = Z2 ^ 2 := by
        rw [← hHsq, ← hBssq]
        simp only [Z2]
        ring
  refine ⟨hPsiT, ?_⟩
  rw [psi_sub_eq (I := I) (M := M) g gT gU]
  change lowJetSq (I := I) (M := M) g 2 (V1 + V2) ≤ _
  calc
    lowJetSq (I := I) (M := M) g 2 (V1 + V2) ≤
        2 * (lowJetSq (I := I) (M := M) g 2 V1 +
          lowJetSq (I := I) (M := M) g 2 V2) :=
      jet_add1 (I := I) (M := M) g 2 V1 V2
    _ ≤ 2 * (Z1 ^ 2 + Z2 ^ 2) :=
      mul_le_mul_of_nonneg_left (add_le_add hV1 hV2) (by norm_num)
    _ ≤ (2 * (Z1 + Z2)) ^ 2 := by
      nlinarith [mul_nonneg hZ1 hZ2]
    _ = (B0 * D3 + B1 * N + B1 * A * N) ^ 2 := by
      simp only [B0, B1, Z1, Z2, XD]
      ring

set_option maxHeartbeats 1200000 in
private theorem jet14
    (g : SmoothRiemannianMetric I M) {r s : ℕ}
    (Q : ℝ)
    (Z0 Z1 Z2 Z3 Z4 Z5 Z6 Z7 Z8 Z9 Z10 Z11 Z12 Z13 :
      SmoothCcTensor g r s)
    (h0 : lowJetSq (I := I) (M := M) g 2 Z0 ≤ Q ^ 2)
    (h1 : lowJetSq (I := I) (M := M) g 2 Z1 ≤ Q ^ 2)
    (h2 : lowJetSq (I := I) (M := M) g 2 Z2 ≤ Q ^ 2)
    (h3 : lowJetSq (I := I) (M := M) g 2 Z3 ≤ Q ^ 2)
    (h4 : lowJetSq (I := I) (M := M) g 2 Z4 ≤ Q ^ 2)
    (h5 : lowJetSq (I := I) (M := M) g 2 Z5 ≤ Q ^ 2)
    (h6 : lowJetSq (I := I) (M := M) g 2 Z6 ≤ Q ^ 2)
    (h7 : lowJetSq (I := I) (M := M) g 2 Z7 ≤ Q ^ 2)
    (h8 : lowJetSq (I := I) (M := M) g 2 Z8 ≤ Q ^ 2)
    (h9 : lowJetSq (I := I) (M := M) g 2 Z9 ≤ Q ^ 2)
    (h10 : lowJetSq (I := I) (M := M) g 2 Z10 ≤ Q ^ 2)
    (h11 : lowJetSq (I := I) (M := M) g 2 Z11 ≤ Q ^ 2)
    (h12 : lowJetSq (I := I) (M := M) g 2 Z12 ≤ Q ^ 2)
    (h13 : lowJetSq (I := I) (M := M) g 2 Z13 ≤ Q ^ 2) :
    lowJetSq (I := I) (M := M) g 2
        (Z0 + (Z1 + Z2 - Z3 - Z4 - Z5 - Z6) +
          (Z7 + Z8 - Z9 - Z10 - Z11 - Z12) + Z13) ≤
      (47 * Q) ^ 2 := by
  let A12 : SmoothCcTensor g r s := Z1 + Z2
  let A123 : SmoothCcTensor g r s := A12 - Z3
  let A1234 : SmoothCcTensor g r s := A123 - Z4
  let A12345 : SmoothCcTensor g r s := A1234 - Z5
  let A1 : SmoothCcTensor g r s := A12345 - Z6
  let A78 : SmoothCcTensor g r s := Z7 + Z8
  let A789 : SmoothCcTensor g r s := A78 - Z9
  let A78910 : SmoothCcTensor g r s := A789 - Z10
  let A7891011 : SmoothCcTensor g r s := A78910 - Z11
  let A2 : SmoothCcTensor g r s := A7891011 - Z12
  let O1 : SmoothCcTensor g r s := Z0 + A1
  let O2 : SmoothCcTensor g r s := O1 + A2
  have hA12 :
      lowJetSq (I := I) (M := M) g 2 A12 ≤ (2 * Q) ^ 2 := by
    calc
      lowJetSq (I := I) (M := M) g 2 A12 ≤
          2 * (lowJetSq (I := I) (M := M) g 2 Z1 +
            lowJetSq (I := I) (M := M) g 2 Z2) := by
              simpa only [A12] using
                jet_add1 (I := I) (M := M) g 2 Z1 Z2
      _ ≤ 2 * (Q ^ 2 + Q ^ 2) :=
        mul_le_mul_of_nonneg_left (add_le_add h1 h2) (by norm_num)
      _ = (2 * Q) ^ 2 := by ring
  have hA123 :
      lowJetSq (I := I) (M := M) g 2 A123 ≤ (4 * Q) ^ 2 := by
    calc
      lowJetSq (I := I) (M := M) g 2 A123 ≤
          2 * (lowJetSq (I := I) (M := M) g 2 A12 +
            lowJetSq (I := I) (M := M) g 2 Z3) := by
              simpa only [A123] using
                jet_sub (I := I) (M := M) g 2 A12 Z3
      _ ≤ 2 * ((2 * Q) ^ 2 + Q ^ 2) :=
        mul_le_mul_of_nonneg_left (add_le_add hA12 h3) (by norm_num)
      _ ≤ (4 * Q) ^ 2 := by nlinarith [sq_nonneg Q]
  have hA1234 :
      lowJetSq (I := I) (M := M) g 2 A1234 ≤ (6 * Q) ^ 2 := by
    calc
      lowJetSq (I := I) (M := M) g 2 A1234 ≤
          2 * (lowJetSq (I := I) (M := M) g 2 A123 +
            lowJetSq (I := I) (M := M) g 2 Z4) := by
              simpa only [A1234] using
                jet_sub (I := I) (M := M) g 2 A123 Z4
      _ ≤ 2 * ((4 * Q) ^ 2 + Q ^ 2) :=
        mul_le_mul_of_nonneg_left (add_le_add hA123 h4) (by norm_num)
      _ ≤ (6 * Q) ^ 2 := by nlinarith [sq_nonneg Q]
  have hA12345 :
      lowJetSq (I := I) (M := M) g 2 A12345 ≤ (9 * Q) ^ 2 := by
    calc
      lowJetSq (I := I) (M := M) g 2 A12345 ≤
          2 * (lowJetSq (I := I) (M := M) g 2 A1234 +
            lowJetSq (I := I) (M := M) g 2 Z5) := by
              simpa only [A12345] using
                jet_sub (I := I) (M := M) g 2 A1234 Z5
      _ ≤ 2 * ((6 * Q) ^ 2 + Q ^ 2) :=
        mul_le_mul_of_nonneg_left (add_le_add hA1234 h5) (by norm_num)
      _ ≤ (9 * Q) ^ 2 := by nlinarith [sq_nonneg Q]
  have hA1 :
      lowJetSq (I := I) (M := M) g 2 A1 ≤ (13 * Q) ^ 2 := by
    calc
      lowJetSq (I := I) (M := M) g 2 A1 ≤
          2 * (lowJetSq (I := I) (M := M) g 2 A12345 +
            lowJetSq (I := I) (M := M) g 2 Z6) := by
              simpa only [A1] using
                jet_sub (I := I) (M := M) g 2 A12345 Z6
      _ ≤ 2 * ((9 * Q) ^ 2 + Q ^ 2) :=
        mul_le_mul_of_nonneg_left (add_le_add hA12345 h6) (by norm_num)
      _ ≤ (13 * Q) ^ 2 := by nlinarith [sq_nonneg Q]
  have hA78 :
      lowJetSq (I := I) (M := M) g 2 A78 ≤ (2 * Q) ^ 2 := by
    calc
      lowJetSq (I := I) (M := M) g 2 A78 ≤
          2 * (lowJetSq (I := I) (M := M) g 2 Z7 +
            lowJetSq (I := I) (M := M) g 2 Z8) := by
              simpa only [A78] using
                jet_add1 (I := I) (M := M) g 2 Z7 Z8
      _ ≤ 2 * (Q ^ 2 + Q ^ 2) :=
        mul_le_mul_of_nonneg_left (add_le_add h7 h8) (by norm_num)
      _ = (2 * Q) ^ 2 := by ring
  have hA789 :
      lowJetSq (I := I) (M := M) g 2 A789 ≤ (4 * Q) ^ 2 := by
    calc
      lowJetSq (I := I) (M := M) g 2 A789 ≤
          2 * (lowJetSq (I := I) (M := M) g 2 A78 +
            lowJetSq (I := I) (M := M) g 2 Z9) := by
              simpa only [A789] using
                jet_sub (I := I) (M := M) g 2 A78 Z9
      _ ≤ 2 * ((2 * Q) ^ 2 + Q ^ 2) :=
        mul_le_mul_of_nonneg_left (add_le_add hA78 h9) (by norm_num)
      _ ≤ (4 * Q) ^ 2 := by nlinarith [sq_nonneg Q]
  have hA78910 :
      lowJetSq (I := I) (M := M) g 2 A78910 ≤ (6 * Q) ^ 2 := by
    calc
      lowJetSq (I := I) (M := M) g 2 A78910 ≤
          2 * (lowJetSq (I := I) (M := M) g 2 A789 +
            lowJetSq (I := I) (M := M) g 2 Z10) := by
              simpa only [A78910] using
                jet_sub (I := I) (M := M) g 2 A789 Z10
      _ ≤ 2 * ((4 * Q) ^ 2 + Q ^ 2) :=
        mul_le_mul_of_nonneg_left (add_le_add hA789 h10) (by norm_num)
      _ ≤ (6 * Q) ^ 2 := by nlinarith [sq_nonneg Q]
  have hA7891011 :
      lowJetSq (I := I) (M := M) g 2 A7891011 ≤
        (9 * Q) ^ 2 := by
    calc
      lowJetSq (I := I) (M := M) g 2 A7891011 ≤
          2 * (lowJetSq (I := I) (M := M) g 2 A78910 +
            lowJetSq (I := I) (M := M) g 2 Z11) := by
              simpa only [A7891011] using
                jet_sub (I := I) (M := M) g 2 A78910 Z11
      _ ≤ 2 * ((6 * Q) ^ 2 + Q ^ 2) :=
        mul_le_mul_of_nonneg_left (add_le_add hA78910 h11) (by norm_num)
      _ ≤ (9 * Q) ^ 2 := by nlinarith [sq_nonneg Q]
  have hA2 :
      lowJetSq (I := I) (M := M) g 2 A2 ≤ (13 * Q) ^ 2 := by
    calc
      lowJetSq (I := I) (M := M) g 2 A2 ≤
          2 * (lowJetSq (I := I) (M := M) g 2 A7891011 +
            lowJetSq (I := I) (M := M) g 2 Z12) := by
              simpa only [A2] using
                jet_sub (I := I) (M := M) g 2 A7891011 Z12
      _ ≤ 2 * ((9 * Q) ^ 2 + Q ^ 2) :=
        mul_le_mul_of_nonneg_left (add_le_add hA7891011 h12) (by norm_num)
      _ ≤ (13 * Q) ^ 2 := by nlinarith [sq_nonneg Q]
  have hO1 :
      lowJetSq (I := I) (M := M) g 2 O1 ≤ (19 * Q) ^ 2 := by
    calc
      lowJetSq (I := I) (M := M) g 2 O1 ≤
          2 * (lowJetSq (I := I) (M := M) g 2 Z0 +
            lowJetSq (I := I) (M := M) g 2 A1) := by
              simpa only [O1] using
                jet_add1 (I := I) (M := M) g 2 Z0 A1
      _ ≤ 2 * (Q ^ 2 + (13 * Q) ^ 2) :=
        mul_le_mul_of_nonneg_left (add_le_add h0 hA1) (by norm_num)
      _ ≤ (19 * Q) ^ 2 := by nlinarith [sq_nonneg Q]
  have hO2 :
      lowJetSq (I := I) (M := M) g 2 O2 ≤ (33 * Q) ^ 2 := by
    calc
      lowJetSq (I := I) (M := M) g 2 O2 ≤
          2 * (lowJetSq (I := I) (M := M) g 2 O1 +
            lowJetSq (I := I) (M := M) g 2 A2) := by
              simpa only [O2] using
                jet_add1 (I := I) (M := M) g 2 O1 A2
      _ ≤ 2 * ((19 * Q) ^ 2 + (13 * Q) ^ 2) :=
        mul_le_mul_of_nonneg_left (add_le_add hO1 hA2) (by norm_num)
      _ ≤ (33 * Q) ^ 2 := by nlinarith [sq_nonneg Q]
  change lowJetSq (I := I) (M := M) g 2 (O2 + Z13) ≤ _
  calc
    lowJetSq (I := I) (M := M) g 2 (O2 + Z13) ≤
        2 * (lowJetSq (I := I) (M := M) g 2 O2 +
          lowJetSq (I := I) (M := M) g 2 Z13) :=
      jet_add1 (I := I) (M := M) g 2 O2 Z13
    _ ≤ 2 * ((33 * Q) ^ 2 + Q ^ 2) :=
      mul_le_mul_of_nonneg_left (add_le_add hO2 h13) (by norm_num)
    _ ≤ (47 * Q) ^ 2 := by nlinarith [sq_nonneg Q]

theorem connSec_self_h2
    (g gm : SmoothRiemannianMetric I M) :
    lowJetSq (I := I) (M := M) g 2
        (connDiffSection (I := I) gm g) =
      lowJetSq (I := I) (M := M) g 2
        (wXi (I := I) (M := M) g gm g) := by
  calc
    lowJetSq (I := I) (M := M) g 2
        (connDiffSection (I := I) gm g) =
      lowJetSq (I := I) (M := M) g 2
        (connDiffSection (I := I) gm g -
          connDiffSection (I := I) g g) := by
            rw [connSec_zero (I := I) (M := M) g, sub_zero]
    _ = lowJetSq (I := I) (M := M) g 2
        (connDiffLoweredCc (I := I) g gm -
          connDiffLoweredCc (I := I) g g) :=
      connSec_h2_eq (I := I) (M := M) g gm g
    _ = lowJetSq (I := I) (M := M) g 2
        (wXi (I := I) (M := M) g gm g) := rfl

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 4000000 in
set_option linter.unusedVariables false in
/-- On a sufficiently small spectral `H²` metric ball, the complete
order-one DeTurck Lie coefficient is Lipschitz with the critical
`H³/H²` two-arm modulus. -/
theorem lie1_pair_h2
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ B0 B1 : ℝ,
      0 < ρ ∧ 0 ≤ B0 ∧ 0 ≤ B1 ∧
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
        {δ : ℝ} (hδ_le : δ ≤ (1 : ℝ) / 3) (hδ0 : 0 ≤ δ)
        (hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδU : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g U) δ),
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ ≤ ρ →
        ∀ (A D3 : ℝ), 0 ≤ A → 0 ≤ D3 →
        lowJetSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
        lowJetSq (I := I) (M := M) g 3 (T - U) ≤ D3 ^ 2 →
      let D2 :=
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U)‖
      lowJetSq (I := I) (M := M) g 2
          (deTurckLieArm1Coeff (I := I) (M := M) g gT g -
            deTurckLieArm1Coeff (I := I) (M := M) g gU g) ≤
        (B0 * D3 + B1 * D2 + B1 * A * D2) ^ 2 := by
  obtain ⟨ρt, Ct, hρt, hCt, htracePair⟩ :=
    LowBaseInternal.trace2_pair_h2 (I := I) (M := M) hDim g
  obtain ⟨ρb, Tb, hρb, hTb, htraceBdd⟩ :=
    LowBaseInternal.trace2_h2_bdd (I := I) (M := M) hDim g
  obtain ⟨ρp, Pp, P0, P1, hρp, hPp, hP0, hP1, hpsi⟩ :=
    psi_pair_h2 (I := I) (M := M) hDim g
      (δ₀ := (1 : ℝ) / 3) (by norm_num) (by norm_num)
  obtain ⟨C0, C1, hC0, hC1, hconn⟩ :=
    connSec_sub_tame (I := I) (M := M) hDim g
      (δ₀ := (1 : ℝ) / 3) (by norm_num) (by norm_num)
  obtain ⟨Kw, hKw, hconnBdd⟩ :=
    wXi_h2_low (I := I) (M := M) g
      (δ₀ := (1 : ℝ) / 3) (by norm_num) (by norm_num)
  obtain ⟨Cp, hCp, hpiece⟩ :=
    liePiece_pair (I := I) (M := M) hDim g
  obtain ⟨Ch, hCh, hhs⟩ :=
    hs2_low2 (I := I) (M := M) g 2
  let ρ : ℝ := min ρt (min ρb ρp)
  let R0 : ℝ := Ch * ρ
  let Hw : ℝ := Real.sqrt Kw
  let LC0 : ℝ := Cp * Tb * C0 R0
  let LC1 : ℝ := Cp * (Tb * C1 R0 * Ch + Ct * Hw)
  let LP0 : ℝ := Cp * Tb * P0
  let LP1 : ℝ := Cp * (Tb * P1 + Ct * Pp)
  let B0 : ℝ := 47 * (LC0 + LP0)
  let B1 : ℝ := 47 * (LC1 + LP1)
  have hρ : 0 < ρ := lt_min hρt (lt_min hρb hρp)
  have hR0 : 0 ≤ R0 := mul_nonneg hCh hρ.le
  have hHw : 0 ≤ Hw := Real.sqrt_nonneg _
  have hHwsq : Hw ^ 2 = Kw := by
    simpa only [Hw] using Real.sq_sqrt hKw
  have hLC0 : 0 ≤ LC0 :=
    mul_nonneg (mul_nonneg hCp hTb) (hC0 R0 hR0)
  have hLC1 : 0 ≤ LC1 :=
    mul_nonneg hCp
      (add_nonneg
        (mul_nonneg (mul_nonneg hTb (hC1 R0 hR0)) hCh)
        (mul_nonneg hCt hHw))
  have hLP0 : 0 ≤ LP0 := mul_nonneg (mul_nonneg hCp hTb) hP0
  have hLP1 : 0 ≤ LP1 :=
    mul_nonneg hCp
      (add_nonneg (mul_nonneg hTb hP1) (mul_nonneg hCt hPp))
  have hB0 : 0 ≤ B0 :=
    mul_nonneg (by norm_num) (add_nonneg hLC0 hLP0)
  have hB1 : 0 ≤ B1 :=
    mul_nonneg (by norm_num) (add_nonneg hLC1 hLP1)
  refine ⟨ρ, B0, B1, hρ, hB0, hB1, ?_⟩
  intro gT gU T U hT hU hTtie hUtie
    δ hδ_le hδ0 hδT hδU hTHs hUHs
    A D3 hA hD3 hT3 hTU3
  dsimp only
  let N : ℝ :=
    ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U)‖
  let CT : SmoothCcTensor g 1 2 := connDiffSection (I := I) gT g
  let CU : SmoothCcTensor g 1 2 := connDiffSection (I := I) gU g
  let PT : SmoothCcTensor g 1 2 :=
    lieArm1PsiB (I := I) (M := M) g gT g
  let PU : SmoothCcTensor g 1 2 :=
    lieArm1PsiB (I := I) (M := M) g gU g
  let XC : ℝ := C0 R0 * D3 +
    C1 R0 * (Ch * N) + C1 R0 * A * (Ch * N)
  let XP : ℝ := P0 * D3 + P1 * N + P1 * A * N
  let YC : ℝ := Cp *
    (Tb * XC + (Ct * N) * (Hw * (1 + A)))
  let YP : ℝ := Cp *
    (Tb * XP + (Ct * N) * (Pp * (1 + A)))
  have hN : 0 ≤ N := norm_nonneg _
  have hTHst : ‖ccTensorToHs (I := I) (M := M) g 2
      (2 : ℝ) T‖ ≤ ρt := hTHs.trans (min_le_left _ _)
  have hUHst : ‖ccTensorToHs (I := I) (M := M) g 2
      (2 : ℝ) U‖ ≤ ρt := hUHs.trans (min_le_left _ _)
  have hTHsb : ‖ccTensorToHs (I := I) (M := M) g 2
      (2 : ℝ) T‖ ≤ ρb :=
    hTHs.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hUHsb : ‖ccTensorToHs (I := I) (M := M) g 2
      (2 : ℝ) U‖ ≤ ρb :=
    hUHs.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hTHsp : ‖ccTensorToHs (I := I) (M := M) g 2
      (2 : ℝ) T‖ ≤ ρp :=
    hTHs.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hUHsp : ‖ccTensorToHs (I := I) (M := M) g 2
      (2 : ℝ) U‖ ≤ ρp :=
    hUHs.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hT2 :
      lowJetSq (I := I) (M := M) g 2 T ≤ R0 ^ 2 := by
    calc
      lowJetSq (I := I) (M := M) g 2 T ≤
          (Ch * ‖ccTensorToHs (I := I) (M := M) g 2
            (2 : ℝ) T‖) ^ 2 := by
        simpa only [lowJetSq, Nat.reduceAdd] using hhs T
      _ ≤ (Ch * ρ) ^ 2 :=
        pow_le_pow_left₀
          (mul_nonneg hCh (norm_nonneg _))
          (mul_le_mul_of_nonneg_left hTHs hCh) 2
      _ = R0 ^ 2 := rfl
  have hU2 :
      lowJetSq (I := I) (M := M) g 2 U ≤ R0 ^ 2 := by
    calc
      lowJetSq (I := I) (M := M) g 2 U ≤
          (Ch * ‖ccTensorToHs (I := I) (M := M) g 2
            (2 : ℝ) U‖) ^ 2 := by
        simpa only [lowJetSq, Nat.reduceAdd] using hhs U
      _ ≤ (Ch * ρ) ^ 2 :=
        pow_le_pow_left₀
          (mul_nonneg hCh (norm_nonneg _))
          (mul_le_mul_of_nonneg_left hUHs hCh) 2
      _ = R0 ^ 2 := rfl
  have hTU2 :
      lowJetSq (I := I) (M := M) g 2 (T - U) ≤
        (Ch * N) ^ 2 := by
    simpa only [lowJetSq, Nat.reduceAdd, N] using hhs (T - U)
  have hTrU : ∀ σ : Equiv.Perm (Fin 4),
      lowJetSq (I := I) (M := M) g 2
          (deTurckLieTraceCoeff (I := I) (M := M) g gU σ) ≤
        Tb ^ 2 := by
    intro σ
    rw [lieTrace_eq (I := I) (M := M) g gU σ,
      reindex_h2_eq (I := I) (M := M)]
    exact htraceBdd U gU hUtie hUHsb
  have hTrD : ∀ σ : Equiv.Perm (Fin 4),
      lowJetSq (I := I) (M := M) g 2
          (deTurckLieTraceCoeff (I := I) (M := M) g gT σ -
            deTurckLieTraceCoeff (I := I) (M := M) g gU σ) ≤
        (Ct * N) ^ 2 := by
    intro σ
    have heq :
        deTurckLieTraceCoeff (I := I) (M := M) g gT σ -
            deTurckLieTraceCoeff (I := I) (M := M) g gU σ =
          reindexCoeffGen (I := I) (M := M) g 4 2
            (pureTrace (I := I) (M := M) g gT 2 -
              pureTrace (I := I) (M := M) g gU 2) σ := by
      rw [lieTrace_eq (I := I) (M := M) g gT σ,
        lieTrace_eq (I := I) (M := M) g gU σ,
        reindex_sub (I := I) (M := M) g 4 2]
    rw [heq, reindex_h2_eq (I := I) (M := M)]
    simpa only [N] using
      htracePair T U gT gU hTtie hUtie hTHst hUHst
  have hCT :
      lowJetSq (I := I) (M := M) g 2 CT ≤
        (Hw * (1 + A)) ^ 2 := by
    rw [show lowJetSq (I := I) (M := M) g 2 CT =
        lowJetSq (I := I) (M := M) g 2
          (wXi (I := I) (M := M) g gT g) by
      simpa only [CT] using
        connSec_self_h2 (I := I) (M := M) g gT]
    calc
      lowJetSq (I := I) (M := M) g 2
          (wXi (I := I) (M := M) g gT g) ≤
        Kw * (1 + lowJetSq (I := I) (M := M) g 3 T) :=
          hconnBdd gT T hT hTtie hδ_le hδ0 hδT
      _ ≤ Kw * (1 + A ^ 2) :=
        mul_le_mul_of_nonneg_left (add_le_add le_rfl hT3) hKw
      _ = Hw ^ 2 * (1 + A ^ 2) := by rw [hHwsq]
      _ ≤ Hw ^ 2 * (1 + A) ^ 2 := by
        apply mul_le_mul_of_nonneg_left _ (sq_nonneg Hw)
        nlinarith
      _ = (Hw * (1 + A)) ^ 2 := by ring
  have hCD :
      lowJetSq (I := I) (M := M) g 2 (CT - CU) ≤ XC ^ 2 := by
    simpa only [CT, CU, XC] using
      hconn gT gU T U hT hU hTtie hUtie
        hδ_le hδ0 hδT hδ_le hδ0 hδU
        R0 A (Ch * N) D3 hR0 hA (mul_nonneg hCh hN) hD3
        hU2 hT3 hTU2 hTU3
  have hPsiRaw := hpsi gT gU T U hT hU hTtie hUtie
    hδ_le hδ0 hδT hδ_le hδ0 hδU
    hTHsp hUHsp A D3 hA hD3 hT3 hTU3
  have hPT :
      lowJetSq (I := I) (M := M) g 2 PT ≤
        (Pp * (1 + A)) ^ 2 := by
    simpa only [PT] using hPsiRaw.1
  have hPD :
      lowJetSq (I := I) (M := M) g 2 (PT - PU) ≤ XP ^ 2 := by
    simpa only [PT, PU, XP, N] using hPsiRaw.2
  have hXC : 0 ≤ XC :=
    add_nonneg
      (add_nonneg (mul_nonneg (hC0 R0 hR0) hD3)
        (mul_nonneg (hC1 R0 hR0) (mul_nonneg hCh hN)))
      (mul_nonneg
        (mul_nonneg (hC1 R0 hR0) hA)
        (mul_nonneg hCh hN))
  have hXP : 0 ≤ XP :=
    add_nonneg
      (add_nonneg (mul_nonneg hP0 hD3) (mul_nonneg hP1 hN))
      (mul_nonneg (mul_nonneg hP1 hA) hN)
  have hYC : 0 ≤ YC :=
    mul_nonneg hCp
      (add_nonneg (mul_nonneg hTb hXC)
        (mul_nonneg (mul_nonneg hCt hN)
          (mul_nonneg hHw (by linarith))))
  have hYP : 0 ≤ YP :=
    mul_nonneg hCp
      (add_nonneg (mul_nonneg hTb hXP)
        (mul_nonneg (mul_nonneg hCt hN)
          (mul_nonneg hPp (by linarith))))
  have hConnPiece : ∀ (σ : Equiv.Perm (Fin 4))
      (r : Equiv.Perm (Fin 3)),
      lowJetSq (I := I) (M := M) g 2
          (lieArm1Piece (I := I) (M := M) g gT σ r CT -
            lieArm1Piece (I := I) (M := M) g gU σ r CU) ≤
        YC ^ 2 := by
    intro σ r
    simpa only [YC] using
      hpiece gT gU σ r CT CU
        Tb (Ct * N) (Hw * (1 + A)) XC
        hTb (mul_nonneg hCt hN)
        (mul_nonneg hHw (by linarith)) hXC
        (hTrU σ) (hTrD σ) hCT hCD
  have hPsiPiece : ∀ (σ : Equiv.Perm (Fin 4))
      (r : Equiv.Perm (Fin 3)),
      lowJetSq (I := I) (M := M) g 2
          (lieArm1Piece (I := I) (M := M) g gT σ r PT -
            lieArm1Piece (I := I) (M := M) g gU σ r PU) ≤
        YP ^ 2 := by
    intro σ r
    simpa only [YP] using
      hpiece gT gU σ r PT PU
        Tb (Ct * N) (Pp * (1 + A)) XP
        hTb (mul_nonneg hCt hN)
        (mul_nonneg hPp (by linarith)) hXP
        (hTrU σ) (hTrD σ) hPT hPD
  have hBgPiece : ∀ (σ : Equiv.Perm (Fin 4))
      (r : Equiv.Perm (Fin 3)),
      lowJetSq (I := I) (M := M) g 2
          (lieArm1Piece (I := I) (M := M) g gT σ r
              (lieArm1ConnDiffBgCc (I := I) (M := M) g gT g) -
            lieArm1Piece (I := I) (M := M) g gU σ r
              (lieArm1ConnDiffBgCc (I := I) (M := M) g gU g)) ≤
        YC ^ 2 := by
    intro σ r
    simpa only [CT, CU, connBg_eq (I := I) (M := M)] using
      hConnPiece σ r
  let Z0 : SmoothCcTensor g 3 2 :=
    lieArm1Piece (I := I) (M := M) g gT lieArm1SigmaC
        lieArm1RhoSlot0
        (lieArm1ConnDiffBgCc (I := I) (M := M) g gT g) -
      lieArm1Piece (I := I) (M := M) g gU lieArm1SigmaC
        lieArm1RhoSlot0
        (lieArm1ConnDiffBgCc (I := I) (M := M) g gU g)
  let Z1 : SmoothCcTensor g 3 2 :=
    lieArm1Piece (I := I) (M := M) g gT lieArm1SigmaA
        (Equiv.refl (Fin 3)) CT -
      lieArm1Piece (I := I) (M := M) g gU lieArm1SigmaA
        (Equiv.refl (Fin 3)) CU
  let Z2 : SmoothCcTensor g 3 2 :=
    lieArm1Piece (I := I) (M := M) g gT lieArm1SigmaA
        (Equiv.refl (Fin 3)) PT -
      lieArm1Piece (I := I) (M := M) g gU lieArm1SigmaA
        (Equiv.refl (Fin 3)) PU
  let Z3 : SmoothCcTensor g 3 2 :=
    lieArm1Piece (I := I) (M := M) g gT lieArm1SigmaC
        (Equiv.refl (Fin 3)) CT -
      lieArm1Piece (I := I) (M := M) g gU lieArm1SigmaC
        (Equiv.refl (Fin 3)) CU
  let Z4 : SmoothCcTensor g 3 2 :=
    lieArm1Piece (I := I) (M := M) g gT lieArm1SigmaD
        lieArm1RhoSlot0 CT -
      lieArm1Piece (I := I) (M := M) g gU lieArm1SigmaD
        lieArm1RhoSlot0 CU
  let Z5 : SmoothCcTensor g 3 2 :=
    lieArm1Piece (I := I) (M := M) g gT (Equiv.refl (Fin 4))
        lieArm1RhoSlot1 CT -
      lieArm1Piece (I := I) (M := M) g gU (Equiv.refl (Fin 4))
        lieArm1RhoSlot1 CU
  let Z6 : SmoothCcTensor g 3 2 :=
    lieArm1Piece (I := I) (M := M) g gT lieArm1SigmaF
        (Equiv.refl (Fin 3)) CT -
      lieArm1Piece (I := I) (M := M) g gU lieArm1SigmaF
        (Equiv.refl (Fin 3)) CU
  let Z7 : SmoothCcTensor g 3 2 :=
    lieArm1Piece (I := I) (M := M) g gT lieArm1SigmaASwap
        (Equiv.refl (Fin 3)) CT -
      lieArm1Piece (I := I) (M := M) g gU lieArm1SigmaASwap
        (Equiv.refl (Fin 3)) CU
  let Z8 : SmoothCcTensor g 3 2 :=
    lieArm1Piece (I := I) (M := M) g gT lieArm1SigmaASwap
        (Equiv.refl (Fin 3)) PT -
      lieArm1Piece (I := I) (M := M) g gU lieArm1SigmaASwap
        (Equiv.refl (Fin 3)) PU
  let Z9 : SmoothCcTensor g 3 2 :=
    lieArm1Piece (I := I) (M := M) g gT lieArm1SigmaCSwap
        (Equiv.refl (Fin 3)) CT -
      lieArm1Piece (I := I) (M := M) g gU lieArm1SigmaCSwap
        (Equiv.refl (Fin 3)) CU
  let Z10 : SmoothCcTensor g 3 2 :=
    lieArm1Piece (I := I) (M := M) g gT lieArm1SigmaDSwap
        lieArm1RhoSlot0 CT -
      lieArm1Piece (I := I) (M := M) g gU lieArm1SigmaDSwap
        lieArm1RhoSlot0 CU
  let Z11 : SmoothCcTensor g 3 2 :=
    lieArm1Piece (I := I) (M := M) g gT lieArm1SigmaESwap
        lieArm1RhoSlot1 CT -
      lieArm1Piece (I := I) (M := M) g gU lieArm1SigmaESwap
        lieArm1RhoSlot1 CU
  let Z12 : SmoothCcTensor g 3 2 :=
    lieArm1Piece (I := I) (M := M) g gT lieArm1SigmaFSwap
        (Equiv.refl (Fin 3)) CT -
      lieArm1Piece (I := I) (M := M) g gU lieArm1SigmaFSwap
        (Equiv.refl (Fin 3)) CU
  let Z13 : SmoothCcTensor g 3 2 :=
    lieArm1Piece (I := I) (M := M) g gT (Equiv.refl (Fin 4))
        lieArm1RhoSlot0 CT -
      lieArm1Piece (I := I) (M := M) g gU (Equiv.refl (Fin 4))
        lieArm1RhoSlot0 CU
  let Q : ℝ := YC + YP
  have hQ : 0 ≤ Q := add_nonneg hYC hYP
  have hCQ : YC ^ 2 ≤ Q ^ 2 :=
    pow_le_pow_left₀ hYC (by dsimp only [Q]; linarith) 2
  have hPQ : YP ^ 2 ≤ Q ^ 2 :=
    pow_le_pow_left₀ hYP (by dsimp only [Q]; linarith) 2
  have hZ0 :
      lowJetSq (I := I) (M := M) g 2 Z0 ≤ Q ^ 2 :=
    (hBgPiece lieArm1SigmaC lieArm1RhoSlot0).trans hCQ
  have hZ1 :
      lowJetSq (I := I) (M := M) g 2 Z1 ≤ Q ^ 2 :=
    (hConnPiece lieArm1SigmaA (Equiv.refl (Fin 3))).trans hCQ
  have hZ2 :
      lowJetSq (I := I) (M := M) g 2 Z2 ≤ Q ^ 2 :=
    (hPsiPiece lieArm1SigmaA (Equiv.refl (Fin 3))).trans hPQ
  have hZ3 :
      lowJetSq (I := I) (M := M) g 2 Z3 ≤ Q ^ 2 :=
    (hConnPiece lieArm1SigmaC (Equiv.refl (Fin 3))).trans hCQ
  have hZ4 :
      lowJetSq (I := I) (M := M) g 2 Z4 ≤ Q ^ 2 :=
    (hConnPiece lieArm1SigmaD lieArm1RhoSlot0).trans hCQ
  have hZ5 :
      lowJetSq (I := I) (M := M) g 2 Z5 ≤ Q ^ 2 :=
    (hConnPiece (Equiv.refl (Fin 4)) lieArm1RhoSlot1).trans hCQ
  have hZ6 :
      lowJetSq (I := I) (M := M) g 2 Z6 ≤ Q ^ 2 :=
    (hConnPiece lieArm1SigmaF (Equiv.refl (Fin 3))).trans hCQ
  have hZ7 :
      lowJetSq (I := I) (M := M) g 2 Z7 ≤ Q ^ 2 :=
    (hConnPiece lieArm1SigmaASwap (Equiv.refl (Fin 3))).trans hCQ
  have hZ8 :
      lowJetSq (I := I) (M := M) g 2 Z8 ≤ Q ^ 2 :=
    (hPsiPiece lieArm1SigmaASwap (Equiv.refl (Fin 3))).trans hPQ
  have hZ9 :
      lowJetSq (I := I) (M := M) g 2 Z9 ≤ Q ^ 2 :=
    (hConnPiece lieArm1SigmaCSwap (Equiv.refl (Fin 3))).trans hCQ
  have hZ10 :
      lowJetSq (I := I) (M := M) g 2 Z10 ≤ Q ^ 2 :=
    (hConnPiece lieArm1SigmaDSwap lieArm1RhoSlot0).trans hCQ
  have hZ11 :
      lowJetSq (I := I) (M := M) g 2 Z11 ≤ Q ^ 2 :=
    (hConnPiece lieArm1SigmaESwap lieArm1RhoSlot1).trans hCQ
  have hZ12 :
      lowJetSq (I := I) (M := M) g 2 Z12 ≤ Q ^ 2 :=
    (hConnPiece lieArm1SigmaFSwap (Equiv.refl (Fin 3))).trans hCQ
  have hZ13 :
      lowJetSq (I := I) (M := M) g 2 Z13 ≤ Q ^ 2 :=
    (hConnPiece (Equiv.refl (Fin 4)) lieArm1RhoSlot0).trans hCQ
  have hdecomp :
      deTurckLieArm1Coeff (I := I) (M := M) g gT g -
          deTurckLieArm1Coeff (I := I) (M := M) g gU g =
        Z0 + (Z1 + Z2 - Z3 - Z4 - Z5 - Z6) +
          (Z7 + Z8 - Z9 - Z10 - Z11 - Z12) + Z13 := by
    rw [deTurckLieArm1Coeff_eq_lieArm1Piece_sum
        (I := I) (M := M) g gT g,
      deTurckLieArm1Coeff_eq_lieArm1Piece_sum
        (I := I) (M := M) g gU g]
    dsimp only [Z0, Z1, Z2, Z3, Z4, Z5, Z6, Z7, Z8, Z9,
      Z10, Z11, Z12, Z13, CT, CU, PT, PU]
    module
  have hYCeq :
      YC = LC0 * D3 + LC1 * N + LC1 * A * N := by
    simp only [YC, XC, LC0, LC1]
    ring
  have hYPeq :
      YP = LP0 * D3 + LP1 * N + LP1 * A * N := by
    simp only [YP, XP, LP0, LP1]
    ring
  rw [hdecomp]
  calc
    lowJetSq (I := I) (M := M) g 2
        (Z0 + (Z1 + Z2 - Z3 - Z4 - Z5 - Z6) +
          (Z7 + Z8 - Z9 - Z10 - Z11 - Z12) + Z13) ≤
      (47 * Q) ^ 2 :=
        jet14 (I := I) (M := M) g Q
          Z0 Z1 Z2 Z3 Z4 Z5 Z6 Z7 Z8 Z9 Z10 Z11 Z12 Z13
          hZ0 hZ1 hZ2 hZ3 hZ4 hZ5 hZ6 hZ7 hZ8 hZ9 hZ10 hZ11 hZ12 hZ13
    _ = (47 * ((LC0 + LP0) * D3 +
          (LC1 + LP1) * N + (LC1 + LP1) * A * N)) ^ 2 := by
      rw [show Q = (LC0 + LP0) * D3 +
          (LC1 + LP1) * N + (LC1 + LP1) * A * N by
        dsimp only [Q]
        rw [hYCeq, hYPeq]
        ring]
    _ = (B0 * D3 + B1 * N + B1 * A * N) ^ 2 := by
      rw [show B0 = 47 * (LC0 + LP0) by rfl,
        show B1 = 47 * (LC1 + LP1) by rfl]
      ring

set_option maxHeartbeats 1800000 in
set_option synthInstance.maxHeartbeats 1800000 in
set_option linter.unusedVariables false in
/-- On a common small spectral `H²` ball, the complete order-one
Ricci--DeTurck coefficient has the critical `H³/H²` two-arm modulus. -/
theorem rhs1_pair_h2
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ B0 B1 : ℝ,
      0 < ρ ∧ 0 ≤ B0 ∧ 0 ≤ B1 ∧
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
      let D2 :=
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U)‖
      lowJetSq (I := I) (M := M) g 2
          ((-2 : ℝ) •
              (linearizedRicciConnDiffOrder1CoeffField
                  (I := I) (M := M) g gT -
                linearizedRicciConnDiffOrder1CoeffField
                  (I := I) (M := M) g gU) +
            (deTurckLieArm1Coeff (I := I) (M := M) g gT g -
              deTurckLieArm1Coeff (I := I) (M := M) g gU g)) ≤
        (B0 * D3 + B1 * D2 + B1 * A * D2) ^ 2 := by
  obtain ⟨ρr, R0, R1, hρr, hR0, hR1, hricci⟩ :=
    ricci1_pair_h2 (I := I) (M := M) hDim g
  obtain ⟨ρl, L0, L1, hρl, hL0, hL1, hlie⟩ :=
    lie1_pair_h2 (I := I) (M := M) hDim g
  let ρ : ℝ := min ρr ρl
  let B0 : ℝ := 4 * R0 + 2 * L0
  let B1 : ℝ := 4 * R1 + 2 * L1
  have hρ : 0 < ρ := lt_min hρr hρl
  have hB0 : 0 ≤ B0 :=
    add_nonneg (mul_nonneg (by norm_num) hR0)
      (mul_nonneg (by norm_num) hL0)
  have hB1 : 0 ≤ B1 :=
    add_nonneg (mul_nonneg (by norm_num) hR1)
      (mul_nonneg (by norm_num) hL1)
  refine ⟨ρ, B0, B1, hρ, hB0, hB1, ?_⟩
  intro gT gU T U hT hU hTtie hUtie
    δ hδ_le hδ0 hδT hδU hδZ hTHs hUHs
    A D3 hA hD3 hT3 hTU3
  dsimp only
  let N : ℝ :=
    ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U)‖
  let XR : ℝ := R0 * D3 + R1 * N + R1 * A * N
  let XL : ℝ := L0 * D3 + L1 * N + L1 * A * N
  let VR : SmoothCcTensor g 3 2 :=
    linearizedRicciConnDiffOrder1CoeffField
        (I := I) (M := M) g gT -
      linearizedRicciConnDiffOrder1CoeffField
        (I := I) (M := M) g gU
  let VL : SmoothCcTensor g 3 2 :=
    deTurckLieArm1Coeff (I := I) (M := M) g gT g -
      deTurckLieArm1Coeff (I := I) (M := M) g gU g
  have hN : 0 ≤ N := norm_nonneg _
  have hXR : 0 ≤ XR :=
    add_nonneg
      (add_nonneg (mul_nonneg hR0 hD3) (mul_nonneg hR1 hN))
      (mul_nonneg (mul_nonneg hR1 hA) hN)
  have hXL : 0 ≤ XL :=
    add_nonneg
      (add_nonneg (mul_nonneg hL0 hD3) (mul_nonneg hL1 hN))
      (mul_nonneg (mul_nonneg hL1 hA) hN)
  have hVR :
      lowJetSq (I := I) (M := M) g 2 VR ≤ XR ^ 2 := by
    simpa only [VR, XR, N] using
      hricci gT gU T U hT hU hTtie hUtie
        hδ_le hδ0 hδT hδU hδZ
        (hTHs.trans (min_le_left _ _))
        (hUHs.trans (min_le_left _ _))
        A D3 hA hD3 hT3 hTU3
  have hVL :
      lowJetSq (I := I) (M := M) g 2 VL ≤ XL ^ 2 := by
    simpa only [VL, XL, N] using
      hlie gT gU T U hT hU hTtie hUtie
        hδ_le hδ0 hδT hδU
        (hTHs.trans (min_le_right _ _))
        (hUHs.trans (min_le_right _ _))
        A D3 hA hD3 hT3 hTU3
  have hRicS :
      lowJetSq (I := I) (M := M) g 2 ((-2 : ℝ) • VR) ≤
        (2 * XR) ^ 2 := by
    rw [jet_smul1 (I := I) (M := M) g 2]
    nlinarith
  change lowJetSq (I := I) (M := M) g 2
      ((-2 : ℝ) • VR + VL) ≤ _
  calc
    lowJetSq (I := I) (M := M) g 2
        ((-2 : ℝ) • VR + VL) ≤
      2 * (lowJetSq (I := I) (M := M) g 2 ((-2 : ℝ) • VR) +
        lowJetSq (I := I) (M := M) g 2 VL) :=
      jet_add1 (I := I) (M := M) g 2 ((-2 : ℝ) • VR) VL
    _ ≤ 2 * ((2 * XR) ^ 2 + XL ^ 2) :=
      mul_le_mul_of_nonneg_left (add_le_add hRicS hVL) (by norm_num)
    _ ≤ (2 * (2 * XR + XL)) ^ 2 := by
      nlinarith [sq_nonneg XR, sq_nonneg XL, mul_nonneg hXR hXL]
    _ = (B0 * D3 + B1 * N + B1 * A * N) ^ 2 := by
      simp only [B0, B1, XR, XL]
      ring

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
