import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciArmResidualCoefficientFields
import DifferentialGeometry.Geometry.Connection.TensorNabla.OperatorFieldInputSlotSymmetrization
import DifferentialGeometry.Analysis.Sobolev.BoundedFactorProductGrid
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.MetricArmCoeffJetTower
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.FlatArmCoeffConnectionDifferenceBridge
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.RicciArmResidualFieldGridWindowGInvQuadResidual

noncomputable section

set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open Bundle Manifold Set Filter Tensor0SBundle MeasureTheory
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck
open DifferentialGeometry.PDE.DeTurck.RicciLinearization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

private theorem iteratedCovGrad_smul_real (g : SmoothRiemannianMetric I M) (r s j : ℕ) (c : ℝ)
    (w : SmoothCcTensor g r s) :
    iteratedCovGrad (I := I) g r s j (c • w) = c • iteratedCovGrad (I := I) g r s j w := by
  induction j with
  | zero => simp only [iteratedCovGrad_zero]
  | succ j ih => rw [iteratedCovGrad_succ, iteratedCovGrad_succ, ih,
      DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covGrad_smul]

set_option linter.unusedSectionVars false in
private lemma riemannianFiberNormSq_smul_value (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (x : M) (c : ℝ) (v : TensorRSSpace r s I x) :
    riemannianFiberNormSq (I := I) (M := M) g r s x (c • v) =
      c ^ 2 * riemannianFiberNormSq (I := I) (M := M) g r s x v := by
  rw [riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g r s x (c • v),
    riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g r s x v]
  rw [TensorRSSpace.toModel_smul, tensorInnerPointwise_smul_left,
    tensorInnerPointwise_smul_right]
  ring

section bgrConversion

open DifferentialGeometry.Analysis.Sobolev.TensorHilbert

variable (g₀ g₁ : SmoothRiemannianMetric I M)

set_option linter.unusedSectionVars false in
private lemma unitModel_add_pt (s : ℕ) (A B : SmoothCcTensor g₀ 0 s) (x : M) :
    unitModel (I := I) (M := M) g₀ s (A + B) x =
      unitModel (I := I) (M := M) g₀ s A x + unitModel (I := I) (M := M) g₀ s B x := by
  rw [unitModel, unitModel, unitModel,
    show (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from (A + B).toSection x) =
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from A.toSection x) +
        (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from B.toSection x) from by
      rw [SmoothCcTensor.toSection_add]; rfl]
  rw [ContinuousLinearMap.add_apply, Tensor0SSpace.toModel_add]

set_option linter.unusedSectionVars false in
private lemma unitModel_smul_pt (s : ℕ) (c : ℝ) (A : SmoothCcTensor g₀ 0 s) (x : M) :
    unitModel (I := I) (M := M) g₀ s (c • A) x =
      c • unitModel (I := I) (M := M) g₀ s A x := by
  have h : ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from (c • A).toSection x)
      (unitTensor (I := I) (M := M) x)) =
      c • ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from A.toSection x)
        (unitTensor (I := I) (M := M) x)) := by
    rw [show ((c • A).toSection x) = c • (A.toSection x) from by
      rw [SmoothCcTensor.toSection_smul]; rfl]
    rfl
  rw [unitModel, unitModel, h, Tensor0SSpace.toModel_smul]

set_option linter.unusedSectionVars false in
lemma unitModel_sub_pt (s : ℕ) (A B : SmoothCcTensor g₀ 0 s) (x : M) :
    unitModel (I := I) (M := M) g₀ s (A - B) x =
      unitModel (I := I) (M := M) g₀ s A x - unitModel (I := I) (M := M) g₀ s B x := by
  have h : ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from (A - B).toSection x)
      (unitTensor (I := I) (M := M) x)) =
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from A.toSection x)
          (unitTensor (I := I) (M := M) x) -
        (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from B.toSection x)
          (unitTensor (I := I) (M := M) x) := by
    rw [show ((A - B).toSection x) = A.toSection x - B.toSection x from by
      rw [SmoothCcTensor.toSection_sub]; rfl]
    rfl
  rw [unitModel, unitModel, unitModel, h, Tensor0SSpace.toModel_sub]

set_option linter.unusedSectionVars false in
private lemma rfns_neg_pt (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (v : TensorRSSpace r s I x) :
    riemannianFiberNormSq (I := I) (M := M) g r s x (-v) =
      riemannianFiberNormSq (I := I) (M := M) g r s x v := by
  have h := riemannianFiberNormSq_smul_value (I := I) (M := M) g r s x (-1 : ℝ) v
  rw [neg_one_smul] at h
  rw [h]; norm_num

set_option linter.unusedVariables false in
set_option linter.unusedSectionVars false in
private lemma toModel_cons_sum_smul (x : M) {n : ℕ}
    (Zm : Tensor0SModel (n + 1) ℝ E) (d : ℕ) (t : Fin d → ℝ)
    (u : Fin d → E) (rest : Fin n → E) :
    Zm (Fin.cons (∑ c, t c • u c) rest) =
      ∑ c, t c * Zm (Fin.cons (u c) rest) := by
  classical
  have h1 : ∀ v : E, (Fin.cons v rest : Fin (n + 1) → E) =
      Function.update (Fin.cons (0 : E) rest) 0 v := by
    intro v
    rw [Fin.update_cons_zero]
  have hgen : ∀ ss : Finset (Fin d),
      Zm (Function.update (Fin.cons (0 : E) rest) 0 (∑ c ∈ ss, t c • u c)) =
        ∑ c ∈ ss, t c * Zm (Function.update (Fin.cons (0 : E) rest) 0 (u c)) := by
    intro ss
    induction ss using Finset.induction_on with
    | empty =>
        rw [Finset.sum_empty, Finset.sum_empty]
        rw [show (0 : E) = ((0 : ℝ) • (0 : E)) from (zero_smul ℝ (0 : E)).symm]
        rw [ContinuousMultilinearMap.map_update_smul]
        rw [zero_smul]
    | @insert a ss ha ih =>
        rw [Finset.sum_insert ha, Finset.sum_insert ha]
        rw [ContinuousMultilinearMap.map_update_add]
        rw [ih]
        congr 1
        rw [ContinuousMultilinearMap.map_update_smul]
        rw [smul_eq_mul]
  have h2 := hgen Finset.univ
  rw [h1, h2]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← h1 (u c)]

set_option linter.unusedVariables false in
set_option linter.unusedSectionVars false in
private lemma toModel_cons_cons_sum_smul (x : M) {n : ℕ}
    (Zm : Tensor0SModel (n + 2) ℝ E) (aa : E) (d : ℕ) (t : Fin d → ℝ)
    (u : Fin d → E) (rest : Fin n → E) :
    Zm (Fin.cons aa (Fin.cons (∑ c, t c • u c) rest)) =
      ∑ c, t c * Zm (Fin.cons aa (Fin.cons (u c) rest)) := by
  classical
  have h1 : ∀ v : E, (Fin.cons aa (Fin.cons v rest) : Fin (n + 2) → E) =
      Function.update (Fin.cons aa (Fin.cons (0 : E) rest)) 1 v := by
    intro v
    rw [show (1 : Fin (n + 2)) = Fin.succ 0 from rfl]
    rw [← Fin.cons_update]
    rw [Fin.update_cons_zero]
  have hgen : ∀ ss : Finset (Fin d),
      Zm (Function.update (Fin.cons aa (Fin.cons (0 : E) rest)) 1 (∑ c ∈ ss, t c • u c)) =
        ∑ c ∈ ss, t c * Zm (Function.update (Fin.cons aa (Fin.cons (0 : E) rest)) 1 (u c)) := by
    intro ss
    induction ss using Finset.induction_on with
    | empty =>
        rw [Finset.sum_empty, Finset.sum_empty]
        rw [show (0 : E) = ((0 : ℝ) • (0 : E)) from (zero_smul ℝ (0 : E)).symm]
        rw [ContinuousMultilinearMap.map_update_smul]
        rw [zero_smul]
    | @insert a ss ha ih =>
        rw [Finset.sum_insert ha, Finset.sum_insert ha]
        rw [ContinuousMultilinearMap.map_update_add]
        rw [ih]
        congr 1
        rw [ContinuousMultilinearMap.map_update_smul]
        rw [smul_eq_mul]
  have h2 := hgen Finset.univ
  rw [h1, h2]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← h1 (u c)]

set_option linter.unusedSectionVars false in
private lemma unitModel_eq_ccTensorBilin_pt (S : SmoothCcTensor g₀ 0 2) (b : M)
    (u w : TangentSpace I b) :
    unitModel (I := I) (M := M) g₀ 2 S b ![u, w] = ccTensorBilin (I := I) g₀ S b u w := by
  rw [ccTensorBilin_apply (I := I) g₀ S b u w, ccTensorModel]
  rw [show ccTensorMultilinear (I := I) g₀ S b =
      (show Tensor0SSpace 0 I b →L[ℝ] Tensor0SSpace 2 I b from S.toSection b)
        (unitZeroSec (I := I) (M := M) b) from rfl]
  rw [unitModel]
  refine congrArg _ ?_
  funext k
  fin_cases k <;> rfl

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
private lemma reindexCoeffGen_one_eq (r s : ℕ) (R : SmoothCcTensor g₀ r s) :
    reindexCoeffGen (I := I) (M := M) g₀ r s R 1 = R := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro D
  rw [show ((reindexCoeffGen (I := I) (M := M) g₀ r s R 1).toSection x) D =
      reindexCoeffFibGen (I := I) r s 1 x
        (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from R.toSection x) D from rfl]
  rw [reindexCoeffFibGen_apply]
  refine congrArg _ ?_
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro v
  beta_reduce
  rw [Tensor0SSpace.toModel_ofModel, ContinuousMultilinearMap.domDomCongr_apply]
  rfl

set_option linter.unusedSectionVars false in
lemma rfns_icg_rsDomDomCongrSection_eq (r s : ℕ) (σ : Equiv.Perm (Fin s))
    (R : SmoothCcTensor g₀ r s) (i : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ r (s + i) x
        ((iteratedCovGrad (I := I) g₀ r s i
          (rsDomDomCongrSection (I := I) (M := M) g₀ r s σ R)).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g₀ r (s + i) x
        ((iteratedCovGrad (I := I) g₀ r s i R).toSection x) := by
  have h := rfns_iteratedCovGrad_rsDomDomCongr_both_eq (I := I) (M := M) g₀ r s
    (1 : Equiv.Perm (Fin r)) σ R i x
  rw [reindexCoeffGen_one_eq (I := I) (M := M) g₀ r s
    (rsDomDomCongrSection (I := I) (M := M) g₀ r s σ R)] at h
  exact h

def sigmaE : Equiv.Perm (Fin 6) :=
  ⟨fun i => (![1, 3, 4, 5, 0, 2] : Fin 6 → Fin 6) i,
   fun i => (![4, 0, 5, 1, 2, 3] : Fin 6 → Fin 6) i,
   by decide, by decide⟩

def tauK3b : Equiv.Perm (Fin 6) :=
  ⟨fun i => (![5, 0, 2, 1, 4, 3] : Fin 6 → Fin 6) i,
   fun i => (![1, 3, 2, 5, 4, 0] : Fin 6 → Fin 6) i,
   by decide, by decide⟩

def tauM1 : Equiv.Perm (Fin 6) :=
  ⟨fun i => (![5, 2, 0, 3, 4, 1] : Fin 6 → Fin 6) i,
   fun i => (![2, 5, 1, 3, 4, 0] : Fin 6 → Fin 6) i,
   by decide, by decide⟩

def tauM2 : Equiv.Perm (Fin 6) :=
  ⟨fun i => (![5, 2, 0, 1, 4, 3] : Fin 6 → Fin 6) i,
   fun i => (![2, 3, 1, 5, 4, 0] : Fin 6 → Fin 6) i,
   by decide, by decide⟩

def tauM3 : Equiv.Perm (Fin 6) :=
  ⟨fun i => (![5, 4, 0, 3, 2, 1] : Fin 6 → Fin 6) i,
   fun i => (![2, 5, 4, 3, 1, 0] : Fin 6 → Fin 6) i,
   by decide, by decide⟩

def tauM4 : Equiv.Perm (Fin 6) :=
  ⟨fun i => (![5, 4, 0, 1, 2, 3] : Fin 6 → Fin 6) i,
   fun i => (![2, 3, 4, 5, 1, 0] : Fin 6 → Fin 6) i,
   by decide, by decide⟩

set_option backward.isDefEq.respectTransparency false in

def mvDoubleTraceField (s : ℕ) : SmoothCcTensor g₀ (s + 2) s where
  toSection :=
    { toFun := fun x : M =>
        (show TensorRSSpace (s + 2) s I x from cometricDoubleTraceFib (I := I) g₁ s x)
      contMDiff_toFun := cometricDoubleTraceFib_contMDiff (I := I) g₁ s }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
lemma mvDoubleTraceField_self_eq (s : ℕ) :
    mvDoubleTraceField (I := I) (M := M) g₀ g₀ s = cometricDoubleTraceField (I := I) g₀ s := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [cometricDoubleTraceField_toSection]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
private lemma slotInsertEndoCc_add_local (s : ℕ)
    (A B : ContMDiffSection I (E →L[ℝ] E) ∞
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)) :
    slotInsertEndoCc (I := I) (M := M) g₀ s (A + B) =
      slotInsertEndoCc (I := I) (M := M) g₀ s A +
        slotInsertEndoCc (I := I) (M := M) g₀ s B := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro D
  rw [show ((slotInsertEndoCc (I := I) (M := M) g₀ s A +
        slotInsertEndoCc (I := I) (M := M) g₀ s B).toSection x) =
      (slotInsertEndoCc (I := I) (M := M) g₀ s A).toSection x +
        (slotInsertEndoCc (I := I) (M := M) g₀ s B).toSection x from by
    rw [SmoothCcTensor.toSection_add]; rfl]
  rw [ContinuousLinearMap.add_apply]
  simp only [slotInsertEndoCc_toSection]
  rw [show ((A + B) x) = A x + B x from by rw [ContMDiffSection.coe_add]; rfl]
  rw [slotInsertEndoFib_add_left, ContinuousLinearMap.add_apply]

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
private lemma fullRaisedEndoField_diff_split_local :
    fullRaisedEndoField (I := I) (M := M) g₀ g₁ =
      gInvDiffRaisedEndoField (I := I) g₀ g₁ +
        fullRaisedEndoField (I := I) (M := M) g₀ g₀ := by
  apply ContMDiffSection.ext
  intro x
  rw [show ((gInvDiffRaisedEndoField (I := I) g₀ g₁ +
        fullRaisedEndoField (I := I) (M := M) g₀ g₀) x) =
      gInvDiffRaisedEndoField (I := I) g₀ g₁ x +
        fullRaisedEndoField (I := I) (M := M) g₀ g₀ x from by
    rw [ContMDiffSection.coe_add]; rfl]
  apply ContinuousLinearMap.ext
  intro v
  rw [fullRaisedEndoField_apply, ContinuousLinearMap.add_apply]
  rw [show (gInvDiffRaisedEndoField (I := I) g₀ g₁ x) = gInvDiffRaisedEndo (I := I) g₀ g₁ x
    from rfl]
  rw [fullRaisedEndoField_apply]
  rw [gInvRaisedEndo_eq_diff_add_id (I := I) g₀ g₁ x v]
  rw [show gInvRaisedEndo (I := I) g₀ g₀ x v = v from by
    rw [gInvRaisedEndo_apply, inverseMetricSharpFib_g0FlatCLM]]

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
private lemma appCcRS_slotInsert_id_eq (s c : ℕ) (Φ : SmoothCcTensor g₀ (s + 1) c) :
    appCcRS (I := I) (M := M) g₀ (s + 1) (s + 1) c Φ
      (slotInsertEndoCc (I := I) (M := M) g₀ s
        (fullRaisedEndoField (I := I) (M := M) g₀ g₀)) = Φ := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro D
  rw [show ((appCcRS (I := I) (M := M) g₀ (s + 1) (s + 1) c Φ
      (slotInsertEndoCc (I := I) (M := M) g₀ s
        (fullRaisedEndoField (I := I) (M := M) g₀ g₀))).toSection x) D =
      ((show Tensor0SSpace (s + 1) I x →L[ℝ] Tensor0SSpace c I x from Φ.toSection x)
        (slotInsertEndoFib (I := I) (M := M) (s + 1) 0 x
          (fullRaisedEndoField (I := I) (M := M) g₀ g₀ x) D)) from by
    rw [appCcRS_toSection]
    rfl]
  refine congrArg _ ?_
  apply Tensor0SSpace.toModel_injective
  refine ContinuousMultilinearMap.ext (fun m => ?_)
  rw [slotInsertEndoFib_apply_eval]
  rw [show (fullRaisedEndoField (I := I) (M := M) g₀ g₀ x (m 0)) = m 0 from by
    rw [fullRaisedEndoField_apply, gInvRaisedEndo_apply, inverseMetricSharpFib_g0FlatCLM]]
  rw [Function.update_eq_self]

set_option linter.unusedSectionVars false in
lemma mvOrthoFrame_center_repr (g : SmoothRiemannianMetric I M) (x : M)
    (v : TangentSpace I x) :
    v = ∑ i : Fin (Module.finrank ℝ E),
      g.inner x (smoothOrthoFrame (I := I) g x i x) v • smoothOrthoFrame (I := I) g x i x := by
  classical
  haveI : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  haveI : Nonempty (Fin (Module.finrank ℝ E)) :=
    ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne (Module.finrank ℝ E))⟩⟩
  set B : Fin (Module.finrank ℝ E) → TangentSpace I x :=
    fun i => smoothOrthoFrame (I := I) g x i x with hB_def
  have horth : ∀ i j, g.inner x (B i) (B j) = if i = j then (1 : ℝ) else 0 :=
    fun i j => smoothOrthoFrame_orthonormal_at_center (I := I) g x i j
  have hlin : LinearIndependent ℝ B := by
    rw [Fintype.linearIndependent_iff]
    intro c hc j
    have hpair : g.inner x (∑ i, c i • B i) (B j) = 0 := by
      rw [hc]
      simp
    rw [map_sum, ContinuousLinearMap.sum_apply] at hpair
    have hsimp : ∀ i, g.inner x (c i • B i) (B j) = c i * (if i = j then (1 : ℝ) else 0) := by
      intro i
      rw [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul, horth i j]
    rw [Finset.sum_congr rfl (fun i _ => hsimp i)] at hpair
    have hcol : (∑ i, c i * (if i = j then (1 : ℝ) else 0)) = c j := by simp
    rw [hcol] at hpair
    exact hpair
  have hcard : Fintype.card (Fin (Module.finrank ℝ E)) =
      Module.finrank ℝ (TangentSpace I x) := by
    rw [Fintype.card_fin]
    rfl
  set bB : Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I x) :=
    basisOfLinearIndependentOfCardEqFinrank hlin hcard with hbB_def
  have hbB_coe : ∀ i, bB i = B i := by
    intro i
    rw [hbB_def]
    change (basisOfLinearIndependentOfCardEqFinrank hlin hcard :
        Fin (Module.finrank ℝ E) → TangentSpace I x) i = B i
    rw [coe_basisOfLinearIndependentOfCardEqFinrank]
  have hrepr : ∀ (w : TangentSpace I x) (j : Fin (Module.finrank ℝ E)),
      bB.repr w j = g.inner x (B j) w := by
    intro w j
    conv_rhs => rw [← bB.sum_repr w]
    rw [map_sum]
    have hsimp : ∀ i, g.inner x (B j) (bB.repr w i • bB i) =
        bB.repr w i * (if j = i then (1 : ℝ) else 0) := by
      intro i
      rw [map_smul, smul_eq_mul, hbB_coe i, horth j i]
    rw [Finset.sum_congr rfl (fun i _ => hsimp i)]
    simp
  conv_lhs => rw [← bB.sum_repr v]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hrepr v i, hbB_coe i]

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
set_option maxHeartbeats 12800000 in
private lemma mvDoubleTraceField_eq_trace_fullRaised (s : ℕ) :
    mvDoubleTraceField (I := I) (M := M) g₀ g₁ s =
      appCcRS (I := I) (M := M) g₀ (s + 2) (s + 2) s
        (cometricDoubleTraceField (I := I) g₀ s)
        (slotInsertEndoCc (I := I) (M := M) g₀ (s + 1)
          (fullRaisedEndoField (I := I) (M := M) g₀ g₁)) := by
  classical
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro Z
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro mm
  have hLHS : Tensor0SSpace.toModel
      ((show Tensor0SSpace (s + 2) I x →L[ℝ] Tensor0SSpace s I x from
        (mvDoubleTraceField (I := I) (M := M) g₀ g₁ s).toSection x) Z) mm =
      ∑ c : Fin (Module.finrank ℝ E),
        Tensor0SSpace.toModel Z
          (Fin.cons ((smoothOrthoFrame (I := I) g₁ x c x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₁ x c x : TangentSpace I x) : E) mm)) := by
    rw [show ((show Tensor0SSpace (s + 2) I x →L[ℝ] Tensor0SSpace s I x from
        (mvDoubleTraceField (I := I) (M := M) g₀ g₁ s).toSection x) Z) =
        cometricDoubleTraceFib (I := I) g₁ s x Z from rfl]
    rw [cometricDoubleTraceFib_toModel (I := I) g₁ s x Z]
    rw [modelDoubleTrace_apply (E := E) s (cometricLmodel (I := I) g₁ x)]
    rw [cometric_dualTrace_eq_orthoFrame_diag (I := I) g₁ x
      (mem_smoothOrthoFrameNbhd_self (I := I) (M := M) x) (Tensor0SSpace.toModel Z) mm]
  rw [hLHS]
  have hRHS : Tensor0SSpace.toModel
      ((show Tensor0SSpace (s + 2) I x →L[ℝ] Tensor0SSpace s I x from
        (appCcRS (I := I) (M := M) g₀ (s + 2) (s + 2) s
          (cometricDoubleTraceField (I := I) g₀ s)
          (slotInsertEndoCc (I := I) (M := M) g₀ (s + 1)
            (fullRaisedEndoField (I := I) (M := M) g₀ g₁))).toSection x) Z) mm =
      ∑ a : Fin (Module.finrank ℝ E),
        Tensor0SSpace.toModel Z
          (Fin.cons (show E from gInvRaisedEndo (I := I) g₀ g₁ x
              (smoothOrthoFrame (I := I) g₀ x a x))
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x a x : TangentSpace I x) : E) mm)) := by
    rw [show ((show Tensor0SSpace (s + 2) I x →L[ℝ] Tensor0SSpace s I x from
        (appCcRS (I := I) (M := M) g₀ (s + 2) (s + 2) s
          (cometricDoubleTraceField (I := I) g₀ s)
          (slotInsertEndoCc (I := I) (M := M) g₀ (s + 1)
            (fullRaisedEndoField (I := I) (M := M) g₀ g₁))).toSection x) Z) =
        cometricDoubleTraceFib (I := I) g₀ s x
          (slotInsertEndoFib (I := I) (M := M) (s + 2) 0 x
            (fullRaisedEndoField (I := I) (M := M) g₀ g₁ x) Z) from by
      rw [appCcRS_toSection]
      rfl]
    rw [cometricDoubleTraceFib_toModel (I := I) g₀ s x]
    rw [modelDoubleTrace_apply (E := E) s (cometricLmodel (I := I) g₀ x)]
    rw [cometric_dualTrace_eq_orthoFrame_diag (I := I) g₀ x
      (mem_smoothOrthoFrameNbhd_self (I := I) (M := M) x)
      (Tensor0SSpace.toModel
        (slotInsertEndoFib (I := I) (M := M) (s + 2) 0 x
          (fullRaisedEndoField (I := I) (M := M) g₀ g₁ x) Z)) mm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [slotInsertEndoFib_apply_eval]
    rw [Fin.update_cons_zero]
    rfl
  rw [hRHS]
  have hGrep : ∀ a : Fin (Module.finrank ℝ E),
      (show E from gInvRaisedEndo (I := I) g₀ g₁ x (smoothOrthoFrame (I := I) g₀ x a x)) =
        ∑ c : Fin (Module.finrank ℝ E),
          (g₀.inner x (smoothOrthoFrame (I := I) g₀ x a x) (smoothOrthoFrame (I := I) g₁ x c x)) •
            (smoothOrthoFrame (I := I) g₁ x c x : E) := by
    intro a
    have h1 := mvOrthoFrame_center_repr (I := I) (M := M) g₁ x
      (gInvRaisedEndo (I := I) g₀ g₁ x (smoothOrthoFrame (I := I) g₀ x a x))
    rw [show (show E from gInvRaisedEndo (I := I) g₀ g₁ x
        (smoothOrthoFrame (I := I) g₀ x a x)) =
        gInvRaisedEndo (I := I) g₀ g₁ x (smoothOrthoFrame (I := I) g₀ x a x) from rfl]
    conv_lhs => rw [h1]
    refine Finset.sum_congr rfl fun c _ => ?_
    congr 1
    rw [g₁.symm x (smoothOrthoFrame (I := I) g₁ x c x)
      (gInvRaisedEndo (I := I) g₀ g₁ x (smoothOrthoFrame (I := I) g₀ x a x))]
    rw [show g₁.inner x (gInvRaisedEndo (I := I) g₀ g₁ x (smoothOrthoFrame (I := I) g₀ x a x))
        (smoothOrthoFrame (I := I) g₁ x c x) =
        g₀.inner x (smoothOrthoFrame (I := I) g₀ x a x)
          (smoothOrthoFrame (I := I) g₁ x c x) from by
      rw [gInvRaisedEndo_apply]
      rw [inverseMetricSharpFib_inner (I := I) g₁ x
        (g0FlatCLM (I := I) g₀ x (smoothOrthoFrame (I := I) g₀ x a x))
        (smoothOrthoFrame (I := I) g₁ x c x)]
      rw [show cotangentToDualLinear (I := I) (x := x)
          (g0FlatCLM (I := I) g₀ x (smoothOrthoFrame (I := I) g₀ x a x))
          (smoothOrthoFrame (I := I) g₁ x c x) =
          cotangentToDual (I := I) (x := x)
            (g0FlatCLM (I := I) g₀ x (smoothOrthoFrame (I := I) g₀ x a x))
            (smoothOrthoFrame (I := I) g₁ x c x) from rfl]
      rw [cotangentToDual_g0FlatCLM]]
  symm
  calc (∑ a : Fin (Module.finrank ℝ E),
        Tensor0SSpace.toModel Z
          (Fin.cons (show E from gInvRaisedEndo (I := I) g₀ g₁ x
              (smoothOrthoFrame (I := I) g₀ x a x))
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x a x : TangentSpace I x) : E) mm)))
      = ∑ a : Fin (Module.finrank ℝ E), ∑ c : Fin (Module.finrank ℝ E),
          (g₀.inner x (smoothOrthoFrame (I := I) g₀ x a x)
            (smoothOrthoFrame (I := I) g₁ x c x)) *
          Tensor0SSpace.toModel Z
            (Fin.cons ((smoothOrthoFrame (I := I) g₁ x c x : TangentSpace I x) : E)
              (Fin.cons ((smoothOrthoFrame (I := I) g₀ x a x : TangentSpace I x) : E) mm)) := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [hGrep a]
        exact toModel_cons_sum_smul (E := E) x (Tensor0SSpace.toModel Z)
          (Module.finrank ℝ E)
          (fun c => g₀.inner x (smoothOrthoFrame (I := I) g₀ x a x)
            (smoothOrthoFrame (I := I) g₁ x c x))
          (fun c => (smoothOrthoFrame (I := I) g₁ x c x : E))
          (Fin.cons ((smoothOrthoFrame (I := I) g₀ x a x : TangentSpace I x) : E) mm)
    _ = ∑ c : Fin (Module.finrank ℝ E), ∑ a : Fin (Module.finrank ℝ E),
          (g₀.inner x (smoothOrthoFrame (I := I) g₀ x a x)
            (smoothOrthoFrame (I := I) g₁ x c x)) *
          Tensor0SSpace.toModel Z
            (Fin.cons ((smoothOrthoFrame (I := I) g₁ x c x : TangentSpace I x) : E)
              (Fin.cons ((smoothOrthoFrame (I := I) g₀ x a x : TangentSpace I x) : E) mm)) :=
        Finset.sum_comm
    _ = ∑ c : Fin (Module.finrank ℝ E),
          Tensor0SSpace.toModel Z
            (Fin.cons ((smoothOrthoFrame (I := I) g₁ x c x : TangentSpace I x) : E)
              (Fin.cons ((smoothOrthoFrame (I := I) g₁ x c x : TangentSpace I x) : E) mm)) := by
        refine Finset.sum_congr rfl fun c _ => ?_
        have hsum := toModel_cons_cons_sum_smul (E := E) x
          (Tensor0SSpace.toModel Z)
          ((smoothOrthoFrame (I := I) g₁ x c x : TangentSpace I x) : E)
          (Module.finrank ℝ E)
          (fun a => g₀.inner x (smoothOrthoFrame (I := I) g₀ x a x)
            (smoothOrthoFrame (I := I) g₁ x c x))
          (fun a => (smoothOrthoFrame (I := I) g₀ x a x : E)) mm
        rw [← hsum]
        congr 2
        have hrep0 := mvOrthoFrame_center_repr (I := I) (M := M) g₀ x
          (smoothOrthoFrame (I := I) g₁ x c x)
        rw [show (∑ a : Fin (Module.finrank ℝ E),
            g₀.inner x (smoothOrthoFrame (I := I) g₀ x a x)
              (smoothOrthoFrame (I := I) g₁ x c x) •
              (smoothOrthoFrame (I := I) g₀ x a x : E)) =
            ((∑ a : Fin (Module.finrank ℝ E),
              g₀.inner x (smoothOrthoFrame (I := I) g₀ x a x)
                (smoothOrthoFrame (I := I) g₁ x c x) •
                smoothOrthoFrame (I := I) g₀ x a x : TangentSpace I x) : E) from rfl]
        rw [← hrep0]

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
private lemma mvDoubleTraceField_cross_split (s : ℕ) :
    mvDoubleTraceField (I := I) (M := M) g₀ g₁ s =
      appCcRS (I := I) (M := M) g₀ (s + 2) (s + 2) s
        (cometricDoubleTraceField (I := I) g₀ s)
        (slotInsertEndoCc (I := I) (M := M) g₀ (s + 1)
          (gInvDiffRaisedEndoField (I := I) g₀ g₁)) +
      cometricDoubleTraceField (I := I) g₀ s := by
  rw [mvDoubleTraceField_eq_trace_fullRaised (I := I) (M := M) g₀ g₁ s]
  rw [fullRaisedEndoField_diff_split_local (I := I) (M := M) g₀ g₁]
  rw [slotInsertEndoCc_add_local (I := I) (M := M) g₀ (s + 1)]
  rw [appCcRS_add_right (I := I) (M := M) g₀ (s + 2) (s + 2) s
    (cometricDoubleTraceField (I := I) g₀ s)]
  rw [appCcRS_slotInsert_id_eq (I := I) (M := M) g₀ (s + 1) s
    (cometricDoubleTraceField (I := I) g₀ s)]

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
lemma slotExtend_toModel_cons (r s : ℕ) (Φ : SmoothCcTensor g₀ r s) (x : M)
    (D : Tensor0SSpace (r + 1) I x) (v0 : TangentSpace I x) (vs : Fin s → E) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace (r + 1) I x →L[ℝ] Tensor0SSpace (s + 1) I x from
          (slotExtend (I := I) (M := M) g₀ r s Φ).toSection x) D)
        (Fin.cons (show E from v0) vs) =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from Φ.toSection x)
          (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) r x D v0)) vs := by
  rw [show ((show Tensor0SSpace (r + 1) I x →L[ℝ] Tensor0SSpace (s + 1) I x from
      (slotExtend (I := I) (M := M) g₀ r s Φ).toSection x) D) =
      slotExtendFib (I := I) (M := M) g₀ r s x
        (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from Φ.toSection x) D from rfl]
  exact slotExtendFib_apply_eval (I := I) (M := M) g₀ r s x
    (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from Φ.toSection x) D
    (show E from v0) vs

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
private lemma slotExtendIter_two_toModel (X : SmoothCcTensor g₀ 0 4) (x : M)
    (D : Tensor0SSpace 2 I x) (u : Fin 6 → TangentSpace I x) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 6 I x from
          (slotExtendIter (I := I) (M := M) g₀ 0 4 2 X).toSection x) D) u =
      Tensor0SSpace.toModel D ![u 0, u 1] *
        unitModel (I := I) (M := M) g₀ 4 X x (fun k : Fin 4 => u (Fin.natAdd 2 k)) := by
  have hu : (fun k : Fin 6 => (u k : E)) =
      Fin.cons (show E from u 0)
        (Fin.cons (show E from u 1) (fun k : Fin 4 => (u (Fin.natAdd 2 k) : E))) := by
    funext k
    refine Fin.cases rfl (fun k1 => ?_) k
    refine Fin.cases rfl (fun k2 => ?_) k1
    change (u (Fin.succ (Fin.succ k2)) : E) = (u (Fin.natAdd 2 k2) : E)
    congr 1
    exact Fin.ext (by simp [Fin.succ, Fin.natAdd]; omega)
  rw [show (Tensor0SSpace.toModel
      ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 6 I x from
        (slotExtendIter (I := I) (M := M) g₀ 0 4 2 X).toSection x) D) u) =
      (Tensor0SSpace.toModel
        ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 6 I x from
          (slotExtend (I := I) (M := M) g₀ 1 5
            (slotExtendIter (I := I) (M := M) g₀ 0 4 1 X)).toSection x) D)
        (fun k : Fin 6 => (u k : E))) from rfl]
  rw [hu]
  rw [slotExtend_toModel_cons (I := I) (M := M) g₀ 1 5
    (slotExtendIter (I := I) (M := M) g₀ 0 4 1 X) x D (u 0)]
  rw [show ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 5 I x from
      (slotExtendIter (I := I) (M := M) g₀ 0 4 1 X).toSection x)
        (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x D (u 0))) =
      ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 5 I x from
        (slotExtend (I := I) (M := M) g₀ 0 4 X).toSection x)
        (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x D (u 0))) from rfl]
  rw [slotExtend_toModel_cons (I := I) (M := M) g₀ 0 4 X x
    (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x D (u 0)) (u 1)]
  set t : Tensor0SSpace 0 I x :=
    tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 0 x
      (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x D (u 0)) (u 1) with ht_def
  have htval : Tensor0SSpace.toModel t (fun i : Fin 0 => i.elim0) =
      Tensor0SSpace.toModel D ![u 0, u 1] := by
    rw [ht_def]
    have h1 := TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M) (n := 0)
      (T := tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x D (u 0)) (v0 := (u 1 : E))
      (vs := fun i : Fin 0 => i.elim0)
    rw [h1]
    have h2 := TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M) (n := 1)
      (T := D) (v0 := (u 0 : E)) (vs := Fin.cons (show E from u 1) (fun i : Fin 0 => i.elim0))
    rw [h2]
    refine congrArg _ ?_
    funext k
    refine Fin.cases rfl (fun i => ?_) k
    refine Fin.cases rfl (fun i2 => i2.elim0) i
  have hdecomp := tensor0S_rank0_eq_smul_unit (I := I) (M := M) x t
  rw [htval] at hdecomp
  rw [hdecomp, map_smul]
  rw [Tensor0SSpace.toModel_smul, ContinuousMultilinearMap.smul_apply, smul_eq_mul]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
private lemma slotExtendIter_three_toModel (X : SmoothCcTensor g₀ 0 3) (x : M)
    (D : Tensor0SSpace 3 I x) (u : Fin 6 → TangentSpace I x) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 3 I x →L[ℝ] Tensor0SSpace 6 I x from
          (slotExtendIter (I := I) (M := M) g₀ 0 3 3 X).toSection x) D) u =
      Tensor0SSpace.toModel D ![u 0, u 1, u 2] *
        unitModel (I := I) (M := M) g₀ 3 X x (fun k : Fin 3 => u (Fin.natAdd 3 k)) := by
  have hu : (fun k : Fin 6 => (u k : E)) =
      Fin.cons (show E from u 0)
        (Fin.cons (show E from u 1)
          (Fin.cons (show E from u 2) (fun k : Fin 3 => (u (Fin.natAdd 3 k) : E)))) := by
    funext k
    refine Fin.cases rfl (fun k1 => ?_) k
    refine Fin.cases rfl (fun k2 => ?_) k1
    refine Fin.cases rfl (fun k3 => ?_) k2
    change (u (Fin.succ (Fin.succ (Fin.succ k3))) : E) = (u (Fin.natAdd 3 k3) : E)
    congr 1
    exact Fin.ext (by simp [Fin.succ, Fin.natAdd]; omega)
  rw [show (Tensor0SSpace.toModel
      ((show Tensor0SSpace 3 I x →L[ℝ] Tensor0SSpace 6 I x from
        (slotExtendIter (I := I) (M := M) g₀ 0 3 3 X).toSection x) D) u) =
      (Tensor0SSpace.toModel
        ((show Tensor0SSpace 3 I x →L[ℝ] Tensor0SSpace 6 I x from
          (slotExtend (I := I) (M := M) g₀ 2 5
            (slotExtendIter (I := I) (M := M) g₀ 0 3 2 X)).toSection x) D)
        (fun k : Fin 6 => (u k : E))) from rfl]
  rw [hu]
  rw [slotExtend_toModel_cons (I := I) (M := M) g₀ 2 5
    (slotExtendIter (I := I) (M := M) g₀ 0 3 2 X) x D (u 0)]
  rw [show ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 5 I x from
      (slotExtendIter (I := I) (M := M) g₀ 0 3 2 X).toSection x)
        (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 2 x D (u 0))) =
      ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 5 I x from
        (slotExtend (I := I) (M := M) g₀ 1 4
          (slotExtendIter (I := I) (M := M) g₀ 0 3 1 X)).toSection x)
        (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 2 x D (u 0))) from rfl]
  rw [slotExtend_toModel_cons (I := I) (M := M) g₀ 1 4
    (slotExtendIter (I := I) (M := M) g₀ 0 3 1 X) x
    (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 2 x D (u 0)) (u 1)]
  rw [show ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 4 I x from
      (slotExtendIter (I := I) (M := M) g₀ 0 3 1 X).toSection x)
        (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x
          (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 2 x D (u 0)) (u 1))) =
      ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 4 I x from
        (slotExtend (I := I) (M := M) g₀ 0 3 X).toSection x)
        (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x
          (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 2 x D (u 0)) (u 1))) from rfl]
  rw [slotExtend_toModel_cons (I := I) (M := M) g₀ 0 3 X x
    (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x
      (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 2 x D (u 0)) (u 1)) (u 2)]
  set t : Tensor0SSpace 0 I x :=
    tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 0 x
      (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x
        (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 2 x D (u 0)) (u 1)) (u 2) with ht_def
  have htval : Tensor0SSpace.toModel t (fun i : Fin 0 => i.elim0) =
      Tensor0SSpace.toModel D ![u 0, u 1, u 2] := by
    rw [ht_def]
    have h1 := TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M) (n := 0)
      (T := tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x
        (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 2 x D (u 0)) (u 1)) (v0 := (u 2 : E))
      (vs := fun i : Fin 0 => i.elim0)
    rw [h1]
    have h2 := TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M) (n := 1)
      (T := tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 2 x D (u 0)) (v0 := (u 1 : E))
      (vs := Fin.cons (show E from u 2) (fun i : Fin 0 => i.elim0))
    rw [h2]
    have h3 := TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M) (n := 2)
      (T := D) (v0 := (u 0 : E))
      (vs := Fin.cons (show E from u 1)
        (Fin.cons (show E from u 2) (fun i : Fin 0 => i.elim0)))
    rw [h3]
    refine congrArg _ ?_
    funext k
    refine Fin.cases rfl (fun i => ?_) k
    refine Fin.cases rfl (fun i2 => ?_) i
    refine Fin.cases rfl (fun i3 => i3.elim0) i2
  have hdecomp := tensor0S_rank0_eq_smul_unit (I := I) (M := M) x t
  rw [htval] at hdecomp
  rw [hdecomp, map_smul]
  rw [Tensor0SSpace.toModel_smul, ContinuousMultilinearMap.smul_apply, smul_eq_mul]
  rfl

def mvPairTraceOp : SmoothCcTensor g₀ 6 2 :=
  appCcRS (I := I) (M := M) g₀ 6 4 2
    (mvDoubleTraceField (I := I) (M := M) g₀ g₁ 2)
    (mvDoubleTraceField (I := I) (M := M) g₀ g₁ 4)

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
set_option maxHeartbeats 12800000 in

lemma mvPairTraceOp_apply_toModel (X : SmoothCcTensor g₀ 0 4) (x : M)
    (D : Tensor0SSpace 2 I x) (v : Fin 2 → E) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
          (appCcRS (I := I) (M := M) g₀ 2 6 2 (mvPairTraceOp (I := I) (M := M) g₀ g₁)
            (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE
              (slotExtendIter (I := I) (M := M) g₀ 0 4 2 X))).toSection x) D) v =
      ∑ b : Fin (Module.finrank ℝ E), ∑ a : Fin (Module.finrank ℝ E),
        Tensor0SSpace.toModel D
            ![(smoothOrthoFrame (I := I) g₁ x a x : E),
              (smoothOrthoFrame (I := I) g₁ x b x : E)] *
          unitModel (I := I) (M := M) g₀ 4 X x
            ![v 0, v 1, (smoothOrthoFrame (I := I) g₁ x a x : E),
              (smoothOrthoFrame (I := I) g₁ x b x : E)] := by
  classical
  set Y : Tensor0SSpace 6 I x :=
    (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 6 I x from
      (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE
        (slotExtendIter (I := I) (M := M) g₀ 0 4 2 X)).toSection x) D with hY_def
  have hYval : ∀ w : Fin 6 → TangentSpace I x,
      Tensor0SSpace.toModel Y w =
        Tensor0SSpace.toModel D ![w 1, w 3] *
          unitModel (I := I) (M := M) g₀ 4 X x ![w 4, w 5, w 0, w 2] := by
    intro w
    rw [hY_def]
    rw [show ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 6 I x from
        (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE
          (slotExtendIter (I := I) (M := M) g₀ 0 4 2 X)).toSection x) D) =
        ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 6 I x from
          rsDomDomCongr sigmaE
            ((slotExtendIter (I := I) (M := M) g₀ 0 4 2 X).toSection x)) D) from by
      rw [rsDomDomCongrSection_toSection]]
    rw [toModel_rsDomDomCongr_apply (I := I) (M := M) sigmaE
      ((slotExtendIter (I := I) (M := M) g₀ 0 4 2 X).toSection x) D]
    rw [ContinuousMultilinearMap.domDomCongr_apply]
    rw [slotExtendIter_two_toModel (I := I) (M := M) g₀ X x D
      (fun i => w (sigmaE i))]
    refine congrArg₂ (· * ·) ?_ ?_
    · refine congrArg _ ?_
      funext k
      fin_cases k <;> rfl
    · refine congrArg _ ?_
      funext k
      fin_cases k <;> rfl
  rw [show ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
      (appCcRS (I := I) (M := M) g₀ 2 6 2 (mvPairTraceOp (I := I) (M := M) g₀ g₁)
        (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE
          (slotExtendIter (I := I) (M := M) g₀ 0 4 2 X))).toSection x) D) =
      cometricDoubleTraceFib (I := I) g₁ 2 x
        (cometricDoubleTraceFib (I := I) g₁ 4 x Y) from by
    rw [hY_def]
    rw [appCcRS_toSection]
    rfl]
  rw [cometricDoubleTraceFib_toModel (I := I) g₁ 2 x]
  rw [modelDoubleTrace_apply (E := E) 2 (cometricLmodel (I := I) g₁ x)]
  rw [cometric_dualTrace_eq_orthoFrame_diag (I := I) g₁ x
    (mem_smoothOrthoFrameNbhd_self (I := I) (M := M) x)
    (Tensor0SSpace.toModel (cometricDoubleTraceFib (I := I) g₁ 4 x Y))
    (fun j => (v j : E))]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [cometricDoubleTraceFib_toModel (I := I) g₁ 4 x Y]
  rw [modelDoubleTrace_apply (E := E) 4 (cometricLmodel (I := I) g₁ x)]
  rw [cometric_dualTrace_eq_orthoFrame_diag (I := I) g₁ x
    (mem_smoothOrthoFrameNbhd_self (I := I) (M := M) x)
    (Tensor0SSpace.toModel Y)
    (Fin.cons ((smoothOrthoFrame (I := I) g₁ x b x : TangentSpace I x) : E)
      (Fin.cons ((smoothOrthoFrame (I := I) g₁ x b x : TangentSpace I x) : E)
        (fun j => (v j : E))))]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [hYval]
  rfl

def bgRArmWeight : SmoothCcTensor g₀ 2 4 :=
  appCcRS (I := I) (M := M) g₀ 2 6 4 (cometricDoubleTraceField (I := I) g₀ 4)
    (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 (Equiv.swap (1 : Fin 6) 3)
      (slotExtendIter (I := I) (M := M) g₀ 0 4 2
        (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀)))

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
set_option maxHeartbeats 12800000 in
private lemma bgRArmWeight_toModel (x : M) (D : Tensor0SSpace 2 I x)
    (m : Fin 4 → TangentSpace I x) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 4 I x from
          (bgRArmWeight (I := I) (M := M) g₀).toSection x) D) m =
      ∑ e : Fin (Module.finrank ℝ E),
        Tensor0SSpace.toModel D
            ![(smoothOrthoFrame (I := I) g₀ x e x : E), (m 1 : E)] *
          g₀.inner x (riemannOp (LeviCivita (I := I) g₀) x (m 0) (m 2) (m 3))
            (smoothOrthoFrame (I := I) g₀ x e x) := by
  classical
  set Y : Tensor0SSpace 6 I x :=
    (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 6 I x from
      (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 (Equiv.swap (1 : Fin 6) 3)
        (slotExtendIter (I := I) (M := M) g₀ 0 4 2
          (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀))).toSection x) D with hY_def
  have hYval : ∀ w : Fin 6 → TangentSpace I x,
      Tensor0SSpace.toModel Y w =
        Tensor0SSpace.toModel D ![w 0, w 3] *
          unitModel (I := I) (M := M) g₀ 4
            (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀) x ![w 2, w 1, w 4, w 5] := by
    intro w
    rw [hY_def]
    rw [show ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 6 I x from
        (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 (Equiv.swap (1 : Fin 6) 3)
          (slotExtendIter (I := I) (M := M) g₀ 0 4 2
            (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀))).toSection x) D) =
        ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 6 I x from
          rsDomDomCongr (Equiv.swap (1 : Fin 6) 3)
            ((slotExtendIter (I := I) (M := M) g₀ 0 4 2
              (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀)).toSection x)) D) from by
      rw [rsDomDomCongrSection_toSection]]
    rw [toModel_rsDomDomCongr_apply (I := I) (M := M) (Equiv.swap (1 : Fin 6) 3)
      ((slotExtendIter (I := I) (M := M) g₀ 0 4 2
        (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀)).toSection x) D]
    rw [ContinuousMultilinearMap.domDomCongr_apply]
    rw [slotExtendIter_two_toModel (I := I) (M := M) g₀
      (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀) x D
      (fun i => w ((Equiv.swap (1 : Fin 6) 3) i))]
    refine congrArg₂ (· * ·) ?_ ?_
    · refine congrArg _ ?_
      funext k
      fin_cases k <;> simp [Equiv.swap_apply_def]
    · refine congrArg _ ?_
      funext k
      fin_cases k <;> simp [Equiv.swap_apply_def]
  rw [show ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 4 I x from
      (bgRArmWeight (I := I) (M := M) g₀).toSection x) D) =
      cometricDoubleTraceFib (I := I) g₀ 4 x Y from by
    rw [hY_def, bgRArmWeight]
    rw [appCcRS_toSection]
    rfl]
  rw [cometricDoubleTraceFib_toModel (I := I) g₀ 4 x Y]
  rw [modelDoubleTrace_apply (E := E) 4 (cometricLmodel (I := I) g₀ x)]
  rw [cometric_dualTrace_eq_orthoFrame_diag (I := I) g₀ x
    (mem_smoothOrthoFrameNbhd_self (I := I) (M := M) x)
    (Tensor0SSpace.toModel Y) (fun j => (m j : E))]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [hYval]
  show Tensor0SSpace.toModel D
      ![((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E), (m 1 : E)] *
      unitModel (I := I) (M := M) g₀ 4
        (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀) x
        ![(m 0 : E), ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E),
          (m 2 : E), (m 3 : E)] = _
  rw [riemannLoweredCc_unitModel_apply (I := I) (M := M) g₀ g₀ g₀ x
    ![(m 0 : E), ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E),
      (m 2 : E), (m 3 : E)]]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
private lemma metricCcTensor_unitModel_apply (g : SmoothRiemannianMetric I M) (x : M)
    (m : Fin 2 → E) :
    unitModel (I := I) (M := M) g₀ 2 (metricCcTensor (I := I) (M := M) g₀ g) x m =
      g.inner x (m 0) (m 1) := by
  have hbase : unitModel (I := I) (M := M) g₀ 2 (metricCcTensor (I := I) (M := M) g₀ g) x =
      Tensor0SSpace.toModel (metricCcTensorFib (I := I) g x) := by
    rw [unitModel]
    change Tensor0SSpace.toModel
        ((MixedSection.eval₀ (F := E) (E := (TangentSpace I : M → Type _)) x).smulRight
          (metricCcTensorFib (I := I) g x)
          (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => TangentSpace I x)
            (1 : ℝ))) =
      Tensor0SSpace.toModel (metricCcTensorFib (I := I) g x)
    rw [ContinuousLinearMap.smulRight_apply, MixedSection.eval₀_apply,
      ContinuousMultilinearMap.constOfIsEmpty_apply, one_smul]
  rw [hbase]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
lemma metricDifferenceCcTensor_eq_symmS (P : SmoothCcTensor g₀ 0 2)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w) :
    metricDifferenceCcTensor (I := I) (M := M) g₀ g₁ = symmS (I := I) g₀ P := by
  apply smoothCcTensor_ext_of_unitModel (I := I) (M := M) g₀
  intro x
  apply ContinuousMultilinearMap.ext
  intro m
  rw [show metricDifferenceCcTensor (I := I) (M := M) g₀ g₁ =
      metricCcTensor (I := I) (M := M) g₀ g₁ - metricCcTensor (I := I) (M := M) g₀ g₀ from rfl]
  rw [unitModel_sub_pt (I := I) (M := M) g₀ 2
    (metricCcTensor (I := I) (M := M) g₀ g₁) (metricCcTensor (I := I) (M := M) g₀ g₀) x]
  rw [ContinuousMultilinearMap.sub_apply]
  rw [metricCcTensor_unitModel_apply (I := I) (M := M) g₀ g₁ x m,
    metricCcTensor_unitModel_apply (I := I) (M := M) g₀ g₀ x m]
  rw [show unitModel (I := I) (M := M) g₀ 2 (symmS (I := I) g₀ P) x m =
      unitModel (I := I) (M := M) g₀ 2 (symmS (I := I) g₀ P) x ![m 0, m 1] from by
    refine congrArg _ ?_
    funext k
    fin_cases k <;> rfl]
  rw [unitModel_eq_ccTensorBilin_pt (I := I) (M := M) g₀ (symmS (I := I) g₀ P) x (m 0) (m 1)]
  rw [ccTensorBilin_symmS (I := I) (M := M) g₀ P x (m 0) (m 1)]
  rw [htie x (m 0) (m 1)]
  ring

set_option linter.unusedSectionVars false in
lemma rfns_eq_sum_componentSq_of_horth_pt
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M) (S : TensorRSSpace r s I x)
    {n : ℕ} (e : Fin n → TangentSpace I x) (hn : n = Module.finrank ℝ E)
    (horth : ∀ a b : Fin n, g.inner x (e a) (e b) = if a = b then (1 : ℝ) else 0) :
    riemannianFiberNormSq (I := I) (M := M) g r s x S =
      ∑ K : Fin r → Fin n, ∑ J : Fin s → Fin n,
        (fiberNormSqComponent (I := I) (M := M) g x r s S n e K J) ^ 2 := by
  classical
  haveI : Nonempty (Fin n) := by
    rw [hn]
    exact ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne (Module.finrank ℝ E))⟩⟩
  have he_li : LinearIndependent ℝ e := by
    rw [linearIndependent_iff']
    intro fs c hsum k hk_mem
    have h_zero : g.inner x (e k) (∑ j ∈ fs, c j • e j) = 0 := by rw [hsum]; simp
    rw [map_sum] at h_zero
    have h_pull : ∀ j ∈ fs, g.inner x (e k) (c j • e j) =
        c j * (if k = j then (1 : ℝ) else 0) := by
      intro j _
      rw [map_smul, horth k j, smul_eq_mul]
    rw [Finset.sum_congr rfl h_pull] at h_zero
    rw [Finset.sum_eq_single k (fun j _ hj => by rw [if_neg (Ne.symm hj), mul_zero])
      (fun hk => absurd hk_mem hk)] at h_zero
    rwa [if_pos rfl, mul_one] at h_zero
  have hrank : Module.finrank ℝ (TangentSpace I x) = Module.finrank ℝ E := rfl
  have hcard : Fintype.card (Fin n) = Module.finrank ℝ (TangentSpace I x) := by
    rw [Fintype.card_fin, hrank]; exact hn
  set bse := basisOfLinearIndependentOfCardEqFinrank he_li hcard with hbse_def
  have hbse : ∀ i : Fin n, bse i = e i := by
    intro i; rw [hbse_def, coe_basisOfLinearIndependentOfCardEqFinrank]
  exact rfns_rs_eq_sum_componentSq_of_basis (I := I) (M := M) g r s x S e bse hn hbse horth

set_option linter.unusedSectionVars false in
lemma fiberNormSqComponent_zero_toModel_pt
    (g : SmoothRiemannianMetric I M) (s : ℕ) (x : M) (S : SmoothCcTensor g 0 s)
    {n : ℕ} (e : Fin n → TangentSpace I x) (K : Fin 0 → Fin n) (L : Fin s → Fin n) :
    fiberNormSqComponent (I := I) (M := M) g x 0 s (S.toSection x) n e K L =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from S.toSection x)
          (unitTensor (I := I) (M := M) x))
        (fun k => (show E from e (L k))) := by
  rw [show fiberNormSqComponent (I := I) (M := M) g x 0 s (S.toSection x) n e K L =
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from S.toSection x)
        (coframeS (I := I) (M := M) g x 0 e K) (fun k => e (L k)) from rfl]
  rw [coframeS_zero_eq_unitZeroSec (I := I) (M := M) g x e K]
  rfl

set_option linter.unusedSectionVars false in
private lemma rfns_symmS_zero_le_of_ball (T : SmoothCcTensor g₀ 0 2) {δ : ℝ} (hδ0 : 0 ≤ δ)
    (hbound : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x
        ((symmS (I := I) (M := M) g₀ T).toSection x) ≤
      (Module.finrank ℝ E : ℝ) ^ 2 * δ ^ 2 := by
  classical
  obtain ⟨n, e, bse, hn, hbse, horth, _hpars, _hrepr, _hsum⟩ :=
    tangent_orthonormalBasis_witness (I := I) (M := M) g₀ x
  have hnE : n = Module.finrank ℝ E := by rw [hn]; rfl
  rw [rfns_eq_sum_componentSq_of_horth_pt (I := I) (M := M) g₀ 0 2 x
    ((symmS (I := I) (M := M) g₀ T).toSection x) e hnE horth]
  have hcomp : ∀ (K : Fin 0 → Fin n) (J : Fin 2 → Fin n),
      (fiberNormSqComponent (I := I) (M := M) g₀ x 0 2
        ((symmS (I := I) (M := M) g₀ T).toSection x) n e K J) ^ 2 ≤ δ ^ 2 := by
    intro K J
    have hval : fiberNormSqComponent (I := I) (M := M) g₀ x 0 2
        ((symmS (I := I) (M := M) g₀ T).toSection x) n e K J =
        ccTensorBilinSymm (I := I) g₀ T x (e (J 0)) (e (J 1)) := by
      rw [fiberNormSqComponent_zero_toModel_pt (I := I) (M := M) g₀ 2 x
        (symmS (I := I) (M := M) g₀ T) e K J]
      rw [show Tensor0SSpace.toModel
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
            (symmS (I := I) (M := M) g₀ T).toSection x)
            (unitTensor (I := I) (M := M) x))
          (fun k => (show E from e (J k))) =
          unitModel (I := I) (M := M) g₀ 2 (symmS (I := I) (M := M) g₀ T) x
            ![e (J 0), e (J 1)] from by
        rw [unitModel]
        refine congrArg _ ?_
        funext k
        fin_cases k <;> rfl]
      rw [unitModel_eq_ccTensorBilin_pt (I := I) (M := M) g₀
        (symmS (I := I) (M := M) g₀ T) x (e (J 0)) (e (J 1))]
      rw [ccTensorBilin_symmS (I := I) (M := M) g₀ T x (e (J 0)) (e (J 1))]
    rw [hval]
    have habs := hbound x (e (J 0)) (e (J 1))
    have h00 : g₀.inner x (e (J 0)) (e (J 0)) = 1 := by
      rw [horth (J 0) (J 0), if_pos rfl]
    have h11 : g₀.inner x (e (J 1)) (e (J 1)) = 1 := by
      rw [horth (J 1) (J 1), if_pos rfl]
    rw [h00, h11, Real.sqrt_one, mul_one, mul_one] at habs
    have := abs_nonneg (ccTensorBilinSymm (I := I) g₀ T x (e (J 0)) (e (J 1)))
    nlinarith [habs, sq_abs (ccTensorBilinSymm (I := I) g₀ T x (e (J 0)) (e (J 1)))]
  calc (∑ K : Fin 0 → Fin n, ∑ J : Fin 2 → Fin n,
        (fiberNormSqComponent (I := I) (M := M) g₀ x 0 2
          ((symmS (I := I) (M := M) g₀ T).toSection x) n e K J) ^ 2)
      ≤ ∑ K : Fin 0 → Fin n, ∑ J : Fin 2 → Fin n, δ ^ 2 :=
        Finset.sum_le_sum fun K _ => Finset.sum_le_sum fun J _ => hcomp K J
    _ = (Fintype.card (Fin 0 → Fin n) : ℝ) * ((Fintype.card (Fin 2 → Fin n) : ℝ) * δ ^ 2) := by
        rw [Finset.sum_const, Finset.sum_const]
        simp only [Finset.card_univ, nsmul_eq_mul]
    _ ≤ (Module.finrank ℝ E : ℝ) ^ 2 * δ ^ 2 := by
        have hc0 : (Fintype.card (Fin 0 → Fin n) : ℝ) = 1 := by
          simp
        have hc2 : (Fintype.card (Fin 2 → Fin n) : ℝ) = (n : ℝ) ^ 2 := by
          simp only [Fintype.card_fun, Fintype.card_fin]
          push_cast
          ring
        rw [hc0, hc2, one_mul, hnE]

set_option linter.unusedSectionVars false in
lemma rfns_iteratedCovGrad_symmS_pointwise (T : SmoothCcTensor g₀ 0 2) (k : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + k) x
        ((iteratedCovGrad (I := I) g₀ 0 2 k (symmS (I := I) (M := M) g₀ T)).toSection x) ≤
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + k) x
        ((iteratedCovGrad (I := I) g₀ 0 2 k T).toSection x) := by
  have hswap : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + k) x
      ((iteratedCovGrad (I := I) g₀ 0 2 k
        (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1) T)).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + k) x
        ((iteratedCovGrad (I := I) g₀ 0 2 k T).toSection x) :=
    riemannianFiberNormSq_iteratedCovGrad_domDomCongrSection (I := I) (M := M) g₀
      (Equiv.swap (0 : Fin 2) 1) T k x
  set A := iteratedCovGrad (I := I) g₀ 0 2 k T with hA
  set B := iteratedCovGrad (I := I) g₀ 0 2 k
    (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1) T) with hB
  have htoSec : ((iteratedCovGrad (I := I) g₀ 0 2 k
        (symmS (I := I) (M := M) g₀ T)).toSection x : TensorRSSpace 0 (2 + k) I x) =
      (1 / 2 : ℝ) • (A.toSection x) + (1 / 2 : ℝ) • (B.toSection x) := by
    rw [iteratedCovGrad_symmS_eq (I := I) (M := M) g₀ T k]
    rw [show (((1 / 2 : ℝ) • A + (1 / 2 : ℝ) • B).toSection x) =
        ((1 / 2 : ℝ) • A).toSection x + ((1 / 2 : ℝ) • B).toSection x from by
      rw [SmoothCcTensor.toSection_add]; rfl]
    rw [show (((1 / 2 : ℝ) • A).toSection x) = (1 / 2 : ℝ) • (A.toSection x) from by
        rw [SmoothCcTensor.toSection_smul]; rfl,
      show (((1 / 2 : ℝ) • B).toSection x) = (1 / 2 : ℝ) • (B.toSection x) from by
        rw [SmoothCcTensor.toSection_smul]; rfl]
  rw [htoSec]
  have hRB : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + k) x (B.toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + k) x (A.toSection x) := hswap
  calc riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + k) x
          ((1 / 2 : ℝ) • (A.toSection x) + (1 / 2 : ℝ) • (B.toSection x))
      ≤ 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + k) x
            ((1 / 2 : ℝ) • (A.toSection x)) +
          2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + k) x
            ((1 / 2 : ℝ) • (B.toSection x)) :=
        riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 0 (2 + k) x _ _
    _ = (1 / 2 : ℝ) * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + k) x (A.toSection x) +
          (1 / 2 : ℝ) * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + k) x (B.toSection x) := by
        rw [riemannianFiberNormSq_smul_value (I := I) (M := M) g₀ 0 (2 + k) x (1 / 2 : ℝ),
          riemannianFiberNormSq_smul_value (I := I) (M := M) g₀ 0 (2 + k) x (1 / 2 : ℝ)]
        ring
    _ = riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + k) x (A.toSection x) := by
        rw [hRB]; ring

set_option linter.unusedSectionVars false in
private lemma rfns_iteratedCovGrad_koszulCovecCc_pointwise (T : SmoothCcTensor g₀ 0 2)
    (i : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + i) x
        ((iteratedCovGrad (I := I) g₀ 0 3 i (koszulCovecCc (I := I) g₀ T)).toSection x) ≤
      10 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 1)) x
        ((iteratedCovGrad (I := I) g₀ 0 2 (i + 1) T).toSection x) := by
  classical
  set W : SmoothCcTensor g₀ 0 3 := symmSCovGrad3 (I := I) g₀ T with hW
  set DA : SmoothCcTensor g₀ 0 3 :=
    domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 3) 2) W with hDA
  set DB : SmoothCcTensor g₀ 0 3 := domDomCongrSection (I := I) g₀ (finRotate 3) W with hDB
  set DC : SmoothCcTensor g₀ 0 3 :=
    domDomCongrSection (I := I) g₀ (Equiv.swap (1 : Fin 3) 2) W with hDC
  have hpermW : ∀ σ : Equiv.Perm (Fin 3),
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + i) x
        ((iteratedCovGrad (I := I) g₀ 0 3 i
          (domDomCongrSection (I := I) g₀ σ W)).toSection x) ≤
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 1)) x
        ((iteratedCovGrad (I := I) g₀ 0 2 (i + 1) T).toSection x) := by
    intro σ
    rw [riemannianFiberNormSq_iteratedCovGrad_domDomCongrSection (I := I) (M := M) g₀ σ W i x]
    rw [hW]
    rw [show symmSCovGrad3 (I := I) g₀ T =
        covGrad (I := I) (M := M) g₀ 0 2 (symmS (I := I) g₀ T) from rfl]
    have hcomm := rfns_iteratedCovGrad_covGrad_comm_rs (I := I) (M := M) g₀ 0 2 i
      (symmS (I := I) g₀ T) x
    rw [hcomm]
    exact rfns_iteratedCovGrad_symmS_pointwise (I := I) (M := M) g₀ T (i + 1) x
  have hkos : koszulCovecCc (I := I) g₀ T = (1 / 2 : ℝ) • (DA + DB - DC) := by
    rw [koszulCovecCc, hDA, hDB, hDC, hW]
  have hsub : iteratedCovGrad (I := I) g₀ 0 3 i (DA + DB - DC) =
      iteratedCovGrad (I := I) g₀ 0 3 i DA + iteratedCovGrad (I := I) g₀ 0 3 i DB -
        iteratedCovGrad (I := I) g₀ 0 3 i DC := by
    rw [sub_eq_add_neg, sub_eq_add_neg, iteratedCovGrad_add, iteratedCovGrad_add,
      iteratedCovGrad_neg]
  have htoSec : ((iteratedCovGrad (I := I) g₀ 0 3 i (koszulCovecCc (I := I) g₀ T)).toSection x :
        TensorRSSpace 0 (3 + i) I x) =
      (1 / 2 : ℝ) • ((iteratedCovGrad (I := I) g₀ 0 3 i DA).toSection x +
        (iteratedCovGrad (I := I) g₀ 0 3 i DB).toSection x -
        (iteratedCovGrad (I := I) g₀ 0 3 i DC).toSection x) := by
    rw [hkos, iteratedCovGrad_smul_real, hsub]
    rw [show (((1 / 2 : ℝ) • (iteratedCovGrad (I := I) g₀ 0 3 i DA +
          iteratedCovGrad (I := I) g₀ 0 3 i DB -
          iteratedCovGrad (I := I) g₀ 0 3 i DC)).toSection x) =
        (1 / 2 : ℝ) • ((iteratedCovGrad (I := I) g₀ 0 3 i DA +
          iteratedCovGrad (I := I) g₀ 0 3 i DB -
          iteratedCovGrad (I := I) g₀ 0 3 i DC).toSection x) from by
      rw [SmoothCcTensor.toSection_smul]; rfl]
    rw [show ((iteratedCovGrad (I := I) g₀ 0 3 i DA +
          iteratedCovGrad (I := I) g₀ 0 3 i DB -
          iteratedCovGrad (I := I) g₀ 0 3 i DC).toSection x) =
        (iteratedCovGrad (I := I) g₀ 0 3 i DA).toSection x +
          (iteratedCovGrad (I := I) g₀ 0 3 i DB).toSection x -
          (iteratedCovGrad (I := I) g₀ 0 3 i DC).toSection x from by
      rw [SmoothCcTensor.toSection_sub, SmoothCcTensor.toSection_add]; rfl]
  set PA := (iteratedCovGrad (I := I) g₀ 0 3 i DA).toSection x with hPA
  set PB := (iteratedCovGrad (I := I) g₀ 0 3 i DB).toSection x with hPB
  set PC := (iteratedCovGrad (I := I) g₀ 0 3 i DC).toSection x with hPC
  set R2 : ℝ := riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 1)) x
    ((iteratedCovGrad (I := I) g₀ 0 2 (i + 1) T).toSection x) with hR2
  have hbA : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + i) x PA ≤ R2 :=
    hpermW (Equiv.swap (0 : Fin 3) 2)
  have hbB : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + i) x PB ≤ R2 :=
    hpermW (finRotate 3)
  have hbC : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + i) x PC ≤ R2 :=
    hpermW (Equiv.swap (1 : Fin 3) 2)
  rw [htoSec, riemannianFiberNormSq_smul_value (I := I) (M := M) g₀ 0 (3 + i) x (1 / 2 : ℝ)]
  have hnegC : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + i) x (-PC) =
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + i) x PC :=
    rfns_neg_pt (I := I) (M := M) g₀ 0 (3 + i) x PC
  have hR2_nn : 0 ≤ R2 := riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + (i + 1)) x _
  have hsum : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + i) x (PA + PB - PC) ≤
      10 * R2 := by
    have h1 := riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 0 (3 + i) x (PA + PB) (-PC)
    have h2 := riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 0 (3 + i) x PA PB
    rw [hnegC] at h1
    rw [show PA + PB - PC = (PA + PB) + (-PC) from sub_eq_add_neg _ _]
    nlinarith [h1, h2, hbA, hbB, hbC,
      riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (3 + i) x PA,
      riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (3 + i) x PB,
      riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (3 + i) x PC]
  nlinarith [hsum, hR2_nn,
    riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (3 + i) x (PA + PB - PC)]

set_option linter.unusedSectionVars false in
lemma rfns_sub_le_pt (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (a b : TensorRSSpace r s I x) :
    riemannianFiberNormSq (I := I) (M := M) g r s x (a - b) ≤
      2 * riemannianFiberNormSq (I := I) (M := M) g r s x a +
        2 * riemannianFiberNormSq (I := I) (M := M) g r s x b := by
  rw [sub_eq_add_neg]
  refine le_trans (riemannianFiberNormSq_add_le (I := I) (M := M) g r s x a (-b)) ?_
  rw [rfns_neg_pt (I := I) (M := M) g r s x b]

set_option linter.unusedVariables false in
lemma exists_rfns_icg_mvDoubleTraceField_window (s : ℕ) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ C : ℕ → ℝ, (∀ u, 0 ≤ C u) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
        (hbound : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (u K : ℕ) (huK : u ≤ K) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ (s + 2) (s + u) x
            ((iteratedCovGrad (I := I) g₀ (s + 2) s u
              (mvDoubleTraceField (I := I) (M := M) g₀ g₁ s)).toSection x) ≤
          C u * Combinatorics.boundedFactorGridWindow
            (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
              ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) K (u + 1) := by
  classical
  obtain ⟨CΛ, hCΛ_nn, hCΛ⟩ :=
    rfns_iteratedCovGrad_slotInsertEndoCc_zero_gInvDiffRaisedEndoField_diagonalProductGrid_le
      (I := I) (M := M) g₀ hδ₀
  set KD : ℕ → ℝ := fun u =>
    (exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ (s + 2) (s + u)
      (iteratedCovGrad (I := I) g₀ (s + 2) s u (cometricDoubleTraceField (I := I) g₀ s))).choose
    with hKD_def
  have hKD_nn : ∀ u, 0 ≤ KD u := fun u =>
    (exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ (s + 2) (s + u)
      (iteratedCovGrad (I := I) g₀ (s + 2) s u
        (cometricDoubleTraceField (I := I) g₀ s))).choose_spec.1
  have hKD : ∀ u (y : M),
      riemannianFiberNormSq (I := I) (M := M) g₀ (s + 2) (s + u) y
          ((iteratedCovGrad (I := I) g₀ (s + 2) s u
            (cometricDoubleTraceField (I := I) g₀ s)).toSection y) ≤ KD u := fun u =>
    (exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ (s + 2) (s + u)
      (iteratedCovGrad (I := I) g₀ (s + 2) s u
        (cometricDoubleTraceField (I := I) g₀ s))).choose_spec.2
  refine ⟨fun u => 2 * (appCcGdiag (E := E) u *
      ∑ u₁ ∈ Finset.range (u + 1), KD u₁ *
        ∑ u₂ ∈ Finset.range (u + 1 - u₁), (Module.finrank ℝ E : ℝ) ^ (s + 1) * CΛ u₂) +
      2 * KD u, fun u => by
    have h1 : 0 ≤ appCcGdiag (E := E) u *
        ∑ u₁ ∈ Finset.range (u + 1), KD u₁ *
          ∑ u₂ ∈ Finset.range (u + 1 - u₁), (Module.finrank ℝ E : ℝ) ^ (s + 1) * CΛ u₂ :=
      mul_nonneg (appCcGdiag_nonneg (E := E) u)
        (Finset.sum_nonneg fun u₁ _ => mul_nonneg (hKD_nn u₁)
          (Finset.sum_nonneg fun u₂ _ => mul_nonneg (by positivity) (hCΛ_nn u₂)))
    have h2 := hKD_nn u
    linarith, ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hbound u K huK x
  set b : ℕ → ℝ := fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
    ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x) with hb_def
  have hb_nn : ∀ l, 0 ≤ b l :=
    fun l => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + l) x _
  set W : ℝ := Combinatorics.boundedFactorGridWindow b K (u + 1) with hW_def
  have hW_nn : 0 ≤ W := Combinatorics.boundedFactorGridWindow_nonneg b hb_nn _ _
  have hW_one : 1 ≤ W := Combinatorics.one_le_boundedFactorGridWindow b hb_nn (by omega)
  have hsec : (iteratedCovGrad (I := I) g₀ (s + 2) s u
      (mvDoubleTraceField (I := I) (M := M) g₀ g₁ s)).toSection x =
      (iteratedCovGrad (I := I) g₀ (s + 2) s u
        (appCcRS (I := I) (M := M) g₀ (s + 2) (s + 2) s
          (cometricDoubleTraceField (I := I) g₀ s)
          (slotInsertEndoCc (I := I) (M := M) g₀ (s + 1)
            (gInvDiffRaisedEndoField (I := I) g₀ g₁)))).toSection x +
      (iteratedCovGrad (I := I) g₀ (s + 2) s u
        (cometricDoubleTraceField (I := I) g₀ s)).toSection x := by
    rw [show mvDoubleTraceField (I := I) (M := M) g₀ g₁ s =
        appCcRS (I := I) (M := M) g₀ (s + 2) (s + 2) s
          (cometricDoubleTraceField (I := I) g₀ s)
          (slotInsertEndoCc (I := I) (M := M) g₀ (s + 1)
            (gInvDiffRaisedEndoField (I := I) g₀ g₁)) +
        cometricDoubleTraceField (I := I) g₀ s from
      mvDoubleTraceField_cross_split (I := I) (M := M) g₀ g₁ s]
    rw [iteratedCovGrad_add (I := I) g₀ (s + 2) s u _ _, SmoothCcTensor.toSection_add]
    rfl
  rw [hsec]
  refine le_trans (riemannianFiberNormSq_add_le (I := I) (M := M) g₀ (s + 2) (s + u) x _ _) ?_
  have hSI : ∀ u₂ : ℕ, u₂ ≤ u →
      riemannianFiberNormSq (I := I) (M := M) g₀ (s + 2) ((s + 2) + u₂) x
          ((iteratedCovGrad (I := I) g₀ (s + 2) (s + 2) u₂
            (slotInsertEndoCc (I := I) (M := M) g₀ (s + 1)
              (gInvDiffRaisedEndoField (I := I) g₀ g₁))).toSection x) ≤
        ((Module.finrank ℝ E : ℝ) ^ (s + 1) * CΛ u₂) * W := by
    intro u₂ hu₂
    refine le_trans (rfns_iteratedCovGrad_slotInsertEndoCc_le_endo (I := I) (M := M) g₀
      (s + 1) (gInvDiffRaisedEndoField (I := I) g₀ g₁) u₂ x) ?_
    have hgrid := hCΛ g₁ P htie hδ_le hδ0 hbound u₂ x
    have hgw : (∑ n ∈ Finset.range (u₂ + 1),
        ∑ e ∈ Finset.Nat.antidiagonalTuple n u₂,
          ∏ m : Fin n, b (e m)) ≤ W := by
      rw [show (∑ n ∈ Finset.range (u₂ + 1),
          ∑ e ∈ Finset.Nat.antidiagonalTuple n u₂,
            ∏ m : Fin n, b (e m)) =
          Combinatorics.antidiagonalTupleGrid b u₂ from rfl]
      exact Combinatorics.antidiagonalTupleGrid_le_boundedFactorGridWindow b hb_nn
        (by omega) (by omega)
    calc (Module.finrank ℝ E : ℝ) ^ (s + 1) *
          riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + u₂) x
            ((iteratedCovGrad (I := I) g₀ 1 1 u₂
              (slotInsertEndoCc (I := I) (M := M) g₀ 0
                (gInvDiffRaisedEndoField (I := I) g₀ g₁))).toSection x)
        ≤ (Module.finrank ℝ E : ℝ) ^ (s + 1) * (CΛ u₂ *
            ∑ n ∈ Finset.range (u₂ + 1),
              ∑ e ∈ Finset.Nat.antidiagonalTuple n u₂,
                ∏ m : Fin n, b (e m)) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact hgrid
      _ ≤ (Module.finrank ℝ E : ℝ) ^ (s + 1) * (CΛ u₂ * W) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hgw (hCΛ_nn u₂)) (by positivity)
      _ = ((Module.finrank ℝ E : ℝ) ^ (s + 1) * CΛ u₂) * W := by ring
  have hQ : riemannianFiberNormSq (I := I) (M := M) g₀ (s + 2) (s + u) x
      ((iteratedCovGrad (I := I) g₀ (s + 2) s u
        (appCcRS (I := I) (M := M) g₀ (s + 2) (s + 2) s
          (cometricDoubleTraceField (I := I) g₀ s)
          (slotInsertEndoCc (I := I) (M := M) g₀ (s + 1)
            (gInvDiffRaisedEndoField (I := I) g₀ g₁)))).toSection x) ≤
      (appCcGdiag (E := E) u *
        ∑ u₁ ∈ Finset.range (u + 1), KD u₁ *
          ∑ u₂ ∈ Finset.range (u + 1 - u₁),
            (Module.finrank ℝ E : ℝ) ^ (s + 1) * CΛ u₂) * W := by
    refine le_trans (rfns_iteratedCovGrad_appCcRS_diagonalProductGrid_rankLeft_le (I := I)
      (M := M) g₀ u (s + 2) (s + 2) s (cometricDoubleTraceField (I := I) g₀ s)
      (slotInsertEndoCc (I := I) (M := M) g₀ (s + 1)
        (gInvDiffRaisedEndoField (I := I) g₀ g₁)) x) ?_
    calc appCcGdiag (E := E) u *
          ∑ u₁ ∈ Finset.range (u + 1),
            riemannianFiberNormSq (I := I) (M := M) g₀ (s + 2) (s + u₁) x
                ((iteratedCovGrad (I := I) g₀ (s + 2) s u₁
                  (cometricDoubleTraceField (I := I) g₀ s)).toSection x) *
              ∑ u₂ ∈ Finset.range (u + 1 - u₁),
                riemannianFiberNormSq (I := I) (M := M) g₀ (s + 2) ((s + 2) + u₂) x
                  ((iteratedCovGrad (I := I) g₀ (s + 2) (s + 2) u₂
                    (slotInsertEndoCc (I := I) (M := M) g₀ (s + 1)
                      (gInvDiffRaisedEndoField (I := I) g₀ g₁))).toSection x)
        ≤ appCcGdiag (E := E) u *
            ∑ u₁ ∈ Finset.range (u + 1), KD u₁ *
              ∑ u₂ ∈ Finset.range (u + 1 - u₁),
                (((Module.finrank ℝ E : ℝ) ^ (s + 1) * CΛ u₂) * W) := by
          refine mul_le_mul_of_nonneg_left
            (Finset.sum_le_sum fun u₁ hu₁ => ?_) (appCcGdiag_nonneg (E := E) u)
          refine mul_le_mul (hKD u₁ x) (Finset.sum_le_sum fun u₂ hu₂ => ?_)
            (Finset.sum_nonneg fun u₂ _ =>
              riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ (s + 2) ((s + 2) + u₂) x _)
            (hKD_nn u₁)
          rw [Finset.mem_range] at hu₁ hu₂
          exact hSI u₂ (by omega)
      _ = (appCcGdiag (E := E) u *
            ∑ u₁ ∈ Finset.range (u + 1), KD u₁ *
              ∑ u₂ ∈ Finset.range (u + 1 - u₁),
                (Module.finrank ℝ E : ℝ) ^ (s + 1) * CΛ u₂) * W := by
          have hstep : ∀ u₁ : ℕ, (KD u₁ *
              ∑ u₂ ∈ Finset.range (u + 1 - u₁),
                (((Module.finrank ℝ E : ℝ) ^ (s + 1) * CΛ u₂) * W)) =
              (KD u₁ * ∑ u₂ ∈ Finset.range (u + 1 - u₁),
                (Module.finrank ℝ E : ℝ) ^ (s + 1) * CΛ u₂) * W := by
            intro u₁
            rw [← Finset.sum_mul]
            ring
          rw [Finset.sum_congr rfl fun u₁ _ => hstep u₁, ← Finset.sum_mul]
          ring
  have hCDT : riemannianFiberNormSq (I := I) (M := M) g₀ (s + 2) (s + u) x
      ((iteratedCovGrad (I := I) g₀ (s + 2) s u
        (cometricDoubleTraceField (I := I) g₀ s)).toSection x) ≤ KD u * W := by
    calc riemannianFiberNormSq (I := I) (M := M) g₀ (s + 2) (s + u) x
          ((iteratedCovGrad (I := I) g₀ (s + 2) s u
            (cometricDoubleTraceField (I := I) g₀ s)).toSection x)
        ≤ KD u := hKD u x
      _ = KD u * 1 := by ring
      _ ≤ KD u * W := mul_le_mul_of_nonneg_left hW_one (hKD_nn u)
  calc 2 * riemannianFiberNormSq (I := I) (M := M) g₀ (s + 2) (s + u) x
        ((iteratedCovGrad (I := I) g₀ (s + 2) s u
          (appCcRS (I := I) (M := M) g₀ (s + 2) (s + 2) s
            (cometricDoubleTraceField (I := I) g₀ s)
            (slotInsertEndoCc (I := I) (M := M) g₀ (s + 1)
              (gInvDiffRaisedEndoField (I := I) g₀ g₁)))).toSection x) +
      2 * riemannianFiberNormSq (I := I) (M := M) g₀ (s + 2) (s + u) x
        ((iteratedCovGrad (I := I) g₀ (s + 2) s u
          (cometricDoubleTraceField (I := I) g₀ s)).toSection x)
      ≤ 2 * ((appCcGdiag (E := E) u *
            ∑ u₁ ∈ Finset.range (u + 1), KD u₁ *
              ∑ u₂ ∈ Finset.range (u + 1 - u₁),
                (Module.finrank ℝ E : ℝ) ^ (s + 1) * CΛ u₂) * W) + 2 * (KD u * W) := by
        have hnn := riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ (s + 2) (s + u) x
          ((iteratedCovGrad (I := I) g₀ (s + 2) s u
            (cometricDoubleTraceField (I := I) g₀ s)).toSection x)
        linarith [hQ, hCDT]
    _ = (2 * (appCcGdiag (E := E) u *
          ∑ u₁ ∈ Finset.range (u + 1), KD u₁ *
            ∑ u₂ ∈ Finset.range (u + 1 - u₁),
              (Module.finrank ℝ E : ℝ) ^ (s + 1) * CΛ u₂) + 2 * KD u) * W := by ring

set_option linter.unusedVariables false in

lemma exists_rfns_icg_mvPairTraceOp_window {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ C : ℕ → ℝ, (∀ u, 0 ≤ C u) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
        (hbound : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (u K : ℕ) (huK : u ≤ K) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 6 (2 + u) x
            ((iteratedCovGrad (I := I) g₀ 6 2 u
              (mvPairTraceOp (I := I) (M := M) g₀ g₁)).toSection x) ≤
          C u * Combinatorics.boundedFactorGridWindow
            (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
              ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) K (u + 1) := by
  classical
  obtain ⟨C2, hC2_nn, hC2⟩ :=
    exists_rfns_icg_mvDoubleTraceField_window (I := I) (M := M) g₀ 2 hδ₀
  obtain ⟨C4, hC4_nn, hC4⟩ :=
    exists_rfns_icg_mvDoubleTraceField_window (I := I) (M := M) g₀ 4 hδ₀
  refine ⟨fun u => appCcGdiag (E := E) u *
      ∑ u₁ ∈ Finset.range (u + 1), C2 u₁ *
        ∑ u₂ ∈ Finset.range (u + 1 - u₁),
          C4 u₂ * Combinatorics.windowPairCellCount (u₁ + 1) (u₂ + 1),
    fun u => mul_nonneg (appCcGdiag_nonneg (E := E) u)
      (Finset.sum_nonneg fun u₁ _ => mul_nonneg (hC2_nn u₁)
        (Finset.sum_nonneg fun u₂ _ => mul_nonneg (hC4_nn u₂)
          (Combinatorics.windowPairCellCount_nonneg _ _))), ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hbound u K huK x
  set b : ℕ → ℝ := fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
    ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x) with hb_def
  have hb_nn : ∀ l, 0 ≤ b l :=
    fun l => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + l) x _
  refine le_trans (rfns_iteratedCovGrad_appCcRS_diagonalProductGrid_rankLeft_le (I := I)
    (M := M) g₀ u 6 4 2 (mvDoubleTraceField (I := I) (M := M) g₀ g₁ 2)
    (mvDoubleTraceField (I := I) (M := M) g₀ g₁ 4) x) ?_
  calc appCcGdiag (E := E) u *
        ∑ u₁ ∈ Finset.range (u + 1),
          riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + u₁) x
              ((iteratedCovGrad (I := I) g₀ 4 2 u₁
                (mvDoubleTraceField (I := I) (M := M) g₀ g₁ 2)).toSection x) *
            ∑ u₂ ∈ Finset.range (u + 1 - u₁),
              riemannianFiberNormSq (I := I) (M := M) g₀ 6 (4 + u₂) x
                ((iteratedCovGrad (I := I) g₀ 6 4 u₂
                  (mvDoubleTraceField (I := I) (M := M) g₀ g₁ 4)).toSection x)
      ≤ appCcGdiag (E := E) u *
          ∑ u₁ ∈ Finset.range (u + 1),
            (C2 u₁ * Combinatorics.boundedFactorGridWindow b K (u₁ + 1)) *
            ∑ u₂ ∈ Finset.range (u + 1 - u₁),
              (C4 u₂ * Combinatorics.boundedFactorGridWindow b K (u₂ + 1)) := by
        refine mul_le_mul_of_nonneg_left
          (Finset.sum_le_sum fun u₁ hu₁ => ?_) (appCcGdiag_nonneg (E := E) u)
        rw [Finset.mem_range] at hu₁
        refine mul_le_mul (hC2 g₁ P htie hδ_le hδ0 hbound u₁ K (by omega) x)
          (Finset.sum_le_sum fun u₂ hu₂ => ?_)
          (Finset.sum_nonneg fun u₂ _ =>
            riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 6 (4 + u₂) x _)
          (mul_nonneg (hC2_nn u₁)
            (Combinatorics.boundedFactorGridWindow_nonneg b hb_nn _ _))
        rw [Finset.mem_range] at hu₂
        exact hC4 g₁ P htie hδ_le hδ0 hbound u₂ K (by omega) x
    _ ≤ (appCcGdiag (E := E) u *
          ∑ u₁ ∈ Finset.range (u + 1), C2 u₁ *
            ∑ u₂ ∈ Finset.range (u + 1 - u₁),
              C4 u₂ * Combinatorics.windowPairCellCount (u₁ + 1) (u₂ + 1)) *
          Combinatorics.boundedFactorGridWindow b K (u + 1) := by
        rw [mul_assoc]
        refine mul_le_mul_of_nonneg_left ?_ (appCcGdiag_nonneg (E := E) u)
        rw [Finset.sum_mul]
        refine Finset.sum_le_sum fun u₁ hu₁ => ?_
        rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_le_sum fun u₂ hu₂ => ?_
        rw [Finset.mem_range] at hu₁ hu₂
        calc C2 u₁ * Combinatorics.boundedFactorGridWindow b K (u₁ + 1) *
              (C4 u₂ * Combinatorics.boundedFactorGridWindow b K (u₂ + 1))
            = (C2 u₁ * C4 u₂) *
                (Combinatorics.boundedFactorGridWindow b K (u₁ + 1) *
                  Combinatorics.boundedFactorGridWindow b K (u₂ + 1)) := by ring
          _ ≤ (C2 u₁ * C4 u₂) *
                (Combinatorics.windowPairCellCount (u₁ + 1) (u₂ + 1) *
                  Combinatorics.boundedFactorGridWindow b K ((u₁ + 1) + (u₂ + 1) - 1)) := by
              refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (hC2_nn u₁) (hC4_nn u₂))
              exact Combinatorics.boundedFactorGridWindow_mul_le b hb_nn K (u₁ + 1) (u₂ + 1)
                (by omega) (by omega)
          _ ≤ (C2 u₁ * C4 u₂) *
                (Combinatorics.windowPairCellCount (u₁ + 1) (u₂ + 1) *
                  Combinatorics.boundedFactorGridWindow b K (u + 1)) := by
              refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (hC2_nn u₁) (hC4_nn u₂))
              refine mul_le_mul_of_nonneg_left ?_
                (Combinatorics.windowPairCellCount_nonneg _ _)
              exact Combinatorics.boundedFactorGridWindow_mono b hb_nn (le_refl _) (by omega)
          _ = C2 u₁ * (C4 u₂ * Combinatorics.windowPairCellCount (u₁ + 1) (u₂ + 1)) *
                Combinatorics.boundedFactorGridWindow b K (u + 1) := by ring

def ricciFoldWeightA (S : SmoothCcTensor g₀ 0 2) : SmoothCcTensor g₀ 0 4 :=
  appCcRS (I := I) (M := M) g₀ 0 6 4 (cometricDoubleTraceField (I := I) g₀ 4)
    (rsDomDomCongrSection (I := I) (M := M) g₀ 0 6 (Equiv.swap (1 : Fin 6) 3)
      (appCcRS (I := I) (M := M) g₀ 0 2 6
        (slotExtendIter (I := I) (M := M) g₀ 0 4 2
          (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀)) S))

def ricciFoldWeightB (S : SmoothCcTensor g₀ 0 2) : SmoothCcTensor g₀ 0 4 :=
  appCcRS (I := I) (M := M) g₀ 0 6 4 (cometricDoubleTraceField (I := I) g₀ 4)
    (rsDomDomCongrSection (I := I) (M := M) g₀ 0 6 tauK3b
      (appCcRS (I := I) (M := M) g₀ 0 2 6
        (slotExtendIter (I := I) (M := M) g₀ 0 4 2
          (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀)) S))

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
set_option maxHeartbeats 12800000 in
private lemma ricciFoldWeight_unitModel_gen (σ : Equiv.Perm (Fin 6))
    (S : SmoothCcTensor g₀ 0 2) (x : M) (m : Fin 4 → E) :
    unitModel (I := I) (M := M) g₀ 4
        (appCcRS (I := I) (M := M) g₀ 0 6 4 (cometricDoubleTraceField (I := I) g₀ 4)
          (rsDomDomCongrSection (I := I) (M := M) g₀ 0 6 σ
            (appCcRS (I := I) (M := M) g₀ 0 2 6
              (slotExtendIter (I := I) (M := M) g₀ 0 4 2
                (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀)) S))) x m =
      ∑ e : Fin (Module.finrank ℝ E),
        unitModel (I := I) (M := M) g₀ 2 S x
            ![((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
                (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E) m) :
                  Fin 6 → E) (σ 0)),
              ((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
                (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E) m) :
                  Fin 6 → E) (σ 1))] *
          unitModel (I := I) (M := M) g₀ 4
            (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀) x
            ![((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
                (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E) m) :
                  Fin 6 → E) (σ 2)),
              ((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
                (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E) m) :
                  Fin 6 → E) (σ 3)),
              ((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
                (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E) m) :
                  Fin 6 → E) (σ 4)),
              ((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
                (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E) m) :
                  Fin 6 → E) (σ 5))] := by
  classical
  set R4 : SmoothCcTensor g₀ 0 4 := riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀ with hR4_def
  set Sval : Tensor0SSpace 2 I x :=
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from S.toSection x)
      (unitTensor (I := I) (M := M) x) with hSval_def
  set Y : Tensor0SSpace 6 I x :=
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 6 I x from
      (rsDomDomCongrSection (I := I) (M := M) g₀ 0 6 σ
        (appCcRS (I := I) (M := M) g₀ 0 2 6
          (slotExtendIter (I := I) (M := M) g₀ 0 4 2 R4) S)).toSection x)
      (unitTensor (I := I) (M := M) x) with hY_def
  have hYval : ∀ w : Fin 6 → TangentSpace I x,
      Tensor0SSpace.toModel Y w =
        Tensor0SSpace.toModel Sval ![(w (σ 0) : E), (w (σ 1) : E)] *
          unitModel (I := I) (M := M) g₀ 4 R4 x
            ![(w (σ 2) : E), (w (σ 3) : E), (w (σ 4) : E), (w (σ 5) : E)] := by
    intro w
    rw [hY_def]
    rw [show ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 6 I x from
        (rsDomDomCongrSection (I := I) (M := M) g₀ 0 6 σ
          (appCcRS (I := I) (M := M) g₀ 0 2 6
            (slotExtendIter (I := I) (M := M) g₀ 0 4 2 R4) S)).toSection x)
        (unitTensor (I := I) (M := M) x)) =
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 6 I x from
          rsDomDomCongr σ
            ((appCcRS (I := I) (M := M) g₀ 0 2 6
              (slotExtendIter (I := I) (M := M) g₀ 0 4 2 R4) S).toSection x))
          (unitTensor (I := I) (M := M) x)) from by
      rw [rsDomDomCongrSection_toSection]]
    rw [toModel_rsDomDomCongr_apply (I := I) (M := M) σ
      ((appCcRS (I := I) (M := M) g₀ 0 2 6
        (slotExtendIter (I := I) (M := M) g₀ 0 4 2 R4) S).toSection x)
      (unitTensor (I := I) (M := M) x)]
    rw [ContinuousMultilinearMap.domDomCongr_apply]
    rw [show ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 6 I x from
        (appCcRS (I := I) (M := M) g₀ 0 2 6
          (slotExtendIter (I := I) (M := M) g₀ 0 4 2 R4) S).toSection x)
        (unitTensor (I := I) (M := M) x)) =
        ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 6 I x from
          (slotExtendIter (I := I) (M := M) g₀ 0 4 2 R4).toSection x) Sval) from by
      rw [appCcRS_toSection]
      rfl]
    rw [slotExtendIter_two_toModel (I := I) (M := M) g₀ R4 x Sval (fun i => w (σ i))]
    refine congrArg₂ (· * ·) ?_ ?_
    · refine congrArg _ ?_
      funext k
      fin_cases k <;> rfl
    · rw [show unitModel (I := I) (M := M) g₀ 4 R4 x
          (fun k : Fin 4 => ((fun i => w (σ i)) (Fin.natAdd 2 k) : E)) =
          unitModel (I := I) (M := M) g₀ 4 R4 x
            ![(w (σ 2) : E), (w (σ 3) : E), (w (σ 4) : E), (w (σ 5) : E)] from by
        refine congrArg _ ?_
        funext k
        fin_cases k <;> rfl]
  rw [show unitModel (I := I) (M := M) g₀ 4
      (appCcRS (I := I) (M := M) g₀ 0 6 4 (cometricDoubleTraceField (I := I) g₀ 4)
        (rsDomDomCongrSection (I := I) (M := M) g₀ 0 6 σ
          (appCcRS (I := I) (M := M) g₀ 0 2 6
            (slotExtendIter (I := I) (M := M) g₀ 0 4 2 R4) S))) x =
      Tensor0SSpace.toModel (cometricDoubleTraceFib (I := I) g₀ 4 x Y) from by
    rw [unitModel, hY_def]
    rw [appCcRS_toSection]
    rfl]
  rw [cometricDoubleTraceFib_toModel (I := I) g₀ 4 x Y]
  rw [modelDoubleTrace_apply (E := E) 4 (cometricLmodel (I := I) g₀ x)]
  rw [cometric_dualTrace_eq_orthoFrame_diag (I := I) g₀ x
    (mem_smoothOrthoFrameNbhd_self (I := I) (M := M) x)
    (Tensor0SSpace.toModel Y) m]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [hYval]
  rfl

set_option linter.unusedSectionVars false in
private lemma ccTensorBilin_expand_left (S : SmoothCcTensor g₀ 0 2) (x : M)
    (u w : TangentSpace I x) :
    ccTensorBilin (I := I) g₀ S x u w =
      ∑ e : Fin (Module.finrank ℝ E),
        g₀.inner x u (smoothOrthoFrame (I := I) g₀ x e x) *
          ccTensorBilin (I := I) g₀ S x (smoothOrthoFrame (I := I) g₀ x e x) w := by
  conv_lhs => rw [orthoFrame_expansion_at_center (I := I) (M := M) g₀ x u]
  rw [map_sum (ccTensorBilin (I := I) g₀ S x) _ Finset.univ, ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [map_smul (ccTensorBilin (I := I) g₀ S x), ContinuousLinearMap.smul_apply, smul_eq_mul]

set_option linter.unusedSectionVars false in
private lemma ccTensorBilin_expand_right (S : SmoothCcTensor g₀ 0 2) (x : M)
    (u w : TangentSpace I x) :
    ccTensorBilin (I := I) g₀ S x u w =
      ∑ e : Fin (Module.finrank ℝ E),
        g₀.inner x w (smoothOrthoFrame (I := I) g₀ x e x) *
          ccTensorBilin (I := I) g₀ S x u (smoothOrthoFrame (I := I) g₀ x e x) := by
  conv_lhs => rw [orthoFrame_expansion_at_center (I := I) (M := M) g₀ x w]
  rw [map_sum (ccTensorBilin (I := I) g₀ S x u) _ Finset.univ]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [map_smul (ccTensorBilin (I := I) g₀ S x u), smul_eq_mul]

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
set_option maxHeartbeats 12800000 in
private lemma ricciFoldWeights_unitModel_eq_kernel (S : SmoothCcTensor g₀ 0 2) (x : M)
    (p q v0 v1 : TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 4
        (ricciFoldWeightA (I := I) (M := M) g₀ S +
          ricciFoldWeightB (I := I) (M := M) g₀ S) x
        ![(v0 : E), (v1 : E), (p : E), (q : E)] =
      ccTensorBilin (I := I) g₀ S x (riemannOp (LeviCivita (I := I) g₀) x v0 p q) v1 +
        ccTensorBilin (I := I) g₀ S x q (riemannOp (LeviCivita (I := I) g₀) x v0 p v1) := by
  classical
  rw [unitModel_add_pt (I := I) (M := M) g₀ 4
    (ricciFoldWeightA (I := I) (M := M) g₀ S) (ricciFoldWeightB (I := I) (M := M) g₀ S) x,
    ContinuousMultilinearMap.add_apply]
  have hA : unitModel (I := I) (M := M) g₀ 4 (ricciFoldWeightA (I := I) (M := M) g₀ S) x
      ![(v0 : E), (v1 : E), (p : E), (q : E)] =
      ccTensorBilin (I := I) g₀ S x (riemannOp (LeviCivita (I := I) g₀) x v0 p q) v1 := by
    rw [show ricciFoldWeightA (I := I) (M := M) g₀ S =
        appCcRS (I := I) (M := M) g₀ 0 6 4 (cometricDoubleTraceField (I := I) g₀ 4)
          (rsDomDomCongrSection (I := I) (M := M) g₀ 0 6 (Equiv.swap (1 : Fin 6) 3)
            (appCcRS (I := I) (M := M) g₀ 0 2 6
              (slotExtendIter (I := I) (M := M) g₀ 0 4 2
                (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀)) S)) from rfl]
    rw [ricciFoldWeight_unitModel_gen (I := I) (M := M) g₀ (Equiv.swap (1 : Fin 6) 3) S x
      ![(v0 : E), (v1 : E), (p : E), (q : E)]]
    rw [ccTensorBilin_expand_left (I := I) (M := M) g₀ S x
      (riemannOp (LeviCivita (I := I) g₀) x v0 p q) v1]
    refine Finset.sum_congr rfl fun e _ => ?_
    have h1 : unitModel (I := I) (M := M) g₀ 2 S x
        ![((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
              ![(v0 : E), (v1 : E), (p : E), (q : E)]) : Fin 6 → E)
            ((Equiv.swap (1 : Fin 6) 3) 0)),
          ((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
              ![(v0 : E), (v1 : E), (p : E), (q : E)]) : Fin 6 → E)
            ((Equiv.swap (1 : Fin 6) 3) 1))] =
        unitModel (I := I) (M := M) g₀ 2 S x
          ![((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E), (v1 : E)] := by
      refine congrArg _ ?_
      funext k
      fin_cases k <;> rfl
    have h2 : unitModel (I := I) (M := M) g₀ 4
        (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀) x
        ![((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
              ![(v0 : E), (v1 : E), (p : E), (q : E)]) : Fin 6 → E)
            ((Equiv.swap (1 : Fin 6) 3) 2)),
          ((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
              ![(v0 : E), (v1 : E), (p : E), (q : E)]) : Fin 6 → E)
            ((Equiv.swap (1 : Fin 6) 3) 3)),
          ((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
              ![(v0 : E), (v1 : E), (p : E), (q : E)]) : Fin 6 → E)
            ((Equiv.swap (1 : Fin 6) 3) 4)),
          ((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
              ![(v0 : E), (v1 : E), (p : E), (q : E)]) : Fin 6 → E)
            ((Equiv.swap (1 : Fin 6) 3) 5))] =
        g₀.inner x (riemannOp (LeviCivita (I := I) g₀) x v0 p q)
          (smoothOrthoFrame (I := I) g₀ x e x) := by
      rw [show (![((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
              ![(v0 : E), (v1 : E), (p : E), (q : E)]) : Fin 6 → E)
            ((Equiv.swap (1 : Fin 6) 3) 2)),
          ((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
              ![(v0 : E), (v1 : E), (p : E), (q : E)]) : Fin 6 → E)
            ((Equiv.swap (1 : Fin 6) 3) 3)),
          ((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
              ![(v0 : E), (v1 : E), (p : E), (q : E)]) : Fin 6 → E)
            ((Equiv.swap (1 : Fin 6) 3) 4)),
          ((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
              ![(v0 : E), (v1 : E), (p : E), (q : E)]) : Fin 6 → E)
            ((Equiv.swap (1 : Fin 6) 3) 5))] : Fin 4 → E) =
          ![(v0 : E), ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E),
            (p : E), (q : E)] from by
        funext k
        fin_cases k <;> rfl]
      rw [riemannLoweredCc_unitModel_apply (I := I) (M := M) g₀ g₀ g₀ x
        ![(v0 : E), ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E),
          (p : E), (q : E)]]
      rfl
    rw [h1, h2]
    rw [unitModel_eq_ccTensorBilin_pt (I := I) (M := M) g₀ S x
      (smoothOrthoFrame (I := I) g₀ x e x) v1]
    ring
  have hB : unitModel (I := I) (M := M) g₀ 4 (ricciFoldWeightB (I := I) (M := M) g₀ S) x
      ![(v0 : E), (v1 : E), (p : E), (q : E)] =
      ccTensorBilin (I := I) g₀ S x q (riemannOp (LeviCivita (I := I) g₀) x v0 p v1) := by
    rw [show ricciFoldWeightB (I := I) (M := M) g₀ S =
        appCcRS (I := I) (M := M) g₀ 0 6 4 (cometricDoubleTraceField (I := I) g₀ 4)
          (rsDomDomCongrSection (I := I) (M := M) g₀ 0 6 tauK3b
            (appCcRS (I := I) (M := M) g₀ 0 2 6
              (slotExtendIter (I := I) (M := M) g₀ 0 4 2
                (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀)) S)) from rfl]
    rw [ricciFoldWeight_unitModel_gen (I := I) (M := M) g₀ tauK3b S x
      ![(v0 : E), (v1 : E), (p : E), (q : E)]]
    rw [ccTensorBilin_expand_right (I := I) (M := M) g₀ S x q
      (riemannOp (LeviCivita (I := I) g₀) x v0 p v1)]
    refine Finset.sum_congr rfl fun e _ => ?_
    have h1 : unitModel (I := I) (M := M) g₀ 2 S x
        ![((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
              ![(v0 : E), (v1 : E), (p : E), (q : E)]) : Fin 6 → E)
            (tauK3b 0)),
          ((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
              ![(v0 : E), (v1 : E), (p : E), (q : E)]) : Fin 6 → E)
            (tauK3b 1))] =
        unitModel (I := I) (M := M) g₀ 2 S x
          ![(q : E), ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)] := by
      refine congrArg _ ?_
      funext k
      fin_cases k <;> rfl
    have h2 : unitModel (I := I) (M := M) g₀ 4
        (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀) x
        ![((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
              ![(v0 : E), (v1 : E), (p : E), (q : E)]) : Fin 6 → E)
            (tauK3b 2)),
          ((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
              ![(v0 : E), (v1 : E), (p : E), (q : E)]) : Fin 6 → E)
            (tauK3b 3)),
          ((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
              ![(v0 : E), (v1 : E), (p : E), (q : E)]) : Fin 6 → E)
            (tauK3b 4)),
          ((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
              ![(v0 : E), (v1 : E), (p : E), (q : E)]) : Fin 6 → E)
            (tauK3b 5))] =
        g₀.inner x (riemannOp (LeviCivita (I := I) g₀) x v0 p v1)
          (smoothOrthoFrame (I := I) g₀ x e x) := by
      rw [show (![((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
              ![(v0 : E), (v1 : E), (p : E), (q : E)]) : Fin 6 → E)
            (tauK3b 2)),
          ((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
              ![(v0 : E), (v1 : E), (p : E), (q : E)]) : Fin 6 → E)
            (tauK3b 3)),
          ((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
              ![(v0 : E), (v1 : E), (p : E), (q : E)]) : Fin 6 → E)
            (tauK3b 4)),
          ((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
              ![(v0 : E), (v1 : E), (p : E), (q : E)]) : Fin 6 → E)
            (tauK3b 5))] : Fin 4 → E) =
          ![(v0 : E), ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E),
            (p : E), (v1 : E)] from by
        funext k
        fin_cases k <;> rfl]
      rw [riemannLoweredCc_unitModel_apply (I := I) (M := M) g₀ g₀ g₀ x
        ![(v0 : E), ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E),
          (p : E), (v1 : E)]]
      rfl
    rw [h1, h2]
    rw [show unitModel (I := I) (M := M) g₀ 2 S x
        ![(q : E), ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)] =
        ccTensorBilin (I := I) g₀ S x q (smoothOrthoFrame (I := I) g₀ x e x) from
      unitModel_eq_ccTensorBilin_pt (I := I) (M := M) g₀ S x q
        (smoothOrthoFrame (I := I) g₀ x e x)]
    ring
  rw [hA, hB]

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
set_option maxHeartbeats 12800000 in
lemma ricciFoldRemainderField_eq_refold (S : SmoothCcTensor g₀ 0 2) :
    ricciArmRicciFoldRemainderField (I := I) (M := M) g₀ g₁ S =
      (-(1 / 2) : ℝ) •
        appCcRS (I := I) (M := M) g₀ 2 6 2 (mvPairTraceOp (I := I) (M := M) g₀ g₁)
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE
            (slotExtendIter (I := I) (M := M) g₀ 0 4 2
              (ricciFoldWeightA (I := I) (M := M) g₀ S +
                ricciFoldWeightB (I := I) (M := M) g₀ S))) := by
  classical
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply tensorRSSpace_ext 2 2 x
  intro D
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro v
  beta_reduce
  have hRHSsmul : ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
      (((-(1 / 2) : ℝ) •
        appCcRS (I := I) (M := M) g₀ 2 6 2 (mvPairTraceOp (I := I) (M := M) g₀ g₁)
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE
            (slotExtendIter (I := I) (M := M) g₀ 0 4 2
              (ricciFoldWeightA (I := I) (M := M) g₀ S +
                ricciFoldWeightB (I := I) (M := M) g₀ S)))).toSection x)) D) =
      (-(1 / 2) : ℝ) • ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        (appCcRS (I := I) (M := M) g₀ 2 6 2 (mvPairTraceOp (I := I) (M := M) g₀ g₁)
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE
            (slotExtendIter (I := I) (M := M) g₀ 0 4 2
              (ricciFoldWeightA (I := I) (M := M) g₀ S +
                ricciFoldWeightB (I := I) (M := M) g₀ S)))).toSection x) D) := by
    rw [show ((((-(1 / 2) : ℝ) •
        appCcRS (I := I) (M := M) g₀ 2 6 2 (mvPairTraceOp (I := I) (M := M) g₀ g₁)
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE
            (slotExtendIter (I := I) (M := M) g₀ 0 4 2
              (ricciFoldWeightA (I := I) (M := M) g₀ S +
                ricciFoldWeightB (I := I) (M := M) g₀ S)))).toSection x)) =
        (-(1 / 2) : ℝ) •
          ((appCcRS (I := I) (M := M) g₀ 2 6 2 (mvPairTraceOp (I := I) (M := M) g₀ g₁)
            (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE
              (slotExtendIter (I := I) (M := M) g₀ 0 4 2
                (ricciFoldWeightA (I := I) (M := M) g₀ S +
                  ricciFoldWeightB (I := I) (M := M) g₀ S)))).toSection x) from by
      rw [SmoothCcTensor.toSection_smul]; rfl]
    rfl
  rw [hRHSsmul, Tensor0SSpace.toModel_smul, ContinuousMultilinearMap.smul_apply, smul_eq_mul]
  rw [mvPairTraceOp_apply_toModel (I := I) (M := M) g₀ g₁
    (ricciFoldWeightA (I := I) (M := M) g₀ S + ricciFoldWeightB (I := I) (M := M) g₀ S) x D v]
  rw [show ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
      (ricciArmRicciFoldRemainderField (I := I) (M := M) g₀ g₁ S).toSection x) D) =
      ricciFoldBiContrFib (I := I) g₀ g₁ S x D from rfl]
  rw [show ricciFoldBiContrFib (I := I) g₀ g₁ S x =
      ricciFoldBiContrFibFixedFrame (I := I) g₀ S (smoothOrthoFrame (I := I) g₁ x) x from rfl]
  rw [ricciFoldBiContrFibFixedFrame_toModel (I := I) g₀ S (smoothOrthoFrame (I := I) g₁ x) x D v]
  rw [Finset.sum_comm]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [ricciFoldKernelBilin_apply (I := I) g₀ S x
    (smoothOrthoFrame (I := I) g₁ x a x) (smoothOrthoFrame (I := I) g₁ x b x) (v 0) (v 1)]
  rw [show unitModel (I := I) (M := M) g₀ 4
      (ricciFoldWeightA (I := I) (M := M) g₀ S + ricciFoldWeightB (I := I) (M := M) g₀ S) x
      ![v 0, v 1, (smoothOrthoFrame (I := I) g₁ x a x : E),
        (smoothOrthoFrame (I := I) g₁ x b x : E)] =
      ccTensorBilin (I := I) g₀ S x
          (riemannOp (LeviCivita (I := I) g₀) x (v 0) (smoothOrthoFrame (I := I) g₁ x a x)
            (smoothOrthoFrame (I := I) g₁ x b x)) (v 1) +
        ccTensorBilin (I := I) g₀ S x (smoothOrthoFrame (I := I) g₁ x b x)
          (riemannOp (LeviCivita (I := I) g₀) x (v 0) (smoothOrthoFrame (I := I) g₁ x a x)
            (v 1)) from
    ricciFoldWeights_unitModel_eq_kernel (I := I) (M := M) g₀ S x
      (smoothOrthoFrame (I := I) g₁ x a x) (smoothOrthoFrame (I := I) g₁ x b x)
      (v 0) (v 1)]
  ring

set_option linter.unusedSectionVars false in
private lemma single_b_le_grid (b : ℕ → ℝ) (hb : ∀ j, 0 ≤ b j) (q : ℕ) (hq : 1 ≤ q) :
    b q ≤ Combinatorics.antidiagonalTupleGrid b q := by
  have h := Combinatorics.single_factor_mul_antidiagonalTupleGrid_le b hb 0 q hq
  rw [Combinatorics.antidiagonalTupleGrid_zero, mul_one] at h
  rwa [zero_add] at h

set_option linter.unusedVariables false in
lemma exists_rfns_icg_ricciFoldWeightGen_window (σ : Equiv.Perm (Fin 6))
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ C : ℕ → ℝ, (∀ w, 0 ≤ C w) ∧
      ∀ (P : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
        (hbound : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (w K : ℕ) (hwK : w ≤ K) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + w) x
            ((iteratedCovGrad (I := I) g₀ 0 4 w
              (appCcRS (I := I) (M := M) g₀ 0 6 4 (cometricDoubleTraceField (I := I) g₀ 4)
                (rsDomDomCongrSection (I := I) (M := M) g₀ 0 6 σ
                  (appCcRS (I := I) (M := M) g₀ 0 2 6
                    (slotExtendIter (I := I) (M := M) g₀ 0 4 2
                      (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀))
                    (symmS (I := I) g₀ P))))).toSection x) ≤
          C w * Combinatorics.boundedFactorGridWindow
            (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
              ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) K (w + 1) := by
  classical
  set fr : ℝ := (Module.finrank ℝ E : ℝ) with hfr_def
  set KD : ℕ → ℝ := fun u =>
    (exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ 6 (4 + u)
      (iteratedCovGrad (I := I) g₀ 6 4 u (cometricDoubleTraceField (I := I) g₀ 4))).choose
    with hKD_def
  have hKD_nn : ∀ u, 0 ≤ KD u := fun u =>
    (exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ 6 (4 + u)
      (iteratedCovGrad (I := I) g₀ 6 4 u
        (cometricDoubleTraceField (I := I) g₀ 4))).choose_spec.1
  have hKD : ∀ u (y : M),
      riemannianFiberNormSq (I := I) (M := M) g₀ 6 (4 + u) y
          ((iteratedCovGrad (I := I) g₀ 6 4 u
            (cometricDoubleTraceField (I := I) g₀ 4)).toSection y) ≤ KD u := fun u =>
    (exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ 6 (4 + u)
      (iteratedCovGrad (I := I) g₀ 6 4 u
        (cometricDoubleTraceField (I := I) g₀ 4))).choose_spec.2
  set KS : ℕ → ℝ := fun u =>
    (exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ 2 (6 + u)
      (iteratedCovGrad (I := I) g₀ 2 6 u
        (slotExtendIter (I := I) (M := M) g₀ 0 4 2
          (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀)))).choose with hKS_def
  have hKS_nn : ∀ u, 0 ≤ KS u := fun u =>
    (exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ 2 (6 + u)
      (iteratedCovGrad (I := I) g₀ 2 6 u
        (slotExtendIter (I := I) (M := M) g₀ 0 4 2
          (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀)))).choose_spec.1
  have hKS : ∀ u (y : M),
      riemannianFiberNormSq (I := I) (M := M) g₀ 2 (6 + u) y
          ((iteratedCovGrad (I := I) g₀ 2 6 u
            (slotExtendIter (I := I) (M := M) g₀ 0 4 2
              (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀))).toSection y) ≤ KS u := fun u =>
    (exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ 2 (6 + u)
      (iteratedCovGrad (I := I) g₀ 2 6 u
        (slotExtendIter (I := I) (M := M) g₀ 0 4 2
          (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀)))).choose_spec.2
  refine ⟨fun w => appCcGdiag (E := E) w *
      ∑ w₁ ∈ Finset.range (w + 1), KD w₁ *
        ∑ w₂ ∈ Finset.range (w + 1 - w₁),
          appCcGdiag (E := E) w₂ *
            ∑ w₃ ∈ Finset.range (w₂ + 1), KS w₃ *
              ∑ w₄ ∈ Finset.range (w₂ + 1 - w₃), (fr ^ 2 + 1),
    fun w => by
      refine mul_nonneg (appCcGdiag_nonneg (E := E) w)
        (Finset.sum_nonneg fun w₁ _ => mul_nonneg (hKD_nn w₁)
          (Finset.sum_nonneg fun w₂ _ => mul_nonneg (appCcGdiag_nonneg (E := E) w₂)
            (Finset.sum_nonneg fun w₃ _ => mul_nonneg (hKS_nn w₃)
              (Finset.sum_nonneg fun w₄ _ => by positivity)))), ?_⟩
  intro P δ hδ_le hδ0 hbound w K hwK x
  set b : ℕ → ℝ := fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
    ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x) with hb_def
  have hb_nn : ∀ l, 0 ≤ b l :=
    fun l => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + l) x _
  set W : ℝ := Combinatorics.boundedFactorGridWindow b K (w + 1) with hW_def
  have hW_nn : 0 ≤ W := Combinatorics.boundedFactorGridWindow_nonneg b hb_nn _ _
  have hW_one : 1 ≤ W := Combinatorics.one_le_boundedFactorGridWindow b hb_nn (by omega)
  have hS : ∀ w₄ : ℕ, w₄ ≤ w →
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + w₄) x
          ((iteratedCovGrad (I := I) g₀ 0 2 w₄
            (symmS (I := I) g₀ P)).toSection x) ≤ (fr ^ 2 + 1) * W := by
    intro w₄ hw₄
    match w₄, hw₄ with
    | 0, _ =>
        rw [iteratedCovGrad_zero]
        have hδ1 : δ ^ 2 ≤ 1 := by nlinarith
        have h0 := rfns_symmS_zero_le_of_ball (I := I) (M := M) g₀ P hδ0 hbound x
        calc riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x
              ((symmS (I := I) (M := M) g₀ P).toSection x)
            ≤ fr ^ 2 * δ ^ 2 := h0
          _ ≤ fr ^ 2 * 1 := by
              refine mul_le_mul_of_nonneg_left hδ1 ?_
              positivity
          _ ≤ (fr ^ 2 + 1) * 1 := by nlinarith
          _ ≤ (fr ^ 2 + 1) * W := by
              refine mul_le_mul_of_nonneg_left hW_one ?_
              positivity
    | (k + 1), hw₄ =>
        refine le_trans (rfns_iteratedCovGrad_symmS_pointwise (I := I) (M := M) g₀ P
          (k + 1) x) ?_
        calc b (k + 1)
            ≤ Combinatorics.antidiagonalTupleGrid b (k + 1) :=
              single_b_le_grid b hb_nn (k + 1) (by omega)
          _ ≤ Combinatorics.boundedFactorGridWindow b K (w + 1) :=
              Combinatorics.antidiagonalTupleGrid_le_boundedFactorGridWindow b hb_nn
                (by omega) (by omega)
          _ ≤ (fr ^ 2 + 1) * W := by
              rw [← hW_def]
              nlinarith [hW_nn]
  have hBase : ∀ w₂ : ℕ, w₂ ≤ w →
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (6 + w₂) x
          ((iteratedCovGrad (I := I) g₀ 0 6 w₂
            (rsDomDomCongrSection (I := I) (M := M) g₀ 0 6 σ
              (appCcRS (I := I) (M := M) g₀ 0 2 6
                (slotExtendIter (I := I) (M := M) g₀ 0 4 2
                  (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀))
                (symmS (I := I) g₀ P)))).toSection x) ≤
        (appCcGdiag (E := E) w₂ *
          ∑ w₃ ∈ Finset.range (w₂ + 1), KS w₃ *
            ∑ w₄ ∈ Finset.range (w₂ + 1 - w₃), (fr ^ 2 + 1)) * W := by
    intro w₂ hw₂
    rw [rfns_icg_rsDomDomCongrSection_eq (I := I) (M := M) g₀ 0 6 σ _ w₂ x]
    refine le_trans (rfns_iteratedCovGrad_appCcRS_diagonalProductGrid_rankLeft_le (I := I)
      (M := M) g₀ w₂ 0 2 6
      (slotExtendIter (I := I) (M := M) g₀ 0 4 2
        (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀))
      (symmS (I := I) g₀ P) x) ?_
    calc appCcGdiag (E := E) w₂ *
          ∑ w₃ ∈ Finset.range (w₂ + 1),
            riemannianFiberNormSq (I := I) (M := M) g₀ 2 (6 + w₃) x
                ((iteratedCovGrad (I := I) g₀ 2 6 w₃
                  (slotExtendIter (I := I) (M := M) g₀ 0 4 2
                    (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀))).toSection x) *
              ∑ w₄ ∈ Finset.range (w₂ + 1 - w₃),
                riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + w₄) x
                  ((iteratedCovGrad (I := I) g₀ 0 2 w₄
                    (symmS (I := I) g₀ P)).toSection x)
        ≤ appCcGdiag (E := E) w₂ *
            ∑ w₃ ∈ Finset.range (w₂ + 1), KS w₃ *
              ∑ w₄ ∈ Finset.range (w₂ + 1 - w₃), ((fr ^ 2 + 1) * W) := by
          refine mul_le_mul_of_nonneg_left
            (Finset.sum_le_sum fun w₃ hw₃ => ?_) (appCcGdiag_nonneg (E := E) w₂)
          rw [Finset.mem_range] at hw₃
          refine mul_le_mul (hKS w₃ x) (Finset.sum_le_sum fun w₄ hw₄ => ?_)
            (Finset.sum_nonneg fun w₄ _ =>
              riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + w₄) x _)
            (hKS_nn w₃)
          rw [Finset.mem_range] at hw₄
          exact hS w₄ (by omega)
      _ = (appCcGdiag (E := E) w₂ *
            ∑ w₃ ∈ Finset.range (w₂ + 1), KS w₃ *
              ∑ w₄ ∈ Finset.range (w₂ + 1 - w₃), (fr ^ 2 + 1)) * W := by
          have hstep : ∀ w₃ : ℕ, (KS w₃ *
              ∑ w₄ ∈ Finset.range (w₂ + 1 - w₃), ((fr ^ 2 + 1) * W)) =
              (KS w₃ * ∑ w₄ ∈ Finset.range (w₂ + 1 - w₃), (fr ^ 2 + 1)) * W := by
            intro w₃
            rw [← Finset.sum_mul]
            ring
          rw [Finset.sum_congr rfl fun w₃ _ => hstep w₃, ← Finset.sum_mul]
          ring
  refine le_trans (rfns_iteratedCovGrad_appCcRS_diagonalProductGrid_rankLeft_le (I := I)
    (M := M) g₀ w 0 6 4 (cometricDoubleTraceField (I := I) g₀ 4)
    (rsDomDomCongrSection (I := I) (M := M) g₀ 0 6 σ
      (appCcRS (I := I) (M := M) g₀ 0 2 6
        (slotExtendIter (I := I) (M := M) g₀ 0 4 2
          (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀))
        (symmS (I := I) g₀ P))) x) ?_
  calc appCcGdiag (E := E) w *
        ∑ w₁ ∈ Finset.range (w + 1),
          riemannianFiberNormSq (I := I) (M := M) g₀ 6 (4 + w₁) x
              ((iteratedCovGrad (I := I) g₀ 6 4 w₁
                (cometricDoubleTraceField (I := I) g₀ 4)).toSection x) *
            ∑ w₂ ∈ Finset.range (w + 1 - w₁),
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (6 + w₂) x
                ((iteratedCovGrad (I := I) g₀ 0 6 w₂
                  (rsDomDomCongrSection (I := I) (M := M) g₀ 0 6 σ
                    (appCcRS (I := I) (M := M) g₀ 0 2 6
                      (slotExtendIter (I := I) (M := M) g₀ 0 4 2
                        (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀))
                      (symmS (I := I) g₀ P)))).toSection x)
      ≤ appCcGdiag (E := E) w *
          ∑ w₁ ∈ Finset.range (w + 1), KD w₁ *
            ∑ w₂ ∈ Finset.range (w + 1 - w₁),
              ((appCcGdiag (E := E) w₂ *
                ∑ w₃ ∈ Finset.range (w₂ + 1), KS w₃ *
                  ∑ w₄ ∈ Finset.range (w₂ + 1 - w₃), (fr ^ 2 + 1)) * W) := by
        refine mul_le_mul_of_nonneg_left
          (Finset.sum_le_sum fun w₁ hw₁ => ?_) (appCcGdiag_nonneg (E := E) w)
        rw [Finset.mem_range] at hw₁
        refine mul_le_mul (hKD w₁ x) (Finset.sum_le_sum fun w₂ hw₂ => ?_)
          (Finset.sum_nonneg fun w₂ _ =>
            riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (6 + w₂) x _)
          (hKD_nn w₁)
        rw [Finset.mem_range] at hw₂
        exact hBase w₂ (by omega)
    _ = (appCcGdiag (E := E) w *
          ∑ w₁ ∈ Finset.range (w + 1), KD w₁ *
            ∑ w₂ ∈ Finset.range (w + 1 - w₁),
              appCcGdiag (E := E) w₂ *
                ∑ w₃ ∈ Finset.range (w₂ + 1), KS w₃ *
                  ∑ w₄ ∈ Finset.range (w₂ + 1 - w₃), (fr ^ 2 + 1)) * W := by
        have hstep : ∀ w₁ : ℕ, (KD w₁ *
            ∑ w₂ ∈ Finset.range (w + 1 - w₁),
              ((appCcGdiag (E := E) w₂ *
                ∑ w₃ ∈ Finset.range (w₂ + 1), KS w₃ *
                  ∑ w₄ ∈ Finset.range (w₂ + 1 - w₃), (fr ^ 2 + 1)) * W)) =
            (KD w₁ * ∑ w₂ ∈ Finset.range (w + 1 - w₁),
              appCcGdiag (E := E) w₂ *
                ∑ w₃ ∈ Finset.range (w₂ + 1), KS w₃ *
                  ∑ w₄ ∈ Finset.range (w₂ + 1 - w₃), (fr ^ 2 + 1)) * W := by
          intro w₁
          rw [← Finset.sum_mul]
          ring
        rw [Finset.sum_congr rfl fun w₁ _ => hstep w₁, ← Finset.sum_mul]
        ring

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
set_option maxHeartbeats 12800000 in
lemma bgRCommCoeffField_eq_refold (g : SmoothRiemannianMetric I M) :
    ricciArmOrder0BgRCommCoeffField (I := I) (M := M) g₀ g =
      appCcRS (I := I) (M := M) g₀ 2 4 2 (mvDoubleTraceField (I := I) (M := M) g₀ g 2)
        (bgRArmWeight (I := I) (M := M) g₀) := by
  classical
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply tensorRSSpace_ext 2 2 x
  intro D
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro v
  beta_reduce
  rw [show ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
      (ricciArmOrder0BgRCommCoeffField (I := I) (M := M) g₀ g).toSection x) D) =
      bgRBiContrFib (I := I) g₀ g x D from rfl]
  rw [show bgRBiContrFib (I := I) g₀ g x =
      bgRBiContrFibFixedFrame (I := I) g₀ (smoothOrthoFrame (I := I) g x) x from rfl]
  rw [bgRBiContrFibFixedFrame_toModel (I := I) g₀ (smoothOrthoFrame (I := I) g x) x D
    (fun j => (v j : E))]
  rw [show ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
      (appCcRS (I := I) (M := M) g₀ 2 4 2 (mvDoubleTraceField (I := I) (M := M) g₀ g 2)
        (bgRArmWeight (I := I) (M := M) g₀)).toSection x) D) =
      cometricDoubleTraceFib (I := I) g 2 x
        ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 4 I x from
          (bgRArmWeight (I := I) (M := M) g₀).toSection x) D) from by
    rw [appCcRS_toSection]
    rfl]
  rw [cometricDoubleTraceFib_toModel (I := I) g 2 x]
  rw [modelDoubleTrace_apply (E := E) 2 (cometricLmodel (I := I) g x)]
  rw [cometric_dualTrace_eq_orthoFrame_diag (I := I) g x
    (mem_smoothOrthoFrameNbhd_self (I := I) (M := M) x)
    (Tensor0SSpace.toModel
      ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 4 I x from
        (bgRArmWeight (I := I) (M := M) g₀).toSection x) D))
    (fun j => (v j : E))]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [bgRArmWeight_toModel (I := I) (M := M) g₀ x D]
  show Tensor0SSpace.toModel D
      (Fin.cons (show E from riemannOp (LeviCivita (I := I) g₀) x
          (smoothOrthoFrame (I := I) g x c x) (v 0) (v 1))
        (Fin.cons ((smoothOrthoFrame (I := I) g x c x : TangentSpace I x) : E)
          (fun i : Fin 0 => i.elim0))) =
    ∑ e : Fin (Module.finrank ℝ E),
      Tensor0SSpace.toModel D
          (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g x c x : TangentSpace I x) : E)
              (fun i : Fin 0 => i.elim0))) *
        g₀.inner x (riemannOp (LeviCivita (I := I) g₀) x
            (smoothOrthoFrame (I := I) g x c x) (v 0) (v 1))
          (smoothOrthoFrame (I := I) g₀ x e x)
  have hu_exp : (show E from riemannOp (LeviCivita (I := I) g₀) x
      (smoothOrthoFrame (I := I) g x c x) (v 0) (v 1)) =
      ∑ e : Fin (Module.finrank ℝ E),
        g₀.inner x (riemannOp (LeviCivita (I := I) g₀) x
            (smoothOrthoFrame (I := I) g x c x) (v 0) (v 1))
          (smoothOrthoFrame (I := I) g₀ x e x) •
        ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E) := by
    rw [show (∑ e : Fin (Module.finrank ℝ E),
        g₀.inner x (riemannOp (LeviCivita (I := I) g₀) x
            (smoothOrthoFrame (I := I) g x c x) (v 0) (v 1))
          (smoothOrthoFrame (I := I) g₀ x e x) •
        ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)) =
        ((∑ e : Fin (Module.finrank ℝ E),
          g₀.inner x (riemannOp (LeviCivita (I := I) g₀) x
              (smoothOrthoFrame (I := I) g x c x) (v 0) (v 1))
            (smoothOrthoFrame (I := I) g₀ x e x) •
          smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E) from rfl]
    conv_lhs => rw [orthoFrame_expansion_at_center (I := I) (M := M) g₀ x
      (riemannOp (LeviCivita (I := I) g₀) x (smoothOrthoFrame (I := I) g x c x) (v 0) (v 1))]
  rw [hu_exp]
  rw [toModel_cons_sum_smul (E := E) x (Tensor0SSpace.toModel D)
    (Module.finrank ℝ E)
    (fun e => g₀.inner x (riemannOp (LeviCivita (I := I) g₀) x
        (smoothOrthoFrame (I := I) g x c x) (v 0) (v 1))
      (smoothOrthoFrame (I := I) g₀ x e x))
    (fun e => ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E))
    (Fin.cons ((smoothOrthoFrame (I := I) g x c x : TangentSpace I x) : E)
      (fun i : Fin 0 => i.elim0))]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [mul_comm]

set_option linter.unusedVariables false in
set_option linter.unusedSectionVars false in
private lemma toModel_vec3_slot0_sum_smul (x : M)
    (Zm : Tensor0SModel 3 ℝ E) (d : ℕ) (t : Fin d → ℝ) (u : Fin d → E) (a b : E) :
    Zm ![∑ c, t c • u c, a, b] = ∑ c, t c * Zm ![u c, a, b] := by
  classical
  have h1 : ∀ v : E, (![v, a, b] : Fin 3 → E) = Function.update ![(0 : E), a, b] 0 v := by
    intro v
    funext k
    fin_cases k <;> simp [Function.update]
  have hgen : ∀ ss : Finset (Fin d),
      Zm (Function.update ![(0 : E), a, b] 0 (∑ c ∈ ss, t c • u c)) =
        ∑ c ∈ ss, t c * Zm (Function.update ![(0 : E), a, b] 0 (u c)) := by
    intro ss
    induction ss using Finset.induction_on with
    | empty =>
        rw [Finset.sum_empty, Finset.sum_empty]
        rw [show (0 : E) = ((0 : ℝ) • (0 : E)) from (zero_smul ℝ (0 : E)).symm]
        rw [ContinuousMultilinearMap.map_update_smul]
        rw [zero_smul]
    | @insert a' ss ha ih =>
        rw [Finset.sum_insert ha, Finset.sum_insert ha]
        rw [ContinuousMultilinearMap.map_update_add]
        rw [ih]
        congr 1
        rw [ContinuousMultilinearMap.map_update_smul]
        rw [smul_eq_mul]
  have h2 := hgen Finset.univ
  rw [h1, h2]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← h1 (u c)]

set_option linter.unusedVariables false in
set_option linter.unusedSectionVars false in
private lemma toModel_vec3_slot2_sum_smul (x : M)
    (Zm : Tensor0SModel 3 ℝ E) (d : ℕ) (t : Fin d → ℝ) (u : Fin d → E) (a b : E) :
    Zm ![a, b, ∑ c, t c • u c] = ∑ c, t c * Zm ![a, b, u c] := by
  classical
  have h1 : ∀ v : E, (![a, b, v] : Fin 3 → E) = Function.update ![a, b, (0 : E)] 2 v := by
    intro v
    funext k
    fin_cases k <;> simp [Function.update]
  have hgen : ∀ ss : Finset (Fin d),
      Zm (Function.update ![a, b, (0 : E)] 2 (∑ c ∈ ss, t c • u c)) =
        ∑ c ∈ ss, t c * Zm (Function.update ![a, b, (0 : E)] 2 (u c)) := by
    intro ss
    induction ss using Finset.induction_on with
    | empty =>
        rw [Finset.sum_empty, Finset.sum_empty]
        rw [show (0 : E) = ((0 : ℝ) • (0 : E)) from (zero_smul ℝ (0 : E)).symm]
        rw [ContinuousMultilinearMap.map_update_smul]
        rw [zero_smul]
    | @insert a' ss ha ih =>
        rw [Finset.sum_insert ha, Finset.sum_insert ha]
        rw [ContinuousMultilinearMap.map_update_add]
        rw [ih]
        congr 1
        rw [ContinuousMultilinearMap.map_update_smul]
        rw [smul_eq_mul]
  have h2 := hgen Finset.univ
  rw [h1, h2]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← h1 (u c)]

set_option linter.unusedSectionVars false in
open DifferentialGeometry.Integral.DivergenceTheorem in
private lemma sharpRaisedKoszulVec_symmS_eq_connDiff (P : SmoothCcTensor g₀ 0 2)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
    (x : M) (u ζ : TangentSpace I x) :
    sharpRaisedKoszulVec (I := I) g₀ g₁ (symmS (I := I) g₀ P) x u ζ =
      PDE.DeTurck.connDiff (I := I) g₁ g₀ x u ζ := by
  rw [sharpRaisedKoszulVec, metricSharp_def, LinearEquiv.symm_apply_eq]
  apply LinearMap.ext
  intro z
  rw [show (metricFlatMap (I := I) g₁ x
      (PDE.DeTurck.connDiff (I := I) g₁ g₀ x u ζ)) z =
      g₁.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x u ζ) z from rfl]
  rw [linearizedKoszulCovec_apply (I := I) g₀ (symmS (I := I) g₀ P) x u ζ z]
  rw [connDiffInner_g1_eq_half_covGradSymmS (I := I) g₀ g₁ P htie x u ζ z]

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
lemma koszulCovecCc_unitModel_eq_g1_inner (P : SmoothCcTensor g₀ 0 2)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
    (x : M) (a b c : TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 3 (koszulCovecCc (I := I) g₀ P) x ![c, a, b] =
      g₁.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x a b) c := by
  rw [koszulCovecCc_unitModel (I := I) (M := M) g₀ P x a b c]
  rw [connDiffInner_g1_eq_half_covGradSymmS (I := I) g₀ g₁ P htie x a b c]
  rfl

def k2FoldWeight (σ : Equiv.Perm (Fin 6)) (P : SmoothCcTensor g₀ 0 2) :
    SmoothCcTensor g₀ 0 4 :=
  appCcRS (I := I) (M := M) g₀ 0 6 4 (cometricDoubleTraceField (I := I) g₀ 4)
    (rsDomDomCongrSection (I := I) (M := M) g₀ 0 6 σ
      (appCcRS (I := I) (M := M) g₀ 0 3 6
        (slotExtendIter (I := I) (M := M) g₀ 0 3 3 (koszulCovecCc (I := I) g₀ P))
        (connDiffLoweredCc (I := I) g₀ g₁)))

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
set_option maxHeartbeats 12800000 in
lemma k2FoldWeight_unitModel_gen (σ : Equiv.Perm (Fin 6))
    (P : SmoothCcTensor g₀ 0 2) (x : M) (m : Fin 4 → E) :
    unitModel (I := I) (M := M) g₀ 4
        (appCcRS (I := I) (M := M) g₀ 0 6 4 (cometricDoubleTraceField (I := I) g₀ 4)
          (rsDomDomCongrSection (I := I) (M := M) g₀ 0 6 σ
            (appCcRS (I := I) (M := M) g₀ 0 3 6
              (slotExtendIter (I := I) (M := M) g₀ 0 3 3 (koszulCovecCc (I := I) g₀ P))
              (connDiffLoweredCc (I := I) g₀ g₁)))) x m =
      ∑ e : Fin (Module.finrank ℝ E),
        unitModel (I := I) (M := M) g₀ 3 (connDiffLoweredCc (I := I) g₀ g₁) x
            ![((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
                (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E) m) :
                  Fin 6 → E) (σ 0)),
              ((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
                (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E) m) :
                  Fin 6 → E) (σ 1)),
              ((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
                (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E) m) :
                  Fin 6 → E) (σ 2))] *
          unitModel (I := I) (M := M) g₀ 3 (koszulCovecCc (I := I) g₀ P) x
            ![((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
                (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E) m) :
                  Fin 6 → E) (σ 3)),
              ((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
                (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E) m) :
                  Fin 6 → E) (σ 4)),
              ((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
                (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E) m) :
                  Fin 6 → E) (σ 5))] := by
  classical
  set κ3 : SmoothCcTensor g₀ 0 3 := koszulCovecCc (I := I) g₀ P with hκ3_def
  set Cval : Tensor0SSpace 3 I x :=
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
      (connDiffLoweredCc (I := I) g₀ g₁).toSection x)
      (unitTensor (I := I) (M := M) x) with hCval_def
  set Y : Tensor0SSpace 6 I x :=
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 6 I x from
      (rsDomDomCongrSection (I := I) (M := M) g₀ 0 6 σ
        (appCcRS (I := I) (M := M) g₀ 0 3 6
          (slotExtendIter (I := I) (M := M) g₀ 0 3 3 κ3)
          (connDiffLoweredCc (I := I) g₀ g₁))).toSection x)
      (unitTensor (I := I) (M := M) x) with hY_def
  have hYval : ∀ w : Fin 6 → TangentSpace I x,
      Tensor0SSpace.toModel Y w =
        Tensor0SSpace.toModel Cval ![(w (σ 0) : E), (w (σ 1) : E), (w (σ 2) : E)] *
          unitModel (I := I) (M := M) g₀ 3 κ3 x
            ![(w (σ 3) : E), (w (σ 4) : E), (w (σ 5) : E)] := by
    intro w
    rw [hY_def]
    rw [show ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 6 I x from
        (rsDomDomCongrSection (I := I) (M := M) g₀ 0 6 σ
          (appCcRS (I := I) (M := M) g₀ 0 3 6
            (slotExtendIter (I := I) (M := M) g₀ 0 3 3 κ3)
            (connDiffLoweredCc (I := I) g₀ g₁))).toSection x)
        (unitTensor (I := I) (M := M) x)) =
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 6 I x from
          rsDomDomCongr σ
            ((appCcRS (I := I) (M := M) g₀ 0 3 6
              (slotExtendIter (I := I) (M := M) g₀ 0 3 3 κ3)
              (connDiffLoweredCc (I := I) g₀ g₁)).toSection x))
          (unitTensor (I := I) (M := M) x)) from by
      rw [rsDomDomCongrSection_toSection]]
    rw [toModel_rsDomDomCongr_apply (I := I) (M := M) σ
      ((appCcRS (I := I) (M := M) g₀ 0 3 6
        (slotExtendIter (I := I) (M := M) g₀ 0 3 3 κ3)
        (connDiffLoweredCc (I := I) g₀ g₁)).toSection x)
      (unitTensor (I := I) (M := M) x)]
    rw [ContinuousMultilinearMap.domDomCongr_apply]
    rw [show ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 6 I x from
        (appCcRS (I := I) (M := M) g₀ 0 3 6
          (slotExtendIter (I := I) (M := M) g₀ 0 3 3 κ3)
          (connDiffLoweredCc (I := I) g₀ g₁)).toSection x)
        (unitTensor (I := I) (M := M) x)) =
        ((show Tensor0SSpace 3 I x →L[ℝ] Tensor0SSpace 6 I x from
          (slotExtendIter (I := I) (M := M) g₀ 0 3 3 κ3).toSection x) Cval) from by
      rw [appCcRS_toSection]
      rfl]
    rw [slotExtendIter_three_toModel (I := I) (M := M) g₀ κ3 x Cval (fun i => w (σ i))]
    refine congrArg₂ (· * ·) ?_ ?_
    · refine congrArg _ ?_
      funext k
      fin_cases k <;> rfl
    · rw [show unitModel (I := I) (M := M) g₀ 3 κ3 x
          (fun k : Fin 3 => ((fun i => w (σ i)) (Fin.natAdd 3 k) : E)) =
          unitModel (I := I) (M := M) g₀ 3 κ3 x
            ![(w (σ 3) : E), (w (σ 4) : E), (w (σ 5) : E)] from by
        refine congrArg _ ?_
        funext k
        fin_cases k <;> rfl]
  rw [show unitModel (I := I) (M := M) g₀ 4
      (appCcRS (I := I) (M := M) g₀ 0 6 4 (cometricDoubleTraceField (I := I) g₀ 4)
        (rsDomDomCongrSection (I := I) (M := M) g₀ 0 6 σ
          (appCcRS (I := I) (M := M) g₀ 0 3 6
            (slotExtendIter (I := I) (M := M) g₀ 0 3 3 κ3)
            (connDiffLoweredCc (I := I) g₀ g₁)))) x =
      Tensor0SSpace.toModel (cometricDoubleTraceFib (I := I) g₀ 4 x Y) from by
    rw [unitModel, hY_def]
    rw [appCcRS_toSection]
    rfl]
  rw [cometricDoubleTraceFib_toModel (I := I) g₀ 4 x Y]
  rw [modelDoubleTrace_apply (E := E) 4 (cometricLmodel (I := I) g₀ x)]
  rw [cometric_dualTrace_eq_orthoFrame_diag (I := I) g₀ x
    (mem_smoothOrthoFrameNbhd_self (I := I) (M := M) x)
    (Tensor0SSpace.toModel Y) m]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [hYval]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
set_option maxHeartbeats 12800000 in
private lemma k2FoldWeights_unitModel_eq_kernel (P : SmoothCcTensor g₀ 0 2)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
    (x : M) (p q v0 v1 : TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 4
        ((k2FoldWeight (I := I) (M := M) g₀ g₁ tauM1 P +
            k2FoldWeight (I := I) (M := M) g₀ g₁ tauM2 P) -
          (k2FoldWeight (I := I) (M := M) g₀ g₁ tauM3 P +
            k2FoldWeight (I := I) (M := M) g₀ g₁ tauM4 P)) x
        ![(v0 : E), (v1 : E), (p : E), (q : E)] =
      sharpGradKoszulKernelBilin (I := I) g₀ g₁ (symmS (I := I) g₀ P) x p q v0 v1 := by
  classical
  have hM1 : unitModel (I := I) (M := M) g₀ 4
      (k2FoldWeight (I := I) (M := M) g₀ g₁ tauM1 P) x
      ![(v0 : E), (v1 : E), (p : E), (q : E)] =
      ∑ e : Fin (Module.finrank ℝ E),
        g₀.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x q v0)
            (smoothOrthoFrame (I := I) g₀ x e x) *
          unitModel (I := I) (M := M) g₀ 3 (koszulCovecCc (I := I) g₀ P) x
            ![(v1 : E), (p : E),
              ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)] := by
    rw [show k2FoldWeight (I := I) (M := M) g₀ g₁ tauM1 P =
        appCcRS (I := I) (M := M) g₀ 0 6 4 (cometricDoubleTraceField (I := I) g₀ 4)
          (rsDomDomCongrSection (I := I) (M := M) g₀ 0 6 tauM1
            (appCcRS (I := I) (M := M) g₀ 0 3 6
              (slotExtendIter (I := I) (M := M) g₀ 0 3 3 (koszulCovecCc (I := I) g₀ P))
              (connDiffLoweredCc (I := I) g₀ g₁))) from rfl]
    rw [k2FoldWeight_unitModel_gen (I := I) (M := M) g₀ g₁ tauM1 P x
      ![(v0 : E), (v1 : E), (p : E), (q : E)]]
    refine Finset.sum_congr rfl fun e _ => ?_
    have h1 : unitModel (I := I) (M := M) g₀ 3 (connDiffLoweredCc (I := I) g₀ g₁) x
        ![((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
              ![(v0 : E), (v1 : E), (p : E), (q : E)]) : Fin 6 → E) (tauM1 0)),
          ((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
              ![(v0 : E), (v1 : E), (p : E), (q : E)]) : Fin 6 → E) (tauM1 1)),
          ((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
              ![(v0 : E), (v1 : E), (p : E), (q : E)]) : Fin 6 → E) (tauM1 2))] =
        unitModel (I := I) (M := M) g₀ 3 (connDiffLoweredCc (I := I) g₀ g₁) x
          ![(q : E), (v0 : E),
            ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)] := by
      refine congrArg _ ?_
      funext k
      fin_cases k <;> rfl
    have h2 : unitModel (I := I) (M := M) g₀ 3 (koszulCovecCc (I := I) g₀ P) x
        ![((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
              ![(v0 : E), (v1 : E), (p : E), (q : E)]) : Fin 6 → E) (tauM1 3)),
          ((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
              ![(v0 : E), (v1 : E), (p : E), (q : E)]) : Fin 6 → E) (tauM1 4)),
          ((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
              ![(v0 : E), (v1 : E), (p : E), (q : E)]) : Fin 6 → E) (tauM1 5))] =
        unitModel (I := I) (M := M) g₀ 3 (koszulCovecCc (I := I) g₀ P) x
          ![(v1 : E), (p : E),
            ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)] := by
      refine congrArg _ ?_
      funext k
      fin_cases k <;> rfl
    rw [h1, h2]
    congr 1
    have h12 := connDiffLowered_unitModel_value (I := I) (M := M) g₀ g₁ x
      ![q, v0, smoothOrthoFrame (I := I) g₀ x e x]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons] at h12
    exact h12
  have hM2 : unitModel (I := I) (M := M) g₀ 4
      (k2FoldWeight (I := I) (M := M) g₀ g₁ tauM2 P) x
      ![(v0 : E), (v1 : E), (p : E), (q : E)] =
      ∑ e : Fin (Module.finrank ℝ E),
        g₀.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x q v0)
            (smoothOrthoFrame (I := I) g₀ x e x) *
          unitModel (I := I) (M := M) g₀ 3 (koszulCovecCc (I := I) g₀ P) x
            ![((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E),
              (p : E), (v1 : E)] := by
    rw [show k2FoldWeight (I := I) (M := M) g₀ g₁ tauM2 P =
        appCcRS (I := I) (M := M) g₀ 0 6 4 (cometricDoubleTraceField (I := I) g₀ 4)
          (rsDomDomCongrSection (I := I) (M := M) g₀ 0 6 tauM2
            (appCcRS (I := I) (M := M) g₀ 0 3 6
              (slotExtendIter (I := I) (M := M) g₀ 0 3 3 (koszulCovecCc (I := I) g₀ P))
              (connDiffLoweredCc (I := I) g₀ g₁))) from rfl]
    rw [k2FoldWeight_unitModel_gen (I := I) (M := M) g₀ g₁ tauM2 P x
      ![(v0 : E), (v1 : E), (p : E), (q : E)]]
    refine Finset.sum_congr rfl fun e _ => ?_
    have h1 : unitModel (I := I) (M := M) g₀ 3 (connDiffLoweredCc (I := I) g₀ g₁) x
        ![((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
              ![(v0 : E), (v1 : E), (p : E), (q : E)]) : Fin 6 → E) (tauM2 0)),
          ((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
              ![(v0 : E), (v1 : E), (p : E), (q : E)]) : Fin 6 → E) (tauM2 1)),
          ((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
              ![(v0 : E), (v1 : E), (p : E), (q : E)]) : Fin 6 → E) (tauM2 2))] =
        unitModel (I := I) (M := M) g₀ 3 (connDiffLoweredCc (I := I) g₀ g₁) x
          ![(q : E), (v0 : E),
            ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)] := by
      refine congrArg _ ?_
      funext k
      fin_cases k <;> rfl
    have h2 : unitModel (I := I) (M := M) g₀ 3 (koszulCovecCc (I := I) g₀ P) x
        ![((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
              ![(v0 : E), (v1 : E), (p : E), (q : E)]) : Fin 6 → E) (tauM2 3)),
          ((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
              ![(v0 : E), (v1 : E), (p : E), (q : E)]) : Fin 6 → E) (tauM2 4)),
          ((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
              ![(v0 : E), (v1 : E), (p : E), (q : E)]) : Fin 6 → E) (tauM2 5))] =
        unitModel (I := I) (M := M) g₀ 3 (koszulCovecCc (I := I) g₀ P) x
          ![((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E),
            (p : E), (v1 : E)] := by
      refine congrArg _ ?_
      funext k
      fin_cases k <;> rfl
    rw [h1, h2]
    congr 1
    have h12 := connDiffLowered_unitModel_value (I := I) (M := M) g₀ g₁ x
      ![q, v0, smoothOrthoFrame (I := I) g₀ x e x]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons] at h12
    exact h12
  have hM3 : unitModel (I := I) (M := M) g₀ 4
      (k2FoldWeight (I := I) (M := M) g₀ g₁ tauM3 P) x
      ![(v0 : E), (v1 : E), (p : E), (q : E)] =
      ∑ e : Fin (Module.finrank ℝ E),
        g₀.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x q p)
            (smoothOrthoFrame (I := I) g₀ x e x) *
          unitModel (I := I) (M := M) g₀ 3 (koszulCovecCc (I := I) g₀ P) x
            ![(v1 : E), (v0 : E),
              ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)] := by
    rw [show k2FoldWeight (I := I) (M := M) g₀ g₁ tauM3 P =
        appCcRS (I := I) (M := M) g₀ 0 6 4 (cometricDoubleTraceField (I := I) g₀ 4)
          (rsDomDomCongrSection (I := I) (M := M) g₀ 0 6 tauM3
            (appCcRS (I := I) (M := M) g₀ 0 3 6
              (slotExtendIter (I := I) (M := M) g₀ 0 3 3 (koszulCovecCc (I := I) g₀ P))
              (connDiffLoweredCc (I := I) g₀ g₁))) from rfl]
    rw [k2FoldWeight_unitModel_gen (I := I) (M := M) g₀ g₁ tauM3 P x
      ![(v0 : E), (v1 : E), (p : E), (q : E)]]
    refine Finset.sum_congr rfl fun e _ => ?_
    have h1 : unitModel (I := I) (M := M) g₀ 3 (connDiffLoweredCc (I := I) g₀ g₁) x
        ![((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
              ![(v0 : E), (v1 : E), (p : E), (q : E)]) : Fin 6 → E) (tauM3 0)),
          ((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
              ![(v0 : E), (v1 : E), (p : E), (q : E)]) : Fin 6 → E) (tauM3 1)),
          ((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
              ![(v0 : E), (v1 : E), (p : E), (q : E)]) : Fin 6 → E) (tauM3 2))] =
        unitModel (I := I) (M := M) g₀ 3 (connDiffLoweredCc (I := I) g₀ g₁) x
          ![(q : E), (p : E),
            ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)] := by
      refine congrArg _ ?_
      funext k
      fin_cases k <;> rfl
    have h2 : unitModel (I := I) (M := M) g₀ 3 (koszulCovecCc (I := I) g₀ P) x
        ![((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
              ![(v0 : E), (v1 : E), (p : E), (q : E)]) : Fin 6 → E) (tauM3 3)),
          ((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
              ![(v0 : E), (v1 : E), (p : E), (q : E)]) : Fin 6 → E) (tauM3 4)),
          ((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
              ![(v0 : E), (v1 : E), (p : E), (q : E)]) : Fin 6 → E) (tauM3 5))] =
        unitModel (I := I) (M := M) g₀ 3 (koszulCovecCc (I := I) g₀ P) x
          ![(v1 : E), (v0 : E),
            ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)] := by
      refine congrArg _ ?_
      funext k
      fin_cases k <;> rfl
    rw [h1, h2]
    congr 1
    have h12 := connDiffLowered_unitModel_value (I := I) (M := M) g₀ g₁ x
      ![q, p, smoothOrthoFrame (I := I) g₀ x e x]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons] at h12
    exact h12
  have hM4 : unitModel (I := I) (M := M) g₀ 4
      (k2FoldWeight (I := I) (M := M) g₀ g₁ tauM4 P) x
      ![(v0 : E), (v1 : E), (p : E), (q : E)] =
      ∑ e : Fin (Module.finrank ℝ E),
        g₀.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x q p)
            (smoothOrthoFrame (I := I) g₀ x e x) *
          unitModel (I := I) (M := M) g₀ 3 (koszulCovecCc (I := I) g₀ P) x
            ![((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E),
              (v0 : E), (v1 : E)] := by
    rw [show k2FoldWeight (I := I) (M := M) g₀ g₁ tauM4 P =
        appCcRS (I := I) (M := M) g₀ 0 6 4 (cometricDoubleTraceField (I := I) g₀ 4)
          (rsDomDomCongrSection (I := I) (M := M) g₀ 0 6 tauM4
            (appCcRS (I := I) (M := M) g₀ 0 3 6
              (slotExtendIter (I := I) (M := M) g₀ 0 3 3 (koszulCovecCc (I := I) g₀ P))
              (connDiffLoweredCc (I := I) g₀ g₁))) from rfl]
    rw [k2FoldWeight_unitModel_gen (I := I) (M := M) g₀ g₁ tauM4 P x
      ![(v0 : E), (v1 : E), (p : E), (q : E)]]
    refine Finset.sum_congr rfl fun e _ => ?_
    have h1 : unitModel (I := I) (M := M) g₀ 3 (connDiffLoweredCc (I := I) g₀ g₁) x
        ![((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
              ![(v0 : E), (v1 : E), (p : E), (q : E)]) : Fin 6 → E) (tauM4 0)),
          ((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
              ![(v0 : E), (v1 : E), (p : E), (q : E)]) : Fin 6 → E) (tauM4 1)),
          ((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
              ![(v0 : E), (v1 : E), (p : E), (q : E)]) : Fin 6 → E) (tauM4 2))] =
        unitModel (I := I) (M := M) g₀ 3 (connDiffLoweredCc (I := I) g₀ g₁) x
          ![(q : E), (p : E),
            ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)] := by
      refine congrArg _ ?_
      funext k
      fin_cases k <;> rfl
    have h2 : unitModel (I := I) (M := M) g₀ 3 (koszulCovecCc (I := I) g₀ P) x
        ![((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
              ![(v0 : E), (v1 : E), (p : E), (q : E)]) : Fin 6 → E) (tauM4 3)),
          ((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
              ![(v0 : E), (v1 : E), (p : E), (q : E)]) : Fin 6 → E) (tauM4 4)),
          ((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
              ![(v0 : E), (v1 : E), (p : E), (q : E)]) : Fin 6 → E) (tauM4 5))] =
        unitModel (I := I) (M := M) g₀ 3 (koszulCovecCc (I := I) g₀ P) x
          ![((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E),
            (v0 : E), (v1 : E)] := by
      refine congrArg _ ?_
      funext k
      fin_cases k <;> rfl
    rw [h1, h2]
    congr 1
    have h12 := connDiffLowered_unitModel_value (I := I) (M := M) g₀ g₁ x
      ![q, p, smoothOrthoFrame (I := I) g₀ x e x]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons] at h12
    exact h12
  have hexp : ∀ r s : TangentSpace I x,
      ((PDE.DeTurck.connDiff (I := I) g₁ g₀ x r s : TangentSpace I x) : E) =
        ∑ e : Fin (Module.finrank ℝ E),
          g₀.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x r s)
            (smoothOrthoFrame (I := I) g₀ x e x) •
          ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E) := by
    intro r s
    rw [show (∑ e : Fin (Module.finrank ℝ E),
        g₀.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x r s)
          (smoothOrthoFrame (I := I) g₀ x e x) •
        ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)) =
        ((∑ e : Fin (Module.finrank ℝ E),
          g₀.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x r s)
            (smoothOrthoFrame (I := I) g₀ x e x) •
          smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E) from rfl]
    conv_lhs => rw [orthoFrame_expansion_at_center (I := I) (M := M) g₀ x
      (PDE.DeTurck.connDiff (I := I) g₁ g₀ x r s)]
  have hT1 : g₁.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x p
        (PDE.DeTurck.connDiff (I := I) g₁ g₀ x q v0)) v1 =
      ∑ e : Fin (Module.finrank ℝ E),
        g₀.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x q v0)
            (smoothOrthoFrame (I := I) g₀ x e x) *
          unitModel (I := I) (M := M) g₀ 3 (koszulCovecCc (I := I) g₀ P) x
            ![(v1 : E), (p : E),
              ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)] := by
    rw [← koszulCovecCc_unitModel_eq_g1_inner (I := I) (M := M) g₀ g₁ P htie x p
      (PDE.DeTurck.connDiff (I := I) g₁ g₀ x q v0) v1]
    conv_lhs => rw [hexp q v0]
    exact toModel_vec3_slot2_sum_smul (E := E) x
      (unitModel (I := I) (M := M) g₀ 3 (koszulCovecCc (I := I) g₀ P) x)
      (Module.finrank ℝ E)
      (fun e => g₀.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x q v0)
        (smoothOrthoFrame (I := I) g₀ x e x))
      (fun e => ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E))
      ((v1 : TangentSpace I x) : E) ((p : TangentSpace I x) : E)
  have hT2 : g₁.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x q v0)
        (PDE.DeTurck.connDiff (I := I) g₁ g₀ x p v1) =
      ∑ e : Fin (Module.finrank ℝ E),
        g₀.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x q v0)
            (smoothOrthoFrame (I := I) g₀ x e x) *
          unitModel (I := I) (M := M) g₀ 3 (koszulCovecCc (I := I) g₀ P) x
            ![((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E),
              (p : E), (v1 : E)] := by
    rw [g₁.symm x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x q v0)
      (PDE.DeTurck.connDiff (I := I) g₁ g₀ x p v1)]
    rw [← koszulCovecCc_unitModel_eq_g1_inner (I := I) (M := M) g₀ g₁ P htie x p v1
      (PDE.DeTurck.connDiff (I := I) g₁ g₀ x q v0)]
    conv_lhs => rw [hexp q v0]
    exact toModel_vec3_slot0_sum_smul (E := E) x
      (unitModel (I := I) (M := M) g₀ 3 (koszulCovecCc (I := I) g₀ P) x)
      (Module.finrank ℝ E)
      (fun e => g₀.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x q v0)
        (smoothOrthoFrame (I := I) g₀ x e x))
      (fun e => ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E))
      ((p : TangentSpace I x) : E) ((v1 : TangentSpace I x) : E)
  have hT3 : g₁.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x v0
        (PDE.DeTurck.connDiff (I := I) g₁ g₀ x q p)) v1 =
      ∑ e : Fin (Module.finrank ℝ E),
        g₀.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x q p)
            (smoothOrthoFrame (I := I) g₀ x e x) *
          unitModel (I := I) (M := M) g₀ 3 (koszulCovecCc (I := I) g₀ P) x
            ![(v1 : E), (v0 : E),
              ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)] := by
    rw [← koszulCovecCc_unitModel_eq_g1_inner (I := I) (M := M) g₀ g₁ P htie x v0
      (PDE.DeTurck.connDiff (I := I) g₁ g₀ x q p) v1]
    conv_lhs => rw [hexp q p]
    exact toModel_vec3_slot2_sum_smul (E := E) x
      (unitModel (I := I) (M := M) g₀ 3 (koszulCovecCc (I := I) g₀ P) x)
      (Module.finrank ℝ E)
      (fun e => g₀.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x q p)
        (smoothOrthoFrame (I := I) g₀ x e x))
      (fun e => ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E))
      ((v1 : TangentSpace I x) : E) ((v0 : TangentSpace I x) : E)
  have hT4 : g₁.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x q p)
        (PDE.DeTurck.connDiff (I := I) g₁ g₀ x v0 v1) =
      ∑ e : Fin (Module.finrank ℝ E),
        g₀.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x q p)
            (smoothOrthoFrame (I := I) g₀ x e x) *
          unitModel (I := I) (M := M) g₀ 3 (koszulCovecCc (I := I) g₀ P) x
            ![((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E),
              (v0 : E), (v1 : E)] := by
    rw [g₁.symm x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x q p)
      (PDE.DeTurck.connDiff (I := I) g₁ g₀ x v0 v1)]
    rw [← koszulCovecCc_unitModel_eq_g1_inner (I := I) (M := M) g₀ g₁ P htie x v0 v1
      (PDE.DeTurck.connDiff (I := I) g₁ g₀ x q p)]
    conv_lhs => rw [hexp q p]
    exact toModel_vec3_slot0_sum_smul (E := E) x
      (unitModel (I := I) (M := M) g₀ 3 (koszulCovecCc (I := I) g₀ P) x)
      (Module.finrank ℝ E)
      (fun e => g₀.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x q p)
        (smoothOrthoFrame (I := I) g₀ x e x))
      (fun e => ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E))
      ((v0 : TangentSpace I x) : E) ((v1 : TangentSpace I x) : E)
  rw [unitModel_sub_pt (I := I) (M := M) g₀ 4
    (k2FoldWeight (I := I) (M := M) g₀ g₁ tauM1 P +
      k2FoldWeight (I := I) (M := M) g₀ g₁ tauM2 P)
    (k2FoldWeight (I := I) (M := M) g₀ g₁ tauM3 P +
      k2FoldWeight (I := I) (M := M) g₀ g₁ tauM4 P) x]
  rw [unitModel_add_pt (I := I) (M := M) g₀ 4
    (k2FoldWeight (I := I) (M := M) g₀ g₁ tauM1 P)
    (k2FoldWeight (I := I) (M := M) g₀ g₁ tauM2 P) x]
  rw [unitModel_add_pt (I := I) (M := M) g₀ 4
    (k2FoldWeight (I := I) (M := M) g₀ g₁ tauM3 P)
    (k2FoldWeight (I := I) (M := M) g₀ g₁ tauM4 P) x]
  rw [ContinuousMultilinearMap.sub_apply, ContinuousMultilinearMap.add_apply,
    ContinuousMultilinearMap.add_apply]
  rw [hM1, hM2, hM3, hM4]
  rw [sharpGradKoszulKernelBilin_apply (I := I) g₀ g₁ (symmS (I := I) g₀ P) x p q v0 v1]
  rw [sharpRaisedKoszulVec_symmS_eq_connDiff (I := I) (M := M) g₀ g₁ P htie x q v0,
    sharpRaisedKoszulVec_symmS_eq_connDiff (I := I) (M := M) g₀ g₁ P htie x q p]
  rw [hT1, hT2, hT3, hT4]

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
set_option maxHeartbeats 12800000 in
lemma sharpGradKoszulResidualField_eq_refold (P : SmoothCcTensor g₀ 0 2)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w) :
    ricciArmSharpGradKoszulResidualField (I := I) (M := M) g₀ g₁ (symmS (I := I) g₀ P) =
      (2 : ℝ) •
        appCcRS (I := I) (M := M) g₀ 2 6 2 (mvPairTraceOp (I := I) (M := M) g₀ g₁)
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE
            (slotExtendIter (I := I) (M := M) g₀ 0 4 2
              ((k2FoldWeight (I := I) (M := M) g₀ g₁ tauM1 P +
                  k2FoldWeight (I := I) (M := M) g₀ g₁ tauM2 P) -
                (k2FoldWeight (I := I) (M := M) g₀ g₁ tauM3 P +
                  k2FoldWeight (I := I) (M := M) g₀ g₁ tauM4 P)))) := by
  classical
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply tensorRSSpace_ext 2 2 x
  intro D
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro v
  beta_reduce
  have hRHSsmul : ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
      (((2 : ℝ) •
        appCcRS (I := I) (M := M) g₀ 2 6 2 (mvPairTraceOp (I := I) (M := M) g₀ g₁)
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE
            (slotExtendIter (I := I) (M := M) g₀ 0 4 2
              ((k2FoldWeight (I := I) (M := M) g₀ g₁ tauM1 P +
                  k2FoldWeight (I := I) (M := M) g₀ g₁ tauM2 P) -
                (k2FoldWeight (I := I) (M := M) g₀ g₁ tauM3 P +
                  k2FoldWeight (I := I) (M := M) g₀ g₁ tauM4 P))))).toSection x)) D) =
      (2 : ℝ) • ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        (appCcRS (I := I) (M := M) g₀ 2 6 2 (mvPairTraceOp (I := I) (M := M) g₀ g₁)
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE
            (slotExtendIter (I := I) (M := M) g₀ 0 4 2
              ((k2FoldWeight (I := I) (M := M) g₀ g₁ tauM1 P +
                  k2FoldWeight (I := I) (M := M) g₀ g₁ tauM2 P) -
                (k2FoldWeight (I := I) (M := M) g₀ g₁ tauM3 P +
                  k2FoldWeight (I := I) (M := M) g₀ g₁ tauM4 P))))).toSection x) D) := by
    rw [show ((((2 : ℝ) •
        appCcRS (I := I) (M := M) g₀ 2 6 2 (mvPairTraceOp (I := I) (M := M) g₀ g₁)
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE
            (slotExtendIter (I := I) (M := M) g₀ 0 4 2
              ((k2FoldWeight (I := I) (M := M) g₀ g₁ tauM1 P +
                  k2FoldWeight (I := I) (M := M) g₀ g₁ tauM2 P) -
                (k2FoldWeight (I := I) (M := M) g₀ g₁ tauM3 P +
                  k2FoldWeight (I := I) (M := M) g₀ g₁ tauM4 P))))).toSection x)) =
        (2 : ℝ) •
          ((appCcRS (I := I) (M := M) g₀ 2 6 2 (mvPairTraceOp (I := I) (M := M) g₀ g₁)
            (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE
              (slotExtendIter (I := I) (M := M) g₀ 0 4 2
                ((k2FoldWeight (I := I) (M := M) g₀ g₁ tauM1 P +
                    k2FoldWeight (I := I) (M := M) g₀ g₁ tauM2 P) -
                  (k2FoldWeight (I := I) (M := M) g₀ g₁ tauM3 P +
                    k2FoldWeight (I := I) (M := M) g₀ g₁ tauM4 P))))).toSection x) from by
      rw [SmoothCcTensor.toSection_smul]; rfl]
    rfl
  rw [hRHSsmul, Tensor0SSpace.toModel_smul, ContinuousMultilinearMap.smul_apply, smul_eq_mul]
  rw [mvPairTraceOp_apply_toModel (I := I) (M := M) g₀ g₁
    ((k2FoldWeight (I := I) (M := M) g₀ g₁ tauM1 P +
        k2FoldWeight (I := I) (M := M) g₀ g₁ tauM2 P) -
      (k2FoldWeight (I := I) (M := M) g₀ g₁ tauM3 P +
        k2FoldWeight (I := I) (M := M) g₀ g₁ tauM4 P)) x D v]
  rw [show ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
      (ricciArmSharpGradKoszulResidualField (I := I) (M := M) g₀ g₁
        (symmS (I := I) g₀ P)).toSection x) D) =
      sharpGradKoszulBiContrFib (I := I) g₀ g₁ (symmS (I := I) g₀ P) x D from rfl]
  rw [show sharpGradKoszulBiContrFib (I := I) g₀ g₁ (symmS (I := I) g₀ P) x =
      sharpGradKoszulBiContrFibFixedFrame (I := I) g₀ g₁ (symmS (I := I) g₀ P)
        (smoothOrthoFrame (I := I) g₁ x) x from rfl]
  rw [sharpGradKoszulBiContrFibFixedFrame_toModel (I := I) g₀ g₁ (symmS (I := I) g₀ P)
    (smoothOrthoFrame (I := I) g₁ x) x D v]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [show unitModel (I := I) (M := M) g₀ 4
      ((k2FoldWeight (I := I) (M := M) g₀ g₁ tauM1 P +
          k2FoldWeight (I := I) (M := M) g₀ g₁ tauM2 P) -
        (k2FoldWeight (I := I) (M := M) g₀ g₁ tauM3 P +
          k2FoldWeight (I := I) (M := M) g₀ g₁ tauM4 P)) x
      ![v 0, v 1, (smoothOrthoFrame (I := I) g₁ x a x : E),
        (smoothOrthoFrame (I := I) g₁ x b x : E)] =
      sharpGradKoszulKernelBilin (I := I) g₀ g₁ (symmS (I := I) g₀ P) x
        (smoothOrthoFrame (I := I) g₁ x a x) (smoothOrthoFrame (I := I) g₁ x b x)
        (v 0) (v 1) from
    k2FoldWeights_unitModel_eq_kernel (I := I) (M := M) g₀ g₁ P htie x
      (smoothOrthoFrame (I := I) g₁ x a x) (smoothOrthoFrame (I := I) g₁ x b x)
      (v 0) (v 1)]

set_option linter.unusedVariables false in
set_option linter.unusedSectionVars false in
lemma exists_rfns_icg_k2FoldWeightGen_window (σ : Equiv.Perm (Fin 6))
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ C : ℕ → ℝ, (∀ w, 0 ≤ C w) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
        (hbound : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (w K : ℕ) (hwK : w + 1 ≤ K) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + w) x
            ((iteratedCovGrad (I := I) g₀ 0 4 w
              (appCcRS (I := I) (M := M) g₀ 0 6 4 (cometricDoubleTraceField (I := I) g₀ 4)
                (rsDomDomCongrSection (I := I) (M := M) g₀ 0 6 σ
                  (appCcRS (I := I) (M := M) g₀ 0 3 6
                    (slotExtendIter (I := I) (M := M) g₀ 0 3 3
                      (koszulCovecCc (I := I) g₀ P))
                    (connDiffLoweredCc (I := I) g₀ g₁))))).toSection x) ≤
          C w * Combinatorics.boundedFactorGridWindow
            (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
              ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) K (w + 3) := by
  classical
  set fr : ℝ := (Module.finrank ℝ E : ℝ) with hfr_def
  have hfr_nn : 0 ≤ fr := Nat.cast_nonneg _
  obtain ⟨CA, hCA_nn, hCA⟩ :=
    exists_rfns_iteratedCovGrad_connDiffSection_tgrid (I := I) (M := M) g₀ hδ₀
  set KD : ℕ → ℝ := fun u =>
    (exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ 6 (4 + u)
      (iteratedCovGrad (I := I) g₀ 6 4 u (cometricDoubleTraceField (I := I) g₀ 4))).choose
    with hKD_def
  have hKD_nn : ∀ u, 0 ≤ KD u := fun u =>
    (exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ 6 (4 + u)
      (iteratedCovGrad (I := I) g₀ 6 4 u
        (cometricDoubleTraceField (I := I) g₀ 4))).choose_spec.1
  have hKD : ∀ u (y : M),
      riemannianFiberNormSq (I := I) (M := M) g₀ 6 (4 + u) y
          ((iteratedCovGrad (I := I) g₀ 6 4 u
            (cometricDoubleTraceField (I := I) g₀ 4)).toSection y) ≤ KD u := fun u =>
    (exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ 6 (4 + u)
      (iteratedCovGrad (I := I) g₀ 6 4 u
        (cometricDoubleTraceField (I := I) g₀ 4))).choose_spec.2
  refine ⟨fun w => appCcGdiag (E := E) w *
      ∑ w₁ ∈ Finset.range (w + 1), KD w₁ *
        ∑ w₂ ∈ Finset.range (w + 1 - w₁),
          appCcGdiag (E := E) w₂ *
            ∑ w₃ ∈ Finset.range (w₂ + 1), (10 * fr ^ 3) *
              ∑ w₄ ∈ Finset.range (w₂ + 1 - w₃),
                CA w₄ * Combinatorics.windowPairCellCount (w₃ + 2) (w₄ + 2),
    fun w => mul_nonneg (appCcGdiag_nonneg (E := E) w)
      (Finset.sum_nonneg fun w₁ _ => mul_nonneg (hKD_nn w₁)
        (Finset.sum_nonneg fun w₂ _ => mul_nonneg (appCcGdiag_nonneg (E := E) w₂)
          (Finset.sum_nonneg fun w₃ _ =>
            mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hfr_nn 3))
              (Finset.sum_nonneg fun w₄ _ => mul_nonneg (hCA_nn w₄)
                (Combinatorics.windowPairCellCount_nonneg _ _))))), ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hbound w K hwK x
  set b : ℕ → ℝ := fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
    ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x) with hb_def
  have hb_nn : ∀ l, 0 ≤ b l :=
    fun l => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + l) x _
  have hκ : ∀ w₃ : ℕ, w₃ ≤ w →
      riemannianFiberNormSq (I := I) (M := M) g₀ 3 (6 + w₃) x
          ((iteratedCovGrad (I := I) g₀ 3 6 w₃
            (slotExtendIter (I := I) (M := M) g₀ 0 3 3
              (koszulCovecCc (I := I) g₀ P))).toSection x) ≤
        (10 * fr ^ 3) * Combinatorics.boundedFactorGridWindow b K (w₃ + 2) := by
    intro w₃ hw₃
    rw [show slotExtendIter (I := I) (M := M) g₀ 0 3 3 (koszulCovecCc (I := I) g₀ P) =
        slotExtend (I := I) (M := M) g₀ 2 5 (slotExtend (I := I) (M := M) g₀ 1 4
          (slotExtend (I := I) (M := M) g₀ 0 3 (koszulCovecCc (I := I) g₀ P))) from rfl]
    refine le_trans (rfns_iteratedCovGrad_slotExtend_le (I := I) (M := M) g₀ 2 5
      (slotExtend (I := I) (M := M) g₀ 1 4
        (slotExtend (I := I) (M := M) g₀ 0 3 (koszulCovecCc (I := I) g₀ P))) w₃ x) ?_
    refine le_trans (mul_le_mul_of_nonneg_left
      (rfns_iteratedCovGrad_slotExtend_le (I := I) (M := M) g₀ 1 4
        (slotExtend (I := I) (M := M) g₀ 0 3 (koszulCovecCc (I := I) g₀ P)) w₃ x)
      hfr_nn) ?_
    refine le_trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
      (rfns_iteratedCovGrad_slotExtend_le (I := I) (M := M) g₀ 0 3
        (koszulCovecCc (I := I) g₀ P) w₃ x) hfr_nn) hfr_nn) ?_
    refine le_trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left
        (rfns_iteratedCovGrad_koszulCovecCc_pointwise (I := I) (M := M) g₀ P w₃ x)
        hfr_nn) hfr_nn) hfr_nn) ?_
    have hb1 : b (w₃ + 1) ≤ Combinatorics.boundedFactorGridWindow b K (w₃ + 2) := by
      refine le_trans (single_b_le_grid b hb_nn (w₃ + 1) (by omega)) ?_
      exact Combinatorics.antidiagonalTupleGrid_le_boundedFactorGridWindow b hb_nn
        (by omega) (by omega)
    calc fr * (fr * (fr * (10 * b (w₃ + 1))))
        = (10 * fr ^ 3) * b (w₃ + 1) := by ring
      _ ≤ (10 * fr ^ 3) * Combinatorics.boundedFactorGridWindow b K (w₃ + 2) := by
          refine mul_le_mul_of_nonneg_left hb1 ?_
          exact mul_nonneg (by norm_num) (pow_nonneg hfr_nn 3)
  have hcdl : ∀ w₄ : ℕ, w₄ ≤ w →
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + w₄) x
          ((iteratedCovGrad (I := I) g₀ 0 3 w₄
            (connDiffLoweredCc (I := I) g₀ g₁)).toSection x) ≤
        CA w₄ * Combinatorics.boundedFactorGridWindow b K (w₄ + 2) := by
    intro w₄ hw₄
    rw [rfns_icg_connDiffLowered_eq_connDiffSection (I := I) (M := M) g₀ g₁ w₄ x]
    refine le_trans (hCA g₁ P htie hδ_le hδ0 hbound w₄ x) ?_
    refine mul_le_mul_of_nonneg_left ?_ (hCA_nn w₄)
    have heq : (∑ k ∈ Finset.range (w₄ + 2), Combinatorics.antidiagonalTupleGrid b k) =
        Combinatorics.boundedFactorGridWindow b (w₄ + 1) (w₄ + 2) := by
      rw [Combinatorics.boundedFactorGridWindow]
      refine Finset.sum_congr rfl fun k hk => ?_
      rw [Finset.mem_range] at hk
      exact Combinatorics.antidiagonalTupleGrid_eq_boundedFactorGrid b (by omega)
    calc (∑ k ∈ Finset.range (w₄ + 2), Combinatorics.antidiagonalTupleGrid b k)
        = Combinatorics.boundedFactorGridWindow b (w₄ + 1) (w₄ + 2) := heq
      _ ≤ Combinatorics.boundedFactorGridWindow b K (w₄ + 2) :=
          Combinatorics.boundedFactorGridWindow_mono b hb_nn (by omega) (le_refl _)
  have hbase : ∀ w₂ : ℕ, w₂ ≤ w →
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (6 + w₂) x
          ((iteratedCovGrad (I := I) g₀ 0 6 w₂
            (rsDomDomCongrSection (I := I) (M := M) g₀ 0 6 σ
              (appCcRS (I := I) (M := M) g₀ 0 3 6
                (slotExtendIter (I := I) (M := M) g₀ 0 3 3
                  (koszulCovecCc (I := I) g₀ P))
                (connDiffLoweredCc (I := I) g₀ g₁)))).toSection x) ≤
        (appCcGdiag (E := E) w₂ *
          ∑ w₃ ∈ Finset.range (w₂ + 1), (10 * fr ^ 3) *
            ∑ w₄ ∈ Finset.range (w₂ + 1 - w₃),
              CA w₄ * Combinatorics.windowPairCellCount (w₃ + 2) (w₄ + 2)) *
          Combinatorics.boundedFactorGridWindow b K (w₂ + 3) := by
    intro w₂ hw₂
    rw [rfns_icg_rsDomDomCongrSection_eq (I := I) (M := M) g₀ 0 6 σ _ w₂ x]
    refine le_trans (rfns_iteratedCovGrad_appCcRS_diagonalProductGrid_rankLeft_le (I := I)
      (M := M) g₀ w₂ 0 3 6
      (slotExtendIter (I := I) (M := M) g₀ 0 3 3 (koszulCovecCc (I := I) g₀ P))
      (connDiffLoweredCc (I := I) g₀ g₁) x) ?_
    calc appCcGdiag (E := E) w₂ *
          ∑ w₃ ∈ Finset.range (w₂ + 1),
            riemannianFiberNormSq (I := I) (M := M) g₀ 3 (6 + w₃) x
                ((iteratedCovGrad (I := I) g₀ 3 6 w₃
                  (slotExtendIter (I := I) (M := M) g₀ 0 3 3
                    (koszulCovecCc (I := I) g₀ P))).toSection x) *
              ∑ w₄ ∈ Finset.range (w₂ + 1 - w₃),
                riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + w₄) x
                  ((iteratedCovGrad (I := I) g₀ 0 3 w₄
                    (connDiffLoweredCc (I := I) g₀ g₁)).toSection x)
        ≤ appCcGdiag (E := E) w₂ *
            ∑ w₃ ∈ Finset.range (w₂ + 1),
              ((10 * fr ^ 3) * Combinatorics.boundedFactorGridWindow b K (w₃ + 2)) *
              ∑ w₄ ∈ Finset.range (w₂ + 1 - w₃),
                (CA w₄ * Combinatorics.boundedFactorGridWindow b K (w₄ + 2)) := by
          refine mul_le_mul_of_nonneg_left
            (Finset.sum_le_sum fun w₃ hw₃ => ?_) (appCcGdiag_nonneg (E := E) w₂)
          rw [Finset.mem_range] at hw₃
          refine mul_le_mul (hκ w₃ (by omega)) (Finset.sum_le_sum fun w₄ hw₄ => ?_)
            (Finset.sum_nonneg fun w₄ _ =>
              riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (3 + w₄) x _)
            (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hfr_nn 3))
              (Combinatorics.boundedFactorGridWindow_nonneg b hb_nn _ _))
          rw [Finset.mem_range] at hw₄
          exact hcdl w₄ (by omega)
      _ ≤ (appCcGdiag (E := E) w₂ *
            ∑ w₃ ∈ Finset.range (w₂ + 1), (10 * fr ^ 3) *
              ∑ w₄ ∈ Finset.range (w₂ + 1 - w₃),
                CA w₄ * Combinatorics.windowPairCellCount (w₃ + 2) (w₄ + 2)) *
            Combinatorics.boundedFactorGridWindow b K (w₂ + 3) := by
          rw [mul_assoc]
          refine mul_le_mul_of_nonneg_left ?_ (appCcGdiag_nonneg (E := E) w₂)
          rw [Finset.sum_mul]
          refine Finset.sum_le_sum fun w₃ hw₃ => ?_
          rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_mul]
          refine Finset.sum_le_sum fun w₄ hw₄ => ?_
          rw [Finset.mem_range] at hw₃ hw₄
          calc (10 * fr ^ 3) * Combinatorics.boundedFactorGridWindow b K (w₃ + 2) *
                (CA w₄ * Combinatorics.boundedFactorGridWindow b K (w₄ + 2))
              = ((10 * fr ^ 3) * CA w₄) *
                  (Combinatorics.boundedFactorGridWindow b K (w₃ + 2) *
                    Combinatorics.boundedFactorGridWindow b K (w₄ + 2)) := by ring
            _ ≤ ((10 * fr ^ 3) * CA w₄) *
                  (Combinatorics.windowPairCellCount (w₃ + 2) (w₄ + 2) *
                    Combinatorics.boundedFactorGridWindow b K
                      ((w₃ + 2) + (w₄ + 2) - 1)) := by
                refine mul_le_mul_of_nonneg_left ?_
                  (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hfr_nn 3))
                    (hCA_nn w₄))
                exact Combinatorics.boundedFactorGridWindow_mul_le b hb_nn K (w₃ + 2)
                  (w₄ + 2) (by omega) (by omega)
            _ ≤ ((10 * fr ^ 3) * CA w₄) *
                  (Combinatorics.windowPairCellCount (w₃ + 2) (w₄ + 2) *
                    Combinatorics.boundedFactorGridWindow b K (w₂ + 3)) := by
                refine mul_le_mul_of_nonneg_left ?_
                  (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hfr_nn 3))
                    (hCA_nn w₄))
                refine mul_le_mul_of_nonneg_left ?_
                  (Combinatorics.windowPairCellCount_nonneg _ _)
                exact Combinatorics.boundedFactorGridWindow_mono b hb_nn (le_refl _)
                  (by omega)
            _ = (10 * fr ^ 3) *
                  (CA w₄ * Combinatorics.windowPairCellCount (w₃ + 2) (w₄ + 2)) *
                  Combinatorics.boundedFactorGridWindow b K (w₂ + 3) := by ring
  refine le_trans (rfns_iteratedCovGrad_appCcRS_diagonalProductGrid_rankLeft_le (I := I)
    (M := M) g₀ w 0 6 4 (cometricDoubleTraceField (I := I) g₀ 4)
    (rsDomDomCongrSection (I := I) (M := M) g₀ 0 6 σ
      (appCcRS (I := I) (M := M) g₀ 0 3 6
        (slotExtendIter (I := I) (M := M) g₀ 0 3 3 (koszulCovecCc (I := I) g₀ P))
        (connDiffLoweredCc (I := I) g₀ g₁))) x) ?_
  calc appCcGdiag (E := E) w *
        ∑ w₁ ∈ Finset.range (w + 1),
          riemannianFiberNormSq (I := I) (M := M) g₀ 6 (4 + w₁) x
              ((iteratedCovGrad (I := I) g₀ 6 4 w₁
                (cometricDoubleTraceField (I := I) g₀ 4)).toSection x) *
            ∑ w₂ ∈ Finset.range (w + 1 - w₁),
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (6 + w₂) x
                ((iteratedCovGrad (I := I) g₀ 0 6 w₂
                  (rsDomDomCongrSection (I := I) (M := M) g₀ 0 6 σ
                    (appCcRS (I := I) (M := M) g₀ 0 3 6
                      (slotExtendIter (I := I) (M := M) g₀ 0 3 3
                        (koszulCovecCc (I := I) g₀ P))
                      (connDiffLoweredCc (I := I) g₀ g₁)))).toSection x)
      ≤ appCcGdiag (E := E) w *
          ∑ w₁ ∈ Finset.range (w + 1), KD w₁ *
            ∑ w₂ ∈ Finset.range (w + 1 - w₁),
              ((appCcGdiag (E := E) w₂ *
                ∑ w₃ ∈ Finset.range (w₂ + 1), (10 * fr ^ 3) *
                  ∑ w₄ ∈ Finset.range (w₂ + 1 - w₃),
                    CA w₄ * Combinatorics.windowPairCellCount (w₃ + 2) (w₄ + 2)) *
                Combinatorics.boundedFactorGridWindow b K (w + 3)) := by
        refine mul_le_mul_of_nonneg_left
          (Finset.sum_le_sum fun w₁ hw₁ => ?_) (appCcGdiag_nonneg (E := E) w)
        rw [Finset.mem_range] at hw₁
        refine mul_le_mul (hKD w₁ x) (Finset.sum_le_sum fun w₂ hw₂ => ?_)
          (Finset.sum_nonneg fun w₂ _ =>
            riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (6 + w₂) x _)
          (hKD_nn w₁)
        rw [Finset.mem_range] at hw₂
        refine le_trans (hbase w₂ (by omega)) ?_
        refine mul_le_mul_of_nonneg_left
          (Combinatorics.boundedFactorGridWindow_mono b hb_nn (le_refl _) (by omega))
          (mul_nonneg (appCcGdiag_nonneg (E := E) w₂)
            (Finset.sum_nonneg fun w₃ _ =>
              mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hfr_nn 3))
                (Finset.sum_nonneg fun w₄ _ => mul_nonneg (hCA_nn w₄)
                  (Combinatorics.windowPairCellCount_nonneg _ _))))
    _ = (appCcGdiag (E := E) w *
          ∑ w₁ ∈ Finset.range (w + 1), KD w₁ *
            ∑ w₂ ∈ Finset.range (w + 1 - w₁),
              appCcGdiag (E := E) w₂ *
                ∑ w₃ ∈ Finset.range (w₂ + 1), (10 * fr ^ 3) *
                  ∑ w₄ ∈ Finset.range (w₂ + 1 - w₃),
                    CA w₄ * Combinatorics.windowPairCellCount (w₃ + 2) (w₄ + 2)) *
          Combinatorics.boundedFactorGridWindow b K (w + 3) := by
        have hstep : ∀ w₁ : ℕ, (KD w₁ *
            ∑ w₂ ∈ Finset.range (w + 1 - w₁),
              ((appCcGdiag (E := E) w₂ *
                ∑ w₃ ∈ Finset.range (w₂ + 1), (10 * fr ^ 3) *
                  ∑ w₄ ∈ Finset.range (w₂ + 1 - w₃),
                    CA w₄ * Combinatorics.windowPairCellCount (w₃ + 2) (w₄ + 2)) *
                Combinatorics.boundedFactorGridWindow b K (w + 3))) =
            (KD w₁ * ∑ w₂ ∈ Finset.range (w + 1 - w₁),
              appCcGdiag (E := E) w₂ *
                ∑ w₃ ∈ Finset.range (w₂ + 1), (10 * fr ^ 3) *
                  ∑ w₄ ∈ Finset.range (w₂ + 1 - w₃),
                    CA w₄ * Combinatorics.windowPairCellCount (w₃ + 2) (w₄ + 2)) *
              Combinatorics.boundedFactorGridWindow b K (w + 3) := by
          intro w₁
          rw [← Finset.sum_mul]
          ring
        rw [Finset.sum_congr rfl fun w₁ _ => hstep w₁, ← Finset.sum_mul]
        ring

end bgrConversion

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
