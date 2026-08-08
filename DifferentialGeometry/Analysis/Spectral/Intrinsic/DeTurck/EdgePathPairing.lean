import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.EdgeRefoldPairing
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.EdgeRicciPairing
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.RHSRefoldPathIntegral
import DifferentialGeometry.Geometry.Metric.TensorInner.TensorRSRiemannianBundle

/-!
# Path-integrated closed-edge formal pairing

This module integrates the complete polarized Riemann--Lie top pair and its
formal partner along the realized radial metric path.  The endpoint is kept in
formal-partner form: no spatial integration by parts is performed, so a later
consumer may test against `L² T` without creating an `H⁵` charge.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000

open Bundle Manifold Set Filter Tensor0SBundle MeasureTheory intervalIntegral
open scoped BigOperators Manifold Topology ContDiff RealInnerProductSpace

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace IntrinsicSpectral

open DifferentialGeometry
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert
open DifferentialGeometry.PDE.DeTurck.RicciLinearization
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete Real E

private abbrev JointRS
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (S : Set Real)
    (A : Real → SmoothCcTensor g r s) : Prop :=
  ContMDiffOn (I.prod 𝓘(Real, Real))
    (I.prod 𝓘(Real, TensorRSModel r s Real E)) ∞
    (fun p : M × Real => TotalSpace.mk' (TensorRSModel r s Real E)
      (E := fun x : M => TensorRSSpace r s I x) p.1
      ((A p.2).toSection p.1))
    ((Set.univ : Set M) ×ˢ S)

omit [NeZero (Module.finrank Real E)] [CompactSpace M] [I.Boundaryless]
    [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private theorem joint_const
    (g : SmoothRiemannianMetric I M) {r s : ℕ} {S : Set Real}
    (A : SmoothCcTensor g r s) :
    JointRS (I := I) g r s S (fun _ => A) := by
  exact (A.toSection.contMDiff.comp_contMDiffOn contMDiffOn_fst).mono
    (Set.subset_univ _)

omit [NeZero (Module.finrank Real E)] [CompactSpace M] [I.Boundaryless]
    [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private theorem joint_add
    (g : SmoothRiemannianMetric I M) {r s : ℕ} {S : Set Real}
    (A B : Real → SmoothCcTensor g r s)
    (hA : JointRS (I := I) g r s S A)
    (hB : JointRS (I := I) g r s S B) :
    JointRS (I := I) g r s S (fun t => A t + B t) := by
  have h := joint_rs_add (I := I) (r := r) (s := s) (S := S)
    (fun p : M × Real => (A p.2).toSection p.1)
    (fun p : M × Real => (B p.2).toSection p.1) hA hB
  refine h.congr (fun p _ => ?_)
  refine congrArg (fun z => TotalSpace.mk' (TensorRSModel r s Real E)
    (E := fun x : M => TensorRSSpace r s I x) p.1 z) ?_
  rw [SmoothCcTensor.toSection_add, ContMDiffSection.coe_add, Pi.add_apply]

omit [NeZero (Module.finrank Real E)] [CompactSpace M] [I.Boundaryless]
    [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private theorem joint_sub
    (g : SmoothRiemannianMetric I M) {r s : ℕ} {S : Set Real}
    (A B : Real → SmoothCcTensor g r s)
    (hA : JointRS (I := I) g r s S A)
    (hB : JointRS (I := I) g r s S B) :
    JointRS (I := I) g r s S (fun t => A t - B t) := by
  have h := joint_rs_sub (I := I) (r := r) (s := s) (S := S)
    (fun p : M × Real => (A p.2).toSection p.1)
    (fun p : M × Real => (B p.2).toSection p.1) hA hB
  refine h.congr (fun p _ => ?_)
  refine congrArg (fun z => TotalSpace.mk' (TensorRSModel r s Real E)
    (E := fun x : M => TensorRSSpace r s I x) p.1 z) ?_
  rw [SmoothCcTensor.toSection_sub, ContMDiffSection.coe_sub, Pi.sub_apply]

omit [NeZero (Module.finrank Real E)] [CompactSpace M] [I.Boundaryless]
    [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private theorem joint_smul
    (g : SmoothRiemannianMetric I M) {r s : ℕ} {S : Set Real}
    (c : Real) (A : Real → SmoothCcTensor g r s)
    (hA : JointRS (I := I) g r s S A) :
    JointRS (I := I) g r s S (fun t => c • A t) := by
  letI := tensorRSBundle_topology (𝕜 := Real) (E := E) (H := H)
    (I := I) (M := M) r s
  intro p hp
  rw [Bundle.contMDiffWithinAt_totalSpace]
  refine ⟨contMDiffWithinAt_fst, ?_⟩
  set x := p.1 with hx
  set e := trivializationAt (TensorRSModel r s Real E)
    (fun z : M => TensorRSSpace r s I z) x with he
  have hA' := (Bundle.contMDiffWithinAt_totalSpace
    (F := TensorRSModel r s Real E)
    (E := fun z : M => TensorRSSpace r s I z)).mp (hA p hp)
  refine ((contMDiffWithinAt_const (c := c)).smul hA'.2).congr_of_eventuallyEq ?_ ?_
  · have hbase : ∀ᶠ q : M × Real in nhdsWithin p ((Set.univ : Set M) ×ˢ S),
        q.1 ∈ e.baseSet :=
      (continuousWithinAt_fst (s := (Set.univ : Set M) ×ˢ S) (p := p))
        (e.open_baseSet.mem_nhds (by
          rw [he]
          exact mem_baseSet_trivializationAt _ _ x))
    filter_upwards [hbase] with q hq
    exact (e.linear Real hq).map_smul c ((A q.2).toSection q.1)
  · exact (e.linear Real (by
      rw [he, ← hx]
      exact mem_baseSet_trivializationAt _ _ x)).map_smul
        c ((A p.2).toSection p.1)

omit [NeZero (Module.finrank Real E)] [CompactSpace M] [I.Boundaryless]
    [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private theorem joint_param_smul
    (g : SmoothRiemannianMetric I M) {r s : ℕ} {S : Set Real}
    (A : Real → SmoothCcTensor g r s)
    (hA : JointRS (I := I) g r s S A) :
    JointRS (I := I) g r s S (fun t => t • A t) := by
  letI := tensorRSBundle_topology (𝕜 := Real) (E := E) (H := H)
    (I := I) (M := M) r s
  intro p hp
  rw [Bundle.contMDiffWithinAt_totalSpace]
  refine ⟨contMDiffWithinAt_fst, ?_⟩
  set x := p.1 with hx
  set e := trivializationAt (TensorRSModel r s Real E)
    (fun z : M => TensorRSSpace r s I z) x with he
  have hA' := (Bundle.contMDiffWithinAt_totalSpace
    (F := TensorRSModel r s Real E)
    (E := fun z : M => TensorRSSpace r s I z)).mp (hA p hp)
  refine (contMDiffWithinAt_snd.smul hA'.2).congr_of_eventuallyEq ?_ ?_
  · have hbase : ∀ᶠ q : M × Real in nhdsWithin p ((Set.univ : Set M) ×ˢ S),
        q.1 ∈ e.baseSet :=
      (continuousWithinAt_fst (s := (Set.univ : Set M) ×ˢ S) (p := p))
        (e.open_baseSet.mem_nhds (by
          rw [he]
          exact mem_baseSet_trivializationAt _ _ x))
    filter_upwards [hbase] with q hq
    exact (e.linear Real hq).map_smul q.2 ((A q.2).toSection q.1)
  · exact (e.linear Real (by
      rw [he, ← hx]
      exact mem_baseSet_trivializationAt _ _ x)).map_smul
        p.2 ((A p.2).toSection p.1)

private theorem joint_app
    (g : SmoothRiemannianMetric I M) {a b c : ℕ} {S : Set Real}
    (A : Real → SmoothCcTensor g b c) (B : Real → SmoothCcTensor g a b)
    (hA : JointRS (I := I) g b c S A)
    (hB : JointRS (I := I) g a b S B) :
    JointRS (I := I) g a c S
      (fun t => appCcRS (I := I) (M := M) g a b c (A t) (B t)) := by
  apply contMDiffOn_clm_section_of_pointwise_jointMR (I := I) (M := M)
    (F₁ := Tensor0SModel a Real E) (V₁ := fun x : M => Tensor0SSpace a I x)
    (F₂ := Tensor0SModel c Real E) (V₂ := fun x : M => Tensor0SSpace c I x)
    (φ := fun p : M × Real =>
      (show Tensor0SSpace a I p.1 →L[Real] Tensor0SSpace c I p.1 from
        (appCcRS (I := I) (M := M) g a b c (A p.2) (B p.2)).toSection p.1))
    (S := S)
  intro Y
  have hY : ContMDiffOn (I.prod 𝓘(Real, Real))
      (I.prod 𝓘(Real, Tensor0SModel a Real E)) ∞
      (fun p : M × Real => TotalSpace.mk' (Tensor0SModel a Real E)
        (E := fun x : M => Tensor0SSpace a I x) p.1 (Y p.1))
      ((Set.univ : Set M) ×ˢ S) :=
    Y.contMDiff.comp_contMDiffOn contMDiffOn_fst
  have hBY := ContMDiffOn.clm_bundle_apply (b := Prod.fst) hB hY
  have hABY := ContMDiffOn.clm_bundle_apply (b := Prod.fst) hA hBY
  refine hABY.congr (fun p _ => ?_)
  refine congrArg (fun z => TotalSpace.mk' (Tensor0SModel c Real E)
    (E := fun x : M => Tensor0SSpace c I x) p.1 z) ?_
  rw [appCcRS_toSection]
  rfl

private theorem perm_app
    (g : SmoothRiemannianMetric I M) {d : ℕ}
    (rho : Equiv.Perm (Fin d)) (A : SmoothCcTensor g 0 d) :
    appCcRS (I := I) (M := M) g 0 d d
        (permCoeff (I := I) (M := M) g rho) A =
      domDomCongrSection (I := I) g rho A := by
  refine smoothCcTensor_ext_of_unitModel (I := I) (M := M) g fun x => ?_
  rw [domDomCongrSection_unitModel]
  rw [unitModel, appCcRS_toSection, ContinuousLinearMap.comp_apply]
  change Tensor0SSpace.toModel
      (slotPermCLM (I := I) rho x
        ((show Tensor0SSpace 0 I x →L[Real] Tensor0SSpace d I x from
          A.toSection x) (unitTensor (I := I) (M := M) x))) = _
  rw [slotPermCLM_apply, Tensor0SSpace.toModel_ofModel]
  rfl

private theorem joint_perm
    (g : SmoothRiemannianMetric I M) {d : ℕ} {S : Set Real}
    (rho : Equiv.Perm (Fin d)) (A : Real → SmoothCcTensor g 0 d)
    (hA : JointRS (I := I) g 0 d S A) :
    JointRS (I := I) g 0 d S
      (fun t => domDomCongrSection (I := I) g rho (A t)) := by
  have hP := joint_const (I := I) (M := M) (S := S) g
    (permCoeff (I := I) (M := M) g rho)
  have h := joint_app (I := I) (M := M)
    (a := 0) (b := d) (c := d) g
    (fun _ => permCoeff (I := I) (M := M) g rho) A hP hA
  simpa only [perm_app (I := I) (M := M)] using h

private theorem fullRaised_joint
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    {delta : Real}
    (hdelta : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) delta)
    (hdeltaZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g (0 : SmoothCcTensor g 0 2)) delta) :
    ContMDiffOn (I.prod 𝓘(Real, Real)) (I.prod 𝓘(Real, E →L[Real] E)) ∞
      (fun p : M × Real => TotalSpace.mk' (E →L[Real] E)
        (E := fun x : M => TangentSpace I x →L[Real] TangentSpace I x) p.1
        (fullRaisedEndoField (I := I) (M := M) g
          (realizedFam (I := I) g T 0 hdelta hdeltaZ p.2) p.1))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := delta) (δ' := delta)) := by
  apply contMDiffOn_clm_section_of_pointwise_jointMR (I := I) (M := M)
    (F₁ := E) (V₁ := fun x : M => TangentSpace I x)
    (F₂ := E) (V₂ := fun x : M => TangentSpace I x)
    (φ := fun p : M × Real =>
      fullRaisedEndoField (I := I) (M := M) g
        (realizedFam (I := I) g T 0 hdelta hdeltaZ p.2) p.1)
    (S := realizedSmallSet (δ := delta) (δ' := delta))
  intro Y
  have hY : ContMDiffOn (I.prod 𝓘(Real, Real)) (I.prod 𝓘(Real, E)) ∞
      (fun p : M × Real => TotalSpace.mk' E
        (E := fun x : M => TangentSpace I x) p.1 (Y p.1))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := delta) (δ' := delta)) :=
    Y.contMDiff.comp_contMDiffOn contMDiffOn_fst
  have hflat : ContMDiffOn (I.prod 𝓘(Real, Real))
      (I.prod 𝓘(Real, E →L[Real] Tensor0SModel 1 Real E)) ∞
      (fun p : M × Real => TotalSpace.mk' (E →L[Real] Tensor0SModel 1 Real E)
        (E := fun x : M => TangentSpace I x →L[Real] Tensor0SSpace 1 I x) p.1
        (g0FlatCLM (I := I) g p.1))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := delta) (δ' := delta)) :=
    (g0FlatField_contMDiff (I := I) g).comp_contMDiffOn contMDiffOn_fst
  have hflatY := ContMDiffOn.clm_bundle_apply (b := Prod.fst) hflat hY
  have hsharp := inverseMetricSharpField_realizedFam_jointContMDiffOn
    (I := I) (M := M) g T 0 hdelta hdeltaZ
  have hout := ContMDiffOn.clm_bundle_apply (b := Prod.fst) hsharp hflatY
  refine hout.congr (fun p _ => ?_)
  rfl

private theorem slotInsert_joint
    (g : SmoothRiemannianMetric I M) (d : ℕ)
    (T : SmoothCcTensor g 0 2) {delta : Real}
    (hdelta : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) delta)
    (hdeltaZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g (0 : SmoothCcTensor g 0 2)) delta) :
    JointRS (I := I) g (d + 1) (d + 1)
      (realizedSmallSet (δ := delta) (δ' := delta))
      (fun t => slotInsertEndoCc (I := I) (M := M) g d
        (fullRaisedEndoField (I := I) (M := M) g
          (realizedFam (I := I) g T 0 hdelta hdeltaZ t))) := by
  apply contMDiffOn_clm_section_of_pointwise_jointMR (I := I) (M := M)
    (F₁ := Tensor0SModel (d + 1) Real E)
    (V₁ := fun x : M => Tensor0SSpace (d + 1) I x)
    (F₂ := Tensor0SModel (d + 1) Real E)
    (V₂ := fun x : M => Tensor0SSpace (d + 1) I x)
    (φ := fun p : M × Real =>
      (show Tensor0SSpace (d + 1) I p.1 →L[Real]
          Tensor0SSpace (d + 1) I p.1 from
        (slotInsertEndoCc (I := I) (M := M) g d
          (fullRaisedEndoField (I := I) (M := M) g
            (realizedFam (I := I) g T 0 hdelta hdeltaZ p.2))).toSection p.1))
    (S := realizedSmallSet (δ := delta) (δ' := delta))
  intro Y
  have hY : ContMDiffOn (I.prod 𝓘(Real, Real))
      (I.prod 𝓘(Real, Tensor0SModel (d + 1) Real E)) ∞
      (fun p : M × Real => TotalSpace.mk' (Tensor0SModel (d + 1) Real E)
        (E := fun x : M => Tensor0SSpace (d + 1) I x) p.1 (Y p.1))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := delta) (δ' := delta)) :=
    Y.contMDiff.comp_contMDiffOn contMDiffOn_fst
  have hout := slotInsertEndo0Field_apply_jointContMDiffOn
    (I := I) (M := M) (d := d)
    (fun p : M × Real => fullRaisedEndoField (I := I) (M := M) g
      (realizedFam (I := I) g T 0 hdelta hdeltaZ p.2) p.1)
    (fullRaised_joint (I := I) (M := M) g T hdelta hdeltaZ)
    (fun p : M × Real => Y p.1) hY
  refine hout.congr (fun p _ => ?_)
  refine congrArg (fun z => TotalSpace.mk' (Tensor0SModel (d + 1) Real E)
    (E := fun x : M => Tensor0SSpace (d + 1) I x) p.1 z) ?_
  rw [slotInsertEndoCc_toSection]

private theorem edgeSlot_joint
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    {delta : Real}
    (hdelta : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) delta)
    (hdeltaZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g (0 : SmoothCcTensor g 0 2)) delta)
    (j : Fin 2) (A : Real → SmoothCcTensor g 0 2)
    (hA : JointRS (I := I) g 0 2
      (realizedSmallSet (δ := delta) (δ' := delta)) A) :
    JointRS (I := I) g 0 2
      (realizedSmallSet (δ := delta) (δ' := delta))
      (fun t => edgeSlot2 (I := I) (M := M) g
        (fullRaisedEndoField (I := I) (M := M) g
          (realizedFam (I := I) g T 0 hdelta hdeltaZ t)) j (A t)) := by
  let rho : Equiv.Perm (Fin 2) := Equiv.swap (0 : Fin 2) j
  have hAperm := joint_perm (I := I) (M := M) g rho A hA
  have hOp := slotInsert_joint (I := I) (M := M) g 1 T hdelta hdeltaZ
  have hApp := joint_app (I := I) (M := M)
    (a := 0) (b := 2) (c := 2) g _ _ hOp hAperm
  have hOut := joint_perm (I := I) (M := M) g rho _ hApp
  simpa only [edgeSlot2, rho, appCcRS_zero_eq_appCc] using hOut

private theorem edgeRaise_joint
    (g : SmoothRiemannianMetric I M) (T P : SmoothCcTensor g 0 2)
    {delta : Real}
    (hdelta : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) delta)
    (hdeltaZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g (0 : SmoothCcTensor g 0 2)) delta) :
    JointRS (I := I) g 0 2
      (realizedSmallSet (δ := delta) (δ' := delta))
      (fun t => edgeRaise2 (I := I) (M := M) g
        (realizedFam (I := I) g T 0 hdelta hdeltaZ t) P) := by
  have hP := joint_const (I := I) (M := M)
    (S := realizedSmallSet (δ := delta) (δ' := delta)) g P
  have h0 := edgeSlot_joint (I := I) (M := M)
    g T hdelta hdeltaZ 0 (fun _ => P) hP
  have h1 := edgeSlot_joint (I := I) (M := M)
    g T hdelta hdeltaZ 1 _ h0
  simpa only [edgeRaise2] using h1

private theorem edgeProd_joint
    (g : SmoothRiemannianMetric I M) {S : Set Real}
    (A : Real → SmoothCcTensor g 0 2) (V : SmoothCcTensor g 0 2)
    (hA : JointRS (I := I) g 0 2 S A) :
    JointRS (I := I) g 0 4 S
      (fun t => edgeProd4 (I := I) (M := M) g (A t) V) := by
  have hC := joint_const (I := I) (M := M) (S := S) g
    (slotExtendIter (I := I) (M := M) g 0 2 2 V)
  have h := joint_app (I := I) (M := M)
    (a := 0) (b := 2) (c := 4) g _ A hC hA
  simpa only [edgeProd4, appCcRS_zero_eq_appCc] using h

private theorem edgePartner_joint
    (g : SmoothRiemannianMetric I M) (T P V : SmoothCcTensor g 0 2)
    {delta : Real}
    (hdelta : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) delta)
    (hdeltaZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g (0 : SmoothCcTensor g 0 2)) delta)
    (sigma : Equiv.Perm (Fin 4)) :
    JointRS (I := I) g 0 4
      (realizedSmallSet (δ := delta) (δ' := delta))
      (fun t => edgePairPartnerBi (I := I) (M := M) g
        (realizedFam (I := I) g T 0 hdelta hdeltaZ t) P V sigma) := by
  have hRaise := edgeRaise_joint (I := I) (M := M)
    g T P hdelta hdeltaZ
  have hProd := edgeProd_joint (I := I) (M := M) g _ V hRaise
  have hPerm := joint_perm (I := I) (M := M) g sigma.symm _ hProd
  simpa only [edgePairPartnerBi] using hPerm

theorem edgeTopPair_joint
    (g : SmoothRiemannianMetric I M) (T U : SmoothCcTensor g 0 2)
    {delta : Real}
    (hdelta : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) delta)
    (hdeltaZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g (0 : SmoothCcTensor g 0 2)) delta)
    (qA qB : Fin 4 → Equiv.Perm (Fin 4))
    (q : Fin 3 → Equiv.Perm (Fin 4)) (epsilon : Fin 3 → Real) :
    JointRS (I := I) g 2 2
      (realizedSmallSet (δ := delta) (δ' := delta))
      (edgeTopPairBi (I := I) (M := M) g T U hdelta hdeltaZ
        qA qB q epsilon) := by
  let G := iteratedCovGrad (I := I) g 0 2 2 U
  have hmono : ∀ sigma : Equiv.Perm (Fin 4),
      JointRS (I := I) g 2 2
        (realizedSmallSet (δ := delta) (δ' := delta))
        (fun t => edgePairMono (I := I) (M := M) g
          (realizedFam (I := I) g T 0 hdelta hdeltaZ t) G sigma) :=
    fun sigma => edgePairMono_joint (I := I) (M := M)
      g T hdelta hdeltaZ G sigma
  have hkernel : ∀ qs : Fin 4 → Equiv.Perm (Fin 4),
      JointRS (I := I) g 2 2
        (realizedSmallSet (δ := delta) (δ' := delta))
        (fun t => edgeKernelPair (I := I) (M := M) g
          (realizedFam (I := I) g T 0 hdelta hdeltaZ t) G qs) := by
    intro qs
    have hsum := joint_sub (I := I) (M := M) g _ _
      (joint_sub (I := I) (M := M) g _ _
        (joint_add (I := I) (M := M) g _ _ (hmono (qs 0)) (hmono (qs 1)))
        (hmono (qs 2)))
      (hmono (qs 3))
    simpa only [edgeKernelPair] using
      joint_smul (I := I) (M := M) g (1 / 2 : Real) _ hsum
  have hR0 := joint_add (I := I) (M := M) g _ _ (hkernel qA) (hkernel qB)
  have hR1 := joint_smul (I := I) (M := M) g (1 / 2 : Real) _ hR0
  have hR2 := joint_param_smul (I := I) (M := M) g _ hR1
  have hR := joint_smul (I := I) (M := M) g (2 : Real) _ hR2
  have hterm : ∀ i : Fin 3,
      JointRS (I := I) g 2 2
        (realizedSmallSet (δ := delta) (δ' := delta))
        (fun t => epsilon i • ((1 / 2 : Real) •
          (edgePairMono (I := I) (M := M) g
              (realizedFam (I := I) g T 0 hdelta hdeltaZ t) G (q i) +
            edgePairMono (I := I) (M := M) g
              (realizedFam (I := I) g T 0 hdelta hdeltaZ t) G
              ((q i).trans (Equiv.swap (0 : Fin 4) 1))))) := by
    intro i
    exact joint_smul (I := I) (M := M) g (epsilon i) _
      (joint_smul (I := I) (M := M) g (1 / 2 : Real) _
        (joint_add (I := I) (M := M) g _ _
          (hmono (q i))
          (hmono ((q i).trans (Equiv.swap (0 : Fin 4) 1)))))
  have hL0 := joint_add (I := I) (M := M) g _ _
    (joint_add (I := I) (M := M) g _ _ (hterm 0) (hterm 1)) (hterm 2)
  have hL := joint_param_smul (I := I) (M := M) g _ hL0
  have hall := joint_add (I := I) (M := M) g _ _ hR hL
  change JointRS (I := I) g 2 2
    (realizedSmallSet (δ := delta) (δ' := delta))
    (fun t =>
      (2 : Real) • (t • ((1 / 2 : Real) •
        (edgeKernelPair (I := I) (M := M) g
            (realizedFam (I := I) g T 0 hdelta hdeltaZ t) G qA +
          edgeKernelPair (I := I) (M := M) g
            (realizedFam (I := I) g T 0 hdelta hdeltaZ t) G qB))) +
      t • ∑ i : Fin 3, epsilon i • ((1 / 2 : Real) •
        (edgePairMono (I := I) (M := M) g
            (realizedFam (I := I) g T 0 hdelta hdeltaZ t) G (q i) +
          edgePairMono (I := I) (M := M) g
            (realizedFam (I := I) g T 0 hdelta hdeltaZ t) G
            ((q i).trans (Equiv.swap (0 : Fin 4) 1)))))
  simpa only [Fin.sum_univ_three] using hall

private theorem edgeTopPartner_joint
    (g : SmoothRiemannianMetric I M) (T P V : SmoothCcTensor g 0 2)
    {delta : Real}
    (hdelta : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) delta)
    (hdeltaZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g (0 : SmoothCcTensor g 0 2)) delta)
    (qA qB : Fin 4 → Equiv.Perm (Fin 4))
    (q : Fin 3 → Equiv.Perm (Fin 4)) (epsilon : Fin 3 → Real) :
    JointRS (I := I) g 0 4
      (realizedSmallSet (δ := delta) (δ' := delta))
      (edgeTopPartnerBi (I := I) (M := M) g T P V hdelta hdeltaZ
        qA qB q epsilon) := by
  have hmono : ∀ sigma : Equiv.Perm (Fin 4),
      JointRS (I := I) g 0 4
        (realizedSmallSet (δ := delta) (δ' := delta))
        (fun t => edgePairPartnerBi (I := I) (M := M) g
          (realizedFam (I := I) g T 0 hdelta hdeltaZ t) P V sigma) :=
    fun sigma => edgePartner_joint (I := I) (M := M)
      g T P V hdelta hdeltaZ sigma
  have hkernel : ∀ qs : Fin 4 → Equiv.Perm (Fin 4),
      JointRS (I := I) g 0 4
        (realizedSmallSet (δ := delta) (δ' := delta))
        (fun t => (1 / 2 : Real) •
          (edgePairPartnerBi (I := I) (M := M) g
                (realizedFam (I := I) g T 0 hdelta hdeltaZ t) P V (qs 0) +
            edgePairPartnerBi (I := I) (M := M) g
                (realizedFam (I := I) g T 0 hdelta hdeltaZ t) P V (qs 1) -
            edgePairPartnerBi (I := I) (M := M) g
                (realizedFam (I := I) g T 0 hdelta hdeltaZ t) P V (qs 2) -
            edgePairPartnerBi (I := I) (M := M) g
              (realizedFam (I := I) g T 0 hdelta hdeltaZ t) P V (qs 3))) := by
    intro qs
    have hsum := joint_sub (I := I) (M := M) g _ _
      (joint_sub (I := I) (M := M) g _ _
        (joint_add (I := I) (M := M) g _ _ (hmono (qs 0)) (hmono (qs 1)))
        (hmono (qs 2)))
      (hmono (qs 3))
    exact joint_smul (I := I) (M := M) g (1 / 2 : Real) _ hsum
  have hR0 := joint_add (I := I) (M := M) g _ _ (hkernel qA) (hkernel qB)
  have hR1 := joint_smul (I := I) (M := M) g (1 / 2 : Real) _ hR0
  have hR2 := joint_param_smul (I := I) (M := M) g _ hR1
  have hR := joint_smul (I := I) (M := M) g (2 : Real) _ hR2
  have hterm : ∀ i : Fin 3,
      JointRS (I := I) g 0 4
        (realizedSmallSet (δ := delta) (δ' := delta))
        (fun t => epsilon i • ((1 / 2 : Real) •
          (edgePairPartnerBi (I := I) (M := M) g
              (realizedFam (I := I) g T 0 hdelta hdeltaZ t) P V (q i) +
            edgePairPartnerBi (I := I) (M := M) g
              (realizedFam (I := I) g T 0 hdelta hdeltaZ t) P V
              ((q i).trans (Equiv.swap (0 : Fin 4) 1))))) := by
    intro i
    exact joint_smul (I := I) (M := M) g (epsilon i) _
      (joint_smul (I := I) (M := M) g (1 / 2 : Real) _
        (joint_add (I := I) (M := M) g _ _
          (hmono (q i))
          (hmono ((q i).trans (Equiv.swap (0 : Fin 4) 1)))))
  have hL0 := joint_add (I := I) (M := M) g _ _
    (joint_add (I := I) (M := M) g _ _ (hterm 0) (hterm 1)) (hterm 2)
  have hL := joint_param_smul (I := I) (M := M) g _ hL0
  have hall := joint_add (I := I) (M := M) g _ _ hR hL
  change JointRS (I := I) g 0 4
    (realizedSmallSet (δ := delta) (δ' := delta))
    (fun t =>
      (2 : Real) • (t • ((1 / 2 : Real) •
        ((1 / 2 : Real) •
            (edgePairPartnerBi (I := I) (M := M) g
                (realizedFam (I := I) g T 0 hdelta hdeltaZ t) P V (qA 0) +
              edgePairPartnerBi (I := I) (M := M) g
                (realizedFam (I := I) g T 0 hdelta hdeltaZ t) P V (qA 1) -
              edgePairPartnerBi (I := I) (M := M) g
                (realizedFam (I := I) g T 0 hdelta hdeltaZ t) P V (qA 2) -
              edgePairPartnerBi (I := I) (M := M) g
                (realizedFam (I := I) g T 0 hdelta hdeltaZ t) P V (qA 3)) +
          (1 / 2 : Real) •
            (edgePairPartnerBi (I := I) (M := M) g
                (realizedFam (I := I) g T 0 hdelta hdeltaZ t) P V (qB 0) +
              edgePairPartnerBi (I := I) (M := M) g
                (realizedFam (I := I) g T 0 hdelta hdeltaZ t) P V (qB 1) -
              edgePairPartnerBi (I := I) (M := M) g
                (realizedFam (I := I) g T 0 hdelta hdeltaZ t) P V (qB 2) -
              edgePairPartnerBi (I := I) (M := M) g
                (realizedFam (I := I) g T 0 hdelta hdeltaZ t) P V (qB 3))))) +
      t • ∑ i : Fin 3, epsilon i • ((1 / 2 : Real) •
        (edgePairPartnerBi (I := I) (M := M) g
            (realizedFam (I := I) g T 0 hdelta hdeltaZ t) P V (q i) +
          edgePairPartnerBi (I := I) (M := M) g
            (realizedFam (I := I) g T 0 hdelta hdeltaZ t) P V
            ((q i).trans (Equiv.swap (0 : Fin 4) 1)))))
  simpa only [Fin.sum_univ_three] using hall

/-- Path integral of the complete polarized raw top pair.  The radial metric
path is fixed by `T`, while `U` supplies the Hessian in the coefficient. -/
def edgeTopPairInt
    (g : SmoothRiemannianMetric I M) (T U : SmoothCcTensor g 0 2)
    {delta : Real} (hdelta_lt : delta < 1)
    (hdelta : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) delta)
    (hdeltaZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g (0 : SmoothCcTensor g 0 2)) delta)
    (qA qB : Fin 4 → Equiv.Perm (Fin 4))
    (q : Fin 3 → Equiv.Perm (Fin 4)) (epsilon : Fin 3 → Real) :
    SmoothCcTensor g 2 2 :=
  pathIntegralCoeffField (I := I) (M := M) g 2 2
    (edgeTopPairBi (I := I) (M := M) g T U hdelta hdeltaZ
      qA qB q epsilon)
    (realizedSmallSet (δ := delta) (δ' := delta)) realizedSmallSet_isOpen
    (by
      rw [Set.uIcc_of_le zero_le_one]
      exact Icc_subset_realizedSmallSet hdelta_lt hdelta_lt)
    (edgeTopPair_joint (I := I) (M := M)
      g T U hdelta hdeltaZ qA qB q epsilon)

/-- Path integral of the complete polarized formal partner.  `P` is the
coefficient passenger and `V` is the test tensor. -/
def edgeTopPartnerInt
    (g : SmoothRiemannianMetric I M) (T P V : SmoothCcTensor g 0 2)
    {delta : Real} (hdelta_lt : delta < 1)
    (hdelta : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) delta)
    (hdeltaZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g (0 : SmoothCcTensor g 0 2)) delta)
    (qA qB : Fin 4 → Equiv.Perm (Fin 4))
    (q : Fin 3 → Equiv.Perm (Fin 4)) (epsilon : Fin 3 → Real) :
    SmoothCcTensor g 0 4 :=
  pathIntegralCoeffField (I := I) (M := M) g 0 4
    (edgeTopPartnerBi (I := I) (M := M) g T P V hdelta hdeltaZ
      qA qB q epsilon)
    (realizedSmallSet (δ := delta) (δ' := delta)) realizedSmallSet_isOpen
    (by
      rw [Set.uIcc_of_le zero_le_one]
      exact Icc_subset_realizedSmallSet hdelta_lt hdelta_lt)
    (edgeTopPartner_joint (I := I) (M := M)
      g T P V hdelta hdeltaZ qA qB q epsilon)

private theorem path_app_zero
    (g : SmoothRiemannianMetric I M) {b c : ℕ}
    (A : Real → SmoothCcTensor g b c) (W : SmoothCcTensor g 0 b)
    (S : Set Real) (hS : IsOpen S) (hSI : Set.uIcc (0 : Real) 1 ⊆ S)
    (hA : JointRS (I := I) g b c S A)
    (hApp : JointRS (I := I) g 0 c S
      (fun t => appCcRS (I := I) (M := M) g 0 b c (A t) W)) :
    pathIntegralCoeffField (I := I) (M := M) g 0 c
        (fun t => appCcRS (I := I) (M := M) g 0 b c (A t) W)
        S hS hSI hApp =
      appCc (I := I) (M := M) g b c
        (pathIntegralCoeffField (I := I) (M := M) g b c
          A S hS hSI hA) W := by
  classical
  apply smoothCcTensor_ext_of_unitModel (I := I) (M := M) g
  intro x
  apply ContinuousMultilinearMap.ext
  intro v
  have hcontA : ∀ y : M, ContinuousOn
      (fun t : Real => TensorRSSpace.toModel ((A t).toSection y)) S :=
    fun y => jointContMDiff_toModel_continuous_slice
      (I := I) g b c A S hA y
  rw [pathIntegralCoeffField_appCc_eq
    (I := I) (M := M) g b c A W S hS hSI hA hcontA x v]
  let Psi : Real → SmoothCcTensor g 0 c :=
    fun t => appCcRS (I := I) (M := M) g 0 b c (A t) W
  let u : Tensor0SModel 0 Real E :=
    Tensor0SSpace.toModel (unitTensor (I := I) (M := M) x)
  have hcontPsi : ContinuousOn
      (fun t : Real => TensorRSSpace.toModel ((Psi t).toSection x)) S :=
    jointContMDiff_toModel_continuous_slice
      (I := I) g 0 c Psi S hApp x
  have hPsiInt : IntervalIntegrable
      (fun t : Real => TensorRSSpace.toModel ((Psi t).toSection x))
      volume 0 1 :=
    (hcontPsi.mono hSI).intervalIntegrable
  have hcontApp : ContinuousOn
      (fun t : Real => (TensorRSSpace.toModel ((Psi t).toSection x)) u) S :=
    (ContinuousLinearMap.apply Real (Tensor0SModel c Real E) u).continuous.comp_continuousOn
      hcontPsi
  have hPsiAppInt : IntervalIntegrable
      (fun t : Real => (TensorRSSpace.toModel ((Psi t).toSection x)) u)
      volume 0 1 :=
    (hcontApp.mono hSI).intervalIntegrable
  let L : Tensor0SModel c Real E →L[Real] Real :=
    ContinuousMultilinearMap.apply Real (fun _ : Fin c => E) Real v
  rw [unitModel, toModel_tensorRS_apply (I := I) 0 c x]
  change L (TensorRSSpace.toModel
    ((pathIntegralCoeffField (I := I) (M := M) g 0 c Psi
      S hS hSI hApp).toSection x) u) = _
  rw [pathIntegralCoeffField_toModel]
  rw [ContinuousLinearMap.intervalIntegral_apply hPsiInt u]
  change L (∫ t in (0 : Real)..1,
    (TensorRSSpace.toModel ((Psi t).toSection x)) u) = _
  rw [← ContinuousLinearMap.intervalIntegral_comp_comm L hPsiAppInt]
  refine intervalIntegral.integral_congr (fun t _ => ?_)
  change unitModel (I := I) (M := M) g c (Psi t) x v =
    unitModel (I := I) (M := M) g c
      (appCc (I := I) (M := M) g b c (A t) W) x v
  simp only [Psi, appCcRS_zero_eq_appCc]

/-- Applying the integrated raw top-pair coefficient to a fixed passenger is
the path integral of the corresponding pointwise applications. -/
theorem edgeTopPairInt_apply
    (g : SmoothRiemannianMetric I M) (T U P : SmoothCcTensor g 0 2)
    {delta : Real} (hdelta_lt : delta < 1)
    (hdelta : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) delta)
    (hdeltaZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g (0 : SmoothCcTensor g 0 2)) delta)
    (qA qB : Fin 4 → Equiv.Perm (Fin 4))
    (q : Fin 3 → Equiv.Perm (Fin 4)) (epsilon : Fin 3 → Real) :
    appCc (I := I) (M := M) g 2 2
        (edgeTopPairInt (I := I) (M := M) g T U hdelta_lt
          hdelta hdeltaZ qA qB q epsilon) P =
      pathIntegralCoeffField (I := I) (M := M) g 0 2
        (fun t => appCcRS (I := I) (M := M) g 0 2 2
          (edgeTopPairBi (I := I) (M := M) g T U hdelta hdeltaZ
            qA qB q epsilon t) P)
        (realizedSmallSet (δ := delta) (δ' := delta)) realizedSmallSet_isOpen
        (by
          rw [Set.uIcc_of_le zero_le_one]
          exact Icc_subset_realizedSmallSet hdelta_lt hdelta_lt)
        (by
          have hA := edgeTopPair_joint (I := I) (M := M)
            g T U hdelta hdeltaZ qA qB q epsilon
          have hP := joint_const (I := I) (M := M)
            (S := realizedSmallSet (δ := delta) (δ' := delta)) g P
          simpa only using joint_app (I := I) (M := M)
            (a := 0) (b := 2) (c := 2) g
            (edgeTopPairBi (I := I) (M := M) g T U hdelta hdeltaZ
              qA qB q epsilon) (fun _ => P) hA hP) := by
  classical
  let S : Set Real := realizedSmallSet (δ := delta) (δ' := delta)
  have hS : IsOpen S := realizedSmallSet_isOpen
  have hSI : Set.uIcc (0 : Real) 1 ⊆ S := by
    rw [Set.uIcc_of_le zero_le_one]
    exact Icc_subset_realizedSmallSet hdelta_lt hdelta_lt
  let A : Real → SmoothCcTensor g 2 2 :=
    edgeTopPairBi (I := I) (M := M) g T U hdelta hdeltaZ
      qA qB q epsilon
  let AP : Real → SmoothCcTensor g 0 2 := fun t =>
    appCcRS (I := I) (M := M) g 0 2 2 (A t) P
  have hA : JointRS (I := I) g 2 2 S A := by
    simpa only [S, A] using edgeTopPair_joint (I := I) (M := M)
      g T U hdelta hdeltaZ qA qB q epsilon
  have hP := joint_const (I := I) (M := M) (S := S) g P
  have hAP : JointRS (I := I) g 0 2 S AP := by
    simpa only [AP] using joint_app (I := I) (M := M)
      (a := 0) (b := 2) (c := 2) g A (fun _ => P) hA hP
  have happ := path_app_zero (I := I) (M := M)
    g A P S hS hSI hA hAP
  simpa only [S, A, AP, edgeTopPairInt] using happ.symm

private theorem path_inner_point
    (g : SmoothRiemannianMetric I M)
    (V : SmoothCcTensor g 0 2) (G : SmoothCcTensor g 0 4)
    (A : Real → SmoothCcTensor g 0 2)
    (Z : Real → SmoothCcTensor g 0 4)
    (S : Set Real) (hS : IsOpen S) (hSI : Set.uIcc (0 : Real) 1 ⊆ S)
    (hA : JointRS (I := I) g 0 2 S A)
    (hZ : JointRS (I := I) g 0 4 S Z)
    (hpoint : ∀ t : Real, ∀ x : M,
      tensorInnerPointwise (I := I) (M := M) g 0 2 x
          (V.toFun x) ((A t).toFun x) =
        tensorInnerPointwise (I := I) (M := M) g 0 4 x
          ((Z t).toFun x) (G.toFun x)) :
    Inner.inner Real V
        (pathIntegralCoeffField (I := I) (M := M) g 0 2
          A S hS hSI hA) =
      Inner.inner Real
        (pathIntegralCoeffField (I := I) (M := M) g 0 4
          Z S hS hSI hZ) G := by
  rw [SmoothCcTensor.inner_def, SmoothCcTensor.inner_def]
  unfold tensorL2Inner
  refine MeasureTheory.integral_congr_ae
    (Filter.Eventually.of_forall fun x => ?_)
  have hcontA := jointContMDiff_toModel_continuous_slice
    (I := I) g 0 2 A S hA x
  have hcontZ := jointContMDiff_toModel_continuous_slice
    (I := I) g 0 4 Z S hZ x
  have hAInt : IntervalIntegrable
      (fun t : Real => TensorRSSpace.toModel ((A t).toSection x))
      volume 0 1 := (hcontA.mono hSI).intervalIntegrable
  have hZInt : IntervalIntegrable
      (fun t : Real => TensorRSSpace.toModel ((Z t).toSection x))
      volume 0 1 := (hcontZ.mono hSI).intervalIntegrable
  let LV : TensorRSModel 0 2 Real E →L[Real] Real :=
    DifferentialGeometry.Tensor.TensorRSRiemannianBundle.innerModelCLMRS
      (I := I) (M := M) g 0 2 x (V.toFun x)
  let LG : TensorRSModel 0 4 Real E →L[Real] Real :=
    (ContinuousLinearMap.apply Real Real (G.toFun x)).comp
      (DifferentialGeometry.Tensor.TensorRSRiemannianBundle.innerModelCLMRS
        (I := I) (M := M) g 0 4 x)
  change LV (TensorRSSpace.toModel
      ((pathIntegralCoeffField (I := I) (M := M) g 0 2
        A S hS hSI hA).toSection x)) =
    LG (TensorRSSpace.toModel
      ((pathIntegralCoeffField (I := I) (M := M) g 0 4
        Z S hS hSI hZ).toSection x))
  rw [pathIntegralCoeffField_toModel, pathIntegralCoeffField_toModel]
  rw [← ContinuousLinearMap.intervalIntegral_comp_comm LV hAInt]
  rw [← ContinuousLinearMap.intervalIntegral_comp_comm LG hZInt]
  refine intervalIntegral.integral_congr (fun t _ => ?_)
  change tensorInnerPointwise (I := I) (M := M) g 0 2 x
      (V.toFun x) ((A t).toFun x) =
    tensorInnerPointwise (I := I) (M := M) g 0 4 x
      ((Z t).toFun x) (G.toFun x)
  exact hpoint t x

/-- The path-integrated complete raw top pair has the path-integrated
polarized formal partner.  This identity performs no spatial integration by
parts and therefore remains admissible when `V` is an `L²`-order test. -/
theorem edgePath_inner_bi
    (g : SmoothRiemannianMetric I M) (T P U V : SmoothCcTensor g 0 2)
    {delta : Real} (hdelta_lt : delta < 1)
    (hdelta : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) delta)
    (hdeltaZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g (0 : SmoothCcTensor g 0 2)) delta)
    (qA qB : Fin 4 → Equiv.Perm (Fin 4))
    (q : Fin 3 → Equiv.Perm (Fin 4)) (epsilon : Fin 3 → Real) :
    Inner.inner Real V
        (appCc (I := I) (M := M) g 2 2
          (edgeTopPairInt (I := I) (M := M) g T U hdelta_lt
            hdelta hdeltaZ qA qB q epsilon) P) =
      Inner.inner Real
        (edgeTopPartnerInt (I := I) (M := M) g T P V hdelta_lt
          hdelta hdeltaZ qA qB q epsilon)
        (iteratedCovGrad (I := I) g 0 2 2 U) := by
  let S : Set Real := realizedSmallSet (δ := delta) (δ' := delta)
  have hS : IsOpen S := realizedSmallSet_isOpen
  have hSI : Set.uIcc (0 : Real) 1 ⊆ S := by
    rw [Set.uIcc_of_le zero_le_one]
    exact Icc_subset_realizedSmallSet hdelta_lt hdelta_lt
  let A : Real → SmoothCcTensor g 2 2 :=
    edgeTopPairBi (I := I) (M := M) g T U hdelta hdeltaZ
      qA qB q epsilon
  let Z : Real → SmoothCcTensor g 0 4 :=
    edgeTopPartnerBi (I := I) (M := M) g T P V hdelta hdeltaZ
      qA qB q epsilon
  let AP : Real → SmoothCcTensor g 0 2 := fun t =>
    appCcRS (I := I) (M := M) g 0 2 2 (A t) P
  have hA : JointRS (I := I) g 2 2 S A := by
    simpa only [S, A] using edgeTopPair_joint (I := I) (M := M)
      g T U hdelta hdeltaZ qA qB q epsilon
  have hZ : JointRS (I := I) g 0 4 S Z := by
    simpa only [S, Z] using edgeTopPartner_joint (I := I) (M := M)
      g T P V hdelta hdeltaZ qA qB q epsilon
  have hP := joint_const (I := I) (M := M) (S := S) g P
  have hAP : JointRS (I := I) g 0 2 S AP := by
    simpa only [AP] using joint_app (I := I) (M := M)
      (a := 0) (b := 2) (c := 2) g A (fun _ => P) hA hP
  have hpath := path_inner_point (I := I) (M := M) g V
    (iteratedCovGrad (I := I) g 0 2 2 U) AP Z S hS hSI hAP hZ
    (fun t x => by
      simpa only [AP, A, Z, appCcRS_zero_eq_appCc] using
        edgeTop_point_bi (I := I) (M := M) g T P U V
          hdelta hdeltaZ qA qB q epsilon t x)
  have happ := path_app_zero (I := I) (M := M)
    g A P S hS hSI hA hAP
  rw [edgeTopPairInt, edgeTopPartnerInt]
  rw [← happ]
  exact hpath

end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry
