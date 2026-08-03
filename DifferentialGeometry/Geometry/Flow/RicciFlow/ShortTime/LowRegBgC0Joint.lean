import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegBgC0Alg

/-!
# Order-zero joint-smooth families

Internal implementation layer for the low-regularity order-zero refold.
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

abbrev C0Joint
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
theorem c0j_const
    (g : SmoothRiemannianMetric I M) {r s : ℕ} {S : Set ℝ}
    (A : SmoothCcTensor g r s) :
    C0Joint (I := I) g r s S (fun _ => A) := by
  exact (A.toSection.contMDiff.comp_contMDiffOn contMDiffOn_fst).mono
    (Set.subset_univ _)

theorem c0j_app
    (g : SmoothRiemannianMetric I M) {a b c : ℕ} {S : Set ℝ}
    {A : ℝ → SmoothCcTensor g b c} {B : ℝ → SmoothCcTensor g a b}
    (hA : C0Joint (I := I) g b c S A)
    (hB : C0Joint (I := I) g a b S B) :
    C0Joint (I := I) g a c S
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
theorem c0j_param
    (g : SmoothRiemannianMetric I M) {r s : ℕ} {S : Set ℝ}
    {A : ℝ → SmoothCcTensor g r s}
    (hA : C0Joint (I := I) g r s S A) :
    C0Joint (I := I) g r s S (fun t => t • A t) := by
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
theorem c0j_add
    (g : SmoothRiemannianMetric I M) {r s : ℕ} {S : Set ℝ}
    {A B : ℝ → SmoothCcTensor g r s}
    (hA : C0Joint (I := I) g r s S A)
    (hB : C0Joint (I := I) g r s S B) :
    C0Joint (I := I) g r s S (fun t => A t + B t) := by
  have h := joint_rs_add (I := I) (r := r) (s := s) (S := S)
    (fun p : M × ℝ => (A p.2).toSection p.1)
    (fun p : M × ℝ => (B p.2).toSection p.1) hA hB
  refine h.congr (fun p _ => ?_)
  refine congrArg (fun z => TotalSpace.mk' (TensorRSModel r s ℝ E)
    (E := fun x : M => TensorRSSpace r s I x) p.1 z) ?_
  rw [SmoothCcTensor.toSection_add, ContMDiffSection.coe_add, Pi.add_apply]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
    [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
theorem c0j_sub
    (g : SmoothRiemannianMetric I M) {r s : ℕ} {S : Set ℝ}
    {A B : ℝ → SmoothCcTensor g r s}
    (hA : C0Joint (I := I) g r s S A)
    (hB : C0Joint (I := I) g r s S B) :
    C0Joint (I := I) g r s S (fun t => A t - B t) := by
  have h := joint_rs_sub (I := I) (r := r) (s := s) (S := S)
    (fun p : M × ℝ => (A p.2).toSection p.1)
    (fun p : M × ℝ => (B p.2).toSection p.1) hA hB
  refine h.congr (fun p _ => ?_)
  refine congrArg (fun z => TotalSpace.mk' (TensorRSModel r s ℝ E)
    (E := fun x : M => TensorRSSpace r s I x) p.1 z) ?_
  rw [SmoothCcTensor.toSection_sub, ContMDiffSection.coe_sub, Pi.sub_apply]

def lift0
    (g : SmoothRiemannianMetric I M) {s : ℕ}
    (Y : Cₛ^∞⟮I; Tensor0SModel s ℝ E,
      (fun x : M => Tensor0SSpace s I x)⟯) :
    SmoothCcTensor g 0 s where
  toSection :=
    MixedSection.fromMultilinearSection
      (𝕜 := ℝ) (F := E) (IB := I)
      (E := (TangentSpace I : M → Type _)) ∞ Y
  hasCompactSupport := HasCompactSupport.of_compactSpace _

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
    [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
theorem lift0_unit
    (g : SmoothRiemannianMetric I M) {s : ℕ}
    (Y : Cₛ^∞⟮I; Tensor0SModel s ℝ E,
      (fun x : M => Tensor0SSpace s I x)⟯) (x : M) :
    (lift0 (I := I) (M := M) g Y).toSection x
        (unitTensor (I := I) (M := M) x) = Y x := by
  have h := congrArg (fun Z => Z x)
    (MixedSection.toMultilinearSection_fromMultilinearSection
      (𝕜 := ℝ) (F := E) (IB := I)
      (E := (TangentSpace I : M → Type _)) ∞ Y)
  simpa only [lift0, MixedSection.toMultilinearSection,
    unitTensor, Tensor0SSpace.ofModel] using h

theorem slot24_joint
    (g : SmoothRiemannianMetric I M) {S : Set ℝ}
    {K : ℝ → SmoothCcTensor g 0 4}
    (hK : C0Joint (I := I) g 0 4 S K) :
    C0Joint (I := I) g 2 6 S
      (fun t => slotExtendIter (I := I) (M := M) g 0 4 2 (K t)) := by
  apply contMDiffOn_clm_section_of_pointwise_jointMR (I := I) (M := M)
    (F₁ := Tensor0SModel 2 ℝ E) (V₁ := fun x : M => Tensor0SSpace 2 I x)
    (F₂ := Tensor0SModel 6 ℝ E) (V₂ := fun x : M => Tensor0SSpace 6 I x)
    (φ := fun q : M × ℝ =>
      (slotExtendIter (I := I) (M := M) g 0 4 2 (K q.2)).toSection q.1)
    (S := S)
  intro Y
  have hY : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, Tensor0SModel 2 ℝ E)) ∞
      (fun q : M × ℝ => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
        (E := fun x : M => Tensor0SSpace 2 I x) q.1 (Y q.1))
      ((Set.univ : Set M) ×ˢ S) :=
    Y.contMDiff.comp_contMDiffOn contMDiffOn_fst
  have hunit : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, Tensor0SModel 0 ℝ E)) ∞
      (fun q : M × ℝ => TotalSpace.mk' (Tensor0SModel 0 ℝ E)
        (E := fun x : M => Tensor0SSpace 0 I x) q.1
        (unitZeroSec (I := I) (M := M) q.1))
      ((Set.univ : Set M) ×ˢ S) :=
    (unitZeroSec (I := I) (M := M)).contMDiff.comp_contMDiffOn
      contMDiffOn_fst
  have hKval := ContMDiffOn.clm_bundle_apply (b := Prod.fst) hK hunit
  have hprod := jointTensor0SProd_local (I := I) (p := 2) (q := 4)
    (S := S) (fun q : M × ℝ => Y q.1)
    (fun q : M × ℝ =>
      (show Tensor0SSpace 0 I q.1 →L[ℝ] Tensor0SSpace 4 I q.1 from
        (K q.2).toSection q.1) (unitTensor (I := I) (M := M) q.1))
    hY hKval
  have hprod' : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, Tensor0SModel 6 ℝ E)) ∞
      (fun q : M × ℝ => TotalSpace.mk' (Tensor0SModel 6 ℝ E)
        (E := fun x : M => Tensor0SSpace 6 I x) q.1
        (tensor0SProdKappaFib (I := I) (p := 2) (q := 4) q.1
          ((show Tensor0SSpace 0 I q.1 →L[ℝ] Tensor0SSpace 4 I q.1 from
            (K q.2).toSection q.1) (unitTensor (I := I) (M := M) q.1))
          (Y q.1)))
      ((Set.univ : Set M) ×ˢ S) := by
    refine hprod.congr (fun q _ => ?_)
    refine congrArg (fun z => TotalSpace.mk' (Tensor0SModel 6 ℝ E)
      (E := fun x : M => Tensor0SSpace 6 I x) q.1 z) ?_
    rw [tensor0SProdKappaFib_apply]
  refine hprod'.congr (fun q _ => ?_)
  refine congrArg (fun z => TotalSpace.mk' (Tensor0SModel 6 ℝ E)
    (E := fun x : M => Tensor0SSpace 6 I x) q.1 z) ?_
  exact slotLift24 (I := I) (M := M) g (K q.2) q.1 (Y q.1)

theorem connIns_c0j
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    {δ : ℝ}
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ) :
    C0Joint (I := I) g 3 4
      (realizedSmallSet (δ := δ) (δ' := δ))
      (fun t => connDiffContrInsertionField (I := I) g
        (realizedFam (I := I) g T 0 hδ hδZ t)) := by
  have h := connIns_joint (I := I) g T 0 hδ hδZ
  simpa only [connDiffContrInsertionField_toSection] using h

theorem fourCast_c0j
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    {δ : ℝ}
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ) :
    C0Joint (I := I) g 4 2
      (realizedSmallSet (δ := δ) (δ' := δ))
      (fun t => ricciCometricFourTraceCastG0 (I := I) g
        (realizedFam (I := I) g T 0 hδ hδZ t)) := by
  apply contMDiffOn_clm_section_of_pointwise_jointMR (I := I) (M := M)
    (F₁ := Tensor0SModel 4 ℝ E) (V₁ := fun x : M => Tensor0SSpace 4 I x)
    (F₂ := Tensor0SModel 2 ℝ E) (V₂ := fun x : M => Tensor0SSpace 2 I x)
    (φ := fun p : M × ℝ =>
      (ricciCometricFourTraceCastG0 (I := I) g
        (realizedFam (I := I) g T 0 hδ hδZ p.2)).toSection p.1)
    (S := realizedSmallSet (δ := δ) (δ' := δ))
  intro Y
  have hY : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, Tensor0SModel 4 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SModel 4 ℝ E)
        (E := fun x : M => Tensor0SSpace 4 I x) p.1 (Y p.1))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ)) :=
    Y.contMDiff.comp_contMDiffOn contMDiffOn_fst
  have h := fourTrace_joint (I := I) g T 0 hδ hδZ
    (fun p : M × ℝ => Y p.1) hY
  refine h.congr (fun p _ => ?_)
  refine congrArg (fun z => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
    (E := fun x : M => Tensor0SSpace 2 I x) p.1 z) ?_
  rw [ricciCometricFourTraceCastG0_toSection]

theorem innerAct_joint
    (g : SmoothRiemannianMetric I M) (T W : SmoothCcTensor g 0 2)
    {δ : ℝ}
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ) :
    C0Joint (I := I) g 3 3
      (realizedSmallSet (δ := δ) (δ' := δ))
      (fun t => innerAct (I := I) (M := M) g
        (realizedFam (I := I) g T 0 hδ hδZ t) W) := by
  have hA := c0j_const (I := I) (M := M) g
    (S := realizedSmallSet (δ := δ) (δ' := δ))
    (innerOne (I := I) (M := M) g W)
  have hB := LowBaseInternal.connLow_joint
    (I := I) (M := M) g T hδ hδZ
  simpa only [innerAct] using c0j_app (I := I) (M := M) g hA hB

theorem aaMid_joint
    (g : SmoothRiemannianMetric I M) (T W : SmoothCcTensor g 0 2)
    {δ : ℝ}
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ)
    (mid : Equiv.Perm (Fin 3)) (out : Equiv.Perm (Fin 4)) :
    C0Joint (I := I) g 3 4
      (realizedSmallSet (δ := δ) (δ' := δ))
      (fun t => aaMidOne (I := I) (M := M) g
        (realizedFam (I := I) g T 0 hδ hδZ t) W mid out) := by
  let S := realizedSmallSet (δ := δ) (δ' := δ)
  have hinner := innerAct_joint (I := I) (M := M) g T W hδ hδZ
  have hmid := c0j_const (I := I) (M := M) g (S := S)
    (permCoeff (I := I) (M := M) g mid)
  have hconn := connIns_c0j (I := I) (M := M) g T hδ hδZ
  have hout := c0j_const (I := I) (M := M) g (S := S)
    (permCoeff (I := I) (M := M) g out)
  have h₁ := c0j_app (I := I) (M := M) g hmid hinner
  have h₂ := c0j_app (I := I) (M := M) g hconn h₁
  have h₃ := c0j_app (I := I) (M := M) g hout h₂
  simpa only [aaMidOne] using h₃

theorem aaBare_joint
    (g : SmoothRiemannianMetric I M) (T W : SmoothCcTensor g 0 2)
    {δ : ℝ}
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ)
    (out : Equiv.Perm (Fin 4)) :
    C0Joint (I := I) g 3 4
      (realizedSmallSet (δ := δ) (δ' := δ))
      (fun t => aaBareOne (I := I) (M := M) g
        (realizedFam (I := I) g T 0 hδ hδZ t) W out) := by
  let S := realizedSmallSet (δ := δ) (δ' := δ)
  have hinner := innerAct_joint (I := I) (M := M) g T W hδ hδZ
  have hconn := connIns_c0j (I := I) (M := M) g T hδ hδZ
  have hout := c0j_const (I := I) (M := M) g (S := S)
    (permCoeff (I := I) (M := M) g out)
  have h₁ := c0j_app (I := I) (M := M) g hconn hinner
  have h₂ := c0j_app (I := I) (M := M) g hout h₁
  simpa only [aaBareOne] using h₂

theorem aaOne_joint
    (g : SmoothRiemannianMetric I M) (T W : SmoothCcTensor g 0 2)
    {δ : ℝ}
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ) :
    C0Joint (I := I) g 3 2
      (realizedSmallSet (δ := δ) (δ' := δ))
      (fun t => aaOne (I := I) (M := M) g
        (realizedFam (I := I) g T 0 hδ hδZ t) W) := by
  let S := realizedSmallSet (δ := δ) (δ' := δ)
  have h₀ := aaMid_joint (I := I) (M := M) g T W hδ hδZ
    ricPerm102 ricPerm3201
  have h₁ := aaMid_joint (I := I) (M := M) g T W hδ hδZ
    ricPerm102 ricPerm2301
  have h₂ := aaMid_joint (I := I) (M := M) g T W hδ hδZ
    ricPerm120 ricPerm3102
  have h₃ := aaBare_joint (I := I) (M := M) g T W hδ hδZ ricPerm1302
  have h₄ := aaBare_joint (I := I) (M := M) g T W hδ hδZ ricPerm1203
  have h₅ := aaMid_joint (I := I) (M := M) g T W hδ hδZ
    ricPerm120 ricPerm2103
  have hker := c0j_add (I := I) (M := M) g
    (c0j_add (I := I) (M := M) g
      (c0j_add (I := I) (M := M) g
        (c0j_add (I := I) (M := M) g
          (c0j_add (I := I) (M := M) g h₀ h₁) h₂) h₃) h₄) h₅
  have htrace := fourCast_c0j (I := I) (M := M) g T hδ hδZ
  have hout := c0j_app (I := I) (M := M) g htrace hker
  simpa only [aaOne, aaKerOne] using hout

theorem traceRF_c0j
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    {δ : ℝ}
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ)
    (p : ℕ) (σ : Equiv.Perm (Fin (p + 2))) :
    C0Joint (I := I) g (p + 2) p
      (realizedSmallSet (δ := δ) (δ' := δ))
      (fun t => lc0TraceRF (I := I) (M := M) g
        (realizedFam (I := I) g T 0 hδ hδZ t) p σ) := by
  apply contMDiffOn_clm_section_of_pointwise_jointMR (I := I) (M := M)
    (F₁ := Tensor0SModel (p + 2) ℝ E)
    (V₁ := fun x : M => Tensor0SSpace (p + 2) I x)
    (F₂ := Tensor0SModel p ℝ E) (V₂ := fun x : M => Tensor0SSpace p I x)
    (φ := fun q : M × ℝ =>
      (lc0TraceRF (I := I) (M := M) g
        (realizedFam (I := I) g T 0 hδ hδZ q.2) p σ).toSection q.1)
    (S := realizedSmallSet (δ := δ) (δ' := δ))
  intro Y
  have hY : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, Tensor0SModel (p + 2) ℝ E)) ∞
      (fun q : M × ℝ => TotalSpace.mk' (Tensor0SModel (p + 2) ℝ E)
        (E := fun x : M => Tensor0SSpace (p + 2) I x) q.1 (Y q.1))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ)) :=
    Y.contMDiff.comp_contMDiffOn contMDiffOn_fst
  have hperm := domDomCongrField_jointContMDiffOn (I := I) σ
    (S := realizedSmallSet (δ := δ) (δ' := δ))
    (fun q : M × ℝ => Y q.1) hY
  have htr := cometricDoubleTraceFib_realizedFam_jointContMDiffOn
    (I := I) (p := p) g T 0 hδ hδZ _ hperm
  refine htr.congr (fun q _ => ?_)
  refine congrArg (fun z => TotalSpace.mk' (Tensor0SModel p ℝ E)
    (E := fun x : M => Tensor0SSpace p I x) q.1 z) ?_
  rw [show
      ((lc0TraceRF (I := I) (M := M) g
        (realizedFam (I := I) g T 0 hδ hδZ q.2) p σ).toSection q.1)
          (Y q.1) =
        LieCorr0Core.lieCorr0TraceStep (I := I)
          (realizedFam (I := I) g T 0 hδ hδZ q.2) p σ q.1 (Y q.1) from
      congrArg (fun L => L (Y q.1))
        (lc0TraceRF_fiber (I := I) (M := M) g
          (realizedFam (I := I) g T 0 hδ hδZ q.2) p σ q.1),
    LieCorr0Core.lieCorr0TraceStep,
    ContinuousLinearMap.comp_apply, domDomCongrFibRank_apply]

theorem pureTrace_c0j
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    {δ : ℝ}
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ)
    (p : ℕ) :
    C0Joint (I := I) g (p + 2) p
      (realizedSmallSet (δ := δ) (δ' := δ))
      (fun t => pureTrace (I := I) (M := M) g
        (realizedFam (I := I) g T 0 hδ hδZ t) p) := by
  apply contMDiffOn_clm_section_of_pointwise_jointMR (I := I) (M := M)
    (F₁ := Tensor0SModel (p + 2) ℝ E)
    (V₁ := fun x : M => Tensor0SSpace (p + 2) I x)
    (F₂ := Tensor0SModel p ℝ E) (V₂ := fun x : M => Tensor0SSpace p I x)
    (φ := fun q : M × ℝ =>
      (pureTrace (I := I) (M := M) g
        (realizedFam (I := I) g T 0 hδ hδZ q.2) p).toSection q.1)
    (S := realizedSmallSet (δ := δ) (δ' := δ))
  intro Y
  have hY : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, Tensor0SModel (p + 2) ℝ E)) ∞
      (fun q : M × ℝ => TotalSpace.mk' (Tensor0SModel (p + 2) ℝ E)
        (E := fun x : M => Tensor0SSpace (p + 2) I x) q.1 (Y q.1))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ)) :=
    Y.contMDiff.comp_contMDiffOn contMDiffOn_fst
  have htr := cometricDoubleTraceFib_realizedFam_jointContMDiffOn
    (I := I) (p := p) g T 0 hδ hδZ (fun q : M × ℝ => Y q.1) hY
  refine htr.congr (fun q _ => ?_)
  refine congrArg (fun z => TotalSpace.mk' (Tensor0SModel p ℝ E)
    (E := fun x : M => Tensor0SSpace p I x) q.1 z) ?_
  rw [pureTrace_toSection]

theorem pairTrace_joint
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    {δ : ℝ}
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ) :
    C0Joint (I := I) g 6 2
      (realizedSmallSet (δ := δ) (δ' := δ))
      (fun t => lieCovPair (I := I) (M := M) g
        (realizedFam (I := I) g T 0 hδ hδZ t)) := by
  have h₂ := pureTrace_c0j (I := I) (M := M) g T hδ hδZ 2
  have h₄ := pureTrace_c0j (I := I) (M := M) g T hδ hδZ 4
  have hout := c0j_app (I := I) (M := M) g h₂ h₄
  simpa only [LowBaseInternal.pairTrace_eq] using hout

theorem riemLive_c0j
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    {δ : ℝ}
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ) :
    C0Joint (I := I) g 4 2
      (realizedSmallSet (δ := δ) (δ' := δ))
      (fun t => lc0RiemLive (I := I) (M := M) g
        (realizedFam (I := I) g T 0 hδ hδZ t)) := by
  apply contMDiffOn_clm_section_of_pointwise_jointMR (I := I) (M := M)
    (F₁ := Tensor0SModel 4 ℝ E) (V₁ := fun x : M => Tensor0SSpace 4 I x)
    (F₂ := Tensor0SModel 2 ℝ E) (V₂ := fun x : M => Tensor0SSpace 2 I x)
    (φ := fun q : M × ℝ =>
      (lc0RiemLive (I := I) (M := M) g
        (realizedFam (I := I) g T 0 hδ hδZ q.2)).toSection q.1)
    (S := realizedSmallSet (δ := δ) (δ' := δ))
  intro Y
  have hY : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, Tensor0SModel 4 ℝ E)) ∞
      (fun q : M × ℝ => TotalSpace.mk' (Tensor0SModel 4 ℝ E)
        (E := fun x : M => Tensor0SSpace 4 I x) q.1 (Y q.1))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ)) :=
    Y.contMDiff.comp_contMDiffOn contMDiffOn_fst
  have htr := cometricDoubleTraceFib_realizedFam_jointContMDiffOn
    (I := I) (p := 2) g T 0 hδ hδZ
    (fun q : M × ℝ => Y q.1) hY
  refine htr.congr (fun q _ => ?_)
  refine congrArg (fun z => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
    (E := fun x : M => Tensor0SSpace 2 I x) q.1 z) ?_
  exact congrArg (fun L => L (Y q.1))
    (lc0RiemLive_fiber (I := I) (M := M) g
      (realizedFam (I := I) g T 0 hδ hδZ q.2) q.1)

theorem vbMcd_c0j
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    {δ : ℝ}
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ) :
    C0Joint (I := I) g 1 4
      (realizedSmallSet (δ := δ) (δ' := δ))
      (fun t => vbMcdArm (I := I) (M := M) g
        (realizedFam (I := I) g T 0 hδ hδZ t)) := by
  apply contMDiffOn_clm_section_of_pointwise_jointMR (I := I) (M := M)
    (F₁ := Tensor0SModel 1 ℝ E) (V₁ := fun x : M => Tensor0SSpace 1 I x)
    (F₂ := Tensor0SModel 4 ℝ E) (V₂ := fun x : M => Tensor0SSpace 4 I x)
    (φ := fun q : M × ℝ =>
      (vbMcdArm (I := I) (M := M) g
        (realizedFam (I := I) g T 0 hδ hδZ q.2)).toSection q.1)
    (S := realizedSmallSet (δ := δ) (δ' := δ))
  intro Y
  have hY : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, Tensor0SModel 1 ℝ E)) ∞
      (fun q : M × ℝ => TotalSpace.mk' (Tensor0SModel 1 ℝ E)
        (E := fun x : M => Tensor0SSpace 1 I x) q.1 (Y q.1))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ)) :=
    Y.contMDiff.comp_contMDiffOn contMDiffOn_fst
  have hM := metricConnDiffLowered_selfFam_jointContMDiffOn
    (I := I) g T 0 hδ hδZ
  have hprod := jointTensor0SProd_local (I := I) (p := 1) (q := 3)
    (S := realizedSmallSet (δ := δ) (δ' := δ))
    (fun q : M × ℝ => Y q.1)
    (fun q : M × ℝ => metricConnDiffLoweredFib (I := I)
      (realizedFam (I := I) g T 0 hδ hδZ q.2)
      (realizedFam (I := I) g T 0 hδ hδZ q.2) g q.1)
    hY hM
  have hprod' : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, Tensor0SModel 4 ℝ E)) ∞
      (fun q : M × ℝ => TotalSpace.mk' (Tensor0SModel 4 ℝ E)
        (E := fun x : M => Tensor0SSpace 4 I x) q.1
        (tensor0SProdKappaFib (I := I) q.1
          (metricConnDiffLoweredFib (I := I)
            (realizedFam (I := I) g T 0 hδ hδZ q.2)
            (realizedFam (I := I) g T 0 hδ hδZ q.2) g q.1)
          (Y q.1)))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ)) := by
    refine hprod.congr (fun q _ => ?_)
    refine congrArg (fun z => TotalSpace.mk' (Tensor0SModel 4 ℝ E)
      (E := fun x : M => Tensor0SSpace 4 I x) q.1 z) ?_
    rw [tensor0SProdKappaFib_apply]
  have hperm := domDomCongrField_jointContMDiffOn (I := I)
    LieCorr0Core.lieCorr0VBPerm
    (S := realizedSmallSet (δ := δ) (δ' := δ)) _ hprod'
  refine hperm.congr (fun q _ => ?_)
  refine congrArg (fun z => TotalSpace.mk' (Tensor0SModel 4 ℝ E)
    (E := fun x : M => Tensor0SSpace 4 I x) q.1 z) ?_
  rw [show
      ((vbMcdArm (I := I) (M := M) g
        (realizedFam (I := I) g T 0 hδ hδZ q.2)).toSection q.1) (Y q.1) =
        domDomCongrFibRank (I := I) 4 LieCorr0Core.lieCorr0VBPerm q.1
          (tensor0SProdKappaFib (I := I) (p := 1) (q := 3) q.1
            (metricConnDiffLoweredFib (I := I)
              (realizedFam (I := I) g T 0 hδ hδZ q.2)
              (realizedFam (I := I) g T 0 hδ hδZ q.2) g q.1)
            (Y q.1)) from rfl,
    domDomCongrFibRank_apply]

theorem vbOne_joint
    (g : SmoothRiemannianMetric I M) (T W : SmoothCcTensor g 0 2)
    {δ : ℝ}
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ) :
    C0Joint (I := I) g 3 2
      (realizedSmallSet (δ := δ) (δ' := δ))
      (fun t => vbOne (I := I) (M := M) g
        (realizedFam (I := I) g T 0 hδ hδZ t) W) := by
  have hconn : C0Joint (I := I) g 3 3
      (realizedSmallSet (δ := δ) (δ' := δ))
      (fun t => LowBaseInternal.connLowOp (I := I) (M := M) g
        (realizedFam (I := I) g T 0 hδ hδZ t)) :=
    LowBaseInternal.connLow_joint (I := I) (M := M) g T hδ hδZ
  have htr : C0Joint (I := I) g 3 1
      (realizedSmallSet (δ := δ) (δ' := δ))
      (fun t => lc0TraceRF (I := I) (M := M) g
        (realizedFam (I := I) g T 0 hδ hδZ t) 1
        (Equiv.refl (Fin 3))) := by
    simpa only using traceRF_c0j (I := I) (M := M) g T hδ hδZ
      1 (Equiv.refl (Fin 3))
  have hraise := c0j_const (I := I) (M := M) g
    (S := realizedSmallSet (δ := δ) (δ' := δ))
    (cometricRaiseSlot0Field (I := I) (M := M) g 0 W)
  have hmcd := vbMcd_c0j (I := I) (M := M) g T hδ hδZ
  have hriem := riemLive_c0j (I := I) (M := M) g T hδ hδZ
  have h₁ := c0j_app (I := I) (M := M) g htr hconn
  have h₂ := c0j_app (I := I) (M := M) g hraise h₁
  have h₃ := c0j_app (I := I) (M := M) g hmcd h₂
  have h₄ := c0j_app (I := I) (M := M) g hriem h₃
  have hcore : C0Joint (I := I) g 3 2
      (realizedSmallSet (δ := δ) (δ' := δ))
      (fun t => vbCore (I := I) (M := M) g
        (realizedFam (I := I) g T 0 hδ hδZ t) W) := by
    simpa only [vbCore] using h₄
  have hcore' : linearizedRicciThreeArmHjoint (I := I) (M := M) g 3
      (fun t => vbCore (I := I) (M := M) g
        (realizedFam (I := I) g T 0 hδ hδZ t) W)
      (δ := δ) (δ' := δ) := hcore
  have hs := threeArmJoint_smul (I := I) (M := M) (r := 3) g (2 : ℝ)
    (fun t => vbCore (I := I) (M := M) g
      (realizedFam (I := I) g T 0 hδ hδZ t) W) hcore'
  simpa only [linearizedRicciThreeArmHjoint, vbOne] using hs

theorem metricLower_val
    (g gm gB : SmoothRiemannianMetric I M) (x : M) :
    ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
      (metricConnDiffLoweredCc (I := I) (M := M) g gm gB).toSection x)
        (unitTensor (I := I) (M := M) x)) =
      metricConnDiffLoweredFib (I := I) gm gm gB x := by
  rw [show
      ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
        (metricConnDiffLoweredCc (I := I) (M := M) g gm gB).toSection x)
          (unitTensor (I := I) (M := M) x)) =
        (MixedSection.eval₀ (F := E) (E := (TangentSpace I : M → Type _)) x).smulRight
          (metricConnDiffLoweredFib (I := I) gm gm gB x)
          (ContinuousMultilinearMap.constOfIsEmpty ℝ
            (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ)) from rfl]
  rw [ContinuousLinearMap.smulRight_apply, MixedSection.eval₀_apply,
    ContinuousMultilinearMap.constOfIsEmpty_apply, one_smul]

theorem slotMcd_c0j
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    {δ : ℝ}
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ) :
    C0Joint (I := I) g 3 6
      (realizedSmallSet (δ := δ) (δ' := δ))
      (fun t => slotExtendIter (I := I) (M := M) g 0 3 3
        (metricConnDiffLoweredCc (I := I) (M := M) g
          (realizedFam (I := I) g T 0 hδ hδZ t) g)) := by
  apply contMDiffOn_clm_section_of_pointwise_jointMR (I := I) (M := M)
    (F₁ := Tensor0SModel 3 ℝ E) (V₁ := fun x : M => Tensor0SSpace 3 I x)
    (F₂ := Tensor0SModel 6 ℝ E) (V₂ := fun x : M => Tensor0SSpace 6 I x)
    (φ := fun q : M × ℝ =>
      (slotExtendIter (I := I) (M := M) g 0 3 3
        (metricConnDiffLoweredCc (I := I) (M := M) g
          (realizedFam (I := I) g T 0 hδ hδZ q.2) g)).toSection q.1)
    (S := realizedSmallSet (δ := δ) (δ' := δ))
  intro Y
  have hY : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, Tensor0SModel 3 ℝ E)) ∞
      (fun q : M × ℝ => TotalSpace.mk' (Tensor0SModel 3 ℝ E)
        (E := fun x : M => Tensor0SSpace 3 I x) q.1 (Y q.1))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ)) :=
    Y.contMDiff.comp_contMDiffOn contMDiffOn_fst
  have hM := metricConnDiffLowered_selfFam_jointContMDiffOn
    (I := I) g T 0 hδ hδZ
  have hK : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, Tensor0SModel 3 ℝ E)) ∞
      (fun q : M × ℝ => TotalSpace.mk' (Tensor0SModel 3 ℝ E)
        (E := fun x : M => Tensor0SSpace 3 I x) q.1
        ((show Tensor0SSpace 0 I q.1 →L[ℝ] Tensor0SSpace 3 I q.1 from
          (metricConnDiffLoweredCc (I := I) (M := M) g
            (realizedFam (I := I) g T 0 hδ hδZ q.2) g).toSection q.1)
          (unitTensor (I := I) (M := M) q.1)))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ)) := by
    refine hM.congr (fun q _ => ?_)
    exact congrArg (fun z => TotalSpace.mk' (Tensor0SModel 3 ℝ E)
      (E := fun x : M => Tensor0SSpace 3 I x) q.1 z)
      (metricLower_val (I := I) (M := M) g
        (realizedFam (I := I) g T 0 hδ hδZ q.2) g q.1)
  have hprod := jointTensor0SProd_local (I := I) (p := 3) (q := 3)
    (S := realizedSmallSet (δ := δ) (δ' := δ))
    (fun q : M × ℝ => Y q.1)
    (fun q : M × ℝ =>
      (show Tensor0SSpace 0 I q.1 →L[ℝ] Tensor0SSpace 3 I q.1 from
        (metricConnDiffLoweredCc (I := I) (M := M) g
          (realizedFam (I := I) g T 0 hδ hδZ q.2) g).toSection q.1)
        (unitTensor (I := I) (M := M) q.1))
    hY hK
  have hprod' : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, Tensor0SModel 6 ℝ E)) ∞
      (fun q : M × ℝ => TotalSpace.mk' (Tensor0SModel 6 ℝ E)
        (E := fun x : M => Tensor0SSpace 6 I x) q.1
        (tensor0SProdKappaFib (I := I) (p := 3) (q := 3) q.1
          ((show Tensor0SSpace 0 I q.1 →L[ℝ] Tensor0SSpace 3 I q.1 from
            (metricConnDiffLoweredCc (I := I) (M := M) g
              (realizedFam (I := I) g T 0 hδ hδZ q.2) g).toSection q.1)
            (unitTensor (I := I) (M := M) q.1))
          (Y q.1)))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ)) := by
    refine hprod.congr (fun q _ => ?_)
    refine congrArg (fun z => TotalSpace.mk' (Tensor0SModel 6 ℝ E)
      (E := fun x : M => Tensor0SSpace 6 I x) q.1 z) ?_
    rw [tensor0SProdKappaFib_apply]
  refine hprod'.congr (fun q _ => ?_)
  refine congrArg (fun z => TotalSpace.mk' (Tensor0SModel 6 ℝ E)
    (E := fun x : M => Tensor0SSpace 6 I x) q.1 z) ?_
  exact slotLift33 (I := I) (M := M) g
    (metricConnDiffLoweredCc (I := I) (M := M) g
      (realizedFam (I := I) g T 0 hδ hδZ q.2) g) q.1 (Y q.1)

theorem amixHalf_joint
    (g : SmoothRiemannianMetric I M) (T W : SmoothCcTensor g 0 2)
    {δ : ℝ}
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ)
    (σlast : Equiv.Perm (Fin 4)) :
    C0Joint (I := I) g 3 2
      (realizedSmallSet (δ := δ) (δ' := δ))
      (fun t => amixHalfOne (I := I) (M := M) g
        (realizedFam (I := I) g T 0 hδ hδZ t) g W σlast) := by
  let S := realizedSmallSet (δ := δ) (δ' := δ)
  have hQ : C0Joint (I := I) g 5 3 S
      (fun t => lc0TraceRF (I := I) (M := M) g
        (realizedFam (I := I) g T 0 hδ hδZ t) 3
        LieCorr0Core.lieCorr0AMixPermQ) := by
    simpa only [S] using traceRF_c0j (I := I) (M := M) g T hδ hδZ
      3 LieCorr0Core.lieCorr0AMixPermQ
  have h₄ : C0Joint (I := I) g 6 4 S
      (fun t => lc0TraceRF (I := I) (M := M) g
        (realizedFam (I := I) g T 0 hδ hδZ t) 4
        LieCorr0Core.lieCorr0AMixPerm1) := by
    simpa only [S] using traceRF_c0j (I := I) (M := M) g T hδ hδZ
      4 LieCorr0Core.lieCorr0AMixPerm1
  have h₂ : C0Joint (I := I) g 4 2 S
      (fun t => lc0TraceRF (I := I) (M := M) g
        (realizedFam (I := I) g T 0 hδ hδZ t) 2 σlast) := by
    simpa only [S] using traceRF_c0j (I := I) (M := M) g T hδ hδZ 2 σlast
  have hslot : C0Joint (I := I) g 3 6 S
      (fun t => slotExtendIter (I := I) (M := M) g 0 3 3
        (metricConnDiffLoweredCc (I := I) (M := M) g
          (realizedFam (I := I) g T 0 hδ hδZ t) g)) := by
    simpa only [S] using slotMcd_c0j (I := I) (M := M) g T hδ hδZ
  have hbase := c0j_const (I := I) (M := M) g (S := S)
    (appCcRS (I := I) (M := M) g 3 3 5
      (prod23 (I := I) (M := M) g W)
      (mcdOne (I := I) (M := M) g))
  have h₁ := c0j_app (I := I) (M := M) g hQ hbase
  have h₂' := c0j_app (I := I) (M := M) g hslot h₁
  have h₃ := c0j_app (I := I) (M := M) g h₄ h₂'
  have hout := c0j_app (I := I) (M := M) g h₂ h₃
  simpa only [amixHalfOne] using hout

theorem amixOne_joint
    (g : SmoothRiemannianMetric I M) (T W : SmoothCcTensor g 0 2)
    {δ : ℝ}
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ) :
    C0Joint (I := I) g 3 2
      (realizedSmallSet (δ := δ) (δ' := δ))
      (fun t => amixOne (I := I) (M := M) g
        (realizedFam (I := I) g T 0 hδ hδZ t) g W) := by
  have hA := amixHalf_joint (I := I) (M := M) g T W hδ hδZ
    LieCorr0Core.lieCorr0AMixPerm2
  have hB := amixHalf_joint (I := I) (M := M) g T W hδ hδZ
    (lc0SwapPermRF * LieCorr0Core.lieCorr0AMixPerm2)
  have hadd := c0j_add (I := I) (M := M) g hA hB
  have hadd' : linearizedRicciThreeArmHjoint (I := I) (M := M) g 3
      (fun t =>
        amixHalfOne (I := I) (M := M) g
            (realizedFam (I := I) g T 0 hδ hδZ t) g W
            LieCorr0Core.lieCorr0AMixPerm2 +
          amixHalfOne (I := I) (M := M) g
            (realizedFam (I := I) g T 0 hδ hδZ t) g W
            (lc0SwapPermRF * LieCorr0Core.lieCorr0AMixPerm2))
      (δ := δ) (δ' := δ) := hadd
  have hs := threeArmJoint_smul (I := I) (M := M) (r := 3) g (2 : ℝ) _ hadd'
  simpa only [linearizedRicciThreeArmHjoint, amixOne] using hs

theorem ricciOne_joint
    (g : SmoothRiemannianMetric I M) (T W : SmoothCcTensor g 0 2)
    {δ : ℝ}
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ) :
    C0Joint (I := I) g 3 2
      (realizedSmallSet (δ := δ) (δ' := δ))
      (fun t => ricciOne (I := I) (M := M) g
        (realizedFam (I := I) g T 0 hδ hδZ t) W) := by
  have hA := aaOne_joint (I := I) (M := M) g T W hδ hδZ
  have hD : C0Joint (I := I) g 3 2
      (realizedSmallSet (δ := δ) (δ' := δ))
      (fun t => LowBaseInternal.ricciDAOne (I := I) (M := M) g
        (realizedFam (I := I) g T 0 hδ hδZ t)
        (symmS (I := I) (M := M) g W)) :=
    LowBaseInternal.ricciDAOne_joint (I := I) (M := M) g T
      (symmS (I := I) (M := M) g W) hδ hδZ
  simpa only [ricciOne] using c0j_add (I := I) (M := M) g hA hD

theorem arm2_eq_ins
    (g gm : SmoothRiemannianMetric I M) :
    lieCovArm2 (I := I) (M := M) g gm =
      appCcRS (I := I) (M := M) g 3 4 4
        (permCoeff (I := I) (M := M) g ricPerm2301)
        (connDiffContrInsertionField (I := I) g gm) := by
  rw [perm_rs (I := I) (M := M) g ricPerm2301]
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [lieCovArm2, armSlotEndoCc_toSection,
    rsDomDomCongrSection_toSection]
  apply ContinuousLinearMap.ext
  intro D
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro v
  change Tensor0SSpace.toModel
      (armSlotFib (I := I) (M := M) 2 x
        (bdConnPair (I := I) (M := M) g gm x) D) v =
    Tensor0SSpace.toModel
      ((rsDomDomCongr ricPerm2301
        ((connDiffContrInsertionField (I := I) g gm).toSection x)) D) v
  rw [armSlotFib_apply_eval, slotInsertEndoFib_apply_eval]
  rw [toModel_rsDomDomCongr_apply,
    ContinuousMultilinearMap.domDomCongr_apply]
  rw [connDiffContrInsertionField_toSection, connContr21_insert]
  rw [bdConnPair_apply]
  congr 1
  funext k
  fin_cases k <;> simp [ricPerm2301] <;> rfl

theorem lieArm_joint
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    {δ : ℝ}
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ) :
    C0Joint (I := I) g 3 4
      (realizedSmallSet (δ := δ) (δ' := δ))
      (fun t => lieCovArm2 (I := I) (M := M) g
        (realizedFam (I := I) g T 0 hδ hδZ t)) := by
  let S := realizedSmallSet (δ := δ) (δ' := δ)
  have hp := c0j_const (I := I) (M := M) g (S := S)
    (permCoeff (I := I) (M := M) g ricPerm2301)
  have hi := connIns_c0j (I := I) (M := M) g T hδ hδZ
  have hout := c0j_app (I := I) (M := M) g hp hi
  simpa only [S, arm2_eq_ins] using hout

theorem revSlot_path
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    {δ : ℝ}
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ)
    {t : ℝ} (ht : t ∈ realizedSmallSet (δ := δ) (δ' := δ)) :
    slotInsertEndoCc (I := I) (M := M) g 2
        (fullRaisedEndoField (I := I) (M := M)
          (realizedFam (I := I) g T 0 hδ hδZ t) g) =
      slotInsertEndoCc (I := I) (M := M) g 2
          (fullRaisedEndoField (I := I) (M := M) g g) +
        t • slotInsertEndoCc (I := I) (M := M) g 2
          (symmRaiseEndo (I := I) (M := M) g T) := by
  have htie : ∀ (x : M) (u v : TangentSpace I x),
      (realizedFam (I := I) g T 0 hδ hδZ t).inner x u v =
        g.inner x u v +
          ccTensorBilinSymm (I := I) g (t • T) x u v := by
    intro x u v
    rw [realizedFam_inner_of_mem (I := I) g T 0 hδ hδZ ht]
    simp only [convexPerturbation, smul_zero, zero_add]
  have hzero : ∀ (x : M) (u v : TangentSpace I x),
      g.inner x u v = g.inner x u v +
        ccTensorBilinSymm (I := I) g
          (0 : SmoothCcTensor g 0 2) x u v := by
    intro x u v
    rw [ccTensorBilinSymm_apply, ccTensorBilin_zero_weight,
      ccTensorBilin_zero_weight]
    ring
  have hrev := LowBaseInternal.fullRev_sub (I := I) (M := M)
    g (realizedFam (I := I) g T 0 hδ hδZ t) g
      (t • T) (0 : SmoothCcTensor g 0 2) htie hzero
  rw [sub_zero, symmRaiseEndo_smul] at hrev
  have hfull :
      fullRaisedEndoField (I := I) (M := M)
          (realizedFam (I := I) g T 0 hδ hδZ t) g =
        fullRaisedEndoField (I := I) (M := M) g g +
          t • symmRaiseEndo (I := I) (M := M) g T := by
    calc
      _ = t • symmRaiseEndo (I := I) (M := M) g T +
          fullRaisedEndoField (I := I) (M := M) g g :=
        (sub_eq_iff_eq_add.mp hrev)
      _ = _ := add_comm _ _
  rw [hfull, slotInsertEndoCc_add, slotInsertEndoCc_smul]

theorem revSlot_joint
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    {δ : ℝ}
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ) :
    C0Joint (I := I) g 3 3
      (realizedSmallSet (δ := δ) (δ' := δ))
      (fun t => slotInsertEndoCc (I := I) (M := M) g 2
        (fullRaisedEndoField (I := I) (M := M)
          (realizedFam (I := I) g T 0 hδ hδZ t) g)) := by
  let S := realizedSmallSet (δ := δ) (δ' := δ)
  let A₀ := slotInsertEndoCc (I := I) (M := M) g 2
    (fullRaisedEndoField (I := I) (M := M) g g)
  let A₁ := slotInsertEndoCc (I := I) (M := M) g 2
    (symmRaiseEndo (I := I) (M := M) g T)
  have h₀ := c0j_const (I := I) (M := M) g (S := S) A₀
  have h₁ := c0j_param (I := I) (M := M) g
    (c0j_const (I := I) (M := M) g (S := S) A₁)
  have hout := c0j_add (I := I) (M := M) g h₀ h₁
  refine hout.congr (fun p hp => ?_)
  refine congrArg (fun z => TotalSpace.mk' (TensorRSModel 3 3 ℝ E)
    (E := fun x : M => TensorRSSpace 3 3 I x) p.1 z) ?_
  change (slotInsertEndoCc (I := I) (M := M) g 2
      (fullRaisedEndoField (I := I) (M := M)
        (realizedFam (I := I) g T 0 hδ hδZ p.2) g)).toSection p.1 =
    (A₀ + p.2 • A₁).toSection p.1
  rw [revSlot_path (I := I) (M := M) g T hδ hδZ hp.2]

noncomputable def omegaOne
    (g gm : SmoothRiemannianMetric I M) : SmoothCcTensor g 3 3 :=
  appCcRS (I := I) (M := M) g 3 3 3
    (slotInsertEndoCc (I := I) (M := M) g 2
      (fullRaisedEndoField (I := I) (M := M) gm g))
    (appCcRS (I := I) (M := M) g 3 3 3
      (permCoeff (I := I) (M := M) g (finRotate 3))
      (LowBaseInternal.connLowOp (I := I) (M := M) g gm))

theorem omegaOne_joint
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    {δ : ℝ}
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ) :
    C0Joint (I := I) g 3 3
      (realizedSmallSet (δ := δ) (δ' := δ))
      (fun t => omegaOne (I := I) (M := M) g
        (realizedFam (I := I) g T 0 hδ hδZ t)) := by
  let S := realizedSmallSet (δ := δ) (δ' := δ)
  have hins := revSlot_joint (I := I) (M := M) g T hδ hδZ
  have hperm := c0j_const (I := I) (M := M) g (S := S)
    (permCoeff (I := I) (M := M) g (finRotate 3))
  have hconn : C0Joint (I := I) g 3 3 S
      (fun t => LowBaseInternal.connLowOp (I := I) (M := M) g
        (realizedFam (I := I) g T 0 hδ hδZ t)) := by
    simpa only [S] using LowBaseInternal.connLow_joint
      (I := I) (M := M) g T hδ hδZ
  have hinner := c0j_app (I := I) (M := M) g hperm hconn
  have hout := c0j_app (I := I) (M := M) g hins hinner
  simpa only [S, omegaOne] using hout

theorem omega_one
    (g gm : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    (hT : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g T x u v =
        ccTensorBilin (I := I) g T x v u)
    (htie : ∀ (x : M) (u v : TangentSpace I x),
      gm.inner x u v =
        g.inner x u v + ccTensorBilinSymm (I := I) g T x u v) :
    appCc (I := I) (M := M) g 3 3
        (omegaOne (I := I) (M := M) g gm)
        (covGrad (I := I) (M := M) g 0 2 T) =
      lrOmegaHat (I := I) (M := M) g gm := by
  rw [omegaOne, ← appCc_assoc, ← appCc_assoc]
  have hconn : appCc (I := I) (M := M) g 3 3
      (LowBaseInternal.connLowOp (I := I) (M := M) g gm)
      (covGrad (I := I) (M := M) g 0 2 T) =
      connDiffLoweredCc (I := I) g gm := by
    simpa only [appCcRS_zero_eq_appCc] using
      LowBaseInternal.connLow_app (I := I) (M := M) g gm T hT htie
  rw [hconn]
  have hperm : appCc (I := I) (M := M) g 3 3
      (permCoeff (I := I) (M := M) g (finRotate 3))
      (connDiffLoweredCc (I := I) g gm) =
      domDomCongrSection (I := I) g (finRotate 3)
        (connDiffLoweredCc (I := I) g gm) := by
    simpa only [appCcRS_zero_eq_appCc] using
      perm_app (I := I) (M := M) g (finRotate 3)
        (connDiffLoweredCc (I := I) g gm)
  rw [hperm]
  rfl

noncomputable def qbOne
    (g gm : SmoothRiemannianMetric I M) : SmoothCcTensor g 3 4 :=
  appCcRS (I := I) (M := M) g 3 3 4
    (lieCovArm2 (I := I) (M := M) g gm)
    (omegaOne (I := I) (M := M) g gm)

noncomputable def qaOne
    (g gm : SmoothRiemannianMetric I M) : SmoothCcTensor g 3 4 :=
  appCcRS (I := I) (M := M) g 3 3 4
    (lieCovArm2 (I := I) (M := M) g gm)
    (appCcRS (I := I) (M := M) g 3 3 3
      (permCoeff (I := I) (M := M) g (Equiv.swap (0 : Fin 3) 1))
      (omegaOne (I := I) (M := M) g gm))

noncomputable def quadOp
    (g gm : SmoothRiemannianMetric I M) : SmoothCcTensor g 3 4 :=
  appCcRS (I := I) (M := M) g 3 4 4
      (permCoeff (I := I) (M := M) g (Equiv.swap (0 : Fin 4) 1))
      (qbOne (I := I) (M := M) g gm) +
    qbOne (I := I) (M := M) g gm +
    appCcRS (I := I) (M := M) g 3 4 4
      (permCoeff (I := I) (M := M) g lrPermA)
      (qaOne (I := I) (M := M) g gm) +
    appCcRS (I := I) (M := M) g 3 4 4
      (permCoeff (I := I) (M := M) g (Equiv.swap (0 : Fin 4) 2))
      (qaOne (I := I) (M := M) g gm) +
    appCcRS (I := I) (M := M) g 3 4 4
      (permCoeff (I := I) (M := M) g lrPermB)
      (qaOne (I := I) (M := M) g gm) +
    appCcRS (I := I) (M := M) g 3 4 4
      (permCoeff (I := I) (M := M) g lrPermC)
      (qaOne (I := I) (M := M) g gm)

theorem qbOne_joint
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    {δ : ℝ}
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ) :
    C0Joint (I := I) g 3 4
      (realizedSmallSet (δ := δ) (δ' := δ))
      (fun t => qbOne (I := I) (M := M) g
        (realizedFam (I := I) g T 0 hδ hδZ t)) := by
  have harm := lieArm_joint (I := I) (M := M) g T hδ hδZ
  have homega := omegaOne_joint (I := I) (M := M) g T hδ hδZ
  simpa only [qbOne] using c0j_app (I := I) (M := M) g harm homega

theorem qaOne_joint
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    {δ : ℝ}
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ) :
    C0Joint (I := I) g 3 4
      (realizedSmallSet (δ := δ) (δ' := δ))
      (fun t => qaOne (I := I) (M := M) g
        (realizedFam (I := I) g T 0 hδ hδZ t)) := by
  let S := realizedSmallSet (δ := δ) (δ' := δ)
  have harm := lieArm_joint (I := I) (M := M) g T hδ hδZ
  have hperm := c0j_const (I := I) (M := M) g (S := S)
    (permCoeff (I := I) (M := M) g (Equiv.swap (0 : Fin 3) 1))
  have homega := omegaOne_joint (I := I) (M := M) g T hδ hδZ
  have hswap := c0j_app (I := I) (M := M) g hperm homega
  simpa only [S, qaOne] using c0j_app (I := I) (M := M) g harm hswap

theorem quadOp_joint
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    {δ : ℝ}
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ) :
    C0Joint (I := I) g 3 4
      (realizedSmallSet (δ := δ) (δ' := δ))
      (fun t => quadOp (I := I) (M := M) g
        (realizedFam (I := I) g T 0 hδ hδZ t)) := by
  let S := realizedSmallSet (δ := δ) (δ' := δ)
  have hqb := qbOne_joint (I := I) (M := M) g T hδ hδZ
  have hqa := qaOne_joint (I := I) (M := M) g T hδ hδZ
  have hswap := c0j_const (I := I) (M := M) g (S := S)
    (permCoeff (I := I) (M := M) g (Equiv.swap (0 : Fin 4) 1))
  have hA := c0j_const (I := I) (M := M) g (S := S)
    (permCoeff (I := I) (M := M) g lrPermA)
  have hswap2 := c0j_const (I := I) (M := M) g (S := S)
    (permCoeff (I := I) (M := M) g (Equiv.swap (0 : Fin 4) 2))
  have hB := c0j_const (I := I) (M := M) g (S := S)
    (permCoeff (I := I) (M := M) g lrPermB)
  have hC := c0j_const (I := I) (M := M) g (S := S)
    (permCoeff (I := I) (M := M) g lrPermC)
  have h₀ := c0j_app (I := I) (M := M) g hswap hqb
  have h₂ := c0j_app (I := I) (M := M) g hA hqa
  have h₃ := c0j_app (I := I) (M := M) g hswap2 hqa
  have h₄ := c0j_app (I := I) (M := M) g hB hqa
  have h₅ := c0j_app (I := I) (M := M) g hC hqa
  have hout := c0j_add (I := I) (M := M) g
    (c0j_add (I := I) (M := M) g
      (c0j_add (I := I) (M := M) g
        (c0j_add (I := I) (M := M) g
          (c0j_add (I := I) (M := M) g h₀ hqb) h₂) h₃) h₄) h₅
  simpa only [S, quadOp] using hout

theorem quad_op
    (g gm : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    (hT : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g T x u v =
        ccTensorBilin (I := I) g T x v u)
    (htie : ∀ (x : M) (u v : TangentSpace I x),
      gm.inner x u v =
        g.inner x u v + ccTensorBilinSymm (I := I) g T x u v) :
    appCc (I := I) (M := M) g 3 4
        (quadOp (I := I) (M := M) g gm)
        (covGrad (I := I) (M := M) g 0 2 T) =
      lrQuadF (I := I) (M := M) g gm := by
  simp only [quadOp, appCc_add_left]
  have hqb : appCc (I := I) (M := M) g 3 4
      (qbOne (I := I) (M := M) g gm)
      (covGrad (I := I) (M := M) g 0 2 T) =
      lrQB (I := I) (M := M) g gm := by
    rw [qbOne, ← appCc_assoc,
      omega_one (I := I) (M := M) g gm T hT htie]
    rfl
  have hqa : appCc (I := I) (M := M) g 3 4
      (qaOne (I := I) (M := M) g gm)
      (covGrad (I := I) (M := M) g 0 2 T) =
      lrQA (I := I) (M := M) g gm := by
    rw [qaOne, ← appCc_assoc, ← appCc_assoc,
      omega_one (I := I) (M := M) g gm T hT htie]
    have hperm : appCc (I := I) (M := M) g 3 3
        (permCoeff (I := I) (M := M) g (Equiv.swap (0 : Fin 3) 1))
        (lrOmegaHat (I := I) (M := M) g gm) =
        domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 3) 1)
          (lrOmegaHat (I := I) (M := M) g gm) := by
      simpa only [appCcRS_zero_eq_appCc] using
        perm_app (I := I) (M := M) g (Equiv.swap (0 : Fin 3) 1)
          (lrOmegaHat (I := I) (M := M) g gm)
    rw [hperm]
    rfl
  rw [← appCc_assoc, ← appCc_assoc, ← appCc_assoc, ← appCc_assoc,
    ← appCc_assoc]
  rw [hqb, hqa]
  rw [← appCcRS_zero_eq_appCc, perm_app,
    ← appCcRS_zero_eq_appCc, perm_app,
    ← appCcRS_zero_eq_appCc, perm_app,
    ← appCcRS_zero_eq_appCc, perm_app,
    ← appCcRS_zero_eq_appCc, perm_app]
  rfl

theorem lrQuad_joint
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    (hT : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g T x u v =
        ccTensorBilin (I := I) g T x v u)
    {δ : ℝ}
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ) :
    C0Joint (I := I) g 0 4
      (realizedSmallSet (δ := δ) (δ' := δ))
      (fun t => lrQuadF (I := I) (M := M) g
        (realizedFam (I := I) g T 0 hδ hδZ t)) := by
  let S := realizedSmallSet (δ := δ) (δ' := δ)
  have hQ := quadOp_joint (I := I) (M := M) g T hδ hδZ
  have hdT := c0j_const (I := I) (M := M) g (S := S)
    (covGrad (I := I) (M := M) g 0 2 T)
  have hsdT := c0j_param (I := I) (M := M) g hdT
  have happ := c0j_app (I := I) (M := M) g hQ hsdT
  refine happ.congr (fun q hq => ?_)
  refine congrArg (fun z => TotalSpace.mk' (TensorRSModel 0 4 ℝ E)
    (E := fun x : M => TensorRSSpace 0 4 I x) q.1 z) ?_
  have hsymm : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g (q.2 • T) x u v =
        ccTensorBilin (I := I) g (q.2 • T) x v u := by
    intro x u v
    simp only [ccTensorBilin_apply, ccTensorModel_smul,
      ContinuousMultilinearMap.smul_apply, smul_eq_mul]
    apply congrArg (fun z : ℝ => q.2 * z)
    simpa only [ccTensorBilin_apply] using hT x u v
  have htie : ∀ (x : M) (u v : TangentSpace I x),
      (realizedFam (I := I) g T 0 hδ hδZ q.2).inner x u v =
        g.inner x u v +
          ccTensorBilinSymm (I := I) g (q.2 • T) x u v := by
    intro x u v
    rw [← show convexPerturbation (I := I) g T 0 q.2 = q.2 • T by
      simp only [convexPerturbation, smul_zero, zero_add]]
    exact realizedFam_inner_of_mem
      (I := I) g T 0 hδ hδZ hq.2 x u v
  have heq := quad_op (I := I) (M := M) g
    (realizedFam (I := I) g T 0 hδ hδZ q.2) (q.2 • T) hsymm htie
  have hsec := congrArg
    (fun A : SmoothCcTensor g 0 4 => A.toSection q.1) heq
  simpa only [S, appCcRS_zero_eq_appCc, covGrad_smul] using hsec.symm

noncomputable def quadZero
    (g gm : SmoothRiemannianMetric I M) : SmoothCcTensor g 2 2 :=
  appCcRS (I := I) (M := M) g 2 6 2
    (lieCovPair (I := I) (M := M) g gm)
    (appCcRS (I := I) (M := M) g 2 6 6
      (permCoeff (I := I) (M := M) g lieCovSigma)
      (slotExtendIter (I := I) (M := M) g 0 4 2
        (lrQuadF (I := I) (M := M) g gm)))

noncomputable def curvZero
    (g gm : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    (s : ℝ) :
    SmoothCcTensor g 2 2 :=
  (-1 : ℝ) •
    appCcRS (I := I) (M := M) g 2 6 2
      (lieCovPair (I := I) (M := M) g gm)
      (appCcRS (I := I) (M := M) g 2 6 6
        (permCoeff (I := I) (M := M) g lieCovSigma)
        (slotExtendIter (I := I) (M := M) g 0 4 2
          ((-(s / 2) : ℝ) • lrCurvF (I := I) (M := M) g T)))

theorem lie_aff_zero
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
    let gm := realizedFam (I := I) g T 0 hδ hδZ s
    (deTurckLieCovDerivArmField (I := I) (M := M) g gm g -
        edgeLiePairFam (I := I) (M := M) g T hδ hδZ
          lieRefoldQ lieRefoldEps s) -
      quadZero (I := I) (M := M) g gm =
        curvZero (I := I) (M := M) g gm T s := by
  dsimp only
  rw [edgeEq (I := I) (M := M) g T hδ hδZ s]
  rw [lieCov_residual (I := I) (M := M)
    g T hδ_lt hδ hδZ hT hs]
  rw [lieCovR4_eq (I := I) (M := M) g T hδ hδZ s]
  rw [← perm_rs (I := I) (M := M) g lieCovSigma]
  simp only [quadZero, curvZero, slotExtendIter,
    slotExtend_sub, appCcRS_sub_right]
  module

theorem quadZero_joint
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    (hT : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g T x u v =
        ccTensorBilin (I := I) g T x v u)
    {δ : ℝ}
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ) :
    C0Joint (I := I) g 2 2
      (realizedSmallSet (δ := δ) (δ' := δ))
      (fun t => quadZero (I := I) (M := M) g
        (realizedFam (I := I) g T 0 hδ hδZ t)) := by
  let S := realizedSmallSet (δ := δ) (δ' := δ)
  have hlr := lrQuad_joint (I := I) (M := M) g T hT hδ hδZ
  have hslot := slot24_joint (I := I) (M := M) g hlr
  have hperm := c0j_const (I := I) (M := M) g (S := S)
    (permCoeff (I := I) (M := M) g lieCovSigma)
  have hmid := c0j_app (I := I) (M := M) g hperm hslot
  have hpair := pairTrace_joint (I := I) (M := M) g T hδ hδZ
  simpa only [S, quadZero] using
    c0j_app (I := I) (M := M) g hpair hmid

noncomputable def quadMid
    (g gm : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2) :
    SmoothCcTensor g 3 6 :=
  appCcRS (I := I) (M := M) g 3 5 6
    (slotExtendIter (I := I) (M := M) g 3 4 2
      (quadOp (I := I) (M := M) g gm))
    (prod23 (I := I) (M := M) g T)

theorem quad_mid
    (g gm : SmoothRiemannianMetric I M)
    (D : SmoothCcTensor g 0 3) (W : SmoothCcTensor g 0 2) :
    appCc (I := I) (M := M) g 3 6
        (quadMid (I := I) (M := M) g gm W) D =
      appCc (I := I) (M := M) g 2 6
        (slotExtendIter (I := I) (M := M) g 0 4 2
          (appCc (I := I) (M := M) g 3 4
            (quadOp (I := I) (M := M) g gm) D)) W := by
  have hprod : appCc (I := I) (M := M) g 3 5
      (prod23 (I := I) (M := M) g W) D =
      appCc (I := I) (M := M) g 2 5
        (slotExtendIter (I := I) (M := M) g 0 3 2 D) W := by
    simpa only [appCcRS_zero_eq_appCc] using
      prod23_app (I := I) (M := M) g D W
  have hslot : appCcRS (I := I) (M := M) g 2 5 6
      (slotExtendIter (I := I) (M := M) g 3 4 2
        (quadOp (I := I) (M := M) g gm))
      (slotExtendIter (I := I) (M := M) g 0 3 2 D) =
      slotExtendIter (I := I) (M := M) g 0 4 2
        (appCc (I := I) (M := M) g 3 4
          (quadOp (I := I) (M := M) g gm) D) := by
    simpa only [appCcRS_zero_eq_appCc] using
      slot_comp2 (I := I) (M := M) g 0 3 4
        (quadOp (I := I) (M := M) g gm) D
  rw [quadMid]
  calc
    _ = appCc (I := I) (M := M) g 5 6
          (slotExtendIter (I := I) (M := M) g 3 4 2
            (quadOp (I := I) (M := M) g gm))
          (appCc (I := I) (M := M) g 3 5
            (prod23 (I := I) (M := M) g W) D) :=
      (appCc_assoc (I := I) (M := M) g 3 5 6 _ _ _).symm
    _ = appCc (I := I) (M := M) g 5 6
          (slotExtendIter (I := I) (M := M) g 3 4 2
            (quadOp (I := I) (M := M) g gm))
          (appCc (I := I) (M := M) g 2 5
            (slotExtendIter (I := I) (M := M) g 0 3 2 D) W) := by
      rw [hprod]
    _ = appCc (I := I) (M := M) g 2 6
          (appCcRS (I := I) (M := M) g 2 5 6
            (slotExtendIter (I := I) (M := M) g 3 4 2
              (quadOp (I := I) (M := M) g gm))
            (slotExtendIter (I := I) (M := M) g 0 3 2 D)) W :=
      appCc_assoc (I := I) (M := M) g 2 5 6 _ _ _
    _ = _ := by rw [hslot]

theorem quadMid_joint
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    {δ : ℝ}
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ) :
    C0Joint (I := I) g 3 6
      (realizedSmallSet (δ := δ) (δ' := δ))
      (fun t => quadMid (I := I) (M := M) g
        (realizedFam (I := I) g T 0 hδ hδZ t) T) := by
  let S := realizedSmallSet (δ := δ) (δ' := δ)
  apply contMDiffOn_clm_section_of_pointwise_jointMR (I := I) (M := M)
    (F₁ := Tensor0SModel 3 ℝ E) (V₁ := fun x : M => Tensor0SSpace 3 I x)
    (F₂ := Tensor0SModel 6 ℝ E) (V₂ := fun x : M => Tensor0SSpace 6 I x)
    (φ := fun q : M × ℝ =>
      (quadMid (I := I) (M := M) g
        (realizedFam (I := I) g T 0 hδ hδZ q.2) T).toSection q.1)
    (S := S)
  intro Y
  have hY : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, Tensor0SModel 3 ℝ E)) ∞
      (fun q : M × ℝ => TotalSpace.mk' (Tensor0SModel 3 ℝ E)
        (E := fun x : M => Tensor0SSpace 3 I x) q.1 (Y q.1))
      ((Set.univ : Set M) ×ˢ S) :=
    Y.contMDiff.comp_contMDiffOn contMDiffOn_fst
  have hQ := quadOp_joint (I := I) (M := M) g T hδ hδZ
  have hQY := ContMDiffOn.clm_bundle_apply (b := Prod.fst) hQ hY
  have hT := c0j_const (I := I) (M := M) g (S := S) T
  have hunit : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, Tensor0SModel 0 ℝ E)) ∞
      (fun q : M × ℝ => TotalSpace.mk' (Tensor0SModel 0 ℝ E)
        (E := fun x : M => Tensor0SSpace 0 I x) q.1
        (unitTensor (I := I) (M := M) q.1))
      ((Set.univ : Set M) ×ˢ S) :=
    (unitZeroSec (I := I) (M := M)).contMDiff.comp_contMDiffOn
      contMDiffOn_fst
  have hTv := ContMDiffOn.clm_bundle_apply (b := Prod.fst) hT hunit
  have hprod := jointTensor0SProd_local (I := I) (p := 2) (q := 4)
    (S := S)
    (fun q : M × ℝ =>
      (show Tensor0SSpace 0 I q.1 →L[ℝ] Tensor0SSpace 2 I q.1 from
        T.toSection q.1) (unitTensor (I := I) (M := M) q.1))
    (fun q : M × ℝ =>
      (show Tensor0SSpace 3 I q.1 →L[ℝ] Tensor0SSpace 4 I q.1 from
        (quadOp (I := I) (M := M) g
          (realizedFam (I := I) g T 0 hδ hδZ q.2)).toSection q.1)
        (Y q.1)) hTv hQY
  have hprod' : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, Tensor0SModel 6 ℝ E)) ∞
      (fun q : M × ℝ => TotalSpace.mk' (Tensor0SModel 6 ℝ E)
        (E := fun x : M => Tensor0SSpace 6 I x) q.1
        (tensor0SProdKappaFib (I := I) (p := 2) (q := 4) q.1
          ((show Tensor0SSpace 3 I q.1 →L[ℝ] Tensor0SSpace 4 I q.1 from
            (quadOp (I := I) (M := M) g
              (realizedFam (I := I) g T 0 hδ hδZ q.2)).toSection q.1)
            (Y q.1))
          ((show Tensor0SSpace 0 I q.1 →L[ℝ] Tensor0SSpace 2 I q.1 from
            T.toSection q.1) (unitTensor (I := I) (M := M) q.1))))
      ((Set.univ : Set M) ×ˢ S) := by
    refine hprod.congr (fun q _ => ?_)
    refine congrArg (fun z => TotalSpace.mk' (Tensor0SModel 6 ℝ E)
      (E := fun x : M => Tensor0SSpace 6 I x) q.1 z) ?_
    rw [tensor0SProdKappaFib_apply]
  refine hprod'.congr (fun q _ => ?_)
  refine congrArg (fun z => TotalSpace.mk' (Tensor0SModel 6 ℝ E)
    (E := fun x : M => Tensor0SSpace 6 I x) q.1 z) ?_
  let D := lift0 (I := I) (M := M) g Y
  have hmid := quad_mid (I := I) (M := M) g
    (realizedFam (I := I) g T 0 hδ hδZ q.2) D T
  have hval := congrArg
    (fun A : SmoothCcTensor g 0 6 =>
      (show Tensor0SSpace 0 I q.1 →L[ℝ] Tensor0SSpace 6 I q.1 from
        A.toSection q.1) (unitTensor (I := I) (M := M) q.1)) hmid
  have hD : D.toSection q.1 (unitTensor (I := I) (M := M) q.1) =
      Y q.1 := lift0_unit (I := I) (M := M) g Y q.1
  simp only [appCc_toSection, ContinuousLinearMap.comp_apply] at hval
  rw [hD] at hval
  rw [slotLift24] at hval
  simp only [appCc_toSection, ContinuousLinearMap.comp_apply] at hval
  rw [hD] at hval
  exact hval

noncomputable def quadAct
    (g gm : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2) :
    SmoothCcTensor g 3 2 :=
  appCcRS (I := I) (M := M) g 3 6 2
    (lieCovPair (I := I) (M := M) g gm)
    (appCcRS (I := I) (M := M) g 3 6 6
      (permCoeff (I := I) (M := M) g lieCovSigma)
      (quadMid (I := I) (M := M) g gm T))

set_option backward.isDefEq.respectTransparency false in
theorem appRSSmulLeft
    (g : SmoothRiemannianMetric I M) (a b c : ℕ)
    (s : ℝ) (Φ : SmoothCcTensor g b c) (W : SmoothCcTensor g a b) :
    appCcRS (I := I) (M := M) g a b c (s • Φ) W =
      s • appCcRS (I := I) (M := M) g a b c Φ W := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [show ((s • appCcRS (I := I) (M := M) g a b c Φ W).toSection x) =
      s • (appCcRS (I := I) (M := M) g a b c Φ W).toSection x from by
    rw [SmoothCcTensor.toSection_smul]
    rfl]
  rw [appCcRS_toSection, appCcRS_toSection]
  rw [show ((s • Φ).toSection x : TensorRSSpace b c I x) =
      s • Φ.toSection x from by
    rw [SmoothCcTensor.toSection_smul]
    rfl]
  rw [ContinuousLinearMap.smul_comp]

set_option backward.isDefEq.respectTransparency false in
theorem slotExtendSmul
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (a : ℝ) (X : SmoothCcTensor g r s) :
    slotExtend (I := I) (M := M) g r s (a • X) =
      a • slotExtend (I := I) (M := M) g r s X := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro D
  rw [show ((a • slotExtend (I := I) (M := M) g r s X).toSection x) =
      a • (slotExtend (I := I) (M := M) g r s X).toSection x from by
    rw [SmoothCcTensor.toSection_smul]
    rfl]
  rw [ContinuousLinearMap.smul_apply]
  rw [show ((slotExtend (I := I) (M := M) g r s (a • X)).toSection x) D =
      (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x).symm
        ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from
          (a • X).toSection x).comp
          (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) r x D)) from rfl]
  rw [show ((slotExtend (I := I) (M := M) g r s X).toSection x) D =
      (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x).symm
        ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from
          X.toSection x).comp
          (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) r x D)) from rfl]
  rw [show ((a • X).toSection x : TensorRSSpace r s I x) =
      a • X.toSection x from by
    rw [SmoothCcTensor.toSection_smul]
    rfl]
  rw [ContinuousLinearMap.smul_comp, map_smul]

theorem slotIterSmul
    (g : SmoothRiemannianMetric I M) (r s w : ℕ)
    (a : ℝ) (X : SmoothCcTensor g r s) :
    slotExtendIter (I := I) (M := M) g r s w (a • X) =
      a • slotExtendIter (I := I) (M := M) g r s w X := by
  induction w with
  | zero => simp only [slotExtendIter]
  | succ w ih =>
      change slotExtend (I := I) (M := M) g (r + w) (s + w)
          (slotExtendIter (I := I) (M := M) g r s w (a • X)) = _
      rw [ih, slotExtendSmul]
      rfl

theorem prod23Smul
    (g : SmoothRiemannianMetric I M) (a : ℝ)
    (W : SmoothCcTensor g 0 2) :
    prod23 (I := I) (M := M) g (a • W) =
      a • prod23 (I := I) (M := M) g W := by
  rw [prod23, slotIterSmul, appCcRS_smul_right]
  rfl

theorem innerOneSmul
    (g : SmoothRiemannianMetric I M) (a : ℝ)
    (W : SmoothCcTensor g 0 2) :
    innerOne (I := I) (M := M) g (a • W) =
      a • innerOne (I := I) (M := M) g W := by
  rw [innerOne, symmRaiseEndo_smul, slotInsertEndoCc_smul,
    appRSSmulLeft]
  rfl

theorem innerActSmul
    (g gm : SmoothRiemannianMetric I M) (a : ℝ)
    (W : SmoothCcTensor g 0 2) :
    innerAct (I := I) (M := M) g gm (a • W) =
      a • innerAct (I := I) (M := M) g gm W := by
  rw [innerAct, innerOneSmul, appRSSmulLeft]
  rfl

theorem aaMidOneSmul
    (g gm : SmoothRiemannianMetric I M) (a : ℝ)
    (W : SmoothCcTensor g 0 2)
    (mid : Equiv.Perm (Fin 3)) (out : Equiv.Perm (Fin 4)) :
    aaMidOne (I := I) (M := M) g gm (a • W) mid out =
      a • aaMidOne (I := I) (M := M) g gm W mid out := by
  simp only [aaMidOne, innerActSmul, appCcRS_smul_right]

theorem aaBareOneSmul
    (g gm : SmoothRiemannianMetric I M) (a : ℝ)
    (W : SmoothCcTensor g 0 2) (out : Equiv.Perm (Fin 4)) :
    aaBareOne (I := I) (M := M) g gm (a • W) out =
      a • aaBareOne (I := I) (M := M) g gm W out := by
  simp only [aaBareOne, innerActSmul, appCcRS_smul_right]

theorem aaKerOneSmul
    (g gm : SmoothRiemannianMetric I M) (a : ℝ)
    (W : SmoothCcTensor g 0 2) :
    aaKerOne (I := I) (M := M) g gm (a • W) =
      a • aaKerOne (I := I) (M := M) g gm W := by
  simp only [aaKerOne, aaMidOneSmul, aaBareOneSmul]
  module

theorem aaOneSmul
    (g gm : SmoothRiemannianMetric I M) (a : ℝ)
    (W : SmoothCcTensor g 0 2) :
    aaOne (I := I) (M := M) g gm (a • W) =
      a • aaOne (I := I) (M := M) g gm W := by
  rw [aaOne, aaKerOneSmul, appCcRS_smul_right]
  rfl

theorem daTransSmul
    (g gm : SmoothRiemannianMetric I M) (a : ℝ)
    (W : SmoothCcTensor g 0 2) :
    LowBaseInternal.daTrans (I := I) (M := M) g gm (a • W) =
      a • LowBaseInternal.daTrans (I := I) (M := M) g gm W := by
  simp only [LowBaseInternal.daTrans, LowBaseInternal.daTransMono,
    LowBaseInternal.daWeight, appCc_smul_right,
    curvatureRefoldMonomialCoeffField_unitValue_smul]
  module

theorem ricciDASmul
    (g gm : SmoothRiemannianMetric I M) (a : ℝ)
    (W : SmoothCcTensor g 0 2) :
    LowBaseInternal.ricciDAOne (I := I) (M := M) g gm (a • W) =
      a • LowBaseInternal.ricciDAOne (I := I) (M := M) g gm W := by
  rw [LowBaseInternal.ricciDAOne, daTransSmul, appRSSmulLeft]
  rfl

theorem ricciOneSmul
    (g gm : SmoothRiemannianMetric I M) (a : ℝ)
    (W : SmoothCcTensor g 0 2) :
    ricciOne (I := I) (M := M) g gm (a • W) =
      a • ricciOne (I := I) (M := M) g gm W := by
  simp only [ricciOne, aaOneSmul, symmS_smul, ricciDASmul]
  module

set_option backward.isDefEq.respectTransparency false in
theorem raise0Smul
    (g : SmoothRiemannianMetric I M) (s : ℕ) (a : ℝ)
    (W : SmoothCcTensor g 0 (s + 2)) :
    cometricRaiseSlot0Field (I := I) (M := M) g s (a • W) =
      a • cometricRaiseSlot0Field (I := I) (M := M) g s W := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [show ((a • cometricRaiseSlot0Field (I := I) (M := M) g s W).toSection x) =
      a • (cometricRaiseSlot0Field (I := I) (M := M) g s W).toSection x from by
    rw [SmoothCcTensor.toSection_smul]
    rfl]
  rw [cometricRaiseSlot0Field_toSection, cometricRaiseSlot0Field_toSection]
  rw [show ((a • W).toSection x : TensorRSSpace 0 (s + 2) I x) =
      a • W.toSection x from by
    rw [SmoothCcTensor.toSection_smul]
    rfl]
  rw [ContinuousLinearMap.smul_apply]
  apply ContinuousLinearMap.ext
  intro om
  rw [ContinuousLinearMap.smul_apply,
    cometricRaiseSlot0Fib_clm_apply, cometricRaiseSlot0Fib_clm_apply]
  rw [map_smul]

theorem vbCoreSmul
    (g gm : SmoothRiemannianMetric I M) (a : ℝ)
    (W : SmoothCcTensor g 0 2) :
    vbCore (I := I) (M := M) g gm (a • W) =
      a • vbCore (I := I) (M := M) g gm W := by
  simp only [vbCore, raise0Smul, appRSSmulLeft, appCcRS_smul_right]

theorem vbOneSmul
    (g gm : SmoothRiemannianMetric I M) (a : ℝ)
    (W : SmoothCcTensor g 0 2) :
    vbOne (I := I) (M := M) g gm (a • W) =
      a • vbOne (I := I) (M := M) g gm W := by
  simp only [vbOne, vbCoreSmul]
  module

theorem amixHalfSmul
    (g gm gB : SmoothRiemannianMetric I M) (a : ℝ)
    (W : SmoothCcTensor g 0 2) (σ : Equiv.Perm (Fin 4)) :
    amixHalfOne (I := I) (M := M) g gm gB (a • W) σ =
      a • amixHalfOne (I := I) (M := M) g gm gB W σ := by
  simp only [amixHalfOne, prod23Smul, appRSSmulLeft,
    appCcRS_smul_right]

theorem amixOneSmul
    (g gm gB : SmoothRiemannianMetric I M) (a : ℝ)
    (W : SmoothCcTensor g 0 2) :
    amixOne (I := I) (M := M) g gm gB (a • W) =
      a • amixOne (I := I) (M := M) g gm gB W := by
  simp only [amixOne, amixHalfSmul]
  module

theorem quadMidSmul
    (g gm : SmoothRiemannianMetric I M) (a : ℝ)
    (W : SmoothCcTensor g 0 2) :
    quadMid (I := I) (M := M) g gm (a • W) =
      a • quadMid (I := I) (M := M) g gm W := by
  rw [quadMid, prod23Smul, appCcRS_smul_right]
  rfl

theorem quadActSmul
    (g gm : SmoothRiemannianMetric I M) (a : ℝ)
    (W : SmoothCcTensor g 0 2) :
    quadAct (I := I) (M := M) g gm (a • W) =
      a • quadAct (I := I) (M := M) g gm W := by
  simp only [quadAct, quadMidSmul, appCcRS_smul_right]

theorem quadAct_joint
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    {δ : ℝ}
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ) :
    C0Joint (I := I) g 3 2
      (realizedSmallSet (δ := δ) (δ' := δ))
      (fun t => quadAct (I := I) (M := M) g
        (realizedFam (I := I) g T 0 hδ hδZ t) T) := by
  let S := realizedSmallSet (δ := δ) (δ' := δ)
  have hmid := quadMid_joint (I := I) (M := M) g T hδ hδZ
  have hperm := c0j_const (I := I) (M := M) g (S := S)
    (permCoeff (I := I) (M := M) g lieCovSigma)
  have hσ := c0j_app (I := I) (M := M) g hperm hmid
  have hpair := pairTrace_joint (I := I) (M := M) g T hδ hδZ
  simpa only [S, quadAct] using
    c0j_app (I := I) (M := M) g hpair hσ

theorem quad_act
    (g gm : SmoothRiemannianMetric I M)
    (P W : SmoothCcTensor g 0 2)
    (hP : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g P x u v =
        ccTensorBilin (I := I) g P x v u)
    (htie : ∀ (x : M) (u v : TangentSpace I x),
      gm.inner x u v =
        g.inner x u v + ccTensorBilinSymm (I := I) g P x u v) :
    appCc (I := I) (M := M) g 2 2
        (quadZero (I := I) (M := M) g gm) W =
      appCc (I := I) (M := M) g 3 2
        (quadAct (I := I) (M := M) g gm W)
        (covGrad (I := I) (M := M) g 0 2 P) := by
  let dP := covGrad (I := I) (M := M) g 0 2 P
  let X := slotExtendIter (I := I) (M := M) g 0 4 2
    (lrQuadF (I := I) (M := M) g gm)
  let Y := appCcRS (I := I) (M := M) g 3 5 6
    (slotExtendIter (I := I) (M := M) g 3 4 2
      (quadOp (I := I) (M := M) g gm))
    (prod23 (I := I) (M := M) g W)
  have hprod : appCc (I := I) (M := M) g 3 5
      (prod23 (I := I) (M := M) g W) dP =
      appCc (I := I) (M := M) g 2 5
        (slotExtendIter (I := I) (M := M) g 0 3 2 dP) W := by
    simpa only [appCcRS_zero_eq_appCc] using
      prod23_app (I := I) (M := M) g dP W
  have hslot : appCcRS (I := I) (M := M) g 2 5 6
      (slotExtendIter (I := I) (M := M) g 3 4 2
        (quadOp (I := I) (M := M) g gm))
      (slotExtendIter (I := I) (M := M) g 0 3 2 dP) =
      slotExtendIter (I := I) (M := M) g 0 4 2
        (appCc (I := I) (M := M) g 3 4
          (quadOp (I := I) (M := M) g gm) dP) := by
    simpa only [appCcRS_zero_eq_appCc] using
      slot_comp2 (I := I) (M := M) g 0 3 4
        (quadOp (I := I) (M := M) g gm) dP
  have hinner : appCc (I := I) (M := M) g 3 6 Y dP =
      appCc (I := I) (M := M) g 2 6 X W := by
    calc
      appCc (I := I) (M := M) g 3 6 Y dP =
          appCc (I := I) (M := M) g 5 6
            (slotExtendIter (I := I) (M := M) g 3 4 2
            (quadOp (I := I) (M := M) g gm))
            (appCc (I := I) (M := M) g 3 5
              (prod23 (I := I) (M := M) g W) dP) :=
        (appCc_assoc (I := I) (M := M) g 3 5 6 _ _ _).symm
      _ = appCc (I := I) (M := M) g 5 6
            (slotExtendIter (I := I) (M := M) g 3 4 2
              (quadOp (I := I) (M := M) g gm))
            (appCc (I := I) (M := M) g 2 5
              (slotExtendIter (I := I) (M := M) g 0 3 2 dP) W) := by
        rw [hprod]
      _ = appCc (I := I) (M := M) g 2 6
            (appCcRS (I := I) (M := M) g 2 5 6
              (slotExtendIter (I := I) (M := M) g 3 4 2
                (quadOp (I := I) (M := M) g gm))
              (slotExtendIter (I := I) (M := M) g 0 3 2 dP)) W :=
        appCc_assoc (I := I) (M := M) g 2 5 6 _ _ _
      _ = appCc (I := I) (M := M) g 2 6
            (slotExtendIter (I := I) (M := M) g 0 4 2
              (appCc (I := I) (M := M) g 3 4
                (quadOp (I := I) (M := M) g gm) dP)) W := by
        rw [hslot]
      _ = appCc (I := I) (M := M) g 2 6 X W := by
        rw [quad_op (I := I) (M := M) g gm P hP htie]
  rw [quadZero, quadAct]
  change appCc (I := I) (M := M) g 2 2
      (appCcRS (I := I) (M := M) g 2 6 2
        (lieCovPair (I := I) (M := M) g gm)
        (appCcRS (I := I) (M := M) g 2 6 6
          (permCoeff (I := I) (M := M) g lieCovSigma) X)) W =
    appCc (I := I) (M := M) g 3 2
      (appCcRS (I := I) (M := M) g 3 6 2
        (lieCovPair (I := I) (M := M) g gm)
        (appCcRS (I := I) (M := M) g 3 6 6
          (permCoeff (I := I) (M := M) g lieCovSigma) Y)) dP
  calc
    _ = appCc (I := I) (M := M) g 6 2
        (lieCovPair (I := I) (M := M) g gm)
        (appCc (I := I) (M := M) g 2 6
          (appCcRS (I := I) (M := M) g 2 6 6
            (permCoeff (I := I) (M := M) g lieCovSigma) X) W) :=
      (appCc_assoc (I := I) (M := M) g 2 6 2 _ _ _).symm
    _ = appCc (I := I) (M := M) g 6 2
        (lieCovPair (I := I) (M := M) g gm)
        (appCc (I := I) (M := M) g 6 6
          (permCoeff (I := I) (M := M) g lieCovSigma)
          (appCc (I := I) (M := M) g 2 6 X W)) := by
      congr 1
    _ = appCc (I := I) (M := M) g 6 2
        (lieCovPair (I := I) (M := M) g gm)
        (appCc (I := I) (M := M) g 6 6
          (permCoeff (I := I) (M := M) g lieCovSigma)
          (appCc (I := I) (M := M) g 3 6 Y dP)) := by
      rw [hinner]
    _ = appCc (I := I) (M := M) g 6 2
        (lieCovPair (I := I) (M := M) g gm)
        (appCc (I := I) (M := M) g 3 6
          (appCcRS (I := I) (M := M) g 3 6 6
            (permCoeff (I := I) (M := M) g lieCovSigma) Y) dP) := by
      congr 1
    _ = _ :=
      appCc_assoc (I := I) (M := M) g 3 6 2 _ _ _


end LowRegBgC0Core
end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral
