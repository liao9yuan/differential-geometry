import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CurvatureCoefficientDifferenceJetTower.Envelope

/-!
# Top-separated transport mirrors and the lowered-difference rung

Chunk of the `CurvatureCoefficientDifferenceJetTower` tower, split
out of the former 15111-line monolith (no longer elaborable in a
single Lean process).  Every declaration is verbatim.  The former
`private` helpers were promoted into the internal `CurvatureCoefficientDifferenceJetTower`
scope, so the public `Connection` API is unchanged.  Chunk map:
`CurvatureCoefficientDifferenceJetTower.md`.
-/

noncomputable section

set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization (gFibreOpBound ccTensorBilinSymm ccTensorBilin ccTensorBilin_apply ccTensorModel ccTensorMultilinear ccTensorBilinSymm_contMDiff ccTensorBilinSymm_apply ccTensorBilinSymm_symm)
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

namespace CurvatureCoefficientDifferenceJetTower
end CurvatureCoefficientDifferenceJetTower

open CurvatureCoefficientDifferenceJetTower

section TopSeparatedTransportMirrors

set_option backward.isDefEq.respectTransparency false

namespace CurvatureCoefficientDifferenceJetTower

set_option linter.unusedSectionVars false in
lemma tsCastRankCc_db_refl (g₀ : SmoothRiemannianMetric I M) (r : ℕ) {a : ℕ} (h : a = a)
    (W : SmoothCcTensor g₀ r a) : castRankCc_db g₀ r h W = W := rfl

set_option linter.unusedSectionVars false in
lemma tsCovGrad_castRankCc_db (g₀ : SmoothRiemannianMetric I M) (r : ℕ) {a b : ℕ}
    (h : a = b) (W : SmoothCcTensor g₀ r a) :
    covGrad (I := I) (M := M) g₀ r b (castRankCc_db g₀ r h W) =
      castRankCc_db g₀ r (by omega : a + 1 = b + 1)
        (covGrad (I := I) (M := M) g₀ r a W) := by
  subst h; rfl

set_option linter.unusedSectionVars false in
lemma tsCastRankCc_db_trans (g₀ : SmoothRiemannianMetric I M) (r : ℕ) {a b c : ℕ}
    (h₁ : a = b) (h₂ : b = c) (W : SmoothCcTensor g₀ r a) :
    castRankCc_db g₀ r h₂ (castRankCc_db g₀ r h₁ W) =
      castRankCc_db g₀ r (h₁.trans h₂) W := by
  subst h₁; subst h₂; rfl

set_option linter.unusedSectionVars false in
lemma tsCastRankCc_db_sub (g₀ : SmoothRiemannianMetric I M) (r : ℕ) {a b : ℕ}
    (h : a = b) (W W' : SmoothCcTensor g₀ r a) :
    castRankCc_db g₀ r h (W - W') = castRankCc_db g₀ r h W - castRankCc_db g₀ r h W' := by
  subst h; rfl

set_option linter.unusedSectionVars false in
lemma tsCastRankCc_db_add (g₀ : SmoothRiemannianMetric I M) (r : ℕ) {a b : ℕ}
    (h : a = b) (W W' : SmoothCcTensor g₀ r a) :
    castRankCc_db g₀ r h (W + W') = castRankCc_db g₀ r h W + castRankCc_db g₀ r h W' := by
  subst h; rfl

set_option linter.unusedSectionVars false in
lemma tsExists_iteratedCovGrad_domDomCongrSection (g₀ : SmoothRiemannianMetric I M)
    {s : ℕ} (σ : Equiv.Perm (Fin s)) (S : SmoothCcTensor g₀ 0 s) (i : ℕ) :
    ∃ σ' : Equiv.Perm (Fin (s + i)),
      iteratedCovGrad (I := I) g₀ 0 s i (domDomCongrSection (I := I) g₀ σ S) =
        domDomCongrSection (I := I) g₀ σ' (iteratedCovGrad (I := I) g₀ 0 s i S) := by
  obtain ⟨σ', hσ'⟩ := exists_iteratedCovGrad_unit_toModel_domDomCongr (I := I) (M := M)
    g₀ s σ S (domDomCongrSection (I := I) g₀ σ S)
    (fun y => domDomCongrSection_unitModel (I := I) g₀ σ S y) i
  refine ⟨σ', ?_⟩
  apply smoothCcTensor_ext_of_unitModel (I := I) (M := M) g₀
  intro x
  rw [hσ' x, domDomCongrSection_unitModel]

set_option linter.unusedSectionVars false in
lemma tsExists_covGrad_domDomCongrSection (g₀ : SmoothRiemannianMetric I M)
    {s : ℕ} (σ : Equiv.Perm (Fin s)) (S : SmoothCcTensor g₀ 0 s) :
    ∃ σ' : Equiv.Perm (Fin (s + 1)),
      covGrad (I := I) (M := M) g₀ 0 s (domDomCongrSection (I := I) g₀ σ S) =
        domDomCongrSection (I := I) g₀ σ' (covGrad (I := I) (M := M) g₀ 0 s S) := by
  obtain ⟨σ', hσ'⟩ := tsExists_iteratedCovGrad_domDomCongrSection (I := I) (M := M) g₀ σ S 1
  rw [show iteratedCovGrad (I := I) g₀ 0 s 1 (domDomCongrSection (I := I) g₀ σ S) =
      covGrad (I := I) (M := M) g₀ 0 s (domDomCongrSection (I := I) g₀ σ S) from by
    rw [iteratedCovGrad_succ, iteratedCovGrad_zero]; rfl] at hσ'
  rw [show iteratedCovGrad (I := I) g₀ 0 s 1 S =
      covGrad (I := I) (M := M) g₀ 0 s S from by
    rw [iteratedCovGrad_succ, iteratedCovGrad_zero]; rfl] at hσ'
  exact ⟨σ', hσ'⟩

set_option linter.unusedSectionVars false in
lemma tsDomDomCongrSection_refl (g₀ : SmoothRiemannianMetric I M) {s : ℕ}
    (S : SmoothCcTensor g₀ 0 s) :
    domDomCongrSection (I := I) g₀ (Equiv.refl (Fin s)) S = S := by
  apply smoothCcTensor_ext_of_unitModel (I := I) (M := M) g₀
  intro x
  rw [domDomCongrSection_unitModel]
  apply ContinuousMultilinearMap.ext
  intro v
  rw [ContinuousMultilinearMap.domDomCongr_apply]
  rfl

set_option linter.unusedSectionVars false in
lemma tsDomDomCongrSection_comp (g₀ : SmoothRiemannianMetric I M) {s : ℕ}
    (σ τ : Equiv.Perm (Fin s)) (S : SmoothCcTensor g₀ 0 s) :
    domDomCongrSection (I := I) g₀ τ (domDomCongrSection (I := I) g₀ σ S) =
      domDomCongrSection (I := I) g₀ (σ.trans τ) S := by
  apply smoothCcTensor_ext_of_unitModel (I := I) (M := M) g₀
  intro x
  rw [domDomCongrSection_unitModel, domDomCongrSection_unitModel,
    domDomCongrSection_unitModel]
  apply ContinuousMultilinearMap.ext
  intro v
  simp only [ContinuousMultilinearMap.domDomCongr_apply, Equiv.trans_apply]

set_option linter.unusedSectionVars false in
lemma tsDomDomCongrSection_sub (g₀ : SmoothRiemannianMetric I M) {s : ℕ}
    (σ : Equiv.Perm (Fin s)) (S S' : SmoothCcTensor g₀ 0 s) :
    domDomCongrSection (I := I) g₀ σ (S - S') =
      domDomCongrSection (I := I) g₀ σ S - domDomCongrSection (I := I) g₀ σ S' := by
  apply smoothCcTensor_ext_of_unitModel (I := I) (M := M) g₀
  intro x
  have hsub : ∀ (A B : SmoothCcTensor g₀ 0 s) (y : M),
      unitModel (I := I) (M := M) g₀ s (A - B) y =
        unitModel (I := I) (M := M) g₀ s A y - unitModel (I := I) (M := M) g₀ s B y := by
    intro A B y
    simp only [unitModel]
    rw [show ((A - B).toSection y) = A.toSection y - B.toSection y from by
      rw [SmoothCcTensor.toSection_sub]; rfl]
    rw [ContinuousLinearMap.sub_apply, Tensor0SSpace.toModel_sub]
  rw [hsub, domDomCongrSection_unitModel, domDomCongrSection_unitModel,
    domDomCongrSection_unitModel, hsub S S' x]
  apply ContinuousMultilinearMap.ext
  intro v
  simp only [ContinuousMultilinearMap.sub_apply, ContinuousMultilinearMap.domDomCongr_apply]

set_option linter.unusedSectionVars false in
lemma tsDomDomCongrSection_add (g₀ : SmoothRiemannianMetric I M) {s : ℕ}
    (σ : Equiv.Perm (Fin s)) (S S' : SmoothCcTensor g₀ 0 s) :
    domDomCongrSection (I := I) g₀ σ (S + S') =
      domDomCongrSection (I := I) g₀ σ S + domDomCongrSection (I := I) g₀ σ S' := by
  apply smoothCcTensor_ext_of_unitModel (I := I) (M := M) g₀
  intro x
  have hadd : ∀ (A B : SmoothCcTensor g₀ 0 s) (y : M),
      unitModel (I := I) (M := M) g₀ s (A + B) y =
        unitModel (I := I) (M := M) g₀ s A y + unitModel (I := I) (M := M) g₀ s B y := by
    intro A B y
    simp only [unitModel]
    rw [show ((A + B).toSection y) = A.toSection y + B.toSection y from by
      rw [SmoothCcTensor.toSection_add]; rfl]
    rw [ContinuousLinearMap.add_apply, Tensor0SSpace.toModel_add]
  rw [hadd, domDomCongrSection_unitModel, domDomCongrSection_unitModel,
    domDomCongrSection_unitModel, hadd S S' x]
  apply ContinuousMultilinearMap.ext
  intro v
  simp only [ContinuousMultilinearMap.add_apply, ContinuousMultilinearMap.domDomCongr_apply]

set_option linter.unusedSectionVars false in
lemma tsIteratedCovGrad_covGrad_eq_cast (g₀ : SmoothRiemannianMetric I M) (r s : ℕ)
    (W : SmoothCcTensor g₀ r s) (i : ℕ) :
    iteratedCovGrad (I := I) g₀ r (s + 1) i (covGrad (I := I) (M := M) g₀ r s W) =
      castRankCc_db g₀ r (by omega : s + (i + 1) = (s + 1) + i)
        (iteratedCovGrad (I := I) g₀ r s (i + 1) W) := by
  induction i with
  | zero =>
      rw [iteratedCovGrad_zero, iteratedCovGrad_succ, iteratedCovGrad_zero]
      rfl
  | succ i ih =>
      rw [iteratedCovGrad_succ, ih]
      rw [tsCovGrad_castRankCc_db (I := I) (M := M) g₀ r
        (by omega : s + (i + 1) = (s + 1) + i)]
      rw [show iteratedCovGrad (I := I) g₀ r s (i + 1 + 1) W =
          covGrad (I := I) (M := M) g₀ r (s + (i + 1))
            (iteratedCovGrad (I := I) g₀ r s (i + 1) W) from by
        rw [iteratedCovGrad_succ]]

set_option linter.unusedSectionVars false in
lemma tsExists_iteratedCovGrad_rsDomDomCongrSection (g₀ : SmoothRiemannianMetric I M)
    (r s : ℕ) (σ : Equiv.Perm (Fin s)) (Z : SmoothCcTensor g₀ r s) (i : ℕ) :
    ∃ σ' : Equiv.Perm (Fin (s + i)),
      ∀ x : M,
        ((iteratedCovGrad (I := I) g₀ r s i
            (rsDomDomCongrSection (I := I) (M := M) g₀ r s σ Z)).toSection x :
          Tensor0SSpace r I x →L[ℝ] Tensor0SSpace (s + i) I x) =
        rsDomDomCongr (I := I) (M := M) σ'
          ((iteratedCovGrad (I := I) g₀ r s i Z).toSection x) := by
  induction i with
  | zero =>
      refine ⟨σ, fun x => ?_⟩
      rw [iteratedCovGrad_zero, iteratedCovGrad_zero]
      rfl
  | succ i ih =>
      obtain ⟨σ', hσ'⟩ := ih
      refine ⟨Equiv.Perm.decomposeFin.symm (0, σ'), fun x => ?_⟩
      rw [iteratedCovGrad_succ, iteratedCovGrad_succ]
      apply ContinuousLinearMap.ext
      intro d
      apply Tensor0SSpace.toModel_injective
      apply ContinuousMultilinearMap.ext
      intro v
      have hL := covGrad_rs_toModel_domDomCongr (I := I) (M := M) g₀ r (s + i) σ'
        (iteratedCovGrad (I := I) g₀ r s i Z)
        (iteratedCovGrad (I := I) g₀ r s i
          (rsDomDomCongrSection (I := I) (M := M) g₀ r s σ Z))
        (fun y d' => by
          rw [hσ' y]
          exact toModel_rsDomDomCongr_apply (I := I) (M := M) σ' _ d') x d v
      refine hL.trans ?_
      exact (congrArg (fun f => f v) (toModel_rsDomDomCongr_apply (I := I) (M := M)
        (Equiv.Perm.decomposeFin.symm (0, σ'))
        ((covGrad (I := I) (M := M) g₀ r (s + i)
          (iteratedCovGrad (I := I) g₀ r s i Z)).toSection x) d)).symm

end CurvatureCoefficientDifferenceJetTower

section TsMetricLowering

open DifferentialGeometry.Integral.DivergenceTheorem

set_option backward.isDefEq.respectTransparency false

namespace CurvatureCoefficientDifferenceJetTower

def tsMetricCovec (g₀ : SmoothRiemannianMetric I M) (x : M) : Tensor0SSpace 2 I x :=
  (show ContinuousMultilinearMap ℝ (fun _ : Fin 2 => TangentSpace I x) ℝ from
    { toFun := fun m => g₀.inner x (m 0) (m 1)
      map_update_add' := by
        have h01 : (0 : Fin 2) ≠ 1 := by decide
        have h10 : (1 : Fin 2) ≠ 0 := by decide
        intro _ m i a a'
        fin_cases i <;>
          simp only [Fin.reduceFinMk, Fin.isValue, Function.update_self, ne_eq,
            Function.update_of_ne, h01, h10, not_false_eq_true, map_add,
            ContinuousLinearMap.add_apply]
      map_update_smul' := by
        have h01 : (0 : Fin 2) ≠ 1 := by decide
        have h10 : (1 : Fin 2) ≠ 0 := by decide
        intro _ m i c a
        fin_cases i <;>
          simp only [Fin.reduceFinMk, Fin.isValue, Function.update_self, ne_eq,
            Function.update_of_ne, h01, h10, not_false_eq_true, map_smul,
            ContinuousLinearMap.smul_apply]
      cont := ((g₀.inner x).continuous.comp (continuous_apply 0)).clm_apply
        (continuous_apply 1) }
    : Tensor0SSpace 2 I x)

set_option linter.unusedSectionVars false in
@[simp] lemma tsMetricCovec_apply (g₀ : SmoothRiemannianMetric I M) (x : M)
    (m : Fin 2 → TangentSpace I x) :
    tsMetricCovec (I := I) g₀ x m = g₀.inner x (m 0) (m 1) := rfl

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
theorem tsMetricCovec_section_contMDiff (g₀ : SmoothRiemannianMetric I M) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
        (E := fun z : M => Tensor0SSpace 2 I z) x (tsMetricCovec (I := I) g₀ x)) := by
  classical
  letI := Tensor0SBundle.tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 2
  refine (contMDiff_multilinearSection_iff_coord (𝕜 := ℝ) (F := E)
      (E := (TangentSpace I : M → Type _)) (IB := I) (n := (∞ : WithTop ℕ∞)) (Module.finBasis ℝ E)
      (fun x : M => (tsMetricCovec (I := I) g₀ x :
        Bundle.continuousMultilinearMap ℝ 2 E (TangentSpace I) x))).mpr ?_
  intro σ x₀
  set b := Module.finBasis ℝ E with hb
  set e₁ := trivializationAt E (TangentSpace I : M → Type _) x₀ with he₁def
  have he₁ : x₀ ∈ e₁.baseSet := mem_baseSet_trivializationAt E (TangentSpace I) x₀
  have hframe := e₁.isLocalFrameOn_localFrame_baseSet I (⊤ : ℕ∞) b
  obtain ⟨Y, hY⟩ := hframe.exists_contMDiffSection_eqOn_nhd e₁.open_baseSet he₁
  have hscalar : ContMDiffAt I 𝓘(ℝ, ℝ) ∞
      (fun x : M => g₀.inner x (Y (σ 0) x) (Y (σ 1) x)) x₀ :=
    (contMDiff_g_inner_of_smooth_sections (I := I) g₀ (Y (σ 0)) (Y (σ 1))).contMDiffAt
  refine hscalar.congr_of_eventuallyEq ?_
  have h_base₁ : ∀ᶠ x in 𝓝 x₀, x ∈ e₁.baseSet := e₁.open_baseSet.mem_nhds he₁
  filter_upwards [h_base₁, hY] with x hx₁ hYx
  rw [continuousMultilinearMap_basis_repr]
  have hframeEq : ∀ k : Fin 2, e₁.symmL ℝ x (b (σ k)) = (Y (σ k)) x := by
    intro k
    rw [hYx (σ k), Trivialization.localFrame_apply_of_mem_baseSet (hx := hx₁)]
    simp [Trivialization.basisAt]
  change g₀.inner x (e₁.symmL ℝ x (b (σ 0))) (e₁.symmL ℝ x (b (σ 1))) = _
  rw [hframeEq 0, hframeEq 1]

def tsMetricField (g₀ : SmoothRiemannianMetric I M) :
    Tensor0SBundle.Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) ∞ 2 :=
  letI := Tensor0SBundle.tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 2
  ⟨fun x => tsMetricCovec (I := I) g₀ x, tsMetricCovec_section_contMDiff (I := I) g₀⟩

def tsMetricCc (g₀ : SmoothRiemannianMetric I M) : SmoothCcTensor g₀ 0 2 where
  toSection :=
    MixedSection.fromMultilinearSection (𝕜 := ℝ) (F := E) (IB := I)
      (E := (TangentSpace I : M → Type _)) ∞ (tsMetricField (I := I) g₀)
  hasCompactSupport := HasCompactSupport.of_compactSpace _

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
lemma tsMetricCc_unitModel (g₀ : SmoothRiemannianMetric I M) (x : M) :
    unitModel (I := I) (M := M) g₀ 2 (tsMetricCc (I := I) (M := M) g₀) x =
      Tensor0SSpace.toModel (tsMetricCovec (I := I) g₀ x) := by
  rw [unitModel]
  rw [show (tsMetricCc (I := I) (M := M) g₀).toSection x
        (unitTensor (I := I) (M := M) x) =
      (MixedSection.eval₀ (F := E) (E := (TangentSpace I : M → Type _)) x).smulRight
          (tsMetricField (I := I) g₀ x)
          (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))
      from rfl]
  rw [ContinuousLinearMap.smulRight_apply, MixedSection.eval₀_apply,
    ContinuousMultilinearMap.constOfIsEmpty_apply, one_smul]
  rfl

set_option linter.unusedSectionVars false in
lemma tsToModel_om_single (x : M) (om : Tensor0SSpace 1 I x)
    (m : Fin 1 → TangentSpace I x) :
    Tensor0SSpace.toModel om (fun k => (m k : E)) =
      cotangentToDual (I := I) (x := x) om (m 0) := by
  rw [show (fun k : Fin 1 => (m k : E)) = (fun _ : Fin 1 => (m 0 : E)) from by
    funext k; fin_cases k; rfl]
  rw [cotangentToDual_apply]
  rfl

set_option linter.unusedSectionVars false in
lemma tsMetricCovec_curry_eq_flat (g₀ : SmoothRiemannianMetric I M) (x : M)
    (v : TangentSpace I x) :
    (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x) (tsMetricCovec (I := I) g₀ x) v =
      g0FlatCLM (I := I) g₀ x v := by
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro w
  have h1 := TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M) (n := 1)
    (T := tsMetricCovec (I := I) g₀ x) (v0 := v) (vs := fun k => w k)
  rw [show (Tensor0SSpace.toModel
        ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x)
          (tsMetricCovec (I := I) g₀ x) v)) w =
      Tensor0SSpace.toModel (tsMetricCovec (I := I) g₀ x)
        (Fin.cons v (fun k => w k)) from h1]
  rw [tsToModel_om_single (I := I) (M := M) x (g0FlatCLM (I := I) g₀ x v) w]
  rw [cotangentToDual_g0FlatCLM]
  rfl

noncomputable def tsLoweredSlot0 (g₀ : SmoothRiemannianMetric I M) (s : ℕ)
    (Z : SmoothCcTensor g₀ 1 (s + 1)) : SmoothCcTensor g₀ 0 (s + 2) :=
  appCc (I := I) (M := M) g₀ 2 (s + 2)
    (slotExtend (I := I) (M := M) g₀ 1 (s + 1) Z) (tsMetricCc (I := I) (M := M) g₀)

set_option linter.unusedSectionVars false in
lemma tsMetricCc_toSection_unit (g₀ : SmoothRiemannianMetric I M) (x : M) :
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
        (tsMetricCc (I := I) (M := M) g₀).toSection x)
      (unitTensor (I := I) (M := M) x) = tsMetricCovec (I := I) g₀ x := by
  apply Tensor0SSpace.toModel_injective
  have h := tsMetricCc_unitModel (I := I) (M := M) g₀ x
  rw [unitModel] at h
  exact h

set_option linter.unusedSectionVars false in
lemma tsLoweredSlot0_unitModel_apply (g₀ : SmoothRiemannianMetric I M) (s : ℕ)
    (Z : SmoothCcTensor g₀ 1 (s + 1)) (x : M) (m : Fin (s + 2) → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ (s + 2) (tsLoweredSlot0 (I := I) (M := M) g₀ s Z) x m =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace (s + 1) I x from Z.toSection x)
          (g0FlatCLM (I := I) g₀ x (m 0)))
        (Matrix.vecTail m) := by
  classical
  rw [unitModel]
  rw [show ((tsLoweredSlot0 (I := I) (M := M) g₀ s Z).toSection x
        (unitTensor (I := I) (M := M) x)) =
      (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace (s + 2) I x from
        (slotExtend (I := I) (M := M) g₀ 1 (s + 1) Z).toSection x)
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
          (tsMetricCc (I := I) (M := M) g₀).toSection x)
          (unitTensor (I := I) (M := M) x)) from rfl]
  rw [tsMetricCc_toSection_unit (I := I) (M := M) g₀ x]
  rw [show ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace (s + 2) I x from
        (slotExtend (I := I) (M := M) g₀ 1 (s + 1) Z).toSection x)
        (tsMetricCovec (I := I) g₀ x)) =
      (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) (s + 1) x).symm
        ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace (s + 1) I x from Z.toSection x).comp
          ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x)
            (tsMetricCovec (I := I) g₀ x))) from rfl]
  rw [show m = Fin.cons (m 0) (Matrix.vecTail m) from by
    funext k
    refine Fin.cases rfl (fun j => rfl) k]
  have hkey := TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M) (n := s + 1)
    (T := (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) (s + 1) x).symm
      ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace (s + 1) I x from Z.toSection x).comp
        ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x) (tsMetricCovec (I := I) g₀ x))))
    (v0 := m 0) (vs := Matrix.vecTail (Fin.cons (m 0) (Matrix.vecTail m)))
  rw [ContinuousLinearEquiv.apply_symm_apply] at hkey
  rw [show (Fin.cons (m 0) (Matrix.vecTail (Fin.cons (m 0) (Matrix.vecTail m)))
        : Fin (s + 2) → TangentSpace I x) =
      Fin.cons (m 0) (Matrix.vecTail m) from by
    funext k
    refine Fin.cases rfl (fun j => rfl) k] at hkey
  rw [← hkey]
  rw [ContinuousLinearMap.comp_apply]
  rw [tsMetricCovec_curry_eq_flat (I := I) (M := M) g₀ x (m 0)]
  rw [show (Matrix.vecTail (Fin.cons (m 0) (Matrix.vecTail m))
        : Fin (s + 1) → TangentSpace I x) = Matrix.vecTail m from by
    funext k
    rfl]
  rfl

set_option linter.unusedSectionVars false in
lemma tsInteriorProduct_toModel_eval (s : ℕ) (x : M) (vv : TangentSpace I x)
    (D : Tensor0SSpace (s + 1) I x) (w : Fin s → TangentSpace I x) :
    Tensor0SSpace.toModel
        (Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) s x vv D) w =
      Tensor0SSpace.toModel D (Fin.cons (show E from vv) (fun k => (show E from w k))) := by
  have h1 : Tensor0SSpace.toModel
      (Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) s x vv D) =
      Tensor0SBundle.model_interior_product (𝕜 := ℝ) (E := E) s (show E from vv)
        (Tensor0SSpace.toModel D) := rfl
  rw [h1]
  rfl

set_option linter.unusedSectionVars false in
theorem tsLoweredSlot0_cometricRaise (g₀ : SmoothRiemannianMetric I M) (s : ℕ)
    (W : SmoothCcTensor g₀ 0 (s + 2)) :
    tsLoweredSlot0 (I := I) (M := M) g₀ s
        (cometricRaiseSlot0Field (I := I) (M := M) g₀ s W) = W := by
  classical
  apply smoothCcTensor_ext_of_unitModel (I := I) (M := M) g₀
  intro x
  apply ContinuousMultilinearMap.ext
  intro m
  rw [tsLoweredSlot0_unitModel_apply (I := I) (M := M) g₀ s
    (cometricRaiseSlot0Field (I := I) (M := M) g₀ s W) x m]
  rw [cometricRaiseSlot0Field_toSection (I := I) (M := M) g₀ s W x]
  rw [cometricRaiseSlot0Fib_clm_apply (I := I) g₀ s x
    ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 2) I x from W.toSection x)
      (unitTensor (I := I) (M := M) x))
    (g0FlatCLM (I := I) g₀ x (m 0))]
  rw [tsInteriorProduct_toModel_eval (I := I) (M := M) (s + 1) x
    (inverseMetricSharpFib (I := I) g₀ x (g0FlatCLM (I := I) g₀ x (m 0)))
    ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 2) I x from W.toSection x)
      (unitTensor (I := I) (M := M) x)) (Matrix.vecTail m)]
  rw [inverseMetricSharpFib_g0FlatCLM]
  rw [unitModel]
  refine congrArg _ ?_
  funext k
  refine Fin.cases rfl (fun j => rfl) k

set_option linter.unusedSectionVars false in
lemma tsExists_iteratedCovGrad_cometricRaiseSlot0Field (g₀ : SmoothRiemannianMetric I M)
    (s : ℕ) (W : SmoothCcTensor g₀ 0 (s + 2)) (i : ℕ) :
    ∃ σ : Equiv.Perm (Fin ((s + i) + 2)),
      iteratedCovGrad (I := I) g₀ 1 (s + 1) i
          (cometricRaiseSlot0Field (I := I) (M := M) g₀ s W) =
        castRankCc_db g₀ 1 (by omega : (s + i) + 1 = (s + 1) + i)
          (cometricRaiseSlot0Field (I := I) (M := M) g₀ (s + i)
            (domDomCongrSection (I := I) g₀ σ
              (castRankCc_db g₀ 0 (by omega : (s + 2) + i = (s + i) + 2)
                (iteratedCovGrad (I := I) g₀ 0 (s + 2) i W)))) := by
  induction i with
  | zero =>
      refine ⟨Equiv.refl _, ?_⟩
      rw [iteratedCovGrad_zero, iteratedCovGrad_zero]
      rw [show (castRankCc_db g₀ 0 (by omega : (s + 2) + 0 = (s + 0) + 2) W) = W from rfl]
      rw [tsDomDomCongrSection_refl (I := I) (M := M) g₀ W]
      rfl
  | succ i ih =>
      obtain ⟨σ, hσ⟩ := ih
      obtain ⟨σ', hσ'⟩ := tsExists_covGrad_domDomCongrSection (I := I) (M := M) g₀ σ
        (castRankCc_db g₀ 0 (by omega : (s + 2) + i = (s + i) + 2)
          (iteratedCovGrad (I := I) g₀ 0 (s + 2) i W))
      refine ⟨σ'.trans (Equiv.swap (0 : Fin ((s + i) + 2 + 1)) 1), ?_⟩
      rw [iteratedCovGrad_succ, hσ]
      rw [tsCovGrad_castRankCc_db (I := I) (M := M) g₀ 1
        (by omega : (s + i) + 1 = (s + 1) + i)]
      rw [covGrad_cometricRaiseSlot0Field_eq (I := I) (M := M) g₀ (s + i)]
      rw [hσ']
      rw [tsDomDomCongrSection_comp (I := I) (M := M) g₀ σ'
        (Equiv.swap (0 : Fin ((s + i) + 2 + 1)) 1)]
      rw [tsCovGrad_castRankCc_db (I := I) (M := M) g₀ 0
        (by omega : (s + 2) + i = (s + i) + 2)]
      rw [← iteratedCovGrad_succ]
      rfl

end CurvatureCoefficientDifferenceJetTower

end TsMetricLowering

section TsHeadTransport

open DifferentialGeometry.Integral.DivergenceTheorem

set_option backward.isDefEq.respectTransparency false

namespace CurvatureCoefficientDifferenceJetTower

set_option linter.unusedSectionVars false in
lemma tsRfns_order_congr (g : SmoothRiemannianMetric I M)
    (r s : ℕ) {n n' : ℕ} (h : n = n') (S : SmoothCcTensor g r s) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g r (s + n) x
        ((iteratedCovGrad (I := I) g r s n S).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g r (s + n') x
        ((iteratedCovGrad (I := I) g r s n' S).toSection x) := by
  subst h; rfl

set_option linter.unusedSectionVars false in
lemma tsRfns_domDomCongrSection_zero (g₀ : SmoothRiemannianMetric I M) {s : ℕ}
    (σ : Equiv.Perm (Fin s)) (S : SmoothCcTensor g₀ 0 s) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 0 s x
        ((domDomCongrSection (I := I) g₀ σ S).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 s x (S.toSection x) := by
  have h := riemannianFiberNormSq_iteratedCovGrad_domDomCongrSection (I := I) (M := M)
    g₀ σ S 0 x
  rw [iteratedCovGrad_zero, iteratedCovGrad_zero] at h
  exact h

set_option linter.unusedSectionVars false in
lemma tsRfns_castRankCc_db_zero (g₀ : SmoothRiemannianMetric I M) (r : ℕ) {a b : ℕ}
    (h : a = b) (W : SmoothCcTensor g₀ r a) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ r b x
        ((castRankCc_db g₀ r h W).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g₀ r a x (W.toSection x) := by
  subst h; rfl

set_option linter.unusedSectionVars false in
lemma tsSlotExtend_sub (g₀ : SmoothRiemannianMetric I M) (r s : ℕ)
    (X X' : SmoothCcTensor g₀ r s) :
    slotExtend (I := I) (M := M) g₀ r s (X - X') =
      slotExtend (I := I) (M := M) g₀ r s X - slotExtend (I := I) (M := M) g₀ r s X' := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [show ((slotExtend (I := I) (M := M) g₀ r s X -
        slotExtend (I := I) (M := M) g₀ r s X').toSection x) =
      (slotExtend (I := I) (M := M) g₀ r s X).toSection x -
        (slotExtend (I := I) (M := M) g₀ r s X').toSection x from by
    rw [SmoothCcTensor.toSection_sub]; rfl]
  rw [slotExtend_toSection, slotExtend_toSection, slotExtend_toSection]
  have e0 : (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from (X - X').toSection x) =
      (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from X.toSection x) -
        (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from X'.toSection x) := by
    rw [SmoothCcTensor.toSection_sub]; rfl
  apply ContinuousLinearMap.ext
  intro D
  rw [show ((show Tensor0SSpace (r + 1) I x →L[ℝ] Tensor0SSpace (s + 1) I x from
        (show TensorRSSpace (r + 1) (s + 1) I x from
          slotExtendFib (I := I) (M := M) g₀ r s x
            (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from X.toSection x)) -
        (show TensorRSSpace (r + 1) (s + 1) I x from
          slotExtendFib (I := I) (M := M) g₀ r s x
            (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from X'.toSection x))) D) =
      (show Tensor0SSpace (r + 1) I x →L[ℝ] Tensor0SSpace (s + 1) I x from
        slotExtendFib (I := I) (M := M) g₀ r s x
          (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from X.toSection x)) D -
      (show Tensor0SSpace (r + 1) I x →L[ℝ] Tensor0SSpace (s + 1) I x from
        slotExtendFib (I := I) (M := M) g₀ r s x
          (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from X'.toSection x)) D from rfl]
  rw [show ((show Tensor0SSpace (r + 1) I x →L[ℝ] Tensor0SSpace (s + 1) I x from
        slotExtendFib (I := I) (M := M) g₀ r s x
          (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from (X - X').toSection x)) D) =
      (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x).symm
        ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from (X - X').toSection x).comp
          ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) r x) D)) from rfl]
  rw [e0, ContinuousLinearMap.sub_comp, map_sub]
  rfl

set_option linter.unusedSectionVars false in
lemma tsAppCc_sub_left (g₀ : SmoothRiemannianMetric I M) (r s : ℕ)
    (Φ Φ' : SmoothCcTensor g₀ r s) (W : SmoothCcTensor g₀ 0 r) :
    appCc (I := I) (M := M) g₀ r s (Φ - Φ') W =
      appCc (I := I) (M := M) g₀ r s Φ W - appCc (I := I) (M := M) g₀ r s Φ' W := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [show ((appCc (I := I) (M := M) g₀ r s Φ W -
        appCc (I := I) (M := M) g₀ r s Φ' W).toSection x) =
      (appCc (I := I) (M := M) g₀ r s Φ W).toSection x -
        (appCc (I := I) (M := M) g₀ r s Φ' W).toSection x from by
    rw [SmoothCcTensor.toSection_sub]; rfl]
  rw [appCc_toSection, appCc_toSection, appCc_toSection]
  rw [show ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from (Φ - Φ').toSection x)) =
      (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from Φ.toSection x) -
        (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from Φ'.toSection x) from by
    rw [SmoothCcTensor.toSection_sub]; rfl]
  rw [ContinuousLinearMap.sub_comp]

set_option linter.unusedSectionVars false in
lemma tsRsDomDomCongr_sub {r s : ℕ} {x : M} (σ : Equiv.Perm (Fin s))
    (T T' : TensorRSSpace r s I x) :
    rsDomDomCongr (I := I) (M := M) σ (T - T') =
      rsDomDomCongr (I := I) (M := M) σ T - rsDomDomCongr (I := I) (M := M) σ T' := by
  apply ContinuousLinearMap.ext
  intro d
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro v
  have hL := congrArg (fun f => f v)
    (toModel_rsDomDomCongr_apply (I := I) (M := M) σ (T - T') d)
  refine hL.trans ?_
  have e1 : ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from T - T') d) =
      (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from T) d -
        (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from T') d := rfl
  have e2 : ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from
        rsDomDomCongr (I := I) (M := M) σ T - rsDomDomCongr (I := I) (M := M) σ T') d) =
      (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from
          rsDomDomCongr (I := I) (M := M) σ T) d -
        (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from
          rsDomDomCongr (I := I) (M := M) σ T') d := rfl
  have h1 : Tensor0SSpace.toModel
      ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from
        rsDomDomCongr (I := I) (M := M) σ T) d) v =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from T) d)
        (fun k => v (σ k)) := by
    have := congrArg (fun f => f v) (toModel_rsDomDomCongr_apply (I := I) (M := M) σ T d)
    refine this.trans ?_
    simp only [ContinuousMultilinearMap.domDomCongr_apply]
  have h2 : Tensor0SSpace.toModel
      ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from
        rsDomDomCongr (I := I) (M := M) σ T') d) v =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from T') d)
        (fun k => v (σ k)) := by
    have := congrArg (fun f => f v) (toModel_rsDomDomCongr_apply (I := I) (M := M) σ T' d)
    refine this.trans ?_
    simp only [ContinuousMultilinearMap.domDomCongr_apply]
  calc ContinuousMultilinearMap.domDomCongr σ
        (Tensor0SSpace.toModel
          ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from T - T') d)) v
      = Tensor0SSpace.toModel
          ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from T - T') d)
          (fun k => v (σ k)) := by
        simp only [ContinuousMultilinearMap.domDomCongr_apply]
    _ = Tensor0SSpace.toModel
          ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from T) d -
            (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from T') d)
          (fun k => v (σ k)) := by rw [e1]
    _ = Tensor0SSpace.toModel
          ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from T) d)
          (fun k => v (σ k)) -
        Tensor0SSpace.toModel
          ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from T') d)
          (fun k => v (σ k)) := by
        rw [Tensor0SSpace.toModel_sub]
        simp only [ContinuousMultilinearMap.sub_apply]
    _ = Tensor0SSpace.toModel
          ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from
            rsDomDomCongr (I := I) (M := M) σ T) d) v -
        Tensor0SSpace.toModel
          ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from
            rsDomDomCongr (I := I) (M := M) σ T') d) v := by rw [h1, h2]
    _ = Tensor0SSpace.toModel
          ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from
            rsDomDomCongr (I := I) (M := M) σ T -
              rsDomDomCongr (I := I) (M := M) σ T') d) v := by
        rw [e2, Tensor0SSpace.toModel_sub]
        simp only [ContinuousMultilinearMap.sub_apply]

set_option linter.unusedSectionVars false in
lemma tsExists_loweredPair_headTransport (g₀ : SmoothRiemannianMetric I M)
    (σ₀ : Equiv.Perm (Fin (2 + 2)))
    (Y : SmoothCcTensor g₀ 1 (2 + 1)) (i : ℕ) (HY : SmoothCcTensor g₀ 1 ((2 + 1) + i)) :
    ∃ Hd : SmoothCcTensor g₀ 0 ((2 + 2) + i), ∀ x : M,
      (riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((2 + 2) + i) x (Hd.toSection x) ≤
        (Module.finrank ℝ E : ℝ) *
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x
            ((tsMetricCc (I := I) (M := M) g₀).toSection x) *
          riemannianFiberNormSq (I := I) (M := M) g₀ 1 ((2 + 1) + i) x (HY.toSection x)) ∧
      (riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((2 + 2) + i) x
          ((iteratedCovGrad (I := I) g₀ 0 (2 + 2) i
              (domDomCongrSection (I := I) g₀ σ₀
                (tsLoweredSlot0 (I := I) (M := M) g₀ 2 Y)) - Hd).toSection x) ≤
        2 * ((Module.finrank ℝ E : ℝ) *
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x
              ((tsMetricCc (I := I) (M := M) g₀).toSection x) *
            riemannianFiberNormSq (I := I) (M := M) g₀ 1 ((2 + 1) + i) x
              ((iteratedCovGrad (I := I) g₀ 1 (2 + 1) i Y - HY).toSection x)) +
        2 * ((i : ℝ) * appCcGdiag (E := E) i *
            ∑ k ∈ Finset.range i,
              ((Module.finrank ℝ E : ℝ) *
                riemannianFiberNormSq (I := I) (M := M) g₀ 1 ((2 + 1) + (i - (k + 1))) x
                  ((iteratedCovGrad (I := I) g₀ 1 (2 + 1) (i - (k + 1)) Y).toSection x)) *
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (k + 1)) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (k + 1)
                  (tsMetricCc (I := I) (M := M) g₀)).toSection x))) := by
  classical
  obtain ⟨σ₂, hσ₂⟩ := exists_iteratedCovGrad_slotExtend_rsDomDomCongr (I := I) (M := M)
    g₀ 1 (2 + 1) Y i
  obtain ⟨σ₁, hσ₁⟩ := tsExists_iteratedCovGrad_domDomCongrSection (I := I) (M := M) g₀
    σ₀ (tsLoweredSlot0 (I := I) (M := M) g₀ 2 Y) i
  set n : ℝ := (Module.finrank ℝ E : ℝ) with hn_def
  set gW : SmoothCcTensor g₀ 0 2 := tsMetricCc (I := I) (M := M) g₀ with hgW_def
  set TransHead : SmoothCcTensor g₀ (1 + 1) (((2 + 1) + 1) + i) :=
    rsDomDomCongrSection (I := I) (M := M) g₀ (1 + 1) (((2 + 1) + 1) + i) σ₂
      (castRankCc_db g₀ (1 + 1) (by omega : (((2 + 1) + i) + 1) = ((2 + 1) + 1) + i)
        (slotExtend (I := I) (M := M) g₀ 1 ((2 + 1) + i) HY)) with hTransHead_def
  refine ⟨domDomCongrSection (I := I) g₀ σ₁
    (appCc (I := I) (M := M) g₀ 2 ((2 + 2) + i) TransHead gW), fun x => ?_⟩
  have hgW_nn : 0 ≤ riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x (gW.toSection x) :=
    riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 2 x _
  have hn_nn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hTransHead_rfns : ∀ (V : SmoothCcTensor g₀ 1 ((2 + 1) + i)),
      riemannianFiberNormSq (I := I) (M := M) g₀ (1 + 1) (((2 + 1) + 1) + i) x
        ((rsDomDomCongrSection (I := I) (M := M) g₀ (1 + 1) (((2 + 1) + 1) + i) σ₂
          (castRankCc_db g₀ (1 + 1) (by omega : (((2 + 1) + i) + 1) = ((2 + 1) + 1) + i)
            (slotExtend (I := I) (M := M) g₀ 1 ((2 + 1) + i) V))).toSection x) =
      n * riemannianFiberNormSq (I := I) (M := M) g₀ 1 ((2 + 1) + i) x (V.toSection x) := by
    intro V
    rw [rsDomDomCongrSection_toSection]
    rw [riemannianFiberNormSq_domDomCongr_covariant (I := I) (M := M) g₀ (1 + 1)
      (((2 + 1) + 1) + i) x σ₂ _]
    rw [tsRfns_castRankCc_db_zero (I := I) (M := M) g₀ (1 + 1)
      (by omega : (((2 + 1) + i) + 1) = ((2 + 1) + 1) + i)
      (slotExtend (I := I) (M := M) g₀ 1 ((2 + 1) + i) V) x]
    rw [rfns_slotExtend_eq (I := I) (M := M) g₀ 1 ((2 + 1) + i) V x]
  constructor
  · rw [tsRfns_domDomCongrSection_zero (I := I) (M := M) g₀ σ₁ _ x]
    rw [appCc_toSection]
    refine le_trans (riemannianFiberNormSq_compRS_le_mul (I := I) (M := M) g₀ 0 2
      ((2 + 2) + i) x
      (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace ((2 + 2) + i) I x from
        TransHead.toSection x)
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from gW.toSection x)) ?_
    rw [hTransHead_def, hTransHead_rfns HY]
    exact le_of_eq (by ring)
  · have hcorner := iteratedCovGrad_appCc_eq_coeffCorner_add_lower (I := I) (M := M) g₀ 2
      (2 + 2) (slotExtend (I := I) (M := M) g₀ 1 (2 + 1) Y) gW i
    have hlow : tsLoweredSlot0 (I := I) (M := M) g₀ 2 Y =
        appCc (I := I) (M := M) g₀ 2 (2 + 2)
          (slotExtend (I := I) (M := M) g₀ 1 (2 + 1) Y) gW := rfl
    have hsplit : iteratedCovGrad (I := I) g₀ 0 (2 + 2) i
          (domDomCongrSection (I := I) g₀ σ₀
            (tsLoweredSlot0 (I := I) (M := M) g₀ 2 Y)) -
          domDomCongrSection (I := I) g₀ σ₁
            (appCc (I := I) (M := M) g₀ 2 ((2 + 2) + i) TransHead gW) =
        domDomCongrSection (I := I) g₀ σ₁
          (appCc (I := I) (M := M) g₀ 2 ((2 + 2) + i)
              (iteratedCovGrad (I := I) g₀ 2 (2 + 2) i
                (slotExtend (I := I) (M := M) g₀ 1 (2 + 1) Y) - TransHead) gW +
            ∑ k ∈ Finset.range i,
              appCcRS (I := I) (M := M) g₀ 0 (2 + (k + 1)) ((2 + 2) + i)
                (appCcLeibnizPsi (I := I) (M := M) g₀ 2 (2 + 2)
                  (slotExtend (I := I) (M := M) g₀ 1 (2 + 1) Y) i (k + 1))
                (iteratedCovGrad (I := I) g₀ 0 2 (k + 1) gW)) := by
      rw [hσ₁, hlow, hcorner]
      rw [← tsDomDomCongrSection_sub (I := I) (M := M) g₀ σ₁]
      refine congrArg (fun Z => domDomCongrSection (I := I) g₀ σ₁ Z) ?_
      rw [tsAppCc_sub_left (I := I) (M := M) g₀ 2 ((2 + 2) + i) _ TransHead gW]
      rw [add_sub_right_comm]
    rw [hsplit]
    rw [tsRfns_domDomCongrSection_zero (I := I) (M := M) g₀ σ₁ _ x]
    rw [show (((appCc (I := I) (M := M) g₀ 2 ((2 + 2) + i)
          (iteratedCovGrad (I := I) g₀ 2 (2 + 2) i
            (slotExtend (I := I) (M := M) g₀ 1 (2 + 1) Y) - TransHead) gW +
        ∑ k ∈ Finset.range i,
          appCcRS (I := I) (M := M) g₀ 0 (2 + (k + 1)) ((2 + 2) + i)
            (appCcLeibnizPsi (I := I) (M := M) g₀ 2 (2 + 2)
              (slotExtend (I := I) (M := M) g₀ 1 (2 + 1) Y) i (k + 1))
            (iteratedCovGrad (I := I) g₀ 0 2 (k + 1) gW)).toSection x)) =
        (appCc (I := I) (M := M) g₀ 2 ((2 + 2) + i)
          (iteratedCovGrad (I := I) g₀ 2 (2 + 2) i
            (slotExtend (I := I) (M := M) g₀ 1 (2 + 1) Y) - TransHead) gW).toSection x +
        (∑ k ∈ Finset.range i,
          appCcRS (I := I) (M := M) g₀ 0 (2 + (k + 1)) ((2 + 2) + i)
            (appCcLeibnizPsi (I := I) (M := M) g₀ 2 (2 + 2)
              (slotExtend (I := I) (M := M) g₀ 1 (2 + 1) Y) i (k + 1))
            (iteratedCovGrad (I := I) g₀ 0 2 (k + 1) gW)).toSection x from by
      rw [SmoothCcTensor.toSection_add]; rfl]
    refine le_trans (riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 0 ((2 + 2) + i) x _ _) ?_
    have hA : riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((2 + 2) + i) x
        ((appCc (I := I) (M := M) g₀ 2 ((2 + 2) + i)
          (iteratedCovGrad (I := I) g₀ 2 (2 + 2) i
            (slotExtend (I := I) (M := M) g₀ 1 (2 + 1) Y) - TransHead) gW).toSection x) ≤
        n * riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x (gW.toSection x) *
          riemannianFiberNormSq (I := I) (M := M) g₀ 1 ((2 + 1) + i) x
            ((iteratedCovGrad (I := I) g₀ 1 (2 + 1) i Y - HY).toSection x) := by
      rw [appCc_toSection]
      refine le_trans (riemannianFiberNormSq_compRS_le_mul (I := I) (M := M) g₀ 0 2
        ((2 + 2) + i) x _ _) ?_
      have hD : riemannianFiberNormSq (I := I) (M := M) g₀ 2 ((2 + 2) + i) x
          ((iteratedCovGrad (I := I) g₀ 2 (2 + 2) i
            (slotExtend (I := I) (M := M) g₀ 1 (2 + 1) Y) - TransHead).toSection x) =
          n * riemannianFiberNormSq (I := I) (M := M) g₀ 1 ((2 + 1) + i) x
            ((iteratedCovGrad (I := I) g₀ 1 (2 + 1) i Y - HY).toSection x) := by
        rw [show ((iteratedCovGrad (I := I) g₀ 2 (2 + 2) i
              (slotExtend (I := I) (M := M) g₀ 1 (2 + 1) Y) - TransHead).toSection x) =
            (iteratedCovGrad (I := I) g₀ 2 (2 + 2) i
              (slotExtend (I := I) (M := M) g₀ 1 (2 + 1) Y)).toSection x -
              TransHead.toSection x from by
          rw [SmoothCcTensor.toSection_sub]; rfl]
        rw [hσ₂ x]
        rw [hTransHead_def, rsDomDomCongrSection_toSection]
        rw [← tsRsDomDomCongr_sub (I := I) (M := M) σ₂]
        rw [riemannianFiberNormSq_domDomCongr_covariant (I := I) (M := M) g₀ (1 + 1)
          (((2 + 1) + 1) + i) x σ₂ _]
        rw [show ((castRankCc_db g₀ (1 + 1)
              (by omega : (((2 + 1) + i) + 1) = ((2 + 1) + 1) + i)
              (slotExtend (I := I) (M := M) g₀ 1 ((2 + 1) + i)
                (iteratedCovGrad (I := I) g₀ 1 (2 + 1) i Y))).toSection x -
            (castRankCc_db g₀ (1 + 1)
              (by omega : (((2 + 1) + i) + 1) = ((2 + 1) + 1) + i)
              (slotExtend (I := I) (M := M) g₀ 1 ((2 + 1) + i) HY)).toSection x) =
            ((castRankCc_db g₀ (1 + 1)
              (by omega : (((2 + 1) + i) + 1) = ((2 + 1) + 1) + i)
              (slotExtend (I := I) (M := M) g₀ 1 ((2 + 1) + i)
                  (iteratedCovGrad (I := I) g₀ 1 (2 + 1) i Y) -
                slotExtend (I := I) (M := M) g₀ 1 ((2 + 1) + i) HY)).toSection x) from by
          rw [tsCastRankCc_db_sub, SmoothCcTensor.toSection_sub]; rfl]
        rw [← tsSlotExtend_sub (I := I) (M := M) g₀ 1 ((2 + 1) + i)]
        rw [tsRfns_castRankCc_db_zero (I := I) (M := M) g₀ (1 + 1)
          (by omega : (((2 + 1) + i) + 1) = ((2 + 1) + 1) + i) _ x]
        rw [rfns_slotExtend_eq (I := I) (M := M) g₀ 1 ((2 + 1) + i) _ x]
      rw [hD]
      have hgWx := riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 2 x (gW.toSection x)
      have hYd := riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 1 ((2 + 1) + i) x
        ((iteratedCovGrad (I := I) g₀ 1 (2 + 1) i Y - HY).toSection x)
      exact le_of_eq (by ring)
    have tsCorrTerm_le : ∀ k ∈ Finset.range i,
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((2 + 2) + i) x
          ((appCcRS (I := I) (M := M) g₀ 0 (2 + (k + 1)) ((2 + 2) + i)
            (appCcLeibnizPsi (I := I) (M := M) g₀ 2 (2 + 2)
              (slotExtend (I := I) (M := M) g₀ 1 (2 + 1) Y) i (k + 1))
            (iteratedCovGrad (I := I) g₀ 0 2 (k + 1) gW)).toSection x) ≤
        appCcGdiag (E := E) i *
          ((n * riemannianFiberNormSq (I := I) (M := M) g₀ 1
              ((2 + 1) + (i - (k + 1))) x
              ((iteratedCovGrad (I := I) g₀ 1 (2 + 1) (i - (k + 1)) Y).toSection x)) *
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (k + 1)) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (k + 1) gW).toSection x)) := by
      intro k hk
      have hk_le : k + 1 ≤ i := by
        rw [Finset.mem_range] at hk; omega
      rw [appCcRS_toSection]
      refine le_trans (riemannianFiberNormSq_compRS_le_mul (I := I) (M := M) g₀ 0
        (2 + (k + 1)) ((2 + 2) + i) x _ _) ?_
      have hΨ : riemannianFiberNormSq (I := I) (M := M) g₀ (2 + (k + 1)) ((2 + 2) + i) x
          ((appCcLeibnizPsi (I := I) (M := M) g₀ 2 (2 + 2)
            (slotExtend (I := I) (M := M) g₀ 1 (2 + 1) Y) i (k + 1)).toSection x) ≤
          appCcGdiag (E := E) i *
            (n * riemannianFiberNormSq (I := I) (M := M) g₀ 1
              ((2 + 1) + (i - (k + 1))) x
              ((iteratedCovGrad (I := I) g₀ 1 (2 + 1) (i - (k + 1)) Y).toSection x)) := by
        have hw := rfns_iteratedCovGrad_appCcLeibnizPsi_window_le (I := I) (M := M) g₀ 2
          (2 + 2) (slotExtend (I := I) (M := M) g₀ 1 (2 + 1) Y) i (k + 1) 0 hk_le x
        rw [iteratedCovGrad_zero] at hw
        rw [tsRfns_order_congr (I := I) (M := M) g₀ 2 (2 + 2)
          (show (i - (k + 1)) + 0 = i - (k + 1) from by omega)
          (slotExtend (I := I) (M := M) g₀ 1 (2 + 1) Y) x] at hw
        refine le_trans hw ?_
        exact mul_le_mul_of_nonneg_left
          (rfns_iteratedCovGrad_slotExtend_le (I := I) (M := M) g₀ 1 (2 + 1)
            Y (i - (k + 1)) x)
          (appCcGdiag_nonneg (E := E) i)
      refine le_trans (mul_le_mul_of_nonneg_right hΨ
        (riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + (k + 1)) x _)) ?_
      exact le_of_eq (by ring)
    have hB : riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((2 + 2) + i) x
        ((∑ k ∈ Finset.range i,
          appCcRS (I := I) (M := M) g₀ 0 (2 + (k + 1)) ((2 + 2) + i)
            (appCcLeibnizPsi (I := I) (M := M) g₀ 2 (2 + 2)
              (slotExtend (I := I) (M := M) g₀ 1 (2 + 1) Y) i (k + 1))
            (iteratedCovGrad (I := I) g₀ 0 2 (k + 1) gW)).toSection x) ≤
        (i : ℝ) * appCcGdiag (E := E) i *
          ∑ k ∈ Finset.range i,
            (n * riemannianFiberNormSq (I := I) (M := M) g₀ 1 ((2 + 1) + (i - (k + 1))) x
              ((iteratedCovGrad (I := I) g₀ 1 (2 + 1) (i - (k + 1)) Y).toSection x)) *
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (k + 1)) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (k + 1) gW).toSection x) := by
      rw [SmoothCcTensor.toSection_sum_apply]
      refine le_trans (riemannianFiberNormSq_sum_le_card_mul (I := I) (M := M) g₀ 0
        ((2 + 2) + i) x (Finset.range i) _) ?_
      rw [Finset.card_range]
      calc ((i : ℕ) : ℝ) * ∑ k ∈ Finset.range i,
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((2 + 2) + i) x
              ((appCcRS (I := I) (M := M) g₀ 0 (2 + (k + 1)) ((2 + 2) + i)
                (appCcLeibnizPsi (I := I) (M := M) g₀ 2 (2 + 2)
                  (slotExtend (I := I) (M := M) g₀ 1 (2 + 1) Y) i (k + 1))
                (iteratedCovGrad (I := I) g₀ 0 2 (k + 1) gW)).toSection x)
          ≤ ((i : ℕ) : ℝ) * ∑ k ∈ Finset.range i,
              appCcGdiag (E := E) i *
                ((n * riemannianFiberNormSq (I := I) (M := M) g₀ 1
                    ((2 + 1) + (i - (k + 1))) x
                    ((iteratedCovGrad (I := I) g₀ 1 (2 + 1) (i - (k + 1)) Y).toSection x)) *
                  riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (k + 1)) x
                    ((iteratedCovGrad (I := I) g₀ 0 2 (k + 1) gW).toSection x)) := by
            refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun k hk => ?_))
              (Nat.cast_nonneg i)
            exact tsCorrTerm_le k hk
        _ = (i : ℝ) * appCcGdiag (E := E) i *
              ∑ k ∈ Finset.range i,
                (n * riemannianFiberNormSq (I := I) (M := M) g₀ 1
                  ((2 + 1) + (i - (k + 1))) x
                  ((iteratedCovGrad (I := I) g₀ 1 (2 + 1) (i - (k + 1)) Y).toSection x)) *
                riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (k + 1)) x
                  ((iteratedCovGrad (I := I) g₀ 0 2 (k + 1) gW).toSection x) := by
            rw [Finset.mul_sum, Finset.mul_sum]
            refine Finset.sum_congr rfl (fun k _ => by ring)
    calc 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((2 + 2) + i) x
            ((appCc (I := I) (M := M) g₀ 2 ((2 + 2) + i)
              (iteratedCovGrad (I := I) g₀ 2 (2 + 2) i
                (slotExtend (I := I) (M := M) g₀ 1 (2 + 1) Y) - TransHead) gW).toSection x) +
          2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((2 + 2) + i) x
            ((∑ k ∈ Finset.range i,
              appCcRS (I := I) (M := M) g₀ 0 (2 + (k + 1)) ((2 + 2) + i)
                (appCcLeibnizPsi (I := I) (M := M) g₀ 2 (2 + 2)
                  (slotExtend (I := I) (M := M) g₀ 1 (2 + 1) Y) i (k + 1))
                (iteratedCovGrad (I := I) g₀ 0 2 (k + 1) gW)).toSection x)
        ≤ 2 * (n * riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x (gW.toSection x) *
              riemannianFiberNormSq (I := I) (M := M) g₀ 1 ((2 + 1) + i) x
                ((iteratedCovGrad (I := I) g₀ 1 (2 + 1) i Y - HY).toSection x)) +
            2 * ((i : ℝ) * appCcGdiag (E := E) i *
              ∑ k ∈ Finset.range i,
                (n * riemannianFiberNormSq (I := I) (M := M) g₀ 1
                  ((2 + 1) + (i - (k + 1))) x
                  ((iteratedCovGrad (I := I) g₀ 1 (2 + 1) (i - (k + 1)) Y).toSection x)) *
                riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (k + 1)) x
                  ((iteratedCovGrad (I := I) g₀ 0 2 (k + 1) gW).toSection x)) := by
          have h2 : (0 : ℝ) ≤ 2 := by norm_num
          exact add_le_add (mul_le_mul_of_nonneg_left hA h2)
            (mul_le_mul_of_nonneg_left hB h2)
      _ = _ := by rw [hgW_def, hn_def]

end CurvatureCoefficientDifferenceJetTower

end TsHeadTransport

section TsCarrierSplit

set_option backward.isDefEq.respectTransparency false

namespace CurvatureCoefficientDifferenceJetTower

set_option linter.unusedSectionVars false in
lemma tsConnDiff_carrier_split (g₀ g₁ : SmoothRiemannianMetric I M) (j : ℕ) :
    iteratedCovGrad (I := I) g₀ 1 2 j (connDiffSection (I := I) g₁ g₀) =
      appCcRS (I := I) (M := M) g₀ 1 1 (2 + j)
          (iteratedCovGrad (I := I) g₀ 1 2 j (raisedKoszul (I := I) g₀ g₁))
          (sharpFlatEndoCc (I := I) g₀ g₁) +
        ∑ k ∈ Finset.range j,
          appCcRS (I := I) (M := M) g₀ 1 (1 + (k + 1)) (2 + j)
            (appCcLeibnizPsi (I := I) (M := M) g₀ 1 2 (raisedKoszul (I := I) g₀ g₁) j (k + 1))
            (iteratedCovGrad (I := I) g₀ 1 1 (k + 1) (sharpFlatEndoCc (I := I) g₀ g₁)) := by
  rw [connDiffSection_eq_appCcRS_raisedKoszul_sharpFlatEndoCc (I := I) (M := M) g₀ g₁]
  rw [iteratedCovGrad_appCcRS_eq (I := I) (M := M) g₀ 1 1 2
    (raisedKoszul (I := I) g₀ g₁) (sharpFlatEndoCc (I := I) g₀ g₁) j]
  rw [Finset.sum_range_succ' (fun k =>
    appCcRS (I := I) (M := M) g₀ 1 (1 + k) (2 + j)
      (appCcLeibnizPsi (I := I) (M := M) g₀ 1 2 (raisedKoszul (I := I) g₀ g₁) j k)
      (iteratedCovGrad (I := I) g₀ 1 1 k (sharpFlatEndoCc (I := I) g₀ g₁))) j]
  have hf0 : appCcRS (I := I) (M := M) g₀ 1 (1 + 0) (2 + j)
      (appCcLeibnizPsi (I := I) (M := M) g₀ 1 2 (raisedKoszul (I := I) g₀ g₁) j 0)
      (iteratedCovGrad (I := I) g₀ 1 1 0 (sharpFlatEndoCc (I := I) g₀ g₁)) =
      appCcRS (I := I) (M := M) g₀ 1 1 (2 + j)
        (iteratedCovGrad (I := I) g₀ 1 2 j (raisedKoszul (I := I) g₀ g₁))
        (sharpFlatEndoCc (I := I) g₀ g₁) :=
    congrArg (fun Z : SmoothCcTensor g₀ 1 (2 + j) =>
      appCcRS (I := I) (M := M) g₀ 1 1 (2 + j) Z (sharpFlatEndoCc (I := I) g₀ g₁))
      (appCcLeibnizPsi_zero_right_eq (I := I) (M := M) g₀ 1 2
        (raisedKoszul (I := I) g₀ g₁) j)
  rw [hf0]
  exact add_comm _ _

set_option linter.unusedSectionVars false in
lemma tsRfns_rsDomDomCongrSection_zero (g₀ : SmoothRiemannianMetric I M)
    (r s : ℕ) (σ : Equiv.Perm (Fin s)) (Z : SmoothCcTensor g₀ r s) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ r s x
        ((rsDomDomCongrSection (I := I) (M := M) g₀ r s σ Z).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g₀ r s x (Z.toSection x) := by
  rw [rsDomDomCongrSection_toSection]
  exact riemannianFiberNormSq_domDomCongr_covariant (I := I) (M := M) g₀ r s x σ _

set_option linter.unusedSectionVars false in
lemma tsRfns_iteratedCovGrad_rsDomDomCongrSection_eq
    (g₀ : SmoothRiemannianMetric I M) (r s : ℕ) (σ : Equiv.Perm (Fin s))
    (Z : SmoothCcTensor g₀ r s) (m : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ r (s + m) x
        ((iteratedCovGrad (I := I) g₀ r s m
          (rsDomDomCongrSection (I := I) (M := M) g₀ r s σ Z)).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g₀ r (s + m) x
        ((iteratedCovGrad (I := I) g₀ r s m Z).toSection x) :=
  rfns_iteratedCovGrad_rs_eq_of_section_domDomCongr (I := I) (M := M) g₀ r s σ Z
    (rsDomDomCongrSection (I := I) (M := M) g₀ r s σ Z)
    (fun y d => by
      rw [rsDomDomCongrSection_toSection, toModel_rsDomDomCongr_apply]) m x

end CurvatureCoefficientDifferenceJetTower

end TsCarrierSplit

end TopSeparatedTransportMirrors

section TopSeparatedRungRLD

open DifferentialGeometry.Integral.DivergenceTheorem

set_option backward.isDefEq.respectTransparency false

namespace CurvatureCoefficientDifferenceJetTower

lemma tsTgridSum_le_boundedWindow (b : ℕ → ℝ) (hb : ∀ j, 0 ≤ b j)
    {W₀ K W : ℕ} (hK : W₀ ≤ K + 1) (hW : W₀ ≤ W) :
    ∑ k ∈ Finset.range W₀, Combinatorics.antidiagonalTupleGrid b k ≤
      Combinatorics.boundedFactorGridWindow b K W := by
  calc ∑ k ∈ Finset.range W₀, Combinatorics.antidiagonalTupleGrid b k
      = ∑ k ∈ Finset.range W₀, Combinatorics.boundedFactorGrid b K k :=
        Finset.sum_congr rfl (fun k hk =>
          Combinatorics.antidiagonalTupleGrid_eq_boundedFactorGrid b
            (by rw [Finset.mem_range] at hk; omega))
    _ ≤ Combinatorics.boundedFactorGridWindow b K W := by
        rw [Combinatorics.boundedFactorGridWindow]
        refine Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.range_subset_range.mpr hW) ?_
        intro k _ _
        exact Combinatorics.boundedFactorGrid_nonneg b hb K k

lemma tsResSum_le_boundedWindow (b : ℕ → ℝ) (hb : ∀ j, 0 ≤ b j) (j : ℕ) :
    ∑ k ∈ Finset.range j, b (j - k) * Combinatorics.antidiagonalTupleGrid b (k + 1) ≤
      (j : ℝ) * Combinatorics.boundedFactorGridWindow b j (j + 2) := by
  calc ∑ k ∈ Finset.range j, b (j - k) * Combinatorics.antidiagonalTupleGrid b (k + 1)
      ≤ ∑ _k ∈ Finset.range j, Combinatorics.boundedFactorGridWindow b j (j + 2) := by
        refine Finset.sum_le_sum (fun k hk => ?_)
        rw [Finset.mem_range] at hk
        rw [Combinatorics.antidiagonalTupleGrid_eq_boundedFactorGrid b
          (show k + 1 ≤ j from by omega)]
        refine le_trans (Combinatorics.single_factor_mul_boundedFactorGrid_le b hb
          (k + 1) (j - k) (by omega) (by omega)) ?_
        rw [show (k + 1) + (j - k) = j + 1 from by omega]
        exact Combinatorics.boundedFactorGrid_le_boundedFactorGridWindow b hb (by omega)
    _ = (j : ℝ) * Combinatorics.boundedFactorGridWindow b j (j + 2) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

lemma tsRfns_sub_le (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (P Q : TensorRSSpace r s I x) :
    riemannianFiberNormSq (I := I) (M := M) g r s x (P - Q) ≤
      2 * riemannianFiberNormSq (I := I) (M := M) g r s x P +
        2 * riemannianFiberNormSq (I := I) (M := M) g r s x Q := by
  have h1 := riemannianFiberNormSq_add_le (I := I) (M := M) g r s x P (-Q)
  have h2 := rfns_neg_pt (I := I) (M := M) g r s x Q
  rw [h2] at h1
  rw [sub_eq_add_neg]
  exact h1

set_option linter.unusedVariables false in
theorem tsExists_quad_jets (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ}
    (hδ₀ : δ₀ < 1) :
    ∃ KQ : ℕ → ℝ, (∀ m, 0 ≤ KQ m) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
        (hbound : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        (m : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 1 (3 + m) x
            ((iteratedCovGrad (I := I) g₀ 1 3 m
              (quadraticConnDiffCc (I := I) (M := M) g₀ g₁)).toSection x) ≤
          KQ m * Combinatorics.boundedFactorGridWindow
            (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
              ((iteratedCovGrad (I := I) g₀ 0 2 l T).toSection x)) (m + 1) (m + 3) := by
  classical
  obtain ⟨CA, hCA_nn, hCA⟩ := exists_rfns_iteratedCovGrad_connDiffSection_tgrid
    (I := I) (M := M) g₀ hδ₀
  refine ⟨fun m => appCcGdiag (E := E) m *
      ∑ a ∈ Finset.range (m + 1),
        ((Module.finrank ℝ E : ℝ) * CA a) *
          ((∑ l ∈ Finset.range (m + 1 - a), CA l) *
            Combinatorics.windowPairCellCount (a + 2) ((m - a) + 2)),
    fun m => mul_nonneg (appCcGdiag_nonneg (E := E) m)
      (Finset.sum_nonneg (fun a _ => mul_nonneg
        (mul_nonneg (Nat.cast_nonneg _) (hCA_nn a))
        (mul_nonneg (Finset.sum_nonneg (fun l _ => hCA_nn l))
          (Combinatorics.windowPairCellCount_nonneg _ _)))), ?_⟩
  intro g₁ T htie δ hδ_le hδ0 hbound m x
  set b : ℕ → ℝ := fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
    ((iteratedCovGrad (I := I) g₀ 0 2 l T).toSection x) with hb_def
  have hb : ∀ l, 0 ≤ b l :=
    fun l => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + l) x _
  set Wfin : ℝ := Combinatorics.boundedFactorGridWindow b (m + 1) (m + 3) with hWfin_def
  have hWfin_nn : 0 ≤ Wfin := Combinatorics.boundedFactorGridWindow_nonneg b hb (m + 1) (m + 3)
  have hquad : quadraticConnDiffCc (I := I) (M := M) g₀ g₁ =
      appCcRS (I := I) (M := M) g₀ 1 2 3
        (armSlotEndoPassZeroCc (I := I) (M := M) g₀
          (connDiffArmFieldPt (I := I) (M := M) g₀ g₁))
        (connDiffSection (I := I) g₁ g₀) := rfl
  rw [hquad]
  refine le_trans (rfns_iteratedCovGrad_appCcRS_diagonalProductGrid_rankLeft_le
    (I := I) (M := M) g₀ m 1 2 3
    (armSlotEndoPassZeroCc (I := I) (M := M) g₀
      (connDiffArmFieldPt (I := I) (M := M) g₀ g₁))
    (connDiffSection (I := I) g₁ g₀) x) ?_
  have hterm : ∀ a ∈ Finset.range (m + 1),
      riemannianFiberNormSq (I := I) (M := M) g₀ 2 (3 + a) x
          ((iteratedCovGrad (I := I) g₀ 2 3 a
            (armSlotEndoPassZeroCc (I := I) (M := M) g₀
              (connDiffArmFieldPt (I := I) (M := M) g₀ g₁))).toSection x) *
        (∑ l ∈ Finset.range (m + 1 - a),
          riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + l) x
            ((iteratedCovGrad (I := I) g₀ 1 2 l
              (connDiffSection (I := I) g₁ g₀)).toSection x)) ≤
      (((Module.finrank ℝ E : ℝ) * CA a) *
        ((∑ l ∈ Finset.range (m + 1 - a), CA l) *
          Combinatorics.windowPairCellCount (a + 2) ((m - a) + 2))) * Wfin := by
    intro a ha
    rw [Finset.mem_range] at ha
    have hΦ : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (3 + a) x
        ((iteratedCovGrad (I := I) g₀ 2 3 a
          (armSlotEndoPassZeroCc (I := I) (M := M) g₀
            (connDiffArmFieldPt (I := I) (M := M) g₀ g₁))).toSection x) ≤
        ((Module.finrank ℝ E : ℝ) * CA a) *
          Combinatorics.boundedFactorGridWindow b (m + 1) (a + 2) := by
      refine le_trans (rfns_iteratedCovGrad_armSlotPass_connDiffArm_le (I := I) (M := M)
        g₀ g₁ a x) ?_
      rw [mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
      refine le_trans (hCA g₁ T htie hδ_le hδ0 hbound a x) ?_
      refine mul_le_mul_of_nonneg_left ?_ (hCA_nn a)
      exact tsTgridSum_le_boundedWindow b hb (by omega) (by omega)
    have hW : (∑ l ∈ Finset.range (m + 1 - a),
        riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + l) x
          ((iteratedCovGrad (I := I) g₀ 1 2 l
            (connDiffSection (I := I) g₁ g₀)).toSection x)) ≤
        (∑ l ∈ Finset.range (m + 1 - a), CA l) *
          Combinatorics.boundedFactorGridWindow b (m + 1) ((m - a) + 2) := by
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum (fun l hl => ?_)
      rw [Finset.mem_range] at hl
      refine le_trans (hCA g₁ T htie hδ_le hδ0 hbound l x) ?_
      refine mul_le_mul_of_nonneg_left ?_ (hCA_nn l)
      exact tsTgridSum_le_boundedWindow b hb (by omega) (by omega)
    have hpair : Combinatorics.boundedFactorGridWindow b (m + 1) (a + 2) *
        Combinatorics.boundedFactorGridWindow b (m + 1) ((m - a) + 2) ≤
        Combinatorics.windowPairCellCount (a + 2) ((m - a) + 2) * Wfin := by
      refine le_trans (Combinatorics.boundedFactorGridWindow_mul_le b hb (m + 1)
        (a + 2) ((m - a) + 2) (by omega) (by omega)) ?_
      refine mul_le_mul_of_nonneg_left ?_ (Combinatorics.windowPairCellCount_nonneg _ _)
      rw [hWfin_def]
      refine Combinatorics.boundedFactorGridWindow_mono b hb (le_refl _) ?_
      omega
    calc riemannianFiberNormSq (I := I) (M := M) g₀ 2 (3 + a) x
            ((iteratedCovGrad (I := I) g₀ 2 3 a
              (armSlotEndoPassZeroCc (I := I) (M := M) g₀
                (connDiffArmFieldPt (I := I) (M := M) g₀ g₁))).toSection x) *
          (∑ l ∈ Finset.range (m + 1 - a),
            riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + l) x
              ((iteratedCovGrad (I := I) g₀ 1 2 l
                (connDiffSection (I := I) g₁ g₀)).toSection x))
        ≤ (((Module.finrank ℝ E : ℝ) * CA a) *
            Combinatorics.boundedFactorGridWindow b (m + 1) (a + 2)) *
          ((∑ l ∈ Finset.range (m + 1 - a), CA l) *
            Combinatorics.boundedFactorGridWindow b (m + 1) ((m - a) + 2)) := by
          refine mul_le_mul hΦ hW (Finset.sum_nonneg (fun l _ =>
            riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 1 (2 + l) x _)) ?_
          exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hCA_nn a))
            (Combinatorics.boundedFactorGridWindow_nonneg b hb _ _)
      _ = (((Module.finrank ℝ E : ℝ) * CA a) * (∑ l ∈ Finset.range (m + 1 - a), CA l)) *
            (Combinatorics.boundedFactorGridWindow b (m + 1) (a + 2) *
              Combinatorics.boundedFactorGridWindow b (m + 1) ((m - a) + 2)) := by ring
      _ ≤ (((Module.finrank ℝ E : ℝ) * CA a) * (∑ l ∈ Finset.range (m + 1 - a), CA l)) *
            (Combinatorics.windowPairCellCount (a + 2) ((m - a) + 2) * Wfin) := by
          refine mul_le_mul_of_nonneg_left hpair ?_
          exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hCA_nn a))
            (Finset.sum_nonneg (fun l _ => hCA_nn l))
      _ = (((Module.finrank ℝ E : ℝ) * CA a) *
            ((∑ l ∈ Finset.range (m + 1 - a), CA l) *
              Combinatorics.windowPairCellCount (a + 2) ((m - a) + 2))) * Wfin := by ring
  change appCcGdiag (E := E) m *
      (∑ a ∈ Finset.range (m + 1),
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (3 + a) x
            ((iteratedCovGrad (I := I) g₀ 2 3 a
              (armSlotEndoPassZeroCc (I := I) (M := M) g₀
                (connDiffArmFieldPt (I := I) (M := M) g₀ g₁))).toSection x) *
          ∑ l ∈ Finset.range (m + 1 - a),
            riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + l) x
              ((iteratedCovGrad (I := I) g₀ 1 2 l
                (connDiffSection (I := I) g₁ g₀)).toSection x)) ≤
    (appCcGdiag (E := E) m *
      ∑ a ∈ Finset.range (m + 1),
        ((Module.finrank ℝ E : ℝ) * CA a) *
          ((∑ l ∈ Finset.range (m + 1 - a), CA l) *
            Combinatorics.windowPairCellCount (a + 2) ((m - a) + 2))) * Wfin
  rw [mul_assoc, Finset.sum_mul]
  refine mul_le_mul_of_nonneg_left ?_ (appCcGdiag_nonneg (E := E) m)
  exact Finset.sum_le_sum hterm

set_option linter.unusedVariables false in
theorem tsExists_palatiniPair_jets (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ}
    (hδ₀ : δ₀ < 1) :
    ∃ KP : ℕ → ℝ, (∀ m, 0 ≤ KP m) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
        (hbound : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        (m : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 1 (3 + m) x
            ((iteratedCovGrad (I := I) g₀ 1 3 m
              (rsDomDomCongrSection (I := I) (M := M) g₀ 1 3 (Equiv.swap (1 : Fin 3) 2)
                  (covGrad (I := I) (M := M) g₀ 1 2 (connDiffSection (I := I) g₁ g₀) +
                    quadraticConnDiffCc (I := I) (M := M) g₀ g₁) -
                rsDomDomCongrSection (I := I) (M := M) g₀ 1 3 (finRotate 3)
                  (covGrad (I := I) (M := M) g₀ 1 2 (connDiffSection (I := I) g₁ g₀) +
                    quadraticConnDiffCc (I := I) (M := M) g₀ g₁))).toSection x) ≤
          KP m * Combinatorics.boundedFactorGridWindow
            (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
              ((iteratedCovGrad (I := I) g₀ 0 2 l T).toSection x)) (m + 2) (m + 3) := by
  classical
  obtain ⟨CA, hCA_nn, hCA⟩ := exists_rfns_iteratedCovGrad_connDiffSection_tgrid
    (I := I) (M := M) g₀ hδ₀
  obtain ⟨KQ, hKQ_nn, hKQ⟩ := tsExists_quad_jets (I := I) (M := M) g₀ hδ₀
  refine ⟨fun m => 8 * (CA (m + 1) + KQ m),
    fun m => by have := hCA_nn (m + 1); have := hKQ_nn m; linarith, ?_⟩
  intro g₁ T htie δ hδ_le hδ0 hbound m x
  set b : ℕ → ℝ := fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
    ((iteratedCovGrad (I := I) g₀ 0 2 l T).toSection x) with hb_def
  have hb : ∀ l, 0 ≤ b l :=
    fun l => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + l) x _
  set A : SmoothCcTensor g₀ 1 3 :=
    covGrad (I := I) (M := M) g₀ 1 2 (connDiffSection (I := I) g₁ g₀) +
      quadraticConnDiffCc (I := I) (M := M) g₀ g₁ with hA_def
  set Wfin : ℝ := Combinatorics.boundedFactorGridWindow b (m + 2) (m + 3) with hWfin_def
  have hWfin_nn : 0 ≤ Wfin :=
    Combinatorics.boundedFactorGridWindow_nonneg b hb (m + 2) (m + 3)
  have hAjets : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (3 + m) x
      ((iteratedCovGrad (I := I) g₀ 1 3 m A).toSection x) ≤
      (2 * CA (m + 1) + 2 * KQ m) * Wfin := by
    rw [hA_def, iteratedCovGrad_add]
    rw [show ((iteratedCovGrad (I := I) g₀ 1 3 m
          (covGrad (I := I) (M := M) g₀ 1 2 (connDiffSection (I := I) g₁ g₀)) +
        iteratedCovGrad (I := I) g₀ 1 3 m
          (quadraticConnDiffCc (I := I) (M := M) g₀ g₁)).toSection x) =
        (iteratedCovGrad (I := I) g₀ 1 3 m
          (covGrad (I := I) (M := M) g₀ 1 2 (connDiffSection (I := I) g₁ g₀))).toSection x +
        (iteratedCovGrad (I := I) g₀ 1 3 m
          (quadraticConnDiffCc (I := I) (M := M) g₀ g₁)).toSection x from by
      rw [SmoothCcTensor.toSection_add]; rfl]
    refine le_trans (riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 1 (3 + m) x _ _) ?_
    have hcd : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (3 + m) x
        ((iteratedCovGrad (I := I) g₀ 1 3 m
          (covGrad (I := I) (M := M) g₀ 1 2 (connDiffSection (I := I) g₁ g₀))).toSection x) ≤
        CA (m + 1) * Wfin := by
      rw [tsIteratedCovGrad_covGrad_eq_cast (I := I) (M := M) g₀ 1 2
        (connDiffSection (I := I) g₁ g₀) m]
      rw [tsRfns_castRankCc_db_zero (I := I) (M := M) g₀ 1
        (by omega : 2 + (m + 1) = (2 + 1) + m)
        (iteratedCovGrad (I := I) g₀ 1 2 (m + 1) (connDiffSection (I := I) g₁ g₀)) x]
      refine le_trans (hCA g₁ T htie hδ_le hδ0 hbound (m + 1) x) ?_
      refine mul_le_mul_of_nonneg_left ?_ (hCA_nn (m + 1))
      exact tsTgridSum_le_boundedWindow b hb (by omega) (by omega)
    have hq : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (3 + m) x
        ((iteratedCovGrad (I := I) g₀ 1 3 m
          (quadraticConnDiffCc (I := I) (M := M) g₀ g₁)).toSection x) ≤
        KQ m * Wfin := by
      refine le_trans (hKQ g₁ T htie hδ_le hδ0 hbound m x) ?_
      refine mul_le_mul_of_nonneg_left ?_ (hKQ_nn m)
      rw [hWfin_def]
      exact Combinatorics.boundedFactorGridWindow_mono b hb (by omega) (le_refl _)
    nlinarith [hcd, hq]
  rw [show ((iteratedCovGrad (I := I) g₀ 1 3 m
        (rsDomDomCongrSection (I := I) (M := M) g₀ 1 3 (Equiv.swap (1 : Fin 3) 2) A -
          rsDomDomCongrSection (I := I) (M := M) g₀ 1 3 (finRotate 3) A)).toSection x) =
      (iteratedCovGrad (I := I) g₀ 1 3 m
        (rsDomDomCongrSection (I := I) (M := M) g₀ 1 3
          (Equiv.swap (1 : Fin 3) 2) A)).toSection x -
      (iteratedCovGrad (I := I) g₀ 1 3 m
        (rsDomDomCongrSection (I := I) (M := M) g₀ 1 3 (finRotate 3) A)).toSection x from by
    rw [iteratedCovGrad_sub, SmoothCcTensor.toSection_sub]; rfl]
  refine le_trans (tsRfns_sub_le (I := I) (M := M) g₀ 1 (3 + m) x _ _) ?_
  rw [tsRfns_iteratedCovGrad_rsDomDomCongrSection_eq (I := I) (M := M) g₀ 1 3
    (Equiv.swap (1 : Fin 3) 2) A m x]
  rw [tsRfns_iteratedCovGrad_rsDomDomCongrSection_eq (I := I) (M := M) g₀ 1 3
    (finRotate 3) A m x]
  nlinarith [hAjets]

end CurvatureCoefficientDifferenceJetTower

set_option linter.unusedVariables false in
theorem rfns_iteratedCovGrad_riemannLoweredBackgroundDifference_topSeparated_le
    (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ Ktop : ℝ, 0 ≤ Ktop ∧ ∃ Kc : ℕ → ℝ, (∀ i, 0 ≤ Kc i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
        (hbound : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        (i : ℕ),
        ∃ Hd : SmoothCcTensor g₀ 0 (4 + i),
          (∀ x : M,
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + i) x (Hd.toSection x) ≤
              Ktop * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T).toSection x)) ∧
          (∀ x : M,
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + i) x
                ((iteratedCovGrad (I := I) g₀ 0 4 i
                    (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁) -
                  Hd).toSection x) ≤
              Kc i * Combinatorics.boundedFactorGridWindow
                (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
                  ((iteratedCovGrad (I := I) g₀ 0 2 l T).toSection x)) (i + 1) (i + 3)) := by
  classical
  obtain ⟨Kt0, hKt0_nn, Kc0, hKc0_nn, hbot⟩ :=
    rfns_iteratedCovGrad_connDiffSection_topSeparated_le (I := I) (M := M) g₀ hδ₀
  obtain ⟨KP, hKP_nn, hKP⟩ := tsExists_palatiniPair_jets (I := I) (M := M) g₀ hδ₀
  obtain ⟨KQ, hKQ_nn, hKQ⟩ := tsExists_quad_jets (I := I) (M := M) g₀ hδ₀
  obtain ⟨cg, hcg_nn, hcg⟩ := exists_backgroundJet_rfns_bound (I := I) (M := M) g₀ 0 2
    (tsMetricCc (I := I) (M := M) g₀)
  set n : ℝ := (Module.finrank ℝ E : ℝ) with hn_def
  have hn_nn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  refine ⟨n * cg 0 * (4 * Kt0),
    mul_nonneg (mul_nonneg hn_nn (hcg_nn 0)) (mul_nonneg (by norm_num) hKt0_nn), ?_⟩
  refine ⟨fun i => 2 * (n * cg 0 *
      (4 * (2 * (Kc0 (i + 1) * ((i + 1 : ℕ) : ℝ)) + 2 * KQ i))) +
      2 * ((i : ℝ) * appCcGdiag (E := E) i *
        ∑ k ∈ Finset.range i, (n * KP (i - (k + 1))) * cg (k + 1)),
    fun i => by
      have h1 : (0 : ℝ) ≤ Kc0 (i + 1) * ((i + 1 : ℕ) : ℝ) :=
        mul_nonneg (hKc0_nn (i + 1)) (Nat.cast_nonneg _)
      have h2 : (0 : ℝ) ≤ KQ i := hKQ_nn i
      have h3 : (0 : ℝ) ≤ ∑ k ∈ Finset.range i, (n * KP (i - (k + 1))) * cg (k + 1) :=
        Finset.sum_nonneg (fun k _ => mul_nonneg (mul_nonneg hn_nn (hKP_nn _)) (hcg_nn _))
      have h4 : (0 : ℝ) ≤ (i : ℝ) * appCcGdiag (E := E) i :=
        mul_nonneg (Nat.cast_nonneg _) (appCcGdiag_nonneg (E := E) i)
      have h5 : (0 : ℝ) ≤ n * cg 0 := mul_nonneg hn_nn (hcg_nn 0)
      nlinarith [mul_nonneg h4 h3, mul_nonneg h5 (by linarith : (0:ℝ) ≤ 4 * (2 * (Kc0 (i + 1) * ((i + 1 : ℕ) : ℝ)) + 2 * KQ i))], ?_⟩
  intro g₁ T htie δ hδ_le hδ0 hbound i
  have hpal := riemannLoweredBackgroundDifference_palatini_repr (I := I) (M := M) g₀ g₁
  set A : SmoothCcTensor g₀ 1 3 :=
    covGrad (I := I) (M := M) g₀ 1 2 (connDiffSection (I := I) g₁ g₀) +
      quadraticConnDiffCc (I := I) (M := M) g₀ g₁ with hA_def
  set PA : SmoothCcTensor g₀ 1 3 :=
    rsDomDomCongrSection (I := I) (M := M) g₀ 1 3 (Equiv.swap (1 : Fin 3) 2) A -
      rsDomDomCongrSection (I := I) (M := M) g₀ 1 3 (finRotate 3) A with hPA_def
  have hswap : tsLoweredSlot0 (I := I) (M := M) g₀ 2 PA =
      domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 4) 1)
        (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁) := by
    rw [← hpal]
    exact tsLoweredSlot0_cometricRaise (I := I) (M := M) g₀ 2 _
  have hCD4 : riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁ =
      domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 4) 1)
        (tsLoweredSlot0 (I := I) (M := M) g₀ 2 PA) := by
    rw [hswap, tsDomDomCongrSection_comp, Equiv.swap_swap, tsDomDomCongrSection_refl]
  set HeadCore : SmoothCcTensor g₀ 1 (2 + (i + 1)) :=
    appCcRS (I := I) (M := M) g₀ 1 1 (2 + (i + 1))
      (iteratedCovGrad (I := I) g₀ 1 2 (i + 1) (raisedKoszul (I := I) g₀ g₁))
      (sharpFlatEndoCc (I := I) g₀ g₁) with hHeadCore_def
  set HA : SmoothCcTensor g₀ 1 (3 + i) :=
    castRankCc_db g₀ 1 (by omega : 2 + (i + 1) = 3 + i) HeadCore with hHA_def
  obtain ⟨τ₁, hτ₁⟩ := tsExists_iteratedCovGrad_rsDomDomCongrSection (I := I) (M := M)
    g₀ 1 3 (Equiv.swap (1 : Fin 3) 2) A i
  obtain ⟨τ₂, hτ₂⟩ := tsExists_iteratedCovGrad_rsDomDomCongrSection (I := I) (M := M)
    g₀ 1 3 (finRotate 3) A i
  set HPA : SmoothCcTensor g₀ 1 (3 + i) :=
    rsDomDomCongrSection (I := I) (M := M) g₀ 1 (3 + i) τ₁ HA -
      rsDomDomCongrSection (I := I) (M := M) g₀ 1 (3 + i) τ₂ HA with hHPA_def
  obtain ⟨Hd, hHd⟩ := tsExists_loweredPair_headTransport (I := I) (M := M) g₀
    (Equiv.swap (0 : Fin 4) 1) PA i HPA
  refine ⟨Hd, ?_, ?_⟩
  · intro x
    have h1 := (hHd x).1
    have hHPA_rfns : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (3 + i) x
        (HPA.toSection x) ≤
        4 * riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + (i + 1)) x
          (HeadCore.toSection x) := by
      rw [hHPA_def]
      rw [show ((rsDomDomCongrSection (I := I) (M := M) g₀ 1 (3 + i) τ₁ HA -
            rsDomDomCongrSection (I := I) (M := M) g₀ 1 (3 + i) τ₂ HA).toSection x) =
          (rsDomDomCongrSection (I := I) (M := M) g₀ 1 (3 + i) τ₁ HA).toSection x -
            (rsDomDomCongrSection (I := I) (M := M) g₀ 1 (3 + i) τ₂ HA).toSection x from by
        rw [SmoothCcTensor.toSection_sub]; rfl]
      refine le_trans (tsRfns_sub_le (I := I) (M := M) g₀ 1 (3 + i) x _ _) ?_
      rw [tsRfns_rsDomDomCongrSection_zero (I := I) (M := M) g₀ 1 (3 + i) τ₁ HA x,
        tsRfns_rsDomDomCongrSection_zero (I := I) (M := M) g₀ 1 (3 + i) τ₂ HA x]
      rw [hHA_def, tsRfns_castRankCc_db_zero (I := I) (M := M) g₀ 1
        (by omega : 2 + (i + 1) = 3 + i) HeadCore x]
      linarith [riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 1 (2 + (i + 1)) x
        (HeadCore.toSection x)]
    have hHC := (hbot g₁ T htie hδ_le hδ0 hbound (i + 1) x).1
    rw [tsRfns_order_congr (I := I) (M := M) g₀ 0 2
      (show (i + 1) + 1 = i + 2 from by omega) T x] at hHC
    have hgW := hcg 0 x
    rw [show (iteratedCovGrad (I := I) g₀ 0 2 0 (tsMetricCc (I := I) (M := M) g₀)) =
        tsMetricCc (I := I) (M := M) g₀ from iteratedCovGrad_zero (I := I) g₀ 0 2 _] at hgW
    have hb_nn := riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
      ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T).toSection x)
    have hHC_nn := riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 1 (2 + (i + 1)) x
      (HeadCore.toSection x)
    have hgW_nn := riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 2 x
      ((tsMetricCc (I := I) (M := M) g₀).toSection x)
    have hHPA_nn := riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 1 (3 + i) x
      (HPA.toSection x)
    calc riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + i) x (Hd.toSection x)
        ≤ n * riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x
            ((tsMetricCc (I := I) (M := M) g₀).toSection x) *
          riemannianFiberNormSq (I := I) (M := M) g₀ 1 (3 + i) x (HPA.toSection x) := h1
      _ ≤ n * cg 0 *
          (4 * (Kt0 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T).toSection x))) := by
          have hstep1 : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (3 + i) x
              (HPA.toSection x) ≤
              4 * (Kt0 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T).toSection x)) := by
            refine le_trans hHPA_rfns ?_
            linarith [hHC]
          have hng : 0 ≤ n * riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x
              ((tsMetricCc (I := I) (M := M) g₀).toSection x) :=
            mul_nonneg hn_nn hgW_nn
          calc n * riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x
                ((tsMetricCc (I := I) (M := M) g₀).toSection x) *
                riemannianFiberNormSq (I := I) (M := M) g₀ 1 (3 + i) x (HPA.toSection x)
              ≤ n * riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x
                  ((tsMetricCc (I := I) (M := M) g₀).toSection x) *
                (4 * (Kt0 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
                  ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T).toSection x))) :=
                mul_le_mul_of_nonneg_left hstep1 hng
            _ ≤ n * cg 0 *
                (4 * (Kt0 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
                  ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T).toSection x))) := by
                refine mul_le_mul_of_nonneg_right ?_ ?_
                · exact mul_le_mul_of_nonneg_left hgW hn_nn
                · exact mul_nonneg (by norm_num) (mul_nonneg hKt0_nn hb_nn)
      _ = n * cg 0 * (4 * Kt0) *
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T).toSection x) := by ring
  · intro x
    have h2 := (hHd x).2
    set b : ℕ → ℝ := fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
      ((iteratedCovGrad (I := I) g₀ 0 2 l T).toSection x) with hb_def
    have hb : ∀ l, 0 ≤ b l :=
      fun l => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + l) x _
    set Wfin : ℝ := Combinatorics.boundedFactorGridWindow b (i + 1) (i + 3) with hWfin_def
    have hWfin_nn : 0 ≤ Wfin :=
      Combinatorics.boundedFactorGridWindow_nonneg b hb (i + 1) (i + 3)
    rw [show (iteratedCovGrad (I := I) g₀ 0 4 i
          (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁)) =
        iteratedCovGrad (I := I) g₀ 0 4 i
          (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 4) 1)
            (tsLoweredSlot0 (I := I) (M := M) g₀ 2 PA)) from by rw [← hCD4]]
    refine le_trans h2 ?_
    have hAdiff : iteratedCovGrad (I := I) g₀ 1 3 i A - HA =
        castRankCc_db g₀ 1 (by omega : 2 + (i + 1) = 3 + i)
          (iteratedCovGrad (I := I) g₀ 1 2 (i + 1) (connDiffSection (I := I) g₁ g₀) -
            HeadCore) +
        iteratedCovGrad (I := I) g₀ 1 3 i (quadraticConnDiffCc (I := I) (M := M) g₀ g₁) := by
      rw [hA_def, iteratedCovGrad_add]
      rw [show (iteratedCovGrad (I := I) g₀ 1 3 i
            (covGrad (I := I) (M := M) g₀ 1 2 (connDiffSection (I := I) g₁ g₀))) =
          castRankCc_db g₀ 1 (by omega : 2 + (i + 1) = 3 + i)
            (iteratedCovGrad (I := I) g₀ 1 2 (i + 1) (connDiffSection (I := I) g₁ g₀))
          from tsIteratedCovGrad_covGrad_eq_cast (I := I) (M := M) g₀ 1 2
            (connDiffSection (I := I) g₁ g₀) i]
      rw [hHA_def]
      rw [tsCastRankCc_db_sub (I := I) (M := M) g₀ 1
        (by omega : 2 + (i + 1) = 3 + i)]
      exact add_sub_right_comm _ _ _
    have hdiff_pt : ((iteratedCovGrad (I := I) g₀ 1 3 i PA - HPA).toSection x :
        Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace (3 + i) I x) =
        rsDomDomCongr (I := I) (M := M) τ₁
            ((iteratedCovGrad (I := I) g₀ 1 3 i A - HA).toSection x) -
          rsDomDomCongr (I := I) (M := M) τ₂
            ((iteratedCovGrad (I := I) g₀ 1 3 i A - HA).toSection x) := by
      rw [show ((iteratedCovGrad (I := I) g₀ 1 3 i PA - HPA).toSection x) =
          (iteratedCovGrad (I := I) g₀ 1 3 i PA).toSection x - HPA.toSection x from by
        rw [SmoothCcTensor.toSection_sub]; rfl]
      rw [hPA_def, iteratedCovGrad_sub]
      rw [show ((iteratedCovGrad (I := I) g₀ 1 3 i
            (rsDomDomCongrSection (I := I) (M := M) g₀ 1 3 (Equiv.swap (1 : Fin 3) 2) A) -
          iteratedCovGrad (I := I) g₀ 1 3 i
            (rsDomDomCongrSection (I := I) (M := M) g₀ 1 3 (finRotate 3) A)).toSection x) =
          (iteratedCovGrad (I := I) g₀ 1 3 i
            (rsDomDomCongrSection (I := I) (M := M) g₀ 1 3
              (Equiv.swap (1 : Fin 3) 2) A)).toSection x -
          (iteratedCovGrad (I := I) g₀ 1 3 i
            (rsDomDomCongrSection (I := I) (M := M) g₀ 1 3 (finRotate 3) A)).toSection x
          from by rw [SmoothCcTensor.toSection_sub]; rfl]
      rw [hτ₁ x, hτ₂ x]
      rw [hHPA_def]
      rw [show ((rsDomDomCongrSection (I := I) (M := M) g₀ 1 (3 + i) τ₁ HA -
            rsDomDomCongrSection (I := I) (M := M) g₀ 1 (3 + i) τ₂ HA).toSection x) =
          (rsDomDomCongrSection (I := I) (M := M) g₀ 1 (3 + i) τ₁ HA).toSection x -
            (rsDomDomCongrSection (I := I) (M := M) g₀ 1 (3 + i) τ₂ HA).toSection x from by
        rw [SmoothCcTensor.toSection_sub]; rfl]
      rw [rsDomDomCongrSection_toSection, rsDomDomCongrSection_toSection]
      rw [show ((iteratedCovGrad (I := I) g₀ 1 3 i A - HA).toSection x) =
          (iteratedCovGrad (I := I) g₀ 1 3 i A).toSection x - HA.toSection x from by
        rw [SmoothCcTensor.toSection_sub]; rfl]
      rw [tsRsDomDomCongr_sub (I := I) (M := M) τ₁, tsRsDomDomCongr_sub (I := I) (M := M) τ₂]
      abel
    have hPAHPA : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (3 + i) x
        ((iteratedCovGrad (I := I) g₀ 1 3 i PA - HPA).toSection x) ≤
        4 * riemannianFiberNormSq (I := I) (M := M) g₀ 1 (3 + i) x
          ((iteratedCovGrad (I := I) g₀ 1 3 i A - HA).toSection x) := by
      rw [hdiff_pt]
      refine le_trans (tsRfns_sub_le (I := I) (M := M) g₀ 1 (3 + i) x _ _) ?_
      rw [riemannianFiberNormSq_domDomCongr_covariant (I := I) (M := M) g₀ 1 (3 + i) x τ₁ _,
        riemannianFiberNormSq_domDomCongr_covariant (I := I) (M := M) g₀ 1 (3 + i) x τ₂ _]
      linarith [riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 1 (3 + i) x
        ((iteratedCovGrad (I := I) g₀ 1 3 i A - HA).toSection x)]
    have hAHA : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (3 + i) x
        ((iteratedCovGrad (I := I) g₀ 1 3 i A - HA).toSection x) ≤
        2 * (Kc0 (i + 1) * ((i + 1 : ℕ) : ℝ)) * Wfin + 2 * KQ i * Wfin := by
      rw [hAdiff]
      rw [show ((castRankCc_db g₀ 1 (by omega : 2 + (i + 1) = 3 + i)
            (iteratedCovGrad (I := I) g₀ 1 2 (i + 1) (connDiffSection (I := I) g₁ g₀) -
              HeadCore) +
          iteratedCovGrad (I := I) g₀ 1 3 i
            (quadraticConnDiffCc (I := I) (M := M) g₀ g₁)).toSection x) =
          (castRankCc_db g₀ 1 (by omega : 2 + (i + 1) = 3 + i)
            (iteratedCovGrad (I := I) g₀ 1 2 (i + 1) (connDiffSection (I := I) g₁ g₀) -
              HeadCore)).toSection x +
          (iteratedCovGrad (I := I) g₀ 1 3 i
            (quadraticConnDiffCc (I := I) (M := M) g₀ g₁)).toSection x from by
        rw [SmoothCcTensor.toSection_add]; rfl]
      refine le_trans (riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 1 (3 + i) x _ _) ?_
      rw [tsRfns_castRankCc_db_zero (I := I) (M := M) g₀ 1
        (by omega : 2 + (i + 1) = 3 + i) _ x]
      have hres := (hbot g₁ T htie hδ_le hδ0 hbound (i + 1) x).2
      rw [hHeadCore_def]
      have hresW : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + (i + 1)) x
          ((iteratedCovGrad (I := I) g₀ 1 2 (i + 1) (connDiffSection (I := I) g₁ g₀) -
            appCcRS (I := I) (M := M) g₀ 1 1 (2 + (i + 1))
              (iteratedCovGrad (I := I) g₀ 1 2 (i + 1) (raisedKoszul (I := I) g₀ g₁))
              (sharpFlatEndoCc (I := I) g₀ g₁)).toSection x) ≤
          Kc0 (i + 1) * (((i + 1 : ℕ) : ℝ) * Wfin) := by
        refine le_trans hres ?_
        refine mul_le_mul_of_nonneg_left ?_ (hKc0_nn (i + 1))
        refine le_trans (tsResSum_le_boundedWindow b hb (i + 1)) ?_
        rw [show (i + 1) + 2 = i + 3 from by omega]
      have hqW := hKQ g₁ T htie hδ_le hδ0 hbound i x
      nlinarith [hresW, hqW, hWfin_nn, hKc0_nn (i + 1), hKQ_nn i]
    have hcorr : ∀ k ∈ Finset.range i,
        (n * riemannianFiberNormSq (I := I) (M := M) g₀ 1 ((2 + 1) + (i - (k + 1))) x
          ((iteratedCovGrad (I := I) g₀ 1 (2 + 1) (i - (k + 1)) PA).toSection x)) *
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (k + 1)) x
          ((iteratedCovGrad (I := I) g₀ 0 2 (k + 1)
            (tsMetricCc (I := I) (M := M) g₀)).toSection x) ≤
        ((n * KP (i - (k + 1))) * cg (k + 1)) * Wfin := by
      intro k hk
      rw [Finset.mem_range] at hk
      have hPAj : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (3 + (i - (k + 1))) x
          ((iteratedCovGrad (I := I) g₀ 1 3 (i - (k + 1)) PA).toSection x) ≤
          KP (i - (k + 1)) * Wfin := by
        rw [hPA_def, hA_def]
        refine le_trans (hKP g₁ T htie hδ_le hδ0 hbound (i - (k + 1)) x) ?_
        refine mul_le_mul_of_nonneg_left ?_ (hKP_nn (i - (k + 1)))
        rw [hWfin_def]
        exact Combinatorics.boundedFactorGridWindow_mono b hb (by omega) (by omega)
      have hgj := hcg (k + 1) x
      have hPAj_nn := riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 1
        (3 + (i - (k + 1))) x
        ((iteratedCovGrad (I := I) g₀ 1 3 (i - (k + 1)) PA).toSection x)
      have hgj_nn := riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + (k + 1)) x
        ((iteratedCovGrad (I := I) g₀ 0 2 (k + 1)
          (tsMetricCc (I := I) (M := M) g₀)).toSection x)
      calc (n * riemannianFiberNormSq (I := I) (M := M) g₀ 1 ((2 + 1) + (i - (k + 1))) x
            ((iteratedCovGrad (I := I) g₀ 1 (2 + 1) (i - (k + 1)) PA).toSection x)) *
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (k + 1)) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (k + 1)
              (tsMetricCc (I := I) (M := M) g₀)).toSection x)
          ≤ (n * (KP (i - (k + 1)) * Wfin)) * cg (k + 1) := by
            refine mul_le_mul ?_ hgj hgj_nn ?_
            · exact mul_le_mul_of_nonneg_left hPAj hn_nn
            · exact mul_nonneg hn_nn (mul_nonneg (hKP_nn _) hWfin_nn)
        _ = ((n * KP (i - (k + 1))) * cg (k + 1)) * Wfin := by ring
    have hterm2 : (∑ k ∈ Finset.range i,
        (n * riemannianFiberNormSq (I := I) (M := M) g₀ 1 ((2 + 1) + (i - (k + 1))) x
          ((iteratedCovGrad (I := I) g₀ 1 (2 + 1) (i - (k + 1)) PA).toSection x)) *
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (k + 1)) x
          ((iteratedCovGrad (I := I) g₀ 0 2 (k + 1)
            (tsMetricCc (I := I) (M := M) g₀)).toSection x)) ≤
        (∑ k ∈ Finset.range i, (n * KP (i - (k + 1))) * cg (k + 1)) * Wfin := by
      rw [Finset.sum_mul]
      exact Finset.sum_le_sum hcorr
    have hterm1 : n * riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x
          ((tsMetricCc (I := I) (M := M) g₀).toSection x) *
        riemannianFiberNormSq (I := I) (M := M) g₀ 1 ((2 + 1) + i) x
          ((iteratedCovGrad (I := I) g₀ 1 (2 + 1) i PA - HPA).toSection x) ≤
        n * cg 0 * (4 * (2 * (Kc0 (i + 1) * ((i + 1 : ℕ) : ℝ)) * Wfin +
          2 * KQ i * Wfin)) := by
      have hgW := hcg 0 x
      rw [show (iteratedCovGrad (I := I) g₀ 0 2 0 (tsMetricCc (I := I) (M := M) g₀)) =
          tsMetricCc (I := I) (M := M) g₀ from iteratedCovGrad_zero (I := I) g₀ 0 2 _] at hgW
      have hd_le : riemannianFiberNormSq (I := I) (M := M) g₀ 1 ((2 + 1) + i) x
          ((iteratedCovGrad (I := I) g₀ 1 (2 + 1) i PA - HPA).toSection x) ≤
          4 * (2 * (Kc0 (i + 1) * ((i + 1 : ℕ) : ℝ)) * Wfin + 2 * KQ i * Wfin) := by
        refine le_trans hPAHPA ?_
        nlinarith [hAHA, riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 1 (3 + i) x
          ((iteratedCovGrad (I := I) g₀ 1 3 i A - HA).toSection x)]
      have hgW_nn := riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 2 x
        ((tsMetricCc (I := I) (M := M) g₀).toSection x)
      have hd_nn := riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 1 ((2 + 1) + i) x
        ((iteratedCovGrad (I := I) g₀ 1 (2 + 1) i PA - HPA).toSection x)
      calc n * riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x
            ((tsMetricCc (I := I) (M := M) g₀).toSection x) *
          riemannianFiberNormSq (I := I) (M := M) g₀ 1 ((2 + 1) + i) x
            ((iteratedCovGrad (I := I) g₀ 1 (2 + 1) i PA - HPA).toSection x)
          ≤ n * riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x
              ((tsMetricCc (I := I) (M := M) g₀).toSection x) *
            (4 * (2 * (Kc0 (i + 1) * ((i + 1 : ℕ) : ℝ)) * Wfin + 2 * KQ i * Wfin)) :=
            mul_le_mul_of_nonneg_left hd_le (mul_nonneg hn_nn hgW_nn)
        _ ≤ n * cg 0 * (4 * (2 * (Kc0 (i + 1) * ((i + 1 : ℕ) : ℝ)) * Wfin +
            2 * KQ i * Wfin)) := by
            refine mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hgW hn_nn) ?_
            have h1 : (0 : ℝ) ≤ 2 * (Kc0 (i + 1) * ((i + 1 : ℕ) : ℝ)) * Wfin :=
              mul_nonneg (mul_nonneg (by norm_num)
                (mul_nonneg (hKc0_nn _) (Nat.cast_nonneg _))) hWfin_nn
            have h2 : (0 : ℝ) ≤ 2 * KQ i * Wfin :=
              mul_nonneg (mul_nonneg (by norm_num) (hKQ_nn i)) hWfin_nn
            linarith
    calc 2 * (n * riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x
            ((tsMetricCc (I := I) (M := M) g₀).toSection x) *
          riemannianFiberNormSq (I := I) (M := M) g₀ 1 ((2 + 1) + i) x
            ((iteratedCovGrad (I := I) g₀ 1 (2 + 1) i PA - HPA).toSection x)) +
        2 * ((i : ℝ) * appCcGdiag (E := E) i *
          ∑ k ∈ Finset.range i,
            (n * riemannianFiberNormSq (I := I) (M := M) g₀ 1 ((2 + 1) + (i - (k + 1))) x
              ((iteratedCovGrad (I := I) g₀ 1 (2 + 1) (i - (k + 1)) PA).toSection x)) *
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (k + 1)) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (k + 1)
                (tsMetricCc (I := I) (M := M) g₀)).toSection x))
        ≤ 2 * (n * cg 0 * (4 * (2 * (Kc0 (i + 1) * ((i + 1 : ℕ) : ℝ)) * Wfin +
            2 * KQ i * Wfin))) +
          2 * ((i : ℝ) * appCcGdiag (E := E) i *
            ((∑ k ∈ Finset.range i, (n * KP (i - (k + 1))) * cg (k + 1)) * Wfin)) := by
          refine add_le_add (mul_le_mul_of_nonneg_left hterm1 (by norm_num)) ?_
          refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
          exact mul_le_mul_of_nonneg_left hterm2
            (mul_nonneg (Nat.cast_nonneg _) (appCcGdiag_nonneg (E := E) i))
      _ = (2 * (n * cg 0 *
            (4 * (2 * (Kc0 (i + 1) * ((i + 1 : ℕ) : ℝ)) + 2 * KQ i))) +
          2 * ((i : ℝ) * appCcGdiag (E := E) i *
            ∑ k ∈ Finset.range i, (n * KP (i - (k + 1))) * cg (k + 1))) * Wfin := by
          ring

end TopSeparatedRungRLD

end Connection
end Integral
end DifferentialGeometry

end
