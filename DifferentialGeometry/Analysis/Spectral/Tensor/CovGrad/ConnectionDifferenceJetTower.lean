import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.ConnectionDifferenceFibreBound
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RicciDeTurckSectionDifference
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.CometricInverseDifferenceMultiplier
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.MetricArmCoeffJetTower

noncomputable section

set_option linter.style.setOption false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open Bundle Manifold Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators Matrix

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Laplacian
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open TensorMultilinear (contMDiffAt_section_apply contMDiff_section_apply)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

theorem g0FlatField_contMDiff (g₀ : SmoothRiemannianMetric I M) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] Tensor0SModel 1 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (E →L[ℝ] Tensor0SModel 1 ℝ E)
        (E := fun z : M => TangentSpace I z →L[ℝ] Tensor0SSpace 1 I z) x
        (g0FlatCLM (I := I) g₀ x)) := by
  classical
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (F₁ := E) (V₁ := fun z : M => TangentSpace I z)
    (F₂ := Tensor0SModel 1 ℝ E) (V₂ := fun z : M => Tensor0SSpace 1 I z)
    (φ := fun x : M => g0FlatCLM (I := I) g₀ x)
  intro Z
  letI := Tensor0SBundle.tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 1
  refine (contMDiff_multilinearSection_iff_coord (𝕜 := ℝ) (F := E)
      (E := (TangentSpace I : M → Type _)) (IB := I) (n := (∞ : WithTop ℕ∞)) (Module.finBasis ℝ E)
      (fun x : M => (g0FlatCLM (I := I) g₀ x (Z x) :
        Bundle.continuousMultilinearMap ℝ 1 E (TangentSpace I) x))).mpr ?_
  intro σ x₀
  set b := Module.finBasis ℝ E with hb
  set e₁ := trivializationAt E (TangentSpace I : M → Type _) x₀ with he₁def
  have he₁ : x₀ ∈ e₁.baseSet := mem_baseSet_trivializationAt E (TangentSpace I) x₀
  have hframe := e₁.isLocalFrameOn_localFrame_baseSet I (⊤ : ℕ∞) b
  obtain ⟨Y, hY⟩ := hframe.exists_contMDiffSection_eqOn_nhd e₁.open_baseSet he₁
  have hscalar : ContMDiffAt I 𝓘(ℝ, ℝ) ∞
      (fun x : M => g₀.inner x (Z x) (Y (σ 0) x)) x₀ := by
    have h_total : ContMDiffAt I (I.prod 𝓘(ℝ, ℝ)) ∞
        (fun b : M => (⟨b, g₀.inner b (Z b) (Y (σ 0) b)⟩ :
          TotalSpace ℝ (Bundle.Trivial M ℝ))) x₀ :=
      (ContMDiffOn.clm_bundle_apply₂ (F₁ := E) (F₂ := E) (F₃ := ℝ) (b := id)
        g₀.contMDiff.contMDiffOn Z.contMDiff.contMDiffOn
        (Y (σ 0)).contMDiff.contMDiffOn x₀ (mem_univ x₀)).contMDiffAt univ_mem
    rw [Bundle.contMDiffAt_totalSpace] at h_total
    exact h_total.2
  refine hscalar.congr_of_eventuallyEq ?_
  have h_base₁ : ∀ᶠ x in 𝓝 x₀, x ∈ e₁.baseSet := e₁.open_baseSet.mem_nhds he₁
  filter_upwards [h_base₁, hY] with x hx₁ hYx
  rw [continuousMultilinearMap_basis_repr]
  have hframe0 : e₁.symmL ℝ x (b (σ 0)) = (Y (σ 0)) x := by
    rw [hYx (σ 0), Trivialization.localFrame_apply_of_mem_baseSet (hx := hx₁)]
    simp [Trivialization.basisAt]
  change (g0FlatCLM (I := I) g₀ x (Z x)) (fun j : Fin 1 => e₁.symmL ℝ x (b (σ j))) = _
  rw [show (fun j : Fin 1 => e₁.symmL ℝ x (b (σ j))) = (fun _ : Fin 1 => e₁.symmL ℝ x (b (σ 0))) from by
    funext j; fin_cases j; rfl]
  rw [hframe0]
  rw [g0FlatCLM_apply, dualToCotangent_apply]
  rfl

theorem sharpFlatEndoCcFib_contMDiff (g₀ g₁ : SmoothRiemannianMetric I M) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 1 ℝ E →L[ℝ] Tensor0SModel 1 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SModel 1 ℝ E →L[ℝ] Tensor0SModel 1 ℝ E)
        (E := fun z : M => Tensor0SSpace 1 I z →L[ℝ] Tensor0SSpace 1 I z) x
        ((g0FlatCLM (I := I) g₀ x).comp (inverseMetricSharpFib (I := I) g₁ x))) := by
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (F₁ := Tensor0SModel 1 ℝ E) (V₁ := fun z : M => Tensor0SSpace 1 I z)
    (F₂ := Tensor0SModel 1 ℝ E) (V₂ := fun z : M => Tensor0SSpace 1 I z)
    (φ := fun x : M => (g0FlatCLM (I := I) g₀ x).comp (inverseMetricSharpFib (I := I) g₁ x))
  intro Y
  have hsharpY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) x
        (inverseMetricSharpFib (I := I) g₁ x (Y x))) :=
    ContMDiff.clm_bundle_apply (b := id)
      (inverseMetricSharpField_contMDiff (I := I) g₁) Y.contMDiff
  have hflatsharpY : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 1 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SModel 1 ℝ E)
        (E := fun z : M => Tensor0SSpace 1 I z) x
        (g0FlatCLM (I := I) g₀ x (inverseMetricSharpFib (I := I) g₁ x (Y x)))) :=
    ContMDiff.clm_bundle_apply (b := id)
      (g0FlatField_contMDiff (I := I) g₀) hsharpY
  refine hflatsharpY.congr (fun x => ?_)
  rfl

def sharpFlatEndoCc (g₀ g₁ : SmoothRiemannianMetric I M) : SmoothCcTensor g₀ 1 1 where
  toSection :=
    { toFun := fun x : M => TensorRSSpace.ofCLM
        ((g0FlatCLM (I := I) g₀ x).comp (inverseMetricSharpFib (I := I) g₁ x))
      contMDiff_toFun := sharpFlatEndoCcFib_contMDiff (I := I) g₀ g₁ }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

@[simp] lemma sharpFlatEndoCc_toSection (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) :
    (sharpFlatEndoCc (I := I) g₀ g₁).toSection x =
      TensorRSSpace.ofCLM
        ((g0FlatCLM (I := I) g₀ x).comp (inverseMetricSharpFib (I := I) g₁ x)) := rfl

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma tensor0SOne_apply_add' (x : M) (om : Tensor0SSpace 1 I x)
    (a b : TangentSpace I x) :
    om (fun _ : Fin 1 => a + b) = om (fun _ : Fin 1 => a) + om (fun _ : Fin 1 => b) := by
  let φ := continuousMultilinearCurryFin1 ℝ (TangentSpace I x) ℝ
    (om : ContinuousMultilinearMap ℝ (fun _ : Fin 1 => TangentSpace I x) ℝ)
  have ha : (om : ContinuousMultilinearMap ℝ (fun _ : Fin 1 => TangentSpace I x) ℝ)
      (fun _ : Fin 1 => a) = φ a := by rw [continuousMultilinearCurryFin1_apply]; rfl
  have hb : (om : ContinuousMultilinearMap ℝ (fun _ : Fin 1 => TangentSpace I x) ℝ)
      (fun _ : Fin 1 => b) = φ b := by rw [continuousMultilinearCurryFin1_apply]; rfl
  have hab : (om : ContinuousMultilinearMap ℝ (fun _ : Fin 1 => TangentSpace I x) ℝ)
      (fun _ : Fin 1 => a + b) = φ (a + b) := by rw [continuousMultilinearCurryFin1_apply]; rfl
  change (om : ContinuousMultilinearMap ℝ (fun _ : Fin 1 => TangentSpace I x) ℝ)
      (fun _ => a + b) = _
  rw [hab, ha, hb, map_add]

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma tensor0SOne_apply_smul' (x : M) (om : Tensor0SSpace 1 I x)
    (c : ℝ) (a : TangentSpace I x) :
    om (fun _ : Fin 1 => c • a) = c • om (fun _ : Fin 1 => a) := by
  let φ := continuousMultilinearCurryFin1 ℝ (TangentSpace I x) ℝ
    (om : ContinuousMultilinearMap ℝ (fun _ : Fin 1 => TangentSpace I x) ℝ)
  have ha : (om : ContinuousMultilinearMap ℝ (fun _ : Fin 1 => TangentSpace I x) ℝ)
      (fun _ : Fin 1 => a) = φ a := by rw [continuousMultilinearCurryFin1_apply]; rfl
  have hca : (om : ContinuousMultilinearMap ℝ (fun _ : Fin 1 => TangentSpace I x) ℝ)
      (fun _ : Fin 1 => c • a) = φ (c • a) := by rw [continuousMultilinearCurryFin1_apply]; rfl
  change (om : ContinuousMultilinearMap ℝ (fun _ : Fin 1 => TangentSpace I x) ℝ)
      (fun _ => c • a) = _
  rw [hca, ha, map_smul]

def sharpFlatRaiseEndo (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) :
    TangentSpace I x →L[ℝ] TangentSpace I x :=
  (inverseMetricSharpFib (I := I) g₀ x).comp (g0FlatCLM (I := I) g₁ x)

@[simp] lemma sharpFlatRaiseEndo_apply (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (v : TangentSpace I x) :
    sharpFlatRaiseEndo (I := I) g₀ g₁ x v =
      inverseMetricSharpFib (I := I) g₀ x (g0FlatCLM (I := I) g₁ x v) := rfl

@[irreducible] def raisedKoszulVec (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (a b : TangentSpace I x) : TangentSpace I x :=
  sharpFlatRaiseEndo (I := I) g₀ g₁ x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x a b)

@[simp] lemma raisedKoszulVec_apply (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (a b : TangentSpace I x) :
    raisedKoszulVec (I := I) g₀ g₁ x a b =
      inverseMetricSharpFib (I := I) g₀ x
        (g0FlatCLM (I := I) g₁ x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x a b)) := by
  unfold raisedKoszulVec; rfl

set_option linter.unusedSectionVars false in
lemma raisedKoszulVec_continuous₂ (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) :
    Continuous (fun p : TangentSpace I x × TangentSpace I x =>
      raisedKoszulVec (I := I) g₀ g₁ x p.1 p.2) := by
  have hcd : Continuous (fun p : TangentSpace I x × TangentSpace I x =>
      PDE.DeTurck.connDiff (I := I) g₁ g₀ x p.1 p.2) :=
    (PDE.DeTurck.connDiff (I := I) g₁ g₀ x).continuous₂
  have heq : (fun p : TangentSpace I x × TangentSpace I x =>
      raisedKoszulVec (I := I) g₀ g₁ x p.1 p.2) =
      (fun p : TangentSpace I x × TangentSpace I x =>
        sharpFlatRaiseEndo (I := I) g₀ g₁ x
          (PDE.DeTurck.connDiff (I := I) g₁ g₀ x p.1 p.2)) := by
    funext p; rw [raisedKoszulVec_apply]; rfl
  rw [heq]
  exact (sharpFlatRaiseEndo (I := I) g₀ g₁ x).continuous.comp hcd

set_option maxHeartbeats 6400000 in
def raisedKoszulPairing (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (om : Tensor0SSpace 1 I x) : Tensor0SSpace 2 I x :=
  (show ContinuousMultilinearMap ℝ (fun _ : Fin 2 => TangentSpace I x) ℝ from
    { toFun := fun YZ => om (fun _ : Fin 1 => raisedKoszulVec (I := I) g₀ g₁ x (YZ 0) (YZ 1))
      map_update_add' := by
        have hne10 : (1 : Fin 2) ≠ 0 := by decide
        have hne01 : (0 : Fin 2) ≠ 1 := by decide
        intro _ YZ i Y Y'
        fin_cases i <;>
          · simp only [Fin.isValue, Fin.mk_zero, Fin.mk_one, Function.update_self,
              Function.update_of_ne, ne_eq, hne10, hne01, not_false_eq_true,
              raisedKoszulVec_apply, ContinuousLinearMap.add_apply, map_add]
            rw [tensor0SOne_apply_add' (I := I) x om]
      map_update_smul' := by
        have hne10 : (1 : Fin 2) ≠ 0 := by decide
        have hne01 : (0 : Fin 2) ≠ 1 := by decide
        intro _ YZ i c Y
        fin_cases i <;>
          · simp only [Fin.isValue, Fin.mk_zero, Fin.mk_one, Function.update_self,
              Function.update_of_ne, ne_eq, hne10, hne01, not_false_eq_true,
              raisedKoszulVec_apply, ContinuousLinearMap.smul_apply, map_smul]
            rw [tensor0SOne_apply_smul' (I := I) x om]
      cont := by
        have hpair : Continuous (fun YZ : Fin 2 → TangentSpace I x => (YZ 0, YZ 1)) :=
          (continuous_apply 0).prodMk (continuous_apply 1)
        have hbil : Continuous (fun YZ : Fin 2 → TangentSpace I x =>
            raisedKoszulVec (I := I) g₀ g₁ x (YZ 0) (YZ 1)) :=
          (raisedKoszulVec_continuous₂ (I := I) g₀ g₁ x).comp hpair
        exact ((ContinuousMultilinearMap.coe_continuous
          (om : ContinuousMultilinearMap ℝ (fun _ : Fin 1 => TangentSpace I x) ℝ)).comp
          (continuous_pi (fun _ => hbil))) } : Tensor0SSpace 2 I x)

@[simp] lemma raisedKoszulPairing_apply (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (om : Tensor0SSpace 1 I x) (YZ : Fin 2 → TangentSpace I x) :
    (raisedKoszulPairing (I := I) g₀ g₁ x om) YZ =
      om (fun _ : Fin 1 => raisedKoszulVec (I := I) g₀ g₁ x (YZ 0) (YZ 1)) := rfl

lemma raisedKoszulPairing_add (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (om om' : Tensor0SSpace 1 I x) :
    raisedKoszulPairing (I := I) g₀ g₁ x (om + om') =
      raisedKoszulPairing (I := I) g₀ g₁ x om + raisedKoszulPairing (I := I) g₀ g₁ x om' := by
  apply ContinuousMultilinearMap.ext
  intro YZ
  exact ContinuousMultilinearMap.add_apply om om' _

lemma raisedKoszulPairing_smul (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (c : ℝ) (om : Tensor0SSpace 1 I x) :
    raisedKoszulPairing (I := I) g₀ g₁ x (c • om) =
      c • raisedKoszulPairing (I := I) g₀ g₁ x om := by
  apply ContinuousMultilinearMap.ext
  intro YZ
  exact ContinuousMultilinearMap.smul_apply om c _

def raisedKoszulFib (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) :
    TensorRSSpace 1 2 I x :=
  TensorRSSpace.ofCLM
    (LinearMap.toContinuousLinearMap
      { toFun := fun om => raisedKoszulPairing (I := I) g₀ g₁ x om
        map_add' := raisedKoszulPairing_add g₀ g₁ x
        map_smul' := raisedKoszulPairing_smul g₀ g₁ x })

@[simp] lemma raisedKoszulFib_apply (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (om : Tensor0SSpace 1 I x) :
    (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from raisedKoszulFib (I := I) g₀ g₁ x) om =
      raisedKoszulPairing (I := I) g₀ g₁ x om := rfl

theorem sharpFlatRaiseEndo_contMDiff (g₀ g₁ : SmoothRiemannianMetric I M) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun x : M => TotalSpace.mk' (E →L[ℝ] E)
        (E := fun z : M => TangentSpace I z →L[ℝ] TangentSpace I z) x
        (sharpFlatRaiseEndo (I := I) g₀ g₁ x)) := by
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (F₁ := E) (V₁ := fun z : M => TangentSpace I z)
    (F₂ := E) (V₂ := fun z : M => TangentSpace I z)
    (φ := fun x : M => sharpFlatRaiseEndo (I := I) g₀ g₁ x)
  intro Y
  have hflatY : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 1 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SModel 1 ℝ E)
        (E := fun z : M => Tensor0SSpace 1 I z) x
        (g0FlatCLM (I := I) g₁ x (Y x))) :=
    ContMDiff.clm_bundle_apply (b := id)
      (g0FlatField_contMDiff (I := I) g₁) Y.contMDiff
  have hsharpflatY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) x
        (inverseMetricSharpFib (I := I) g₀ x (g0FlatCLM (I := I) g₁ x (Y x)))) :=
    ContMDiff.clm_bundle_apply (b := id)
      (inverseMetricSharpField_contMDiff (I := I) g₀) hflatY
  refine hsharpflatY.congr (fun x => ?_)
  rfl

theorem raisedKoszulFib_contMDiff (g₀ g₁ : SmoothRiemannianMetric I M) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 1 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel 1 2 ℝ E)
        (E := fun z : M => TensorRSSpace 1 2 I z) x (raisedKoszulFib (I := I) g₀ g₁ x)) := by
  classical
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (F₁ := Tensor0SModel 1 ℝ E) (V₁ := fun x : M => Tensor0SSpace 1 I x)
    (F₂ := Tensor0SModel 2 ℝ E) (V₂ := fun x : M => Tensor0SSpace 2 I x)
    (φ := fun x : M => (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from
      raisedKoszulFib (I := I) g₀ g₁ x))
  intro om
  letI := Tensor0SBundle.tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 2
  have hsec : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
        (E := fun z : M => Tensor0SSpace 2 I z) x
        (raisedKoszulPairing (I := I) g₀ g₁ x (om x))) := by
    refine (contMDiff_multilinearSection_iff_coord (𝕜 := ℝ) (F := E)
      (E := (TangentSpace I : M → Type _)) (IB := I) (n := (∞ : WithTop ℕ∞)) (Module.finBasis ℝ E)
      (fun x : M => (raisedKoszulPairing (I := I) g₀ g₁ x (om x) :
        Bundle.continuousMultilinearMap ℝ 2 E (TangentSpace I) x))).mpr ?_
    intro σ x₀
    set b := Module.finBasis ℝ E with hb
    set e₁ := trivializationAt E (TangentSpace I : M → Type _) x₀ with he₁def
    have he₁ : x₀ ∈ e₁.baseSet := mem_baseSet_trivializationAt E (TangentSpace I) x₀
    have hframe := e₁.isLocalFrameOn_localFrame_baseSet I (⊤ : ℕ∞) b
    obtain ⟨Y, hY⟩ := hframe.exists_contMDiffSection_eqOn_nhd e₁.open_baseSet he₁
    have hvec : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
        (fun x : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) x
          (raisedKoszulVec (I := I) g₀ g₁ x (Y (σ 0) x) (Y (σ 1) x))) := by
      have hcd : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
          (fun x : M => (⟨x, PDE.DeTurck.connDiff (I := I) g₁ g₀ x (Y (σ 0) x) (Y (σ 1) x)⟩ :
            TotalSpace E (TangentSpace I))) :=
        PDE.DeTurck.connDiff_contMDiff (I := I) g₁ g₀ (Y (σ 0)).contMDiff (Y (σ 1)).contMDiff
      have hcomp : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
          (fun x : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) x
            (sharpFlatRaiseEndo (I := I) g₀ g₁ x
              (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (Y (σ 0) x) (Y (σ 1) x)))) :=
        ContMDiff.clm_bundle_apply (b := id)
          (sharpFlatRaiseEndo_contMDiff (I := I) g₀ g₁) hcd
      refine hcomp.congr (fun x => ?_)
      rw [raisedKoszulVec_apply]
      rfl
    have hscalar : ContMDiffAt I 𝓘(ℝ, ℝ) ∞
        (fun x : M => Tensor0SSpace.toModel (om x)
          (fun _ : Fin 1 => raisedKoszulVec (I := I) g₀ g₁ x (Y (σ 0) x) (Y (σ 1) x))) x₀ :=
      TensorMultilinear.contMDiffAt_section_apply (n := 1) (x₀ := x₀)
        (fun x : M => om x) (om.contMDiff x₀)
        (fun _ : Fin 1 => fun x : M => raisedKoszulVec (I := I) g₀ g₁ x (Y (σ 0) x) (Y (σ 1) x))
        (fun _ => (hvec x₀))
    refine hscalar.congr_of_eventuallyEq ?_
    have h_base₁ : ∀ᶠ x in 𝓝 x₀, x ∈ e₁.baseSet := e₁.open_baseSet.mem_nhds he₁
    filter_upwards [h_base₁, hY] with x hx₁ hYx
    rw [continuousMultilinearMap_basis_repr]
    have hframe0 : e₁.symmL ℝ x (b (σ 0)) = (Y (σ 0)) x := by
      rw [hYx (σ 0), Trivialization.localFrame_apply_of_mem_baseSet (hx := hx₁)]
      simp [Trivialization.basisAt]
    have hframe1 : e₁.symmL ℝ x (b (σ 1)) = (Y (σ 1)) x := by
      rw [hYx (σ 1), Trivialization.localFrame_apply_of_mem_baseSet (hx := hx₁)]
      simp [Trivialization.basisAt]
    change (raisedKoszulPairing (I := I) g₀ g₁ x (om x))
        (fun j : Fin 2 => e₁.symmL ℝ x (b (σ j))) = _
    rw [raisedKoszulPairing_apply]
    rw [Tensor0SSpace.toModel, tensor0SSpace_continuousLinearEquiv_apply]
    rw [hframe0, hframe1]
    rfl
  refine hsec.congr ?_
  intro x
  rfl

def raisedKoszul (g₀ g₁ : SmoothRiemannianMetric I M) : SmoothCcTensor g₀ 1 2 where
  toSection :=
    { toFun := fun x : M => raisedKoszulFib (I := I) g₀ g₁ x
      contMDiff_toFun := raisedKoszulFib_contMDiff (I := I) g₀ g₁ }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

@[simp] lemma raisedKoszul_toSection (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) :
    (raisedKoszul (I := I) g₀ g₁).toSection x = raisedKoszulFib (I := I) g₀ g₁ x := rfl

def symmSCovGrad3 (g₀ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2) :
    SmoothCcTensor g₀ 0 3 :=
  covGrad (I := I) (M := M) g₀ 0 2 (symmS (I := I) g₀ T)

@[simp] lemma symmSCovGrad3_def (g₀ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2) :
    symmSCovGrad3 (I := I) (M := M) g₀ T =
      covGrad (I := I) (M := M) g₀ 0 2 (symmS (I := I) g₀ T) := rfl

set_option linter.unusedSectionVars false in
private lemma connDiffPairing_eq_raisedKoszul_sharpFlat (g₀ g₁ : SmoothRiemannianMetric I M)
    (x : M) (om : Tensor0SSpace 1 I x) (YZ : Fin 2 → TangentSpace I x) :
    om (fun _ : Fin 1 => PDE.DeTurck.connDiff (I := I) g₁ g₀ x (YZ 0) (YZ 1)) =
      (g0FlatCLM (I := I) g₀ x (inverseMetricSharpFib (I := I) g₁ x om))
        (fun _ : Fin 1 => raisedKoszulVec (I := I) g₀ g₁ x (YZ 0) (YZ 1)) := by
  set D : TangentSpace I x := PDE.DeTurck.connDiff (I := I) g₁ g₀ x (YZ 0) (YZ 1) with hD
  set u : TangentSpace I x := inverseMetricSharpFib (I := I) g₁ x om with hu
  have hLHS : om (fun _ : Fin 1 => D) = g₁.inner x u D := by
    rw [← cotangentToDual_apply (I := I) (x := x) om D]
    rw [show cotangentToDual (I := I) (x := x) om D
          = cotangentToDualLinear (I := I) (x := x) om D from rfl]
    rw [← inverseMetricSharpFib_inner (I := I) g₁ x om D]
  rw [hLHS]
  set P : TangentSpace I x := raisedKoszulVec (I := I) g₀ g₁ x (YZ 0) (YZ 1) with hPdef
  rw [show (g0FlatCLM (I := I) g₀ x u) (fun _ : Fin 1 => P)
        = cotangentToDual (I := I) (x := x) (g0FlatCLM (I := I) g₀ x u) P from
      (cotangentToDual_apply (I := I) (x := x) (g0FlatCLM (I := I) g₀ x u) P).symm]
  rw [cotangentToDual_g0FlatCLM (I := I) g₀ x u P]
  rw [g₀.symm x u P]
  have hPval : P = inverseMetricSharpFib (I := I) g₀ x (g0FlatCLM (I := I) g₁ x D) := by
    rw [hPdef, raisedKoszulVec_apply]
  have hPinner : g₀.inner x P u = cotangentToDual (I := I) (x := x) (g0FlatCLM (I := I) g₁ x D) u := by
    rw [hPval, ← cotangentToDualLinear_apply (I := I) (x := x)]
    rw [inverseMetricSharpFib_inner (I := I) g₀ x (g0FlatCLM (I := I) g₁ x D) u]
  rw [hPinner, cotangentToDual_g0FlatCLM (I := I) g₁ x D u]
  rw [g₁.symm x D u, hu]

set_option linter.unusedSectionVars false in
theorem connDiffSection_eq_appCcRS_raisedKoszul_sharpFlatEndoCc
    (g₀ g₁ : SmoothRiemannianMetric I M) :
    connDiffSection (I := I) g₁ g₀ =
      appCcRS (I := I) (M := M) g₀ 1 1 2
        (raisedKoszul (I := I) g₀ g₁) (sharpFlatEndoCc (I := I) g₀ g₁) := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [connDiffSection_toSection, appCcRS_toSection, sharpFlatEndoCc_toSection,
    raisedKoszul_toSection]
  apply tensorRSSpace_ext 1 2 x
  intro om
  apply ContinuousMultilinearMap.ext
  intro YZ
  rw [ContinuousLinearMap.comp_apply]
  rw [connDiffFib_apply_eval]
  rw [show (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from
        raisedKoszulFib (I := I) g₀ g₁ x)
      ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
        TensorRSSpace.ofCLM
          ((g0FlatCLM (I := I) g₀ x).comp (inverseMetricSharpFib (I := I) g₁ x))) om)
      = raisedKoszulPairing (I := I) g₀ g₁ x
          ((g0FlatCLM (I := I) g₀ x).comp (inverseMetricSharpFib (I := I) g₁ x) om) from rfl]
  rw [raisedKoszulPairing_apply]
  rw [ContinuousLinearMap.comp_apply]
  exact connDiffPairing_eq_raisedKoszul_sharpFlat (I := I) g₀ g₁ x om YZ

set_option linter.unusedSectionVars false in
theorem rfns_iteratedCovGrad_connDiffSection_diagonalProductGrid_le
    (g₀ g₁ : SmoothRiemannianMetric I M) (j : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + j) x
        ((iteratedCovGrad (I := I) g₀ 1 2 j (connDiffSection (I := I) g₁ g₀)).toSection x) ≤
      appCcGdiag (E := E) j *
        ∑ i ∈ Finset.range (j + 1),
          riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + i) x
              ((iteratedCovGrad (I := I) g₀ 1 2 i (raisedKoszul (I := I) g₀ g₁)).toSection x) *
            ∑ l ∈ Finset.range (j + 1 - i),
              riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + l) x
                ((iteratedCovGrad (I := I) g₀ 1 1 l
                  (sharpFlatEndoCc (I := I) g₀ g₁)).toSection x) := by
  rw [connDiffSection_eq_appCcRS_raisedKoszul_sharpFlatEndoCc (I := I) g₀ g₁]
  exact rfns_iteratedCovGrad_appCcRS_diagonalProductGrid_rankLeft_le (I := I) (M := M) g₀ j 1 1 2
    (raisedKoszul (I := I) g₀ g₁) (sharpFlatEndoCc (I := I) g₀ g₁) x

set_option linter.unusedSectionVars false in
theorem rfns_iteratedCovGrad_connDiffSection_le
    (g₀ g₁ : SmoothRiemannianMetric I M) (j : ℕ) (x : M)
    (B S : ℕ → ℝ)
    (hKos : ∀ i ≤ j,
      riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + i) x
          ((iteratedCovGrad (I := I) g₀ 1 2 i (raisedKoszul (I := I) g₀ g₁)).toSection x) ≤ B i)
    (hSharp : ∀ l ≤ j,
      riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + l) x
          ((iteratedCovGrad (I := I) g₀ 1 1 l
            (sharpFlatEndoCc (I := I) g₀ g₁)).toSection x) ≤ S l)
    (hS0 : ∀ l, 0 ≤ S l) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + j) x
        ((iteratedCovGrad (I := I) g₀ 1 2 j (connDiffSection (I := I) g₁ g₀)).toSection x) ≤
      appCcGdiag (E := E) j *
        ∑ i ∈ Finset.range (j + 1), B i * ∑ l ∈ Finset.range (j + 1 - i), S l := by
  refine (rfns_iteratedCovGrad_connDiffSection_diagonalProductGrid_le (I := I) (M := M)
    g₀ g₁ j x).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (appCcGdiag_nonneg (E := E) j)
  refine Finset.sum_le_sum (fun i hi => ?_)
  have hile : i ≤ j := by simp only [Finset.mem_range] at hi; omega
  have hKi_nn : (0 : ℝ) ≤ riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + i) x
      ((iteratedCovGrad (I := I) g₀ 1 2 i (raisedKoszul (I := I) g₀ g₁)).toSection x) :=
    riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 1 (2 + i) x _
  have hinner : (∑ l ∈ Finset.range (j + 1 - i),
        riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + l) x
          ((iteratedCovGrad (I := I) g₀ 1 1 l
            (sharpFlatEndoCc (I := I) g₀ g₁)).toSection x)) ≤
      ∑ l ∈ Finset.range (j + 1 - i), S l := by
    refine Finset.sum_le_sum (fun l hl => ?_)
    have hlj : l ≤ j := by simp only [Finset.mem_range] at hl; omega
    exact hSharp l hlj
  have hinnerS_nn : (0 : ℝ) ≤ ∑ l ∈ Finset.range (j + 1 - i), S l :=
    Finset.sum_nonneg (fun l _ => hS0 l)
  calc riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + i) x
          ((iteratedCovGrad (I := I) g₀ 1 2 i (raisedKoszul (I := I) g₀ g₁)).toSection x) *
        ∑ l ∈ Finset.range (j + 1 - i),
          riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + l) x
            ((iteratedCovGrad (I := I) g₀ 1 1 l
              (sharpFlatEndoCc (I := I) g₀ g₁)).toSection x)
      ≤ riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 1 2 i (raisedKoszul (I := I) g₀ g₁)).toSection x) *
          ∑ l ∈ Finset.range (j + 1 - i), S l :=
        mul_le_mul_of_nonneg_left hinner hKi_nn
    _ ≤ B i * ∑ l ∈ Finset.range (j + 1 - i), S l :=
        mul_le_mul_of_nonneg_right (hKos i hile) hinnerS_nn

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
