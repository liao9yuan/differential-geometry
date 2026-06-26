import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.GreenIdentityAndIBP.TensorDirichletCurrentGreenIdentityRS
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.RiemannianFiberNormSqTensorInnerBridge
import DifferentialGeometry.Tensor.RSTensor.Derivation.Contract
import DifferentialGeometry.Geometry.Curvature.Order2Defect.MetricTraceFrame

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle CovariantDerivative
open scoped Manifold Topology ContDiff ENNReal BigOperators Matrix

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Tensor.TensorRSRiemannian
open Tensor0SNabla TensorRSNabla TensorMetricLowering

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

set_option linter.unusedSectionVars false in
theorem tensorInnerPointwise_0s_succ_eq_sum_curryLeft_orthoFrame
    (g : SmoothRiemannianMetric I M) (x : M) (s : ℕ)
    (frame : Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I x))
    (horth : ∀ a b, g.inner x (frame a) (frame b) = if a = b then 1 else 0)
    (S T : ContinuousMultilinearMap ℝ (fun _ : Fin (s + 1) => E) ℝ) :
    tensorInnerPointwise_0s (I := I) (M := M) (s + 1) g x S T =
      ∑ a : Fin (Module.finrank ℝ E),
        tensorInnerPointwise_0s (I := I) (M := M) s g x
          (S.curryLeft (frame a)) (T.curryLeft (frame a)) := by
  classical
  rw [tensorInnerPointwise_0s_eq_diag_sum_orthoFrame (I := I) (M := M) g x (s + 1) frame horth S T]
  rw [show (∑ a : Fin (Module.finrank ℝ E),
        tensorInnerPointwise_0s (I := I) (M := M) s g x
          (S.curryLeft (frame a)) (T.curryLeft (frame a))) =
      ∑ a : Fin (Module.finrank ℝ E),
        ∑ φ : Fin s → Fin (Module.finrank ℝ E),
          (S.curryLeft (frame a)) (fun k => frame (φ k)) *
            (T.curryLeft (frame a)) (fun k => frame (φ k)) from by
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [tensorInnerPointwise_0s_eq_diag_sum_orthoFrame (I := I) (M := M) g x s frame horth]]
  rw [← (Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (s + 1) => Fin (Module.finrank ℝ E)))
        (fun pr : Fin (Module.finrank ℝ E) × (Fin s → Fin (Module.finrank ℝ E)) =>
          (S.curryLeft (frame pr.1)) (fun k => frame (pr.2 k)) *
            (T.curryLeft (frame pr.1)) (fun k => frame (pr.2 k)))
        (fun ψ : Fin (s + 1) → Fin (Module.finrank ℝ E) =>
          S (fun k => frame (ψ k)) * T (fun k => frame (ψ k)))
        ?_)]
  · rw [Fintype.sum_prod_type]
  · intro pr
    simp only [Fin.consEquiv_apply, ContinuousMultilinearMap.curryLeft_apply]
    have hcons : (Fin.cons (frame pr.1) (fun k => frame (pr.2 k)) : Fin (s + 1) → E) =
        fun k => frame ((Fin.cons pr.1 pr.2 : Fin (s + 1) → Fin (Module.finrank ℝ E)) k) := by
      funext k
      refine Fin.cases ?_ ?_ k
      · simp
      · intro j; simp
    rw [hcons]

set_option linter.unusedSectionVars false in
lemma contract_covariant_smul_left (s : ℕ) (x : M) (c : ℝ) (v : TangentSpace I x)
    (A : TensorRSSpace 0 (s + 1) I x) :
    contract_covariant 0 s x (c • v) A =
      c • contract_covariant 0 s x v A := by
  classical
  have hmodel : ∀ w : E,
      model_interior_product (𝕜 := ℝ) (E := E) s w = model_interior_bilinear ℝ E s w :=
    fun w => rfl
  unfold contract_covariant
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe]
  rw [hmodel, hmodel, map_smul, map_smul, ContinuousLinearMap.smul_apply, map_smul]

set_option linter.unusedSectionVars false in
lemma contract_covariant_add_left (s : ℕ) (x : M) (v w : TangentSpace I x)
    (A : TensorRSSpace 0 (s + 1) I x) :
    contract_covariant 0 s x (v + w) A =
      contract_covariant 0 s x v A + contract_covariant 0 s x w A := by
  classical
  have hmodel : ∀ z : E,
      model_interior_product (𝕜 := ℝ) (E := E) s z = model_interior_bilinear ℝ E s z :=
    fun z => rfl
  unfold contract_covariant
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe]
  rw [hmodel, hmodel, hmodel, map_add, map_add, ContinuousLinearMap.add_apply, map_add]

noncomputable def codiffPsi
    (g : SmoothRiemannianMetric I M) (s : ℕ) (V : SmoothCcTensor g 0 (s + 1)) (y : M) :
    TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] TensorRSSpace 0 s I y :=
  TensorialAt.mkHom₂
    (I := I) (F := E) (F' := E)
    (V := (TangentSpace I : M → Type _))
    (V' := (TangentSpace I : M → Type _))
    (A := TensorRSSpace 0 s I y)
    (Φ := fun (X Y : Π b : M, TangentSpace I b) =>
      contract_covariant 0 s y (Y y)
        ((TensorRSNabla.tensorRSCovariantDerivative I M 0 (s + 1)
            (LeviCivita (I := I) g)).toFun (fun z : M => V.toSection z) y (X y)))
    y
    (fun Y _hY => by
      refine ⟨?_, ?_⟩
      · intro f X _hf _hX
        have hsmul : (f • X : Π b : M, TangentSpace I b) y = f y • X y := rfl
        change contract_covariant 0 s y (Y y)
            ((TensorRSNabla.tensorRSCovariantDerivative I M 0 (s + 1)
              (LeviCivita (I := I) g)).toFun (fun z : M => V.toSection z) y ((f • X) y)) =
          f y • contract_covariant 0 s y (Y y)
            ((TensorRSNabla.tensorRSCovariantDerivative I M 0 (s + 1)
              (LeviCivita (I := I) g)).toFun (fun z : M => V.toSection z) y (X y))
        rw [hsmul, ContinuousLinearMap.map_smul, ContinuousLinearMap.map_smul]
      · intro X X' _hX _hX'
        have hadd : (X + X' : Π b : M, TangentSpace I b) y = X y + X' y := rfl
        change contract_covariant 0 s y (Y y)
            ((TensorRSNabla.tensorRSCovariantDerivative I M 0 (s + 1)
              (LeviCivita (I := I) g)).toFun (fun z : M => V.toSection z) y ((X + X') y)) =
          contract_covariant 0 s y (Y y)
            ((TensorRSNabla.tensorRSCovariantDerivative I M 0 (s + 1)
              (LeviCivita (I := I) g)).toFun (fun z : M => V.toSection z) y (X y)) +
          contract_covariant 0 s y (Y y)
            ((TensorRSNabla.tensorRSCovariantDerivative I M 0 (s + 1)
              (LeviCivita (I := I) g)).toFun (fun z : M => V.toSection z) y (X' y))
        rw [hadd, ContinuousLinearMap.map_add, ContinuousLinearMap.map_add])
    (fun X _hX => by
      refine ⟨?_, ?_⟩
      · intro f Y _hf _hY
        have hsmul : (f • Y : Π b : M, TangentSpace I b) y = f y • Y y := rfl
        change contract_covariant 0 s y ((f • Y) y)
            ((TensorRSNabla.tensorRSCovariantDerivative I M 0 (s + 1)
              (LeviCivita (I := I) g)).toFun (fun z : M => V.toSection z) y (X y)) =
          f y • contract_covariant 0 s y (Y y)
            ((TensorRSNabla.tensorRSCovariantDerivative I M 0 (s + 1)
              (LeviCivita (I := I) g)).toFun (fun z : M => V.toSection z) y (X y))
        rw [hsmul]
        exact contract_covariant_smul_left s y (f y) (Y y) _
      · intro Y Y' _hY _hY'
        have hadd : (Y + Y' : Π b : M, TangentSpace I b) y = Y y + Y' y := rfl
        change contract_covariant 0 s y ((Y + Y') y)
            ((TensorRSNabla.tensorRSCovariantDerivative I M 0 (s + 1)
              (LeviCivita (I := I) g)).toFun (fun z : M => V.toSection z) y (X y)) =
          contract_covariant 0 s y (Y y)
            ((TensorRSNabla.tensorRSCovariantDerivative I M 0 (s + 1)
              (LeviCivita (I := I) g)).toFun (fun z : M => V.toSection z) y (X y)) +
          contract_covariant 0 s y (Y' y)
            ((TensorRSNabla.tensorRSCovariantDerivative I M 0 (s + 1)
              (LeviCivita (I := I) g)).toFun (fun z : M => V.toSection z) y (X y))
        rw [hadd]
        exact contract_covariant_add_left s y (Y y) (Y' y) _)

set_option linter.unusedSectionVars false in
theorem codiffPsi_apply
    (g : SmoothRiemannianMetric I M) (s : ℕ) (V : SmoothCcTensor g 0 (s + 1)) (y : M)
    {X Y : Π b : M, TangentSpace I b}
    (hX : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun z : M => TotalSpace.mk' E (E := fun w : M => TangentSpace I w) z (X z)) y)
    (hY : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun z : M => TotalSpace.mk' E (E := fun w : M => TangentSpace I w) z (Y z)) y) :
    codiffPsi (I := I) (M := M) g s V y (X y) (Y y) =
      contract_covariant 0 s y (Y y)
        ((TensorRSNabla.tensorRSCovariantDerivative I M 0 (s + 1)
            (LeviCivita (I := I) g)).toFun (fun z : M => V.toSection z) y (X y)) := by
  classical
  unfold codiffPsi
  exact TensorialAt.mkHom₂_apply _ _ hX hY

def covDivergenceRaw
    (g : SmoothRiemannianMetric I M) (s : ℕ) (V : SmoothCcTensor g 0 (s + 1)) (b : M) :
    TensorRSSpace 0 s I b :=
  ∑ i : Fin (Module.finrank ℝ E),
    codiffPsi (I := I) (M := M) g s V b
      (smoothOrthoFrame (I := I) g b i b) (smoothOrthoFrame (I := I) g b i b)

def covDivergenceFixedFrame
    (g : SmoothRiemannianMetric I M) (s : ℕ) (V : SmoothCcTensor g 0 (s + 1))
    (B : Fin (Module.finrank ℝ E) → Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (b : M) :
    TensorRSSpace 0 s I b :=
  ∑ i : Fin (Module.finrank ℝ E),
    contract_covariant 0 s b (B i b)
      (tensorCovDerivAt (I := I) (M := M) g 0 (s + 1) V b (B i b))

set_option linter.unusedSectionVars false in
lemma covDivergenceFixedFrame_eq_sum_section
    (g : SmoothRiemannianMetric I M) (s : ℕ) (V : SmoothCcTensor g 0 (s + 1))
    (B : Fin (Module.finrank ℝ E) → Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (b : M) :
    covDivergenceFixedFrame (I := I) (M := M) g s V B b =
      ∑ i : Fin (Module.finrank ℝ E),
        (contract_covariantField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (n := ∞) 0 s
          (covDerivAlongVFSectionRS (I := I) (M := M) g 0 (s + 1) V.toSection (B i)) (B i)) b :=
  rfl

set_option linter.unusedSectionVars false in
lemma covDivergenceFixedFrame_contMDiff
    (g : SmoothRiemannianMetric I M) (s : ℕ) (V : SmoothCcTensor g 0 (s + 1))
    (B : Fin (Module.finrank ℝ E) → Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 0 s ℝ E)) ∞
      (fun b : M => TotalSpace.mk' (TensorRSModel 0 s ℝ E)
        (E := fun z : M => TensorRSSpace 0 s I z) b
        (covDivergenceFixedFrame (I := I) (M := M) g s V B b)) := by
  classical
  have hsummand : ∀ i : Fin (Module.finrank ℝ E),
      ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 0 s ℝ E)) ∞
        (fun b : M => TotalSpace.mk' (TensorRSModel 0 s ℝ E)
          (E := fun z : M => TensorRSSpace 0 s I z) b
          ((contract_covariantField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (n := ∞) 0 s
            (covDerivAlongVFSectionRS (I := I) (M := M) g 0 (s + 1) V.toSection (B i))
            (B i)) b)) :=
    fun i =>
      (contract_covariantField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (n := ∞) 0 s
        (covDerivAlongVFSectionRS (I := I) (M := M) g 0 (s + 1) V.toSection (B i)) (B i)).contMDiff
  have heq : (fun b : M => TotalSpace.mk' (TensorRSModel 0 s ℝ E)
        (E := fun z : M => TensorRSSpace 0 s I z) b
        (covDivergenceFixedFrame (I := I) (M := M) g s V B b)) =
      (fun b : M => TotalSpace.mk' (TensorRSModel 0 s ℝ E)
        (E := fun z : M => TensorRSSpace 0 s I z) b
        (∑ i : Fin (Module.finrank ℝ E),
          (contract_covariantField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (n := ∞) 0 s
            (covDerivAlongVFSectionRS (I := I) (M := M) g 0 (s + 1) V.toSection (B i))
            (B i)) b)) := by
    funext b
    rw [covDivergenceFixedFrame_eq_sum_section (I := I) (M := M) g s V B b]
  rw [heq]
  exact ContMDiff.sum_section (fun i _ => hsummand i)

def smoothOrthoFrameSection
    (g : SmoothRiemannianMetric I M) (x₀ : M) (i : Fin (Module.finrank ℝ E)) :
    Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
  ⟨fun b : M => smoothOrthoFrame (I := I) g x₀ i b, smoothOrthoFrame_smooth (I := I) g x₀ i⟩

set_option linter.unusedSectionVars false in
@[simp] lemma smoothOrthoFrameSection_apply
    (g : SmoothRiemannianMetric I M) (x₀ : M) (i : Fin (Module.finrank ℝ E)) (b : M) :
    smoothOrthoFrameSection (I := I) (M := M) g x₀ i b =
      smoothOrthoFrame (I := I) g x₀ i b := rfl

set_option linter.unusedSectionVars false in
lemma covDivergenceRaw_eq_codiffPsi_smoothOrthoFrame_trace
    (g : SmoothRiemannianMetric I M) (s : ℕ) (V : SmoothCcTensor g 0 (s + 1)) (b : M)
    (B : Fin (Module.finrank ℝ E) → TangentSpace I b)
    (hB_orth : ∀ i j : Fin (Module.finrank ℝ E),
      g.inner b (B i) (B j) = if i = j then (1 : ℝ) else 0) :
    covDivergenceRaw (I := I) (M := M) g s V b =
      ∑ i : Fin (Module.finrank ℝ E),
        codiffPsi (I := I) (M := M) g s V b (B i) (B i) := by
  classical
  have hb_base : b ∈ (trivializationAt E (TangentSpace I) b).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) b
  have hcentral : ∀ i j : Fin (Module.finrank ℝ E),
      g.inner b (smoothOrthoFrame (I := I) g b i b) (smoothOrthoFrame (I := I) g b j b) =
        if i = j then (1 : ℝ) else 0 :=
    fun i j => smoothOrthoFrame_orthonormal_at_center (I := I) g b i j
  have hcentral_trace := orthonormal_basis_bilin_trace_chartα (I := I)
    (A := TensorRSSpace 0 s I b) g b hb_base (codiffPsi (I := I) (M := M) g s V b)
    (fun i => smoothOrthoFrame (I := I) g b i b) hcentral
  have hB_trace := orthonormal_basis_bilin_trace_chartα (I := I)
    (A := TensorRSSpace 0 s I b) g b hb_base (codiffPsi (I := I) (M := M) g s V b) B hB_orth
  rw [covDivergenceRaw, hcentral_trace, ← hB_trace]

set_option linter.unusedSectionVars false in
lemma covDivergenceRaw_eq_fixedFrame_on_nbhd
    (g : SmoothRiemannianMetric I M) (s : ℕ) (V : SmoothCcTensor g 0 (s + 1)) (x₀ : M)
    {b : M} (hb : b ∈ smoothOrthoFrameNbhd (I := I) (M := M) x₀) :
    covDivergenceRaw (I := I) (M := M) g s V b =
      covDivergenceFixedFrame (I := I) (M := M) g s V
        (fun i => smoothOrthoFrameSection (I := I) (M := M) g x₀ i) b := by
  classical
  have hB_orth : ∀ i j : Fin (Module.finrank ℝ E),
      g.inner b (smoothOrthoFrame (I := I) g x₀ i b) (smoothOrthoFrame (I := I) g x₀ j b) =
        if i = j then (1 : ℝ) else 0 :=
    fun i j => smoothOrthoFrame_orthonormal (I := I) g x₀ hb i j
  rw [covDivergenceRaw_eq_codiffPsi_smoothOrthoFrame_trace (I := I) (M := M) g s V b
    (fun i => smoothOrthoFrame (I := I) g x₀ i b) hB_orth]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have hSmooth_at : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun z : M => TotalSpace.mk' E (E := fun w : M => TangentSpace I w) z
        (smoothOrthoFrame (I := I) g x₀ i z)) b :=
    (smoothOrthoFrame_smooth (I := I) g x₀ i).contMDiffAt.mdifferentiableAt (by simp)
  rw [codiffPsi_apply (I := I) (M := M) g s V b hSmooth_at hSmooth_at]
  rfl

set_option linter.unusedSectionVars false in
theorem covDivergenceRaw_contMDiff
    (g : SmoothRiemannianMetric I M) (s : ℕ) (V : SmoothCcTensor g 0 (s + 1)) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 0 s ℝ E)) ∞
      (fun b : M => TotalSpace.mk' (TensorRSModel 0 s ℝ E)
        (E := fun z : M => TensorRSSpace 0 s I z) b
        (covDivergenceRaw (I := I) (M := M) g s V b)) := by
  classical
  intro x₀
  have h_fixed : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 0 s ℝ E)) ∞
      (fun b : M => TotalSpace.mk' (TensorRSModel 0 s ℝ E)
        (E := fun z : M => TensorRSSpace 0 s I z) b
        (covDivergenceFixedFrame (I := I) (M := M) g s V
          (fun i => smoothOrthoFrameSection (I := I) (M := M) g x₀ i) b)) :=
    covDivergenceFixedFrame_contMDiff (I := I) (M := M) g s V
      (fun i => smoothOrthoFrameSection (I := I) (M := M) g x₀ i)
  have h_fixed_at := h_fixed x₀
  have h_eventuallyEq :
      (fun b : M => TotalSpace.mk' (TensorRSModel 0 s ℝ E)
        (E := fun z : M => TensorRSSpace 0 s I z) b
        (covDivergenceRaw (I := I) (M := M) g s V b)) =ᶠ[𝓝 x₀]
      (fun b : M => TotalSpace.mk' (TensorRSModel 0 s ℝ E)
        (E := fun z : M => TensorRSSpace 0 s I z) b
        (covDivergenceFixedFrame (I := I) (M := M) g s V
          (fun i => smoothOrthoFrameSection (I := I) (M := M) g x₀ i) b)) := by
    filter_upwards [smoothOrthoFrameNbhd_mem_nhds (I := I) (M := M) x₀] with b hb
    exact congrArg (TotalSpace.mk' (TensorRSModel 0 s ℝ E)
      (E := fun z : M => TensorRSSpace 0 s I z) b)
      (covDivergenceRaw_eq_fixedFrame_on_nbhd (I := I) (M := M) g s V x₀ hb)
  exact h_fixed_at.congr_of_eventuallyEq h_eventuallyEq

set_option linter.unusedSectionVars false in
lemma covDivergenceRaw_eq_zero_off_tsupport
    (g : SmoothRiemannianMetric I M) (s : ℕ) (V : SmoothCcTensor g 0 (s + 1))
    {b : M} (hb : b ∉ tsupport V.toFun) :
    covDivergenceRaw (I := I) (M := M) g s V b = 0 := by
  classical
  rw [covDivergenceRaw]
  refine Finset.sum_eq_zero (fun i _ => ?_)
  have hzero : (TensorRSNabla.tensorRSCovariantDerivative I M 0 (s + 1)
      (LeviCivita (I := I) g)).toFun (fun z : M => V.toSection z) b
        (smoothOrthoFrame (I := I) g b i b) = 0 := by
    have := tensorCovDerivAt_eq_zero_off_tsupport (I := I) (M := M) g 0 (s + 1) V hb
      (smoothOrthoFrame (I := I) g b i b)
    exact this
  have hSmooth_at : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun z : M => TotalSpace.mk' E (E := fun w : M => TangentSpace I w) z
        (smoothOrthoFrame (I := I) g b i z)) b :=
    (smoothOrthoFrame_smooth (I := I) g b i).contMDiffAt.mdifferentiableAt (by simp)
  rw [codiffPsi_apply (I := I) (M := M) g s V b hSmooth_at hSmooth_at]
  rw [hzero, map_zero]

set_option linter.unusedSectionVars false in
lemma covDivergenceRaw_toModel_hasCompactSupport
    (g : SmoothRiemannianMetric I M) (s : ℕ) (V : SmoothCcTensor g 0 (s + 1)) :
    HasCompactSupport
      (fun b : M => TensorRSSpace.toModel (covDivergenceRaw (I := I) (M := M) g s V b)) := by
  classical
  refine HasCompactSupport.of_support_subset_isCompact V.hasCompactSupport ?_
  intro b hb
  rw [Function.mem_support] at hb
  by_contra hbnot
  apply hb
  rw [covDivergenceRaw_eq_zero_off_tsupport (I := I) (M := M) g s V hbnot,
    TensorRSSpace.toModel_zero]

noncomputable def covDivergence
    (g : SmoothRiemannianMetric I M) (s : ℕ) (V : SmoothCcTensor g 0 (s + 1)) :
    SmoothCcTensor g 0 s where
  toSection :=
    { toFun := fun b : M => covDivergenceRaw (I := I) (M := M) g s V b
      contMDiff_toFun := covDivergenceRaw_contMDiff (I := I) (M := M) g s V }
  hasCompactSupport := covDivergenceRaw_toModel_hasCompactSupport (I := I) (M := M) g s V

set_option linter.unusedSectionVars false in
@[simp] lemma covDivergence_toSection_apply
    (g : SmoothRiemannianMetric I M) (s : ℕ) (V : SmoothCcTensor g 0 (s + 1)) (b : M) :
    (covDivergence (I := I) (M := M) g s V).toSection b =
      covDivergenceRaw (I := I) (M := M) g s V b := rfl

set_option linter.unusedSectionVars false in
@[simp] lemma covDivergence_toFun_apply
    (g : SmoothRiemannianMetric I M) (s : ℕ) (V : SmoothCcTensor g 0 (s + 1)) (b : M) :
    (covDivergence (I := I) (M := M) g s V).toFun b =
      TensorRSSpace.toModel (covDivergenceRaw (I := I) (M := M) g s V b) := rfl

def oneSidedDirichletForm
    (g : SmoothRiemannianMetric I M) (s : ℕ) (T : SmoothCcTensor g 0 s)
    (V : SmoothCcTensor g 0 (s + 1)) (b : M) :
    TangentSpace I b →ₗ[ℝ] ℝ where
  toFun X := tensorInnerPointwise (I := I) (M := M) g 0 s b
    (TensorRSSpace.toModel (T.toSection b))
    (TensorRSSpace.toModel (contract_covariant 0 s b X (V.toSection b)))
  map_add' X Y := by
    rw [contract_covariant_add_left (I := I) (M := M) s b X Y (V.toSection b),
      TensorRSSpace.toModel_add, tensorInnerPointwise_add_right]
  map_smul' c X := by
    rw [contract_covariant_smul_left (I := I) (M := M) s b c X (V.toSection b),
      TensorRSSpace.toModel_smul, tensorInnerPointwise_smul_right]
    rfl

set_option linter.unusedSectionVars false in
@[simp] lemma oneSidedDirichletForm_apply
    (g : SmoothRiemannianMetric I M) (s : ℕ) (T : SmoothCcTensor g 0 s)
    (V : SmoothCcTensor g 0 (s + 1)) (b : M) (X : TangentSpace I b) :
    oneSidedDirichletForm (I := I) (M := M) g s T V b X =
      tensorInnerPointwise (I := I) (M := M) g 0 s b
        (TensorRSSpace.toModel (T.toSection b))
        (TensorRSSpace.toModel (contract_covariant 0 s b X (V.toSection b))) := rfl

def oneSidedDirichletVF
    (g : SmoothRiemannianMetric I M) (s : ℕ) (T : SmoothCcTensor g 0 s)
    (V : SmoothCcTensor g 0 (s + 1)) (b : M) :
    TangentSpace I b :=
  metricSharp (I := I) g b (oneSidedDirichletForm (I := I) (M := M) g s T V b)

set_option linter.unusedSectionVars false in
lemma inner_oneSidedDirichletVF
    (g : SmoothRiemannianMetric I M) (s : ℕ) (T : SmoothCcTensor g 0 s)
    (V : SmoothCcTensor g 0 (s + 1)) (b : M) (X : TangentSpace I b) :
    g.inner b (oneSidedDirichletVF (I := I) (M := M) g s T V b) X =
      oneSidedDirichletForm (I := I) (M := M) g s T V b X := by
  rw [oneSidedDirichletVF]
  exact inner_metricSharp (I := I) g b (oneSidedDirichletForm (I := I) (M := M) g s T V b) X

set_option linter.unusedSectionVars false in
lemma contract_chartBasis_contMDiffOn
    (g : SmoothRiemannianMetric I M) (s : ℕ) (V : SmoothCcTensor g 0 (s + 1)) (α : M)
    (j : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I (I.prod 𝓘(ℝ, TensorRSModel 0 s ℝ E)) ∞
      (fun b : M => TotalSpace.mk' (TensorRSModel 0 s ℝ E)
        (E := fun y : M => TensorRSSpace 0 s I y) b
        (contract_covariant 0 s b (chartBasisVecFiber (I := I) α j b) (V.toSection b)))
      (trivializationAt E (TangentSpace I) α).baseSet := by
  classical
  letI := tensorRSBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 0 (s + 1)
  letI := tensorRSBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 0 s
  letI := tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 0
  letI := tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) s
  letI := tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (s + 1)
  have hV_on : ContMDiffOn I (I.prod 𝓘(ℝ, TensorRSModel 0 (s + 1) ℝ E)) ∞
      (fun b : M => TotalSpace.mk' (TensorRSModel 0 (s + 1) ℝ E)
        (E := fun y : M => TensorRSSpace 0 (s + 1) I y) b (V.toSection b))
      (trivializationAt E (TangentSpace I) α).baseSet :=
    V.toSection.contMDiff.contMDiffOn
  have hX_on : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => TotalSpace.mk' E (E := fun y : M => TangentSpace I y) b
        (chartBasisVecFiber (I := I) α j b))
      (trivializationAt E (TangentSpace I) α).baseSet :=
    chartBasisVec_contMDiffOn (I := I) α j
  set biop : E →L[ℝ] (TensorRSModel 0 (s + 1) ℝ E →L[ℝ] TensorRSModel 0 s ℝ E) :=
    (ContinuousLinearMap.compL ℝ
      (Tensor0SModel 0 ℝ E) (Tensor0SModel (s + 1) ℝ E) (Tensor0SModel s ℝ E)).comp
      (model_interior_bilinear ℝ E s) with hbiop
  intro x₀ hx₀
  refine ContMDiffWithinAt.mono ?_ (Set.subset_univ _)
  refine ContMDiffAt.contMDiffWithinAt ?_
  rw [Bundle.contMDiffAt_section (F := TensorRSModel 0 s ℝ E)
    (E := fun z : M => TensorRSSpace 0 s I z)]
  have hV_at := (hV_on x₀ hx₀).contMDiffAt
    ((trivializationAt E (TangentSpace I) α).open_baseSet.mem_nhds hx₀)
  have hX_at := (hX_on x₀ hx₀).contMDiffAt
    ((trivializationAt E (TangentSpace I) α).open_baseSet.mem_nhds hx₀)
  have hV' := (Bundle.contMDiffAt_section (F := TensorRSModel 0 (s + 1) ℝ E)
    (E := fun z : M => TensorRSSpace 0 (s + 1) I z) x₀).mp hV_at
  have hX' := (Bundle.contMDiffAt_section (F := E) (E := TangentSpace I) x₀).mp hX_at
  have h_combine :
      ContMDiffAt I 𝓘(ℝ, TensorRSModel 0 s ℝ E) ∞
        (fun b : M => biop
          ((trivializationAt E (TangentSpace I) x₀ ⟨b, chartBasisVecFiber (I := I) α j b⟩).2)
          ((trivializationAt (TensorRSModel 0 (s + 1) ℝ E)
            (fun z : M => TensorRSSpace 0 (s + 1) I z) x₀ ⟨b, V.toSection b⟩).2)) x₀ :=
    ((contMDiffAt_const (c := biop)).clm_apply hX').clm_apply hV'
  refine h_combine.congr_of_eventuallyEq ?_
  have hbase := (trivializationAt E (TangentSpace I) x₀).open_baseSet.mem_nhds
    (mem_baseSet_trivializationAt _ _ x₀)
  filter_upwards [hbase] with b hb
  refine ContinuousLinearMap.ext fun γ => ?_
  refine ContinuousMultilinearMap.ext fun w => ?_
  set sL := (trivializationAt E (TangentSpace I) x₀).symmL ℝ b with hsL
  set Xtilde : E := (trivializationAt E (TangentSpace I) x₀ ⟨b, chartBasisVecFiber (I := I) α j b⟩).2
    with hXtilde
  set gtilde : Tensor0SSpace 0 I b :=
    (trivializationAt (Tensor0SModel 0 ℝ E) (fun z : M => Tensor0SSpace 0 I z) x₀).symmL ℝ b γ
    with hgtilde
  have h_cLMAt_s : ∀ (Tm : Tensor0SSpace s I b) (v : Fin s → E),
      (trivializationAt (Tensor0SModel s ℝ E)
        (fun z : M => Tensor0SSpace s I z) x₀).continuousLinearMapAt ℝ b Tm v =
      Tm (fun i => sL (v i)) := by
    intro Tm v
    rw [Trivialization.continuousLinearMapAt_apply,
      show ⇑((trivializationAt (Tensor0SModel s ℝ E)
        (fun z : M => Tensor0SSpace s I z) x₀).linearMapAt ℝ b) =
        fun y => (trivializationAt (Tensor0SModel s ℝ E)
          (fun z : M => Tensor0SSpace s I z) x₀ ⟨b, y⟩).2 from
      (trivializationAt _ _ x₀).coe_linearMapAt_of_mem (R := ℝ) hb]
    rfl
  have h_cLMAt_s1 : ∀ (Tm : Tensor0SSpace (s + 1) I b) (v : Fin (s + 1) → E),
      (trivializationAt (Tensor0SModel (s + 1) ℝ E)
        (fun z : M => Tensor0SSpace (s + 1) I z) x₀).continuousLinearMapAt ℝ b Tm v =
      Tm (fun i => sL (v i)) := by
    intro Tm v
    rw [Trivialization.continuousLinearMapAt_apply,
      show ⇑((trivializationAt (Tensor0SModel (s + 1) ℝ E)
        (fun z : M => Tensor0SSpace (s + 1) I z) x₀).linearMapAt ℝ b) =
        fun y => (trivializationAt (Tensor0SModel (s + 1) ℝ E)
          (fun z : M => Tensor0SSpace (s + 1) I z) x₀ ⟨b, y⟩).2 from
      (trivializationAt _ _ x₀).coe_linearMapAt_of_mem (R := ℝ) hb]
    rfl
  change (trivializationAt (Tensor0SModel s ℝ E)
      (fun z : M => Tensor0SSpace s I z) x₀).continuousLinearMapAt ℝ b
      (model_interior_product s (chartBasisVecFiber (I := I) α j b : E)
        ((show Tensor0SSpace 0 I b →L[ℝ] Tensor0SSpace (s + 1) I b from V.toSection b) gtilde)) w =
    (trivializationAt (Tensor0SModel (s + 1) ℝ E)
      (fun z : M => Tensor0SSpace (s + 1) I z) x₀).continuousLinearMapAt ℝ b
      ((show Tensor0SSpace 0 I b →L[ℝ] Tensor0SSpace (s + 1) I b from V.toSection b) gtilde)
      (Fin.cons Xtilde w)
  rw [h_cLMAt_s, h_cLMAt_s1]
  change ((show Tensor0SSpace 0 I b →L[ℝ] Tensor0SSpace (s + 1) I b from V.toSection b) gtilde :
        Tensor0SModel (s + 1) ℝ E)
      (@Fin.cons s (fun _ => E) (chartBasisVecFiber (I := I) α j b : E) (fun i => sL (w i))) =
    ((show Tensor0SSpace 0 I b →L[ℝ] Tensor0SSpace (s + 1) I b from V.toSection b) gtilde)
      (fun i => sL (@Fin.cons s (fun _ => E) Xtilde w i))
  congr 1
  funext i
  refine Fin.cases ?_ ?_ i
  · change (chartBasisVecFiber (I := I) α j b : E) = sL Xtilde
    have h := (trivializationAt E (TangentSpace I) x₀).symmL_continuousLinearMapAt
      (R := ℝ) hb (chartBasisVecFiber (I := I) α j b)
    have hcl : (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ b
        (chartBasisVecFiber (I := I) α j b) = Xtilde := by
      change (trivializationAt E (TangentSpace I) x₀).linearMapAt ℝ b
        (chartBasisVecFiber (I := I) α j b) = _
      rw [(trivializationAt E (TangentSpace I) x₀).coe_linearMapAt_of_mem (R := ℝ) hb]
    rw [hcl] at h
    exact h.symm
  · intro jj
    rfl

set_option linter.unusedSectionVars false in
lemma oneSidedDirichletForm_chartBasis_component_contMDiffOn
    (g : SmoothRiemannianMetric I M) (s : ℕ) (T : SmoothCcTensor g 0 s)
    (V : SmoothCcTensor g 0 (s + 1)) (α : M) (j : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I 𝓘(ℝ) ∞
      (fun b : M => oneSidedDirichletForm (I := I) (M := M) g s T V b
        (chartBasisVecFiber (I := I) α j b))
      (chartAt H α).source := by
  classical
  have hT_lowered : ContMDiffOn I 𝓘(ℝ, Tensor0SModel (0 + s) ℝ E) ∞
      (fun b : M => loweredCompose (I := I) (M := M) g 0 s α b
        (TensorRSSpace.toModel (T.toSection b)))
      (trivializationAt E (TangentSpace I) α).baseSet :=
    TensorMetricLowering.contMDiffOn_loweredCompose (I := I) (M := M) g 0 s T.toSection α
  have hcontract_lowered : ContMDiffOn I 𝓘(ℝ, Tensor0SModel (0 + s) ℝ E) ∞
      (fun b : M => loweredCompose (I := I) (M := M) g 0 s α b
        (TensorRSSpace.toModel
          (contract_covariant 0 s b (chartBasisVecFiber (I := I) α j b) (V.toSection b))))
      (trivializationAt E (TangentSpace I) α).baseSet :=
    TensorMetricLowering.contMDiffOn_loweredCompose_of_section_contMDiffOn
      (I := I) (M := M) g 0 s
      (fun b : M => contract_covariant 0 s b (chartBasisVecFiber (I := I) α j b) (V.toSection b))
      α (contract_chartBasis_contMDiffOn (I := I) (M := M) g s V α j)
  have hinner : ContMDiffOn I 𝓘(ℝ) ∞
      (fun b : M =>
        tensorInnerPointwise (I := I) (M := M) g 0 s b
          (TensorRSSpace.toModel (T.toSection b))
          (TensorRSSpace.toModel
            (contract_covariant 0 s b (chartBasisVecFiber (I := I) α j b) (V.toSection b))))
      (trivializationAt E (TangentSpace I) α).baseSet :=
    DifferentialGeometry.Tensor.TensorRSRiemannian.chartLocal_contMDiff_inner_of_smooth_sections
      (I := I) (M := M) g 0 s
      (fun b : M => T.toSection b)
      (fun b : M => contract_covariant 0 s b (chartBasisVecFiber (I := I) α j b) (V.toSection b))
      α hT_lowered hcontract_lowered
  have hbase_eq : (trivializationAt E (TangentSpace I) α).baseSet =
      (chartAt H α).source :=
    DifferentialGeometry.Integral.Measure.trivializationAt_baseSet_eq_chartAt_source
      (I := I) α
  rw [hbase_eq] at hinner
  refine hinner.congr ?_
  intro b _
  rw [oneSidedDirichletForm_apply]

set_option linter.unusedSectionVars false in
lemma oneSidedDirichletVF_contMDiff
    (g : SmoothRiemannianMetric I M) (s : ℕ) (T : SmoothCcTensor g 0 s)
    (V : SmoothCcTensor g 0 (s + 1)) :
    ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => TotalSpace.mk' E b (oneSidedDirichletVF (I := I) (M := M) g s T V b)) :=
  metricSharp_contMDiff_total (I := I) g
    (cv := fun b : M => oneSidedDirichletForm (I := I) (M := M) g s T V b)
    (fun α j => oneSidedDirichletForm_chartBasis_component_contMDiffOn
      (I := I) (M := M) g s T V α j)

def oneSidedDirichletVFSection
    (g : SmoothRiemannianMetric I M) (s : ℕ) (T : SmoothCcTensor g 0 s)
    (V : SmoothCcTensor g 0 (s + 1)) :
    Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
  ContMDiffSection.mk
    (fun b : M => oneSidedDirichletVF (I := I) (M := M) g s T V b)
    (oneSidedDirichletVF_contMDiff (I := I) (M := M) g s T V)

set_option linter.unusedSectionVars false in
@[simp] lemma oneSidedDirichletVFSection_apply
    (g : SmoothRiemannianMetric I M) (s : ℕ) (T : SmoothCcTensor g 0 s)
    (V : SmoothCcTensor g 0 (s + 1)) (b : M) :
    oneSidedDirichletVFSection (I := I) (M := M) g s T V b =
      oneSidedDirichletVF (I := I) (M := M) g s T V b := rfl

theorem divergence_oneSidedVF_eq
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (T : SmoothCcTensor g 0 s) (V : SmoothCcTensor g 0 (s + 1)) (b : M) :
    divergence_g (I := I) g (oneSidedDirichletVFSection (I := I) (M := M) g s T V) b =
      tensorInnerPointwise (I := I) (M := M) g 0 (s + 1) b
          (TensorRSSpace.toModel ((covGrad (I := I) (M := M) g 0 s T).toSection b))
          (TensorRSSpace.toModel (V.toSection b))
        + tensorInnerPointwise (I := I) (M := M) g 0 s b
          (TensorRSSpace.toModel (T.toSection b))
          (TensorRSSpace.toModel (covDivergenceRaw (I := I) (M := M) g s V b)) := by
  sorry

set_option linter.unusedSectionVars false in
theorem tensorL2Inner_covGrad_eq_neg_tensorL2Inner_covDivergence
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (T : SmoothCcTensor g 0 s) (V : SmoothCcTensor g 0 (s + 1)) :
    tensorL2Inner (I := I) (M := M) g 0 (s + 1)
        (covGrad (I := I) (M := M) g 0 s T).toFun V.toFun =
      - tensorL2Inner (I := I) (M := M) g 0 s
          T.toFun (covDivergence (I := I) (M := M) g s V).toFun := by
  classical
  set μ := riemannianVolumeMeasure (I := I) (M := M) g with hμ_def
  set Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    oneSidedDirichletVFSection (I := I) (M := M) g s T V with hZ_def
  have hZ_cs : HasCompactSupport (Z : ∀ x, TangentSpace I x) :=
    HasCompactSupport.of_compactSpace _
  have hdiv_zero : ∫ b, divergence_g (I := I) g Z b ∂μ = 0 :=
    integral_divergence_eq_zero_of_hasCompactSupport (I := I) g Z hZ_cs
  have hpt : ∀ b : M, divergence_g (I := I) g Z b =
      tensorInnerPointwise (I := I) (M := M) g 0 (s + 1) b
          (TensorRSSpace.toModel ((covGrad (I := I) (M := M) g 0 s T).toSection b))
          (TensorRSSpace.toModel (V.toSection b))
        + tensorInnerPointwise (I := I) (M := M) g 0 s b
          (TensorRSSpace.toModel (T.toSection b))
          (TensorRSSpace.toModel (covDivergenceRaw (I := I) (M := M) g s V b)) := by
    intro b; rw [hZ_def]; exact divergence_oneSidedVF_eq (I := I) (M := M) g s T V b
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt)] at hdiv_zero
  have hcross_cont : Continuous
      (fun b : M => tensorInnerPointwise (I := I) (M := M) g 0 (s + 1) b
          (TensorRSSpace.toModel ((covGrad (I := I) (M := M) g 0 s T).toSection b))
          (TensorRSSpace.toModel (V.toSection b))) :=
    (tensorInnerScalar_contMDiff (I := I) (M := M) g 0 (s + 1)
      (covGrad (I := I) (M := M) g 0 s T).toSection V.toSection).continuous
  have hsecond_cont : Continuous
      (fun b : M => tensorInnerPointwise (I := I) (M := M) g 0 s b
          (TensorRSSpace.toModel (T.toSection b))
          (TensorRSSpace.toModel (covDivergenceRaw (I := I) (M := M) g s V b))) := by
    have heq : (fun b : M => tensorInnerPointwise (I := I) (M := M) g 0 s b
          (TensorRSSpace.toModel (T.toSection b))
          (TensorRSSpace.toModel (covDivergenceRaw (I := I) (M := M) g s V b))) =
        (fun b : M => tensorInnerPointwise (I := I) (M := M) g 0 s b
          (TensorRSSpace.toModel (T.toSection b))
          (TensorRSSpace.toModel ((covDivergence (I := I) (M := M) g s V).toSection b))) := by
      funext b
      rw [covDivergence_toSection_apply]
    rw [heq]
    exact (tensorInnerScalar_contMDiff (I := I) (M := M) g 0 s
      T.toSection (covDivergence (I := I) (M := M) g s V).toSection).continuous
  have hcross_int : Integrable
      (fun b : M => tensorInnerPointwise (I := I) (M := M) g 0 (s + 1) b
          (TensorRSSpace.toModel ((covGrad (I := I) (M := M) g 0 s T).toSection b))
          (TensorRSSpace.toModel (V.toSection b))) μ :=
    Continuous.integrable_of_hasCompactSupport_riemannianVolumeMeasure
      (I := I) g hcross_cont (HasCompactSupport.of_compactSpace _)
  have hsecond_int : Integrable
      (fun b : M => tensorInnerPointwise (I := I) (M := M) g 0 s b
          (TensorRSSpace.toModel (T.toSection b))
          (TensorRSSpace.toModel (covDivergenceRaw (I := I) (M := M) g s V b))) μ :=
    Continuous.integrable_of_hasCompactSupport_riemannianVolumeMeasure
      (I := I) g hsecond_cont (HasCompactSupport.of_compactSpace _)
  rw [integral_add hcross_int hsecond_int] at hdiv_zero
  rw [show tensorL2Inner (I := I) (M := M) g 0 (s + 1)
        (covGrad (I := I) (M := M) g 0 s T).toFun V.toFun =
      ∫ b, tensorInnerPointwise (I := I) (M := M) g 0 (s + 1) b
          (TensorRSSpace.toModel ((covGrad (I := I) (M := M) g 0 s T).toSection b))
          (TensorRSSpace.toModel (V.toSection b)) ∂μ from ?_]
  · rw [show tensorL2Inner (I := I) (M := M) g 0 s
          T.toFun (covDivergence (I := I) (M := M) g s V).toFun =
        ∫ b, tensorInnerPointwise (I := I) (M := M) g 0 s b
            (TensorRSSpace.toModel (T.toSection b))
            (TensorRSSpace.toModel (covDivergenceRaw (I := I) (M := M) g s V b)) ∂μ from ?_]
    · linarith [hdiv_zero]
    · unfold tensorL2Inner
      rw [← hμ_def]
      refine integral_congr_ae (Filter.Eventually.of_forall (fun b => ?_))
      simp only [SmoothCcTensor.toFun_apply, covDivergence_toSection_apply]
  · unfold tensorL2Inner
    rw [← hμ_def]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun b => ?_))
    simp only [SmoothCcTensor.toFun_apply]

end Connection
end Integral
end DifferentialGeometry

end
