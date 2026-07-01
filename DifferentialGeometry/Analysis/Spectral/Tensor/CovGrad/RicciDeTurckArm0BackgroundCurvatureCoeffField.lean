import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RicciDeTurckSectionDifference

noncomputable section

set_option linter.style.setOption false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open Bundle Manifold Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators Matrix

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

def bgKernelBilin (gI gC : SmoothRiemannianMetric I M) (x : M) (p q : TangentSpace I x) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  haveI : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  LinearMap.toContinuousLinearMap
    { toFun := fun v0 => (gI.inner x (riemannOp (LeviCivita (I := I) gC) x v0 p q))
      map_add' := fun v0 v0' => by
        rw [(riemannOp (LeviCivita (I := I) gC) x).map_add v0 v0',
          ContinuousLinearMap.add_apply, ContinuousLinearMap.add_apply, map_add]
      map_smul' := fun c v0 => by
        rw [(riemannOp (LeviCivita (I := I) gC) x).map_smul c v0,
          ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply, map_smul,
          RingHom.id_apply] }

@[simp] theorem bgKernelBilin_apply (gI gC : SmoothRiemannianMetric I M) (x : M)
    (p q v0 v1 : TangentSpace I x) :
    bgKernelBilin (I := I) gI gC x p q v0 v1 =
      gI.inner x (riemannOp (LeviCivita (I := I) gC) x v0 p q) v1 := by
  rw [bgKernelBilin, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk]

def bgSummandFib (gI gC : SmoothRiemannianMetric I M) (x : M) (p q : TangentSpace I x) :
    Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x :=
  haveI : FiniteDimensional ℝ (Tensor0SSpace 2 I x) := inferInstance
  LinearMap.toContinuousLinearMap
    { toFun := fun D =>
        (Tensor0SSpace.toModel D ![(p : E), (q : E)]) •
          Tensor0SSpace.ofModel (I := I) (x := x)
            (bilinFormToModel E (bgKernelBilin (I := I) gI gC x p q))
      map_add' := fun D D' => by
        rw [Tensor0SSpace.toModel_add, ContinuousMultilinearMap.add_apply, add_smul]
      map_smul' := fun c D => by
        rw [Tensor0SSpace.toModel_smul, ContinuousMultilinearMap.smul_apply, smul_eq_mul,
          RingHom.id_apply, mul_smul] }

@[simp] theorem bgSummandFib_toModel (gI gC : SmoothRiemannianMetric I M) (x : M)
    (p q : TangentSpace I x) (D : Tensor0SSpace 2 I x) (v : Fin 2 → E) :
    Tensor0SSpace.toModel (bgSummandFib (I := I) gI gC x p q D) v =
      (Tensor0SSpace.toModel D ![(p : E), (q : E)]) *
        gI.inner x (riemannOp (LeviCivita (I := I) gC) x (v 0) p q) (v 1) := by
  rw [bgSummandFib, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk,
    Tensor0SSpace.toModel_smul, ContinuousMultilinearMap.smul_apply, Tensor0SSpace.toModel_ofModel,
    bilinFormToModel_apply, smul_eq_mul]
  rfl

def bgBiContrFibFixedFrame (gI gC : SmoothRiemannianMetric I M)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b) (x : M) :
    Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x :=
  (2 : ℝ) • ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
    bgSummandFib (I := I) gI gC x (B a x) (B b x)

theorem bgBiContrFibFixedFrame_toModel (gI gC : SmoothRiemannianMetric I M)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b) (x : M)
    (D : Tensor0SSpace 2 I x) (v : Fin 2 → E) :
    Tensor0SSpace.toModel (bgBiContrFibFixedFrame (I := I) gI gC B x D) v =
      2 * ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        gI.inner x (riemannOp (LeviCivita (I := I) gC) x (v 0) (B a x) (B b x)) (v 1) *
          Tensor0SSpace.toModel D ![(B a x : E), (B b x : E)] := by
  classical
  rw [bgBiContrFibFixedFrame, ContinuousLinearMap.smul_apply, Tensor0SSpace.toModel_smul,
    ContinuousMultilinearMap.smul_apply, smul_eq_mul]
  congr 1
  rw [ContinuousLinearMap.sum_apply, ← Tensor0SSpace.toModelL_apply, map_sum,
    ContinuousMultilinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [ContinuousLinearMap.sum_apply, Tensor0SSpace.toModelL_apply, ← Tensor0SSpace.toModelL_apply,
    map_sum, ContinuousMultilinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [Tensor0SSpace.toModelL_apply, bgSummandFib_toModel]
  ring

theorem bgKernelScalar_global (gI gC : SmoothRiemannianMetric I M)
    {Y W p q : Π b : M, TangentSpace I b}
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Y))
    (hW : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% W))
    (hp : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% p))
    (hq : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% q)) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun x : M => gI.inner x
        (riemannOp (LeviCivita (I := I) gC) x (Y x) (p x) (q x)) (W x)) := by
  classical
  have hRsec : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (T% (fun b : M => riemannSec (LeviCivita (I := I) gC) Y p q b)) :=
    riemannSec_contMDiff (cov := LeviCivita (I := I) gC) hY hp hq
  have hcongr : (fun x : M => gI.inner x
        (riemannOp (LeviCivita (I := I) gC) x (Y x) (p x) (q x)) (W x)) =
      (fun x : M => gI.inner x (riemannSec (LeviCivita (I := I) gC) Y p q x) (W x)) := by
    funext x
    rw [riemannOp_apply_smooth (cov := LeviCivita (I := I) gC) hY hp hq]
  rw [hcongr]
  exact contMDiff_g_inner_of_smooth_sections (I := I) gI
    ⟨fun b => riemannSec (LeviCivita (I := I) gC) Y p q b, hRsec⟩ ⟨fun b => W b, hW⟩

theorem bgKernelBilin_homSection_contMDiff (gI gC : SmoothRiemannianMetric I M)
    {p q : Π b : M, TangentSpace I b}
    (hp : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% p))
    (hq : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% q)) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun x : M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun b : M => TangentSpace I b →L[ℝ] TangentSpace I b →L[ℝ] ℝ)
        x (bgKernelBilin (I := I) gI gC x (p x) (q x))) := by
  classical
  apply cotangentCov_clmSection_smooth_aux
    (V₂ := fun x : M => TangentSpace I x →L[ℝ] ℝ)
    (φ := fun x : M => bgKernelBilin (I := I) gI gC x (p x) (q x))
  intro Y
  apply cotangentCov_clmSection_smooth_aux
    (V₂ := fun _ : M => ℝ)
    (φ := fun x : M => bgKernelBilin (I := I) gI gC x (p x) (q x) (Y x))
  intro W
  have h_scalar := bgKernelScalar_global (I := I) gI gC Y.contMDiff W.contMDiff hp hq
  intro x
  rw [contMDiffAt_section]
  refine (h_scalar.contMDiffAt).congr_of_eventuallyEq ?_
  filter_upwards with y
  change bgKernelBilin (I := I) gI gC y (p y) (q y) (Y y) (W y) =
    (trivializationAt ℝ (Bundle.Trivial M ℝ) x ⟨y, _⟩).2
  rw [bgKernelBilin_apply]
  rfl

theorem bgBiContrFibFixedFrame_apply_section_contMDiff (gI gC : SmoothRiemannianMetric I M)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b)
    (hB : ∀ i, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (B i)))
    (Y : Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun x : M => Tensor0SSpace 2 I x⟯) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
        (E := fun z : M => Tensor0SSpace 2 I z) x
        (bgBiContrFibFixedFrame (I := I) gI gC B x (Y x))) := by
  classical
  have hsummand : ∀ a b : Fin (Module.finrank ℝ E),
      ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 2 ℝ E)) ∞
        (fun x : M => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
          (E := fun z : M => Tensor0SSpace 2 I z) x
          (bgSummandFib (I := I) gI gC x (B a x) (B b x) (Y x))) := by
    intro a b
    have hscalar : ContMDiff I 𝓘(ℝ, ℝ) ∞
        (fun x : M => Tensor0SSpace.toModel (Y x) ![(B a x : E), (B b x : E)]) := by
      have h := TensorMultilinear.contMDiff_section_apply (n := 2)
        (fun b => Y b) Y.contMDiff
        (![fun z => B a z, fun z => B b z])
        (by
          intro i
          fin_cases i
          · exact hB a
          · exact hB b)
      refine h.congr ?_
      intro x
      congr 1
      funext i
      fin_cases i <;> rfl
    have hbilin := contMDiff_bilinSection_of_homSection (I := I)
      (fun x => bgKernelBilin (I := I) gI gC x (B a x) (B b x))
      (bgKernelBilin_homSection_contMDiff (I := I) gI gC (hB a) (hB b))
    have hsmul := ContMDiff.smul_section (f := fun x => Tensor0SSpace.toModel (Y x)
        ![(B a x : E), (B b x : E)])
      (s := fun x => Tensor0SSpace.ofModel (I := I) (x := x)
        (bilinFormToModel (TangentSpace I x) (bgKernelBilin (I := I) gI gC x (B a x) (B b x))))
      hscalar hbilin
    refine hsmul.congr ?_
    intro x
    rfl
  set S : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
      Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun z : M => Tensor0SSpace 2 I z⟯ :=
    fun a b =>
      { toFun := fun x : M => bgSummandFib (I := I) gI gC x (B a x) (B b x) (Y x)
        contMDiff_toFun := hsummand a b } with hS_def
  set Stot : Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun z : M => Tensor0SSpace 2 I z⟯ :=
    (2 : ℝ) • ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E), S a b with hStot_def
  have hStot := Stot.contMDiff
  refine hStot.congr ?_
  intro x
  refine congrArg (TotalSpace.mk' (Tensor0SModel 2 ℝ E)
    (E := fun z : M => Tensor0SSpace 2 I z) x) ?_
  rw [bgBiContrFibFixedFrame, hStot_def, ContMDiffSection.coe_smul, Pi.smul_apply]
  have hcoeOuter : ((∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E), S a b :
      Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun z : M => Tensor0SSpace 2 I z⟯) :
        Π z : M, Tensor0SSpace 2 I z) =
      ∑ a : Fin (Module.finrank ℝ E),
        ((∑ b : Fin (Module.finrank ℝ E), S a b :
          Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun z : M => Tensor0SSpace 2 I z⟯) :
          Π z : M, Tensor0SSpace 2 I z) :=
    map_sum (ContMDiffSection.coeAddHom I (Tensor0SModel 2 ℝ E) ∞
      (fun z : M => Tensor0SSpace 2 I z))
      (fun a => ∑ b : Fin (Module.finrank ℝ E), S a b) Finset.univ
  have hcoeInner : ∀ a : Fin (Module.finrank ℝ E),
      ((∑ b : Fin (Module.finrank ℝ E), S a b :
        Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun z : M => Tensor0SSpace 2 I z⟯) :
        Π z : M, Tensor0SSpace 2 I z) =
      ∑ b : Fin (Module.finrank ℝ E), ((S a b : Π z : M, Tensor0SSpace 2 I z)) := fun a =>
    map_sum (ContMDiffSection.coeAddHom I (Tensor0SModel 2 ℝ E) ∞
      (fun z : M => Tensor0SSpace 2 I z)) (fun b => S a b) Finset.univ
  have hsum : ((∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E), S a b :
      Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun z : M => Tensor0SSpace 2 I z⟯) :
        Π z : M, Tensor0SSpace 2 I z) x =
      ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        (S a b : Π z : M, Tensor0SSpace 2 I z) x := by
    rw [hcoeOuter, Finset.sum_apply]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [hcoeInner a, Finset.sum_apply]
  rw [hsum, ContinuousLinearMap.smul_apply, ContinuousLinearMap.sum_apply]
  congr 1
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [ContinuousLinearMap.sum_apply]
  rfl

theorem bgBiContrFibFixedFrame_contMDiff (gI gC : SmoothRiemannianMetric I M)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b)
    (hB : ∀ i, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (B i))) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 2 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel 2 2 ℝ E)
        (E := fun z : M => TensorRSSpace 2 2 I z) x
        (TensorRSSpace.ofCLM (bgBiContrFibFixedFrame (I := I) gI gC B x))) := by
  classical
  apply contMDiff_clm_section_of_pointwise (I := I)
    (F₁ := Tensor0SModel 2 ℝ E) (V₁ := fun z : M => Tensor0SSpace 2 I z)
    (F₂ := Tensor0SModel 2 ℝ E) (V₂ := fun z : M => Tensor0SSpace 2 I z)
    (φ := fun x : M => bgBiContrFibFixedFrame (I := I) gI gC B x)
  intro Y
  exact bgBiContrFibFixedFrame_apply_section_contMDiff (I := I) gI gC B hB Y

def bgFrameKernel (gI gC : SmoothRiemannianMetric I M) (x : M) (v0 v1 : TangentSpace I x) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  haveI : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  LinearMap.toContinuousLinearMap
    { toFun := fun p => (gI.inner x).flip v1 |>.comp
        ((riemannOp (LeviCivita (I := I) gC) x v0 p))
      map_add' := fun p p' => by
        ext q
        simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply,
          (riemannOp (LeviCivita (I := I) gC) x v0).map_add p p', map_add]
      map_smul' := fun c p => by
        ext q
        simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
          RingHom.id_apply, (riemannOp (LeviCivita (I := I) gC) x v0).map_smul c p, map_smul] }

theorem bgFrameKernel_apply (gI gC : SmoothRiemannianMetric I M) (x : M)
    (v0 v1 p q : TangentSpace I x) :
    bgFrameKernel (I := I) gI gC x v0 v1 p q =
      gI.inner x (riemannOp (LeviCivita (I := I) gC) x v0 p q) v1 := by
  rw [bgFrameKernel, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply]

def mixedBiContrFib (gI gC : SmoothRiemannianMetric I M) (x : M) :
    Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x :=
  bgBiContrFibFixedFrame (I := I) gI gC (smoothOrthoFrame (I := I) gI x) x

theorem mixedBiContrFib_eq_fixedFrame_on_nbhd (gI gC : SmoothRiemannianMetric I M) (x₀ : M)
    {y : M} (hy : y ∈ smoothOrthoFrameNbhd (I := I) (M := M) x₀) :
    mixedBiContrFib (I := I) gI gC y =
      bgBiContrFibFixedFrame (I := I) gI gC (smoothOrthoFrame (I := I) gI x₀) y := by
  classical
  apply ContinuousLinearMap.ext
  intro D
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro v
  rw [mixedBiContrFib, bgBiContrFibFixedFrame_toModel, bgBiContrFibFixedFrame_toModel]
  congr 1
  have hrewrite : ∀ (Bf : Fin (Module.finrank ℝ E) → TangentSpace I y),
      ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        gI.inner y (riemannOp (LeviCivita (I := I) gC) y (v 0) (Bf a) (Bf b)) (v 1) *
          Tensor0SSpace.toModel D ![(Bf a : E), (Bf b : E)] =
      ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        bgFrameKernel (I := I) gI gC y (v 0) (v 1) (Bf a) (Bf b) *
          (bilinFormToModel (TangentSpace I y)).symm (Tensor0SSpace.toModel D) (Bf a) (Bf b) := by
    intro Bf
    refine Finset.sum_congr rfl (fun a _ => ?_)
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [bgFrameKernel_apply (I := I) gI gC y (v 0) (v 1) (Bf a) (Bf b),
      bilinFormToModel_symm_apply (TangentSpace I y) (Tensor0SSpace.toModel D) (Bf a) (Bf b)]
    rfl
  rw [hrewrite (fun a => smoothOrthoFrame (I := I) gI y a y),
    hrewrite (fun a => smoothOrthoFrame (I := I) gI x₀ a y)]
  exact double_frame_bilin_trace_indep (I := I) gI y
    (bgFrameKernel (I := I) gI gC y (v 0) (v 1))
    ((bilinFormToModel (TangentSpace I y)).symm (Tensor0SSpace.toModel D))
    (fun a => smoothOrthoFrame (I := I) gI y a y)
    (fun a => smoothOrthoFrame (I := I) gI x₀ a y)
    (fun i j => smoothOrthoFrame_orthonormal_at_center (I := I) gI y i j)
    (fun i j => smoothOrthoFrame_orthonormal (I := I) gI x₀ hy i j)

theorem mixedBiContrFib_contMDiff (gI gC : SmoothRiemannianMetric I M) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 2 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel 2 2 ℝ E)
        (E := fun z : M => TensorRSSpace 2 2 I z) x
        (TensorRSSpace.ofCLM (mixedBiContrFib (I := I) gI gC x))) := by
  classical
  intro x₀
  have h_fixed : ContMDiffAt I (I.prod 𝓘(ℝ, TensorRSModel 2 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel 2 2 ℝ E)
        (E := fun z : M => TensorRSSpace 2 2 I z) x
        (TensorRSSpace.ofCLM (bgBiContrFibFixedFrame (I := I) gI gC
          (smoothOrthoFrame (I := I) gI x₀) x))) x₀ :=
    bgBiContrFibFixedFrame_contMDiff (I := I) gI gC (smoothOrthoFrame (I := I) gI x₀)
      (fun i => smoothOrthoFrame_smooth (I := I) gI x₀ i) x₀
  refine h_fixed.congr_of_eventuallyEq ?_
  filter_upwards [smoothOrthoFrameNbhd_mem_nhds (I := I) (M := M) x₀] with y hy
  exact congrArg (TotalSpace.mk' (TensorRSModel 2 2 ℝ E)
    (E := fun z : M => TensorRSSpace 2 2 I z) y)
    (congrArg TensorRSSpace.ofCLM
      (mixedBiContrFib_eq_fixedFrame_on_nbhd (I := I) gI gC x₀ hy))

def coeffMixedRmField (g₀ gI gC : SmoothRiemannianMetric I M) : SmoothCcTensor g₀ 2 2 where
  toSection :=
    { toFun := fun x : M =>
        (show TensorRSSpace 2 2 I x from TensorRSSpace.ofCLM (mixedBiContrFib (I := I) gI gC x))
      contMDiff_toFun := mixedBiContrFib_contMDiff (I := I) gI gC }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

@[simp] theorem coeffMixedRmField_toSection (g₀ gI gC : SmoothRiemannianMetric I M) (x : M) :
    (coeffMixedRmField (I := I) (M := M) g₀ gI gC).toSection x =
      (show TensorRSSpace 2 2 I x from TensorRSSpace.ofCLM (mixedBiContrFib (I := I) gI gC x)) :=
  rfl

theorem coeffMixedRmField_appCc_eq (g₀ gI gC : SmoothRiemannianMetric I M)
    (W : SmoothCcTensor g₀ 0 2) (x : M) (v : Fin 2 → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 2
        (appCc (I := I) (M := M) g₀ 2 2 (coeffMixedRmField (I := I) (M := M) g₀ gI gC) W) x v =
      2 * ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        gI.inner x
            (riemannOp (LeviCivita (I := I) gC) x (v 0)
              (smoothOrthoFrame (I := I) gI x a x)
              (smoothOrthoFrame (I := I) gI x b x)) (v 1) *
          unitModel (I := I) (M := M) g₀ 2 W x
            (fun j => if j = 0 then smoothOrthoFrame (I := I) gI x a x
              else smoothOrthoFrame (I := I) gI x b x) := by
  rw [unitModel, appCc_toSection]
  rw [show ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        (coeffMixedRmField (I := I) (M := M) g₀ gI gC).toSection x).comp
        (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from W.toSection x))
        (unitTensor (I := I) (M := M) x) =
      (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        (coeffMixedRmField (I := I) (M := M) g₀ gI gC).toSection x)
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from W.toSection x)
          (unitTensor (I := I) (M := M) x)) from rfl]
  rw [coeffMixedRmField_toSection]
  rw [show (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        (show TensorRSSpace 2 2 I x from TensorRSSpace.ofCLM (mixedBiContrFib (I := I) gI gC x)))
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from W.toSection x)
          (unitTensor (I := I) (M := M) x)) =
      mixedBiContrFib (I := I) gI gC x
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from W.toSection x)
          (unitTensor (I := I) (M := M) x)) from rfl]
  rw [mixedBiContrFib, bgBiContrFibFixedFrame_toModel]
  refine congrArg (fun t => (2 : ℝ) * t) ?_
  refine Finset.sum_congr rfl (fun a _ => ?_)
  refine Finset.sum_congr rfl (fun b _ => ?_)
  congr 1
  rw [unitModel]
  congr 1
  funext j
  fin_cases j <;> simp

def bgRicEndoRaisedFib (gI gC : SmoothRiemannianMetric I M) (x : M) :
    TangentSpace I x →L[ℝ] TangentSpace I x :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v => metricSharp (I := I) gI x (ricciTensor (I := I) gC x v).toLinearMap
      map_add' := fun v v' => by
        have h : (ricciTensor (I := I) gC x (v + v')).toLinearMap =
            (ricciTensor (I := I) gC x v).toLinearMap +
              (ricciTensor (I := I) gC x v').toLinearMap := by
          ext w
          simp [map_add]
        rw [show metricSharp (I := I) gI x (ricciTensor (I := I) gC x (v + v')).toLinearMap =
            (metricFlatMap (I := I) gI x).symm
              (ricciTensor (I := I) gC x (v + v')).toLinearMap from rfl,
          h, map_add]
        rfl
      map_smul' := fun c v => by
        have h : (ricciTensor (I := I) gC x (c • v)).toLinearMap =
            c • (ricciTensor (I := I) gC x v).toLinearMap := by
          ext w
          simp [map_smul]
        rw [show metricSharp (I := I) gI x (ricciTensor (I := I) gC x (c • v)).toLinearMap =
            (metricFlatMap (I := I) gI x).symm
              (ricciTensor (I := I) gC x (c • v)).toLinearMap from rfl,
          h, map_smul]
        rfl }

@[simp] lemma bgRicEndoRaisedFib_apply (gI gC : SmoothRiemannianMetric I M) (x : M)
    (v : TangentSpace I x) :
    bgRicEndoRaisedFib (I := I) gI gC x v =
      metricSharp (I := I) gI x (ricciTensor (I := I) gC x v).toLinearMap := by
  rw [bgRicEndoRaisedFib, LinearMap.coe_toContinuousLinearMap']
  rfl

theorem bgRicEndoRaisedFib_contMDiff (gI gC : SmoothRiemannianMetric I M) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun x : M => TotalSpace.mk' (E →L[ℝ] E)
        (E := fun y : M => TangentSpace I y →L[ℝ] TangentSpace I y) x
        (bgRicEndoRaisedFib (I := I) gI gC x)) := by
  apply cotangentCov_clmSection_smooth_aux (I := I) (M := M)
    (F₂ := E) (V₂ := fun y : M => TangentSpace I y)
    (φ := fun x : M => bgRicEndoRaisedFib (I := I) gI gC x)
  intro Y
  have hcv : ∀ (α : M) (j : Fin (Module.finrank ℝ E)),
      ContMDiffOn I 𝓘(ℝ) ∞
        (fun b : M => (ricciTensor (I := I) gC b (Y b)).toLinearMap
          (chartBasisVecFiber (I := I) α j b))
        (chartAt H α).source := by
    intro α j
    have hRic : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
        (fun b : M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
          (E := fun y => TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ) b
          (ricciTensor (I := I) gC b)) :=
      ricciTensor_contMDiff (I := I) gC
    have hBasis : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
        (chartBasisVec (I := I) α j)
        (trivializationAt E (TangentSpace I) α).baseSet :=
      chartBasisVec_contMDiffOn (I := I) α j
    have happ : ContMDiffOn I (I.prod 𝓘(ℝ, ℝ)) ∞
        (fun b : M => (⟨b,
            ricciTensor (I := I) gC b (Y b) (chartBasisVecFiber (I := I) α j b)⟩ :
            TotalSpace ℝ (Bundle.Trivial M ℝ)))
        (trivializationAt E (TangentSpace I) α).baseSet :=
      ContMDiffOn.clm_bundle_apply₂ (F₁ := E) (F₂ := E) (F₃ := ℝ)
        (b := id) hRic.contMDiffOn Y.contMDiff.contMDiffOn hBasis
    have hbase_eq :
        (trivializationAt E (TangentSpace I) α).baseSet = (chartAt H α).source :=
      trivializationAt_baseSet_eq_chartAt_source (I := I) α
    rw [hbase_eq] at happ
    intro b hb
    have hpb := happ b hb
    rw [Bundle.contMDiffWithinAt_totalSpace] at hpb
    exact hpb.2
  have hsmooth := metricSharp_contMDiff_total (I := I) gI
    (cv := fun b : M => (ricciTensor (I := I) gC b (Y b)).toLinearMap) hcv
  refine hsmooth.congr ?_
  intro x
  change TotalSpace.mk' E x
      (metricSharp (I := I) gI x (ricciTensor (I := I) gC x (Y x)).toLinearMap) =
    TotalSpace.mk' E x (bgRicEndoRaisedFib (I := I) gI gC x (Y x))
  rw [bgRicEndoRaisedFib_apply]

def coeffMixedCurvFibSlot (gI gC : SmoothRiemannianMetric I M) (k : Fin 2) (x : M) :
    Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x :=
  slotInsertEndoFib (I := I) (M := M) 2 k x (bgRicEndoRaisedFib (I := I) gI gC x)

theorem coeffMixedCurvFibSlot_contMDiff (g₀ gI gC : SmoothRiemannianMetric I M) (k : Fin 2) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 2 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel 2 2 ℝ E)
        (E := fun z : M => TensorRSSpace 2 2 I z) x
        (TensorRSSpace.ofCLM (coeffMixedCurvFibSlot (I := I) gI gC k x))) := by
  exact slotInsertEndoFib_contMDiff (I := I) (M := M) g₀ 2 k
    (fun x : M => bgRicEndoRaisedFib (I := I) gI gC x)
    (bgRicEndoRaisedFib_contMDiff (I := I) gI gC)

@[simp] theorem coeffMixedCurvFibSlot_toModel (gI gC : SmoothRiemannianMetric I M)
    (k : Fin 2) (x : M) (D : Tensor0SSpace 2 I x) (v : Fin 2 → E) :
    Tensor0SSpace.toModel (coeffMixedCurvFibSlot (I := I) gI gC k x D) v =
      Tensor0SSpace.toModel D
        (Function.update v k (bgRicEndoRaisedFib (I := I) gI gC x (v k))) := by
  rw [coeffMixedCurvFibSlot]
  exact slotInsertEndoFib_apply_eval (I := I) (M := M) 2 k x
    (bgRicEndoRaisedFib (I := I) gI gC x) D v

def coeffMixedCurvSlot (g₀ gI gC : SmoothRiemannianMetric I M) (k : Fin 2) :
    SmoothCcTensor g₀ 2 2 where
  toSection :=
    { toFun := fun x : M =>
        (show TensorRSSpace 2 2 I x from
          TensorRSSpace.ofCLM (coeffMixedCurvFibSlot (I := I) gI gC k x))
      contMDiff_toFun := coeffMixedCurvFibSlot_contMDiff (I := I) g₀ gI gC k }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

@[simp] theorem coeffMixedCurvSlot_toSection (g₀ gI gC : SmoothRiemannianMetric I M)
    (k : Fin 2) (x : M) :
    (coeffMixedCurvSlot (I := I) (M := M) g₀ gI gC k).toSection x =
      (show TensorRSSpace 2 2 I x from
        TensorRSSpace.ofCLM (coeffMixedCurvFibSlot (I := I) gI gC k x)) := rfl

def coeffMixedCurvFib (gI gC : SmoothRiemannianMetric I M) (x : M) :
    Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x :=
  coeffMixedCurvFibSlot (I := I) gI gC 0 x + coeffMixedCurvFibSlot (I := I) gI gC 1 x

@[simp] theorem coeffMixedCurvFib_toModel (gI gC : SmoothRiemannianMetric I M) (x : M)
    (D : Tensor0SSpace 2 I x) (v : Fin 2 → E) :
    Tensor0SSpace.toModel (coeffMixedCurvFib (I := I) gI gC x D) v =
      Tensor0SSpace.toModel D
          (Function.update v 0 (bgRicEndoRaisedFib (I := I) gI gC x (v 0))) +
        Tensor0SSpace.toModel D
          (Function.update v 1 (bgRicEndoRaisedFib (I := I) gI gC x (v 1))) := by
  rw [coeffMixedCurvFib, ContinuousLinearMap.add_apply,
    Tensor0SSpace.toModel_add, ContinuousMultilinearMap.add_apply,
    coeffMixedCurvFibSlot_toModel, coeffMixedCurvFibSlot_toModel]

def coeffMixedCurvField (g₀ gI gC : SmoothRiemannianMetric I M) : SmoothCcTensor g₀ 2 2 :=
  coeffMixedCurvSlot (I := I) (M := M) g₀ gI gC 0 + coeffMixedCurvSlot (I := I) (M := M) g₀ gI gC 1

@[simp] theorem coeffMixedCurvField_toSection (g₀ gI gC : SmoothRiemannianMetric I M) (x : M) :
    (coeffMixedCurvField (I := I) (M := M) g₀ gI gC).toSection x =
      (show TensorRSSpace 2 2 I x from
        TensorRSSpace.ofCLM (coeffMixedCurvFib (I := I) gI gC x)) := by
  rw [coeffMixedCurvField, SmoothCcTensor.toSection_add, ContMDiffSection.coe_add,
    Pi.add_apply, coeffMixedCurvSlot_toSection, coeffMixedCurvSlot_toSection]
  rfl

theorem coeffMixedCurvField_appCc_eq (g₀ gI gC : SmoothRiemannianMetric I M)
    (W : SmoothCcTensor g₀ 0 2) (x : M) (v : Fin 2 → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 2
        (appCc (I := I) (M := M) g₀ 2 2 (coeffMixedCurvField (I := I) (M := M) g₀ gI gC) W) x v =
      unitModel (I := I) (M := M) g₀ 2 W x
          (Function.update v 0 (bgRicEndoRaisedFib (I := I) gI gC x (v 0))) +
        unitModel (I := I) (M := M) g₀ 2 W x
          (Function.update v 1 (bgRicEndoRaisedFib (I := I) gI gC x (v 1))) := by
  rw [unitModel, appCc_toSection]
  rw [show ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        (coeffMixedCurvField (I := I) (M := M) g₀ gI gC).toSection x).comp
        (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from W.toSection x))
        (unitTensor (I := I) (M := M) x) =
      (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        (coeffMixedCurvField (I := I) (M := M) g₀ gI gC).toSection x)
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from W.toSection x)
          (unitTensor (I := I) (M := M) x)) from rfl]
  rw [coeffMixedCurvField_toSection]
  rw [show (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        (show TensorRSSpace 2 2 I x from
          TensorRSSpace.ofCLM (coeffMixedCurvFib (I := I) gI gC x)))
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from W.toSection x)
          (unitTensor (I := I) (M := M) x)) =
      coeffMixedCurvFib (I := I) gI gC x
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from W.toSection x)
          (unitTensor (I := I) (M := M) x)) from rfl]
  rw [coeffMixedCurvFib_toModel]
  rfl

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
