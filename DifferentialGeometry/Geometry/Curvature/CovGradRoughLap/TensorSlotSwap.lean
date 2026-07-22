import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.SecondCovGradEvaluation
import DifferentialGeometry.Geometry.Connection.TensorNabla.HomTensorRSSectionCalculus


noncomputable section

set_option backward.isDefEq.respectTransparency false

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.PDE.RicciFlow
open TensorMultilinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

set_option backward.isDefEq.respectTransparency false in

private noncomputable def chooseCcThrough (g : SmoothRiemannianMetric I M) (r a : ℕ) (x : M)
    (T : TensorRSSpace r a I x) : SmoothCcTensor g r a where
  toSection :=
    letI : NormedAddCommGroup (TensorRSModel r a ℝ E) :=
      Tensor0SBundle.tensorRSModel_normedAddCommGroup r a
    letI : NormedSpace ℝ (TensorRSModel r a ℝ E) := Tensor0SBundle.tensorRSModel_normedSpace r a
    Classical.choose (ContMDiffSection.exists_eq_at (I := I) (F := TensorRSModel r a ℝ E)
      (V := fun z : M => TensorRSSpace r a I z) (n := (⊤ : ℕ∞)) x T)
  hasCompactSupport := HasCompactSupport.of_compactSpace _

set_option backward.isDefEq.respectTransparency false in

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private lemma chooseCcThrough_eq (g : SmoothRiemannianMetric I M) (r a : ℕ) (x : M)
    (T : TensorRSSpace r a I x) :
    (chooseCcThrough (I := I) (M := M) g r a x T).toSection x = T :=
  letI : NormedAddCommGroup (TensorRSModel r a ℝ E) :=
    Tensor0SBundle.tensorRSModel_normedAddCommGroup r a
  letI : NormedSpace ℝ (TensorRSModel r a ℝ E) := Tensor0SBundle.tensorRSModel_normedSpace r a
  Classical.choose_spec (ContMDiffSection.exists_eq_at (I := I) (F := TensorRSModel r a ℝ E)
    (V := fun z : M => TensorRSSpace r a I z) (n := (⊤ : ℕ∞)) x T)

set_option backward.isDefEq.respectTransparency false in

noncomputable def curryLastTwoTensorSlots (r t : ℕ) (x : M) (T : TensorRSSpace r (t + 2) I x) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TensorRSSpace r t I x :=
  (((covGradBundleEquiv (I := I) (M := M) r t x).symm :
      TensorRSSpace r (t + 1) I x ≃L[ℝ] (TangentSpace I x →L[ℝ] TensorRSSpace r t I x))
        : TensorRSSpace r (t + 1) I x →L[ℝ] (TangentSpace I x →L[ℝ] TensorRSSpace r t I x)).comp
    ((covGradBundleEquiv (I := I) (M := M) r (t + 1) x).symm T)

set_option backward.isDefEq.respectTransparency false in

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
lemma twoSlotPeel_eval (r t : ℕ) (x : M) (T : TensorRSSpace r (t + 2) I x)
    (u w : TangentSpace I x) (D : Tensor0SSpace r I x) (m : Fin t → TangentSpace I x) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace t I x from
          curryLastTwoTensorSlots (I := I) (M := M) r t x T u w) D) m =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace (t + 2) I x from T) D)
        (Fin.cons u (Fin.cons w m)) := by
  have h1 : curryLastTwoTensorSlots (I := I) (M := M) r t x T u w =
      (covGradBundleEquiv (I := I) (M := M) r t x).symm
        ((covGradBundleEquiv (I := I) (M := M) r (t + 1) x).symm T u) w := by
    rw [curryLastTwoTensorSlots, ContinuousLinearMap.comp_apply]
    rfl
  rw [h1]
  rw [covGradBundleEquiv_symm_apply_eval (I := I) (M := M) r t x
    ((covGradBundleEquiv (I := I) (M := M) r (t + 1) x).symm T u) w D m]
  exact covGradBundleEquiv_symm_apply_eval (I := I) (M := M) r (t + 1) x T u D (Fin.cons w m)

set_option backward.isDefEq.respectTransparency false in

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
lemma twoSlotPeel_add (r t : ℕ) (x : M) (T T' : TensorRSSpace r (t + 2) I x) :
    curryLastTwoTensorSlots (I := I) (M := M) r t x (T + T') =
      curryLastTwoTensorSlots (I := I) (M := M) r t x T + curryLastTwoTensorSlots (I := I) (M := M) r t x T' := by
  rw [curryLastTwoTensorSlots, curryLastTwoTensorSlots, curryLastTwoTensorSlots,
    map_add ((covGradBundleEquiv (I := I) (M := M) r (t + 1) x).symm) T T',
    ContinuousLinearMap.comp_add]

set_option backward.isDefEq.respectTransparency false in

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
lemma twoSlotPeel_smul (r t : ℕ) (x : M) (c : ℝ) (T : TensorRSSpace r (t + 2) I x) :
    curryLastTwoTensorSlots (I := I) (M := M) r t x (c • T) =
      c • curryLastTwoTensorSlots (I := I) (M := M) r t x T := by
  rw [curryLastTwoTensorSlots, curryLastTwoTensorSlots,
    map_smul ((covGradBundleEquiv (I := I) (M := M) r (t + 1) x).symm) c T,
    ContinuousLinearMap.comp_smul]



omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
@[reducible] def tangentSpaceFiniteDimensional {x : M} :
    FiniteDimensional ℝ (TangentSpace I x) := by
  unfold TangentSpace
  infer_instance

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
@[reducible] def tangentSpaceT2 {x : M} : T2Space (TangentSpace I x) := by
  unfold TangentSpace
  infer_instance

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
@[reducible] def tensorRSSpaceFiniteDimensional {r t : ℕ} {x : M} :
    FiniteDimensional ℝ (TensorRSSpace r t I x) := by
  unfold TensorRSSpace
  infer_instance

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
@[reducible] def tensorRSSpaceT2 {r t : ℕ} {x : M} : T2Space (TensorRSSpace r t I x) := by
  unfold TensorRSSpace
  infer_instance

set_option backward.isDefEq.respectTransparency true in

private noncomputable def tangentBilinFlip {r t : ℕ} {x : M}
    (P : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TensorRSSpace r t I x) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TensorRSSpace r t I x :=
  haveI : FiniteDimensional ℝ (TangentSpace I x) :=
    tangentSpaceFiniteDimensional (I := I) (M := M)
  haveI : T2Space (TangentSpace I x) := tangentSpaceT2 (I := I) (M := M)
  haveI : T2Space (TensorRSSpace r t I x) := tensorRSSpaceT2 (I := I) (M := M)
  LinearMap.toContinuousLinearMap
    { toFun := fun a => LinearMap.toContinuousLinearMap
        { toFun := fun b => P b a
          map_add' := fun b b' => by rw [map_add, ContinuousLinearMap.add_apply]
          map_smul' := fun c b => by rw [map_smul, ContinuousLinearMap.smul_apply]; rfl }
      map_add' := fun a a' => by
        refine ContinuousLinearMap.ext (fun b => ?_)
        change P b (a + a') = _
        rw [map_add (P b), ContinuousLinearMap.add_apply]
        rfl
      map_smul' := fun c a => by
        refine ContinuousLinearMap.ext (fun b => ?_)
        change P b (c • a) = _
        rw [map_smul (P b), ContinuousLinearMap.smul_apply]
        rfl }

set_option backward.isDefEq.respectTransparency false in

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma tangentBilinFlip_apply {r t : ℕ} {x : M}
    (P : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TensorRSSpace r t I x)
    (a b : TangentSpace I x) :
    tangentBilinFlip (I := I) (M := M) P a b = P b a := rfl

set_option backward.isDefEq.respectTransparency false in

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma tangentBilinFlip_add {r t : ℕ} {x : M}
    (P P' : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TensorRSSpace r t I x) :
    tangentBilinFlip (I := I) (M := M) (P + P') =
      tangentBilinFlip (I := I) (M := M) P + tangentBilinFlip (I := I) (M := M) P' := by
  refine ContinuousLinearMap.ext (fun a => ContinuousLinearMap.ext (fun b => ?_))
  have h1 : tangentBilinFlip (I := I) (M := M) (P + P') a b = (P + P') b a :=
    tangentBilinFlip_apply (P + P') a b
  have h2 : ((tangentBilinFlip (I := I) (M := M) P +
      tangentBilinFlip (I := I) (M := M) P') a) b = P b a + P' b a := by
    rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.add_apply,
      tangentBilinFlip_apply, tangentBilinFlip_apply]
  rw [h1, h2, ContinuousLinearMap.add_apply, ContinuousLinearMap.add_apply]

set_option backward.isDefEq.respectTransparency false in

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma tangentBilinFlip_smul {r t : ℕ} {x : M} (c : ℝ)
    (P : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TensorRSSpace r t I x) :
    tangentBilinFlip (I := I) (M := M) (c • P) =
      c • tangentBilinFlip (I := I) (M := M) P := by
  refine ContinuousLinearMap.ext (fun a => ContinuousLinearMap.ext (fun b => ?_))
  have h1 : tangentBilinFlip (I := I) (M := M) (c • P) a b = (c • P) b a :=
    tangentBilinFlip_apply (c • P) a b
  have h2 : ((c • tangentBilinFlip (I := I) (M := M) P) a) b = c • P b a := by
    rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply,
      tangentBilinFlip_apply]
  rw [h1, h2, ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply]

set_option backward.isDefEq.respectTransparency false in

private noncomputable def swapTwoCurryFib (r t : ℕ) (x : M)
    (T : TensorRSSpace r (t + 2) I x) :
    TangentSpace I x →L[ℝ] TensorRSSpace r (t + 1) I x :=
  (((covGradBundleEquiv (I := I) (M := M) r t x) :
      (TangentSpace I x →L[ℝ] TensorRSSpace r t I x) ≃L[ℝ] TensorRSSpace r (t + 1) I x) :
        (TangentSpace I x →L[ℝ] TensorRSSpace r t I x) →L[ℝ]
          TensorRSSpace r (t + 1) I x).comp
    (tangentBilinFlip (I := I) (M := M)
      (curryLastTwoTensorSlots (I := I) (M := M) r t x T))

set_option backward.isDefEq.respectTransparency false in

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma swapTwoCurryFib_apply (r t : ℕ) (x : M)
    (T : TensorRSSpace r (t + 2) I x) (v : TangentSpace I x) :
    swapTwoCurryFib (I := I) (M := M) r t x T v =
      covGradBundleEquiv (I := I) (M := M) r t x
        (tangentBilinFlip (I := I) (M := M)
          (curryLastTwoTensorSlots (I := I) (M := M) r t x T) v) := rfl

set_option backward.isDefEq.respectTransparency false in

noncomputable def swapTwoFib (r t : ℕ) (x : M) :
    TensorRSSpace r (t + 2) I x →L[ℝ] TensorRSSpace r (t + 2) I x :=
  haveI : FiniteDimensional ℝ (TensorRSSpace r (t + 2) I x) :=
    tensorRSSpaceFiniteDimensional (I := I) (M := M)
  haveI : T2Space (TensorRSSpace r (t + 2) I x) := tensorRSSpaceT2 (I := I) (M := M)
  LinearMap.toContinuousLinearMap
    { toFun := fun T =>
        covGradBundleEquiv (I := I) (M := M) r (t + 1) x
          (swapTwoCurryFib (I := I) (M := M) r t x T)
      map_add' := fun T T' => by
        rw [swapTwoCurryFib, swapTwoCurryFib, swapTwoCurryFib,
          twoSlotPeel_add, tangentBilinFlip_add, ContinuousLinearMap.comp_add,
          map_add (covGradBundleEquiv (I := I) (M := M) r (t + 1) x)]
      map_smul' := fun c T => by
        rw [swapTwoCurryFib, swapTwoCurryFib,
          twoSlotPeel_smul, tangentBilinFlip_smul, ContinuousLinearMap.comp_smul,
          map_smul (covGradBundleEquiv (I := I) (M := M) r (t + 1) x)]
        rfl }

set_option backward.isDefEq.respectTransparency false in

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma swapTwoFib_apply (r t : ℕ) (x : M) (T : TensorRSSpace r (t + 2) I x) :
    swapTwoFib (I := I) (M := M) r t x T =
      covGradBundleEquiv (I := I) (M := M) r (t + 1) x
        (swapTwoCurryFib (I := I) (M := M) r t x T) := rfl

set_option backward.isDefEq.respectTransparency false in

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
lemma swapTwoFib_eval (r t : ℕ) (x : M) (T : TensorRSSpace r (t + 2) I x)
    (a b : TangentSpace I x) (D : Tensor0SSpace r I x) (m : Fin t → TangentSpace I x) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace (t + 2) I x from
          swapTwoFib (I := I) (M := M) r t x T) D) (Fin.cons a (Fin.cons b m)) =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace (t + 2) I x from T) D)
        (Fin.cons b (Fin.cons a m)) := by
  rw [swapTwoFib_apply]
  rw [covGradBundleEquiv_apply_eval (I := I) (M := M) r (t + 1) x _ D
    (Fin.cons a (Fin.cons b m))]
  simp only [Fin.cons_zero]
  rw [vecTail_cons' a (Fin.cons b m)]
  rw [show swapTwoCurryFib (I := I) (M := M) r t x T a =
    covGradBundleEquiv (I := I) (M := M) r t x
      (tangentBilinFlip (I := I) (M := M) (curryLastTwoTensorSlots (I := I) (M := M) r t x T) a)
    from rfl]
  rw [covGradBundleEquiv_apply_eval (I := I) (M := M) r t x _ D (Fin.cons b m)]
  simp only [Fin.cons_zero]
  rw [vecTail_cons' b m]
  rw [tangentBilinFlip_apply]
  exact twoSlotPeel_eval (I := I) (M := M) r t x T b a D m

set_option backward.isDefEq.respectTransparency false in

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
omit [T2Space M] in
private theorem tangentBilinFlip_curry_apply_apply_contMDiff (r t : ℕ) :
    letI : NormedAddCommGroup (TensorRSModel r (t + 2) ℝ E) :=
      tensorRSModel_normedAddCommGroup r (t + 2)
    letI : NormedSpace ℝ (TensorRSModel r (t + 2) ℝ E) :=
      tensorRSModel_normedSpace r (t + 2)
    letI := tensorRSBundle_topology (I := I) (M := M) r (t + 2)
    letI := tensorRSBundle_fiber (I := I) (M := M) r (t + 2)
    letI := tensorRSBundle_vector (I := I) (M := M) r (t + 2)
    letI := tensorRSBundle_smooth (I := I) (M := M) ∞ r (t + 2)
    ∀ (Z : Cₛ^∞⟮I; TensorRSModel r (t + 2) ℝ E,
        (fun z : M => TensorRSSpace r (t + 2) I z)⟯)
      (Yv Yu : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯),
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r t ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel r t ℝ E)
        (E := fun z : M => TensorRSSpace r t I z) x
        (tangentBilinFlip (I := I) (M := M)
          (curryLastTwoTensorSlots (I := I) (M := M) r t x (Z x)) (Yv x) (Yu x))) := by
  letI : NormedAddCommGroup (TensorRSModel r (t + 2) ℝ E) :=
    tensorRSModel_normedAddCommGroup r (t + 2)
  letI : NormedSpace ℝ (TensorRSModel r (t + 2) ℝ E) :=
    tensorRSModel_normedSpace r (t + 2)
  letI : TopologicalSpace (TotalSpace (TensorRSModel r (t + 2) ℝ E)
      (fun y : M => TensorRSSpace r (t + 2) I y)) :=
    tensorRSBundle_topology r (t + 2)
  letI : FiberBundle (TensorRSModel r (t + 2) ℝ E)
      (fun y : M => TensorRSSpace r (t + 2) I y) :=
    tensorRSBundle_fiber r (t + 2)
  letI : VectorBundle ℝ (TensorRSModel r (t + 2) ℝ E)
      (fun y : M => TensorRSSpace r (t + 2) I y) :=
    tensorRSBundle_vector r (t + 2)
  letI : ContMDiffVectorBundle (∞ : WithTop ℕ∞) (TensorRSModel r (t + 2) ℝ E)
      (fun y : M => TensorRSSpace r (t + 2) I y) I := tensorRSBundle_smooth ∞ r (t + 2)
  intro Z Yv Yu
  have hA :=
    (covGradBundleEquiv_symm_contMDiff_totalSpace (I := I) (M := M) r (t + 1)).comp Z.contMDiff
  have h1 := ContMDiff.clm_bundle_apply (b := id) hA Yu.contMDiff
  have h2 :=
    (covGradBundleEquiv_symm_contMDiff_totalSpace (I := I) (M := M) r t).comp h1
  have h3 := ContMDiff.clm_bundle_apply (b := id) h2 Yv.contMDiff
  refine h3.congr ?_
  intro x
  rfl

set_option backward.isDefEq.respectTransparency false in

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private theorem tangentBilinFlip_curry_apply_contMDiff (r t : ℕ)
    :
    letI : NormedAddCommGroup (TensorRSModel r (t + 2) ℝ E) :=
      tensorRSModel_normedAddCommGroup r (t + 2)
    letI : NormedSpace ℝ (TensorRSModel r (t + 2) ℝ E) :=
      tensorRSModel_normedSpace r (t + 2)
    letI : TopologicalSpace (TotalSpace (TensorRSModel r (t + 2) ℝ E)
        (fun y : M => TensorRSSpace r (t + 2) I y)) :=
      tensorRSBundle_topology r (t + 2)
    letI : FiberBundle (TensorRSModel r (t + 2) ℝ E)
        (fun y : M => TensorRSSpace r (t + 2) I y) :=
      tensorRSBundle_fiber r (t + 2)
    letI : VectorBundle ℝ (TensorRSModel r (t + 2) ℝ E)
        (fun y : M => TensorRSSpace r (t + 2) I y) :=
      tensorRSBundle_vector r (t + 2)
    letI : ContMDiffVectorBundle (∞ : WithTop ℕ∞) (TensorRSModel r (t + 2) ℝ E)
        (fun y : M => TensorRSSpace r (t + 2) I y) I := tensorRSBundle_smooth ∞ r (t + 2)
    ∀ (Z : Cₛ^∞⟮I; TensorRSModel r (t + 2) ℝ E,
        (fun z : M => TensorRSSpace r (t + 2) I z)⟯)
      (Yv : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯),
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] TensorRSModel r t ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (E →L[ℝ] TensorRSModel r t ℝ E)
        (E := fun z : M => TangentSpace I z →L[ℝ] TensorRSSpace r t I z) x
        (tangentBilinFlip (I := I) (M := M)
          (curryLastTwoTensorSlots (I := I) (M := M) r t x (Z x)) (Yv x))) := by
  letI : NormedAddCommGroup (TensorRSModel r (t + 2) ℝ E) :=
    tensorRSModel_normedAddCommGroup r (t + 2)
  letI : NormedSpace ℝ (TensorRSModel r (t + 2) ℝ E) :=
    tensorRSModel_normedSpace r (t + 2)
  letI : TopologicalSpace (TotalSpace (TensorRSModel r (t + 2) ℝ E)
      (fun y : M => TensorRSSpace r (t + 2) I y)) :=
    tensorRSBundle_topology r (t + 2)
  letI : FiberBundle (TensorRSModel r (t + 2) ℝ E)
      (fun y : M => TensorRSSpace r (t + 2) I y) :=
    tensorRSBundle_fiber r (t + 2)
  letI : VectorBundle ℝ (TensorRSModel r (t + 2) ℝ E)
      (fun y : M => TensorRSSpace r (t + 2) I y) :=
    tensorRSBundle_vector r (t + 2)
  letI : ContMDiffVectorBundle (∞ : WithTop ℕ∞) (TensorRSModel r (t + 2) ℝ E)
      (fun y : M => TensorRSSpace r (t + 2) I y) I := tensorRSBundle_smooth ∞ r (t + 2)
  intro Z Yv
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (V₁ := TangentSpace I) (V₂ := fun z : M => TensorRSSpace r t I z)
    (φ := fun x => tangentBilinFlip (I := I) (M := M)
      (curryLastTwoTensorSlots (I := I) (M := M) r t x (Z x)) (Yv x))
  intro Yu
  exact tangentBilinFlip_curry_apply_apply_contMDiff (I := I) (M := M) r t Z Yv Yu

set_option backward.isDefEq.respectTransparency false in

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
    [BoundarylessManifold I M] [SigmaCompactSpace M] in
private theorem swapTwoCurryFib_apply_contMDiff (r t : ℕ) :
    letI : NormedAddCommGroup (TensorRSModel r (t + 2) ℝ E) :=
      tensorRSModel_normedAddCommGroup r (t + 2)
    letI : NormedSpace ℝ (TensorRSModel r (t + 2) ℝ E) :=
      tensorRSModel_normedSpace r (t + 2)
    letI : TopologicalSpace (TotalSpace (TensorRSModel r (t + 2) ℝ E)
        (fun y : M => TensorRSSpace r (t + 2) I y)) :=
      tensorRSBundle_topology r (t + 2)
    letI : FiberBundle (TensorRSModel r (t + 2) ℝ E)
        (fun y : M => TensorRSSpace r (t + 2) I y) :=
      tensorRSBundle_fiber r (t + 2)
    letI : VectorBundle ℝ (TensorRSModel r (t + 2) ℝ E)
        (fun y : M => TensorRSSpace r (t + 2) I y) :=
      tensorRSBundle_vector r (t + 2)
    letI : ContMDiffVectorBundle (∞ : WithTop ℕ∞) (TensorRSModel r (t + 2) ℝ E)
        (fun y : M => TensorRSSpace r (t + 2) I y) I := tensorRSBundle_smooth ∞ r (t + 2)
    ∀ (Z : Cₛ^∞⟮I; TensorRSModel r (t + 2) ℝ E,
        (fun x : M => TensorRSSpace r (t + 2) I x)⟯)
      (Yv : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯),
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r (t + 1) ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel r (t + 1) ℝ E)
        (E := fun z : M => TensorRSSpace r (t + 1) I z) x
        (swapTwoCurryFib (I := I) (M := M) r t x (Z x) (Yv x))) := by
  letI : NormedAddCommGroup (TensorRSModel r (t + 2) ℝ E) :=
    tensorRSModel_normedAddCommGroup r (t + 2)
  letI : NormedSpace ℝ (TensorRSModel r (t + 2) ℝ E) :=
    tensorRSModel_normedSpace r (t + 2)
  letI : TopologicalSpace (TotalSpace (TensorRSModel r (t + 2) ℝ E)
      (fun y : M => TensorRSSpace r (t + 2) I y)) :=
    tensorRSBundle_topology r (t + 2)
  letI : FiberBundle (TensorRSModel r (t + 2) ℝ E)
      (fun y : M => TensorRSSpace r (t + 2) I y) :=
    tensorRSBundle_fiber r (t + 2)
  letI : VectorBundle ℝ (TensorRSModel r (t + 2) ℝ E)
      (fun y : M => TensorRSSpace r (t + 2) I y) :=
    tensorRSBundle_vector r (t + 2)
  letI : ContMDiffVectorBundle (∞ : WithTop ℕ∞) (TensorRSModel r (t + 2) ℝ E)
      (fun y : M => TensorRSSpace r (t + 2) I y) I := tensorRSBundle_smooth ∞ r (t + 2)
  intro Z Yv
  have hflip := tangentBilinFlip_curry_apply_contMDiff (I := I) (M := M) r t Z Yv
  letI : NormedAddCommGroup (TensorRSModel r (t + 1) ℝ E) :=
    tensorRSModel_normedAddCommGroup r (t + 1)
  letI : NormedSpace ℝ (TensorRSModel r (t + 1) ℝ E) :=
    tensorRSModel_normedSpace r (t + 1)
  letI := tensorRSBundle_topology (I := I) (M := M) r (t + 1)
  letI := tensorRSBundle_fiber (I := I) (M := M) r (t + 1)
  letI := tensorRSBundle_vector (I := I) (M := M) r (t + 1)
  letI := tensorRSBundle_smooth (I := I) (M := M) ∞ r (t + 1)
  have hcomp : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r (t + 1) ℝ E)) ∞
      ((covGradBundleSmoothEquiv (I := I) (M := M) r t).toDiffeomorph ∘
        (fun x : M => (⟨x, tangentBilinFlip (I := I) (M := M)
          (curryLastTwoTensorSlots (I := I) (M := M) r t x (Z x)) (Yv x)⟩ :
          TotalSpace (E →L[ℝ] TensorRSModel r t ℝ E)
            fun y : M => TangentSpace I y →L[ℝ] TensorRSSpace r t I y))) :=
    (covGradBundleSmoothEquiv (I := I) (M := M) r t).toDiffeomorph.contMDiff.comp hflip
  refine hcomp.congr ?_
  intro x
  rw [Function.comp_apply,
    covGradBundleSmoothEquiv_toDiffeomorph_apply (I := I) (M := M) r t x
      (tangentBilinFlip (I := I) (M := M)
          (curryLastTwoTensorSlots (I := I) (M := M) r t x (Z x)) (Yv x)),
    swapTwoCurryFib_apply (I := I) (M := M) r t x (Z x) (Yv x)]

set_option backward.isDefEq.respectTransparency false in

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
    [BoundarylessManifold I M] [SigmaCompactSpace M] in
private theorem swapTwoCurryFib_contMDiff (r t : ℕ) :
    letI : NormedAddCommGroup (TensorRSModel r (t + 2) ℝ E) :=
      tensorRSModel_normedAddCommGroup r (t + 2)
    letI : NormedSpace ℝ (TensorRSModel r (t + 2) ℝ E) :=
      tensorRSModel_normedSpace r (t + 2)
    letI : TopologicalSpace (TotalSpace (TensorRSModel r (t + 2) ℝ E)
        (fun y : M => TensorRSSpace r (t + 2) I y)) :=
      tensorRSBundle_topology r (t + 2)
    letI : FiberBundle (TensorRSModel r (t + 2) ℝ E)
        (fun y : M => TensorRSSpace r (t + 2) I y) :=
      tensorRSBundle_fiber r (t + 2)
    letI : VectorBundle ℝ (TensorRSModel r (t + 2) ℝ E)
        (fun y : M => TensorRSSpace r (t + 2) I y) :=
      tensorRSBundle_vector r (t + 2)
    letI : ContMDiffVectorBundle (∞ : WithTop ℕ∞) (TensorRSModel r (t + 2) ℝ E)
        (fun y : M => TensorRSSpace r (t + 2) I y) I := tensorRSBundle_smooth ∞ r (t + 2)
    ∀ Z : Cₛ^∞⟮I; TensorRSModel r (t + 2) ℝ E,
      (fun x : M => TensorRSSpace r (t + 2) I x)⟯,
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] TensorRSModel r (t + 1) ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (E →L[ℝ] TensorRSModel r (t + 1) ℝ E)
        (E := fun z : M => TangentSpace I z →L[ℝ] TensorRSSpace r (t + 1) I z) x
        (swapTwoCurryFib (I := I) (M := M) r t x (Z x))) := by
  letI : NormedAddCommGroup (TensorRSModel r (t + 2) ℝ E) :=
    tensorRSModel_normedAddCommGroup r (t + 2)
  letI : NormedSpace ℝ (TensorRSModel r (t + 2) ℝ E) :=
    tensorRSModel_normedSpace r (t + 2)
  letI : TopologicalSpace (TotalSpace (TensorRSModel r (t + 2) ℝ E)
      (fun y : M => TensorRSSpace r (t + 2) I y)) :=
    tensorRSBundle_topology r (t + 2)
  letI : FiberBundle (TensorRSModel r (t + 2) ℝ E)
      (fun y : M => TensorRSSpace r (t + 2) I y) :=
    tensorRSBundle_fiber r (t + 2)
  letI : VectorBundle ℝ (TensorRSModel r (t + 2) ℝ E)
      (fun y : M => TensorRSSpace r (t + 2) I y) :=
    tensorRSBundle_vector r (t + 2)
  letI : ContMDiffVectorBundle (∞ : WithTop ℕ∞) (TensorRSModel r (t + 2) ℝ E)
      (fun y : M => TensorRSSpace r (t + 2) I y) I := tensorRSBundle_smooth ∞ r (t + 2)
  intro Z
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (V₁ := TangentSpace I) (V₂ := fun z : M => TensorRSSpace r (t + 1) I z)
    (φ := fun x => swapTwoCurryFib (I := I) (M := M) r t x (Z x))
  intro Yv
  exact swapTwoCurryFib_apply_contMDiff (I := I) (M := M) r t Z Yv

set_option backward.isDefEq.respectTransparency false in

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
omit [T2Space M] in
private lemma swapTwoFib_fromCurry (r t : ℕ) (x : M)
    (T : TensorRSSpace r (t + 2) I x) :
    covGradBundleEquiv (I := I) (M := M) r (t + 1) x
        (swapTwoCurryFib (I := I) (M := M) r t x T) =
      swapTwoFib (I := I) (M := M) r t x T :=
  (swapTwoFib_apply (I := I) (M := M) r t x T).symm

set_option backward.isDefEq.respectTransparency false in

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private theorem swapTwoFib_apply_contMDiff (r t : ℕ) :
    letI : NormedAddCommGroup (TensorRSModel r (t + 2) ℝ E) :=
      tensorRSModel_normedAddCommGroup r (t + 2)
    letI : NormedSpace ℝ (TensorRSModel r (t + 2) ℝ E) :=
      tensorRSModel_normedSpace r (t + 2)
    letI := tensorRSBundle_topology (I := I) (M := M) r (t + 2)
    letI := tensorRSBundle_fiber (I := I) (M := M) r (t + 2)
    letI := tensorRSBundle_vector (I := I) (M := M) r (t + 2)
    letI := tensorRSBundle_smooth (I := I) (M := M) ∞ r (t + 2)
    ∀ Z : Cₛ^∞⟮I; TensorRSModel r (t + 2) ℝ E,
      (fun x : M => TensorRSSpace r (t + 2) I x)⟯,
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r (t + 2) ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel r (t + 2) ℝ E)
        (E := fun z : M => TensorRSSpace r (t + 2) I z) x
        (swapTwoFib (I := I) (M := M) r t x (Z x))) := by
  letI : NormedAddCommGroup (TensorRSModel r (t + 2) ℝ E) :=
    tensorRSModel_normedAddCommGroup r (t + 2)
  letI : NormedSpace ℝ (TensorRSModel r (t + 2) ℝ E) :=
    tensorRSModel_normedSpace r (t + 2)
  letI : TopologicalSpace (TotalSpace (TensorRSModel r (t + 2) ℝ E)
      (fun y : M => TensorRSSpace r (t + 2) I y)) :=
    tensorRSBundle_topology r (t + 2)
  letI : FiberBundle (TensorRSModel r (t + 2) ℝ E)
      (fun y : M => TensorRSSpace r (t + 2) I y) :=
    tensorRSBundle_fiber r (t + 2)
  letI : VectorBundle ℝ (TensorRSModel r (t + 2) ℝ E)
      (fun y : M => TensorRSSpace r (t + 2) I y) :=
    tensorRSBundle_vector r (t + 2)
  letI : ContMDiffVectorBundle (∞ : WithTop ℕ∞) (TensorRSModel r (t + 2) ℝ E)
      (fun y : M => TensorRSSpace r (t + 2) I y) I := tensorRSBundle_smooth ∞ r (t + 2)
  intro Z
  have hΨ := swapTwoCurryFib_contMDiff (I := I) (M := M) r t Z
  letI : NormedAddCommGroup (TensorRSModel r (t + 1) ℝ E) :=
    tensorRSModel_normedAddCommGroup r (t + 1)
  letI : NormedSpace ℝ (TensorRSModel r (t + 1) ℝ E) :=
    tensorRSModel_normedSpace r (t + 1)
  letI := tensorRSBundle_topology (I := I) (M := M) r (t + 1)
  letI := tensorRSBundle_fiber (I := I) (M := M) r (t + 1)
  letI := tensorRSBundle_vector (I := I) (M := M) r (t + 1)
  letI := tensorRSBundle_smooth (I := I) (M := M) ∞ r (t + 1)
  have hcomp : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r (t + 2) ℝ E)) ∞
      ((covGradBundleSmoothEquiv (I := I) (M := M) r (t + 1)).toDiffeomorph ∘
        (fun x : M => (⟨x,
          swapTwoCurryFib (I := I) (M := M) r t x (Z x)⟩ :
          TotalSpace (E →L[ℝ] TensorRSModel r (t + 1) ℝ E)
            fun y : M => TangentSpace I y →L[ℝ] TensorRSSpace r (t + 1) I y))) :=
    (covGradBundleSmoothEquiv (I := I) (M := M) r (t + 1)).toDiffeomorph.contMDiff.comp hΨ
  refine hcomp.congr ?_
  intro x
  rw [Function.comp_apply,
    covGradBundleSmoothEquiv_toDiffeomorph_apply (I := I) (M := M) r (t + 1) x _]
  exact congrArg (TotalSpace.mk' (TensorRSModel r (t + 2) ℝ E) x)
    (swapTwoFib_fromCurry (I := I) (M := M) r t x (Z x))

set_option backward.isDefEq.respectTransparency false in

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private theorem swapTwoFib_contMDiff (r t : ℕ) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r (t + 2) ℝ E →L[ℝ] TensorRSModel r (t + 2) ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel r (t + 2) ℝ E →L[ℝ] TensorRSModel r (t + 2) ℝ E)
        (E := fun z : M => TensorRSSpace r (t + 2) I z →L[ℝ] TensorRSSpace r (t + 2) I z) x
        (swapTwoFib (I := I) (M := M) r t x)) := by
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (V₁ := fun z : M => TensorRSSpace r (t + 2) I z)
    (V₂ := fun z : M => TensorRSSpace r (t + 2) I z)
    (φ := fun x => swapTwoFib (I := I) (M := M) r t x)
  intro Z
  exact swapTwoFib_apply_contMDiff (I := I) (M := M) r t Z

set_option backward.isDefEq.respectTransparency false in

noncomputable def swapTwoSec (r t : ℕ) :
    HomTensorRSField (E := E) (M := M) r (t + 2) (t + 2) I where
  toFun := fun x : M => swapTwoFib (I := I) (M := M) r t x
  contMDiff_toFun := swapTwoFib_contMDiff (I := I) (M := M) r t

set_option backward.isDefEq.respectTransparency false in

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
lemma swapTwoSec_apply (r t : ℕ) (x : M) :
    (show TensorRSSpace r (t + 2) I x →L[ℝ] TensorRSSpace r (t + 2) I x from
      swapTwoSec (I := I) (M := M) (E := E) r t x) = swapTwoFib (I := I) (M := M) r t x := rfl



end Connection
end Integral
end DifferentialGeometry
