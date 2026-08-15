import DifferentialGeometry.Geometry.Comparison.GeodesicConvexity
import DifferentialGeometry.Geometry.Exponential.IntrinsicFramedCoordinates
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Convex.PathConnected

open Bundle Set
open scoped Bundle Manifold ContDiff Topology ENNReal

noncomputable section

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace NormalCoordinates

open Exponential

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [T2Space (TangentBundle I M)]
  [SigmaCompactSpace M] [ConnectedSpace M]

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace

variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
variable [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

def normalSlice
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (C : Set M) (p : M) (r : ℝ) : Set E :=
  Metric.ball (0 : E) r ∩
    intrinsicFramedExp (I := I) g hEnorm p ⁻¹' C

omit [CompleteSpace E] [T2Space (TangentBundle I M)] [ConnectedSpace M] in
@[simp] theorem mem_normalSlice
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    {C : Set M} {p : M} {r : ℝ} {z : E} :
    z ∈ normalSlice (I := I) g hEnorm C p r ↔
      z ∈ Metric.ball (0 : E) r ∧
        intrinsicFramedExp (I := I) g hEnorm p z ∈ C :=
  Iff.rfl

omit [CompleteSpace E] [ConnectedSpace M] in
theorem zero_mem_normalSlice
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    {C : Set M} {p : M} {r : ℝ} (hp : p ∈ C) (hr : 0 < r) :
    (0 : E) ∈ normalSlice (I := I) g hEnorm C p r := by
  rw [mem_normalSlice]
  refine ⟨Metric.mem_ball_self hr, ?_⟩
  simpa only [intrFrame_zero] using hp

omit [CompleteSpace E] [T2Space (TangentBundle I M)] [ConnectedSpace M] in
theorem normalSlice_star
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    {C : Set M} {p : M} (hC : IsTotallyConvex (I := I) g C)
    (hp : p ∈ C) (r : ℝ) :
    StarConvex ℝ (0 : E) (normalSlice (I := I) g hEnorm C p r) := by
  rw [starConvex_zero_iff]
  intro z hz t ht0 ht1
  rw [mem_normalSlice] at hz ⊢
  refine ⟨?_, ?_⟩
  · have hr : 0 < r := lt_of_le_of_lt dist_nonneg hz.1
    exact ((convex_ball (0 : E) r).starConvex
      (Metric.mem_ball_self hr)).smul_mem hz.1 ht0 ht1
  · let u : TangentSpace I p := normalFrame (I := I) g p z
    have hzC : expMapIntrinsic (I := I) g hEnorm p u ∈ C := by
      simpa only [u, intrFrame_apply] using hz.2
    have htC := hC (a := (0 : ℝ)) (b := (1 : ℝ)) zero_le_one
      ((intrinsicGeodesic_isGeodesic (I := I) g hEnorm p u).isGeodesicOn
        (Set.Icc 0 1))
      (intrinsicGeodesic_continuous (I := I) g hEnorm p u).continuousOn
      (by simpa only [intrinsicGeodesic_zero] using hp)
      (by simpa only [expMapIntrinsic_def] using hzC) ⟨ht0, ht1⟩
    simpa only [intrFrame_apply, map_smul, expMapIntrinsic_def,
      intrinsicGeodesic_smul, u] using htC

omit [ConnectedSpace M] in
theorem exists_slice_chart
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (C : Set M) (p : M) :
    ∃ r : ℝ, 0 < r ∧
      let B := intrFrameDiffeo (I := I) g hEnorm p
      let V := Metric.ball (0 : E) r
      let U := B '' V
      V ⊆ B.source ∧ IsOpen U ∧ p ∈ U ∧ Set.InjOn B V ∧
        B '' normalSlice (I := I) g hEnorm C p r = U ∩ C := by
  let B := intrFrameDiffeo (I := I) g hEnorm p
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp B.open_source
    0 (zero_mem_intrFrame_source (I := I) g hEnorm p)
  refine ⟨r, hr, hball, ?_, ?_, ?_, ?_⟩
  · exact B.toOpenPartialHomeomorph.isOpen_image_of_subset_source
      Metric.isOpen_ball hball
  · exact ⟨0, Metric.mem_ball_self hr, by
      simp only [intrFrameDiffeo_apply, intrFrame_zero]⟩
  · exact B.toPartialEquiv.injOn.mono hball
  · ext x
    constructor
    · rintro ⟨z, ⟨hzV, hzC⟩, rfl⟩
      exact ⟨⟨z, hzV, rfl⟩, by
        simpa only [B, intrFrameDiffeo_apply] using hzC⟩
    · rintro ⟨⟨z, hzV, rfl⟩, hzC⟩
      exact ⟨z, ⟨hzV, by
        simpa only [B, intrFrameDiffeo_apply] using hzC⟩, rfl⟩

omit [ConnectedSpace M] in
theorem exists_rel_path
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    {C : Set M} {p : M} (hC : IsTotallyConvex (I := I) g C)
    (hp : p ∈ C) :
    ∃ U : Set M, IsOpen U ∧ p ∈ U ∧ IsPathConnected (U ∩ C) := by
  obtain ⟨r, hr, hsource, hopen, hpU, _, himage⟩ :=
    exists_slice_chart (I := I) g hEnorm C p
  let B := intrFrameDiffeo (I := I) g hEnorm p
  refine ⟨B '' Metric.ball (0 : E) r, hopen, hpU, ?_⟩
  have hpath : IsPathConnected (normalSlice (I := I) g hEnorm C p r) :=
    (normalSlice_star (I := I) g hEnorm hC hp r).isPathConnected
      (zero_mem_normalSlice (I := I) g hEnorm hp hr)
  have himagePath := hpath.image'
    (B.contMDiffOn_toFun.continuousOn.mono
      (inter_subset_left.trans hsource))
  rw [himage] at himagePath
  exact himagePath

end NormalCoordinates
end Riemannian
end Geometry
end DifferentialGeometry
