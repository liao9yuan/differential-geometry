import DifferentialGeometry.Geometry.Comparison.GeodesicConvexity
import DifferentialGeometry.Geometry.Exponential.DiagInvBranch
import DifferentialGeometry.Geometry.Exponential.IntrinsicBallDiffeo

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set
open scoped ContDiff Manifold Topology ENNReal

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Exponential
namespace DiagInvBranch

open NormalCoordinates

section Normed

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
  [ConnectedSpace M]

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace

variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
variable [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
  [T2Space (TangentBundle I M)]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

theorem minimizingVec_seg
    {g : SmoothRiemannianMetric I M}
    {hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w))}
    {p : M} (B : DiagInvBranch (I := I) g hEnorm p) :
    ∀ᶠ yz : M × M in 𝓝 (p, p),
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        (⟨yz.1, t • minimizingVec (I := I) g hEnorm yz.1 yz.2⟩ :
          TangentBundle I M) ∈ B.hom.source := by
  rcases B.exists_source_tube with ⟨A, hA, δ, hδ, hsource⟩
  have hfirst : Prod.fst ⁻¹' A ∈ 𝓝 (p, p) :=
    continuous_fst.continuousAt hA
  have hto : Continuous (fun y : M ↦ riemannianEDist I y p) :=
    continuous_riemannianEDist_to (I := I) p
  have hfrom : Continuous (fun z : M ↦ riemannianEDist I p z) := by
    simpa only [riemannianEDist_comm] using hto
  have hleft :
      {yz : M × M |
        riemannianEDist I yz.1 p < ENNReal.ofReal (δ / 2)} ∈
        𝓝 (p, p) := by
    apply (isOpen_lt (hto.comp continuous_fst) continuous_const).mem_nhds
    change riemannianEDist I p p < ENNReal.ofReal (δ / 2)
    rw [riemannianEDist_self]
    exact ENNReal.ofReal_pos.2 (half_pos hδ)
  have hright :
      {yz : M × M |
        riemannianEDist I p yz.2 < ENNReal.ofReal (δ / 2)} ∈
        𝓝 (p, p) := by
    apply (isOpen_lt (hfrom.comp continuous_snd) continuous_const).mem_nhds
    change riemannianEDist I p p < ENNReal.ofReal (δ / 2)
    rw [riemannianEDist_self]
    exact ENNReal.ofReal_pos.2 (half_pos hδ)
  filter_upwards [hfirst, hleft, hright] with yz hyA hyLeft hyRight
  have hsum :
      ENNReal.ofReal (δ / 2) + ENNReal.ofReal (δ / 2) =
        ENNReal.ofReal δ := by
    calc
      ENNReal.ofReal (δ / 2) + ENNReal.ofReal (δ / 2) =
          ENNReal.ofReal (δ / 2 + δ / 2) :=
        (ENNReal.ofReal_add (by positivity) (by positivity)).symm
      _ = ENNReal.ofReal δ := by ring_nf
  have hyDist :
      riemannianEDist I yz.1 yz.2 < ENNReal.ofReal δ := by
    calc
      riemannianEDist I yz.1 yz.2 ≤
          riemannianEDist I yz.1 p + riemannianEDist I p yz.2 :=
        Manifold.riemannianEDist_triangle
      _ < ENNReal.ofReal (δ / 2) + ENNReal.ofReal (δ / 2) :=
        ENNReal.add_lt_add hyLeft hyRight
      _ = ENNReal.ofReal δ := hsum
  have hfin : riemannianEDist I yz.1 yz.2 ≠ ⊤ :=
    ne_of_lt (hyDist.trans ENNReal.ofReal_lt_top)
  have hreal :=
    (ENNReal.toReal_lt_toReal hfin ENNReal.ofReal_ne_top).2 hyDist
  have hreal' : (riemannianEDist I yz.1 yz.2).toReal < δ := by
    simpa only [ENNReal.toReal_ofReal hδ.le] using hreal
  intro t ht
  apply hsource yz.1 hyA
  rw [sqrt_gInner_smul_self (I := I) g yz.1 ht.1,
    minimizingVec_len]
  calc
    t * (riemannianEDist I yz.1 yz.2).toReal ≤
        (riemannianEDist I yz.1 yz.2).toReal := by
      simpa only [one_mul] using
        (mul_le_mul_of_nonneg_right ht.2 ENNReal.toReal_nonneg)
    _ < δ := hreal'

theorem minimizingVec_mem
    {g : SmoothRiemannianMetric I M}
    {hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w))}
    {p : M} (B : DiagInvBranch (I := I) g hEnorm p) :
    ∀ᶠ yz : M × M in 𝓝 (p, p),
      (⟨yz.1, minimizingVec (I := I) g hEnorm yz.1 yz.2⟩ :
        TangentBundle I M) ∈ B.hom.source := by
  filter_upwards [B.minimizingVec_seg] with yz hseg
  simpa only [one_smul] using hseg 1 ⟨zero_le_one, le_rfl⟩

theorem inv_eq_minimizingVec
    {g : SmoothRiemannianMetric I M}
    {hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w))}
    {p : M} (B : DiagInvBranch (I := I) g hEnorm p) :
    ∀ᶠ yz : M × M in 𝓝 (p, p),
      B.inv yz =
        (⟨yz.1, minimizingVec (I := I) g hEnorm yz.1 yz.2⟩ :
          TangentBundle I M) := by
  filter_upwards [B.minimizingVec_mem] with yz hsource
  exact B.inv_eq_of_exp hsource
    (minimizingVec_exp (I := I) g hEnorm yz.1 yz.2)

end Normed

section Framed

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
  [ConnectedSpace M]

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace

variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
variable [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
  [T2Space (TangentBundle I M)]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

theorem framed_symm_norm
    {g : SmoothRiemannianMetric I M}
    {hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w))}
    {p : M} (B : DiagInvBranch (I := I) g hEnorm p) :
    ∀ᶠ yz : M × M in 𝓝 (p, p),
      yz.2 ∈ (ExpInvBranch.framed (E := E) (B.fixed yz.1)).target ∧
        ‖(ExpInvBranch.framed (E := E) (B.fixed yz.1)).symm yz.2‖ =
          (riemannianEDist I yz.1 yz.2).toReal := by
  filter_upwards [B.minimizingVec_seg, B.inv_eq_minimizingVec] with yz hseg hinv
  have hsource :
      (⟨yz.1, minimizingVec (I := I) g hEnorm yz.1 yz.2⟩ :
        TangentBundle I M) ∈ B.hom.source := by
    simpa only [one_smul] using hseg 1 ⟨zero_le_one, le_rfl⟩
  have htarget : yz.2 ∈
      (ExpInvBranch.framed (E := E) (B.fixed yz.1)).target := by
    change (yz.1, yz.2) ∈ B.hom.target
    have hmap := B.hom.map_source hsource
    have heq := B.hom_eq hsource
    have hpair :
        B.hom
            (⟨yz.1, minimizingVec (I := I) g hEnorm yz.1 yz.2⟩ :
              TangentBundle I M) = yz := by
      exact heq.trans (by simp only [diagExp, minimizingVec_exp])
    rw [← hpair]
    exact hmap
  refine ⟨htarget, ?_⟩
  have hcoord :
      normalFrame (I := I) g yz.1
          ((ExpInvBranch.framed (E := E) (B.fixed yz.1)).symm yz.2) =
        minimizingVec (I := I) g hEnorm yz.1 yz.2 := by
    change intrFrameCLE (I := I) g yz.1
        ((intrFrameCLE (I := I) g yz.1).symm (B.inv yz).snd) = _
    rw [ContinuousLinearEquiv.apply_symm_apply]
    exact congrArg (fun z : TangentBundle I M ↦ z.snd) hinv
  rw [← normalFrame_sqrt (I := I) g yz.1
    ((ExpInvBranch.framed (E := E) (B.fixed yz.1)).symm yz.2),
      hcoord, minimizingVec_len]

theorem framed_smul_eq_join
    {g : SmoothRiemannianMetric I M}
    {hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w))}
    {p : M} (B : DiagInvBranch (I := I) g hEnorm p) :
    ∀ᶠ yz : M × M in 𝓝 (p, p),
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        ExpInvBranch.framed (E := E) (B.fixed yz.1)
            (t • (ExpInvBranch.framed (E := E) (B.fixed yz.1)).symm yz.2) =
          minJoin (I := I) g hEnorm yz.1 yz.2 t := by
  filter_upwards [B.minimizingVec_seg, B.inv_eq_minimizingVec] with yz hseg hinv
  intro t ht
  have hcoord :
      normalFrame (I := I) g yz.1
          ((ExpInvBranch.framed (E := E) (B.fixed yz.1)).symm yz.2) =
        minimizingVec (I := I) g hEnorm yz.1 yz.2 := by
    change intrFrameCLE (I := I) g yz.1
        ((intrFrameCLE (I := I) g yz.1).symm (B.inv yz).snd) = _
    rw [ContinuousLinearEquiv.apply_symm_apply]
    exact congrArg (fun z : TangentBundle I M ↦ z.snd) hinv
  have hsource :
      t • (ExpInvBranch.framed (E := E) (B.fixed yz.1)).symm yz.2 ∈
        (ExpInvBranch.framed (E := E) (B.fixed yz.1)).source := by
    rw [ExpInvBranch.framed_source]
    change intrFrameCLE (I := I) g yz.1
        (t • (ExpInvBranch.framed (E := E) (B.fixed yz.1)).symm yz.2) ∈
          (B.fixed yz.1).hom.source
    rw [DiagInvBranch.fixed_source]
    change (⟨yz.1, intrFrameCLE (I := I) g yz.1
        (t • (ExpInvBranch.framed (E := E) (B.fixed yz.1)).symm yz.2)⟩ :
          TangentBundle I M) ∈ B.hom.source
    rw [map_smul, intrFrameCLE_apply, hcoord]
    exact hseg t ht
  rw [← ExpInvBranch.framed_eq_intr (E := E) (B.fixed yz.1) hsource]
  simp only [intrFrame_apply, map_smul, expMapIntrinsic_def,
    intrinsicGeodesic_smul, minJoin]
  rw [hcoord]

theorem framed_smul_mem
    {g : SmoothRiemannianMetric I M}
    {hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w))}
    {p : M} (B : DiagInvBranch (I := I) g hEnorm p) :
    ∀ᶠ yz : M × M in 𝓝 (p, p),
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        t • (ExpInvBranch.framed (E := E) (B.fixed yz.1)).symm yz.2 ∈
          (ExpInvBranch.framed (E := E) (B.fixed yz.1)).source := by
  filter_upwards [B.minimizingVec_seg, B.inv_eq_minimizingVec] with yz hseg hinv
  intro t ht
  have hcoord :
      normalFrame (I := I) g yz.1
          ((ExpInvBranch.framed (E := E) (B.fixed yz.1)).symm yz.2) =
        minimizingVec (I := I) g hEnorm yz.1 yz.2 := by
    change intrFrameCLE (I := I) g yz.1
        ((intrFrameCLE (I := I) g yz.1).symm (B.inv yz).snd) = _
    rw [ContinuousLinearEquiv.apply_symm_apply]
    exact congrArg (fun z : TangentBundle I M ↦ z.snd) hinv
  rw [ExpInvBranch.framed_source]
  change intrFrameCLE (I := I) g yz.1
      (t • (ExpInvBranch.framed (E := E) (B.fixed yz.1)).symm yz.2) ∈
        (B.fixed yz.1).hom.source
  rw [DiagInvBranch.fixed_source]
  change (⟨yz.1, intrFrameCLE (I := I) g yz.1
      (t • (ExpInvBranch.framed (E := E) (B.fixed yz.1)).symm yz.2)⟩ :
        TangentBundle I M) ∈ B.hom.source
  rw [map_smul, intrFrameCLE_apply, hcoord]
  exact hseg t ht

end Framed

end DiagInvBranch
end Exponential
end Riemannian
end Geometry
end DifferentialGeometry
