import DifferentialGeometry.Geometry.Comparison.CGTRawTransport

set_option autoImplicit false

noncomputable section

open Bundle Function Manifold Metric Set
open scoped ContDiff ENNReal Manifold Topology

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace CGT

open Exponential NormalCoordinates

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [T2Space (TangentBundle I M)]

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace

variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
variable [PseudoEMetricSpace M] [IsRiemannianManifold I M]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

/-- A nonclosed raw lift of a short based loop prevents raw loop transport
from fixing any point of the norm core. -/
theorem rawTransport_ne
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) {R L a : Real} (hL : 0 ≤ L) (ha : 0 ≤ a)
    (hfit : L + a < R)
    (hdom : ∀ z ∈ Metric.ball (0 : E) R, ∀ t ∈ Set.Icc (0 : Real) 1,
      (show TangentSpace I p from
        t • normalFrame (I := I) g p z) ∈ expDomain (I := I) g p)
    (hloc : IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
      (framedExpMap (I := I) g p) (Metric.ball (0 : E) R))
    (c : Path p p) (hc : IsFlatC1Path (I := I) c)
    (hcLen : pathLen (I := I) c < ENNReal.ofReal L)
    (A : Real → E)
    (hA : IsLiftOn (framedExpMap (I := I) g p) c.extend
      (Metric.ball (0 : E) R) 0 0 1 A)
    (hA1 : A 1 ≠ 0)
    (z : rawPullBall (E := E) R)
    (hz : z ∈ rawCore (E := E) R a) :
    rawTransport (I := I) g hEnorm p hL ha hfit hdom hloc
      c hc hcLen z hz ≠ z := by
  intro hfix
  let F : E → M := framedExpMap (I := I) g p
  let U : Set E := Metric.ball (0 : E) R
  let r : Path p (framedExpMap (I := I) g p (z : E)) :=
    rawFlatPath (I := I) g p (z : E) (hdom z z.property)
  let P : Real → E :=
    rawLoopLift (I := I) g hEnorm p hL ha hfit hdom hloc
      c hc hcLen z hz
  have hloc' : IsLocalDiffeomorphOn 𝓘(Real, E) I ∞ F U := by
    simpa only [F, U] using hloc
  have hA' : IsLiftOn F c.extend U 0 0 1 A := by
    simpa only [F, U] using hA
  have hP : IsLiftOn F (c.trans r).extend U 0 0 1 P := by
    simpa only [F, U, P, r, rawLoopPath] using
      (rawLoopLift_spec (I := I) g hEnorm p hL ha hfit hdom hloc
        c hc hcLen z hz)
  have hscaleLeft : Set.MapsTo (fun t : Real ↦ 2 * t)
      (Set.Icc 0 (1 / 2)) (Set.Icc 0 1) := by
    intro t ht
    constructor <;> linarith [ht.1, ht.2]
  have hAleft : IsLiftOn F (fun t ↦ c.extend (2 * t)) U
      0 0 (1 / 2) (fun t ↦ A (2 * t)) := by
    refine ⟨hA'.continuousOn.comp
      (continuous_const.mul continuous_id).continuousOn hscaleLeft, ?_, ?_⟩
    · simpa only [mul_zero] using hA'.2.1
    · intro t ht
      have ht' : 2 * t ∈ Set.Icc (0 : Real) 1 := hscaleLeft ht
      exact ⟨hA'.mapsTo ht', (hA'.2.2 (2 * t) ht').2⟩
  have hPleft : IsLiftOn F (fun t ↦ c.extend (2 * t)) U
      0 0 (1 / 2) P := by
    refine ⟨hP.continuousOn.mono ?_, hP.2.1, ?_⟩
    · intro t ht
      exact ⟨ht.1, ht.2.trans (by norm_num)⟩
    · intro t ht
      have ht' : t ∈ Set.Icc (0 : Real) 1 :=
        ⟨ht.1, ht.2.trans (by norm_num)⟩
      refine ⟨hP.mapsTo ht', ?_⟩
      change F (P t) = c.extend (2 * t)
      rw [← Path.extend_trans_of_le_half c r ht.2]
      exact (hP.2.2 t ht').2
  have hmid : P (1 / 2) = A 1 := by
    have heq := hPleft.eqOn (by norm_num) Metric.isOpen_ball hloc' hAleft
    convert heq ⟨by norm_num, le_rfl⟩ using 1
    all_goals norm_num
  have hPend : P 1 = (z : E) := by
    have hval := congrArg Subtype.val hfix
    simpa only [rawTransport, P] using hval
  have hzR : ‖(z : E)‖ < R := by
    have hzball := z.property
    change (z : E) ∈ Metric.ball (0 : E) R at hzball
    simpa only [Metric.mem_ball, dist_zero_right] using hzball
  let γ : Real → M := fun t ↦ r.extend (2 * t - 1)
  have hsub : Set.Icc (1 / 2 : Real) 1 ⊆ Set.Icc (0 : Real) 1 := by
    intro t ht
    exact ⟨by linarith [ht.1], ht.2⟩
  have hPright : IsLiftOn F γ U (P (1 / 2)) (1 / 2) 1 P := by
    refine ⟨hP.continuousOn.mono hsub, rfl, ?_⟩
    intro t ht
    have ht' : t ∈ Set.Icc (0 : Real) 1 := hsub ht
    refine ⟨hP.mapsTo ht', ?_⟩
    change F (P t) = r.extend (2 * t - 1)
    rw [← Path.extend_trans_of_half_le c r ht.1]
    exact (hP.2.2 t ht').2
  have hscaleRight : Set.MapsTo (fun t : Real ↦ 2 * t - 1)
      (Set.Icc (1 / 2) 1) (Set.Icc 0 1) := by
    intro t ht
    constructor <;> linarith [ht.1, ht.2]
  have hB : IsLiftOn F γ U 0 (1 / 2) 1
      (fun t ↦ rawFlatRay (z : E) (2 * t - 1)) := by
    refine ⟨(rawFlatRay_cd (z : E)).continuous.continuousOn.comp
      ((continuous_const.mul continuous_id).sub continuous_const).continuousOn
        hscaleRight, ?_, ?_⟩
    · norm_num
    · intro t ht
      refine ⟨rawFlatRay_mem hzR _, ?_⟩
      simp only [γ, r, rawFlatPath_ext, F, Function.comp_apply]
  have hend : P 1 = (fun t ↦ rawFlatRay (z : E) (2 * t - 1)) 1 := by
    convert hPend using 1
    all_goals norm_num
  have hhalf :
      P (1 / 2) =
        (fun t ↦ rawFlatRay (z : E) (2 * t - 1)) (1 / 2) :=
    hPright.eqOn_of_eq Metric.isOpen_ball hloc' hB
      ⟨by norm_num, le_rfl⟩ hend ⟨le_rfl, by norm_num⟩
  have hBhalf :
      (fun t ↦ rawFlatRay (z : E) (2 * t - 1)) (1 / 2) = 0 := by
    norm_num
  exact hA1 (hmid.symm.trans (hhalf.trans hBhalf))

end CGT
end Riemannian
end Geometry
end DifferentialGeometry

end
