import DifferentialGeometry.Geometry.Comparison.CGTRawExpLift
import DifferentialGeometry.Geometry.Comparison.CGTRawLiftOps

set_option autoImplicit false

noncomputable section

open Bundle Function Manifold Set
open scoped ContDiff ENNReal Manifold Topology

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace CGT

open Exponential NormalCoordinates

private theorem append_end_eq
    {E₁ : Type*} [NormedAddCommGroup E₁] [NormedSpace Real E₁]
    {H₁ : Type*} [TopologicalSpace H₁]
    {J : ModelWithCorners Real E₁ H₁}
    {M₁ : Type*} [TopologicalSpace M₁] [ChartedSpace H₁ M₁]
    [IsManifold J ∞ M₁] [T2Space M₁]
    {F : E₁ → M₁} {U : Set E₁} {x y z : M₁}
    {p q : Path x y} {c : Path y z}
    {A B P Q : Real → E₁}
    (hU : IsOpen U)
    (hloc : IsLocalDiffeomorphOn 𝓘(Real, E₁) J ∞ F U)
    (hA : IsLiftOn F p.extend U 0 0 1 A)
    (hB : IsLiftOn F q.extend U 0 0 1 B)
    (hP : IsLiftOn F (p.trans c).extend U 0 0 1 P)
    (hQ : IsLiftOn F (q.trans c).extend U 0 0 1 Q)
    (hend : P 1 = Q 1) :
    A 1 = B 1 := by
  let γp : Real → M₁ := fun t => p.extend (2 * t)
  let γq : Real → M₁ := fun t => q.extend (2 * t)
  have hscale : Set.MapsTo (fun t : Real => 2 * t)
      (Set.Icc 0 (1 / 2)) (Set.Icc 0 1) := by
    intro t ht
    constructor <;> linarith [ht.1, ht.2]
  have hA' : IsLiftOn F γp U 0 0 (1 / 2) (fun t => A (2 * t)) := by
    refine ⟨hA.continuousOn.comp
      (continuous_const.mul continuous_id).continuousOn hscale, ?_, ?_⟩
    · simpa only [mul_zero] using hA.2.1
    · intro t ht
      have ht' : 2 * t ∈ Set.Icc (0 : Real) 1 := hscale ht
      exact ⟨hA.mapsTo ht', hA.2.2 (2 * t) ht' |>.2⟩
  have hB' : IsLiftOn F γq U 0 0 (1 / 2) (fun t => B (2 * t)) := by
    refine ⟨hB.continuousOn.comp
      (continuous_const.mul continuous_id).continuousOn hscale, ?_, ?_⟩
    · simpa only [mul_zero] using hB.2.1
    · intro t ht
      have ht' : 2 * t ∈ Set.Icc (0 : Real) 1 := hscale ht
      exact ⟨hB.mapsTo ht', hB.2.2 (2 * t) ht' |>.2⟩
  have hPleft : IsLiftOn F γp U 0 0 (1 / 2) P := by
    refine ⟨hP.continuousOn.mono ?_, hP.2.1, ?_⟩
    · intro t ht
      exact ⟨ht.1, ht.2.trans (by norm_num)⟩
    · intro t ht
      have ht' : t ∈ Set.Icc (0 : Real) 1 :=
        ⟨ht.1, ht.2.trans (by norm_num)⟩
      refine ⟨hP.mapsTo ht', ?_⟩
      change F (P t) = p.extend (2 * t)
      rw [← Path.extend_trans_of_le_half p c ht.2]
      exact hP.2.2 t ht' |>.2
  have hQleft : IsLiftOn F γq U 0 0 (1 / 2) Q := by
    refine ⟨hQ.continuousOn.mono ?_, hQ.2.1, ?_⟩
    · intro t ht
      exact ⟨ht.1, ht.2.trans (by norm_num)⟩
    · intro t ht
      have ht' : t ∈ Set.Icc (0 : Real) 1 :=
        ⟨ht.1, ht.2.trans (by norm_num)⟩
      refine ⟨hQ.mapsTo ht', ?_⟩
      change F (Q t) = q.extend (2 * t)
      rw [← Path.extend_trans_of_le_half q c ht.2]
      exact hQ.2.2 t ht' |>.2
  have hPA : P (1 / 2) = A 1 := by
    have heq := hPleft.eqOn (by norm_num) hU hloc hA'
    convert heq ⟨by norm_num, le_rfl⟩ using 1
    all_goals norm_num
  have hQB : Q (1 / 2) = B 1 := by
    have heq := hQleft.eqOn (by norm_num) hU hloc hB'
    convert heq ⟨by norm_num, le_rfl⟩ using 1
    all_goals norm_num
  let γc : Real → M₁ := fun t => c.extend (2 * t - 1)
  have hsub : Set.Icc (1 / 2 : Real) 1 ⊆ Set.Icc (0 : Real) 1 := by
    intro t ht
    exact ⟨by linarith [ht.1], ht.2⟩
  have hPright : IsLiftOn F γc U (P (1 / 2)) (1 / 2) 1 P := by
    refine ⟨hP.continuousOn.mono hsub, rfl, ?_⟩
    intro t ht
    have ht' : t ∈ Set.Icc (0 : Real) 1 := hsub ht
    refine ⟨hP.mapsTo ht', ?_⟩
    change F (P t) = c.extend (2 * t - 1)
    rw [← Path.extend_trans_of_half_le p c ht.1]
    exact hP.2.2 t ht' |>.2
  have hQright : IsLiftOn F γc U (Q (1 / 2)) (1 / 2) 1 Q := by
    refine ⟨hQ.continuousOn.mono hsub, rfl, ?_⟩
    intro t ht
    have ht' : t ∈ Set.Icc (0 : Real) 1 := hsub ht
    refine ⟨hQ.mapsTo ht', ?_⟩
    change F (Q t) = c.extend (2 * t - 1)
    rw [← Path.extend_trans_of_half_le q c ht.1]
    exact hQ.2.2 t ht' |>.2
  have hmid : P (1 / 2) = Q (1 / 2) :=
    hPright.eqOn_of_eq hU hloc hQright
      ⟨by norm_num, le_rfl⟩ hend ⟨le_rfl, by norm_num⟩
  exact hPA.symm.trans (hmid.trans hQB)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [T2Space (TangentBundle I M)]

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace

variable [RiemannianBundle (fun x : M => TangentSpace I x)]
variable [PseudoEMetricSpace M] [IsRiemannianManifold I M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

/-- The fiber of the raw framed exponential inside a centered model ball. -/
def rawFiber
    (g : SmoothRiemannianMetric I M) (p q : M) (r : Real) : Set E :=
  {u | u ∈ Metric.ball (0 : E) r ∧ framedExpMap (I := I) g p u = q}

/-- Raw path lifting injects the pole fiber into every nearby fiber in the
correspondingly enlarged model ball. -/
theorem rawFiber_encard_le
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    {p q : M} {R r₀ s : Real}
    (hr₀ : 0 < r₀) (hs : 0 < s)
    (hqs : riemannianEDist I p q < ENNReal.ofReal s)
    (hfit : r₀ + s < R)
    (hdom : ∀ z ∈ Metric.ball (0 : E) R,
      ∀ t ∈ Set.Icc (0 : Real) 1,
        (show TangentSpace I p from
          t • normalFrame (I := I) g p z) ∈ expDomain (I := I) g p)
    (hloc : IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
      (framedExpMap (I := I) g p) (Metric.ball (0 : E) R)) :
    (rawFiber (I := I) g p p r₀).encard ≤
      (rawFiber (I := I) g p q (r₀ + s)).encard := by
  classical
  obtain ⟨c, hcFlat, hcLen⟩ := exists_flat_path (I := I) hqs
  have hR : 0 < R := (add_pos hr₀ hs).trans hfit
  have hr₀R : r₀ < R := by linarith
  let F : E → M := framedExpMap (I := I) g p
  let U : Set E := Metric.ball (0 : E) R
  have hfiberR (u : rawFiber (I := I) g p p r₀) : (u : E) ∈ U :=
    Metric.ball_subset_ball hr₀R.le u.2.1
  have hradDom (u : rawFiber (I := I) g p p r₀) :
      ∀ t ∈ Set.Icc (0 : Real) 1,
        (show TangentSpace I p from
          t • normalFrame (I := I) g p (u : E)) ∈ expDomain (I := I) g p :=
    hdom u (hfiberR u)
  let loop (u : rawFiber (I := I) g p p r₀) : Path p p :=
    (rawFlatPath (I := I) g p u (hradDom u)).cast rfl u.2.2.symm
  let path (u : rawFiber (I := I) g p p r₀) : Path p q :=
    (loop u).trans c
  have hloopFlat (u : rawFiber (I := I) g p p r₀) :
      IsFlatC1Path (I := I) (loop u) := by
    have h := rawFlatPath_flat (I := I) g p u (hradDom u)
    refine { c1 := ?_, flat_zero := ?_, flat_one := ?_ }
    · simpa only [loop, Path.extend_cast] using h.c1
    · simpa only [loop, Path.extend_cast] using h.flat_zero
    · simpa only [loop, Path.extend_cast, u.2.2] using h.flat_one
  have hloopLen (u : rawFiber (I := I) g p p r₀) :
      pathLen (I := I) (loop u) = ENNReal.ofReal ‖(u : E)‖ := by
    simpa only [pathLen, loop, Path.extend_cast] using
      rawFlatPath_len (I := I) g hEnorm p u (hradDom u)
  have hpathFlat (u : rawFiber (I := I) g p p r₀) :
      IsFlatC1Path (I := I) (path u) :=
    (hloopFlat u).trans hcFlat
  have huNorm (u : rawFiber (I := I) g p p r₀) : ‖(u : E)‖ < r₀ := by
    simpa only [rawFiber, Metric.mem_ball, dist_zero_right] using u.2.1
  have hpathSmall (u : rawFiber (I := I) g p p r₀) :
      pathLen (I := I) (path u) < ENNReal.ofReal (r₀ + s) := by
    dsimp only [path]
    rw [pathLen_trans (hloopFlat u) hcFlat, hloopLen u]
    calc
      ENNReal.ofReal ‖(u : E)‖ + pathLen (I := I) c <
          ENNReal.ofReal r₀ + ENNReal.ofReal s :=
        ENNReal.add_lt_add
          ((ENNReal.ofReal_lt_ofReal_iff hr₀).2 (huNorm u)) hcLen
      _ = ENNReal.ofReal (r₀ + s) :=
        (ENNReal.ofReal_add hr₀.le hs.le).symm
  have hpathR (u : rawFiber (I := I) g p p r₀) :
      pathLen (I := I) (path u) < ENNReal.ofReal R :=
    (hpathSmall u).trans ((ENNReal.ofReal_lt_ofReal_iff hR).2 hfit)
  have hex (u : rawFiber (I := I) g p p r₀) :
      ∃ η : Real → E, IsLiftOn F (path u).extend U 0 0 1 η := by
    apply exists_raw_lift (I := I) g hEnorm p zero_le_one
      (hpathFlat u).c1.contMDiffOn
    · simp only [path, loop, Path.extend_zero]
    · exact hR
    · exact hpathR u
    · exact hdom
    · simpa only [F, U] using hloc
  let lift (u : rawFiber (I := I) g p p r₀) : Real → E :=
    Classical.choose (hex u)
  have hlift (u : rawFiber (I := I) g p p r₀) :
      IsLiftOn F (path u).extend U 0 0 1 (lift u) :=
    Classical.choose_spec (hex u)
  have hliftLen (u : rawFiber (I := I) g p p r₀) :
      Manifold.pathELength I (F ∘ lift u) 0 1 = pathLen (I := I) (path u) := by
    apply Manifold.pathELength_congr
    intro t ht
    exact hlift u |>.2.2 t ht |>.2
  have hliftNorm (u : rawFiber (I := I) g p p r₀) :
      ‖lift u 1‖ < r₀ + s := by
    have hcd : ContDiffOn Real 1 (lift u) (Set.Icc (0 : Real) 1) :=
      (hlift u).contDiffOn (by simpa only [F, U] using hloc)
        (hpathFlat u).c1.contMDiffOn
    have hrad : ENNReal.ofReal ‖lift u 1‖ ≤
        Manifold.pathELength I (F ∘ lift u) 0 1 := by
      apply rawLift_norm_le (I := I) g hEnorm p zero_le_one (hlift u).2.1 hcd
      intro t ht a ha
      exact hdom (lift u t) ((hlift u).mapsTo ht) a ha
    apply (ENNReal.ofReal_lt_ofReal_iff (add_pos hr₀ hs)).mp
    calc
      ENNReal.ofReal ‖lift u 1‖ ≤
          Manifold.pathELength I (F ∘ lift u) 0 1 := hrad
      _ = pathLen (I := I) (path u) := hliftLen u
      _ < ENNReal.ofReal (r₀ + s) := hpathSmall u
  let f : rawFiber (I := I) g p p r₀ →
      rawFiber (I := I) g p q (r₀ + s) := fun u =>
    ⟨lift u 1, by
      constructor
      · simpa only [Metric.mem_ball, dist_zero_right] using hliftNorm u
      · have h := (hlift u).2.2 1 ⟨zero_le_one, le_rfl⟩ |>.2
        simpa only [F, path, Path.extend_one] using h⟩
  have hf : Function.Injective f := by
    intro u v huv
    apply Subtype.ext
    have hend : lift u 1 = lift v 1 := congrArg Subtype.val huv
    have hA : IsLiftOn F (loop u).extend U 0 0 1 (rawFlatRay u) := by
      simpa only [F, U, loop, Path.extend_cast,
        rawFlatPath_ext (I := I) g p u (hradDom u)] using
        rawFlatRay_lift (I := I) g p
          (show ‖(u : E)‖ < R from (huNorm u).trans hr₀R)
    have hB : IsLiftOn F (loop v).extend U 0 0 1 (rawFlatRay v) := by
      simpa only [F, U, loop, Path.extend_cast,
        rawFlatPath_ext (I := I) g p v (hradDom v)] using
        rawFlatRay_lift (I := I) g p
          (show ‖(v : E)‖ < R from (huNorm v).trans hr₀R)
    have hends : rawFlatRay (u : E) 1 = rawFlatRay (v : E) 1 :=
      append_end_eq Metric.isOpen_ball (by simpa only [F, U] using hloc)
        hA hB (hlift u) (hlift v) hend
    simpa only [rawFlatRay_one] using hends
  exact (Function.Embedding.mk f hf).encard_le

end CGT
end Riemannian
end Geometry
end DifferentialGeometry

end
