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

/-- The norm core is compact whenever its closed model ball lies strictly
inside the raw pullback ball. -/
theorem rawCore_compact
    {R a : Real} (haR : a < R) :
    IsCompact (rawCore (E := E) R a) := by
  letI : ProperSpace E := FiniteDimensional.proper Real E
  rw [Subtype.isCompact_iff]
  have himage :
      ((fun z : rawPullBall (E := E) R ↦ (z : E)) ''
          rawCore (E := E) R a) =
        Metric.closedBall (0 : E) a := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      simpa only [Metric.mem_closedBall, dist_zero_right] using hw
    · intro hz
      have hza : ‖z‖ ≤ a := by
        simpa only [Metric.mem_closedBall, dist_zero_right] using hz
      have hzR : ‖z‖ < R := hza.trans_lt haR
      refine ⟨⟨z, ?_⟩, hza, rfl⟩
      change z ∈ Metric.ball (0 : E) R
      simpa only [Metric.mem_ball, dist_zero_right] using hzR
  rw [himage]
  exact isCompact_closedBall (0 : E) a

/-- The origin as a point of a positive-radius raw pullback ball. -/
def rawZero {R : Real} (hR : 0 < R) : rawPullBall (E := E) R :=
  ⟨0, by
    change (0 : E) ∈ Metric.ball 0 R
    simpa only [Metric.mem_ball, dist_self] using hR⟩

omit [InnerProductSpace Real E] [FiniteDimensional Real E] in
/-- The raw pullback origin belongs to every core of nonnegative radius. -/
theorem rawZero_mem
    {R a : Real} (hR : 0 < R) (ha : 0 ≤ a) :
    rawZero (E := E) hR ∈ rawCore (E := E) R a := by
  simpa only [mem_rawCore, rawZero, norm_zero] using ha

section PullbackDistance

variable {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space (TangentBundle I M)]

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace

variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
variable [PseudoEMetricSpace M] [IsRiemannianManifold I M]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

noncomputable local instance {R : Real} :
    SigmaCompactSpace (rawPullBall (E := E) R) :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen
      𝓘(Real, E) (rawPullBall (E := E) R).isOpen)

/-- Raw radial-domain coverage identifies pullback distance from the origin
with the model-space norm. -/
theorem rawPull_dist_zero
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) {R : Real} (hR : 0 < R)
    (hloc : IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
      (framedExpMap (I := I) g p) (Metric.ball (0 : E) R))
    (hdom : ∀ w : rawPullBall (E := E) R,
      ∀ t ∈ Set.Icc (0 : Real) 1,
        (show TangentSpace I p from
          t • normalFrame (I := I) g p (w : E)) ∈ expDomain (I := I) g p)
    (z : rawPullBall (E := E) R) :
    riemannianEDistOf (I := 𝓘(Real, E))
        (rawPullMetric (I := I) g p hloc)
        (rawZero (E := E) hR) z =
      ENNReal.ofReal ‖(z : E)‖ := by
  letI : RiemannianBundle
      (fun y : rawPullBall (E := E) R ↦
        TangentSpace 𝓘(Real, E) y) :=
    ⟨(rawPullMetric (I := I) g p hloc).toRiemannianMetric⟩
  change
    Manifold.riemannianEDist 𝓘(Real, E)
        (rawZero (E := E) hR) z =
      ENNReal.ofReal ‖(z : E)‖
  apply le_antisymm
  · have hzR : ‖(z : E)‖ < R := by
      have hzball := z.property
      change (z : E) ∈ Metric.ball (0 : E) R at hzball
      simpa only [Metric.mem_ball, dist_zero_right] using hzball
    let ρ : Real → rawPullBall (E := E) R := fun t ↦
      ⟨rawFlatRay (z : E) t, rawFlatRay_mem hzR t⟩
    have hρsmooth : ContMDiff 𝓘(Real, Real) 𝓘(Real, E) ∞ ρ := by
      intro t
      have hbase : ContMDiffAt 𝓘(Real, Real) 𝓘(Real, E) ∞
          (rawFlatRay (z : E)) t := by
        rw [contMDiffAt_iff_contDiffAt]
        exact (rawFlatRay_cd (z : E)).contDiffAt
      have hmem : ∀ s : Real,
          rawFlatRay (z : E) s ∈ rawPullBall (E := E) R :=
        fun s ↦ (ρ s).property
      exact codRestr_contMDiffAt (V := rawPullBall (E := E) R) hmem hbase
    have hρC1 : ContMDiffOn 𝓘(Real, Real) 𝓘(Real, E) 1 ρ
        (Set.Icc 0 1) :=
      (hρsmooth.of_le (by norm_num)).contMDiffOn
    have hρ0 : ρ 0 = rawZero (E := E) hR := by
      apply Subtype.ext
      simp only [ρ, rawZero, rawFlatRay_zero]
    have hρ1 : ρ 1 = z := by
      apply Subtype.ext
      simp only [ρ, rawFlatRay_one]
    have himage :
        rawExpOn (I := I) g p R ∘ ρ =
          (rawFlatPath (I := I) g p (z : E) (hdom z)).extend := by
      funext t
      change framedExpMap (I := I) g p (rawFlatRay (z : E) t) = _
      rw [rawFlatPath_ext]
      rfl
    have hρlen :
        Manifold.pathELength 𝓘(Real, E) ρ 0 1 =
          ENNReal.ofReal ‖(z : E)‖ := by
      calc
        Manifold.pathELength 𝓘(Real, E) ρ 0 1 =
            Manifold.pathELength I
              (rawExpOn (I := I) g p R ∘ ρ) 0 1 :=
          (rawPull_pathLen (I := I) g hEnorm p hloc hρC1).symm
        _ = pathLen (I := I)
            (rawFlatPath (I := I) g p (z : E) (hdom z)) := by
          rw [himage]
          rfl
        _ = ENNReal.ofReal ‖(z : E)‖ :=
          rawFlatPath_len (I := I) g hEnorm p (z : E) (hdom z)
    have hdist :=
      Manifold.riemannianEDist_le_pathELength
        (I := 𝓘(Real, E)) (x := rawZero (E := E) hR) (y := z)
        hρC1 hρ0 hρ1 zero_le_one
    rw [hρlen] at hdist
    exact hdist
  · by_contra hnot
    have hlt :
        Manifold.riemannianEDist 𝓘(Real, E)
            (rawZero (E := E) hR) z <
          ENNReal.ofReal ‖(z : E)‖ :=
      lt_of_not_ge hnot
    obtain ⟨γ, hγ0, hγ1, hγC1, hγlen⟩ :=
      Manifold.exists_lt_of_riemannianEDist_lt hlt
    let η : Real → E := fun t ↦ (γ t : E)
    have hηm : ContMDiffOn 𝓘(Real, Real) 𝓘(Real, E) 1 η
        (Set.Icc 0 1) := by
      exact
        ((contMDiff_subtype_val (n := (⊤ : WithTop ℕ∞))
          (I := 𝓘(Real, E))
          (U := rawPullBall (E := E) R)).of_le
            (show (1 : WithTop ℕ∞) ≤ (⊤ : WithTop ℕ∞) from le_top)
          ).comp_contMDiffOn hγC1
    have hη : ContDiffOn Real 1 η (Set.Icc 0 1) :=
      contMDiffOn_iff_contDiffOn.mp hηm
    have hη0 : η 0 = 0 := by
      simp only [η, hγ0, rawZero]
    have hη1 : η 1 = (z : E) := by
      simp only [η, hγ1]
    have hlift :=
      rawLift_norm_le (I := I) g hEnorm p zero_le_one hη0 hη
        (fun x _ ↦ hdom (γ x))
    have hlen :
        Manifold.pathELength I
            ((framedExpMap (I := I) g p) ∘ η) 0 1 =
          Manifold.pathELength 𝓘(Real, E) γ 0 1 := by
      simpa only [η, rawExpOn, Function.comp_apply] using
        (rawPull_pathLen (I := I) g hEnorm p hloc hγC1)
    have hnorm_le :
        ENNReal.ofReal ‖(z : E)‖ ≤
          Manifold.pathELength 𝓘(Real, E) γ 0 1 := by
      rw [← hη1, ← hlen]
      exact hlift
    exact (not_lt_of_ge hnorm_le) hγlen

end PullbackDistance

end CGT
end Riemannian
end Geometry
end DifferentialGeometry

end
