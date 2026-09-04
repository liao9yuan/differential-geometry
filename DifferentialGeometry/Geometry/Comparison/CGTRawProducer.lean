import DifferentialGeometry.Geometry.Comparison.CGTScale
import DifferentialGeometry.Geometry.Comparison.CGTRawCoreJoin
import DifferentialGeometry.Geometry.Comparison.CGTRawBranchHess
import DifferentialGeometry.Geometry.Comparison.CGTRawBigon
import DifferentialGeometry.Geometry.Comparison.CGTWhiteheadBigon
import DifferentialGeometry.Geometry.Comparison.CenterOfMass

set_option autoImplicit false

noncomputable section

open Bundle Function Manifold Metric Set TopologicalSpace
open scoped ContDiff ENNReal Manifold Topology

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace CGT

open Exponential Geodesic NormalCoordinates

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
  [T2Space (TangentBundle I M)]

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

omit [T2Space M] [SigmaCompactSpace M] in
/-- The complete-extension minimizer between raw-core points has no conjugate
endpoint. -/
theorem rawCore_min_regular
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) {R a K : Real} (hR : 0 < R) (h4aR : 4 * a < R)
    (hloc : IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
      (framedExpMap (I := I) g p) (Metric.ball (0 : E) R))
    (hdom : ∀ w : rawPullBall (E := E) R,
      ∀ s ∈ Set.Icc (0 : Real) 1,
        (show TangentSpace I p from
          s • normalFrame (I := I) g p (w : E)) ∈ expDomain (I := I) g p)
    (hK : 0 ≤ K)
    (hsmall : K * (2 * a) ^ 2 < (Real.pi / 2) ^ 2)
    (hRm : ∀ z : E, ‖z‖ < 3 * R / 4 →
      Real.sqrt (Tensor0SBundle.normSq0S (I := I) g
        (framedExpMap (I := I) g p z) 4
        (Geometry.Curvature.metricRm04At (I := I) (M := M) g
          (framedExpMap (I := I) g p z))) ≤ K)
    {pt q : rawPullBall (E := E) R}
    (hpt : pt ∈ rawCore (E := E) R a)
    (hq : q ∈ rawCore (E := E) R a) :
    let gExt := rawExtMetric (I := I) g p hR hloc
    letI : RiemannianBundle
        (fun z : E ↦ TangentSpace 𝓘(Real, E) z) :=
      ⟨gExt.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E
        (fun z : E ↦ TangentSpace 𝓘(Real, E) z) :=
      ⟨gExt.inner, gExt.contMDiff.continuous, by intro z v w; rfl⟩
    letI : PseudoEMetricSpace E :=
      PseudoEMetricSpace.ofRiemannianMetric 𝓘(Real, E) E
    letI : IsRiemannianManifold 𝓘(Real, E) E := ⟨fun _ _ => rfl⟩
    letI : UniformSpace E := PseudoEMetricSpace.toUniformSpace
    letI : CompleteSpace E := (rawExt_complete (I := I) g p hR hloc).complete
    let hExt : ∀ (z : E) (v : TangentSpace 𝓘(Real, E) z),
        ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (gExt.inner z v v)) :=
      fun z v => tensor0SBundle_enorm_eq_riemannianBundle_enorm
        (I := 𝓘(Real, E)) gExt z v
    let u := minimizingVec (I := 𝓘(Real, E)) gExt hExt (pt : E) (q : E)
    ¬ IsConjVec (I := 𝓘(Real, E)) gExt hExt (pt : E) (u : E) := by
  classical
  let gExt := rawExtMetric (I := I) g p hR hloc
  letI : RiemannianBundle
      (fun z : E ↦ TangentSpace 𝓘(Real, E) z) :=
    ⟨gExt.toRiemannianMetric⟩
  letI (z : E) : NormedAddCommGroup (TangentSpace 𝓘(Real, E) z) := inferInstance
  letI (z : E) : NormedSpace Real (TangentSpace 𝓘(Real, E) z) := inferInstance
  letI : ∀ z : E, ENormSMulClass Real (TangentSpace 𝓘(Real, E) z) :=
    fun _ => inferInstance
  letI : IsContinuousRiemannianBundle E
      (fun z : E ↦ TangentSpace 𝓘(Real, E) z) :=
    ⟨gExt.inner, gExt.contMDiff.continuous, by intro z v w; rfl⟩
  letI : PseudoEMetricSpace E :=
    PseudoEMetricSpace.ofRiemannianMetric 𝓘(Real, E) E
  letI : IsRiemannianManifold 𝓘(Real, E) E := ⟨fun _ _ => rfl⟩
  letI : UniformSpace E := PseudoEMetricSpace.toUniformSpace
  letI : CompleteSpace E := (rawExt_complete (I := I) g p hR hloc).complete
  let hExt : ∀ (z : E) (v : TangentSpace 𝓘(Real, E) z),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (gExt.inner z v v)) :=
    fun z v => tensor0SBundle_enorm_eq_riemannianBundle_enorm
      (I := 𝓘(Real, E)) gExt z v
  let u := minimizingVec (I := 𝓘(Real, E)) gExt hExt (pt : E) (q : E)
  change ¬ IsConjVec (I := 𝓘(Real, E)) gExt hExt (pt : E) (u : E)
  obtain ⟨L, h2aL, hbudget, hsmallL⟩ := exists_short_scale h4aR hsmall
  have hpt' : ‖(pt : E)‖ ≤ a := (mem_rawCore (E := E) pt).mp hpt
  have hq' : ‖(q : E)‖ ≤ a := (mem_rawCore (E := E) q).mp hq
  have ha : 0 ≤ a := (norm_nonneg (pt : E)).trans hpt'
  have haInner : a ≤ 3 * R / 4 := by linarith
  have hdist : riemannianEDistOf (I := 𝓘(Real, E)) gExt (pt : E) (q : E) ≤
      ENNReal.ofReal (2 * a) :=
    rawExt_edist_le (I := I) g hEnorm p hR hloc hpt' hq' haInner
      (hdom pt) (hdom q)
  have hdistReal : (riemannianEDistOf
      (I := 𝓘(Real, E)) gExt (pt : E) (q : E)).toReal ≤ 2 * a :=
    ENNReal.toReal_le_of_le_ofReal (mul_nonneg (by norm_num) ha) hdist
  have hu2a : Real.sqrt (gExt.inner (pt : E) u u) ≤ 2 * a := by
    rw [minimizingVec_len (I := 𝓘(Real, E)) gExt hExt (pt : E) (q : E)]
    exact hdistReal
  have huL : Real.sqrt (gExt.inner (pt : E) u u) ≤ L := hu2a.trans h2aL.le
  have hdim : Module.finrank Real E ≠ 0 := NeZero.ne _
  have hLaunch : rawExtLaunch (I := I) g p hR hloc (pt : E) u =
      rawExtJoin (I := I) g p hR hloc (pt : E) (q : E) := by
    rw [rawExtJoin_eq_min (I := I) g p hR hloc hdim (pt : E) (q : E)]
    change intrinsicGeodesic (I := 𝓘(Real, E)) gExt hExt (pt : E) u =
      minJoin (I := 𝓘(Real, E)) gExt hExt (pt : E) (q : E)
    rfl
  have hfence : ∀ t ∈ Set.Icc (0 : Real) 1,
      ‖rawExtLaunch (I := I) g p hR hloc (pt : E) u t‖ < 3 * R / 4 := by
    rw [hLaunch]
    exact rawExtJoin_fenced (I := I) g hEnorm p hR h4aR hloc hdom hpt' hq'
  have hnot := rawExt_no_conj (I := I) g p hR hloc u hfence huL hK hRm hsmallL
  change ¬ IsConjVec (I := 𝓘(Real, E)) gExt hExt (pt : E) (u : E) at hnot
  exact hnot

omit [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
  [T2Space (TangentBundle I M)]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [PseudoEMetricSpace M] [IsRiemannianManifold I M]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)] in
private theorem rawExt_minVec_mem
    (g : SmoothRiemannianMetric I M)
    (p : M) {R : Real} (hR : 0 < R)
    (hloc : IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
      (framedExpMap (I := I) g p) (Metric.ball (0 : E) R))
    {pt q u : E} :
    let gExt := rawExtMetric (I := I) g p hR hloc
    letI : RiemannianBundle
        (fun z : E ↦ TangentSpace 𝓘(Real, E) z) :=
      ⟨gExt.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E
        (fun z : E ↦ TangentSpace 𝓘(Real, E) z) :=
      ⟨gExt.inner, gExt.contMDiff.continuous, by intro z v w; rfl⟩
    letI : PseudoEMetricSpace E :=
      PseudoEMetricSpace.ofRiemannianMetric 𝓘(Real, E) E
    letI : IsRiemannianManifold 𝓘(Real, E) E := ⟨fun _ _ => rfl⟩
    letI : UniformSpace E := PseudoEMetricSpace.toUniformSpace
    letI : CompleteSpace E := (rawExt_complete (I := I) g p hR hloc).complete
    let hExt : ∀ (z : E) (v : TangentSpace 𝓘(Real, E) z),
        ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (gExt.inner z v v)) :=
      fun z v => tensor0SBundle_enorm_eq_riemannianBundle_enorm
        (I := 𝓘(Real, E)) gExt z v
    ∀ (B : ExpInvBranch (I := 𝓘(Real, E)) gExt hExt pt),
      u ∈ B.hom.source →
      (∀ v : E,
        expMapIntrinsic (I := 𝓘(Real, E)) gExt hExt pt v = q →
        Real.sqrt (gExt.inner pt v v) =
          (riemannianEDist 𝓘(Real, E) pt q).toReal →
        v = u) →
      ∀ᶠ z in 𝓝 q,
        (minimizingVec (I := 𝓘(Real, E)) gExt hExt pt z : E) ∈
          B.hom.source := by
  classical
  let gExt := rawExtMetric (I := I) g p hR hloc
  letI : RiemannianBundle
      (fun z : E ↦ TangentSpace 𝓘(Real, E) z) :=
    ⟨gExt.toRiemannianMetric⟩
  letI (z : E) : NormedAddCommGroup (TangentSpace 𝓘(Real, E) z) := inferInstance
  letI (z : E) : NormedSpace Real (TangentSpace 𝓘(Real, E) z) := inferInstance
  letI : ∀ z : E, ENormSMulClass Real (TangentSpace 𝓘(Real, E) z) :=
    fun _ => inferInstance
  letI : IsContinuousRiemannianBundle E
      (fun z : E ↦ TangentSpace 𝓘(Real, E) z) :=
    ⟨gExt.inner, gExt.contMDiff.continuous, by intro z v w; rfl⟩
  letI : PseudoEMetricSpace E :=
    PseudoEMetricSpace.ofRiemannianMetric 𝓘(Real, E) E
  letI : IsRiemannianManifold 𝓘(Real, E) E := ⟨fun _ _ => rfl⟩
  letI : UniformSpace E := PseudoEMetricSpace.toUniformSpace
  letI : CompleteSpace E := (rawExt_complete (I := I) g p hR hloc).complete
  let hExt : ∀ (z : E) (v : TangentSpace 𝓘(Real, E) z),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (gExt.inner z v v)) :=
    fun z v => tensor0SBundle_enorm_eq_riemannianBundle_enorm
      (I := 𝓘(Real, E)) gExt z v
  dsimp only
  intro B hu huniq
  let mv : E → E := fun z =>
    (minimizingVec (I := 𝓘(Real, E)) gExt hExt pt z : E)
  let d : E → Real := fun z =>
    (riemannianEDist 𝓘(Real, E) pt z).toReal
  have hfinite :
      {z : E |
        riemannianEDist 𝓘(Real, E) pt z ≠ (⊤ : ENNReal)} = Set.univ := by
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
    exact riemannianEDist_ne_top (I := 𝓘(Real, E)) pt z
  have hd : Continuous d := by
    have hdOn := continuousOn_riemannianEDist_toReal_on_finite gExt pt
    rw [hfinite] at hdOn
    exact continuousOn_univ.mp hdOn
  have hmv : Filter.Tendsto mv (𝓝 q) (𝓝 u) := by
    rw [Filter.tendsto_iff_seq_tendsto]
    intro seq hseq
    apply Filter.tendsto_of_subseq_tendsto
    intro ns hns
    have hz :
        Filter.Tendsto (fun n => seq (ns n)) Filter.atTop (𝓝 q) :=
      hseq.comp hns
    have hdseq :
        Filter.Tendsto (fun n => d (seq (ns n)))
          Filter.atTop (𝓝 (d q)) :=
      (hd.tendsto q).comp hz
    have hdbdd :
        Bornology.IsBounded (Set.range fun n => d (seq (ns n))) :=
      Metric.isBounded_range_of_tendsto _ hdseq
    rw [isBounded_iff_forall_norm_le] at hdbdd
    obtain ⟨C, hC⟩ := hdbdd
    let C₀ : Real := max 0 C
    let K : Set E :=
      {v : E | Real.sqrt (gExt.inner pt v v) ≤ C₀}
    have hK : IsCompact K := by
      simpa only [K] using
        gLenBall_isCompact (I := 𝓘(Real, E)) gExt pt C₀
    have hmvK : ∀ n, mv (seq (ns n)) ∈ K := by
      intro n
      have hdC : d (seq (ns n)) ≤ C := by
        have hnorm := hC _ ⟨n, rfl⟩
        rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg] at hnorm
        exact hnorm
      have hdC₀ : d (seq (ns n)) ≤ C₀ :=
        hdC.trans (le_max_right _ _)
      change
        Real.sqrt
            (gExt.inner pt
              (minimizingVec (I := 𝓘(Real, E)) gExt hExt pt (seq (ns n)))
              (minimizingVec (I := 𝓘(Real, E)) gExt hExt pt (seq (ns n)))) ≤
          C₀
      rw [minimizingVec_len
        (I := 𝓘(Real, E)) gExt hExt pt (seq (ns n))]
      exact hdC₀
    obtain ⟨v, _hvK, φ, hφ, hv⟩ := hK.tendsto_subseq hmvK
    have hzφ :
        Filter.Tendsto (fun n => seq (ns (φ n)))
          Filter.atTop (𝓝 q) :=
      hz.comp hφ.tendsto_atTop
    have hexp_v :
        Filter.Tendsto
          (fun n =>
            expMapIntrinsic (I := 𝓘(Real, E)) gExt hExt pt
              (mv (seq (ns (φ n)))))
          Filter.atTop
          (𝓝 (expMapIntrinsic (I := 𝓘(Real, E)) gExt hExt pt v)) := by
      simpa only [Function.comp_apply] using
        ((expMapIntrinsic_continuous
          (I := 𝓘(Real, E)) gExt hExt pt).tendsto v).comp hv
    have hexp_q :
        Filter.Tendsto
          (fun n =>
            expMapIntrinsic (I := 𝓘(Real, E)) gExt hExt pt
              (mv (seq (ns (φ n)))))
          Filter.atTop (𝓝 q) := by
      apply hzφ.congr'
      exact Filter.Eventually.of_forall fun n => by
        simpa only [mv] using
          (minimizingVec_exp
            (I := 𝓘(Real, E)) gExt hExt pt (seq (ns (φ n)))).symm
    have hexp :
        expMapIntrinsic (I := 𝓘(Real, E)) gExt hExt pt v = q :=
      tendsto_nhds_unique hexp_v hexp_q
    have hlen_v :
        Filter.Tendsto
          (fun n =>
            Real.sqrt
              (gExt.inner pt (mv (seq (ns (φ n))))
                (mv (seq (ns (φ n))))))
          Filter.atTop
          (𝓝 (Real.sqrt (gExt.inner pt v v))) := by
      simpa only [Function.comp_apply] using
        ((continuous_sqrt_gInner_self
          (I := 𝓘(Real, E)) gExt pt).tendsto v).comp hv
    have hdist_q :
        Filter.Tendsto
          (fun n =>
            Real.sqrt
              (gExt.inner pt (mv (seq (ns (φ n))))
                (mv (seq (ns (φ n))))))
          Filter.atTop (𝓝 (d q)) := by
      have hdistφ :
          Filter.Tendsto (fun n => d (seq (ns (φ n))) )
            Filter.atTop (𝓝 (d q)) :=
        (hd.tendsto q).comp hzφ
      apply hdistφ.congr'
      exact Filter.Eventually.of_forall fun n => by
        simpa only [mv, d] using
          (minimizingVec_len
            (I := 𝓘(Real, E)) gExt hExt pt (seq (ns (φ n)))).symm
    have hlen :
        Real.sqrt (gExt.inner pt v v) =
          (riemannianEDist 𝓘(Real, E) pt q).toReal :=
      tendsto_nhds_unique hlen_v hdist_q
    refine ⟨φ, ?_⟩
    rw [show v = u from huniq v hexp hlen] at hv
    simpa only [mv] using hv
  have hBopen : B.hom.source ∈ 𝓝 u :=
    B.hom.open_source.mem_nhds hu
  exact hmv hBopen

omit [T2Space M] [SigmaCompactSpace M] in
/-- Near a raw-core endpoint, one inverse exponential branch realizes the
actual raw pullback half-squared distance. -/
theorem rawCore_dist_germ
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) {R a K : Real} (hR : 0 < R) (h4aR : 4 * a < R)
    (hloc : IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
      (framedExpMap (I := I) g p) (Metric.ball (0 : E) R))
    (hdom : ∀ w : rawPullBall (E := E) R,
      ∀ s ∈ Set.Icc (0 : Real) 1,
        (show TangentSpace I p from
          s • normalFrame (I := I) g p (w : E)) ∈ expDomain (I := I) g p)
    (hK : 0 ≤ K)
    (hsmall : K * (2 * a) ^ 2 < (Real.pi / 2) ^ 2)
    (hRm : ∀ z : E, ‖z‖ < 3 * R / 4 →
      Real.sqrt (Tensor0SBundle.normSq0S (I := I) g
        (framedExpMap (I := I) g p z) 4
        (Geometry.Curvature.metricRm04At (I := I) (M := M) g
          (framedExpMap (I := I) g p z))) ≤ K)
    {pt q : rawPullBall (E := E) R}
    (hpt : pt ∈ rawCore (E := E) R a)
    (hq : q ∈ rawCore (E := E) R a) :
    let gExt := rawExtMetric (I := I) g p hR hloc
    letI : RiemannianBundle
        (fun z : E ↦ TangentSpace 𝓘(Real, E) z) :=
      ⟨gExt.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E
        (fun z : E ↦ TangentSpace 𝓘(Real, E) z) :=
      ⟨gExt.inner, gExt.contMDiff.continuous, by intro z v w; rfl⟩
    letI : PseudoEMetricSpace E :=
      PseudoEMetricSpace.ofRiemannianMetric 𝓘(Real, E) E
    letI : IsRiemannianManifold 𝓘(Real, E) E := ⟨fun _ _ => rfl⟩
    letI : UniformSpace E := PseudoEMetricSpace.toUniformSpace
    letI : CompleteSpace E := (rawExt_complete (I := I) g p hR hloc).complete
    let hExt : ∀ (z : E) (v : TangentSpace 𝓘(Real, E) z),
        ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (gExt.inner z v v)) :=
      fun z v => tensor0SBundle_enorm_eq_riemannianBundle_enorm
        (I := 𝓘(Real, E)) gExt z v
    let u := minimizingVec (I := 𝓘(Real, E)) gExt hExt (pt : E) (q : E)
    ∃ B : ExpInvBranch (I := 𝓘(Real, E)) gExt hExt (pt : E),
      (u : E) ∈ B.hom.source ∧
      (fun z : rawPullBall (E := E) R =>
        branchEnergy (I := 𝓘(Real, E)) gExt B (z : E)) =ᶠ[𝓝 q]
        (fun z =>
          (1 / 2 : Real) *
            (riemannianEDistOf (I := 𝓘(Real, E))
              (rawPullMetric (I := I) g p hloc) pt z).toReal ^ 2) := by
  classical
  let gExt := rawExtMetric (I := I) g p hR hloc
  letI : RiemannianBundle
      (fun z : E ↦ TangentSpace 𝓘(Real, E) z) :=
    ⟨gExt.toRiemannianMetric⟩
  letI (z : E) : NormedAddCommGroup (TangentSpace 𝓘(Real, E) z) := inferInstance
  letI (z : E) : NormedSpace Real (TangentSpace 𝓘(Real, E) z) := inferInstance
  letI : ∀ z : E, ENormSMulClass Real (TangentSpace 𝓘(Real, E) z) :=
    fun _ => inferInstance
  letI : IsContinuousRiemannianBundle E
      (fun z : E ↦ TangentSpace 𝓘(Real, E) z) :=
    ⟨gExt.inner, gExt.contMDiff.continuous, by intro z v w; rfl⟩
  letI : PseudoEMetricSpace E :=
    PseudoEMetricSpace.ofRiemannianMetric 𝓘(Real, E) E
  letI : IsRiemannianManifold 𝓘(Real, E) E := ⟨fun _ _ => rfl⟩
  letI : UniformSpace E := PseudoEMetricSpace.toUniformSpace
  letI : CompleteSpace E := (rawExt_complete (I := I) g p hR hloc).complete
  let hExt : ∀ (z : E) (v : TangentSpace 𝓘(Real, E) z),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (gExt.inner z v v)) :=
    fun z v => tensor0SBundle_enorm_eq_riemannianBundle_enorm
      (I := 𝓘(Real, E)) gExt z v
  let u := minimizingVec (I := 𝓘(Real, E)) gExt hExt (pt : E) (q : E)
  obtain ⟨L, h2aL, hbudget, hsmallL⟩ := exists_short_scale h4aR hsmall
  have hpt' : ‖(pt : E)‖ ≤ a := (mem_rawCore (E := E) pt).mp hpt
  have hq' : ‖(q : E)‖ ≤ a := (mem_rawCore (E := E) q).mp hq
  have ha : 0 ≤ a := (norm_nonneg (pt : E)).trans hpt'
  have haInner : a ≤ 3 * R / 4 := by linarith
  have hdist : riemannianEDistOf (I := 𝓘(Real, E)) gExt (pt : E) (q : E) ≤
      ENNReal.ofReal (2 * a) :=
    rawExt_edist_le (I := I) g hEnorm p hR hloc hpt' hq' haInner
      (hdom pt) (hdom q)
  have hdistReal : (riemannianEDistOf
      (I := 𝓘(Real, E)) gExt (pt : E) (q : E)).toReal ≤ 2 * a :=
    ENNReal.toReal_le_of_le_ofReal (mul_nonneg (by norm_num) ha) hdist
  have hu2a : Real.sqrt (gExt.inner (pt : E) u u) ≤ 2 * a := by
    rw [minimizingVec_len (I := 𝓘(Real, E)) gExt hExt (pt : E) (q : E)]
    exact hdistReal
  have huL : Real.sqrt (gExt.inner (pt : E) u u) ≤ L :=
    hu2a.trans h2aL.le
  have hnot :=
    rawCore_min_regular (I := I) g hEnorm p hR h4aR hloc hdom
      hK hsmall hRm hpt hq
  change ¬ IsConjVec (I := 𝓘(Real, E)) gExt hExt (pt : E) (u : E) at hnot
  obtain ⟨B, huB⟩ :=
    branch_of_not_conj (I := 𝓘(Real, E)) gExt hExt hnot
  have huniq :
      ∀ v : E,
        expMapIntrinsic (I := 𝓘(Real, E)) gExt hExt (pt : E) v = (q : E) →
        Real.sqrt (gExt.inner (pt : E) v v) =
          (riemannianEDist 𝓘(Real, E) (pt : E) (q : E)).toReal →
        v = u := by
    intro v hv hlen
    have hlenOf : Real.sqrt (gExt.inner (pt : E) v v) =
        (riemannianEDistOf
          (I := 𝓘(Real, E)) gExt (pt : E) (q : E)).toReal := by
      simpa only [riemannianEDistOf] using hlen
    have hvL : Real.sqrt (gExt.inner (pt : E) v v) ≤ L := by
      rw [hlenOf]
      exact hdistReal.trans h2aL.le
    have huEnd : rawExtLaunch (I := I) g p hR hloc (pt : E) u 1 = (q : E) := by
      simpa only [gExt, hExt, u, rawExtLaunch, expMapIntrinsic_def] using
        minimizingVec_exp (I := 𝓘(Real, E)) gExt hExt (pt : E) (q : E)
    have hvEnd : rawExtLaunch (I := I) g p hR hloc (pt : E) v 1 = (q : E) := by
      simpa only [gExt, hExt, rawExtLaunch, expMapIntrinsic_def] using hv
    exact rawCore_short_inj
      (I := I) g hEnorm p hR hloc hdom hK hRm hsmallL h2aL hbudget
        (x := (pt : E)) (y := (q : E)) (u := u) (v := v)
        hpt hq huL hvL huEnd hvEnd
  have hmem :=
    rawExt_minVec_mem (I := I) g p hR hloc
      (pt := (pt : E)) (q := (q : E)) (u := u) B huB huniq
  refine ⟨B, huB, ?_⟩
  have hgerm :=
    branchEnergy_min_germ (I := 𝓘(Real, E)) gExt hExt B hmem
  have hgerm' :
      branchEnergy (I := 𝓘(Real, E)) gExt B =ᶠ[𝓝 (q : E)]
        (fun z =>
          (1 / 2 : Real) *
            (riemannianEDistOf
              (I := 𝓘(Real, E)) gExt (pt : E) z).toReal ^ 2) := by
    simpa only [riemannianEDistOf] using hgerm
  have hgermSub :
      (fun z : rawPullBall (E := E) R =>
        branchEnergy (I := 𝓘(Real, E)) gExt B (z : E)) =ᶠ[𝓝 q]
        (fun z =>
          (1 / 2 : Real) *
            (riemannianEDistOf
              (I := 𝓘(Real, E)) gExt (pt : E) (z : E)).toReal ^ 2) := by
    simpa only [Function.comp_apply] using
      hgerm'.comp_tendsto (continuous_subtype_val.tendsto q)
  let a' : Real := (a + R / 4) / 2
  have haa' : a < a' := by
    dsimp only [a']
    linarith [h4aR]
  have h4a'R : 4 * a' < R := by
    dsimp only [a']
    linarith [h4aR]
  have hptA : pt ∈ rawCore (E := E) R a' := by
    apply (mem_rawCore (E := E) pt).mpr
    exact hpt'.trans haa'.le
  have hqBall : (q : E) ∈ Metric.ball (0 : E) a' := by
    rw [Metric.mem_ball, dist_zero_right]
    exact hq'.trans_lt haa'
  have hnear : ∀ᶠ z in 𝓝 q, z ∈ rawCore (E := E) R a' := by
    have hpre :
        (fun z : rawPullBall (E := E) R => (z : E)) ⁻¹'
            Metric.ball (0 : E) a' ∈ 𝓝 q :=
      continuous_subtype_val.continuousAt.preimage_mem_nhds
        (Metric.ball_mem_nhds (q : E) hqBall)
    filter_upwards [hpre] with z hz
    apply (mem_rawCore (E := E) z).mpr
    exact le_of_lt (by
      simpa only [Metric.mem_ball, dist_zero_right] using hz)
  filter_upwards [hgermSub, hnear] with z hz hcore
  rw [rawCore_edist_eq (I := I) g hEnorm p hR h4a'R hloc hdom hptA hcore]
  exact hz

attribute [-instance] Subtype.metricSpace Subtype.pseudoMetricSpace in
omit [T2Space M] [SigmaCompactSpace M] in
/-- On the raw norm core, half-squared pullback distance is strictly midpoint
convex along fenced minimizing joins. -/
theorem rawCore_jensen
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) {R a K : Real} (hR : 0 < R) (h4aR : 4 * a < R)
    (hloc : IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
      (framedExpMap (I := I) g p) (Metric.ball (0 : E) R))
    (hdom : ∀ w : rawPullBall (E := E) R,
      ∀ s ∈ Set.Icc (0 : Real) 1,
        (show TangentSpace I p from
          s • normalFrame (I := I) g p (w : E)) ∈ expDomain (I := I) g p)
    (hK : 0 ≤ K)
    (hsmall : K * (2 * a) ^ 2 < (Real.pi / 2) ^ 2)
    (hRm : ∀ z : E, ‖z‖ < 3 * R / 4 →
      Real.sqrt (Tensor0SBundle.normSq0S (I := I) g
        (framedExpMap (I := I) g p z) 4
        (Geometry.Curvature.metricRm04At (I := I) (M := M) g
          (framedExpMap (I := I) g p z))) ≤ K) :
    let gPull := rawPullMetric (I := I) g p hloc
    letI : RiemannianBundle
        (fun z : rawPullBall (E := E) R ↦ TangentSpace 𝓘(Real, E) z) :=
      ⟨gPull.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E
        (fun z : rawPullBall (E := E) R ↦ TangentSpace 𝓘(Real, E) z) :=
      ⟨gPull.inner, gPull.contMDiff.continuous, by intro z v w; rfl⟩
    letI : ConnectedSpace (rawPullBall (E := E) R) :=
      Subtype.connectedSpace (isConnected_ball hR)
    letI : MetricSpace (rawPullBall (E := E) R) :=
      HopfRinow.riemMetricSpace
        (I := 𝓘(Real, E)) (M := rawPullBall (E := E) R)
    ∃ join :
        rawPullBall (E := E) R →
        rawPullBall (E := E) R →
        Real → rawPullBall (E := E) R,
      ∀ pt ∈ rawCore (E := E) R a,
        CenterOfMass.StrictMidJensenOn join
          (rawCore (E := E) R a) (CenterOfMass.halfSqDist pt) := by
  classical
  let gPull := rawPullMetric (I := I) g p hloc
  letI : RiemannianBundle
      (fun z : rawPullBall (E := E) R ↦ TangentSpace 𝓘(Real, E) z) :=
    ⟨gPull.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle E
      (fun z : rawPullBall (E := E) R ↦ TangentSpace 𝓘(Real, E) z) :=
    ⟨gPull.inner, gPull.contMDiff.continuous, by intro z v w; rfl⟩
  letI : ConnectedSpace (rawPullBall (E := E) R) :=
    Subtype.connectedSpace (isConnected_ball hR)
  letI : MetricSpace (rawPullBall (E := E) R) :=
    HopfRinow.riemMetricSpace
      (I := 𝓘(Real, E)) (M := rawPullBall (E := E) R)
  obtain ⟨L, h2aL, hbudget, hsmallL⟩ := exists_short_scale h4aR hsmall
  let join : rawPullBall (E := E) R → rawPullBall (E := E) R →
      Real → rawPullBall (E := E) R := fun x y =>
    if hxy : x ∈ rawCore (E := E) R a ∧ y ∈ rawCore (E := E) R a then
      Classical.choose (exists_raw_fenced (I := I) g hEnorm p hR h4aR hloc
        hdom hxy.1 hxy.2)
    else fun _ => x
  have hjoin :
      ∀ x ∈ rawCore (E := E) R a, ∀ y ∈ rawCore (E := E) R a,
        ContMDiff 𝓘(Real, Real) 𝓘(Real, E) ∞ (join x y) ∧
        IsGeodesicOn (I := 𝓘(Real, E)) gPull (join x y)
          (Set.Icc (0 : Real) 1) ∧
        join x y 0 = x ∧ join x y 1 = y ∧
        (∀ t ∈ Set.Icc (0 : Real) 1,
          ‖((join x y t : rawPullBall (E := E) R) : E)‖ < 3 * R / 4) ∧
        Set.EqOn (fun t => ((join x y t : rawPullBall (E := E) R) : E))
          (rawExtJoin (I := I) g p hR hloc (x : E) (y : E))
          (Set.Icc (0 : Real) 1) := by
    intro x hx y hy
    dsimp only [join]
    rw [dif_pos ⟨hx, hy⟩]
    exact Classical.choose_spec
      (exists_raw_fenced (I := I) g hEnorm p hR h4aR hloc hdom hx hy)
  let gExt := rawExtMetric (I := I) g p hR hloc
  letI : RiemannianBundle
      (fun z : E ↦ TangentSpace 𝓘(Real, E) z) :=
    ⟨gExt.toRiemannianMetric⟩
  letI (z : E) : NormedAddCommGroup (TangentSpace 𝓘(Real, E) z) := inferInstance
  letI (z : E) : NormedSpace Real (TangentSpace 𝓘(Real, E) z) := inferInstance
  letI : ∀ z : E, ENormSMulClass Real (TangentSpace 𝓘(Real, E) z) :=
    fun _ => inferInstance
  letI : IsContinuousRiemannianBundle E
      (fun z : E ↦ TangentSpace 𝓘(Real, E) z) :=
    ⟨gExt.inner, gExt.contMDiff.continuous, by intro z v w; rfl⟩
  letI : PseudoEMetricSpace E :=
    PseudoEMetricSpace.ofRiemannianMetric 𝓘(Real, E) E
  letI : IsRiemannianManifold 𝓘(Real, E) E := ⟨fun _ _ => rfl⟩
  letI : UniformSpace E := PseudoEMetricSpace.toUniformSpace
  letI : CompleteSpace E := (rawExt_complete (I := I) g p hR hloc).complete
  let hExt : ∀ (z : E) (v : TangentSpace 𝓘(Real, E) z),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (gExt.inner z v v)) :=
    fun z v => tensor0SBundle_enorm_eq_riemannianBundle_enorm
      (I := 𝓘(Real, E)) gExt z v
  have haR : a < R := by linarith
  have hcoreJoin :
      ∀ x ∈ rawCore (E := E) R a, ∀ y ∈ rawCore (E := E) R a,
        ∀ t ∈ Set.Icc (0 : Real) 1, join x y t ∈ rawCore (E := E) R a := by
    intro x hx y hy t ht
    let v : E := minimizingVec (I := 𝓘(Real, E)) gExt hExt (x : E) (y : E)
    have hx' : ‖(x : E)‖ ≤ a := (mem_rawCore (E := E) x).mp hx
    have hy' : ‖(y : E)‖ ≤ a := (mem_rawCore (E := E) y).mp hy
    have ha : 0 ≤ a := (norm_nonneg (x : E)).trans hx'
    have haInner : a ≤ 3 * R / 4 := by linarith
    have hdist : riemannianEDistOf (I := 𝓘(Real, E)) gExt (x : E) (y : E) ≤
        ENNReal.ofReal (2 * a) :=
      rawExt_edist_le (I := I) g hEnorm p hR hloc hx' hy' haInner
        (hdom x) (hdom y)
    have hdistReal : (riemannianEDistOf
        (I := 𝓘(Real, E)) gExt (x : E) (y : E)).toReal ≤ 2 * a :=
      ENNReal.toReal_le_of_le_ofReal (mul_nonneg (by norm_num) ha) hdist
    have hvL : Real.sqrt (gExt.inner (x : E) v v) ≤ L := by
      rw [show Real.sqrt (gExt.inner (x : E) v v) =
        (riemannianEDistOf (I := 𝓘(Real, E)) gExt (x : E) (y : E)).toReal by
        simpa only [v, riemannianEDistOf] using
          minimizingVec_len (I := 𝓘(Real, E)) gExt hExt (x : E) (y : E)]
      exact hdistReal.trans h2aL.le
    have hvEnd : rawExtLaunch (I := I) g p hR hloc (x : E) v 1 = (y : E) := by
      simpa only [gExt, hExt, v, rawExtLaunch, expMapIntrinsic_def] using
        minimizingVec_exp (I := 𝓘(Real, E)) gExt hExt (x : E) (y : E)
    have hcoreExt := rawExt_edge_core (I := I) g hEnorm p hR hloc hdom
      hK hRm hsmallL h2aL hbudget hx' hy' v hvL hvEnd t ht
    have hdim : Module.finrank Real E ≠ 0 := NeZero.ne _
    have hLaunch : rawExtLaunch (I := I) g p hR hloc (x : E) v =
        rawExtJoin (I := I) g p hR hloc (x : E) (y : E) := by
      rw [rawExtJoin_eq_min (I := I) g p hR hloc hdim (x : E) (y : E)]
      change intrinsicGeodesic (I := 𝓘(Real, E)) gExt hExt (x : E) v =
        minJoin (I := 𝓘(Real, E)) gExt hExt (x : E) (y : E)
      rfl
    have hEq := (hjoin x hx y hy).2.2.2.2.2 ht
    have hEq' : ((join x y t : rawPullBall (E := E) R) : E) =
        rawExtJoin (I := I) g p hR hloc (x : E) (y : E) t := by
      simpa only using hEq
    apply (mem_rawCore (E := E) (join x y t)).mpr
    rw [hEq', ← hLaunch]
    simpa only [gExt, hExt, v] using hcoreExt
  refine ⟨join, ?_⟩
  intro pt hpt
  apply CenterOfMass.jensen_of_strict
  · intro x hx y hy hxy
    exact hcoreJoin x hx y hy (1 / 2 : Real) (by constructor <;> norm_num)
  · intro x hx y hy
    exact (hjoin x hx y hy).2.2.1
  · intro x hx y hy
    exact (hjoin x hx y hy).2.2.2.1
  · intro x hx y hy hxy
    let γ : Real → E := rawExtJoin (I := I) g p hR hloc (x : E) (y : E)
    let uxy : E := minimizingVec (I := 𝓘(Real, E)) gExt hExt (x : E) (y : E)
    have huxy : uxy ≠ 0 := by
      intro hu0
      apply hxy
      apply Subtype.ext
      have hzero := expMapIntrinsic_zero
        (I := 𝓘(Real, E)) gExt hExt (x : E)
      have hend := minimizingVec_exp
        (I := 𝓘(Real, E)) gExt hExt (x : E) (y : E)
      calc
        (x : E) = expMapIntrinsic (I := 𝓘(Real, E)) gExt hExt (x : E) 0 :=
          hzero.symm
        _ = expMapIntrinsic (I := 𝓘(Real, E)) gExt hExt (x : E) uxy := by
          rw [hu0]
          rfl
        _ = (y : E) := by simpa only [uxy] using hend
    have hγsmooth : ContMDiff 𝓘(Real, Real) 𝓘(Real, E) ∞ γ := by
      simpa only [γ] using rawExtJoin_smooth (I := I) g p hR hloc (x : E) (y : E)
    have hγgeo : IsGeodesic (I := 𝓘(Real, E)) gExt γ := by
      simpa only [γ, gExt] using rawExtJoin_geo (I := I) g p hR hloc (x : E) (y : E)
    have hvel (t : Real) :
        (mfderiv 𝓘(Real, Real) 𝓘(Real, E) γ t (1 : Real) : E) ≠ 0 := by
      simpa only [γ, uxy, gExt, hExt, rawExtJoin] using
        intrGeo_vel_ne (I := 𝓘(Real, E)) gExt hExt (x : E) uxy huxy t
    let f : E → Real := fun z => (1 / 2 : Real) *
      (riemannianEDistOf (I := 𝓘(Real, E)) gExt (pt : E) z).toReal ^ 2
    have hfinite :
        {z : E | riemannianEDist 𝓘(Real, E) (pt : E) z ≠ (⊤ : ENNReal)} =
          Set.univ := by
      ext z
      simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
      exact riemannianEDist_ne_top (I := 𝓘(Real, E)) (pt : E) z
    have hdistCont : Continuous fun z : E =>
        (riemannianEDistOf (I := 𝓘(Real, E)) gExt (pt : E) z).toReal := by
      have hOn := continuousOn_riemannianEDist_toReal_on_finite gExt (pt : E)
      rw [hfinite] at hOn
      simpa only [riemannianEDistOf] using continuousOn_univ.mp hOn
    have hfcont : Continuous f := continuous_const.mul (hdistCont.pow 2)
    have hstrictExt : StrictConvexOn Real (Set.Icc (0 : Real) 1) (f ∘ γ) := by
      apply strictConvexOn_of_deriv2_pos
        (convex_Icc (0 : Real) 1)
        (hfcont.comp hγsmooth.continuous).continuousOn
      intro t ht
      rw [interior_Icc] at ht
      have htIcc : t ∈ Set.Icc (0 : Real) 1 := ⟨ht.1.le, ht.2.le⟩
      have hqtJoin := hcoreJoin x hx y hy t htIcc
      have hEq := (hjoin x hx y hy).2.2.2.2.2 htIcc
      have hEq' : ((join x y t : rawPullBall (E := E) R) : E) = γ t := by
        simpa only [γ] using hEq
      let qU : rawPullBall (E := E) R := ⟨γ t, by
        rw [Metric.mem_ball, dist_zero_right]
        have hqtNorm : ‖γ t‖ ≤ a := by
          change ‖((join x y t : rawPullBall (E := E) R) : E)‖ ≤ a at hqtJoin
          rw [hEq'] at hqtJoin
          exact hqtJoin
        exact hqtNorm.trans_lt haR⟩
      have hqU : qU ∈ rawCore (E := E) R a := by
        apply (mem_rawCore (E := E) qU).mpr
        change ‖γ t‖ ≤ a
        change ‖((join x y t : rawPullBall (E := E) R) : E)‖ ≤ a at hqtJoin
        rwa [hEq'] at hqtJoin
      let v : E := minimizingVec (I := 𝓘(Real, E)) gExt hExt (pt : E) (qU : E)
      obtain ⟨B, hvB, hgerm⟩ := rawCore_dist_germ (I := I) g hEnorm p hR
        h4aR hloc hdom hK hsmall hRm hpt hqU
      have ha : 0 ≤ a := (norm_nonneg (pt : E)).trans (mem_rawCore.mp hpt)
      have haInner : a ≤ 3 * R / 4 := by linarith
      have hdist : riemannianEDistOf (I := 𝓘(Real, E)) gExt (pt : E) (qU : E) ≤
          ENNReal.ofReal (2 * a) :=
        rawExt_edist_le (I := I) g hEnorm p hR hloc
          (mem_rawCore.mp hpt) (mem_rawCore.mp hqU) haInner (hdom pt) (hdom qU)
      have hdistReal : (riemannianEDistOf
          (I := 𝓘(Real, E)) gExt (pt : E) (qU : E)).toReal ≤ 2 * a :=
        ENNReal.toReal_le_of_le_ofReal (mul_nonneg (by norm_num) ha) hdist
      have hvL : Real.sqrt (gExt.inner (pt : E) v v) ≤ L := by
        rw [show Real.sqrt (gExt.inner (pt : E) v v) =
          (riemannianEDistOf (I := 𝓘(Real, E)) gExt (pt : E) (qU : E)).toReal by
          simpa only [v, riemannianEDistOf] using
            minimizingVec_len (I := 𝓘(Real, E)) gExt hExt (pt : E) (qU : E)]
        exact hdistReal.trans h2aL.le
      have hvEnd : rawExtLaunch (I := I) g p hR hloc (pt : E) v 1 = (qU : E) := by
        simpa only [gExt, hExt, v, rawExtLaunch, expMapIntrinsic_def] using
          minimizingVec_exp (I := 𝓘(Real, E)) gExt hExt (pt : E) (qU : E)
      have hdim : Module.finrank Real E ≠ 0 := NeZero.ne _
      have hvLaunch : rawExtLaunch (I := I) g p hR hloc (pt : E) v =
          rawExtJoin (I := I) g p hR hloc (pt : E) (qU : E) := by
        rw [rawExtJoin_eq_min (I := I) g p hR hloc hdim (pt : E) (qU : E)]
        change intrinsicGeodesic (I := 𝓘(Real, E)) gExt hExt (pt : E) v =
          minJoin (I := 𝓘(Real, E)) gExt hExt (pt : E) (qU : E)
        rfl
      have hvFence : ∀ s ∈ Set.Icc (0 : Real) 1,
          ‖rawExtLaunch (I := I) g p hR hloc (pt : E) v s‖ < 3 * R / 4 := by
        rw [hvLaunch]
        exact rawExtJoin_fenced (I := I) g hEnorm p hR h4aR hloc hdom
          (mem_rawCore.mp hpt) (mem_rawCore.mp hqU)
      let Y : E := (mfderiv 𝓘(Real, Real) 𝓘(Real, E) γ t (1 : Real) : E)
      have hY : Y ≠ 0 := by simpa only [Y] using hvel t
      have hposRaw := rawBranch_hess_pos (I := I) g p hR hloc hK hRm hsmallL
        (x := (pt : E)) v hvFence hvL B hvB (Y := Y) hY
      have hvEndγ : expMapIntrinsic (I := 𝓘(Real, E)) gExt hExt (pt : E) v =
          γ t := by simpa only [qU] using hvEnd
      rw [hvEndγ] at hposRaw
      have hpos : 0 < hessFun (I := 𝓘(Real, E)) gExt
          (branchEnergy (I := 𝓘(Real, E)) gExt B) (γ t) Y Y := by
        simpa only [gExt, hExt, Y] using hposRaw
      have hBmap : B.hom (v : E) = (qU : E) := (B.hom_eq hvB).symm.trans hvEnd
      have hqDom : γ t ∈ B.dom := by
        change (qU : E) ∈ B.dom
        rw [← hBmap]
        exact B.hom.map_source hvB
      have hbranch : ContMDiffOn 𝓘(Real, E) 𝓘(Real, Real) ∞
          (branchEnergy (I := 𝓘(Real, E)) gExt B) B.dom := by
        let gp : E →L[Real] E →L[Real] Real := gExt.inner (pt : E)
        have hgp : ContMDiffOn 𝓘(Real, E)
            𝓘(Real, E →L[Real] E →L[Real] Real) ∞ (fun _ : E => gp) B.dom :=
          contMDiffOn_const
        have hinv : ContMDiffOn 𝓘(Real, E) 𝓘(Real, E) ∞ B.inv B.dom := B.inv_inf
        have hinner : ContMDiffOn 𝓘(Real, E) 𝓘(Real, Real) ∞
            (fun z : E => gExt.inner (pt : E) (B.inv z) (B.inv z)) B.dom := by
          simpa only [gp] using (hgp.clm_apply hinv).clm_apply hinv
        simpa only [branchEnergy] using contMDiffOn_const.mul hinner
      have hd2Branch := deriv2_geo_on_at (I := 𝓘(Real, E)) gExt
        B.hom.open_target hbranch hγsmooth (hγgeo t) hqDom
      have hqEq : join x y t = qU := by
        apply Subtype.ext
        exact hEq'
      have hjoinTendsto : Filter.Tendsto (join x y) (𝓝 t) (𝓝 qU) := by
        rw [← hqEq]
        exact (hjoin x hx y hy).1.continuous.tendsto t
      have hgermAlong :
          (fun s : Real => branchEnergy (I := 𝓘(Real, E)) gExt B
            ((join x y s : rawPullBall (E := E) R) : E)) =ᶠ[𝓝 t]
          (fun s => (1 / 2 : Real) *
            (riemannianEDistOf (I := 𝓘(Real, E)) gPull pt (join x y s)).toReal ^ 2) := by
        simpa only using hgerm.comp_tendsto hjoinTendsto
      have hIcc : ∀ᶠ s in 𝓝 t, s ∈ Set.Icc (0 : Real) 1 :=
        Filter.mem_of_superset (Ioo_mem_nhds ht.1 ht.2) Set.Ioo_subset_Icc_self
      have hcomp : (branchEnergy (I := 𝓘(Real, E)) gExt B) ∘ γ =ᶠ[𝓝 t]
          f ∘ γ := by
        filter_upwards [hgermAlong, hIcc] with s hs hsIcc
        have hsCore := hcoreJoin x hx y hy s hsIcc
        have hsEq := (hjoin x hx y hy).2.2.2.2.2 hsIcc
        have hsEq' : ((join x y s : rawPullBall (E := E) R) : E) = γ s := by
          simpa only [γ] using hsEq
        calc
          branchEnergy (I := 𝓘(Real, E)) gExt B (γ s) =
              branchEnergy (I := 𝓘(Real, E)) gExt B
                ((join x y s : rawPullBall (E := E) R) : E) := by rw [hsEq']
          _ = (1 / 2 : Real) *
              (riemannianEDistOf (I := 𝓘(Real, E)) gPull pt (join x y s)).toReal ^ 2 := hs
          _ = f (γ s) := by
            dsimp only [f]
            rw [rawCore_edist_eq (I := I) g hEnorm p hR h4aR hloc hdom hpt hsCore,
              hsEq']
      have hd2Eq : (deriv^[2] (f ∘ γ)) t =
          (deriv^[2] ((branchEnergy (I := 𝓘(Real, E)) gExt B) ∘ γ)) t :=
        Filter.EventuallyEq.deriv_eq hcomp.symm.deriv
      rw [hd2Eq, hd2Branch]
      exact hpos
    apply hstrictExt.congr
    intro t ht
    have hqt := hcoreJoin x hx y hy t ht
    have hEq := (hjoin x hx y hy).2.2.2.2.2 ht
    have hEq' : ((join x y t : rawPullBall (E := E) R) : E) = γ t := by
      simpa only [γ] using hEq
    have hdistPull : dist (join x y t) pt =
        (riemannianEDistOf (I := 𝓘(Real, E)) gExt (pt : E) (γ t)).toReal := by
      calc
        dist (join x y t) pt = dist pt (join x y t) := dist_comm _ _
        _ = (riemannianEDist 𝓘(Real, E) pt (join x y t)).toReal :=
          HopfRinow.riemMetric_dist_eq (I := 𝓘(Real, E))
            (M := rawPullBall (E := E) R) pt (join x y t)
        _ = (riemannianEDistOf (I := 𝓘(Real, E)) gPull pt (join x y t)).toReal := by
          rfl
        _ = (riemannianEDistOf (I := 𝓘(Real, E)) gExt (pt : E)
              ((join x y t : rawPullBall (E := E) R) : E)).toReal := by
          rw [rawCore_edist_eq (I := I) g hEnorm p hR h4aR hloc hdom hpt hqt]
        _ = (riemannianEDistOf (I := 𝓘(Real, E)) gExt (pt : E) (γ t)).toReal := by
          rw [hEq']
    simp only [Function.comp_apply, f, CenterOfMass.halfSqDist]
    rw [hdistPull]

end CGT
end Riemannian
end Geometry
end DifferentialGeometry

end
