import DifferentialGeometry.Geometry.Comparison.CGTRawExpLift
import DifferentialGeometry.Geometry.Comparison.CGTRawLiftOps
import DifferentialGeometry.Geometry.Comparison.CGTRawPullback
import Mathlib.Topology.Homotopy.Lifting

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
variable [hPseudo : PseudoEMetricSpace M]
  [hRiemMan : IsRiemannianManifold I M]
  [hContRiem : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

noncomputable local instance {R : Real} :
    SigmaCompactSpace (rawPullBall (E := E) R) :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen
      𝓘(Real, E) (rawPullBall (E := E) R).isOpen)

section

/-- The closed norm core inside the raw pullback ball. -/
def rawCore (R a : Real) : Set (rawPullBall (E := E) R) :=
  {z | ‖(z : E)‖ ≤ a}

omit [InnerProductSpace Real E] [FiniteDimensional Real E] in
/-- Membership in the raw core is exactly the model-space norm bound. -/
@[simp] theorem mem_rawCore {R a : Real} (z : rawPullBall (E := E) R) :
    z ∈ rawCore (E := E) R a ↔ ‖(z : E)‖ ≤ a :=
  Iff.rfl

/-- A loop based at the center followed by a raw radial path. -/
noncomputable def rawLoopPath
    (g : SmoothRiemannianMetric I M) (p : M) (c : Path p p) (z : E)
    (hdom : ∀ s ∈ Set.Icc (0 : Real) 1,
      (show TangentSpace I p from
        s • normalFrame (I := I) g p z) ∈ expDomain (I := I) g p) :
    Path p (framedExpMap (I := I) g p z) :=
  c.trans (rawFlatPath (I := I) g p z hdom)

omit [T2Space M] hPseudo hRiemMan hContRiem in
/-- The raw loop-radial path is flat and C1. -/
theorem rawLoop_flat
    (g : SmoothRiemannianMetric I M) (p : M) (c : Path p p)
    (hc : IsFlatC1Path (I := I) c) (z : E)
    (hdom : ∀ s ∈ Set.Icc (0 : Real) 1,
      (show TangentSpace I p from
        s • normalFrame (I := I) g p z) ∈ expDomain (I := I) g p) :
    IsFlatC1Path (I := I) (rawLoopPath (I := I) g p c z hdom) :=
  hc.trans (rawFlatPath_flat (I := I) g p z hdom)

omit [T2Space M] hPseudo hRiemMan hContRiem in
/-- The raw loop-radial path has loop length plus the launch norm. -/
theorem rawLoop_len
    [PseudoEMetricSpace M] [IsRiemannianManifold I M]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) (c : Path p p) (hc : IsFlatC1Path (I := I) c) (z : E)
    (hdom : ∀ s ∈ Set.Icc (0 : Real) 1,
      (show TangentSpace I p from
        s • normalFrame (I := I) g p z) ∈ expDomain (I := I) g p) :
    pathLen (I := I) (rawLoopPath (I := I) g p c z hdom) =
      pathLen (I := I) c + ENNReal.ofReal ‖z‖ := by
  rw [rawLoopPath, pathLen_trans hc
    (rawFlatPath_flat (I := I) g p z hdom),
    rawFlatPath_len (I := I) g hEnorm p z hdom]

omit [T2Space M] hPseudo hRiemMan hContRiem in
/-- A short loop followed by a raw radial path stays below the combined length
budget. -/
theorem rawLoop_len_lt
    [PseudoEMetricSpace M] [IsRiemannianManifold I M]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) {L a : Real} (hL : 0 ≤ L) (ha : 0 ≤ a)
    (c : Path p p) (hc : IsFlatC1Path (I := I) c)
    (hcLen : pathLen (I := I) c < ENNReal.ofReal L)
    {z : E} (hz : ‖z‖ ≤ a)
    (hdom : ∀ s ∈ Set.Icc (0 : Real) 1,
      (show TangentSpace I p from
        s • normalFrame (I := I) g p z) ∈ expDomain (I := I) g p) :
    pathLen (I := I) (rawLoopPath (I := I) g p c z hdom) <
      ENNReal.ofReal (L + a) := by
  rw [rawLoop_len (I := I) g hEnorm p c hc z hdom]
  calc
    pathLen (I := I) c + ENNReal.ofReal ‖z‖ <
        ENNReal.ofReal L + ENNReal.ofReal a :=
      ENNReal.add_lt_add_of_lt_of_le ENNReal.ofReal_ne_top
        hcLen (ENNReal.ofReal_le_ofReal hz)
    _ = ENNReal.ofReal (L + a) := (ENNReal.ofReal_add hL ha).symm

/-- Every raw loop-radial path from the core has a lift through the raw framed
exponential on the full unit interval. -/
theorem rawLoop_lift_exists
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) {R L a : Real} (hL : 0 ≤ L) (ha : 0 ≤ a)
    (hfit : L + a < R)
    (hdom : ∀ z ∈ Metric.ball (0 : E) R, ∀ s ∈ Set.Icc (0 : Real) 1,
      (show TangentSpace I p from
        s • normalFrame (I := I) g p z) ∈ expDomain (I := I) g p)
    (hloc : IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
      (framedExpMap (I := I) g p) (Metric.ball (0 : E) R))
    (c : Path p p) (hc : IsFlatC1Path (I := I) c)
    (hcLen : pathLen (I := I) c < ENNReal.ofReal L)
    (z : rawPullBall (E := E) R) (hz : z ∈ rawCore (E := E) R a) :
    ∃ η : Real → E,
      IsLiftOn (framedExpMap (I := I) g p)
        (rawLoopPath (I := I) g p c (z : E)
          (hdom z z.property)).extend
        (Metric.ball (0 : E) R) 0 0 1 η := by
  have hR : 0 < R := (add_nonneg hL ha).trans_lt hfit
  have hlenLa := rawLoop_len_lt (I := I) g hEnorm p hL ha
    c hc hcLen ((mem_rawCore (E := E) z).mp hz) (hdom z z.property)
  have hlenR :
      pathLen (I := I)
          (rawLoopPath (I := I) g p c (z : E) (hdom z z.property)) <
        ENNReal.ofReal R :=
    hlenLa.trans ((ENNReal.ofReal_lt_ofReal_iff hR).2 hfit)
  apply exists_raw_lift (I := I) g hEnorm p zero_le_one
    (rawLoop_flat (I := I) g p c hc (z : E)
      (hdom z z.property)).c1.contMDiffOn
  · simp only [Path.extend_zero]
  · exact hR
  · exact hlenR
  · exact hdom
  · exact hloc

/-- The chosen raw lift of a loop-radial path. -/
noncomputable def rawLoopLift
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) {R L a : Real} (hL : 0 ≤ L) (ha : 0 ≤ a)
    (hfit : L + a < R)
    (hdom : ∀ z ∈ Metric.ball (0 : E) R, ∀ s ∈ Set.Icc (0 : Real) 1,
      (show TangentSpace I p from
        s • normalFrame (I := I) g p z) ∈ expDomain (I := I) g p)
    (hloc : IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
      (framedExpMap (I := I) g p) (Metric.ball (0 : E) R))
    (c : Path p p) (hc : IsFlatC1Path (I := I) c)
    (hcLen : pathLen (I := I) c < ENNReal.ofReal L)
    (z : rawPullBall (E := E) R) (hz : z ∈ rawCore (E := E) R a) :
    Real → E :=
  Classical.choose
    (rawLoop_lift_exists (I := I) g hEnorm p hL ha hfit hdom hloc
      c hc hcLen z hz)

/-- The chosen raw loop lift satisfies the canonical `IsLiftOn` predicate. -/
theorem rawLoopLift_spec
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) {R L a : Real} (hL : 0 ≤ L) (ha : 0 ≤ a)
    (hfit : L + a < R)
    (hdom : ∀ z ∈ Metric.ball (0 : E) R, ∀ s ∈ Set.Icc (0 : Real) 1,
      (show TangentSpace I p from
        s • normalFrame (I := I) g p z) ∈ expDomain (I := I) g p)
    (hloc : IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
      (framedExpMap (I := I) g p) (Metric.ball (0 : E) R))
    (c : Path p p) (hc : IsFlatC1Path (I := I) c)
    (hcLen : pathLen (I := I) c < ENNReal.ofReal L)
    (z : rawPullBall (E := E) R) (hz : z ∈ rawCore (E := E) R a) :
    IsLiftOn (framedExpMap (I := I) g p)
      (rawLoopPath (I := I) g p c (z : E) (hdom z z.property)).extend
      (Metric.ball (0 : E) R) 0 0 1
      (rawLoopLift (I := I) g hEnorm p hL ha hfit hdom hloc
        c hc hcLen z hz) :=
  Classical.choose_spec
    (rawLoop_lift_exists (I := I) g hEnorm p hL ha hfit hdom hloc
      c hc hcLen z hz)

/-- The endpoint of the chosen raw loop lift. -/
noncomputable def rawTransport
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) {R L a : Real} (hL : 0 ≤ L) (ha : 0 ≤ a)
    (hfit : L + a < R)
    (hdom : ∀ z ∈ Metric.ball (0 : E) R, ∀ s ∈ Set.Icc (0 : Real) 1,
      (show TangentSpace I p from
        s • normalFrame (I := I) g p z) ∈ expDomain (I := I) g p)
    (hloc : IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
      (framedExpMap (I := I) g p) (Metric.ball (0 : E) R))
    (c : Path p p) (hc : IsFlatC1Path (I := I) c)
    (hcLen : pathLen (I := I) c < ENNReal.ofReal L)
    (z : rawPullBall (E := E) R) (hz : z ∈ rawCore (E := E) R a) :
    rawPullBall (E := E) R :=
  ⟨rawLoopLift (I := I) g hEnorm p hL ha hfit hdom hloc
      c hc hcLen z hz 1,
    (rawLoopLift_spec (I := I) g hEnorm p hL ha hfit hdom hloc
      c hc hcLen z hz).mapsTo ⟨zero_le_one, le_rfl⟩⟩

/-- Raw loop transport stays in the same framed-exponential fiber. -/
theorem rawTransport_exp
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) {R L a : Real} (hL : 0 ≤ L) (ha : 0 ≤ a)
    (hfit : L + a < R)
    (hdom : ∀ z ∈ Metric.ball (0 : E) R, ∀ s ∈ Set.Icc (0 : Real) 1,
      (show TangentSpace I p from
        s • normalFrame (I := I) g p z) ∈ expDomain (I := I) g p)
    (hloc : IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
      (framedExpMap (I := I) g p) (Metric.ball (0 : E) R))
    (c : Path p p) (hc : IsFlatC1Path (I := I) c)
    (hcLen : pathLen (I := I) c < ENNReal.ofReal L)
    (z : rawPullBall (E := E) R) (hz : z ∈ rawCore (E := E) R a) :
    framedExpMap (I := I) g p
        (rawTransport (I := I) g hEnorm p hL ha hfit hdom hloc
          c hc hcLen z hz : E) =
      framedExpMap (I := I) g p (z : E) := by
  have hspec := rawLoopLift_spec (I := I) g hEnorm p hL ha hfit
    hdom hloc c hc hcLen z hz
  have h1 := hspec.2.2 (1 : Real) ⟨zero_le_one, le_rfl⟩
  simpa only [rawTransport, Function.comp_apply, Path.extend_one,
    rawLoopPath] using h1.2

/-- Raw loop transport is continuous on the norm core. -/
theorem rawTransport_cont
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) {R L a : Real} (hL : 0 ≤ L) (ha : 0 ≤ a)
    (hfit : L + a < R)
    (hdom : ∀ z ∈ Metric.ball (0 : E) R, ∀ s ∈ Set.Icc (0 : Real) 1,
      (show TangentSpace I p from
        s • normalFrame (I := I) g p z) ∈ expDomain (I := I) g p)
    (hloc : IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
      (framedExpMap (I := I) g p) (Metric.ball (0 : E) R))
    (c : Path p p) (hc : IsFlatC1Path (I := I) c)
    (hcLen : pathLen (I := I) c < ENNReal.ofReal L) :
    Continuous
      (fun z : {z : rawPullBall (E := E) R // z ∈ rawCore (E := E) R a} =>
        rawTransport (I := I) g hEnorm p hL ha hfit hdom hloc
          c hc hcLen z.1 z.2) := by
  let Core :=
    {z : rawPullBall (E := E) R // z ∈ rawCore (E := E) R a}
  let Uo : TopologicalSpace.Opens E := rawPullBall (E := E) R
  let fU : Uo → M := rawExpOn (I := I) g p R
  have hR : 0 < R := (add_nonneg hL ha).trans_lt hfit
  have haR : a < R := (le_add_of_nonneg_left hL).trans_lt hfit
  have hlocU : IsLocalDiffeomorph 𝓘(Real, E) I ∞ fU :=
    rawExpOn_local (I := I) g p hloc
  let lift : unitInterval × Core → Uo :=
    fun tz =>
      ⟨rawLoopLift (I := I) g hEnorm p hL ha hfit hdom hloc
          c hc hcLen tz.2.1 tz.2.2 tz.1,
        (rawLoopLift_spec (I := I) g hEnorm p hL ha hfit hdom hloc
          c hc hcLen tz.2.1 tz.2.2).mapsTo tz.1.property⟩
  let base : unitInterval × Core → M :=
    fun tz => rawLoopPath (I := I) g p c (tz.2.1 : E)
      (hdom tz.2.1 tz.2.1.property) tz.1
  have hrad :
      Continuous
        (fun zt : Core × unitInterval =>
          rawFlatPath (I := I) g p (zt.1.1 : E)
            (hdom zt.1.1 zt.1.1.property) zt.2) := by
    change Continuous
      (fun zt : Core × unitInterval =>
        framedExpMap (I := I) g p
          (rawFlatRay (zt.1.1 : E) zt.2))
    have ht : Continuous
        (fun zt : Core × unitInterval =>
          Real.smoothTransition (3 * (zt.2 : Real) - 1)) :=
      Real.smoothTransition.continuous.comp
        ((continuous_const.mul
          (continuous_subtype_val.comp continuous_snd)).sub continuous_const)
    have hz : Continuous
        (fun zt : Core × unitInterval => (zt.1.1 : E)) :=
      continuous_subtype_val.comp
        (continuous_subtype_val.comp continuous_fst)
    have harg : Continuous
        (fun zt : Core × unitInterval =>
          rawFlatRay (zt.1.1 : E) zt.2) := by
      simpa only [rawFlatRay] using ht.smul hz
    exact hloc.contMDiffOn.continuousOn.comp_continuous harg fun zt =>
      rawFlatRay_mem
        (((mem_rawCore (E := E) zt.1.1).mp zt.1.2).trans_lt haR) zt.2
  have hloop : Continuous (fun zt : Core × unitInterval => c zt.2) := by
    fun_prop
  have hfamily :
      Continuous
        (fun zt : Core × unitInterval =>
          rawLoopPath (I := I) g p c (zt.1.1 : E)
            (hdom zt.1.1 zt.1.1.property) zt.2) := by
    simpa only [rawLoopPath, HasUncurry.uncurry] using
      Path.trans_continuous_family
        (fun _ : Core => c) hloop
        (fun z : Core => rawFlatPath (I := I) g p (z.1 : E)
          (hdom z.1 z.1.property)) hrad
  have hbase : Continuous base := by
    have hswap : Continuous
        (fun tz : unitInterval × Core => (tz.2, tz.1)) := by
      fun_prop
    simpa only [base] using hfamily.comp hswap
  let f : C(unitInterval × Core, M) := ⟨base, hbase⟩
  have hlifts : fU ∘ lift = f := by
    funext tz
    have hspec := rawLoopLift_spec (I := I) g hEnorm p hL ha hfit
      hdom hloc c hc hcLen tz.2.1 tz.2.2
    have hP := hspec.2.2 tz.1 tz.1.property
    rw [Path.extend_apply _ tz.1.property] at hP
    exact hP.2
  have hstart : Continuous (fun z : Core => lift (0, z)) := by
    let zeroU : Uo := ⟨0, Metric.mem_ball_self hR⟩
    have hzero : (fun z : Core => lift (0, z)) = fun _ : Core => zeroU := by
      funext z
      apply Subtype.ext
      exact (rawLoopLift_spec (I := I) g hEnorm p hL ha hfit
        hdom hloc c hc hcLen z.1 z.2).2.1
    rw [hzero]
    exact continuous_const
  have hpaths :
      ∀ z : Core, Continuous (fun t : unitInterval => lift (t, z)) := by
    intro z
    have hspec := rawLoopLift_spec (I := I) g hEnorm p hL ha hfit
      hdom hloc c hc hcLen z.1 z.2
    exact
      (continuousOn_iff_continuous_restrict.mp
        hspec.continuousOn).codRestrict
          (fun t => hspec.mapsTo t.property)
  have hjoint : Continuous lift :=
    hlocU.isLocalHomeomorph.continuous_lift
      (T2Space.isSeparatedMap fU) f hlifts hstart hpaths
  have hend : Continuous (fun z : Core => lift (1, z)) :=
    hjoint.comp (continuous_const.prodMk continuous_id)
  apply hend.congr
  intro z
  rfl

/-- Raw loop transport preserves C1 regularity and exact pullback path length
for curves in the raw core. -/
theorem rawTransport_curve
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) {R L a : Real} (hL : 0 ≤ L) (ha : 0 ≤ a)
    (hfit : L + a < R)
    (hdom : ∀ z ∈ Metric.ball (0 : E) R, ∀ u ∈ Set.Icc (0 : Real) 1,
      (show TangentSpace I p from
        u • normalFrame (I := I) g p z) ∈ expDomain (I := I) g p)
    (hloc : IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
      (framedExpMap (I := I) g p) (Metric.ball (0 : E) R))
    (c : Path p p) (hc : IsFlatC1Path (I := I) c)
    (hcLen : pathLen (I := I) c < ENNReal.ofReal L)
    {γ : Real → rawPullBall (E := E) R} {s t : Real}
    (hγ : ContMDiffOn 𝓘(Real, Real) 𝓘(Real, E) 1 γ (Set.Icc s t))
    (hγcore : ∀ u : Real, γ u ∈ rawCore (E := E) R a) :
    letI : RiemannianBundle
        (fun z : rawPullBall (E := E) R ↦
          TangentSpace 𝓘(Real, E) z) :=
      ⟨(rawPullMetric (I := I) g p hloc).toRiemannianMetric⟩
    let η : Real → rawPullBall (E := E) R :=
      fun u => rawTransport (I := I) g hEnorm p hL ha hfit hdom hloc
        c hc hcLen (γ u) (hγcore u)
    ContMDiffOn 𝓘(Real, Real) 𝓘(Real, E) 1 η (Set.Icc s t) ∧
      Manifold.pathELength 𝓘(Real, E) η s t =
        Manifold.pathELength 𝓘(Real, E) γ s t := by
  let gPull := rawPullMetric (I := I) g p hloc
  letI : RiemannianBundle
      (fun z : rawPullBall (E := E) R ↦ TangentSpace 𝓘(Real, E) z) :=
    ⟨gPull.toRiemannianMetric⟩
  letI pullNormedAdd (z : rawPullBall (E := E) R) :
      NormedAddCommGroup (TangentSpace 𝓘(Real, E) z) := inferInstance
  letI pullNormed (z : rawPullBall (E := E) R) :
      NormedSpace Real (TangentSpace 𝓘(Real, E) z) := inferInstance
  letI pullENormSmul : ∀ z : rawPullBall (E := E) R,
      ENormSMulClass Real (TangentSpace 𝓘(Real, E) z) :=
    fun _ => inferInstance
  let Core :=
    {z : rawPullBall (E := E) R // z ∈ rawCore (E := E) R a}
  let η : Real → rawPullBall (E := E) R :=
    fun u => rawTransport (I := I) g hEnorm p hL ha hfit hdom hloc
      c hc hcLen (γ u) (hγcore u)
  let ηE : Real → E := fun u => (η u : E)
  let γE : Real → E := fun u => (γ u : E)
  let F : E → M := framedExpMap (I := I) g p
  let β : Real → M := F ∘ γE
  have hγCore : ContinuousOn
      (fun u => (⟨γ u, hγcore u⟩ : Core)) (Set.Icc s t) :=
    Topology.IsInducing.subtypeVal.continuousOn_iff.mpr (by
      simpa only [Function.comp_apply] using hγ.continuousOn)
  have hT : Continuous
      (fun z : Core =>
        (rawTransport (I := I) g hEnorm p hL ha hfit hdom hloc
          c hc hcLen z.1 z.2 : E)) :=
    continuous_subtype_val.comp
      (rawTransport_cont (I := I) g hEnorm p hL ha hfit hdom hloc
        c hc hcLen)
  have hηcont : ContinuousOn ηE (Set.Icc s t) := by
    simpa only [ηE, η] using hT.comp_continuousOn' hγCore
  have hγE : ContMDiffOn 𝓘(Real, Real) 𝓘(Real, E) 1 γE
      (Set.Icc s t) :=
    ((contMDiff_subtype_val (n := (⊤ : WithTop ℕ∞))
      (I := 𝓘(Real, E)) (U := rawPullBall (E := E) R)).of_le
        (show (1 : WithTop ℕ∞) ≤ (⊤ : WithTop ℕ∞) from le_top)
      ).comp_contMDiffOn hγ
  have hβ : ContMDiffOn 𝓘(Real, Real) I 1 β (Set.Icc s t) := by
    exact (hloc.contMDiffOn.of_le (by norm_num)).comp hγE fun u hu =>
      (γ u).property
  have hηLift :
      IsLiftOn F β (Metric.ball (0 : E) R) (ηE s) s t ηE := by
    refine ⟨hηcont, rfl, ?_⟩
    intro u hu
    refine ⟨(η u).property, ?_⟩
    exact rawTransport_exp (I := I) g hEnorm p hL ha hfit hdom hloc
      c hc hcLen (γ u) (hγcore u)
  have hηEcd : ContDiffOn Real 1 ηE (Set.Icc s t) :=
    hηLift.contDiffOn hloc hβ
  have hηEm : ContMDiffOn 𝓘(Real, Real) 𝓘(Real, E) 1 ηE
      (Set.Icc s t) := hηEcd.contMDiffOn
  have hη : ContMDiffOn 𝓘(Real, Real) 𝓘(Real, E) 1 η
      (Set.Icc s t) := by
    intro u hu
    have hamb := hηEm u hu
    rw [contMDiffWithinAt_iff] at hamb ⊢
    obtain ⟨hcont, hdiff⟩ := hamb
    refine ⟨Topology.IsInducing.subtypeVal.continuousWithinAt_iff.mpr ?_, ?_⟩
    · simpa only [ηE, η, Function.comp_apply] using hcont
    · convert hdiff using 2
  have hηlen := rawPull_pathLen (I := I) g hEnorm p hloc hη
  have hγlen := rawPull_pathLen (I := I) g hEnorm p hloc hγ
  have hproj : Set.EqOn
      (rawExpOn (I := I) g p R ∘ η)
      (rawExpOn (I := I) g p R ∘ γ) (Set.Icc s t) := by
    intro u hu
    exact rawTransport_exp (I := I) g hEnorm p hL ha hfit hdom hloc
      c hc hcLen (γ u) (hγcore u)
  refine ⟨hη, ?_⟩
  calc
    Manifold.pathELength 𝓘(Real, E) η s t =
        Manifold.pathELength I
          (rawExpOn (I := I) g p R ∘ η) s t := hηlen.symm
    _ = Manifold.pathELength I
        (rawExpOn (I := I) g p R ∘ γ) s t :=
      Manifold.pathELength_congr hproj
    _ = Manifold.pathELength 𝓘(Real, E) γ s t := hγlen

/-- Raw loop transport preserves exact pullback path length. -/
theorem rawTransport_len
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) {R L a : Real} (hL : 0 ≤ L) (ha : 0 ≤ a)
    (hfit : L + a < R)
    (hdom : ∀ z ∈ Metric.ball (0 : E) R, ∀ u ∈ Set.Icc (0 : Real) 1,
      (show TangentSpace I p from
        u • normalFrame (I := I) g p z) ∈ expDomain (I := I) g p)
    (hloc : IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
      (framedExpMap (I := I) g p) (Metric.ball (0 : E) R))
    (c : Path p p) (hc : IsFlatC1Path (I := I) c)
    (hcLen : pathLen (I := I) c < ENNReal.ofReal L)
    {γ : Real → rawPullBall (E := E) R} {s t : Real}
    (hγ : ContMDiffOn 𝓘(Real, Real) 𝓘(Real, E) 1 γ (Set.Icc s t))
    (hγcore : ∀ u : Real, γ u ∈ rawCore (E := E) R a) :
    letI : RiemannianBundle
        (fun z : rawPullBall (E := E) R ↦
          TangentSpace 𝓘(Real, E) z) :=
      ⟨(rawPullMetric (I := I) g p hloc).toRiemannianMetric⟩
    Manifold.pathELength 𝓘(Real, E)
        (fun u => rawTransport (I := I) g hEnorm p hL ha hfit hdom hloc
          c hc hcLen (γ u) (hγcore u)) s t =
      Manifold.pathELength 𝓘(Real, E) γ s t :=
  (rawTransport_curve (I := I) g hEnorm p hL ha hfit hdom hloc
    c hc hcLen hγ hγcore).2

end

end CGT
end Riemannian
end Geometry
end DifferentialGeometry
