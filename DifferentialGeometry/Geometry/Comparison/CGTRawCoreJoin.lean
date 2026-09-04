import DifferentialGeometry.Geometry.Comparison.CGTRawExtJoin

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
  [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace

section CoreJoin

variable [I.Boundaryless] [T2Space (TangentBundle I M)]
variable [RiemannianBundle (fun x : M => TangentSpace I x)]
variable [PseudoEMetricSpace M] [IsRiemannianManifold I M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

/-- Core endpoints admit a raw-pullback geodesic whose model-space inclusion is
the fenced complete-extension minimizing join. -/
theorem exists_raw_fenced
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) {R a : Real} (hR : 0 < R) (h4aR : 4 * a < R)
    (hloc : IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
      (framedExpMap (I := I) g p) (Metric.ball (0 : E) R))
    (hdom : ∀ w : rawPullBall (E := E) R,
      ∀ s ∈ Set.Icc (0 : Real) 1,
        (show TangentSpace I p from
          s • normalFrame (I := I) g p (w : E)) ∈ expDomain (I := I) g p)
    {x y : rawPullBall (E := E) R}
    (hx : x ∈ rawCore (E := E) R a)
    (hy : y ∈ rawCore (E := E) R a) :
    ∃ γU : Real → rawPullBall (E := E) R,
      ContMDiff 𝓘(Real, Real) 𝓘(Real, E) ∞ γU ∧
      IsGeodesicOn (I := 𝓘(Real, E))
        (rawPullMetric (I := I) g p hloc)
        γU (Set.Icc (0 : Real) 1) ∧
      γU 0 = x ∧ γU 1 = y ∧
      (∀ t ∈ Set.Icc (0 : Real) 1,
        ‖((γU t : rawPullBall (E := E) R) : E)‖ < 3 * R / 4) ∧
      Set.EqOn
        (fun t => ((γU t : rawPullBall (E := E) R) : E))
        (rawExtJoin (I := I) g p hR hloc (x : E) (y : E))
        (Set.Icc (0 : Real) 1) := by
  classical
  let γ : Real → E :=
    rawExtJoin (I := I) g p hR hloc (x : E) (y : E)
  have hx' : ‖(x : E)‖ ≤ a :=
    (mem_rawCore (E := E) x).mp hx
  have hy' : ‖(y : E)‖ ≤ a :=
    (mem_rawCore (E := E) y).mp hy
  have hγinf : ContMDiff 𝓘(Real, Real) 𝓘(Real, E) ∞ γ := by
    simpa only [γ] using
      rawExtJoin_smooth (I := I) g p hR hloc (x : E) (y : E)
  have hγgeo :
      IsGeodesic (I := 𝓘(Real, E))
        (rawExtMetric (I := I) g p hR hloc) γ := by
    simpa only [γ] using
      rawExtJoin_geo (I := I) g p hR hloc (x : E) (y : E)
  have hγfence : ∀ t ∈ Set.Icc (0 : Real) 1,
      ‖γ t‖ < 3 * R / 4 := by
    simpa only [γ] using
      rawExtJoin_fenced (I := I) g hEnorm p hR h4aR hloc hdom hx' hy'
  have hγ0_ball : γ 0 ∈ Metric.ball (0 : E) R := by
    simpa only [γ, rawExtJoin_zero] using x.property
  have hγ1_ball : γ 1 ∈ Metric.ball (0 : E) R := by
    simpa only [γ, rawExtJoin_one] using y.property
  have hpre0 : γ ⁻¹' Metric.ball (0 : E) R ∈ 𝓝 (0 : Real) :=
    hγinf.continuous.continuousAt.preimage_mem_nhds
      (Metric.isOpen_ball.mem_nhds hγ0_ball)
  have hpre1 : γ ⁻¹' Metric.ball (0 : E) R ∈ 𝓝 (1 : Real) :=
    hγinf.continuous.continuousAt.preimage_mem_nhds
      (Metric.isOpen_ball.mem_nhds hγ1_ball)
  obtain ⟨ε0, hε0, hε0sub⟩ := Metric.mem_nhds_iff.mp hpre0
  obtain ⟨ε1, hε1, hε1sub⟩ := Metric.mem_nhds_iff.mp hpre1
  let ε : Real := min ε0 ε1
  have hε : 0 < ε := by
    simpa only [ε] using lt_min hε0 hε1
  have hε_le0 : ε ≤ ε0 := min_le_left ε0 ε1
  have hε_le1 : ε ≤ ε1 := min_le_right ε0 ε1
  have hstayExt : ∀ t ∈ Set.Icc (-ε / 2) (1 + ε / 2),
      γ t ∈ Metric.ball (0 : E) R := by
    intro t ht
    by_cases ht0 : t < 0
    · apply hε0sub
      rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_neg ht0]
      have hhalf : ε / 2 < ε0 := by
        linarith [hε, hε_le0]
      linarith [ht.1, hhalf]
    · have ht0' : 0 ≤ t := le_of_not_gt ht0
      by_cases ht1 : t ≤ 1
      · rw [Metric.mem_ball, dist_zero_right]
        exact (hγfence t ⟨ht0', ht1⟩).trans (by linarith)
      · have ht1' : 1 < t := lt_of_not_ge ht1
        apply hε1sub
        rw [Metric.mem_ball, Real.dist_eq, abs_of_pos (sub_pos.mpr ht1')]
        have hhalf : ε / 2 < ε1 := by
          linarith [hε, hε_le1]
        linarith [ht.2, hhalf]
  let c : Real := 1 / 2
  let lam : Real := 1 / 2 + ε / 2
  let clipLeft : Real := -1 / 2 - ε / 4
  let clipRight : Real := 1 / 2 + ε / 4
  have hlam : 0 < lam := by
    dsimp only [lam]
    linarith
  have hclipLeft : -lam < clipLeft := by
    dsimp only [lam, clipLeft]
    linarith
  have hclipRight : clipRight < lam := by
    dsimp only [lam, clipRight]
    linarith
  obtain ⟨σ, hσinf, hσid, hσrange⟩ :=
    DifferentialGeometry.Geometry.Riemannian.exists_time_window_clip
      hlam hclipLeft hclipRight
  let τ : Real → Real := fun t => c + σ (t - c)
  have hτinf : ContDiff Real (∞ : WithTop ℕ∞) τ := by
    dsimp only [τ]
    exact contDiff_const.add
      (hσinf.comp (contDiff_id.sub contDiff_const))
  have hτrange : ∀ t, τ t ∈ Set.Icc (-ε / 2) (1 + ε / 2) := by
    intro t
    have hσbounds := abs_le.mp (hσrange (t - c))
    dsimp only [τ, c, lam] at hσbounds ⊢
    constructor <;> linarith
  have hτid :
      Set.EqOn τ id (Set.Icc (-ε / 4) (1 + ε / 4)) := by
    intro t ht
    have htClip : t - c ∈ Set.Icc clipLeft clipRight := by
      dsimp only [c, clipLeft, clipRight]
      constructor <;> linarith [ht.1, ht.2]
    have hσ := hσid htClip
    change σ (t - c) = t - c at hσ
    dsimp only [τ]
    rw [hσ]
    dsimp only [c, id]
    ring
  let γU : Real → rawPullBall (E := E) R := fun t =>
    ⟨γ (τ t), hstayExt (τ t) (hτrange t)⟩
  have hγUinf :
      ContMDiff 𝓘(Real, Real) 𝓘(Real, E) ∞ γU := by
    have hcomp :
        ContMDiff 𝓘(Real, Real) 𝓘(Real, E) ∞ (fun t => γ (τ t)) := by
      apply hγinf.comp
      rw [contMDiff_iff_contDiff]
      exact hτinf
    intro t
    exact codRestr_contMDiffAt
      (V := rawPullBall (E := E) R)
      (fun s => hstayExt (τ s) (hτrange s)) (hcomp t)
  have hEqLarge :
      Set.EqOn
        (fun t => ((γU t : rawPullBall (E := E) R) : E)) γ
        (Set.Icc (-ε / 4) (1 + ε / 4)) := by
    intro t ht
    change γ (τ t) = γ t
    rw [hτid ht]
    rfl
  have hEq :
      Set.EqOn
        (fun t => ((γU t : rawPullBall (E := E) R) : E)) γ
        (Set.Icc (0 : Real) 1) := by
    intro t ht
    exact hEqLarge ⟨by linarith [ht.1, hε], by linarith [ht.2, hε]⟩
  have hγUgeoExt :
      IsGeodesicOn (I := 𝓘(Real, E))
        (rawExtMetric (I := I) g p hR hloc)
        (fun t => ((γU t : rawPullBall (E := E) R) : E))
        (Set.Icc (0 : Real) 1) := by
    intro t ht
    have hlarge_nhds :
        Set.Icc (-ε / 4) (1 + ε / 4) ∈ 𝓝 t :=
      Icc_mem_nhds (by linarith [ht.1, hε])
        (by linarith [ht.2, hε])
    have heq :
        (fun s => ((γU s : rawPullBall (E := E) R) : E)) =ᶠ[𝓝 t] γ :=
      hEqLarge.eventuallyEq_of_mem hlarge_nhds
    exact Geodesic.HasGeodesicEquationAt.congr_of_eventuallyEq_at
      heq.eq_of_nhds heq (hγgeo t)
  have hγUfence : ∀ t ∈ Set.Icc (0 : Real) 1,
      ‖((γU t : rawPullBall (E := E) R) : E)‖ < 3 * R / 4 := by
    intro t ht
    calc
      ‖((γU t : rawPullBall (E := E) R) : E)‖ = ‖γ t‖ :=
        congrArg norm (hEq ht)
      _ < 3 * R / 4 := hγfence t ht
  have hγUgeo :
      IsGeodesicOn (I := 𝓘(Real, E))
        (rawPullMetric (I := I) g p hloc)
        γU (Set.Icc (0 : Real) 1) :=
    rawPull_geo_of_ext (I := I) g p hR hloc γU
      (Set.Icc (0 : Real) 1) hγUinf hγUfence hγUgeoExt
  refine ⟨γU, hγUinf, hγUgeo, ?_, ?_, hγUfence, ?_⟩
  · apply Subtype.ext
    simpa only [γ, rawExtJoin_zero] using
      hEq (x := (0 : Real)) (by norm_num)
  · apply Subtype.ext
    simpa only [γ, rawExtJoin_one] using
      hEq (x := (1 : Real)) (by norm_num)
  · simpa only [γ] using hEq

/-- Under a strict extension-distance budget, core endpoints have identical
raw-pullback and complete-extension distances. -/
theorem rawPull_edist_eq
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) {R a L : Real} (hR : 0 < R) (h4aR : 4 * a < R)
    (hloc : IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
      (framedExpMap (I := I) g p) (Metric.ball (0 : E) R))
    (hdom : ∀ w : rawPullBall (E := E) R,
      ∀ s ∈ Set.Icc (0 : Real) 1,
        (show TangentSpace I p from
          s • normalFrame (I := I) g p (w : E)) ∈ expDomain (I := I) g p)
    {x y : rawPullBall (E := E) R}
    (hx : x ∈ rawCore (E := E) R a)
    (hy : y ∈ rawCore (E := E) R a)
    (hd : riemannianEDistOf (I := 𝓘(Real, E))
      (rawExtMetric (I := I) g p hR hloc) (x : E) (y : E) <
        ENNReal.ofReal L)
    (hbudget : a + L < 3 * R / 4) :
    riemannianEDistOf (I := 𝓘(Real, E))
        (rawPullMetric (I := I) g p hloc) x y =
      riemannianEDistOf (I := 𝓘(Real, E))
        (rawExtMetric (I := I) g p hR hloc) (x : E) (y : E) := by
  classical
  by_cases hdim : Module.finrank Real E = 0
  · letI : Subsingleton E := Module.finrank_zero_iff.mp hdim
    have hxy : x = y := Subtype.ext (Subsingleton.elim (x : E) (y : E))
    subst y
    simp only [riemannianEDistOf_self]
  · letI : NeZero (Module.finrank Real E) := ⟨hdim⟩
    let gExt := rawExtMetric (I := I) g p hR hloc
    let gPull := rawPullMetric (I := I) g p hloc
    letI : RiemannianBundle
        (fun z : E => TangentSpace 𝓘(Real, E) z) :=
      ⟨gExt.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E
        (fun z : E => TangentSpace 𝓘(Real, E) z) :=
      ⟨gExt.inner, gExt.contMDiff.continuous, by intro z v w; rfl⟩
    letI : PseudoEMetricSpace E :=
      PseudoEMetricSpace.ofRiemannianMetric 𝓘(Real, E) E
    letI : IsRiemannianManifold 𝓘(Real, E) E := ⟨fun _ _ => rfl⟩
    letI : UniformSpace E := PseudoEMetricSpace.toUniformSpace
    letI : CompleteSpace E :=
      (rawExt_complete (I := I) g p hR hloc).complete
    let hExt : ∀ (z : E) (v : TangentSpace 𝓘(Real, E) z),
        ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (gExt.inner z v v)) :=
      fun z v =>
        tensor0SBundle_enorm_eq_riemannianBundle_enorm
          (I := 𝓘(Real, E)) gExt z v
    letI : SigmaCompactSpace (rawPullBall (E := E) R) :=
      isSigmaCompact_iff_sigmaCompactSpace.mp
        (Geometry.isSigmaCompact_of_isOpen
          𝓘(Real, E) (rawPullBall (E := E) R).isOpen)
    letI : RiemannianBundle
        (fun z : rawPullBall (E := E) R =>
          TangentSpace 𝓘(Real, E) z) :=
      ⟨gPull.toRiemannianMetric⟩
    letI (z : rawPullBall (E := E) R) :
        NormedAddCommGroup (TangentSpace 𝓘(Real, E) z) :=
      inferInstance
    letI (z : rawPullBall (E := E) R) :
        NormedSpace Real (TangentSpace 𝓘(Real, E) z) :=
      inferInstance
    letI : ∀ z : rawPullBall (E := E) R,
        ENormSMulClass Real (TangentSpace 𝓘(Real, E) z) :=
      fun _ => inferInstance
    letI : IsContinuousRiemannianBundle E
        (fun z : rawPullBall (E := E) R =>
          TangentSpace 𝓘(Real, E) z) :=
      ⟨gPull.inner, gPull.contMDiff.continuous, by intro z v w; rfl⟩
    letI : PseudoEMetricSpace (rawPullBall (E := E) R) :=
      PseudoEMetricSpace.ofRiemannianMetric 𝓘(Real, E)
        (rawPullBall (E := E) R)
    letI : IsRiemannianManifold 𝓘(Real, E)
        (rawPullBall (E := E) R) :=
      ⟨fun _ _ => rfl⟩
    change
      Manifold.riemannianEDist 𝓘(Real, E) x y =
        Manifold.riemannianEDist 𝓘(Real, E) (x : E) (y : E)
    have hx' : ‖(x : E)‖ ≤ a :=
      (mem_rawCore (E := E) x).mp hx
    have ha : 0 ≤ a := (norm_nonneg (x : E)).trans hx'
    have hExtLt :
        Manifold.riemannianEDist 𝓘(Real, E) (x : E) (y : E) <
          ENNReal.ofReal L := by
      simpa only [gExt, riemannianEDistOf] using hd
    have hLPos : 0 < L :=
      ENNReal.ofReal_pos.mp (lt_of_le_of_lt bot_le hExtLt)
    have hExtBound :
        Manifold.riemannianEDist 𝓘(Real, E) (x : E) (y : E) ≤
          ENNReal.ofReal L := hExtLt.le
    have hExtTop :
        Manifold.riemannianEDist 𝓘(Real, E) (x : E) (y : E) ≠
          (⊤ : ENNReal) :=
      ne_top_of_le_ne_top ENNReal.ofReal_ne_top hExtBound
    have hlen_of_stay :
        ∀ {γ : Real → rawPullBall (E := E) R} {s t : Real},
          ContMDiffOn 𝓘(Real, Real) 𝓘(Real, E) 1 γ (Set.Icc s t) →
          (∀ u ∈ Set.Icc s t,
            ‖((γ u : rawPullBall (E := E) R) : E)‖ ≤ 3 * R / 4) →
          Manifold.pathELength 𝓘(Real, E) γ s t =
            Manifold.pathELength 𝓘(Real, E)
              (fun u => ((γ u : rawPullBall (E := E) R) : E)) s t := by
      intro γ s t hγ hstay
      let η : Real → E := fun u => ((γ u : rawPullBall (E := E) R) : E)
      have hη :
          ContMDiffOn 𝓘(Real, Real) 𝓘(Real, E) 1 η (Set.Icc s t) := by
        exact
          ((contMDiff_subtype_val (n := (⊤ : WithTop ℕ∞))
            (I := 𝓘(Real, E))
            (U := rawPullBall (E := E) R)).of_le
              (show (1 : WithTop ℕ∞) ≤ (⊤ : WithTop ℕ∞) from le_top)
            ).comp_contMDiffOn hγ
      have hpull :
          Manifold.pathELength 𝓘(Real, E) γ s t =
            Manifold.pathELength I
              ((framedExpMap (I := I) g p) ∘ η) s t := by
        simpa only [η, rawExpOn, Function.comp_apply] using
          (rawPull_pathLen (I := I) g hEnorm p hloc hγ).symm
      have hext :
          Manifold.pathELength 𝓘(Real, E) η s t =
            Manifold.pathELength I
              ((framedExpMap (I := I) g p) ∘ η) s t := by
        simpa only [gExt] using
          (rawExt_pathLen (I := I) g hEnorm p hR hloc hη
            (fun u hu => by
              rw [Metric.mem_closedBall, dist_zero_right]
              exact hstay u hu))
      exact hpull.trans hext.symm
    apply le_antisymm
    · obtain ⟨γ, hγinf, _, hγ0, hγ1, hγstay, hγeq⟩ :=
        exists_raw_fenced (I := I) g hEnorm p hR h4aR hloc hdom hx hy
      have hγC1 :
          ContMDiffOn 𝓘(Real, Real) 𝓘(Real, E) 1 γ
            (Set.Icc (0 : Real) 1) :=
        (hγinf.of_le (by decide)).contMDiffOn
      have hpath :=
        Manifold.riemannianEDist_le_pathELength
          (I := 𝓘(Real, E)) (x := x) (y := y)
          hγC1 hγ0 hγ1 zero_le_one
      have hlen :
          Manifold.pathELength 𝓘(Real, E) γ 0 1 =
            Manifold.pathELength 𝓘(Real, E)
              (fun t => ((γ t : rawPullBall (E := E) R) : E)) 0 1 :=
        hlen_of_stay hγC1 (fun t ht => (hγstay t ht).le)
      have hjoin :
          Manifold.pathELength 𝓘(Real, E)
              (rawExtJoin (I := I) g p hR hloc (x : E) (y : E)) 0 1 =
            Manifold.riemannianEDist 𝓘(Real, E) (x : E) (y : E) := by
        calc
          Manifold.pathELength 𝓘(Real, E)
                (rawExtJoin (I := I) g p hR hloc (x : E) (y : E)) 0 1 =
              ENNReal.ofReal
                ((Manifold.riemannianEDist 𝓘(Real, E)
                  (x : E) (y : E)).toReal) := by
            simpa only [rawExtJoin, dif_neg hdim, gExt] using
              (minJoin_pathLen (I := 𝓘(Real, E)) gExt hExt (x : E) (y : E))
          _ = Manifold.riemannianEDist 𝓘(Real, E) (x : E) (y : E) :=
            ENNReal.ofReal_toReal hExtTop
      calc
        Manifold.riemannianEDist 𝓘(Real, E) x y ≤
            Manifold.pathELength 𝓘(Real, E) γ 0 1 := hpath
        _ = Manifold.pathELength 𝓘(Real, E)
            (fun t => ((γ t : rawPullBall (E := E) R) : E)) 0 1 := hlen
        _ = Manifold.pathELength 𝓘(Real, E)
            (rawExtJoin (I := I) g p hR hloc (x : E) (y : E)) 0 1 :=
          Manifold.pathELength_congr hγeq
        _ = Manifold.riemannianEDist 𝓘(Real, E) (x : E) (y : E) := hjoin
    · by_contra hnot
      have hlt :
          Manifold.riemannianEDist 𝓘(Real, E) x y <
            Manifold.riemannianEDist 𝓘(Real, E) (x : E) (y : E) :=
        lt_of_not_ge hnot
      obtain ⟨γ, hγ0, hγ1, hγC1, hγlen⟩ :=
        Manifold.exists_lt_of_riemannianEDist_lt hlt
      have hstay :
          ∀ t ∈ Set.Icc (0 : Real) 1,
            ‖((γ t : rawPullBall (E := E) R) : E)‖ ≤ 3 * R / 4 := by
        intro t ht
        have hγC1pre :
            ContMDiffOn 𝓘(Real, Real) 𝓘(Real, E) 1 γ
              (Set.Icc 0 t) :=
          hγC1.mono (Set.Icc_subset_Icc le_rfl ht.2)
        have hdist_pre :
            Manifold.riemannianEDist 𝓘(Real, E) x (γ t) ≤
              Manifold.pathELength 𝓘(Real, E) γ 0 t :=
          Manifold.riemannianEDist_le_pathELength
            (I := 𝓘(Real, E)) (x := x) (y := γ t)
            hγC1pre hγ0 rfl ht.1
        have hdist_lt :
            Manifold.riemannianEDist 𝓘(Real, E) x (γ t) <
              ENNReal.ofReal L := by
          calc
            Manifold.riemannianEDist 𝓘(Real, E) x (γ t) ≤
                Manifold.pathELength 𝓘(Real, E) γ 0 t := hdist_pre
            _ ≤ Manifold.pathELength 𝓘(Real, E) γ 0 1 :=
              Manifold.pathELength_mono le_rfl ht.2
            _ < Manifold.riemannianEDist 𝓘(Real, E) (x : E) (y : E) :=
              hγlen
            _ ≤ ENNReal.ofReal L := hExtBound
        have hx0 := rawPull_dist_zero (I := I) g hEnorm p hR hloc hdom x
        have hz0 := rawPull_dist_zero (I := I) g hEnorm p hR hloc hdom (γ t)
        have hnormE :
            ENNReal.ofReal ‖((γ t : rawPullBall (E := E) R) : E)‖ <
              ENNReal.ofReal (a + L) := by
          calc
            ENNReal.ofReal ‖((γ t : rawPullBall (E := E) R) : E)‖ =
                Manifold.riemannianEDist 𝓘(Real, E)
                  (rawZero (E := E) hR) (γ t) := by
              change
                ENNReal.ofReal ‖((γ t : rawPullBall (E := E) R) : E)‖ =
                  riemannianEDistOf (I := 𝓘(Real, E)) gPull
                    (rawZero (E := E) hR) (γ t)
              exact hz0.symm
            _ ≤ Manifold.riemannianEDist 𝓘(Real, E)
                  (rawZero (E := E) hR) x +
                Manifold.riemannianEDist 𝓘(Real, E) x (γ t) :=
              Manifold.riemannianEDist_triangle
            _ < ENNReal.ofReal a + ENNReal.ofReal L := by
              have hx0' :
                  Manifold.riemannianEDist 𝓘(Real, E)
                      (rawZero (E := E) hR) x =
                    ENNReal.ofReal ‖(x : E)‖ := by
                change
                  riemannianEDistOf (I := 𝓘(Real, E)) gPull
                      (rawZero (E := E) hR) x =
                    ENNReal.ofReal ‖(x : E)‖
                exact hx0
              rw [hx0']
              exact ENNReal.add_lt_add_of_le_of_lt
                ENNReal.ofReal_ne_top (ENNReal.ofReal_le_ofReal hx') hdist_lt
            _ = ENNReal.ofReal (a + L) := by
              rw [← ENNReal.ofReal_add ha hLPos.le]
        have hnorm :
            ‖((γ t : rawPullBall (E := E) R) : E)‖ < a + L :=
          (ENNReal.ofReal_lt_ofReal_iff
            (add_pos_of_nonneg_of_pos ha hLPos)).mp hnormE
        exact (hnorm.trans hbudget).le
      let η : Real → E := fun t => ((γ t : rawPullBall (E := E) R) : E)
      have hηC1 :
          ContMDiffOn 𝓘(Real, Real) 𝓘(Real, E) 1 η
            (Set.Icc (0 : Real) 1) := by
        exact
          ((contMDiff_subtype_val (n := (⊤ : WithTop ℕ∞))
            (I := 𝓘(Real, E))
            (U := rawPullBall (E := E) R)).of_le
              (show (1 : WithTop ℕ∞) ≤ (⊤ : WithTop ℕ∞) from le_top)
            ).comp_contMDiffOn hγC1
      have hη0 : η 0 = (x : E) := by
        simp only [η, hγ0]
      have hη1 : η 1 = (y : E) := by
        simp only [η, hγ1]
      have hExtPath :
          Manifold.riemannianEDist 𝓘(Real, E) (x : E) (y : E) ≤
            Manifold.pathELength 𝓘(Real, E) η 0 1 :=
        Manifold.riemannianEDist_le_pathELength
          (I := 𝓘(Real, E)) (x := (x : E)) (y := (y : E))
          hηC1 hη0 hη1 zero_le_one
      have hlen :
          Manifold.pathELength 𝓘(Real, E) γ 0 1 =
            Manifold.pathELength 𝓘(Real, E) η 0 1 := by
        simpa only [η] using hlen_of_stay hγC1 hstay
      exact (not_lt_of_ge (hExtPath.trans_eq hlen.symm)) hγlen

/-- On the raw norm core, the pullback distance equals the complete-extension
distance under the whole-ball radial-domain certificate. -/
theorem rawCore_edist_eq
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) {R a : Real} (hR : 0 < R) (h4aR : 4 * a < R)
    (hloc : IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
      (framedExpMap (I := I) g p) (Metric.ball (0 : E) R))
    (hdom : ∀ w : rawPullBall (E := E) R,
      ∀ s ∈ Set.Icc (0 : Real) 1,
        (show TangentSpace I p from
          s • normalFrame (I := I) g p (w : E)) ∈ expDomain (I := I) g p)
    {x y : rawPullBall (E := E) R}
    (hx : x ∈ rawCore (E := E) R a)
    (hy : y ∈ rawCore (E := E) R a) :
    riemannianEDistOf (I := 𝓘(Real, E))
        (rawPullMetric (I := I) g p hloc) x y =
      riemannianEDistOf (I := 𝓘(Real, E))
        (rawExtMetric (I := I) g p hR hloc) (x : E) (y : E) := by
  let L : Real := (a + 3 * R / 4) / 2
  have hx' : ‖(x : E)‖ ≤ a :=
    (mem_rawCore (E := E) x).mp hx
  have hy' : ‖(y : E)‖ ≤ a :=
    (mem_rawCore (E := E) y).mp hy
  have ha : 0 ≤ a := (norm_nonneg (x : E)).trans hx'
  have haInner : a ≤ 3 * R / 4 := by linarith
  have hLPos : 0 < L := by
    dsimp only [L]
    linarith
  have h2aL : 2 * a < L := by
    dsimp only [L]
    linarith
  have hdistLe :
      riemannianEDistOf (I := 𝓘(Real, E))
          (rawExtMetric (I := I) g p hR hloc) (x : E) (y : E) ≤
        ENNReal.ofReal (2 * a) :=
    rawExt_edist_le (I := I) g hEnorm p hR hloc hx' hy' haInner
      (hdom x) (hdom y)
  have hdistLt :
      riemannianEDistOf (I := 𝓘(Real, E))
          (rawExtMetric (I := I) g p hR hloc) (x : E) (y : E) <
        ENNReal.ofReal L :=
    hdistLe.trans_lt ((ENNReal.ofReal_lt_ofReal_iff hLPos).2 h2aL)
  apply rawPull_edist_eq
    (I := I) g hEnorm p hR h4aR hloc hdom hx hy hdistLt
  dsimp only [L]
  linarith

end CoreJoin

end CGT
end Riemannian
end Geometry
end DifferentialGeometry
