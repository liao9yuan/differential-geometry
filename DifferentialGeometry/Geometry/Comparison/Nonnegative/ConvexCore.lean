import DifferentialGeometry.Geometry.Comparison.Nonnegative.ConvexExhaustion
import Mathlib.Topology.Order.Compact

open Set Bundle Manifold
open scoped ContDiff ENNReal Manifold Topology

namespace DifferentialGeometry
namespace RiemannianMetricComplete

open Geometry.Riemannian Geometry.Riemannian.Exponential

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [T2Space (TangentBundle I M)]
  [SigmaCompactSpace M] [ConnectedSpace M]

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace

noncomputable def rayMinLevel
    (g : SmoothRiemannianMetric I M) (p : M) : ℝ :=
  sInf {c : ℝ |
    (Geometry.Riemannian.rayBusemannSublevel (I := I) g p c).Nonempty}

noncomputable def rayMinCore
    (g : SmoothRiemannianMetric I M) (p : M) : Set M :=
  Geometry.Riemannian.rayBusemannSublevel (I := I) g p
    (rayMinLevel (I := I) g p)

theorem rayMinLevel_spec
    {g : SmoothRiemannianMetric I M}
    (hg : RiemannianMetricComplete (I := I) g) [NoncompactSpace M]
    (p : M) (hsec : Integral.Connection.NonnegSecMetric (I := I) (M := M) g) :
    (Geometry.Riemannian.rayBusemannSublevel (I := I) g p
      (rayMinLevel (I := I) g p)).Nonempty ∧
    ∀ ⦃c : ℝ⦄,
      (Geometry.Riemannian.rayBusemannSublevel (I := I) g p c).Nonempty →
        rayMinLevel (I := I) g p ≤ c := by
  classical
  letI : IsManifold I 1 M :=
    IsManifold.of_le (I := I) (M := M) (n := (∞ : WithTop ℕ∞))
      (by decide : (1 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞))
  letI : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I M
  letI : T3Space M := inferInstance
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
    ⟨g.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle E
      (fun x : M ↦ TangentSpace I x) :=
    ⟨⟨g.inner, g.contMDiff.continuous, by intro x v w; rfl⟩⟩
  letI : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
  letI : CompleteSpace M := by simpa only using hg.complete
  let hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)) :=
    fun x v ↦ tensor0SBundle_enorm_eq_riemannianBundle_enorm
      (I := I) g x v
  let C : ℝ → Set M :=
    fun c ↦ Geometry.Riemannian.rayBusemannSublevel (I := I) g p c
  have hC0ne : (C 0).Nonempty := by
    refine ⟨p, ?_⟩
    simpa only [C] using
      Geometry.Riemannian.rayBusemannSublevel.base_mem (I := I) g p le_rfl
  have hC0compact : IsCompact (C 0) := by
    simpa only [C] using
      ray_compact_nonneg (I := I) hg p (c := 0) hsec
  have hnoncompact : ¬ IsCompact (Set.univ : Set M) := by
    intro hcompact
    exact hcompact.ne_univ rfl
  obtain ⟨u, _, hγ, _⟩ := exists_minRay_in
    (I := I) hg (C := Set.univ) isClosed_univ IsTotallyConvex.univ
      p (Set.mem_univ p) hnoncompact
  let γ : ℝ → M := intrinsicGeodesic (I := I) g hEnorm p u
  have hγ' : IsMinGeodesicRay (I := I) g γ := by
    simpa only [γ] using hγ
  have hγ0 : γ 0 = p := by
    simpa only [γ] using intrinsicGeodesic_zero (I := I) g hEnorm p u
  let f : M → ℝ := fun x ↦ -busemannOf (I := I) g γ x
  have hfcont : Continuous f := by
    exact (busemannOf.continuous hγ'.minRay).neg
  obtain ⟨x₀, _, hxmin⟩ :=
    hC0compact.exists_isMinOn hC0ne hfcont.continuousOn
  have hp0 : p ∈ C 0 := by
    simpa only [C] using
      Geometry.Riemannian.rayBusemannSublevel.base_mem (I := I) g p le_rfl
  have hfp : f p = 0 := by
    rw [← hγ0]
    simp only [f, busemannOf.zero hγ'.minRay, neg_zero]
  have hmin0 : f x₀ ≤ 0 := (hxmin hp0).trans_eq hfp
  let A : Set ℝ := {c | (C c).Nonempty}
  have hAne : A.Nonempty := by
    exact ⟨0, hC0ne⟩
  have hAbdd : BddBelow A := by
    refine ⟨f x₀, ?_⟩
    intro c hc
    change (C c).Nonempty at hc
    obtain ⟨x, hx⟩ := hc
    by_cases hc0 : 0 ≤ c
    · exact hmin0.trans hc0
    · have hxc : x ∈
          Geometry.Riemannian.rayBusemannSublevel (I := I) g p c := by
        simpa only [C] using hx
      have hxc0 : x ∈ C 0 := by
        have hsub := Geometry.Riemannian.rayBusemannSublevel.mono
          (I := I) (g := g) (p := p) (lt_of_not_ge hc0).le
        simpa only [C] using hsub hxc
      have hxγ :=
        (Geometry.Riemannian.rayBusemannSublevel.mem (I := I)).mp hxc
          γ hγ' hγ0
      change f x ≤ c at hxγ
      exact (hxmin hxc0).trans hxγ
  haveI : Nonempty A := hAne.to_subtype
  have hdir : Directed (· ⊇ ·) (fun c : A ↦ C c.1) := by
    intro c d
    rcases le_total c.1 d.1 with hcd | hdc
    · refine ⟨c, Set.Subset.rfl, ?_⟩
      simpa only [C] using
        Geometry.Riemannian.rayBusemannSublevel.mono
          (I := I) (g := g) (p := p) hcd
    · refine ⟨d, ?_, Set.Subset.rfl⟩
      simpa only [C] using
        Geometry.Riemannian.rayBusemannSublevel.mono
          (I := I) (g := g) (p := p) hdc
  have hinter : (⋂ c : A, C c.1).Nonempty :=
    IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
      (fun c : A ↦ C c.1) hdir (fun c ↦ c.2)
      (fun c ↦ by
        simpa only [C] using
          ray_compact_nonneg (I := I) hg p (c := c.1) hsec)
      (fun c ↦ by
        simpa only [C] using
          Geometry.Riemannian.rayBusemannSublevel.isClosed
            (I := I) g p c.1)
  obtain ⟨x, hx⟩ := hinter
  have hxall : ∀ c : A, x ∈ C c.1 := Set.mem_iInter.mp hx
  have hxa : x ∈ C (sInf A) := by
    have hxraw : x ∈ Geometry.Riemannian.rayBusemannSublevel
        (I := I) g p (sInf A) := by
      rw [Geometry.Riemannian.rayBusemannSublevel.mem]
      intro δ hδ hδ0
      change -busemannOf (I := I) g δ x ≤ sInf A
      apply le_csInf hAne
      intro c hc
      have hxc : x ∈
          Geometry.Riemannian.rayBusemannSublevel (I := I) g p c := by
        simpa only [C] using hxall ⟨c, hc⟩
      have hxδ := (Geometry.Riemannian.rayBusemannSublevel.mem (I := I)).mp
        hxc δ hδ hδ0
      change -busemannOf (I := I) g δ x ≤ c at hxδ
      exact hxδ
    simpa only [C] using hxraw
  refine ⟨?_, ?_⟩
  · simpa only [rayMinLevel, A, C] using (show (C (sInf A)).Nonempty from ⟨x, hxa⟩)
  · intro c hc
    have hcA : c ∈ A := by
      simpa only [A, C] using hc
    simpa only [rayMinLevel, A, C] using csInf_le hAbdd hcA

theorem exists_ray_min_level
    {g : SmoothRiemannianMetric I M}
    (hg : RiemannianMetricComplete (I := I) g) [NoncompactSpace M]
    (p : M) (hsec : Integral.Connection.NonnegSecMetric (I := I) (M := M) g) :
    ∃ a : ℝ,
      (Geometry.Riemannian.rayBusemannSublevel (I := I) g p a).Nonempty ∧
      ∀ ⦃c : ℝ⦄,
        (Geometry.Riemannian.rayBusemannSublevel (I := I) g p c).Nonempty →
          a ≤ c := by
  exact ⟨rayMinLevel (I := I) g p,
    rayMinLevel_spec (I := I) hg p hsec⟩

theorem rayMinCore_spec
    {g : SmoothRiemannianMetric I M}
    (hg : RiemannianMetricComplete (I := I) g) [NoncompactSpace M]
    (p : M) (hsec : Integral.Connection.NonnegSecMetric (I := I) (M := M) g) :
    (rayMinCore (I := I) g p).Nonempty ∧
      IsCompact (rayMinCore (I := I) g p) ∧
      IsTotallyConvex (I := I) g (rayMinCore (I := I) g p) := by
  refine ⟨?_, ?_, ?_⟩
  · simpa only [rayMinCore] using
      (rayMinLevel_spec (I := I) hg p hsec).1
  · simpa only [rayMinCore] using
      ray_compact_nonneg (I := I) hg p
        (c := rayMinLevel (I := I) g p) hsec
  · simpa only [rayMinCore] using
      ray_convex_of_nonneg (I := I) hg p
        (c := rayMinLevel (I := I) g p) hsec

end RiemannianMetricComplete
end DifferentialGeometry
