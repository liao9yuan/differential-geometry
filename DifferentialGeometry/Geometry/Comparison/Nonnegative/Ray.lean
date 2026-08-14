import DifferentialGeometry.Geometry.Comparison.Nonnegative.Busemann
import DifferentialGeometry.Geometry.Comparison.GeodesicConvexity
import DifferentialGeometry.Geometry.Comparison.HopfRinowProper
import DifferentialGeometry.Geometry.Comparison.Volume.SegmentDomain

noncomputable section

open Set Function Filter Bundle Manifold
open scoped Topology Manifold ContDiff ENNReal

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian

open Exponential VolumeComparison

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [T2Space (TangentBundle I M)]
  [SigmaCompactSpace M] [ConnectedSpace M]
variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace

def IsMinGeodesicRay (g : SmoothRiemannianMetric I M) (γ : ℝ → M) : Prop :=
  IsMinRayOf (I := I) g γ ∧
    Geodesic.IsGeodesicOn (I := I) g γ (Set.Ici 0)

namespace IsMinGeodesicRay

omit [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M]
  [T2Space (TangentBundle I M)] [SigmaCompactSpace M] [ConnectedSpace M] in
theorem minRay {g : SmoothRiemannianMetric I M} {γ : ℝ → M}
    (hγ : IsMinGeodesicRay (I := I) g γ) : IsMinRayOf (I := I) g γ :=
  hγ.1

omit [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M]
  [T2Space (TangentBundle I M)] [SigmaCompactSpace M] [ConnectedSpace M] in
theorem isGeodesicOn {g : SmoothRiemannianMetric I M} {γ : ℝ → M}
    (hγ : IsMinGeodesicRay (I := I) g γ) :
    Geodesic.IsGeodesicOn (I := I) g γ (Set.Ici 0) :=
  hγ.2

end IsMinGeodesicRay

theorem minRay_in_of_escape
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (C : Set M) (hCclosed : IsClosed C)
    (hCconv : IsTotallyConvex (I := I) g C)
    (p : M) (hp : p ∈ C) (q : ℕ → M) (hqC : ∀ n, q n ∈ C)
    (hq : ∀ n : ℕ,
      (n : ℝ) + 1 ≤ (riemannianEDist I p (q n)).toReal) :
    ∃ u : TangentSpace I p, g.inner p u u = 1 ∧
      IsMinRay (I := I) (intrinsicGeodesic (I := I) g hEnorm p u) ∧
      Geodesic.IsGeodesicOn (I := I) g
        (intrinsicGeodesic (I := I) g hEnorm p u) (Set.Ici 0) ∧
      Set.MapsTo (intrinsicGeodesic (I := I) g hEnorm p u) (Set.Ici 0) C := by
  classical
  choose v hvexp hvlen using fun n =>
    hopf_rinow_expMapIntrinsic_surjective_minimizing
      (I := I) g hEnorm p (q n)
  let r : ℕ → ℝ := fun n => (riemannianEDist I p (q n)).toReal
  have hrpos (n : ℕ) : 0 < r n := by
    dsimp [r]
    exact lt_of_lt_of_le (by positivity) (hq n)
  have hvseg (n : ℕ) : v n ∈ SegDom (I := I) g hEnorm p := by
    rw [mem_segDom, hvexp n]
    exact hvlen n
  have hCseg (n : ℕ) :
      Set.MapsTo (intrinsicGeodesic (I := I) g hEnorm p (v n))
        (Set.Icc 0 1) C := by
    apply hCconv (by norm_num)
      ((intrinsicGeodesic_isGeodesic (I := I) g hEnorm p (v n)).isGeodesicOn _)
    · simpa only [intrinsicGeodesic_zero] using hp
    · change expMapIntrinsic (I := I) g hEnorm p (v n) ∈ C
      rw [hvexp n]
      exact hqC n
  let u : ℕ → TangentSpace I p := fun n => (r n)⁻¹ • v n
  have huunit (n : ℕ) : g.inner p (u n) (u n) = 1 := by
    have hv_sq : g.inner p (v n) (v n) = (r n) ^ 2 := by
      calc
        g.inner p (v n) (v n) = Real.sqrt (g.inner p (v n) (v n)) ^ 2 :=
          (Real.sq_sqrt (gInner_self_nonneg (I := I) g p (v n))).symm
        _ = (r n) ^ 2 := by rw [hvlen n]
    change g.inner p ((r n)⁻¹ • v n) ((r n)⁻¹ • v n) = 1
    rw [gInner_smul_self (I := I) g p, hv_sq]
    field_simp [ne_of_gt (hrpos n)]
  obtain ⟨uInf, huInf, φ, hφ, hlim⟩ :=
    (gUnitSphere_isCompact (I := I) g p).tendsto_subseq huunit
  have huInf_eq : g.inner p uInf uInf = 1 := huInf
  have hfar_subseq (t : ℝ) : ∀ᶠ k in atTop, t ≤ r (φ k) := by
    have hcast : Tendsto (fun k => (φ k : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp hφ.tendsto_atTop
    filter_upwards [hcast.eventually (eventually_ge_atTop t)] with k hk
    dsimp [r]
    exact hk.trans
      ((by linarith : (φ k : ℝ) ≤ (φ k : ℝ) + 1).trans (hq (φ k)))
  have hseg_limit (t : ℝ) (ht : 0 ≤ t) :
      t • uInf ∈ SegDom (I := I) g hEnorm p := by
    apply (isClosed_segDom (I := I) g hEnorm p).mem_of_tendsto
      (hlim.const_smul t)
    filter_upwards [hfar_subseq t] with k htk
    have h0 : 0 ≤ t / r (φ k) := div_nonneg ht (hrpos _).le
    have h1 : t / r (φ k) ≤ 1 := (div_le_one (hrpos _)).2 htk
    have hs := segDom_smul (I := I) g hEnorm (hvseg (φ k)) h0 h1
    simpa [u, Function.comp_apply, div_eq_mul_inv, smul_smul] using hs
  have hC_limit (t : ℝ) (ht : 0 ≤ t) :
      expMapIntrinsic (I := I) g hEnorm p (t • uInf) ∈ C := by
    apply hCclosed.mem_of_tendsto (by
      simpa only [Function.comp_apply] using
        ((expMapIntrinsic_continuous (I := I) g hEnorm p).tendsto (t • uInf)).comp
          (hlim.const_smul t))
    filter_upwards [hfar_subseq t] with k htk
    have h0 : 0 ≤ t / r (φ k) := div_nonneg ht (hrpos _).le
    have h1 : t / r (φ k) ≤ 1 := (div_le_one (hrpos _)).2 htk
    have hm := hCseg (φ k) ⟨h0, h1⟩
    simpa only [u, Function.comp_apply, expMapIntrinsic_def,
      intrinsicGeodesic_smul, div_eq_mul_inv, smul_smul] using hm
  have hmin : IsMinRay (I := I)
      (intrinsicGeodesic (I := I) g hEnorm p uInf) := by
    intro s t hs hst
    let γ : ℝ → M := intrinsicGeodesic (I := I) g hEnorm p uInf
    have hbase (a : ℝ) (ha : 0 ≤ a) :
        (riemannianEDist I p (γ a)).toReal = a := by
      have hm := (mem_segDom (I := I)).mp (hseg_limit a ha)
      have hexp : expMapIntrinsic (I := I) g hEnorm p (a • uInf) = γ a := by
        change expMapIntrinsic (I := I) g hEnorm p (a • uInf) =
          intrinsicGeodesic (I := I) g hEnorm p uInf a
        rw [expMapIntrinsic_def, intrinsicGeodesic_smul]
      rw [hexp, sqrt_gInner_smul_self (I := I) g p ha, huInf_eq,
        Real.sqrt_one, mul_one] at hm
      exact hm.symm
    have hup : (riemannianEDist I (γ s) (γ t)).toReal ≤ t - s := by
      have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top
        (intrinsicGeodesic_riemannianEDist_le
          (I := I) g hEnorm p uInf hst)
      simpa [γ, huInf_eq, ENNReal.toReal_ofReal (sub_nonneg.mpr hst)] using h
    have htri : (riemannianEDist I p (γ t)).toReal ≤
        (riemannianEDist I p (γ s)).toReal +
          (riemannianEDist I (γ s) (γ t)).toReal :=
      ENNReal.toReal_le_add riemannianEDist_triangle
        (riemannianEDist_ne_top (I := I) p (γ s))
        (riemannianEDist_ne_top (I := I) (γ s) (γ t))
    rw [hbase t (hs.trans hst), hbase s hs] at htri
    linarith
  refine ⟨uInf, huInf, hmin,
    (intrinsicGeodesic_isGeodesic (I := I) g hEnorm p uInf).isGeodesicOn _, ?_⟩
  intro t ht
  simpa only [expMapIntrinsic_def, intrinsicGeodesic_smul] using hC_limit t ht

theorem minRay_of_escape
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) (q : ℕ → M)
    (hq : ∀ n : ℕ,
      (n : ℝ) + 1 ≤ (riemannianEDist I p (q n)).toReal) :
    ∃ u : TangentSpace I p, g.inner p u u = 1 ∧
      IsMinRay (I := I) (intrinsicGeodesic (I := I) g hEnorm p u) := by
  obtain ⟨u, hu, hγ, _, _⟩ := minRay_in_of_escape
    (I := I) g hEnorm Set.univ isClosed_univ IsTotallyConvex.univ
      p (Set.mem_univ p) q (fun n => Set.mem_univ (q n)) hq
  exact ⟨u, hu, hγ⟩

end Riemannian
end Geometry
end DifferentialGeometry

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

theorem exists_minRay_in
    {g : SmoothRiemannianMetric I M}
    (hg : RiemannianMetricComplete (I := I) g)
    {C : Set M} (hCclosed : IsClosed C)
    (hCconv : IsTotallyConvex (I := I) g C)
    (p : M) (hp : p ∈ C) (hCnoncompact : ¬ IsCompact C) :
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
      fun x v => tensor0SBundle_enorm_eq_riemannianBundle_enorm
        (I := I) g x v
    ∃ u : TangentSpace I p, g.inner p u u = 1 ∧
      IsMinGeodesicRay (I := I) g
        (intrinsicGeodesic (I := I) g hEnorm p u) ∧
      Set.MapsTo (intrinsicGeodesic (I := I) g hEnorm p u) (Set.Ici 0) C := by
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
    fun x v => tensor0SBundle_enorm_eq_riemannianBundle_enorm
      (I := I) g x v
  have hfar (n : ℕ) : ∃ x : M, x ∈ C ∧
      (n : ℝ) + 1 ≤ (riemannianEDist I p x).toReal := by
    have hcompact := closedEBall_isCompact (I := I) hg p ((n : ℝ) + 1)
    have hnotSub : ¬ C ⊆
        {x : M | riemannianEDistOf (I := I) g p x ≤
          ENNReal.ofReal ((n : ℝ) + 1)} := by
      intro hsub
      exact hCnoncompact (hcompact.of_isClosed_subset hCclosed hsub)
    obtain ⟨x, hxC, hx⟩ := Set.not_subset.mp hnotSub
    refine ⟨x, hxC, ?_⟩
    have hle : ENNReal.ofReal ((n : ℝ) + 1) ≤
        riemannianEDist I p x := by
      have hx' : ¬riemannianEDistOf (I := I) g p x ≤
          ENNReal.ofReal ((n : ℝ) + 1) := hx
      have hle' := le_of_lt (lt_of_not_ge hx')
      simpa only [riemannianEDistOf] using hle'
    have hreal := (ENNReal.toReal_le_toReal ENNReal.ofReal_ne_top
      (riemannianEDist_ne_top (I := I) p x)).2 hle
    have hn : 0 ≤ (n : ℝ) + 1 := by positivity
    rw [ENNReal.toReal_ofReal hn] at hreal
    exact hreal
  choose q hqC hq using hfar
  obtain ⟨u, hu, hmin, hgeo, hmap⟩ := Geometry.Riemannian.minRay_in_of_escape
    (I := I) g hEnorm C hCclosed hCconv p hp q hqC hq
  refine ⟨u, hu, ⟨?_, hgeo⟩, hmap⟩
  change IsMinRay (I := I) (intrinsicGeodesic (I := I) g hEnorm p u)
  exact hmin

theorem exists_minRay
    {g : SmoothRiemannianMetric I M}
    (hg : RiemannianMetricComplete (I := I) g)
    [NoncompactSpace M] (p : M) :
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
      fun x v => tensor0SBundle_enorm_eq_riemannianBundle_enorm
        (I := I) g x v
    ∃ u : TangentSpace I p, g.inner p u u = 1 ∧
      IsMinRay (I := I) (intrinsicGeodesic (I := I) g hEnorm p u) := by
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
    fun x v => tensor0SBundle_enorm_eq_riemannianBundle_enorm
      (I := I) g x v
  have hnoncompact : ¬ IsCompact (Set.univ : Set M) := by
    intro hcompact
    exact hcompact.ne_univ rfl
  obtain ⟨u, hu, hγ, _⟩ := exists_minRay_in
    (I := I) hg (C := Set.univ) isClosed_univ IsTotallyConvex.univ
      p (Set.mem_univ p) hnoncompact
  have hmin := hγ.minRay
  change IsMinRay (I := I) (intrinsicGeodesic (I := I) g hEnorm p u) at hmin
  exact ⟨u, hu, hmin⟩

end RiemannianMetricComplete
end DifferentialGeometry
