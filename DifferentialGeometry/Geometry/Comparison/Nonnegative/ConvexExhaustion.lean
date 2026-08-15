import Mathlib.Topology.Compactness.SigmaCompact
import DifferentialGeometry.Geometry.Comparison.Nonnegative.BusemannConcavity
import DifferentialGeometry.Geometry.Comparison.Nonnegative.Ray

noncomputable section

open Set Bundle Manifold
open scoped Topology Manifold ContDiff ENNReal

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [IsManifold I ∞ M] [T2Space M] [T2Space (TangentBundle I M)]
  [SigmaCompactSpace M] [ConnectedSpace M]

def busemannHalfspace (g : SmoothRiemannianMetric I M)
    (γ : ℝ → M) (c : ℝ) : Set M :=
  {x | -busemannOf (I := I) g γ x ≤ c}

namespace busemannHalfspace

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [T2Space M] [T2Space (TangentBundle I M)] [SigmaCompactSpace M]
  [ConnectedSpace M] in
@[simp] theorem mem {g : SmoothRiemannianMetric I M}
    {γ : ℝ → M} {c : ℝ} {x : M} :
    x ∈ busemannHalfspace (I := I) g γ c ↔
      -busemannOf (I := I) g γ x ≤ c :=
  Iff.rfl

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [T2Space M] [T2Space (TangentBundle I M)] [SigmaCompactSpace M]
  [ConnectedSpace M] in
theorem mono {g : SmoothRiemannianMetric I M} {γ : ℝ → M}
    {c d : ℝ} (hcd : c ≤ d) :
    busemannHalfspace (I := I) g γ c ⊆
      busemannHalfspace (I := I) g γ d := by
  intro x hx
  exact hx.trans hcd

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M]
  [T2Space (TangentBundle I M)] [SigmaCompactSpace M] in
theorem isClosed {g : SmoothRiemannianMetric I M} {γ : ℝ → M}
    (hγ : IsMinRayOf (I := I) g γ) (c : ℝ) :
    IsClosed (busemannHalfspace (I := I) g γ c) := by
  exact isClosed_le (busemannOf.continuous hγ).neg continuous_const

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M]
  [T2Space (TangentBundle I M)] [SigmaCompactSpace M] in
@[simp] theorem ray_mem {g : SmoothRiemannianMetric I M} {γ : ℝ → M}
    (hγ : IsMinRayOf (I := I) g γ)
    {s c : ℝ} (hs : 0 ≤ s) :
    γ s ∈ busemannHalfspace (I := I) g γ c ↔ s ≤ c := by
  change -busemannOf (I := I) g γ (γ s) ≤ c ↔ s ≤ c
  rw [busemannOf.ray hγ hs, neg_neg]

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [T2Space M] [T2Space (TangentBundle I M)] [SigmaCompactSpace M]
  [ConnectedSpace M] in
theorem totallyConvex {g : SmoothRiemannianMetric I M} {γ : ℝ → M} {c : ℝ}
    (hγ : IsGeodesicConcave (I := I) g (busemannOf (I := I) g γ)) :
    IsTotallyConvex (I := I) g (busemannHalfspace (I := I) g γ c) := by
  simpa only [busemannHalfspace, neg_le] using
    IsGeodesicConcave.superlevel hγ (-c)

end busemannHalfspace

def rayBusemannSublevel (g : SmoothRiemannianMetric I M) (p : M) (c : ℝ) : Set M :=
  ⋂ (γ : ℝ → M), ⋂ (_ : IsMinGeodesicRay (I := I) g γ),
    ⋂ (_ : γ 0 = p), busemannHalfspace (I := I) g γ c

namespace rayBusemannSublevel

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [T2Space M] [T2Space (TangentBundle I M)] [SigmaCompactSpace M]
  [ConnectedSpace M] in
@[simp] theorem mem {g : SmoothRiemannianMetric I M} {p : M} {c : ℝ} {x : M} :
    x ∈ rayBusemannSublevel (I := I) g p c ↔
      ∀ (γ : ℝ → M), IsMinGeodesicRay (I := I) g γ → γ 0 = p →
        x ∈ busemannHalfspace (I := I) g γ c := by
  simp only [rayBusemannSublevel, Set.mem_iInter]

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [T2Space M] [T2Space (TangentBundle I M)] [SigmaCompactSpace M] in
theorem isClosed (g : SmoothRiemannianMetric I M) (p : M) (c : ℝ) :
    IsClosed (rayBusemannSublevel (I := I) g p c) := by
  unfold rayBusemannSublevel
  exact isClosed_iInter fun γ =>
    isClosed_iInter fun hγ =>
      isClosed_iInter fun _ => busemannHalfspace.isClosed hγ.minRay c

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [T2Space M] [T2Space (TangentBundle I M)] [SigmaCompactSpace M]
  [ConnectedSpace M] in
theorem mono {g : SmoothRiemannianMetric I M} {p : M} {c d : ℝ} (hcd : c ≤ d) :
    rayBusemannSublevel (I := I) g p c ⊆ rayBusemannSublevel (I := I) g p d := by
  intro x hx
  rw [mem] at hx ⊢
  intro γ hγ hγ0
  exact busemannHalfspace.mono hcd (hx γ hγ hγ0)

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [T2Space M] [T2Space (TangentBundle I M)] [SigmaCompactSpace M]
  [ConnectedSpace M] in
theorem monotone (g : SmoothRiemannianMetric I M) (p : M) :
    Monotone (rayBusemannSublevel (I := I) g p) :=
  fun _ _ hcd => mono hcd

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [T2Space M] [T2Space (TangentBundle I M)] [SigmaCompactSpace M] in
theorem base_mem (g : SmoothRiemannianMetric I M) (p : M) {c : ℝ} (hc : 0 ≤ c) :
    p ∈ rayBusemannSublevel (I := I) g p c := by
  rw [mem]
  intro γ hγ hγ0
  change -busemannOf (I := I) g γ p ≤ c
  rw [← hγ0, busemannOf.zero hγ.minRay, neg_zero]
  exact hc

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [T2Space M] [T2Space (TangentBundle I M)] [SigmaCompactSpace M] in
theorem dist_mem (g : SmoothRiemannianMetric I M) (p x : M) :
    x ∈ rayBusemannSublevel (I := I) g p
      (riemannianEDistOf (I := I) g p x).toReal := by
  rw [mem]
  intro γ hγ hγ0
  change -busemannOf (I := I) g γ x ≤
    (riemannianEDistOf (I := I) g p x).toReal
  have h := busemannOf.lower hγ.minRay x
  rw [hγ0] at h
  linarith

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [T2Space M] [T2Space (TangentBundle I M)] [SigmaCompactSpace M] in
theorem iUnion_nat (g : SmoothRiemannianMetric I M) (p : M) :
    (⋃ n : ℕ, rayBusemannSublevel (I := I) g p (n : ℝ)) = Set.univ := by
  ext x
  simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
  obtain ⟨n, hn⟩ := exists_nat_ge
    (riemannianEDistOf (I := I) g p x).toReal
  exact ⟨n, mono hn (dist_mem g p x)⟩

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [T2Space M] [T2Space (TangentBundle I M)] [SigmaCompactSpace M] in
theorem not_ray_mapsTo {g : SmoothRiemannianMetric I M} {p : M} {c : ℝ}
    {γ : ℝ → M} (hγ : IsMinGeodesicRay (I := I) g γ) (hγ0 : γ 0 = p) :
    ¬MapsTo γ (Set.Ici 0) (rayBusemannSublevel (I := I) g p c) := by
  intro hmap
  let s : ℝ := max 0 (c + 1)
  have hs0 : 0 ≤ s := le_max_left 0 (c + 1)
  have hcs : c < s :=
    lt_of_lt_of_le (lt_add_one c) (le_max_right 0 (c + 1))
  have hsC := hmap (show s ∈ Set.Ici 0 from hs0)
  rw [mem] at hsC
  have hhalf := hsC γ hγ hγ0
  have hsc := (busemannHalfspace.ray_mem hγ.minRay hs0).mp hhalf
  exact (not_le_of_gt hcs) hsc

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [T2Space M] [T2Space (TangentBundle I M)] [SigmaCompactSpace M] in
theorem subset_interior (g : SmoothRiemannianMetric I M) (p : M)
    {c d : ℝ} (hcd : c < d) :
    rayBusemannSublevel (I := I) g p c ⊆
      interior (rayBusemannSublevel (I := I) g p d) := by
  letI : RiemannianBundle (fun z : M ↦ TangentSpace I z) :=
    ⟨g.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle E
      (fun z : M ↦ TangentSpace I z) :=
    ⟨⟨g.inner, g.contMDiff.continuous, by intro z v w; rfl⟩⟩
  intro x hx
  apply mem_interior_iff_mem_nhds.mpr
  have hgap : 0 < ENNReal.ofReal (d - c) :=
    ENNReal.ofReal_pos.mpr (sub_pos.mpr hcd)
  filter_upwards [eventually_riemannianEDist_lt (I := I) (M := M) x hgap] with y hy
  rw [mem] at hx ⊢
  intro γ hγ hγ0
  have hxγ := hx γ hγ hγ0
  change -busemannOf (I := I) g γ x ≤ c at hxγ
  change -busemannOf (I := I) g γ y ≤ d
  have hdist := busemannOf.dist hγ.minRay x y
  rw [abs_le] at hdist
  have hreal : (riemannianEDistOf (I := I) g x y).toReal < d - c :=
    by
      change (riemannianEDist I x y).toReal < d - c
      exact ENNReal.toReal_lt_of_lt_ofReal hy
  linarith

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [T2Space M] [T2Space (TangentBundle I M)] [SigmaCompactSpace M]
  [ConnectedSpace M] in
theorem totallyConvex {g : SmoothRiemannianMetric I M} {p : M} {c : ℝ}
    (hconv : ∀ (γ : ℝ → M), IsMinGeodesicRay (I := I) g γ → γ 0 = p →
      IsGeodesicConcave (I := I) g (busemannOf (I := I) g γ)) :
    IsTotallyConvex (I := I) g (rayBusemannSublevel (I := I) g p c) := by
  intro η a b hab hη hηcont ha hb t ht
  rw [mem] at ha hb ⊢
  intro γ hγ hγ0
  exact busemannHalfspace.totallyConvex (hconv γ hγ hγ0) hab hη
    hηcont (ha γ hγ hγ0) (hb γ hγ hγ0) ht

end rayBusemannSublevel

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

theorem raySublevel_compact
    {g : SmoothRiemannianMetric I M}
    (hg : RiemannianMetricComplete (I := I) g) (p : M) {c : ℝ} :
    (∀ (γ : ℝ → M), IsMinGeodesicRay (I := I) g γ → γ 0 = p →
      IsGeodesicConcave (I := I) g (busemannOf (I := I) g γ)) →
    IsCompact (rayBusemannSublevel (I := I) g p c) := by
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
    ⟨g.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle E
      (fun x : M ↦ TangentSpace I x) :=
    ⟨⟨g.inner, g.contMDiff.continuous, by intro x v w; rfl⟩⟩
  intro hconv
  letI : IsManifold I 1 M :=
    IsManifold.of_le (I := I) (M := M) (n := (∞ : WithTop ℕ∞))
      (by decide : (1 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞))
  letI : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I M
  letI : T3Space M := inferInstance
  letI : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
  letI : CompleteSpace M := by simpa only using hg.complete
  let hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)) :=
    fun x v => tensor0SBundle_enorm_eq_riemannianBundle_enorm
      (I := I) g x v
  have compact_nonneg (d : ℝ) (hd : 0 ≤ d) :
      IsCompact (rayBusemannSublevel (I := I) g p d) := by
    by_contra hcompact
    have hclosed := Geometry.Riemannian.rayBusemannSublevel.isClosed g p d
    have htotal := Geometry.Riemannian.rayBusemannSublevel.totallyConvex
      (c := d) hconv
    obtain ⟨u, _, hγ, hmap⟩ := exists_minRay_in
      (I := I) hg hclosed htotal p
        (Geometry.Riemannian.rayBusemannSublevel.base_mem g p hd) hcompact
    have hγ0 : intrinsicGeodesic (I := I) g hEnorm p u 0 = p :=
      intrinsicGeodesic_zero (I := I) g hEnorm p u
    exact (Geometry.Riemannian.rayBusemannSublevel.not_ray_mapsTo hγ hγ0) hmap
  by_cases hc : 0 ≤ c
  · exact compact_nonneg c hc
  · exact (compact_nonneg 0 le_rfl).of_isClosed_subset
      (Geometry.Riemannian.rayBusemannSublevel.isClosed g p c)
      (Geometry.Riemannian.rayBusemannSublevel.mono (le_of_not_ge hc))

theorem ray_convex_of_nonneg
    {g : SmoothRiemannianMetric I M}
    (hg : RiemannianMetricComplete (I := I) g) (p : M) {c : ℝ}
    (hsec : Integral.Connection.NonnegSecMetric (I := I) (M := M) g) :
    IsTotallyConvex (I := I) g
      (Geometry.Riemannian.rayBusemannSublevel (I := I) g p c) := by
  apply Geometry.Riemannian.rayBusemannSublevel.totallyConvex
  intro γ hγ hγ0
  exact buse_geo_concave (I := I) hg hγ.minRay hsec

theorem ray_compact_nonneg
    {g : SmoothRiemannianMetric I M}
    (hg : RiemannianMetricComplete (I := I) g) (p : M) {c : ℝ}
    (hsec : Integral.Connection.NonnegSecMetric (I := I) (M := M) g) :
    IsCompact
      (Geometry.Riemannian.rayBusemannSublevel (I := I) g p c) := by
  apply raySublevel_compact (I := I) hg p
  intro γ hγ hγ0
  exact buse_geo_concave (I := I) hg hγ.minRay hsec

def rayExhaustion
    {g : SmoothRiemannianMetric I M}
    (hg : RiemannianMetricComplete (I := I) g) (p : M)
    (hsec : Integral.Connection.NonnegSecMetric (I := I) (M := M) g) :
    CompactExhaustion M where
  toFun n := Geometry.Riemannian.rayBusemannSublevel (I := I) g p (n : ℝ)
  isCompact' n := ray_compact_nonneg (I := I) hg p hsec
  subset_interior_succ' n := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      Geometry.Riemannian.rayBusemannSublevel.subset_interior
        (I := I) g p (c := (n : ℝ)) (d := (n : ℝ) + 1) (by linarith)
  iUnion_eq' := Geometry.Riemannian.rayBusemannSublevel.iUnion_nat
    (I := I) g p

theorem rayExhaustion_convex
    {g : SmoothRiemannianMetric I M}
    (hg : RiemannianMetricComplete (I := I) g) (p : M)
    (hsec : Integral.Connection.NonnegSecMetric (I := I) (M := M) g) (n : ℕ) :
    IsTotallyConvex (I := I) g (rayExhaustion (I := I) hg p hsec n) := by
  simpa only [rayExhaustion] using
    (ray_convex_of_nonneg (I := I) hg p (c := (n : ℝ)) hsec)

end RiemannianMetricComplete
end DifferentialGeometry
