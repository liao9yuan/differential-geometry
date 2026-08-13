import DifferentialGeometry.Geometry.Exponential.MinimizingGeodesic

/-!
# Busemann functions: the metric layer

This file begins the nonnegative-curvature comparison package with the part of
the Busemann construction that uses only the Riemannian distance.  A minimizing
ray is recorded by its exact distance along nonnegative parameters.  Its
Busemann function is the infimum of the usual distance-minus-time
approximants.

Curvature, weak Laplacian comparison, elliptic regularity, and the
Cheeger--Gromoll splitting theorem belong in later modules.  Keeping this file
purely metric makes those analytic and geometric frontiers explicit.
-/

noncomputable section

open Set Bundle Manifold
open scoped Topology Manifold ContDiff ENNReal

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace

variable [RiemannianBundle (fun x : M => TangentSpace I x)]

open Exponential

/-- The real value of the intrinsic Riemannian distance is nonnegative. -/
theorem riemDist_nonneg (x y : M) :
    0 ≤ (riemannianEDist I x y).toReal :=
  ENNReal.toReal_nonneg

/-- The real value of the intrinsic Riemannian distance is symmetric. -/
theorem riemDist_comm (x y : M) :
    (riemannianEDist I x y).toReal = (riemannianEDist I y x).toReal := by
  rw [riemannianEDist_comm]

variable [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [IsManifold I ∞ M] [T2Space M] [T2Space (TangentBundle I M)]
  [SigmaCompactSpace M] [ConnectedSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

/-- The real value of the intrinsic Riemannian distance satisfies the triangle
inequality on a connected manifold. -/
theorem riemDist_triangle (x y z : M) :
    (riemannianEDist I x z).toReal ≤
      (riemannianEDist I x y).toReal + (riemannianEDist I y z).toReal := by
  exact ENNReal.toReal_le_add riemannianEDist_triangle
    (riemannianEDist_ne_top (I := I) x y)
    (riemannianEDist_ne_top (I := I) y z)

/-- A unit-speed minimizing ray, recorded by exact distance between all of its
nonnegative parameters.  Geodesicity and smoothness are supplied separately by
the differential-geometric ray constructor. -/
def IsMinRay (γ : ℝ → M) : Prop :=
  ∀ ⦃s t : ℝ⦄, 0 ≤ s → s ≤ t →
    (riemannianEDist I (γ s) (γ t)).toReal = t - s

/-- A unit-speed minimizing line, recorded by exact distance between ordered
parameters. -/
def IsMinLine (γ : ℝ → M) : Prop :=
  ∀ ⦃s t : ℝ⦄, s ≤ t →
    (riemannianEDist I (γ s) (γ t)).toReal = t - s

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [IsManifold I ∞ M]
  [T2Space M] [T2Space (TangentBundle I M)] [SigmaCompactSpace M]
  [ConnectedSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)] in
/-- The positive half of a minimizing line is a minimizing ray. -/
theorem minLine_pos {γ : ℝ → M} (hγ : IsMinLine (I := I) γ) :
    IsMinRay (I := I) γ := by
  intro s t _hs hst
  exact hγ hst

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [IsManifold I ∞ M]
  [T2Space M] [T2Space (TangentBundle I M)] [SigmaCompactSpace M]
  [ConnectedSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)] in
/-- Reversing the negative half of a minimizing line gives a minimizing ray. -/
theorem minLine_neg {γ : ℝ → M} (hγ : IsMinLine (I := I) γ) :
    IsMinRay (I := I) (fun t => γ (-t)) := by
  intro s t _hs hst
  rw [riemDist_comm (I := I) (γ (-s)) (γ (-t))]
  have h := hγ (s := -t) (t := -s) (neg_le_neg hst)
  simpa only [neg_sub_neg] using h

/-- The distance-minus-time approximant associated to a ray. -/
def buseApprox (γ : ℝ → M) (t : ℝ) (x : M) : ℝ :=
  (riemannianEDist I (γ t) x).toReal - t

/-- Busemann approximants decrease as their ray parameter increases. -/
theorem buseApprox_anti {γ : ℝ → M} (hγ : IsMinRay (I := I) γ)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (x : M) :
    buseApprox (I := I) γ t x ≤ buseApprox (I := I) γ s x := by
  have htri := riemDist_triangle (I := I) (γ t) (γ s) x
  have hdist : (riemannianEDist I (γ t) (γ s)).toReal = t - s := by
    rw [riemDist_comm (I := I) (γ t) (γ s)]
    exact hγ hs hst
  rw [hdist] at htri
  dsimp only [buseApprox]
  linarith

/-- Every Busemann approximant is bounded below by minus the distance from the
ray origin. -/
theorem buseApprox_lower {γ : ℝ → M} (hγ : IsMinRay (I := I) γ)
    {t : ℝ} (ht : 0 ≤ t) (x : M) :
    -(riemannianEDist I (γ 0) x).toReal ≤ buseApprox (I := I) γ t x := by
  have htri := riemDist_triangle (I := I) (γ 0) x (γ t)
  have h0t : (riemannianEDist I (γ 0) (γ t)).toReal = t := by
    simpa using hγ (s := 0) (t := t) le_rfl ht
  have hxt : (riemannianEDist I x (γ t)).toReal =
      (riemannianEDist I (γ t) x).toReal :=
    riemDist_comm (I := I) x (γ t)
  rw [h0t, hxt] at htri
  dsimp only [buseApprox]
  linarith

/-- At a fixed time, two Busemann approximants differ by at most the distance
between their evaluation points. -/
theorem buseApprox_dist (γ : ℝ → M) (t : ℝ) (x y : M) :
    |buseApprox (I := I) γ t x - buseApprox (I := I) γ t y| ≤
      (riemannianEDist I x y).toReal := by
  have hxy := riemDist_triangle (I := I) (γ t) x y
  have hyx := riemDist_triangle (I := I) (γ t) y x
  rw [riemDist_comm (I := I) y x] at hyx
  rw [abs_le]
  constructor <;> dsimp only [buseApprox] <;> linarith

private def buseSet (γ : ℝ → M) (x : M) : Set ℝ :=
  (fun t => buseApprox (I := I) γ t x) '' Ici 0

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [IsManifold I ∞ M]
  [T2Space M] [T2Space (TangentBundle I M)] [SigmaCompactSpace M]
  [ConnectedSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)] in
private theorem buseSet_nonempty (γ : ℝ → M) (x : M) :
    (buseSet (I := I) γ x).Nonempty := by
  exact ⟨buseApprox (I := I) γ 0 x, ⟨0, self_mem_Ici, rfl⟩⟩

private theorem buseSet_bddBelow {γ : ℝ → M} (hγ : IsMinRay (I := I) γ)
    (x : M) : BddBelow (buseSet (I := I) γ x) := by
  refine ⟨-(riemannianEDist I (γ 0) x).toReal, ?_⟩
  intro a ha
  rcases ha with ⟨t, ht, rfl⟩
  exact buseApprox_lower (I := I) hγ ht x

/-- The Busemann function of a minimizing ray, defined as the infimum of its
distance-minus-time approximants over nonnegative time. -/
def busemann (γ : ℝ → M) (x : M) : ℝ :=
  sInf (buseSet (I := I) γ x)

/-- The Busemann function lies below every nonnegative-time approximant. -/
theorem busemann_le_approx {γ : ℝ → M} (hγ : IsMinRay (I := I) γ)
    {t : ℝ} (ht : 0 ≤ t) (x : M) :
    busemann (I := I) γ x ≤ buseApprox (I := I) γ t x := by
  exact csInf_le (buseSet_bddBelow (I := I) hγ x) ⟨t, ht, rfl⟩

/-- The Busemann function has the same origin-distance lower bound as all of
its approximants. -/
theorem busemann_lower {γ : ℝ → M} (hγ : IsMinRay (I := I) γ) (x : M) :
    -(riemannianEDist I (γ 0) x).toReal ≤ busemann (I := I) γ x := by
  apply le_csInf (buseSet_nonempty (I := I) γ x)
  intro a ha
  rcases ha with ⟨t, ht, rfl⟩
  exact buseApprox_lower (I := I) hγ ht x

/-- The Busemann function is one-Lipschitz with respect to the real intrinsic
Riemannian distance. -/
theorem busemann_dist {γ : ℝ → M} (hγ : IsMinRay (I := I) γ) (x y : M) :
    |busemann (I := I) γ x - busemann (I := I) γ y| ≤
      (riemannianEDist I x y).toReal := by
  have hxy : busemann (I := I) γ x - (riemannianEDist I x y).toReal ≤
      busemann (I := I) γ y := by
    apply le_csInf (buseSet_nonempty (I := I) γ y)
    intro a ha
    rcases ha with ⟨t, ht, rfl⟩
    have hle := busemann_le_approx (I := I) hγ ht x
    have hdist := buseApprox_dist (I := I) γ t x y
    rw [abs_le] at hdist
    linarith
  have hyx : busemann (I := I) γ y - (riemannianEDist I x y).toReal ≤
      busemann (I := I) γ x := by
    apply le_csInf (buseSet_nonempty (I := I) γ x)
    intro a ha
    rcases ha with ⟨t, ht, rfl⟩
    have hle := busemann_le_approx (I := I) hγ ht y
    have hdist := buseApprox_dist (I := I) γ t y x
    rw [riemDist_comm (I := I) y x, abs_le] at hdist
    linarith
  rw [abs_le]
  constructor <;> linarith

/-- The Busemann function of a minimizing ray is continuous in the manifold
topology. -/
theorem busemann_continuous {γ : ℝ → M} (hγ : IsMinRay (I := I) γ) :
    Continuous (busemann (I := I) γ) := by
  rw [continuous_iff_continuousAt]
  intro x
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  have hεe : 0 < ENNReal.ofReal ε := ENNReal.ofReal_pos.mpr hε
  have hnear : ∀ᶠ y in 𝓝 x, riemannianEDist I x y < ENNReal.ofReal ε :=
    eventually_riemannianEDist_lt I x hεe
  filter_upwards [hnear] with y hy
  rw [Real.dist_eq]
  have hdist := busemann_dist (I := I) hγ y x
  rw [riemDist_comm (I := I) y x] at hdist
  exact lt_of_le_of_lt hdist (ENNReal.toReal_lt_of_lt_ofReal hy)

/-- The sum of the two Busemann functions associated to the opposite halves of
a minimizing line is nonnegative. -/
theorem buse_sum_nonneg {γ : ℝ → M} (hγ : IsMinLine (I := I) γ) (x : M) :
    0 ≤ busemann (I := I) γ x +
      busemann (I := I) (fun t => γ (-t)) x := by
  have hp : IsMinRay (I := I) γ := minLine_pos (I := I) hγ
  have hn : IsMinRay (I := I) (fun t => γ (-t)) := minLine_neg (I := I) hγ
  have hminus :
      -busemann (I := I) γ x ≤ busemann (I := I) (fun t => γ (-t)) x := by
    apply le_csInf (buseSet_nonempty (I := I) (fun t => γ (-t)) x)
    intro a ha
    rcases ha with ⟨s, hs, rfl⟩
    simp only [mem_Ici] at hs
    have hplus :
        -buseApprox (I := I) (fun t => γ (-t)) s x ≤
          busemann (I := I) γ x := by
      apply le_csInf (buseSet_nonempty (I := I) γ x)
      intro b hb
      rcases hb with ⟨t, ht, rfl⟩
      simp only [mem_Ici] at ht
      have htri := riemDist_triangle (I := I) (γ (-s)) x (γ t)
      have hline : (riemannianEDist I (γ (-s)) (γ t)).toReal = t + s := by
        have hst : -s ≤ t := by linarith
        have h := hγ hst
        simpa only [sub_neg_eq_add] using h
      have hxt : (riemannianEDist I x (γ t)).toReal =
          (riemannianEDist I (γ t) x).toReal :=
        riemDist_comm (I := I) x (γ t)
      rw [hline, hxt] at htri
      dsimp only [buseApprox]
      linarith
    linarith
  linarith

/-- Along a minimizing ray, its Busemann function has the exact value `-s`. -/
theorem busemann_ray {γ : ℝ → M} (hγ : IsMinRay (I := I) γ)
    {s : ℝ} (hs : 0 ≤ s) :
    busemann (I := I) γ (γ s) = -s := by
  apply le_antisymm
  · have hle := busemann_le_approx (I := I) hγ hs (γ s)
    simpa [buseApprox, riemannianEDist_self] using hle
  · have hlower := busemann_lower (I := I) hγ (γ s)
    have h0s : (riemannianEDist I (γ 0) (γ s)).toReal = s := by
      simpa using hγ (s := 0) (t := s) le_rfl hs
    simpa [h0s] using hlower

/-- On a minimizing line, the sum of the Busemann functions of its two halves
vanishes at every point of the line. -/
theorem buse_sum_line {γ : ℝ → M} (hγ : IsMinLine (I := I) γ) (u : ℝ) :
    busemann (I := I) γ (γ u) +
      busemann (I := I) (fun t => γ (-t)) (γ u) = 0 := by
  apply le_antisymm
  · have hp : IsMinRay (I := I) γ := minLine_pos (I := I) hγ
    have hn : IsMinRay (I := I) (fun t => γ (-t)) := minLine_neg (I := I) hγ
    rcases le_total 0 u with hu | hu
    · have hpval := busemann_ray (I := I) hp hu
      have hnle := busemann_le_approx (I := I) hn (t := 0) le_rfl (γ u)
      have h0u := hγ (s := 0) (t := u) hu
      have happ :
          buseApprox (I := I) (fun t => γ (-t)) 0 (γ u) = u := by
        simpa [buseApprox] using h0u
      rw [hpval]
      rw [happ] at hnle
      linarith
    · have hnu : 0 ≤ -u := neg_nonneg.mpr hu
      have hnval :
          busemann (I := I) (fun t => γ (-t)) (γ u) = u := by
        simpa only [neg_neg] using busemann_ray (I := I) hn hnu
      have hple := busemann_le_approx (I := I) hp (t := 0) le_rfl (γ u)
      have hu0 := hγ (s := u) (t := 0) hu
      have h0u : (riemannianEDist I (γ 0) (γ u)).toReal = -u := by
        rw [riemDist_comm (I := I) (γ 0) (γ u)]
        simpa only [zero_sub] using hu0
      have happ : buseApprox (I := I) γ 0 (γ u) = -u := by
        simp only [buseApprox, h0u, sub_zero]
      rw [hnval]
      rw [happ] at hple
      linarith
  · exact buse_sum_nonneg (I := I) hγ (γ u)

/-- The Busemann function vanishes at the origin of its minimizing ray. -/
@[simp] theorem busemann_zero {γ : ℝ → M} (hγ : IsMinRay (I := I) γ) :
    busemann (I := I) γ (γ 0) = 0 := by
  simpa using busemann_ray (I := I) hγ (s := 0) le_rfl

end Riemannian
end Geometry
end DifferentialGeometry
