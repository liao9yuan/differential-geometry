import DifferentialGeometry.Geometry.Comparison.DistanceSemiconcavity
import DifferentialGeometry.Geometry.Comparison.GeodesicSpeedBound
import DifferentialGeometry.Geometry.Comparison.Nonnegative.Busemann
import DifferentialGeometry.Geometry.Metric.Completeness
import Mathlib.Analysis.SpecificLimits.Basic

set_option autoImplicit false

noncomputable section

open Bundle Filter Function Manifold Set Topology
open scoped ContDiff ENNReal Manifold Topology

namespace DifferentialGeometry

open Geometry.Riemannian
open Geometry.Riemannian.Exponential
open Geometry.Riemannian.HopfRinow
open Integral.Connection

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
theorem buse_comp_concave
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    [ConnectedSpace M] [T2Space (TangentBundle I M)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    {η γ : ℝ → M}
    (hη : IsMinRay (I := I) η)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ)
    (hgeo : Geodesic.IsGeodesic (I := I) g γ)
    (hsec : NonnegSecMetric (I := I) (M := M) g)
    {a b : ℝ} (hab : a ≤ b) :
    ConcaveOn ℝ (Icc a b) (busemann (I := I) η ∘ γ) := by
  let d₀ : ℝ → ℝ := fun s =>
    (riemannianEDist I (η 0) (γ s)).toReal
  have hdist : Continuous (fun x : M => riemannianEDist I (η 0) x) := by
    simpa only [riemannianEDist_comm] using
      (continuous_riemannianEDist_to (I := I) (η 0))
  have hd₀ : Continuous d₀ := by
    apply continuousOn_univ.mp
    refine ENNReal.continuousOn_toReal.comp'
      (hdist.comp hγ.continuous).continuousOn ?_
    intro s _
    exact riemannianEDist_ne_top (I := I) (η 0) (γ s)
  obtain ⟨s₀, hs₀, hs₀max⟩ :=
    isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr hab) hd₀.continuousOn
  let R : ℝ := max (d₀ s₀) 0
  have hR0 : 0 ≤ R := le_max_right _ _
  have hR (s : ℝ) (hs : s ∈ Icc a b) : d₀ s ≤ R :=
    (hs₀max hs).trans (le_max_left _ _)
  let T : ℕ → ℝ := fun n => R + (n : ℝ) + 1
  let q : ℕ → ℝ := fun n => (n : ℝ) + 1
  let K : ℝ :=
    g.inner (γ a) (mfderiv 𝓘(ℝ, ℝ) I γ a 1)
      (mfderiv 𝓘(ℝ, ℝ) I γ a 1)
  let A : ℕ → ℝ := fun n => K / q n
  let G : ℕ → ℝ → ℝ := fun n s =>
    buseApprox (I := I) η (T n) (γ s) - A n * s ^ 2
  have hC1 : ContMDiff 𝓘(ℝ, ℝ) I 1 γ :=
    hγ.of_le (by decide : (1 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞))
  have hspeed (s : ℝ) :
      g.inner (γ s) (mfderiv 𝓘(ℝ, ℝ) I γ s 1)
          (mfderiv 𝓘(ℝ, ℝ) I γ s 1) = K := by
    exact HopfRinow.geodesic_speed_constant (I := I) g hgeo hC1 s a
  have hsep (n : ℕ) (s : ℝ) (hs : s ∈ Icc a b) :
      q n ≤ (riemannianEDist I (η (T n)) (γ s)).toReal := by
    have hT0 : 0 ≤ T n := by
      dsimp only [T]
      positivity
    have hray :
        (riemannianEDist I (η 0) (η (T n))).toReal = T n := by
      simpa only [sub_zero] using hη (s := 0) (t := T n) le_rfl hT0
    have htri := riemDist_triangle (I := I) (η 0) (γ s) (η (T n))
    rw [hray, riemDist_comm (I := I) (γ s) (η (T n))] at htri
    have hbound := hR s hs
    dsimp only [d₀, T, q] at htri hbound ⊢
    linarith
  have hG (n : ℕ) : ConcaveOn ℝ (Icc a b) (G n) := by
    have hsemi : ConcaveOn ℝ (Icc a b) (fun s =>
        (riemannianEDist I (η (T n)) (γ s)).toReal - A n * s ^ 2) := by
      apply dist_geo_semiconcave (I := I) g hEnorm
        (D := Icc a b) (δ := q n) (S := K) (convex_Icc a b) hγ
        (fun t _ => hgeo t)
        (fun t _ => riemannianEDist_ne_top (I := I) (η (T n)) (γ t))
        (by dsimp only [q]; positivity)
        (fun t ht => hsep n t (interior_subset ht))
        (fun t _ => (hspeed t).le) hsec
    have hadd := hsemi.add_const (-(T n))
    have heq :
        (fun s =>
          ((riemannianEDist I (η (T n)) (γ s)).toReal - A n * s ^ 2) +
            (-(T n))) = G n := by
      funext s
      dsimp only [G, buseApprox]
      ring
    rw [← heq]
    simpa only [Pi.add_apply] using hadd
  have hnat : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hT : Tendsto T atTop atTop := by
    simpa only [T, add_assoc, add_comm, add_left_comm] using
      tendsto_atTop_add_const_right atTop (R + 1) hnat
  have hqTop : Tendsto q atTop atTop := by
    simpa only [q] using
      tendsto_atTop_add_const_right atTop 1 hnat
  have hA0 : Tendsto A atTop (𝓝 0) := by
    dsimp only [A]
    exact tendsto_const_nhds.div_atTop hqTop
  have herr (s : ℝ) :
      Tendsto (fun n => A n * s ^ 2) atTop (𝓝 0) := by
    simpa only [zero_mul] using hA0.mul_const (s ^ 2)
  have happrox (s : ℝ) :
      Tendsto (fun n => buseApprox (I := I) η (T n) (γ s)) atTop
        (𝓝 (busemann (I := I) η (γ s))) :=
    (buseApprox_tendsto (I := I) hη (γ s)).comp hT
  have hlim (s : ℝ) (_hs : s ∈ Icc a b) :
      Tendsto (fun n => G n s) atTop
        (𝓝 ((busemann (I := I) η ∘ γ) s)) := by
    simpa only [G, Function.comp_apply, sub_zero] using
      (happrox s).sub (herr s)
  exact Analysis.concaveOn_tendsto hG hlim

end DifferentialGeometry

namespace DifferentialGeometry
namespace RiemannianMetricComplete

open Bundle Manifold Set
open scoped ContDiff ENNReal Manifold Topology
open Geometry.Riemannian
open Integral.Connection

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
  [ConnectedSpace M] [T2Space (TangentBundle I M)]

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
theorem buse_comp_concave
    {g : SmoothRiemannianMetric I M}
    (hg : RiemannianMetricComplete (I := I) g)
    {η γ : ℝ → M}
    (hη : IsMinRayOf (I := I) g η)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ)
    (hgeo : Geodesic.IsGeodesic (I := I) g γ)
    (hsec : NonnegSecMetric (I := I) (M := M) g)
    {a b : ℝ} (hab : a ≤ b) :
    ConcaveOn ℝ (Icc a b) (busemannOf (I := I) g η ∘ γ) := by
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
  change IsMinRay (I := I) η at hη
  change ConcaveOn ℝ (Icc a b) (busemann (I := I) η ∘ γ)
  exact DifferentialGeometry.buse_comp_concave
    (I := I) g hEnorm hη hγ hgeo hsec hab

end RiemannianMetricComplete
end DifferentialGeometry
