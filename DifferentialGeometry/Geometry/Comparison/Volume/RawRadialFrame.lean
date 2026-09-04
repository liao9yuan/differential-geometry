import DifferentialGeometry.Geometry.Comparison.Variation.PerpFrame
import DifferentialGeometry.Geometry.Curvature.RicciOperatorNormBound
import DifferentialGeometry.Geometry.Exponential.JacobiVariation
import DifferentialGeometry.Geometry.Exponential.Smoothness.Domain

noncomputable section

open Set Filter Bundle Manifold
open scoped Topology Manifold ContDiff

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace VolumeComparison

open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.Geometry.Riemannian.Exponential

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space (TangentBundle I M)]

private theorem exists_raw_frame_ne
    [NeZero (Module.finrank ℝ E)]
    (g : SmoothRiemannianMetric I M) (p : M) (u : E)
    {L : ℝ} (hL : 0 < L)
    (hdom : ∀ t ∈ Set.Icc (0 : ℝ) L,
      (show TangentSpace I p from t • u) ∈ expDomain (I := I) g p) :
    let γ : ℝ → M := fun t =>
      expMap (I := I) g p (show TangentSpace I p from t • u)
    ∃ F : Fin (Module.finrank ℝ E) → ∀ t : ℝ, TangentSpace I (γ t),
      (∀ t : ℝ, Fintype.card (Fin (Module.finrank ℝ E)) =
        Module.finrank ℝ (TangentSpace I (γ t))) ∧
      (∀ i, ∀ t ∈ Set.Icc (0 : ℝ) L,
        covDerivAlong (I := I) g γ (F i) t = 0) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) L, ∀ i j,
        g.inner (γ t) (F i t) (F j t) = if i = j then (1 : ℝ) else 0) ∧
      ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) L,
        DifferentiableAt ℝ (chartRepAt (I := I) γ (F i) t) t := by
  classical
  dsimp only
  let γ : ℝ → M := fun t =>
    expMap (I := I) g p (show TangentSpace I p from t • u)
  obtain ⟨γg, hγg, hgerm⟩ := exists_raw_ray_ext (I := I) g p u hL hdom
  obtain ⟨basis, hON0⟩ :=
    DifferentialGeometry.Geometry.Curvature.exists_gOrthonormalBasis
      (I := I) g (γg 0)
  obtain ⟨Fg, _hF0, hFdiff, hFpar, hFON⟩ :=
    exists_parallel_frame (I := I) g γg (N := 2) (by norm_num)
      (hγg.of_le (by exact_mod_cast le_top)) hL basis hON0
  let F : Fin (Module.finrank ℝ E) → ∀ t : ℝ, TangentSpace I (γ t) :=
    fun i t => show TangentSpace I (γ t) from (Fg i t : E)
  have hfield : ∀ i t,
      (fun s : ℝ => (F i s : E)) =ᶠ[𝓝 t] fun s : ℝ => (Fg i s : E) :=
    fun _ _ => Filter.Eventually.of_forall fun _ => rfl
  refine ⟨F, ?_, ?_, ?_, ?_⟩
  · intro t
    rw [Fintype.card_fin]
    rfl
  · intro i t ht
    have hcongr := covDerivAlong_congr_curve (I := I) g (F i) (Fg i)
      (hgerm t ht).symm (hfield i t)
    have hzero : (covDerivAlong (I := I) g γ (F i) t : E) = 0 := by
      rw [hcongr]
      simpa using congrArg (fun v => (v : E)) (hFpar i t ht)
    simpa using hzero
  · intro t ht i j
    have hpoint : γg t = γ t := (hgerm t ht).eq_of_nhds
    change g.inner (γ t) (F i t) (F j t) = if i = j then (1 : ℝ) else 0
    rw [← hpoint]
    simpa only [F] using hFON t ht i j
  · intro i t ht
    have hrep := chartRep_congr_curve (I := I) (F i) (Fg i)
      (hgerm t ht).symm (hfield i t)
    rw [hrep.differentiableAt_iff]
    exact hFdiff i t ht

/-- A raw radial exponential curve admits an orthonormal parallel frame on
every compact time segment contained in its maximal exponential domain. -/
theorem exists_raw_frame
    (g : SmoothRiemannianMetric I M) (p : M) (u : E)
    {L : ℝ} (hL : 0 < L)
    (hdom : ∀ t ∈ Set.Icc (0 : ℝ) L,
      (show TangentSpace I p from t • u) ∈ expDomain (I := I) g p) :
    let γ : ℝ → M := fun t =>
      expMap (I := I) g p (show TangentSpace I p from t • u)
    ∃ F : Fin (Module.finrank ℝ E) → ∀ t : ℝ, TangentSpace I (γ t),
      (∀ t : ℝ, Fintype.card (Fin (Module.finrank ℝ E)) =
        Module.finrank ℝ (TangentSpace I (γ t))) ∧
      (∀ i, ∀ t ∈ Set.Icc (0 : ℝ) L,
        covDerivAlong (I := I) g γ (F i) t = 0) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) L, ∀ i j,
        g.inner (γ t) (F i t) (F j t) = if i = j then (1 : ℝ) else 0) ∧
      ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) L,
        DifferentiableAt ℝ (chartRepAt (I := I) γ (F i) t) t := by
  classical
  by_cases hdim : Module.finrank ℝ E = 0
  · dsimp only
    let γ : ℝ → M := fun t =>
      expMap (I := I) g p (show TangentSpace I p from t • u)
    let F : Fin (Module.finrank ℝ E) → ∀ t : ℝ, TangentSpace I (γ t) :=
      fun i => Fin.elim0 (Fin.cast hdim i)
    refine ⟨F, ?_, ?_, ?_, ?_⟩
    · intro t
      rw [Fintype.card_fin]
      rfl
    · intro i
      exact Fin.elim0 (Fin.cast hdim i)
    · intro _ _ i
      exact Fin.elim0 (Fin.cast hdim i)
    · intro i
      exact Fin.elim0 (Fin.cast hdim i)
  · letI : NeZero (Module.finrank ℝ E) := ⟨hdim⟩
    exact exists_raw_frame_ne (I := I) g p u hL hdom

end VolumeComparison
end Riemannian
end Geometry
end DifferentialGeometry

end
