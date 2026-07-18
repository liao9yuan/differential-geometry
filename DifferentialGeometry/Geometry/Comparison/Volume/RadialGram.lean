import DifferentialGeometry.Geometry.Comparison.Variation.JacobiGram
import DifferentialGeometry.Geometry.Comparison.Volume.RadialGronwall

/-!
# Radial Gram data for volume comparison

This module connects the local radial-Jacobi producers to the Gram-matrix
calculus used by Bishop--Gromov comparison.
-/

noncomputable section

open Set Bundle
open scoped Topology Manifold ContDiff ENNReal

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace VolumeComparison

open DifferentialGeometry.Geometry.Riemannian.Variation
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]

section Radial

variable [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
  [T2Space (TangentBundle I M)]

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- On a common small radial scale, two radial Jacobi fields that vanish at the
center have zero Wronskian throughout every compact subinterval of `(0, 1)`.
The direction vectors are kept inside the common local-variation radius; a
later transverse-frame consumer may enforce this by a fixed positive scaling. -/
theorem radial_wronsk_zero
    [PseudoEMetricSpace M] [RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M] [CompleteSpace M] [ConnectedSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) :
    ∃ r : ℝ, 0 < r ∧ ∀ x w z : E,
      ‖x‖ < r → ‖w‖ < r → ‖z‖ < r →
      ∀ {b : ℝ}, 0 < b → b < 1 → ∀ t ∈ Icc (0 : ℝ) b,
        jacobiWronskian g (radialCurve (I := I) g p x)
          (radialJacobiField (I := I) g p x w)
          (radialJacobiField (I := I) g p x z) t = 0 := by
  obtain ⟨rd, hrd, hdiff⟩ := exists_radialJacobi_diff (I := I) g p
  obtain ⟨rj, hrj, hJac⟩ := exists_jacobi_Ioo (I := I) g p
  obtain ⟨r0, hr0, hJac0⟩ := exists_radialJacobi_zero_radius (I := I) g hEnorm p
  let re : ℝ := expMapC2Radius (I := I) g p
  let r : ℝ := min rd (min rj (min r0 re))
  have hre : 0 < re := expMapC2Radius_pos (I := I) g p
  have hr : 0 < r := by
    dsimp [r, re]
    exact lt_min hrd (lt_min hrj (lt_min hr0 hre))
  refine ⟨r, hr, ?_⟩
  intro x w z hx hw hz b hb hblt t ht
  have hr_rd : r ≤ rd := min_le_left _ _
  have hr_rj : r ≤ rj := (min_le_right _ _).trans (min_le_left _ _)
  have hr_r0 : r ≤ r0 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hr_re : r ≤ re :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hxrd : ‖x‖ < rd := hx.trans_le hr_rd
  have hxj : ‖x‖ < rj := hx.trans_le hr_rj
  have hx0 : ‖x‖ < r0 := hx.trans_le hr_r0
  have hxe : ‖x‖ < expMapC2Radius (I := I) g p := by
    simpa only [re] using hx.trans_le hr_re
  have hwrd : ‖w‖ < rd := hw.trans_le hr_rd
  have hzrd : ‖z‖ < rd := hz.trans_le hr_rd
  have hwj : ‖w‖ < rj := hw.trans_le hr_rj
  have hzj : ‖z‖ < rj := hz.trans_le hr_rj
  have hw0 : ‖w‖ < r0 := hw.trans_le hr_r0
  have hz0 : ‖z‖ < r0 := hz.trans_le hr_r0
  have hb1 : b ≤ 1 := hblt.le
  obtain ⟨hJdiff, hDJdiff⟩ := hdiff x w hxrd hwrd hb1
  obtain ⟨hKdiff, hDKdiff⟩ := hdiff x z hxrd hzrd hb1
  have hJ0 := hJac0 x w hx0 hw0
  have hK0 := hJac0 x z hx0 hz0
  have hJacJ : ∀ s ∈ Icc (0 : ℝ) b,
      IsJacobiAt (I := I) g (radialCurve (I := I) g p x)
        (radialJacobiField (I := I) g p x w) s := by
    intro s hs
    by_cases hs0 : s = 0
    · subst s
      simpa only [radialCurve] using hJ0
    · exact hJac x w hxj hwj (b := (1 : ℝ)) le_rfl s
        ⟨lt_of_le_of_ne hs.1 (Ne.symm hs0), hs.2.trans_lt hblt⟩
  have hJacK : ∀ s ∈ Icc (0 : ℝ) b,
      IsJacobiAt (I := I) g (radialCurve (I := I) g p x)
        (radialJacobiField (I := I) g p x z) s := by
    intro s hs
    by_cases hs0 : s = 0
    · subst s
      simpa only [radialCurve] using hK0
    · exact hJac x z hxj hzj (b := (1 : ℝ)) le_rfl s
        ⟨lt_of_le_of_ne hs.1 (Ne.symm hs0), hs.2.trans_lt hblt⟩
  exact wronskian_zero_on (I := I) (by norm_num) g
    (radialCurve (I := I) g p x)
    (radialJacobiField (I := I) g p x w)
    (radialJacobiField (I := I) g p x z)
    (radialCurve_contMDiffAt_Icc (I := I) g p x hb1 hxe)
    hJdiff hKdiff hDJdiff hDKdiff hJacJ hJacK
    (radialJacobi_zero (I := I) g p x w)
    (radialJacobi_zero (I := I) g p x z) t ht

end Radial

end VolumeComparison
end Riemannian
end Geometry
end DifferentialGeometry

end
