import DifferentialGeometry.Geometry.Comparison.Volume.RadialGronwall
import DifferentialGeometry.Geometry.Comparison.Volume.RawRadialFrame

noncomputable section

open Set Bundle Function Manifold
open scoped Topology Manifold ContDiff

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace VolumeComparison

open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Riemannian.Variation
open DifferentialGeometry.Geometry.Curvature

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [T2Space (TangentBundle I M)]

open Bundle in
attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- A raw radial Jacobi field cannot vanish at time one when the radial
curvature error is smaller than its initial linear growth. -/
theorem rawJacobi_ne_of_rm
    (g : SmoothRiemannianMetric I M) (p : M) (x w : E)
    {K R Vb : ℝ}
    (hdom : ∀ t ∈ Icc (0 : ℝ) 1,
      (show TangentSpace I p from t • x) ∈ expDomain (I := I) g p)
    (hK : 0 ≤ K) (hVb : 0 ≤ Vb)
    (hV : ∀ t ∈ Ioo (0 : ℝ) 1,
      Real.sqrt (g.inner (radialCurve (I := I) g p x t)
        (curveVelocity (I := I) (radialCurve (I := I) g p x) t)
        (curveVelocity (I := I) (radialCurve (I := I) g p x) t)) ≤ Vb)
    (hRm : ∀ t ∈ Ioo (0 : ℝ) 1,
      Real.sqrt (Tensor0SBundle.normSq0S (I := I) g
        (radialCurve (I := I) g p x t) 4
        (DifferentialGeometry.Geometry.Curvature.metricRm04At
          (I := I) (M := M) g (radialCurve (I := I) g p x t))) ≤ R)
    (hcoef :
      Real.sqrt ((Fintype.card
        (Fin 1 → Fin (Module.finrank ℝ E)) : ℝ)) * R * Vb ^ 2 ≤ K)
    (hw : w ≠ 0)
    (hsmall : gronwallBound 0 (max K 1) K 1 < 1) :
    radialJacobiField (I := I) g p x w 1 ≠ 0 := by
  classical
  have hdim : Module.finrank ℝ E ≠ 0 := by
    intro hzero
    letI : Subsingleton E := Module.finrank_zero_iff.1 hzero
    exact hw (Subsingleton.elim w 0)
  letI : NeZero (Module.finrank ℝ E) := ⟨hdim⟩
  have hγ : ∀ t ∈ Icc (0 : ℝ) 1,
      ContMDiffAt 𝓘(ℝ, ℝ) I 1 (radialCurve (I := I) g p x) t := by
    intro t ht
    have hline : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞
        (fun s : ℝ => s • x) t :=
      (contMDiff_id.smul contMDiff_const).contMDiffAt
    have hexp := expMap_contMDiffAt (I := I) g p (hdom t ht)
    simpa only [radialCurve] using
      (hexp.comp t hline).of_le (by decide : (1 : WithTop ℕ∞) ≤ ∞)
  obtain ⟨F, hcard, hpar, hON, hFdiff⟩ :=
    exists_raw_frame (I := I) g p x zero_lt_one hdom
  have hreg : ∀ t ∈ Icc (0 : ℝ) 1,
      DifferentiableAt ℝ
          (chartRepAt (I := I) (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x w) t) t ∧
        DifferentiableAt ℝ
          (chartRepAt (I := I) (radialCurve (I := I) g p x)
            (fun u => covDerivAlong (I := I) g
              (radialCurve (I := I) g p x)
              (radialJacobiField (I := I) g p x w) u) t) t := by
    intro t ht
    simpa only [radialCurve, radialJacobiField] using
      radial_jacobi_reg (I := I) g p x w t (hdom t ht)
  have hJac : ∀ t ∈ Ioo (0 : ℝ) 1,
      IsJacobiAt (I := I) g (radialCurve (I := I) g p x)
        (radialJacobiField (I := I) g p x w) t := by
    simpa only [radialCurve, radialJacobiField] using
      (radial_jacobi_on (I := I) g p x w hdom).2.2
  have hbasis : ∀ t : ℝ, t ∈ Ioo (0 : ℝ) 1 →
      ∃ basis : Module.Basis (Fin (Module.finrank ℝ E)) ℝ
          (TangentSpace I (radialCurve (I := I) g p x t)),
        ∀ i j,
          g.inner (radialCurve (I := I) g p x t) (basis i) (basis j) =
            if i = j then (1 : ℝ) else 0 := by
    intro t _ht
    simpa [show Module.finrank ℝ
        (TangentSpace I (radialCurve (I := I) g p x t)) =
          Module.finrank ℝ E from rfl] using
      (DifferentialGeometry.Geometry.Curvature.exists_gOrthonormalBasis
        (I := I) g (radialCurve (I := I) g p x t))
  choose basis hBasisON using hbasis
  have hcurv := by
    refine curv_sq_of_rm04_velocity_Ioo (I := I) g p x w hK hVb basis
      (fun t ht i j => hBasisON t ht i j) hV ?_
    intro t ht
    set C : ℝ :=
      Real.sqrt ((Fintype.card (Fin 1 → Fin (Module.finrank ℝ E)) : ℝ))
    set A : ℝ := Real.sqrt (Tensor0SBundle.normSq0S (I := I) g
      (radialCurve (I := I) g p x t) 4
      (DifferentialGeometry.Geometry.Curvature.metricRm04At
        (I := I) (M := M) g (radialCurve (I := I) g p x t)))
    have hC : 0 ≤ C := Real.sqrt_nonneg _
    have hV2 : 0 ≤ Vb ^ 2 := sq_nonneg Vb
    exact (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hRm t ht) hC) hV2).trans hcoef
  have hD2 :
      covDerivAlong (I := I) g (radialCurve (I := I) g p x)
        (fun s => covDerivAlong (I := I) g
          (radialCurve (I := I) g p x)
          (radialJacobiField (I := I) g p x w) s) 0 = 0 := by
    apply d2_zero_of_jac0 (I := I) g p x w
    simpa only [radialCurve, radialJacobiField] using
      radial_jacobi_at0 (I := I) g p x w
  have hODE := ode_Ico_of_Ioo_d2 (I := I) g p x w hJac hcurv hD2
  have hDJ0 : covDerivAlong (I := I) g
      (radialCurve (I := I) g p x)
      (radialJacobiField (I := I) g p x w) 0 =
        (show TangentSpace I (radialCurve (I := I) g p x 0) from w) := by
    change (covDerivAlong (I := I) g
      (radialCurve (I := I) g p x)
      (radialJacobiField (I := I) g p x w) 0 : E) = w
    simpa only [radialCurve, radialJacobiField] using
      radial_jacobi_d0 (I := I) g p x w
  have hs : 0 < Real.sqrt (g.inner p w w) :=
    Real.sqrt_pos.2 (g.pos p w hw)
  have hsmall' :
      gronwallBound 0 (max K 1)
          (K * ((1 : ℝ) * Real.sqrt (g.inner p w w))) 1 <
        (1 : ℝ) * Real.sqrt (g.inner p w w) := by
    have hscaled := mul_lt_mul_of_pos_left hsmall hs
    have herr :
        gronwallBound 0 (max K 1)
            (K * ((1 : ℝ) * Real.sqrt (g.inner p w w))) 1 =
          Real.sqrt (g.inner p w w) * gronwallBound 0 (max K 1) K 1 := by
      have heps : K * ((1 : ℝ) * Real.sqrt (g.inner p w w)) =
          Real.sqrt (g.inner p w w) * K := by ring
      rw [heps, gronwallBound_zero_mul_eps]
    rw [herr]
    simpa only [one_mul, mul_one] using hscaled
  have hγ0 : radialCurve (I := I) g p x 0 = p := by
    simp only [radialCurve, zero_smul]
    exact expMap_zero (I := I) g p
  apply covGronwall_ne_zero_at (I := I) g
    (radialCurve (I := I) g p x) hγ hcard F
    (radialJacobiField (I := I) g p x w) hK zero_lt_one
    hpar hON hFdiff (fun t ht => (hreg t ht).1)
    (fun t ht => (hreg t ht).2) hODE
    (radialJacobi_zero (I := I) g p x w) hDJ0
  rw [hγ0]
  exact hsmall'

/-- Curvature control on a raw radial segment makes the differential of the
raw exponential injective at its launch vector. -/
theorem rawExp_mfderiv_inj
    (g : SmoothRiemannianMetric I M) (p : M) (x : E)
    {K R Vb : ℝ}
    (hdom : ∀ t ∈ Icc (0 : ℝ) 1,
      (show TangentSpace I p from t • x) ∈ expDomain (I := I) g p)
    (hK : 0 ≤ K) (hVb : 0 ≤ Vb)
    (hV : ∀ t ∈ Ioo (0 : ℝ) 1,
      Real.sqrt (g.inner (radialCurve (I := I) g p x t)
        (curveVelocity (I := I) (radialCurve (I := I) g p x) t)
        (curveVelocity (I := I) (radialCurve (I := I) g p x) t)) ≤ Vb)
    (hRm : ∀ t ∈ Ioo (0 : ℝ) 1,
      Real.sqrt (Tensor0SBundle.normSq0S (I := I) g
        (radialCurve (I := I) g p x t) 4
        (DifferentialGeometry.Geometry.Curvature.metricRm04At
          (I := I) (M := M) g (radialCurve (I := I) g p x t))) ≤ R)
    (hcoef :
      Real.sqrt ((Fintype.card
        (Fin 1 → Fin (Module.finrank ℝ E)) : ℝ)) * R * Vb ^ 2 ≤ K)
    (hsmall : gronwallBound 0 (max K 1) K 1 < 1) :
    Function.Injective
      (mfderiv 𝓘(ℝ, E) I
        (fun u : E => expMap (I := I) g p
          (show TangentSpace I p from u)) x) := by
  rw [injective_iff_map_eq_zero]
  intro w hzero
  by_contra hw
  have hne := rawJacobi_ne_of_rm (I := I) g p x w hdom hK hVb
    hV hRm hcoef hw hsmall
  apply hne
  rw [radialJacobiField, radial_jacobi_dom (I := I) g p x w]
  · exact hzero
  · simpa only [one_smul] using hdom 1 ⟨zero_le_one, le_rfl⟩

end VolumeComparison
end Riemannian
end Geometry
end DifferentialGeometry

end
