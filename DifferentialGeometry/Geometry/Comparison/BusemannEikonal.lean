import DifferentialGeometry.Analysis.Calculus.CurveDerivative
import DifferentialGeometry.Analysis.Elliptic.MetricBounds
import DifferentialGeometry.Geometry.Comparison.BusemannAsymptotic
import DifferentialGeometry.Geometry.Metric.LipschitzGradient

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set
open scoped ENNReal Manifold Topology

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian

open DifferentialGeometry.Geometry.Operator
open Exponential

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ℕ∞) : WithTop ℕ∞) M]
  [T2Space M] [T2Space (TangentBundle I M)] [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
omit [T2Space (TangentBundle I M)] in
/-- Wherever the Busemann function of a supplied minimizing ray is
differentiable, its metric gradient has unit squared norm. -/
theorem busemann_grad_sq
    [ConnectedSpace M]
    [RiemannianBundle (fun z : M => TangentSpace I z)]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun z : M => TangentSpace I z)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    {p : M} {gamma : Real → M}
    (hgamma : IsMinimizingRay (I := I) g p gamma) (x : M)
    (hB : MDifferentiableAt I 𝓘(Real, Real)
      (busemann (I := I) gamma) x) :
    g.inner x
        (gradientFun (I := I) g (busemann (I := I) gamma) x)
        (gradientFun (I := I) g (busemann (I := I) gamma) x) = 1 := by
  classical
  let b : M → Real := busemann (I := I) gamma
  change MDifferentiableAt I 𝓘(Real, Real) b x at hB
  obtain ⟨u, hu, hdata⟩ :=
    exists_asymp_ray (I := I) g hEnorm hgamma x
  let sigma : Real → M := fun t ↦
    expMapIntrinsic (I := I) g hEnorm x (t • u)
  change IsMinimizingRay (I := I) g x sigma ∧
    (∀ (t : Real), 0 ≤ t → ∀ y : M,
      b y ≤ (riemannianEDist I (sigma t) y).toReal - t + b x) at hdata
  rcases hdata with ⟨hsigma, hsupport⟩
  have hsigma_zero : sigma 0 = x := hsigma.start_eq
  have hb_sigma : ∀ {t : Real}, 0 ≤ t →
      b (sigma t) = b x - t := by
    intro t ht
    have hupper := hsupport t ht (sigma t)
    have hlower := busemann_sub_le (I := I) hgamma x (sigma t)
    have hdist : (riemannianEDist I x (sigma t)).toReal = t := by
      rw [← hsigma_zero, hsigma.edist_eq (le_refl 0) ht, sub_zero,
        ENNReal.toReal_ofReal ht]
    simp only [riemannianEDist_self, ENNReal.toReal_zero, zero_sub] at hupper
    rw [hdist] at hlower
    linarith
  have hsigma_eq :
      sigma = intrinsicGeodesic (I := I) g hEnorm x u := by
    funext t
    simpa only [sigma, expMapIntrinsic_def] using
      intrinsicGeodesic_smul (I := I) g hEnorm x u t
  have hsigma_md : MDifferentiableAt 𝓘(Real, Real) I sigma 0 := by
    rw [hsigma_eq]
    exact (intrinsicGeodesic_contMDiff (I := I) g hEnorm x u).contMDiffAt
      |>.mdifferentiableAt (by simp)
  have hsigma_deriv :
      (mfderiv 𝓘(Real, Real) I sigma 0 (1 : Real) : E) = (u : E) := by
    rw [hsigma_eq]
    exact intrinsicGeodesic_mfderiv_zero (I := I) g hEnorm x u
  have hB_zero : MDifferentiableAt I 𝓘(Real, Real) b (sigma 0) := by
    simpa only [hsigma_zero] using hB
  let q : Real :=
    NormedSpace.fromTangentSpace (b (sigma 0))
      (mfderiv I 𝓘(Real, Real) b (sigma 0)
        (mfderiv 𝓘(Real, Real) I sigma 0 (1 : Real)))
  have hcurve : HasDerivAt (fun t : Real ↦ b (sigma t)) q 0 := by
    simpa only [q] using
      DifferentialGeometry.Analysis.Calculus.hasDerivAt_comp_mfderiv_along
        I b sigma 0 hB_zero hsigma_md
  have hlinear : HasDerivWithinAt (fun t : Real ↦ b x - t) (-1)
      (Ici 0) 0 := by
    simpa using
      ((hasDerivAt_const (x := (0 : Real)) (c := b x)).sub
        (hasDerivAt_id (x := (0 : Real)))).hasDerivWithinAt
  have hcurve_neg : HasDerivWithinAt (fun t : Real ↦ b (sigma t)) (-1)
      (Ici 0) 0 := by
    refine hlinear.congr ?_ ?_
    · intro t ht
      exact hb_sigma ht
    · exact hb_sigma (le_refl 0)
  have hq : q = -1 :=
    UniqueDiffWithinAt.eq_deriv (Ici (0 : Real))
      (uniqueDiffWithinAt_Ici (0 : Real)) hcurve.hasDerivWithinAt hcurve_neg
  have hq_inner :
      q = g.inner x (gradientFun (I := I) g b x) u := by
    dsimp only [q]
    rw [hsigma_zero]
    change mfderiv I 𝓘(Real, Real) b x
        (mfderiv 𝓘(Real, Real) I sigma 0 (1 : Real)) = _
    rw [hsigma_deriv]
    exact (inner_gradientFun (I := I) g b x u).symm
  have hpair : g.inner x (gradientFun (I := I) g b x) u = -1 := by
    rw [← hq_inner]
    exact hq
  have hb_lip : ∀ y z, edist (b y) (b z) ≤
      (1 : ENNReal) * riemannianEDistOf (I := I) g y z := by
    intro y z
    dsimp only [b]
    rw [one_mul, riemannianEDistOf_eq_riemannianEDist
      (I := I) g hEnorm, edist_dist, Real.dist_eq]
    rw [← ENNReal.ofReal_toReal
      (riemannianEDist_ne_top (I := I) y z)]
    exact ENNReal.ofReal_le_ofReal (busemann_dist (I := I) hgamma y z)
  have hupper : Real.sqrt
      (g.inner x (gradientFun (I := I) g b x)
        (gradientFun (I := I) g b x)) ≤ 1 := by
    simpa only [gradFun, gradientFun, NNReal.coe_one] using
      grad_norm_le_lip (I := I) g hb_lip hB
  let v : TangentSpace I x := gradientFun (I := I) g b x
  have hcs : |g.inner x v u| ≤
      Real.sqrt (g.inner x v v) * Real.sqrt (g.inner x u u) := by
    exact
      DifferentialGeometry.Analysis.Laplacian.abs_metric_inner_le_sqrt_metric_quadratic
        (I := I) (M := M) g x v u
  have hlower : 1 ≤ Real.sqrt (g.inner x v v) := by
    rw [show g.inner x v u = -1 by simpa only [v] using hpair,
      abs_neg, abs_one, hu, Real.sqrt_one, mul_one] at hcs
    exact hcs
  have hsqrt : Real.sqrt (g.inner x v v) = 1 :=
    le_antisymm (by simpa only [v] using hupper) hlower
  have hnonneg : 0 ≤ g.inner x v v :=
    DifferentialGeometry.Analysis.Laplacian.metric_inner_self_nonneg
      (I := I) (M := M) g x v
  change g.inner x v v = 1
  rw [← Real.sq_sqrt hnonneg, hsqrt, one_pow]

end Riemannian
end Geometry
end DifferentialGeometry
