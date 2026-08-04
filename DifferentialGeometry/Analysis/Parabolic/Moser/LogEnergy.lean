import DifferentialGeometry.Analysis.Parabolic.Energy.Caccioppoli
import DifferentialGeometry.Geometry.Operator.LaplacianBridge


noncomputable section

open Bundle Manifold
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.Analysis.Parabolic.Moser

open DifferentialGeometry.Analysis.Laplacian
open DifferentialGeometry.Analysis.Parabolic.Energy
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.DivergenceTheorem

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

variable [I.Boundaryless] [T2Space M]

omit [Module.Finite ℝ E] [IsManifold I ∞ M] [I.Boundaryless] [T2Space M] in
theorem contMDiff_log_of_pos
    {u : ℝ → M → ℝ}
    (hu : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2))
    (hpos : ∀ t x, 0 < u t x) :
    ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => Real.log (u p.1 p.2)) := by
  intro p
  exact (Real.contDiffAt_log.2 (hpos p.1 p.2).ne').comp_contMDiffAt
    (x := p) (hu p)

omit [I.Boundaryless] [T2Space M] in
theorem inner_gradientFun_log_self
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} {x : M}
    (hf : MDifferentiableAt I 𝓘(ℝ, ℝ) f x)
    (hpos : 0 < f x) :
    g.inner x
        (gradientFun (I := I) g (fun y => Real.log (f y)) x)
        (gradientFun (I := I) g (fun y => Real.log (f y)) x) =
      (f x ^ 2)⁻¹ *
        g.inner x
          (gradientFun (I := I) g f x)
          (gradientFun (I := I) g f x) := by
  rw [gradientFun_log (I := I) g hf hpos]
  simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
  field_simp

theorem log_supersolution
    (g : SmoothRiemannianMetric I M)
    (u source : ℝ → M → ℝ)
    (hu : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2))
    (hpos : ∀ t x, 0 < u t x)
    {t : ℝ} {x : M}
    (hpde :
      Δ_g (I := I) g (smoothScalarSlice (I := I) g u hu t).smooth x + source t x ≤
        deriv (fun s => u s x) t) :
    Δ_g (I := I) g
          (smoothScalarSlice (I := I) g (fun s y => Real.log (u s y))
            (contMDiff_log_of_pos hu hpos) t).smooth x +
        g.inner x
          (gradientFun (I := I) g (fun y => Real.log (u t y)) x)
          (gradientFun (I := I) g (fun y => Real.log (u t y)) x) +
        (u t x)⁻¹ * source t x ≤
      deriv (fun s => Real.log (u s x)) t := by
  let ut := smoothScalarSlice (I := I) g u hu t
  let hlog := contMDiff_log_of_pos hu hpos
  let logut := smoothScalarSlice (I := I) g (fun s y => Real.log (u s y)) hlog t
  have htime : ContDiff ℝ ∞ (fun s => u s x) :=
    contMDiff_iff_contDiff.mp (hu.comp (contMDiff_id.prodMk contMDiff_const))
  have htime_deriv :
      deriv (fun s => Real.log (u s x)) t =
        (u t x)⁻¹ * deriv (fun s => u s x) t := by
    exact ((Real.hasDerivAt_log (hpos t x).ne').comp t
      ((htime.differentiable (by norm_num)).differentiableAt.hasDerivAt)).deriv
  have hgrad : MDiffAt
      (T% fun y : M => gradientFun (I := I) g ut.toFun y) x :=
    (grad_g (I := I) g ut.smooth).mdifferentiable x
  have hlap_raw := laplacian_log (I := I)
    (LeviCivita (I := I) g) g
    (fun y => ut.smooth.mdifferentiable (by simp) y)
    (fun y => hpos t y) hgrad
  have hlap :
      Δ_g (I := I) g logut.smooth x =
        (u t x)⁻¹ * Δ_g (I := I) g ut.smooth x -
          (u t x ^ 2)⁻¹ *
            g.inner x
              (gradientFun (I := I) g ut.toFun x)
              (gradientFun (I := I) g ut.toFun x) := by
    rw [← laplacian_levi_eq (I := I) g logut.smooth x,
      ← laplacian_levi_eq (I := I) g ut.smooth x]
    simpa only [ut, logut, smoothScalarSlice_toFun] using hlap_raw
  have hloggrad := inner_gradientFun_log_self (I := I) g
    (ut.smooth.mdifferentiable (by simp) x) (hpos t x)
  have hloggrad' :
      g.inner x
          (gradientFun (I := I) g (fun y => Real.log (u t y)) x)
          (gradientFun (I := I) g (fun y => Real.log (u t y)) x) =
        (u t x ^ 2)⁻¹ *
          g.inner x
            (gradientFun (I := I) g ut.toFun x)
            (gradientFun (I := I) g ut.toFun x) := by
    simpa only [ut, smoothScalarSlice_toFun] using hloggrad
  have hcoeff : 0 ≤ (u t x)⁻¹ := inv_nonneg.mpr (hpos t x).le
  have hmul := mul_le_mul_of_nonneg_left hpde hcoeff
  rw [htime_deriv]
  change Δ_g (I := I) g logut.smooth x +
      g.inner x
        (gradientFun (I := I) g (fun y => Real.log (u t y)) x)
        (gradientFun (I := I) g (fun y => Real.log (u t y)) x) +
      (u t x)⁻¹ * source t x ≤
    (u t x)⁻¹ * deriv (fun s => u s x) t
  rw [hlap, hloggrad']
  convert hmul using 1
  all_goals ring

end DifferentialGeometry.Analysis.Parabolic.Moser

end
