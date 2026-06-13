import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.MapConvergence
import Mathlib.Analysis.Calculus.ContDiff.Bounds

set_option autoImplicit false
set_option linter.style.longLine false

/-!
# Derivative-closure for `MapCInfConvOnCompacts` (Euclidean analysis layer)

`MapCInfConvOnCompacts U Φ Φinf` retains the FULL Fréchet-derivative data of the
MSM135 `C^∞`-convergence definition: `mapDerivNorm r Φₖ Φinf = ‖∇ʳ(Φₖ - Φ_∞)‖`
is controlled uniformly on compacts for every order `r`.  Hence the notion is
closed under taking a directional derivative: if `Φₖ → Φ_∞` in `C^∞`-on-compacts
(with all maps `C^∞`), then

  `z ↦ fderiv ℝ (Φₖ) z v  →  z ↦ fderiv ℝ Φ_∞ z v`

again in `C^∞`-on-compacts.  This is the analytic producer the covariant-tower
bridge `componentConv_covDeriv_of_chartCInf` (Gap B, order `a ≥ 1`) needs to push
the order-0 chart-component convergence through one covariant-derivative step
(`fderiv … v` is the coordinate directional derivative entering
`nabla0SFun_two_eval_coordFrame`).

This file is `MapConvergence.lean`-adjacent Euclidean analysis (no manifold
content).  It lives here rather than in `MapConvergence.lean` only because that
file is currently owned by another session.
-/

namespace DifferentialGeometry
namespace HCGCompactness

open Filter Topology
open scoped ContDiff

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Pointwise bound: the order-`r` Euclidean derivative norm of the difference of
directional derivatives `z ↦ fderiv ℝ (·) z v` is `≤ ‖v‖` times the order-`(r+1)`
derivative norm of the difference of the maps.  (`fderiv` is linear, so the
difference of directional derivatives is the directional derivative of the
difference; then `clm_apply_const` peels off `· v` and `norm_iteratedFDeriv_fderiv`
raises the order by one.) -/
theorem mapDerivNorm_fderivApply_le (r : ℕ) (v : E) {Φk Φinf : E → F} {x : E}
    (hk : ContDiff ℝ (∞ : WithTop ℕ∞) Φk) (hinf : ContDiff ℝ (∞ : WithTop ℕ∞) Φinf) :
    mapDerivNorm r (fun z => fderiv ℝ Φk z v) (fun z => fderiv ℝ Φinf z v) x
      ≤ ‖v‖ * mapDerivNorm (r + 1) Φk Φinf x := by
  have hfun : (fun z => fderiv ℝ Φk z v - fderiv ℝ Φinf z v)
      = (fun z => fderiv ℝ (fun y => Φk y - Φinf y) z v) := by
    funext z
    have hd : fderiv ℝ (fun y => Φk y - Φinf y) z = fderiv ℝ Φk z - fderiv ℝ Φinf z :=
      fderiv_sub (hk.differentiable (by simp)).differentiableAt
        (hinf.differentiable (by simp)).differentiableAt
    rw [hd, ContinuousLinearMap.sub_apply]
  rw [mapDerivNorm, hfun]
  set g : E → F := fun y => Φk y - Φinf y with hg
  have hgcd : ContDiff ℝ (∞ : WithTop ℕ∞) g := hk.sub hinf
  have hfd : ContDiffAt ℝ (r : WithTop ℕ∞) (fderiv ℝ g) x :=
    (hgcd.fderiv_right (m := (r : WithTop ℕ∞)) (by exact_mod_cast le_top)).contDiffAt
  calc ‖iteratedFDeriv ℝ r (fun z => fderiv ℝ g z v) x‖
      ≤ ‖v‖ * ‖iteratedFDeriv ℝ r (fderiv ℝ g) x‖ :=
        norm_iteratedFDeriv_clm_apply_const hfd le_rfl
    _ = ‖v‖ * ‖iteratedFDeriv ℝ (r + 1) g x‖ := by rw [norm_iteratedFDeriv_fderiv]
    _ = ‖v‖ * mapDerivNorm (r + 1) Φk Φinf x := by rw [mapDerivNorm, hg]

/-- **Derivative-closure of `C^∞`-on-compacts convergence.**  If `Φₖ → Φ_∞` in
`C^∞`-on-compacts on `U` (all maps `C^∞`), then the directional derivatives
`z ↦ fderiv ℝ (Φₖ) z v` converge to `z ↦ fderiv ℝ Φ_∞ z v` in `C^∞`-on-compacts.
At order `p`/`K` it consumes the order-`(p+1)` content of the hypothesis. -/
theorem MapCInfConvOnCompacts.fderivApply {U : Set E} {Φ : ℕ → E → F} {Φinf : E → F}
    (h : MapCInfConvOnCompacts U Φ Φinf)
    (hΦ : ∀ k, ContDiff ℝ (∞ : WithTop ℕ∞) (Φ k))
    (hΦinf : ContDiff ℝ (∞ : WithTop ℕ∞) Φinf) (v : E) :
    MapCInfConvOnCompacts U (fun k z => fderiv ℝ (Φ k) z v) (fun z => fderiv ℝ Φinf z v) := by
  intro K hK hKU p ε hε
  obtain ⟨k0, hk0⟩ := h K hK hKU (p + 1) (ε / (‖v‖ + 1)) (by positivity)
  refine ⟨k0, fun k hk r hr x hx => ?_⟩
  calc mapDerivNorm r (fun z => fderiv ℝ (Φ k) z v) (fun z => fderiv ℝ Φinf z v) x
      ≤ ‖v‖ * mapDerivNorm (r + 1) (Φ k) Φinf x :=
        mapDerivNorm_fderivApply_le r v (hΦ k) hΦinf
    _ ≤ ‖v‖ * (ε / (‖v‖ + 1)) := by
        gcongr
        exact hk0 k hk (r + 1) (by omega) x hx
    _ ≤ ε := by
        rw [← mul_div_assoc, div_le_iff₀ (by positivity : (0:ℝ) < ‖v‖ + 1)]
        nlinarith [norm_nonneg v, hε.le]

end HCGCompactness
end DifferentialGeometry
