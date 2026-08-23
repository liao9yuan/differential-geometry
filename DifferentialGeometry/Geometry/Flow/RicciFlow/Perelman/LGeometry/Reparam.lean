import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Defs
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

set_option autoImplicit false

/-!
# Square-root reparameterization of Perelman L-length

This file reparameterizes a backward-time curve by `tau = s ^ 2`.  It records
the velocity chain rule and the resulting regularized `s`-energy formula.
-/

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open DifferentialGeometry.Geometry.Curvature
open Bundle MeasureTheory Set
open scoped Manifold ContDiff Topology

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
variable {D : RealTimeInterval}

/-- A curve reparameterized by backward square time `tau = s ^ 2`. -/
def sqReparam (gamma : Real -> M) (s : Real) : M :=
  gamma (s ^ 2)

/-- A square-root-time curve read as a backward-time curve. -/
def sqrtReparam (alpha : Real → M) (tau : Real) : M :=
  alpha (Real.sqrt tau)

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- The velocity of the square-time reparameterization is
`2 s` times the original backward-time velocity. -/
theorem lVelocity_sq
    [IsManifold I 1 M]
    (gamma : Real -> M) (s : Real)
    (hgamma : MDifferentiableAt 𝓘(Real, Real) I gamma (s ^ 2))
    :
    lVelocity (I := I) (sqReparam gamma) s =
      (2 * s) • lVelocity (I := I) gamma (s ^ 2) := by
  have hsqAt : MDifferentiableAt 𝓘(Real, Real) 𝓘(Real, Real)
      (fun x : Real => x ^ 2) s :=
    mdifferentiableAt_iff_differentiableAt.mpr (differentiableAt_id.pow 2)
  have hchain := mfderiv_comp
    (I := 𝓘(Real, Real)) (I' := 𝓘(Real, Real)) (I'' := I)
    (f := fun x : Real => x ^ 2) (g := gamma) s hgamma hsqAt
  have hsq :
      (mfderiv 𝓘(Real, Real) 𝓘(Real, Real)
        (fun x : Real => x ^ 2) s) (1 : Real) = 2 * s := by
    rw [mfderiv_eq_fderiv]
    change deriv (fun x : Real => x ^ 2) s = 2 * s
    rw [deriv_pow_field]
    norm_num
  calc
    lVelocity (I := I) (sqReparam gamma) s =
        (mfderiv 𝓘(Real, Real) I gamma (s ^ 2))
          ((mfderiv 𝓘(Real, Real) 𝓘(Real, Real)
            (fun x : Real => x ^ 2) s) (1 : Real)) := by
      simpa only [lVelocity, sqReparam, Function.comp_apply] using
        congrArg (fun L => L (1 : Real)) hchain
    _ = (mfderiv 𝓘(Real, Real) I gamma (s ^ 2)) (2 * s) := by rw [hsq]
    _ = (mfderiv 𝓘(Real, Real) I gamma (s ^ 2))
          ((2 * s) • (1 : Real)) := by
      congr 1
      rw [smul_eq_mul, mul_one]
      rfl
    _ = (2 * s) • lVelocity (I := I) gamma (s ^ 2) := by
      simpa only [lVelocity] using
        (mfderiv 𝓘(Real, Real) I gamma (s ^ 2)).map_smul
          (2 * s) (1 : Real)

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- At positive square-root time the square-reparameterization velocity
formula holds even when manifold derivatives take their default zero value. -/
theorem lVelocity_sq_pos
    [IsManifold I 1 M]
    (gamma : Real → M) (s : Real) (hs : 0 < s) :
    lVelocity (I := I) (sqReparam gamma) s =
      (2 * s) • lVelocity (I := I) gamma (s ^ 2) := by
  by_cases hgamma : MDifferentiableAt 𝓘(Real, Real) I gamma (s ^ 2)
  · exact lVelocity_sq (I := I) gamma s hgamma
  · have hs2 : 0 < s ^ 2 := sq_pos_of_pos hs
    have halpha : ¬ MDifferentiableAt 𝓘(Real, Real) I
        (sqReparam gamma) s := by
      intro halpha
      have hsqrt : Real.sqrt (s ^ 2) = s := Real.sqrt_sq hs.le
      have hsqrtDiff : MDifferentiableAt 𝓘(Real, Real) 𝓘(Real, Real)
          Real.sqrt (s ^ 2) :=
        mdifferentiableAt_iff_differentiableAt.mpr
          (Real.hasDerivAt_sqrt (ne_of_gt hs2)).differentiableAt
      have halpha' : MDifferentiableAt 𝓘(Real, Real) I
          (sqReparam gamma) (Real.sqrt (s ^ 2)) := by
        simpa only [hsqrt] using halpha
      have hcomp : MDifferentiableAt 𝓘(Real, Real) I
          (sqReparam gamma ∘ Real.sqrt) (s ^ 2) :=
        halpha'.comp (s ^ 2) hsqrtDiff
      have heq : (sqReparam gamma ∘ Real.sqrt) =ᶠ[𝓝 (s ^ 2)] gamma := by
        filter_upwards [eventually_gt_nhds hs2] with r hr
        simp only [Function.comp_apply, sqReparam, Real.sq_sqrt hr.le]
      exact hgamma (hcomp.congr_of_eventuallyEq heq.symm)
    simp only [lVelocity,
      mfderiv_zero_of_not_mdifferentiableAt halpha,
      mfderiv_zero_of_not_mdifferentiableAt hgamma,
      ContinuousLinearMap.zero_apply, smul_zero]
    rfl

variable [IsManifold I ∞ M] [FiniteDimensional Real E]
variable [IsManifold I 1 M]
variable [T2Space M] [SigmaCompactSpace M]

/-- The regularized `s`-density after the substitution `tau = s ^ 2`. -/
noncomputable def lRegDensity
    (S : SolutionOn (I := I) (M := M) D) (T : Real) (gamma : Real -> M)
    (s : Real) : Real :=
  (1 / 2 : Real) *
      (S.base.metric (T - s ^ 2)).inner (sqReparam gamma s)
        (lVelocity (I := I) (sqReparam gamma) s)
        (lVelocity (I := I) (sqReparam gamma) s) +
    2 * s ^ 2 * S.scalar (T - s ^ 2) (sqReparam gamma s)

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
omit [T2Space M] [SigmaCompactSpace M] in
/-- On nonnegative square-root time, the substituted L-density agrees with
the regularized `s`-density. -/
theorem lDensity_sq
    (S : SolutionOn (I := I) (M := M) D) (T : Real) (gamma : Real -> M)
    (s : Real)
    (hgamma : MDifferentiableAt 𝓘(Real, Real) I gamma (s ^ 2))
    (hs : 0 <= s) :
    lDensity S T gamma (s ^ 2) * (2 * s) = lRegDensity S T gamma s := by
  let g := S.base.metric (T - s ^ 2)
  let p := gamma (s ^ 2)
  let v := lVelocity (I := I) gamma (s ^ 2)
  have hfirst : (g.inner p) ((2 * s) • v) = (2 * s) • (g.inner p) v :=
    (g.inner p).map_smul (2 * s) v
  have hsecond : (g.inner p v) ((2 * s) • v) =
      (2 * s) • (g.inner p v) v :=
    (g.inner p v).map_smul (2 * s) v
  have hquad : g.inner p ((2 * s) • v) ((2 * s) • v) =
      (2 * s) ^ 2 * g.inner p v v := by
    calc
      g.inner p ((2 * s) • v) ((2 * s) • v) =
          ((2 * s) • (g.inner p v)) ((2 * s) • v) :=
        congrArg (fun L => L ((2 * s) • v)) hfirst
      _ = (2 * s) * ((2 * s) * g.inner p v v) := by
        rw [ContinuousLinearMap.smul_apply, hsecond, smul_eq_mul, smul_eq_mul]
      _ = (2 * s) ^ 2 * g.inner p v v := by ring
  have hquad' : (S.base.metric (T - s ^ 2)).inner (gamma (s ^ 2))
      ((2 * s) • lVelocity (I := I) gamma (s ^ 2))
      ((2 * s) • lVelocity (I := I) gamma (s ^ 2)) =
      (2 * s) ^ 2 * (S.base.metric (T - s ^ 2)).inner (gamma (s ^ 2))
        (lVelocity (I := I) gamma (s ^ 2))
        (lVelocity (I := I) gamma (s ^ 2)) := by
    simpa only [g, p, v] using hquad
  rw [lRegDensity, lDensity, lSpeedSq, Real.sqrt_sq hs,
    lVelocity_sq gamma s hgamma]
  simp only [sqReparam]
  calc
    _ = (1 / 2 : Real) * ((2 * s) ^ 2 *
          (S.base.metric (T - s ^ 2)).inner (gamma (s ^ 2))
            (lVelocity (I := I) gamma (s ^ 2))
            (lVelocity (I := I) gamma (s ^ 2))) +
        2 * s ^ 2 * S.scalar (T - s ^ 2) (gamma (s ^ 2)) := by ring
    _ = _ := by
      exact congrArg
        (fun z : Real => (1 / 2 : Real) * z +
          2 * s ^ 2 * S.scalar (T - s ^ 2) (gamma (s ^ 2))) hquad'.symm

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
omit [T2Space M] [SigmaCompactSpace M] in
/-- At positive square-root time the substituted density identity holds for
every raw curve, using the totalized manifold derivative in both parameters. -/
theorem lDensity_sq_pos
    (S : SolutionOn (I := I) (M := M) D) (T : Real) (gamma : Real → M)
    (s : Real) (hs : 0 < s) :
    lDensity S T gamma (s ^ 2) * (2 * s) =
      lRegDensity S T gamma s := by
  by_cases hgamma : MDifferentiableAt 𝓘(Real, Real) I gamma (s ^ 2)
  · exact lDensity_sq S T gamma s hgamma hs.le
  · have hvel : lVelocity (I := I) gamma (s ^ 2) = 0 := by
      simp only [lVelocity, mfderiv_zero_of_not_mdifferentiableAt hgamma,
        ContinuousLinearMap.zero_apply]
    have hvelsq : lVelocity (I := I) (sqReparam gamma) s = 0 := by
      simpa only [hvel, smul_zero] using
        lVelocity_sq_pos (I := I) gamma s hs
    have hspeed0 : lSpeedSq S T gamma (s ^ 2) = 0 := by
      simp [lSpeedSq, hvel]
    have hreg0 :
        (S.base.metric (T - s ^ 2)).inner (sqReparam gamma s)
          (lVelocity (I := I) (sqReparam gamma) s)
          (lVelocity (I := I) (sqReparam gamma) s) = 0 := by
      simp [hvelsq]
    rw [lDensity, lRegDensity, Real.sqrt_sq hs.le, hspeed0, hreg0]
    simp only [sqReparam]
    ring

omit [T2Space M] [SigmaCompactSpace M] in
/-- Perelman L-length is the regularized energy after the monotone substitution
`tau = s ^ 2`. -/
theorem lLength_sq
    (S : SolutionOn (I := I) (M := M) D) (T : Real) (gamma : Real -> M)
    (tau1 tau2 : Real) (htau1 : 0 <= tau1) (htau2 : 0 <= tau2)
    (hgamma : ∀ s ∈ uIcc (Real.sqrt tau1) (Real.sqrt tau2),
      MDifferentiableAt 𝓘(Real, Real) I gamma (s ^ 2)) :
    lLength S T gamma tau1 tau2 =
      ∫ s in Real.sqrt tau1..Real.sqrt tau2, lRegDensity S T gamma s := by
  have hsub :=
    intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
      (g := lDensity S T gamma) (f := fun s : Real => s ^ 2)
      (f' := fun s : Real => 2 * s)
      (a := Real.sqrt tau1) (b := Real.sqrt tau2)
      (continuous_id.pow 2).continuousOn
      (by
        intro s hs
        simpa using hasDerivAt_pow 2 s)
      (by
        intro s hs
        have hmin : 0 <= min (Real.sqrt tau1) (Real.sqrt tau2) :=
          le_min (Real.sqrt_nonneg tau1) (Real.sqrt_nonneg tau2)
        exact mul_nonneg (by norm_num) (hmin.trans hs.1.le))
  have hsub' :
      (∫ s in Real.sqrt tau1..Real.sqrt tau2,
        (lDensity S T gamma ∘ fun r : Real => r ^ 2) s * (2 * s)) =
        ∫ tau in tau1..tau2, lDensity S T gamma tau := by
    simpa only [Real.sq_sqrt htau1, Real.sq_sqrt htau2] using hsub
  have hcongr :
      (∫ s in Real.sqrt tau1..Real.sqrt tau2,
        (lDensity S T gamma ∘ fun r : Real => r ^ 2) s * (2 * s)) =
        ∫ s in Real.sqrt tau1..Real.sqrt tau2, lRegDensity S T gamma s := by
    apply intervalIntegral.integral_congr
    intro s hs
    have hs0 : 0 <= s := by
      rcases mem_uIcc.mp hs with hs | hs
      · exact (Real.sqrt_nonneg tau1).trans hs.1
      · exact (Real.sqrt_nonneg tau2).trans hs.1
    simpa only [Function.comp_apply] using
      lDensity_sq S T gamma s (hgamma s hs) hs0
  simpa only [lLength] using hsub'.symm.trans hcongr

omit [T2Space M] [SigmaCompactSpace M] in
/-- Perelman L-length obeys the square-root change of variables for every raw
curve; the possible failure of the pointwise identity at zero is negligible. -/
theorem lLength_sq_ae
    (S : SolutionOn (I := I) (M := M) D) (T : Real) (gamma : Real → M)
    (tau1 tau2 : Real) (htau1 : 0 ≤ tau1) (htau2 : 0 ≤ tau2) :
    lLength S T gamma tau1 tau2 =
      ∫ s in Real.sqrt tau1..Real.sqrt tau2, lRegDensity S T gamma s := by
  have hsub :=
    intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
      (g := lDensity S T gamma) (f := fun s : Real => s ^ 2)
      (f' := fun s : Real => 2 * s)
      (a := Real.sqrt tau1) (b := Real.sqrt tau2)
      (continuous_id.pow 2).continuousOn
      (by
        intro s _
        simpa using hasDerivAt_pow 2 s)
      (by
        intro s hs
        have hmin : 0 ≤ min (Real.sqrt tau1) (Real.sqrt tau2) :=
          le_min (Real.sqrt_nonneg tau1) (Real.sqrt_nonneg tau2)
        exact mul_nonneg (by norm_num) (hmin.trans hs.1.le))
  have hsub' :
      (∫ s in Real.sqrt tau1..Real.sqrt tau2,
        (lDensity S T gamma ∘ fun r : Real => r ^ 2) s * (2 * s)) =
        ∫ tau in tau1..tau2, lDensity S T gamma tau := by
    simpa only [Real.sq_sqrt htau1, Real.sq_sqrt htau2] using hsub
  have hcongr :
      (∫ s in Real.sqrt tau1..Real.sqrt tau2,
        (lDensity S T gamma ∘ fun r : Real => r ^ 2) s * (2 * s)) =
        ∫ s in Real.sqrt tau1..Real.sqrt tau2, lRegDensity S T gamma s := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards
      [MeasureTheory.Measure.ae_ne MeasureTheory.volume (0 : Real)]
        with s hs0 hsmem
    have hsu := Set.uIoc_subset_uIcc hsmem
    have hsnonneg : 0 ≤ s := by
      rcases Set.mem_uIcc.mp hsu with hs | hs
      · exact (Real.sqrt_nonneg tau1).trans hs.1
      · exact (Real.sqrt_nonneg tau2).trans hs.1
    have hspos : 0 < s := lt_of_le_of_ne hsnonneg hs0.symm
    simpa only [Function.comp_apply] using
      lDensity_sq_pos (I := I) S T gamma s hspos
  simpa only [lLength] using hsub'.symm.trans hcongr

end DifferentialGeometry.PDE.RicciFlow.Perelman
