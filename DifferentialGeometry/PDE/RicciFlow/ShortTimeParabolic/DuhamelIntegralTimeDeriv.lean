/-
The local per-mode scalar Duhamel–Leibniz rule: the per-mode convolution is
differentiable at an interior time with derivative `-λ·(conv) + f`. Skeleton stub
for the short-time-existence blueprint (GAP 1, per-mode scalar leaf).
-/
import DifferentialGeometry.PDE.RicciFlow.HamiltonDeTurckPullbackFlat
import DifferentialGeometry.PDE.RicciFlow.Pullback.EvaluationFormChainRule
import DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurckRemainderStrongExists
import DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization.DeTurckGeometricNonlinearity
import DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.EigenCombination
import DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization.TensorHsRealize
import DifferentialGeometry.PDE.RicciFlow.ODE.TimeDependentFlow.ChartLocalPicard
import DifferentialGeometry.PDE.RicciFlow.ODE.TimeDependentFlow.ChartOverlapUniqueness
import DifferentialGeometry.PDE.RicciFlow.ODE.TimeDependentFlow.BareFlowFromJointC1
import DifferentialGeometry.PDE.RicciFlow.ODE.TimeDependentFlow.SmoothInSpace.VariationalLiftFlatIdentity
import DifferentialGeometry.PDE.RicciFlow.ODE.TimeDependentFlow.SmoothDependence.GlobalClosedManifold

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle
open scoped Manifold ContDiff NNReal ENNReal Topology BigOperators
open DifferentialGeometry
open DifferentialGeometry.PDE
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.DeTurck
open DifferentialGeometry.PDE.RicciFlow.ODE
open DifferentialGeometry.PDE.RicciFlow.Pullback
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [BoundarylessManifold I M]
      [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

-- `hlam : 0 ≤ lam` is part of the fixed node signature; the per-mode Leibniz
-- rule below holds for every `lam`, so this sign hypothesis is genuinely unused.
set_option linter.unusedVariables false in
theorem duhamel_integral_time_deriv
    (lam : ℝ) (hlam : 0 ≤ lam) (f : ℝ → ℝ) {T : ℝ}
    (hf : ContinuousOn f (Set.Icc 0 T)) {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    HasDerivAt (fun s : ℝ => perModeConv lam f s)
      (-lam * perModeConv lam f t + f t) t := by
  obtain ⟨ht0, htT⟩ := ht
  -- The kernel `e^{−lam(t−s)}` factors as `e^{−lam·t}·e^{lam·s}`, separating the
  -- time variable out of the integral.  Write `perModeConv lam f` as the product
  -- `e^{−lam·t}·ψ(t)` with `ψ(t) = ∫₀ᵗ e^{lam·s} f(s) ds`.
  set g : ℝ → ℝ := fun s => Real.exp (lam * s) * f s with hg_def
  set ψ : ℝ → ℝ := fun t => ∫ s in (0 : ℝ)..t, g s with hψ_def
  -- `g` is continuous on `[0,T]`: `s ↦ e^{lam·s}` is continuous and `f` is
  -- continuous on `[0,T]`.
  have hg_on : ContinuousOn g (Set.Icc (0 : ℝ) T) :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn.mul hf
  -- `[0,t] ⊆ [0,T]` (since `t < T`), so `g` is interval-integrable on `0..t`.
  have hsub : Set.Icc (0 : ℝ) t ⊆ Set.Icc (0 : ℝ) T :=
    Set.Icc_subset_Icc le_rfl htT.le
  have hg_int : IntervalIntegrable g MeasureTheory.volume 0 t :=
    ContinuousOn.intervalIntegrable_of_Icc ht0.le (hg_on.mono hsub)
  -- `(0,T)` is an open neighbourhood of `t` on which `g` is continuous, hence `g`
  -- is strongly measurable at the filter `𝓝 t` and continuous at `t`.
  have hg_Ioo : ContinuousOn g (Set.Ioo (0 : ℝ) T) :=
    hg_on.mono Set.Ioo_subset_Icc_self
  have ht_Ioo : t ∈ Set.Ioo (0 : ℝ) T := ⟨ht0, htT⟩
  have hg_meas : StronglyMeasurableAtFilter g (𝓝 t) MeasureTheory.volume :=
    hg_Ioo.stronglyMeasurableAtFilter isOpen_Ioo t ht_Ioo
  have hg_at : ContinuousAt g t :=
    hg_Ioo.continuousAt (isOpen_Ioo.mem_nhds ht_Ioo)
  -- Rewrite the per-mode convolution as `e^{−lam·t}·ψ(t)`.
  have hsplit : (fun s : ℝ => perModeConv lam f s)
      = fun t => Real.exp (-(lam * t)) * ψ t := by
    funext u
    rw [perModeConv, hψ_def, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr (fun s _ => ?_)
    have hk : Real.exp (-(lam * (u - s))) = Real.exp (-(lam * u)) * Real.exp (lam * s) := by
      rw [← Real.exp_add]; ring_nf
    rw [hk, hg_def, mul_assoc]
  -- FTC: `ψ'(t) = g t = e^{lam·t} f(t)`.
  have hψ_deriv : HasDerivAt ψ (g t) t :=
    intervalIntegral.integral_hasDerivAt_right hg_int hg_meas hg_at
  -- The prefactor `e^{−lam·t}` is differentiable with derivative `−lam·e^{−lam·t}`.
  have hpre_deriv : HasDerivAt (fun t => Real.exp (-(lam * t)))
      (-lam * Real.exp (-(lam * t))) t := by
    have hbase : HasDerivAt (fun t : ℝ => -(lam * t)) (-lam) t := by
      have h1 : HasDerivAt (fun t : ℝ => lam * t) lam t := by
        simpa using (hasDerivAt_id t).const_mul lam
      simpa using h1.neg
    have hexp := hbase.exp
    simpa [mul_comm] using hexp
  -- Product rule: `(e^{−lam·t}·ψ)' = −lam·e^{−lam·t}·ψ + e^{−lam·t}·g(t)`.
  have hprod : HasDerivAt (fun t => Real.exp (-(lam * t)) * ψ t)
      (-lam * Real.exp (-(lam * t)) * ψ t
        + Real.exp (-(lam * t)) * g t) t :=
    hpre_deriv.mul hψ_deriv
  -- `e^{−lam·t}·e^{lam·t} = 1`, so the derivative collapses to `−lam·φ_λ(t) + f t`.
  have hcancel : Real.exp (-(lam * t)) * Real.exp (lam * t) = 1 := by
    rw [← Real.exp_add]; simp
  have hderiv_eq : -lam * Real.exp (-(lam * t)) * ψ t
        + Real.exp (-(lam * t)) * g t
      = -lam * (Real.exp (-(lam * t)) * ψ t) + f t := by
    have hone : Real.exp (-(lam * t)) * g t = f t := by
      rw [hg_def]; rw [← mul_assoc, hcancel, one_mul]
    rw [hone]; ring
  -- The derivative value `−lam·perModeConv lam f t + f t` also rewrites through
  -- the same factorization `perModeConv lam f t = e^{−lam·t}·ψ(t)`.
  have hval : perModeConv lam f t = Real.exp (-(lam * t)) * ψ t := by
    have := congrFun hsplit t
    simpa using this
  rw [hsplit, hval]
  rw [hderiv_eq] at hprod
  exact hprod

end DifferentialGeometry.PDE.RicciFlow
