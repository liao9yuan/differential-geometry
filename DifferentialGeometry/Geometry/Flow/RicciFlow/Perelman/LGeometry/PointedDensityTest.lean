import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.PointedDensityCompact

set_option autoImplicit false

/-!
# Weighted compact-chart convergence of reduced density

This file supplies the analytic single-chart producer for compactly supported
test functions.  It adds a fixed nonnegative weight to the common-coordinate
dominated-convergence argument used for pointed reduced density.
-/

noncomputable section

open Filter MeasureTheory Set
open scoped Topology

namespace DifferentialGeometry.HCGCompactness

open DifferentialGeometry.Integral.Measure

universe uE

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩

/-- A fixed nonnegative bounded test weight preserves compact-chart convergence
of the volume-density times reduced-density product.  This is the local
weighted producer used before changing variables or assembling a finite chart
cover of a compactly supported test function. -/
theorem redDensity_wgt_lim
    {B : Set E} (hBc : IsCompact B)
    {vol red : Nat → E → Real} {volLim redLim : E → Real}
    (w : E → Real)
    (hWMeas : AEMeasurable (fun z ↦ ENNReal.ofReal (w z))
      ((modelHaar (E := E)).restrict B))
    (hVolMeas : ∀ n, AEMeasurable (fun z ↦ ENNReal.ofReal (vol n z))
      ((modelHaar (E := E)).restrict B))
    (hRedMeas : ∀ᶠ n in atTop, AEMeasurable (fun z ↦ ENNReal.ofReal (red n z))
      ((modelHaar (E := E)).restrict B))
    (hVolLim : ∀ z ∈ B, Tendsto (fun n ↦ vol n z) atTop (nhds (volLim z)))
    (hRedLim : ∀ z ∈ B, Tendsto (fun n ↦ red n z) atTop (nhds (redLim z)))
    (Cw Cvol Cred : NNReal)
    (hWBd : ∀ᵐ z ∂((modelHaar (E := E)).restrict B),
      ENNReal.ofReal (w z) ≤ (Cw : ENNReal))
    (hVolBd : ∀ᶠ n in atTop, ∀ᵐ z ∂((modelHaar (E := E)).restrict B),
      ENNReal.ofReal (vol n z) ≤ (Cvol : ENNReal))
    (hRedBd : ∀ᶠ n in atTop, ∀ᵐ z ∂((modelHaar (E := E)).restrict B),
      ENNReal.ofReal (red n z) ≤ (Cred : ENNReal)) :
    Tendsto
      (fun n ↦ ∫⁻ z in B, ENNReal.ofReal (w z) *
        (ENNReal.ofReal (vol n z) * ENNReal.ofReal (red n z))
        ∂(modelHaar (E := E)))
      atTop
      (nhds (∫⁻ z in B, ENNReal.ofReal (w z) *
        (ENNReal.ofReal (volLim z) * ENNReal.ofReal (redLim z))
        ∂(modelHaar (E := E)))) := by
  let μ : Measure E := (modelHaar (E := E)).restrict B
  let F : Nat → E → ENNReal := fun n z ↦
    ENNReal.ofReal (w z) * (ENNReal.ofReal (vol n z) * ENNReal.ofReal (red n z))
  let f : E → ENNReal := fun z ↦
    ENNReal.ofReal (w z) * (ENNReal.ofReal (volLim z) * ENNReal.ofReal (redLim z))
  let C : E → ENNReal := fun _ ↦
    (Cw : ENNReal) * ((Cvol : ENNReal) * (Cred : ENNReal))
  have hFMeas : ∀ᶠ n in atTop, AEMeasurable (F n) μ := by
    filter_upwards [hRedMeas] with n hn
    simpa only [F, μ] using hWMeas.mul ((hVolMeas n).mul hn)
  have hBound : ∀ᶠ n in atTop, F n ≤ᵐ[μ] C := by
    filter_upwards [hVolBd, hRedBd] with n hnVol hnRed
    filter_upwards [hWBd, hnVol, hnRed] with z hzW hzVol hzRed
    exact mul_le_mul' hzW (mul_le_mul' hzVol hzRed)
  have hFin : ∫⁻ z, C z ∂μ ≠ ⊤ := by
    rw [lintegral_const]
    apply ENNReal.mul_ne_top
    · exact ENNReal.mul_ne_top (by simp) (ENNReal.mul_ne_top (by simp) (by simp))
    · simpa only [μ, Measure.restrict_apply_univ] using hBc.measure_lt_top.ne
  have hMem : ∀ᵐ z ∂μ, z ∈ B := by
    simpa only [μ] using ae_restrict_mem hBc.measurableSet
  have hLim : ∀ᵐ z ∂μ, Tendsto (fun n ↦ F n z) atTop (nhds (f z)) := by
    filter_upwards [hMem] with z hz
    apply ENNReal.Tendsto.mul
    · exact tendsto_const_nhds
    · exact Or.inr (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
    · apply ENNReal.Tendsto.mul
      · exact (ENNReal.continuous_ofReal.tendsto _).comp (hVolLim z hz)
      · exact Or.inr ENNReal.ofReal_ne_top
      · exact (ENNReal.continuous_ofReal.tendsto _).comp (hRedLim z hz)
      · exact Or.inr ENNReal.ofReal_ne_top
    · exact Or.inr ENNReal.ofReal_ne_top
  have hReady := hFMeas.and hBound
  rw [eventually_atTop] at hReady
  obtain ⟨N, hN⟩ := hReady
  have hShiftLim : ∀ᵐ z ∂μ,
      Tendsto (fun n ↦ F (n + N) z) atTop (nhds (f z)) :=
    hLim.mono fun _ hz ↦ hz.comp (tendsto_add_atTop_nat N)
  have hShift := tendsto_lintegral_of_dominated_convergence' C
    (fun n ↦ (hN (n + N) (Nat.le_add_left N n)).1)
    (fun n ↦ (hN (n + N) (Nat.le_add_left N n)).2)
    hFin hShiftLim
  have hOrig : Tendsto (fun n ↦ ∫⁻ z, F n z ∂μ) atTop
      (nhds (∫⁻ z, f z ∂μ)) :=
    (tendsto_add_atTop_iff_nat N).1 hShift
  simpa only [F, f, C, μ] using hOrig

end DifferentialGeometry.HCGCompactness
