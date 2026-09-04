import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.ReducedVolume
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.RiemannianTail

set_option autoImplicit false

/-!
# Exterior reduced-density mass bounds

This file combines a quadratic reduced-length lower bound with the intrinsic
Gaussian tail estimate on a complete nonnegatively Ricci-curved time slice.
-/

noncomputable section

open Bundle MeasureTheory Set
open scoped ContDiff ENNReal Manifold Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open DifferentialGeometry.Analysis.Measure
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.BonnetMyers
open DifferentialGeometry.Integral.Measure

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [PseudoMetricSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ℕ∞) : WithTop ℕ∞) M]
  [T2Space M] [T2Space (TangentBundle I M)] [SigmaCompactSpace M]
  [ConnectedSpace M]
variable {D : RealTimeInterval}

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- A quadratic lower bound for reduced length controls the reduced-density
mass outside every intrinsic ball by the explicit Gaussian shell tail. -/
theorem redDensity_tail_le
    (S : SolutionOn (I := I) (M := M) D) (T : Real) (x q : M)
    (tau : Real) (htau : 0 < tau) {decay : Real} (hdecay : 0 < decay)
    (C : Real)
    (hquad : ∀ y : M,
      decay *
          (riemannianEDistOf (I := I)
            (S.base.metric (T - tau)) q y).toReal ^ 2 - C ≤
        redLength S T x y tau)
    (hcomplete : RiemannianMetricComplete (I := I)
      (S.base.metric (T - tau)))
    (hRic : RicciBoundedBelow (I := I)
      (S.base.metric (T - tau)) 0) (N : ℕ) :
    ∫⁻ y in {y : M | (N : Real) ≤
          (riemannianEDistOf (I := I)
            (S.base.metric (T - tau)) q y).toReal},
        ENNReal.ofReal (redDensity S T x y tau)
        ∂riemannianVolumeMeasure (I := I) (M := M)
          (S.base.metric (T - tau)) ≤
      ENNReal.ofReal (Real.exp
        (C - ((Module.finrank Real E : Real) / 2) * Real.log tau -
          ((Module.finrank Real E : Real) / 2) * Real.log (4 * Real.pi))) *
        ((((MeasureTheory.volume : MeasureTheory.Measure
            (EuclideanSpace Real (Fin (Module.finrank Real E)))).toSphere Set.univ) *
          ENNReal.ofReal ((Module.finrank Real E : Real)⁻¹)) *
          gaussTail (Module.finrank Real E) decay N) := by
  let A : Real := Real.exp
    (C - ((Module.finrank Real E : Real) / 2) * Real.log tau -
      ((Module.finrank Real E : Real) / 2) * Real.log (4 * Real.pi))
  let rho : M → Real := fun y ↦
    (riemannianEDistOf (I := I)
      (S.base.metric (T - tau)) q y).toReal
  let tail : Set M := {y | (N : Real) ≤ rho y}
  let mu : Measure M := riemannianVolumeMeasure (I := I) (M := M)
    (S.base.metric (T - tau))
  let G : M → Real := fun y ↦ Real.exp (-decay * rho y ^ 2)
  change (∫⁻ y in tail, ENNReal.ofReal (redDensity S T x y tau) ∂mu) ≤
    ENNReal.ofReal A *
      ((((MeasureTheory.volume : MeasureTheory.Measure
          (EuclideanSpace Real (Fin (Module.finrank Real E)))).toSphere Set.univ) *
        ENNReal.ofReal ((Module.finrank Real E : Real)⁻¹)) *
        gaussTail (Module.finrank Real E) decay N)
  have hcdiv : decay * tau / tau = decay := by
    exact mul_div_cancel_right₀ decay htau.ne'
  have hpoint (y : M) :
      redDensity S T x y tau ≤ A * G y := by
    have hgauss := redDensity_gauss (I := I) S T x q y tau
      (decay * tau) C (by simpa only [hcdiv] using hquad y)
    calc
      redDensity S T x y tau ≤
          Real.exp
            (C - decay *
                (riemannianEDistOf (I := I)
                  (S.base.metric (T - tau)) q y).toReal ^ 2 -
              ((Module.finrank Real E : Real) / 2) * Real.log tau -
              ((Module.finrank Real E : Real) / 2) * Real.log (4 * Real.pi)) := by
        simpa only [hcdiv] using hgauss
      _ = A * G y := by
        dsimp only [A, G, rho]
        rw [← Real.exp_add]
        congr 1
        ring
  have hmono :
      (∫⁻ y in tail, ENNReal.ofReal (redDensity S T x y tau) ∂mu) ≤
        ∫⁻ y in tail, ENNReal.ofReal (A * G y) ∂mu :=
    lintegral_mono fun y ↦ ENNReal.ofReal_le_ofReal (hpoint y)
  have hfactor :
      (∫⁻ y in tail, ENNReal.ofReal (A * G y) ∂mu) =
        ENNReal.ofReal A *
          (∫⁻ y in tail, ENNReal.ofReal (G y) ∂mu) := by
    calc
      (∫⁻ y in tail, ENNReal.ofReal (A * G y) ∂mu) =
          ∫⁻ y in tail, ENNReal.ofReal A * ENNReal.ofReal (G y) ∂mu :=
        lintegral_congr fun y ↦ ENNReal.ofReal_mul (by positivity)
      _ = ENNReal.ofReal A *
          (∫⁻ y in tail, ENNReal.ofReal (G y) ∂mu) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  have htail := riem_gauss_tail (I := I)
    (S.base.metric (T - tau)) hcomplete q hdecay hRic N
  change (∫⁻ y in tail, ENNReal.ofReal (G y) ∂mu) ≤
    (((MeasureTheory.volume : MeasureTheory.Measure
        (EuclideanSpace Real (Fin (Module.finrank Real E)))).toSphere Set.univ) *
      ENNReal.ofReal ((Module.finrank Real E : Real)⁻¹)) *
      gaussTail (Module.finrank Real E) decay N at htail
  calc
    (∫⁻ y in tail, ENNReal.ofReal (redDensity S T x y tau) ∂mu) ≤
        ∫⁻ y in tail, ENNReal.ofReal (A * G y) ∂mu := hmono
    _ = ENNReal.ofReal A *
        (∫⁻ y in tail, ENNReal.ofReal (G y) ∂mu) := hfactor
    _ ≤ ENNReal.ofReal A *
        ((((MeasureTheory.volume : MeasureTheory.Measure
            (EuclideanSpace Real (Fin (Module.finrank Real E)))).toSphere Set.univ) *
          ENNReal.ofReal ((Module.finrank Real E : Real)⁻¹)) *
          gaussTail (Module.finrank Real E) decay N) := by
      simpa only [mul_comm] using mul_le_mul_right htail (ENNReal.ofReal A)

end DifferentialGeometry.PDE.RicciFlow.Perelman
