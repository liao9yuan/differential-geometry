import DifferentialGeometry.Analysis.Integration.Measure.BasisHaar
import DifferentialGeometry.Geometry.Comparison.Volume.SegmentArea
import DifferentialGeometry.Geometry.Comparison.Volume.SegmentDomain
import DifferentialGeometry.Geometry.Comparison.Volume.SegmentGauss
import DifferentialGeometry.Geometry.Exponential.NormalFrame

set_option autoImplicit false

/-!
# Normal-frame measure normalization for segment comparison

The chart-basis determinant in the exponential Jacobian and the determinant
relating the corresponding basis-normalized Haar measures cancel.  This file
records that simultaneous change of basis and then transports the resulting
integral through the center-metric normal frame.
-/

noncomputable section

open Bundle Function Manifold MeasureTheory Metric Set
open scoped ENNReal Manifold

namespace DifferentialGeometry.Geometry.Riemannian.VolumeComparison

open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Riemannian.NormalCoordinates
open DifferentialGeometry.Geometry.Riemannian.Variation
open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E]
  [InnerProductSpace Real E] [FiniteDimensional Real E]
  [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I (↑(⊤ : ℕ∞) : WithTop ℕ∞) M]

omit [NeZero (Module.finrank Real E)] [I.Boundaryless] in
/-- The center-metric normal frame pulls the `g`-radial ball back to the
canonical model ball. -/
theorem preimage_gBall
    (g : SmoothRiemannianMetric I M) (x : M) (R : Real) :
    (normalFrame (I := I) (E := E) g x) ⁻¹'
        gBall (I := I) g x R =
      ball (0 : E) R := by
  ext w
  simp only [mem_preimage, gBall, mem_setOf_eq, mem_ball, dist_zero_right]
  rw [normalFrame_sqrt]

section Measure

variable [T2Space M] [T2Space (TangentBundle I M)] [SigmaCompactSpace M]
variable [RiemannianBundle (fun x : M => TangentSpace I x)]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩

omit [T2Space (TangentBundle I M)] in
attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- The chart-basis exponential-Jacobian integral equals the normal-basis
Jacobian integral in canonical model coordinates.  The determinant from the
basis change cancels exactly against the determinant relating the two Haar
normalizations. -/
theorem expJac_normal_int
    [ConnectedSpace M] [PseudoEMetricSpace M]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (y : M) (v : TangentSpace I y),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner y v v)))
    (x : M) (K : Set E) :
    (∫⁻ v in K,
        ENNReal.ofReal (expJacDensity (I := I) g hEnorm x v)
        ∂(modelHaar (E := E))) =
      ∫⁻ w in (normalFrame (I := I) (E := E) g x) ⁻¹' K,
        ENNReal.ofReal
          (curveDensity (I := I) g
            (intrinsicGeodesic (I := I) g hEnorm x
              (normalFrame (I := I) (E := E) g x w))
            (fun i t =>
              intrinsicJacobi (I := I) g hEnorm x
                (normalFrame (I := I) (E := E) g x w)
                ((normalBasis (I := I) g x) i) t)
            1)
        ∂(volume : Measure E) := by
  classical
  let b : Module.Basis (Fin (Module.finrank Real E)) Real E :=
    chartModelBasis E
  let b' : Module.Basis (Fin (Module.finrank Real E)) Real E :=
    normalBasis (I := I) g x
  let L : E ≃L[Real] E := normalFrame (I := I) (E := E) g x
  let Dn : E → Real := fun v =>
    curveDensity (I := I) g
      (intrinsicGeodesic (I := I) g hEnorm x v)
      (fun i t => intrinsicJacobi (I := I) g hEnorm x v (b' i) t) 1
  have hD (v : E) :
      ENNReal.ofReal |b.det b'| *
          ENNReal.ofReal (expJacDensity (I := I) g hEnorm x v) =
        ENNReal.ofReal (Dn v) := by
    rw [← ENNReal.ofReal_mul (abs_nonneg (b.det b'))]
    congr 1
    simpa only [b, b', Dn, expJacDensity] using
      (jacDens_basis (I := I) g hEnorm x v b b').symm
  have hbasis :
      (∫⁻ v in K,
          ENNReal.ofReal (expJacDensity (I := I) g hEnorm x v)
          ∂(modelHaar (E := E))) =
        ∫⁻ v in K, ENNReal.ofReal (Dn v) ∂b'.addHaar := by
    calc
      _ = ∫⁻ v in K,
          ENNReal.ofReal (expJacDensity (I := I) g hEnorm x v)
          ∂b.addHaar := by rfl
      _ = ∫⁻ v in K,
          ENNReal.ofReal |b.det b'| *
            ENNReal.ofReal (expJacDensity (I := I) g hEnorm x v)
          ∂b'.addHaar := by
            rw [← Module.Basis.det_smul_addHaar b b',
              setLIntegral_smul_measure]
            exact
              (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).symm
      _ = ∫⁻ v in K, ENNReal.ofReal (Dn v) ∂b'.addHaar := by
            apply lintegral_congr
            exact hD
  have hbmap :
      (stdOrthonormalBasis Real E).toBasis.map L.toLinearEquiv = b' := by
    ext i
    change normalFrame (I := I) (E := E) g x
        ((stdOrthonormalBasis Real E) i) =
      normalBasis (I := I) g x i
    exact normalFrame_basis (I := I) g x i
  have hmap :
      Measure.map L (volume : Measure E) = b'.addHaar := by
    calc
      _ = Measure.map L (stdOrthonormalBasis Real E).toBasis.addHaar := by
            rw [(stdOrthonormalBasis Real E).addHaar_eq_volume]
      _ = ((stdOrthonormalBasis Real E).toBasis.map
          L.toLinearEquiv).addHaar :=
            Module.Basis.map_addHaar _ _
      _ = b'.addHaar := congrArg Module.Basis.addHaar hbmap
  have hmp : MeasurePreserving L (volume : Measure E) b'.addHaar :=
    ⟨L.continuous.measurable, hmap⟩
  rw [hbasis]
  simpa only [Dn, L, b'] using
    (hmp.setLIntegral_comp_preimage_emb
      L.toHomeomorph.toMeasurableEquiv.measurableEmbedding
      (fun v => ENNReal.ofReal (Dn v)) K).symm

end Measure

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison

end
