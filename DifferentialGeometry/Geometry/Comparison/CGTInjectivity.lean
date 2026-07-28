import DifferentialGeometry.Geometry.Comparison.IntrinsicInjectivityRadius
import DifferentialGeometry.Geometry.Comparison.Volume.BishopBall
import DifferentialGeometry.Geometry.Comparison.Volume.BallVolume
import DifferentialGeometry.Geometry.Comparison.Volume.SegmentFrameBound
import DifferentialGeometry.Geometry.Comparison.Volume.SegmentMeasure

set_option autoImplicit false

/-!
# Cheeger--Gromov--Taylor injectivity estimates

This file separates the analytic and topological parts of the
Cheeger--Gromov--Taylor injectivity-radius estimate.  `intrPullVol` is the
Riemannian pullback volume of an intrinsic framed tangent ball.  The first
result bounds it by the hyperbolic model whenever the radial exponential has
no conjugate vectors.

The remaining theorem in this layer is the original geodesic-loop
collision/overlap estimate.  Its injectivity-radius corollary belongs after the
separate local collision-to-loop lemma.
-/

noncomputable section

open Bundle Function Manifold MeasureTheory Metric Set
open scoped ENNReal Manifold

namespace DifferentialGeometry.Geometry.Riemannian.VolumeComparison

open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Riemannian.NormalCoordinates
open DifferentialGeometry.Geometry.Riemannian.Variation
open DifferentialGeometry.Geometry.Riemannian.BonnetMyers
open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E]
  [InnerProductSpace Real E] [FiniteDimensional Real E]
  [CompleteSpace E] [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I (↑(⊤ : ℕ∞) : WithTop ℕ∞) M]
  [T2Space M] [T2Space (TangentBundle I M)]
  [SigmaCompactSpace M] [ConnectedSpace M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace

variable [RiemannianBundle (fun x : M => TangentSpace I x)]
variable [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

/-- Pullback Riemannian volume of the radius-`R` model ball under the complete
intrinsic framed exponential at `p`. -/
noncomputable def intrPullVol
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (y : M) (w : TangentSpace I y),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner y w w)))
    (p : M) (R : Real) : ENNReal :=
  ∫⁻ z in ball (0 : E) R,
    ENNReal.ofReal
      (curveDensity (I := I) g
        (intrinsicGeodesic (I := I) g hEnorm p
          (normalFrame (I := I) g p z))
        (fun i t =>
          intrinsicJacobi (I := I) g hEnorm p
            (normalFrame (I := I) g p z)
            ((normalBasis (I := I) g p) i) t)
        1)
    ∂(volume : Measure E)

omit [CompleteSpace E] [ConnectedSpace M] in
/-- The intrinsic pullback volume is bounded by the hyperbolic model volume
when every nonzero radial launch vector is nonconjugate before time one. -/
theorem intrPullVol_le_hyp
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (y : M) (w : TangentSpace I y),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner y w w)))
    (p : M) {q R : Real} (hq : 0 ≤ q) (hR : 0 < R)
    (hno : ∀ z, z ∈ ball (0 : E) R → z ≠ 0 →
      ∀ t, t ∈ Ioo (0 : Real) 1 →
        ¬ IsConjVec (I := I) g hEnorm p
          ((t • normalFrame (I := I) g p z :
            TangentSpace I p) : E))
    (hRic : RicciBoundedBelow (I := I) g
      (-(((Module.finrank Real E - 1 : Nat) : Real) * q ^ 2))) :
    intrPullVol (I := I) g hEnorm p R ≤
      (volume : Measure E).toSphere Set.univ *
        ENNReal.ofReal
          (hypRadVol q (Module.finrank Real E - 1) R) := by
  classical
  letI : Nontrivial E :=
    Module.nontrivial_of_finrank_pos
      (Nat.pos_of_ne_zero (NeZero.ne (Module.finrank Real E)))
  let L : E ≃L[Real] E := normalFrame (I := I) (E := E) g p
  let Dn : E → Real := fun z =>
    curveDensity (I := I) g
      (intrinsicGeodesic (I := I) g hEnorm p (L z))
      (fun i t =>
        intrinsicJacobi (I := I) g hEnorm p (L z)
          ((normalBasis (I := I) g p) i) t)
      1
  let Dh : E → ENNReal := fun z =>
    ENNReal.ofReal
      (hypDensity (q * ‖z‖) (Module.finrank Real E - 1) 1)
  have hpoint :
      ∀ᵐ z ∂(volume : Measure E), z ∈ ball (0 : E) R →
        ENNReal.ofReal (Dn z) ≤ Dh z := by
    filter_upwards [Measure.ae_ne (volume : Measure E) (0 : E)] with z hz0 hz
    have hu0 : L z ≠ 0 := by
      intro hLz
      apply hz0
      exact L.injective (by simpa only [map_zero] using hLz)
    have hdens :=
      expDens_le_hyp (I := I) g hEnorm p (L z)
        (normalBasis (I := I) g p)
        (normalBasis_inner (I := I) g p)
        q hq hu0 (hno z hz hz0) hRic
    have hsqrt :
        Real.sqrt (g.inner p (L z) (L z)) = ‖z‖ := by
      simpa only [L] using normalFrame_sqrt (I := I) g p z
    apply ENNReal.ofReal_le_ofReal
    simpa only [Dn, Dh, hsqrt] using hdens
  have hmono :
      (∫⁻ z in ball (0 : E) R,
          ENNReal.ofReal (Dn z) ∂(volume : Measure E)) ≤
        ∫⁻ z in ball (0 : E) R, Dh z ∂(volume : Measure E) :=
    setLIntegral_mono_ae' measurableSet_ball hpoint
  calc
    intrPullVol (I := I) g hEnorm p R =
        ∫⁻ z in ball (0 : E) R,
          ENNReal.ofReal (Dn z) ∂(volume : Measure E) := rfl
    _ ≤ ∫⁻ z in ball (0 : E) R, Dh z ∂(volume : Measure E) := hmono
    _ = (volume : Measure E).toSphere Set.univ *
        ENNReal.ofReal
          (hypRadVol q (Module.finrank Real E - 1) R) := by
      simpa only [Dh] using hypBall_lintegral (E := E) q hq hR

/-- **Cheeger--Gromov--Taylor geodesic-loop estimate.**

Suppose the radius-`R` intrinsic framed exponential ball is nonsingular, the
global `Rm04` norm is bounded by `K`, and `R ≤ π / √K`.  A based radial
geodesic loop of length `2ℓ` then satisfies the CGT lower bound

`ℓ ≥ (r₀ / 2) · V(B(p,s)) / (V(B(p,s)) + V⁰(B(0,r₀+s)))`

whenever `r₀ + 2s < R` and `r₀ < R / 4`.

The nonsingularity input is explicit at this lower boundary so the theorem
isolates the propeller argument from the separate Rauch comparison theorem.
The proof constructs distinct bounded-length radial classes by iterating the
loop, propagates them to inverse sheets above `B(p,s)`, and applies the area
formula. -/
theorem intrLoop_ge_cgt
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (y : M) (w : TangentSpace I y),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner y w w)))
    (p : M) {K R r₀ s ell : Real}
    (hK : 0 < K) (hR : 0 < R)
    (hRpi : R ≤ Real.pi / Real.sqrt K)
    (hRm : Rm04GlobalBound (I := I) (M := M) g K)
    (hloc :
      IsLocalDiffeomorphOn (modelWithCornersSelf Real E) I
        (↑(⊤ : ℕ∞) : WithTop ℕ∞)
        (intrinsicFramedExp (I := I) g hEnorm p)
        (ball (0 : E) R))
    (hr₀ : 0 < r₀) (hs : 0 < s)
    (hfit : r₀ + 2 * s < R) (hquarter : r₀ < R / 4)
    {u : E} (hell : 0 < ell) (hlen : ‖u‖ = 2 * ell)
    (hloop : intrinsicFramedExp (I := I) g hEnorm p u = p) :
    ENNReal.ofReal (r₀ / 2) *
          riemannianVolumeMeasure (I := I) (M := M) g
            {y : M | riemannianEDist I p y < ENNReal.ofReal s} /
        (riemannianVolumeMeasure (I := I) (M := M) g
            {y : M | riemannianEDist I p y < ENNReal.ofReal s} +
          intrPullVol (I := I) g hEnorm p (r₀ + s))
      ≤ ENNReal.ofReal ell := by
  sorry

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison
