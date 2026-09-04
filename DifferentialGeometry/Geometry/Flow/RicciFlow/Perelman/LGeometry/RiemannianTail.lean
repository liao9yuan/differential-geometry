import DifferentialGeometry.Analysis.Integration.Measure.GaussianTail
import DifferentialGeometry.Geometry.Comparison.HopfRinowProper
import DifferentialGeometry.Geometry.Comparison.Volume.SegmentBallEuclideanUpper

set_option autoImplicit false

noncomputable section

open Bundle Manifold MeasureTheory Set
open scoped ENNReal Manifold Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open DifferentialGeometry.Analysis.Measure
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.BonnetMyers
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Riemannian.VolumeComparison
open DifferentialGeometry.Integral.Measure

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ℕ∞) : WithTop ℕ∞) M]
  [T2Space M] [T2Space (TangentBundle I M)]
  [SigmaCompactSpace M]

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- On a complete manifold with nonnegative Ricci curvature, the exterior
Gaussian integral is bounded by the universal polynomial shell tail. -/
theorem riem_gauss_tail [ConnectedSpace M]
    (g : SmoothRiemannianMetric I M)
    (hcomplete : RiemannianMetricComplete (I := I) g)
    (p : M) {decay : ℝ} (hdecay : 0 < decay)
    (hRic : RicciBoundedBelow (I := I) g 0) (N : ℕ) :
    ∫⁻ y in {y : M | (N : ℝ) ≤
          (riemannianEDistOf (I := I) g p y).toReal},
        ENNReal.ofReal (Real.exp (-decay *
          (riemannianEDistOf (I := I) g p y).toReal ^ 2))
        ∂riemannianVolumeMeasure (I := I) (M := M) g ≤
      (((MeasureTheory.volume : MeasureTheory.Measure
          (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).toSphere Set.univ) *
        ENNReal.ofReal ((Module.finrank ℝ E : ℝ)⁻¹)) *
        gaussTail (Module.finrank ℝ E) decay N := by
  classical
  letI : IsManifold I 1 M :=
    IsManifold.of_le (I := I) (M := M)
      (n := ((⊤ : ℕ∞) : WithTop ℕ∞))
      (by decide : (1 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞))
  letI : TopologicalSpace.MetrizableSpace M :=
    Manifold.metrizableSpace I M
  letI : T3Space M := inferInstance
  letI cg : Bundle.ContinuousRiemannianMetric E
      (TangentSpace I : M → Type _) :=
    g.toContinuousRiemannianMetric
  letI : RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨cg.toRiemannianMetric⟩
  letI : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
  letI : PseudoEMetricSpace M :=
    (EMetricSpace.ofRiemannianMetric I M).toPseudoEMetricSpace
  letI : CompleteSpace M := hcomplete.complete
  letI : MetricSpace M :=
    DifferentialGeometry.Geometry.Riemannian.HopfRinow.riemMetricSpace
      (I := I) (M := M)
  have hEnorm : IsMetricNorm (I := I) (M := M) g := by
    intro x v
    exact tensor0SBundle_enorm_eq_riemannianBundle_enorm (I := I) g x v
  let n : ℕ := Module.finrank ℝ E
  let C : ℝ≥0∞ :=
    ((MeasureTheory.volume : MeasureTheory.Measure
        (EuclideanSpace ℝ (Fin n))).toSphere Set.univ) *
      ENNReal.ofReal ((n : ℝ)⁻¹)
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hmodel (r : ℝ) (hr : 0 ≤ r) :
      ENNReal.ofReal (hypRadVol 0 (n - 1) r) =
        ENNReal.ofReal (r ^ n) * ENNReal.ofReal ((n : ℝ)⁻¹) := by
    have hnR : ((n - 1 : ℕ) : ℝ) + 1 = n := by
      rw [Nat.cast_sub hn]
      norm_num
    rw [hypRadVol_zero, Nat.sub_add_cancel hn, hnR, div_eq_mul_inv,
      ENNReal.ofReal_mul (pow_nonneg hr n)]
  have hball : ∀ r : ℝ, 1 ≤ r →
      riemannianVolumeMeasure (I := I) (M := M) g (Metric.ball p r) ≤
        C * ENNReal.ofReal (r ^ n) := by
    intro r hr
    have hrpos : 0 < r := zero_lt_one.trans_le hr
    have hvol := segBall_vol_le_euclidean (I := I) g hEnorm p
      (q := 0) (R := r) (by positivity) hrpos (by simpa using hRic)
    have hset : Metric.ball p r =
        {y : M | riemannianEDist I p y < ENNReal.ofReal r} := by
      ext y
      simp only [Metric.mem_ball, mem_setOf_eq]
      rw [dist_comm]
      rw [DifferentialGeometry.Geometry.Riemannian.HopfRinow.riemMetric_dist_eq
        (I := I) (M := M) p y]
      exact (ENNReal.lt_ofReal_iff_toReal_lt
        (riemannianEDist_ne_top (I := I) p y)).symm
    rw [← hset] at hvol
    rw [show Module.finrank ℝ E - 1 = n - 1 by rfl,
      hmodel r hrpos.le] at hvol
    simpa only [C, mul_assoc, mul_left_comm, mul_comm] using hvol
  have hgauss := gauss_tail_of_ball
    (riemannianVolumeMeasure (I := I) (M := M) g) p n C
      hdecay hball N
  have hdist (y : M) :
      dist p y = (riemannianEDistOf (I := I) g p y).toReal := by
    rw [riemannianEDistOf_eq_riemannianEDist (I := I) g hEnorm]
    exact
      DifferentialGeometry.Geometry.Riemannian.HopfRinow.riemMetric_dist_eq
        (I := I) (M := M) p y
  have htail : (Metric.ball p (N : ℝ))ᶜ =
      {y : M | (N : ℝ) ≤
        (riemannianEDistOf (I := I) g p y).toReal} := by
    ext y
    simp only [mem_compl_iff, Metric.mem_ball, mem_setOf_eq, not_lt]
    rw [dist_comm, hdist]
  rw [htail] at hgauss
  simpa only [hdist, C, n] using hgauss

end DifferentialGeometry.PDE.RicciFlow.Perelman
