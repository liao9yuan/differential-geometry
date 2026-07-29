import DifferentialGeometry.Analysis.Elliptic.MetricBounds
import DifferentialGeometry.Geometry.Exponential.IntrinsicMetricJets
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.H6JacobiPair

set_option autoImplicit false

/-!
# Metric-jet bounds for H6

This file converts the finite-tube intrinsic Jacobi-jet estimates into scalar
endpoint Gram-jet estimates. The multivariate metric bound is obtained later
by polarization.
-/

noncomputable section

open Bundle Set
open scoped Manifold ContDiff BigOperators

namespace DifferentialGeometry
namespace HCGCompactness

open Geometry.Riemannian.Exponential
open Geometry.Riemannian.NormalCoordinates

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
  [InnerProductSpace Real E] [FiniteDimensional Real E] [CompleteSpace E]
  [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [T2Space (TangentBundle I M)]
  [SigmaCompactSpace M] [ConnectedSpace M]

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
omit [ConnectedSpace M] [CompleteSpace E]
  [T2Space (TangentBundle I M)] in
/-- A common bound for the launch Jacobi jets through order `n` controls the
order-`n` endpoint Gram jet by the binomial factor `2 ^ n`. -/
theorem intrMetricJet_abs_le
    [PseudoEMetricSpace M]
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : forall x : M, forall v : TangentSpace I x,
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) (u a b : E) (n : Nat) (r B : Real) (hB : 0 ≤ B)
    (hjet : forall k, k ≤ n ->
      Real.sqrt
        (g.inner
          (intrLaunch3 (I := I) g hEnorm p u a b ((r, 0), 1))
          (intrLaunchJet (I := I) g hEnorm p u a b k (r, 1))
          (intrLaunchJet (I := I) g hEnorm p u a b k (r, 1))) ≤ B) :
    |intrMetricJet (I := I) g hEnorm p u a b n r| ≤
      2 ^ n * B ^ 2 := by
  classical
  unfold intrMetricJet
  calc
    |∑ i ∈ Finset.range (n + 1),
        (n.choose i : Real) *
          g.inner
            (intrLaunch3 (I := I) g hEnorm p u a b ((r, 0), 1))
            (intrLaunchJet (I := I) g hEnorm p u a b i (r, 1))
            (intrLaunchJet (I := I) g hEnorm p u a b (n - i) (r, 1))| ≤
        ∑ i ∈ Finset.range (n + 1),
          |(n.choose i : Real) *
            g.inner
              (intrLaunch3 (I := I) g hEnorm p u a b ((r, 0), 1))
              (intrLaunchJet (I := I) g hEnorm p u a b i (r, 1))
              (intrLaunchJet (I := I) g hEnorm p u a b (n - i) (r, 1))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : Real) * B ^ 2 := by
      refine Finset.sum_le_sum fun i hi => ?_
      have hin : i ≤ n := by
        have hi_lt := Finset.mem_range.mp hi
        omega
      have hleft := hjet i hin
      have hright := hjet (n - i) (Nat.sub_le n i)
      have hinner :=
        Geometry.Riemannian.abs_metric_inner_le_sqrt_metric_quadratic
          (I := I) (M := M) g
          (intrLaunch3 (I := I) g hEnorm p u a b ((r, 0), 1))
          (intrLaunchJet (I := I) g hEnorm p u a b i (r, 1))
          (intrLaunchJet (I := I) g hEnorm p u a b (n - i) (r, 1))
      rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg (n.choose i))]
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg (n.choose i))
      exact hinner.trans
        (mul_le_mul hleft hright (Real.sqrt_nonneg _) hB)
    _ = 2 ^ n * B ^ 2 := by
      rw [← Finset.sum_mul]
      have hsum :
          (∑ i ∈ Finset.range (n + 1), (n.choose i : Real)) =
            2 ^ n := by
        rw [← Nat.cast_sum, Nat.sum_range_choose]
        push_cast
        ring
      rw [hsum]

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- On a fixed launch tube, bounded geometry controls the diagonal endpoint
Gram jet at the central launch parameter. -/
theorem intrMetricJet_tube
    (P : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (hcomplete : MetricComplete (I := I) P)
    (hconn : letI : TopologicalSpace P.M := P.topology; ConnectedSpace P.M)
    (hP : BoundedGeometry (I := I) P)
    (p : P.M) (u a b : E) (n : Nat) {U D : Real} (hD : 0 ≤ D) :
    letI : TopologicalSpace P.M := P.topology
    letI : ChartedSpace H P.M := P.charted
    letI : IsManifold I ∞ P.M := P.smooth
    letI : IsManifold I 1 P.M :=
      IsManifold.of_le (I := I) (M := P.M) (n := ∞) (by decide)
    letI : SigmaCompactSpace P.M := P.sigmaCompact
    letI : T2Space P.M := P.t2
    letI : T2Space (TangentBundle I P.M) := P.t2TangentBundle
    letI : RiemannianBundle (fun x : P.M => TangentSpace I x) :=
      P.riemBundle (I := I)
    letI : (x : P.M) → InnerProductSpace Real (TangentSpace I x) :=
      P.riemInner (I := I)
    letI : IsContinuousRiemannianBundle E
        (fun x : P.M => TangentSpace I x) :=
      P.riemBundle_cont (I := I)
    letI : EMetricSpace P.M := P.emetricSpace (I := I)
    letI : CompleteSpace P.M :=
      MetricComplete.complete (I := I) P hcomplete
    letI : ConnectedSpace P.M := hconn
    let hEnorm : ∀ (x : P.M) (v : TangentSpace I x),
        ‖v‖ₑ = ENNReal.ofReal
          (Real.sqrt (P.metric.inner x v v)) := by
      intro x v
      simpa using
        (Geometry.Riemannian.tensor0SBundle_enorm_eq_riemannianBundle_enorm
          (I := I) P.metric x v)
    Real.sqrt (P.metric.inner p u u) ≤ U →
    Real.sqrt (P.metric.inner p a a) ≤ D →
    Real.sqrt (P.metric.inner p b b) ≤ D →
    |intrMetricJet (I := I) P.metric hEnorm p u a b n 0| ≤
      2 ^ n * jetCap hP.C U D n ^ 2 := by
  letI : TopologicalSpace P.M := P.topology
  letI : ChartedSpace H P.M := P.charted
  letI : IsManifold I ∞ P.M := P.smooth
  letI : IsManifold I 1 P.M :=
    IsManifold.of_le (I := I) (M := P.M) (n := ∞) (by decide)
  letI : SigmaCompactSpace P.M := P.sigmaCompact
  letI : T2Space P.M := P.t2
  letI : T2Space (TangentBundle I P.M) := P.t2TangentBundle
  letI : RiemannianBundle (fun x : P.M => TangentSpace I x) :=
    P.riemBundle (I := I)
  letI : (x : P.M) → InnerProductSpace Real (TangentSpace I x) :=
    P.riemInner (I := I)
  letI : IsContinuousRiemannianBundle E
      (fun x : P.M => TangentSpace I x) :=
    P.riemBundle_cont (I := I)
  letI : EMetricSpace P.M := P.emetricSpace (I := I)
  letI : CompleteSpace P.M :=
    MetricComplete.complete (I := I) P hcomplete
  letI : ConnectedSpace P.M := hconn
  let hEnorm : ∀ (x : P.M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal
        (Real.sqrt (P.metric.inner x v v)) := by
    intro x v
    simpa using
      (Geometry.Riemannian.tensor0SBundle_enorm_eq_riemannianBundle_enorm
        (I := I) P.metric x v)
  dsimp only
  intro hu ha hb
  have hjets :=
    intrJet_upto_le (I := I) P hcomplete hconn hP p u
      (R := 0) (U := U) (D := D) hD (by simpa using hu)
      n a b ha hb 0 (by simp)
  apply intrMetricJet_abs_le (I := I) P.metric hEnorm p u a b n 0
    (jetCap hP.C U D n) (jetCap_nonneg hP.C hD n)
  intro k hk
  simpa only [IntrJetAtom.eval, intrLaunchJet] using
    hjets.1 k hk 1 (by constructor <;> norm_num)

end HCGCompactness
end DifferentialGeometry

end
