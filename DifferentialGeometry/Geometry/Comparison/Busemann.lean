import DifferentialGeometry.Geometry.Comparison.MinimizingRay
import Mathlib.Topology.Order.MonotoneConvergence

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold Set Topology
open scoped ENNReal Manifold

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian

open Exponential

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ℕ∞) : WithTop ℕ∞) M]
  [T2Space M] [SigmaCompactSpace M]

section BusemannMetricCore

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace

variable [ConnectedSpace M]
  [RiemannianBundle (fun x : M => TangentSpace I x)]
  [PseudoEMetricSpace M] [IsRiemannianManifold I M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

/-- The distance-to-an-integer-pole approximation of the Busemann function. -/
def busemannApprox (γ : Real → M) (n : ℕ) (x : M) : Real :=
  (riemannianEDist I (γ (n : Real)) x).toReal - (n : Real)

/-- The Busemann function of a ray, defined as the infimum of its integer-pole
approximations. -/
def busemann (γ : Real → M) (x : M) : Real :=
  sInf (Set.range (fun n : ℕ => busemannApprox (I := I) γ n x))

omit [FiniteDimensional Real E] [NeZero (Module.finrank Real E)] [I.Boundaryless]
    [T2Space M] [SigmaCompactSpace M] [PseudoEMetricSpace M]
    [IsRiemannianManifold I M] in
private theorem edist_real_triangle (x y z : M) :
    (riemannianEDist I x z).toReal ≤
      (riemannianEDist I x y).toReal +
        (riemannianEDist I y z).toReal := by
  have hxy : riemannianEDist I x y ≠ ⊤ :=
    riemannianEDist_ne_top (I := I) x y
  have hyz : riemannianEDist I y z ≠ ⊤ :=
    riemannianEDist_ne_top (I := I) y z
  have htri : riemannianEDist I x z ≤
      riemannianEDist I x y + riemannianEDist I y z :=
    Manifold.riemannianEDist_triangle
  have hreal := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hxy, hyz⟩) htri
  rwa [ENNReal.toReal_add hxy hyz] at hreal

omit [FiniteDimensional Real E] [NeZero (Module.finrank Real E)] [I.Boundaryless]
    [IsManifold I ((⊤ : ℕ∞) : WithTop ℕ∞) M] [T2Space M]
    [SigmaCompactSpace M] [ConnectedSpace M] [PseudoEMetricSpace M]
    [IsRiemannianManifold I M] in
private theorem edist_real_comm (x y : M) :
    (riemannianEDist I x y).toReal =
      (riemannianEDist I y x).toReal := by
  exact congrArg ENNReal.toReal
    (Manifold.riemannianEDist_comm (I := I) (x := x) (y := y))

omit [NeZero (Module.finrank Real E)] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] [ConnectedSpace M] [PseudoEMetricSpace M]
    [IsRiemannianManifold I M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)] in
private theorem ray_dist_real
    {g : SmoothRiemannianMetric I M} {p : M} {γ : Real → M}
    (hray : IsMinimizingRay (I := I) g p γ)
    {s t : Real} (hs : 0 ≤ s) (hst : s ≤ t) :
    (riemannianEDist I (γ s) (γ t)).toReal = t - s := by
  calc
    (riemannianEDist I (γ s) (γ t)).toReal =
        (ENNReal.ofReal (t - s)).toReal :=
      congrArg ENNReal.toReal (hray.edist_eq hs hst)
    _ = t - s := ENNReal.toReal_ofReal (sub_nonneg.mpr hst)

omit [NeZero (Module.finrank Real E)] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] [PseudoEMetricSpace M] [IsRiemannianManifold I M] in
/-- Integer-pole Busemann approximations decrease as the pole moves out along
the minimizing ray. -/
theorem buseApprox_anti
    {g : SmoothRiemannianMetric I M} {p : M} {γ : Real → M}
    (hray : IsMinimizingRay (I := I) g p γ) (x : M) :
    Antitone (fun n : ℕ => busemannApprox (I := I) γ n x) := by
  intro n m hnm
  have hnm_real : (n : Real) ≤ (m : Real) := by exact_mod_cast hnm
  have htri := edist_real_triangle (I := I) (γ (m : Real)) (γ (n : Real)) x
  have hdist :
      (riemannianEDist I (γ (m : Real)) (γ (n : Real))).toReal =
        (m : Real) - (n : Real) := by
    rw [edist_real_comm (I := I) (γ (m : Real)) (γ (n : Real))]
    exact ray_dist_real (I := I) hray (Nat.cast_nonneg n) hnm_real
  unfold busemannApprox
  rw [hdist] at htri
  linarith

omit [NeZero (Module.finrank Real E)] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] [PseudoEMetricSpace M] [IsRiemannianManifold I M] in
/-- Every integer-pole approximation is bounded below by minus the distance
from the initial point of the ray. -/
theorem buseApprox_lower
    {g : SmoothRiemannianMetric I M} {p : M} {γ : Real → M}
    (hray : IsMinimizingRay (I := I) g p γ) (x : M) (n : ℕ) :
    -(riemannianEDist I (γ 0) x).toReal ≤
      busemannApprox (I := I) γ n x := by
  have hdist :
      (riemannianEDist I (γ 0) (γ (n : Real))).toReal = (n : Real) := by
    simpa only [sub_zero] using
      ray_dist_real (I := I) hray (le_refl 0) (Nat.cast_nonneg n)
  have htri : (n : Real) ≤
      (riemannianEDist I (γ 0) x).toReal +
        (riemannianEDist I (γ (n : Real)) x).toReal := by
    calc
      (n : Real) =
          (riemannianEDist I (γ 0) (γ (n : Real))).toReal := hdist.symm
      _ ≤ (riemannianEDist I (γ 0) x).toReal +
          (riemannianEDist I x (γ (n : Real))).toReal :=
        edist_real_triangle (I := I) (γ 0) x (γ (n : Real))
      _ = (riemannianEDist I (γ 0) x).toReal +
          (riemannianEDist I (γ (n : Real)) x).toReal := by
        rw [edist_real_comm (I := I) x (γ (n : Real))]
  change -(riemannianEDist I (γ 0) x).toReal ≤
    (riemannianEDist I (γ (n : Real)) x).toReal - (n : Real)
  linarith

omit [NeZero (Module.finrank Real E)] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] [PseudoEMetricSpace M] [IsRiemannianManifold I M] in
/-- The set of integer-pole approximations is bounded below. -/
theorem buseApprox_bdd
    {g : SmoothRiemannianMetric I M} {p : M} {γ : Real → M}
    (hray : IsMinimizingRay (I := I) g p γ) (x : M) :
    BddBelow (Set.range (fun n : ℕ => busemannApprox (I := I) γ n x)) := by
  refine ⟨-(riemannianEDist I (γ 0) x).toReal, ?_⟩
  rintro y ⟨n, rfl⟩
  exact buseApprox_lower (I := I) hray x n

omit [NeZero (Module.finrank Real E)] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] [PseudoEMetricSpace M] [IsRiemannianManifold I M] in
/-- The Busemann function is at most each integer-pole approximation. -/
theorem busemann_le_approx
    {g : SmoothRiemannianMetric I M} {p : M} {γ : Real → M}
    (hray : IsMinimizingRay (I := I) g p γ) (x : M) (n : ℕ) :
    busemann (I := I) γ x ≤ busemannApprox (I := I) γ n x := by
  unfold busemann
  exact csInf_le (buseApprox_bdd (I := I) hray x) ⟨n, rfl⟩

omit [NeZero (Module.finrank Real E)] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] [PseudoEMetricSpace M] [IsRiemannianManifold I M] in
/-- Integer-pole approximations converge to the Busemann function. -/
theorem busemann_tendsto
    {g : SmoothRiemannianMetric I M} {p : M} {γ : Real → M}
    (hray : IsMinimizingRay (I := I) g p γ) (x : M) :
    Tendsto (fun n : ℕ => busemannApprox (I := I) γ n x) atTop
      (nhds (busemann (I := I) γ x)) := by
  unfold busemann
  rw [sInf_range]
  exact tendsto_atTop_ciInf
    (buseApprox_anti (I := I) hray x) (buseApprox_bdd (I := I) hray x)

omit [FiniteDimensional Real E] [NeZero (Module.finrank Real E)] [I.Boundaryless]
    [T2Space M] [SigmaCompactSpace M] [PseudoEMetricSpace M]
    [IsRiemannianManifold I M] in
/-- At each integer pole, two Busemann approximations differ by at most the
distance between their spatial arguments. -/
theorem buseApprox_dist (γ : Real → M) (n : ℕ) (x y : M) :
    |busemannApprox (I := I) γ n x - busemannApprox (I := I) γ n y| ≤
      (riemannianEDist I x y).toReal := by
  have hxy := edist_real_triangle (I := I) (γ (n : Real)) y x
  have hyx := edist_real_triangle (I := I) (γ (n : Real)) x y
  have hcomm := edist_real_comm (I := I) y x
  unfold busemannApprox
  rw [hcomm] at hxy
  rw [abs_le]
  constructor <;> linarith

omit [NeZero (Module.finrank Real E)] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] [PseudoEMetricSpace M] [IsRiemannianManifold I M] in
/-- The change of a Busemann function is bounded above by Riemannian distance. -/
theorem busemann_sub_le
    {g : SmoothRiemannianMetric I M} {p : M} {γ : Real → M}
    (hray : IsMinimizingRay (I := I) g p γ) (x y : M) :
    busemann (I := I) γ x - busemann (I := I) γ y ≤
      (riemannianEDist I x y).toReal := by
  have hlim :
      Tendsto
        (fun n : ℕ => busemannApprox (I := I) γ n x -
          busemannApprox (I := I) γ n y) atTop
        (nhds (busemann (I := I) γ x - busemann (I := I) γ y)) :=
    (busemann_tendsto (I := I) hray x).sub
      (busemann_tendsto (I := I) hray y)
  apply le_of_tendsto hlim
  exact Eventually.of_forall fun n =>
    (abs_le.mp (buseApprox_dist (I := I) γ n x y)).2

omit [NeZero (Module.finrank Real E)] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] [PseudoEMetricSpace M] [IsRiemannianManifold I M] in
/-- A Busemann function is one-Lipschitz for the real-valued Riemannian
distance. -/
theorem busemann_dist
    {g : SmoothRiemannianMetric I M} {p : M} {γ : Real → M}
    (hray : IsMinimizingRay (I := I) g p γ) (x y : M) :
    |busemann (I := I) γ x - busemann (I := I) γ y| ≤
      (riemannianEDist I x y).toReal := by
  rw [abs_le]
  constructor
  · have h := busemann_sub_le (I := I) hray y x
    rw [edist_real_comm (I := I) y x] at h
    linarith
  · exact busemann_sub_le (I := I) hray x y

omit [NeZero (Module.finrank Real E)] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] [PseudoEMetricSpace M] [IsRiemannianManifold I M] in
/-- Along a minimizing ray, its Busemann function has value minus the ray
parameter. -/
theorem busemann_ray
    {g : SmoothRiemannianMetric I M} {p : M} {γ : Real → M}
    (hray : IsMinimizingRay (I := I) g p γ) {s : Real} (hs : 0 ≤ s) :
    busemann (I := I) γ (γ s) = -s := by
  obtain ⟨N, hN⟩ := exists_nat_ge s
  have hconst :
      Tendsto (fun n : ℕ => busemannApprox (I := I) γ n (γ s)) atTop
        (nhds (-s)) := by
    apply tendsto_atTop_of_eventually_const (i₀ := N)
    intro n hn
    have hNn : (N : Real) ≤ (n : Real) := by exact_mod_cast hn
    have hsn : s ≤ (n : Real) := hN.trans hNn
    have hdist :
        (riemannianEDist I (γ (n : Real)) (γ s)).toReal =
          (n : Real) - s := by
      rw [edist_real_comm (I := I) (γ (n : Real)) (γ s)]
      exact ray_dist_real (I := I) hray hs hsn
    unfold busemannApprox
    rw [hdist]
    ring
  exact tendsto_nhds_unique (busemann_tendsto (I := I) hray (γ s)) hconst

end BusemannMetricCore

end Riemannian
end Geometry
end DifferentialGeometry
