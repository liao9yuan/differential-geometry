import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.MinMax

set_option autoImplicit false

/-!
# Split-coefficient speed control for regularized L-rays

This module keeps the scalar-gradient and Ricci coefficients separate in the
regularized L-speed Gronwall estimate.  That separation preserves parabolic
scale invariance when the two inputs have orders `radius ^ (-3)` and
`radius ^ (-2)`.
-/

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Bundle Set
open scoped Manifold ContDiff Topology

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Riemannian.AlongCurve
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
  [InnerProductSpace Real E] [FiniteDimensional Real E]
  [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
variable {D : RealTimeInterval}

private theorem speedDeriv_split
    {s R G K U P Q : Real} (hs : |s| ≤ R) (hR : 0 ≤ R)
    (hG : 0 ≤ G) (hU : 0 ≤ U)
    (hP : |P| ≤ G * Real.sqrt U) (hQ : |Q| ≤ K * U) :
    |4 * s ^ 2 * P - 4 * s * Q| ≤
      (1 + 2 * G * R ^ 2 + 4 * K * R) * U +
        (1 + 2 * G * R ^ 2) := by
  have hs0 : 0 ≤ |s| := abs_nonneg s
  have hsSq : s ^ 2 ≤ R ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ hs0 hR).2 hs
  have hsqrt : 0 ≤ Real.sqrt U := Real.sqrt_nonneg U
  have hsqrtSq : (Real.sqrt U) ^ 2 = U := Real.sq_sqrt hU
  have hsqrtYoung : 2 * Real.sqrt U ≤ U + 1 := by
    nlinarith [sq_nonneg (Real.sqrt U - 1)]
  calc
    |4 * s ^ 2 * P - 4 * s * Q| ≤
        |4 * s ^ 2 * P| + |4 * s * Q| := abs_sub _ _
    _ = 4 * s ^ 2 * |P| + 4 * |s| * |Q| := by
      simp only [abs_mul, abs_of_nonneg (sq_nonneg s)]
      norm_num
    _ ≤ 4 * R ^ 2 * (G * Real.sqrt U) + 4 * R * (K * U) := by
      gcongr
    _ ≤ (1 + 2 * G * R ^ 2 + 4 * K * R) * U +
        (1 + 2 * G * R ^ 2) := by
      nlinarith [mul_nonneg hG (sq_nonneg R)]

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [SigmaCompactSpace M] in
/-- Separate scalar-gradient and Ricci bounds give a scale-sensitive Gronwall
comparison for regularized L-speed squared. -/
theorem lRegSpeed_split
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : Real) {alpha : Real → M} {J : Set Real} {x : M}
    {Z : TangentSpace I x} (halpha : IsLRegCurveOn S T alpha J x Z)
    (a b G K R : Real) (hG : 0 ≤ G) (hK : 0 ≤ K) (hR : 0 ≤ R)
    (hJ : Set.uIcc a b ⊆ J)
    (hsR : ∀ s ∈ Set.uIcc a b, |s| ≤ R)
    (hgrad : ∀ s ∈ Set.uIcc a b,
      |(S.base.metric (T - s ^ 2)).inner (alpha s)
          (gradientFun (I := I) (S.base.metric (T - s ^ 2))
            (S.scalar (T - s ^ 2)) (alpha s))
          (lVelocity (I := I) alpha s)| ≤
        G * Real.sqrt (lRegSpeedSq S T alpha s))
    (hric : ∀ s ∈ Set.uIcc a b,
      |S.ricciAt (T - s ^ 2) (alpha s)
          (vec2 (lVelocity (I := I) alpha s)
            (lVelocity (I := I) alpha s))| ≤
        K * lRegSpeedSq S T alpha s) :
    lRegSpeedSq S T alpha b ≤
      Real.exp ((1 + 2 * G * R ^ 2 + 4 * K * R) * |b - a|) *
        (lRegSpeedSq S T alpha a +
          (1 + 2 * G * R ^ 2) /
            (1 + 2 * G * R ^ 2 + 4 * K * R)) := by
  let U : Real → Real := lRegSpeedSq S T alpha
  let U' : Real → Real := fun s ↦
    4 * s ^ 2 *
        (S.base.metric (T - s ^ 2)).inner (alpha s)
          (gradientFun (I := I) (S.base.metric (T - s ^ 2))
            (S.scalar (T - s ^ 2)) (alpha s))
          (lVelocity (I := I) alpha s) -
      4 * s * S.ricciAt (T - s ^ 2) (alpha s)
        (vec2 (lVelocity (I := I) alpha s)
          (lVelocity (I := I) alpha s))
  have hk : 0 < 1 + 2 * G * R ^ 2 + 4 * K * R := by
    nlinarith [mul_nonneg hG (sq_nonneg R), mul_nonneg hK hR]
  have hd : 0 < 1 + 2 * G * R ^ 2 := by
    nlinarith [mul_nonneg hG (sq_nonneg R)]
  apply DifferentialGeometry.HCGCompactness.affineGronwall_of_abs_deriv_le
    U U' hk hd
  · intro s hs
    exact lRegSpeedSq_nonneg (I := I) S T alpha s
  · intro s hs
    simpa only [U, U'] using
      lRegSpeedSq_deriv (I := I) S hS T halpha (hJ hs)
  · intro s hs
    apply speedDeriv_split (hsR s hs) hR hG
      (lRegSpeedSq_nonneg (I := I) S T alpha s)
      (hgrad s hs) (hric s hs)

end DifferentialGeometry.PDE.RicciFlow.Perelman
