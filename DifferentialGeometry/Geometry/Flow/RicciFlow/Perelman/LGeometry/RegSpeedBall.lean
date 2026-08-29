import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.GradBall
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.MinMaxSplit
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.NLCEndpoint

set_option autoImplicit false

/-!
# Uniform speed control on a flow metric ball

The scalar-gradient and Ricci inputs are localized to a controlled parabolic
ball.  Their coefficients are kept separate so the Gronwall exponent remains
uniform as the ball radius tends to zero.
-/

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Bundle Set
open scoped Manifold ContDiff ENNReal Topology

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [PseudoMetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]

private theorem scaleRic_eq (n : Nat) {r : Real} (hr : 0 < r) :
    r ^ 2 * ((n : Real) ^ 2 * Real.sqrt (1 / r ^ 4)) = (n : Real) ^ 2 := by
  have hr2 : 0 < r ^ 2 := sq_pos_of_pos hr
  rw [show r ^ 4 = (r ^ 2) ^ 2 by ring]
  rw [show 1 / (r ^ 2) ^ 2 = (1 / r ^ 2) ^ 2 by field_simp]
  rw [Real.sqrt_sq_eq_abs, abs_of_pos (one_div_pos.mpr hr2)]
  field_simp

private theorem exp_le_four {x : Real} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 4) :
    Real.exp x ≤ 4 / 3 := by
  calc
    Real.exp x ≤ 1 / (1 - x) :=
      Real.exp_bound_div_one_sub_of_interval hx0 (by linarith [hx])
    _ ≤ 4 / 3 := by
      apply (div_le_iff₀ (by linarith [hx])).2
      nlinarith [hx]

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- There is a dimension-scale choice for which every sufficiently short
regularized L-ray has speed controlled by its initial speed, as long as its
prefix stays in the later radius-`1/16` moving ball. -/
theorem lRegSpeed_unif
    [NeZero (Module.finrank Real E)] [T2Space (TangentBundle I M)]
    [ConnectedSpace M] [BoundarylessManifold I M] :
    ∃ theta : Real, 0 < theta ∧ theta < 1 ∧
      ∀ rho : Real, 0 < rho → ∃ eps₀ : Real, 0 < eps₀ ∧
        ∀ {D : RealTimeInterval} {S : SolutionOn (I := I) (M := M) D},
          IsSolutionOn (I := I) S →
          ∀ {time : RealTimeInterval.FlowTime D}
            (B : FlowMetricBall S time),
            B.radius ≤ rho → B.IsRmControlled →
            Set.Ioc ((time : Real) - B.radius ^ 2) (time : Real) ⊆ D.regular →
            (∀ q ∈ Set.Icc
              ((time : Real) - theta * B.radius ^ 2) (time : Real),
                RiemannianMetricComplete (I := I) (S.base.metric q)) →
            ∀ eps : Real, 0 < eps → eps ≤ eps₀ →
              ∀ Z : TangentSpace I B.center,
                let b := Real.sqrt eps * B.radius
                ∀ s ∈ Set.Icc (0 : Real) b,
                  s ∈ lRegDomain S (time : Real) B.center Z →
                  (∀ q ∈ Set.Icc (0 : Real) s,
                    riemannianEDistOf (I := I)
                        (S.base.metric ((time : Real) - q ^ 2)) B.center
                        (lRegCurve S (time : Real) B.center Z q) <
                      ENNReal.ofReal (B.radius / 16)) →
                  lRegSpeedSq S (time : Real)
                      (lRegCurve S (time : Real) B.center Z) s ≤
                    (4 / 3 : Real) *
                      (lRegSpeedSq S (time : Real)
                        (lRegCurve S (time : Real) B.center Z) 0 + 1) := by
  letI : CompleteSpace E := FiniteDimensional.complete Real E
  obtain ⟨theta, A, htheta, hthetaOne, hA, hgrad⟩ :=
    lGrad_ball (E := E) (I := I) (M := M)
  refine ⟨theta, htheta, hthetaOne, ?_⟩
  intro rho hrho
  let n : Real := Module.finrank Real E
  let C₀ : Real := rho + 2 * A + 4 * n ^ 2 + 1
  have hC₀ : 0 < C₀ := by
    dsimp only [C₀, n]
    nlinarith [hrho, hA.le, sq_nonneg (Module.finrank Real E : Real)]
  let d : Real := 1 / (4 * C₀)
  have hd : 0 < d := one_div_pos.mpr (mul_pos (by norm_num) hC₀)
  let eps₀ : Real := min (theta / 2) (min 1 (d ^ 2))
  have heps₀ : 0 < eps₀ := by
    dsimp only [eps₀]
    exact lt_min (div_pos htheta (by norm_num))
      (lt_min zero_lt_one (sq_pos_of_pos hd))
  refine ⟨eps₀, heps₀, ?_⟩
  intro D S hS time B hBrho hB hreg hcomplete eps heps heps₀ Z
  dsimp only
  intro s hs hsdom hpoint
  let b : Real := Real.sqrt eps * B.radius
  let G : Real := A / B.radius ^ 3
  let K : Real := n ^ 2 * Real.sqrt (1 / B.radius ^ 4)
  have hepsTheta : eps ≤ theta / 2 := by
    exact heps₀.trans (min_le_left (theta / 2) (min 1 (d ^ 2)))
  have hepsOne : eps ≤ 1 := by
    calc
      eps ≤ eps₀ := heps₀
      _ ≤ min 1 (d ^ 2) := min_le_right _ _
      _ ≤ 1 := min_le_left _ _
  have hepsD : eps ≤ d ^ 2 := by
    calc
      eps ≤ eps₀ := heps₀
      _ ≤ min 1 (d ^ 2) := min_le_right _ _
      _ ≤ d ^ 2 := min_le_right _ _
  have hsqrteps : 0 < Real.sqrt eps := Real.sqrt_pos.2 heps
  have hbpos : 0 < b := mul_pos hsqrteps B.radius_pos
  have hbSq : b ^ 2 = eps * B.radius ^ 2 := by
    dsimp only [b]
    rw [mul_pow, Real.sq_sqrt heps.le]
  have hepsLtOne : eps < 1 := by
    calc
      eps ≤ theta / 2 := hepsTheta
      _ < 1 := by linarith [hthetaOne]
  have hbSqLt : b ^ 2 < B.radius ^ 2 := by
    rw [hbSq]
    nlinarith [sq_pos_of_pos B.radius_pos]
  by_cases hsZero : s = 0
  · subst s
    have hU := lRegSpeedSq_nonneg (I := I) S (time : Real)
      (lRegCurve S (time : Real) B.center Z) 0
    nlinarith
  have hspos : 0 < s := lt_of_le_of_ne hs.1 (Ne.symm hsZero)
  have halpha : IsLRegCurveOn S (time : Real)
      (lRegCurve S (time : Real) B.center Z) (Set.Icc (0 : Real) s)
      B.center Z := by
    simpa only [Set.uIcc_of_le hs.1] using
      lRegCurve_isReg (I := I) S hS (time : Real) B.center Z hspos hsdom
  have hG : 0 ≤ G := div_nonneg hA.le (pow_nonneg B.radius_pos.le 3)
  have hK : 0 ≤ K := mul_nonneg (sq_nonneg n) (Real.sqrt_nonneg _)
  have hsle : s ≤ b := hs.2
  have hsub : Set.uIcc (0 : Real) s ⊆ Set.Icc (0 : Real) b := by
    intro q hq
    have hq' : q ∈ Set.Icc (0 : Real) s := by
      simpa only [Set.uIcc_of_le hs.1] using hq
    exact ⟨hq'.1, hq'.2.trans hsle⟩
  have htimeGrad : ∀ q ∈ Set.Icc (0 : Real) b,
      (time : Real) - q ^ 2 ∈ Set.Icc
        ((time : Real) - theta * B.radius ^ 2 / 2) (time : Real) := by
    intro q hq
    have hqSq : q ^ 2 ≤ b ^ 2 :=
      (sq_le_sq₀ hq.1 hbpos.le).2 hq.2
    have hqTheta : q ^ 2 ≤ theta * B.radius ^ 2 / 2 := by
      calc
        q ^ 2 ≤ b ^ 2 := hqSq
        _ = eps * B.radius ^ 2 := hbSq
        _ ≤ theta * B.radius ^ 2 / 2 := by
          nlinarith [mul_le_mul_of_nonneg_right hepsTheta
            (sq_nonneg B.radius)]
    exact ⟨by linarith, by nlinarith [sq_nonneg q]⟩
  have htimeBall : ∀ q ∈ Set.Icc (0 : Real) b,
      (time : Real) - q ^ 2 ∈ Set.Icc
        ((time : Real) - B.radius ^ 2) (time : Real) := by
    intro q hq
    have hqSq : q ^ 2 ≤ b ^ 2 :=
      (sq_le_sq₀ hq.1 hbpos.le).2 hq.2
    exact ⟨by linarith [hqSq, hbSqLt], by nlinarith [sq_nonneg q]⟩
  have hgr := lRegSpeed_split (I := I) S hS (time : Real) halpha
    0 s G K b hG hK hbpos.le
    (fun _ hq ↦ by simpa only [Set.uIcc_of_le hs.1] using hq)
    (fun q hq ↦ by
      have hqI := hsub hq
      rw [abs_of_nonneg hqI.1]
      exact hqI.2)
    (fun q hq ↦ by
      have hqI := hsub hq
      have hqS : q ∈ Set.Icc (0 : Real) s := by
        simpa only [Set.uIcc_of_le hs.1] using hq
      simpa only [G] using
        hgrad hS B hB hreg hcomplete ((time : Real) - q ^ 2)
          (htimeGrad q hqI)
          (lRegCurve S (time : Real) B.center Z q)
          (lVelocity (I := I) (lRegCurve S (time : Real) B.center Z) q)
          (hpoint q hqS))
    (fun q hq ↦ by
      have hqI := hsub hq
      have hqS : q ∈ Set.Icc (0 : Real) s := by
        simpa only [Set.uIcc_of_le hs.1] using hq
      have hmem : lRegCurve S (time : Real) B.center Z q ∈
          B.setAt ((time : Real) - q ^ 2) := by
        change riemannianEDistOf (I := I)
            (S.base.metric ((time : Real) - q ^ 2)) B.center
            (lRegCurve S (time : Real) B.center Z q) <
          ENNReal.ofReal B.radius
        exact (hpoint q hqS).trans_le
          (ENNReal.ofReal_le_ofReal (by nlinarith [B.radius_pos]))
      simpa only [K, n] using
        lRegRicci_le (I := I) S time B hB (htimeBall q hqI) hmem)
  have hscaleK : B.radius ^ 2 * K = n ^ 2 := by
    simpa only [K, n] using scaleRic_eq (Module.finrank Real E) B.radius_pos
  have hb3G : G * b ^ 2 * b = A * eps * Real.sqrt eps := by
    dsimp only [G, b]
    rw [mul_pow, Real.sq_sqrt heps.le]
    field_simp [B.radius_pos.ne']
  have hb2K : K * b * b = n ^ 2 * eps := by
    calc
      K * b * b = B.radius ^ 2 * K * (Real.sqrt eps) ^ 2 := by
        dsimp only [b]
        ring
      _ = B.radius ^ 2 * K * eps := by rw [Real.sq_sqrt heps.le]
      _ = n ^ 2 * eps := by rw [hscaleK]
  let k : Real := 1 + 2 * G * b ^ 2 + 4 * K * b
  let d₁ : Real := 1 + 2 * G * b ^ 2
  have hk : 0 < k := by
    dsimp only [k]
    exact add_pos_of_pos_of_nonneg
      (add_pos_of_pos_of_nonneg zero_lt_one
        (mul_nonneg (mul_nonneg (by norm_num) hG) (sq_nonneg b)))
      (mul_nonneg (mul_nonneg (by norm_num) hK) hbpos.le)
  have hd₁ : 0 < d₁ := by
    dsimp only [d₁]
    exact add_pos_of_pos_of_nonneg zero_lt_one
      (mul_nonneg (mul_nonneg (by norm_num) hG) (sq_nonneg b))
  have hratio : d₁ / k ≤ 1 := by
    rw [div_le_one hk]
    dsimp only [d₁, k]
    exact le_add_of_nonneg_right
      (mul_nonneg (mul_nonneg (by norm_num) hK) hbpos.le)
  have hsabs : |s - 0| ≤ b := by
    rw [sub_zero, abs_of_nonneg hs.1]
    exact hs.2
  have hepsSqrt : eps ≤ Real.sqrt eps := by
    nlinarith [Real.sq_sqrt heps.le, Real.sqrt_nonneg eps, hepsOne]
  have hepsMul : eps * Real.sqrt eps ≤ Real.sqrt eps :=
    mul_le_of_le_one_left (Real.sqrt_nonneg eps) hepsOne
  have hsqrtD : Real.sqrt eps ≤ d := by
    rw [Real.sqrt_le_iff]
    exact ⟨hd.le, hepsD⟩
  have hsqrtC₀ : Real.sqrt eps * C₀ ≤ 1 / 4 := by
    calc
      Real.sqrt eps * C₀ ≤ d * C₀ :=
        mul_le_mul_of_nonneg_right hsqrtD hC₀.le
      _ = 1 / 4 := by
        dsimp only [d]
        field_simp [hC₀.ne']
  have hexpArg : k * |s - 0| ≤ 1 / 4 := by
    have hkb : k * |s - 0| ≤ k * b :=
      mul_le_mul_of_nonneg_left hsabs hk.le
    have hcore : k * b = b + 2 * (G * b ^ 2 * b) + 4 * (K * b * b) := by
      dsimp only [k]
      ring
    calc
      k * |s - 0| ≤ k * b := hkb
      _ = b + 2 * (G * b ^ 2 * b) + 4 * (K * b * b) := hcore
      _ = Real.sqrt eps * B.radius +
          2 * (A * eps * Real.sqrt eps) + 4 * (n ^ 2 * eps) := by
        rw [hb3G, hb2K]
      _ ≤ Real.sqrt eps * (rho + 2 * A + 4 * n ^ 2) := by
        have h₁ : Real.sqrt eps * B.radius ≤ Real.sqrt eps * rho :=
          mul_le_mul_of_nonneg_left hBrho (Real.sqrt_nonneg eps)
        have h₂ : A * eps * Real.sqrt eps ≤ A * Real.sqrt eps := by
          simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hepsMul hA.le
        have h₃ : n ^ 2 * eps ≤ n ^ 2 * Real.sqrt eps :=
          mul_le_mul_of_nonneg_left hepsSqrt (sq_nonneg n)
        calc
          Real.sqrt eps * B.radius + 2 * (A * eps * Real.sqrt eps) +
                4 * (n ^ 2 * eps) ≤
              Real.sqrt eps * rho + 2 * (A * Real.sqrt eps) +
                4 * (n ^ 2 * Real.sqrt eps) :=
            add_le_add (add_le_add h₁
              (mul_le_mul_of_nonneg_left h₂ (by norm_num)))
              (mul_le_mul_of_nonneg_left h₃ (by norm_num))
          _ = Real.sqrt eps * (rho + 2 * A + 4 * n ^ 2) := by ring
      _ ≤ Real.sqrt eps * C₀ := by
        dsimp only [C₀]
        exact mul_le_mul_of_nonneg_left
          (le_add_of_nonneg_right zero_le_one) (Real.sqrt_nonneg eps)
      _ ≤ 1 / 4 := hsqrtC₀
  have hexp : Real.exp (k * |s - 0|) ≤ 4 / 3 :=
    exp_le_four (mul_nonneg hk.le (abs_nonneg _)) hexpArg
  have hterm : 0 ≤ lRegSpeedSq S (time : Real)
        (lRegCurve S (time : Real) B.center Z) 0 + d₁ / k :=
    add_nonneg (lRegSpeedSq_nonneg (I := I) S (time : Real)
      (lRegCurve S (time : Real) B.center Z) 0) (div_nonneg hd₁.le hk.le)
  calc
    lRegSpeedSq S (time : Real)
        (lRegCurve S (time : Real) B.center Z) s ≤
      Real.exp (k * |s - 0|) *
        (lRegSpeedSq S (time : Real)
          (lRegCurve S (time : Real) B.center Z) 0 + d₁ / k) := by
        simpa only [k, d₁] using hgr
    _ ≤ (4 / 3 : Real) *
        (lRegSpeedSq S (time : Real)
          (lRegCurve S (time : Real) B.center Z) 0 + d₁ / k) :=
      mul_le_mul_of_nonneg_right hexp hterm
    _ ≤ (4 / 3 : Real) *
        (lRegSpeedSq S (time : Real)
          (lRegCurve S (time : Real) B.center Z) 0 + 1) := by
      exact mul_le_mul_of_nonneg_left (add_le_add_right hratio _)
        (by norm_num)

end DifferentialGeometry.PDE.RicciFlow.Perelman
