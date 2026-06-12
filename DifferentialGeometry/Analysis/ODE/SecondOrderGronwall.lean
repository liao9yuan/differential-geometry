import Mathlib.Analysis.ODE.Gronwall

set_option autoImplicit false

/-!
# Grönwall bound for second-order linear ODEs

`norm_le_gronwall_secondOrder`: if `Y : ℝ → E` satisfies the second-order estimate
`‖Y''(t)‖ ≤ K‖Y(t)‖ + ε` on `[0, b)` with `‖Y 0‖ ≤ δ` and `‖Y' 0‖ ≤ δ`, then
`‖Y t‖ ≤ gronwallBound δ (max K 1) ε t` on `[0, b]`.  Proved by passing to the
first-order system `Z = (Y, Y')` and applying Mathlib's
`norm_le_gronwallBound_of_norm_deriv_right_le`.

This is the ODE engine for the Jacobi-field route to the normal-coordinate metric
bounds (MSM135 Chapter 4 Step B, B0; see
`Geometry/Flow/RicciFlow/HCGCompactness/B0NormalCoordBounds.md`): the Jacobi equation
`Y'' + A(t)Y = F` with `‖A‖ ≤ K` and `‖F‖ ≤ ε` satisfies the hypothesis, and each
`x`-derivative of the Jacobi field satisfies such an inhomogeneous equation with `F`
controlled by curvature derivatives and lower-order data.
-/

namespace DifferentialGeometry

open Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Grönwall bound for a second-order linear ODE estimate, via the first-order
system `(Y, Y')`. -/
theorem norm_le_gronwall_secondOrder
    {Y Y' Y'' : ℝ → E} {K eps δ b : ℝ}
    (hK : 0 ≤ K) (heps : 0 ≤ eps)
    (hcY : ContinuousOn Y (Icc 0 b))
    (hcY' : ContinuousOn Y' (Icc 0 b))
    (hdY : ∀ t ∈ Ico 0 b, HasDerivWithinAt Y (Y' t) (Ici t) t)
    (hdY' : ∀ t ∈ Ico 0 b, HasDerivWithinAt Y' (Y'' t) (Ici t) t)
    (hbound : ∀ t ∈ Ico 0 b, ‖Y'' t‖ ≤ K * ‖Y t‖ + eps)
    (h0 : ‖Y 0‖ ≤ δ) (h0' : ‖Y' 0‖ ≤ δ) :
    ∀ t ∈ Icc 0 b, ‖Y t‖ ≤ gronwallBound δ (max K 1) eps t := by
  set Z : ℝ → E × E := fun t => (Y t, Y' t) with hZdef
  have hcZ : ContinuousOn Z (Icc 0 b) := hcY.prodMk hcY'
  have hdZ : ∀ t ∈ Ico 0 b,
      HasDerivWithinAt Z (Y' t, Y'' t) (Ici t) t :=
    fun t ht => (hdY t ht).prodMk (hdY' t ht)
  have h0Z : ‖Z 0‖ ≤ δ := by
    rw [Prod.norm_def]
    exact max_le h0 h0'
  have hboundZ : ∀ t ∈ Ico 0 b,
      ‖(Y' t, Y'' t)‖ ≤ max K 1 * ‖Z t‖ + eps := by
    intro t ht
    rw [Prod.norm_def]
    have h1 : ‖Y' t‖ ≤ ‖Z t‖ := norm_snd_le (Z t)
    have h2 : ‖Y t‖ ≤ ‖Z t‖ := norm_fst_le (Z t)
    have hZ0 : 0 ≤ ‖Z t‖ := norm_nonneg _
    apply max_le
    · calc ‖Y' t‖ ≤ ‖Z t‖ := h1
        _ ≤ max K 1 * ‖Z t‖ := le_mul_of_one_le_left hZ0 (le_max_right K 1)
        _ ≤ max K 1 * ‖Z t‖ + eps := le_add_of_nonneg_right heps
    · calc ‖Y'' t‖ ≤ K * ‖Y t‖ + eps := hbound t ht
        _ ≤ max K 1 * ‖Z t‖ + eps := by
            have hmul : K * ‖Y t‖ ≤ max K 1 * ‖Z t‖ :=
              mul_le_mul (le_max_left K 1) h2 (norm_nonneg _)
                (hK.trans (le_max_left K 1))
            linarith
  have hmain := norm_le_gronwallBound_of_norm_deriv_right_le hcZ hdZ h0Z hboundZ
  intro t ht
  calc ‖Y t‖ ≤ ‖Z t‖ := norm_fst_le (Z t)
    _ ≤ gronwallBound δ (max K 1) eps (t - 0) := hmain t ht
    _ = gronwallBound δ (max K 1) eps t := by rw [sub_zero]

/-- **Perturbation form of the second-order Grönwall bound.**  A solution of the
homogeneous Jacobi-type estimate `‖Y''‖ ≤ K‖Y‖` with `Y 0 = 0`, `Y' 0 = w` stays
`gronwallBound`-close to its linearisation `t ↦ t • w`.  (Apply with
`Z := Y - t • w`: `Z'' = Y''` and `‖Y‖ ≤ ‖Z‖ + t‖w‖` make the estimate
inhomogeneous with `ε = K·b·‖w‖` and zero initial data.) -/
theorem gronwall_sub_linear
    {Y Y' Y'' : ℝ → E} {K b : ℝ} {w : E}
    (hK : 0 ≤ K) (hb : 0 ≤ b)
    (hcY : ContinuousOn Y (Icc 0 b))
    (hcY' : ContinuousOn Y' (Icc 0 b))
    (hdY : ∀ t ∈ Ico 0 b, HasDerivWithinAt Y (Y' t) (Ici t) t)
    (hdY' : ∀ t ∈ Ico 0 b, HasDerivWithinAt Y' (Y'' t) (Ici t) t)
    (hbound : ∀ t ∈ Ico 0 b, ‖Y'' t‖ ≤ K * ‖Y t‖)
    (h0 : Y 0 = 0) (h0' : Y' 0 = w) :
    ∀ t ∈ Icc 0 b,
      ‖Y t - t • w‖ ≤ gronwallBound 0 (max K 1) (K * (b * ‖w‖)) t := by
  set Z : ℝ → E := fun t => Y t - t • w with hZ
  set Z' : ℝ → E := fun t => Y' t - w with hZ'
  have heps : 0 ≤ K * (b * ‖w‖) :=
    mul_nonneg hK (mul_nonneg hb (norm_nonneg w))
  have hlin : ∀ (t : ℝ) (s : Set ℝ),
      HasDerivWithinAt (fun x : ℝ => x • w) w s t := by
    intro t s
    simpa using (hasDerivWithinAt_id t s).smul_const w
  have hcZ : ContinuousOn Z (Icc 0 b) :=
    hcY.sub ((continuous_id.smul continuous_const).continuousOn)
  have hcZ' : ContinuousOn Z' (Icc 0 b) := hcY'.sub continuousOn_const
  have hdZ : ∀ t ∈ Ico 0 b, HasDerivWithinAt Z (Z' t) (Ici t) t :=
    fun t ht => (hdY t ht).sub (hlin t (Ici t))
  have hdZ' : ∀ t ∈ Ico 0 b, HasDerivWithinAt Z' (Y'' t) (Ici t) t :=
    fun t ht => (hdY' t ht).sub_const w
  have hZ0 : ‖Z 0‖ ≤ 0 := by simp [hZ, h0]
  have hZ'0 : ‖Z' 0‖ ≤ 0 := by simp [hZ', h0']
  have hboundZ : ∀ t ∈ Ico 0 b, ‖Y'' t‖ ≤ K * ‖Z t‖ + K * (b * ‖w‖) := by
    intro t ht
    have hYt : Y t = Z t + t • w := by simp [hZ]
    have htb : |t| ≤ b := by
      rw [abs_of_nonneg ht.1]; exact ht.2.le
    calc ‖Y'' t‖ ≤ K * ‖Y t‖ := hbound t ht
      _ = K * ‖Z t + t • w‖ := by rw [← hYt]
      _ ≤ K * (‖Z t‖ + ‖t • w‖) :=
          mul_le_mul_of_nonneg_left (norm_add_le _ _) hK
      _ = K * ‖Z t‖ + K * (|t| * ‖w‖) := by
          rw [norm_smul, Real.norm_eq_abs]; ring
      _ ≤ K * ‖Z t‖ + K * (b * ‖w‖) := by
          have := mul_le_mul_of_nonneg_right htb (norm_nonneg w)
          nlinarith
  exact norm_le_gronwall_secondOrder hK heps hcZ hcZ' hdZ hdZ' hboundZ hZ0 hZ'0

/-- **Nonvanishing of a Jacobi-type solution below the Grönwall scale.**  If the
linearisation dominates the Grönwall error at the endpoint —
`gronwallBound 0 (max K 1) (K·b·‖w‖) b < b‖w‖` — then `Y b ≠ 0`.  This is the
analytic heart of the nonsingularity of `d exp` below the conjugate scale: the
Jacobi field with initial data `(0, w)` cannot return to zero while the
curvature-size `K` is small against the window `b`. -/
theorem gronwall_ne_zero
    {Y Y' Y'' : ℝ → E} {K b : ℝ} {w : E}
    (hK : 0 ≤ K) (hb : 0 < b)
    (hcY : ContinuousOn Y (Icc 0 b))
    (hcY' : ContinuousOn Y' (Icc 0 b))
    (hdY : ∀ t ∈ Ico 0 b, HasDerivWithinAt Y (Y' t) (Ici t) t)
    (hdY' : ∀ t ∈ Ico 0 b, HasDerivWithinAt Y' (Y'' t) (Ici t) t)
    (hbound : ∀ t ∈ Ico 0 b, ‖Y'' t‖ ≤ K * ‖Y t‖)
    (h0 : Y 0 = 0) (h0' : Y' 0 = w)
    (hsmall : gronwallBound 0 (max K 1) (K * (b * ‖w‖)) b < b * ‖w‖) :
    Y b ≠ 0 := by
  intro hYb
  have h := gronwall_sub_linear hK hb.le hcY hcY' hdY hdY' hbound h0 h0' b
    ⟨hb.le, le_rfl⟩
  rw [hYb, zero_sub, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos hb] at h
  exact absurd h (not_le.mpr hsmall)

end DifferentialGeometry
