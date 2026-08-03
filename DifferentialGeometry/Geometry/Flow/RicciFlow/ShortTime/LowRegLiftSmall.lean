import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.BochnerL2

/-!
# The closed horizon on which the adjacent-scale lift contracts

`lowreg_lift_two` (`ShortTime/LowRegLiftTwo.lean`) — and behind it
`nonautL2_lift` — carries two contraction hypotheses of the shape

```
(C₂ : ℝ) * (1 + T) + 2 * Real.sqrt (1 + T) * ‖hA1.toLp A1‖ < 1
```

one at the high scale (`hsmallHi`) and one at the low scale (`hsmallLo`).
This file supplies the closed horizon on which both hold, and the arithmetic
that proves them.

## What drives the two terms

* the zeroth term is **not** small in `T`: `C₂ * (1 + T) → C₂` as `T → 0`, so
  the second-order coefficient bound must satisfy `C₂ < 1` outright.  That is
  the radius-side smallness (`‖A2‖ ≤ C₂ρ` with `ρ` chosen small), not a
  horizon-side one;
* the first term **is** small in `T`, but only through the time-`L²` norm of
  `A1`.  The producer shape is a pointwise operator bound `‖A1 t‖ ≤ M`, which
  gives `‖A1‖_{L²(0,T)} ≤ M √T` (`norm_toLp_le_bd`); equivalently the affine
  output of `memLp_clm_affine`, `‖A1‖_{L²} ≤ L‖u‖_{L²} + √T Z₀`, combined with
  a pointwise state bound `‖u‖_{L²} ≤ √T K`, gives the same `M √T` shape with
  `M = L K + Z₀` (`norm_le_of_affine`).

## The closed horizon

```
lowregLiftHorizon c M =
  min 1 (min ((1 - c) / (2 * (c + 1))) ((1 - c) ^ 2 / (64 * (M + 1) ^ 2)))
```

where `c` is any upper bound for both `C₂` bounds and `M` any upper bound for
both `L²`-in-time constants.  The first cap makes `c * (1 + T) ≤ (1 + c) / 2`,
i.e. it spends half of the remaining budget `1 - c`; the second makes
`√T ≤ (1 - c) / (8 (M + 1))`, so the first-order term is at most
`3 (1 - c) / 8`.  The total is at most `(7 + c) / 8 < 1`.

The horizon is positive whenever `0 ≤ c < 1` and `0 ≤ M`, is antitone in both
arguments (`lowregLiftHorizon_mono`), and is `≤ 1`, so it composes with the
Lane-A existence time by a plain `min`.

The shape mirrors `partial_sol_tame`'s `1 / (64 (B + 1) ^ 2)` cap and
`lowregHorizon` (`ShortTime/UnifClassBounds.lean`): a `(… + 1)` denominator
avoids dividing by a constant that may vanish.
-/

noncomputable section

open MeasureTheory Filter
open scoped NNReal ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry.Analysis.Parabolic.TimeSobolev

/-! ### The closed horizon -/

/-- The closed horizon on which both contraction conditions of `nonautL2_lift`
hold, as a function of an upper bound `c` for the uniform second-order
coefficient bound `C₂` and an upper bound `M` for the time-`L²` growth constant
of the first-order coefficient family (`‖A1‖_{L²(0,T)} ≤ M √T`). -/
def lowregLiftHorizon (c M : ℝ) : ℝ :=
  min 1 (min ((1 - c) / (2 * (c + 1))) ((1 - c) ^ 2 / (64 * (M + 1) ^ 2)))

theorem lowregLiftHorizon_le_one {c M : ℝ} : lowregLiftHorizon c M ≤ 1 :=
  min_le_left _ _

/-- The second-order cap: it spends half of the budget `1 - c` on `c * T`. -/
theorem lowregLiftHorizon_le_c2 {c M : ℝ} :
    lowregLiftHorizon c M ≤ (1 - c) / (2 * (c + 1)) :=
  le_trans (min_le_right _ _) (min_le_left _ _)

/-- The first-order cap: it forces `√T ≤ (1 - c) / (8 (M + 1))`. -/
theorem lowregLiftHorizon_le_a1 {c M : ℝ} :
    lowregLiftHorizon c M ≤ (1 - c) ^ 2 / (64 * (M + 1) ^ 2) :=
  le_trans (min_le_right _ _) (min_le_right _ _)

/-- The horizon is positive exactly under the sign conditions the lift needs:
the second-order bound is a genuine contraction (`c < 1`) and the first-order
constant is nonnegative. -/
theorem lowregLiftHorizon_pos {c M : ℝ} (hc0 : 0 ≤ c) (hc1 : c < 1)
    (hM : 0 ≤ M) : 0 < lowregLiftHorizon c M := by
  have h1c : (0 : ℝ) < 1 - c := by linarith
  have hc : (0 : ℝ) < c + 1 := by linarith
  have hM1 : (0 : ℝ) < M + 1 := by linarith
  exact lt_min one_pos (lt_min (by positivity) (by positivity))

/-- The horizon is antitone in both constants: primed inputs are the *worse*
ones (a larger second-order bound, a larger first-order `L²` constant), and
they give a shorter horizon.  So a class-uniform bound on `C₂` and `M` yields a
class-uniform positive lift horizon. -/
theorem lowregLiftHorizon_mono {c c' M M' : ℝ} (hc0 : 0 ≤ c) (hc1' : c' < 1)
    (hM : 0 ≤ M) (hcc : c ≤ c') (hMM : M ≤ M') :
    lowregLiftHorizon c' M' ≤ lowregLiftHorizon c M := by
  have h1c' : (0 : ℝ) ≤ 1 - c' := by linarith
  have hM1 : (0 : ℝ) < M + 1 := by linarith
  have hM1' : (0 : ℝ) < M' + 1 := by linarith
  refine min_le_min le_rfl (min_le_min ?_ ?_)
  · have hden : (0 : ℝ) < 2 * (c + 1) := by linarith
    have hden' : (0 : ℝ) < 2 * (c' + 1) := by linarith
    rw [div_le_div_iff₀ hden' hden]
    nlinarith
  · have hd : (0 : ℝ) < 64 * (M + 1) ^ 2 := by positivity
    have hd' : (0 : ℝ) < 64 * (M' + 1) ^ 2 := by positivity
    rw [div_le_div_iff₀ hd' hd]
    have h1 : (1 - c') ^ 2 ≤ (1 - c) ^ 2 := by nlinarith
    have h2 : 64 * (M + 1) ^ 2 ≤ 64 * (M' + 1) ^ 2 := by nlinarith
    exact mul_le_mul h1 h2 hd.le (sq_nonneg _)

/-! ### The arithmetic of the two contraction conditions -/

/-- **The lift smallness, as pure arithmetic.**  On the closed horizon
`lowregLiftHorizon c M`, any second-order bound `C ≤ c` and any first-order
time-`L²` size `N ≤ M √T` satisfy the contraction condition of `nonautL2_lift`.

The proof is the budget split described in the module docstring: the total is
at most `c + (1 - c)/2 + 3(1 - c)/8 = (7 + c)/8`, which is `< 1` precisely
because `c < 1`. -/
theorem lift_small_arith {c M T C N : ℝ}
    (hc0 : 0 ≤ c) (hc1 : c < 1) (hM : 0 ≤ M)
    (hT : 0 < T) (hTle : T ≤ lowregLiftHorizon c M)
    (hCc : C ≤ c)
    (hN0 : 0 ≤ N) (hN : N ≤ M * Real.sqrt T) :
    C * (1 + T) + 2 * Real.sqrt (1 + T) * N < 1 := by
  have h1c : (0 : ℝ) < 1 - c := by linarith
  have hM1 : (0 : ℝ) < M + 1 := by linarith
  have hT1 : T ≤ 1 := hTle.trans lowregLiftHorizon_le_one
  have hs0 : (0 : ℝ) ≤ Real.sqrt T := Real.sqrt_nonneg _
  -- The second-order term spends half of the budget `1 - c`.
  have hTa : T ≤ (1 - c) / (2 * (c + 1)) := hTle.trans lowregLiftHorizon_le_c2
  have hcT : c * T ≤ (1 - c) / 2 := by
    have hden : (0 : ℝ) < 2 * (c + 1) := by linarith
    rw [le_div_iff₀ hden] at hTa
    nlinarith
  -- On a horizon `≤ 1` the parabolic weight is bounded by `3/2`.
  have hq : Real.sqrt (1 + T) ≤ 3 / 2 := by
    have h := Real.sqrt_le_sqrt (show 1 + T ≤ (3 / 2 : ℝ) ^ 2 by nlinarith)
    rwa [Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 3 / 2)] at h
  -- The first-order cap in the form `√T ≤ (1 - c) / (8 (M + 1))`.
  have hTb : T ≤ (1 - c) ^ 2 / (64 * (M + 1) ^ 2) :=
    hTle.trans lowregLiftHorizon_le_a1
  have hsq : ((1 - c) / (8 * (M + 1))) ^ 2 = (1 - c) ^ 2 / (64 * (M + 1) ^ 2) := by
    rw [div_pow, mul_pow]
    norm_num
  have hs : Real.sqrt T ≤ (1 - c) / (8 * (M + 1)) := by
    have h := Real.sqrt_le_sqrt (hTb.trans_eq hsq.symm)
    rwa [Real.sqrt_sq (by positivity)] at h
  have hs' : Real.sqrt T * (8 * (M + 1)) ≤ 1 - c := by
    rw [← le_div_iff₀ (by linarith : (0 : ℝ) < 8 * (M + 1))]
    exact hs
  -- The first-order term spends at most `3/8` of the budget `1 - c`.
  have hfirst : Real.sqrt (1 + T) * N ≤ 3 / 2 * (M * Real.sqrt T) :=
    mul_le_mul hq hN hN0 (by norm_num)
  have hthird : 3 * (M * Real.sqrt T) ≤ 3 * (1 - c) / 8 := by nlinarith
  have hCT : C * T ≤ c * T := mul_le_mul_of_nonneg_right hCc hT.le
  rw [show C * (1 + T) = C + C * T from by ring]
  linarith

/-! ### From a pointwise operator bound to the time-`L²` size -/

/-- A pointwise-a.e. norm bound `M` on a time-`L²` family gives the `L²`-in-time
bound `M √T`.  This is the general-codomain form of
`timeL2_norm_le_of_ae_bound`: the first-order coefficient family takes values in
an *operator* space, which is not an inner-product space, so the `timeL2`
version does not apply.

Canonical home if this gets reused: `Analysis/Parabolic/TimeSobolev/BochnerL2`. -/
theorem norm_toLp_le_bd {T : ℝ} {Z : Type*} [NormedAddCommGroup Z]
    {A : ℝ → Z} (hA : MemLp A 2 (timeMeasure T)) {M : ℝ} (hM : 0 ≤ M)
    (hbd : ∀ᵐ t ∂timeMeasure T, ‖A t‖ ≤ M) :
    ‖hA.toLp A‖ ≤ M * Real.sqrt T := by
  rw [Lp.norm_toLp]
  have hle := eLpNorm_le_of_ae_bound (μ := timeMeasure T) (p := 2) hbd
  refine le_trans (ENNReal.toReal_mono ?_ hle) ?_
  · exact ENNReal.mul_ne_top
      (by rw [timeMeasure_univ]
          exact ENNReal.rpow_ne_top_of_nonneg (by norm_num) (by finiteness))
      ENNReal.ofReal_ne_top
  · rw [ENNReal.toReal_mul, timeMeasure_univ,
      show ((2 : ℝ≥0∞).toReal)⁻¹ = (1 / 2 : ℝ) by norm_num,
      toReal_ofReal_rpow_half, ENNReal.toReal_ofReal hM]
    exact le_of_eq (mul_comm _ _)

/-- The affine time-`L²` bound produced by `memLp_clm_affine`
(`‖A‖_{L²} ≤ L ‖u‖_{L²} + √T Z₀`), combined with a `√T`-type bound on the state
field, is again of the `M √T` shape with `M = L K + Z₀`. -/
theorem norm_le_of_affine {T L Z₀ K U V : ℝ} (hL : 0 ≤ L)
    (hU : U ≤ Real.sqrt T * K) (hV : V ≤ L * U + Real.sqrt T * Z₀) :
    V ≤ (L * K + Z₀) * Real.sqrt T := by
  nlinarith [mul_le_mul_of_nonneg_left hU hL]

/-! ### The two contraction conditions of `lowreg_lift_two` -/

/-- **One contraction condition, in the exact shape consumed by
`lowreg_lift_two` / `nonautL2_lift`.** -/
theorem lift_small_toLp {T c M : ℝ} {Z : Type*} [NormedAddCommGroup Z]
    {A1 : ℝ → Z} (hA1 : MemLp A1 2 (timeMeasure T))
    {C2 : ℝ≥0} (hC2 : (C2 : ℝ) ≤ c)
    (hc0 : 0 ≤ c) (hc1 : c < 1) (hM : 0 ≤ M)
    (hT : 0 < T) (hTle : T ≤ lowregLiftHorizon c M)
    (hnorm : ‖hA1.toLp A1‖ ≤ M * Real.sqrt T) :
    (C2 : ℝ) * (1 + T) + 2 * Real.sqrt (1 + T) * ‖hA1.toLp A1‖ < 1 :=
  lift_small_arith hc0 hc1 hM hT hTle hC2 (norm_nonneg _) hnorm

/-- The same, starting from the *pointwise* operator bound that the low-base
coefficient producers actually deliver. -/
theorem lift_small_of_bd {T c M : ℝ} {Z : Type*} [NormedAddCommGroup Z]
    {A1 : ℝ → Z} (hA1 : MemLp A1 2 (timeMeasure T))
    {C2 : ℝ≥0} (hC2 : (C2 : ℝ) ≤ c)
    (hc0 : 0 ≤ c) (hc1 : c < 1) (hM : 0 ≤ M)
    (hT : 0 < T) (hTle : T ≤ lowregLiftHorizon c M)
    (hbd : ∀ᵐ t ∂timeMeasure T, ‖A1 t‖ ≤ M) :
    (C2 : ℝ) * (1 + T) + 2 * Real.sqrt (1 + T) * ‖hA1.toLp A1‖ < 1 :=
  lift_small_toLp hA1 hC2 hc0 hc1 hM hT hTle (norm_toLp_le_bd hA1 hM hbd)

/-- **Both contraction conditions at once**, in exactly the shapes of
`hsmallHi` and `hsmallLo` of `lowreg_lift_two`.  The two scales share a single
horizon: `c` bounds both uniform second-order coefficient bounds and `M` bounds
both first-order time-`L²` constants (take maxima and use
`lowregLiftHorizon_mono` if the two lanes report different numbers).

The high and low coefficient families live at different Sobolev scales, hence
in different operator spaces, which is why `ZHi` and `ZLo` are separate type
variables. -/
theorem lift_smallness {T c M : ℝ} {ZHi ZLo : Type*}
    [NormedAddCommGroup ZHi] [NormedAddCommGroup ZLo]
    {A1Hi : ℝ → ZHi} (hA1Hi : MemLp A1Hi 2 (timeMeasure T))
    {A1Lo : ℝ → ZLo} (hA1Lo : MemLp A1Lo 2 (timeMeasure T))
    {C2Hi C2Lo : ℝ≥0} (hC2Hi : (C2Hi : ℝ) ≤ c) (hC2Lo : (C2Lo : ℝ) ≤ c)
    (hc0 : 0 ≤ c) (hc1 : c < 1) (hM : 0 ≤ M)
    (hT : 0 < T) (hTle : T ≤ lowregLiftHorizon c M)
    (hHi : ‖hA1Hi.toLp A1Hi‖ ≤ M * Real.sqrt T)
    (hLo : ‖hA1Lo.toLp A1Lo‖ ≤ M * Real.sqrt T) :
    ((C2Hi : ℝ) * (1 + T) + 2 * Real.sqrt (1 + T) * ‖hA1Hi.toLp A1Hi‖ < 1) ∧
      ((C2Lo : ℝ) * (1 + T) +
        2 * Real.sqrt (1 + T) * ‖hA1Lo.toLp A1Lo‖ < 1) :=
  ⟨lift_small_toLp hA1Hi hC2Hi hc0 hc1 hM hT hTle hHi,
    lift_small_toLp hA1Lo hC2Lo hc0 hc1 hM hT hTle hLo⟩

/-- The pointwise-bound form of `lift_smallness`. -/
theorem lift_small_two_bd {T c M : ℝ} {ZHi ZLo : Type*}
    [NormedAddCommGroup ZHi] [NormedAddCommGroup ZLo]
    {A1Hi : ℝ → ZHi} (hA1Hi : MemLp A1Hi 2 (timeMeasure T))
    {A1Lo : ℝ → ZLo} (hA1Lo : MemLp A1Lo 2 (timeMeasure T))
    {C2Hi C2Lo : ℝ≥0} (hC2Hi : (C2Hi : ℝ) ≤ c) (hC2Lo : (C2Lo : ℝ) ≤ c)
    (hc0 : 0 ≤ c) (hc1 : c < 1) (hM : 0 ≤ M)
    (hT : 0 < T) (hTle : T ≤ lowregLiftHorizon c M)
    (hHi : ∀ᵐ t ∂timeMeasure T, ‖A1Hi t‖ ≤ M)
    (hLo : ∀ᵐ t ∂timeMeasure T, ‖A1Lo t‖ ≤ M) :
    ((C2Hi : ℝ) * (1 + T) + 2 * Real.sqrt (1 + T) * ‖hA1Hi.toLp A1Hi‖ < 1) ∧
      ((C2Lo : ℝ) * (1 + T) +
        2 * Real.sqrt (1 + T) * ‖hA1Lo.toLp A1Lo‖ < 1) :=
  lift_smallness hA1Hi hA1Lo hC2Hi hC2Lo hc0 hc1 hM hT hTle
    (norm_toLp_le_bd hA1Hi hM hHi) (norm_toLp_le_bd hA1Lo hM hLo)

/-! ### The affine first-order size

The refolded first-order families do not come with a pointwise operator bound
that a producer can supply: maximal regularity controls the low trajectory only
in `L²_t H³`, so the honest certificate is the affine time-`L²` bound of
`memLp_clm_affine`,

```
‖A1‖_{L²(0,T)} ≤ A + √T · Z,   A = L · ‖duhH3‖ ≲ L · ‖f‖.
```

Only the second summand is small in `T`; the first is a genuine radius-side
smallness, exactly like the second-order term `C₂`.  So the horizon absorbs `Z`
alone and `A` is capped by the separate `T`-free margin `6 A < 1 - c`. -/

/-- The closed horizon for a first-order family whose time-`L²` size is only
*affine* in `√T` (`‖A1‖ ≤ A + √T · Z`).  Only the `√T`-carrying constant `Z`
enters; the `√T`-free part `A` is capped by the margin of `lift_aff_arith`.

The budget split is `c·T ≤ (1-c)/4` from the first cap and
`3·√T·Z ≤ (1-c)/4` from the second, leaving `(1-c)/2` for `3A`. -/
def lowregLiftHorizon' (c Z : ℝ) : ℝ :=
  min 1 (min ((1 - c) / (4 * (c + 1))) ((1 - c) ^ 2 / (144 * (Z + 1) ^ 2)))

theorem lowregLiftHorizon'_le_one {c Z : ℝ} : lowregLiftHorizon' c Z ≤ 1 :=
  min_le_left _ _

/-- The affine horizon is positive under the same sign conditions as
`lowregLiftHorizon`: a genuine second-order contraction (`c < 1`) and a
nonnegative zeroth-order size. -/
theorem lowregLiftHorizon'_pos {c Z : ℝ} (hc0 : 0 ≤ c) (hc1 : c < 1)
    (hZ : 0 ≤ Z) : 0 < lowregLiftHorizon' c Z := by
  have h1c : (0 : ℝ) < 1 - c := by linarith
  have hc : (0 : ℝ) < c + 1 := by linarith
  have hZ1 : (0 : ℝ) < Z + 1 := by linarith
  exact lt_min one_pos (lt_min (by positivity) (by positivity))

/-- **The lift smallness from an affine first-order size, as pure arithmetic.**
On the horizon `lowregLiftHorizon' c Z`, a second-order bound `C ≤ c` and a
first-order time-`L²` size `V ≤ A + √T · Z` whose `√T`-free part obeys the
margin `6 A < 1 - c` satisfy the contraction condition of `nonautL2_lift`.

The total is at most `c + (1-c)/4 + 3A + (1-c)/4 < c + (1-c) = 1`. -/
theorem lift_aff_arith {c A Z T C V : ℝ}
    (hc0 : 0 ≤ c) (hc1 : c < 1) (hZ : 0 ≤ Z)
    (hA : 6 * A < 1 - c)
    (hT : 0 < T) (hTle : T ≤ lowregLiftHorizon' c Z)
    (hCc : C ≤ c) (hV0 : 0 ≤ V) (hV : V ≤ A + Real.sqrt T * Z) :
    C * (1 + T) + 2 * Real.sqrt (1 + T) * V < 1 := by
  have h1c : (0 : ℝ) < 1 - c := by linarith
  have hZ1 : (0 : ℝ) < Z + 1 := by linarith
  have hT1 : T ≤ 1 := hTle.trans lowregLiftHorizon'_le_one
  have hs0 : (0 : ℝ) ≤ Real.sqrt T := Real.sqrt_nonneg _
  -- The second-order term spends a quarter of the budget `1 - c`.
  have hTa : T ≤ (1 - c) / (4 * (c + 1)) :=
    hTle.trans (le_trans (min_le_right _ _) (min_le_left _ _))
  have hcT : c * T ≤ (1 - c) / 4 := by
    have hden : (0 : ℝ) < 4 * (c + 1) := by linarith
    rw [le_div_iff₀ hden] at hTa
    nlinarith
  -- On a horizon `≤ 1` the parabolic weight is bounded by `3/2`.
  have hq : Real.sqrt (1 + T) ≤ 3 / 2 := by
    have h := Real.sqrt_le_sqrt (show 1 + T ≤ (3 / 2 : ℝ) ^ 2 by nlinarith)
    rwa [Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 3 / 2)] at h
  -- The zeroth-order cap in the form `√T ≤ (1 - c) / (12 (Z + 1))`.
  have hTb : T ≤ (1 - c) ^ 2 / (144 * (Z + 1) ^ 2) :=
    hTle.trans (le_trans (min_le_right _ _) (min_le_right _ _))
  have hsq : ((1 - c) / (12 * (Z + 1))) ^ 2 =
      (1 - c) ^ 2 / (144 * (Z + 1) ^ 2) := by
    rw [div_pow, mul_pow]
    norm_num
  have hs : Real.sqrt T ≤ (1 - c) / (12 * (Z + 1)) := by
    have h := Real.sqrt_le_sqrt (hTb.trans_eq hsq.symm)
    rwa [Real.sqrt_sq (by positivity)] at h
  have hs' : Real.sqrt T * (12 * (Z + 1)) ≤ 1 - c := by
    rw [← le_div_iff₀ (by linarith : (0 : ℝ) < 12 * (Z + 1))]
    exact hs
  have hzT : 3 * (Real.sqrt T * Z) ≤ (1 - c) / 4 := by nlinarith
  have hfirst : Real.sqrt (1 + T) * V ≤ 3 / 2 * V :=
    mul_le_mul_of_nonneg_right hq hV0
  have hCT : C * T ≤ c * T := mul_le_mul_of_nonneg_right hCc hT.le
  rw [show C * (1 + T) = C + C * T from by ring]
  linarith

/-- **One contraction condition from the affine time-`L²` certificate**, in the
exact shape consumed by `lowreg_lift_two` / `nonautL2_lift`.  This is the
`memLp_clm_affine` companion of `lift_small_toLp`: the producer supplies the
affine bound `‖A1‖_{L²} ≤ A + √T · Z` instead of a pointwise operator bound,
and the caller supplies the `T`-free margin `6 A < 1 - c`. -/
theorem lift_small_aff {T c A Z : ℝ} {Y : Type*} [NormedAddCommGroup Y]
    {A1 : ℝ → Y} (hA1 : MemLp A1 2 (timeMeasure T))
    {C2 : ℝ≥0} (hC2 : (C2 : ℝ) ≤ c)
    (hc0 : 0 ≤ c) (hc1 : c < 1) (hZ : 0 ≤ Z)
    (hA : 6 * A < 1 - c)
    (hT : 0 < T) (hTle : T ≤ lowregLiftHorizon' c Z)
    (hnorm : ‖hA1.toLp A1‖ ≤ A + Real.sqrt T * Z) :
    (C2 : ℝ) * (1 + T) + 2 * Real.sqrt (1 + T) * ‖hA1.toLp A1‖ < 1 :=
  lift_aff_arith hc0 hc1 hZ hA hT hTle hC2 (norm_nonneg _) hnorm

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
