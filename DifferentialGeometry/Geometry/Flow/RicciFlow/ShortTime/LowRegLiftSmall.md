# LowRegLiftSmall

The horizon-smallness producer for Lane C: it discharges `hsmallHi` and
`hsmallLo` of `lowreg_lift_two` (`ShortTime/LowRegLiftTwo.lean`), i.e. the two
contraction hypotheses of `nonautL2_lift`.

## What is in this file

* `lowregLiftHorizon c M` — the closed horizon
  `min 1 (min ((1 - c) / (2 * (c + 1))) ((1 - c) ^ 2 / (64 * (M + 1) ^ 2)))`,
  with `lowregLiftHorizon_le_one`, `_le_c2`, `_le_a1`, `_pos`, `_mono`.
* `lift_small_arith` — the pure-real arithmetic: on that horizon, `C ≤ c` and
  `N ≤ M √T` give `C (1 + T) + 2 √(1 + T) N < 1`.
* `norm_toLp_le_bd` — pointwise a.e. operator bound `M` ⟹ `‖toLp A‖ ≤ M √T`,
  for a *general* normed codomain.
* `norm_le_of_affine` — `memLp_clm_affine`'s affine output plus a `√T` state
  bound collapses to the same `M √T` shape with `M = L K + Z₀`.
* `lift_small_toLp`, `lift_small_of_bd` — one contraction condition in exactly
  the shape `lowreg_lift_two` demands (`NNReal` coefficient bound, `MemLp.toLp`
  norm).
* `lift_smallness`, `lift_small_two_bd` — both conditions at once, from a
  single horizon shared by the two adjacent scales.

All sorry-free and axiom-clean (`propext`, `Classical.choice`, `Quot.sound`).
Focused check passed and a real targeted module build passed. A throwaway probe
file checked that the statements are consumed *verbatim* at `lowreg_lift_two`'s
hypothesis shapes, at the concrete operator types
`tensorHs g 0 2 (aHi + 1) →L[ℝ] tensorHs g 0 2 aHi`; the probe was deleted
afterwards.

## Mathematical findings

**The `C₂` term is not a horizon condition.** The engine's smallness is
`C₂ (1 + T) + 2 √(1 + T) ‖A1‖_{L²(0,T)} < 1`. The first summand tends to `C₂`,
not to `0`, as `T → 0`. So shrinking the horizon can never rescue a
second-order coefficient bound with `C₂ ≥ 1`: `C₂ < 1` is a *radius* condition
(`‖A2‖ ≤ C₂ρ` with `ρ` small, `lowRegA2Total_data`), and the horizon only
controls the first-order term. The brief "the C₂·ρ part is < 1 by radius
choice" is exactly right, and it is a genuine standing hypothesis (`hc1 : c < 1`
in every statement here), not something the horizon buys.

**The `A1` term needs a `√T`-shaped producer bound, not a bare `L²` bound.**
`‖hA1.toLp A1‖` is the `L²` norm over `[0,T]`, and a hypothesis of the form
`‖A1‖_{L²(0,T)} ≤ M` with `M` independent of `T` does *not* vanish as `T → 0`
— it is compatible with `A1` concentrating near `t = 0`. The honest producer
shape is a pointwise operator bound, and the tree already delivers it:
`lowRegA1_memLp` (`TensorMaximalRegularity/LowRegOperatorTime.lean`) proves
`∀ᵐ t, ‖A1 t‖ ≤ Φ (1 + ‖field t‖)`, so a pointwise `H3` bound `K` on the
order-one solution field gives `M = Φ (1 + K)` and hence `‖A1‖_{L²} ≤ M √T`.
The alternative route through the `L²` conclusion of `memLp_clm_affine`
(`‖A1‖_{L²} ≤ Φ ‖field‖_{L²} + √T Φ`, currently discarded by `lowRegA1_memLp`
via `obtain ⟨hmem, -⟩`) collapses to the same shape once `‖field‖_{L²} ≤ √T K`;
that is `norm_le_of_affine`.

**The budget split.** With `c` bounding `C₂` and `M` bounding the `L²` constant:
the cap `T ≤ (1 - c)/(2(c + 1))` gives `c T ≤ (1 - c)/2` (using `c/(c+1) ≤ 1`,
which is why the `+1` denominator is there — `c` may be `0`); the cap
`T ≤ (1 - c)²/(64 (M + 1)²)` gives `√T ≤ (1 - c)/(8(M + 1))`, hence
`3 M √T ≤ 3(1 - c)/8`; and `T ≤ 1` gives `√(1 + T) ≤ 3/2`. Total:
`c + (1 - c)/2 + 3(1 - c)/8 = (7 + c)/8 < 1`. The slack is deliberate — `(7+c)/8`
leaves room if a later lane needs to absorb an extra constant into `M`.

## Lean lessons

* `lift_small_arith` does **not** need `0 ≤ C`: a negative second-order bound
  only helps. The `unusedVariables` linter caught the spurious hypothesis and
  it was dropped (weakest-assumptions rule).
* `timeL2_norm_le_of_ae_bound` (`LocallyLipschitzExistence.lean`) is stated for
  `timeL2 X T` and therefore demands `InnerProductSpace ℝ X`. The first-order
  coefficient family takes values in an *operator* space, which is not an inner
  product space, so that lemma does not apply; `norm_toLp_le_bd` is the
  general-codomain restatement (same proof skeleton:
  `Lp.norm_toLp` + `eLpNorm_le_of_ae_bound` + `timeMeasure_univ` +
  `toReal_ofReal_rpow_half`). Its canonical home is
  `Analysis/Parabolic/TimeSobolev/BochnerL2.lean`; it was kept local here to
  avoid a full-tree rebuild for a one-consumer helper. Move it if a second
  consumer appears.
* The file imports only `TimeSobolev/BochnerL2`, not `NonautonomousL2Lift`. The
  smallness condition mentions nothing but `timeMeasure`, `MemLp.toLp` and
  `ℝ≥0`, so keeping the import light makes this a cheap leaf; call sites that
  need both import both.
* `div_le_div_iff₀ h h'` (not the deprecated `div_le_div_iff`) plus `nlinarith`
  is the reliable route for the monotonicity of `(1 - c)/(2(c + 1))`; the
  cross-multiplied goal simplifies to `4(c' - c) ≥ 0`.
* `Real.sqrt_le_sqrt` composed with `Real.sqrt_sq` is the robust way to turn a
  quadratic cap into a `√T` bound; write the square in the form
  `((1 - c)/(8(M + 1)))^2` first (`div_pow`, `mul_pow`, `norm_num`) rather than
  fighting `Real.sqrt_le_iff`.

## Progress and what is still missing

* `ricci_flow_unif_existence`: unstated; still 0%.
* Lane-B packaging obstruction "horizon smallness": **closed** as a
  conditional producer. `lowreg_lift_two` can now be applied as soon as the two
  numeric inputs exist.
* What is *not* done here, and is the remaining Lane-B work:
  1. a witness for `c` — i.e. `lowRegA2Total_data`'s uniform bound must be
     shown `< 1` at the chosen coefficient radius (radius-side, not horizon);
  2. a witness for `M` — i.e. the pointwise `‖A1 t‖ ≤ M`, which is downstream
     of `lowRegA1_memLp`'s hypotheses `hcont` and `hlin` (the affine bound
     `Φ (1 + ‖v‖)`, still the outstanding low-base frontier — the tree's
     `remainder_low_pair` envelope is degree six) *and* of a pointwise `H3`
     bound on the order-one solution field;
  3. composing this horizon with the Lane-A existence time `lowregHorizon`
     (`UnifClassBounds.lean`) by a plain `min` — both are `≤ 1` and positive,
     so `min` is positive; no lemma was added for that since it is `lt_min`.
