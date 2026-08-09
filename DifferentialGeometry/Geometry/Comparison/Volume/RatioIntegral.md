# RatioIntegral.lean — brick B4 (§5 truncated ratio-of-integrals, γ)

## Role
Pure measure-theoretic input for capped relative Bishop–Gromov (brick B5).
No geometry imports. Delivers the multiplicative `ℝ≥0∞` cross-inequality and
the two feeders that adapt it to B5's inputs (antitone real ratio; cut-time
truncation).

The segment-interior route no longer selects a cut time.  It works directly on
the positive-radius subtype with a measurable downward-closed launch set.

## Deliverables (all in namespace `...Riemannian.VolumeComparison`)
- `CrossAnti R f g : Prop` — division-free `ℝ≥0∞` encoding of "`f/g` antitone on
  `(0,R]`": `∀ a b, 0 < a → a ≤ b → b ≤ R → f b * g a ≤ f a * g b`. Factored as a
  `def` so the three lemmas compose (B5 pipeline: `crossAnti_ofReal` →
  `crossAnti_indicator` → `lintegral_cross_le`).
- `lintegral_cross_le` (main): `(∫ f over (0,R])*(∫ g over (0,s]) ≤
  (∫ f over (0,s])*(∫ g over (0,R])` for `0 ≤ s ≤ R`, hypotheses
  `AEMeasurable f/g (μ.restrict (Ioc 0 R))` + `CrossAnti R f g`. General
  measure `μ : Measure ℝ` (Lebesgue not required).
- `crossAnti_ofReal` (bridge, part 2): `AntitoneOn (F/G) (Ioc 0 R)` + `F ≥ 0`,
  `G > 0` on the window ⟹ `CrossAnti R (ofReal∘F) (ofReal∘G)`.
- `crossAnti_indicator` (truncation, part 3): `CrossAnti R f g →
  CrossAnti R (indicator (Iio τ) f) g` for any `τ` (lower-set argument).
- `crossIic_indic`: the order-generic lower-set form.  If `S` is downward
  closed, cutting the numerator by `S` preserves a pointwise cross inequality
  on `Iic R`:
  ```lean
  (∀ ⦃a b⦄, a ≤ b → b ≤ R → f b * g a ≤ f a * g b) →
  (∀ ⦃a b⦄, a ≤ b → b ∈ S → a ∈ S) →
  ∀ ⦃a b⦄, a ≤ b → b ≤ R →
    S.indicator f b * g a ≤ S.indicator f a * g b
  ```
- `lintegral_Iic_cross`: the corresponding order-generic integral theorem on
  nested `Iic s ⊆ Iic R`.  In the volume lane it applies directly to
  `α = Ioi 0` and `μ = volumeIoiPow d`, avoiding a pushforward to `ℝ`.  Its
  only data hypotheses are `AEMeasurable f/g` on `μ.restrict (Iic R)`, the
  displayed pointwise cross inequality, and `s ≤ R`; the conclusion is
  ```lean
  (∫⁻ t in Iic R, f t ∂μ) * (∫⁻ t in Iic s, g t ∂μ) ≤
    (∫⁻ t in Iic s, f t ∂μ) * ∫⁻ t in Iic R, g t ∂μ
  ```

## Mathlib search (done first, per brick instructions)
No integral-form Chebyshev / monovary ratio inequality exists in Mathlib's
MeasureTheory tree. Chebyshev's inequality is finset-only
(`Mathlib/Algebra/Order/Chebyshev.lean`); `MonovaryOn` has no integral form;
`LpSeminorm/ChebyshevMarkov.lean` and `Integral/Lebesgue/Markov.lean` are the
tail-bound Markov/Chebyshev, unrelated. Conclusion: prove from scratch. The
in-tree `localBall_cross` (`BishopLocal.lean:141`) is the untruncated,
chart-bound analog (same product shape `V(R)·v(r) ≤ V(r)·v(R)`) — shape pattern
only, not reusable here.

## Route (from scratch, division-free)
Split `Ioc 0 R = Ioc 0 s ∪ Ioc s R` (disjoint). Distribute
`(If+Jf)*Ig ≤ If*(Ig+Jg)`; the common `If*Ig` is ADDED (never subtracted — `∞-∞`
safe) via `add_le_add le_rfl _`, reducing to `Jf*Ig ≤ If*Jg`. Reshape both
products into the SAME iterated integral over `(s,R] × (0,s]`:
`Jf*Ig = ∫_B ∫_A f b * g a`, `If*Jg = ∫_B ∫_A f a * g b`, using
`lintegral_const_mul''` / `lintegral_mul_const''` (AEMeasurable form) under
`lintegral_congr`. Compare integrands pointwise by `hcross` (for `a ∈ (0,s]`,
`b ∈ (s,R]`: `0 < a`, `a ≤ s < b` ⟹ `a ≤ b`, `b ≤ R`) via nested
`lintegral_mono_ae` + `ae_restrict_mem`. Bridge = `div_le_div_iff₀` +
`ENNReal.ofReal_mul` (needs `F ≥ 0`) + `ofReal_le_ofReal`. Truncation = case
split on `b ∈ Iio τ` (`a ≤ b` keeps `a ∈ Iio τ`; else numerator is `0`).

## Key Mathlib lemmas used
`Set.Ioc_union_Ioc_eq_Ioc`, `Ioc_disjoint_Ioc_of_le`, `Ioc_subset_Ioc`,
`lintegral_union`, `lintegral_const_mul''` / `lintegral_mul_const''`,
`lintegral_congr`, `lintegral_mono_ae`, `ae_restrict_mem`,
`AEMeasurable.mono_measure` + `Measure.restrict_mono`, `add_le_add`,
`div_le_div_iff₀`, `ENNReal.ofReal_mul`, `ENNReal.ofReal_le_ofReal`,
`Set.indicator_of_mem` / `Set.indicator_of_notMem`.

## Pitfalls paid
- `add_le_add_left hstar _` resolved with the wrong orientation (added the
  common term on the RIGHT). Use `add_le_add le_rfl hstar` (common term on the
  left, unambiguous).
- `Set.indicator_of_not_mem` was renamed to `Set.indicator_of_notMem`.

## Verification
Focused check PASSED; targeted module build PASSED (sorry-free, no new axioms,
no new imports beyond Mathlib measure-theory/order/ENNReal). Endpoint reminder:
B4 is machinery — the A0′ producer `volInput_of_bg` remains 0% until B5–B7 land.

The generic downward-set and `Iic` extensions are focused-check verified.  They
add no geometry or selected-cut-time assumptions.  `segBall_vol_rel` itself
remains a separate theorem frontier until the polar assembly uses them.
