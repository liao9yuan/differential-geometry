# CurvatureCoeffDiffRadiusFree — radius-free arm0 base coefficient jet-L² sibling

Consumer sibling of THE GATE (`boundedFactorGridWindow_integral_radiusFree_topSeparated`),
the 2nd brick of the Pro-ruled repair of UNIF item-2. See
`ShortTime/THREEARM_RECON.md` §11/§11b and `CurvatureCoefficientDifferenceJetTower.md`.

## Target

Radius-free sibling of `ricciArmOrder0BaseCoeff_perOrder_l2_topSeparated_generic`
(monolith :14808, whose `Kc` routes through the R-dependent ballUniform converter):
```
∑_{i≤a} ‖∇ⁱ(RiemannCoeff g₀ g₁ − CurvCoeff g₀ g₁)‖²
   ≤ Ktop·∑_{j≤a+2}‖∇ʲ(symmS g₀ T)‖² + Klow·(1 + ∑_{j≤a+1}‖∇ʲ(symmS g₀ T)‖²)
```
Ktop/Klow depend only on g₀/a/dim E/δ₀. NO R binder, NO ball hypothesis. Hyp: fibre
smallness `gFibreOpBound g₀ (ccTensorBilinSymm g₀ T) δ`, `δ ≤ δ₀`, `htie`.

## Route (why L²-level, why a new file)

The generic's ONLY R-dependence is the ballUniform integration `∫ boundedFactorGridWindow
≤ KI i·(1+low)` (monolith :14843). Everything else — the per-order head `Hd` (R-free
`Ktop` from the two `*_backgroundDifference_topSeparated_le` lemmas) and the pointwise
residual grid bound — is already R-free. Swap that ONE integration for THE GATE
(`∫ ≤ Klow·(1+low) + Ktop·‖∇^{i+2}‖²`, the top leak absorbing the capped antidiagonal
terms per the §11 pointwise-head caveat) and the whole thing is radius-free.

- **L²-level, not pointwise-head.** Instead of cloning the generic's pointwise
  `Hd`+`hpt` block (which needs the monolith-private `tsRfns_sub_le`,
  `exists_backgroundJet_rfns_bound`), bound `‖∇ⁱC‖²` via an L² 5-term triangle
  `∇ⁱC = ∇ⁱ(Rie g₀−Cu g₀) + (∇ⁱ(Rie g₁−g₀)−HdCr) + HdCr − (∇ⁱ(Cu g₁−g₀)−HdCu) − HdCu`,
  `sq_sum5_le`, then integrate each piece (`normSq_le_integral_of_pointwise_fiberNormSq_le_rs`)
  against the gate. Background jet is just the constant `‖∇ⁱ(Rie g₀−Cu g₀)‖²` — no private
  helper. This uses ONLY public API ⟹ lives in a NEW small file (fast iteration; the
  15.4k-line monolith would re-elaborate on every focused check). Respects the §11
  addendum: no pointwise-head API exposed, capped top terms land in the `Ktop` L² envelope.

- **symmS point.** The gate's `hsup` is fed by `rfns_symmS_zero_le_fibreSmall`, which
  controls only `symmS g₀ T`. So the background-difference lemmas are instantiated at
  `T := symmS g₀ T` (grids run over `symmS g₀ T`); `htie`/`hbound` transfer via the two
  local copies of `ccTensorBilinSymm_symmS_app` / `gFibreOpBound_ccTensorBilinSymm_symmS`
  (private in `DeTurckRemainderTameLipschitz`, 3-line re-derivations here). RHS jets are
  over `symmS g₀ T` (the geometrically correct perturbation).

- **abstract Λ₀ engine.** Per-order engine `..._perOrder_l2_radiusFree` mirrors the gate's
  design decision 1 (abstract Λ₀ + `hsup` hypothesis, decoupled from δ₀). Summed sibling
  `..._summed_l2_radiusFree` supplies `Λ₀ := max 0 (dim E·δ₀)` + `hsup` via the bridge and
  sums i≤a (per-order `Atop`/`Alow` collapse to `∑Atop`/`∑Alow`).

## Landed declarations

- `ricciArmOrder0BaseCoeff_perOrder_l2_radiusFree` — per-order engine (abstract Λ₀ + `hsup`).
- `ricciArmOrder0BaseCoeff_summed_l2_radiusFree` — summed deliverable (fibre smallness in,
  bridge applied inside, `Λ₀ := max 0 (dim E·δ₀)`, `Ktop/Klow = ∑Atop/∑Alow`).
- Local privates: `ccTensorBilinSymm_symmS_app_rf`, `gFibreOpBound_symmS_rf`, `sq_sum5_le`,
  `sum_shift_le_rf`.

## Status: GREEN (2026-07-26)

Targeted module build `Build completed successfully (9388 jobs)`, my module built clean
(`✔`, no warnings). `#print axioms` on both public theorems =
`[propext, Classical.choice, Quot.sound]` (no `sorryAx`).

## Lessons

- `intro` introduces implicit `{δ}` positionally: must name it (`intro g₁ T δ hδ_le …`),
  exactly as the R-dependent generic does. Omitting it silently shifts every later
  hypothesis and produces a cascade of type mismatches. (First failed check.)
- `pow_le_pow_left` is gone in this Mathlib. Stable replacement for `a² ≤ b²` from
  `0 ≤ a`, `a ≤ b`: `simp only [pow_two]; exact mul_self_le_mul_self ha hab`.
- Ordering matters for `set` folding: obtain the gate instance (`hgate … hsup i`) BEFORE
  `set W`/`set low`, so the gate bound and the goal RHS both fold to `W`/`low`.
- Placement rationale confirmed: the L²-5-term route uses ONLY public API, so a new small
  file iterates ~25s/check vs. re-elaborating the 15.4k-line monolith. The pointwise-`hpt`
  clone route would have needed the monolith-private `tsRfns_sub_le` /
  `exists_backgroundJet_rfns_bound`, forcing an in-monolith edit.
