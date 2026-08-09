# LowRegFatouMass — F4 FATOU-ASSEMBLE

**Status: green, sorry-free, censused (2026-08-05).**  Verification passed:
focused check green, targeted build "Build completed successfully", census
`[propext, Classical.choice, Quot.sound]` only.

## What this file is

The closing brick of the (N) campaign's Fatou stage.  It takes the two
conjuncts `lowregFatouPack` (`LowRegFatouIdent.lean`) hands out — the per-mode
convergence and the `N`-uniform rung-3 energy bound — and closes them with
`fatou_sq_mass` (`Analysis/Spectral/Intrinsic/GalerkinCompactness.lean:28–34`),
producing a `σ`-weighted spectral-mass bound on the **limit** forcing for every
`σ ≤ 3`.

Endpoint: `lowregMassLow`.

## Why a sibling file and not more of `LowRegFatouIdent.lean`

Abstraction boundary, not line count (`LowRegFatouIdent.lean` is ≈640 lines,
far under the cap).  `LowRegFatouIdent.lean` is *identification*: it says what
the projected trajectory is and what bound it satisfies.  This file is
*assembly*: it forgets the trajectory entirely and only uses the two Fatou
inputs.  It also carries the only import of
`Analysis/Spectral/Intrinsic/GalerkinCompactness.lean` in the ShortTime tree,
which does not belong in the identification file.

## The proof, in three lines

1. Destructure `lowregFatouPack` — one call, one tuple of constants; this is
   the whole point of F1's widening and of F3 removing the `Bd` antecedent.
2. Weight domination: `tensorSobolevWeight i σ ≤ tensorSobolevWeight i 3`, i.e.
   `(1+λᵢ)^σ ≤ (1+λᵢ)^3`, by `Real.rpow_le_rpow_of_exponent_le` with
   `one_le_one_add_lambda` (λᵢ ≥ 0).  Verbatim the high-regularity mirror
   `GalerkinLimitUniformMass.lean:1175–1188`.  `galerkinEnergy … 3 t` unfolds
   to the finset sum by `rfl`, so `hΦ N t ht` closes the domination directly.
3. `fatou_sq_mass` with `hS := tendsto_eigenIdxFinset_atTop`,
   `v N i := lowregProjMode g₀ fseq N t i`,
   `vlim i := perModeConv λᵢ (timeModeCoeff fLo i) t`, `B := Φ`.

No new estimate, no new analysis.  `Cσ := Φ` is `t`-uniform because the rung's
`Φ` already is.

## The σ range, exactly

`σ ≤ 3`, with **no lower bound** — the domination only needs `1 ≤ 1 + λᵢ` and
`σ ≤ 3`, so every real `σ ∈ (-∞, 3]` is covered.  This is the natural range the
rung-3 energy supports; carrying it past 3 is exactly what rungs 4–5 are for.

## The limit-object identification (checked, not assumed)

`lowregFatouPack`'s `hconv` names the limit

    perModeConv (TensorEigenIdx.lambda i) (fun u => (timeModeCoeff fLo i) u) t

and `lowreg_loMass` (`LowRegAllOrderJet.lean:1058–1064`) states its conclusion
about **the same expression, syntactically**: same `perModeConv`, same
`timeModeCoeff fLo i`, same `tensorSobolevWeight i σ` weight, same
`Summable ∧ ∑' ≤ Cσ` pair, same `∀ t ∈ Icc 0 T`.  **No bridge remains on the
limit object.**  The gap between `lowregMassLow` and `lowreg_loMass` is
therefore exactly two things and nothing else:

* the exponent range (`σ ≤ 3` vs. every real `σ`), and
* the hypothesis GAP-ADAPTH (`lowreg_loMass` has no such hypothesis, so a
  future consumption must discharge it).

## Consumption shape for `lowreg_loMass` (recorded, NOT acted on)

`LowRegAllOrderJet.lean` is untouched; its `sorry` at `:1065` stands.  If a
later brick splits that proof on `σ ≤ 3` / `3 < σ`, `lowregMassLow` is the
`σ ≤ 3` branch verbatim *once* GAP-ADAPTH is discharged — the ∃-bound constants
`Ctop, B1, ρ, P` in `lowregMassLow`'s conclusion are the same package constants
`lowreg_projMode_tendsto` produces, so no re-instantiation is needed.  Do not
claim the branch before GAP-ADAPTH lands.

## Honest scope

* `lowregMassLow` is the σ ≤ 3 **instance**.  It does **not** close
  `lowreg_loMass`, which stays at 0%.
* GAP-ADAPTH is an explicit hypothesis of the produced `∀ ε` statement.
  Nothing here discharges it.

## 2026-08-05: exact adapted σ≤3 branch

This section supersedes the earlier GAP-ADAPTH status above.  The new
`lowregMassLowAt` consumes `IsAdaptedLowSolve` through `lowregFatouPackAt`, so
the stored ordered certificate and calibrated budget discharge the gate before
the Fatou mass argument begins.  Its conclusion is the `σ ≤ 3` branch of
`lowreg_loMass` directly, with no reselected constants and no conditional
antecedent.  The generic `lowregMassLow` remains for compatibility.  Focused
verification passed, warning-free, and the targeted module refresh passed.

Honest denominator: the σ≤3 branch is now closed for an explicit adapted solve;
the all-real-σ theorem `lowreg_loMass` remains unproved (0%) because the higher
rungs are still required.

## 2026-08-05 — generic all-real Fatou adapter

This section supersedes the exponent limitation above.  `lowregMassOfEnergy`
takes an explicit projected sequence, its mode convergence, any real
`σ ≤ τ`, and a pointwise projected energy bound at `τ`.  It returns summability
and the corresponding limiting `tsum` bound at `σ`, with no solve, dimension,
or horizon assumptions beyond those used by the supplied data.

`lowregAllMassAt` now chooses an integer order above an arbitrary real `σ` and
applies this adapter on the same path.  Focused verification and the direct
module refresh passed warning-free.  Consequently `lowreg_loMass` is proved
(100%); `(N)` remains theorem-level 0%, and whole HCG compactness remains about
3%.
