# LowRegGalerkinSol.lean — notes

Status: **GREEN, sorry-free, axiom-clean**.  Created 2026-08-04.  Brick (1) of
the three-brick gap recorded at the tail of `UNIF_EXISTENCE_PLAN4.md`.

## What it is

The `a = 1` instantiation of `galTameSolOne`
(`HeatSemigroup/GalerkinTameSol.lean`) against `lowregNfun`.  One theorem,
`lowregGalSol`.

## Interface choice (deliberate)

`lowregGalSol` takes the **six-number producer form** — `g_bg, δ, Ctop, B0, B1,
ρ, P` plus `hreal` and the tame estimate — exactly as
`lowreg_partial_sol_of_bounds` does, and NOT an `IsLowSolve` bundle.  Reason:
`IsLowSolve` existentially binds the six numbers and `hreal`, and `lowregNfun`
depends on all of them, so an `IsLowSolve`-consuming statement would have to
re-existentialise `Nfun` and would lose the link to the `Nfun` that
`lowreg_projMode_tendsto` (`LowRegGalerkinIdent.lean`) talks about.  Brick (2)
destructures `IsLowSolve` **once** and feeds both theorems the same witnesses.

Hypotheses actually used: only `hδ, hCtop, hB0, hB1, hρ, hP, hreal, htame`.
`hcont`, the zero-state bound `D`, the horizon cap and the forcing ball are NOT
needed for existence — the retraction removes every smallness requirement.  (In
particular the Galerkin system exists on **any** `T`, not only on
`lowregHorizon`.)

## Instantiation data

* `R := lowregStateRad Ctop B1 ρ P`, `hR` from `lowregStateRad_pos`.
* tame coefficients `A := Ctop`, `Rt := lowregOuterRad Ctop ρ P`
  (`lowregOuterRad_pos`), `B := B0`, `C := B1` — the three arms are already in
  `galTameSolOne`'s `A * Rt * ‖·‖ + B * ‖J·‖ + C * (‖u‖+‖v‖) * ‖J·‖` shape, so
  `htame` transfers verbatim (no renormalisation, unlike
  `lowreg_proj_tendsto`'s `toNNReal` juggling for `partial_sol_tame`).
* `S := eigenIdxFinset g₀ N`, `κ := (N : ℝ) + 1`, from
  `mem_eigenIdxFinset : i ∈ eigenIdxFinset g₀ N ↔ 1 + λᵢ < (N : ℝ) + 1`.
* `choose` over `N` turns the per-`S` statement into the family
  `U : ℕ → ℝ → TensorEigenIdx → ℝ`, matching
  `deTurckGalerkin_solution_existsSymm`'s shape.

## What brick (2) gets

`U N`, continuous on `[0, T]` per coordinate, supported on
`eigenIdxFinset g₀ N`, `U N 0 = 0`, and

    d/dt (U N t i) = −λᵢ · U N t i + galTameForce g₀ 1 hR lowregNfun (eigenIdxFinset g₀ N) (U N t) i

on `[0, T)`.  `galTameForce_eq` replaces `galTameForce` by the true
`Π_N ∘ lowregNfun` as soon as `‖J (finiteEigenComboHs … (U N t) 3)‖_{H²} ≤ R`.

## Open (for bricks 1b / 2 / 3)

The state-ball bound above is NOT proved here; the sketch of the Grönwall
argument that yields it, `N`-uniformly, is in `GalerkinTameSol.md`.  Until it
lands, brick (2)'s identification of `U N` with `perModeConv` of the projected
forcing must either carry it as a hypothesis or produce it.

## Lean lessons

* The `open` block must include `DifferentialGeometry.Integral.L2`,
  `…Integral.Connection` and
  `…IntrinsicSpectral.MetricRealization` (for `SmoothCcTensor`,
  `smoothCcToTensorHs`, `gFibreOpBound`, `ccTensorBilinSymm`) — copy
  `UnifClassBounds.lean`'s header, not `LowRegGalerkinIdent.lean`'s.
* `a` stays symbolic as the literal `1 : ℕ` fed to `galTameSolOne`, so
  `(a : ℝ)` prints as `((1 : ℕ) : ℝ)` and matches the campaign's exponents.

## Verification

Focused check green, targeted build green (9705 jobs), no warnings.  Axiom
census: `lowregGalSol` is `[propext, Classical.choice, Quot.sound]`.
`LowRegAllOrderJet.lean` untouched — `lowreg_loMass` is still the sole front-2
`sorry`.
