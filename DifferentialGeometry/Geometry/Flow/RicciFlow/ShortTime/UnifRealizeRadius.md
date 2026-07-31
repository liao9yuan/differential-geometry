# UnifRealizeRadius.lean — the `P` slot of the six-number solve (Lane E, brick E5 tail)

Status 2026-07-30: **landed, sorry-free, axiom-clean**.  Verification: focused check green,
targeted module build green, `#print axioms` clean.

## Content

One theorem, `lowregHorizon_unif_pos`:

```
0 < lowregHorizon Ctop B0 B1 D ρ (unifRealizeRad Cpt Fc d)
```

from `lowregHorizon_pos` (`ShortTime/UnifClassBounds.lean`, brick E8a) and
`unifRealizeRad_pos` (`Analysis/Spectral/Tensor/Estimates/H2PointwiseUnif.lean`, brick E5).

## Why it is only one theorem

The other two `P`-side obligations of `lowreg_partial_sol_of_bounds` are already discharged
in `H2PointwiseUnif.lean` in exactly the shape that theorem wants:

* `hP : 0 < P` is `unifRealizeRad_pos`;
* `hreal : ∀ T, ‖smoothCcToTensorHs g₀ ((1:ℕ)+1) T‖ ≤ P → gFibreOpBound g₀
  (ccTensorBilinSymm g₀ T) δ` is `realize_at_unif`, verbatim, at
  `δ = deTurckArmContractionThreshold'' (finrank ℝ E)`.

So the only genuinely new fact at this layer is that the closed horizon stays positive at the
closed radius.  A full specialization of `lowreg_partial_sol_of_bounds` with
`P := unifRealizeRad …` was deliberately NOT written: it is pure mechanical substitution (the
`hcont`/`htame`/`hzero` hypotheses would have to be re-typed against the specific `hreal`
term, ~50 lines of copy with no mathematics), and its remaining inputs — `Ctop, B0, B1, D, ρ`
— are exactly what bricks E6/E7 do not yet supply.  That instantiation is brick E8b and
should be written once, there, when the five coefficient bounds exist.

## Effect on Lane E

`P` is no longer a source of `g₀`-dependence in the horizon: given class-uniform inputs
`Cpt` (brick E4, NOT landed — currently a hypothesis) and `Fc` (brick E3, open), two metrics
of the same `Λ`-class receive the SAME realization radius, hence — via `lowregHorizon_mono`
plus class bounds on the five coefficient numbers — the same positive horizon.
