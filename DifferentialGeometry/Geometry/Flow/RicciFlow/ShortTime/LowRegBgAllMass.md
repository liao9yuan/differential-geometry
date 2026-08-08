# LowRegBgAllMass

## Role

This module is the final conditional spectral-mass assembly for an arbitrary
fixed DeTurck background.  It turns an `IsAdaptedLowSolveBg` certificate into
one coherent `IsAllRungPath`, applies the existing background-neutral Fatou
mass theorem, and exports the thin `lowreg_loMassBg` endpoint consumed by the
background smoothing packet.

All spectral spaces, modes, Galerkin energies, and limiting convolutions remain
based at the state metric `g₀`.  The independent metric `g_bg` is passed only
through the fixed-background rung-five and higher-rung producers.

## Source port

The implementation is a narrow port of `lowregAllRungsAt`,
`lowregAllMassAt`, and `lowreg_loMass`:

- `lowregRung5PathAtBg` supplies the common projected sequence and rung-five
  path;
- the gate stored in `IsAdaptedLowSolveBg` supplies the absorption budget;
- `lowregHighRungsBg` supplies every energy rung `6 + k`;
- the unchanged `IsAllRungPath` and `lowregMassOfEnergy` close the spectral
  mass statement.

No compatibility aliases or per-metric constant selectors are added here.
This is a conditional consumer of an already adapted solve, not a class-first
producer of the adapted certificate.

## Verification

Focused Lean verification passed.  The targeted module refresh also passed,
and `LowRegBgAllMass.olean` is newer than its source.  The only emitted warnings
were replayed warnings from imported modules; this new file emitted no local
diagnostic.

## Project accounting

`lowreg_loMassBg` is proved and verified.  This module completes the conditional
mass-assembly layer only.  The headline
`ricci_flow_unif_existence` theorem remains unstated on this route and therefore
0%; its dedicated fixed-background direct-smoothing machinery is roughly 82%,
with class-first adapted-solve production and final theorem composition still
remaining.
