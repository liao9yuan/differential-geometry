# MapConvergenceDeriv

## 2026-07-15 canonical placement

The generic derivative and convergence-algebra closures were moved from the
HCG tree into `Analysis/Calculus` without renaming their public declarations.
The new `MapCInfConvOnCompacts.fderivOn` proves convergence of the full
Fréchet-derivative field on an open domain, consuming one additional derivative
order from the original family.

Focused verification passed. The old HCG file is now a compatibility import.
