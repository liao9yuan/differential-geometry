# LowRegForceHiBg

## Purpose

This module separates the fixed-background frozen high forcing from the
self-background realization path.  `liftHiNBg` uses the canonical completed
background A2 map and an explicitly supplied completed high A1 map, while
`lowBaseNBgWith` uses the compatible low A1 map.

## Status

Focused verification passed.  The scale-inclusion theorem `hiNBg_incl` is
proved without new analytic assumptions and preserves the arbitrary fixed
DeTurck background.

## Remaining frontier

The time-dependent adjacent-scale driver still needs a background-aware
assembly of the low/high coefficient families and a proof that the supplied
low solve has the `lowBaseNBgWith` frozen forcing.  Those are realization
adapters; existence of the class-first A1 and A2 certificates remains a
separate analytic producer problem.
