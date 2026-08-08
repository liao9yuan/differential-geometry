# LowRegBgFatouIdent.lean

## Role

`lowregFatouE3AtBg` is the arbitrary-fixed-background primitive mirror of
`lowregFatouE3At`.  It consumes a projected forcing sequence, its state-ball
and fixed-background Nemytskii identities, the integrated `H³` energy bound,
one exact `IsRung3OrdBg` certificate, and its absorption budget.  It returns an
`N`- and time-uniform `H³` Galerkin energy bound.

This file intentionally does not add a background compatibility pack.  The
later calibrated producer will call `lowreg_projMode_atBg` and this primitive
separately, matching the diagonal layering.

## Reuse and background seam

No new forcing-identification helper is needed.  `lowregModeDeriv`,
`lowregForceMode`, and `lowregL2H3` already quantify over an arbitrary
nonlinearity, while `lowregForceCont` already has distinct state and DeTurck
background metrics.  The port therefore changes only the `coreN` and
`lowregNfun` background slots and replaces `IsRung3Ord` by `IsRung3OrdBg`.

The forcing identity remains the exact a.e. projected Nemytskii identity for
`lowregNfun g₀ g_bg`; no equality with the diagonal nonlinearity is assumed.

## Verification

Focused verification passed on the first attempt without local warnings.  The
targeted refresh's outer wrapper timed out before returning its final log, but
the single child build chain continued to completion, all Lean/Lake processes
exited naturally, and the resulting module `.olean` is newer than the source.
The stale elaboration metadata left by the timed-out wrapper was then removed
after its exact token and the absence of live children were verified.

## Accounting

The primitive Fatou background brick is complete (100%).  The later calibrated
projected-mode composition and `lowreg_loMassBg` remain unstated and unproved
(0%), as does headline `ricci_flow_unif_existence` (0%).  The broader route-(c)
background/adapted infrastructure remains approximately 65% complete.
