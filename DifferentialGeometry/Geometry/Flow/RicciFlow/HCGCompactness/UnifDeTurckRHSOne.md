# UnifDeTurckRHSOne

## Status

The intrinsic class-uniform `j = 1` static Ricci--DeTurck fibre-bound producer
is complete.

The proof stays intrinsic.  Reverse metric jets through order three feed the
connection-difference two-jet estimate.  A fixed rank-three-to-rank-one trace
tower then controls the differentiated DeTurck covector, while the curvature
one-jet packet controls the differentiated Ricci term.  The exact
Ricci--DeTurck section identity combines those terms with the slot-swapped Lie
term.

The public endpoints are:

- `unifKsupOne`, the class-uniform `j = 1` bound;
- `unifKsupLow`, the complete packet for every `j <= 1`.

Both focused and exact verification passed.  This module has no
`sorry`, `admit`, or new axiom declaration.

## Remaining boundary

`ShortTime/UnifNZeroBound.lean` now obtains its order-one spectral estimate from
the curvature-free exact `H¹` identity, so the former `Fc/hFc/hcurv` packet is
not an E6 input.

The remaining E6 risk is the quantifier order of this module's public endpoints:
they currently prove `∀ g₀, ∃ K`, whereas a uniform horizon needs
`∃ Kstar, ∀ g₀`.  A source audit shows that the witnesses are mathematically
class-uniform, but two constants still need to be exposed in the API:

- the identity-endomorphism factor in the connection-difference grid should use
  the dimension bound `rfns_idEndo_le` rather than a metric-specific compactness
  choice;
- the constant behind `iterCovG1_three` should be made explicit.

After those extractions, reorder `unifKsupZero`, `unifKsupOne`, and
`unifKsupLow`, then assemble the common zero-forcing bound in a new
`ShortTime/UnifNZeroClass.lean`.  Do not import this class-specific module back
into the parameterized consumer.

## Project position

`ricci_flow_unif_existence` itself remains 0% complete because its endpoint
proof still contains a placeholder.  Its dedicated uniform-existence machinery
is approximately 80% complete after this producer; the whole HCG compactness
project remains in the low single digits.

## Superseding status (2026-07-31)

The quantifier-order risk above is now closed.  Explicit reverse-jet,
connection-difference, Ricci, Lie-arm, and `j = 0,1` coefficients feed the new
public theorem `unifKsupLeOne`.  It chooses one nonnegative `Kstar` from
`gBase` and arbitrary `Λ ≥ 1` before the varying metric, then controls every
covariant slot `j ≤ 1` under the class metric-jet assumptions.  The proof uses
the supplied-cap endpoints `unifKsupZero_of` and `unifKsupOne_of`; no
metric-dependent compactness witness is chosen after `g₀`.

The persistent LSP loop was effective here: after deliberately recycling the
downstream file worker to load the refreshed upstream `.olean`, saved edits
re-elaborated in seconds and identical goal queries reused the existing info
tree in well under one second.  Focused and exact verification passed.  Direct
axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound`.

`ricci_flow_unif_existence` itself remains unstated/proved at this endpoint
(0%); its dedicated machinery is approximately 68% complete.  The independent
high-side Nemytskii realization remains the next substantial frontier, and the
whole HCG compactness project remains in the low single digits.
