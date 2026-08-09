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

## Reverse-jet packet (2026-08-05)

`reverseJetPack` now exposes the exact bidirectional order-one/order-two metric
jet data needed by `fibreMorrey_unif_class`.  From `Λ`-equivalence and the
forward order-one and order-two metric-jet bounds it supplies the common
first-order coefficient `max (revJetOneC Λ) Λ`, the reverse second-order
coefficient `revJetTwoC Λ`, their nonnegativity, and all three
bound predicates in the required orientations.  The constants are fixed by
the class data before the varying metric; the order-three class hypothesis is
not used by this Morrey subroute.

Focused verification passed.  The remaining realization-radius boundary is
separate: the current `realize_at_unif` interface still asks for its
unrestricted curvature-defect family, whereas the rank-two `H2` use only needs
a finite low-order curvature producer.

## Narrow reverse-jet extraction (2026-08-05)

The order-at-most-two reverse-jet machinery has moved to
`UnifReverseJetTwo.lean`.  That module now owns the private metric-parallelism
helpers, `metric_self_sum`, `revJetOneC`, `revJetTwoC`, `reverseJetOne`,
`reverseJetTwo`, and `reverseJetPack`.  This file imports the narrow producer;
its order-three constant, reverse-order-three proof, and all downstream
Ricci--DeTurck estimates remain here unchanged.  Verification of the extracted
module and this consumer is pending.

## Fixed-background connection packet (2026-08-06)

The pointwise fixed-background connection estimates needed by the class-first
`H2` producer are now public in this module:

- `unifConnDiffZero` packages the reverse order-one metric jet with the
  ungated order-zero Koszul estimate;
- `unifConnDiffOne` packages the reverse order-one/order-two metric jets with
  the ungated first connection-derivative estimate;
- `unifConnDiffTwo` is the former private order-two result, now exposed without
  changing its statement or proof.

Their squared fibre-norm coefficients are respectively
`connDiffZeroSqC`, `connDiffOneSqC`, and `connDiffTwoC`.  All are explicit in
the class parameter and dimension, and none is selected after the class metric
appears.  The public `ShortTime/UnifFixedConnH2.lean` wrapper integrates these
three bounds and changes total volume back to the fixed background metric.

Focused Lean verification passed after closing the order-zero definitional
`iterCov` reduction with an explicit reflexivity step.  Axiom audits for all
three public pointwise bounds contain only `propext`, `Classical.choice`, and
`Quot.sound`.  The overall uniform-existence endpoint remains 0%.
