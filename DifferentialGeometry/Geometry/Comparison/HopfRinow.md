# HopfRinow

## Compact-tail endpoint extension

`geo_Ioo_extend_cpt` combines the compact-tail endpoint continuation producer with
the existing open-interval gluing theorem. It assumes only eventual containment of
the curve tail in a pseudo-emetric compact set and does not require ambient
completeness.

Focused verification and the named module refresh passed.

## Finite-horizon continuation

`geo_Ioo_extend_to` continues a supplied local geodesic to `Ioo a₀ B` when
every compatible candidate endpoint strictly below `B` has a
`HasEndpointContinuation` witness. It reuses the existing global maximal-chain
theorem by contradiction: a compatible candidate whose endpoint is at least
`B` already restricts to the capped target, so only endpoints below `B` consume
the supplied continuation hypothesis. No second Zorn construction and no
ambient `CompleteSpace M` assumption are introduced.

Focused verification passed without warnings. The finite-horizon base-geodesic
producer is complete; minimizing coverage, raw `expDomain`, and segment-polar
coverage remain separate downstream frontiers.
