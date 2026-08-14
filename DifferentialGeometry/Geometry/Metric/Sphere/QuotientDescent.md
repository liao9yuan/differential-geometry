# Round quotient descent

## 2026-08-14 compactness and connectedness producers

`RoundQuotientData.proj_surjective` now extracts surjectivity directly from the
stored local sections.  The continuous image of the compact round sphere then
supplies `RoundQuotientData.compactSpace`, and connectedness descends along the
same surjection through `RoundQuotientData.connectedSpace`.

Focused verification passed.  The abstract finite-round-quotient closure layer
is complete for the Hamilton examples (100%).  Concrete `RP³` and lens-space
constructors remain unstated (0%); their missing frontier is the smooth quotient
manifold and local-section construction, not curvature descent.
