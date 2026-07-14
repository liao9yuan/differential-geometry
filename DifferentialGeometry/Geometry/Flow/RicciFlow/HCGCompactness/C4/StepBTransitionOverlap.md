# StepBTransitionOverlap status

Status: 2026-07-13, focused verification passed without warnings or `sorry`.

`normalOverlap_of_map` turns source/target C2-radius inclusions plus an
exponential-image containment into the canonical `NormalOverlapOn` predicate.
`normalTrans_mapsTo` produces the coordinate maps-to fact from the same image
containment, and `NormalOverlapOn.cancel` gives the reverse-transition
cancellation on the overlap.  These are compatibility adapters over the
existing normal-coordinate API, not new transition assumptions.

This overlap-adapter sub-brick is 100%.  Stable-pair geometric containment and
the finite transition diagonal remain separate producers.  Dedicated
Step-B/B1 machinery is about 83%, Chapter 4 machinery about 79%, and whole-HCG
machinery about 53%; `StepB1RawInput`, textbook B1, and the conditional
compactness endpoint remain theorem-level 0%.
