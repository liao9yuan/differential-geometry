# Canonical metric compactness construction

## Reverse ball capture route

The canonical construction retains the finite-stage almost-isometry data and
the tail direct-system maps long enough to prove reverse compact-ball capture.
`tailMember_chain` is the local provenance bridge: on a point inserted from an
earlier tail stage, the final member map is exactly the corresponding finite
`chainComp`, up to the unavoidable associativity cast in the ambient index.

The public capture theorem belongs specifically to `compactness_canon`; it must
not be asserted for an arbitrary `StepDCanon`, whose public fields intentionally
forget the finite-stage map provenance.

## Verification

An initial direct implementation of the complete reverse-capture geometry
inside `compactness_canonPackage` hit an elaboration performance wall despite
using only one Lean thread.  The stable route factors that geometry into the
generic `tailBall_capture` producer and leaves here only the existing
`ProperMetricOn.realizes` conversion from the public `Metric.eball` to the
aligned intrinsic `Metric.ball`.

The resulting `tailMember_chain` and `canon_ball_capture` declarations are
warning-free focused GREEN.  The exact `CanonicalConstruction` module refresh
is also GREEN, so downstream audit modules see the exported declarations.

## Project progress

`tailMember_chain`: 100%.  `canon_ball_capture`: 100%.  Dedicated P2-side
no-mass-loss machinery is about 95--97%; the geometric no-mass-loss endpoint
remains 0% because its moving-center quadratic coercivity input belongs to P3.
