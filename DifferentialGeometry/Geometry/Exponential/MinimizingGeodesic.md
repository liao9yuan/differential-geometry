# MinimizingGeodesic

## 2026-08-30: local velocity matching

### Mathematical change

`broken_minimizer_velocity_match` no longer assumes `CompleteSpace M`. Its
proof is entirely local: it builds compactly supported chart variations of the
two geodesic pieces, applies first variation to their lengths, and uses the
global distance lower bound to force the velocity jump to have zero metric
norm. None of those inputs consumes ambient geodesic completeness.

The existing complete Hopf--Rinow endpoints and their signatures are
unchanged. General raw radial reparametrization was deliberately placed in
`Geodesic/MaximalRescaling.lean`, not in this minimizing-geodesic consumer.

### Verification and progress

Focused verification passed without warnings after the imported
`Geodesic/MaximalRescaling` artifact became available. The earlier attempt had
stopped before theorem elaboration because that object file did not yet exist;
no proof repair or added hypothesis was needed once the dependency was current.
Thus the existing proof genuinely verifies under the weaker statement without
ambient completeness.

- `broken_minimizer_velocity_match`: source change and focused verification
  complete (100% for this local producer).
- `minExp_of_cptBall`: its downstream source proof is now written but remains
  unverified, so the theorem is still 0% complete.
- Dedicated incomplete-ambient minimizing-exponential machinery and source
  assembly: about 95%; downstream endpoint elaboration remains.
- The whole P1a compact-closure Bishop endpoint remains unstated and unproved
  (0%).
