# CGTRawCollisionPath

## Mathematical route

For two raw framed-exponential vectors with the same image, take the flat raw
radial path to the first vector and concatenate it with the reverse of the
second radial path, cast to the common image endpoint.  The result is the
canonical collision loop based at the center.

`rawCollision_flat` is only the generic `IsFlatC1Path.trans` and `symm` API,
plus the representation-neutral endpoint cast.  `rawCollision_len` uses the
existing radial length identity together with `pathLen_trans` and
`pathLen_symm`; no new Gauss or lift hierarchy is introduced.

## Reuse and boundary

- Reuses `rawFlatPath`, `rawFlatPath_flat`, and `rawFlatPath_len`.
- Assumes only closed radial-domain coverage for each endpoint and their raw
  framed-exponential collision.
- Adds no public completeness, nonzero-dimension, wrapper predicate, or
  intrinsic-completeness assumption.
- This is collision/fiber-count machinery, not either P1b endpoint E1 or E2.

The next genuine lemma is the canonical `IsLiftOn` midpoint/cancellation fact
for this loop: an arbitrary lift of the concatenation agrees at time `1/2`
with `rawFlatRay u` at time `1`, and a zero loop endpoint would force `u = v`
by comparing the reversed second half with `rawFlatRay v`.

## Verification

After the exact downstream-required `CGTRawLiftOps` refresh, the collision
path module passes a warning-free focused check.  No additional source repair
was needed.

## Accounting

- P1b endpoints E1/E2 remain unstated and therefore 0%.
- Dedicated P1b machinery remains about 96%; this closes the collision-loop
  path/length packaging but not the lift cancellation or raw fiber count.
- Aggregate P1 endpoint completion remains 11/14 (78.6%), and the whole
  Poincare theorem endpoint remains 0%.
