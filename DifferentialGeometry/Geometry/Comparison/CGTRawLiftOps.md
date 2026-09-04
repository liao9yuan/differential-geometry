# CGTRawLiftOps

## Mathematical route

The existing canonical `IsLiftOn` API already provides local differentiability
and uniqueness for two lifts with either a common start or a common point.  No
raw wrapper structure or CGT-specific uniqueness theorem is needed.

This file supplies only the missing explicit radial candidate.  `rawFlatRay`
uses a smooth transition with constant endpoint germs.  It stays in every
origin-centered ball containing its endpoint, transports a supplied radial
`expDomain` hypothesis through `normalFrame`, and is an `IsLiftOn` lift of its
own `framedExpMap` image.  The same candidate is realized as `rawFlatPath` under
the full radial-domain premise.  Its extension is the raw exponential image,
so the constant endpoint germs give `IsFlatC1Path` without a parallel lift
hierarchy.

For length, first compute the unflattened radial segment.  In positive model
dimension, `rawSpeed_sq` makes its metric speed constant and
`normalFrame_sqrt` identifies that constant with the model norm.  The
zero-dimensional branch is constant.  A local finite-dimensional completeness
instance is used only inside the proof required by the existing raw-speed API;
it is not a public assumption.  Monotone smooth-transition reparametrization
then transfers the exact length to `rawFlatPath`.

## Reuse and boundary

- Reuses `IsLiftOn` directly; no `RawFrameLift` analogue is introduced.
- Adds no public completeness, nonzero-dimension, or sigma-compactness
  assumption.
- Does not duplicate the generic restriction, reparametrization, or uniqueness
  arguments already expressible with `IsLiftOn.eqOn` and `eqOn_of_eq`.
- The next genuine raw propeller lemma is the two-collision loop built from
  these radial paths, with its canonical raw lifts related by generic
  `IsLiftOn` append/uniqueness and cancellation.

## Verification

The original lift-only layer passed focused verification warning-free.  The
first path/length pass exposed only local notation, unit-interval coercion,
model-manifold conversion, zero-dimensional instance, and reparametrization
normal-form issues; there was no mathematical or API blocker.  After those
local repairs, the complete file passed focused verification warning-free.

## Accounting

- P1b endpoints E1/E2 remain unstated and therefore 0%.
- Dedicated P1b machinery remains about 96%; this small operations layer closes
  plumbing but not the collision/fiber-count mathematics.
- Aggregate P1 endpoint completion remains 11/14 (78.6%), and the whole
  Poincare theorem endpoint remains 0%.
