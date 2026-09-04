# CGTRawExpLift

## Mathematical route

`exists_raw_lift` applies the existing map-generic compact path-lifting theorem
to the raw framed exponential.  A partial lift is fenced in the closed ball of
radius equal to the path length by `rawLift_norm_le`; the supplied radial
`expDomain` hypothesis is used only along the lifted vectors inside the open
local-diffeomorphism ball.

The target tangent `NormedAddCommGroup` and `NormedSpace` families are explicit
instance parameters of `exists_raw_lift`, matching `rawLift_norm_le`.  They are
not new geometry assumptions: `hEnorm`, `pathELength`, and the lift fence
already use them.  Exposing the families prevents a canonical `Tensor0SBundle`
norm from being baked into this declaration and lets raw Riemannian consumers
select one norm consistently throughout the path-length argument.

The conclusion deliberately returns the canonical `IsLiftOn` predicate rather
than introducing a raw analogue of `IntrFrameLift`.  This keeps the raw CGT
specialization map-generic and avoids a duplicate wrapper hierarchy.

## Reuse and boundary

- Reuses `IsLiftOn.exists_of_compact` and `rawLift_norm_le`.
- Does not assume ambient completeness or sigma-compactness.
- Does not modify or wrap the checked intrinsic CGT path.
- The next consumer is the raw loop/fiber-count specialization; this file does
  not yet state either P1b endpoint.

## Verification

- The initial preflight found only the missing already-checked
  `RawLiftLength` artifact; its exact refresh passed.
- The first elaborating pass found a two-site model-with-corners notation typo;
  after that local correction the focused check passed warning-free.
- The explicit norm-family signature passed focused verification without
  warnings.

## Accounting

- P1b endpoints E1/E2: both unstated and therefore 0%.
- This is dedicated machinery only; it does not change aggregate endpoint
  completion.
