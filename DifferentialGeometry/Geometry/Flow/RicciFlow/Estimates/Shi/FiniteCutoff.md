# Fixed finite-cutoff first derivative estimate

## Role

`estimate_cutoff_one` is the generic finite-error `m = 1` Bernstein maximum-
principle brick.  It uses one compactly supported `ShiFixedCutoff` and requires
the zeroth-order bound only where that cutoff is positive.  It does not construct
a `BernsteinTower`, assume a global `hw0_bound`, or introduce a new class.

The proof extracts the raw two-level calculation from `Complete.lean`.  Its
localized Bernstein quantity is

`beta * chi * w 0 + t * chi ^ 2 * w 1`,

and the finite cutoff error is retained explicitly as

`9 * eps * beta * K ^ 2 * t`.

## Verification

Warning-free focused verification passed in 27.2 seconds, with no `sorry` or
`admit`.  The six point-local parabolic/cutoff helpers reused from
`Complete.lean` also pass that file's focused check and their export has been
refreshed.  The public theorem and assumptions remained unchanged through the
final declaration split.

## Project position

- `estimate_cutoff_one` theorem: proved and focused-verified (100%).
- Dedicated finite-cutoff `m = 1` machinery: proved and focused-verified (100%).
- `shiRm1_ball`: not yet stated and proved (0%); this theorem is its generic
  analytic engine, not the geometric cutoff/continuity producer.
- `smooth_nlc`: unchanged at 0%; its broader dedicated machinery remains a
  separate downstream lane.

The next downstream step is to use this generic engine in the geometric
`shiRm1_ball` producer; that endpoint remains separate and unstated here.
