# StepCStageReturn.lean - target-ball and return control

## 2026-07-16 verified return machinery

The new file is focused-green and warning-free.  It provides three checked
rectangular pair-index tails:

- `liveCenters_radial` compares every retained live center at two independently
  moving stages through their common `rInf` radius;
- `HasStageJetData.mapsTo_tail` maps the stage-`k` source ball into a larger
  stage-`l` source ball under the explicit construction-radius margin
  `R0 + (4 + 8 * sqrt 2) * lambda D 0 < R1`;
- `HasStageJetData.return_tail` applies the map in both directions and proves
  that the resulting return map is uniformly as close to the identity as
  requested on the smaller source ball.

The public statements do not retain a redundant nonnegativity assumption on
`R0`.  The strict radius sandwich already supplies every nesting inequality
used by the proofs.

## Global-injectivity frontier

The next desired theorem is a rectangular tail asserting `Set.InjOn` for the
forward stage map.  Its return-map input is now checked, and
`HasStageJetData.hloc_tail` supplies local diffeomorphisms.  The tempting route
of extracting a Lebesgue radius separately for each fixed pair `(k,l)` is not
valid: that radius would depend on `(k,l)`, while the threshold supplied by
`return_tail` would then depend on that radius, recreating the forbidden frozen
threshold circularity.

The smallest missing producer output is a stage-independent intrinsic buffer:
there should be `rho > 0` such that every point in the controlled source ball,
at every sufficiently large stage, lies in a source-chart core whose inverse
image contains the intrinsic ball of radius `rho` around that point.  Equivalently,
one needs the lower-layer first-exit/confinement lemma that derives this from the
existing coordinate closed-ball buffer, normal-metric comparison, and the
`expRadiusGp` floor.

This is a missing retained-field/API issue, not an endpoint-radius assumption.
The upstream support capstone proves normal-scale and `expRadiusGp` fence data,
but `HasStageJetData` currently retains only support convergence, metric
convergence, jet tails, and basepoint preservation.  It therefore does not
expose enough information to prove that the minimizing join stays inside the
normal-coordinate chart while converting the coordinate buffer to an intrinsic
buffer.  The right repair is to prove and retain the intrinsic-buffer output at
the producer layer, not to add a hypothesis to the final B1 endpoint.

## Honest accounting

- The return-control sublane in this file: approximately 100% implemented and
  focused-verified.
- Dedicated global-injectivity machinery: approximately 70%; local jet/local
  diffeomorphism and uniform approximate return are checked, while the uniform
  intrinsic-buffer producer and final `injOn_of_return` assembly remain.
- The global `InjOn` tail theorem itself: unstated, hence 0% theorem completion.
- The concrete `StepB1RawInput` producer: unstated, hence 0% theorem completion.
- Textbook Step B1: 0% theorem completion; the work here is supporting
  infrastructure in its Step-C-to-B1 producer lane.
