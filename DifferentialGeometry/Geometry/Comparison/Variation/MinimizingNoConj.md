# MinimizingNoConj

## Mathematical route

`minTail_edist` is the reusable tail counterpart of `minSeg_edist`: once an
intrinsic radial segment realizes the endpoint distance, every remaining tail
also realizes the corresponding fraction of that distance.  The proof uses
the two radial length upper bounds and equality in the full triangle inequality.

The already-proved `tailCurve_eq` and `tailVel_one` identities are also exported.
They provide the exact restarted-curve and endpoint-velocity data used by the
regular-distance sandwich, without duplicating their continuation argument in
the consumer.

These declarations were already proved privately in this module.  They are
exported because the regular-distance sandwich needs their exact endpoint and
reparametrization data; no proof bodies or assumptions were changed.

## Verification

Focused verification and the explicitly targeted module refresh both passed
without warnings after all three tail declarations were exported.
