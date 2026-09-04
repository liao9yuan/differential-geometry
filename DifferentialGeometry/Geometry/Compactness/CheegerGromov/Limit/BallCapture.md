# BallCapture

## Purpose

This module supplies the geometric inverse-ball estimate needed before a
canonical Cheeger--Gromov compact-ball capture theorem can be assembled.  It is
stated for an existing `BookApproxIsoPartialData`; it does not add a compactness
assumption or a replacement convergence structure.

## Route

`ball_subset_image` uses a compact source closed ball and the openness of the
partial diffeomorphism image.  If a target point in the prescribed ball were
outside that compact image, a short target path has a first exit point.  The
path prefix lifts through the inverse partial diffeomorphism.  The reverse
metric `c0` estimate bounds its lifted length, contradicting the source radial
buffer.

The proof reuses `exists_first_exit`, the native Riemannian path-length API,
and the forward/reverse estimates already stored by
`BookApproxIsoPartialData`.  It does not compare bundle-valued metrics or
introduce a new provenance class.

## Verification

The file passes its focused check without warnings and contains no
`sorry`/`admit`.

## Remaining canonical bridge

The public `StepDCanon` projection records source exhaustion, reference-metric
convergence, and relative compactness, but not the finite-stage tower data that
identifies its maps with the buffered `BookApproxIsoPartialData` maps.  The
generic theorem here is therefore not by itself a theorem about an arbitrary
`StepDCanon`.  The next honest endpoint must be projected from the private
canonical package while that tower provenance is still available.

Three routes were checked.  An arbitrary `StepDCanon` is insufficient because
source exhaustion does not imply that its target images contain metric balls.
Unfolding `compactness_canon` cannot recover more information because its
private opaque package projects only `canon` and connectedness.  The viable
route is to add the canonical capture proof inside that package, using its
still-live `D₀`, `tailMemberMaps`, and direct-limit inclusions; the missing
lowest API is an equality identifying the eventual member map on an included
finite-stage compact ball with the corresponding restricted `D₀` map.
