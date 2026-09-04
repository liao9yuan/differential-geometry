# LocalIsometryRigidity

## Geodesic support migration

The local small-ray construction already carries a fixed-chart lifted flow and proves
that its foot remains in the chart source at every supported time.  Its local geodesic
equation is therefore obtained directly from `IsGeodesicAt` using that chart lift.
It no longer packages chart-specific support as the global
`IsGeodesicOnWithInitial` predicate.

All public theorem statements and the later local-isometry rigidity argument are
unchanged.

## Verification

Focused verification initially exposed one now-obsolete positive-dimension section
assumption.  After omitting that unused instance, verification passed without warnings.
