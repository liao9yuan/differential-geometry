# CrossVFReduction

## Chart-to-global integral curves

`chart_vf_on_iff` lifts the existing pointwise identity
`geodesicVectorFieldChart_eq_geodesicVectorField` to
`IsMIntegralCurveOn` on an arbitrary set `K`.  Its only additional input is
that the projection of the supplied curve stays in the fixed chart source at
each time in `K`.

The equivalence is appropriate here because both directions are the same
pointwise rewrite.  No continuity, openness, preconnectedness, completeness,
or initial-value assumptions are added.  The proof does not unfold tangent
bundle derivatives or duplicate the coordinate calculation establishing the
underlying vector-field equality.

The equality, equivalence, and global smoothness producer now live unchanged
in the lower `GlobalVectorField` module.  `CrossVFReduction` imports that
module and retains its higher projection-uniqueness and geodesic-equation
results.  This preserves the old import path while removing the dependency
cycle with `MaximalInterval`.

After the lower producer gained its zero-dimensional branch, the immediate
cross-chart compatibility and projection-uniqueness endpoints also shed their
gratuitous `NeZero` section dependency; their mathematical statements are
otherwise unchanged.

## Verification and scope

Focused verification of the reduced compatibility module passed without
warnings.  Both the lower producer and this compatibility module received
successful explicit named refreshes for downstream consumers.

- `chart_vf_on_iff`: 100% complete and checked.
- Fixed-chart/global integral-curve reduction represented by this theorem:
  100% complete.
- Any downstream global geodesic-existence or compact-closure Bishop theorem:
  not stated or proved here (0% theorem completion in this file); this adapter
  is estimated to be under 1% of the larger P1a comparison assembly.
