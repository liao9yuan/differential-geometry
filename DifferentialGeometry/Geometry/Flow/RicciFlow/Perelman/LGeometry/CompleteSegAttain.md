# CompleteSegAttain

## Role

This module supplies the complete bounded-curvature same-clock segment
attainer needed by pointed reduced-geometry consumers.

## Native route

- `lSegCurve_sqrtOn` weakens the existing square-root admissibility bridge from
  global `C1` to `C1` on the compact square-root-time interval.  Endpoint
  neighborhoods are handled within the interval; differentiability is used
  only almost everywhere in its interior.
- `exists_lSegAtt_rm` consumes `exists_lRegMin_rm`, derives the scalar lower
  bound directly from the Riemann-curvature norm bound, and uses
  `lSegValue_eq_reg` to identify the raw same-clock value with the attained
  regularized action.

No new minimization hierarchy or supplied-attainment assumption is introduced.

## Verification

The final source is warning-free focused GREEN with four Lean threads.  Both
public endpoints were also checked directly and use only `propext`,
`Classical.choice`, and `Quot.sound`.  No named refresh was run because parallel
tasks were active and no downstream module yet imports this new file.

An earlier proof shape timed out because the generic bridge and complete-flow
section installed distinct `NormedSpace` paths.  Separating their instance
contexts removed that diamond; the final file checks under the default
heartbeat budget.

## Progress

- `lSegCurve_sqrtOn`: verified theorem 100%.
- `exists_lSegAtt_rm`: verified theorem 100%.
- Dedicated complete-flow same-clock attainer machinery: 100%.
- Geometric no-mass-loss and the P3 asymptotic-shrinker endpoint remain 0%.
- Whole P0--P9 infrastructure remains approximately 15--25%.
