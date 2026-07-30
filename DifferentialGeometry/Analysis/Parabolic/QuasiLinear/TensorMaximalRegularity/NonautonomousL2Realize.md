# NonautonomousL2Realize

## Role

`nonautL2_realize` is the generic intrinsic realization immediately after
`nonautL2_lift`.

It consumes the six conclusions returned by the lift:

- the high Duhamel identity;
- the high forcing fixed-point identity;
- the zero trace;
- the expanded non-autonomous derivative equation;
- inclusion of the high forcing to the prescribed low forcing; and
- inclusion of the high top field to the prescribed low top field.

It produces one canonical `CrossScaleField` on the unchanged horizon.  The
carrier and top field are the high solution data, the fixed-point identity
refolds the expanded derivative equation to

`timeDeriv u = timeScaleLaplacian u.hiL2 + fHi`,

and the Lions--Magenes intermediate representative is pinned almost everywhere
to the prescribed low Duhamel field.  Continuity upgrades the almost-everywhere
compatibility to an every-time equality between the included high carrier and
the canonical low carrier on the closed slab.  The package also records zero
trace, zero intermediate initial value, continuity of the squared intermediate
norm, and the every-time inclusion from the intermediate representative to
the high carrier.

## API reuse

The construction uses the existing reverse-realization interfaces
`duhField_pin` and `strongCross`, followed by the existing
`CrossScaleField` representative and energy-continuity theorems.  The two
private component lemmas are the minimal lower-layer versions of the
representative links already used by the geometry-level
`LowRegBootstrapOne` consumer.  No geometric hypothesis, realization
predicate, new class, or wrapper assumption was introduced.

## Concrete frontier

At the time of this audit, the fixed-background low-base coefficient tree does
not yet export one complete pair of measurable, bounded, adjacent-compatible
`A2` and `A1` time families together with the affine forcing data required to
invoke `nonautL2_lift`.  Consequently this module is deliberately generic and
does not claim a concrete order-two Ricci--DeTurck bootstrap.

After that coefficient packet is assembled, `nonautL2_lift` followed by
`nonautL2_realize` will give the intrinsic same-horizon strong pair.  The next
separate producer must then iterate/upgrade the spatial and time regularity
enough to invoke the existing smooth spectral realization and obtain the two
inputs consumed by `ricci_gauge_of_dt`:
`IsQuasilinearMetricParabolicSolution` and `JointChartGramSmooth`.

## Verification

Focused verification passes without local warnings.  The source contains no
deferred proof or axiom facade.  A direct dependency audit of
`nonautL2_realize` reports only `propext`, `Classical.choice`, and
`Quot.sound`.  No exact module build was run.

## Project position

- `nonautL2_realize`: theorem 100%; its dedicated generic realization
  machinery 100%.
- Concrete same-horizon order-two Ricci--DeTurck bootstrap: not yet stated or
  proved, 0%; its dedicated low-base machinery remains approximately 98--99%.
- Smooth metric realization/bootstrap producer for `ricci_gauge_of_dt`: not
  yet stated or proved, 0%; substantial reusable spectral realization
  machinery already exists, but the low-base all-order packet remains
  independent.
- `ricci_flow_unif_existence`: unstated/unproved, 0%.
- HCG compactness is a separate project lane and is not advanced here.
