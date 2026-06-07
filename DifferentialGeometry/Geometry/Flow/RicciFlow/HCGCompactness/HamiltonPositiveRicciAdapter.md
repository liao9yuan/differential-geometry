# HamiltonPositiveRicciAdapter

Source used: the current `HamiltonPositiveRicci.lean` black-box interface around `Ham3CGHLimitData`, `Ham3LimitSubseq`, `Ham3LimitWindow`, `Ham3LimitFlow`, `Ham3CGHLimitExists`, and `ham3_cgh_limit`.

Introduced definitions: `pointedFlowToHam3` and theorem `toHam3Exists`.

2026-05-26 update: added `ham3OfCompactSol`, which is the intended derivation
shape for the Hamilton `ham3_cgh_limit` black box from the MSM135 Theorem 3.10
wrapper `compactnessSol`.  It takes the rescaled pointed-flow sequence `X`,
the three compactness inputs `CompleteInput`, `CurvBoundInput`, and `InjInput`,
the explicit time-zero metric compactness inputs, the derivative-input record,
and the smooth-flow upgrade backend. It then applies `compactnessSol` and feeds
the result through `toHam3Exists`.
The remaining explicit inputs are the Hamilton-specific limit-window,
regular-window, connectedness/boundarylessness, and tensor/scalar convergence
transfer producers.

Relation to `Ham3CGHLimitExists`: the adapter forgets the new convergence fields down to the current Section 12 limit-data record. The old proposition does not yet store the source rescaling relation, so the adapter needs the new compactness conclusion plus the fixed closed time-window inclusion and open regular-window inclusion.

2026-05-26 update: `Ham3CGHLimitExists` now also records connectedness and
boundarylessness for the limit.  The generic HCG `PointedFlowData` record does
not yet store those global manifold facts, so `toHam3Exists` takes them as
explicit adapter inputs rather than hiding them in the compactness conclusion.
This keeps the adapter checked while preserving the honest frontier: a future
CGH producer should prove connectedness/boundarylessness for limits of the
closed connected source manifolds.

2026-05-26 update: `Ham3CGHLimitExists` now also records basepoint scalar
convergence, the `Ham3RicNonnegTransfer` datum used by the Section 12 Ricci
nonnegativity inheritance step, and the `Ham3PinchTransfer` datum used by the
trace-free Ricci argument.  The adapter takes these as explicit inputs from the
HCG side; it does not pretend that the generic `PointedFlowData` record alone
contains those tensor/scalar/function-pullback convergence facts.

2026-05-27 update: `ham3OfCompactSol` was adjusted after `compactnessSol`
became an honest Theorem 3.10 wrapper requiring derivative and smooth-flow
upgrade inputs; the adapter still does not edit `HamiltonPositiveRicci.lean`.

2026-05-27 review update: after the pointed Riemannian rename and removal of
public `smoothPlus` fields from generic HCG data, the adapter now derives the
old `Ham3CGHLimitData.smooth_plus` field locally from `L.smooth`. The adapter
still only forgets the generic HCG conclusion into the old Hamilton endpoint
and does not edit `HamiltonPositiveRicci.lean`.

2026-05-27 update: added the first Hamilton transfer producer from the generic
smooth CGH convergence scaffold.  `Ham3BaseScalarSeq` records only the source
realization needed here: the time-zero basepoint scalar of the generic pointed
flow sequence is the Hamilton rescaled scalar from `(P,Q)`.  Then
`baseScalarConv_of_smoothCGH` proves `Ham3LimitBaseScalarConv` from
`SmoothCGHConverges.scalar_converges` and the comparison maps'
`basepoint_map`.  Consequently `toHam3Exists` and `ham3OfCompactSol` no longer
take the broad `hbaseScalar` transfer input; they take the narrower source
realization input and derive the scalar convergence internally.

Verification: focused checking passed for this file after refreshing stale
upstream HCG and curvature artifacts.  A later targeted adapter build was
blocked by an unrelated upstream failure in `DimensionThree/RicciControlsRm`;
the adapter source itself elaborated successfully.  Remaining explicit
Hamilton-specific inputs are connectedness, boundarylessness, Ricci
nonnegativity transfer, and pinching transfer.

2026-05-27 shape cleanup: moved connectedness and boundarylessness out of the
late Hamilton adapter assumptions.  The adapter now introduces
`HamCGHConclusion`, a Hamilton-specific strengthened compactness conclusion
containing the ordinary `SmoothCGHConverges` witness plus limit connectedness
and boundarylessness.  The package `HamCGHTopology` is the honest upstream
frontier: it should be proved from the connected/boundaryless source manifold
and the CGH construction, then used to lift `solutionCompactness`'s ordinary
`CompactnessConclusion`.  Consequently `toHam3Exists` consumes
`HamCGHConclusion`, while `ham3OfCompactSol` consumes `HamCGHTopology` and no
longer asks for per-limit `hconnected`/`hboundaryless` functions.

Verification: blocked before adapter elaboration by upstream Rm04 slot
migration failures in `RicciFlow/Evolution/ImprovedPinching/Definitions.lean`.
The visible upstream errors are old output/slot order assumptions now expecting
the corrected first-two input skew and standard `Rm04` order.  Re-run this file
after `ImprovedPinching.Definitions` is repaired.

2026-05-27 noncollapse producer update: added `noncollapseInput_of_ham3`,
which turns Hamilton's geometric `Ham3Noncollapse` ball/volume package into
the legacy HCG `NoncollapseInput` volume slot.  Because the Hamilton package is
eventual in the selected index while `NoncollapseInput` is currently a numeric
all-index record, the finite prefix is saturated by the lower-bound value
itself.  This does not prove the real noncollapse-to-injectivity-radius bridge;
that remains the next compactness producer needed by Theorem 3.10.

Verification: focused checking passed for this file.

2026-05-27 injectivity update: `ham3OfCompactSol` now carries `[I.Boundaryless]`
to pass the real normal-coordinate `FlowBaseInjBound` through
`compactnessSol`.  The adapter still does not edit `HamiltonPositiveRicci.lean`
and does not bridge the legacy `InjInput` to the new injectivity-radius
predicate.

Verification: focused checking of this adapter passed after the injectivity
update.  The targeted adapter module build and umbrella import are blocked by
the unrelated upstream `RicciFlow/Evolution/ImprovedPinching/Wrappers.lean`
slot-order mismatch at line 133, where the available `hRm` statement has the
last four slots ordered differently from the wrapper theorem input.

2026-05-27 alias cleanup: removed the HCG `LimitFlowData` abbrev and rewrote
the adapter directly over `PointedFlowData`.  The old namespace helper
`LimitFlowData.toHam3` is now the standalone adapter `pointedFlowToHam3`.
