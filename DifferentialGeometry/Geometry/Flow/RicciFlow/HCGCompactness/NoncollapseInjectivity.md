# NoncollapseInjectivity

## State — 2026-07-29 closure

`flowInj_of_vol` is proved.  It converts the genuine curvature-controlled
time-zero base-ball volume lower bound into one uniform positive injectivity
radius by the pointwise Cheeger--Gromov--Taylor theorem.  The proof constructs
the uniform intrinsic control scale from `SeqBoundedGeometry`, transfers the
base-ball volume lower bound to the CGT scale by relative Bishop--Gromov, and
uses the absolute and pullback volume upper bounds required by
`intrInj_ge_cgt`.

Focused verification passed, the exact module refresh is GREEN
(`4132/4132`), and direct axiom replay contains only `propext`,
`Classical.choice`, and `Quot.sound`.  Thus `flowInj_of_vol` and its dedicated
CGT consumer machinery are each 100%; no independent injectivity black box
remains.

`HamiltonPositiveRicciAdapter.exists_ham3_vol` now supplies the corresponding
all-index `FlowBaseVolData` and `IsFlowBaseVolBound` for the canonical Hamilton
source using one fixed radius and one Perelman `kappa`.  The remaining
axiom-clean Hamilton-main blocker is not noncollapse or H6: it is the separate
`ham3_flow_exists_normalized` uniform-existence producer.

## Historical state — 2026-07-09

The canonical HCG bridge now separates data from proofs:

- `FlowBaseVolData` stores time-zero membership, a positive `kappa`, and a
  positive radius;
- `IsFlowBaseVolBound` proves that the actual basepoint flow balls have
  backward-parabolic curvature control and genuine Riemannian-volume lower
  bounds;
- `flowInj_of_vol` produces the `FlowBaseInjBound` consumed by Hamilton
  compactness.

The ball constructor and both input packages check.  `flowInj_of_vol` is the
single remaining `sorry`: it is the genuine Cheeger–Gromov–Taylor
volume-plus-curvature-to-injectivity theorem, not local record plumbing.

Dedicated data/realization machinery is about 20%; the bridge theorem itself is
0%.  The next prerequisite is an actual Hamilton rescaled `PointedFlowSeq`, not
another numeric compatibility record.

Hamilton's local Section 12 package now constructs genuine `paraSolution`
rescalings and genuine time-zero `FlowMetricBall`s.  What remains is to collect
that sequence on a common time window and realize it as the `PointedFlowSeq`
consumed here.  Including that Hamilton-side migration, the dedicated
noncollapse data/realization machinery is about 40%; `flowInj_of_vol` remains
0%.
