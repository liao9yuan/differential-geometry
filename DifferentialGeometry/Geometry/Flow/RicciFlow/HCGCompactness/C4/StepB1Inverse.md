# StepB1Inverse

## Status

Focused verification passes with no `sorry`, and the exact module artifact was
refreshed after its missing C4 import chain completed.

The exact-local-inverse chart lane now has two checked layers:

- `exists_inv_seq` packages each sufficiently late forward chart map as a
  partial diffeomorphism, applies the moving-inverse theorem, and identifies
  its selected inverse with the actual `Function.invFunOn` readout by the
  checked left-inverse relation.
- `HasStageJetData.inv_chart_conv` proves compact-open smooth convergence of
  that exact inverse along every cofinal source/target pair.  It now also
  exposes the eventual `ContDiffOn` conclusion already supplied by the same
  moving partial-diffeomorphism construction; no assumption was added.
- `HasStageJetData.inv_chart_tail` performs the bad-pair uniformization and
  gives one rectangular two-stage jet tail on a fixed compact target core.

The reverse finite-stage comparison map is used only in the already checked
approximate-return/global-injectivity producer.  No equality between that map
and the exact inverse is asserted.

## Radius ledger

The source coordinate core lies in the closed radius-`S` source ball.  The
exact inverse is `Function.invFunOn` on the open radius-`T` ball, with `S < T`.
Global injectivity is supplied on a larger radius `Vrad`, with the existing
return-map buffer between `T` and `Vrad`, and `Vrad < r`.  No endpoint-radius
assumption was added.

## Remaining frontier

The coordinate consumer in `StepB1MetricReverse.lean` now combines this chart
convergence with target/source normal-metric and Christoffel convergence and
produces the checked finite component covariant-derivative tower.  The
remaining reverse-side frontier is the separate conversion of those checked
components into the intrinsic `tensor02CovDerivNormWith` bound and its local
pullback-field carrier.

## Honest accounting

- `HasStageJetData.inv_chart_conv`: theorem 100%.
- `HasStageJetData.inv_chart_tail`: theorem 100%.
- Exact-local-inverse chart-convergence sublane: 100%.
- Concrete `MetricCompactBase.exists_b1_raw`: theorem 0% while its two
  `PreApproxIsoDataOn` fields remain open; concrete raw-record field closure is
  about 60%.
- Dedicated B/C machinery: about 98%; Chapter 4 machinery: about 90%; whole
  HCG machinery: about 60%.
- Textbook B1 and compactness endpoints: theorem-level 0%.
