# StepB1MetricIntrinsic

## Status

`HasStageJetData.cov_comp_tail` is focused-green with no `sorry`, `admit`, or
warnings.  It gives one rectangular pair-index tail on every retained smaller
source ball.  The producer-owned buffered finite chart cover supplies the chart,
and the conclusion is uniform over every order `a <= p` and every component
slot.

`HasStageJetData.fwd_norm_tail` and `HasStageJetData.inv_norm_tail` are also
focused-green and contain no `sorry` or `admit`.  The forward theorem realizes
the actual stage-map pullback metric; the reverse theorem uses the exact
`Function.invFunOn` obtained from the local partial diffeomorphism, not the
opposite-direction stage comparison map.  Both retain the existing radius
hierarchy and introduce no endpoint-radius or whole-cage assumption.

The exact module refresh is green, so both intrinsic tails are available to
downstream compiled consumers.

## Proof architecture

The local argument is a bad-pair/compact-subsequence contradiction.  On the
compact coordinate patch, `pb_conv` gives smooth convergence of the actual
pullback coefficients while the retained normal-metric family converges to the
same coercive limit.  The actual pullback family is smooth on an eventual tail;
its finite prefix is totalized by the smooth limit metric before applying
`metric_tower_conv`.

The latter theorem controls the complete Pi-valued component tower.  Its
order-zero norm therefore controls a varying component slot directly; no slot
subsequence or slotwise stabilization is needed.  A finite maximum over
`Fin (p + 1)` and then over the live source charts gives the common rectangular
tail.

## Remaining frontier and accounting

The intrinsic realization is checked for both the forward actual stage map and
the exact local inverse. Its stage-specific `preapprox_tail` consumer and the
final raw-record consumer are now also checked.

- `cov_comp_tail`: theorem 100%.
- Forward component covariant-tower sublane: 100%.
- `fwd_norm_tail` and `inv_norm_tail`: theorem 100% and focused-green.
- Concrete `StepB1RawInput` record fields: 5/5 checked (100%).
- `MetricCompactBase.exists_b1_raw`: theorem 100%. A separately named combined
  textbook-B1 endpoint remains unstated (0%).
- Selected B/C-to-B1 producer lane: 100%; Chapter 4 machinery:
  approximately 90%; whole-HCG machinery: approximately 60%.
