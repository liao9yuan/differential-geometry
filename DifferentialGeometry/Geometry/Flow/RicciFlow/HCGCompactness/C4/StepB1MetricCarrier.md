# StepB1MetricCarrier

## Status

`preapprox_pair` is the generic final carrier assembly for Step B1.  It keeps
the existing `PreApproxIsoDataOn` interface and introduces no new input.  A
compact source collar and the image collar are extended to genuine smooth
pullback metrics using `exists_pullbackField`.  The reverse carrier uses the
exact `Function.invFunOn` of the forward map.

`HasStageJetData.preapprox_tail` is the stage-specific capstone.  It takes one
maximum of the forward intrinsic, exact-inverse intrinsic, local-diffeomorphism,
and injectivity thresholds, then instantiates `preapprox_pair` on nested closed
source balls.  The output already has the exact two fields required by
`StepB1RawInput`; no auxiliary carrier record is introduced.

Focused verification is green.  The final repair was local assembly only:
the generic injective-local-diffeomorphism glue was qualified at its canonical
Riemannian namespace, the stage comparison map's local `let` was unfolded at
the local-diffeomorphism boundary, and the forward/reverse norm tails were
applied with their already-inferred order and point arguments.  No theorem
statement, endpoint assumption, or carrier interface changed.

## Next consumer

The forward and reverse intrinsic norm tails feed this checked stage-specific
capstone, and `StepB1RawProducer` now consumes it successfully on the master
subsequence.

## Accounting

- `preapprox_pair` and `HasStageJetData.preapprox_tail`: focused-green.
- Concrete `StepB1RawInput` fields: 5/5 checked (100%).
- `MetricCompactBase.exists_b1_raw`: theorem 100%. A separately named combined
  textbook-B1 endpoint remains unstated (0%).
- Selected B/C-to-B1 producer lane: 100%; Chapter 4 machinery:
  approximately 90%; whole-HCG machinery: approximately 60%.
