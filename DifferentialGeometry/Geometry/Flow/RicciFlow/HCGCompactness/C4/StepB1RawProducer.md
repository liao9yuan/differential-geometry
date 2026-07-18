# StepB1RawProducer

## Target-first assembly

`MetricCompactBase.exists_b1_raw` is stated at the exact final
`StepB1RawInput` interface. This keeps the target theorem visible while its
radius diagonal, stage-map geometry, and metric-error producers are assembled.

## Checked result

`MetricCompactBase.exists_b1_raw` is focused-green and its exact module refresh
is green. It extracts one strict master subsequence `psi` and constructs the
unchanged `StepB1RawInput` for `X.subseq psi`. The record closes all five
requested fields for the same global finite-stage comparison map:

1. local diffeomorphism on the larger open ball;
2. injectivity there;
3. exact basepoint preservation;
4. the forward arbitrary-order `PreApproxIsoDataOn` carrier;
5. the reverse carrier for the exact `Function.invFunOn`.

The radius master diagonal, pair-index shift, and final casts are part of the
checked proof. No endpoint-radius assumption, whole-cage target containment,
pointwise chart selector, or glued limit-weight family was added. The source
contains no `sorry` or `admit`.

## Next consumer

The checked `stepB1_of_raw` now turns this raw package into the book's partial
approximate-isometry maps on the extracted sequence. The checked
`compactness_of_b1` then produces the Step-D compactness conclusion for that
sequence. The next assembly seam is purely subsequence bookkeeping: lift the
resulting nested-subsequence conclusion back to the original sequence and use
it to discharge the conditional Chapter-4 endpoint.

## Accounting

- `MetricCompactBase.exists_b1_raw`: theorem 100%.
- Concrete `StepB1RawInput` field closure: 5/5 checked (100%).
- Selected B/C-to-B1 producer lane: 100%; the older full textbook Step-C
  recurrence route remains separate and incomplete.
- A separately named combined textbook-B1 endpoint is not yet stated, so it is
  still recorded as theorem-level 0% despite its producer and conditional
  consumer both being checked.
- Conditional compactness endpoint: theorem-level 0% until the nested
  subsequence lift and final assembly are checked. Chapter-4 machinery remains
  approximately 90%; whole-HCG machinery approximately 60%.
