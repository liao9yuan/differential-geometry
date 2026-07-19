# MetricCompactnessEndpoint

## Role

`MetricCompactnessEndpoint.lean` is the final assembly layer for the conditional
MSM135 Theorem 3.9 endpoint.  The input structure remains in
`MetricCompactnessInputs.lean`; moving the theorem body here avoids an import
cycle while preserving the public name
`MetricCompactnessInputs.metricCompactness` and its statement.

## Checked assembly

The proof uses exactly this chain:

1. completeness and connectedness give the per-stage `ProperMetricOn` data;
2. `MetricCompactBase.exists_b1_raw` chooses a strict subsequence and produces
   the concrete `StepB1RawInput` (all 5/5 fields checked);
3. `compactness_of_b1` runs the checked Step-D consumer on that subsequence;
4. `MetricCompactnessConclusion.ofSeqSubseq` composes the nested subsequence and
   returns a conclusion for the original pointed sequence.

Focused verification and the exact targeted module refresh pass against the
canonical framed B/C chain.  There is no local `sorry` or `admit` in this file,
but the concrete sidecar constructor it calls still contains the single
`HasCanonBounds` `sorry` recorded below.

## Honest accounting

- `MetricCompactBase.exists_b1_raw`: 100%.
- concrete `StepB1RawInput`: 5/5 fields checked.
- selected B/C-to-B1 producer route: 100%.
- nested-subsequence lift and endpoint wiring: 100%.
- `compactness_canon`, `metricCanon`, and the current projected
  `MetricCompactnessInputs.metricCompactness`: theorem-level 0% until the
  upstream `HasCanonBounds` producer is proved.
- separately named textbook B1 theorem: unstated/unproved, 0%.
- historical full textbook Step-C arbitrary recurrence: separate and incomplete.
- unconditional Theorem 3.9: 0%; native CGT, Bishop--Gromov/uniform-packing,
  [H6], and connectedness producers remain outside this explicit-input theorem.
- Chapter 4 machinery: approximately 95%.
- whole-HCG machinery: approximately 60%.

The endpoint adds no branch-specific radius field and no new mathematical
assumption.  The explicit-volume conditional endpoint is complete; native
Bishop--Gromov/uniform-packing production is the remaining unconditional volume
frontier.

## 2026-07-18 canonical sidecar endpoint

The assembly now exposes `MetricCompactnessInputs.metricCanon`, which runs the
same selected B/C producer and concrete Step-D construction but retains the
`StepDCanonData` provenance through the nested subsequence.  The existing
`metricCompactness` name and statement are preserved as the `.mc` projection;
the abstract `MetricCompactnessConclusion` itself is unchanged.

The canonical framed dependency chain is now exact-current through
`StepDAssembly` and this endpoint.  Consumer/import verification is green; the
remaining obstruction is mathematical/API content in `HasCanonBounds`, not a
stale artifact or framed-coordinate mismatch.

Honest accounting: `metricCanon` is stated but theorem-level 0% while the
single `HasCanonBounds` producer in `compactness_canon` remains `sorry`;
canonical endpoint wiring is about 90% and exact-current.  The old public
conclusion is source-compatible by projection, but the edited proof chain
currently depends on that explicit frontier.  The unconditional
Theorem 3.9 and `compactnessSol` endpoints remain 0%; whole-HCG machinery is
approximately 60%.
