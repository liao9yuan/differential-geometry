# StepB1RawProducer

## Target-first assembly

`MetricCompactBase.exists_b1_raw` is now stated at the exact final
`StepB1RawInput` interface.  This follows the working preference to keep the
target theorem visible and fill its proof in place as lower producers become
checked.

## Current frontier

The theorem body has one explicit `sorry` at the first honest missing assembly:
the integer-radius master subsequence diagonal.  It must not be replaced by
`psi := id`.  Once that diagonal is implemented, the proof should immediately
be refined to

```lean
refine ⟨psi, hpsi, { comparison := ?_ }⟩
```

and the remaining frontier moved into the concrete `comparison` field.

The Route-A two-bump stage configurations are implemented and focused-green in
`StepCStageFill.lean`, including arbitrary two-index reindexing convergence and
the exact active-target readout for retained interacting slots.  Still
genuinely missing downstream are common-domain center-equation and moving
implicit-center convergence, exact inverse convergence, and the
chart-to-intrinsic covariant metric-error bridge.

The current target-first body remains the honest readable stopping shape until
the integer-radius master diagonal supplies an actual `psi`: refining with
`psi := id` would be false, while introducing a second assumption/wrapper only
hides the same frontier.  Once `psi` exists, immediately expose
`{ comparison := ... }` and use `stageComparisonMap` as its concrete `F`.

## Accounting

- `MetricCompactBase.exists_b1_raw`: stated, proof 0% while it contains `sorry`.
- Dedicated Route-A stage-filler/configuration machinery: checked (100%).
- Concrete `StepB1RawInput` producer: 0%.
- Textbook Step B1 theorem: 0%.
- Dedicated Step-B/B1 machinery: approximately 95%; Chapter 4 machinery:
  approximately 87%; whole HCG machinery: approximately 57%.
