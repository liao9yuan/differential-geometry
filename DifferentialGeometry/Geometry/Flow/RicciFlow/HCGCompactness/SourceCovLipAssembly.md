# SourceCovLipAssembly

## Role

`convOut_of_src` is the fixed-window bridge from the source-native
`SrcCovLipData` package and one uniform metric-equivalence constant to the
global `ConvOut` Arzelà--Ascoli output.

The theorem deliberately does not require the whole closed window to lie in
the regular set of the restricted sequence flow.  Endpoint regularity is
handled by the producer of `SrcCovLipData`, which may use a larger ambient
solution.

## Status

Focused verification passed with no diagnostics.

## Progress

- `convOut_of_src`: implementation and focused verification 100%.
- Closed-window Hamilton `ConvOut`: theorem not yet stated (0%); this bridge is
  dedicated machinery for that theorem.
- `ham3_cgh_limit`: 0%; this file does not supply the time-zero
  `MetricCompactBase` producer.
