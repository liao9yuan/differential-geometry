# `LowRegDlbInsH2`

## Status

GREEN.  `LowRegDlbInsH2.lean` checks with four Lean threads and a 6144 MB
memory cap.  The file has no local warnings, `sorry`, or `axiom` declarations.

## Result

The public theorem `dlbIns_pair_h2` gives the arbitrary-fixed-background
`H²` pair bound for the cancellation-preserving sum

```text
(DLb(gT,g_bg) - DLb(gT,g)) + (Insert(gT,g_bg) - Insert(gT,g))
```

minus the corresponding expression at `gU`.

The interface is dimension three, assumes the fixed fibre-small ball at both
endpoints, carries `H²` and `H³` caps at both endpoints, and proves the scale

```text
B R * (D3 + D2 + A * D2).
```

This is stronger than the downstream common five-term currency: it introduces
no extra fourth-jet or independently estimated insertion term.

## Proof route

1. Combine `DLb` and insertion pointwise before taking a norm.  The exact
   algebra identifies the sum with a two-slot endomorphism insertion.
2. Rewrite the remaining endomorphism as the raised difference of the
   `wAlphaA` background corrections.
3. Rewrite the `wAlphaA` difference as one covariant derivative of the
   `wOmega` difference.
4. Rewrite the `wOmega` difference as the product of the moving-trace
   difference and the fixed connection-difference tensor.
5. Apply `LowBaseInternal.trace1_pair_h3` and `app_h3_tame`, then drop one
   derivative for the alpha arm and use the raise/insertion jet isometries.

Only the small exact structural identities formerly private to the `H¹` pair
proof were ported.  The large `DeTurckRemainderLowBaseH2Pair.lean` file was not
edited.

## API lessons

- The endomorphism slot estimate is
  `LowRegBgC0Core.endoIns_jet`; the namespace qualification is required.
- The pointwise insertion definitions are exposed through `LieCorr0Core`, so
  that namespace must be opened for the exact cancellation calculation.
- `LowRegInsertH1` is not needed as an import.  The final file uses only the
  moving-trace producer and the fixed-background zero-order algebra module.
- The moving-trace hypotheses really require an `H³` cap on both endpoints.

## Project accounting

- `ricci_flow_unif_existence`: theorem still unstated/unproved at the final
  class-first endpoint, so 0% by the project convention.
- Dedicated uniform-existence machinery: approximately 80%; this percentage
  is infrastructure, not the endpoint theorem.
- Moving-trace `H³` package: 100% for its present interface.
- Arbitrary-background `DLb + Insert` `H²` arm: 100% for the requested pair
  estimate.
- Completed arbitrary-background `A1` high/low operator pair: still 0% as an
  endpoint until it is stated and proved; this theorem removes one of its main
  coefficient-arm prerequisites.

## Downstream handoff

The next consumer may import this file and use `dlbIns_pair_h2` directly in the
fixed-background `H²` coefficient assembly.  It should preserve the combined
`DLb + Insert` expression instead of splitting the two estimates again.
