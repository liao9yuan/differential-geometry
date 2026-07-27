# ConvFieldComplete

## 2026-07-27 fixed-window completeness

`ConvOut.complete_at` transfers completeness of the fixed reference pointed
manifold to every slice of a fixed-window limit.  It combines the uniform
sequence lower bound already retained by `ConvOut.lower_of` with
`MetricComplete.complete_of_lower`; no new compactness or convergence
assumption is introduced.

The focused source verification passed without warnings.  This theorem is a
completed infrastructure brick, not the Hamilton compactness endpoint:

- `ConvOut.complete_at`: 100%;
- closed-window flow-upgrade theorem: not yet stated, 0%;
- `ham3_cgh_limit`: 0%;
- whole-HCG supporting machinery: about 61%.

The next conditional frontier is to construct the closed-window `ConvOut` from
the Hamilton source.  The generic `srcCovLip_of_soln` cannot be applied directly
at the two carrier endpoints because it requires the whole closed window to lie
in the restricted source flow's regular set.  The intended route is to derive
the same evolution estimates from the untruncated buffered Hamilton
rescalings, whose regular time sets contain the closed common window.
