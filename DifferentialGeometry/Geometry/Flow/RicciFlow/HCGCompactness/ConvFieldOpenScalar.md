# ConvFieldOpenScalar

## 2026-07-17 open-window scalar readout

`OpenConvOut.scalar_conv` chooses a canonical compact window containing each
carrier time of the book-facing open interval and invokes the pointwise
`ConvOut.scalar_conv_at` producer there.  One global subsequence and one global
limit metric family are inherited from `OpenConvOut`; no equality of
independently produced window limits and no whole-interval closed-window
containment is assumed.

Focused verification passes without warnings. This theorem is an additive
open-interval readout and has no existing downstream call site yet.
