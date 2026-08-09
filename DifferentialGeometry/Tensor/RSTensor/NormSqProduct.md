# NormSqProduct

## 2026-07-12 — short-time branch alignment

- Slot-permutation invariance now rewrites with the public `Tensor0SSpace.domDomCongr_apply` theorem after component expansion.
- Focused verification passed without `sorry`; no local blocker remains.

## 2026-07-26 — fiber product norm

- Added `normSq0S_prod`, the fiber-level form of tensor-product norm
  multiplicativity.  It lets pointwise estimates use structural tensor algebra
  without manufacturing a globally smooth field.
- Focused verification and the targeted export refresh both passed.
