# PositiveTestDensity

## Purpose

`MemH01.nonneg_approx` is the density producer needed to extend inequalities
proved first for nonnegative smooth compactly supported tests to arbitrary
pointwise nonnegative `H₀¹` tests.  It returns one `MemW1pWitness` for the
limit function together with a compatible approximation sequence; the weak
gradient in the convergence statement is therefore the same witness consumed
by the weak formulation.

## Construction

The existing `MemH01` data supplies smooth compactly supported approximants
`f n`, but `max (f n) 0` is not smooth.  The replacement used here is the
exact-support regularization

```text
t ↦ t * smoothTransition ((k + 1) * t).
```

It is smooth, nonnegative, vanishes whenever `t ≤ 0`, and is exactly `t`
once `(k + 1) * t ≥ 1`.  Thus composition does not enlarge topological
support, so every approximant remains compactly supported inside the original
open set.  Its derivatives are uniformly bounded in `k`; dominated `L²`
convergence identifies the limiting derivative with the positive-part weak
gradient.  The Stampacchia zero-set theorem already provided by
`PositivePart.lean` removes the derivative on the zero set.  A finite-dimensional
diagonal choice makes the regularization error small simultaneously for the
function and every weak-gradient component.

This avoids the finite-measure assumption on the whole open set that the older
`MemW1pWitness.posPart` constructor carries, and it does not assume positivity
of the approximants.

## Verification

Focused verification and the named module refresh both passed warning-free.

## Project position

The splitting theorem endpoint itself is still unstated (0%).  This file is a
single lower analytic producer for the weak maximum-principle lane; the
remaining frontier is the weak-form closure/maximum-principle consumer rather
than positive-test density.  Dedicated splitting machinery is roughly 34%,
whole P1c machinery roughly 62%, and whole Poincare infrastructure roughly
20%.  The final Poincare endpoint remains unstated and unproved (0%).
