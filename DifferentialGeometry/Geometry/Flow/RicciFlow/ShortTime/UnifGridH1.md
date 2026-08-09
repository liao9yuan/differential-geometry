# `UnifGridH1.lean`

## Purpose

This module supplies the missing class-first `H1` summation adapter for a
pointwise grid whose order-`i` window is `range (i + 2)`.  That window is the
one produced by the connection-difference jet tower, and it still uses only
perturbation derivatives through order two when `i < 2`.

## Current state

- `h1_low_unif` is source-complete with no `sorry` or extra frontier
  assumptions.
- It chooses the coefficient from `(gBase, Λ, C)` before the class metric,
  perturbation, and output tensor vary.
- It reuses the class-first integrated grid `h2_grid_unif`; no third metric jet
  or third perturbation derivative enters this adapter.
- Focused verification and direct export pass without warnings.  The axiom
  census contains only `propext`, `Classical.choice`, and `Quot.sound`.

## Progress accounting

- `h1_low_unif` theorem: verified, 100% locally.
- Dedicated class-first low-window grid machinery: 100% for this adapter.
- `lowreg_bounds_unif`: 0%; this adapter is infrastructure, not that producer.
- `ricci_flow_unif_existence`: 0%; it is still neither stated nor proved from
  this lane's class-first producer.
- Whole HCG compactness project: about 3% on the current honest denominator.

The downstream insertion producer has also been checked against this exported
interface.
