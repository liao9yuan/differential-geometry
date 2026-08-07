# DeTurckLieKernelL2JetBoundUniform.lean

## Role

This lower-layer module supplies the real class-first finite-window producer for
the DLa coefficient.  It does not choose a metric class or integrate the
pointwise grid.  Instead it accepts one nonnegative sequence bounding the first
three fixed-background connection-difference jets.

## Public producer

`dla_grid_of_conn` has the binding order

```text
δ₀, F
→ ∃ C
→ ∀ g₀ g_bg
→ fixed connection cap for j < 3
→ ∀ g₁ P
→ pointwise DLa grid for i < 2.
```

Thus no metric occurs before `C` is selected.  `F` is the only external
coefficient input.  The moving inverse, moving connection, and two moving
traces use the existing class-first factories.

The fixed-connection hypothesis is deliberately left as the raw three-jet
tower, rather than hidden in a DLa-specific package.  A later DLb factory can
therefore consume exactly the same class cap without depending on this DLa
module or translating through a consumer-only wrapper.

## Implementation

- `kernel_grid_of_conn` replaces the metricwise fixed-field witnesses in the
  eight-arm raised DLa kernel by `F`.  The differentiated fixed arm consumes
  `F (i + 1)`, so `i < 2` requires exactly `j < 3`.
- `lowered_grid_of_conn` transports the raised estimate through the exact
  lowering/raising identity.
- `sym_grid_of_conn` reuses the perturbative lowering and symmetrization proof,
  retaining the same DLa product-window currency.
- `pair_trace_grid_unif` uses `trace_grid_unif` at passenger ranks two and four;
  its constants are selected before both metrics.
- `dla_grid_of_conn` composes the pair trace and symmetrized kernel through the
  exact DLa factorization.

The old 6000-line owning module received only the
`DLaUniformInternal` extraction surface: reducible aliases and wrappers around
already-proved private algebra.  No new estimate proof was placed there.

## Verification

The owning extraction surface and this producer both pass whole-file focused
verification under one Lean thread and the 6 GB memory cap.  This file is
warning-free.  Its exact targeted export produced a fresh `.olean`, which was
then imported by an independent axiom audit.  The outer command wrapper timed
out before observing that export, but the exact owned Lake/Lean process tree was
left running, monitored below the memory cap, and exited naturally before the
fresh target was accepted; no overlapping Lean process was started.

`dla_grid_of_conn` depends only on the standard axioms `propext`,
`Classical.choice`, and `Quot.sound`.  The previously identified elaboration
risks all closed without changing the public statement.

## Project status

- `dla_grid_of_conn`: **100%**, focused-green, exported, and axiom-clean apart
  from the standard three axioms.
- `dla_h1_unif`: not yet stated in this module, theorem-level 0%; it should be a
  short specialization using the three fixed-connection class bounds and
  `h1_grid_unif` after this producer verifies.
- `ricci_flow_unif_existence`: theorem-level 0%; this is dedicated coefficient
  infrastructure only.
