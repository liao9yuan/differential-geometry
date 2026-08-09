# PrincipalLowRegCore

## Purpose

This module supplies the smooth-core realization bridge from the Banach
Neumann inverse correction to the actual moving inverse-cometric coefficient.

## Current status

The smooth-core realization is complete.

- `invPerturbH2_core` identifies the Banach-algebra Neumann correction with
  `gInvDiffRaisedEndoField g0 g1` inserted in the leading covariant slot.
- `lowRegPrincipal_core` proves equality of the complete low-regularity A2
  operator with `principalOpH2 g0 g1`.  Its final step uses the public
  operator-field associativity theorem, so the fixed double trace and the
  leading-slot inverse-metric action are exactly the full Ricci--DeTurck
  principal coefficient.

Focused verification passed without `sorry` or `whnf`.  The named artifact
refresh was not run after an upstream named refresh expanded into an unrelated
long dependency replay and was stopped to protect the shared workspace.

The endpoint `ricci_flow_unif_existence` remains unproved (0%).
