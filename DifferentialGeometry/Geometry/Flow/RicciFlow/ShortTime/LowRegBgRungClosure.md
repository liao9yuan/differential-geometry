# LowRegBgRungClosure.lean

## Role

`IsRung5PathBg` records one fixed-background projected trajectory after the
bottom ladder has closed: pointwise mode convergence, continuity, the exact
Galerkin ODE, zero initial data, and an `N,t`-uniform fifth-energy cap.

`lowregRung5PathAtBg` is the production endpoint.  It obtains one projected
sequence from `lowreg_projMode_atBg`, closes order three with
`lowregFatouE3AtBg`, then invokes the exact background rung-four and rung-five
certificates stored in the adapted solve's single gate package.

The compatibility projections `lowregRung5At` and `lowregMassFiveAt` are not
ported.  Later higher-rung code consumes the full path package directly.

## Slot and identity audit

All Sobolev spaces, eigenmodes, projections, convolutions, and Galerkin
energies remain on the state metric `g₀`.  Every nonlinear forcing occurrence
is exactly `lowregNfun g₀ g_bg`, and each rung certificate is the corresponding
`IsRung*OrdBg g₀ g_bg` witness.  No equality with the diagonal forcing is used.

The `lowreg_projMode_atBg` trajectory pack has the same conjunction order as
the diagonal producer, so the state, Nemytskii, and forcing-ball projections
are reused without an adapter.  No forcing-identity seam was found at source
level.

## Verification

Focused verification passed on the first attempt without local warnings.  The
single-threaded targeted refresh passed, and the resulting module `.olean` is
newer than the source.  The final slot audit found no diagonal nonlinearity,
diagonal rung certificate, compatibility endpoint, `sorry`, or option override.

## Accounting

The background rung-closure brick is complete (100%).  `lowreg_loMassBg` and
headline `ricci_flow_unif_existence` remain unstated and unproved (0%).  The
broader route-(c) background/adapted infrastructure is approximately 70%
complete.
