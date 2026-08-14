# Hamilton positive-Ricci examples

## 2026-08-14 classical regression examples

The module constructs the standard round metric on `S³` as an explicit
positive-Ricci witness.  It contracts the checked constant-sectional-curvature
formula through `ricci_of_sec`, rather than assuming Ricci positivity.

The same bridge is applied to every finite round three-sphere quotient carried
by `RoundQuotientData`, using its explicit descended metric `gQuot`.  Both the
standard sphere and quotient family are then fed to the public Hamilton endpoint
to obtain `AdmitsConstPosSec ∧ SphericalSpaceForm`.

The selected regression suite is complete (100%): explicit positive-Ricci
witnesses and Hamilton conclusions are present for both supported example
classes.  The Hamilton theorem endpoint remains complete (100%) and axiom-clean;
this test layer does not change the completion percentage of the broader
differential-geometry library.  Concrete `RP³` and lens-space types remain a
separate quotient-manifold API frontier (0%).
