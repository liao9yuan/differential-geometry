# RicciLinearizationArmFields

## 2026-07-27 cometric projection

`cometricLmodel_covectorOfCLM_inner` is retained as a compatibility theorem, but
its proof now delegates to the canonical lower-layer
`IntrinsicSpectral.DeTurck.cometricLmodel_inner`.  This removes the need for
chart readout consumers to import the complete arm-field module.

Focused verification is pending restoration of shared upstream object files by
the currently running geometry build.

